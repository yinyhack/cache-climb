;; CacheClimb - Decentralized Identity Verification System

;; Three-tier architecture:
;;   1. Self-Attestation   - users stake tokens to register credentials
;;   2. Peer Validation    - validators verify credential claims
;;   3. Reputation Engine  - scores updated based on verification history
;;
;; Progressive Trust Staking: staking requirements decrease as reputation grows.
;; Time-decay: credentials expire after a configurable number of blocks.
;; Sharded pools: validators are assigned to shards to reduce collusion risk.

;; ============================================================
;; ERRORS
;; ============================================================

(define-constant ERR-NOT-AUTHORIZED        (err u100))
(define-constant ERR-ALREADY-REGISTERED   (err u101))
(define-constant ERR-NOT-REGISTERED       (err u102))
(define-constant ERR-INSUFFICIENT-STAKE   (err u103))
(define-constant ERR-CREDENTIAL-NOT-FOUND (err u104))
(define-constant ERR-CREDENTIAL-EXPIRED   (err u105))
(define-constant ERR-ALREADY-VALIDATED    (err u106))
(define-constant ERR-NOT-A-VALIDATOR      (err u107))
(define-constant ERR-INVALID-SHARD        (err u108))
(define-constant ERR-TRANSFER-FAILED      (err u109))
(define-constant ERR-SELF-VALIDATION      (err u110))

;; ============================================================
;; CONSTANTS
;; ============================================================

;; Contract deployer / admin
(define-constant CONTRACT-OWNER tx-sender)

;; Token amounts (in micro-STX, 1 STX = 1_000_000 uSTX)
(define-constant BASE-STAKE-AMOUNT       u1000000)   ;; 1 STX base stake
(define-constant VALIDATOR-BOND          u5000000)   ;; 5 STX validator bond
(define-constant VALIDATOR-REWARD        u100000)    ;; 0.1 STX per validation

;; Reputation thresholds
(define-constant REPUTATION-TIER-1       u10)   ;; reduced stake at tier 1
(define-constant REPUTATION-TIER-2       u50)   ;; further reduction at tier 2
(define-constant REPUTATION-TIER-3       u100)  ;; minimal stake at tier 3

;; Time-decay: credential lifetime in blocks (~1 block per 10 min on Stacks)
(define-constant CREDENTIAL-LIFETIME     u52560) ;; ~1 year

;; Minimum validations required before a credential is considered verified
(define-constant MIN-VALIDATIONS         u3)

;; Number of shards for validator pool partitioning
(define-constant SHARD-COUNT             u5)

;; ============================================================
;; DATA MAPS & VARS
;; ============================================================

;; User profile: reputation score and registration block
(define-map users
  { owner: principal }
  {
    reputation:       uint,
    registered-at:    uint,
    total-staked:     uint,
    validator-shard:  (optional uint)
  }
)

;; Credential record submitted via self-attestation
;; credential-hash: off-chain zk-SNARK proof hash (bytes32 represented as (buff 32))
(define-map credentials
  { credential-id: uint }
  {
    owner:            principal,
    credential-hash:  (buff 32),
    credential-type:  (string-ascii 64),
    stake-amount:     uint,
    created-at:       uint,
    validation-count: uint,
    is-verified:      bool,
    is-revoked:       bool
  }
)

;; Track which validators have already validated a given credential
(define-map validations
  { credential-id: uint, validator: principal }
  { validated-at: uint, approved: bool }
)

;; Validator registry
(define-map validators
  { validator: principal }
  {
    bond-amount:        uint,
    shard-assignment:   uint,
    validations-done:   uint,
    is-active:          bool
  }
)

;; Auto-increment credential ID counter
(define-data-var next-credential-id uint u1)

;; Total STX held in escrow by this contract
(define-data-var total-escrowed uint u0)

;; ============================================================
;; PRIVATE HELPERS
;; ============================================================

;; Calculate staking requirement based on caller reputation
(define-private (get-stake-requirement (owner principal))
  (let ((user (map-get? users { owner: owner })))
    (match user
      u (let ((rep (get reputation u)))
          (if (>= rep REPUTATION-TIER-3)
            (/ BASE-STAKE-AMOUNT u4)          ;; 75% discount
            (if (>= rep REPUTATION-TIER-2)
              (/ BASE-STAKE-AMOUNT u2)         ;; 50% discount
              (if (>= rep REPUTATION-TIER-1)
                (/ (* BASE-STAKE-AMOUNT u3) u4) ;; 25% discount
                BASE-STAKE-AMOUNT))))           ;; no discount
      BASE-STAKE-AMOUNT)))

;; Derive a shard index from a principal (simple modulo on last byte)
(define-private (derive-shard (addr principal))
  (mod (len (unwrap-panic (to-consensus-buff? addr))) SHARD-COUNT))

;; Increment and return the next credential ID
(define-private (next-id)
  (let ((id (var-get next-credential-id)))
    (var-set next-credential-id (+ id u1))
    id))

;; Increase reputation of a principal by delta
(define-private (add-reputation (addr principal) (delta uint))
  (match (map-get? users { owner: addr })
    u (map-set users
        { owner: addr }
        (merge u { reputation: (+ (get reputation u) delta) }))
    false))

;; ============================================================
;; PUBLIC: USER REGISTRATION
;; ============================================================

;; Register as a new user. Anyone may register once.
(define-public (register-user)
  (begin
    (asserts! (is-none (map-get? users { owner: tx-sender }))
              ERR-ALREADY-REGISTERED)
    (map-set users
      { owner: tx-sender }
      {
        reputation:      u0,
        registered-at:   block-height,
        total-staked:    u0,
        validator-shard: none
      })
    (ok true)))

;; ============================================================
;; PUBLIC: SELF-ATTESTATION (Tier 1)
;; ============================================================

;; Submit a new credential claim backed by a zk-SNARK proof hash.
;; The caller must be registered and stake the required STX.
(define-public (submit-credential
    (credential-hash (buff 32))
    (credential-type (string-ascii 64)))
  (let (
    (user    (unwrap! (map-get? users { owner: tx-sender }) ERR-NOT-REGISTERED))
    (req     (get-stake-requirement tx-sender))
    (cred-id (next-id))
  )
    ;; Transfer stake into contract escrow
    (unwrap! (stx-transfer? req tx-sender (as-contract tx-sender)) ERR-TRANSFER-FAILED)
    ;; Record credential
    (map-set credentials
      { credential-id: cred-id }
      {
        owner:            tx-sender,
        credential-hash:  credential-hash,
        credential-type:  credential-type,
        stake-amount:     req,
        created-at:       block-height,
        validation-count: u0,
        is-verified:      false,
        is-revoked:       false
      })
    ;; Update user total-staked
    (map-set users
      { owner: tx-sender }
      (merge user { total-staked: (+ (get total-staked user) req) }))
    (var-set total-escrowed (+ (var-get total-escrowed) req))
    (ok cred-id)))

;; Owner may revoke their own credential and reclaim staked STX.
(define-public (revoke-credential (credential-id uint))
  (let (
    (cred (unwrap! (map-get? credentials { credential-id: credential-id })
                   ERR-CREDENTIAL-NOT-FOUND))
  )
    (asserts! (is-eq tx-sender (get owner cred)) ERR-NOT-AUTHORIZED)
    (asserts! (not (get is-revoked cred))         ERR-NOT-AUTHORIZED)
    ;; Return stake
    (unwrap! (as-contract (stx-transfer? (get stake-amount cred) tx-sender (get owner cred)))
             ERR-TRANSFER-FAILED)
    (map-set credentials
      { credential-id: credential-id }
      (merge cred { is-revoked: true }))
    (var-set total-escrowed (- (var-get total-escrowed) (get stake-amount cred)))
    (ok true)))

;; ============================================================
;; PUBLIC: VALIDATOR MANAGEMENT
;; ============================================================

;; Register as a validator by bonding STX. Shard is assigned deterministically.
(define-public (register-validator)
  (begin
    (asserts! (is-none (map-get? validators { validator: tx-sender })) ERR-ALREADY-REGISTERED)
    (asserts! (is-some (map-get? users { owner: tx-sender })) ERR-NOT-REGISTERED)
    ;; Bond transfer
    (unwrap! (stx-transfer? VALIDATOR-BOND tx-sender (as-contract tx-sender)) ERR-TRANSFER-FAILED)
    (let ((shard (derive-shard tx-sender)))
      (map-set validators
        { validator: tx-sender }
        {
          bond-amount:      VALIDATOR-BOND,
          shard-assignment: shard,
          validations-done: u0,
          is-active:        true
        })
      ;; Record shard on user profile
      (match (map-get? users { owner: tx-sender })
        u (map-set users { owner: tx-sender } (merge u { validator-shard: (some shard) }))
        false))
    (var-set total-escrowed (+ (var-get total-escrowed) VALIDATOR-BOND))
    (ok true)))

;; Deregister as validator and reclaim bond (only if no pending duties).
(define-public (deregister-validator)
  (let (
    (v (unwrap! (map-get? validators { validator: tx-sender }) ERR-NOT-A-VALIDATOR))
  )
    (asserts! (get is-active v) ERR-NOT-AUTHORIZED)
    (unwrap! (as-contract (stx-transfer? (get bond-amount v) tx-sender tx-sender)) ERR-TRANSFER-FAILED)
    (map-set validators
      { validator: tx-sender }
      (merge v { is-active: false, bond-amount: u0 }))
    (var-set total-escrowed (- (var-get total-escrowed) (get bond-amount v)))
    (ok true)))

;; ============================================================
;; PUBLIC: PEER VALIDATION (Tier 2)
;; ============================================================

;; Validate a credential. Validators must be active and assigned to the
;; correct shard (credential-id mod SHARD-COUNT). Prevents self-validation.
(define-public (validate-credential (credential-id uint) (approved bool))
  (let (
    (cred (unwrap! (map-get? credentials { credential-id: credential-id })
                   ERR-CREDENTIAL-NOT-FOUND))
    (v    (unwrap! (map-get? validators { validator: tx-sender }) ERR-NOT-A-VALIDATOR))
  )
    ;; Basic guards
    (asserts! (get is-active v)                                    ERR-NOT-A-VALIDATOR)
    (asserts! (not (is-eq tx-sender (get owner cred)))             ERR-SELF-VALIDATION)
    (asserts! (not (get is-revoked cred))                          ERR-NOT-AUTHORIZED)
    (asserts! (is-none (map-get? validations
                         { credential-id: credential-id, validator: tx-sender }))
              ERR-ALREADY-VALIDATED)
    ;; Shard check: validator shard must match credential-id mod SHARD-COUNT
    (asserts! (is-eq (get shard-assignment v) (mod credential-id SHARD-COUNT))
              ERR-INVALID-SHARD)
    ;; Time-decay check
    (asserts! (<= (- block-height (get created-at cred)) CREDENTIAL-LIFETIME)
              ERR-CREDENTIAL-EXPIRED)
    ;; Record validation
    (map-set validations
      { credential-id: credential-id, validator: tx-sender }
      { validated-at: block-height, approved: approved })
    ;; Update credential validation count and verification status
    (let ((new-count (+ (get validation-count cred) u1)))
      (map-set credentials
        { credential-id: credential-id }
        (merge cred {
          validation-count: new-count,
          is-verified:      (and approved (>= new-count MIN-VALIDATIONS))
        })))
    ;; Update validator stats and reputation
    (map-set validators
      { validator: tx-sender }
      (merge v { validations-done: (+ (get validations-done v) u1) }))
    (add-reputation tx-sender u1)
    ;; Pay validator reward from contract
    (unwrap! (as-contract (stx-transfer? VALIDATOR-REWARD tx-sender tx-sender)) ERR-TRANSFER-FAILED)
    ;; Reward credential owner reputation if approved
    (if approved (add-reputation (get owner cred) u2) false)
    (ok true)))

;; ============================================================
;; READ-ONLY QUERIES
;; ============================================================

;; Get user profile
(define-read-only (get-user (addr principal))
  (map-get? users { owner: addr }))

;; Get credential by ID
(define-read-only (get-credential (credential-id uint))
  (map-get? credentials { credential-id: credential-id }))

;; Get validator info
(define-read-only (get-validator (addr principal))
  (map-get? validators { validator: addr }))

;; Check whether a specific validator has already validated a credential
(define-read-only (get-validation (credential-id uint) (validator principal))
  (map-get? validations { credential-id: credential-id, validator: validator }))

;; Compute current stake requirement for an address
(define-read-only (stake-requirement-for (addr principal))
  (get-stake-requirement addr))

;; Check if a credential is still within its validity window
(define-read-only (is-credential-valid (credential-id uint))
  (match (map-get? credentials { credential-id: credential-id })
    cred (and
           (get is-verified cred)
           (not (get is-revoked cred))
           (<= (- block-height (get created-at cred)) CREDENTIAL-LIFETIME))
    false))

;; Total STX held in escrow
(define-read-only (get-total-escrowed)
  (var-get total-escrowed))

;; Next credential ID (useful for off-chain indexers)
(define-read-only (get-next-credential-id)
  (var-get next-credential-id))
