import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]
variable (h : I → ℝ)      -- h_i: Customer demand for each customer i ∈ I
variable (g : I → J → ℝ) -- g_ij: Utility factor related to distance for customer i and site j
variable (U_L U_F : I → ℝ) -- U_i^L and U_i^F: Pre-existing utilities

structure LeaderDecisions :=
  (x : J → ℕ)  -- x_j: Binary location decisions (using ℕ for now, will constrain to 0 or 1 later)
  (z : J → ℝ)
  (ξ : J → ℝ)  -- ξ_j: The reformulated attractiveness-location variables

structure FollowerDecisions :=
  (y : J → ℕ)  -- y_j: Follower's binary location decisions
  (z_prime : J → ℝ)
  (ψ : J → ℝ)  -- ψ_j: Follower's attractiveness-location variables


-- Define the leader's total utility for a single customer 'i'
def leader_utility (ld : LeaderDecisions) (i : I) : ℝ :=
  (∑ j : J, (g i j)⁻¹ * ld.ξ j) + U_L i

-- Define the total utility from all firms for a single customer 'i'
def total_utility (ld : LeaderDecisions) (fd : FollowerDecisions) (i : I) : ℝ :=
  (∑ j : J, (g i j)⁻¹ * (ld.ξ j + fd.ψ j)) + U_L i + U_F i

-- Finally, define the leader's total market share (the main objective function)
def leader_market_share (ld : LeaderDecisions) (fd : FollowerDecisions) : ℝ :=
  ∑ i : I, h i * (leader_utility ld i / total_utility ld fd i)




-- Define the follower's total utility for a single customer 'i'
def follower_utility (fd : FollowerDecisions) (i : I) : ℝ :=
  (∑ j : J, (g i j)⁻¹ * fd.ψ j) + U_F i

-- Define the follower's total market share (their objective function)
def follower_market_share (ld : LeaderDecisions) (fd : FollowerDecisions) : ℝ :=
  ∑ i : I, h i * (follower_utility fd i / total_utility ld fd i)





-- Global Problem Parameters
variable (p r : ℕ)      -- p, r: Max number of facilities for leader and follower
variable (A B : ℝ)      -- A, B: Attractiveness budgets for leader and follower


-- A structure to define the constraints for the leader's decisions
structure LeaderFeasibility (ld : LeaderDecisions) : Prop :=
  -- Constraint (4): Leader can open at most p facilities [cite: 24]
  facility_limit : (∑ j : J, ld.x j) ≤ p

  -- Binary decision variable constraint
  x_is_binary : ∀ j : J, ld.x j = 0 ∨ ld.x j = 1

  -- Let's define the upper bound on z_j for convenience
  let z_upper_bound := Real.exp A

  -- The reformulated budget constraint using z_j = exp(α_j) [cite: 24]
  -- We also need to define z_j for the McCormick envelope.
  -- A clean way is to have z as a variable and ln(z) in the budget.
  -- Let's add z to the LeaderDecisions structure.
  -- (Go back and add `z : J → ℝ` to the LeaderDecisions structure)
  budget_limit : (∑ j : J, Real.log (ld.z j)) ≤ A

  -- Variable Bounds [cite: 27]
  z_bounds : ∀ j : J, ld.z j ≥ 1
  ξ_nonnegative : ∀ j : J, ld.ξ j ≥ 0

  -- McCormick Envelope constraints to linearize ξ_j = z_j * x_j
  -- This enforces that z_j must be 1 if x_j is 0.
  mccormick_z_upper : ∀ j : J, ld.z j ≤ (z_upper_bound - 1) * (ld.x j) + 1

  -- These four inequalities define the exact convex relaxation of the bilinear term.
  mccormick_1 : ∀ j : J, ld.ξ j ≤ z_upper_bound * (ld.x j)
  mccormick_2 : ∀ j : J, ld.ξ j ≤ ld.z j - (1 - ld.x j) -- Since lower bound on z is 1
  mccormick_3 : ∀ j : J, ld.ξ j ≥ ld.x j
  mccormick_4 : ∀ j : J, ld.ξ j ≥ ld.z j - z_upper_bound * (1 - ld.x j)


-- END OF LEADERFEASIBILITY. NOW DEFINE FOLLOWERFEASIBILITY SEPARATELY.

-- A structure to define the constraints for the follower's decisions
structure FollowerFeasibility (ld : LeaderDecisions) (fd : FollowerDecisions) : Prop :=
  -- Constraint (10): Follower can open at most r facilities [cite: 29]
  facility_limit : (∑ j : J, fd.y j) ≤ r

  -- Binary decision variable constraint
  y_is_binary : ∀ j : J, fd.y j = 0 ∨ fd.y j = 1

  -- Constraint: Follower cannot open a facility at a site taken by the leader
  no_overlap : ∀ j : J, fd.y j ≤ 1 - ld.x j

  -- Let's define the upper bound on z'_j for convenience
  let z_prime_upper_bound := Real.exp B

  -- (Go back and add `z_prime : J → ℝ` to the FollowerDecisions structure)
  budget_limit : (∑ j : J, Real.log (fd.z_prime j)) ≤ B [cite: 30]

  -- Variable Bounds [cite: 33]
  z_prime_bounds : ∀ j : J, fd.z_prime j ≥ 1
  ψ_nonnegative : ∀ j : J, fd.ψ j ≥ 0

  -- McCormick Envelope constraints for ψ_j = z'_j * y_j
  mccormick_z_upper : ∀ j : J, fd.z_prime j ≤ (z_prime_upper_bound - 1) * (fd.y j) + 1
  mccormick_1 : ∀ j : J, fd.ψ j ≤ z_prime_upper_bound * (fd.y j)
  mccormick_2 : ∀ j : J, fd.ψ j ≤ fd.z_prime j - (1 - fd.y j)
  mccormick_3 : ∀ j : J, fd.ψ j ≥ fd.y j
  mccormick_4 : ∀ j : J, fd.ψ j ≥ fd.z_prime j - z_prime_upper_bound * (1 - fd.y j)


-- This proposition states that `fd` is an optimal response to a given `ld`.
-- It captures the follower's entire optimization problem.
def IsOptimalFollowerResponse (ld : LeaderDecisions) (fd : FollowerDecisions) : Prop :=
  -- First, the follower's decision must be feasible.
  (FollowerFeasibility ld fd) ∧

  -- Second, this decision must yield a market share greater than or equal to
  -- any *other* feasible decision the follower could have made.
  (∀ (other_fd : FollowerDecisions), FollowerFeasibility ld other_fd →
    follower_market_share ld other_fd ≤ follower_market_share ld fd)

-- This proposition is true if `(ld, fd)` constitutes a valid
-- equilibrium solution to the full bilevel game.
structure IsBilevelSolution (ld : LeaderDecisions) (fd : FollowerDecisions) : Prop :=
  -- The leader's own decisions must be feasible.
  leader_is_feasible : LeaderFeasibility ld

  -- The follower's response must be an optimal one.
  follower_is_optimal : IsOptimalFollowerResponse ld fd
