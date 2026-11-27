import OMAStatements.S_mo_264127

/-! The first step settles an explicit initial time interval on every finite
sample. The remaining times form the second step. -/
namespace OMA.R_mo_264127_R1
open OMA.S_mo_264127

def H1 : Prop := ∀ (V : Type) (G : SimpleGraph V) [G.LocallyFinite] (d : ℕ),
  G.IsRegularOfDegree d → ∀ (S : Finset V) (i j : S), G.Adj i.val j.val →
  (∀ v, G.Adj i.val v → v∈S) → ∀ t : ℝ, 0≤t →
  24*((S.card:ℝ)^2+1)^4*t ≤ 1 → comparison G S i j t

def H2 : Prop := ∀ (V : Type) (G : SimpleGraph V) [G.LocallyFinite] (d : ℕ),
  G.IsRegularOfDegree d → ∀ (S : Finset V) (i j : S), G.Adj i.val j.val →
  (∀ v, G.Adj i.val v → v∈S) → ∀ t : ℝ, 0≤t →
  1 < 24*((S.card:ℝ)^2+1)^4*t → comparison G S i j t

theorem main : H1 → H2 → type_of% @OMA.S_mo_264127.main := by
  intro h1 h2 V G lf d reg S i j adj closed t ht
  rcases le_or_gt (24*((S.card:ℝ)^2+1)^4*t) 1 with h|h
  · exact h1 V G d reg S i j adj closed t ht h
  · exact h2 V G d reg S i j adj closed t ht h

end OMA.R_mo_264127_R1
