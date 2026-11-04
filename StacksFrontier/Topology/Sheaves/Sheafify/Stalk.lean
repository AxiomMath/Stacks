module

public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Stacks 007Z: stalk of a presheaf equals stalk of its sheafification

Let `X` be a topological space and `F` a presheaf of sets on `X`. For `x : X`,
the canonical map `F → F^#` induces an isomorphism `F_x ≃ F^#_x` on stalks.

In Mathlib this is the statement that `(stalkFunctor _ x).map (toSheafify F)` is
an isomorphism. The proof identifies this morphism as the inverse of the
isomorphism `F.stalkToFiber x : F^#_x ≅ F_x` (which lands at the espace étalé
fiber, here identified with the presheaf stalk).
-/

@[expose] public section

open CategoryTheory TopCat Presheaf


universe u

/-- The composition `F.stalkToFiber x ≫ (stalkFunctor _ x).map (toSheafify F)`
is the identity on `F^#_x`. On a germ `germ V x hxV t` of the sheafification we
pass to a local representative `s : F V` of `t` provided by the sheafification
construction, and check that both sides return that representative's germ. -/
private lemma stalkToFiber_comp_stalkMap_toSheafify
    {X : TopCat} (F : Presheaf (Type u) X) (x : X) :
    F.stalkToFiber x ≫ (stalkFunctor (Type u) x).map (toSheafify F) = 𝟙 _ := by
  refine ConcreteCategory.hom_ext _ _ ?_
  intro g
  obtain ⟨U, hxU, t, rfl⟩ := F.sheafify.presheaf.exists_germ_eq g
  change (stalkFunctor (Type u) x).map (toSheafify F)
      (F.stalkToFiber x (F.sheafify.presheaf.germ U x hxU t)) =
      F.sheafify.presheaf.germ U x hxU t
  rw [show F.stalkToFiber x (F.sheafify.presheaf.germ U x hxU t) = t.val ⟨x, hxU⟩ from
        TopCat.stalkToFiber_germ (Sheafify.isLocallyGerm F) U x hxU t]
  obtain ⟨V, hxV, i, s, hs⟩ := t.2 ⟨x, hxU⟩
  rw [show t.val ⟨x, hxU⟩ = F.germ V x hxV s by simpa using hs ⟨x, hxV⟩]
  have hfun : (stalkFunctor (Type u) x).map (toSheafify F) (F.germ V x hxV s) =
      F.sheafify.presheaf.germ V x hxV ((toSheafify F).app (Opposite.op V) s) :=
    stalkFunctor_map_germ_apply V x hxV (toSheafify F) s
  rw [hfun, show (toSheafify F).app (Opposite.op V) s = F.sheafify.presheaf.map i.op t from
        Subtype.ext (funext fun y => (hs y).symm)]
  exact germ_res_apply F.sheafify.presheaf i x hxV t

/-- **Stacks tag 007Z.** Let `F` be a presheaf of sets on a topological space `X`
and let `x : X`. The canonical map `F → F^#` induces an isomorphism of stalks
`F_x ≃ F^#_x`. -/
@[stacks 007Z]
theorem stalkFunctor_map_toSheafify_isIso
    {X : TopCat} (F : Presheaf (Type u) X) (x : X) :
    IsIso ((stalkFunctor (Type u) x).map (toSheafify F)) := by
  have : IsIso (F.stalkToFiber x) := (F.sheafifyStalkIso x).isIso_hom
  have h := stalkToFiber_comp_stalkMap_toSheafify F x
  refine ⟨F.stalkToFiber x, ?_, h⟩
  rw [← IsIso.inv_eq_of_hom_inv_id h]
  simp
