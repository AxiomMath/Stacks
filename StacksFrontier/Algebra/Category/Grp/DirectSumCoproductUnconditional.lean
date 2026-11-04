module
public import StacksFrontier.Algebra.Category.Grp.DirectSumCoproduct
import all StacksFrontier.Algebra.Category.Grp.DirectSumCoproduct

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Coproducts of abelian groups are direct sums

For a family `A` of abelian groups indexed by `ι` and any colimit cofan `c` of `A`, the map
`⨁ i, A i → c.pt` induced by the inclusions `c.inj i` is bijective.

## Main results

* `AddCommGrpCat.bijective_toAddMonoid_of_isColimit`: for a colimit cofan `c` of `A`, the map
  `DirectSum.toAddMonoid fun i => (c.inj i).hom` is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped DirectSum

universe w t

namespace AddCommGrpCat

variable {ι : Type w} (A A' : ι → AddCommGrpCat.{max w t})

/-- **A coproduct of abelian groups is the direct sum, elementwise.** For a colimit cofan `c` of a
family of abelian groups `A`, the map `⨁ i, A i → c.pt` induced by the inclusions is bijective. -/
public theorem bijective_toAddMonoid_of_isColimit [DecidableEq ι] {c : Cofan A}
    (hc : IsColimit c) :
    Function.Bijective (DirectSum.toAddMonoid fun i => (c.inj i).hom) := by
  let T := DirectSum.toAddMonoid fun i => (c.inj i).hom
  have hT : ∀ i (x : A i), T (DirectSum.of (fun i => (A i : Type _)) i x) = c.inj i x :=
    fun i x => DirectSum.toAddMonoid_of (fun i => (c.inj i).hom) i x
  refine ⟨?_, fun y => ?_⟩
  · let d : Cofan A := Cofan.mk (AddCommGrpCat.of (⨁ i : ι, (A i : Type _))) fun i =>
      AddCommGrpCat.ofHom (DirectSum.of (fun i => (A i : Type _)) i)
    let Ψ : c.pt ⟶ d.pt := hc.desc d
    have hΨ : Ψ.hom.comp T = AddMonoidHom.id _ := DirectSum.addHom_ext fun i x => by
      have h := ConcreteCategory.congr_hom (hc.fac d ⟨i⟩) x
      simp only [ConcreteCategory.comp_apply] at h
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.id_apply, hT]
      exact h
    exact Function.LeftInverse.injective (g := Ψ.hom) fun x => DFunLike.congr_fun hΨ x
  · let q : c.pt ⟶ AddCommGrpCat.of (c.pt ⧸ T.range) :=
      AddCommGrpCat.ofHom (QuotientAddGroup.mk' _)
    have hq : q = 0 := hc.hom_ext fun ⟨i⟩ => by
      ext x
      simp only [ConcreteCategory.comp_apply, Limits.comp_zero, AddCommGrpCat.hom_zero,
        AddMonoidHom.zero_apply]
      exact (QuotientAddGroup.eq_zero_iff _).2 ⟨_, hT i x⟩
    have hy := ConcreteCategory.congr_hom hq y
    simp only [AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply] at hy
    exact (QuotientAddGroup.eq_zero_iff _).1 hy

end AddCommGrpCat

end
