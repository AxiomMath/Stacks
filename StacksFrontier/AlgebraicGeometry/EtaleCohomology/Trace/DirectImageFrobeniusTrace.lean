module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionFrobeniusTraceInvariance
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RightDerivedTwistTrace

/-!
# The canonical Frobenius trace under a direct image with base change

Let `h : Z ⟶ Y` be a morphism of schemes over a finite field `k` and `M` a bounded below complex
of sheaves of `Λ`-modules on `Z_étale`. Write `h_k̄ : Z_k̄ ⟶ Y_k̄` for the base change of `h` and
`β : (h_* M)|_{Y_k̄} ⟶ (h_k̄)_*(M|_{Z_k̄})` for the base change map. If `β`, followed by
`(h_k̄)_*` of a resolution of `M|_{Z_k̄}` by injectives, is a quasi-isomorphism — that is, if the
derived base change map `(h_* M)|_{Y_k̄} ⟶ R(h_k̄)_*(M|_{Z_k̄})` is invertible, which by proper
base change ([Stacks, Tag 095T]) is the case for `h` proper and `M` a complex of injectives with
torsion coefficients — then the traces of the canonical Frobenius endomorphisms of
`RΓ(Y_k̄, (h_* M)|_{Y_k̄})` and of `RΓ(Z_k̄, M|_{Z_k̄})` agree, and the two complexes are perfect
together.

This generalizes the closed immersion case
(`Stacks.EtaleCohomology.perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage`,
where `β` is an isomorphism and `(h_k̄)_*` is exact).

## Main results

* `perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage_of_quasiIso`: the two
  Frobenius traces agree.

## References

* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI), part (1)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {Z Y : Over (Spec (.of k))}
  (i : Z ⟶ Y) (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **The canonical Frobenius trace under a direct image.** For a morphism `h : Z ⟶ Y` over `k`
and a bounded below complex `M` on `Z_étale` such that the base change map
`(h_* M)|_{Y_k̄} ⟶ (h_k̄)_*(M|_{Z_k̄})` becomes a quasi-isomorphism after resolving `M|_{Z_k̄}` by
injectives, `RΓ(Y_k̄, (h_* M)|_{Y_k̄})` and `RΓ(Z_k̄, M|_{Z_k̄})` are perfect together and the
traces of their canonical Frobenius endomorphisms agree. -/
theorem perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage_of_quasiIso
    (M : CochainComplex.Plus (EtaleModules.{u, r} Λ Z.left))
    (hq : Functor.BaseChangeQuasiIsoAt
      (etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap i kbar))
      (etaleModuleDirectImage.{u, r} Λ i.left)
      (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar))
      (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Z kbar))
      (etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar)
        (fieldBaseChangeProj Y kbar) (fieldBaseChangeProj Z kbar)
        (fieldBaseChangeMap_comp_fst i kbar)) M) :
    ∃ (_ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
          ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
            (fieldBaseChangeRestriction.{u, r} Λ Y kbar
              ((etaleModuleDirectImage.{u, r} Λ i.left).mapCochainComplexPlus.obj M))))) ↔
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
          ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Z.hom (specAlgebraMap k kbar))).obj
            (fieldBaseChangeRestriction.{u, r} Λ Z kbar M))))),
      ∀ hY hZ, perfectDerivedTrace Λ ⟨_, hY⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard
            ((etaleModuleDirectImage.{u, r} Λ i.left).mapCochainComplexPlus.obj M))) =
        perfectDerivedTrace Λ ⟨_, hZ⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, r} Λ Z kbar p q hcard M)) := by
  obtain ⟨hiff, htr⟩ := Functor.perfectDerivedTrace_derivedTwistEndo_eq_of_baseChangeTrans
    (R := Λ) _ _ _ _ (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar))) _
    (etaleModuleDirectImageComp.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
    (etaleModuleDirectImageComp.{u, r} Λ (geometricFrobeniusBaseChange Z kbar p q hcard)
      (pullback.snd Z.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Z kbar p q hcard).symm)
    (etaleModuleDirectImageComp.{u, r} Λ (fieldBaseChangeMap i kbar)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (fieldBaseChangeMap_comp_snd i kbar).symm)
    (directImageTwistTransfer Λ (fieldBaseChangeMap i kbar)
      (geometricFrobeniusBaseChange Z kbar p q hcard)
      (geometricFrobeniusBaseChange Y kbar p q hcard)
      (geometricFrobeniusBaseChange_comp_fieldBaseChangeMap i p q hcard kbar))
    (directImageTwistTransfer_compat Λ (fieldBaseChangeMap i kbar)
      (geometricFrobeniusBaseChange Z kbar p q hcard)
      (geometricFrobeniusBaseChange Y kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_fieldBaseChangeMap i p q hcard kbar)
      (fieldBaseChangeMap_comp_snd i kbar).symm
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm
      (geometricFrobeniusBaseChange_comp_toBase Z kbar p q hcard).symm)
    (etaleModuleDirectImage.{u, r} Λ i.left)
    (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar))
    (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Z kbar))
    (etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar)
      (fieldBaseChangeProj Y kbar) (fieldBaseChangeProj Z kbar)
      (fieldBaseChangeMap_comp_fst i kbar))
    (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard)
    (frobeniusBaseChangeTwist.{u, r} Λ Z kbar p q hcard)
    (etaleModuleBaseChange_comp_frobeniusBaseChangeTwist Λ i p q hcard kbar) M hq
  refine ⟨hiff, fun hY hZ => ?_⟩
  rw [frobeniusRestrictionCohomologyEndo_eq_derivedTwistEndo,
    frobeniusRestrictionCohomologyEndo_eq_derivedTwistEndo]
  exact htr hY hZ

end Stacks.EtaleCohomology

end
