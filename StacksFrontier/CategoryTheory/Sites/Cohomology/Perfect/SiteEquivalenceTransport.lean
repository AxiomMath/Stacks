module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongAnExactFunctor
public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximationLocal

/-!
# Perfectness and pseudo-coherence along an equivalence of ringed sites

Let `(C, O_C)` and `(D, O_D)` be ringed sites and let `e : C ≌ D` be an equivalence of the
underlying sites, continuous in both directions, together with structure maps
`φ : O_C ⟶ e_* O_D` and `ψ : O_D ⟶ (e^{-1})_* O_C` exhibiting the two pushforwards of modules
as mutually inverse equivalences, the data of Mathlib's
`SheafOfModules.pushforwardPushforwardEquivalence`.  This file proves that the pushforward
`ψ_* : Mod(O_C) ⥤ Mod(O_D)` carries perfect objects (Stacks 08G5) to perfect objects and
`m`-pseudo-coherent objects (Stacks 08FT) to `m`-pseudo-coherent objects.

## The argument

Both statements are instances of the transfer engines
`AlgebraicGeometry.RingedSite.isPerfect_mapDerivedCategory_of_hypotheses` and
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_mapDerivedCategory_of_hypotheses`, with the
continuous functor `e`, the exact functor `ψ_*` (an equivalence) and, on the slice over an object
`W` of `C`, the inverse of the equivalence of slices
`Stacks.SheafOfModules.InternalHom.siteEquivModulesOver`.  The localization square
`(ψ_* A)|_{e(W)} = (A|_W)` transported along the equivalence of slices holds on the nose: both
sides have the sections of `A` over `e^{-1}(V)` at an object `V ⟶ e(W)` of the slice, with the
same action of the structure sheaf.  The family `e(W)` covers the final object of `D` because
every object of `D` is isomorphic to one of them.

The transported unit of each slice is identified with the unit by Mathlib's
`SheafOfModules.unitToPushforwardObjUnit`, which is an isomorphism because `ψ` is
(`Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit`).

## Main results

* `AlgebraicGeometry.RingedSite.isPerfect_pushforward_of_siteEquivalence`
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_pushforward_of_siteEquivalence`

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w dX dY

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules.InternalHom

variable {X Y : RingedSite.{u, v, w}} in
/-- The localized structure map of an equivalence of ringed sites is invertible when the
structure map is. -/
instance isIso_siteEquivPsiOver_hom (eqv : Y.C ≌ X.C)
    [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
    (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      (eqv.inverse.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) [IsIso ψ] (W : Y.C) :
    IsIso (siteEquivPsiOver eqv ψ W) := by
  rw [← ObjectProperty.isIso_hom_iff]
  have : IsIso ψ.hom := by rwa [ObjectProperty.isIso_hom_iff]
  exact inferInstanceAs (IsIso (Functor.whiskerLeft (Over.forget (eqv.functor.obj W)).op ψ.hom))

variable {X Y : RingedSite.{u, v, w}} (eqv : Y.C ≌ X.C)
  [hFc : eqv.functor.IsContinuous Y.J X.J] [hIc : eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.inverse.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)

omit hFc hIc in
/-- The images of the objects of `Y.C` under an essentially surjective functor cover the final
object: every object of `X.C` is isomorphic to one of them, so the sieve of arrows factoring
through one of them is maximal. -/
theorem coversTop_obj_of_equivalence : X.J.CoversTop eqv.functor.obj := by
  intro Z
  have h : Sieve.ofObjects eqv.functor.obj Z = ⊤ := by
    ext V f
    simp only [Sieve.top_apply, iff_true]
    exact ⟨eqv.inverse.obj Z, ⟨f ≫ eqv.counitInv.app Z⟩⟩
  rw [h]
  exact X.J.top_mem Z

/-- The localization square of the pushforward along an equivalence of ringed sites: restricting
`ψ_* A` to `e(W)` is transporting `A|_W` along the equivalence of slices.  Both sides are equal
on the nose. -/
def pushforwardOverSquare (W : Y.C) :
    SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W ⋙
        (siteEquivModulesOver.{u, v, w, w} eqv φ ψ H₁ H₂ W).inverse ≅
      SheafOfModules.pushforward.{w} ψ ⋙
        SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (eqv.functor.obj W) :=
  Iso.refl _

/-- The transported unit of a slice is the unit, when the structure map `ψ` is invertible. -/
def pushforwardUnitIso [hψ : IsIso ψ] (W : Y.C) :
    (siteEquivModulesOver.{u, v, w, w} eqv φ ψ H₁ H₂ W).inverse.obj
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W)) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (eqv.functor.obj W)) :=
  haveI := Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit (siteEquivPsiOver eqv ψ W)
  (asIso (SheafOfModules.unitToPushforwardObjUnit
    (F := (Over.postEquiv W eqv).inverse) (siteEquivPsiOver eqv ψ W))).symm

variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ W : Y.C, HasSheafify (Y.J.over W) AddCommGrpCat.{w}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

omit [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ W : Y.C, HasSheafify (Y.J.over W) AddCommGrpCat.{w}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- The pushforward along an equivalence of ringed sites is additive. -/
theorem pushforward_additive_of_siteEquivalence : (SheafOfModules.pushforward.{w} ψ).Additive where
  map_add := by intros; ext; rfl

omit [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ W : Y.C, HasSheafify (Y.J.over W) AddCommGrpCat.{w}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
include φ H₁ H₂ in
/-- The pushforward along an equivalence of ringed sites is exact, being an equivalence. -/
theorem preservesFiniteLimits_pushforward_of_siteEquivalence :
    PreservesFiniteLimits (SheafOfModules.pushforward.{w} ψ) :=
  have : (SheafOfModules.pushforward.{w} ψ).IsEquivalence :=
    (SheafOfModules.pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂).symm.isEquivalence_functor
  inferInstance

omit [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ W : Y.C, HasSheafify (Y.J.over W) AddCommGrpCat.{w}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
include φ H₁ H₂ in
/-- The pushforward along an equivalence of ringed sites is right exact, being an equivalence. -/
theorem preservesFiniteColimits_pushforward_of_siteEquivalence :
    PreservesFiniteColimits (SheafOfModules.pushforward.{w} ψ) :=
  have : (SheafOfModules.pushforward.{w} ψ).IsEquivalence :=
    (SheafOfModules.pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂).symm.isEquivalence_functor
  inferInstance

/-- **The pushforward along an equivalence of ringed sites preserves perfectness.**  If `E` is a
perfect object of `D(O_C)` then `ψ_* E` is a perfect object of `D(O_D)`, for `ψ` invertible. -/
theorem isPerfect_pushforward_of_siteEquivalence
    [hψ : IsIso ψ]
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hE : Y.IsPerfect E) :
    haveI := pushforward_additive_of_siteEquivalence eqv ψ
    haveI := preservesFiniteLimits_pushforward_of_siteEquivalence eqv φ ψ H₁ H₂
    haveI := preservesFiniteColimits_pushforward_of_siteEquivalence eqv φ ψ H₁ H₂
    X.IsPerfect ((SheafOfModules.pushforward.{w} ψ).mapDerivedCategory.obj E) :=
  isPerfect_mapDerivedCategory_of_hypotheses eqv.functor (SheafOfModules.pushforward.{w} ψ)
    (fun W => (siteEquivModulesOver.{u, v, w, w} eqv φ ψ H₁ H₂ W).inverse)
    (pushforward_additive_of_siteEquivalence eqv ψ)
    (preservesFiniteLimits_pushforward_of_siteEquivalence eqv φ ψ H₁ H₂)
    (preservesFiniteColimits_pushforward_of_siteEquivalence eqv φ ψ H₁ H₂)
    (fun W => ⟨by intros; ext; rfl⟩) (fun _ => inferInstance)
    (fun _ => inferInstance) inferInstance (coversTop_obj_of_equivalence eqv)
    (pushforwardUnitIso eqv φ ψ H₁ H₂)
    (pushforwardOverSquare eqv φ ψ H₁ H₂) E hE

/-- **The pushforward along an equivalence of ringed sites preserves `m`-pseudo-coherence.** If
`E` is an `m`-pseudo-coherent object of `D(O_C)` then so is `ψ_* E` in `D(O_D)`. -/
theorem isPseudoCoherentFrom_pushforward_of_siteEquivalence
    [hψ : IsIso ψ]
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (m : ℤ) (hE : Y.IsPseudoCoherentFrom E m) :
    haveI := pushforward_additive_of_siteEquivalence eqv ψ
    haveI := preservesFiniteLimits_pushforward_of_siteEquivalence eqv φ ψ H₁ H₂
    haveI := preservesFiniteColimits_pushforward_of_siteEquivalence eqv φ ψ H₁ H₂
    X.IsPseudoCoherentFrom ((SheafOfModules.pushforward.{w} ψ).mapDerivedCategory.obj E) m :=
  isPseudoCoherentFrom_mapDerivedCategory_of_hypotheses eqv.functor
    (SheafOfModules.pushforward.{w} ψ)
    (fun W => (siteEquivModulesOver.{u, v, w, w} eqv φ ψ H₁ H₂ W).inverse)
    (pushforward_additive_of_siteEquivalence eqv ψ)
    (preservesFiniteLimits_pushforward_of_siteEquivalence eqv φ ψ H₁ H₂)
    (preservesFiniteColimits_pushforward_of_siteEquivalence eqv φ ψ H₁ H₂)
    (fun W => ⟨by intros; ext; rfl⟩) (fun _ => inferInstance)
    (fun _ => inferInstance) inferInstance (coversTop_obj_of_equivalence eqv)
    (pushforwardUnitIso eqv φ ψ H₁ H₂)
    (pushforwardOverSquare eqv φ ψ H₁ H₂) E m hE

end AlgebraicGeometry.RingedSite

end
