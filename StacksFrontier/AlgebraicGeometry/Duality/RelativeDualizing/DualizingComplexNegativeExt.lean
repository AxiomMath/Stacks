module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingModelSliceSite
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModel
public import StacksFrontier.RingTheory.Dualizing.LocalizationCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.SelfExtOnACollectionOfOpens

/-!
# Dualizing complexes have no negative self-Ext

Let `X` be a locally Noetherian scheme and `K` a dualizing complex on `X` ([Stacks, Tag 0A87]).
Then `Ext^n(K|_W, K|_W) = 0` for every open `W ⊆ X` and every `n < 0`. Over an affine open `V`
this holds for every `n ≠ 0`: `K|_V` is the complex associated to a dualizing complex `ω` over
`Γ(X, V)`, and `Ext^n_{Γ(X, V)}(ω, ω)` is the degree-`n` cohomology of `R Hom(ω, ω) = Γ(X, V)`.
Negative degrees then pass from the affine opens to every open by [Stacks, Tag 0D66], part (2).

## Main results

* `Dualizing.IsDualizingComplex.subsingleton_shiftedHom_self`: over a Noetherian ring,
  `Hom_{D(A)}(ω, ω[n]) = 0` for a dualizing complex `ω` and `n ≠ 0`.
* `Stacks.Duality.subsingleton_shiftedHom_overFunctor_of_isAffineOpen`: the same for the
  restriction of a dualizing complex to an affine open.
* `Stacks.Duality.subsingleton_shiftedHom_overFunctor_of_isDualizingComplex`: negative self-Ext
  of the restriction of a dualizing complex to any open vanishes.

## References

* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe w u

namespace Dualizing

/-- **A dualizing complex has no self-Ext away from degree zero.** For a dualizing complex `ω`
over a Noetherian ring `A` and `n ≠ 0`, `Hom_{D(A)}(ω, ω[n]) = 0`: on a bounded injective
representative `I` it is the degree-`n` cohomology of `Hom^•(I, I)`, which the homothety
`A[0] ⟶ Hom^•(I, I)` identifies with that of `A[0]`. -/
theorem IsDualizingComplex.subsingleton_shiftedHom_self {A : Type u} [CommRing A]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {ω : DerivedCategory (ModuleCat.{u} A)} (hω : IsDualizingComplex ω) {n : ℤ} (hn : n ≠ 0) :
    Subsingleton (ShiftedHom ω ω n) := by
  obtain ⟨a, b, I, hIGE, hILE, hIinj, ⟨eI⟩⟩ := hω.finiteInjectiveDimension
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  have hz := isZero_homology_homComplexR_of_quasiIso_homothety.{u, u} I
    (hω.homothetyQuasiIso I ⟨eI.symm⟩ hIinj ⟨a, b, hIGE, hILE⟩) n hn
  let H := CochainComplex.HomComplexR A I I
  let V := forget₂ (ModuleCat.{u} A) AddCommGrpCat
  let eV : (H.homology n) ≃+ (I.HomComplex I).homology n :=
    ((H.sc n).mapHomologyIso V).symm.addCommGroupIsoToAddEquiv
  let eClass := (CochainComplex.HomComplex.homologyAddEquiv I I n).trans
    (cohomologyClassRHomAddEquivOfIsKInjective I I n)
  have : Subsingleton (H.homology n) := ModuleCat.isZero_iff_subsingleton.mp hz
  have := Equiv.subsingleton (eV.trans eClass).symm.toEquiv
  let q := HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)
  let η := DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)
  let eSrc : DerivedCategory.Qh.obj (q.obj I) ≅ ω := η.app I ≪≫ eI.symm
  let eTgt : DerivedCategory.Qh.obj (q.obj (I⟦n⟧)) ≅ ω⟦n⟧ :=
    η.app (I⟦n⟧) ≪≫ (DerivedCategory.Q.commShiftIso n).app I ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) n).mapIso eI.symm
  exact Equiv.subsingleton (Iso.homCongr eSrc eTgt).symm

end Dualizing

namespace Stacks.Duality

/-- A full functor commuting with the shift carries the vanishing of a shifted Hom group to the
images. -/
theorem subsingleton_shiftedHom_map_of_full {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.Full] [F.CommShift ℤ] {a b : C} {n : ℤ}
    (h : Subsingleton (ShiftedHom a b n)) : Subsingleton (ShiftedHom (F.obj a) (F.obj b) n) := by
  refine ⟨fun g₁ g₂ => ?_⟩
  have e : F.preimage (g₁ ≫ (F.commShiftIso n).inv.app b) =
      F.preimage (g₂ ≫ (F.commShiftIso n).inv.app b) := h.elim _ _
  simpa only [Functor.map_preimage, cancel_mono] using congrArg F.map e

/-- **Being a dualizing complex does not depend on the model of `D(𝒪_X)`**: a dualizing complex
at the locally small model of [Stacks, Tag 079Q] is one at the standard model, the two models
having the same objects and computing derived restriction to an open at the same object. -/
theorem isDualizingComplex_standard_of_isDualizingComplex {X : Scheme.{u}} [IsLocallyNoetherian X]
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) :
    @IsDualizingComplex X _ (HasDerivedCategory.standard X.Modules)
      ((Stacks.Injectives.grothendieckModelEquiv X.Modules).inverse.obj K) := by
  intro U hU
  obtain ⟨ω, hω, ⟨i⟩⟩ := hK U hU
  unfold HasDualizingModelOn
  exact ⟨ω, hω, ⟨Stacks.Injectives.mapDerivedCategoryObjIso X.Modules
    (hd₂ := HasDerivedCategory.standard U.toScheme.Modules)
    (Scheme.Modules.restrictFunctor U.ι) K ≪≫ i⟩⟩

section Scheme

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-- **The restriction of a dualizing complex to an affine open has no self-Ext away from degree
zero.** Over an affine open `V ⊆ X`, read on the slice site, `K|_V` is the complex associated to
a dualizing complex `ω` over `Γ(X, V)` (transported along `V ≅ Spec Γ(X, V)`), and the derived
functor of `~` is fully faithful, so its self-Ext is that of `ω`. -/
theorem subsingleton_shiftedHom_overFunctor_of_isAffineOpen (V : X.Opens) (hV : IsAffineOpen V)
    [HasSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]
    [PreservesFiniteLimits (SheafOfModules.overFunctor.{u} X.ringCatSheaf V)]
    [PreservesFiniteColimits (SheafOfModules.overFunctor.{u} X.ringCatSheaf V)]
    (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K) {n : ℤ} (hn : n ≠ 0) :
    Subsingleton (ShiftedHom
      ((SheafOfModules.overFunctor.{u} X.ringCatSheaf V).mapDerivedCategory.obj K)
      ((SheafOfModules.overFunctor.{u} X.ringCatSheaf V).mapDerivedCategory.obj K) n) := by
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  obtain ⟨ω, hω, ⟨i⟩⟩ := exists_isDualizingComplex_iso_overFunctor_of_isDualizingComplex V K hV hK
  let E := Scheme.Modules.overEquiv V
  let k := hV.isoSpec.hom
  -- through the fully faithful derived functor of `~`
  have h₁ : Subsingleton (ShiftedHom ((tilde.functor Γ(X, V)).mapDerivedCategory.obj ω)
      ((tilde.functor Γ(X, V)).mapDerivedCategory.obj ω) n) :=
    let := (StandardModel.mapDerivedCategoryFullyFaithful Γ(X, V)).full
    subsingleton_shiftedHom_map_of_full _ (hω.subsingleton_shiftedHom_self hn)
  -- through restriction along the isomorphism `V ≅ Spec Γ(X, V)`
  have h₂ : Subsingleton (ShiftedHom
      ((Scheme.Modules.restrictFunctor k).mapDerivedCategory.obj
        ((tilde.functor Γ(X, V)).mapDerivedCategory.obj ω))
      ((Scheme.Modules.restrictFunctor k).mapDerivedCategory.obj
        ((tilde.functor Γ(X, V)).mapDerivedCategory.obj ω)) n) := by
    have := Stacks.DerivedGlueing.faithful_mapDerivedCategory_of_comp
      (Scheme.Modules.restrictFunctor (inv k)) (Scheme.Modules.restrictFunctor (inv (inv k)))
      (Scheme.Modules.restrictFunctorCompInvIso (inv k))
    refine Stacks.DerivedGlueing.subsingleton_shiftedHom_of_faithful
      (Scheme.Modules.restrictFunctor (inv k)).mapDerivedCategory _ _ n ?_
    let e := (Stacks.DerivedGlueing.mapDerivedCategoryCompIso (Scheme.Modules.restrictFunctor k)
      (Scheme.Modules.restrictFunctor (inv k)) ≪≫
        Stacks.DerivedGlueing.mapDerivedCategoryCongr
          (Scheme.Modules.restrictFunctorCompInvIso k) ≪≫
        Stacks.Homology.mapDerivedCategoryIdIso).app
      ((tilde.functor Γ(X, V)).mapDerivedCategory.obj ω)
    exact Stacks.DerivedGlueing.subsingleton_shiftedHom_of_iso e e n h₁
  have h₃ : Subsingleton (ShiftedHom
      ((tilde.functor Γ(X, V) ⋙ Scheme.Modules.restrictFunctor k).mapDerivedCategory.obj ω)
      ((tilde.functor Γ(X, V) ⋙ Scheme.Modules.restrictFunctor k).mapDerivedCategory.obj ω) n) :=
    let e := (Stacks.DerivedGlueing.mapDerivedCategoryCompIso (tilde.functor Γ(X, V))
      (Scheme.Modules.restrictFunctor k)).symm.app ω
    Stacks.DerivedGlueing.subsingleton_shiftedHom_of_iso e e n h₂
  -- back through the equivalence between the slice site and the open subscheme
  have := Stacks.DerivedGlueing.faithful_mapDerivedCategory_of_comp E.functor E.inverse
    E.unitIso.symm
  exact Stacks.DerivedGlueing.subsingleton_shiftedHom_of_faithful E.functor.mapDerivedCategory
    _ _ n (Stacks.DerivedGlueing.subsingleton_shiftedHom_of_iso i i n h₃)

/-- **Negative self-Ext of a dualizing complex vanishes on every open.** For a dualizing complex
`K` on a locally Noetherian scheme `X`, an open `W ⊆ X` and `n < 0`, `Ext^n(K|_W, K|_W) = 0`,
restriction being read on the slice site. The affine opens form a basis on which this holds
(`Stacks.Duality.subsingleton_shiftedHom_overFunctor_of_isAffineOpen`), and negative Ext extends
from a basis to every open by [Stacks, Tag 0D66], part (2). -/
theorem subsingleton_shiftedHom_overFunctor_of_isDualizingComplex
    (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K) (W : X.Opens) {n : ℤ}
    (hn : n < 0) :
    Subsingleton (ShiftedHom
      ((Stacks.Cohomology.UnboundedHigherDirectImage.preimageRestrict (𝟙 X.toRingedSpace) W).obj K)
      ((Stacks.Cohomology.UnboundedHigherDirectImage.preimageRestrict (𝟙 X.toRingedSpace) W).obj K)
      n) :=
  Stacks.Cohomology.UnboundedHigherDirectImage.subsingleton_shiftedHom_preimageRestrict_of_isBasis
    X.isBasis_affineOpens (𝟙 X.toRingedSpace) K K
    (fun V hV _ hi => subsingleton_shiftedHom_overFunctor_of_isAffineOpen V hV K hK hi.ne) W n hn

/-- **`Ext^{-1}` of a dualizing complex restricted to an open vanishes**, restriction being the
derived pullback along the open immersion `W ⟶ X`: every morphism `(K|_W)[1] ⟶ K|_W` is zero.
This is `Stacks.Duality.subsingleton_shiftedHom_overFunctor_of_isDualizingComplex` in degree `-1`,
carried from the slice site over `W` to the open subspace `W`. -/
theorem eq_zero_of_isDualizingComplex (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K)
    (W : X.Opens)
    (g : ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        W.ι.toLRSHom.toShHom).obj K)⟦(1 : ℤ)⟧ ⟶
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        W.ι.toLRSHom.toShHom).obj K) :
    g = 0 := by
  let O := structureSheafRing X.toRingedSpace
  let S := Stacks.DerivedGlueing.sliceToSubspace O W
  let T := Stacks.DerivedGlueing.subspaceToSlice O W
  let B := (SheafOfModules.overFunctor.{u} O W).mapDerivedCategory.obj K
  have := Stacks.DerivedGlueing.faithful_mapDerivedCategory_of_comp T S
    (W.sheafOfModulesEquivOver O).counitIso
  let e : T.mapDerivedCategory.obj (S.mapDerivedCategory.obj B) ≅ B :=
    (Stacks.DerivedGlueing.mapDerivedCategoryCompIso S T ≪≫
      Stacks.DerivedGlueing.mapDerivedCategoryCongr (W.sheafOfModulesEquivOver O).unitIso.symm ≪≫
      Stacks.Homology.mapDerivedCategoryIdIso).app B
  have h₁ : Subsingleton (ShiftedHom (S.mapDerivedCategory.obj B)
      (S.mapDerivedCategory.obj B) (-1)) :=
    Stacks.DerivedGlueing.subsingleton_shiftedHom_of_faithful T.mapDerivedCategory _ _ _
      (Stacks.DerivedGlueing.subsingleton_shiftedHom_of_iso e e _
        (subsingleton_shiftedHom_overFunctor_of_isDualizingComplex K hK W (by norm_num)))
  let A := (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    W.ι.toLRSHom.toShHom).obj K
  let eA : A ≅ S.mapDerivedCategory.obj B :=
    (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso
        X.toRingedSpace W).app K ≪≫
      (Stacks.DerivedGlueing.mapDerivedCategoryCompIso
        (SheafOfModules.overFunctor.{u} O W) S).symm.app K
  have h₃ : Subsingleton (A⟦(1 : ℤ)⟧ ⟶ A) :=
    @Equiv.subsingleton _ _
      ((shiftEquiv (DerivedCategory (SheafOfModules.{u} (ExtensionByZeroModules.resRing W O)))
        (1 : ℤ)).toAdjunction.homEquiv _ _)
      (Stacks.DerivedGlueing.subsingleton_shiftedHom_of_iso eA eA _ h₁)
  exact h₃.elim g 0

end Scheme

end Stacks.Duality

end
