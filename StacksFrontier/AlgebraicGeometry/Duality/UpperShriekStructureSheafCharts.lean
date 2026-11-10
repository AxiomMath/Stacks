module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.AffineRightAdjointDerivedHom
public import StacksFrontier.RingTheory.Dualizing.LocalizationTransportModels
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.Composition
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.AffineChart
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.AffineChartPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonAffine
public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeOpens
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.ClosureCompactification
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.OpenRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekStructureSheafChartsPredicate
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.ProperRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelowPlus
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulRegularRightAdjoint.SheafHom
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FibreDimensionBound
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.TorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Composition
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekChartModels
public import StacksFrontier.RingTheory.Dualizing.LocalizationTransport

/-!
# The affine chart description of `f^!E`

[Stacks, Tag 0BV2] computes `f^!` on affine charts: over affine opens `U ⊆ f⁻¹(V)` with
`V = Spec R`, `U = Spec A`, a presentation `A = P/I` with `P = R[x_1, …, x_n]`, and `E|_V ≅ K~`,

  `(f^!E)|_U ≅ (RHom_P(A, K ⊗ᴸ_R P)[n])~`.

This file assembles that description for the upper shriek functor
`Stacks.Duality.upperShriek f j` of every compactification `j`, through the compactification of
the chart `U ⟶ V` by its closure in `Pⁿ_V`.

## Main results

* `Stacks.Duality.nonempty_twistedInverseImage_specMap_derivedTilde_iso` — the twisted inverse
  image of `Spec φ` is `RHom_R(S, -)` on associated sheaves ([Stacks, Tag 0A9F]).
* `Stacks.Duality.nonempty_twistedInverseImage_chartImmersion_iso` — for a presentation
  `P ⟶ Γ(X, U)` in `n` variables, the twisted inverse image of `U ⟶ Spec P` carries `N~[n]` to
  the associated sheaf of `RHom_P(Γ(X, U), N)[n]`.
* `Stacks.Duality.upperShriekCharts` — the chart description of `f^!E` for `E ∈ D⁺_QCoh(𝒪_Y)`
  ([Stacks, Tag 0BV2], second assertion).
* `Stacks.Duality.upperShriekStructureSheafCharts` — the chart description of `f^!𝒪_Y`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

/-! ### The affine step -/

/-- **The twisted inverse image of `Spec φ` on an associated sheaf**: for `φ : R ⟶ S` and
`M ∈ D(R)`, `a_{Spec φ}(M̃) ≅ RHom_R(S, M)~`. This is [Stacks, Tag 0A9F] read at the twisted
inverse image `Stacks.Duality.twistedInverseImage`. -/
theorem nonempty_twistedInverseImage_specMap_derivedTilde_iso {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : DerivedCategory (ModuleCat.{u} R)) :
    Nonempty ((twistedInverseImage (Spec.map φ)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj ((derivedTilde R).obj M) ≅
      (derivedTilde S).obj ((Dualizing.AnyModel.derivedHom.{u, u, u, u, u} φ.hom).obj M)) :=
  let ⟨e⟩ := derivedTilde_comp_rightAdjoint_derivedQuasicoherentPushforwardIsoDerivedHom φ
    (twistedInverseImageAdjunction (Spec.map φ)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
  ⟨e.app M⟩

end Stacks.Duality

namespace Stacks.Duality

/-! ### The twisted inverse image of an isomorphism is restriction -/

section Iso

variable {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y] (e : X ⟶ Y) [IsIso e] [IsOpenImmersion e]

/-- **The twisted inverse image of an isomorphism `e` is restriction along `e`**: restriction
along `e` is left adjoint to `Re_*`, which is an equivalence with quasi-inverse `R(e⁻¹)_*`, and
`a_e` is right adjoint to `Re_*`; both are therefore `R(e⁻¹)_*`. -/
def twistedInverseImageIsoRestrictOfIsIso :
    twistedInverseImage e (isQuasicoherent_homology_derivedPushforward_of_qcqs e) ≅
      OpenImmersion.restrictedDerivedRestrict e :=
  let E := quasiCoherentDerivedPushforwardEquivalenceOfIsIso e
    (isQuasicoherent_homology_derivedPushforward_of_qcqs e)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (inv e))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 Y))
  twistedInverseImageIsoOfIsIso e _ _
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X))
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 Y)) ≪≫
    (Adjunction.leftAdjointUniq
      (OpenImmersion.restrictedDerivedRestrictAdjunction e) E.symm.toAdjunction).symm

end Iso

end Stacks.Duality

namespace Stacks.Duality

/-! ### Derived Hom at the two models -/

section DerivedHomModel

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)

/-- **`RHom_A(B, -)` at the standard and the locally small model agree on objects**: both are
total right derived functors of coextension of scalars, matched by the comparison equivalences of
the two models, which are the identity on objects. -/
def derivedHomStandardIsoLocallySmall
    (M : @DerivedCategory (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _)) :
    @Functor.obj _ _ _ _
        (Dualizing.AnyModel.derivedHom.{u, u, u, u, u} φ) (M : DerivedCategory (ModuleCat.{u} A)) ≅
      ((Stacks.Injectives.grothendieckModelEquiv (ModuleCat.{u} B)).functor.obj
        ((@Dualizing.AnyModel.derivedHom.{u, u, u, u + 1, u + 1} A B _ _
          (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) φ).obj M)) :=
  ((StacksDraft.DerivedModel.rightDerivedModelIso
    (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
    (L₁ := @DerivedCategory.Qh (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _))
    (L₂ := @DerivedCategory.Qh (ModuleCat.{u} A) _ _ inferInstance)
    (G := (Stacks.Injectives.grothendieckModelEquiv (ModuleCat.{u} A)).functor)
    (J := (Stacks.Injectives.grothendieckModelEquiv (ModuleCat.{u} B)).functor)
    (Functor.totalRightDerivedUnit _ _ _) (Functor.totalRightDerivedUnit _ _ _)
    (StacksDraft.DerivedModel.shrinkComparisonQhIso (ModuleCat.{u} A)).symm
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (StacksDraft.DerivedModel.shrinkComparisonQhIso (ModuleCat.{u} B)).symm)).app M).symm

end DerivedHomModel

end Stacks.Duality

namespace Stacks.Duality

/-! ### The affine chart -/

section AffineChart

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) {R : CommRingCat.{u}}
  {φ : R →+* Γ(X, U)} (p : Dualizing.PolynomialPresentation φ)

/-- The closed immersion `U ≅ Spec Γ(X, U) ⟶ Spec P` of a polynomial presentation `P ⟶ Γ(X, U)`
of the chart ring. -/
abbrev chartImmersion : U.toScheme ⟶ Spec (CommRingCat.of p.Poly) :=
  hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom p.toRingHom)

/-- **The affine chart computation.** For a polynomial presentation `P ⟶ A = Γ(X, U)` of
`R ⟶ A` in `n` variables and `N ∈ D(P)`, the twisted inverse image of `U ⟶ Spec P` carries
`Ñ[n]` to the associated sheaf of `RHom_P(A, N)[n]`. -/
theorem nonempty_twistedInverseImage_chartImmersion_iso
    (N : @DerivedCategory (ModuleCat.{u} p.Poly) _ _ (HasDerivedCategory.standard _)) :
    letI : IsAffine U.toScheme := hU
    Nonempty (((twistedInverseImage (chartImmersion U hU p)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          (((derivedTilde (CommRingCat.of p.Poly)).obj
            ((Stacks.Injectives.grothendieckModelEquiv (ModuleCat.{u} p.Poly)).functor.obj N))⟦
            (p.variableCount : ℤ)⟧)).obj ≅
      (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _ _
        (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) _ _ _).obj
          (((Dualizing.derivedHom.{u, 0, u} p.toRingHom).obj N)⟦(p.variableCount : ℤ)⟧)) := by
  let : IsAffine U.toScheme := hU
  let P := CommRingCat.of p.Poly
  let ψ : P ⟶ Γ(X, U) := CommRingCat.ofHom p.toRingHom
  let e := hU.isoSpec.hom
  let n : ℤ := p.variableCount
  let aψ := twistedInverseImage (Spec.map ψ)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (Spec.map ψ))
  let := (twistedInverseImageAdjunction (Spec.map ψ)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (Spec.map ψ))).rightAdjointCommShift ℤ
  let N' := (Stacks.Injectives.grothendieckModelEquiv (ModuleCat.{u} p.Poly)).functor.obj N
  obtain ⟨e₁⟩ := nonempty_twistedInverseImage_specMap_derivedTilde_iso ψ N'
  let O := (derivedTilde P).obj N'
  let ιQ := ObjectProperty.ι (DerivedCategoryB.derivedCategoryB (A := (Spec Γ(X, U)).Modules)
    (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf))
  let Rs := (Scheme.Modules.restrictFunctor e).mapDerivedCategory
  let T := (tilde.functor Γ(X, U)).mapDerivedCategory
  let i₁ := (ObjectProperty.ι _).mapIso
    ((twistedInverseImageCompIso e (Spec.map ψ) _ _
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).app (O⟦n⟧) ≪≫
      (twistedInverseImageIsoRestrictOfIsIso e).app (aψ.obj (O⟦n⟧)))
  let i₂ : Rs.obj (aψ.obj (O⟦n⟧)).obj ≅ (Rs.obj (aψ.obj O).obj)⟦n⟧ :=
    Rs.mapIso (ιQ.mapIso ((aψ.commShiftIso n).app O) ≪≫ (ιQ.commShiftIso n).app _) ≪≫
      (Rs.commShiftIso n).app _
  let i₃ : Rs.obj (aψ.obj O).obj ≅ (T ⋙ Rs).obj _ :=
    Rs.mapIso ((ObjectProperty.ι _).mapIso e₁)
  let F := tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor e
  let i₄ : (T ⋙ Rs).obj ((Dualizing.AnyModel.derivedHom.{u, u, u, u, u} ψ.hom).obj N') ≅
      F.mapDerivedCategory.obj
        ((@Dualizing.AnyModel.derivedHom.{u, u, u, u + 1, u + 1} P Γ(X, U) _ _
          (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) ψ.hom).obj N) :=
    ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).app _).symm ≪≫
      F.mapDerivedCategory.mapIso (derivedHomStandardIsoLocallySmall ψ.hom _)
  let Z₀ := (Dualizing.derivedHom.{u, 0, u} p.toRingHom).obj N
  let i₆ := (Stacks.Injectives.mapDerivedCategoryObjIso (ModuleCat.{u} Γ(X, U)) F Z₀).symm
  let i₇ := ((@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _ _ F _ _ _
    ).commShiftIso n).app Z₀
  exact ⟨i₁ ≪≫ i₂ ≪≫ (shiftFunctor _ n).mapIso (i₃ ≪≫ i₄ ≪≫ i₆) ≪≫ i₇.symm⟩

end AffineChart

end Stacks.Duality

namespace Stacks.Duality

/-! ### The chart immersion lies over the restriction of `f` -/

/-- For affine opens `U ⊆ f⁻¹(V)` and a polynomial presentation `P ⟶ Γ(X, U)` of the chart ring
map `Γ(Y, V) ⟶ Γ(X, U)`, the chart immersion `U ⟶ Spec P` followed by `Spec P ⟶ Spec Γ(Y, V) ≅ V`
is the restriction `U ⟶ V` of `f`. -/
theorem chartImmersion_comp_specMap_C_comp_isoSpec_inv {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) (p : Dualizing.PolynomialPresentation (f.appLE V U hUV).hom) :
    chartImmersion U hU p ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) ≫ hV.isoSpec.inv =
      f.resLE V U hUV := by
  rw [← cancel_mono V.ι, Scheme.Hom.resLE_comp_ι]
  simp only [Category.assoc, IsAffineOpen.isoSpec_inv_ι]
  rw [← Spec.map_comp_assoc]
  have hcomp : CommRingCat.ofHom (MvPolynomial.C : Γ(Y, V) →+* p.Poly) ≫
      CommRingCat.ofHom p.toRingHom = f.appLE V U hUV := by
    ext1; exact p.commutes
  rw [hcomp, IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV, ← Category.assoc,
    IsAffineOpen.isoSpec_hom_fromSpec]

end Stacks.Duality

namespace Stacks.Duality

/-! ### Transport of tilde models -/

section TildeTransport

/-- **A tilde model, read at the locally small model of `D(𝒪_U)`.** `IsTildeModelOnAnyModel` reads
`D(𝒪_U)` at the standard model; the comparison equivalence of the two models carries its
isomorphism to the same isomorphism at the locally small model. -/
theorem nonempty_restrict_iso_of_isTildeModelOn {X : Scheme.{u}} [IsLocallyNoetherian X]
    {K : DerivedCategory X.Modules} {U : X.Opens} {hU : IsAffineOpen U}
    {ω : @DerivedCategory (ModuleCat.{u} Γ(X, U)) _ _ (HasDerivedCategory.standard _)}
    (h : IsTildeModelOnAnyModel K U hU ω) :
    Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _ _
        (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) _ _ _).obj ω) :=
  let ⟨e⟩ := h
  ⟨((Stacks.Injectives.mapDerivedCategoryTargetModelIso U.toScheme.Modules
      (Scheme.Modules.restrictFunctor U.ι)).app K).symm ≪≫
    (Stacks.Injectives.grothendieckModelEquiv U.toScheme.Modules).functor.mapIso e ≪≫
    (Stacks.Injectives.mapDerivedCategoryTargetModelIso U.toScheme.Modules
      (hd₁ := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U)))
      (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom)).app ω⟩

/-- **A tilde model on `Z ≅ Spec R` is the associated sheaf after restriction back to `Spec R`.**
If `K|_Z` is the associated sheaf of `ω ∈ D(R)` transported along `eZ : Z ≅ Spec R`, then
restricting `K` along `eZ⁻¹` gives `ω~`. -/
def restrictedDerivedRestrictInvIsoDerivedTilde {Z : Scheme.{u}} {R : CommRingCat.{u}}
    (eZ : Z ≅ Spec R) (K : quasiCoherentDerivedCategory Z)
    (ω : @DerivedCategory (ModuleCat.{u} R) _ _ (HasDerivedCategory.standard _))
    (e : K.obj ≅ (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _ _
      (tilde.functor R ⋙ Scheme.Modules.restrictFunctor eZ.hom) _ _ _).obj ω) :
    (OpenImmersion.restrictedDerivedRestrict eZ.inv).obj K ≅
      (derivedTilde R).obj ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj ω) :=
  let T := (derivedTilde R).obj ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj ω)
  let e' : K ≅ (OpenImmersion.restrictedDerivedRestrict eZ.hom).obj T :=
    ObjectProperty.isoMk _ (e ≪≫
      Stacks.Injectives.mapDerivedCategoryObjIso (ModuleCat.{u} R)
        (tilde.functor R ⋙ Scheme.Modules.restrictFunctor eZ.hom) ω ≪≫
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).app _)
  (restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback eZ.inv).app K ≪≫
    (quasiCoherentDerivedPullback' eZ.inv).mapIso (e' ≪≫
      (restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback eZ.hom).app T) ≪≫
    (quasiCoherentDerivedPullbackCompIso eZ.inv eZ.hom).app T ≪≫
    (quasiCoherentDerivedPullbackCongr eZ.inv_hom_id).app T ≪≫
    (quasiCoherentDerivedPullbackIdIso _ _).app T

/-- **Derived pullback along the polynomial algebra of a presentation, on associated sheaves**:
`L(Spec C)^*(ω~) ≅ (ω ⊗_R P)~` for the flat `C : R ⟶ P`, the affine comparison square of
[Stacks, Tag 08DW] part (2) with the derivation removed by flatness. -/
def quasiCoherentDerivedPullbackSpecMapDerivedTildeIso {R : CommRingCat.{u}} {A : Type u}
    [CommRing A] {φ : R →+* A} (p : Dualizing.PolynomialPresentation φ)
    (ω : @DerivedCategory (ModuleCat.{u} R) _ _ (HasDerivedCategory.standard _)) :
    (quasiCoherentDerivedPullback' (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : R →+* p.Poly)))).obj
          ((derivedTilde R).obj ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj ω)) ≅
      (derivedTilde (CommRingCat.of p.Poly)).obj
        ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj
          (p.derivedExtension.{u, u}.obj ω)) :=
  letI : Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (MvPolynomial.C : R →+* p.Poly)) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _ p.flat_C
  ObjectProperty.isoMk _
    ((affinePullbackComparison R (CommRingCat.of p.Poly)
        (CommRingCat.ofHom MvPolynomial.C)).app _ ≪≫
      (tilde.functor (CommRingCat.of p.Poly)).mapDerivedCategory.mapIso
        ((Dualizing.totalDerivedExtensionScalarsIsoExtendScalarsOfModels _).app _ ≪≫
          (Stacks.Injectives.mapDerivedCategoryObjIso (ModuleCat.{u} R)
            (ModuleCat.extendScalars.{u, u, u} (MvPolynomial.C : R →+* p.Poly)) ω).symm ≪≫
          ((Stacks.Injectives.mapDerivedCategoryTargetModelIso (ModuleCat.{u} p.Poly)
            (hd₁ := HasDerivedCategory.standard (ModuleCat.{u} R))
            (ModuleCat.extendScalars.{u, u, u} (MvPolynomial.C : R →+* p.Poly))).app ω).symm))

end TildeTransport

end Stacks.Duality

namespace Stacks.Duality.ChartCompactification

open AlgebraicGeometry _root_.Stacks.Duality.ProjectiveSpace
  _root_.AlgebraicGeometry.ProjectiveSpace Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] {X Y : FTS S} (f : X ⟶ Y)
  {U : X.left.Opens} (hU : IsAffineOpen U) {V : Y.left.Opens} (hV : IsAffineOpen V)
  (hUV : U ≤ f.left ⁻¹ᵁ V) (p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom)

/-- The projection `Pⁿ_V ⟶ V`. -/
abbrev π :
    AlgebraicGeometry.Proj (polyGrading Γ(Y.left, V) p.variableCount) ⟶
      (FTS.ofAffineOpen Y V hV).left :=
  projToSpecCoeff Γ(Y.left, V) p.variableCount ≫ hV.isoSpec.inv

/-- The projection `π f hV hUV p : Pⁿ_V ⟶ V` is a proper morphism. -/
instance : IsProper (π f hV hUV p) :=
  MorphismProperty.comp_mem @IsProper _ _
    (Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff Γ(Y.left, V) p.variableCount)
    (inferInstance : IsProper hV.isoSpec.inv)

/-- The closed immersion `U ⟶ D₊(T₀) = 𝔸ⁿ_V` of the presentation `p`. -/
abbrev ι : (FTS.ofAffineOpen X U hU).left ⟶ (chartOpen Γ(Y.left, V) p.variableCount).toScheme :=
  (hU.isoSpec.hom : U.toScheme ⟶ Spec Γ(X.left, U)) ≫
    Spec.map (CommRingCat.ofHom p.toRingHom) ≫
      (chartIsoAffineSpace Γ(Y.left, V) p.variableCount).inv

/-- The morphism `ι f hU hUV p : U ⟶ D₊(T₀)` is a closed immersion of schemes. -/
instance : IsClosedImmersion (ι f hU hUV p) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom p.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ p.surjective
  have h₂ : IsClosedImmersion (Spec.map (CommRingCat.ofHom p.toRingHom) ≫
      (chartIsoAffineSpace Γ(Y.left, V) p.variableCount).inv) :=
    IsClosedImmersion.comp _ _
  exact @IsClosedImmersion.comp _ _ _ hU.isoSpec.hom _ inferInstance h₂

omit [CompactSpace S] in
/-- The composite `U ⟶ D₊(T₀) ⟶ Pⁿ_V ⟶ V` is the morphism `U ⟶ V` induced by `f`. -/
theorem ι_comp : ι f hU hUV p ≫ chartι Γ(Y.left, V) p.variableCount ≫ π f hV hUV p =
    (FTS.homOfAffineOpens f hU hV hUV).left := by
  change (chartImmersion U hU p ≫ (chartIsoAffineSpace Γ(Y.left, V) p.variableCount).inv) ≫
      chartι Γ(Y.left, V) p.variableCount ≫ projToSpecCoeff Γ(Y.left, V) p.variableCount ≫
        hV.isoSpec.inv = f.left.resLE V U hUV
  rw [Category.assoc, ← Category.assoc (chartι _ _), ← chartIsoAffineSpace_hom_comp,
    Category.assoc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact chartImmersion_comp_specMap_C_comp_isoSpec_inv f.left hU hV hUV p

/-- **The compactification of the chart `U ⟶ V` by closure in `Pⁿ_V`.** -/
abbrev compactification :
    CompactificationOf (Over.mk (FTS.homOfAffineOpens f hU hV hUV).left) :=
  CompactificationOf.ofClosedInOpen (FTS.homOfAffineOpens f hU hV hUV) (π f hV hUV p)
    (chartι Γ(Y.left, V) p.variableCount) (ι f hU hUV p) (ι_comp f hU hV hUV p)

/-- The chart `D₊(T₀)` of `Pⁿ_V` is affine. -/
instance (R : CommRingCat.{u}) (n : ℕ) : IsAffine (chartOpen R n).toScheme :=
  IsAffine.of_isIso (chartIsoAffineSpace R n).hom

/-- Restriction along an open immersion carries the structure sheaf to the structure sheaf. -/
def restrictDerivedStructureSheafIso {Z W : Scheme.{u}} (e : Z ⟶ W) [IsOpenImmersion e] :
    (OpenImmersion.restrictedDerivedRestrict e).obj (DerivedPushforward.derivedStructureSheaf W) ≅
      DerivedPushforward.derivedStructureSheaf Z :=
  (restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback e).app _ ≪≫
    ObjectProperty.isoMk _ (derivedPullbackStructureSheafIso e)

/-- Restriction along an open immersion carries a shift of the structure sheaf to the same shift
of the structure sheaf. -/
def restrictDerivedStructureSheafShiftIso {Z W : Scheme.{u}} (e : Z ⟶ W) [IsOpenImmersion e]
    (n : ℤ) :
    ((OpenImmersion.restrictedDerivedRestrict e).obj
      ((DerivedPushforward.derivedStructureSheaf W)⟦n⟧)).obj ≅
        ((DerivedPushforward.derivedStructureSheaf Z)⟦n⟧).obj :=
  (OpenImmersion.derivedRestrict e).mapIso
      (((ObjectProperty.ι _).commShiftIso n).app (DerivedPushforward.derivedStructureSheaf W)) ≪≫
    ((OpenImmersion.derivedRestrict e).commShiftIso n).app
      (DerivedPushforward.derivedStructureSheaf W).obj ≪≫
    (shiftFunctor _ n).mapIso ((ObjectProperty.ι _).mapIso (restrictDerivedStructureSheafIso e)) ≪≫
    (((ObjectProperty.ι _).commShiftIso n).app (DerivedPushforward.derivedStructureSheaf Z)).symm

/-- The tilde model on `U` of the algebraic upper shriek along `p` of a complex `ω` over
`Γ(Y, V)`. -/
abbrev tildeModel
    (ω : @DerivedCategory (ModuleCat.{u} Γ(Y.left, V)) _ _ (HasDerivedCategory.standard _)) :
    DerivedCategory U.toScheme.Modules :=
  (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _ _
    (tilde.functor Γ(X.left, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) _ _ _).obj
      (p.upperShriekFunctor.{u, u}.obj ω)

/-- **`a_π(𝒪)` on the chart `D₊(T₀) ≅ 𝔸ⁿ_R`** is `𝒪[n]`, read as the restriction of
`a_π((R[0])~)` to `𝔸ⁿ_R` against the pullback of `(R[0])~` along `𝔸ⁿ_R ⟶ Spec R`, shifted by
`n`. -/
theorem nonempty_chart_twistedInverseImage_derivedTilde_unit_iso (R : CommRingCat.{u}) (n : ℕ) :
    Nonempty ((OpenImmersion.restrictedDerivedRestrict (chartIsoAffineSpace R n).inv).obj
      ((quasiCoherentDerivedPullback' (chartι R n)).obj
        ((twistedInverseImage (projToSpecCoeff R n)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
            ((derivedTilde R).obj ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
                (ModuleCat.of R R)))))) ≅
      ((quasiCoherentDerivedPullback' (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)))).obj
          ((derivedTilde R).obj ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
              (ModuleCat.of R R)))))⟦(n : ℤ)⟧) := by
  let eA := chartIsoAffineSpace R n
  let t : (derivedTilde R).obj ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) ≅
        DerivedPushforward.derivedStructureSheaf (Spec R) :=
    (derivedStructureSheafIsoDerivedTilde R).symm
  let C := Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin n) R))
  exact ⟨(OpenImmersion.restrictedDerivedRestrict eA.inv).mapIso
      ((quasiCoherentDerivedPullback' (chartι R n)).mapIso
        ((twistedInverseImage (projToSpecCoeff R n)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).mapIso t) ≪≫
        chartPullbackTwistedInverseImageIso R n
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)) ≪≫
    ObjectProperty.isoMk _ (restrictDerivedStructureSheafShiftIso eA.inv n) ≪≫
    (shiftFunctor _ (n : ℤ)).mapIso ((ObjectProperty.isoMk _
      (derivedPullbackStructureSheafIso C).symm :
        DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of (MvPolynomial (Fin n) R))) ≅
          (quasiCoherentDerivedPullback' C).obj
            (DerivedPushforward.derivedStructureSheaf (Spec R))) ≪≫
        (quasiCoherentDerivedPullback' C).mapIso t.symm)⟩

/-- **`g^!K` on the chart compactification is the tilde model** of the algebraic upper shriek
of a model `ω` of `K`, wherever the map of [Stacks, Tag 0A9L] for `U ⟶ Ū` over `D₊(T₀) ⟶ Pⁿ_V`
is invertible at `a_π(K)` and `h0A9U` computes `La^*(a_π(ω~))` on the chart `D₊(T₀)`. -/
theorem nonempty_upperShriek_compactification_iso
    (K : quasiCoherentDerivedCategory (FTS.ofAffineOpen Y V hV).left)
    (ω : @DerivedCategory (ModuleCat.{u} Γ(Y.left, V)) _ _ (HasDerivedCategory.standard _))
    (hK : Nonempty (K.obj ≅ (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _)
      _ _ _ _ (tilde.functor Γ(Y.left, V) ⋙ Scheme.Modules.restrictFunctor hV.isoSpec.hom)
        _ _ _).obj ω))
    (h0A9U : Nonempty ((OpenImmersion.restrictedDerivedRestrict
        (chartIsoAffineSpace Γ(Y.left, V) p.variableCount).inv).obj
      ((quasiCoherentDerivedPullback' (chartι Γ(Y.left, V) p.variableCount)).obj
        ((twistedInverseImage (projToSpecCoeff Γ(Y.left, V) p.variableCount)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
            ((derivedTilde Γ(Y.left, V)).obj
              ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj ω)))) ≅
      ((quasiCoherentDerivedPullback' (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : Γ(Y.left, V) →+* p.Poly)))).obj
          ((derivedTilde Γ(Y.left, V)).obj
            ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj
              ω)))⟦(p.variableCount : ℤ)⟧))
    [IsIso ((closedInOpenRestrictionMap (chartι Γ(Y.left, V) p.variableCount)
      (ι f hU hUV p)).app ((twistedInverseImage (π f hV hUV p)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K))] :
    Nonempty (((upperShriek (FTS.homOfAffineOpens f hU hV hUV)
        (compactification f hU hV hUV p)).obj K).obj ≅ tildeModel f hU hUV p ω) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : CompactSpace U.toScheme := inferInstance
  have : QuasiSeparatedSpace U.toScheme := inferInstance
  let R := Γ(Y.left, V)
  let n := p.variableCount
  let a := chartι R n
  let eV := hV.isoSpec
  let eA := chartIsoAffineSpace R n
  let c : U.toScheme ⟶ Spec (CommRingCat.of p.Poly) := chartImmersion U hU p
  let proj := projToSpecCoeff R n
  let aproj := twistedInverseImage proj (isQuasicoherent_homology_derivedPushforward_of_qcqs proj)
  let ac := twistedInverseImage c (isQuasicoherent_homology_derivedPushforward_of_qcqs c)
  let aι := twistedInverseImage (ι f hU hUV p)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (ι f hU hUV p))
  let M := (derivedTilde R).obj ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj ω)
  obtain ⟨eK⟩ := hK
  obtain ⟨e₃⟩ := h0A9U
  let e₁ := upperShriekOfClosedInOpenObjIsoOfIsIso (FTS.homOfAffineOpens f hU hV hUV)
    (π f hV hUV p) a (ι f hU hUV p) (ι_comp f hU hV hUV p) K
  let e₂ : (twistedInverseImage (π f hV hUV p)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K ≅ aproj.obj M :=
    (twistedInverseImageCompIso proj eV.inv
      (isQuasicoherent_homology_derivedPushforward_of_qcqs proj)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs eV.inv)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).app K ≪≫
      aproj.mapIso ((twistedInverseImageIsoRestrictOfIsIso eV.inv).app K ≪≫
        restrictedDerivedRestrictInvIsoDerivedTilde eV K ω eK)
  let e₄ : aι ≅ twistedInverseImage (c ≫ eA.inv)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _) :=
    twistedInverseImageCongr (Category.assoc _ _ _).symm
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (c ≫ eA.inv))
  let Z := (quasiCoherentDerivedPullback' a).obj (aproj.obj M)
  let e₅ := (twistedInverseImageCompIso c eA.inv
    (isQuasicoherent_homology_derivedPushforward_of_qcqs c)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs eA.inv)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (c ≫ eA.inv))).app Z
  let e₆ := (twistedInverseImageIsoRestrictOfIsIso eA.inv).app Z ≪≫ e₃ ≪≫
    (shiftFunctor _ (n : ℤ)).mapIso (quasiCoherentDerivedPullbackSpecMapDerivedTildeIso p ω)
  obtain ⟨e₇⟩ := nonempty_twistedInverseImage_chartImmersion_iso U hU p
    (p.derivedExtension.{u, u}.obj ω)
  exact ⟨(ObjectProperty.ι _).mapIso (e₁ ≪≫
    aι.mapIso ((quasiCoherentDerivedPullback' a).mapIso e₂) ≪≫ e₄.app _ ≪≫ e₅ ≪≫
      ac.mapIso e₆) ≪≫ e₇⟩

/-- **The chart description of `f^!E` at one chart, for any compactification `j`**, wherever
the maps of [Stacks, Tag 0A9L] used along the way are invertible and `h0A9U` computes
`La^*(a_π(ω~))` on the chart `D₊(T₀)` of `Pⁿ_V`: restriction of `j` to the chart, independence
of the compactification, and the chart computation. -/
theorem nonempty_restrict_upperShriek_iso_tildeModel [AlgebraicGeometry.IsNoetherian S]
    (j : CompactificationOf (Over.mk f.left)) (E : quasiCoherentDerivedCategory Y.left)
    (ω : @DerivedCategory (ModuleCat.{u} Γ(Y.left, V)) _ _ (HasDerivedCategory.standard _))
    (hE : IsTildeModelOnAnyModel E.obj V hV ω)
    (h0A9U : Nonempty ((OpenImmersion.restrictedDerivedRestrict
        (chartIsoAffineSpace Γ(Y.left, V) p.variableCount).inv).obj
      ((quasiCoherentDerivedPullback' (chartι Γ(Y.left, V) p.variableCount)).obj
        ((twistedInverseImage (projToSpecCoeff Γ(Y.left, V) p.variableCount)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
            ((derivedTilde Γ(Y.left, V)).obj
              ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj ω)))) ≅
      ((quasiCoherentDerivedPullback' (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : Γ(Y.left, V) →+* p.Poly)))).obj
          ((derivedTilde Γ(Y.left, V)).obj
            ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj
              ω)))⟦(p.variableCount : ℤ)⟧))
    (h₁ : letI : IsAffine V.toScheme := hV
      IsIso ((restrictOpenRestrictionMap (f := f) (i := FTS.ofAffineOpenι Y V hV) (c := j)).app E))
    (h₂ : letI : IsAffine V.toScheme := hV
      letI : IsAffine U.toScheme := hU
      IsIso ((DominatingCompactification.restrictionMapFst (FTS.homOfAffineOpens f hU hV hUV)
        (j.restrictOpenPullback f _ _ _ (FTS.ofAffineOpenι_comp f hU hV hUV))
        (compactification f hU hV hUV p)).app ((twistedInverseImage
          (j.restrictOpenPullback f _ _ _ (FTS.ofAffineOpenι_comp f hU hV hUV)).toBase
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
            ((quasiCoherentDerivedPullback' (FTS.ofAffineOpenι Y V hV).left).obj E))))
    (h₃ : letI : IsAffine V.toScheme := hV
      letI : IsAffine U.toScheme := hU
      IsIso ((DominatingCompactification.restrictionMapSnd (FTS.homOfAffineOpens f hU hV hUV)
        (j.restrictOpenPullback f _ _ _ (FTS.ofAffineOpenι_comp f hU hV hUV))
        (compactification f hU hV hUV p)).app ((twistedInverseImage
          (compactification f hU hV hUV p).toBase
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
            ((quasiCoherentDerivedPullback' (FTS.ofAffineOpenι Y V hV).left).obj E))))
    (h₄ : letI : IsAffine V.toScheme := hV
      letI : IsAffine U.toScheme := hU
      IsIso ((closedInOpenRestrictionMap (chartι Γ(Y.left, V) p.variableCount)
        (ι f hU hUV p)).app ((twistedInverseImage (π f hV hUV p)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
            ((quasiCoherentDerivedPullback' (FTS.ofAffineOpenι Y V hV).left).obj E)))) :
    Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
        ((upperShriek f j).obj E).obj ≅ tildeModel f hU hUV p ω) := by
  let : IsAffine V.toScheme := hV
  let : IsAffine U.toScheme := hU
  let g := FTS.homOfAffineOpens f hU hV hUV
  let w := FTS.ofAffineOpenι_comp f hU hV hUV
  let c₁ := j.restrictOpenPullback f g _ _ w
  let c₀ := compactification f hU hV hUV p
  let K := (quasiCoherentDerivedPullback' (FTS.ofAffineOpenι Y V hV).left).obj E
  have := h₁
  have := h₂
  have := h₃
  have := h₄
  have : IsLocallyNoetherian Y.left := inferInstance
  obtain ⟨eE⟩ := nonempty_restrict_iso_of_isTildeModelOn hE
  let i₀ : (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
      ((upperShriek f j).obj E).obj ≅
        ((quasiCoherentDerivedPullback' U.ι).obj ((upperShriek f j).obj E)).obj :=
    (derivedRestrictIsoDerivedPullback U.ι).app _
  let i₁ := upperShriekRestrictOpenObjIsoOfIsIso f g (FTS.ofAffineOpenι X U hU)
    (FTS.ofAffineOpenι Y V hV) w j E
  let i₂ := DominatingCompactification.upperShriekObjIsoOfIsIso g c₁ c₀ K
  obtain ⟨i₄⟩ := nonempty_upperShriek_compactification_iso f hU hV hUV p K ω
    ⟨((derivedRestrictIsoDerivedPullback V.ι).app E.obj).symm ≪≫ eE⟩ h0A9U
  exact ⟨i₀ ≪≫ (ObjectProperty.ι _).mapIso (i₁ ≪≫ i₂) ≪≫ i₄⟩

/-- The chart description of `f^!E` at one chart, for `E` bounded below: the four maps of
[Stacks, Tag 0A9L] are invertible by properness of the compactifications involved. -/
private theorem nonempty_restrict_upperShriek_iso_tildeModel_of_isBoundedBelow
    (hS : AlgebraicGeometry.IsNoetherian S)
    (j : CompactificationOf (Over.mk f.left)) (E : quasiCoherentDerivedCategory Y.left)
    (hE : DerivedCategoryB.IsBoundedBelow E.obj)
    (ω : @DerivedCategory (ModuleCat.{u} Γ(Y.left, V)) _ _ (HasDerivedCategory.standard _))
    (hω : IsTildeModelOnAnyModel E.obj V hV ω)
    (h0A9U : Nonempty ((OpenImmersion.restrictedDerivedRestrict
        (chartIsoAffineSpace Γ(Y.left, V) p.variableCount).inv).obj
      ((quasiCoherentDerivedPullback' (chartι Γ(Y.left, V) p.variableCount)).obj
        ((twistedInverseImage (projToSpecCoeff Γ(Y.left, V) p.variableCount)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
            ((derivedTilde Γ(Y.left, V)).obj
              ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj ω)))) ≅
      ((quasiCoherentDerivedPullback' (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : Γ(Y.left, V) →+* p.Poly)))).obj
          ((derivedTilde Γ(Y.left, V)).obj
            ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj
              ω)))⟦(p.variableCount : ℤ)⟧)) :
    Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
        ((upperShriek f j).obj E).obj ≅ tildeModel f hU hUV p ω) := by
  have := hS
  have : IsAffine V.toScheme := hV
  have : IsAffine U.toScheme := hU
  have : AlgebraicGeometry.IsNoetherian Y.left := ⟨⟩
  have : AlgebraicGeometry.IsNoetherian V.toScheme := isNoetherian_of_isOpenImmersion V.ι
  have : AlgebraicGeometry.IsNoetherian (FTS.ofAffineOpen Y V hV).left :=
    inferInstanceAs (AlgebraicGeometry.IsNoetherian V.toScheme)
  have : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hEV : DerivedCategoryB.IsBoundedBelow
      ((quasiCoherentDerivedPullback' (FTS.ofAffineOpenι Y V hV).left).obj E).obj :=
    let ⟨n₀, hn₀⟩ := hE
    ⟨n₀, fun m hm => ((Scheme.Modules.restrictFunctor V.ι).map_isZero (hn₀ m hm)).of_iso
      ((DerivedCategory.homologyFunctor V.toScheme.Modules m).mapIso
          ((derivedRestrictIsoDerivedPullback V.ι).app E.obj).symm ≪≫
        (DerivedCategoryB.mapDerivedCategoryHomologyIso
          (Scheme.Modules.restrictFunctor V.ι) m).app E.obj)⟩
  let g := FTS.homOfAffineOpens f hU hV hUV
  let c₁ := j.restrictOpenPullback f g _ _ (FTS.ofAffineOpenι_comp f hU hV hUV)
  let c₀ := compactification f hU hV hUV p
  have : AlgebraicGeometry.IsNoetherian c₁.space := isNoetherian_of_isProper c₁.toBase
  have : AlgebraicGeometry.IsNoetherian c₀.space := isNoetherian_of_isProper c₀.toBase
  have := isNoetherian_of_isProper (π f hV hUV p)
  exact nonempty_restrict_upperShriek_iso_tildeModel f hU hV hUV p j E ω hω h0A9U
    (isIso_twistedInverseImageRestrictionMap_app_of_isProper _ _ _ _
      (IsPullback.of_hasPullback _ _) _ hE)
    (isIso_twistedInverseImageRestrictionMap_app_of_isProper _ _ _ _
      (DominatingCompactification.isPullback_fst g c₁ c₀) _
      (isBoundedBelow_twistedInverseImage_obj _ _ hEV))
    (isIso_twistedInverseImageRestrictionMap_app_of_isProper _ _ _ _
      (DominatingCompactification.isPullback_snd g c₁ c₀) _
      (isBoundedBelow_twistedInverseImage_obj _ _ hEV))
    (isIso_twistedInverseImageRestrictionMap_app_of_isProper _ _ _ _
      (CompactificationOf.isPullback_closedInOpen _ _) _
      (isBoundedBelow_twistedInverseImage_obj _ _ hEV))

end Stacks.Duality.ChartCompactification

namespace Stacks.Duality

open ChartCompactification

/-- **[Stacks, Tag 0BV2] for `𝒪_Y`: the affine chart description of `f^!𝒪_Y`.** Let `S` be
Noetherian and `f : X ⟶ Y` a morphism of `FTS S`, with any compactification `j`. For affine opens
`U ⊆ f⁻¹(V)` and any polynomial presentation `P ⟶ Γ(X, U)` of `Γ(Y, V) ⟶ Γ(X, U)` in `n`
variables, the restriction of `f^!𝒪_Y` to `U` is the associated sheaf of
`φ^!(Γ(Y, V)) = RHom_P(Γ(X, U), P)[n]`. -/
theorem upperShriekStructureSheafCharts {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S]
    {X Y : FTS S} (f : X ⟶ Y) (j : CompactificationOf (Over.mk f.left)) :
    UpperShriekStructureSheafCharts f j := by
  intro V hV U hU hUV p
  exact nonempty_restrict_upperShriek_iso_tildeModel_of_isBoundedBelow f hU hV hUV p inferInstance j
    (DerivedPushforward.derivedStructureSheaf Y.left)
    (Stacks.Duality.KoszulRegular.isBoundedBelow_singleFunctor_obj _) (structureModel (Y := Y) V)
    (isTildeModelOnAnyModel_unit V hV)
    (nonempty_chart_twistedInverseImage_derivedTilde_unit_iso Γ(Y.left, V) p.variableCount)

end Stacks.Duality

namespace Stacks.Duality

open ChartCompactification _root_.Stacks.Duality.ProjectiveSpace
  _root_.AlgebraicGeometry.ProjectiveSpace Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Stacks Project, Tag 0BV2 (Remark 48.17.5), second assertion.** In Situation 48.16.1 let
`f : X ⟶ Y` be a morphism of `FTS S`, `j` any compactification computing `f^!`, and
`E ∈ D⁺_QCoh(𝒪_Y)`. For affine opens `U = Spec A ⊆ f⁻¹(V)`, `V = Spec R`, every presentation
`A = P/I` with `P = R[x_1, …, x_n]` and every `K ∈ D(R)` with `E|_V ≅ K~`, the restriction
`(f^!E)|_U` is the sheaf associated to `φ^!(K) = RHom_P(A, K ⊗ᴸ_R P)[n]`. -/
@[stacks 0BV2 "part (b): (f^!E)|_U corresponds to phi^!(K) = RHom(A, K (x)^L_R P)[n] for every \
  pair of affine opens U, V with f(U) in V, every presentation A = P/I and every K in D(R) with \
  E|_V = K~, E in D^+_QCoh, every compactification"]
theorem upperShriekCharts
    {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S]
    {X Y : FTS S} (f : X ⟶ Y) (j : CompactificationOf (Over.mk f.left))
    (E : quasiCoherentDerivedCategory Y.left) (hE : DerivedCategoryB.IsBoundedBelow E.obj) :
    UpperShriekCharts f j E := by
  intro V hV U hU hUV p ω hω
  have : AlgebraicGeometry.IsNoetherian Y.left := ⟨⟩
  have : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  exact nonempty_restrict_upperShriek_iso_tildeModel_of_isBoundedBelow f hU hV hUV p inferInstance
    j E hE ω hω
    (nonempty_chart_twistedInverseImage_iso Γ(Y.left, V) p.variableCount _)

end Stacks.Duality
