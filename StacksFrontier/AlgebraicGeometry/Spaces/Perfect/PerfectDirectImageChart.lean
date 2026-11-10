module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineChartRingModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineChartPerfectness
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeBaseScalars
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeFlatRepresentativeBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardUniformAmplitude
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.MatrixActionFlatGap
public import StacksFrontier.Algebra.Homology.DerivedCategory.MatrixActionSerre
public import StacksFrontier.Homology.Perfect.MatrixActionPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TensorOfStrictlyPerfectComplexes
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRightScalar
public import StacksFrontier.CategoryTheory.Localization.AbsoluteLeftDerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.Perfect.TorAmplitudeQuasiCoherentTestsTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationSquareStep
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AlternatingQuasicoherentComparison
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.GeneratedInDegreeOne

/-!
# Perfectness of a derived direct image on an affine chart of the base

This file proves the chart-local core of Stacks 08IS.  Let `f : X ⟶ Y` be a morphism of algebraic
spaces whose higher direct images of quasi-coherent modules vanish uniformly from degree `N` on,
along every base change (Stacks 073G), let `E ∈ D(𝒪_X)` be bounded below with quasi-coherent
cohomology and represented, in `D(f⁻¹𝒪_Y)`, by a complex of flat modules concentrated in `[a, b]`,
and suppose that `Rf_*E` has coherent cohomology vanishing in large degrees.  Then the restriction
of `Rf_*E` to every Noetherian affine étale chart `V` of `Y` is perfect.

## Main results

* `Stacks.SheafOfModules.Tensor.isZero_homology_tot_stupidTrunc_of_isFlat`: the vanishing gap
  for sheaves of modules.
* `AlgebraicGeometry.Space.isZero_homology_derivedTot_derivedModulePushforward`: the vanishing of
  `H^i(Rf_*E ⊗_A σ^{≥k}R)` for `i < a`, `b + k + N ≤ i`.
* `AlgebraicGeometry.Space.isPerfect_etaleModulePullback_chartToSpace_derivedModulePushforward`:
  perfectness on a Noetherian affine chart.

## References

* [Stacks Project, Tag 08IS](https://stacks.math.columbia.edu/tag/08IS)
* [Stacks Project, Tag 068V](https://stacks.math.columbia.edu/tag/068V)
* [Stacks Project, Tag 073G](https://stacks.math.columbia.edu/tag/073G)
* [Stacks Project, Tag 08GE](https://stacks.math.columbia.edu/tag/08GE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 5000] SheafOfModules.instAbelian

namespace Stacks.SheafOfModules.Tensor

universe w' v' u'

section Unitor

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w'})
  [HasSheafify J AddCommGrpCat.{w'}] [J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

open MonoidalCategory

/-- The monoidal structure on presheaves of modules over the underlying ring presheaf, which the
sheaf tensor product sheafifies. -/
local instance monoidalPresheavesOfModulesUnitor :
    MonoidalCategory (PresheafOfModules.{w'} (ringSheaf R).obj) :=
  inferInstanceAs (MonoidalCategory
    (PresheafOfModules.{w'} (R.obj ⋙ forget₂ CommRingCat RingCat)))

/-- The left unit constraint `𝒪 ⊗ M ≅ M` of the sheaf tensor product is natural in `M`. -/
theorem sheafTensorUnitIsoLeft_naturality {M M' : _root_.SheafOfModules.{w'} (ringSheaf R)}
    (f : M ⟶ M') :
    ((sheafTensor R).obj (_root_.SheafOfModules.unit (ringSheaf R))).map f ≫
        (sheafTensorUnitIsoLeft R M').hom =
      (sheafTensorUnitIsoLeft R M).hom ≫ f := by
  have hM : (sheafTensorUnitIsoLeft R M).hom =
      (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).map
          (λ_ M.val).hom ≫
        (PresheafOfModules.sheafificationAdjunction (R := ringSheaf R)
          (𝟙 (ringSheaf R).obj)).counit.app M := rfl
  have hM' : (sheafTensorUnitIsoLeft R M').hom =
      (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).map
          (λ_ M'.val).hom ≫
        (PresheafOfModules.sheafificationAdjunction (R := ringSheaf R)
          (𝟙 (ringSheaf R).obj)).counit.app M' := rfl
  have hT : ((sheafTensor R).obj (_root_.SheafOfModules.unit (ringSheaf R))).map f =
      (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).map
        ((_root_.SheafOfModules.unit (ringSheaf R)).val ◁ f.val) := rfl
  rw [hM, hM', hT]
  set SH := (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)) with hSH
  set EP := (PresheafOfModules.sheafificationAdjunction (R := ringSheaf R)
    (𝟙 (ringSheaf R).obj)).counit with hEP
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ EP.app M')
      ((SH.map_comp _ _).symm.trans
        (congrArg (fun z => SH.map z)
          (MonoidalCategory.leftUnitor_naturality f.val)))).trans
      ((congrArg (fun z => z ≫ EP.app M') (SH.map_comp _ _)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z => SH.map (λ_ M.val).hom ≫ z) (EP.naturality f)).trans
            (Category.assoc _ _ _).symm))))

/-- Tensoring with the structure sheaf on the left is naturally isomorphic to the identity, with
the functor `M ↦ 𝒪 ⊗ M` read through the flipped tensor bifunctor. -/
def sheafTensorFlipUnitIso :
    (sheafTensor R).flip.flip.obj (_root_.SheafOfModules.unit (ringSheaf R)) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M => sheafTensorUnitIsoLeft R M)
    (fun f => sheafTensorUnitIsoLeft_naturality R f)

end Unitor

section Gap

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w'})
  [HasSheafify J AddCommGrpCat.{w'}] [J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasDerivedCategory (_root_.SheafOfModules.{w'} (ringSheaf R))]
  [∀ (K L : CochainComplex (_root_.SheafOfModules.{w'} (ringSheaf R)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor R).flip (ComplexShape.up ℤ)]
  {A : Type*} [CommRing A] [Linear A (_root_.SheafOfModules.{w'} (ringSheaf R))]
  [∀ (K : CochainComplex (_root_.SheafOfModules.{w'} (ringSheaf R)) ℤ)
      (Q : CochainComplex (Mat_ (SingleObj A)) ℤ),
      HomologicalComplex.HasMapBifunctor K Q (MatrixAction.matrixAction A) (ComplexShape.up ℤ)]
  (ψ : A →+* Stacks.Cohomology.SiteModules.GlobalSectionRing (ringSheaf R))
  (hψ : ∀ (a : A) (M : _root_.SheafOfModules.{w'} (ringSheaf R)),
    a • 𝟙 M = Stacks.Cohomology.SiteModules.globalSmul _ (ψ a) M)

/-- The rings of sections of a sheaf of commutative rings, read as a sheaf of rings, are
commutative. -/
instance (U : Cᵒᵖ) : IsMulCommutative ((commRingSheafToRingSheaf R).obj.obj U) :=
  ⟨⟨fun a b => mul_comm (G := R.obj.obj U) a b⟩⟩

include hψ in
/-- **The vanishing gap for sheaves of modules.** Let `𝒪` be a sheaf of commutative rings with
an `A`-linear structure on its modules given by global sections, `R` a strictly bounded above
complex of finite free `A`-modules with chosen bases whose realization `𝒪 ⊗_A R` has cohomology
only in degree `0`, and `K` a complex of flat `𝒪`-modules strictly concentrated in `[a, b]`.  Then
`K ⊗_A σ^{≥k}R` has no cohomology in the degrees `j` with `b + k < j < a`. -/
theorem isZero_homology_tot_stupidTrunc_of_isFlat
    (Rm : CochainComplex (Mat_ (SingleObj A)) ℤ)
    (hR : ∀ j : ℤ, j ≠ 0 → (((MatrixAction.realize A
      (_root_.SheafOfModules.unit (ringSheaf R))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Rm).ExactAt j)
    (K : CochainComplex (_root_.SheafOfModules.{w'} (ringSheaf R)) ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (hK : ∀ p : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat (O := R) (K.X p))
    (k j : ℤ) (hbk : b + k < j) (hja : j < a) :
    IsZero (((MatrixAction.tot A
      (Rm.stupidTrunc (ComplexShape.embeddingUpIntGE k))).obj K).homology j) := by
  refine MatrixAction.isZero_homology_tot_stupidTrunc_of_flat A (sheafTensor R).flip
    (_root_.SheafOfModules.unit (ringSheaf R)) (sheafTensorFlipUnitIso R) (fun X a => ?_)
    Rm hR K a b (fun p G hG => ?_) k j hbk hja
  · rw [hψ, hψ]
    exact Stacks.sheafTensorRight_map_globalSmul X _ _
  · have hF := hK p
    have : PreservesFiniteLimits ((sheafTensor R).flip.obj (K.X p)) := hF.1
    have : PreservesFiniteColimits ((sheafTensor R).flip.obj (K.X p)) := hF.2
    exact fun i => (hG i).map ((sheafTensor R).flip.obj (K.X p))

end Gap

end Stacks.SheafOfModules.Tensor

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] SmallEtale.preservesFiniteLimits_associatedModule

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] Abelian.hasFiniteBiproducts

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- The ring model functor of an affine chart reflects zero objects. -/
theorem isZero_of_isZero_chartRingModel
    (M : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (hM : IsZero ((chartRingModel B S hS T).obj M)) : IsZero M := by
  have hqc := Stacks.Cohomology.TorAmplitude.isQuasicoherent_modulePullback_schemeIso
    ((BigFppfOver.toScheme B S hS).obj T).isoSpec.symm ((chartTilde B S hS T).obj M)
    (inferInstanceAs ((tilde.functor _).obj M).IsQuasicoherent)
  have h₁ := isZero_of_isZero_representedAssociatedModule B S hS T
    (isAlgebraicSpace_yoneda B S hS T) _ hqc hM
  have := Stacks.Cohomology.modulePullbackIso_isEquivalence (chartSpecIso B S hS T)
  have h₂ : IsZero ((chartTilde B S hS T).obj M) := by
    refine (IsZero.iff_id_eq_zero _).2 ((RingedSpaceModuleAdjunction.modulePullback
      (chartSpecIso B S hS T).hom).map_injective ?_)
    exact h₁.eq_of_src _ _
  refine (IsZero.iff_id_eq_zero _).2 (tilde.fullyFaithfulFunctor.map_injective ?_)
  exact h₂.eq_of_src _ _

/-- The modules on the small étale site of an algebraic space have all small coproducts indexed
in `Type`, in particular those forming total complexes. -/
theorem hasColimitsOfSize_modules (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) : HasColimitsOfSize.{0, 0} (Modules.{u, u} B S hS F hF) :=
  have := isGrothendieckAbelian_modules B S hS F hF
  hasColimitsOfSizeShrink.{0, 0, u, u} _

/-- The modules on the small étale site of an algebraic space have finite biproducts, at the
universe of the schemes. -/
instance (priority := high) hasFiniteBiproducts_modules_of_isAlgebraicSpace
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    HasFiniteBiproducts (Modules.{u, u} B S hS F hF) :=
  @Abelian.hasFiniteBiproducts _ _
    (SheafOfModules.instAbelian ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)))

/-- The total complexes of the matrix action exist for modules over an algebraic space. -/
instance hasMapBifunctor_matrixAction_modules (A : Type u) [CommRing A]
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    [Linear A (Modules.{u, u} B S hS F hF)] (K : CochainComplex (Modules.{u, u} B S hS F hF) ℤ)
    (Q : CochainComplex (Mat_ (SingleObj A)) ℤ) :
    HomologicalComplex.HasMapBifunctor K Q
      (MatrixAction.matrixAction A (C := Modules.{u, u} B S hS F hF)) (ComplexShape.up ℤ) :=
  fun _ => @HasColimitsOfShape.has_colimit _ _ _ _
    (@HasColimitsOfSize.has_colimits_of_shape _ _ (hasColimitsOfSize_modules B S hS F hF) _ _) _

/-- Restriction of scalars of sheaves of modules reflects zero objects. -/
theorem isZero_of_isZero_restrictScalars {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R') (M : _root_.SheafOfModules.{u} R')
    (h : IsZero ((_root_.SheafOfModules.restrictScalars.{u} α).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  ext X x
  exact congrArg (fun φ : (_root_.SheafOfModules.restrictScalars.{u} α).obj M ⟶
    (_root_.SheafOfModules.restrictScalars.{u} α).obj M => φ.val.app X x) (h.eq_of_src (𝟙 _) 0)

/-- The modules over the inverse image `f⁻¹𝒪_Y` form a Grothendieck abelian category. -/
theorem isGrothendieckAbelian_inverseImageModules {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    IsGrothendieckAbelian.{u}
      (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f)) :=
  have : EssentiallySmall.{u} (inverseImageRingedSite B S hS f).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS X.1)
    infer_instance
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _

/-- The modules over the inverse image `f⁻¹𝒪_Y` have all small coproducts indexed in `Type`. -/
theorem hasColimitsOfSize_inverseImageModules {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    HasColimitsOfSize.{0, 0}
      (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f)) :=
  have := isGrothendieckAbelian_inverseImageModules B S hS f
  hasColimitsOfSizeShrink.{0, 0, u, u} _

/-- The total complexes of the matrix action exist for modules over the inverse image of the
structure sheaf of the target. -/
instance hasMapBifunctor_matrixAction_inverseImage {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (A : Type u) [CommRing A]
    [Linear A (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f))]
    (K : CochainComplex (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f)) ℤ)
    (Q : CochainComplex (Mat_ (SingleObj A)) ℤ) :
    HomologicalComplex.HasMapBifunctor K Q
      (MatrixAction.matrixAction A
        (C := RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f)))
      (ComplexShape.up ℤ) :=
  fun _ => @HasColimitsOfShape.has_colimit _ _ _ _
    (@HasColimitsOfSize.has_colimits_of_shape _ _
      (hasColimitsOfSize_inverseImageModules B S hS f) _ _) _

/-- The total complexes of the tensor product exist for modules over the inverse image of the
structure sheaf of the target. -/
instance hasMapBifunctor_sheafTensor_inverseImage {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageRingedSite B S hS f).O)
      (ComplexShape.up ℤ) :=
  fun _ => @HasColimitsOfShape.has_colimit _ _ _ _
    (@HasColimitsOfSize.has_colimits_of_shape _ _
      (hasColimitsOfSize_inverseImageModules B S hS f) _ _) _

/-- The total complexes of the tensor product exist for modules over the inverse image of the
structure sheaf of the target. -/
instance hasMapBifunctor_sheafTensor_flip_inverseImage {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageRingedSite B S hS f).O).flip
      (ComplexShape.up ℤ) :=
  fun _ => @HasColimitsOfShape.has_colimit _ _ _ _
    (@HasColimitsOfSize.has_colimits_of_shape _ _
      (hasColimitsOfSize_inverseImageModules B S hS f) _ _) _



attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

attribute [local instance] isGrothendieckAbelian_modules

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

/-- Exactness of a complex is transported along a homology-preserving functor `F` and an
isomorphism `G ⋙ F ≅ H`. -/
private theorem exactAt_mapHomologicalComplex_of_compIso {M C D : Type*} [Category M] [Category C]
    [Category D] [Preadditive M] [Preadditive C] [Preadditive D] {G : M ⥤ C} {H : M ⥤ D}
    [G.Additive] [H.Additive] (F : C ⥤ D) [F.Additive] [F.PreservesHomology] (e : G ⋙ F ≅ H)
    (R : CochainComplex M ℤ) (j : ℤ)
    (h : ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj R).ExactAt j) :
    ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj R).ExactAt j :=
  (h.map F).of_iso ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).app R)

section Crux

variable {X' Y' : AlgebraicSpaces B S hS} (f' : X' ⟶ Y') {A : Type u} [CommRing A]
  (θ : A →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y'.1 Y'.2).O))

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces
whose higher direct images of quasi-coherent modules vanish from degree `N` on, and let the
`𝒪_Y`-modules carry the `A`-linear structure of a ring map `θ : A →+* Γ(Y, 𝒪_Y)`.  Let `E` be a
bounded below object of `D(𝒪_X)` with quasi-coherent cohomology which, read in `D(f⁻¹𝒪_Y)`, is
represented by a complex of flat modules concentrated in `[a, b]`.  Let `R` be a strictly bounded
above complex of finite free `A`-modules with chosen bases whose realization `𝒪_Y ⊗_A R` has
cohomology only in degree `0`.  Then `H^i(Rf_*E ⊗_A σ^{≥k}R) = 0` for `i < a` as soon as
`b + k + N ≤ i`. -/
theorem isZero_homology_derivedTot_derivedModulePushforward (N : ℕ)
    (hN : ∀ F : Modules.{u, u} B S hS X'.1 X'.2, F.IsQuasicoherentOnSite → ∀ p : ℕ, N ≤ p →
      have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
      IsZero (((modulePushforward B S hS f').rightDerived p).obj F))
    (E : DerivedCategory (Modules.{u, u} B S hS X'.1 X'.2))
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj E).IsQuasicoherentOnSite)
    (c : ℤ) [E.IsGE c]
    (K : CochainComplex (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f')) ℤ)
    (hK : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat
      (O := (inverseImageRingedSite B S hS f').O) (K.X n))
    (a b : ℤ) (hKab : ∀ n : ℤ, n ∉ Set.Icc a b → IsZero (K.X n))
    (eK : DerivedCategory.Q.obj K ≅ (derivedScalarRestriction B S hS f').obj E)
    (R : CochainComplex (Mat_ (SingleObj A)) ℤ) (cR : ℤ) [R.IsStrictlyLE cR]
    (hR : letI := Stacks.SheafOfModules.linearOver.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y'.1 Y'.2).O) θ
      ∀ j : ℤ, j ≠ 0 → (((MatrixAction.realize A (_root_.SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y'.1 Y'.2).O))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj R).ExactAt j)
    (i k : ℤ) (hi : i < a) (hk : b + k + N ≤ i) :
    letI := Stacks.SheafOfModules.linearOver.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y'.1 Y'.2).O) θ
    IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) i).obj
      ((MatrixAction.derivedTot A (R.stupidTrunc (ComplexShape.embeddingUpIntGE k)) k cR).obj
        ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f')).obj E))) := by
  let LY := Stacks.SheafOfModules.linearOver.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS Y'.1 Y'.2).O) θ
  let LX := Stacks.SheafOfModules.linearOver.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X'.1 X'.2).O) ((sourceScalars B S hS f').comp θ)
  let LR := Stacks.SheafOfModules.linearOver.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (inverseImageRingedSite B S hS f').O) ((relativeScalars B S hS f').comp θ)
  have := modulePushforward_linear B S hS f' θ
  have := scalarRestriction_linear B S hS f' θ
  have := relativeInverseImage_linear B S hS f' θ
  let Q := R.stupidTrunc (ComplexShape.embeddingUpIntGE k)
  let L := (MatrixAction.derivedTot A Q k cR).obj E
  let Fp := Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f')
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ i).mapIso
    (MatrixAction.derivedTotTotalRightDerivedIso A Q (modulePushforward B S hS f') k cR E c))
  have hR' : ∀ j : ℤ, j ≠ 0 → (((MatrixAction.realize A (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (inverseImageRingedSite B S hS f').O))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj R).ExactAt j := by
    intro j hj
    let Gi := relativeInverseImage B S hS f'
    have : Gi.Additive := inferInstanceAs (Stacks.Sheaves.RingedToposModules.inverseImageModules
      (smallEtaleRingedToposHom B S hS f').toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y').O)).Additive
    have : PreservesFiniteLimits Gi := inferInstanceAs (PreservesFiniteLimits
      (Stacks.Sheaves.RingedToposModules.inverseImageModules
      (smallEtaleRingedToposHom B S hS f').toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y').O)))
    have : PreservesFiniteColimits Gi := inferInstanceAs (PreservesFiniteColimits
      (Stacks.Sheaves.RingedToposModules.inverseImageModules
      (smallEtaleRingedToposHom B S hS f').toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y').O)))
    let eU : Gi.obj (_root_.SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y'.1 Y'.2).O)) ≅
        _root_.SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedSite B S hS f').O) :=
      Iso.refl _
    let e : MatrixAction.realize A (_root_.SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y'.1 Y'.2).O)) ⋙ Gi ≅
        MatrixAction.realize A (_root_.SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedSite B S hS f').O)) :=
      MatrixAction.realizeCompIso A Gi _ ≪≫ (MatrixAction.matrixAction A).mapIso eU
    exact exactAt_mapHomologicalComplex_of_compIso Gi e R j (hR j hj)
  have hLGE : L.IsGE (c + k) := MatrixAction.isGE_derivedTot_obj A Q k cR E c
  have hLqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj L).IsQuasicoherentOnSite :=
    MatrixAction.derivedCategoryB_derivedTot A _
      (isWeakSerre_quasicoherentSheaves_smallEtaleRingedSite B S hS X'.1 X'.2) Q k cR E hE
  have hgap : ∀ j : ℤ, b + k < j → j < a →
      IsZero ((DerivedCategory.homologyFunctor _ j).obj L) := by
    intro j hj₁ hj₂
    have : K.IsStrictlyGE a := ⟨fun n hn => hKab n (by
      rw [ComplexShape.notMem_range_embeddingUpIntGE_iff] at hn
      simp only [Set.mem_Icc]; omega)⟩
    have : K.IsStrictlyLE b := ⟨fun n hn => hKab n (by
      rw [ComplexShape.notMem_range_embeddingUpIntLE_iff] at hn
      simp only [Set.mem_Icc]; omega)⟩
    let ρ := scalarRestriction B S hS f'
    have e₁ : ρ.mapDerivedCategory.obj L ≅
        (MatrixAction.derivedTot A Q k cR).obj (ρ.mapDerivedCategory.obj E) :=
      MatrixAction.derivedTotMapDerivedCategoryIso A Q ρ k cR E
    have e₂ : (MatrixAction.derivedTot A Q k cR).obj (ρ.mapDerivedCategory.obj E) ≅
        DerivedCategory.Q.obj ((MatrixAction.tot A Q).obj K) :=
      MatrixAction.derivedTotObjIso A Q k cR (X := K) eK
    have hz : IsZero (((MatrixAction.tot A Q).obj K).homology j) :=
      Stacks.SheafOfModules.Tensor.isZero_homology_tot_stupidTrunc_of_isFlat
        (inverseImageRingedSite B S hS f').O ((relativeScalars B S hS f').comp θ)
        (fun a M => Stacks.SheafOfModules.linearOver_smul_id _ _ M a) R hR' K a b hK k j hj₁ hj₂
    have hz₁ : IsZero ((DerivedCategory.homologyFunctor _ j).obj (ρ.mapDerivedCategory.obj L)) :=
      hz.of_iso ((DerivedCategory.homologyFunctor _ j).mapIso (e₁ ≪≫ e₂) ≪≫
        (DerivedCategory.homologyFunctorFactors _ j).app _)
    have hz₂ : IsZero (ρ.obj ((DerivedCategory.homologyFunctor _ j).obj L)) :=
      hz₁.of_iso ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso ρ j).app
        L).symm
    exact isZero_of_isZero_restrictScalars _ _ hz₂
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished (b + k + 1) L
  have hex :=
    (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) i).map_distinguished_exact
      _ (Fp.map_distinguished _ hT)
  have h₃ : IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) i).obj
      (Fp.obj ((DerivedCategory.TStructure.t.truncGE (b + k + 1)).obj L))) := by
    have : ((DerivedCategory.TStructure.t.truncGE (b + k + 1)).obj L).IsGE a := by
      rw [DerivedCategory.isGE_iff]
      intro q hq
      by_cases hqm : q < b + k + 1
      · exact DerivedCategory.isZero_of_isGE _ (b + k + 1) q hqm
      · have hπ : IsIso ((DerivedCategory.homologyFunctor _ q).map
            ((DerivedCategory.TStructure.t.truncGEπ (b + k + 1)).app L)) :=
          DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁ _ hT q (b + k)
            (DerivedCategory.TStructure.t.isLE_truncLT_obj L (b + k + 1) (b + k) (by omega))
            (by omega)
        exact (hgap q (by omega) hq).of_iso
          (asIso ((DerivedCategory.homologyFunctor _ q).map
            ((DerivedCategory.TStructure.t.truncGEπ (b + k + 1)).app L))).symm
    exact Stacks.DerivedFunctor.isZero_homology_totalRightDerived_obj _ _ a i hi
  have h₁ : IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) i).obj
      (Fp.obj ((DerivedCategory.TStructure.t.truncLT (b + k + 1)).obj L))) := by
    let lo := min (c + k) (b + k)
    have hι : ∀ q : ℤ, q < b + k + 1 → IsIso ((DerivedCategory.homologyFunctor _ q).map
        ((DerivedCategory.TStructure.t.truncLTι (b + k + 1)).app L)) := fun q hq =>
      DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃ _ hT q (b + k + 1) inferInstance hq
    have hGE : ((DerivedCategory.TStructure.t.truncLT (b + k + 1)).obj L).IsGE lo := by
      rw [DerivedCategory.isGE_iff]
      intro q hq
      have := hι q (by omega)
      exact (DerivedCategory.isZero_of_isGE L (c + k) q (by omega)).of_iso
        (asIso ((DerivedCategory.homologyFunctor _ q).map
          ((DerivedCategory.TStructure.t.truncLTι (b + k + 1)).app L)))
    have hLE : ((DerivedCategory.TStructure.t.truncLT (b + k + 1)).obj L).IsLE
        (lo + ((b + k - lo).toNat : ℕ)) :=
      DerivedCategory.TStructure.t.isLE_truncLT_obj L (b + k + 1) _ (by omega)
    refine isZero_homology_derivedModulePushforward_of_isLE B S hS f' N hN lo _ _ hGE hLE
      (fun q => ?_) i (by omega)
    by_cases hq : q < b + k + 1
    · have := hι q hq
      exact SheafOfModules.IsQuasicoherentOnSite.of_iso
        (asIso ((DerivedCategory.homologyFunctor _ q).map
          ((DerivedCategory.TStructure.t.truncLTι (b + k + 1)).app L))).symm (hLqc q)
    · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
        (DerivedCategory.isZero_of_isLE _ (b + k) q (by omega))
  exact hex.isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

end Crux

section Chart

variable {X Y : AlgebraicSpaces B S hS}

/-- **Perfectness of a derived direct image on a Noetherian affine chart of the base.** Let
`f : X ⟶ Y` be a morphism of algebraic spaces with a uniform vanishing bound `N` for its higher
direct images (Stacks 073G), `V` a Noetherian affine étale chart of `Y`, and `E` a bounded below
object of `D(𝒪_X)` with quasi-coherent cohomology which, read in `D(f⁻¹𝒪_Y)`, is represented by
a complex of flat modules concentrated in `[a, b]`.  If `Rf_*E` has coherent cohomology sheaves
vanishing in large degrees, then its restriction to `V` is perfect. -/
theorem isPerfect_etaleModulePullback_chartToSpace_derivedModulePushforward (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1) (hV : IsNoetherianAffineChart B S hS Y.1 V)
    (N : ℕ) (hN : IsUniformHigherDirectImageBound B S hS f N)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj E).IsQuasicoherentOnSite)
    (c : ℤ) [E.IsGE c]
    (K : CochainComplex (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f)) ℤ)
    (hK : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat
      (O := (inverseImageRingedSite B S hS f).O) (K.X n))
    (a b : ℤ) (hKab : ∀ n : ℤ, n ∉ Set.Icc a b → IsZero (K.X n))
    (eK : DerivedCategory.Q.obj K ≅ (derivedScalarRestriction B S hS f).obj E)
    (hcoh : ∀ i : ℤ, IsCoherent B S hS Y.1 Y.2 ((DerivedCategory.homologyFunctor _ i).obj
      ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj E)))
    (d : ℤ) (hd : ∀ i : ℤ, d < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj E))) :
    (smallEtaleRingedSite B S hS (chartSpace B S hS Y V).1 (chartSpace B S hS Y V).2).IsPerfect
      ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS Y V)
        (isEtale_chartToSpace B S hS Y V)).mapDerivedCategory.obj
        ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj E)) := by
  let T := (SmallEtale.toOver B S hS Y.1).obj V
  let X₀ := (BigFppfOver.toScheme B S hS).obj T
  have : IsAffine X₀ := hV.1
  have : _root_.AlgebraicGeometry.IsNoetherian X₀ :=
    isNoetherian_chartScheme_of_isNoetherianAffineChart B S hS Y V hV
  let g := chartToSpace B S hS Y V
  have hg : IsEtale B S hS g.hom := isEtale_chartToSpace B S hS Y V
  have sq := IsPullback.of_hasPullback f g
  have hi : IsEtale B S hS (pullback.fst f g).hom :=
    isEtale_of_isPullback B S hS (pullback.snd f g) (pullback.fst f g) g f sq.flip hg
  let Fg := etaleModulePullback.{u, u} B S hS g hg
  let Fi := etaleModulePullback.{u, u} B S hS (pullback.fst f g) hi
  let Rf := Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)
  let Rf' := Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS (pullback.snd f g))
  have := Functor.isRightDerivedFunctor_mapDerivedCategory_of_exact Fg
  have := Functor.isRightDerivedFunctor_mapDerivedCategory_of_exact Fi
  let eG : Fg.mapDerivedCategory.obj (Rf.obj E) ≅ Rf'.obj (Fi.mapDerivedCategory.obj E) :=
    (derivedModulePushforwardEtaleRestrictIso B S hS sq hg
      (etaleModuleLowerShriekAdjunction B S hS _ hi) Rf Rf' Fi.mapDerivedCategory
      Fg.mapDerivedCategory
      ((Stacks.DerivedFunctor.homotopyMap (modulePushforward B S hS f)).totalRightDerivedUnit
        DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
      ((Stacks.DerivedFunctor.homotopyMap
        (modulePushforward B S hS (pullback.snd f g))).totalRightDerivedUnit
        DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
      Fi.mapDerivedCategoryFactorsh.inv Fg.mapDerivedCategoryFactorsh.inv).app E
  let EV := Fi.mapDerivedCategory.obj E
  have hHi : ∀ q : ℤ, (DerivedCategory.homologyFunctor _ q).obj EV ≅
      Fi.obj ((DerivedCategory.homologyFunctor _ q).obj E) := fun q =>
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso Fi q).app E
  have hEV : ∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj EV).IsQuasicoherentOnSite :=
    fun q => SheafOfModules.IsQuasicoherentOnSite.of_iso (hHi q).symm
      (isQuasicoherentOnSite_etaleModulePullback B S hS _ hi _ (hE q))
  have : EV.IsGE c := by
    rw [DerivedCategory.isGE_iff]
    exact fun q hq => (Fi.map_isZero (DerivedCategory.isZero_of_isGE E c q hq)).of_iso (hHi q)
  obtain ⟨KV, hKV, hKVab, ⟨eKV⟩⟩ :=
    exists_flatRepresentative_etaleModulePullback B S hS sq hg hi E K hK a b hKab eK
  have hHg : ∀ q : ℤ, (DerivedCategory.homologyFunctor _ q).obj (Fg.mapDerivedCategory.obj
      (Rf.obj E)) ≅ Fg.obj ((DerivedCategory.homologyFunctor _ q).obj (Rf.obj E)) := fun q =>
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso Fg q).app _
  have hGqc : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)).O))) (Fg.mapDerivedCategory.obj (Rf.obj E)) :=
    fun n => SheafOfModules.IsQuasicoherentOnSite.of_iso (hHg n).symm
      (isQuasicoherentOnSite_etaleModulePullback_chartToSpace B S hS Y _
        (hcoh n).toIsQuasicoherentOnSite V)
  obtain ⟨ω, M, hωqc, ⟨eω⟩, ⟨eM⟩, ⟨eΦ⟩⟩ := exists_chartRingModel_iso B S hS T _ hGqc
  have hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj
      (Rf.obj E)).IsQuasicoherentOnSite := fun i => (hcoh i).toIsQuasicoherentOnSite
  have hNω := homologyIsoChartSchemeModule B S hS Y V (Rf.obj E) hqc ω hωqc eω
  have hωb : ∀ i : ℤ, d < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj ω) := by
    intro i hi'
    refine isZero_of_isZero_representedAssociatedModule B S hS T
      (isAlgebraicSpace_yoneda B S hS T) _ (hωqc i) ?_
    exact (Fg.map_isZero (hd i hi')).of_iso
      (representedAssociatedModuleHomologyIso B S hS Y V (Rf.obj E) ω eω i)
  have hωpc : RingedSpace.IsPseudoCoherent (X := X₀.toRingedSpace) ω :=
    (isPseudoCoherent_iff_boundedAbove_coherent_homology X₀ ⟨ω, hωqc⟩).2
      ⟨⟨d, hωb⟩, fun i => Stacks.AlgebraicGeometry.IrreducibleDevissage.isCoherent_of_iso' (hNω i)
        (isCoherent_chartSchemeModule B S hS Y _ (hcoh i) V hV)⟩
  have hMpc := isPseudoCoherent_of_chartRingModel B S hS T ω M eM hωpc
  let LY := Stacks.SheafOfModules.linearOver.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).O)
    (chartModelRingHom B S hS T)
  have hΦ := chartRingModel_linear B S hS T
  have : IsNoetherianRing Γ(X₀, ⊤) := hV.2
  have hMperf : StacksDraft.Perfect.IsPerfect M := by
    refine MatrixAction.isPerfect_of_forall_resolution _ M hMpc a
      (fun R cR _ hR i hi' => ⟨i - b - N, fun k hk => ?_⟩)
    let Φ := chartRingModel B S hS T
    have hRY : ∀ j : ℤ, j ≠ 0 → (((MatrixAction.realize Γ(X₀, ⊤) (_root_.SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)).O))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj R).ExactAt j := by
      intro j hj
      let e : MatrixAction.realizeModule Γ(X₀, ⊤) ⋙ Φ ≅
          MatrixAction.realize Γ(X₀, ⊤) (_root_.SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj T)
              (isAlgebraicSpace_yoneda B S hS T)).O)) :=
        MatrixAction.realizeCompIso _ Φ _ ≪≫
          (MatrixAction.matrixAction Γ(X₀, ⊤)).mapIso (chartRingModelUnitIso B S hS T)
      exact exactAt_mapHomologicalComplex_of_compIso Φ e R j
        ((HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (hR j hj))
    have h := isZero_homology_derivedTot_derivedModulePushforward B S hS (pullback.snd f g)
      (chartModelRingHom B S hS T) N (hN _ _ g (pullback.fst f g) (pullback.snd f g) sq) EV hEV c
      KV hKV a b hKVab eKV R cR hRY i k hi' (by omega)
    let Q := R.stupidTrunc (ComplexShape.embeddingUpIntGE k)
    have e : Φ.mapDerivedCategory.obj ((MatrixAction.derivedTot _ Q k cR).obj M) ≅
        (MatrixAction.derivedTot _ Q k cR).obj (Rf'.obj EV) :=
      MatrixAction.derivedTotMapDerivedCategoryIso _ Q Φ k cR M ≪≫
        (MatrixAction.derivedTot _ Q k cR).mapIso (eΦ ≪≫ eG)
    have hz : IsZero (Φ.obj ((DerivedCategory.homologyFunctor _ i).obj
        ((MatrixAction.derivedTot _ Q k cR).obj M))) :=
      (h.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e)).of_iso
        ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso Φ i).app _).symm
    exact isZero_of_isZero_chartRingModel B S hS T _ hz
  obtain ⟨P, hP, ⟨e⟩⟩ := isPerfect_chartRingModel B S hS T M hMperf
  exact ⟨P, hP, ⟨e ≪≫ eΦ⟩⟩

end Chart

end AlgebraicGeometry.Space

end
