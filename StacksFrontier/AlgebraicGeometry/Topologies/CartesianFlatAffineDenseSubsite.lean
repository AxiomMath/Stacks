module

public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianFlatAffineSiteWeakSerre
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfCartesianQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts

/-!
# Quasi-coherent modules on a site with a dense subsite of affine schemes

Let `(D, K)` be an essentially small site with a functor `M : D ⥤ Scheme` whose sheaf of rings
of global functions `X ↦ Γ(M X, 𝒪)` is a sheaf, and let `A` be a full subcategory of objects
over affine schemes which is cover dense. If `A`, with the topology it inherits, is a site of
affine schemes with fibre products along its coverings and flat factorizations in the sense of
`StacksFrontier.AlgebraicGeometry.Topologies.CartesianFlatAffineSite` and
`StacksFrontier.AlgebraicGeometry.Topologies.CartesianFlatAffineSiteKernel`, then the quasi-coherent
modules on `D` form a weak Serre subcategory of all modules.

Restriction to `A` is an equivalence of categories of modules (the Comparison Lemma), under
which the quasi-coherent modules are exactly the modules cartesian over every morphism of `A`;
those form a weak Serre subcategory by `Stacks.FlatAffineSite.isWeakSerreClass_cartesianModules`.
This is the shape of the lisse-étale and of the flat-fppf site of an algebraic stack, and so it is
the core of **Stacks 07B4**.

## Main results

* `CategoryTheory.ObjectProperty.isWeakSerreClass_of_equivalence`: weak Serre subcategories
  transfer along an equivalence.
* `Stacks.FlatAffineSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite_dense`: a
  quasi-coherent module is cartesian over every morphism of `A`.
* `Stacks.FlatAffineSite.isQuasicoherentOnSite_iff_cartesianModules`: quasi-coherence is being
  cartesian on `A`.
* `Stacks.FlatAffineSite.isWeakSerreClass_isQuasicoherentOnSite_of_affineSubsite`: the weak Serre
  property.

## References

* [Stacks Project, Tag 07B4](https://stacks.math.columbia.edu/tag/07B4)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u u₁ v₁

namespace CategoryTheory.ObjectProperty

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

/-- **Weak Serre subcategories transfer along an equivalence**: if `P'` is the preimage of a weak
Serre subcategory `P` under the functor of an equivalence, it is a weak Serre subcategory. -/
theorem isWeakSerreClass_of_equivalence (e : C ≌ D) (P : ObjectProperty D) (hP : P.IsWeakSerreClass)
    (P' : ObjectProperty C) (h : ∀ X, P' X ↔ P (e.functor.obj X)) : P'.IsWeakSerreClass where
  exists_zero := by
    obtain ⟨Z, hZ, hPZ⟩ := P.exists_prop_of_containsZero
    refine ⟨e.inverse.obj Z, e.inverse.map_isZero hZ, (h _).2 ?_⟩
    exact P.prop_of_iso (e.counitIso.app Z).symm hPZ
  of_iso i hX := (h _).2 (P.prop_of_iso (e.functor.mapIso i) ((h _).1 hX))
  kernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact (h _).2 (P.prop_of_isLimit_kernelFork (KernelFork.mapIsLimit k hk e.functor)
      ((h _).1 hX) ((h _).1 hY))
  cokernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact (h _).2 (P.prop_of_isColimit_cokernelCofork
      (CokernelCofork.mapIsColimit k hk e.functor) ((h _).1 hX) ((h _).1 hY))
  prop_X₂_of_shortExact hT h₁ h₃ :=
    (h _).2 (P.prop_X₂_of_shortExact (hT.map_of_exact e.functor) ((h _).1 h₁) ((h _).1 h₃))

end CategoryTheory.ObjectProperty

namespace Stacks.FlatAffineSite

open Stacks.PresheafOfModules

variable {D : Type u₁} [Category.{v₁} D] (K : GrothendieckTopology D) [EssentiallySmall.{u} D]
  (M : D ⥤ Scheme.{u}) (hO : Presheaf.IsSheaf K (M.op ⋙ Scheme.Γ))
  (A : ObjectProperty D) [A.ι.IsCoverDense K]

/-- The sheaf of rings `X ↦ Γ(M X, 𝒪)`, as a sheaf of rings for the category of modules. -/
noncomputable abbrev ringSheafOfSchemes : Sheaf K RingCat.{u} :=
  Stacks.SheafOfModules.Tensor.ringSheaf (⟨M.op ⋙ Scheme.Γ, hO⟩ : Sheaf K CommRingCat.{u})

omit [EssentiallySmall.{u, v₁, u₁} D] in
include hO in
/-- The restriction of `ringSheafOfSchemes` to `A` is the sheaf of rings of global functions
of `A.ι ⋙ M`. -/
theorem isSheaf_rings_affineSubsite :
    Presheaf.IsSheaf (A.ι.inducedTopology K) (rings (A.ι ⋙ M) ⋙ forget₂ CommRingCat RingCat) :=
  (Stacks.DenseSubsiteModules.ringRestriction (A.ι.inducedTopology K) K A.ι
    (ringSheafOfSchemes K M hO)).property

section Transfer

/-- Sheafification of abelian presheaves exists over every slice of an essentially small site, and
inverts exactly the locally bijective morphisms. -/
private theorem sheafify_over_of_essentiallySmall {C : Type u₁} [Category.{v₁} C]
    [EssentiallySmall.{u} C] (J : GrothendieckTopology C) :
    (∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}) ∧
      ∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  ⟨fun V => (GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u}
    (J.over V)).1, fun _ => GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _⟩

variable [∀ X : A.FullSubcategory, IsAffine ((A.ι ⋙ M).obj X)]
  {Q : MorphismProperty A.FullSubcategory} [Q.HasPullbacks] [Q.IsStableUnderBaseChange]
  [Q.IsStableUnderComposition]

include hO in
/-- **A quasi-coherent module is cartesian over every morphism of the dense affine subsite.** The
restriction of a quasi-coherent module to `A` is quasi-coherent (Stacks 03DM), so is the universe
lift of its sections, and on `A` quasi-coherent modules are cartesian
(`Stacks.FlatAffineSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`); the universe lift
changes no base change comparison. -/
theorem cartesianModules_restriction_of_isQuasicoherentOnSite
    (hQ : ∀ ⦃X Y : A.FullSubcategory⦄ (f : X ⟶ Y), Q f → Flat ((A.ι ⋙ M).map f))
    (hL : PreservesPullbacksAlong (A.ι ⋙ M) Q)
    (hJ : HasCoverRefinements.{w} (A.ι ⋙ M) Q (A.ι.inducedTopology K))
    (hcov : CoversAreCovering.{w} (A.ι ⋙ M) Q (A.ι.inducedTopology K))
    (F : SheafOfModules.{u} (ringSheafOfSchemes K M hO)) (hF : F.IsQuasicoherentOnSite) :
    cartesianModules.{u} (isSheaf_rings_affineSubsite K M hO A)
      ((Stacks.DenseSubsiteModules.moduleRestriction (A.ι.inducedTopology K) K A.ι
        (ringSheafOfSchemes K M hO)).obj F) := by
  have : ∀ (U : A.FullSubcategory) (X : (Over (A.ι.obj U))ᵒᵖ),
      HasLimitsOfShape (StructuredArrow X (Over.post (X := U) A.ι).op) AddCommGrpCat.{u} :=
    fun _ _ => hasLimitsOfShape_of_essentiallySmall.{u} _ _
  have : ∀ X : Dᵒᵖ, HasLimitsOfShape (StructuredArrow X A.ι.op) AddCommGrpCat.{u} :=
    fun _ => hasLimitsOfShape_of_essentiallySmall.{u} _ _
  obtain ⟨_, _⟩ := sheafify_over_of_essentiallySmall.{u} (A.ι.inducedTopology K)
  obtain ⟨_, _⟩ := sheafify_over_of_essentiallySmall.{u} K
  have hG := (Stacks.Sheaves.SpecialCocontinuous.isQuasicoherentOnSite_iff
    (A.ι.inducedTopology K) K A.ι (ringSheafOfSchemes K M hO) F).1 hF
  have hG' : (SheafOfModules.uliftForPresentation.{u₁, v₁, u, u, max u₁ v₁ u}
      ((Stacks.DenseSubsiteModules.moduleRestriction (A.ι.inducedTopology K) K A.ι
        (ringSheafOfSchemes K M hO)).obj F)).IsQuasicoherentOnSite :=
    SheafOfModules.isQuasicoherentOnSite_uliftForPresentation hG
  intro X Y f
  have h3 := isIso_restrictionBaseChange_of_isQuasicoherentOnSite.{w, u, u, u₁, v₁}
    (isSheaf_rings_affineSubsite K M hO A) hQ hL hJ hcov _ hG' f.unop
  have h4 := bijective_restrictionBaseChange_of_uliftForPresentation.{u₁, v₁, u, u, max u₁ v₁ u}
    (rings (A.ι ⋙ M)) (isSheaf_rings_affineSubsite K M hO A) _ f h3
  exact (ConcreteCategory.isIso_iff_bijective _).mpr h4

include hO in
/-- **Quasi-coherence is being cartesian on the dense affine subsite.** A module on `D` is
quasi-coherent if and only if its restriction to `A` is cartesian over every morphism of `A`. The
converse direction is
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_isIso_restrictionBaseChange_of_isCoverDense`. -/
theorem isQuasicoherentOnSite_iff_cartesianModules
    (hQ : ∀ ⦃X Y : A.FullSubcategory⦄ (f : X ⟶ Y), Q f → Flat ((A.ι ⋙ M).map f))
    (hL : PreservesPullbacksAlong (A.ι ⋙ M) Q)
    (hJ : HasCoverRefinements.{w} (A.ι ⋙ M) Q (A.ι.inducedTopology K))
    (hcov : CoversAreCovering.{w} (A.ι ⋙ M) Q (A.ι.inducedTopology K))
    (F : SheafOfModules.{u} (ringSheafOfSchemes K M hO)) :
    F.IsQuasicoherentOnSite ↔ cartesianModules.{u} (isSheaf_rings_affineSubsite K M hO A)
      ((Stacks.DenseSubsiteModules.moduleRestriction (A.ι.inducedTopology K) K A.ι
        (ringSheafOfSchemes K M hO)).obj F) :=
  ⟨cartesianModules_restriction_of_isQuasicoherentOnSite K M hO A hQ hL hJ hcov F,
    fun h =>
      Stacks.SheafOfModules.isQuasicoherentOnSite_of_isIso_restrictionBaseChange_of_isCoverDense
        A.ι K (⟨M.op ⋙ Scheme.Γ, hO⟩ : Sheaf K CommRingCat.{u}) F fun _ _ f => h f.op⟩

/-- **Quasi-coherent modules on a site with a dense subsite of affine schemes, with fibre products
along its coverings and flat factorizations, form a weak Serre subcategory** (Stacks 0754,
conditions (1)–(4)). Restriction to `A` is an equivalence of categories of modules carrying the
quasi-coherent modules exactly to the cartesian ones
(`Stacks.FlatAffineSite.isQuasicoherentOnSite_iff_cartesianModules`), and those form a weak Serre
subcategory (`Stacks.FlatAffineSite.isWeakSerreClass_cartesianModules`). -/
theorem isWeakSerreClass_isQuasicoherentOnSite_of_affineSubsite
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (hQ : ∀ ⦃X Y : A.FullSubcategory⦄ (f : X ⟶ Y), Q f → Flat ((A.ι ⋙ M).map f))
    (hL : PreservesPullbacksAlong (A.ι ⋙ M) Q)
    (hJ : HasCoverRefinements.{w} (A.ι ⋙ M) Q (A.ι.inducedTopology K))
    (hcov : CoversAreCovering.{w} (A.ι ⋙ M) Q (A.ι.inducedTopology K))
    (hfac : HasFlatFactorizations.{w} (A.ι ⋙ M) Q) :
    (SheafOfModules.isQuasicoherentOnSite (ringSheafOfSchemes K M hO) :
      ObjectProperty (SheafOfModules.{u} (ringSheafOfSchemes K M hO))).IsWeakSerreClass := by
  have : ∀ X : Dᵒᵖ, HasLimitsOfShape (StructuredArrow X A.ι.op) AddCommGrpCat.{u} :=
    fun _ => hasLimitsOfShape_of_essentiallySmall.{u} _ _
  have : HasSheafify (A.ι.inducedTopology K) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  have : (A.ι.inducedTopology K).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  have := isWeakSerreClass_cartesianModules.{w, u} (isSheaf_rings_affineSubsite K M hO A)
    hQ hL hJ hcov hfac
  exact ObjectProperty.isWeakSerreClass_of_equivalence
    (Stacks.DenseSubsiteModules.moduleRestrictionEquivalence (A.ι.inducedTopology K) K A.ι
      (ringSheafOfSchemes K M hO))
    (cartesianModules.{u} (isSheaf_rings_affineSubsite K M hO A)) this _
    (isQuasicoherentOnSite_iff_cartesianModules K M hO A hQ hL hJ hcov)

end Transfer

end Stacks.FlatAffineSite

end
