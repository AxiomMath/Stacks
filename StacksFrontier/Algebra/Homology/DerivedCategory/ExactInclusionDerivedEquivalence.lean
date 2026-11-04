module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactInclusionDerivedAdjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveLocalization
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.HomologyComparisonCounit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismComposition

/-!
# The derived inclusion of an exact subcategory, tested by a derived global sections functor

Let `ι : 𝒜 ⥤ ℳ` be a fully faithful exact functor of abelian categories with a right adjoint `Q`,
let `(R, β)` be a total right derived functor of `Q`, and let `Γ : ℳ ⥤ 𝒩` be a left exact
functor with a total right derived functor `(RΓ, βΓ)`.  Suppose that

* `ι ⋙ Γ` is exact and reflects isomorphisms;
* `Γ` carries the counit `ι(Q N) ⟶ N` of `ι ⊣ Q` to an isomorphism;
* `βΓ` is invertible at every complex `ι(K)` of objects of `𝒜`;
* `RΓ` reflects isomorphisms between objects of a class `P` containing the image of `D(ι)`.

Then the unit of the derived adjunction `D(ι) ⊣ R` is invertible, so `D(ι)` is fully faithful,
its counit is invertible at every object of `P`, and `β` is invertible at every complex `ι(K)`.

## Main definitions

* `Stacks.DerivedCoherator.sectionsDerivedComparison`: the comparison `RΓ ⟶ R ⋙ D(ι ⋙ Γ)` of two
  right derived functors of `Γ`.

## Main results

* `Stacks.DerivedCoherator.isIso_homologyComparison_of_comp_exact` — the homology comparison of a
  left exact `Γ` is invertible at `ι(K)` when `ι ⋙ Γ` is exact.
* `Stacks.DerivedCoherator.isIso_derivedUnit_of_isIso_derivedHomologyComparison` — the comparison
  of a right derived functor is invertible at a complex where every edge morphism and every
  homology comparison is.
* `Stacks.DerivedCoherator.isIso_sectionsDerivedComparison` — `RΓ ≅ R ⋙ D(ι ⋙ Γ)`.
* `Stacks.DerivedCoherator.isIso_comparison_of_derivedSections` — `β` is invertible at `ι(K)`.
* `Stacks.DerivedCoherator.isIso_inclusionDerivedAdjunction_unit_of_derivedSections` — the unit
  of `D(ι) ⊣ R` is invertible.
* `Stacks.DerivedCoherator.isIso_inclusionDerivedAdjunction_counit_app_of_derivedSections` — the
  counit of `D(ι) ⊣ R` is invertible on `P`.

## References

* [Stacks Project, Tag 08H0](https://stacks.math.columbia.edu/tag/08H0)
* [Stacks Project, Tag 08D9](https://stacks.math.columbia.edu/tag/08D9)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

namespace Stacks.DerivedCoherator

/-! ### The homology comparison along a composite -/

section HomologyComparison

variable {𝒜 ℳ 𝒩 : Type*} [Category* 𝒜] [Category* ℳ] [Category* 𝒩]
  [Abelian 𝒜] [Abelian ℳ] [Abelian 𝒩]
  (ι : 𝒜 ⥤ ℳ) [ι.Additive] [PreservesFiniteLimits ι] [PreservesFiniteColimits ι]
  (Γ : ℳ ⥤ 𝒩) [Γ.Additive] [PreservesFiniteLimits Γ]

/-- The homology comparison of a left exact functor is invertible on the image of an exact
functor `ι` along which it becomes exact. -/
lemma isIso_homologyComparison_of_comp_exact [PreservesFiniteLimits (ι ⋙ Γ)]
    [PreservesFiniteColimits (ι ⋙ Γ)] (K : CochainComplex 𝒜 ℤ) (q : ℤ) :
    IsIso (homologyComparison Γ ((ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q) := by
  have h₁ := isIso_homologyComparison_of_exact (ι ⋙ Γ) K q
  have h₂ := isIso_homologyComparison_of_exact ι K q
  rw [homologyComparison_comp ι Γ] at h₁
  exact IsIso.of_isIso_comp_right _ (Γ.map (homologyComparison ι K q))

end HomologyComparison

/-! ### The comparison of a right derived functor, read off from its edge morphisms -/

section Edge

variable {ℳ 𝒩 : Type*} [Category* ℳ] [Category* 𝒩] [Abelian ℳ] [Abelian 𝒩]
  [HasDerivedCategory ℳ] [HasDerivedCategory 𝒩]
  (Γ : ℳ ⥤ 𝒩) [Γ.Additive] [PreservesFiniteLimits Γ]
  (RΓ : DerivedCategory ℳ ⥤ DerivedCategory 𝒩)
  (βΓ : Γ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RΓ)
  [RΓ.IsRightDerivedFunctor βΓ (HomotopyCategory.quasiIso ℳ (ComplexShape.up ℤ))]
  (hA : ∀ K : CochainComplex ℳ ℤ, ∃ (I : CochainComplex ℳ ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)

/-- The comparison `Γ(K) ⟶ RΓ(K)` is invertible at a complex `K` at which every edge morphism
`H^q(RΓ K) ⟶ Γ(H^q K)` and every homology comparison `H^q(Γ K) ⟶ Γ(H^q K)` is invertible. -/
lemma isIso_derivedUnit_of_isIso_derivedHomologyComparison (K : CochainComplex ℳ ℤ)
    (hedge : ∀ q, IsIso ((derivedHomologyComparison Γ RΓ βΓ hA q).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient ℳ (ComplexShape.up ℤ)).obj K))))
    (hcomp : ∀ q, IsIso (homologyComparison Γ K q)) :
    IsIso (βΓ.app ((HomotopyCategory.quotient ℳ (ComplexShape.up ℤ)).obj K)) := by
  rw [DerivedCategory.isIso_iff]
  intro q
  have := hcomp q
  have := hedge q
  have hfac := derivedHomologyComparison_fac_app Γ RΓ βΓ hA q
    ((HomotopyCategory.quotient ℳ (ComplexShape.up ℤ)).obj K)
  have hcomp' : IsIso ((DerivedCategory.homologyFunctor 𝒩 q).map
      (βΓ.app ((HomotopyCategory.quotient ℳ (ComplexShape.up ℤ)).obj K)) ≫
      (derivedHomologyComparison Γ RΓ βΓ hA q).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient ℳ (ComplexShape.up ℤ)).obj K))) := by
    rw [hfac]; exact isIso_homotopyHomologyComparisonToDerived_app Γ K q
  exact IsIso.of_isIso_comp_right _ ((derivedHomologyComparison Γ RΓ βΓ hA q).app
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient ℳ (ComplexShape.up ℤ)).obj K)))

end Edge

/-! ### Reflecting isomorphisms through an exact functor -/

section Reflects

variable {𝒜 𝒩 : Type*} [Category* 𝒜] [Category* 𝒩] [Abelian 𝒜] [Abelian 𝒩]
  [HasDerivedCategory 𝒜] [HasDerivedCategory 𝒩]
  (E : 𝒜 ⥤ 𝒩) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  [E.ReflectsIsomorphisms]

/-- An exact functor which reflects isomorphisms induces a functor of derived categories which
reflects isomorphisms. -/
lemma isIso_of_isIso_mapDerivedCategory_map_of_reflectsIsomorphisms {K L : DerivedCategory 𝒜}
    (φ : K ⟶ L)
    (h : IsIso (E.mapDerivedCategory.map φ)) : IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso ((DerivedCategory.homologyFunctor 𝒩 n).map (E.mapDerivedCategory.map φ)) :=
    inferInstance
  rw [Functor.isIso_homologyFunctor_map_mapDerivedCategory_map_iff] at this
  exact isIso_of_reflects_iso ((DerivedCategory.homologyFunctor 𝒜 n).map φ) E

end Reflects

/-! ### The derived inclusion -/

section Inclusion

universe wG

variable {𝒜 ℳ 𝒩 : Type*} [Category* 𝒜] [Category* ℳ] [Category* 𝒩]
  [Abelian 𝒜] [Abelian ℳ] [Abelian 𝒩]
  [HasDerivedCategory 𝒜] [HasDerivedCategory ℳ] [HasDerivedCategory 𝒩]
  [IsGrothendieckAbelian.{wG} ℳ]
  (ι : 𝒜 ⥤ ℳ) [ι.Additive] [PreservesFiniteLimits ι] [PreservesFiniteColimits ι]
  {Q : ℳ ⥤ 𝒜} [Q.Additive] (adj : ι ⊣ Q)
  (R : DerivedCategory ℳ ⥤ DerivedCategory 𝒜)
  (β : Q.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ R)
  [R.IsRightDerivedFunctor β (HomotopyCategory.quasiIso ℳ (ComplexShape.up ℤ))]
  (Γ : ℳ ⥤ 𝒩) [Γ.Additive] [PreservesFiniteLimits Γ]
  [PreservesFiniteLimits (ι ⋙ Γ)] [PreservesFiniteColimits (ι ⋙ Γ)]
  (RΓ : DerivedCategory ℳ ⥤ DerivedCategory 𝒩)
  (βΓ : Γ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RΓ)
  [RΓ.IsRightDerivedFunctor βΓ (HomotopyCategory.quasiIso ℳ (ComplexShape.up ℤ))]
  (hcounit : ∀ N : ℳ, IsIso (Γ.map (adj.counit.app N)))

/-- The comparison `Q ⋙ ι ⋙ Γ ⟶ Γ` given by `Γ` of the counit of `ι ⊣ Q`. -/
abbrev counitSections : Q ⋙ ι ⋙ Γ ⟶ Γ :=
  (Functor.associator Q ι Γ).inv ≫ Functor.whiskerRight adj.counit Γ ≫
    (Functor.leftUnitor Γ).hom

omit [Abelian 𝒜] [Abelian ℳ] [Abelian 𝒩] [HasDerivedCategory 𝒜] [HasDerivedCategory ℳ]
  [HasDerivedCategory 𝒩] [IsGrothendieckAbelian.{wG} ℳ] [ι.Additive] [PreservesFiniteLimits ι]
  [PreservesFiniteColimits ι] [Q.Additive] [Γ.Additive] [PreservesFiniteLimits Γ]
  [PreservesFiniteLimits (ι ⋙ Γ)] [PreservesFiniteColimits (ι ⋙ Γ)] in
include hcounit in
/-- The comparison `counitSections` is an isomorphism when `Γ` inverts the counit of `ι ⊣ Q`. -/
lemma isIso_counitSections : IsIso (counitSections ι adj Γ) := by
  have : ∀ N, IsIso ((counitSections ι adj Γ).app N) := fun N => by
    simpa [counitSections] using hcounit N
  exact NatIso.isIso_of_isIso_app _

/-- The isomorphism `Γ ≅ Q ⋙ ι ⋙ Γ` of the counit, on homotopy categories. -/
def counitSectionsHomotopyIso :
    Γ.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (Q ⋙ ι ⋙ Γ).mapHomotopyCategory (ComplexShape.up ℤ) :=
  have := isIso_counitSections ι adj Γ hcounit
  { hom := NatTrans.mapHomotopyCategory (inv (counitSections ι adj Γ)) (ComplexShape.up ℤ)
    inv := NatTrans.mapHomotopyCategory (counitSections ι adj Γ) (ComplexShape.up ℤ)
    hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp
    inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp }

/-- The isomorphism underlying `sectionsComparison`: the counit isomorphism `Γ ≅ Q ⋙ ι ⋙ Γ`
followed by the factorisation of `D(ι ⋙ Γ)` through the localization. -/
def sectionsComparisonIso :
    Γ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ≅
      (Q.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙
        (ι ⋙ Γ).mapDerivedCategory :=
  Functor.isoWhiskerRight (counitSectionsHomotopyIso ι adj Γ hcounit) DerivedCategory.Qh ≪≫
    Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (Q ⋙ ι ⋙ Γ)) (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Q.mapHomotopyCategory (ComplexShape.up ℤ))
      (ι ⋙ Γ).mapDerivedCategoryFactorsh.symm ≪≫
    (Functor.associator _ _ _).symm

/-- The comparison exhibiting `R ⋙ D(ι ⋙ Γ)` as a derived functor of `Γ`: the counit
isomorphism `Γ ≅ Q ⋙ ι ⋙ Γ`, the factorisation of `D(ι ⋙ Γ)` through the localization, and
`D(ι ⋙ Γ)` of the comparison `β` of `R`. -/
def sectionsComparison :
    Γ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R ⋙ (ι ⋙ Γ).mapDerivedCategory :=
  (sectionsComparisonIso ι adj Γ hcounit).hom ≫
    Functor.whiskerRight β (ι ⋙ Γ).mapDerivedCategory ≫
    (Functor.associator _ _ _).hom

omit [IsGrothendieckAbelian.{wG} ℳ] [PreservesFiniteLimits ι] [PreservesFiniteColimits ι]
  [R.IsRightDerivedFunctor β (HomotopyCategory.quasiIso ℳ (ComplexShape.up ℤ))]
  [PreservesFiniteLimits Γ] in
/-- At an object `X` of the homotopy category, `sectionsComparison` is an isomorphism followed
by `D(ι ⋙ Γ)` of the comparison `β` of `R`. -/
lemma isIso_sectionsComparison_app_iff (X : HomotopyCategory ℳ (ComplexShape.up ℤ)) :
    IsIso ((sectionsComparison ι adj R β Γ hcounit).app X) ↔
      IsIso ((ι ⋙ Γ).mapDerivedCategory.map (β.app X)) := by
  have h : (sectionsComparison ι adj R β Γ hcounit).app X =
      (sectionsComparisonIso ι adj Γ hcounit).hom.app X ≫
        (ι ⋙ Γ).mapDerivedCategory.map (β.app X) := by
    simp [sectionsComparison]
  rw [h]
  exact isIso_comp_left_iff _ _

omit [PreservesFiniteLimits ι] [PreservesFiniteColimits ι] [PreservesFiniteLimits Γ] in
include hcounit in
/-- `R ⋙ D(ι ⋙ Γ)` is a right derived functor of `Γ`, with comparison `sectionsComparison`. -/
lemma isRightDerivedFunctor_sectionsComparison :
    (R ⋙ (ι ⋙ Γ).mapDerivedCategory).IsRightDerivedFunctor
      (sectionsComparison ι adj R β Γ hcounit)
      (HomotopyCategory.quasiIso ℳ (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ fun I _ => by
    have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ R β I
    exact (isIso_sectionsComparison_app_iff ι adj R β Γ hcounit _).2 inferInstance

/-- The comparison `RΓ ⟶ R ⋙ D(ι ⋙ Γ)` of the two right derived functors of `Γ`. -/
def sectionsDerivedComparison : RΓ ⟶ R ⋙ (ι ⋙ Γ).mapDerivedCategory :=
  RΓ.rightDerivedDesc βΓ (HomotopyCategory.quasiIso ℳ (ComplexShape.up ℤ))
    (R ⋙ (ι ⋙ Γ).mapDerivedCategory) (sectionsComparison ι adj R β Γ hcounit)

omit [IsGrothendieckAbelian.{wG} ℳ] [PreservesFiniteLimits ι] [PreservesFiniteColimits ι]
  [R.IsRightDerivedFunctor β (HomotopyCategory.quasiIso ℳ (ComplexShape.up ℤ))]
  [PreservesFiniteLimits Γ] in
/-- The comparison `βΓ` of `RΓ`, followed by `sectionsDerivedComparison`, is
`sectionsComparison`. -/
lemma sectionsDerivedComparison_fac_app (X : HomotopyCategory ℳ (ComplexShape.up ℤ)) :
    βΓ.app X ≫ (sectionsDerivedComparison ι adj R β Γ RΓ βΓ hcounit).app
        (DerivedCategory.Qh.obj X) =
      (sectionsComparison ι adj R β Γ hcounit).app X :=
  RΓ.rightDerived_fac_app βΓ (HomotopyCategory.quasiIso ℳ (ComplexShape.up ℤ))
    (R ⋙ (ι ⋙ Γ).mapDerivedCategory) (sectionsComparison ι adj R β Γ hcounit) X

/-- The two right derived functors of `Γ` agree: `RΓ ≅ R ⋙ D(ι ⋙ Γ)`. -/
instance isIso_sectionsDerivedComparison :
    IsIso (sectionsDerivedComparison ι adj R β Γ RΓ βΓ hcounit) := by
  have := isRightDerivedFunctor_sectionsComparison ι adj R β Γ hcounit
  exact (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc RΓ βΓ
    (HomotopyCategory.quasiIso ℳ (ComplexShape.up ℤ)) (R ⋙ (ι ⋙ Γ).mapDerivedCategory)
    (sectionsComparison ι adj R β Γ hcounit)).1 inferInstance

variable [(ι ⋙ Γ).ReflectsIsomorphisms]

include adj hcounit

omit [PreservesFiniteLimits ι] [PreservesFiniteColimits ι] [PreservesFiniteLimits Γ] in
/-- The comparison `β` of `R` is invertible at every complex of objects of `𝒜` as soon as the
comparison `βΓ` of `RΓ` is. -/
lemma isIso_comparison_of_derivedSections
    (hβΓ : ∀ K : HomotopyCategory 𝒜 (ComplexShape.up ℤ),
      IsIso (βΓ.app ((ι.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)))
    (K : HomotopyCategory 𝒜 (ComplexShape.up ℤ)) :
    IsIso (β.app ((ι.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) := by
  have := hβΓ K
  have h := sectionsDerivedComparison_fac_app ι adj R β Γ RΓ βΓ hcounit
    ((ι.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
  have : IsIso ((sectionsComparison ι adj R β Γ hcounit).app
      ((ι.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) := by
    rw [← h]; infer_instance
  rw [isIso_sectionsComparison_app_iff] at this
  exact isIso_of_isIso_mapDerivedCategory_map_of_reflectsIsomorphisms (ι ⋙ Γ) _ this

variable [ι.Full] [ι.Faithful] [ι.mapDerivedCategory.IsLeftAdjoint]

omit [PreservesFiniteLimits Γ] in
/-- The unit of `D(ι) ⊣ R` is invertible, so `D(ι)` is fully faithful, as soon as the
comparison `βΓ` of `RΓ` is invertible at every complex of objects of `𝒜`. -/
lemma isIso_inclusionDerivedAdjunction_unit_of_derivedSections
    (hβΓ : ∀ K : HomotopyCategory 𝒜 (ComplexShape.up ℤ),
      IsIso (βΓ.app ((ι.mapHomotopyCategory (ComplexShape.up ℤ)).obj K))) :
    IsIso (inclusionDerivedAdjunction ι adj R β).unit :=
  isIso_inclusionDerivedAdjunction_unit ι adj R β
    (isIso_comparison_of_derivedSections ι adj R β Γ RΓ βΓ hcounit hβΓ)

omit [PreservesFiniteLimits Γ] in
/-- The counit of `D(ι) ⊣ R` is invertible on a class `P` of objects of `D(ℳ)` containing the
image of `D(ι)`, on which `RΓ` reflects isomorphisms, as soon as `βΓ` is invertible at every
complex of objects of `𝒜`. -/
lemma isIso_inclusionDerivedAdjunction_counit_app_of_derivedSections
    (hβΓ : ∀ K : HomotopyCategory 𝒜 (ComplexShape.up ℤ),
      IsIso (βΓ.app ((ι.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)))
    (P : ObjectProperty (DerivedCategory ℳ)) (hPL : ∀ B, P (ι.mapDerivedCategory.obj B))
    (hRΓ : ∀ {M N : DerivedCategory ℳ} (f : M ⟶ N), P M → P N → IsIso (RΓ.map f) → IsIso f)
    (M : DerivedCategory ℳ) (hM : P M) :
    IsIso ((inclusionDerivedAdjunction ι adj R β).counit.app M) := by
  have hu := isIso_inclusionDerivedAdjunction_unit_of_derivedSections ι adj R β Γ RΓ βΓ hcounit
    hβΓ
  set a := inclusionDerivedAdjunction ι adj R β
  have hR : IsIso (R.map (a.counit.app M)) := by
    have : IsIso (a.unit.app (R.obj M) ≫ R.map (a.counit.app M)) := by
      rw [a.right_triangle_components M]; exact IsIso.id _
    exact IsIso.of_isIso_comp_left (a.unit.app (R.obj M)) _
  have hnat := (sectionsDerivedComparison ι adj R β Γ RΓ βΓ hcounit).naturality (a.counit.app M)
  simp only [Functor.id_obj] at hnat
  have : IsIso (RΓ.map (a.counit.app M)) := by
    have : IsIso (RΓ.map (a.counit.app M) ≫
        (sectionsDerivedComparison ι adj R β Γ RΓ βΓ hcounit).app M) := by
      rw [hnat]
      have : IsIso ((R ⋙ (ι ⋙ Γ).mapDerivedCategory).map (a.counit.app M)) := by
        simp only [Functor.comp_map]
        infer_instance
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((sectionsDerivedComparison ι adj R β Γ RΓ βΓ hcounit).app M)
  exact hRΓ _ (hPL _) hM this

end Inclusion

end Stacks.DerivedCoherator
