module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToSheafColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.AcyclicObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.HomologyComparisonCriteria

/-!
# Cohomology sheaves of a K-injective complex, read on sections over an acyclic object

Let `(C, O)` be a ringed site, `I` a K-injective complex of `O`-modules and `B` a class of
objects covering the site, over whose members the cohomology sheaves of `I` have no higher
cohomology.  Stacks 0BKZ says that over every `U ∈ B` the hypercohomology `H^q(U, I)` — which is
the cohomology `H^q(I(U))` of the complex of sections, `I` being K-injective — is
`Γ(U, H^q(I))`.  This file reads that statement on the complex itself: over `U` the cokernel
presentation

`I^{q-1}(U) ⟶ Z^q(I)(U) ⟶ H^q(I)(U) ⟶ 0`

of the sections of the cohomology sheaf is exact.  In other words, sections over `U` of the
cohomology sheaves of `I` are computed sectionwise.

The comparison `H^q(I(-)) ⟶ H^q(I)(-)` of the presheaf of sectionwise cohomology with the
underlying presheaf of the cohomology sheaf is the homology comparison of the left exact functor
`SheafOfModules.toSheaf ⋙ sheafToPresheaf`.  It is the composite of the sheafification unit of
the presheaf `H^q(I(-))` with the sheafification of the comparison, and the latter is an
isomorphism because sheafification is exact
(`Stacks.Cohomology.HypercohomologyEdge.isIso_presheafToSheaf_map_homologyComparison`).  So the
comparison is invertible over `U` exactly when the sheafification unit is, and that is what
Stacks 0BKZ provides, in the form
`Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_iff`.

## Main results

* `Stacks.Cohomology.HypercohomologyEdge.isIso_τ₃_of_exact_of_epi`: a morphism of cokernel
  presentations which is an epimorphism on the first terms and an isomorphism on the middle terms
  is an isomorphism on the cokernels.
* `Stacks.Cohomology.HypercohomologyEdge.isIso_presheafToSheaf_map_homologyComparison`: the
  sheafification of the presheaf of sectionwise cohomology is the cohomology sheaf.
* `Stacks.Cohomology.HypercohomologyEdge.isIso_homologyComparison_app_of_acyclic_cover`: over a
  member of `B` the sectionwise cohomology of a K-injective complex is the module of sections of
  its cohomology sheaf.
* `Stacks.Cohomology.HypercohomologyEdge.exact_and_epi_sections_of_acyclic_cover`: the same, as
  exactness of `I^{q-1}(U) ⟶ Z^q(I)(U) ⟶ H^q(I)(U) ⟶ 0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

namespace Stacks.Cohomology.HypercohomologyEdge

universe u v w g

/-! ### Comparing two cokernel presentations -/

section CokernelPresentation

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜]

/-- A morphism `φ : S₁ ⟶ S₂` between two short complexes which are both cokernel presentations —
exact with epimorphic second map — is an isomorphism on the third terms as soon as it is an
epimorphism on the first terms and an isomorphism on the middle terms. -/
lemma isIso_τ₃_of_exact_of_epi {S₁ S₂ : ShortComplex 𝒜} (φ : S₁ ⟶ S₂)
    (_h₁ : S₁.Exact) (h₂ : S₂.Exact) [Epi S₁.g] [Epi S₂.g] [Epi φ.τ₁] [IsIso φ.τ₂] :
    IsIso φ.τ₃ := by
  have hT := h₂.gIsCokernel
  have hw : S₂.f ≫ inv φ.τ₂ ≫ S₁.g = 0 := by
    apply (cancel_epi φ.τ₁).1
    rw [comp_zero, ← Category.assoc, φ.comm₁₂, Category.assoc, IsIso.hom_inv_id_assoc, S₁.zero]
  let j : S₂.X₃ ⟶ S₁.X₃ := hT.desc (CokernelCofork.ofπ (inv φ.τ₂ ≫ S₁.g) hw)
  have hj : S₂.g ≫ j = inv φ.τ₂ ≫ S₁.g :=
    hT.fac (CokernelCofork.ofπ _ hw) WalkingParallelPair.one
  refine ⟨j, ?_, ?_⟩
  · apply (cancel_epi S₁.g).1
    rw [← Category.assoc, ← φ.comm₂₃, Category.assoc, hj, IsIso.hom_inv_id_assoc,
      Category.comp_id]
  · apply (cancel_epi S₂.g).1
    rw [reassoc_of% hj, ← φ.comm₂₃, IsIso.inv_hom_id_assoc, Category.comp_id]

/-- The second map of a short complex isomorphic to one with epimorphic second map is an
epimorphism. -/
lemma epi_g_of_iso {S₁ S₂ : ShortComplex 𝒜} (e : S₁ ≅ S₂) [Epi S₁.g] : Epi S₂.g := by
  have h : S₂.g = e.inv.τ₂ ≫ S₁.g ≫ e.hom.τ₃ := by
    rw [← Category.assoc, e.inv.comm₂₃, Category.assoc, ← ShortComplex.comp_τ₃, e.inv_hom_id,
      ShortComplex.id_τ₃, Category.comp_id]
  rw [h]
  infer_instance

end CokernelPresentation

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The underlying abelian presheaf of a sheaf of `O`-modules. -/
abbrev underlyingPresheaf : SheafOfModules.{w} O ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{w} :=
  SheafOfModules.toSheaf O ⋙ sheafToPresheaf J AddCommGrpCat.{w}

/-! ### Sheafifying the sectionwise cohomology -/

/-- `SheafOfModules.toSheaf` preserves finite colimits. -/
lemma preservesFiniteColimits_toSheaf :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{w} O) :=
  ⟨fun _ _ _ => SheafOfModules.preservesColimitsOfShape_toSheaf O⟩

/-- A functor preserving zero morphisms and epimorphisms maps the comparison of cokernel
presentations to a morphism which is invertible on the first two terms, and keeps the second map
of the presentation epimorphic. -/
private lemma isIso_τ₁_τ₂_and_epi_g_map_cyclesHomologyShortComplexHom
    {A : Type*} [Category* A] [Abelian A] {B : Type*} [Category* B] [Abelian B]
    {D : Type*} [Category* D] [Abelian D] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (G : B ⥤ D) [G.PreservesZeroMorphisms] [G.PreservesEpimorphisms]
    (K : CochainComplex A ℤ) (q : ℤ) :
    IsIso (G.mapShortComplex.map (cyclesHomologyShortComplexHom F K q)).τ₁ ∧
      IsIso (G.mapShortComplex.map (cyclesHomologyShortComplexHom F K q)).τ₂ ∧
      Epi (G.mapShortComplex.obj (cyclesHomologyShortComplexOfMap F K q)).g :=
  have := isIso_cyclesComparison F K q
  ⟨inferInstanceAs (IsIso (G.map (𝟙 _))), Functor.map_isIso G (cyclesComparison F K q),
    inferInstanceAs (Epi (G.map (cyclesHomologyShortComplexOfMap F K q).g))⟩

/-- **Sheafifying the presheaf of sectionwise cohomology gives the cohomology sheaf**: for a
complex `K` of `O`-modules, the sheafification of the homology comparison
`H^q(K(-)) ⟶ H^q(K)(-)` of abelian presheaves is an isomorphism.  Sheafification is exact and
undoes the passage to the underlying presheaf, so it carries the cokernel presentation of the
sectionwise cohomology to that of the cohomology sheaf. -/
theorem isIso_presheafToSheaf_map_homologyComparison
    (K : CochainComplex (SheafOfModules.{w} O) ℤ) (q : ℤ) :
    IsIso ((presheafToSheaf J AddCommGrpCat.{w}).map
      (homologyComparison (underlyingPresheaf O) K q)) := by
  have := preservesFiniteColimits_toSheaf O
  let a := presheafToSheaf J AddCommGrpCat.{w}
  let ψ := a.mapShortComplex.map (cyclesHomologyShortComplexHom (underlyingPresheaf O) K q)
  obtain ⟨hex₁, hepi₁⟩ := exact_and_epi_cyclesHomologyShortComplexOfMap (underlyingPresheaf O) K q
  let T := ShortComplex.mk (K.toCycles (q - 1) q) (K.homologyπ q)
    (K.toCycles_comp_homologyπ (q - 1) q)
  obtain ⟨hexT, hepiT⟩ := (ShortComplex.exact_and_epi_g_iff_g_is_cokernel T).2
    ⟨K.homologyIsCokernel (q - 1) q (by simp)⟩
  let e : a.mapShortComplex.obj (cyclesHomologyShortComplex (underlyingPresheaf O) K q) ≅
      T.map (SheafOfModules.toSheaf O) :=
    ShortComplex.mapNatIso (T.map (SheafOfModules.toSheaf O))
      (asIso (sheafificationAdjunction J AddCommGrpCat.{w}).counit)
  have : Epi (T.map (SheafOfModules.toSheaf O)).g :=
    (inferInstance : Epi ((SheafOfModules.toSheaf O).map T.g))
  have hepi₂ : Epi (a.mapShortComplex.obj
      (cyclesHomologyShortComplex (underlyingPresheaf O) K q)).g :=
    epi_g_of_iso e.symm
  obtain ⟨h₁, h₂, _⟩ := isIso_τ₁_τ₂_and_epi_g_map_cyclesHomologyShortComplexHom
    (underlyingPresheaf O) a K q
  exact isIso_τ₃_of_exact_of_epi ψ (hex₁.map a)
    ((ShortComplex.exact_iff_of_iso e).2 (hexT.map (SheafOfModules.toSheaf O)))

/-- **The comparison is the sheafification unit followed by an isomorphism.**  Over every object
`U`, the homology comparison `H^q(K(U)) ⟶ H^q(K)(U)` is invertible as soon as the sheafification
unit of the presheaf `H^q(K(-))` is invertible over `U`. -/
theorem isIso_homologyComparison_app_of_isIso_toSheafify_app
    (K : CochainComplex (SheafOfModules.{w} O) ℤ) (q : ℤ) (U : C)
    (h : IsIso ((toSheafify J ((((underlyingPresheaf O).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).homology q)).app (op U))) :
    IsIso ((homologyComparison (underlyingPresheaf O) K q).app (op U)) := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{w}
  let f := homologyComparison (underlyingPresheaf O) K q
  have hf : f = adj.unit.app _ ≫ (sheafToPresheaf J AddCommGrpCat.{w}).map
      ((adj.homEquiv _ _).symm f) :=
    ((adj.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)).symm
  have hsharp : IsIso ((adj.homEquiv _ _).symm f) := by
    rw [Adjunction.homEquiv_counit]
    have := isIso_presheafToSheaf_map_homologyComparison O K q
    infer_instance
  show IsIso (f.app (op U))
  rw [hf, NatTrans.comp_app]
  exact IsIso.comp_isIso' h inferInstance

/-! ### Reading Stacks 0BKZ on a K-injective complex -/

section Acyclic

variable [IsGrothendieckAbelian.{g} (SheafOfModules.{w} O)]
  [EnoughInjectives (SheafOfModules.{w} O)]

attribute [local instance] HasDerivedCategory.standard in
/-- **Stacks 0BKZ, read on the presheaf of sectionwise cohomology.**  Let `I` be a K-injective
complex of `O`-modules whose cohomology sheaves have no higher cohomology over the members of a
class `B` of objects covering the site.  Over every `U ∈ B`, the sheafification unit of the
presheaf `H^q(I(-))` of sectionwise cohomology is invertible.

The hypercohomology edge morphism of `Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge`
is, at `I`, the sheafification unit of the degree-`q` cohomology presheaf of derived sections,
and derived sections of the K-injective `I` are its sections. -/
theorem isIso_toSheafify_app_of_acyclic_cover
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) (hI : I.IsKInjective)
    (B : ObjectProperty C) (hB : J.HasEnoughObjects B)
    (hvan : ∀ V : C, B V → ∀ p : ℕ, 0 < p → ∀ m : ℤ,
      IsZero (((SheafOfModules.evaluation O (.op V)).rightDerived p).obj (I.homology m)))
    {U : C} (hU : B U) (q : ℤ) :
    IsIso ((toSheafify J ((((underlyingPresheaf O).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).homology q)).app (op U)) := by
  have hA := HomologyComparison.exists_quasiIso_isKInjective_sheafOfModules O
  let K : DerivedCategory (SheafOfModules.{w} O) := DerivedCategory.Q.obj I
  have hedge := isIso_hypercohomologyEdge_app_of_acyclic_cover O U K B hB
    (fun V hV p hp m => (hvan V hV p hp m).of_iso
      (((SheafOfModules.evaluation O (.op V)).rightDerived p).mapIso
        ((DerivedCategory.homologyFunctorFactors _ m).app I))) hU q
  rw [isIso_hypercohomologyEdge_app_iff, cohomologyPresheafUnit_app] at hedge
  let P' := (DerivedCategory.homologyFunctor (PresheafOfModules.{w} O.obj) q).obj
    ((derivedSectionsPresheaf O).obj K)
  have h₁ : IsIso ((toSheafify J P'.presheaf).app (op U)) := by
    show IsIso (((PresheafOfModules.toPresheaf O.obj).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).unit.app P')).app (op U))
    exact @Functor.map_isIso _ _ _ _ _ _
      (forget₂ (ModuleCat.{w} (O.obj.obj (op U))) AddCommGrpCat.{w}) _ hedge
  let F' := ((SheafOfModules.forget O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have hunit : IsIso (((homotopySectionsPresheaf O).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ _)).app ((HomotopyCategory.quotient _ _).obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (homotopySectionsPresheaf O) hA).2 (D := DerivedCategory (SheafOfModules.{w} O))
      DerivedCategory.Qh _ _ I hI
  let e₁ : P' ≅ F'.homology q :=
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((derivedSectionsPresheaf O).mapIso ((DerivedCategory.quotientCompQhIso _).app I).symm ≪≫
        (asIso (((homotopySectionsPresheaf O).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso _ _)).app ((HomotopyCategory.quotient _ _).obj I))).symm ≪≫
        DerivedCategory.Qh.mapIso
          ((Functor.mapHomotopyCategoryFactors (SheafOfModules.forget O) _).app I)) ≪≫
      (DerivedCategory.homologyFunctorFactorsh _ q).app _ ≪≫
      (HomotopyCategory.homologyFunctorFactors _ _ q).app F'
  let e₂ : (PresheafOfModules.toPresheaf O.obj).obj (F'.homology q) ≅
      (((underlyingPresheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homology q :=
    ((F'.sc q).mapHomologyIso (PresheafOfModules.toPresheaf O.obj)).symm
  let e : (((underlyingPresheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homology q ≅
      P'.presheaf :=
    e₂.symm ≪≫ (PresheafOfModules.toPresheaf O.obj).mapIso e₁.symm
  have hnat := congr_app (toSheafify_naturality J e.hom) (op U)
  simp only [NatTrans.comp_app] at hnat
  have h₂ : IsIso (e.hom.app (op U) ≫ (toSheafify J P'.presheaf).app (op U)) := inferInstance
  rw [hnat] at h₂
  have : IsIso (sheafifyMap J e.hom) :=
    ⟨sheafifyMap J e.inv, by rw [← sheafifyMap_comp, e.hom_inv_id, sheafifyMap_id],
      by rw [← sheafifyMap_comp, e.inv_hom_id, sheafifyMap_id]⟩
  exact IsIso.of_isIso_comp_right _ ((sheafifyMap J e.hom).app (op U))

/-- **Over a member of the covering class, the sectionwise cohomology of a K-injective complex is
the module of sections of its cohomology sheaf**: the comparison `H^q(I(U)) ⟶ H^q(I)(U)` is an
isomorphism. -/
theorem isIso_homologyComparison_app_of_acyclic_cover
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) (hI : I.IsKInjective)
    (B : ObjectProperty C) (hB : J.HasEnoughObjects B)
    (hvan : ∀ V : C, B V → ∀ p : ℕ, 0 < p → ∀ m : ℤ,
      IsZero (((SheafOfModules.evaluation O (.op V)).rightDerived p).obj (I.homology m)))
    {U : C} (hU : B U) (q : ℤ) :
    IsIso ((homologyComparison (underlyingPresheaf O) I q).app (op U)) :=
  isIso_homologyComparison_app_of_isIso_toSheafify_app O I q U
    (isIso_toSheafify_app_of_acyclic_cover O I hI B hB hvan hU q)

/-- **Stacks 0BKZ, read on the complex of sections.**  Over a member `U` of the covering class,
the sequence `I^{q-1}(U) ⟶ Z^q(I)(U) ⟶ H^q(I)(U) ⟶ 0` of abelian groups is exact, for a
K-injective complex `I` whose cohomology sheaves have no higher cohomology over the members of
the class. -/
theorem exact_and_epi_sections_of_acyclic_cover
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) (hI : I.IsKInjective)
    (B : ObjectProperty C) (hB : J.HasEnoughObjects B)
    (hvan : ∀ V : C, B V → ∀ p : ℕ, 0 < p → ∀ m : ℤ,
      IsZero (((SheafOfModules.evaluation O (.op V)).rightDerived p).obj (I.homology m)))
    {U : C} (hU : B U) (q : ℤ) :
    ((cyclesHomologyShortComplex (underlyingPresheaf O) I q).map
        ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U))).Exact ∧
      Epi ((cyclesHomologyShortComplex (underlyingPresheaf O) I q).map
        ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U))).g := by
  let E := (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U)
  let ψ := E.mapShortComplex.map (cyclesHomologyShortComplexHom (underlyingPresheaf O) I q)
  obtain ⟨h₁, h₂, _⟩ := isIso_τ₁_τ₂_and_epi_g_map_cyclesHomologyShortComplexHom
    (underlyingPresheaf O) E I q
  have hψ : IsIso ψ := by
    rw [ShortComplex.isIso_iff]
    exact ⟨h₁, h₂, isIso_homologyComparison_app_of_acyclic_cover O I hI B hB hvan hU q⟩
  obtain ⟨hex, hepi⟩ := exact_and_epi_cyclesHomologyShortComplexOfMap (underlyingPresheaf O) I q
  exact ⟨(ShortComplex.exact_iff_of_iso (asIso ψ)).1 (hex.map E), epi_g_of_iso (asIso ψ)⟩

end Acyclic

end Stacks.Cohomology.HypercohomologyEdge

end
