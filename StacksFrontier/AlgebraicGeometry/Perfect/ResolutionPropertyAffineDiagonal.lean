module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.ColimitClose.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.NoetherianExtension.Equivalence
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.AffineBaseSections
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.Absolute
public import StacksFrontier.AlgebraicGeometry.Morphisms.AffineFromVanishing
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionProperty
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyLimitStageNoetherian
public import StacksFrontier.AlgebraicGeometry.QcohInduction.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.BaseChange
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# The resolution property implies an affine diagonal

A quasi-compact and quasi-separated scheme with the resolution property has affine diagonal.

By [Stacks, Tag 0BDX] it is enough that the intersection of two affine opens be affine, and for
that it is enough that the inclusion `j : U ⟶ X` of an affine open be an affine morphism.  By
[Stacks, Tag 0F83] the latter follows from `R¹j_*𝓘 = 0` for every quasi-coherent sheaf of ideals
`𝓘` on `U`.  On a Noetherian `X` the object `Rj_*𝓘` is represented by a complex `𝓗` of
quasi-coherent modules ([Stacks, Tag 09T4]); were `H¹(𝓗)` nonzero, the resolution property would
produce a finite locally free `𝓔` and a map `𝓔 ⟶ Z¹(𝓗)` with nonzero composite to `H¹(𝓗)`, hence
a nonzero morphism `𝓔[-1] ⟶ Rj_*𝓘` in `D(𝒪_X)`.  Adjunction turns such a morphism into a class in
`H¹(U, (j^*𝓔)^∨ ⊗ 𝓘)`, which vanishes because `U` is affine; here this last step is the
vanishing of `Hom` out of a projective object in the derived category of an affine scheme.

## Main results

* `AlgebraicGeometry.isAffineHom_ι_of_isAffineOpen_of_isNoetherian`: on a Noetherian
  quasi-separated scheme with the resolution property the inclusion of an affine open is affine.
* `AlgebraicGeometry.isAffineHom_diagonal_of_hasResolutionProperty_of_isNoetherian`: the
  Noetherian case of the conclusion.
* `AlgebraicGeometry.isAffineHom_diagonal_of_isAffineHom_of_isNoetherian_of_hasResolutionProperty`:
  the Noetherian case transported along an affine morphism — a scheme affine over a Noetherian
  scheme with the resolution property has affine diagonal.  **Unconditional**, and it is
  everything in [Stacks, Tag 0F8C] past the reduction to the Noetherian case.
* `AlgebraicGeometry.isAffineHom_diagonal_of_exists_isAffineHom_isNoetherian_hasResolutionProperty`
  — **[Stacks, Tag 0F8C]**, with the reduction to the Noetherian case carried as the hypothesis
  that such an affine morphism exists.
* `AlgebraicGeometry.exists_isAffineHom_isNoetherian_hasResolutionProperty`: that hypothesis
  discharged, **unconditionally**, from the converse of
  `AlgebraicGeometry.hasResolutionProperty_of_isLimit` at Noetherian stages.
* `AlgebraicGeometry.HasResolutionProperty.isAffineHom_diagonal`: the two composed, which is
  **[Stacks, Tag 0F8C] with no hypothesis beyond the source's**.

## Implementation notes

Affineness of the diagonal is `IsAffineHom (pullback.diagonal (terminal.from X))`, the spelling
of `StacksFrontier/AlgebraicGeometry/Cohomology/Coherent/AffineDiagonal.lean`, and the resolution
property is `AlgebraicGeometry.HasResolutionProperty`.

The passage from the Noetherian case to the general one writes `X` as an inverse limit of schemes
of finite type over the integers with affine transition morphisms ([Stacks, Tag 01ZA]) and
transports an affine diagonal along the affine projection.  It needs the resolution property at
one stage of that system, which is the half of [Stacks, Tag 0F8B] that
`AlgebraicGeometry.hasResolutionProperty_of_isLimit` does not prove.  That half is now proved at
Noetherian stages (`AlgebraicGeometry.hasResolutionProperty_stage`), and the stages produced by
[Stacks, Tag 01ZA] are of finite type over the integers, hence Noetherian — so the reduction goes
through and nothing in this file is conditional.  The converse of [Stacks, Tag 0F8B] for systems
of merely quasi-compact quasi-separated stages is not used.

**What that reduction is used for, and nothing else, is an affine morphism from `X` to a
Noetherian scheme with the resolution property.**  That is why
`isAffineHom_diagonal_of_exists_isAffineHom_isNoetherian_hasResolutionProperty` is stated on
its own: it has the same conclusion under a strictly weaker hypothesis, satisfiable by
`⟨X, 𝟙 X, …⟩` whenever `X` is Noetherian, and it is the statement the general case factors
through.

Affineness of the morphism in
`isAffineHom_diagonal_of_isAffineHom_of_isNoetherian_of_hasResolutionProperty` is load-bearing and
not merely convenient: dropping it would make every scheme admitting a morphism to a Noetherian
scheme with the resolution property have affine diagonal, hence be quasi-separated, which the
doubled spectrum of `StacksFrontier/Examples/QuasiCoherentPushforward/NotQuasiSeparated.lean` is not.

## References

* [Stacks Project, Tag 0F8C](https://stacks.math.columbia.edu/tag/0F8C)
* [Stacks Project, Tag 0F83](https://stacks.math.columbia.edu/tag/0F83)
* [Stacks Project, Tag 0BDX](https://stacks.math.columbia.edu/tag/0BDX)
* [Stacks Project, Tag 09T4](https://stacks.math.columbia.edu/tag/09T4)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.Tag01PGColimitClose
open Stacks.AlgebraicGeometry.QuasicoherentDerived

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Quasi-coherence of kernels and cycles -/

/-- The kernel of a morphism of quasi-coherent modules is quasi-coherent, quasi-coherence being
a weak Serre class. -/
private theorem isQuasicoherent_kernel {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_kernel f inferInstance inferInstance

/-- The cycles of a complex of quasi-coherent modules are quasi-coherent, being the kernel of a
differential. -/
private theorem isQuasicoherent_cycles {X : Scheme.{u}}
    (K : CochainComplex X.Modules ℤ)
    (hK : ∀ i : ℤ, (K.X i).IsQuasicoherent) (i : ℤ) :
    (K.cycles i).IsQuasicoherent := by
  let : (K.X i).IsQuasicoherent := hK i
  let : (K.X (i + 1)).IsQuasicoherent := hK (i + 1)
  let : (K.sc i).X₂.IsQuasicoherent := by
    show (K.X i).IsQuasicoherent
    infer_instance
  let : (K.sc i).X₃.IsQuasicoherent := by
    show (K.X ((ComplexShape.up ℤ).next i)).IsQuasicoherent
    rw [CochainComplex.next]
    exact hK (i + 1)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (K.sc i).cyclesIsoKernel.symm (isQuasicoherent_kernel (K.sc i).g)

/-! ### Cycle classes coming from a vanishing group of the derived category -/

/-- A morphism of complexes that vanishes in the derived category induces zero on homology. -/
private theorem homologyMap_eq_zero_of_derived_map_eq_zero
    {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ} (g : K ⟶ L)
    (hg : DerivedCategory.Q.map g = 0) (i : ℤ) :
    HomologicalComplex.homologyMap g i = 0 := by
  apply (cancel_epi ((DerivedCategory.homologyFunctorFactors X.Modules i).hom.app K)).1
  rw [← DerivedCategory.homologyFunctorFactors_hom_naturality, hg]
  simp only [Functor.map_zero, zero_comp]
  exact (comp_zero).symm

/-- If no nonzero morphism `E[-1] ⟶ K` exists in the derived category, then every map from `E`
to the degree-one cycles of `K` has zero composite to `H¹(K)`: the map extends to a morphism of
complexes out of `E` placed in degree one, which is zero in the derived category. -/
private theorem cycle_class_eq_zero_of_derived_hom_subsingleton
    {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) (E : X.Modules)
    (f : E ⟶ K.cycles 1)
    [Subsingleton
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 1).obj E) ⟶
        DerivedCategory.Q.obj K)] :
    f ≫ K.homologyπ 1 = 0 := by
  let S := (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 1).obj E
  let φ : E ⟶ K.X 1 := f ≫ K.iCycles 1
  have hφ : ∀ k : ℤ, (ComplexShape.up ℤ).Rel 1 k → φ ≫ K.d 1 k = 0 := by
    intro k hk
    simp only [φ, Category.assoc, K.iCycles_d, comp_zero]
  let g : S ⟶ K := HomologicalComplex.mkHomFromSingle φ hφ
  have hg : DerivedCategory.Q.map g = 0 := Subsingleton.elim _ _
  have hhom : HomologicalComplex.homologyMap g 1 = 0 :=
    homologyMap_eq_zero_of_derived_map_eq_zero g hg 1
  have hcycles :
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 1 E).inv ≫
        HomologicalComplex.cyclesMap g 1 = f := by
    apply (cancel_mono (K.iCycles 1)).1
    rw [Category.assoc, HomologicalComplex.cyclesMap_i]
    rw [← Category.assoc, HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles]
    simp only [g, HomologicalComplex.mkHomFromSingle_f, Iso.inv_hom_id_assoc, φ]
  calc
    f ≫ K.homologyπ 1 =
        ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 1 E).inv ≫
          HomologicalComplex.cyclesMap g 1) ≫ K.homologyπ 1 := by rw [hcycles]
    _ = (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 1 E).inv ≫
          HomologicalComplex.homologyMap g 1 := by
      rw [Category.assoc, ← HomologicalComplex.homologyπ_naturality,
        ← Category.assoc, HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ]
    _ = 0 := by rw [hhom, comp_zero]

/-! ### The resolution property detects the zero module -/

/-- **The resolution property tests morphisms out of a quasi-coherent module on finite locally
free modules.** On a quasi-compact and quasi-separated scheme with the resolution property, a
morphism out of a quasi-coherent module vanishes as soon as its composite with every morphism
from a finite locally free module does: the source is the filtered colimit of its finite type
quasi-coherent submodules ([Stacks, Tag 01PG]) and each of those is a quotient of a finite
locally free module. -/
private theorem eq_zero_of_comp_finiteLocallyFree_eq_zero (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [HasResolutionProperty X]
    (Z : X.Modules) [Z.IsQuasicoherent] {H : X.Modules} (q : Z ⟶ H)
    (h : ∀ E : X.Modules, SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E →
      ∀ f : E ⟶ Z, f ≫ q = 0) : q = 0 := by
  apply (isColimit_finiteTypeQuasicoherentSubobjectCocone Z).hom_ext
  intro G
  let : (G.obj : X.Modules).IsQuasicoherent := G.property.1
  let : (G.obj : X.Modules).IsFiniteType := G.property.2
  obtain ⟨E, hE, p, hp⟩ :=
    HasResolutionProperty.exists_finiteLocallyFree_quotient (G.obj : X.Modules)
  let : Epi p := hp
  show G.obj.arrow ≫ q = G.obj.arrow ≫ 0
  apply (cancel_epi p).mp
  simpa only [Category.assoc, comp_zero] using h E hE (p ≫ G.obj.arrow)

/-- **The first cohomology of a complex of quasi-coherent modules vanishes when no nonzero
morphism out of a finite locally free module in degree one exists in the derived category.** -/
private theorem isZero_first_homology_of_derived_hom_subsingleton
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] [HasResolutionProperty X]
    (K : CochainComplex X.Modules ℤ) (hK : ∀ i : ℤ, (K.X i).IsQuasicoherent)
    (h : ∀ E : X.Modules,
      SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E →
      Subsingleton
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 1).obj E) ⟶
          DerivedCategory.Q.obj K)) :
    IsZero (K.homology 1) := by
  let : (K.cycles 1).IsQuasicoherent := isQuasicoherent_cycles K hK 1
  refine IsZero.of_epi_eq_zero (K.homologyπ 1)
    (eq_zero_of_comp_finiteLocallyFree_eq_zero X (K.cycles 1) (K.homologyπ 1) ?_)
  intro E hE f
  let := h E hE
  exact cycle_class_eq_zero_of_derived_hom_subsingleton K E f

/-! ### Finite locally free modules on an affine scheme are projective -/

/-- Alias of `Module.finite_and_projective_of_isFiniteLocallyFree`. -/
private alias finite_and_projective_of_module_isFiniteLocallyFree :=
  Module.finite_and_projective_of_isFiniteLocallyFree

/-- The module of global sections of a finite locally free quasi-coherent module on an affine
scheme is finite and projective. -/
private lemma finite_and_projective_moduleSpecΓ_of_isFiniteLocallyFree
    {R : Type u} [CommRing R] (F : (Spec (CommRingCat.of R)).Modules)
    [F.IsQuasicoherent] (hF : Scheme.Modules.IsFiniteLocallyFree F) :
    Module.Finite R (moduleSpecΓFunctor.obj F) ∧
      Module.Projective R (moduleSpecΓFunctor.obj F) := by
  have hfrom : IsIso F.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := CommRingCat.of R) F
  let e : tilde (R := CommRingCat.of R) (ModuleCat.of R (moduleSpecΓFunctor.obj F)) ≅ F :=
    @asIso _ _ _ _ F.fromTildeΓ hfrom
  have htilde : (tilde (R := CommRingCat.of R)
      (ModuleCat.of R (moduleSpecΓFunctor.obj F))).IsFiniteLocallyFree := by
    intro x
    obtain ⟨U, hx, I, hI, ⟨eU⟩⟩ := hF x
    exact ⟨U, hx, I, hI, ⟨(Scheme.Modules.restrictFunctor (Scheme.Opens.ι U)).mapIso e ≪≫ eU⟩⟩
  exact finite_and_projective_of_module_isFiniteLocallyFree
    ((tilde_isFiniteLocallyFree_iff R (moduleSpecΓFunctor.obj F)).mp htilde)

/-- A finite locally free quasi-coherent module on an affine scheme is a projective object of the
category of quasi-coherent modules, which is equivalent to the category of modules over the ring
of global functions. -/
private theorem projective_of_isFiniteLocallyFree_of_isAffine {R : CommRingCat.{u}}
    (E : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory)
    (hE : Scheme.Modules.IsFiniteLocallyFree E.obj) : Projective E := by
  let e := tildeEquiv (R := R)
  let : Module.Projective R (moduleSpecΓFunctor.obj E.obj) :=
    (finite_and_projective_moduleSpecΓ_of_isFiniteLocallyFree E.obj hE).2
  have : Projective (e.inverse.obj E) := by
    show Projective (moduleSpecΓFunctor.obj E.obj)
    infer_instance
  exact Projective.of_iso (e.counitIso.app E) (e.functor.projective_obj (e.inverse.obj E))

/-! ### Vanishing of derived homomorphism groups -/

/-- A group of morphisms between two objects vanishes when it does between isomorphic objects. -/
private theorem subsingleton_hom_of_iso {C : Type*} [Category* C] {X Y X' Y' : C}
    (eX : X ≅ X') (eY : Y ≅ Y') (h : Subsingleton (X ⟶ Y)) : Subsingleton (X' ⟶ Y') :=
  (Equiv.subsingleton_congr (Iso.homCongr eX eY)).mp h

/-- A morphism of complexes that vanishes in the homotopy category vanishes in the derived
category. -/
private theorem derived_map_eq_zero_of_homotopy_map_eq_zero
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {K L : CochainComplex C ℤ} (g : K ⟶ L)
    (h : (HomotopyCategory.quotient C (.up ℤ)).map g = 0) :
    DerivedCategory.Q.map g = 0 := by
  have hn := (DerivedCategory.quotientCompQhIso C).hom.naturality g
  apply (cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app K)).mp
  simpa only [Functor.comp_map, h, Functor.map_zero, zero_comp, comp_zero] using hn.symm

/-- A morphism into a K-injective complex that vanishes in the derived category vanishes already
in the homotopy category. -/
private theorem homotopy_map_eq_zero_of_derived_map_eq_zero
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {K L : CochainComplex C ℤ} [L.IsKInjective] (g : K ⟶ L)
    (h : DerivedCategory.Q.map g = 0) :
    (HomotopyCategory.quotient C (.up ℤ)).map g = 0 := by
  apply (CochainComplex.IsKInjective.Qh_map_bijective _ L).injective
  have hn := (DerivedCategory.quotientCompQhIso C).hom.naturality g
  simp only [Functor.comp_map, h, comp_zero] at hn
  rw [Functor.map_zero]
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app L)).mp
  simpa only [zero_comp] using hn

/-- If every morphism of complexes into a K-injective complex vanishes in the derived category,
then the group of morphisms in the derived category is trivial: every such morphism is the image
of a morphism of complexes. -/
private theorem derived_hom_subsingleton_of_isKInjective
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (K L : CochainComplex C ℤ) [L.IsKInjective]
    (h : ∀ g : K ⟶ L, DerivedCategory.Q.map g = 0) :
    Subsingleton (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) := by
  let q := HomotopyCategory.quotient C (.up ℤ)
  have : Subsingleton (q.obj K ⟶ q.obj L) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := q.map_surjective a
    obtain ⟨b, rfl⟩ := q.map_surjective b
    rw [homotopy_map_eq_zero_of_derived_map_eq_zero a (h a),
      homotopy_map_eq_zero_of_derived_map_eq_zero b (h b)]
  have : Subsingleton (DerivedCategory.Qh.obj (q.obj K) ⟶ DerivedCategory.Qh.obj (q.obj L)) :=
    (CochainComplex.IsKInjective.Qh_map_bijective _ L).surjective.subsingleton
  exact subsingleton_hom_of_iso ((DerivedCategory.quotientCompQhIso C).app K)
    ((DerivedCategory.quotientCompQhIso C).app L) this

/-- **Adjunction on derived homomorphism groups.** For an adjunction `F ⊣ G` with `F` exact, a
vanishing group of morphisms from the termwise image of `K` under `F` into a K-injective complex
`L` gives a vanishing group of morphisms from `K` into the termwise image of `L` under `G`. -/
private theorem derived_hom_subsingleton_of_adjunction
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (G : C ⥤ D) (F : D ⥤ C) [G.Additive] [F.Additive] (adj : F ⊣ G)
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex D ℤ) (L : CochainComplex C ℤ) [L.IsKInjective]
    [Subsingleton (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj L)] :
    Subsingleton (DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj L)) := by
  let := CochainComplex.isKInjective_mapHomologicalComplex_of_exact G F adj L
  apply derived_hom_subsingleton_of_isKInjective
  intro g
  let adjc := adj.mapHomologicalComplex (.up ℤ)
  let f := (adjc.homEquiv K L).symm g
  have hf : (HomotopyCategory.quotient C (.up ℤ)).map f = 0 :=
    homotopy_map_eq_zero_of_derived_map_eq_zero f (Subsingleton.elim _ _)
  have hg : g = adjc.unit.app K ≫ (G.mapHomologicalComplex (.up ℤ)).map f := by
    have h := adjc.homEquiv_unit (X := K) (Y := L) (f := f)
    rwa [show adjc.homEquiv K L f = g from (adjc.homEquiv K L).apply_symm_apply g] at h
  have key : (HomotopyCategory.quotient D (.up ℤ)).map
      ((G.mapHomologicalComplex (.up ℤ)).map f) = 0 := by
    have hn := (G.mapHomotopyCategoryFactors (.up ℤ)).hom.naturality f
    simp only [Functor.comp_map, hf, Functor.map_zero, zero_comp] at hn
    exact (cancel_epi ((G.mapHomotopyCategoryFactors (.up ℤ)).hom.app _)).mp
      (by rw [comp_zero]; exact hn.symm)
  apply derived_map_eq_zero_of_homotopy_map_eq_zero
  rw [hg, Functor.map_comp, key, comp_zero]

/-- There is no nonzero morphism in the derived category between two objects concentrated in
distinct degrees when the source is projective. -/
private theorem derived_single_hom_subsingleton_of_projective
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (E F : C) [Projective E] (i j : ℤ) (hij : i ≠ j) :
    Subsingleton (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C i).obj E) ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor C j).obj F)) := by
  let K := (CochainComplex.singleFunctor C i).obj E
  let L := (CochainComplex.singleFunctor C j).obj F
  let q := HomotopyCategory.quotient C (.up ℤ)
  have : ∀ n, Projective (K.X n) := by
    intro n
    by_cases hn : n = i
    · subst n
      exact Projective.of_iso (HomologicalComplex.singleObjXSelf (.up ℤ) i E).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) i E n hn).projective
  have : K.IsKProjective := CochainComplex.isKProjective_of_projective K i
  have : Subsingleton (K ⟶ L) := by
    refine ⟨fun a b => ?_⟩
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    by_cases hn : n = i
    · subst n
      exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) j F i hij).eq_of_tgt _ _
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) i E n hn).eq_of_src _ _
  have : Subsingleton (q.obj K ⟶ q.obj L) := q.map_surjective.subsingleton
  have : Subsingleton (DerivedCategory.Qh.obj (q.obj K) ⟶ DerivedCategory.Qh.obj (q.obj L)) :=
    (CochainComplex.IsKProjective.Qh_map_bijective K _).surjective.subsingleton
  exact subsingleton_hom_of_iso ((DerivedCategory.quotientCompQhIso C).app K)
    ((DerivedCategory.quotientCompQhIso C).app L) this

/-- **On an affine scheme there is no nonzero morphism from a finite locally free module placed
in degree one to a quasi-coherent module placed in degree zero.** The two objects come from the
derived category of quasi-coherent modules, where the source is projective, and that category is
equivalent to the complexes with quasi-coherent cohomology by [Stacks, Tag 06Z0]. -/
private theorem derived_single_hom_subsingleton_of_isAffine (R : CommRingCat.{u})
    [IsNoetherian (Spec R)] (E F : (Spec R).Modules) [E.IsQuasicoherent] [F.IsQuasicoherent]
    (hE : Scheme.Modules.IsFiniteLocallyFree E) :
    Subsingleton
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Spec R).Modules 1).obj E) ⟶
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Spec R).Modules 0).obj F)) := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  have hAdd : P.ι.Additive := P.ι.additive_of_preserves_binary_products
  let e : P.FullSubcategory := ⟨E, inferInstance⟩
  let f : P.FullSubcategory := ⟨F, inferInstance⟩
  let K := (CochainComplex.singleFunctor P.FullSubcategory 1).obj e
  let L := (CochainComplex.singleFunctor P.FullSubcategory 0).obj f
  have : Projective e := projective_of_isFiniteLocallyFree_of_isAffine e hE
  have : Subsingleton (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :=
    derived_single_hom_subsingleton_of_projective e f 1 0 (by decide)
  let Cmp := derivedQuasicoherentComparison.{u + 1} (Spec R)
  have : Cmp.IsEquivalence :=
    Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_isNoetherian (Spec R)
  let J := Cmp ⋙ (DerivedCategoryB.derivedCategoryB P).ι
  have : J.Full := inferInstance
  let eI : J ≅ P.ι.mapDerivedCategory := derivedQuasicoherentComparisonCompι.{u + 1} (Spec R)
  let eK : J.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Spec R).Modules 1).obj E) :=
    eI.app _ ≪≫ P.ι.mapDerivedCategoryFactors.app K ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex P.ι (.up ℤ) 1).app e)
  let eL : J.obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Spec R).Modules 0).obj F) :=
    eI.app _ ≪≫ P.ι.mapDerivedCategoryFactors.app L ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex P.ι (.up ℤ) 0).app f)
  exact subsingleton_hom_of_iso eK eL J.map_surjective.subsingleton

/-! ### Representing a higher direct image by a complex of quasi-coherent modules -/

/-- **[Stacks, Tag 09T4] read on complexes.** On a Noetherian scheme an object of the derived
category with quasi-coherent cohomology is isomorphic to the image of a complex of quasi-coherent
modules. -/
private theorem exists_quasicoherent_complex_model (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory X.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent) :
    ∃ H : CochainComplex X.Modules ℤ,
      (∀ i : ℤ, (H.X i).IsQuasicoherent) ∧ Nonempty (DerivedCategory.Q.obj H ≅ K) := by
  let P := SheafOfModules.isQuasicoherent X.ringCatSheaf
  have hAdd : P.ι.Additive := P.ι.additive_of_preserves_binary_products
  let C := derivedQuasicoherentComparison.{u + 1} X
  have : C.IsEquivalence :=
    Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_isNoetherian X
  let Kqc : (DerivedCategoryB.derivedCategoryB P).FullSubcategory := ⟨K, hK⟩
  obtain ⟨A, ⟨eA⟩⟩ := Functor.EssSurj.mem_essImage C Kqc
  let F : CochainComplex P.FullSubcategory ℤ := DerivedCategory.Q.objPreimage A
  let H : CochainComplex X.Modules ℤ :=
    (P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  have eHK : DerivedCategory.Q.obj H ≅ K :=
    (P.ι.mapDerivedCategoryFactors.app F).symm ≪≫
      P.ι.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso A) ≪≫
      ((derivedQuasicoherentComparisonCompι.{u + 1} X).app A).symm ≪≫
      (DerivedCategoryB.derivedCategoryB P).ι.mapIso eA
  exact ⟨H, fun i => (F.X i).property, ⟨eHK⟩⟩

/-- An injective resolution, extended to all integer degrees, as a bounded-below complex. -/
private def extendedInjectiveResolutionPlus {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] [EnoughInjectives C] {A : C} (I : InjectiveResolution A) :
    CochainComplex.Plus C :=
  ⟨I.cocomplex.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩

/-- An object placed in degree zero, as a bounded-below complex. -/
private def singleComplexPlus {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (A : C) : CochainComplex.Plus C :=
  ⟨(CochainComplex.singleFunctor C 0).obj A, ⟨0, inferInstance⟩⟩

/-- **The right derived functor of an additive functor computed on an injective resolution.**
Applying the functor termwise to an injective resolution of `A`, extended to all integer degrees,
computes the higher right derived functors of the functor at `A`. -/
private def mappedInjectiveResolutionHomologyIso
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (G : C ⥤ D) [G.Additive] (A : C) (n : ℤ) :
    (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((injectiveResolution A).cocomplex.extend ComplexShape.embeddingUpNat)).homology n) ≅
      (G.rightDerivedPlus n).obj A := by
  let I := injectiveResolution A
  let Lp := extendedInjectiveResolutionPlus I
  let L : CochainComplex _ ℤ := I.cocomplex.extend ComplexShape.embeddingUpNat
  let hp := (HomotopyCategory.Plus.quotient C).obj Lp
  let s : (CochainComplex.singleFunctor C 0).obj A ⟶ L :=
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat A 0 0 (by simp)).inv ≫
      HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat
  have : QuasiIso s := by dsimp [s]; infer_instance
  let Pc := singleComplexPlus A
  let sp : Pc ⟶ Lp := ⟨s⟩
  have hP : (HomotopyCategory.Plus.quotient C).obj Pc =
      (HomotopyCategory.Plus.singleFunctor C 0).obj A := rfl
  let sp' : (HomotopyCategory.Plus.singleFunctor C 0).obj A ⟶ hp :=
    eqToHom hP.symm ≫ (HomotopyCategory.Plus.quotient C).map sp
  have hq : IsIso (DerivedCategory.Plus.Qh.map
      ((HomotopyCategory.Plus.quotient C).map sp)) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 (by change QuasiIso s; infer_instance))
  have : IsIso (DerivedCategory.Plus.Qh.map sp') := by simpa [sp', hP] using hq
  have : ∀ i, Injective (hp.obj.as.X i) := fun i => inferInstanceAs (Injective (L.X i))
  have : IsIso (G.rightDerivedFunctorPlusUnith.app hp) := by infer_instance
  refine ((DerivedCategory.homologyFunctorFactors D n).app
    ((G.mapHomologicalComplex _).obj L)).symm ≪≫ ?_
  refine (DerivedCategory.homologyFunctor D n).mapIso
    (((DerivedCategory.Plus.QhCompιIsoιCompQh D).app
        (G.mapHomotopyCategoryPlus.obj hp) ≪≫
      DerivedCategory.Qh.mapIso (G.mapHomotopyCategoryPlusCompιIso.app hp) ≪≫
      DerivedCategory.Qh.mapIso
        ((G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app L) ≪≫
      (DerivedCategory.quotientCompQhIso D).app ((G.mapHomologicalComplex _).obj L)).symm) ≪≫ ?_
  exact (DerivedCategory.Plus.homologyFunctor D n).mapIso
    ((asIso (G.rightDerivedFunctorPlusUnith.app hp)) ≪≫
      (G.rightDerivedFunctorPlus.mapIso
        ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).app A ≪≫
          asIso (DerivedCategory.Plus.Qh.map sp'))).symm)

/-! ### The inclusion of an affine open of a Noetherian scheme with the resolution property -/

/-- Alias of `Stacks.AffineTilde.preservesFiniteLimits_restrictFunctor`. -/
private alias preservesFiniteLimits_restrictFunctor :=
    Stacks.AffineTilde.preservesFiniteLimits_restrictFunctor

/-- **An open immersion with affine source into a Noetherian scheme with the resolution property
is an affine morphism.** By [Stacks, Tag 0F83] it suffices that `R¹f_*` vanish on quasi-coherent
sheaves of ideals; the derived direct image of such an ideal is represented by a complex of
quasi-coherent modules, and no nonzero morphism into it from a finite locally free module placed
in degree one exists, because adjunction moves such a morphism to the affine source. -/
private theorem isAffineHom_of_isOpenImmersion_from_spec (X : Scheme.{u}) [IsNoetherian X]
    [QuasiSeparatedSpace X] [HasResolutionProperty X] (R : CommRingCat.{u}) (f : Spec R ⟶ X)
    [IsOpenImmersion f] : IsAffineHom f := by
  have : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion f
  have : IsNoetherian (Spec R) := ⟨⟩
  have : PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) :=
    preservesFiniteLimits_restrictFunctor f
  apply Stacks.AffineFromVanishing.isAffineHom_of_forall_isZero_rightDerived_ideal f
  intro A hA
  let F : (Spec R).Modules := Subobject.underlying.obj A
  have : F.IsQuasicoherent := hA
  let G := Scheme.Modules.pushforward f
  let I := injectiveResolution F
  let L : CochainComplex _ ℤ := I.cocomplex.extend ComplexShape.embeddingUpNat
  let J := (G.mapHomologicalComplex (.up ℤ)).obj L
  let P := SheafOfModules.isQuasicoherent X.ringCatSheaf
  have hJ (n : ℤ) : (J.homology n).IsQuasicoherent :=
    P.prop_of_iso (mappedInjectiveResolutionHomologyIso G F n).symm
      (Stacks.AlgebraicGeometry.Tag01XJQcohInduction.higherDirectImage_isQuasicoherent f F n)
  have hQJ (n : ℤ) :
      ((DerivedCategory.homologyFunctor X.Modules n).obj
        (DerivedCategory.Q.obj J)).IsQuasicoherent :=
    P.prop_of_iso ((DerivedCategory.homologyFunctorFactors X.Modules n).app J).symm (hJ n)
  obtain ⟨H, hH, ⟨eH⟩⟩ := exists_quasicoherent_complex_model X (DerivedCategory.Q.obj J) hQJ
  let e : H.homology 1 ≅ (G.rightDerived 1).obj F :=
    ((DerivedCategory.homologyFunctorFactors X.Modules 1).app H).symm ≪≫
      (DerivedCategory.homologyFunctor X.Modules 1).mapIso eH ≪≫
      (DerivedCategory.homologyFunctorFactors X.Modules 1).app J ≪≫
      mappedInjectiveResolutionHomologyIso G F 1 ≪≫
      Stacks.AlgebraicGeometry.HigherDirectImageQcoh.derivedPlusIsoNat G F 1
  refine IsZero.of_iso (isZero_first_homology_of_derived_hom_subsingleton X H hH ?_) e.symm
  intro E hE
  have : E.IsQuasicoherent := by
    obtain ⟨q, hq, _⟩ := hE.exists_isFiniteLocallyFreeData
    have := hq
    exact q.quasiCoherentData.isQuasicoherent
  let T := (CochainComplex.singleFunctor X.Modules 1).obj E
  let B := Scheme.Modules.restrictFunctor f
  have : PreservesBinaryBiproducts B := preservesBinaryBiproducts_of_preservesBinaryCoproducts B
  have : B.Additive := Functor.additive_of_preservesBinaryBiproducts B
  have hBE : Scheme.Modules.IsFiniteLocallyFree (B.obj E) :=
    Scheme.Modules.IsFiniteLocallyFree.restrict f
      ((Scheme.Modules.isFiniteLocallyFree_iff E).mpr hE)
  have : Subsingleton
      (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (Spec R).Modules 1).obj (B.obj E)) ⟶
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Spec R).Modules 0).obj F)) :=
    derived_single_hom_subsingleton_of_isAffine R (B.obj E) F hBE
  let s : (CochainComplex.singleFunctor (Spec R).Modules 0).obj F ⟶ L :=
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 (by simp)).inv ≫
      HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat
  have : QuasiIso s := by dsimp [s]; infer_instance
  let es : DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Spec R).Modules 0).obj F) ≅
      DerivedCategory.Q.obj L := asIso (DerivedCategory.Q.map s)
  let et : DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (Spec R).Modules 1).obj (B.obj E)) ≅
      DerivedCategory.Q.obj ((B.mapHomologicalComplex (.up ℤ)).obj T) :=
    (DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex B (.up ℤ) 1).app E)).symm
  have : Subsingleton (DerivedCategory.Q.obj ((B.mapHomologicalComplex (.up ℤ)).obj T) ⟶
      DerivedCategory.Q.obj L) :=
    subsingleton_hom_of_iso et es inferInstance
  have : L.IsKInjective := CochainComplex.isKInjective_of_injective L 0
  have : Subsingleton (DerivedCategory.Q.obj T ⟶ DerivedCategory.Q.obj J) :=
    derived_hom_subsingleton_of_adjunction G B (Scheme.Modules.restrictAdjunction f) T L
  exact subsingleton_hom_of_iso (Iso.refl _) eH.symm this

/-- **On a Noetherian scheme with the resolution property the inclusion of an affine open is an
affine morphism.** The inclusion factors through the canonical isomorphism of the affine open
subscheme with the spectrum of its ring of functions. -/
theorem isAffineHom_ι_of_isAffineOpen_of_isNoetherian (X : Scheme.{u}) [IsNoetherian X]
    [HasResolutionProperty X] (U : X.Opens) (hU : IsAffineOpen U) : IsAffineHom U.ι := by
  have : QuasiSeparatedSpace X := IsLocallyNoetherian.quasiSeparatedSpace
  have : IsAffineHom hU.fromSpec := isAffineHom_of_isOpenImmersion_from_spec X _ hU.fromSpec
  rw [← hU.isoSpec_hom_fromSpec]
  infer_instance

/-- The intersection of an affine open with an affine open whose inclusion is an affine morphism
is affine: it is the image of the preimage of the second in the first. -/
private theorem isAffineOpen_inf_of_isAffineHom_ι (X : Scheme.{u}) {U V : X.Opens}
    (hV : IsAffineOpen V) [IsAffineHom U.ι] : IsAffineOpen (U ⊓ V) := by
  let W : U.toScheme.Opens := U.ι ⁻¹ᵁ V
  have hW : IsAffineOpen W := IsAffineHom.isAffine_preimage V hV
  have hImage : IsAffineOpen (U.ι ''ᵁ W) := hW.image_of_isOpenImmersion U.ι
  have hEq : U.ι ''ᵁ W = U ⊓ V := by
    simpa [W, Scheme.Opens.opensRange_ι] using
      Scheme.Hom.image_preimage_eq_opensRange_inf U.ι V
  rw [← hEq]
  exact hImage

/-- **The Noetherian case of [Stacks, Tag 0F8C].** A Noetherian scheme with the resolution
property has affine diagonal: by [Stacks, Tag 0BDX] it is enough that the intersection of two
affine opens be affine, and the inclusion of an affine open is an affine morphism. -/
theorem isAffineHom_diagonal_of_hasResolutionProperty_of_isNoetherian (X : Scheme.{u})
    [IsNoetherian X] [HasResolutionProperty X] :
    IsAffineHom (pullback.diagonal (terminal.from X)) := by
  refine ((isAffineHom_diagonal_tfae X).out 2 1).mp ?_
  intro U V hU hV
  have : IsAffineHom U.ι := isAffineHom_ι_of_isAffineOpen_of_isNoetherian X U hU
  exact isAffineOpen_inf_of_isAffineHom_ι X hV

/-- **[Stacks, Tag 0F8C] for a scheme affine over a Noetherian scheme with the resolution
property.** A scheme admitting an affine morphism to a Noetherian scheme with the resolution
property has affine diagonal.  Nothing is assumed about the source.

The target has affine diagonal by the Noetherian case, and an affine morphism carries an affine
diagonal back to its source
(`Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_diagonal_of_isAffineHom`).  This is
the whole of [Stacks, Tag 0F8C] beyond the reduction to the Noetherian case: that reduction
produces exactly such a morphism, the projection onto one stage of an inverse system of schemes
of finite type over the integers. -/
theorem isAffineHom_diagonal_of_isAffineHom_of_isNoetherian_of_hasResolutionProperty
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [IsNoetherian Y]
    [HasResolutionProperty Y] :
    IsAffineHom (pullback.diagonal (terminal.from X)) :=
  have _ : IsAffineHom (pullback.diagonal (terminal.from Y)) :=
    isAffineHom_diagonal_of_hasResolutionProperty_of_isNoetherian Y
  Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_diagonal_of_isAffineHom f

/-- **Stacks Project, Tag 0F8C**, with the reduction to the Noetherian case carried as the
hypothesis that `X` is affine over a Noetherian scheme with the resolution property.

A quasi-compact and quasi-separated scheme with the resolution property has affine diagonal.
The proof of the source reduces to the Noetherian case by writing `X` as an inverse limit of
schemes of finite type over the integers with affine transition morphisms ([Stacks, Tag 01ZA])
and locating one stage with the resolution property; what that reduction delivers, and all it
is used for, is an affine morphism from `X` to a Noetherian scheme with the resolution property.
That existential is therefore the hypothesis here — the weakest form in which the missing half
of [Stacks, Tag 0F8B] enters this tag, and one satisfied by `Y = X` and `f = 𝟙` whenever `X` is
itself Noetherian. -/
theorem isAffineHom_diagonal_of_exists_isAffineHom_isNoetherian_hasResolutionProperty
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] [HasResolutionProperty X]
    (hmodel : ∃ (Y : Scheme.{u}) (f : X ⟶ Y),
      IsAffineHom f ∧ IsNoetherian Y ∧ HasResolutionProperty Y) :
    IsAffineHom (pullback.diagonal (terminal.from X)) := by
  obtain ⟨Y, f, hf, hN, hRP⟩ := hmodel
  have _ : IsAffineHom f := hf
  have _ : IsNoetherian Y := hN
  have _ : HasResolutionProperty Y := hRP
  exact isAffineHom_diagonal_of_isAffineHom_of_isNoetherian_of_hasResolutionProperty f

/-! ### Reduction to the Noetherian case -/

/-- A quasi-compact scheme of finite type over the integers is Noetherian. -/
private theorem isNoetherian_of_locallyOfFiniteType_terminal {T : Scheme.{u}}
    [LocallyOfFiniteType (terminal.from T)] [QuasiCompact (terminal.from T)] :
    IsNoetherian T := by
  let e : (⊤_ Scheme.{u}) ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal).symm
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : IsLocallyNoetherian (⊤_ Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian e.hom
  have : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (terminal.from T)
  have : CompactSpace (⊤_ Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace e.hom
  have : CompactSpace T :=
    QuasiCompact.compactSpace_of_compactSpace (terminal.from T)
  exact {}

/-- A quasi-compact and quasi-separated scheme with the resolution property is affine over a
Noetherian scheme with the resolution property, as soon as the resolution property descends to a
stage of an inverse system of Noetherian schemes with affine transition morphisms (`hstage`). -/
private theorem exists_isAffineHom_isNoetherian_hasResolutionProperty_of_stage
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] [HasResolutionProperty X]
    (hstage : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : Iᵒᵈ ⥤ Scheme.{u}) (c : Cone D), IsLimit c →
      (∀ {i j : Iᵒᵈ} (g : i ⟶ j), IsAffineHom (D.map g)) →
      (∀ i, IsNoetherian (D.obj i)) → HasResolutionProperty c.pt →
      ∃ i, HasResolutionProperty (D.obj i)) :
    ∃ (Y : Scheme.{u}) (f : X ⟶ Y),
      IsAffineHom f ∧ IsNoetherian Y ∧ HasResolutionProperty Y := by
  obtain ⟨I, hpre, hne, hdir, D, cπ, haff, hft, hqc, ⟨hlim⟩⟩ :=
    Scheme.exists_isLimit_affine_locallyOfFiniteType X
  let _ : Preorder I := hpre
  let _ : Nonempty I := hne
  let _ : IsDirected I (· ≤ ·) := hdir
  have _ : ∀ {i j : Iᵒᵈ} (g : i ⟶ j), IsAffineHom (D.map g) := fun g => haff g
  have hnoeth : ∀ i, IsNoetherian (D.obj i) := by
    intro i
    have := hft i
    have := hqc i
    exact isNoetherian_of_locallyOfFiniteType_terminal
  obtain ⟨i, hRP⟩ := hstage D (Cone.mk X cπ) hlim (fun g => haff g) hnoeth inferInstance
  have _ : IsCofiltered Iᵒᵈ := inferInstance
  exact ⟨D.obj i, (Cone.mk X cπ).π.app i, isAffineHom_π_app D (Cone.mk X cπ) hlim i,
    hnoeth i, hRP⟩

/-- **The reduction of [Stacks, Tag 0F8C] to the Noetherian case.** A quasi-compact and
quasi-separated scheme with the resolution property is affine over a Noetherian scheme with the
resolution property.

The scheme is written as the inverse limit of a directed system of schemes of finite type over
the integers with affine transition morphisms ([Stacks, Tag 01ZA]).  Every stage is Noetherian
and every projection is affine, so the only thing at issue is the resolution property at one
stage, which is the substantial half of [Stacks, Tag 0F8B].  That half is available at
Noetherian stages — `AlgebraicGeometry.hasResolutionProperty_stage` — and the stages here are of
finite type over the integers, hence Noetherian, so this statement is unconditional.

The converse of [Stacks, Tag 0F8B] for systems of merely quasi-compact quasi-separated stages is
not needed, here or by any consumer of this tag. -/
theorem exists_isAffineHom_isNoetherian_hasResolutionProperty (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [HasResolutionProperty X] :
    ∃ (Y : Scheme.{u}) (f : X ⟶ Y),
      IsAffineHom f ∧ IsNoetherian Y ∧ HasResolutionProperty Y :=
  exists_isAffineHom_isNoetherian_hasResolutionProperty_of_stage X
    fun D c hc haff hN hRP => hasResolutionProperty_stage D c hc haff hN hRP

/-- **Stacks Project, Tag 0F8C.** A quasi-compact and quasi-separated scheme with the resolution
property has affine diagonal.

This is
`AlgebraicGeometry.isAffineHom_diagonal_of_exists_isAffineHom_isNoetherian_hasResolutionProperty`
composed with `AlgebraicGeometry.exists_isAffineHom_isNoetherian_hasResolutionProperty`, which
supplies the required affine morphism from the converse of
`AlgebraicGeometry.hasResolutionProperty_of_isLimit` at Noetherian stages
(`AlgebraicGeometry.hasResolutionProperty_stage`). -/
@[stacks 0F8C]
theorem HasResolutionProperty.isAffineHom_diagonal (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [HasResolutionProperty X] :
    IsAffineHom (pullback.diagonal (terminal.from X)) :=
  isAffineHom_diagonal_of_exists_isAffineHom_isNoetherian_hasResolutionProperty X
    (exists_isAffineHom_isNoetherian_hasResolutionProperty X)

/-- A quasi-compact and quasi-separated scheme with the resolution property has affine diagonal,
as soon as the resolution property of the limit of a directed system of quasi-compact
quasi-separated schemes with affine transition morphisms descends to some stage (`hstage`).

The scheme is written as the inverse limit of a directed system of schemes of finite type over
the integers with affine transition morphisms ([Stacks, Tag 01ZA]).  Every stage is Noetherian,
`hstage` gives one stage with the resolution property, hence affine diagonal, and the projection
onto that stage is an affine morphism, which carries the affine diagonal back to the scheme.
Without `hstage` this is `AlgebraicGeometry.HasResolutionProperty.isAffineHom_diagonal`. -/
theorem isAffineHom_diagonal_of_hasResolutionProperty (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [HasResolutionProperty X]
    (hstage : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : Iᵒᵈ ⥤ Scheme.{u}) (c : Cone D), IsLimit c →
      (∀ {i j : Iᵒᵈ} (g : i ⟶ j), IsAffineHom (D.map g)) →
      (∀ i, CompactSpace (D.obj i)) → (∀ i, QuasiSeparatedSpace (D.obj i)) →
      HasResolutionProperty c.pt → ∃ i, HasResolutionProperty (D.obj i)) :
    IsAffineHom (pullback.diagonal (terminal.from X)) := by
  obtain ⟨Y, f, _, _, _⟩ := exists_isAffineHom_isNoetherian_hasResolutionProperty_of_stage X
    fun D c hc haff hN hRP => hstage D c hc haff (fun i => (hN i).toCompactSpace)
      (fun i => have := (hN i).toIsLocallyNoetherian; IsLocallyNoetherian.quasiSeparatedSpace) hRP
  exact isAffineHom_diagonal_of_isAffineHom_of_isNoetherian_of_hasResolutionProperty f

end AlgebraicGeometry

end
