module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessResolution.Basic
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.AlgebraicGeometry.Modules.GlobalSectionsOverGamma

/-!
# The genus of a finite disjoint union

For finitely many schemes `X i` with a proper structure morphism `p : ∐ X ⟶ Spec k` on their
coproduct, `dim_k H¹(∐ X, 𝒪) = ∑ i, dim_k H¹(X i, 𝒪)`. Along the way: if finitely many open
immersions `f i : X i ⟶ Y` have pairwise disjoint ranges covering `Y`, then `𝒪_Y` is the product
of the `(f i)_* 𝒪_{X i}`, and the dimension of the cohomology of a finite product of modules is
the sum of the dimensions.

## Main results

* `AlgebraicGeometry.sections_bijective_of_disjoint_cover`: a section of `𝒪_Y` over an open is
  the same thing as a family of sections on the pieces of a disjoint open cover.
* `AlgebraicGeometry.structureSheafDisjointCoverIso`: consequently `𝒪_Y` is the product of the
  `(f i)_* 𝒪_{X i}`.
* `AlgebraicGeometry.isClosedImmersion_sigmaι`: the inclusion of a piece of a coproduct of schemes
  is a closed immersion as well as an open one.
* `AlgebraicGeometry.finrank_cohomologyOverField_biproduct` and
  `AlgebraicGeometry.finrank_cohomologyOverField_pi`: `dim_k Hⁿ(X, ⨁ⱼ ℰⱼ) = ∑ⱼ dim_k Hⁿ(X, ℰⱼ)`
  for a finite family with finite-dimensional cohomology, for an index type in any universe.
* `AlgebraicGeometry.genus_eq_sum_of_disjoint_cover`: **the genus is additive over a finite
  partition of a proper scheme into pieces that are open and closed.**
* `AlgebraicGeometry.genus_sigma`: the genus of a finite disjoint union of schemes is the sum
  of the genera of the pieces, the case of the coproduct itself.

## References

* [Stacks Project, Tag 0CDV](https://stacks.math.columbia.edu/tag/0CDV)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.CurveEulerBridge
open Stacks.AlgebraicGeometry.ProperCohomologyFinite

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasFiniteBiproducts_modules

/-! ### Sections over a disjoint cover -/

/-- Let `f i : X i ⟶ Y` be open immersions with pairwise disjoint ranges covering `Y`.  Then
restricting a section of `𝒪_Y` over an open `V` to the pieces is a bijection onto families of
sections of the `𝒪_{X i}` over the `f i ⁻¹ V`. -/
theorem sections_bijective_of_disjoint_cover
    {ι : Type u} {Y : Scheme.{u}} (X : ι → Scheme.{u})
    (f : ∀ i, X i ⟶ Y) [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ y : Y, ∃ i x, (f i).base x = y)
    (hdisj : Pairwise fun i j ↦ Disjoint (Set.range (f i).base) (Set.range (f j).base))
    (V : Y.Opens) :
    Function.Bijective (fun s : Γ(Y, V) ↦ fun i ↦ (f i).app V s) := by
  classical
  let U : ι → Y.Opens := fun i ↦ f i ''ᵁ (f i ⁻¹ᵁ V)
  let e (i) := (f i).appIso (f i ⁻¹ᵁ V)
  have hUV (i) : U i ≤ V := (Scheme.Hom.image_preimage_eq_opensRange_inf ..).trans_le inf_le_right
  have hsup : V ≤ iSup U := by
    intro y hy
    obtain ⟨i, x, rfl⟩ := hcover y
    exact Opens.mem_iSup.mpr ⟨i, x, hy, rfl⟩
  have happ (i) (s : Γ(Y, V)) :
      (e i).inv ((f i).app V s) =
        Y.presheaf.map (homOfLE (hUV i)).op s :=
    congrArg (fun q : Γ(Y, V) ⟶ Γ(Y, U i) ↦ q s) ((f i).app_appIso_inv V)
  constructor
  · intro s t h
    apply Y.sheaf.eq_of_locally_eq' U V (fun i ↦ homOfLE (hUV i)) hsup
    intro i
    show Y.presheaf.map (homOfLE (hUV i)).op s =
      Y.presheaf.map (homOfLE (hUV i)).op t
    rw [← happ, ← happ]
    exact congrArg (fun a ↦ (e i).inv a) (congrFun h i)
  · intro b
    let sf : ∀ i, Γ(Y, U i) := fun i ↦ (e i).inv (b i)
    have hc : TopCat.Presheaf.IsCompatible Y.presheaf U sf := by
      intro i j
      by_cases hij : i = j
      · subst j; rfl
      · have hbot : U i ⊓ U j = ⊥ := eq_bot_iff.2 fun y ⟨⟨a, _, ha⟩, ⟨b, _, hb⟩⟩ ↦
          Set.disjoint_left.mp (hdisj hij) ⟨a, ha⟩ ⟨b, hb⟩
        have : Subsingleton Γ(Y, U i ⊓ U j) := by rw [hbot]; infer_instance
        exact Subsingleton.elim _ _
    obtain ⟨s, hs, _⟩ := Y.sheaf.existsUnique_gluing' U V
      (fun i ↦ homOfLE (hUV i)) hsup sf hc
    refine ⟨s, funext fun i ↦ ?_⟩
    apply (e i).symm.commRingCatIsoToRingEquiv.injective
    show (e i).inv ((f i).app V s) = sf i
    exact (happ i s).trans (hs i)

/-- **The structure sheaf of a finite disjoint union is the product of the structure sheaves of
the pieces.**  For finitely many open immersions `f i : X i ⟶ Y` with pairwise disjoint ranges
covering `Y`, the canonical map `𝒪_Y ⟶ ∏ᶜ (f i)_* 𝒪_{X i}` is an isomorphism. -/
noncomputable def structureSheafDisjointCoverIso
    {ι : Type u} [Fintype ι] {Y : Scheme.{u}} (X : ι → Scheme.{u})
    (f : ∀ i, X i ⟶ Y) [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ y : Y, ∃ i x, (f i).base x = y)
    (hdisj : Pairwise fun i j ↦ Disjoint (Set.range (f i).base) (Set.range (f j).base)) :
    SheafOfModules.unit Y.ringCatSheaf ≅
      ∏ᶜ (fun i ↦ (Scheme.Modules.pushforward (f i)).obj
        (SheafOfModules.unit (X i).ringCatSheaf)) := by
  let A := fun i ↦ (Scheme.Modules.pushforward (f i)).obj
    (SheafOfModules.unit (X i).ringCatSheaf)
  let q : SheafOfModules.unit Y.ringCatSheaf ⟶ ∏ᶜ A :=
    Pi.lift (fun i ↦ SheafOfModules.unitToPushforwardObjUnit (f i).toRingCatSheafHom)
  have hq : IsIso q := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro U
    let E : Y.Modules ⥤ ModuleCat.{u} Γ(Y, U) :=
      SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)
    have : E.Additive := ⟨by intro M N a b; ext x; rfl⟩
    have : PreservesLimitsOfShape (Discrete ι) E :=
      preservesLimitsOfShape_of_equiv (Discrete.equivalence (Fintype.equivFin ι).symm) E
    let e : E.obj (∏ᶜ A) ≅ ModuleCat.of Γ(Y, U) (∀ i, E.obj (A i)) :=
      asIso (piComparison E A) ≪≫ ModuleCat.piIsoPi _
    have he (x : E.obj (∏ᶜ A)) (i) : e.hom x i = (E.map (Pi.π A i)) x := by
      change ((piComparison E A ≫ (ModuleCat.piIsoPi _).hom).hom x) i = _
      exact congrArg (fun g : E.obj (∏ᶜ A) ⟶ E.obj (A i) ↦ g x)
        (show piComparison E A ≫ (ModuleCat.piIsoPi _).hom ≫
          ModuleCat.ofHom (LinearMap.proj i) = E.map (Pi.π A i) by
            rw [ModuleCat.piIsoPi_hom_ker_subtype, piComparison_comp_π])
    have hc : Function.Bijective (fun x ↦ e.hom ((E.map q) x)) := by
      have hfun : (fun x ↦ e.hom ((E.map q) x)) =
          (fun s : Γ(Y, U) ↦ fun i ↦ (f i).app U s) := by
        have hmor (i : ι) : E.map q ≫ E.map (Pi.π A i) =
            E.map (SheafOfModules.unitToPushforwardObjUnit (f i).toRingCatSheafHom) :=
          (E.map_comp q (Pi.π A i)).symm.trans (congrArg E.map
            (Pi.lift_π (fun j ↦ SheafOfModules.unitToPushforwardObjUnit
              (f j).toRingCatSheafHom) i))
        funext x i
        refine (he ((E.map q) x) i).trans ?_
        exact congrArg
          (fun g : E.obj (SheafOfModules.unit Y.ringCatSheaf) ⟶ E.obj (A i) ↦ g x) (hmor i)
      rw [hfun]
      exact sections_bijective_of_disjoint_cover X f hcover hdisj U
    have : IsIso (E.map q) := (ConcreteCategory.isIso_iff_bijective _).mpr
      ((Function.Bijective.of_comp_iff' e.toLinearEquiv.bijective _).mp hc)
    exact inferInstanceAs (IsIso ((forget₂ (ModuleCat Γ(Y, U)) AddCommGrpCat).map (E.map q)))
  exact asIso q

/-- The inclusion of a piece into a disjoint union of schemes is a closed immersion. -/
theorem isClosedImmersion_sigmaι {ι : Type u} (X : ι → Scheme.{u}) (i : ι) :
    IsClosedImmersion (Limits.Sigma.ι X i) := by
  classical
  apply IsClosedImmersion.of_isPreimmersion
  have he : (Set.range (Limits.Sigma.ι X i).base)ᶜ = ⋃ j : {j : ι // j ≠ i},
      Set.range (Limits.Sigma.ι X j.1).base := by
    ext y
    obtain ⟨⟨j, x⟩, rfl⟩ := (sigmaMk X).surjective y
    simp only [sigmaMk_mk]
    constructor
    · intro hy
      have hji : j ≠ i := by rintro rfl; exact hy ⟨x, rfl⟩
      exact Set.mem_iUnion.mpr ⟨⟨j, hji⟩, x, rfl⟩
    · rintro hy ⟨z, hz⟩
      obtain ⟨⟨l, hli⟩, w, hw⟩ := Set.mem_iUnion.mp hy
      have := (sigmaι_eq_iff X l i w z).mp (hw.trans hz.symm)
      exact hli (congrArg Sigma.fst this)
  rw [← isOpen_compl_iff, he]
  exact isOpen_iUnion fun j ↦ (Limits.Sigma.ι X j.1).isOpenEmbedding.isOpen_range

/-! ### Cohomology of a finite disjoint union -/

/-- **The dimension of the cohomology of a finite biproduct is the sum of the dimensions**, given
that each summand has finite-dimensional cohomology. -/
theorem finrank_cohomologyOverField_biproduct (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {J : Type u} [Fintype J] (E : J → X.Modules)
    [HasBiproduct E] (n : ℕ)
    (hfin : ∀ j, FiniteDimensional k (cohomologyOverField k f (E j) n)) :
    Module.finrank k (cohomologyOverField k f (⨁ E) n) =
      ∑ j, Module.finrank k (cohomologyOverField k f (E j) n) := by
  classical
  let d := Fintype.equivFin J
  let E' : Fin (Fintype.card J) → X.Modules := E ∘ d.symm
  have hre : (⨁ E) ≅ ⨁ E' :=
    biproduct.whiskerEquiv d fun j ↦ eqToIso (congrArg E (d.symm_apply_apply j))
  have hfin' (j : Fin (Fintype.card J)) :
      Module.Finite k ((ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj (E' j))) :=
    cohomologyOverField_eq_restrictScalars_appTop k f (E' j) n ▸ hfin (d.symm j)
  obtain ⟨e⟩ := nonempty_cohomology_ringBase_biproduct_linearEquiv k f E' n
  have hbip : Module.finrank k (cohomologyOverField k f (⨁ E') n) =
      ∑ j, Module.finrank k (cohomologyOverField k f (E' j) n) := by
    rw [cohomologyOverField_eq_restrictScalars_appTop k f (⨁ E') n,
      Finset.sum_congr rfl fun j _ ↦ congrArg (fun M : ModuleCat.{u} k ↦ Module.finrank k M)
        (cohomologyOverField_eq_restrictScalars_appTop k f (E' j) n),
      e.finrank_eq]
    exact Module.finrank_pi_fintype k
  rw [(cohomologyOverFieldIso k f hre n).toLinearEquiv.finrank_eq, hbip]
  exact Fintype.sum_equiv d.symm _ _ fun j ↦ rfl

/-- **The dimension of the cohomology of a finite product is the sum of the dimensions**, given
that each factor has finite-dimensional cohomology. -/
theorem finrank_cohomologyOverField_pi (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {J : Type u} [Fintype J] (E : J → X.Modules)
    (n : ℕ) (hfin : ∀ j, FiniteDimensional k (cohomologyOverField k f (E j) n)) :
    Module.finrank k (cohomologyOverField k f (∏ᶜ E) n) =
      ∑ j, Module.finrank k (cohomologyOverField k f (E j) n) := by
  let : HasFiniteBiproducts X.Modules := hasFiniteBiproducts_modules
  let : HasBiproductsOfShape J X.Modules := hasBiproductsOfShape_finite _
  let : HasBiproduct E := HasBiproductsOfShape.has_biproduct E
  have hiso : (⨁ E) ≅ ∏ᶜ E :=
    (biproduct.isLimit E).conePointUniqueUpToIso (limit.isLimit (Discrete.functor E))
  rw [← (cohomologyOverFieldIso k f hiso n).toLinearEquiv.finrank_eq]
  exact finrank_cohomologyOverField_biproduct k f E n hfin

/-- **The genus is additive over a finite partition into clopen pieces.**  Let `f i : A i ⟶ Y`
be finitely many immersions, each open and closed, whose ranges are pairwise disjoint and cover
`Y`, and let `p : Y ⟶ Spec k` be proper.  Then
`dim_k H¹(Y, 𝒪_Y) = ∑ i, dim_k H¹(A i, 𝒪_{A i})`. -/
theorem genus_eq_sum_of_disjoint_cover {k : Type u} [Field k] {ι : Type u} [Fintype ι]
    {Y : Scheme.{u}} {A : ι → Scheme.{u}} (f : ∀ i, A i ⟶ Y)
    [∀ i, IsOpenImmersion (f i)] [∀ i, IsClosedImmersion (f i)]
    (hcover : ∀ y : Y, ∃ i x, (f i).base x = y)
    (hdisj : Pairwise fun i j ↦ Disjoint (Set.range (f i).base) (Set.range (f j).base))
    (p : Y ⟶ Spec (.of k)) [IsProper p] :
    genus p = ∑ i, genus (f i ≫ p) := by
  classical
  have : ∀ i, IsFinite (f i) := fun i ↦ inferInstance
  have hpi : ∀ i, IsProper (f i ≫ p) := fun i ↦ inferInstance
  let B : ι → Y.Modules := fun i ↦ (Scheme.Modules.pushforward (f i)).obj
    (SheafOfModules.unit (A i).ringCatSheaf)
  have ecov : SheafOfModules.unit Y.ringCatSheaf ≅ ∏ᶜ B :=
    structureSheafDisjointCoverIso A f hcover hdisj
  have hpush (i : ι) : cohomologyOverField k p (B i) 1 ≅
      cohomologyOverField k (f i ≫ p) (SheafOfModules.unit (A i).ringCatSheaf) 1 :=
    (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k (f i) p
      (SheafOfModules.unit (A i).ringCatSheaf) 1).symm
  have hAi (i : ι) : Module.finrank k (cohomologyOverField k p (B i) 1) = genus (f i ≫ p) := by
    rw [(hpush i).toLinearEquiv.finrank_eq, genus_eq_finrank_structureSheafCohomology,
      (structureSheafCohomologyIsoCohomologyOverField k (f i ≫ p) 1).toLinearEquiv.finrank_eq]
  have hfin (i : ι) : FiniteDimensional k (cohomologyOverField k p (B i) 1) := by
    have := isCoherent_unit k (f i ≫ p)
    have : FiniteDimensional k (cohomologyOverField k (f i ≫ p)
        (SheafOfModules.unit (A i).ringCatSheaf) 1) :=
      finiteDimensional_cohomologyOverField_of_isProper k (f i ≫ p) _ 1
    exact Module.Finite.equiv (hpush i).toLinearEquiv.symm
  rw [genus_eq_finrank_structureSheafCohomology,
    (structureSheafCohomologyIsoCohomologyOverField k p 1).toLinearEquiv.finrank_eq,
    (cohomologyOverFieldIso k p ecov 1).toLinearEquiv.finrank_eq]
  exact (finrank_cohomologyOverField_pi k p B 1 hfin).trans
    (Finset.sum_congr rfl fun i _ ↦ hAi i)

/-- **The genus is additive over a finite disjoint union.**  For finitely many schemes `X i`
with a proper structure morphism `p : ∐ X ⟶ Spec k` on their coproduct,
`dim_k H¹(∐ X, 𝒪) = ∑ i, dim_k H¹(X i, 𝒪)`. -/
theorem genus_sigma {k : Type u} [Field k] {ι : Type u} [Fintype ι]
    (X : ι → Scheme.{u}) (p : (∐ X) ⟶ Spec (.of k)) [IsProper p] :
    genus p = ∑ i, genus (Limits.Sigma.ι X i ≫ p) := by
  have : ∀ i, IsClosedImmersion (Limits.Sigma.ι X i) := isClosedImmersion_sigmaι X
  refine genus_eq_sum_of_disjoint_cover (Limits.Sigma.ι X) (fun y ↦ ?_) (fun i j hij ↦ ?_) p
  · obtain ⟨⟨i, x⟩, hx⟩ := (sigmaMk X).surjective y
    exact ⟨i, x, by simpa using hx⟩
  · exact Set.disjoint_left.mpr fun y hy hj ↦
      (disjoint_opensRange_sigmaι X i j hij).le_bot ⟨hy, hj⟩

end AlgebraicGeometry

end
