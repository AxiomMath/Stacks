module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Simple
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.SimpleModule.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Linear autoequivalences of finite-length modules

Over a Noetherian local ring `A`, every `A`-linear self-equivalence of the category of
finite-length `A`-modules is naturally isomorphic to the identity functor. This is the
rigidity statement behind the uniqueness of a dualizing complex up to shift and twist by an
invertible module.

The proof goes through the quotients `A / m ^ (n + 1)`. A self-equivalence fixes the
annihilator of every object, carries the residue field to a copy of itself, and therefore
carries `A / m ^ (n + 1)` to a cyclic module with the same annihilator, hence to a copy of
itself; the resulting isomorphisms can be chosen compatibly with the transition maps
`A / m ^ (n + 2) → A / m ^ (n + 1)`. Since every finite-length module is annihilated by some
power of `m`, representing it as `Hom(A / m ^ (n + 1), -)` transports the chosen
isomorphisms into a natural isomorphism from the identity functor.

## Main results

* `Dualizing.linearEquivalenceFiniteLengthIsoIdentity` identifies a linear self-equivalence
  of finite-length modules with the identity functor.

## Implementation notes

The category of finite-length modules is expressed as the full subcategory of
`ModuleCat A` cut out by `IsFiniteLength A`. The source's assertion that the
self-equivalence is `A`-linear is represented by `Functor.Linear A F.functor`.

## References

* [Stacks Project, Tag 0A7P](https://stacks.math.columbia.edu/tag/0A7P)
-/

@[expose] public section

namespace Dualizing

section FiniteLengthAutoequivalence

open CategoryTheory CategoryTheory.Limits

universe u

/-- A linear functor preserves zero morphisms. -/
private lemma linear_functor_map_zero
    {A : Type u} [CommRing A] {C : Type*} [Category C] [Preadditive C]
    [CategoryTheory.Linear A C] (G : C ⥤ C) [G.Linear A] (X Y : C) :
    G.map (0 : X ⟶ Y) = 0 :=
  calc
    G.map (0 : X ⟶ Y) = G.map ((0 : A) • (0 : X ⟶ Y)) := by rw [smul_zero]
    _ = 0 := by rw [G.map_smul, zero_smul]

private lemma map_smul_id_eq_zero
    {A : Type u} [CommRing A] {C : Type*} [Category C] [Preadditive C]
    [CategoryTheory.Linear A C] (G : C ⥤ C) [G.Linear A]
    (X : C) (r : A) (hr : r • (𝟙 X) = 0) :
    r • (𝟙 (G.obj X)) = 0 := by
  calc
    r • (𝟙 (G.obj X)) = G.map (r • (𝟙 X)) := by simp
    _ = 0 := by rw [hr, linear_functor_map_zero (A := A)]

private lemma map_smul_id_eq_zero_iff
    {A : Type u} [CommRing A] {C : Type*} [Category C] [Preadditive C]
    [CategoryTheory.Linear A C] (G : C ⥤ C) [G.Linear A] [G.Faithful]
    (X : C) (r : A) :
    r • (𝟙 X) = 0 ↔ r • (𝟙 (G.obj X)) = 0 := by
  refine ⟨map_smul_id_eq_zero G X r, fun h => G.map_injective ?_⟩
  rw [linear_functor_map_zero (A := A), G.map_smul, G.map_id]
  exact h

private lemma smul_id_eq_zero_iff_annihilator
    {A : Type u} [CommRing A]
    (X : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M)) (r : A) :
    r • (𝟙 X) = 0 ↔ r ∈ Module.annihilator A X.obj := by
  rw [Module.mem_annihilator]
  refine ⟨fun h x => congrArg (fun f : X ⟶ X => f.hom.hom x) h, fun h => ?_⟩
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  exact LinearMap.ext h

private lemma annihilator_image_eq
    (A : Type u) [CommRing A]
    (F : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M) ≌
      ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    [F.functor.Linear A]
    (X : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M)) :
    Module.annihilator A (F.functor.obj X).obj = Module.annihilator A X.obj := by
  ext r
  rw [← smul_id_eq_zero_iff_annihilator,
    ← smul_id_eq_zero_iff_annihilator]
  exact (map_smul_id_eq_zero_iff F.functor X r).symm

private lemma isSimpleModule_residueField
    (A : Type u) [CommRing A] [IsLocalRing A] :
    IsSimpleModule A (A ⧸ IsLocalRing.maximalIdeal A) :=
  isSimpleModule_iff_isCoatom.mpr
    (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal A))

private lemma simpleModule_iso_residueField
    (A : Type u) [CommRing A] [IsLocalRing A]
    (M : ModuleCat.{u} A) [IsSimpleModule A M] :
    Nonempty (M ≅ ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A)) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (inferInstance : IsSimpleModule A M)
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  exact ⟨e.toModuleIso⟩

private lemma finiteLength_of_simpleModule
    {A : Type u} [Ring A] {M : Type u} [AddCommGroup M] [Module A M]
    [IsSimpleModule A M] : IsFiniteLength A M :=
  isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

private lemma residue_isFiniteLength
    (A : Type u) [CommRing A] [IsLocalRing A] :
    IsFiniteLength A (A ⧸ IsLocalRing.maximalIdeal A) := by
  have := isSimpleModule_residueField A
  exact finiteLength_of_simpleModule

private instance finiteLength_closedUnderSubobjects
    (A : Type u) [CommRing A] :
    ObjectProperty.IsClosedUnderSubobjects
      ((fun M : ModuleCat.{u} A => IsFiniteLength A M) :
        ObjectProperty (ModuleCat.{u} A)) where
  prop_of_mono := fun f _ hY =>
    IsFiniteLength.of_injective hY ((ModuleCat.mono_iff_injective f).mp inferInstance)

private instance finiteLength_closedUnderQuotients
    (A : Type u) [CommRing A] :
    ObjectProperty.IsClosedUnderQuotients
      ((fun M : ModuleCat.{u} A => IsFiniteLength A M) :
        ObjectProperty (ModuleCat.{u} A)) where
  prop_of_epi := fun f _ hX =>
    IsFiniteLength.of_surjective hX ((ModuleCat.epi_iff_surjective f).mp inferInstance)

private instance finiteLength_containsZero
    (A : Type u) [CommRing A] :
    ObjectProperty.ContainsZero
      ((fun M : ModuleCat.{u} A => IsFiniteLength A M) :
        ObjectProperty (ModuleCat.{u} A)) where
  exists_zero := ⟨ModuleCat.of A (Fin 0 → A),
    (ModuleCat.isZero_iff_subsingleton).2 inferInstance,
    IsFiniteLength.of_subsingleton⟩

private lemma finiteLength_product
    (A : Type u) [CommRing A] {J : Type} [Finite J]
    (f : J → ModuleCat.{u} A) (hf : ∀ j, IsFiniteLength A (f j)) :
    IsFiniteLength A ((∏ᶜ f : ModuleCat.{u} A)) := by
  let (j : J) : IsNoetherian A (f j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hf j)).1
  let (j : J) : IsArtinian A (f j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hf j)).2
  have hpi : IsFiniteLength A (∀ j, f j) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  let e : (∏ᶜ f) ≅ ModuleCat.of A (∀ j, f j) :=
    IsLimit.conePointUniqueUpToIso (limit.isLimit (Discrete.functor f))
      (ModuleCat.HasLimit.productLimitCone f).isLimit
  exact IsFiniteLength.of_injective hpi
    ((ModuleCat.mono_iff_injective e.hom).mp inferInstance)

private instance finiteLength_closedUnderBinaryProducts
    (A : Type u) [CommRing A] :
    ObjectProperty.IsClosedUnderLimitsOfShape
      ((fun M : ModuleCat.{u} A => IsFiniteLength A M) :
        ObjectProperty (ModuleCat.{u} A)) (Discrete WalkingPair) := by
  refine ⟨?_⟩
  rintro X ⟨p⟩
  let f : WalkingPair → ModuleCat.{u} A := fun j => p.diag.obj ⟨j⟩
  have hdiag : Discrete.functor f = p.diag :=
    Discrete.functor_ext (fun _ => rfl)
  let q := p.toLimitPresentation.changeDiag (eqToIso hdiag)
  let e : X ≅ (∏ᶜ f : ModuleCat.{u} A) :=
    IsLimit.conePointUniqueUpToIso q.isLimit (limit.isLimit (Discrete.functor f))
  exact IsFiniteLength.of_injective (f := e.hom.hom)
    (finiteLength_product A f (fun j => p.prop_diag_obj ⟨j⟩))
    ((ModuleCat.mono_iff_injective e.hom).mp inferInstance)

private instance finiteLength_closedUnderFiniteProducts
    (A : Type u) [CommRing A] :
    ObjectProperty.IsClosedUnderFiniteProducts
      ((fun M : ModuleCat.{u} A => IsFiniteLength A M) :
        ObjectProperty (ModuleCat.{u} A)) :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

private lemma finiteLength_linear_equivalence_additive
    (A : Type u) [CommRing A]
    (F : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M) ≌
      ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    [F.functor.Linear A] : F.functor.Additive := by
  have : F.functor.PreservesZeroMorphisms :=
    ⟨fun X Y => linear_functor_map_zero (A := A) F.functor X Y⟩
  exact Functor.additive_of_preserves_binary_products F.functor

private lemma simple_module_of_simple_finiteLength
    (A : Type u) [CommRing A]
    (X : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    [Simple X] : IsSimpleModule A X.obj := by
  let P : ObjectProperty (ModuleCat.{u} A) :=
    fun M => IsFiniteLength A M
  have hX : Simple X.obj := by
    refine ⟨fun {Y} f _ => ?_⟩
    let Y' : P.FullSubcategory := ⟨Y, P.prop_of_mono f X.property⟩
    let g : Y' ⟶ X := P.homMk f
    have : Mono g := P.ι.mono_of_mono_map (by simpa [g] using inferInstanceAs (Mono f))
    constructor
    · intro h hf
      have : IsIso g := (P.isIso_hom_iff g).mp h
      exact (Simple.mono_isIso_iff_nonzero g).mp inferInstance
        (P.ι.map_injective (by simpa [g] using hf))
    · intro h
      have : IsIso g := (Simple.mono_isIso_iff_nonzero g).mpr
        (fun hg => h (congrArg InducedCategory.Hom.hom hg))
      exact (P.isIso_hom_iff g).mpr inferInstance
  exact (simple_iff_isSimpleModule' X.obj).mp hX

private lemma simple_finiteLength_of_simple_module
    (A : Type u) [CommRing A]
    (X : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    [IsSimpleModule A X.obj] : Simple X := by
  let P : ObjectProperty (ModuleCat.{u} A) :=
    fun M => IsFiniteLength A M
  have : Simple (P.ι.obj X) :=
    (simple_iff_isSimpleModule' (P.ι.obj X)).mpr (by
      simpa only [ObjectProperty.ι_obj] using (inferInstance : IsSimpleModule A X.obj))
  have : P.ι.PreservesMonomorphisms :=
    P.preservesMonomorphisms_ι_of_isNormalEpiCategory
  exact Functor.simple_of_simple_obj P.ι X

private lemma residue_iso_image
    (A : Type u) [CommRing A] [IsLocalRing A]
    (F : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M) ≌
      ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M)) :
    let K : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M) :=
        ⟨ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A),
          residue_isFiniteLength A⟩
    Nonempty (F.functor.obj K ≅ K) := by
  let P : ObjectProperty (ModuleCat.{u} A) :=
    fun M => IsFiniteLength A M
  have := isSimpleModule_residueField A
  let K : P.FullSubcategory :=
    ⟨ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A), residue_isFiniteLength A⟩
  have : Simple K := simple_finiteLength_of_simple_module A K
  have : Simple (F.functor.obj K) := simple_obj F.functor K
  have : IsSimpleModule A (F.functor.obj K).obj :=
    simple_module_of_simple_finiteLength A (F.functor.obj K)
  obtain ⟨e⟩ := simpleModule_iso_residueField A (F.functor.obj K).obj
  exact ⟨P.isoMk e⟩

private lemma quotient_mk_eq_smul_one {A : Type u} [CommRing A] (I : Ideal A) (a : A) :
    Ideal.Quotient.mk I a = a • (1 : A ⧸ I) := by
  simp [Algebra.smul_def]

private lemma hom_quotient_smul
    (A : Type u) [CommRing A]
    (I J : Ideal A) (hIJ : I ≤ J)
    (f : ModuleCat.of A (A ⧸ I) ⟶ ModuleCat.of A (A ⧸ J)) :
    ∃ r : A, f = r • ModuleCat.ofHom (Ideal.Quotient.factorₐ A hIJ).toLinearMap := by
  obtain ⟨r, hr⟩ :=
    Ideal.Quotient.mk_surjective (f.hom (1 : A ⧸ I))
  refine ⟨r, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [ModuleCat.hom_smul, ModuleCat.hom_ofHom]
  rw [quotient_mk_eq_smul_one, map_smul, LinearMap.smul_apply, map_smul]
  simp [← hr, Algebra.smul_def, mul_comm]

private lemma cyclic_of_hom_residue_cyclic
    (A : Type u) [CommRing A] [IsLocalRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (g : M →ₗ[A] (A ⧸ IsLocalRing.maximalIdeal A))
    (hg : g ≠ 0)
    (hgen : ∀ h : M →ₗ[A] (A ⧸ IsLocalRing.maximalIdeal A),
      ∃ r : A, h = r • g) :
    ∃ e : M, Submodule.span A {e} = ⊤ := by
  have := isSimpleModule_residueField A
  obtain ⟨e, he⟩ := (g.surjective_of_ne_zero hg) 1
  refine ⟨e, ?_⟩
  by_contra hspan
  obtain ⟨S, hS, hle⟩ :=
    (eq_top_or_exists_le_coatom (Submodule.span A {e})).resolve_left hspan
  have : IsSimpleModule A (M ⧸ S) := isSimpleModule_iff_isCoatom.mpr hS
  obtain ⟨i⟩ := simpleModule_iso_residueField A (ModuleCat.of A (M ⧸ S))
  let h : M →ₗ[A] (A ⧸ IsLocalRing.maximalIdeal A) := i.hom.hom.comp S.mkQ
  have hh_surj : Function.Surjective h :=
    (ModuleCat.epi_iff_surjective i.hom).mp inferInstance |>.comp S.mkQ_surjective
  have hh : h ≠ 0 := LinearMap.ne_zero_of_surjective hh_surj
  have heS : e ∈ S := hle (Submodule.mem_span_singleton_self e)
  have hhe : h e = 0 := by
    have hq : S.mkQ e = 0 := by simpa using heS
    simp [h, hq]
  obtain ⟨r, hr⟩ := hgen h
  have hr1 : r • (1 : A ⧸ IsLocalRing.maximalIdeal A) = 0 := by
    simpa [hr, he] using hhe
  have hrall (z : A ⧸ IsLocalRing.maximalIdeal A) : r • z = 0 := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [quotient_mk_eq_smul_one, smul_comm, hr1, smul_zero]
  apply hh
  rw [hr]
  ext x
  exact hrall (g x)

private lemma image_quotient_is_cyclic
    (A : Type u) [CommRing A] [IsLocalRing A]
    (F : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M) ≌
      ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    [F.functor.Linear A]
    (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A)
    (hfinite : IsFiniteLength A (A ⧸ I)) :
    let Q : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M) :=
        ⟨ModuleCat.of A (A ⧸ I), hfinite⟩
    ∃ x : (F.functor.obj Q).obj, Submodule.span A {x} = ⊤ := by
  let P : ObjectProperty (ModuleCat.{u} A) := fun M => IsFiniteLength A M
  let K : P.FullSubcategory :=
    ⟨ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A), residue_isFiniteLength A⟩
  let Q : P.FullSubcategory := ⟨ModuleCat.of A (A ⧸ I), hfinite⟩
  obtain ⟨e⟩ := residue_iso_image A F
  let q : Q ⟶ K := P.homMk (ModuleCat.ofHom (Ideal.Quotient.factorₐ A hI).toLinearMap)
  let g : (F.functor.obj Q).obj →ₗ[A] K.obj := (F.functor.map q ≫ e.hom).hom.hom
  have : F.functor.Additive := finiteLength_linear_equivalence_additive A F
  have hq_surj : Function.Surjective q.hom.hom := by
    change Function.Surjective (Ideal.Quotient.factor hI)
    exact Ideal.Quotient.factor_surjective hI
  have hq_ne : q ≠ 0 := by
    intro hq0
    have hz : q.hom.hom = 0 := by
      simpa using congrArg (fun f : Q ⟶ K => f.hom.hom) hq0
    exact (LinearMap.ne_zero_of_surjective hq_surj) hz
  have hg_ne : g ≠ 0 := by
    intro hg0
    have hcomp : F.functor.map q ≫ e.hom = 0 := P.hom_ext (ModuleCat.hom_ext hg0)
    have hFq : F.functor.map q = 0 := by
      calc
        F.functor.map q = (F.functor.map q ≫ e.hom) ≫ e.inv := by simp
        _ = 0 := by simp [hcomp]
    apply hq_ne
    apply F.functor.map_injective
    simpa using hFq
  have hgen : ∀ h : (F.functor.obj Q).obj →ₗ[A] K.obj, ∃ r : A, h = r • g := by
    intro h
    let hh : F.functor.obj Q ⟶ K := P.homMk (ModuleCat.ofHom h)
    obtain ⟨f, hf⟩ := F.functor.map_surjective (hh ≫ e.inv)
    obtain ⟨r, hr⟩ := hom_quotient_smul A I _ hI f.hom
    have hf_eq : f = r • q := P.hom_ext hr
    have hhcat : hh = r • (F.functor.map q ≫ e.hom) := by
      calc
        hh = (hh ≫ e.inv) ≫ e.hom := by simp
        _ = F.functor.map f ≫ e.hom := by rw [hf]
        _ = r • (F.functor.map q ≫ e.hom) := by
          rw [hf_eq, F.functor.map_smul, Linear.smul_comp]
    exact ⟨r, congrArg (fun t : F.functor.obj Q ⟶ K => t.hom.hom) hhcat⟩
  let _ : Module.Finite A (F.functor.obj Q).obj :=
    have : IsNoetherian A (F.functor.obj Q).obj :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp (F.functor.obj Q).property).1
    inferInstance
  exact cyclic_of_hom_residue_cyclic A (F.functor.obj Q).obj g hg_ne hgen

private lemma image_quotient_iso
    (A : Type u) [CommRing A] [IsLocalRing A]
    (F : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M) ≌
      ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    [F.functor.Linear A]
    (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A)
    (hfinite : IsFiniteLength A (A ⧸ I)) :
    let Q : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M) :=
        ⟨ModuleCat.of A (A ⧸ I), hfinite⟩
    Nonempty (Q ≅ F.functor.obj Q) := by
  let P : ObjectProperty (ModuleCat.{u} A) := fun M => IsFiniteLength A M
  let Q : P.FullSubcategory := ⟨ModuleCat.of A (A ⧸ I), hfinite⟩
  obtain ⟨x, hx⟩ := image_quotient_is_cyclic A F I hI hfinite
  let t : A →ₗ[A] (F.functor.obj Q).obj :=
    LinearMap.toSpanSingleton A (F.functor.obj Q).obj x
  have hker : LinearMap.ker t = (I : Submodule A A) := by
    change LinearMap.ker (LinearMap.toSpanSingleton A (F.functor.obj Q).obj x) = I
    rw [← Submodule.annihilator_span_singleton, hx, Submodule.annihilator_top,
      annihilator_image_eq A F Q]
    exact Ideal.annihilator_quotient
  have ht_surj : Function.Surjective t := by
    rw [← LinearMap.range_eq_top]
    change LinearMap.range (LinearMap.toSpanSingleton A (F.functor.obj Q).obj x) = ⊤
    rw [LinearMap.range_toSpanSingleton]
    exact hx
  let l : (A ⧸ I) →ₗ[A] (F.functor.obj Q).obj :=
    I.liftQ t hker.ge
  have hl_inj : Function.Injective l :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot I t hker.ge hker.le)
  have hl_surj : Function.Surjective l := by
    intro y
    obtain ⟨a, rfl⟩ := ht_surj y
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  exact ⟨P.isoMk (LinearEquiv.ofBijective l ⟨hl_inj, hl_surj⟩).toModuleIso⟩

private lemma finite_length_annihilated_by_power
    (A : Type u) [CommRing A] [IsLocalRing A]
    (M : Type u) [AddCommGroup M] [Module A M]
    (hM : IsFiniteLength A M) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal A ^ n ≤ Module.annihilator A M := by
  let _ : IsNoetherian A M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  let _ : IsArtinian A M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).2
  let f : ℕ →o (Submodule A M)ᵒᵈ :=
    ⟨fun n => OrderDual.toDual ((IsLocalRing.maximalIdeal A ^ n) • ⊤),
      fun n k hnk => Submodule.smul_mono_left (Ideal.pow_le_pow_right hnk)⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes f
  let N : Submodule A M := (IsLocalRing.maximalIdeal A ^ n) • ⊤
  have hNfg : N.FG := IsNoetherian.noetherian N
  have hNle : N ≤ IsLocalRing.maximalIdeal A • N := by
    have hs := hn (n + 1) (Nat.le_succ n)
    change (IsLocalRing.maximalIdeal A ^ n) • (⊤ : Submodule A M) =
      (IsLocalRing.maximalIdeal A ^ (n + 1)) • ⊤ at hs
    simpa [N, pow_succ, smul_smul, mul_comm] using hs.le
  have hNbot : N = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      (IsLocalRing.maximalIdeal A) N hNfg hNle (by
        rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top])
  refine ⟨n, ?_⟩
  rw [← Submodule.annihilator_top]
  exact Submodule.le_annihilator_iff.mpr hNbot

private lemma maximalIdeal_power_quotient_isFiniteLength
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (n : ℕ) :
    IsFiniteLength A (A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1)) := by
  let I : Ideal A := IsLocalRing.maximalIdeal A ^ (n + 1)
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    (Ideal.pow_le_self (Nat.succ_ne_zero n))
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsNoetherianRing (A ⧸ I) := inferInstance
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal (A ⧸ I)) := by
    use n + 1
    rw [← IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
      ← Ideal.map_pow]
    change Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal A ^ (n + 1)) = ⊥
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  have : IsArtinianRing (A ⧸ I) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal (A ⧸ I)).mpr hnil
  change IsFiniteLength A (A ⧸ I)
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_quotient I,
      isArtinian_of_surjective_algebraMap
        (Ideal.Quotient.mk_surjective (I := I))⟩

private abbrev powerQuotient
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (n : ℕ) : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M) :=
  ⟨ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1)),
    maximalIdeal_power_quotient_isFiniteLength A n⟩

private def powerQuotientMap
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {m n : ℕ} (h : m ≤ n) : powerQuotient A n ⟶ powerQuotient A m :=
  ObjectProperty.homMk <| ModuleCat.ofHom <|
    (Ideal.Quotient.factorₐ A
      (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))).toLinearMap

private lemma unit_of_surjective_smul_quotient_map
    (A : Type u) [CommRing A] [IsLocalRing A]
    (I J : Ideal A) (hIJ : I ≤ J) (hJ : J ≤ IsLocalRing.maximalIdeal A)
    (r : A)
    (hsurj : Function.Surjective
      ((r • (Ideal.Quotient.factorₐ A hIJ).toLinearMap) :
        (A ⧸ I) →ₗ[A] (A ⧸ J))) : IsUnit r := by
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro hr
  obtain ⟨z, hz⟩ := hsurj (1 : A ⧸ J)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hza : (Ideal.Quotient.mk J) (r * a) = 1 := by
    simpa [Algebra.smul_def] using hz
  have hprod : r * a ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.maximalIdeal A).mul_mem_right a hr
  have hsub : r * a - 1 ∈ IsLocalRing.maximalIdeal A :=
    hJ ((Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp hza)
  have hone : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    have hh := (IsLocalRing.maximalIdeal A).sub_mem hprod hsub
    simp at hh
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    ((IsLocalRing.maximalIdeal A).eq_top_iff_one.mpr hone)

private lemma image_power_quotient_map_surjective
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (F : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M) ≌
      ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    (n : ℕ) :
    Function.Surjective
      (F.functor.map (powerQuotientMap A (Nat.le_succ n))).hom.hom := by
  let P : ObjectProperty (ModuleCat.{u} A) := fun M => IsFiniteLength A M
  let q := powerQuotientMap A (Nat.le_succ n)
  have hq_surj : Function.Surjective q.hom.hom := by
    change Function.Surjective (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.add_le_add_right (Nat.le_succ n) 1)))
    exact Ideal.Quotient.factor_surjective _
  have : Epi q := P.ι.epi_of_epi_map
    ((ModuleCat.epi_iff_surjective q.hom).mpr hq_surj)
  have : Epi (F.functor.map q) := inferInstance
  have : P.ι.PreservesEpimorphisms :=
    P.preservesEpimorphisms_ι_of_isNormalMonoCategory
  have : Epi (F.functor.map q).hom := by
    change Epi (P.ι.map (F.functor.map q))
    infer_instance
  exact (ModuleCat.epi_iff_surjective (F.functor.map q).hom).mp inferInstance

private lemma power_quotient_iso_exists
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (F : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M) ≌
      ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    [F.functor.Linear A] (n : ℕ) :
    Nonempty (powerQuotient A n ≅ F.functor.obj (powerQuotient A n)) :=
  image_quotient_iso A F _
    (Ideal.pow_le_self (Nat.succ_ne_zero n))
    (maximalIdeal_power_quotient_isFiniteLength A n)

private lemma power_quotient_iso_next
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (F : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M) ≌
      ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    [F.functor.Linear A] (n : ℕ)
    (α : powerQuotient A n ≅ F.functor.obj (powerQuotient A n)) :
    ∃ β : powerQuotient A (n + 1) ≅ F.functor.obj (powerQuotient A (n + 1)),
      β.hom ≫ F.functor.map (powerQuotientMap A (Nat.le_succ n)) =
        powerQuotientMap A (Nat.le_succ n) ≫ α.hom := by
  let P : ObjectProperty (ModuleCat.{u} A) := fun M => IsFiniteLength A M
  let Qn := powerQuotient A n
  let Qs := powerQuotient A (n + 1)
  let q : Qs ⟶ Qn := powerQuotientMap A (Nat.le_succ n)
  obtain ⟨β₀⟩ := power_quotient_iso_exists A F (n + 1)
  let t : Qs ⟶ Qn := β₀.hom ≫ F.functor.map q ≫ α.inv
  obtain ⟨r, hr⟩ := hom_quotient_smul A
    (IsLocalRing.maximalIdeal A ^ (n + 1 + 1))
    (IsLocalRing.maximalIdeal A ^ (n + 1))
    (Ideal.pow_le_pow_right (Nat.add_le_add_right (Nat.le_succ n) 1)) t.hom
  have ht : t = r • q := P.hom_ext hr
  have ht_surj : Function.Surjective t.hom.hom := by
    have hβ : Function.Surjective β₀.hom.hom.hom :=
      (ModuleCat.epi_iff_surjective β₀.hom.hom).mp inferInstance
    have hα : Function.Surjective α.inv.hom.hom :=
      (ModuleCat.epi_iff_surjective α.inv.hom).mp inferInstance
    exact hα.comp ((image_power_quotient_map_surjective A F n).comp hβ)
  have hunit : IsUnit r := by
    apply unit_of_surjective_smul_quotient_map A
      (IsLocalRing.maximalIdeal A ^ (n + 1 + 1))
      (IsLocalRing.maximalIdeal A ^ (n + 1))
      (Ideal.pow_le_pow_right (Nat.add_le_add_right (Nat.le_succ n) 1))
      (Ideal.pow_le_self (Nat.succ_ne_zero n)) r
    change Function.Surjective (r • q).hom.hom
    rw [← ht]
    exact ht_surj
  let v : Aˣ := hunit.unit
  let s : Qs ≅ Qs :=
    P.isoMk (LinearEquiv.smulOfUnit (v⁻¹) : Qs.obj ≃ₗ[A] Qs.obj).toModuleIso
  let β := s ≪≫ β₀
  have hs : s.hom = ((v⁻¹ : Aˣ) : A) • (𝟙 Qs) := by
    apply P.hom_ext
    apply ModuleCat.hom_ext
    ext
    rfl
  refine ⟨β, (cancel_mono α.inv).mp ?_⟩
  calc
    (β.hom ≫ F.functor.map q) ≫ α.inv =
        s.hom ≫ t := by simp [β, t, Category.assoc]
    _ = q := by
      rw [hs, ht]
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
      have hv : (v : A) = r := hunit.unit_spec
      rw [← hv]
      simp
    _ = (q ≫ α.hom) ≫ α.inv := by simp

private noncomputable def powerIsoSequence
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (F : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M) ≌
      ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    [F.functor.Linear A] (n : ℕ) :
    powerQuotient A n ≅ F.functor.obj (powerQuotient A n) :=
  Nat.rec (Classical.choice (power_quotient_iso_exists A F 0))
    (fun n α => Classical.choose (power_quotient_iso_next A F n α)) n

private lemma powerIsoSequence_comm_succ
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (F : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M) ≌
      ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    [F.functor.Linear A] (n : ℕ) :
    (powerIsoSequence A F (n + 1)).hom ≫
        F.functor.map (powerQuotientMap A (Nat.le_succ n)) =
      powerQuotientMap A (Nat.le_succ n) ≫ (powerIsoSequence A F n).hom :=
  Classical.choose_spec
    (power_quotient_iso_next A F n (powerIsoSequence A F n))

private lemma powerQuotientMap_comp
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    powerQuotientMap A hnk ≫ powerQuotientMap A hmn =
      powerQuotientMap A (hmn.trans hnk) := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext
  rfl

private lemma powerQuotientMap_refl
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (n : ℕ) : powerQuotientMap A (le_refl n) = 𝟙 (powerQuotient A n) := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext
  rfl

private lemma powerIsoSequence_comm
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (F : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M) ≌
      ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    [F.functor.Linear A] {m n : ℕ} (h : m ≤ n) :
    (powerIsoSequence A F n).hom ≫ F.functor.map (powerQuotientMap A h) =
      powerQuotientMap A h ≫ (powerIsoSequence A F m).hom := by
  induction n, h using Nat.le_induction with
  | base =>
      rw [powerQuotientMap_refl]
      simp
  | succ n h ih =>
      rw [← powerQuotientMap_comp A h (Nat.le_succ n), F.functor.map_comp,
        reassoc_of% powerIsoSequence_comm_succ A F n, ih, Category.assoc]

private def powerEvalOne
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (n : ℕ)
    (X : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M)) :
    (powerQuotient A n ⟶ X) →ₗ[A] X.obj where
  toFun f := f.hom.hom (1 : A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def powerHomEquiv
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (n : ℕ)
    (X : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    (hAnn : IsLocalRing.maximalIdeal A ^ (n + 1) ≤ Module.annihilator A X.obj) :
    X.obj ≃ₗ[A] (powerQuotient A n ⟶ X) := by
  let I : Ideal A := IsLocalRing.maximalIdeal A ^ (n + 1)
  let ev := powerEvalOne A n X
  have hinj : Function.Injective ev := by
    intro f g hfg
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [quotient_mk_eq_smul_one]
    change (f.hom.hom : (A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1)) →ₗ[A] X.obj)
        (a • 1) =
      (g.hom.hom : (A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1)) →ₗ[A] X.obj) (a • 1)
    rw [map_smul, map_smul]
    exact congrArg (a • ·) hfg
  have hsurj : Function.Surjective ev := by
    intro x
    let t : A →ₗ[A] X.obj := LinearMap.toSpanSingleton A X.obj x
    have hle : (I : Submodule A A) ≤ LinearMap.ker t := by
      intro r hr
      change r • x = 0
      exact (Module.mem_annihilator.mp (hAnn hr)) x
    let l : (A ⧸ I) →ₗ[A] X.obj := I.liftQ t hle
    refine ⟨ObjectProperty.homMk (ModuleCat.ofHom l), ?_⟩
    change l (Ideal.Quotient.mk I 1) = x
    change t (1 : A) = x
    simp [t]
  exact (LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩).symm

private noncomputable def functorMapHomEquiv
    (A : Type u) [CommRing A]
    (F : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M) ≌
      ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    [F.functor.Linear A]
    (X Y : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M)) :
    (X ⟶ Y) ≃ₗ[A] (F.functor.obj X ⟶ F.functor.obj Y) := by
  let _ : F.functor.Additive := finiteLength_linear_equivalence_additive A F
  exact LinearEquiv.ofBijective (F.functor.mapLinearMap A)
    ⟨F.functor.map_injective, F.functor.map_surjective⟩

private noncomputable def powerComparison
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (F : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M) ≌
      ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    [F.functor.Linear A] (n : ℕ)
    (X : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    (hAnn : IsLocalRing.maximalIdeal A ^ (n + 1) ≤ Module.annihilator A X.obj) :
    X.obj ≃ₗ[A] (F.functor.obj X).obj := by
  have hFX : IsLocalRing.maximalIdeal A ^ (n + 1) ≤
      Module.annihilator A (F.functor.obj X).obj := by
    rwa [annihilator_image_eq A F X]
  exact ((powerHomEquiv A n X hAnn).trans
    (functorMapHomEquiv A F (powerQuotient A n) X)).trans
      ((CategoryTheory.Linear.homCongr A (powerIsoSequence A F n).symm
        (Iso.refl (F.functor.obj X))).trans
          (powerHomEquiv A n (F.functor.obj X) hFX).symm)

private lemma powerHomEquiv_symm_apply
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (n : ℕ)
    (X : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    (hAnn : IsLocalRing.maximalIdeal A ^ (n + 1) ≤ Module.annihilator A X.obj)
    (f : powerQuotient A n ⟶ X) :
    (powerHomEquiv A n X hAnn).symm f =
      f.hom.hom (1 : A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1)) := rfl

private lemma powerComparison_apply
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (F : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M) ≌
      ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    [F.functor.Linear A] (n : ℕ)
    (X : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    (hAnn : IsLocalRing.maximalIdeal A ^ (n + 1) ≤ Module.annihilator A X.obj)
    (x : X.obj) :
    powerComparison A F n X hAnn x =
      ((powerIsoSequence A F n).hom ≫
        F.functor.map (powerHomEquiv A n X hAnn x)).hom.hom
        (1 : A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1)) := rfl

private lemma powerHomEquiv_comp_factor
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {m n : ℕ} (h : m ≤ n)
    (X : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    (hm : IsLocalRing.maximalIdeal A ^ (m + 1) ≤ Module.annihilator A X.obj)
    (hn : IsLocalRing.maximalIdeal A ^ (n + 1) ≤ Module.annihilator A X.obj)
    (x : X.obj) :
    powerQuotientMap A h ≫ powerHomEquiv A m X hm x =
      powerHomEquiv A n X hn x := by
  apply (powerHomEquiv A n X hn).symm.injective
  simp only [LinearEquiv.symm_apply_apply]
  change (ModuleCat.Hom.hom ((powerHomEquiv A m X hm) x).hom)
    (1 : A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) = x
  rw [← powerHomEquiv_symm_apply A m X hm ((powerHomEquiv A m X hm) x)]
  simp

private lemma powerComparison_of_le
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (F : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M) ≌
      ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    [F.functor.Linear A] {m n : ℕ} (h : m ≤ n)
    (X : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    (hm : IsLocalRing.maximalIdeal A ^ (m + 1) ≤ Module.annihilator A X.obj)
    (hn : IsLocalRing.maximalIdeal A ^ (n + 1) ≤ Module.annihilator A X.obj) :
    powerComparison A F m X hm = powerComparison A F n X hn := by
  apply LinearEquiv.ext
  intro x
  rw [powerComparison_apply, powerComparison_apply,
    ← powerHomEquiv_comp_factor A h X hm hn x, F.functor.map_comp, ← Category.assoc,
    powerIsoSequence_comm A F h]
  simp [Category.assoc, powerQuotientMap]

private lemma powerHomEquiv_natural
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (n : ℕ)
    {X Y : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M)}
    (hX : IsLocalRing.maximalIdeal A ^ (n + 1) ≤ Module.annihilator A X.obj)
    (hY : IsLocalRing.maximalIdeal A ^ (n + 1) ≤ Module.annihilator A Y.obj)
    (f : X ⟶ Y) (x : X.obj) :
    powerHomEquiv A n Y hY (f.hom.hom x) =
      powerHomEquiv A n X hX x ≫ f := by
  apply (powerHomEquiv A n Y hY).symm.injective
  change (powerHomEquiv A n Y hY).symm
      ((powerHomEquiv A n Y hY) (f.hom.hom x)) =
    f.hom.hom ((powerHomEquiv A n X hX).symm
      ((powerHomEquiv A n X hX) x))
  simp

private lemma powerComparison_natural
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (F : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M) ≌
      ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    [F.functor.Linear A] (n : ℕ)
    {X Y : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M)}
    (hX : IsLocalRing.maximalIdeal A ^ (n + 1) ≤ Module.annihilator A X.obj)
    (hY : IsLocalRing.maximalIdeal A ^ (n + 1) ≤ Module.annihilator A Y.obj)
    (f : X ⟶ Y) (x : X.obj) :
    powerComparison A F n Y hY (f.hom.hom x) =
      (F.functor.map f).hom.hom (powerComparison A F n X hX x) := by
  rw [powerComparison_apply, powerComparison_apply,
    powerHomEquiv_natural A n hX hY f x, F.functor.map_comp]
  rfl

private noncomputable def annihilatorPowerIndex
    (A : Type u) [CommRing A] [IsLocalRing A]
    (X : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M)) : ℕ :=
  Classical.choose (finite_length_annihilated_by_power A X.obj X.property)

private lemma annihilatorPowerIndex_spec
    (A : Type u) [CommRing A] [IsLocalRing A]
    (X : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M)) :
    IsLocalRing.maximalIdeal A ^ (annihilatorPowerIndex A X + 1) ≤
      Module.annihilator A X.obj :=
  (Ideal.pow_le_pow_right (Nat.le_succ (annihilatorPowerIndex A X))).trans
    (Classical.choose_spec (finite_length_annihilated_by_power A X.obj X.property))

private noncomputable def comparisonIso
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (F : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M) ≌
      ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    [F.functor.Linear A]
    (X : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M)) :
    X ≅ F.functor.obj X :=
  ObjectProperty.isoMk
    ((fun M : ModuleCat.{u} A => IsFiniteLength A M) :
      ObjectProperty (ModuleCat.{u} A))
    (powerComparison A F (annihilatorPowerIndex A X) X
      (annihilatorPowerIndex_spec A X)).toModuleIso

private lemma comparisonIso_natural
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (F : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M) ≌
      ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    [F.functor.Linear A]
    {X Y : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M)} (f : X ⟶ Y) :
    f ≫ (comparisonIso A F Y).hom =
      (comparisonIso A F X).hom ≫ F.functor.map f := by
  let n := max (annihilatorPowerIndex A X) (annihilatorPowerIndex A Y)
  have hX : IsLocalRing.maximalIdeal A ^ (n + 1) ≤ Module.annihilator A X.obj :=
    (Ideal.pow_le_pow_right
      (Nat.add_le_add_right (Nat.le_max_left _ _) 1)).trans
      (annihilatorPowerIndex_spec A X)
  have hY : IsLocalRing.maximalIdeal A ^ (n + 1) ≤ Module.annihilator A Y.obj :=
    (Ideal.pow_le_pow_right
      (Nat.add_le_add_right (Nat.le_max_right _ _) 1)).trans
      (annihilatorPowerIndex_spec A Y)
  have hCX := powerComparison_of_le A F (Nat.le_max_left _ _) X
    (annihilatorPowerIndex_spec A X) hX
  have hCY := powerComparison_of_le A F (Nat.le_max_right _ _) Y
    (annihilatorPowerIndex_spec A Y) hY
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext x
  simp only [ObjectProperty.FullSubcategory.comp_hom, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  change powerComparison A F (annihilatorPowerIndex A Y) Y
      (annihilatorPowerIndex_spec A Y) (f.hom.hom x) =
    (F.functor.map f).hom.hom
      (powerComparison A F (annihilatorPowerIndex A X) X
        (annihilatorPowerIndex_spec A X) x)
  rw [congrArg (fun e : Y.obj ≃ₗ[A] (F.functor.obj Y).obj => e (f.hom.hom x)) hCY,
    congrArg (fun e : X.obj ≃ₗ[A] (F.functor.obj X).obj => e x) hCX]
  exact powerComparison_natural A F n hX hY f x

/-- Every linear self-equivalence of finite-length modules over a Noetherian local ring is
naturally isomorphic to the identity functor. -/
@[stacks 0A7P]
theorem linearEquivalenceFiniteLengthIsoIdentity
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (F : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M) ≌
      ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} A => IsFiniteLength A M))
    [F.functor.Linear A] :
    Nonempty (F.functor ≅ 𝟭 (ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{u} A => IsFiniteLength A M))) :=
  ⟨(NatIso.ofComponents (comparisonIso A F) (fun f => by
    simpa using comparisonIso_natural A F f)).symm⟩

end FiniteLengthAutoequivalence

end Dualizing
