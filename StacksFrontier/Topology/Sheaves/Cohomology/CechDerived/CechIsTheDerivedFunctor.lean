module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Effaceable
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness

/-!
# Čech cohomology as a derived functor

For an open covering of an open `U` of a ringed space, Čech cohomology of presheaves of
modules, in all degrees at once, is a cohomological δ-functor with values in modules over the
ring of sections on `U`, and degree-zero Čech cohomology is left exact. The assertion of
Stacks 01EN is that this δ-functor is the right-derived δ-functor of its degree-zero part,
normalized by `Functor.toRightDerivedZero`.

The argument is the one of Stacks 010T: both δ-functors are universal, the Čech one because
its higher terms are effaceable, the right-derived one because higher right derived functors
vanish on injectives; universal δ-functors with the same degree-zero part are uniquely
isomorphic (Stacks 010U). The two universality statements are proved here. The effaceability
input — vanishing of the higher Čech cohomology of an *injective presheaf* of modules, which is
the content of Stacks 01EL and 01EM — is carried as a hypothesis, as is the existence of a
δ-functor realizing the right derived functors.

## Main definitions

* `deltaFunctor` is the cohomological δ-functor `Hⁿ(E(-))` of an additive functor `E` into
  cochain complexes that carries short exact sequences to short exact sequences.
* `cechComplexFunctor` is the Čech cochain complex functor on presheaves of modules, built
  from the Čech cosimplicial object `cechCosimplicial` whose degree-`n` term is the Čech
  cochain functor `cechObj` of Stacks 01EJ; `cechCohomologyFunctor` is its cohomology and
  `cechDeltaFunctor` the resulting δ-functor.

## Main results

* `preservesFiniteLimits_functor_zero`: the degree-zero part of a δ-functor is left exact;
  `isoRightDerivedZero` and `cechIsoRightDerivedZero` are the resulting degree-zero
  comparisons with the zeroth right derived functor.
* `deltaFunctor_isUniversal` and `cechDeltaFunctor_isUniversal`: effaceability from the
  vanishing of the higher cohomology on injectives, hence universality.
* `isUniversal_of_functor_eq_rightDerived`: a δ-functor whose components are the right derived
  functors of its degree-zero part is universal.
* `deltaIsoRightDerived` and `cechDeltaIsoRightDerived`: the canonical comparison of the two
  δ-functors, the identity in degree zero, given the effaceability input and a δ-functor
  realizing the right derived functors.

## Implementation notes

The Čech complex is assembled as the alternating coface map complex of a cosimplicial object
in the category of functors, so that the vanishing of the square of the differential is
Mathlib's, and so that the degree-`n` term is *definitionally* the Čech cochain functor of
Stacks 01EJ (`cechComplexFunctor_comp_eval`); exactness is therefore exactly the degreewise
exactness proved there. The module universe is the one fixed by that construction; the
abbreviation `Modules` records it.

Mathlib has no long exact sequence for `Functor.rightDerived`: there is no horseshoe lemma for
injective resolutions, and `Functor.rightDerivedFunctorPlus` is not yet known to be
triangulated. The δ-functor structure on the right derived functors is therefore an argument
of `deltaIsoRightDerived` rather than a construction here.

## References

* [Stacks Project, Tag 01EN](https://stacks.math.columbia.edu/tag/01EN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace

universe v₁ v₂ u₁ u₂

namespace Stacks.Cohomology.CechDerived

section Abstract

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- A monomorphism of cochain complexes indexed by `ℕ` is a monomorphism on degree-zero
homology, because in degree zero there is no incoming differential and homology is the
object of cycles. -/
theorem mono_homologyMap_zero {K L : CochainComplex B ℕ} (f : K ⟶ L) (hf : Mono (f.f 0)) :
    Mono (HomologicalComplex.homologyMap f 0) := by
  have hcyc : Mono (HomologicalComplex.cyclesMap f 0 ≫ L.iCycles 0) := by
    rw [HomologicalComplex.cyclesMap_i]
    exact mono_comp _ _
  have : Mono (HomologicalComplex.cyclesMap f 0) := mono_of_mono _ (L.iCycles 0)
  have hmono : Mono (K.isoHomologyπ₀.inv ≫ HomologicalComplex.cyclesMap f 0) := mono_comp _ _
  rw [← CochainComplex.isoHomologyπ₀_inv_naturality f] at hmono
  exact mono_of_mono _ L.isoHomologyπ₀.inv

variable (E : A ⥤ CochainComplex B ℕ) [E.Additive]
  (hE : ∀ S : ShortComplex A, S.ShortExact → (S.map E).ShortExact)

include hE

/-- The degreewise form of the exactness hypothesis on `E`: a short exact sequence of `A` is
sent to a sequence of cochain complexes that is short exact in every degree. -/
theorem shortExact_eval {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (S.map (E ⋙ HomologicalComplex.eval B (up ℕ) n)).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 (hE S hS) n

/-- **The cohomological δ-functor of an exact complex-valued functor.** If `E` carries objects
of `A` to cochain complexes of `B` and short exact sequences to short exact sequences of
complexes, then the cohomology objects `Hⁿ(E(-))` form a cohomological δ-functor, the
connecting morphisms being those of the long exact homology sequence. For the Čech complex
functor this is the δ-functor structure on Čech cohomology. -/
def deltaFunctor : DeltaFunctor A B where
  functor n := E ⋙ HomologicalComplex.homologyFunctor B (up ℕ) n
  δ hS n := (hE _ hS).δ n (n + 1) rfl
  map_g_δ hS n := (hE _ hS).comp_δ n (n + 1) rfl
  δ_map_f hS n := (hE _ hS).δ_comp n (n + 1) rfl
  mono_map_f hS := mono_homologyMap_zero _ (shortExact_eval E hE hS 0).mono_f
  exact_map hS n := (hE _ hS).homology_exact₂ n
  exact_δ₁ hS n := (hE _ hS).homology_exact₃ n (n + 1) rfl
  exact_δ₂ hS n := (hE _ hS).homology_exact₁ n (n + 1) rfl
  δ_naturality hS hT φ n := (HomologicalComplex.HomologySequence.δ_naturality
    (E.mapShortComplex.map φ) (hE _ hS) (hE _ hT) n (n + 1) rfl).symm

/-- The component functors of `deltaFunctor` are the cohomology functors of `E`. -/
theorem deltaFunctor_functor (n : ℕ) :
    (deltaFunctor E hE).functor n = E ⋙ HomologicalComplex.homologyFunctor B (up ℕ) n :=
  rfl

/-- The connecting morphisms of `deltaFunctor` are those of the long exact homology sequence
of the short exact sequence of complexes obtained from `E`. -/
theorem deltaFunctor_δ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (deltaFunctor E hE).δ hS n = (hE S hS).δ n (n + 1) rfl :=
  rfl

/-- **Effaceability of the cohomology δ-functor.** If the higher cohomology of `E(I)` vanishes
for every injective `I`, then the δ-functor `Hⁿ(E(-))` is universal: by Stacks 010T every
natural transformation out of `H⁰(E(-))` extends uniquely to the higher degrees. -/
theorem deltaFunctor_isUniversal [EnoughInjectives A]
    (hinj : ∀ (n : ℕ) (I : A), Injective I → IsZero ((E.obj I).homology (n + 1))) :
    (deltaFunctor E hE).IsUniversal :=
  DeltaFunctor.isUniversal_of_isZero_injective _ fun n I _ ↦ hinj n I ‹_›

omit hE

/-- The degree-zero functor of a cohomological δ-functor is left exact: the long exact sequence
makes `0 → F⁰(X₁) → F⁰(X₂) → F⁰(X₃)` exact for every short exact sequence, and for an additive
functor between abelian categories this is equivalent to preserving finite limits. -/
theorem preservesFiniteLimits_functor_zero (F : DeltaFunctor A B) :
    PreservesFiniteLimits (F.functor 0) :=
  (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).2
    fun _ hS ↦ ⟨F.exact_map hS 0, F.mono_map_f hS⟩

/-- **The degree-zero comparison.** The degree-zero functor of a cohomological δ-functor is
canonically its own zeroth right derived functor, the comparison being
`Functor.toRightDerivedZero`. This is left exactness of `F⁰` together with Mathlib's
`Functor.rightDerivedZeroIsoSelf`. -/
def isoRightDerivedZero [EnoughInjectives A] (F : DeltaFunctor A B) :
    (F.functor 0).rightDerived 0 ≅ F.functor 0 :=
  letI := preservesFiniteLimits_functor_zero F
  Functor.rightDerivedZeroIsoSelf _

/-- The degree-zero comparison is inverse to `Functor.toRightDerivedZero`. -/
theorem toRightDerivedZero_comp_isoRightDerivedZero [EnoughInjectives A] (F : DeltaFunctor A B) :
    (F.functor 0).toRightDerivedZero ≫ (isoRightDerivedZero F).hom = 𝟙 _ :=
  let _ := preservesFiniteLimits_functor_zero F
  Functor.rightDerivedZeroIsoSelf_inv_hom_id _

/-- **A δ-functor realizing the right derived functors is universal.** The higher right derived
functors vanish on injective objects, so Stacks 010T applies. This is the second half of the
uniqueness argument of Stacks 01EN. -/
theorem isUniversal_of_functor_eq_rightDerived [EnoughInjectives A] (G : DeltaFunctor A B)
    (hG : ∀ n, G.functor n = (G.functor 0).rightDerived n) : G.IsUniversal :=
  DeltaFunctor.isUniversal_of_isZero_injective G fun n I _ ↦ by
    rw [hG (n + 1)]
    exact Functor.isZero_rightDerived_obj_injective_succ _ n I

include hE

/-- **The canonical comparison of the cohomology δ-functor with the right-derived δ-functor.**
Assume the higher cohomology of `E` vanishes on injectives, and let `G` be a δ-functor whose
degree-zero part is `H⁰(E(-))` and whose components are the right derived functors of that
degree-zero part. Then `Hⁿ(E(-))` and `G` are isomorphic as δ-functors. Both are universal, so
the isomorphism extending the identity in degree zero exists and is unique; see
`deltaIsoRightDerived_app_zero` and `DeltaFunctor.IsUniversal.iso_ext`. -/
def deltaIsoRightDerived [EnoughInjectives A]
    (hinj : ∀ (n : ℕ) (I : A), Injective I → IsZero ((E.obj I).homology (n + 1)))
    (G : DeltaFunctor A B) (hG0 : G.functor 0 = (deltaFunctor E hE).functor 0)
    (hG : ∀ n, G.functor n = (G.functor 0).rightDerived n) :
    deltaFunctor E hE ≅ G :=
  letI := deltaFunctor_isUniversal E hE hinj
  letI := isUniversal_of_functor_eq_rightDerived G hG
  DeltaFunctor.IsUniversal.isoOfIso (eqToIso hG0.symm)

/-- The comparison of `deltaIsoRightDerived` is the identity in degree zero. -/
theorem deltaIsoRightDerived_app_zero [EnoughInjectives A]
    (hinj : ∀ (n : ℕ) (I : A), Injective I → IsZero ((E.obj I).homology (n + 1)))
    (G : DeltaFunctor A B) (hG0 : G.functor 0 = (deltaFunctor E hE).functor 0)
    (hG : ∀ n, G.functor n = (G.functor 0).rightDerived n) :
    (deltaIsoRightDerived E hE hinj G hG0 hG).hom.app 0 = eqToHom hG0.symm :=
  let _ := deltaFunctor_isUniversal E hE hinj
  let _ := isUniversal_of_functor_eq_rightDerived G hG
  DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero (eqToIso hG0.symm)

end Abstract

/-- The alternating coface map complex functor is additive: a natural transformation of
cosimplicial objects acts on the associated cochain complexes degree by degree. -/
instance alternatingCofaceMapComplex_additive (C : Type u₁) [Category.{v₁} C] [Preadditive C] :
    (AlgebraicTopology.alternatingCofaceMapComplex C).Additive where
  map_add {_ _ _ _} := by
    apply HomologicalComplex.hom_ext
    intro n
    rfl

section Cech

variable {Y : TopCat} (R : (Opens Y)ᵒᵖ ⥤ RingCat) (𝒰 : CechOpenCover Y)

/-- Presheaves of `R`-modules. The module universe is the one fixed by the Čech cochain
functor of Tag 01EJ, namely `Type 0`; this abbreviation records that choice so that the
statements below are about the same category as the Čech construction. -/
abbrev Modules := PresheafOfModules.{0} R

/-- Modules over the ring of sections on the covered open, the target of Čech cohomology. -/
abbrev SectionModules := ModuleCat.{0} (R.obj (op 𝒰.U))

/-- The sections over an open `V` contained in the covered open `U`, as a functor from
presheaves of `R`-modules to modules over the ring `R(U)` of sections on `U`. The `R(U)`-module
structure is obtained by restricting scalars along the restriction map `R(U) → R(V)`. -/
def sectionsFunctor (V : Opens Y) (hV : V ≤ 𝒰.U) :
    PresheafOfModules R ⥤ ModuleCat (R.obj (op 𝒰.U)) :=
  PresheafOfModules.evaluation R (op V) ⋙
    ModuleCat.restrictScalars (R.map (homOfLE hV).op).hom

/-- The Čech factor indexed by a tuple is the sections over the corresponding intersection. -/
theorem cechTermFunctor_eq (p : ℕ) (σ : Fin (p + 1) → 𝒰.ι) :
    cechTermFunctor R 𝒰 p σ = sectionsFunctor R 𝒰 (cechInter 𝒰 p σ) (cechInter_le_U 𝒰 p σ) :=
  rfl

/-- The restriction map of a presheaf of modules is `R(U)`-linear for the module structures
obtained by restricting scalars along the two restriction maps out of `R(U)`. -/
theorem map_res_smul (M : PresheafOfModules R) {V W : Opens Y} (hV : V ≤ 𝒰.U) (hW : W ≤ 𝒰.U)
    (h : W ≤ V) (r : R.obj (op 𝒰.U)) (x : M.obj (op V)) :
    M.map (homOfLE h).op ((R.map (homOfLE hV).op).hom r • x)
      = (R.map (homOfLE hW).op).hom r • M.map (homOfLE h).op x := by
  have hc : (R.map (homOfLE hW).op).hom r
      = (R.map (homOfLE h).op).hom ((R.map (homOfLE hV).op).hom r) := by
    rw [show (homOfLE hW).op = (homOfLE hV).op ≫ (homOfLE h).op from rfl, R.map_comp]
    rfl
  rw [hc]
  exact PresheafOfModules.map_smul M (homOfLE h).op _ x

/-- The restriction map on sections over `V ⊇ W`, as a morphism of `R(U)`-modules. -/
def sectionsResApp {V W : Opens Y} (hV : V ≤ 𝒰.U) (hW : W ≤ 𝒰.U) (h : W ≤ V)
    (M : PresheafOfModules R) :
    (sectionsFunctor R 𝒰 V hV).obj M ⟶ (sectionsFunctor R 𝒰 W hW).obj M :=
  ConcreteCategory.ofHom
    { toFun := (M.map (homOfLE h).op).hom
      map_add' := fun x y ↦ map_add _ x y
      map_smul' := fun r x ↦ map_res_smul R 𝒰 M hV hW h r x }

/-- `sectionsResApp` is the restriction map of the presheaf of modules. -/
@[simp]
theorem sectionsResApp_hom_apply {V W : Opens Y} (hV : V ≤ 𝒰.U) (hW : W ≤ 𝒰.U) (h : W ≤ V)
    (M : PresheafOfModules R) (x : (sectionsFunctor R 𝒰 V hV).obj M) :
    (sectionsResApp R 𝒰 hV hW h M).hom x = M.map (homOfLE h).op x :=
  rfl

/-- The restriction natural transformation on the sections functors, for `W ≤ V ≤ U`. -/
def sectionsRes {V W : Opens Y} (hV : V ≤ 𝒰.U) (hW : W ≤ 𝒰.U) (h : W ≤ V) :
    sectionsFunctor R 𝒰 V hV ⟶ sectionsFunctor R 𝒰 W hW where
  app M := sectionsResApp R 𝒰 hV hW h M
  naturality M N φ := by
    ext x
    exact (PresheafOfModules.naturality_apply φ (homOfLE h).op x).symm

/-- Restriction along the identity inclusion is the identity. -/
theorem sectionsRes_refl {V : Opens Y} (hV hV' : V ≤ 𝒰.U) :
    sectionsRes R 𝒰 hV hV' le_rfl = 𝟙 _ := by
  ext M x
  show M.map (𝟙 (op V)) x = x
  rw [M.map_id]
  rfl

/-- Restriction along a composite of inclusions is the composite of the restrictions. -/
theorem sectionsRes_comp {V W Z : Opens Y} (hV : V ≤ 𝒰.U) (hW : W ≤ 𝒰.U) (hZ : Z ≤ 𝒰.U)
    (h : W ≤ V) (h' : Z ≤ W) :
    sectionsRes R 𝒰 hV hW h ≫ sectionsRes R 𝒰 hW hZ h' =
      sectionsRes R 𝒰 hV hZ (h'.trans h) := by
  ext M x
  exact (PresheafOfModules.map_comp_apply M (homOfLE h).op (homOfLE h').op x).symm

/-- Reindexing a tuple along `f` enlarges the corresponding intersection. -/
theorem cechInter_le_comp {m n : ℕ} (τ : Fin (n + 1) → 𝒰.ι) (f : Fin (m + 1) → Fin (n + 1)) :
    cechInter 𝒰 n τ ≤ cechInter 𝒰 m (τ ∘ f) :=
  le_iInf fun j ↦ iInf_le (fun k ↦ 𝒰.obj (τ k)) (f j)

/-- The restriction from the Čech factor indexed by `τ ∘ f` to the one indexed by `τ`. -/
def cechTermRes {m n : ℕ} (τ : Fin (n + 1) → 𝒰.ι) (f : Fin (m + 1) → Fin (n + 1)) :
    cechTermFunctor R 𝒰 m (τ ∘ f) ⟶ cechTermFunctor R 𝒰 n τ :=
  sectionsRes R 𝒰 (cechInter_le_U 𝒰 m (τ ∘ f)) (cechInter_le_U 𝒰 n τ)
    (cechInter_le_comp 𝒰 τ f)

/-- Reindexing along the identity does nothing. -/
theorem cechTermRes_id {n : ℕ} (τ : Fin (n + 1) → 𝒰.ι) : cechTermRes R 𝒰 τ id = 𝟙 _ :=
  sectionsRes_refl R 𝒰 _ _

/-- Reindexing along a composite is the composite of the reindexings. -/
theorem cechTermRes_comp {l m n : ℕ} (τ : Fin (n + 1) → 𝒰.ι) (f : Fin (m + 1) → Fin (n + 1))
    (g : Fin (l + 1) → Fin (m + 1)) :
    cechTermRes R 𝒰 (τ ∘ f) g ≫ cechTermRes R 𝒰 τ f = cechTermRes R 𝒰 τ (f ∘ g) :=
  sectionsRes_comp R 𝒰 _ _ _ _ _

/-- The projection of the degree-`p` Čech cochains onto the factor indexed by the tuple `σ`. -/
def cechπ (p : ℕ) (σ : Fin (p + 1) → 𝒰.ι) : cechObj R 𝒰 p ⟶ cechTermFunctor R 𝒰 p σ :=
  Pi.π _ σ

/-- Two morphisms into the degree-`p` Čech cochains agree as soon as all their components
agree. -/
theorem cech_hom_ext {p : ℕ} {W : PresheafOfModules R ⥤ ModuleCat (R.obj (op 𝒰.U))}
    {α β : W ⟶ cechObj R 𝒰 p} (h : ∀ σ, α ≫ cechπ R 𝒰 p σ = β ≫ cechπ R 𝒰 p σ) : α = β :=
  Pi.hom_ext _ _ h

/-- Reindexing Čech cochains along a map of index tuples: the component at `τ` is the
restriction of the component at `τ ∘ f`. -/
def cechMap {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) : cechObj R 𝒰 m ⟶ cechObj R 𝒰 n :=
  Pi.lift fun τ ↦ cechπ R 𝒰 m (τ ∘ f) ≫ cechTermRes R 𝒰 τ f

/-- The components of `cechMap`. -/
@[reassoc]
theorem cechMap_comp_π {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (τ : Fin (n + 1) → 𝒰.ι) :
    cechMap R 𝒰 f ≫ cechπ R 𝒰 n τ = cechπ R 𝒰 m (τ ∘ f) ≫ cechTermRes R 𝒰 τ f :=
  Pi.lift_π _ _

/-- Reindexing along the identity is the identity. -/
theorem cechMap_id (n : ℕ) : cechMap R 𝒰 (id : Fin (n + 1) → Fin (n + 1)) = 𝟙 _ := by
  refine cech_hom_ext R 𝒰 fun τ ↦ ?_
  rw [cechMap_comp_π, cechTermRes_id, Category.comp_id, Category.id_comp]
  rfl

/-- Reindexing along a composite is the composite of the reindexings. -/
theorem cechMap_comp {l m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (g : Fin (l + 1) → Fin (m + 1)) :
    cechMap R 𝒰 (f ∘ g) = cechMap R 𝒰 g ≫ cechMap R 𝒰 f := by
  refine cech_hom_ext R 𝒰 fun τ ↦ ?_
  rw [cechMap_comp_π, Category.assoc, cechMap_comp_π, cechMap_comp_π_assoc,
    cechTermRes_comp]
  rfl

/-- **The Čech cosimplicial object of cochain modules.** In degree `n` it is the product of
the sections over the `(n+1)`-fold intersections of the members of the covering, and a
morphism `f` of the simplex category acts by reindexing tuples along `f` and restricting. -/
def cechCosimplicial :
    CosimplicialObject (PresheafOfModules R ⥤ ModuleCat (R.obj (op 𝒰.U))) where
  obj n := cechObj R 𝒰 n.len
  map {_ _} f := cechMap R 𝒰 f.toOrderHom
  map_id n := cechMap_id R 𝒰 n.len
  map_comp {_ _ _} f g := cechMap_comp R 𝒰 g.toOrderHom f.toOrderHom

/-- **The Čech cochain complex functor on presheaves of modules.** It sends a presheaf of
`R`-modules to the Čech cochain complex of the covering, a cochain complex of modules over
the ring of sections on the covered open; the differential is the alternating sum of the
coface maps of `cechCosimplicial`. -/
def cechComplexFunctor :
    PresheafOfModules R ⥤ CochainComplex (ModuleCat (R.obj (op 𝒰.U))) ℕ :=
  (cechCosimplicial R 𝒰).flip ⋙
    AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat (R.obj (op 𝒰.U)))

/-- The degree-`p` term of the Čech complex is the degree-`p` Čech cochain functor of
Tag 01EJ. -/
theorem cechComplexFunctor_comp_eval (p : ℕ) :
    cechComplexFunctor R 𝒰 ⋙ HomologicalComplex.eval _ (up ℕ) p = cechObj R 𝒰 p :=
  rfl

/-- The Čech cochain modules depend additively on the presheaf of modules, degree by
degree. -/
instance cechCosimplicial_flip_additive : ((cechCosimplicial R 𝒰).flip).Additive where
  map_add {_ _ _ _} := NatTrans.ext (funext fun n ↦ (cechObj R 𝒰 n.len).map_add)

/-- The Čech cochain complex functor on presheaves of `R`-modules is additive. -/
instance cechComplexFunctor_additive : (cechComplexFunctor R 𝒰).Additive := by
  dsimp only [cechComplexFunctor]
  infer_instance

/-- **Exactness of the Čech complex functor, Stacks 01EJ.** A short exact sequence of
presheaves of `R`-modules is carried to a short exact sequence of Čech complexes, since this
holds in every degree. -/
theorem cechComplexFunctor_shortExact (S : ShortComplex (PresheafOfModules R))
    (hS : S.ShortExact) : (S.map (cechComplexFunctor R 𝒰)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p ↦
    cech_functor_exact R 𝒰 p S hS

/-- Čech cohomology of a presheaf of `R`-modules in degree `n`, with values in modules over
the ring of sections on the covered open. -/
def cechCohomologyFunctor (n : ℕ) :
    PresheafOfModules R ⥤ ModuleCat (R.obj (op 𝒰.U)) :=
  cechComplexFunctor R 𝒰 ⋙ HomologicalComplex.homologyFunctor _ (up ℕ) n

/-- Čech cohomology in each degree `n` is an additive functor of the presheaf of modules. -/
instance cechCohomologyFunctor_additive (n : ℕ) : (cechCohomologyFunctor R 𝒰 n).Additive := by
  dsimp only [cechCohomologyFunctor]
  infer_instance

/-- **The Čech cohomology δ-functor.** Čech cohomology of presheaves of `R`-modules, in all
degrees, together with the connecting morphisms of the long exact sequence attached to a short
exact sequence of presheaves. This is the δ-functor whose comparison with the right derived
functors of degree-zero Čech cohomology is the content of Stacks 01EN. -/
def cechDeltaFunctor : DeltaFunctor (PresheafOfModules R) (ModuleCat (R.obj (op 𝒰.U))) :=
  deltaFunctor (cechComplexFunctor R 𝒰) (cechComplexFunctor_shortExact R 𝒰)

/-- The components of the Čech δ-functor are the Čech cohomology functors. -/
theorem cechDeltaFunctor_functor (n : ℕ) :
    (cechDeltaFunctor R 𝒰).functor n = cechCohomologyFunctor R 𝒰 n :=
  rfl

/-- The connecting morphisms of the Čech δ-functor are those of the long exact homology
sequence of the short exact sequence of Čech complexes. -/
theorem cechDeltaFunctor_δ {S : ShortComplex (PresheafOfModules R)} (hS : S.ShortExact)
    (n : ℕ) :
    (cechDeltaFunctor R 𝒰).δ hS n =
      (cechComplexFunctor_shortExact R 𝒰 S hS).δ n (n + 1) rfl :=
  rfl

/-- **Degree-zero Čech cohomology is left exact.** -/
instance cechCohomologyFunctor_zero_preservesFiniteLimits :
    PreservesFiniteLimits (cechCohomologyFunctor R 𝒰 0) :=
  preservesFiniteLimits_functor_zero (cechDeltaFunctor R 𝒰)

/-- **The degree-zero comparison of Stacks 01EN.** Degree-zero Čech cohomology is canonically
its own zeroth right derived functor, the comparison being `Functor.toRightDerivedZero`. -/
def cechIsoRightDerivedZero [EnoughInjectives (Modules R)] :
    (cechCohomologyFunctor R 𝒰 0).rightDerived 0 ≅ cechCohomologyFunctor R 𝒰 0 :=
  isoRightDerivedZero (cechDeltaFunctor R 𝒰)

/-- The degree-zero comparison is inverse to `Functor.toRightDerivedZero`. -/
theorem cechIsoRightDerivedZero_fac [EnoughInjectives (Modules R)] :
    (cechCohomologyFunctor R 𝒰 0).toRightDerivedZero ≫ (cechIsoRightDerivedZero R 𝒰).hom = 𝟙 _ :=
  toRightDerivedZero_comp_isoRightDerivedZero (cechDeltaFunctor R 𝒰)

/-- **Universality of the Čech δ-functor from the acyclicity of injectives.** If the higher
Čech cohomology of every injective presheaf of `R`-modules vanishes, the Čech δ-functor is
universal, hence determined by degree-zero Čech cohomology. -/
theorem cechDeltaFunctor_isUniversal [EnoughInjectives (Modules R)]
    (hinj : ∀ (n : ℕ) (I : Modules R), Injective I →
      IsZero ((cechCohomologyFunctor R 𝒰 (n + 1)).obj I)) :
    (cechDeltaFunctor R 𝒰).IsUniversal :=
  deltaFunctor_isUniversal _ _ hinj

/-- **The Čech-to-derived δ-functor comparison.** Assume the higher Čech cohomology of
injective presheaves of `R`-modules vanishes, and let `G` be a δ-functor whose degree-zero part
is degree-zero Čech cohomology and whose components are the right derived functors of that
degree-zero part. Then the Čech δ-functor is isomorphic to `G`, by the unique isomorphism that
is the identity in degree zero. -/
def cechDeltaIsoRightDerived [EnoughInjectives (Modules R)]
    (hinj : ∀ (n : ℕ) (I : Modules R), Injective I →
      IsZero ((cechCohomologyFunctor R 𝒰 (n + 1)).obj I))
    (G : DeltaFunctor (Modules R) (SectionModules R 𝒰))
    (hG0 : G.functor 0 = cechCohomologyFunctor R 𝒰 0)
    (hG : ∀ n, G.functor n = (G.functor 0).rightDerived n) :
    cechDeltaFunctor R 𝒰 ≅ G :=
  deltaIsoRightDerived _ _ hinj G hG0 hG

/-- The Čech-to-derived comparison is the identity in degree zero. -/
theorem cechDeltaIsoRightDerived_app_zero [EnoughInjectives (Modules R)]
    (hinj : ∀ (n : ℕ) (I : Modules R), Injective I →
      IsZero ((cechCohomologyFunctor R 𝒰 (n + 1)).obj I))
    (G : DeltaFunctor (Modules R) (SectionModules R 𝒰))
    (hG0 : G.functor 0 = cechCohomologyFunctor R 𝒰 0)
    (hG : ∀ n, G.functor n = (G.functor 0).rightDerived n) :
    (cechDeltaIsoRightDerived R 𝒰 hinj G hG0 hG).hom.app 0 = eqToHom hG0.symm :=
  deltaIsoRightDerived_app_zero _ _ hinj G hG0 hG

end Cech

end Stacks.Cohomology.CechDerived

end
