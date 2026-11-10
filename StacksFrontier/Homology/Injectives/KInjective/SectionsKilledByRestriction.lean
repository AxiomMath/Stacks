module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Sections killed by restriction, and K-injective complexes

Let `j : A ⥤ A'` be a functor between abelian categories with a left adjoint `ℓ` and a right
adjoint `r`. Think of `j` as restriction to an open subspace `V`, of `ℓ` as extension by zero and
of `r` as direct image. The *sections killed by restriction* of `M` are
```
Γ M = ker(M ⟶ r(j M)),
```
the kernel of the unit of `j ⊣ r`; for sheaves on a space `Y` with `V ⊆ Y` open this is the
subsheaf of sections supported on the closed complement of `V`. This file proves the formal
properties of `Γ` that the proof of Stacks 0AEU uses to replace a K-injective complex `I`
supported on `Y ∖ V` by the complex `Γ I`.

## Main definitions

* `Stacks.Injectives.SectionsKilledByRestriction.sections`: the functor `Γ`, with its inclusion
  `Stacks.Injectives.SectionsKilledByRestriction.sectionsι : Γ ⟶ 𝟭 A`.
* `Stacks.Injectives.SectionsKilledByRestriction.cosupport`: the functor
  `M ↦ coker(ℓ(j M) ⟶ M)`, the cokernel of the counit of `ℓ ⊣ j`.
* `Stacks.Injectives.SectionsKilledByRestriction.adjunction`: the adjunction `cosupport ⊣ Γ`.

## Main results

* `Stacks.Injectives.SectionsKilledByRestriction.isKInjective_sections`: if `ℓ` is exact and the
  counit `ℓ(j M) ⟶ M` is a monomorphism for every `M`, then `Γ`, applied degreewise, carries
  K-injective complexes to K-injective complexes.
* `Stacks.Injectives.SectionsKilledByRestriction.quasiIso_sectionsι`: if moreover the
  K-injective complex `I` has injective terms and `j I` is acyclic, then `Γ I ⟶ I` is a
  quasi-isomorphism.

## Implementation notes

The functor `Γ` is defined objectwise as `kernel (adjR.unit.app M)` rather than as a kernel in
the functor category, so that its value at an object is definitionally a kernel in `A`.

The adjunction `cosupport ⊣ Γ` rests on the observation that for `g : M ⟶ N` the three
conditions `ℓ(j M) ⟶ M ⟶ N = 0`, `j g = 0` and `M ⟶ N ⟶ r(j N) = 0` are equivalent, each
of the two composites being the transpose of `j g` under one of the two adjunctions.

K-injectivity of `Γ I` is proved directly, not through the exactness of `cosupport`: a chain map
`K ⟶ Γ I` from an acyclic complex is the transpose of a chain map `cosupport K ⟶ I`, the complex
`cosupport K` is acyclic as the cokernel of the degreewise monomorphism `ℓ(j K) ⟶ K` between two
acyclic complexes, so that chain map is null-homotopic, and `Γ` carries the homotopy back.

For an injective object `N` the unit `N ⟶ r(j N)` is a split epimorphism when the counit of
`ℓ ⊣ j` at `r(j N)` is a monomorphism: the section is an extension of `ℓ(j r j N) ⟶ N` along that
monomorphism. So on a complex with injective terms `Γ I ⟶ I ⟶ r(j I)` is degreewise short exact,
and `r(j I)` is acyclic because `j I` is K-injective and acyclic, hence null-homotopic.

## References

* [Stacks Project, Tag 0AEU](https://stacks.math.columbia.edu/tag/0AEU)
* [Stacks Project, Tag 070G](https://stacks.math.columbia.edu/tag/070G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u v' u'

namespace Stacks.Injectives.SectionsKilledByRestriction

variable {A : Type u} [Category.{v} A] [Abelian A] {A' : Type u'} [Category.{v'} A'] [Abelian A']
  {j : A ⥤ A'} {ℓ r : A' ⥤ A} [j.Additive] [ℓ.Additive] [r.Additive]
  (adjL : ℓ ⊣ j) (adjR : j ⊣ r)

/-! ### The two functors and the adjunction -/

/-- The component `M ⟶ r(j M)` of the unit of `j ⊣ r`, with its source and target written
without the identity and composite functors. -/
def unitApp (M : A) : M ⟶ r.obj (j.obj M) := adjR.unit.app M

/-- The component `ℓ(j M) ⟶ M` of the counit of `ℓ ⊣ j`. -/
def counitApp (M : A) : ℓ.obj (j.obj M) ⟶ M := adjL.counit.app M

omit [Abelian A] [Abelian A'] [j.Additive] [ℓ.Additive] [r.Additive] in
/-- Naturality of the unit components `M ⟶ r(j M)`. -/
@[reassoc]
lemma unitApp_naturality {M N : A} (g : M ⟶ N) :
    g ≫ unitApp adjR N = unitApp adjR M ≫ r.map (j.map g) :=
  (adjR.unit_naturality g).symm

omit [Abelian A] [Abelian A'] [j.Additive] [ℓ.Additive] [r.Additive] in
/-- Naturality of the counit components `ℓ(j M) ⟶ M`. -/
@[reassoc]
lemma counitApp_naturality {M N : A} (g : M ⟶ N) :
    ℓ.map (j.map g) ≫ counitApp adjL N = counitApp adjL M ≫ g :=
  adjL.counit_naturality g

omit [ℓ.Additive] in
include adjL in
/-- The composite `ℓ(j M) ⟶ M ⟶ N` vanishes exactly when `j g` does. -/
lemma counit_comp_eq_zero_iff {M N : A} (g : M ⟶ N) :
    counitApp adjL M ≫ g = 0 ↔ j.map g = 0 := by
  rw [counitApp, ← (adjL.homEquiv _ _).apply_eq_iff_eq, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_unit]
  simp

omit [r.Additive] in
include adjR in
/-- The composite `M ⟶ N ⟶ r(j N)` vanishes exactly when `j g` does. -/
lemma comp_unit_eq_zero_iff {M N : A} (g : M ⟶ N) :
    g ≫ unitApp adjR N = 0 ↔ j.map g = 0 := by
  rw [unitApp, ← (adjR.homEquiv _ _).symm.apply_eq_iff_eq, Adjunction.homEquiv_counit,
    Adjunction.homEquiv_counit]
  simp

/-- The sections killed by restriction, `Γ M = ker(M ⟶ r(j M))`. -/
def sections : A ⥤ A where
  obj M := kernel (unitApp adjR M)
  map {M N} g := kernel.lift _ (kernel.ι _ ≫ g) <| by
    rw [Category.assoc, unitApp_naturality, kernel.condition_assoc, zero_comp]
  map_id M := (cancel_mono (kernel.ι _)).1 (by simp)
  map_comp f g := (cancel_mono (kernel.ι _)).1 (by simp)

/-- The inclusion `Γ M ⟶ M`. -/
def ι (M : A) : (sections adjR).obj M ⟶ M := kernel.ι (unitApp adjR M)

/-- The inclusion `Γ M ⟶ M` is a monomorphism. -/
instance (M : A) : Mono (ι adjR M) := inferInstanceAs (Mono (kernel.ι _))

omit [Abelian A'] [j.Additive] [r.Additive] in
/-- `Γ M ⟶ M ⟶ r(j M)` vanishes. -/
@[reassoc (attr := simp)]
lemma ι_unitApp (M : A) : ι adjR M ≫ unitApp adjR M = 0 := kernel.condition _

/-- `Γ M ⟶ M` is a kernel of `M ⟶ r(j M)`. -/
def ιIsKernel (M : A) : IsLimit (KernelFork.ofι (ι adjR M) (ι_unitApp adjR M)) :=
  kernelIsKernel _

/-- A morphism into `M` killed by restriction factors through `Γ M`. -/
def lift {W M : A} (k : W ⟶ M) (hk : k ≫ unitApp adjR M = 0) : W ⟶ (sections adjR).obj M :=
  kernel.lift _ k hk

omit [Abelian A'] [j.Additive] [r.Additive] in
/-- The factorisation through `Γ M`, followed by the inclusion, is the original map. -/
@[reassoc (attr := simp)]
lemma lift_ι {W M : A} (k : W ⟶ M) (hk : k ≫ unitApp adjR M = 0) :
    lift adjR k hk ≫ ι adjR M = k :=
  kernel.lift_ι _ _ _

omit [Abelian A'] [j.Additive] [r.Additive] in
/-- The inclusion `Γ ⟶ 𝟭` is natural. -/
@[reassoc (attr := simp)]
lemma map_ι {M N : A} (g : M ⟶ N) :
    (sections adjR).map g ≫ ι adjR N = ι adjR M ≫ g :=
  kernel.lift_ι _ _ _

omit [Abelian A'] [j.Additive] [r.Additive] in
/-- Maps into `Γ M` are determined by their composite with the inclusion. -/
lemma hom_ext_ι {W M : A} {a b : W ⟶ (sections adjR).obj M} (h : a ≫ ι adjR M = b ≫ ι adjR M) :
    a = b :=
  (cancel_mono (ι adjR M)).1 h

/-- The sections killed by restriction form an additive functor. -/
instance : (sections adjR).Additive where
  map_add := hom_ext_ι adjR (by simp)

/-- The inclusion `Γ ⟶ 𝟭`, as a natural transformation. -/
def sectionsι : sections adjR ⟶ 𝟭 A where
  app M := ι adjR M
  naturality _ _ g := map_ι adjR g

/-- The quotient by the part coming from the open, `M ↦ coker(ℓ(j M) ⟶ M)`. -/
def cosupport : A ⥤ A where
  obj M := cokernel (counitApp adjL M)
  map {M N} g := cokernel.desc _ (g ≫ cokernel.π _) <| by
    rw [← Category.assoc, ← counitApp_naturality, Category.assoc, cokernel.condition, comp_zero]
  map_id M := (cancel_epi (cokernel.π _)).1 (by simp)
  map_comp f g := (cancel_epi (cokernel.π _)).1 (by simp)

/-- The projection `M ⟶ coker(ℓ(j M) ⟶ M)`. -/
def π (M : A) : M ⟶ (cosupport adjL).obj M := cokernel.π (counitApp adjL M)

/-- The projection `M ⟶ coker(ℓ(j M) ⟶ M)` is an epimorphism. -/
instance (M : A) : Epi (π adjL M) := inferInstanceAs (Epi (cokernel.π _))

omit [Abelian A'] [j.Additive] [ℓ.Additive] in
/-- `ℓ(j M) ⟶ M ⟶ coker(ℓ(j M) ⟶ M)` vanishes. -/
@[reassoc (attr := simp)]
lemma counitApp_π (M : A) : counitApp adjL M ≫ π adjL M = 0 := cokernel.condition _

/-- `M ⟶ coker(ℓ(j M) ⟶ M)` is a cokernel of `ℓ(j M) ⟶ M`. -/
def πIsCokernel (M : A) : IsColimit (CokernelCofork.ofπ (π adjL M) (counitApp_π adjL M)) :=
  cokernelIsCokernel _

/-- A morphism out of `M` killing the part from the open factors through `coker(ℓ(j M) ⟶ M)`. -/
def desc {M W : A} (k : M ⟶ W) (hk : counitApp adjL M ≫ k = 0) : (cosupport adjL).obj M ⟶ W :=
  cokernel.desc _ k hk

omit [Abelian A'] [j.Additive] [ℓ.Additive] in
/-- The projection followed by the induced map out of the cokernel is the original map. -/
@[reassoc (attr := simp)]
lemma π_desc {M W : A} (k : M ⟶ W) (hk : counitApp adjL M ≫ k = 0) :
    π adjL M ≫ desc adjL k hk = k :=
  cokernel.π_desc _ _ _

omit [Abelian A'] [j.Additive] [ℓ.Additive] in
/-- The projection `𝟭 ⟶ cosupport` is natural. -/
@[reassoc (attr := simp)]
lemma π_map {M N : A} (g : M ⟶ N) :
    π adjL M ≫ (cosupport adjL).map g = g ≫ π adjL N :=
  cokernel.π_desc _ _ _

omit [Abelian A'] [j.Additive] [ℓ.Additive] in
/-- Maps out of `coker(ℓ(j M) ⟶ M)` are determined by their composite with the projection. -/
lemma hom_ext_π {M W : A} {a b : (cosupport adjL).obj M ⟶ W} (h : π adjL M ≫ a = π adjL M ≫ b) :
    a = b :=
  (cancel_epi (π adjL M)).1 h

/-- The quotient by the part from the open is an additive functor. -/
instance : (cosupport adjL).Additive where
  map_add := hom_ext_π adjL (by simp)

/-- The projection `𝟭 ⟶ cosupport`, as a natural transformation. -/
def cosupportπ : 𝟭 A ⟶ cosupport adjL where
  app M := π adjL M
  naturality _ _ g := (π_map adjL g).symm

/-- The bijection `Hom(coker(ℓ(j M) ⟶ M), N) ≃ Hom(M, ker(N ⟶ r(j N)))`. -/
def homEquiv (M N : A) : ((cosupport adjL).obj M ⟶ N) ≃ (M ⟶ (sections adjR).obj N) where
  toFun g := lift adjR (π adjL M ≫ g)
    ((comp_unit_eq_zero_iff adjR _).2 ((counit_comp_eq_zero_iff adjL _).1 (by simp)))
  invFun h := desc adjL (h ≫ ι adjR N)
    ((counit_comp_eq_zero_iff adjL _).2 ((comp_unit_eq_zero_iff adjR _).1 (by simp)))
  left_inv g := hom_ext_π adjL (by simp)
  right_inv h := hom_ext_ι adjR (by simp)

omit [ℓ.Additive] [r.Additive] in
/-- The bijection `homEquiv`, followed by the inclusion, is precomposition with the projection. -/
@[reassoc (attr := simp)]
lemma homEquiv_apply_ι {M N : A} (g : (cosupport adjL).obj M ⟶ N) :
    homEquiv adjL adjR M N g ≫ ι adjR N = π adjL M ≫ g :=
  lift_ι _ _ _

omit [ℓ.Additive] [r.Additive] in
/-- The inverse of `homEquiv`, preceded by the projection, is postcomposition with the
inclusion. -/
@[reassoc (attr := simp)]
lemma π_homEquiv_symm_apply {M N : A} (h : M ⟶ (sections adjR).obj N) :
    π adjL M ≫ (homEquiv adjL adjR M N).symm h = h ≫ ι adjR N :=
  π_desc _ _ _

omit [ℓ.Additive] [r.Additive] in
/-- Naturality of the inverse of `homEquiv` in the source. -/
lemma homEquiv_symm_naturality_left {M M' N : A} (f : M ⟶ M')
    (g : M' ⟶ (sections adjR).obj N) :
    (homEquiv adjL adjR M N).symm (f ≫ g) =
      (cosupport adjL).map f ≫ (homEquiv adjL adjR M' N).symm g :=
  hom_ext_π adjL (by simp)

omit [ℓ.Additive] [r.Additive] in
/-- Naturality of the inverse of `homEquiv` in the target. -/
lemma homEquiv_symm_naturality_right {M N N' : A} (h : M ⟶ (sections adjR).obj N)
    (g : N ⟶ N') :
    (homEquiv adjL adjR M N').symm (h ≫ (sections adjR).map g) =
      (homEquiv adjL adjR M N).symm h ≫ g :=
  hom_ext_π adjL (by simp)

/-- **The quotient by the part from the open is left adjoint to the sections killed by
restriction**, `coker(ℓ j ⟶ 𝟭) ⊣ ker(𝟭 ⟶ r j)`. -/
def adjunction : cosupport adjL ⊣ sections adjR :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv adjL adjR
      homEquiv_naturality_left_symm := homEquiv_symm_naturality_left adjL adjR
      homEquiv_naturality_right := fun {M N N'} f g ↦ hom_ext_ι adjR (by simp) }

omit [r.Additive] in
/-- **The sections killed by restriction restrict to zero** when the counit `j(r N) ⟶ N` of
`j ⊣ r` is invertible, as it is for restriction to an open subspace: `j` carries the unit
`M ⟶ r(j M)` to an isomorphism, by a triangle identity, and preserves its kernel. -/
lemma isZero_map_sections [PreservesFiniteLimits j] (hε : ∀ N, IsIso (adjR.counit.app N))
    (M : A) : IsZero (j.obj ((sections adjR).obj M)) := by
  have h : j.map (unitApp adjR M) ≫ adjR.counit.app (j.obj M) = 𝟙 _ :=
    adjR.left_triangle_components M
  have := hε (j.obj M)
  have : IsIso (j.map (unitApp adjR M) ≫ adjR.counit.app (j.obj M)) := by
    rw [h]
    infer_instance
  have : IsIso (j.map (unitApp adjR M)) :=
    IsIso.of_isIso_comp_right _ (adjR.counit.app (j.obj M))
  exact (isZero_kernel_of_mono (j.map (unitApp adjR M))).of_iso
    (PreservesKernel.iso j (unitApp adjR M))

/-! ### Acyclicity and K-injectivity -/

/-- The degreewise sequence `ℓ(j K) ⟶ K ⟶ coker(ℓ(j K) ⟶ K)` of complexes. -/
def cosupportShortComplex {κ : Type*} {c : ComplexShape κ} (K : HomologicalComplex A c) :
    ShortComplex (HomologicalComplex A c) where
  X₁ := ((j ⋙ ℓ).mapHomologicalComplex c).obj K
  X₂ := K
  X₃ := ((cosupport adjL).mapHomologicalComplex c).obj K
  f :=
    { f n := counitApp adjL (K.X n)
      comm' p q _ := (counitApp_naturality adjL (K.d p q)).symm }
  g :=
    { f n := π adjL (K.X n)
      comm' p q _ := π_map adjL (K.d p q) }
  zero := by ext n; exact counitApp_π adjL _

/-- `ℓ(j K) ⟶ K ⟶ coker(ℓ(j K) ⟶ K)` is short exact when the counit of `ℓ ⊣ j` is a
monomorphism. -/
lemma shortExact_cosupportShortComplex {κ : Type*} {c : ComplexShape κ}
    (hε : ∀ M, Mono (counitApp adjL M)) (K : HomologicalComplex A c) :
    (cosupportShortComplex adjL K).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  have : Mono (counitApp adjL (K.X n)) := hε _
  exact
    { exact := ShortComplex.exact_of_g_is_cokernel _ (πIsCokernel adjL (K.X n))
      mono_f := this
      epi_g := inferInstanceAs (Epi (π adjL (K.X n))) }

/-- An exact functor carries acyclic complexes to acyclic complexes. -/
lemma acyclic_map_of_exact {B : Type*} [Category B] [Abelian B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {κ : Type*} {c : ComplexShape κ}
    (K : HomologicalComplex A c) (hK : K.Acyclic) :
    ((F.mapHomologicalComplex c).obj K).Acyclic := fun i ↦ by
  have h := hK i
  rw [HomologicalComplex.exactAt_iff] at h ⊢
  exact h.map F

omit [r.Additive] in
include adjR in
/-- If `ℓ` is exact and the counit of `ℓ ⊣ j` is a monomorphism, `coker(ℓ(j K) ⟶ K)` is acyclic
for every acyclic complex `K`. -/
lemma acyclic_cosupport [PreservesFiniteLimits ℓ] (hε : ∀ M, Mono (counitApp adjL M))
    {κ : Type*} {c : ComplexShape κ} (K : HomologicalComplex A c) (hK : K.Acyclic) :
    (((cosupport adjL).mapHomologicalComplex c).obj K).Acyclic := by
  have : j.IsRightAdjoint := adjL.isRightAdjoint
  have : j.IsLeftAdjoint := adjR.isLeftAdjoint
  have : ℓ.IsLeftAdjoint := adjL.isLeftAdjoint
  have : PreservesFiniteLimits j := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits j := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits ℓ := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteLimits (j ⋙ ℓ) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (j ⋙ ℓ) := comp_preservesFiniteColimits _ _
  have hS := shortExact_cosupportShortComplex adjL hε K
  have h₁ : (cosupportShortComplex adjL K).X₁.Acyclic :=
    acyclic_map_of_exact (j ⋙ ℓ) K hK
  have h₂ : (cosupportShortComplex adjL K).X₂.Acyclic := hK
  intro i
  exact hS.exactAt_X₃ i ((h₂ i).isZero_homology.epi _) fun k _ ↦ (h₁ k).isZero_homology.mono _

/-- The transpose `cosupport K ⟶ I` of a chain map `K ⟶ Γ I`. -/
def transposeChainMap {κ : Type*} {c : ComplexShape κ} {K I : HomologicalComplex A c}
    (f : K ⟶ ((sections adjR).mapHomologicalComplex c).obj I) :
    ((cosupport adjL).mapHomologicalComplex c).obj K ⟶ I where
  f n := (homEquiv adjL adjR _ _).symm (f.f n)
  comm' p q _ := by
    have hf : f.f p ≫ (sections adjR).map (I.d p q) = K.d p q ≫ f.f q := f.comm p q
    change _ ≫ I.d p q = (cosupport adjL).map (K.d p q) ≫ _
    rw [← homEquiv_symm_naturality_left, ← homEquiv_symm_naturality_right, hf]

/-- The unit `K ⟶ Γ(cosupport K)` of `cosupport ⊣ Γ`, applied degreewise. -/
def unitChainMap {κ : Type*} {c : ComplexShape κ} (K : HomologicalComplex A c) :
    K ⟶ ((sections adjR).mapHomologicalComplex c).obj
      (((cosupport adjL).mapHomologicalComplex c).obj K) where
  f n := homEquiv adjL adjR _ _ (𝟙 _)
  comm' p q _ := hom_ext_ι adjR (by
    change (_ ≫ (sections adjR).map ((cosupport adjL).map (K.d p q))) ≫ _ = _
    simp)

omit [ℓ.Additive] [r.Additive] in
/-- A chain map `K ⟶ Γ I` is the unit followed by `Γ` of its transpose. -/
lemma eq_unitChainMap_comp_map_transposeChainMap {κ : Type*} {c : ComplexShape κ}
    {K I : HomologicalComplex A c}
    (f : K ⟶ ((sections adjR).mapHomologicalComplex c).obj I) :
    f = unitChainMap adjL adjR K ≫
      ((sections adjR).mapHomologicalComplex c).map (transposeChainMap adjL adjR f) := by
  ext n
  refine hom_ext_ι adjR ?_
  change _ = (_ ≫ (sections adjR).map _) ≫ _
  simp [unitChainMap, transposeChainMap]

omit [r.Additive] in
/-- **The sections killed by restriction of a K-injective complex form a K-injective
complex**, when `ℓ` is exact and the counit of `ℓ ⊣ j` is a monomorphism. -/
theorem isKInjective_sections [PreservesFiniteLimits ℓ] (hε : ∀ M, Mono (counitApp adjL M))
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective (((sections adjR).mapHomologicalComplex _).obj I) := by
  refine ⟨fun {K} f hK ↦ ⟨?_⟩⟩
  have h := CochainComplex.IsKInjective.homotopyZero (transposeChainMap adjL adjR f)
    (acyclic_cosupport adjL adjR hε K hK)
  refine (Homotopy.ofEq (eq_unitChainMap_comp_map_transposeChainMap adjL adjR f)).trans ?_
  refine (((sections adjR).mapHomotopy h).compLeft
    (unitChainMap adjL adjR K)).trans (Homotopy.ofEq ?_)
  simp

/-! ### The comparison `Γ I ⟶ I` -/

omit [Abelian A] [Abelian A'] [j.Additive] [ℓ.Additive] [r.Additive] in
include adjL in
/-- For an injective object `N`, the unit `N ⟶ r(j N)` is a split epimorphism as soon as the
counit `ℓ(j(r(j N))) ⟶ r(j N)` is a monomorphism. -/
lemma isSplitEpi_unitApp_of_injective (N : A) [Injective N]
    [Mono (counitApp adjL (r.obj (j.obj N)))] :
    IsSplitEpi (unitApp adjR N) := by
  set t : ℓ.obj (j.obj (r.obj (j.obj N))) ⟶ N :=
    (adjL.homEquiv _ _).symm (adjR.counit.app (j.obj N))
  set s := Injective.factorThru t (counitApp adjL (r.obj (j.obj N)))
  have hs : counitApp adjL _ ≫ s = t := Injective.comp_factorThru _ _
  have hjs : j.map s = adjR.counit.app (j.obj N) := by
    have := congrArg (adjL.homEquiv _ _) hs
    rw [counitApp, Adjunction.homEquiv_unit, Functor.map_comp,
      Adjunction.right_triangle_components_assoc, Equiv.apply_symm_apply] at this
    exact this
  refine ⟨⟨s, ?_⟩⟩
  apply (adjR.homEquiv _ _).symm.injective
  rw [unitApp, Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp,
    Category.assoc, Adjunction.left_triangle_components, Category.comp_id, hjs,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The degreewise sequence `Γ I ⟶ I ⟶ r(j I)` of complexes. -/
def sectionsShortComplex {κ : Type*} {c : ComplexShape κ} (I : HomologicalComplex A c) :
    ShortComplex (HomologicalComplex A c) where
  X₁ := ((sections adjR).mapHomologicalComplex c).obj I
  X₂ := I
  X₃ := ((j ⋙ r).mapHomologicalComplex c).obj I
  f :=
    { f n := ι adjR (I.X n)
      comm' p q _ := (map_ι adjR (I.d p q)).symm }
  g :=
    { f n := unitApp adjR (I.X n)
      comm' p q _ := (unitApp_naturality adjR (I.d p q)).symm }
  zero := by ext n; exact ι_unitApp adjR _

omit [ℓ.Additive] in
/-- `Γ I ⟶ I ⟶ r(j I)` is short exact for a complex with injective terms, when the counit of
`ℓ ⊣ j` is a monomorphism. -/
lemma shortExact_sectionsShortComplex {κ : Type*} {c : ComplexShape κ}
    (hε : ∀ M, Mono (counitApp adjL M)) (I : HomologicalComplex A c)
    [∀ n, Injective (I.X n)] :
    (sectionsShortComplex adjR I).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  have : Mono (counitApp adjL (r.obj (j.obj (I.X n)))) := hε _
  have := isSplitEpi_unitApp_of_injective adjL adjR (I.X n)
  exact
    { exact := ShortComplex.exact_of_f_is_kernel _ (ιIsKernel adjR (I.X n))
      mono_f := inferInstanceAs (Mono (ι adjR (I.X n)))
      epi_g := inferInstanceAs (Epi (unitApp adjR (I.X n))) }

omit [ℓ.Additive] in
/-- **`Γ I ⟶ I` is a quasi-isomorphism** for a complex `I` with injective terms whose
restriction `j I` is K-injective and acyclic, when the counit of `ℓ ⊣ j` is a monomorphism.

By Stacks 070G the restriction `j I` of a K-injective complex `I` is K-injective as soon as `ℓ`
is exact, `j` being right adjoint to `ℓ`. -/
theorem quasiIso_sectionsι (hε : ∀ M, Mono (counitApp adjL M))
    (I : CochainComplex A ℤ) [∀ n, Injective (I.X n)]
    (hjI : CochainComplex.IsKInjective ((j.mapHomologicalComplex _).obj I))
    (hjI' : ((j.mapHomologicalComplex _).obj I).Acyclic) :
    QuasiIso (sectionsShortComplex adjR I).f := by
  have hS := shortExact_sectionsShortComplex adjL adjR hε I
  have h₀ : Homotopy (𝟙 ((j.mapHomologicalComplex _).obj I)) 0 :=
    CochainComplex.IsKInjective.homotopyZero _ hjI'
  have h₃ : (sectionsShortComplex adjR I).X₃.Acyclic := by
    have h := r.mapHomotopy h₀
    intro i
    rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
    have := h.homologyMap_eq i
    simp only [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero,
      HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] at this
    exact this
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : Mono (HomologicalComplex.homologyMap (sectionsShortComplex adjR I).f i) :=
    (hS.homology_exact₁ (i - 1) i (by simp)).mono_g
      ((h₃ (i - 1)).isZero_homology.eq_of_src _ _)
  have hepi : Epi (HomologicalComplex.homologyMap (sectionsShortComplex adjR I).f i) :=
    (hS.homology_exact₂ i).epi_f ((h₃ i).isZero_homology.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end Stacks.Injectives.SectionsKilledByRestriction

end
