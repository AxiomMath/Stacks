module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Exact categories, and the extension-closed full subcategories of an abelian category

Following [Stacks, Tag 05SF], a *kernel-cokernel pair* in an additive category `𝒜` is a pair
`(i, p)` of composable morphisms such that `i` is a kernel of `p` and `p` is a cokernel of `i`.
Given a class `ℰ` of kernel-cokernel pairs, `i` is an *admissible monomorphism* if `(i, p) ∈ ℰ`
for some `p`, and `p` is an *admissible epimorphism* if `(i, p) ∈ ℰ` for some `i`; the pair
`(𝒜, ℰ)` is an *exact category* when `ℰ` is closed under isomorphism, identities are admissible
monomorphisms and admissible epimorphisms, both classes are stable under composition,
admissible monomorphisms have push-outs along every morphism and are stable under them, and
dually for admissible epimorphisms and base change.

The basic example, which is the one [Stacks, Tag 0B37] uses for the category `Vect(X)` of finite
locally free modules, is a full subcategory `P` of an abelian category `𝒞` which contains a zero
object and is closed under isomorphisms and under extensions, with `ℰ` the short complexes of
`P` which are short exact in `𝒞`. Its admissible epimorphisms are the epimorphisms of `𝒞`
between objects of `P` whose kernel lies in `P`, and its admissible monomorphisms are the kernels
of those.

The zeroth `K`-group of that exact category is the free abelian group on the objects of `P`
modulo `[E] = [E'] + [E'']` for every short exact sequence `0 → E' → E → E'' → 0` of `𝒞` whose
three terms lie in `P`.

## Main definitions

* `Stacks.ExactCategory.IsKernelCokernelPair`, `Stacks.ExactCategory.AdmissibleMono`,
  `Stacks.ExactCategory.AdmissibleEpi`, `Stacks.ExactCategory.IsExactStructure`: the notions of
  [Stacks, Tag 05SF].
* `Stacks.ExactCategory.conflation`: the short complexes of `P` which are short exact in `𝒞`.
* `Stacks.ExactCategory.KZero`: the zeroth `K`-group of that exact structure, with its classes
  `Stacks.ExactCategory.KZero.of` and its universal property `Stacks.ExactCategory.KZero.lift`.

## Main results

* `Stacks.ExactCategory.isExactStructure_conflation`: the short complexes of `P` which are
  short exact in `𝒞` form an exact structure on `P`.
* `Stacks.ExactCategory.admissibleEpi_conflation_iff` and
  `Stacks.ExactCategory.admissibleMono_conflation_iff`: its admissible epimorphisms and
  monomorphisms.

## References

* [Stacks Project, Tag 05SF](https://stacks.math.columbia.edu/tag/05SF)
* [Stacks Project, Tag 0B37](https://stacks.math.columbia.edu/tag/0B37)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.ExactCategory

section Definitions

variable {A : Type u} [Category.{v} A] [Preadditive A]

/-- A short complex `X ⟶ Y ⟶ Z` is a *kernel-cokernel pair* when its first map is a kernel of
its second and its second map is a cokernel of its first. -/
def IsKernelCokernelPair (S : ShortComplex A) : Prop :=
  Nonempty (IsLimit (KernelFork.ofι S.f S.zero)) ∧
    Nonempty (IsColimit (CokernelCofork.ofπ S.g S.zero))

variable (E : ShortComplex A → Prop)

/-- A morphism is an *admissible monomorphism* for the class `E` of short complexes when it is
the first map of a member of `E`. -/
def AdmissibleMono {X Y : A} (i : X ⟶ Y) : Prop :=
  ∃ (Z : A) (p : Y ⟶ Z) (w : i ≫ p = 0), E (ShortComplex.mk i p w)

/-- A morphism is an *admissible epimorphism* for the class `E` of short complexes when it is
the second map of a member of `E`. -/
def AdmissibleEpi {Y Z : A} (p : Y ⟶ Z) : Prop :=
  ∃ (X : A) (i : X ⟶ Y) (w : i ≫ p = 0), E (ShortComplex.mk i p w)

/-- **An exact structure** on an additive category in the sense of [Stacks, Tag 05SF]: a class
`E` of kernel-cokernel pairs, closed under isomorphism, such that identities are admissible
monomorphisms and admissible epimorphisms, admissible monomorphisms and admissible epimorphisms
are stable under composition, the push-out of an admissible monomorphism along any morphism
exists and is an admissible monomorphism, and the base change of an admissible epimorphism along
any morphism exists and is an admissible epimorphism. -/
structure IsExactStructure : Prop where
  isKernelCokernelPair {S : ShortComplex A} : E S → IsKernelCokernelPair S
  of_iso {S T : ShortComplex A} : (S ≅ T) → E S → E T
  admissibleMono_id (X : A) : AdmissibleMono E (𝟙 X)
  admissibleEpi_id (X : A) : AdmissibleEpi E (𝟙 X)
  admissibleMono_comp {X Y Z : A} {i : X ⟶ Y} {j : Y ⟶ Z} :
    AdmissibleMono E i → AdmissibleMono E j → AdmissibleMono E (i ≫ j)
  admissibleEpi_comp {X Y Z : A} {p : X ⟶ Y} {q : Y ⟶ Z} :
    AdmissibleEpi E p → AdmissibleEpi E q → AdmissibleEpi E (p ≫ q)
  exists_isPushout {X Y X' : A} {i : X ⟶ Y} (hi : AdmissibleMono E i) (a : X ⟶ X') :
    ∃ (Y' : A) (i' : X' ⟶ Y') (b : Y ⟶ Y'), IsPushout i a b i' ∧ AdmissibleMono E i'
  exists_isPullback {Y Z Z' : A} {p : Y ⟶ Z} (hp : AdmissibleEpi E p) (c : Z' ⟶ Z) :
    ∃ (Y' : A) (p' : Y' ⟶ Z') (b : Y' ⟶ Y), IsPullback b p' p c ∧ AdmissibleEpi E p'

end Definitions

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The push-out of the first map of a short exact sequence along any morphism is the first map
of a short exact sequence with the same third term. -/
theorem shortExact_pushout {X Y Z X' : C} {i : X ⟶ Y} {p : Y ⟶ Z} {w : i ≫ p = 0}
    (hS : (ShortComplex.mk i p w).ShortExact) (a : X ⟶ X') :
    (ShortComplex.mk (pushout.inr i a)
      (pushout.desc (f := i) (g := a) p (0 : X' ⟶ Z) (by rw [w, comp_zero]))
      (by rw [pushout.inr_desc])).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have hc := hS.gIsCokernel
  have hp' : Epi (pushout.desc (f := i) (g := a) p (0 : X' ⟶ Z) (by rw [w, comp_zero])) :=
    epi_of_epi_fac (pushout.inl_desc (f := i) (g := a) p (0 : X' ⟶ Z) (by rw [w, comp_zero]))
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ ?_) inferInstance hp'
  have hdesc : ∀ {T : C} (t : pushout i a ⟶ T), pushout.inr i a ≫ t = 0 →
      i ≫ pushout.inl i a ≫ t = 0 := fun t ht => by
    rw [← Category.assoc, pushout.condition, Category.assoc, ht, comp_zero]
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun {T} t ht => (CokernelCofork.IsColimit.desc' hc (pushout.inl i a ≫ t) (hdesc t ht)).1)
    (fun {T} t ht => ?_) (fun {T} t ht m hm => ?_)
  · have hd := (CokernelCofork.IsColimit.desc' hc (pushout.inl i a ≫ t) (hdesc t ht)).2
    refine pushout.hom_ext ?_ ?_
    · rw [pushout.inl_desc_assoc]
      exact hd
    · rw [pushout.inr_desc_assoc, zero_comp]
      exact ht.symm
  · have hd := (CokernelCofork.IsColimit.desc' hc (pushout.inl i a ≫ t) (hdesc t ht)).2
    refine Cofork.IsColimit.hom_ext hc ?_
    refine Eq.trans ?_ hd.symm
    change p ≫ m = pushout.inl i a ≫ t
    rw [← hm, pushout.inl_desc_assoc]

/-- The base change of the second map of a short exact sequence along any morphism is the second
map of a short exact sequence with the same first term. -/
theorem shortExact_pullback {X Y Z Z' : C} {i : X ⟶ Y} {p : Y ⟶ Z} {w : i ≫ p = 0}
    (hS : (ShortComplex.mk i p w).ShortExact) (c : Z' ⟶ Z) :
    (ShortComplex.mk (pullback.lift (f := p) (g := c) i (0 : X ⟶ Z') (by rw [w, zero_comp]))
      (pullback.snd p c) (by rw [pullback.lift_snd])).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have hk := hS.fIsKernel
  have hi' : Mono (pullback.lift (f := p) (g := c) i (0 : X ⟶ Z') (by rw [w, zero_comp])) :=
    mono_of_mono_fac (pullback.lift_fst (f := p) (g := c) i (0 : X ⟶ Z') (by rw [w, zero_comp]))
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ ?_) hi' inferInstance
  have hlift : ∀ {T : C} (t : T ⟶ pullback p c), t ≫ pullback.snd p c = 0 →
      (t ≫ pullback.fst p c) ≫ p = 0 := fun t ht => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, zero_comp]
  refine KernelFork.IsLimit.ofι _ _
    (fun {T} t ht => (KernelFork.IsLimit.lift' hk (t ≫ pullback.fst p c) (hlift t ht)).1)
    (fun {T} t ht => ?_) (fun {T} t ht m hm => ?_)
  · have hl := (KernelFork.IsLimit.lift' hk (t ≫ pullback.fst p c) (hlift t ht)).2
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst]
      exact hl
    · rw [Category.assoc, pullback.lift_snd, comp_zero]
      exact ht.symm
  · have hl := (KernelFork.IsLimit.lift' hk (t ≫ pullback.fst p c) (hlift t ht)).2
    refine Fork.IsLimit.hom_ext hk ?_
    refine Eq.trans ?_ hl.symm
    change m ≫ i = t ≫ pullback.fst p c
    rw [← hm, Category.assoc, pullback.lift_fst]

/-- **The cokernels of two composable monomorphisms and of their composite form a short exact
sequence** `0 → coker i → coker (i ≫ j) → coker j → 0`. -/
theorem shortExact_cokernel_comp {X Y Z : C} (i : X ⟶ Y) (j : Y ⟶ Z) [Mono j] :
    (ShortComplex.mk (cokernel.map i (i ≫ j) (𝟙 _) j (by simp))
      (cokernel.map (i ≫ j) j i (𝟙 _) (by simp)) (by ext; simp)).ShortExact := by
  have h := kernelCokernelCompSequence_exact i j
  have h₂ := h.exact 2
  have h₃ := h.exact 3
  have hz : IsZero (kernel j) := isZero_kernel_of_mono j
  have hmono : Mono (cokernel.map i (i ≫ j) (𝟙 _) j (by simp)) :=
    h₂.mono_g (hz.eq_of_src _ _)
  have hepi : Epi (cokernel.map (i ≫ j) j i (𝟙 _) (by simp)) :=
    inferInstanceAs (Epi ((kernelCokernelCompSequence i j).map' 4 5))
  exact ShortComplex.ShortExact.mk' h₃ hmono hepi

/-- **The kernels of two composable epimorphisms and of their composite form a short exact
sequence** `0 → ker p → ker (p ≫ q) → ker q → 0`. -/
theorem shortExact_kernel_comp {X Y Z : C} (p : X ⟶ Y) (q : Y ⟶ Z) [Epi p] :
    (ShortComplex.mk (kernel.map p (p ≫ q) (𝟙 _) q (by simp))
      (kernel.map (p ≫ q) q p (𝟙 _) (by simp)) (by ext; simp)).ShortExact := by
  have h := kernelCokernelCompSequence_exact p q
  have h₀ := h.exact 0
  have h₁ := h.exact 1
  have hz : IsZero (cokernel p) := isZero_cokernel_of_epi p
  have hepi : Epi (kernel.map (p ≫ q) q p (𝟙 _) (by simp)) :=
    h₁.epi_f (hz.eq_of_tgt _ _)
  have hmono : Mono (kernel.map p (p ≫ q) (𝟙 _) q (by simp)) :=
    inferInstanceAs (Mono ((kernelCokernelCompSequence p q).map' 0 1))
  exact ShortComplex.ShortExact.mk' h₀ hmono hepi

variable (P : ObjectProperty C)

/-- The *conflations* of a full subcategory `P` of an abelian category: the short complexes of
`P` which are short exact in the ambient category. -/
def conflation (S : ShortComplex P.FullSubcategory) : Prop :=
  (S.map P.ι).ShortExact

variable {P}

/-- An object of the full subcategory `P`, from an object of the ambient category satisfying
`P`. -/
abbrev mkObj (X : C) (hX : P X) : P.FullSubcategory := ⟨X, hX⟩

/-- A short exact sequence of the ambient category whose three terms satisfy `P` is a
conflation of `P`. -/
theorem conflation_mk {X Y Z : C} (hX : P X) (hY : P Y) (hZ : P Z) {i : X ⟶ Y} {p : Y ⟶ Z}
    {w : i ≫ p = 0} (hS : (ShortComplex.mk i p w).ShortExact) :
    conflation P (ShortComplex.mk (X₁ := mkObj X hX) (X₂ := mkObj Y hY) (X₃ := mkObj Z hZ)
      (P.homMk i) (P.homMk p) (by ext; exact w)) :=
  hS

variable [P.IsClosedUnderIsomorphisms]

/-- A morphism of the full subcategory `P` is an admissible epimorphism for the conflations
exactly when it is an epimorphism of the ambient category whose kernel lies in `P`. -/
theorem admissibleEpi_conflation_iff {Y Z : P.FullSubcategory} (p : Y ⟶ Z) :
    AdmissibleEpi (conflation P) p ↔ Epi p.hom ∧ P (kernel p.hom) := by
  constructor
  · rintro ⟨X, i, w, hS⟩
    have hS' : (ShortComplex.mk (P.ι.map i) (P.ι.map p)
        (by rw [← P.ι.map_comp, w, P.ι.map_zero])).ShortExact := hS
    have := hS'.epi_g
    refine ⟨this, P.prop_of_iso ?_ X.property⟩
    exact IsLimit.conePointUniqueUpToIso hS'.fIsKernel (limit.isLimit _)
  · rintro ⟨hp, hK⟩
    refine ⟨mkObj (kernel p.hom) hK, P.homMk (kernel.ι p.hom), by ext; exact kernel.condition _, ?_⟩
    exact ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p.hom))
      (inferInstanceAs (Mono (kernel.ι p.hom))) hp

/-- A morphism of the full subcategory `P` is an admissible monomorphism for the conflations
exactly when it is a monomorphism of the ambient category whose cokernel lies in `P`. -/
theorem admissibleMono_conflation_iff' {X Y : P.FullSubcategory} (i : X ⟶ Y) :
    AdmissibleMono (conflation P) i ↔ Mono i.hom ∧ P (cokernel i.hom) := by
  constructor
  · rintro ⟨Z, p, w, hS⟩
    have hS' : (ShortComplex.mk (P.ι.map i) (P.ι.map p)
        (by rw [← P.ι.map_comp, w, P.ι.map_zero])).ShortExact := hS
    have := hS'.mono_f
    refine ⟨this, P.prop_of_iso ?_ Z.property⟩
    exact IsColimit.coconePointUniqueUpToIso hS'.gIsCokernel (colimit.isColimit _)
  · rintro ⟨hi, hQ⟩
    refine ⟨mkObj (cokernel i.hom) hQ, P.homMk (cokernel.π i.hom),
      by ext; exact cokernel.condition _, ?_⟩
    exact ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i.hom)) hi
      (inferInstanceAs (Epi (cokernel.π i.hom)))

/-- **The admissible monomorphisms are the kernels of the admissible epimorphisms**: a morphism
of `P` is an admissible monomorphism exactly when it is a kernel, in the ambient category, of an
epimorphism of `P` whose kernel lies in `P`. -/
theorem admissibleMono_conflation_iff {X Y : P.FullSubcategory} (i : X ⟶ Y) :
    AdmissibleMono (conflation P) i ↔
      ∃ (Z : P.FullSubcategory) (p : Y ⟶ Z) (w : i.hom ≫ p.hom = 0),
        (Epi p.hom ∧ P (kernel p.hom)) ∧ Nonempty (IsLimit (KernelFork.ofι i.hom w)) := by
  constructor
  · rintro ⟨Z, p, w, hS⟩
    have hS' : (ShortComplex.mk (P.ι.map i) (P.ι.map p)
        (by rw [← P.ι.map_comp, w, P.ι.map_zero])).ShortExact := hS
    refine ⟨Z, p, congrArg InducedCategory.Hom.hom w,
      (admissibleEpi_conflation_iff p).mp ⟨X, i, w, hS⟩,
      ⟨hS'.fIsKernel⟩⟩
  · rintro ⟨Z, p, w, ⟨hp, -⟩, ⟨hk⟩⟩
    refine ⟨Z, p, by ext; exact w, ?_⟩
    have hmono : Mono i.hom := mono_of_isLimit_fork hk
    exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hk) hmono hp

variable [P.IsClosedUnderExtensions] [P.ContainsZero]

/-- **The extension-closed full subcategories of an abelian category are exact categories.** If
`P` contains a zero object and is closed under isomorphisms and under extensions, the short
complexes of `P` which are short exact in the ambient abelian category form an exact structure
on `P` in the sense of [Stacks, Tag 05SF]. -/
theorem isExactStructure_conflation : IsExactStructure (conflation P) where
  isKernelCokernelPair {S} hS := by
    have hS' : (S.map P.ι).ShortExact := hS
    refine ⟨⟨isLimitOfReflects P.ι ?_⟩, ⟨isColimitOfReflects P.ι ?_⟩⟩
    · exact (KernelFork.isLimitMapConeEquiv _ P.ι).symm hS'.fIsKernel
    · exact (CokernelCofork.isColimitMapCoconeEquiv _ P.ι).symm hS'.gIsCokernel
  of_iso {S T} e hS :=
    ShortComplex.shortExact_of_iso (P.ι.mapShortComplex.mapIso e) hS
  admissibleMono_id X := by
    refine (admissibleMono_conflation_iff' (𝟙 X)).mpr ⟨inferInstanceAs (Mono (𝟙 X.obj)), ?_⟩
    exact P.prop_of_isZero (isZero_cokernel_of_epi (𝟙 X.obj))
  admissibleEpi_id X := by
    refine (admissibleEpi_conflation_iff (𝟙 X)).mpr ⟨inferInstanceAs (Epi (𝟙 X.obj)), ?_⟩
    exact P.prop_of_isZero (isZero_kernel_of_mono (𝟙 X.obj))
  admissibleMono_comp {X Y Z i j} hi hj := by
    obtain ⟨hi, hQi⟩ := (admissibleMono_conflation_iff' i).mp hi
    obtain ⟨hj, hQj⟩ := (admissibleMono_conflation_iff' j).mp hj
    refine (admissibleMono_conflation_iff' (i ≫ j)).mpr
      ⟨inferInstanceAs (Mono (i.hom ≫ j.hom)), ?_⟩
    exact P.prop_X₂_of_shortExact (shortExact_cokernel_comp i.hom j.hom) hQi hQj
  admissibleEpi_comp {X Y Z p q} hp hq := by
    obtain ⟨hp, hKp⟩ := (admissibleEpi_conflation_iff p).mp hp
    obtain ⟨hq, hKq⟩ := (admissibleEpi_conflation_iff q).mp hq
    refine (admissibleEpi_conflation_iff (p ≫ q)).mpr
      ⟨inferInstanceAs (Epi (p.hom ≫ q.hom)), ?_⟩
    exact P.prop_X₂_of_shortExact (shortExact_kernel_comp p.hom q.hom) hKp hKq
  exists_isPushout {X Y X' i} hi a := by
    obtain ⟨Z, p, w, hS⟩ := hi
    have hw : i.hom ≫ p.hom = 0 := congrArg InducedCategory.Hom.hom w
    have hS' : (ShortComplex.mk i.hom p.hom hw).ShortExact := hS
    have hT := shortExact_pushout hS' a.hom
    have hB : P (pushout i.hom a.hom) := P.prop_X₂_of_shortExact hT X'.property Z.property
    refine ⟨mkObj _ hB, P.homMk (pushout.inr i.hom a.hom), P.homMk (pushout.inl i.hom a.hom),
      ?_, ⟨Z, P.homMk (pushout.desc (f := i.hom) (g := a.hom) p.hom 0
        (by rw [hw, comp_zero])), by ext; exact pushout.inr_desc _ _ _, hT⟩⟩
    exact IsPushout.of_map_of_faithful P.ι (IsPushout.of_hasPushout i.hom a.hom)
  exists_isPullback {Y Z Z' p} hp c := by
    obtain ⟨X, i, w, hS⟩ := hp
    have hw : i.hom ≫ p.hom = 0 := congrArg InducedCategory.Hom.hom w
    have hS' : (ShortComplex.mk i.hom p.hom hw).ShortExact := hS
    have hT := shortExact_pullback hS' c.hom
    have hB : P (pullback p.hom c.hom) := P.prop_X₂_of_shortExact hT X.property Z'.property
    refine ⟨mkObj _ hB, P.homMk (pullback.snd p.hom c.hom), P.homMk (pullback.fst p.hom c.hom),
      ?_, ⟨X, P.homMk (pullback.lift (f := p.hom) (g := c.hom) i.hom 0
        (by rw [hw, zero_comp])), by ext; exact pullback.lift_snd _ _ _, hT⟩⟩
    exact IsPullback.of_map_of_faithful P.ι (IsPullback.of_hasPullback p.hom c.hom)

end Abelian

/-! ### The zeroth `K`-group of the exact structure -/

section KZero

variable {C : Type u} [Category.{v} C] [Preadditive C] (P : ObjectProperty C)

/-- The relations `[E] - [E'] - [E'']` defining the zeroth `K`-group of the conflations of `P`,
one for each short exact sequence `0 → E' → E → E'' → 0` of the ambient category whose three
terms satisfy `P`. -/
def KZero.relations : Set (FreeAbelianGroup P.FullSubcategory) :=
  {r | ∃ (S : ShortComplex C) (_ : S.ShortExact) (h₁ : P S.X₁) (h₂ : P S.X₂) (h₃ : P S.X₃),
    r = FreeAbelianGroup.of (mkObj S.X₂ h₂) - FreeAbelianGroup.of (mkObj S.X₁ h₁) -
      FreeAbelianGroup.of (mkObj S.X₃ h₃)}

/-- **The zeroth `K`-group** `K₀` of the conflations of `P`: the abelian group generated by a
class `[E]` for every object `E` of `P`, subject to `[E] = [E'] + [E'']` for every short exact
sequence `0 → E' → E → E'' → 0` of the ambient category with its three terms in `P`. -/
def KZero : Type _ :=
  FreeAbelianGroup P.FullSubcategory ⧸ AddSubgroup.closure (KZero.relations P)

namespace KZero

/-- The abelian group structure of the zeroth `K`-group. -/
instance : AddCommGroup (KZero P) :=
  inferInstanceAs (AddCommGroup (FreeAbelianGroup P.FullSubcategory ⧸
    AddSubgroup.closure (KZero.relations P)))

variable {P}

/-- The class `[E]` of an object of `P` in the zeroth `K`-group. -/
def of (E : P.FullSubcategory) : KZero P :=
  QuotientAddGroup.mk (s := AddSubgroup.closure (KZero.relations P)) (FreeAbelianGroup.of E)

/-- **The defining relation** `[E] = [E'] + [E'']` for a short exact sequence of the ambient
category whose three terms lie in `P`. -/
theorem of_shortExact {S : ShortComplex C} (hS : S.ShortExact) (h₁ : P S.X₁) (h₂ : P S.X₂)
    (h₃ : P S.X₃) : of (mkObj S.X₂ h₂) = of (mkObj S.X₁ h₁) + of (mkObj S.X₃ h₃) := by
  have h := (QuotientAddGroup.eq_zero_iff (N := AddSubgroup.closure (KZero.relations P)) _).mpr
    (AddSubgroup.subset_closure ⟨S, hS, h₁, h₂, h₃, rfl⟩)
  rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_sub, sub_sub, sub_eq_zero] at h
  exact h

/-- The additive map out of the zeroth `K`-group determined by a function on the objects of `P`
which is additive on the short exact sequences of the ambient category with terms in `P`. -/
def lift {G : Type*} [AddCommGroup G] (f : P.FullSubcategory → G)
    (hf : ∀ (S : ShortComplex C) (_ : S.ShortExact) (h₁ : P S.X₁) (h₂ : P S.X₂) (h₃ : P S.X₃),
      f (mkObj S.X₂ h₂) = f (mkObj S.X₁ h₁) + f (mkObj S.X₃ h₃)) :
    KZero P →+ G :=
  QuotientAddGroup.lift _ (FreeAbelianGroup.lift f) <| by
    refine (AddSubgroup.closure_le _).mpr ?_
    rintro _ ⟨S, hS, h₁, h₂, h₃, rfl⟩
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift_apply_of,
      hf S hS h₁ h₂ h₃]
    abel

@[simp]
theorem lift_of {G : Type*} [AddCommGroup G] (f : P.FullSubcategory → G)
    (hf : ∀ (S : ShortComplex C) (_ : S.ShortExact) (h₁ : P S.X₁) (h₂ : P S.X₂) (h₃ : P S.X₃),
      f (mkObj S.X₂ h₂) = f (mkObj S.X₁ h₁) + f (mkObj S.X₃ h₃)) (E : P.FullSubcategory) :
    lift f hf (of E) = f E :=
  FreeAbelianGroup.lift_apply_of f E

/-- An additive map out of the zeroth `K`-group is determined by its values on the classes of
objects. -/
theorem hom_ext {G : Type*} [AddCommGroup G] {φ ψ : KZero P →+ G}
    (h : ∀ E : P.FullSubcategory, φ (of E) = ψ (of E)) : φ = ψ :=
  QuotientAddGroup.addMonoidHom_ext _ (FreeAbelianGroup.lift_ext _ _ fun E => h E)

end KZero

end KZero

end Stacks.ExactCategory

end
