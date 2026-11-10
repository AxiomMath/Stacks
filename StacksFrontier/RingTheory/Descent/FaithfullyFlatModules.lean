module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
public import Mathlib.RingTheory.Finiteness.Descent
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of modules along a flat ring map

Let `R → S` be a ring map and let `N` be an `S`-module. A *descent datum* on `N` is an `S`-linear
coaction `N →ₗ[S] S ⊗[R] N` which is counital and coassociative, i.e. precisely a coalgebra over
the comonad on `S`-modules induced by the adjunction between extension and restriction of scalars
along `R → S`. It is the normalised form of the more familiar gluing isomorphism
`N ⊗[R] S ≅ S ⊗[R] N` together with its cocycle condition.

Two further consequences of flatness are recorded here because they are the ring-level content of
quasi-coherence statements: flat base change commutes with kernels, and membership in the image of
a map is detected by a faithfully flat base change.

Given such a datum, the *descended module* is the `R`-submodule
`{n : N | coaction n = 1 ⊗ₜ n}` of `N`. The main theorem is that for `S` flat over `R` the
inclusion of the descended module exhibits `N` as the base change of an `R`-module: descent data
along a flat ring map are effective.

When `S` is moreover faithfully flat over `R`, the construction is inverse to base change: for an
`R`-module `M` the module `S ⊗[R] M` carries a canonical descent datum whose descended module is
exactly the image of `M`. Equivalently, the Amitsur (descent) complex
`M → S ⊗[R] M → S ⊗[R] S ⊗[R] M` is exact, which in the mirror-image spelling says that
`M ⊗[R] S` is the equalizer of the two coaction maps into `M ⊗[R] (S ⊗[R] S)`. The case `M = R`
of this is Mathlib's `Algebra.IsEffective.of_faithfullyFlat`.

## Main definitions

* `Module.Descent.counit`: for an `S`-module `N`, the `S`-linear map `S ⊗[R] N →ₗ[S] N`
  given by `s ⊗ₜ n ↦ s • n`.
* `Module.Descent.Datum`: a descent datum on an `S`-module relative to `R → S`.
* `Module.Descent.Datum.descended`: the `R`-submodule of `N` cut out by a descent datum.
* `Module.Descent.Datum.IsHom`: compatibility of an `S`-linear map with two descent data.
* `Module.Descent.Datum.mapDescended`: the induced map of descended modules.
* `Module.Descent.baseChange`: the canonical descent datum on a base-changed module.
* `Module.Descent.toKerLTensor`: the canonical map from the kernel of an `R`-linear map to the
  kernel of its base change.

## Main results

* `Module.Descent.Datum.isBaseChange`: for `S` flat over `R`, the inclusion of the descended
  module exhibits `N` as the base change of the descended module. This is effectivity of descent.
* `Module.Descent.Datum.equivBaseChange`: the same statement as an `S`-linear equivalence
  `S ⊗[R] descended ≃ₗ[S] N`.
* `Module.Descent.Datum.span_descended_eq_top` and
  `Module.Descent.Datum.exists_fin_descended_span_eq_top`: `N` is generated over `S` by the
  descended module, by finitely many of its elements when `N` is a finite `S`-module.
* `Module.Descent.Datum.surjective_mapDescended`: a surjective morphism of descent data induces a
  surjection of descended modules.
* `Module.Descent.descendedEquiv`: for `S` faithfully flat over `R`, an `R`-module `M` is
  isomorphic to the module descended from the canonical datum on `S ⊗[R] M`.
* `Module.Descent.descended_baseChange`: exactness of the Amitsur complex, in the form that the
  equalizer of the two coactions on `S ⊗[R] M` is the image of `M`.
* `Module.Descent.exact_mk_one` and `Module.Descent.exact_lTensor_includeLeftSubRight`: exactness
  of the Amitsur complex `M → M ⊗[R] S → M ⊗[R] (S ⊗[R] S)`, in the two mirror-image spellings.
  The latter generalises `Algebra.IsEffective.of_faithfullyFlat` from the module `R` to an
  arbitrary module `M`.
* `Module.Descent.Datum.finite_descended`, `Module.Descent.Datum.finitePresentation_descended`:
  finite generation and finite presentation transfer from `N` to the descended module.
* `Module.Descent.isBaseChange_ker`: flat base change commutes with kernels, so that the kernel of
  a map of quasi-coherent modules is again quasi-coherent.
* `Module.Descent.mem_range_of_one_tmul_mem_range` and
  `Module.Descent.surjective_of_forall_one_tmul_mem_range`: membership in the image of a map, and
  hence its surjectivity, is detected by a faithfully flat base change.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open TensorProduct

namespace Module.Descent

variable (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
variable (N : Type*) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- For an `S`-module `N`, the `S`-linear map `S ⊗[R] N →ₗ[S] N` given by `s ⊗ₜ n ↦ s • n`.
This is the counit at `N` of the comonad on `S`-modules induced by extension and restriction of
scalars along `R → S`. -/
noncomputable def counit : S ⊗[R] N →ₗ[S] N :=
  AlgebraTensorModule.lift (LinearMap.restrictScalarsₗ R S N N S ∘ₗ LinearMap.lsmul S N)

/-- `Module.Descent.counit` on a pure tensor. -/
@[simp]
lemma counit_tmul (s : S) (n : N) : counit R S N (s ⊗ₜ[R] n) = s • n := rfl

omit [Module S N] [IsScalarTower R S N] in
/-- The counit of the comonad is a retraction of its comultiplication. -/
lemma counit_comp_lTensor_mk_one :
    counit R S (S ⊗[R] N) ∘ₗ AlgebraTensorModule.lTensor S S (TensorProduct.mk R S N 1) =
      LinearMap.id := by
  ext; simp

variable {R S N}

/-- A descent datum on the `S`-module `N` relative to a ring map `R → S`: an `S`-linear coaction
`N →ₗ[S] S ⊗[R] N` which is counital and coassociative. This is exactly a coalgebra over the
comonad on `S`-modules induced by extension and restriction of scalars along `R → S`, and is the
normalised form of a gluing isomorphism `N ⊗[R] S ≅ S ⊗[R] N` satisfying the cocycle condition. -/
structure Datum (R S N : Type*) [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] where
  /-- The coaction of the descent datum. -/
  coaction : N →ₗ[S] S ⊗[R] N
  /-- Counitality: composing the coaction with `s ⊗ₜ n ↦ s • n` is the identity. -/
  counit_coaction (n : N) : counit R S N (coaction n) = n
  /-- Coassociativity, the normalised form of the cocycle condition. -/
  coassoc (n : N) :
    AlgebraTensorModule.lTensor S S (coaction.restrictScalars R) (coaction n) =
      AlgebraTensorModule.lTensor S S (TensorProduct.mk R S N 1) (coaction n)

namespace Datum

variable (d : Datum R S N)

/-- The `S`-submodule of `S ⊗[R] N` on which the two coactions
`S ⊗[R] N → S ⊗[R] (S ⊗[R] N)` agree. It is the base change of `Datum.descended`. -/
noncomputable def eqSubmodule : Submodule S (S ⊗[R] N) :=
  LinearMap.eqLocus (AlgebraTensorModule.lTensor S S (d.coaction.restrictScalars R))
    (AlgebraTensorModule.lTensor S S (TensorProduct.mk R S N 1))

/-- Membership in `Module.Descent.Datum.eqSubmodule` unfolded. -/
lemma mem_eqSubmodule_iff {x : S ⊗[R] N} :
    x ∈ d.eqSubmodule ↔
      AlgebraTensorModule.lTensor S S (d.coaction.restrictScalars R) x =
        AlgebraTensorModule.lTensor S S (TensorProduct.mk R S N 1) x := Iff.rfl

/-- Coassociativity says exactly that the coaction lands in `Datum.eqSubmodule`. -/
lemma coaction_mem (n : N) : d.coaction n ∈ d.eqSubmodule := d.coassoc n

/-- Base changing the coaction and then applying the counit is the same as applying the counit
and then the coaction. -/
lemma counit_comp_lTensor_coaction :
    counit R S (S ⊗[R] N) ∘ₗ AlgebraTensorModule.lTensor S S (d.coaction.restrictScalars R) =
      d.coaction ∘ₗ counit R S N := by
  ext; simp

/-- On `Datum.eqSubmodule` the counit is a left inverse of the coaction. -/
lemma coaction_counit {x : S ⊗[R] N} (hx : x ∈ d.eqSubmodule) :
    d.coaction (counit R S N x) = x := by
  have h₁ := congr($(d.counit_comp_lTensor_coaction) x)
  have h₂ := congr($(counit_comp_lTensor_mk_one R S N) x)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at h₁ h₂
  rw [← h₁, d.mem_eqSubmodule_iff.1 hx, h₂]

/-- The counit identifies `Datum.eqSubmodule` with `N`. -/
noncomputable def eqSubmoduleEquiv : d.eqSubmodule ≃ₗ[S] N :=
  LinearEquiv.ofLinearMap (counit R S N ∘ₗ d.eqSubmodule.subtype)
    (LinearMap.codRestrict _ d.coaction d.coaction_mem)
    (by ext n; exact d.counit_coaction n)
    (by ext x; simpa using d.coaction_counit x.2)

/-- `Module.Descent.Datum.eqSubmoduleEquiv` is induced by the counit. -/
@[simp]
lemma eqSubmoduleEquiv_apply (x : d.eqSubmodule) :
    d.eqSubmoduleEquiv x = counit R S N (x : S ⊗[R] N) := rfl

/-- The `R`-module descended from a descent datum: the `R`-submodule of `N` on which the coaction
agrees with `n ↦ 1 ⊗ₜ n`. -/
noncomputable def descended : Submodule R N :=
  LinearMap.eqLocus (d.coaction.restrictScalars R) (TensorProduct.mk R S N 1)

/-- Membership in `Module.Descent.Datum.descended` is the coaction equation: the descended
module is cut out as the locus where the coaction agrees with `n ↦ 1 ⊗ₜ n`. -/
lemma mem_descended_iff {n : N} : n ∈ d.descended ↔ d.coaction n = (1 : S) ⊗ₜ[R] n :=
  LinearMap.mem_eqLocus

section Flat

variable [Module.Flat R S]

/-- **Effectivity of flat descent for modules**, as an explicit isomorphism: for `S` flat over `R`,
base changing the descended module of a descent datum recovers `N`. -/
noncomputable def equivBaseChange : S ⊗[R] d.descended ≃ₗ[S] N :=
  LinearMap.tensorEqLocusEquiv S S (d.coaction.restrictScalars R) (TensorProduct.mk R S N 1) ≪≫ₗ
    d.eqSubmoduleEquiv

/-- `Module.Descent.Datum.equivBaseChange` on a pure tensor. -/
@[simp]
lemma equivBaseChange_tmul (s : S) (m : d.descended) :
    d.equivBaseChange (s ⊗ₜ[R] m) = s • (m : N) := by
  change counit R S N ((LinearMap.tensorEqLocus S S (d.coaction.restrictScalars R)
      (TensorProduct.mk R S N 1) (s ⊗ₜ[R] m) : S ⊗[R] N)) = s • (m : N)
  rw [LinearMap.tensorEqLocus_coe]
  rfl

/-- **Effectivity of flat descent for modules.** For `S` flat over `R`, the inclusion of the
module descended from a descent datum on an `S`-module `N` exhibits `N` as the base change of
that `R`-module along `R → S`. -/
theorem isBaseChange : IsBaseChange S d.descended.subtype :=
  IsBaseChange.of_equiv d.equivBaseChange (by simp)

/-- `N` is generated as an `S`-module by its descended `R`-submodule. In sheaf language this says
that a quasi-coherent module is generated, over a flat cover, by the sections that descend to the
base. -/
theorem span_descended_eq_top : Submodule.span S (d.descended : Set N) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x => ?_
  induction x using d.isBaseChange.inductionOn with
  | tmul m => exact Submodule.subset_span m.2
  | smul s n h => exact Submodule.smul_mem _ s h
  | add n₁ n₂ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂

end Flat

section FaithfullyFlat

variable [Module.FaithfullyFlat R S]

/-- Finite generation descends: if `N` is a finite `S`-module and `S` is faithfully flat over `R`,
the module descended from a descent datum on `N` is a finite `R`-module. -/
theorem finite_descended [Module.Finite S N] : Module.Finite R d.descended :=
  have : Module.Finite S (S ⊗[R] d.descended) := Module.Finite.equiv d.equivBaseChange.symm
  Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S

/-- Finite presentation descends: if `N` is a finitely presented `S`-module and `S` is faithfully
flat over `R`, the module descended from a descent datum on `N` is a finitely presented
`R`-module. -/
theorem finitePresentation_descended [Module.FinitePresentation S N] :
    Module.FinitePresentation R d.descended :=
  Module.FinitePresentation.of_isBaseChange_of_faithfullyFlat _ d.isBaseChange

/-- If `N` is a finite `S`-module carrying a descent datum and `S` is faithfully flat over `R`,
then `N` is generated as an `S`-module by finitely many elements of the descended `R`-module. In
sheaf language: a finitely generated quasi-coherent module over a flat cover is generated by
finitely many sections coming from the base. -/
theorem exists_fin_descended_span_eq_top [Module.Finite S N] :
    ∃ (n : ℕ) (g : Fin n → N), (∀ i, g i ∈ d.descended) ∧ Submodule.span S (Set.range g) = ⊤ := by
  have := d.finite_descended
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := d.descended)
  refine ⟨n, fun i => (s i : N), fun i => (s i).2, ?_⟩
  have h₁ : d.descended = Submodule.span R (Set.range fun i => (s i : N)) := by
    conv_lhs => rw [← Submodule.map_subtype_top d.descended]
    rw [← hs, Submodule.map_span]
    exact congrArg _ (Set.range_comp _ _).symm
  rw [← Submodule.span_span_of_tower R S, ← h₁]
  exact d.span_descended_eq_top

end FaithfullyFlat

section Morphism

variable {N' : Type*} [AddCommGroup N'] [Module R N'] [Module S N'] [IsScalarTower R S N']
variable (d' : Datum R S N') (f : N →ₗ[S] N')

/-- An `S`-linear map between modules carrying descent data is a *morphism of descent data* if it
is compatible with the two coactions, i.e. if it is a morphism of coalgebras over the comonad
induced by `R → S`. -/
def IsHom : Prop :=
  ∀ n : N, d'.coaction (f n) =
    AlgebraTensorModule.lTensor S S (f.restrictScalars R) (d.coaction n)

variable {d d' f}

/-- A morphism of descent data carries the descended module into the descended module. -/
lemma map_mem_descended (hf : d.IsHom d' f) {n : N} (hn : n ∈ d.descended) :
    f n ∈ d'.descended := by
  rw [Datum.mem_descended_iff, hf n, d.mem_descended_iff.1 hn]
  rfl

/-- The `R`-linear map between descended modules induced by a morphism of descent data. -/
noncomputable def mapDescended (hf : d.IsHom d' f) : d.descended →ₗ[R] d'.descended :=
  LinearMap.codRestrict _ ((f.restrictScalars R) ∘ₗ d.descended.subtype)
    fun n => map_mem_descended hf n.2

/-- `Module.Descent.Datum.mapDescended` is the restriction of the given map. -/
@[simp]
lemma coe_mapDescended (hf : d.IsHom d' f) (n : d.descended) :
    (mapDescended hf n : N') = f (n : N) := rfl

/-- **Injectivity descends.** The map of descended modules induced by an injective morphism of
descent data is injective. -/
theorem injective_mapDescended (hf : d.IsHom d' f) (hinj : Function.Injective f) :
    Function.Injective (mapDescended hf) :=
  fun _ _ h => Subtype.ext (hinj (congrArg Subtype.val h))

section Flat

variable [Module.Flat R S]

/-- Base changing `Module.Descent.Datum.mapDescended` recovers the original map, through the
identifications of `Module.Descent.Datum.equivBaseChange`. -/
lemma equivBaseChange_lTensor_mapDescended (hf : d.IsHom d' f) (x : S ⊗[R] d.descended) :
    d'.equivBaseChange (LinearMap.lTensor S (mapDescended hf) x) = f (d.equivBaseChange x) := by
  have h : (d'.equivBaseChange.toLinearMap.restrictScalars R) ∘ₗ
      LinearMap.lTensor S (mapDescended hf) =
      (f.restrictScalars R) ∘ₗ (d.equivBaseChange.toLinearMap.restrictScalars R) := by
    ext; simp
  simpa using congr($h x)

end Flat

section FaithfullyFlatMorphism

variable [Module.FaithfullyFlat R S]

/-- **Surjectivity descends.** If a morphism of descent data is surjective and `S` is faithfully
flat over `R`, then the induced map of descended modules is surjective.

Over an affine base this is the surjectivity of a quasi-coherent epimorphism on global sections:
the vanishing of the relevant first cohomology group. -/
theorem surjective_mapDescended (hf : d.IsHom d' f)
    (hsurj : Function.Surjective f) : Function.Surjective (mapDescended hf) := by
  rw [← Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S]
  intro w
  obtain ⟨x, hx⟩ := (hsurj.comp d.equivBaseChange.surjective) (d'.equivBaseChange w)
  exact ⟨x, d'.equivBaseChange.injective ((equivBaseChange_lTensor_mapDescended hf x).trans hx)⟩

end FaithfullyFlatMorphism

end Morphism

end Datum

section BaseChange

variable (R S) (M : Type*) [AddCommGroup M] [Module R M]

/-- The two base-changed coactions out of `S ⊗[R] (S ⊗[R] M)` agree after composing with
`s ⊗ₜ m ↦ s ⊗ₜ 1 ⊗ₜ m`. This is coassociativity of the canonical descent datum on a base
change. -/
lemma lTensor_mk_one_comp_lTensor_mk_one :
    AlgebraTensorModule.lTensor S S
        ((AlgebraTensorModule.lTensor S S (TensorProduct.mk R S M 1)).restrictScalars R) ∘ₗ
      AlgebraTensorModule.lTensor S S (TensorProduct.mk R S M 1) =
    AlgebraTensorModule.lTensor S S (TensorProduct.mk R S (S ⊗[R] M) 1) ∘ₗ
      AlgebraTensorModule.lTensor S S (TensorProduct.mk R S M 1) := by
  ext; simp

/-- The canonical descent datum on a base-changed module `S ⊗[R] M`, with coaction
`s ⊗ₜ m ↦ s ⊗ₜ 1 ⊗ₜ m`. Under the comonadic description of descent data this is the image of `M`
under the comparison functor. -/
noncomputable def baseChange : Datum R S (S ⊗[R] M) where
  coaction := AlgebraTensorModule.lTensor S S (TensorProduct.mk R S M 1)
  counit_coaction n := congr($(counit_comp_lTensor_mk_one R S M) n)
  coassoc n := congr($(lTensor_mk_one_comp_lTensor_mk_one R S M) n)

/-- The coaction of the canonical descent datum on a pure tensor. -/
@[simp]
lemma baseChange_coaction_tmul (s : S) (m : M) :
    (baseChange R S M).coaction (s ⊗ₜ[R] m) = s ⊗ₜ[R] ((1 : S) ⊗ₜ[R] m) := rfl

/-- The image of `M` in `S ⊗[R] M` lies in the module descended from the canonical datum. -/
lemma mk_one_mem_descended_baseChange (m : M) :
    (1 : S) ⊗ₜ[R] m ∈ (baseChange R S M).descended := by
  rw [Datum.mem_descended_iff, baseChange_coaction_tmul]

/-- The canonical `R`-linear map from `M` to the module descended from the canonical descent datum
on `S ⊗[R] M`. -/
noncomputable def toDescendedBaseChange : M →ₗ[R] (baseChange R S M).descended :=
  LinearMap.codRestrict _ (TensorProduct.mk R S M 1) (mk_one_mem_descended_baseChange R S M)

/-- `Module.Descent.toDescendedBaseChange` followed by the inclusion into `S ⊗[R] M`. -/
@[simp]
lemma coe_toDescendedBaseChange (m : M) :
    (toDescendedBaseChange R S M m : S ⊗[R] M) = (1 : S) ⊗ₜ[R] m := rfl

section Flat

variable [Module.Flat R S]

/-- Base changing `Module.Descent.toDescendedBaseChange` and then identifying the base change of
the descended module with `S ⊗[R] M` is the identity. -/
lemma equivBaseChange_lTensor_toDescendedBaseChange (x : S ⊗[R] M) :
    (baseChange R S M).equivBaseChange
      (LinearMap.lTensor S (toDescendedBaseChange R S M) x) = x := by
  have h : ((baseChange R S M).equivBaseChange.toLinearMap.restrictScalars R) ∘ₗ
      LinearMap.lTensor S (toDescendedBaseChange R S M) = LinearMap.id := by
    ext; simp [TensorProduct.smul_tmul']
  simpa using congr($h x)

end Flat

section FaithfullyFlat

variable [Module.FaithfullyFlat R S]

/-- For `S` faithfully flat over `R`, the canonical map from `M` to the module descended from the
canonical descent datum on `S ⊗[R] M` is bijective. -/
theorem bijective_toDescendedBaseChange :
    Function.Bijective (toDescendedBaseChange R S M) := by
  rw [← Module.FaithfullyFlat.lTensor_bijective_iff_bijective R S]
  have h : ((LinearMap.lTensor S (toDescendedBaseChange R S M)) :
      S ⊗[R] M → S ⊗[R] (baseChange R S M).descended) =
      (baseChange R S M).equivBaseChange.symm := by
    funext x
    exact ((baseChange R S M).equivBaseChange.symm_apply_eq.2
      (equivBaseChange_lTensor_toDescendedBaseChange R S M x).symm).symm
  rw [h]
  exact (baseChange R S M).equivBaseChange.symm.bijective

/-- For `S` faithfully flat over `R`, descent along `R → S` is inverse to base change: an
`R`-module `M` is isomorphic to the module descended from the canonical descent datum on
`S ⊗[R] M`. -/
noncomputable def descendedEquiv : M ≃ₗ[R] (baseChange R S M).descended :=
  LinearEquiv.ofBijective _ (bijective_toDescendedBaseChange R S M)

/-- `Module.Descent.descendedEquiv` followed by the inclusion into `S ⊗[R] M`. -/
@[simp]
lemma coe_descendedEquiv_apply (m : M) :
    (descendedEquiv R S M m : S ⊗[R] M) = (1 : S) ⊗ₜ[R] m := rfl

/-- **Exactness of the Amitsur complex**, in equalizer form: for `S` faithfully flat over `R`, the
submodule of `S ⊗[R] M` on which the two coactions into `S ⊗[R] (S ⊗[R] M)` agree is the image of
`M`. -/
theorem descended_baseChange :
    (baseChange R S M).descended = LinearMap.range (TensorProduct.mk R S M 1) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨m, hm⟩ := (bijective_toDescendedBaseChange R S M).surjective ⟨x, hx⟩
    exact ⟨m, congrArg Subtype.val hm⟩
  · rintro x ⟨m, rfl⟩
    exact mk_one_mem_descended_baseChange R S M m

/-- **Exactness of the Amitsur complex** `M → S ⊗[R] M → S ⊗[R] (S ⊗[R] M)`, for `S` faithfully
flat over `R`. The two maps out of `S ⊗[R] M` are `s ⊗ₜ m ↦ s ⊗ₜ 1 ⊗ₜ m` and `x ↦ 1 ⊗ₜ x`. -/
theorem exact_mk_one :
    Function.Exact (TensorProduct.mk R S M 1)
      ((AlgebraTensorModule.lTensor S S (TensorProduct.mk R S M 1)).restrictScalars R -
        TensorProduct.mk R S (S ⊗[R] M) 1) := by
  intro x
  rw [LinearMap.sub_apply, sub_eq_zero]
  exact (SetLike.ext_iff.1 (descended_baseChange R S M) x).trans LinearMap.mem_range

/-- **Exactness of the Amitsur complex** in the spelling `M → M ⊗[R] S → M ⊗[R] (S ⊗[R] S)`, with
the difference of the two coactions written using `Algebra.TensorProduct.includeLeftSubRight`.
For the module `M = R` this is `Algebra.IsEffective.of_faithfullyFlat`. -/
theorem exact_lTensor_includeLeftSubRight :
    Function.Exact ((TensorProduct.mk R M S).flip 1)
      (LinearMap.lTensor M (Algebra.TensorProduct.includeLeftSubRight R S)) := by
  refine (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := LinearEquiv.refl R M) (e₂ := TensorProduct.comm R M S)
    (e₃ := TensorProduct.comm R M (S ⊗[R] S) ≪≫ₗ TensorProduct.assoc R S S M)
    ?_ ?_).1 (exact_mk_one R S M)
  · ext m; simp
  · ext m s
    simp [Algebra.TensorProduct.includeLeftSubRight]

end FaithfullyFlat

end BaseChange

section Kernel

variable (S) {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
variable (g : M →ₗ[R] M')

/-- The canonical `R`-linear map from the kernel of `g` to the kernel of its base change along
`R → S`, given by `x ↦ 1 ⊗ₜ x`. -/
noncomputable def toKerLTensor :
    LinearMap.ker g →ₗ[R] LinearMap.ker (AlgebraTensorModule.lTensor S S g) where
  toFun x := ⟨(1 : S) ⊗ₜ[R] (x : M), by simp [LinearMap.mem_ker]⟩
  map_add' x y := Subtype.ext (by simp [TensorProduct.tmul_add])
  map_smul' r x := Subtype.ext (by simp [TensorProduct.tmul_smul])

/-- `Module.Descent.toKerLTensor` followed by the inclusion into `S ⊗[R] M`. -/
@[simp]
lemma coe_toKerLTensor (x : LinearMap.ker g) :
    (toKerLTensor S g x : S ⊗[R] M) = (1 : S) ⊗ₜ[R] (x : M) := rfl

/-- **Flat base change commutes with kernels.** For `S` flat over `R`, the kernel of the base
change of `g : M →ₗ[R] M'` is the base change of the kernel of `g`.

Over an affine base this says that the kernel of a map of quasi-coherent modules is again
quasi-coherent: its sections over a flat cover are the base change of its sections over the
base. -/
theorem isBaseChange_ker [Module.Flat R S] : IsBaseChange S (toKerLTensor S g) :=
  IsBaseChange.of_equiv (LinearMap.tensorKerEquiv S S g) fun x => Subtype.ext (by simp)

end Kernel

section Image

variable (R S) [Module.FaithfullyFlat R S]
variable {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

/-- Membership in the image of an `R`-linear map is detected by a faithfully flat base change: if
`1 ⊗ₜ m'` lies in the image of the base change of `f`, then `m'` lies in the image of `f`.

Over an affine base this is the ring-level content of surjectivity on global sections of a locally
surjective map of quasi-coherent modules: local liftability of a single section forces that
section to be globally a value. -/
theorem mem_range_of_one_tmul_mem_range (f : M →ₗ[R] M') {m' : M'}
    (h : (1 : S) ⊗ₜ[R] m' ∈ LinearMap.range (LinearMap.lTensor S f)) :
    m' ∈ LinearMap.range f := by
  obtain ⟨y, hy⟩ := h
  have key : LinearMap.lTensor S (LinearMap.range f).mkQ ((1 : S) ⊗ₜ[R] m') = 0 := by
    rw [← hy, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      show (LinearMap.range f).mkQ ∘ₗ f = 0 from
        LinearMap.ext fun x => (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩]
    simp
  rw [LinearMap.lTensor_tmul] at key
  exact (Submodule.Quotient.mk_eq_zero _).1
    ((Module.FaithfullyFlat.one_tmul_eq_zero_iff R (M' ⧸ LinearMap.range f) (A := S) _).1 key)

/-- **Surjectivity is detected by a faithfully flat base change**, in the form a locally surjective
map of quasi-coherent modules over an affine base is applied to: if every element of `M'` becomes a
value of the base change of `f` after tensoring with `S`, then `f` is surjective. -/
@[ega "IV 2.2.7" "partial"]
theorem surjective_of_forall_one_tmul_mem_range (f : M →ₗ[R] M')
    (h : ∀ m' : M', (1 : S) ⊗ₜ[R] m' ∈ LinearMap.range (LinearMap.lTensor S f)) :
    Function.Surjective f :=
  fun m' => mem_range_of_one_tmul_mem_range R S f (h m')

end Image

end Module.Descent
