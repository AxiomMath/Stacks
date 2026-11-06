module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.TensorProduct.Pi
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleColimits.EqualizerAlgebra

/-!
# Forming the equalizer algebra commutes with base change

Let `R` be a commutative ring, let `B` and `C` be finite étale `R`-algebras and let
`α, β : B ⟶ C` be two `R`-algebra maps. For an arbitrary `R`-algebra `S` there is a canonical
map `S ⊗[R] Eq(α, β) ⟶ Eq(α_S, β_S)` (`AlgHom.tensorEqualizer`), and it is an isomorphism when
`S` is flat over `R`. This file proves that it is an isomorphism for **every** `R`-algebra `S`.

This is the step that the proof of Stacks Tag 0BN9 omits ("we omit the verification that this is
compatible with base change"), and it is what the fourth assertion of that tag — exactness of the
base-change functor `FÉt_X ⥤ FÉt_{X'}` — needs on top of the right exactness proved in
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/FiniteEtaleColimits/EqualizerAlgebra.lean`: over an
affine base the coequalizer of two finite étale covers is the spectrum of the equalizer algebra, so
base change preserves it exactly when forming the equalizer algebra commutes with base change.

The proof follows the source's reduction, run for the stronger statement. Rather than bijectivity
of the comparison map, what is carried through the reduction is **universal exactness** of the
three-term sequence `Eq(α, β) ⟶ B ⟶ C` whose second map is `α - β`
(`Stacks.FundamentalGroup.IsUnivExact`): it is a statement about linear maps only, so it descends
along a faithfully flat base change and is local on the base without any bookkeeping about algebra
structures, and it is equivalent to bijectivity of `AlgHom.tensorEqualizer` for every `S`
(`Stacks.FundamentalGroup.bijective_tensorEqualizer_of_isStableEqualizer`). The three reductions
are then exactly those of `StacksFrontier/AlgebraicGeometry/FundamentalGroup/FiniteEtaleColimits/EqualizerAlgebra.lean`: localize so that `B` and `C` have constant
rank, pass to a faithfully flat finite étale extension over which both split, and localize again
at the refined idempotents of the two maps, after which both are induced by maps of index types.
In that last case the equalizer is the algebra of functions on the coequalizer `IndexCoeq σ τ` of
the index maps, a section of `ι ⟶ IndexCoeq σ τ` splits the inclusion, and an element of `W ⊗ B`
is killed by `α - β` exactly when its coordinates are constant on the fibres of
`ι ⟶ IndexCoeq σ τ` — which is where the splitting reproduces it.

## Main definitions

* `Stacks.FundamentalGroup.IsUnivExact` — universal exactness of `0 ⟶ A ⟶ B ⟶ C`: for every
  module `W` the sequence stays exact and its first map stays injective after tensoring with `W`.
* `Stacks.FundamentalGroup.IsStableEqualizer` — universal exactness of the equalizer sequence of
  two algebra maps.
* `Stacks.FundamentalGroup.baseChangeCommIso` — the comparison isomorphism
  `T ⊗ (W ⊗ X) ≅ (T ⊗ W) ⊗_T (T ⊗ X)`.

## Main results

* `Stacks.FundamentalGroup.IsUnivExact.of_faithfullyFlat` and
  `Stacks.FundamentalGroup.IsUnivExact.of_localized_span` — universal exactness descends along a
  faithfully flat base change, and is local on the base.
* `Stacks.FundamentalGroup.isUnivExact_piPrecompAlgHom` — the index case: the equalizer sequence
  of two precomposition maps `(ι → R) ⇉ (κ → R)` is universally exact.
* `Stacks.FundamentalGroup.isStableEqualizer_pi`,
  `Stacks.FundamentalGroup.isStableEqualizer_of_isFiniteSplit`,
  `Stacks.FundamentalGroup.isStableEqualizer_of_faithfullyFlat` and
  `Stacks.FundamentalGroup.isStableEqualizer_of_rankAtStalk` — the same for two maps of split
  algebras, of finite split algebras, of algebras split after a faithfully flat base change, and
  of finite étale algebras of constant rank.
* `Stacks.FundamentalGroup.isStableEqualizer` — **the equalizer sequence of two maps of finite
  étale algebras is universally exact**, with no further hypotheses.
* `RingHom.FiniteEtale.hasStableEqualizers` — **forming the equalizer algebra commutes with base
  change**, in the form Mathlib's `RingHom.HasStableEqualizers` consumes.
* `Stacks.FundamentalGroup.preservesFiniteLimits_pushout_finiteEtale` and
  `Stacks.FundamentalGroup.preservesFiniteColimits_op_pushout_finiteEtale` — **the affine form of
  the fourth assertion of Stacks Tag 0BN9**: base change along an arbitrary ring homomorphism is
  exact on finite étale algebras, equivalently right exact on finite étale covers of an affine
  scheme.

## Implementation notes

No `@[stacks]` attribute appears here. Tag 0BN9 has four assertions, of which this file completes
only the affine case of the fourth, and the audit scanner keys on the bare four-character tag, so
an attribute on a partial result reports the whole tag formalized.

The statement of the index case is made for an arbitrary module `W` rather than an arbitrary
algebra `S`, which is what makes both descent steps cheap: the faithfully flat descent and the
localization step both compare `W ⊗_R X` with `(T ⊗_R W) ⊗_T (T ⊗_R X)`, and that one comparison
(`Stacks.FundamentalGroup.baseChangeCommIso`) serves both. Stating the reduction for algebras
instead would require identifying `AlgHom.tensorEqualizer` for the tower `R ⟶ T ⟶ S` with its
two factors at every step.

## References

* [Stacks Project, Tag 0BN9](https://stacks.math.columbia.edu/tag/0BN9)
-/

@[expose] public section

open TensorProduct

universe u

namespace Stacks.FundamentalGroup

/-! ### Universally exact short sequences -/

section UnivExact

variable {R : Type u} [CommRing R] {A B C : Type u}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B] [Module R C]

/-- A pair of maps `f : A ⟶ B`, `g : B ⟶ C` of `R`-modules is **universally exact** if for every
`R`-module `W` the sequence `W ⊗ A ⟶ W ⊗ B ⟶ W ⊗ C` is exact and its first map is injective;
that is, if `0 ⟶ A ⟶ B ⟶ C` stays exact under every base change. -/
def IsUnivExact (f : A →ₗ[R] B) (g : B →ₗ[R] C) : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module R W],
    Function.Injective (LinearMap.lTensor W f) ∧
      Function.Exact (LinearMap.lTensor W f) (LinearMap.lTensor W g)

variable {A' B' C' : Type u} [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
  [Module R A'] [Module R B'] [Module R C']

/-- Universal exactness is transported along an isomorphism of sequences. -/
theorem IsUnivExact.congr {f : A →ₗ[R] B} {g : B →ₗ[R] C} {f' : A' →ₗ[R] B'} {g' : B' →ₗ[R] C'}
    (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B') (eC : C ≃ₗ[R] C')
    (hf : f' ∘ₗ (eA : A →ₗ[R] A') = (eB : B →ₗ[R] B') ∘ₗ f)
    (hg : g' ∘ₗ (eB : B →ₗ[R] B') = (eC : C →ₗ[R] C') ∘ₗ g)
    (h : IsUnivExact f g) : IsUnivExact f' g' := by
  intro W _ _
  have hfW : LinearMap.lTensor W f' ∘ₗ (LinearMap.lTensor W (eA : A →ₗ[R] A'))
      = LinearMap.lTensor W (eB : B →ₗ[R] B') ∘ₗ LinearMap.lTensor W f := by
    rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, hf]
  have hgW : LinearMap.lTensor W g' ∘ₗ (LinearMap.lTensor W (eB : B →ₗ[R] B'))
      = LinearMap.lTensor W (eC : C →ₗ[R] C') ∘ₗ LinearMap.lTensor W g := by
    rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, hg]
  refine ⟨?_, (Function.Exact.iff_of_ladder_linearEquiv (e₁ := eA.lTensor W)
    (e₂ := eB.lTensor W) (e₃ := eC.lTensor W) hfW hgW).mpr (h W).2⟩
  have hinj : Function.Injective
      ⇑(LinearMap.lTensor W f' ∘ₗ LinearMap.lTensor W (eA : A →ₗ[R] A')) := by
    rw [hfW, LinearMap.coe_comp]
    exact (eB.lTensor W).injective.comp (h W).1
  rw [LinearMap.coe_comp] at hinj
  exact (Function.Injective.of_comp_iff' _ (eA.lTensor W).bijective).mp hinj

end UnivExact

/-! ### Descent of universal exactness -/

section Descent

/-- The comparison isomorphism `T ⊗ (W ⊗ X) ≅ (T ⊗ W) ⊗_T (T ⊗ X)` between the base change to
`T` of a tensor product over `R` and the corresponding tensor product over `T`. -/
def baseChangeCommIso (R T W X : Type u) [CommRing R] [CommRing T] [Algebra R T]
    [AddCommGroup W] [Module R W] [AddCommGroup X] [Module R X] :
    T ⊗[R] (W ⊗[R] X) ≃ₗ[R] (T ⊗[R] W) ⊗[T] (T ⊗[R] X) :=
  (TensorProduct.assoc R T W X).symm.trans
    ((AlgebraTensorModule.cancelBaseChange R T T (T ⊗[R] W) X).restrictScalars R).symm

/-- `baseChangeCommIso` sends `t ⊗ (w ⊗ x)` to `(t ⊗ w) ⊗ (1 ⊗ x)`. -/
@[simp]
theorem baseChangeCommIso_tmul (R T W X : Type u) [CommRing R] [CommRing T] [Algebra R T]
    [AddCommGroup W] [Module R W] [AddCommGroup X] [Module R X] (t : T) (w : W) (x : X) :
    baseChangeCommIso R T W X (t ⊗ₜ (w ⊗ₜ x)) = (t ⊗ₜ w) ⊗ₜ ((1 : T) ⊗ₜ x) := rfl

variable {R : Type u} [CommRing R] (T : Type u) [CommRing T] [Algebra R T]
  (W : Type u) [AddCommGroup W] [Module R W]
  {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C]

/-- **Naturality of the base-change comparison isomorphism.** Tensoring a map `f : A ⟶ B` first
with `W` over `R` and then with `T`, or first with `T` and then with `T ⊗ W` over `T`, agree. -/
theorem baseChangeCommIso_naturality (f : A →ₗ[R] B) :
    ((LinearMap.lTensor (T ⊗[R] W) (f.baseChange T)).restrictScalars R) ∘ₗ
        (baseChangeCommIso R T W A).toLinearMap
      = (baseChangeCommIso R T W B).toLinearMap ∘ₗ
        LinearMap.lTensor T (LinearMap.lTensor W f) := by
  ext t w a
  simp

/-- The base-changed sequence being universally exact over `T` makes the `T`-base change of each
`W`-tensored sequence injective and exact. -/
theorem injective_and_exact_lTensor_of_isUnivExact_baseChange {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (h : IsUnivExact (f.baseChange T) (g.baseChange T)) :
    Function.Injective (LinearMap.lTensor T (LinearMap.lTensor W f)) ∧
      Function.Exact (LinearMap.lTensor T (LinearMap.lTensor W f))
        (LinearMap.lTensor T (LinearMap.lTensor W g)) := by
  obtain ⟨h1, h2⟩ := h (T ⊗[R] W)
  have hf := baseChangeCommIso_naturality T W f
  have hg := baseChangeCommIso_naturality T W g
  refine ⟨?_, (Function.Exact.iff_of_ladder_linearEquiv (e₁ := baseChangeCommIso R T W A)
    (e₂ := baseChangeCommIso R T W B) (e₃ := baseChangeCommIso R T W C) hf hg).mp h2⟩
  have hinj : Function.Injective
      ⇑(((LinearMap.lTensor (T ⊗[R] W) (f.baseChange T)).restrictScalars R) ∘ₗ
        (baseChangeCommIso R T W A).toLinearMap) := by
    rw [LinearMap.coe_comp]
    exact h1.comp (baseChangeCommIso R T W A).injective
  rw [hf, LinearMap.coe_comp] at hinj
  exact (Function.Injective.of_comp_iff (baseChangeCommIso R T W B).injective _).mp hinj

variable {T W}

/-- **Universal exactness descends along a faithfully flat base change.** -/
theorem IsUnivExact.of_faithfullyFlat [Module.FaithfullyFlat R T] {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (h : IsUnivExact (f.baseChange T) (g.baseChange T)) : IsUnivExact f g := by
  intro W _ _
  obtain ⟨h1, h2⟩ := injective_and_exact_lTensor_of_isUnivExact_baseChange T W h
  exact ⟨(Module.FaithfullyFlat.lTensor_injective_iff_injective R T _).mp h1,
    (Module.FaithfullyFlat.lTensor_exact_iff_exact R T _ _).mp h2⟩

/-- The localized map of a linear map, for the localization of a module realized as a base
change, is the base change of the map. -/
theorem isLocalizedModule_map_eq_lTensor (r : R) [IsLocalization.Away r T] (F : A →ₗ[R] B) :
    IsLocalizedModule.map (Submonoid.powers r)
        (TensorProduct.mk R T A 1) (TensorProduct.mk R T B 1) F
      = LinearMap.lTensor T F := by
  refine IsLocalizedModule.ext (Submonoid.powers r) (TensorProduct.mk R T A 1)
    (fun x ↦ IsLocalizedModule.map_units (TensorProduct.mk R T B 1) x) ?_
  rw [IsLocalizedModule.map_comp]
  ext a
  simp

/-- **Universal exactness is local on the base.** If the sequence stays universally exact after
localizing `R` away from each element of a spanning set, it is universally exact. -/
theorem IsUnivExact.of_localized_span (s : Set R) (spn : Ideal.span s = ⊤)
    {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (h : ∀ r : s, IsUnivExact (f.baseChange (Localization.Away (r : R)))
      (g.baseChange (Localization.Away (r : R)))) : IsUnivExact f g := by
  intro W _ _
  have key : ∀ r : s,
      Function.Injective
          (LinearMap.lTensor (Localization.Away (r : R)) (LinearMap.lTensor W f)) ∧
        Function.Exact (LinearMap.lTensor (Localization.Away (r : R)) (LinearMap.lTensor W f))
          (LinearMap.lTensor (Localization.Away (r : R)) (LinearMap.lTensor W g)) :=
    fun r ↦ injective_and_exact_lTensor_of_isUnivExact_baseChange _ W (h r)
  constructor
  · refine injective_of_isLocalized_span s spn
      (fun r : s ↦ Localization.Away (r : R) ⊗[R] (W ⊗[R] A))
      (fun r : s ↦ TensorProduct.mk R (Localization.Away (r : R)) (W ⊗[R] A) 1)
      (fun r : s ↦ Localization.Away (r : R) ⊗[R] (W ⊗[R] B))
      (fun r : s ↦ TensorProduct.mk R (Localization.Away (r : R)) (W ⊗[R] B) 1)
      _ (fun r ↦ ?_)
    rw [isLocalizedModule_map_eq_lTensor (r : R)]
    exact (key r).1
  · refine exact_of_isLocalized_span s spn
      (fun r : s ↦ Localization.Away (r : R) ⊗[R] (W ⊗[R] A))
      (fun r : s ↦ TensorProduct.mk R (Localization.Away (r : R)) (W ⊗[R] A) 1)
      (fun r : s ↦ Localization.Away (r : R) ⊗[R] (W ⊗[R] B))
      (fun r : s ↦ TensorProduct.mk R (Localization.Away (r : R)) (W ⊗[R] B) 1)
      (fun r : s ↦ Localization.Away (r : R) ⊗[R] (W ⊗[R] C))
      (fun r : s ↦ TensorProduct.mk R (Localization.Away (r : R)) (W ⊗[R] C) 1)
      _ _ (fun r ↦ ?_)
    rw [isLocalizedModule_map_eq_lTensor (r : R), isLocalizedModule_map_eq_lTensor (r : R)]
    exact (key r).2

end Descent

/-! ### The split case: two maps induced by maps of index types -/

section Index

/-- The coordinates of the base change of a precomposition map are the corresponding coordinates
of the argument. -/
theorem piScalarRight_lTensor_piPrecompAlgHom {R : Type u} [CommRing R] {ι ι' : Type u}
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (W : Type u) [AddCommGroup W] [Module R W]
    (ρ : ι' → ι) (z : W ⊗[R] (ι → R)) (j : ι') :
    TensorProduct.piScalarRight R R W ι'
        (LinearMap.lTensor W (piPrecompAlgHom R ρ).toLinearMap z) j
      = TensorProduct.piScalarRight R R W ι z (ρ j) := by
  induction z with
  | tmul w x => simp
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply]
    rw [hx, hy]

variable {R : Type u} [CommRing R] {ι κ : Type u} (σ τ : κ → ι)

/-- A family on the index type which is unchanged by `σ` and `τ` takes equal values at any two
indices with the same image in the coequalizer of the index types. -/
theorem eq_of_toIndexCoeq_eq {β : Type*} (x : ι → β) (hx : ∀ j, x (σ j) = x (τ j))
    {i i' : ι} (h : toIndexCoeq σ τ i = toIndexCoeq σ τ i') : x i = x i' := by
  simpa using congrArg (indexCoeqLift x hx) h

/-- **The equalizer sequence of two index-induced maps of split algebras is universally exact.**
For `σ, τ : κ → ι` with `ι` and `κ` finite, the inclusion of the equalizer of the two
precomposition maps `(ι → R) ⇉ (κ → R)` into `ι → R` stays injective, with image the kernel of
the difference, after tensoring with an arbitrary `R`-module.

The equalizer is the algebra of functions on the coequalizer `IndexCoeq σ τ` of the index maps
(`Stacks.FundamentalGroup.indexCoeqPiAlgEquiv`); choosing a set-theoretic section of
`ι ⟶ IndexCoeq σ τ` splits the inclusion, and an element of the tensor product lies in the
kernel of the difference exactly when its coordinates are constant on the fibres of
`ι ⟶ IndexCoeq σ τ`, in which case the splitting reproduces it. -/
theorem isUnivExact_piPrecompAlgHom [Finite ι] [Finite κ] :
    IsUnivExact
      (AlgHom.equalizer (piPrecompAlgHom R σ) (piPrecompAlgHom R τ)).val.toLinearMap
      ((piPrecompAlgHom R σ).toLinearMap - (piPrecompAlgHom R τ).toLinearMap) := by
  classical
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  set A := AlgHom.equalizer (piPrecompAlgHom R σ) (piPrecompAlgHom R τ)
  have hsurj : Function.Surjective (toIndexCoeq σ τ) := fun t ↦ Quot.exists_rep t
  set sc := Function.surjInv hsurj
  have hscπ : ∀ t, toIndexCoeq σ τ (sc t) = t := Function.surjInv_eq hsurj
  set ρ : (ι → R) →ₗ[R] A := (indexCoeqPiAlgEquiv R σ τ).toLinearMap ∘ₗ
    (piPrecompAlgHom R sc).toLinearMap
  have hcoe : ∀ (x : ι → R) (i : ι), ((ρ x : A) : ι → R) i = x (sc (toIndexCoeq σ τ i)) :=
    fun x i ↦ rfl
  have hmem : ∀ a : A, ∀ j, (a : ι → R) (σ j) = (a : ι → R) (τ j) :=
    fun a ↦ (mem_equalizer_piPrecompAlgHom R σ τ (a : ι → R)).mp a.2
  have hretr : ρ ∘ₗ A.val.toLinearMap = LinearMap.id := by
    refine LinearMap.ext fun a ↦ Subtype.ext (funext fun i ↦ ?_)
    exact (hcoe _ i).trans (eq_of_toIndexCoeq_eq σ τ (a : ι → R) (hmem a) (hscπ _))
  have hzero : ((piPrecompAlgHom R σ).toLinearMap - (piPrecompAlgHom R τ).toLinearMap) ∘ₗ
      A.val.toLinearMap = 0 := by
    refine LinearMap.ext fun a ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.zero_apply,
      AlgHom.toLinearMap_apply, Subalgebra.coe_val, sub_eq_zero]
    exact (AlgHom.mem_equalizer _ _ _).mp a.2
  have hcomp : A.val.toLinearMap ∘ₗ ρ
      = (piPrecompAlgHom R (fun i : ι ↦ sc (toIndexCoeq σ τ i))).toLinearMap :=
    LinearMap.ext fun x ↦ funext fun i ↦ hcoe x i
  intro W _ _
  refine ⟨Function.LeftInverse.injective (g := LinearMap.lTensor W ρ) fun z ↦ ?_,
    fun z ↦ ⟨fun hz ↦ ?_, ?_⟩⟩
  · rw [← LinearMap.lTensor_comp_apply, hretr, LinearMap.lTensor_id_apply]
  · rw [LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero] at hz
    have hcoord : ∀ j, TensorProduct.piScalarRight R R W ι z (σ j)
        = TensorProduct.piScalarRight R R W ι z (τ j) := fun j ↦ by
      rw [← piScalarRight_lTensor_piPrecompAlgHom W σ z j,
        ← piScalarRight_lTensor_piPrecompAlgHom W τ z j, hz]
    refine ⟨LinearMap.lTensor W ρ z,
      (TensorProduct.piScalarRight R R W ι).injective (funext fun i ↦ ?_)⟩
    rw [← LinearMap.lTensor_comp_apply, hcomp, piScalarRight_lTensor_piPrecompAlgHom W _ z i]
    exact eq_of_toIndexCoeq_eq σ τ (TensorProduct.piScalarRight R R W ι z) hcoord
      (hscπ (toIndexCoeq σ τ i))
  · rintro ⟨a, rfl⟩
    rw [← LinearMap.lTensor_comp_apply, hzero, LinearMap.lTensor_zero, LinearMap.zero_apply]

end Index

/-! ### Stability of the equalizer algebra under base change -/

section StableEqualizer

variable {R : Type u} [CommRing R] {B C : Type u} [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C]

/-- The equalizer of two `R`-algebra maps `α, β : B ⟶ C` is **stable under base change** if the
sequence `Eq(α, β) ⟶ B ⟶ C`, whose second map is the difference of `α` and `β`, is universally
exact; equivalently (`Stacks.FundamentalGroup.bijective_tensorEqualizer_of_isStableEqualizer`)
if the canonical map `S ⊗ Eq(α, β) ⟶ Eq(α_S, β_S)` is bijective for every `R`-algebra `S`. -/
def IsStableEqualizer (α β : B →ₐ[R] C) : Prop :=
  IsUnivExact (AlgHom.equalizer α β).val.toLinearMap (α.toLinearMap - β.toLinearMap)

/-- The base change of an algebra map along `R ⟶ S` is the tensor product of linear maps. -/
theorem toLinearMap_tensorProduct_map_id (S : Type u) [CommRing S] [Algebra R S]
    (φ : B →ₐ[R] C) :
    (Algebra.TensorProduct.map (AlgHom.id R S) φ).toLinearMap
      = LinearMap.lTensor S φ.toLinearMap := by
  ext s b
  simp

/-- **Base change of the equalizer algebra is an isomorphism.** If the equalizer sequence of
`α` and `β` is universally exact, then for every `R`-algebra `S` the canonical map
`S ⊗ Eq(α, β) ⟶ Eq(α_S, β_S)` is bijective. -/
theorem bijective_tensorEqualizer_of_isStableEqualizer {α β : B →ₐ[R] C}
    (h : IsStableEqualizer α β) (S : Type u) [CommRing S] [Algebra R S] :
    Function.Bijective (AlgHom.tensorEqualizer R S α β) := by
  obtain ⟨h1, h2⟩ := h S
  have hval : ∀ x : S ⊗[R] (AlgHom.equalizer α β),
      ((AlgHom.tensorEqualizer R S α β x : _) : S ⊗[R] B)
        = LinearMap.lTensor S (AlgHom.equalizer α β).val.toLinearMap x := by
    intro x
    rw [AlgHom.coe_tensorEqualizer]
    exact DFunLike.congr_fun (toLinearMap_tensorProduct_map_id S (AlgHom.equalizer α β).val) x
  constructor
  · intro x y hxy
    refine h1 ?_
    rw [← hval, ← hval]
    exact congrArg _ hxy
  · intro y
    have hy : LinearMap.lTensor S (α.toLinearMap - β.toLinearMap) (y : S ⊗[R] B) = 0 := by
      rw [LinearMap.lTensor_sub]
      simp only [LinearMap.sub_apply, sub_eq_zero]
      rw [← toLinearMap_tensorProduct_map_id, ← toLinearMap_tensorProduct_map_id]
      exact (AlgHom.mem_equalizer _ _ _).mp y.2
    obtain ⟨x, hx⟩ := (h2 _).mp hy
    exact ⟨x, Subtype.ext ((hval x).trans hx)⟩

variable {B' C' : Type u} [CommRing B'] [CommRing C'] [Algebra R B'] [Algebra R C']

/-- Stability of the equalizer under base change is transported along algebra equivalences of the
source and the target. -/
theorem IsStableEqualizer.congr (e₁ : B ≃ₐ[R] B') (e₂ : C ≃ₐ[R] C') (α β : B →ₐ[R] C)
    (h : IsStableEqualizer α β) :
    IsStableEqualizer (e₂.toAlgHom.comp (α.comp e₁.symm.toAlgHom))
      (e₂.toAlgHom.comp (β.comp e₁.symm.toAlgHom)) := by
  refine IsUnivExact.congr
    (((Subalgebra.equivMapOfInjective _ e₁.toAlgHom e₁.injective).trans
      (Subalgebra.equivOfEq _ _ (map_equalizer_eq e₁ e₂ α β))).toLinearEquiv)
    e₁.toLinearEquiv e₂.toLinearEquiv ?_ ?_ h
  · exact LinearMap.ext fun _ ↦ rfl
  · refine LinearMap.ext fun b ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
      AlgEquiv.toLinearMap_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.symm_apply_apply, map_sub]

variable (T : Type u) [CommRing T] [Algebra R T]

/-- Over a flat base change, universal exactness of the base-changed equalizer sequence is the
stability of the equalizer of the base-changed maps: the two agree because base change along a
flat algebra already computes the equalizer (`AlgHom.tensorEqualizerEquiv`). -/
theorem isUnivExact_baseChange_of_isStableEqualizer [Module.Flat R T] {α β : B →ₐ[R] C}
    (h : IsStableEqualizer (Algebra.TensorProduct.map (AlgHom.id T T) α)
      (Algebra.TensorProduct.map (AlgHom.id T T) β)) :
    IsUnivExact ((AlgHom.equalizer α β).val.toLinearMap.baseChange T)
      ((α.toLinearMap - β.toLinearMap).baseChange T) := by
  have hmap : ∀ {B' C' : Type u} [CommRing B'] [CommRing C'] [Algebra R B'] [Algebra R C']
      (φ : B' →ₐ[R] C'), (Algebra.TensorProduct.map (AlgHom.id T T) φ).toLinearMap
        = φ.toLinearMap.baseChange T := by
    intro B' C' _ _ _ _ φ
    ext t
    simp
  have key : ∀ y : T ⊗[R] (AlgHom.equalizer α β),
      ((AlgHom.tensorEqualizerEquiv T T α β y : _) : T ⊗[R] B)
        = (AlgHom.equalizer α β).val.toLinearMap.baseChange T y := by
    intro y
    rw [AlgHom.tensorEqualizerEquiv_apply, AlgHom.coe_tensorEqualizer]
    exact DFunLike.congr_fun (hmap (AlgHom.equalizer α β).val) y
  refine IsUnivExact.congr (R := T) (AlgHom.tensorEqualizerEquiv T T α β).toLinearEquiv.symm
    (LinearEquiv.refl T (T ⊗[R] B)) (LinearEquiv.refl T (T ⊗[R] C)) ?_ ?_ h
  · refine LinearMap.ext fun z ↦ ?_
    have hz : (AlgHom.tensorEqualizerEquiv T T α β).toLinearEquiv.symm z
        = (AlgHom.tensorEqualizerEquiv T T α β).symm z := rfl
    have hk := key ((AlgHom.tensorEqualizerEquiv T T α β).symm z)
    rw [AlgEquiv.apply_symm_apply] at hk
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.refl_apply, hz]
    exact hk.symm
  · refine LinearMap.ext fun z ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.refl_apply, LinearEquiv.coe_coe,
      LinearMap.sub_apply]
    rw [hmap α, hmap β]
    induction z with
    | tmul t b => simp
    | add x y hx hy => simp only [map_add, hx, hy, add_sub_add_comm]

end StableEqualizer

/-! ### Split algebras -/

section Split

variable {T : Type u} [CommRing T] {ι κ : Type u} [DecidableEq ι] [Fintype κ] [Finite ι]

/-- **The two idempotents selected by `s` become `1` in the localization away from the refined
idempotent of `s`.** The refined idempotent is the product over `j` of the pair idempotents it
selects, so it becomes `1` only if every factor does; and a product of two idempotents equal
to `1` forces each of them to be `1`. -/
theorem algebraMap_piIdem_selected (α β : (ι → T) →ₐ[T] (κ → T)) (s : κ → ι × ι)
    (T' : Type u) [CommRing T'] [Algebra T T']
    [IsLocalization.Away (piRefineIdem α β s) T'] (j : κ) :
    algebraMap T T' (piIdem α j (s j).1) = 1 ∧ algebraMap T T' (piIdem β j (s j).2) = 1 := by
  classical
  cases nonempty_fintype ι
  have h1 : algebraMap T T' (piRefineIdem α β s) = 1 :=
    algebraMap_eq_one_of_isIdempotentElem (isIdempotentElem_piRefineIdem α β s) T'
  have h2 : algebraMap T T' (piIdem α j (s j).1) * algebraMap T T' (piIdem β j (s j).2) = 1 := by
    have h := congrArg (algebraMap T T') (piRefineIdem_mul_piPairIdem_self α β s j)
    rw [map_mul, h1, one_mul] at h
    rwa [← map_mul]
  obtain ⟨ha, hb⟩ := IsUnit.mul_iff.mp (h2 ▸ isUnit_one)
  exact ⟨(IsIdempotentElem.iff_eq_one_of_isUnit ha).mp
      (((completeOrthogonalIdempotents_piIdem α j).idem _).map (algebraMap T T')),
    (IsIdempotentElem.iff_eq_one_of_isUnit hb).mp
      (((completeOrthogonalIdempotents_piIdem β j).idem _).map (algebraMap T T'))⟩

/-- An idempotent of a complete orthogonal family other than the selected one becomes `0` once the
selected one becomes `1`. -/
private theorem algebraMap_piIdem_eq_zero_of_ne {a b : Type u} [DecidableEq a] [Finite a]
    (γ : (a → T) →ₐ[T] (b → T))
    (T' : Type u) [CommRing T'] [Algebra T T'] (j : b) {i₀ i : a} (hi : i ≠ i₀)
    (h : algebraMap T T' (piIdem γ j i₀) = 1) : algebraMap T T' (piIdem γ j i) = 0 := by
  classical
  cases nonempty_fintype a
  rw [← mul_one (algebraMap T T' (piIdem γ j i)), ← h, ← map_mul,
    (completeOrthogonalIdempotents_piIdem γ j).ortho hi, map_zero]

/-- If the idempotent of `γ` selecting `i₀` becomes `1`, then `γ y j` becomes `y i₀`. -/
private theorem algebraMap_apply_of_piIdem_eq_one {a b : Type u} [DecidableEq a] [Finite a]
    (γ : (a → T) →ₐ[T] (b → T))
    (T' : Type u) [CommRing T'] [Algebra T T'] (j : b) (i₀ : a) (y : a → T)
    (h : algebraMap T T' (piIdem γ j i₀) = 1) :
    algebraMap T T' (γ y j) = algebraMap T T' (y i₀) := by
  classical
  cases nonempty_fintype a
  rw [apply_eq_sum_piIdem γ y j, map_sum]
  refine (Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ _) fun i _ hi ↦ ?_).trans ?_
  · rw [map_mul, algebraMap_piIdem_eq_zero_of_ne γ T' j hi h, zero_mul]
  · rw [map_mul, h, one_mul]

/-- In the localization away from the refined idempotent of `s`, every idempotent of `α` other
than the one selected by `s` becomes `0`. -/
theorem algebraMap_piIdem_fst_eq_zero (α β : (ι → T) →ₐ[T] (κ → T)) (s : κ → ι × ι)
    (T' : Type u) [CommRing T'] [Algebra T T']
    [IsLocalization.Away (piRefineIdem α β s) T'] (j : κ) {i : ι} (hi : i ≠ (s j).1) :
    algebraMap T T' (piIdem α j i) = 0 :=
  algebraMap_piIdem_eq_zero_of_ne α T' j hi (algebraMap_piIdem_selected α β s T' j).1

/-- In the localization away from the refined idempotent of `s`, every idempotent of `β` other
than the one selected by `s` becomes `0`. -/
theorem algebraMap_piIdem_snd_eq_zero (α β : (ι → T) →ₐ[T] (κ → T)) (s : κ → ι × ι)
    (T' : Type u) [CommRing T'] [Algebra T T']
    [IsLocalization.Away (piRefineIdem α β s) T'] (j : κ) {i : ι} (hi : i ≠ (s j).2) :
    algebraMap T T' (piIdem β j i) = 0 :=
  algebraMap_piIdem_eq_zero_of_ne β T' j hi (algebraMap_piIdem_selected α β s T' j).2

/-- In the localization away from the refined idempotent of `s`, the maps `α` and `β` are the
precomposition maps of the index maps `j ↦ (s j).1` and `j ↦ (s j).2`. -/
theorem algebraMap_apply_eq (α β : (ι → T) →ₐ[T] (κ → T)) (s : κ → ι × ι)
    (T' : Type u) [CommRing T'] [Algebra T T']
    [IsLocalization.Away (piRefineIdem α β s) T'] (y : ι → T) (j : κ) :
    algebraMap T T' (α y j) = algebraMap T T' (y (s j).1) ∧
      algebraMap T T' (β y j) = algebraMap T T' (y (s j).2) := by
  exact ⟨algebraMap_apply_of_piIdem_eq_one α T' j _ y (algebraMap_piIdem_selected α β s T' j).1,
    algebraMap_apply_of_piIdem_eq_one β T' j _ y (algebraMap_piIdem_selected α β s T' j).2⟩

omit [Finite ι] in
/-- A `T`-algebra map between finite products of copies of `T` whose reduction to a `T`-algebra
`T'` is the precomposition map of an index map is, after base change to `T'`, that precomposition
map read through the isomorphism `T' ⊗ (ι → T) ≅ (ι → T')`. -/
theorem tensorProduct_map_eq_piPrecompAlgHom [Fintype ι] [DecidableEq κ] (T' : Type u)
    [CommRing T'] [Algebra T T'] (ρ : κ → ι) (φ : (ι → T) →ₐ[T] (κ → T))
    (hφ : ∀ (y : ι → T) (j : κ), algebraMap T T' (φ y j) = algebraMap T T' (y (ρ j))) :
    (Algebra.TensorProduct.piScalarRight T T' T' κ).symm.toAlgHom.comp
        ((piPrecompAlgHom T' ρ).comp
          (Algebra.TensorProduct.piScalarRight T T' T' ι).toAlgHom)
      = Algebra.TensorProduct.map (AlgHom.id T' T') φ := by
  refine AlgHom.ext fun x ↦ (Algebra.TensorProduct.piScalarRight T T' T' κ).injective ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply]
  induction x with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul t y =>
    refine funext fun j ↦ ?_
    simp only [piPrecompAlgHom_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
      Algebra.TensorProduct.piScalarRight_tmul_apply]
    rw [Algebra.smul_def, Algebra.smul_def, hφ y j]

omit [DecidableEq ι] [Fintype κ] in
/-- **The split case of stability of the equalizer under base change.** For two `T`-algebra maps
between finite products of copies of `T`, the equalizer sequence is universally exact.

The refined idempotents of `α` and `β` span `T`
(`Stacks.FundamentalGroup.span_range_piRefineIdem`), universal exactness is local on `T`
(`Stacks.FundamentalGroup.IsUnivExact.of_localized_span`), and over the localization away from
one of them both maps are induced by maps of index types
(`Stacks.FundamentalGroup.tensorProduct_map_eq_piPrecompAlgHom`), where
`Stacks.FundamentalGroup.isUnivExact_piPrecompAlgHom` applies. -/
theorem isStableEqualizer_pi [Finite κ] (α β : (ι → T) →ₐ[T] (κ → T)) :
    IsStableEqualizer α β := by
  classical
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  refine IsUnivExact.of_localized_span (Set.range (piRefineIdem α β))
    (span_range_piRefineIdem α β) fun r ↦ ?_
  obtain ⟨s, hs⟩ := r.2
  have hinst : IsLocalization.Away (piRefineIdem α β s) (Localization.Away (r : T)) := by
    rw [hs]
    infer_instance
  let _ := hinst
  refine isUnivExact_baseChange_of_isStableEqualizer (Localization.Away (r : T)) ?_
  have h0 : IsStableEqualizer
      (piPrecompAlgHom (Localization.Away (r : T)) (fun j ↦ (s j).1))
      (piPrecompAlgHom (Localization.Away (r : T)) (fun j ↦ (s j).2)) :=
    isUnivExact_piPrecompAlgHom _ _
  have h1 := IsStableEqualizer.congr
    (Algebra.TensorProduct.piScalarRight T (Localization.Away (r : T))
      (Localization.Away (r : T)) ι).symm
    (Algebra.TensorProduct.piScalarRight T (Localization.Away (r : T))
      (Localization.Away (r : T)) κ).symm _ _ h0
  simp only [AlgEquiv.symm_symm] at h1
  rwa [← tensorProduct_map_eq_piPrecompAlgHom (Localization.Away (r : T)) _ α
      (fun y j ↦ (algebraMap_apply_eq α β s (Localization.Away (r : T)) y j).1),
    ← tensorProduct_map_eq_piPrecompAlgHom (Localization.Away (r : T)) _ β
      (fun y j ↦ (algebraMap_apply_eq α β s (Localization.Away (r : T)) y j).2)]

end Split

/-! ### The general case -/

section General

variable {R : Type u} [CommRing R] {B C : Type u} [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C]

/-- **The equalizer of two maps of split algebras is stable under base change.** This is
`Stacks.FundamentalGroup.isStableEqualizer_pi` transported along the splittings; the index types
are lifted to the universe of `R`. -/
theorem isStableEqualizer_of_isFiniteSplit [Algebra.IsFiniteSplit R B]
    [Algebra.IsFiniteSplit R C] (α β : B →ₐ[R] C) : IsStableEqualizer α β := by
  classical
  obtain ⟨n, ⟨f₁⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun R B
  obtain ⟨m, ⟨f₂⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun R C
  set e₁ : B ≃ₐ[R] (ULift.{u} (Fin n) → R) :=
    f₁.trans (AlgEquiv.piCongrLeft' R (fun _ : Fin n ↦ R) Equiv.ulift.symm)
  set e₂ : C ≃ₐ[R] (ULift.{u} (Fin m) → R) :=
    f₂.trans (AlgEquiv.piCongrLeft' R (fun _ : Fin m ↦ R) Equiv.ulift.symm)
  have h := IsStableEqualizer.congr e₁.symm e₂.symm _ _
    (isStableEqualizer_pi (e₂.toAlgHom.comp (α.comp e₁.symm.toAlgHom))
      (e₂.toAlgHom.comp (β.comp e₁.symm.toAlgHom)))
  have hconj : ∀ φ : B →ₐ[R] C, e₂.symm.toAlgHom.comp
      ((e₂.toAlgHom.comp (φ.comp e₁.symm.toAlgHom)).comp e₁.symm.symm.toAlgHom) = φ :=
    fun φ ↦ AlgHom.ext fun b ↦ by simp
  rwa [← hconj α, ← hconj β]

/-- **Descent of base-change stability along a faithfully flat splitting.** If `B` and `C` become
finite split after base change to a faithfully flat `R`-algebra `T`, the equalizer of any two
`R`-algebra maps `B ⟶ C` is stable under base change. -/
theorem isStableEqualizer_of_faithfullyFlat (T : Type u) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] [Algebra.IsFiniteSplit T (T ⊗[R] B)]
    [Algebra.IsFiniteSplit T (T ⊗[R] C)] (α β : B →ₐ[R] C) : IsStableEqualizer α β :=
  IsUnivExact.of_faithfullyFlat (T := T)
    (isUnivExact_baseChange_of_isStableEqualizer T (isStableEqualizer_of_isFiniteSplit _ _))

/-- **The constant-rank case.** For `B` and `C` finite étale over `R` of constant rank, the
equalizer of any two `R`-algebra maps `B ⟶ C` is stable under base change: such algebras become
split over a faithfully flat finite étale extension
(`Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`). -/
theorem isStableEqualizer_of_rankAtStalk [Module.Finite R B] [Algebra.Etale R B]
    [Module.Finite R C] [Algebra.Etale R C] {n m : ℕ}
    (hn : Module.rankAtStalk (R := R) B = n) (hm : Module.rankAtStalk (R := R) C = m)
    (α β : B →ₐ[R] C) : IsStableEqualizer α β := by
  obtain ⟨T₁, _, _, _, _, _, hB⟩ :=
    Algebra.IsFiniteSplit.exists_tensorProduct_of_etale (R := R) (S := B) hn
  have : Algebra.Etale T₁ (T₁ ⊗[R] C) := Algebra.Etale.baseChange R C T₁
  have hmT : Module.rankAtStalk (R := T₁) (T₁ ⊗[R] C) = m := by
    funext p
    rw [Module.rankAtStalk_baseChange]
    exact congrFun hm _
  obtain ⟨T₂, _, _, _, _, _, hC⟩ :=
    Algebra.IsFiniteSplit.exists_tensorProduct_of_etale (R := T₁) (S := T₁ ⊗[R] C) hmT
  algebraize [(algebraMap T₁ T₂).comp (algebraMap R T₁)]
  have : Module.FaithfullyFlat R T₂ := Module.FaithfullyFlat.trans R T₁ T₂
  have : Algebra.IsFiniteSplit T₂ (T₂ ⊗[R] B) :=
    Algebra.IsFiniteSplit.of_algEquiv (Algebra.TensorProduct.cancelBaseChange R T₁ T₂ T₂ B)
  have : Algebra.IsFiniteSplit T₂ (T₂ ⊗[R] C) :=
    Algebra.IsFiniteSplit.of_algEquiv (Algebra.TensorProduct.cancelBaseChange R T₁ T₂ T₂ C)
  exact isStableEqualizer_of_faithfullyFlat T₂ α β

/-- **Forming the equalizer of two maps of finite étale algebras commutes with base change.**
For `B` and `C` finite étale over `R` and any two `R`-algebra maps `α, β : B ⟶ C`, the sequence
`Eq(α, β) ⟶ B ⟶ C` is universally exact.

The ranks of `B` and `C` are constant after localizing away from the elements of a spanning set
(`Stacks.FundamentalGroup.span_rankConstantAway_eq_top`), universal exactness is local on the
base, and there `Stacks.FundamentalGroup.isStableEqualizer_of_rankAtStalk` applies. -/
theorem isStableEqualizer [Module.Finite R B] [Algebra.Etale R B] [Module.Finite R C]
    [Algebra.Etale R C] (α β : B →ₐ[R] C) : IsStableEqualizer α β := by
  refine IsUnivExact.of_localized_span (rankConstantAway R B C)
    (span_rankConstantAway_eq_top R B C) fun r ↦ ?_
  obtain ⟨n, m, hn, hm⟩ := r.2
  have : Algebra.Etale (Localization.Away (r : R)) (Localization.Away (r : R) ⊗[R] B) :=
    Algebra.Etale.baseChange R B _
  have : Algebra.Etale (Localization.Away (r : R)) (Localization.Away (r : R) ⊗[R] C) :=
    Algebra.Etale.baseChange R C _
  exact isUnivExact_baseChange_of_isStableEqualizer _
    (isStableEqualizer_of_rankAtStalk hn hm _ _)

/-- **Stacks 0BN9: forming the equalizer algebra commutes with base change.** The class of
finite étale ring homomorphisms has stable equalizers: for `B` and `C` finite étale over `R`,
the canonical map `S ⊗[R] Eq(α, β) ⟶ Eq(α_S, β_S)` is bijective for *every* `R`-algebra `S`,
not only for the flat ones. -/
theorem _root_.RingHom.FiniteEtale.hasStableEqualizers :
    RingHom.HasStableEqualizers @RingHom.FiniteEtale := by
  intro R S B C _ _ _ _ _ _ _ α β hB hC
  have : Module.Finite R B := RingHom.finite_algebraMap.mp hB.1
  have : Algebra.Etale R B := RingHom.etale_algebraMap.mp hB.2
  have : Module.Finite R C := RingHom.finite_algebraMap.mp hC.1
  have : Algebra.Etale R C := RingHom.etale_algebraMap.mp hC.2
  exact bijective_tensorEqualizer_of_isStableEqualizer (isStableEqualizer α β) S

end General

/-! ### The affine form of the fourth assertion of Stacks 0BN9 -/

section Category

open CategoryTheory CategoryTheory.Limits

/-- Being finite étale is stable under base change. -/
theorem _root_.RingHom.FiniteEtale.isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange @RingHom.FiniteEtale :=
  RingHom.finite_isStableUnderBaseChange.and RingHom.Etale.isStableUnderBaseChange

/-- The class of finite étale ring homomorphisms, as morphisms of `CommRingCat`, is stable under
cobase change. -/
instance _root_.RingHom.FiniteEtale.isStableUnderCobaseChange :
    (RingHom.toMorphismProperty @RingHom.FiniteEtale).IsStableUnderCobaseChange :=
  RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr
    RingHom.FiniteEtale.isStableUnderBaseChange

/-- **Stacks 0BN9, the affine form of the fourth assertion: base change is left exact on finite
étale algebras.** Base change along an arbitrary homomorphism `R ⟶ S` of commutative rings
preserves finite limits of finite étale algebras.

Finite limits are assembled from finite products and equalizers; the products are preserved
because the property is stable under cobase change, and the equalizers because forming the
equalizer algebra commutes with base change
(`RingHom.FiniteEtale.hasStableEqualizers`). -/
theorem preservesFiniteLimits_pushout_finiteEtale {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PreservesFiniteLimits (MorphismProperty.Under.pushout
      (RingHom.toMorphismProperty @RingHom.FiniteEtale) ⊤ f) :=
  RingHom.HasStableEqualizers.preservesFiniteLimits_pushout RingHom.FiniteEtale.respectsIso
    RingHom.FiniteEtale.hasFiniteProducts RingHom.FiniteEtale.hasEqualizers
    RingHom.FiniteEtale.hasStableEqualizers f

/-- **Stacks 0BN9, the affine form of the fourth assertion: base change is right exact on finite
étale covers of an affine scheme.** The category of finite étale covers of `Spec R` is the
opposite of the category of finite étale `R`-algebras, so the base-change functor along
`Spec S ⟶ Spec R` preserves finite colimits. -/
theorem preservesFiniteColimits_op_pushout_finiteEtale {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PreservesFiniteColimits (MorphismProperty.Under.pushout
      (RingHom.toMorphismProperty @RingHom.FiniteEtale) ⊤ f).op :=
  have := preservesFiniteLimits_pushout_finiteEtale f
  preservesFiniteColimits_op _

end Category

end Stacks.FundamentalGroup

end
