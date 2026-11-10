module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Flat.Tensor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.UniversalInjectivity
public import StacksFrontier.AlgebraicGeometry.Descent.UniversallyInjective.CharacterModule

/-!
# Descent of flatness along universally injective ring maps

Let `R → S` be a universally injective map of commutative rings. An `R`-module is flat,
respectively faithfully flat, exactly when its scalar extension to `S` is.

## Main results

* `Module.flat_iff_baseChange_of_universallyInjective`: flatness descends and ascends along a
  universally injective ring map.
* `Module.faithfullyFlat_iff_baseChange_of_universallyInjective`: the same for faithful
  flatness.

## Implementation notes

The scalar extension is written `S ⊗[R] M`, with the scalar algebra as the left tensor
factor, so that it carries Mathlib's canonical `S`-module structure.

Flatness is detected by Baer's criterion on the character module. The descent argument
transports a chosen section of `C(S) → C(R)` to a section of `C(B) → C(M)` for an arbitrary
surjection `B → M`: the section is first spread over `S ⊗[R] -` by
`functorialCharacterModuleSection`, then pushed back along `m ↦ 1 ⊗ m`. Applying this to a
free presentation of `M` turns Baer's property for a free module into Baer's property for
`M`. Faithful flatness then reduces to flatness together with properness of extended ideals,
which is where universal injectivity is used a second time.

The evaluation formulas for the sections on an elementary tensor hold by definitional
unfolding; they are recorded as separate equations so that the rewrites below do not depend on
the elaborator's unfolding behaviour.

## References

* [Stacks Project, Tag 08XD](https://stacks.math.columbia.edu/tag/08XD)
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Module

/-- Evaluating the character-module dual of `f` at `χ` and `a` applies `χ` to `f a`. -/
private lemma characterModule_dual_apply_apply
    {R : Type*} [CommRing R] {A B : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (f : A →ₗ[R] B) (χ : CharacterModule B) (a : A) :
    CharacterModule.dual f χ a = χ (f a) := rfl

/-- Evaluating `functorialCharacterModuleSection g P` on an elementary tensor. -/
private lemma functorialCharacterModuleSection_tmul
    {R : Type u} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (g : CharacterModule M →ₗ[R] CharacterModule N)
    (P : Type*) [AddCommGroup P] [Module R P] (χ : CharacterModule (P ⊗[R] M))
    (p : P) (n : N) :
    functorialCharacterModuleSection g P χ (p ⊗ₜ[R] n) = g (CharacterModule.curry χ p) n :=
  rfl

/-- The character-module section of `C(S ⊗[R] P) → C(P)` induced by a section `s` of
`C(S) → C(R)`, written through the symmetry of the tensor product. -/
private noncomputable def baseChangeCharacterSection
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    (s : CharacterModule R →ₗ[R] CharacterModule S)
    (P : Type*) [AddCommGroup P] [Module R P] :
    CharacterModule P →ₗ[R] CharacterModule (S ⊗[R] P) :=
  CharacterModule.dual (TensorProduct.comm R S P).toLinearMap ∘ₗ
    functorialCharacterModuleSection s P ∘ₗ
      CharacterModule.dual (TensorProduct.rid R P).toLinearMap

/-- Evaluating `baseChangeCharacterSection s P` on an elementary tensor. -/
private lemma baseChangeCharacterSection_tmul
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    (s : CharacterModule R →ₗ[R] CharacterModule S)
    (P : Type*) [AddCommGroup P] [Module R P]
    (χ : CharacterModule P) (t : S) (p : P) :
    baseChangeCharacterSection s P χ (t ⊗ₜ[R] p) =
      s (CharacterModule.curry
        (CharacterModule.dual (TensorProduct.rid R P).toLinearMap χ) p) t := rfl

/-- The character `CharacterModule.curry (C(rid) χ) p` sends `1` to `χ p`. -/
private lemma curry_dual_rid_apply_one
    {R : Type u} [CommRing R] {P : Type*} [AddCommGroup P] [Module R P]
    (χ : CharacterModule P) (p : P) :
    CharacterModule.curry (CharacterModule.dual (TensorProduct.rid R P).toLinearMap χ) p
      (1 : R) = χ p := by
  change χ (TensorProduct.rid R P (p ⊗ₜ[R] (1 : R))) = χ p
  rw [TensorProduct.rid_tmul, one_smul]

/-- The section splits the dual of the unit `p ↦ 1 ⊗ p`. -/
private lemma baseChangeCharacterSection_split
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    (s : CharacterModule R →ₗ[R] CharacterModule S)
    (hs : CharacterModule.dual (Algebra.linearMap R S) ∘ₗ s = LinearMap.id)
    (P : Type*) [AddCommGroup P] [Module R P] :
    CharacterModule.dual (TensorProduct.mk R S P 1) ∘ₗ
      baseChangeCharacterSection s P = LinearMap.id := by
  ext χ p
  change baseChangeCharacterSection s P χ ((1 : S) ⊗ₜ[R] p) = χ p
  rw [baseChangeCharacterSection_tmul]
  have h1 := congrArg (fun φ : CharacterModule R => φ (1 : R))
    (LinearMap.congr_fun hs (CharacterModule.curry
      (CharacterModule.dual (TensorProduct.rid R P).toLinearMap χ) p))
  simp only [LinearMap.comp_apply, characterModule_dual_apply_apply, Algebra.linearMap_apply,
    map_one, LinearMap.id_apply] at h1
  exact h1.trans (curry_dual_rid_apply_one χ p)

/-- The section is natural in the module: it commutes with the duals of a map and of its
base change. -/
private lemma baseChangeCharacterSection_natural
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    (s : CharacterModule R →ₗ[R] CharacterModule S)
    {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (h : P →ₗ[R] Q) :
    CharacterModule.dual ((LinearMap.baseChange S h).restrictScalars R) ∘ₗ
        baseChangeCharacterSection s Q =
      baseChangeCharacterSection s P ∘ₗ CharacterModule.dual h := by
  ext χ x
  induction x using TensorProduct.inductionOn with
  | tmul s' p =>
      change baseChangeCharacterSection s Q χ (s' ⊗ₜ[R] h p) =
        baseChangeCharacterSection s P (CharacterModule.dual h χ) (s' ⊗ₜ[R] p)
      rw [baseChangeCharacterSection_tmul, baseChangeCharacterSection_tmul]
      congr 2
      ext r
      rw [CharacterModule.curry_apply_apply, CharacterModule.curry_apply_apply]
      change χ (TensorProduct.rid R Q (h p ⊗ₜ[R] r)) =
        χ (h (TensorProduct.rid R P (p ⊗ₜ[R] r)))
      simp [TensorProduct.rid_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- An `S`-linear map of character modules, read as an `R`-linear map along `R → S`.

Mathlib's `LinearMap.restrictScalars` does not apply because the character module of an
`S`-module carries no `IsScalarTower R S` instance for its two actions; the two scalar
actions agree because both are induced by the action on the source module. -/
private def characterModuleRestrictScalars
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    {P Q : Type*} [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
      [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    (f : CharacterModule P →ₗ[S] CharacterModule Q) :
    CharacterModule P →ₗ[R] CharacterModule Q where
  toFun := f
  map_add' := f.map_add
  map_smul' r χ := by
    have hp : r • χ = (algebraMap R S r) • χ := by
      ext x
      simp [CharacterModule.smul_apply]
    have hq : r • f χ = (algebraMap R S r) • f χ := by
      ext x
      simp [CharacterModule.smul_apply]
    rw [hp, map_smul]
    exact hq.symm

/-- For a universally injective `R → S` with `S ⊗[R] M` flat over `S`, the character-module
dual of any surjection onto `M` admits a linear section. -/
private lemma dual_surjection_split_of_baseChange_flat
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    (hRS : Algebra.UniversallyInjective R S)
    {M : Type v} [AddCommGroup M] [Module R M]
    (hflat : Module.Flat S (S ⊗[R] M))
    {B : Type*} [AddCommGroup B] [Module R B]
    (g : B →ₗ[R] M) (hg : Function.Surjective g) :
    ∃ r : CharacterModule B →ₗ[R] CharacterModule M,
      r ∘ₗ CharacterModule.dual g = LinearMap.id := by
  obtain ⟨s, hs⟩ :=
    (universallyInjective_iff_dual_splitSurjective (Algebra.linearMap R S)).mp hRS
  have hBaer : Module.Baer S (CharacterModule (S ⊗[R] M)) :=
    Module.Flat.iff_characterModule_baer.mp hflat
  have hgS : Function.Surjective (LinearMap.baseChange S g) := by
    simpa only [LinearMap.baseChange_eq_lTensor] using LinearMap.lTensor_surjective S hg
  obtain ⟨rS, hrS⟩ :=
    hBaer.extension_property (CharacterModule.dual (LinearMap.baseChange S g))
      (CharacterModule.dual_injective_iff_surjective.mpr hgS) LinearMap.id
  refine ⟨CharacterModule.dual (TensorProduct.mk R S M 1) ∘ₗ
    characterModuleRestrictScalars rS ∘ₗ baseChangeCharacterSection s B, ?_⟩
  ext χ x
  have hn := LinearMap.congr_fun (baseChangeCharacterSection_natural s g) χ
  have hsplit := LinearMap.congr_fun (baseChangeCharacterSection_split s hs M) χ
  have hright := LinearMap.congr_fun hrS (baseChangeCharacterSection s M χ)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hn hsplit hright
  have hdualEq : CharacterModule.dual ((LinearMap.baseChange S g).restrictScalars R)
      (baseChangeCharacterSection s M χ) =
      CharacterModule.dual (LinearMap.baseChange S g)
        (baseChangeCharacterSection s M χ) := by
    ext z
    rfl
  change (CharacterModule.dual (TensorProduct.mk R S M 1)
    (rS (baseChangeCharacterSection s B (CharacterModule.dual g χ)))) x = χ x
  rw [hn.symm.trans hdualEq, hright, hsplit]

/-- Flatness descends and ascends along a universally injective ring map. -/
@[stacks 08XD "flat"]
theorem flat_iff_baseChange_of_universallyInjective
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    (hRS : Algebra.UniversallyInjective R S)
    (M : Type v) [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔ Module.Flat S (TensorProduct R S M) := by
  refine ⟨fun _ ↦ Module.Flat.baseChange R S M, fun hS ↦ ?_⟩
  let F : Type (max u v) := M →₀ R
  let q : F →ₗ[R] M := Finsupp.linearCombination R (id : M → M)
  have hFbaer : Module.Baer R (CharacterModule F) :=
    Module.Flat.iff_characterModule_baer.mp (inferInstance : Module.Flat R F)
  obtain ⟨r, hr⟩ := dual_surjection_split_of_baseChange_flat hRS hS q
    (Finsupp.linearCombination_id_surjective R M)
  refine Module.Flat.iff_characterModule_baer.mpr fun I φ ↦ ?_
  obtain ⟨g, hg⟩ := hFbaer I ((CharacterModule.dual q).comp φ)
  refine ⟨r.comp g, fun x hx ↦ ?_⟩
  change r (g x) = φ ⟨x, hx⟩
  rw [hg]
  simpa [LinearMap.comp_apply] using LinearMap.congr_fun hr (φ ⟨x, hx⟩)

/-- Along a universally injective ring map, a proper ideal extends to a proper ideal. -/
theorem _root_.Ideal.map_ne_top_of_universallyInjective
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    (hRS : Algebra.UniversallyInjective R S) {I : Ideal R} (hI : I ≠ ⊤) :
    I.map (algebraMap R S) ≠ ⊤ := by
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : Nontrivial (TensorProduct R (R ⧸ I) S) :=
    (baseChangeUnit_injective (hRS : UniversallyInjective (Algebra.linearMap R S)) _).nontrivial
  have : Nontrivial (TensorProduct R S (R ⧸ I)) :=
    (TensorProduct.comm R (R ⧸ I) S).toEquiv.symm.nontrivial
  exact Ideal.Quotient.nontrivial_iff.mp
    ((Ideal.quotMapEquivTensorQuot (S := S) (I := I)).toEquiv.nontrivial)

/-- Faithful flatness descends and ascends along a universally injective ring map. -/
@[stacks 08XD "faithfully_flat", ega "0 6.6.3" "more general"]
theorem faithfullyFlat_iff_baseChange_of_universallyInjective
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    (hRS : Algebra.UniversallyInjective R S)
    (M : Type v) [AddCommGroup M] [Module R M] :
    Module.FaithfullyFlat R M ↔ Module.FaithfullyFlat S (TensorProduct R S M) := by
  refine ⟨fun _ ↦ inferInstance, fun hS ↦ ?_⟩
  refine (Module.FaithfullyFlat.iff_flat_and_proper_ideal R M).2
    ⟨(flat_iff_baseChange_of_universallyInjective hRS M).mpr hS.toFlat, fun I hI htop ↦ ?_⟩
  have : Subsingleton (M ⧸ (I • (⊤ : Submodule R M))) :=
    Submodule.Quotient.subsingleton_iff.mpr htop
  exact ((Module.FaithfullyFlat.iff_flat_and_proper_ideal S (S ⊗[R] M)).mp hS).2
    (I.map (algebraMap R S)) (Ideal.map_ne_top_of_universallyInjective hRS hI)
    (Submodule.Quotient.subsingleton_iff.mp
      ((Equiv.subsingleton_congr
        (TensorProduct.tensorQuotMapSMulEquivTensorQuot (S := S) (M := M) I).toEquiv).mpr
        inferInstance))

end Module

end
