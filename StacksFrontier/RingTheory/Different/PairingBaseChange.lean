module

public import Mathlib.Algebra.FiveLemma
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.IsBaseChange
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom

/-!
# Base change of a perfect pairing

A bilinear pairing `p : M × N → R` induces `N → Hom_R(M, R)`, and this file collects the
module theory that decides when that induced map is bijective after a base change `R → S`, and
when bijectivity descends from a faithfully flat base change.

The key input is that the dual of a finitely presented module is a base change along a flat
ring map: the canonical map `Hom_R(M, R) → Hom_S(S ⊗_R M, S)` exhibits the target as the scalar
extension of the source. That rests in turn on the Hom–tensor comparison
`Hom_R(M, N) ⊗_R L → Hom_R(M, N ⊗_R L)` being bijective for a finitely presented source and a
flat tensor factor.

## Main results

* `Stacks.Discriminant.rTensorHomToHomRTensor_bijective_of_finitePresentation`: the Hom–tensor
  comparison is bijective for a finitely presented source and a flat tensor factor.
* `Stacks.Discriminant.isBaseChange_toDual_of_flat`: for a finitely presented module and a flat
  algebra, the dual of a base change is the base change of the dual.
* `Stacks.Discriminant.baseChange_bijective_iff_of_isBaseChange`: bijectivity of a scalar
  extension is bijectivity of any map it is a base change of.
* `Stacks.Discriminant.pairing_flip_baseChange_bijective_iff` and
  `Stacks.Discriminant.pairing_flip_iteratedBaseChange_bijective_iff`: the map induced by a
  pairing and the map induced by its base change are simultaneously bijective.
* `Stacks.Discriminant.pairing_flip_bijective_of_isBaseChange`: bijectivity of the induced map
  descends along a faithfully flat base change.
* `Stacks.Discriminant.localizedMap_bijective_of_flat_baseChange`: a map which is bijective
  after a flat base change is bijective after localizing at a prime lying under a prime of the
  extension.

## Implementation notes

A pairing is represented as a linear map `M →ₗ[R] N →ₗ[R] R`; the map it induces on the second
argument is its `LinearMap.flip`. Base changes are not assumed to be literal tensor products:
each is given as an `IsBaseChange` witness, so the results apply to localizations and to
explicitly constructed scalar extensions without transporting along a comparison isomorphism
first.

## References

* [Stacks Project, Tag 0BVS](https://stacks.math.columbia.edu/tag/0BVS)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.Discriminant

/-- Precomposition with an exact pair whose second member is surjective is exact. -/
private theorem exact_lcomp_of_exact {R : Type*} [CommRing R]
    {M N P Q : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hg : Function.Surjective g)
    (h : Function.Exact f g) :
    Function.Exact (LinearMap.lcomp R Q g) (LinearMap.lcomp R Q f) := by
  intro k
  constructor
  · intro hk
    have hker : g.ker ≤ k.ker := by
      intro n hn
      obtain ⟨m, rfl⟩ := (h n).mp hn
      exact DFunLike.congr_fun hk m
    refine ⟨(g.ker.liftQ k hker).comp (g.quotKerEquivOfSurjective hg).symm.toLinearMap, ?_⟩
    ext n
    simp
  · rintro ⟨k, rfl⟩
    ext m
    change k (g (f m)) = 0
    rw [(h (f m)).mpr ⟨m, rfl⟩, map_zero]

/-- The Hom–tensor comparison is natural in the source. -/
private theorem rTensorHomToHomRTensor_lcomp {R : Type*} [CommRing R]
    {M N P Q : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q]
    (f : M →ₗ[R] N) :
    (LinearMap.lcomp R (P ⊗[R] Q) f).comp
        (TensorProduct.rTensorHomToHomRTensor (RingHom.id R) N P Q) =
      (TensorProduct.rTensorHomToHomRTensor (RingHom.id R) M P Q).comp
        ((LinearMap.lcomp R P f).rTensor Q) := by
  ext k q m
  rfl

/-- The Hom–tensor comparison is bijective for a finite projective source, with no flatness
hypothesis on the tensor factor. -/
private theorem rTensorHomToHomRTensor_bijective_of_projective
    (R M N P : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective
      (TensorProduct.rTensorHomToHomRTensor (RingHom.id R) M N P) := by
  have he : ⇑(rTensorHomEquivHomRTensor R M N P) =
      ⇑(TensorProduct.rTensorHomToHomRTensor (RingHom.id R) M N P) :=
    funext rTensorHomEquivHomRTensor_apply
  rw [← he]
  exact (rTensorHomEquivHomRTensor R M N P).bijective

/-- The Hom–tensor comparison `Hom_R(M, N) ⊗_R P → Hom_R(M, N ⊗_R P)` is bijective for a
finitely presented source and a flat tensor factor. -/
theorem rTensorHomToHomRTensor_bijective_of_finitePresentation
    (R M N P : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [Module.FinitePresentation R M] [Module.Flat R P] :
    Function.Bijective
      (TensorProduct.rTensorHomToHomRTensor (RingHom.id R) M N P) := by
  obtain ⟨n, m, g, f, hg, hfg⟩ := Module.FinitePresentation.exists_fin' R M
  apply LinearMap.bijective_of_bijective_of_injective_of_left_exact
    ((LinearMap.lcomp R N g).rTensor P) ((LinearMap.lcomp R N f).rTensor P)
    (LinearMap.lcomp R (N ⊗[R] P) g) (LinearMap.lcomp R (N ⊗[R] P) f)
    _ (TensorProduct.rTensorHomToHomRTensor (RingHom.id R) (Fin n → R) N P)
    (TensorProduct.rTensorHomToHomRTensor (RingHom.id R) (Fin m → R) N P)
    (rTensorHomToHomRTensor_lcomp g) (rTensorHomToHomRTensor_lcomp f)
    (Module.Flat.rTensor_exact P (exact_lcomp_of_exact f g hg hfg))
    (exact_lcomp_of_exact f g hg hfg)
  · exact rTensorHomToHomRTensor_bijective_of_projective R _ _ _
  · exact (rTensorHomToHomRTensor_bijective_of_projective R _ _ _).1
  · exact Module.Flat.rTensor_preserves_injective_linearMap _
      (LinearMap.lcomp_injective_of_surjective g hg)
  · exact LinearMap.lcomp_injective_of_surjective g hg

/-- For a finitely presented module and a flat algebra, taking the dual commutes with base
change: the canonical map `Hom_R(M, R) → Hom_S(N, S)` out of the dual exhibits the dual of a
base change as the base change of the dual. -/
theorem isBaseChange_toDual_of_flat
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N]
    [Module.FinitePresentation R M] [Module.Flat R S]
    {j : M →ₗ[R] N} (hj : IsBaseChange S j) :
    IsBaseChange S hj.toDual := by
  have hright : IsBaseChange S
      (LinearMap.compRight (M := M) R (Algebra.linearMap R S)) := by
    let f := IsBaseChange.linearMapRightBaseChangeHom S M (Algebra.linearMap R S)
    have hf : Function.Bijective f := by
      let e : (M →ₗ[R] R ⊗[R] S) ≃ₗ[R] (M →ₗ[R] S) :=
        LinearEquiv.arrowCongr (LinearEquiv.refl R M) (TensorProduct.lid R S)
      have he : ⇑f = ⇑e ∘
          (TensorProduct.rTensorHomToHomRTensor (RingHom.id R) M R S) ∘
          ⇑(TensorProduct.comm R S (Module.Dual R M)) := by
        funext z
        induction z using TensorProduct.induction_on with
        | zero => simp [f]
        | add x y hx hy => simp_all [Function.comp_def]
        | tmul s φ =>
          ext m
          simp [f, e, IsBaseChange.linearMapRightBaseChangeHom,
            Algebra.smul_def, mul_comm]
      rw [he]
      exact e.bijective.comp
        ((rTensorHomToHomRTensor_bijective_of_finitePresentation R M R S).comp
          (TensorProduct.comm R S (Module.Dual R M)).bijective)
    apply IsBaseChange.of_equiv (LinearEquiv.ofBijective f hf)
    intro φ
    ext m
    simp [f, IsBaseChange.linearMapRightBaseChangeHom]
  apply IsBaseChange.of_equiv
    (hright.equiv ≪≫ₗ LinearMap.liftBaseChangeEquiv S ≪≫ₗ LinearEquiv.congrLeft S S hj.equiv)
  intro φ
  ext n
  simp [IsBaseChange.toDual, IsBaseChange.linearMapLeftRightHom_apply,
    LinearEquiv.congrLeft]

/-- A map is bijective after scalar extension exactly when any map it base changes to is
bijective. -/
theorem baseChange_bijective_iff_of_isBaseChange
    {R S M N P Q : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
    [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    (f : M →ₗ[R] N) (g : P →ₗ[S] Q)
    (i : M →ₗ[R] P) (j : N →ₗ[R] Q)
    (hi : IsBaseChange S i) (hj : IsBaseChange S j)
    (hcomm : ∀ m, g (i m) = j (f m)) :
    Function.Bijective (f.baseChange S) ↔ Function.Bijective g := by
  have h : hj.equiv.toLinearMap.comp (f.baseChange S) =
      g.comp hi.equiv.toLinearMap := by
    ext s
    simp [hcomm]
  have he : ⇑g = ⇑hj.equiv ∘ ⇑(f.baseChange S) ∘ ⇑hi.equiv.symm := by
    funext p
    simpa using (DFunLike.congr_fun h (hi.equiv.symm p)).symm
  simp only [he, EquivLike.bijective_comp, EquivLike.comp_bijective]

/-- An iterated scalar extension is bijective exactly when the single extension to the larger
ring is. -/
theorem baseChange_baseChange_bijective_iff
    {R S T M N : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    Function.Bijective ((f.baseChange S).baseChange T) ↔
      Function.Bijective (f.baseChange T) := by
  rw [LinearMap.baseChange_baseChange]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.bijective_comp,
    EquivLike.comp_bijective]

/-- Two maps identified by linear equivalences on source and target have simultaneously
bijective scalar extensions. -/
theorem baseChange_bijective_iff_of_linearEquiv
    {R S M N P Q : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (f : M →ₗ[R] N) (g : P →ₗ[R] Q) (eM : M ≃ₗ[R] P) (eN : N ≃ₗ[R] Q)
    (hcomm : ∀ m, g (eM m) = eN (f m)) :
    Function.Bijective (f.baseChange S) ↔ Function.Bijective (g.baseChange S) := by
  have hg : g = eN.toLinearMap.comp (f.comp eM.symm.toLinearMap) := by
    ext p
    simpa using hcomm (eM.symm p)
  have hf : f = eN.symm.toLinearMap.comp (g.comp eM.toLinearMap) := by
    ext m
    exact eN.injective (by simpa using (hcomm m).symm)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hg, LinearMap.baseChange_comp, LinearMap.baseChange_comp]
    exact (LinearEquiv.baseChange R S N Q eN).bijective.comp
      (h.comp (LinearEquiv.baseChange R S P M eM.symm).bijective)
  · rw [hf, LinearMap.baseChange_comp, LinearMap.baseChange_comp]
    exact (LinearEquiv.baseChange R S Q N eN.symm).bijective.comp
      (h.comp (LinearEquiv.baseChange R S M P eM).bijective)

/-- A map and a base change of it to an intermediate ring have simultaneously bijective
extensions to a larger ring. -/
theorem iteratedBaseChange_bijective_iff_of_isBaseChange
    {R S T M N P Q : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
    [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    (f : M →ₗ[R] N) (g : P →ₗ[S] Q)
    (i : M →ₗ[R] P) (j : N →ₗ[R] Q)
    (hi : IsBaseChange S i) (hj : IsBaseChange S j)
    (hcomm : ∀ m, g (i m) = j (f m)) :
    Function.Bijective (f.baseChange T) ↔ Function.Bijective (g.baseChange T) := by
  apply (baseChange_baseChange_bijective_iff (S := S) f).symm.trans
  apply baseChange_bijective_iff_of_linearEquiv (f.baseChange S) g hi.equiv hj.equiv
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => simp [hcomm]
  | add x y hx hy => simp [hx, hy]

/-- Scalar extension of a bijective map is bijective. -/
theorem baseChange_bijective_of_bijective
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (h : Function.Bijective f) :
    Function.Bijective (f.baseChange S) :=
  (LinearEquiv.baseChange R S M N (LinearEquiv.ofBijective f h)).bijective

/-- Localizing a map is the same as extending scalars to the localization. -/
theorem localizedMap_bijective_iff_baseChange
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (S : Submonoid R) (f : M →ₗ[R] N) :
    Function.Bijective (LocalizedModule.map S f) ↔
      Function.Bijective (f.baseChange (Localization S)) :=
  (baseChange_bijective_iff_of_isBaseChange f (LocalizedModule.map S f)
    (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S N)
    (LocalizedModule.isBaseChange S M) (LocalizedModule.isBaseChange S N)
    (fun m => by simp)).symm

/-- A map which becomes bijective after a flat base change becomes bijective after localizing
at a prime under a prime of the extension. -/
theorem localizedMap_bijective_of_flat_baseChange
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (h : Function.Bijective (f.baseChange S)) :
    Function.Bijective (LocalizedModule.map p.primeCompl f) := by
  let _ := Localization.AtPrime.algebraOfLiesOver p q
  have : Module.Flat S (Localization.AtPrime q) :=
    IsLocalization.flat (Localization.AtPrime q) q.primeCompl
  have : Module.Flat R (Localization.AtPrime q) :=
    Module.Flat.trans R S (Localization.AtPrime q)
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl _).mpr
      inferInstance
  have : Module.FaithfullyFlat (Localization.AtPrime p) (Localization.AtPrime q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  apply (localizedMap_bijective_iff_baseChange p.primeCompl f).mpr
  apply (Module.FaithfullyFlat.lTensor_bijective_iff_bijective
    (Localization.AtPrime p) (Localization.AtPrime q)
    (f.baseChange (Localization.AtPrime p))).mp
  apply (baseChange_baseChange_bijective_iff f).mpr
  apply (baseChange_baseChange_bijective_iff (S := S) f).mp
  exact baseChange_bijective_of_bijective (f.baseChange S) h

/-- The maps induced by a pairing and by its base change are simultaneously bijective, for a
flat base change of a pairing whose first argument is finitely presented. -/
theorem pairing_flip_baseChange_bijective_iff
    {R S M N P Q : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
    [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    [Module.Flat R S] [Module.FinitePresentation R M]
    (p : M →ₗ[R] N →ₗ[R] R) (q : P →ₗ[S] Q →ₗ[S] S)
    (i : M →ₗ[R] P) (j : N →ₗ[R] Q)
    (hi : IsBaseChange S i) (hj : IsBaseChange S j)
    (hcomm : ∀ m n, q (i m) (j n) = algebraMap R S (p m n)) :
    Function.Bijective (p.flip.baseChange S) ↔ Function.Bijective q.flip :=
  baseChange_bijective_iff_of_isBaseChange p.flip q.flip j hi.toDual hj
    (isBaseChange_toDual_of_flat hi) fun n => hi.algHom_ext _ _ fun m =>
      (hcomm m n).trans (hi.toDual_comp_apply (p.flip n) m).symm

/-- The maps induced by a pairing and by its base change have simultaneously bijective
extensions to any further algebra. -/
theorem pairing_flip_iteratedBaseChange_bijective_iff
    {R S T M N P Q : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
    [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    [Module.Flat R S] [Module.FinitePresentation R M]
    (p : M →ₗ[R] N →ₗ[R] R) (q : P →ₗ[S] Q →ₗ[S] S)
    (i : M →ₗ[R] P) (j : N →ₗ[R] Q)
    (hi : IsBaseChange S i) (hj : IsBaseChange S j)
    (hcomm : ∀ m n, q (i m) (j n) = algebraMap R S (p m n)) :
    Function.Bijective (p.flip.baseChange T) ↔
      Function.Bijective (q.flip.baseChange T) :=
  iteratedBaseChange_bijective_iff_of_isBaseChange p.flip q.flip j hi.toDual hj
    (isBaseChange_toDual_of_flat hi) fun n => hi.algHom_ext _ _ fun m =>
      (hcomm m n).trans (hi.toDual_comp_apply (p.flip n) m).symm

/-- Bijectivity descends along a faithfully flat base change. -/
theorem bijective_of_isBaseChange_of_faithfullyFlat
    {R S M N P Q : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
    [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    [Module.FaithfullyFlat R S]
    (f : M →ₗ[R] N) (g : P →ₗ[S] Q)
    (i : M →ₗ[R] P) (j : N →ₗ[R] Q)
    (hi : IsBaseChange S i) (hj : IsBaseChange S j)
    (hcomm : ∀ m, g (i m) = j (f m)) (hg : Function.Bijective g) :
    Function.Bijective f :=
  (Module.FaithfullyFlat.lTensor_bijective_iff_bijective R S f).mp
    ((baseChange_bijective_iff_of_isBaseChange f g i j hi hj hcomm).mpr hg)

/-- Bijectivity of the map induced by a pairing descends along a faithfully flat base
change. -/
theorem pairing_flip_bijective_of_isBaseChange
    {R S M N P Q : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
    [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    [Module.FaithfullyFlat R S] [Module.FinitePresentation R M]
    (p : M →ₗ[R] N →ₗ[R] R) (q : P →ₗ[S] Q →ₗ[S] S)
    (i : M →ₗ[R] P) (j : N →ₗ[R] Q)
    (hi : IsBaseChange S i) (hj : IsBaseChange S j)
    (hcomm : ∀ m n, q (i m) (j n) = algebraMap R S (p m n))
    (hq : Function.Bijective q.flip) : Function.Bijective p.flip :=
  bijective_of_isBaseChange_of_faithfullyFlat p.flip q.flip j hi.toDual hj
    (isBaseChange_toDual_of_flat hi) (fun n => hi.algHom_ext _ _ fun m =>
      (hcomm m n).trans (hi.toDual_comp_apply (p.flip n) m).symm) hq

end Stacks.Discriminant

end
