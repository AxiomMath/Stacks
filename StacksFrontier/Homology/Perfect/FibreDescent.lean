module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.Perfect.Local
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.Homology.TorAmplitude.FlatRepresentative
public import StacksFrontier.RingTheory.GlobalDimension.Cyclic
public import StacksFrontier.RingTheory.GlobalDimension.Defs
public import StacksFrontier.RingTheory.RegularLocalRing.GlobalDimension
import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# Perfectness over a flat algebra with fibres of bounded global dimension

Let `A → B` be a flat map of commutative rings and let `K` be a complex of `B`-modules which is
pseudo-coherent over `B` and has Tor amplitude in `[a, b]` as a complex of `A`-modules. This module
proves that `K` is perfect over `B` with Tor amplitude in `[a - d, b]` in two situations: when
every fibre ring `B ⊗_A κ(p)` has global dimension at most `d`, and when `A → B` is a local
homomorphism of local rings whose closed fibre `B/m_A B` is regular of dimension `d`.

## Main results

* `StacksDraft.Perfect.isPerfect_and_torAmplitude_of_flat_of_fibre_globalDimension_le`
  ([stacks 068X]): the criterion over a flat algebra all of whose fibres have global dimension at
  most `d`.
* `StacksDraft.Perfect.isPerfect_and_torAmplitude_of_flat_local_of_regular_closedFibre`
  ([stacks 09PC]): the criterion for a flat local homomorphism with regular closed fibre; as the
  source allows, the Tor-amplitude hypothesis over `A` is weakened to the vanishing of
  `Hⁱ(K ⊗_A^L κ(m_A))` outside `[a, b]`.
* `StacksDraft.Perfect.hasTorAmplitudeIn_flatRepresentative_of_hasTorAmplitude`: derived Tor
  amplitude against any certified derived tensor product, in the sense of [stacks 0652], gives the
  termwise Tor-amplitude condition on every bounded above flat representative, which is the form in
  which the Tor-amplitude hypotheses below are stated.
* `StacksDraft.Perfect.isZero_homology_tensorComplex_of_hasProjectiveDimensionLE` and
  `StacksDraft.Perfect.hasTorAmplitudeIn_of_ringGlobalDimension_le`: the termwise form of
  [stacks 066P] (2) over a ring of bounded global dimension, which is the local input the two
  criteria apply at the fibre ring.

## Implementation notes

Perfectness and Tor amplitude are recorded exactly as the fibrewise criterion [stacks 068V]
(`Perfect.isPerfect_and_torAmplitude_iff_fibreCohomologyVanishes`) records them:
`Perfect.IsPerfect` together with `Perfect.HasFlatRepresentative` in the window and the termwise
consequence that every bounded above flat representative has termwise Tor amplitude in the window.
By [stacks 0654] the flat representative is exactly Tor amplitude, and
`hasTorAmplitudeIn_flatRepresentative_of_hasTorAmplitude` supplies the same reading of the
Tor-amplitude *hypothesis* over `A` from derived Tor amplitude at an arbitrary certified derived
tensor product; the hypothesis is stated in the termwise form so that the statements of the two
criteria mention no derived tensor product at all.

Both criteria reduce by [stacks 068V] to the vanishing, outside the window `[a - d, b]`, of the
cohomology of the derived fibres `K ⊗_B^L κ(q)` at the primes (respectively at the maximal ideal)
of `B`. That vanishing is the content of
`isZero_homology_extendScalars_of_fibre_globalDimension_le` below and is proved on a bounded above
finite free representative `P` of `K`, along the factorization `B → C → κ(q)` through the fibre
ring `C`:

* `Hⁱ(C ⊗_B P)` vanishes outside `[a, b]`: restricted to `A` the complex `C ⊗_B P` is the termwise
  tensor product of the `A`-complex underlying `P` with the residue field the fibre is taken at.
  This is the projection formula, assembled from the module-level
  `projectionFormulaIso` of `StacksFrontier.Homology.KFlat.BaseChange` and the symmetry of
  `ModuleCat`, and restriction of scalars neither creates nor destroys the vanishing of a
  cohomology module.
* `C ⊗_B P` is a bounded above complex of free `C`-modules, so the global-dimension bound at `C`
  gives it termwise Tor amplitude in `[a - d, b]` by
  `hasTorAmplitudeIn_of_ringGlobalDimension_le`.
* Testing that against `κ(q)` and composing the two base changes `B → C → κ(q)` identifies the
  result with `Hⁱ(κ(q) ⊗_B P)`, which is the derived fibre of [stacks 068U].

The fibre ring is `B ⊗_A κ(p)` for [stacks 068X], with `p` the preimage of `q`, and the quotient
`B/m_A B` for [stacks 09PC]; in the latter case there is only one maximal ideal, so the criterion
is applied in its "maximal ideals only" form, and the global-dimension bound at the fibre comes
from [stacks 00O7], a regular local ring of dimension `d` having global dimension at most `d`.

The termwise Tor-amplitude bound over a ring of bounded global dimension is proved by induction on
the projective dimension of the test module rather than by the source's spectral sequence. A module
`M` of projective dimension at most `n + 1` sits in a short exact sequence `0 → K → P → M → 0` with
`P` projective and `K` of projective dimension at most `n`
(`ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff`); tensoring with the flat terms of `E`
keeps that sequence exact degreewise, hence exact as a sequence of complexes, and the long exact
cohomology sequence sandwiches `Hⁱ(E ⊗ M)` between `Hⁱ(E ⊗ P)` and `Hⁱ⁺¹(E ⊗ K)`. In the base case
`M` is projective, hence flat, and tensoring with a flat module preserves the vanishing of a single
cohomology module. Global dimension is `ringGlobalDimension`, a supremum over the modules in the
ring's own universe; [stacks 065T] (`ringGlobalDimension_lt_tfae`) transports the resulting bound
to the carrier universe used there. That part of the file carries the content of [stacks 066P] (2)
only in this termwise form, at independent ring and carrier universes; the tag belongs to its
owning module and is deliberately not attached here.

The two criteria themselves are stated with the module carriers in the universe of the rings, which
is the setting of the source: the fibre rings, their residue fields and the test modules of the
Tor-amplitude conditions all live in that universe, and the fibrewise criterion [stacks 068V] is
used at the instance `v = u` of its independent carrier universe.

## References

* [Stacks Project, Tag 066P](https://stacks.math.columbia.edu/tag/066P)
* [Stacks Project, Tag 068X](https://stacks.math.columbia.edu/tag/068X)
* [Stacks Project, Tag 09PC](https://stacks.math.columbia.edu/tag/09PC)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

universe u v

/-! ### Termwise Tor amplitude over a ring of bounded global dimension -/

section GlobalDimension

variable {C : Type u} [CommRing C]

/-- The morphism of termwise tensor products induced by a morphism of test modules. -/
private noncomputable def tensorComplexMap
    (E : CochainComplex (ModuleCat.{max u v} C) ℤ) {M N : ModuleCat.{max u v} C} (φ : M ⟶ N) :
    TorAmplitude.tensorComplex E M ⟶ TorAmplitude.tensorComplex E N where
  f n := ModuleCat.ofHom (LinearMap.lTensor (E.X n) φ.hom)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl

private lemma tensorComplexMap_comp_eq_zero
    (E : CochainComplex (ModuleCat.{max u v} C) ℤ) {M N P : ModuleCat.{max u v} C}
    (φ : M ⟶ N) (ψ : N ⟶ P) (h : φ ≫ ψ = 0) :
    tensorComplexMap.{u, v} E φ ≫ tensorComplexMap.{u, v} E ψ = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  have : ψ.hom (φ.hom y) = 0 := congrFun (congrArg (fun f => f.hom.toFun) h) y
  change x ⊗ₜ[C] (ψ.hom (φ.hom y)) = (0 : TensorProduct C (E.X n) P)
  rw [this, TensorProduct.tmul_zero]

/-- A short exact sequence of test modules gives a short exact sequence of the termwise tensor
products with a complex of flat modules: degreewise it is the given sequence tensored with a flat
module, and short exactness of a sequence of complexes is degreewise. -/
@[sga "7 VII 3.7.6" "special case"]
private lemma shortExact_tensorComplex
    (E : CochainComplex (ModuleCat.{max u v} C) ℤ)
    (hflat : ∀ n : ℤ, Module.Flat C (E.X n))
    (S : ShortComplex (ModuleCat.{max u v} C)) (hS : S.ShortExact) :
    (ShortComplex.mk (tensorComplexMap.{u, v} E S.f) (tensorComplexMap.{u, v} E S.g)
      (tensorComplexMap_comp_eq_zero E S.f S.g S.zero)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have := hflat n
  apply ModuleCat.shortComplex_shortExact
  · exact Module.Flat.lTensor_exact (E.X n : Type (max u v))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact)
  · exact Module.Flat.lTensor_preserves_injective_linearMap (M := (E.X n : Type (max u v)))
      S.f.hom (hS.moduleCat_injective_f)
  · exact LinearMap.lTensor_surjective _ hS.moduleCat_surjective_g

/-- Tensoring with a flat module preserves the vanishing of a single cohomology module. -/
private lemma isZero_homology_tensorComplex_of_flat
    (E : CochainComplex (ModuleCat.{max u v} C) ℤ) (M : ModuleCat.{max u v} C)
    [Module.Flat C M] (i : ℤ) (hE : IsZero (E.homology i)) :
    IsZero ((TorAmplitude.tensorComplex E M).homology i) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, i = m + 1 := ⟨i - 1, by ring⟩
  rw [← HomologicalComplex.exactAt_iff_isZero_homology] at hE ⊢
  rw [HomologicalComplex.exactAt_iff' E m (m + 1) (m + 1 + 1)
      (ComplexShape.prev_eq' _ rfl) (ComplexShape.next_eq' _ rfl),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hE
  rw [HomologicalComplex.exactAt_iff' _ m (m + 1) (m + 1 + 1)
      (ComplexShape.prev_eq' _ rfl) (ComplexShape.next_eq' _ rfl),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact Module.Flat.rTensor_exact (M : Type (max u v)) hE

/-- **Termwise Tor amplitude from bounded projective dimension of the test module.** Let `E` be a
complex of flat `C`-modules whose cohomology vanishes outside `[a, b]`. If the test module `M` has
projective dimension at most `n`, then `Hⁱ(E ⊗ M)` vanishes outside `[a - n, b]`.

The induction on `n` breaks `M` as `0 → K → P → M → 0` with `P` projective and `K` of projective
dimension at most `n - 1`; tensoring with the flat terms of `E` keeps that sequence exact, and the
long exact cohomology sequence sandwiches `Hⁱ(E ⊗ M)` between `Hⁱ(E ⊗ P)` and `Hⁱ⁺¹(E ⊗ K)`. -/
theorem isZero_homology_tensorComplex_of_hasProjectiveDimensionLE
    (E : CochainComplex (ModuleCat.{max u v} C) ℤ)
    (hflat : ∀ n : ℤ, Module.Flat C (E.X n)) (a b : ℤ)
    (hE : ∀ i : ℤ, (i < a ∨ b < i) → IsZero (E.homology i)) :
    ∀ (n : ℕ) (M : ModuleCat.{max u v} C), HasProjectiveDimensionLE M n →
      ∀ i : ℤ, (i < a - (n : ℤ) ∨ b < i) →
        IsZero ((TorAmplitude.tensorComplex E M).homology i) := by
  have hsmall : Small.{max u v} C := small_max C
  -- The projective case, which is also the base of the induction.
  have hbase : ∀ (M : ModuleCat.{max u v} C), Projective M → ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((TorAmplitude.tensorComplex E M).homology i) := by
    intro M hM i hi
    have : Module.Projective C M := ModuleCat.projective_of_module_projective M
    exact isZero_homology_tensorComplex_of_flat E M i (hE i hi)
  intro n
  induction n with
  | zero =>
      intro M hM i hi
      let _ := HasExt.standard (ModuleCat.{max u v} C)
      exact hbase M ((projective_iff_hasProjectiveDimensionLE_zero M).2 hM) i (by simpa using hi)
  | succ n ih =>
      intro M hM i hi
      set p : Projective.over M ⟶ M := Projective.π M
      set S : ShortComplex (ModuleCat.{max u v} C) :=
        ShortComplex.mk (kernel.ι p) p (kernel.condition p) with hSdef
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_kernel p
          mono_f := by rw [hSdef]; infer_instance
          epi_g := by rw [hSdef]; infer_instance }
      have hProj : Projective S.X₂ := by rw [hSdef]; infer_instance
      have hK : HasProjectiveDimensionLE S.X₁ n :=
        (hS.hasProjectiveDimensionLT_X₃_iff n hProj).1 hM
      have hSE := shortExact_tensorComplex.{u, v} E hflat S hS
      have h2 : IsZero ((TorAmplitude.tensorComplex E S.X₂).homology i) :=
        hbase S.X₂ hProj i (by omega)
      have h1 : IsZero ((TorAmplitude.tensorComplex E S.X₁).homology (i + 1)) :=
        ih S.X₁ hK (i + 1) (by omega)
      exact (hSE.homology_exact₃ i (i + 1) rfl).isZero_X₂
        (h2.eq_of_src _ _) (h1.eq_of_tgt _ _)

/-- Bounded global dimension bounds the projective dimension of every module, in any carrier
universe containing the ring. -/
private lemma hasProjectiveDimensionLE_of_ringGlobalDimension_le
    (d : ℕ) (hd : ringGlobalDimension C ≤ (d : ℕ)) (M : ModuleCat.{max u v} C) :
    HasProjectiveDimensionLE M d := by
  have hsmall : Small.{max u v} C := small_max C
  have hlt : (⨆ N : ModuleCat.{u} C, projectiveDimension N) < ((d + 1 : ℕ) : ℕ∞) :=
    lt_of_le_of_lt hd (by exact_mod_cast Nat.lt_succ_self d)
  have h := (ringGlobalDimension_lt_tfae.{max u v, u} C (d + 1)).out 1 2
  exact h.mp hlt M

/-- **The termwise form of [stacks 066P] (2).** Over a commutative ring of global dimension at
most `d`, a complex of flat modules whose cohomology is concentrated in `[a, b]` has termwise Tor
amplitude in `[a - d, b]`. -/
theorem hasTorAmplitudeIn_of_ringGlobalDimension_le
    (d : ℕ) (hd : ringGlobalDimension C ≤ (d : ℕ))
    (E : CochainComplex (ModuleCat.{max u v} C) ℤ)
    (hflat : ∀ n : ℤ, Module.Flat C (E.X n)) (a b : ℤ)
    (hE : ∀ i : ℤ, (i < a ∨ b < i) → IsZero (E.homology i)) :
    TorAmplitude.HasTorAmplitudeIn E (a - (d : ℤ)) b := fun M i hi =>
  isZero_homology_tensorComplex_of_hasProjectiveDimensionLE.{u, v} E hflat a b hE d M
    (hasProjectiveDimensionLE_of_ringGlobalDimension_le.{u, v} d hd M) i hi

end GlobalDimension

/-! ### Change of rings preliminaries -/

section ChangeOfRings

/-- Restriction of scalars neither creates nor destroys the vanishing of a cohomology module: it
changes neither the underlying abelian groups nor the differentials. -/
private theorem isZero_homology_restrictScalars_iff {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (K : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) :
    IsZero (((CochainComplex.restrictScalars f).obj K).homology i) ↔ IsZero (K.homology i) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff, HomologicalComplex.exactAt_iff,
    ShortComplex.moduleCat_exact_iff, ShortComplex.moduleCat_exact_iff]
  rfl

/-- The base change of a free module is flat. -/
private lemma flat_extendScalars_of_free {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) (h : Module.Free R M) :
    Module.Flat S ((ModuleCat.extendScalars f).obj M) := by
  let _ : Algebra R S := f.toAlgebra
  have := h
  change Module.Flat S (TensorProduct R S M)
  infer_instance

/-- Restricting the base change `S ⊗_R -` back to `R` is tensoring with `S` viewed as an
`R`-module: on carriers the two functors are the same. -/
private noncomputable def extendRestrictTensorLeftIso {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars f ≅
      tensorLeft ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- `extendRestrictTensorLeftIso` with the two tensor factors interchanged, which is the form in
which the termwise Tor-amplitude condition `TorAmplitude.HasTorAmplitudeIn` reads. -/
private noncomputable def extendRestrictTensorRightIso {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars f ≅
      tensorRight ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) :=
  extendRestrictTensorLeftIso f ≪≫ BraidedCategory.tensorLeftIsoTensorRight _

/-- Restriction of scalars along `A → B` of a bounded above complex of free `B`-modules is a
bounded above complex of flat `A`-modules, for `B` flat over `A`. -/
private lemma boundedAbove_and_isComplexOfFlats_restrictScalars
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (P : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ) (hPle : P.IsStrictlyLE n)
    (hPfree : ∀ j : ℤ, Module.Free B (P.X j)) :
    TorAmplitude.BoundedAbove ((CochainComplex.restrictScalars (algebraMap A B)).obj P) ∧
      TorAmplitude.IsComplexOfFlats
        ((CochainComplex.restrictScalars (algebraMap A B)).obj P) := by
  have := hPle
  refine ⟨⟨n, fun m hm => ?_⟩, fun j => ?_⟩
  · exact (ModuleCat.restrictScalars (algebraMap A B)).map_isZero
      (P.isZero_of_isStrictlyLE n m hm)
  · have : Module.Free B (P.X j) := hPfree j
    let _ : Module A (P.X j) := Module.compHom (P.X j) (algebraMap A B)
    let _ : IsScalarTower A B (P.X j) := IsScalarTower.of_compHom A B (P.X j)
    exact Module.Flat.trans A B (P.X j)

/-- A representative of `K` gives one of the complex of `A`-modules underlying `K`. -/
private noncomputable def restrictScalarsDerivedIso {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (K : DerivedCategory (ModuleCat.{u} B))
    (P : CochainComplex (ModuleCat.{u} B) ℤ) (e : DerivedCategory.Q.obj P ≅ K) :
    (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K ≅
      DerivedCategory.Q.obj ((CochainComplex.restrictScalars (algebraMap A B)).obj P) :=
  (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.mapIso e.symm ≪≫
    (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategoryFactors.app P

/-- A pseudo-coherent complex has a bounded above finite free representative `P` whose restriction
of scalars to `A`, a bounded above complex of flat modules representing the complex of `A`-modules
underlying `K`, satisfies any condition `T` imposed on such representatives. -/
private lemma exists_freeRepresentative_restrictScalars_of_pseudoCoherent
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (K : DerivedCategory (ModuleCat.{u} B)) (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (T : CochainComplex (ModuleCat.{u} A) ℤ → Prop)
    (hT : ∀ F : CochainComplex (ModuleCat.{u} A) ℤ, TorAmplitude.BoundedAbove F →
      TorAmplitude.IsComplexOfFlats F →
      Nonempty ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K ≅
        DerivedCategory.Q.obj F) → T F) :
    ∃ P : CochainComplex (ModuleCat.{u} B) ℤ,
      StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ K) ∧ ∃ n : ℤ, P.IsStrictlyLE n ∧
          (∀ j : ℤ, Module.Free B (P.X j)) ∧
            T ((CochainComplex.restrictScalars (algebraMap A B)).obj P) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hK
  obtain ⟨n, hn⟩ := hP.upperBound
  have hPfree : ∀ j : ℤ, Module.Free B (P.X j) := fun j => (hP.finiteFree j).2
  obtain ⟨hbdd, hflat⟩ :=
    boundedAbove_and_isComplexOfFlats_restrictScalars (A := A) P n hn hPfree
  exact ⟨P, hP, ⟨e⟩, n, hn, hPfree, hT _ hbdd hflat ⟨restrictScalarsDerivedIso K P e⟩⟩

/-- **Derived Tor amplitude gives the termwise condition on every flat representative.** If `L` has
Tor amplitude in `[a, b]` in the sense of [stacks 0652], against any derived tensor product
certified by a comparison to termwise tensoring and the universal property of a total left derived
functor, then every bounded above flat representative of `L` has termwise Tor amplitude in
`[a, b]`.

This is the form in which the Tor-amplitude hypotheses of [stacks 068X] and [stacks 09PC] below are
stated, and it is also the form in which [stacks 068V] states its Tor-amplitude conclusion. -/
theorem hasTorAmplitudeIn_flatRepresentative_of_hasTorAmplitude {R : Type u} [CommRing R]
    {derivedTensor : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R)}
    (comparison : ∀ N : ModuleCat.{u} R,
      DerivedCategory.Q ⋙ derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
        (TorAmplitude.tensorModuleRight N).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} R,
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
          (comparison N)
          (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (L : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ)
    (h : TorAmplitude.HasTorAmplitude derivedTensor comparison isLeftDerived L a b) :
    ∀ F : CochainComplex (ModuleCat.{u} R) ℤ, TorAmplitude.BoundedAbove F →
      TorAmplitude.IsComplexOfFlats F → Nonempty (L ≅ DerivedCategory.Q.obj F) →
        TorAmplitude.HasTorAmplitudeIn F a b := by
  rintro F hbounded hflat ⟨eF⟩
  refine (TorAmplitude.hasTorAmplitude_iff_termwise_of_flat comparison isLeftDerived F hbounded
    hflat a b).1 fun M i hi => ?_
  exact (h M i hi).of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
    ((derivedTensor.mapIso eF).symm.app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)))

end ChangeOfRings

/-! ### The derived fibre of a flat algebra along a factorization through the fibre ring -/

section Fibre

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **The projection formula at a fibre.** Let `C` be a `B`-algebra whose underlying `B`-module is
the base change `B ⊗_A N` of an `A`-module `N`. Restricted to `A`, the base change `C ⊗_B -` of a
`B`-module is the tensor product over `A` with `N` of its underlying `A`-module.

The isomorphism is the module-level projection formula `projectionFormulaIso` after interchanging
the two tensor factors by the symmetry of `ModuleCat B`. -/
private noncomputable def fibreComparisonNatIso (C : Type u) [CommRing C] [Algebra B C]
    (N : ModuleCat.{u} A)
    (eC : (ModuleCat.restrictScalars (algebraMap B C)).obj (ModuleCat.of C C) ≅
      (ModuleCat.extendScalars (algebraMap A B)).obj N) :
    ModuleCat.extendScalars (algebraMap B C) ⋙ ModuleCat.restrictScalars (algebraMap B C) ⋙
        ModuleCat.restrictScalars (algebraMap A B) ≅
      ModuleCat.restrictScalars (algebraMap A B) ⋙ tensorRight N := by
  have hproj : tensorRight ((ModuleCat.extendScalars (algebraMap A B)).obj N) ⋙
        ModuleCat.restrictScalars (algebraMap A B) ≅
      ModuleCat.restrictScalars (algebraMap A B) ⋙ tensorRight N :=
    NatIso.ofComponents (fun M => projectionFormulaIso (algebraMap A B) M N)
      (fun f => projectionFormulaIso_natural_left (algebraMap A B) N f)
  exact Functor.isoWhiskerRight (extendRestrictTensorLeftIso (algebraMap B C) ≪≫
      BraidedCategory.tensorLeftIsoTensorRight _ ≪≫
      (tensoringRight (ModuleCat.{u} B)).mapIso eC)
      (ModuleCat.restrictScalars (algebraMap A B)) ≪≫ hproj

/-- **The derived fibre of a pseudo-coherent complex over a flat algebra with a fibre of bounded
global dimension.** Let `A → B` be flat, let `C` be a `B`-algebra whose underlying `B`-module is
the base change of an `A`-module `N`, and let `C → κ` be a `B`-algebra map. Let `P` be a bounded
above complex of free `B`-modules whose termwise tensor product over `A` with `N` has cohomology
concentrated in `[a, b]`. If `C` has global dimension at most `d`, then the termwise base change of
`P` to `κ` has cohomology concentrated in `[a - d, b]`.

For a pseudo-coherent object of `D(B)` and a prime `q` of `B` the conclusion is the vanishing of
the cohomology of the derived fibre at `q` in the sense of [stacks 068U], which is what the
fibrewise criterion [stacks 068V] tests. -/
private theorem isZero_homology_extendScalars_of_fibre_globalDimension_le [Module.Flat A B]
    (C : Type u) [CommRing C] [Algebra B C] (d : ℕ) (hC : ringGlobalDimension C ≤ (d : ℕ))
    (N : ModuleCat.{u} A)
    (eC : (ModuleCat.restrictScalars (algebraMap B C)).obj (ModuleCat.of C C) ≅
      (ModuleCat.extendScalars (algebraMap A B)).obj N)
    (κ : Type u) [CommRing κ] [Algebra B κ] [Algebra C κ] [IsScalarTower B C κ]
    (P : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ) (hPle : P.IsStrictlyLE n)
    (hPfree : ∀ j : ℤ, Module.Free B (P.X j)) (a b : ℤ)
    (hamp : ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((TorAmplitude.tensorComplex
        ((CochainComplex.restrictScalars (algebraMap A B)).obj P) N).homology i))
    (i : ℤ) (hi : i < a - (d : ℤ) ∨ b < i) :
    IsZero ((((ModuleCat.extendScalars (algebraMap B κ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P).homology i) := by
  have := hPle
  -- The base change of `P` to the fibre ring is bounded above with free, hence flat, terms.
  have hEle : ((CochainComplex.extendScalars (algebraMap B C)).obj P).IsStrictlyLE n := by
    change CochainComplex.IsStrictlyLE
      (((ModuleCat.extendScalars (algebraMap B C)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) n
    infer_instance
  have := hEle
  have hEflat : ∀ j : ℤ,
      Module.Flat C (((CochainComplex.extendScalars (algebraMap B C)).obj P).X j) := fun j =>
    flat_extendScalars_of_free (algebraMap B C) (P.X j) (hPfree j)
  -- Its cohomology is concentrated in `[a, b]`, by the projection formula.
  have hE : ∀ j : ℤ, (j < a ∨ b < j) →
      IsZero (((CochainComplex.extendScalars (algebraMap B C)).obj P).homology j) := by
    intro j hj
    have h : IsZero (((CochainComplex.restrictScalars (algebraMap A B)).obj
        ((CochainComplex.restrictScalars (algebraMap B C)).obj
          ((CochainComplex.extendScalars (algebraMap B C)).obj P))).homology j) :=
      (hamp j hj).of_iso ((HomologicalComplex.homologyFunctor _ _ j).mapIso
        ((NatIso.mapHomologicalComplex (fibreComparisonNatIso C N eC)
          (ComplexShape.up ℤ)).app P))
    exact (isZero_homology_restrictScalars_iff (algebraMap B C) _ j).1
      ((isZero_homology_restrictScalars_iff (algebraMap A B) _ j).1 h)
  -- The global-dimension bound at `C` gives it termwise Tor amplitude in `[a - d, b]`.
  have hEamp := hasTorAmplitudeIn_of_ringGlobalDimension_le.{u, u} d hC
    ((CochainComplex.extendScalars (algebraMap B C)).obj P) hEflat a b hE
  -- Test that against `κ`, and compose the two base changes `B → C → κ`.
  have hz := hEamp ((ModuleCat.restrictScalars (algebraMap C κ)).obj (ModuleCat.of κ κ)) i hi
  have hz' : IsZero (((CochainComplex.extendScalars (algebraMap C κ)).obj
      ((CochainComplex.extendScalars (algebraMap B C)).obj P)).homology i) :=
    (isZero_homology_restrictScalars_iff (algebraMap C κ) _ i).1
      (hz.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso
        ((NatIso.mapHomologicalComplex (extendRestrictTensorRightIso (algebraMap C κ))
          (ComplexShape.up ℤ)).app ((CochainComplex.extendScalars (algebraMap B C)).obj P))))
  exact hz'.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso
    (StacksDraft.TorAmplitude.FaithfullyFlat.extendComplexTowerIso B C κ P))

end Fibre

/-! ### Perfectness over a flat algebra with fibres of bounded global dimension -/

section FibreGlobalDimension

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The fibre ring `B ⊗_A κ(p)`, as a `B`-module, is the base change of `κ(p)`. -/
private noncomputable def fibreRingIso (p : PrimeSpectrum A) :
    (ModuleCat.restrictScalars
        (algebraMap B (TensorProduct A B p.asIdeal.ResidueField))).obj
      (ModuleCat.of (TensorProduct A B p.asIdeal.ResidueField)
        (TensorProduct A B p.asIdeal.ResidueField)) ≅
      (ModuleCat.extendScalars (algebraMap A B)).obj
        (ModuleCat.of A p.asIdeal.ResidueField) :=
  LinearEquiv.toModuleIso
    ((StacksDraft.TorAmplitude.FaithfullyFlat.restrictScalarsSelfEquiv B (TensorProduct A B
      p.asIdeal.ResidueField)).trans
      (StacksDraft.TorAmplitude.FaithfullyFlat.extendScalarsCarrierEquiv A B (ModuleCat.of A
        p.asIdeal.ResidueField)).symm)

/-- The canonical map `B ⊗_A κ(p) → κ(q)` from the fibre at the preimage `p` of a prime `q` of `B`
to the residue field at `q`. -/
private noncomputable def fibreToResidueField (q : PrimeSpectrum B) :
    TensorProduct A B ((PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField) →+*
      q.asIdeal.ResidueField :=
  (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A B q.asIdeal.ResidueField)
    (Ideal.ResidueField.mapₐ (PrimeSpectrum.comap (algebraMap A B) q).asIdeal q.asIdeal
      (Algebra.ofId A B) rfl) (fun _ _ => Commute.all ..)).toRingHom

/-- `fibreToResidueField` is a map of `B`-algebras. -/
private theorem fibreToResidueField_apply_algebraMap (q : PrimeSpectrum B) (x : B) :
    (fibreToResidueField q) (algebraMap B (TensorProduct A B
        ((PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField)) x) =
      algebraMap B q.asIdeal.ResidueField x := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp only [fibreToResidueField, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  rfl

/-- **Stacks 068X.** Let `A → B` be a flat map of commutative rings, let `a, b : ℤ` and let `d ≥ 0`
be an integer such that for every prime `p` of `A` the fibre ring `B ⊗_A κ(p)` has global dimension
at most `d`. Let `K` be an object of the derived category of `B`-modules which is pseudo-coherent
as a complex of `B`-modules and has Tor amplitude in `[a, b]` as a complex of `A`-modules. Then `K`
is perfect as a complex of `B`-modules with Tor amplitude in `[a - d, b]`.

Tor amplitude is recorded as in [stacks 068V]: by a flat representative supported in the window,
which by [stacks 0654] is exactly Tor amplitude, together with the termwise condition on every
bounded above flat representative. The hypothesis over `A` is the same condition for the complex of
`A`-modules underlying `K`, and `hasTorAmplitudeIn_flatRepresentative_of_hasTorAmplitude` derives
it from derived Tor amplitude against any certified derived tensor product. -/
@[stacks 068X, sga "6 III 4.4" "(ii), special case"]
theorem isPerfect_and_torAmplitude_of_flat_of_fibre_globalDimension_le [Module.Flat A B]
    (a b : ℤ) (d : ℕ)
    (hfibre : ∀ p : PrimeSpectrum A,
      ringGlobalDimension (TensorProduct A B p.asIdeal.ResidueField) ≤ (d : ℕ))
    (K : DerivedCategory (ModuleCat.{u} B))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hamp : ∀ F : CochainComplex (ModuleCat.{u} A) ℤ, TorAmplitude.BoundedAbove F →
      TorAmplitude.IsComplexOfFlats F →
      Nonempty ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K ≅
        DerivedCategory.Q.obj F) → TorAmplitude.HasTorAmplitudeIn F a b) :
    IsPerfect K ∧ HasFlatRepresentative.{u, u} K (a - (d : ℤ)) b ∧
      ∀ E : CochainComplex (ModuleCat.{u} B) ℤ, TorAmplitude.BoundedAbove E →
        TorAmplitude.IsComplexOfFlats E → Nonempty (K ≅ DerivedCategory.Q.obj E) →
          TorAmplitude.HasTorAmplitudeIn E (a - (d : ℤ)) b := by
  refine (isPerfect_and_torAmplitude_iff_fibreCohomologyVanishes.{u, u} K hK
    (a - (d : ℤ)) b).1.2 ?_
  obtain ⟨P, hP, he, n, hn, hPfree, hampP⟩ :=
    exists_freeRepresentative_restrictScalars_of_pseudoCoherent K hK _ hamp
  intro q i hi
  refine ⟨P, hP, he, ?_⟩
  let p := PrimeSpectrum.comap (algebraMap A B) q
  let _ : Algebra (TensorProduct A B p.asIdeal.ResidueField) q.asIdeal.ResidueField :=
    (fibreToResidueField q).toAlgebra
  have _ : IsScalarTower B (TensorProduct A B p.asIdeal.ResidueField)
      q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun x => (fibreToResidueField_apply_algebraMap q x).symm
  exact isZero_homology_extendScalars_of_fibre_globalDimension_le
    (TensorProduct A B p.asIdeal.ResidueField) d (hfibre p)
    (ModuleCat.of A p.asIdeal.ResidueField) (fibreRingIso p) q.asIdeal.ResidueField P n hn hPfree
    a b (hampP (ModuleCat.of A p.asIdeal.ResidueField)) i hi

end FibreGlobalDimension

/-! ### Perfectness over a flat local extension with regular closed fibre -/

section RegularClosedFibre

open IsLocalRing

variable {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]

/-- A regular local ring of dimension at most `d` has global dimension at most `d`, by
[stacks 00O7]. -/
private lemma ringGlobalDimension_le_of_isRegularLocalRing (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (d : ℕ) (hd : ringKrullDim R ≤ (d : WithBot ℕ∞)) :
    ringGlobalDimension R ≤ (d : ℕ) := by
  refine iSup_le fun M ↦ ?_
  have := (IsRegularLocalRing.exists_leftResolution_free_finite_and_hasProjectiveDimensionLE
    hd).2 M
  exact (CategoryTheory.projectiveDimension_le_iff M d).2 inferInstance

/-- The closed fibre `B/m_A B` is the base change `B ⊗_A κ(m_A)` of the residue field of `A`. -/
private noncomputable def closedFibreAlgEquiv :
    (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) ≃ₐ[B]
      TensorProduct A B (maximalIdeal A).ResidueField :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (maximalIdeal A)).trans
    (Algebra.TensorProduct.congr AlgEquiv.refl
      (AlgEquiv.ofBijective (IsScalarTower.toAlgHom A (A ⧸ maximalIdeal A)
        (maximalIdeal A).ResidueField)
        (maximalIdeal A).bijective_algebraMap_quotient_residueField))

/-- The closed fibre, as a `B`-module, is the base change of the residue field of `A`. -/
private noncomputable def closedFibreIso :
    (ModuleCat.restrictScalars
        (algebraMap B (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)))).obj
      (ModuleCat.of (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))
        (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))) ≅
      (ModuleCat.extendScalars (algebraMap A B)).obj
        (ModuleCat.of A (maximalIdeal A).ResidueField) :=
  LinearEquiv.toModuleIso
    ((StacksDraft.TorAmplitude.FaithfullyFlat.restrictScalarsSelfEquiv B
        (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))).trans
      ((closedFibreAlgEquiv (A := A) (B := B)).toLinearEquiv.trans
        (StacksDraft.TorAmplitude.FaithfullyFlat.extendScalarsCarrierEquiv A B
          (ModuleCat.of A (maximalIdeal A).ResidueField)).symm))

/-- **Stacks 09PC.** Let `A → B` be a flat local homomorphism of local rings, let `a, b : ℤ` and
let `d ≥ 0` be an integer such that the closed fibre `B/m_A B` is regular of dimension `d`. Let `K`
be an object of the derived category of `B`-modules which is pseudo-coherent as a complex of
`B`-modules and whose derived fibre `K ⊗_A^L κ(m_A)` has cohomology only in the degrees `[a, b]`.
Then `K` is perfect as a complex of `B`-modules with Tor amplitude in `[a - d, b]`.

The source states the hypothesis over `A` as Tor amplitude in `[a, b]` and remarks that the weaker
condition on the derived fibre suffices; it is that weaker hypothesis which is used here. Tor
amplitude in the conclusion is recorded as in [stacks 068V]: by a flat representative supported in
the window, which by [stacks 0654] is exactly Tor amplitude, together with the termwise condition
on every bounded above flat representative. The derived fibre over `A` is computed on a bounded
above flat representative of the complex of `A`-modules underlying `K`, which is what the termwise
tensor product with `κ(m_A)` of such a representative is. -/
@[stacks 09PC]
theorem isPerfect_and_torAmplitude_of_flat_local_of_regular_closedFibre [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B] (a b : ℤ) (d : ℕ)
    [IsRegularLocalRing (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))]
    (hdim : ringKrullDim (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) = (d : WithBot ℕ∞))
    (K : DerivedCategory (ModuleCat.{u} B))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hfibre : ∀ F : CochainComplex (ModuleCat.{u} A) ℤ, TorAmplitude.BoundedAbove F →
      TorAmplitude.IsComplexOfFlats F →
      Nonempty ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K ≅
        DerivedCategory.Q.obj F) →
      ∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((TorAmplitude.tensorComplex F
          (ModuleCat.of A (maximalIdeal A).ResidueField)).homology i)) :
    IsPerfect K ∧ HasFlatRepresentative.{u, u} K (a - (d : ℤ)) b ∧
      ∀ E : CochainComplex (ModuleCat.{u} B) ℤ, TorAmplitude.BoundedAbove E →
        TorAmplitude.IsComplexOfFlats E → Nonempty (K ≅ DerivedCategory.Q.obj E) →
          TorAmplitude.HasTorAmplitudeIn E (a - (d : ℤ)) b := by
  obtain ⟨hcriterion, hmaximal⟩ :=
    isPerfect_and_torAmplitude_iff_fibreCohomologyVanishes.{u, u} K hK (a - (d : ℤ)) b
  refine hcriterion.2 (hmaximal.2 ?_)
  obtain ⟨P, hP, he, n, hn, hPfree, hfibreP⟩ :=
    exists_freeRepresentative_restrictScalars_of_pseudoCoherent K hK _ hfibre
  intro m i hi
  obtain rfl : m = ⟨maximalIdeal B, inferInstance⟩ := Subsingleton.elim _ _
  refine ⟨P, hP, he, ?_⟩
  -- The closed fibre maps to the residue field of `B`, over `B`.
  have hker : Ideal.map (algebraMap A B) (maximalIdeal A) ≤
      RingHom.ker (algebraMap B (maximalIdeal B).ResidueField) := by
    rw [(maximalIdeal B).ker_algebraMap_residueField]
    exact IsLocalRing.map_maximalIdeal_le (algebraMap A B)
  let _ : Algebra (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))
      (maximalIdeal B).ResidueField :=
    (Ideal.Quotient.lift _ (algebraMap B (maximalIdeal B).ResidueField) hker).toAlgebra
  have _ : IsScalarTower B (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))
      (maximalIdeal B).ResidueField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact isZero_homology_extendScalars_of_fibre_globalDimension_le
    (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) d
    (ringGlobalDimension_le_of_isRegularLocalRing _ d hdim.le)
    (ModuleCat.of A (maximalIdeal A).ResidueField) closedFibreIso
    (maximalIdeal B).ResidueField P n hn hPfree a b hfibreP i hi

end RegularClosedFibre

end StacksDraft.Perfect

end
