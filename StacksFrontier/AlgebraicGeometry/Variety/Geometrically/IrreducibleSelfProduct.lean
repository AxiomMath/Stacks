module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleLocal
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Tower

/-!
# Geometric irreducibility from the self-product

A scheme over a field is geometrically irreducible if and only if its fibre product with itself
over that field is irreducible.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_iff_irreducibleSpace_self_pullback` characterizes
  geometric irreducibility using the self-product.

## Implementation notes

The structure morphism to the spectrum of the field is supplied explicitly, and the self-product
is the categorical pullback of that morphism along itself.

The reduction to algebra happens in two steps. First the question is localized to an affine open
by the local criterion for geometric irreducibility, which turns the self-product of the scheme
into the spectrum of `A ⊗[k] A` for `A` the sections over that open. Then irreducibility of that
spectrum is propagated down the nilradical quotient and up the fraction field, where geometric
irreducibility is equivalent to the separable closure of `k` inside it being trivial.

## References

* [Stacks Project, Tag 0H8G](https://stacks.math.columbia.edu/tag/0H8G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

/-- A scheme whose self-product over a base is irreducible is itself irreducible, because the
diagonal splits the first projection. -/
private lemma irreducibleSpace_of_irreducible_self_pullback
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IrreducibleSpace ↥(pullback f f)] : IrreducibleSpace X := by
  have hsurj : Function.Surjective (pullback.fst f f) := fun x =>
    ⟨pullback.diagonal f x, congrArg (fun g : X ⟶ X => g x) (pullback.diagonal_fst f)⟩
  exact hsurj.irreducibleSpace (pullback.fst f f).continuous

/-- Restricting both legs of a fibre product to open subschemes preserves irreducibility, as
long as the restricted product is nonempty. -/
private lemma irreducibleSpace_pullback_open_both
    {S X Y X' Y' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (i : X' ⟶ X) (j : Y' ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
    [Nonempty ↥(pullback (i ≫ f) (j ≫ g))] [IrreducibleSpace ↥(pullback f g)] :
    IrreducibleSpace ↥(pullback (i ≫ f) (j ≫ g)) := by
  let m := pullback.map (i ≫ f) (j ≫ g) f g i j (𝟙 _) (by simp) (by simp)
  have : IsOpenImmersion m := by
    dsimp [m]
    infer_instance
  exact m.isOpenEmbedding.irreducibleSpace

/-- A tensor product of two surjections with nilpotent kernels induces a homeomorphism of prime
spectra, so irreducibility of either tensor product determines the other. -/
private lemma irreducibleSpace_tensorMap_iff
    {k A B C D : Type*} [Field k] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k D]
    (f : A →ₐ[k] B) (g : C →ₐ[k] D)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hfk : RingHom.ker f.toRingHom ≤ nilradical A)
    (hgk : RingHom.ker g.toRingHom ≤ nilradical C) :
    IrreducibleSpace (PrimeSpectrum (A ⊗[k] C)) ↔
      IrreducibleSpace (PrimeSpectrum (B ⊗[k] D)) := by
  let ψ := (Algebra.TensorProduct.map f g).toRingHom
  have hker : RingHom.ker ψ ≤ nilradical (A ⊗[k] C) := by
    change RingHom.ker (Algebra.TensorProduct.map f g) ≤ _
    rw [Algebra.TensorProduct.map_ker (f := f) (g := g) hf hg]
    apply sup_le
    · calc
        (RingHom.ker f.toRingHom).map
            (Algebra.TensorProduct.includeLeft (R := k) (A := A) (B := C)).toRingHom
          ≤ (nilradical A).map
              (Algebra.TensorProduct.includeLeft (R := k) (A := A) (B := C)).toRingHom :=
                Ideal.map_mono hfk
        _ ≤ nilradical (A ⊗[k] C) := by
          simpa [nilradical] using
            (Ideal.map_radical_le
              (f := (Algebra.TensorProduct.includeLeft (R := k) (A := A) (B := C)).toRingHom)
              (I := (⊥ : Ideal A)))
    · calc
        (RingHom.ker g.toRingHom).map
            (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := C)).toRingHom
          ≤ (nilradical C).map
              (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := C)).toRingHom :=
                Ideal.map_mono hgk
        _ ≤ nilradical (A ⊗[k] C) := by
          simpa [nilradical] using
            (Ideal.map_radical_le
              (f := (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := C)).toRingHom)
              (I := (⊥ : Ideal C)))
  have hsurj : Function.Surjective ψ := by
    change Function.Surjective (Algebra.TensorProduct.map f g)
    exact Algebra.TensorProduct.map_surjective (f := f) (g := g) hf hg
  have hpow : ∀ x : B ⊗[k] D, ∃ n > 0, x ^ n ∈ ψ.range := by
    intro x
    obtain ⟨y, rfl⟩ := hsurj x
    exact ⟨1, one_pos, y, by simp⟩
  obtain ⟨e, he⟩ := isHomeomorph_iff_exists_homeomorph.mp
    (PrimeSpectrum.isHomeomorph_comap ψ hpow hker)
  exact e.symm.irreducibleSpace_iff

/-- Irreducibility of `S ⊗[k] A` passes to `S ⊗[k] A[1/b]` for a nonzero `b` in a domain `A`,
since the latter is an open subscheme of the former. -/
private lemma irreducibleSpace_tensor_away {k S A : Type*} [Field k] [CommRing S] [Nontrivial S]
    [CommRing A] [IsDomain A] [Algebra k S] [Algebra k A] (b : A) (hb : b ≠ 0)
    (h : IrreducibleSpace (PrimeSpectrum (S ⊗[k] A))) :
    IrreducibleSpace (PrimeSpectrum (S ⊗[k] Localization.Away b)) := by
  let C := Localization.Away ((1 : S) ⊗ₜ[k] b)
  let e : S ⊗[k] Localization.Away b ≃ₐ[S] C :=
    IsLocalization.Away.tensorProductEquivTMulRight k S b _
  have : IsDomain (Localization.Away b) := IsLocalization.Away.isDomain _ hb
  have : Nontrivial (S ⊗[k] Localization.Away b) := Module.FaithfullyFlat.lTensor_nontrivial k S _
  have : Nontrivial C := e.toRingEquiv.symm.nontrivial
  have : Nonempty (PrimeSpectrum C) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal C
    exact ⟨⟨m, hm.isPrime⟩⟩
  exact (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).irreducibleSpace_iff.mpr
    (PrimeSpectrum.localization_away_isOpenEmbedding C ((1 : S) ⊗ₜ[k] b)).irreducibleSpace

/-- Irreducibility of the self-product of a domain passes to the self-product of a localization
away from a nonzero element, since that localization is an open subscheme of the product. -/
private lemma irreducibleSpace_away_tensor_self {k A : Type*} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] (b : A) (hb : b ≠ 0)
    (h : IrreducibleSpace (PrimeSpectrum (A ⊗[k] A))) :
    IrreducibleSpace (PrimeSpectrum (Localization.Away b ⊗[k] Localization.Away b)) := by
  have : IsDomain (Localization.Away b) := IsLocalization.Away.isDomain _ hb
  have hBA : IrreducibleSpace (PrimeSpectrum (Localization.Away b ⊗[k] A)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.comm k A (Localization.Away b)).toRingEquiv).irreducibleSpace_iff.mp
      (irreducibleSpace_tensor_away b hb h)
  exact irreducibleSpace_tensor_away b hb hBA

/-- A finite separable extension whose self-tensor product has irreducible spectrum is trivial:
that tensor product is a field isomorphic to the extension, and comparing degrees forces the
extension to have degree one. -/
private lemma finrank_eq_one_of_irred_self (k E : Type*) [Field k] [Field E]
    [Algebra k E] [FiniteDimensional k E] [Algebra.IsSeparable k E]
    (h : IrreducibleSpace (PrimeSpectrum (E ⊗[k] E))) : Module.finrank k E = 1 := by
  have : Algebra.FormallyEtale k E := .of_isSeparable k E
  let B := E ⊗[k] E
  let : Algebra E B := Algebra.TensorProduct.leftAlgebra
  have hred : _root_.IsReduced B := Algebra.FormallyUnramified.isReduced_of_field E B
  have hbot : (⊥ : Ideal B).IsPrime := by
    rw [← nilradical_eq_bot_iff.mpr hred]
    exact PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp h
  have hdom : IsDomain B := .of_bot_isPrime _
  have hfield : IsField B := Algebra.TensorProduct.isField_of_isAlgebraic k E E
    (Or.inl (Algebra.IsIntegral.isAlgebraic (R := k)))
  let : Field B := hfield.toField
  let φ : B →ₐ[E] E :=
    Algebra.TensorProduct.lift (AlgHom.id E E) (AlgHom.id k E) fun x y => Commute.all x y
  have hsurj : Function.Surjective φ := by
    intro x
    refine ⟨Algebra.TensorProduct.includeLeft (R := k) (S := E) (A := E) (B := E) x, ?_⟩
    change (AlgHom.id E E x) * (AlgHom.id k E 1) = x
    simp
  have hequiv : B ≃ₐ[E] E := AlgEquiv.ofBijective φ ⟨RingHom.injective φ.toRingHom, hsurj⟩
  have hdim : Module.finrank k B = Module.finrank k E :=
    hequiv.toLinearEquiv.restrictScalars k |>.finrank_eq
  rw [Module.finrank_tensorProduct] at hdim
  have hp : 0 < Module.finrank k E := Module.finrank_pos
  nlinarith

/-- If the self-tensor product of a domain over `k` has irreducible spectrum, then the separable
closure of `k` in its fraction field is trivial: a separable element generates a finite separable
subextension, which the previous lemma forces to be trivial. -/
private theorem sepClosure_eq_bot_of_irred_selfProduct
    (k A K : Type*) [Field k] [CommRing A] [IsDomain A]
    [Field K] [Algebra k A] [Algebra A K] [Algebra k K] [IsScalarTower k A K]
    [IsFractionRing A K]
    (h : IrreducibleSpace (PrimeSpectrum (A ⊗[k] A))) : separableClosure k K = ⊥ := by
  rw [eq_bot_iff, IsConcreteLE.le_iff]
  intro α hα
  have hsep : IsSeparable k α := mem_separableClosure_iff.mp hα
  let E := IntermediateField.adjoin k ({α} : Set K)
  have : FiniteDimensional k E := IntermediateField.adjoin.finiteDimensional hsep.isIntegral
  have : Algebra.IsSeparable k E :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable k K).mpr hsep
  obtain ⟨a, y, hay⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors A) α
  let b : A := y
  have hb : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp y.2
  let B := Localization.Away b
  let z : Submonoid.powers b := ⟨b, Submonoid.mem_powers b⟩
  let w : B := IsLocalization.mk' B a z
  let fAK : A →ₐ[A] K := Algebra.ofId A K
  have hbk : IsUnit (fAK b) := isUnit_iff_ne_zero.mpr fun heq =>
    hb (IsFractionRing.injective A K (by simpa [fAK] using heq))
  have hloc : ∀ y : Submonoid.powers b, IsUnit (fAK y) := by
    intro y
    obtain ⟨n, hn⟩ := y.2
    rw [← hn]
    simpa only [map_pow] using hbk.pow n
  let jA : B →ₐ[A] K := IsLocalization.liftAlgHom (f := fAK) hloc
  let j : B →ₐ[k] K := jA.restrictScalars k
  have hcross : (algebraMap A K) a = α * algebraMap A K b := by
    simpa [b, mul_comm] using IsLocalization.mk'_eq_iff_eq_mul.mp hay
  have hαw : j w = α := by
    change IsLocalization.lift hloc (IsLocalization.mk' B a z) = α
    rw [IsLocalization.lift_mk'_spec hloc a α z]
    simpa [fAK, z, b, mul_comm] using hcross
  have hαrange : α ∈ j.range := ⟨w, hαw⟩
  have hEsub : E.toSubalgebra ≤ j.range := by
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      hsep.isIntegral.isAlgebraic]
    exact Algebra.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hαrange)
  let q : E →ₐ[k] ↥j.range := AlgHom.codRestrict E.val j.range fun x => hEsub x.2
  have hAB : Function.Injective (algebraMap A B) :=
    IsLocalization.injectiveₛ (M := Submonoid.powers b) B fun c hc =>
      isRegular_iff_mem_nonZeroDivisors.mpr
        (powers_le_nonZeroDivisors_of_noZeroDivisors hb hc)
  have hinjA : Function.Injective jA := by
    change Function.Injective (IsLocalization.lift hloc)
    rw [IsLocalization.lift_injective_iff (M := Submonoid.powers b) (S := B) hloc]
    exact fun x y => ⟨fun hxy => congrArg fAK (hAB hxy), fun hxy => congrArg (algebraMap A B)
      (IsFractionRing.injective A K (by simpa [fAK] using hxy))⟩
  let e : B ≃ₐ[k] ↥j.range := AlgEquiv.ofInjective j hinjA
  let i : E →ₐ[k] B := e.symm.toAlgHom.comp q
  have hi : Function.Injective i := e.symm.injective.comp (RingHom.injective q.toRingHom)
  have hEE : IrreducibleSpace (PrimeSpectrum (E ⊗[k] E)) := by
    apply Stacks.Irreducibility.TrivialSepClosure.irreducibleSpace_primeSpectrum_of_injective
      (Algebra.TensorProduct.map i i).toRingHom ?_ (irreducibleSpace_away_tensor_self b hb h)
    have hlin : Function.Injective (TensorProduct.map i.toLinearMap i.toLinearMap) :=
      TensorProduct.map_injective_of_flat_flat' _ _ hi hi
    intro x y hxy
    exact hlin (by
      simpa [← AlgHom.toLinearMap_apply, Algebra.TensorProduct.toLinearMap_map,
        TensorProduct.AlgebraTensorModule.map_eq] using hxy)
  rw [← IntermediateField.finrank_eq_one_iff.mp (finrank_eq_one_of_irred_self k E hEE)]
  exact IntermediateField.mem_adjoin_simple_self k α

/-- An algebra whose self-tensor product over `k` has irreducible spectrum is geometrically
irreducible over `k`. -/
private theorem isGeometricallyIrreducible_of_irreducible_self_tensor
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (h : IrreducibleSpace (PrimeSpectrum (A ⊗[k] A))) :
    Algebra.IsGeometricallyIrreducible k A := by
  let I : Ideal A := nilradical A
  let R := A ⧸ I
  let q : A →ₐ[k] R := Ideal.Quotient.mkₐ k I
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hqker : RingHom.ker q.toRingHom ≤ nilradical A := by
    intro x (hx : Ideal.Quotient.mkₐ k I x = 0)
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [Ideal.Quotient.mkₐ_eq_mk] using hx)
  have hRR : IrreducibleSpace (PrimeSpectrum (R ⊗[k] R)) :=
    (irreducibleSpace_tensorMap_iff q q hq hq hqker hqker).mp h
  have hRtensor_ne : Nonempty (PrimeSpectrum (R ⊗[k] R)) := by
    let : IrreducibleSpace (PrimeSpectrum (R ⊗[k] R)) := hRR
    obtain ⟨p, _⟩ := (IrreducibleSpace.isIrreducible_univ (PrimeSpectrum (R ⊗[k] R))).nonempty
    exact ⟨p⟩
  have hRne : Nonempty (PrimeSpectrum R) := by
    obtain ⟨p⟩ := hRtensor_ne
    exact ⟨PrimeSpectrum.comap
      (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := R) (B := R)).toRingHom p⟩
  let : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp hRne
  have hinc : Function.Injective
      (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := R) (B := R)) := by
    intro x y hxy
    exact (Algebra.TensorProduct.includeLeft_injective (S := k)
      (algebraMap k R).injective) hxy
  have hRspec : IrreducibleSpace (PrimeSpectrum R) :=
    Stacks.Irreducibility.TrivialSepClosure.irreducibleSpace_primeSpectrum_of_injective
      (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := R) (B := R)).toRingHom hinc hRR
  have : _root_.IsReduced R :=
    (Ideal.isRadical_iff_quotient_reduced I).mp (Ideal.radical_isRadical _)
  have hbot : (⊥ : Ideal R).IsPrime := by
    rw [← nilradical_eq_bot_iff.mpr (show _root_.IsReduced R from inferInstance)]
    exact PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp hRspec
  let : IsDomain R := .of_bot_isPrime _
  let K := FractionRing R
  have hsc : separableClosure k K = ⊥ :=
    sepClosure_eq_bot_of_irred_selfProduct k R K hRR
  have hK : Algebra.IsGeometricallyIrreducible k K := by
    change GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    exact (separableClosure.eq_bot_iff_geometricallyIrreducible k K).mp hsc
  let : Algebra.IsGeometricallyIrreducible k K := hK
  have hRgeom : Algebra.IsGeometricallyIrreducible k R :=
    Stacks.Irreducibility.TrivialSepClosure.isGeometricallyIrreducible_of_injective
      (k := k) (A := R) (B := K)
      ((Algebra.ofId R K : R →ₐ[R] K).restrictScalars k)
      (IsFractionRing.injective R K)
  rw [Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct]
  intro F _ _
  refine (irreducibleSpace_tensorMap_iff q (AlgHom.id k F) hq Function.surjective_id
    hqker ?_).mpr
    ((Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct
      k R).mp hRgeom F)
  intro x hx
  change x = 0 at hx
  simp [hx]

/-- **Stacks Project, Tag 0H8G.** A scheme over a field is geometrically irreducible
if and only if its self-product over the field is irreducible. -/
@[stacks 0H8G, ega "IV 4.5.8" "(i), special case"]
public theorem geometricallyIrreducible_iff_irreducibleSpace_self_pullback
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    GeometricallyIrreducible f ↔ IrreducibleSpace ↥(pullback f f) := by
  constructor
  · intro hf
    have := GeometricallyIrreducible.irreducibleSpace f f.isOpenMap
    infer_instance
  · intro h
    have := irreducibleSpace_of_irreducible_self_pullback k X f
    apply ((geometricallyIrreducible_tfae_local k f).out 2 1).mp
    refine ⟨⟨Classical.choice inferInstance⟩, ?_⟩
    intro U hU
    let A := Γ(X, U.1)
    let : Algebra k A :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    change Algebra.IsGeometricallyIrreducible k A
    let g := Spec.map (CommRingCat.ofHom (algebraMap k A))
    have hg : g = U.2.fromSpec ≫ f := by
      change Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫
        f.appLE ⊤ U.1 (by simp)) = U.2.fromSpec ≫ f
      rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) U.2 (by simp),
        Spec.map_comp, IsAffineOpen.fromSpec_top]
      congr 1
      rw [← cancel_mono (Spec (.of k)).toSpecΓ]
      simp
    obtain ⟨x, hx⟩ := hU
    have : Nonempty ↥(pullback (U.2.fromSpec ≫ f) (U.2.fromSpec ≫ f)) := by
      rw [← hg]
      exact ⟨pullback.diagonal g (U.2.isoSpec.hom ⟨x, hx⟩)⟩
    have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    have hG : IrreducibleSpace ↥(pullback g g) := by
      rw [hg]
      exact irreducibleSpace_pullback_open_both f f U.2.fromSpec U.2.fromSpec
    exact isGeometricallyIrreducible_of_irreducible_self_tensor k A
      ((pullbackSpecIso k A A).schemeIsoToHomeo.irreducibleSpace_iff.mp hG)

end AlgebraicGeometry
