module

import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.RingHom.Etale

public import Mathlib.RingTheory.Ideal.Height
import StacksFrontier.RingTheory.Module.LocallyFree.FiniteProjective
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Étale criterion for a finite type map from a polynomial ring over a field

Let `k` be a field, let `A` be a `k`-algebra of finite type and let `a₁, …, aₙ` be elements of
`A`. They determine the `k`-algebra map `φ : k[x₁, …, xₙ] → A`, `xᵢ ↦ aᵢ`, that is,
`MvPolynomial.aeval a`. Then `φ` is étale if and only if

* (a) the local rings of `A` at its maximal ideals all have dimension `n`, and
* (b) the differentials `d(a₁), …, d(aₙ)` generate `Ω[A⁄k]` as an `A`-module.

Both conditions are conditions on `A` and on the elements `aᵢ` alone; neither mentions the
polynomial ring. Condition (a) does not mention the `aᵢ` at all, so whether `φ` is étale depends on
`a₁, …, aₙ` only through the differentials `d(aᵢ) ∈ Ω[A⁄k]`.

## Main results

* `MvPolynomial.etale_aeval_iff_height_eq_and_span_range_D_eq_top`: the criterion, Stacks 0G1C.
* `Stacks.Etale.PolynomialRingCriterion.solution`: the same statement, in the namespace of its
  proof.

## Implementation notes

The étale hypothesis is on the ring map `φ` itself, `RingHom.Etale`, applied to
`MvPolynomial.aeval a`, rather than on an abstract algebra structure
`Algebra (MvPolynomial (Fin n) k) A` in a scalar tower over `k`. The source's map is given by
where it sends the variables, and the criterion's intended use compares two maps `φ, φ'` out of
the same polynomial ring into the *same* ring `A` (Fundamental Groups, Lemma 0G1F). With the
family `a : Fin n → A` as an explicit argument that is a change of argument, whereas in the tower
form it would be a second algebra instance on `A`.

Condition (a) is spelled `m.height = n` for every maximal ideal `m` of `A`. This is Mathlib's
form of "the local ring `Aₘ` has dimension `n`": `IsLocalization.AtPrime.ringKrullDim_eq_height`
says `ringKrullDim (Localization.AtPrime m) = m.height`, so no generality is lost, and the height
lives in `ℕ∞` rather than in `WithBot ℕ∞`. Note that `Ideal.height` of a prime ideal is its
codimension, the supremum of the lengths of chains of primes below it.

The finiteness hypothesis is `Algebra.FiniteType k A`, finite type over the field, rather than
finite type of `φ`. The two are equivalent: `A` is generated over the image of `k[x₁, …, xₙ]` by a
set of elements if and only if it is generated over `k` by that set together with `a₁, …, aₙ`. The
form over `k` is chosen because it does not mention `a`, and because `Algebra.FiniteType` is a
class and can be found by instance search.

Both directions are organised around the base change map
`mapBaseChange k k[x] A : A ⊗_{k[x]} Ω[k[x]⁄k] → Ω[A⁄k]`, whose source is free on the `1 ⊗ dxᵢ`
and whose range is the span of the `d(aᵢ)`: condition (b) says exactly that it is surjective.
Surjectivity is in turn `Ω[A⁄k[x]] = 0`, by the Jacobi–Zariski sequence at the level of
differentials, and that is one half of formal étaleness.

The other half, the vanishing of `H¹L_{A/k[x]}`, uses, instead of the miracle flatness of
Lemma 00R4 of the source, the Jacobi–Zariski exact sequence
`H¹L_{A/k} → H¹L_{A/k[x]} → A ⊗_{k[x]} Ω[k[x]⁄k] → Ω[A⁄k]`,
whose left-hand term vanishes for `A` smooth over `k`.  This is
`formallyEtale_of_bijective_mapBaseChange`, and it is what carries the criterion: what has to be
supplied is that the base change map is *injective*, which holds because it is a surjection from a
free module of rank `n` onto a projective module whose fibre at every maximal ideal has dimension
`n`.  The Cohen–Macaulay theory of Lemmas 00NQ, 00R4 and the flat descent of Lemma 00HT are not
needed, and the two directions share all of their machinery.

Condition (a) enters through Lemma 00TT, whose three equivalent conditions are smoothness of `A`
over `k` at a point, the inequality `dim_κ(m) (κ(m) ⊗_A Ω[A⁄k]) ≤ dim_m Spec A`, and the
corresponding equality; Lemma 00OT identifies `dim_m Spec A` with `m.height` at a *closed* point,
which is `isSmoothAt_tfae_height`.  Both directions of the criterion use that equivalence, in
opposite senses: (a) and (b) give the inequality, hence smoothness at every closed point; and
étaleness gives smoothness, hence the equality, hence (a).

Smoothness at the closed points is smoothness (`formallySmooth_iff_forall_isSmoothAt`) because for
`A` of finite presentation the smooth locus is open, so its complement is a zero locus `V(s)`, and
a nonempty `V(s)` contains a closed point: a prime containing `s` lies in a maximal ideal, which
then contains `s` too.  The same observation is what turns Nakayama's lemma into
`subsingleton_of_forall_subsingleton_residueField_tensor`, the vanishing of a finite module all of
whose fibres at maximal ideals vanish, its support being closed.

## References

* [Stacks Project, Tag 0G1C](https://stacks.math.columbia.edu/tag/0G1C)
-/

@[expose] public section

namespace Stacks.Etale.PolynomialRingCriterion

open MvPolynomial _root_.TensorProduct _root_.KaehlerDifferential TopologicalSpace

/-! ### Closed points of an affine scheme -/

/-- **A closed subset of `Spec A` containing no closed point is empty.** -/
private theorem eq_empty_of_isClosed_of_forall_isMaximal_notMem {A : Type*} [CommRing A]
    {Z : Set (PrimeSpectrum A)} (hZ : IsClosed Z)
    (h : ∀ (m : Ideal A) [hm : m.IsMaximal], (⟨m, hm.isPrime⟩ : PrimeSpectrum A) ∉ Z) : Z = ∅ := by
  obtain ⟨s, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus _).mp hZ
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨m, hm, hle⟩ := x.asIdeal.exists_le_maximal x.isPrime.ne_top
  exact h m fun z hz => hle (PrimeSpectrum.mem_zeroLocus x s |>.mp hx hz)

/-! ### Fibres of a module at the maximal ideals -/

/-- **Nakayama's lemma, globally.** A finite module whose fibre at every maximal ideal vanishes is
zero. -/
private theorem subsingleton_of_forall_subsingleton_residueField_tensor
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (h : ∀ (m : Ideal A) [m.IsMaximal], Subsingleton (m.ResidueField ⊗[A] M)) :
    Subsingleton M :=
  Module.support_eq_empty_iff.mp <|
    eq_empty_of_isClosed_of_forall_isMaximal_notMem Module.isClosed_support fun m =>
      (Module.mem_support_iff_nontrivial_residueField_tensorProduct _).not.mpr
        (not_nontrivial_iff_subsingleton.mpr (h m))

/-- **A module spanned by `n` elements has fibres of dimension at most `n`.** -/
private theorem finrank_residueField_tensor_le {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] {n : ℕ} {v : Fin n → M} (hv : Submodule.span A (Set.range v) = ⊤)
    (m : Ideal A) [m.IsMaximal] :
    Module.finrank m.ResidueField (m.ResidueField ⊗[A] M) ≤ n := by
  have := (algebraMap A m.ResidueField).domain_nontrivial
  have hf : Function.Surjective (Fintype.linearCombination A v) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hv]
  calc Module.finrank m.ResidueField (m.ResidueField ⊗[A] M)
      ≤ Module.finrank m.ResidueField (m.ResidueField ⊗[A] (Fin n → A)) :=
        LinearMap.finrank_le_finrank_of_surjective
          (LinearMap.baseChange_surjective _ hf)
    _ = n := by rw [Module.finrank_baseChange, Module.finrank_fin_fun]

/-- **A surjection from a finite free module onto a projective module whose fibres have the rank of
the source is injective.** -/
private theorem injective_of_surjective_of_finrank_residueField_eq
    {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Free A N] [Module.Finite A N] [Module.Projective A M]
    (f : N →ₗ[A] M) (hf : Function.Surjective f)
    (h : ∀ (m : Ideal A) [m.IsMaximal],
      Module.finrank m.ResidueField (m.ResidueField ⊗[A] M) = Module.finrank A N) :
    Function.Injective f := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f (LinearMap.id : M →ₗ[A] M) hf
  set π : N →ₗ[A] N := LinearMap.id - g ∘ₗ f with hπ
  have hmem : ∀ x : N, π x ∈ LinearMap.ker f := fun x => by
    have : f (g (f x)) = f x := congrArg (fun φ => (φ : M →ₗ[A] M) (f x)) hg
    simp [hπ, this]
  set p : N →ₗ[A] LinearMap.ker f := LinearMap.codRestrict _ π hmem with hp
  have hpi : p ∘ₗ (LinearMap.ker f).subtype = LinearMap.id :=
    LinearMap.ext fun y => Subtype.ext (by
      simp [hp, hπ, LinearMap.codRestrict, LinearMap.mem_ker.mp y.2])
  have : Module.Finite A (LinearMap.ker f) :=
    Module.Finite.of_surjective p fun y => ⟨y, LinearMap.congr_fun hpi y⟩
  have : Subsingleton (LinearMap.ker f) := by
    refine subsingleton_of_forall_subsingleton_residueField_tensor (A := A) fun m _ => ?_
    have := (algebraMap A m.ResidueField).domain_nontrivial
    have hfbc := LinearMap.baseChange_surjective m.ResidueField hf
    have : Module.Finite m.ResidueField (m.ResidueField ⊗[A] M) :=
      Module.Finite.of_surjective _ hfbc
    have hinj : Function.Injective (f.baseChange m.ResidueField) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by rw [h m, Module.finrank_baseChange])).mpr hfbc
    have hsub : Function.Injective ((LinearMap.ker f).subtype.baseChange m.ResidueField) :=
      Function.LeftInverse.injective (g := p.baseChange m.ResidueField) fun z => by
        rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hpi, LinearMap.baseChange_id,
          LinearMap.id_apply]
    refine subsingleton_of_forall_eq 0 fun z => hsub ?_
    rw [map_zero]
    refine hinj ?_
    rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      LinearMap.comp_ker_subtype, LinearMap.baseChange_zero, LinearMap.zero_apply]
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.eq_bot_of_subsingleton

/-! ### Smoothness at the closed points -/

/-- **At a closed point the local dimension of `Spec A` is the height of the point** (Stacks
00OT). -/
@[ega "IV 17.15.8" "special case"]
private theorem localKrullDim_eq_height (k : Type*) [Field k] {A : Type*} [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] (m : Ideal A) [hm : m.IsMaximal] :
    localKrullDim (PrimeSpectrum A) ⟨m, hm.isPrime⟩ = (m.height : WithBot ℕ∞) := by
  rw [(PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height k
    (⟨m, hm.isPrime⟩ : PrimeSpectrum A)).2]
  refine le_antisymm (iInf₂_le m ⟨hm, le_rfl⟩) (le_iInf₂ fun 𝔫 h => le_of_eq ?_)
  rw [hm.eq_of_le h.1.ne_top h.2]

/-- **Stacks 00TT at a closed point.** For a finite type algebra over a field, smoothness at a
maximal ideal `m`, the fibre `κ(m) ⊗ Ω[A⁄k]` of the differentials having dimension at most the
height of `m`, and its having dimension exactly the height of `m`, are all equivalent. -/
private theorem isSmoothAt_tfae_height {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (m : Ideal A) [hm : m.IsMaximal] :
    List.TFAE
      [Algebra.IsSmoothAt k m,
       (Module.finrank m.ResidueField (m.ResidueField ⊗[A] Ω[A⁄k]) : ℕ∞) ≤ m.height,
       (Module.finrank m.ResidueField (m.ResidueField ⊗[A] Ω[A⁄k]) : ℕ∞) = m.height] := by
  have h := (Algebra.isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing (k := k)
    (⟨m, hm.isPrime⟩ : PrimeSpectrum A) (Localization.AtPrime m)).1
  dsimp only at h
  rw [localKrullDim_eq_height k m] at h
  tfae_have 1 ↔ 2 := (h.out 1 2).trans (by exact_mod_cast Iff.rfl)
  tfae_have 1 ↔ 3 := (h.out 1 3).trans (by exact_mod_cast Iff.rfl)
  tfae_finish

/-- **For an algebra of finite presentation, formal smoothness is smoothness at the closed
points.** -/
@[ega "0 22.6.7" "(ii), a)⇔c), case k = k₀"]
private theorem formallySmooth_iff_forall_isSmoothAt {k A : Type*} [CommRing k] [CommRing A]
    [Algebra k A] [Algebra.FinitePresentation k A] :
    Algebra.FormallySmooth k A ↔ ∀ (m : Ideal A) [m.IsMaximal], Algebra.IsSmoothAt k m := by
  rw [← Algebra.smoothLocus_eq_univ_iff]
  constructor
  · intro h m _
    change (⟨m, ‹m.IsMaximal›.isPrime⟩ : PrimeSpectrum A) ∈ Algebra.smoothLocus k A
    rw [h]
    trivial
  · intro h
    rw [← Set.compl_empty_iff]
    exact eq_empty_of_isClosed_of_forall_isMaximal_notMem
      (Algebra.isOpen_smoothLocus (R := k) (A := A)).isClosed_compl fun m _ hmem => hmem (h m)

/-! ### Formal étaleness from the base change map on differentials -/

section BaseChange

variable (k S A : Type*) [CommRing k] [CommRing S] [CommRing A] [Algebra k S] [Algebra k A]
  [Algebra S A] [IsScalarTower k S A]

/-- **The differentials of `A` over `S` vanish exactly when the base change map
`A ⊗_S Ω[S⁄k] → Ω[A⁄k]` is surjective.** -/
private theorem subsingleton_kaehlerDifferential_iff_surjective_mapBaseChange :
    Subsingleton Ω[A⁄S] ↔ Function.Surjective (mapBaseChange k S A) := by
  rw [← LinearMap.range_eq_top, ← LinearMap.exact_iff.mp (exact_mapBaseChange_map k S A),
    LinearMap.ker_eq_top]
  refine ⟨fun _ => LinearMap.ext fun _ => Subsingleton.elim _ _, fun h0 => ?_⟩
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨u, rfl⟩ := KaehlerDifferential.map_surjective k S A x
  rw [h0, LinearMap.zero_apply]

/-- **Formal étaleness from a bijective base change map on differentials.** For a tower
`k → S → A` with `A` formally smooth over `k`, if `A ⊗_S Ω[S⁄k] → Ω[A⁄k]` is bijective then `A` is
formally étale over `S`. -/
private theorem formallyEtale_of_bijective_mapBaseChange [Algebra.FormallySmooth k A]
    (hF : Function.Bijective (mapBaseChange k S A)) : Algebra.FormallyEtale S A := by
  refine (Algebra.formallyEtale_iff S A).mpr
    ⟨(subsingleton_kaehlerDifferential_iff_surjective_mapBaseChange k S A).mpr hF.2,
      subsingleton_of_forall_eq 0 fun z => ?_⟩
  have : Subsingleton (Algebra.H1Cotangent k A) :=
    Algebra.FormallySmooth.subsingleton_h1Cotangent
  obtain ⟨w, hw⟩ := (Algebra.H1Cotangent.exact_map_δ k S A z).mp
    (hF.1 (by rw [(Algebra.H1Cotangent.exact_δ_mapBaseChange k S A _).mpr ⟨z, rfl⟩, map_zero]))
  rw [← hw, Subsingleton.elim w 0, map_zero]

end BaseChange

/-! ### The base change map over a polynomial ring -/

/-- `A ⊗_{k[x₁, …, xₙ]} Ω[k[x₁, …, xₙ]⁄k]` is free of rank `n`, on the `1 ⊗ dxᵢ`. -/
private theorem finrank_tensor_kaehlerDifferential_mvPolynomial {n : ℕ} (k A : Type*) [Field k]
    [CommRing A] [Nontrivial A] [Algebra (MvPolynomial (Fin n) k) A] :
    Module.finrank A (A ⊗[MvPolynomial (Fin n) k] Ω[MvPolynomial (Fin n) k⁄k]) = n := by
  rw [Module.finrank_eq_card_basis
    (Algebra.TensorProduct.basis A (mvPolynomialBasis k (Fin n))), Fintype.card_fin]

/-- **The base change map has as range the span of the differentials of the images of the
variables.** -/
private theorem range_mapBaseChange_mvPolynomial {n : ℕ} (k A : Type*) [Field k] [CommRing A]
    [Algebra k A] [Algebra (MvPolynomial (Fin n) k) A]
    [IsScalarTower k (MvPolynomial (Fin n) k) A] {a : Fin n → A}
    (ha : ∀ i, algebraMap (MvPolynomial (Fin n) k) A (X i) = a i) :
    LinearMap.range (mapBaseChange k (MvPolynomial (Fin n) k) A) =
      Submodule.span A (Set.range fun i ↦ D k A (a i)) := by
  rw [LinearMap.range_eq_map,
    ← (Algebra.TensorProduct.basis A (mvPolynomialBasis k (Fin n))).span_eq, Submodule.map_span,
    ← Set.range_comp]
  exact congrArg _ (congrArg Set.range (funext fun i => by
    simp [Algebra.TensorProduct.basis_apply, mvPolynomialBasis_apply, ha]))

/-! ### The criterion -/

/-- Stacks 0G1C, in the form of an algebra structure on `A` over the polynomial ring. -/
private theorem etale_iff_height_eq_and_span_eq_top {n : ℕ} (k A : Type*) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] (a : Fin n → A)
    [Algebra (MvPolynomial (Fin n) k) A] [IsScalarTower k (MvPolynomial (Fin n) k) A]
    (ha : ∀ i, algebraMap (MvPolynomial (Fin n) k) A (X i) = a i) :
    Algebra.Etale (MvPolynomial (Fin n) k) A ↔
      (∀ m : Ideal A, m.IsMaximal → Ideal.height m = n) ∧
      Submodule.span A (Set.range fun i ↦ D k A (a i)) = ⊤ := by
  have hFP : Algebra.FinitePresentation (MvPolynomial (Fin n) k) A :=
    Algebra.FinitePresentation.of_finiteType.mp
      (Algebra.FiniteType.of_restrictScalars_finiteType k _ A)
  have hFPk : Algebra.FinitePresentation k A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have hsurj : Function.Surjective (mapBaseChange k (MvPolynomial (Fin n) k) A) ↔
      Submodule.span A (Set.range fun i ↦ D k A (a i)) = ⊤ := by
    rw [← LinearMap.range_eq_top, range_mapBaseChange_mvPolynomial k A ha]
  constructor
  · intro hEt
    have hFE : Algebra.FormallyEtale (MvPolynomial (Fin n) k) A := hEt.formallyEtale
    have hFS : Algebra.FormallySmooth k A :=
      Algebra.FormallySmooth.comp k (MvPolynomial (Fin n) k) A
    have e := tensorKaehlerEquivOfFormallyEtale k (MvPolynomial (Fin n) k) A
    have hfree : Module.Free A Ω[A⁄k] := Module.Free.of_equiv e
    refine ⟨fun m hm => ?_, hsurj.mp
      ((subsingleton_kaehlerDifferential_iff_surjective_mapBaseChange k _ A).mp
        Algebra.FormallyEtale.subsingleton_kaehlerDifferential)⟩
    have := (algebraMap A m.ResidueField).domain_nontrivial
    have hfib : Module.finrank m.ResidueField (m.ResidueField ⊗[A] Ω[A⁄k]) = n := by
      rw [Module.finrank_baseChange, ← e.finrank_eq,
        finrank_tensor_kaehlerDifferential_mvPolynomial k A]
    have := ((isSmoothAt_tfae_height m).out 1 3).mp
      (formallySmooth_iff_forall_isSmoothAt.mp hFS m)
    rw [hfib] at this
    exact this.symm
  · rintro ⟨hheight, hspan⟩
    have hFsurj := hsurj.mpr hspan
    have hsm : ∀ (m : Ideal A) [m.IsMaximal], Algebra.IsSmoothAt k m := fun m hm =>
      ((isSmoothAt_tfae_height m).out 2 1).mp (by
        rw [hheight m hm]
        exact_mod_cast finrank_residueField_tensor_le hspan m)
    have hfib : ∀ (m : Ideal A) [m.IsMaximal],
        Module.finrank m.ResidueField (m.ResidueField ⊗[A] Ω[A⁄k]) = n := fun m hm => by
      have := ((isSmoothAt_tfae_height m).out 1 3).mp (hsm m)
      rw [hheight m hm] at this
      exact_mod_cast this
    have hFS : Algebra.FormallySmooth k A := formallySmooth_iff_forall_isSmoothAt.mpr hsm
    have : Module.Projective A Ω[A⁄k] := Algebra.FormallySmooth.projective_kaehlerDifferential
    refine ⟨formallyEtale_of_bijective_mapBaseChange k _ A ⟨?_, hFsurj⟩, hFP⟩
    refine injective_of_surjective_of_finrank_residueField_eq _ hFsurj fun m _ => ?_
    have := (algebraMap A m.ResidueField).domain_nontrivial
    rw [finrank_tensor_kaehlerDifferential_mvPolynomial k A]
    exact hfib m

/-! ### The criterion for `MvPolynomial.aeval` -/

/-- **Stacks 0G1C.** For a finite type algebra `A` over a field `k` and `a : Fin n → A`, the map
`MvPolynomial.aeval a : k[x₁, …, xₙ] → A` is étale if and only if every maximal ideal of `A` has
height `n` and the differentials `d(aᵢ)` generate `Ω[A⁄k]` as an `A`-module. -/
public theorem solution
    {n : ℕ} (k A : Type*) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (a : Fin n → A) :
    (aeval a : MvPolynomial (Fin n) k →ₐ[k] A).toRingHom.Etale ↔
      (∀ m : Ideal A, m.IsMaximal → Ideal.height m = n) ∧
      Submodule.span A (Set.range fun i ↦ KaehlerDifferential.D k A (a i)) = ⊤ := by
  let _ : Algebra (MvPolynomial (Fin n) k) A :=
    (aeval a : MvPolynomial (Fin n) k →ₐ[k] A).toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin n) k) A := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = (aeval a : MvPolynomial (Fin n) k →ₐ[k] A) _
    simp
  refine etale_iff_height_eq_and_span_eq_top k A a fun i => ?_
  change (aeval a : MvPolynomial (Fin n) k →ₐ[k] A) (X i) = a i
  simp

end Stacks.Etale.PolynomialRingCriterion

end

@[expose] public section

/-- **Stacks 0G1C.** Let `k` be a field, let `A` be a `k`-algebra of finite type and let
`a₁, …, aₙ ∈ A`. The `k`-algebra map `φ : k[x₁, …, xₙ] → A`, `xᵢ ↦ aᵢ`, is étale if and only if
(a) every maximal ideal of `A` has height `n`, equivalently the local rings of `A` at maximal
ideals have dimension `n`, and (b) the differentials `d(a₁), …, d(aₙ)` generate `Ω[A⁄k]` as an
`A`-module. -/
@[stacks 0G1C, sga "1 II 5.1" "(i) ⟺ (iii)"]
public theorem MvPolynomial.etale_aeval_iff_height_eq_and_span_range_D_eq_top
    {n : ℕ} (k A : Type*) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (a : Fin n → A) :
    (aeval a : MvPolynomial (Fin n) k →ₐ[k] A).toRingHom.Etale ↔
      (∀ m : Ideal A, m.IsMaximal → Ideal.height m = n) ∧
      Submodule.span A (Set.range fun i ↦ KaehlerDifferential.D k A (a i)) = ⊤ :=
  Stacks.Etale.PolynomialRingCriterion.solution k A a

end
