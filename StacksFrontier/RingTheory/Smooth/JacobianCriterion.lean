module

public import StacksFrontier.RingTheory.CompleteIntersection.RelativeConormal
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Jacobian criterion for smoothness of a relative global complete intersection

Let `P` be a presentation `S = R[x_1, …, x_n]/(f_1, …, f_c)` all of whose nonempty fibres have
dimension `n - c`, and let `𝔮` be a prime of `S`. This file proves Stacks 00TE: `R → S` is smooth
at `𝔮` if and only if one of the minors `g_I = det (∂f_j/∂x_i)_{j, i ∈ I}`, `I ⊆ {1, …, n}` of
cardinality `c`, avoids `𝔮`.

Both directions read the minors as the maximal minors of the matrix of the naive cotangent complex
`⊕_j S · f_j → ⊕_i S · dx_i`, `f_j ↦ ∑_i (∂f_j/∂x_i) dx_i`, in the basis of `I/I²` given by the
relations, which is `jacobian_eq_det_submatrix_toMatrix`. That such a basis exists is Lemma 00SV
(3), the one place the fibre dimension hypothesis is used.

If some `g_I` avoids `𝔮`, then inverting it makes the presentation submersive, so `S_{g_I}` is
standard smooth over `R` and `R → S` is smooth on the standard open `D(g_I) ∋ 𝔮`. Conversely, if
`R → S` is smooth at `𝔮` then `H¹(L_{S_𝔮/R}) = 0` and `Ω_{S_𝔮/R}` is projective, so after base
change to `S_𝔮` the naive cotangent complex is a split injection: injective by Lemma 00S7, which
identifies the kernel of the base changed differential with the kernel of the differential of a
presentation of `S_𝔮`, and split because its cokernel `S_𝔮 ⊗_S Ω_{S/R} = Ω_{S_𝔮/R}` is projective.
The matrix of a split injection has a left inverse, and over the local ring `S_𝔮` a matrix with a
left inverse has a maximal minor which is a unit: modulo the maximal ideal its rows span, so `c` of
them form a basis of the residue field's `c`-space, and a spanning family of a vector space
contains a basis. That minor is the image of a `g_I`, and a unit of `S_𝔮` is an element outside
`𝔮`.

## Main results

* `Stacks.Smooth.JacobianCriterion.solution`: Lemma 00TE.

## Implementation notes

`exists_isUnit_det_submatrix_of_mul_eq_one` carries the local algebra: over a local ring a matrix
with a one-sided inverse has an invertible maximal minor. Its engine over a field,
`exists_isUnit_det_submatrix_of_span_eq_top`, is the determinant form of
`exists_embedding_basis_comp`, which extracts a basis from a spanning family as a *subfamily*,
indexed by an embedding of the index type of a given basis; that generality is what makes the minor
a minor rather than the determinant of an unrelated square matrix. Cauchy–Binet would replace the
reduction to the residue field by the identity `1 = ∑_I g_I h_I`, but it is not in Mathlib.

Lemma 00SV (3) is stated for relations indexed by `Fin c`, since its parts (1) and (2) depend on
their order; `exists_basis_cotangent` transports it along an enumeration of the relations, which is
harmless because the naive cotangent complex of a presentation depends only on its underlying
generators, so reindexing the relations does not move the module `I/I²`.

## References

* [Stacks 00TE](https://stacks.math.columbia.edu/tag/00TE), Lemma 10.137.15, whose two inputs are
  Lemma 00SV (the naive cotangent complex of the presentation) and Lemma 00S7 (localization of the
  naive cotangent complex).
-/

namespace Stacks.Smooth.JacobianCriterion

open Algebra Matrix
open scoped TensorProduct

/-- A spanning family contains a basis, as a subfamily: if `v : ι → V` spans `V` and `V` has a
basis indexed by `σ`, there is an injection `e : σ ↪ ι` such that `v ∘ e` is a basis of `V`. -/
public lemma exists_embedding_basis_comp {K V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] {σ ι : Type*} (b : Module.Basis σ K V) (v : ι → V)
    (hv : Submodule.span K (Set.range v) = ⊤) :
    ∃ e : σ ↪ ι, LinearIndependent K (v ∘ e) ∧ Submodule.span K (Set.range (v ∘ e)) = ⊤ := by
  classical
  set c := Module.Basis.ofSpan hv.ge with hc
  set φ := b.indexEquiv c with hφ
  choose g hg using fun j : σ ↦ Module.Basis.ofSpan_subset hv.ge (Set.mem_range_self (φ j))
  have hginj : Function.Injective g := fun j₁ j₂ hj ↦ φ.injective <| c.injective <| by
    rw [← hg j₁, ← hg j₂, hj]
  have hcg : v ∘ g = ⇑(c.reindex φ.symm) := by
    funext j
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, Function.comp_apply, hg j]
  exact ⟨⟨g, hginj⟩, hcg ▸ (c.reindex φ.symm).linearIndependent,
    hcg ▸ (c.reindex φ.symm).span_eq⟩

/-- Over a field, a matrix whose rows span the target has an invertible maximal minor: if the rows
of `M : Matrix ι σ K` span `σ → K`, there is an injection `e : σ ↪ ι` such that the square
submatrix of `M` on the rows `e` has invertible determinant. -/
public lemma exists_isUnit_det_submatrix_of_span_eq_top {K : Type*} [Field K] {ι σ : Type*}
    [Fintype σ] [DecidableEq σ] (M : Matrix ι σ K)
    (h : Submodule.span K (Set.range M.row) = ⊤) :
    ∃ e : σ ↪ ι, IsUnit (M.submatrix e id).det := by
  obtain ⟨e, hli, hsp⟩ := exists_embedding_basis_comp (Pi.basisFun K σ) M.row h
  have hdet : (Pi.basisFun K σ).det (M.row ∘ e) = (M.submatrix e id).det := by
    rw [Module.Basis.det_apply, ← Matrix.det_transpose]
    rfl
  exact ⟨e, hdet ▸ ((Pi.basisFun K σ).is_basis_iff_det).mp ⟨hli, hsp⟩⟩

/-- Over a local ring, a matrix with a left inverse has a maximal minor which is a unit: if
`N * M = 1` for `M : Matrix ι σ T` and `N : Matrix σ ι T`, there is an injection `e : σ ↪ ι` such
that the square submatrix of `M` on the rows `e` has unit determinant.

Modulo the maximal ideal the rows of `M` still span, and over the residue field `σ` of them form a
basis. -/
public lemma exists_isUnit_det_submatrix_of_mul_eq_one {T : Type*} [CommRing T] [IsLocalRing T]
    {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ] (M : Matrix ι σ T) (N : Matrix σ ι T)
    (h : N * M = 1) : ∃ e : σ ↪ ι, IsUnit (M.submatrix e id).det := by
  have hspan : Submodule.span (IsLocalRing.ResidueField T)
      (Set.range (M.map (IsLocalRing.residue T)).row) = ⊤ := by
    rw [← range_vecMulLinear, LinearMap.range_eq_top]
    intro w
    refine ⟨w ᵥ* N.map (IsLocalRing.residue T), ?_⟩
    rw [Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, ← Matrix.map_mul, h]
    simp
  obtain ⟨e, he⟩ := exists_isUnit_det_submatrix_of_span_eq_top _ hspan
  refine ⟨e, (IsLocalRing.residue_ne_zero_iff_isUnit _).mp ?_⟩
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map]
  exact he.ne_zero

/-- The conormal module of a relative global complete intersection is free on the relations, for
relations indexed by an arbitrary finite type: Lemma 00SV (3) transported along an enumeration of
the relations. -/
private lemma exists_basis_cotangent {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι σ : Type*} [Finite ι] [Finite σ] (P : Algebra.Presentation R S ι σ)
    (hP : ∀ (p : Ideal R) [p.IsPrime], Nontrivial (p.Fiber S) →
      ringKrullDim (p.Fiber S) + Nat.card σ = Nat.card ι) :
    ∃ b : Module.Basis σ S P.toExtension.Cotangent,
      ∀ j, b j = Algebra.Extension.Cotangent.mk ⟨P.relation j, P.relation_mem_ker j⟩ := by
  classical
  set f := Finite.equivFin σ
  let Q : Algebra.Presentation R S ι (Fin (Nat.card σ)) :=
    { P with
      relation := P.relation ∘ f.symm
      span_range_relation_eq_ker := by
        rw [← P.span_range_relation_eq_ker, Set.range_comp, f.symm.range_eq_univ, Set.image_univ] }
  have hQrel : ∀ j, Q.relation j = P.relation (f.symm j) := fun _ ↦ rfl
  have : Q.IsRelativeGlobalCompleteIntersection :=
    ⟨fun p _ hp ↦ by rw [Nat.card_fin]; exact hP p hp⟩
  obtain ⟨b, hb⟩ := Algebra.Presentation.exists_basis_cotangent_relation Q
  refine ⟨b.reindex f.symm, fun j ↦ ?_⟩
  rw [Module.Basis.reindex_apply, Equiv.symm_symm, hb (f j)]
  simp [hQrel]

/-- The Jacobian minor `g_I` of a presentation is the maximal minor, on the rows `I`, of the matrix
of the naive cotangent complex in the basis of `I/I²` given by the relations and the basis `dx_i`
of `S ⊗ Ω_{R[x]/R}`. -/
private lemma jacobian_eq_det_submatrix_toMatrix {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {ι σ : Type*} [Finite ι] [Fintype σ] [DecidableEq σ]
    (P : Algebra.Presentation R S ι σ) (bC : Module.Basis σ S P.toExtension.Cotangent)
    (hbC : ∀ j, bC j = Algebra.Extension.Cotangent.mk ⟨P.relation j, P.relation_mem_ker j⟩)
    (e : σ ↪ ι) :
    (Algebra.PreSubmersivePresentation.mk P e e.injective).jacobian =
      ((LinearMap.toMatrix bC P.cotangentSpaceBasis P.toExtension.cotangentComplex).submatrix
        e id).det := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, RingHom.map_det,
    RingHom.mapMatrix_apply]
  congr 1
  ext a b
  rw [Matrix.map_apply, Matrix.submatrix_apply, LinearMap.toMatrix_apply,
    Algebra.PreSubmersivePresentation.jacobiMatrix_apply, hbC,
    Algebra.Extension.cotangentComplex_mk, P.cotangentSpaceBasis_repr_one_tmul,
    Algebra.Generators.algebraMap_apply]
  rfl

/-- If `H¹(L_{T/R})` vanishes for a localization `T` of `S`, the naive cotangent complex of any
presentation of `S` becomes injective after base change to `T`: by Lemma 00S7 its kernel maps
bijectively onto the kernel of the differential of a presentation of `T`, and the latter vanishes
because `H¹(L_{T/R})` does. -/
public lemma injective_baseChange_cotangentComplex {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] {ι : Type*}
    (P : Algebra.Generators R S ι) (M : Submonoid S) [IsLocalization M T]
    [Subsingleton (Algebra.H1Cotangent R T)] :
    Function.Injective (P.toExtension.cotangentComplex.baseChange T) := by
  set Q := Algebra.Generators.self R T with hQ
  have hQinj : Function.Injective Q.toExtension.cotangentComplex :=
    (Algebra.Extension.subsingleton_h1Cotangent _).mp Q.equivH1Cotangent.subsingleton
  have hbij := Algebra.Extension.Cotangent.bijOn_ker_liftBaseChange_map_of_isLocalization
    (T := T) M ((Algebra.Generators.defaultHom P Q).toExtensionHom)
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  refine hbij.injOn hx (zero_mem _) ?_
  have hmt := hbij.mapsTo hx
  rw [LinearMap.ker_eq_bot.mpr hQinj] at hmt
  rw [show ((Algebra.Extension.Cotangent.map _).liftBaseChange T) x = 0 from hmt, map_zero]

/-- **A left inverse for the base-changed naive cotangent complex.**  Over a localization `T`
of `S` which is formally smooth over `R`, the base change of the cotangent complex of a
presentation is split injective. -/
@[ega "0 22.6.1" "partial"]
public lemma exists_leftInverse_baseChange_cotangentComplex {R S T : Type*} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] {ι : Type*} (P : Algebra.Generators R S ι)
    (M : Submonoid S) [IsLocalization M T] [Algebra.FormallySmooth R T] :
    ∃ r : T ⊗[S] P.toExtension.CotangentSpace →ₗ[T]
        T ⊗[S] P.toExtension.Cotangent,
      r ∘ₗ P.toExtension.cotangentComplex.baseChange T = LinearMap.id := by
  have : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_isLocalization M
  have : Module.Projective T Ω[T⁄R] := Algebra.FormallySmooth.projective_kaehlerDifferential
  have : Module.Projective T (T ⊗[S] Ω[S⁄R]) :=
    Module.Projective.of_equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm
  have hsurj : Function.Surjective (P.toExtension.toKaehler.baseChange T) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective T Algebra.Extension.toKaehler_surjective
  have hex : Function.Exact (P.toExtension.cotangentComplex.baseChange T)
      (P.toExtension.toKaehler.baseChange T) := by
    simp only [LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact T Algebra.Extension.exact_cotangentComplex_toKaehler
      Algebra.Extension.toKaehler_surjective
  obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id hsurj
  have hsplit := hex.split_tfae'.out 1 2
  exact (hsplit.mp ⟨injective_baseChange_cotangentComplex P M, s, hs⟩).2

/-- The hard direction of Stacks 00TE: if `R → S` is smooth at `𝔮`, some Jacobian minor of the
presentation avoids `𝔮`. The matrix of the base changed naive cotangent complex has a left inverse
over the local ring `S_𝔮`, hence a maximal minor which is a unit, and that minor is the image of a
`g_I`. -/
private lemma exists_jacobian_notMem_of_isSmoothAt {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {ι σ : Type*} [Finite ι] [Finite σ] (P : Algebra.Presentation R S ι σ)
    (hP : ∀ (p : Ideal R) [p.IsPrime], Nontrivial (p.Fiber S) →
      ringKrullDim (p.Fiber S) + Nat.card σ = Nat.card ι)
    (q : Ideal S) [q.IsPrime] [Algebra.IsSmoothAt R q] :
    ∃ e : σ ↪ ι, (Algebra.PreSubmersivePresentation.mk P e e.injective).jacobian ∉ q := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have : Fintype σ := Fintype.ofFinite σ
  set T := Localization.AtPrime q
  obtain ⟨bC, hbC⟩ := exists_basis_cotangent P hP
  have : Algebra.FormallySmooth R T := ‹Algebra.IsSmoothAt R q›
  obtain ⟨r, hr⟩ :=
    exists_leftInverse_baseChange_cotangentComplex (T := T) P.toGenerators q.primeCompl
  set M := LinearMap.toMatrix bC P.cotangentSpaceBasis P.toExtension.cotangentComplex with hM
  have hmul : LinearMap.toMatrix (Algebra.TensorProduct.basis T P.cotangentSpaceBasis)
      (Algebra.TensorProduct.basis T bC) r * M.map (algebraMap S T) = 1 := by
    rw [hM, ← LinearMap.toMatrix_baseChange, ← LinearMap.toMatrix_comp, hr, LinearMap.toMatrix_id]
  obtain ⟨e, he⟩ := exists_isUnit_det_submatrix_of_mul_eq_one _ _ hmul
  refine ⟨e, (IsLocalization.AtPrime.isUnit_to_map_iff T q _).mp ?_⟩
  rw [jacobian_eq_det_submatrix_toMatrix P bC hbC e, ← hM, RingHom.map_det,
    RingHom.mapMatrix_apply, ← Matrix.submatrix_map]
  exact he

/-- The easy direction of Stacks 00TE: if one Jacobian minor of the presentation avoids the prime
`q`, then `R → S` is smooth at `q`. Inverting that minor `g` turns the presentation into a
submersive one, so `S_g` is standard smooth, hence smooth, over `R`. -/
@[sga "1 II 4.14" "special case"]
private lemma isSmoothAt_of_jacobian_notMem {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι σ : Type*} [Finite ι] [Finite σ] (P : Algebra.Presentation R S ι σ)
    (q : Ideal S) [q.IsPrime] (e : σ ↪ ι)
    (he : (Algebra.PreSubmersivePresentation.mk P e e.injective).jacobian ∉ q) :
    Algebra.IsSmoothAt R q := by
  have : Algebra.FinitePresentation R S := P.finitePresentation_of_isFinite
  set g : S := (Algebra.PreSubmersivePresentation.mk P e e.injective).jacobian with hg
  have hunit : IsUnit (algebraMap S (Localization.Away g) g) :=
    IsLocalization.map_units (Localization.Away g)
      (⟨g, Submonoid.mem_powers g⟩ : Submonoid.powers g)
  have hj : IsUnit ((Algebra.PreSubmersivePresentation.localizationAway (Localization.Away g)
      g).comp (Algebra.PreSubmersivePresentation.mk P e e.injective)).jacobian := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
    exact hunit.mul hunit
  have : Algebra.IsStandardSmooth R (Localization.Away g) :=
    (Algebra.SubmersivePresentation.mk _ hj).isStandardSmooth
  have hsub := (Algebra.basicOpen_subset_smoothLocus_iff_smooth (R := R) (A := S)
    (f := g)).mpr inferInstance
  have hmem : (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum S) ∈
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) := by
    simpa [PrimeSpectrum.mem_basicOpen] using he
  exact hsub hmem

/-- For a presentation `P` of `S` over `R` whose nonempty fibres have dimension `|ι| - |σ|`,
`R → S` is smooth at a prime `q` of `S` if and only if, for some injection `f : σ ↪ ι`, the
Jacobian minor of `P` equipped with `f` does not lie in `q`. -/
public theorem solution {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] {ι σ : Type*} [Finite ι] [Finite σ]
    (P : Algebra.Presentation R S ι σ)
    (hP : ∀ (p : Ideal R) [p.IsPrime], Nontrivial (p.Fiber S) →
      ringKrullDim (p.Fiber S) + Nat.card σ = Nat.card ι)
    (q : Ideal S) [q.IsPrime] :
    Algebra.IsSmoothAt R q ↔
      ∃ f : σ ↪ ι, (Algebra.PreSubmersivePresentation.mk P f f.injective).jacobian ∉ q :=
  ⟨fun _ ↦ exists_jacobian_notMem_of_isSmoothAt P hP q,
    fun ⟨e, he⟩ ↦ isSmoothAt_of_jacobian_notMem P q e he⟩

end Stacks.Smooth.JacobianCriterion

/-!
# Smoothness of a relative global complete intersection at a prime

Let `R` be a ring and let `S = R[x_1, …, x_n]/(f_1, …, f_c)` be a relative global complete
intersection (Definition 00SP): a presentation of `S` over `R` by `n` variables and `c` relations
such that every nonempty fibre of `Spec(S) → Spec(R)` has dimension `n - c`. For a subset
`I ⊆ {1, …, n}` of cardinality `c` put
`g_I = det (∂f_j/∂x_i)_{j = 1, …, c, i ∈ I}`, a polynomial in `R[x_1, …, x_n]`. Then `R → S` is
smooth at a prime `q ⊂ S` if and only if the image in `S` of some `g_I` does not lie in `q`.

The naive cotangent complex of the given presentation is the complex
`⊕_{j = 1}^c S · f_j → ⊕_{i = 1}^n S · dx_i`, `f_j ↦ ∑_i (∂f_j/∂x_i) dx_i` (Lemma 00SV), and the
`g_I` are exactly the maximal minors of the matrix of that map. So the criterion says that the map
becomes a split injection with free rank `n - c` cokernel after inverting one element outside `q`,
which by Lemma 00S7 is smoothness at `q`.

## Main results

* `Algebra.Presentation.isSmoothAt_iff_exists_jacobian_notMem`: for a presentation of `S` over `R`
  all of whose nonempty fibres have dimension `n - c`, smoothness at a prime `q` of `S` is the
  existence of a `c`-element subset of the variables whose Jacobian minor avoids `q`, 00TE.

## Implementation notes

*A subset `I ⊆ {1, …, n}` of cardinality `c` is an injection `σ ↪ ι` from the relations to the
variables, and `g_I` is Mathlib's `Algebra.PreSubmersivePresentation.jacobian`.* Equipping a
presentation with an injection from its relations to its variables is exactly Mathlib's
`Algebra.PreSubmersivePresentation`, whose `jacobian` is the image in `S` of
`det (∂f_j/∂x_i)_{j, i ∈ I}` — this is `jacobian_eq_jacobiMatrix_det` together with
`jacobiMatrix_apply`, so no new determinant is introduced here. Quantifying over injections rather
than over subsets loses nothing: every `c`-element subset is the image of an injection, and two
injections with the same image give minors differing by the sign of a permutation, so they lie in
`q` together.

*The dimension hypothesis is imposed on the given presentation, not through the class
`Algebra.IsRelativeGlobalCompleteIntersection` (00SP).* The criterion is a statement about a
presentation, and the class only asserts that *some* presentation has the fibre dimension `n - c`.
It genuinely cannot be weakened to the class: `k = k[x]/(x, x^2)` is smooth over `k`, and it is a
relative global complete intersection through the presentation with `n = c = 0`, but through the
displayed presentation `n = 1 < 2 = c`, so there is no subset `I` at all and the right-hand side
is false. The hypothesis here is verbatim the property that the field
`Algebra.IsRelativeGlobalCompleteIntersection.out` asserts of its chosen presentation, so an
instance of that class is exactly a presentation to which this lemma applies.

*Stated for arbitrary finite index types `ι` and `σ` rather than `Fin n` and `Fin c`.* Mathlib's
`Algebra.Presentation.reindex` moves between the two, `Nat.card ι` and `Nat.card σ` are the
source's `n` and `c`, and the injection `σ ↪ ι` makes `c ≤ n` automatic. The dimension condition is
written additively, `ringKrullDim (p.Fiber S) + c = n` in `WithBot ℕ∞`, and the fibre over `p` is
`Ideal.Fiber p S = κ(p) ⊗_R S`, both exactly as in Definition 00SP; see that file for why the
truncated subtraction `n - c` in `ℕ` would be a different, weaker condition.

*Smoothness at `q` is Mathlib's `Algebra.IsSmoothAt R q`*, that is, `Localization.AtPrime q` is
formally smooth over `R`; the attribute for Definition 00TB already sits on it upstream. A
presentation with finitely many variables and relations makes `S` of finite presentation over `R`,
and for such algebras `Algebra.IsSmoothAt` agrees with the source's "there is `g ∉ q` with `S_g`
smooth over `R`" by `Algebra.basicOpen_subset_smoothLocus_iff_smooth` and
`Algebra.isOpen_smoothLocus`. No finite presentation hypothesis is stated because it is a
consequence of `P`, by `Algebra.Presentation.finitePresentation_of_isFinite`.

Faithfulness. (1) Both hypotheses are used: without the fibre dimension condition on `P` the
statement is false, as the presentation `k[x]/(x, x^2)` of `k` above shows, and `q` is the prime at
which smoothness is tested on the left and which the minor must avoid on the right. (2) The
scalars and the base are the source's: the presentation is over `R` itself, the partial derivatives
are those of the relations of that presentation in `R[x_1, …, x_n]`, the dimension is that of the
fibre over the residue field `κ(p)` of `R`, and smoothness is of `R → S`, not of a localization of
`R`. (3) The canonical maps are pinned rather than merely asserted to exist: `P` pins the
surjection `R[x_1, …, x_n] → S` whose kernel the `f_j` span, and `jacobian` pins the image of the
minor `g_I` under that surjection — the content is which element of `S` must avoid `q`, not that
some element does. (4) The instantiation is not degenerate: `R → R[x]` with `ι = Fin 1`,
`σ = Fin 0` satisfies the hypothesis (each fibre `κ(p)[x]` has dimension `1 = 1 - 0`) and both
sides hold, the empty minor being `1`; and `k → k[x, y]/(xy)` with `ι = Fin 2`, `σ = Fin 1`
satisfies it (the only fibre has dimension `1 = 2 - 1`) while at `q = (x, y)` both minors `y` and
`x` lie in `q` and the node is not smooth, so both sides fail there and neither direction is
vacuous.

## References

* [Stacks 00TE](https://stacks.math.columbia.edu/tag/00TE), Lemma 10.137.15, in Section 10.137
  "Smooth ring maps".
  Definition 00SP of a relative global complete intersection is
  `Algebra.IsRelativeGlobalCompleteIntersection`, Definition 00TB of smoothness at a prime is
  `Algebra.IsSmoothAt`, and the two inputs of the source's proof are Lemma 00SV (the naive
  cotangent complex of the presentation) and Lemma 00S7 (smoothness from the naive cotangent
  complex after inverting one element).
-/

@[expose] public section

/-- **Jacobian criterion for smoothness at a prime.** Let `S = R[x_1, …, x_n]/(f_1, …, f_c)` be a
presentation of `S` over `R` such that every nonempty fibre of `Spec(S) → Spec(R)` has dimension
`n - c`, i.e. a relative global complete intersection (Definition 00SP). Then `R → S` is smooth at
a prime `q ⊂ S` if and only if there is a subset `I ⊆ {1, …, n}` of cardinality `c` such that
`g_I = det (∂f_j/∂x_i)_{j = 1, …, c, i ∈ I}` does not map into `q`.

The subset `I` is an injection `f : σ ↪ ι` from the relations to the variables, and the image of
`g_I` in `S` is the `Algebra.PreSubmersivePresentation.jacobian` of `P` equipped with `f`. See the
module docstring. -/
@[stacks 00TE "The subset `I ⊆ {1, …, n}` of cardinality `c` is an injection `σ ↪ ι` from the
relations to the variables — that is, the extra datum of an
`Algebra.PreSubmersivePresentation` — and the image of `g_I` in `S` is its `jacobian`. The
hypothesis is placed on the given presentation `P`, not on the class
`Algebra.IsRelativeGlobalCompleteIntersection` (00SP), since the criterion depends on `P`; it is
verbatim the condition that class asserts of its chosen presentation. Index types are arbitrary
finite ones rather than `Fin n`, `Fin c`, and smoothness at `q` is `Algebra.IsSmoothAt`
(00TB). See the module docstring."]
public theorem Algebra.Presentation.isSmoothAt_iff_exists_jacobian_notMem {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] {ι σ : Type*} [Finite ι] [Finite σ]
    (P : Algebra.Presentation R S ι σ)
    (hP : ∀ (p : Ideal R) [p.IsPrime], Nontrivial (p.Fiber S) →
      ringKrullDim (p.Fiber S) + Nat.card σ = Nat.card ι)
    (q : Ideal S) [q.IsPrime] :
    Algebra.IsSmoothAt R q ↔
      ∃ f : σ ↪ ι, (Algebra.PreSubmersivePresentation.mk P f f.injective).jacobian ∉ q :=
    by apply Stacks.Smooth.JacobianCriterion.solution; assumption

end
