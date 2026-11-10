module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Restricted.RigSmoothCriteria
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.Completion
public import StacksFrontier.RingTheory.Smooth.SmoothAt
public import StacksFrontier.RingTheory.Smoothing.ConormalLocalization

/-!
# Rig-smoothness of a completion and smoothness away from the ideal of definition

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal and let `B` be a finite type `A`-algebra.
If `Spec(B) → Spec(A)` is smooth over `Spec(A) ∖ V(I)`, then the `I`-adic completion `B^` is
rig-smooth over `(A, I)`; conversely, if `B^` is rig-smooth over `(A, I)`, then there is
`g ∈ 1 + IB` for which `Spec(B_g) → Spec(A)` is smooth over `Spec(A) ∖ V(I)`.

Both directions are organized around one ideal of `B`: for a presentation
`α : A[x₁, …, xₙ] → B` with kernel `J` and naive cotangent complex
`NL(α) = (J / J² --d--> ⨁ᵢ B dxᵢ)`, the *retraction ideal* of `d` consists of those `a : B` for
which multiplication by `a` on `J / J²` factors through `d`. Smoothness of `A → B` at a prime
`q` is exactly the non-containment of that ideal in `q`
(`Rig.smoothAt_iff_not_retractionIdeal_le`), so smoothness over `Spec(A) ∖ V(I)` is the
containment of `IB` in its radical, and — `B` being Noetherian — the containment of a power of
`IB` in the ideal itself. Transporting such a factorization across the isomorphism
`NL^∧_{B^/A} = NL(α) ⊗_B B^` of Stacks 0GAF turns it into the factorization criterion for
rig-smoothness of Stacks 0GAJ, and back.

## Main definitions

* `Rig.retractionIdeal`: the scalars whose multiplication on the source of a linear map factors
  through that map.
* `Rig.SmoothAwayFrom`: smoothness of `Spec(B) → Spec(A)` over `Spec(A) ∖ V(I)`, as smoothness
  of `A → B` (Definition 00TB) at every prime of `B` whose contraction does not contain `I`.
* `Rig.relationMap`: the linear system solved by a factorization of multiplication by a scalar
  through the differential of a presentation, written in a generating family of the conormal
  module.

## Main results

* `Rig.smoothAt_iff_not_retractionIdeal_le`: `A → B` is smooth at `q` if and only if the
  retraction ideal of the differential of a presentation is not contained in `q`.
* `Rig.isRigSmooth_adicCompletionObj_of_smoothAwayFrom`: **Stacks 0GAK (1)**.
* `Rig.exists_sub_one_mem_and_smoothAwayFrom_of_isRigSmooth`: **Stacks 0GAK (2)**.

## Implementation notes

Smoothness over the open `Spec(A) ∖ V(I)` is read pointwise, at the primes of `B` lying over
the complement of `V(I)`; this keeps the whole file inside the ring-theoretic language of the
surrounding development, which uses no scheme theory. `g ∈ 1 + IB` is spelled `g - 1 ∈ IB`, and
`B_g` is `Localization.Away g`; that the second conclusion is about the points of `Spec(B_g)`
rather than those of `Spec(B)` avoiding `g` is `Rig.smoothAwayFrom_of_forall_notMem`, which
transports smoothness along the localization.

The proof of the second part departs from the source's route. The source represents the
obstruction as the class `ξ ∈ Ext¹_B(NL_{B/A}, J / J²)` of the identity and base changes `Ext`
along the flat map `B → B^` using More on Algebra 0A6A (or 087R). Here `ξ` is realized by hand
as the class of a generating family `z` of `J / J²` in the cokernel of `Rig.relationMap`: that
cokernel base changes with no flatness and no `Hom` or `Ext` base change at all, since cokernels
commute with the tensor product. Flatness of `B → B^` enters only once afterwards, to see that
a finitely generated submodule dying in `B^ ⊗_B M` dies, and the comparison `B^ / IB^ = B / IB`
only through `AdicCompletion.eval` in level one. Nakayama's lemma is then Stacks 00DV, as in
the source.

## References

* [Stacks Project, Lemma 88.4.3 (Tag 0GAK)](https://stacks.math.columbia.edu/tag/0GAK)
* [Stacks Project, Tag 0GAJ](https://stacks.math.columbia.edu/tag/0GAJ)
* [Stacks Project, Tag 0GAF](https://stacks.math.columbia.edu/tag/0GAF)
* [Stacks Project, Tag 00S7](https://stacks.math.columbia.edu/tag/00S7)
* [Stacks Project, Tag 00TB](https://stacks.math.columbia.edu/tag/00TB)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v

namespace Rig

/-! ## The retraction ideal of a linear map -/

section Retraction

variable {R : Type*} [CommRing R] {D E F : Type*} [AddCommGroup D] [Module R D]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

/-- The ideal of those scalars `a` for which multiplication by `a` on the source of a linear
map `d` factors through `d`. -/
public def retractionIdeal (d : D →ₗ[R] E) : Ideal R where
  carrier := {a | ∃ h : E →ₗ[R] D, h.comp d = a • LinearMap.id}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    intro a b ha hb
    rcases ha with ⟨f, hf⟩
    rcases hb with ⟨g, hg⟩
    refine ⟨f + g, ?_⟩
    ext x
    have hf' : f (d x) = a • x := by
      have h := congrArg (fun q : D →ₗ[R] D => q x) hf
      simpa using h
    have hg' : g (d x) = b • x := by
      have h := congrArg (fun q : D →ₗ[R] D => q x) hg
      simpa using h
    change f (d x) + g (d x) = _
    rw [hf', hg']
    simp [add_smul]
  smul_mem' := by
    intro r a ha
    obtain ⟨f, hf⟩ := ha
    refine ⟨r • f, ?_⟩
    ext x
    have hf' : f (d x) = a • x := by
      have h := congrArg (fun q : D →ₗ[R] D => q x) hf
      simpa using h
    change r • f (d x) = (r * a) • x
    rw [hf']
    simp [smul_smul]

/-- Unfolding of membership in `Rig.retractionIdeal`. -/
public theorem mem_retractionIdeal {d : D →ₗ[R] E} {a : R} :
    a ∈ retractionIdeal d ↔ ∃ h : E →ₗ[R] D, h.comp d = a • LinearMap.id := Iff.rfl

/-- Every tuple of scalars is the corresponding combination of the standard basis. -/
private theorem sum_smul_single {m : ℕ} (v : Fin m → R) :
    ∑ i, (v i) • (Pi.single i 1 : Fin m → R) = v := by
  classical
  simpa using (Pi.basisFun R (Fin m)).sum_repr v

/-- Composing a linear map with an isomorphism of its target does not change its retraction
ideal. -/
public theorem retractionIdeal_equiv_comp (d : D →ₗ[R] E) (e : E ≃ₗ[R] F) :
    retractionIdeal (e.toLinearMap ∘ₗ d) = retractionIdeal d := by
  ext a
  refine ⟨fun ⟨h, hh⟩ ↦ ⟨h ∘ₗ e.toLinearMap, hh⟩, fun ⟨h, hh⟩ ↦ ⟨h ∘ₗ e.symm.toLinearMap, ?_⟩⟩
  rw [← hh]
  ext x
  change h (e.symm (e (d x))) = h (d x)
  rw [e.symm_apply_apply]

end Retraction

/-! ## Smoothness at a prime and the retraction ideal of a presentation -/

section Presentation

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {B : Type v} [CommRing B] [Algebra A B]
  [Algebra.FiniteType A B] {n : ℕ} (G : Algebra.Generators A B (Fin n))

omit [IsNoetherianRing A] [Algebra.FiniteType A B] in
/-- The retraction ideal of the differential of a presentation, written in the basis of the
degree-`0` term, is the retraction ideal of the conormal map of the presentation. -/
public theorem retractionIdeal_presentationDifferential :
    retractionIdeal (presentationDifferential G) =
      retractionIdeal G.toExtension.cotangentComplex :=
  retractionIdeal_equiv_comp G.toExtension.cotangentComplex G.cotangentSpaceBasis.equivFun

/-- The conormal module of a presentation by finitely many variables of a finite type algebra
over a Noetherian ring is a finite module. -/
private instance finite_cotangent_generators :
    Module.Finite B G.toExtension.Cotangent := by
  have : IsNoetherianRing G.toExtension.Ring := by
    change IsNoetherianRing (MvPolynomial (Fin n) A)
    infer_instance
  exact Algebra.Extension.Cotangent.finite (Ideal.fg_of_isNoetherianRing _)

/-- The degree-`0` term of the naive cotangent complex of a presentation is free on the
variables. -/
private instance free_cotangentSpace_generators :
    Module.Free B G.toExtension.CotangentSpace :=
  Module.Free.of_basis G.cotangentSpaceBasis

/-- The degree-`0` term of the naive cotangent complex of a presentation by finitely many
variables is a finite module. -/
private instance finite_cotangentSpace_generators :
    Module.Finite B G.toExtension.CotangentSpace :=
  Module.Finite.of_basis G.cotangentSpaceBasis

/-- The degree-`0` term of the naive cotangent complex of a presentation by finitely many
variables is finitely presented, being finite free. -/
private instance finitePresentation_cotangentSpace_generators :
    Module.FinitePresentation B G.toExtension.CotangentSpace :=
  Module.finitePresentation_of_projective _ _

/-- The base change of multiplication by a scalar is multiplication by its image. -/
private theorem baseChange_smul_id {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (T : Type*) [CommRing T] [Algebra R T] (a : R) :
    LinearMap.baseChange T (a • (LinearMap.id : M →ₗ[R] M)) =
      (algebraMap R T a) • (LinearMap.id : T ⊗[R] M →ₗ[T] T ⊗[R] M) := by
  ext x
  change ((1 : T) ⊗ₜ[R] (a • x) : T ⊗[R] M) = (algebraMap R T a) • ((1 : T) ⊗ₜ[R] x)
  rw [TensorProduct.tmul_smul, algebraMap_smul]

omit [IsNoetherianRing A] [Algebra.FiniteType A B] in
/-- An element of the retraction ideal of a presentation splits the base changed conormal map
over any algebra in which it becomes invertible. -/
private theorem exists_leftInverse_baseChange_of_mem_retractionIdeal {a : B}
    (ha : a ∈ retractionIdeal G.toExtension.cotangentComplex)
    (T : Type*) [CommRing T] [Algebra B T] (hunit : IsUnit (algebraMap B T a)) :
    ∃ l : T ⊗[B] G.toExtension.CotangentSpace →ₗ[T] T ⊗[B] G.toExtension.Cotangent,
      l ∘ₗ LinearMap.baseChange T G.toExtension.cotangentComplex = LinearMap.id := by
  obtain ⟨h, hh⟩ := ha
  obtain ⟨c, hc⟩ := hunit.exists_left_inv
  refine ⟨c • LinearMap.baseChange T h, ?_⟩
  have hcomp : LinearMap.baseChange T h ∘ₗ
      LinearMap.baseChange T G.toExtension.cotangentComplex =
      (algebraMap B T a) • (LinearMap.id : T ⊗[B] G.toExtension.Cotangent →ₗ[T] _) := by
    rw [← LinearMap.baseChange_comp, hh, baseChange_smul_id]
  rw [LinearMap.smul_comp, hcomp, smul_smul, hc, one_smul]

/-- If the base changed conormal map of a presentation is split injective over a localization
`T` of `B`, then the first cotangent cohomology of `T` over `A` vanishes. -/
private theorem subsingleton_h1Cotangent_of_injective_baseChange
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] {ι : Type*} (P : Algebra.Generators R S ι)
    (M : Submonoid S) [IsLocalization M T]
    (hinj : Function.Injective (LinearMap.baseChange T P.toExtension.cotangentComplex)) :
    Subsingleton (Algebra.H1Cotangent R T) := by
  have hbij := Algebra.Extension.Cotangent.bijOn_ker_liftBaseChange_map_of_isLocalization
    (T := T) M ((Algebra.Generators.defaultHom P (Algebra.Generators.self R T)).toExtensionHom)
  have hker : LinearMap.ker (Algebra.Generators.self R T).toExtension.cotangentComplex = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hbij.surjOn hy
    have hx0 : x = 0 := by
      have hx' : x ∈ LinearMap.ker
          (LinearMap.baseChange T P.toExtension.cotangentComplex) := hx
      rw [LinearMap.ker_eq_bot.mpr hinj, Submodule.mem_bot] at hx'
      exact hx'
    rw [← hxy, hx0, map_zero]
  rw [show Algebra.H1Cotangent R T =
      (Algebra.Generators.self R T).toExtension.H1Cotangent from rfl,
    Algebra.Extension.subsingleton_h1Cotangent]
  exact LinearMap.ker_eq_bot.mp hker

/-- If the base changed conormal map of a presentation is split over a localization `T` of `B`,
then the module of differentials of `T` over `A` is projective. -/
private theorem projective_kaehlerDifferential_of_exists_leftInverse
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] {ι : Type*} (P : Algebra.Generators R S ι)
    (M : Submonoid S) [IsLocalization M T]
    (hl : ∃ l : T ⊗[S] P.toExtension.CotangentSpace →ₗ[T] T ⊗[S] P.toExtension.Cotangent,
      l ∘ₗ LinearMap.baseChange T P.toExtension.cotangentComplex = LinearMap.id) :
    Module.Projective T Ω[T⁄R] := by
  have : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_isLocalization M
  have hsurj : Function.Surjective
      (LinearMap.baseChange T P.toExtension.toKaehler) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact LinearMap.lTensor_surjective T Algebra.Extension.toKaehler_surjective
  have hex : Function.Exact (LinearMap.baseChange T P.toExtension.cotangentComplex)
      (LinearMap.baseChange T P.toExtension.toKaehler) := by
    simp only [LinearMap.baseChange_eq_lTensor]
    exact lTensor_exact T Algebra.Extension.exact_cotangentComplex_toKaehler
      Algebra.Extension.toKaehler_surjective
  obtain ⟨l, hlid⟩ := hl
  obtain ⟨s, hs⟩ := ((hex.split_tfae'.out 2 1 rfl rfl).mp ⟨hsurj, l, hlid⟩).2
  have : Module.Projective T (T ⊗[S] P.toExtension.CotangentSpace) := by
    have : Module.Free T (T ⊗[S] P.toExtension.CotangentSpace) :=
      Module.Free.of_basis (P.cotangentSpaceBasis.baseChange T)
    infer_instance
  have hproj : Module.Projective T (T ⊗[S] Ω[S⁄R]) :=
    Module.Projective.of_split s _ hs
  exact Module.Projective.of_equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T)

/-- **Smoothness from the retraction ideal.** If `a : B` lies in the retraction ideal of the
differential of a presentation of `B` over `A`, then `B_a` is smooth over `A`. -/
public theorem smooth_of_mem_retractionIdeal {a : B}
    (ha : a ∈ retractionIdeal (presentationDifferential G))
    (T : Type v) [CommRing T] [Algebra B T] [Algebra A T] [IsScalarTower A B T]
    [IsLocalization.Away a T] : Algebra.Smooth A T := by
  rw [retractionIdeal_presentationDifferential] at ha
  have hl := exists_leftInverse_baseChange_of_mem_retractionIdeal G ha T
    (IsLocalization.Away.algebraMap_isUnit a)
  have hfp : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact projective_kaehlerDifferential_of_exists_leftInverse G (Submonoid.powers a) hl
  · obtain ⟨l, hlid⟩ := hl
    exact subsingleton_h1Cotangent_of_injective_baseChange G (Submonoid.powers a)
      (Function.LeftInverse.injective (g := l) fun x ↦ LinearMap.congr_fun hlid x)
  · exact Algebra.FinitePresentation.of_isLocalizationAway (S' := T) a

omit [Algebra.FiniteType A B] in
/-- **The retraction ideal from smoothness.** If `A → B` is smooth at a prime `q`, then the
retraction ideal of the differential of a presentation of `B` is not contained in `q`. -/
public theorem not_retractionIdeal_le_of_smoothAt (q : Ideal B) [q.IsPrime]
    (hq : Algebra.SmoothAt A B q) :
    ¬ retractionIdeal (presentationDifferential G) ≤ q := by
  obtain ⟨g, hgq, hsm⟩ := hq
  set T := Localization.Away g with hT
  have : Algebra.FormallySmooth A T := hsm.formallySmooth
  obtain ⟨l, hl⟩ := Stacks.Smoothing.exists_leftInverse_cotangentComplex_baseChange
    (R := A) G (Submonoid.powers g) (T := T)
  -- descend the retraction from `T` to `B`
  set locC : G.toExtension.Cotangent →ₗ[B] T ⊗[B] G.toExtension.Cotangent :=
    TensorProduct.mk B T G.toExtension.Cotangent 1 with hlocC
  have hloc : IsLocalizedModule (Submonoid.powers g) locC :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g) T locC).mpr
      (TensorProduct.isBaseChange (R := B) (S := T) (M := G.toExtension.Cotangent))
  set locE : G.toExtension.CotangentSpace →ₗ[B] T ⊗[B] G.toExtension.CotangentSpace :=
    TensorProduct.mk B T G.toExtension.CotangentSpace 1 with hlocE
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (S := Submonoid.powers g) (f := locC)
    (M := G.toExtension.CotangentSpace) ((l.restrictScalars B) ∘ₗ locE)
  -- `h ∘ cotangentComplex` and `s • id` agree after localization
  have hagree : locC ∘ₗ (h ∘ₗ G.toExtension.cotangentComplex) =
      locC ∘ₗ ((s : B) • (LinearMap.id : G.toExtension.Cotangent →ₗ[B] _)) := by
    ext x
    have h1 : locC (h (G.toExtension.cotangentComplex x)) =
        (s : B) • l (locE (G.toExtension.cotangentComplex x)) := by
      have hx := LinearMap.congr_fun hs (G.toExtension.cotangentComplex x)
      simpa only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearMap.smul_apply,
        Submonoid.smul_def] using hx
    have h2 : locE (G.toExtension.cotangentComplex x) =
        LinearMap.baseChange T G.toExtension.cotangentComplex (locC x) := by
      change (1 : T) ⊗ₜ[B] G.toExtension.cotangentComplex x = _
      rw [show locC x = (1 : T) ⊗ₜ[B] x from rfl, LinearMap.baseChange_tmul]
    have h3 : l (LinearMap.baseChange T G.toExtension.cotangentComplex (locC x)) = locC x :=
      LinearMap.congr_fun hl (locC x)
    change locC (h (G.toExtension.cotangentComplex x)) = locC ((s : B) • x)
    rw [map_smul, h1, h2, h3]
  obtain ⟨t, ht⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
    (S := Submonoid.powers g) (f := locC) _ _ hagree
  -- so `t * s` lies in the retraction ideal and avoids `q`
  have hmem : ((t : B) * (s : B)) ∈ retractionIdeal G.toExtension.cotangentComplex := by
    refine ⟨(t : B) • h, ?_⟩
    have ht' : (t : B) • (h ∘ₗ G.toExtension.cotangentComplex) =
        (t : B) • ((s : B) • (LinearMap.id : G.toExtension.Cotangent →ₗ[B] _)) := by
      simpa only [Submonoid.smul_def] using ht
    rw [LinearMap.smul_comp, ht', smul_smul]
  rw [retractionIdeal_presentationDifferential]
  intro hle
  have hts : ((t : B) * (s : B)) ∈ q := hle hmem
  have hpow : ∀ u : Submonoid.powers g, (u : B) ∈ q → g ∈ q := fun u hu ↦ by
    obtain ⟨k, hk⟩ := u.2
    exact ‹q.IsPrime›.mem_of_pow_mem k (by rwa [show g ^ k = (u : B) from hk])
  exact hgq ((‹q.IsPrime›.mul_mem_iff_mem_or_mem.mp hts).elim (hpow t) (hpow s))

/-- **Smoothness at a prime is non-containment of the retraction ideal.** -/
public theorem smoothAt_iff_not_retractionIdeal_le (q : Ideal B) [q.IsPrime] :
    Algebra.SmoothAt A B q ↔ ¬ retractionIdeal (presentationDifferential G) ≤ q := by
  refine ⟨not_retractionIdeal_le_of_smoothAt G q, fun hq ↦ ?_⟩
  obtain ⟨a, ha, haq⟩ := Set.not_subset.mp hq
  exact ⟨a, haq, smooth_of_mem_retractionIdeal G ha (Localization.Away a)⟩

end Presentation

/-! ## Smoothness away from the vanishing locus of the ideal -/

/-- **Smoothness of `Spec(B) → Spec(A)` over `Spec(A) ∖ V(I)`**: the ring map `A → B` is smooth
(Definition 00TB) at every prime of `B` whose contraction to `A` does not contain `I`, that is at
every point of `Spec(B)` lying over the complement of `V(I)`. -/
public def SmoothAwayFrom (A : Type u) [CommRing A] (I : Ideal A) (B : Type v) [CommRing B]
    [Algebra A B] : Prop :=
  ∀ (q : Ideal B) (_ : q.IsPrime), ¬ I.map (algebraMap A B) ≤ q → Algebra.SmoothAt A B q

section SmoothAway

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {B : Type v} [CommRing B] [Algebra A B]
  [Algebra.FiniteType A B] {n : ℕ} (G : Algebra.Generators A B (Fin n)) {I : Ideal A}

/-- Smoothness over `Spec(A) ∖ V(I)` is the containment of `IB` in the radical of the retraction
ideal of the differential of a presentation. -/
public theorem smoothAwayFrom_iff_le_radical_retractionIdeal :
    SmoothAwayFrom A I B ↔
      I.map (algebraMap A B) ≤ (retractionIdeal (presentationDifferential G)).radical := by
  refine ⟨fun h ↦ ?_, fun h q hq hqI ↦ (smoothAt_iff_not_retractionIdeal_le G q).mpr fun hle ↦
    hqI (h.trans ((Ideal.radical_mono hle).trans_eq hq.radical))⟩
  rw [Ideal.radical_eq_sInf]
  exact le_sInf fun q ⟨hqle, hqp⟩ ↦ not_not.mp fun hnot ↦
    (smoothAt_iff_not_retractionIdeal_le G q).mp (h q hqp hnot) hqle

/-- Smoothness over `Spec(A) ∖ V(I)` makes a power of `IB` act through the differential of a
presentation. -/
public theorem exists_pow_le_retractionIdeal_of_smoothAwayFrom (h : SmoothAwayFrom A I B) :
    ∃ c : ℕ, (I.map (algebraMap A B)) ^ c ≤ retractionIdeal (presentationDifferential G) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  exact Ideal.exists_pow_le_of_le_radical_of_fg
    ((smoothAwayFrom_iff_le_radical_retractionIdeal G).mp h) (Ideal.fg_of_isNoetherianRing _)

omit [IsNoetherianRing A] in
/-- A finite type algebra has a presentation by finitely many variables. -/
public theorem nonempty_generators_fin :
    ∃ m : ℕ, Nonempty (Algebra.Generators A B (Fin m)) := by
  obtain ⟨m, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  refine ⟨m, ⟨Algebra.Generators.ofSurjective (fun i ↦ f (MvPolynomial.X i)) ?_⟩⟩
  have hfe : MvPolynomial.aeval (R := A) (fun i ↦ f (MvPolynomial.X i)) = f := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  rw [hfe]
  exact hf

end SmoothAway

/-! ## Transfer between a presentation and its completion -/

section Transfer

/-- A chain map of two-term complexes which is bijective in both degrees identifies the
factorizations of multiplication by a scalar through the differentials of its source and
target. -/
private theorem exists_retraction_iff_of_bijective {C : Type*} [CommRing C]
    {X Y : NaiveCotangent.TwoTerm C} (φ : NaiveCotangent.ChainMap X Y)
    (h1 : Function.Bijective φ.f₁) (h0 : Function.Bijective φ.f₀) (a : C) :
    (∃ l : X.X₀ →ₗ[C] X.X₁, l ∘ₗ X.d = a • LinearMap.id) ↔
      ∃ L : Y.X₀ →ₗ[C] Y.X₁, L ∘ₗ Y.d = a • LinearMap.id := by
  let e1 := LinearEquiv.ofBijective φ.f₁ h1
  let e0 := LinearEquiv.ofBijective φ.f₀ h0
  have hstep : ∀ y, Y.d (e1 y) = e0 (X.d y) := fun y ↦ LinearMap.congr_fun φ.comm y
  refine ⟨fun ⟨l, hl⟩ ↦ ⟨e1.toLinearMap ∘ₗ l ∘ₗ e0.symm.toLinearMap, ?_⟩,
    fun ⟨L, hL⟩ ↦ ⟨e1.symm.toLinearMap ∘ₗ L ∘ₗ e0.toLinearMap, ?_⟩⟩
  · ext z
    obtain ⟨y, rfl⟩ := e1.surjective z
    change e1 (l (e0.symm (Y.d (e1 y)))) = a • e1 y
    have hly : l (X.d y) = a • y := LinearMap.congr_fun hl y
    rw [hstep, e0.symm_apply_apply, hly, map_smul]
  · ext y
    change e1.symm (L (e0 (X.d y))) = a • y
    have hLy : L (Y.d (e1 y)) = a • e1 y := LinearMap.congr_fun hL (e1 y)
    rw [← hstep, hLy, map_smul, e1.symm_apply_apply]

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {B : Type v} [CommRing B]
  [Algebra A B] [Algebra.FiniteType A B] {n : ℕ} (G : Algebra.Generators A B (Fin n))

/-- The base change to `B^` of a factorization of multiplication by `a` through the differential
of a presentation of `B`, read through the comparison of Stacks 0GAF. -/
private theorem baseChange_comp_presentationDifferential (a : A)
    (h : (Fin n → B) →ₗ[B] G.toExtension.Cotangent)
    (hh : h ∘ₗ presentationDifferential G = (algebraMap A B a) • LinearMap.id) :
    LinearMap.baseChange (adicCompletionObj I (B := B)).carrier h ∘ₗ
        LinearMap.baseChange (adicCompletionObj I (B := B)).carrier
          (presentationDifferential G) =
      (algebraMap A (adicCompletionObj I (B := B)).carrier a) •
        (LinearMap.id : (adicCompletionObj I (B := B)).carrier ⊗[B] G.toExtension.Cotangent
          →ₗ[(adicCompletionObj I (B := B)).carrier] _) := by
  rw [← LinearMap.baseChange_comp, hh, baseChange_smul_id,
    ← IsScalarTower.algebraMap_apply A B (adicCompletionObj I (B := B)).carrier a]

/-- **Stacks 0GAF transfer, forwards.** A factorization of multiplication by `a : A` through the
differential of a presentation of `B` gives one through the differential of the completed naive
cotangent complex of the completed presentation. -/
private theorem exists_factorization_completed_of_factorization (a : A)
    (h : (Fin n → B) →ₗ[B] G.toExtension.Cotangent)
    (hh : h ∘ₗ presentationDifferential G = (algebraMap A B a) • LinearMap.id) :
    ∃ H : (Fin n → (adicCompletionObj I (B := B)).carrier) →ₗ[(adicCompletionObj I
          (B := B)).carrier] (presentationCompletion I G).extension.Cotangent,
      H ∘ₗ (completedComplex I G).differential =
        (algebraMap A (adicCompletionObj I (B := B)).carrier a) • LinearMap.id :=
  (exists_retraction_iff_of_bijective (completionComparison I G)
    (bijective_completionComparison_f₁ I G) (bijective_completionComparison_f₀ I G) _).mp
    ⟨LinearMap.baseChange (adicCompletionObj I (B := B)).carrier h,
      baseChange_comp_presentationDifferential I G a h hh⟩

/-- **Stacks 0GAF transfer, backwards.** A factorization of multiplication by `a : A` through the
differential of the completed naive cotangent complex gives one through the base change to `B^`
of the differential of the presentation of `B`. -/
private theorem exists_baseChange_factorization_of_factorization_completed (a : A)
    (H : (Fin n → (adicCompletionObj I (B := B)).carrier) →ₗ[(adicCompletionObj I
          (B := B)).carrier] (presentationCompletion I G).extension.Cotangent)
    (hH : H ∘ₗ (completedComplex I G).differential =
      (algebraMap A (adicCompletionObj I (B := B)).carrier a) • LinearMap.id) :
    ∃ L : (adicCompletionObj I (B := B)).carrier ⊗[B] (Fin n → B) →ₗ[(adicCompletionObj I
          (B := B)).carrier] (adicCompletionObj I (B := B)).carrier ⊗[B]
            G.toExtension.Cotangent,
      L ∘ₗ LinearMap.baseChange (adicCompletionObj I (B := B)).carrier
          (presentationDifferential G) =
        (algebraMap A (adicCompletionObj I (B := B)).carrier a) • LinearMap.id :=
  (exists_retraction_iff_of_bijective (completionComparison I G)
    (bijective_completionComparison_f₁ I G) (bijective_completionComparison_f₀ I G) _).mpr
    ⟨H, hH⟩

end Transfer

/-! ## The linear system cut out by a generating family of the conormal module -/

section RelationSystem

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {B : Type v} [CommRing B] [Algebra A B]
  [Algebra.FiniteType A B] {n : ℕ} (G : Algebra.Generators A B (Fin n))
  {k : ℕ} (z : Fin k → G.toExtension.Cotangent)

omit [IsNoetherianRing A] [Algebra.FiniteType A B] in
/-- The `B`-linear map sending a tuple `y` of elements of the conormal module to the tuple
`j ↦ ∑ i, (∂ f_j / ∂ x_i) · y i`; a solution of `relationMap y = a • z` is the same thing as a
factorization of multiplication by `a` through the differential of the presentation. -/
public def relationMap :
    (Fin n → G.toExtension.Cotangent) →ₗ[B] (Fin k → G.toExtension.Cotangent) :=
  LinearMap.pi fun j ↦ ∑ i, (presentationDifferential G (z j) i) • LinearMap.proj i

omit [IsNoetherianRing A] [Algebra.FiniteType A B] in
/-- The `j`-th component of `Rig.relationMap` reads the coefficients of `d (z j)` against the
given tuple. -/
@[simp] public theorem relationMap_apply (y : Fin n → G.toExtension.Cotangent) (j : Fin k) :
    relationMap G z y j = ∑ i, (presentationDifferential G (z j) i) • y i := by
  simp [relationMap, LinearMap.pi_apply, LinearMap.sum_apply]

omit [IsNoetherianRing A] [Algebra.FiniteType A B] in
/-- The `B`-linear map determined by prescribing the images of the standard basis. -/
private def homOfVec (y : Fin n → G.toExtension.Cotangent) :
    (Fin n → B) →ₗ[B] G.toExtension.Cotangent :=
  ∑ i, (LinearMap.proj i).smulRight (y i)

omit [IsNoetherianRing A] [Algebra.FiniteType A B] in
private theorem homOfVec_apply (y : Fin n → G.toExtension.Cotangent) (e : Fin n → B) :
    homOfVec G y e = ∑ i, (e i) • y i := by
  simp [homOfVec, LinearMap.sum_apply]

omit [IsNoetherianRing A] [Algebra.FiniteType A B] in
private theorem homOfVec_eq (h : (Fin n → B) →ₗ[B] G.toExtension.Cotangent) :
    homOfVec G (fun i ↦ h (Pi.single i 1)) = h := by
  classical
  classical
  apply (Pi.basisFun B (Fin n)).ext
  intro i
  rw [Pi.basisFun_apply, homOfVec_apply]
  simp [Pi.single_apply, Finset.sum_ite_eq']

omit [IsNoetherianRing A] [Algebra.FiniteType A B] in
private theorem homOfVec_presentationDifferential (y : Fin n → G.toExtension.Cotangent)
    (j : Fin k) :
    homOfVec G y (presentationDifferential G (z j)) = relationMap G z y j := by
  rw [homOfVec_apply, relationMap_apply]

omit [IsNoetherianRing A] [Algebra.FiniteType A B] in
/-- **Membership in the retraction ideal is the solvability of a linear system.** -/
public theorem mem_retractionIdeal_iff_smul_mem_range
    (hz : Submodule.span B (Set.range z) = ⊤) (a : B) :
    a ∈ retractionIdeal (presentationDifferential G) ↔
      (a • z) ∈ LinearMap.range (relationMap G z) := by
  refine ⟨fun ⟨h, hh⟩ ↦ ⟨fun i ↦ h (Pi.single i 1), funext fun j ↦ ?_⟩,
    fun ⟨y, hy⟩ ↦ ⟨homOfVec G y, ?_⟩⟩
  · rw [← homOfVec_presentationDifferential G z, homOfVec_eq G h]
    simpa using LinearMap.congr_fun hh (z j)
  · have hgen : ∀ w ∈ Submodule.span B (Set.range z),
        homOfVec G y (presentationDifferential G w) = a • w := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨j, rfl⟩ := hw
        rw [homOfVec_presentationDifferential G z y j, hy]
        rfl
      | zero => simp
      | add w w' _ _ ihw ihw' => rw [map_add, map_add, ihw, ihw', smul_add]
      | smul c w _ ih => rw [map_smul, map_smul, ih, smul_comm]
    refine LinearMap.ext fun w ↦ ?_
    simpa using hgen w (hz ▸ Submodule.mem_top)

omit [IsNoetherianRing A] [Algebra.FiniteType A B] in
/-- **Membership in the retraction ideal is the annihilation of a class in a cokernel.** -/
public theorem mem_retractionIdeal_iff_smul_mkQ_eq_zero
    (hz : Submodule.span B (Set.range z) = ⊤) (a : B) :
    a ∈ retractionIdeal (presentationDifferential G) ↔
      a • (LinearMap.range (relationMap G z)).mkQ z = 0 := by
  rw [mem_retractionIdeal_iff_smul_mem_range G z hz a, ← map_smul, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]

omit [IsNoetherianRing A] [Algebra.FiniteType A B] in
/-- The base change of the relation map, read in coordinates. -/
private theorem piRight_baseChange_relationMap {S : Type*} [CommRing S] [Algebra B S]
    (w : S ⊗[B] (Fin n → G.toExtension.Cotangent)) (j : Fin k) :
    TensorProduct.piRight B S S (fun _ : Fin k ↦ G.toExtension.Cotangent)
        (LinearMap.baseChange S (relationMap G z) w) j =
      ∑ i, (algebraMap B S (presentationDifferential G (z j) i)) •
        (TensorProduct.piRight B S S (fun _ : Fin n ↦ G.toExtension.Cotangent) w i) := by
  classical
  induction w using TensorProduct.inductionOn with
  | tmul s y =>
    have hpi : ∀ {m : ℕ} (w : Fin m → G.toExtension.Cotangent) (i : Fin m),
        TensorProduct.piRight B S S (fun _ : Fin m ↦ G.toExtension.Cotangent) (s ⊗ₜ[B] w) i =
          s ⊗ₜ[B] w i := fun w i ↦ by
      simp [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
    rw [LinearMap.baseChange_tmul, hpi, relationMap_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hpi, TensorProduct.tmul_smul, algebraMap_smul]
  | add w w' hw hw' =>
    rw [map_add, map_add, Pi.add_apply, hw, hw', map_add]
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]

omit [IsNoetherianRing A] [Algebra.FiniteType A B] in
/-- If multiplication by `a` factors through the base change of the differential over a
`B`-algebra `S`, then `a` annihilates the base changed class of the generating family. -/
private theorem smul_tmul_mkQ_eq_zero_of_baseChange {S : Type*} [CommRing S] [Algebra B S]
    (a : B)
    (L : S ⊗[B] (Fin n → B) →ₗ[S] S ⊗[B] G.toExtension.Cotangent)
    (hL : L ∘ₗ LinearMap.baseChange S (presentationDifferential G) =
      (algebraMap B S a) • LinearMap.id) :
    (algebraMap B S a) • ((1 : S) ⊗ₜ[B]
        ((LinearMap.range (relationMap G z)).mkQ z)) = 0 := by
  classical
  set pk := TensorProduct.piRight B S S (fun _ : Fin k ↦ G.toExtension.Cotangent) with hpk
  set pn := TensorProduct.piRight B S S (fun _ : Fin n ↦ G.toExtension.Cotangent) with hpn
  set u : S ⊗[B] (Fin n → G.toExtension.Cotangent) :=
    pn.symm (fun i ↦ L ((1 : S) ⊗ₜ[B] Pi.single i 1)) with hu
  have hpnu : ∀ i, pn u i = L ((1 : S) ⊗ₜ[B] Pi.single i 1) := by
    intro i
    rw [hu, pn.apply_symm_apply]
  have hkey : LinearMap.baseChange S (relationMap G z) u =
      (algebraMap B S a) • ((1 : S) ⊗ₜ[B] z) := by
    apply pk.injective
    funext j
    have hvec : ((1 : S) ⊗ₜ[B] presentationDifferential G (z j) : S ⊗[B] (Fin n → B)) =
        ∑ i, (algebraMap B S (presentationDifferential G (z j) i)) •
          ((1 : S) ⊗ₜ[B] (Pi.single i 1 : Fin n → B)) := by
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) ↦
        (by rw [algebraMap_smul, ← TensorProduct.tmul_smul] :
          (algebraMap B S (presentationDifferential G (z j) i)) •
              ((1 : S) ⊗ₜ[B] (Pi.single i 1 : Fin n → B)) =
            (1 : S) ⊗ₜ[B] ((presentationDifferential G (z j) i) •
              (Pi.single i 1 : Fin n → B))), ← TensorProduct.tmul_sum,
        sum_smul_single (presentationDifferential G (z j))]
    have hLd : L ((1 : S) ⊗ₜ[B] presentationDifferential G (z j)) =
        (algebraMap B S a) • ((1 : S) ⊗ₜ[B] z j) := by
      have hb : L (LinearMap.baseChange S (presentationDifferential G)
          ((1 : S) ⊗ₜ[B] z j)) = (algebraMap B S a) • ((1 : S) ⊗ₜ[B] z j) := by
        have hc := LinearMap.congr_fun hL ((1 : S) ⊗ₜ[B] z j)
        simpa using hc
      rwa [LinearMap.baseChange_tmul] at hb
    have hrhs : pk ((algebraMap B S a) • ((1 : S) ⊗ₜ[B] z)) j =
        (algebraMap B S a) • ((1 : S) ⊗ₜ[B] z j) := by
      rw [map_smul, Pi.smul_apply, hpk]
      congr 1
    rw [hrhs, piRight_baseChange_relationMap G z u j]
    calc ∑ i, (algebraMap B S (presentationDifferential G (z j) i)) • pn u i
        = ∑ i, (algebraMap B S (presentationDifferential G (z j) i)) •
            L ((1 : S) ⊗ₜ[B] (Pi.single i 1 : Fin n → B)) :=
          Finset.sum_congr rfl fun i _ ↦ congrArg
            (fun w ↦ (algebraMap B S (presentationDifferential G (z j) i)) • w) (hpnu i)
      _ = L (∑ i, (algebraMap B S (presentationDifferential G (z j) i)) •
            ((1 : S) ⊗ₜ[B] (Pi.single i 1 : Fin n → B))) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ ↦ (map_smul L _ _).symm
      _ = L ((1 : S) ⊗ₜ[B] presentationDifferential G (z j)) := by rw [← hvec]
      _ = (algebraMap B S a) • ((1 : S) ⊗ₜ[B] z j) := hLd
  calc (algebraMap B S a) • ((1 : S) ⊗ₜ[B]
        ((LinearMap.range (relationMap G z)).mkQ z))
      = LinearMap.baseChange S (LinearMap.range (relationMap G z)).mkQ
          ((algebraMap B S a) • ((1 : S) ⊗ₜ[B] z)) := by
        rw [map_smul, LinearMap.baseChange_tmul]
    _ = LinearMap.baseChange S (LinearMap.range (relationMap G z)).mkQ
          (LinearMap.baseChange S (relationMap G z) u) := by rw [hkey]
    _ = LinearMap.baseChange S
          ((LinearMap.range (relationMap G z)).mkQ ∘ₗ relationMap G z) u := by
        rw [LinearMap.baseChange_comp]
        rfl
    _ = 0 := by rw [LinearMap.range_mkQ_comp, LinearMap.baseChange_zero, LinearMap.zero_apply]

end RelationSystem

/-! ## Vanishing in the completion -/

section CompletionVanishing

variable {B : Type v} [CommRing B] [IsNoetherianRing B] (K : Ideal B)
  {M : Type*} [AddCommGroup M] [Module B M]

/-- A finitely generated submodule whose image in `B^ ⊗_B M` vanishes satisfies `M₀ ⊆ K · M₀`,
because `B → B^` is flat and `B^ ⊗_B M₀ = M₀^` has `M₀ / K M₀` as a quotient. -/
private theorem le_smul_of_tmul_eq_zero (M₀ : Submodule B M) (hfg : M₀.FG)
    (hzero : ∀ (s : AdicCompletion K B) (m : M), m ∈ M₀ →
      (s ⊗ₜ[B] m : AdicCompletion K B ⊗[B] M) = 0) :
    M₀ ≤ K • M₀ := by
  have hfin : Module.Finite B ↥M₀ := Module.Finite.iff_fg.mpr hfg
  have hinj : Function.Injective
      (LinearMap.lTensor (AdicCompletion K B) M₀.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  have hzero' : ∀ x : AdicCompletion K B ⊗[B] ↥M₀,
      LinearMap.lTensor (AdicCompletion K B) M₀.subtype x = 0 := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s m => rw [LinearMap.lTensor_tmul]; exact hzero s m.1 m.2
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
  have hsub : Subsingleton (AdicCompletion K B ⊗[B] ↥M₀) :=
    ⟨fun x y ↦ hinj (by rw [hzero' x, hzero' y])⟩
  -- `B^ → B / K` is a surjection of `B`-modules, so `(B / K) ⊗ M₀ = 0` as well
  have hKeq : (K ^ 1 • (⊤ : Submodule B B)) = K := by simp
  have hφ : Function.Surjective
      ((Submodule.quotEquivOfEq (K ^ 1 • (⊤ : Submodule B B)) K hKeq).toLinearMap ∘ₗ
        AdicCompletion.eval K B 1) :=
    (Submodule.quotEquivOfEq _ _ hKeq).surjective.comp (AdicCompletion.eval_surjective K B 1)
  have hsubQ : Subsingleton ((B ⧸ K) ⊗[B] ↥M₀) :=
    (LinearMap.rTensor_surjective (↥M₀) hφ).subsingleton
  have htop : (K • (⊤ : Submodule B ↥M₀)) = ⊤ := by
    rw [← Submodule.Quotient.subsingleton_iff]
    exact (TensorProduct.quotTensorEquivQuotSMul (↥M₀) K).symm.injective.subsingleton
  have hmap : K • M₀ = M₀ := by
    have hc := congrArg (Submodule.map M₀.subtype) htop
    rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at hc
  exact hmap.ge

end CompletionVanishing

/-! ## Stacks 0GAK -/

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {B : Type v} [CommRing B]
  [Algebra A B] [Algebra.FiniteType A B]

/-- **Stacks 0GAK (1).** If `Spec(B) → Spec(A)` is smooth over `Spec(A) ∖ V(I)`, then the
`I`-adic completion `B^` is rig-smooth over `(A, I)`. -/
@[stacks 0GAK "part (1)"]
public theorem isRigSmooth_adicCompletionObj_of_smoothAwayFrom (h : SmoothAwayFrom A I B) :
    IsRigSmooth (adicCompletionObj I (B := B)) := by
  obtain ⟨m, ⟨G⟩⟩ := nonempty_generators_fin (A := A) (B := B)
  obtain ⟨c, hc⟩ := exists_pow_le_retractionIdeal_of_smoothAwayFrom (I := I) G h
  rw [isRigSmooth_iff_cotangentFactorization _ (presentationCompletion I G)]
  refine ⟨c, fun a ha ↦ ?_⟩
  have hmem : algebraMap A B a ∈ (I.map (algebraMap A B)) ^ c := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha
  obtain ⟨hh, hhh⟩ := hc hmem
  exact exists_factorization_completed_of_factorization I G a hh hhh

/-- Smoothness of `A → B` at every prime of `B` avoiding `g` and lying over `Spec(A) ∖ V(I)` is
smoothness of `Spec(B_g) → Spec(A)` over `Spec(A) ∖ V(I)`. -/
public theorem smoothAwayFrom_of_forall_notMem (g : B) (C : Type v) [CommRing C] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [IsLocalization.Away g C]
    (h : ∀ (q : Ideal B) (_ : q.IsPrime), g ∉ q → ¬ I.map (algebraMap A B) ≤ q →
      Algebra.SmoothAt A B q) :
    SmoothAwayFrom A I C := by
  have hfpB : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have hfpC : Algebra.FinitePresentation A C :=
    Algebra.FinitePresentation.of_isLocalizationAway (S' := C) g
  intro q' hq' hq'I
  have hpp : (Ideal.comap (algebraMap B C) q').IsPrime := Ideal.comap_isPrime _ _
  have hgp : g ∉ Ideal.comap (algebraMap B C) q' := by
    intro hmem
    exact hq'.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_comap.mp hmem)
      (IsLocalization.Away.algebraMap_isUnit g))
  have hKp : ¬ I.map (algebraMap A B) ≤ Ideal.comap (algebraMap B C) q' := fun hle ↦ hq'I <| by
    rwa [IsScalarTower.algebraMap_eq A B C, ← Ideal.map_map, Ideal.map_le_iff_le_comap]
  have hsm := h _ hpp hgp hKp
  rw [Algebra.smoothAt_iff_isSmoothAt A B] at hsm
  rw [Algebra.smoothAt_iff_isSmoothAt A C]
  have hloc := Algebra.smoothLocus_comap_of_isLocalization (R := A) (A := B) (Af := C) g
  have hmemC : (⟨q', hq'⟩ : PrimeSpectrum C) ∈ Algebra.smoothLocus A C := by
    rw [← hloc]
    exact hsm
  exact hmemC

/-- **Stacks 0GAK (2).** If the `I`-adic completion `B^` is rig-smooth over `(A, I)`, then there
is `g ∈ 1 + IB` such that `Spec(B_g) → Spec(A)` is smooth over `Spec(A) ∖ V(I)`. -/
@[stacks 0GAK "part (2)"]
public theorem exists_sub_one_mem_and_smoothAwayFrom_of_isRigSmooth
    (h : IsRigSmooth (adicCompletionObj I (B := B))) :
    ∃ g : B, g - 1 ∈ I.map (algebraMap A B) ∧ SmoothAwayFrom A I (Localization.Away g) := by
  classical
  have hBnoe : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  obtain ⟨m, ⟨G⟩⟩ := nonempty_generators_fin (A := A) (B := B)
  obtain ⟨k, z, hz⟩ := Module.Finite.exists_fin (R := B) (M := G.toExtension.Cotangent)
  rw [isRigSmooth_iff_cotangentFactorization _ (presentationCompletion I G)] at h
  obtain ⟨c, hc⟩ := h
  set K : Ideal B := I.map (algebraMap A B) with hK
  set Mq := (Fin k → G.toExtension.Cotangent) ⧸ LinearMap.range (relationMap G z) with hMq
  set x : Mq := (LinearMap.range (relationMap G z)).mkQ z with hx
  set Jx : Ideal B := LinearMap.ker (LinearMap.toSpanSingleton B
    (AdicCompletion K B ⊗[B] Mq) ((1 : AdicCompletion K B) ⊗ₜ[B] x)) with hJx
  have hKc : K ^ c ≤ Jx := by
    rw [hK, ← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro a ha
    obtain ⟨H, hH⟩ := hc a ha
    obtain ⟨L, hL⟩ := exists_baseChange_factorization_of_factorization_completed I G a H hH
    have hLB : L ∘ₗ LinearMap.baseChange (adicCompletionObj I (B := B)).carrier
          (presentationDifferential G) =
        (algebraMap B (adicCompletionObj I (B := B)).carrier (algebraMap A B a)) •
          LinearMap.id := by
      rw [hL, ← IsScalarTower.algebraMap_apply A B (adicCompletionObj I (B := B)).carrier a]
    have hzero := smul_tmul_mkQ_eq_zero_of_baseChange G z (algebraMap A B a) L hLB
    refine Ideal.mem_comap.mpr (LinearMap.mem_ker.mpr ?_)
    rw [LinearMap.toSpanSingleton_apply, ← algebraMap_smul (AdicCompletion K B)]
    exact hzero
  set M₀ : Submodule B Mq := Submodule.map (LinearMap.toSpanSingleton B Mq x) (K ^ c) with hM₀
  have hM₀fg : M₀.FG := Submodule.FG.map _ (Ideal.fg_of_isNoetherianRing _)
  have hM₀zero : ∀ (s : AdicCompletion K B) (w : Mq), w ∈ M₀ →
      (s ⊗ₜ[B] w : AdicCompletion K B ⊗[B] Mq) = 0 := by
    rintro s w hw
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hw
    have hbJ : (algebraMap B (AdicCompletion K B) b) •
        ((1 : AdicCompletion K B) ⊗ₜ[B] x) = (0 : AdicCompletion K B ⊗[B] Mq) := by
      rw [algebraMap_smul, ← LinearMap.toSpanSingleton_apply]
      exact LinearMap.mem_ker.mp (hKc hb)
    change (s ⊗ₜ[B] (b • x) : AdicCompletion K B ⊗[B] Mq) = 0
    rw [← mul_one s, ← smul_eq_mul, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
      ← algebraMap_smul (AdicCompletion K B) b, hbJ, smul_zero]
  obtain ⟨g, hg1, hg0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul K M₀
    hM₀fg (le_smul_of_tmul_eq_zero K M₀ hM₀fg hM₀zero)
  refine ⟨g, hg1, ?_⟩
  refine smoothAwayFrom_of_forall_notMem I g (Localization.Away g) ?_
  intro q hq hgq hKq
  rw [smoothAt_iff_not_retractionIdeal_le G q]
  have hnot : ¬ I ≤ Ideal.comap (algebraMap A B) q := by
    intro hle'
    exact hKq (Ideal.map_le_iff_le_comap.mpr hle')
  obtain ⟨a₀, ha₀, ha₀q⟩ := Set.not_subset.mp hnot
  have hbK : (algebraMap A B a₀) ^ c ∈ K ^ c :=
    Ideal.pow_mem_pow (by rw [hK]; exact Ideal.mem_map_of_mem _ ha₀) c
  have hbq : (algebraMap A B a₀) ^ c ∉ q := fun hmem ↦
    ha₀q (Ideal.mem_comap.mpr (hq.mem_of_pow_mem c hmem))
  have hmemM₀ : ((algebraMap A B a₀) ^ c) • x ∈ M₀ :=
    Submodule.mem_map.mpr ⟨(algebraMap A B a₀) ^ c, hbK, rfl⟩
  have hmemF : g * (algebraMap A B a₀) ^ c ∈
      retractionIdeal (presentationDifferential G) := by
    rw [mem_retractionIdeal_iff_smul_mkQ_eq_zero G z hz, ← hx, ← smul_smul]
    exact hg0 _ hmemM₀
  intro hcon
  rcases hq.mul_mem_iff_mem_or_mem.mp (hcon hmemF) with hcc | hcc
  · exact hgq hcc
  · exact hbq hcc

end Main

end Rig

end
