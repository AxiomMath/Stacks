module

public import Mathlib.RingTheory.Spectrum.Maximal.Localization
public import StacksFrontier.Algebra.Module.FiniteLength.Determinant
public import StacksFrontier.Algebra.Module.FiniteLength.DeterminantProduct
public import StacksFrontier.RingTheory.Artinian.Basic
public import StacksFrontier.RingTheory.Length.FlatLocalHom

/-!
# Norms and lengths of a local quotient under a flat local base change

Let `A → S` be a flat local homomorphism of local rings with `m = length_S(S / 𝔪_A S)`, let `B`
be a local `A`-algebra along a local homomorphism whose residue field is finite over that of `A`,
and let `π`, `u` be elements of `B` with `B / πB` of finite length. Writing `T = S ⊗_A B` and
letting `𝔮` run over the maximal ideals of `T`, one has

```
(Norm_{κ(B)/κ(A)}(ū) ^ length_B(B / πB)) ^ m
  = ∏_𝔮 Norm_{κ(T_𝔮)/κ(S)}(ū) ^ length_{T_𝔮}(T_𝔮 / πT_𝔮)
```

in `κ(S)`, the left-hand side being read there through `κ(A) → κ(S)`.

## Main results

* `Stacks.Length.map_norm_pow_length_eq_prod_norm_pow_length_support` — the identity, with the
  product over the maximal ideals of `T` containing the image of `π`.
* `Stacks.Length.map_norm_pow_length_eq_prod_norm_pow_length` — the identity, with the product
  over all of `MaximalSpectrum T`.

## References

* [Stacks Project, Tag 0GU1](https://stacks.math.columbia.edu/tag/0GU1)
* [Stacks Project, Tag 0GSZ](https://stacks.math.columbia.edu/tag/0GSZ)
* [Stacks Project, Tag 0GT0](https://stacks.math.columbia.edu/tag/0GT0)
-/

@[expose] public section

open IsLocalRing

open scoped TensorProduct
open FiniteLengthEndomorphism (isFiniteLength_pi)

universe u v w

namespace Stacks.Length

/-- A module of finite length over a local ring stays of finite length after restriction of
scalars along a local homomorphism with finite residue field extension. -/
theorem isFiniteLength_restrictScalars_of_finite_residueField
    (R : Type u) [CommRing R] [IsLocalRing R]
    (R' : Type v) [CommRing R'] [IsLocalRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')]
    [Module.Finite (ResidueField R) (ResidueField R')]
    (M : Type w) [AddCommGroup M] [Module R M] [Module R' M] [IsScalarTower R R' M]
    (hM : IsFiniteLength R' M) : IsFiniteLength R M :=
  Module.length_ne_top_iff.mp <| by
    rw [IsLocalRing.length_restrictScalars R R' M]
    exact WithTop.mul_ne_top (Module.length_ne_top_iff.mpr hM)
      (by rw [Module.length_eq_finrank]; exact ENat.natCast_ne_top _)

/-- Finite length over `R` implies finite length over any `R`-algebra `R'` acting compatibly. -/
private theorem isFiniteLength_of_isScalarTower {R : Type*} [CommRing R] {R' : Type*} [CommRing R']
    [Algebra R R'] {M : Type*} [AddCommGroup M] [Module R M] [Module R' M]
    [IsScalarTower R R' M] (h : IsFiniteLength R M) : IsFiniteLength R' M := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at h ⊢
  exact ⟨isNoetherian_of_tower R h.1, isArtinian_of_tower R h.2⟩

/-- The quotient of a localization at a prime is the localization of the quotient at the image
of that prime. -/
theorem isLocalization_quotient_atPrime {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] (Rₚ : Type v) [CommRing Rₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p] (I : Ideal R) (q : Ideal (R ⧸ I)) [q.IsPrime]
    (hq : q.comap (Ideal.Quotient.mk I) = p) :
    IsLocalization.AtPrime (Rₚ ⧸ I.map (algebraMap R Rₚ)) q := by
  have hsub : Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl = q.primeCompl := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨z, hz, hzy⟩ hmem
      subst hq
      refine hz ?_
      have hzz : Ideal.Quotient.mk I z = Ideal.Quotient.mk I y := by
        simpa [Ideal.Quotient.algebraMap_eq] using hzy
      simpa [Ideal.mem_comap, hzz] using hmem
    · exact fun hx ↦ ⟨y, by subst hq; exact hx, rfl⟩
  have := IsLocalization.instQuotientIdealAlgebraMapSubmonoidMapRingHomAlgebraMap
    (M := p.primeCompl) (S := Rₚ) I
  rwa [hsub] at this

/-! ### The determinant of a product of endomorphisms -/

section Pi

variable {R : Type*} [CommRing R]

/-- The endomorphism of a product acting by a given endomorphism in each factor. -/
def piEnd {ι : Type*} (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (φ : ∀ i, Module.End R (M i)) : Module.End R (∀ i, M i) :=
  LinearMap.pi fun i => (φ i).comp (LinearMap.proj i)

variable [IsLocalRing R]

/-- The determinant of a finite-length endomorphism is unchanged by an equivariant isomorphism. -/
theorem det_congr_linearEquiv
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (φ : Module.End R M) (ψ : Module.End R N) (e : M ≃ₗ[R] N)
    (hφ : e.toLinearMap.comp φ = ψ.comp e.toLinearMap) :
    FiniteLengthEndomorphism.det R hM φ = FiniteLengthEndomorphism.det R hN ψ := by
  let g : N →ₗ[R] PUnit.{1} := 0
  have hg : Function.Surjective g := fun _ ↦ ⟨0, Subsingleton.elim _ _⟩
  have hexact : Function.Exact e.toLinearMap g := by
    rw [LinearMap.exact_iff]
    simp [g]
  have hcomm : g.comp ψ = (0 : Module.End R PUnit.{1}).comp g := by ext x
  simpa using (FiniteLengthEndomorphism.det_exact R M N PUnit.{1} hM hN
    IsFiniteLength.of_subsingleton φ ψ 0 e.toLinearMap g e.injective hexact hg hφ hcomm).symm

/-- The determinant of an endomorphism of a binary product is the product of the determinants. -/
theorem det_prodMap {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (hMN : IsFiniteLength R (M × N))
    (φ : Module.End R M) (ψ : Module.End R N) :
    FiniteLengthEndomorphism.det R hMN (LinearMap.prodMap φ ψ) =
      FiniteLengthEndomorphism.det R hM φ * FiniteLengthEndomorphism.det R hN ψ := by
  let f : M →ₗ[R] M × N := LinearMap.inl R M N
  let g : M × N →ₗ[R] N := LinearMap.snd R M N
  have hf : Function.Injective f := fun x y h => congrArg Prod.fst h
  have hex : Function.Exact f g := by
    rw [LinearMap.exact_iff]
    ext x
    rcases x with ⟨x, y⟩
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hy
      simp only [g, LinearMap.snd_apply] at hy
      exact ⟨x, Prod.ext rfl hy.symm⟩
    · rintro ⟨x', hx'⟩
      simp only [f, LinearMap.inl_apply, Prod.mk.injEq] at hx'
      exact hx'.2.symm
  have hg : Function.Surjective g := fun y ↦ ⟨(0, y), rfl⟩
  have hφ : f.comp φ = (LinearMap.prodMap φ ψ).comp f := by
    ext x <;> simp [f, LinearMap.prodMap]
  have hψ : g.comp (LinearMap.prodMap φ ψ) = ψ.comp g := by
    ext x <;> simp [g, LinearMap.prodMap]
  exact FiniteLengthEndomorphism.det_exact R M (M × N) N hM hMN hN φ
    (LinearMap.prodMap φ ψ) ψ f g hf hex hg hφ hψ

/-- **The determinant of a product of endomorphisms is the product of the determinants.** -/
theorem det_piEnd {ι : Type v} [Fintype ι] (M : ι → Type w) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] (hM : ∀ i, IsFiniteLength R (M i))
    (φ : ∀ i, Module.End R (M i)) :
    FiniteLengthEndomorphism.det R (isFiniteLength_pi M hM) (piEnd M φ) =
      ∏ i, FiniteLengthEndomorphism.det R (hM i) (φ i) := by
  classical
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ (M : ι → Type w) [∀ i, AddCommGroup (M i)]
      [∀ i, Module R (M i)] (hM : ∀ i, IsFiniteLength R (M i))
      (φ : ∀ i, Module.End R (M i)),
      FiniteLengthEndomorphism.det R (isFiniteLength_pi M hM) (piEnd M φ) =
        ∏ i, FiniteLengthEndomorphism.det R (hM i) (φ i))
    ?_ ?_ ?_ ι M hM φ
  · intro α β _ e IH (M : β → Type w) _ _ hM φ
    let : Fintype α := Fintype.ofEquiv β e.symm
    let hM' : ∀ a : α, IsFiniteLength R (M (e a)) := fun a => hM (e a)
    let φ' : ∀ a : α, Module.End R (M (e a)) := fun a => φ (e a)
    let E := LinearEquiv.piCongrLeft R M e
    have hcomm : E.toLinearMap.comp (piEnd (fun a => M (e a)) φ') =
        (piEnd M φ).comp E.toLinearMap := by
      apply LinearMap.ext
      intro x
      apply E.symm.injective
      show E.symm (E (piEnd (fun a => M (e a)) φ' x)) = E.symm (piEnd M φ (E x))
      rw [LinearEquiv.symm_apply_apply]
      funext a
      show φ' a (x a) = φ (e a) ((Equiv.piCongrLeft M e) x (e a))
      rw [Equiv.piCongrLeft_apply_apply]
    have hdet := det_congr_linearEquiv (isFiniteLength_pi _ hM')
      (isFiniteLength_pi M hM) _ _ E hcomm
    calc
      FiniteLengthEndomorphism.det R (isFiniteLength_pi M hM) (piEnd M φ) =
          FiniteLengthEndomorphism.det R (isFiniteLength_pi _ hM')
            (piEnd (fun a => M (e a)) φ') := hdet.symm
      _ = ∏ a, FiniteLengthEndomorphism.det R (hM' a) (φ' a) :=
        IH (fun a => M (e a)) hM' φ'
      _ = ∏ b, FiniteLengthEndomorphism.det R (hM b) (φ b) := by
        simpa [hM', φ'] using
          (Equiv.prod_comp e (fun b => FiniteLengthEndomorphism.det R (hM b) (φ b)))
  · intro M _ _ hM φ
    have : Subsingleton (∀ i : PEmpty, M i) := ⟨fun _ _ => funext fun i => PEmpty.elim i⟩
    simp [FiniteLengthEndomorphism.det, FiniteLengthEndomorphism.smallValues_subsingleton]
  · intro α _ IH (M : Option α → Type w) _ _ hM φ
    let hRest : ∀ i : α, IsFiniteLength R (M (some i)) := fun i => hM (some i)
    let φRest : ∀ i : α, Module.End R (M (some i)) := fun i => φ (some i)
    let hProd : IsFiniteLength R (M none × (∀ i : α, M (some i))) := by
      obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp (hM none)
      obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp (isFiniteLength_pi _ hRest)
      exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
    let E := LinearEquiv.piOptionEquivProd R (M := M)
    have hcomm : E.toLinearMap.comp (piEnd M φ) =
        (LinearMap.prodMap (φ none)
          (piEnd (fun i => M (some i)) φRest)).comp E.toLinearMap := by
      rfl
    have hdet := det_congr_linearEquiv (isFiniteLength_pi M hM) hProd (piEnd M φ) _ E hcomm
    calc
      FiniteLengthEndomorphism.det R (isFiniteLength_pi M hM) (piEnd M φ) =
          FiniteLengthEndomorphism.det R hProd
            (LinearMap.prodMap (φ none) (piEnd (fun i => M (some i)) φRest)) := hdet
      _ = FiniteLengthEndomorphism.det R (hM none) (φ none) *
            FiniteLengthEndomorphism.det R (isFiniteLength_pi _ hRest)
              (piEnd (fun i => M (some i)) φRest) :=
        det_prodMap (hM none) (isFiniteLength_pi _ hRest) hProd
          (φ none) (piEnd (fun i => M (some i)) φRest)
      _ = FiniteLengthEndomorphism.det R (hM none) (φ none) *
            ∏ i, FiniteLengthEndomorphism.det R (hRest i) (φRest i) := by
        rw [IH (fun i => M (some i)) hRest φRest]
      _ = ∏ i : Option α, FiniteLengthEndomorphism.det R (hM i) (φ i) := by
        simp [Fintype.prod_option, φRest]

end Pi

/-- The maximal ideals of `S ⊗_A B` that contain the image of `π`. -/
abbrev tensorSupport (A : Type u) [CommRing A] (S : Type v) [CommRing S] [Algebra A S]
    {B : Type w} [CommRing B] [Algebra A B] (π : B) :=
  {r : MaximalSpectrum (S ⊗[A] B) //
    (Algebra.TensorProduct.includeRight π : S ⊗[A] B) ∈ r.asIdeal}

/-- Let `A → S` be a flat local homomorphism of local rings
with `m = length_S(S / 𝔪_A S)`, let `B` be a local `A`-algebra along a local homomorphism with
`κ(B) / κ(A)` finite, and let `π`, `u ∈ B` with `B / πB` of finite length. Then, writing
`T = S ⊗_A B`,

`(Norm_{κ(B)/κ(A)}(ū) ^ length_B(B / πB)) ^ m
  = ∏_𝔮 Norm_{κ(T_𝔮)/κ(S)}(ū) ^ length_{T_𝔮}(T_𝔮 / πT_𝔮)`,

the product running over the maximal ideals of `T` that contain the image of `π` and the
left-hand side being read in `κ(S)` through `κ(A) → κ(S)`. -/
theorem map_norm_pow_length_eq_prod_norm_pow_length_support
    {A : Type u} {S : Type v} {B : Type w}
    [CommRing A] [CommRing S] [CommRing B]
    [IsLocalRing A] [IsLocalRing S] [IsLocalRing B]
    [Algebra A S] [Algebra A B] [IsLocalHom (algebraMap A S)]
    [IsLocalHom (algebraMap A B)] [Module.Flat A S]
    [Module.Finite (ResidueField A) (ResidueField B)]
    (π u : B) [Fintype (tensorSupport A S π)]
    [hloc : ∀ r : tensorSupport A S π,
      IsLocalHom (algebraMap S (Localization.AtPrime r.1.asIdeal))]
    [hres : ∀ r : tensorSupport A S π,
      Module.Finite (ResidueField S) (ResidueField (Localization.AtPrime r.1.asIdeal))]
    (hM : IsFiniteLength B (B ⧸ Ideal.span {π}))
    {m : ℕ} (hm : Module.length S (S ⧸ extendedMaximalIdeal A S) = m) :
    ResidueField.map (algebraMap A S)
      ((Algebra.norm (ResidueField A) (residue B u) ^
        (Module.length B (B ⧸ Ideal.span {π})).toNat) ^ m) =
      ∏ r : tensorSupport A S π,
        Algebra.norm (ResidueField S)
          (residue (Localization.AtPrime r.1.asIdeal)
            ((algebraMap (S ⊗[A] B) (Localization.AtPrime r.1.asIdeal))
              (Algebra.TensorProduct.includeRight u))) ^
            (Module.length (Localization.AtPrime r.1.asIdeal)
            (Localization.AtPrime r.1.asIdeal ⧸
              Ideal.span {(algebraMap (S ⊗[A] B) (Localization.AtPrime r.1.asIdeal)
                (Algebra.TensorProduct.includeRight π))})).toNat := by
  classical
  have hMA : IsFiniteLength A (B ⧸ Ideal.span {π}) :=
    isFiniteLength_restrictScalars_of_finite_residueField A B (B ⧸ Ideal.span {π}) hM
  obtain ⟨hMS, hbaseEq⟩ := FiniteLengthEndomorphism.map_det_pow_eq_det_baseChange m hm
    hMA ((LinearMap.lsmul B (B ⧸ Ideal.span {π}) u).restrictScalars A)
  have hdetA' : FiniteLengthEndomorphism.det A hMA
      ((LinearMap.lsmul B (B ⧸ Ideal.span {π}) u).restrictScalars A) =
      Algebra.norm (ResidueField A) (residue B u) ^
        (Module.length B (B ⧸ Ideal.span {π})).toNat := by
    simpa [hMA, isFiniteLength_restrictScalars_of_finite_residueField] using
      FiniteLengthEndomorphism.multiplication_det_eq_norm_pow_length A B (B ⧸ Ideal.span {π}) hM u
  have hleft : ResidueField.map (algebraMap A S)
      ((Algebra.norm (ResidueField A) (residue B u) ^
        (Module.length B (B ⧸ Ideal.span {π})).toNat) ^ m) =
      FiniteLengthEndomorphism.det S hMS
        (LinearMap.baseChange S
          ((LinearMap.lsmul B (B ⧸ Ideal.span {π}) u).restrictScalars A)) := by
    rwa [hdetA'] at hbaseEq
  set T := S ⊗[A] B with hT
  let I : Ideal T := Ideal.map (Algebra.TensorProduct.includeRight (A := S)) (Ideal.span {π})
  have hIle (r : MaximalSpectrum T) :
      I ≤ r.asIdeal ↔ (Algebra.TensorProduct.includeRight π : T) ∈ r.asIdeal :=
    ⟨fun h => h (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self π)), fun h =>
      Ideal.map_le_iff_le_comap.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h))⟩
  let Q := T ⧸ I
  let eQ : S ⊗[A] (B ⧸ Ideal.span {π}) ≃ₐ[S] Q :=
    Algebra.TensorProduct.tensorQuotientEquiv (R := A) S B S (Ideal.span {π})
  have hQ : IsFiniteLength S Q := eQ.toLinearEquiv.isFiniteLength hMS
  let : IsArtinian T Q :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (isFiniteLength_of_isScalarTower (R := S) hQ)).2
  let : IsArtinianRing Q := isArtinianRing_iff.mpr (isArtinian_of_tower T inferInstance)
  let : Fintype (MaximalSpectrum Q) := Fintype.ofFinite _
  let q : MaximalSpectrum Q → MaximalSpectrum T := fun p =>
    ⟨p.asIdeal.comap (Ideal.Quotient.mk I),
      Ideal.comap_isMaximal_of_surjective (f := Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective⟩
  let toSupport : MaximalSpectrum Q → tensorSupport A S π := fun p =>
    ⟨q p, (hIle (q p)).mp fun x hx => by
      show Ideal.Quotient.mk I x ∈ p.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact p.asIdeal.zero_mem⟩
  let Rq (p : MaximalSpectrum Q) :=
    Localization.AtPrime (q p).asIdeal ⧸
      I.map (algebraMap T (Localization.AtPrime (q p).asIdeal))
  have hspan (p : MaximalSpectrum Q) :
      I.map (algebraMap T (Localization.AtPrime (q p).asIdeal)) =
        Ideal.span {(algebraMap T (Localization.AtPrime (q p).asIdeal)
          (Algebra.TensorProduct.includeRight π))} := by
    show (Ideal.map (algebraMap T (Localization.AtPrime (q p).asIdeal))
      (Ideal.map (Algebra.TensorProduct.includeRight (A := S)) (Ideal.span {π}))) = _
    rw [Ideal.map_span, Ideal.map_span]
    simp
  let : ∀ p : MaximalSpectrum Q, IsLocalization.AtPrime (Rq p) p.asIdeal := fun p =>
    isLocalization_quotient_atPrime (q p).asIdeal (Localization.AtPrime (q p).asIdeal)
      I p.asIdeal rfl
  let : ∀ p : MaximalSpectrum Q, IsScalarTower S Q (Rq p) := fun p =>
    IsScalarTower.of_algebraMap_eq (R := S) (S := Q) (A := Rq p) (fun s => by
      rw [IsScalarTower.algebraMap_apply S T (Rq p), IsScalarTower.algebraMap_apply T Q (Rq p)]
      rfl)
  have hbij : Function.Bijective (algebraMap Q (∀ p : MaximalSpectrum Q, Rq p)) :=
    MaximalSpectrum.algebraMap_pi_bijective Q Rq
  let eProd : Q ≃ₐ[S] (∀ p : MaximalSpectrum Q, Rq p) :=
    AlgEquiv.ofBijective
      { toRingHom := algebraMap Q (∀ p : MaximalSpectrum Q, Rq p)
        commutes' := fun s => by
          ext p
          show algebraMap Q (Rq p) (algebraMap S Q s) = algebraMap S (Rq p) s
          exact (congrArg (fun f : S →+* Rq p => f s)
            (IsScalarTower.algebraMap_eq S Q (Rq p))).symm } hbij
  have hRqS (p : MaximalSpectrum Q) : IsFiniteLength S (Rq p) := by
    have hpi : IsFiniteLength S (∀ p : MaximalSpectrum Q, Rq p) :=
      eProd.toLinearEquiv.isFiniteLength hQ
    exact IsFiniteLength.of_surjective
      (f := (LinearMap.proj p : (∀ p : MaximalSpectrum Q, Rq p) →ₗ[S] Rq p)) hpi
      fun y => ⟨Pi.single p y, by simp⟩
  have hRqLocal (p : MaximalSpectrum Q) :
      IsFiniteLength (Localization.AtPrime (q p).asIdeal) (Rq p) := by
    exact isFiniteLength_of_isScalarTower (R := S) (hRqS p)
  let φq (p : MaximalSpectrum Q) : Module.End S (Rq p) :=
    (LinearMap.lsmul (Localization.AtPrime (q p).asIdeal) (Rq p)
      (algebraMap T (Localization.AtPrime (q p).asIdeal)
        (Algebra.TensorProduct.includeRight u))).restrictScalars S
  let F (r : tensorSupport A S π) :=
    Algebra.norm (ResidueField S)
      (residue (Localization.AtPrime r.1.asIdeal)
        (algebraMap T (Localization.AtPrime r.1.asIdeal)
          (Algebra.TensorProduct.includeRight u))) ^
      (Module.length (Localization.AtPrime r.1.asIdeal)
        (Localization.AtPrime r.1.asIdeal ⧸
          Ideal.span {(algebraMap T (Localization.AtPrime r.1.asIdeal)
            (Algebra.TensorProduct.includeRight π))})).toNat
  have hlocaldet (p : MaximalSpectrum Q) :
      FiniteLengthEndomorphism.det S (hRqS p) (φq p) = F (toSupport p) := by
    let := hloc (toSupport p)
    let := hres (toSupport p)
    have h := FiniteLengthEndomorphism.multiplication_det_eq_norm_pow_length
      S (Localization.AtPrime (q p).asIdeal) (Rq p) (hRqLocal p)
      (algebraMap T (Localization.AtPrime (q p).asIdeal)
        (Algebra.TensorProduct.includeRight u))
    let e : (Localization.AtPrime (q p).asIdeal ⧸
          I.map (algebraMap T (Localization.AtPrime (q p).asIdeal)))
        ≃ₐ[Localization.AtPrime (q p).asIdeal]
        (Localization.AtPrime (q p).asIdeal ⧸
          Ideal.span {(algebraMap T (Localization.AtPrime (q p).asIdeal)
            (Algebra.TensorProduct.includeRight π))}) :=
      Ideal.quotientEquivAlgOfEq (Localization.AtPrime (q p).asIdeal) (hspan p)
    have hlen : Module.length (Localization.AtPrime (q p).asIdeal) (Rq p) =
        Module.length (Localization.AtPrime (q p).asIdeal)
          (Localization.AtPrime (q p).asIdeal ⧸
            Ideal.span {(algebraMap T (Localization.AtPrime (q p).asIdeal)
              (Algebra.TensorProduct.includeRight π))}) := by
      simpa [Rq] using e.toLinearEquiv.length_eq
    rw [hlen] at h
    simpa [φq, F, toSupport] using h
  let z : Q := Ideal.Quotient.mk I (Algebra.TensorProduct.includeRight u)
  let ψQ : Module.End S Q := (LinearMap.lsmul Q Q z).restrictScalars S
  have hcompat : eProd.toLinearEquiv.toLinearMap.comp ψQ =
      (piEnd Rq φq).comp eProd.toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    intro x
    funext p
    show algebraMap Q (Rq p) (z * x) =
      algebraMap (Localization.AtPrime (q p).asIdeal) (Rq p)
        (algebraMap T (Localization.AtPrime (q p).asIdeal)
          (Algebra.TensorProduct.includeRight u)) * algebraMap Q (Rq p) x
    rw [map_mul]
    simp [z, Rq, Q, T, Ideal.Quotient.algebraMap_eq]
  have hsplit : FiniteLengthEndomorphism.det S hQ ψQ =
      ∏ p : MaximalSpectrum Q, FiniteLengthEndomorphism.det S (hRqS p) (φq p) := by
    rw [det_congr_linearEquiv hQ (isFiniteLength_pi Rq hRqS) ψQ (piEnd Rq φq)
      eProd.toLinearEquiv hcompat]
    exact det_piEnd Rq hRqS φq
  have hQcompat : eQ.toLinearMap.comp
      (LinearMap.baseChange S
        ((LinearMap.lsmul B (B ⧸ Ideal.span {π}) u).restrictScalars A)) =
      ψQ.comp eQ.toLinearMap := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [LinearMap.map_add, hx, hy]
    | tmul s n =>
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective n
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul]
      show eQ (s ⊗ₜ[A] (Ideal.Quotient.mk (Ideal.span {π}) u *
          Ideal.Quotient.mk (Ideal.span {π}) b)) =
        z * eQ (s ⊗ₜ[A] Ideal.Quotient.mk (Ideal.span {π}) b)
      have hfactor : s ⊗ₜ[A]
          (Ideal.Quotient.mk (Ideal.span {π}) u * Ideal.Quotient.mk (Ideal.span {π}) b) =
          (1 ⊗ₜ[A] Ideal.Quotient.mk (Ideal.span {π}) u) *
            (s ⊗ₜ[A] Ideal.Quotient.mk (Ideal.span {π}) b) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      have hz : eQ (1 ⊗ₜ[A] Ideal.Quotient.mk (Ideal.span {π}) u) = z := by
        show Algebra.TensorProduct.tensorQuotientEquiv S B S (Ideal.span {π})
            (1 ⊗ₜ[A] Ideal.Quotient.mk (Ideal.span {π}) u) =
          Ideal.Quotient.mk (Ideal.map (Algebra.TensorProduct.includeRight (A := S))
            (Ideal.span {π})) (Algebra.TensorProduct.includeRight u)
        rw [Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
        rfl
      rw [hfactor, map_mul, hz]
  have hwholeDet : FiniteLengthEndomorphism.det S hMS
      (LinearMap.baseChange S
        ((LinearMap.lsmul B (B ⧸ Ideal.span {π}) u).restrictScalars A)) =
      FiniteLengthEndomorphism.det S hQ ψQ :=
    det_congr_linearEquiv hMS hQ _ _ eQ.toLinearEquiv hQcompat
  have hmapq (p : MaximalSpectrum Q) :
      Ideal.map (Ideal.Quotient.mk I) (q p).asIdeal = p.asIdeal :=
    Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective p.asIdeal
  have htoSupport : Function.Bijective toSupport := by
    constructor
    · intro p p' h
      apply MaximalSpectrum.ext
      have hqq : (q p).asIdeal = (q p').asIdeal :=
        congrArg (fun x : tensorSupport A S π => x.1.asIdeal) h
      rw [← hmapq p, ← hmapq p', hqq]
    · intro r
      have hr : I ≤ r.1.asIdeal := (hIle r.1).mpr r.2
      let JQ := Ideal.map (Ideal.Quotient.mk I) r.1.asIdeal
      have hJQ : JQ.IsMaximal :=
        Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by
          rwa [Ideal.mk_ker])
      refine ⟨⟨JQ, hJQ⟩, Subtype.ext (MaximalSpectrum.ext ?_)⟩
      show JQ.comap (Ideal.Quotient.mk I) = r.1.asIdeal
      dsimp only [JQ]
      rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left]
  calc
    _ = FiniteLengthEndomorphism.det S hMS
        (LinearMap.baseChange S
          ((LinearMap.lsmul B (B ⧸ Ideal.span {π}) u).restrictScalars A)) := hleft
    _ = FiniteLengthEndomorphism.det S hQ ψQ := hwholeDet
    _ = ∏ p : MaximalSpectrum Q, FiniteLengthEndomorphism.det S (hRqS p) (φq p) := hsplit
    _ = ∏ p : MaximalSpectrum Q, F (toSupport p) := Finset.prod_congr rfl fun p _ ↦ hlocaldet p
    _ = ∏ r : tensorSupport A S π, F r :=
      Equiv.prod_comp (Equiv.ofBijective toSupport htoSupport) F

/-- Let `A → S` be a flat local homomorphism of local rings with `m = length_S(S / 𝔪_A S)`, let
`B` be a local `A`-algebra along a local homomorphism with `κ(B) / κ(A)` finite, and let
`π`, `u ∈ B` with `B / πB` of finite length. Then, writing `T = S ⊗_A B`,

`(Norm_{κ(B)/κ(A)}(ū) ^ length_B(B / πB)) ^ m
  = ∏_𝔮 Norm_{κ(T_𝔮)/κ(S)}(ū) ^ length_{T_𝔮}(T_𝔮 / πT_𝔮)`,

the product running over the maximal ideals of `T` and the left-hand side being read in `κ(S)`
through `κ(A) → κ(S)`. -/
@[stacks 0GU1]
theorem map_norm_pow_length_eq_prod_norm_pow_length
    {A : Type u} {S : Type v} {B : Type w}
    [CommRing A] [CommRing S] [CommRing B]
    [IsLocalRing A] [IsLocalRing S] [IsLocalRing B]
    [Algebra A S] [Algebra A B] [IsLocalHom (algebraMap A S)]
    [IsLocalHom (algebraMap A B)] [Module.Flat A S]
    [Fintype (MaximalSpectrum (S ⊗[A] B))]
    [Module.Finite (ResidueField A) (ResidueField B)]
    [∀ q : MaximalSpectrum (S ⊗[A] B),
      IsLocalHom (algebraMap S (Localization.AtPrime q.asIdeal))]
    [∀ q : MaximalSpectrum (S ⊗[A] B),
      Module.Finite (ResidueField S) (ResidueField (Localization.AtPrime q.asIdeal))]
    (π u : B) (hM : IsFiniteLength B (B ⧸ Ideal.span {π}))
    {m : ℕ} (hm : Module.length S (S ⧸ extendedMaximalIdeal A S) = m) :
    ResidueField.map (algebraMap A S)
      ((Algebra.norm (ResidueField A) (residue B u) ^
        (Module.length B (B ⧸ Ideal.span {π})).toNat) ^ m) =
      ∏ q : MaximalSpectrum (S ⊗[A] B),
        Algebra.norm (ResidueField S)
          (residue (Localization.AtPrime q.asIdeal)
            ((algebraMap (S ⊗[A] B) (Localization.AtPrime q.asIdeal))
              (Algebra.TensorProduct.includeRight u))) ^
            (Module.length (Localization.AtPrime q.asIdeal)
            (Localization.AtPrime q.asIdeal ⧸
              Ideal.span {(algebraMap (S ⊗[A] B) (Localization.AtPrime q.asIdeal)
                (Algebra.TensorProduct.includeRight π))})).toNat := by
  classical
  let F (r : MaximalSpectrum (S ⊗[A] B)) :=
    Algebra.norm (ResidueField S)
      (residue (Localization.AtPrime r.asIdeal)
        (algebraMap (S ⊗[A] B) (Localization.AtPrime r.asIdeal)
          (Algebra.TensorProduct.includeRight u))) ^
      (Module.length (Localization.AtPrime r.asIdeal)
        (Localization.AtPrime r.asIdeal ⧸
          Ideal.span {(algebraMap (S ⊗[A] B) (Localization.AtPrime r.asIdeal)
            (Algebra.TensorProduct.includeRight π))})).toNat
  have houtside (r : MaximalSpectrum (S ⊗[A] B))
      (hr : (Algebra.TensorProduct.includeRight π : S ⊗[A] B) ∉ r.asIdeal) : F r = 1 := by
    have huπ : IsUnit (algebraMap (S ⊗[A] B) (Localization.AtPrime r.asIdeal)
        (Algebra.TensorProduct.includeRight π)) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime r.asIdeal)
        r.asIdeal (Algebra.TensorProduct.includeRight π)).2 hr
    have hsub : Subsingleton (Localization.AtPrime r.asIdeal ⧸
        Ideal.span {(algebraMap (S ⊗[A] B) (Localization.AtPrime r.asIdeal)
          (Algebra.TensorProduct.includeRight π))}) :=
      Ideal.Quotient.subsingleton_iff.mpr (Ideal.span_singleton_eq_top.mpr huπ)
    have hlen : Module.length (Localization.AtPrime r.asIdeal)
        (Localization.AtPrime r.asIdeal ⧸
          Ideal.span {(algebraMap (S ⊗[A] B) (Localization.AtPrime r.asIdeal)
            (Algebra.TensorProduct.includeRight π))}) = 0 :=
      Module.length_eq_zero_iff.mpr hsub
    simp only [F, hlen]
    simp
  have hprodAll : (∏ r : MaximalSpectrum (S ⊗[A] B), F r) = ∏ r : tensorSupport A S π, F r.1 := by
    have hs := Fintype.prod_subtype_mul_prod_subtype
      (fun r : MaximalSpectrum (S ⊗[A] B) =>
        (Algebra.TensorProduct.includeRight π : S ⊗[A] B) ∈ r.asIdeal) F
    rw [show (∏ r : {r : MaximalSpectrum (S ⊗[A] B) //
        ¬ (Algebra.TensorProduct.includeRight π : S ⊗[A] B) ∈ r.asIdeal}, F r.1) = 1 from
      Finset.prod_eq_one fun r _ => houtside r.1 r.2, mul_one] at hs
    exact hs.symm
  exact (map_norm_pow_length_eq_prod_norm_pow_length_support π u hM hm).trans hprodAll.symm

end Stacks.Length

end

