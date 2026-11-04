module

public import StacksFrontier.RingTheory.Smoothing.TwistedQuotientLocalResolution

/-!
# The twisted smooth factorization of items (24)–(26) of Stacks 07FJ

Items (24), (25) and (26) of the proof of Stacks 07FJ — tags 07G8, 07G9 and 07GA — produce the
smooth factorization that items (22) and (23) consume. In the source the chain in question is

`Λ₀[t_1, …, t_d] → C ⊗_{k[x_1, …, x_d]} Λ₀[t_1, …, t_d] → Λ_𝔮/𝔮ⁿΛ_𝔮`

with `Λ₀ = k[y_1, …, y_m]_𝔭/𝔭ⁿ`; item (24) replaces `C` by `B = A[x_i, z_{ij}]/(x_i^{2N} - Σ_j
z_{ij}a_j)` through the retraction `grt : C → B` of Stacks 07CE, item (26) writes down the
twisted map `B → D'[t_1, …, t_d]`, `x_i ↦ π_i t_i`, `z_{ij} ↦ λ_{ij}t_i^{2N}/δ_i^{2N}`, and item
(25) factors it through a smooth `Λ₀[t_1, …, t_d]`-algebra using that `D'[t_1, …, t_d]` is a
filtered colimit of such.

The three items are already available as the general lemmas
`Stacks.Smoothing.hasSmoothFactorization_of_algHom` (07G8),
`Stacks.Smoothing.canBeResolved_of_factorization_mvPolynomial` (07G9) and
`Stacks.Smoothing.exists_algHom_parameterPowerAlgebra_mvPolynomial` (07GA) of
`StacksFrontier.RingTheory.Smoothing.ArtinianFactorizationDescent`. What this file does is assemble
them into the one datum that
`Stacks.Smoothing.hasSmoothFactorization_tensor_of_exists` asks for: a smooth
`Λ₀[t_1, …, t_d]`-algebra `T`, a ring map `C → T` over `k[x_1, …, x_d]` and a ring map
`T → Λ_𝔮/𝔮ⁿΛ_𝔮` over `Λ₀[t_1, …, t_d]`, compatible with the given map `C → Λ_𝔮/𝔮ⁿΛ_𝔮`.

## Main definitions

None.

## Main results

* `Stacks.Smoothing.exists_smoothFactorizationData`: the factorization step of item (25) in the
  shape of that datum — a map from a finitely presented `k[x]`-algebra into an algebra ind-smooth
  over the auxiliary base, together with an evaluation of the latter in the target, factors
  through a smooth algebra over the auxiliary base.
* `Stacks.Smoothing.exists_smoothFactorizationData_of_algHom`: **item (24)** (tag 07G8) in the
  same shape — the datum for `B` transports to `C` along a `k[x]`-algebra map `C → B`
  compatible with the two evaluations in the target. This is
  `Stacks.Smoothing.hasSmoothFactorization_of_algHom` for the datum rather than for
  `Stacks.Smoothing.HasSmoothFactorization`.
* `Stacks.Smoothing.exists_smoothFactorizationData_twisted`: **items (25) and (26)** (tags 07G9
  and 07GA) at `B`: the twisted map `B → D'[t_1, …, t_d]` of item (26), factored through a smooth
  `Λ₀[t_1, …, t_d]`-algebra by item (25).
* `Stacks.Smoothing.exists_smoothFactorizationData_improved`: **items (24), (25) and (26)**
  together, at `C`. This is what
  `StacksFrontier.RingTheory.Smoothing.TwistedQuotientClosure` consumes to discharge
  `Stacks.Smoothing.TwistedQuotientSmoothFactorization`, and hence
  `Stacks.Smoothing.TwistedQuotientLocallyResolvable`, outright.
* `Stacks.Smoothing.parameterPowerAlgebra_ringHom_ext`: two ring maps out of
  `B = A[x_i, z_{ij}]/(x_i^{2N} - Σ_j z_{ij}a_j)` agreeing on the image of `A`, on the `x_i` and
  on the `z_{ij}` are equal.

## Implementation notes

Every statement here keeps the rings opaque and takes the structure maps as hypotheses. The
reason is elaboration cost, not style: in the application the rings are localizations of
quotients of a tensor product, and a statement which writes them out blows the instance-search
budget. Correspondingly all the maps are *plain ring homomorphisms* carrying their compatibility
as a hypothesis, which is also the shape
`Stacks.Smoothing.hasSmoothFactorization_tensor_of_exists` wants; the only algebra instances in
the statements are the ones the ind-smoothness input of item (25) genuinely needs.

The hypotheses of `exists_smoothFactorizationData_twisted` are the data of items (24)–(26) read
in `L₀ = Λ_𝔮/𝔮ⁿΛ_𝔮` and in `D'`, as follows.

* `M`, `hD`: essential smoothness of `Λ₀ → D'`, in the form item (25) uses it — `D'` is a
  localization of a `Λ₀`-algebra `B₀` of finite presentation and is formally smooth over `Λ₀`.
* `φ`, `π`, `δ`, `lam`, `hδ`, `hrel`: the input of item (26) — the map `A → D'` of (07FT), the
  images in `D'` of the parameters `π_i`, the units `δ_i` and the coefficients `λ_{ij}` of
  (07FU) and (07FX), and the relation `(δ_iπ_i)^{2N} = Σ_j φ(a_j)λ_{ij}` which is clause (a) of
  (07FX) read in `D'`.
* `cD`, `τ`: the evaluation `D'[t_1, …, t_d] → L₀` of items (25) and (26), given by a ring map
  `cD : D' → L₀` and the images `τ_i ∈ L₀` of the variables; `hcD` and `hτ` say that it is a map
  over `Λ₀[t_1, …, t_d]`.
* `hsqC`, `hsqX`: the square of items (25) and (26) commutes — the composite
  `k[x_1, …, x_d] → Λ₀[t_1, …, t_d] → D'[t_1, …, t_d]` is the twisted structure map
  `x_i ↦ π_i t_i` of item (26). This is where `γ_i = π_i t_i` enters.
* `fB`, `hfBA`, `hfBX`, `hfBZ`: the evaluation `B → L₀` of the source, pinned down on the
  generators of `B`. `hfBZ` is stated multiplied through by `δ_i^{2N}`, so that no inverse of
  `δ_i` appears; since `δ_i` is a unit of `D'` this is equivalent to the unmultiplied form.

All of these are supplied by the front end of 07FJ: `D'` is the Artinian local ring of item (19)
(tag 07FX), `φ` is the map whose existence is the condition `E ⊆ D` of item (9) (tag 07FT),
`cD` is the map `D' → Λ_𝔮/𝔮ⁿΛ_𝔮` called `b'` in
`Stacks.Smoothing.TwistedQuotientLocallyResolvable`, `τ_i` is the image of `t_i`, and `fB` is the
composite of `Stacks.Smoothing.parameterPowerAlgebraToTarget` with `Λ → Λ/IΛ → L₀`. Exactly that
translation is carried out in `StacksFrontier.RingTheory.Smoothing.TwistedQuotientClosure`.

The file stops at `exists_smoothFactorizationData_improved` and does not restate it further:
pushing the datum through `Stacks.Smoothing.hasSmoothFactorization_tensor_of_exists` to
`HasSmoothFactorization (Λ₀[t_1, …, t_d]) (Λ₀[t_1, …, t_d] ⊗_{k[x]} C) (Λ_𝔮/𝔮ⁿΛ_𝔮)`, which is
the same datum read through the equivalence of
`Stacks.Smoothing.hasSmoothFactorization_tensor_of_exists` and
`Stacks.Smoothing.exists_of_hasSmoothFactorization_tensor`; and composing that with items
(22) and (23) at a local smoothing situation is done by
`Stacks.Smoothing.isResolvableAfterLocalizing_twistedQuotient`, which *constructs* the two structure maps of the auxiliary base instead of assuming them, and is
therefore the one that applies to the twisted quotient chain.

## References

* [Stacks Project, Tag 07FJ](https://stacks.math.columbia.edu/tag/07FJ)
* [Stacks Project, Tag 07G8](https://stacks.math.columbia.edu/tag/07G8)
* [Stacks Project, Tag 07G9](https://stacks.math.columbia.edu/tag/07G9)
* [Stacks Project, Tag 07GA](https://stacks.math.columbia.edu/tag/07GA)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.Smoothing

universe u

/-! ### Maps out of the parameter power algebra -/

/-- Two ring maps out of `B = A[x_i, z_{ij}]/(x_i^{2N} - Σ_j z_{ij}a_j)` which agree on the image
of `A`, on the generators `x_i` and on the generators `z_{ij}` are equal. -/
theorem parameterPowerAlgebra_ringHom_ext {A Y : Type u} [CommRing A] [CommRing Y] {d t N : ℕ}
    {a : Fin t → A} {f g : parameterPowerAlgebra A d N a →+* Y}
    (hA : ∀ x : A, f (algebraMap A (parameterPowerAlgebra A d N a) x) =
      g (algebraMap A (parameterPowerAlgebra A d N a) x))
    (hX : ∀ i : Fin d,
      f (Ideal.Quotient.mk (parameterPowerIdeal d N a) (MvPolynomial.X (Sum.inl i))) =
        g (Ideal.Quotient.mk (parameterPowerIdeal d N a) (MvPolynomial.X (Sum.inl i))))
    (hZ : ∀ (i : Fin d) (j : Fin t),
      f (Ideal.Quotient.mk (parameterPowerIdeal d N a) (MvPolynomial.X (Sum.inr (i, j)))) =
        g (Ideal.Quotient.mk (parameterPowerIdeal d N a) (MvPolynomial.X (Sum.inr (i, j))))) :
    f = g := by
  have hC : ∀ x : A, algebraMap A (parameterPowerAlgebra A d N a) x =
      Ideal.Quotient.mk (parameterPowerIdeal d N a) (MvPolynomial.C x) := fun x => by
    rw [IsScalarTower.algebraMap_apply A (MvPolynomial (Fin d ⊕ Fin d × Fin t) A)
      (parameterPowerAlgebra A d N a), MvPolynomial.algebraMap_eq]
    rfl
  have key : f.comp (Ideal.Quotient.mk (parameterPowerIdeal d N a)) =
      g.comp (Ideal.Quotient.mk (parameterPowerIdeal d N a)) := by
    refine MvPolynomial.ringHom_ext (fun x => ?_) fun s => ?_
    · simpa [← hC x] using hA x
    · obtain i | ⟨i, j⟩ := s
      · exact hX i
      · exact hZ i j
  refine RingHom.ext fun z => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact RingHom.congr_fun key y

/-! ### Factoring through a smooth algebra over the auxiliary base -/

/-- **The factorization step of item (25).** Let `kx → R₀` be the auxiliary base of items
(22)–(26), let `Aop` be a `kx`-algebra of finite presentation, and let `E` be an `R₀`-algebra
which is a filtered colimit of smooth `R₀`-algebras. A ring map `Aop → E` over `kx` together with
a ring map `E → L₀` over `R₀` then factors the composite `Aop → L₀` through an `R₀`-algebra
smooth over `R₀`, in the shape asked for by
`Stacks.Smoothing.hasSmoothFactorization_tensor_of_exists`.

The factorization is obtained by base changing `Aop` to `R₀ ⊗_{kx} Aop`, which is of finite
presentation over `R₀`, and applying the characterization
`Stacks.Smoothing.indSmooth_iff_exists_factorization` of ind-smoothness there. -/
theorem exists_smoothFactorizationData {kx Aop R₀ E L₀ : Type u} [CommRing kx] [CommRing Aop]
    [CommRing R₀] [CommRing E] [CommRing L₀] [Algebra kx Aop] [Algebra kx R₀] [Algebra R₀ L₀]
    [Algebra R₀ E] [Algebra.FinitePresentation kx Aop] (hE : IndSmooth R₀ E) (gE : Aop →+* E)
    (kE : E →+* L₀) (cL : Aop →+* L₀)
    (hgE : ∀ y : kx, gE (algebraMap kx Aop y) = algebraMap R₀ E (algebraMap kx R₀ y))
    (hkE : ∀ x : R₀, kE (algebraMap R₀ E x) = algebraMap R₀ L₀ x)
    (hcomp : ∀ x : Aop, kE (gE x) = cL x) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R₀ T), Algebra.Smooth R₀ T ∧
      ∃ (g : Aop →+* T) (kk : T →+* L₀),
        (∀ y : kx, g (algebraMap kx Aop y) = algebraMap R₀ T (algebraMap kx R₀ y)) ∧
        (∀ x : R₀, kk (algebraMap R₀ T x) = algebraMap R₀ L₀ x) ∧
        ∀ x : Aop, kk (g x) = cL x := by
  let instkxE : Algebra kx E := ((algebraMap R₀ E).comp (algebraMap kx R₀)).toAlgebra
  have instTkxR₀E : IsScalarTower kx R₀ E := IsScalarTower.of_algebraMap_eq' rfl
  let gEalg : Aop →ₐ[kx] E := { toRingHom := gE, commutes' := hgE }
  let G : R₀ ⊗[kx] Aop →ₐ[kx] E :=
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom kx R₀ E) gEalg fun _ _ => Commute.all _ _
  have hGleft : ∀ x : R₀, G (algebraMap R₀ (R₀ ⊗[kx] Aop) x) = algebraMap R₀ E x := fun x =>
    (Algebra.TensorProduct.lift_tmul _ _ _ x 1).trans (by simp [gEalg])
  have hGright : ∀ x : Aop, G (Algebra.TensorProduct.includeRight x) = gE x := fun x =>
    (Algebra.TensorProduct.lift_tmul _ _ _ 1 x).trans (by simp [gEalg])
  let G' : R₀ ⊗[kx] Aop →ₐ[R₀] E := { toRingHom := G.toRingHom, commutes' := hGleft }
  obtain ⟨T, instT, algT, hT, g', k', hg'k'⟩ :=
    (indSmooth_iff_exists_factorization R₀ E).mp hE (R₀ ⊗[kx] Aop) inferInstance inferInstance
      inferInstance G'
  refine ⟨T, instT, algT, hT,
    g'.toRingHom.comp (Algebra.TensorProduct.includeRight (R := kx) (A := R₀) (B := Aop)),
    kE.comp k'.toRingHom, fun y => ?_, fun x => ?_, fun x => ?_⟩
  · show g' (Algebra.TensorProduct.includeRight (algebraMap kx Aop y)) = _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply kx R₀ (R₀ ⊗[kx] Aop), g'.commutes]
  · show kE (k' (algebraMap R₀ T x)) = _
    rw [k'.commutes, hkE]
  · show kE (k' (g' (Algebra.TensorProduct.includeRight x))) = _
    rw [show k' (g' (Algebra.TensorProduct.includeRight x)) =
      G' (Algebra.TensorProduct.includeRight x) from
      AlgHom.congr_fun hg'k' (Algebra.TensorProduct.includeRight x),
      show G' (Algebra.TensorProduct.includeRight x) = gE x from hGright x, hcomp x]

/-- **Stacks 07FJ, item (24)** (tag 07G8), in the shape of the datum asked for by
`Stacks.Smoothing.hasSmoothFactorization_tensor_of_exists`. A `kx`-algebra map `σ : Cop → Aop`
whose composite with the evaluation `Aop → L₀` is the evaluation `Cop → L₀` carries a smooth
factorization datum for `Aop` to one for `Cop`.

In the source `σ` is the retraction `grt : C → B` of Stacks 07CE, so that it suffices to resolve
the chain with `B` in place of `C`; this is
`Stacks.Smoothing.hasSmoothFactorization_of_algHom` with
`Stacks.Smoothing.HasSmoothFactorization` replaced by the datum. -/
theorem exists_smoothFactorizationData_of_algHom {kx Aop Cop R₀ L₀ : Type u} [CommRing kx]
    [CommRing Aop] [CommRing Cop] [CommRing R₀] [CommRing L₀] [Algebra kx Aop] [Algebra kx Cop]
    [Algebra kx R₀] [Algebra R₀ L₀] (σ : Cop →ₐ[kx] Aop) (fB : Aop →+* L₀) (cL : Cop →+* L₀)
    (hcL : ∀ c : Cop, cL c = fB (σ c))
    (h : ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R₀ T), Algebra.Smooth R₀ T ∧
      ∃ (g : Aop →+* T) (kk : T →+* L₀),
        (∀ y : kx, g (algebraMap kx Aop y) = algebraMap R₀ T (algebraMap kx R₀ y)) ∧
        (∀ x : R₀, kk (algebraMap R₀ T x) = algebraMap R₀ L₀ x) ∧
        ∀ x : Aop, kk (g x) = fB x) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R₀ T), Algebra.Smooth R₀ T ∧
      ∃ (g : Cop →+* T) (kk : T →+* L₀),
        (∀ y : kx, g (algebraMap kx Cop y) = algebraMap R₀ T (algebraMap kx R₀ y)) ∧
        (∀ x : R₀, kk (algebraMap R₀ T x) = algebraMap R₀ L₀ x) ∧
        ∀ c : Cop, kk (g c) = cL c := by
  obtain ⟨T, instT, algT, hT, g, kk, hgkx, hkkR₀, hcomp⟩ := h
  refine ⟨T, instT, algT, hT, g.comp σ.toRingHom, kk, fun y => ?_, hkkR₀, fun c => ?_⟩
  · show g (σ (algebraMap kx Cop y)) = _
    rw [σ.commutes y, hgkx y]
  · show kk (g (σ c)) = _
    rw [hcL c, hcomp (σ c)]

/-! ### The twisted factorization over `Λ₀[t_1, …, t_d]` -/

/-- **Stacks 07FJ, items (25) and (26)** (tags 07G9 and 07GA), at
`B = A[x_i, z_{ij}]/(x_i^{2N} - Σ_j z_{ij}a_j)`.

The twisted map `B → D'[t_1, …, t_d]` of item (26) sends `x_i` to `π_i t_i` and `z_{ij}` to
`λ_{ij}t_i^{2N}/δ_i^{2N}`, and is a `k[x_1, …, x_d]`-algebra map for the structure
`x_i ↦ π_i t_i` on `D'[t_1, …, t_d]`; `hsqC` and `hsqX` say that this structure is the composite
`k[x_1, …, x_d] → Λ₀[t_1, …, t_d] → D'[t_1, …, t_d]`, which is the commutation of the square in
the source. Item (25) then factors the map through a smooth `Λ₀[t_1, …, t_d]`-algebra, because
`D'[t_1, …, t_d]` is a filtered colimit of such and `B` is of finite presentation over
`k[x_1, …, x_d]`.

The evaluation `D'[t_1, …, t_d] → L₀` is `MvPolynomial.eval₂Hom cD τ`; `hcD` and `hτ` say it is a
map over `Λ₀[t_1, …, t_d]`, and `hfBA`, `hfBX`, `hfBZ` say that it carries the twisted map to the
given evaluation `fB : B → L₀`. `hfBZ` is multiplied through by `δ_i^{2N}` so that no inverse
appears; it is equivalent to the unmultiplied form because `δ_i` is a unit. -/
theorem exists_smoothFactorizationData_twisted (k : Type u) {A Λ₀ D' L₀ : Type u} {d t N : ℕ}
    [CommRing k] [IsNoetherianRing k] [CommRing A] [CommRing Λ₀] [CommRing D'] [CommRing L₀]
    [Algebra k A] [Algebra.FiniteType k A] [Algebra k D'] [Algebra Λ₀ D']
    [Algebra (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) Λ₀)]
    [Algebra (MvPolynomial (Fin d) Λ₀) L₀] (a : Fin t → A) {B₀ : Type u}
    [CommRing B₀] [Algebra Λ₀ B₀] [Algebra B₀ D'] [IsScalarTower Λ₀ B₀ D']
    [Algebra.FinitePresentation Λ₀ B₀] (M : Submonoid B₀) [IsLocalization M D']
    (hD : Algebra.FormallySmooth Λ₀ D') (φ : A →ₐ[k] D') (π δ : Fin d → D')
    (lam : Fin d → Fin t → D') (hδ : ∀ i, IsUnit (δ i))
    (hrel : ∀ i, (δ i * π i) ^ (2 * N) = ∑ j, φ (a j) * lam i j) (cD : D' →+* L₀)
    (τ : Fin d → L₀)
    (hcD : ∀ y : Λ₀, cD (algebraMap Λ₀ D' y) =
      algebraMap (MvPolynomial (Fin d) Λ₀) L₀ (MvPolynomial.C y))
    (hτ : ∀ i, τ i = algebraMap (MvPolynomial (Fin d) Λ₀) L₀ (MvPolynomial.X i))
    (hsqC : ∀ r : k, MvPolynomial.map (algebraMap Λ₀ D')
        (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) Λ₀) (MvPolynomial.C r)) =
      MvPolynomial.C (algebraMap k D' r))
    (hsqX : ∀ i, MvPolynomial.map (algebraMap Λ₀ D')
        (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) Λ₀) (MvPolynomial.X i)) =
      MvPolynomial.C (π i) * MvPolynomial.X i)
    (fB : parameterPowerAlgebra A d N a →+* L₀)
    (hfBA : ∀ x : A, fB (algebraMap A (parameterPowerAlgebra A d N a) x) = cD (φ x))
    (hfBX : ∀ i, fB (Ideal.Quotient.mk (parameterPowerIdeal d N a)
      (MvPolynomial.X (Sum.inl i))) = cD (π i) * τ i)
    (hfBZ : ∀ i j, fB (Ideal.Quotient.mk (parameterPowerIdeal d N a)
        (MvPolynomial.X (Sum.inr (i, j)))) * cD (δ i) ^ (2 * N) =
      cD (lam i j) * τ i ^ (2 * N)) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra (MvPolynomial (Fin d) Λ₀) T),
      Algebra.Smooth (MvPolynomial (Fin d) Λ₀) T ∧
      ∃ (g : parameterPowerAlgebra A d N a →+* T) (kk : T →+* L₀),
        (∀ y : MvPolynomial (Fin d) k,
          g (algebraMap (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a) y) =
            algebraMap (MvPolynomial (Fin d) Λ₀) T
              (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) Λ₀) y)) ∧
        (∀ x : MvPolynomial (Fin d) Λ₀, kk (algebraMap (MvPolynomial (Fin d) Λ₀) T x) =
          algebraMap (MvPolynomial (Fin d) Λ₀) L₀ x) ∧
        ∀ x : parameterPowerAlgebra A d N a, kk (g x) = fB x := by
  let instRE : Algebra (MvPolynomial (Fin d) Λ₀) (MvPolynomial (Fin d) D') :=
    MvPolynomial.algebraMvPolynomial
  let instTw : Algebra (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) D') :=
    (MvPolynomial.aeval (R := k)
      fun i => MvPolynomial.C (π i) * MvPolynomial.X i).toRingHom.toAlgebra
  obtain ⟨ψ, hψA, hψX, hψZ⟩ :=
    exists_algHom_parameterPowerAlgebra_mvPolynomial k a φ π δ lam hδ hrel
  have hRE : ∀ x : MvPolynomial (Fin d) Λ₀,
      algebraMap (MvPolynomial (Fin d) Λ₀) (MvPolynomial (Fin d) D') x =
        MvPolynomial.map (algebraMap Λ₀ D') x := fun _ => rfl
  -- the square commutes
  have hgE : ∀ y : MvPolynomial (Fin d) k,
      ψ (algebraMap (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a) y) =
        algebraMap (MvPolynomial (Fin d) Λ₀) (MvPolynomial (Fin d) D')
          (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) Λ₀) y) := by
    have key : (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) D') : _ →+* _) =
        (MvPolynomial.map (algebraMap Λ₀ D')).comp
          (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) Λ₀)) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) fun i => ?_
      · show MvPolynomial.aeval (R := k)
          (fun i => MvPolynomial.C (π i) * MvPolynomial.X i) (MvPolynomial.C r) = _
        rw [MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply k D' (MvPolynomial (Fin d) D'),
          MvPolynomial.algebraMap_eq]
        exact (hsqC r).symm
      · show MvPolynomial.aeval (R := k)
          (fun i => MvPolynomial.C (π i) * MvPolynomial.X i) (MvPolynomial.X i) = _
        rw [MvPolynomial.aeval_X]
        exact (hsqX i).symm
    intro y
    rw [ψ.commutes y, hRE, ← RingHom.comp_apply, ← key]
  -- the evaluation of `D'[t]` in `L₀` is a map over `Λ₀[t]`
  have hkE : ∀ x : MvPolynomial (Fin d) Λ₀,
      MvPolynomial.eval₂Hom cD τ
          (algebraMap (MvPolynomial (Fin d) Λ₀) (MvPolynomial (Fin d) D') x) =
        algebraMap (MvPolynomial (Fin d) Λ₀) L₀ x := by
    have key : (MvPolynomial.eval₂Hom cD τ).comp (MvPolynomial.map (algebraMap Λ₀ D')) =
        (algebraMap (MvPolynomial (Fin d) Λ₀) L₀ : _ →+* _) := by
      refine MvPolynomial.ringHom_ext (fun y => ?_) fun i => ?_
      · show MvPolynomial.eval₂Hom cD τ
          (MvPolynomial.map (algebraMap Λ₀ D') (MvPolynomial.C y)) = _
        rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, hcD]
      · show MvPolynomial.eval₂Hom cD τ
          (MvPolynomial.map (algebraMap Λ₀ D') (MvPolynomial.X i)) = _
        rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X']
        exact hτ i
    intro x
    rw [hRE, ← RingHom.comp_apply, key]
  -- the evaluation of `D'[t]` carries the twisted map to `fB`
  have hcomp : ∀ x : parameterPowerAlgebra A d N a,
      MvPolynomial.eval₂Hom cD τ (ψ x) = fB x := by
    have key : (MvPolynomial.eval₂Hom cD τ).comp (ψ : _ →+* MvPolynomial (Fin d) D') = fB := by
      refine parameterPowerAlgebra_ringHom_ext (fun x => ?_) (fun i => ?_) fun i j => ?_
      · show MvPolynomial.eval₂Hom cD τ (ψ (algebraMap A _ x)) = _
        rw [hψA x, MvPolynomial.eval₂Hom_C, hfBA x]
      · show MvPolynomial.eval₂Hom cD τ (ψ _) = _
        rw [hψX i, hfBX i, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
      · show MvPolynomial.eval₂Hom cD τ (ψ _) = _
        rw [hψZ i j, map_mul, MvPolynomial.eval₂Hom_C, map_pow, MvPolynomial.eval₂Hom_X',
          map_mul, map_pow]
        calc cD (lam i j) * cD ((↑(hδ i).unit⁻¹ : D')) ^ (2 * N) * τ i ^ (2 * N)
            = (cD (lam i j) * τ i ^ (2 * N)) * cD ((↑(hδ i).unit⁻¹ : D')) ^ (2 * N) := by ring
          _ = fB (Ideal.Quotient.mk (parameterPowerIdeal d N a)
              (MvPolynomial.X (Sum.inr (i, j)))) := by
                rw [← hfBZ i j, mul_assoc, ← mul_pow, mul_comm (cD (δ i)),
                  show cD ((↑(hδ i).unit⁻¹ : D')) * cD (δ i) = 1 by
                    rw [← map_mul, IsUnit.val_inv_mul, map_one],
                  one_pow, mul_one]
    exact fun x => RingHom.congr_fun key x
  exact exists_smoothFactorizationData
    (indSmooth_mvPolynomial_of_formallySmooth_of_isLocalization M hD d) ψ.toRingHom
    (MvPolynomial.eval₂Hom cD τ) fB hgE hkE hcomp

/-- **Stacks 07FJ, items (24), (25) and (26)** (tags 07G8, 07G9 and 07GA) together, at the
improved algebra `C` of Stacks 07CE. The retraction `grt : C → B` of 07CE transports the datum
produced by `Stacks.Smoothing.exists_smoothFactorizationData_twisted` from `B` to `C`, which is
item (24); `hcL` is the compatibility of the two evaluations in `L₀` that item (24) needs. -/
theorem exists_smoothFactorizationData_improved (k : Type u) {A C Λ₀ D' L₀ : Type u}
    {d t N : ℕ} [CommRing k] [IsNoetherianRing k] [CommRing A] [CommRing C] [CommRing Λ₀]
    [CommRing D'] [CommRing L₀] [Algebra k A] [Algebra.FiniteType k A] [Algebra k D']
    [Algebra Λ₀ D'] [Algebra (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) Λ₀)]
    [Algebra (MvPolynomial (Fin d) Λ₀) L₀] (a : Fin t → A)
    [Algebra (MvPolynomial (Fin d) k) C]
    (grt : C →ₐ[MvPolynomial (Fin d) k] parameterPowerAlgebra A d N a) {B₀ : Type u}
    [CommRing B₀] [Algebra Λ₀ B₀] [Algebra B₀ D'] [IsScalarTower Λ₀ B₀ D']
    [Algebra.FinitePresentation Λ₀ B₀] (M : Submonoid B₀) [IsLocalization M D']
    (hD : Algebra.FormallySmooth Λ₀ D') (φ : A →ₐ[k] D') (π δ : Fin d → D')
    (lam : Fin d → Fin t → D') (hδ : ∀ i, IsUnit (δ i))
    (hrel : ∀ i, (δ i * π i) ^ (2 * N) = ∑ j, φ (a j) * lam i j) (cD : D' →+* L₀)
    (τ : Fin d → L₀)
    (hcD : ∀ y : Λ₀, cD (algebraMap Λ₀ D' y) =
      algebraMap (MvPolynomial (Fin d) Λ₀) L₀ (MvPolynomial.C y))
    (hτ : ∀ i, τ i = algebraMap (MvPolynomial (Fin d) Λ₀) L₀ (MvPolynomial.X i))
    (hsqC : ∀ r : k, MvPolynomial.map (algebraMap Λ₀ D')
        (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) Λ₀) (MvPolynomial.C r)) =
      MvPolynomial.C (algebraMap k D' r))
    (hsqX : ∀ i, MvPolynomial.map (algebraMap Λ₀ D')
        (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) Λ₀) (MvPolynomial.X i)) =
      MvPolynomial.C (π i) * MvPolynomial.X i)
    (fB : parameterPowerAlgebra A d N a →+* L₀)
    (hfBA : ∀ x : A, fB (algebraMap A (parameterPowerAlgebra A d N a) x) = cD (φ x))
    (hfBX : ∀ i, fB (Ideal.Quotient.mk (parameterPowerIdeal d N a)
      (MvPolynomial.X (Sum.inl i))) = cD (π i) * τ i)
    (hfBZ : ∀ i j, fB (Ideal.Quotient.mk (parameterPowerIdeal d N a)
        (MvPolynomial.X (Sum.inr (i, j)))) * cD (δ i) ^ (2 * N) =
      cD (lam i j) * τ i ^ (2 * N)) (cL : C →+* L₀) (hcL : ∀ c : C, cL c = fB (grt c)) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra (MvPolynomial (Fin d) Λ₀) T),
      Algebra.Smooth (MvPolynomial (Fin d) Λ₀) T ∧
      ∃ (g : C →+* T) (kk : T →+* L₀),
        (∀ y : MvPolynomial (Fin d) k, g (algebraMap (MvPolynomial (Fin d) k) C y) =
          algebraMap (MvPolynomial (Fin d) Λ₀) T
            (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) Λ₀) y)) ∧
        (∀ x : MvPolynomial (Fin d) Λ₀, kk (algebraMap (MvPolynomial (Fin d) Λ₀) T x) =
          algebraMap (MvPolynomial (Fin d) Λ₀) L₀ x) ∧
        ∀ c : C, kk (g c) = cL c :=
  exists_smoothFactorizationData_of_algHom grt fB cL hcL
    (exists_smoothFactorizationData_twisted k a M hD φ π δ lam hδ hrel cD τ hcD hτ hsqC hsqX fB
      hfBA hfBX hfBZ)

end Stacks.Smoothing

end
