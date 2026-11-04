module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Kaehler.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.HigherTrace.Basic
public import StacksFrontier.LinearAlgebra.ExteriorPower.Localization
public import StacksFrontier.RingTheory.DeRham.PolynomialHomotopy
public import StacksFrontier.RingTheory.DiscreteValuationRing.PurelyInseparable
public import StacksFrontier.RingTheory.Kaehler.Basic
public import StacksFrontier.LinearAlgebra.ExteriorPower.LocalizationSupplement
public import StacksFrontier.RingTheory.DiscreteValuationRing.PurelyInseparableSupplement

/-!
# The trace of [Stacks, Tag 0AX5] at a codimension-one point

Let `Λ → Λ'` be a ring map, let `A → B` be an extension of `Λ`-algebras with fraction fields
`K → L`, and suppose `B = A[x]` with `x ^ p = a ∈ A`, so that `L = K[T]/(Tᵖ - a)`.  The trace of
[Stacks, Tag 0AX5] on `⋀ⁱ Ω_{L/Λ'} → ⋀ⁱ Ω_{K/Λ'}` then carries the image of `⋀ⁱ Ω_{B/Λ}` into
the image of `⋀ⁱ Ω_{A/Λ}`.

This is the third paragraph of the proof of [Stacks, Tag 0AX6]: the codimension-one condition
that the extension criterion of [Stacks, Tag 0AY7] asks for, in the form it takes once the
stalks at a codimension-one point and at the generic point have been identified with modules of
Kähler differentials.

## Main results

* `KaehlerDifferential.forall_mem_of_span_union_singleton`: a reduction principle.  If `Ω_{B/Λ}`
  is generated over `B` by the differentials pulled back from `A` together with one extra
  element `ξ`, then an additive map out of `⋀ⁱ Ω_{L/Λ'}` sends the whole image of
  `⋀ⁱ Ω_{B/Λ}` into a subgroup as soon as it does so on the wedges of pulled-back
  differentials and on those wedges with `ξ` appended, each scaled by an element of `B`.
* `KaehlerDifferential.higherTrace_mem_range_mapExteriorPowerTower`: the statement above.
* `KaehlerDifferential.higherTrace_mem_range_mapExteriorPowerTower_of_tower`: the same for the
  image of `⋀ⁱ Ω_{B₀/Λ}` for any `Λ`-algebra `B₀` mapping to `B`.  This is the form
  [Stacks, Tag 0AX6] needs, because the ring whose image is to be traced there is a local ring
  of the source, which the Lean statement of that lemma does not assume normal, so that it need
  not itself be presentable as `A[x]`.
* `KaehlerDifferential.higherTrace_mem_range_mapExteriorPowerTower_of_isPurelyInseparable`: the
  same with the presentation itself removed from the hypotheses.  For `A` a discrete valuation
  ring with fraction field `K`, `L / K` purely inseparable of degree `p` and `B₀` module-finite
  over `A` inside `L`, the trace attached to *any* presentation of `L / K` carries the image of
  `⋀ⁱ Ω_{B₀/Λ}` into the image of `⋀ⁱ Ω_{A/Λ}`.  This is the form [Stacks, Tag 0AX6] consumes.

## Implementation notes

The reduction principle is the membership analogue of the extensionality principle that
`KaehlerDifferential.higherTrace_eq_of_presentations` runs on, and it is proved the same way:
`exteriorPower.ιMulti_family_span_of_span` applied to the spanning family
`WithTop.recTopCoe ξ ψ`, whose order embeddings `Fin (i) ↪o WithTop _` either hit `⊤` in the last
slot or miss it everywhere.  Carrying the scalar `b` through the induction, rather than fixing
it, is what makes the `smul` case of `Submodule.span_induction` go through: the conclusion for
`b • z` is *not* implied by the conclusion for `z`, because the trace is only `K`-linear while
the image of `⋀ⁱ Ω_{B/Λ}` is only a `B`-submodule.

Three inputs do the work on the generators.  `KaehlerDifferential.higherTrace_smul_baseForm`
kills a wedge of pulled-back differentials.  On a wedge with `d x` appended,
`Algebra.span_range_pow_eq_top_of_adjoin_singleton_eq_top` writes the scalar as
`∑_{m < p} aₘ xᵐ` with `aₘ ∈ A`, and then `KaehlerDifferential.higherTrace_apply_of_le` gives
zero for `m ≤ p - 2` while `KaehlerDifferential.higherTrace_apply_top` gives
`a_{p-1} · (η₁ ∧ ⋯ ∧ η_t ∧ d a)` for `m = p - 1`, a form pulled back from `A` because `a` lies in
`A`.  That last point is why the presentation is taken with its constant term in `A`.

Where the presentation comes from is
`IsDiscreteValuationRing.exists_algEquiv_adjoinRoot_and_mem_adjoin_of_isPurelyInseparable`: the
image of `B₀` is *contained* in some `A[x]` inside `L` with `x ^ p` in `A`, and that `A[x]` is
what plays the part of `B`.  Containment is all that is on offer and all that is needed.  The
integral closure of `A` in `L` is **not** a substitute: over a non-excellent discrete valuation
ring in characteristic `p` it need not even be module-finite over `A`, let alone monogenic —
that is the failure of the N-2 property.  Pushing `B` out of the statement is therefore not a
convenience but the only available route, and it is what
`KaehlerDifferential.higherTrace_mem_range_mapExteriorPowerTower_of_isPurelyInseparable` is
built on; `KaehlerDifferential.higherTrace_eq_of_presentations` then replaces the quantified
presentation by the constructed one.

## References

* [Stacks Project, Tag 0AX5](https://stacks.math.columbia.edu/tag/0AX5)
* [Stacks Project, Tag 0AX6](https://stacks.math.columbia.edu/tag/0AX6)
-/

public noncomputable section

namespace KaehlerDifferential

open Polynomial
open scoped KaehlerDifferential

/-- Appending a scalar multiple of a vector to a fixed wedge pulls the scalar out. -/
private theorem exterior_snoc_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (v : Fin n → M) (m : M) (s : R) :
    exteriorPower.ιMulti R (n + 1) (Fin.snoc v (s • m)) =
      s • exteriorPower.ιMulti R (n + 1) (Fin.snoc v m) :=
  (exteriorPower.ιMulti R (n + 1)).toMultilinearMap.snoc_smul v s m

/-- A generator of the exterior power indexed by an order embedding into `WithTop M` lies in `W`,
given that the generators built from `ψ` alone, and those with `ξ` appended, do. -/
private theorem mem_of_orderEmbedding_withTop {B L M NB N P : Type*}
    [CommRing B] [CommRing L] [Algebra B L] [AddCommGroup NB] [Module B NB]
    [AddCommGroup N] [Module B N] [Module L N] [IsScalarTower B L N] [AddCommGroup P]
    [LinearOrder M] (n : ℕ) (ψ : M → NB) (ξ : NB)
    (Φ : NB →ₗ[B] N) (F : (⋀[L]^(n + 1) N) →+ P) (W : AddSubgroup P)
    (hbase : ∀ b : B, ∀ η : Fin (n + 1) → M,
      F (b • exteriorPower.ιMulti L (n + 1) fun j => Φ (ψ (η j))) ∈ W)
    (hroot : ∀ b : B, ∀ η : Fin n → M,
      F (b • exteriorPower.ιMulti L (n + 1) (Fin.snoc (fun j => Φ (ψ (η j))) (Φ ξ))) ∈ W)
    (α : Fin (n + 1) ↪o WithTop M) (b : B) :
    F (b • exteriorPower.ιMulti L (n + 1)
      fun i => Φ (WithTop.recTopCoe ξ ψ (α i) : NB)) ∈ W := by
  have hne (j : Fin n) : α j.castSucc ≠ ⊤ :=
    ne_top_of_lt (α.strictMono (Fin.castSucc_lt_last j))
  let η : Fin n → M := fun j => (α j.castSucc).untop (hne j)
  have hη (j : Fin n) : (WithTop.recTopCoe ξ ψ (α j.castSucc) : NB) = ψ (η j) := by
    rw [← WithTop.coe_untop (α j.castSucc) (hne j)]
    rfl
  by_cases hlast : α (Fin.last n) = ⊤
  · have heq : (fun i => Φ (WithTop.recTopCoe ξ ψ (α i) : NB)) =
        Fin.snoc (fun j => Φ (ψ (η j))) (Φ ξ) := by
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp [hlast]
      · simp [hη i]
    rw [heq]
    exact hroot b η
  · have hall (j : Fin (n + 1)) : α j ≠ ⊤ := fun h =>
      hlast (top_unique (h ▸ α.monotone (Fin.le_last j)))
    let ζ : Fin (n + 1) → M := fun j => (α j).untop (hall j)
    have heq : (fun i => Φ (WithTop.recTopCoe ξ ψ (α i) : NB)) = fun j => Φ (ψ (ζ j)) := by
      funext j
      rw [← WithTop.coe_untop (α j) (hall j)]
      rfl
    rw [heq]
    exact hbase b ζ

/-- **A reduction principle for maps out of the top exterior power of a module with a generating
set of the shape `range ψ ∪ {ξ}`.**  An additive map `F` out of `⋀ⁿ⁺¹ N`, for `N` a module over
an algebra `L` over `B`, sends the whole image of `⋀ⁿ⁺¹ NB` into a subgroup `W` as soon as it
sends there every `b • (Φ (ψ η₁) ∧ ⋯ ∧ Φ (ψ η_{n+1}))` and every
`b • (Φ (ψ η₁) ∧ ⋯ ∧ Φ (ψ η_n) ∧ Φ ξ)`.

The scalar `b` is quantified inside the two hypotheses rather than outside the conclusion
because `W` is only assumed to be an additive subgroup: it need not be stable under the action
of `B`, so the conclusion for `b • z` does not follow from the conclusion for `z`. -/
theorem forall_mem_of_span_union_singleton {B L M NB N P : Type*}
    [CommRing B] [CommRing L] [Algebra B L] [AddCommGroup NB] [Module B NB]
    [AddCommGroup N] [Module B N] [Module L N] [IsScalarTower B L N] [AddCommGroup P]
    (n : ℕ) (ψ : M → NB) (ξ : NB)
    (hspan : Submodule.span B (Set.range ψ ∪ {ξ}) = ⊤)
    (Φ : NB →ₗ[B] N) (F : (⋀[L]^(n + 1) N) →+ P) (W : AddSubgroup P)
    (hbase : ∀ b : B, ∀ η : Fin (n + 1) → M,
      F (b • exteriorPower.ιMulti L (n + 1) fun j => Φ (ψ (η j))) ∈ W)
    (hroot : ∀ b : B, ∀ η : Fin n → M,
      F (b • exteriorPower.ιMulti L (n + 1) (Fin.snoc (fun j => Φ (ψ (η j))) (Φ ξ))) ∈ W)
    (z : ⋀[B]^(n + 1) NB) :
    F (exteriorPower.mapTower (S := L) (n + 1) Φ z) ∈ W := by
  classical
  let : LinearOrder M := linearOrderOfSTO WellOrderingRel
  let v : WithTop M → NB := WithTop.recTopCoe ξ ψ
  have hv : Submodule.span B (Set.range v) = ⊤ := by
    convert hspan using 2
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      induction i using WithTop.recTopCoe with
      | top => exact Or.inr rfl
      | coe i => exact Or.inl ⟨i, rfl⟩
    · rintro (⟨i, rfl⟩ | rfl)
      · exact ⟨(i : WithTop M), rfl⟩
      · exact ⟨⊤, rfl⟩
  have hgen (α : Fin (n + 1) ↪o WithTop M) (b : B) :
      F (exteriorPower.mapTower (S := L) (n + 1) Φ
        (b • exteriorPower.ιMulti B (n + 1) (v ∘ α))) ∈ W := by
    rw [map_smul, exteriorPower.mapTower_ιMulti]
    exact mem_of_orderEmbedding_withTop n ψ ξ Φ F W hbase hroot α b
  have hz : z ∈ Submodule.span B (Set.range (exteriorPower.ιMulti_family B (n + 1) v)) := by
    rw [exteriorPower.ιMulti_family_span_of_span B (n := n + 1) hv]
    exact Submodule.mem_top
  suffices h : ∀ b : B, F (exteriorPower.mapTower (S := L) (n + 1) Φ (b • z)) ∈ W by
    simpa using h 1
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨z, rfl⟩ := hz
    exact hgen (Set.powersetCard.ofFinEmbEquiv.symm z)
  | zero =>
    intro b
    simp
  | add z w hz hw iz iw =>
    intro b
    rw [smul_add, map_add, map_add]
    exact W.add_mem (iz b) (iw b)
  | smul c z hz ih =>
    intro b
    simpa [smul_smul] using ih (b * c)

section BaseTransport

/-- **Enlarging the base of a map of relative differentials commutes with taking exterior
powers.**  For a tower `Λ → Λ' → Λ''` of bases and an algebra `B → L` over `Λ`, the map
`⋀ⁿ Ω[B⁄Λ] → ⋀ⁿ Ω[L⁄Λ']` followed by the enlargement of the base to `Λ''` is the map
`⋀ⁿ Ω[B⁄Λ] → ⋀ⁿ Ω[L⁄Λ'']`.

This is `KaehlerDifferential.map_base_comp_map` carried through `exteriorPower.mapTower` by
`exteriorPower.map_comp_mapTower`.  The enlargement is taken as a map `g` together with an
equation rather than as `KaehlerDifferential.map Λ' Λ'' L L` itself, because in the application
it arrives as a linear equivalence — the comparison of the two readings of the base ring of
`Ω_{Y/S}` at a point — and the equation is what identifies that comparison with a
change-of-base map. -/
theorem map_mapTower_of_base {Λ Λ' Λ'' B L : Type*} [CommRing Λ] [CommRing Λ'] [CommRing Λ'']
    [CommRing B] [CommRing L] [Algebra Λ Λ'] [Algebra Λ' Λ''] [Algebra Λ Λ''] [Algebra Λ B]
    [Algebra Λ' L] [Algebra Λ'' L] [Algebra Λ L] [Algebra B L] [IsScalarTower Λ Λ' Λ'']
    [IsScalarTower Λ' Λ'' L] [IsScalarTower Λ Λ' L] [IsScalarTower Λ Λ'' L]
    [IsScalarTower Λ B L] (n : ℕ) {g : Ω[L⁄Λ'] →ₗ[L] Ω[L⁄Λ'']} (hg : g = map Λ' Λ'' L L)
    (ω : ⋀[B]^n (Ω[B⁄Λ])) :
    exteriorPower.map n g (exteriorPower.mapTower (S := L) n (map Λ Λ' B L) ω) =
      exteriorPower.mapTower (S := L) n (map Λ Λ'' B L) ω := by
  subst hg
  have hcomp := LinearMap.congr_fun
    (exteriorPower.map_comp_mapTower L (map Λ Λ' B L) (map Λ' Λ'' L L) n) ω
  rwa [map_base_comp_map Λ Λ' Λ'' B L] at hcomp

end BaseTransport

section Tower

variable {p t : ℕ} {Λ Λ' A B K L : Type*}
  [CommRing Λ] [CommRing Λ'] [CommRing A] [CommRing B] [Field K] [Field L]
  [Algebra Λ Λ'] [Algebra Λ A] [Algebra Λ B] [Algebra Λ K] [Algebra Λ L]
  [Algebra Λ' K] [Algebra Λ' L] [Algebra A B] [Algebra A K] [Algebra A L]
  [Algebra B L] [Algebra K L]
  [IsScalarTower Λ Λ' K] [IsScalarTower Λ Λ' L] [IsScalarTower Λ' K L]
  [IsScalarTower Λ A B] [IsScalarTower Λ A K] [IsScalarTower Λ A L]
  [IsScalarTower Λ B L] [IsScalarTower A B L] [IsScalarTower A K L]
  [SMulCommClass Λ' A K] [SMulCommClass Λ' A L] [SMulCommClass Λ' B L]
  [SMulCommClass Λ A B]

variable {B₀ : Type*} [CommRing B₀] [Algebra Λ B₀] [Algebra B₀ B] [Algebra B₀ L]
  [IsScalarTower Λ B₀ B] [IsScalarTower Λ B₀ L] [IsScalarTower B₀ B L]
  [SMulCommClass Λ' B₀ L] [SMulCommClass Λ B₀ B]

omit [IsScalarTower Λ A L] [SMulCommClass Λ' A L] in
/-- The two routes `Ω[A⁄Λ] → Ω[B⁄Λ] → Ω[L⁄Λ']` and `Ω[A⁄Λ] → Ω[K⁄Λ'] → Ω[L⁄Λ']` agree: both are
the map induced by the square `Λ → Λ'`, `A → L`. -/
private theorem map_map_eq_map_map (α : Ω[A⁄Λ]) :
    map Λ Λ' B L (map Λ Λ A B α) = map Λ' Λ' K L (map Λ Λ' A K α) := by
  refine LinearMap.congr_fun (LinearMap.ext_on_range
    (f := (map Λ Λ' B L).restrictScalars A ∘ₗ map Λ Λ A B)
    (g := (map Λ' Λ' K L).restrictScalars A ∘ₗ map Λ Λ' A K) (span_range_derivation Λ A)
    fun c => ?_) α
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [map_D Λ Λ A B, map_D Λ Λ' B L, map_D Λ Λ' A K, map_D Λ' Λ' K L,
    ← IsScalarTower.algebraMap_apply A B L, ← IsScalarTower.algebraMap_apply A K L]

omit [Algebra Λ L] [Algebra A L] [IsScalarTower Λ Λ' L] [IsScalarTower Λ A L]
  [IsScalarTower A K L] [SMulCommClass Λ' A L] in
/-- The trace of [Stacks, Tag 0AX5] carries `η₁ ∧ ⋯ ∧ η_t ∧ xⁱ d x`, for forms `ηⱼ` pulled back
from `A`, into the image of `⋀ⁱ Ω_{A/Λ}`. -/
private theorem higherTrace_snoc_pow_mem_range (hp : p.Prime) [CharP Λ' p] {a : A}
    (e : AdjoinRoot (X ^ p - C (algebraMap A K a)) ≃ₐ[K] L) (η : Fin t → Ω[A⁄Λ]) (i : Fin p) :
    higherTrace (t := t) (Λ := Λ') hp (algebraMap A K a) e
        (exteriorPower.ιMulti L (t + 1)
          (Fin.snoc (fun j => map Λ' Λ' K L (map Λ Λ' A K (η j)))
            (e (AdjoinRoot.root (X ^ p - C (algebraMap A K a))) ^ (i : ℕ) •
              D Λ' L (e (AdjoinRoot.root (X ^ p - C (algebraMap A K a))))))) ∈
      LinearMap.range (exteriorPower.mapTower (S := K) (t + 1) (map Λ Λ' A K)) := by
  rcases eq_or_lt_of_le (Nat.le_sub_one_of_lt i.isLt) with hi | hi
  · -- the top power: the value is a form pulled back from `A`
    have hfun : (fun j => map Λ Λ' A K
          ((Fin.snoc η (D Λ A a) : Fin (t + 1) → Ω[A⁄Λ]) j)) =
        Fin.snoc (fun j => map Λ Λ' A K (η j)) (D Λ' K (algebraMap A K a)) := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [map_D Λ Λ' A K]
      · simp
    refine ⟨exteriorPower.ιMulti A (t + 1) (Fin.snoc η (D Λ A a)), ?_⟩
    rw [exteriorPower.mapTower_ιMulti, hfun, hi]
    exact (higherTrace_apply_top hp (algebraMap A K a) e _).symm
  · -- below the top power: the value is zero
    refine ⟨0, ?_⟩
    rw [map_zero]
    exact (higherTrace_apply_of_le hp (algebraMap A K a) e _ (by omega) _).symm

omit [IsScalarTower Λ A L] [SMulCommClass Λ' A L] in
/-- **The trace of [Stacks, Tag 0AX5] carries the image of `⋀ⁱ Ω_{B/Λ}` into the image of
`⋀ⁱ Ω_{A/Λ}`.**  This is the third paragraph of the proof of [Stacks, Tag 0AX6]: `B = A[x]` with
`x ^ p = a ∈ A`, and the presentation `L ≅ K[T]/(Tᵖ - a)` it induces has its constant term in
`A`, so the value `η₁ ∧ ⋯ ∧ η_t ∧ d a` of the trace on the top power is again a form pulled back
from `A`. -/
theorem higherTrace_mem_range_mapExteriorPowerTower (hp : p.Prime) [CharP Λ' p]
    {x : B} {a : A} (e : AdjoinRoot (X ^ p - C (algebraMap A K a)) ≃ₐ[K] L)
    (hxp : x ^ p = algebraMap A B a) (hgen : Algebra.adjoin A ({x} : Set B) = ⊤)
    (he : e (AdjoinRoot.root (X ^ p - C (algebraMap A K a))) = algebraMap B L x)
    (ω : ⋀[B]^(t + 1) (Ω[B⁄Λ])) :
    higherTrace (t := t) (Λ := Λ') hp (algebraMap A K a) e
        (exteriorPower.mapTower (S := L) (t + 1) (map Λ Λ' B L) ω) ∈
      LinearMap.range (exteriorPower.mapTower (S := K) (t + 1) (map Λ Λ' A K)) := by
  classical
  set T := higherTrace (t := t) (Λ := Λ') hp (algebraMap A K a) e with hT
  set g := exteriorPower.mapTower (S := K) (t + 1) (map Λ Λ' A K)
  obtain ⟨xL, hxL⟩ : ∃ y : L, y = e (AdjoinRoot.root (X ^ p - C (algebraMap A K a))) :=
    ⟨_, rfl⟩
  have hpowspan : Submodule.span A (Set.range fun i : Fin p => x ^ (i : ℕ)) = ⊤ :=
    Algebra.span_range_pow_eq_top_of_adjoin_singleton_eq_top hp.pos hxp hgen
  have hξ : map Λ Λ' B L (D Λ B x) = D Λ' L xL := by
    rw [map_D Λ Λ' B L, hxL, he]
  -- the base-form family, after the two identifications
  have hbasefun {s : ℕ} (η : Fin s → Ω[A⁄Λ]) :
      (fun j => map Λ Λ' B L (map Λ Λ A B (η j))) =
        fun j => map Λ' Λ' K L (map Λ Λ' A K (η j)) :=
    funext fun j => map_map_eq_map_map (η j)
  refine forall_mem_of_span_union_singleton t (⇑(map Λ Λ A B)) (D Λ B x)
    (span_union_range_map_D_of_adjoin_singleton_eq_top Λ A B hgen) (map Λ Λ' B L)
    T.toAddMonoidHom (LinearMap.range g).toAddSubgroup ?_ ?_ ω
  · -- a wedge of forms pulled back from `A`: the trace kills it
    intro b η
    have hsmul : (b : B) • exteriorPower.ιMulti L (t + 1)
          (fun j => map Λ Λ' B L (map Λ Λ A B (η j))) =
        (algebraMap B L b) • exteriorPower.ιMulti L (t + 1)
          (fun j => map Λ' Λ' K L (map Λ Λ' A K (η j))) := by
      rw [hbasefun η, algebraMap_smul]
    show T _ ∈ _
    rw [hsmul, hT, higherTrace_smul_baseForm]
    exact Submodule.zero_mem _
  · -- a wedge with `d x` appended: expand the scalar in the powers of `x`
    intro b η
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp
      (hpowspan ▸ (Submodule.mem_top : b ∈ (⊤ : Submodule A B)))
    have hbL : algebraMap B L b = ∑ i : Fin p, algebraMap A L (c i) * xL ^ (i : ℕ) := by
      rw [← hc, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, map_pow, ← IsScalarTower.algebraMap_apply A B L, hxL, he]
    have hsnoc : (b : B) • exteriorPower.ιMulti L (t + 1)
          (Fin.snoc (fun j => map Λ Λ' B L (map Λ Λ A B (η j))) (map Λ Λ' B L (D Λ B x))) =
        ∑ i : Fin p, (algebraMap A L (c i)) • exteriorPower.ιMulti L (t + 1)
          (Fin.snoc (fun j => map Λ' Λ' K L (map Λ Λ' A K (η j)))
            (xL ^ (i : ℕ) • D Λ' L xL)) := by
      rw [hbasefun η, hξ, ← algebraMap_smul L b, hbL, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul, exterior_snoc_smul]
    show T _ ∈ _
    rw [hsnoc, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [IsScalarTower.algebraMap_apply A K L (c i), algebraMap_smul, map_smul, hxL]
    exact Submodule.smul_mem _ _ (higherTrace_snoc_pow_mem_range hp e η i)

/-- The two routes `Ω[B₀⁄Λ] → Ω[B⁄Λ] → Ω[L⁄Λ']` and `Ω[B₀⁄Λ] → Ω[L⁄Λ']` agree. -/
private theorem map_map_eq_map_tower (α : Ω[B₀⁄Λ]) :
    map Λ Λ' B L (map Λ Λ B₀ B α) = map Λ Λ' B₀ L α := by
  refine LinearMap.congr_fun (LinearMap.ext_on_range
    (f := (map Λ Λ' B L).restrictScalars B₀ ∘ₗ map Λ Λ B₀ B) (g := map Λ Λ' B₀ L)
    (span_range_derivation Λ B₀) fun c => ?_) α
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [map_D Λ Λ B₀ B, map_D Λ Λ' B L, map_D Λ Λ' B₀ L, ← IsScalarTower.algebraMap_apply B₀ B L]

/-- `exteriorPower.mapTower` of `KaehlerDifferential.map` composes along a tower
`B₀ → B → L`. -/
private theorem mapTower_map_tower (n : ℕ) (ω : ⋀[B₀]^n (Ω[B₀⁄Λ])) :
    exteriorPower.mapTower (S := L) n (map Λ Λ' B₀ L) ω =
      exteriorPower.mapTower (S := L) n (map Λ Λ' B L)
        (exteriorPower.mapTower (S := B) n (map Λ Λ B₀ B) ω) := by
  have hmem : ω ∈ Submodule.span B₀ (Set.range (exteriorPower.ιMulti B₀ n)) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem ω hω =>
    obtain ⟨v, rfl⟩ := hω
    have hfun : (fun j => map Λ Λ' B₀ L (v j)) =
        fun j => map Λ Λ' B L (map Λ Λ B₀ B (v j)) :=
      funext fun j => (map_map_eq_map_tower (v j)).symm
    rw [exteriorPower.mapTower_ιMulti, exteriorPower.mapTower_ιMulti,
      exteriorPower.mapTower_ιMulti, hfun]
  | zero => simp
  | add ω ν _ _ hω hν => simp [hω, hν]
  | smul c ω _ hω =>
    have e1 : exteriorPower.mapTower (S := B) n (map Λ Λ B₀ B) (c • ω) =
        (algebraMap B₀ B c) • exteriorPower.mapTower (S := B) n (map Λ Λ B₀ B) ω := by
      rw [map_smul, algebraMap_smul]
    rw [map_smul, e1, map_smul, hω, ← algebraMap_smul L c,
      ← algebraMap_smul L (algebraMap B₀ B c), ← IsScalarTower.algebraMap_apply B₀ B L]

omit [IsScalarTower Λ A L] [SMulCommClass Λ' A L] in
/-- **The trace of [Stacks, Tag 0AX5] carries the image of `⋀ⁱ Ω_{B₀/Λ}` into the image of
`⋀ⁱ Ω_{A/Λ}`, for any `Λ`-algebra `B₀` between `A` and `B`.**

This is `KaehlerDifferential.higherTrace_mem_range_mapExteriorPowerTower` with the ring carrying
the `p`-th root pushed out of the statement.  [Stacks, Tag 0AX6] needs it in this form because
the ring whose image is to be traced is a local ring of the source, which the Lean statement of
that lemma does not assume normal, so it need not itself be a discrete valuation ring and need
not be presentable as `A[x]`.  Some `A[x]` inside `L` containing the image of `B₀` is, and the
image of `⋀ⁱ Ω_{B₀/Λ}` is contained in the image of `⋀ⁱ Ω_{B/Λ}` whenever `B₀ → B`. -/
theorem higherTrace_mem_range_mapExteriorPowerTower_of_tower (hp : p.Prime) [CharP Λ' p]
    {x : B} {a : A} (e : AdjoinRoot (X ^ p - C (algebraMap A K a)) ≃ₐ[K] L)
    (hxp : x ^ p = algebraMap A B a) (hgen : Algebra.adjoin A ({x} : Set B) = ⊤)
    (he : e (AdjoinRoot.root (X ^ p - C (algebraMap A K a))) = algebraMap B L x)
    (ω : ⋀[B₀]^(t + 1) (Ω[B₀⁄Λ])) :
    higherTrace (t := t) (Λ := Λ') hp (algebraMap A K a) e
        (exteriorPower.mapTower (S := L) (t + 1) (map Λ Λ' B₀ L) ω) ∈
      LinearMap.range (exteriorPower.mapTower (S := K) (t + 1) (map Λ Λ' A K)) := by
  rw [mapTower_map_tower (B := B) (t + 1) ω]
  exact higherTrace_mem_range_mapExteriorPowerTower hp e hxp hgen he _

end Tower

section PurelyInseparable

variable {p t : ℕ} {Λ Λ' A K L B₀ : Type*}
  [CommRing Λ] [CommRing Λ'] [CommRing A] [Field K] [Field L] [CommRing B₀]
  [Algebra Λ Λ'] [Algebra Λ A] [Algebra Λ K] [Algebra Λ L] [Algebra Λ B₀]
  [Algebra Λ' K] [Algebra Λ' L]
  [Algebra A K] [Algebra A L] [Algebra A B₀] [Algebra B₀ L] [Algebra K L]
  [IsScalarTower Λ Λ' K] [IsScalarTower Λ Λ' L] [IsScalarTower Λ' K L]
  [IsScalarTower Λ A K] [IsScalarTower Λ A L] [IsScalarTower Λ A B₀]
  [IsScalarTower Λ B₀ L] [IsScalarTower A B₀ L] [IsScalarTower A K L]

omit [IsScalarTower Λ A B₀] in
/-- **The trace of [Stacks, Tag 0AX5] carries the image of `⋀ⁱ Ω_{B₀/Λ}` into the image of
`⋀ⁱ Ω_{A/Λ}`, with no presentation assumed.**

This is the third paragraph of the proof of [Stacks, Tag 0AX6] in the form that lemma consumes:
`A` is a discrete valuation ring with fraction field `K`, the extension `L / K` is purely
inseparable of prime degree `p`, and `B₀` is any `Λ`-algebra between `A` and `L` that is
module-finite over `A` — in the application, the local ring of the source at a point above a
codimension-one point of the target.  The presentation `L ≅ K[T] ⧸ (Tᵖ - a)` and the monogenic
ring carrying it are produced rather than assumed, by
`IsDiscreteValuationRing.exists_algEquiv_adjoinRoot_and_mem_adjoin_of_isPurelyInseparable`: the
image of `B₀` is contained in some `A[x]` inside `L` whose generator has `x ^ p` in `A`.  Since
the conclusion is about an arbitrary presentation `(a, e)`,
`KaehlerDifferential.higherTrace_eq_of_presentations` swaps it for the constructed one, and
`KaehlerDifferential.higherTrace_mem_range_mapExteriorPowerTower_of_tower` finishes.

`B₀` is not assumed normal, and that is the point: the monogenic ring has to be found inside
`L` because neither `B₀` nor the integral closure of `A` in `L` need be presentable as
`A[x]`. -/
theorem higherTrace_mem_range_mapExteriorPowerTower_of_isPurelyInseparable
    [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K]
    [IsPurelyInseparable K L] [Module.Finite A B₀]
    (hp : p.Prime) [CharP Λ' p] (hdegree : Module.finrank K L = p) (a : K)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[K] L) (ω : ⋀[B₀]^(t + 1) (Ω[B₀⁄Λ])) :
    higherTrace (t := t) (Λ := Λ') hp a e
        (exteriorPower.mapTower (S := L) (t + 1) (map Λ Λ' B₀ L) ω) ∈
      LinearMap.range (exteriorPower.mapTower (S := K) (t + 1) (map Λ Λ' A K)) := by
  obtain ⟨xL, a', e', hxp, hmem, he'⟩ :=
    IsDiscreteValuationRing.exists_algEquiv_adjoinRoot_and_mem_adjoin_of_isPurelyInseparable
      A K L B₀ hp hdegree
  let : Algebra B₀ (Algebra.adjoin A ({xL} : Set L)) :=
    (AlgHom.codRestrict (IsScalarTower.toAlgHom A B₀ L)
      (Algebra.adjoin A ({xL} : Set L)) hmem).toRingHom.toAlgebra
  have : IsScalarTower A (Algebra.adjoin A ({xL} : Set L)) L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower B₀ (Algebra.adjoin A ({xL} : Set L)) L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Λ A (Algebra.adjoin A ({xL} : Set L)) :=
    IsScalarTower.of_algebraMap_eq fun w =>
      Subtype.ext (IsScalarTower.algebraMap_apply Λ A L w)
  have : IsScalarTower Λ (Algebra.adjoin A ({xL} : Set L)) L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Λ B₀ (Algebra.adjoin A ({xL} : Set L)) :=
    IsScalarTower.of_algebraMap_eq fun w =>
      Subtype.ext (IsScalarTower.algebraMap_apply Λ B₀ L w)
  have hxLmem : xL ∈ Algebra.adjoin A ({xL} : Set L) :=
    Algebra.self_mem_adjoin_singleton A xL
  have hgen : Algebra.adjoin A
      ({(⟨xL, hxLmem⟩ : Algebra.adjoin A ({xL} : Set L))} :
        Set (Algebra.adjoin A ({xL} : Set L))) = ⊤ := by
    rw [← @Algebra.adjoin_adjoin_coe_preimage A L _ _ _ {xL}]
    congr 1
    ext w
    simp [Subtype.ext_iff]
  have hxpB : (⟨xL, hxLmem⟩ : Algebra.adjoin A ({xL} : Set L)) ^ p =
      algebraMap A (Algebra.adjoin A ({xL} : Set L)) a' := Subtype.ext (by simpa using hxp)
  have heB : e' (AdjoinRoot.root (X ^ p - C (algebraMap A K a'))) =
      algebraMap (Algebra.adjoin A ({xL} : Set L)) L
        (⟨xL, hxLmem⟩ : Algebra.adjoin A ({xL} : Set L)) := he'
  rw [higherTrace_eq_of_presentations (t := t) (Λ := Λ') hp a (algebraMap A K a') e e']
  exact higherTrace_mem_range_mapExteriorPowerTower_of_tower hp e' hxpB hgen heB ω

end PurelyInseparable

end KaehlerDifferential

end
