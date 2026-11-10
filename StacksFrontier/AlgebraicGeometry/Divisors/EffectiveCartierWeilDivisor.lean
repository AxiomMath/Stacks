module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.Stalkwise
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.PrimeDivisorStalk
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Weil divisor of an effective Cartier divisor

Let `X` be a Noetherian integral scheme and let `D ⊆ X` be an effective Cartier divisor, cut
out by an ideal sheaf `I`.  The *Weil divisor of `D`* is the formal sum `Σ v_Z(D) [Z]` over the
prime divisors of `X`, where the coefficient at `Z` with generic point `ξ` is

* `v_Z(D) = 0` when `ξ ∉ D`, and
* `v_Z(D) = length_{𝒪_{X, ξ}} (𝒪_{X, ξ} / (f))` when `ξ ∈ D`, for the nonzerodivisor `f`
  cutting out `D` on an affine open neighbourhood of `ξ`.

Both clauses are instances of one formula: the coefficient is the length of the quotient of the
local ring at `ξ` by the stalk of `I` there, which is the unit ideal exactly when `ξ ∉ D`.  The
coefficient family is finitely supported, so it is a Weil divisor.

## Main definitions

* `AlgebraicGeometry.effectiveCartierMultiplicity` is that length, as an integer.
* `AlgebraicGeometry.effectiveCartierWeilDivisor` is the Weil divisor of an effective Cartier
  divisor.

## Main results

* `AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support`: the stalk of an ideal
  sheaf is the unit ideal exactly away from its support.
* `AlgebraicGeometry.PrimeDivisor.eq_of_support_eq`: a prime divisor is determined by its
  underlying closed subset.
* `AlgebraicGeometry.PrimeDivisor.support_eq_of_isIrreducible`: an irreducible closed subset of
  a proper closed subset of `X` containing the generic point of a prime divisor is that prime
  divisor's support.
* `AlgebraicGeometry.effectiveCartierMultiplicity_support_finite`: the coefficient family of
  any ideal sheaf is finitely supported.
* `AlgebraicGeometry.length_quotient_idealSheafStalk_ne_top`: for an effective Cartier divisor
  the local length is finite.
* `AlgebraicGeometry.effectiveCartierWeilDivisor_apply`,
  `AlgebraicGeometry.effectiveCartierWeilDivisor_apply_of_notMem_support` and
  `AlgebraicGeometry.effectiveCartierWeilDivisor_apply_of_ideal_eq_span` identify the
  coefficients, the second and third being the two clauses of the definition.

## Implementation notes

The order function `v_Z` of Tag 02AR is `Ring.ord` of Tag 02MD once the stalk ideal is written
as a principal ideal, and the finiteness of the length is Mathlib's `Ring.ord_ne_top`, which
needs the local ring to be Noetherian of dimension at most one — the latter supplied by
`AlgebraicGeometry.PrimeDivisor.ringKrullDim_stalk_genericPoint_eq_one`.  This is not
`AlgebraicGeometry.orderOfVanishingAtPrimeDivisor`, which is the order of a section of an
invertible sheaf along a prime divisor, a different and later construction.

Finite support needs no hypothesis on the ideal sheaf beyond `X` being Noetherian and integral:
a prime divisor with a nonzero coefficient has its generic point in the support of the ideal
sheaf, its underlying closed subset is then an irreducible component of that support because
codimension one leaves no room for a strictly larger proper irreducible closed subset, and a
prime divisor is determined by that subset.  Effective Cartier-ness enters only through the
finiteness of the length, which is what makes the conversion from `ℕ∞` to `ℤ` faithful; so the
hypothesis is retained in the construction even though the term does not use it, because
dropping it would define the Weil divisor of an arbitrary closed subscheme, which is not the
object of Tag 02AR part (5).

A Weil divisor is `AlgebraicGeometry.WeilDivisor`, a locally finite coefficient
family; `AlgebraicGeometry.weilDivisorEquivFinsupp` identifies it with the finite formal linear
combinations, and `weilDivisorEquivFinsupp_effectiveCartierWeilDivisor` reads the construction
below in that form.

## References

* [Stacks Project, Tag 02AR](https://stacks.math.columbia.edu/tag/02AR)
* [Stacks Project, Tag 0BE2](https://stacks.math.columbia.edu/tag/0BE2)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### The stalk of an ideal sheaf and its support -/

/-- The image under a germ map of the sections of an ideal sheaf on an affine open is
contained in the ideal that sheaf induces in the local ring. -/
theorem IdealSheafData.map_germ_le_stalk (I : X.IdealSheafData) {x : X}
    (U : X.affineOpens) (hx : x ∈ U.1) :
    (I.ideal U).map (X.presheaf.germ U.1 x hx).hom ≤ IdealSheafData.stalk I x :=
  le_iSup_of_le U (le_iSup_of_le hx le_rfl)

/-- The ideal induced in the local ring at `x` by an ideal sheaf is contained in the maximal
ideal exactly when `x` lies in the support of the sheaf. -/
alias IdealSheafData.stalk_le_maximalIdeal_iff_mem_support :=
  Stacks.Divisors.stalk_le_maximalIdeal_iff_mem_support

/-- The ideal induced in the local ring at `x` by an ideal sheaf is the unit ideal exactly when
`x` lies outside the support of the sheaf. -/
alias IdealSheafData.stalk_eq_top_iff_notMem_support :=
  Stacks.Divisors.stalk_eq_top_iff_notMem_support

/-- If an ideal sheaf is generated by one section on an affine open, the ideal it induces in
the local ring at a point of that open is generated by the germ of that section. -/
theorem IdealSheafData.stalk_eq_span_germ_of_ideal_eq_span {I : X.IdealSheafData} {x : X}
    {U : X.affineOpens} (hx : x ∈ U.1) {f : Γ(X, U.1)} (hf : I.ideal U = Ideal.span {f}) :
    IdealSheafData.stalk I x = Ideal.span {(X.presheaf.germ U.1 x hx).hom f} := by
  rw [IdealSheafData.stalk_eq_map_germ I x U hx, hf, Ideal.map_span]
  simp

/-- The ideal that an effective Cartier divisor induces in the local ring at any point is
generated by a single nonzerodivisor: the germ of the nonzerodivisor cutting the divisor out on
an affine open neighbourhood.  This is the element written `f ∈ 𝒪_{X, Z}` in Tag 02AR part (5),
clause (b). -/
theorem exists_stalk_eq_span_of_isEffectiveCartierDivisor [IsIntegral X]
    {I : X.IdealSheafData} (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (x : X) :
    ∃ g : X.presheaf.stalk x,
      IdealSheafData.stalk I x = Ideal.span {g} ∧ g ∈ nonZeroDivisors (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, f, hf, hlocal⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor I hI x
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : IsDomain Γ(X, U) := IsIntegral.component_integral U
  refine ⟨(X.presheaf.germ U x hxU).hom f,
    IdealSheafData.stalk_eq_span_germ_of_ideal_eq_span (U := ⟨U, hU⟩) hxU hlocal,
    mem_nonZeroDivisors_iff_ne_zero.mpr fun h =>
      isRegular_iff_ne_zero.mp hf (germ_injective_of_isIntegral X x hxU (by simpa using h))⟩

/-! ### The support of a prime divisor -/

/-- The underlying closed subset of a prime divisor is the closure of its generic point. -/
theorem PrimeDivisor.support_eq_closure_genericPoint (Z : PrimeDivisor X) :
    (Z.support : Set X) = closure ({Z.genericPoint} : Set X) := by
  have := Z.integral
  change ((Z.idealSheaf.support : Closeds X) : Set X) = _
  rw [← Scheme.IdealSheafData.range_subschemeι]
  set η := _root_.genericPoint Z.idealSheaf.subscheme with hη
  calc Set.range Z.idealSheaf.subschemeι
      = Z.idealSheaf.subschemeι '' closure ({η} : Set _) := by
        rw [hη, genericPoint_closure]
        simp
    _ = closure (Z.idealSheaf.subschemeι '' ({η} : Set _)) :=
        (Z.idealSheaf.subschemeι.isClosedEmbedding.closure_image_eq _).symm
    _ = closure ({Z.genericPoint} : Set X) := by rw [Set.image_singleton]; rfl

/-- A prime divisor is determined by its underlying closed subset: the subscheme is integral,
hence reduced, so its ideal sheaf is the vanishing ideal of that subset. -/
theorem PrimeDivisor.eq_of_support_eq {Z W : PrimeDivisor X}
    (h : (Z.support : Set X) = W.support) : Z = W := by
  have key (P : PrimeDivisor X) :
      P.idealSheaf = Scheme.IdealSheafData.vanishingIdeal P.idealSheaf.support :=
    have := P.integral
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl
  have hI : Z.idealSheaf = W.idealSheaf := by
    rw [key Z, key W, show Z.idealSheaf.support = W.idealSheaf.support from
      SetLike.coe_injective h, ← key W]
  cases Z with
  | mk IZ hIZ hdimZ =>
    cases W with
    | mk IW hIW hdimW =>
      cases hI
      cases Subsingleton.elim hIZ hIW
      cases Subsingleton.elim hdimZ hdimW
      rfl

/-- An irreducible closed subset `S` of `X` that contains the generic point of a prime divisor
`Z` and is contained in a proper subset `D` of `X` is the underlying closed subset of `Z`.  The
codimension of `Z` is one, so a strict inclusion `Z ⊂ S ⊂ X` would exhibit a chain of length
two above `Z`. -/
theorem PrimeDivisor.support_eq_of_isIrreducible [IsIntegral X] (Z : PrimeDivisor X)
    {S : Set X} (hSclosed : IsClosed S) (hSirred : IsIrreducible S) {D : Set X} (hSsub : S ⊆ D)
    (hxi : Z.genericPoint ∈ S) (hDproper : D ≠ Set.univ) :
    S = Z.support := by
  set A : IrreducibleCloseds X := IrreducibleCloseds.closureSingleton Z.genericPoint with hA
  set B : IrreducibleCloseds X := ⟨S, hSirred, hSclosed⟩
  set T : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hABle : A ≤ B := closure_minimal (Set.singleton_subset_iff.mpr hxi) hSclosed
  have hBT : B < T := lt_of_le_of_ne (Set.subset_univ _) fun he =>
    hDproper (Set.eq_univ_of_univ_subset
      (fun x _ => hSsub (show x ∈ (B : Set X) from he ▸ Set.mem_univ x)))
  have hABeq : A = B := by
    by_contra hne
    have htwo : (2 : ℕ∞) ≤ codimension A :=
      (codimension_iff_exists_chain A 2).2
        ⟨((RelSeries.singleton _ T).cons B (by simpa using hBT)).cons A
          (by simpa using lt_of_le_of_ne hABle hne), by simp, by simp⟩
    rw [Z.codimension_closureSingleton_genericPoint] at htwo
    norm_num at htwo
  rw [show S = (A : Set X) from
      congrArg (fun Q : IrreducibleCloseds X => (Q : Set X)) hABeq.symm,
    hA, Z.support_eq_closure_genericPoint]
  rfl

/-! ### The order of an ideal sheaf at a prime divisor -/

/-- **The order `v_Z(D)` of Tag 02AR part (5).** The length of the quotient of the local ring
at the generic point of `Z` by the ideal that `I` induces there, read as an integer.  For an
effective Cartier divisor that length is finite, by
`AlgebraicGeometry.length_quotient_idealSheafStalk_ne_top`. -/
@[ega "IV 21.6.5" "partial", ega "IV 21.6.7" "special case"]
def effectiveCartierMultiplicity (I : X.IdealSheafData) (Z : PrimeDivisor X) : ℤ :=
  ((Module.length (X.presheaf.stalk Z.genericPoint)
    ((X.presheaf.stalk Z.genericPoint) ⧸ IdealSheafData.stalk I Z.genericPoint)).toNat : ℤ)

/-- **Tag 02AR part (5), clause (a).** The order vanishes at a prime divisor whose generic
point lies outside the subscheme. -/
theorem effectiveCartierMultiplicity_eq_zero_of_notMem_support (I : X.IdealSheafData)
    (Z : PrimeDivisor X) (hZ : Z.genericPoint ∉ I.support) :
    effectiveCartierMultiplicity I Z = 0 := by
  rw [effectiveCartierMultiplicity,
    (IdealSheafData.stalk_eq_top_iff_notMem_support I Z.genericPoint).2 hZ]
  simp

/-- A commutative ring of positive Krull dimension has infinite length as a module over
itself: finite length would make it Artinian, hence of dimension zero. -/
theorem length_self_eq_top_of_ringKrullDim_pos (R : Type*) [CommRing R]
    (hR : 0 < ringKrullDim R) : Module.length R R = ⊤ := by
  by_contra h
  obtain ⟨hNoeth, hArt⟩ :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp h)
  have : IsNoetherianRing R := hNoeth
  exact absurd (Ring.krullDimLE_iff.mp (isArtinianRing_iff_krullDimLE_zero.mp hArt))
    (not_le_of_gt hR)

/-- The order of the whole scheme, viewed as a closed subscheme of itself, vanishes: the local
ring at the generic point of a prime divisor has dimension one, so it has infinite length. -/
theorem effectiveCartierMultiplicity_bot (Z : PrimeDivisor X) :
    effectiveCartierMultiplicity (⊥ : X.IdealSheafData) Z = 0 := by
  have hstalk : IdealSheafData.stalk (⊥ : X.IdealSheafData) Z.genericPoint = ⊥ := by
    simp [IdealSheafData.stalk]
  have hdim : 0 < ringKrullDim (X.presheaf.stalk Z.genericPoint) := by
    rw [Z.ringKrullDim_stalk_genericPoint_eq_one]
    norm_num
  rw [effectiveCartierMultiplicity, hstalk,
    (AlgEquiv.quotientBot (X.presheaf.stalk Z.genericPoint)
      (X.presheaf.stalk Z.genericPoint)).toLinearEquiv.length_eq,
    length_self_eq_top_of_ringKrullDim_pos _ hdim]
  simp

/-- The order function of an arbitrary ideal sheaf on a Noetherian integral scheme is finitely
supported, so it is a finite formal linear combination of prime divisors.  A prime divisor with
nonzero order has its generic point in the support of the ideal sheaf, its own closed subset is
then an irreducible component of that support, and it is determined by that subset. -/
theorem effectiveCartierMultiplicity_support_finite [IsNoetherian X] [IsIntegral X]
    (I : X.IdealSheafData) :
    (Function.support (effectiveCartierMultiplicity I)).Finite := by
  classical
  by_cases hbot : I = ⊥
  · subst hbot
    simp [Function.support, effectiveCartierMultiplicity_bot]
  have hIproper : ((I.support : Closeds X) : Set X) ≠ Set.univ := fun h =>
    hbot (Scheme.IdealSheafData.support_eq_top_iff.mp (SetLike.coe_injective h))
  have : NoetherianSpace ((I.support : Closeds X) : Set X) :=
    NoetherianSpace.of_subset (Set.subset_univ ((I.support : Closeds X) : Set X))
  have : Finite (irreducibleComponents ((I.support : Closeds X) : Set X)) :=
    NoetherianSpace.finite_irreducibleComponents
  set S : Type u := {Z : PrimeDivisor X // effectiveCartierMultiplicity I Z ≠ 0}
  have hmem (Z : S) : Z.1.genericPoint ∈ ((I.support : Closeds X) : Set X) := by
    by_contra hnot
    exact Z.2 (effectiveCartierMultiplicity_eq_zero_of_notMem_support I Z.1 hnot)
  have key (Z : S) : ∃ C : irreducibleComponents ((I.support : Closeds X) : Set X),
      Subtype.val '' (C.1 : Set ((I.support : Closeds X) : Set X)) =
        (Z.1.support : Set X) := by
    obtain ⟨C, hC, hyC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure ({(⟨Z.1.genericPoint, hmem Z⟩ : ((I.support : Closeds X) : Set X))} : Set _))
      (isIrreducible_iff_closure.mpr isIrreducible_singleton)
    have hCclosed : IsClosed C := isClosed_of_mem_irreducibleComponents _ hC
    have hiClosed := (I.support : Closeds X).2.isClosedEmbedding_subtypeVal
    refine ⟨⟨C, hC⟩, (Z.1.support_eq_of_isIrreducible (hiClosed.isClosedMap _ hCclosed)
      (IsIrreducible.image hC.1 _ hiClosed.continuous.continuousOn)
      (D := ((I.support : Closeds X) : Set X)) (fun _ ⟨y, _, hy⟩ => hy ▸ y.property)
      ⟨_, hyC (subset_closure rfl), rfl⟩ hIproper)⟩
  choose c hc using key
  have hinj : Function.Injective c := fun Z W hZW =>
    Subtype.ext (PrimeDivisor.eq_of_support_eq ((hc Z).symm.trans (hZW ▸ hc W)))
  have : Finite S := Finite.of_injective c hinj
  exact Set.Finite.subset (Set.finite_range (Subtype.val : S → PrimeDivisor X))
    fun Z hZ => ⟨⟨Z, hZ⟩, rfl⟩

/-! ### Finite length at a prime divisor -/

/-- The local quotient of an effective Cartier divisor at a prime divisor has finite length:
the divisor is cut out near the generic point by a nonzerodivisor `f`, the local ring is
Noetherian of dimension one, so `𝒪_{X, Z} / (f)` has finite length by Tag 02MD, and the local
quotient is a quotient of it.  This is what makes the conversion to an integer in
`AlgebraicGeometry.effectiveCartierMultiplicity` lose no information. -/
@[ega "IV 21.6.5" "O_{Y(D), special case"]
theorem length_quotient_idealSheafStalk_ne_top [IsNoetherian X] [IsIntegral X]
    {I : X.IdealSheafData} (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (Z : PrimeDivisor X) :
    Module.length (X.presheaf.stalk Z.genericPoint)
      ((X.presheaf.stalk Z.genericPoint) ⧸ IdealSheafData.stalk I Z.genericPoint) ≠ ⊤ := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk Z.genericPoint) :=
    Ring.krullDimLE_iff.mpr (Z.ringKrullDim_stalk_genericPoint_eq_one.le)
  obtain ⟨g, hJ, hg⟩ := exists_stalk_eq_span_of_isEffectiveCartierDivisor hI Z.genericPoint
  rw [hJ]
  exact Ring.ord_ne_top hg

/-! ### The Weil divisor of an effective Cartier divisor -/

/-- **Stacks 02AR part (5).** The Weil divisor `[D] = Σ v_Z(D) [Z]` of an effective Cartier
divisor on a Noetherian integral scheme.

The hypothesis is not used by the term — the coefficient family of an arbitrary ideal sheaf is
already finitely supported — but it is what makes the coefficients the orders of Tag 02AR,
since only for an effective Cartier divisor is the local length finite. -/
@[stacks 02AR "effective_cartier_weil_divisor"]
def effectiveCartierWeilDivisor [IsNoetherian X] [IsIntegral X] (I : X.IdealSheafData)
    (_hI : Stacks.Divisors.IsEffectiveCartierDivisor I) : WeilDivisor X :=
  ⟨effectiveCartierMultiplicity I,
    (mem_weilDivisor_iff_finite_support _).mpr
      (effectiveCartierMultiplicity_support_finite I)⟩

/-- **Stacks 02AR part (5).** The coefficient of `[D]` at a prime divisor is the order
`v_Z(D)`. -/
@[stacks 02AR "effective_cartier_weil_divisor"]
theorem effectiveCartierWeilDivisor_apply [IsNoetherian X] [IsIntegral X]
    (I : X.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (Z : PrimeDivisor X) :
    (effectiveCartierWeilDivisor I hI).1 Z = effectiveCartierMultiplicity I Z := rfl

/-- **Stacks 02AR part (5), clause (a).** The coefficient of `[D]` at a prime divisor whose
generic point lies outside `D` is zero. -/
@[stacks 02AR "effective_cartier_weil_divisor"]
theorem effectiveCartierWeilDivisor_apply_of_notMem_support [IsNoetherian X] [IsIntegral X]
    (I : X.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (Z : PrimeDivisor X) (hZ : Z.genericPoint ∉ I.support) :
    (effectiveCartierWeilDivisor I hI).1 Z = 0 :=
  effectiveCartierMultiplicity_eq_zero_of_notMem_support I Z hZ

/-- The coefficient of `[D]` at a prime divisor is the length of the quotient of the local ring
by any generator of the ideal `D` induces there. -/
theorem effectiveCartierWeilDivisor_apply_of_stalk_eq_span [IsNoetherian X] [IsIntegral X]
    (I : X.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (Z : PrimeDivisor X) (f : X.presheaf.stalk Z.genericPoint)
    (hf : IdealSheafData.stalk I Z.genericPoint = Ideal.span {f}) :
    (effectiveCartierWeilDivisor I hI).1 Z =
      ((Module.length (X.presheaf.stalk Z.genericPoint)
        ((X.presheaf.stalk Z.genericPoint) ⧸ Ideal.span {f})).toNat : ℤ) := by
  rw [effectiveCartierWeilDivisor_apply, effectiveCartierMultiplicity, hf]

/-- **Stacks 02AR part (5), clause (b).** When the generic point of `Z` lies in `D`, the
coefficient of `[D]` at `Z` is the length of `𝒪_{X, Z} / (f)` for the nonzerodivisor `f` that
defines `D` on an affine open neighbourhood of that generic point, as in part (4). -/
@[stacks 02AR "effective_cartier_weil_divisor"]
theorem effectiveCartierWeilDivisor_apply_of_ideal_eq_span [IsNoetherian X] [IsIntegral X]
    {I : X.IdealSheafData} (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (Z : PrimeDivisor X) {U : X.affineOpens} (hxU : Z.genericPoint ∈ U.1) {f : Γ(X, U.1)}
    (hf : I.ideal U = Ideal.span {f}) :
    (effectiveCartierWeilDivisor I hI).1 Z =
      ((Module.length (X.presheaf.stalk Z.genericPoint)
        ((X.presheaf.stalk Z.genericPoint) ⧸
          Ideal.span {(X.presheaf.germ U.1 Z.genericPoint hxU).hom f})).toNat : ℤ) :=
  effectiveCartierWeilDivisor_apply_of_stalk_eq_span I hI Z _
    (IdealSheafData.stalk_eq_span_germ_of_ideal_eq_span hxU hf)

/-- The Weil divisor of an effective Cartier divisor, read as a finite formal linear
combination of prime divisors through `AlgebraicGeometry.weilDivisorEquivFinsupp`. -/
theorem weilDivisorEquivFinsupp_effectiveCartierWeilDivisor [IsNoetherian X] [IsIntegral X]
    (I : X.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) :
    weilDivisorEquivFinsupp (effectiveCartierWeilDivisor I hI) =
      Finsupp.ofSupportFinite (effectiveCartierMultiplicity I)
        (effectiveCartierMultiplicity_support_finite I) := by
  ext Z; rfl

end AlgebraicGeometry

end
