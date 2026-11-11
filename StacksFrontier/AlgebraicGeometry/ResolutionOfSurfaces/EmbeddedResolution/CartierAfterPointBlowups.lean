module

public import Mathlib.RingTheory.Ideal.Colon
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.CartierPart
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Difference
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.DivisorCover
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafColon
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain

/-!
# Turning a closed subscheme of a regular surface into an effective Cartier divisor

Let `X` be a regular Noetherian scheme of dimension two and let `Z ⊆ X` be a closed subscheme
which does not contain an irreducible component of `X`. Then there is a finite sequence of
blowups at closed points `Xₙ → … → X₁ → X` along which the inverse image of `Z` becomes an
effective Cartier divisor.

The sequence is the inductive predicate `Stacks.ResolutionOfSurfaces.PointBlowupChain`, so the
conclusion records that the morphism `Xₙ ⟶ X` really is a composite of blowups at closed points
and not merely some morphism with a Cartier inverse image.

## Main definitions

* `Stacks.ResolutionOfSurfaces.PointBlowupChain.mono` — a chain of blowups at points of a set is
  a chain of blowups at points of any larger set.

## Main results

* `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_comap_isEffectiveCartierDivisor` — the
  argument of [Stacks, Tag 0BIB](https://stacks.math.columbia.edu/tag/0BIB) for `Z` containing no
  irreducible component of `X`, with the principalization step taken as an argument. The
  registered form of Tag 0BIB is
  `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_comap_isEffectiveCartierDivisor_of_isRegular`
  in `StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierInverseImage`.
* `Stacks.ResolutionOfSurfaces.isNowhereDense_support_of_irreducibleSpace` — on an irreducible
  scheme a closed subscheme whose support is not everything does not contain a component, so the
  hypothesis of the previous result is the literal properness hypothesis of the source there.

## Implementation notes

The source reads "let `Z ⊂ X` be a proper closed subscheme", where *proper* means *not the whole
of `X`* (it is not a properness hypothesis on a morphism: `Z` is a subscheme, and the next lemma
in the source, Tag 0BIC, repeats the phrase with the same meaning). That hypothesis is taken here
in the form `IsNowhereDense (Z.support : Set X)`, i.e. `Z` contains no irreducible component of
`X`. The two readings agree when `X` is irreducible, which
`isNowhereDense_support_of_irreducibleSpace` records, and the literal reading is not enough in
general: for `X = 𝔸² ⊔ 𝔸²` and `Z` one of the two copies, `Z` is a closed subscheme different
from `X`, its ideal sheaf is zero on that copy, and so is the ideal sheaf of its inverse image
under any morphism — such a `Z` never becomes an effective Cartier divisor. Nowhere density is
also exactly what the two halves of Tag 0AGB consumed below ask for.

The scheme-theoretic inverse image of a closed subscheme along `f` is
`AlgebraicGeometry.Scheme.IdealSheafData.comap`, which Mathlib defines as the kernel of the
pullback of its closed immersion, and an effective Cartier divisor is
`Stacks.Divisors.IsEffectiveCartierDivisor`, invertibility of the ideal sheaf.

The proof is the one in the source. The largest effective Cartier divisor `E` inside `Z` is the
one supplied by the two halves of [Stacks, Tag 0AGB]: `E` agrees with `Z` outside a set of
codimension two, which on a two-dimensional scheme is a finite set of closed points. Writing
`Z = E · (Z : E)` with the ideal quotient `AlgebraicGeometry.Scheme.IdealSheafData.colon`, the
second factor is supported on that finite set, so [Stacks, Tag 0AHH] principalizes it along a
chain of blowups at closed points; the inverse image of `E` stays Cartier along that chain, and a
product of effective Cartier divisors is one.

The principalization step is the descent step of [Stacks, Tag 0AHH] (built on the local
splitting of [Stacks, Tag 0AGT]), taken here as the argument `descent` so that this module does
not import its proof. The library proves it (`Stacks.ResolutionOfSurfaces.pointBlowupDescent`),
and `exists_pointBlowupChain_comap_isEffectiveCartierDivisor_of_isRegular` in
`StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierInverseImage` is
Tag 0BIB with no such argument.

## References

* [Stacks Project, Tag 0BIB](https://stacks.math.columbia.edu/tag/0BIB)
* [Stacks Project, Tag 0AHH](https://stacks.math.columbia.edu/tag/0AHH)
* [Stacks Project, Tag 0AGB](https://stacks.math.columbia.edu/tag/0AGB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-! ### The ideal quotient by an effective Cartier divisor -/

private theorem fg_ideal {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (U : X.affineOpens) : (J.ideal U : Submodule Γ(X, U) Γ(X, U)).FG := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  exact Ideal.fg_of_isNoetherianRing _

/-- The ideal quotient `Z : E` on a locally Noetherian scheme, where the second argument is
finitely generated on every affine open because the scheme is locally Noetherian. -/
private def cartierQuotient {X : Scheme.{u}} [IsLocallyNoetherian X]
    (Z E : X.IdealSheafData) : X.IdealSheafData :=
  Z.colon E (fg_ideal E)

/-- If `E` is an effective Cartier divisor contained in `Z` then `Z` factors as `E · (Z : E)`.
This is `AlgebraicGeometry.mul_colon_eq_of_isEffectiveCartierDivisor`, read at the quotient
`cartierQuotient`, which differs from the one there only in the proof that `E` is finitely
generated on affine opens. -/
private theorem mul_cartierQuotient_eq {X : Scheme.{u}} [IsLocallyNoetherian X]
    {Z E : X.IdealSheafData} (hE : Stacks.Divisors.IsEffectiveCartierDivisor E)
    (hZE : Z ≤ E) : E * cartierQuotient Z E = Z :=
  AlgebraicGeometry.mul_colon_eq_of_isEffectiveCartierDivisor E Z hE hZE

/-- Two ideal sheaves with the same inverse image on an open have the same sections on every
affine open contained in it. -/
private theorem ideal_eq_of_comap_eq {X : Scheme.{u}} (I J : X.IdealSheafData) {U : X.Opens}
    (h : I.comap U.ι = J.comap U.ι) (V : X.affineOpens) (hVU : V.1 ≤ U) :
    I.ideal V = J.ideal V := by
  have hV : I.comap V.1.ι = J.comap V.1.ι := by
    have := congrArg (fun K => K.comap (X.homOfLE hVU)) h
    simpa only [← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι] using this
  have hv := congrArg
    (fun K : V.1.toScheme.IdealSheafData => K.ideal ⟨⊤, isAffineOpen_top _⟩) hV
  exact eq_of_heq ((Stacks.Divisors.ideal_comap_top_heq I V).symm.trans
    ((heq_of_eq hv).trans (Stacks.Divisors.ideal_comap_top_heq J V)))

/-- The ideal quotient `Z : E` is the unit ideal wherever `Z` and `E` agree, so its support is
contained in the part of the support of `Z` lying outside such an open. -/
private theorem support_cartierQuotient_subset {X : Scheme.{u}} [IsLocallyNoetherian X]
    (Z E : X.IdealSheafData) (U : X.Opens) (h : Z.comap U.ι = E.comap U.ι) :
    ((cartierQuotient Z E).support : Set X) ⊆ (Z.support : Set X) \ (U : Set X) := by
  intro x hx
  refine ⟨Scheme.IdealSheafData.support_antitone
    (show Z ≤ cartierQuotient Z E from fun _ => Ideal.le_colon) hx, ?_⟩
  intro hxU
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
  have heq := ideal_eq_of_comap_eq Z E h ⟨V, hV⟩ hVU
  have htop : (cartierQuotient Z E).ideal ⟨V, hV⟩ = ⊤ := by
    refine (Ideal.eq_top_iff_one _).mpr ?_
    change (1 : Γ(X, V)) ∈
      (Z.ideal ⟨V, hV⟩).colon ((E.ideal ⟨V, hV⟩ : Ideal Γ(X, V)) : Set Γ(X, V))
    rw [heq, Submodule.mem_colon]
    intro a ha
    simpa using ha
  have hzero := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hxV).mp hx
  rw [htop] at hzero
  exact (X.mem_zeroLocus_iff _ _).mp hzero 1 (by trivial) (by simpa using hxV)

/-! ### Points of codimension two on a two-dimensional scheme -/

private theorem ringKrullDim_stalk_le {X : Scheme.{u}} (hdim : topologicalKrullDim X = 2)
    (x : X) : ringKrullDim (X.presheaf.stalk x) ≤ 2 :=
  le_of_le_of_eq (le_iSup (fun y : X => ringKrullDim (X.presheaf.stalk y)) x)
    (by rw [← topologicalKrullDim_eq_iSup_krullDimOfRing_stalk, hdim])

private theorem coheight_eq_codimension {X : Scheme.{u}} (x : X) :
    letI : PartialOrder X := specializationOrder X
    codimension (IrreducibleCloseds.closureSingleton x) = Order.coheight x := by
  let _ : PartialOrder X := specializationOrder X
  rw [codimension_eq_coheight]
  have h : (irreducibleSetEquivPoints (α := X)).symm x =
      IrreducibleCloseds.closureSingleton x := IrreducibleCloseds.ext rfl
  rw [← h, Order.coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm]

/-- On a scheme of dimension two a point of codimension two has a two-dimensional local ring. -/
private theorem ringKrullDim_stalk_eq_two {X : Scheme.{u}} (hdim : topologicalKrullDim X = 2)
    (x : X) (hx : (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) :
    ringKrullDim (X.presheaf.stalk x) = 2 := by
  let _ : PartialOrder X := specializationOrder X
  refine le_antisymm (ringKrullDim_stalk_le hdim x) ?_
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, ← coheight_eq_codimension x]
  exact WithBot.coe_le_coe.mpr hx

/-- On a scheme of dimension two a point of codimension two is a closed point: a strictly
larger point would have coheight at least three. -/
private theorem isClosed_singleton_of_codimension_two {X : Scheme.{u}}
    (hdim : topologicalKrullDim X = 2) (x : X)
    (hx : (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) :
    IsClosed ({x} : Set X) := by
  let _ : PartialOrder X := specializationOrder X
  have hco : (Order.coheight x : WithBot ℕ∞) = 2 := by
    rw [← AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
    exact ringKrullDim_stalk_eq_two hdim x hx
  have hclosure : closure ({x} : Set X) = {x} := by
    refine Set.Subset.antisymm (fun y hy => ?_) subset_closure
    have hyx : y ≤ x := by
      rw [Scheme.le_iff_specializes, specializes_iff_mem_closure]
      exact hy
    by_contra hne
    have hnot : ¬ x ≤ y := fun hxy =>
      hne ((inseparable_iff_specializes_and.mpr
        ⟨Scheme.le_iff_specializes.mp hyx, Scheme.le_iff_specializes.mp hxy⟩).eq.symm)
    have hstep : (2 : WithBot ℕ∞) + 1 ≤ (Order.coheight y : WithBot ℕ∞) := by
      simpa [hco] using
        (WithBot.coe_le_coe.mpr (Order.coheight_add_one_le (lt_of_le_not_ge hyx hnot)))
    have hbound : (Order.coheight y : WithBot ℕ∞) ≤ 2 := by
      rw [← AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
      exact ringKrullDim_stalk_le hdim y
    have : (2 : WithBot ℕ∞) + 1 ≤ 2 := hstep.trans hbound
    norm_num at this
  exact closure_subset_iff_isClosed.mp hclosure.subset

/-- A closed set of closed points in a Noetherian sober space is finite. -/
private theorem finite_of_forall_isClosed_singleton {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [QuasiSober X] {T : Set X} (hT : IsClosed T)
    (hclosed : ∀ x ∈ T, IsClosed ({x} : Set X)) : T.Finite := by
  obtain ⟨S, hS, hc, hi, hcov⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  rw [hcov]
  refine hS.sUnion fun s hs => ?_
  obtain ⟨x, hx⟩ := QuasiSober.sober (hi s hs) (hc s hs)
  have hxT : x ∈ T := hcov ▸ Set.mem_sUnion.mpr ⟨s, hs, hx.mem⟩
  rw [← hx.def, (hclosed x hxT).closure_eq]
  exact Set.finite_singleton x

/-! ### Monotonicity of a chain of blowups in its set of centres -/

/-- A sequence of blowups at closed points lying over `T` is one lying over any larger set. -/
public theorem PointBlowupChain.mono {X Y : Scheme.{u}} {T T' : Set X} {f : Y ⟶ X}
    (h : T ⊆ T') (hf : PointBlowupChain X T Y f) : PointBlowupChain X T' Y f := by
  induction hf with
  | refl => exact .refl
  | step hh w hw hwT ih => exact ih.step w hw (h hwT)

/-! ### Turning a closed subscheme into an effective Cartier divisor -/

/-- The argument of [Stacks, Tag 0BIB]: let `X` be a regular Noetherian scheme of dimension `2`
and let `Z ⊆ X` be a closed subscheme containing no irreducible component of `X`. Then there is a
sequence `Xₙ → … → X₁ → X` of blowups at closed points such that the inverse image `Zₙ` of `Z` in
`Xₙ` is an effective Cartier divisor.

The first argument is the descent step of [Stacks, Tag 0AHH], which the library proves as
`Stacks.ResolutionOfSurfaces.pointBlowupDescent`. Tag 0BIB itself, with no such argument, is
`exists_pointBlowupChain_comap_isEffectiveCartierDivisor_of_isRegular`. -/
public theorem exists_pointBlowupChain_comap_isEffectiveCartierDivisor
    (descent : ∀ (Y : Scheme.{u}) (S : Finset Y) (J : Y.IdealSheafData),
      (∀ y ∈ S, IsClosed ({y} : Set Y)) →
      (∀ y ∈ S, IsRegularLocalRing (Y.presheaf.stalk y)) →
      (∀ y ∈ S, ringKrullDim (Y.presheaf.stalk y) = 2) →
      (J.support : Set Y) ⊆ (S : Set Y) →
      ∀ y ∈ (J.support : Set Y), ∀ hy : IsClosed ({y} : Set Y),
      ∀ M : Y.IdealSheafData, M = Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩ →
        ∃ (d : ℕ) (S' : Finset (blowUp M)) (J' : (blowUp M).IdealSheafData),
          exceptionalIdeal M ^ d * J' = J.comap (blowUpToBase M) ∧
          (∀ z ∈ S', IsClosed ({z} : Set (blowUp M))) ∧
          (∀ z ∈ S', IsRegularLocalRing ((blowUp M).presheaf.stalk z)) ∧
          (∀ z ∈ S', ringKrullDim ((blowUp M).presheaf.stalk z) = 2) ∧
          (J'.support : Set (blowUp M)) ⊆ (S' : Set (blowUp M)) ∧
          (∀ z ∈ S', (blowUpToBase M).base z ∈ S) ∧
          totalColength J' S' < totalColength J S)
    (X : Scheme.{u}) [IsNoetherian X] (hX : AlgebraicGeometry.IsRegular X)
    (hdim : topologicalKrullDim X = 2) (Z : X.IdealSheafData)
    (hZ : IsNowhereDense (Z.support : Set X)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), PointBlowupChain X Set.univ Y f ∧
      Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap f) := by
  classical
  obtain ⟨D, Z', hD, hZ', hcover⟩ :=
    AlgebraicGeometry.exists_integral_effectiveCartierDivisors_cover X Z hZ (Or.inr hX)
  have hcover' : (Z.support : Set X) ⊆
      (Z' : Set X) ∪ ⋃ I : D, ((I.1 : X.IdealSheafData).support : Set X) := by
    simpa only [Set.iUnion_subtype] using hcover
  obtain ⟨a, hE, hZE, U, hU, hcodim⟩ :=
    AlgebraicGeometry.exists_effectiveCartierDivisor_agree_off_codimension_two X Z
      (fun I : D => (I.1 : X.IdealSheafData)) Z' (fun I => hD I.1 I.2) hZ' hcover'
  set E : X.IdealSheafData := a.prod fun I n => (I.1 : X.IdealSheafData) ^ n with hEdef
  have hfactor : E * cartierQuotient Z E = Z := mul_cartierQuotient_eq hE hZE
  have hpoints : ∀ x ∈ (Z.support : Set X) \ (U : Set X), IsClosed ({x} : Set X) :=
    fun x hx => isClosed_singleton_of_codimension_two hdim x (hcodim x hx.1 hx.2)
  have hfinite : ((Z.support : Set X) \ (U : Set X)).Finite :=
    finite_of_forall_isClosed_singleton
      (Z.support.isClosed.inter U.isOpen.isClosed_compl) hpoints
  have hstalkPair : IsLocallyNoetherian X ∧ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    ((AlgebraicGeometry.isRegular_tfae X).out 1 2 (by simp) (by simp)).mp hX
  have hstalk : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := hstalkPair.2
  obtain ⟨Y, f, hchain, hQ⟩ :=
    exists_pointBlowupChain_isEffectiveCartierDivisor descent hfinite.toFinset
      (fun x hx => hpoints x (hfinite.mem_toFinset.mp hx))
      (fun x _ => hstalk x)
      (fun x hx => by
        have hx' := hfinite.mem_toFinset.mp hx
        exact ringKrullDim_stalk_eq_two hdim x (hcodim x hx'.1 hx'.2))
      (cartierQuotient Z E)
      (by
        rw [hfinite.coe_toFinset]
        exact support_cartierQuotient_subset Z E U hU.symm)
  refine ⟨Y, f, hchain.mono (Set.subset_univ _), ?_⟩
  rw [← hfactor, AlgebraicGeometry.comap_mul]
  exact AlgebraicGeometry.isEffectiveCartierDivisor_mul _ _
    (hchain.isEffectiveCartierDivisor_comap hE) hQ

/-- On an irreducible scheme a closed subscheme whose support is not the whole space contains no
irreducible component, since the complement of its support is a nonempty open and so is dense.
This is the literal reading of the source's "proper closed subscheme" in the only case in which
the source statement is true for it. -/
public theorem isNowhereDense_support_of_irreducibleSpace {X : Scheme.{u}} [IrreducibleSpace X]
    (Z : X.IdealSheafData) (hZ : (Z.support : Set X) ≠ Set.univ) :
    IsNowhereDense (Z.support : Set X) := by
  rw [Z.support.isClosed.isNowhereDense_iff, interior_eq_empty_iff_dense_compl]
  exact Z.support.isClosed.isOpen_compl.dense (Set.nonempty_compl.mpr hZ)

end Stacks.ResolutionOfSurfaces

end
