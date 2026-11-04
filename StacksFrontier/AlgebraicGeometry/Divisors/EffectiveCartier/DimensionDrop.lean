module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.Topology.Dimension.Krull

/-!
# An effective Cartier divisor drops the local dimension

Let `S` be a scheme and `D ⊆ S` an effective Cartier divisor.  At a point `s ∈ D` at which the
local dimension of `S` is finite, the local dimension of `D` is strictly smaller.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_subscheme_lt`: **Stacks Tag 056N.**

## The argument

Both local dimensions are computed on one affine chart.  Tag 01WS
(`Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal`) gives an affine open `V` around
`s` on which `D` is `Spec (A / (f))` with `A = Γ(S, V)` and `f` a nonzerodivisor, and
`topologicalKrullDimAt_isLeast` lets the local dimension of `S` at `s` be computed on a basic
open `D(g) ⊆ V` small enough to realise the infimum, where it is `dim A_g`.  The corresponding
chart for `D` is `Spec` of `(A/(f))_{g}`, whose dimension drops by at least one from `dim A_g`
because `A_g → (A/(f))_g` is a surjection killing the nonzerodivisor `f`
(`ringKrullDim_succ_le_of_surjective`).  Finiteness of `dim A_g` turns `d + 1 ≤ dim A_g` into
`d < dim A_g`.

## Implementation notes

Finiteness of the ambient local dimension is `topologicalKrullDimAt S s < ⊤`, matching the
`WithBot ℕ∞` codomain of `topologicalKrullDimAt`.  A point of `D` is a point of the closed
subscheme `I.subscheme`, and its image in `S` is its image under the closed immersion
`I.subschemeι`.

## References

* [Stacks Project, Tag 056N](https://stacks.math.columbia.edu/tag/056N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Divisors
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

private lemma ringKrullDim_away_quotient_succ_le {A : Type*} [CommRing A]
    (f g : A) (hf : f ∈ nonZeroDivisors A) :
    ringKrullDim (Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g)) + 1 ≤
      ringKrullDim (Localization.Away g) := by
  let J : Ideal A := Ideal.span {f}
  let m : A →+* A ⧸ J := Ideal.Quotient.mk J
  let R := Localization.Away g
  let T := Localization.Away (m g)
  let φ : R →+* T := Localization.awayMap m g
  have hsurj : Function.Surjective φ := by
    rw [IsLocalization.Away.map_surjective_iff]
    intro a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨b, 0, by simp [m]⟩
  have hfR : algebraMap A R f ∈ nonZeroDivisors R := by
    apply IsLocalization.map_nonZeroDivisors_le (Submonoid.powers g) R
    exact ⟨f, hf, rfl⟩
  have hφ : φ (algebraMap A R f) = 0 := by
    change (IsLocalization.Away.map R T m g) (algebraMap A R f) = 0
    rw [IsLocalization.Away.map, IsLocalization.map_eq]
    simp [m, J]
  exact ringKrullDim_succ_le_of_surjective φ hsurj hfR hφ

private lemma topologicalKrullDim_basicOpen_eq_ringKrullDim_away
    {A : Type*} [CommRing A] (g : A) (R : Type*) [CommRing R] [Algebra A R]
    [IsLocalization.Away g R] :
    topologicalKrullDim (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) =
      ringKrullDim R := by
  let e := (PrimeSpectrum.localization_away_isOpenEmbedding R g).isEmbedding.toHomeomorph
  rw [← PrimeSpectrum.localization_away_comap_range R g]
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).symm

/-- An effective Cartier divisor has smaller local dimension at every point where the ambient
local dimension is finite. -/
@[stacks 056N]
theorem topologicalKrullDimAt_subscheme_lt {X : Scheme.{u}}
    (I : X.IdealSheafData) (hI : IsEffectiveCartierDivisor I)
    (x : I.subscheme)
    (hfin : topologicalKrullDimAt X (I.subschemeι x) < ⊤) :
    topologicalKrullDimAt I.subscheme x <
      topologicalKrullDimAt X (I.subschemeι x) := by
  classical
  let s : X := I.subschemeι x
  have hs : s ∈ I.supportSet := by
    rw [Scheme.IdealSheafData.mem_supportSet_iff_mem_support]
    change s ∈ (I.support : Set X)
    rw [← I.range_subschemeι]
    exact Set.mem_range_self x
  obtain ⟨⟨O, hsO, hOopen, hOdim⟩, hOmin⟩ :=
    topologicalKrullDimAt_isLeast X s
  let O' : X.Opens := ⟨O, hOopen⟩
  obtain ⟨V, hV, hsV, f, hf, e, he⟩ :=
    (isEffectiveCartierDivisor_iff_affineLocal I).mp hI s hs
  obtain ⟨g, hgle, hsg⟩ := hV.exists_basicOpen_le (V := O') ⟨s, hsO⟩ hsV
  let W : X.Opens := X.basicOpen g
  have hWleO : W ≤ O' := hgle
  have hsW : s ∈ W := hsg
  have hWdim : topologicalKrullDim (W : Set X) =
      topologicalKrullDimAt X s := by
    apply le_antisymm
    · calc
        topologicalKrullDim (W : Set X) ≤ topologicalKrullDim (O' : Set X) :=
          (Topology.IsEmbedding.inclusion hWleO).isInducing.topologicalKrullDim_le
        _ = topologicalKrullDimAt X s := hOdim.symm
    · exact hOmin ⟨W, hsW, W.2, rfl⟩
  let A : Type u := Γ(X, V)
  let J : Ideal A := Ideal.span {f}
  let Q : Type u := A ⧸ J
  let m : A →+* Q := Ideal.Quotient.mk J
  let P := pullback I.subschemeι V.ι
  let hpull := Scheme.Pullback.exists_preimage_pullback
    (f := I.subschemeι) (g := V.ι) x ⟨s, hsV⟩ (by rfl)
  let z : P := Classical.choose hpull
  have hzfst : pullback.fst I.subschemeι V.ι z = x :=
    (Classical.choose_spec hpull).1
  have hzsnd : pullback.snd I.subschemeι V.ι z = ⟨s, hsV⟩ :=
    (Classical.choose_spec hpull).2
  let q : PrimeSpectrum Q := e.hom z
  have hpq : hV.isoSpec.hom ⟨s, hsV⟩ = PrimeSpectrum.comap m q := by
    have heval := congrArg (fun k : P ⟶ Spec (.of A) => k z) he
    change hV.isoSpec.hom (pullback.snd I.subschemeι V.ι z) =
      Spec.map (CommRingCat.ofHom m) (show Spec (.of Q) from e.hom z) at heval
    rw [hzsnd] at heval
    change hV.isoSpec.hom ⟨s, hsV⟩ = PrimeSpectrum.comap m q at heval
    exact heval
  let p : PrimeSpectrum A := hV.isoSpec.hom ⟨s, hsV⟩
  have hpg : g ∉ p.asIdeal := by
    apply (PrimeSpectrum.mem_basicOpen g p).mp
    rw [← hV.fromSpec_preimage_basicOpen]
    change hV.fromSpec p ∈ X.basicOpen g
    convert hsg using 1
    change (hV.isoSpec.hom ≫ hV.fromSpec) ⟨s, hsV⟩ = s
    rw [hV.isoSpec_hom_fromSpec]
    rfl
  have hpc : p.asIdeal = Ideal.comap m q.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hpq
  have hqg : m g ∉ q.asIdeal := by
    intro hmem
    apply hpg
    rw [hpc]
    exact Ideal.mem_comap.mpr hmem
  have hqbasic : q ∈ PrimeSpectrum.basicOpen (m g) :=
    (PrimeSpectrum.mem_basicOpen (m g) q).mpr hqg
  have hQlocal : topologicalKrullDimAt (Spec (.of Q)) q ≤
      topologicalKrullDim (PrimeSpectrum.basicOpen (m g) : Set (PrimeSpectrum Q)) := by
    exact (topologicalKrullDimAt_isLeast _ q).2
      ⟨_, hqbasic, PrimeSpectrum.isOpen_basicOpen, rfl⟩
  let T := Localization.Away (m g)
  let Waff : X.affineOpens := ⟨W, hV.basicOpen g⟩
  have hWV : W ≤ V := X.basicOpen_le g
  let i : W ⟶ V := homOfLE hWV
  let B : Type u := Γ(X, W)
  let _ : Algebra A B := (X.presheaf.map i.op).hom.toAlgebra
  let _ : IsLocalization.Away g B := hV.isLocalization_of_eq_basicOpen g i rfl
  let R := Localization.Away g
  let _ : Algebra A R := inferInstance
  let _ : IsLocalization.Away g R := inferInstance
  have hringDim : ringKrullDim T + 1 ≤ ringKrullDim R :=
    ringKrullDim_away_quotient_succ_le f g ((isRegular_iff_mem_nonZeroDivisors).mp hf)
  let eR : B ≃ₐ[A] R := IsLocalization.algEquiv (Submonoid.powers g) B R
  have hWring : topologicalKrullDim (W : Set X) = ringKrullDim R := by
    calc
      topologicalKrullDim (W : Set X) = topologicalKrullDim (PrimeSpectrum B) := by
        exact IsHomeomorph.topologicalKrullDim_eq _
          Waff.2.isoSpec.hom.homeomorph.isHomeomorph
      _ = ringKrullDim B := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim B
      _ = ringKrullDim R := ringKrullDim_eq_of_ringEquiv eR.toRingEquiv
  have hdiv : topologicalKrullDimAt I.subscheme x ≤ ringKrullDim T := by
    let j := pullback.fst I.subschemeι V.ι
    have _ : IsOpenImmersion j := inferInstance
    have hopen : Topology.IsOpenEmbedding j.base := j.isOpenEmbedding
    have hlocal : topologicalKrullDimAt I.subscheme x =
        topologicalKrullDimAt P z := by
      rw [← hzfst]
      exact hopen.topologicalKrullDimAt_eq z
    calc
      topologicalKrullDimAt I.subscheme x = topologicalKrullDimAt P z := hlocal
      _ = topologicalKrullDimAt (Spec (.of Q)) q :=
        topologicalKrullDimAt_eq_of_homeomorph e.hom.homeomorph z
      _ ≤ topologicalKrullDim (PrimeSpectrum.basicOpen (m g) : Set (PrimeSpectrum Q)) :=
        hQlocal
      _ = ringKrullDim T :=
        topologicalKrullDim_basicOpen_eq_ringKrullDim_away (m g) T
  have hRdim : ringKrullDim R = topologicalKrullDimAt X s := hWring.symm.trans hWdim
  have hRfinite : ringKrullDim R < ⊤ := hRdim ▸ hfin
  have hRne : ringKrullDim R ≠ ⊥ := by
    rw [hRdim, hOdim]
    intro hbot
    have hempty : IsEmpty O :=
      (topologicalKrullDim_eq_bot_iff_isEmpty O).mp hbot
    exact hempty.false ⟨s, hsO⟩
  have hstrict : ringKrullDim T < ringKrullDim R := by
    cases hR : ringKrullDim R with
    | bot =>
        exact (hRne hR).elim
    | coe n =>
        cases n with
        | top => exact (hRfinite.not_ge (by simp [hR])).elim
        | coe n =>
            have hh : ringKrullDim T + 1 ≤ (n : WithBot ℕ∞) := by
              simpa [hR] using hringDim
            exact ENat.WithBot.add_one_le_natCast_iff.mp hh
  calc
    topologicalKrullDimAt I.subscheme x ≤ ringKrullDim T := hdiv
    _ < ringKrullDim R := hstrict
    _ = topologicalKrullDimAt X s := hRdim

end AlgebraicGeometry

end
