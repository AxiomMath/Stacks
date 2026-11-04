module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GraphConstruction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPointChain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.DominatingBlowup
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.SpecialFiberComponentDimension

/-!
# A modification is an isomorphism over the punctured spectrum

In the vanishing situation of [Stacks, Tag 0AX8] — a two-dimensional Noetherian normal local
domain `A` with closed point `s` of `S = Spec(A)` and punctured spectrum `U = S ∖ {s}`, and a
modification `f : X ⟶ S` — the discussion following the situation records that `f` restricts
to an isomorphism `f⁻¹(U) ⟶ U`
(`AlgebraicGeometry.VanishingSituation.isIso_morphismRestrict_puncturedSpectrumOpen`). This file
proves the pointwise form of that statement, a neighbourhood of each point of `U` over which `f`
is an isomorphism, and the consequence for opens contained in `U`.

## Main results

* `AlgebraicGeometry.VanishingSituation.natTrdegFiber_eq_zero_of_ne_closedPoint`: a point of `X`
  not over `s` has residue field algebraic over that of its image.
* `AlgebraicGeometry.VanishingSituation.finite_preimage_singleton_of_ne_closedPoint`: the fibres
  of `f` away from `s` are finite.
* `AlgebraicGeometry.VanishingSituation.exists_isIso_morphismRestrict_of_ne_closedPoint`: `f` is
  an isomorphism over a neighbourhood of each point of `U`.
* `AlgebraicGeometry.VanishingSituation.isIso_morphismRestrict_of_le_puncturedSpectrumOpen`: the
  same over any open contained in `U`.

## Implementation notes

The local rings of `S` away from `s` have dimension at most one, so the dimension formula
[Stacks, Tag 0BAE] for the birational `f` leaves no room for transcendence in the residue field
extension at a point `x` over `y ≠ s`: either `x` is the generic point, over the generic point
whose local ring is a field, or `𝒪_{X,x}` has dimension at least one. A point of a scheme of
finite type over a field whose residue field is algebraic is closed, so every point of the fibre
`X_y` is closed; a Noetherian sober space all of whose points are closed is finite. Then `f` is
finite over a neighbourhood of `y` ([Stacks, Tag 02UP]), hence an isomorphism there
([Stacks, Tag 0AB1]).

## References

* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 0BAE](https://stacks.math.columbia.edu/tag/0BAE)
* [Stacks Project, Tag 02UP](https://stacks.math.columbia.edu/tag/02UP)
* [Stacks Project, Tag 0AB1](https://stacks.math.columbia.edu/tag/0AB1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace VanishingSituation

variable (V : VanishingSituation.{u})

/-- The local rings of the base away from its closed point have dimension at most one. -/
theorem ringKrullDim_stalk_base_le_one_of_ne_closedPoint (y : V.base) (hy : y ≠ V.closedPoint) :
    ringKrullDim (V.base.presheaf.stalk y) ≤ 1 := by
  have hsp : y ⤳ V.closedPoint := IsLocalRing.specializes_closedPoint (R := V.A) y
  have hlt : V.closedPoint < y :=
    lt_of_le_not_ge hsp fun h => hy (hsp.antisymm h).eq
  have hadd : Order.coheight y + 1 ≤ Order.coheight (V.closedPoint : V.base) :=
    Order.coheight_add_one_le hlt
  have h2 := V.ringKrullDim_stalk_base_le_two V.closedPoint
  rw [ringKrullDim_stalk_eq_coheight] at h2 ⊢
  have h2' : Order.coheight (V.closedPoint : V.base) ≤ 2 :=
    WithBot.coe_le_coe.mp (by simpa using h2)
  have h3 : Order.coheight y + 1 ≤ 1 + 1 := by
    rw [one_add_one_eq_two]
    exact hadd.trans h2'
  have h1 : Order.coheight y ≤ 1 := (ENat.add_le_add_iff_right ENat.one_ne_top).mp h3
  have h1' : ((Order.coheight y : ℕ∞) : WithBot ℕ∞) ≤ ((1 : ℕ∞) : WithBot ℕ∞) :=
    WithBot.coe_le_coe.mpr h1
  simpa using h1'

/-- **Away from the closed point the residue field extensions of `f` are algebraic.** The local
ring of the base at `f x` has dimension at most one, and the dimension formula
[Stacks, Tag 0BAE] for the birational `f` bounds `dim 𝒪_{X,x} + trdeg κ(x)/κ(f x)` by it: if `x`
is the generic point then so is `f x`, whose local ring is a field, and otherwise
`dim 𝒪_{X,x} ≥ 1`. -/
theorem natTrdegFiber_eq_zero_of_ne_closedPoint (x : V.X) (hx : V.f x ≠ V.closedPoint) :
    natTrdegFiber V.f x = 0 := by
  have hformula := ringKrullDim_stalk_add_residueFieldTranscendenceDegree_le V.f x
  rw [genericResidueFieldTranscendenceDegreeAt_eq_zero V.f V.modification.isBirational x]
    at hformula
  have key : residueFieldTranscendenceDegree V.f x = 0 := by
    obtain ⟨e, he⟩ : ∃ e : ℕ∞, e = residueFieldTranscendenceDegree V.f x := ⟨_, rfl⟩
    rw [← he] at hformula ⊢
    have hb : ∀ c : WithBot ℕ∞, c ≤ ringKrullDim (V.X.presheaf.stalk x) →
        c + (e : WithBot ℕ∞) ≤ ringKrullDim (V.base.presheaf.stalk (V.f x)) := fun c hc => by
      simpa using (add_le_add_left hc _).trans hformula
    by_cases hg : x = genericPoint V.X
    · have hfx : V.f x = genericPoint V.base := by
        rw [hg]
        exact IsBirational.genericPoint_eq V.f V.modification.isBirational
      have h0 : ringKrullDim (V.base.presheaf.stalk (V.f x)) = 0 := by
        rw [hfx, ringKrullDim_stalk_eq_coheight,
          Order.coheight_eq_zero.2 (isMax_genericPoint V.base)]
        rfl
      have := hb 0 Order.krullDim_nonneg
      rw [h0, zero_add] at this
      exact nonpos_iff_eq_zero.mp (by exact_mod_cast this)
    · have h1 := Stacks.LocalCohomology.one_le_ringKrullDim_stalk_of_ne_genericPoint _ hg
      have := (hb 1 h1).trans (V.ringKrullDim_stalk_base_le_one_of_ne_closedPoint (V.f x) hx)
      have h' : 1 + e ≤ 1 := by exact_mod_cast this
      have : e + 1 ≤ 0 + 1 := by simpa [add_comm] using h'
      exact nonpos_iff_eq_zero.mp ((ENat.add_le_add_iff_right ENat.one_ne_top).mp this)
  let _ : Algebra (V.base.residueField (V.f x)) (V.X.residueField x) :=
    (V.f.residueFieldMap x).hom.toAlgebra
  have htr : Algebra.trdeg (V.base.residueField (V.f x)) (V.X.residueField x) = 0 :=
    Cardinal.toENat_eq_zero.mp key
  rw [natTrdegFiber_eq_toNat_trdeg_residueField V.f x, htr]
  simp

/-- A point of `X` not over the closed point is a closed point of its fibre. -/
theorem isClosed_singleton_asFiber_of_ne_closedPoint (x : V.X) (hx : V.f x ≠ V.closedPoint) :
    IsClosed ({V.f.asFiber x} : Set (V.f.fiber (V.f x))) := by
  let k := V.base.residueField (V.f x)
  let g : V.f.fiber (V.f x) ⟶ Spec (.of k) := V.f.fiberToSpecResidueField (V.f x)
  have : LocallyOfFiniteType g := by
    change LocallyOfFiniteType (pullback.snd V.f (V.base.fromSpecResidueField (V.f x)))
    infer_instance
  exact isClosed_singleton_of_natTrdegResidueField_eq_zero k _ g (V.f.asFiber x)
    (V.natTrdegFiber_eq_zero_of_ne_closedPoint x hx)

/-- **The fibres of `f` away from the closed point are finite.** Every point of such a fibre is
closed in it, and a Noetherian sober space all of whose points are closed is finite: each of its
finitely many irreducible components is the closure of its generic point. -/
theorem finite_preimage_singleton_of_ne_closedPoint (y : V.base) (hy : y ≠ V.closedPoint) :
    (V.f ⁻¹' {y}).Finite := by
  let e := V.f.fiberHomeo y
  have hP : ∀ (x : V.X) (hx : V.f x ∈ ({y} : Set V.base)),
      IsClosed ({⟨x, hx⟩} : Set (V.f ⁻¹' {y})) := by
    rintro x rfl
    have hc := (V.f.fiberHomeo (V.f x)).isClosed_image.mpr
      (V.isClosed_singleton_asFiber_of_ne_closedPoint x hy)
    rw [Set.image_singleton] at hc
    convert hc using 2
    exact Subtype.ext (V.f.fiberι_asFiber x).symm
  have hT1 : T1Space (V.f.fiber y) := by
    refine ⟨fun t => ?_⟩
    have h := hP (e t).1 (e t).2
    have : ({t} : Set (V.f.fiber y)) = e ⁻¹' {e t} := by
      ext z
      simp
    rw [this]
    exact h.preimage e.continuous
  have : CompactSpace V.X := QuasiCompact.compactSpace_of_compactSpace V.f
  have : IsNoetherian V.X := {}
  have : NoetherianSpace (V.f.fiber y) :=
    (noetherianSpace_iff_of_homeomorph e).mpr inferInstance
  have hfin : Finite (V.f.fiber y) := by
    have hcomp : ∀ C ∈ irreducibleComponents (V.f.fiber y), C.Finite := by
      intro C hC
      have hcl := isClosed_of_mem_irreducibleComponents C hC
      have hgen := hC.1.isGenericPoint_genericPoint hcl
      rw [← hgen.def, closure_singleton]
      exact Set.finite_singleton _
    have huniv : (Set.univ : Set (V.f.fiber y)).Finite := by
      rw [← sUnion_irreducibleComponents]
      exact NoetherianSpace.finite_irreducibleComponents.sUnion hcomp
    exact Set.finite_univ_iff.mp huniv
  exact Set.finite_coe_iff.mp (e.finite_iff.mp hfin)

/-- **Away from the closed point, `f` is an isomorphism over a neighbourhood of each point.** It
is finite over a neighbourhood because the fibre is finite ([Stacks, Tag 02UP]), and a finite
birational morphism onto a normal integral scheme is an isomorphism ([Stacks, Tag 0AB1]). -/
theorem exists_isIso_morphismRestrict_of_ne_closedPoint (y : V.base) (hy : y ≠ V.closedPoint) :
    ∃ W : V.base.Opens, y ∈ W ∧ IsIso (V.f ∣_ W) := by
  obtain ⟨W, hyW, hW⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton V.f y
    (V.finite_preimage_singleton_of_ne_closedPoint y hy)
  refine ⟨W, hyW, ?_⟩
  have hgW : genericPoint V.base ∈ W :=
    ((genericPoint_spec V.base).mem_open_set_iff W.2).mpr ⟨y, trivial, hyW⟩
  have : Nonempty W := ⟨⟨_, hgW⟩⟩
  have : Nonempty (V.f ⁻¹ᵁ W) := ⟨⟨genericPoint V.X, by
    change V.f (genericPoint V.X) ∈ W
    rw [IsBirational.genericPoint_eq V.f V.modification.isBirational]
    exact hgW⟩⟩
  have hN : IsNormal V.base :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed V.A)
  exact isIso_of_isIntegralHom_of_isBirational_of_isNormal (V.f ∣_ W)
    (V.modification.isBirational.morphismRestrict W)

/-- The modification is an isomorphism over every open contained in the punctured spectrum. -/
theorem isIso_morphismRestrict_of_le_puncturedSpectrumOpen {W : V.base.Opens}
    (hW : W ≤ V.puncturedSpectrumOpen) : IsIso (V.f ∣_ W) :=
  isIso_morphismRestrict_of_le V.f hW V.isIso_morphismRestrict_puncturedSpectrumOpen

end VanishingSituation

end AlgebraicGeometry

end
