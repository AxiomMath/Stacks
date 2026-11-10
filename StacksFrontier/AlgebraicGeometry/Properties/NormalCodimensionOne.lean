module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.DedekindBase
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Basic
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.GlobalSections
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs

/-!
# Local rings of an integral scheme inside its function field, and codimension one

Let `X` be an integral scheme with function field `K`. Every local ring `𝒪_{X, x}` is a subring
of `K`, and when `x` specializes to `y` the subring `𝒪_{X, y}` is contained in `𝒪_{X, x}`. This
file records that, and then proves the pointwise form of algebraic Hartogs for a normal
locally Noetherian integral scheme: an element of `K` lies in `𝒪_{X, x}` as soon as it lies in
`𝒪_{X, y}` for every point `y` of codimension one that specializes to `x`. At such a `y` the local
ring is a discrete valuation ring, and membership in it means that the order of vanishing
`AlgebraicGeometry.Scheme.ord` is nonnegative.

It also records that the global sections of an integral scheme proper over a field form a
field. This is the form in which a proper integral curve has no nonconstant functions.

## Main results

* `AlgebraicGeometry.Scheme.algebraMap_stalkSpecializes`: the specialization map
  `𝒪_{X, y} ⟶ 𝒪_{X, x}` is compatible with the maps to the function field.
* `AlgebraicGeometry.Scheme.stalkSpecializes_injective`: it is injective.
* `AlgebraicGeometry.Scheme.mem_maximalIdeal_of_stalkSpecializes_mem`: an element of `𝒪_{X, x}`
  vanishing at a generization of `x` vanishes at `x`.
* `AlgebraicGeometry.Scheme.range_algebraMap_stalk_le_of_specializes`: the subring `𝒪_{X, y}` of
  `K` is contained in `𝒪_{X, x}`.
* `AlgebraicGeometry.Scheme.exists_globalSection_of_forall_mem_range_stalk`: an element of the
  function field lying in every local ring is a global function.
* `AlgebraicGeometry.Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord`: at a point of
  codimension one of a normal locally Noetherian integral scheme, a nonzero element of `K` lies
  in the local ring exactly when its order of vanishing there is nonnegative.
* `AlgebraicGeometry.Scheme.valuationAt`, `valuationAt_le_one_iff`,
  `valuationAt_algebraMap_lt_one_iff`: the valuation of the function field at a point of
  codimension one, and membership in the local ring and its maximal ideal read off from it.
* `AlgebraicGeometry.Scheme.mem_range_algebraMap_stalk_of_forall_coheight_eq_one`: **algebraic
  Hartogs at a point.** An element of `K` lying in `𝒪_{X, y}` for every codimension-one
  generization `y` of `x` lies in `𝒪_{X, x}`.
* `AlgebraicGeometry.Scheme.mem_range_algebraMap_stalk_of_forall_zero_le_ord`: the same, with
  the hypothesis read as nonnegativity of the order of vanishing.
* `AlgebraicGeometry.Scheme.isField_globalSections_of_isProper`: the global sections of an
  integral scheme proper over a field form a field.

## References

* [Stacks Project, Tag 031T](https://stacks.math.columbia.edu/tag/031T)
* [Stacks Project, Tag 00PD](https://stacks.math.columbia.edu/tag/00PD)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Order Topology
open scoped WithZero

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-! ### Local rings as subrings of the function field -/

/-- The specialization map `𝒪_{X, y} ⟶ 𝒪_{X, x}`, for `x` specializing to `y`, is compatible with
the maps of the two local rings to the function field. -/
theorem algebraMap_stalkSpecializes [IrreducibleSpace X] {x y : X} (h : x ⤳ y)
    (a : X.presheaf.stalk y) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.stalkSpecializes h a) =
      algebraMap (X.presheaf.stalk y) X.functionField a := by
  simp only [RingHom.algebraMap_toAlgebra]
  exact X.presheaf.stalkSpecializes_comp_apply _ h a

/-- On an integral scheme the specialization maps between local rings are injective. -/
alias stalkSpecializes_injective := AlgebraicGeometry.stalkSpecializes_injective_of_isIntegral

/-- On an irreducible scheme, if `x` specializes to `y`, then the image of `𝒪_{X, y}` in the
function field is contained in the image of `𝒪_{X, x}`. -/
theorem range_algebraMap_stalk_le_of_specializes [IrreducibleSpace X] {x y : X} (h : x ⤳ y) :
    (algebraMap (X.presheaf.stalk y) X.functionField).range ≤
      (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  rintro _ ⟨a, rfl⟩
  exact ⟨X.presheaf.stalkSpecializes h a, algebraMap_stalkSpecializes h a⟩

/-- An element of `𝒪_{X, x}` whose image in the local ring at a generization of `x` lies in the
maximal ideal there lies in the maximal ideal of `𝒪_{X, x}`: a unit stays a unit. -/
theorem mem_maximalIdeal_of_stalkSpecializes_mem {x y : X} (h : y ⤳ x)
    {c : X.presheaf.stalk x}
    (hc : X.presheaf.stalkSpecializes h c ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y)) :
    c ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  by_contra hcx
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hcx
  exact (IsLocalRing.mem_maximalIdeal _).mp hc
    (hcx.map (X.presheaf.stalkSpecializes h).hom)

/-- On an integral scheme an element of the function field lying in every local ring is the image
of a global function. -/
theorem exists_globalSection_of_forall_mem_range_stalk [IsIntegral X] {z : X.functionField}
    (h : ∀ x : X, z ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃ a : Γ(X, ⊤), X.presheaf.germ ⊤ (genericPoint X) trivial a = z := by
  classical
  have hgen (W : X.Opens) (hW : Nonempty W) : genericPoint X ∈ W :=
    ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr (by simpa using hW)
  choose c hc using h
  choose V hxV r hr using fun x => X.presheaf.exists_germ_eq (x := x) (c x)
  have hne (x : X) : Nonempty (V x) := ⟨⟨x, hxV x⟩⟩
  have hs : ∀ x : X, X.germToFunctionField (V x) (r x) = z := fun x => by
    have := hne x
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField X (hxV x), hr x, hc x]
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf V r := by
    intro x y
    have : Nonempty (V x ⊓ V y : X.Opens) := ⟨⟨genericPoint X, hgen _ (hne x), hgen _ (hne y)⟩⟩
    apply X.germToFunctionField_injective (V x ⊓ V y : X.Opens)
    rw [X.presheaf.germ_res_apply, X.presheaf.germ_res_apply]
    exact (hs x).trans (hs y).symm
  obtain ⟨t, ht, -⟩ :=
    X.sheaf.existsUnique_gluing' V ⊤ (fun _ => homOfLE le_top)
      (fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩) r hcompat
  refine ⟨t, ?_⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hres : X.presheaf.map (homOfLE (le_top : V x ≤ ⊤)).op t = r x := ht x
  rw [← X.presheaf.germ_res_apply (homOfLE (le_top : V x ≤ ⊤)) (genericPoint X)
    (hgen _ (hne x)) t, hres]
  exact hs x

/-! ### Codimension one -/

/-- Over a discrete valuation ring `R` with fraction field `K`, an element of `K` lies in `R`
exactly when its valuation is at most `1`. -/
private theorem mem_range_algebraMap_iff_valuation_le_one {R K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (z : K) :
    z ∈ (algebraMap R K).range ↔
      (IsDiscreteValuationRing.maximalIdeal R).valuation K z ≤ 1 :=
  ⟨by rintro ⟨a, rfl⟩; exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a,
    IsDiscreteValuationRing.exists_lift_of_le_one⟩

/-- At a point of codimension one of a normal locally Noetherian integral scheme, a nonzero
element of the function field lies in the local ring exactly when its order of vanishing there is
nonnegative. -/
theorem mem_range_algebraMap_stalk_iff_zero_le_ord [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {y : X} (hy : coheight y = 1) {z : X.functionField} (hz : z ≠ 0) :
    z ∈ (algebraMap (X.presheaf.stalk y) X.functionField).range ↔ 0 ≤ ord z y := by
  have : IsDiscreteValuationRing (X.presheaf.stalk y) :=
    Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk hy
  have : Ring.KrullDimLE 1 (X.presheaf.stalk y) := krullDimLE_of_coheight_le hy.le
  rw [le_ord_iff hy hz, show ordHom y hy z = Ring.ordFrac (X.presheaf.stalk y) z from rfl,
    ofAdd_zero, WithZero.coe_one, Ring.ordFrac_eq_valuation_inv]
  rw [one_le_inv₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hz))]
  exact mem_range_algebraMap_iff_valuation_le_one z

/-- The valuation of the function field at a point of codimension one of a normal locally
Noetherian integral scheme: the local ring there is a discrete valuation ring, and this is the
valuation of its maximal ideal, with values in `ℤᵐ⁰`. Elements of the local ring have valuation
at most `1`, and a uniformizer has valuation `exp (-1)`. -/
noncomputable def valuationAt [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (y : X)
    (hy : coheight y = 1) : Valuation X.functionField ℤᵐ⁰ :=
  letI := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk hy
  (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk y)).valuation X.functionField

/-- An element of the function field lies in the local ring at a point of codimension one
exactly when its valuation there is at most `1`. -/
theorem valuationAt_le_one_iff [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {y : X}
    (hy : coheight y = 1) (z : X.functionField) :
    valuationAt y hy z ≤ 1 ↔ z ∈ (algebraMap (X.presheaf.stalk y) X.functionField).range := by
  have := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk hy
  exact (mem_range_algebraMap_iff_valuation_le_one z).symm

/-- The image of an element of the local ring at a point of codimension one has valuation less
than `1` exactly when the element lies in the maximal ideal. -/
theorem valuationAt_algebraMap_lt_one_iff [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {y : X} (hy : coheight y = 1) (c : X.presheaf.stalk y) :
    valuationAt y hy (algebraMap (X.presheaf.stalk y) X.functionField c) < 1 ↔
      c ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
  have := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk hy
  exact IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ c

/-- The image of an element of the local ring at a point of codimension one which is not in the
maximal ideal has valuation `1`. -/
theorem valuationAt_algebraMap_eq_one [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {y : X} (hy : coheight y = 1) {c : X.presheaf.stalk y}
    (hc : c ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk y)) :
    valuationAt y hy (algebraMap (X.presheaf.stalk y) X.functionField c) = 1 :=
  le_antisymm ((valuationAt_le_one_iff hy _).mpr ⟨c, rfl⟩)
    (not_lt.mp fun h => hc ((valuationAt_algebraMap_lt_one_iff hy c).mp h))

/-- **Algebraic Hartogs at a point.** On a normal locally Noetherian integral scheme, an element of
the function field lying in the local ring at every point of codimension one that specializes to
`x` lies in the local ring at `x`. -/
theorem mem_range_algebraMap_stalk_of_forall_coheight_eq_one [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (x : X) {z : X.functionField}
    (h : ∀ y : X, coheight y = 1 → y ⤳ x →
      z ∈ (algebraMap (X.presheaf.stalk y) X.functionField).range) :
    z ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  obtain ⟨U, hU, hxU, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (x := x) (U := ⊤) trivial
  obtain ⟨xU, rfl⟩ : ∃ xU : U, (xU : X) = x := ⟨⟨x, hxU⟩, rfl⟩
  have : Nonempty U := ⟨xU⟩
  let p := hU.primeIdealOf xU
  have : IsLocalization.AtPrime (X.presheaf.stalk xU) p.asIdeal := hU.isLocalization_stalk xU
  have : IsIntegrallyClosed (X.presheaf.stalk xU) := IsNormal.stalk_normal _
  refine Set.mem_range.mpr
    (Stacks.AlgebraicGeometry.UnitsNormalProper.exists_algebraMap_eq_of_forall_height_eq_one
      (R := X.presheaf.stalk xU) X.functionField fun Q hQ => ?_)
  let q : PrimeSpectrum Γ(X, U) :=
    ⟨Q.asIdeal.comap (algebraMap Γ(X, U) (X.presheaf.stalk xU)), Ideal.comap_isPrime _ _⟩
  have hqh : q.asIdeal.height = 1 :=
    (IsLocalization.height_under p.asIdeal.primeCompl Q.asIdeal).trans hQ
  have hqp : q ≤ p := by
    change Q.asIdeal.comap _ ≤ p.asIdeal
    rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk xU) p.asIdeal]
    exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal Q.2.ne_top)
  let q' : ↥(Spec Γ(X, U)) := q
  have hround : hU.isoSpec.hom.base (hU.isoSpec.inv.base q') = q := by
    rw [← Scheme.Hom.comp_apply, hU.isoSpec.inv_hom_id]
    rfl
  obtain ⟨u, hpq⟩ : ∃ u : U, hU.primeIdealOf u = q := ⟨hU.isoSpec.inv.base q', hround⟩
  have hch : coheight (u : X) = 1 := by
    rw [show (u : X) = U.ι.base u from rfl,
      AlgebraicGeometry.coheight_eq_of_isOpenImmersion U.ι (x := u),
      ← AlgebraicGeometry.coheight_eq_of_isOpenImmersion hU.isoSpec.hom (x := u),
      ← AlgebraicGeometry.idealHeight_eq_coheight, show hU.isoSpec.hom.base u = q from hpq, hqh]
  have hsp : (u : X) ⤳ xU := by
    have h1 : hU.primeIdealOf u ⤳ hU.primeIdealOf xU :=
      hpq ▸ (PrimeSpectrum.le_iff_specializes q p).mp hqp
    have h2 := h1.map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf u, hU.fromSpec_primeIdealOf xU] at h2
  obtain ⟨a, hae⟩ := h u hch hsp
  have hloc := hU.isLocalization_stalk u
  obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.mk'_surjective (hU.primeIdealOf u).asIdeal.primeCompl a
  have hs : s.1 ∉ q.asIdeal := hpq ▸ s.2
  refine ⟨algebraMap Γ(X, U) (X.presheaf.stalk xU) b,
    algebraMap Γ(X, U) (X.presheaf.stalk xU) s.1, hs, ?_⟩
  have hbs' : IsLocalization.mk' (X.presheaf.stalk (u : X)) b s = a := hbs
  have hspec := IsLocalization.mk'_spec (X.presheaf.stalk (u : X)) b s
  rw [hbs'] at hspec
  have hcg := congrArg (algebraMap (X.presheaf.stalk (u : X)) X.functionField) hspec
  rw [map_mul, hae] at hcg
  rwa [← IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk xU) X.functionField,
    ← IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk xU) X.functionField,
    IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk (u : X)) X.functionField s.1,
    IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk (u : X)) X.functionField b]

/-- **Algebraic Hartogs at a point**, read through orders of vanishing. On a normal locally
Noetherian integral scheme, a nonzero element of the function field whose order of vanishing is
nonnegative at every point of codimension one specializing to `x` lies in the local ring at
`x`. -/
theorem mem_range_algebraMap_stalk_of_forall_zero_le_ord [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (x : X) {z : X.functionField} (hz : z ≠ 0)
    (h : ∀ y : X, coheight y = 1 → y ⤳ x → 0 ≤ ord z y) :
    z ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range :=
  mem_range_algebraMap_stalk_of_forall_coheight_eq_one x fun y hy hyx =>
    (mem_range_algebraMap_stalk_iff_zero_le_ord hy hz).mpr (h y hy hyx)

/-! ### Global sections of a proper integral scheme over a field -/

/-- The global sections of an integral scheme proper over a field form a field: they are a
domain integral over the field. -/
theorem isField_globalSections_of_isProper [IsIntegral X] {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] : IsField Γ(X, ⊤) := by
  have : IsDomain Γ(X, ⊤) :=
    Stacks.AlgebraicGeometry.UnitsNormalProper.isDomain_globalSections (X := X)
  let _ : Algebra k Γ(X, ⊤) :=
    (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom : k →+* Γ(X, ⊤)).toAlgebra
  have : Algebra.IsIntegral k Γ(X, ⊤) :=
    ⟨Stacks.AlgebraicGeometry.ProperGeomConnected.isIntegral_toSpecΓ_algebraMap f⟩
  exact isField_of_isIntegral_of_isField' (Field.toIsField k)

end AlgebraicGeometry.Scheme

end
