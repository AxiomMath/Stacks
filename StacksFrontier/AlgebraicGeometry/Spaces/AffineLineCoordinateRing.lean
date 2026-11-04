module

public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.NonvanishingLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolution
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionNotSeparated

/-!
# The coordinate ring of the affine line and of its puncture

Let `k` be a field. The ring of global functions of the affine line `𝔸¹_k` of
`AlgebraicGeometry.AffineLineInvolution.affineLine` is the polynomial ring `k[t]` in its standard
coordinate `t`, and that of the punctured line `𝔸¹_k ∖ {0}` is `k[t, t⁻¹]`. Both rings are
principal ideal domains, the points of coheight one of the affine line are its closed points, and
the origin is the unique point outside the puncture.

## Main definitions

* `AlgebraicGeometry.AffineLineInvolution.coordinate` is the standard coordinate `t`.
* `AlgebraicGeometry.AffineLineInvolution.polynomialRingEquiv` is the isomorphism
  `k[t] ≃ Γ(𝔸¹_k, 𝒪)` sending the variable to `t`.
* `AlgebraicGeometry.AffineLineInvolution.puncturedRestriction` is the restriction of functions to
  the punctured line, and `AlgebraicGeometry.AffineLineInvolution.origin` is the origin.

## Main results

* `IsLocalization.isPrincipalIdealRing`: a localization of a principal ideal ring is one.
* `Ring.ord_eq_one_of_span_eq_maximalIdeal`: a generator of the maximal ideal of a local ring has
  order of vanishing one.
* For an integral affine scheme `Y` whose ring of functions is a principal ideal domain:
  `AlgebraicGeometry.coheight_eq_height_primeIdealOf`,
  `AlgebraicGeometry.eq_of_mem_primeIdealOf` and
  `AlgebraicGeometry.ord_germ_eq_one_of_primeIdealOf_eq_span`.
* `AlgebraicGeometry.AffineLineInvolution.irreducible_coordinate` and
  `AlgebraicGeometry.AffineLineInvolution.isMaximal_span_coordinate`: `t` is irreducible and
  generates a maximal ideal.
* `AlgebraicGeometry.AffineLineInvolution.isLocalization_puncturedRestriction`: the functions on
  the punctured line are those on the line with `t` inverted.
* `AlgebraicGeometry.AffineLineInvolution.exists_eq_div_puncturedRestriction`: every rational
  function on the punctured line is a quotient of polynomials.
* `AlgebraicGeometry.AffineLineInvolution.eq_of_notMem_puncturedAffineLineOpen`,
  `AlgebraicGeometry.AffineLineInvolution.coheight_origin` and
  `AlgebraicGeometry.AffineLineInvolution.isClosed_singleton_iff_coheight_eq_one`: the origin is
  the only point outside the puncture, it has coheight one, and the closed points of the affine
  line are its points of coheight one.
* `AlgebraicGeometry.AffineLineInvolution.topologicalKrullDim_affineLine`: `dim 𝔸¹_k = 1`.
-/

@[expose] public section

open CategoryTheory

universe u

/-- A localization of a principal ideal ring is a principal ideal ring. -/
theorem IsLocalization.isPrincipalIdealRing {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] [IsPrincipalIdealRing R] : IsPrincipalIdealRing S := by
  refine ⟨fun I => ?_⟩
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (I.comap (algebraMap R S))).principal
  refine ⟨⟨algebraMap R S g, ?_⟩⟩
  rw [← IsLocalization.map_comap M S I, show Ideal.under R I = Ideal.span {g} from hg,
    Ideal.map_span, Set.image_singleton]

/-- In a local ring, an element generating the maximal ideal has order of vanishing one. -/
theorem Ring.ord_eq_one_of_span_eq_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] {x : R}
    (h : Ideal.span {x} = IsLocalRing.maximalIdeal R) : Ring.ord R x = 1 := by
  rw [Ring.ord, Module.length_eq_one_iff, h,
    isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
      (S := R ⧸ IsLocalRing.maximalIdeal R) Ideal.Quotient.mk_surjective]
  let := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  exact instIsSimpleModule _

namespace AlgebraicGeometry

/-- Two points of an affine scheme with the same prime ideal of global functions coincide. -/
private theorem eq_of_asIdeal_primeIdealOf_eq {Y : Scheme.{u}} [IsAffine Y] {q q' : Y}
    (h : ((isAffineOpen_top Y).primeIdealOf ⟨q, trivial⟩).asIdeal =
      ((isAffineOpen_top Y).primeIdealOf ⟨q', trivial⟩).asIdeal) : q = q' := by
  have h' := (isAffineOpen_top Y).fromSpec_primeIdealOf ⟨q, trivial⟩
  rw [PrimeSpectrum.ext h, (isAffineOpen_top Y).fromSpec_primeIdealOf ⟨q', trivial⟩] at h'
  exact h'.symm

/-! ### Points of codimension one of an affine scheme with principal ring of functions -/

section PrincipalAffine

open Order

variable {Y : Scheme.{u}} [IsAffine Y] [IsIntegral Y] [IsPrincipalIdealRing Γ(Y, ⊤)]

omit [IsIntegral Y] [IsPrincipalIdealRing Γ(Y, ⊤)] in
/-- The coheight of a point of an affine scheme is the height of its prime ideal. -/
theorem coheight_eq_height_primeIdealOf (q : Y) :
    (coheight q : WithBot ℕ∞) =
      ((isAffineOpen_top Y).primeIdealOf ⟨q, trivial⟩).asIdeal.height := by
  let : Algebra Γ(Y, ⊤) (Y.presheaf.stalk q) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf (U := ⊤) ⟨q, trivial⟩
  have : IsLocalization.AtPrime (Y.presheaf.stalk q)
      ((isAffineOpen_top Y).primeIdealOf ⟨q, trivial⟩).asIdeal :=
    (isAffineOpen_top Y).isLocalization_stalk ⟨q, trivial⟩
  rw [← ringKrullDim_stalk_eq_coheight q]
  exact IsLocalization.AtPrime.ringKrullDim_eq_height
    ((isAffineOpen_top Y).primeIdealOf ⟨q, trivial⟩).asIdeal (Y.presheaf.stalk q)

omit [IsIntegral Y] [IsPrincipalIdealRing Γ(Y, ⊤)] in
/-- The prime ideal of a point of coheight one of an affine scheme has height one. -/
theorem height_primeIdealOf_eq_one {q : Y} (hq : coheight q = 1) :
    ((isAffineOpen_top Y).primeIdealOf ⟨q, trivial⟩).asIdeal.height = 1 := by
  have h := coheight_eq_height_primeIdealOf q
  rw [hq] at h
  exact_mod_cast h.symm

/-- The prime ideal of a point of coheight one of an integral affine scheme whose ring of
functions is a principal ideal domain is maximal. -/
theorem isMaximal_primeIdealOf {q : Y} (hq : coheight q = 1) :
    ((isAffineOpen_top Y).primeIdealOf ⟨q, trivial⟩).asIdeal.IsMaximal := by
  refine IsPrime.to_maximal_ideal fun hbot => ?_
  have h := height_primeIdealOf_eq_one hq
  rw [hbot, Ideal.height_bot] at h
  exact zero_ne_one h

/-- Two points of coheight one of an integral affine scheme with principal ring of functions,
the second of whose prime ideals contains the generator of the first, coincide. -/
theorem eq_of_mem_primeIdealOf {q q' : Y} (hq : coheight q = 1)
    {a : Γ(Y, ⊤)} (ha : ((isAffineOpen_top Y).primeIdealOf ⟨q, trivial⟩).asIdeal = Ideal.span {a})
    (hmem : a ∈ ((isAffineOpen_top Y).primeIdealOf ⟨q', trivial⟩).asIdeal) : q = q' := by
  have hle : ((isAffineOpen_top Y).primeIdealOf ⟨q, trivial⟩).asIdeal ≤
      ((isAffineOpen_top Y).primeIdealOf ⟨q', trivial⟩).asIdeal := by
    rwa [ha, Ideal.span_singleton_le_iff_mem]
  exact eq_of_asIdeal_primeIdealOf_eq ((isMaximal_primeIdealOf hq).eq_of_le
    ((isAffineOpen_top Y).primeIdealOf ⟨q', trivial⟩).isPrime.ne_top hle)

omit [IsIntegral Y] [IsPrincipalIdealRing Γ(Y, ⊤)] in
/-- A generator of the prime ideal of a point of an affine scheme has order of vanishing one in
the stalk at that point. -/
theorem ord_germ_eq_one_of_primeIdealOf_eq_span {q : Y}
    {a : Γ(Y, ⊤)} (ha : ((isAffineOpen_top Y).primeIdealOf ⟨q, trivial⟩).asIdeal = Ideal.span {a}) :
    Ring.ord (Y.presheaf.stalk q) (Y.presheaf.germ ⊤ q trivial a) = 1 := by
  let : Algebra Γ(Y, ⊤) (Y.presheaf.stalk q) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf (U := ⊤) ⟨q, trivial⟩
  have : IsLocalization.AtPrime (Y.presheaf.stalk q)
      ((isAffineOpen_top Y).primeIdealOf ⟨q, trivial⟩).asIdeal :=
    (isAffineOpen_top Y).isLocalization_stalk ⟨q, trivial⟩
  refine Ring.ord_eq_one_of_span_eq_maximalIdeal ?_
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
    ((isAffineOpen_top Y).primeIdealOf ⟨q, trivial⟩).asIdeal (Y.presheaf.stalk q), ha,
    Ideal.map_span, Set.image_singleton]
  rfl

end PrincipalAffine

namespace AffineLineInvolution

variable (k : Type u) [Field k]

/-- The standard coordinate `t` of the affine line. -/
noncomputable abbrev coordinate : Γ((affineLine k).left, ⊤) :=
  AffineSpace.coord (Spec (.of k)) PUnit.unit

/-- The ring of global functions of the affine line is the multivariable polynomial ring in one
variable, read through the isomorphism of `𝔸¹_k` with `Spec k[t]`. -/
noncomputable def globalSectionsEquiv :
    Γ((affineLine k).left, ⊤) ≃+* MvPolynomial PUnit.{u + 1} k :=
  ((Scheme.Γ.mapIso (AffineSpace.SpecIso PUnit.{u + 1} (.of k)).op).symm ≪≫
    Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv

/-- `globalSectionsEquiv` is the composite of pulling back along `𝔸¹_k ≅ Spec k[t]` with the
identification of the global sections of `Spec k[t]` with `k[t]`. -/
theorem globalSectionsEquiv_apply (x : Γ((affineLine k).left, ⊤)) :
    globalSectionsEquiv k x =
      (Scheme.ΓSpecIso _).hom ((AffineSpace.SpecIso PUnit.{u + 1} (.of k)).inv.appTop x) :=
  rfl

/-- `globalSectionsEquiv` sends the standard coordinate to the variable. -/
theorem globalSectionsEquiv_coordinate :
    globalSectionsEquiv k (coordinate k) = MvPolynomial.X PUnit.unit := by
  rw [globalSectionsEquiv_apply, AffineSpace.SpecIso_inv_appTop_coord]
  exact Iso.inv_hom_id_apply _ _

/-- The isomorphism of the polynomial ring `k[t]` with the ring of global functions of the
affine line, sending the variable to the standard coordinate. -/
noncomputable def polynomialRingEquiv : Polynomial k ≃+* Γ((affineLine k).left, ⊤) :=
  (MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1}).symm.toRingEquiv.trans
    (globalSectionsEquiv k).symm

/-- `polynomialRingEquiv` sends the variable `X` to the standard coordinate. -/
theorem polynomialRingEquiv_X : polynomialRingEquiv k Polynomial.X = coordinate k := by
  rw [polynomialRingEquiv, RingEquiv.trans_apply, RingEquiv.symm_apply_eq,
    globalSectionsEquiv_coordinate, ← Polynomial.monomial_one_one_eq_X, AlgEquiv.toRingEquiv_eq_coe,
    AlgEquiv.coe_ringEquiv,
    show (1 : ℕ) = (Finsupp.single PUnit.unit 1 : PUnit.{u + 1} →₀ ℕ) PUnit.unit by simp,
    MvPolynomial.uniqueAlgEquiv_symm_monomial]
  rfl

/-- The ring of global functions of the affine line is a principal ideal ring. -/
instance isPrincipalIdealRing_globalSections :
    IsPrincipalIdealRing Γ((affineLine k).left, ⊤) :=
  IsPrincipalIdealRing.of_surjective (polynomialRingEquiv k) (polynomialRingEquiv k).surjective

/-- The standard coordinate of the affine line is irreducible. -/
theorem irreducible_coordinate : Irreducible (coordinate k) := by
  rw [← polynomialRingEquiv_X]
  exact (MulEquiv.irreducible_iff (polynomialRingEquiv k).toMulEquiv).2 Polynomial.irreducible_X

/-- The standard coordinate of the affine line generates a maximal ideal. -/
theorem isMaximal_span_coordinate : (Ideal.span {coordinate k}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (irreducible_coordinate k)

/-! ### The punctured affine line -/

/-- The restriction of global functions from the affine line to its puncture. -/
noncomputable abbrev puncturedRestriction :
    Γ((affineLine k).left, ⊤) →+* Γ((puncturedAffineLine k).left, ⊤) :=
  (puncturedAffineLineOpen k).ι.appTop.hom

/-- The affine line is an integral scheme. -/
instance isIntegral_affineLine : IsIntegral (affineLine k).left :=
  inferInstanceAs (IsIntegral (AffineSpace PUnit.{u + 1} (Spec (.of k))))

/-- The coordinate does not vanish identically. -/
theorem coordinate_ne_zero : coordinate k ≠ 0 :=
  (irreducible_coordinate k).ne_zero

/-- The punctured affine line is nonempty. -/
instance nonempty_puncturedAffineLine : Nonempty (puncturedAffineLine k).left := by
  have hne : (affineLine k).left.basicOpen (coordinate k) ≠ ⊥ := by
    rw [Ne, basicOpen_eq_bot_iff]
    exact coordinate_ne_zero k
  obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
  exact ⟨⟨x, hx⟩⟩

/-- The punctured affine line is an integral scheme. -/
instance isIntegral_puncturedAffineLine : IsIntegral (puncturedAffineLine k).left :=
  isIntegral_of_isOpenImmersion (puncturedAffineLineOpen k).ι

/-- The global functions on the punctured affine line are those on the affine line with the
coordinate inverted. -/
theorem isLocalization_puncturedRestriction :
    let := (puncturedRestriction k).toAlgebra
    IsLocalization.Away (coordinate k) Γ((puncturedAffineLine k).left, ⊤) :=
  (isAffineOpen_top (affineLine k).left).isLocalization_of_eq_basicOpen (coordinate k) _
    (TopologicalSpace.Opens.isOpenEmbedding_obj_top _)

/-- The restriction from the affine line to its puncture is injective. -/
theorem puncturedRestriction_injective : Function.Injective (puncturedRestriction k) := by
  let := (puncturedRestriction k).toAlgebra
  have := isLocalization_puncturedRestriction k
  exact IsLocalization.injective (M := Submonoid.powers (coordinate k)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (coordinate_ne_zero k))

/-- The ring of global functions of the punctured affine line is a principal ideal ring. -/
instance isPrincipalIdealRing_puncturedAffineLine :
    IsPrincipalIdealRing Γ((puncturedAffineLine k).left, ⊤) := by
  let := (puncturedRestriction k).toAlgebra
  have := isLocalization_puncturedRestriction k
  exact IsLocalization.isPrincipalIdealRing (Submonoid.powers (coordinate k))

/-- The restriction of the coordinate to the punctured line is a unit. -/
theorem isUnit_puncturedRestriction_coordinate :
    IsUnit (puncturedRestriction k (coordinate k)) := by
  let := (puncturedRestriction k).toAlgebra
  have := isLocalization_puncturedRestriction k
  exact IsLocalization.Away.algebraMap_isUnit (coordinate k)

/-- Every element of the function field of the punctured line is a quotient of restrictions of
global functions of the affine line. -/
theorem exists_eq_div_puncturedRestriction (F : FractionRing Γ((puncturedAffineLine k).left, ⊤)) :
    ∃ a b : Γ((affineLine k).left, ⊤), b ≠ 0 ∧
      F = algebraMap _ _ (puncturedRestriction k a) /
        algebraMap _ _ (puncturedRestriction k b) := by
  let := (puncturedRestriction k).toAlgebra
  have := isLocalization_puncturedRestriction k
  obtain ⟨x, y, rfl⟩ := IsLocalization.exists_mk'_eq
    (nonZeroDivisors Γ((puncturedAffineLine k).left, ⊤)) F
  obtain ⟨x₀, ⟨_, i, rfl⟩, hx⟩ := IsLocalization.exists_mk'_eq
    (Submonoid.powers (coordinate k)) x
  obtain ⟨y₀, ⟨_, j, rfl⟩, hy⟩ := IsLocalization.exists_mk'_eq
    (Submonoid.powers (coordinate k)) (y : Γ((puncturedAffineLine k).left, ⊤))
  have hy₀ : y₀ ≠ 0 := by
    rintro rfl
    exact nonZeroDivisors.coe_ne_zero y (by rw [← hy, IsLocalization.mk'_zero])
  refine ⟨x₀ * coordinate k ^ j, y₀ * coordinate k ^ i,
    mul_ne_zero hy₀ (pow_ne_zero _ (coordinate_ne_zero k)), ?_⟩
  have hu : ∀ n : ℕ, algebraMap _ (FractionRing Γ((puncturedAffineLine k).left, ⊤))
      (puncturedRestriction k (coordinate k ^ n)) ≠ 0 := fun n => by
    rw [map_pow, map_pow]
    exact pow_ne_zero _ ((IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (isUnit_puncturedRestriction_coordinate k).ne_zero)))
  have hxe : x * puncturedRestriction k (coordinate k ^ i) = puncturedRestriction k x₀ := by
    rw [← hx]
    exact IsLocalization.mk'_spec _ _ _
  have hye : (y : Γ((puncturedAffineLine k).left, ⊤)) *
      puncturedRestriction k (coordinate k ^ j) = puncturedRestriction k y₀ := by
    rw [← hy]
    exact IsLocalization.mk'_spec _ _ _
  have hyK : algebraMap _ (FractionRing Γ((puncturedAffineLine k).left, ⊤))
      (y : Γ((puncturedAffineLine k).left, ⊤)) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.2
  have h1 := congrArg (algebraMap _ (FractionRing Γ((puncturedAffineLine k).left, ⊤))) hxe
  have h2 := congrArg (algebraMap _ (FractionRing Γ((puncturedAffineLine k).left, ⊤))) hye
  rw [map_mul] at h1 h2
  rw [IsFractionRing.mk'_eq_div, map_mul, map_mul, map_mul, map_mul, ← h1, ← h2]
  have := hu i
  have := hu j
  field_simp

/-- The prime ideal of a point of the affine line outside its puncture is generated by the
coordinate. -/
theorem primeIdealOf_eq_span_coordinate_of_notMem {z : (affineLine k).left}
    (hz : z ∉ puncturedAffineLineOpen k) :
    ((isAffineOpen_top (affineLine k).left).primeIdealOf ⟨z, trivial⟩).asIdeal =
      Ideal.span {coordinate k} := by
  have hU := isAffineOpen_top (affineLine k).left
  have hmem : coordinate k ∈ (hU.primeIdealOf ⟨z, trivial⟩).asIdeal := by
    by_contra h
    exact hz ((hU.mem_basicOpen_iff_notMem_primeIdealOf (coordinate k) trivial).2 h)
  exact ((isMaximal_span_coordinate k).eq_of_le
    (hU.primeIdealOf ⟨z, trivial⟩).isPrime.ne_top
    ((Ideal.span_singleton_le_iff_mem _).2 hmem)).symm

/-- Any two points of the affine line outside its puncture coincide. -/
theorem eq_of_notMem_puncturedAffineLineOpen {x y : (affineLine k).left}
    (hx : x ∉ puncturedAffineLineOpen k) (hy : y ∉ puncturedAffineLineOpen k) : x = y := by
  exact eq_of_asIdeal_primeIdealOf_eq ((primeIdealOf_eq_span_coordinate_of_notMem k hx).trans
    (primeIdealOf_eq_span_coordinate_of_notMem k hy).symm)

/-- The origin of the affine line: the image of the section with coordinate `0`. -/
noncomputable def origin : (affineLine k).left :=
  constSection k 0 (IsLocalRing.closedPoint k)

/-- The origin lies outside the punctured line. -/
theorem origin_notMem_puncturedAffineLineOpen : origin k ∉ puncturedAffineLineOpen k := by
  intro h
  have h' : IsLocalRing.closedPoint k ∈ (constSection k 0) ⁻¹ᵁ (puncturedAffineLineOpen k) := h
  rw [preimage_puncturedAffineLineOpen, Scheme.basicOpen_zero] at h'
  exact h'

/-- The prime ideal of the origin is generated by the coordinate. -/
theorem primeIdealOf_origin :
    ((isAffineOpen_top (affineLine k).left).primeIdealOf ⟨origin k, trivial⟩).asIdeal =
      Ideal.span {coordinate k} :=
  primeIdealOf_eq_span_coordinate_of_notMem k (origin_notMem_puncturedAffineLineOpen k)

/-- The origin has coheight one in the affine line. -/
theorem coheight_origin : Order.coheight (origin k) = 1 := by
  have h := coheight_eq_height_primeIdealOf (origin k)
  rw [primeIdealOf_origin, Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero (coordinate_ne_zero k)) (irreducible_coordinate k).not_isUnit]
    at h
  exact_mod_cast h

/-- The generic point of the affine line lies in the punctured line. -/
theorem genericPoint_mem_puncturedAffineLineOpen :
    genericPoint (affineLine k).left ∈ puncturedAffineLineOpen k :=
  ((genericPoint_spec (affineLine k).left).mem_open_set_iff (puncturedAffineLineOpen k).isOpen).2
    ⟨_, trivial, (Classical.arbitrary (puncturedAffineLine k).left).2⟩

/-- The affine line over a field has dimension one. -/
theorem topologicalKrullDim_affineLine : topologicalKrullDim (affineLine k).left = 1 := by
  rw [IsHomeomorph.topologicalKrullDim_eq _
    ((affineLine k).left.isoSpec.hom.homeomorph).isHomeomorph]
  refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
    (R := Γ((affineLine k).left, ⊤))).trans ?_
  rw [ringKrullDim_eq_of_ringEquiv (polynomialRingEquiv k).symm,
    Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]

/-- A closed point of the affine line is not its generic point. -/
theorem ne_genericPoint_of_isClosed_singleton {y : (affineLine k).left}
    (hy : IsClosed ({y} : Set (affineLine k).left)) : y ≠ genericPoint (affineLine k).left := by
  rintro rfl
  have h := (genericPoint_spec (affineLine k).left).def
  rw [hy.closure_eq] at h
  have hmem : origin k ∈ ({genericPoint (affineLine k).left} : Set (affineLine k).left) := by
    rw [h]
    trivial
  rw [Set.mem_singleton_iff] at hmem
  exact origin_notMem_puncturedAffineLineOpen k (hmem ▸ genericPoint_mem_puncturedAffineLineOpen k)

/-- A point of the affine line is closed if and only if it has coheight one. -/
theorem isClosed_singleton_iff_coheight_eq_one (y : (affineLine k).left) :
    IsClosed ({y} : Set (affineLine k).left) ↔ Order.coheight y = 1 := by
  have hdim := topologicalKrullDim_affineLine k
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · have h :=
      Stacks.AlgebraicGeometry.AmpleDimensionOne.ringKrullDim_stalk_eq_one_of_ne_genericPoint _
        hdim (ne_genericPoint_of_isClosed_singleton k hy)
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact_mod_cast h
  · refine
      Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint _ hdim ?_
    rintro rfl
    have h0 : Order.coheight (genericPoint (affineLine k).left) = 0 :=
      Order.coheight_eq_zero.2 fun z _ => (genericPoint_spec (affineLine k).left).specializes
        (Set.mem_univ z)
    exact zero_ne_one (h0.symm.trans hy)

end AffineLineInvolution

end AlgebraicGeometry

end
