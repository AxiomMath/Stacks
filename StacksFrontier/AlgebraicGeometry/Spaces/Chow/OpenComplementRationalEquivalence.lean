module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FunctionFieldAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingOpenImmersion

/-!
# Integral closed subspaces of an open subspace, and rational equivalence on the complement

In the situation of Stacks 0EDT let `X/B` be good, let `j : U ⟶ X` be an open immersion over
the base and let `i : Y ⟶ X` be a closed immersion over the base whose image is the complement
of the image of `j`. An integral closed subspace `W ⊆ U` determines the integral closed
subspace `W' ⊆ X` on the closure of its image; `W` is recovered from `W'` as its inverse image
in `|U|`, is in fact the fibre product `W' ×_X U`, the two have the same generic point, and the
integral closed subspaces of `W` are carried into `X` by either route to the same subspaces.
The comparison morphism `W ⟶ W'` is an open immersion, and the function fields, the henselian
local rings at corresponding points and the orders of vanishing along corresponding prime
divisors of `W` and of `W'` all agree.

If a cycle `δ ∈ Z_k(X)` rationally equivalent to zero satisfies `(α - β - δ)|_U = 0`, then the
difference `α - β - δ` is a pushforward `i_*γ` and `α ∼_rat β + i_*γ`.

## Main results

* `IntegralClosedSubspace.preimage_subspacePointSet_closureImage`: the point set of `W` is the
  inverse image of the point set of `W'`.
* `IntegralClosedSubspace.isPullback_of_preimage_subspacePointSet`: `W` is the fibre product
  `W' ×_X U`.
* `IntegralClosedSubspace.isOpenImmersion_of_comp_ι_eq` and
  `IntegralClosedSubspace.isOpenImmersion_of_comp_ι_eq_closureImage`: the comparison morphism
  `m : W ⟶ W'` is an open immersion.
* `IntegralClosedSubspace.henselianLocalRingRingEquivOfCompIEq` and
  `IntegralClosedSubspace.genericHenselianLocalRingRingEquivOfCompIEq`: the henselian local rings
  of `W` and of `W'` agree at a point and at its image under `m`, in particular at the generic
  points of corresponding prime divisors.
* `IntegralClosedSubspace.ord_genericHenselianLocalRingRingEquivOfCompIEq`: the order of
  vanishing along a prime divisor of `W` is the order of vanishing along the corresponding prime
  divisor of `W'`.
* `IntegralClosedSubspace.isGenericPoint_closureImage`: `W` and `W'` have the same generic point.
* `IntegralClosedSubspace.pushforward_closureImage`: for an integral closed subspace of `W`,
  taking its closure in `W'` and then its image in `X` gives the closure in `X` of its image in
  `U`.
* `IntegralClosedSubspace.rationalFunctionsRingEquivClosureImage`: `R(W) = R(W')`, the function
  fields of `W` and of `W'` agree.
* `IntegralClosedSubspace.codimension_integralClosedSubspaceSupport_closureImage`:
  **Stacks 02I4** for integral closed subspaces — codimension is unchanged by taking the closure
  of the image along an open immersion.
* `PrimeDivisor.closureImage`, `PrimeDivisor.pointsMap_genericPoint_closureImage`,
  `PrimeDivisor.genericHenselianLocalRingRingEquivClosureImage` and
  `PrimeDivisor.ord_closureImage`: a prime divisor of an open subspace determines one of the
  ambient space, with the same generic point, the same henselian local ring there and the same
  order of vanishing.
* `principalDivisorCycleCoefficients_closureImage`: the coefficients of `div(f)` on `U` and on
  `X` agree along the closure of the image, given that the two embeddings of Stacks 0ENK are
  compatible.
* `cycleGroupRestrict_cycleFamilySum_closureImage`: the cycle `∑ (i'_n)_* c'_n` on `X` built
  from the closures restricts on `U` to `∑ (i_n)_* c_n`.
* `exists_rationallyEquivalent_of_restrict_of_lift`: **Stacks 0EQ7** under the extra hypothesis
  that a principal divisor on an integral closed subspace of `U` lifts to one on the closure of
  its image.
* `exists_rationallyEquivalent_add_cycleGroupClosedPushforward`: a cycle rationally equivalent
  to zero whose difference with `α - β` restricts to zero on `U` produces `γ ∈ Z_k(Y)` with
  `α ∼_rat β + i_*γ`.

## Implementation notes

The comparison of the subspaces of `W` with those of `X` is stated for an arbitrary morphism
`m : W ⟶ W'` over `X`; one exists by Stacks 03JJ, as
`IntegralClosedSubspace.exists_hom_closureImage`. The statements about `m` are given for any
integral closed subspace `W'` of `X` whose point set pulls back along `j` to the point set of
`W`, with the `closureImage` case as a corollary.

## References

* [Stacks Project, Tag 02I4](https://stacks.math.columbia.edu/tag/02I4)
* [Stacks Project, Tag 02YW](https://stacks.math.columbia.edu/tag/02YW)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 0BGV](https://stacks.math.columbia.edu/tag/0BGV)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EEG](https://stacks.math.columbia.edu/tag/0EEG)
* [Stacks Project, Tag 0EMX](https://stacks.math.columbia.edu/tag/0EMX)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EP9](https://stacks.math.columbia.edu/tag/0EP9)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ7](https://stacks.math.columbia.edu/tag/0EQ7)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### An integral closed subspace of an open subspace and its closure -/

section ClosureImage

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The order of vanishing along a prime divisor is transported along a ring isomorphism of the
henselian local rings at the generic points: if `e` identifies the henselian local ring of `Z` with
that of `Z'`, the order of vanishing of a unit `f` along `Z` agrees with the order of vanishing
along `Z'` of the unit `e` carries `f` to, on the induced isomorphism of total rings of
fractions. -/
theorem PrimeDivisor.ord_ringEquiv (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)
    [Nontrivial ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    [IsNoetherianRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    [Ring.KrullDimLE 1 ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    (hX' : IsAlgebraicSpace B S hS U) (hdec' : IsDecentSpace B S hS U)
    (Z' : PrimeDivisor B S hS U)
    [Nontrivial ↥(Z'.genericHenselianLocalRing B S hS hX' hdec')]
    [IsNoetherianRing ↥(Z'.genericHenselianLocalRing B S hS hX' hdec')]
    [Ring.KrullDimLE 1 ↥(Z'.genericHenselianLocalRing B S hS hX' hdec')]
    (e : ↥(Z.genericHenselianLocalRing B S hS hX hdec) ≃+*
      ↥(Z'.genericHenselianLocalRing B S hS hX' hdec'))
    (f : Z.genericTotalFractionRing B S hS hX hdec) (hf : IsUnit f) :
    Z.ord B S hS hX hdec f hf =
      Z'.ord B S hS hX' hdec'
        ((IsFractionRing.ringEquivOfRingEquiv e :
          Z.genericTotalFractionRing B S hS hX hdec ≃+*
            Z'.genericTotalFractionRing B S hS hX' hdec') f)
        (hf.map (IsFractionRing.ringEquivOfRingEquiv e :
          Z.genericTotalFractionRing B S hS hX hdec ≃+*
            Z'.genericTotalFractionRing B S hS hX' hdec').toRingHom) := by
  have := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  have := henselianLocalRing_isLocalRing B S hS U hX' (Z'.genericPoint B S hS U) hdec'
  exact (Ring.ordTotalFracInt_ringEquivOfRingEquiv e f hf).symm

/-- A base change of an open immersion of algebraic spaces, as a square of presheaves, is an open
immersion. -/
private theorem isOpenImmersion_of_isPullback_of_isAlgebraicSpace
    {P F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {fst : P ⟶ F} {snd : P ⟶ G} {f : F ⟶ H}
    {g : G ⟶ H} (hP : IsAlgebraicSpace B S hS P) (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (hH : IsAlgebraicSpace B S hS H)
    (sq : IsPullback fst snd f g) (hf : IsOpenImmersion B S hS f) :
    IsOpenImmersion B S hS snd :=
  isOpenImmersion_of_isPullback B S hS
    (show IsPullback (ObjectProperty.homMk fst : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩)
        (ObjectProperty.homMk snd : _ ⟶ ⟨G, hG⟩) (ObjectProperty.homMk f : _ ⟶ ⟨H, hH⟩)
        (ObjectProperty.homMk g) from
      IsPullback.of_map_of_faithful
        (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
          IsAlgebraicSpace B S hS T)) sq) hf

/-- The point set of an integral closed subspace `W` of `U` is the inverse image of the point set
of the integral closed subspace of `X` on the closure of its image along an immersion
`j : U ⟶ X`. -/
theorem IntegralClosedSubspace.preimage_subspacePointSet_closureImage
    (hX : IsAlgebraicSpace B S hS X) (hU : IsAlgebraicSpace B S hS U)
    (hXdec : IsDecentSpace B S hS X) {j : U ⟶ X} (hj : IsImmersion B S hS j)
    (W : IntegralClosedSubspace B S hS U) :
    pointsMap B S hS U j ⁻¹' subspacePointSet B S hS X
        (IntegralClosedSubspace.closureImage B S hS hX hXdec j W).subspace =
      subspacePointSet B S hS U W.subspace := by
  have hind := (isEmbedding_pointsMap_of_isImmersion B S hS hX j hj).isInducing
  have hcl : IsClosed (subspacePointSet B S hS U W.subspace) :=
    isClosed_range_pointsMap_integralClosedSubspace B S hS hU W
  rw [IntegralClosedSubspace.subspacePointSet_closureImage,
    ← hind.closure_eq_preimage_closure_image, hcl.closure_eq]

/-- **Stacks 02I4 for integral closed subspaces.** Taking the closure of the image along an open
immersion `j : U ⟶ X` does not change the codimension of an integral closed subspace of `U`. -/
theorem IntegralClosedSubspace.codimension_integralClosedSubspaceSupport_closureImage
    (hX : IsAlgebraicSpace B S hS X) (hU : IsAlgebraicSpace B S hS U)
    (hXdec : IsDecentSpace B S hS X) {j : U ⟶ X} (hj : IsOpenImmersion B S hS j)
    (V : IntegralClosedSubspace B S hS U) :
    codimension (integralClosedSubspaceSupport B S hS hX
        (IntegralClosedSubspace.closureImage B S hS hX hXdec j V)) =
      codimension (integralClosedSubspaceSupport B S hS hU V) := by
  have hemb : Topology.IsOpenEmbedding (pointsMap B S hS U j) :=
    ⟨isEmbedding_pointsMap_of_isImmersion B S hS hX j
        (isImmersion_of_isOpenImmersion B S hS hj),
      isOpen_range_pointsMap_of_isOpenImmersion B S hS j hj⟩
  have hmap : integralClosedSubspaceSupport B S hS hX
      (IntegralClosedSubspace.closureImage B S hS hX hXdec j V) =
      IrreducibleCloseds.map (pointsMap B S hS U j) (continuous_pointsMap B S hS j)
        (integralClosedSubspaceSupport B S hS hU V) :=
    IrreducibleCloseds.ext
      (IntegralClosedSubspace.subspacePointSet_closureImage B S hS hX hXdec j V)
  rw [hmap, codimension_eq_coheight, codimension_eq_coheight]
  exact hemb.coheight_map _

/-- An integral closed subspace `W` of `U` is the fibre product `W' ×_X U` along an open immersion
`j : U ⟶ X`, for `W'` an integral closed subspace of `X` whose point set pulls back to the point
set of `W`. -/
theorem IntegralClosedSubspace.isPullback_of_preimage_subspacePointSet
    (hX : IsAlgebraicSpace B S hS X) (hU : IsAlgebraicSpace B S hS U) {j : U ⟶ X}
    (hj : IsOpenImmersion B S hS j) (W : IntegralClosedSubspace B S hS U)
    (W' : IntegralClosedSubspace B S hS X)
    (hpre : pointsMap B S hS U j ⁻¹' subspacePointSet B S hS X W'.subspace =
      subspacePointSet B S hS U W.subspace)
    {m : W.subspace.toFunctor ⟶ W'.subspace.toFunctor}
    (hm : m ≫ W'.subspace.ι = W.subspace.ι ≫ j) :
    IsPullback W.subspace.ι m j W'.subspace.ι := by
  have hPc : IsClosedSubspace B S hS (W'.subspace.preimage j) :=
    AlgebraicGeometry.Space.isClosedSubspace_preimage B S hS j W'.subspace hX hU
      W'.isClosedSubspace
  have hsq : IsPullback (W'.subspace.fromPreimage j) (W'.subspace.preimage j).ι
      W'.subspace.ι j := Subfunctor.isPullback_preimage j W'.subspace
  have hfromOpen : IsOpenImmersion B S hS (W'.subspace.fromPreimage j) :=
    isOpenImmersion_of_isPullback_of_isAlgebraicSpace B S hS hPc.1 hU W'.isClosedSubspace.1 hX
      hsq.flip hj
  have hPred : HasEtaleLocalProperty B S hS (W'.subspace.preimage j).toFunctor
      (fun T : Scheme.{u} => IsReduced T) :=
    hasEtaleLocalProperty_of_isEtale B S hS hPc.1 W'.isClosedSubspace.1
      (isEtale_of_presheaf_etale B S hS
        (presheaf_etale_of_isOpenImmersion B S hS hfromOpen)) W'.isIntegralSpace.1
  have hPrange : Set.range (pointsMap B S hS (W'.subspace.preimage j).toFunctor
        (W'.subspace.preimage j).ι) =
      pointsMap B S hS U j ⁻¹' subspacePointSet B S hS X W'.subspace := by
    rw [show subspacePointSet B S hS X W'.subspace =
      pointsMap B S hS W'.subspace.toFunctor W'.subspace.ι '' Set.univ from
        Set.image_univ.symm, preimage_image_pointsMap_of_isPullback B S hS hsq Set.univ,
      Set.preimage_univ, Set.image_univ]
  obtain ⟨t, ht⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hU hPc.1
    W.subspace W.isClosedSubspace hPred (W'.subspace.preimage j).ι).2
      (hPrange.trans hpre).subset
  have htm : t ≫ m = W'.subspace.fromPreimage j := by
    refine (cancel_mono W'.subspace.ι).1 ?_
    rw [Category.assoc, hm, ← Category.assoc, ht, Subfunctor.fromPreimage_ι]
  refine IsPullback.of_isLimit (c := Limits.PullbackCone.mk _ _ hm.symm) ?_
  refine Limits.PullbackCone.IsLimit.mk hm.symm
    (fun s => hsq.flip.lift s.fst s.snd s.condition ≫ t) (fun s => ?_) (fun s => ?_)
    (fun s l hl₁ _ => ?_)
  · rw [Category.assoc, ht, hsq.flip.lift_fst]
  · rw [Category.assoc, htm, hsq.flip.lift_snd]
  · refine (cancel_mono W.subspace.ι).1 ?_
    rw [Category.assoc, ht, hsq.flip.lift_fst, hl₁]

/-- **The comparison morphism of Stacks 0EEG is an open immersion along an open immersion.** For
`W` an integral closed subspace of `U` and `W'` one of `X` whose point set pulls back along an open
immersion `j : U ⟶ X` to the point set of `W`, a morphism `W ⟶ W'` over `j` is an open
immersion. -/
theorem IntegralClosedSubspace.isOpenImmersion_of_comp_ι_eq
    (hX : IsAlgebraicSpace B S hS X) (hU : IsAlgebraicSpace B S hS U) {j : U ⟶ X}
    (hj : IsOpenImmersion B S hS j) (W : IntegralClosedSubspace B S hS U)
    (W' : IntegralClosedSubspace B S hS X)
    (hpre : pointsMap B S hS U j ⁻¹' subspacePointSet B S hS X W'.subspace =
      subspacePointSet B S hS U W.subspace)
    {m : W.subspace.toFunctor ⟶ W'.subspace.toFunctor}
    (hm : m ≫ W'.subspace.ι = W.subspace.ι ≫ j) :
    IsOpenImmersion B S hS m :=
  isOpenImmersion_of_isPullback_of_isAlgebraicSpace B S hS W.isClosedSubspace.1 hU
    W'.isClosedSubspace.1 hX
    (IntegralClosedSubspace.isPullback_of_preimage_subspacePointSet B S hS hX hU hj W W' hpre hm)
    hj

/-- **The comparison morphism to the closure of the image is an open immersion.** A morphism
from an integral closed subspace `W` of `U` to the integral closed subspace of `X` on the
closure of its image, over an open immersion `j : U ⟶ X`, is an open immersion. -/
theorem IntegralClosedSubspace.isOpenImmersion_of_comp_ι_eq_closureImage
    (hX : IsAlgebraicSpace B S hS X) (hU : IsAlgebraicSpace B S hS U)
    (hXdec : IsDecentSpace B S hS X) {j : U ⟶ X} (hj : IsOpenImmersion B S hS j)
    (W : IntegralClosedSubspace B S hS U)
    {m : W.subspace.toFunctor ⟶
      (IntegralClosedSubspace.closureImage B S hS hX hXdec j W).subspace.toFunctor}
    (hm : m ≫ (IntegralClosedSubspace.closureImage B S hS hX hXdec j W).subspace.ι =
      W.subspace.ι ≫ j) :
    IsOpenImmersion B S hS m :=
  IntegralClosedSubspace.isOpenImmersion_of_comp_ι_eq B S hS hX hU hj W _
    (IntegralClosedSubspace.preimage_subspacePointSet_closureImage B S hS hX hU hXdec
      (isImmersion_of_isOpenImmersion B S hS hj) W) hm

/-- The henselian local ring at a point depends only on the point: the identification along an
equality of points. -/
noncomputable def henselianLocalRingCongr {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hdec : IsDecentSpace B S hS Y)
    {x y : points B S hS Y} (h : x = y) :
    ↥(henselianLocalRing B S hS Y hY x hdec) ≃+* ↥(henselianLocalRing B S hS Y hY y hdec) := by
  subst h
  exact RingEquiv.refl _

/-- **The henselian local rings of `W` and of `W'` agree along the comparison morphism.** For `W`
an integral closed subspace of `U` and `W'` one of `X` whose point set pulls back along an open
immersion `j : U ⟶ X` to the point set of `W`, and `m : W ⟶ W'` over `j`, the henselian local ring
of `W` at a point is the henselian local ring of `W'` at its image. -/
noncomputable def IntegralClosedSubspace.henselianLocalRingRingEquivOfCompIEq
    (hX : IsAlgebraicSpace B S hS X) (hU : IsAlgebraicSpace B S hS U) {j : U ⟶ X}
    (hj : IsOpenImmersion B S hS j) (W : IntegralClosedSubspace B S hS U)
    (W' : IntegralClosedSubspace B S hS X)
    (hpre : pointsMap B S hS U j ⁻¹' subspacePointSet B S hS X W'.subspace =
      subspacePointSet B S hS U W.subspace)
    {m : W.subspace.toFunctor ⟶ W'.subspace.toFunctor}
    (hm : m ≫ W'.subspace.ι = W.subspace.ι ≫ j)
    (x : points B S hS W.subspace.toFunctor) :
    ↥(henselianLocalRing B S hS W.subspace.toFunctor W.isClosedSubspace.1 x
        W.isIntegralSpace.2.1) ≃+*
      ↥(henselianLocalRing B S hS W'.subspace.toFunctor W'.isClosedSubspace.1
        (pointsMap B S hS W.subspace.toFunctor m x) W'.isIntegralSpace.2.1) :=
  henselianLocalRingRingEquivOfIsOpenImmersion B S hS W'.isClosedSubspace.1
    W.isClosedSubspace.1 W'.isIntegralSpace.2.1 W.isIntegralSpace.2.1
    (IntegralClosedSubspace.isOpenImmersion_of_comp_ι_eq B S hS hX hU hj W W' hpre hm) x

/-- The henselian local rings at the generic points of corresponding prime divisors of `W` and
of `W'` agree: the comparison of
`AlgebraicGeometry.Space.IntegralClosedSubspace.henselianLocalRingRingEquivOfCompIEq` at the
generic point of the prime divisor of `W`, followed by the identification along the equality of
that image with the generic point of the prime divisor of `W'`. -/
noncomputable def IntegralClosedSubspace.genericHenselianLocalRingRingEquivOfCompIEq
    (hX : IsAlgebraicSpace B S hS X) (hU : IsAlgebraicSpace B S hS U) {j : U ⟶ X}
    (hj : IsOpenImmersion B S hS j) (W : IntegralClosedSubspace B S hS U)
    (W' : IntegralClosedSubspace B S hS X)
    (hpre : pointsMap B S hS U j ⁻¹' subspacePointSet B S hS X W'.subspace =
      subspacePointSet B S hS U W.subspace)
    {m : W.subspace.toFunctor ⟶ W'.subspace.toFunctor}
    (hm : m ≫ W'.subspace.ι = W.subspace.ι ≫ j)
    (Z : PrimeDivisor B S hS W.subspace.toFunctor)
    (Z' : PrimeDivisor B S hS W'.subspace.toFunctor)
    (hgen : pointsMap B S hS W.subspace.toFunctor m
        (Z.genericPoint B S hS W.subspace.toFunctor) =
      Z'.genericPoint B S hS W'.subspace.toFunctor) :
    ↥(Z.genericHenselianLocalRing B S hS W.isClosedSubspace.1 W.isIntegralSpace.2.1) ≃+*
      ↥(Z'.genericHenselianLocalRing B S hS W'.isClosedSubspace.1 W'.isIntegralSpace.2.1) :=
  (IntegralClosedSubspace.henselianLocalRingRingEquivOfCompIEq B S hS hX hU hj W W' hpre hm
    (Z.genericPoint B S hS W.subspace.toFunctor)).trans
      (henselianLocalRingCongr B S hS W'.isClosedSubspace.1 W'.isIntegralSpace.2.1 hgen)

/-- **The order of vanishing is the same on `W` and on `W'`.** At corresponding prime divisors of
an integral closed subspace `W` of `U` and of an integral closed subspace `W'` of `X` whose point
set pulls back along an open immersion `j : U ⟶ X` to the point set of `W`, the order of vanishing
of a unit of the total ring of fractions of the henselian local ring at the generic point of the
prime divisor of `W` is the order of vanishing along the prime divisor of `W'` of the unit it is
carried to by
`AlgebraicGeometry.Space.IntegralClosedSubspace.genericHenselianLocalRingRingEquivOfCompIEq`. -/
theorem IntegralClosedSubspace.ord_genericHenselianLocalRingRingEquivOfCompIEq
    (hX : IsAlgebraicSpace B S hS X) (hU : IsAlgebraicSpace B S hS U) {j : U ⟶ X}
    (hj : IsOpenImmersion B S hS j) (W : IntegralClosedSubspace B S hS U)
    (W' : IntegralClosedSubspace B S hS X)
    (hpre : pointsMap B S hS U j ⁻¹' subspacePointSet B S hS X W'.subspace =
      subspacePointSet B S hS U W.subspace)
    {m : W.subspace.toFunctor ⟶ W'.subspace.toFunctor}
    (hm : m ≫ W'.subspace.ι = W.subspace.ι ≫ j)
    (Z : PrimeDivisor B S hS W.subspace.toFunctor)
    (Z' : PrimeDivisor B S hS W'.subspace.toFunctor)
    (hgen : pointsMap B S hS W.subspace.toFunctor m
        (Z.genericPoint B S hS W.subspace.toFunctor) =
      Z'.genericPoint B S hS W'.subspace.toFunctor)
    [Nontrivial ↥(Z.genericHenselianLocalRing B S hS W.isClosedSubspace.1
      W.isIntegralSpace.2.1)]
    [IsNoetherianRing ↥(Z.genericHenselianLocalRing B S hS W.isClosedSubspace.1
      W.isIntegralSpace.2.1)]
    [Ring.KrullDimLE 1 ↥(Z.genericHenselianLocalRing B S hS W.isClosedSubspace.1
      W.isIntegralSpace.2.1)]
    [Nontrivial ↥(Z'.genericHenselianLocalRing B S hS W'.isClosedSubspace.1
      W'.isIntegralSpace.2.1)]
    [IsNoetherianRing ↥(Z'.genericHenselianLocalRing B S hS W'.isClosedSubspace.1
      W'.isIntegralSpace.2.1)]
    [Ring.KrullDimLE 1 ↥(Z'.genericHenselianLocalRing B S hS W'.isClosedSubspace.1
      W'.isIntegralSpace.2.1)]
    (f : Z.genericTotalFractionRing B S hS W.isClosedSubspace.1 W.isIntegralSpace.2.1)
    (hf : IsUnit f) :
    Z.ord B S hS W.isClosedSubspace.1 W.isIntegralSpace.2.1 f hf =
      Z'.ord B S hS W'.isClosedSubspace.1 W'.isIntegralSpace.2.1
        ((IsFractionRing.ringEquivOfRingEquiv
          (IntegralClosedSubspace.genericHenselianLocalRingRingEquivOfCompIEq B S hS hX hU hj W
            W' hpre hm Z Z' hgen) :
          Z.genericTotalFractionRing B S hS W.isClosedSubspace.1 W.isIntegralSpace.2.1 ≃+*
            Z'.genericTotalFractionRing B S hS W'.isClosedSubspace.1
              W'.isIntegralSpace.2.1) f)
        (hf.map (IsFractionRing.ringEquivOfRingEquiv
          (IntegralClosedSubspace.genericHenselianLocalRingRingEquivOfCompIEq B S hS hX hU hj W
            W' hpre hm Z Z' hgen) :
          Z.genericTotalFractionRing B S hS W.isClosedSubspace.1 W.isIntegralSpace.2.1 ≃+*
            Z'.genericTotalFractionRing B S hS W'.isClosedSubspace.1
              W'.isIntegralSpace.2.1).toRingHom) :=
  PrimeDivisor.ord_ringEquiv B S hS W.isClosedSubspace.1 W.isIntegralSpace.2.1 Z
    W'.isClosedSubspace.1 W'.isIntegralSpace.2.1 Z' _ f hf

/-- The integral closed subspace of `X` on the closure of the image of an integral closed subspace
`W` of `U` has the image of the generic point of `W` as its generic point. -/
theorem IntegralClosedSubspace.isGenericPoint_closureImage
    (hX : IsAlgebraicSpace B S hS X) (hU : IsAlgebraicSpace B S hS U)
    (hXdec : IsDecentSpace B S hS X) (j : U ⟶ X) (W : IntegralClosedSubspace B S hS U) :
    IsGenericPoint
      (pointsMap B S hS U j
        (pointsMap B S hS W.subspace.toFunctor W.subspace.ι (W.genericPoint B S hS)))
      (subspacePointSet B S hS X
        (IntegralClosedSubspace.closureImage B S hS hX hXdec j W).subspace) := by
  have hgen := isGenericPoint_pointsMap_genericPoint B S hS hU W
  have hstep : closure ({pointsMap B S hS U j
        (pointsMap B S hS W.subspace.toFunctor W.subspace.ι (W.genericPoint B S hS))} :
          Set (points B S hS X)) =
      closure (pointsMap B S hS U j '' subspacePointSet B S hS U W.subspace) := by
    rw [← hgen, closure_image_closure (continuous_pointsMap B S hS j), Set.image_singleton]
  exact hstep.trans
    (IntegralClosedSubspace.subspacePointSet_closureImage B S hS hX hXdec j W).symm

/-- The two routes from an integral closed subspace `V` of an integral closed subspace `W` of
`U` to an integral closed subspace of `X` agree: taking the closure of the image of `V` in the
closure `W'` of `W` and then the image in `X` gives the closure of the image in `X` of the
image of `V` in `U`. -/
theorem IntegralClosedSubspace.pushforward_closureImage
    (hX : IsAlgebraicSpace B S hS X) (hU : IsAlgebraicSpace B S hS U)
    (hXdec : IsDecentSpace B S hS X) (hUdec : IsDecentSpace B S hS U) {j : U ⟶ X}
    (W : IntegralClosedSubspace B S hS U)
    {m : W.subspace.toFunctor ⟶
      (IntegralClosedSubspace.closureImage B S hS hX hXdec j W).subspace.toFunctor}
    (hm : m ≫ (IntegralClosedSubspace.closureImage B S hS hX hXdec j W).subspace.ι =
      W.subspace.ι ≫ j)
    (V : IntegralClosedSubspace B S hS W.subspace.toFunctor) :
    IntegralClosedSubspace.pushforward B S hS hX
        (IntegralClosedSubspace.closureImage B S hS hX hXdec j W).isClosedSubspace.1 hXdec
        (IntegralClosedSubspace.closureImage B S hS hX hXdec j W).isClosedSubspace.2
        (IntegralClosedSubspace.closureImage B S hS
          (IntegralClosedSubspace.closureImage B S hS hX hXdec j W).isClosedSubspace.1
          (IntegralClosedSubspace.closureImage B S hS hX hXdec j W).isIntegralSpace.2.1 m V) =
      IntegralClosedSubspace.closureImage B S hS hX hXdec j
        (IntegralClosedSubspace.pushforward B S hS hU W.isClosedSubspace.1 hUdec
          W.isClosedSubspace.2 V) := by
  have hemb := isClosedEmbedding_pointsMap_of_isClosedImmersion B S hS hX
    (IntegralClosedSubspace.closureImage B S hS hX hXdec j W).isClosedSubspace.2
  have hcomp : pointsMap B S hS
        (IntegralClosedSubspace.closureImage B S hS hX hXdec j W).subspace.toFunctor
        (IntegralClosedSubspace.closureImage B S hS hX hXdec j W).subspace.ι ∘
      pointsMap B S hS W.subspace.toFunctor m =
      pointsMap B S hS U j ∘
        pointsMap B S hS W.subspace.toFunctor W.subspace.ι := by
    rw [← pointsMap_comp, ← pointsMap_comp, hm]
  refine injective_integralClosedSubspaceSupport B S hS hX (IrreducibleCloseds.ext ?_)
  show subspacePointSet B S hS X _ = subspacePointSet B S hS X _
  rw [IntegralClosedSubspace.subspacePointSet_pushforward,
    IntegralClosedSubspace.subspacePointSet_closureImage,
    IntegralClosedSubspace.subspacePointSet_closureImage,
    IntegralClosedSubspace.subspacePointSet_pushforward, ← hemb.closure_image_eq,
    ← Set.image_comp, hcomp, Set.image_comp]

/-- The function field of an integral closed subspace `W` of `U` is identified with the function
field of the integral closed subspace of `X` on the closure of its image along a monomorphism
`j : U ⟶ X`, through the residue fields at the generic point of `W` in `U` and at its image in `X`,
which a monomorphism identifies by Stacks 0EMX. -/
noncomputable def IntegralClosedSubspace.rationalFunctionsRingEquivClosureImage
    (hX : IsAlgebraicSpace B S hS X) (hU : IsAlgebraicSpace B S hS U)
    (hXdec : IsDecentSpace B S hS X) (hUdec : IsDecentSpace B S hS U)
    {j : U ⟶ X} (hjmono : Mono j) (W : IntegralClosedSubspace B S hS U) :
    rationalFunctions B S hS W.isClosedSubspace.1 ≃+*
      rationalFunctions B S hS
        (IntegralClosedSubspace.closureImage B S hS hX hXdec j W).isClosedSubspace.1 := by
  set ξ : points B S hS U :=
    pointsMap B S hS W.subspace.toFunctor W.subspace.ι (W.genericPoint B S hS) with hξdef
  have hmono0 : Mono (residueFieldMorphism B S hS U hUdec ξ) :=
    (residueFieldRepresentative B S hS U hUdec ξ).2.2
  have hmono : Mono (residueFieldMorphism B S hS U hUdec ξ ≫ j) := mono_comp _ _
  have hbij : Function.Bijective (residueFieldHom B S hS U X hX hUdec hXdec j ξ) := by
    have hiso := (isIso_residueFieldHom_iff_mono B S hS U X hX hUdec hXdec j ξ).2 hmono
    simpa using ConcreteCategory.bijective_of_isIso
      (CommRingCat.ofHom (residueFieldHom B S hS U X hX hUdec hXdec j ξ))
  have hpt : pointsMap B S hS U j ξ =
      pointsMap B S hS
        (IntegralClosedSubspace.closureImage B S hS hX hXdec j W).subspace.toFunctor
        (IntegralClosedSubspace.closureImage B S hS hX hXdec j W).subspace.ι
        ((IntegralClosedSubspace.closureImage B S hS hX hXdec j W).genericPoint B S hS) :=
    eq_pointsMap_genericPoint_of_isGenericPoint B S hS hX
      (IntegralClosedSubspace.closureImage B S hS hX hXdec j W) (pointsMap B S hS U j ξ)
      (IntegralClosedSubspace.isGenericPoint_closureImage B S hS hX hU hXdec j W)
  exact (residueFieldGenericPointRingEquiv B S hS hU hUdec W).symm.trans
    ((RingEquiv.ofBijective _ hbij).symm.trans
      ((residueFieldCongr B S hS hXdec hpt).trans
        (residueFieldGenericPointRingEquiv B S hS hX hXdec
          (IntegralClosedSubspace.closureImage B S hS hX hXdec j W))))

/-! ### Prime divisors along an open immersion -/

/-- **A prime divisor of an open subspace determines a prime divisor of the ambient space**, the
one on the closure of its image along an open immersion `j : U ⟶ X`. -/
noncomputable def PrimeDivisor.closureImage (hX : IsAlgebraicSpace B S hS X)
    (hU : IsAlgebraicSpace B S hS U) (hXdec : IsDecentSpace B S hS X) {j : U ⟶ X}
    (hj : IsOpenImmersion B S hS j) (Z : PrimeDivisor B S hS U) : PrimeDivisor B S hS X :=
  IntegralClosedSubspace.toPrimeDivisor B S hS hX
    (IntegralClosedSubspace.closureImage B S hS hX hXdec j
      (Z.toIntegralClosedSubspace B S hS))
    (by
      rw [IntegralClosedSubspace.codimension_integralClosedSubspaceSupport_closureImage
        B S hS hX hU hXdec hj]
      exact Z.codimension_integralClosedSubspaceSupport B S hS hU)

/-- The subfunctor underlying the prime divisor on the closure of the image. -/
@[simp]
theorem PrimeDivisor.subspace_closureImage (hX : IsAlgebraicSpace B S hS X)
    (hU : IsAlgebraicSpace B S hS U) (hXdec : IsDecentSpace B S hS X) {j : U ⟶ X}
    (hj : IsOpenImmersion B S hS j) (Z : PrimeDivisor B S hS U) :
    (Z.closureImage B S hS hX hU hXdec hj).subspace =
      (IntegralClosedSubspace.closureImage B S hS hX hXdec j
        (Z.toIntegralClosedSubspace B S hS)).subspace :=
  rfl

/-- **Corresponding prime divisors have corresponding generic points.** The generic point of the
prime divisor on the closure of the image of `Z` is the image of the generic point of `Z`. -/
theorem PrimeDivisor.pointsMap_genericPoint_closureImage (hX : IsAlgebraicSpace B S hS X)
    (hU : IsAlgebraicSpace B S hS U) (hXdec : IsDecentSpace B S hS X) {j : U ⟶ X}
    (hj : IsOpenImmersion B S hS j) (Z : PrimeDivisor B S hS U) :
    pointsMap B S hS U j (Z.genericPoint B S hS U) =
      (Z.closureImage B S hS hX hU hXdec hj).genericPoint B S hS X := by
  have : T0Space (points B S hS X) := t0Space_points_of_isDecentSpace B S hS hX hXdec
  refine IsGenericPoint.eq ?_
    ((Z.closureImage B S hS hX hU hXdec hj).isGenericPoint_genericPoint B S hS X)
  show closure {pointsMap B S hS U j (Z.genericPoint B S hS U)} =
    subspacePointSet B S hS X (Z.closureImage B S hS hX hU hXdec hj).subspace
  have hgen : closure {Z.genericPoint B S hS U} =
      subspacePointSet B S hS U Z.subspace :=
    Z.isGenericPoint_genericPoint B S hS U
  rw [PrimeDivisor.subspace_closureImage,
    IntegralClosedSubspace.subspacePointSet_closureImage,
    PrimeDivisor.subspace_toIntegralClosedSubspace, ← hgen,
    closure_image_closure (continuous_pointsMap B S hS j), Set.image_singleton]

/-- **The henselian local rings at corresponding prime divisors agree.** For `j : U ⟶ X` an open
immersion and `Z` a prime divisor of `U`, the henselian local ring of `U` at the generic point of
`Z` is the henselian local ring of `X` at the generic point of the prime divisor on the closure of
its image. -/
noncomputable def PrimeDivisor.genericHenselianLocalRingRingEquivClosureImage
    (hX : IsAlgebraicSpace B S hS X) (hU : IsAlgebraicSpace B S hS U)
    (hXdec : IsDecentSpace B S hS X) (hUdec : IsDecentSpace B S hS U) {j : U ⟶ X}
    (hj : IsOpenImmersion B S hS j) (Z : PrimeDivisor B S hS U) :
    ↥(Z.genericHenselianLocalRing B S hS hU hUdec) ≃+*
      ↥((Z.closureImage B S hS hX hU hXdec hj).genericHenselianLocalRing B S hS hX hXdec) :=
  (henselianLocalRingRingEquivOfIsOpenImmersion B S hS hX hU hXdec hUdec hj
      (Z.genericPoint B S hS U)).trans
    (henselianLocalRingCongr B S hS hX hXdec
      (Z.pointsMap_genericPoint_closureImage B S hS hX hU hXdec hj))

/-- **The order of vanishing along corresponding prime divisors agrees.** The order of vanishing
along a prime divisor `Z` of an open subspace `U ⊆ X` is the order of vanishing along the prime
divisor of `X` on the closure of its image, of the element it is carried to by
`AlgebraicGeometry.Space.PrimeDivisor.genericHenselianLocalRingRingEquivClosureImage`. -/
theorem PrimeDivisor.ord_closureImage (hX : IsAlgebraicSpace B S hS X)
    (hU : IsAlgebraicSpace B S hS U) (hXdec : IsDecentSpace B S hS X)
    (hUdec : IsDecentSpace B S hS U) {j : U ⟶ X} (hj : IsOpenImmersion B S hS j)
    (Z : PrimeDivisor B S hS U)
    [Nontrivial ↥(Z.genericHenselianLocalRing B S hS hU hUdec)]
    [IsNoetherianRing ↥(Z.genericHenselianLocalRing B S hS hU hUdec)]
    [Ring.KrullDimLE 1 ↥(Z.genericHenselianLocalRing B S hS hU hUdec)]
    [Nontrivial ↥((Z.closureImage B S hS hX hU hXdec hj).genericHenselianLocalRing B S hS hX
      hXdec)]
    [IsNoetherianRing ↥((Z.closureImage B S hS hX hU hXdec hj).genericHenselianLocalRing B S hS
      hX hXdec)]
    [Ring.KrullDimLE 1 ↥((Z.closureImage B S hS hX hU hXdec hj).genericHenselianLocalRing B S hS
      hX hXdec)]
    (f : Z.genericTotalFractionRing B S hS hU hUdec) (hf : IsUnit f) :
    Z.ord B S hS hU hUdec f hf =
      (Z.closureImage B S hS hX hU hXdec hj).ord B S hS hX hXdec
        ((IsFractionRing.ringEquivOfRingEquiv
          (Z.genericHenselianLocalRingRingEquivClosureImage B S hS hX hU hXdec hUdec hj) :
          Z.genericTotalFractionRing B S hS hU hUdec ≃+*
            (Z.closureImage B S hS hX hU hXdec hj).genericTotalFractionRing B S hS hX hXdec) f)
        (hf.map (IsFractionRing.ringEquivOfRingEquiv
          (Z.genericHenselianLocalRingRingEquivClosureImage B S hS hX hU hXdec hUdec hj) :
          Z.genericTotalFractionRing B S hS hU hUdec ≃+*
            (Z.closureImage B S hS hX hU hXdec hj).genericTotalFractionRing B S hS hX
              hXdec).toRingHom) :=
  PrimeDivisor.ord_ringEquiv B S hS hU hUdec Z hX hXdec _ _ f hf

end ClosureImage

/-! ### Principal divisors along an open immersion -/

section PrincipalDivisorComparison

variable (D : BaseSpaceDimensionSituation.{u})
    {X U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sU : U ⟶ D.space) (hU : D.IsGood sU)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X)
    (hUdec : IsDecentSpace D.site D.base D.base_mem U)
    {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j)
variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
  Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hXdec)]
variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
  IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hXdec)]
variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
  Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hXdec)]
variable [∀ W : PrimeDivisor D.site D.base D.base_mem U,
  Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hU.1 hUdec)]
variable [∀ W : PrimeDivisor D.site D.base D.base_mem U,
  IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hU.1 hUdec)]
variable [∀ W : PrimeDivisor D.site D.base D.base_mem U,
  Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hU.1 hUdec)]
variable (embX : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
    rationalFunctions D.site D.base D.base_mem hX.1 →+*
      W.genericTotalFractionRing D.site D.base D.base_mem hX.1 hXdec)
  (fX : rationalFunctions D.site D.base D.base_mem hX.1)
  (hfX : ∀ W : PrimeDivisor D.site D.base D.base_mem X, IsUnit (embX W fX))
  (embU : ∀ W : PrimeDivisor D.site D.base D.base_mem U,
    rationalFunctions D.site D.base D.base_mem hU.1 →+*
      W.genericTotalFractionRing D.site D.base D.base_mem hU.1 hUdec)
  (fU : rationalFunctions D.site D.base D.base_mem hU.1)
  (hfU : ∀ W : PrimeDivisor D.site D.base D.base_mem U, IsUnit (embU W fU))

/-- The order of vanishing along a prime divisor depends only on the element, not on the proof
that it is a unit. -/
private theorem ord_congr_of_eq (W : PrimeDivisor D.site D.base D.base_mem X)
    {a b : W.genericTotalFractionRing D.site D.base D.base_mem hX.1 hXdec}
    (ha : IsUnit a) (hb : IsUnit b) (hab : a = b) :
    W.ord D.site D.base D.base_mem hX.1 hXdec a ha =
      W.ord D.site D.base D.base_mem hX.1 hXdec b hb := by
  subst hab
  rfl

/-- **The coefficients of `div(f)` agree at corresponding prime divisors.** If the two embeddings
of Stacks 0ENK are compatible along
`AlgebraicGeometry.Space.PrimeDivisor.genericHenselianLocalRingRingEquivClosureImage`, then the
coefficient of `div(f_X)` at the prime divisor of `X` on the closure of the image of a prime
divisor `Z` of `U` is the coefficient of `div(f_U)` at `Z`. -/
theorem principalDivisorCycleCoefficients_closureImage_toIntegralClosedSubspace
    (hcompat : ∀ Z : PrimeDivisor D.site D.base D.base_mem U,
      embX (Z.closureImage D.site D.base D.base_mem hX.1 hU.1 hXdec hj) fX =
        (IsFractionRing.ringEquivOfRingEquiv
          (Z.genericHenselianLocalRingRingEquivClosureImage D.site D.base D.base_mem hX.1 hU.1
            hXdec hUdec hj) :
          Z.genericTotalFractionRing D.site D.base D.base_mem hU.1 hUdec ≃+*
            (Z.closureImage D.site D.base D.base_mem hX.1 hU.1 hXdec hj).genericTotalFractionRing
              D.site D.base D.base_mem hX.1 hXdec) (embU Z fU))
    (Z : PrimeDivisor D.site D.base D.base_mem U) :
    principalDivisorCycleCoefficients D sX hX hXdec embX fX hfX
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1 hXdec j
          (Z.toIntegralClosedSubspace D.site D.base D.base_mem)) =
      principalDivisorCycleCoefficients D sU hU hUdec embU fU hfU
        (Z.toIntegralClosedSubspace D.site D.base D.base_mem) := by
  have h1 : IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1 hXdec j
      (Z.toIntegralClosedSubspace D.site D.base D.base_mem) =
      (Z.closureImage D.site D.base D.base_mem hX.1 hU.1 hXdec hj).toIntegralClosedSubspace
        D.site D.base D.base_mem :=
    (IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor D.site D.base D.base_mem
      hX.1 _ _).symm
  rw [h1, principalDivisorCycleCoefficients_toIntegralClosedSubspace,
    principalDivisorCycleCoefficients_toIntegralClosedSubspace,
    principalDivisorCoefficients_apply, principalDivisorCoefficients_apply,
    PrimeDivisor.ord_closureImage D.site D.base D.base_mem hX.1 hU.1 hXdec hUdec hj Z
      (embU Z fU) (hfU Z)]
  exact ord_congr_of_eq D sX hX hXdec _ _ _ (hcompat Z)

/-- **The coefficient families of `div(f_X)` and `div(f_U)` agree along the closure of the image.**
The coefficient of `div(f_X)` at the integral closed subspace of `X` on the closure of the image of
an integral closed subspace `V` of `U` is the coefficient of `div(f_U)` at `V`. -/
theorem principalDivisorCycleCoefficients_closureImage
    (hcompat : ∀ Z : PrimeDivisor D.site D.base D.base_mem U,
      embX (Z.closureImage D.site D.base D.base_mem hX.1 hU.1 hXdec hj) fX =
        (IsFractionRing.ringEquivOfRingEquiv
          (Z.genericHenselianLocalRingRingEquivClosureImage D.site D.base D.base_mem hX.1 hU.1
            hXdec hUdec hj) :
          Z.genericTotalFractionRing D.site D.base D.base_mem hU.1 hUdec ≃+*
            (Z.closureImage D.site D.base D.base_mem hX.1 hU.1 hXdec hj).genericTotalFractionRing
              D.site D.base D.base_mem hX.1 hXdec) (embU Z fU))
    (V : IntegralClosedSubspace D.site D.base D.base_mem U) :
    principalDivisorCycleCoefficients D sX hX hXdec embX fX hfX
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1 hXdec j V) =
      principalDivisorCycleCoefficients D sU hU hUdec embU fU hfU V := by
  by_cases hcod : codimension
      (integralClosedSubspaceSupport D.site D.base D.base_mem hU.1 V) = 1
  · have hV : (V.toPrimeDivisor D.site D.base D.base_mem hU.1 hcod).toIntegralClosedSubspace
        D.site D.base D.base_mem = V :=
      IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor D.site D.base D.base_mem
        hU.1 V hcod
    rw [← hV]
    exact principalDivisorCycleCoefficients_closureImage_toIntegralClosedSubspace D sX hX sU hU
      hXdec hUdec hj embX fX hfX embU fU hfU hcompat _
  · rw [principalDivisorCycleCoefficients_of_codimension_ne_one D sU hU hUdec embU fU hfU hcod,
      principalDivisorCycleCoefficients_of_codimension_ne_one D sX hX hXdec embX fX hfX ?_]
    rw [IntegralClosedSubspace.codimension_integralClosedSubspaceSupport_closureImage
      D.site D.base D.base_mem hX.1 hU.1 hXdec hj V]
    exact hcod

end PrincipalDivisorComparison

/-! ### Rational equivalence on the complement of an open subspace -/

section Localization

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- In Situation 0EDT let `X/B` be good, let `i : Y ⟶ X` be a closed immersion over the base and
let `j : U ⟶ X` be an open immersion over the base whose image is the complement of the image of
`i`. If `δ ∈ Z_k(X)` is rationally equivalent to zero and `α - β - δ` restricts to zero on `U`,
then `α ∼_rat β + i_*γ` for a `k`-cycle `γ` on `Y`. -/
theorem exists_rationallyEquivalent_add_cycleGroupClosedPushforward (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (sU : U ⟶ D.space)
    (hU : D.IsGood sU) {i : Y ⟶ X} (hi : IsClosedImmersion D.site D.base D.base_mem i)
    (hic : i ≫ sX = sY) {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j)
    (hjc : j ≫ sX = sU)
    (hcomplement : Set.range (pointsMap D.site D.base D.base_mem Y i) =
      (Set.range (pointsMap D.site D.base D.base_mem U j))ᶜ) (k : ℤ)
    (α β δ : CycleGroup D sX k) (hδ : IsRationallyEquivalentToZero.{v} D sX hX k δ)
    (hres : cycleGroupRestrict D sX hX sU hU hj hjc k (α - β - δ) = 0) :
    ∃ γ : CycleGroup D sY k,
      RationallyEquivalent.{v} D sX hX k α
        (β + cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hi sX
          hX.2.2 sY hic k γ) := by
  obtain ⟨γ, hγ⟩ := (cycleGroupRestrict_eq_zero_iff D sX hX sY hY sU hU hi hic hj hjc
    hcomplement k (α - β - δ)).1 hres
  refine ⟨γ, ?_⟩
  have hkey : α - (β + cycleGroupClosedPushforward D hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hi sX hX.2.2 sY hic k γ) = δ := by
    rw [hγ]
    abel
  show IsRationallyEquivalentToZero.{v} D sX hX k (α - (β + _))
  rw [hkey]
  exact hδ

/-- The coefficient family of the pushforward of a cycle along the inclusion of an integral
closed subspace. -/
private theorem integralClosedSubspacePushforward_coe (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) (k : ℤ)
    (c : CycleGroup D (W.subspace.ι ≫ sX) k)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (integralClosedSubspacePushforward D sX hX W k c).1 Z =
      cycleClosedPushforward D hX.1 W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX)
        W.isClosedSubspace.2 c.1 Z :=
  rfl

/-- Let `j : U ⟶ X` be an open immersion over the base, let `W ⊆ U` be an integral closed subspace,
let `W' ⊆ X` be the integral closed subspace on the closure of its image and let `m : W ⟶ W'` be a
morphism over `j`. A `k`-cycle `c'` on `W'` whose coefficients agree with those of a `k`-cycle `c`
on `W` at corresponding integral closed subspaces pushes forward to a cycle on `X` whose
restriction to `U` is the pushforward of `c`. -/
theorem cycleGroupRestrict_integralClosedSubspacePushforward_closureImage
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sU : U ⟶ D.space) (hU : D.IsGood sU)
    {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j) (hjc : j ≫ sX = sU)
    (W : IntegralClosedSubspace D.site D.base D.base_mem U)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW' : W' = IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX) j W)
    {m : W.subspace.toFunctor ⟶ W'.subspace.toFunctor}
    (hm : m ≫ W'.subspace.ι = W.subspace.ι ≫ j)
    (k : ℤ) (c : CycleGroup D (W.subspace.ι ≫ sU) k)
    (c' : CycleGroup D (W'.subspace.ι ≫ sX) k)
    (hcc : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor,
      c'.1 (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
        W'.isClosedSubspace.1 W'.isIntegralSpace.2.1 m V) = c.1 V) :
    cycleGroupRestrict D sX hX sU hU hj hjc k
        (integralClosedSubspacePushforward D sX hX W' k c') =
      integralClosedSubspacePushforward D sU hU W k c := by
  have himm : IsImmersion D.site D.base D.base_mem j :=
    isImmersion_of_isOpenImmersion D.site D.base D.base_mem hj
  have hjinj : Function.Injective (pointsMap D.site D.base D.base_mem U j) :=
    (isEmbedding_pointsMap_of_isImmersion D.site D.base D.base_mem hX.1 j himm).injective
  subst hW'
  refine Subtype.ext (funext fun A => ?_)
  rw [cycleGroupRestrict_apply, integralClosedSubspacePushforward_coe,
    integralClosedSubspacePushforward_coe]
  by_cases hex : ∃ V : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor,
      IntegralClosedSubspace.pushforward D.site D.base D.base_mem hU.1 W.isClosedSubspace.1
        (D.isDecentSpace_of_isGood sU hU) W.isClosedSubspace.2 V = A
  · obtain ⟨V, rfl⟩ := hex
    rw [← IntegralClosedSubspace.pushforward_closureImage D.site D.base D.base_mem hX.1 hU.1
      (D.isDecentSpace_of_isGood sX hX) (D.isDecentSpace_of_isGood sU hU) W hm V,
      cycleClosedPushforward_apply_pushforward, cycleClosedPushforward_apply_pushforward]
    exact hcc V
  · rw [cycleClosedPushforward_apply_of_forall_ne D hU.1 W.isClosedSubspace.1
      (D.isDecentSpace_of_isGood sU hU) W.isClosedSubspace.2 c.1 A fun V hV => hex ⟨V, hV⟩]
    refine cycleClosedPushforward_apply_of_forall_ne D hX.1 _ _ _ c'.1 _ fun V hV => hex ?_
    have h1 : closure (pointsMap D.site D.base D.base_mem U j ''
          subspacePointSet D.site D.base D.base_mem U A.subspace) ⊆
        closure (pointsMap D.site D.base D.base_mem U j ''
          subspacePointSet D.site D.base D.base_mem U W.subspace) := by
      rw [← IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem hX.1
          (D.isDecentSpace_of_isGood sX hX) j A,
        ← IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem hX.1
          (D.isDecentSpace_of_isGood sX hX) j W, ← hV,
        IntegralClosedSubspace.subspacePointSet_pushforward]
      exact Set.image_subset_range _ _
    have h2 : pointsMap D.site D.base D.base_mem U j ''
          subspacePointSet D.site D.base D.base_mem U A.subspace ⊆
        pointsMap D.site D.base D.base_mem U j ''
          subspacePointSet D.site D.base D.base_mem U W.subspace := by
      rw [← IntegralClosedSubspace.image_subspacePointSet_eq_inter D.site D.base D.base_mem
          hX.1 hU.1 himm A,
        ← IntegralClosedSubspace.image_subspacePointSet_eq_inter D.site D.base D.base_mem
          hX.1 hU.1 himm W]
      exact Set.inter_subset_inter_left _ h1
    exact IntegralClosedSubspace.exists_pushforward_eq D.site D.base D.base_mem hU.1
      W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sU hU) W.isIntegralSpace.2.1
      W.isClosedSubspace.2 A ((Set.image_subset_image_iff hjinj).1 h2)

/-- Let `j : U ⟶ X` be an open immersion over the base, let `{W_n ⊆ U}` be a locally finite family
of integral closed subspaces, let `W'_n ⊆ X` be the integral closed subspace on the closure of the
image of `W_n` and let `m_n : W_n ⟶ W'_n` be a morphism over `j`. If a family of `k`-cycles `c'_n`
on the `W'_n` has, at corresponding integral closed subspaces, the coefficients of a family of
`k`-cycles `c_n` on the `W_n`, then the cycle `∑ (i'_n)_* c'_n` on `X` restricts on `U` to
`∑ (i_n)_* c_n`. -/
theorem cycleGroupRestrict_cycleFamilySum_closureImage
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sU : U ⟶ D.space) (hU : D.IsGood sU)
    {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j) (hjc : j ≫ sX = sU)
    {J : Type*} (W : J → IntegralClosedSubspace D.site D.base D.base_mem U)
    (hWfin : LocallyFinite fun n =>
      subspacePointSet D.site D.base D.base_mem U (W n).subspace)
    (W' : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW' : ∀ n, W' n = IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX) j (W n))
    (hW'fin : LocallyFinite fun n =>
      subspacePointSet D.site D.base D.base_mem X (W' n).subspace)
    {m : ∀ n, (W n).subspace.toFunctor ⟶ (W' n).subspace.toFunctor}
    (hm : ∀ n, m n ≫ (W' n).subspace.ι = (W n).subspace.ι ≫ j)
    (k : ℤ) (c : ∀ n, CycleGroup D ((W n).subspace.ι ≫ sU) k)
    (c' : ∀ n, CycleGroup D ((W' n).subspace.ι ≫ sX) k)
    (hcc : ∀ (n : J) (V : IntegralClosedSubspace D.site D.base D.base_mem
        (W n).subspace.toFunctor),
      (c' n).1 (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
        (W' n).isClosedSubspace.1 (W' n).isIntegralSpace.2.1 (m n) V) = (c n).1 V) :
    cycleGroupRestrict D sX hX sU hU hj hjc k (cycleFamilySum D sX hX W' hW'fin k c') =
      cycleFamilySum D sU hU W hWfin k c := by
  refine Subtype.ext (funext fun A => ?_)
  rw [cycleGroupRestrict_apply, cycleFamilySum_apply, cycleFamilySum_apply]
  refine finsum_congr fun n => ?_
  have h := congrArg (fun e : CycleGroup D sU k => e.1 A)
    (cycleGroupRestrict_integralClosedSubspacePushforward_closureImage D sX hX sU hU hj hjc
      (W n) (W' n) (hW' n) (hm n) k (c n) (c' n) (hcc n))
  simpa only [cycleGroupRestrict_apply] using h

/-- **Stacks 0EQ7 from the lifting of its principal divisors.** In Situation 0EDT let `X/B` be
good, let `i : Y ⟶ X` be a closed immersion over the base and let `j : U ⟶ X` be an open immersion
over the base whose image is the complement of the image of `i`. Suppose that every principal
divisor `div(f)` on an integral closed subspace `W ⊆ U` of δ-dimension `k + 1` is the restriction,
coefficient by coefficient along the comparison morphism, of a principal divisor on the integral
closed subspace `W' ⊆ X` on the closure of its image. Then two `k`-cycles on `X` whose restrictions
to `U` are rationally equivalent satisfy `α ∼_rat β + i_*γ` for a `k`-cycle `γ` on `Y`. -/
theorem exists_rationallyEquivalent_of_restrict_of_lift (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (sU : U ⟶ D.space) (hU : D.IsGood sU)
    {i : Y ⟶ X} (hi : IsClosedImmersion D.site D.base D.base_mem i) (hic : i ≫ sX = sY)
    {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j) (hjc : j ≫ sX = sU)
    (hcomplement : Set.range (pointsMap D.site D.base D.base_mem Y i) =
      (Set.range (pointsMap D.site D.base D.base_mem U j))ᶜ) (k : ℤ)
    (hlift : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem U)
      (c : CycleGroup D (W.subspace.ι ≫ sU) k)
      (m : W.subspace.toFunctor ⟶ (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
        hX.1 (D.isDecentSpace_of_isGood sX hX) j W).subspace.toFunctor),
      m ≫ (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1
          (D.isDecentSpace_of_isGood sX hX) j W).subspace.ι = W.subspace.ι ≫ j →
      deltaDimension D sU W = k + 1 →
      IsPrincipalDivisorCycle D (W.subspace.ι ≫ sU) k c →
      ∃ c' : CycleGroup D ((IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1
        (D.isDecentSpace_of_isGood sX hX) j W).subspace.ι ≫ sX) k,
        IsPrincipalDivisorCycle D ((IntegralClosedSubspace.closureImage D.site D.base D.base_mem
            hX.1 (D.isDecentSpace_of_isGood sX hX) j W).subspace.ι ≫ sX) k c' ∧
          ∀ V : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor,
            c'.1 (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
              (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1
                (D.isDecentSpace_of_isGood sX hX) j W).isClosedSubspace.1
              (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1
                (D.isDecentSpace_of_isGood sX hX) j W).isIntegralSpace.2.1 m V) = c.1 V)
    (α β : CycleGroup D sX k)
    (h : RationallyEquivalent.{v} D sU hU k
      (cycleGroupRestrict D sX hX sU hU hj hjc k α)
      (cycleGroupRestrict D sX hX sU hU hj hjc k β)) :
    ∃ γ : CycleGroup D sY k,
      RationallyEquivalent.{v} D sX hX k α
        (β + cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hi sX
          hX.2.2 sY hic k γ) := by
  have himm : IsImmersion D.site D.base D.base_mem j :=
    isImmersion_of_isOpenImmersion D.site D.base D.base_mem hj
  obtain ⟨J, W, hWfin, c, hdim, hprin, heq⟩ := h
  choose m hm using fun n => IntegralClosedSubspace.exists_hom_closureImage D.site D.base
    D.base_mem hX.1 (D.isDecentSpace_of_isGood sX hX) j (W n)
  choose c' hprin' hcc using fun n => hlift (W n) (c n) (m n) (hm n) (hdim n) (hprin n)
  have hW'fin := locallyFinite_subspacePointSet_closureImage D sX hX hj W hWfin
  have hdim' : ∀ n, deltaDimension D sX (IntegralClosedSubspace.closureImage D.site D.base
      D.base_mem hX.1 (D.isDecentSpace_of_isGood sX hX) j (W n)) = k + 1 := by
    intro n
    rw [IntegralClosedSubspace.deltaDimension_closureImage D sX hX.2.2 hX.1 hU.1
      (D.isDecentSpace_of_isGood sX hX) himm (W n), hjc]
    exact hdim n
  refine exists_rationallyEquivalent_add_cycleGroupClosedPushforward D sX hX sY hY sU hU hi hic
    hj hjc hcomplement k α β (cycleFamilySum D sX hX _ hW'fin k c')
    ⟨J, _, hW'fin, c', hdim', hprin', rfl⟩ ?_
  rw [map_sub, map_sub,
    cycleGroupRestrict_cycleFamilySum_closureImage D sX hX sU hU hj hjc W hWfin _
      (fun n => rfl) hW'fin hm k c c' hcc,
    ← heq, sub_self]

end Localization

end AlgebraicGeometry.Space

end
