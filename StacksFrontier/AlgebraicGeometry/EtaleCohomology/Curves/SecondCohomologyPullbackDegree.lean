module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.DivisorClassPullbackDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RamifiedDivisorSequenceSquare
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.SecondCohomologyOfRootsOfUnity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ClassGroupPicardBridge
public import StacksFrontier.AlgebraicGeometry.Curves.FlatMorphism
public import StacksFrontier.AlgebraicGeometry.Curves.SeparableClosedPoint
public import StacksCore.Tactic.StacksAttribute

/-!
# Pullback on `H²_étale(-, μ_n)` of a curve is multiplication by the degree

Let `k` be an algebraically closed field, let `π : X ⟶ Y` be a nonconstant morphism of smooth
proper curves over `k`, and let `n` be invertible in `k`.  Each of `H²_étale(Y, μ_n)` and
`H²_étale(X, μ_n)` is cyclic of order `n`, and in those coordinates the pullback `π^*` is
multiplication by the degree `deg(X/Y) = [R(X) : R(Y)]` of the extension of function fields.

The argument is the source's.  Every class of `H²_étale(Y, μ_n)` is the Kummer coboundary of a
class of `H¹_étale(Y, 𝐆_m)`, and the coordinate of that coboundary is the degree of that class
modulo `n`; restriction along `π` commutes with the Kummer coboundary, so what is left is that
restriction on `H¹_étale(-, 𝐆_m)` multiplies the degree by `deg(X/Y)`.  That is proved here by
identifying restriction on `H¹_étale(-, 𝐆_m)` with pullback of divisor classes, for which the
degree formula is the rank-one case of [Stacks, Tag 0AYZ].

The identification goes through the divisor sequence `0 → 𝐆_m → j_* 𝐆_{m,K} → ⨁_x i_{x,*} 𝐙 → 0`
of [Stacks, Tag 03RI].  Its comparison along `π`,
`Stacks.EtaleCohomology.divisorSequenceRamifiedHom`, weights each closed point of `X` above a
closed point `y` of `Y` by the local multiplicity of `π` there, so on global divisors the class of
`y` goes to the class of the fibre above `y` with those weights.  The connecting map of the
divisor sequence is compatible with restriction, so the same holds for the induced map of divisor
class groups.  On the other side, the fibre above `y` with those weights is exactly the pullback
of the effective Cartier divisor `y`: the local multiplicity at a closed point `x` of `X` is the
order of vanishing at `x` of a local equation of that pullback, by the order-of-vanishing identity
`Stacks.Chow.ord_dominantFunctionFieldMap_eq_ramificationLength_mul`.  Hence the two maps of
divisor class groups agree on the classes of the closed points, which generate, and pullback of
line bundles multiplies the degree by `deg(X/Y)`.

## Main definitions

The elided prefix throughout is `Stacks.EtaleCohomology`.

* `curveClosedPointFibre`: the closed points of `X` above a closed point of `Y`, as a `Finset`.
* `curveDivisorSequenceHom`, `curveDivisorSequenceInverseImageHom`: the comparison of the divisor
  sequences along `π`, and its adjoint.
* `curveDivisorRamifiedTop`: the induced map on global divisors.
* `curveClassGroupRamifiedPullback`: **the map of divisor class groups along `π`**, namely
  restriction on `H¹_étale(-, 𝐆_m)` read through `H¹(𝐆_m) ≅ Cl`.

## Main results

* `multiplicativeRestriction_divisorBoundary_ramified`: the connecting map of the divisor sequence
  commutes with restriction along `π`.
* `curveClassGroupRamifiedPullback_single`: the class group map sends the class of a closed point
  to the class of the weighted fibre above it.
* `curveClassGroupAddEquivSchemePicard_fibre`: that weighted fibre has `π^*𝒪_Y(y)` as its line
  bundle.
* `curveClassGroupRamifiedPullback_eq_curveClassGroupPullback`: **restriction on
  `H¹_étale(-, 𝐆_m)` is pullback of divisor classes.**
* `sheafHOneMultiplicativeDegreeMod_multiplicativeRestriction`: restriction multiplies the degree
  modulo `n` on `H¹_étale(-, 𝐆_m)` by `deg(X/Y)`.
* `sheafHTwoRootsOfUnityAddEquivZMod_rootsOfUnityRestriction`: **[Stacks, Tag 0AMB]**, the
  statement proved here.

## Implementation notes

Properness, dimension one and smoothness are presented separately rather than through a notion of
projective curve, because that is the shape in which the degree of a morphism
`AlgebraicGeometry.degreeOver`, the degree on the divisor class group
`Stacks.EtaleCohomology.curveClassGroupDegree` and the coordinate
`Stacks.EtaleCohomology.sheafHTwoRootsOfUnityAddEquivZMod` consume them.  Over a field this is no
loss: a smooth proper curve is projective.

Flatness of `π`, its finiteness, the finiteness of its fibres above the closed points, and the
preservation of codimension are all consequences of nonconstancy and are proved in the first
section; none of them is an assumption.

The coefficient universe is `u + 1` and the `Ext` universe is `u + 1`, which is where the divisor
sequence of a curve is exact and where `H¹_étale(X, 𝐆_m)` is identified with the divisor class
group; `Stacks.Cohomology.CoefficientLift.sheafHUliftAddEquiv` transports to a larger coefficient
universe.

## References

* [Stacks Project, Tag 0AMB](https://stacks.math.columbia.edu/tag/0AMB): the statement proved
  here.
* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ): the cohomology of `μ_n`
  on a smooth projective curve, whose `q = 2` clause supplies the coordinates.
* [Stacks Project, Tag 0AYZ](https://stacks.math.columbia.edu/tag/0AYZ): the degree of a
  pullback.
* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the divisor sequence.
* [Stacks Project, Tag 02OO](https://stacks.math.columbia.edu/tag/02OO): the pullback of an
  effective Cartier divisor along a dominant morphism of integral schemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Order TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### The hypotheses of the divisor-sequence comparison -/

section Plumbing

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (gX : X ⟶ Spec (.of k))
  (gY : Y ⟶ Spec (.of k)) [IsCurve k gX] [IsCurve k gY] [Smooth gX] [Smooth gY]
  [IsProper gX] [IsProper gY] (π : X ⟶ Y) (hπ : π ≫ gY = gX)
  (hnc : ¬ ∃ y : Y, ∀ x : X, π.base x = y)

omit [IsAlgClosed k] [IsCurve k gY] [Smooth gX] [Smooth gY] [IsProper gX] [IsProper gY] in
include gX hnc in
/-- A nonconstant morphism has a nontrivial range. -/
theorem nontrivial_range_of_not_constant : (Set.range π).Nontrivial := by
  by_contra h
  rw [Set.not_nontrivial_iff] at h
  exact hnc ⟨π.base (genericPoint X), fun x => h ⟨x, rfl⟩ ⟨_, rfl⟩⟩

omit [IsAlgClosed k] [Smooth gX] [IsProper gX] [IsProper gY] in
include hπ hnc in
/-- A nonconstant morphism of smooth proper curves over a field is flat. -/
theorem flat_of_not_constant : Flat π :=
  have := isNormal_of_isCurve_of_smooth gY
  (Flat.iff_flat_stalkMap π).2 (isFlat_of_nonconstant_of_isNormal gX gY π hπ
    (nontrivial_range_of_not_constant gX π hnc))

omit [IsAlgClosed k] [Smooth gX] [Smooth gY] in
include hπ hnc in
/-- A nonconstant morphism of smooth proper curves preserves codimension: the generic point goes
to the generic point and nothing else does, and every other point of either curve has
codimension one. -/
theorem coheight_base_eq_of_not_constant (x : X) : coheight (π.base x) = coheight x := by
  have : LocallyOfFiniteType π := locallyOfFiniteType_of_isCurve_comp k gX gY π hπ
  have : IsDominant π := isDominant_of_not_constant k gX gY π hnc
  by_cases hx : x = genericPoint X
  · subst hx
    rw [map_genericPoint_of_not_constant k gX gY π hnc,
      coheight_eq_zero.2 (isMax_genericPoint Y), coheight_eq_zero.2 (isMax_genericPoint X)]
  · have hy : π.base x ≠ genericPoint Y := by
      intro h
      refine hx ?_
      have : x ∈ π.base ⁻¹' {genericPoint Y} := h
      rw [preimage_genericPoint_of_not_constant k gX gY π hπ hnc] at this
      exact this
    rw [IsCurve.coheight_eq_one (f := gY) hy, IsCurve.coheight_eq_one (f := gX) hx]

omit [IsAlgClosed k] [Smooth gX] [Smooth gY] in
include hπ hnc in
/-- The fibres of a nonconstant morphism of proper curves above the closed points are finite. -/
theorem finite_preimage_closedPoint_of_not_constant (y : closedPoints Y) :
    (π.base ⁻¹' {y.1}).Finite :=
  have := isFinite_of_not_constant k gX gY π hπ hnc
  π.finite_preimage_singleton y.1

omit [IsAlgClosed k] [Smooth gX] [IsProper gX] [IsProper gY] in
include hπ in
/-- A morphism of curves over a field carries closed points to closed points. -/
theorem isClosed_base_of_mem_closedPoints (x : closedPoints X) :
    IsClosed ({π.base x.1} : Set Y) := by
  have : LocallyOfFiniteType π := locallyOfFiniteType_of_isCurve_comp k gX gY π hπ
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace gY
  exact π.closedPoints_subset_preimage_closedPoints x.2

/-- The image under `π` of a closed point of `X`, as a closed point of `Y`. -/
def closedPointBase (x : closedPoints X) : closedPoints Y :=
  ⟨π.base x.1, isClosed_base_of_mem_closedPoints gX gY π hπ x⟩

omit [IsAlgClosed k] [Smooth gX] [IsProper gX] [IsProper gY] in
/-- The underlying point of `closedPointBase x` is `π(x)`. -/
theorem closedPointBase_coe (x : closedPoints X) :
    (closedPointBase gX gY π hπ x).1 = π.base x.1 :=
  rfl

end Plumbing

/-! ### The morphism of divisor sequences along `π` -/

section Hom

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse
attribute [local instance 10000] hasCoproduct_closedPointSkyscraper

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (gX : X ⟶ Spec (.of k))
  (gY : Y ⟶ Spec (.of k)) [IsCurve k gX] [IsCurve k gY] [Smooth gX] [Smooth gY]
  [IsProper gX] [IsProper gY] (π : X ⟶ Y) (hπ : π ≫ gY = gX)
  (hnc : ¬ ∃ y : Y, ∀ x : X, π.base x = y)

/-- The finite set of closed points of `X` above a closed point of `Y`. -/
def curveClosedPointFibre (y : closedPoints Y) : Finset ↥(closedPoints X) :=
  closedPointFibreFinset π (finite_preimage_closedPoint_of_not_constant gX gY π hπ hnc) y

omit [IsAlgClosed k] [Smooth gX] [Smooth gY] in
/-- A closed point `x` of `X` lies in the fibre above `y` exactly when `π(x) = y`. -/
theorem mem_curveClosedPointFibre (y : closedPoints Y) (x : closedPoints X) :
    x ∈ curveClosedPointFibre gX gY π hπ hnc y ↔ π.base x.1 = y.1 :=
  mem_closedPointFibreFinset π _ y x

/-- **The morphism from the divisor sequence of `Y` to the direct image along `π` of that of
`X`**, for `π` a nonconstant morphism of smooth proper curves over an algebraically closed
field: the ramification-weighted comparison of `Stacks.EtaleCohomology.divisorSequenceRamifiedHom`
with its hypotheses discharged. -/
def curveDivisorSequenceHom :
    divisorSequence gY ⟶ (divisorSequence gX).map (etaleAbelianDirectImage.{u, u + 1} π) :=
  have := flat_of_not_constant gX gY π hπ hnc
  have := isFinite_of_not_constant k gX gY π hπ hnc
  divisorSequenceRamifiedHom gX gY π (coheight_base_eq_of_not_constant gX gY π hπ hnc)
    (curveClosedPointFibre gX gY π hπ hnc)
    (fun y x hx => (mem_curveClosedPointFibre gX gY π hπ hnc y x).1 hx)
    (fun y x hx => (mem_curveClosedPointFibre gX gY π hπ hnc y x).2 hx)
    (closedPointBase gX gY π hπ) (fun _ => rfl)

/-- **The morphism from the inverse image of the divisor sequence of `Y` to that of `X`**,
adjoint to `Stacks.EtaleCohomology.curveDivisorSequenceHom`. -/
def curveDivisorSequenceInverseImageHom :
    (divisorSequence gY).map (etaleAbelianInverseImage.{u, u + 1} π) ⟶ divisorSequence gX :=
  inverseImageShortComplexHom.{u, u + 1} π (curveDivisorSequenceHom gX gY π hπ hnc)

omit [IsAlgClosed k] in
/-- The first component of `Stacks.EtaleCohomology.curveDivisorSequenceInverseImageHom` is the
comparison `π⁻¹ 𝐆_{m,Y} ⟶ 𝐆_{m,X}`. -/
theorem curveDivisorSequenceInverseImageHom_τ₁ :
    (curveDivisorSequenceInverseImageHom gX gY π hπ hnc).τ₁ =
      Stacks.Kummer.multiplicativeInverseImageComparison.{u, u + 1} π :=
  rfl

/-- **The third component on global divisors**: a global divisor of `Y` is carried to `X` by the
ramification-weighted third component, and read over `X` itself. -/
def curveDivisorRamifiedTop :
    ToType ((closedPointDivisorSheaf.{u, u + 1} Y).obj.obj (op (Scheme.Etale.mk (𝟙 Y)))) →+
      ToType ((closedPointDivisorSheaf.{u, u + 1} X).obj.obj (op (Scheme.Etale.mk (𝟙 X)))) :=
  ((closedPointDivisorSheaf.{u, u + 1} X).obj.map
      (((isTerminalEtaleMkId Y).isTerminalObj (smallEtaleBaseChange π)).from
        (Scheme.Etale.mk (𝟙 X))).op).hom.comp
    ((curveDivisorSequenceHom gX gY π hπ hnc).τ₃.hom.app (op (Scheme.Etale.mk (𝟙 Y)))).hom

omit [IsAlgClosed k] in
/-- **Restriction in degree zero along the third component**: the restriction of the class of a
global divisor of `Y`, moved along `π⁻¹(⨁ i_{y,*} 𝐙) ⟶ ⨁ i_{x,*} 𝐙`, is the class of the carried
global divisor. -/
theorem sheafH_map_etaleCohomologyRestrictionMap_closedPointDivisorSheaf_ramified
    (s : ToType ((closedPointDivisorSheaf.{u, u + 1} Y).obj.obj (op (Scheme.Etale.mk (𝟙 Y))))) :
    Sheaf.H.map (curveDivisorSequenceInverseImageHom gX gY π hπ hnc).τ₃ 0
        (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} π
          (closedPointDivisorSheaf.{u, u + 1} Y) 0
          ((Sheaf.H.equiv₀ (closedPointDivisorSheaf.{u, u + 1} Y) (isTerminalEtaleMkId Y)).symm
            s)) =
      (Sheaf.H.equiv₀ (closedPointDivisorSheaf.{u, u + 1} X) (isTerminalEtaleMkId X)).symm
        (curveDivisorRamifiedTop gX gY π hπ hnc s) := by
  have hψ : (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} π).unit.app
      (closedPointDivisorSheaf.{u, u + 1} Y) ≫
        (etaleAbelianDirectImage.{u, u + 1} π).map
          (curveDivisorSequenceInverseImageHom gX gY π hπ hnc).τ₃ =
      (curveDivisorSequenceHom gX gY π hπ hnc).τ₃ :=
    ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} π).homEquiv_unit _ _ _).symm.trans
      (((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} π).homEquiv _ _).apply_symm_apply _)
  have h0 := equiv₀_etaleCohomologyRestrictionMap_zero.{u, u + 1, u + 1} π
    (closedPointDivisorSheaf.{u, u + 1} Y) (isTerminalEtaleMkId X)
    ((Sheaf.H.equiv₀ (closedPointDivisorSheaf.{u, u + 1} Y) (isTerminalEtaleMkId Y)).symm s)
  rw [AddEquiv.apply_symm_apply] at h0
  refine ((Sheaf.H.equiv₀ _ (isTerminalEtaleMkId X)).symm_apply_eq.mpr ?_).symm
  refine Eq.trans ?_ (Sheaf.H.equiv₀_naturality (isTerminalEtaleMkId X)
    (curveDivisorSequenceInverseImageHom gX gY π hπ hnc).τ₃ _)
  refine Eq.trans ?_ (congrArg (fun t =>
    ((curveDivisorSequenceInverseImageHom gX gY π hπ hnc).τ₃.hom.app
      (op (Scheme.Etale.mk (𝟙 X)))).hom t) h0.symm)
  refine Eq.trans ?_ (ConcreteCategory.congr_hom
    ((curveDivisorSequenceInverseImageHom gX gY π hπ hnc).τ₃.hom.naturality
      (((isTerminalEtaleMkId Y).isTerminalObj (smallEtaleBaseChange π)).from
        (Scheme.Etale.mk (𝟙 X))).op) _).symm
  exact (congrArg (fun t => ((closedPointDivisorSheaf.{u, u + 1} X).obj.map
      (((isTerminalEtaleMkId Y).isTerminalObj (smallEtaleBaseChange π)).from
        (Scheme.Etale.mk (𝟙 X))).op).hom t)
    (ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun f => f.hom) hψ)
      (op (Scheme.Etale.mk (𝟙 Y)))) s)).symm

omit [IsAlgClosed k] in
/-- **The connecting map of the divisor sequence commutes with restriction along `π`**:
restricting the class in `H¹(Y, 𝐆_m)` of a global divisor of `Y` to `X` gives the class of the
carried global divisor of `X`. -/
theorem multiplicativeRestriction_divisorBoundary_ramified
    (s : ToType ((closedPointDivisorSheaf.{u, u + 1} Y).obj.obj (op (Scheme.Etale.mk (𝟙 Y))))) :
    multiplicativeRestriction.{u, u + 1, u + 1} π 1 (divisorBoundary gY s) =
      divisorBoundary gX (curveDivisorRamifiedTop gX gY π hπ hnc s) := by
  have h := etaleCohomologyRestrictionMap_extClass_of_hom.{u, u + 1, u + 1} π
    (shortExact_divisorSequenceOfCurve gY) (shortExact_divisorSequenceOfCurve gX)
    (curveDivisorSequenceInverseImageHom gX gY π hπ hnc) 0 1 (zero_add 1)
    ((Sheaf.H.equiv₀ (closedPointDivisorSheaf.{u, u + 1} Y) (isTerminalEtaleMkId Y)).symm s)
  rw [sheafH_map_etaleCohomologyRestrictionMap_closedPointDivisorSheaf_ramified] at h
  exact h

omit [IsAlgClosed k] in
/-- The third component of `curveDivisorSequenceHom` is the ramification-weighted direct-image map
of closed-point divisors along the fibres of `π`. -/
theorem curveDivisorSequenceHom_τ₃ :
    (curveDivisorSequenceHom gX gY π hπ hnc).τ₃ =
      ramifiedClosedPointDivisorDirectImageMap.{u, u + 1} π
        (curveClosedPointFibre gX gY π hπ hnc)
        (fun y x hx => (mem_curveClosedPointFibre gX gY π hπ hnc y x).1 hx) :=
  rfl

end Hom

/-! ### The integer attached to a section of a summand -/

section Summand

variable {X Y : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsNormal X]
  [AlgebraicGeometry.IsIntegral Y] [IsNormal Y] (π : X ⟶ Y) [Flat π]

omit [AlgebraicGeometry.IsIntegral X] [IsNormal X] [AlgebraicGeometry.IsIntegral Y] [IsNormal Y]
  [Flat π] in
/-- **The integer of a summand section is unchanged by the third component**: the section of the
skyscraper at `x` produced from a global section of the skyscraper at `y` has the same integer,
the local multiplicity being carried as a separate weight. -/
theorem integerSkyscraperTopAddEquiv_ramifiedSummandMap (x : closedPoints X) (y : closedPoints Y)
    (hxy : π.base x.1 = y.1)
    (t : ToType ((closedPointSkyscraper.{u, u + 1} Y y).obj.obj
      (op (Scheme.Etale.mk (𝟙 Y))))) :
    integerSkyscraperTopAddEquiv.{u, u + 1} X x.1
        (((closedPointSkyscraper.{u, u + 1} X x).obj.map
            (((isTerminalEtaleMkId Y).isTerminalObj (smallEtaleBaseChange π)).from
              (Scheme.Etale.mk (𝟙 X))).op).hom
          (ramifiedSummandMap.{u, u + 1} π (Scheme.Etale.mk (𝟙 Y)) x y hxy t)) =
      integerSkyscraperTopAddEquiv.{u, u + 1} Y y.1 t := by
  refine integerSkyscraperTopAddEquiv_of_eq_const _ _ _ _ ?_
  refine integerSkyscraperSectionsIsoLocallyConstantMaps_map_of_eq_const _ _ _ _ ?_
  refine integerSkyscraperDirectImageMap_app_of_eq_const _ _ _ _ _ ?_
  exact integerSkyscraperSectionsIsoLocallyConstantMaps_eqToHom_of_eq_const hxy.symm _ _ _ _
    (integerSkyscraperSectionsIsoLocallyConstantMaps_eq_const Y y.1 t)

end Summand

/-! ### The carried global divisor of a closed point -/

section Fibre

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse
attribute [local instance 10000] hasCoproduct_closedPointSkyscraper

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (gX : X ⟶ Spec (.of k))
  (gY : Y ⟶ Spec (.of k)) [IsCurve k gX] [IsCurve k gY] [Smooth gX] [Smooth gY]
  [IsProper gX] [IsProper gY] (π : X ⟶ Y) (hπ : π ≫ gY = gX)
  (hnc : ¬ ∃ y : Y, ∀ x : X, π.base x = y)
  [IsNormal X] [IsLocallyNoetherian X] [NoetherianSpace X] [QuasiSeparatedSpace X]
  [IsNormal Y] [IsLocallyNoetherian Y] [NoetherianSpace Y] [QuasiSeparatedSpace Y]

omit [IsNormal Y] [IsLocallyNoetherian Y] [NoetherianSpace Y] [QuasiSeparatedSpace Y]
  [IsAlgClosed k] in
/-- **The carried global divisor of a global section of the summand at a closed point `y`** is the
sum over the closed points of `X` above `y`, with the local multiplicity of `π` as the
coefficient. -/
theorem closedPointDivisorSheafTopAddEquiv_curveDivisorRamifiedTop_ι (y : closedPoints Y)
    (t : ToType ((closedPointSkyscraper.{u, u + 1} Y y).obj.obj
      (op (Scheme.Etale.mk (𝟙 Y))))) :
    closedPointDivisorSheafTopAddEquiv.{u, u + 1} X
        (curveDivisorRamifiedTop gX gY π hπ hnc
          (((closedPointDivisorSheaf.ι.{u, u + 1} Y y).hom.app
            (op (Scheme.Etale.mk (𝟙 Y)))).hom t)) =
      ∑ x ∈ (curveClosedPointFibre gX gY π hπ hnc y).attach,
        Finsupp.single x.1 ((π.ramificationLength x.1.1 : ℤ) *
          integerSkyscraperTopAddEquiv.{u, u + 1} Y y.1 t) := by
  have := flat_of_not_constant gX gY π hπ hnc
  have := isFinite_of_not_constant k gX gY π hπ hnc
  set F := curveClosedPointFibre gX gY π hπ hnc with hFdef
  have hF : ∀ (z : closedPoints Y) (x : closedPoints X), x ∈ F z → π.base x.1 = z.1 :=
    fun z x hx => (mem_curveClosedPointFibre gX gY π hπ hnc z x).1 hx
  set r := ((isTerminalEtaleMkId Y).isTerminalObj (smallEtaleBaseChange π)).from
    (Scheme.Etale.mk (𝟙 X)) with hr
  have hA : ((curveDivisorSequenceHom gX gY π hπ hnc).τ₃.hom.app (op (Scheme.Etale.mk (𝟙 Y)))).hom
        (((closedPointDivisorSheaf.ι.{u, u + 1} Y y).hom.app (op (Scheme.Etale.mk (𝟙 Y)))).hom t) =
      ∑ x ∈ (F y).attach, (π.ramificationLength x.1.1 : ℤ) •
        ((closedPointDivisorSheaf.ι.{u, u + 1} X x.1).hom.app
            (op ((smallEtaleBaseChange π).obj (Scheme.Etale.mk (𝟙 Y))))).hom
          (ramifiedSummandMap.{u, u + 1} π (Scheme.Etale.mk (𝟙 Y)) x.1 y (hF y x.1 x.2) t) := by
    have l2 : sheafHomEval.{u, u + 1} (Scheme.Etale.mk (𝟙 Y)) t
          (closedPointDivisorSheaf.ι.{u, u + 1} Y y ≫
            ramifiedClosedPointDivisorDirectImageMap.{u, u + 1} π F hF) =
        ∑ x ∈ (F y).attach, sheafHomEval.{u, u + 1} (Scheme.Etale.mk (𝟙 Y)) t
          (weightedIntegerSkyscraperDirectImageMap.{u, u + 1} π x.1 y (hF y x.1 x.2)
            (π.ramificationLength x.1.1)) := by
      rw [ι_ramifiedClosedPointDivisorDirectImageMap, map_sum]
    rw [curveDivisorSequenceHom_τ₃]
    refine l2.trans (Finset.sum_congr rfl fun x _ => ?_)
    rw [sheafHomEval_apply, weightedIntegerSkyscraperDirectImageMap_app]
  have hB : ∀ (x : closedPoints X) (w : ToType ((closedPointSkyscraper.{u, u + 1} X x).obj.obj
        (op ((smallEtaleBaseChange π).obj (Scheme.Etale.mk (𝟙 Y)))))),
      ((closedPointDivisorSheaf.{u, u + 1} X).obj.map r.op).hom
          (((closedPointDivisorSheaf.ι.{u, u + 1} X x).hom.app
            (op ((smallEtaleBaseChange π).obj (Scheme.Etale.mk (𝟙 Y))))).hom w) =
        ((closedPointDivisorSheaf.ι.{u, u + 1} X x).hom.app (op (Scheme.Etale.mk (𝟙 X)))).hom
          (((closedPointSkyscraper.{u, u + 1} X x).obj.map r.op).hom w) := by
    intro x w
    have h := ConcreteCategory.congr_hom
      ((closedPointDivisorSheaf.ι.{u, u + 1} X x).hom.naturality r.op) w
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    exact h.symm
  have hC : curveDivisorRamifiedTop gX gY π hπ hnc
        (((closedPointDivisorSheaf.ι.{u, u + 1} Y y).hom.app (op (Scheme.Etale.mk (𝟙 Y)))).hom t) =
      ∑ x ∈ (F y).attach, (π.ramificationLength x.1.1 : ℤ) •
        ((closedPointDivisorSheaf.ι.{u, u + 1} X x.1).hom.app (op (Scheme.Etale.mk (𝟙 X)))).hom
          (((closedPointSkyscraper.{u, u + 1} X x.1).obj.map r.op).hom
            (ramifiedSummandMap.{u, u + 1} π (Scheme.Etale.mk (𝟙 Y)) x.1 y (hF y x.1 x.2) t)) := by
    change ((closedPointDivisorSheaf.{u, u + 1} X).obj.map r.op).hom
        (((curveDivisorSequenceHom gX gY π hπ hnc).τ₃.hom.app (op (Scheme.Etale.mk (𝟙 Y)))).hom
          (((closedPointDivisorSheaf.ι.{u, u + 1} Y y).hom.app (op (Scheme.Etale.mk (𝟙 Y)))).hom
            t)) = _
    rw [hA, map_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [map_zsmul, hB]
  rw [hC, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_zsmul, closedPointDivisorSheafTopAddEquiv_ι,
    integerSkyscraperTopAddEquiv_ramifiedSummandMap π x.1 y (hF y x.1 x.2) t,
    Finsupp.smul_single, smul_eq_mul]

end Fibre

/-! ### The map of divisor class groups along `π` -/

section ClassGroup

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse
attribute [local instance 10000] hasCoproduct_closedPointSkyscraper

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (gX : X ⟶ Spec (.of k))
  (gY : Y ⟶ Spec (.of k)) [IsCurve k gX] [IsCurve k gY] [Smooth gX] [Smooth gY]
  [IsProper gX] [IsProper gY] (π : X ⟶ Y) (hπ : π ≫ gY = gX)
  (hnc : ¬ ∃ y : Y, ∀ x : X, π.base x = y)

/-- **The map of divisor class groups along a nonconstant morphism of smooth proper curves over
an algebraically closed field**: restriction on `H¹(-, 𝐆_m)`, read through the identification of
that group with the divisor class group
(`Stacks.EtaleCohomology.sheafHOneMultiplicativeAddEquivClosedPointClassGroup`). -/
def curveClassGroupRamifiedPullback : curveClassGroup gY →+ curveClassGroup gX :=
  (sheafHOneMultiplicativeAddEquivClosedPointClassGroup gX).toAddMonoidHom.comp
    ((multiplicativeRestriction.{u, u + 1, u + 1} π 1).comp
      (sheafHOneMultiplicativeAddEquivClosedPointClassGroup gY).symm.toAddMonoidHom)

omit [IsProper gX] [IsProper gY] in
/-- Restriction on `H¹(-, 𝐆_m)` is the class group map read through `H¹(𝐆_m) ≅ Cl`. -/
theorem multiplicativeRestriction_one_eq_curveClassGroupRamifiedPullback
    (b : Sheaf.H.{u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} Y) 1) :
    multiplicativeRestriction.{u, u + 1, u + 1} π 1 b =
      (sheafHOneMultiplicativeAddEquivClosedPointClassGroup gX).symm
        (curveClassGroupRamifiedPullback gX gY π
          (sheafHOneMultiplicativeAddEquivClosedPointClassGroup gY b)) := by
  change _ = (sheafHOneMultiplicativeAddEquivClosedPointClassGroup gX).symm
    (sheafHOneMultiplicativeAddEquivClosedPointClassGroup gX
      (multiplicativeRestriction.{u, u + 1, u + 1} π 1
        ((sheafHOneMultiplicativeAddEquivClosedPointClassGroup gY).symm
          (sheafHOneMultiplicativeAddEquivClosedPointClassGroup gY b))))
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]

/-- **The class group map sends the class of a closed point `y` to the class of the fibre above
`y`**, each closed point of `X` above `y` weighted by the local multiplicity of `π` there. -/
theorem curveClassGroupRamifiedPullback_single (y : closedPoints Y) :
    curveClassGroupRamifiedPullback gX gY π
        (QuotientAddGroup.mk (Finsupp.single y (1 : ℤ)) : curveClassGroup gY) =
      (QuotientAddGroup.mk (∑ x ∈ (curveClosedPointFibre gX gY π hπ hnc y).attach,
          Finsupp.single x.1 (π.ramificationLength x.1.1 : ℤ)) : curveClassGroup gX) := by
  obtain ⟨_, _, _, _⟩ :=
    isNormal_isLocallyNoetherian_noetherianSpace_quasiSeparatedSpace_of_isCurve gX
  obtain ⟨_, _, _, _⟩ :=
    isNormal_isLocallyNoetherian_noetherianSpace_quasiSeparatedSpace_of_isCurve gY
  let t : ToType ((closedPointSkyscraper.{u, u + 1} Y y).obj.obj
      (op (Scheme.Etale.mk (𝟙 Y)))) := (integerSkyscraperTopAddEquiv.{u, u + 1} Y y.1).symm 1
  let sy := ((closedPointDivisorSheaf.ι.{u, u + 1} Y y).hom.app
    (op (Scheme.Etale.mk (𝟙 Y)))).hom t
  have hsy : closedPointDivisorSheafTopAddEquiv.{u, u + 1} Y sy = Finsupp.single y 1 := by
    refine (closedPointDivisorSheafTopAddEquiv_ι Y y t).trans ?_
    rw [AddEquiv.apply_symm_apply]
  have he := sheafHOneMultiplicativeAddEquivClosedPointClassGroup_divisorBoundary gY sy
  rw [hsy] at he
  rw [← he]
  change sheafHOneMultiplicativeAddEquivClosedPointClassGroup gX
    (multiplicativeRestriction.{u, u + 1, u + 1} π 1
      ((sheafHOneMultiplicativeAddEquivClosedPointClassGroup gY).symm
        (sheafHOneMultiplicativeAddEquivClosedPointClassGroup gY (divisorBoundary gY sy)))) = _
  rw [AddEquiv.symm_apply_apply,
    multiplicativeRestriction_divisorBoundary_ramified gX gY π hπ hnc,
    sheafHOneMultiplicativeAddEquivClosedPointClassGroup_divisorBoundary gX]
  refine congrArg QuotientAddGroup.mk ?_
  refine (closedPointDivisorSheafTopAddEquiv_curveDivisorRamifiedTop_ι gX gY π hπ hnc y t).trans ?_
  exact Finset.sum_congr rfl fun x _ => by rw [AddEquiv.apply_symm_apply, mul_one]

end ClassGroup

/-! ### The line bundle of a divisor read off from local equations -/

section Picard

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup
  AlgebraicGeometry.schemePicardGroupAddCommGroup

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g]

omit [IsAlgClosed k] in
/-- **Under `Cl(X) ≅ Pic(X)` a divisor goes to the class of `𝒪_X(D)`** when its Weil divisor
class is that of `D`: the identification is built from the first Chern class, so this is what
remains after the Weil divisor class has been computed. -/
theorem curveClassGroupAddEquivSchemePicard_mk_of_weilDivisorClass
    [IsLocallyNoetherian X] [AlgebraicGeometry.IsNoetherian X] (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (d : closedPoints X →₀ ℤ)
    (hwd : weilDivisorClassOfInvertibleSheaf X (Stacks.Divisors.modulesInvertibleSheaf D) =
      (((weilDivisorAddEquivClosedPointDivisor g).symm d : WeilDivisor X) :
        weilDivisorClassGroup X)) :
    curveClassGroupAddEquivSchemePicard g (QuotientAddGroup.mk d : curveClassGroup g) =
      divisorSchemePicardClass D := by
  let : AddCommGroup (Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      X.ringCatSheaf.property) :=
    Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup X.sheaf.obj X.ringCatSheaf.property
  have h1 : (Stacks.SheafOfModules.picardGroupShrinkAddEquiv X.sheaf.obj
      X.ringCatSheaf.property).symm (divisorSchemePicardClass D) =
      Stacks.SheafOfModules.picardClass X.sheaf.obj X.ringCatSheaf.property
        (Stacks.Divisors.divisorSheaf D) (stacksIsInvertible_divisorSheaf _) :=
    (AddEquiv.symm_apply_eq _).2 rfl
  have h2 : (curveClassGroupAddEquivSchemePicard g).symm (divisorSchemePicardClass D) =
      (QuotientAddGroup.mk d : curveClassGroup g) := by
    change weilDivisorClassGroupAddEquivClosedPointClassGroup g
      (picardToWeilDivisorClassGroup X ((Stacks.SheafOfModules.picardGroupShrinkAddEquiv
        X.sheaf.obj X.ringCatSheaf.property).symm (divisorSchemePicardClass D))) = _
    rw [h1]
    change weilDivisorClassGroupAddEquivClosedPointClassGroup g
      (weilDivisorClassOfPicardClass X _) = _
    refine (congrArg (weilDivisorClassGroupAddEquivClosedPointClassGroup g)
      ((@weilDivisorClassOfPicardClass_picardClass X _ _ _
        (stacksIsInvertible_divisorSheaf _)).trans hwd)).trans ?_
    rw [weilDivisorClassGroupAddEquivClosedPointClassGroup_mk, AddEquiv.apply_symm_apply]
  exact ((AddEquiv.symm_apply_eq _).1 h2).symm

end Picard

/-! ### The pullback of the divisor of a closed point -/

section Local

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (gX : X ⟶ Spec (.of k))
  (gY : Y ⟶ Spec (.of k)) [IsCurve k gX] [IsCurve k gY] [Smooth gX] [Smooth gY]
  [IsProper gX] [IsProper gY] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (π : X ⟶ Y)
  (hπ : π ≫ gY = gX) (hnc : ¬ ∃ y : Y, ∀ x : X, π.base x = y)

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [IsAlgClosed k] [Smooth gX] [IsProper gX] [IsProper gY] in
include hπ hnc in
/-- **A local equation of the pullback of a closed point `y` is nonzero** at a closed point `z`
of `X` above `y`: it generates the ideal that the maximal ideal at `y` induces, and the stalk map
of the flat `π` is injective, so a uniformizer at `y` has nonzero image. -/
theorem ne_zero_of_stalk_comap_vanishingIdeal_eq_span (y : closedPoints Y) (z : closedPoints X)
    (hzy : π.base z.1 = y.1) {c : X.presheaf.stalk z.1}
    (hc : (IsLocalRing.maximalIdeal (Y.presheaf.stalk (π.base z.1))).map
      (π.stalkMap z.1).hom = Ideal.span {c}) :
    c ≠ 0 := by
  have := flat_of_not_constant gX gY π hπ hnc
  have : IsDiscreteValuationRing (Y.presheaf.stalk (π.base z.1)) :=
    IsCurve.isDiscreteValuationRing_stalk_of_isClosed k gY (hzy ▸ y.2)
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk (π.base z.1))
  have hwm : w ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (π.base z.1)) := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer w).1 hw]
    exact Ideal.mem_span_singleton_self w
  intro h
  have hmem : (π.stalkMap z.1).hom w ∈ Ideal.span {c} :=
    hc ▸ Ideal.mem_map_of_mem _ hwm
  rw [h, Ideal.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at hmem
  exact hw.ne_zero ((map_eq_zero_iff _ (π.stalkMap_injective_of_flat z.1)).1 hmem)

omit [IsLocallyNoetherian Y] [IsAlgClosed k] [IsProper gX] [IsProper gY] in
open scoped Classical in
include hπ hnc in
/-- **The order of vanishing of a local equation of the pullback of a closed point `y`** is the
local multiplicity of `π` at the closed points above `y`, and zero at the others: above `y` the
induced ideal is the one generated by the maximal ideal at `y`, whose colength is that local
multiplicity, and elsewhere the induced ideal is the unit ideal. -/
theorem ord_of_stalk_comap_vanishingIdeal_eq_span (y : closedPoints Y) (z : closedPoints X)
    {c : X.presheaf.stalk z.1}
    (hc : AlgebraicGeometry.IdealSheafData.stalk
      ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y.1} : Set Y))).comap π) z.1 =
        Ideal.span {c}) :
    X.ord (algebraMap (X.presheaf.stalk z.1) X.functionField c) z.1 =
      if π.base z.1 = y.1 then (π.ramificationLength z.1 : ℤ) else 0 := by
  have hcoh : coheight z.1 = 1 :=
    IsCurve.coheight_eq_one (f := gX) (ne_genericPoint_of_mem_closedPoints_of_isCurve gX z)
  rw [AlgebraicGeometry.IdealSheafData.stalk_comap] at hc
  split_ifs with hzy
  · rw [← hzy, AlgebraicGeometry.IdealSheafData.stalk_vanishingIdeal_closure_singleton
      (π.base z.1) (hzy ▸ y.2)] at hc
    have hc0 := ne_zero_of_stalk_comap_vanishingIdeal_eq_span gX gY π hπ hnc y z hzy hc
    have : IsDiscreteValuationRing (X.presheaf.stalk z.1) :=
      IsCurve.isDiscreteValuationRing_stalk_of_isClosed k gX z.2
    have : Ring.KrullDimLE 1 (X.presheaf.stalk z.1) := krullDimLE_of_coheight_le hcoh.le
    have hnt : Ring.ord (X.presheaf.stalk z.1) c ≠ ⊤ :=
      Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hc0)
    have hram : π.ramificationLength z.1 = (Ring.ord (X.presheaf.stalk z.1) c).toNat := by
      rw [Scheme.Hom.ramificationLength_eq, hc]
      rfl
    exact Stacks.Chow.ord_algebraMap_eq_ringOrd hcoh hc0 (by rw [hram, ENat.natCast_toNat hnt])
  · have hnot : π.base z.1 ∉ (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y.1} : Set Y))).support := by
      intro hmem
      have hmem' : π.base z.1 ∈ ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y.1} : Set Y))).support : Set Y) := hmem
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure,
        (y.2 : IsClosed ({y.1} : Set Y)).closure_eq, Set.mem_singleton_iff] at hmem'
      exact hzy hmem'
    rw [(AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 hnot,
      Ideal.map_top] at hc
    exact Scheme.ord_algebraMap_of_isUnit hcoh (Ideal.span_singleton_eq_top.1 hc.symm)

end Local

/-! ### The fibre divisor is the pullback of the point divisor -/

section PicardPullback

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup
  AlgebraicGeometry.schemePicardGroupAddCommGroup

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (gX : X ⟶ Spec (.of k))
  (gY : Y ⟶ Spec (.of k)) [IsCurve k gX] [IsCurve k gY] [Smooth gX] [Smooth gY]
  [IsProper gX] [IsProper gY] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [AlgebraicGeometry.IsNoetherian X] (π : X ⟶ Y) (hπ : π ≫ gY = gX)
  (hnc : ¬ ∃ y : Y, ∀ x : X, π.base x = y)

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [AlgebraicGeometry.IsNoetherian X]
  [IsAlgClosed k] [Smooth gX] [Smooth gY] in
open scoped Classical in
/-- The coefficient of the fibre divisor of a closed point `y` at a closed point `z` of `X` is the
local multiplicity of `π` at `z` when `z` lies above `y`, and zero otherwise. -/
theorem sum_single_ramificationLength_apply (y : closedPoints Y) (z : closedPoints X) :
    (∑ x ∈ (curveClosedPointFibre gX gY π hπ hnc y).attach,
        Finsupp.single x.1 (π.ramificationLength x.1.1 : ℤ)) z =
      if π.base z.1 = y.1 then (π.ramificationLength z.1 : ℤ) else 0 := by
  rw [Finset.sum_apply']
  split_ifs with hzy
  · have hz : z ∈ curveClosedPointFibre gX gY π hπ hnc y :=
      (mem_curveClosedPointFibre gX gY π hπ hnc y z).2 hzy
    refine (Finset.sum_eq_single_of_mem (⟨z, hz⟩ : ↥(curveClosedPointFibre gX gY π hπ hnc y))
      (Finset.mem_attach _ _) fun x _ hx => by
        exact Finsupp.single_eq_of_ne fun h => hx (Subtype.ext h.symm)).trans ?_
    exact Finsupp.single_eq_same
  · refine Finset.sum_eq_zero fun x _ => ?_
    refine Finsupp.single_eq_of_ne fun h => hzy ?_
    rw [h]
    exact (mem_curveClosedPointFibre gX gY π hπ hnc y x.1).1 x.2

omit [IsAlgClosed k] [IsLocallyNoetherian Y] in
include hπ hnc in
/-- **The fibre divisor of a closed point `y`, weighted by the local multiplicities of `π`, has
the pullback of `𝒪_Y(y)` as its line bundle.** Its coefficients are the orders of vanishing of a
local equation of the pullback of the divisor `y`
(`Stacks.EtaleCohomology.ord_of_stalk_comap_vanishingIdeal_eq_span`), and the pullback of the
divisor `y` has `π^*𝒪_Y(y)` as its line bundle (Tag 02OO (2) and Tag 01WV). -/
theorem curveClassGroupAddEquivSchemePicard_fibre (y : closedPoints Y) :
    curveClassGroupAddEquivSchemePicard gX
        (QuotientAddGroup.mk (∑ x ∈ (curveClosedPointFibre gX gY π hπ hnc y).attach,
          Finsupp.single x.1 (π.ramificationLength x.1.1 : ℤ)) : curveClassGroup gX) =
      schemePicardPullbackHom π (curveClassGroupAddEquivSchemePicard gY
        (QuotientAddGroup.mk (Finsupp.single y (1 : ℤ)) : curveClassGroup gY)) := by
  classical
  have : IsDominant π := isDominant_of_not_constant k gX gY π hnc
  have hDy := isEffectiveCartierDivisor_closedPoint gY y
  have hDX : Stacks.Divisors.IsEffectiveCartierDivisor
      ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y.1} : Set Y))).comap π) :=
    Stacks.Divisors.isPullbackDefined_of_isDominant π _ hDy
  have hR : schemePicardPullbackHom π (divisorSchemePicardClass
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y.1} : Set Y)))) =
      divisorSchemePicardClass
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y.1} : Set Y))).comap π) := by
    rw [← picardModelAddEquiv_picardClass, schemePicardPullbackHom_picardModelAddEquiv,
      Stacks.Divisors.schemePullbackClass_picardClass, picardModelAddEquiv_picardClass]
  rw [curveClassGroupAddEquivSchemePicard_single, hR]
  refine curveClassGroupAddEquivSchemePicard_mk_of_weilDivisorClass gX _ _ ?_
  refine weilDivisorClassOfInvertibleSheaf_eq_of_forall_ord _ _ fun Z c hc => ?_
  have h := weilDivisorAddEquivClosedPointDivisor_apply gX
    ((weilDivisorAddEquivClosedPointDivisor gX).symm
      (∑ x ∈ (curveClosedPointFibre gX gY π hπ hnc y).attach,
        Finsupp.single x.1 (π.ramificationLength x.1.1 : ℤ)))
    (primeDivisorEquivClosedPoints gX Z)
  rw [AddEquiv.apply_symm_apply, Equiv.symm_apply_apply] at h
  rw [← h, sum_single_ramificationLength_apply gX gY π hπ hnc y
    (primeDivisorEquivClosedPoints gX Z)]
  exact (ord_of_stalk_comap_vanishingIdeal_eq_span gX gY π hπ hnc y
    (primeDivisorEquivClosedPoints gX Z) hc).symm

end PicardPullback

/-! ### The degree of the pullback of a divisor class -/

section Degree

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse
attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup
  AlgebraicGeometry.schemePicardGroupAddCommGroup
attribute [local instance 10000] hasCoproduct_closedPointSkyscraper

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (gX : X ⟶ Spec (.of k))
  (gY : Y ⟶ Spec (.of k)) [IsCurve k gX] [IsCurve k gY] [Smooth gX] [Smooth gY]
  [IsProper gX] [IsProper gY] (π : X ⟶ Y) (hπ : π ≫ gY = gX)
  (hnc : ¬ ∃ y : Y, ∀ x : X, π.base x = y)

include hπ hnc in
/-- **Restriction on `H¹(-, 𝐆_m)` is pullback of divisor classes**: the two homomorphisms
`Cl(Y) → Cl(X)` agree, because the classes of the closed points generate `Cl(Y)` and both send
the class of a closed point `y` to the class of the fibre above `y` weighted by the local
multiplicities of `π` — for the one through `H¹(-, 𝐆_m)` by
`Stacks.EtaleCohomology.curveClassGroupRamifiedPullback_single`, and for pullback of line bundles
by `Stacks.EtaleCohomology.curveClassGroupAddEquivSchemePicard_fibre`. -/
theorem curveClassGroupRamifiedPullback_eq_curveClassGroupPullback (c : curveClassGroup gY) :
    curveClassGroupRamifiedPullback gX gY π c = curveClassGroupPullback gX gY π c := by
  have := isLocallyNoetherian_of_isCurve gX
  have := Stacks.ProjectiveSpaceSections.isNoetherian_of_isCurve gX
  have := isLocallyNoetherian_of_isCurve gY
  have := Stacks.ProjectiveSpaceSections.isNoetherian_of_isCurve gY
  have h : (curveClassGroupAddEquivSchemePicard gX).toAddMonoidHom.comp
      (curveClassGroupRamifiedPullback gX gY π) =
      (curveClassGroupAddEquivSchemePicard gX).toAddMonoidHom.comp
        (curveClassGroupPullback gX gY π) := by
    refine AddMonoidHom.eq_of_eqOn_dense (closure_range_closedPointClassGroup_single Y) ?_
    rintro _ ⟨y, rfl⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
    rw [curveClassGroupRamifiedPullback_single gX gY π hπ hnc y,
      curveClassGroupAddEquivSchemePicard_fibre gX gY π hπ hnc y,
      curveClassGroupAddEquivSchemePicard_curveClassGroupPullback]
  exact (curveClassGroupAddEquivSchemePicard gX).injective (DFunLike.congr_fun h c)

include hπ hnc in
/-- **The degree of the pullback of a divisor class along `π` is `deg(π)` times the degree**, the
pullback being restriction on `H¹(-, 𝐆_m)` read through `H¹(𝐆_m) ≅ Cl`. -/
theorem curveClassGroupDegree_curveClassGroupRamifiedPullback (c : curveClassGroup gY) :
    curveClassGroupDegree gX (curveClassGroupRamifiedPullback gX gY π c) =
      (@degreeOver X Y π _ _ (locallyOfFiniteType_of_isCurve_comp k gX gY π hπ)
          (isDominant_of_not_constant k gX gY π hnc) : ℤ) * curveClassGroupDegree gY c := by
  rw [curveClassGroupRamifiedPullback_eq_curveClassGroupPullback gX gY π hπ hnc]
  exact curveClassGroupDegree_curveClassGroupPullback gX gY π hπ hnc c

include hπ hnc in
/-- **The degree modulo `n` of a restricted class of `H¹(-, 𝐆_m)`** is `deg(π)` times the degree
modulo `n` of the class. -/
theorem sheafHOneMultiplicativeDegreeMod_multiplicativeRestriction (n : ℕ)
    (a : Sheaf.H.{u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} Y) 1) :
    sheafHOneMultiplicativeDegreeMod gX n
        (multiplicativeRestriction.{u, u + 1, u + 1} π 1 a) =
      ((@degreeOver X Y π _ _ (locallyOfFiniteType_of_isCurve_comp k gX gY π hπ)
            (isDominant_of_not_constant k gX gY π hnc) : ℕ) : ZMod n) *
        sheafHOneMultiplicativeDegreeMod gY n a := by
  have h : sheafHOneMultiplicativeAddEquivClosedPointClassGroup gX
        (multiplicativeRestriction.{u, u + 1, u + 1} π 1 a) =
      curveClassGroupRamifiedPullback gX gY π
        (sheafHOneMultiplicativeAddEquivClosedPointClassGroup gY a) := by
    change _ = sheafHOneMultiplicativeAddEquivClosedPointClassGroup gX
      (multiplicativeRestriction.{u, u + 1, u + 1} π 1
        ((sheafHOneMultiplicativeAddEquivClosedPointClassGroup gY).symm
          (sheafHOneMultiplicativeAddEquivClosedPointClassGroup gY a)))
    rw [AddEquiv.symm_apply_apply]
  rw [sheafHOneMultiplicativeDegreeMod_apply, sheafHOneMultiplicativeDegreeMod_apply,
    curveClassGroupDegreeMod_apply, curveClassGroupDegreeMod_apply, h,
    curveClassGroupDegree_curveClassGroupRamifiedPullback gX gY π hπ hnc, Int.cast_mul,
    Int.cast_natCast]

end Degree

/-! ### Pullback on `H²(-, μ_n)` is multiplication by the degree -/

section Main

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse
attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup
  AlgebraicGeometry.schemePicardGroupAddCommGroup
attribute [local instance 10000] hasCoproduct_closedPointSkyscraper

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (gX : X ⟶ Spec (.of k))
  (gY : Y ⟶ Spec (.of k)) [IsCurve k gX] [IsCurve k gY] [Smooth gX] [Smooth gY]
  [IsProper gX] [IsProper gY] (π : X ⟶ Y) (hπ : π ≫ gY = gX)
  (hnc : ¬ ∃ y : Y, ∀ x : X, π.base x = y) {n : ℕ} (hn : IsUnit (n : k))

/-- **[Stacks, Tag 0AMB].**  Let `k` be an algebraically closed field, let `π : X ⟶ Y` be a
nonconstant morphism of smooth proper curves over `k`, and let `n` be invertible in `k`.  In the
coordinates of `Stacks.EtaleCohomology.sheafHTwoRootsOfUnityAddEquivZMod`, which identify both
`H²_étale(Y, μ_n)` and `H²_étale(X, μ_n)` with `𝐙/n𝐙`, the pullback

`π^* : H²_étale(Y, μ_n) ⟶ H²_étale(X, μ_n)`

is multiplication by the degree `deg(X/Y) = [R(X) : R(Y)]` of the extension of function fields
([Stacks, Tag 02NY]).

The proof is the source's.  Every class of `H²_étale(Y, μ_n)` is the Kummer coboundary of a class
`a` of `H¹_étale(Y, 𝐆_m)` ([Stacks, Tag 03RM]), and the coordinate of that coboundary is the
degree of `a` modulo `n`.  Restriction along `π` commutes with the Kummer coboundary
(`Stacks.Kummer.etaleCohomologyRestrictionMap_kummerExtClass`), so the coordinate of the
restricted class is the degree of the restriction of `a`, which is `deg(X/Y)` times the degree of
`a` by `Stacks.EtaleCohomology.sheafHOneMultiplicativeDegreeMod_multiplicativeRestriction` —
and that is where nonconstancy of `π` is used, through the rank-one case of [Stacks, Tag 0AYZ]. -/
@[stacks 0AMB "for a nonconstant morphism pi : X -> Y of smooth proper curves over an \
algebraically closed field k and n invertible in k, the pullback pi^* : H^2_etale(Y, mu_n) -> \
H^2_etale(X, mu_n) is multiplication by the degree of pi, under the canonical identifications \
H^2_etale(-, mu_n) = Z/nZ of Stacks 03RQ (sheafHTwoRootsOfUnityAddEquivZMod), given by the Kummer \
coboundary of H^1_etale(-, G_m) = Cl(-) = Pic(-) followed by the degree"]
theorem sheafHTwoRootsOfUnityAddEquivZMod_rootsOfUnityRestriction
    (x : Sheaf.H.{u + 1} (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} Y n) 2) :
    sheafHTwoRootsOfUnityAddEquivZMod gX hn
        (rootsOfUnityRestriction.{u, u + 1, u + 1} π n 2 x) =
      ((@degreeOver X Y π _ _ (locallyOfFiniteType_of_isCurve_comp k gX gY π hπ)
            (isDominant_of_not_constant k gX gY π hnc) : ℕ) : ZMod n) *
        sheafHTwoRootsOfUnityAddEquivZMod gY hn x := by
  obtain ⟨a, rfl⟩ := exists_curveKummerCoboundary_eq gY hn x
  have hbox : rootsOfUnityRestriction.{u, u + 1, u + 1} π n 2 (curveKummerCoboundary gY hn a) =
      curveKummerCoboundary gX hn (multiplicativeRestriction.{u, u + 1, u + 1} π 1 a) :=
    Stacks.Kummer.etaleCohomologyRestrictionMap_kummerExtClass.{u, u + 1, u + 1} π
      (ne_zero_of_isUnit_natCast hn) (isUnit_natCast_globalSections_of_isUnit gY hn) 1 2 rfl a
  rw [hbox, sheafHTwoRootsOfUnityAddEquivZMod_curveKummerCoboundary,
    sheafHTwoRootsOfUnityAddEquivZMod_curveKummerCoboundary,
    sheafHOneMultiplicativeDegreeMod_multiplicativeRestriction gX gY π hπ hnc]

end Main

end Stacks.EtaleCohomology

end
