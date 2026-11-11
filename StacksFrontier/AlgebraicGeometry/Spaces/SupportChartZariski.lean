module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedMinimalSupport

/-!
# The support of a module on an étale scheme chart

Let `X` be an algebraic space over a scheme `S`, let `F` be an `𝒪_X`-module and let
`φ : U → X` be an étale morphism from a scheme, that is, an object of the small étale site
`AlgebraicGeometry.Space.SmallEtale` of `X`.  Two supports are attached to this situation: the
support `AlgebraicGeometry.Space.supportOfSheaf` of Stacks 04KA, a set of points of `X` cut out
by nonvanishing of the geometric stalks, and the ordinary support `SheafOfModules.supp` of the
restriction `AlgebraicGeometry.Space.restrictToChart` of `F` to the scheme `chartScheme U`, a
set of points of that scheme cut out by nonvanishing of the Zariski stalks.  **Stacks 07TY**
asserts that the second is the inverse image of the first,
`Supp(φ^* F) = |φ|^{-1}(Supp(F))`.

Its proof has exactly two inputs: the comparison `(φ^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄} = F_{x̄}` of
Stacks 05VP, and faithful flatness of the ring map that comparison base changes along.  The
second is available here as
`AlgebraicGeometry.Space.faithfullyFlat_chartLocalRingToEtaleLocalRing`.  The first is proved
for a quasi-coherent module in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartStalkTensorIsomorphism.lean`, not imported here;
so the support equality is proved here for every module for which the comparison holds,
and Stacks 07TY itself, for a quasi-coherent module, is
`AlgebraicGeometry.Space.supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent` in
`StacksFrontier/AlgebraicGeometry/Spaces/SupportGeometricStalkCriterion.lean`.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtaleNeighborhood.ofChartGeometricPoint` turns a geometric point
  of the algebraic space represented by an étale chart into a small étale neighbourhood of its
  image in `X` whose chart is that chart.  It inverts
  `AlgebraicGeometry.Space.neighborhoodPoint`, and it is what moves a point of the scheme
  underlying the chart to the configuration `AlgebraicGeometry.Space.chartZariskiModuleStalk`
  is stated for.

## Main results

* `Stacks.mem_supp_iff_nontrivial_moduleStalkLarge`: on a scheme, membership in the support of
  a sheaf of modules is nonvanishing of the stalk at the corresponding point of the Zariski
  *site*, in the form `Stacks.moduleStalkLarge` in which that stalk enters Stacks 05VP.  Both
  nonvanishing conditions are rephrased, by
  `Stacks.germ_eq_zero_iff_exists_restrict_eq_zero` and
  `Stacks.moduleStalkLargeGerm_eq_zero_iff_exists_restrict_eq_zero`, as the existence of a
  section over an open neighbourhood which no further shrinking kills.
* `AlgebraicGeometry.Space.nontrivial_chartZariskiModuleStalk_iff_mem_supp`: the right factor of
  the tensor product of Stacks 05VP is nonzero exactly when the point of the chart underlying
  the geometric point lies in the support of the chart restriction.
* `AlgebraicGeometry.Space.subsingleton_chartStalkTensorEtaleLocalRing_iff` and
  `AlgebraicGeometry.Space.nontrivial_chartStalkTensorEtaleLocalRing_iff`: the left-hand side of
  Stacks 05VP vanishes exactly when the Zariski stalk does.  This is the step "it is faithfully
  flat, so faithful flatness forces the equivalence" of the proof of Stacks 07TY.
* `AlgebraicGeometry.Space.nontrivial_chartStalkTensorEtaleLocalRing_iff_mem_supp`: the two
  previous results combined — the left-hand side of Stacks 05VP is nonzero exactly when the
  chart point lies in the support of the chart restriction.
* `AlgebraicGeometry.Space.supp_restrictToChart_eq_preimage_supportOfSheaf`: the equality of
  the Zariski support of the chart restriction with the inverse image of the support on the
  space, for a module satisfying the comparison isomorphism of Stacks 05VP; Stacks 07TY follows
  from it once that comparison is proved for quasi-coherent modules.

## Implementation notes

The module universe is the universe `u` of the schemes throughout, because `SheafOfModules.supp`
is stated for a sheaf of modules whose sections, coefficient rings and space share one universe.
`AlgebraicGeometry.Space.restrictToChart` produces a `SheafOfModules.{max u m}` from a
`Modules.{u, m}`, so taking `m = u` is what makes the ordinary support of the restriction
expressible at all.

**The comparison hypothesis.**  The hypothesis of
`AlgebraicGeometry.Space.supp_restrictToChart_eq_preimage_supportOfSheaf` is the isomorphism
`(φ^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄} ≅ F_{x̄}` of Stacks 05VP, a lemma of a different chapter whose
statement mentions no support at all.  Both of its sides are constructed here,
`AlgebraicGeometry.Space.chartStalkTensorEtaleLocalRing` and
`AlgebraicGeometry.Space.geometricModuleStalk`.  For a quasi-coherent `F` the isomorphism is
`AlgebraicGeometry.Space.isIso_chartStalkTensorComparison`, in a module not imported here;
quasi-coherence of `F` enters the proof of Stacks 07TY only through it, so stating the
equality under the comparison makes it apply to every module for which the comparison holds.

The support of Stacks 04KA is nonvanishing of a *geometric* stalk, which
`AlgebraicGeometry.Space.mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk` expresses as
nonvanishing of `AlgebraicGeometry.Space.geometricModuleStalk`.  The support is defined by the
existence of *some* geometric point above a point with nonzero stalk, so the two inclusions of
the main result use different inputs: the forward one needs only a geometric representative of
the point of the chart (`AlgebraicGeometry.Space.exists_geometricRepresentative`), while the
reverse one has to produce a geometric point of the chart over a prescribed point of the chart
whose image is the *given* geometric point of `X`, which is Stacks 05VN,
`AlgebraicGeometry.Space.exists_geometricPoint_lift_of_isEtale`.

Objects of `AlgebraicGeometry.Space.SmallEtale` are by definition the representable morphisms
`φ : yoneda.obj U ⟶ X` all of whose represented base changes are étale, for `U` an object of the
big fppf site; so quantifying over them is exactly the hypothesis "`U` is a scheme and
`φ : U → X` is étale" of Stacks 07TY, and the étaleness of `φ` needed by Stacks 05VN is supplied
by `AlgebraicGeometry.Space.isEtale_chartToSpace` rather than assumed.  The identification of
the points of the chart scheme with the points of the presheaf it represents is clause (1) of
Stacks 03BX, `AlgebraicGeometry.Space.pointsEquivScheme`; the map `|φ|` of the statement is the
map on points of the presheaves read through it.

The two nonvanishing criteria of `Stacks.mem_supp_iff_nontrivial_moduleStalkLarge` are compared
through germs rather than by constructing a comparison map of the two stalks: the colimit
`Stacks.moduleStalkLarge` is taken over a small final model of the category of elements of the
fibre functor, so writing down an isomorphism to the Zariski stalk would mean transporting along
that final model, while the germ criteria on the two sides are literally the same condition on
sections.  The fibre of `Opens.pointGrothendieckTopology x` at an open `O` is
`ULift (PLift (x ∈ O))`, a subsingleton, so the compatibility of fibre elements that
`Stacks.moduleStalkLargeGerm_eq_iff` asks for is automatic.

## References

* [Stacks Project, Lemma 67.15.1 (Tag 07TY)](https://stacks.math.columbia.edu/tag/07TY)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 05VN](https://stacks.math.columbia.edu/tag/05VN)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks

/-! ### The support of a sheaf of modules on a scheme and the stalk at a point of the site -/

variable (T : Scheme.{u}) (M : SheafOfModules.{u} T.ringCatSheaf) (x : T)

/-- The germ at `x` of a section of a sheaf of modules on a scheme vanishes exactly when the
section is killed by restriction to some open neighbourhood of `x`. -/
theorem germ_eq_zero_iff_exists_restrict_eq_zero (O : TopologicalSpace.Opens T) (hO : x ∈ O)
    (s : M.val.obj (op O)) :
    (show TopCat.Presheaf Ab.{u} T.toTopCat from M.val.presheaf).germ O x hO s = 0 ↔
      ∃ (W : TopologicalSpace.Opens T) (iW : W ⟶ O), x ∈ W ∧ M.val.map iW.op s = 0 := by
  constructor
  · intro h
    obtain ⟨W, hW, iU, _, he⟩ :=
      (show TopCat.Presheaf Ab.{u} T.toTopCat from M.val.presheaf).germ_eq x hO hO s
        (0 : M.val.obj (op O)) (h.trans (map_zero _).symm)
    exact ⟨W, iU, hW, he.trans (map_zero _)⟩
  · rintro ⟨W, iW, hW, he⟩
    refine Eq.trans ((show TopCat.Presheaf Ab.{u} T.toTopCat from M.val.presheaf).germ_ext
      (hxU := hO) (hxV := hO) W hW iW iW (sU := s) (sV := (0 : M.val.obj (op O))) ?_)
      (map_zero _)
    exact he.trans (map_zero _).symm

/-- The germ of a section in the stalk at the point of the Zariski *site* attached to `x`
vanishes exactly when the section is killed by restriction to some open neighbourhood of `x`:
the same condition as for the germ in the ordinary stalk. -/
theorem moduleStalkLargeGerm_eq_zero_iff_exists_restrict_eq_zero
    (O : TopologicalSpace.Opens T)
    (hO : (_root_.Opens.pointGrothendieckTopology x).fiber.obj O)
    (s : M.val.obj (op O)) :
    moduleStalkLargeGerm.{u} (_root_.Opens.pointGrothendieckTopology x) T.sheaf M O hO s = 0 ↔
      ∃ (W : TopologicalSpace.Opens T) (iW : W ⟶ O), x ∈ W ∧ M.val.map iW.op s = 0 := by
  constructor
  · intro h
    obtain ⟨W, iW, y, -, he⟩ :=
      (moduleStalkLargeGerm_eq_iff.{u} (_root_.Opens.pointGrothendieckTopology x)
        T.sheaf M O hO s 0).mp (h.trans (map_zero _).symm)
    exact ⟨W, iW, y.down.down, he.trans (map_zero _)⟩
  · rintro ⟨W, iW, hW, he⟩
    exact Eq.trans ((moduleStalkLargeGerm_eq_iff.{u}
      (_root_.Opens.pointGrothendieckTopology x) T.sheaf M O hO s 0).mpr
        ⟨W, iW, ⟨⟨hW⟩⟩, Subsingleton.elim _ _, he.trans (map_zero _).symm⟩) (map_zero _)

/-- **The support of a sheaf of modules on a scheme is the nonvanishing locus of the stalk at
the corresponding point of the Zariski site.**  The site-theoretic stalk is
`Stacks.moduleStalkLarge` at the point `Opens.pointGrothendieckTopology x`, which is the form in
which the Zariski stalk enters Stacks 05VP as
`AlgebraicGeometry.Space.chartZariskiModuleStalk`.

Both sides say that some section over some open neighbourhood of `x` survives every further
shrinking, by `Stacks.germ_eq_zero_iff_exists_restrict_eq_zero` on the left and
`Stacks.moduleStalkLargeGerm_eq_zero_iff_exists_restrict_eq_zero` on the right. -/
theorem mem_supp_iff_nontrivial_moduleStalkLarge :
    x ∈ SheafOfModules.supp M ↔
      Nontrivial (moduleStalkLarge.{u} (_root_.Opens.pointGrothendieckTopology x) T.sheaf M) := by
  have key : ∀ O hO s,
      (show TopCat.Presheaf Ab.{u} T.toTopCat from M.val.presheaf).germ O x hO s = 0 ↔
        moduleStalkLargeGerm.{u} (_root_.Opens.pointGrothendieckTopology x) T.sheaf M O
          ⟨⟨hO⟩⟩ s = 0 := fun O hO s =>
    (germ_eq_zero_iff_exists_restrict_eq_zero T M x O hO s).trans
      (moduleStalkLargeGerm_eq_zero_iff_exists_restrict_eq_zero T M x O ⟨⟨hO⟩⟩ s).symm
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨O, hO, s, rfl⟩ :=
      (show TopCat.Presheaf Ab.{u} T.toTopCat from M.val.presheaf).exists_germ_eq a
    exact (nontrivial_iff_exists_ne _).mpr ⟨_, fun h => ha ((key O hO s).mpr h)⟩
  · intro hnt
    obtain ⟨z, hz⟩ := (nontrivial_iff_exists_ne _).mp hnt
    obtain ⟨O, hO, s, rfl⟩ :=
      moduleStalkLargeGerm_jointly_surjective.{u} (_root_.Opens.pointGrothendieckTopology x)
        T.sheaf M z
    exact ⟨_, fun h => hz ((key O hO.down.down s).mp h)⟩

end Stacks

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-! ### The right factor of Stacks 05VP and the support on the chart -/

/-- **The right factor of the tensor product of Stacks 05VP is nonzero exactly when the chart
point lies in the support of the chart restriction.**  The Zariski stalk
`AlgebraicGeometry.Space.chartZariskiModuleStalk` is the stalk of the restriction of `F` to the
chart at the point of the Zariski site attached to
`AlgebraicGeometry.Space.chartPoint`, with its scalars restricted; restriction of scalars does
not change the underlying type, so the criterion is
`Stacks.mem_supp_iff_nontrivial_moduleStalkLarge`. -/
theorem nontrivial_chartZariskiModuleStalk_iff_mem_supp
    {x : GeometricPoint B S hS X} (V : SmallEtaleNeighborhood x)
    (F : Modules.{u, u} B S hS X hX) :
    Nontrivial (chartZariskiModuleStalk.{u, u} B S hS X hX V F) ↔
      chartPoint B S hS X V ∈ SheafOfModules.supp (restrictToChart B S hS hX F V.chart) :=
  (Stacks.mem_supp_iff_nontrivial_moduleStalkLarge (chartScheme V.chart)
    (restrictToChart B S hS hX F V.chart) (chartPoint B S hS X V)).symm

/-! ### Faithful flatness of the base change of Stacks 05VP -/

include hX

/-- **Faithful flatness forces the equivalence of the two vanishings.**  The left-hand side of
Stacks 05VP — the Zariski stalk of the chart restriction, base changed to the étale local ring
at the geometric point — vanishes exactly when the Zariski stalk itself vanishes, because the
ring map along which the base change is taken is faithfully flat
(`AlgebraicGeometry.Space.faithfullyFlat_chartLocalRingToEtaleLocalRing`, which is Stacks 04KF
together with faithful flatness of a strict henselization). -/
theorem subsingleton_chartStalkTensorEtaleLocalRing_iff
    {x : GeometricPoint B S hS X} (V : SmallEtaleNeighborhood x)
    (F : Modules.{u, u} B S hS X hX) :
    Subsingleton (chartStalkTensorEtaleLocalRing.{u, u} B S hS X hX V F) ↔
      Subsingleton (chartZariskiModuleStalk.{u, u} B S hS X hX V F) := by
  let _ : Algebra ↥(chartLocalRing B S hS X V) ↥(etaleLocalRing B S hS X x) :=
    (chartLocalRingToEtaleLocalRing B S hS X hX V).toAlgebra
  have _ : Module.FaithfullyFlat ↥(chartLocalRing B S hS X V)
      ↥(etaleLocalRing B S hS X x) :=
    faithfullyFlat_chartLocalRingToEtaleLocalRing B S hS X hX V
  exact Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right
    ↥(chartLocalRing B S hS X V) ↥(etaleLocalRing B S hS X x)

/-- The nonvanishing form of
`AlgebraicGeometry.Space.subsingleton_chartStalkTensorEtaleLocalRing_iff`. -/
theorem nontrivial_chartStalkTensorEtaleLocalRing_iff
    {x : GeometricPoint B S hS X} (V : SmallEtaleNeighborhood x)
    (F : Modules.{u, u} B S hS X hX) :
    Nontrivial (chartStalkTensorEtaleLocalRing.{u, u} B S hS X hX V F) ↔
      Nontrivial (chartZariskiModuleStalk.{u, u} B S hS X hX V F) := by
  rw [← not_subsingleton_iff_nontrivial, ← not_subsingleton_iff_nontrivial,
    subsingleton_chartStalkTensorEtaleLocalRing_iff B S hS X hX V F]

/-- **The left-hand side of Stacks 05VP is nonzero exactly when the chart point lies in the
support of the chart restriction.**  This is the whole of the proof of Stacks 07TY except for
the comparison asserted by Stacks 05VP itself
(`AlgebraicGeometry.Space.isIso_chartStalkTensorComparison`): with that comparison, the right-hand side is the
geometric stalk, whose nonvanishing is membership in the support of Stacks 04KA by
`AlgebraicGeometry.Space.mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk`. -/
theorem nontrivial_chartStalkTensorEtaleLocalRing_iff_mem_supp
    {x : GeometricPoint B S hS X} (V : SmallEtaleNeighborhood x)
    (F : Modules.{u, u} B S hS X hX) :
    Nontrivial (chartStalkTensorEtaleLocalRing.{u, u} B S hS X hX V F) ↔
      chartPoint B S hS X V ∈ SheafOfModules.supp (restrictToChart B S hS hX F V.chart) :=
  (nontrivial_chartStalkTensorEtaleLocalRing_iff B S hS X hX V F).trans
    (nontrivial_chartZariskiModuleStalk_iff_mem_supp B S hS X hX V F)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (U : SmallEtale B S hS X.1)

/-! ### Small étale neighbourhoods from geometric points of a chart -/

/-- The small étale neighbourhood of `X` determined by a geometric point `y` of the algebraic
space represented by an étale chart `U`: the chart is `U` itself and the chosen lift of the
image geometric point of `X` is the section defining `y`.

This inverts `AlgebraicGeometry.Space.neighborhoodPoint`, which reads off from a small étale
neighbourhood the geometric point of its chart; see
`AlgebraicGeometry.Space.neighborhoodPoint_ofChartGeometricPoint`. -/
noncomputable def SmallEtaleNeighborhood.ofChartGeometricPoint
    (y : GeometricPoint B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U))) :
    SmallEtaleNeighborhood (geometricPointMap U.obj.hom y) where
  chart := U
  point := y.val.value
  point_comp := rfl

/-- The chart of `AlgebraicGeometry.Space.SmallEtaleNeighborhood.ofChartGeometricPoint` is the
chart it was built from. -/
@[simp]
theorem SmallEtaleNeighborhood.ofChartGeometricPoint_chart
    (y : GeometricPoint B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U))) :
    (SmallEtaleNeighborhood.ofChartGeometricPoint B S hS X U y).chart = U :=
  rfl

/-- `AlgebraicGeometry.Space.SmallEtaleNeighborhood.ofChartGeometricPoint` is a section of
`AlgebraicGeometry.Space.neighborhoodPoint`. -/
@[simp]
theorem neighborhoodPoint_ofChartGeometricPoint
    (y : GeometricPoint B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U))) :
    neighborhoodPoint B S hS X.1
        (SmallEtaleNeighborhood.ofChartGeometricPoint B S hS X U y) = y :=
  rfl

/-- The point of the chart scheme at which
`AlgebraicGeometry.Space.SmallEtaleNeighborhood.ofChartGeometricPoint` takes its Zariski stalk
is the point of the chart scheme underlying the geometric point it was built from. -/
@[simp]
theorem chartPoint_ofChartGeometricPoint
    (y : GeometricPoint B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U))) :
    chartPoint B S hS X.1 (SmallEtaleNeighborhood.ofChartGeometricPoint B S hS X U y) =
      pointsToScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U) y.image :=
  rfl

/-! ### The support equality of Stacks 07TY under the comparison of Stacks 05VP -/

/-- **The support of a chart restriction is the inverse image of the support, given the
comparison of Stacks 05VP.** Let `X` be an algebraic space over `S`, let `F` be an `𝒪_X`-module
satisfying the comparison isomorphism of Stacks 05VP and let `φ : U ⟶ X` be an étale morphism from a scheme, that is, an object of the small étale site of
`X`.  Then the support of `φ^* F` as a module on the *scheme* `U` is the inverse image under
`|φ|` of the support of `F` on `X`:
`Supp(φ^* F) = |φ|^{-1}(Supp(F))`.

The hypothesis `hcomp` is the comparison of Stacks 05VP,
`(φ^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄} ≅ F_{x̄}`.  It holds for a quasi-coherent `F`
(`AlgebraicGeometry.Space.isIso_chartStalkTensorComparison`), and Stacks 07TY in exactly its
own hypotheses is
`AlgebraicGeometry.Space.supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent`,
which is this result with the comparison supplied.  Beyond the comparison the proof uses:
faithful flatness of the base change, which turns the comparison into the equivalence of the
two vanishings
(`AlgebraicGeometry.Space.nontrivial_chartStalkTensorEtaleLocalRing_iff_mem_supp`), a geometric
representative of a point of the chart for one inclusion
(`AlgebraicGeometry.Space.exists_geometricRepresentative`), and the étale lift of a geometric
point, Stacks 05VN, for the other
(`AlgebraicGeometry.Space.exists_geometricPoint_lift_of_isEtale`). -/
theorem supp_restrictToChart_eq_preimage_supportOfSheaf
    (F : Modules.{u, u} B S hS X.1 X.2)
    (hcomp : ∀ (x : GeometricPoint B S hS X.1) (V : SmallEtaleNeighborhood x),
      Nonempty (chartStalkTensorEtaleLocalRing.{u, u} B S hS X.1 X.2 V F ≅
        geometricModuleStalk B S hS X x F)) :
    SheafOfModules.supp (restrictToChart B S hS X.2 F U) =
      (fun u => pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U))
          U.obj.hom
          ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).symm u)) ⁻¹'
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) := by
  have key : ∀ (y : GeometricPoint B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U))),
      Nontrivial (geometricModuleStalk B S hS X (geometricPointMap U.obj.hom y) F) ↔
        pointsToScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U) y.image ∈
          SheafOfModules.supp (restrictToChart B S hS X.2 F U) := by
    intro y
    refine Iff.trans ?_
      (nontrivial_chartStalkTensorEtaleLocalRing_iff_mem_supp B S hS X.1 X.2
        (SmallEtaleNeighborhood.ofChartGeometricPoint B S hS X U y) F)
    exact (Equiv.ofBijective _ (ConcreteCategory.bijective_of_isIso
      (hcomp (geometricPointMap U.obj.hom y)
          (SmallEtaleNeighborhood.ofChartGeometricPoint B S hS X U y)).some.hom)
      ).nontrivial_congr.symm
  ext u
  have hyu : pointsToScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)
      ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).symm u) = u :=
    (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).apply_symm_apply u
  constructor
  · intro hu
    obtain ⟨ybar, hybar⟩ := exists_geometricRepresentative B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U))
      ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).symm u)
    refine (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X F _).mpr
      ⟨geometricPointMap U.obj.hom ybar, ?_, (key ybar).mpr ?_⟩
    · exact (geometricPointMap_image U.obj.hom ybar).trans (congrArg _ hybar)
    · rw [hybar, hyu]
      exact hu
  · intro hu
    obtain ⟨xbar, hlies, hnt⟩ :=
      (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X F _).mp hu
    obtain ⟨ybar, hyb, hval⟩ := exists_geometricPoint_lift_of_isEtale B S hS
      (isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS X.1).obj U)) X.2
      U.obj.hom (isEtale_chartToSpace B S hS X U) xbar _ hlies.symm
    have hxy : geometricPointMap U.obj.hom ybar = xbar := Subtype.ext hval
    have hmem := (key ybar).mp (hxy ▸ hnt)
    rwa [hyb, hyu] at hmem

end AlgebraicGeometry.Space

end
