module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionGeometricLength
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAtGeometricPointEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable

/-!
# Relative flatness of a module is unchanged by a closed immersion of algebraic spaces

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, let `g : X ⟶ T` be a morphism of algebraic spaces and let `G` be an
`𝒪_Z`-module.  This file proves that `G` is flat over `T` at a geometric point `z̄` of `Z`
exactly when the direct image `i_*G` is flat over `T` at the image geometric point `i(z̄)`, and
deduces that flatness of `i_*G` over `T` in the sense of Stacks 05VV forces flatness of `G`
over `T`.

This is the flatness analogue of Stacks 0EE3, which is the same statement for the length at a
geometric point, and it rests on the same stalk comparison: the stalk `(i_*G)_{i(z̄)}` is the
stalk `G_{z̄}`, semilinearly over the germ map `𝒪_{X, i(z̄)} → 𝒪_{Z, z̄}` of étale local rings
of Stacks 04NG.  Restricting the scalars of both sides along `𝒪_{T, t̄} → 𝒪_{X, i(z̄)}` turns
that comparison into an isomorphism of `𝒪_{T, t̄}`-modules, because the germ map of the
composite `i ≫ g` is the composite of the two germ maps
(`AlgebraicGeometry.Space.etaleLocalRingMap_comp`).  So the two flatness conditions are
flatness of one and the same `𝒪_{T, t̄}`-module.

The direct image is `AlgebraicGeometry.Space.chartDirectImage`, the direct image of modules
along base change of étale scheme charts, which is available because a closed immersion is
representable.  See the implementation notes for what separates it from
`AlgebraicGeometry.Space.modulePushforward`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_chartDirectImage_iff`: **the direct image
  along a closed immersion neither creates nor destroys relative flatness at a geometric
  point.**  No hypothesis beyond the closed immersion; in particular no quasi-coherence of `G`.
* `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_chartDirectImage_of_isFlatOver`: if `G`
  is flat over `T` in the sense of Stacks 05VV then `i_*G` is flat over `T` at every geometric
  point of `X` in the image of `i`.
* `AlgebraicGeometry.Space.isFlatOver_of_isFlatOver_chartDirectImage`: **flatness of `i_*G`
  over `T` implies flatness of `G` over `T`**, both in the sense of Stacks 05VV.  This is
  unconditional apart from the quasi-coherence that Stacks 05VU needs on each side.

## Implementation notes

The pointwise statement is proved at an arbitrary module universe `m`; the statement about
`AlgebraicGeometry.Space.IsFlatOver` is at `m = u`, the universe of the structure rings, which
is where that predicate is stated.

The module structures are introduced by `let` in exactly the shape in which
`AlgebraicGeometry.Space.IsFlatOverAtGeometricPoint` introduces them, namely
`Module.compHom` along the germ map of Stacks 04NG, so that a hypothesis of that form is
accepted as a `Module.Flat` statement about them and conversely.  This is the convention of
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_comp` in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleComposition.lean`.

The semilinear comparison of stalks is used through
`AlgebraicGeometry.Space.geometricStalkPushforwardMap` and its two companion results rather
than through `AlgebraicGeometry.Space.geometricStalkPushforwardAddEquiv`, because the linear
equivalence over `𝒪_{T, t̄}` is assembled from the underlying function, its additivity and its
semilinearity, and the inverse is produced from bijectivity.

**The direct image.** `AlgebraicGeometry.Space.chartDirectImage` is
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, whose sections over an étale chart
`V` of `X` are the sections of `G` over the base-changed chart `Z ×_X V`, on the nose.  It is
not identified in this development with `AlgebraicGeometry.Space.modulePushforward`, the
realization of Stacks 03LU; the two comparisons that identification needs are listed in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeRestriction.lean`.  Consequently the
results here do not apply verbatim to
`AlgebraicGeometry.Space.pushforwardStructureSheaf` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraDegreeZero.lean`, which is built from
`AlgebraicGeometry.Space.structureSharp`.  The same separation is recorded in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionGeometricLength.lean`, whose form of
Stacks 0EE3 is stated for the same direct image.

**What the converse direction needs, and where it is done.** The implication opposite to
`AlgebraicGeometry.Space.isFlatOver_of_isFlatOver_chartDirectImage` — flatness of `G` over `T`
implies flatness of `i_*G` over `T` — does not follow from the pointwise equivalence alone,
because `AlgebraicGeometry.Space.IsFlatOver` of `i_*G` is a condition at *every* geometric
point of `X`, including those outside the image of `i`, where the pointwise equivalence says
nothing.  What is needed there is the vanishing of `(i_*G)_{x̄}` at a geometric point `x̄` of
`X` not in the image of `i`, which is the geometric-stalk form of the inclusion
`Supp(i_*G) ⊆ |Z|`.

**That vanishing is available.** The inclusion is
`AlgebraicGeometry.Space.supportOfSheaf_smallEtaleAbelianPushforward_subset`, the half of
Stacks 04FX away from the subspace, which holds for the direct image of any abelian sheaf; and
nontriviality of a geometric stalk is membership of the point it lies over in the support, by
`AlgebraicGeometry.Space.mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk`. A module with
at most one element is flat, so the points outside the image cost nothing —
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_of_subsingleton_geometricModuleStalk` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleAtGeometricPoint.lean`.

The converse is still not stated here for a general `G`, because what the argument needs is the
support *equality* `Supp(i_*G) = |i|(|Z|)`, and the inclusion above is only one half of it: the
other half asks the support of `G` to be all of `|Z|`, which is special to `G = 𝒪_Z`. For that
case the converse is
`AlgebraicGeometry.Space.isFlatOver_chartDirectImage_structureSheafModule_of_isFlat` of
`StacksFrontier/AlgebraicGeometry/Quot/HilbertFamilyStructureSheafDictionary.lean`, the forward
flatness entry of the dictionary of Stacks 0D00, and
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_chartDirectImage_of_isFlatOver` is what it
uses at the points in the image.

## References

* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 0EE3](https://stacks.math.columbia.edu/tag/0EE3)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Z X T : AlgebraicSpaces B S hS}

/-- **Relative flatness at a geometric point is unchanged by a closed immersion.**  Let
`i : Z ⟶ X` be a closed immersion of algebraic spaces, let `g : X ⟶ T` and let `G` be an
`𝒪_Z`-module.  For a geometric point `z̄` of `Z`, the direct image `i_*G` is flat over `T` at
`i(z̄)` exactly when `G` is flat over `T` at `z̄`.

The stalk `(i_*G)_{i(z̄)}` is the stalk `G_{z̄}`, semilinearly over the germ map
`𝒪_{X, i(z̄)} → 𝒪_{Z, z̄}`, and the germ map of `i ≫ g` is the composite of the germ maps of
`i` and `g`.  So after restriction of scalars along `𝒪_{T, t̄} → 𝒪_{X, i(z̄)}` the two sides
are flatness of one and the same `𝒪_{T, t̄}`-module. -/
theorem isFlatOverAtGeometricPoint_chartDirectImage_iff (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (g : X ⟶ T)
    (G : Modules.{u, m} B S hS Z.1 Z.2) (zbar : GeometricPoint B S hS Z.1) :
    IsFlatOverAtGeometricPoint B S hS g (chartDirectImage B S hS i hi G)
        (geometricPointMap i.hom zbar) ↔
      IsFlatOverAtGeometricPoint B S hS (i ≫ g) G zbar := by
  set xbar := geometricPointMap i.hom zbar
  set Rt := etaleLocalRing B S hS T.1 (geometricPointMap g.hom xbar)
  set N := geometricModuleStalk B S hS X xbar (chartDirectImage B S hS i hi G)
  set M := geometricModuleStalk B S hS Z zbar G
  set α := etaleLocalRingMap Z.2 i.hom zbar
  set β := etaleLocalRingMap X.2 g.hom xbar
  set γ := etaleLocalRingMap Z.2 (i ≫ g).hom zbar
  have hαγ : γ = α.comp β := (etaleLocalRingMap_comp Z.2 X.2 i.hom g.hom zbar).symm
  let _ : Module Rt N := Module.compHom N β
  let _ : Module Rt M := Module.compHom M γ
  let Φ := geometricStalkPushforwardMap B S hS i hi zbar G
  let e : N ≃+ M := AddEquiv.ofBijective Φ
    ⟨injective_geometricStalkPushforwardMap B S hS i hi zbar G,
      surjective_geometricStalkPushforwardMap B S hS i hi zbar G⟩
  have hsmul : ∀ (c : Rt) (z : N), e (c • z) = c • e z := by
    intro c z
    change Φ (β c • z) = γ c • Φ z
    refine Eq.trans (geometricStalkPushforwardMap_smul B S hS i hi zbar G (β c) z) ?_
    exact congrArg (fun r => r • Φ z) (RingHom.congr_fun hαγ c).symm
  exact Module.Flat.equiv_iff (e.toLinearEquiv hsmul)

/-- Every geometric point of a space `Y` over `T` lies over a point of the source chart of some
commuting square of étale scheme charts. -/
private theorem exists_chartDiagram_chartPoint {Y : AlgebraicSpaces B S hS} (f : Y ⟶ T)
    (ybar : GeometricPoint B S hS Y.1) :
    ∃ (d : ChartDiagram B S hS Y.1 T.1 f.hom) (u : chartScheme d.U),
      ChartPoint B S hS d.U.obj.left d.U.obj.hom u ybar.image := by
  obtain ⟨V₀, b, hbSurjective, hbEtale⟩ := T.2.exists_atlas
  obtain ⟨U₀, a, k, hcomm, haSurjective, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS Y.2 T.2 f.hom V₀ b
      hbSurjective hbEtale
  obtain ⟨y, hy⟩ := (surjective_iff_surjective_pointsMap B S hS Y.1 Y.2 U₀ a).mp
    haSurjective ybar.image
  exact ⟨{ U := ⟨CostructuredArrow.mk a, haEtale⟩, V := ⟨CostructuredArrow.mk b, hbEtale⟩
           g := k, comm := hcomm }, pointsToScheme B S hS U₀ y,
    hy ▸ chartPoint_pointsToScheme B S hS U₀ a y⟩

/-- **Flatness of `G` over `T` gives flatness of `i_*G` over `T` at the geometric points of `X`
in the image of the closed immersion.**  This is the content the pointwise equivalence gives
towards the implication opposite to
`AlgebraicGeometry.Space.isFlatOver_of_isFlatOver_chartDirectImage`; the geometric points of
`X` outside the image of `i` are not reached by it. -/
theorem isFlatOverAtGeometricPoint_chartDirectImage_of_isFlatOver (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (g : X ⟶ T)
    (G : Modules.{u, u} B S hS Z.1 Z.2) [G.IsQuasicoherentOnSite]
    (h : IsFlatOver B S hS Z.2 (i ≫ g).hom G) (zbar : GeometricPoint B S hS Z.1) :
    IsFlatOverAtGeometricPoint B S hS g (chartDirectImage B S hS i hi G)
      (geometricPointMap i.hom zbar) := by
  refine (isFlatOverAtGeometricPoint_chartDirectImage_iff B S hS i hi g G zbar).2 ?_
  obtain ⟨d, u, hcp⟩ := exists_chartDiagram_chartPoint B S hS (i ≫ g) zbar
  obtain ⟨q, hq, -⟩ := exists_chartLift_of_chartPoint B S hS Z.2 zbar d.U _ hcp
  exact (isFlatOverAtOnChartDiagram_iff_isFlatOverAtGeometricPoint B S hS (i ≫ g) G
    ⟨d.U, q, hq⟩ d.V d.g d.comm).1 (h d _)

/-- **Flatness of the direct image along a closed immersion descends to the module.**  Let
`i : Z ⟶ X` be a closed immersion of algebraic spaces, let `g : X ⟶ T` and let `G` be a
quasi-coherent `𝒪_Z`-module whose direct image `i_*G` is quasi-coherent.  If `i_*G` is flat
over `T` in the sense of Stacks 05VV, then so is `G`.

Flatness of `i_*G` over `T` is in particular flatness at every geometric point of `X` in the
image of `i`, and the pointwise equivalence turns that into flatness of `G` at every geometric
point of `Z`, which is Stacks 05VV for `G` by Stacks 05VU.

Quasi-coherence of both modules is the hypothesis of Stacks 05VU, used once on each side; it
is not an input to the pointwise equivalence. -/
theorem isFlatOver_of_isFlatOver_chartDirectImage (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (g : X ⟶ T)
    (G : Modules.{u, u} B S hS Z.1 Z.2) [G.IsQuasicoherentOnSite]
    [(chartDirectImage B S hS i hi G).IsQuasicoherentOnSite]
    (h : IsFlatOver B S hS X.2 g.hom (chartDirectImage B S hS i hi G)) :
    IsFlatOver B S hS Z.2 (i ≫ g).hom G := by
  intro d z
  obtain ⟨p, hp⟩ := exists_fieldValuedPoint_schemePoint_eq B S hS d.U.obj.left z
  obtain ⟨zbar, hzbar⟩ := exists_geometricRepresentative B S hS Z.1
    (pointsMap B S hS (yoneda.obj d.U.obj.left) d.U.obj.hom
      (p.class B S hS (yoneda.obj d.U.obj.left)))
  obtain ⟨q, hq, rfl⟩ := exists_chartLift_of_chartPoint B S hS Z.2 zbar d.U z ⟨p, hp, hzbar.symm⟩
  refine (isFlatOverAtOnChartDiagram_iff_isFlatOverAtGeometricPoint B S hS (i ≫ g) G
    ⟨d.U, q, hq⟩ d.V d.g d.comm).2 ?_
  refine (isFlatOverAtGeometricPoint_chartDirectImage_iff B S hS i hi g G zbar).1 ?_
  refine (isFlatOverAt_exists_chartDiagram_iff_isFlatOverAtGeometricPoint B S hS g
    (chartDirectImage B S hS i hi G) (geometricPointMap i.hom zbar)).1 ?_
  obtain ⟨d, u, hcp⟩ := exists_chartDiagram_chartPoint B S hS g (geometricPointMap i.hom zbar)
  exact ⟨d, u, hcp, h _ _⟩

end AlgebraicGeometry.Space

end
