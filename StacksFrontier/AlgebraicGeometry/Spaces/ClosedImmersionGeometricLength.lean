module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricLength
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleStalkPointDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleNeighborhoodBaseChange

/-!
# The length of a module at a geometric point is unchanged by a closed immersion

Let `f : X ⟶ Y` be a closed immersion of algebraic spaces over a scheme `S`, let `G` be an
`𝒪_X`-module and let `x̄` be a geometric point of `X`. Stacks 0EE3 asserts that `G` has
length `d` at `x̄` exactly when `f_*G` has length `d` at `f(x̄)`. This file proves that, in the
form of an equality of the two lengths of
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricLength.lean`, together with the stalk
comparison it rests on:

`(f_*G)_{f(x̄)} ≃+ G_{x̄}`, semilinear over the germ map `𝒪_{Y, f(x̄)} → 𝒪_{X, x̄}`.

The direct image is `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, the direct
image of modules along base change of étale scheme charts; see the implementation notes for
why, and for where it is identified with
`AlgebraicGeometry.Space.modulePushforward`.

## Main definitions

* `AlgebraicGeometry.Space.chartDirectImage` is the direct image `f_*G` used here.
* `AlgebraicGeometry.Space.geometricStalkPushforwardMap` and
  `AlgebraicGeometry.Space.geometricStalkPushforwardAddEquiv` are the comparison
  `(f_*G)_{f(x̄)} ⟶ G_{x̄}` and the fact that it is an isomorphism of additive groups.

## Main results

* `AlgebraicGeometry.Space.geometricStalkPushforwardMap_germ`: the comparison of stalks sends
  the germ at `f(x̄)` of a section of `f_*G` over `V` to the germ at `x̄` of the same section,
  read over the base-changed chart `X ×_Y V`.
* `AlgebraicGeometry.Space.surjective_geometricStalkPushforwardMap` and
  `AlgebraicGeometry.Space.injective_geometricStalkPushforwardMap`: it is bijective.
* `AlgebraicGeometry.Space.geometricStalkPushforwardMap_smul`: it is semilinear over
  `AlgebraicGeometry.Space.etaleLocalRingMap`, the germ map of Stacks 04NG.
* `AlgebraicGeometry.Space.geometricLength_chartDirectImage` and
  `AlgebraicGeometry.Space.geometricLength_chartDirectImage_iff`: Stacks 0EE3 for algebraic
  spaces at a geometric point, as an equality of lengths and in the iff form of the source.
  The form at a point of the space, for a quasi-coherent module, is deduced from them in
  `StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionLengthAtPoint.lean`.

## Implementation notes

**The shape of the comparison.** Sections of `f_*G` over an étale chart `V` of `Y` are
sections of `G` over the base-changed chart `X ×_Y V`, on the nose, because the direct image
used here is `CategoryTheory.SheafOfModules.pushforward` along
`AlgebraicGeometry.Space.smallBaseChange`. So the stalk of `f_*G` at `f(x̄)` is a colimit of
sections of `G` over base-changed pointed charts, and the stalk of `G` at `x̄` is a colimit of
the same sections over all pointed charts. The comparison is therefore a cofinality statement,
and the cofinality input is
`AlgebraicGeometry.Space.SmallEtaleNeighborhood.initial_baseChange` — strictly, the two
statements it is proved from, which is what the two halves of bijectivity consume:
`…exists_baseChange_hom` for surjectivity and `…exists_baseChange_factorization` for
injectivity.

**Why `moduleStalkLargeDescOfCompatibleFamily`.** The geometric stalk is not presented in this
library as a colimit over the small étale neighbourhoods; it is `Stacks.moduleStalkLarge`, a
colimit over a small final model of the elements of the fibre functor, with its scalars
restricted and then extended. `Stacks.moduleStalkLargeDescOfCompatibleFamily` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleStalkPointDescent.lean` recovers the universal
property in the form needed, descending a compatible family of maps on sections to the fibre
of the lifted presheaf of sections and transporting it to the colimit over the final model.
The two stalks are compared *before* the extension of scalars, where both live in the universe
`max u m`; the extension of scalars raises the étale local ring to `CommRingCat.{u + 1}` and
hence the stalk to `max (u + 1) m`, so a map out of the colimit cannot be built there.
`AlgebraicGeometry.Space.geometricModuleStalkAddEquiv` crosses the extension of scalars once,
at the end.

**The direct image.** `AlgebraicGeometry.Space.modulePushforward`, the realization of
Stacks 03LU, is *not* the functor used. Its sections over `V` are sections of
`AlgebraicGeometry.Space.smallEtaleDirectImage`, which is the spaces-étale direct image
conjugated by the comparison equivalence of Stacks 03G1 — a chosen quasi-inverse — with the
module operations transported across that conjugation by
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctor`. The present file therefore states
Stacks 0EE3 for the base-change direct image, which for a representable morphism is the
concrete `f_*`: on an étale chart `V` of `Y` its sections are the sections of `G` over
`X ×_Y V` and its structure map is pullback of regular functions along the cartesian
projection. The two functors *are* identified in
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardChartComparison.lean`, by
`AlgebraicGeometry.Space.modulePushforwardChartIso` and, for a closed immersion, by
`AlgebraicGeometry.Space.modulePushforwardIsoChartDirectImage`; that file imports this one, so
the identification cannot be used here, but through it the statements below transfer to the
direct image of Stacks 03LU, in the module universe `u` in which that identification is
stated.

**Quasi-coherence and the point.** The source assumes `G` quasi-coherent; nothing here does,
so the statement proved is more general in that respect. It is *less* general in the point:
the source speaks of a point of the space the module lives on — its `|Y|`, which is `|X|`
here — and "length at a point" presupposes the independence of the choice of geometric point
above it. That independence is Stacks 0EE1, and it *is* proved in this development, for a
quasi-coherent module, as `AlgebraicGeometry.Space.geometricLength_eq_of_image_eq` of
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricLengthPointIndependence.lean`. The form of
Stacks 0EE3 at a point of the space is
`AlgebraicGeometry.Space.lengthAtPoint_chartDirectImage_iff` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionLengthAtPoint.lean`, deduced from the
statements below; the length at a point of the space is the value
`AlgebraicGeometry.Space.lengthAtPoint` of that file, which rests on that independence. It
lives downstream of this file because it needs one input more than
Stacks 0EE1: the quasi-coherence of the direct image, which is the first assertion of
Stacks 07U8 and is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineDirectImageCartesian.lean`, a file that imports
this one. The tags below are therefore for the statement at a geometric point, and the point
form carries its own.

## References

* [Stacks Project, Tag 0EE3](https://stacks.math.columbia.edu/tag/0EE3)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE2](https://stacks.math.columbia.edu/tag/0EE2)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m v w t

attribute [local instance] FinallySmall.preservesColimitsOfShape_of_isFiltered

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-! ### The comparison of geometric stalks -/

/-- The direct image `f_*G` of an `𝒪_X`-module along a closed immersion `f : X ⟶ Y` of
algebraic spaces, taken along base change of étale scheme charts: on an étale chart `V` of `Y`
its sections are the sections of `G` over `X ×_Y V`, and its structure map is pullback of
regular functions along the cartesian projection `X ×_Y V ⟶ V`.

This is `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, available because a closed
immersion is representable; see the implementation notes of this file for its relation to
`AlgebraicGeometry.Space.modulePushforward`. -/
noncomputable abbrev chartDirectImage (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f.hom)
    (G : Modules.{u, m} B S hS X.1 X.2) : Modules.{u, m} B S hS Y.1 Y.2 :=
  (smallBaseChangeModulePushforward B S hS f hf.rep).obj G

/-- The comparison of stalks before the extension of scalars: the additive map from the stalk
of `f_*G` at `f(x̄)` to the stalk of `G` at `x̄` sending the germ of a section over an étale
chart `V` of `Y` to the germ of the same section over the base-changed chart `X ×_Y V`.

The family of germ maps is compatible with restriction because base change of charts is
functorial and the lifts of `x̄` into the base-changed charts are compatible with it
(`AlgebraicGeometry.Space.smallBaseChangeFiberInv_map`). -/
noncomputable def moduleStalkLargePushforwardMap (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (x : GeometricPoint B S hS X.1)
    (G : Modules.{u, m} B S hS X.1 X.2) :
    Stacks.moduleStalkLarge.{m} (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
        (smallEtaleRingedTopos B S hS Y).O (chartDirectImage B S hS f hf G) →+
      Stacks.moduleStalkLarge.{m} (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O G :=
  Stacks.moduleStalkLargeDescOfCompatibleFamily
    (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
    (smallEtaleRingedTopos B S hS Y).O (chartDirectImage B S hS f hf G)
    (fun V q => Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O G ((smallBaseChange B S hS f hf.rep).obj V)
      (smallBaseChangeFiberInv B S hS f hf.rep x V q))
    (by
      intro V W k q s
      refine Eq.trans (Stacks.moduleStalkLargeGerm_w (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O G ((smallBaseChange B S hS f hf.rep).map k)
        (smallBaseChangeFiberInv B S hS f hf.rep x V q) s) ?_
      exact congrArg (fun z => Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O G ((smallBaseChange B S hS f hf.rep).obj W) z s)
        (smallBaseChangeFiberInv_map B S hS f hf.rep x k q))

/-- The comparison before the extension of scalars is the identity on germs. -/
theorem moduleStalkLargePushforwardMap_germ (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (x : GeometricPoint B S hS X.1)
    (G : Modules.{u, m} B S hS X.1 X.2) (V : SmallEtale B S hS Y.1)
    (q : GeometricFiber B S hS Y.1 (geometricPointMap f.hom x) V)
    (s : (chartDirectImage B S hS f hf G).val.obj (op V)) :
    moduleStalkLargePushforwardMap B S hS f hf x G
        (Stacks.moduleStalkLargeGerm
          (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
          (smallEtaleRingedTopos B S hS Y).O (chartDirectImage B S hS f hf G) V q s) =
      Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O G ((smallBaseChange B S hS f hf.rep).obj V)
        (smallBaseChangeFiberInv B S hS f hf.rep x V q) s :=
  Stacks.moduleStalkLargeDescOfCompatibleFamily_germ
    (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
    (smallEtaleRingedTopos B S hS Y).O (chartDirectImage B S hS f hf G) _ _ V q s

/-- **The comparison of geometric stalks along a closed immersion.** For a closed immersion
`f : X ⟶ Y` of algebraic spaces, an `𝒪_X`-module `G` and a geometric point `x̄` of `X`, the
additive map `(f_*G)_{f(x̄)} ⟶ G_{x̄}` which is the identity on germs.

It is `AlgebraicGeometry.Space.moduleStalkLargePushforwardMap` conjugated by the two crossings
of the extension of scalars defining the geometric stalks. -/
noncomputable def geometricStalkPushforwardMap (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (x : GeometricPoint B S hS X.1)
    (G : Modules.{u, m} B S hS X.1 X.2) :
    geometricModuleStalk B S hS Y (geometricPointMap f.hom x)
        (chartDirectImage B S hS f hf G) →+
      geometricModuleStalk B S hS X x G :=
  (geometricModuleStalkAddEquiv B S hS X x G).toAddMonoidHom.comp
    ((moduleStalkLargePushforwardMap B S hS f hf x G).comp
      (geometricModuleStalkAddEquiv B S hS Y (geometricPointMap f.hom x)
        (chartDirectImage B S hS f hf G)).symm.toAddMonoidHom)

/-- The comparison of geometric stalks sends the germ at `f(x̄)` of a section of `f_*G` over a
small étale neighbourhood `V` of `f(x̄)` to the germ at `x̄` of the same section, read over the
base-changed neighbourhood `X ×_Y V`. -/
theorem geometricStalkPushforwardMap_germ (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (x : GeometricPoint B S hS X.1)
    (G : Modules.{u, m} B S hS X.1 X.2)
    (V : SmallEtaleNeighborhood (geometricPointMap f.hom x))
    (s : (chartDirectImage B S hS f hf G).val.obj (op V.chart)) :
    geometricStalkPushforwardMap B S hS f hf x G
        (geometricModuleStalkGerm B S hS Y (geometricPointMap f.hom x)
          (chartDirectImage B S hS f hf G) V s) =
      geometricModuleStalkGerm B S hS X x G
        ((SmallEtaleNeighborhood.baseChange B S hS f hf.rep x).obj V) s := by
  have h1 : (geometricModuleStalkAddEquiv B S hS Y (geometricPointMap f.hom x)
        (chartDirectImage B S hS f hf G)).symm
        (geometricModuleStalkGerm B S hS Y (geometricPointMap f.hom x)
          (chartDirectImage B S hS f hf G) V s) =
      Stacks.moduleStalkLargeGerm
        (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
        (smallEtaleRingedTopos B S hS Y).O (chartDirectImage B S hS f hf G) V.chart
        ⟨V.point, V.point_comp⟩ s :=
    (congrArg (geometricModuleStalkAddEquiv B S hS Y (geometricPointMap f.hom x)
        (chartDirectImage B S hS f hf G)).symm
      (geometricModuleStalkGerm_apply B S hS Y (geometricPointMap f.hom x)
        (chartDirectImage B S hS f hf G) V s)).trans
      ((geometricModuleStalkAddEquiv B S hS Y (geometricPointMap f.hom x)
        (chartDirectImage B S hS f hf G)).symm_apply_apply _)
  have h2 : Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O G
        ((smallBaseChange B S hS f hf.rep).obj V.chart)
        (smallBaseChangeFiberInv B S hS f hf.rep x V.chart ⟨V.point, V.point_comp⟩) s =
      Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O G
        ((SmallEtaleNeighborhood.baseChange B S hS f hf.rep x).obj V).chart
        ⟨((SmallEtaleNeighborhood.baseChange B S hS f hf.rep x).obj V).point,
          ((SmallEtaleNeighborhood.baseChange B S hS f hf.rep x).obj V).point_comp⟩ s :=
    congrArg (fun z => Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O G
      ((smallBaseChange B S hS f hf.rep).obj V.chart) z s)
      (Subtype.ext rfl)
  have h3 := moduleStalkLargePushforwardMap_germ B S hS f hf x G V.chart
    ⟨V.point, V.point_comp⟩ s
  exact ((congrArg (fun z => geometricModuleStalkAddEquiv B S hS X x G
        (moduleStalkLargePushforwardMap B S hS f hf x G z)) h1).trans
    (congrArg (geometricModuleStalkAddEquiv B S hS X x G) (h3.trans h2))).trans
      (geometricModuleStalkGerm_apply B S hS X x G
        ((SmallEtaleNeighborhood.baseChange B S hS f hf.rep x).obj V) s).symm

/-! ### Bijectivity -/

/-- The comparison of geometric stalks is surjective: every germ at `x̄` is the germ of a
section over a base-changed pointed chart, because base-changed pointed charts refine every
pointed chart (`AlgebraicGeometry.Space.SmallEtaleNeighborhood.exists_baseChange_hom`). -/
theorem surjective_geometricStalkPushforwardMap (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (x : GeometricPoint B S hS X.1)
    (G : Modules.{u, m} B S hS X.1 X.2) :
    Function.Surjective (geometricStalkPushforwardMap B S hS f hf x G) := by
  intro z
  obtain ⟨U, t, hU⟩ := geometricModuleStalkGerm_jointly_surjective B S hS X x G z
  obtain ⟨V, ⟨mm⟩⟩ := SmallEtaleNeighborhood.exists_baseChange_hom B S hS f hf x U
  refine ⟨geometricModuleStalkGerm B S hS Y (geometricPointMap f.hom x)
    (chartDirectImage B S hS f hf G) V (G.val.map mm.hom.op t), ?_⟩
  refine Eq.trans (geometricStalkPushforwardMap_germ B S hS f hf x G V
    (G.val.map mm.hom.op t)) ?_
  exact (geometricModuleStalkGerm_map B S hS X x G mm t).trans hU

/-- The comparison of geometric stalks is injective. A section of `f_*G` over `V` whose germ
at `x̄` vanishes is killed by restriction to some pointed chart of `X` over `X ×_Y V`; that
chart is refined by a base-changed one, and the resulting morphism between base changes is the
base change of a morphism of pointed charts of `Y`
(`AlgebraicGeometry.Space.SmallEtaleNeighborhood.exists_baseChange_factorization`), along which
the section is therefore killed over a pointed chart of `Y`. -/
theorem injective_geometricStalkPushforwardMap (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (x : GeometricPoint B S hS X.1)
    (G : Modules.{u, m} B S hS X.1 X.2) :
    Function.Injective (geometricStalkPushforwardMap B S hS f hf x G) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro w hw
  obtain ⟨V, s, rfl⟩ := geometricModuleStalkGerm_jointly_surjective B S hS Y
    (geometricPointMap f.hom x) (chartDirectImage B S hS f hf G) w
  rw [geometricStalkPushforwardMap_germ] at hw
  obtain ⟨Wn, n, hn⟩ := (geometricModuleStalkGerm_eq_zero_iff B S hS X x G
    ((SmallEtaleNeighborhood.baseChange B S hS f hf.rep x).obj V) s).mp hw
  obtain ⟨V₀, ⟨k⟩⟩ := SmallEtaleNeighborhood.exists_baseChange_hom B S hS f hf x Wn
  obtain ⟨W₁, a, b, hab⟩ :=
    SmallEtaleNeighborhood.exists_baseChange_factorization B S hS f hf x V₀ V (k ≫ n)
  refine (geometricModuleStalkGerm_eq_zero_iff B S hS Y (geometricPointMap f.hom x)
    (chartDirectImage B S hS f hf G) V s).mpr ⟨W₁, b, ?_⟩
  have hb : (smallBaseChange B S hS f hf.rep).map b.hom =
      (smallBaseChange B S hS f hf.rep).map a.hom ≫ k.hom ≫ n.hom :=
    (congrArg SmallEtaleNeighborhood.Hom.hom hab).symm
  change G.val.presheaf.map ((smallBaseChange B S hS f hf.rep).map b.hom).op s = 0
  rw [hb]
  refine Eq.trans (ConcreteCategory.congr_hom (G.val.presheaf.map_comp
    (n.hom.op ≫ k.hom.op) ((smallBaseChange B S hS f hf.rep).map a.hom).op) s) ?_
  refine Eq.trans (congrArg
    (fun z => G.val.presheaf.map ((smallBaseChange B S hS f hf.rep).map a.hom).op z)
    (Eq.trans (ConcreteCategory.congr_hom (G.val.presheaf.map_comp n.hom.op k.hom.op) s)
      (Eq.trans (congrArg (fun z => G.val.presheaf.map k.hom.op z) hn)
        (map_zero (ConcreteCategory.hom (G.val.presheaf.map k.hom.op)))))) ?_
  exact map_zero (ConcreteCategory.hom
    (G.val.presheaf.map ((smallBaseChange B S hS f hf.rep).map a.hom).op))

/-! ### Semilinearity -/

/-- The germ at `x̄` of the pullback to `X ×_Y V` of a regular function on an étale chart `V`
of `Y` is the image under the germ map of étale local rings of Stacks 04NG of its germ at
`f(x̄)`.

This is `AlgebraicGeometry.Space.etaleLocalRingMap_isEtaleLocalRingMap` applied to the
base-change square, whose commutativity is the defining square of the representability of `f`
and whose compatibility of lifts is
`AlgebraicGeometry.Space.smallBaseChangeFiberMap_smallBaseChangeFiberInv`. -/
theorem etaleLocalRingGerm_baseChange (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f.hom)
    (x : GeometricPoint B S hS X.1)
    (V : SmallEtaleNeighborhood (geometricPointMap f.hom x))
    (rr : (structurePresheaf B S hS Y.1).obj (op V.chart)) :
    etaleLocalRingGerm B S hS X.1 x
        (op ((SmallEtaleNeighborhood.baseChange B S hS f hf.rep x).obj V))
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          (hf.rep.snd V.chart.1.hom)).op).hom rr) =
      etaleLocalRingMap X.2 f.hom x
        (etaleLocalRingGerm B S hS Y.1 (geometricPointMap f.hom x) (op V) rr) := by
  have hsnd : ((SmallEtaleNeighborhood.baseChange B S hS f hf.rep x).obj V).point ≫
      hf.rep.snd V.chart.1.hom = V.point :=
    congrArg Subtype.val (smallBaseChangeFiberMap_smallBaseChangeFiberInv B S hS f hf.rep x
      V.chart ⟨V.point, V.point_comp⟩)
  have hsq := etaleLocalRingMap_isEtaleLocalRingMap X.2 f.hom x
    ((SmallEtaleNeighborhood.baseChange B S hS f hf.rep x).obj V) V
    (hf.rep.snd V.chart.1.hom) (hf.rep.w V.chart.1.hom) hsnd
  exact congrArg (fun φ => φ rr) hsq

/-- Semilinearity of the comparison of geometric stalks on germs: the scalar action of a
regular function on `V` on a section of `f_*G` over `V` is, read over `X ×_Y V`, the action of
its pullback, whose germ is the image of the germ of the function. -/
theorem geometricStalkPushforwardMap_germ_smul (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (x : GeometricPoint B S hS X.1)
    (G : Modules.{u, m} B S hS X.1 X.2)
    (V : SmallEtaleNeighborhood (geometricPointMap f.hom x))
    (rr : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.obj (op V.chart))
    (s : (chartDirectImage B S hS f hf G).val.obj (op V.chart)) :
    geometricStalkPushforwardMap B S hS f hf x G
        (geometricModuleStalkGerm B S hS Y (geometricPointMap f.hom x)
          (chartDirectImage B S hS f hf G) V (rr • s)) =
      etaleLocalRingMap X.2 f.hom x
          (etaleLocalRingGerm B S hS Y.1 (geometricPointMap f.hom x) (op V) rr) •
        geometricStalkPushforwardMap B S hS f hf x G
          (geometricModuleStalkGerm B S hS Y (geometricPointMap f.hom x)
            (chartDirectImage B S hS f hf G) V s) := by
  rw [geometricStalkPushforwardMap_germ, geometricStalkPushforwardMap_germ]
  refine Eq.trans ?_ (congrArg (fun c => c • geometricModuleStalkGerm B S hS X x G
      ((SmallEtaleNeighborhood.baseChange B S hS f hf.rep x).obj V) s)
    (etaleLocalRingGerm_baseChange B S hS f hf x V rr))
  exact geometricModuleStalkGerm_smul B S hS X x G
    ((SmallEtaleNeighborhood.baseChange B S hS f hf.rep x).obj V)
    ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (hf.rep.snd V.chart.1.hom)).op).hom rr) s

/-- **The comparison of geometric stalks is semilinear.** For every `r` in the étale local ring
`𝒪_{Y, f(x̄)}` and every `z` in the stalk of `f_*G` at `f(x̄)`, the comparison carries `r • z`
to `etaleLocalRingMap r • ` its value on `z`.

Both `r` and `z` are germs, over possibly different pointed charts of `Y`; cofilteredness of
the small étale neighbourhoods of `f(x̄)` puts them over a common one, where the statement is
`AlgebraicGeometry.Space.geometricStalkPushforwardMap_germ_smul`. -/
theorem geometricStalkPushforwardMap_smul (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (x : GeometricPoint B S hS X.1)
    (G : Modules.{u, m} B S hS X.1 X.2)
    (r : etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x))
    (z : geometricModuleStalk B S hS Y (geometricPointMap f.hom x)
      (chartDirectImage B S hS f hf G)) :
    geometricStalkPushforwardMap B S hS f hf x G (r • z) =
      etaleLocalRingMap X.2 f.hom x r •
        geometricStalkPushforwardMap B S hS f hf x G z := by
  have : IsCofiltered (SmallEtaleNeighborhood (geometricPointMap f.hom x)) :=
    isCofiltered_smallEtaleNeighborhood B S hS Y.1 Y.2 (geometricPointMap f.hom x)
  obtain ⟨N₁, a, hNa⟩ := (spaceGerms_isColimit Y.2).ι_jointly_surjective r
  obtain ⟨V₂, s, hs⟩ := geometricModuleStalkGerm_jointly_surjective B S hS Y
    (geometricPointMap f.hom x) (chartDirectImage B S hS f hf G) z
  obtain ⟨W, k₁, k₂, -⟩ := IsCofilteredOrEmpty.cone_objs N₁.unop V₂
  have hr : etaleLocalRingGerm B S hS Y.1 (geometricPointMap f.hom x) (op W)
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS Y.1).map k₁.hom)).op).hom a) = r :=
    (congrArg (fun φ => φ a) (etaleLocalRingGerm_comp_map B S hS k₁)).trans hNa
  have hz : geometricModuleStalkGerm B S hS Y (geometricPointMap f.hom x)
      (chartDirectImage B S hS f hf G) W
      ((chartDirectImage B S hS f hf G).val.map k₂.hom.op s) = z :=
    (geometricModuleStalkGerm_map B S hS Y (geometricPointMap f.hom x)
      (chartDirectImage B S hS f hf G) k₂ s).trans hs
  obtain ⟨rr, hrr⟩ : ∃ rr : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.obj (op W.chart),
      etaleLocalRingGerm B S hS Y.1 (geometricPointMap f.hom x) (op W) rr = r := ⟨_, hr⟩
  obtain ⟨s', hs'⟩ : ∃ s' : (chartDirectImage B S hS f hf G).val.obj (op W.chart),
      geometricModuleStalkGerm B S hS Y (geometricPointMap f.hom x)
        (chartDirectImage B S hS f hf G) W s' = z := ⟨_, hz⟩
  rw [← hrr, ← hs']
  refine Eq.trans (congrArg (geometricStalkPushforwardMap B S hS f hf x G)
    (geometricModuleStalkGerm_smul B S hS Y (geometricPointMap f.hom x)
      (chartDirectImage B S hS f hf G) W rr s').symm) ?_
  exact geometricStalkPushforwardMap_germ_smul B S hS f hf x G W rr s'

/-- **The stalk of the direct image at the image point.** For a closed immersion `f : X ⟶ Y` of
algebraic spaces, an `𝒪_X`-module `G` and a geometric point `x̄` of `X`, the stalk of `f_*G` at
`f(x̄)` is isomorphic, as an additive group, to the stalk of `G` at `x̄`.

Together with `AlgebraicGeometry.Space.geometricStalkPushforwardMap_smul`, which makes it
semilinear over the germ map of étale local rings, this is the identification
`(f_*G)_{f(x̄)} = G_{x̄}` over `𝒪_{Y, f(x̄)}` that the proof of Stacks 0EE3 uses. -/
noncomputable def geometricStalkPushforwardAddEquiv (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (x : GeometricPoint B S hS X.1)
    (G : Modules.{u, m} B S hS X.1 X.2) :
    geometricModuleStalk B S hS Y (geometricPointMap f.hom x)
        (chartDirectImage B S hS f hf G) ≃+
      geometricModuleStalk B S hS X x G :=
  AddEquiv.ofBijective (geometricStalkPushforwardMap B S hS f hf x G)
    ⟨injective_geometricStalkPushforwardMap B S hS f hf x G,
      surjective_geometricStalkPushforwardMap B S hS f hf x G⟩

/-! ### Stacks 0EE3 -/

/-- **Stacks 0EE3 for algebraic spaces, at a geometric point.** Let `f : X ⟶ Y` be a closed
immersion of algebraic spaces over a scheme `S`, let `G` be an `𝒪_X`-module and let `x̄` be a
geometric point of `X`. Then `f_*G` has the same length at `f(x̄)` as `G` has at `x̄`.

The germ map `𝒪_{Y, f(x̄)} → 𝒪_{X, x̄}` of a closed immersion is surjective
(`AlgebraicGeometry.Space.surjective_etaleLocalRingMap_of_isClosedImmersion`) and the stalk of
`f_*G` at `f(x̄)` is the stalk of `G` at `x̄` semilinearly over it
(`AlgebraicGeometry.Space.geometricStalkPushforwardAddEquiv`), so
`AlgebraicGeometry.Space.geometricLength_eq_of_surjective_of_addEquiv` applies: restriction of
scalars along a surjection does not change the lattice of submodules, hence not its length.

No quasi-coherence of `G` is assumed. The direct image is the one along base change of étale
scheme charts; see the implementation notes of this file. -/
@[stacks 0EE3 "at a geometric point of the source, and for the direct image of modules along
  base change of étale scheme charts; the form at a point of the space is
  `AlgebraicGeometry.Space.lengthAtPoint_chartDirectImage_iff` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionLengthAtPoint.lean`"]
theorem geometricLength_chartDirectImage (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f.hom)
    (x : GeometricPoint B S hS X.1) (G : Modules.{u, m} B S hS X.1 X.2) :
    geometricLength B S hS Y (geometricPointMap f.hom x)
        ((smallBaseChangeModulePushforward B S hS f hf.rep).obj G) =
      geometricLength B S hS X x G :=
  geometricLength_eq_of_surjective_of_addEquiv (geometricPointMap f.hom x) x
    (chartDirectImage B S hS f hf G) G (etaleLocalRingMap X.2 f.hom x)
    (surjective_etaleLocalRingMap_of_isClosedImmersion B S hS f hf x)
    (geometricStalkPushforwardAddEquiv B S hS f hf x G)
    (geometricStalkPushforwardMap_smul B S hS f hf x G)

/-- **Stacks 0EE3 for algebraic spaces, at a geometric point**, in the iff form of the source:
for every `d` in `ℕ∞ = {0, 1, 2, …, ∞}`, the module `G` has length `d` at the geometric
point `x̄` of `X` exactly when `f_*G` has length `d` at `f(x̄)`.

This is `AlgebraicGeometry.Space.geometricLength_chartDirectImage` read as an equivalence. -/
@[stacks 0EE3 "at a geometric point of the source, and for the direct image of modules along
  base change of étale scheme charts; the form at a point of the space is
  `AlgebraicGeometry.Space.lengthAtPoint_chartDirectImage_iff` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionLengthAtPoint.lean`"]
theorem geometricLength_chartDirectImage_iff (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (x : GeometricPoint B S hS X.1)
    (G : Modules.{u, m} B S hS X.1 X.2) (d : ℕ∞) :
    geometricLength B S hS X x G = d ↔
      geometricLength B S hS Y (geometricPointMap f.hom x)
        ((smallBaseChangeModulePushforward B S hS f hf.rep).obj G) = d := by
  rw [geometricLength_chartDirectImage B S hS f hf x G]

end AlgebraicGeometry.Space

end
