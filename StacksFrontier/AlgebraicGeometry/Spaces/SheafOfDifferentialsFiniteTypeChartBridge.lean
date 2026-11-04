module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleStructureSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsChartAlgebraBridge
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 05ZE: the sheaf of differentials of a morphism locally of finite type

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B`.
Stacks 05ZE asserts that `Ω_{X/Y}` is a finite type `𝒪_X`-module when `f` is locally of finite
type.  The finiteness is read off the construction of `Ω_{X/Y}` in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsFiniteType.lean`, which proves it from
the étale-local finite generation of `𝒪_X` as an `f⁻¹𝒪_Y`-algebra
(`AlgebraicGeometry.Space.HasFiniteTypeAffineChartAlgebras`); this file supplies that condition
from `AlgebraicGeometry.Space.IsLocallyOfFiniteType`, and therefore states the tag.

## The bridge

`AlgebraicGeometry.Space.IsLocallyOfFiniteType` is Stacks 03XF(1): the scheme morphism of every
commuting square of étale scheme charts over `f` is locally of finite type.  The condition
`Ω_{X/Y}` needs is about the two sheaves of rings `f⁻¹𝒪_Y ⟶ 𝒪_X` on the small étale site of `X`.
Three inputs join them, and all three are available.

* **The squares of affine charts cover.**
  `AlgebraicGeometry.Space.exists_affine_chartDiagram_ofArrows` (Stacks 03G2) gives, over every
  object `U` of the small étale site of `X`, a covering family of affine étale charts each of which
  is the chart of `X` of a commuting square whose chart of `Y` is affine as well. Affineness of
  both charts is what turns the chart condition of Stacks 03XF(1) into a finite type *ring* map
  `𝒪_Y(W) ⟶ 𝒪_X(V)`, which is `AlgebraicGeometry.Space.exists_adjoin_inverseImage_of_square`.
* **The coefficient comparison.**  That ring map has coefficients in `𝒪_Y(W)`, while `Ω_{X/Y}`
  wants them in `(f⁻¹𝒪_Y)(V)`.  The comparison `𝒪_Y(W) ⟶ (f⁻¹𝒪_Y)(V)` is the unit of the
  inverse-image adjunction of the morphism of small étale topoi, read on the square through the
  chart correspondence of Stacks 03G8
  (`AlgebraicGeometry.Space.chartDiagramInverseImageSection`), and its composite with `f♯` is
  exactly the pullback of regular functions along the square
  (`AlgebraicGeometry.Space.structureSharpInverseImage_chartDiagramInverseImageSection`).
* **Enlarging the coefficients.**  Finite generation over `𝒪_Y(W)` becomes finite generation over
  `(f⁻¹𝒪_Y)(V)` by `Stacks.Algebra.mem_adjoin_of_forall_exists`, already inside
  `AlgebraicGeometry.Space.exists_adjoin_inverseImage_of_square`.

## Main definitions

* `AlgebraicGeometry.Space.chartDiagramInverseImageSection`: the section of `f⁻¹𝒪_Y` over the
  chart of `X` of a commuting square of étale scheme charts attached to a regular function on the
  chart of `Y`.

## Main results

* `AlgebraicGeometry.Space.unit_comp_pushforward_map_structureSharpInverseImage`: on underlying
  sheaves of sets, the unit of the inverse-image adjunction followed by the direct image of
  `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` is `f♯ : 𝒪_Y ⟶ f_*𝒪_X`.
* `AlgebraicGeometry.Space.structureSharpInverseImage_chartDiagramInverseImageSection`: **the
  coefficient comparison** — `f♯` carries that section to the pullback of the regular function
  along the scheme morphism of the square.
* `AlgebraicGeometry.Space.exists_mem_adjoin_inverseImage_of_chartDiagram`: at a square of affine
  étale charts over a morphism locally of finite type, `𝒪_X` of the upper chart is generated as
  an `f⁻¹𝒪_Y`-algebra by finitely many sections.
* `AlgebraicGeometry.Space.hasFiniteTypeAffineChartAlgebras_of_isLocallyOfFiniteType`: **the
  bridge** — a morphism locally of finite type satisfies
  `AlgebraicGeometry.Space.HasFiniteTypeAffineChartAlgebras`.
* `isFiniteTypeOnSite_sheafOfDifferentials_of_isLocallyOfFiniteType_unconditional`:
  **Stacks 05ZE**.

## Implementation notes

The coefficient comparison is proved on *sheaves of sets*, not on sheaves of rings.  The
adjunction identity it needs is
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv`, which is stated after
`AlgebraicGeometry.RingedTopos.forgetRing`, and the chart correspondence
`AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse` is a bijection of sheaves of sets
too.  Nothing is lost: the comparison asserts an equality of *elements* of `𝒪_X(V)`, and the
witness it produces is used only through the ring map `f♯`, whose underlying function is the one
the set-level statement describes.

All of it is term mode.  Rewriting is not available here: ascribing the unit of the adjunction to
the type `𝒪_Y ⟶ f_*(f⁻¹𝒪_Y)` with `f⁻¹𝒪_Y` spelled as the forgetful image of the inverse image
of *rings* leaves a term that is not type-correct at `implicit` transparency — the two spellings
of the inverse image agree definitionally but not syntactically — so `rewrite` fails on it with
an application type mismatch.  Transporting the adjunction identity with `congrArg` instead
keeps every term at the spelling it was built at.

`AlgebraicGeometry.Space.exists_mem_adjoin_inverseImage_of_eq_chartDiagram` exists only to move
the conclusion from `d.U` to a chart presented as being equal to it:
`AlgebraicGeometry.Space.exists_affine_chartDiagram_ofArrows` returns the covering family and the
squares separately, with an equation between the members and the squares' upper charts, and that
equation cannot be rewritten in the goal — the chart occurs in dependent positions — while
`subst` discharges it once the target chart is a variable.

The index type of the covering family is `ULift`ed: Stacks 03G2 produces a family indexed by a
`Type u` (the affine opens of two schemes), whereas
`AlgebraicGeometry.Space.HasFiniteTypeAffineChartAlgebras` asks for `Type (u + 1)`, the universe in
which `SheafOfModules.IsFiniteTypeOnSite` indexes its covering families on this site. The reindexed
family generates a larger sieve, which is all
`CategoryTheory.GrothendieckTopology.superset_covering` needs.

## References

* [Stacks Project, Tag 05ZE](https://stacks.math.columbia.edu/tag/05ZE)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF), part (1), locally of
  finite type for morphisms of algebraic spaces.
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), the comparison of the
  small étale site with the charts, whose cofinality of affine squares is used here.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the chart correspondence
  and the structure map of the morphism of small étale ringed topoi.
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The coefficient comparison of a commuting square of étale scheme charts.**  The section of
`f⁻¹𝒪_Y` over the chart of `X` of a commuting square of étale scheme charts over `f` attached to
a regular function on the chart of `Y`.

It is the unit of the inverse-image adjunction `f⁻¹ ⊣ f_*` of the morphism of small étale topoi,
read as a map of sections over the square by the chart correspondence of Stacks 03G8.  Its image
under `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` is the pullback of the regular function along the scheme morphism of
the square, which is
`AlgebraicGeometry.Space.structureSharpInverseImage_chartDiagramInverseImageSection`. -/
noncomputable def chartDiagramInverseImageSection (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (r : chartRing B S hS Y.1 Y.2 d.V) :
    inverseImageStructureRing B S hS f d.U :=
  ((fMapEquivPushforwardHom_ringUniverse B S hS f
      ((smallEtaleRingedTopos B S hS X).forgetRing.obj (inverseImageStructureSheaf B S hS f))
      ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
        (smallEtaleRingedTopos B S hS Y).O)).symm
    ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.unit.app
      ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
        (smallEtaleRingedTopos B S hS Y).O))).app d r

/-- **The two forms of the structure map are adjunct, spelled through the unit.**  On underlying
sheaves of sets, the unit of the inverse-image adjunction of the morphism of small étale topoi of
`f`, followed by the direct image of the inverse-image form `f⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map,
is the direct-image form `𝒪_Y ⟶ f_*𝒪_X`.

This is `AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv` with the hom-set
bijection of the adjunction expanded by `CategoryTheory.Adjunction.homEquiv_unit`. -/
theorem unit_comp_pushforward_map_structureSharpInverseImage (f : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS f).toToposHom.adj.unit.app
          ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
            (smallEtaleRingedTopos B S hS Y).O) ≫
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map
          ((smallEtaleRingedTopos B S hS X).forgetRing.map
            (structureSharpInverseImage B S hS f)) =
      (smallEtaleRingedTopos B S hS Y).forgetRing.map
        (smallEtaleRingedToposHom B S hS f).fSharp :=
  ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv_unit _ _ _).symm.trans
    ((congrArg ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv _ _)
        (AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv
          (smallEtaleRingedToposHom B S hS f))).trans
      (((smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv _ _).apply_symm_apply _))

/-- **The coefficient comparison of a commuting square of étale scheme charts computes.**  The
structure map `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` carries
`AlgebraicGeometry.Space.chartDiagramInverseImageSection` of a regular function on the chart of
`Y` to the pullback of that function along the scheme morphism of the square.

So the image of `𝒪_Y(V)` in `𝒪_X(U)` is contained in the image of `(f⁻¹𝒪_Y)(U)`, which is what
turns generation over the first ring into generation over the second.

Both sides are read off the chart correspondence of Stacks 03G8: the naturality of that
correspondence in the sheaf on the source
(`AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse_symm_app_map`) applied to `f♯` and
the unit of the adjunction, whose composite is the direct-image form of the structure map by
`AlgebraicGeometry.Space.unit_comp_pushforward_map_structureSharpInverseImage`; and the
direct-image form is pullback of regular functions along the square, which is Stacks 03G8 in the
form `AlgebraicGeometry.Space.structureFMap_app`. -/
theorem structureSharpInverseImage_chartDiagramInverseImageSection (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (r : chartRing B S hS Y.1 Y.2 d.V) :
    ((structureSharpInverseImage B S hS f).hom.app (op d.U)).hom
        (chartDiagramInverseImageSection B S hS f d r) =
      Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) r := by
  have key := fMapEquivPushforwardHom_ringUniverse_symm_app_map B S hS f
    ((smallEtaleRingedTopos B S hS X).forgetRing.obj (inverseImageStructureSheaf B S hS f))
    ((smallEtaleRingedTopos B S hS X).forgetRing.obj (smallEtaleRingedTopos B S hS X).O)
    ((smallEtaleRingedTopos B S hS Y).forgetRing.obj (smallEtaleRingedTopos B S hS Y).O)
    ((smallEtaleRingedTopos B S hS X).forgetRing.map (structureSharpInverseImage B S hS f))
    ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.unit.app _) d r
  refine Eq.trans (Eq.symm ?_) (structureFMap_app B S hS f d r)
  refine Eq.trans ?_ key
  exact congrArg (fun m ↦ ((fMapEquivPushforwardHom_ringUniverse B S hS f
    ((smallEtaleRingedTopos B S hS X).forgetRing.obj (smallEtaleRingedTopos B S hS X).O)
    ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
      (smallEtaleRingedTopos B S hS Y).O)).symm m).app d r)
    (unit_comp_pushforward_map_structureSharpInverseImage B S hS f).symm

/-- **Finite generation at one square of affine étale charts.**  Let `f` be locally of finite
type and let `d` be a commuting square of étale scheme charts over `f` whose chart of `X` and
chart of `Y` both have affine underlying scheme.  Then `𝒪_X` of the chart of `X` is generated as
an `(f⁻¹𝒪_Y)`-algebra by finitely many sections.

This is `AlgebraicGeometry.Space.exists_adjoin_inverseImage_of_square` with its coefficient
comparison discharged by
`AlgebraicGeometry.Space.structureSharpInverseImage_chartDiagramInverseImageSection`. -/
theorem exists_mem_adjoin_inverseImage_of_chartDiagram (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    ∃ (n : ℕ) (y : Fin n → chartRing B S hS X.1 X.2 d.U),
      letI := sharpAlgebra B S hS f d.U
      ∀ z : chartRing B S hS X.1 X.2 d.U,
        z ∈ Algebra.adjoin (inverseImageStructureRing B S hS f d.U) (Set.range y) :=
  exists_adjoin_inverseImage_of_square B S hS f hf d.U d.V d.g d.comm.symm hU hV
    (fun r ↦ ⟨chartDiagramInverseImageSection B S hS f d r,
      structureSharpInverseImage_chartDiagramInverseImageSection B S hS f d r⟩)

/-- `AlgebraicGeometry.Space.exists_mem_adjoin_inverseImage_of_chartDiagram` at a chart given
together with an equation presenting it as the chart of `X` of the square.  That is the shape in
which `AlgebraicGeometry.Space.exists_affine_chartDiagram_ofArrows` delivers its covering family,
and the equation is discharged here by `subst` rather than by rewriting in the goal, where the
chart occurs in dependent positions. -/
theorem exists_mem_adjoin_inverseImage_of_eq_chartDiagram (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (Z : SmallEtale B S hS X.1) (hZ : d.U = Z)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj Z))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    ∃ (n : ℕ) (y : Fin n → chartRing B S hS X.1 X.2 Z),
      letI := sharpAlgebra B S hS f Z
      ∀ z : chartRing B S hS X.1 X.2 Z,
        z ∈ Algebra.adjoin (inverseImageStructureRing B S hS f Z) (Set.range y) := by
  subst hZ
  exact exists_mem_adjoin_inverseImage_of_chartDiagram B S hS f hf d hU hV

/-- **A morphism locally of finite type has étale-locally finitely generated chart algebras.**
If `f : X ⟶ Y` is locally of finite type in the sense of Stacks 03XF(1), then every object of the
small étale site of `X` has a covering family of charts with affine underlying scheme over each
of which `𝒪_X` is generated as an `(f⁻¹𝒪_Y)`-algebra by finitely many sections.

The covering family is the one supplied by Stacks 03G2 in the form
`AlgebraicGeometry.Space.exists_affine_chartDiagram_ofArrows`: each of its members is the chart of
`X` of a commuting square whose chart of `Y` is affine as well, so
`AlgebraicGeometry.Space.exists_mem_adjoin_inverseImage_of_chartDiagram` applies to it. -/
theorem hasFiniteTypeAffineChartAlgebras_of_isLocallyOfFiniteType (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom) :
    HasFiniteTypeAffineChartAlgebras B S hS f := by
  intro U
  obtain ⟨I, W, a, d, hdU, haff, haffV, hcov⟩ :=
    exists_affine_chartDiagram_ofArrows B S hS f U
  refine ⟨ULift.{u + 1} I, fun i ↦ W i.down, fun i ↦ a i.down, ?_,
    fun i ↦ ⟨haff i.down, ?_⟩⟩
  · refine GrothendieckTopology.superset_covering _ ?_ hcov
    refine (Sieve.generate_le_iff _ _).2 (Presieve.ofArrows_le_iff.2 fun i ↦ ?_)
    exact Sieve.ofArrows_mk _ _ (ULift.up i)
  · exact exists_mem_adjoin_inverseImage_of_eq_chartDiagram B S hS f hf (d i.down)
      (W i.down) (hdU i.down) (haff i.down) (haffV i.down)

/-- **Stacks 05ZE.**  If `f : X ⟶ Y` is a morphism of algebraic spaces over `S` which is locally
of finite type, then `Ω_{X/Y}` is a finite type `𝒪_X`-module.

The chart-algebra condition of
`AlgebraicGeometry.Space.hasFiniteTypeAffineChartAlgebras_of_isLocallyOfFiniteType` feeds
`AlgebraicGeometry.Space.isFiniteTypeOnSite_sheafOfDifferentials_of_affineChartAlgebras`, which
generates `Ω_{X/Y}` over each member of the covering by the universal differentials of the
generators. Algebra, Lemma 00UU for the transition maps of the small étale site is proved there,
not assumed. -/
@[stacks 05ZE "Ω_{X/Y} is a finite type 𝒪_X-module for f locally of finite type, with no
  further hypothesis"]
theorem isFiniteTypeOnSite_sheafOfDifferentials_of_isLocallyOfFiniteType_unconditional
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom) :
    (sheafOfDifferentials B S hS f).IsFiniteTypeOnSite :=
  isFiniteTypeOnSite_sheafOfDifferentials_of_affineChartAlgebras B S hS f
    (hasFiniteTypeAffineChartAlgebras_of_isLocallyOfFiniteType B S hS f hf)

end AlgebraicGeometry.Space

end
