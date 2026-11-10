module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.IntegralSquareLimitSetup
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteBaseChangeSiteTransfer
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SetsToAbelianBaseChangeBridge
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# Étale base change along an integral morphism: the pieces of the affine case

Consider a cartesian square

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

of schemes with `f` integral and `Y`, `Y'` affine, and a sheaf of sets `F` on the small étale
site of `X`. [Stacks, Tag 0EYP] asserts that the base change comparison
`g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` is an isomorphism. The source's proof writes `f` as the limit of a
directed system of *finite* morphisms `st_i : X_i ⟶ Y`, which is
`Stacks.EtaleCohomology.IntegralSquareLimitData`, and then runs the chain

```
g⁻¹ f_* F = g⁻¹ (colim_i f_{i,*}F_i) = colim_i g⁻¹ f_{i,*}F_i
          = colim_i f'_{i,*}(g'_i)⁻¹F_i = f'_* (g')⁻¹ F
```

with `F_i = p_{i,*}F` the direct image of `F` along the projection `p_i : X ⟶ X_i`. The third
equality is [Stacks, Tag 0959] at each stage; the first two are bookkeeping, because the diagram
`i ↦ f_{i,*}F_i` is *constant* up to the canonical comparison of direct images along a composite;
the last is the conjunction of the second half of [Stacks, Tag 0EYN] and the interchange of a
direct image with such a colimit.

This file assembles the links of that chain that do not depend on those two colimit statements.

## Main results

* `Stacks.EtaleCohomology.isIso_smallEtaleSetsBaseChange_of_isFinite` and
  `Stacks.EtaleCohomology.isIso_smallEtaleSetsBaseChange_app_of_isFinite` — **[Stacks, Tag 0959]
  for sheaves of sets on Mathlib's small étale sites**, for a square of bare schemes.
* `Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeNatTrans_of_isIso_smallEtaleSetsBaseChange` —
  the passage from that presentation back to the size-bounded sites of [Stacks, Tag 021B], at an
  arbitrary big étale site containing the square.
* `Stacks.EtaleCohomology.stageDirectImageTransition_eq` and
  `Stacks.EtaleCohomology.stageDirectImageTransition_comp_iso` — **the system of direct images
  along the stages is the constant system at `f_* F`**, compatibly with its transitions, and in
  particular every transition of it is an isomorphism
  (`Stacks.EtaleCohomology.isIso_stageDirectImageTransition`).
* `Stacks.EtaleCohomology.isIso_stageBaseChange` — **[Stacks, Tag 0959] at each stage of the
  system**, which is the stagewise isomorphism of the third equality above.

## Main definitions

* `Stacks.EtaleCohomology.stageSheafAt` and `Stacks.EtaleCohomology.stageSheaf` — the sheaf
  `F_i = p_{i,*}F` on a stage, at arbitrary coefficients and at sheaves of sets.
* `Stacks.EtaleCohomology.stageDirectImage`, `Stacks.EtaleCohomology.stageDirectImageIso`,
  `Stacks.EtaleCohomology.stageDirectImageTransition` — the diagram `i ↦ f_{i,*}F_i` whose
  colimit the source takes, its identification with the constant diagram at `f_* F`, and its
  transition morphisms.
* `Stacks.EtaleCohomology.stageComparison` — the stagewise base change comparison
  `g⁻¹ f_{i,*}F_i ⟶ f'_{i,*}(g'_i)⁻¹F_i`.
* `Stacks.EtaleCohomology.projectionComparison` — the base change comparison
  `(g'_i)⁻¹ p_{i,*}F ⟶ p'_{i,*}(g')⁻¹F` of the *upper* square of the system, whose right vertical
  morphism `p_i` is integral but not finite.
* `Stacks.EtaleCohomology.stageLeg` — the canonical map
  `f'_{i,*}(g'_i)⁻¹F_i ⟶ f'_*(g')⁻¹F`, the direct image along `f'_i` of the preceding comparison
  followed by the comparison of direct images along `f' = p'_i ≫ f'_i`. This is the cocone whose
  being a colimit cocone is the last equality of the chain.

## Implementation notes

**Every stage morphism is in plain-corner form.** Not one signature below names
`S.structureMap.app i` or `S.projection.app i`; they all use
`Stacks.EtaleCohomology.IntegralSquareLimitData.structureMapAt` and its three companions, whose
sources and targets are written as `X`, `X'`, `Y`, `Y'` rather than as the value at `i` of a
constant functor. The docstring of that definition says why this is load-bearing rather than
cosmetic, and `Stacks.EtaleCohomology.stageComparison_comp_stageLeg` is the declaration that
cannot be checked without it.

**Which presentation of the small étale site.** The statements of this file are about Mathlib's
small étale sites, `AlgebraicGeometry.Scheme.smallEtaleTopology`, not about the size-bounded sites
of [Stacks, Tag 021B], and the comparison is
`Stacks.EtaleCohomology.smallEtaleSetsBaseChange`. This is forced by the geometry: the stages
`X_i` of the limit presentation are produced by [Stacks, Tag 09YZ] and nothing bounds their size,
so a bounded site containing the four corners of the given square need not contain them.
`isIso_smallEtaleBaseChangeNatTrans_of_isIso_smallEtaleSetsBaseChange` carries a statement in
this presentation to `AlgebraicGeometry.smallEtaleBaseChangeNatTrans` at any big étale site, so
nothing is lost. The existing presentation-independent datum
`AlgebraicGeometry.IntegralBaseChangeColimitPresentation` is *not* usable for the same reason:
its stages are objects of a fixed big étale site.

Conversely, [Stacks, Tag 0959] is proved in the library only for the bounded sites, so
`isIso_smallEtaleSetsBaseChange_of_isFinite` has to discharge the site; this is the four-element
`AlgebraicGeometry.BigEtaleSite.ofSet` argument of `exists_bigEtaleSite_square`, as in
`Stacks.EtaleCohomology.h0EYP_of_setsLevel0EYP`.

**The constant diagram.** `Stacks.EtaleCohomology.stageDirectImageTransition` is defined from the
comparisons of direct images along composites rather than from
`Stacks.EtaleCohomology.coneDirectImageMap`, to which it is adjoint: the two agree by the
definition of that map, which is the transpose of
`Stacks.EtaleCohomology.coneDirectImageComp`. That it is compatible with the identification of
the diagram with the constant one is the associativity pentagon of those comparisons, in the form
`Stacks.EtaleCohomology.smallEtalePushforwardComp'_inv_app_cocycle`, applied to the threefold
composite `p_i`, `f_{ij}`, `st_j`; no further input is needed.

**What this file leaves to the next one.** The chain above closes once one knows that

```
(g⁻¹ (stageDirectImageIso i)) ≫ (base change comparison of the given square at F)
  = stageComparison i ≫ stageLeg i,
```

the vertical pasting law for the base-change comparison applied to the decomposition of the
given square into the upper square over `g'_i` and the stage square over `g`. The tree has the
pasting law in the *horizontal* direction only, for abelian coefficients
(`Stacks.EtaleCohomology.smallEtaleBaseChangeAb_paste`); the identity above pastes in the
direction of the direct images, so it is `CategoryTheory.mateEquiv_vcomp` together with the
vertical pasting of `Stacks.EtaleCohomology.smallEtaleSquarePushforwardIsoAt`, which is again the
associativity pentagon. That law is
`Stacks.EtaleCohomology.smallEtaleSetsBaseChange_vpaste_app'`, and the identity above is its
instance at the limit presentation,
`Stacks.EtaleCohomology.stageComparison_comp_stageLeg`, proved in the module
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.IntegralBaseChangeAffineCaseColimit`.
Granted it, invertibility of the given comparison is equivalent to
invertibility of `stageLeg i`, and that is what the two colimit statements — the second half of
[Stacks, Tag 0EYN] and the interchange of `f'_*` with the colimit — deliver, the diagram
`i ↦ f'_{i,*}(g'_i)⁻¹F_i` having invertible transitions by
`isIso_stageDirectImageTransition` and `isIso_stageBaseChange`.

**No `@[stacks 0EYP]` attribute is attached.** Nothing here is a proof of that tag; the links
above are its ingredients.

## References

* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe w' w u

namespace Stacks.EtaleCohomology

/-! ### Discharging the big étale site -/

section Site

variable {X' X Y' Y : Scheme.{u}}

/-- A big étale site containing the four corners of a square of schemes. The four schemes form a
four-element, hence `Small.{u}`, set, so `AlgebraicGeometry.BigEtaleSite.ofSet` applies. -/
theorem exists_bigEtaleSite_square (X' X Y' Y : Scheme.{u}) :
    ∃ B : BigEtaleSite.{u},
      B.Contains X' ∧ B.Contains X ∧ B.Contains Y' ∧ B.Contains Y := by
  have := small_single.{u} Y
  have : Small.{u} ({X', X, Y', Y} : Set Scheme.{u}) := inferInstance
  refine ⟨BigEtaleSite.ofSet ({X', X, Y', Y} : Set Scheme.{u}), ?_, ?_, ?_, ?_⟩ <;>
    exact BigEtaleSite.contains_ofSet _ (by simp)

/-- **Stacks 0959 for sheaves of sets on Mathlib's small étale sites.** For a cartesian square

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

of schemes with `f` finite, the base change comparison `g⁻¹ f_* ⟶ f'_* (g')⁻¹` on Mathlib's
small étale sites is an isomorphism.

The library proves Stacks 0959 for the size-bounded sites of Stacks 021B, hence for a square of
the underlying category of a big étale site; `exists_bigEtaleSite_square` produces such a site
containing the four corners, and the two site transfers
`AlgebraicGeometry.SmallEtale.isIso_mateEquiv_symm_unboundedBaseChangeMate` and
`isIso_mateEquiv_symm_unboundedBaseChangeMate_iff` carry the statement to Mathlib's sites. -/
theorem isIso_smallEtaleSetsBaseChange_of_isFinite (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (sq : IsPullback g' f' f g) [IsFinite f] :
    IsIso (smallEtaleSetsBaseChange.{u, 0} g' f' f g sq.w) := by
  obtain ⟨B, hX', hX, hY', hY⟩ := exists_bigEtaleSite_square X' X Y' Y
  let bg' : B.obj X' hX' ⟶ B.obj X hX := ObjectProperty.homMk g'
  let bf' : B.obj X' hX' ⟶ B.obj Y' hY' := ObjectProperty.homMk f'
  let bf : B.obj X hX ⟶ B.obj Y hY := ObjectProperty.homMk f
  let bg : B.obj Y' hY' ⟶ B.obj Y hY := ObjectProperty.homMk g
  have hcomm : bg' ≫ bf = bf' ≫ bg := ObjectProperty.hom_ext _ sq.w
  have : IsFinite (B.inclusion.map bf) := inferInstanceAs (IsFinite f)
  have key := AlgebraicGeometry.SmallEtale.isIso_mateEquiv_symm_unboundedBaseChangeMate B bf bg
    bg' bf' sq hcomm (bg' ≫ bf) rfl hcomm.symm
    (smallEtaleSetsAdjunction.{u, 0} g) (smallEtaleSetsAdjunction.{u, 0} g')
  rwa [isIso_mateEquiv_symm_unboundedBaseChangeMate_iff B bf bg bg' bf' (bg' ≫ bf) rfl hcomm.symm
    sq.w] at key

/-- **Stacks 0959 for sheaves of sets on Mathlib's small étale sites, at a single sheaf.** The
componentwise form of `Stacks.EtaleCohomology.isIso_smallEtaleSetsBaseChange_of_isFinite`.

It is stated here, about plain variables, rather than derived at each use: with the stages of an
inverse system substituted for the four corners the arguments are large terms, and the kernel
does not get through the defeq check of the resulting type. -/
theorem isIso_smallEtaleSetsBaseChange_app_of_isFinite (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback g' f' f g) [IsFinite f]
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    IsIso ((smallEtaleSetsBaseChange.{u, 0} g' f' f g sq.w).app F) :=
  have := isIso_smallEtaleSetsBaseChange_of_isFinite g' f' f g sq
  NatIso.isIso_app_of_isIso _ F

/-- **The base change comparison of the size-bounded sites of Stacks 021B from the comparison of
Mathlib's sites.** For a commuting square of the underlying category of a big étale site,
invertibility of the base change comparison for sheaves of sets on Mathlib's small étale sites
forces invertibility of `AlgebraicGeometry.smallEtaleBaseChangeNatTrans`, the comparison on the
bounded sites.

This is the composite of the two transfers of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SetsToAbelianBaseChangeBridge`:
`isIso_mateEquiv_symm_unboundedBaseChangeMate_iff` read from right to left, and
`isIso_smallEtaleBaseChangeNatTrans_of_isIso_mateEquiv_symm`. Its point is that the bounded
statement does not depend on the choice of big étale site: the comparison on Mathlib's sites
mentions no site at all, so a bounded statement proved at one site transfers to every other site
containing the square. -/
theorem isIso_smallEtaleBaseChangeNatTrans_of_isIso_smallEtaleSetsBaseChange
    (B : BigEtaleSite.{u}) {Z Z' W W' : B.Scheme} (a : Z ⟶ W) (b : W' ⟶ W) (b' : Z' ⟶ Z)
    (a' : Z' ⟶ W') (h : b' ≫ a = a' ≫ b)
    (hsets : IsIso (smallEtaleSetsBaseChange.{u, 0} (B.inclusion.map b')
      (B.inclusion.map a') (B.inclusion.map a) (B.inclusion.map b)
      (by simpa using congrArg B.inclusion.map h))) :
    IsIso (smallEtaleBaseChangeNatTrans B b' a' a b h) := by
  refine isIso_smallEtaleBaseChangeNatTrans_of_isIso_mateEquiv_symm B a b b' a' h (b' ≫ a) rfl
    h.symm (smallEtaleSetsAdjunction.{u, 0} (B.inclusion.map b))
    (smallEtaleSetsAdjunction.{u, 0} (B.inclusion.map b')) ?_
  rwa [isIso_mateEquiv_symm_unboundedBaseChangeMate_iff B a b b' a' (b' ≫ a) rfl h.symm
    (by simpa using congrArg B.inclusion.map h)]

end Site

/-! ### The system of direct images along the stages is constant -/

section ConstantDiagram

variable {X X' Y Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (S : IntegralSquareLimitData g' f' f g) (A : Type w) [Category.{w'} A]
  (F : Sheaf (smallEtaleTopology X) A)

/-- The cone exhibiting `X` as the limit of the system of finite schemes over `Y`. -/
abbrev limitCone : Cone S.diagram := Cone.mk X S.projection

/-- The sheaf `F_i = p_{i,*}F` on the small étale site of the stage `X_i`. This is
`Stacks.EtaleCohomology.coneDirectImage` of `Stacks.EtaleCohomology.limitCone`, written with the
projection's source as `X`: see
`Stacks.EtaleCohomology.IntegralSquareLimitData.projectionAt`. -/
abbrev stageSheafAt (i : S.indexTypeᵒᵖ) : Sheaf (smallEtaleTopology (S.diagram.obj i)) A :=
  (smallEtalePushforward (S.projectionAt i) A).obj F

/-- The direct image `f_{i,*} F_i = st_{i,*} p_{i,*} F` of `F` along a stage of the system. -/
abbrev stageDirectImage (i : S.indexTypeᵒᵖ) : Sheaf (smallEtaleTopology Y) A :=
  (smallEtalePushforward (S.structureMapAt i) A).obj (stageSheafAt S A F i)

/-- **The system of direct images along the stages is constant.** The direct image of
`F_i = p_{i,*} F` along the structure morphism `st_i : X_i ⟶ Y` is `f_* F`, because
`f = p_i ≫ st_i`; the identification is the comparison of direct images along a composite.

This is the step [Stacks, Tag 0EYP] spends a line on: the diagram `i ↦ f_{i,*} F_i` whose colimit
the source takes is constant up to this canonical isomorphism. -/
def stageDirectImageIso (i : S.indexTypeᵒᵖ) :
    stageDirectImage S A F i ≅ (smallEtalePushforward f A).obj F :=
  (smallEtalePushforwardComp' (S.projectionAt i) (S.structureMapAt i) f
    (S.projectionAt_comp_structureMapAt i).symm A).app F

/-- The transition morphism `f_{j,*}F_j ⟶ f_{i,*}F_i` of the system of direct images along the
stages, for a transition `a : i ⟶ j` of the index category.

Its first factor is the transposed system map `φ_{ij} : F_j ⟶ f_{ij,*}F_i` of
`Stacks.EtaleCohomology.directImageSystem`, which by the definition of
`Stacks.EtaleCohomology.coneDirectImageMap` is the inverse of the comparison of direct images
along `p_j = p_i ≫ f_{ij}`; the second is the comparison along `st_i = f_{ij} ≫ st_j`. -/
def stageDirectImageTransition {i j : S.indexTypeᵒᵖ} (a : i ⟶ j) :
    stageDirectImage S A F j ⟶ stageDirectImage S A F i :=
  (smallEtalePushforward (S.structureMapAt j) A).map
      ((smallEtalePushforwardComp' (S.projectionAt i) (S.diagram.map a) (S.projectionAt j)
        (S.projectionAt_comp_map a).symm A).inv.app F) ≫
    (smallEtalePushforwardComp' (S.diagram.map a) (S.structureMapAt j)
        (S.structureMapAt i) (S.map_comp_structureMapAt a).symm A).hom.app
      (stageSheafAt S A F i)

/-- **The transition morphism is the identity of `f_* F` conjugated by the identification with
the constant system.** This is the associativity pentagon of the comparison of direct images, in
the form `Stacks.EtaleCohomology.smallEtalePushforwardComp'_inv_app_cocycle`, applied to the
threefold composite `p_i`, `f_{ij}`, `st_j`. -/
theorem stageDirectImageTransition_eq {i j : S.indexTypeᵒᵖ} (a : i ⟶ j) :
    stageDirectImageTransition S A F a =
      (stageDirectImageIso S A F j).hom ≫ (stageDirectImageIso S A F i).inv := by
  have hcoc := smallEtalePushforwardComp'_inv_app_cocycle (S.projectionAt i)
    (S.diagram.map a) (S.structureMapAt j) (S.projectionAt j)
    (S.projectionAt_comp_map a).symm (S.structureMapAt i)
    (S.map_comp_structureMapAt a).symm f (S.projectionAt_comp_structureMapAt j).symm
    (S.projectionAt_comp_structureMapAt i).symm A F
  rw [← Iso.inv_comp_eq]
  simp only [stageDirectImageIso, Iso.app_inv, stageDirectImageTransition]
  rw [← Category.assoc, hcoc]
  simp

/-- **The identification of the system of direct images with the constant system is compatible
with the transitions**: the diagram `i ↦ f_{i,*} F_i` of
`Stacks.EtaleCohomology.stageDirectImage`, with the transitions of
`Stacks.EtaleCohomology.stageDirectImageTransition`, is the constant diagram at `f_* F` up to
`Stacks.EtaleCohomology.stageDirectImageIso`. -/
theorem stageDirectImageTransition_comp_iso {i j : S.indexTypeᵒᵖ} (a : i ⟶ j) :
    stageDirectImageTransition S A F a ≫ (stageDirectImageIso S A F i).hom =
      (stageDirectImageIso S A F j).hom := by
  rw [stageDirectImageTransition_eq]
  simp

/-- Every transition morphism of the system of direct images along the stages is an
isomorphism. -/
instance isIso_stageDirectImageTransition {i j : S.indexTypeᵒᵖ} (a : i ⟶ j) :
    IsIso (stageDirectImageTransition S A F a) := by
  rw [stageDirectImageTransition_eq]
  infer_instance

end ConstantDiagram

/-! ### The comparison at a stage, and the leg over it -/

section Stage

variable {X X' Y Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (S : IntegralSquareLimitData g' f' f g) (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))

/-- The sheaf `F_i = p_{i,*}F` on the small étale site of the stage `X_i`. -/
abbrev stageSheaf (i : S.indexTypeᵒᵖ) :
    Sheaf (smallEtaleTopology (S.diagram.obj i)) (Type (u + 1)) :=
  stageSheafAt S (Type (u + 1)) F i

/-- **The base change comparison of the cartesian square at a stage**, applied to
`F_i = p_{i,*}F`: the map `g⁻¹ f_{i,*}F_i ⟶ f'_{i,*}(g'_i)⁻¹F_i`.

The type is written as the application of the natural transformation, with the two composites of
functors left composed, rather than with the inner `.obj` written out: the kernel does not get
through the defeq check that rebracketing an inverse image costs.

Every stage morphism entering it is the plain-corner form
`Stacks.EtaleCohomology.IntegralSquareLimitData.structureMapAt`, never
`S.structureMap.app i`, and that is not cosmetic: with the component spelling the corner `Y` of
`Stacks.EtaleCohomology.smallEtaleSetsBaseChange` is `((Functor.const _).obj Y).obj i`, so this
comparison is not syntactically an instance of any lemma stated over plain `Y`, and deciding the
two forces the kernel through that definition — the mate of the square comparison of composite
direct images. The docstring of
`Stacks.EtaleCohomology.IntegralSquareLimitData.structureMapAt` records the rule.

The *body* writes the direct image `p_{i,*}F` out rather than naming it
`Stacks.EtaleCohomology.stageSheaf`, for the same reason one step further on. A consumer reaches
this comparison through a lemma stated about plain variables, whose instance carries
`(smallEtalePushforward (S.projectionAt i) _).obj F`; identifying that with `stageSheaf S F i`
*under the `.app`* means comparing two values of one and the same base change map at arguments
that are only definitionally equal, and that measures as fatal — the kernel descends into the
mate rather than comparing the arguments. With the body written out the two agree syntactically
and nothing has to be decided. The *type* still names `stageSheaf`: there it sits under `.obj`,
where the check is cheap. -/
abbrev stageComparison (i : S.indexTypeᵒᵖ) :
    (smallEtaleDirectImage.{u, 0} (S.structureMapAt i) ⋙
        smallEtaleInverseImage.{u, 0} g).obj (stageSheaf S F i) ⟶
      (smallEtaleInverseImage.{u, 0} (S.horizontal.app i) ⋙
        smallEtaleDirectImage.{u, 0} (S.structureMapAt' i)).obj (stageSheaf S F i) :=
  (smallEtaleSetsBaseChange.{u, 0} (S.horizontal.app i) (S.structureMapAt' i)
    (S.structureMapAt i) g (S.isPullbackStageAt i).w).app
    ((smallEtalePushforward (S.projectionAt i) (Type (u + 1))).obj F)

/-- **Stacks 0959 at a stage of the system.** The square at a stage is cartesian and its right
vertical morphism `st_i : X_i ⟶ Y` is finite, so the base change comparison there is an
isomorphism. This is the only geometric input of [Stacks, Tag 0EYP] beyond the limit
presentation of the square, and in particular `Stacks.EtaleCohomology.stageComparison` is an
isomorphism for every sheaf, by `CategoryTheory.NatIso.isIso_app_of_isIso`.

The statement is at the level of the natural transformation rather than of its value at
`Stacks.EtaleCohomology.stageSheaf`: the kernel does not get through the defeq check of the
value form, whose type carries an inverse image applied to a stage of the system. -/
instance isIso_stageBaseChange (i : S.indexTypeᵒᵖ) :
    IsIso (smallEtaleSetsBaseChange.{u, 0} (S.horizontal.app i) (S.structureMapAt' i)
      (S.structureMapAt i) g (S.isPullbackStageAt i).w) :=
  haveI := S.isFinite_structureMapAt i
  isIso_smallEtaleSetsBaseChange_of_isFinite (S.horizontal.app i) (S.structureMapAt' i)
    (S.structureMapAt i) g (S.isPullbackStageAt i)

/-- **The base change comparison of the upper square of the system**, applied to `F`: the map
`(g'_i)⁻¹ p_{i,*}F ⟶ p'_{i,*}(g')⁻¹F`.

The upper square is cartesian — this is
`Stacks.EtaleCohomology.IntegralSquareLimitData.isPullback_projectionAt` — but its right vertical
morphism `p_i : X ⟶ X_i` is only integral, not finite, so Stacks 0959 does not apply to it. It is
the colimit over `i` of these comparisons that carries the content of [Stacks, Tag 0EYP]. -/
abbrev projectionComparison (i : S.indexTypeᵒᵖ) :
    (smallEtaleDirectImage.{u, 0} (S.projectionAt i) ⋙
        smallEtaleInverseImage.{u, 0} (S.horizontal.app i)).obj F ⟶
      (smallEtaleInverseImage.{u, 0} g' ⋙
        smallEtaleDirectImage.{u, 0} (S.projectionAt' i)).obj F :=
  (smallEtaleSetsBaseChange.{u, 0} g' (S.projectionAt' i) (S.projectionAt i)
    (S.horizontal.app i) (S.projectionAt'_comp_horizontal i).symm).app F

/-- **The canonical leg `f'_{i,*}(g'_i)⁻¹F_i ⟶ f'_*(g')⁻¹F`** of the cocone whose colimit
[Stacks, Tag 0EYP] computes: the direct image along `f'_i` of the comparison of the upper square,
followed by the comparison of direct images along `f' = p'_i ≫ f'_i`.

The body writes the comparison of the upper square out rather than naming
`Stacks.EtaleCohomology.projectionComparison`, for the reason recorded at
`Stacks.EtaleCohomology.stageComparison`: a consumer comparing this leg with the value of a lemma
stated about plain variables must find the two sides syntactically equal, and must not have to
decide an equality of values of a base change map on the way.
`Stacks.EtaleCohomology.stageComparison_comp_stageLeg` is that consumer. -/
def stageLeg (i : S.indexTypeᵒᵖ) :
    (smallEtaleDirectImage.{u, 0} (S.structureMapAt' i)).obj
        ((smallEtaleDirectImage.{u, 0} (S.projectionAt i) ⋙
          smallEtaleInverseImage.{u, 0} (S.horizontal.app i)).obj F) ⟶
      (smallEtaleDirectImage.{u, 0} f').obj ((smallEtaleInverseImage.{u, 0} g').obj F) :=
  (smallEtaleDirectImage.{u, 0} (S.structureMapAt' i)).map
      ((smallEtaleSetsBaseChange.{u, 0} g' (S.projectionAt' i) (S.projectionAt i)
        (S.horizontal.app i) (S.projectionAt'_comp_horizontal i).symm).app F) ≫
    (smallEtalePushforwardComp' (S.projectionAt' i) (S.structureMapAt' i) f'
      (S.projectionAt'_comp_structureMapAt' i).symm (Type (u + 1))).hom.app
      ((smallEtaleInverseImage.{u, 0} g').obj F)

/-! ### A big étale site containing the whole limit presentation -/

/-- **A big étale site containing the four corners of the square *and every stage of a limit
presentation of it*.** The index of a `Stacks.EtaleCohomology.IntegralSquareLimitData` is a
`Type u`, so the stages of its two systems form the ranges of two functions out of a `Type u`;
together with the four corners they are a `Small.{u}` set of schemes, and
`AlgebraicGeometry.BigEtaleSite.ofSet` produces a big étale site containing all of them.

This corrects the implementation note of this file, which recorded that "nothing bounds the size
of the stages, so a bounded site containing the four corners of the given square need not contain
them" and concluded that the chain of [Stacks, Tag 0EYP] has to be run on Mathlib's small étale
sites. The first half is true of a site chosen for the corners alone; the conclusion does not
follow, because the site may be chosen for the presentation instead. That matters because the
inverse-system machinery of [Stacks, Tag 0EYL] and [Stacks, Tag 09YN] — including
`Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimit_limitToSmallEtale`, the second
half of [Stacks, Tag 0EYN] — is stated only for the size-bounded sites of [Stacks, Tag 021B], and
`AlgebraicGeometry.Scheme.smallEtaleSheafEquiv` carries sheaves between the two presentations for
a bare scheme. -/
theorem exists_bigEtaleSite_integralSquareLimitData :
    ∃ B : BigEtaleSite.{u}, B.Contains X ∧ B.Contains X' ∧ B.Contains Y ∧ B.Contains Y' ∧
      (∀ i, B.Contains (S.diagram.obj i)) ∧ ∀ i, B.Contains (S.diagram'.obj i) := by
  have := small_single.{u} Y'
  have : Small.{u} (({X, X', Y, Y'} : Set Scheme.{u}) ∪ Set.range S.diagram.obj ∪
      Set.range S.diagram'.obj : Set Scheme.{u}) := inferInstance
  refine ⟨BigEtaleSite.ofSet (({X, X', Y, Y'} : Set Scheme.{u}) ∪ Set.range S.diagram.obj ∪
      Set.range S.diagram'.obj), ?_, ?_, ?_, ?_, fun i => ?_, fun i => ?_⟩ <;>
    exact BigEtaleSite.contains_ofSet _ (by simp)

end Stage

end Stacks.EtaleCohomology

end
