module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleSchemeAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedKernelIdealSquareMapAgreement

/-!
# Naturality of the conormal comparison of Stacks 04G2 (1) in the closed immersion

Let
```
R --j--→ V
|        |
b        a
↓        ↓
R' -j'-→ V'
```
be a commutative square of the big fppf category over a scheme `S` contained in a big fppf site
`B` whose two horizontal morphisms are closed immersions of schemes.  Part (1) of
[Stacks Project, Tag 04G2] — `AlgebraicGeometry.Space.conormalModuleClosedSubspaceRangeIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeAgreement.lean` — identifies the
conormal module of the closed subspace that `j` cuts out, read on `yoneda.obj R`, with the module
which the Zariski conormal sheaf of the underlying morphism of schemes becomes on the small étale
site.  This file states and proves that **that comparison is natural in the square**: it carries
the spaces-side canonical map of conormal modules of [Stacks Project, Tag 04CP] to the associated
module of the schemes-side map of Morphisms, Lemma [Stacks Project, Tag 01R4].

## Main definitions

* `AlgebraicGeometry.Space.representedConormalDefiningIdealIso`: part (1)'s comparison **respelled
  as the transport of the inverse image at the ideal sheaf** — the inverse of
  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` at
  `Stacks.ClosedImmersion.idealSheaf`, corrected by
  `AlgebraicGeometry.Space.representedAssociatedModuleIdealSheafIso`.
* `AlgebraicGeometry.Space.representedConormalKernelIdealZPowIso`: the same at the
  `AlgebraicGeometry.Space.kernelIdealSheafZPow` spelling, which is the spelling the canonical map
  of a square is stated at.

## Main results

* `AlgebraicGeometry.Space.representedDefiningIdealPullbackConormalSheafIso_hom_comp` and
  `AlgebraicGeometry.Space.conormalModuleRepresentedIso_hom_comp`: **the respelling is the
  registered comparison**, read against
  `Stacks.CartierConormal.conormalSheafIsoPullbackSelf`.  Before this file
  `AlgebraicGeometry.Space.conormalModuleClosedSubspaceRangeIso` had no derived statement of any
  kind.
* `AlgebraicGeometry.Space.representedConormalKernelIdealZPowIso_hom_eq`: the two spellings of the
  respelling differ by the equality of sheaves of ideals
  `AlgebraicGeometry.Space.kernelIdealSheafZPow_one_representedSpaceMap`.
* `AlgebraicGeometry.Space.conormalSheafMap_representedConormalKernelIdealZPowIso`: **the
  naturality.**  The comparison carries the composite
  `AlgebraicGeometry.Space.squarePullbackCompIso` followed by the inverse image along `j` of
  `AlgebraicGeometry.Space.kernelIdealSquareMap` — which is
  `AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap` in degree one, by
  `AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap_eq_comp` — to the associated module of
  `Stacks.ClosedImmersion.conormalSheafMap`.

## What the naturality assumes, and what that assumption is

The naturality is proved from one hypothesis, `hΞ`: that the transport
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` carries the ringed-space square
comparison `Stacks.ClosedImmersion.pullbackCompIso` to the spaces-side square comparison
`AlgebraicGeometry.Space.squarePullbackCompIso`, read at
`Stacks.ClosedImmersion.idealSheaf` of `j'`.  That is **not a placeholder predicate and not a
quantified assumption**: it is a single equation between two composites of existing morphisms, and
it is exactly the obligation that the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeAgreement.lean` and of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleImmersionFunctorial.lean` record as part (2)
of [Stacks Project, Tag 04G2]'s single remaining one — the compatibility of that transport with
**composition** of represented morphisms, since
`AlgebraicGeometry.Space.squarePullbackCompIso` is two
`AlgebraicGeometry.Space.modulePullbackCompIso`s and
`Stacks.ClosedImmersion.pullbackCompIso` is two
`RingedSpaceModuleAdjunction.modulePullbackComp`s.  The reduction so far of that compatibility is
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_of_objComp` of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedAssociatedModulePullbackComposition.lean`, whose
own residue is a statement about
`AlgebraicGeometry.Space.representedModuleObjPullbackIso`.

Everything else the naturality needs is discharged here from existing statements: the ideal-sheaf
level of the agreement
(`AlgebraicGeometry.Space.kernelIdealSquareMap_representedAssociatedModuleKernelIdealZPowIso`),
the naturality of the square comparison with a tail
(`AlgebraicGeometry.Space.squarePullbackCompIso_hom_app_naturality_comp`), the naturality of the
transport in the module
(`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_naturality`) and the two
factorisations that hold by `rfl`.

## Implementation notes

**The whole naturality is one application of a generic lemma whose morphisms all live in one
category.**  `Stacks.CategoryTheory.square_conormal_eq` takes the eight equations the argument
uses as hypotheses and mentions no functor and no object outside the category the comparison
lands in, so nothing at the point of use is a restatement; the geometric instance supplies eight
existing lemmas.  That is what makes the instantiation affordable.

`AlgebraicGeometry.Space.modulePullback`,
`AlgebraicGeometry.Space.modulePullbackCompIso` and
`AlgebraicGeometry.Space.representedModuleObjPullbackIso` are made file-locally irreducible.  The
first two as in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeAgreement.lean`; without them even the
`rfl` reading of the registered comparison's forward map is a `whnf` timeout.  The third as in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedAssociatedModulePullbackComposition.lean`;
without it the unification that identifies the transport appearing in two existing statements walks
into its construction.

**An `eqToHom` of the equality of sheaves of ideals is a kernel wall, and the remedy is to pick
the spelling in which it does not occur.**  If the bridge
`AlgebraicGeometry.Space.representedDefiningIdealPullbackConormalSheafIso_hom_comp` is stated
with the respelling taken at `AlgebraicGeometry.Space.kernelIdealSheafZPow`, the two sides'
sources differ by `eqToHom` of
`AlgebraicGeometry.Space.kernelIdealSheafZPow_one_representedSpaceMap`, and proving the generic
lemma by `subst` on that equality elaborates but is then a **kernel** deterministic timeout; it
checks only at 2 000 000 heartbeats, and no `irreducible` attribute helps because no attribute
reaches the kernel.  Stated at
the `AlgebraicGeometry.Space.definingIdealSheaf` spelling, where the respelling's target is the
registered comparison's source on the nose and no `eqToHom` occurs anywhere, the same bridge
checks inside the 200 000-heartbeat budget.  The passage between the two spellings is then
affordable on its own, as
`AlgebraicGeometry.Space.representedConormalKernelIdealZPowIso_hom_eq`.

**`Stacks.ClosedImmersion.idealSheafMap`, `Stacks.ClosedImmersion.pullbackCompIso` and
`Stacks.ClosedImmersion.conormalSheafMap` need their four implicit morphisms written out.**  Left
to unification against the expected type the *statement alone* is a `whnf` timeout, exactly as the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedKernelIdealSquareMapAgreement.lean` record for
the first of the three.

The naturality is **not** restated at
`AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap`, although that is the form 04G2 (2) and
[Stacks Project, Tag 04AM] consume.  `AlgebraicGeometry.Space.conormalAlgebra` ·`piece 1` and
`(modulePullback j)^*(Ker(j^♯))` are equal by `rfl`
(`AlgebraicGeometry.Space.conormalAlgebra_piece`) but not at reducible transparency, so composing
the comparison with the canonical map of the square is rejected by the elaborator; a consumer
should move between the two by
`AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap_eq_comp`, whose right-hand side is exactly
the composite this file's naturality is stated at, in its own file where the graded spelling is
native.

No `@[stacks]` attribute is claimed.  A naturality square is not a Stacks tag, and part (2) of
[Stacks Project, Tag 04G2] is not asserted here.  `hΞ` itself is **proved**: it is
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_squarePullbackCompIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquareTransportAgreement.lean`, and the naturality
below is restated there with nothing assumed as
`AlgebraicGeometry.Space.conormalSheafMap_representedConormalKernelIdealZPowIso_of_comp_eq`.
What part (2) still needs is named in the section "What the reduction of `hnat` still
owes" of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleRepresentedImmersionNaturality.lean`.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace Stacks.CategoryTheory

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] {F : Type u₄} [Category.{v₄} F]

/-- Cancelling an isomorphism written inside two nested functors. -/
theorem map_map_comp_inv_comp_map_map_hom (G : E ⥤ C) (A : F ⥤ E) {X Y Z : F} (u : X ⟶ Z)
    (e : Y ≅ Z) :
    G.map (A.map (u ≫ e.inv)) ≫ G.map (A.map e.hom) = G.map (A.map u) := by
  rw [← G.map_comp, ← A.map_comp]; simp

/-- **The algebra of the bridge between two presentations of one transported comparison.** -/
theorem transport_bridge_eq (P : D ⥤ C) {D₁ D₂ D₃ : D} {α' : D₁ ⟶ D₂} {ν : D₂ ⟶ D₃}
    {C₁ C₂ C₃ : C} {β : P.obj D₂ ⟶ C₁} {τ : P.obj D₃ ⟶ C₃}
    {w : C₁ ⟶ C₂} {w' : C₂ ⟶ C₃} {m : C₁ ⟶ C₃}
    {L : P.obj D₁ ⟶ C₂} {Ψinv : P.obj D₁ ⟶ C₃}
    (hL : L = P.map α' ≫ β ≫ w) (hΨ : Ψinv = P.map (α' ≫ ν) ≫ τ)
    (hw : w ≫ w' = m) (hnat : β ≫ m = P.map ν ≫ τ) :
    L ≫ w' = Ψinv := by
  rw [hL, hΨ, Category.assoc, Category.assoc, hw, hnat, P.map_comp, Category.assoc]

/-- A functor carries the inverse followed by the forward map of an isomorphism to the
identity. -/
theorem map_inv_comp_map_hom (P : D ⥤ C) {X Y : D} (e : X ≅ Y) :
    P.map e.inv ≫ P.map e.hom = 𝟙 (P.obj Y) := by
  exact (P.mapIso e).inv_hom_id

/-- A composite under two nested functors, split. -/
theorem map_map_comp_eq_of (G : E ⥤ C) (A : F ⥤ E) {X Y Z : F} {w : X ⟶ Z} (x : X ⟶ Y)
    (y : Y ⟶ Z) (h : w = x ≫ y) : G.map (A.map x) ≫ G.map (A.map y) = G.map (A.map w) := by
  rw [h]; simp

/-- A functor applied to a factorisation. -/
theorem map_eq_map_comp_map (P : D ⥤ C) {X Y Z : D} {w : X ⟶ Z} (x : X ⟶ Y) (y : Y ⟶ Z)
    (h : w = x ≫ y) : P.map w = P.map x ≫ P.map y := by
  rw [h, P.map_comp]

/-- A functor applied to an equation between a three-fold and a two-fold composite. -/
theorem map_comp₃_eq_map_comp₂_of (P : D ⥤ C) {X Y Z W U : D} (x : X ⟶ Y) (y : Y ⟶ Z)
    (z : Z ⟶ W) (u : X ⟶ U) (v : U ⟶ W) (h : x ≫ y ≫ z = u ≫ v) :
    P.map x ≫ P.map y ≫ P.map z = P.map u ≫ P.map v := by
  rw [← P.map_comp, ← P.map_comp, ← P.map_comp, h]

/-- Naturality read backwards: two isomorphisms conjugating a square carry it to the square of
the inverses. -/
theorem inv_comp_eq_comp_inv_of {X Y Z W : C} (eF : X ≅ Y) (eG : Z ≅ W) (u : X ⟶ Z) (v : Y ⟶ W)
    (h : u ≫ eG.hom = eF.hom ≫ v) : eF.inv ≫ u = v ≫ eG.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, eG.hom_inv_id, Category.comp_id]

/-- A factorisation under a functor, after a head. -/
theorem comp_map_eq_comp_map_comp_map (P : D ⥤ C) {X Y Z : D} {w : X ⟶ Z} (x : X ⟶ Y) (y : Y ⟶ Z)
    (h : w = x ≫ y) {W : C} (t : W ⟶ P.obj X) :
    t ≫ P.map w = (t ≫ P.map x) ≫ P.map y := by
  rw [map_eq_map_comp_map P x y h, Category.assoc]

/-- **The whole algebra of the conormal naturality square, at variables.**

Read against the geometric instance: `Ψ'map` is the inverse image along the left edge of the
part-(1) comparison at the right-hand immersion, `ξK` the square comparison at the ideal sheaf,
`mi` the inverse image of the map of ideal sheaves, `tb` the transport along the left edge,
`cm` the associated module of the schemes-side conormal map and `Pj` the part-(1) comparison at
the left-hand immersion.  Every morphism lives in one category and is implicit, determined by
the hypothesis naming it, so no argument at the point of use is a restatement. -/
theorem square_conormal_eq
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ A₉ A₁₀ : C}
    {Ψ'map : A₀ ⟶ A₂} {t' : A₀ ⟶ A₁} {e' : A₁ ⟶ A₂}
    {ξK : A₂ ⟶ A₄} {mi : A₄ ⟶ A₅} {ξM : A₁ ⟶ A₃} {eg : A₃ ⟶ A₄}
    {tb : A₀ ⟶ A₆} {pc : A₆ ⟶ A₇} {tj' : A₇ ⟶ A₈} {ta : A₈ ⟶ A₃} {taH : A₃ ⟶ A₈}
    {idm : A₈ ⟶ A₉} {psij : A₉ ⟶ A₅} {cm : A₆ ⟶ A₁₀} {jm : A₇ ⟶ A₁₀}
    {tjInv : A₁₀ ⟶ A₉} {Pj : A₁₀ ⟶ A₅}
    (h₁ : Ψ'map = t' ≫ e')
    (h₂ : e' ≫ ξK ≫ mi = ξM ≫ eg ≫ mi)
    (h₃ : t' ≫ ξM = tb ≫ pc ≫ tj' ≫ ta)
    (h₄ : taH ≫ idm ≫ psij = eg ≫ mi)
    (h₅ : ta ≫ taH = 𝟙 A₈)
    (h₆ : tj' ≫ idm = jm ≫ tjInv)
    (h₇ : Pj = tjInv ≫ psij)
    (h₈ : pc ≫ jm = cm) :
    Ψ'map ≫ ξK ≫ mi = tb ≫ cm ≫ Pj :=
  calc Ψ'map ≫ ξK ≫ mi
      = t' ≫ e' ≫ ξK ≫ mi := by rw [h₁, Category.assoc]
    _ = t' ≫ ξM ≫ eg ≫ mi := by rw [h₂]
    _ = (t' ≫ ξM) ≫ eg ≫ mi := by rw [Category.assoc]
    _ = (tb ≫ pc ≫ tj' ≫ ta) ≫ taH ≫ idm ≫ psij := by rw [h₃, h₄]
    _ = tb ≫ pc ≫ tj' ≫ (ta ≫ taH) ≫ idm ≫ psij := by simp only [Category.assoc]
    _ = tb ≫ pc ≫ (tj' ≫ idm) ≫ psij := by
          rw [h₅, Category.id_comp]; simp only [Category.assoc]
    _ = tb ≫ (pc ≫ jm) ≫ tjInv ≫ psij := by rw [h₆]; simp only [Category.assoc]
    _ = tb ≫ cm ≫ Pj := by rw [h₇, h₈]

end Stacks.CategoryTheory

namespace AlgebraicGeometry.Space

attribute [local irreducible] modulePullback modulePullbackCompIso
  representedModuleObjPullbackIso

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R V : BigFppfOver B S hS} (j : R ⟶ V)
    [hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)]

/-- **The comparison of [Stacks Project, Tag 04G2] (1), respelled as the transport of the
inverse image at the ideal sheaf.**  The module which the Zariski conormal sheaf of a represented
closed immersion becomes on the small étale site is the inverse image along the represented
morphism of the defining ideal sheaf of its range.

It is the inverse of `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` at
`Stacks.ClosedImmersion.idealSheaf`, followed by the inverse image of
`AlgebraicGeometry.Space.representedAssociatedModuleIdealSheafIso`; that it is the registered
comparison of part (1) is
`AlgebraicGeometry.Space.representedDefiningIdealPullbackConormalSheafIso_hom_comp`. -/
noncomputable def representedConormalDefiningIdealIso :
    (representedSmallEtaleModuleEquivalence B S hS R).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj R) R.left.property).obj
          (Stacks.ClosedImmersion.conormalSheaf
            ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)) ≅
      (modulePullback B S hS (representedSpaceMap B S hS j)).obj
        (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj)).toSheafOfModules :=
  (representedAssociatedModulePullbackIso B S hS j
      (relativelyRepresentable_yoneda_map B S hS j)
      (Stacks.ClosedImmersion.idealSheaf
        ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).symm ≪≫
    (modulePullback B S hS (representedSpaceMap B S hS j)).mapIso
      (representedAssociatedModuleIdealSheafIso B S hS V j hj)

/-- The two factors of `AlgebraicGeometry.Space.representedConormalDefiningIdealIso`, with the
second written out.  True by `rfl`; it is a declaration of its own so that the generic bridge
lemma receives it verbatim. -/
theorem representedConormalDefiningIdealIso_inv :
    (representedConormalDefiningIdealIso B S hS j).inv =
      (modulePullback B S hS (representedSpaceMap B S hS j)).map
          ((representedAssociatedModuleChartZariskiIdealSheafIso B S hS V
              (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
                (closedSubspaceRange B S hS j hj))
              (isQuasicoherentOnSite_definingIdealSheaf B S hS
                ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
                (closedSubspaceRange B S hS j hj))).inv ≫
            (representedSmallEtaleModuleEquivalence B S hS V).functor.map
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
                (chartZariskiIdealSheafSelfChartIsoIdealSheaf B S hS V j hj).hom)) ≫
        (representedAssociatedModulePullbackIso B S hS j
          (relativelyRepresentable_yoneda_map B S hS j)
          (Stacks.ClosedImmersion.idealSheaf
            ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).hom :=
  rfl

/-- The forward map of the registered comparison of part (1), written out.  True by `rfl`; the
local `irreducible` attributes are what make it so — see the implementation notes. -/
theorem representedDefiningIdealPullbackConormalSheafIso_hom :
    (representedDefiningIdealPullbackConormalSheafIso B S hS j).hom =
      (modulePullback B S hS (representedSpaceMap B S hS j)).map
          (representedAssociatedModuleChartZariskiIdealSheafIso B S hS V
            (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
              (closedSubspaceRange B S hS j hj))
            (isQuasicoherentOnSite_definingIdealSheaf B S hS
              ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
              (closedSubspaceRange B S hS j hj))).inv ≫
        (representedAssociatedModulePullbackIso B S hS j
            (relativelyRepresentable_yoneda_map B S hS j)
            (selfChartZariskiDefiningIdeal B S hS j)).hom ≫
          (representedSmallEtaleModuleEquivalence B S hS R).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj R) R.left.property).map
              ((Scheme.Modules.pullback (B.inclusion.map j.left)).map
                  (chartZariskiIdealSheafSelfChartIsoIdealSheaf B S hS V j hj).hom ≫
                (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
                  ((BigFppfOver.toScheme B S hS).map j)).inv)) :=
  rfl

/-- **The respelling is the registered comparison of [Stacks Project, Tag 04G2] (1).**  The
forward map of `AlgebraicGeometry.Space.representedDefiningIdealPullbackConormalSheafIso`,
followed by the associated module of `Stacks.CartierConormal.conormalSheafIsoPullbackSelf`, is the
inverse of `AlgebraicGeometry.Space.representedConormalDefiningIdealIso`.

The two differ by the position of the identification
`AlgebraicGeometry.Space.chartZariskiIdealSheafSelfChartIsoIdealSheaf` of the Zariski restriction
of the defining ideal sheaf with `Stacks.ClosedImmersion.idealSheaf`: the registered comparison
takes it after the transport and the respelling takes it before, and the naturality of the
transport in the module moves it across. -/
theorem representedDefiningIdealPullbackConormalSheafIso_hom_comp :
    (representedDefiningIdealPullbackConormalSheafIso B S hS j).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS R).functor.map
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj R) R.left.property).map
            (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
              ((BigFppfOver.toScheme B S hS).map j)).hom) =
      (representedConormalDefiningIdealIso B S hS j).inv :=
  Stacks.CategoryTheory.transport_bridge_eq
    (modulePullback B S hS (representedSpaceMap B S hS j))
    (representedDefiningIdealPullbackConormalSheafIso_hom B S hS j)
    (representedConormalDefiningIdealIso_inv B S hS j)
    (Stacks.CategoryTheory.map_map_comp_inv_comp_map_map_hom
      (representedSmallEtaleModuleEquivalence B S hS R).functor
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj R) R.left.property)
      ((Scheme.Modules.pullback (B.inclusion.map j.left)).map
        (chartZariskiIdealSheafSelfChartIsoIdealSheaf B S hS V j hj).hom)
      (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
        ((BigFppfOver.toScheme B S hS).map j)))
    (representedAssociatedModulePullbackIso_naturality B S hS j
      (relativelyRepresentable_yoneda_map B S hS j)
      (chartZariskiIdealSheafSelfChartIsoIdealSheaf B S hS V j hj).hom).symm

/-- **Stacks 04G2 (1) itself, read against the ringed-space presentation of the conormal
sheaf.**  The registered comparison
`conormalModuleClosedSubspaceRangeIso`, followed by the associated module of
`Stacks.CartierConormal.conormalSheafIsoPullbackSelf`, is the comparison of `yoneda.obj R` with
the closed subspace followed by the inverse of
`AlgebraicGeometry.Space.representedConormalDefiningIdealIso`.

This is `AlgebraicGeometry.Space.representedDefiningIdealPullbackConormalSheafIso_hom_comp` with
the first, transparent factor of the registered comparison carried along. -/
theorem conormalModuleRepresentedIso_hom_comp :
    (conormalModuleClosedSubspaceRangeIso B S hS j).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS R).functor.map
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj R) R.left.property).map
            (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
              ((BigFppfOver.toScheme B S hS).map j)).hom) =
      (modulePullbackRepresentedSpaceMapIso B S hS j).hom ≫
        (representedConormalDefiningIdealIso B S hS j).inv :=
  (Category.assoc _ _ _).trans
    (congrArg (fun t => (modulePullbackRepresentedSpaceMapIso B S hS j).hom ≫ t)
      (representedDefiningIdealPullbackConormalSheafIso_hom_comp B S hS j))

/-- Ψ at the kernel-ideal-power spelling, which is the spelling the canonical map of a square
uses. -/
noncomputable def representedConormalKernelIdealZPowIso :
    (representedSmallEtaleModuleEquivalence B S hS R).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj R) R.left.property).obj
          (Stacks.ClosedImmersion.conormalSheaf
            ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)) ≅
      (modulePullback B S hS (representedSpaceMap B S hS j)).obj
        (kernelIdealSheafZPow B S hS (representedSpaceMap B S hS j) 1).toSheafOfModules :=
  (representedAssociatedModulePullbackIso B S hS j
      (relativelyRepresentable_yoneda_map B S hS j)
      (Stacks.ClosedImmersion.idealSheaf
        ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).symm ≪≫
    (modulePullback B S hS (representedSpaceMap B S hS j)).mapIso
      (representedAssociatedModuleKernelIdealZPowIso B S hS j hj)

/-- The two factors of `AlgebraicGeometry.Space.representedConormalKernelIdealZPowIso`. -/
theorem representedConormalKernelIdealZPowIso_hom :
    (representedConormalKernelIdealZPowIso B S hS j).hom =
      (representedAssociatedModulePullbackIso B S hS j
          (relativelyRepresentable_yoneda_map B S hS j)
          (Stacks.ClosedImmersion.idealSheaf
            ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).inv ≫
        (modulePullback B S hS (representedSpaceMap B S hS j)).map
          (representedAssociatedModuleKernelIdealZPowIso B S hS j hj).hom :=
  rfl

omit hj in
/-- The schemes-side conormal map of a square is the ringed-space square comparison followed by
the pullback of the map of ideal sheaves. -/
theorem conormalSheafMap_eq {R' V' : BigFppfOver B S hS} (j' : R' ⟶ V') (b : R ⟶ R') (a : V ⟶ V')
    (comm : ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom ≫
          ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom =
        ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom ≫
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) :
    Stacks.ClosedImmersion.conormalSheafMap comm =
      (Stacks.ClosedImmersion.pullbackCompIso comm
          (Stacks.ClosedImmersion.idealSheaf
            ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).hom ≫
        (RingedSpaceModuleAdjunction.modulePullback
            ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom).map
          (Stacks.ClosedImmersion.idealSheafMap comm) :=
  rfl

/-- The two spellings of the part-(1) comparison differ by the equality of sheaves of ideals
`AlgebraicGeometry.Space.kernelIdealSheafZPow_one_representedSpaceMap`. -/
theorem representedConormalKernelIdealZPowIso_hom_eq :
    (representedConormalKernelIdealZPowIso B S hS j).hom =
      (representedConormalDefiningIdealIso B S hS j).hom ≫
        (modulePullback B S hS (representedSpaceMap B S hS j)).map
          (eqToHom (congrArg
            (fun N : (SheafOfModules.unit (structureRingSheaf B S hS
                ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)).Submodule => N.toSheafOfModules)
            (kernelIdealSheafZPow_one_representedSpaceMap B S hS j hj).symm)) :=
  Stacks.CategoryTheory.comp_map_eq_comp_map_comp_map
    (modulePullback B S hS (representedSpaceMap B S hS j)) _ _ rfl _

section Square

variable {R' V' : BigFppfOver B S hS} (j' : R' ⟶ V') (b : R ⟶ R') (a : V ⟶ V')
    [hj' : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j')]

/-- **The naturality of the comparison of [Stacks Project, Tag 04G2] (1) in the closed
immersion.**

For a commutative square of the big fppf category over `S` whose horizontal morphisms are closed
immersions of schemes, the comparison of part (1) carries the spaces-side canonical map of
conormal modules of [Stacks Project, Tag 04CP] — the square comparison
`AlgebraicGeometry.Space.squarePullbackCompIso` followed by the inverse image along `j` of
`AlgebraicGeometry.Space.kernelIdealSquareMap`, which is
`AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap` in degree one — to the associated module
of `Stacks.ClosedImmersion.conormalSheafMap`, the map of Morphisms, Lemma
[Stacks Project, Tag 01R4].

The hypothesis `hΞ` is the agreement of the two **square comparisons** under the transport of the
inverse image, read at `Stacks.ClosedImmersion.idealSheaf` of `j'`.  It is a single equation
between existing morphisms, and it is part (2) of [Stacks Project, Tag 04G2]'s one remaining
obligation; see the section "What the naturality assumes, and what that assumption is" of
the module documentation. -/
theorem conormalSheafMap_representedConormalKernelIdealZPowIso (hsq : j ≫ a = b ≫ j')
    (hΞ : (modulePullback B S hS (representedSpaceMap B S hS b)).map
            (representedAssociatedModulePullbackIso B S hS j'
              (relativelyRepresentable_yoneda_map B S hS j')
              (Stacks.ClosedImmersion.idealSheaf
                ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).inv ≫
          (squarePullbackCompIso B S hS (representedSpaceMap B S hS j)
              (representedSpaceMap B S hS j') (representedSpaceMap B S hS b)
              (representedSpaceMap B S hS a)
              (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq)).hom.app
            ((representedSmallEtaleModuleEquivalence B S hS V').functor.obj
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj V') V'.left.property).obj
                (Stacks.ClosedImmersion.idealSheaf
                  ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))) =
        (representedAssociatedModulePullbackIso B S hS b
              (relativelyRepresentable_yoneda_map B S hS b)
              (Stacks.ClosedImmersion.conormalSheaf
                ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).hom ≫
          (representedSmallEtaleModuleEquivalence B S hS R).functor.map
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj R) R.left.property).map
                (Stacks.ClosedImmersion.pullbackCompIso
                    (i := ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)
                    (j := ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)
                    (f := ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom)
                    (k := ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom)
                    (toShHom_square_of_comp_eq B S hS j j' b a hsq)
                    (Stacks.ClosedImmersion.idealSheaf
                      ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).hom) ≫
            (representedAssociatedModulePullbackIso B S hS j
                (relativelyRepresentable_yoneda_map B S hS j)
                ((Scheme.Modules.pullback (B.inclusion.map a.left)).obj
                  (Stacks.ClosedImmersion.idealSheaf
                    ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))).inv ≫
              (modulePullback B S hS (representedSpaceMap B S hS j)).map
                (representedAssociatedModulePullbackIso B S hS a
                  (relativelyRepresentable_yoneda_map B S hS a)
                  (Stacks.ClosedImmersion.idealSheaf
                    ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).inv) :
    (modulePullback B S hS (representedSpaceMap B S hS b)).map
          (representedConormalKernelIdealZPowIso B S hS j').hom ≫
        (squarePullbackCompIso B S hS (representedSpaceMap B S hS j)
            (representedSpaceMap B S hS j') (representedSpaceMap B S hS b)
            (representedSpaceMap B S hS a)
            (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq)).hom.app
          (kernelIdealSheafZPow B S hS (representedSpaceMap B S hS j') 1).toSheafOfModules ≫
          (modulePullback B S hS (representedSpaceMap B S hS j)).map
            (kernelIdealSquareMap B S hS (representedSpaceMap B S hS j)
              (representedSpaceMap B S hS j') (representedSpaceMap B S hS b)
              (representedSpaceMap B S hS a)
              (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq) 1) =
      (representedAssociatedModulePullbackIso B S hS b
            (relativelyRepresentable_yoneda_map B S hS b)
            (Stacks.ClosedImmersion.conormalSheaf
              ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS R).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj R) R.left.property).map
              (Stacks.ClosedImmersion.conormalSheafMap
                (i := ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)
                (j := ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)
                (f := ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom)
                (k := ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom)
                (toShHom_square_of_comp_eq B S hS j j' b a hsq))) ≫
          (representedConormalKernelIdealZPowIso B S hS j).hom :=
  Stacks.CategoryTheory.square_conormal_eq
    (Stacks.CategoryTheory.map_eq_map_comp_map
      (modulePullback B S hS (representedSpaceMap B S hS b)) _ _
      (representedConormalKernelIdealZPowIso_hom B S hS j'))
    (squarePullbackCompIso_hom_app_naturality_comp B S hS (representedSpaceMap B S hS j)
      (representedSpaceMap B S hS j') (representedSpaceMap B S hS b)
      (representedSpaceMap B S hS a)
      (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq)
      (representedAssociatedModuleKernelIdealZPowIso B S hS j' hj').hom
      ((modulePullback B S hS (representedSpaceMap B S hS j)).map
        (kernelIdealSquareMap B S hS (representedSpaceMap B S hS j)
          (representedSpaceMap B S hS j') (representedSpaceMap B S hS b)
          (representedSpaceMap B S hS a)
          (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq) 1)))
    hΞ
    (Stacks.CategoryTheory.map_comp₃_eq_map_comp₂_of
      (modulePullback B S hS (representedSpaceMap B S hS j)) _ _ _ _ _
      (kernelIdealSquareMap_representedAssociatedModuleKernelIdealZPowIso B S hS j j' b a hj hj'
        (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq)
        (toShHom_square_of_comp_eq B S hS j j' b a hsq)))
    (Stacks.CategoryTheory.map_inv_comp_map_hom
      (modulePullback B S hS (representedSpaceMap B S hS j))
      (representedAssociatedModulePullbackIso B S hS a
        (relativelyRepresentable_yoneda_map B S hS a)
        (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)))
    (Stacks.CategoryTheory.inv_comp_eq_comp_inv_of _ _ _ _
      (representedAssociatedModulePullbackIso_naturality B S hS j
        (relativelyRepresentable_yoneda_map B S hS j)
        (Stacks.ClosedImmersion.idealSheafMap
          (i := ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)
          (j := ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)
          (f := ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom)
          (k := ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom)
          (toShHom_square_of_comp_eq B S hS j j' b a hsq))))
    (representedConormalKernelIdealZPowIso_hom B S hS j)
    (Stacks.CategoryTheory.map_map_comp_eq_of
      (representedSmallEtaleModuleEquivalence B S hS R).functor
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj R) R.left.property) _ _
      (conormalSheafMap_eq B S hS j j' b a (toShHom_square_of_comp_eq B S hS j j' b a hsq)))

end Square

end AlgebraicGeometry.Space

end
