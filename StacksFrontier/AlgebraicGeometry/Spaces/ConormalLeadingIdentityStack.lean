module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSchemesRectangleIdentity

/-!
# Part (2) of Stacks 04G2 at immersion generality: the leading-identity junction, and the clause

Part (2) of [Stacks Project, Tag 04G2] says that when every space of [Stacks Project, Tag 04CP]
is a scheme, the canonical map of conormal modules of that tag is the canonical map of Morphisms,
Lemma [Stacks Project, Tag 01R4].  Tag 04CP states its hypothesis for **immersions**, so that is
the generality of the clause.

`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleRepresentedImmersionNaturality.lean` reduces
the clause to one naturality statement, its `hnat`; the reduction of that statement to the closed
case stacks four squares, and
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleImmersionNaturalityAssembly.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSchemesRectangleIdentity.lean` land the forward step,
the two stacks and the schemes-side rectangle identity.  This file is the **backward** step and the
clause.

## Main results

* `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_id_left`: the transport's
  composition law at a **leading** identity — the companion the trailing-identity law
  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_id_right` was recorded as
  not having.
* `AlgebraicGeometry.Space.conormalCoborderRectangle_square_rsm_id` and
  `.conormalCoborderOuterRectangle_square_rsm_id`: the backward step's upper square and outer
  rectangle, each at the left-edge spelling the other hypotheses fix.
* `AlgebraicGeometry.Space.ha_zariski`: the schemes-side rectangle identity in the spelling the
  stack consumes.
* `AlgebraicGeometry.Space.conormalMapOfImmersions_naturality_of_immersions`: **the backward
  step** — `hnat`, discharged.
* `AlgebraicGeometry.Space.conormalModuleOfImmersionRepresentedIso_naturality`: **part (2) of
  [Stacks Project, Tag 04G2] at immersion generality**, which carries the tag.

## The leading-identity junction

The backward step's functor is the inverse image along the upper square's left edge, which is
`AlgebraicGeometry.Space.representedSpaceMap (𝟙 R) ≫ 𝟙` — `representedSpaceMap` of *nothing*, so
the edge cannot be held at a variable and substituted away.  Its hypothesis `hTcomp` is the
transport's composition law there.  Specialising the junction bridge
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_app_eq_of_eq_left` at
`representedSpaceMap (𝟙 T₁)` is a kernel deterministic timeout, but it does not follow that every
junction at a leading identity is.

**The distinction is between two functors, not between a variable and the identity:**

* the junction under `AlgebraicGeometry.Space.modulePullback`, at the level of **morphisms** —
  `(modulePullback (representedSpaceMap (𝟙 R) ≫ 𝟙)).map x` against
  `(modulePullback (representedSpaceMap (𝟙 R))).map x` — is `rfl` and free, at a variable site
  morphism and at the identity alike;
* the same junction on the **outer** argument of
  `AlgebraicGeometry.Space.modulePullbackCompIso` is a kernel deterministic timeout;
* `AlgebraicGeometry.Space.representedSpaceMap_id` is `rfl`, as the module documentation of
  `ConormalSchemesRectangleIdentity.lean` says.

So the stack is assembled with the comparison of [Stacks Project, Tag 03LU] read at
`representedSpaceMap (𝟙 R)` on **every** side — `hc`, `hc2`, `hk` and `hTcomp` all take it there,
and no spelling of it is ever identified with another — while the functor stays at
`representedSpaceMap (𝟙 R) ≫ 𝟙`, where the squares are stated.  The one crossing left is the
free one.

## Implementation notes

Three things here are forced by elaboration cost and none is stylistic.

* **Every left-edge move is lifted into its own declaration.**
  `AlgebraicGeometry.Space.k1move`, `.k1move2`, `.k2move` and `.mpmove` are each two lines, and
  each is a kernel deterministic timeout when left inline as a `have` in the declaration that
  consumes it: a `have` is re-checked inside the enclosing declaration, where the canonical maps
  it stands between are expanded.
* **`AlgebraicGeometry.Space.ha_zariski` needs its map of [Stacks Project, Tag 01R4] written with
  `Stacks.ClosedImmersion.conormalSheafMap`'s four implicit morphisms named and with a type
  ascription** to the `AlgebraicGeometry.Scheme.Modules` spelling of its source.  Without either,
  feeding it to `AlgebraicGeometry.Scheme.Modules.pullback` leaves the elaborator to identify a
  ringed-space sheaf of modules with a scheme's, and that is a `whnf` timeout **in the
  statement**, before any proof runs.  With them, the hand-off from
  `AlgebraicGeometry.Space.conormalSheafMap_coborderRectangle_eq` is a bare `exact`.
* **`rw` cannot make that crossing.**  Named `rfl` bridges between
  `AlgebraicGeometry.Scheme.Modules.pullbackComp` and
  `RingedSpaceModuleAdjunction.modulePullbackComp` rewrite into a motive that is not type-correct
  at the `implicit` transparency level, which is the failure
  `ConormalModuleRepresentedImmersionNaturality.lean` records for the ringed-space pasting law.
  The ascription above removes the need for them.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section LeadingIdentity

attribute [local irreducible] modulePullback modulePullbackCompIso modulePullbackIdIso
  representedModuleObjPullbackIso representedAssociatedModulePullbackIso
  representedSmallEtaleModuleEquivalence

/-- **The composition law for the transport of the inverse image at a leading identity**, with
the transport of its right-hand side's tail at the reduced spelling. -/
theorem representedAssociatedModulePullbackIso_comp_id_left
    {T₁ T₂ : BigFppfOver B S hS} (q : T₁ ⟶ T₂)
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T₂).Modules) :
    (modulePullback B S hS (representedSpaceMap B S hS (𝟙 T₁))).map
          (representedAssociatedModulePullbackIso B S hS q
            (relativelyRepresentable_yoneda_map B S hS q) 𝓕).hom ≫
        (representedAssociatedModulePullbackIso B S hS (𝟙 T₁)
            (relativelyRepresentable_yoneda_map B S hS (𝟙 T₁))
            ((Scheme.Modules.pullback (B.inclusion.map q.left)).obj 𝓕)).hom ≫
          (representedSmallEtaleModuleEquivalence B S hS T₁).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T₁) T₁.left.property).map
              ((Scheme.Modules.pullbackComp (B.inclusion.map (Over.Hom.left (𝟙 T₁)))
                  (B.inclusion.map q.left)).hom.app 𝓕)) =
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS (𝟙 T₁))
            (representedSpaceMap B S hS q)).hom.app
          ((representedSmallEtaleModuleEquivalence B S hS T₂).functor.obj
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T₂) T₂.left.property).obj 𝓕)) ≫
        (representedAssociatedModulePullbackIso B S hS q
          (relativelyRepresentable_yoneda_map B S hS q) 𝓕).hom :=
  (representedAssociatedModulePullbackIso_comp_of_eq B S hS (𝟙 T₁) q
      (relativelyRepresentable_yoneda_map B S hS (𝟙 T₁))
      (relativelyRepresentable_yoneda_map B S hS q)
      (relativelyRepresentable_yoneda_map B S hS (𝟙 T₁ ≫ q)) 𝓕 _ rfl).trans
    (CategoryTheory.whisker_eq _
      (representedAssociatedModulePullbackIso_hom_id_comp B S hS q 𝓕))

end LeadingIdentity

section Backward

attribute [local irreducible] modulePullback modulePullbackCompIso modulePullbackIdIso
  representedModuleObjPullbackIso representedAssociatedModulePullbackIso
  squarePullbackCompIso representedSmallEtaleModuleEquivalence

variable {R V R' V' : BigFppfOver B S hS} (j : R ⟶ V) (j' : R' ⟶ V') (b : R ⟶ R')
    (a : V ⟶ V')
    [hj : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)]
    [hj' : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j')]

/-- **The rectangle `S₁` over `S₃` at the represented spaces, with its left-hand vertical spelled
as a single `AlgebraicGeometry.Space.representedSpaceMap` of the site's identity.** -/
theorem coborderRectangle_comm_rsm_id (hsq : j ≫ a = b ≫ j') :
    representedSpaceMap B S hS (coborderSquareLift B S hS j j' b a hsq) ≫
        representedSpaceMap B S hS (coborderSquareHom B S hS j j' b a hsq) ≫
          representedSpaceMap B S hS
            (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange) =
      representedSpaceMap B S hS (𝟙 R) ≫ representedSpaceMap B S hS j :=
  (coborderSquare_comp_comm B S hS j j' b a hsq).trans (by
    rw [representedSpaceMap_id, Category.id_comp])

/-- **The outer rectangle's commutativity at the left-hand vertical `representedSpaceMap (𝟙 R) ≫
representedSpaceMap b`**, which is the spelling
`AlgebraicGeometry.Space.kernelIdealZPowSquareMap_comp` produces for a stack whose upper square is
the rectangle above. -/
theorem coborderOuterRectangle_comm_rsm_id (hsq : j ≫ a = b ≫ j') :
    representedSpaceMap B S hS (coborderSquareLift B S hS j j' b a hsq) ≫
        (representedSpaceMap B S hS (coborderSquareHom B S hS j j' b a hsq) ≫
            representedSpaceMap B S hS
              (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange)) ≫
          representedSpaceMap B S hS a =
      (representedSpaceMap B S hS (𝟙 R) ≫ representedSpaceMap B S hS b) ≫
        representedSpaceMap B S hS j' := by
  rw [← Category.assoc, coborderRectangle_comm_rsm_id B S hS j j' b a hsq, Category.assoc,
    representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq, ← Category.assoc]

/-- K: the `k₁` left-edge move alone. -/
theorem k1move (hsq : j ≫ a = b ≫ j') :
    kernelIdealZPowSquareMap B S hS
        (representedSpaceMap B S hS (coborderSquareLift B S hS j j' b a hsq))
        (representedSpaceMap B S hS j) (representedSpaceMap B S hS (𝟙 R))
        (representedSpaceMap B S hS (coborderSquareHom B S hS j j' b a hsq) ≫
          representedSpaceMap B S hS
            (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))
        (coborderRectangle_comm_rsm_id B S hS j j' b a hsq) 1 =
      kernelIdealZPowSquareMap B S hS
        (representedSpaceMap B S hS (coborderSquareLift B S hS j j' b a hsq))
        (representedSpaceMap B S hS j)
        (representedSpaceMap B S hS (𝟙 R) ≫
          𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS))
        (representedSpaceMap B S hS (coborderSquareHom B S hS j j' b a hsq) ≫
          representedSpaceMap B S hS
            (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))
        (coborderSquare_comp_comm_representedSpaceMap_id B S hS j j' b a hsq) 1 :=
  (kernelIdealZPowSquareMap_eq_of_eq_left B S hS _ _
        (show representedSpaceMap B S hS (𝟙 R) =
            representedSpaceMap B S hS (𝟙 R) ≫
              𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ :
                AlgebraicSpaces B S hS) from (Category.comp_id _).symm)
        _ _ _ 1 rfl).trans (eqToHom_comp_of_refl _ _)

/-- **The transported naturality square of the rectangle `S₁` over `S₃`, with the canonical map
of [Stacks Project, Tag 04CP] read at the left-hand vertical
`AlgebraicGeometry.Space.representedSpaceMap (𝟙 R)`.** -/
theorem conormalCoborderRectangle_square_rsm_id (hsq : j ≫ a = b ≫ j') :
    (modulePullback B S hS (representedSpaceMap B S hS (𝟙 R) ≫
            𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS))).map
          (representedConormalOfImmersionKernelIdealZPowIso B S hS j).hom ≫
        kernelIdealZPowSquareMap B S hS
          (representedSpaceMap B S hS (coborderSquareLift B S hS j j' b a hsq))
          (representedSpaceMap B S hS j)
          (representedSpaceMap B S hS (𝟙 R))
          (representedSpaceMap B S hS (coborderSquareHom B S hS j j' b a hsq) ≫
            representedSpaceMap B S hS
              (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))
          (coborderRectangle_comm_rsm_id B S hS j j' b a hsq) 1 =
      (representedAssociatedModulePullbackIso B S hS (𝟙 R)
            (relativelyRepresentable_yoneda_map B S hS (𝟙 R))
            (Stacks.ClosedImmersion.conormalSheaf
              ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS R).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj R) R.left.property).map
              ((Scheme.Modules.pullbackComp (B.inclusion.map (Over.Hom.left (𝟙 R)))
                    (B.inclusion.map (Over.Hom.left (𝟙 R)))).inv.app
                  (Stacks.ClosedImmersion.conormalSheaf
                    ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom) ≫
                (Scheme.Modules.pullback (B.inclusion.map (Over.Hom.left (𝟙 R)))).map
                    (((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj R)).hom.app
                          (Stacks.ClosedImmersion.conormalSheaf
                            ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom) ≫
                        (Stacks.Immersion.conormalSheafSelfIso
                          ((BigFppfOver.toScheme B S hS).map j)).hom :
                      (Scheme.Modules.pullback
                            (B.inclusion.map (Over.Hom.left (𝟙 R)))).obj
                          (Stacks.ClosedImmersion.conormalSheaf
                            ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom) ⟶
                        Stacks.ClosedImmersion.conormalSheaf
                          ((BigFppfOver.toScheme B S hS).map
                            (immersionCoborderLift B S hS j)).toLRSHom.toShHom)) ≫
                  Stacks.ClosedImmersion.conormalSheafMap
                    (toShHom_square_of_comp_eq B S hS
                      (coborderSquareLift B S hS j j' b a hsq)
                      (immersionCoborderLift B S hS j) (𝟙 R)
                      (coborderSquareHom B S hS j j' b a hsq)
                      (coborderSquareLift_comp_coborderSquareHom_id B S hS j j' b a hsq)))) ≫
          (representedConormalKernelIdealZPowIso B S hS
            (coborderSquareLift B S hS j j' b a hsq)).hom :=
  (CategoryTheory.whisker_eq _ (k1move B S hS j j' b a hsq)).trans
    (conormalCoborderRectangle_square B S hS j j' b a hsq)

/-- The same move, to the `𝟙 ≫ 𝟙` spelling the cancellation is stated at. -/
theorem k1move2 (hsq : j ≫ a = b ≫ j') :
    kernelIdealZPowSquareMap B S hS
        (representedSpaceMap B S hS (coborderSquareLift B S hS j j' b a hsq))
        (representedSpaceMap B S hS j) (representedSpaceMap B S hS (𝟙 R))
        (representedSpaceMap B S hS (coborderSquareHom B S hS j j' b a hsq) ≫
          representedSpaceMap B S hS
            (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))
        (coborderRectangle_comm_rsm_id B S hS j j' b a hsq) 1 =
      kernelIdealZPowSquareMap B S hS
        (representedSpaceMap B S hS (coborderSquareLift B S hS j j' b a hsq))
        (representedSpaceMap B S hS j)
        (𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS) ≫
          𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS))
        (representedSpaceMap B S hS (coborderSquareHom B S hS j j' b a hsq) ≫
          representedSpaceMap B S hS
            (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))
        (coborderSquare_comp_comm B S hS j j' b a hsq) 1 :=
  (kernelIdealZPowSquareMap_eq_of_eq_left B S hS _ _
        (show representedSpaceMap B S hS (𝟙 R) =
            𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS) ≫
              𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ :
                AlgebraicSpaces B S hS) by rw [representedSpaceMap_id, Category.id_comp])
        _ _ _ 1 rfl).trans (eqToHom_comp_of_refl _ _)

/-- **The canonical map of the rectangle `S₁` over `S₃` is an isomorphism, at the left-hand
vertical `AlgebraicGeometry.Space.representedSpaceMap (𝟙 R)`.** -/
theorem isIso_kernelIdealZPowSquareMap_coborderRectangle_rsm_id (hsq : j ≫ a = b ≫ j') :
    IsIso (kernelIdealZPowSquareMap B S hS
      (representedSpaceMap B S hS (coborderSquareLift B S hS j j' b a hsq))
      (representedSpaceMap B S hS j) (representedSpaceMap B S hS (𝟙 R))
      (representedSpaceMap B S hS (coborderSquareHom B S hS j j' b a hsq) ≫
        representedSpaceMap B S hS
          (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))
      (coborderRectangle_comm_rsm_id B S hS j j' b a hsq) 1) := by
  rw [k1move2 B S hS j j' b a hsq]
  exact isIso_kernelIdealZPowSquareMap_coborderSquare_comp B S hS j j' b a hsq

/-! ### The outer rectangle at the spelling the composition law produces -/

/-- The outer rectangle's left-hand vertical, from the spelling the forward step produces to the
spelling `AlgebraicGeometry.Space.kernelIdealZPowSquareMap_comp` produces. -/
theorem coborderOuterRectangle_left_rsm_id :
    representedSpaceMap B S hS (𝟙 R) ≫ representedSpaceMap B S hS b =
      representedSpaceMap B S hS b ≫
        𝟙 (⟨yoneda.obj R', isAlgebraicSpace_yoneda B S hS R'⟩ : AlgebraicSpaces B S hS) := by
  rw [representedSpaceMap_id, Category.id_comp, Category.comp_id]

/-- The outer rectangle's right-hand vertical, read the two ways
`AlgebraicGeometry.Space.coborderSquareMap_comp_openSubHom` identifies. -/
theorem coborderOuterRectangle_right_rsm_id (hsq : j ≫ a = b ≫ j') :
    (representedSpaceMap B S hS (coborderSquareHom B S hS j j' b a hsq) ≫
          representedSpaceMap B S hS
            (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange)) ≫
        representedSpaceMap B S hS a =
      representedSpaceMap B S hS (coborderSquareMap B S hS j j' b a hsq) ≫
        representedSpaceMap B S hS
          (openSubHom V' ((BigFppfOver.toScheme B S hS).map j').coborderRange) := by
  rw [representedSpaceMap_comp B S hS, representedSpaceMap_comp B S hS,
    representedSpaceMap_comp B S hS, coborderSquareMap_comp_openSubHom B S hS j j' b a hsq]

/-- The outer rectangle's commutativity at the left-hand vertical the forward step produces. -/
theorem coborderOuterRectangle_comm_mixed (hsq : j ≫ a = b ≫ j') :
    representedSpaceMap B S hS (coborderSquareLift B S hS j j' b a hsq) ≫
        (representedSpaceMap B S hS (coborderSquareHom B S hS j j' b a hsq) ≫
            representedSpaceMap B S hS
              (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange)) ≫
          representedSpaceMap B S hS a =
      (representedSpaceMap B S hS b ≫
          𝟙 (⟨yoneda.obj R', isAlgebraicSpace_yoneda B S hS R'⟩ : AlgebraicSpaces B S hS)) ≫
        representedSpaceMap B S hS j' :=
  (coborderOuterRectangle_comm_rsm_id B S hS j j' b a hsq).trans
    (CategoryTheory.eq_whisker (coborderOuterRectangle_left_rsm_id B S hS b) _)

/-- The inverse image of the part-(1) comparison at the two spellings of the outer rectangle's
left-hand vertical.  `rfl`: composition in `AlgebraicGeometry.Space.AlgebraicSpaces` is unital and
`AlgebraicGeometry.Space.representedSpaceMap_id` holds by `rfl`. -/
theorem mpmove :
    (modulePullback B S hS (representedSpaceMap B S hS (𝟙 R) ≫
          representedSpaceMap B S hS b)).map
        (representedConormalOfImmersionKernelIdealZPowIso B S hS j').hom =
      (modulePullback B S hS (representedSpaceMap B S hS b ≫
          𝟙 (⟨yoneda.obj R', isAlgebraicSpace_yoneda B S hS R'⟩ :
            AlgebraicSpaces B S hS))).map
        (representedConormalOfImmersionKernelIdealZPowIso B S hS j').hom :=
  rfl

/-- The outer rectangle's canonical map, from the spelling
`AlgebraicGeometry.Space.kernelIdealZPowSquareMap_comp` produces to the spelling the forward step
produces. -/
theorem k2move (hsq : j ≫ a = b ≫ j') :
    kernelIdealZPowSquareMap B S hS
        (representedSpaceMap B S hS (coborderSquareLift B S hS j j' b a hsq))
        (representedSpaceMap B S hS j')
        (representedSpaceMap B S hS (𝟙 R) ≫ representedSpaceMap B S hS b)
        ((representedSpaceMap B S hS (coborderSquareHom B S hS j j' b a hsq) ≫
            representedSpaceMap B S hS
              (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange)) ≫
          representedSpaceMap B S hS a)
        (coborderOuterRectangle_comm_rsm_id B S hS j j' b a hsq) 1 =
      kernelIdealZPowSquareMap B S hS
        (representedSpaceMap B S hS (coborderSquareLift B S hS j j' b a hsq))
        (representedSpaceMap B S hS j')
        (representedSpaceMap B S hS b ≫
          𝟙 (⟨yoneda.obj R', isAlgebraicSpace_yoneda B S hS R'⟩ : AlgebraicSpaces B S hS))
        (representedSpaceMap B S hS (coborderSquareMap B S hS j j' b a hsq) ≫
          representedSpaceMap B S hS
            (openSubHom V' ((BigFppfOver.toScheme B S hS).map j').coborderRange))
        (coborderSquareMap_comp_comm_representedSpaceMap_id B S hS j j' b a hsq) 1 :=
  (kernelIdealZPowSquareMap_eq_of_eq_left B S hS _ _
        (coborderOuterRectangle_left_rsm_id B S hS b) _ _ _ 1 (by rfl)).trans
    ((eqToHom_comp_of_refl _ _).trans
      (kernelIdealZPowSquareMap_congr_right B S hS _ _ _
        (coborderOuterRectangle_right_rsm_id B S hS j j' b a hsq)
        (coborderOuterRectangle_comm_mixed B S hS j j' b a hsq) _ 1))

/-- **The transported naturality square of the rectangle `S₂` over `S₄`, at the left-hand vertical
`AlgebraicGeometry.Space.representedSpaceMap (𝟙 R) ≫ representedSpaceMap b` and the right-hand
vertical read through the ambient of the lifted square.**  This is the outer rectangle of the
backward step, in the spelling in which its canonical map is literally the one
`AlgebraicGeometry.Space.kernelIdealZPowSquareMap_comp` produces from the rectangle `S₁` over `S₃`
and the square part (2) is about. -/
theorem conormalCoborderOuterRectangle_square_rsm_id (hsq : j ≫ a = b ≫ j') :
    (modulePullback B S hS (representedSpaceMap B S hS (𝟙 R) ≫
            representedSpaceMap B S hS b)).map
          (representedConormalOfImmersionKernelIdealZPowIso B S hS j').hom ≫
        kernelIdealZPowSquareMap B S hS
          (representedSpaceMap B S hS (coborderSquareLift B S hS j j' b a hsq))
          (representedSpaceMap B S hS j')
          (representedSpaceMap B S hS (𝟙 R) ≫ representedSpaceMap B S hS b)
          ((representedSpaceMap B S hS (coborderSquareHom B S hS j j' b a hsq) ≫
              representedSpaceMap B S hS
                (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange)) ≫
            representedSpaceMap B S hS a)
          (coborderOuterRectangle_comm_rsm_id B S hS j j' b a hsq) 1 =
      (representedAssociatedModulePullbackIso B S hS b
            (relativelyRepresentable_yoneda_map B S hS b)
            (Stacks.ClosedImmersion.conormalSheaf
              ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS R).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj R) R.left.property).map
              ((Scheme.Modules.pullbackComp (B.inclusion.map b.left)
                    (B.inclusion.map (Over.Hom.left (𝟙 R')))).inv.app
                  (Stacks.ClosedImmersion.conormalSheaf
                    ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) ≫
                (Scheme.Modules.pullback (B.inclusion.map b.left)).map
                    (((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj R')).hom.app
                          (Stacks.ClosedImmersion.conormalSheaf
                            ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) ≫
                        (Stacks.Immersion.conormalSheafSelfIso
                          ((BigFppfOver.toScheme B S hS).map j')).hom :
                      (Scheme.Modules.pullback
                            (B.inclusion.map (Over.Hom.left (𝟙 R')))).obj
                          (Stacks.ClosedImmersion.conormalSheaf
                            ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) ⟶
                        Stacks.ClosedImmersion.conormalSheaf
                          ((BigFppfOver.toScheme B S hS).map
                            (immersionCoborderLift B S hS j')).toLRSHom.toShHom)) ≫
                  Stacks.ClosedImmersion.conormalSheafMap
                    (i := ((BigFppfOver.toScheme B S hS).map
                      (coborderSquareLift B S hS j j' b a hsq)).toLRSHom.toShHom)
                    (j := ((BigFppfOver.toScheme B S hS).map
                      (immersionCoborderLift B S hS j')).toLRSHom.toShHom)
                    (f := ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom)
                    (k := ((BigFppfOver.toScheme B S hS).map
                      (coborderSquareMap B S hS j j' b a hsq)).toLRSHom.toShHom)
                    (toShHom_square_of_comp_eq B S hS
                      (coborderSquareLift B S hS j j' b a hsq)
                      (immersionCoborderLift B S hS j') b
                      (coborderSquareMap B S hS j j' b a hsq)
                      (coborderSquareLift_comp_coborderSquareMap B S hS j j' b a hsq)))) ≫
          (representedConormalKernelIdealZPowIso B S hS
            (coborderSquareLift B S hS j j' b a hsq)).hom :=
  ((CategoryTheory.eq_whisker (mpmove B S hS j' b) _).trans
      (CategoryTheory.whisker_eq _ (k2move B S hS j j' b a hsq))).trans
    (conormalCoborderOuterRectangle_square B S hS j j' b a hsq)

/-! ### Faithfulness of the inverse image along the stack's upper left edge -/

/-- **The inverse image along `representedSpaceMap (𝟙 R) ≫ 𝟙` is faithful.**  It is the inverse
image along an identity, `AlgebraicGeometry.Space.representedSpaceMap_id` holding by `rfl`, and
that is an equivalence by `AlgebraicGeometry.Space.isEquivalence_modulePullback_id`. -/
theorem modulePullback_rsm_id_map_injective {X Y : Modules.{u, u} B S hS
      (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS).1
      (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS).2}
    (x y : X ⟶ Y)
    (h : (modulePullback B S hS (representedSpaceMap B S hS (𝟙 R) ≫
          𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ :
            AlgebraicSpaces B S hS))).map x =
      (modulePullback B S hS (representedSpaceMap B S hS (𝟙 R) ≫
          𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ :
            AlgebraicSpaces B S hS))).map y) : x = y := by
  have : (modulePullback B S hS
      (𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ :
        AlgebraicSpaces B S hS))).Faithful :=
    Functor.Faithful.of_iso
      (modulePullbackIdIso B S hS
        (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS)).symm
  exact Functor.map_injective
    (modulePullback B S hS (𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ :
      AlgebraicSpaces B S hS))) h

/-- **The schemes-side rectangle identity of part (2), in the spelling the stack's `ha`
consumes.**

`AlgebraicGeometry.Space.conormalSheafMap_coborderRectangle_eq` states it with
`RingedSpaceModuleAdjunction.modulePullbackComp` and the two change-of-ambient canonical maps
unexpanded.  Both differences are discharged here: the canonical maps by
`AlgebraicGeometry.Space.conormalSheafMap_immersionCoborder_eq` at `j'` and at `j`, and the
comparison by `AlgebraicGeometry.Space.pullbackComp_inv_app_eq` and
`AlgebraicGeometry.Space.pullback_map_eq`.

**Two things in this statement are load-bearing.**  The map of
[Stacks Project, Tag 01R4] of the square `(j, j', b, a)` is written with
`Stacks.ClosedImmersion.conormalSheafMap`'s four implicit morphisms **named**, and it carries a
**type ascription** to the `AlgebraicGeometry.Scheme.Modules` spelling of its source.  Without
either, feeding it to `AlgebraicGeometry.Scheme.Modules.pullback` leaves the elaborator to
identify a ringed-space sheaf of modules with a scheme's, and that is a 200 000-heartbeat `whnf`
timeout in the statement — before any proof runs.

This is the hypothesis `ha` of `Stacks.CategoryTheory.square_transport_of_comp` for the backward
step, before the associated-module functors are applied to its three factors. -/
theorem ha_zariski (hsq : j ≫ a = b ≫ j') :
    (Scheme.Modules.pullbackComp (B.inclusion.map b.left)
                    (B.inclusion.map (Over.Hom.left (𝟙 R')))).inv.app
                  (Stacks.ClosedImmersion.conormalSheaf
                    ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) ≫
                (Scheme.Modules.pullback (B.inclusion.map b.left)).map
                    (((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj R')).hom.app
                          (Stacks.ClosedImmersion.conormalSheaf
                            ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) ≫
                        (Stacks.Immersion.conormalSheafSelfIso
                          ((BigFppfOver.toScheme B S hS).map j')).hom :
                      (Scheme.Modules.pullback
                            (B.inclusion.map (Over.Hom.left (𝟙 R')))).obj
                          (Stacks.ClosedImmersion.conormalSheaf
                            ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) ⟶
                        Stacks.ClosedImmersion.conormalSheaf
                          ((BigFppfOver.toScheme B S hS).map
                            (immersionCoborderLift B S hS j')).toLRSHom.toShHom)) ≫
                  Stacks.ClosedImmersion.conormalSheafMap
                    (i := ((BigFppfOver.toScheme B S hS).map
                      (coborderSquareLift B S hS j j' b a hsq)).toLRSHom.toShHom)
                    (j := ((BigFppfOver.toScheme B S hS).map
                      (immersionCoborderLift B S hS j')).toLRSHom.toShHom)
                    (f := ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom)
                    (k := ((BigFppfOver.toScheme B S hS).map
                      (coborderSquareMap B S hS j j' b a hsq)).toLRSHom.toShHom)
                    (toShHom_square_of_comp_eq B S hS
                      (coborderSquareLift B S hS j j' b a hsq)
                      (immersionCoborderLift B S hS j') b
                      (coborderSquareMap B S hS j j' b a hsq)
                      (coborderSquareLift_comp_coborderSquareMap B S hS j j' b a hsq)) =
      (Scheme.Modules.pullbackComp (B.inclusion.map (Over.Hom.left (𝟙 R)))
              (B.inclusion.map b.left)).inv.app
            (Stacks.ClosedImmersion.conormalSheaf
              ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) ≫
          (Scheme.Modules.pullback (B.inclusion.map (Over.Hom.left (𝟙 R)))).map
              (Stacks.ClosedImmersion.conormalSheafMap
                  (i := ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)
                  (j := ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)
                  (f := ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom)
                  (k := ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom)
                  (toShHom_square_of_comp_eq B S hS j j' b a hsq) :
                (Scheme.Modules.pullback (B.inclusion.map b.left)).obj
                    (Stacks.ClosedImmersion.conormalSheaf
                      ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) ⟶
                  Stacks.ClosedImmersion.conormalSheaf
                    ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom) ≫
            ((Scheme.Modules.pullbackComp (B.inclusion.map (Over.Hom.left (𝟙 R)))
                    (B.inclusion.map (Over.Hom.left (𝟙 R)))).inv.app
                  (Stacks.ClosedImmersion.conormalSheaf
                    ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom) ≫
                (Scheme.Modules.pullback (B.inclusion.map (Over.Hom.left (𝟙 R)))).map
                    (((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj R)).hom.app
                          (Stacks.ClosedImmersion.conormalSheaf
                            ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom) ≫
                        (Stacks.Immersion.conormalSheafSelfIso
                          ((BigFppfOver.toScheme B S hS).map j)).hom :
                      (Scheme.Modules.pullback
                            (B.inclusion.map (Over.Hom.left (𝟙 R)))).obj
                          (Stacks.ClosedImmersion.conormalSheaf
                            ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom) ⟶
                        Stacks.ClosedImmersion.conormalSheaf
                          ((BigFppfOver.toScheme B S hS).map
                            (immersionCoborderLift B S hS j)).toLRSHom.toShHom)) ≫
                  Stacks.ClosedImmersion.conormalSheafMap
                    (toShHom_square_of_comp_eq B S hS
                      (coborderSquareLift B S hS j j' b a hsq)
                      (immersionCoborderLift B S hS j) (𝟙 R)
                      (coborderSquareHom B S hS j j' b a hsq)
                      (coborderSquareLift_comp_coborderSquareHom_id B S hS j j' b a hsq))) := by
  have h := conormalSheafMap_coborderRectangle_eq B S hS j j' b a hsq
  rw [conormalSheafMap_immersionCoborder_eq B S hS j',
    conormalSheafMap_immersionCoborder_eq B S hS j] at h
  exact h

/-! ### The backward step, and part (2) -/

/-- **The naturality of the part-(1) comparison at immersion generality: the lower square of the
reduction.**

This is the hypothesis `hnat` of
`AlgebraicGeometry.Space.conormalMapOfImmersions_conormalModuleOfImmersionRepresentedIso`,
discharged.  One instantiation of `Stacks.CategoryTheory.square_transport_of_comp`, whose outer
rectangle is `AlgebraicGeometry.Space.conormalCoborderOuterRectangle_square_rsm_id`, whose upper
square is `AlgebraicGeometry.Space.conormalCoborderRectangle_square_rsm_id`, whose cancellations
are `AlgebraicGeometry.Space.isIso_kernelIdealZPowSquareMap_coborderRectangle_rsm_id` and the
comparison of [Stacks Project, Tag 03LU], whose faithfulness is
`AlgebraicGeometry.Space.modulePullback_rsm_id_map_injective`, and whose Zariski-side input is
`AlgebraicGeometry.Space.ha_zariski`.

The functor the step is taken along is the inverse image along the rectangle's left edge,
`AlgebraicGeometry.Space.representedSpaceMap (𝟙 R) ≫ 𝟙`, and its hypothesis `hTcomp` — the
transport's composition law at a **leading** identity — is
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_id_left`.  That law is stated
at `representedSpaceMap (𝟙 R)` and consumed here at `representedSpaceMap (𝟙 R) ≫ 𝟙`; the junction
between the two is under `AlgebraicGeometry.Space.modulePullback` and is **`rfl` and free**.  What is not affordable is the same junction on the *outer* argument of
`AlgebraicGeometry.Space.modulePullbackCompIso`, and this assembly never asks for it: the
comparison is read at `representedSpaceMap (𝟙 R)` on every side. -/
theorem conormalMapOfImmersions_naturality_of_immersions (hsq : j ≫ a = b ≫ j') :
 (modulePullback B S hS (representedSpaceMap B S hS b)).map
            (representedConormalOfImmersionKernelIdealZPowIso B S hS j').hom ≫
          kernelIdealZPowSquareMap B S hS (representedSpaceMap B S hS j)
            (representedSpaceMap B S hS j') (representedSpaceMap B S hS b)
            (representedSpaceMap B S hS a)
            (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq) 1 =
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
            (representedConormalOfImmersionKernelIdealZPowIso B S hS j).hom := by
  have := isIso_kernelIdealZPowSquareMap_coborderRectangle_rsm_id B S hS j j' b a hsq
  exact Stacks.CategoryTheory.square_transport_of_comp
    (F := modulePullback B S hS (representedSpaceMap B S hS (𝟙 R) ≫
      𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS)))
    (hc := Iso.inv_hom_id_app (modulePullbackCompIso B S hS
      (representedSpaceMap B S hS (𝟙 R)) (representedSpaceMap B S hS b)) _)
    (hgpc := Stacks.CategoryTheory.map_map_comp_eq_id_of
      (representedSmallEtaleModuleEquivalence B S hS R).functor
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj R) R.left.property) _ _
      (Iso.hom_inv_id_app (Scheme.Modules.pullbackComp (B.inclusion.map (Over.Hom.left (𝟙 R)))
        (B.inclusion.map b.left)) _))
    (hk := kernelIdealZPowSquareMap_comp B S hS
      (representedSpaceMap B S hS (coborderSquareLift B S hS j j' b a hsq))
      (representedSpaceMap B S hS j) (representedSpaceMap B S hS j')
      (representedSpaceMap B S hS (𝟙 R))
      (representedSpaceMap B S hS (coborderSquareHom B S hS j j' b a hsq) ≫
        representedSpaceMap B S hS
          (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))
      (representedSpaceMap B S hS b) (representedSpaceMap B S hS a)
      (coborderRectangle_comm_rsm_id B S hS j j' b a hsq)
      (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq)
      (coborderOuterRectangle_comm_rsm_id B S hS j j' b a hsq) 1)
    (hnat := (modulePullbackCompIso B S hS (representedSpaceMap B S hS (𝟙 R))
      (representedSpaceMap B S hS b)).inv.naturality
        (representedConormalOfImmersionKernelIdealZPowIso B S hS j').hom)
    (hD := conormalCoborderOuterRectangle_square_rsm_id B S hS j j' b a hsq)
    (h₁ := conormalCoborderRectangle_square_rsm_id B S hS j j' b a hsq)
    (hTnat := representedAssociatedModulePullbackIso_naturality B S hS (𝟙 R)
      (relativelyRepresentable_yoneda_map B S hS (𝟙 R)) _)
    (hTcomp := representedAssociatedModulePullbackIso_comp_id_left B S hS b _)
    (ha := Stacks.CategoryTheory.map_map_eq_comp₃_of
      (representedSmallEtaleModuleEquivalence B S hS R).functor
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj R) R.left.property)
      _ _ _ (ha_zariski B S hS j j' b a hsq))
    (hc2 := Iso.hom_inv_id_app (modulePullbackCompIso B S hS
      (representedSpaceMap B S hS (𝟙 R)) (representedSpaceMap B S hS b)) _)
    (hki := @IsIso.hom_inv_id _ _ _ _ _ this)
    (hfaith := fun x y hxy => modulePullback_rsm_id_map_injective B S hS x y hxy)

/-- **Part (2) of [Stacks Project, Tag 04G2] at immersion generality.**

For a commutative square of the big fppf category over `S` whose horizontal morphisms are
immersions of schemes — the generality at which [Stacks Project, Tag 04CP] states its hypothesis,
and so the generality of the clause — the comparison of part (1)
(`AlgebraicGeometry.Space.conormalModuleOfImmersionRepresentedIso`) carries the canonical map of
conormal modules of [Stacks Project, Tag 04CP] to the associated module of
`Stacks.Immersion.immersionConormalSheafMap`, the canonical map of Morphisms, Lemma
[Stacks Project, Tag 01R4].

`AlgebraicGeometry.Space.conormalMapOfImmersions_conormalModuleOfImmersionRepresentedIso` with its
hypothesis `hnat` supplied by
`AlgebraicGeometry.Space.conormalMapOfImmersions_naturality_of_immersions`. -/
@[stacks 04G2 "part (2): for a commutative square of the big fppf site whose two horizontal \
morphisms are immersions of schemes, the comparison of part (1) carries the canonical map of \
conormal modules of 04CP to the associated module of the canonical map of Morphisms, Lemma 01R4"]
theorem conormalModuleOfImmersionRepresentedIso_naturality (hsq : j ≫ a = b ≫ j') :
    conormalMapOfImmersions B S hS (representedSpaceMap B S hS j)
          (representedSpaceMap B S hS j') (representedSpaceMap B S hS b)
          (representedSpaceMap B S hS a) (isImmersion_representedSpaceMap B S hS j)
          (isImmersion_representedSpaceMap B S hS j')
          (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq) ≫
        (conormalModuleOfImmersionRepresentedIso B S hS j).hom =
      (modulePullback B S hS (representedSpaceMap B S hS b)).map
          (conormalModuleOfImmersionRepresentedIso B S hS j').hom ≫
        (representedAssociatedModulePullbackIso B S hS b
              (relativelyRepresentable_yoneda_map B S hS b)
              (Stacks.Conormal.conormalSheaf
                ((BigFppfOver.toScheme B S hS).map j'))).hom ≫
          (representedSmallEtaleModuleEquivalence B S hS R).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj R) R.left.property).map
              (Stacks.Immersion.immersionConormalSheafMap
                ((BigFppfOver.toScheme B S hS).map j)
                ((BigFppfOver.toScheme B S hS).map j')
                ((BigFppfOver.toScheme B S hS).map b)
                ((BigFppfOver.toScheme B S hS).map a)
                (toShHom_square_of_comp_eq B S hS j j' b a hsq))) :=
  conormalMapOfImmersions_conormalModuleOfImmersionRepresentedIso B S hS j j' b a hsq
    (conormalMapOfImmersions_naturality_of_immersions B S hS j j' b a hsq)

end Backward

end AlgebraicGeometry.Space

end
