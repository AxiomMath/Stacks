module

public import StacksFrontier.CategoryTheory.ChangeOfAmbientConormal
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleOfImmersionRestrictionCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleRepresentedImmersionNaturality

/-!
# The agreement of the two part-(1) comparisons across the change of ambient

Let `j : R ⟶ V` be a morphism of the big fppf category over a scheme `S` whose underlying
morphism of schemes is an **immersion**, let `C` be its coborder ambient
`AlgebraicGeometry.Space.immersionCoborderObj` and let `L = `
`AlgebraicGeometry.Space.immersionCoborderLift` be the closed factorisation of `j` through it.

Part (1) of [Stacks Project, Tag 04G2] is available in two forms over this pair:

* at `j` itself, at immersion generality, as
  `AlgebraicGeometry.Space.conormalModuleOfImmersionRepresentedIso`, respelled into the
  kernel-ideal-power spelling by
  `AlgebraicGeometry.Space.representedConormalOfImmersionKernelIdealZPowIso`;
* at `L`, which is a **closed** immersion, as
  `AlgebraicGeometry.Space.representedConormalKernelIdealZPowIso`.

The two are *not* the same construction — the first carries the ambient open of
[Stacks Project, Tag 04CE] and the second does not — and nothing in the tree related them.  This
file does: they are carried to one another by the canonical map of [Stacks Project, Tag 04CP] of
the change-of-ambient square

```
R --L--→ C
|        |
𝟙        ι
↓        ↓
R --j--→ V
```

and the associated module of `Stacks.Immersion.conormalSheafSelfIso`.  That is
`AlgebraicGeometry.Space.conormalChangeOfAmbientAgreement`.

## Main results

* `AlgebraicGeometry.Space.conormalChangeOfAmbientAgreement`: **the agreement of the two
  part-(1) comparisons across the change of ambient.**
* `AlgebraicGeometry.Space.coborderComparisonTailIso_hom_comp`: the tail of part (1)'s chain,
  followed by the closed comparison at the lift, is the inverse of the bridge of
  [Stacks Project, Tag 09RR] at the lift.  This is where the bridge, the identification of the
  kernel ideal sheaf with the defining ideal sheaf of [Stacks Project, Tag 03MB] and the closed
  respelling all cancel.
* `AlgebraicGeometry.Space.nineRRBridge_comp_representedIdealIdentifications` and
  `AlgebraicGeometry.Space.representedConormalTail_comp`: that cancellation at an arbitrary
  represented closed immersion of the site, which is where it is proved.
* `AlgebraicGeometry.Space.kernelIdealZPowSquareMap_coborder_eq`: the canonical map of
  [Stacks Project, Tag 04CP] of the change-of-ambient square, written through
  [Stacks Project, Tag 04CO]'s isomorphism.

## Route

Part (1) at immersion generality is, by construction, the unit law of
[Stacks Project, Tag 03LU] followed by the isomorphism of [Stacks Project, Tag 04CO] at the
cartesian square above followed by a tail
(`AlgebraicGeometry.Space.coborderComparisonTailIso`).  Three identifications turn that into the
statement:

* [Stacks Project, Tag 04CO]'s isomorphism **is**
  `AlgebraicGeometry.Space.conormalMapOfImmersions` of the square
  (`AlgebraicGeometry.Space.conormalModuleOfImmersionEtaleRestrictionIso_hom`), which
  `AlgebraicGeometry.Space.conormalMapOfImmersions_eq_kernelIdealZPowSquareMap` writes at the
  kernel-ideal-power spelling; solving that for the canonical map is
  `Stacks.CategoryTheory.eq_map_comp_of_conjugate`.
* the tail cancels against the closed comparison, which is
  `AlgebraicGeometry.Space.coborderComparisonTailIso_hom_comp`.
* the unit law of [Stacks Project, Tag 03LU] moves across by its naturality.

## Implementation notes

`AlgebraicGeometry.Space.modulePullback` and its composition comparison are made locally
irreducible in the second section only, as they are in the two files this one sits over.  The
first section must not make them irreducible: the identification of the bridge of
[Stacks Project, Tag 09RR] with
`AlgebraicGeometry.Space.conormalModuleOfImmersionZPowIso` needs the equality of the degree-one
piece of `AlgebraicGeometry.Space.conormalAlgebra` with the inverse image of the kernel ideal
sheaf, which holds by `rfl` and which the irreducible attribute blocks — with it the check is an
`isDefEq` deterministic timeout, without it free.

The cancellation of that bridge is proved at a **plain morphism `k` of the site**, not inline at
the coborder lift: at the lift the same statement is a kernel deterministic timeout, and
instantiating the plain-variable lemma there is free.

**No equation between morphisms is proved by `rfl` here**, and that is not stylistic:
the factorisation of the bridge of [Stacks Project, Tag 09RR] into
`AlgebraicGeometry.Space.conormalModuleOfImmersionZPowIso` and a transport is a **kernel
deterministic timeout** when stated between morphisms and proved by `rfl` — in both the
`AlgebraicGeometry.Space.conormalAlgebra` piece spelling and the
`AlgebraicGeometry.Space.kernelIdealSheafZPow` one — while the *same equation* proved by a term
application of `Stacks.CategoryTheory.symm_trans_hom`, a generic lemma at plain variables, is
free.  Equations between isomorphisms, on the other hand, are free by `rfl`.  So every chain here
is introduced by an `Iso`-level `rfl` and read out by a generic lemma.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 09RR](https://stacks.math.columbia.edu/tag/09RR)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Represented

variable {T' T : BigFppfOver B S hS} (k : T' ⟶ T)
    [hk : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map k)]
    (hik : IsImmersion B S hS (representedSpaceMap B S hS k).hom)

omit hk in
/-- **The bridge of [Stacks Project, Tag 09RR] in degree one is the conormal-algebra piece
comparison.**  True by `rfl` between isomorphisms; the module documentation records why no
equation between morphisms in this file is. -/
theorem conormalModuleOfImmersionZPowIso_eq_piece :
    conormalModuleOfImmersionZPowIso B S hS (representedSpaceMap B S hS k) hik =
      conormalAlgebraOfImmersionPieceIso B S hS (representedSpaceMap B S hS k) hik 1 :=
  rfl

omit hk in
/-- **The bridge of [Stacks Project, Tag 09RR] is the degree-one bridge inverted, up to the
transport along `AlgebraicGeometry.Space.kernelIdealSheafZPow_one`.**  An equation between
isomorphisms; the module documentation records why no equation between morphisms in this file
is proved by `rfl`. -/
theorem conormalModuleOfImmersionKernelPullbackIso_eq :
    conormalModuleOfImmersionKernelPullbackIso B S hS (representedSpaceMap B S hS k) hik =
      (conormalModuleOfImmersionZPowIso B S hS (representedSpaceMap B S hS k) hik).symm ≪≫
        eqToIso (congrArg
          (fun N : (SheafOfModules.unit (structureRingSheaf B S hS
              ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)).Submodule =>
            (modulePullback B S hS (representedSpaceMap B S hS k)).obj N.toSheafOfModules)
          (kernelIdealSheafZPow_one B S hS (representedSpaceMap B S hS k))) :=
  rfl

/-- **The bridge of [Stacks Project, Tag 09RR] cancels against the two identifications of ideal
sheaves.**  For a represented closed immersion, the bridge presenting the conormal module as the
inverse image of the kernel ideal sheaf, the identification of that kernel ideal sheaf with the
defining ideal sheaf of [Stacks Project, Tag 03MB], and the transport onto the degree-one power
compose to the inverse of `AlgebraicGeometry.Space.conormalModuleOfImmersionZPowIso`.

Stated at a plain morphism `k` of the site rather than inline at the coborder lift: at the lift
the same statement is a kernel deterministic timeout. -/
theorem nineRRBridge_comp_representedIdealIdentifications :
    (conormalModuleOfImmersionKernelPullbackIso B S hS
          (representedSpaceMap B S hS k) hik).hom ≫
        (modulePullbackKernelIdealSheafDefiningIdealSheafIso B S hS k hk).hom ≫
          (modulePullback B S hS (representedSpaceMap B S hS k)).map
            (eqToHom (congrArg
              (fun N : (SheafOfModules.unit (structureRingSheaf B S hS
                  ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)).Submodule =>
                N.toSheafOfModules)
              (kernelIdealSheafZPow_one_representedSpaceMap B S hS k hk).symm)) =
      (conormalModuleOfImmersionZPowIso B S hS (representedSpaceMap B S hS k) hik).inv :=
  Stacks.CategoryTheory.comp3_eq_of_transport
    (conormalModuleOfImmersionZPowIso B S hS (representedSpaceMap B S hS k) hik).inv
    (congrArg
      (fun N : (SheafOfModules.unit (structureRingSheaf B S hS
          ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)).Submodule =>
        (modulePullback B S hS (representedSpaceMap B S hS k)).obj N.toSheafOfModules)
      (kernelIdealSheafZPow_one B S hS (representedSpaceMap B S hS k)))
    _ _ _ _ _
    ((congrArg Iso.hom (conormalModuleOfImmersionKernelPullbackIso_eq B S hS k hik)).trans
      (Stacks.CategoryTheory.symm_trans_hom
        (conormalModuleOfImmersionZPowIso B S hS (representedSpaceMap B S hS k) hik) _))
    rfl (eqToHom_map _ _)

/-- **The tail of part (1)'s chain, followed by the closed comparison, is the inverse of the
bridge of [Stacks Project, Tag 09RR].**

The last two factors of the tail are the inverse of
`AlgebraicGeometry.Space.representedConormalDefiningIdealIso`, by
`AlgebraicGeometry.Space.representedDefiningIdealPullbackConormalSheafIso_hom_comp`, and the
closed comparison is that isomorphism followed by a transport, by
`AlgebraicGeometry.Space.representedConormalKernelIdealZPowIso_hom_eq`; so they cancel and what
is left is `AlgebraicGeometry.Space.nineRRBridge_comp_representedIdealIdentifications`. -/
theorem representedConormalTail_comp :
    (conormalModuleOfImmersionKernelPullbackIso B S hS
          (representedSpaceMap B S hS k) hik ≪≫
        modulePullbackKernelIdealSheafDefiningIdealSheafIso B S hS k hk ≪≫
          representedDefiningIdealPullbackConormalSheafIso B S hS k ≪≫
            (representedSmallEtaleModuleEquivalence B S hS T').functor.mapIso
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).mapIso
                (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
                  ((BigFppfOver.toScheme B S hS).map k)))).hom ≫
        (representedConormalKernelIdealZPowIso B S hS k).hom =
      (conormalModuleOfImmersionZPowIso B S hS (representedSpaceMap B S hS k) hik).inv :=
  Stacks.CategoryTheory.comp4_comp_cancel _ _ _ _ _ _ _ _ _ _
    (Stacks.CategoryTheory.trans4_hom _ _ _ _)
    (representedConormalKernelIdealZPowIso_hom_eq B S hS k)
    (representedDefiningIdealPullbackConormalSheafIso_hom_comp B S hS k)
    (Iso.inv_hom_id _)
    (nineRRBridge_comp_representedIdealIdentifications B S hS k hik)

end Represented

section Coborder

attribute [local irreducible] modulePullback modulePullbackCompIso
  representedModuleObjPullbackIso

variable {R V : BigFppfOver B S hS} (j : R ⟶ V)
    [hj : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)]

/-- **The coborder lift of a represented immersion represents an immersion of algebraic
spaces.**  It is the base change of `j` along the ambient inclusion, by
`AlgebraicGeometry.Space.isPullback_representedSpaceMap_immersionCoborderLift`. -/
theorem isImmersion_representedSpaceMap_immersionCoborderLift :
    IsImmersion B S hS (representedSpaceMap B S hS (immersionCoborderLift B S hS j)).hom :=
  isImmersion_of_isPullback B S hS
    (isPullback_representedSpaceMap_immersionCoborderLift B S hS j)
    (isImmersion_representedSpaceMap B S hS j)

/-- **The isomorphism of [Stacks Project, Tag 04CO] at the coborder factorisation of a
represented immersion.**  The cartesian square is
`AlgebraicGeometry.Space.isPullback_representedSpaceMap_immersionCoborderLift` and its bottom
edge, the inclusion of the ambient open, is étale. -/
def coborderEtaleRestrictionIso :
    (modulePullback B S hS
          (𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS))).obj
        (immersionConormalModule B S hS (representedSpaceMap B S hS j)
          (isImmersion_representedSpaceMap B S hS j)) ≅
      immersionConormalModule B S hS
        (representedSpaceMap B S hS (immersionCoborderLift B S hS j))
        (isImmersion_representedSpaceMap_immersionCoborderLift B S hS j) :=
  conormalModuleOfImmersionEtaleRestrictionIso B S hS
    (𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS))
    (representedSpaceMap B S hS (immersionCoborderLift B S hS j))
    (representedSpaceMap B S hS j)
    (representedSpaceMap B S hS
      (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))
    (isPullback_representedSpaceMap_immersionCoborderLift B S hS j)
    (isImmersion_representedSpaceMap B S hS j)
    (isEtale_representedSpaceMap_openSubHom B S hS V
      ((BigFppfOver.toScheme B S hS).map j).coborderRange)

/-- **The tail of part (1)'s chain at immersion generality**, from the conormal module of the
coborder lift to the associated module of the conormal sheaf of the morphism of schemes: the
bridge of [Stacks Project, Tag 09RR] at the lift, the identification of its kernel ideal sheaf
with the defining ideal sheaf of [Stacks Project, Tag 03MB], the closed case of part (1) at the
lift, and the schemes-side presentation of the conormal sheaf of the lift as its own. -/
noncomputable abbrev coborderComparisonTailIso :
    immersionConormalModule B S hS
        (representedSpaceMap B S hS (immersionCoborderLift B S hS j))
        (isImmersion_representedSpaceMap_immersionCoborderLift B S hS j) ≅
      (representedSmallEtaleModuleEquivalence B S hS R).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj R) R.left.property).obj
          (Stacks.ClosedImmersion.conormalSheaf
            ((BigFppfOver.toScheme B S hS).map
              (immersionCoborderLift B S hS j)).toLRSHom.toShHom)) :=
  conormalModuleOfImmersionKernelPullbackIso B S hS
      (representedSpaceMap B S hS (immersionCoborderLift B S hS j))
      (isImmersion_representedSpaceMap_immersionCoborderLift B S hS j) ≪≫
    modulePullbackKernelIdealSheafDefiningIdealSheafIso B S hS
        (immersionCoborderLift B S hS j)
        (isClosedImmersion_toScheme_map_immersionCoborderLift B S hS j) ≪≫
      representedDefiningIdealPullbackConormalSheafIso B S hS
          (immersionCoborderLift B S hS j) ≪≫
        (representedSmallEtaleModuleEquivalence B S hS R).functor.mapIso
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj R) R.left.property).mapIso
            (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
              ((BigFppfOver.toScheme B S hS).map (immersionCoborderLift B S hS j))))

/-- **Part (1) at immersion generality, in the three named factors it is built from**: the unit
law of [Stacks Project, Tag 03LU], the isomorphism of [Stacks Project, Tag 04CO] at the coborder
factorisation, and the tail. -/
theorem conormalModuleOfImmersionRepresentedIso_eq :
    conormalModuleOfImmersionRepresentedIso B S hS j =
      ((modulePullbackIdIso B S hS
              (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ :
                AlgebraicSpaces B S hS)).app
            (immersionConormalModule B S hS (representedSpaceMap B S hS j)
              (isImmersion_representedSpaceMap B S hS j))).symm ≪≫
        coborderEtaleRestrictionIso B S hS j ≪≫ coborderComparisonTailIso B S hS j :=
  rfl

/-- The four factors of `AlgebraicGeometry.Space.coborderComparisonTailIso`, written out. -/
theorem coborderComparisonTailIso_hom :
    (coborderComparisonTailIso B S hS j).hom =
      (conormalModuleOfImmersionKernelPullbackIso B S hS
            (representedSpaceMap B S hS (immersionCoborderLift B S hS j))
            (isImmersion_representedSpaceMap_immersionCoborderLift B S hS j)).hom ≫
        (modulePullbackKernelIdealSheafDefiningIdealSheafIso B S hS
              (immersionCoborderLift B S hS j)
              (isClosedImmersion_toScheme_map_immersionCoborderLift B S hS j)).hom ≫
          (representedDefiningIdealPullbackConormalSheafIso B S hS
                (immersionCoborderLift B S hS j)).hom ≫
            ((representedSmallEtaleModuleEquivalence B S hS R).functor.mapIso
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj R) R.left.property).mapIso
                (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
                  ((BigFppfOver.toScheme B S hS).map
                    (immersionCoborderLift B S hS j))))).hom :=
  Stacks.CategoryTheory.trans4_hom
    (conormalModuleOfImmersionKernelPullbackIso B S hS
      (representedSpaceMap B S hS (immersionCoborderLift B S hS j))
      (isImmersion_representedSpaceMap_immersionCoborderLift B S hS j))
    (modulePullbackKernelIdealSheafDefiningIdealSheafIso B S hS
      (immersionCoborderLift B S hS j)
      (isClosedImmersion_toScheme_map_immersionCoborderLift B S hS j))
    (representedDefiningIdealPullbackConormalSheafIso B S hS
      (immersionCoborderLift B S hS j))
    ((representedSmallEtaleModuleEquivalence B S hS R).functor.mapIso
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj R) R.left.property).mapIso
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
          ((BigFppfOver.toScheme B S hS).map (immersionCoborderLift B S hS j)))))

/-- The inverse of part (1) at immersion generality, in the three named factors. -/
theorem conormalModuleOfImmersionRepresentedIso_inv :
    (conormalModuleOfImmersionRepresentedIso B S hS j).inv =
      (coborderComparisonTailIso B S hS j).inv ≫ (coborderEtaleRestrictionIso B S hS j).inv ≫
        (modulePullbackIdIso B S hS
            (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ :
              AlgebraicSpaces B S hS)).hom.app
          (immersionConormalModule B S hS (representedSpaceMap B S hS j)
            (isImmersion_representedSpaceMap B S hS j)) :=
  Stacks.CategoryTheory.symm_trans3_inv
    ((modulePullbackIdIso B S hS
        (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS)).app
      (immersionConormalModule B S hS (representedSpaceMap B S hS j)
        (isImmersion_representedSpaceMap B S hS j)))
    (coborderEtaleRestrictionIso B S hS j) (coborderComparisonTailIso B S hS j)


/-- **The tail of part (1)'s chain at the coborder lift, followed by the closed comparison
there**, which is `AlgebraicGeometry.Space.representedConormalTail_comp` at the lift. -/
theorem coborderComparisonTailIso_hom_comp :
    (coborderComparisonTailIso B S hS j).hom ≫
        (representedConormalKernelIdealZPowIso B S hS
          (immersionCoborderLift B S hS j)).hom =
      (conormalModuleOfImmersionZPowIso B S hS
        (representedSpaceMap B S hS (immersionCoborderLift B S hS j))
        (isImmersion_representedSpaceMap_immersionCoborderLift B S hS j)).inv := by
  rw [coborderComparisonTailIso_hom]
  exact representedConormalTail_comp B S hS (immersionCoborderLift B S hS j)
    (hk := isClosedImmersion_toScheme_map_immersionCoborderLift B S hS j)
    (isImmersion_representedSpaceMap_immersionCoborderLift B S hS j)

/-- **The canonical map of [Stacks Project, Tag 04CP] of the change-of-ambient square, written
through the isomorphism of [Stacks Project, Tag 04CO].** -/
theorem kernelIdealZPowSquareMap_coborder_eq :
    kernelIdealZPowSquareMap B S hS
        (representedSpaceMap B S hS (immersionCoborderLift B S hS j))
        (representedSpaceMap B S hS j)
        (𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS))
        (representedSpaceMap B S hS
          (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))
        (isPullback_representedSpaceMap_immersionCoborderLift B S hS j).w.symm 1 =
      (modulePullback B S hS
            (𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ :
              AlgebraicSpaces B S hS))).map
          (conormalModuleOfImmersionZPowIso B S hS (representedSpaceMap B S hS j)
            (isImmersion_representedSpaceMap B S hS j)).hom ≫
        (coborderEtaleRestrictionIso B S hS j).hom ≫
          (conormalModuleOfImmersionZPowIso B S hS
            (representedSpaceMap B S hS (immersionCoborderLift B S hS j))
            (isImmersion_representedSpaceMap_immersionCoborderLift B S hS j)).inv :=
  Stacks.CategoryTheory.eq_map_comp_of_conjugate _ _ _ _ _ _ _
    ((conormalModuleOfImmersionEtaleRestrictionIso_hom B S hS
          (𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS))
          (representedSpaceMap B S hS (immersionCoborderLift B S hS j))
          (representedSpaceMap B S hS j)
          (representedSpaceMap B S hS
            (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))
          (isPullback_representedSpaceMap_immersionCoborderLift B S hS j)
          (isImmersion_representedSpaceMap B S hS j)
          (isEtale_representedSpaceMap_openSubHom B S hS V
            ((BigFppfOver.toScheme B S hS).map j).coborderRange)).trans
      (conormalMapOfImmersions_eq_kernelIdealZPowSquareMap B S hS
        (representedSpaceMap B S hS (immersionCoborderLift B S hS j))
        (representedSpaceMap B S hS j)
        (𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS))
        (representedSpaceMap B S hS
          (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))
        (isImmersion_representedSpaceMap_immersionCoborderLift B S hS j)
        (isImmersion_representedSpaceMap B S hS j)
        (isPullback_representedSpaceMap_immersionCoborderLift B S hS j).w.symm))
    (Iso.hom_inv_id _) (Iso.hom_inv_id _)

/-- **The agreement of the two part-(1) comparisons of [Stacks Project, Tag 04G2] across the
change of ambient.**

For a morphism `j : R ⟶ V` of the big fppf category over `S` whose underlying morphism of
schemes is an immersion, the comparison of part (1) at immersion generality at `j` and the
comparison at the **closed** coborder lift of `j` are carried to one another by the canonical map
of [Stacks Project, Tag 04CP] of the change-of-ambient square — up to the unit law of
[Stacks Project, Tag 03LU] and the associated module of `Stacks.Immersion.conormalSheafSelfIso`,
which is the schemes-side change of ambient of Morphisms, Definition
[Stacks Project, Tag 01R2].

This is the shape in which a composition law for the canonical map consumes the statement, so it
is what lets part (2) of [Stacks Project, Tag 04G2] be reduced from immersions to closed
immersions. -/
theorem conormalChangeOfAmbientAgreement :
    (modulePullback B S hS
            (𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ :
              AlgebraicSpaces B S hS))).map
          (representedConormalOfImmersionKernelIdealZPowIso B S hS j).hom ≫
        kernelIdealZPowSquareMap B S hS
          (representedSpaceMap B S hS (immersionCoborderLift B S hS j))
          (representedSpaceMap B S hS j)
          (𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS))
          (representedSpaceMap B S hS
            (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))
          (isPullback_representedSpaceMap_immersionCoborderLift B S hS j).w.symm 1 =
      (modulePullbackIdIso B S hS
            (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ :
              AlgebraicSpaces B S hS)).hom.app
          ((representedSmallEtaleModuleEquivalence B S hS R).functor.obj
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj R) R.left.property).obj
              (Stacks.ClosedImmersion.conormalSheaf
                ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom))) ≫
        ((representedSmallEtaleModuleEquivalence B S hS R).functor.mapIso
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj R) R.left.property).mapIso
                (Stacks.Immersion.conormalSheafSelfIso
                  ((BigFppfOver.toScheme B S hS).map j)))).hom ≫
          (representedConormalKernelIdealZPowIso B S hS
            (immersionCoborderLift B S hS j)).hom :=
  Stacks.CategoryTheory.change_of_ambient_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (representedConormalOfImmersionKernelIdealZPowIso_hom B S hS j) (Iso.inv_hom_id _)
    (kernelIdealZPowSquareMap_coborder_eq B S hS j)
    (conormalModuleOfImmersionRepresentedIso_inv B S hS j)
    (Iso.hom_inv_id_app _ _) (Iso.inv_hom_id _) (Iso.inv_hom_id _)
    (coborderComparisonTailIso_hom_comp B S hS j)
    ((modulePullbackIdIso B S hS
        (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ :
          AlgebraicSpaces B S hS)).hom.naturality _)

end Coborder

end AlgebraicGeometry.Space

end
