module

public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.SectionwiseKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModule
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFiniteLocallyFreeTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedStructureProjectionSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureProjectionComposition

/-!
# The defining ideal sheaf of a closed subspace of a representable algebraic space, as an object

Let `B` be a big fppf site containing a scheme `S`, let `T` be an object of the big fppf category
over `S` and let `Z ⊆ yoneda.obj T` be a closed subspace of the algebraic space it represents.
Two ideal sheaves are attached to that datum:

* `AlgebraicGeometry.Space.definingIdealSheaf` of Stacks 03MB, an `𝒪`-module on the **small étale
  site** of `yoneda.obj T`;
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom` of the representing closed
  immersion of schemes, a module on the **Zariski site** of the representing scheme.

This file identifies the first with the transport of the second along
`AlgebraicGeometry.Space.representedAssociatedModule`, and reads that identification at the
conormal module of Stacks 04CN: the conormal module of `Z` in `yoneda.obj T` is, up to the
inverse image along the identification of `Z` with the algebraic space the representing scheme
represents, the `𝒪`-module that the Zariski pullback of `definingIdealOfHom` along the
representing closed immersion becomes.  Finite local freeness then crosses from the scheme to the
small étale site by the transport
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_representedQuasicoherentSchemeEquivalence`.

This is the comparison of the two ideal sheaves **as objects**. It is not clause (2) of Stacks
06CB; see *What this leaves owed* below for what separates them.

## Main definitions

* `AlgebraicGeometry.Space.kernelStructureProjectionOfHomIsoOfIso`: the kernel of the canonical
  morphism `𝒪_W ⟶ g_*𝒪_Y` of modules of [Stacks Project, Tag 03LU] is unchanged when `g` is
  precomposed with an isomorphism of algebraic spaces.
* `AlgebraicGeometry.Space.definingIdealSheafIsoKernelRepresented`: the defining ideal sheaf of a
  closed subspace of a representable algebraic space is the kernel of the canonical morphism of
  modules of `AlgebraicGeometry.Space.representedSpaceMap` of the representing morphism.
* `AlgebraicGeometry.Space.representedAssociatedModuleObjDefiningIdealOfHomIso`: the transport of
  the Zariski defining ideal sheaf of a morphism of the big fppf category over `S` whose
  underlying morphism of schemes is affine is the kernel of the same canonical morphism.
* `AlgebraicGeometry.Space.definingIdealSheafIsoRepresented`: **the object identification.**
* `AlgebraicGeometry.Space.modulePullbackObjIsoOfComp`: the inverse image of modules along a
  morphism factored as `r ≫ c` is the inverse image along `r` of the inverse image along `c`.
* `AlgebraicGeometry.Space.conormalModuleIsoRepresentedQuasicoherent`: **the conormal module of a
  closed subspace of a representable algebraic space, read on the representing scheme.**

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_conormalModule_representable`: **finite local
  freeness of the conormal module of a closed subspace of a representable algebraic space follows
  from finite local freeness of the Zariski pullback of the defining ideal sheaf of the
  representing closed immersion of schemes**, with no hypothesis beyond that.

## Implementation notes

**Every step is stated at variable objects and morphisms, and instantiated at the representing
datum only at the end.**  This is not a matter of taste.  The same chain written out at the
concrete data — `AlgebraicGeometry.Space.representingHom` of the closed subspace, its
`AlgebraicGeometry.Space.representedSubspaceIso` and the structure projections of both —
does not survive the kernel: three spellings of the composition step
(`CategoryTheory.Limits.kernelCompMono` with the transport taken separately, the composite's
invertibility as its own declaration, and the whole square passed to
`CategoryTheory.Limits.kernel.mapIso`) each exhausted the kernel's budget, because the implicit
object arguments of `≫` there mention `AlgebraicGeometry.Space.modulePushforward` of two
morphisms that are equal and not syntactically equal, and reconciling them unfolds the inverse
image to its construction by sheafification.  With the morphisms *variable* there is nothing to
unfold: `AlgebraicGeometry.Space.kernelStructureProjectionOfHomIsoOfIso` takes the factorisation
`ef.hom ≫ g = k` as a hypothesis and `subst`s it, and its instantiation at the representing datum
is substitution and costs under a second.

For the same reason the equation that `CategoryTheory.Limits.kernel.mapIso` consumes,
`AlgebraicGeometry.Space.structureProjectionOfHom_comp_eqToHom`, is a separate declaration: the
heartbeat budget is per declaration, and the composition law of [Stacks Project, Tag 03G8] at the
level of modules, `AlgebraicGeometry.Space.structureProjectionOfHom_comp`, is right-associated
exactly so that its second factor is the isomorphism the comparison needs.

The target of the assembled square
`AlgebraicGeometry.Space.representedAssociatedModule_structureProjection_square` is not given
there as an isomorphism, and it is one: the comparison of direct images
`AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso` is an isomorphism by construction,
and `CategoryTheory.SheafOfModules.pullbackObjUnitToUnit` at the structure map of a small étale
site is one by `AlgebraicGeometry.SmallEtale.isIso_pullbackObjUnitToUnit`; the three
`IsIso` facts are cut into their own declarations and the instance arguments are passed
explicitly, instance search not finding them at these concrete morphisms of sheaves on a small
étale site.

Left exactness of the transport is
`AlgebraicGeometry.Space.preservesFiniteLimits_representedAssociatedModule`, which is what lets
`CategoryTheory.Limits.PreservesKernel.iso` carry the scheme-side kernel presentation across it.

The two spellings of the structure map of a morphism of schemes meet here —
`AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`, which the assembled square uses, and
`RingedSpaceModuleAdjunction.structureSheafHom` of the underlying morphism of ringed spaces,
which `Stacks.ClosedImmersion.idealSheaf` and hence
`Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso` use — and they are equal by
`rfl`, so the two kernels are the same object and no bridge is needed.

## What this leaves owed

The comparison `AlgebraicGeometry.Space.RepresentableConormalSheafComparison` itself is proved,
by another route, as `AlgebraicGeometry.Space.representableConormalSheafComparison`, from
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_conormalSheaf_of_scheme` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/RepresentableConormal.lean`; what follows is
what this file's own route would still need.

This is the object identification, not clause (2) of
`AlgebraicGeometry.Space.RepresentableConormalSheafComparison`.  What separates them is now
entirely **scheme-level**, the space-level side being discharged by the statement below together
with `AlgebraicGeometry.Space.exists_schemeThickening_conormalSheafIso_of_isRepresentable` of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedUniversalThickeningConormal.lean`:

* that `Stacks.Thickenings.universalConormalSheaf` of a formally unramified morphism of schemes is
  finite locally free as soon as the Zariski pullback of
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom` of the inclusion of *some*
  universal first-order thickening of it is — which asks for the comparison of
  `Stacks.Thickenings.schemeConormalSheaf` of that inclusion with
  `Stacks.Thickenings.immersionConormalSheaf` of the inclusion of the thickening
  `Stacks.Thickenings.universalFirstOrderThickening` chooses, i.e. for
  `Stacks.Thickenings.UniversalFirstOrderThickening.canonicalIso` read on conormal sheaves and for
  the passage through `AlgebraicGeometry.Scheme.Hom.liftCoborder` that
  `Stacks.Thickenings.immersionConormalSheaf` takes;
* and that the thickening the space-level statement produces, which lives over
  `AlgebraicGeometry.Space.representingObj` of the closed subspace rather than over the object of
  the site the thickening identification names, may be transported along the isomorphism of the
  two — the ideal-sheaf half of which is
  `Stacks.ClosedImmersion.idealSheafCompIso`.

Nothing of the space-level comparison remains open.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 06CB](https://stacks.math.columbia.edu/tag/06CB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The canonical morphism of modules of a composite with an isomorphism -/

/-- **The composition law of [Stacks Project, Tag 03G8] at the level of modules, read at a
factorisation.**  Let `ef : X ≅ Y` be an isomorphism of algebraic spaces over `S`, let
`g : Y ⟶ W` and let `k = ef.hom ≫ g`.  Then the canonical morphism `𝒪_W ⟶ g_*𝒪_Y` of
`AlgebraicGeometry.Space.structureProjectionOfHom`, followed by the direct image along `g` of the
canonical morphism of `ef.hom`, the comparison of direct images of [Stacks Project, Tag 03LU] and
the transport along the factorisation, is the canonical morphism of `k`.

The transport is `CategoryTheory.eqToHom` of the factorisation and not left to defeq, and the
factorisation is a hypothesis rather than a definition, because this is the one step of the
comparison below whose two sides mention `AlgebraicGeometry.Space.modulePushforward` of two
morphisms that are equal and not syntactically equal; see the implementation notes of this file
for what writing it out at concrete morphisms costs.  The identity on the right is there so that
the statement is the equation `CategoryTheory.Limits.kernel.mapIso` consumes. -/
theorem structureProjectionOfHom_comp_eqToHom {X Y W : AlgebraicSpaces B S hS}
    (ef : X ≅ Y) (g : Y ⟶ W) (k : X ⟶ W) (h : ef.hom ≫ g = k) :
    structureProjectionOfHom B S hS g ≫
        ((modulePushforward B S hS g).map (structureProjectionOfHom B S hS ef.hom) ≫
          (modulePushforwardCompIso B S hS ef.hom g).hom.app
              (SheafOfModules.unit (structureRingSheaf B S hS X)) ≫
            eqToHom (congrArg (fun m : X ⟶ W => (modulePushforward B S hS m).obj
              (SheafOfModules.unit (structureRingSheaf B S hS X))) h)) =
      𝟙 _ ≫ structureProjectionOfHom B S hS k := by
  subst h
  exact Eq.trans (whisker_eq _ (whisker_eq _ (Category.comp_id _)))
    (Eq.trans (structureProjectionOfHom_comp B S hS ef.hom g).symm (Category.id_comp _).symm)

/-- **The kernel of the canonical morphism `𝒪_W ⟶ g_*𝒪_Y` of modules is unchanged by
precomposing `g` with an isomorphism of algebraic spaces.**

The comparison is `CategoryTheory.Limits.kernel.mapIso` at the square of
`AlgebraicGeometry.Space.structureProjectionOfHom_comp_eqToHom`, whose vertical arrows are the
identity at the source — both canonical morphisms come out of `𝒪_W` — and, at the target, the
direct image along `g` of the canonical morphism of the isomorphism, which is invertible by
`AlgebraicGeometry.Space.isIso_structureProjectionOfHom`, followed by the comparison of direct
images of [Stacks Project, Tag 03LU] and the transport along the factorisation. -/
noncomputable def kernelStructureProjectionOfHomIsoOfIso {X Y W : AlgebraicSpaces B S hS}
    (ef : X ≅ Y) (g : Y ⟶ W) (k : X ⟶ W) (h : ef.hom ≫ g = k) :
    kernel (structureProjectionOfHom B S hS g) ≅
      kernel (structureProjectionOfHom B S hS k) :=
  kernel.mapIso _ _ (Iso.refl _)
    ((modulePushforward B S hS g).mapIso
          (@asIso _ _ _ _ _ (isIso_structureProjectionOfHom B S hS ef)) ≪≫
        (modulePushforwardCompIso B S hS ef.hom g).app
            (SheafOfModules.unit (structureRingSheaf B S hS X)) ≪≫
          eqToIso (congrArg (fun m : X ⟶ W => (modulePushforward B S hS m).obj
            (SheafOfModules.unit (structureRingSheaf B S hS X))) h))
    (structureProjectionOfHom_comp_eqToHom B S hS ef g k h)

/-! ### The transported Zariski ideal sheaf as a kernel -/

section Square

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

/-- The direct image along the structure map of the square of small étale ringed sites of the
identification of the pulled-back structure sheaf with the structure sheaf is an isomorphism: the
identification is one by `AlgebraicGeometry.SmallEtale.isIso_pullbackObjUnitToUnit`, and a functor
preserves isomorphisms. -/
theorem isIso_pushforward_map_pullbackObjUnitToUnit :
    IsIso ((SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g)).map
      (SheafOfModules.pullbackObjUnitToUnit.{u}
        (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T') T'.left.property))) :=
  Functor.map_isIso _ _

section Affine

variable [_root_.AlgebraicGeometry.IsAffineHom
  (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)]

/-- The reading of the target of the assembled square
`AlgebraicGeometry.Space.representedAssociatedModule_structureProjection_square` before the
transport along the equivalence of the two small étale sites is an isomorphism: it is the inverse
of `AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso` followed by a direct image of the
unit comparison. -/
theorem isIso_pushforwardAssociatedModuleIso_inv_comp :
    IsIso ((_root_.AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso
            (associatedBigEtaleSite B) g.left
            (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf)
            (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit
              ((BigFppfOver.toScheme B S hS).obj T'))).inv ≫
        (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g)).map
          (SheafOfModules.pullbackObjUnitToUnit.{u}
            (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T') T'.left.property))) :=
  @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv _)
    (isIso_pushforward_map_pullbackObjUnitToUnit B S hS g)

/-- **The target of the assembled square is an isomorphism.**  The square
`AlgebraicGeometry.Space.representedAssociatedModule_structureProjection_square` identifies the
transport of the Zariski structure projection with
`AlgebraicGeometry.Space.structureProjectionOfHom` of the represented morphism under an
identification of the source and this one of the target; the square does not say that it is
invertible, and it is, which is what lets the two kernels be compared. -/
theorem isIso_representedAssociatedModule_structureProjection_target :
    IsIso (((representedModulePushforward B S hS T).map
          ((_root_.AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso
                (associatedBigEtaleSite B) g.left
                (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf)
                (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit
                  ((BigFppfOver.toScheme B S hS).obj T'))).inv ≫
            (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g)).map
              (SheafOfModules.pullbackObjUnitToUnit.{u}
                (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj T') T'.left.property)))) ≫
        (representedModulePushforwardSquareIso B S hS g
            (relativelyRepresentable_yoneda_map B S hS g)).hom.app
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))) :=
  @IsIso.comp_isIso _ _ _ _ _ _ _
    (@Functor.map_isIso _ _ _ _ _ _ (representedModulePushforward B S hS T) _
      (isIso_pushforwardAssociatedModuleIso_inv_comp B S hS g))
    (NatIso.isIso_app_of_isIso (representedModulePushforwardSquareIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g)).hom _)

/-- **The kernel of the transported Zariski structure projection is the kernel of the canonical
morphism of modules of the represented morphism.**  This is
`AlgebraicGeometry.Space.representedAssociatedModule_structureProjection_square` read on kernels,
its two vertical arrows being isomorphisms. -/
noncomputable def kernelRepresentedAssociatedModuleMapIso :
    kernel ((representedAssociatedModule B S hS T
            (isAlgebraicSpace_yoneda B S hS T)).map
        (SheafOfModules.unitToPushforwardObjUnit
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            g.left).toRingCatSheafHom)) ≅
      kernel (structureProjectionOfHom B S hS (representedSpaceMap B S hS g)) :=
  kernel.mapIso _ _
    (representedAssociatedModuleObjUnitIso B S hS T (isAlgebraicSpace_yoneda B S hS T))
    (@asIso _ _ _ _ _ (isIso_representedAssociatedModule_structureProjection_target B S hS g))
    (representedAssociatedModule_structureProjection_square B S hS g)

/-- **The transport of modules from the representing scheme commutes with the kernel of the
Zariski structure projection**, being left exact by
`AlgebraicGeometry.Space.preservesFiniteLimits_representedAssociatedModule`. -/
noncomputable def representedAssociatedModuleObjKernelIso :
    (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).obj
        (kernel (SheafOfModules.unitToPushforwardObjUnit
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            g.left).toRingCatSheafHom)) ≅
      kernel ((representedAssociatedModule B S hS T
            (isAlgebraicSpace_yoneda B S hS T)).map
        (SheafOfModules.unitToPushforwardObjUnit
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            g.left).toRingCatSheafHom)) :=
  PreservesKernel.iso _ _

/-- **The transport of the Zariski defining ideal sheaf of a morphism of the big fppf category
over `S` whose underlying morphism of schemes is affine is the kernel of the canonical morphism
`𝒪 ⟶ φ_*𝒪` of modules of the represented morphism.**

The three steps are the identification of the sectionwise ideal sheaf with the categorical kernel,
`Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso`; the left exactness of the
transport; and the assembled square.  The categorical kernel on the scheme side is taken of
`AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`, which is
`RingedSpaceModuleAdjunction.structureSheafHom` of the underlying morphism of ringed spaces by
`rfl`, so no comparison of the two spellings intervenes. -/
noncomputable def representedAssociatedModuleObjDefiningIdealOfHomIso :
    (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).obj
        (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            g.left)).toSheafOfModules ≅
      kernel (structureProjectionOfHom B S hS (representedSpaceMap B S hS g)) :=
  (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).mapIso
      (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)) ≪≫
    representedAssociatedModuleObjKernelIso B S hS g ≪≫
      kernelRepresentedAssociatedModuleMapIso B S hS g

end Affine

end Square

/-! ### The object identification at a closed subspace -/

variable (T : BigFppfOver B S hS) (Z : ClosedSubspaces B S hS (yoneda.obj T))

/-- **The defining ideal sheaf of a closed subspace of a representable algebraic space is the
kernel of the canonical morphism of modules of the representing morphism.**

`AlgebraicGeometry.Space.definingIdealSheafIsoKernel` presents it as the kernel of the structure
projection, which is `AlgebraicGeometry.Space.structureProjectionOfHom` of the inclusion of the
subspace, and `AlgebraicGeometry.Space.representedSpaceMap_representingHom` factors that inclusion
as `AlgebraicGeometry.Space.representedSubspaceIso` followed by the represented morphism of the
representing morphism. -/
noncomputable def definingIdealSheafIsoKernelRepresented :
    (definingIdealSheaf B S hS
          ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ Z).toSheafOfModules ≅
      kernel (structureProjectionOfHom B S hS
        (representedSpaceMap B S hS (representingHom B S hS T Z))) :=
  definingIdealSheafIsoKernel B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ Z ≪≫
    kernelStructureProjectionOfHomIsoOfIso B S hS (representedSubspaceIso B S hS T Z)
      (subspaceInclusion B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ Z)
      (representedSpaceMap B S hS (representingHom B S hS T Z))
      (representedSpaceMap_representingHom B S hS T Z).symm

/-- **The object identification: the defining ideal sheaf of Stacks 03MB of a closed subspace of a
representable algebraic space is the `𝒪`-module that the defining ideal sheaf of the representing
closed immersion of schemes becomes.**

Both are kernels of a structure projection — the first by
`AlgebraicGeometry.Space.definingIdealSheafIsoKernelRepresented`, the second by
`AlgebraicGeometry.Space.representedAssociatedModuleObjDefiningIdealOfHomIso` — and the two
projections are identified by the assembled square
`AlgebraicGeometry.Space.representedAssociatedModule_structureProjection_square`, whose standing
affineness hypothesis is discharged at the representing morphism by
`AlgebraicGeometry.Space.isAffineHom_schemeHom_representingHom`.  Nothing is assumed. -/
noncomputable def definingIdealSheafIsoRepresented :
    (definingIdealSheaf B S hS
          ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ Z).toSheafOfModules ≅
      (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).obj
        (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            (representingHom B S hS T Z).left)).toSheafOfModules :=
  letI := isAffineHom_schemeHom_representingHom B S hS T Z
  definingIdealSheafIsoKernelRepresented B S hS T Z ≪≫
    (representedAssociatedModuleObjDefiningIdealOfHomIso B S hS
      (representingHom B S hS T Z)).symm

/-! ### The conormal module at the representing closed immersion -/

/-- **The inverse image of modules along a factored morphism.**  For `r ≫ c = k` the inverse image
of Stacks 03LU along `k` of a module on the target is the inverse image along `r` of the inverse
image along `c`.

The factorisation is a hypothesis and the transport along it is `CategoryTheory.eqToIso`, for the
reason recorded in the implementation notes of this file: comparing two spellings of one object
under `CategoryTheory.Functor.obj` of the inverse image forces that functor open to its
construction by sheafification. -/
noncomputable def modulePullbackObjIsoOfComp {X Y W : AlgebraicSpaces B S hS}
    (r : X ⟶ Y) (c : Y ⟶ W) (k : X ⟶ W) (h : r ≫ c = k)
    (M : Modules.{u, u} B S hS W.1 W.2) :
    (modulePullback B S hS k).obj M ≅
      (modulePullback B S hS r).obj ((modulePullback B S hS c).obj M) :=
  eqToIso (congrArg (fun m : X ⟶ W => (modulePullback B S hS m).obj M) h.symm) ≪≫
    ((modulePullbackCompIso B S hS r c).app M).symm

/-- The inverse image of the defining ideal sheaf of a closed subspace along the represented
morphism of the representing morphism is the inverse image, along
`AlgebraicGeometry.Space.representedSubspaceIso`, of the conormal module of Stacks 04CN of the
subspace. -/
noncomputable def modulePullbackDefiningIdealSheafIsoConormalModule :
    (modulePullback B S hS
          (representedSpaceMap B S hS (representingHom B S hS T Z))).obj
        (definingIdealSheaf B S hS
          ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ Z).toSheafOfModules ≅
      (modulePullback B S hS (representedSubspaceIso B S hS T Z).hom).obj
        (conormalModule B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ Z) :=
  modulePullbackObjIsoOfComp B S hS (representedSubspaceIso B S hS T Z).hom
    (subspaceInclusion B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ Z)
    (representedSpaceMap B S hS (representingHom B S hS T Z))
    (representedSpaceMap_representingHom B S hS T Z).symm
    (definingIdealSheaf B S hS
      ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ Z).toSheafOfModules

/-- **The conormal module of a closed subspace of a representable algebraic space, read on the
representing scheme.**  Pulled back along `AlgebraicGeometry.Space.representedSubspaceIso`, the
conormal module of Stacks 04CN of `Z ⊆ yoneda.obj T` is the `𝒪`-module that the Zariski pullback,
along the representing closed immersion of schemes, of the defining ideal sheaf of that immersion
becomes under `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`.

This is `AlgebraicGeometry.Space.definingIdealSheafIsoRepresented` pulled back along the
represented morphism of the representing morphism and read through
`AlgebraicGeometry.Space.representedQuasicoherentSchemePullbackIso`; the quasi-coherence the
latter asks for is `AlgebraicGeometry.Space.isQuasicoherent_definingIdealOfHom`, available because
the representing morphism of schemes is a closed immersion. -/
noncomputable def conormalModuleIsoRepresentedQuasicoherent :
    (modulePullback B S hS (representedSubspaceIso B S hS T Z).hom).obj
        (conormalModule B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ Z) ≅
      ((representedQuasicoherentSchemeEquivalence B S hS
            (representingObj B S hS T Z)).functor.obj
          (representedQuasicoherentSchemePullback B S hS (representingHom B S hS T Z)
            ⟨(Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
                (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
                  (representingHom B S hS T Z).left)).toSheafOfModules,
              letI := isClosedImmersion_schemeHom_representingHom B S hS T Z
              isQuasicoherent_definingIdealOfHom
                (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
                  (representingHom B S hS T Z).left)⟩)).obj :=
  (modulePullbackDefiningIdealSheafIsoConormalModule B S hS T Z).symm ≪≫
    (modulePullback B S hS
          (representedSpaceMap B S hS (representingHom B S hS T Z))).mapIso
        (definingIdealSheafIsoRepresented B S hS T Z) ≪≫
      representedQuasicoherentSchemePullbackIso B S hS (representingHom B S hS T Z)
        ⟨(Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              (representingHom B S hS T Z).left)).toSheafOfModules,
          letI := isClosedImmersion_schemeHom_representingHom B S hS T Z
          isQuasicoherent_definingIdealOfHom
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              (representingHom B S hS T Z).left)⟩

/-! ### Finite local freeness of the conormal module from the representing scheme -/

/-- The morphism of presheaves underlying `AlgebraicGeometry.Space.representedSubspaceIso` is an
isomorphism: it is the base-change projection of the representability square of the inclusion at
the identity, which `AlgebraicGeometry.Space.isIso_rep_fst_id` says is one. -/
theorem isIso_representedSubspaceIso_hom_hom :
    IsIso (representedSubspaceIso B S hS T Z).hom.hom :=
  isIso_rep_fst_id B S hS Z.1 Z.2

/-- **Finite local freeness of the conormal module of a closed subspace of a representable
algebraic space follows from finite local freeness on the representing scheme.**  If the Zariski
pullback, along the representing closed immersion of schemes, of the defining ideal sheaf of that
immersion is finite locally free in the sense of Stacks 01C6 (2), then the conormal module of
Stacks 04CN of `Z ⊆ yoneda.obj T` is finite locally free on the small étale site in the sense of
clause (2) of Stacks 03DL.

The property crosses from the Zariski site of the representing scheme to the small étale site of
the algebraic space it represents by
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_representedQuasicoherentSchemeEquivalence`, and
is carried onto the conormal module by
`AlgebraicGeometry.Space.conormalModuleIsoRepresentedQuasicoherent` and the insensitivity of
finite local freeness to the inverse image along an isomorphism. -/
theorem isFiniteLocallyFreeOnSite_conormalModule_representable
    (hflf : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((_root_.AlgebraicGeometry.Scheme.Modules.pullback
            (B.inclusion.map (representingHom B S hS T Z).left)).obj
        (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            (representingHom B S hS T Z).left)).toSheafOfModules)) :
    SheafOfModules.IsFiniteLocallyFreeOnSite
      (conormalModule B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ Z) := by
  let := isClosedImmersion_schemeHom_representingHom B S hS T Z
  let := isIso_representedSubspaceIso_hom_hom B S hS T Z
  refine (isFiniteLocallyFreeOnSite_modulePullback_iff B S hS
    (representedSubspaceIso B S hS T Z).hom (isEtale_of_isIso B S hS _)
    (isSurjective_of_isIso B S hS _)
    (conormalModule B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ Z)).2 ?_
  exact SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    (conormalModuleIsoRepresentedQuasicoherent B S hS T Z).symm
    (isFiniteLocallyFreeOnSite_representedQuasicoherentSchemeEquivalence B S hS _ _ _ hflf)

end AlgebraicGeometry.Space

end
