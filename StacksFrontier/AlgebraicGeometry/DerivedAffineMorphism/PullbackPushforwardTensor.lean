module

public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.DirectImageInDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaLocal
public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentPushforwardAdjoint
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pullback followed by direct image along an affine morphism

Let `f : X ⟶ S` be an affine morphism of schemes. [Stacks, Tag 08I9] asserts that

`Rf_* Lf^* E ≅ E ⊗^𝐋_{𝒪_S} f_*𝒪_X`

for every `E` in `D_QCoh(𝒪_S)`. This file proves the identity for `E` a quasi-coherent
`𝒪_S`-module placed in degree zero, with the **underived** tensor product on the right-hand
side, and in three unconditional forms. The general statement, for an arbitrary object of
`D_QCoh(𝒪_S)` and with the derived tensor product, is not proved here; it is proved in
`StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/AffineProjectionFormulaGeneralBase.lean`, as
`AlgebraicGeometry.AffineProjectionFormula.isIso_pullbackPushforwardTensorMap_unconditional`, so
each declaration below is a special case of a result the library holds. What each declaration
does and does not claim is recorded in the qualifier text of its Stacks attribute, and the two
restrictions that separate all of them from the source are listed under *What is restricted*
below.

The mathematical content is the ordinary projection formula for an affine morphism,
[Stacks, Tag 08I9]'s underived shadow: `Stacks.AlgebraicGeometry.ProjectionFormula` proves
[Stacks, Tag 0FZE], that

`f_*G ⊗_{𝒪_S} H ⟶ f_*(G ⊗_{𝒪_X} f^*H)`

is invertible for `f` affine and `G`, `H` quasi-coherent. Taking `G = 𝒪_X` and cancelling the
left unitor `𝒪_X ⊗_{𝒪_X} f^*H ≅ f^*H` turns this into `f_*𝒪_X ⊗_{𝒪_S} H ≅ f_*f^*H`, which is
`pushforwardStructureSheafTensorIso`. Passing to the derived category then costs nothing beyond
[Stacks, Tag 01XC]: `f` is affine and `f^*H` is quasi-coherent, so the ordinary direct image
`f_*f^*H` placed in degree zero already *is* `Rf_*((f^*H)[0])`, which is
`Stacks.AlgebraicGeometry.DerivedAffinePushforward.derivedPushforwardSingleIso`.

## Main definitions

* `pushforwardStructureSheafTensorIso`: `f_*𝒪_X ⊗_{𝒪_S} H ≅ f_*f^*H` for `f` affine and `H`
  quasi-coherent, with no hypothesis on the base. This is [Stacks, Tag 0FZE] at `G = 𝒪_X`.
* `derivedPushforwardPullbackTensorIso`: `Rf_*((f^*H)[0]) ≅ (f_*𝒪_X ⊗_{𝒪_S} H)[0]` in
  `D(𝒪_S)`, for `f` affine and `H` quasi-coherent. Unconditional.
* `derivedPullbackSingleIsoOfFlat`: `Lf^*(H[0]) ≅ (f^*H)[0]` for a flat `𝒪_S`-module `H` and an
  arbitrary morphism of schemes.
* `derivedPushforwardDerivedPullbackTensorIso`: `Rf_*Lf^*(H[0]) ≅ (f_*𝒪_X ⊗_{𝒪_S} H)[0]` with
  the genuine derived pullback `Lf^*` on the left, for `f` affine and `H` flat and
  quasi-coherent. Unconditional.
* `derivedPullbackSingleIsoOfExact`: the degree-zero comparison again, proved instead for an
  arbitrary `H` when `f^*` is exact.
* `derivedPushforwardDerivedPullbackTensorIsoOfExact`:
  `Rf_*Lf^*(H[0]) ≅ (f_*𝒪_X ⊗_{𝒪_S} H)[0]` for `f` affine with `f^*` exact and `H`
  quasi-coherent. Unconditional; flatness of `f` here replaces flatness of `H` there, so the
  two forms with the genuine `Lf^*` are not comparable.

## What is restricted

Two restrictions separate these statements from [Stacks, Tag 08I9] itself, and neither is hidden
inside a proof: each is visible in the statements above. No mathematical input is assumed.

*The right-hand tensor product is the ordinary one.* The source writes `E ⊗^𝐋_{𝒪_S} f_*𝒪_X`;
what appears here is `(f_*𝒪_X ⊗_{𝒪_S} H)[0]`, the ordinary tensor product of sheaves of modules
placed in degree zero. The two agree when `f_*𝒪_X` or `H` is flat and differ otherwise, so under
the hypotheses of `derivedPushforwardDerivedPullbackTensorIso`, where `H` is flat, and under
those of `derivedPushforwardDerivedPullbackTensorIsoOfExact`, where `f` is, the identity proved
is the source's; but that identification of the two sides is not carried out, the derived tensor
product of `Stacks.Duality.derivedTensor` occurring in no statement in this file.

*Only `E` concentrated in degree zero.* The source quantifies over all of `D_QCoh(𝒪_S)`. The
reduction of the general case to this one is the local-on-`S` argument of the source's proof
together with the affine case read off [Stacks, Tag 06Z0] and [Stacks, Tag 08DW]; that is carried
out in
`StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/AffineProjectionFormulaGeneralBase.lean`
and not here.

The canonical morphism of the source's proof — the adjoint of
`Lf^*(E ⊗^𝐋 Rf_*𝒪_X) ≅ Lf^*E ⊗^𝐋 Lf^*Rf_*𝒪_X ⟶ Lf^*E` — is likewise not the morphism
underlying these isomorphisms; the derived projection-formula map it is built from is
`Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap` ([Stacks, Tag 0B53]); its
invertibility ([Stacks, Tag 08EU]) is nowhere proved unconditionally in this library, and what
[Stacks, Tag 08I9] needs of it is invertibility at the source complex `𝒪_X[0]` for an arbitrary
`K`, which is
`Stacks.Cohomology.DerivedProjectionFormula.isIso_pullbackPushforwardTensorMap_iff`.

## Implementation notes

*The model of the derived category is the locally small one.* `Stacks.Duality.derivedPushforward`
and `Stacks.Duality.derivedPullback` resolve `HasDerivedCategory` to
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, at universe `u`, which is the model the
whole `D_QCoh` development of `Stacks.Duality` is written against; the statements here are
pinned to it rather than carrying a model binder, so that they compose with that development.
`Stacks.AlgebraicGeometry.DerivedAffinePushforward.derivedPushforwardSingleIso` leaves the model
free and is instantiated at `u`, where it describes `Stacks.Duality.derivedPushforward` — the two
functors are equal by `rfl`, `AlgebraicGeometry.pushforwardSheafOfModules` and
`AlgebraicGeometry.Scheme.Modules.pushforward` being the same functor under a type ascription.

*Quasi-coherence is an explicit argument, not an instance.* `AlgebraicGeometry.Scheme.Modules` is
not reducible, so instance search does not cross between `H.IsQuasicoherent` for `H : S.Modules`
and `SheafOfModules.IsQuasicoherent` over `S.ringCatSheaf` even though the two are definitionally
equal; this is the convention of `StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaLocal`
and is followed here. Where an instance is needed —
`derivedPushforwardSingleIso` takes `[F.IsQuasicoherent]` — the hypothesis is reintroduced with
`haveI`.

*The order of the tensor factors.* [Stacks, Tag 0FZE] produces the direct image as the left
factor, so these statements read `f_*𝒪_X ⊗_{𝒪_S} H` where the source reads
`E ⊗^𝐋_{𝒪_S} f_*𝒪_X`. The tensor product of sheaves of modules is symmetric, so this is the
same statement.

*Exactness of `f^*` in place of flatness.* `derivedPullbackSingleIsoOfExact` and
`derivedPushforwardDerivedPullbackTensorIsoOfExact` ask
`CategoryTheory.Limits.PreservesFiniteLimits (AlgebraicGeometry.Scheme.Modules.pullback f)`.
Inverse image is right exact for every morphism, so this is exactly flatness of `f`, and it is
the form in which `Stacks.Duality.derivedPullbackMapDerivedIso` consumes it. The companion
`PreservesFiniteColimits` hypothesis of that isomorphism is discharged unconditionally by
`AlgebraicGeometry.preservesFiniteColimits_modulesPullback`.

*The K-flat route is taken at a free model.* `derivedPullbackSingleIsoOfFlat` goes through
`Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat`, whose two `HasDerivedCategory` binders are
free, so it instantiates at the locally small model this file is pinned to;
`Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso` is the same isomorphism
but fixed at `HasDerivedCategory.standard`, and `HasDerivedCategory` carries the localized
category as data, so it does not transport here.

## References

* [Stacks Project, Tag 08I9](https://stacks.math.columbia.edu/tag/08I9)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.DerivedAffinePushforward

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The ordinary projection formula at the structure sheaf**: for an affine morphism of
schemes `f : X ⟶ S` and a quasi-coherent `𝒪_S`-module `H`,

`f_*𝒪_X ⊗_{𝒪_S} H ≅ f_*f^*H`.

There is no hypothesis on the base. This is [Stacks, Tag 0FZE] —
`Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaIsoOfQuasicoherent` — at the
quasi-coherent `𝒪_X`-module `G = 𝒪_X`, whose target `f_*(𝒪_X ⊗_{𝒪_X} f^*H)` is cancelled by the
left unitor of the tensor product sheaf. -/
@[sga "3 VIB 11.1"]
def pushforwardStructureSheafTensorIso [IsAffineHom f] (H : S.Modules)
    (hH : H.IsQuasicoherent) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((S.toRingedSpace)).presheaf, ((S.toRingedSpace)).IsSheaf⟩))).obj
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf : X.Modules), H) ≅
      (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj H) :=
  Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaIsoOfQuasicoherent f
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) H
      (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X) hH ≪≫
    (Scheme.Modules.pushforward f).mapIso
      (Stacks.RingedSpace.tensorSheafUnitLeftIso X.toRingedSpace
        ((Scheme.Modules.pullback f).obj H))

/-- **[Stacks, Tag 08I9] for `E` a quasi-coherent module in degree zero, with the underived
inverse image and tensor product**: for an affine morphism of schemes `f : X ⟶ S` and a
quasi-coherent `𝒪_S`-module `H`,

`Rf_*((f^*H)[0]) ≅ (f_*𝒪_X ⊗_{𝒪_S} H)[0]`

in `D(𝒪_S)`. Unconditional.

The source states `Rf_*Lf^*E ≅ E ⊗^𝐋_{𝒪_S} f_*𝒪_X`; here both derived functors on the
right-hand side of that identity are replaced by their underived counterparts `f^*` and `⊗`.
See the module documentation for what that costs. The proof is
`pushforwardStructureSheafTensorIso` followed by [Stacks, Tag 01XC] in the form
`derivedPushforwardSingleIso`: `f^*H` is quasi-coherent and `f` is affine, so the ordinary direct
image of `f^*H` in degree zero is already its derived direct image. -/
@[stacks 08I9 "a SPECIAL CASE of the general statement, which is proved — the tag is closed by \
AlgebraicGeometry.AffineProjectionFormula.isIso_pullbackPushforwardTensorMap_unconditional. The \
degree-zero clause: Rf_*((f^*H)[0]) ≅ (f_*𝒪_X ⊗_{𝒪_S} H)[0] for H a quasi-coherent 𝒪_S-module, \
with the underived f^* and ⊗ in place of the general statement's Lf^* and ⊗ᴸ and E restricted to \
a module in degree zero"]
def derivedPushforwardPullbackTensorIso [IsAffineHom f] (H : S.Modules)
    (hH : H.IsQuasicoherent) :
    (Stacks.Duality.derivedPushforward f).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj ((Scheme.Modules.pullback f).obj H)) ≅
      (DerivedCategory.singleFunctor S.Modules 0).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((S.toRingedSpace)).presheaf, ((S.toRingedSpace)).IsSheaf⟩))).obj
          ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf : X.Modules),
            H)) :=
  haveI : ((Scheme.Modules.pullback f).obj H).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback f H hH
  (derivedPushforwardSingleIso.{u} f ((Scheme.Modules.pullback f).obj H)).symm ≪≫
    (DerivedCategory.singleFunctor S.Modules 0).mapIso
      (pushforwardStructureSheafTensorIso f H hH).symm

/-- **The derived pullback of a flat module placed in degree zero**: `Lf^*(H[0]) ≅ (f^*H)[0]`
for an arbitrary morphism of schemes `f : X ⟶ S` and a flat `𝒪_S`-module `H`.

A flat module placed in a single degree is K-flat ([Stacks, Tag 06YQ]), and on a K-flat complex
the canonical comparison `Lf^* ⟶ f^*` is invertible ([Stacks, Tag 06YJ]); no hypothesis on `f`
is needed, and no higher `Tor` of `H` along `f` intervenes. -/
def derivedPullbackSingleIsoOfFlat (H : S.Modules)
    (hHflat : SheafOfModules.IsFlat.{u, u, u, u} (O := S.toRingedSpace.sheaf) H) :
    (Stacks.Duality.derivedPullback f).obj
        ((DerivedCategory.singleFunctor S.Modules 0).obj H) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj ((Scheme.Modules.pullback f).obj H) :=
  (Stacks.Duality.derivedPullback f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ S.Modules 0).app H) ≪≫
    Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat f.toLRSHom.toShHom
      ((CochainComplex.singleFunctor S.Modules 0).obj H)
      (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat
        S.toRingedSpace.sheaf H hHflat 0) ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (modulePullback f.toLRSHom.toShHom) (ComplexShape.up ℤ) 0).app H) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app
      ((Scheme.Modules.pullback f).obj H)).symm

/-- **[Stacks, Tag 08I9] for `E` a flat quasi-coherent module in degree zero, with the genuine
derived pullback**: for an affine morphism of schemes `f : X ⟶ S` and a flat quasi-coherent
`𝒪_S`-module `H`,

`Rf_*Lf^*(H[0]) ≅ (f_*𝒪_X ⊗_{𝒪_S} H)[0]`,

with nothing assumed beyond those restrictions on `f` and `H`. Flatness of `H` makes `H[0]`
K-flat, so the degree-zero comparison `Lf^*(H[0]) ≅ (f^*H)[0]` is
`derivedPullbackSingleIsoOfFlat`; the tensor product on the right-hand side is still the
underived one. -/
@[stacks 08I9 "a SPECIAL CASE of the general statement, which is proved — the tag is closed by \
AlgebraicGeometry.AffineProjectionFormula.isIso_pullbackPushforwardTensorMap_unconditional. \
E = H[0] for f affine and H a flat quasi-coherent 𝒪_S-module, with the genuine Lf^* and nothing \
carried: Rf_*Lf^*(H[0]) ≅ (f_*𝒪_X ⊗_{𝒪_S} H)[0]; the right-hand tensor product is the underived \
⊗, not ⊗ᴸ, and E is restricted to a module in degree zero"]
def derivedPushforwardDerivedPullbackTensorIso [IsAffineHom f] (H : S.Modules)
    (hH : H.IsQuasicoherent)
    (hHflat : SheafOfModules.IsFlat.{u, u, u, u} (O := S.toRingedSpace.sheaf) H) :
    (Stacks.Duality.derivedPushforward f).obj
        ((Stacks.Duality.derivedPullback f).obj
          ((DerivedCategory.singleFunctor S.Modules 0).obj H)) ≅
      (DerivedCategory.singleFunctor S.Modules 0).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((S.toRingedSpace)).presheaf, ((S.toRingedSpace)).IsSheaf⟩))).obj
          ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf : X.Modules),
            H)) :=
  (Stacks.Duality.derivedPushforward f).mapIso (derivedPullbackSingleIsoOfFlat f H hHflat) ≪≫
    derivedPushforwardPullbackTensorIso f H hH

/-- **The derived pullback of a module in degree zero, when inverse image is exact**:
`Lf^*(H[0]) ≅ (f^*H)[0]` for a morphism of schemes `f` along which `f^*` preserves finite
limits, that is for `f` flat.

Inverse image is right exact for every morphism, so the hypothesis is exactly flatness; the
companion `PreservesFiniteColimits` is unconditional. The proof identifies `Lf^*` with the
degreewise inverse image (`Stacks.Duality.derivedPullbackMapDerivedIso`) and then commutes the
degreewise functor past the degree-zero complex. -/
def derivedPullbackSingleIsoOfExact [PreservesFiniteLimits (Scheme.Modules.pullback f)]
    (H : S.Modules) :
    (Stacks.Duality.derivedPullback f).obj
        ((DerivedCategory.singleFunctor S.Modules 0).obj H) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj ((Scheme.Modules.pullback f).obj H) :=
  haveI : PreservesFiniteColimits (Scheme.Modules.pullback f) :=
    AlgebraicGeometry.preservesFiniteColimits_modulesPullback f
  (Stacks.Duality.derivedPullbackMapDerivedIso f).app
      ((DerivedCategory.singleFunctor S.Modules 0).obj H) ≪≫
    ((Scheme.Modules.pullback f).mapDerivedCategorySingleFunctor 0).app H

/-- **[Stacks, Tag 08I9] for a flat affine morphism and `E` a quasi-coherent module in degree
zero**: for `f : X ⟶ S` affine with `f^*` exact and `H` a quasi-coherent `𝒪_S`-module,

`Rf_*Lf^*(H[0]) ≅ (f_*𝒪_X ⊗_{𝒪_S} H)[0]`

in `D(𝒪_S)`, with no hypothesis carried. Flatness of `f` replaces the flatness of `H` asked by
`derivedPushforwardDerivedPullbackTensorIso`: it supplies the degree-zero comparison
`Lf^*(H[0]) ≅ (f^*H)[0]` through `derivedPullbackSingleIsoOfExact` instead.

Both sides are the source's, except that the tensor product on the right is the ordinary one
rather than `⊗^𝐋`; for `f` flat the two agree, but that identification is not proved here. -/
@[stacks 08I9 "a SPECIAL CASE of the general statement, which is proved — the tag is closed by \
AlgebraicGeometry.AffineProjectionFormula.isIso_pullbackPushforwardTensorMap_unconditional. \
E = H[0] for f affine with f^* exact (f flat) and H quasi-coherent, with the genuine Rf_* and \
Lf^* and nothing carried: Rf_*Lf^*(H[0]) ≅ (f_*𝒪_X ⊗_{𝒪_S} H)[0]; the right-hand tensor product \
is the underived ⊗, not ⊗ᴸ, and E is restricted to a module in degree zero"]
def derivedPushforwardDerivedPullbackTensorIsoOfExact [IsAffineHom f]
    [PreservesFiniteLimits (Scheme.Modules.pullback f)] (H : S.Modules)
    (hH : H.IsQuasicoherent) :
    (Stacks.Duality.derivedPushforward f).obj
        ((Stacks.Duality.derivedPullback f).obj
          ((DerivedCategory.singleFunctor S.Modules 0).obj H)) ≅
      (DerivedCategory.singleFunctor S.Modules 0).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((S.toRingedSpace)).presheaf, ((S.toRingedSpace)).IsSheaf⟩))).obj
          ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf : X.Modules),
            H)) :=
  (Stacks.Duality.derivedPushforward f).mapIso (derivedPullbackSingleIsoOfExact f H) ≪≫
    derivedPushforwardPullbackTensorIso f H hH

end Stacks.AlgebraicGeometry.DerivedAffinePushforward

end
