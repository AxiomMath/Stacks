module

public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaMap.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaSections
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.ClosedImmersionPushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The ordinary projection formula for a closed embedding of ringed spaces

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, `G` a sheaf of `𝒪_X`-modules and
`H` a sheaf of `𝒪_Y`-modules.  `Stacks.ProjectionFormula.projectionFormulaMap'` is the canonical
morphism

`f_*G ⊗_{𝒪_Y} H ⟶ f_*(G ⊗_{𝒪_X} f^*H)`,

the adjoint transpose of the pullback-tensor comparison of [Stacks, Tag 01CD] followed by the
counit of `f^* ⊣ f_*` in the left tensor factor.  This file proves that it is an **isomorphism**
whenever `f` is a homeomorphism onto a closed subset, for *arbitrary* `G` and `H`.  That is the
first step of the source's proof of [Stacks, Tag 0B55], and the step where the mathematics of
that tag sits: the source verifies it on stalks, and so does the proof below.

## Main results

* `Stacks.ProjectionFormula.projectionFormulaMap'_unit_tmul`: **the morphism on local sections.**
  On an open `U` of `Y`, a section `m` of `f_*G` over `U` — equivalently of `G` over `f⁻¹U` — and
  a section `k` of `H` over `U`, it carries the sheafification-unit image of `m ⊗ k` to the
  sheafification-unit image over `f⁻¹U` of `m ⊗ η k`, where `η` is the unit of `f^* ⊣ f_*`.  No
  hypothesis on `f`.
* `Stacks.ClosedEmbeddingProjectionFormula.isZero_stalk_source_of_notMemRange` and
  `Stacks.ClosedEmbeddingProjectionFormula.isZero_stalk_target_of_notMemRange`: for `f` a
  homeomorphism onto a closed subset, both the source and the target of the morphism have zero
  stalk at every point outside the image of `f`, so
  `Stacks.ClosedEmbeddingProjectionFormula.isIso_stalkMap_projectionFormulaMap'_of_notMemRange`:
  **the morphism is invertible on every stalk outside the image.**
* `Stacks.ClosedEmbeddingProjectionFormula.stalkPushforwardEquiv`: for an *inducing* `f` the
  stalk of `f_*E` at `f x` is the stalk of `E` at `x`, as a module over `𝒪_{Y, f x}` acting
  through the germ map — [Stacks, Tag 00AE] read on the image, at the module structures of
  [Stacks, Tag 01CB].
* `Stacks.ClosedEmbeddingProjectionFormula.isIso_stalkMap_projectionFormulaMap'_of_memRange`:
  **the morphism is invertible on the stalk at `f x`**, for an inducing `f`.
* `Stacks.ClosedEmbeddingProjectionFormula.isIso_projectionFormulaMap'_of_isClosedEmbedding`:
  **the morphism is an isomorphism** for a homeomorphism onto a closed subset and arbitrary
  `G`, `H`.

## The stalk over a point of the image

Writing `R = 𝒪_{Y, f x}` and `S = 𝒪_{X, x}`, the two stalks are

`(f_*G ⊗_{𝒪_Y} H)_{f x} ≅ (f_*G)_{f x} ⊗_R H_{f x} ≅ G_x ⊗_R H_{f x}`

and

`(f_*(G ⊗_{𝒪_X} f^*H))_{f x} ≅ (G ⊗_{𝒪_X} f^*H)_x ≅ G_x ⊗_S (f^*H)_x ≅ G_x ⊗_S (S ⊗_R H_{f x})`,

the first isomorphism of each line being `stalkPushforwardEquiv`, the second
[Stacks, Tag 01CB] (`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`) and the third
[Stacks, Tag 0098] (`Stacks.RingedSpace.pullbackStalkEquiv`).  The two are identified by
`TensorProduct.AlgebraTensorModule.cancelBaseChange`, and `tensorProjectionMap_bijective` says
that any `R`-linear map between them which carries `m ⊗ n` to `m ⊗ (1 ⊗ n)` is therefore
bijective.  That the stalk map of the morphism is such a map is the sections formula
`projectionFormulaMap'_unit_tmul` read on germs.

Note that the counit `f^*f_*G ⟶ G` is **not** invertible for a bare closed embedding, so the
formal argument available under a stronger hypothesis is unavailable here; that is exactly why
the source argues on stalks.  The library's
`Stacks.AffineProjectionFormula.isIso_projectionFormulaMap` assumes a
`ClosedQuotientMorphismOfRingedSpaces`, that is a closed embedding **together with** local
surjectivity of `𝒪_Y ⟶ f_*𝒪_X`, which does make the counit invertible; nothing below uses it.

## What of [Stacks, Tag 0B55] is not here

The **derived** statement.  [Stacks, Tag 0B55] asserts that the derived projection-formula map
of [Stacks, Tag 0B53] is invertible for arbitrary `E ∈ D(𝒪_X)` and `K ∈ D(𝒪_Y)`; deducing that
from the ordinary statement proved here needs the reduction to K-flat resolutions and the
compatibility of `f_*` with the relevant colimits.  That is **not** proved here, and nothing
below mentions the derived map.

## Implementation notes

*The sections formula is a transcription.*  `projectionFormulaMap'_app_eq` splits the adjoint
transpose by `rfl`; the three rewrites that follow are the canonicality clause of
[Stacks, Tag 01CD] (`Stacks.RingedSpace.comparison_homEquiv_unit_tmul`), the effect of a tensor
of two morphisms on a pure tensor (`Stacks.RingedSpace.tensorSheaf_map_unit_tmul`), and the
triangle identity read on sections (`Stacks.RingedSpace.counit_pullbackUnit`).  They are applied
through `congrArg` and `Eq.trans` rather than by `rw`, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/Duality/ProjectionFormulaSections.lean`: the element being
rewritten sits in a type spelled through `restrictScalars` and a motive built against the
syntactic form does not typecheck.

*Why the source stalk vanishes off the image.*  `(f_*G)_y` vanishes off the closed image by
[Stacks, Tag 00AE], and the stalk of a tensor product is the tensor product of the stalks by
[Stacks, Tag 01CB]; a tensor product with a trivial left factor is trivial.  The vanishing is
recorded as `IsZero` of the `𝒪_{Y,y}`-module stalk, which is the form
`Stacks.ClosedImmersion.isZero_stalk_modulePushforward_of_notMemRange` supplies, and converted to
`Subsingleton` of the abelian stalk where the stalkwise criterion needs it.

*Why the pushforward stalk is rebuilt here.*  `Stacks.ClosedImmersion.stalkPushforwardModuleMap`
already carries the comparison `(f_*E)_{f x} ⟶ E_x` with its linearity, but over the
`RingCat`-valued stalk of the structure sheaf, whereas the Tag 01CB and Tag 0098 toolkit used
above is stated over the `CommRingCat`-valued one; `TensorProduct.congr` on the left factor needs
`𝒪_{Y, f x}`-linearity across that gap.  `stalkPushforwardEquiv` therefore re-proves the one
`map_smul` on germs — a scalar and a germ are represented over a common open, the scalar action
on sections of `f_*E` is the action of `𝒪_X(f⁻¹U)` through `f^♯` by `rfl`, and the two germ
computations are matched by `AlgebraicGeometry.PresheafedSpace.stalkMap_germ` — directly at the
Tag 01CB module structures, which is cheaper than bridging the two stalk rings.

*Why every stalk statement is written at `structureSheafRing`.*  As in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorComparisonIso.lean`: typeclass
inference finds `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule` only at that spelling
of the structure sheaf.  The two spellings are `rfl`-equal, and `atX`, `atY`, `pushforwardAt`
and `projectionFormulaMapAt` are reducible retypings across that equality.

## References

* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction Stacks.RingedSpace _root_.PresheafOfModules
open scoped TensorProduct CategoryTheory.Prod

universe u

noncomputable section

namespace Stacks.ProjectionFormula

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (G : SheafOfModules.{u} (structureRingSheaf X))
  (H : SheafOfModules.{u} (structureRingSheaf Y))

/-! ### The morphism on local sections -/

/-- The projection-formula morphism of a morphism of ringed spaces, split on local sections into
the adjoint transpose of the pullback-tensor comparison of [Stacks, Tag 01CD] followed by the
tensor of the counit with the identity.  The split is
`CategoryTheory.Adjunction.homEquiv_naturality_right`, which on sections is a reduction: the
pushforward of a composite is the composite of the pushforwards sectionwise, by definition. -/
private lemma projectionFormulaMap'_app_eq (U : (Opens Y.carrier)ᵒᵖ)
    (m : ((pushforwardFunctor f).obj G).val.obj U) (k : H.val.obj U) :
    Hom.app (projectionFormulaMap' f G H).val U
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf (Y))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf (Y)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := (Y).presheaf)
            (((pushforwardFunctor f).obj G)).val (H).val)) U (m ⊗ₜ k)) =
      Hom.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(X).presheaf, (X).IsSheaf⟩))).map
          (((pullbackAdjunction f).counit.app G, 𝟙 ((pullbackFunctor f).obj H)) :
            ((((pullbackFunctor f).obj ((pushforwardFunctor f).obj G)),
              ((pullbackFunctor f).obj H)) : _ × _) ⟶ (G, (pullbackFunctor f).obj H))).val
        ((opensMap f).op.obj U)
        (Hom.app ((pullbackAdjunction f).homEquiv _ _
            (comparison f ((pushforwardFunctor f).obj G) H)).val U
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.RingedSpace.structureRingSheaf (Y))
              (𝟙 (Stacks.RingedSpace.structureRingSheaf (Y)).obj)).unit.app
              (PresheafOfModules.tensorObj (O := (Y).presheaf)
              (((pushforwardFunctor f).obj G)).val (H).val)) U (m ⊗ₜ k))) := rfl

/-- **The projection-formula morphism of a morphism of ringed spaces on local sections.**  Let
`U` be an open of `Y`, `m` a section of `G` over `f⁻¹U` — equivalently, of `f_*G` over `U` — and
`k` a section of `H` over `U`.  Then

`f_*G ⊗_{𝒪_Y} H ⟶ f_*(G ⊗_{𝒪_X} f^*H)`

carries the sheafification-unit image of the pure tensor `m ⊗ k` to the sheafification-unit image
over `f⁻¹U` of the pure tensor of `m` with the image of `k` under the unit of `f^* ⊣ f_*`.  There
is no hypothesis on `f`.

This is the canonicality clause of the morphism: it is `m ⊗ k ↦ m ⊗ f^♯k` and nothing else.  The
same computation for a morphism of *schemes*, and for a different `projectionFormulaMap`
declaration, is `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_unit_tmul`; the
proof below is that one, which uses nothing about schemes. -/
lemma projectionFormulaMap'_unit_tmul (U : (Opens Y.carrier)ᵒᵖ)
    (m : ((pushforwardFunctor f).obj G).val.obj U) (k : H.val.obj U) :
    Hom.app (projectionFormulaMap' f G H).val U
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf (Y))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf (Y)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := (Y).presheaf)
            (((pushforwardFunctor f).obj G)).val (H).val)) U (m ⊗ₜ k)) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf (X))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf (X)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (X).presheaf) (G).val
          (((pullbackFunctor f).obj H)).val))
        ((opensMap f).op.obj U) (m ⊗ₜ pullbackUnit f H U k) := by
  refine (projectionFormulaMap'_app_eq f G H U m k).trans ?_
  refine Eq.trans (congrArg
    (fun z => Hom.app
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(X).presheaf, (X).IsSheaf⟩))).map
        (((pullbackAdjunction f).counit.app G, 𝟙 ((pullbackFunctor f).obj H)) :
          ((((pullbackFunctor f).obj ((pushforwardFunctor f).obj G)),
            ((pullbackFunctor f).obj H)) : _ × _) ⟶ (G, (pullbackFunctor f).obj H))).val
      ((opensMap f).op.obj U) z)
    (comparison_homEquiv_unit_tmul f ((pushforwardFunctor f).obj G) H U m k)) ?_
  refine Eq.trans (tensorSheaf_map_unit_tmul X
      ((pullbackAdjunction f).counit.app G) (𝟙 ((pullbackFunctor f).obj H))
      ((opensMap f).op.obj U)
      (pullbackUnit f ((pushforwardFunctor f).obj G) U m)
      (pullbackUnit f H U k)) ?_
  exact congrArg (fun z => Hom.app
      ((PresheafOfModules.sheafificationAdjunction (R := Stacks.RingedSpace.structureRingSheaf (X))
      (𝟙 (Stacks.RingedSpace.structureRingSheaf (X)).obj)).unit.app (PresheafOfModules.tensorObj
      (O := (X).presheaf) (G).val (((pullbackFunctor f).obj H)).val))
      ((opensMap f).op.obj U) (z ⊗ₜ pullbackUnit f H U k))
    (counit_pullbackUnit f G U m)

end Stacks.ProjectionFormula

namespace Stacks.ClosedEmbeddingProjectionFormula

open Stacks.ProjectionFormula

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (G : SheafOfModules.{u} (structureRingSheaf X))
  (H : SheafOfModules.{u} (structureRingSheaf Y))

/-! ### Both stalks vanish off the image -/

/-- A tensor product with a trivial left factor is trivial. -/
private lemma tensorProduct_subsingleton_of_subsingleton_left {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Subsingleton M] :
    Subsingleton (M ⊗[R] N) := by
  have h : ∀ t : M ⊗[R] N, t = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rfl
    | add p q hp hq => rw [hp, hq, add_zero]
    | tmul a b => rw [Subsingleton.elim a 0, TensorProduct.zero_tmul]
  exact ⟨fun a b => (h a).trans (h b).symm⟩

/-- A sheaf of `𝒪_Y`-modules retyped over
`structureSheafRing`, a reducible retyping across
the `rfl`-equality of the two spellings of the structure sheaf whose only purpose is that
typeclass inference then finds
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule` on its stalks. -/
private noncomputable abbrev atY (M : SheafOfModules.{u} (structureRingSheaf Y)) :
    SheafOfModules.{u} (structureSheafRing Y) := M

/-- **The source of the projection-formula morphism has zero stalk off the image.**  For `f` a
homeomorphism onto a closed subset and `y` outside the image, the stalk of the abelian sheaf
underlying `f_*G ⊗_{𝒪_Y} H` at `y` is a zero object: the stalk `(f_*G)_y` vanishes by
[Stacks, Tag 00AE] and the stalk of a tensor product is the tensor product of the stalks by
[Stacks, Tag 01CB], so a trivial left factor makes the whole stalk trivial. -/
theorem isZero_stalk_source_of_notMemRange
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base)) (y : Y.carrier)
    (hy : y ∉ Set.range (ConcreteCategory.hom f.hom.base)) :
    IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).obj
      ((ExtensionByZeroModules.toAb (structureRingSheaf Y)).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(Y).presheaf, (Y).IsSheaf⟩))).obj ((pushforwardFunctor f).obj G, H)))) := by
  have hpush : Subsingleton ↑(Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y
      (atY ((pushforwardFunctor f).obj G)).val y) :=
    ModuleCat.subsingleton_of_isZero
      (Stacks.ClosedImmersion.isZero_stalk_modulePushforward_of_notMemRange f hf G y hy)
  have hten : Subsingleton
      (TensorProduct ↑(Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y y)
        ↑(Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y
          (atY ((pushforwardFunctor f).obj G)).val y)
        ↑(Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y (atY H).val y)) :=
    @tensorProduct_subsingleton_of_subsingleton_left _ _ _ _ _ _ _ _ hpush
  have hsrc : Subsingleton ↑((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).obj
      ((ExtensionByZeroModules.toAb (structureRingSheaf Y)).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(Y).presheaf, (Y).IsSheaf⟩))).obj ((pushforwardFunctor f).obj G, H)))) :=
    @Equiv.subsingleton _ _
      (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso Y y
        (atY ((pushforwardFunctor f).obj G)) (atY H)).toEquiv hten
  exact @AddCommGrpCat.isZero_of_subsingleton _ hsrc

/-- **The target of the projection-formula morphism has zero stalk off the image.**  For `f` a
homeomorphism onto a closed subset and `y` outside the image, the stalk of the abelian sheaf
underlying `f_*(G ⊗_{𝒪_X} f^*H)` at `y` is a zero object.  This is [Stacks, Tag 00AE],
`Stacks.ClosedImmersion.isZero_stalk_modulePushforward_of_notMemRange`, read at the module
`G ⊗_{𝒪_X} f^*H`. -/
theorem isZero_stalk_target_of_notMemRange
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base)) (y : Y.carrier)
    (hy : y ∉ Set.range (ConcreteCategory.hom f.hom.base)) :
    IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).obj
      ((ExtensionByZeroModules.toAb (structureRingSheaf Y)).obj
        ((pushforwardFunctor f).obj
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(X).presheaf, (X).IsSheaf⟩))).obj (G, (pullbackFunctor f).obj H))))) := by
  have htgt : Subsingleton ↑((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).obj
      ((ExtensionByZeroModules.toAb (structureRingSheaf Y)).obj
        ((pushforwardFunctor f).obj
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(X).presheaf, (X).IsSheaf⟩))).obj (G, (pullbackFunctor f).obj H))))) :=
    ModuleCat.subsingleton_of_isZero
      (Stacks.ClosedImmersion.isZero_stalk_modulePushforward_of_notMemRange f hf
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(X).presheaf, (X).IsSheaf⟩))).obj (G, (pullbackFunctor f).obj H)) y hy)
  exact @AddCommGrpCat.isZero_of_subsingleton _ htgt

/-- **Off the closed image the projection-formula morphism is invertible on stalks.**  This is the
first half of the stalk verification in the source's proof of [Stacks, Tag 0B55]: for `y` outside
the image of a homeomorphism onto a closed subset both stalks vanish, by
`isZero_stalk_source_of_notMemRange` and `isZero_stalk_target_of_notMemRange`, and any morphism
between zero objects is invertible.

The other half, the stalk over a point of the image, is
`isIso_stalkMap_projectionFormulaMap'_of_memRange`; together the two give
`isIso_projectionFormulaMap'_of_isClosedEmbedding`. -/
@[stacks 0B55 "the stalk computation off the closed image: both stalks vanish there"]
theorem isIso_stalkMap_projectionFormulaMap'_of_notMemRange
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base)) (y : Y.carrier)
    (hy : y ∉ Set.range (ConcreteCategory.hom f.hom.base)) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      ((ExtensionByZeroModules.toAb (structureRingSheaf Y)).map
        (projectionFormulaMap' f G H))) := by
  have hs := isZero_stalk_source_of_notMemRange f G H hf y hy
  have ht := isZero_stalk_target_of_notMemRange f G H hf y hy
  rw [hs.eq_of_src ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
    ((ExtensionByZeroModules.toAb (structureRingSheaf Y)).map (projectionFormulaMap' f G H)))
    (hs.iso ht).hom]
  exact (hs.iso ht).isIso_hom

/-! ### The stalk over a point of the image -/

section InImage

open Stacks.SheafOfModules.TensorStalkRingedSpace

/-- A sheaf of `𝒪_X`-modules retyped over
`structureSheafRing`, the companion of `atY` on the
source of `f`; see the module documentation for why the retyping is there. -/
private noncomputable abbrev atX (M : SheafOfModules.{u} (structureRingSheaf X)) :
    SheafOfModules.{u} (structureSheafRing X) := M

/-- The pushforward `f_*E`, retyped over
`structureSheafRing`.  A reducible retyping across
the `rfl`-equality of the two spellings of the structure sheaf, so that typeclass inference
finds `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule` on its stalks.  It is not
`private` because it appears in the statements below, which are `public`. -/
noncomputable abbrev pushforwardAt (E : SheafOfModules.{u} (structureSheafRing X)) :
    SheafOfModules.{u} (structureSheafRing Y) :=
  (pushforwardFunctor f).obj E

variable (E : SheafOfModules.{u} (structureSheafRing X)) (x : X.carrier)

/-- **The comparison `(f_*E)_{f x} ⟶ E_x` on abelian stalks**, Mathlib's
`TopCat.Presheaf.stalkPushforward` of the underlying presheaf of abelian groups.  The underlying
presheaf of `f_*E` *is* the topological pushforward of the underlying presheaf of `E`, so no
transport is needed to state this. -/
noncomputable abbrev stalkPushforwardHom :
    grpStalk Y (pushforwardAt f E).val (f.hom.base x) ⟶ grpStalk X E.val x :=
  TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base E.val.presheaf x

/-- The comparison carries the germ at `f x` of a section of `f_*E` over `U` to the germ at `x`
of the same section, read over `f⁻¹U`. -/
lemma stalkPushforwardHom_germ (U : Opens Y.carrier) (hU : f.hom.base x ∈ U)
    (m : (pushforwardAt f E).val.obj (op U)) :
    (stalkPushforwardHom f E x).hom
        (grpGerm Y (pushforwardAt f E).val (f.hom.base x) U hU m) =
      grpGerm X E.val x ((opensMap f).obj U) hU m :=
  TopCat.Presheaf.stalkPushforward_germ_apply AddCommGrpCat.{u} f.hom.base E.val.presheaf U x hU m

/-- **The germ map commutes with the map on structure-sheaf stalks.**  The germ at `x` of the
image under `f^♯` of a section `r` of `𝒪_Y` over `U` is the image of the germ of `r` at `f x`
under `AlgebraicGeometry.PresheafedSpace.Hom.stalkMap`.  This is
`AlgebraicGeometry.PresheafedSpace.stalkMap_germ` read on an element. -/
lemma stalkMap_ringGerm (U : Opens Y.carrier) (hU : f.hom.base x ∈ U)
    (r : Y.presheaf.obj (op U)) :
    (f.hom.stalkMap x).hom (ringGerm Y (f.hom.base x) U hU r) =
      ringGerm X x ((opensMap f).obj U) hU ((f.hom.c.app (op U)).hom r) :=
  congrArg (fun q ↦ (ConcreteCategory.hom q) r)
    (AlgebraicGeometry.PresheafedSpace.stalkMap_germ (C := CommRingCat.{u}) f.hom U x hU)

variable (hf : Topology.IsInducing (ConcreteCategory.hom f.hom.base))

/-- **The stalk of a pushforward on the image**, [Stacks, Tag 00AE] read on the image: for `f`
with inducing underlying map, the stalk of `f_*E` at `f x` is the stalk of `E` at `x`, as a
module over `𝒪_{Y, f x}` acting on the latter through
`AlgebraicGeometry.PresheafedSpace.Hom.stalkMap`.

The underlying additive bijection is Mathlib's `TopCat.Presheaf.stalkPushforward`, invertible by
`TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing`.  The content is the
`map_smul'` field, and it is stated and proved at the module structures of [Stacks, Tag 01CB] so
that `TensorProduct.congr` can be applied to it; see the module documentation. -/
@[ega "0 3.4.5" "special case"]
noncomputable def stalkPushforwardEquiv :
    letI : Module ↑(ringStalk Y (f.hom.base x)) ↑(grpStalk X E.val x) :=
      Module.compHom _ (f.hom.stalkMap x).hom
    ↑(grpStalk Y (pushforwardAt f E).val (f.hom.base x)) ≃ₗ[↑(ringStalk Y (f.hom.base x))]
      ↑(grpStalk X E.val x) := by
  let _ : Module ↑(ringStalk Y (f.hom.base x)) ↑(grpStalk X E.val x) :=
    Module.compHom _ (f.hom.stalkMap x).hom
  have hiso : IsIso (stalkPushforwardHom f E x) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat.{u} hf E.val.presheaf x
  let eAdd := AddEquiv.ofBijective (ConcreteCategory.hom (stalkPushforwardHom f E x))
    (ConcreteCategory.bijective_of_isIso (stalkPushforwardHom f E x))
  refine { toFun := ConcreteCategory.hom (stalkPushforwardHom f E x)
           invFun := eAdd.symm
           left_inv := eAdd.left_inv
           right_inv := eAdd.right_inv
           map_add' := eAdd.map_add
           map_smul' := ?_ }
  intro r m
  obtain ⟨U₁, hU₁, r₁, hr₁⟩ := Y.presheaf.exists_germ_eq r
  obtain ⟨U₂, hU₂, m₂, hm₂⟩ :=
    Stacks.SheafOfModules.exists_grpGerm_eq Y (pushforwardAt f E).val (f.hom.base x) m
  set U : Opens Y.carrier := U₁ ⊓ U₂ with hUdef
  have hxU : f.hom.base x ∈ U := ⟨hU₁, hU₂⟩
  set rU : Y.presheaf.obj (op U) :=
    (Y.presheaf.map (homOfLE (show U ≤ U₁ from inf_le_left)).op).hom r₁ with hrUdef
  set mU : (pushforwardAt f E).val.obj (op U) :=
    ((pushforwardAt f E).val.map (homOfLE (show U ≤ U₂ from inf_le_right)).op).hom m₂ with hmUdef
  have hr : ringGerm Y (f.hom.base x) U hxU rU = r := by
    rw [hrUdef]
    exact (TopCat.Presheaf.germ_res_apply Y.presheaf
      (homOfLE (show U ≤ U₁ from inf_le_left)) (f.hom.base x) hxU r₁).trans hr₁
  have hm : grpGerm Y (pushforwardAt f E).val (f.hom.base x) U hxU mU = m := by
    rw [hmUdef]
    exact (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u})
      (pushforwardAt f E).val.presheaf (homOfLE (show U ≤ U₂ from inf_le_right))
      (f.hom.base x) hxU m₂).trans hm₂
  rw [← hr, ← hm, ← Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul Y
    (pushforwardAt f E).val (f.hom.base x) U hxU rU mU]
  change (ConcreteCategory.hom (stalkPushforwardHom f E x))
      (grpGerm Y (pushforwardAt f E).val (f.hom.base x) U hxU (rU • mU)) = _
  rw [stalkPushforwardHom_germ]
  change grpGerm X E.val x ((opensMap f).obj U) hxU
      ((f.hom.c.app (op U)).hom rU • (show E.val.obj (op ((opensMap f).obj U)) from mU)) = _
  rw [Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul X E.val x
      ((opensMap f).obj U) hxU ((f.hom.c.app (op U)).hom rU) mU,
    ← stalkMap_ringGerm f x U hxU rU]
  change _ = (f.hom.stalkMap x).hom (ringGerm Y (f.hom.base x) U hxU rU) •
    (ConcreteCategory.hom (stalkPushforwardHom f E x))
      (grpGerm Y (pushforwardAt f E).val (f.hom.base x) U hxU mU)
  rw [stalkPushforwardHom_germ]

/-- `stalkPushforwardEquiv` on a germ: it is `stalkPushforwardHom_germ`, since the equivalence is
built on that map. -/
lemma stalkPushforwardEquiv_germ (U : Opens Y.carrier) (hU : f.hom.base x ∈ U)
    (m : (pushforwardAt f E).val.obj (op U)) :
    letI : Module ↑(ringStalk Y (f.hom.base x)) ↑(grpStalk X E.val x) :=
      Module.compHom _ (f.hom.stalkMap x).hom
    stalkPushforwardEquiv f E x hf
        (grpGerm Y (pushforwardAt f E).val (f.hom.base x) U hU m) =
      grpGerm X E.val x ((opensMap f).obj U) hU m :=
  stalkPushforwardHom_germ f E x U hU m

/-- **The algebraic shape of the projection formula on a stalk.**  Let `A` be an `R`-algebra,
`M₀`, `N` be `R`-modules, `M`, `P` be `A`-modules with compatible `R`-structures, and let
`eM : M₀ ≃ₗ[R] M` and `eP : P ≃ₗ[A] A ⊗[R] N`.  Then *any* `R`-linear map
`M₀ ⊗[R] N ⟶ M ⊗[A] P` carrying `m ⊗ n` to `eM m ⊗ eP.symm (1 ⊗ n)` is bijective, because that
formula pins it down as the composite

`M₀ ⊗_R N ≅ M ⊗_R N ≅ M ⊗_A (A ⊗_R N) ≅ M ⊗_A P`

of `eM`, `TensorProduct.AlgebraTensorModule.cancelBaseChange` and `eP`. -/
private lemma tensorProjectionMap_bijective
    {R A M₀ M N P : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M₀] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M₀] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module R N] [Module R P] [Module A P] [IsScalarTower R A P]
    (eM : M₀ ≃ₗ[R] M) (eP : P ≃ₗ[A] A ⊗[R] N) (g : (M₀ ⊗[R] N) →ₗ[R] (M ⊗[A] P))
    (hg : ∀ (m : M₀) (n : N), g (m ⊗ₜ[R] n) = eM m ⊗ₜ[A] eP.symm ((1 : A) ⊗ₜ[R] n)) :
    Function.Bijective g := by
  let q₁ : (M₀ ⊗[R] N) ≃ₗ[R] M ⊗[R] N := TensorProduct.congr eM (LinearEquiv.refl R N)
  let q₂ : (M ⊗[R] N) ≃ₗ[R] M ⊗[A] (A ⊗[R] N) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A M N).symm.restrictScalars R
  let q₃ : (M ⊗[A] (A ⊗[R] N)) ≃ₗ[R] M ⊗[A] P :=
    (TensorProduct.congr (LinearEquiv.refl A M) eP.symm).restrictScalars R
  let q := (q₁.trans q₂).trans q₃
  have hgq : g = q.toLinearMap :=
    TensorProduct.ext' fun m n ↦ (hg m n).trans (by simp [q, q₁, q₂, q₃])
  rw [hgq]
  exact q.bijective

/-- A germ represented over `U₁` is represented over every smaller open `U` containing `x`. -/
private lemma exists_germ_eq_of_le {C : Type (u + 1)} [Category.{u} C] [HasColimits C]
    {FC : C → C → Type*} {CC : C → Type u} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory.{u} C FC] {T : TopCat.{u}} (F : T.Presheaf C) {U₁ U : Opens T} (h : U ≤ U₁)
    {x : T} (hx : x ∈ U) {s : ToType (F.obj (op U₁))} {m : ToType (F.stalk x)}
    (hs : F.germ U₁ x (h hx) s = m) : ∃ t : ToType (F.obj (op U)), F.germ U x hx t = m :=
  ⟨F.map (homOfLE h).op s, (F.germ_res_apply (homOfLE h) x hx s).trans hs⟩

variable (K : SheafOfModules.{u} (structureSheafRing Y))

/-- The projection-formula morphism, retyped over
`structureSheafRing` so that the stalk machinery of
[Stacks, Tag 01CB] applies to it. -/
private noncomputable abbrev projectionFormulaMapAt :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩).obj
        ((pushforwardAt f E))).obj (K)) ⟶
      pushforwardAt f
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (E)).obj
            ((pullbackSheaf f K)))) :=
  projectionFormulaMap' f E K

include hf in
/-- **Over a point of the image the projection-formula morphism is invertible on stalks.**  This
is the second half of the stalk verification in the source's proof of [Stacks, Tag 0B55], and the
step where the mathematics sits: at `y = f x` the source stalk is `G_x ⊗_R H_{f x}` and the
target stalk is `G_x ⊗_S (S ⊗_R H_{f x})`, and they are identified by cancelling the base change.

The stalk map is `R`-linear and carries the germ of `m ⊗ k` to the germ of `m ⊗ η k` by
`Stacks.ProjectionFormula.projectionFormulaMap'_unit_tmul`, which under the three identifications
`stalkPushforwardEquiv`, [Stacks, Tag 01CB] and [Stacks, Tag 0098] is exactly the formula
`m ⊗ n ↦ m ⊗ (1 ⊗ n)` that `tensorProjectionMap_bijective` recognises. -/
@[stacks 0B55 "the stalk computation over a point of the image, by cancelling the base change"]
theorem isIso_stalkMap_projectionFormulaMap'_of_memRange :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f.hom.base x)).map
      ((ExtensionByZeroModules.toAb (structureRingSheaf Y)).map
        (projectionFormulaMap' f E K))) := by
  let R := ringStalk Y (f.hom.base x)
  let A := ringStalk X x
  let _ : Algebra ↑R ↑A := (f.hom.stalkMap x).hom.toAlgebra
  let M₀ := grpStalk Y (pushforwardAt f E).val (f.hom.base x)
  let M := grpStalk X E.val x
  let N := grpStalk Y K.val (f.hom.base x)
  let P₀ := grpStalk X (pullbackSheaf f K).val x
  let V := grpStalk X ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (E)).obj ((pullbackSheaf f K)))).val x
  let _ : Module ↑A ↑V :=
    stalkModule X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
        (E)).obj ((pullbackSheaf f K)))).val x
  let _ : Module ↑R ↑(grpStalk Y
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩).obj
      ((pushforwardAt f E))).obj (K))).val (f.hom.base x)) :=
    stalkModule Y ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩).obj
        ((pushforwardAt f E))).obj (K))).val (f.hom.base x)
  let _ : Module ↑R ↑M := Module.compHom _ (f.hom.stalkMap x).hom
  let _ : Module ↑R ↑P₀ := Module.compHom _ (f.hom.stalkMap x).hom
  let _ : Module ↑R ↑V := Module.compHom _ (f.hom.stalkMap x).hom
  let _ : IsScalarTower ↑R ↑A ↑M := .of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower ↑R ↑A ↑P₀ := .of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower ↑R ↑A ↑V := .of_algebraMap_smul fun _ _ ↦ rfl
  let eM : ↑M₀ ≃ₗ[↑R] ↑M := stalkPushforwardEquiv f E x hf
  let eP : ↑P₀ ≃ₗ[↑A] ↑A ⊗[↑R] ↑N := pullbackStalkEquiv f K x
  let eS : ↑(grpStalk Y
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩).obj
      ((pushforwardAt f E))).obj (K))).val (f.hom.base x)) ≃ₗ[↑R] ↑M₀ ⊗[↑R] ↑N :=
    tensorStalkIso Y (f.hom.base x) (pushforwardAt f E) K
  let eT : ↑(grpStalk Y (pushforwardAt f
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (E)).obj
          ((pullbackSheaf f K))))).val (f.hom.base x)) ≃ₗ[↑R] ↑V :=
    stalkPushforwardEquiv f ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (E)).obj ((pullbackSheaf f K)))) x hf
  let eV : ↑V ≃ₗ[↑A] ↑M ⊗[↑A] ↑P₀ := tensorStalkIso X x E (pullbackSheaf f K)
  let pmap := stalkMapL Y
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩).obj
        ((pushforwardAt f E))).obj (K))).val
    (pushforwardAt f
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (E)).obj
        ((pullbackSheaf f K))))).val (projectionFormulaMapAt f E K).val (f.hom.base x)
  let g : (↑M₀ ⊗[↑R] ↑N) →ₗ[↑R] (↑M ⊗[↑A] ↑P₀) :=
    (eV.restrictScalars ↑R).toLinearMap.comp
      (eT.toLinearMap.comp (pmap.comp eS.symm.toLinearMap))
  have hg : ∀ (m : ↑M₀) (n : ↑N), g (m ⊗ₜ[↑R] n) =
      eM m ⊗ₜ[↑A] eP.symm ((1 : ↑A) ⊗ₜ[↑R] n) := by
    intro m n
    obtain ⟨U₁, hU₁, m₁, hm₁⟩ :=
      Stacks.SheafOfModules.exists_grpGerm_eq Y (pushforwardAt f E).val (f.hom.base x) m
    obtain ⟨U₂, hU₂, n₂, hn₂⟩ :=
      Stacks.SheafOfModules.exists_grpGerm_eq Y K.val (f.hom.base x) n
    set U : Opens Y.carrier := U₁ ⊓ U₂ with hUdef
    have hU : f.hom.base x ∈ U := ⟨hU₁, hU₂⟩
    obtain ⟨mU, hmU⟩ : ∃ mU : (pushforwardAt f E).val.obj (op U),
        grpGerm Y (pushforwardAt f E).val (f.hom.base x) U hU mU = m :=
      exists_germ_eq_of_le (C := AddCommGrpCat.{u}) _ inf_le_left hU hm₁
    obtain ⟨nU, hnU⟩ : ∃ nU : K.val.obj (op U), grpGerm Y K.val (f.hom.base x) U hU nU = n :=
      exists_germ_eq_of_le (C := AddCommGrpCat.{u}) _ inf_le_right hU hn₂
    set sY := Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection Y
      (pushforwardAt f E) K (op U) (mU ⊗ₜ[Y.presheaf.obj (op U)] nU) with hsYdef
    set sX := Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X
      E (pullbackSheaf f K) (op ((opensMap f).obj U))
      ((show E.val.obj (op ((opensMap f).obj U)) from mU) ⊗ₜ[X.presheaf.obj
        (op ((opensMap f).obj U))] pullbackUnit f K (op U) nU) with hsXdef
    have hsY : eS (grpGerm Y
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩).obj
        ((pushforwardAt f E))).obj (K))).val (f.hom.base x) U hU sY) = m ⊗ₜ[↑R] n := by
      rw [hsYdef, tensorStalkIso_germ Y (f.hom.base x) (pushforwardAt f E) K U hU mU nU,
        hmU, hnU]
    have hsX : pmap (grpGerm Y
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩).obj
        ((pushforwardAt f E))).obj (K))).val (f.hom.base x) U hU sY) =
        grpGerm Y (pushforwardAt f
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (E)).obj
              ((pullbackSheaf f K))))).val (f.hom.base x) U hU sX :=
      (Stacks.SheafOfModules.stalkMapL_germ Y (projectionFormulaMapAt f E K).val
          (f.hom.base x) U hU sY).trans
        (congrArg (fun t ↦ grpGerm Y (pushforwardAt f
            ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
                (E)).obj ((pullbackSheaf f K))))).val (f.hom.base x) U hU t)
          (projectionFormulaMap'_unit_tmul f E K (op U) mU nU))
    have hV : eV (grpGerm X
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (E)).obj
        ((pullbackSheaf f K)))).val x ((opensMap f).obj U) hU sX) =
        eM m ⊗ₜ[↑A] eP.symm ((1 : ↑A) ⊗ₜ[↑R] n) := by
      rw [hsXdef, tensorStalkIso_germ X x E (pullbackSheaf f K) ((opensMap f).obj U) hU
          (show E.val.obj (op ((opensMap f).obj U)) from mU) (pullbackUnit f K (op U) nU),
        show eP.symm ((1 : ↑A) ⊗ₜ[↑R] n) =
            grpGerm X (pullbackSheaf f K).val x ((opensMap f).obj U) hU
              (pullbackUnit f K (op U) nU) by
          rw [← hnU]
          exact pullbackStalkEquiv_symm_one_tmul f K x U hU nU,
        show eM m = grpGerm X E.val x ((opensMap f).obj U) hU
            (show E.val.obj (op ((opensMap f).obj U)) from mU) by
          rw [← hmU]
          exact stalkPushforwardEquiv_germ f E x hf U hU mU]
    show eV (eT (pmap (eS.symm (m ⊗ₜ[↑R] n)))) = _
    rw [← hsY, eS.symm_apply_apply, hsX,
      stalkPushforwardEquiv_germ f ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (E)).obj ((pullbackSheaf f K)))) x hf U hU
        (show (pushforwardAt f
            ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
            (E)).obj ((pullbackSheaf f K))))).val.obj (op U) from sX)]
    exact hV
  have hbij : Function.Bijective g := tensorProjectionMap_bijective eM eP g hg
  have hpmap : Function.Bijective pmap := by
    refine ⟨fun s t hst ↦ eS.injective (hbij.1 ?_), fun t ↦ ?_⟩
    · show eV (eT (pmap (eS.symm (eS s)))) = eV (eT (pmap (eS.symm (eS t))))
      simp only [eS.symm_apply_apply]
      exact congrArg (fun z ↦ eV (eT z)) hst
    · obtain ⟨z, hz⟩ := hbij.2 (eV (eT t))
      refine ⟨eS.symm z, eT.injective (eV.injective ?_)⟩
      change eV (eT (pmap (eS.symm z))) = eV (eT t) at hz ⊢
      exact hz
  exact (ConcreteCategory.isIso_iff_bijective _).2 hpmap

end InImage

/-! ### The projection formula for a closed embedding -/

/-- **The ordinary projection formula for a closed embedding of ringed spaces.**  For a morphism
of ringed spaces `f : X ⟶ Y` whose underlying continuous map is a homeomorphism onto a closed
subset, and for *arbitrary* sheaves of modules `G` on `X` and `H` on `Y`, the canonical morphism

`f_*G ⊗_{𝒪_Y} H ⟶ f_*(G ⊗_{𝒪_X} f^*H)`

is an isomorphism.

This is step 1 of the source's proof of [Stacks, Tag 0B55].  A morphism of sheaves of modules
which is invertible on every stalk is invertible
(`ExtensionByZeroModules.isIso_of_stalk_isIso`), and the two stalk computations are
`isIso_stalkMap_projectionFormulaMap'_of_memRange` on the image and
`isIso_stalkMap_projectionFormulaMap'_of_notMemRange` off it.

No local surjectivity of `𝒪_Y ⟶ f_*𝒪_X` is assumed, so the counit of `f^* ⊣ f_*` is not
invertible and the formal argument of `Stacks.AffineProjectionFormula.isIso_projectionFormulaMap`
is unavailable; that is why the proof goes through stalks.  The derived statement of
[Stacks, Tag 0B55] does not follow from this without the K-flat reduction, and is not proved
here. -/
@[stacks 0B55 "step 1: the ordinary projection formula map is invertible for a closed embedding",
  sga "3 VIB 11.5" "Clause (a), special case"]
theorem isIso_projectionFormulaMap'_of_isClosedEmbedding
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base)) :
    IsIso (projectionFormulaMap' f G H) := by
  refine ExtensionByZeroModules.isIso_of_stalk_isIso (structureRingSheaf Y)
    (projectionFormulaMap' f G H) fun y ↦ ?_
  by_cases hy : y ∈ Set.range (ConcreteCategory.hom f.hom.base)
  · obtain ⟨x, rfl⟩ := hy
    exact isIso_stalkMap_projectionFormulaMap'_of_memRange f (atX G) x hf.isInducing (atY H)
  · exact isIso_stalkMap_projectionFormulaMap'_of_notMemRange f G H hf y hy

/-- **The projection formula isomorphism for a closed embedding**,
`f_*G ⊗_{𝒪_Y} H ≅ f_*(G ⊗_{𝒪_X} f^*H)`, whose forward map is
`Stacks.ProjectionFormula.projectionFormulaMap'`. -/
noncomputable def projectionFormulaIso
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(Y).presheaf, (Y).IsSheaf⟩))).obj ((pushforwardFunctor f).obj G, H) ≅
      (pushforwardFunctor f).obj (((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩))).obj (G,
          (pullbackFunctor f).obj H)) :=
  have := isIso_projectionFormulaMap'_of_isClosedEmbedding f G H hf
  asIso (projectionFormulaMap' f G H)

end Stacks.ClosedEmbeddingProjectionFormula

end

end
