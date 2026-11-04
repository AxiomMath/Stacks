module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison
public import StacksFrontier.AlgebraicGeometry.ModuleSkyscraper.PullbackStalk
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero

/-!
# The pullback–tensor comparison of Stacks 01CD on stalks

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `A`, `B` be sheaves of
`𝒪_Y`-modules. `Stacks.RingedSpace.comparison` is the canonical morphism

`f^*(A ⊗_{𝒪_Y} B) ⟶ f^*A ⊗_{𝒪_X} f^*B`

of Stacks 01CD, and Stacks 01CD is the assertion that it is invertible. The comparison is
pinned only through the pullback adjunction, by its effect on the sheafification-unit image of a
pure tensor (`comparison_homEquiv_unit_tmul`).

Here the comparison is computed on germs, the stalk of a pullback is computed on elements, and
invertibility is reduced to a condition on stalks: the three inputs of the route to Stacks 01CD
through stalks, which is carried out in `Invertible.lean`.

## Main results

* `Stacks.PullbackTensorIso.comparison_val_app_pullbackUnit`: on a section of `f^*(A ⊗ B)`
  which is the pullback-unit image of a section of `A ⊗ B`, the comparison is computed by
  its adjoint transpose.
* `Stacks.PullbackTensorIso.germ_comparison_pullbackUnit`: the germ formula. The map on
  stalks induced by the comparison carries the germ at `x` of the pullback-unit image of the
  sheafification-unit image of a pure tensor `a ⊗ b` to the germ of the sheafification-unit
  image of `η a ⊗ η b`, where `η` is the pullback unit. In words: on germs of pulled-back
  pure tensors the comparison is `germ (η (a ⊗ b)) ↦ germ (η a ⊗ η b)`.
* `Stacks.PullbackTensorIso.tensorStalkIso_germ_comparison`: the same statement read through
  the identification `(F ⊗ G)_x ≅ F_x ⊗_{𝒪_{X,x}} G_x` of Stacks 01CB
  (`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`): the comparison followed by that
  identification carries the germ of the pullback-unit image of `a ⊗ b` to `germ (η a) ⊗ germ (η
  b)`.
* `Stacks.PullbackTensorIso.pullbackStalkIso_inv_app_unit` and its ringed-space form
  `ringedSpacePullbackStalkIso_inv_app_unit`: the stalk of a pullback on elements. The
  identification `(f^*A)_x ≅ L (A_{f x})` of `Stacks.ModuleSkyscraper.pullbackStalkIsoOfAdjunction`
  carries, in the inverse direction, the image of `germ a` under the unit of the adjunction
  defining `L` to `germ (η a)`, the germ of the pullback-unit image of `a`. For `L` the
  extension of scalars along the stalk map this is `germ a ⊗ 1 ↦ germ (η a)`.
* `Stacks.PullbackTensorIso.isIso_of_bijective_stalk_map` and
  `isIso_of_isIso_stalkFunctor_map`: a morphism of sheaves of modules whose induced map of
  stalks is bijective at every point — respectively, is an isomorphism of modules over the
  stalk of the sheaf of rings at every point — is an isomorphism.

## The canonical tensor product

Stacks 01CB and the comparison of Stacks 01CD use the same native curried
`Stacks.SheafOfModules.Tensor.sheafTensor`, constructed from `PresheafOfModules.tensorObj`.
The stalk isomorphism therefore applies directly to the comparison, without a tensor spelling
isomorphism. The section map is the generic sheafification unit
(`toTensorSheafSection_eq_tensorSheafUnit`), and
`structureSheafRing_eq_structureRingSheaf` identifies the two spellings of the coefficient sheaf
of rings.

## Universes

A single universe `u`: everything is over `AlgebraicGeometry.RingedSpace.{u, u}` and
`SheafOfModules.{u}`, which is the generality of `Stacks.RingedSpace.comparison` and of
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` alike.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)
-/

@[expose] public section

attribute [local implicit_reducible] TopCat.Presheaf.IsSheaf TopCat.Sheaf
  AlgebraicGeometry.SheafedSpace.sheaf

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.PullbackTensorIso

open RingedSpaceModuleAdjunction PresheafOfModules CategoryTheory.Sheaf Stacks.RingedSpace

/-! ### Germs and the stalkwise criterion for invertibility -/

section Germs

variable {T : TopCat.{u}} {R : (Opens T)ᵒᵖ ⥤ RingCat.{u}}

/-- The map on stalks induced by a morphism of presheaves of modules, on a germ: it carries
the germ of a section to the germ of its image. -/
lemma stalkFunctor_map_germ_hom {F F' : PresheafOfModules.{u} R} (φ : F ⟶ F') (x : T)
    (U : Opens T) (hx : x ∈ U) (s : F.obj (op U)) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf R).map φ)
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) F.presheaf U x hx s) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) F'.presheaf U x hx (Hom.app φ (op U) s) :=
  (TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u}) U x hx
    ((PresheafOfModules.toPresheaf R).map φ) s).trans rfl

variable (O : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u})

/-- A morphism of sheaves of modules whose induced map of stalks is bijective at every point
is an isomorphism. -/
lemma isIso_of_bijective_stalk_map {M N : SheafOfModules.{u} O} (φ : M ⟶ N)
    (h : ∀ x : T, Function.Bijective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf O.obj).map φ.val))) : IsIso φ :=
  ExtensionByZeroModules.isIso_of_stalk_isIso O φ fun x =>
    (ConcreteCategory.isIso_iff_bijective _).2 (h x)

/-- A morphism of sheaves of modules which is invertible on every stalk, as a morphism of
modules over the stalk of the sheaf of rings, is an isomorphism. -/
lemma isIso_of_isIso_stalkFunctor_map {M N : SheafOfModules.{u} O} (φ : M ⟶ N)
    (h : ∀ x : T, IsIso ((AlgebraicGeometry.SheafOfModules.stalkFunctor O x).map φ)) :
    IsIso φ :=
  isIso_of_bijective_stalk_map O φ fun x =>
    have := h x
    ConcreteCategory.bijective_of_isIso
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor O x).map φ)

end Germs

/-! ### The tensor product of Stacks 01CB is the tensor product of Stacks 01CD -/

section Identifications

variable (Z : RingedSpace.{u, u})

/-- The structure sheaf read as a sheaf of rings, in the spelling of Stacks 01CB and in the
spelling of the comparison of Stacks 01CD, are the same sheaf of rings. -/
lemma structureSheafRing_eq_structureRingSheaf :
    structureSheafRing Z = structureRingSheaf Z := rfl

variable (A B : SheafOfModules.{u} (structureRingSheaf Z))

/-- The map on sections into the tensor product of Stacks 01CB is the sheafification unit the
comparison of Stacks 01CD is stated for. -/
lemma toTensorSheafSection_eq_tensorSheafUnit (U : (Opens Z.carrier)ᵒᵖ) (a : A.val.obj U)
    (b : B.val.obj U) :
    Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection Z A B U (a ⊗ₜ b) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf).obj)).unit.app
        (PresheafOfModules.tensorObj (O := Z.presheaf) A.val B.val)) U (a ⊗ₜ b) := rfl

end Identifications

/-! ### The comparison on sections and on germs -/

section Comparison

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (A B : SheafOfModules.{u} (structureRingSheaf Y))

/-- The comparison morphism on a pullback-unit image: it is computed there by its adjoint
transpose. -/
lemma comparison_val_app_pullbackUnit (V : Opens Y.carrier)
    (t : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj A).obj B).val.obj
      (op V)) :
    Hom.app (comparison f A B).val (op ((opensMap f).obj V))
        (pullbackUnit f
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj A).obj B)
          (op V) t) =
      Hom.app ((pullbackAdjunction f).homEquiv
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj A).obj B)
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
          ((pullbackFunctor f).obj A)).obj ((pullbackFunctor f).obj B))
        (comparison f A B)).val (op V) t :=
  (homEquiv_val_app f
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj A).obj B)
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
      ((pullbackFunctor f).obj A)).obj ((pullbackFunctor f).obj B))
    (comparison f A B) (op V) t).symm

/-- The comparison morphism of Stacks 01CD on germs: the induced map of stalks at a point
`x` of `X` carries the germ of the pullback-unit image of the sheafification-unit image of a
pure tensor `a ⊗ b` to the germ of the sheafification-unit image of the tensor of the two
pullback-unit images. -/
lemma germ_comparison_pullbackUnit (x : X.carrier) (U : Opens Y.carrier)
    (hx : x ∈ (opensMap f).obj U) (a : A.val.obj (op U)) (b : B.val.obj (op U)) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf (structureRingSheaf X).obj).map (comparison f A B).val)
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          ((pullbackFunctor f).obj
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj A).obj
              B)).val.presheaf
          ((opensMap f).obj U) x hx
          (pullbackUnit f
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj A).obj B)
            (op U)
            (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj)).unit.app
              (PresheafOfModules.tensorObj (O := Y.presheaf) A.val B.val)) (op U) (a ⊗ₜ b)))) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
          ((pullbackFunctor f).obj A)).obj ((pullbackFunctor f).obj B)).val.presheaf
        ((opensMap f).obj U) x hx
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.app
          (PresheafOfModules.tensorObj (O := X.presheaf) ((pullbackFunctor f).obj A).val
            ((pullbackFunctor f).obj B).val))
          ((opensMap f).op.obj (op U))
          (pullbackUnit f A (op U) a ⊗ₜ pullbackUnit f B (op U) b)) := by
  refine (stalkFunctor_map_germ_hom (comparison f A B).val x ((opensMap f).obj U) hx _).trans ?_
  refine congrArg _ ?_
  refine (comparison_val_app_pullbackUnit f A B U _).trans ?_
  exact comparison_homEquiv_unit_tmul f A B (op U) a b

/-- The pullback of a sheaf of `𝒪_Y`-modules, re-typed over the spelling `structureSheafRing` of
the structure sheaf of `X` as a sheaf of rings. The two spellings are the same sheaf of rings
(`structureSheafRing_eq_structureRingSheaf`), but only this one lets instance search find the
module structure on a stalk. -/
noncomputable abbrev pullbackSheaf (A : SheafOfModules.{u} (structureRingSheaf Y)) :
    SheafOfModules.{u} (structureSheafRing X) :=
  (pullbackFunctor f).obj A

/-- The comparison morphism of Stacks 01CD on germs, through the stalk of a tensor product of
Stacks 01CB. Composed with the identification `(f^*A ⊗ f^*B)_x ≅ (f^*A)_x ⊗ (f^*B)_x`,
the map on stalks induced by the comparison carries the germ of the pullback-unit image of a
pure tensor `a ⊗ b` to the tensor of the germs of the two pullback-unit images.

With the stalk of a pullback described on elements, this is the identity that exhibits the
map on stalks as the base-change isomorphism, and hence Stacks 01CD. -/
theorem tensorStalkIso_germ_comparison (x : X.carrier) (U : Opens Y.carrier)
    (hx : x ∈ (opensMap f).obj U) (a : A.val.obj (op U)) (b : B.val.obj (op U)) :
    Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X x (pullbackSheaf f A)
      (pullbackSheaf f B)
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf (structureRingSheaf X).obj).map
            (comparison f A B).val)
          (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            ((pullbackFunctor f).obj
              (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj A).obj
                B)).val.presheaf
            ((opensMap f).obj U) x hx
            (pullbackUnit f
              (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj A).obj B)
              (op U)
              (Hom.app ((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj)).unit.app
                (PresheafOfModules.tensorObj (O := Y.presheaf) A.val B.val)) (op U) (a ⊗ₜ b))))) =
      Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X (pullbackSheaf f A).val x
        ((opensMap f).obj U) hx
          (pullbackUnit f A (op U) a) ⊗ₜ
        Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X (pullbackSheaf f B).val x
          ((opensMap f).obj U) hx
          (pullbackUnit f B (op U) b) := by
  refine (congrArg _ (germ_comparison_pullbackUnit f A B x U hx a b)).trans ?_
  exact Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso_germ X x (pullbackSheaf f A)
    (pullbackSheaf f B)
    ((opensMap f).obj U) hx _ _

end Comparison

/-! ### The stalk of a pullback, on elements -/

section StalkOfPullback

open Stacks.ModuleSkyscraper

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  (OX : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (OY : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) RingCat.{u})
  (φ : OY ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj OX)
  (x : X)
  {L : ModuleCat.{u} (Stalk OY (f x)) ⥤ ModuleCat.{u} (Stalk OX x)}
  (adjL : L ⊣ ModuleCat.restrictScalars (stalkRingMap f OX OY φ x).hom)

/-- The stalk of a pullback, on elements. The inverse of
`Stacks.ModuleSkyscraper.pullbackStalkIsoOfAdjunction` carries the image of the germ at `f x` of a
section `a` of `A`, under the unit of the adjunction defining `L`, to the germ at `x` of the
pullback-unit image of `a`. For `L` the extension of scalars along the stalk map this reads
`germ a ⊗ 1 ↦ germ (η a)`.

It is read off the characterisation `CategoryTheory.unit_conjugateEquiv_symm` of a conjugate
transformation, evaluated at a section over an open containing `f x`: that characterisation is an
equation of morphisms into the module skyscraper at `f x` whose two sides are precisely the two
sides above. -/
lemma pullbackStalkIso_inv_app_unit (A : SheafOfModules.{u} OY) (V : Opens Y) (hV : f x ∈ V)
    (a : A.val.obj (op V)) :
    ((pullbackStalkIsoOfAdjunction f OX OY φ x adjL).inv.app A).hom
        (adjL.unit.app (stalkMod OY (f x) A) (modGerm OY (f x) A V hV a)) =
      modGerm OX x ((SheafOfModules.pullback φ).obj A) ((Opens.map f).obj V) hV
        (((SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app A).val.app (op V) a) := by
  have h := unit_conjugateEquiv_symm
    ((SheafOfModules.pullbackPushforwardAdjunction.{u} φ).comp (adjunction OX x))
    ((adjunction OY (f x)).comp adjL) (pushforwardSkyscraperIso f OX OY φ x).hom A
  have h2 := congrArg
    (fun ψ : A ⟶ ((ModuleCat.restrictScalars (stalkRingMap f OX OY φ x).hom ⋙
        functor OY (f x)).obj
          ((SheafOfModules.pullback.{u} φ ⋙
            AlgebraicGeometry.SheafOfModules.stalkFunctor OX x).obj A)) =>
      PresheafOfModules.Hom.app ψ.val (op V) a) h
  exact (congrFun h2 ⟨hV⟩).symm

end StalkOfPullback

section RingedSpaceStalkOfPullback

open Stacks.ModuleSkyscraper

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (x : X.carrier)
  {L : ModuleCat.{u} (Stalk (structureSheafRing Y) (f.hom.base x)) ⥤
    ModuleCat.{u} (Stalk (structureSheafRing X) x)}
  (adjL : L ⊣ ModuleCat.restrictScalars (ringedSpaceStalkRingMap f x).hom)

/-- The stalk of a pullback along a morphism of ringed spaces, on elements, in the vocabulary
Stacks 01CD is stated over: the inverse of
`Stacks.ModuleSkyscraper.ringedSpacePullbackStalkIso` carries the image of the germ of a
section `a` under the unit of the adjunction defining `L` to the germ of
`Stacks.RingedSpace.pullbackUnit` of `a`. -/
lemma ringedSpacePullbackStalkIso_inv_app_unit
    (A : SheafOfModules.{u} (structureRingSheaf Y)) (V : Opens Y.carrier)
    (hV : f.hom.base x ∈ V) (a : A.val.obj (op V)) :
    ((ringedSpacePullbackStalkIso f x adjL).inv.app A).hom
        (adjL.unit.app (stalkMod (structureSheafRing Y) (f.hom.base x) A)
          (modGerm (structureSheafRing Y) (f.hom.base x) A V hV a)) =
      modGerm (structureSheafRing X) x ((pullbackFunctor f).obj A) ((opensMap f).obj V) hV
        (pullbackUnit f A (op V) a) :=
  pullbackStalkIso_inv_app_unit f.hom.base (structureSheafRing X) (structureSheafRing Y)
    (structureSheafHom f) x adjL A V hV a

end RingedSpaceStalkOfPullback

end Stacks.PullbackTensorIso
