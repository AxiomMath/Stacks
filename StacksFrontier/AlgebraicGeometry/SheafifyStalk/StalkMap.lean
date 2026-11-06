module

public import StacksFrontier.AlgebraicGeometry.SheafifyStalk.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalk of the sheaf inverse image, against the stalk map of a morphism

`Stacks.SheafifyStalk.stalkSheafPullbackIso` identifies the stalk `(f⁻¹F)_x` of the sheaf
inverse image with the stalk `F_{f(x)}`.  **This file shows that identification is compatible
with adjunction**: a morphism `φ : f⁻¹F ⟶ G` of sheaves and its adjoint
`ψ : F ⟶ f_*G` induce the same map `F_{f(x)} ⟶ G_x`, the first through the identification and
the second through `TopCat.Presheaf.stalkPushforward`.

At the structure sheaf of a morphism of schemes this is the statement that
`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso` carries the stalk of the structural
map `g⁻¹ 𝒪_S ⟶ 𝒪_T` to `AlgebraicGeometry.Scheme.Hom.stalkMap`, which is what the module
docstring of `StacksFrontier.AlgebraicGeometry.SheafifyStalk.Basic` records as missing and what
`StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.Scheme` needs in order to rewrite
the base ring of its Kähler differentials from `(f⁻¹𝒪_S)_x` to `𝒪_{S, f x}`.

## Main results

* `Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_comp`: the compatibility, in general.  For
  `φ : f⁻¹F ⟶ G`,
  `(stalkSheafPullbackIso f F x).inv ≫ (φ_x) = (ψ_{f x}) ≫ stalkPushforward f G x`
  where `ψ` is the adjoint of `φ`.
* `Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso_inv_comp`: its instance at the
  structural map of a morphism of schemes, where the right-hand side *is*
  `AlgebraicGeometry.Scheme.Hom.stalkMap`.
* `Stacks.SheafifyStalk.stalkMap_eq_stalkInverseImageStructureSheafIso_hom_comp`: the same
  equation read as a formula for `AlgebraicGeometry.Scheme.Hom.stalkMap`, and
  `Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso_hom_comp_stalkMap` the form with the
  isomorphism on the other side.
* `Stacks.SheafifyStalk.stalkMap_hom_eq_comp`: the same equation between the underlying ring
  homomorphisms, which is the form the two algebra structures on `𝒪_{T,t}` are compared in.

## Route and why

Three reductions, each removing one of the three comparisons that
`Stacks.SheafifyStalk.stalkSheafPullbackIso` is built from.

* `Stacks.SheafifyStalk.stalkPullbackHom_comp` is the compatibility at the level of
  *presheaves*: it is `Mathlib`'s definition of `TopCat.Presheaf.stalkPullbackHom` as a stalk of
  the presheaf-level unit followed by `stalkPushforward`, together with the naturality of
  `stalkPushforward` proved in
  `StacksFrontier.AlgebraicGeometry.SheafifyStalk.Basic`.  No sheaves are involved.
* `Stacks.SheafifyStalk.sheafPullbackPushforwardAdjunction_unit_hom` descends the unit of the
  *sheaf*-level adjunction to presheaves: it is the presheaf-level unit, followed by the unit of
  sheafification, followed by `TopCat.Sheaf.pullbackIso`.  This is where all the work is.
  `TopCat.Sheaf.pullback` is a chosen left adjoint and `TopCat.Sheaf.pullbackIso` compares it
  with the construction by sheafifying the presheaf inverse image; the comparison is
  `CategoryTheory.Adjunction.leftAdjointUniq`, so
  `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` transports the unit along it, and
  what is left is to read the unit of the constructed adjunction on underlying presheaves.
  That constructed adjunction is a composite of the left Kan extension adjunction with the
  sheafification adjunction, restricted along the fully faithful inclusion of sheaves into
  presheaves, so its unit is computed by
  `CategoryTheory.Adjunction.map_restrictFullyFaithful_unit_app` and
  `CategoryTheory.Adjunction.comp_unit_app`.
* `Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_eq` then rewrites the inverse of the stalk
  comparison as the stalk of that sheaf-level unit followed by `stalkPushforward`, and the
  general compatibility follows from `stalkPushforward` naturality once more.

## Transparency gotchas

* `TopCat.Sheaf C X` is a `def` with a derived `Category` instance, distinct as a constant from
  the `CategoryTheory.Sheaf` instance it is derived from, and
  `CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback` is a `def` whose unfolding
  `rw` and `simp` will not perform.  So the identity morphisms that
  `CategoryTheory.Adjunction.map_restrictFullyFaithful_unit_app` leaves behind — it is applied
  with both of its comparison isomorphisms equal to `Iso.refl` — cannot be removed by
  `Category.comp_id` as a rewrite: the object of the trailing identity and the codomain of the
  morphism before it are definitionally equal and not syntactically equal.  They are removed in
  term mode instead, where the elaborator checks definitional equality at default transparency.
* `TopCat.Presheaf.stalk` is a `def`, so the germ lemmas are stated at a spelling that the
  stalk of a functorial construction does not have; it is made implicitly reducible for the
  sections that rewrite with them, exactly as in
  `StacksFrontier.AlgebraicGeometry.SheafifyStalk.Basic`.

## What is *not* here

The compatibility below is stated for `AlgebraicGeometry.inverseImageStructureMap`, the
structural map used by `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`.  The copy of that
definition in `StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence.Basic` is a different
constant with the same body, so the general statement
`Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_comp` applies to it but
`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso_inv_comp` is not stated at it.

No `stacks` attribute is attached.  This is one of the three pieces that the module docstring of
`StacksFrontier.AlgebraicGeometry.SheafifyStalk.Basic` lists as missing for the
`algebraPullback_isQuasicoherent` clause of [Stacks, Tag 01SA]; the other two — naturality of
the stalk comparison in the sheaf, and the stalk of the presheaf-level extension of scalars —
are still missing, and the statement of Tag 01SA is a single unqualified tag on a nine-field
structure.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe v u

noncomputable section

namespace Stacks.SheafifyStalk

section Presheaves

open TopCat.Presheaf

attribute [local implicit_reducible] TopCat.Presheaf.stalk

variable (C : Type u) [Category.{v} C] [HasColimits.{v} C] {X Y : TopCat.{v}}

/-- **The presheaf-level stalk comparison is compatible with adjunction.**  For a morphism
`η : f⁻¹P ⟶ Q` of presheaves, the composite of `TopCat.Presheaf.stalkPullbackHom` with the stalk
of `η` is the stalk of the adjoint of `η` followed by `TopCat.Presheaf.stalkPushforward`.

Both sides are the stalk of the presheaf-level unit followed by `stalkPushforward`, so this is
the naturality of `stalkPushforward` in the presheaf
(`Stacks.SheafifyStalk.stalkPushforward_naturality`). -/
public theorem stalkPullbackHom_comp (f : X ⟶ Y) {P : Y.Presheaf C} {Q : X.Presheaf C}
    (η : (TopCat.Presheaf.pullback C f).obj P ⟶ Q) (x : X) :
    stalkPullbackHom C f P x ≫ (stalkFunctor C x).map η =
      (stalkFunctor C (f x)).map
          ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).homEquiv P Q η) ≫
        TopCat.Presheaf.stalkPushforward C f Q x := by
  rw [stalkPullbackHom, Category.assoc, ← stalkPushforward_naturality C f η x,
    Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]

end Presheaves

section SheafUnit

variable {X Y : TopCat.{v}} (A : Type u) [Category.{v} A] {FA : A → A → Type*} {CA : A → Type v}
variable [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{v} A FA] [HasColimits A]
variable [HasLimits A] [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

/-- `TopCat.Sheaf.pullbackIso`, the comparison of the sheaf inverse image with the
sheafification of the presheaf inverse image, is the comparison of two left adjoints of
pushforward.  This holds by `rfl` and is recorded because
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` is stated at the second spelling. -/
public theorem pullbackIso_eq_leftAdjointUniq (f : X ⟶ Y) :
    TopCat.Sheaf.pullbackIso A f =
      Adjunction.leftAdjointUniq (TopCat.Sheaf.pullbackPushforwardAdjunction A f)
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) A
          (Opens.grothendieckTopology (Y : Type v)) (Opens.grothendieckTopology (X : Type v))) :=
  rfl

set_option synthInstance.maxHeartbeats 400000 in
/-- **The unit of the constructed inverse-image adjunction, on underlying presheaves.**  The
adjunction obtained by sheafifying the presheaf inverse image has unit the presheaf-level unit
followed by the unit of sheafification.

The constructed adjunction is `CategoryTheory.Adjunction.restrictFullyFaithful` applied to the
composite of the left Kan extension adjunction with the sheafification adjunction, so this is
`CategoryTheory.Adjunction.map_restrictFullyFaithful_unit_app` followed by
`CategoryTheory.Adjunction.comp_unit_app`.  The two comparison isomorphisms of the restriction
are `Iso.refl`, and the identities they leave behind are cancelled in term mode: as rewrites
`Category.comp_id` does not apply, because the object of the trailing identity is only
definitionally the codomain of the morphism it follows. -/
public theorem sheafPullbackConstruction_unit_hom (f : X ⟶ Y) (F : TopCat.Sheaf A Y) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) A
        (Opens.grothendieckTopology (Y : Type v))
        (Opens.grothendieckTopology (X : Type v))).unit.app F).hom =
      (TopCat.Presheaf.pullbackPushforwardAdjunction A f).unit.app F.presheaf ≫
        (TopCat.Presheaf.pushforward A f).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology (X : Type v))
            ((TopCat.Presheaf.pullback A f).obj F.presheaf)) := by
  refine (Adjunction.map_restrictFullyFaithful_unit_app
    (L := Functor.sheafPullbackConstruction.sheafPullback (Opens.map f) A
      (Opens.grothendieckTopology (Y : Type v)) (Opens.grothendieckTopology (X : Type v)))
    (R := (Opens.map f).sheafPushforwardContinuous A
      (Opens.grothendieckTopology (Y : Type v)) (Opens.grothendieckTopology (X : Type v)))
    (((Opens.map f).op.lanAdjunction A).comp
      (sheafificationAdjunction (Opens.grothendieckTopology (X : Type v)) A))
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology (Y : Type v)) A)
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _) F).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (Category.comp_id _).trans ?_
  refine (Category.comp_id _).trans ?_
  exact Adjunction.comp_unit_app _ _ _

set_option synthInstance.maxHeartbeats 400000 in
/-- **The unit of the inverse-image/pushforward adjunction on sheaves, read on underlying
presheaves.**  It is the presheaf-level unit, then the unit of sheafification, then the
comparison `TopCat.Sheaf.pullbackIso` of the sheaf inverse image with that sheafification.

The sheaf inverse image is a *chosen* left adjoint, so its unit is pinned down only up to the
comparison of left adjoints; `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` is what
transports the unit of the constructed adjunction
(`Stacks.SheafifyStalk.sheafPullbackConstruction_unit_hom`) along that comparison. -/
public theorem sheafPullbackPushforwardAdjunction_unit_hom (f : X ⟶ Y) (F : TopCat.Sheaf A Y) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction A f).unit.app F).hom =
      (TopCat.Presheaf.pullbackPushforwardAdjunction A f).unit.app F.presheaf ≫
        (TopCat.Presheaf.pushforward A f).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology (X : Type v))
              ((TopCat.Presheaf.pullback A f).obj F.presheaf) ≫
            ((TopCat.Sheaf.pullbackIso A f).inv.app F).hom) := by
  have key : (TopCat.Sheaf.pullbackPushforwardAdjunction A f).unit.app F ≫
      (TopCat.Sheaf.pushforward A f).map ((TopCat.Sheaf.pullbackIso A f).hom.app F) =
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) A
          (Opens.grothendieckTopology (Y : Type v))
          (Opens.grothendieckTopology (X : Type v))).unit.app F := by
    rw [pullbackIso_eq_leftAdjointUniq]
    exact Adjunction.unit_leftAdjointUniq_hom_app _ _ F
  have hsheaf : (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) A
        (Opens.grothendieckTopology (Y : Type v))
        (Opens.grothendieckTopology (X : Type v))).unit.app F ≫
      (TopCat.Sheaf.pushforward A f).map ((TopCat.Sheaf.pullbackIso A f).inv.app F) =
        (TopCat.Sheaf.pullbackPushforwardAdjunction A f).unit.app F := by
    refine (congrArg (fun z => z ≫ (TopCat.Sheaf.pushforward A f).map
      ((TopCat.Sheaf.pullbackIso A f).inv.app F)) key).symm.trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg
      (fun z => (TopCat.Sheaf.pullbackPushforwardAdjunction A f).unit.app F ≫ z)
      ((TopCat.Sheaf.pushforward A f).mapIso
        ((TopCat.Sheaf.pullbackIso A f).app F)).hom_inv_id).trans ?_
    exact Category.comp_id _
  refine (congrArg (fun z => z.hom) hsheaf.symm).trans ?_
  refine (congrArg (fun z => z ≫ (TopCat.Presheaf.pushforward A f).map
    (((TopCat.Sheaf.pullbackIso A f).inv.app F).hom))
      (sheafPullbackConstruction_unit_hom A f F)).trans ?_
  exact (Category.assoc _ _ _).trans
    (congrArg
      (fun z => (TopCat.Presheaf.pullbackPushforwardAdjunction A f).unit.app F.presheaf ≫ z)
      (CategoryTheory.Functor.map_comp _ _ _).symm)

end SheafUnit

section SheafPullback

open TopCat.Presheaf

attribute [local implicit_reducible] TopCat.Presheaf.stalk

variable {X Y : TopCat.{v}} (A : Type u) [Category.{v} A] {FA : A → A → Type*} {CA : A → Type v}
variable [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{v} A FA] [HasColimits A]
variable [HasLimits A] [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

/-- **The inverse of the stalk comparison of the sheaf inverse image is the stalk of the unit of
the adjunction, followed by `TopCat.Presheaf.stalkPushforward`** — that is, it has exactly the
shape of `AlgebraicGeometry.PresheafedSpace.Hom.stalkMap`.

This replaces the three-fold composite of
`Stacks.SheafifyStalk.stalkSheafPullbackIso_inv` by a single map built from the sheaf-level
unit: the sheafification comparison is absorbed by
`Stacks.SheafifyStalk.sheafPullbackPushforwardAdjunction_unit_hom` and the presheaf-level
comparison by `Stacks.SheafifyStalk.stalkPullbackHom_comp`. -/
@[ega "0 3.7.2" "more general"]
public theorem stalkSheafPullbackIso_inv_eq (f : X ⟶ Y) (F : TopCat.Sheaf A Y) (x : X) :
    (stalkSheafPullbackIso A f F x).inv =
      (stalkFunctor A (f x)).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction A f).unit.app F).hom ≫
        TopCat.Presheaf.stalkPushforward A f
          ((TopCat.Sheaf.pullback A f).obj F).presheaf x := by
  refine (stalkSheafPullbackIso_inv A f F x).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => stalkPullbackHom A f F.presheaf x ≫ z)
    (CategoryTheory.Functor.map_comp (stalkFunctor A x)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology (X : Type v))
        ((TopCat.Presheaf.pullback A f).obj F.presheaf))
      ((TopCat.Sheaf.pullbackIso A f).inv.app F).hom).symm).trans ?_
  refine (stalkPullbackHom_comp A f _ x).trans ?_
  exact congrArg
    (fun z => (stalkFunctor A (f x)).map z ≫
      TopCat.Presheaf.stalkPushforward A f ((TopCat.Sheaf.pullback A f).obj F).presheaf x)
    ((Adjunction.homEquiv_unit _ _ _ _).trans
      (sheafPullbackPushforwardAdjunction_unit_hom A f F).symm)

/-- **The stalk comparison of the sheaf inverse image is compatible with adjunction.**  For a
morphism `φ : f⁻¹F ⟶ G` of sheaves with adjoint `ψ : F ⟶ f_*G`, the map `F_{f(x)} ⟶ G_x`
obtained by inverting the comparison `(f⁻¹F)_x ≅ F_{f(x)}` and taking the stalk of `φ` is the
stalk of `ψ` followed by `TopCat.Presheaf.stalkPushforward`.

The right-hand side is the formula defining `AlgebraicGeometry.PresheafedSpace.Hom.stalkMap`, so
at the structure sheaves of a morphism of schemes this says that the comparison carries the stalk
of the structural map to `AlgebraicGeometry.Scheme.Hom.stalkMap`. -/
@[ega "0 3.7.2" "more general"]
public theorem stalkSheafPullbackIso_inv_comp (f : X ⟶ Y) {F : TopCat.Sheaf A Y}
    {G : TopCat.Sheaf A X} (φ : (TopCat.Sheaf.pullback A f).obj F ⟶ G) (x : X) :
    (stalkSheafPullbackIso A f F x).inv ≫ (stalkFunctor A x).map φ.hom =
      (stalkFunctor A (f x)).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction A f).homEquiv F G φ).hom ≫
        TopCat.Presheaf.stalkPushforward A f G.presheaf x := by
  refine (congrArg (fun z => z ≫ (stalkFunctor A x).map φ.hom)
    (stalkSheafPullbackIso_inv_eq A f F x)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => (stalkFunctor A (f x)).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction A f).unit.app F).hom ≫ z)
    (stalkPushforward_naturality A f φ.hom x).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ TopCat.Presheaf.stalkPushforward A f G.presheaf x)
    (CategoryTheory.Functor.map_comp (stalkFunctor A (f x))
      ((TopCat.Sheaf.pullbackPushforwardAdjunction A f).unit.app F).hom
      ((TopCat.Presheaf.pushforward A f).map φ.hom)).symm).trans ?_
  refine congrArg
    (fun z => (stalkFunctor A (f x)).map z ≫
      TopCat.Presheaf.stalkPushforward A f G.presheaf x) ?_
  exact congrArg (fun w => InducedCategory.Hom.hom w)
    (Adjunction.homEquiv_unit (TopCat.Sheaf.pullbackPushforwardAdjunction A f) F G φ).symm

end SheafPullback

section Schemes

open TopCat.Presheaf

attribute [local implicit_reducible] TopCat.Presheaf.stalk

variable {T S : Scheme.{u}} (g : T ⟶ S)

/-- **The identification `(g⁻¹𝒪_S)_t ≅ 𝒪_{S,g(t)}` carries the stalk of the structural map of
`g` to `g`'s stalk map.**

This is `Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_comp` at the structure sheaf: the
adjoint of `AlgebraicGeometry.inverseImageStructureMap g` is the comorphism `g.c` by
construction, and the stalk of `g.c` followed by `TopCat.Presheaf.stalkPushforward` *is*
`AlgebraicGeometry.Scheme.Hom.stalkMap g t`. -/
@[ega "0 3.7.2" "special case"]
public theorem stalkInverseImageStructureSheafIso_inv_comp (t : T) :
    (stalkInverseImageStructureSheafIso g t).inv ≫
        (stalkFunctor CommRingCat.{u} t).map
          (AlgebraicGeometry.inverseImageStructureMap g).hom =
      g.stalkMap t := by
  have h := stalkSheafPullbackIso_inv_comp CommRingCat.{u} g.base
    (AlgebraicGeometry.inverseImageStructureMap g) t
  rw [show (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).homEquiv
      S.sheaf T.sheaf (AlgebraicGeometry.inverseImageStructureMap g) = ⟨g.c⟩ from
    Equiv.apply_symm_apply _ _] at h
  exact h

/-- **`AlgebraicGeometry.Scheme.Hom.stalkMap` factors through the stalk of the inverse image of
the structure sheaf.**  The form of
`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso_inv_comp` with the isomorphism moved to
the other side: `g`'s stalk map is the comparison `𝒪_{S,g(t)} ≅ (g⁻¹𝒪_S)_t` followed by the
stalk of the structural map. -/
public theorem stalkInverseImageStructureSheafIso_hom_comp_stalkMap (t : T) :
    (stalkInverseImageStructureSheafIso g t).hom ≫ g.stalkMap t =
      (stalkFunctor CommRingCat.{u} t).map
        (AlgebraicGeometry.inverseImageStructureMap g).hom := by
  refine (congrArg (fun z => (stalkInverseImageStructureSheafIso g t).hom ≫ z)
    (stalkInverseImageStructureSheafIso_inv_comp g t).symm).trans ?_
  exact Iso.hom_inv_id_assoc _ _

/-- **The stalk of the structural map of `g`, transported to `𝒪_{S,g(t)}`, is `g`'s stalk
map.**  This is the equation of
`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso_inv_comp` read as a formula for
`AlgebraicGeometry.Scheme.Hom.stalkMap`, which is the direction in which the base ring of a
module over `(g⁻¹𝒪_S)_t` is rewritten as `𝒪_{S,g(t)}`. -/
public theorem stalkMap_eq_stalkInverseImageStructureSheafIso_hom_comp (t : T) :
    g.stalkMap t =
      (stalkInverseImageStructureSheafIso g t).inv ≫
        (stalkFunctor CommRingCat.{u} t).map
          (AlgebraicGeometry.inverseImageStructureMap g).hom :=
  (stalkInverseImageStructureSheafIso_inv_comp g t).symm

/-- **The two algebra structures on `𝒪_{T,t}` agree.**  The ring homomorphism `g.stalkMap t`,
which makes `𝒪_{T,t}` an algebra over `𝒪_{S,g(t)}`, is the ring homomorphism induced by the
structural map `g⁻¹ 𝒪_S ⟶ 𝒪_T`, which makes it an algebra over `(g⁻¹𝒪_S)_t`, precomposed with
the isomorphism of those two base rings.

This is the form of `Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso_inv_comp` that the
Kähler differentials of
`Stacks.RelativeDifferentialStalk.relativeDifferentialsStalkLinearEquiv` consume: that
equivalence has `(g⁻¹𝒪_S)_t` for its base ring through
`Stacks.RelativeDifferentialStalk.algebraStalk`, which is the right-hand factor below read as
an algebra structure. -/
public theorem stalkMap_hom_eq_comp (t : T) :
    (g.stalkMap t).hom =
      ((stalkFunctor CommRingCat.{u} t).map
          (AlgebraicGeometry.inverseImageStructureMap g).hom).hom.comp
        (stalkInverseImageStructureSheafIso g t).inv.hom :=
  congrArg CommRingCat.Hom.hom (stalkInverseImageStructureSheafIso_inv_comp g t).symm

end Schemes

end Stacks.SheafifyStalk

end

end
