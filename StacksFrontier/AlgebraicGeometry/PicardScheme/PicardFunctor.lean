module

public import StacksFrontier.AlgebraicGeometry.Picard.RelativePicardFunctor
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Picard functor of a morphism of a big fppf site

Let `f : X ⟶ S` be a morphism of a big fppf site. Every `S`-scheme `T` of the site has a base
change `X_T = X ×_S T`, and pulling an invertible module back along the transition map
`X_T ⟶ X_U` of two test schemes makes `T ↦ Pic(X_T)` a presheaf of sets on the `S`-schemes of
the site. The *Picard functor* `Pic_{X/S}` is its fppf sheafification.

## Main definitions

* `Stacks.PicardFunctor.picardAt` — the Picard group `Pic(X_T)` of a base change.
* `Stacks.PicardFunctor.picardMap` — pullback of Picard classes along a morphism of test
  schemes, and `Stacks.PicardFunctor.picardMapHom` the same as a homomorphism of abelian
  groups.
* `Stacks.PicardFunctor.picardPresheaf` — the presheaf `T ↦ Pic(X_T)`.
* `Stacks.PicardFunctor.picardFunctor` — the Picard functor `Pic_{X/S}`, the fppf
  sheafification of that presheaf, with `Stacks.PicardFunctor.toPicardFunctor` the canonical
  map into it.
* `Stacks.PicardFunctor.picardAddPresheaf` and `Stacks.PicardFunctor.picardAddFunctor` — the
  same presheaf and its fppf sheafification formed in abelian groups rather than in sets, and
  `Stacks.PicardFunctor.toPicardFunctorHom` the canonical map `Pic(X_T) → Pic_{X/S}(T)` read as
  a homomorphism of abelian groups.

## Main results

* `Stacks.PicardFunctor.baseChangeMap_id` and `Stacks.PicardFunctor.baseChangeMap_comp` — the
  base change of a test scheme is functorial.
* `Stacks.PicardFunctor.picardMap_id` and `Stacks.PicardFunctor.picardMap_comp` — pullback of
  Picard classes along an identity is the identity and along a composite is the composite of
  the pullbacks; these are the functor laws of the presheaf.
* `Stacks.PicardFunctor.isSheaf_picardFunctor` — the Picard functor is an fppf sheaf.
* `Stacks.PicardFunctor.picardFunctorIsoPicardAddFunctor` — the Picard functor is the presheaf
  of sets underlying the Picard functor formed in abelian groups, so each of its values carries
  a group law, `Stacks.PicardFunctor.instAddCommGroupPicardFunctorObj`.

## Implementation notes

The Picard group of a base change is `Stacks.Picard.ofScheme`, the group of isomorphism classes
of invertible modules on the scheme, and pullback of classes is
`Stacks.Picard.schemePullbackClass`, whose two functor laws
`Stacks.Picard.schemePullbackClass_id` and `Stacks.Picard.schemePullbackClass_comp` hold with no
hypothesis: invertibility is stable under pullback by Tag 0B8L, and an isomorphism of invertible
modules is already an equality of Picard classes, so only the existence of the comparisons
`(𝟙)^* L ≅ L` and `(g ≫ h)^* L ≅ g^* h^* L` is needed and not any coherence between them.

The two base-change laws are strict equalities of morphisms of schemes, being uniqueness
statements for a fibre product, so the functor laws of the presheaf reduce to the two statements
about `Stacks.Picard.schemePullbackClass` at a single morphism and no transport along an
equality of base changes appears.

The big site need not contain the fibre products `X ×_S T`; they are formed in the category of
all schemes, which is why `Stacks.PicardFunctor.baseChange` lands in `Scheme`.

An invertible module on a scheme `Y` has its sections in the universe `u` of `Y`, and the opens
of `Y` lie in `Type u`, so `Pic(Y)` — a type of isomorphism classes of such modules — lies in
`Type (u + 1)`. The `S`-schemes of the site form a category in `Type (u + 1)` with morphisms in
`Type u`, so the sheafification of `Type (u + 1)`-valued presheaves applies with no appeal to
essential smallness.

The values of the Picard functor are groups because the presheaf being sheafified is one, but
the sheafification above is formed in sets. Rather than redefine it, the group law is obtained
by sheafifying the same presheaf a second time in abelian groups and comparing the two with
`CategoryTheory.sheafifyComposeIso`, sheafification commuting with the forgetful functor.

## References

* [Stacks Project, Tag 0B9L](https://stacks.math.columbia.edu/tag/0B9L)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.PicardFunctor

variable (B : BigFppfSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : B.obj hX ⟶ B.obj hS)

/-! ### Functoriality of the base change -/

/-- The base change of the identity of a test scheme is the identity of `X_T`. -/
@[simp]
theorem baseChangeMap_id (T : BigFppfOver B S hS) :
    baseChangeMap B hX hS f (𝟙 T) = 𝟙 (baseChange B hX hS f T) := by
  simp only [baseChangeMap, Over.id_left]
  exact pullback.map_id

/-- The base change of a composite of morphisms of test schemes is the composite of the base
changes. -/
theorem baseChangeMap_comp {T U V : BigFppfOver B S hS} (g : T ⟶ U) (h : U ⟶ V) :
    baseChangeMap B hX hS f (g ≫ h) =
      baseChangeMap B hX hS f g ≫ baseChangeMap B hX hS f h := by
  simp only [baseChangeMap, Over.comp_left, Functor.map_comp]
  rw [pullback.map_comp]
  simp

/-! ### The presheaf of Picard groups of the base changes -/

/-- The Picard group `Pic(X_T)` of the base change of `X ⟶ S` along a test scheme `T`: the
group of isomorphism classes of invertible modules on `X ×_S T`. -/
abbrev picardAt (T : BigFppfOver B S hS) : Type (u + 1) :=
  Stacks.Picard.ofScheme (baseChange B hX hS f T)

/-- Pullback of Picard classes along a morphism `g : T ⟶ U` of test schemes: pullback along the
transition map `X_T ⟶ X_U` of the two base changes. -/
abbrev picardMap {T U : BigFppfOver B S hS} (g : T ⟶ U) :
    picardAt B hX hS f U → picardAt B hX hS f T :=
  Stacks.Picard.schemePullbackClass (baseChangeMap B hX hS f g)

/-- Pullback of Picard classes along a morphism of test schemes is additive. -/
theorem picardMap_add {T U : BigFppfOver B S hS} (g : T ⟶ U) (x y : picardAt B hX hS f U) :
    picardMap B hX hS f g (x + y) = picardMap B hX hS f g x + picardMap B hX hS f g y :=
  Stacks.Picard.schemePullbackClass_add _ x y

/-- Pullback of Picard classes along a morphism of test schemes, as a homomorphism of abelian
groups. -/
abbrev picardMapHom {T U : BigFppfOver B S hS} (g : T ⟶ U) :
    picardAt B hX hS f U →+ picardAt B hX hS f T :=
  Stacks.Picard.schemePullbackClassHom (baseChangeMap B hX hS f g)

/-- Pullback of Picard classes along the identity of a test scheme is the identity. -/
theorem picardMap_id (T : BigFppfOver B S hS) (x : picardAt B hX hS f T) :
    picardMap B hX hS f (𝟙 T) x = x := by
  change Stacks.Picard.schemePullbackClass (baseChangeMap B hX hS f (𝟙 T)) x = x
  rw [baseChangeMap_id]
  exact Stacks.Picard.schemePullbackClass_id _ x

/-- Pullback of Picard classes along a composite of morphisms of test schemes is the composite
of the pullbacks. -/
theorem picardMap_comp {T U V : BigFppfOver B S hS} (g : T ⟶ U) (h : U ⟶ V)
    (x : picardAt B hX hS f V) :
    picardMap B hX hS f (g ≫ h) x = picardMap B hX hS f g (picardMap B hX hS f h x) := by
  change Stacks.Picard.schemePullbackClass (baseChangeMap B hX hS f (g ≫ h)) x = _
  rw [baseChangeMap_comp]
  exact (Stacks.Picard.schemePullbackClass_comp _ _ x).symm

/-- **Stacks Project, Tag 0B9L.** The presheaf `T ↦ Pic(X_T)` on the `S`-schemes of the site,
whose fppf sheafification is the Picard functor. Its action on a morphism of test schemes is
pullback of Picard classes. -/
@[stacks 0B9L "the presheaf of Picard groups of the base changes"]
def picardPresheaf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) where
  obj T := picardAt B hX hS f T.unop
  map g := TypeCat.ofHom (picardMap B hX hS f g.unop)
  map_id T := ConcreteCategory.hom_ext _ _ (picardMap_id B hX hS f T.unop)
  map_comp g h := ConcreteCategory.hom_ext _ _ (picardMap_comp B hX hS f h.unop g.unop)

/-- The value of the presheaf at a test scheme is the Picard group of the base change. -/
theorem picardPresheaf_obj (T : BigFppfOver B S hS) :
    (picardPresheaf B hX hS f).obj (Opposite.op T) = picardAt B hX hS f T :=
  rfl

/-- The action of the presheaf on a morphism of test schemes is pullback of Picard classes. -/
theorem picardPresheaf_map {T U : BigFppfOver B S hS} (g : T ⟶ U) :
    (picardPresheaf B hX hS f).map (Opposite.op g) = TypeCat.ofHom (picardMap B hX hS f g) :=
  rfl

/-! ### The Picard functor -/

/-- **Stacks Project, Tag 0B9L.** The *Picard functor* `Pic_{X/S} : (Sch/S)_{fppf} ⥤ Sets` of a
morphism `f : X ⟶ S` of a big fppf site: the fppf sheafification of the presheaf
`T ↦ Pic(X_T)` of isomorphism classes of invertible modules on the base changes of `X`. -/
@[stacks 0B9L "the Picard functor", sga "6 X 2.4" "definition of Pic_{X/S}", sga "6 XIII 3.1"]
def picardFunctor : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) :=
  sheafify (BigFppfOver.topology B S hS) (picardPresheaf B hX hS f)

/-- The canonical map from the presheaf of Picard groups of the base changes to the Picard
functor: the unit of the sheafification. It sends the class of an invertible module on `X_T` to
its class in `Pic_{X/S}(T)`. -/
def toPicardFunctor : picardPresheaf B hX hS f ⟶ picardFunctor B hX hS f :=
  toSheafify (BigFppfOver.topology B S hS) (picardPresheaf B hX hS f)

/-- The Picard functor is an fppf sheaf. -/
theorem isSheaf_picardFunctor :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (picardFunctor B hX hS f) :=
  ((presheafToSheaf (BigFppfOver.topology B S hS)
    (Type (u + 1))).obj (picardPresheaf B hX hS f)).property

/-! ### The group law on the values of the Picard functor -/

/-- The presheaf `T ↦ Pic(X_T)` read as a presheaf of abelian groups: its values are the Picard
groups of the base changes and its restriction maps are pullback of Picard classes. -/
def picardAddPresheaf : (BigFppfOver B S hS)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj T := AddCommGrpCat.of (picardAt B hX hS f T.unop)
  map g := AddCommGrpCat.ofHom (picardMapHom B hX hS f g.unop)
  map_id T := by
    ext x
    exact picardMap_id B hX hS f T.unop x
  map_comp g h := by
    ext x
    exact picardMap_comp B hX hS f h.unop g.unop x

/-- Forgetting the group law of the presheaf of Picard groups of the base changes gives back
the presheaf `T ↦ Pic(X_T)`. -/
theorem picardAddPresheaf_comp_forget :
    picardAddPresheaf B hX hS f ⋙ forget AddCommGrpCat.{u + 1} = picardPresheaf B hX hS f :=
  rfl

/-- The Picard functor formed in abelian groups: the fppf sheafification of the presheaf of
Picard groups of the base changes, taken in abelian groups rather than in sets. -/
@[sga "6 XIII 3.1", sga "7 IX 12.1"]
def picardAddFunctor : (BigFppfOver B S hS)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  sheafify (BigFppfOver.topology B S hS) (picardAddPresheaf B hX hS f)

/-- The canonical map from the presheaf of Picard groups of the base changes to the Picard
functor formed in abelian groups: the unit of the sheafification taken in abelian groups. -/
def toPicardAddFunctor : picardAddPresheaf B hX hS f ⟶ picardAddFunctor B hX hS f :=
  toSheafify (BigFppfOver.topology B S hS) (picardAddPresheaf B hX hS f)

/-- The Picard functor is the presheaf of sets underlying the Picard functor formed in abelian
groups: fppf sheafification commutes with forgetting the group law. -/
def picardFunctorIsoPicardAddFunctor :
    picardFunctor B hX hS f ≅ picardAddFunctor B hX hS f ⋙ forget AddCommGrpCat.{u + 1} :=
  sheafifyComposeIso (BigFppfOver.topology B S hS) (forget AddCommGrpCat.{u + 1})
    (picardAddPresheaf B hX hS f)

/-- The group law on a value of the Picard functor, transported from the Picard functor formed
in abelian groups. -/
instance instAddCommGroupPicardFunctorObj (T : BigFppfOver B S hS) :
    AddCommGroup ((picardFunctor B hX hS f).obj (Opposite.op T)) :=
  ((picardFunctorIsoPicardAddFunctor B hX hS f).app (Opposite.op T)).toEquiv.addCommGroup

/-- The comparison with the Picard functor formed in abelian groups carries the canonical map
from the Picard group of a base change to the sheafification unit of the latter. -/
theorem picardFunctorIsoPicardAddFunctor_hom_app_toPicardFunctor (T : BigFppfOver B S hS)
    (x : picardAt B hX hS f T) :
    (picardFunctorIsoPicardAddFunctor B hX hS f).hom.app (Opposite.op T)
        ((toPicardFunctor B hX hS f).app (Opposite.op T) x) =
      (toPicardAddFunctor B hX hS f).app (Opposite.op T) x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (sheafComposeIso_hom_fac (BigFppfOver.topology B S hS) (forget AddCommGrpCat.{u + 1})
      (picardAddPresheaf B hX hS f)) (Opposite.op T)) x

/-- A value of the Picard functor is isomorphic, as an abelian group, to the corresponding
value of the Picard functor formed in abelian groups. -/
def picardFunctorAddEquiv (T : BigFppfOver B S hS) :
    (picardFunctor B hX hS f).obj (Opposite.op T) ≃+
      (picardAddFunctor B hX hS f).obj (Opposite.op T) where
  toFun := ((picardFunctorIsoPicardAddFunctor B hX hS f).app (Opposite.op T)).toEquiv
  invFun := ((picardFunctorIsoPicardAddFunctor B hX hS f).app (Opposite.op T)).toEquiv.symm
  left_inv := Equiv.symm_apply_apply _
  right_inv := Equiv.apply_symm_apply _
  map_add' _ _ := Equiv.apply_symm_apply _ _

/-- The comparison of a value of the Picard functor with the corresponding value of the Picard
functor formed in abelian groups carries the canonical map from the Picard group of a base
change to the sheafification unit. -/
theorem picardFunctorAddEquiv_toPicardFunctor (T : BigFppfOver B S hS)
    (x : picardAt B hX hS f T) :
    picardFunctorAddEquiv B hX hS f T
        ((toPicardFunctor B hX hS f).app (Opposite.op T) x) =
      (toPicardAddFunctor B hX hS f).app (Opposite.op T) x :=
  picardFunctorIsoPicardAddFunctor_hom_app_toPicardFunctor B hX hS f T x

/-- The canonical map from the Picard group of a base change to the Picard functor sends the
trivial class to zero. -/
theorem toPicardFunctor_app_zero (T : BigFppfOver B S hS) :
    (toPicardFunctor B hX hS f).app (Opposite.op T) (0 : picardAt B hX hS f T) = 0 := by
  apply (picardFunctorAddEquiv B hX hS f T).injective
  rw [map_zero, picardFunctorAddEquiv_toPicardFunctor]
  exact map_zero _

/-- The canonical map from the Picard group of a base change to the Picard functor is
additive. -/
theorem toPicardFunctor_app_add (T : BigFppfOver B S hS) (x y : picardAt B hX hS f T) :
    (toPicardFunctor B hX hS f).app (Opposite.op T) (x + y) =
      (toPicardFunctor B hX hS f).app (Opposite.op T) x +
        (toPicardFunctor B hX hS f).app (Opposite.op T) y := by
  apply (picardFunctorAddEquiv B hX hS f T).injective
  rw [map_add, picardFunctorAddEquiv_toPicardFunctor, picardFunctorAddEquiv_toPicardFunctor,
    picardFunctorAddEquiv_toPicardFunctor]
  exact map_add _ x y

/-- The canonical map `Pic(X_T) → Pic_{X/S}(T)` from the Picard group of a base change to the
Picard functor, as a homomorphism of abelian groups. -/
def toPicardFunctorHom (T : BigFppfOver B S hS) :
    picardAt B hX hS f T →+ (picardFunctor B hX hS f).obj (Opposite.op T) where
  toFun := (toPicardFunctor B hX hS f).app (Opposite.op T)
  map_zero' := toPicardFunctor_app_zero B hX hS f T
  map_add' := toPicardFunctor_app_add B hX hS f T

/-- The canonical map `Pic(X_T) → Pic_{X/S}(T)` is the sheafification unit on elements. -/
theorem toPicardFunctorHom_apply (T : BigFppfOver B S hS) (x : picardAt B hX hS f T) :
    toPicardFunctorHom B hX hS f T x = (toPicardFunctor B hX hS f).app (Opposite.op T) x :=
  rfl

/-- The canonical map to the Picard functor commutes with restriction along a morphism of test
schemes: pulling a Picard class of `X_U` back to `X_T` and then taking its class in the Picard
functor is restricting its class along `T ⟶ U`. -/
theorem toPicardFunctor_app_naturality {T U : BigFppfOver B S hS} (g : T ⟶ U)
    (x : picardAt B hX hS f U) :
    (toPicardFunctor B hX hS f).app (Opposite.op T) (picardMap B hX hS f g x) =
      (picardFunctor B hX hS f).map (Opposite.op g)
        ((toPicardFunctor B hX hS f).app (Opposite.op U) x) :=
  ConcreteCategory.congr_hom
    ((toPicardFunctor B hX hS f).naturality (Opposite.op g)) x

end Stacks.PicardFunctor

end
