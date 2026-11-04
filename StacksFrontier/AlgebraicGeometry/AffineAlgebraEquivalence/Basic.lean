module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Topology.Sheaves.Functors
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.QuasicoherentSquare

/-!
# Affine morphisms and quasi-coherent algebras

Schemes affine over a scheme `S` are anti-equivalent to quasi-coherent sheaves of commutative
`𝒪_S`-algebras; under the anti-equivalence an affine morphism `f : X ⟶ S` corresponds to
`f_* 𝒪_X`, and the anti-equivalence commutes with arbitrary base change.

This file sets up the vocabulary of that statement, packages it as the structure
`AffineAlgebraAntiEquivalence`, and constructs the parts of such a structure that do not need
the relative spectrum: the algebra-pullback functor together with its universal property, and
the pushforward functor `X ↦ f_* 𝒪_X` which is the functor underlying the anti-equivalence.

## Main definitions

* `IsAffineHomOver` and `AffineOver` are the property of being affine over `S` and the category
  of schemes affine over `S`.
* `IsQuasicoherentAlgebra` and `QuasicoherentAlgebra` are quasi-coherence of an algebra sheaf
  and the category of quasi-coherent algebra sheaves.
* `pushforwardAlgebra` is the `𝒪_S`-algebra `f_* 𝒪_X` of a morphism `f : X ⟶ S`, and
  `pushforwardAlgebraMap` is the canonical contravariant map on pushed-forward structure
  sheaves induced by a morphism over `S`.
* `pushforwardAlgebraFunctor` assembles these into a functor `(Over S)ᵒᵖ ⥤ AlgebraSheaf S`,
  and `affinePushforwardAlgebraFunctor` restricts it to the affine objects.
* `algebraPullback` is pullback of algebra sheaves along `g : T ⟶ S`, i.e. extension of
  scalars `g⁻¹ A ⊗_{g⁻¹ 𝒪_S} 𝒪_T`, with `algebraPullbackMap` the canonical map from the
  inverse image.
* `affineBaseChange` is base change of schemes restricted to the affine objects, and
  `pushforwardBaseChangeMap` is the canonical comparison from the inverse image of a
  pushed-forward structure sheaf to the pushforward along the base-changed morphism.
* `AffineAlgebraAntiEquivalence` packages the anti-equivalence, its identification with
  pushforward of structure sheaves, and its base-change compatibility.

## Main results

* `algebraPullback_isPushout` is the universal property of `algebraPullback`: it exhibits the
  pullback of an algebra as the extension of scalars of its inverse image along
  `g⁻¹ 𝒪_S ⟶ 𝒪_T`.
* `pushforwardAlgebraMap_id` and `pushforwardAlgebraMap_comp` are the functoriality of the
  canonical map on pushed-forward structure sheaves.

## Implementation notes

The inverse-image algebra along `g : T ⟶ S` is characterized intrinsically as the pushout of
`g⁻¹ A` and `𝒪_T` over `g⁻¹ 𝒪_S`; this avoids choosing a particular construction of pushouts
in the category of sheaves of commutative rings. The construction itself is nevertheless
available, because `TopCat.Sheaf CommRingCat X` is by definition the category of
`CommRingCat`-valued sheaves for the Grothendieck topology of the opens of `X`, which has
every colimit that `CommRingCat` has; this is recorded as
`hasPushouts_topCatSheafCommRingCat`, after which `algebraPullback` is literally
`Under.post (TopCat.Sheaf.pullback CommRingCat g.base) ⋙ Under.pushout _` and its universal
property is `IsPushout.of_hasPushout`.

Functoriality of `pushforwardAlgebraMap` is proved by computing its sections over an open `U`
of `S`. The definition carries an `eqToHom` transporting along `Over.w`, which is removed by
`pushforwardAlgebraMap_app`: that lemma is stated for a general morphism `q` together with a
proof `u ≫ p = q`, so that the equality can be substituted away, after which the sections of
the map are the canonical `Scheme.Hom.appLE` of the morphism over `S`. Functoriality is then
`Scheme.Hom.id_app` and `Scheme.Hom.appLE_comp_appLE`.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.AffineAlgebraEquivalence

/-! ### The two categories -/

/-- Quasi-coherence as an object property on algebra sheaves. -/
public abbrev IsQuasicoherentAlgebra (S : Scheme.{u}) :
    ObjectProperty (Stacks.RelativeSpec.AlgebraSheaf S) :=
  Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent

/-- The category of quasi-coherent sheaves of commutative `𝒪_S`-algebras. -/
public abbrev QuasicoherentAlgebra (S : Scheme.{u}) :=
  (IsQuasicoherentAlgebra S).FullSubcategory

/-! ### Pushforward of structure sheaves -/

/-- The `𝒪_S`-algebra `f_* 𝒪_X` associated to a morphism `f : X ⟶ S`. -/
public noncomputable def pushforwardAlgebra {X S : Scheme.{u}} (f : X ⟶ S) :
    Stacks.RelativeSpec.AlgebraSheaf S :=
  Under.mk (Y := (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf) ⟨f.c⟩

/-- The canonical map `p_* 𝒪_Y ⟶ (u ≫ p)_* 𝒪_X` of `𝒪_S`-algebras attached to a morphism
`u : X ⟶ Y` and a morphism `p : Y ⟶ S`. This is `pushforwardAlgebraMap` with the structure
morphism of the source left in composite form, so that no transport is involved. -/
public noncomputable def pushforwardAlgebraMapAux {X Y S : Scheme.{u}} (p : Y ⟶ S)
    (u : X ⟶ Y) : pushforwardAlgebra p ⟶ pushforwardAlgebra (u ≫ p) :=
  Under.homMk ((TopCat.Sheaf.pushforward CommRingCat p.base).map
    (⟨u.c⟩ : Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat u.base).obj X.sheaf)) (by rfl)

/-- A morphism of schemes over `S` induces the canonical map in the opposite
direction between their pushed-forward structure sheaves. -/
public noncomputable def pushforwardAlgebraMap {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) : pushforwardAlgebra Y.hom ⟶ pushforwardAlgebra X.hom :=
  pushforwardAlgebraMapAux Y.hom f.left ≫ eqToHom (congrArg pushforwardAlgebra (Over.w f))

/-- The sections over an open `U` of `S` of the canonical map
`pushforwardAlgebraMapAux p u`, transported along an identification `u ≫ p = q` of the
structure morphism of the source: they are the canonical map `Γ(Y, p⁻¹U) ⟶ Γ(X, q⁻¹U)`. -/
public theorem pushforwardAlgebraMapAux_app {X Y S : Scheme.{u}} (p : Y ⟶ S) (u : X ⟶ Y)
    (q : X ⟶ S) (h : u ≫ p = q) (U : S.Opens) (hle : q ⁻¹ᵁ U ≤ u ⁻¹ᵁ (p ⁻¹ᵁ U)) :
    (pushforwardAlgebraMapAux p u ≫
        eqToHom (congrArg pushforwardAlgebra h)).right.hom.app (op U) =
      u.appLE (p ⁻¹ᵁ U) (q ⁻¹ᵁ U) hle := by
  subst h
  rw [show u.appLE (p ⁻¹ᵁ U) ((u ≫ p) ⁻¹ᵁ U) hle = u.app (p ⁻¹ᵁ U) from u.appLE_eq_app]
  rfl

/-- The preimage of an open of the base under the structure morphism of the source of a
morphism over `S` is contained in the preimage of its preimage under the target's structure
morphism. -/
public theorem preimage_le_preimage_preimage {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (U : S.Opens) : X.hom ⁻¹ᵁ U ≤ f.left ⁻¹ᵁ (Y.hom ⁻¹ᵁ U) := by
  rw [← Over.w f]; exact le_rfl

/-- The sections of `pushforwardAlgebraMap f` over an open `U` of `S` are the canonical map
`Γ(Y, Y.hom⁻¹U) ⟶ Γ(X, X.hom⁻¹U)` induced by `f`. -/
public theorem pushforwardAlgebraMap_app {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (U : S.Opens) (hle : X.hom ⁻¹ᵁ U ≤ f.left ⁻¹ᵁ (Y.hom ⁻¹ᵁ U)) :
    (pushforwardAlgebraMap f).right.hom.app (op U)
      = f.left.appLE (Y.hom ⁻¹ᵁ U) (X.hom ⁻¹ᵁ U) hle :=
  pushforwardAlgebraMapAux_app Y.hom f.left X.hom (Over.w f) U hle

/-- The canonical map on pushed-forward structure sheaves of an identity is the identity. -/
public theorem pushforwardAlgebraMap_id {S : Scheme.{u}} (X : Over S) :
    pushforwardAlgebraMap (𝟙 X) = 𝟙 (pushforwardAlgebra X.hom) := by
  ext1
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun V => ?_)
  obtain ⟨U⟩ := V
  rw [pushforwardAlgebraMap_app (𝟙 X) U (preimage_le_preimage_preimage _ _)]
  simp only [Scheme.Hom.appLE, Over.id_left, AlgebraicGeometry.Scheme.Hom.id_app]
  exact X.left.presheaf.map_id _

/-- The canonical map on pushed-forward structure sheaves is contravariantly functorial. -/
public theorem pushforwardAlgebraMap_comp {S : Scheme.{u}} {X Y Z : Over S} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    pushforwardAlgebraMap (f ≫ g) = pushforwardAlgebraMap g ≫ pushforwardAlgebraMap f := by
  ext1
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun V => ?_)
  obtain ⟨U⟩ := V
  have h1 : ((pushforwardAlgebraMap g ≫ pushforwardAlgebraMap f).right.hom.app (op U))
      = (pushforwardAlgebraMap g).right.hom.app (op U) ≫
        (pushforwardAlgebraMap f).right.hom.app (op U) := rfl
  rw [pushforwardAlgebraMap_app (f ≫ g) U (preimage_le_preimage_preimage _ _), h1,
    pushforwardAlgebraMap_app g U (preimage_le_preimage_preimage _ _),
    pushforwardAlgebraMap_app f U (preimage_le_preimage_preimage _ _)]
  exact (Scheme.Hom.appLE_comp_appLE f.left g.left _ _ _ _ _).symm

/-- The functor `X ↦ f_* 𝒪_X` from schemes over `S`, contravariantly, to sheaves of
commutative `𝒪_S`-algebras. This is the functor underlying the anti-equivalence of
Stacks Tag 01SA. -/
public noncomputable def pushforwardAlgebraFunctor (S : Scheme.{u}) :
    (Over S)ᵒᵖ ⥤ Stacks.RelativeSpec.AlgebraSheaf S where
  obj X := pushforwardAlgebra X.unop.hom
  map f := pushforwardAlgebraMap f.unop
  map_id X := pushforwardAlgebraMap_id X.unop
  map_comp f g := pushforwardAlgebraMap_comp g.unop f.unop

/-- The functor `X ↦ f_* 𝒪_X` restricted to the schemes affine over `S`. -/
public noncomputable def affinePushforwardAlgebraFunctor (S : Scheme.{u}) :
    (AffineOver S)ᵒᵖ ⥤ Stacks.RelativeSpec.AlgebraSheaf S :=
  (IsAffineHomOver S).ι.op ⋙ pushforwardAlgebraFunctor S

/-! ### Inverse image and pullback of algebra sheaves -/

/-- Pushouts exist in the category of sheaves of commutative rings on a topological space:
`TopCat.Sheaf C X` is by definition the category of `C`-valued sheaves for the Grothendieck
topology on the opens of `X`, which has all colimits that `C` has because sheafification
exists. -/
public noncomputable instance hasPushouts_topCatSheafCommRingCat (X : TopCat.{u}) :
    HasPushouts (TopCat.Sheaf CommRingCat.{u} X) :=
  inferInstanceAs
    (HasPushouts (Sheaf (_root_.Opens.grothendieckTopology X) CommRingCat.{u}))

/-- Pullback of algebra sheaves along a morphism of schemes `g : T ⟶ S`: the `𝒪_T`-algebra
`g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T`, obtained by taking the inverse image of `A` as a sheaf of rings over
`g⁻¹𝒪_S` and then pushing out along `g⁻¹𝒪_S ⟶ 𝒪_T`. -/
public noncomputable def algebraPullback {T S : Scheme.{u}} (g : T ⟶ S) :
    Stacks.RelativeSpec.AlgebraSheaf S ⥤ Stacks.RelativeSpec.AlgebraSheaf T :=
  Under.post (TopCat.Sheaf.pullback CommRingCat g.base) ⋙
    Under.pushout (inverseImageStructureMap g)

/-- The canonical map from the inverse image of an algebra sheaf to its pullback. -/
public noncomputable def algebraPullbackMap {T S : Scheme.{u}} (g : T ⟶ S) :
    Under.post (TopCat.Sheaf.pullback CommRingCat g.base) ⋙ Under.forget _ ⟶
      algebraPullback g ⋙ Under.forget _ where
  app _ := Limits.pushout.inl _ _
  naturality _ _ _ := (Limits.pushout.inl_desc _ _ _).symm

/-- Algebra pullback is extension of scalars from `g⁻¹ 𝒪_S` to `𝒪_T`: the pullback of `A`
along `g` is `g⁻¹ A ⊗_{g⁻¹ 𝒪_S} 𝒪_T`. -/
public theorem algebraPullback_isPushout {T S : Scheme.{u}} (g : T ⟶ S)
    (A : Stacks.RelativeSpec.AlgebraSheaf S) :
    IsPushout
      ((TopCat.Sheaf.pullback CommRingCat g.base).map A.hom)
      (inverseImageStructureMap g)
      ((algebraPullbackMap g).app A)
      ((algebraPullback g).obj A).hom :=
  IsPushout.of_hasPushout _ _

/-- The inverse-image comparison `g⁻¹(f_* 𝒪_X) ⟶ f'_* 𝒪_{X ×_S T}`. It is adjoint to the map
on structure sheaves induced by the projection `X ×_S T ⟶ X`. -/
public noncomputable def pushforwardBaseChangeMap {T S : Scheme.{u}} (g : T ⟶ S)
    (X : Over S) :
    (TopCat.Sheaf.pullback CommRingCat g.base).obj (pushforwardAlgebra X.hom).right ⟶
      (pushforwardAlgebra ((Over.pullback g).obj X).hom).right :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g.base).homEquiv
    (pushforwardAlgebra X.hom).right
    (pushforwardAlgebra ((Over.pullback g).obj X).hom).right).symm
      (pushforwardAlgebraMap
        (Over.homMk (V := X) (U := Over.mk (Limits.pullback.snd X.hom g ≫ g))
          (Limits.pullback.fst X.hom g) Limits.pullback.condition)).right

/-! ### The anti-equivalence -/

/-- A base-change-compatible anti-equivalence between affine schemes over a base and
quasi-coherent algebra sheaves on that base.

The maps `algebraPullbackMap` exhibit algebra pullback as extension of scalars: the
accompanying `IsPushout` field says that its value on `A` is `g⁻¹ A ⊗_{g⁻¹ 𝒪_S} 𝒪_T`. -/
public structure AffineAlgebraAntiEquivalence where
  /-- Pullback of algebra sheaves along a morphism of schemes. -/
  algebraPullback : ∀ {T S : Scheme.{u}} (_g : T ⟶ S),
    Stacks.RelativeSpec.AlgebraSheaf S ⥤ Stacks.RelativeSpec.AlgebraSheaf T
  /-- The canonical map from the inverse image of an algebra to its pullback. -/
  algebraPullbackMap : ∀ {T S : Scheme.{u}} (g : T ⟶ S),
    Under.post (TopCat.Sheaf.pullback CommRingCat g.base) ⋙ Under.forget _ ⟶
      algebraPullback g ⋙ Under.forget _
  /-- Algebra pullback is extension of scalars from `g⁻¹ 𝒪_S` to `𝒪_T`. -/
  algebraPullback_isPushout : ∀ {T S : Scheme.{u}} (g : T ⟶ S)
      (A : Stacks.RelativeSpec.AlgebraSheaf S),
    IsPushout
      ((TopCat.Sheaf.pullback CommRingCat g.base).map A.hom)
      (inverseImageStructureMap g)
      ((algebraPullbackMap g).app A)
      ((algebraPullback g).obj A).hom
  /-- Pullback of a quasi-coherent algebra is quasi-coherent. -/
  algebraPullback_isQuasicoherent : ∀ {T S : Scheme.{u}} (g : T ⟶ S)
      (A : QuasicoherentAlgebra S),
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent ((algebraPullback g).obj A.obj)
  /-- The anti-equivalence over every base scheme. -/
  equivalence : ∀ S : Scheme.{u}, (AffineOver S)ᵒᵖ ≌ QuasicoherentAlgebra S
  /-- Under the anti-equivalence, `f : X ⟶ S` corresponds to `f_* 𝒪_X`. -/
  pushforwardIso : ∀ (S : Scheme.{u}) (X : AffineOver S),
    ((IsQuasicoherentAlgebra S).ι.obj ((equivalence S).functor.obj (.op X))) ≅
      pushforwardAlgebra X.obj.hom
  /-- The preceding identifications are natural: the equivalence acts on a morphism over `S`
  by the canonical contravariant map on pushed-forward structure sheaves. -/
  pushforwardIso_naturality : ∀ (S : Scheme.{u}) {X Y : AffineOver S} (f : X ⟶ Y),
    (IsQuasicoherentAlgebra S).ι.map ((equivalence S).functor.map f.op) ≫
        (pushforwardIso S X).hom =
      (pushforwardIso S Y).hom ≫
        pushforwardAlgebraMap ((IsAffineHomOver S).ι.map f)
  /-- The anti-equivalence commutes naturally with arbitrary base change. -/
  baseChangeIso : ∀ {T S : Scheme.{u}} (g : T ⟶ S),
    let F : QuasicoherentAlgebra S ⥤ QuasicoherentAlgebra T :=
      ObjectProperty.lift _ ((IsQuasicoherentAlgebra S).ι ⋙ algebraPullback g)
        (algebraPullback_isQuasicoherent g)
    (equivalence S).functor ⋙ F ≅
      (affineBaseChange g).op ⋙ (equivalence T).functor
  /-- After identifying the equivalence with pushforward, base change is the canonical
  comparison induced by the fibre-product projection. The pushout property of algebra
  pullback uniquely determines the algebra map from this equality on inverse-image
  sheaves. -/
  baseChangeIso_canonical : ∀ {T S : Scheme.{u}} (g : T ⟶ S) (X : AffineOver S),
    (algebraPullbackMap g).app ((equivalence S).functor.obj (.op X)).obj ≫
        ((IsQuasicoherentAlgebra T).ι.map ((baseChangeIso g).hom.app (.op X)) ≫
          (pushforwardIso T ((affineBaseChange g).obj X)).hom).right =
      (TopCat.Sheaf.pullback CommRingCat g.base).map (pushforwardIso S X).hom.right ≫
        pushforwardBaseChangeMap g X.obj

end Stacks.AffineAlgebraEquivalence

end
