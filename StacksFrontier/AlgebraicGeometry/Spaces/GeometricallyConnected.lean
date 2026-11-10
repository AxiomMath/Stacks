module

public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Connected.OpenConnectedFibres
public import StacksFrontier.AlgebraicGeometry.Size.Pullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.PointsRelocalized
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Open
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedAffine
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleGaloisAction
public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrict
public import StacksFrontier.RingTheory.GeometricallyConnected

/-!
# Geometrically connected algebraic spaces

An algebraic space over a field `k` can be connected and become disconnected after extending
the ground field. It is *geometrically connected* when this does not happen: when the base
change `X_{k'}` is connected for every field extension `k'/k`.

An algebraic space over `k` is a presheaf on the big fppf site over `Spec k`, and its base
change along a field extension is restriction along the induced morphism of spectra, so
geometric connectedness is a condition on the point sets of Tag 03BU with the topology of
Tag 03BX, which here is the explicit topology
`AlgebraicGeometry.Space.pointTopology`. The field extensions range over those whose spectra
are objects of the chosen big fppf site, which is where the base change is defined.

For a Galois extension `K/k` the opposite group of `k`-algebra automorphisms of `K` acts on
`Spec K` over `Spec k`, and hence on the base change `X_K` viewed again as a presheaf over
`k`. The action changes only the `K`-coordinate of a section, so it is constructed here from a
general twisting construction: an endomorphism `t` of the base with `t ≫ f = f` twists the
unit of the relocalization adjunction into an endomorphism of `j_! j^{-1} X`.

## Main definitions

* `CategoryTheory.OverShriek.relocalizeTwist` is the endomorphism of `j_! j^{-1} X` attached
  to an endomorphism of the base over `U`.
* `CategoryTheory.OverShriek.relocalizeRestrictCounit` is the canonical morphism
  `j_! j^{-1} X ⟶ X`, and `CategoryTheory.OverShriek.toYonedaMkId` the morphism from a
  presheaf to the representable presheaf of the slice's terminal object.
* `AlgebraicGeometry.Space.fieldExtensionMap` is the morphism `Spec K ⟶ Spec k` of the
  chosen big fppf site induced by a field extension `K/k`.
* `AlgebraicGeometry.Space.IsGeometricallyConnected` is geometric connectedness of a
  presheaf on the big fppf site over a field.
* `AlgebraicGeometry.Space.pointsOfRelocalizeRestrict` is the map on point sets induced by
  restricting a presheaf to a smaller base, and
  `AlgebraicGeometry.Space.pointsOverMap` is its represented counterpart.
* `AlgebraicGeometry.Space.relocalizedPointsHomeo` is the homeomorphism between the points of
  a presheaf and those of its lower-shriek extension to a larger base.
* `AlgebraicGeometry.Space.siteMapAlgAut` is the automorphism of the site object `Spec K`
  attached to a `k`-algebra automorphism of `K`.
* `AlgebraicGeometry.Space.galoisActionOnBaseChange` is the action of the opposite
  automorphism group on the base change of a presheaf, viewed over `k`.

## Main results

* `AlgebraicGeometry.Space.continuous_pointsOfRelocalizeRestrict`: restriction to a smaller
  base is continuous on points.
* `AlgebraicGeometry.Space.exists_fieldExtension_common`: two field extensions of `k` inside
  the chosen big fppf site have a common extension inside it.
* `AlgebraicGeometry.Space.isGeometricallyConnected_iff_relocalizeRestrict`: **Stacks 0A10**,
  geometric connectedness is unchanged by extending the ground field.
* `AlgebraicGeometry.Space.galoisActionOnBaseChange_ρ_app_fst` and
  `AlgebraicGeometry.Space.galoisActionOnBaseChange_ρ_app_snd` describe the action on both
  coordinates of a section.
* `CategoryTheory.OverShriek.isPullback_relocalizeRestrictCounit`: the restriction of `X` to a
  smaller base, viewed again over the original one, is the product of `X` with that base.
* `AlgebraicGeometry.Space.bijective_connectedComponents_pullback_of_isGeometricallyConnected`:
  **Stacks 0A11**, the projection from a product with a geometrically connected algebraic
  space is a bijection on connected components.
* `AlgebraicGeometry.Space.isGeometricallyConnected_yoneda_fieldExtensionMap`: over a
  separably closed field the spectrum of a field extension is geometrically connected.
* `AlgebraicGeometry.Space.bijective_connectedComponents_relocalizeRestrict_of_isSepClosed`
  and `AlgebraicGeometry.Space.isGeometricallyConnected_iff_connectedSpace_of_isSepClosed`:
  **Stacks 0A12**, extending a separably closed ground field is a bijection on connected
  components, and over such a field geometric connectedness is connectedness.
* `AlgebraicGeometry.Space.isGeometricallyConnected_iff_connectedSpace_sepClosure`:
  **Stacks 0A13**, geometric connectedness is tested by one base change to a separable
  algebraic closure.

## Implementation notes

The topology used throughout is `AlgebraicGeometry.Space.pointTopology`, which is defined for
an arbitrary presheaf and is the topology of Tag 03BX on an algebraic space
(`AlgebraicGeometry.Space.PointTopologyFamily.topology_eq`). Consequently the definition of
geometric connectedness, and the transfer of connectedness along an isomorphism of presheaves,
need no algebraicity hypothesis; only the surjectivity of an étale atlas on points does.

A section of `j_! j^{-1} X` over a `k`-scheme `W` is a factorization `ψ : W ⟶ Spec K` of the
structure morphism of `W` together with a section of `X` over `(W, ψ ≫ f)`. The twist composes
`ψ` with the automorphism and leaves the section untouched; the statement of the second
component is heterogeneous because its type is indexed by the first.

The same description makes the base change of `X` to `K`, viewed again over `k`, the product
of `X` with `Spec K`: the factorization is a `K`-point of `W` and the section is a section of
`X`. That is `CategoryTheory.OverShriek.isPullback_relocalizeRestrictCounit`, stated over any
presheaf with subsingleton sections, and it is what reduces Tag 0A12 to Tag 0A11.

`AlgebraicGeometry.Space.relocalizedPointsHomeo` repeats, for the point topologies, the
bijection of `AlgebraicGeometry.Space.relocalizedPointsEquiv`. It is constructed from the
uniqueness in Tag 03BX as an inducing bijection, so that its underlying map is the transport
of field-valued points itself; that is what lets the map `|X_K| → |X|` of
`AlgebraicGeometry.Space.pointsOfRelocalizeRestrict` be identified with a projection from a
product.

## References

* [Stacks Project, Tag 0A0Z](https://stacks.math.columbia.edu/tag/0A0Z)
* [Stacks Project, Tag 0A10](https://stacks.math.columbia.edu/tag/0A10)
* [Stacks Project, Tag 0A11](https://stacks.math.columbia.edu/tag/0A11)
* [Stacks Project, Tag 0A12](https://stacks.math.columbia.edu/tag/0A12)
* [Stacks Project, Tag 0A13](https://stacks.math.columbia.edu/tag/0A13)
* [Stacks Project, Tag 0A14](https://stacks.math.columbia.edu/tag/0A14)
* [Stacks Project, Tag 0378](https://stacks.math.columbia.edu/tag/0378)
* [Stacks Project, Tag 037U](https://stacks.math.columbia.edu/tag/037U)
* [Stacks Project, Tag 0386](https://stacks.math.columbia.edu/tag/0386)
* [Stacks Project, Tag 06DN](https://stacks.math.columbia.edu/tag/06DN)
-/

@[expose] public section

open CategoryTheory Cardinal Opposite
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe w v u

namespace CategoryTheory.OverShriek

/-- Applying a natural transformation given by an equality of presheaves is a cast. -/
private theorem eqToHom_app_cast {D : Type u} [Category.{v} D] {F F' : Dᵒᵖ ⥤ Type w}
    (h : F = F') (W : Dᵒᵖ) (x : F.obj W) :
    (eqToHom h).app W x = cast (congrArg (fun Q ↦ Q.obj W) h) x := by
  cases h
  rfl

/-- Applying a morphism of types given by an equality is a cast. -/
private theorem typeEqToHom_apply_cast {α β : Type w} (h : α = β) (x : α) :
    (eqToHom h : α ⟶ β) x = cast h x := by
  cases h
  rfl

variable {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U) (X : (Over U)ᵒᵖ ⥤ Type v)

/-- Restriction along a composite of two localization functors is the composite of the
restrictions. -/
def relocalizeRestrictComp {U₀ U₁ U₂ : C} (g₁ : U₂ ⟶ U₁) (g₂ : U₁ ⟶ U₀)
    (F : (Over U₀)ᵒᵖ ⥤ Type v) :
    (relocalizeRestrict g₁).obj ((relocalizeRestrict g₂).obj F) ≅
      (relocalizeRestrict (g₁ ≫ g₂)).obj F := by
  dsimp [relocalizeRestrict]
  exact (Functor.associator (Over.map g₁).op (Over.map g₂).op F).symm ≪≫
    Functor.isoWhiskerRight (NatIso.op (Over.mapComp g₁ g₂)) F

/-! ### Twisting the lower-shriek extension by an endomorphism of the base -/

/-- An endomorphism `t` of `V` over `U` does not change the localization functor
`Over.map f`. -/
theorem overMap_comp_eq (t : V ⟶ V) (ht : t ≫ f = f) : Over.map t ⋙ Over.map f = Over.map f :=
  calc Over.map t ⋙ Over.map f = Over.map (t ≫ f) := (Over.mapComp_eq t f).symm
    _ = Over.map f := congrArg Over.map ht

/-- Restriction along `Over.map f` is unchanged by further restricting along `Over.map t`, for
an endomorphism `t` of `V` over `U`. -/
theorem relocalizeRestrict_twist_eq (t : V ⟶ V) (ht : t ≫ f = f) (Y : (Over U)ᵒᵖ ⥤ Type v) :
    (Over.map t).op ⋙ ((Over.map f).op ⋙ Y) = (Over.map f).op ⋙ Y := by
  have hop : (Over.map t).op ⋙ (Over.map f).op = (Over.map f).op := by
    change (Over.map t ⋙ Over.map f).op = (Over.map f).op
    exact congrArg Functor.op (overMap_comp_eq f t ht)
  exact (Functor.assoc _ _ _).symm.trans (congrArg (fun F ↦ F ⋙ Y) hop)

/-- The unit of the relocalization adjunction, twisted by an endomorphism `t` of `V` over
`U`. -/
def relocalizeTwistRestricted (t : V ⟶ V) (ht : t ≫ f = f) :
    (Over.map f).op ⋙ X ⟶
      (Over.map f).op ⋙ (relocalizePresheafFunctor f).obj ((Over.map f).op ⋙ X) :=
  eqToHom (relocalizeRestrict_twist_eq f t ht X).symm ≫
    Functor.whiskerLeft (Over.map t).op
      ((relocalizeAdjunction f).unit.app ((Over.map f).op ⋙ X)) ≫
    eqToHom (relocalizeRestrict_twist_eq f t ht
      ((relocalizePresheafFunctor f).obj ((Over.map f).op ⋙ X)))

/-- **The twist of the lower-shriek extension by an endomorphism of the base.** An
endomorphism `t` of `V` over `U` induces an endomorphism of `j_! j^{-1} X` which composes the
factorization recorded by a section with `t` and leaves the section itself alone. -/
def relocalizeTwist (t : V ⟶ V) (ht : t ≫ f = f) :
    (relocalizePresheafFunctor f).obj ((Over.map f).op ⋙ X) ⟶
      (relocalizePresheafFunctor f).obj ((Over.map f).op ⋙ X) :=
  relocalizeOfRestricted f (relocalizeTwistRestricted f X t ht)

private theorem relocalizeTwistRestricted_app (t : V ⟶ V) (ht : t ≫ f = f) (W : Over V)
    (s : ((Over.map f).op ⋙ X).obj (op W)) :
    (relocalizeTwistRestricted f X t ht).app (op W) s =
      (eqToHom (relocalizeRestrict_twist_eq f t ht
        ((relocalizePresheafFunctor f).obj ((Over.map f).op ⋙ X)))).app (op W)
        (((relocalizeAdjunction f).unit.app ((Over.map f).op ⋙ X)).app
          ((Over.map t).op.obj (op W))
          ((eqToHom (relocalizeRestrict_twist_eq f t ht X).symm).app (op W) s)) := rfl

private theorem relocalizeCastFst (G : (Over V)ᵒᵖ ⥤ Type v) {W W' : (Over U)ᵒᵖ} (h : W = W')
    (x : ((relocalizePresheafFunctor f).obj G).obj W) :
    HEq ((cast (congrArg (fun Z ↦ ((relocalizePresheafFunctor f).obj G).obj Z) h) x).val.1)
      x.val.1 := by
  cases h
  rfl

private theorem relocalizeCastSnd (G : (Over V)ᵒᵖ ⥤ Type v) {W W' : (Over U)ᵒᵖ} (h : W = W')
    (x : ((relocalizePresheafFunctor f).obj G).obj W) :
    HEq ((cast (congrArg (fun Z ↦ ((relocalizePresheafFunctor f).obj G).obj Z) h) x).val.2)
      x.val.2 := by
  cases h
  rfl

private theorem relocalizeTwistOutputEq_index (t : V ⟶ V) (ht : t ≫ f = f) (W : Over V) :
    congrArg (fun F ↦ F.obj (op W)) (relocalizeRestrict_twist_eq f t ht
        ((relocalizePresheafFunctor f).obj ((Over.map f).op ⋙ X))) =
      congrArg (fun Z ↦ ((relocalizePresheafFunctor f).obj ((Over.map f).op ⋙ X)).obj Z)
        (congrArg op
          (congrArg (fun F : Over V ⥤ Over U ↦ F.obj W) (overMap_comp_eq f t ht))) :=
  Subsingleton.elim _ _

private theorem relocalizeTwistRestricted_fst (t : V ⟶ V) (ht : t ≫ f = f) (W : Over V)
    (s : ((Over.map f).op ⋙ X).obj (op W)) :
    HEq (((relocalizeTwistRestricted f X t ht).app (op W) s).val.1)
      ((((relocalizeAdjunction f).unit.app ((Over.map f).op ⋙ X)).app
        ((Over.map t).op.obj (op W))
        ((eqToHom (relocalizeRestrict_twist_eq f t ht X).symm).app (op W) s)).val.1) := by
  rw [relocalizeTwistRestricted_app,
    eqToHom_app_cast (D := Over V) (W := op W)
      (h := relocalizeRestrict_twist_eq f t ht
        ((relocalizePresheafFunctor f).obj ((Over.map f).op ⋙ X))),
    relocalizeTwistOutputEq_index f X t ht W]
  exact relocalizeCastFst f ((Over.map f).op ⋙ X)
    (congrArg op (congrArg (fun F : Over V ⥤ Over U ↦ F.obj W) (overMap_comp_eq f t ht))) _

private theorem relocalizeTwistRestricted_snd (t : V ⟶ V) (ht : t ≫ f = f) (W : Over V)
    (s : ((Over.map f).op ⋙ X).obj (op W)) :
    HEq (((relocalizeTwistRestricted f X t ht).app (op W) s).val.2)
      ((((relocalizeAdjunction f).unit.app ((Over.map f).op ⋙ X)).app
        ((Over.map t).op.obj (op W))
        ((eqToHom (relocalizeRestrict_twist_eq f t ht X).symm).app (op W) s)).val.2) := by
  rw [relocalizeTwistRestricted_app,
    eqToHom_app_cast (D := Over V) (W := op W)
      (h := relocalizeRestrict_twist_eq f t ht
        ((relocalizePresheafFunctor f).obj ((Over.map f).op ⋙ X))),
    relocalizeTwistOutputEq_index f X t ht W]
  exact relocalizeCastSnd f ((Over.map f).op ⋙ X)
    (congrArg op (congrArg (fun F : Over V ⥤ Over U ↦ F.obj W) (overMap_comp_eq f t ht))) _

private theorem relocalizeUnit_eq (G : (Over V)ᵒᵖ ⥤ Type v) :
    (relocalizeAdjunction f).unit.app G =
      relocalizeToRestricted f (𝟙 ((relocalizePresheafFunctor f).obj G)) := by
  simp [relocalizeAdjunction]

private theorem relocalizeUnit_fst (G : (Over V)ᵒᵖ ⥤ Type v) (W : Over V) (s : G.obj (op W)) :
    (((relocalizeAdjunction f).unit.app G).app (op W) s).val.1 = W.hom := by
  rw [relocalizeUnit_eq]
  rfl

private theorem relocalizeUnit_snd (G : (Over V)ᵒᵖ ⥤ Type v) (W : Over V) (s : G.obj (op W)) :
    HEq (((relocalizeAdjunction f).unit.app G).app (op W) s).val.2 s := by
  rw [relocalizeUnit_eq]
  rfl

/-- The descended morphism is the recorded morphism followed by a cast along the comparison of
the object with the recorded factorization. -/
private theorem relocalizeDescend_eq_cast (G : (Over V)ᵒᵖ ⥤ Type v)
    (β : G ⟶ (relocalizeRestrict f).obj ((relocalizePresheafFunctor f).obj G))
    {W : Over U} (p : ((relocalizePresheafFunctor f).obj G).obj (op W))
    (h : p.val.1 ≫ f = W.hom) :
    ∃ hW : W = Over.mk (p.val.1 ≫ f), relocalizeDescend f β h p.val.2 =
      cast (congrArg (fun Z ↦ ((relocalizePresheafFunctor f).obj G).obj Z)
        (congrArg op hW.symm)) (β.app (op (Over.mk p.val.1)) p.val.2) := by
  have hW : W = Over.mk (p.val.1 ≫ f) :=
    CostructuredArrow.obj_ext W (Over.mk (p.val.1 ≫ f)) rfl (by simpa using h)
  have hm : (Over.homMk (𝟙 W.left) (by simpa using h) : W ⟶ Over.mk (p.val.1 ≫ f)) =
      eqToHom hW := Over.OverMorphism.ext (by simp)
  refine ⟨hW, ?_⟩
  change (((relocalizePresheafFunctor f).obj G).map
      (Over.homMk (𝟙 W.left) (by simpa using h) : W ⟶ Over.mk (p.val.1 ≫ f)).op
      (β.app (op (Over.mk p.val.1)) p.val.2)) = _
  rw [hm, eqToHom_op, eqToHom_map, typeEqToHom_apply_cast]

private theorem relocalizeDescend_fst (G : (Over V)ᵒᵖ ⥤ Type v)
    (β : G ⟶ (relocalizeRestrict f).obj ((relocalizePresheafFunctor f).obj G))
    {W : Over U} (p : ((relocalizePresheafFunctor f).obj G).obj (op W))
    (h : p.val.1 ≫ f = W.hom) :
    (relocalizeDescend f β h p.val.2).val.1 =
      (β.app (op (Over.mk p.val.1)) p.val.2).val.1 := by
  obtain ⟨hW, e⟩ := relocalizeDescend_eq_cast f G β p h
  rw [e]
  exact eq_of_heq (relocalizeCastFst f G (congrArg op hW.symm)
    (β.app (op (Over.mk p.val.1)) p.val.2))

private theorem relocalizeDescend_snd (G : (Over V)ᵒᵖ ⥤ Type v)
    (β : G ⟶ (relocalizeRestrict f).obj ((relocalizePresheafFunctor f).obj G))
    {W : Over U} (p : ((relocalizePresheafFunctor f).obj G).obj (op W))
    (h : p.val.1 ≫ f = W.hom) :
    HEq (relocalizeDescend f β h p.val.2).val.2
      (β.app (op (Over.mk p.val.1)) p.val.2).val.2 := by
  obtain ⟨hW, e⟩ := relocalizeDescend_eq_cast f G β p h
  rw [e]
  exact relocalizeCastSnd f G (congrArg op hW.symm) (β.app (op (Over.mk p.val.1)) p.val.2)

/-- **The twist acts on the factorization by composition.** -/
theorem relocalizeTwist_app_fst (t : V ⟶ V) (ht : t ≫ f = f) (W : Over U)
    (x : ((relocalizePresheafFunctor f).obj ((Over.map f).op ⋙ X)).obj (op W)) :
    ((relocalizeTwist f X t ht).app (op W) x).val.1 = x.val.1 ≫ t := by
  have hdesc : ((relocalizeTwist f X t ht).app (op W) x).val.1 =
      ((relocalizeTwistRestricted f X t ht).app (op (Over.mk x.val.1)) x.val.2).val.1 :=
    relocalizeDescend_fst f ((Over.map f).op ⋙ X) (relocalizeTwistRestricted f X t ht)
      x x.property
  have hβ := relocalizeTwistRestricted_fst f X t ht (Over.mk x.val.1) x.val.2
  have hu := relocalizeUnit_fst f ((Over.map f).op ⋙ X)
    ((Over.map t).obj (Over.mk x.val.1))
    ((eqToHom (relocalizeRestrict_twist_eq f t ht X).symm).app
      (op (Over.mk x.val.1)) x.val.2)
  rw [hdesc]
  simpa [Over.map] using (eq_of_heq hβ).trans hu

/-- **The twist leaves the section itself alone.** -/
theorem relocalizeTwist_app_snd (t : V ⟶ V) (ht : t ≫ f = f) (W : Over U)
    (x : ((relocalizePresheafFunctor f).obj ((Over.map f).op ⋙ X)).obj (op W)) :
    HEq ((relocalizeTwist f X t ht).app (op W) x).val.2 x.val.2 := by
  have hdesc : HEq ((relocalizeTwist f X t ht).app (op W) x).val.2
      ((relocalizeTwistRestricted f X t ht).app (op (Over.mk x.val.1)) x.val.2).val.2 :=
    relocalizeDescend_snd f ((Over.map f).op ⋙ X) (relocalizeTwistRestricted f X t ht)
      x x.property
  have hβ := relocalizeTwistRestricted_snd f X t ht (Over.mk x.val.1) x.val.2
  have hu := relocalizeUnit_snd f ((Over.map f).op ⋙ X)
    ((Over.map t).obj (Over.mk x.val.1))
    ((eqToHom (relocalizeRestrict_twist_eq f t ht X).symm).app
      (op (Over.mk x.val.1)) x.val.2)
  have hcast : HEq ((eqToHom (relocalizeRestrict_twist_eq f t ht X).symm).app
      (op (Over.mk x.val.1)) x.val.2) x.val.2 := by
    rw [eqToHom_app_cast]
    exact cast_heq _ _
  exact hdesc.trans (hβ.trans (hu.trans hcast))

/-- The twist by the identity is the identity. -/
theorem relocalizeTwist_id (h : 𝟙 V ≫ f = f) : relocalizeTwist f X (𝟙 V) h = 𝟙 _ := by
  apply NatTrans.ext
  funext W
  ext x
  apply Subtype.ext
  apply Sigma.ext
  · simpa using relocalizeTwist_app_fst f X (𝟙 V) h W.unop x
  · exact relocalizeTwist_app_snd f X (𝟙 V) h W.unop x

/-- The twist by a composite is the composite of the twists. -/
theorem relocalizeTwist_comp (t t' : V ⟶ V) (ht : t ≫ f = f) (ht' : t' ≫ f = f)
    (htt' : (t ≫ t') ≫ f = f) :
    relocalizeTwist f X (t ≫ t') htt' =
      relocalizeTwist f X t ht ≫ relocalizeTwist f X t' ht' := by
  apply NatTrans.ext
  funext W
  ext x
  apply Subtype.ext
  apply Sigma.ext
  · calc ((relocalizeTwist f X (t ≫ t') htt').app W x).val.1
        = x.val.1 ≫ (t ≫ t') := relocalizeTwist_app_fst f X (t ≫ t') htt' W.unop x
      _ = (x.val.1 ≫ t) ≫ t' := (Category.assoc _ _ _).symm
      _ = ((relocalizeTwist f X t ht).app W x).val.1 ≫ t' := by
            rw [relocalizeTwist_app_fst f X t ht W.unop x]
      _ = ((relocalizeTwist f X t' ht').app W
            ((relocalizeTwist f X t ht).app W x)).val.1 :=
            (relocalizeTwist_app_fst f X t' ht' W.unop _).symm
  · exact (relocalizeTwist_app_snd f X (t ≫ t') htt' W.unop x).trans
      ((relocalizeTwist_app_snd f X t ht W.unop x).symm.trans
        (relocalizeTwist_app_snd f X t' ht' W.unop
          ((relocalizeTwist f X t ht).app W x)).symm)

/-! ### The lower-shriek extension of a restriction as a product -/

/-- A morphism of the slice over `U` with target the identity of `U` is determined by its
source: the representable presheaf of the terminal object of the slice takes subsingleton
values. -/
theorem subsingleton_yoneda_obj_mkId {U : C} (W : (Over U)ᵒᵖ) :
    Subsingleton ((yoneda.obj (Over.mk (𝟙 U))).obj W) :=
  ⟨fun a b ↦ Over.OverMorphism.ext (by
    have ha : a.left = (Opposite.unop W).hom := by simpa using Over.w a
    have hb : b.left = (Opposite.unop W).hom := by simpa using Over.w b
    rw [ha, hb])⟩

/-- The morphism from any presheaf on the slice over `U` to the representable presheaf of the
slice's terminal object. -/
def toYonedaMkId {U : C} (Y : (Over U)ᵒᵖ ⥤ Type v) : Y ⟶ yoneda.obj (Over.mk (𝟙 U)) where
  app W := ↾fun _ ↦ Over.homMk (Opposite.unop W).hom (by simp)
  naturality _ W' _ := by
    ext x
    exact (subsingleton_yoneda_obj_mkId W').elim _ _

/-- The canonical morphism from the lower-shriek extension of a restriction back to the
original presheaf: a section of the extension carries a factorization of the structure
morphism, which identifies the object with the one the section lives over. -/
def relocalizeRestrictCounit : (relocalizePresheafFunctor f).obj ((relocalizeRestrict f).obj X) ⟶
    X :=
  relocalizeOfRestricted f (𝟙 ((relocalizeRestrict f).obj X))

/-- The counit sends a section of the lower-shriek extension to the restriction of the section
of `X` it carries along the comparison of the object with the recorded factorization. -/
theorem relocalizeRestrictCounit_app_apply {W : (Over U)ᵒᵖ}
    (x : ((relocalizePresheafFunctor f).obj ((relocalizeRestrict f).obj X)).obj W) :
    (relocalizeRestrictCounit f X).app W x =
      X.map (Over.homMk (𝟙 (Opposite.unop W).left) (by rw [Category.id_comp]; exact x.2) :
        Opposite.unop W ⟶ Over.mk (x.1.1 ≫ f)).op x.1.2 := rfl

/-- Restricting a section of `X` along the comparison identifying an object of the slice with
the factorization recorded by a section of the lower-shriek extension is a bijection. -/
private theorem bijective_map_homMk_id {W : Over U} {ψ : W.left ⟶ V} (hψ : ψ ≫ f = W.hom) :
    Function.Bijective (X.map (Over.homMk (𝟙 W.left)
      (by rw [Category.id_comp]; exact hψ) : W ⟶ Over.mk (ψ ≫ f)).op) := by
  have hobj : W = Over.mk (ψ ≫ f) :=
    CostructuredArrow.obj_ext _ _ rfl (by simpa using hψ)
  rw [show (Over.homMk (𝟙 W.left) (by rw [Category.id_comp]; exact hψ) :
      W ⟶ Over.mk (ψ ≫ f)) = eqToHom hobj from Over.OverMorphism.ext (by simp),
    eqToHom_op, eqToHom_map]
  exact (isIso_iff_bijective _).mp inferInstance

/-- **The lower-shriek extension of a restriction is a product with the base.** For `f : V ⟶ U`
and a presheaf `X` on the slice over `U`, the square whose upper horizontal arrow is
`CategoryTheory.OverShriek.relocalizeRestrictCounit` and whose left vertical arrow reads off
the factorization recorded by a section is cartesian over any presheaf taking subsingleton
values. So the restriction of `X` to the slice over `V`, viewed again over `U`, is the fibre
product of `X` with the representable presheaf of `f` over the terminal object of the slice. -/
@[sga "3 I 1.6.1" "partial", sga "4 I 5.11" "special case"]
theorem isPullback_relocalizeRestrictCounit {T : (Over U)ᵒᵖ ⥤ Type v}
    (hT : ∀ W, Subsingleton (T.obj W)) (π : X ⟶ T) (τ : yoneda.obj (Over.mk f) ⟶ T) :
    IsPullback (relocalizeRestrictCounit f X)
      (relocalizeToYoneda f ((relocalizeRestrict f).obj X)) π τ := by
  apply IsPullback.of_forall_isPullback_app
  intro W
  rw [Limits.Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    exact (hT W).elim _ _
  · rintro ⟨⟨ψ, s⟩, hψ⟩ ⟨⟨ψ', s'⟩, hψ'⟩ ⟨h₁, h₂⟩
    have hi : ψ = ψ' := congrArg Over.Hom.left h₂
    subst hi
    exact Subtype.ext (congrArg (fun t ↦ (⟨ψ, t⟩ :
      Σ χ : (Opposite.unop W).left ⟶ V,
        ((relocalizeRestrict f).obj X).obj (Opposite.op (Over.mk χ))))
      ((bijective_map_homMk_id f X hψ).1 h₁))
  · rintro t χ -
    have hψ : χ.left ≫ f = (Opposite.unop W).hom := by simpa using Over.w χ
    obtain ⟨s, hs⟩ := (bijective_map_homMk_id f X hψ).2 t
    exact ⟨⟨⟨χ.left, s⟩, hψ⟩, hs, Over.OverMorphism.ext rfl⟩

end CategoryTheory.OverShriek

namespace AlgebraicGeometry.Space

/-- The morphism of the chosen big fppf site underlying a field extension `K/k`: the morphism
`Spec K ⟶ Spec k` of spectra, lifted to the site's underlying full subcategory. -/
noncomputable def fieldExtensionMap (B : BigFppfSite.{u}) (k K : Type u) [Field k] [Field K]
    [Algebra k K] (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K))) :
    B.obj hK ⟶ B.obj hk :=
  B.inclusion.preimage (Spec.map (CommRingCat.ofHom (algebraMap k K)))

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.fieldExtensionMap`. -/
@[simp]
theorem map_fieldExtensionMap (B : BigFppfSite.{u}) (k K : Type u) [Field k] [Field K]
    [Algebra k K] (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K))) :
    B.inclusion.map (fieldExtensionMap B k K hk hK) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) :=
  B.inclusion.map_preimage _

/-- A tower of field extensions `k ⊆ k' ⊆ K` gives a factorization of the site morphism of
`K/k` through the site morphism of `k'/k`. -/
theorem fieldExtensionMap_comp (B : BigFppfSite.{u}) (k k' K : Type u)
    [Field k] [Field k'] [Field K] [Algebra k k'] [Algebra k' K] [Algebra k K]
    [IsScalarTower k k' K] (hk : B.Contains (Spec (.of k)))
    (hk' : B.Contains (Spec (.of k'))) (hK : B.Contains (Spec (.of K))) :
    fieldExtensionMap B k' K hk' hK ≫ fieldExtensionMap B k k' hk hk' =
      fieldExtensionMap B k K hk hK := by
  apply B.inclusion.map_injective
  rw [B.inclusion.map_comp, map_fieldExtensionMap, map_fieldExtensionMap,
    map_fieldExtensionMap, ← Spec.map_comp]
  refine congrArg Spec.map (CommRingCat.hom_ext ?_)
  ext x
  exact (IsScalarTower.algebraMap_apply k k' K x).symm

/-- **Stacks 0A0Z.** A presheaf on the big fppf site over a field `k` — in particular an
algebraic space over `k` — is *geometrically connected* when for every field extension `K/k`
whose spectrum lies in the chosen big fppf site the base change `X_K` has a connected space
of points. -/
@[stacks 0A0Z]
def IsGeometricallyConnected (B : BigFppfSite.{u}) (k : Type u) [Field k]
    (hk : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K] (hK : B.Contains (Spec (.of K))),
    @ConnectedSpace
      (points B (Spec (.of K)) hK
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X))
      (pointTopology B (Spec (.of K)) hK _)

/-! ### Points under restriction to a smaller base -/

section Restriction

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- A field-valued point of the restriction of `F` to the smaller base `S` is a field-valued
point of `F` itself: compose its structure morphism with `g`. -/
noncomputable def FieldValuedPoint.ofRelocalizeRestrict
    (F : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u)
    (p : FieldValuedPoint B S hS ((OverShriek.relocalizeRestrict g).obj F)) :
    FieldValuedPoint B S' hS' F where
  carrier := p.carrier
  field := p.field
  contained := p.contained
  toBase := p.toBase ≫ B.inclusion.map g
  value := p.value

/-- Viewing a field-valued point of a restriction as a field-valued point of the original
presheaf preserves common extensions. -/
theorem FieldValuedPoint.hasCommonExtension_ofRelocalizeRestrict
    (F : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u)
    {p q : FieldValuedPoint B S hS ((OverShriek.relocalizeRestrict g).obj F)}
    (hpq : FieldValuedPoint.HasCommonExtension B S hS
      ((OverShriek.relocalizeRestrict g).obj F) p q) :
    FieldValuedPoint.HasCommonExtension B S' hS' F
      (FieldValuedPoint.ofRelocalizeRestrict B S S' hS hS' g F p)
      (FieldValuedPoint.ofRelocalizeRestrict B S S' hS hS' g F q) := by
  obtain ⟨r, ⟨f, hf⟩, ⟨f', hf'⟩⟩ := hpq
  refine ⟨FieldValuedPoint.ofRelocalizeRestrict B S S' hS hS' g F r,
    ⟨(Over.map g).map f, ?_⟩, ⟨(Over.map g).map f', ?_⟩⟩
  · change F.map ((Over.map g).map f).op p.value = r.value
    simpa [FieldValuedPoint.ofRelocalizeRestrict] using hf
  · change F.map ((Over.map g).map f').op q.value = r.value
    simpa [FieldValuedPoint.ofRelocalizeRestrict] using hf'

/-- The map on point sets induced by restricting a presheaf on the big fppf site of `S'` to
the smaller base `S`. -/
noncomputable def pointsOfRelocalizeRestrict (F : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u) :
    points B S hS ((OverShriek.relocalizeRestrict g).obj F) → points B S' hS' F :=
  Quot.map (FieldValuedPoint.ofRelocalizeRestrict B S S' hS hS' g F)
    (fun _ _ h ↦ FieldValuedPoint.hasCommonExtension_ofRelocalizeRestrict B S S' hS hS' g F h)

/-- `AlgebraicGeometry.Space.pointsOfRelocalizeRestrict` on the class of a field-valued point is
the class of the corresponding field-valued point over `S'`. -/
@[simp]
theorem pointsOfRelocalizeRestrict_class (F : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u)
    (p : FieldValuedPoint B S hS ((OverShriek.relocalizeRestrict g).obj F)) :
    pointsOfRelocalizeRestrict B S S' hS hS' g F
        (p.class B S hS ((OverShriek.relocalizeRestrict g).obj F)) =
      (FieldValuedPoint.ofRelocalizeRestrict B S S' hS hS' g F p).class B S' hS' F := rfl

/-- A field-valued point of a represented presheaf over `S` is a field-valued point of the
presheaf represented by the same object viewed over `S'`. -/
noncomputable def FieldValuedPoint.overMap (U : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    FieldValuedPoint B S' hS' (yoneda.obj ((Over.map g).obj U)) where
  carrier := p.carrier
  field := p.field
  contained := p.contained
  toBase := p.toBase ≫ B.inclusion.map g
  value := (Over.map g).map p.value

/-- Viewing a field-valued point of a represented presheaf over the larger base preserves
common extensions. -/
theorem FieldValuedPoint.hasCommonExtension_overMap (U : BigFppfOver B S hS)
    {p q : FieldValuedPoint B S hS (yoneda.obj U)}
    (hpq : FieldValuedPoint.HasCommonExtension B S hS (yoneda.obj U) p q) :
    FieldValuedPoint.HasCommonExtension B S' hS' (yoneda.obj ((Over.map g).obj U))
      (FieldValuedPoint.overMap B S S' hS hS' g U p)
      (FieldValuedPoint.overMap B S S' hS hS' g U q) := by
  obtain ⟨r, ⟨f, hf⟩, ⟨f', hf'⟩⟩ := hpq
  refine ⟨FieldValuedPoint.overMap B S S' hS hS' g U r,
    ⟨(Over.map g).map f, ?_⟩, ⟨(Over.map g).map f', ?_⟩⟩
  · change (Over.map g).map f ≫ (Over.map g).map p.value = (Over.map g).map r.value
    have h : f ≫ p.value = r.value := hf
    simpa only [Functor.map_comp] using congrArg ((Over.map g).map) h
  · change (Over.map g).map f' ≫ (Over.map g).map q.value = (Over.map g).map r.value
    have h : f' ≫ q.value = r.value := hf'
    simpa only [Functor.map_comp] using congrArg ((Over.map g).map) h

/-- The map on point sets induced by viewing an object of the big fppf site over `S` as an
object over `S'`. -/
noncomputable def pointsOverMap (U : BigFppfOver B S hS) :
    points B S hS (yoneda.obj U) → points B S' hS' (yoneda.obj ((Over.map g).obj U)) :=
  Quot.map (FieldValuedPoint.overMap B S S' hS hS' g U)
    (fun _ _ h ↦ FieldValuedPoint.hasCommonExtension_overMap B S S' hS hS' g U h)

/-- `AlgebraicGeometry.Space.pointsOverMap` on the class of a field-valued point is the class of
the same point viewed over `S'`. -/
@[simp]
theorem pointsOverMap_class (U : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    pointsOverMap B S S' hS hS' g U (p.class B S hS (yoneda.obj U)) =
      (FieldValuedPoint.overMap B S S' hS hS' g U p).class B S' hS'
        (yoneda.obj ((Over.map g).obj U)) := rfl

/-- Viewing an object over the larger base does not move the underlying scheme point of a
field-valued point, since it does not change the underlying scheme. -/
@[simp]
theorem schemePoint_overMap (U : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    schemePoint B S' hS' ((Over.map g).obj U)
        (FieldValuedPoint.overMap B S S' hS hS' g U p) =
      schemePoint B S hS U p := rfl

/-- Viewing an object of the big fppf site over `S` as an object over `S'` is continuous on
points: on either side the topology is the one of the common underlying scheme. -/
theorem continuous_pointsOverMap (U : BigFppfOver B S hS) :
    @Continuous _ _ (pointTopology B S hS (yoneda.obj U))
      (pointTopology B S' hS' (yoneda.obj ((Over.map g).obj U)))
      (pointsOverMap B S S' hS hS' g U) := by
  let : TopologicalSpace (points B S hS (yoneda.obj U)) := pointTopology B S hS (yoneda.obj U)
  let : TopologicalSpace (points B S' hS' (yoneda.obj ((Over.map g).obj U))) :=
    pointTopology B S' hS' (yoneda.obj ((Over.map g).obj U))
  rw [continuous_def]
  intro V hV
  obtain ⟨W, hW, hmem⟩ := (isOpen_yoneda_iff_isSchemeOpen B S' hS' ((Over.map g).obj U) V).mp hV
  refine (isOpen_yoneda_iff_isSchemeOpen B S hS U _).mpr ⟨W, hW, fun p ↦ ?_⟩
  rw [Set.mem_preimage, pointsOverMap_class, hmem, schemePoint_overMap]

/-- **Restriction to a smaller base is continuous on points.** The atlas of the restriction is
an open continuous surjection on points, hence a quotient map, and the composite of
restriction with it factors through the represented case. -/
theorem continuous_pointsOfRelocalizeRestrict (F : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u)
    (hG : IsAlgebraicSpace B S hS ((OverShriek.relocalizeRestrict g).obj F)) :
    @Continuous _ _ (pointTopology B S hS ((OverShriek.relocalizeRestrict g).obj F))
      (pointTopology B S' hS' F) (pointsOfRelocalizeRestrict B S S' hS hS' g F) := by
  classical
  set G := (OverShriek.relocalizeRestrict g).obj F with hGdef
  let : TopologicalSpace (points B S hS G) := pointTopology B S hS G
  let : TopologicalSpace (points B S' hS' F) := pointTopology B S' hS' F
  obtain ⟨U, a, haSurj, haEtale⟩ := hG.exists_atlas
  set U' := (Over.map g).obj U with hU'
  let : TopologicalSpace (points B S hS (yoneda.obj U)) := pointTopology B S hS (yoneda.obj U)
  let : TopologicalSpace (points B S' hS' (yoneda.obj U')) :=
    pointTopology B S' hS' (yoneda.obj U')
  let ξ : F.obj (Opposite.op U') := by
    change G.obj (Opposite.op U)
    exact yonedaEquiv a
  let a' : yoneda.obj U' ⟶ F := yonedaEquiv.symm ξ
  let i : yoneda.obj U ⟶ (OverShriek.relocalizeRestrict g).obj (yoneda.obj U') :=
    yonedaEquiv.symm (𝟙 U')
  have hi : a = i ≫ (OverShriek.relocalizeRestrict g).map a' := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp]
    change ξ = F.map (𝟙 (Opposite.op U')) ξ
    simp
  have hcomp : pointsOfRelocalizeRestrict B S S' hS hS' g F ∘
      pointsMap B S hS (yoneda.obj U) a =
      pointsMap B S' hS' (yoneda.obj U') a' ∘ pointsOverMap B S S' hS hS' g U := by
    funext x
    refine Quot.inductionOn x fun p => ?_
    rw [Function.comp_apply, Function.comp_apply, pointsMap_class,
      pointsOfRelocalizeRestrict_class, pointsOverMap_class, pointsMap_class]
    refine congrArg (FieldValuedPoint.class B S' hS' F) ?_
    have hval : (FieldValuedPoint.ofRelocalizeRestrict B S S' hS hS' g F
          (FieldValuedPoint.map B S hS (yoneda.obj U) a p)).value =
        (FieldValuedPoint.map B S' hS' (yoneda.obj U') a'
          (FieldValuedPoint.overMap B S S' hS hS' g U p)).value := by
      change a.app (Opposite.op p.siteObject) p.value =
        a'.app (Opposite.op ((Over.map g).obj p.siteObject)) ((Over.map g).map p.value)
      have hiapp : i.app (Opposite.op p.siteObject) p.value = (Over.map g).map p.value := by
        dsimp [i]
        change (((OverShriek.relocalizeRestrict g).obj (yoneda.obj U')).map p.value.op) (𝟙 U') =
          (Over.map g).map p.value
        change (Over.map g).map p.value ≫ 𝟙 U' = _
        exact Category.comp_id _
      have hnat := congrArg
        (fun η : yoneda.obj U ⟶ G ↦ η.app (Opposite.op p.siteObject) p.value) hi
      simpa [NatTrans.comp_app, hiapp] using hnat
    dsimp [FieldValuedPoint.ofRelocalizeRestrict, FieldValuedPoint.map,
      FieldValuedPoint.overMap] at hval ⊢
    rw [FieldValuedPoint.mk.injEq]
    exact ⟨rfl, HEq.rfl, HEq.rfl, heq_of_eq hval⟩
  have heSurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) a) :=
    (surjective_iff_surjective_pointsMap B S hS G hG U a).mp haSurj
  have heOpen : @IsOpenMap _ _ (pointTopology B S hS (yoneda.obj U)) (pointTopology B S hS G)
      (pointsMap B S hS (yoneda.obj U) a) :=
    isOpenMap_pointsMap_of_etale B S hS hG U a haEtale
  refine (heOpen.isQuotientMap (continuous_pointsMap B S hS a) heSurj).continuous_iff.mpr ?_
  rw [hcomp]
  exact (continuous_pointsMap B S' hS' a').comp (continuous_pointsOverMap B S S' hS hS' g U)

/-- Connectedness of the space of points is transported along an isomorphism of presheaves:
`AlgebraicGeometry.Space.pointsMap` is functorial and every morphism of presheaves is
continuous on points. -/
theorem connectedSpace_points_of_iso {F G : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (hconn : @ConnectedSpace (points B S' hS' F) (pointTopology B S' hS' F)) :
    @ConnectedSpace (points B S' hS' G) (pointTopology B S' hS' G) := by
  let : TopologicalSpace (points B S' hS' F) := pointTopology B S' hS' F
  let : TopologicalSpace (points B S' hS' G) := pointTopology B S' hS' G
  let : ConnectedSpace (points B S' hS' F) := hconn
  have hsurj : Function.Surjective (pointsMap B S' hS' F e.hom) := by
    intro y
    refine ⟨pointsMap B S' hS' G e.inv y, ?_⟩
    calc pointsMap B S' hS' F e.hom (pointsMap B S' hS' G e.inv y)
        = pointsMap B S' hS' G (e.inv ≫ e.hom) y := by rw [pointsMap_comp]; rfl
      _ = y := by rw [e.inv_hom_id, pointsMap_id]; rfl
  exact hsurj.connectedSpace (continuous_pointsMap B S' hS' e.hom)

end Restriction

/-! ### Amalgamating two field extensions inside the site -/

/-- Two field extensions of `k` whose spectra lie in the chosen big fppf site have a common
field extension whose spectrum lies in the site: a quotient of their tensor product by a
maximal ideal, which is small enough because the site's cutoff is a strong prelimit. -/
theorem exists_fieldExtension_common (B : BigFppfSite.{u}) (k E F : Type u)
    [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F]
    (hE : B.Contains (Spec (.of E))) (hF : B.Contains (Spec (.of F))) :
    ∃ (M : Type u) (_ : Field M) (_ : Algebra k M) (_ : Algebra E M) (_ : Algebra F M)
      (_ : B.Contains (Spec (.of M))), IsScalarTower k E M ∧ IsScalarTower k F M := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (E ⊗[k] F)
  let : I.IsMaximal := hI
  let : Field ((E ⊗[k] F) ⧸ I) := Ideal.Quotient.field I
  have hcard : ∀ (A : Type u) [Field A], B.Contains (Spec (.of A)) → #A < B.cutoff := by
    intro A _ hA
    have h : (Spec (CommRingCat.of A)).size < B.cutoff := hA
    rw [Scheme.size_Spec] at h
    exact lt_of_le_of_lt (le_max_right _ _) h
  have hEcard := hcard E hE
  have hFcard := hcard F hF
  have hTensorSize : (Spec (CommRingCat.of (E ⊗[k] F))).size < B.cutoff := by
    rw [Scheme.size_Spec]
    exact max_lt B.aleph0_lt_cutoff (Cardinal.mk_tensorProduct_le.trans_lt
      (max_lt B.aleph0_lt_cutoff (max_lt hEcard hFcard)))
  have hMSize : (Spec (.of ((E ⊗[k] F) ⧸ I))).size < B.cutoff :=
    Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hTensorSize
      ((mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := I))).trans (le_max_right _ _))
  exact ⟨(E ⊗[k] F) ⧸ I, inferInstance, inferInstance, inferInstance, inferInstance, hMSize,
    inferInstance, inferInstance⟩

/-! ### Geometric connectedness after a field extension -/

/-- A field extension `M/K` of a field extension `K/k` inside the site is surjective on the
points of any restricted presheaf: a field-valued point over `K` can be amalgamated with `M`
inside the site. -/
theorem surjective_pointsOfRelocalizeRestrict_fieldExtension (B : BigFppfSite.{u})
    (K M : Type u) [Field K] [Field M]
    (hK : B.Contains (Spec (.of K))) (hM : B.Contains (Spec (.of M)))
    (g : B.obj hM ⟶ B.obj hK) (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u) :
    Function.Surjective
      (pointsOfRelocalizeRestrict B (Spec (.of M)) (Spec (.of K)) hM hK g F) := by
  classical
  intro x
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  let α := Spec.homEquiv (B.inclusion.map g)
  let β := Spec.homEquiv p.toBase
  let : Algebra K M := α.hom.toAlgebra
  let : Algebra K p.carrier := β.hom.toAlgebra
  have hα : α.hom = algebraMap K M := (RingHom.algebraMap_toAlgebra α.hom).symm
  have hβ : β.hom = algebraMap K p.carrier := (RingHom.algebraMap_toAlgebra β.hom).symm
  obtain ⟨N, hNfield, hKN, hMN, hpN, hN, hKMN, hKpN⟩ :=
    exists_fieldExtension_common B K M p.carrier hM p.contained
  let : Field N := hNfield
  let : Algebra K N := hKN
  let : Algebra M N := hMN
  let : Algebra p.carrier N := hpN
  let : IsScalarTower K M N := hKMN
  let : IsScalarTower K p.carrier N := hKpN
  let nM : Spec (.of N) ⟶ Spec (.of M) := Spec.map (CommRingCat.ofHom (algebraMap M N))
  let nL : Spec (.of N) ⟶ Spec (.of p.carrier) :=
    Spec.map (CommRingCat.ofHom (algebraMap p.carrier N))
  have hαMap : B.inclusion.map g = Spec.map α :=
    (Spec.homEquiv.symm_apply_apply (B.inclusion.map g)).symm
  have hβMap : p.toBase = Spec.map β := (Spec.homEquiv.symm_apply_apply p.toBase).symm
  have hbase : nL ≫ p.toBase = nM ≫ B.inclusion.map g := by
    rw [hβMap, hαMap, ← Spec.map_comp, ← Spec.map_comp]
    refine congrArg Spec.map (CommRingCat.hom_ext ?_)
    ext b
    change (algebraMap p.carrier N) (β.hom b) = (algebraMap M N) (α.hom b)
    rw [hα, hβ, ← IsScalarTower.algebraMap_apply K p.carrier N,
      ← IsScalarTower.algebraMap_apply K M N]
  let A : BigFppfOver B (Spec (.of M)) hM := Over.mk (⟨nM⟩ : B.obj hN ⟶ B.obj hM)
  let e : B.obj hN ⟶ B.obj p.contained := B.inclusion.preimage nL
  have he : e ≫ p.siteObject.hom = A.hom ≫ g := by
    apply B.inclusion.map_injective
    rwa [B.inclusion.map_comp, B.inclusion.map_comp, B.inclusion.map_preimage]
  let f : (Over.map g).obj A ⟶ p.siteObject := Over.homMk e he
  refine ⟨({ carrier := N
             field := inferInstance
             contained := hN
             toBase := nM
             value := F.map f.op p.value } :
      FieldValuedPoint B (Spec (.of M)) hM
        ((OverShriek.relocalizeRestrict g).obj F)).class B (Spec (.of M)) hM _, ?_⟩
  rw [pointsOfRelocalizeRestrict_class]
  exact FieldValuedPoint.class_eq_class_of_hasCommonExtension B (Spec (.of K)) hK F
    ⟨_, FieldValuedPoint.dominates_refl B (Spec (.of K)) hK F _, ⟨f, rfl⟩⟩

/-- **Stacks 0A10.** A presheaf on the big fppf site over a field `k` — in particular an
algebraic space over `k` — is geometrically connected over `k` if and only if its base change
to a field extension `k'` of `k` is geometrically connected over `k'`. -/
@[stacks 0A10]
theorem isGeometricallyConnected_iff_relocalizeRestrict (B : BigFppfSite.{u})
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (hk : B.Contains (Spec (.of k))) (hk' : B.Contains (Spec (.of k')))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) :
    IsGeometricallyConnected B k hk X ↔
      IsGeometricallyConnected B k' hk'
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B k k' hk hk')).obj X) := by
  constructor
  · intro hgeom K hKfield hKalg hK
    let : Field K := hKfield
    let : Algebra k' K := hKalg
    let : Algebra k K := ((algebraMap k' K).comp (algebraMap k k')).toAlgebra
    let : IsScalarTower k k' K := IsScalarTower.of_algebraMap_eq' rfl
    exact connectedSpace_points_of_iso B (Spec (.of K)) hK
      ((OverShriek.relocalizeRestrictComp (fieldExtensionMap B k' K hk' hK)
            (fieldExtensionMap B k k' hk hk') X ≪≫
          eqToIso (congrArg (fun f ↦ (OverShriek.relocalizeRestrict f).obj X)
            (fieldExtensionMap_comp B k k' K hk hk' hK))).symm)
      (hgeom K hK)
  · intro hgeom' K hKfield hKalg hK
    let : Field K := hKfield
    let : Algebra k K := hKalg
    obtain ⟨M, hMfield, hkM, hk'M, hKM, hM, hTowerk', hTowerK⟩ :=
      exists_fieldExtension_common B k k' K hk' hK
    let : Field M := hMfield
    let : Algebra k M := hkM
    let : Algebra k' M := hk'M
    let : Algebra K M := hKM
    let : IsScalarTower k k' M := hTowerk'
    let : IsScalarTower k K M := hTowerK
    have hroute : fieldExtensionMap B K M hK hM ≫ fieldExtensionMap B k K hk hK =
        fieldExtensionMap B k' M hk' hM ≫ fieldExtensionMap B k k' hk hk' :=
      (fieldExtensionMap_comp B k K M hk hK hM).trans
        (fieldExtensionMap_comp B k k' M hk hk' hM).symm
    have hconn : @ConnectedSpace _ (pointTopology B (Spec (.of M)) hM
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B K M hK hM)).obj
          ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X))) :=
      connectedSpace_points_of_iso B (Spec (.of M)) hM
        (OverShriek.relocalizeRestrictComp (fieldExtensionMap B k' M hk' hM)
              (fieldExtensionMap B k k' hk hk') X ≪≫
          eqToIso (congrArg (fun f ↦ (OverShriek.relocalizeRestrict f).obj X) hroute.symm) ≪≫
          (OverShriek.relocalizeRestrictComp (fieldExtensionMap B K M hK hM)
            (fieldExtensionMap B k K hk hK) X).symm)
        (hgeom' M hM)
    let : TopologicalSpace (points B (Spec (.of M)) hM
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B K M hK hM)).obj
          ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X))) :=
      pointTopology B (Spec (.of M)) hM _
    let : ConnectedSpace (points B (Spec (.of M)) hM
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B K M hK hM)).obj
          ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X))) := hconn
    let : TopologicalSpace (points B (Spec (.of K)) hK
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X)) :=
      pointTopology B (Spec (.of K)) hK _
    have hXK : IsAlgebraicSpace B (Spec (.of K)) hK
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X) :=
      isAlgebraicSpace_relocalizeRestrict B (Spec (.of K)) (Spec (.of k)) hK hk
        (fieldExtensionMap B k K hk hK) X hX
    exact (surjective_pointsOfRelocalizeRestrict_fieldExtension B K M hK hM
      (fieldExtensionMap B K M hK hM) _).connectedSpace
      (continuous_pointsOfRelocalizeRestrict B (Spec (.of M)) (Spec (.of K)) hM hK
        (fieldExtensionMap B K M hK hM) _
        (isAlgebraicSpace_relocalizeRestrict B (Spec (.of M)) (Spec (.of K)) hM hK
          (fieldExtensionMap B K M hK hM) _ hXK))

/-! ### The Galois action on a base change -/

section GaloisAction

variable (B : BigFppfSite.{u}) (k K : Type u) [Field k] [Field K] [Algebra k K]
  (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))

/-- The automorphism of the site object `Spec K` attached to a `k`-algebra automorphism
of `K`. -/
noncomputable def siteMapAlgAut (σ : K ≃ₐ[k] K) : B.obj hK ⟶ B.obj hK :=
  B.inclusion.preimage
    (show B.inclusion.obj (B.obj hK) ⟶ B.inclusion.obj (B.obj hK) from specMapAlgAut k K σ)

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.siteMapAlgAut`. -/
@[simp]
theorem map_siteMapAlgAut (σ : K ≃ₐ[k] K) :
    B.inclusion.map (siteMapAlgAut B k K hK σ) = specMapAlgAut k K σ :=
  B.inclusion.map_preimage _

/-- The identity automorphism induces the identity of the site object. -/
@[simp]
theorem siteMapAlgAut_one : siteMapAlgAut B k K hK (1 : K ≃ₐ[k] K) = 𝟙 (B.obj hK) := by
  apply B.inclusion.map_injective
  rw [map_siteMapAlgAut, specMapAlgAut_one]
  exact (B.inclusion.map_id (B.obj hK)).symm

/-- Taking site objects turns composition of automorphisms into composition in the other
order. -/
theorem siteMapAlgAut_mul (σ τ : K ≃ₐ[k] K) :
    siteMapAlgAut B k K hK (σ * τ) =
      siteMapAlgAut B k K hK σ ≫ siteMapAlgAut B k K hK τ := by
  apply B.inclusion.map_injective
  rw [B.inclusion.map_comp, map_siteMapAlgAut, map_siteMapAlgAut, map_siteMapAlgAut,
    specMapAlgAut_mul]

/-- The automorphism of `Spec K` attached to a `k`-algebra automorphism lies over
`Spec k`. -/
@[simp]
theorem siteMapAlgAut_comp_fieldExtensionMap (σ : K ≃ₐ[k] K) :
    siteMapAlgAut B k K hK σ ≫ fieldExtensionMap B k K hk hK =
      fieldExtensionMap B k K hk hK := by
  apply B.inclusion.map_injective
  rw [B.inclusion.map_comp, map_siteMapAlgAut, map_fieldExtensionMap,
    specMapAlgAut_comp_structureMap]

variable (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)

/-- **Stacks 0A14, the action.** The canonical action of the opposite group of `k`-algebra
automorphisms of `K` on the base change `X_K`, viewed again as a presheaf over `k`. For a
Galois extension `K/k` this is the Galois action on `X_{\overline{k}}`.

The action is over `k`, not over `K`: an automorphism changes only the `K`-coordinate of a
section. -/
@[implicit_reducible, stacks 0A14 "the action"]
noncomputable def galoisActionOnBaseChange :
    Action ((BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) (MulOpposite (K ≃ₐ[k] K)) where
  V := (OverShriek.relocalizePresheafFunctor (fieldExtensionMap B k K hk hK)).obj
    ((Over.map (fieldExtensionMap B k K hk hK)).op ⋙ X)
  ρ :=
    { toFun := fun σ ↦ End.of (OverShriek.relocalizeTwist (fieldExtensionMap B k K hk hK) X
        (siteMapAlgAut B k K hK σ.unop)
        (siteMapAlgAut_comp_fieldExtensionMap B k K hk hK σ.unop))
      map_one' := by
        ext1
        simp only [MulOpposite.unop_one, siteMapAlgAut_one, End.one_asHom]
        exact OverShriek.relocalizeTwist_id (fieldExtensionMap B k K hk hK) X _
      map_mul' := fun σ τ ↦ by
        have hunop : (σ * τ).unop = τ.unop * σ.unop := rfl
        ext1
        simp only [hunop, siteMapAlgAut_mul, End.mul_asHom]
        exact OverShriek.relocalizeTwist_comp (fieldExtensionMap B k K hk hK) X _ _
          (siteMapAlgAut_comp_fieldExtensionMap B k K hk hK τ.unop)
          (siteMapAlgAut_comp_fieldExtensionMap B k K hk hK σ.unop) _ }

/-- The presheaf underlying `AlgebraicGeometry.Space.galoisActionOnBaseChange` is the base
change of `X` to `K`, viewed over `k` by the lower-shriek extension. -/
theorem galoisActionOnBaseChange_V :
    (galoisActionOnBaseChange B k K hk hK X).V =
      (OverShriek.relocalizePresheafFunctor (fieldExtensionMap B k K hk hK)).obj
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X) := rfl

/-- **Stacks 0A14, the action on the `K`-coordinate.** An automorphism `σ` acts on a section
of `X_K` over a `k`-scheme by composing its morphism to `Spec K` with the automorphism of
`Spec K` induced by `σ`. -/
@[stacks 0A14 "the action on the K-coordinate of a section"]
theorem galoisActionOnBaseChange_ρ_app_fst (σ : MulOpposite (K ≃ₐ[k] K))
    (W : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ)
    (x : ((OverShriek.relocalizePresheafFunctor (fieldExtensionMap B k K hk hK)).obj
      ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X)).obj W) :
    (((galoisActionOnBaseChange B k K hk hK X).ρ σ).asHom.app W x).val.1 =
      x.val.1 ≫ siteMapAlgAut B k K hK σ.unop :=
  OverShriek.relocalizeTwist_app_fst (fieldExtensionMap B k K hk hK) X _ _ W.unop x

/-- **Stacks 0A14, the action on the section.** An automorphism leaves the section of `X`
itself untouched. The equality is heterogeneous because the type of the section is indexed by
the morphism to `Spec K`, which the action does change. -/
@[stacks 0A14 "the action on the section"]
theorem galoisActionOnBaseChange_ρ_app_snd (σ : MulOpposite (K ≃ₐ[k] K))
    (W : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ)
    (x : ((OverShriek.relocalizePresheafFunctor (fieldExtensionMap B k K hk hK)).obj
      ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X)).obj W) :
    HEq (((galoisActionOnBaseChange B k K hk hK X).ρ σ).asHom.app W x).val.2 x.val.2 :=
  OverShriek.relocalizeTwist_app_snd (fieldExtensionMap B k K hk hK) X _ _ W.unop x

end GaloisAction

/-! ### Connected components of a product with a geometrically connected space -/

section Product

open CategoryTheory.Limits

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))

/-- The site morphism carried by a field-valued point of a presheaf over `k` is the morphism
of the field extension it defines. -/
theorem siteObject_hom_eq_fieldExtensionMap
    {Y : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (q : FieldValuedPoint B (Spec (.of k)) hk Y)
    [Algebra k q.carrier]
    (halg : (Spec.homEquiv q.toBase).hom = algebraMap k q.carrier) :
    q.siteObject.hom = fieldExtensionMap B k q.carrier hk q.contained := by
  apply B.inclusion.map_injective
  have hqSpec : q.toBase = Spec.map (Spec.homEquiv q.toBase) :=
    (Spec.homEquiv.symm_apply_apply q.toBase).symm
  have halg' : Spec.homEquiv q.toBase = CommRingCat.ofHom (algebraMap k q.carrier) :=
    CommRingCat.hom_ext halg
  change q.toBase = B.inclusion.map (fieldExtensionMap B k q.carrier hk q.contained)
  rw [map_fieldExtensionMap, hqSpec, halg']

/-- **Stacks 0A11.** Let `k` be a field, let `X` and `Y` be algebraic spaces over `k` and
assume `X` is geometrically connected over `k`. The projection `X ×_k Y ⟶ Y` induces a
bijection between the sets of connected components of the two point spaces.

The projection is open on points because `X ⟶ Spec k` is universally open (Stacks 06DN), and
its fibre over the point represented by a field-valued point `Spec K ⟶ Y` is the image of
`|X_K ×_k Spec K|`; that fibre product is the base change `X_K` of `X` to `K` viewed again over
`k`, whose point space is homeomorphic to `|X_K|` and so is connected. Stacks 0378 then gives
the bijection. -/
@[stacks 0A11]
theorem bijective_connectedComponents_pullback_of_isGeometricallyConnected
    {X Y : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hY : IsAlgebraicSpace B (Spec (.of k)) hk Y)
    (hXconn : IsGeometricallyConnected B k hk X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (g : Y ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk)))) :
    Function.Bijective
      (continuous_pointsMap B (Spec (.of k)) hk
        (pullback.snd f g)).connectedComponentsMap := by
  classical
  refine bijective_connectedComponentsMap_of_isOpenMap _ _ ?_ ?_
  · exact isOpenMap_pointsMap_of_comp_isIso B (Spec (.of k)) hk (pullbackSymmetry f g).hom
      (pullbackSymmetry_hom_comp_fst f g)
      (universallyOpen_to_field B (Spec (.of k)) hk hX (k := k) (Iso.refl _) f Y hY g)
  · intro y
    obtain ⟨q, rfl⟩ := Quot.exists_rep y
    let : Algebra k q.carrier := (Spec.homEquiv q.toBase).hom.toAlgebra
    have hqMor : q.siteObject.hom = fieldExtensionMap B k q.carrier hk q.contained :=
      siteObject_hom_eq_fieldExtensionMap B k hk q
        (RingHom.algebraMap_toAlgebra (Spec.homEquiv q.toBase).hom).symm
    -- the base change of `X` to the field of definition of `q` has connected point space
    let : ConnectedSpace (points B (Spec (.of q.carrier)) q.contained
        ((OverShriek.relocalizeRestrict q.siteObject.hom).obj X)) :=
      connectedSpace_points_of_iso B (Spec (.of q.carrier)) q.contained
        (eqToIso (congrArg (fun t ↦ (OverShriek.relocalizeRestrict t).obj X) hqMor.symm))
        (hXconn q.carrier q.contained)
    -- viewed again over `k`, its point space is the same
    let e := relocalizedPointsHomeomorph B (Spec (.of q.carrier)) (Spec (.of k)) q.contained hk
      q.siteObject.hom ((OverShriek.relocalizeRestrict q.siteObject.hom).obj X)
      (isAlgebraicSpace_relocalizeRestrict B (Spec (.of q.carrier)) (Spec (.of k)) q.contained hk
        q.siteObject.hom X hX)
    let : ConnectedSpace (points B (Spec (.of k)) hk
        ((OverShriek.relocalizePresheafFunctor q.siteObject.hom).obj
          ((OverShriek.relocalizeRestrict q.siteObject.hom).obj X))) :=
      e.surjective.connectedSpace e.continuous
    -- and it is the fibre product of `X` with the field spectrum over `k`
    set qmap : yoneda.obj (Over.mk q.siteObject.hom) ⟶ Y := yonedaEquiv.symm q.value with hqmap
    have hsq₁ := OverShriek.isPullback_relocalizeRestrictCounit q.siteObject.hom X
      (fun W ↦ OverShriek.subsingleton_yoneda_obj_mkId W) f (qmap ≫ g)
    have hsq₂ : IsPullback (pullback.fst (pullback.snd f g) qmap ≫ pullback.fst f g)
        (pullback.snd (pullback.snd f g) qmap) f (qmap ≫ g) :=
      (IsPullback.of_hasPullback (pullback.snd f g) qmap).paste_horiz
        (IsPullback.of_hasPullback f g)
    let : ConnectedSpace (points B (Spec (.of k)) hk
        (fieldFibre B (Spec (.of k)) hk (pullback.snd f g) q)) :=
      connectedSpace_points_of_iso B (Spec (.of k)) hk
        (hsq₁.isoPullback ≪≫ hsq₂.isoPullback.symm) inferInstance
    change IsConnected (setFibre B (Spec (.of k)) hk (pullback.snd f g) q)
    rw [← range_pointsMap_fst_fieldFibre B (Spec (.of k)) hk (pullback.snd f g) q,
      ← Set.image_univ]
    exact isConnected_univ.image _ (continuous_pointsMap B (Spec (.of k)) hk
      (pullback.fst (pullback.snd f g) (yonedaEquiv.symm q.value))).continuousOn

end Product

/-! ### Extension of a separably closed ground field -/

section SepClosed

open CategoryTheory.Limits

attribute [local instance] pointTopology

/-- Restriction to a smaller base, read on points, is the lower-shriek extension followed by
the counit: both send a field-valued point to the same field spectrum with its structure
morphism composed with the morphism of bases, and the same section. -/
theorem pointsOfRelocalizeRestrict_eq (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')
    (F : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u) :
    pointsOfRelocalizeRestrict B S S' hS hS' g F =
      pointsMap B S' hS' _ (OverShriek.relocalizeRestrictCounit g F) ∘
        relocalizedPointsMap B S S' hS hS' g ((OverShriek.relocalizeRestrict g).obj F) := by
  funext x
  induction x using Quot.ind with | _ p => ?_
  refine congrArg (FieldValuedPoint.class B S' hS' F) ?_
  exact congrArg (fun v ↦ (FieldValuedPoint.mk p.carrier p.contained
      (p.toBase ≫ B.inclusion.map g) v : FieldValuedPoint B S' hS' F))
    (OverShriek.relocalizeDescend_self g (𝟙 ((OverShriek.relocalizeRestrict g).obj F))
      p.siteObject.hom p.value).symm

/-- A map which, up to a homeomorphism of its source, is a map with bijective induced map on
connected components has bijective induced map on connected components. -/
private theorem bijective_connectedComponentsMap_of_homeomorph {A D E : Type*}
    [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace E] (h : A ≃ₜ D) {ψ : D → E}
    {hψ : Continuous ψ} (hψbij : Function.Bijective hψ.connectedComponentsMap) {φ : A → E}
    (hφ : Continuous φ) (hcomm : ∀ a, φ a = ψ (h a)) :
    Function.Bijective hφ.connectedComponentsMap := by
  have hmk : ∀ a : A, hφ.connectedComponentsMap (ConnectedComponents.mk a) =
      hψ.connectedComponentsMap (ConnectedComponents.mk (h a)) := by
    intro a
    rw [hφ.connectedComponentsMap_mk, hψ.connectedComponentsMap_mk, hcomm a]
  refine ⟨?_, ?_⟩
  · intro a b hab
    induction a using Quotient.inductionOn with | h x => ?_
    induction b using Quotient.inductionOn with | h y => ?_
    have hab' : hψ.connectedComponentsMap (ConnectedComponents.mk (h x)) =
        hψ.connectedComponentsMap (ConnectedComponents.mk (h y)) := by
      rw [← hmk x, ← hmk y]
      exact hab
    have hsymm := congrArg h.symm.continuous.connectedComponentsMap (hψbij.1 hab')
    rwa [h.symm.continuous.connectedComponentsMap_mk,
      h.symm.continuous.connectedComponentsMap_mk, h.symm_apply_apply,
      h.symm_apply_apply] at hsymm
  · intro c
    obtain ⟨d, hd⟩ := hψbij.2 c
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe d
    refine ⟨ConnectedComponents.mk (h.symm y), ?_⟩
    rw [hmk, h.apply_symm_apply]
    exact hd

variable (B : BigFppfSite.{u}) (k K : Type u) [Field k] [Field K] [Algebra k K]
  (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))

/-- The fibre product of the spectra of two field extensions of a separably closed field is
connected: the spectrum of a field extension of a separably closed field is geometrically
connected over it (Stacks 037U and 0386), and a geometrically connected morphism has connected
base changes along open maps out of connected schemes. -/
@[ega "IV 4.4.4" "special case",
  ega "IV 4.5.21" "special case",
  ega "IV 4.5.8" "(i), special case",
  sga "3 X 9.7.2" "special case"]
theorem connectedSpace_pullback_spec_of_isSepClosed [IsSepClosed k] (L : Type u) [Field L]
    [Algebra k L] :
    ConnectedSpace (pullback (C := Scheme.{u})
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))) := by
  let f : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let gL : Spec (.of L) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let : GeometricallyConnected f :=
    (geometricallyConnected_spec_iff k K).2
      ((Algebra.isGeometricallyConnected_iff_connectedSpace_primeSpectrum k K).2 inferInstance)
  exact GeometricallyConnected.connectedSpace (pullback.snd f gL) (pullback.snd f gL).isOpenMap

/-- **Over a separably closed field the spectrum of a field extension is geometrically
connected.** The base change of `Spec K` to a further field extension `L` of `k` is the fibre
product `Spec K ×_{Spec k} Spec L`, which is connected. -/
theorem isGeometricallyConnected_yoneda_fieldExtensionMap [IsSepClosed k] :
    IsGeometricallyConnected B k hk
      (yoneda.obj (Over.mk (fieldExtensionMap B k K hk hK))) := by
  intro L _ _ hL
  have _ : HasPullbacks B.Schemes := inferInstance
  have hT : ConnectedSpace ((BigFppfOver.toScheme B (Spec (.of L)) hL).obj
      ((Over.pullback (fieldExtensionMap B k L hk hL)).obj
        (Over.mk (fieldExtensionMap B k K hk hK)))) := by
    have hp := IsPullback.map B.inclusion (IsPullback.of_hasPullback
      (Over.mk (fieldExtensionMap B k K hk hK)).hom (fieldExtensionMap B k L hk hL))
    have hconn : ConnectedSpace (pullback (C := Scheme.{u})
        (B.inclusion.map (Over.mk (fieldExtensionMap B k K hk hK)).hom)
        (B.inclusion.map (fieldExtensionMap B k L hk hL))) := by
      rw [show (Over.mk (fieldExtensionMap B k K hk hK)).hom
            = fieldExtensionMap B k K hk hK from rfl,
        map_fieldExtensionMap, map_fieldExtensionMap]
      exact connectedSpace_pullback_spec_of_isSepClosed k K L
    exact (Scheme.homeoOfIso hp.isoPullback).connectedSpace_iff.mpr hconn
  exact (pointsHomeomorphOfIso B (Spec (.of L)) hL
      (OverShriek.restrictYonedaIso (fieldExtensionMap B k L hk hL)
        (Over.mk (fieldExtensionMap B k K hk hK)))).connectedSpace_iff.mp
    ((schemePointsHomeomorph B (Spec (.of L)) hL _).connectedSpace_iff.mpr hT)

/-- The point space of a presheaf on the big fppf site over `S` and that of its lower-shriek
extension to the site over `Z` are homeomorphic for the point topologies: the uniqueness in
Tag 03BX identifies the point topology with the one induced along the canonical bijection. -/
noncomputable def relocalizedPointsHomeo (B : BigFppfSite.{u}) (S Z : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains Z) (g : B.obj hS ⟶ B.obj hZ)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    points B S hS F ≃ₜ points B Z hZ ((OverShriek.relocalizePresheafFunctor g).obj F) :=
  (relocalizedPointsEquiv B S Z hS hZ g F).toHomeomorphOfIsInducing
    ⟨congrArg (fun T : PointTopologyFamily B S hS ↦ T.topology F hF)
      (PointTopologyFamily.eq B S hS (pointTopologyFamily B S hS)
        (relocalizedPointTopologyFamily B S Z hS hZ g))⟩

variable (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)

/-- **Stacks 0A12, the bijection on connected components.** Let `k` be a separably closed
field, let `K/k` be a field extension whose spectrum lies in the chosen big fppf site and let
`X` be an algebraic space over `k`. The map `|X_K| → |X|` induced by the base change is a
bijection between the sets of connected components.

Viewed again over `k`, the base change `X_K` is the product `Spec K ×_k X`
(`CategoryTheory.OverShriek.isPullback_relocalizeRestrictCounit`), and `Spec K` is
geometrically connected over `k`, so Stacks 0A11 applies to the projection to `X`. -/
@[stacks 0A12 "bijection on connected components", ega "IV 4.4.6" "more general"]
theorem bijective_connectedComponents_relocalizeRestrict_of_isSepClosed [IsSepClosed k]
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) :
    Function.Bijective
      (continuous_pointsOfRelocalizeRestrict B (Spec (.of K)) (Spec (.of k)) hK hk
        (fieldExtensionMap B k K hk hK) X
        (isAlgebraicSpace_relocalizeRestrict B (Spec (.of K)) (Spec (.of k)) hK hk
          (fieldExtensionMap B k K hk hK) X hX)).connectedComponentsMap := by
  classical
  set g := fieldExtensionMap B k K hk hK with hgdef
  set π : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))) := OverShriek.toYonedaMkId X with hπ
  set τ : yoneda.obj (Over.mk g) ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))) :=
    OverShriek.toYonedaMkId (yoneda.obj (Over.mk g)) with hτ
  have hsq : IsPullback
      (OverShriek.relocalizeToYoneda g ((OverShriek.relocalizeRestrict g).obj X))
      (OverShriek.relocalizeRestrictCounit g X) τ π :=
    (OverShriek.isPullback_relocalizeRestrictCounit g X
      (fun W ↦ OverShriek.subsingleton_yoneda_obj_mkId W) π τ).flip
  have hXK := isAlgebraicSpace_relocalizeRestrict B (Spec (.of K)) (Spec (.of k)) hK hk g X hX
  refine bijective_connectedComponentsMap_of_homeomorph
    ((relocalizedPointsHomeo B (Spec (.of K)) (Spec (.of k)) hK hk g
        ((OverShriek.relocalizeRestrict g).obj X) hXK).trans
      (pointsHomeomorphOfIso B (Spec (.of k)) hk hsq.isoPullback))
    (bijective_connectedComponents_pullback_of_isGeometricallyConnected B k hk
      (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (Over.mk g)) hX
      (isGeometricallyConnected_yoneda_fieldExtensionMap B k K hk hK) τ π) _ ?_
  intro a
  have hcounit : hsq.isoPullback.hom ≫ pullback.snd τ π =
      OverShriek.relocalizeRestrictCounit g X := hsq.isoPullback_hom_snd
  have hstep := congrFun (pointsMap_comp B (Spec (.of k)) hk
      ((OverShriek.relocalizePresheafFunctor g).obj ((OverShriek.relocalizeRestrict g).obj X))
      hsq.isoPullback.hom (pullback.snd τ π))
    (relocalizedPointsMap B (Spec (.of K)) (Spec (.of k)) hK hk g
      ((OverShriek.relocalizeRestrict g).obj X) a)
  rw [hcounit, Function.comp_apply] at hstep
  have h1 := congrFun (pointsOfRelocalizeRestrict_eq B (Spec (.of K)) (Spec (.of k)) hK hk g X) a
  rw [Function.comp_apply] at h1
  exact h1.trans hstep

/-- The restriction of a presheaf along the morphism of the trivial field extension is the
presheaf itself. -/
private noncomputable def relocalizeRestrictSelfIso :
    (OverShriek.relocalizeRestrict (fieldExtensionMap B k k hk hk)).obj X ≅ X := by
  have hid : fieldExtensionMap B k k hk hk = 𝟙 (B.obj hk) := by
    apply B.inclusion.map_injective
    rw [map_fieldExtensionMap, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    exact (B.inclusion.map_id (B.obj hk)).symm
  exact eqToIso (congrArg (fun t ↦ (OverShriek.relocalizeRestrict t).obj X) hid) ≪≫
    Functor.isoWhiskerRight (NatIso.op (Over.mapId (B.obj hk))) X ≪≫
      Functor.isoWhiskerRight (Functor.opId (BigFppfOver B (Spec (.of k)) hk)) X ≪≫
        Functor.leftUnitor X

/-- Connectedness of a space is nonemptiness together with there being at most one connected
component. -/
private theorem connectedSpace_iff_nonempty_subsingleton (α : Type*) [TopologicalSpace α] :
    ConnectedSpace α ↔ Nonempty α ∧ Subsingleton (ConnectedComponents α) := by
  rw [connectedSpace_iff_connectedComponent]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨⟨x⟩, ⟨fun a b ↦ ?_⟩⟩
    obtain ⟨a, rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨b, rfl⟩ := ConnectedComponents.surjective_coe b
    exact ConnectedComponents.coe_eq_coe.mpr
      ((connectedComponent_eq (show a ∈ connectedComponent x by simp [hx])).symm.trans
        (connectedComponent_eq (show b ∈ connectedComponent x by simp [hx])))
  · rintro ⟨⟨x⟩, hcc⟩
    exact ⟨x, Set.eq_univ_of_forall fun y ↦ (ConnectedComponents.coe_eq_coe').mp
      (hcc.elim (ConnectedComponents.mk y) (ConnectedComponents.mk x))⟩

/-- **Stacks 0A12, geometric connectedness.** Over a separably closed field an algebraic space
is geometrically connected exactly when its space of points is connected. -/
@[stacks 0A12 "geometric connectedness"]
theorem isGeometricallyConnected_iff_connectedSpace_of_isSepClosed [IsSepClosed k]
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) :
    IsGeometricallyConnected B k hk X ↔ ConnectedSpace (points B (Spec (.of k)) hk X) := by
  refine ⟨fun h ↦ connectedSpace_points_of_iso B (Spec (.of k)) hk
    (relocalizeRestrictSelfIso B k hk X) (h k hk), fun h L _ _ hL ↦ ?_⟩
  let : ConnectedSpace (points B (Spec (.of k)) hk X) := h
  have hbij :=
    bijective_connectedComponents_relocalizeRestrict_of_isSepClosed B k L hk hL X hX
  obtain ⟨hne, hsub⟩ := (connectedSpace_iff_nonempty_subsingleton _).mp h
  refine (connectedSpace_iff_nonempty_subsingleton _).mpr ⟨?_, ⟨fun a b ↦ hbij.1 ?_⟩⟩
  · obtain ⟨x⟩ := hne
    obtain ⟨c, -⟩ := hbij.2 (ConnectedComponents.mk x)
    obtain ⟨p, -⟩ := ConnectedComponents.surjective_coe c
    exact ⟨p⟩
  · exact hsub.elim _ _

end SepClosed

/-! ### Testing geometric connectedness on a separable closure -/

section SepClosure

attribute [local instance] pointTopology

/-- **Stacks 0A13.** Let `k` be a field, let `K` be a separable algebraic closure of `k` whose
spectrum lies in the chosen big fppf site and let `X` be an algebraic space over `k`. Then `X`
is geometrically connected over `k` if and only if the base change `X_K` has a connected space
of points.

Geometric connectedness over `k` is geometric connectedness of `X_K` over `K` by Stacks 0A10,
and over the separably closed field `K` that is connectedness by Stacks 0A12. -/
@[stacks 0A13]
theorem isGeometricallyConnected_iff_connectedSpace_sepClosure (B : BigFppfSite.{u})
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) :
    IsGeometricallyConnected B k hk X ↔
      ConnectedSpace (points B (Spec (.of K)) hK
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj X)) := by
  let : IsSepClosed K := IsSepClosure.sep_closed k
  exact (isGeometricallyConnected_iff_relocalizeRestrict B k K hk hK X hX).trans
    (isGeometricallyConnected_iff_connectedSpace_of_isSepClosed B K hK _
      (isAlgebraicSpace_relocalizeRestrict B (Spec (.of K)) (Spec (.of k)) hK hk
        (fieldExtensionMap B k K hk hK) X hX))

end SepClosure

end AlgebraicGeometry.Space

end
