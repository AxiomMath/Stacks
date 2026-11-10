module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RelocalizationBaseChangeModules

/-!
# Restriction of modules along a cocontinuous functor has a right adjoint

Let `w : X ⥤ Y` be a functor of sites and `T` a presheaf of rings on `Y`. Restriction along `w`
takes a presheaf of `T`-modules to a presheaf of `w.op ⋙ T`-modules — Mathlib's
`CategoryTheory.PresheafOfModules.pushforward₀`, which on underlying presheaves of abelian groups
is precomposition with `w.op`. When `w` is cocontinuous it is the inverse image of the morphism of
topoi it induces (Stacks 00XO), whose direct image is right Kan extension along `w.op`; on
presheaves of modules that direct image is `Stacks.SheafOfModules.ranPushforward`.

This file proves the two are adjoint, for the structure map `T ⟶ {}_sw (w.op ⋙ T)` given by the
unit of the Kan-extension adjunction — the structure map that makes the restricted presheaf of
rings *the* one on `X`, so that the inverse image of modules is restriction on the nose — and
then the same on sheaves of modules, for a functor continuous as well as cocontinuous and a sheaf
of rings on `Y`.

So restriction of sheaves of modules along such a functor has a right adjoint. That is what
`StacksFrontier/CategoryTheory/Sites/Simplicial/ComponentModuleSumFormulaPresheaf.lean` records as
missing for case (A) of the direct-sum formula of Stacks 0D72, which obtains the formula on the
right-adjoint side, and it is also what identifies sheafification of presheaves of modules with
restriction to a subsite, which is what case (B) of that formula needs.

## Main definitions

* `Stacks.SheafOfModules.RestrictRan.unitRingHom`: the structure map of the restricted presheaf
  of rings, namely the unit of the right-Kan-extension adjunction.
* `Stacks.SheafOfModules.RestrictRan.homEquiv`: the hom bijection.
* `Stacks.SheafOfModules.RestrictRan.adjunction`: the adjunction `w^{-1} ⊣ {}_sw` on presheaves
  of modules.
* `Stacks.SheafOfModules.RestrictRan.ringSheaf`: the restriction of a sheaf of rings along a
  continuous functor.
* `Stacks.SheafOfModules.RestrictRan.sheafUnit`: its structure map, the unit read as a morphism
  of sheaves of rings.
* `Stacks.SheafOfModules.RestrictRan.sheafAdjunction`: the adjunction `w^{-1} ⊣ {}_sw` on sheaves
  of modules.

## Main results

* `Stacks.SheafOfModules.RestrictRan.scalarπ_unitRingHom`: for the unit structure map, the ring
  map that `Stacks.SheafOfModules.ranSMul` acts through at the index `(U, ψ)` is the restriction
  map of the presheaf of rings along `ψ`.
* `Stacks.SheafOfModules.RestrictRan.sheafAdjunction_unit_app_val`: the unit of the adjunction on
  sheaves of modules is, on underlying presheaves of modules, the unit of the adjunction on
  presheaves of modules.

## Implementation notes

The whole proof rests on one identity, already available as
`Stacks.SheafOfModules.ranAdjunction_unit_app_app_comp_ranπ`: the unit of the Kan-extension
adjunction, followed by the leg at `(a, ψ)` of the limit cone computing the extension, is the
restriction map along `ψ`. It holds for a presheaf of abelian groups and for a presheaf of rings
at once, which is exactly why the adjunct of a linear map is linear — the ring map through which
scalar multiplication on the right Kan extension acts at the index `(U, ψ)` is then `T(ψ)`, and
the semilinearity of the restriction maps of the source does the rest.

The adjunction is obtained from the adjunction on underlying presheaves of abelian groups by
cutting it down to the linear maps. The two hom bijections and the two naturality squares are all
proved by `CategoryTheory.Functor.map_injective` for
`CategoryTheory.PresheafOfModules.toPresheaf`, which is faithful: the underlying transformations
of both sides are literally the two sides of the corresponding statement about the Kan-extension
adjunction. The equivalence argument of each of those appeals has to be written out rather than
left to unification — the right Kan extension of a presheaf is built from
`CategoryTheory.Limits.getLimitCone`, which this library does not see through, so the elaborator
cannot discover it from the expected type.

Three identities are stated separately in the spelling their call site has rather than rewritten
into place: scalar multiplication on the restriction of a presheaf of modules, scalar
multiplication on its direct image, and the linearity of a morphism out of a restriction. Each is
a `rfl` or an immediate consequence of `Stacks.SheafOfModules.smulPresheaf_naturality`, but
`pushforward₀` and `ranPushforward` are `def`s, so a goal mentioning both spellings of one scalar
multiplication is not type-correct at `implicit` transparency and a rewrite cannot build its
motive.

The passage to sheaves is `CategoryTheory.Adjunction.restrictFullyFaithful` along the two
forgetful functors to presheaves of modules, with both comparison isomorphisms the identity:
restriction of sheaves of modules with the identity structure map and `pushforward₀` are the same
functor on underlying presheaves of modules — Mathlib's
`CategoryTheory.SheafOfModules.pushforward` at the identity is `pushforward₀` followed by
restriction of scalars along an identity, which is definitionally nothing — and the direct image
of sheaves of modules is `ranPushforward` on underlying presheaves of modules by construction.

The two Grothendieck topologies are explicit arguments of the statements on sheaves. They occur
only inside the restricted sheaf of rings, so they are not determined by the other arguments, and
leaving them implicit makes the continuity instance of the restriction unresolvable.

## References

* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 0FN3](https://stacks.math.columbia.edu/tag/0FN3)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe v r v₁ u₁ v₂ u₂ uA vA uB vB uH vH

namespace Stacks.SheafOfModules.RestrictRan

section KanExtension

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B] (L : A ⥤ B)
  {H : Type uH} [Category.{vH} H] [∀ F : A ⥤ H, L.HasRightKanExtension F]

/-- The adjunct of a transformation out of the restriction, followed by the leg at
`(a, ψ : b ⟶ L(a))`, is the restriction map along `ψ` followed by the transformation. -/
@[reassoc]
lemma homEquiv_app_comp_ranπ {G : B ⥤ H} {F : A ⥤ H} (α : L ⋙ G ⟶ F) (b : B)
    (j : StructuredArrow b L) :
    (((L.ranAdjunction H).homEquiv G F) α).app b ≫ ranπ L F b j
      = G.map j.hom ≫ α.app j.right := by
  rw [Adjunction.homEquiv_unit]
  dsimp
  rw [Category.assoc, ranπ_map_functor, ← Category.assoc,
    ranAdjunction_unit_app_app_comp_ranπ L G b j]

/-- The inverse adjunct of a transformation into the right Kan extension, at an object in the
image of `L`. -/
lemma homEquiv_symm_app {G : B ⥤ H} {F : A ⥤ H} (g : G ⟶ L.ran.obj F) (a : A) :
    (((L.ranAdjunction H).homEquiv G F).symm g).app a
      = g.app (L.obj a) ≫ (L.ranCounit.app F).app a := by
  rw [Adjunction.homEquiv_counit]
  simp

/-- The leg at the index `(a, 𝟙)` is the counit of the Kan-extension adjunction. -/
lemma ranπ_mk_id (G : A ⥤ H) (a : A) :
    ranπ L G (L.obj a) (StructuredArrow.mk (𝟙 (L.obj a))) = (L.ranCounit.app G).app a := by
  dsimp only [ranπ]
  simp

end KanExtension

section Presheaf

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y] (w : X ⥤ Y)
  {T : Yᵒᵖ ⥤ RingCat.{r}}
  [∀ F : Xᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F]

/-- The structure map making the right Kan extension along `w.op` of the restricted presheaf of
rings a direct image: the unit of the Kan-extension adjunction. -/
abbrev unitRingHom : T ⟶ w.op.ran.obj (w.op ⋙ T) :=
  (w.op.ranAdjunction RingCat.{r}).unit.app T

omit [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F] in
/-- For the unit structure map the ring map attached to `(U, ψ : V ⟶ w.op(U))` is the restriction
map of the presheaf of rings along `ψ`. -/
lemma scalarπ_unitRingHom (V : Yᵒᵖ) (j : StructuredArrow V w.op) :
    scalarπ w (unitRingHom w (T := T)) V j = T.map j.hom :=
  ranAdjunction_unit_app_app_comp_ranπ w.op T V j

variable (M : PresheafOfModules.{v} T) (N : PresheafOfModules.{v} (w.op ⋙ T))

/-- The underlying transformation of a morphism of presheaves of modules out of the restriction
along `w`, read as a transformation out of the restriction of the underlying presheaf of abelian
groups. -/
abbrev sourceMap (α : (PresheafOfModules.pushforward₀.{v} w T).obj M ⟶ N) :
    w.op ⋙ M.presheaf ⟶ N.presheaf :=
  presheafMap α

omit [∀ F : Xᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F] in
/-- A morphism of presheaves of modules out of the restriction along `w` commutes with scalar
multiplication, read with the scalar multiplication of the source presheaf itself.

This is `Stacks.SheafOfModules.smulPresheaf_naturality`; the scalar multiplication on the
restriction of `M` along `w` and the scalar multiplication on `M` at the corresponding object are
the same endomorphism, but the two spellings are not syntactically equal, and a goal that
mentions both is not type-correct at `implicit` transparency. So the identity is stated once here,
in the spelling its call site has, and applied as a term. -/
lemma smulPresheaf_naturality_source
    (α : (PresheafOfModules.pushforward₀.{v} w T).obj M ⟶ N) (U : Xᵒᵖ) (s : T.obj (w.op.obj U)) :
    smulPresheaf M (w.op.obj U) s ≫ (sourceMap w M N α).app U
      = (sourceMap w M N α).app U ≫ smulPresheaf N U s :=
  smulPresheaf_naturality α U s

/-- The adjunct of the underlying transformation of a morphism of presheaves of modules out of
the restriction is linear for the module structure of the direct image. -/
lemma homEquiv_smul (α : (PresheafOfModules.pushforward₀.{v} w T).obj M ⟶ N) (V : Yᵒᵖ)
    (rr : T.obj V) :
    smulPresheaf M V rr ≫
        (((w.op.ranAdjunction AddCommGrpCat.{v}).homEquiv M.presheaf N.presheaf)
          (sourceMap w M N α)).app V
      = (((w.op.ranAdjunction AddCommGrpCat.{v}).homEquiv M.presheaf N.presheaf)
          (sourceMap w M N α)).app V ≫ ranSMul w (unitRingHom w (T := T)) N V rr := by
  refine ran_hom_ext w.op N.presheaf (fun j => ?_)
  simp only [Category.assoc]
  rw [homEquiv_app_comp_ranπ, ranSMul_π, homEquiv_app_comp_ranπ_assoc, scalarπ_unitRingHom,
    smulPresheaf_map_assoc, smulPresheaf_naturality_source w M N α j.right]

/-- Scalar multiplication on the direct image of a presheaf of modules is `ranSMul`.

Stated here because `Stacks.SheafOfModules.ranPushforward` is a `def`, so the two spellings are
not syntactically equal. -/
lemma smulPresheaf_ranPushforward (V : Yᵒᵖ) (rr : T.obj V) :
    smulPresheaf ((ranPushforward.{v} w (unitRingHom w (T := T))).obj N) V rr
      = ranSMul w (unitRingHom w (T := T)) N V rr :=
  rfl

/-- The underlying transformation of a morphism of presheaves of modules into the direct image,
read as a transformation into the right Kan extension of the underlying presheaf of abelian
groups. -/
abbrev targetMap (β : M ⟶ (ranPushforward.{v} w (unitRingHom w)).obj N) :
    M.presheaf ⟶ w.op.ran.obj N.presheaf :=
  presheafMap β

/-- A morphism of presheaves of modules into the direct image commutes with scalar
multiplication, read with `ranSMul` on the target. -/
lemma smulPresheaf_naturality_target (β : M ⟶ (ranPushforward.{v} w (unitRingHom w)).obj N)
    (V : Yᵒᵖ) (rr : T.obj V) :
    smulPresheaf M V rr ≫ (targetMap w M N β).app V
      = (targetMap w M N β).app V ≫ ranSMul w (unitRingHom w (T := T)) N V rr :=
  smulPresheaf_naturality β V rr

/-- The adjunct of the underlying transformation of a morphism of presheaves of modules into the
direct image is linear. -/
lemma homEquiv_symm_smul (β : M ⟶ (ranPushforward.{v} w (unitRingHom w)).obj N) (U : Xᵒᵖ)
    (s : T.obj (w.op.obj U)) :
    smulPresheaf M (w.op.obj U) s ≫
        (((w.op.ranAdjunction AddCommGrpCat.{v}).homEquiv M.presheaf N.presheaf).symm
          (targetMap w M N β)).app U
      = (((w.op.ranAdjunction AddCommGrpCat.{v}).homEquiv M.presheaf N.presheaf).symm
          (targetMap w M N β)).app U ≫ smulPresheaf N U s := by
  have hleg := ranSMul_π w (unitRingHom w (T := T)) N (w.op.obj U) s
    (StructuredArrow.mk (𝟙 (w.op.obj U)))
  rw [ranπ_mk_id, scalarπ_unitRingHom] at hleg
  simp only [StructuredArrow.mk_right, StructuredArrow.mk_hom_eq_self] at hleg
  rw [homEquiv_symm_app, ← Category.assoc, smulPresheaf_naturality_target, Category.assoc, hleg,
    Category.assoc]
  simp

/-- The hom bijection of the adjunction between restriction along `w` and the direct image. -/
def homEquiv :
    ((PresheafOfModules.pushforward₀.{v} w T).obj M ⟶ N) ≃
      (M ⟶ (ranPushforward.{v} w (unitRingHom w)).obj N) where
  toFun α := PresheafOfModules.homMk
    (((w.op.ranAdjunction AddCommGrpCat.{v}).homEquiv M.presheaf N.presheaf)
      (sourceMap w M N α))
    (fun V rr m => ConcreteCategory.congr_hom (homEquiv_smul w M N α V rr) m)
  invFun β := PresheafOfModules.homMk
    (((w.op.ranAdjunction AddCommGrpCat.{v}).homEquiv M.presheaf N.presheaf).symm
      (targetMap w M N β))
    (fun U s m => ConcreteCategory.congr_hom (homEquiv_symm_smul w M N β U s) m)
  left_inv α := (PresheafOfModules.toPresheaf _).map_injective
    (Equiv.symm_apply_apply
      ((w.op.ranAdjunction AddCommGrpCat.{v}).homEquiv M.presheaf N.presheaf)
      (sourceMap w M N α))
  right_inv β := (PresheafOfModules.toPresheaf _).map_injective
    (Equiv.apply_symm_apply
      ((w.op.ranAdjunction AddCommGrpCat.{v}).homEquiv M.presheaf N.presheaf)
      (targetMap w M N β))

variable (T)

/-- **The direct image along a cocontinuous functor is right adjoint to restriction, on presheaves
of modules.** -/
def adjunction :
    PresheafOfModules.pushforward₀.{v} w T ⊣ ranPushforward.{v} w (unitRingHom w (T := T)) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N => homEquiv w M N
      homEquiv_naturality_left_symm := fun {_ M N} f g =>
        (PresheafOfModules.toPresheaf _).map_injective
          ((w.op.ranAdjunction AddCommGrpCat.{v}).homEquiv_naturality_left_symm
            (presheafMap f) (targetMap w M N g))
      homEquiv_naturality_right := fun {M N _} f g =>
        (PresheafOfModules.toPresheaf _).map_injective
          ((w.op.ranAdjunction AddCommGrpCat.{v}).homEquiv_naturality_right
            (sourceMap w M N f) (presheafMap g)) }

/-- **The hom bijection of the adjunction is, on underlying presheaves of abelian groups, the hom
bijection of the Kan-extension adjunction.** The adjunction is assembled by
`CategoryTheory.Adjunction.mkOfHomEquiv` from `Stacks.SheafOfModules.RestrictRan.homEquiv`, whose
value is `CategoryTheory.PresheafOfModules.homMk` at the Kan-extension adjunct of the underlying
transformation; so the forgetful functor to presheaves of abelian groups sends it to that
adjunct.

`CategoryTheory.Adjunction.homEquiv` is not a field of `CategoryTheory.Adjunction` but is derived
from the unit, so this is `CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv` and not a
definitional unfolding. It is what carries the defining property of the adjunct,
`Stacks.SheafOfModules.RestrictRan.homEquiv_app_comp_ranπ`, to a transpose taken along the
adjunction itself. -/
lemma toPresheaf_map_adjunction_homEquiv
    (a : (PresheafOfModules.pushforward₀.{v} w T).obj M ⟶ N) :
    (PresheafOfModules.toPresheaf T).map ((adjunction.{v} w T).homEquiv M N a) =
      ((w.op.ranAdjunction AddCommGrpCat.{v}).homEquiv M.presheaf N.presheaf)
        (sourceMap w M N a) := by
  simp only [adjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

end Presheaf

section Sheaf

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y] (w : X ⥤ Y)
  (JX : GrothendieckTopology X) (JY : GrothendieckTopology Y)
  [w.IsContinuous JX JY] [w.IsCocontinuous JX JY] (OY : Sheaf JY RingCat.{r})
  [∀ F : Xᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F]

/-- The restriction of a sheaf of rings along a continuous functor of sites. -/
abbrev ringSheaf : Sheaf JX RingCat.{r} :=
  (w.sheafPushforwardContinuous RingCat.{r} JX JY).obj OY

/-- The structure map exhibiting the restricted sheaf of rings as a sheaf of rings on the source
of the morphism of topoi attached to a cocontinuous functor: the unit of the Kan-extension
adjunction, read as a morphism of sheaves of rings. -/
def sheafUnit :
    OY ⟶ (w.sheafPushforwardCocontinuous RingCat.{r} JX JY).obj (ringSheaf w JX JY OY) :=
  ⟨unitRingHom w (T := OY.obj)⟩

/-- **The direct image along a cocontinuous functor is right adjoint to restriction, on sheaves
of modules.** In particular restriction of sheaves of modules along a continuous and cocontinuous
functor of sites has a right adjoint. -/
def sheafAdjunction :
    _root_.SheafOfModules.pushforward.{v} (F := w) (R := OY) (S := ringSheaf w JX JY OY)
        (𝟙 (ringSheaf w JX JY OY)) ⊣
      pushforwardCocontinuous.{v} w (sheafUnit w JX JY OY) :=
  Adjunction.restrictFullyFaithful (adjunction.{v} w OY.obj)
    (_root_.SheafOfModules.fullyFaithfulForget.{v} OY)
    (_root_.SheafOfModules.fullyFaithfulForget.{v} (ringSheaf w JX JY OY))
    (Iso.refl _) (Iso.refl _)

/-- **The unit of the adjunction on sheaves of modules is the unit of the adjunction on
presheaves of modules.** The sheaf-level adjunction is the presheaf-level one cut down along the
fully faithful forgetful functors at the identity comparisons, so its unit is the presheaf-level
unit up to the two identities that `CategoryTheory.Adjunction.restrictFullyFaithful` inserts. -/
theorem sheafAdjunction_unit_app_val (B : _root_.SheafOfModules.{v} OY) :
    ((sheafAdjunction.{v} w JX JY OY).unit.app B).val =
      (adjunction.{v} w OY.obj).unit.app B.val := by
  change (_root_.SheafOfModules.forget.{v} OY).map
    ((sheafAdjunction.{v} w JX JY OY).unit.app B) = _
  exact Eq.trans (Adjunction.map_restrictFullyFaithful_unit_app (adjunction.{v} w OY.obj)
    (_root_.SheafOfModules.fullyFaithfulForget.{v} OY)
    (_root_.SheafOfModules.fullyFaithfulForget.{v} (ringSheaf w JX JY OY)) _ _ B)
    (by
      change (adjunction.{v} w OY.obj).unit.app B.val ≫
          (ranPushforward.{v} w (unitRingHom w (T := OY.obj))).map
            (𝟙 ((PresheafOfModules.pushforward₀.{v} w OY.obj).obj B.val)) ≫
          𝟙 ((ranPushforward.{v} w (unitRingHom w (T := OY.obj))).obj
            ((PresheafOfModules.pushforward₀.{v} w OY.obj).obj B.val)) = _
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact Category.comp_id _)

end Sheaf

end Stacks.SheafOfModules.RestrictRan

end
