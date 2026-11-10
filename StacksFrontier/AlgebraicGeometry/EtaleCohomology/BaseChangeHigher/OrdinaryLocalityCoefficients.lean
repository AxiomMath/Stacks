module

public import Mathlib.CategoryTheory.Sites.LocalProperties
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDirectImages

/-!
# The square comparison of direct images at arbitrary coefficients, and the étale square

Direct images of sheaves on small étale sites with values in an arbitrary category, the
identification of the two composite direct images around a commutative square of schemes, and
the invertibility of the base change map of a cartesian square whose inverse-image legs are étale.

## Main definitions

* `Stacks.EtaleCohomology.smallEtalePushforwardAt`: the direct image along `f : X ⟶ Y`.
* `Stacks.EtaleCohomology.smallEtalePushforwardCompIsoAt`: the isomorphism
  `g_* ∘ f_* ≅ (f ≫ g)_*`.
* `Stacks.EtaleCohomology.smallEtaleSquarePushforwardIsoAt`: the isomorphism `e_* g_* ≅ h_* f_*`
  around a commutative square `e ≫ g = h ≫ f`.

## Main results

* `Stacks.EtaleCohomology.isIso_mate_smallEtaleSquarePushforwardIsoAt_of_isPullback`: for a
  cartesian square with `e` and `f` étale, the base change map is invertible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe w t u v z

namespace Stacks.EtaleCohomology

section Mates

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄


end Mates

/-- The direct image of sheaves with values in an arbitrary category along the morphism of small
étale sites induced by `f : X ⟶ Y`: restriction along base change by `f`. -/
public abbrev smallEtalePushforwardAt {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type w)
    [Category.{t} A] :
    Sheaf (smallEtaleTopology X) A ⥤ Sheaf (smallEtaleTopology Y) A :=
  (smallEtaleBaseChange f).sheafPushforwardContinuous A
    (smallEtaleTopology Y) (smallEtaleTopology X)

/-- The composition isomorphism `g_* ∘ f_* ≅ (f ≫ g)_*` for direct images at arbitrary
coefficients. -/
public def smallEtalePushforwardCompIsoAt {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Type w) [Category.{t} A] :
    smallEtalePushforwardAt f A ⋙ smallEtalePushforwardAt g A ≅
      smallEtalePushforwardAt (f ≫ g) A :=
  Functor.sheafPushforwardContinuousComp' (smallEtaleBaseChangeComp f g).symm _ _ _ _

/-- The identification `e_* g_* ≅ h_* f_*` of the two composite direct images around a
commutative square `e ≫ g = h ≫ f`, at arbitrary coefficients. -/
public def smallEtaleSquarePushforwardIsoAt {Y T X S : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f)
    (A : Type w) [Category.{t} A] :
    smallEtalePushforwardAt e A ⋙ smallEtalePushforwardAt g A ≅
      smallEtalePushforwardAt h A ⋙ smallEtalePushforwardAt f A :=
  smallEtalePushforwardCompIsoAt e g A ≪≫
    eqToIso (congrArg (fun k : Y ⟶ S => smallEtalePushforwardAt k A) w) ≪≫
    (smallEtalePushforwardCompIsoAt h f A).symm

section EtaleSquare

/-- The composition isomorphism for direct images acts on sections by the composition
isomorphism for the base change functors of sites. -/
private lemma pushCompAt_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Type w) [Category.{t} A] (F : Sheaf (smallEtaleTopology X) A) (V : Z.Etale) :
    ((smallEtalePushforwardCompIsoAt f g A).hom.app F).hom.app (op V) =
      F.obj.map ((smallEtaleBaseChangeComp f g).hom.app V).op := by
  exact Category.id_comp _

/-- The inverse of the composition isomorphism for direct images, on sections. -/
private lemma pushCompAt_inv_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Type w) [Category.{t} A] (F : Sheaf (smallEtaleTopology X) A) (V : Z.Etale) :
    ((smallEtalePushforwardCompIsoAt f g A).inv.app F).hom.app (op V) =
      F.obj.map ((smallEtaleBaseChangeComp f g).inv.app V).op := by
  exact Category.comp_id _

/-- Transport of the direct image along an equality of morphisms, on sections. -/
private lemma pushCongrAt_app {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (A : Type w) [Category.{t} A] (F : Sheaf (smallEtaleTopology X) A) (V : Y.Etale) :
    ((eqToHom (congrArg (fun k : X ⟶ Y => smallEtalePushforwardAt k A) h)).app F).hom.app
        (op V) =
      F.obj.map (eqToHom (congrArg
        (fun k => (smallEtaleBaseChange k).obj V) h.symm)).op := by
  subst g
  simp
  rfl

end EtaleSquare

section SquareApp

variable (A : Type w) [Category.{t} A] {Y T X S : Scheme.{u}}
  (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f)

/-- The square comparison of direct images is the composite of its three factors. -/
private lemma rightSquareAt_hom_eq :
    (smallEtaleSquarePushforwardIsoAt e h g f w A).hom =
      (smallEtalePushforwardCompIsoAt e g A).hom ≫
        eqToHom (congrArg (fun k : Y ⟶ S => smallEtalePushforwardAt k A) w) ≫
        (smallEtalePushforwardCompIsoAt h f A).inv :=
  rfl

/-- The same composite, with its three factors absorbed into a single contravariant map of `F`,
given the action of the middle factor on sections. -/
private lemma pushComp₃At_app_hom_app_map (F : Sheaf (smallEtaleTopology Y) A) (V : S.Etale)
    (β : smallEtalePushforwardAt (e ≫ g) A ⟶ smallEtalePushforwardAt (h ≫ f) A)
    (b : (smallEtaleBaseChange (h ≫ f)).obj V ⟶ (smallEtaleBaseChange (e ≫ g)).obj V)
    (hβ : (β.app F).hom.app (op V) = F.obj.map b.op) :
    (((smallEtalePushforwardCompIsoAt e g A).hom ≫ β ≫
        (smallEtalePushforwardCompIsoAt h f A).inv).app F).hom.app (op V) =
      F.obj.map ((smallEtaleBaseChangeComp h f).inv.app V ≫ b ≫
        (smallEtaleBaseChangeComp e g).hom.app V).op := by
  change _ ≫ (β.app F).hom.app (op V) ≫ _ = _
  rw [pushCompAt_hom_app, hβ, pushCompAt_inv_app]
  exact map_op_triple F.obj _ b _

/-- If `τ` is the composite of the two composition isomorphisms with a middle factor `β` acting on
sections by `F.obj.map b.op`, then `τ` acts on sections by `F.obj.map c.op` for the corresponding
composite `c` of site morphisms. -/
private lemma squarePushforwardIsoAt_app_of (F : Sheaf (smallEtaleTopology Y) A) (V : S.Etale)
    (τ : smallEtalePushforwardAt e A ⋙ smallEtalePushforwardAt g A ⟶
      smallEtalePushforwardAt h A ⋙ smallEtalePushforwardAt f A)
    (β : smallEtalePushforwardAt (e ≫ g) A ⟶ smallEtalePushforwardAt (h ≫ f) A)
    (b : (smallEtaleBaseChange (h ≫ f)).obj V ⟶ (smallEtaleBaseChange (e ≫ g)).obj V)
    (c : (smallEtaleBaseChange f ⋙ smallEtaleBaseChange h).obj V ⟶
      (smallEtaleBaseChange g ⋙ smallEtaleBaseChange e).obj V)
    (hβ : (β.app F).hom.app (op V) = F.obj.map b.op)
    (hτ : τ = (smallEtalePushforwardCompIsoAt e g A).hom ≫ β ≫
      (smallEtalePushforwardCompIsoAt h f A).inv)
    (hc : c = (smallEtaleBaseChangeComp h f).inv.app V ≫ b ≫
      (smallEtaleBaseChangeComp e g).hom.app V) :
    (τ.app F).hom.app (op V) = F.obj.map c.op := by
  subst hc
  exact (congrArg (fun z : smallEtalePushforwardAt e A ⋙ smallEtalePushforwardAt g A ⟶
      smallEtalePushforwardAt h A ⋙ smallEtalePushforwardAt f A =>
    (NatTrans.app z F).hom.app (op V)) hτ).trans
      (pushComp₃At_app_hom_app_map A e h g f F V β b hβ)

/-- For a commutative square `e ≫ g = h ≫ f` of schemes, a sheaf `F` on the small étale site of
`Y` with values in an arbitrary category and an object `V` of the small étale site of `S`, the
component at `V` of the comparison of the two composite direct images is `F` applied
contravariantly to the component at `V` of the comparison `Stacks.EtaleCohomology.siteSquare` of
the two composite base change functors. -/
private theorem smallEtaleSquarePushforwardIsoAt_app
    (F : Sheaf (smallEtaleTopology Y) A) (V : S.Etale) :
    ((smallEtaleSquarePushforwardIsoAt e h g f w A).hom.app F).hom.app (op V) =
      F.obj.map ((siteSquare e h g f w).hom.app V).op :=
  squarePushforwardIsoAt_app_of A e h g f F V
    (smallEtaleSquarePushforwardIsoAt e h g f w A).hom _ _ _ (pushCongrAt_app w A F V)
    (rightSquareAt_hom_eq A e h g f w) (siteSquare_hom_app e h g f w V)

end SquareApp

section SiteProjections


end SiteProjections

section EtaleSquareBaseChange

variable {Y T X S : Scheme.{u}}

/-- Composition with an étale morphism does not change the underlying morphism of schemes. -/
private lemma smallEtaleCompose_map_left {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    {A B : U.Etale} (z : A ⟶ B) : ((smallEtaleCompose j).map z).left = z.left :=
  rfl

/-- The counit of the site-level adjunction `smallEtaleCompose e ⊣ smallEtaleBaseChange e` at a
base change, on underlying schemes: the projection of the fibre product to the first factor,
written with the structure morphism of the base change reduced. -/
private lemma composeBaseChangeAdj_counit_left_baseChange (e : Y ⟶ T) [Etale e] (g : T ⟶ S)
    (W : S.Etale) :
    ((smallEtaleComposeBaseChangeAdj e).counit.app ((smallEtaleBaseChange g).obj W)).left =
      pullback.fst (pullback.snd W.hom g) e :=
  rfl

/-- The unit of the site-level adjunction `smallEtaleCompose f ⊣ smallEtaleBaseChange f`, on
underlying schemes: the morphism into the fibre product given by the identity and the structure
morphism. -/
private lemma composeBaseChangeAdj_unit_left (f : X ⟶ S) [Etale f] (V : X.Etale) :
    ((smallEtaleComposeBaseChangeAdj f).unit.app V).left =
      pullback.lift (𝟙 V.left) V.hom (Category.id_comp _) :=
  rfl

/-- The unit of the site-level adjunction, followed by the projection to `V`, is the identity. -/
private lemma composeBaseChangeAdj_unit_left_fst (f : X ⟶ S) [Etale f] (V : X.Etale) :
    ((smallEtaleComposeBaseChangeAdj f).unit.app V).left ≫
      pullback.fst ((smallEtaleCompose f).obj V).hom f = 𝟙 V.left :=
  pullback.lift_fst _ _ _

/-- Base change of a morphism of the small étale site, followed by the projection to the base. -/
@[reassoc]
lemma baseChange_map_left_fst (f : X ⟶ S) {V W : S.Etale} (k : V ⟶ W) :
    ((smallEtaleBaseChange f).map k).left ≫ pullback.fst W.hom f =
      pullback.fst V.hom f ≫ k.left :=
  pullback.lift_fst _ _ _

/-- A rearrangement of composites in a category: from `y ≫ z ≫ t = p ≫ q`, `x ≫ p = r ≫ k` and
`k ≫ q = 𝟙 n` follows `(x ≫ y ≫ z) ≫ t = r`. -/
private lemma comp_rearrange {C : Type*} [Category* C] {a b c d m n : C}
    {x : a ⟶ b} {y : b ⟶ c} {z : c ⟶ d} {t : d ⟶ n} {p : b ⟶ m} {q : m ⟶ n}
    {r : a ⟶ n} {k : n ⟶ m}
    (h₁ : y ≫ z ≫ t = p ≫ q) (h₂ : x ≫ p = r ≫ k) (h₃ : k ≫ q = 𝟙 n) :
    (x ≫ y ≫ z) ≫ t = r := by
  rw [Category.assoc, Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc, h₃,
    Category.comp_id]

/-- The mate of the site comparison of a cartesian square, followed by the projection to the
base: the component is the canonical morphism into the fibre product. -/
private lemma siteMate_left_fst (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S)
    (w : e ≫ g = h ≫ f) [Etale e] [Etale f] (V : X.Etale) :
    (((mateEquiv (smallEtaleComposeBaseChangeAdj f)
          (smallEtaleComposeBaseChangeAdj e)).symm (siteSquare e h g f w).hom).app V).left ≫
        pullback.fst ((smallEtaleCompose f).obj V).hom g =
      pullback.fst V.hom h := by
  refine (congrArg (fun z : (smallEtaleBaseChange h ⋙ smallEtaleCompose e).obj V ⟶
      (smallEtaleCompose f ⋙ smallEtaleBaseChange g).obj V =>
    z.left ≫ pullback.fst ((smallEtaleCompose f).obj V).hom g)
    (mate_symm_app_eq (smallEtaleComposeBaseChangeAdj f)
      (smallEtaleComposeBaseChangeAdj e) (siteSquare e h g f w).hom V)).trans ?_
  rw [etaleOver_comp₃_left, smallEtaleCompose_map_left, smallEtaleCompose_map_left,
    composeBaseChangeAdj_counit_left_baseChange]
  exact comp_rearrange (siteSquare_hom_fst e h g f w ((smallEtaleCompose f).obj V))
    (baseChange_map_left_fst h ((smallEtaleComposeBaseChangeAdj f).unit.app V))
    (composeBaseChangeAdj_unit_left_fst f V)

/-- The mate of the site comparison of a cartesian square is invertible: for a cartesian
square with `e` and `f` étale, the mate of `siteSquare` along the two site-level adjunctions
`smallEtaleComposeBaseChangeAdj` is, at an object `V` of the small étale site of `X`, the
canonical morphism `V ×_X Y ⟶ (V ⟶ S) ×_S T`, which is invertible. -/
private lemma isIso_siteMate_of_isPullback (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S)
    (w : e ≫ g = h ≫ f) (sq : IsPullback e h g f) [Etale e] [Etale f] (V : X.Etale) :
    IsIso (((mateEquiv (smallEtaleComposeBaseChangeAdj f)
      (smallEtaleComposeBaseChangeAdj e)).symm (siteSquare e h g f w).hom).app V) := by
  set t := ((mateEquiv (smallEtaleComposeBaseChangeAdj f)
    (smallEtaleComposeBaseChangeAdj e)).symm (siteSquare e h g f w).hom).app V with hdef
  have hw : pullback.fst V.hom h ≫ (V.hom ≫ f) = (pullback.snd V.hom h ≫ e) ≫ g := by
    rw [Category.assoc, sq.w, ← pullback.condition_assoc]
  have ht : t.left = pullback.lift (pullback.fst V.hom h) (pullback.snd V.hom h ≫ e) hw :=
    pullback.hom_ext ((siteMate_left_fst e h g f w V).trans (pullback.lift_fst _ _ _).symm)
      ((MorphismProperty.Over.w t).trans (pullback.lift_snd _ _ _).symm)
  have : IsIso ((Scheme.Etale.forget T ⋙ CategoryTheory.Over.forget T).map t) := by
    change IsIso t.left
    rw [ht]
    exact isIso_pullbackLift_of_isPullback sq V.hom hw
  exact isIso_of_reflects_iso t (Scheme.Etale.forget T ⋙ CategoryTheory.Over.forget T)

/-- The base change map of a cartesian square with both inverse-image legs étale, taken along the
restriction/direct-image adjunctions, is invertible. -/
private lemma isIso_restrictionMate_of_isPullback (A : Type w) [Category.{t} A]
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f)
    (sq : IsPullback e h g f) [Etale e] [Etale f] (F : Sheaf (smallEtaleTopology T) A) :
    IsIso (((mateEquiv
      ((smallEtaleComposeBaseChangeAdj e).sheafPushforwardContinuous
        (E := A) (smallEtaleTopology Y) (smallEtaleTopology T))
      ((smallEtaleComposeBaseChangeAdj f).sheafPushforwardContinuous
        (E := A) (smallEtaleTopology X) (smallEtaleTopology S))).symm
      (smallEtaleSquarePushforwardIsoAt e h g f w A).hom).app F) := by
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro V
  have hsec := mate_sheafPushforward_app (smallEtaleTopology X) (smallEtaleTopology S)
    (smallEtaleTopology Y) (smallEtaleTopology T)
    (smallEtaleComposeBaseChangeAdj f) (smallEtaleComposeBaseChangeAdj e)
    (siteSquare e h g f w).hom (smallEtaleSquarePushforwardIsoAt e h g f w A).hom
    (fun F V => smallEtaleSquarePushforwardIsoAt_app A e h g f w F V) F V.unop
  change IsIso ((((mateEquiv _ _).symm
    (smallEtaleSquarePushforwardIsoAt e h g f w A).hom).app F).hom.app (op V.unop))
  rw [hsec]
  have hV := isIso_siteMate_of_isPullback e h g f w sq V.unop
  exact inferInstanceAs (IsIso (F.obj.mapIso (asIso
    (((mateEquiv (smallEtaleComposeBaseChangeAdj f)
      (smallEtaleComposeBaseChangeAdj e)).symm
        (siteSquare e h g f w).hom).app V.unop)).op).hom)

/-- The base change map of a cartesian square with both inverse-image legs étale is invertible.
Let

```
Y --e--> T
|h       |g
X --f--> S
```

be a cartesian square of schemes with `e` and `f` étale, let the coefficients `A` be arbitrary,
and let `L e ⊣ e_*` and `L f ⊣ f_*` be any inverse-image/direct-image adjunctions for the direct
images along `e` and `f`. Then the base change map `f^{-1} g_* F ⟶ h_* e^{-1} F`, the mate of
the comparison of the two composite direct images around the square, is invertible for every
sheaf `F` on the small étale site of `T`. -/
public theorem isIso_mate_smallEtaleSquarePushforwardIsoAt_of_isPullback
    (A : Type w) [Category.{t} A]
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f)
    (sq : IsPullback e h g f) [Etale e] [Etale f]
    {LE : Sheaf (smallEtaleTopology T) A ⥤ Sheaf (smallEtaleTopology Y) A}
    {LF : Sheaf (smallEtaleTopology S) A ⥤ Sheaf (smallEtaleTopology X) A}
    (adjE : LE ⊣ smallEtalePushforwardAt e A) (adjF : LF ⊣ smallEtalePushforwardAt f A)
    (F : Sheaf (smallEtaleTopology T) A) :
    IsIso (((mateEquiv adjE adjF).symm
      (smallEtaleSquarePushforwardIsoAt e h g f w A).hom).app F) := by
  refine (isIso_mate_symm_iff adjE
    ((smallEtaleComposeBaseChangeAdj e).sheafPushforwardContinuous
      (E := A) (smallEtaleTopology Y) (smallEtaleTopology T))
    adjF
    ((smallEtaleComposeBaseChangeAdj f).sheafPushforwardContinuous
      (E := A) (smallEtaleTopology X) (smallEtaleTopology S))
    (smallEtaleSquarePushforwardIsoAt e h g f w A).hom
    (smallEtaleSquarePushforwardIsoAt e h g f w A).hom (Iso.refl _) (Iso.refl _) ?_ F).mpr
    (isIso_restrictionMate_of_isPullback A e h g f w sq F)
  refine NatTrans.ext (funext fun P => ?_)
  simp [TwoSquare.whiskerBottom, TwoSquare.whiskerTop]

end EtaleSquareBaseChange

end Stacks.EtaleCohomology

end
