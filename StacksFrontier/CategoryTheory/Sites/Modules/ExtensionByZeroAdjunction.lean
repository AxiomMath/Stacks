module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero for modules on a ringed site

Let `(C, O)` be a ringed site and let `U` be an object of `C`. Restriction along
`Over.forget U` sends a sheaf of `O`-modules to a sheaf of `O_U`-modules on the localized
site `C/U`. This file establishes that this restriction functor has a left adjoint `j_{U!}`
(extension by zero) at the level of *presheaves* of modules, and it computes the presheaf
whose sheafification is `j_{U!}`: its module of sections over `V` is the direct sum of the
modules `G(φ : V ⟶ U)` indexed by all maps `φ : V ⟶ U`.

Mathlib supplies the names but not the existence. Restriction is
`SheafOfModules.pushforward` along `Over.forget U` for the identity map of `O_U`, so
`SheafOfModules.pullback` is `j_{U!}`, `SheafOfModules.pullbackPushforwardAdjunction` is the
adjunction, and `SheafOfModules.pullbackIso` exhibits it as a sheafification — but all three
are defined only under the hypothesis `(SheafOfModules.pushforward φ).IsRightAdjoint`, which
is exactly the existence Stacks 03DI asserts, so none of them discharges it. What discharges
it here is `presheafRestrictionIsRightAdjoint`, the presheaf-level instance, from which
`Stacks.Sites.ExtensionByZero.sheafRestrictionIsRightAdjoint`
(`StacksFrontier/CategoryTheory/Sites/Modules/ExtensionByZeroExactness.lean`) obtains the
sheaf-level one; the hypothesis-free statements of Stacks 03DI — the displayed bijection and
the identification of `j_{U!} G` with the sheafification of the direct-sum presheaf — are in
`StacksFrontier/CategoryTheory/Sites/Modules/ExtensionByZeroDirectSumSheafification.lean`. The
direct-sum formula itself is proved here by building the direct-sum presheaf by hand and
checking that it satisfies the universal property of the presheaf-level pullback.

## Main definitions

* `Stacks.Sites.ExtensionByZero.directSumPresheaf`: the presheaf of modules whose sections
  over `V` are `⨁_{φ : V ⟶ U} G(φ)`.
* `Stacks.Sites.ExtensionByZero.extensionByZeroSummands`: the family of modules indexed by
  the maps `V ⟶ U` that this direct sum is taken over.

## Main results

* `Stacks.Sites.ExtensionByZero.directSumPresheafIso`: the direct-sum presheaf is the
  presheaf-level pullback along `Over.forget U`.
* `Stacks.Sites.ExtensionByZero.extensionByZeroPresheafSectionIso`: the direct-sum formula
  for the sections of the presheaf whose sheafification is `j_{U!} G`.
* `Stacks.Sites.ExtensionByZero.extensionByZeroPresheafSectionIso_inv_ι`: that comparison is
  the canonical one, namely the unit of the presheaf-level adjunction on each summand.

## Implementation notes

The direct-sum presheaf is produced at the level of a presheaf of rings `S` on `C`, since
nothing in its construction uses the sheaf condition; the statements for a ringed site are
the special case `S = O`. The universal property is checked against
`PresheafOfModules.pullbackPushforwardAdjunction`, which is what `SheafOfModules.pullbackIso`
sheafifies, so the resulting comparison is literally the unit of that adjunction on each
summand; `extensionByZeroPresheafSectionIso_inv_ι` records this.

It is also produced with the objects of `C` in a universe `c` unrelated to the universe `u`
of its morphisms, its rings and its module sections, since nothing in the construction of the
direct sum relates the two: the direct sum is indexed by the hom-set `V ⟶ U`, which lies in
`Type u` whatever the universe of the objects. The existence of the left adjoint is the one
step that does depend on the size of `C`, so the few declarations that mention
`PresheafOfModules.pullback` take `(PresheafOfModules.pushforward _).IsRightAdjoint` as a
hypothesis rather than obtaining it from Mathlib's smallness instance. For a site whose
objects lie in `Type u` that hypothesis is discharged by instance search, which is why the
sheaf-level section below, where `C : Type u`, never mentions it.

The auxiliary family `presheafSummands` is indexed by an object of `Cᵒᵖ` rather than of `C`,
even though the mathematics only involves `C`. The reason is that `directSumPresheaf` must
have `ModuleCat (S.obj X)` as its module of sections over `X : Cᵒᵖ`, whereas the coproduct of
a family indexed over `C` carries its `HasColimit` instance in `ModuleCat (S.obj (op V))`.
The two are definitionally equal, but the equality is not available to unification, which
cannot unfold `CategoryTheory.Limits.getColimitCocone`. Indexing by `Cᵒᵖ` makes the instances
match syntactically, which is what lets the proofs below rewrite with `Sigma.ι_desc` and
reduce to components with `Sigma.hom_ext`.

`extensionByZeroPresheafSectionIso_inv_ι` is stated with `HEq` because the two sides live in
`ModuleCat` over rings that are equal but not syntactically identical.

## References

* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero

universe u c

add_to_stacks 03DI "extension-by-zero functor" SheafOfModules.pullback
add_to_sga "3 I 4.6.1" "more general" SheafOfModules.pullback
add_to_sga "3 III 0.1.4" "more general" SheafOfModules.pullback
add_to_sga "4 VI 8.7.1" "partial" SheafOfModules.pullback
add_to_sga "4 XVII 4.1" SheafOfModules.pullback
add_to_sga "7 XIV 4.5" "more general" SheafOfModules.pullback
add_to_ega "IV 11.9.16" "more general" SheafOfModules.pullback
add_to_ega "IV 2.5.1" "partial" SheafOfModules.pullback
add_to_ega "IV 4.8.2" "more general" SheafOfModules.pullback
add_to_ega "IV 9.4.9" SheafOfModules.pullback
add_to_stacks 03DI "adjunction" SheafOfModules.pullbackPushforwardAdjunction
add_to_sga "3 VIIA 1.3" "more general" SheafOfModules.pullbackPushforwardAdjunction
add_to_stacks 03DI "sheafification" SheafOfModules.pullbackIso

section Presheaf

variable {C : Type c} [Category.{u} C] (U : C) (S : Cᵒᵖ ⥤ RingCat.{u})

/-- The family of modules indexed by the maps from `X.unop` to `U`, for a presheaf of modules
over a presheaf of rings `S`. -/
abbrev presheafSummands (G : PresheafOfModules.{u} ((Over.forget U).op ⋙ S)) (X : Cᵒᵖ) :
    (X.unop ⟶ U) → ModuleCat (S.obj X) :=
  fun φ => G.obj (op (Over.mk φ))

/-- The restriction map of `G` along `f`, from the summand indexed by `φ` to the summand
indexed by `f.unop ≫ φ`.

This is `G.map` of the evident map of `C/U`, but with its source and target spelled in terms
of `S.obj X` and `S.map f`. Those agree with what `G.map` produces only after unfolding
`Over.forget` and `Functor.op`; naming the morphism performs that identification once, where
the elaborator can still see it, and keeps it out of the rewriting below. -/
noncomputable def summandRestriction (G : PresheafOfModules.{u} ((Over.forget U).op ⋙ S))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (φ : X.unop ⟶ U) :
    presheafSummands U S G X φ ⟶
      (ModuleCat.restrictScalars (S.map f).hom).obj
        (presheafSummands U S G Y (f.unop ≫ φ)) :=
  G.map (Over.homMk f.unop : Over.mk (f.unop ≫ φ) ⟶ Over.mk φ).op

/-- The restriction maps of `directSumPresheaf`: the summand indexed by `φ` is sent into the
summand indexed by `f ≫ φ` by the restriction map of `G`. -/
noncomputable def presheafRestriction (G : PresheafOfModules.{u} ((Over.forget U).op ⋙ S))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (∐ presheafSummands U S G X) ⟶
      (ModuleCat.restrictScalars (S.map f).hom).obj (∐ presheafSummands U S G Y) :=
  Sigma.desc fun φ =>
    summandRestriction U S G f φ ≫
      (ModuleCat.restrictScalars (S.map f).hom).map
        (Sigma.ι (presheafSummands U S G Y) (f.unop ≫ φ))

/-- `presheafRestriction` precomposed with the inclusion of the summand indexed by `φ`. -/
@[reassoc]
lemma ι_comp_presheafRestriction (G : PresheafOfModules.{u} ((Over.forget U).op ⋙ S))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (φ : X.unop ⟶ U) :
    Sigma.ι (presheafSummands U S G X) φ ≫ presheafRestriction U S G f =
      summandRestriction U S G f φ ≫
        (ModuleCat.restrictScalars (S.map f).hom).map
          (Sigma.ι (presheafSummands U S G Y) (f.unop ≫ φ)) :=
  Sigma.ι_desc _ _

/-- `presheafRestriction` applied to an element of the summand indexed by `φ`. -/
@[simp]
lemma presheafRestriction_ι_apply
    (G : PresheafOfModules.{u} ((Over.forget U).op ⋙ S))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (φ : X.unop ⟶ U) (ψ : Y.unop ⟶ U)
    (h : f.unop ≫ φ = ψ) (x : G.obj (op (Over.mk φ))) :
    presheafRestriction U S G f (Sigma.ι (presheafSummands U S G X) φ x) =
      Sigma.ι (presheafSummands U S G Y) ψ
        (G.restrictₛₗ (Over.homMk f.unop h : Over.mk ψ ⟶ Over.mk φ).op x) := by
  subst ψ
  exact congrArg (fun k => k x) (ι_comp_presheafRestriction U S G f φ)

/-- The presheaf of `S`-modules whose sections over `V` are the direct sum of the sections of
`G` over all objects `φ : V ⟶ U` of `C/U`. -/
noncomputable def directSumPresheaf (G : PresheafOfModules.{u} ((Over.forget U).op ⋙ S)) :
    PresheafOfModules.{u} S where
  obj X := ∐ presheafSummands U S G X
  map f := presheafRestriction U S G f
  map_id X := by
    apply Sigma.hom_ext; intro φ; ext x
    change presheafRestriction U S G (𝟙 X) (Sigma.ι (presheafSummands U S G X) φ x) =
      Sigma.ι (presheafSummands U S G X) φ x
    rw [presheafRestriction_ι_apply U S G (𝟙 X) φ φ (Category.id_comp φ)]
    change Sigma.ι (presheafSummands U S G X) φ (G.map (𝟙 _) x) = _
    rw [G.map_id]
    rfl
  map_comp {X Y Z} f g := by
    apply Sigma.hom_ext; intro φ; ext x
    change presheafRestriction U S G (f ≫ g)
        (Sigma.ι (presheafSummands U S G X) φ x) =
      presheafRestriction U S G g
        (presheafRestriction U S G f (Sigma.ι (presheafSummands U S G X) φ x))
    rw [presheafRestriction_ι_apply U S G (f ≫ g) φ (g.unop ≫ f.unop ≫ φ)
      (Category.assoc _ _ _), presheafRestriction_ι_apply U S G f φ (f.unop ≫ φ) rfl,
      presheafRestriction_ι_apply U S G g (f.unop ≫ φ) (g.unop ≫ f.unop ≫ φ) rfl]
    change @Eq (↑(∐ presheafSummands U S G Z)) _ _
    exact congrArg
      (fun t : G.obj (op (Over.mk (g.unop ≫ f.unop ≫ φ))) =>
        Sigma.ι (presheafSummands U S G Z) (g.unop ≫ f.unop ≫ φ) t)
      (G.map_comp_apply
        (Over.homMk f.unop : Over.mk (f.unop ≫ φ) ⟶ Over.mk φ).op
        (Over.homMk g.unop : Over.mk (g.unop ≫ f.unop ≫ φ) ⟶
          Over.mk (f.unop ≫ φ)).op x)

/-- The sections of `directSumPresheaf` are the coproduct of the summands. -/
lemma directSumPresheaf_obj (G : PresheafOfModules.{u} ((Over.forget U).op ⋙ S)) (X : Cᵒᵖ) :
    (directSumPresheaf U S G).obj X = ∐ presheafSummands U S G X := rfl

/-- The restriction maps of `directSumPresheaf` are `presheafRestriction`. -/
lemma directSumPresheaf_map (G : PresheafOfModules.{u} ((Over.forget U).op ⋙ S))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (directSumPresheaf U S G).map f = presheafRestriction U S G f := rfl

/-- Restriction of presheaves of modules along `Over.forget U`, i.e. `j_U^*` at the level of
presheaves. -/
noncomputable abbrev restrictionFunctor :
    PresheafOfModules.{u} S ⥤ PresheafOfModules.{u} ((Over.forget U).op ⋙ S) :=
  PresheafOfModules.pushforward (F := Over.forget U)
    (𝟙 ((Over.forget U).op ⋙ S))

/-- The component of a map `α : G ⟶ j_U^* H` at the object `φ : X.unop ⟶ U` of `C/U`, with
its source and target spelled as `presheafSummands U S G X φ` and `H.obj X`. As with
`summandRestriction`, naming it performs the identification of those spellings once. -/
noncomputable def descComponent {G : PresheafOfModules.{u} ((Over.forget U).op ⋙ S)}
    {H : PresheafOfModules.{u} S} (α : G ⟶ (restrictionFunctor U S).obj H) (X : Cᵒᵖ)
    (φ : X.unop ⟶ U) : presheafSummands U S G X φ ⟶ H.obj X :=
  α.app (op (Over.mk φ))

/-- The canonical map from `G` to the restriction of `directSumPresheaf G`, given over
`φ : V ⟶ U` by the inclusion of the summand indexed by `φ`. -/
noncomputable def directSumInclusion (G : PresheafOfModules.{u} ((Over.forget U).op ⋙ S)) :
    G ⟶ (restrictionFunctor U S).obj (directSumPresheaf U S G) where
  app X := Sigma.ι (presheafSummands U S G (op X.unop.left)) X.unop.hom
  naturality {X Y} f := by
    ext x
    change Sigma.ι (presheafSummands U S G (op Y.unop.left)) Y.unop.hom (G.restrictₛₗ f x) =
      presheafRestriction U S G f.unop.left.op
        (Sigma.ι (presheafSummands U S G (op X.unop.left)) X.unop.hom x)
    rw [presheafRestriction_ι_apply U S G f.unop.left.op X.unop.hom Y.unop.hom (Over.w f.unop)]
    rfl

/-- The naturality square for the map out of the direct sum determined by `α`. It is stated
for `presheafRestriction` rather than for `(directSumPresheaf U S G).map`, so that the
coproducts it mentions carry the same `HasCoproduct` instance throughout and the proof can
reduce to components. -/
lemma presheafRestriction_comp_desc
    {G : PresheafOfModules.{u} ((Over.forget U).op ⋙ S)} {H : PresheafOfModules.{u} S}
    (α : G ⟶ (restrictionFunctor U S).obj H) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    presheafRestriction U S G f ≫
        (ModuleCat.restrictScalars (S.map f).hom).map (Sigma.desc (descComponent U S α Y)) =
      Sigma.desc (descComponent U S α X) ≫ H.map f := by
  apply Sigma.hom_ext; intro φ
  rw [ι_comp_presheafRestriction_assoc, ← Functor.map_comp, Sigma.ι_desc, Sigma.ι_desc_assoc]
  exact α.naturality _

/-- The map out of `directSumPresheaf G` determined by a map `G ⟶ j_U^* H`: it is given on the
summand indexed by `φ` by the component of the map at `φ`. -/
noncomputable def directSumDesc
    {G : PresheafOfModules.{u} ((Over.forget U).op ⋙ S)} {H : PresheafOfModules.{u} S}
    (α : G ⟶ (restrictionFunctor U S).obj H) : directSumPresheaf U S G ⟶ H where
  app X := Sigma.desc (descComponent U S α X)
  naturality {_ _} f := presheafRestriction_comp_desc U S α f

variable [(PresheafOfModules.pushforward.{u} (F := Over.forget U)
  (𝟙 ((Over.forget U).op ⋙ S))).IsRightAdjoint]

/-- The presheaf-level adjunction between extension by zero and restriction along
`Over.forget U`. -/
noncomputable abbrev restrictionAdjunction :=
  PresheafOfModules.pullbackPushforwardAdjunction.{u} (F := Over.forget U)
    (R := S) (S := (Over.forget U).op ⋙ S) (𝟙 ((Over.forget U).op ⋙ S))

/-- The comparison map from the direct-sum presheaf to the presheaf-level pullback, induced by
the unit of `restrictionAdjunction`. -/
noncomputable def directSumComparison (G : PresheafOfModules.{u} ((Over.forget U).op ⋙ S)) :
    directSumPresheaf U S G ⟶ (PresheafOfModules.pullback
      (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ S))).obj G :=
  directSumDesc U S ((restrictionAdjunction U S).unit.app G)

/-- The inverse comparison map, obtained from `directSumInclusion` by the universal property of
the presheaf-level pullback. -/
noncomputable def directSumComparisonInv
    (G : PresheafOfModules.{u} ((Over.forget U).op ⋙ S)) :
    (PresheafOfModules.pullback
      (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ S))).obj G ⟶ directSumPresheaf U S G :=
  ((restrictionAdjunction U S).homEquiv G (directSumPresheaf U S G)).symm
    (directSumInclusion U S G)

/-- The direct-sum presheaf is the presheaf-level pullback of `G` along `Over.forget U`. -/
noncomputable def directSumPresheafIso
    (G : PresheafOfModules.{u} ((Over.forget U).op ⋙ S)) :
    directSumPresheaf U S G ≅ (PresheafOfModules.pullback
      (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ S))).obj G where
  hom := directSumComparison U S G
  inv := directSumComparisonInv U S G
  hom_inv_id := by
    apply PresheafOfModules.hom_ext; intro X; apply Sigma.hom_ext; intro φ
    change Sigma.ι (presheafSummands U S G X) φ ≫
      Sigma.desc (descComponent U S ((restrictionAdjunction U S).unit.app G) X) ≫
        (directSumComparisonInv U S G).app X =
      Sigma.ι (presheafSummands U S G X) φ ≫ 𝟙 _
    rw [Sigma.ι_desc_assoc, Category.comp_id]
    exact congrArg (fun β => β.app (op (Over.mk φ)))
      (((restrictionAdjunction U S).homEquiv_unit G _
          (directSumComparisonInv U S G)).symm.trans
        (Equiv.apply_symm_apply _ _))
  inv_hom_id := by
    apply ((restrictionAdjunction U S).homEquiv G _).injective
    rw [(restrictionAdjunction U S).homEquiv_naturality_right]
    change ((restrictionAdjunction U S).homEquiv G (directSumPresheaf U S G))
      (((restrictionAdjunction U S).homEquiv G (directSumPresheaf U S G)).symm
        (directSumInclusion U S G)) ≫
        (restrictionFunctor U S).map (directSumComparison U S G) = _
    rw [Equiv.apply_symm_apply, (restrictionAdjunction U S).homEquiv_id]
    exact PresheafOfModules.hom_ext fun X =>
      Sigma.ι_desc (descComponent U S ((restrictionAdjunction U S).unit.app G)
        (op X.unop.left)) X.unop.hom

end Presheaf

section Sheaf

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{u}) (U : C)

/-- Restriction of presheaves of modules along `Over.forget U` has a left adjoint. This is
Mathlib's existence result, restated with the morphism of presheaves of rings spelled as the
identity of `R.over U`, which is the form the declarations below ask for. -/
instance presheafRestrictionIsRightAdjoint :
    (PresheafOfModules.pushforward.{u} (F := Over.forget U) (R := R.obj)
      (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).IsRightAdjoint :=
  PresheafOfModules.instIsRightAdjointPushforward _

/-- The family of modules indexed by the maps from `V` to `U`. -/
abbrev extensionByZeroSummands (G : SheafOfModules.{u} (R.over U)) (V : C) :
    (V ⟶ U) → ModuleCat (R.obj.obj (op V)) :=
  fun φ => G.val.obj (op (Over.mk φ))

/-- The presheaf whose sheafification is extension by zero has over `V` the direct sum of
the sections over all maps from `V` to `U`. -/
@[stacks 03DI "direct-sum formula"]
noncomputable def extensionByZeroPresheafSectionIso
    (G : SheafOfModules.{u} (R.over U)) (V : C) :
    ((PresheafOfModules.pullback.{u} (F := Over.forget U) (R := R.obj)
      (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).obj G.val).obj (op V) ≅
      (∐ extensionByZeroSummands J R U G V) := by
  let comparison : (∐ extensionByZeroSummands J R U G V) ⟶
      ((PresheafOfModules.pullback.{u} (F := Over.forget U) (R := R.obj)
        (S := (R.over U).obj) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).obj
          G.val).obj (op V) :=
    Sigma.desc fun φ =>
      (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
        (F := Over.forget U) (R := R.obj) (S := (R.over U).obj)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).unit.app G.val).app
          (op (Over.mk φ)))
  haveI : IsIso comparison := by
    change IsIso (((PresheafOfModules.evaluation R.obj (op V)).mapIso
      (directSumPresheafIso U R.obj G.val)).hom)
    infer_instance
  exact (asIso comparison).symm

/-- The direct-sum comparison is the canonical one: on the summand indexed by
`φ : V ⟶ U`, its inverse is the unit of the presheaf adjunction at `φ`. -/
@[stacks 03DI "canonical direct-sum comparison"]
theorem extensionByZeroPresheafSectionIso_inv_ι
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G : SheafOfModules.{u} (R.over U)) (V : C) (φ : V ⟶ U) :
    HEq (Limits.Sigma.ι (extensionByZeroSummands J R U G V) φ ≫
      (extensionByZeroPresheafSectionIso J R U G V).inv)
    (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (F := Over.forget U) (R := R.obj) (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).unit.app G.val).app
        (op (Over.mk φ))) :=
  heq_of_eq <| Sigma.ι_desc (f := extensionByZeroSummands J R U G V)
    (P := ((PresheafOfModules.pullback (F := Over.forget U)
      (𝟙 ((Over.forget U).op ⋙ R.obj))).obj G.val).obj (op V))
    (fun ψ => ((restrictionAdjunction U R.obj).unit.app G.val).app
      (op (Over.mk ψ))) φ

end Sheaf

end Stacks.Sites.ExtensionByZero
