module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackContinuousUnivLE

/-!
# Extension by zero for modules on a site: the direct-sum formula, at independent universes

Let `(C, J)` be a site, `R` a sheaf of rings on it and `U` an object of `C`. Restriction along
`Over.forget U` sends a sheaf of `R`-modules to a sheaf of `R_U`-modules on the localized site
`C/U`, and its left adjoint `j_{U!}` (extension by zero) is the sheafification of a pullback of
presheaves of modules whose module of sections over `V` is the direct sum of the modules
`G(φ : V ⟶ U)` indexed by all maps `φ : V ⟶ U` (Stacks 03DI).

This file constructs that presheaf of direct sums and identifies it with the presheaf-level
pullback, with the universes of the site `C : Type u₁`, of its morphisms `Category.{v₁} C`, of
the (pre)sheaf of rings `RingCat.{w}` and of the module sections `PresheafOfModules.{v}`
mutually independent.  The single-universe statements of
`StacksFrontier/CategoryTheory/Sites/Modules/ExtensionByZeroAdjunction.lean` are its
specializations.

## Main definitions

* `Stacks.Sites.ExtensionByZero.AnyUniverse.directSumPresheaf`: the presheaf of direct sums.
* `Stacks.Sites.ExtensionByZero.AnyUniverse.directSumPresheafIso`: it is the presheaf-level
  pullback along `Over.forget U`.
* `Stacks.Sites.ExtensionByZero.AnyUniverse.extensionByZeroPresheafSectionIso`: its sections
  over `V` are the direct sum of the sections over all maps `V ⟶ U`.

## Main results

* `Stacks.Sites.ExtensionByZero.AnyUniverse.extensionByZeroPresheafSectionIso_inv_ι`: the
  direct-sum comparison is the unit of the presheaf adjunction on each summand.

## Implementation notes

`UnivLE.{v₁, v}` is what makes the `V ⟶ U`-indexed coproducts of module sections exist.
Existence of the presheaf-level extension by zero is taken as the hypothesis
`(PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ S))).IsRightAdjoint` rather than
derived from smallness, which keeps the construction usable over a site whose objects lie in a
universe unrelated to that of the module sections.

## References

* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero.AnyUniverse

universe v w u₁ v₁


section Adjunction

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{w}) (U : C)

/-- The family of modules indexed by the maps from `V` to `U`. -/
abbrev extensionByZeroSummands (G : SheafOfModules.{v} (R.over U)) (V : C) :
    (V ⟶ U) → ModuleCat (R.obj.obj (op V)) :=
  fun φ => G.val.obj (op (Over.mk φ))

variable (S : Cᵒᵖ ⥤ RingCat.{w})

/-- The family of modules indexed by the maps from `X.unop` to `U`, for a presheaf of modules
over a presheaf of rings `S`. -/
abbrev presheafSummands (G : PresheafOfModules.{v} ((Over.forget U).op ⋙ S)) (X : Cᵒᵖ) :
    (X.unop ⟶ U) → ModuleCat (S.obj X) :=
  fun φ => G.obj (op (Over.mk φ))

/-- The restriction map of `G` along `f`, from the summand indexed by `φ` to the summand
indexed by `f.unop ≫ φ`.

This is `G.map` of the evident map of `C/U`, but with its source and target spelled in terms
of `S.obj X` and `S.map f`. Those agree with what `G.map` produces only after unfolding
`Over.forget` and `Functor.op`; naming the morphism performs that identification once, where
the elaborator can still see it, and keeps it out of the rewriting below. -/
noncomputable def summandRestriction (G : PresheafOfModules.{v} ((Over.forget U).op ⋙ S))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (φ : X.unop ⟶ U) :
    presheafSummands U S G X φ ⟶
      (ModuleCat.restrictScalars (S.map f).hom).obj
        (presheafSummands U S G Y (f.unop ≫ φ)) :=
  G.map (Over.homMk f.unop : Over.mk (f.unop ≫ φ) ⟶ Over.mk φ).op

variable [UnivLE.{v₁, v}]

/-- The restriction maps of `directSumPresheaf`: the summand indexed by `φ` is sent into the
summand indexed by `f ≫ φ` by the restriction map of `G`. -/
noncomputable def presheafRestriction (G : PresheafOfModules.{v} ((Over.forget U).op ⋙ S))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (∐ presheafSummands U S G X) ⟶
      (ModuleCat.restrictScalars (S.map f).hom).obj (∐ presheafSummands U S G Y) :=
  Sigma.desc fun φ =>
    summandRestriction U S G f φ ≫
      (ModuleCat.restrictScalars (S.map f).hom).map
        (Sigma.ι (presheafSummands U S G Y) (f.unop ≫ φ))

/-- `presheafRestriction` precomposed with the inclusion of the summand indexed by `φ`. -/
@[reassoc]
lemma ι_comp_presheafRestriction (G : PresheafOfModules.{v} ((Over.forget U).op ⋙ S))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (φ : X.unop ⟶ U) :
    Sigma.ι (presheafSummands U S G X) φ ≫ presheafRestriction U S G f =
      summandRestriction U S G f φ ≫
        (ModuleCat.restrictScalars (S.map f).hom).map
          (Sigma.ι (presheafSummands U S G Y) (f.unop ≫ φ)) :=
  Sigma.ι_comp_desc _ _

/-- `presheafRestriction` applied to an element of the summand indexed by `φ`. -/
@[simp]
lemma presheafRestriction_ι_apply
    (G : PresheafOfModules.{v} ((Over.forget U).op ⋙ S))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (φ : X.unop ⟶ U) (ψ : Y.unop ⟶ U)
    (h : f.unop ≫ φ = ψ) (x : G.obj (op (Over.mk φ))) :
    presheafRestriction U S G f (Sigma.ι (presheafSummands U S G X) φ x) =
      Sigma.ι (presheafSummands U S G Y) ψ
        (G.restrictₛₗ (Over.homMk f.unop h : Over.mk ψ ⟶ Over.mk φ).op x) := by
  subst ψ
  exact congrArg (fun k => k x) (ι_comp_presheafRestriction U S G f φ)

/-- The presheaf of `S`-modules whose sections over `V` are the direct sum of the sections of
`G` over all objects `φ : V ⟶ U` of `C/U`. -/
noncomputable def directSumPresheaf (G : PresheafOfModules.{v} ((Over.forget U).op ⋙ S)) :
    PresheafOfModules.{v} S where
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
lemma directSumPresheaf_obj (G : PresheafOfModules.{v} ((Over.forget U).op ⋙ S)) (X : Cᵒᵖ) :
    (directSumPresheaf U S G).obj X = ∐ presheafSummands U S G X := rfl

/-- The restriction maps of `directSumPresheaf` are `presheafRestriction`. -/
lemma directSumPresheaf_map (G : PresheafOfModules.{v} ((Over.forget U).op ⋙ S))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (directSumPresheaf U S G).map f = presheafRestriction U S G f := rfl

omit [UnivLE.{v₁, v}] in
/-- Restriction of presheaves of modules along `Over.forget U`, i.e. `j_U^*` at the level of
presheaves. -/
noncomputable abbrev restrictionFunctor :
    PresheafOfModules.{v} S ⥤ PresheafOfModules.{v} ((Over.forget U).op ⋙ S) :=
  PresheafOfModules.pushforward (F := Over.forget U)
    (𝟙 ((Over.forget U).op ⋙ S))

omit [UnivLE.{v₁, v}] in
/-- The component of a map `α : G ⟶ j_U^* H` at the object `φ : X.unop ⟶ U` of `C/U`, with
its source and target spelled as `presheafSummands U S G X φ` and `H.obj X`. As with
`summandRestriction`, naming it performs the identification of those spellings once. -/
noncomputable def descComponent {G : PresheafOfModules.{v} ((Over.forget U).op ⋙ S)}
    {H : PresheafOfModules.{v} S} (α : G ⟶ (restrictionFunctor U S).obj H) (X : Cᵒᵖ)
    (φ : X.unop ⟶ U) : presheafSummands U S G X φ ⟶ H.obj X :=
  α.app (op (Over.mk φ))

/-- The canonical map from `G` to the restriction of `directSumPresheaf G`, given over
`φ : V ⟶ U` by the inclusion of the summand indexed by `φ`. -/
noncomputable def directSumInclusion (G : PresheafOfModules.{v} ((Over.forget U).op ⋙ S)) :
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
    {G : PresheafOfModules.{v} ((Over.forget U).op ⋙ S)} {H : PresheafOfModules.{v} S}
    (α : G ⟶ (restrictionFunctor U S).obj H) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    presheafRestriction U S G f ≫
        (ModuleCat.restrictScalars (S.map f).hom).map (Sigma.desc (descComponent U S α Y)) =
      Sigma.desc (descComponent U S α X) ≫ H.map f := by
  refine Sigma.hom_ext _ _ fun φ => ?_
  rw [ι_comp_presheafRestriction_assoc, ← Functor.map_comp, Sigma.ι_comp_desc,
    Sigma.ι_comp_desc_assoc]
  exact α.naturality _

/-- The map out of `directSumPresheaf G` determined by a map `G ⟶ j_U^* H`: it is given on the
summand indexed by `φ` by the component of the map at `φ`. -/
noncomputable def directSumDesc
    {G : PresheafOfModules.{v} ((Over.forget U).op ⋙ S)} {H : PresheafOfModules.{v} S}
    (α : G ⟶ (restrictionFunctor U S).obj H) : directSumPresheaf U S G ⟶ H where
  app X := Sigma.desc (descComponent U S α X)
  naturality {_ _} f := presheafRestriction_comp_desc U S α f

variable [(PresheafOfModules.pushforward.{v} (F := Over.forget U)
  (𝟙 ((Over.forget U).op ⋙ S))).IsRightAdjoint]

/- The same hypothesis for the sheaf of rings `R` rather than the presheaf `S`: the declarations
below that read the direct-sum formula off the adjunction use `R.obj` as the base, and the two
spellings are different morphisms. Both are strictly weaker than the `UnivLE` hypotheses that
would derive them. -/
variable [(PresheafOfModules.pushforward.{v} (F := Over.forget U)
  (𝟙 ((Over.forget U).op ⋙ R.obj))).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{v} (F := Over.forget U) (R := R.obj)
  (S := (R.over U).obj)
  (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).IsRightAdjoint]

/-- The presheaf-level adjunction between extension by zero and restriction along
`Over.forget U`. -/
noncomputable abbrev restrictionAdjunction :=
  PresheafOfModules.pullbackPushforwardAdjunction.{v} (F := Over.forget U)
    (R := S) (S := (Over.forget U).op ⋙ S) (𝟙 ((Over.forget U).op ⋙ S))

/-- The comparison map from the direct-sum presheaf to the presheaf-level pullback, induced by
the unit of `restrictionAdjunction`. -/
noncomputable def directSumComparison (G : PresheafOfModules.{v} ((Over.forget U).op ⋙ S)) :
    directSumPresheaf U S G ⟶ (PresheafOfModules.pullback
      (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ S))).obj G :=
  directSumDesc U S ((restrictionAdjunction U S).unit.app G)

/-- The inverse comparison map, obtained from `directSumInclusion` by the universal property of
the presheaf-level pullback. -/
noncomputable def directSumComparisonInv
    (G : PresheafOfModules.{v} ((Over.forget U).op ⋙ S)) :
    (PresheafOfModules.pullback
      (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ S))).obj G ⟶ directSumPresheaf U S G :=
  ((restrictionAdjunction U S).homEquiv G (directSumPresheaf U S G)).symm
    (directSumInclusion U S G)

/-- The direct-sum presheaf is the presheaf-level pullback of `G` along `Over.forget U`. -/
noncomputable def directSumPresheafIso
    (G : PresheafOfModules.{v} ((Over.forget U).op ⋙ S)) :
    directSumPresheaf U S G ≅ (PresheafOfModules.pullback
      (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ S))).obj G where
  hom := directSumComparison U S G
  inv := directSumComparisonInv U S G
  hom_inv_id := by
    refine PresheafOfModules.hom_ext fun X => Sigma.hom_ext _ _ fun φ => ?_
    change Sigma.ι (presheafSummands U S G X) φ ≫
      Sigma.desc (descComponent U S ((restrictionAdjunction U S).unit.app G) X) ≫
        (directSumComparisonInv U S G).app X =
      Sigma.ι (presheafSummands U S G X) φ ≫ 𝟙 _
    rw [Sigma.ι_comp_desc_assoc, Category.comp_id]
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
    refine PresheafOfModules.hom_ext fun X => ?_
    change Sigma.ι (presheafSummands U S G (op X.unop.left)) X.unop.hom ≫
      Sigma.desc (descComponent U S ((restrictionAdjunction U S).unit.app G)
        (op X.unop.left)) = ((restrictionAdjunction U S).unit.app G).app X
    exact Sigma.ι_comp_desc (descComponent U S ((restrictionAdjunction U S).unit.app G)
      (op X.unop.left)) X.unop.hom

/-- The presheaf whose sheafification is extension by zero has over `V` the direct sum of
the sections over all maps from `V` to `U`. -/
noncomputable def extensionByZeroPresheafSectionIso
    (G : SheafOfModules.{v} (R.over U)) (V : C) :
    ((PresheafOfModules.pullback.{v} (F := Over.forget U) (R := R.obj)
      (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).obj G.val).obj (op V) ≅
      (∐ extensionByZeroSummands J R U G V) := by
  let comparison : (∐ extensionByZeroSummands J R U G V) ⟶
      ((PresheafOfModules.pullback.{v} (F := Over.forget U) (R := R.obj)
        (S := (R.over U).obj) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).obj
          G.val).obj (op V) :=
    Sigma.desc fun φ =>
      (((PresheafOfModules.pullbackPushforwardAdjunction.{v}
        (F := Over.forget U) (R := R.obj) (S := (R.over U).obj)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).unit.app G.val).app
          (op (Over.mk φ)))
  have : IsIso comparison := by
    change IsIso (((PresheafOfModules.evaluation R.obj (op V)).mapIso
      (directSumPresheafIso U R.obj G.val)).hom)
    infer_instance
  exact (asIso comparison).symm

/-- The direct-sum comparison is the canonical one: on the summand indexed by
`φ : V ⟶ U`, its inverse is the unit of the presheaf adjunction at `φ`. -/
theorem extensionByZeroPresheafSectionIso_inv_ι
    [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    (G : SheafOfModules.{v} (R.over U)) (V : C) (φ : V ⟶ U) :
    HEq (Limits.Sigma.ι (extensionByZeroSummands J R U G V) φ ≫
      (extensionByZeroPresheafSectionIso J R U G V).inv)
    (((PresheafOfModules.pullbackPushforwardAdjunction.{v}
      (F := Over.forget U) (R := R.obj) (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).unit.app G.val).app
        (op (Over.mk φ))) := by
  apply heq_of_eq
  change Sigma.ι (extensionByZeroSummands J R U G V) φ ≫
    (directSumComparison U R.obj G.val).app (op V) = _
  exact Sigma.ι_comp_desc (f := extensionByZeroSummands J R U G V)
    (P := ((PresheafOfModules.pullback (F := Over.forget U)
      (𝟙 ((Over.forget U).op ⋙ R.obj))).obj G.val).obj (op V))
    (fun ψ => ((restrictionAdjunction U R.obj).unit.app G.val).app
      (op (Over.mk ψ))) φ

end Adjunction

end Stacks.Sites.ExtensionByZero.AnyUniverse

end
