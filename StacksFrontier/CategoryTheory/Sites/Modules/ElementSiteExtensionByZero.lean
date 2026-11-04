module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionPreservesInjectivesEssentiallySmall
import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of modules to the site of elements of a presheaf preserves injectives

Let `(C, J)` be a site, `R` a sheaf of rings on it and `K` a presheaf of sets on `C`. The *site
of elements* of `K` has as objects the pairs `(X, t)` with `t` a section of `K` over `X`; it is
written here as the opposite `(K.Elements)ᵒᵖ` of Mathlib's category of elements, whose
projection to `C` is `Stacks.Sites.ExtensionByZero.OverElements.proj`. Its topology is any
topology for which the projection is continuous. Restriction of sheaves of modules along the
projection is `j_K^{-1}`, and its left adjoint is extension by zero `j_{K!}`. The objects of `C`
live in an arbitrary universe `c`, while the morphisms, the sheaf of rings and the modules live
in `u`.

The sections over `X` of the presheaf whose sheafification is `j_{K!} G` are the direct sum of
the `G(X, t)` over all `t ∈ K(X)`. So a monomorphism of sheaves of modules on the site of
elements induces a coproduct of monomorphisms of modules, which is again a monomorphism by
Grothendieck's axiom AB4 for `ModuleCat`. Hence `j_{K!}` preserves monomorphisms and its right
adjoint preserves injective objects.

## Main results

* `Stacks.Sites.ExtensionByZero.OverElements.preservesInjectiveObjects_pushforward_proj`:
  restriction of sheaves of modules along the projection of the site of elements preserves
  injective objects.
* `Stacks.Sites.ExtensionByZero.OverElements.injective_pushforward_proj_obj`: the same statement
  for one injective module.
* `Stacks.Sites.ExtensionByZero.OverElements.extensionByZero_preservesMonomorphisms`: extension
  by zero preserves monomorphisms.
* `Stacks.Sites.ExtensionByZero.OverElements.directSumPresheafIso` and
  `Stacks.Sites.ExtensionByZero.OverElements.extensionByZeroPresheafSectionIso`: the direct-sum
  formula for the presheaf computing `j_{K!}`.

## References

* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero.OverElements

universe u c

variable {C : Type c} [Category.{u} C] (K : Cᵒᵖ ⥤ Type u)

/-- The projection of the site of elements of `K` to `C`: the pair `(X, t)` goes to `X`. -/
abbrev proj : (K.Elements)ᵒᵖ ⥤ C := (CategoryOfElements.π K).leftOp

/-- The object of the site of elements of `K` given by a section `t` of `K` over `X`. -/
abbrev elt (X : Cᵒᵖ) (t : K.obj X) : (K.Elements)ᵒᵖ := op ⟨X, t⟩

/-- The morphism of the site of elements of `K` over `f : X ⟶ Y` in `Cᵒᵖ`, from the object of
the restricted section `K.map f t` to the object of `t`. -/
def eltHom {X Y : Cᵒᵖ} (f : X ⟶ Y) (t : K.obj X) : elt K Y (K.map f t) ⟶ elt K X t :=
  Quiver.Hom.op (CategoryOfElements.homMk (⟨X, t⟩ : K.Elements) ⟨Y, K.map f t⟩ f rfl)

variable (S : Cᵒᵖ ⥤ RingCat.{u})

/-- The family of modules indexed by the sections of `K` over `X`: the sections of `G` at the
objects `(X, t)` of the site of elements. -/
abbrev presheafSummands (G : PresheafOfModules.{u} ((proj K).op ⋙ S)) (X : Cᵒᵖ) :
    K.obj X → ModuleCat (S.obj X) :=
  fun t => G.obj (op (elt K X t))

/-- The restriction map of `G` along `f`, from the summand indexed by `t` to the summand indexed
by `K.map f t`, with its source and target spelled in terms of `S.obj X` and `S.map f`. -/
noncomputable def summandRestriction (G : PresheafOfModules.{u} ((proj K).op ⋙ S))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (t : K.obj X) :
    presheafSummands K S G X t ⟶
      (ModuleCat.restrictScalars (S.map f).hom).obj
        (presheafSummands K S G Y (K.map f t)) :=
  G.map (eltHom K f t).op

/-- The restriction maps of `directSumPresheaf`: the summand indexed by `t` is sent into the
summand indexed by `K.map f t` by the restriction map of `G`. -/
noncomputable def presheafRestriction (G : PresheafOfModules.{u} ((proj K).op ⋙ S))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (∐ presheafSummands K S G X) ⟶
      (ModuleCat.restrictScalars (S.map f).hom).obj (∐ presheafSummands K S G Y) :=
  Sigma.desc fun t =>
    summandRestriction K S G f t ≫
      (ModuleCat.restrictScalars (S.map f).hom).map
        (Sigma.ι (presheafSummands K S G Y) (K.map f t))

/-- `presheafRestriction` precomposed with the inclusion of the summand indexed by `t`. -/
@[reassoc]
lemma ι_comp_presheafRestriction (G : PresheafOfModules.{u} ((proj K).op ⋙ S))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (t : K.obj X) :
    Sigma.ι (presheafSummands K S G X) t ≫ presheafRestriction K S G f =
      summandRestriction K S G f t ≫
        (ModuleCat.restrictScalars (S.map f).hom).map
          (Sigma.ι (presheafSummands K S G Y) (K.map f t)) :=
  Sigma.ι_desc _ _

/-- `presheafRestriction` applied to an element of the summand indexed by `t`. -/
@[simp]
lemma presheafRestriction_ι_apply (G : PresheafOfModules.{u} ((proj K).op ⋙ S))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (t : K.obj X) (s : K.obj Y)
    (h : K.map f t = s) (x : G.obj (op (elt K X t))) :
    presheafRestriction K S G f (Sigma.ι (presheafSummands K S G X) t x) =
      Sigma.ι (presheafSummands K S G Y) s
        (G.restrictₛₗ (Quiver.Hom.op (CategoryOfElements.homMk (⟨X, t⟩ : K.Elements)
          ⟨Y, s⟩ f h)).op x) := by
  subst h
  exact congrArg (fun k => k x) (ι_comp_presheafRestriction K S G f t)

/-- The presheaf of `S`-modules whose sections over `X` are the direct sum of the sections of
`G` over all objects `(X, t)` of the site of elements of `K`. -/
noncomputable def directSumPresheaf (G : PresheafOfModules.{u} ((proj K).op ⋙ S)) :
    PresheafOfModules.{u} S where
  obj X := ∐ presheafSummands K S G X
  map f := presheafRestriction K S G f
  map_id X := by
    apply Sigma.hom_ext; intro t; ext x
    change presheafRestriction K S G (𝟙 X) (Sigma.ι (presheafSummands K S G X) t x) =
      Sigma.ι (presheafSummands K S G X) t x
    rw [presheafRestriction_ι_apply K S G (𝟙 X) t t (by simp)]
    change Sigma.ι (presheafSummands K S G X) t (G.map (𝟙 _) x) = _
    rw [G.map_id]
    rfl
  map_comp {X Y Z} f g := by
    apply Sigma.hom_ext; intro t; ext x
    change presheafRestriction K S G (f ≫ g)
        (Sigma.ι (presheafSummands K S G X) t x) =
      presheafRestriction K S G g
        (presheafRestriction K S G f (Sigma.ι (presheafSummands K S G X) t x))
    rw [presheafRestriction_ι_apply K S G (f ≫ g) t (K.map g (K.map f t)) (by simp),
      presheafRestriction_ι_apply K S G f t (K.map f t) rfl,
      presheafRestriction_ι_apply K S G g (K.map f t) (K.map g (K.map f t)) rfl]
    change @Eq (↑(∐ presheafSummands K S G Z)) _ _
    exact congrArg
      (fun y : G.obj (op (elt K Z (K.map g (K.map f t)))) =>
        Sigma.ι (presheafSummands K S G Z) (K.map g (K.map f t)) y)
      (G.map_comp_apply (eltHom K f t).op (eltHom K g (K.map f t)).op x)

/-- Restriction of presheaves of modules along the projection of the site of elements, i.e.
`j_K^*` at the level of presheaves. -/
noncomputable abbrev restrictionFunctor :
    PresheafOfModules.{u} S ⥤ PresheafOfModules.{u} ((proj K).op ⋙ S) :=
  PresheafOfModules.pushforward (F := proj K) (𝟙 ((proj K).op ⋙ S))

/-- The component of a map `α : G ⟶ j_K^* H` at the object `(X, t)` of the site of elements,
with its source and target spelled as `presheafSummands K S G X t` and `H.obj X`. -/
noncomputable def descComponent {G : PresheafOfModules.{u} ((proj K).op ⋙ S)}
    {H : PresheafOfModules.{u} S} (α : G ⟶ (restrictionFunctor K S).obj H) (X : Cᵒᵖ)
    (t : K.obj X) : presheafSummands K S G X t ⟶ H.obj X :=
  α.app (op (elt K X t))

/-- The canonical map from `G` to the restriction of `directSumPresheaf G`, given at the object
`(X, t)` by the inclusion of the summand indexed by `t`. -/
noncomputable def directSumInclusion (G : PresheafOfModules.{u} ((proj K).op ⋙ S)) :
    G ⟶ (restrictionFunctor K S).obj (directSumPresheaf K S G) where
  app := fun ⟨⟨X, t⟩⟩ => Sigma.ι (presheafSummands K S G X) t
  naturality := by
    rintro ⟨⟨X, t⟩⟩ ⟨⟨Y, s⟩⟩ ⟨g, hg⟩
    ext x
    change Sigma.ι (presheafSummands K S G Y) s (G.restrictₛₗ _ x) =
      presheafRestriction K S G g (Sigma.ι (presheafSummands K S G X) t x)
    rw [presheafRestriction_ι_apply K S G g t s hg]
    rfl

/-- The naturality square for the map out of the direct sum determined by `α`. -/
lemma presheafRestriction_comp_desc
    {G : PresheafOfModules.{u} ((proj K).op ⋙ S)} {H : PresheafOfModules.{u} S}
    (α : G ⟶ (restrictionFunctor K S).obj H) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    presheafRestriction K S G f ≫
        (ModuleCat.restrictScalars (S.map f).hom).map (Sigma.desc (descComponent K S α Y)) =
      Sigma.desc (descComponent K S α X) ≫ H.map f := by
  apply Sigma.hom_ext; intro t
  rw [ι_comp_presheafRestriction_assoc, ← Functor.map_comp, Sigma.ι_desc, Sigma.ι_desc_assoc]
  exact α.naturality _

/-- The map out of `directSumPresheaf G` determined by a map `G ⟶ j_K^* H`. -/
noncomputable def directSumDesc
    {G : PresheafOfModules.{u} ((proj K).op ⋙ S)} {H : PresheafOfModules.{u} S}
    (α : G ⟶ (restrictionFunctor K S).obj H) : directSumPresheaf K S G ⟶ H where
  app X := Sigma.desc (descComponent K S α X)
  naturality {_ _} f := presheafRestriction_comp_desc K S α f

variable [EssentiallySmall.{u} (K.Elements)ᵒᵖ]

/-- Restriction of presheaves of modules along the projection of the site of elements has a left
adjoint. -/
instance presheafRestrictionIsRightAdjoint :
    (PresheafOfModules.pushforward.{u} (F := proj K)
      (𝟙 ((proj K).op ⋙ S))).IsRightAdjoint :=
  PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall.{u} _

/-- The presheaf-level adjunction between extension by zero and restriction along the
projection of the site of elements. -/
noncomputable abbrev restrictionAdjunction :=
  PresheafOfModules.pullbackPushforwardAdjunction.{u} (F := proj K)
    (R := S) (S := (proj K).op ⋙ S) (𝟙 ((proj K).op ⋙ S))

/-- The comparison map from the direct-sum presheaf to the presheaf-level pullback, induced by
the unit of `restrictionAdjunction`. -/
noncomputable def directSumComparison (G : PresheafOfModules.{u} ((proj K).op ⋙ S)) :
    directSumPresheaf K S G ⟶ (PresheafOfModules.pullback
      (F := proj K) (𝟙 ((proj K).op ⋙ S))).obj G :=
  directSumDesc K S ((restrictionAdjunction K S).unit.app G)

/-- The inverse comparison map, obtained from `directSumInclusion` by the universal property of
the presheaf-level pullback. -/
noncomputable def directSumComparisonInv (G : PresheafOfModules.{u} ((proj K).op ⋙ S)) :
    (PresheafOfModules.pullback
      (F := proj K) (𝟙 ((proj K).op ⋙ S))).obj G ⟶ directSumPresheaf K S G :=
  ((restrictionAdjunction K S).homEquiv G (directSumPresheaf K S G)).symm
    (directSumInclusion K S G)

/-- The direct-sum presheaf is the presheaf-level pullback of `G` along the projection. -/
noncomputable def directSumPresheafIso (G : PresheafOfModules.{u} ((proj K).op ⋙ S)) :
    directSumPresheaf K S G ≅ (PresheafOfModules.pullback
      (F := proj K) (𝟙 ((proj K).op ⋙ S))).obj G where
  hom := directSumComparison K S G
  inv := directSumComparisonInv K S G
  hom_inv_id := by
    apply PresheafOfModules.hom_ext; intro X; apply Sigma.hom_ext; intro t
    change Sigma.ι (presheafSummands K S G X) t ≫
      Sigma.desc (descComponent K S ((restrictionAdjunction K S).unit.app G) X) ≫
        (directSumComparisonInv K S G).app X =
      Sigma.ι (presheafSummands K S G X) t ≫ 𝟙 _
    rw [Sigma.ι_desc_assoc, Category.comp_id]
    exact congrArg (fun β => β.app (op (elt K X t)))
      (((restrictionAdjunction K S).homEquiv_unit G _
          (directSumComparisonInv K S G)).symm.trans
        (Equiv.apply_symm_apply _ _))
  inv_hom_id := by
    apply ((restrictionAdjunction K S).homEquiv G _).injective
    rw [(restrictionAdjunction K S).homEquiv_naturality_right]
    change ((restrictionAdjunction K S).homEquiv G (directSumPresheaf K S G))
      (((restrictionAdjunction K S).homEquiv G (directSumPresheaf K S G)).symm
        (directSumInclusion K S G)) ≫
        (restrictionFunctor K S).map (directSumComparison K S G) = _
    rw [Equiv.apply_symm_apply, (restrictionAdjunction K S).homEquiv_id]
    apply PresheafOfModules.hom_ext
    rintro ⟨⟨X, t⟩⟩
    change Sigma.ι (presheafSummands K S G X) t ≫
      Sigma.desc (descComponent K S ((restrictionAdjunction K S).unit.app G) X) =
      ((restrictionAdjunction K S).unit.app G).app (op (elt K X t))
    exact Sigma.ι_desc (descComponent K S ((restrictionAdjunction K S).unit.app G) X) t

section Sheaves

variable (J : GrothendieckTopology C) (JD : GrothendieckTopology (K.Elements)ᵒᵖ)
  (R : Sheaf J RingCat.{u}) [(proj K).IsContinuous JD J]

/-- The structure sheaf of the site of elements: the restriction of `R` along the projection. -/
abbrev restrictedRingSheaf : Sheaf JD RingCat.{u} :=
  ((proj K).sheafPushforwardContinuous RingCat.{u} JD J).obj R

/-- Restriction of presheaves of modules along the projection of the site of elements, along the
identity of the underlying presheaf of `restrictedRingSheaf K J JD R`, has a left adjoint. -/
instance presheafRestrictionSheafIsRightAdjoint :
    (PresheafOfModules.pushforward.{u} (F := proj K) (R := R.obj)
      (S := (restrictedRingSheaf K J JD R).obj)
      (𝟙 (restrictedRingSheaf K J JD R) :
        (restrictedRingSheaf K J JD R) ⟶
          (restrictedRingSheaf K J JD R)).hom).IsRightAdjoint :=
  presheafRestrictionIsRightAdjoint K R.obj

/-- The family of modules indexed by the sections of `K` over `V`, for a sheaf of modules on the
site of elements. -/
abbrev extensionByZeroSummands (G : SheafOfModules.{u} (restrictedRingSheaf K J JD R))
    (V : C) : K.obj (op V) → ModuleCat (R.obj.obj (op V)) :=
  fun t => G.val.obj (op (elt K (op V) t))

/-- The presheaf whose sheafification is extension by zero has over `V` the direct sum of the
sections of `G` at the objects `(V, t)` of the site of elements, over all sections `t` of `K`
over `V`. -/
@[stacks 03DI "for the site of elements of a presheaf of sets"]
noncomputable def extensionByZeroPresheafSectionIso
    (G : SheafOfModules.{u} (restrictedRingSheaf K J JD R)) (V : C) :
    ((PresheafOfModules.pullback.{u} (F := proj K) (R := R.obj)
      (S := (restrictedRingSheaf K J JD R).obj)
      (𝟙 (restrictedRingSheaf K J JD R) :
        (restrictedRingSheaf K J JD R) ⟶ (restrictedRingSheaf K J JD R)).hom).obj
          G.val).obj (op V) ≅
      (∐ extensionByZeroSummands K J JD R G V) := by
  let comparison : (∐ extensionByZeroSummands K J JD R G V) ⟶
      ((PresheafOfModules.pullback.{u} (F := proj K) (R := R.obj)
        (S := (restrictedRingSheaf K J JD R).obj)
        (𝟙 (restrictedRingSheaf K J JD R) :
          (restrictedRingSheaf K J JD R) ⟶ (restrictedRingSheaf K J JD R)).hom).obj
            G.val).obj (op V) :=
    Sigma.desc fun t =>
      (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
        (F := proj K) (R := R.obj) (S := (restrictedRingSheaf K J JD R).obj)
        (𝟙 (restrictedRingSheaf K J JD R) :
          (restrictedRingSheaf K J JD R) ⟶ (restrictedRingSheaf K J JD R)).hom).unit.app
            G.val).app (op (elt K (op V) t)))
  have : IsIso comparison := by
    change IsIso (((PresheafOfModules.evaluation R.obj (op V)).mapIso
      (directSumPresheafIso K R.obj G.val)).hom)
    infer_instance
  exact (asIso comparison).symm

/-- The direct-sum comparison is the canonical one: on the summand indexed by the section `t`,
its inverse is the unit of the presheaf adjunction at `(V, t)`. -/
theorem extensionByZeroPresheafSectionIso_inv_ι
    (G : SheafOfModules.{u} (restrictedRingSheaf K J JD R)) (V : C) (t : K.obj (op V)) :
    HEq (Limits.Sigma.ι (extensionByZeroSummands K J JD R G V) t ≫
      (extensionByZeroPresheafSectionIso K J JD R G V).inv)
    (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (F := proj K) (R := R.obj) (S := (restrictedRingSheaf K J JD R).obj)
      (𝟙 (restrictedRingSheaf K J JD R) :
        (restrictedRingSheaf K J JD R) ⟶ (restrictedRingSheaf K J JD R)).hom).unit.app
          G.val).app (op (elt K (op V) t))) := by
  apply heq_of_eq
  show Sigma.ι (extensionByZeroSummands K J JD R G V) t ≫
    (directSumComparison K R.obj G.val).app (op V) = _
  exact Sigma.ι_desc (f := extensionByZeroSummands K J JD R G V)
    (P := ((PresheafOfModules.pullback (F := proj K)
      (𝟙 ((proj K).op ⋙ R.obj))).obj G.val).obj (op V))
    (fun s => ((restrictionAdjunction K R.obj).unit.app G.val).app
      (op (elt K (op V) s))) t

variable [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction of sheaves of modules along the projection of the site of elements has a left
adjoint, namely extension by zero. -/
instance sheafRestrictionIsRightAdjoint :
    (SheafOfModules.pushforward.{u} (F := proj K)
      (𝟙 (restrictedRingSheaf K J JD R) :
        (restrictedRingSheaf K J JD R) ⟶ (restrictedRingSheaf K J JD R))).IsRightAdjoint :=
  have := presheafRestrictionIsRightAdjoint K R.obj
  (SheafOfModules.PullbackConstruction.adjunction.{u}
    (F := proj K) (𝟙 (restrictedRingSheaf K J JD R) :
      (restrictedRingSheaf K J JD R) ⟶ (restrictedRingSheaf K J JD R))).isRightAdjoint

/-- The map of direct sums induced on the sections over `V` of the extension-by-zero presheaf by
a map `f : G ⟶ H` of sheaves of modules on the site of elements: on the summand indexed by the
section `t` it is the component of `f` at `(V, t)`. -/
noncomputable def extensionByZeroSummandsMap
    {G H : SheafOfModules.{u} (restrictedRingSheaf K J JD R)} (f : G ⟶ H) (V : C) :
    (∐ extensionByZeroSummands K J JD R G V) ⟶ (∐ extensionByZeroSummands K J JD R H V) :=
  Limits.Sigma.map
    (f := extensionByZeroSummands K J JD R G V)
    (g := extensionByZeroSummands K J JD R H V)
    (fun t => (f.val.app (op (elt K (op V) t)) :
      extensionByZeroSummands K J JD R G V t ⟶ extensionByZeroSummands K J JD R H V t))

omit [EssentiallySmall.{u} (K.Elements)ᵒᵖ] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `extensionByZeroSummandsMap` is a monomorphism as soon as `f` is. -/
lemma extensionByZeroSummandsMap_mono
    {G H : SheafOfModules.{u} (restrictedRingSheaf K J JD R)} (f : G ⟶ H) (V : C) [Mono f] :
    Mono (extensionByZeroSummandsMap K J JD R f V) := by
  have hval : Mono f.val := by
    show Mono ((SheafOfModules.forget (restrictedRingSheaf K J JD R)).map f)
    infer_instance
  refine Stacks.Sites.ExtensionByZero.mono_sigmaMap _ fun t => ?_
  exact (ModuleCat.mono_iff_injective _).2
    (PresheafOfModules.injective_of_mono f.val (op (elt K (op V) t)))

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The direct-sum formula is natural in the sheaf of modules: the map induced by `f : G ⟶ H` on
the sections of the extension-by-zero presheaf over `V` is `extensionByZeroSummandsMap`. -/
lemma extensionByZeroSectionMap_naturality
    {G H : SheafOfModules.{u} (restrictedRingSheaf K J JD R)} (f : G ⟶ H) (V : C) :
    ((PresheafOfModules.pullback.{u} (F := proj K)
        (R := R.obj) (S := (restrictedRingSheaf K J JD R).obj)
        (𝟙 (restrictedRingSheaf K J JD R) :
          (restrictedRingSheaf K J JD R) ⟶ (restrictedRingSheaf K J JD R)).hom).map
          f.val).app (op V) ≫
      (extensionByZeroPresheafSectionIso K J JD R H V).hom =
      (extensionByZeroPresheafSectionIso K J JD R G V).hom ≫
      extensionByZeroSummandsMap K J JD R f V := by
  let eG := extensionByZeroPresheafSectionIso K J JD R G V
  let eH := extensionByZeroPresheafSectionIso K J JD R H V
  let P : PresheafOfModules (restrictedRingSheaf K J JD R).obj ⥤ PresheafOfModules R.obj :=
    PresheafOfModules.pullback.{u} (F := proj K)
      (R := R.obj) (S := (restrictedRingSheaf K J JD R).obj)
      (𝟙 (restrictedRingSheaf K J JD R) :
        (restrictedRingSheaf K J JD R) ⟶ (restrictedRingSheaf K J JD R)).hom
  let adj : P ⊣ PresheafOfModules.pushforward.{u} (F := proj K)
      (R := R.obj) (S := (restrictedRingSheaf K J JD R).obj)
      (𝟙 (restrictedRingSheaf K J JD R) :
        (restrictedRingSheaf K J JD R) ⟶ (restrictedRingSheaf K J JD R)).hom :=
    PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (F := proj K) (R := R.obj) (S := (restrictedRingSheaf K J JD R).obj)
      (𝟙 (restrictedRingSheaf K J JD R) :
        (restrictedRingSheaf K J JD R) ⟶ (restrictedRingSheaf K J JD R)).hom
  apply (Iso.inv_comp_eq eG).1
  apply Sigma.hom_ext
  intro t
  have hG' := eq_of_heq (extensionByZeroPresheafSectionIso_inv_ι K J JD R G V t)
  have hH' := eq_of_heq (extensionByZeroPresheafSectionIso_inv_ι K J JD R H V t)
  have hnat' :
      ((adj.unit.app G.val).app (op (elt K (op V) t))) ≫ (P.map f.val).app (op V) =
        f.val.app (op (elt K (op V) t)) ≫ ((adj.unit.app H.val).app (op (elt K (op V) t))) :=
    (congrArg (fun g => g.app (op (elt K (op V) t))) (adj.unit.naturality f.val)).symm
  have hUnit : ((adj.unit.app H.val).app (op (elt K (op V) t))) ≫ eH.hom =
      Sigma.ι (extensionByZeroSummands K J JD R H V) t :=
    ((Iso.comp_inv_eq eH).1 hH').symm
  have hι : (f.val.app (op (elt K (op V) t)) :
        extensionByZeroSummands K J JD R G V t ⟶ extensionByZeroSummands K J JD R H V t) ≫
      Sigma.ι (extensionByZeroSummands K J JD R H V) t =
      Sigma.ι (extensionByZeroSummands K J JD R G V) t ≫
        extensionByZeroSummandsMap K J JD R f V :=
    (Limits.Sigma.ι_map (f := extensionByZeroSummands K J JD R G V)
      (g := extensionByZeroSummands K J JD R H V)
      (fun s => (f.val.app (op (elt K (op V) s)) :
        extensionByZeroSummands K J JD R G V s ⟶
          extensionByZeroSummands K J JD R H V s)) t).symm
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun x => x ≫ ((P.map f.val).app (op V) ≫ eH.hom)) hG').trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun x => x ≫ eH.hom) hnat').trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun x => f.val.app (op (elt K (op V) t)) ≫ x) hUnit).trans hι)))))

variable [EssentiallySmall.{u} C]

/-- Extension by zero along the projection of the site of elements preserves monomorphisms. -/
@[stacks 03DJ "for the site of elements of a presheaf of sets, monomorphisms"]
lemma extensionByZero_preservesMonomorphisms :
    Functor.PreservesMonomorphisms (SheafOfModules.pullback.{u}
      (F := proj K) (𝟙 (restrictedRingSheaf K J JD R) :
        (restrictedRingSheaf K J JD R) ⟶ (restrictedRingSheaf K J JD R))) := by
  have := presheafRestrictionIsRightAdjoint K R.obj
  have : HasSheafify J AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{u} J AddCommGrpCat.{u}
  constructor
  intro G H f hf
  have hP : Mono ((PresheafOfModules.pullback.{u} (F := proj K)
      (R := R.obj) (S := (restrictedRingSheaf K J JD R).obj)
      (𝟙 (restrictedRingSheaf K J JD R) :
        (restrictedRingSheaf K J JD R) ⟶ (restrictedRingSheaf K J JD R)).hom).map f.val) := by
    apply PresheafOfModules.mono_of_injective
    intro X
    let V := unop X
    rw [← ModuleCat.mono_iff_injective]
    have hcomp :
        ((PresheafOfModules.pullback.{u} (F := proj K)
          (R := R.obj) (S := (restrictedRingSheaf K J JD R).obj)
          (𝟙 (restrictedRingSheaf K J JD R) :
            (restrictedRingSheaf K J JD R) ⟶
              (restrictedRingSheaf K J JD R)).hom).map f.val).app (op V) =
        ((extensionByZeroPresheafSectionIso K J JD R G V).hom ≫
          extensionByZeroSummandsMap K J JD R f V) ≫
            (extensionByZeroPresheafSectionIso K J JD R H V).inv :=
      (Iso.eq_comp_inv _).2 (extensionByZeroSectionMap_naturality K J JD R f V)
    have : Mono f := hf
    have := extensionByZeroSummandsMap_mono K J JD R f V
    rw [hcomp]
    infer_instance
  let e := SheafOfModules.pullbackIso (𝟙 (restrictedRingSheaf K J JD R))
  have hcomp : Mono ((SheafOfModules.forget (restrictedRingSheaf K J JD R) ⋙
      PresheafOfModules.pullback.{u} (F := proj K)
        (R := R.obj) (S := (restrictedRingSheaf K J JD R).obj)
        (𝟙 (restrictedRingSheaf K J JD R) :
          (restrictedRingSheaf K J JD R) ⟶ (restrictedRingSheaf K J JD R)).hom ⋙
      PresheafOfModules.sheafification (𝟙 R.obj)).map f) := by
    show Mono ((PresheafOfModules.sheafification (𝟙 R.obj)).map
      ((PresheafOfModules.pullback.{u} (F := proj K)
        (R := R.obj) (S := (restrictedRingSheaf K J JD R).obj)
        (𝟙 (restrictedRingSheaf K J JD R) :
          (restrictedRingSheaf K J JD R) ⟶ (restrictedRingSheaf K J JD R)).hom).map f.val))
    infer_instance
  have hmap : (SheafOfModules.pullback.{u} (F := proj K)
      (𝟙 (restrictedRingSheaf K J JD R) :
        (restrictedRingSheaf K J JD R) ⟶ (restrictedRingSheaf K J JD R))).map f =
      (e.app G).hom ≫ ((SheafOfModules.forget (restrictedRingSheaf K J JD R) ⋙
        PresheafOfModules.pullback.{u} (F := proj K)
          (R := R.obj) (S := (restrictedRingSheaf K J JD R).obj)
          (𝟙 (restrictedRingSheaf K J JD R) :
            (restrictedRingSheaf K J JD R) ⟶ (restrictedRingSheaf K J JD R)).hom ⋙
        PresheafOfModules.sheafification (𝟙 R.obj)).map f) ≫ (e.app H).inv := by
    apply (cancel_mono (e.app H).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact e.hom.naturality f
  rw [hmap]
  infer_instance

/-- Restriction of sheaves of modules along the projection of the site of elements preserves
injective objects. -/
@[stacks 03F3 "part (1), for the site of elements of a presheaf of sets",
  sga "4 V 4.11" "1) injective case", sga "4 V 2.3.2" "more general"]
theorem preservesInjectiveObjects_pushforward_proj :
    (SheafOfModules.pushforward.{u} (F := proj K)
      (𝟙 (restrictedRingSheaf K J JD R) :
        (restrictedRingSheaf K J JD R) ⟶
          (restrictedRingSheaf K J JD R))).PreservesInjectiveObjects :=
  have := extensionByZero_preservesMonomorphisms K J JD R
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (SheafOfModules.pullbackPushforwardAdjunction
      (F := proj K) (𝟙 (restrictedRingSheaf K J JD R) :
        (restrictedRingSheaf K J JD R) ⟶ (restrictedRingSheaf K J JD R)))

/-- The restriction of an injective sheaf of `R`-modules to the site of elements of `K` is
injective. -/
@[stacks 03F3 "part (1), for one module, at the site of elements of a presheaf of sets",
  sga "4 V 4.11" "1) injective case", sga "4 V 2.3.2" "more general"]
theorem injective_pushforward_proj_obj (I : SheafOfModules.{u} R) [Injective I] :
    Injective ((SheafOfModules.pushforward.{u} (F := proj K)
      (𝟙 (restrictedRingSheaf K J JD R) :
        (restrictedRingSheaf K J JD R) ⟶ (restrictedRingSheaf K J JD R))).obj I) :=
  have := preservesInjectiveObjects_pushforward_proj K J JD R
  Functor.injective_obj _ I

end Sheaves

end Stacks.Sites.ExtensionByZero.OverElements

end
