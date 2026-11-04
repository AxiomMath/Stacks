module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Localization.Construction

/-!
# Morphisms into a local object of a Gabriel–Zisman localization

Let `W` be a class of morphisms of a category `C` and let `P` be a property of objects of `C`
whose objects are *local* for `W`, meaning that precomposition with a morphism of `W` is
bijective on morphisms into them. Assume moreover that every object of `C` admits a morphism of
`W` into an object satisfying `P`. Then the localization functor `W.Q : C ⥤ W.Localization` is
bijective on morphisms into an object satisfying `P`:
`(X ⟶ I) ⟶ (W.Q.obj X ⟶ W.Q.obj I)` is a bijection whenever `P I`.

This is the mechanism by which the morphism groups of a derived category are computed by
homotopy classes of maps into a K-injective resolution, and it needs no calculus of fractions:
the two hypotheses already make the chosen resolutions into a *functor* on `C` inverting `W`,
and the functor it descends to on the localization is inverse to `W.Q` on the nose.

## Main definitions

* `CategoryTheory.MorphismProperty.LocalResolutions` bundles the two hypotheses.
* `CategoryTheory.MorphismProperty.LocalResolutions.functor` is the resolution functor `C ⥤ C`,
  with `CategoryTheory.MorphismProperty.LocalResolutions.ι` the morphism of `W` into it.
* `CategoryTheory.MorphismProperty.LocalResolutions.liftFunctor` is its descent
  `W.Localization ⥤ C`.

## Main results

* `CategoryTheory.MorphismProperty.LocalResolutions.isIso_map`: the resolution functor sends
  `W` to isomorphisms.
* `CategoryTheory.MorphismProperty.LocalResolutions.exists_inverse_ι` and
  `CategoryTheory.MorphismProperty.LocalResolutions.isIso_ι`: an object satisfying `P` is
  already isomorphic to its resolution.
* `CategoryTheory.MorphismProperty.LocalResolutions.bijective_Q_map`: the localization functor
  is bijective on morphisms into an object satisfying `P`.
* `CategoryTheory.MorphismProperty.LocalResolutions.isLimitMapFan`: the localization functor
  sends a limit fan all of whose objects satisfy `P` to a limit fan.
* `CategoryTheory.MorphismProperty.LocalResolutions.isColimitMapCofan`: the localization
  functor sends a colimit cofan to a colimit cofan.

## Implementation notes

The resolution of an object is *chosen* from the existence hypothesis, so the resolution
functor is not canonical; its action on morphisms, however, is forced, being the unique
morphism of resolutions compatible with the two chosen inclusions. That uniqueness is the
injectivity half of the locality hypothesis, and it is what makes the assignment functorial
with no further input.

The localization is Mathlib's Gabriel–Zisman construction `W.Localization` rather than an
abstract `Functor.IsLocalization`, because its universal property holds with an *equality*
`W.Q ⋙ lift F = F` of functors and its natural transformations extend from `W.Q` with no
transport; both are used below, and the general case would only add `eqToHom`s.
-/

@[expose] public noncomputable section

namespace CategoryTheory

universe w v u

namespace MorphismProperty

variable {C : Type u} [Category.{v} C]

/-- Two equal functors have heterogeneously equal actions on a morphism. This is used where the
object parts of the two functors are *definitionally* equal, so that the heterogeneous equality
can be read as an equality with no transport. -/
private theorem map_heq_of_functor_eq {D : Type*} [Category D] {F G : C ⥤ D} (h : F = G)
    {X Y : C} (f : X ⟶ Y) : HEq (F.map f) (G.map f) := by
  subst h
  rfl

/-- The hypotheses making the objects with property `P` a class of resolutions for the class of
morphisms `W`: they are local for `W`, and every object maps into one by a morphism of `W`. -/
structure LocalResolutions (W : MorphismProperty C) (P : C → Prop) where
  /-- Precomposition with a morphism of `W` is bijective on morphisms into a `P`-object. -/
  bijective_comp : ∀ {X Y : C} (s : X ⟶ Y), W s → ∀ I : C, P I →
    Function.Bijective (fun g : Y ⟶ I => s ≫ g)
  /-- Every object admits a morphism of `W` into a `P`-object. -/
  exists_resolution : ∀ X : C, ∃ (I : C) (s : X ⟶ I), W s ∧ P I

namespace LocalResolutions

variable {W : MorphismProperty C} {P : C → Prop} (H : LocalResolutions W P)

/-- The chosen resolution of an object. -/
def obj (X : C) : C := (H.exists_resolution X).choose

/-- The chosen morphism of `W` from an object into its resolution. -/
def ι (X : C) : X ⟶ H.obj X := (H.exists_resolution X).choose_spec.choose

/-- The chosen inclusion of an object into its resolution lies in `W`. -/
theorem ι_mem (X : C) : W (H.ι X) :=
  (H.exists_resolution X).choose_spec.choose_spec.1

/-- The chosen resolution of an object satisfies `P`. -/
theorem prop_obj (X : C) : P (H.obj X) :=
  (H.exists_resolution X).choose_spec.choose_spec.2

/-- Precomposition with the chosen inclusion is bijective on morphisms into a `P`-object. -/
private theorem bijective_ι_comp (X : C) {I : C} (hI : P I) :
    Function.Bijective (fun g : H.obj X ⟶ I => H.ι X ≫ g) :=
  H.bijective_comp (H.ι X) (H.ι_mem X) I hI

/-- Two morphisms from a resolution into a `P`-object agree if they agree after precomposition
with the chosen inclusion. -/
theorem hom_ext {X I : C} (hI : P I) {g g' : H.obj X ⟶ I}
    (h : H.ι X ≫ g = H.ι X ≫ g') : g = g' :=
  (H.bijective_ι_comp X hI).injective h

/-- The action of the resolution functor on a morphism: the unique morphism of resolutions
compatible with the two chosen inclusions. -/
def map {X Y : C} (f : X ⟶ Y) : H.obj X ⟶ H.obj Y :=
  ((H.bijective_comp (H.ι X) (H.ι_mem X) (H.obj Y) (H.prop_obj Y)).surjective
    (f ≫ H.ι Y)).choose

/-- The resolution of a morphism is compatible with the chosen inclusions. -/
@[simp]
theorem ι_comp_map {X Y : C} (f : X ⟶ Y) : H.ι X ≫ H.map f = f ≫ H.ι Y :=
  ((H.bijective_ι_comp X (H.prop_obj Y)).surjective (f ≫ H.ι Y)).choose_spec

/-- The resolution functor. -/
def functor : C ⥤ C where
  obj := H.obj
  map := H.map
  map_id X := H.hom_ext (H.prop_obj X) (by rw [H.ι_comp_map, Category.id_comp, Category.comp_id])
  map_comp {X Y Z} f g := H.hom_ext (H.prop_obj Z) (by
    simp only [← Category.assoc, H.ι_comp_map]
    simp only [Category.assoc, H.ι_comp_map])

/-- The resolution functor sends an object to its chosen resolution. -/
@[simp] theorem functor_obj (X : C) : H.functor.obj X = H.obj X := rfl

/-- The resolution functor acts on morphisms by `LocalResolutions.map`. -/
@[simp] theorem functor_map {X Y : C} (f : X ⟶ Y) : H.functor.map f = H.map f := rfl

/-- Precomposition with the resolution of a morphism of `W` is bijective on morphisms into a
`P`-object: it becomes precomposition with that morphism after the two chosen inclusions. -/
theorem bijective_comp_map {X Y : C} (s : X ⟶ Y) (hs : W s) {I : C} (hI : P I) :
    Function.Bijective (fun g : H.obj Y ⟶ I => H.map s ≫ g) := by
  have hcomp : (fun g : H.obj X ⟶ I => H.ι X ≫ g) ∘ (fun g : H.obj Y ⟶ I => H.map s ≫ g) =
      (fun g : Y ⟶ I => s ≫ g) ∘ (fun g : H.obj Y ⟶ I => H.ι Y ≫ g) := by
    funext g
    simp only [Function.comp_apply, ← Category.assoc, H.ι_comp_map]
  refine ((H.bijective_ι_comp X hI).of_comp_iff' _).1 ?_
  rw [hcomp]
  exact (H.bijective_comp s hs I hI).comp (H.bijective_ι_comp Y hI)

/-- The resolution functor sends a morphism of `W` to an isomorphism: a one-sided inverse is
produced by the previous bijection, and is two-sided by its injectivity half. -/
theorem isIso_map {X Y : C} (s : X ⟶ Y) (hs : W s) : IsIso (H.map s) := by
  obtain ⟨t, ht : H.map s ≫ t = 𝟙 _⟩ :=
    (H.bijective_comp_map s hs (H.prop_obj X)).surjective (𝟙 (H.obj X))
  refine ⟨⟨t, ht, (H.bijective_comp_map s hs (H.prop_obj Y)).injective ?_⟩⟩
  simp [reassoc_of% ht]

/-- An object satisfying `P` is already isomorphic to its chosen resolution: a retraction of
the inclusion is produced by locality, and is a two-sided inverse by its injectivity half. -/
theorem exists_inverse_ι {I : C} (hI : P I) :
    ∃ t : H.obj I ⟶ I, H.ι I ≫ t = 𝟙 I ∧ t ≫ H.ι I = 𝟙 (H.obj I) := by
  obtain ⟨t, ht : H.ι I ≫ t = 𝟙 I⟩ :=
    (H.bijective_ι_comp I hI).surjective (𝟙 I)
  refine ⟨t, ht, H.hom_ext (H.prop_obj I) ?_⟩
  rw [← Category.assoc, ht, Category.id_comp, Category.comp_id]

/-- An object satisfying `P` is already isomorphic to its chosen resolution. -/
theorem isIso_ι {I : C} (hI : P I) : IsIso (H.ι I) := ⟨H.exists_inverse_ι hI⟩

/-- The resolution functor inverts `W`. -/
theorem functor_inverts : W.IsInvertedBy H.functor := fun _ _ s hs => H.isIso_map s hs

/-- The descent of the resolution functor to the localization. -/
def liftFunctor : W.Localization ⥤ C :=
  Localization.Construction.lift H.functor H.functor_inverts

/-- The localization functor followed by the descended resolution functor is the resolution
functor. -/
theorem Q_comp_liftFunctor : W.Q ⋙ H.liftFunctor = H.functor :=
  Localization.Construction.fac _ _

/-- The descended resolution functor sends the image of a morphism in the localization to its
resolution. -/
theorem liftFunctor_Q_map {X Y : C} (f : X ⟶ Y) :
    H.liftFunctor.map (W.Q.map f) = H.map f :=
  eq_of_heq (map_heq_of_functor_eq H.Q_comp_liftFunctor f)

/-- The chosen inclusions, read in the localization, assemble into a natural transformation from
the identity to the descended resolution functor followed by the localization functor. -/
def localizationUnit : 𝟭 W.Localization ⟶ H.liftFunctor ⋙ W.Q :=
  Localization.Construction.natTransExtension
    { app := fun X => W.Q.map (H.ι X)
      naturality := fun {X Y} f => by
        have key : W.Q.map f ≫ W.Q.map (H.ι Y) = W.Q.map (H.ι X) ≫ W.Q.map (H.map f) := by
          rw [← W.Q.map_comp, ← W.Q.map_comp, H.ι_comp_map]
        exact key.trans (congrArg (fun φ : H.obj X ⟶ H.obj Y => W.Q.map (H.ι X) ≫ W.Q.map φ)
          (H.liftFunctor_Q_map f).symm) }

/-- The component of `localizationUnit` at the image of an object is the image of the chosen
inclusion. -/
theorem localizationUnit_app_Q_obj (X : C) :
    H.localizationUnit.app (W.Q.obj X) = W.Q.map (H.ι X) :=
  Localization.Construction.NatTransExtension.app_eq _ X

include H in
/-- **The localization functor of the Gabriel–Zisman construction is bijective on morphisms
into an object which is local for `W`.** -/
theorem bijective_Q_map (X : C) {I : C} (hI : P I) :
    Function.Bijective (fun f : X ⟶ I => W.Q.map f) := by
  refine ⟨fun f f' hff' => ?_, fun g => ?_⟩
  · have hmap := congrArg H.liftFunctor.map hff'
    simp only [H.liftFunctor_Q_map] at hmap
    have := H.isIso_ι hI
    rw [← cancel_mono (H.ι I), ← H.ι_comp_map, ← H.ι_comp_map, hmap]
  · obtain ⟨t, ht₁, -⟩ := H.exists_inverse_ι hI
    obtain ⟨ψ, hψ⟩ : ∃ ψ : H.obj X ⟶ H.obj I, W.Q.map ψ = W.Q.map (H.liftFunctor.map g) :=
      ⟨H.liftFunctor.map g, rfl⟩
    have hnat : g ≫ W.Q.map (H.ι I) = W.Q.map (H.ι X) ≫ W.Q.map ψ := by
      have h := H.localizationUnit.naturality g
      rw [H.localizationUnit_app_Q_obj, H.localizationUnit_app_Q_obj] at h
      exact h.trans (congrArg (fun φ : W.Q.obj (H.obj X) ⟶ W.Q.obj (H.obj I) =>
        W.Q.map (H.ι X) ≫ φ) hψ.symm)
    refine ⟨H.ι X ≫ ψ ≫ t, ?_⟩
    simp only [W.Q.map_comp]
    rw [← Category.assoc, ← hnat, Category.assoc, ← W.Q.map_comp, ht₁, W.Q.map_id,
      Category.comp_id]

/-! ### Transporting a morphism along the bijection -/

include H in
/-- The morphism of `C` corresponding to a morphism of the localization into a `P`-object. -/
def homOfQ {X I : C} (hI : P I) (g : W.Q.obj X ⟶ W.Q.obj I) : X ⟶ I :=
  (Equiv.ofBijective _ (H.bijective_Q_map X hI)).symm g

include H in
/-- The image of `homOfQ H hI g` in the localization is `g`. -/
@[simp]
theorem Q_map_homOfQ {X I : C} (hI : P I) (g : W.Q.obj X ⟶ W.Q.obj I) :
    W.Q.map (homOfQ H hI g) = g :=
  (Equiv.ofBijective _ (H.bijective_Q_map X hI)).apply_symm_apply g

include H in
/-- The localization functor is injective on morphisms into a `P`-object. -/
theorem Q_map_injective {X I : C} (hI : P I) {f f' : X ⟶ I} (h : W.Q.map f = W.Q.map f') :
    f = f' :=
  (H.bijective_Q_map X hI).injective h

/-! ### A `P`-object modelling an object of the localization -/

/-- A `P`-object of `C` whose image in the localization is isomorphic to a given object: the
chosen resolution of a preimage. -/
def model (Y : W.Localization) : C := H.obj (W.Q.objPreimage Y)

/-- The model of an object of the localization satisfies `P`. -/
theorem prop_model (Y : W.Localization) : P (H.model Y) := H.prop_obj _

/-- The image of the model is isomorphic to the given object. -/
def modelIso (Y : W.Localization) : W.Q.obj (H.model Y) ≅ Y :=
  letI : IsIso (W.Q.map (H.ι (W.Q.objPreimage Y))) :=
    MorphismProperty.Q_inverts W _ (H.ι_mem (W.Q.objPreimage Y))
  (asIso (W.Q.map (H.ι (W.Q.objPreimage Y)))).symm ≪≫ W.Q.objObjPreimageIso Y

/-! ### Products and direct sums -/

open Limits in
include H in
/-- **The localization functor sends a limit fan all of whose objects are local for `W` to a
limit fan.** -/
def isLimitMapFan {T : Type w} {J : T → C} (hJ : ∀ k, P (J k)) {c : C} (hc : P c)
    (π : ∀ k, c ⟶ J k) (hlim : IsLimit (Fan.mk c π)) :
    IsLimit (Fan.mk (W.Q.obj c) (fun k => W.Q.map (π k))) := by
  refine Fan.IsLimit.mk _ (fun s => (H.modelIso s.pt).inv ≫
    W.Q.map (Fan.IsLimit.lift hlim
      (fun k => homOfQ H (hJ k) ((H.modelIso s.pt).hom ≫ s.proj k)))) ?_ ?_
  · intro s k
    have h := Fan.IsLimit.fac hlim
      (fun j => homOfQ H (hJ j) ((H.modelIso s.pt).hom ≫ s.proj j)) k
    rw [fan_mk_proj] at h
    dsimp only [fan_mk_proj]
    rw [Category.assoc, ← W.Q.map_comp, h, Q_map_homOfQ, Iso.inv_hom_id_assoc]
  · intro s m hm
    rw [fan_mk_proj] at hm
    have key : homOfQ H hc ((H.modelIso s.pt).hom ≫ m) =
        Fan.IsLimit.lift hlim
          (fun k => homOfQ H (hJ k) ((H.modelIso s.pt).hom ≫ s.proj k)) := by
      refine Fan.IsLimit.hom_ext hlim _ _ fun k => ?_
      rw [Fan.IsLimit.fac hlim, fan_mk_proj]
      refine Q_map_injective H (hJ k) ?_
      rw [W.Q.map_comp, Q_map_homOfQ, Q_map_homOfQ, Category.assoc, hm k]
    rw [← key, Q_map_homOfQ, Iso.inv_hom_id_assoc]

open Limits in
include H in
/-- **The localization functor sends a colimit cofan to a colimit cofan.** No locality is
needed of the objects of the cofan: it is the object a morphism out of the colimit lands in
that is replaced by a local one. -/
def isColimitMapCofan {T : Type w} {Z : T → C} {c : C} (ι : ∀ k, Z k ⟶ c)
    (hcol : IsColimit (Cofan.mk c ι)) :
    IsColimit (Cofan.mk (W.Q.obj c) (fun k => W.Q.map (ι k))) := by
  refine Cofan.IsColimit.mk _ (fun s => W.Q.map (Cofan.IsColimit.desc hcol
      (fun k => homOfQ H (H.prop_model s.pt) (s.inj k ≫ (H.modelIso s.pt).inv))) ≫
        (H.modelIso s.pt).hom) ?_ ?_
  · intro s k
    have h := Cofan.IsColimit.fac hcol
      (fun j => homOfQ H (H.prop_model s.pt) (s.inj j ≫ (H.modelIso s.pt).inv)) k
    rw [cofan_mk_inj] at h
    dsimp only [cofan_mk_inj]
    rw [← Category.assoc, ← W.Q.map_comp, h, Q_map_homOfQ, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  · intro s m hm
    rw [cofan_mk_inj] at hm
    have key : homOfQ H (H.prop_model s.pt) (m ≫ (H.modelIso s.pt).inv) =
        Cofan.IsColimit.desc hcol
          (fun k => homOfQ H (H.prop_model s.pt) (s.inj k ≫ (H.modelIso s.pt).inv)) := by
      refine Cofan.IsColimit.hom_ext hcol _ _ fun k => ?_
      rw [Cofan.IsColimit.fac hcol, cofan_mk_inj]
      refine Q_map_injective H (H.prop_model s.pt) ?_
      rw [W.Q.map_comp, Q_map_homOfQ, Q_map_homOfQ, ← Category.assoc, hm k]
    rw [← key, Q_map_homOfQ, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end LocalResolutions

end MorphismProperty

end CategoryTheory

end
