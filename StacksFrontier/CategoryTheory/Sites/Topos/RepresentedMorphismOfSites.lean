module

public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismsOfTopoi
public import StacksFrontier.CategoryTheory.Sites.Representable.RepresentableSheafDefs
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Subcanonical
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reading a functor between topoi off the objects representing its values on representables

Let `(C, J)` and `(D, K)` be sites with `J` subcanonical and let `H : Sh(D) ⥤ Sh(C)` be a
functor. Suppose each sheaf `H(h_V^#)`, for `V` an object of `D`, is representable on `C`, say by
an object `u(V)`. Choosing those objects and those isomorphisms makes `u` into a functor
`D ⥤ C`, because `J.yoneda` is fully faithful, and makes `H ∘ (-)^#` isomorphic to
`J.yoneda ∘ u`. This file carries out that construction and records what `u` inherits from `H`:

* if `H` preserves finite limits, so does `u`, since `J.yoneda` creates them;
* if `H` has a right adjoint, then `u` is continuous, with `u^s ≅ H.rightAdjoint` and
  `u_s ≅ H`; and
* if `H` is an *equivalence* and `C` has fibre products, then `u` is a special cocontinuous
  functor, i.e. `u.IsDenseSubsite K J`.

The last item is the step that lets an equivalence of topoi be presented on a single site: `H` is
read as a functor between the two sites, not merely between the two topoi. It is proved by
feeding `u` to Stacks 03A1 — the full subcategory in question being the image of `J.yoneda`
transported along `H⁻¹`, which is `Sh(D)` itself up to equivalence — and then identifying the
topology Stacks 03A1 produces with `J` itself, using that a family of arrows of `C` generates a
`J`-covering sieve exactly when the induced map of sheafified representables is an epimorphism.

## Main definitions

* `Stacks.Topos.RepresentedFunctor.representedFunctor`: the functor `u : B ⥤ C` chosen from a
  functor `B ⥤ Sh(C)` all of whose values are representable.
* `Stacks.Topos.RepresentedFunctor.representedFunctorIso`: the isomorphism of the given functor
  with `u ⋙ J.yoneda`.
* `Stacks.Topos.RepresentedFunctor.representedPullbackIso`: the identification `u_s ≅ H`.

## Main results

* `Stacks.Topos.RepresentedFunctor.representedFunctor_isContinuous`: `u` is continuous.
* `Stacks.Topos.RepresentedFunctor.representedFunctor_isDenseSubsite`: if `H` is an equivalence
  then `u` is a special cocontinuous functor.

## Implementation notes

The construction is `Classical.choose` applied to the representability hypothesis, so it is
noncomputable and no claim is made about which object represents which sheaf; only the chosen
isomorphism is ever used. Representability is taken in the sheaf-level form
`IsRepresentableSheaf` of Stacks 00WR rather than as representability of the underlying presheaf,
since it is the sheaf-level isomorphism that the construction needs; the two are interchangeable
for a subcanonical topology, which is `isRepresentableSheaf_of_obj_isRepresentable` and
`obj_isRepresentable_of_isRepresentableSheaf` below.

The universes are those of a Stacks site: both sites are `SmallCategory`s on `Type u` and the
sheaves take values in `Type u`. This matches Stacks 03A1 and Stacks 03CI, whose output sites
live in a single universe.

## References

* [Stacks 03A1](https://stacks.math.columbia.edu/tag/03A1),
  [Stacks 00WR](https://stacks.math.columbia.edu/tag/00WR),
  [Stacks 03CG](https://stacks.math.columbia.edu/tag/03CG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Topos.RepresentedFunctor

/-- For a subcanonical topology, a sheaf whose underlying presheaf is representable is
representable as a sheaf: the representing isomorphism of presheaves is the image under the fully
faithful `sheafToPresheaf` of an isomorphism of sheaves. -/
theorem isRepresentableSheaf_of_obj_isRepresentable {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) [J.Subcanonical] (F : Sheaf J (Type u))
    (h : F.obj.IsRepresentable) : IsRepresentableSheaf J F := by
  obtain ⟨U, ⟨r⟩⟩ := h.has_representation
  have e' : (sheafToPresheaf J (Type u)).obj (J.yoneda.obj U) ≅
      (sheafToPresheaf J (Type u)).obj F :=
    J.yonedaCompSheafToPresheaf.app U ≪≫ Functor.representableByEquiv r
  exact ⟨U, ⟨(fullyFaithfulSheafToPresheaf J (Type u)).preimageIso e'.symm⟩⟩

/-- For a subcanonical topology, the underlying presheaf of a representable sheaf is
representable. -/
theorem obj_isRepresentable_of_isRepresentableSheaf {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) [J.Subcanonical] (F : Sheaf J (Type u))
    (h : IsRepresentableSheaf J F) : F.obj.IsRepresentable := by
  obtain ⟨U, ⟨e⟩⟩ := h
  exact isRepresentable_of_natIso (CategoryTheory.yoneda.obj U)
    ((J.yonedaCompSheafToPresheaf.app U).symm ≪≫ ((sheafToPresheaf J (Type u)).mapIso e).symm)

/-- Sheaves of types admit all small colimits; this is Mathlib's instance, restated so that it
can be used as a local instance for colimits indexed by a category in an arbitrary universe. -/
@[sga "4 IV 1.1.2" "more general"]
theorem sheaf_hasColimit {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    {I : Type*} [Category* I] [HasColimitsOfShape I (Type u)] (F : I ⥤ Sheaf J (Type u)) :
    HasColimit F :=
  @HasColimitsOfShape.has_colimit _ _ _ _ Sheaf.instHasColimitsOfShape F

attribute [local instance] sheaf_hasColimit

/-- A family of arrows `Y i ⟶ X` of a site generates a covering sieve exactly when the induced
morphism `∐ h_{Y i}^# ⟶ h_X^#` of sheafified representables is an epimorphism.

This is Mathlib's `ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map` read through
the identification of local surjectivity of a morphism of presheaves with epimorphy of its
sheafification, and the comparison of the coproduct of sheafifications with the sheafification of
the coproduct. -/
@[sga "4 III 4.1.2" "Final step of 4.1.2"]
theorem epi_sigmaDesc_sheafifiedYoneda_iff {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) {X : C} {ι : Type u} (Y : ι → C) (f : (i : ι) → Y i ⟶ X) :
    Sieve.ofArrows Y f ∈ J X ↔
      Epi (Sigma.desc fun i : ι => (Sheaf.sheafifiedYoneda J).map (f i)) := by
  let eCop := (asIso (sigmaComparison (presheafToSheaf J (Type u))
    (fun i : ι => uliftYoneda.{u}.obj (Y i)))).symm
  let p₀ : (∐ fun i : ι => uliftYoneda.{u}.obj (Y i)) ⟶ uliftYoneda.{u}.obj X :=
    Sigma.desc fun i : ι => uliftYoneda.{u}.map (f i)
  let p := (presheafToSheaf J (Type u)).map p₀
  let q : (∐ fun i : ι => (presheafToSheaf J (Type u)).obj (uliftYoneda.{u}.obj (Y i))) ⟶
      (presheafToSheaf J (Type u)).obj (uliftYoneda.{u}.obj X) :=
    Sigma.desc fun i : ι => (presheafToSheaf J (Type u)).map (uliftYoneda.{u}.map (f i))
  have hcomp : eCop.hom ≫ q = p := by
    have hq : sigmaComparison (presheafToSheaf J (Type u))
        (fun i : ι => uliftYoneda.{u}.obj (Y i)) ≫ (presheafToSheaf J (Type u)).map p₀ = q :=
      sigmaComparison_map_desc (presheafToSheaf J (Type u))
        (fun i : ι => uliftYoneda.{u}.obj (Y i)) (uliftYoneda.{u}.obj X)
        (fun i : ι => uliftYoneda.{u}.map (f i))
    rw [← hq]
    simp [eCop, p]
  have hcover : Sieve.ofArrows Y f ∈ J X ↔ Epi p := by
    rw [GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map,
      ← Presheaf.isLocallySurjective_presheafToSheaf_map_iff, Sheaf.isLocallySurjective_iff_epi]
  rw [hcover, ← hcomp]
  exact epi_comp_iff_of_epi eCop.hom q

/-- An object of `C` representing the value of `F` at `b`, chosen once and for all. -/
noncomputable def chosenRepresentingObject {C : Type u} [SmallCategory C] {B : Type u}
    [Category B] (J : GrothendieckTopology C) [J.Subcanonical] (F : B ⥤ Sheaf J (Type u))
    (h : ∀ b, IsRepresentableSheaf J (F.obj b)) (b : B) : C :=
  Classical.choose (h b)

/-- The chosen isomorphism of `F.obj b` with the sheaf represented by
`chosenRepresentingObject J F h b`. -/
noncomputable def chosenRepresentingIso {C : Type u} [SmallCategory C] {B : Type u}
    [Category B] (J : GrothendieckTopology C) [J.Subcanonical] (F : B ⥤ Sheaf J (Type u))
    (h : ∀ b, IsRepresentableSheaf J (F.obj b)) (b : B) :
    F.obj b ≅ J.yoneda.obj (chosenRepresentingObject J F h b) :=
  Classical.choice (Classical.choose_spec (h b))

/-- The functor `B ⥤ C` reading off objects of `C` representing the values of a functor
`F : B ⥤ Sh(C)` whose values are all representable sheaves.

Functoriality is forced: `J.yoneda` is fully faithful for a subcanonical topology, so a morphism
of `B` has a unique preimage along `J.yoneda` of the corresponding morphism of representing
sheaves. -/
noncomputable def representedFunctor {C : Type u} [SmallCategory C] {B : Type u} [Category B]
    (J : GrothendieckTopology C) [J.Subcanonical] (F : B ⥤ Sheaf J (Type u))
    (h : ∀ b, IsRepresentableSheaf J (F.obj b)) : B ⥤ C where
  obj b := chosenRepresentingObject J F h b
  map {b c} f := J.yoneda.preimage
    ((chosenRepresentingIso J F h b).inv ≫ F.map f ≫ (chosenRepresentingIso J F h c).hom)
  map_id b := by
    apply J.yoneda.map_injective
    simp [chosenRepresentingIso]
  map_comp f g := by
    apply J.yoneda.map_injective
    simp [chosenRepresentingIso]

/-- The functor of `representedFunctor` does represent: `F ≅ u ⋙ J.yoneda`. -/
noncomputable def representedFunctorIso {C : Type u} [SmallCategory C] {B : Type u} [Category B]
    (J : GrothendieckTopology C) [J.Subcanonical] (F : B ⥤ Sheaf J (Type u))
    (h : ∀ b, IsRepresentableSheaf J (F.obj b)) : F ≅ representedFunctor J F h ⋙ J.yoneda := by
  classical
  refine NatIso.ofComponents (fun b => chosenRepresentingIso J F h b) ?_
  intro b c f
  dsimp [representedFunctor]
  rw [Functor.map_preimage]
  simp [chosenRepresentingIso]

/-- If a functor to sheaves preserves finite limits and has representable values, the functor
reading off the representing objects preserves finite limits: `J.yoneda` reflects limits and
`u ⋙ J.yoneda` preserves them. -/
theorem preservesFiniteLimits_representedFunctor {C : Type u} [SmallCategory C] {B : Type u}
    [Category B] (J : GrothendieckTopology C) [J.Subcanonical] (F : B ⥤ Sheaf J (Type u))
    (h : ∀ b, IsRepresentableSheaf J (F.obj b)) [PreservesFiniteLimits F] :
    PreservesFiniteLimits (representedFunctor J F h) := by
  have : PreservesFiniteLimits (representedFunctor J F h ⋙ J.yoneda) :=
    preservesFiniteLimits_of_natIso (representedFunctorIso J F h)
  exact preservesFiniteLimits_of_reflects_of_preserves (representedFunctor J F h) J.yoneda

section Adjoint

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (J : GrothendieckTopology C)
  [J.Subcanonical] (K : GrothendieckTopology D) (H : Sheaf K (Type u) ⥤ Sheaf J (Type u))
  [H.IsLeftAdjoint]
  (h : ∀ V, IsRepresentableSheaf J (H.obj ((Sheaf.sheafifiedYoneda K).obj V)))

/-- The sections of a sheaf `P` on `C` over the object representing `H(h_V^#)` are the sections
over `V` of the value at `P` of the right adjoint of `H`.

Both are the morphisms `H(h_V^#) ⟶ P`: on the left by Yoneda on the site `C`, on the right by
the adjunction followed by Yoneda on the site `D`. -/
noncomputable def representedSectionEquiv (V : D) (P : Sheaf J (Type u)) :
    P.obj.obj (Opposite.op ((representedFunctor J (Sheaf.sheafifiedYoneda K ⋙ H) h).obj V)) ≃
      (H.rightAdjoint.obj P).obj.obj (Opposite.op V) := by
  let e := representedFunctorIso J (Sheaf.sheafifiedYoneda K ⋙ H) h
  let precomp :
      (J.yoneda.obj ((representedFunctor J (Sheaf.sheafifiedYoneda K ⋙ H) h).obj V) ⟶ P) ≃
        ((H.obj ((Sheaf.sheafifiedYoneda K).obj V)) ⟶ P) :=
    { toFun := fun f => e.hom.app V ≫ f
      invFun := fun f => e.inv.app V ≫ f
      left_inv := fun f => by
        simpa only [Functor.comp_obj] using Iso.inv_hom_id_app_assoc e V f
      right_inv := fun f => by
        simpa only [Functor.comp_obj] using Iso.hom_inv_id_app_assoc e V f }
  exact Equiv.trans (GrothendieckTopology.yonedaEquiv J).symm
    (Equiv.trans precomp <| Equiv.trans
      ((Adjunction.ofIsLeftAdjoint H).homEquiv ((Sheaf.sheafifiedYoneda K).obj V) P)
      (Sheaf.sectionEquiv K))

/-- Restriction of a sheaf on `C` along the functor reading off the representing objects is the
value at that sheaf of the right adjoint of `H`. -/
noncomputable def representedRestrictionIso (P : Sheaf J (Type u)) :
    (representedFunctor J (Sheaf.sheafifiedYoneda K ⋙ H) h).op ⋙ P.obj ≅
      (H.rightAdjoint.obj P).obj := by
  classical
  let U := representedFunctor J (Sheaf.sheafifiedYoneda K ⋙ H) h
  let e := representedFunctorIso J (Sheaf.sheafifiedYoneda K ⋙ H) h
  refine NatIso.ofComponents (fun V => Equiv.toIso (representedSectionEquiv J K H h V.unop P)) ?_
  intro V V' k
  ext x
  change representedSectionEquiv J K H h V'.unop P (P.obj.map (U.map k.unop).op x) =
    (H.rightAdjoint.obj P).obj.map k (representedSectionEquiv J K H h V.unop P x)
  simp only [representedSectionEquiv, Equiv.trans_apply]
  change (Sheaf.sectionEquiv K (X := V'.unop) (F := H.rightAdjoint.obj P)) _ =
    (H.rightAdjoint.obj P).obj.map k.unop.op
      ((Sheaf.sectionEquiv K (X := V.unop) (F := H.rightAdjoint.obj P)) _)
  rw [← Sheaf.sectionEquiv_map_comp (J := K) (i := k.unop)]
  apply congrArg (Sheaf.sectionEquiv K)
  change (Adjunction.ofIsLeftAdjoint H).homEquiv ((Sheaf.sheafifiedYoneda K).obj V'.unop) P
      (e.hom.app V'.unop ≫ J.yonedaEquiv.symm (P.obj.map (U.map k.unop).op x)) =
    (Sheaf.sheafifiedYoneda K).map k.unop ≫
      (Adjunction.ofIsLeftAdjoint H).homEquiv ((Sheaf.sheafifiedYoneda K).obj V.unop) P
        (e.hom.app V.unop ≫ J.yonedaEquiv.symm x)
  rw [GrothendieckTopology.yonedaEquiv_symm_map, ← Category.assoc]
  change (Adjunction.ofIsLeftAdjoint H).homEquiv ((Sheaf.sheafifiedYoneda K).obj V'.unop) P
      ((e.hom.app V'.unop ≫ (U ⋙ J.yoneda).map k.unop) ≫ J.yonedaEquiv.symm x) = _
  rw [← e.hom.naturality (k.unop)]
  simpa only [Functor.comp_map, Category.assoc] using
    (Adjunction.homEquiv_naturality_left (Adjunction.ofIsLeftAdjoint H)
      ((Sheaf.sheafifiedYoneda K).map k.unop) (e.hom.app V.unop ≫ J.yonedaEquiv.symm x))

/-- The functor reading off the representing objects of a left adjoint is continuous: restriction
along it carries a sheaf to the value of the right adjoint of `H`, which is a sheaf. -/
theorem representedFunctor_isContinuous :
    (representedFunctor J (Sheaf.sheafifiedYoneda K ⋙ H) h).IsContinuous K J := by
  classical
  refine ⟨fun P => ?_⟩
  rw [← isSheaf_iff_isSheaf_of_type]
  exact (Presheaf.isSheaf_of_iso_iff (representedRestrictionIso J K H h P)).2
    (H.rightAdjoint.obj P).property

/-- The pushforward of sheaves along the functor reading off the representing objects is the
right adjoint of `H`. -/
noncomputable def representedPushforwardIso
    [Functor.IsContinuous (representedFunctor J (Sheaf.sheafifiedYoneda K ⋙ H) h) K J] :
    (representedFunctor J (Sheaf.sheafifiedYoneda K ⋙ H) h).sheafPushforwardContinuous
        (Type u) K J ≅ H.rightAdjoint := by
  classical
  let U := representedFunctor J (Sheaf.sheafifiedYoneda K ⋙ H) h
  let e := representedFunctorIso J (Sheaf.sheafifiedYoneda K ⋙ H) h
  refine NatIso.ofComponents (fun P => ?_) ?_
  · let eP := representedRestrictionIso J K H h P
    exact ⟨ObjectProperty.homMk eP.hom, ObjectProperty.homMk eP.inv,
      Sheaf.hom_ext eP.hom_inv_id, Sheaf.hom_ext eP.inv_hom_id⟩
  · intro P Q f
    apply Sheaf.hom_ext
    ext V x
    change P.obj.obj (Opposite.op (U.obj V.unop)) at x
    change representedSectionEquiv J K H h V.unop Q
        ((ConcreteCategory.hom (f.hom.app (Opposite.op (U.obj V.unop)))) x) =
      (ConcreteCategory.hom ((H.rightAdjoint.map f).hom.app V))
        (representedSectionEquiv J K H h V.unop P x)
    simp only [representedSectionEquiv, Equiv.trans_apply]
    rw [← Sheaf.sectionEquiv_comp]
    apply congrArg (Sheaf.sectionEquiv K)
    rw [← GrothendieckTopology.yonedaEquiv_symm_naturality_right]
    change (Adjunction.ofIsLeftAdjoint H).homEquiv ((Sheaf.sheafifiedYoneda K).obj V.unop) Q
        (e.hom.app V.unop ≫ (J.yonedaEquiv.symm x ≫ f)) =
      (Adjunction.ofIsLeftAdjoint H).homEquiv ((Sheaf.sheafifiedYoneda K).obj V.unop) P
        (e.hom.app V.unop ≫ J.yonedaEquiv.symm x) ≫ H.rightAdjoint.map f
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right]

/-- The pullback of sheaves along the functor reading off the representing objects is `H` itself:
both are left adjoint to `representedPushforwardIso`. -/
noncomputable def representedPullbackIso
    [Functor.IsContinuous (representedFunctor J (Sheaf.sheafifiedYoneda K ⋙ H) h) K J] :
    (representedFunctor J (Sheaf.sheafifiedYoneda K ⋙ H) h).sheafPullback (Type u) K J ≅ H :=
  Adjunction.leftAdjointUniq
    ((representedFunctor J (Sheaf.sheafifiedYoneda K ⋙ H) h).sheafAdjunctionContinuous
      (Type u) K J)
    ((Adjunction.ofIsLeftAdjoint H).ofNatIsoRight (representedPushforwardIso J K H h).symm)

end Adjoint

/-- Whether a morphism out of a coproduct is an epimorphism is unchanged by applying an
equivalence to all of its components. -/
theorem epi_sigmaDesc_map_iff {A : Type*} {B : Type*} [Category A] [Category B]
    (H : A ⥤ B) [H.IsEquivalence] {ι : Type*} {Y : ι → A} {X : A} (f : ∀ i, Y i ⟶ X)
    [HasCoproduct Y] [HasCoproduct (fun i => H.obj (Y i))] :
    Epi (Sigma.desc fun i => H.map (f i)) ↔ Epi (Sigma.desc f) := by
  rw [← sigmaComparison_map_desc H Y X f, epi_comp_iff_of_epi, H.epi_map_iff_epi]

/-- Whether a morphism out of a coproduct is an epimorphism is unchanged by replacing the functor
whose images it is assembled from by an isomorphic one. -/
theorem epi_sigmaDesc_natIso_iff {C : Type*} {A : Type*} [Category C] [Category A]
    {F G : C ⥤ A} (e : F ≅ G) {ι : Type*} {Y : ι → C} {X : C} (f : ∀ i, Y i ⟶ X)
    [HasCoproduct (fun i => F.obj (Y i))] [HasCoproduct (fun i => G.obj (Y i))] :
    Epi (Sigma.desc fun i => F.map (f i)) ↔ Epi (Sigma.desc fun i => G.map (f i)) := by
  have he : Sigma.desc (fun i => F.map (f i)) ≫ e.hom.app X =
      CategoryTheory.Limits.Sigma.map (fun i => e.hom.app (Y i)) ≫
        Sigma.desc (fun i => G.map (f i)) := by
    ext i
    simp only [Sigma.ι_desc_assoc, Sigma.ι_map_assoc, Sigma.ι_desc]
    exact e.hom.naturality (f i)
  rw [← epi_comp_iff_of_isIso _ (e.hom.app X), he, epi_comp_iff_of_epi]

/-- For a subcanonical topology the sheafified Yoneda embedding is the Yoneda embedding into
sheaves: the sheafification of a representable presheaf is that presheaf. -/
noncomputable def sheafifiedYonedaIsoYoneda {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) [J.Subcanonical] : Sheaf.sheafifiedYoneda J ≅ J.yoneda :=
  (Functor.isoWhiskerRight (GrothendieckTopology.uliftYonedaCompSheafToPresheaf.{u} J).symm
      (presheafToSheaf J (Type u))) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso (sheafificationAdjunction J (Type u)).counit) ≪≫
    Functor.rightUnitor _ ≪≫ J.uliftYonedaIsoYoneda

/-- **An equivalence of topoi is a special cocontinuous functor of sites, once the sites are good
enough.** If `H : Sh(D) ⥤ Sh(C)` is an equivalence carrying each `h_V^#` to a representable sheaf
on `C`, both topologies are subcanonical and `C` has fibre products, then the functor `u : D ⥤ C`
reading off the representing objects exhibits `(D, K)` as a dense subsite of `(C, J)`, i.e. is a
special cocontinuous functor in the sense of Stacks 03CG.

Stacks 03A1 is applied to the site `(D, K)` and the full subcategory `J.yoneda ⋙ H⁻¹` of `Sh(D)`
indexed by `C`, with `u` as its `U ↦ h_U^#`; it produces a topology on `C` for which `u` is a
dense subsite. That topology is `J`: both characterize a family of arrows as covering by
epimorphy of the induced map of sheafified representables, and `H⁻¹` is an equivalence, so does
not change epimorphy. -/
theorem representedFunctor_isDenseSubsite {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) [J.Subcanonical] [HasFiniteLimits C]
    (K : GrothendieckTopology D) [K.Subcanonical] (H : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    [H.IsEquivalence]
    (h : ∀ V, IsRepresentableSheaf J (H.obj ((Sheaf.sheafifiedYoneda K).obj V))) :
    (representedFunctor J (Sheaf.sheafifiedYoneda K ⋙ H) h).IsDenseSubsite K J := by
  let U := representedFunctor J (Sheaf.sheafifiedYoneda K ⋙ H) h
  let Q := J.yoneda ⋙ H.asEquivalence.inverse
  let e : U ⋙ Q ≅ Sheaf.sheafifiedYoneda K :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (representedFunctorIso J _ h).symm H.asEquivalence.inverse ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ H.asEquivalence.unitIso.symm ≪≫ Functor.rightUnitor _
  let : PreservesLimitsOfShape WalkingCospan Q := by
    dsimp [Q]
    infer_instance
  obtain ⟨L, hL, _, hU, _⟩ := GrothendieckTopology.exists_isDenseSubsite_subcanonical K Q U e
  have hLJ : L = J := by
    ext V S
    obtain ⟨ι, Y, f, rfl⟩ := S.exists_eq_ofArrows
    rw [hL Y f (coproductIsCoproduct (fun i : ι => Q.obj (Y i)))]
    show Epi (Sigma.desc (fun i => H.asEquivalence.inverse.map (J.yoneda.map (f i)))) ↔ _
    rw [epi_sigmaDesc_map_iff, ← epi_sigmaDesc_natIso_iff (sheafifiedYonedaIsoYoneda J),
      ← epi_sigmaDesc_sheafifiedYoneda_iff]
  subst L
  exact hU

end Stacks.Topos.RepresentedFunctor

end
