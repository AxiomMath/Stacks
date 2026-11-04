module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyB
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricFibreSections

/-!
# Sections of a sheaf over a scheme finite étale over a separably closed field

Let `Ω` be a separably closed field and `f : Y ⟶ Spec Ω` a finite étale morphism.  Every section
`ȳ : Spec Ω ⟶ Y` of `f` is an open immersion, the images of distinct sections are disjoint, and
together they cover `Y`: so `Y` is the disjoint union of finitely many copies of `Spec Ω`, one
for each `Ω`-point.  This file draws the consequences for a sheaf `G` on the small étale site of
`Y`.

* A geometric point `s : Spec Ω ⟶ S` which is itself étale is an initial étale neighbourhood of
  itself, so the stalk of a presheaf at `s` is its value on the étale `S`-scheme `s`.  This holds
  for every coefficient category.
* The global sections of `G` are the product of its values on the `Ω`-points of `Y`, that is of
  its stalks at those points.

## Main definitions

* `Stacks.EtaleCohomology.pointSmallEtaleSelfElement` — the identity, as a lift of an étale
  geometric point `s` to the étale `S`-scheme `s` itself.
* `Stacks.EtaleCohomology.presheafFiberSelfIso` — the stalk at an étale geometric point `s` is
  evaluation at the étale `S`-scheme `s`.
* `Stacks.EtaleCohomology.etaleSectionObj` — an `Ω`-point of `Y` as an object of the small étale
  site of `Y`.

## Main results

* `Stacks.EtaleCohomology.isInitialPointSmallEtaleSelfElement` — that lift is initial among
  the étale neighbourhoods of `s`.
* `Stacks.EtaleCohomology.eq_of_etale_section_apply_eq` — two sections of an étale morphism to
  `Spec Ω` with the same image point are equal.
* `Stacks.EtaleCohomology.bijective_etaleSections_restriction` — for `f` finite étale, restriction
  of sections of a sheaf of sets from `Y` to its `Ω`-points is bijective.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 2.
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

/-! ### The stalk at an étale geometric point -/

section Self

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)
  [Etale s]

/-- The identity, viewed as a lift of the geometric point `s` to the étale `S`-scheme `s`. -/
def pointSmallEtaleSelfElement :
    (pointSmallEtale s).fiber.obj (Scheme.Etale.mk s) :=
  𝟙 (CategoryTheory.Over.mk s)

/-- **An étale geometric point is an initial étale neighbourhood of itself.**  A lift of `s` to
an étale `S`-scheme `U` is itself the unique morphism of neighbourhoods from `(s, 𝟙)` to it. -/
def isInitialPointSmallEtaleSelfElement :
    IsInitial (show (pointSmallEtale s).fiber.Elements from
      ⟨Scheme.Etale.mk s, pointSmallEtaleSelfElement s⟩) := by
  apply IsInitial.ofUniqueHom
    (fun U : (pointSmallEtale s).fiber.Elements ↦
      CategoryOfElements.homMk _ U
      (MorphismProperty.Over.homMk U.2.left (CategoryTheory.Over.w U.2)) ?_)
    (fun U m ↦ ?_)
  · apply CategoryTheory.Over.OverMorphism.ext
    change (𝟙 (Spec (.of Ω))) ≫ U.2.left = U.2.left
    exact Category.id_comp _
  · apply CategoryOfElements.ext
    apply MorphismProperty.Over.Hom.ext
    exact (Category.id_comp m.1.left).symm.trans (congrArg (fun b ↦ b.left) m.2)

variable (A : Type v) [Category.{w} A] [HasColimitsOfSize.{u, u} A]

/-- The germ at `s` of a section over the étale `S`-scheme `s`, as a natural transformation in
the presheaf. -/
def sectionsToPresheafFiberSelf :
    (evaluation S.Etaleᵒᵖ A).obj (op (Scheme.Etale.mk s)) ⟶ (pointSmallEtale s).presheafFiber :=
  (pointSmallEtale s).toPresheafFiberNatTrans (Scheme.Etale.mk s) (pointSmallEtaleSelfElement s)

/-- **The stalk at an étale geometric point `s` is evaluation at the étale `S`-scheme `s`**, for
presheaves with values in any category with the relevant colimits. -/
def presheafFiberSelfIso :
    (evaluation S.Etaleᵒᵖ A).obj (op (Scheme.Etale.mk s)) ≅ (pointSmallEtale s).presheafFiber := by
  letI : ∀ P, IsIso ((sectionsToPresheafFiberSelf s A).app P) := fun P ↦
    ((pointSmallEtale s).isColimitPresheafFiberCocone P).isIso_ι_app_of_isTerminal
      (op ⟨Scheme.Etale.mk s, pointSmallEtaleSelfElement s⟩)
      (isInitialPointSmallEtaleSelfElement s).op
  letI := NatIso.isIso_of_isIso_app (sectionsToPresheafFiberSelf s A)
  exact asIso (sectionsToPresheafFiberSelf s A)

/-- The component at `P` of `presheafFiberSelfIso` is the germ at the lift
`pointSmallEtaleSelfElement s`. -/
@[simp]
lemma presheafFiberSelfIso_hom_app (P : S.Etaleᵒᵖ ⥤ A) :
    (presheafFiberSelfIso s A).hom.app P =
      (pointSmallEtale s).toPresheafFiber (Scheme.Etale.mk s) (pointSmallEtaleSelfElement s) P :=
  rfl

/-- The morphism of étale `S`-schemes from `s` to `U` given by a lift `u` of `s` to `U`. -/
abbrev pointSmallEtaleSelfHom {U : S.Etale} (u : (pointSmallEtale s).fiber.obj U) :
    Scheme.Etale.mk s ⟶ U :=
  MorphismProperty.Over.homMk u.left (CategoryTheory.Over.w u)

/-- **The germ at an étale geometric point, read on the initial neighbourhood.**  The germ of a
section over `U` at a lift `u`, transported to the value on the étale `S`-scheme `s`, is
restriction along the morphism `s ⟶ U` given by `u`. -/
lemma toPresheafFiber_comp_presheafFiberSelfIso_inv (P : S.Etaleᵒᵖ ⥤ A) (U : S.Etale)
    (u : (pointSmallEtale s).fiber.obj U) :
    (pointSmallEtale s).toPresheafFiber U u P ≫ (presheafFiberSelfIso s A).inv.app P =
      P.map (pointSmallEtaleSelfHom s u).op := by
  have hu : (pointSmallEtale s).fiber.map (pointSmallEtaleSelfHom s u)
      (pointSmallEtaleSelfElement s) = u := by
    apply CategoryTheory.Over.OverMorphism.ext
    show (𝟙 (Spec (.of Ω))) ≫ u.left = u.left
    exact Category.id_comp _
  have h := (pointSmallEtale s).toPresheafFiber_w (pointSmallEtaleSelfHom s u)
    (pointSmallEtaleSelfElement s) P
  rw [hu] at h
  rw [← h, Category.assoc, ← presheafFiberSelfIso_hom_app, Iso.hom_inv_id_app]
  exact Category.comp_id _

end Self

/-! ### Sections of an étale morphism to the spectrum of a separably closed field -/

section Sections

variable {Ω : Type u} [Field Ω] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of Ω))

/-- A section of an étale morphism is étale. -/
lemma etale_of_section [Etale f] (y : Spec (.of Ω) ⟶ Y) (hy : y ≫ f = 𝟙 _) : Etale y := by
  have : Etale (y ≫ f) := hy ▸ inferInstance
  exact Etale.of_comp y f

/-- **Two sections of an étale morphism to the spectrum of a field with the same image point are
equal.** -/
lemma eq_of_etale_section_apply_eq [Etale f] (y y' : Spec (.of Ω) ⟶ Y) (hy : y ≫ f = 𝟙 _)
    (hy' : y' ≫ f = 𝟙 _) (h : y (default : Spec (.of Ω)) = y' (default : Spec (.of Ω))) :
    y = y' := by
  have hoi : IsOpenImmersion y' := isOpenImmersion_of_etale_section f y' hy'
  have hrange : Set.range y ⊆ Set.range y' := by
    rintro _ ⟨z, rfl⟩
    exact ⟨default, by rw [Subsingleton.elim z default, h]⟩
  have hl : IsOpenImmersion.lift y' y hrange ≫ y' = y := IsOpenImmersion.lift_fac y' y hrange
  have hid : IsOpenImmersion.lift y' y hrange = 𝟙 _ := by
    have h' : IsOpenImmersion.lift y' y hrange ≫ y' ≫ f = y ≫ f := by
      rw [← Category.assoc, hl]
    rwa [hy', Category.comp_id, hy] at h'
  rw [← hl, hid, Category.id_comp]

/-- The `Ω`-points of `Y` over `Spec Ω`: the sections of `f`. -/
abbrev EtaleSections : Type u := {y : Spec (.of Ω) ⟶ Y // y ≫ f = 𝟙 _}

/-- A scheme finite over the spectrum of a field has finitely many points over it. -/
instance finite_etaleSections [IsFinite f] : Finite (EtaleSections f) :=
  finite_lifts_of_isFinite f (𝟙 _)

variable [Etale f]

/-- An `Ω`-point of `Y`, as an object of the small étale site of `Y`. -/
abbrev etaleSectionObj (y : EtaleSections f) : Y.Etale :=
  haveI := etale_of_section f y.1 y.2
  Scheme.Etale.mk y.1

/-- The `Ω`-point `y`, as a morphism of the small étale site of `Y` to its final object. -/
abbrev etaleSectionToTop (y : EtaleSections f) : etaleSectionObj f y ⟶ Scheme.Etale.mk (𝟙 Y) :=
  MorphismProperty.Over.homMk y.1 (Category.comp_id _)

end Sections

/-! ### Sheaves on a disjoint union of copies of `Spec Ω` -/

section Sheaves

variable {Ω : Type u} [Field Ω] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of Ω)) [Etale f]

/-- **Families of sections over the `Ω`-points are automatically compatible.** -/
lemma etaleSections_compatible (F : Sheaf (smallEtaleTopology Y) (Type w))
    (x : (y : EtaleSections f) → F.obj.obj (op (etaleSectionObj f y))) :
    Presieve.Arrows.Compatible F.obj (etaleSectionToTop f) x := by
  intro i j Z gi gj _
  rcases isEmpty_or_nonempty Z.left with hZ | ⟨⟨z⟩⟩
  · exact (subsingleton_sections_of_isEmpty F Z hZ).elim _ _
  · have hi : gi.left ≫ i.1 = Z.hom := CategoryTheory.Over.w gi.hom
    have hj : gj.left ≫ j.1 = Z.hom := CategoryTheory.Over.w gj.hom
    have hij : i = j := by
      apply Subtype.ext
      apply eq_of_etale_section_apply_eq f i.1 j.1 i.2 j.2
      have key : ∀ (k : EtaleSections f) (g : Z.left ⟶ Spec (.of Ω)), g ≫ k.1 = Z.hom →
          k.1 default = Z.hom z := fun k g hk =>
        (congrArg k.1 (Subsingleton.elim default (g z))).trans
          ((Scheme.Hom.comp_apply g k.1 z).symm.trans (congrArg (fun g : Z.left ⟶ Y => g z) hk))
      exact (key i gi.left hi).trans (key j gj.left hj).symm
    subst hij
    have : IsSplitMono i.1 := IsSplitMono.mk' ⟨f, i.2⟩
    obtain rfl : gi = gj := MorphismProperty.Over.Hom.ext ((cancel_mono i.1).1 (hi.trans hj.symm))
    rfl

variable [IsSepClosed Ω]

/-- The `Ω`-points of `Y` cover it in the small étale topology. -/
lemma ofArrows_etaleSectionToTop_mem :
    Sieve.ofArrows _ (etaleSectionToTop f) ∈ smallEtaleTopology Y (Scheme.Etale.mk (𝟙 Y)) := by
  rw [ofArrows_mem_smallEtaleTopology_iff]
  ext z
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  obtain ⟨l, hl, hz⟩ := exists_fac_of_etale_of_isSepClosed f (𝟙 _) z (Subsingleton.elim _ _)
  exact ⟨⟨l, hl⟩, (default : Spec (.of Ω)), hz⟩

/-- **The global sections of a sheaf of sets on a scheme étale over a separably closed field are
the product of its values on the `Ω`-points.** -/
theorem bijective_etaleSections_restriction (F : Sheaf (smallEtaleTopology Y) (Type w)) :
    Function.Bijective (fun (t : F.obj.obj (op (Scheme.Etale.mk (𝟙 Y)))) (y : EtaleSections f) =>
      F.obj.map (etaleSectionToTop f y).op t) := by
  have hP : Presieve.IsSheaf (smallEtaleTopology Y) F.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).1 F.property
  have h := (Presieve.isSheafFor_arrows_iff F.obj (etaleSectionToTop f)).1
    ((Presieve.isSheafFor_iff_generate _).2 (hP _ (ofArrows_etaleSectionToTop_mem f)))
  refine ⟨fun t₁ t₂ ht => ?_, fun x => ?_⟩
  · obtain ⟨t, _, hu⟩ := h (fun y => F.obj.map (etaleSectionToTop f y).op t₁)
      (etaleSections_compatible f F _)
    exact (hu t₁ fun _ => rfl).trans (hu t₂ fun y => (congrFun ht y).symm).symm
  · obtain ⟨t, ht, _⟩ := h x (etaleSections_compatible f F x)
    exact ⟨t, funext ht⟩

end Sheaves

/-! ### Sheaves of modules -/

section Modules

variable (Λ : Type v) [Ring Λ] {Ω : Type u} [Field Ω] [IsSepClosed Ω] {Y : Scheme.{u}}
  (f : Y ⟶ Spec (.of Ω)) [Etale f]

/-- Restriction of sections of a sheaf of modules from the final object to the `Ω`-points of `Y`,
as a linear map into the product. -/
def etaleSectionsPiRestriction (G : Sheaf (smallEtaleTopology Y) (ModuleCat.{max (u + 1) v} Λ)) :
    G.obj.obj (op (Scheme.Etale.mk (𝟙 Y))) →ₗ[Λ]
      ((y : EtaleSections f) → G.obj.obj (op (etaleSectionObj f y))) :=
  LinearMap.pi fun y => (G.obj.map (etaleSectionToTop f y).op).hom

/-- Restriction of sections of a sheaf of modules to the `Ω`-points of `Y` is bijective. -/
lemma bijective_etaleSectionsPiRestriction
    (G : Sheaf (smallEtaleTopology Y) (ModuleCat.{max (u + 1) v} Λ)) :
    Function.Bijective (etaleSectionsPiRestriction Λ f G) :=
  bijective_etaleSections_restriction f
    ((sheafCompose (smallEtaleTopology Y)
      (CategoryTheory.forget (ModuleCat.{max (u + 1) v} Λ))).obj G)

/-- **The global sections of a sheaf of modules on a scheme étale over a separably closed field
are the product of its values on the `Ω`-points.** -/
def etaleSectionsLinearEquiv (G : Sheaf (smallEtaleTopology Y) (ModuleCat.{max (u + 1) v} Λ)) :
    G.obj.obj (op (Scheme.Etale.mk (𝟙 Y))) ≃ₗ[Λ]
      ((y : EtaleSections f) → G.obj.obj (op (etaleSectionObj f y))) :=
  LinearEquiv.ofBijective _ (bijective_etaleSectionsPiRestriction Λ f G)

open Classical in
/-- The inclusion of the sections over one `Ω`-point into the global sections: extension by zero
over the other `Ω`-points. -/
def etaleSectionsInclusion (G : Sheaf (smallEtaleTopology Y) (ModuleCat.{max (u + 1) v} Λ))
    (y : EtaleSections f) :
    G.obj.obj (op (etaleSectionObj f y)) ⟶ G.obj.obj (op (Scheme.Etale.mk (𝟙 Y))) :=
  ModuleCat.ofHom ((etaleSectionsLinearEquiv Λ f G).symm.toLinearMap ∘ₗ
    LinearMap.single Λ (fun y => G.obj.obj (op (etaleSectionObj f y))) y)

omit [IsSepClosed Ω] in
/-- The component at `y` of `etaleSectionsPiRestriction` is restriction to `y`. -/
lemma etaleSectionsRestriction_apply
    (G : Sheaf (smallEtaleTopology Y) (ModuleCat.{max (u + 1) v} Λ))
    (t : G.obj.obj (op (Scheme.Etale.mk (𝟙 Y)))) (y : EtaleSections f) :
    etaleSectionsPiRestriction Λ f G t y = (G.obj.map (etaleSectionToTop f y).op).hom t :=
  rfl

open Classical in
/-- Restricting the inclusion of a section over `y` to all `Ω`-points gives `Pi.single y`. -/
lemma etaleSectionsRestriction_inclusion
    (G : Sheaf (smallEtaleTopology Y) (ModuleCat.{max (u + 1) v} Λ)) (y : EtaleSections f)
    (a : G.obj.obj (op (etaleSectionObj f y))) :
    etaleSectionsPiRestriction Λ f G ((etaleSectionsInclusion Λ f G y).hom a) = Pi.single y a := by
  show etaleSectionsLinearEquiv Λ f G ((etaleSectionsLinearEquiv Λ f G).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Restricting the inclusion of a section over `y` to the `Ω`-point `y'` is the `y'`-component of
`Pi.single y`. -/
private lemma restrict_etaleSectionsInclusion_apply [DecidableEq (EtaleSections f)]
    (G : Sheaf (smallEtaleTopology Y) (ModuleCat.{max (u + 1) v} Λ)) (y y' : EtaleSections f)
    (a : G.obj.obj (op (etaleSectionObj f y))) :
    (G.obj.map (etaleSectionToTop f y').op).hom ((etaleSectionsInclusion Λ f G y).hom a) =
      (Pi.single y a : (y : EtaleSections f) → G.obj.obj (op (etaleSectionObj f y))) y' := by
  convert congrFun (etaleSectionsRestriction_inclusion Λ f G y a) y'
  rfl

/-- The inclusion over `y` followed by restriction to `y` is the identity. -/
@[reassoc (attr := simp)]
lemma etaleSectionsInclusion_restrict_self
    (G : Sheaf (smallEtaleTopology Y) (ModuleCat.{max (u + 1) v} Λ)) (y : EtaleSections f) :
    etaleSectionsInclusion Λ f G y ≫ G.obj.map (etaleSectionToTop f y).op = 𝟙 _ := by
  classical
  ext a
  have h := restrict_etaleSectionsInclusion_apply Λ f G y y a
  rwa [Pi.single_eq_same] at h

/-- The inclusion over `y` followed by restriction to another `Ω`-point vanishes. -/
@[reassoc]
lemma etaleSectionsInclusion_restrict_of_ne
    (G : Sheaf (smallEtaleTopology Y) (ModuleCat.{max (u + 1) v} Λ)) {y y' : EtaleSections f}
    (h : y ≠ y') :
    etaleSectionsInclusion Λ f G y ≫ G.obj.map (etaleSectionToTop f y').op = 0 := by
  classical
  ext a
  have h' := restrict_etaleSectionsInclusion_apply Λ f G y y' a
  rwa [Pi.single_eq_of_ne' h] at h'

/-- **The global sections decompose as the sum over the `Ω`-points.** -/
lemma sum_etaleSections_restrict_inclusion [Fintype (EtaleSections f)]
    (G : Sheaf (smallEtaleTopology Y) (ModuleCat.{max (u + 1) v} Λ)) :
    ∑ y, G.obj.map (etaleSectionToTop f y).op ≫ etaleSectionsInclusion Λ f G y = 𝟙 _ := by
  classical
  ext t
  apply (bijective_etaleSectionsPiRestriction Λ f G).1
  funext y'
  rw [ModuleCat.hom_sum, LinearMap.sum_apply, map_sum, Finset.sum_apply,
    Finset.sum_eq_single y']
  · rw [ModuleCat.hom_comp, LinearMap.comp_apply, etaleSectionsRestriction_inclusion,
      Pi.single_eq_same, etaleSectionsRestriction_apply]
    rfl
  · intro b _ hb
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, etaleSectionsRestriction_inclusion,
      Pi.single_eq_of_ne' hb]
  · exact fun h => absurd (Finset.mem_univ y') h

/-- The inclusion is natural in the sheaf. -/
@[reassoc]
lemma etaleSectionsInclusion_naturality
    {G G' : Sheaf (smallEtaleTopology Y) (ModuleCat.{max (u + 1) v} Λ)} (φ : G ⟶ G')
    (y : EtaleSections f) :
    etaleSectionsInclusion Λ f G y ≫ φ.hom.app (op (Scheme.Etale.mk (𝟙 Y))) =
      φ.hom.app (op (etaleSectionObj f y)) ≫ etaleSectionsInclusion Λ f G' y := by
  classical
  ext a
  apply (bijective_etaleSectionsPiRestriction Λ f G').1
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
    etaleSectionsRestriction_inclusion]
  funext y'
  rw [etaleSectionsRestriction_apply]
  have hn := congrArg (fun g => g.hom ((etaleSectionsInclusion Λ f G y).hom a))
    (φ.hom.naturality (etaleSectionToTop f y').op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hn
  rw [← hn]
  rw [restrict_etaleSectionsInclusion_apply]
  by_cases hy : y = y'
  · subst hy
    simp
  · rw [Pi.single_eq_of_ne' hy, Pi.single_eq_of_ne' hy, map_zero]

end Modules

end Stacks.EtaleCohomology

end
