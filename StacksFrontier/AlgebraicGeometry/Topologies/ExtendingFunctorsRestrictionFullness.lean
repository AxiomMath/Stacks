module

public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsExtensionFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsRestrictionEquivalence

/-!
# The restriction functor of Stacks 0GE3 is an equivalence

Let `S` be a locally Noetherian scheme, let `τ` be one of the five topologies of
`AlgebraicGeometry.CoveringTopology` and let `Noetherian/S` be the full subcategory of `Sch/S`
whose objects are locally Noetherian. Restriction along the inclusion is a functor from the limit
preserving sheaves on `(Sch/S)_τ` to the limit preserving sheaves on the site
`(Noetherian/S)_τ`. It is faithful and essentially surjective by
`AlgebraicGeometry.ExtendingFunctors.faithful_limitPreservingRestriction` and
`AlgebraicGeometry.ExtendingFunctors.essSurj_limitPreservingRestriction`; this file supplies
fullness and assembles the three into an equivalence of categories.

Fullness is deduced from the functoriality of the extension of Stacks 0EUW: a limit preserving
sheaf on `(Sch/S)_τ` is isomorphic to the extension of its restriction, and between two
extensions every morphism of the restrictions is induced by a morphism of the extensions, because
the identification of the restriction of the extension with the functor being extended is natural
(`AlgebraicGeometry.ExtendingFunctors.whiskerLeft_extensionMap_comp_restrictionHom`).

## Main results

* `AlgebraicGeometry.ExtendingFunctors.full_limitPreservingRestriction`: the restriction functor
  is full.
* `AlgebraicGeometry.ExtendingFunctors.isEquivalence_limitPreservingRestriction_noetherian`:
  **Stacks 0GE3**, the restriction functor between the limit preserving sheaves on `(Sch/S)_τ`
  and those on `(Noetherian/S)_τ` is an equivalence.

## Implementation notes

Fullness is a property of a functor which transports along isomorphisms of the two objects
involved, and the isomorphism of a limit preserving sheaf with the extension of its restriction is
not canonical: it is extracted from the uniqueness clause of
`AlgebraicGeometry.ExtendingFunctors.exists_unique_extension`, applied twice, once to the
extension itself and once to the given sheaf. The transport is
`AlgebraicGeometry.ExtendingFunctors.exists_map_eq_of_iso`, which needs no canonicity.

## References

* [Stacks Project, Tag 0GE3](https://stacks.math.columbia.edu/tag/0GE3)
* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ExtendingFunctors

universe w u

/-! ### Fullness is tested on isomorphic objects -/

section Transport

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **Surjectivity of the action of a functor on morphisms transports along isomorphisms of the
two objects involved.** If every morphism between the images of `H₁` and `H₂` is induced by a
morphism `H₁ ⟶ H₂`, the same holds for any pair of objects isomorphic to them: conjugate the
given morphism by the images of the isomorphisms, lift it, and conjugate back. -/
theorem exists_map_eq_of_iso (R : C ⥤ D) {H₁ H₂ G₁ G₂ : C} (ε₁ : H₁ ≅ G₁) (ε₂ : H₂ ≅ G₂)
    (h : ∀ σ' : R.obj H₁ ⟶ R.obj H₂, ∃ θ' : H₁ ⟶ H₂, R.map θ' = σ')
    (σ : R.obj G₁ ⟶ R.obj G₂) : ∃ θ : G₁ ⟶ G₂, R.map θ = σ := by
  obtain ⟨θ', hθ'⟩ := h (R.map ε₁.hom ≫ σ ≫ R.map ε₂.inv)
  have hi₁ : R.map ε₁.inv ≫ R.map ε₁.hom = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  have hi₂ : R.map ε₂.inv ≫ R.map ε₂.hom = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  refine ⟨ε₁.inv ≫ θ' ≫ ε₂.hom, ?_⟩
  rw [Functor.map_comp, Functor.map_comp, hθ', Category.assoc, Category.assoc, hi₂,
    Category.comp_id, ← Category.assoc, hi₁, Category.id_comp]

end Transport

variable {S : Scheme.{u}}

/-! ### The extension of a limit preserving sheaf on the site -/

/-- **The extension of a limit preserving sheaf on the site `(𝒞)_τ` is a limit preserving sheaf on
`(Sch/S)_τ`.** This is the content of `AlgebraicGeometry.ExtendingFunctors.extension` extracted
from `AlgebraicGeometry.ExtendingFunctors.exists_isLimitPreservingSheaf_restriction`, which
reports it only as an existence statement. -/
theorem isLimitPreservingSheaf_extension (τ : CoveringTopology) {P : ObjectProperty (Over S)}
    (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))
    (hF : IsLimitPreservingSheafOnSubcategory τ P F) :
    IsLimitPreservingSheaf τ (extension P F) := by
  obtain ⟨hsF, hbF⟩ := hF
  have haF : IsZariskiSheafOnSubcategory P F :=
    isZariskiSheafOnSubcategory_of_isCoveringSheafOnSubcategory τ hP1 hsF
  exact ⟨isCoveringSheaf_extension_of_isStandardAffineSheafOnSubcategory τ P F hP1 hP2 haF hbF
      (isStandardAffineSheafOnSubcategory_of_isCoveringSheafOnSubcategory τ hsF),
    preservesAffineLimits_extension F hP1 hP2 haF⟩

/-- The restriction of a limit preserving sheaf on `(Sch/S)_τ` is a Zariski sheaf on the
subcategory. -/
private theorem isZariskiSheafOnSubcategory_restriction (τ : CoveringTopology)
    {P : ObjectProperty (Over S)} (hP1 : HasAffineOpens P) (hPp : HasCoveringPullbacks τ P)
    {G : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))} (hG : IsLimitPreservingSheaf τ G) :
    IsZariskiSheafOnSubcategory P (P.ι.op ⋙ G) :=
  isZariskiSheafOnSubcategory_of_isCoveringSheafOnSubcategory τ hP1
    (isLimitPreservingSheafOnSubcategory_restriction τ hPp hG).1

/-- **Every limit preserving sheaf on `(Sch/S)_τ` is isomorphic to the extension of its
restriction to the full subcategory.** Both the given sheaf and the extension of its restriction
satisfy the three conditions characterising the extension in Stacks 0EUW, so each is isomorphic to
the functor that statement produces. -/
theorem nonempty_iso_extension_restriction (τ : CoveringTopology) {P : ObjectProperty (Over S)}
    (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    (hPp : HasCoveringPullbacks τ P) {G : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))}
    (hG : IsLimitPreservingSheaf τ G) :
    Nonempty (extension P (P.ι.op ⋙ G) ≅ G) := by
  have haF := isZariskiSheafOnSubcategory_restriction τ hP1 hPp hG
  have hbF := (isLimitPreservingSheafOnSubcategory_restriction τ hPp hG).2
  obtain ⟨F', -, -, -, huniq⟩ := exists_unique_extension hP1 hP2 haF hbF
  obtain ⟨e₁⟩ := huniq (extension P (P.ι.op ⋙ G))
    (isZariskiSheaf_extension P _ hP1 hP2 haF)
    (preservesAffineLimits_extension _ hP1 hP2 haF)
    (nonempty_restrictionIso _ hP1 hP2 haF hbF).some
  obtain ⟨e₂⟩ := huniq G (isZariskiSheaf_of_isCoveringSheaf τ hG.1) hG.2 (Iso.refl _)
  exact ⟨e₁.symm.trans e₂⟩

/-! ### Fullness of the restriction functor -/

/-- **Fullness of the restriction functor of Stacks 0GE3.** Every morphism of limit preserving
sheaves on the site `(𝒞)_τ` between the restrictions of two limit preserving sheaves on
`(Sch/S)_τ` is the restriction of a morphism of the latter.

Both sheaves are isomorphic to the extensions of their restrictions, so by
`AlgebraicGeometry.ExtendingFunctors.exists_map_eq_of_iso` it suffices to treat two extensions,
where the morphism is transported along the natural identification of the restriction of the
extension with the functor being extended and then extended again. -/
theorem full_limitPreservingRestriction (τ : CoveringTopology) {P : ObjectProperty (Over S)}
    (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    (hPp : HasCoveringPullbacks τ P) :
    (limitPreservingRestriction (S := S) τ hPp).Full where
  map_surjective {G₁ G₂} σ := by
    have key (G : (IsLimitPreservingSheaf (S := S) τ).FullSubcategory) :
        ∃ h : IsLimitPreservingSheaf τ (extension P (P.ι.op ⋙ G.obj)),
          Nonempty ((⟨_, h⟩ : (IsLimitPreservingSheaf (S := S) τ).FullSubcategory) ≅ G) :=
      ⟨isLimitPreservingSheaf_extension τ hP1 hP2 _
        (isLimitPreservingSheafOnSubcategory_restriction τ hPp G.property),
        (nonempty_iso_extension_restriction τ hP1 hP2 hPp G.property).map
          (ObjectProperty.fullyFaithfulι _).preimageIso⟩
    obtain ⟨_, ⟨ε₁⟩⟩ := key G₁
    obtain ⟨_, ⟨ε₂⟩⟩ := key G₂
    refine exists_map_eq_of_iso (limitPreservingRestriction τ hPp) ε₁ ε₂ (fun σ' => ?_) σ
    obtain ⟨θ, hθ⟩ := exists_whiskerLeft_eq_of_extension hP1 hP2
      (isZariskiSheafOnSubcategory_restriction τ hP1 hPp G₁.property)
      (isLimitPreservingSheafOnSubcategory_restriction τ hPp G₁.property).2
      (isZariskiSheafOnSubcategory_restriction τ hP1 hPp G₂.property)
      (isLimitPreservingSheafOnSubcategory_restriction τ hPp G₂.property).2 σ'.hom
    exact ⟨ObjectProperty.homMk θ, ObjectProperty.hom_ext _ hθ⟩

/-- **Fullness of the restriction functor of Stacks 0GE3** for the locally Noetherian subcategory
of a locally Noetherian base. -/
theorem full_limitPreservingRestriction_noetherian (τ : CoveringTopology) {S : Scheme.{u}}
    [IsLocallyNoetherian S] :
    (limitPreservingRestriction (P := IsLocallyNoetherianOver (S := S)) τ
      (hasCoveringPullbacks_isLocallyNoetherianOver τ)).Full :=
  full_limitPreservingRestriction τ hasAffineOpens_isLocallyNoetherianOver
    hasFinitePresentationAffines_isLocallyNoetherianOver _

/-! ### Stacks 0GE3 -/

/-- **Stacks 0GE3.** Let `S` be a locally Noetherian scheme and let `τ` be one of the five
topologies — Zariski, étale, smooth, syntomic and fppf. Restriction along the inclusion of the
full subcategory of locally Noetherian objects of `Sch/S` is an equivalence from the category of
limit preserving sheaves on `(Sch/S)_τ` to the category of limit preserving sheaves on the site
`(Noetherian/S)_τ`.

Faithfulness is the sharp uniqueness statement of Stacks 0EUW, essential surjectivity is the
existence statement of Stacks 0EUW together with the sheaf property of the extension supplied by
Stacks 0GDW, and fullness is the functoriality of that extension. -/
@[stacks 0GE3]
theorem isEquivalence_limitPreservingRestriction_noetherian (τ : CoveringTopology)
    {S : Scheme.{u}} [IsLocallyNoetherian S] :
    (limitPreservingRestriction (P := IsLocallyNoetherianOver (S := S)) τ
      (hasCoveringPullbacks_isLocallyNoetherianOver τ)).IsEquivalence where
  faithful := faithful_limitPreservingRestriction_noetherian τ
  full := full_limitPreservingRestriction_noetherian τ
  essSurj := essSurj_limitPreservingRestriction_noetherian τ

end AlgebraicGeometry.ExtendingFunctors

end
