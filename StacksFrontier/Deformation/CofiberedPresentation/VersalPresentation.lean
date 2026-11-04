module

public import StacksFrontier.Deformation.CofiberedPresentation.Existence
public import StacksFrontier.Deformation.GroupoidQuotient.MoritaPresentation

/-!
# The groupoid in functors of a versal formal object presents the category

Let `ℱ` be a predeformation category over `𝒞_Λ` and `ξ` a versal formal object of `ℱ` over `A`.
The groupoid in functors `(A|_{𝒞_Λ}, A|_{𝒞_Λ} ×_{ξ, ℱ, ξ} A|_{𝒞_Λ}, s, t, c)` of Stacks 06KY is
smooth and presents `ℱ` (Stacks 06L1). This is the presentation of Stacks Remark 0DR3, with no
prorepresentability assumption on the functor of arrows.

## Main definitions

* `Deformation.versalGroupoid`: the groupoid in functors attached to a formal object.
* `Deformation.presentationOfIsVersal`: the groupoid of a versal formal object presents `ℱ`.

## Main results

* `Deformation.isSmooth_versalGroupoid`: the groupoid of a versal formal object is smooth.
* `Deformation.twoMul_ringKrullDim_sub_eq_of_isVersal`: for two versal formal objects whose
  functors of arrows are prorepresented, the integers `2 dim A - dim B` agree.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

universe u w uF

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k] {F : Type uF}
  [Category.{w} F]

/-- The groupoid in functors of Stacks 06KY attached to a versal formal object. -/
noncomputable abbrev versalGroupoid (p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k)
    (hp : IsPredeformationCategory.{u, w, w} p) (ξ : FormalObject p) :
    GroupoidInFunctors.{_, w, w} (ArtinianLocalAlgCat.{u, w, w} Λ k) :=
  (presentationGroupoid p (restrictedCoyoneda ξ.base)
    (associatedMorphism hp.cofibered ξ
      (chosenPushforwardsOfCofibered p hp.cofibered)).toBasedFunctor.toFunctor
    (associatedMorphism hp.cofibered ξ
      (chosenPushforwardsOfCofibered p hp.cofibered)).toBasedFunctor.w
    hp.cofibered).toGroupoidInFunctors

/-- The groupoid in functors of a versal formal object is smooth (Stacks 06L1). -/
public theorem isSmooth_versalGroupoid (p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k)
    (hp : IsPredeformationCategory.{u, w, w} p) (ξ : FormalObject p)
    (hξ : IsVersal hp.cofibered ξ) :
    GroupoidInFunctors.IsSmooth (versalGroupoid p hp ξ) :=
  isSmooth_presentationGroupoid p _ _ hp.cofibered (hξ _)

/-- The groupoid in functors of a versal formal object presents `ℱ` (Stacks 06L1). -/
public noncomputable def presentationOfIsVersal (p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k)
    (hp : IsPredeformationCategory.{u, w, w} p) (ξ : FormalObject p)
    (hξ : IsVersal hp.cofibered ξ) :
    Presentation (versalGroupoid p hp ξ) p := by
  classical
  let U := restrictedCoyoneda.{u, w, w} ξ.base
  let f := (associatedMorphism hp.cofibered ξ
    (chosenPushforwardsOfCofibered p hp.cofibered)).toBasedFunctor
  have hu₀ : Nonempty (U.obj (residueFieldObject.{u, w, w} Λ k)) :=
    ⟨(restrictedCoyoneda_isPredeformationFunctor.{u, w, w} ξ.base).some.default⟩
  let y₀ : U.Elements := ⟨residueFieldObject.{u, w, w} Λ k, hu₀.some⟩
  have h₀ : (fiberFunctor f (residueFieldObject.{u, w, w} Λ k)).EssSurj :=
    ⟨fun z => ⟨⟨y₀, rfl⟩, by
      obtain ⟨E⟩ := hp.specialFiber
      exact ⟨E.unitIso.app _ ≪≫ E.inverse.mapIso (eqToIso (Discrete.ext (Subsingleton.elim _ _))) ≪≫
        (E.unitIso.app z).symm⟩⟩⟩
  let G := presentationMorphism p U f.toFunctor f.w
    (presentationGroupoid p U f.toFunctor f.w hp.cofibered)
  have : G.1.Full := presentationMorphism_full p U f.toFunctor f.w _ hp.cofibered
  have : G.1.Faithful := presentationMorphism_faithful p U f.toFunctor f.w _
  have : G.1.EssSurj := (presentationMorphism_isEquivalence_of_isSmooth_of_fiber_essSurj
    p U f hp.cofibered (hξ _) h₀).essSurj
  exact presentationOfQuotientEquivalence _ p _ G.2.1

/-- The objects of the groupoid of a versal formal object are prorepresented by its base. -/
public noncomputable def versalGroupoidObjectsIso (p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k)
    (hp : IsPredeformationCategory.{u, w, w} p) (ξ : FormalObject p) :
    (versalGroupoid p hp ξ).objects ≅ restrictedCoyoneda ξ.base :=
  Functor.isoWhiskerLeft _ uliftFunctorTrivial ≪≫ Functor.rightUnitor _

/-- For two versal formal objects `ξ` over `A` and `ξ'` over `A'` of a predeformation category,
with rings `B` and `B'` prorepresenting the functors of arrows of their groupoids in functors, the
Krull dimensions of `A`, `B`, `A'` and `B'` are finite and
`2 dim A - dim B = 2 dim A' - dim B'`. -/
public theorem twoMul_ringKrullDim_sub_eq_of_isVersal (p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k)
    (hp : IsPredeformationCategory.{u, w, w} p) (ξ ξ' : FormalObject p)
    (hξ : IsVersal hp.cofibered ξ) (hξ' : IsVersal hp.cofibered ξ')
    (B B' : CompleteLocalAlgCat.{u, w, w} Λ k)
    (e : restrictedCoyoneda B ≅ (versalGroupoid p hp ξ).arrows)
    (e' : restrictedCoyoneda B' ≅ (versalGroupoid p hp ξ').arrows) :
    ∃ a b a' b' : ℕ, ringKrullDim ξ.base = a ∧ ringKrullDim B = b ∧ ringKrullDim ξ'.base = a' ∧
      ringKrullDim B' = b' ∧ 2 * a + b' = 2 * a' + b :=
  GroupoidInFunctors.twoMul_ringKrullDim_sub_eq_of_presentations.{u, w, w}
    (versalGroupoid p hp ξ) (versalGroupoid p hp ξ') (isSmooth_versalGroupoid p hp ξ hξ)
    (isSmooth_versalGroupoid p hp ξ' hξ') (versalGroupoidObjectsIso p hp ξ) e.symm
    (versalGroupoidObjectsIso p hp ξ') e'.symm (presentationOfIsVersal p hp ξ hξ)
    (presentationOfIsVersal p hp ξ' hξ')

end Deformation

end
