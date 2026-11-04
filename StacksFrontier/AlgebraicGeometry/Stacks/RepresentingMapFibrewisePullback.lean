module

public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpaceSections
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal

/-!
# A fibrewise criterion for cartesian squares of representing presheaves

Let `𝒜`, `ℬ`, `𝒞`, `𝒟` be categories fibred in groupoids over the big fppf site of `S`, each
equivalent over the site to the category of elements of a presheaf `A`, `B`, `C`, `D` of sets, and
let `fa : 𝒜 ⟶ ℬ`, `fb : 𝒜 ⟶ 𝒞`, `fc : ℬ ⟶ 𝒟`, `fd : 𝒞 ⟶ 𝒟` be 1-morphisms. Stacks 04SW turns
them into morphisms of presheaves `A ⟶ B`, `A ⟶ C`, `B ⟶ D`, `C ⟶ D`. This file shows that the
resulting square of presheaves is cartesian as soon as, over every object `W` of the site,

* the two composites agree up to a vertical morphism,
* every pair of objects `y` of `ℬ` and `z` of `𝒞` over `W` with `fc y` and `fd z` related by a
  vertical morphism is, up to vertical morphisms, the image of an object of `𝒜` over `W`, and
* two objects of `𝒜` over `W` whose images in `ℬ` and in `𝒞` are related by vertical morphisms
  are related by a vertical morphism.

Since a section of a representing presheaf over `W` is the same as an isomorphism class of the
fibre over `W` (`CategoryTheory.PresheafOfCategories.isoClassSectionEquiv`), these three
conditions say exactly that the square is cartesian on sections over `W`.

## Main results

* `AlgebraicGeometry.Stack.representingMap_comp_eq_of_fibrewise`: commutativity of the square of
  representing maps from vertical morphisms between the two composites.
* `AlgebraicGeometry.Stack.isPullback_representingMap_of_fibrewise`: the criterion.
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒜 ℬ 𝒞 𝒟 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {A B' C D : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (eA : StacksRepresentableCFG.EquivalenceOver 𝒜.val.p (presheafOfCategories (A ⋙ typeToCat)).p)
  (eB : StacksRepresentableCFG.EquivalenceOver ℬ.val.p
    (presheafOfCategories (B' ⋙ typeToCat)).p)
  (eC : StacksRepresentableCFG.EquivalenceOver 𝒞.val.p (presheafOfCategories (C ⋙ typeToCat)).p)
  (eD : StacksRepresentableCFG.EquivalenceOver 𝒟.val.p (presheafOfCategories (D ⋙ typeToCat)).p)

/-- The section named by the image of an object under a 1-morphism is the image under the
representing map of the section named by the object (Stacks 04SW on sections). -/
theorem representingMap_app_sectionOfObj (f : 𝒜 ⟶ ℬ) (z : 𝒜.val.obj) {W : BigFppfOver B S hS}
    (hz : 𝒜.val.p.obj z = W) :
    (representingMap B S hS 𝒜 ℬ A B' eA eB f).app (op W)
        (PresheafOfCategories.sectionOfObj eA z hz) =
      PresheafOfCategories.sectionOfObj eB ((CatFiberedInGroupoids.homFunctor f).obj z)
        ((Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p f) z).trans hz) :=
  morphismSpaceEquiv_app_sectionOfObj B S hS 𝒜 ℬ A B' eA eB _ z hz

/-- If the representing map sends the sections named by `a'` and `a` to the same section, the
images of `a'` and `a` are related by a morphism over an identity. -/
private theorem exists_lift_of_representingMap_app_eq (f : 𝒜 ⟶ ℬ) {a a' : 𝒜.val.obj}
    {W : BigFppfOver B S hS} (ha' : 𝒜.val.p.obj a' = W) (ha : 𝒜.val.p.obj a = W)
    (h : (representingMap B S hS 𝒜 ℬ A B' eA eB f).app (op W)
        (PresheafOfCategories.sectionOfObj eA a' ha') =
      (representingMap B S hS 𝒜 ℬ A B' eA eB f).app (op W)
        (PresheafOfCategories.sectionOfObj eA a ha)) :
    ∃ ψ : (CatFiberedInGroupoids.homFunctor f).obj a' ⟶
      (CatFiberedInGroupoids.homFunctor f).obj a, ℬ.val.p.IsHomLift (𝟙 W) ψ := by
  rw [representingMap_app_sectionOfObj, representingMap_app_sectionOfObj] at h
  let e := PresheafOfCategories.fiberIsoOfSectionOfObj_eq eB _ _ h
  exact ⟨e.hom.1, e.hom.2⟩

/-- **Commutativity on sections.** If for every object `z` of `𝒜` the two images of `z` in `𝒟`
are related by a morphism lying over an identity, then the two composites of representing maps
agree. -/
theorem representingMap_comp_eq_of_fibrewise (fa : 𝒜 ⟶ ℬ) (fb : 𝒜 ⟶ 𝒞) (fc : ℬ ⟶ 𝒟)
    (fd : 𝒞 ⟶ 𝒟)
    (hcomm : ∀ (z : 𝒜.val.obj) (W : BigFppfOver B S hS), 𝒜.val.p.obj z = W →
      ∃ φ : (CatFiberedInGroupoids.homFunctor fc).obj
          ((CatFiberedInGroupoids.homFunctor fa).obj z) ⟶
        (CatFiberedInGroupoids.homFunctor fd).obj ((CatFiberedInGroupoids.homFunctor fb).obj z),
        𝒟.val.p.IsHomLift (𝟙 W) φ) :
    representingMap B S hS 𝒜 ℬ A B' eA eB fa ≫ representingMap B S hS ℬ 𝒟 B' D eB eD fc =
      representingMap B S hS 𝒜 𝒞 A C eA eC fb ≫ representingMap B S hS 𝒞 𝒟 C D eC eD fd := by
  refine natTrans_eq_of_forall_sectionOfObj B S hS 𝒜 A D eA _ _ (fun z W hz => ?_)
  obtain ⟨φ, hφ⟩ := hcomm z W hz
  simp only [NatTrans.comp_app, types_comp_apply, representingMap_app_sectionOfObj]
  exact PresheafOfCategories.sectionOfObj_eq_of_hom eD _ _ φ hφ

/-- **The fibrewise criterion for a cartesian square of representing maps.** -/
theorem isPullback_representingMap_of_fibrewise (fa : 𝒜 ⟶ ℬ) (fb : 𝒜 ⟶ 𝒞) (fc : ℬ ⟶ 𝒟)
    (fd : 𝒞 ⟶ 𝒟)
    (hcomm : ∀ (z : 𝒜.val.obj) (W : BigFppfOver B S hS), 𝒜.val.p.obj z = W →
      ∃ φ : (CatFiberedInGroupoids.homFunctor fc).obj
          ((CatFiberedInGroupoids.homFunctor fa).obj z) ⟶
        (CatFiberedInGroupoids.homFunctor fd).obj ((CatFiberedInGroupoids.homFunctor fb).obj z),
        𝒟.val.p.IsHomLift (𝟙 W) φ)
    (hsurj : ∀ (W : BigFppfOver B S hS) (y : ℬ.val.obj) (z : 𝒞.val.obj),
      ℬ.val.p.obj y = W → 𝒞.val.p.obj z = W →
      ∀ φ : (CatFiberedInGroupoids.homFunctor fc).obj y ⟶
          (CatFiberedInGroupoids.homFunctor fd).obj z, 𝒟.val.p.IsHomLift (𝟙 W) φ →
      ∃ (a : 𝒜.val.obj) (_ : 𝒜.val.p.obj a = W)
        (ψ : (CatFiberedInGroupoids.homFunctor fa).obj a ⟶ y)
        (χ : (CatFiberedInGroupoids.homFunctor fb).obj a ⟶ z),
        ℬ.val.p.IsHomLift (𝟙 W) ψ ∧ 𝒞.val.p.IsHomLift (𝟙 W) χ)
    (hinj : ∀ (W : BigFppfOver B S hS) (a a' : 𝒜.val.obj),
      𝒜.val.p.obj a = W → 𝒜.val.p.obj a' = W →
      ∀ (ψ : (CatFiberedInGroupoids.homFunctor fa).obj a ⟶
          (CatFiberedInGroupoids.homFunctor fa).obj a')
        (χ : (CatFiberedInGroupoids.homFunctor fb).obj a ⟶
          (CatFiberedInGroupoids.homFunctor fb).obj a'),
        ℬ.val.p.IsHomLift (𝟙 W) ψ → 𝒞.val.p.IsHomLift (𝟙 W) χ →
      ∃ θ : a ⟶ a', 𝒜.val.p.IsHomLift (𝟙 W) θ) :
    IsPullback (representingMap B S hS 𝒜 ℬ A B' eA eB fa)
      (representingMap B S hS 𝒜 𝒞 A C eA eC fb)
      (representingMap B S hS ℬ 𝒟 B' D eB eD fc)
      (representingMap B S hS 𝒞 𝒟 C D eC eD fd) := by
  refine CategoryTheory.isPullback_of_existsUnique_app
    (representingMap_comp_eq_of_fibrewise eA eB eC eD fa fb fc fd hcomm) ?_
  intro V x₂ x₃ hx
  obtain ⟨y, hy, rfl⟩ := PresheafOfCategories.exists_sectionOfObj eB (W := V.unop) x₂
  obtain ⟨z, hz, rfl⟩ := PresheafOfCategories.exists_sectionOfObj eC (W := V.unop) x₃
  rw [representingMap_app_sectionOfObj, representingMap_app_sectionOfObj] at hx
  let φ := PresheafOfCategories.fiberIsoOfSectionOfObj_eq eD _ _ hx
  obtain ⟨a, ha, ψ, χ, hψ, hχ⟩ := hsurj V.unop y z hy hz φ.hom.1 φ.hom.2
  have h₁ := (representingMap_app_sectionOfObj eA eB fa a ha).trans
    (PresheafOfCategories.sectionOfObj_eq_of_hom eB _ hy ψ hψ)
  have h₂ := (representingMap_app_sectionOfObj eA eC fb a ha).trans
    (PresheafOfCategories.sectionOfObj_eq_of_hom eC _ hz χ hχ)
  refine ⟨PresheafOfCategories.sectionOfObj eA a ha, ⟨h₁, h₂⟩, ?_⟩
  rintro x₁ ⟨h₁', h₂'⟩
  obtain ⟨a', ha', rfl⟩ := PresheafOfCategories.exists_sectionOfObj eA (W := V.unop) x₁
  obtain ⟨ψ', hψ'⟩ := exists_lift_of_representingMap_app_eq eA eB fa ha' ha (h₁'.trans h₁.symm)
  obtain ⟨χ', hχ'⟩ := exists_lift_of_representingMap_app_eq eA eC fb ha' ha (h₂'.trans h₂.symm)
  obtain ⟨θ, hθ⟩ := hinj V.unop a' a ha' ha ψ' χ' hψ' hχ'
  exact PresheafOfCategories.sectionOfObj_eq_of_hom eA _ _ θ hθ

end AlgebraicGeometry.Stack

end
