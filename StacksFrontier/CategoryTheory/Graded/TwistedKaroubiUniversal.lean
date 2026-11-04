module

public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiTate
public import StacksFrontier.CategoryTheory.Idempotents.KaroubiLift
public import Mathlib.CategoryTheory.Idempotents.FunctorExtension

/-!
# The universal property of the twisted Karoubi envelope

Let `C` be a category graded over `ℚ` with a graded symmetric monoidal structure, and let `L` be
a formal direct factor of the degree-zero category `DegreeZero ℚ C` whose untwisted triple
`(L, 0)` is isomorphic to the twist `T(-1) = (𝟙, 𝟙, -1)`. Then a symmetric monoidal functor `F`
from the degree-zero category to a `ℚ`-linear Karoubian symmetric monoidal category `𝒞`, such
that an image of `F` of the idempotent of `L` is invertible, extends along
`J : X ↦ (X, 1, 0)` to a symmetric monoidal functor on the twisted Karoubi envelope, and the
extension is unique up to a unique monoidal isomorphism.

This is the argument of the proof of Stacks 0FGH: first extend `F` to the formal direct factors,
`(X, p) ↦ image of F(p)`, which is possible because `𝒞` is Karoubian; then extend across the
twists, using that the image of `F` of the idempotent of `L` is invertible. The second step is
the abstract statement `CategoryTheory.InvertingObject.LinearExistence` (and
`CategoryTheory.InvertingObject.Uniqueness`) for the functor
`CategoryTheory.GradedCategory.TwistedKaroubi.untwisted`, whose hypotheses are verified in
`StacksFrontier.CategoryTheory.Graded.TwistedKaroubiTate`.

## Main definitions

* `CategoryTheory.GradedCategory.TwistedKaroubi.untwistedOfObj`: the functor `J : X ↦ (X, 1, 0)`
  from the degree-zero category.

## Main results

* `CategoryTheory.GradedCategory.TwistedKaroubi.exists_extension_of_linearExistence`: the
  extension exists, additive and `ℚ`-linear.
* `CategoryTheory.GradedCategory.TwistedKaroubi.existsUnique_iso_of_uniqueness`: it is unique up
  to a unique monoidal isomorphism compatible with the identifications along `J`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Category Idempotents Limits

namespace CategoryTheory.GradedCategory.TwistedKaroubi

universe v u v₂ u₂

variable {C : Type u} [Category.{v} C] [Preadditive C] [GradedCategory ℚ C]
  [MonoidalCategory C] [IsGradedMonoidal ℚ C] [SymmetricCategory C] [IsGradedBraided ℚ C]

variable (C) in
/-- The functor `J : X ↦ (X, 1, 0)` from the degree-zero category to the twisted Karoubi
envelope. -/
noncomputable abbrev untwistedOfObj : DegreeZero ℚ C ⥤ TwistedKaroubi ℚ C :=
  toKaroubi (DegreeZero ℚ C) ⋙ untwisted ℚ C

variable {𝒞 : Type u₂} [Category.{v₂} 𝒞] [MonoidalCategory 𝒞] [SymmetricCategory 𝒞]
  [Preadditive 𝒞] [Linear ℚ 𝒞] [IsIdempotentComplete 𝒞]
  (L : Karoubi (DegreeZero ℚ C)) (eL : (untwisted ℚ C).obj L ≅ tateTriple ℚ C (-1))

/-- An isomorphism `K ⋙ G ≅ lift F` on the formal direct factors restricts along `toKaroubi` to
an isomorphism `J ⋙ G ≅ F`. -/
private noncomputable def untwistedOfObjCompIso (F : DegreeZero ℚ C ⥤ 𝒞)
    (G : TwistedKaroubi ℚ C ⥤ 𝒞) (φ : untwisted ℚ C ⋙ G ≅ Karoubi.lift F) :
    untwistedOfObj C ⋙ G ≅ F :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (toKaroubi _) φ ≪≫
    Karoubi.toKaroubiCompLiftIso F

/-- If `φ` is monoidal, so is the isomorphism `untwistedOfObjCompIso F G φ`. -/
private instance untwistedOfObjCompIso_isMonoidal (F : DegreeZero ℚ C ⥤ 𝒞) [F.Braided]
    (G : TwistedKaroubi ℚ C ⥤ 𝒞) [G.Braided] (φ : untwisted ℚ C ⋙ G ≅ Karoubi.lift F)
    [NatTrans.IsMonoidal φ.hom] : NatTrans.IsMonoidal (untwistedOfObjCompIso F G φ).hom := by
  have := NatTrans.IsMonoidal.comp (Functor.whiskerLeft (toKaroubi (DegreeZero ℚ C)) φ.hom)
    (Karoubi.toKaroubiCompLiftIso F).hom
  exact NatTrans.IsMonoidal.comp
    (Functor.associator (toKaroubi (DegreeZero ℚ C)) (untwisted ℚ C) G).hom
    (Functor.whiskerLeft (toKaroubi (DegreeZero ℚ C)) φ.hom ≫
      (Karoubi.toKaroubiCompLiftIso F).hom)

omit [Preadditive 𝒞] [Linear ℚ 𝒞] in
include eL in
/-- **The extension across the twists exists.** If `K(L) ≅ T(-1)`, every braided functor `F` from
the degree-zero category to `𝒞`, such that an image of `F` of the idempotent of `L` is invertible,
extends along `J` to a braided functor on the twisted Karoubi envelope. -/
theorem exists_extension_of_existence
    (hE : InvertingObject.Existence 𝒞 (untwisted ℚ C) L (tateTriple ℚ C 1))
    (F : DegreeZero ℚ C ⥤ 𝒞) [F.Braided]
    (hF : ∃ (U : 𝒞) (i : U ⟶ F.obj L.X) (e : F.obj L.X ⟶ U),
      i ≫ e = 𝟙 U ∧ e ≫ i = F.map L.p ∧ IsInvertible U) :
    ∃ (G : TwistedKaroubi ℚ C ⥤ 𝒞) (_ : G.Braided) (φ : untwistedOfObj C ⋙ G ≅ F),
      NatTrans.IsMonoidal φ.hom := by
  obtain ⟨G, hGb, φ, hφ⟩ := hE (untwistedTensorTateIso L eL) braiding_tateTriple_one
    (exists_iso_untwisted_tensor_tensorPow L eL) (Karoubi.lift F)
    (Karoubi.isInvertible_lift_obj F L hF)
  exact ⟨G, hGb, untwistedOfObjCompIso F G φ, untwistedOfObjCompIso_isMonoidal F G φ⟩

include eL in
/-- **The extension across the twists exists.** If `K(L) ≅ T(-1)`, every additive braided
functor `F` from the degree-zero category to `𝒞`, such that an image of `F` of the idempotent of
`L` is invertible, extends along `J` to an additive, `ℚ`-linear braided functor on the twisted
Karoubi envelope. -/
theorem exists_extension_of_linearExistence [MonoidalPreadditive (TwistedKaroubi ℚ C)]
    [MonoidalPreadditive 𝒞]
    (hE : InvertingObject.LinearExistence 𝒞 (untwisted ℚ C) L (tateTriple ℚ C 1))
    (F : DegreeZero ℚ C ⥤ 𝒞) [F.Braided] [F.Additive]
    (hF : ∃ (U : 𝒞) (i : U ⟶ F.obj L.X) (e : F.obj L.X ⟶ U),
      i ≫ e = 𝟙 U ∧ e ≫ i = F.map L.p ∧ IsInvertible U) :
    ∃ (G : TwistedKaroubi ℚ C ⥤ 𝒞) (_ : G.Braided) (_ : G.Additive) (_ : Functor.Linear ℚ G)
      (φ : untwistedOfObj C ⋙ G ≅ F), NatTrans.IsMonoidal φ.hom := by
  obtain ⟨G, hGb, hGa, hGl, φ, hφ⟩ := hE (untwistedTensorTateIso L eL) braiding_tateTriple_one
    (exists_iso_untwisted_tensor_tensorPow L eL) (Karoubi.lift F)
    (Karoubi.isInvertible_lift_obj F L hF)
  exact ⟨G, hGb, hGa, hGl, untwistedOfObjCompIso F G φ, untwistedOfObjCompIso_isMonoidal F G φ⟩

/-- An isomorphism `J ⋙ G ≅ F`, for `G` on the twisted Karoubi envelope, as an isomorphism
`K ⋙ G ≅ lift F` on the formal direct factors: the unique one whose restriction along `toKaroubi`
is the given one. -/
noncomputable def untwistedCompIsoLift (F : DegreeZero ℚ C ⥤ 𝒞) (G : TwistedKaroubi ℚ C ⥤ 𝒞)
    (φ : untwistedOfObj C ⋙ G ≅ F) : untwisted ℚ C ⋙ G ≅ Karoubi.lift F :=
  (whiskeringLeftObjToKaroubiFullyFaithful (C := DegreeZero ℚ C) (D := 𝒞)).preimageIso
    ((Functor.associator _ _ _).symm ≪≫ φ ≪≫ (Karoubi.toKaroubiCompLiftIso F).symm)

omit [MonoidalCategory C] [IsGradedMonoidal ℚ C] [SymmetricCategory C] [IsGradedBraided ℚ C]
  [MonoidalCategory 𝒞] [SymmetricCategory 𝒞] [Preadditive 𝒞] [Linear ℚ 𝒞] in
/-- The restriction along `toKaroubi` of `untwistedCompIsoLift F G φ` is `φ`, up to the
identifications `Functor.associator` and `Karoubi.toKaroubiCompLiftIso F`. -/
private theorem whiskerLeft_untwistedCompIsoLift_hom (F : DegreeZero ℚ C ⥤ 𝒞)
    (G : TwistedKaroubi ℚ C ⥤ 𝒞) (φ : untwistedOfObj C ⋙ G ≅ F) :
    Functor.whiskerLeft (toKaroubi (DegreeZero ℚ C)) (untwistedCompIsoLift F G φ).hom =
      (Functor.associator (toKaroubi (DegreeZero ℚ C)) (untwisted ℚ C) G).inv ≫
        φ.hom ≫ (Karoubi.toKaroubiCompLiftIso F).inv :=
  (whiskeringLeftObjToKaroubiFullyFaithful (C := DegreeZero ℚ C) (D := 𝒞)).map_preimage
    ((Functor.associator _ _ _).symm ≪≫ φ ≪≫ (Karoubi.toKaroubiCompLiftIso F).symm).hom

omit [MonoidalCategory C] [IsGradedMonoidal ℚ C] [SymmetricCategory C] [IsGradedBraided ℚ C]
  [MonoidalCategory 𝒞] [SymmetricCategory 𝒞] [Preadditive 𝒞] [Linear ℚ 𝒞] in
/-- On the image under `toKaroubi` of an object `X`, the component of `untwistedCompIsoLift F G φ`
is that of `φ` followed by the inverse of `Karoubi.toKaroubiCompLiftIso F`. -/
theorem untwistedCompIsoLift_hom_app (F : DegreeZero ℚ C ⥤ 𝒞) (G : TwistedKaroubi ℚ C ⥤ 𝒞)
    (φ : untwistedOfObj C ⋙ G ≅ F) (X : DegreeZero ℚ C) :
    (untwistedCompIsoLift F G φ).hom.app ((toKaroubi _).obj X) =
      φ.hom.app X ≫ (Karoubi.toKaroubiCompLiftIso F).inv.app X := by
  have := NatTrans.congr_app (whiskerLeft_untwistedCompIsoLift_hom F G φ) X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app] at this
  exact this.trans (id_comp _)

/-- If `φ` is monoidal, so is the isomorphism `untwistedCompIsoLift F G φ`. -/
instance untwistedCompIsoLift_isMonoidal (F : DegreeZero ℚ C ⥤ 𝒞) [F.Braided]
    (G : TwistedKaroubi ℚ C ⥤ 𝒞) [G.Braided] (φ : untwistedOfObj C ⋙ G ≅ F)
    [NatTrans.IsMonoidal φ.hom] : NatTrans.IsMonoidal (untwistedCompIsoLift F G φ).hom := by
  have := NatTrans.IsMonoidal.comp φ.hom (Karoubi.toKaroubiCompLiftIso F).inv
  have := NatTrans.IsMonoidal.comp
    (Functor.associator (toKaroubi (DegreeZero ℚ C)) (untwisted ℚ C) G).inv
    (φ.hom ≫ (Karoubi.toKaroubiCompLiftIso F).inv)
  rw [← whiskerLeft_untwistedCompIsoLift_hom F G φ] at this
  exact Karoubi.isMonoidal_of_whiskerLeft_toKaroubi _

omit [MonoidalCategory C] [IsGradedMonoidal ℚ C] [SymmetricCategory C] [IsGradedBraided ℚ C]
  [MonoidalCategory 𝒞] [SymmetricCategory 𝒞] [Preadditive 𝒞] [Linear ℚ 𝒞] in
/-- A natural transformation `θ : G₁ ⟶ G₂` is compatible with `untwistedCompIsoLift F Gᵢ φᵢ`
along `K` if and only if it is compatible with the `φᵢ` along `J`. -/
private theorem whiskerLeft_comp_untwistedCompIsoLift_iff (F : DegreeZero ℚ C ⥤ 𝒞)
    {G₁ G₂ : TwistedKaroubi ℚ C ⥤ 𝒞} (φ₁ : untwistedOfObj C ⋙ G₁ ≅ F)
    (φ₂ : untwistedOfObj C ⋙ G₂ ≅ F) (θ : G₁ ⟶ G₂) :
    Functor.whiskerLeft (untwisted ℚ C) θ ≫ (untwistedCompIsoLift F G₂ φ₂).hom =
        (untwistedCompIsoLift F G₁ φ₁).hom ↔
      Functor.whiskerLeft (untwistedOfObj C) θ ≫ φ₂.hom = φ₁.hom := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext X
    have := congrArg (fun τ ↦ NatTrans.app τ ((toKaroubi _).obj X)) h
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, untwistedCompIsoLift_hom_app] at this
    simpa using congrArg (· ≫ (Karoubi.toKaroubiCompLiftIso F).hom.app X) this
  · apply (whiskeringLeftObjToKaroubiFullyFaithful (C := DegreeZero ℚ C) (D := 𝒞)).map_injective
    ext X
    have := congrArg (fun τ ↦ NatTrans.app τ X) h
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at this
    simp only [Functor.whiskeringLeft_obj_map, NatTrans.comp_app, Functor.whiskerLeft_app,
      untwistedCompIsoLift_hom_app]
    rw [← this, assoc]
    rfl

omit [Preadditive 𝒞] [Linear ℚ 𝒞] in
include eL in
/-- **The extension across the twists is unique up to a unique isomorphism.** If `K(L) ≅ T(-1)`,
two braided extensions `G₁`, `G₂` of a braided functor `F` along `J`, with monoidal isomorphisms
`φᵢ : J ⋙ Gᵢ ≅ F`, are related by a unique monoidal isomorphism `θ : G₁ ≅ G₂` compatible with
the `φᵢ`. -/
theorem existsUnique_iso_of_uniqueness
    (hU : InvertingObject.Uniqueness 𝒞 (untwisted ℚ C) L (tateTriple ℚ C 1))
    (F : DegreeZero ℚ C ⥤ 𝒞) [F.Braided] (G₁ G₂ : TwistedKaroubi ℚ C ⥤ 𝒞) [G₁.Braided]
    [G₂.Braided] (φ₁ : untwistedOfObj C ⋙ G₁ ≅ F) (φ₂ : untwistedOfObj C ⋙ G₂ ≅ F)
    [NatTrans.IsMonoidal φ₁.hom] [NatTrans.IsMonoidal φ₂.hom] :
    ∃! θ : G₁ ≅ G₂, NatTrans.IsMonoidal θ.hom ∧
      Functor.whiskerLeft (untwistedOfObj C) θ.hom ≫ φ₂.hom = φ₁.hom := by
  obtain ⟨θ, ⟨hθm, hθ⟩, huniq⟩ := hU (untwistedTensorTateIso L eL)
    (exists_iso_untwisted_tensor_tensorPow L eL) (Karoubi.lift F) G₁ G₂
    (untwistedCompIsoLift F G₁ φ₁) (untwistedCompIsoLift F G₂ φ₂)
  exact ⟨θ, ⟨hθm, (whiskerLeft_comp_untwistedCompIsoLift_iff F φ₁ φ₂ θ.hom).1 hθ⟩,
    fun θ' ⟨hθ'm, hθ'⟩ ↦
      huniq θ' ⟨hθ'm, (whiskerLeft_comp_untwistedCompIsoLift_iff F φ₁ φ₂ θ'.hom).2 hθ'⟩⟩

end CategoryTheory.GradedCategory.TwistedKaroubi
