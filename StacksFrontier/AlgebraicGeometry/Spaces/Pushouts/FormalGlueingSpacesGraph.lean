module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria

/-!
# The hom-set bijection of Stacks 0AF6, reduced to the essential surjectivity of Stacks 0AF4

In a formal glueing situation the restriction functor `F` of Stacks 0AF3 induces a map
`Mor_X(X'₁, X'₂) ⟶ Mor_{Spaces(Y → X, Z)}(F X'₁, F X'₂)`. For `X'₂ ⟶ X` separated this map is
surjective, hence bijective, given the essential surjectivity of Stacks 0AF4 part (2) in the
slice over a space `Q` over `X`: a morphism of glueing data into the restriction of `Q` whose
components are closed immersions comes from a space over `Q`.

## Main results

* `AlgebraicGeometry.Space.exists_map_eq_of_graph`: the graph criterion, for a functor that
  reflects isomorphisms.
* `AlgebraicGeometry.Space.FormalGlueingSituation.exists_lift_formalGlueingFunctor`: the
  restriction functor of Stacks 0AF3 preserves fibre products.
* `AlgebraicGeometry.Space.FormalGlueingSituation.exists_map_eq_of_essSurj_closedImmersion`:
  surjectivity of the map on hom-sets, given the essential surjectivity above.
* `…FormalGlueingSituation.bijective_formalGlueingFunctor_map_of_essSurj_closedImmersion`: the
  bijection of Stacks 0AF6, given the same input.

## References

* [Stacks Project, Tag 03KL](https://stacks.math.columbia.edu/tag/03KL)
* [Stacks Project, Tag 03KP](https://stacks.math.columbia.edu/tag/03KP)
* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
* [Stacks Project, Tag 0AF3](https://stacks.math.columbia.edu/tag/0AF3)
* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
* [Stacks Project, Tag 0AF5](https://stacks.math.columbia.edu/tag/0AF5)
* [Stacks Project, Tag 0AF6](https://stacks.math.columbia.edu/tag/0AF6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- The graph criterion for a functor that reflects isomorphisms. Let `p₁ : Q ⟶ A` and
`p₂ : Q ⟶ Bb` be a pair of morphisms, let `k : T ⟶ Q`, and let `φ : F.obj A ⟶ F.obj Bb`.
Suppose `F.map k` is the graph of `φ` along an isomorphism `θ : F.obj T ≅ F.obj A`, meaning
that `F` sends `k ≫ p₁` to `θ.hom` and `k ≫ p₂` to `θ.hom ≫ φ`. If `F` reflects isomorphisms
then `φ` is the image of a morphism `A ⟶ Bb`. -/
theorem exists_map_eq_of_graph {C E : Type*} [Category C] [Category E] (F : C ⥤ E)
    [F.ReflectsIsomorphisms] {A Bb T Q : C} (p₁ : Q ⟶ A) (p₂ : Q ⟶ Bb) (k : T ⟶ Q)
    {φ : F.obj A ⟶ F.obj Bb} (θ : F.obj T ≅ F.obj A)
    (h₁ : F.map (k ≫ p₁) = θ.hom) (h₂ : F.map (k ≫ p₂) = θ.hom ≫ φ) :
    ∃ a : A ⟶ Bb, F.map a = φ := by
  have hFiso : IsIso (F.map (k ≫ p₁)) := by rw [h₁]; infer_instance
  have hiso : IsIso (k ≫ p₁) := isIso_of_reflects_iso _ F
  have hunit : F.map (inv (k ≫ p₁)) ≫ θ.hom = 𝟙 (F.obj A) := by
    rw [← h₁, ← F.map_comp, IsIso.inv_hom_id, F.map_id]
  have hinv : F.map (inv (k ≫ p₁)) = θ.inv := by
    rw [← Category.comp_id (F.map (inv (k ≫ p₁))), ← θ.hom_inv_id, ← Category.assoc,
      hunit, Category.id_comp]
  exact ⟨inv (k ≫ p₁) ≫ k ≫ p₂, by rw [F.map_comp, hinv, h₂, Iso.inv_hom_id_assoc]⟩

/-- Base change along `g` preserves binary products. -/
private theorem preservesBinaryProducts_overPullback {C : Type*} [Category C]
    [HasPullbacks C] {X W : C} (g : W ⟶ X) :
    PreservesLimitsOfShape (Discrete WalkingPair) (Over.pullback g) :=
  (Over.mapPullbackAdj g).rightAdjoint_preservesLimits.preservesLimitsOfShape

/-- The fibre product of two objects of `Over X` is their binary product. -/
noncomputable def overProdIsLimit {C : Type*} [Category C] [HasPullbacks C] {X : C}
    (A Bb : Over X) :
    IsLimit (BinaryFan.mk
      (Over.homMk (pullback.fst A.hom Bb.hom) rfl :
        Over.mk (pullback.fst A.hom Bb.hom ≫ A.hom) ⟶ A)
      (Over.homMk (pullback.snd A.hom Bb.hom) pullback.condition.symm :
        Over.mk (pullback.fst A.hom Bb.hom ≫ A.hom) ⟶ Bb)) :=
  BinaryFan.isLimitMk
    (fun s => Over.homMk
      (pullback.lift s.fst.left s.snd.left ((Over.w s.fst).trans (Over.w s.snd).symm))
      ((Category.assoc _ _ _).symm.trans (by rw [pullback.lift_fst]; exact Over.w s.fst)))
    (fun s => Over.OverMorphism.ext (pullback.lift_fst _ _ _))
    (fun s => Over.OverMorphism.ext (pullback.lift_snd _ _ _))
    (fun s m h₁ h₂ => Over.OverMorphism.ext
      (pullback.hom_ext
        ((congrArg Over.Hom.left h₁).trans (pullback.lift_fst _ _ _).symm)
        ((congrArg Over.Hom.left h₂).trans (pullback.lift_snd _ _ _).symm)))

/-- A comma-valued diagram built from two product-preserving functors preserves binary
products. Let `α : P ⋙ L ⟶ Q ⋙ R` be a natural transformation, so that `A ↦ ⟨P A, Q A, α A⟩`
is a functor into `Comma L R`, and let `Z` with `p₁, p₂` be a binary product of `A₁` and `A₂`.
A pair of morphisms of `Comma L R` out of a common `G`, into the images of `A₁` and of `A₂`,
then lifts to a morphism into the image of `Z`. -/
private theorem exists_lift_comma {E A₀ Bb₀ T₀ : Type*} [Category E] [Category A₀] [Category Bb₀]
    [Category T₀] {L : A₀ ⥤ T₀} {R : Bb₀ ⥤ T₀} (P : E ⥤ A₀) (Q : E ⥤ Bb₀) (α : P ⋙ L ⟶ Q ⋙ R)
    [PreservesLimitsOfShape (Discrete WalkingPair) P]
    [PreservesLimitsOfShape (Discrete WalkingPair) Q]
    [PreservesLimitsOfShape (Discrete WalkingPair) R]
    {A₁ A₂ Z : E} (p₁ : Z ⟶ A₁) (p₂ : Z ⟶ A₂) (hZ : IsLimit (BinaryFan.mk p₁ p₂))
    (G : Comma L R)
    (ul : G.left ⟶ P.obj A₁) (ur : G.right ⟶ Q.obj A₁)
    (hu : L.map ul ≫ α.app A₁ = G.hom ≫ R.map ur)
    (vl : G.left ⟶ P.obj A₂) (vr : G.right ⟶ Q.obj A₂)
    (hv : L.map vl ≫ α.app A₂ = G.hom ≫ R.map vr) :
    ∃ (wl : G.left ⟶ P.obj Z) (wr : G.right ⟶ Q.obj Z),
      (L.map wl ≫ α.app Z = G.hom ≫ R.map wr) ∧
        wl ≫ P.map p₁ = ul ∧ wr ≫ Q.map p₁ = ur ∧
          wl ≫ P.map p₂ = vl ∧ wr ≫ Q.map p₂ = vr := by
  have hP := (isLimitMapConeBinaryFanEquiv P p₁ p₂) (isLimitOfPreserves P hZ)
  have hQ := (isLimitMapConeBinaryFanEquiv Q p₁ p₂) (isLimitOfPreserves Q hZ)
  have hQR := (isLimitMapConeBinaryFanEquiv (Q ⋙ R) p₁ p₂) (isLimitOfPreserves (Q ⋙ R) hZ)
  obtain ⟨wl, hwl₁, hwl₂⟩ : ∃ wl : G.left ⟶ P.obj Z,
      wl ≫ P.map p₁ = ul ∧ wl ≫ P.map p₂ = vl :=
    ⟨_, (BinaryFan.IsLimit.lift' hP ul vl).2⟩
  obtain ⟨wr, hwr₁, hwr₂⟩ : ∃ wr : G.right ⟶ Q.obj Z,
      wr ≫ Q.map p₁ = ur ∧ wr ≫ Q.map p₂ = vr :=
    ⟨_, (BinaryFan.IsLimit.lift' hQ ur vr).2⟩
  have key : ∀ {A' : E} (p : Z ⟶ A') (l : G.left ⟶ P.obj A') (r : G.right ⟶ Q.obj A'),
      L.map l ≫ α.app A' = G.hom ≫ R.map r → wl ≫ P.map p = l → wr ≫ Q.map p = r →
        (L.map wl ≫ α.app Z) ≫ R.map (Q.map p) = (G.hom ≫ R.map wr) ≫ R.map (Q.map p) := by
    intro A' p l r h hl hr
    have hnat : L.map (P.map p) ≫ α.app A' = α.app Z ≫ R.map (Q.map p) := α.naturality p
    rw [Category.assoc, Category.assoc, ← hnat, ← Category.assoc, ← Functor.map_comp, hl, h,
      ← Functor.map_comp, hr]
  exact ⟨wl, wr, BinaryFan.IsLimit.hom_ext hQR (key p₁ ul ur hu hwl₁ hwr₁)
    (key p₂ vl vr hv hwl₂ hwr₂), hwl₁, hwr₁, hwl₂, hwr₂⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Restriction along `g` of a morphism of `Over X` is the base change of that morphism along
the projection: the square comparing the two first projections is cartesian. -/
theorem isPullback_overPullback_map_left {C : Type*} [Category C] [HasPullbacks C]
    {X W : C} (g : W ⟶ X) {A Bb : Over X} (φ : A ⟶ Bb) :
    IsPullback ((Over.pullback g).map φ).left (pullback.fst A.hom g)
      (pullback.fst Bb.hom g) φ.left :=
  IsPullback.of_right
    (by
      rw [FormalGlueingSituation.overPullback_map_left_comp_snd g φ, Over.w φ]
      exact (IsPullback.of_hasPullback A.hom g).flip)
    (FormalGlueingSituation.overPullback_map_left_comp_fst g φ)
    (IsPullback.of_hasPullback Bb.hom g).flip

/-- A morphism sitting in a cartesian square over a separated morphism is separated. -/
theorem isSeparated_of_isPullback {X Y X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : X' ⟶ X} {b : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (hpb : IsPullback a b f g)
    (hf : IsSeparated B S hS f) : IsSeparated B S hS b := by
  have hbc := isClosedImmersion_isStableUnderBaseChange B S hS
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (MorphismProperty.IsStableUnderBaseChange.diagonal
    (P := MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))).of_isPullback hpb hf

namespace FormalGlueingSituation

variable {B S hS}

/-- The restriction functor preserves fibre products: given a pair of morphisms
`u : G ⟶ F X₁`, `v : G ⟶ F X₂` of glueing data out of a common source, and a fibre product
`X₁ ×_X X₂` of the two spaces over `X`, there is a morphism `G ⟶ F (X₁ ×_X X₂)` with components
`u` and `v`. -/
theorem exists_lift_formalGlueingFunctor (D : FormalGlueingSituation B S hS)
    {X₁ X₂ Q : spacesOverX D} (p₁ : Q ⟶ X₁) (p₂ : Q ⟶ X₂)
    (hQ : IsLimit (BinaryFan.mk p₁.hom p₂.hom)) (G : glueingData D)
    (u : G ⟶ (formalGlueingFunctor D).1.obj X₁)
    (v : G ⟶ (formalGlueingFunctor D).1.obj X₂) :
    ∃ w : G ⟶ (formalGlueingFunctor D).1.obj Q,
      w ≫ (formalGlueingFunctor D).1.map p₁ = u ∧
        w ≫ (formalGlueingFunctor D).1.map p₂ = v := by
  have := preservesBinaryProducts_overPullback D.U.ι
  have := preservesBinaryProducts_overPullback D.f
  have := preservesBinaryProducts_overPullback D.V.ι
  obtain ⟨wl, wr, hw, hwl₁, hwr₁, hwl₂, hwr₂⟩ :=
    exists_lift_comma (Over.pullback D.U.ι) (Over.pullback D.f) (restrictionComparison D).hom
      p₁.hom p₂.hom hQ G.obj u.hom.left u.hom.right u.hom.w v.hom.left v.hom.right v.hom.w
  exact ⟨⟨{ left := wl, right := wr, w := hw }⟩,
    ObjectProperty.hom_ext _ (Comma.hom_ext _ _ hwl₁ hwr₁),
    ObjectProperty.hom_ext _ (Comma.hom_ext _ _ hwl₂ hwr₂)⟩

/-- The graph criterion for the restriction functor `F` of Stacks 0AF3: if `F` sends `k ≫ p₁`
to `θ.hom` and `k ≫ p₂` to `θ.hom ≫ φ` for an isomorphism `θ : F T ≅ F X₁`, then `φ` is the
image of a morphism `X₁ ⟶ X₂`. -/
theorem exists_map_eq_of_graph_formalGlueingFunctor (D : FormalGlueingSituation B S hS)
    {X₁ X₂ T Q : spacesOverX D} (p₁ : Q ⟶ X₁) (p₂ : Q ⟶ X₂) (k : T ⟶ Q)
    {φ : (formalGlueingFunctor D).1.obj X₁ ⟶ (formalGlueingFunctor D).1.obj X₂}
    (θ : (formalGlueingFunctor D).1.obj T ≅ (formalGlueingFunctor D).1.obj X₁)
    (h₁ : (formalGlueingFunctor D).1.map (k ≫ p₁) = θ.hom)
    (h₂ : (formalGlueingFunctor D).1.map (k ≫ p₂) = θ.hom ≫ φ) :
    ∃ a : X₁ ⟶ X₂, (formalGlueingFunctor D).1.map a = φ :=
  exists_map_eq_of_graph (formalGlueingFunctor D).1 p₁ p₂ k θ h₁ h₂

/-- Surjectivity of the hom-set map of Stacks 0AF6 for `X₂ ⟶ X` separated, given `hreal`: the
essential surjectivity of Stacks 0AF4 part (2) in the slice over a space `Qq` over `X`, that is,
a morphism of glueing data into the restriction of `Qq` whose two components are closed
immersions comes from a space over `Qq`. -/
theorem exists_map_eq_of_essSurj_closedImmersion (D : FormalGlueingSituation B S hS)
    {X₁ X₂ : spacesOverX D} (hsep : IsSeparated B S hS X₂.obj.hom)
    (hreal : ∀ (Qq : spacesOverX D) (G : glueingData D)
      (ψ : G ⟶ (formalGlueingFunctor D).1.obj Qq),
      IsClosedImmersion B S hS ψ.hom.left.left →
      IsClosedImmersion B S hS ψ.hom.right.left →
      ∃ (T : spacesOverX D) (k : T ⟶ Qq) (θ : (formalGlueingFunctor D).1.obj T ≅ G),
        θ.hom ≫ ψ = (formalGlueingFunctor D).1.map k)
    (φ : (formalGlueingFunctor D).1.obj X₁ ⟶ (formalGlueingFunctor D).1.obj X₂) :
    ∃ a : X₁ ⟶ X₂, (formalGlueingFunctor D).1.map a = φ := by
  obtain ⟨Q, p₁, p₂, ⟨hQlim⟩, hsep₁⟩ : ∃ (Q : spacesOverX D) (p₁ : Q ⟶ X₁) (p₂ : Q ⟶ X₂),
      Nonempty (IsLimit (BinaryFan.mk p₁.hom p₂.hom)) ∧ IsSeparated B S hS p₁.hom.left :=
    ⟨⟨Over.mk (pullback.fst X₁.obj.hom X₂.obj.hom ≫ X₁.obj.hom),
        isAlgebraicSpace_pullback B S hS X₁.obj.hom X₂.obj.hom X₁.property X₂.property
          D.algebraicSpace_X⟩,
      ⟨Over.homMk (pullback.fst X₁.obj.hom X₂.obj.hom) rfl⟩,
      ⟨Over.homMk (pullback.snd X₁.obj.hom X₂.obj.hom) pullback.condition.symm⟩,
      ⟨overProdIsLimit X₁.obj X₂.obj⟩,
      isSeparated_of_isPullback B S hS
        (IsPullback.of_hasPullback X₁.obj.hom X₂.obj.hom).flip hsep⟩
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := exists_lift_formalGlueingFunctor D p₁ p₂ hQlim
    ((formalGlueingFunctor D).1.obj X₁) (𝟙 _) φ
  have hciU : IsClosedImmersion B S hS Γ.hom.left.left :=
    isClosedImmersion_of_isSeparated_of_section B S hS _
      (isSeparated_of_isPullback B S hS
        (isPullback_overPullback_map_left D.U.ι p₁.hom).flip hsep₁) _
      (congrArg (fun m : (formalGlueingFunctor D).1.obj X₁ ⟶
        (formalGlueingFunctor D).1.obj X₁ ↦ m.hom.left.left) hΓ₁)
  have hciY : IsClosedImmersion B S hS Γ.hom.right.left :=
    isClosedImmersion_of_isSeparated_of_section B S hS _
      (isSeparated_of_isPullback B S hS
        (isPullback_overPullback_map_left D.f p₁.hom).flip hsep₁) _
      (congrArg (fun m : (formalGlueingFunctor D).1.obj X₁ ⟶
        (formalGlueingFunctor D).1.obj X₁ ↦ m.hom.right.left) hΓ₁)
  obtain ⟨T, k, θ, hθ⟩ := hreal Q _ Γ hciU hciY
  refine exists_map_eq_of_graph_formalGlueingFunctor D p₁ p₂ k θ ?_ ?_
  · rw [Functor.map_comp, ← hθ, Category.assoc, hΓ₁, Category.comp_id]
  · rw [Functor.map_comp, ← hθ, Category.assoc, hΓ₂]

/-- The map on hom-sets induced by the restriction functor of Stacks 0AF3 is bijective as soon
as it is surjective. -/
theorem bijective_formalGlueingFunctor_map (D : FormalGlueingSituation B S hS)
    {X₁ X₂ : spacesOverX D}
    (hsurj : ∀ φ : (formalGlueingFunctor D).1.obj X₁ ⟶ (formalGlueingFunctor D).1.obj X₂,
      ∃ a : X₁ ⟶ X₂, (formalGlueingFunctor D).1.map a = φ) :
    Function.Bijective fun a : X₁ ⟶ X₂ ↦ (formalGlueingFunctor D).1.map a :=
  ⟨fun _ _ h ↦ injective_formalGlueingFunctor_map D _ _ h, hsurj⟩

/-- For `X₂ ⟶ X` separated, the restriction functor of Stacks 0AF3 induces a bijection
`Mor_X(X₁, X₂) ⟶ Mor(F X₁, F X₂)`, given `hreal`, the essential surjectivity of Stacks 0AF4
part (2) in the slice over a space over `X`. -/
theorem bijective_formalGlueingFunctor_map_of_essSurj_closedImmersion
    (D : FormalGlueingSituation B S hS) {X₁ X₂ : spacesOverX D}
    (hsep : IsSeparated B S hS X₂.obj.hom)
    (hreal : ∀ (Qq : spacesOverX D) (G : glueingData D)
      (ψ : G ⟶ (formalGlueingFunctor D).1.obj Qq),
      IsClosedImmersion B S hS ψ.hom.left.left →
      IsClosedImmersion B S hS ψ.hom.right.left →
      ∃ (T : spacesOverX D) (k : T ⟶ Qq) (θ : (formalGlueingFunctor D).1.obj T ≅ G),
        θ.hom ≫ ψ = (formalGlueingFunctor D).1.map k) :
    Function.Bijective fun a : X₁ ⟶ X₂ ↦ (formalGlueingFunctor D).1.map a :=
  bijective_formalGlueingFunctor_map D
    (exists_map_eq_of_essSurj_closedImmersion D hsep hreal)

end FormalGlueingSituation

end AlgebraicGeometry.Space

end
