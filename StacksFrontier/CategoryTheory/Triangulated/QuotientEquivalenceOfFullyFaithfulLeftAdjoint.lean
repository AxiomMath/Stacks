module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# A Verdier quotient identified with the target of a functor with a fully faithful left adjoint

Let `G : 𝒞 ⥤ 𝒞'` be a triangulated functor between pretriangulated categories with a left
adjoint `L` whose unit `𝟭 ⟶ L ⋙ G` is an isomorphism, i.e. `G ∘ L = id`. Let `𝒜 ⊆ 𝒞` be a
triangulated subcategory and `𝒜' ⊆ 𝒞'` a subcategory such that `G(𝒜) ⊆ 𝒜'` and
`L(𝒜') ⊆ 𝒜`, and let `𝒩` be the objects of `𝒜` killed by `G`.  Then the quotient of `𝒜` by the
morphisms with cone in `𝒩` is equivalent to `𝒜'`: the functor induced by `G` on the quotient
and the composite of `L` with the quotient functor are mutually inverse.

## Main definitions

* `CategoryTheory.Pretriangulated.quotientFunctorOfLeftAdjoint`: the functor `c : 𝒜[W⁻¹] ⥤ 𝒜'`
  induced by `G`.
* `CategoryTheory.Pretriangulated.quotientEquivalenceOfLeftAdjoint`: the equivalence, with
  functor `c` and inverse `q ∘ L`.

## References

* [Stacks Project, Tag 07B9](https://stacks.math.columbia.edu/tag/07B9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {C' : Type*} [Category* C'] [Preadditive C'] [HasZeroObject C'] [HasShift C' ℤ]
  [∀ n : ℤ, (shiftFunctor C' n).Additive] [Pretriangulated C']
  (G : C ⥤ C') [G.CommShift ℤ] [G.IsTriangulated]
  {L : C' ⥤ C} (adj : L ⊣ G)
  (A : ObjectProperty C) (A' : ObjectProperty C') (N : ObjectProperty C)
  (hGA : ∀ X, A X → A' (G.obj X)) (hLA : ∀ Y, A' Y → A (L.obj Y))
  (hN : ∀ X, N X → IsZero (G.obj X))
  {Q : Type*} [Category* Q] (q : A.FullSubcategory ⥤ Q)
  [q.IsLocalization (N.trW.inverseImage A.ι)]

/-- `G`, read as a functor `𝒜 ⥤ 𝒜'`. -/
def restrictionOfClass : A.FullSubcategory ⥤ A'.FullSubcategory :=
  A'.lift (A.ι ⋙ G) fun X => hGA X.obj X.property

/-- `L`, read as a functor `𝒜' ⥤ 𝒜`. -/
def leftAdjointOfClass : A'.FullSubcategory ⥤ A.FullSubcategory :=
  A.lift (A'.ι ⋙ L) fun Y => hLA Y.obj Y.property

include hN in
/-- `G` inverts the morphisms of `𝒜` whose cone lies in `𝒩`. -/
theorem isInvertedBy_restrictionOfClass :
    (N.trW.inverseImage A.ι).IsInvertedBy (restrictionOfClass G A A' hGA) := by
  intro X Y f hf
  obtain ⟨Z, g, h, hT, hZ⟩ := hf
  have hiso : IsIso (G.map f.hom) :=
    (Triangle.isZero₃_iff_isIso₁ _ (G.map_distinguished _ hT)).1 (hN Z hZ)
  have : IsIso (A'.ι.map ((restrictionOfClass G A A' hGA).map f)) := hiso
  exact A'.fullyFaithfulι.isIso_of_isIso_map _

/-- The functor `c : 𝒜[W⁻¹] ⥤ 𝒜'` induced by `G` on the quotient of `𝒜` by the morphisms with
cone in `𝒩`. -/
def quotientFunctorOfLeftAdjoint : Q ⥤ A'.FullSubcategory :=
  Localization.lift _ (isInvertedBy_restrictionOfClass G A A' N hGA hN) q

/-- The functor `c` composed with the quotient functor is `G`. -/
def quotientFunctorOfLeftAdjointFac :
    q ⋙ quotientFunctorOfLeftAdjoint G A A' N hGA hN q ≅ restrictionOfClass G A A' hGA :=
  Localization.fac _ (isInvertedBy_restrictionOfClass G A A' N hGA hN) q

/-- The inverse functor `q ∘ L : 𝒜' ⥤ 𝒜[W⁻¹]`. -/
def quotientInverseOfLeftAdjoint : A'.FullSubcategory ⥤ Q :=
  leftAdjointOfClass A A' hLA ⋙ q

variable [IsIso adj.unit] [A.IsTriangulated] [A.IsClosedUnderIsomorphisms]
  (hNA : ∀ X, A X → IsZero (G.obj X) → N X)

include hNA in
/-- The counit `L G E ⟶ E` at an object of `𝒜` has its cone in `𝒩`. -/
theorem trW_counit_app (X : A.FullSubcategory) :
    N.trW.inverseImage A.ι
      ((A.fullyFaithfulι.preimage (adj.counit.app X.obj)) :
        (leftAdjointOfClass A A' hLA).obj ((restrictionOfClass G A A' hGA).obj X) ⟶ X) := by
  show N.trW (adj.counit.app X.obj)
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (adj.counit.app X.obj)
  have hGε : IsIso (G.map (adj.counit.app X.obj)) :=
    IsIso.of_isIso_fac_left (adj.right_triangle_components X.obj)
  have hZ : IsZero (G.obj Z) :=
    (Triangle.isZero₃_iff_isIso₁ _ (G.map_distinguished _ hT)).2 hGε
  have hAZ : A Z := A.ext_of_isTriangulatedClosed₃ _ hT
    (hLA _ (hGA _ X.property)) X.property
  exact ⟨Z, g, h, hT, hNA Z hAZ hZ⟩

/-- The quotient of `𝒜` by the morphisms with cone in `𝒩` is equivalent to `𝒜'`, by the functor
`c` induced by `G`, with inverse `q ∘ L`. -/
def quotientEquivalenceOfLeftAdjoint : Q ≌ A'.FullSubcategory :=
  Equivalence.mk (quotientFunctorOfLeftAdjoint G A A' N hGA hN q)
    (quotientInverseOfLeftAdjoint A A' hLA q) (by
    let W := N.trW.inverseImage A.ι
    let e₁ : q ⋙ quotientFunctorOfLeftAdjoint G A A' N hGA hN q ⋙
        quotientInverseOfLeftAdjoint A A' hLA q ≅
        (restrictionOfClass G A A' hGA ⋙ leftAdjointOfClass A A' hLA) ⋙ q :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (quotientFunctorOfLeftAdjointFac G A A' N hGA hN q) _ ≪≫
          (Functor.associator _ _ _).symm
    let ε : restrictionOfClass G A A' hGA ⋙ leftAdjointOfClass A A' hLA ⟶ 𝟭 _ :=
      { app := fun X => A.fullyFaithfulι.preimage (adj.counit.app X.obj)
        naturality := fun X Y f => A.fullyFaithfulι.map_injective (by
          simp only [Functor.comp_map, Functor.map_comp, Functor.id_map]
          exact adj.counit.naturality f.hom) }
    have : ∀ X, IsIso ((Functor.whiskerRight ε q).app X) := fun X =>
      Localization.inverts q W _ (trW_counit_app G adj A A' N hGA hLA hNA X)
    have : IsIso (Functor.whiskerRight ε q) := NatIso.isIso_of_isIso_app _
    let e₂ : (restrictionOfClass G A A' hGA ⋙ leftAdjointOfClass A A' hLA) ⋙ q ≅ q :=
      asIso (Functor.whiskerRight ε q) ≪≫ q.leftUnitor
    exact ((Localization.whiskeringLeftFunctor' q W Q).preimageIso
      (q.rightUnitor ≪≫ e₂.symm ≪≫ e₁.symm))) (by
    let e : quotientInverseOfLeftAdjoint A A' hLA q ⋙
        quotientFunctorOfLeftAdjoint G A A' N hGA hN q ≅
        leftAdjointOfClass A A' hLA ⋙ restrictionOfClass G A A' hGA :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (quotientFunctorOfLeftAdjointFac G A A' N hGA hN q)
    refine e ≪≫ NatIso.ofComponents (fun Y => A'.fullyFaithfulι.preimageIso
      (asIso (adj.unit.app Y.obj)).symm) fun {Y Y'} f => A'.fullyFaithfulι.map_injective ?_
    simp only [Functor.comp_map, Functor.map_comp, Functor.id_map]
    simp [restrictionOfClass, leftAdjointOfClass])

/-- The functor of `quotientEquivalenceOfLeftAdjoint` is the functor `c` induced by `G`. -/
@[simp]
theorem quotientEquivalenceOfLeftAdjoint_functor :
    (quotientEquivalenceOfLeftAdjoint G adj A A' N hGA hLA hN q hNA).functor =
      quotientFunctorOfLeftAdjoint G A A' N hGA hN q :=
  rfl

/-- The inverse of `quotientEquivalenceOfLeftAdjoint` is `q ∘ L`. -/
@[simp]
theorem quotientEquivalenceOfLeftAdjoint_inverse :
    (quotientEquivalenceOfLeftAdjoint G adj A A' N hGA hLA hN q hNA).inverse =
      quotientInverseOfLeftAdjoint A A' hLA q :=
  rfl

end CategoryTheory.Pretriangulated
