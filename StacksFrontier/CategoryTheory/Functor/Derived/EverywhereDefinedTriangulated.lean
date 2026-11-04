module

public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksFrontier.CategoryTheory.EssentiallyConstant.Operations
public import StacksFrontier.CategoryTheory.Functor.Derived.Triangle
public import StacksFrontier.CategoryTheory.Functor.Derived.ValueIsPointwise
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An everywhere defined right derived functor is exact

Let `F : 𝒞 ⥤ ℋ` be an exact functor of pre-triangulated categories, let `W` be a saturated
multiplicative system of morphisms of `𝒞` compatible with the triangulation and with the shift,
and let `L : 𝒞 ⥤ 𝒟` be a localization functor for `W`, so that `𝒟` is a model of `W⁻¹𝒞`. Let
`F' : 𝒟 ⥤ ℋ` be a right derived functor of `F`, with comparison `α : F ⟶ L ⋙ F'`. If the right
derived functor is *everywhere defined* in Deligne's sense — if for every `X` the ind-object
`X/W ⟶ ℋ`, `(s : X ⟶ X') ↦ F(X')` is essentially constant (`Functor.IsRightDerivable`, Tag
05SV) — then `F'` is exact.

## Main results

* `CategoryTheory.Functor.derivedUnitCocone`: the cocone on the ind-object at `X` with vertex
  `F'(L(X))` whose coprojection at `(s : X ⟶ X')` is `F(X') ⟶ F'(L(X')) ≅ F'(L(X))`, the
  comparison followed by the inverse of the isomorphism `F'(L(s))`.
* `CategoryTheory.Functor.isRightDerivedValueAt_derivedUnitCocone`: that cocone is a value of the
  right derived functor at `X` in the sense of Tag 05S9, as soon as the right derived functor is
  defined at every object.
* `CategoryTheory.Functor.isTriangulated_of_isRightDerivable`: `F'` is exact.

## Implementation notes

*Why the comparison cocone.* The content of the file is the identification of Mathlib's right
derived functor — a left Kan extension along `L` — with Deligne's values. Everywhere-definedness
gives, through `Functor.hasPointwiseRightDerivedFunctor_of_isRightDerivable`, that the Kan
extension is pointwise, so `F'(L(X))` is the colimit of the diagram indexed by the arrows
`L(Y) ⟶ L(X)` of the localization; the comparison functor from `X/W` to that index category is
final (`MorphismProperty.final_underToCostructuredArrow`), so `F'(L(X))` is also the colimit of
the ind-object, at the restricted cocone, which is `derivedUnitCocone`. A colimit cocone on an
essentially constant ind-object is itself a value of the right derived functor, by
`EssentiallyConstantInd.IsEssentiallyConstantInd.exists_retraction_of_isColimit`: the retraction
and the cofinal factorization transport along the canonical isomorphism of colimit cocones. The
restricted cocone is *definitionally* the whiskering, so its coprojections are the stated
composites by `rfl`.

*Why exactness is then Tag 05SC.* `L ⋙ F'` carries a distinguished triangle `T` of `𝒞` to the
triangle of values of Tag 05SC, which that tag says is distinguished: the three morphisms it
produces are characterised by compatibility with the coprojections (Tag 05SA), and the
coprojections of `derivedUnitCocone` are explicit enough that `F'(L(T.mor₁))`, `F'(L(T.mor₂))`
and `F'(L(T.mor₃))` followed by the shift comparison are checked to satisfy the same
characterisations — `unit_comp_map_eq` and `unit_comp_map_comp_commShiftIso_eq`, which use of the
shift no more than the naturality of the shift comparison of `L ⋙ F'` and the compatibility of
`α` with the shift. Each characterisation determines the morphism, because a value is a colimit
cocone and the Ore condition MS2 completes any index to a square; for the third morphism the
square needed is one over an object of `W` out of `X⟦1⟧`, which stability of `W` under the shift
turns into one out of `X` (`exists_shifted_sq`). Exactness of `F'` itself then follows from
exactness of `L ⋙ F'` by `Functor.isTriangulated_of_precomp`, the localization functor being
exact and essentially surjective on arrows.

This is the half of Tag 05SE's part (7) that the everywhere-defined case needs, obtained for the
derived functor as Mathlib builds it rather than for a functor on the localization of the
subcategory where `RF` is defined.

## References

* [Stacks Project, Tag 05SE](https://stacks.math.columbia.edu/tag/05SE), of which this is the
  everywhere-defined case; [Tag 05SC](https://stacks.math.columbia.edu/tag/05SC) for the triangle
  of values and [Tag 05SV](https://stacks.math.columbia.edu/tag/05SV) for everywhere-definedness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

section Value

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H]
  (F : C ⥤ H) (W : MorphismProperty C) (L : C ⥤ D) [L.IsLocalization W]
  (F' : D ⥤ H) (α : F ⟶ L ⋙ F')

/-- The cocone on Deligne's ind-object `X/W ⟶ ℋ`, `(s : X ⟶ X') ↦ F(X')` of Tag 05S9 with vertex
`F'(L(X))` attached to a comparison `α : F ⟶ L ⋙ F'`: its coprojection at `(s : X ⟶ X')` is `α`
at `X'` followed by the inverse of `F'(L(s))`, which is invertible because a localization functor
inverts `W`.

It is the cocone computing the pointwise left Kan extension of `F` along `L` at `L(X)`,
restricted along the comparison functor `X/W ⥤ CostructuredArrow L (L(X))` of
`CategoryTheory.MorphismProperty.underToCostructuredArrow`. -/
noncomputable def derivedUnitCocone (X : C) :
    Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F) :=
  ((LeftExtension.mk F' α).coconeAt (L.obj X)).whisker (W.underToCostructuredArrow L X)

/-- The vertex of `CategoryTheory.Functor.derivedUnitCocone` at `X` is `F'(L(X))`. -/
@[simp]
lemma derivedUnitCocone_pt (X : C) :
    (derivedUnitCocone F W L F' α X).pt = F'.obj (L.obj X) :=
  rfl

/-- The coprojection of `CategoryTheory.Functor.derivedUnitCocone` at `(s : X ⟶ X')` is `α` at
`X'` followed by the inverse of `F'(L(s))`. -/
@[simp]
lemma derivedUnitCocone_ι_app (X : C) (s : W.Under ⊤ X) :
    (derivedUnitCocone F W L F' α X).ι.app s
      = α.app s.right ≫ F'.map (W.underIso L X s).inv :=
  rfl

/-- **The comparison cocone is a colimit cocone**, as soon as the right derived functor is
everywhere defined: the left Kan extension is then pointwise, and the comparison functor from
Deligne's index category to the Kan-extension index category is final. -/
noncomputable def isColimitDerivedUnitCocone [W.HasLeftCalculusOfFractions]
    [F.HasPointwiseRightDerivedFunctor W] [F'.IsRightDerivedFunctor α W] (X : C) :
    IsColimit (derivedUnitCocone F W L F' α X) :=
  letI := W.final_underToCostructuredArrow L X
  (Functor.Final.isColimitWhiskerEquiv (W.underToCostructuredArrow L X)
      ((LeftExtension.mk F' α).coconeAt (L.obj X))).symm
    (Functor.isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor F' α W (L.obj X))

/-- A colimit cocone on the ind-object of Tag 05S9 is a value of the right derived functor as
soon as that ind-object is essentially constant: any two colimit cocones are canonically
isomorphic, and the essential-constancy data transports. -/
theorem isRightDerivedValueAt_of_isColimit (X : C)
    {c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)}
    (h : ∃ c', F.IsRightDerivedValueAt W X c') (hc : IsColimit c) :
    F.IsRightDerivedValueAt W X c := by
  rw [Functor.isRightDerivedValueAt_iff]
  exact EssentiallyConstantInd.IsEssentiallyConstantInd.exists_retraction_of_isColimit
    ((F.exists_isRightDerivedValueAt_iff W X).1 h) hc

/-- **The comparison cocone is a value of the right derived functor** at `X` in the sense of
Tag 05S9, as soon as the right derived functor is everywhere defined. -/
theorem isRightDerivedValueAt_derivedUnitCocone [W.HasLeftCalculusOfFractions]
    [F'.IsRightDerivedFunctor α W] (h : F.IsRightDerivable W) (X : C) :
    F.IsRightDerivedValueAt W X (derivedUnitCocone F W L F' α X) :=
  have := F.hasPointwiseRightDerivedFunctor_of_isRightDerivable W h
  isRightDerivedValueAt_of_isColimit F W X (h X) (isColimitDerivedUnitCocone F W L F' α X)

/-- The two halves of the isomorphism attached to a morphism of `W` cancel after `F'`: this is
what makes the coprojections of `CategoryTheory.Functor.derivedUnitCocone` split `F'(L(a))`. -/
lemma map_comp_map_isoOfHom_inv {X X' : C} (a : X ⟶ X') (ha : W a) :
    F'.map (L.map a) ≫ F'.map (Localization.isoOfHom L W a ha).inv = 𝟙 (F'.obj (L.obj X)) := by
  rw [← F'.map_comp, show L.map a = (Localization.isoOfHom L W a ha).hom from rfl,
    Iso.hom_inv_id, F'.map_id]

/-- **`(L ⋙ F')(f)` satisfies the characterisation of Tag 05SA** relative to the comparison
cocones: it is compatible with their coprojections along every square `f ≫ b = a ≫ g` whose
vertical sides `a` and `b` lie in `W`. -/
lemma unit_comp_map_eq {X Y X' Y' : C} (f : X ⟶ Y) (a : X ⟶ X') (ha : W a)
    (b : Y ⟶ Y') (hb : W b) (g : X' ⟶ Y') (hsq : f ≫ b = a ≫ g) :
    (α.app X' ≫ F'.map (Localization.isoOfHom L W a ha).inv) ≫ (L ⋙ F').map f
      = F.map g ≫ (α.app Y' ≫ F'.map (Localization.isoOfHom L W b hb).inv) := by
  have hL : (Localization.isoOfHom L W a ha).inv ≫ L.map f
      = L.map g ≫ (Localization.isoOfHom L W b hb).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, Localization.isoOfHom_hom,
      Localization.isoOfHom_hom, ← L.map_comp, ← L.map_comp, hsq]
  have hnat : F.map g ≫ α.app Y' = α.app X' ≫ F'.map (L.map g) := α.naturality g
  rw [Functor.comp_map, Category.assoc, ← F'.map_comp, hL, F'.map_comp, ← Category.assoc,
    ← hnat, Category.assoc]

/-- **The third morphism of the triangle of values satisfies the characterisation of Tag 05SC**:
`(L ⋙ F')(φ)` followed by the shift comparison of `L ⋙ F'` is compatible with the coprojections
of the comparison cocones along every shifted square `φ ≫ b⟦1⟧' = a ≫ h'`.

The proof uses of the shift only the naturality of the shift comparison of `L ⋙ F'` and the
compatibility of `α` with the shift; the two halves of the isomorphisms attached to `a` and `b`
cancel by `CategoryTheory.Functor.map_comp_map_isoOfHom_inv`. -/
lemma unit_comp_map_comp_commShiftIso_eq
    [HasShift C ℤ] [HasShift D ℤ] [HasShift H ℤ]
    [F.CommShift ℤ] [L.CommShift ℤ] [F'.CommShift ℤ] [NatTrans.CommShift α ℤ]
    {Z X R S : C} (φ : Z ⟶ X⟦(1 : ℤ)⟧)
    (a : Z ⟶ R) (ha : W a) (b : X ⟶ S) (hb : W b) (h' : R ⟶ S⟦(1 : ℤ)⟧)
    (hsq : φ ≫ b⟦(1 : ℤ)⟧' = a ≫ h') :
    (α.app R ≫ F'.map (Localization.isoOfHom L W a ha).inv) ≫
        ((L ⋙ F').map φ ≫ ((L ⋙ F').commShiftIso (1 : ℤ)).hom.app X)
      = F.map h' ≫ (F.commShiftIso (1 : ℤ)).hom.app S ≫
          (α.app S ≫ F'.map (Localization.isoOfHom L W b hb).inv)⟦(1 : ℤ)⟧' := by
  have hiso : IsIso (L.map a) := Localization.inverts L W a ha
  have hsplitZ := map_comp_map_isoOfHom_inv W L F' a ha
  have hsplitX := map_comp_map_isoOfHom_inv W L F' b hb
  have hcs := ((L ⋙ F').commShiftIso (1 : ℤ)).hom.naturality b
  have e₁ := NatTrans.shift_app_comm α (1 : ℤ) S
  have e₂ := α.naturality h'
  dsimp only [Functor.comp_obj, Functor.comp_map] at hcs e₁ e₂
  have key : F'.map (L.map h') ≫ ((L ⋙ F').commShiftIso (1 : ℤ)).hom.app S ≫
        (F'.map (Localization.isoOfHom L W b hb).inv)⟦(1 : ℤ)⟧'
      = F'.map (Localization.isoOfHom L W a ha).inv ≫ F'.map (L.map φ) ≫
        ((L ⋙ F').commShiftIso (1 : ℤ)).hom.app X := by
    rw [← cancel_epi (F'.map (L.map a)),
      ← Category.assoc (F'.map (L.map a)) (F'.map (Localization.isoOfHom L W a ha).inv),
      hsplitZ, Category.id_comp,
      ← Category.assoc (F'.map (L.map a)) (F'.map (L.map h')), ← F'.map_comp, ← L.map_comp,
      ← hsq, L.map_comp, F'.map_comp, Category.assoc]
    congr 1
    rw [← Category.assoc, hcs, Category.assoc, ← CategoryTheory.Functor.map_comp, hsplitX]
    simp
  have hR : F.map h' ≫ (F.commShiftIso (1 : ℤ)).hom.app S ≫
      (α.app S ≫ F'.map (Localization.isoOfHom L W b hb).inv)⟦(1 : ℤ)⟧'
      = α.app R ≫ F'.map (L.map h') ≫ ((L ⋙ F').commShiftIso (1 : ℤ)).hom.app S ≫
          (F'.map (Localization.isoOfHom L W b hb).inv)⟦(1 : ℤ)⟧' := by
    rw [CategoryTheory.Functor.map_comp,
      ← Category.assoc ((F.commShiftIso (1 : ℤ)).hom.app S) ((α.app S)⟦(1 : ℤ)⟧'), e₁,
      Category.assoc, ← Category.assoc (F.map h') (α.app (S⟦(1 : ℤ)⟧)), e₂]
    simp only [Category.assoc]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  rw [hR, key]
  simp only [Category.assoc]

/-- A morphism `u` between the vertices of the comparison cocones at `X` and `Y` which is
compatible with their coprojections along every square over `f` is `(L ⋙ F')(f)`. -/
private theorem eq_map_of_forall_eq [W.HasLeftCalculusOfFractions]
    [F.HasPointwiseRightDerivedFunctor W] [F'.IsRightDerivedFunctor α W] {X Y : C} (f : X ⟶ Y)
    (u : F'.obj (L.obj X) ⟶ F'.obj (L.obj Y))
    (hu : ∀ (s : W.Under ⊤ X) (t : W.Under ⊤ Y) (f' : s.right ⟶ t.right), f ≫ t.hom = s.hom ≫ f' →
      (derivedUnitCocone F W L F' α X).ι.app s ≫ u
        = F.map f' ≫ (derivedUnitCocone F W L F' α Y).ι.app t) :
    u = (L ⋙ F').map f := by
  refine (isColimitDerivedUnitCocone F W L F' α X).hom_ext fun c => ?_
  obtain ⟨ψ, hψ⟩ := MorphismProperty.HasLeftCalculusOfFractions.exists_leftFraction
    (MorphismProperty.RightFraction.mk (W := W) (X := c.right) (Y := Y)
      (show X ⟶ c.right from c.hom) c.prop f)
  exact (hu c (MorphismProperty.Under.mk ⊤ ψ.s ψ.hs) ψ.f hψ).trans
    (unit_comp_map_eq F W L F' α f _ c.prop _ ψ.hs ψ.f hψ).symm

end Value

section Exact

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {H : Type u₃} [Category.{v₃} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]

omit [HasZeroObject C] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- Every morphism `a : Z ⟶ R` of `W` fits into a shifted square for `φ : Z ⟶ X⟦1⟧`: the Ore
condition MS2 completes `φ` and `a` to a square over a morphism of `W` out of `X⟦1⟧`, and
stability of `W` under the shift turns that into a morphism of `W` out of `X`. -/
lemma exists_shifted_sq (W : MorphismProperty C) [W.IsCompatibleWithShift ℤ]
    (hW : W.IsSaturated) {Z X R : C} (φ : Z ⟶ X⟦(1 : ℤ)⟧) (a : Z ⟶ R) (ha : W a) :
    ∃ (S : C) (b : X ⟶ S) (_ : W b) (h' : R ⟶ S⟦(1 : ℤ)⟧), φ ≫ b⟦(1 : ℤ)⟧' = a ≫ h' := by
  have := hW.hasLeftCalculusOfFractions
  have := hW.isMultiplicative
  obtain ⟨ψ, hψ⟩ := MorphismProperty.HasLeftCalculusOfFractions.exists_leftFraction
    (MorphismProperty.RightFraction.mk (W := W) (X := R) (Y := X⟦(1 : ℤ)⟧) a ha φ)
  have he : W ((shiftFunctorCompIsoId C (1 : ℤ) (-1) (by omega)).inv.app X) :=
    DerivedFunctorValues.isomorphisms_le_of_isSaturated hW _ inferInstance
  have hb : W ((shiftFunctorCompIsoId C (1 : ℤ) (-1) (by omega)).inv.app X ≫
      ψ.s⟦(-1 : ℤ)⟧') :=
    W.comp_mem _ _ he ((MorphismProperty.IsCompatibleWithShift.iff W ψ.s (-1 : ℤ)).2 ψ.hs)
  have key : ((shiftFunctorCompIsoId C (1 : ℤ) (-1) (by omega)).inv.app X ≫
      ψ.s⟦(-1 : ℤ)⟧')⟦(1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId C (-1 : ℤ) 1 (by omega)).hom.app ψ.Y' = ψ.s := by
    rw [CategoryTheory.Functor.map_comp, shift_shiftFunctorCompIsoId_add_neg_cancel_inv_app,
      Category.assoc]
    exact shiftFunctorCompIsoId_naturality_1 ψ.s (-1 : ℤ) 1 (by omega)
  refine ⟨ψ.Y'⟦(-1 : ℤ)⟧, _, hb,
    ψ.f ≫ (shiftFunctorCompIsoId C (-1 : ℤ) 1 (by omega)).inv.app ψ.Y', ?_⟩
  rw [← cancel_mono ((shiftFunctorCompIsoId C (-1 : ℤ) 1 (by omega)).hom.app ψ.Y'),
    Category.assoc, key, Category.assoc, Category.assoc, Iso.inv_hom_id_app]
  simpa using hψ

/-- **An everywhere defined right derived functor, composed with the localization, is exact.**
For a distinguished triangle `T` of `𝒞`, Tag 05SC produces morphisms between the values of `RF`
at the three vertices forming a distinguished triangle; they are `(L ⋙ F')` of the three
morphisms of `T` — the third read through the shift comparison — because each is characterised by
compatibility with the coprojections and the characterisation determines it, a value being a
colimit cocone. -/
@[sga "4 XVII 1.2.2" "(ii), special case"]
theorem isTriangulated_comp_of_isRightDerivable
    (F : C ⥤ H) [F.CommShift ℤ] [F.IsTriangulated]
    (W : MorphismProperty C) [W.IsCompatibleWithTriangulation]
    (L : C ⥤ D) [L.IsLocalization W] [L.CommShift ℤ] [L.IsTriangulated]
    (F' : D ⥤ H) [F'.CommShift ℤ] (α : F ⟶ L ⋙ F') [NatTrans.CommShift α ℤ]
    [F'.IsRightDerivedFunctor α W] (hW : W.IsSaturated)
    (h : F.IsRightDerivable W) : (L ⋙ F').IsTriangulated := by
  have := hW.hasLeftCalculusOfFractions
  have := F.hasPointwiseRightDerivedFunctor_of_isRightDerivable W h
  constructor
  intro T hT
  obtain ⟨u, v, w, hdist, hu, hv, hw⟩ :=
    (F.exists_isRightDerivedValueAt_and_isLeftDerivedValueAt_and_triangle_distinguished W hW
        T hT).1.2.2.2
      (derivedUnitCocone F W L F' α T.obj₁)
      (isRightDerivedValueAt_derivedUnitCocone F W L F' α h T.obj₁)
      (derivedUnitCocone F W L F' α T.obj₂)
      (isRightDerivedValueAt_derivedUnitCocone F W L F' α h T.obj₂)
      (derivedUnitCocone F W L F' α T.obj₃)
      (isRightDerivedValueAt_derivedUnitCocone F W L F' α h T.obj₃)
  have heu : u = (L ⋙ F').map T.mor₁ :=
    eq_map_of_forall_eq F W L F' α T.mor₁ u hu
  have hev : v = (L ⋙ F').map T.mor₂ :=
    eq_map_of_forall_eq F W L F' α T.mor₂ v hv
  have hew : w = (L ⋙ F').map T.mor₃ ≫
      ((L ⋙ F').commShiftIso (1 : ℤ)).hom.app T.obj₁ := by
    refine (isColimitDerivedUnitCocone F W L F' α T.obj₃).hom_ext fun c => ?_
    obtain ⟨S, b, hb, h', hsq⟩ := exists_shifted_sq W hW T.mor₃
      (show T.obj₃ ⟶ c.right from c.hom) c.prop
    exact (hw c (MorphismProperty.Under.mk ⊤ b hb) h' hsq).trans
      (unit_comp_map_comp_commShiftIso_eq F W L F' α T.mor₃ _ c.prop b hb h' hsq).symm
  have hmk : Pretriangulated.Triangle.mk u v w = (L ⋙ F').mapTriangle.obj T := by
    rw [heu, hev, hew]
    exact (Functor.mapTriangle_obj (L ⋙ F') T).symm
  exact hmk ▸ hdist

/-- **An everywhere defined right derived functor is exact.** Let `F : 𝒞 ⥤ ℋ` be an exact functor
of pre-triangulated categories, let `W` be a saturated multiplicative system of morphisms of `𝒞`
compatible with the triangulation and with the shift, let `L : 𝒞 ⥤ 𝒟` be a localization functor
for `W`, and let `F'` be a right derived functor of `F` along `L`, with comparison `α`. If the
right derived functor is defined at every object of `𝒞` (Tag 05SV), then `F'` is exact.

Exactness of `L ⋙ F'` is `CategoryTheory.Functor.isTriangulated_comp_of_isRightDerivable`, and
exactness of `F'` follows because `L` is exact and essentially surjective on arrows. -/
@[sga "4 XVII 1.2.2" "(ii), special case"]
theorem isTriangulated_of_isRightDerivable
    (F : C ⥤ H) [F.CommShift ℤ] [F.IsTriangulated]
    (W : MorphismProperty C) [W.IsCompatibleWithTriangulation]
    (L : C ⥤ D) [L.IsLocalization W] [L.CommShift ℤ] [L.IsTriangulated]
    (F' : D ⥤ H) [F'.CommShift ℤ] (α : F ⟶ L ⋙ F') [NatTrans.CommShift α ℤ]
    [F'.IsRightDerivedFunctor α W] (hW : W.IsSaturated) (h : F.IsRightDerivable W) :
    F'.IsTriangulated :=
  have := hW.hasLeftCalculusOfFractions
  have := Localization.essSurj_mapArrow L W
  have := isTriangulated_comp_of_isRightDerivable F W L F' α hW h
  Functor.isTriangulated_of_precomp L F'

end Exact

end CategoryTheory.Functor

end
