module

public import StacksFrontier.CategoryTheory.Functor.Derived.EverywhereDefinedTriangulated
public import StacksFrontier.CategoryTheory.Functor.Derived.ValueIsPointwiseLeft

/-!
# An everywhere defined left derived functor is exact

This is the dual of `StacksFrontier.CategoryTheory.Functor.Derived.EverywhereDefinedTriangulated`.
Let `F : 𝒞 ⥤ ℋ` be an exact functor of pre-triangulated categories, let `W` be a saturated
multiplicative system of morphisms of `𝒞` compatible with the triangulation, let `L : 𝒞 ⥤ 𝒟` be a
localization functor for `W`, and let `F' : 𝒟 ⥤ ℋ` be a left derived functor of `F`, with
comparison `α : L ⋙ F' ⟶ F`. If the left derived functor is *everywhere defined* in Deligne's
sense (`Functor.IsLeftDerivable`, Tag 05SV) then `F'` is exact.

## Main results

* `CategoryTheory.Functor.derivedCounitCone`: the cone on the pro-object at `X` with vertex
  `F'(L(X))` whose projection at `(s : X' ⟶ X)` is `F'(L(X)) ≅ F'(L(X')) ⟶ F(X')`.
* `CategoryTheory.Functor.isLeftDerivedValueAt_derivedCounitCone`: that cone is a value of the
  left derived functor at `X` in the sense of Tag 05S9, as soon as `F` is left derivable.
* `CategoryTheory.Functor.isTriangulated_of_isLeftDerivable`: `F'` is exact.

## Implementation notes

The argument is the dual of the right-hand one: everywhere-definedness makes the right Kan
extension pointwise (`Functor.hasPointwiseLeftDerivedFunctor_of_isLeftDerivable`), the comparison
functor `W/X ⥤ StructuredArrow (L(X)) L` is initial, so `F'(L(X))` with the restricted cone is a
limit of the pro-object, hence a value; then the left half of Tag 05SC applied to these values
produces a distinguished triangle whose morphisms are characterised by compatibility with the
projections (Tag 05SA), and `(L ⋙ F')` of the morphisms of the triangle satisfy the same
characterisations. For the third morphism, uniqueness is tested against the projections of the
shifted limit cone at `X⟦1⟧`, and the square needed is completed by the right Ore condition
against `s⟦1⟧`, which lies in `W` by compatibility with the shift.

## References

* [Stacks Project, Tag 05SE](https://stacks.math.columbia.edu/tag/05SE), of which this is the
  everywhere-defined case for `LF`; [Tag 05SC](https://stacks.math.columbia.edu/tag/05SC) for the
  triangle of values and [Tag 05SV](https://stacks.math.columbia.edu/tag/05SV) for
  everywhere-definedness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

section LeftValue

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H]
  (F : C ⥤ H) (W : MorphismProperty C) (L : C ⥤ D) [L.IsLocalization W]
  (F' : D ⥤ H) (α : L ⋙ F' ⟶ F)

/-- The cone on Deligne's pro-object `W/X ⟶ ℋ`, `(s : X' ⟶ X) ↦ F(X')` of Tag 05S9 with vertex
`F'(L(X))` attached to a comparison `α : L ⋙ F' ⟶ F`: its projection at `(s : X' ⟶ X)` is the
inverse of `F'(L(s))` followed by `α` at `X'`.

It is the cone computing the pointwise right Kan extension of `F` along `L` at `L(X)`,
restricted along the comparison functor `W/X ⥤ StructuredArrow (L(X)) L` of
`CategoryTheory.MorphismProperty.overToStructuredArrow`. -/
noncomputable def derivedCounitCone (X : C) :
    Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F) :=
  ((RightExtension.mk F' α).coneAt (L.obj X)).whisker (W.overToStructuredArrow L X)

/-- The vertex of `CategoryTheory.Functor.derivedCounitCone` at `X` is `F'(L(X))`. -/
@[simp]
lemma derivedCounitCone_pt (X : C) :
    (derivedCounitCone F W L F' α X).pt = F'.obj (L.obj X) :=
  rfl

/-- The projection of `CategoryTheory.Functor.derivedCounitCone` at `(s : X' ⟶ X)` is the inverse
of `F'(L(s))` followed by `α` at `X'`. -/
@[simp]
lemma derivedCounitCone_π_app (X : C) (s : W.Over ⊤ X) :
    (derivedCounitCone F W L F' α X).π.app s
      = F'.map (W.overIso L X s).inv ≫ α.app s.left :=
  rfl

/-- **The comparison cone is a limit cone**, as soon as `F` has a pointwise left derived functor:
the right Kan extension is then pointwise, and the comparison functor from Deligne's index
category to the Kan-extension index category is initial. -/
noncomputable def isLimitDerivedCounitCone [W.HasRightCalculusOfFractions]
    [F.HasPointwiseLeftDerivedFunctor W] [F'.IsLeftDerivedFunctor α W] (X : C) :
    IsLimit (derivedCounitCone F W L F' α X) :=
  letI := W.initial_overToStructuredArrow L X
  (Functor.Initial.isLimitWhiskerEquiv (W.overToStructuredArrow L X)
      ((RightExtension.mk F' α).coneAt (L.obj X))).symm
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor F' α W (L.obj X))

/-- A limit cone on the pro-object of Tag 05S9 is a value of the left derived functor as soon as
that pro-object is essentially constant: any two limit cones are canonically isomorphic, and the
essential-constancy data transports. -/
theorem isLeftDerivedValueAt_of_isLimit (X : C)
    {c : Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F)}
    (h : ∃ c', F.IsLeftDerivedValueAt W X c') (hc : IsLimit c) :
    F.IsLeftDerivedValueAt W X c := by
  obtain ⟨c', hc'⟩ := h
  obtain ⟨s₀, r, hw⟩ := (F.isLeftDerivedValueAt_iff W X c').1 hc'
  exact (F.isLeftDerivedValueAt_iff W X c).2 ⟨s₀, _, hw.of_iso (hc'.isLimit.uniqueUpToIso hc)⟩

/-- **The comparison cone is a value of the left derived functor** at `X` in the sense of
Tag 05S9, as soon as the left derived functor is everywhere defined. -/
theorem isLeftDerivedValueAt_derivedCounitCone [W.HasRightCalculusOfFractions]
    [F'.IsLeftDerivedFunctor α W] (h : F.IsLeftDerivable W) (X : C) :
    F.IsLeftDerivedValueAt W X (derivedCounitCone F W L F' α X) :=
  have := F.hasPointwiseLeftDerivedFunctor_of_isLeftDerivable W h
  isLeftDerivedValueAt_of_isLimit F W X (h X) (isLimitDerivedCounitCone F W L F' α X)

/-- The two halves of the isomorphism attached to a morphism of `W` cancel after `F'`, in the
order that makes the projections of `CategoryTheory.Functor.derivedCounitCone` split `F'(L(a))`. -/
lemma map_isoOfHom_inv_comp_map {X' X : C} (a : X' ⟶ X) (ha : W a) :
    F'.map (Localization.isoOfHom L W a ha).inv ≫ F'.map (L.map a) = 𝟙 (F'.obj (L.obj X)) := by
  rw [← F'.map_comp, show L.map a = (Localization.isoOfHom L W a ha).hom from rfl,
    Iso.inv_hom_id, F'.map_id]

/-- **`(L ⋙ F')(f)` satisfies the characterisation of Tag 05SA(2)** relative to the comparison
cones: it is compatible with their projections along every square `a ≫ f = g ≫ b` whose vertical
sides `a` and `b` lie in `W`. -/
lemma map_comp_counit_eq {X Y X' Y' : C} (f : X ⟶ Y) (a : X' ⟶ X) (ha : W a)
    (b : Y' ⟶ Y) (hb : W b) (g : X' ⟶ Y') (hsq : a ≫ f = g ≫ b) :
    (L ⋙ F').map f ≫ (F'.map (Localization.isoOfHom L W b hb).inv ≫ α.app Y')
      = (F'.map (Localization.isoOfHom L W a ha).inv ≫ α.app X') ≫ F.map g := by
  have hL : L.map f ≫ (Localization.isoOfHom L W b hb).inv
      = (Localization.isoOfHom L W a ha).inv ≫ L.map g := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, Localization.isoOfHom_hom,
      Localization.isoOfHom_hom, ← L.map_comp, ← L.map_comp, hsq]
  have hnat : F'.map (L.map g) ≫ α.app Y' = α.app X' ≫ F.map g := α.naturality g
  rw [Functor.comp_map, ← Category.assoc, ← F'.map_comp, hL, F'.map_comp, Category.assoc,
    hnat, Category.assoc]

/-- **The third morphism of the triangle of values satisfies the characterisation of
Tag 05SC(2)**: `(L ⋙ F')(φ)` followed by the shift comparison of `L ⋙ F'` is compatible with the
projections of the comparison cones along every shifted square `a ≫ φ = h' ≫ b⟦1⟧'`. -/
lemma map_comp_commShiftIso_comp_counit_eq
    [HasShift C ℤ] [HasShift D ℤ] [HasShift H ℤ]
    [F.CommShift ℤ] [L.CommShift ℤ] [F'.CommShift ℤ] [NatTrans.CommShift α ℤ]
    {Z X R S : C} (φ : Z ⟶ X⟦(1 : ℤ)⟧)
    (a : R ⟶ Z) (ha : W a) (b : S ⟶ X) (hb : W b) (h' : R ⟶ S⟦(1 : ℤ)⟧)
    (hsq : a ≫ φ = h' ≫ b⟦(1 : ℤ)⟧') :
    ((L ⋙ F').map φ ≫ ((L ⋙ F').commShiftIso (1 : ℤ)).hom.app X) ≫
        (F'.map (Localization.isoOfHom L W b hb).inv ≫ α.app S)⟦(1 : ℤ)⟧'
      = (F'.map (Localization.isoOfHom L W a ha).inv ≫ α.app R) ≫ F.map h' ≫
          (F.commShiftIso (1 : ℤ)).hom.app S := by
  have hiso : IsIso (L.map a) := Localization.inverts L W a ha
  have hsplitZ := map_isoOfHom_inv_comp_map W L F' a ha
  have hsplitX := map_comp_map_isoOfHom_inv W L F' b hb
  have hcs := ((L ⋙ F').commShiftIso (1 : ℤ)).hom.naturality b
  have e₁ := NatTrans.shift_app_comm α (1 : ℤ) S
  have e₂ := α.naturality h'
  dsimp only [Functor.comp_obj, Functor.comp_map] at hcs e₁ e₂
  rw [← cancel_epi (F'.map (L.map a))]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  rw [← Category.assoc (F'.map (L.map a)) (F'.map (Localization.isoOfHom L W a ha).inv ≫
      α.app R), ← Category.assoc (F'.map (L.map a)) (F'.map (Localization.isoOfHom L W a ha).inv),
    map_comp_map_isoOfHom_inv W L F' a ha, Category.id_comp]
  simp only [Category.assoc]
  rw [← F'.map_comp_assoc, ← L.map_comp, hsq, L.map_comp, F'.map_comp, Category.assoc,
    reassoc_of% hcs, (shiftFunctor H (1 : ℤ)).map_comp,
    ← (shiftFunctor H (1 : ℤ)).map_comp_assoc, hsplitX, (shiftFunctor H (1 : ℤ)).map_id,
    Category.id_comp, e₁, reassoc_of% e₂]

/-- A morphism `u` between the vertices of the comparison cones at `X` and `Y` which is compatible
with their projections along every square over `f` is `(L ⋙ F')(f)`. -/
private theorem eq_map_of_forall_eq_counit [W.HasRightCalculusOfFractions]
    [F.HasPointwiseLeftDerivedFunctor W] [F'.IsLeftDerivedFunctor α W] {X Y : C} (f : X ⟶ Y)
    (u : F'.obj (L.obj X) ⟶ F'.obj (L.obj Y))
    (hu : ∀ (s : W.Over ⊤ X) (t : W.Over ⊤ Y) (f' : s.left ⟶ t.left), s.hom ≫ f = f' ≫ t.hom →
      u ≫ (derivedCounitCone F W L F' α Y).π.app t
        = (derivedCounitCone F W L F' α X).π.app s ≫ F.map f') :
    u = (L ⋙ F').map f := by
  refine (isLimitDerivedCounitCone F W L F' α Y).hom_ext fun c => ?_
  obtain ⟨ψ, hψ⟩ := MorphismProperty.HasRightCalculusOfFractions.exists_rightFraction
    (MorphismProperty.LeftFraction.mk (W := W) (X := X) (Y := c.left) f
      (show c.left ⟶ Y from c.hom) c.prop)
  exact (hu (MorphismProperty.Over.mk ⊤ ψ.s ψ.hs) c ψ.f hψ).trans
    (map_comp_counit_eq F W L F' α f _ ψ.hs _ c.prop ψ.f hψ).symm

end LeftValue

section LeftExact

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {H : Type u₃} [Category.{v₃} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]

/-- **An everywhere defined left derived functor, composed with the localization, is exact.**
For a distinguished triangle `T` of `𝒞`, Tag 05SC produces morphisms between the values of `LF`
at the three vertices forming a distinguished triangle; they are `(L ⋙ F')` of the three
morphisms of `T` — the third read through the shift comparison — because each is characterised by
compatibility with the projections and the characterisation determines it, a value being a
limit cone. -/
theorem isTriangulated_comp_of_isLeftDerivable
    (F : C ⥤ H) [F.CommShift ℤ] [F.IsTriangulated]
    (W : MorphismProperty C) [W.IsCompatibleWithTriangulation]
    (L : C ⥤ D) [L.IsLocalization W] [L.CommShift ℤ] [L.IsTriangulated]
    (F' : D ⥤ H) [F'.CommShift ℤ] (α : L ⋙ F' ⟶ F) [NatTrans.CommShift α ℤ]
    [F'.IsLeftDerivedFunctor α W] (hW : W.IsSaturated)
    (h : F.IsLeftDerivable W) : (L ⋙ F').IsTriangulated := by
  have := hW.hasRightCalculusOfFractions
  have := F.hasPointwiseLeftDerivedFunctor_of_isLeftDerivable W h
  constructor
  intro T hT
  obtain ⟨u, v, w, hdist, hu, hv, hw⟩ :=
    (F.exists_isRightDerivedValueAt_and_isLeftDerivedValueAt_and_triangle_distinguished W hW
        T hT).2.2.2.2
      (derivedCounitCone F W L F' α T.obj₁)
      (isLeftDerivedValueAt_derivedCounitCone F W L F' α h T.obj₁)
      (derivedCounitCone F W L F' α T.obj₂)
      (isLeftDerivedValueAt_derivedCounitCone F W L F' α h T.obj₂)
      (derivedCounitCone F W L F' α T.obj₃)
      (isLeftDerivedValueAt_derivedCounitCone F W L F' α h T.obj₃)
  have heu : u = (L ⋙ F').map T.mor₁ :=
    eq_map_of_forall_eq_counit F W L F' α T.mor₁ u hu
  have hev : v = (L ⋙ F').map T.mor₂ :=
    eq_map_of_forall_eq_counit F W L F' α T.mor₂ v hv
  have hew : w = (L ⋙ F').map T.mor₃ ≫
      ((L ⋙ F').commShiftIso (1 : ℤ)).hom.app T.obj₁ := by
    refine (isLimitOfPreserves (shiftFunctor H (1 : ℤ))
      (isLimitDerivedCounitCone F W L F' α T.obj₁)).hom_ext fun c => ?_
    obtain ⟨ψ, hψ⟩ := MorphismProperty.HasRightCalculusOfFractions.exists_rightFraction
      (MorphismProperty.LeftFraction.mk (W := W) (X := T.obj₃) (Y := c.left⟦(1 : ℤ)⟧) T.mor₃
        ((show c.left ⟶ T.obj₁ from c.hom)⟦(1 : ℤ)⟧')
        ((MorphismProperty.IsCompatibleWithShift.iff W _ (1 : ℤ)).2 c.prop))
    exact (hw (MorphismProperty.Over.mk ⊤ ψ.s ψ.hs) c ψ.f hψ).trans
      (map_comp_commShiftIso_comp_counit_eq F W L F' α T.mor₃ _ ψ.hs _ c.prop ψ.f hψ).symm
  have hmk : Pretriangulated.Triangle.mk u v w = (L ⋙ F').mapTriangle.obj T := by
    rw [heu, hev, hew]
    exact (Functor.mapTriangle_obj (L ⋙ F') T).symm
  exact hmk ▸ hdist

/-- **An everywhere defined left derived functor is exact.** Let `F : 𝒞 ⥤ ℋ` be an exact functor
of pre-triangulated categories, let `W` be a saturated multiplicative system of morphisms of `𝒞`
compatible with the triangulation, let `L : 𝒞 ⥤ 𝒟` be a localization functor for `W`, and let
`F'` be a left derived functor of `F` along `L`, with comparison `α`. If the left derived
functor is defined at every object of `𝒞` (Tag 05SV), then `F'` is exact. -/
theorem isTriangulated_of_isLeftDerivable
    (F : C ⥤ H) [F.CommShift ℤ] [F.IsTriangulated]
    (W : MorphismProperty C) [W.IsCompatibleWithTriangulation]
    (L : C ⥤ D) [L.IsLocalization W] [L.CommShift ℤ] [L.IsTriangulated]
    (F' : D ⥤ H) [F'.CommShift ℤ] (α : L ⋙ F' ⟶ F) [NatTrans.CommShift α ℤ]
    [F'.IsLeftDerivedFunctor α W] (hW : W.IsSaturated) (h : F.IsLeftDerivable W) :
    F'.IsTriangulated :=
  have := hW.hasLeftCalculusOfFractions
  have := Localization.essSurj_mapArrow L W
  have := isTriangulated_comp_of_isLeftDerivable F W L F' α hW h
  Functor.isTriangulated_of_precomp L F'

end LeftExact

end CategoryTheory.Functor

end
