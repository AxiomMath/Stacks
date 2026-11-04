module

public import StacksFrontier.Homology.FilteredDerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.AcyclicHomotopy
public import StacksFrontier.Homology.FilteredDerivedCategory.InjectiveResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# The filtered derived category is triangulated

Let `𝒜` be an abelian category. The filtered derived category `DF(𝒜)`, the localisation of
`K(Fil^f(𝒜))` at the filtered quasi-isomorphisms `FQis(𝒜)`, is triangulated and the
localisation functor `Qh : K(Fil^f(𝒜)) ⥤ DF(𝒜)` is exact. The bounded parts `DF⁺(𝒜)`, `DF⁻(𝒜)`,
`DFᵇ(𝒜)` are triangulated subcategories, and the functors to them from `K⁺`, `K⁻`, `Kᵇ` are exact
localisations.

A bounded below complex of filtered injective objects admits no nonzero map from a filtered
acyclic complex. If `𝒜` has enough injectives, the functor `K⁺(I^f) ⥤ DF⁺(𝒜)` is an equivalence
of triangulated categories, compatible with `gr^p` and `forget F`.

## Main definitions

* `CochainComplex.FilteredDerivedCategory.filteredInjectivePlus`: the full subcategory `K⁺(I^f)`
  of bounded below complexes of filtered injective objects.
* `CochainComplex.FilteredDerivedCategory.toPlus`: the functor `K⁺(I^f) ⥤ DF⁺(𝒜)`.
* `CochainComplex.FilteredDerivedCategory.grDF` and
  `CochainComplex.FilteredDerivedCategory.forgetDF`: the functors `gr^p, forget F : DF(𝒜) ⥤ D(𝒜)`.

## Main results

* `CochainComplex.FilteredDerivedCategory.isTriangulated_isLocalization_Qplus_Qminus_Qbounded`:
  the functors `K⁺ ⥤ DF⁺(𝒜)`, `K⁻ ⥤ DF⁻(𝒜)`, `Kᵇ ⥤ DFᵇ(𝒜)` are exact localisations.
* `CochainComplex.FilteredDerivedCategory.rightOrthogonal_of_filteredInjectivePlus`: a bounded
  below complex of filtered injective objects is right orthogonal to the filtered acyclic
  complexes.
* `CochainComplex.FilteredDerivedCategory.isEquivalence_isTriangulated_toPlus_and_squares`:
  `K⁺(I^f) ⥤ DF⁺(𝒜)` is an exact equivalence, compatible with `gr^p` and `forget F`.

## References

* [Stacks Project, Tag 05S2](https://stacks.math.columbia.edu/tag/05S2)
* [Stacks Project, Tag 05S6](https://stacks.math.columbia.edu/tag/05S6)
* [Stacks Project, Tag 05TX](https://stacks.math.columbia.edu/tag/05TX)
* [Stacks Project, Tag 05TW](https://stacks.math.columbia.edu/tag/05TW)
* [Stacks Project, Tag 015Q](https://stacks.math.columbia.edu/tag/015Q)
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Pretriangulated Opposite HomologicalComplex

noncomputable section

namespace CochainComplex.FilteredDerivedCategory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- `Qh` is a localization at the morphisms whose cone is filtered acyclic. -/
instance isLocalization_Qh_trW :
    (Qh (𝒜 := 𝒜)).IsLocalization (HomotopyCategory.filteredAcyclic 𝒜).trW := by
  rw [HomotopyCategory.filteredAcyclic_trW]
  infer_instance

/-- The filtered derived category is preadditive. -/
instance : Preadditive (FilteredDerivedCategory 𝒜) :=
  Localization.preadditive Qh (HomotopyCategory.filteredAcyclic 𝒜).trW

/-- The localization functor `Qh` is additive. -/
instance : (Qh (𝒜 := 𝒜)).Additive :=
  Localization.functor_additive Qh (HomotopyCategory.filteredAcyclic 𝒜).trW

/-- The filtered derived category has a zero object. -/
instance : HasZeroObject (FilteredDerivedCategory 𝒜) :=
  Qh.hasZeroObject_of_additive

/-- The shift on the filtered derived category induced by that of `K(Fil^f(𝒜))`. -/
instance : HasShift (FilteredDerivedCategory 𝒜) ℤ :=
  HasShift.localized Qh (HomotopyCategory.filteredAcyclic 𝒜).trW ℤ

/-- The localization functor `Qh` commutes with the shifts. -/
instance : (Qh (𝒜 := 𝒜)).CommShift ℤ :=
  Functor.CommShift.localized Qh (HomotopyCategory.filteredAcyclic 𝒜).trW ℤ

/-- The shift functors of the filtered derived category are additive. -/
instance (n : ℤ) : (CategoryTheory.shiftFunctor (FilteredDerivedCategory 𝒜) n).Additive :=
  (Localization.functor_additive_iff Qh (HomotopyCategory.filteredAcyclic 𝒜).trW _).2
    (Functor.additive_of_iso (Qh.commShiftIso n))

/-- The filtered derived category is pretriangulated. -/
instance : Pretriangulated (FilteredDerivedCategory 𝒜) :=
  Triangulated.Localization.pretriangulated Qh (HomotopyCategory.filteredAcyclic 𝒜).trW

/-- The localization functor `Qh` is a triangulated functor. -/
instance : (Qh (𝒜 := 𝒜)).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor Qh (HomotopyCategory.filteredAcyclic 𝒜).trW

/-- The filtered derived category is triangulated. -/
instance : IsTriangulated (FilteredDerivedCategory 𝒜) :=
  Triangulated.Localization.isTriangulated Qh (HomotopyCategory.filteredAcyclic 𝒜).trW


/-! ### `DF⁺(𝒜)` is a triangulated subcategory -/

/-- Every object of `DF⁺(𝒜)` is the image under `Qh` of an object of `K⁺(Fil^f(𝒜))`. -/
lemma exists_Qh_obj_iso_of_plus {Y : FilteredDerivedCategory 𝒜} (hY : plus 𝒜 Y) :
    ∃ X : HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ), HomotopyCategory.plus _ X ∧
      Nonempty (Qh.obj X ≅ Y) := by
  obtain ⟨X, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := Qplus (𝒜 := 𝒜)) ⟨Y, hY⟩
  exact ⟨X.obj, X.property, ⟨(plus 𝒜).ι.mapIso e⟩⟩

/-- `DF⁺(𝒜)` is closed under isomorphisms. -/
instance : (plus 𝒜).IsClosedUnderIsomorphisms := by
  unfold plus; infer_instance

/-- `DF⁺(𝒜)` contains a zero object. -/
instance : (plus 𝒜).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ, hZ'⟩ :=
      (HomotopyCategory.plus (FiniteFilteredObject 𝒜)).exists_prop_of_containsZero
    exact ⟨_, Qh.map_isZero hZ, plus_Qh_obj_of_plus hZ'⟩

/-- `DF⁺(𝒜)` is stable under the shifts. -/
instance : (plus 𝒜).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun Y hY ↦ by
    obtain ⟨X, hX, ⟨e⟩⟩ := exists_Qh_obj_iso_of_plus hY
    exact (plus 𝒜).prop_of_iso
      ((Qh.commShiftIso n).app X ≪≫ (CategoryTheory.shiftFunctor _ n).mapIso e)
      (plus_Qh_obj_of_plus ((HomotopyCategory.plus _).le_shift n X hX))⟩

/-- `DF⁺(𝒜)` contains the third object of a distinguished triangle whose first two objects
lie in it. -/
instance : (plus 𝒜).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    obtain ⟨X₁, hX₁, ⟨e₁⟩⟩ := exists_Qh_obj_iso_of_plus h₁
    obtain ⟨X₂, hX₂, ⟨e₂⟩⟩ := exists_Qh_obj_iso_of_plus h₂
    obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction Qh
      (HomotopyCategory.filteredAcyclic 𝒜).trW (e₁.hom ≫ T.mor₁ ≫ e₂.inv)
    obtain ⟨Z, s', b, hZ, hs', hsb⟩ :=
      (ObjectProperty.isVerdierRightLocalizing_iff _ _).1 inferInstance φ.s hX₂ φ.hs
    have hs'' : (HomotopyCategory.filteredAcyclic 𝒜).trW s' :=
      ObjectProperty.trW_monotone inf_le_right _ hs'
    have : IsIso (Qh.map φ.s) := Localization.inverts Qh _ _ φ.hs
    obtain ⟨W, v, w, hT'⟩ := Pretriangulated.distinguished_cocone_triangle (φ.f ≫ b)
    obtain ⟨W', hW', ⟨eW⟩⟩ :=
      (HomotopyCategory.plus _).ext_of_isTriangulatedClosed₃' _ hT' hX₁ hZ
    have h' : T.mor₁ ≫ e₂.inv = e₁.inv ≫ Qh.map φ.f ≫ inv (Qh.map φ.s) := by
      rw [← cancel_epi e₁.hom, e₁.hom_inv_id_assoc, hφ]
      simp only [MorphismProperty.LeftFraction.map]
    refine (plus 𝒜).le_isoClosure _ <| (plus 𝒜).prop_of_iso
      (Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT (Qh.map_distinguished _ hT') e₁.symm
        (e₂.symm ≪≫ Localization.isoOfHom Qh _ s' hs'') ?_) ≪≫ Qh.mapIso eW).symm
      (plus_Qh_obj_of_plus hW')
    change T.mor₁ ≫ e₂.inv ≫ Qh.map s' = e₁.inv ≫ Qh.map (φ.f ≫ b)
    rw [reassoc_of% h', ← hsb, Functor.map_comp, IsIso.inv_hom_id_assoc, Functor.map_comp]

/-- `DF⁺(𝒜)` is a triangulated subcategory. -/
instance : (plus 𝒜).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃


/-! ### `DF⁻(𝒜)` and `DFᵇ(𝒜)` are triangulated subcategories -/

/-- Every object of `DF⁻(𝒜)` is the image under `Qh` of an object of `K⁻(Fil^f(𝒜))`. -/
lemma exists_Qh_obj_iso_of_minus {Y : FilteredDerivedCategory 𝒜} (hY : minus 𝒜 Y) :
    ∃ X : HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ), Kminus X ∧
      Nonempty (Qh.obj X ≅ Y) := by
  obtain ⟨X, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := Qminus (𝒜 := 𝒜)) ⟨Y, hY⟩
  exact ⟨X.obj, X.property, ⟨(minus 𝒜).ι.mapIso e⟩⟩

/-- `DF⁻(𝒜)` is closed under isomorphisms. -/
instance : (minus 𝒜).IsClosedUnderIsomorphisms := by
  unfold minus; infer_instance

/-- `DF⁻(𝒜)` contains a zero object. -/
instance : (minus 𝒜).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ, hZ'⟩ := (Kminus (𝒜 := 𝒜)).exists_prop_of_containsZero
    exact ⟨_, Qh.map_isZero hZ, minus_Qh_obj_of_minus hZ'⟩

/-- `DF⁻(𝒜)` is stable under the shifts. -/
instance : (minus 𝒜).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun Y hY ↦ by
    obtain ⟨X, hX, ⟨e⟩⟩ := exists_Qh_obj_iso_of_minus hY
    exact (minus 𝒜).prop_of_iso
      ((Qh.commShiftIso n).app X ≪≫ (CategoryTheory.shiftFunctor _ n).mapIso e)
      (minus_Qh_obj_of_minus ((Kminus (𝒜 := 𝒜)).le_shift n X hX))⟩

/-- `DF⁻(𝒜)` contains the third object of a distinguished triangle whose first two objects
lie in it. -/
instance : (minus 𝒜).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    obtain ⟨X₁, hX₁, ⟨e₁⟩⟩ := exists_Qh_obj_iso_of_minus h₁
    obtain ⟨X₂, hX₂, ⟨e₂⟩⟩ := exists_Qh_obj_iso_of_minus h₂
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction Qh
      (HomotopyCategory.filteredAcyclic 𝒜).trW (e₁.hom ≫ T.mor₁ ≫ e₂.inv)
    obtain ⟨Z, s', b, hZ, hs', hbs⟩ :=
      (ObjectProperty.isVerdierLeftLocalizing_iff _ _).1 inferInstance φ.s hX₁ φ.hs
    have hs'' : (HomotopyCategory.filteredAcyclic 𝒜).trW s' :=
      ObjectProperty.trW_monotone inf_le_right _ hs'
    have : IsIso (Qh.map φ.s) := Localization.inverts Qh _ _ φ.hs
    have : IsIso (Qh.map s') := Localization.inverts Qh _ _ hs''
    obtain ⟨W, v, w, hT'⟩ := Pretriangulated.distinguished_cocone_triangle (b ≫ φ.f)
    obtain ⟨W', hW', ⟨eW⟩⟩ :=
      (Kminus (𝒜 := 𝒜)).ext_of_isTriangulatedClosed₃' _ hT' hZ hX₂
    have h' : T.mor₁ ≫ e₂.inv = e₁.inv ≫ inv (Qh.map φ.s) ≫ Qh.map φ.f := by
      rw [← cancel_epi e₁.hom, e₁.hom_inv_id_assoc, hφ]
      simp only [MorphismProperty.RightFraction.map]
    have hb : inv (Qh.map s') ≫ Qh.map b = inv (Qh.map φ.s) := by
      rw [IsIso.inv_comp_eq, ← hbs, Functor.map_comp, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
    refine (minus 𝒜).le_isoClosure _ <| (minus 𝒜).prop_of_iso
      (Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT (Qh.map_distinguished _ hT')
        (e₁.symm ≪≫ (asIso (Qh.map s')).symm) e₂.symm ?_) ≪≫ Qh.mapIso eW).symm
      (minus_Qh_obj_of_minus hW')
    change T.mor₁ ≫ e₂.inv = (e₁.inv ≫ inv (Qh.map s')) ≫ Qh.map (b ≫ φ.f)
    rw [h', Functor.map_comp, Category.assoc, reassoc_of% hb]

/-- `DF⁻(𝒜)` is a triangulated subcategory. -/
instance : (minus 𝒜).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- The cohomology `H^i(gr^p(-))` descends to `DF(𝒜)`: isomorphic objects of `DF(𝒜)` have
isomorphic `H^i(gr^p(-))`. -/
private noncomputable def homologyGrPIso (p i : ℤ)
    {X X' : HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ)} (e : Qh.obj X ≅ Qh.obj X') :
    (((FiniteFilteredObject.grP p).mapHomotopyCategory _ ⋙
        HomotopyCategory.homologyFunctor 𝒜 _ i).obj X) ≅
      (((FiniteFilteredObject.grP p).mapHomotopyCategory _ ⋙
        HomotopyCategory.homologyFunctor 𝒜 _ i).obj X') :=
  have hH : (HomotopyCategory.filteredQuasiIso 𝒜).IsInvertedBy
      ((FiniteFilteredObject.grP p).mapHomotopyCategory _ ⋙
        HomotopyCategory.homologyFunctor 𝒜 _ i) := fun _ _ _ hf ↦ hf p i
  ((Localization.fac _ hH Qh).app X).symm ≪≫ (Localization.lift _ hH Qh).mapIso e ≪≫
    (Localization.fac _ hH Qh).app X'

/-- `DFᵇ(𝒜)` is the intersection of `DF⁺(𝒜)` and `DF⁻(𝒜)`. -/
lemma bounded_eq_plus_inf_minus : bounded 𝒜 = plus 𝒜 ⊓ minus 𝒜 := by
  ext Y
  refine ⟨fun ⟨K, ⟨hp, hm⟩, ⟨e⟩⟩ ↦ ⟨⟨K, hp, ⟨e⟩⟩, ⟨K, hm, ⟨e⟩⟩⟩, fun ⟨hp, hm⟩ ↦ ?_⟩
  obtain ⟨X', hX', ⟨e'⟩⟩ := exists_Qh_obj_iso_of_plus hp
  obtain ⟨X, hX, ⟨e⟩⟩ := exists_Qh_obj_iso_of_minus hm
  obtain ⟨K', ⟨a, _⟩, rfl⟩ := (ObjectProperty.strictMap_iff _ _ _).1 hX'
  obtain ⟨K, ⟨b, _⟩, rfl⟩ := (ObjectProperty.strictMap_iff _ _ _).1 hX
  have hGE : ∀ p,
      CochainComplex.IsGE (((FiniteFilteredObject.grP p).mapHomologicalComplex _).obj K) a :=
    fun p ↦ by
      rw [isGE_iff]
      intro i hi
      have := isStrictlyGE_grP K' a p
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact IsZero.of_iso ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1
          (CochainComplex.exactAt_of_isGE
            (((FiniteFilteredObject.grP p).mapHomologicalComplex _).obj K') a i hi))
        (((HomotopyCategory.homologyFunctorFactors 𝒜 _ i).app _).symm ≪≫
          homologyGrPIso p i (e ≪≫ e'.symm) ≪≫
            (HomotopyCategory.homologyFunctorFactors 𝒜 _ i).app _)
  exact ⟨toFilf.obj K,
    ⟨⟨a, fun p ↦ by
        have := hGE p
        exact isGE_of_iso ((grIso p).app K).symm a⟩,
      ⟨b, fun p ↦ by
        have := isStrictlyLE_grP K b p
        exact isLE_of_iso ((grIso p).app K).symm b⟩⟩,
    ⟨(quotientCompQhIso.app K).symm ≪≫ e⟩⟩

/-- `DFᵇ(𝒜)` is a triangulated subcategory. -/
instance : (bounded 𝒜).IsTriangulated := by
  rw [bounded_eq_plus_inf_minus]
  infer_instance

/-- The functors `K⁺(Fil^f(𝒜)) ⥤ DF⁺(𝒜)`, `K⁻(Fil^f(𝒜)) ⥤ DF⁻(𝒜)`
and `Kᵇ(Fil^f(𝒜)) ⥤ DFᵇ(𝒜)` induced by `Qh` are exact localisations at `FQis⁺(𝒜)`,
`FQis⁻(𝒜)`, `FQisᵇ(𝒜)`: so the induced equivalences
`FQis^*(𝒜)⁻¹K^*(Fil^f(𝒜)) ⥤ DF^*(𝒜)` are equivalences of triangulated categories. -/
@[stacks 05S6 "the equivalences are equivalences of triangulated categories"]
theorem isTriangulated_isLocalization_Qplus_Qminus_Qbounded :
    ((Qplus (𝒜 := 𝒜)).IsTriangulated ∧ (Qplus (𝒜 := 𝒜)).IsLocalization
        ((HomotopyCategory.filteredQuasiIso 𝒜).inverseImage (HomotopyCategory.Plus.ι _))) ∧
      ((Qminus (𝒜 := 𝒜)).IsTriangulated ∧ (Qminus (𝒜 := 𝒜)).IsLocalization
        ((HomotopyCategory.filteredQuasiIso 𝒜).inverseImage (Kminus (𝒜 := 𝒜)).ι)) ∧
      ((Qbounded (𝒜 := 𝒜)).IsTriangulated ∧ (Qbounded (𝒜 := 𝒜)).IsLocalization
        ((HomotopyCategory.filteredQuasiIso 𝒜).inverseImage (Kbounded (𝒜 := 𝒜)).ι)) :=
  ⟨⟨inferInstance, isLocalization_Qplus⟩, ⟨inferInstance, isLocalization_Qminus⟩,
    ⟨inferInstance, isLocalization_Qbounded⟩⟩

/-! ### `K⁺(I^f)` -/

/-- An additive functor `Fil^f(𝒜) ⥤ 𝒜` carries a strictly `≥ a` complex to a strictly `≥ a`
complex. -/
private theorem isStrictlyGE_map_of_additive (G : FiniteFilteredObject 𝒜 ⥤ 𝒜) [G.Additive]
    (K : CochainComplex (FiniteFilteredObject 𝒜) ℤ) (a : ℤ) [K.IsStrictlyGE a] :
    CochainComplex.IsStrictlyGE ((G.mapHomologicalComplex _).obj K) a := by
  rw [isStrictlyGE_iff]
  intro i hi
  exact G.map_isZero (K.isZero_of_isStrictlyGE a i hi)

/-- The graded pieces of the filtered complex attached to a complex of filtered injective objects
are injective. -/
private theorem injective_gr_toFilf_X {J : CochainComplex (FiniteFilteredObject 𝒜) ℤ}
    (hJ : ∀ n p, Injective ((FiniteFilteredObject.grP p).obj (J.X n))) (p n : ℤ) :
    Injective (((FilteredObject.gr p).obj (toFilf.obj J).obj).X n) :=
  Injective.of_iso (HomologicalComplex.Hom.isoApp ((grIso p).app J) n).symm (hJ n p)

variable (𝒜) in
/-- The bounded below complexes of filtered injective objects of `Fil^f(𝒜)`: complexes `I^•`
with `I^n = 0` for `n ≪ 0` all of whose terms are filtered injective, i.e. have injective graded
pieces `gr^p(I^n)` ([Stacks, Tag 015P]). -/
def filteredInjectivePlusC : ObjectProperty (CochainComplex (FiniteFilteredObject 𝒜) ℤ) :=
  fun K => (∃ a : ℤ, K.IsStrictlyGE a) ∧
    ∀ n p : ℤ, Injective ((FiniteFilteredObject.grP p).obj (K.X n))

variable (𝒜) in
/-- `K⁺(I^f)`: the full subcategory of `K(Fil^f(𝒜))` on the bounded below complexes of filtered
injective objects. -/
def filteredInjectivePlus :
    ObjectProperty (HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ)) :=
  (filteredInjectivePlusC 𝒜).strictMap (HomotopyCategory.quotient _ _)

/-- `K⁺(I^f)` is a triangulated subcategory of `K(Fil^f(𝒜))`. -/
instance : (filteredInjectivePlus 𝒜).IsTriangulated :=
  HomotopyCategory.isTriangulated_strictMap_quotient _
    ⟨⟨0, inferInstance⟩, fun n p ↦ ((FiniteFilteredObject.grP p).map_isZero
      ((HomologicalComplex.eval _ _ n).map_isZero (isZero_zero _))).injective⟩
    (fun K n hK ↦ by
      obtain ⟨⟨a, _⟩, h⟩ := hK
      exact ⟨⟨a - n, K.isStrictlyGE_shift a n (a - n) (by lia)⟩, fun m p ↦ h (m + n) p⟩)
    (fun {K L} f hK hL ↦ by
      obtain ⟨⟨a, _⟩, hK⟩ := hK
      obtain ⟨⟨b, _⟩, hL⟩ := hL
      refine ⟨⟨min (a - 1) b, CochainComplex.isStrictlyGE_mappingCone f a b _ (by lia) (by lia)⟩,
        fun n p ↦ ?_⟩
      have := hK (n + 1) p
      have := hL n p
      have : PreservesBinaryBiproducts (FiniteFilteredObject.grP (𝒜 := 𝒜) p) :=
        preservesBinaryBiproducts_of_preservesBinaryProducts _
      exact Injective.of_iso ((FiniteFilteredObject.grP p).mapIso
        (homotopyCofiber.XIsoBiprod f n (n + 1) rfl) ≪≫
          (FiniteFilteredObject.grP p).mapBiprod _ _).symm inferInstance)

/-- Bounded below complexes of filtered injective objects are bounded below. -/
lemma filteredInjectivePlus_le_plus :
    filteredInjectivePlus 𝒜 ≤ HomotopyCategory.plus (FiniteFilteredObject 𝒜) := by
  intro X hX
  obtain ⟨K, ⟨hK, -⟩, rfl⟩ := (ObjectProperty.strictMap_iff _ _ _).1 hX
  exact (HomotopyCategory.plus_quotient_obj_iff K).2 hK

/-- There are no nonzero morphisms from a filtered
acyclic complex to a bounded below complex of filtered injective objects. -/
lemma rightOrthogonal_of_filteredInjectivePlus
    {I : HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ)} (hI : filteredInjectivePlus 𝒜 I) :
    (HomotopyCategory.filteredAcyclic 𝒜).rightOrthogonal I := by
  intro X f hX
  obtain ⟨J, ⟨⟨a, _⟩, hJ⟩, rfl⟩ := (ObjectProperty.strictMap_iff _ _ _).1 hI
  obtain ⟨K, rfl⟩ := X.quotient_obj_surjective
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
  have : (toFilf.obj J).obj.X.IsStrictlyGE a :=
    isStrictlyGE_map_of_additive FiniteFilteredObject.forget J a
  have hK : filteredAcyclic 𝒜 (toFilf.obj K).obj := fun p n ↦ by
    have : HomotopyCategory.subcategoryAcyclic 𝒜 ((HomotopyCategory.quotient _ _).obj
        (((FiniteFilteredObject.grP p).mapHomologicalComplex _).obj K)) :=
      (HomotopyCategory.filteredAcyclic_iff _).1 hX p
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_exactAt] at this
    exact (this n).of_iso ((grIso p).app K).symm
  have hIinj : ∀ n, (evalFil (toFilf.obj J).obj n).IsFilteredInjective := fun n ↦
    (isFilteredInjective_evalFil_iff _ n).2 ⟨(toFilf.obj J).property n,
      fun p ↦ injective_gr_toFilf_X hJ p n⟩
  obtain ⟨h, hh⟩ := exists_homotopy_zero_of_filteredAcyclic_of_injective_gradedPiece
    (toFilf.map g).hom a hK (toFilf.obj K).property hIinj
  rw [← (HomotopyCategory.quotient _ _).map_zero]
  let F : FiniteFilteredObject 𝒜 ⥤ 𝒜 := FiniteFilteredObject.forget
  exact HomotopyCategory.eq_of_homotopy _ _
    { hom i j := ObjectProperty.homMk (FilteredObject.homMk (h.hom i j)
        (fun q ↦ (hh i j q.unop).choose) (fun q ↦ (hh i j q.unop).choose_spec))
      zero i j hij := F.map_injective (by rw [Functor.map_zero]; exact h.zero i j hij)
      comm i := F.map_injective (by
        have := h.comm i
        rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
          prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp),
          HomologicalComplex.zero_f, add_zero] at this ⊢
        rwa [Functor.map_add, Functor.map_comp, Functor.map_comp]) }


/-! ### The equivalence `K⁺(I^f) ≃ DF⁺(𝒜)` -/

variable (𝒜) in
/-- The functor `K⁺(I^f) ⥤ DF⁺(𝒜)` induced by the localisation functor `Qh`. -/
noncomputable abbrev toPlus :
    (filteredInjectivePlus 𝒜).FullSubcategory ⥤ (plus 𝒜).FullSubcategory :=
  (plus 𝒜).lift ((filteredInjectivePlus 𝒜).ι ⋙ Qh)
    (fun X => plus_Qh_obj_of_plus (filteredInjectivePlus_le_plus _ X.property))

/-- `Qh` is bijective on morphisms into a bounded below complex of filtered injective objects. -/
lemma map_bijective_Qh_of_filteredInjectivePlus
    (X : HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ))
    {I : HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ)} (hI : filteredInjectivePlus 𝒜 I) :
    Function.Bijective (Qh.map : (X ⟶ I) → _) :=
  (rightOrthogonal_of_filteredInjectivePlus hI).map_bijective_of_isTriangulated Qh X

/-- `K⁺(I^f) ⥤ DF⁺(𝒜)` is faithful. -/
instance : (toPlus 𝒜).Faithful where
  map_injective {X Y} f g h := by
    ext
    exact (map_bijective_Qh_of_filteredInjectivePlus X.obj Y.property).1
      (congrArg (fun φ ↦ φ.hom) h :)

/-- `K⁺(I^f) ⥤ DF⁺(𝒜)` is full. -/
instance : (toPlus 𝒜).Full where
  map_surjective {X Y} φ := by
    obtain ⟨f, hf⟩ := (map_bijective_Qh_of_filteredInjectivePlus X.obj Y.property).2 φ.hom
    exact ⟨ObjectProperty.homMk f, by ext; exact hf⟩

/-- If `𝒜` has enough injectives, `K⁺(I^f) ⥤ DF⁺(𝒜)` is essentially surjective. -/
instance [EnoughInjectives 𝒜] : (toPlus 𝒜).EssSurj where
  mem_essImage Y := by
    obtain ⟨X, hX, ⟨e⟩⟩ := exists_Qh_obj_iso_of_plus Y.property
    obtain ⟨K, ⟨a, _⟩, rfl⟩ := (ObjectProperty.strictMap_iff _ _ _).1 hX
    have : (toFilf.obj K).obj.X.IsStrictlyGE a := by
      rw [isStrictlyGE_iff]
      intro i hi
      exact FiniteFilteredObject.forget.map_isZero (K.isZero_of_isStrictlyGE a i hi)
    obtain ⟨I, α, hα, -, -, hIGE, hI⟩ :=
      exists_mono_isStrictHom_filteredQuasiIso_isStrictlyGE_injective_gradedPiece
        (toFilf.obj K).obj a (toFilf.obj K).property
    let I' : (Filf (𝒜 := 𝒜)).FullSubcategory :=
      ⟨I, fun n ↦ ((isFilteredInjective_evalFil_iff I n).1 (hI n)).1⟩
    have : I'.obj.X.IsStrictlyGE a := hIGE
    have := isStrictlyGE_ofFilf I' a
    have hJ : filteredInjectivePlus 𝒜 ((HomotopyCategory.quotient _ _).obj (ofFilf I')) :=
      ⟨_, ⟨⟨a, inferInstance⟩, fun n p ↦ (hI n).injective_gr p⟩⟩
    let t := toFilf.preimage (ObjectProperty.homMk α ≫ (toFilfOfFilfIso I').inv)
    have ht : HomotopyCategory.filteredQuasiIso 𝒜 ((HomotopyCategory.quotient _ _).map t) :=
      (filteredQuasiIso_quotient_map_iff t).2 (filteredQuasiIsoC_preimage (M := I') α hα)
    have : IsIso (Qh.map ((HomotopyCategory.quotient _ _).map t)) :=
      Localization.inverts Qh (HomotopyCategory.filteredQuasiIso 𝒜) _ ht
    exact ⟨⟨_, hJ⟩, ⟨(plus 𝒜).isoMk
      ((asIso (Qh.map ((HomotopyCategory.quotient _ _).map t))).symm ≪≫ e)⟩⟩

/-- If `𝒜` has enough injectives, `K⁺(I^f) ⥤ DF⁺(𝒜)` is an equivalence. -/
instance [EnoughInjectives 𝒜] : (toPlus 𝒜).IsEquivalence where

/-! ### The squares with `gr^p` and `forget F` -/

variable (𝒜) in
/-- The bounded below complexes of injective objects of `𝒜`. -/
def injectivePlusC : ObjectProperty (CochainComplex 𝒜 ℤ) :=
  fun K => (∃ a : ℤ, K.IsStrictlyGE a) ∧ ∀ n : ℤ, Injective (K.X n)

variable (𝒜) in
/-- `K⁺(I)`: the full subcategory of `K(𝒜)` on the bounded below complexes of injective objects. -/
def injectivePlus : ObjectProperty (HomotopyCategory 𝒜 (.up ℤ)) :=
  (injectivePlusC 𝒜).strictMap (HomotopyCategory.quotient _ _)

/-- Bounded below complexes of injective objects are bounded below. -/
lemma injectivePlus_le_plus : injectivePlus 𝒜 ≤ HomotopyCategory.plus 𝒜 := by
  intro X hX
  obtain ⟨K, ⟨hK, -⟩, rfl⟩ := (ObjectProperty.strictMap_iff _ _ _).1 hX
  exact (HomotopyCategory.plus_quotient_obj_iff K).2 hK

/-- An additive functor `Fil^f(𝒜) ⥤ 𝒜` carries `K⁺(Fil^f(𝒜))` into `K⁺(𝒜)`. -/
lemma plus_mapHomotopyCategory_obj (G : FiniteFilteredObject 𝒜 ⥤ 𝒜) [G.Additive]
    {X : HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ)} (hX : HomotopyCategory.plus _ X) :
    HomotopyCategory.plus 𝒜 ((G.mapHomotopyCategory _).obj X) := by
  obtain ⟨K, ⟨a, _⟩, rfl⟩ := (ObjectProperty.strictMap_iff _ _ _).1 hX
  exact (HomotopyCategory.plus_quotient_obj_iff ((G.mapHomologicalComplex _).obj K)).2
    ⟨a, isStrictlyGE_map_of_additive G K a⟩

/-- `gr^p` carries `K⁺(I^f)` into `K⁺(I)`. -/
lemma injectivePlus_grP_obj (p : ℤ) {X : HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ)}
    (hX : filteredInjectivePlus 𝒜 X) :
    injectivePlus 𝒜 (((FiniteFilteredObject.grP p).mapHomotopyCategory _).obj X) := by
  obtain ⟨J, ⟨⟨a, _⟩, hJ⟩, rfl⟩ := (ObjectProperty.strictMap_iff _ _ _).1 hX
  exact ⟨((FiniteFilteredObject.grP p).mapHomologicalComplex _).obj J,
    ⟨⟨a, isStrictlyGE_grP J a p⟩, fun n ↦ hJ n p⟩⟩

/-- `forget F` carries `K⁺(I^f)` into `K⁺(I)`: a filtered injective object is injective. -/
lemma injectivePlus_forget_obj {X : HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ)}
    (hX : filteredInjectivePlus 𝒜 X) :
    injectivePlus 𝒜 ((FiniteFilteredObject.forget.mapHomotopyCategory _).obj X) := by
  obtain ⟨J, ⟨⟨a, _⟩, hJ⟩, rfl⟩ := (ObjectProperty.strictMap_iff _ _ _).1 hX
  exact ⟨(FiniteFilteredObject.forget.mapHomologicalComplex _).obj J,
    ⟨⟨a, isStrictlyGE_map_of_additive _ J a⟩, fun n ↦
      Stacks.FilteredDerived.ForgetCommutes.injective_X_of_injective_gradedPiece
        (toFilf.obj J).obj (toFilf.obj J).property (fun p m ↦ injective_gr_toFilf_X hJ p m) n⟩⟩

variable [HasDerivedCategory.{w} 𝒜]

variable (𝒜) in
/-- The functor `K⁺(I) ⥤ D⁺(𝒜)`. -/
noncomputable abbrev injectivePlusQ : (injectivePlus 𝒜).FullSubcategory ⥤ DerivedCategory.Plus 𝒜 :=
  (HomotopyCategory.plus 𝒜).lift (injectivePlus 𝒜).ι (fun X => injectivePlus_le_plus _ X.property) ⋙
    DerivedCategory.Plus.Qh

/-- `gr^p` followed by the localization to `D(𝒜)` inverts the filtered quasi-isomorphisms. -/
lemma grP_inverts (p : ℤ) : (HomotopyCategory.filteredQuasiIso 𝒜).IsInvertedBy
    ((FiniteFilteredObject.grP p).mapHomotopyCategory _ ⋙ DerivedCategory.Qh) :=
  fun _ _ _ hf ↦ Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _ (hf p)

/-- `forget F` followed by the localization to `D(𝒜)` inverts the filtered
quasi-isomorphisms. -/
lemma forget_inverts : (HomotopyCategory.filteredQuasiIso 𝒜).IsInvertedBy
    (FiniteFilteredObject.forget.mapHomotopyCategory _ ⋙ DerivedCategory.Qh) := by
  rintro ⟨K⟩ ⟨L⟩ f hf
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
  have hg := (filteredQuasiIso_toFilf_map_iff g).2 ((filteredQuasiIso_quotient_map_iff g).1 hf)
  have : QuasiIso ((FiniteFilteredObject.forget.mapHomologicalComplex _).map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1
      ((isIso_Q_map_gradedPiece_and_forget_of_filteredQuasiIso _ hg).2
        (toFilf.obj K).property (toFilf.obj L).property)
  exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 this)

/-- The functor `DF(𝒜) ⥤ D(𝒜)` induced by an additive functor `G : Fil^f(𝒜) ⥤ 𝒜` sending
filtered quasi-isomorphisms to quasi-isomorphisms. -/
noncomputable abbrev liftDF (G : FiniteFilteredObject 𝒜 ⥤ 𝒜) [G.Additive]
    (hG : (HomotopyCategory.filteredQuasiIso 𝒜).IsInvertedBy
      (G.mapHomotopyCategory _ ⋙ DerivedCategory.Qh)) :
    FilteredDerivedCategory 𝒜 ⥤ DerivedCategory 𝒜 :=
  Localization.lift _ hG Qh

/-- The restriction `DF⁺(𝒜) ⥤ D⁺(𝒜)` of
`CochainComplex.FilteredDerivedCategory.liftDF`. -/
noncomputable abbrev liftDFPlus (G : FiniteFilteredObject 𝒜 ⥤ 𝒜) [G.Additive]
    (hG : (HomotopyCategory.filteredQuasiIso 𝒜).IsInvertedBy
      (G.mapHomotopyCategory _ ⋙ DerivedCategory.Qh)) :
    (plus 𝒜).FullSubcategory ⥤ DerivedCategory.Plus 𝒜 :=
  DerivedCategory.TStructure.t.plus.lift ((plus 𝒜).ι ⋙ liftDF G hG) (fun Y => by
    obtain ⟨X, hX, ⟨e⟩⟩ := exists_Qh_obj_iso_of_plus Y.property
    exact DerivedCategory.TStructure.t.plus.prop_of_iso
      (((Localization.fac _ hG Qh).app X).symm ≪≫ (liftDF G hG).mapIso e)
      (DerivedCategory.Plus.Qh.obj ⟨_, plus_mapHomotopyCategory_obj G hX⟩).property)

/-- `gr^p : DF(𝒜) ⥤ D(𝒜)`. -/
noncomputable abbrev grDF (p : ℤ) : FilteredDerivedCategory 𝒜 ⥤ DerivedCategory 𝒜 :=
  liftDF (FiniteFilteredObject.grP p) (grP_inverts p)

/-- `forget F : DF(𝒜) ⥤ D(𝒜)`. -/
noncomputable abbrev forgetDF : FilteredDerivedCategory 𝒜 ⥤ DerivedCategory 𝒜 :=
  liftDF FiniteFilteredObject.forget forget_inverts

/-- The square `Qh ⋙ liftDF G ≅ G ⋙ Qh`, restricted to `K⁺(I^f) ⥤ DF⁺(𝒜) ⥤ D⁺(𝒜)` and
`K⁺(I^f) ⥤ K⁺(I) ⥤ D⁺(𝒜)`. -/
noncomputable def toPlusCompLiftDFPlusIso (G : FiniteFilteredObject 𝒜 ⥤ 𝒜) [G.Additive]
    (hG : (HomotopyCategory.filteredQuasiIso 𝒜).IsInvertedBy
      (G.mapHomotopyCategory _ ⋙ DerivedCategory.Qh))
    (hGI : ∀ X, filteredInjectivePlus 𝒜 X → injectivePlus 𝒜 ((G.mapHomotopyCategory _).obj X)) :
    toPlus 𝒜 ⋙ liftDFPlus G hG ≅
      (injectivePlus 𝒜).lift ((filteredInjectivePlus 𝒜).ι ⋙ G.mapHomotopyCategory _)
        (fun X => hGI _ X.property) ⋙ injectivePlusQ 𝒜 :=
  (DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (filteredInjectivePlus 𝒜).ι (Localization.fac _ hG Qh))

/-- Let `𝒜` be an abelian category with enough injectives, let `I^f ⊂ Fil^f(𝒜)`
be the filtered injective objects and `I ⊂ 𝒜` the injective objects. The canonical functor
`K⁺(I^f) ⥤ DF⁺(𝒜)` is exact, fully faithful and essentially surjective, i.e. an equivalence of
triangulated categories. Furthermore the squares
```
K⁺(I^f) ──→ DF⁺(𝒜)          K⁺(I^f) ──→ DF⁺(𝒜)
  │gr^p        │gr^p           │forget F    │forget F
  ↓            ↓               ↓            ↓
K⁺(I) ────→ D⁺(𝒜)           K⁺(I) ────→ D⁺(𝒜)
```
commute. Here `gr^p, forget F : DF(𝒜) ⥤ D(𝒜)` are the functors induced by
`gr^p, forget F : K(Fil^f(𝒜)) ⥤ K(𝒜)`, as recorded by the isomorphisms
`Qh ⋙ gr^p ≅ gr^p ⋙ Q` and `Qh ⋙ forget F ≅ forget F ⋙ Q`. -/
@[stacks 015Q]
theorem isEquivalence_isTriangulated_toPlus_and_squares [EnoughInjectives 𝒜] :
    (toPlus 𝒜).IsEquivalence ∧ (toPlus 𝒜).IsTriangulated ∧
      (∀ p : ℤ, Nonempty (Qh (𝒜 := 𝒜) ⋙ grDF p ≅
          (FiniteFilteredObject.grP p).mapHomotopyCategory _ ⋙ DerivedCategory.Qh) ∧
        Nonempty (toPlus 𝒜 ⋙ liftDFPlus (FiniteFilteredObject.grP p) (grP_inverts p) ≅
          (injectivePlus 𝒜).lift ((filteredInjectivePlus 𝒜).ι ⋙
              (FiniteFilteredObject.grP p).mapHomotopyCategory _)
            (fun X => injectivePlus_grP_obj p X.property) ⋙ injectivePlusQ 𝒜)) ∧
      Nonempty (Qh (𝒜 := 𝒜) ⋙ forgetDF ≅
        FiniteFilteredObject.forget.mapHomotopyCategory _ ⋙ DerivedCategory.Qh) ∧
      Nonempty (toPlus 𝒜 ⋙ liftDFPlus FiniteFilteredObject.forget forget_inverts ≅
        (injectivePlus 𝒜).lift ((filteredInjectivePlus 𝒜).ι ⋙
            FiniteFilteredObject.forget.mapHomotopyCategory _)
          (fun X => injectivePlus_forget_obj X.property) ⋙ injectivePlusQ 𝒜) :=
  ⟨inferInstance, inferInstance,
    fun p ↦ ⟨⟨Localization.fac _ _ _⟩,
      ⟨toPlusCompLiftDFPlusIso _ _ (fun _ hX ↦ injectivePlus_grP_obj p hX)⟩⟩,
    ⟨Localization.fac _ _ _⟩,
    ⟨toPlusCompLiftDFPlusIso _ _ (fun _ hX ↦ injectivePlus_forget_obj hX)⟩⟩

end CochainComplex.FilteredDerivedCategory

end
