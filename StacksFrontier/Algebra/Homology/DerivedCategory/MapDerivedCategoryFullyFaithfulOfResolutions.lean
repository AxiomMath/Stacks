module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose

/-!
# Full faithfulness of an exact fully faithful functor on unbounded derived categories

Let `F : C₁ ⥤ C₂` be an exact, fully faithful functor between abelian categories. Suppose that
every cochain complex of `C₂` whose cohomology objects lie in the essential image of `F` receives
a quasi-isomorphism from the image under `F` of a complex of `C₁`. Then the induced functor
`F.mapDerivedCategory : D(C₁) ⥤ D(C₂)` is fully faithful, and an object of `D(C₂)` all of whose
cohomology objects lie in the essential image of `F` is in the essential image of
`F.mapDerivedCategory`. No boundedness is assumed. The resolution hypothesis is what a
Löwenheim–Skolem statement for sheaves (Stacks 0GYY) provides.

The argument is the calculus of right fractions. It is first proved for an arbitrary functor
`Φ : D₁ ⥤ D₂` between localizations `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` with calculus of right
fractions, together with a fully faithful `H : C₁ ⥤ C₂` and an isomorphism `L₁ ⋙ Φ ≅ H ⋙ L₂`.
The hypotheses are that `H` reflects the morphisms of the class and that every morphism of the
class with target in the image of `H` is dominated by one with source in that image. It is then
applied to `F.mapHomotopyCategory` and the localizations `DerivedCategory.Qh`.

## Main results

* `CategoryTheory.Localization.full_of_rightResolutions` and
  `CategoryTheory.Localization.faithful_of_rightResolutions`: the abstract statements.
* `CategoryTheory.Functor.mapDerivedCategory_full_of_resolutions`,
  `CategoryTheory.Functor.mapDerivedCategory_faithful_of_resolutions`: `F.mapDerivedCategory` is
  full and faithful.
* `CategoryTheory.Functor.exists_mapDerivedCategory_obj_iso_of_resolutions`: its essential image
  contains the objects with cohomology objects in the essential image of `F`.

## References

* [Stacks Project, Tag 0GYY](https://stacks.math.columbia.edu/tag/0GYY)
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.Localization

variable {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  (L₁ : C₁ ⥤ D₁) (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
  [W₁.HasRightCalculusOfFractions]
  (L₂ : C₂ ⥤ D₂) (W₂ : MorphismProperty C₂) [L₂.IsLocalization W₂]
  [W₂.HasRightCalculusOfFractions]
  (H : C₁ ⥤ C₂) [H.Full] [H.Faithful] (Φ : D₁ ⥤ D₂) (e : L₁ ⋙ Φ ≅ H ⋙ L₂)

omit [W₁.HasRightCalculusOfFractions] [H.Faithful] in
include e in
/-- `Φ` is surjective on morphisms between objects of the form `L₁.obj A`. -/
theorem map_surjective_of_rightResolutions
    (hW : ∀ {A B : C₁} (s : A ⟶ B), W₂ (H.map s) → W₁ s)
    (hres : ∀ {M : C₂} {K : C₁} (s : M ⟶ H.obj K), W₂ s →
      ∃ (N : C₁) (u : H.obj N ⟶ M), W₂ (u ≫ s))
    {A B : C₁} (φ : Φ.obj (L₁.obj A) ⟶ Φ.obj (L₁.obj B)) :
    ∃ g : L₁.obj A ⟶ L₁.obj B, Φ.map g = φ := by
  obtain ⟨ψ, hψ⟩ := Localization.exists_rightFraction L₂ W₂
    (e.inv.app A ≫ φ ≫ e.hom.app B)
  have hψ' := ψ.map_s_comp_map L₂ (Localization.inverts L₂ W₂)
  rw [← hψ] at hψ'
  obtain ⟨N, u, hu⟩ := hres ψ.s ψ.hs
  let t : N ⟶ A := H.preimage (u ≫ ψ.s)
  let k : N ⟶ B := H.preimage (u ≫ ψ.f)
  have ht : W₁ t := hW t (by simpa only [t, Functor.map_preimage] using hu)
  have : IsIso (L₁.map t) := Localization.inverts L₁ W₁ t ht
  refine ⟨inv (L₁.map t) ≫ L₁.map k, ?_⟩
  rw [Φ.map_comp, Φ.map_inv, IsIso.inv_comp_eq]
  have key : ∀ {N X : C₁} (f : H.obj N ⟶ H.obj X),
      Φ.map (L₁.map (H.preimage f)) = e.hom.app N ≫ L₂.map f ≫ e.inv.app X := by
    intro N X f
    rw [← cancel_mono (e.hom.app X)]
    simp only [assoc, Iso.inv_hom_id_app, comp_id, Functor.comp_obj]
    simpa only [Functor.comp_map, Functor.map_preimage] using e.hom.naturality (H.preimage f)
  have h1 := key (u ≫ ψ.s)
  have h2 := key (u ≫ ψ.f)
  rw [h1, h2, assoc, assoc, L₂.map_comp, L₂.map_comp, assoc, assoc, ← hψ', assoc, assoc, assoc,
    Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  rw [comp_id]

omit [W₁.HasRightCalculusOfFractions] [H.Faithful] in
include e in
/-- `Φ` is full. -/
theorem full_of_rightResolutions
    (hW : ∀ {A B : C₁} (s : A ⟶ B), W₂ (H.map s) → W₁ s)
    (hres : ∀ {M : C₂} {K : C₁} (s : M ⟶ H.obj K), W₂ s →
      ∃ (N : C₁) (u : H.obj N ⟶ M), W₂ (u ≫ s)) :
    Φ.Full where
  map_surjective {X Y} φ := by
    have := Localization.essSurj L₁ W₁
    let eX := L₁.objObjPreimageIso X
    let eY := L₁.objObjPreimageIso Y
    obtain ⟨g, hg⟩ := map_surjective_of_rightResolutions L₁ W₁ L₂ W₂ H Φ e hW hres
      (Φ.map eX.hom ≫ φ ≫ Φ.map eY.inv)
    refine ⟨eX.inv ≫ g ≫ eY.hom, ?_⟩
    rw [Φ.map_comp, Φ.map_comp, hg]
    simp only [assoc]
    rw [← Φ.map_comp eY.inv eY.hom, eY.inv_hom_id, Φ.map_id, comp_id, ← Φ.map_comp_assoc,
      eX.inv_hom_id, Φ.map_id, id_comp]

include e in
/-- `Φ` is injective on morphisms of the form `L₁.map a`. -/
theorem map_eq_of_rightResolutions
    (hW : ∀ {A B : C₁} (s : A ⟶ B), W₂ (H.map s) → W₁ s)
    (hres : ∀ {M : C₂} {K : C₁} (s : M ⟶ H.obj K), W₂ s →
      ∃ (N : C₁) (u : H.obj N ⟶ M), W₂ (u ≫ s))
    {A B : C₁} (a b : A ⟶ B) (h : Φ.map (L₁.map a) = Φ.map (L₁.map b)) :
    L₁.map a = L₁.map b := by
  have ha := e.hom.naturality a
  have hb := e.hom.naturality b
  simp only [Functor.comp_map] at ha hb
  have h₂ : L₂.map (H.map a) = L₂.map (H.map b) := by
    rw [← cancel_epi (e.hom.app A), ← ha, ← hb, h]
  obtain ⟨X, σ, hσ, hσab⟩ := (MorphismProperty.map_eq_iff_precomp L₂ W₂ _ _).1 h₂
  obtain ⟨N, u, hu⟩ := hres σ hσ
  let t : N ⟶ A := H.preimage (u ≫ σ)
  have ht : W₁ t := hW t (by simpa only [t, Functor.map_preimage] using hu)
  refine (MorphismProperty.map_eq_iff_precomp L₁ W₁ _ _).2 ⟨N, t, ht, H.map_injective ?_⟩
  simp only [t, Functor.map_comp, Functor.map_preimage, assoc, hσab]

include e in
/-- `Φ` is faithful. -/
theorem faithful_of_rightResolutions
    (hW : ∀ {A B : C₁} (s : A ⟶ B), W₂ (H.map s) → W₁ s)
    (hres : ∀ {M : C₂} {K : C₁} (s : M ⟶ H.obj K), W₂ s →
      ∃ (N : C₁) (u : H.obj N ⟶ M), W₂ (u ≫ s)) :
    Φ.Faithful where
  map_injective {X Y} φ₁ φ₂ h := by
    have := Localization.essSurj L₁ W₁
    let eX := L₁.objObjPreimageIso X
    let eY := L₁.objObjPreimageIso Y
    suffices H' : eX.hom ≫ φ₁ ≫ eY.inv = eX.hom ≫ φ₂ ≫ eY.inv by
      simpa only [cancel_epi, cancel_mono] using H'
    set ψ₁ := eX.hom ≫ φ₁ ≫ eY.inv
    set ψ₂ := eX.hom ≫ φ₂ ≫ eY.inv
    have hψ : Φ.map ψ₁ = Φ.map ψ₂ := by simp only [ψ₁, ψ₂, Φ.map_comp, h]
    obtain ⟨χ₁, hχ₁⟩ := Localization.exists_rightFraction L₁ W₁ ψ₁
    have h₁ := χ₁.map_s_comp_map L₁ (Localization.inverts L₁ W₁)
    rw [← hχ₁] at h₁
    obtain ⟨χ₂, hχ₂⟩ := Localization.exists_rightFraction L₁ W₁ (L₁.map χ₁.s ≫ ψ₂)
    have h₂ := χ₂.map_s_comp_map L₁ (Localization.inverts L₁ W₁)
    rw [← hχ₂] at h₂
    have : IsIso (L₁.map χ₁.s) := Localization.inverts L₁ W₁ _ χ₁.hs
    have : IsIso (L₁.map χ₂.s) := Localization.inverts L₁ W₁ _ χ₂.hs
    have key : L₁.map (χ₂.s ≫ χ₁.f) = L₁.map χ₂.f := by
      refine map_eq_of_rightResolutions L₁ W₁ L₂ W₂ H Φ e hW hres _ _ ?_
      rw [L₁.map_comp, ← h₁, ← h₂]
      simp only [Φ.map_comp, hψ]
    rw [L₁.map_comp, ← h₁, ← h₂] at key
    simpa only [cancel_epi] using key

end CategoryTheory.Localization

namespace CategoryTheory.Functor

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Full] [F.Faithful]

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] [F.Full] [F.Faithful] in
/-- The cohomology objects of the image under `F` of a complex lie in the essential image of
`F`. -/
theorem essImage_homology_mapHomologicalComplex_obj (N : CochainComplex C₁ ℤ) (n : ℤ) :
    F.essImage (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N).homology n) :=
  ⟨N.homology n, ⟨((F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).app N).symm⟩⟩

/-- The resolution property of `F`: every cochain complex of `C₂` whose cohomology objects lie
in the essential image of `F` receives a quasi-isomorphism from the image of a complex of
`C₁`. -/
def HasResolutionsOfEssImageHomology : Prop :=
  ∀ M : CochainComplex C₂ ℤ, (∀ n : ℤ, F.essImage (M.homology n)) →
    ∃ (N : CochainComplex C₁ ℤ) (t : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N ⟶ M),
      QuasiIso t

variable {F}

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] in
/-- `F.mapHomotopyCategory` reflects quasi-isomorphisms. -/
theorem mem_quasiIso_of_mapHomotopyCategory_map {A B : HomotopyCategory C₁ (ComplexShape.up ℤ)}
    (s : A ⟶ B)
    (hs : HomotopyCategory.quasiIso C₂ (ComplexShape.up ℤ)
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map s)) :
    HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ) s := by
  obtain ⟨A, rfl⟩ := HomotopyCategory.quotient_obj_surjective A
  obtain ⟨B, rfl⟩ := HomotopyCategory.quotient_obj_surjective B
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  have : F.PreservesHomology := Functor.preservesHomologyOfExact F
  have hs' : HomotopyCategory.quasiIso C₂ (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient _ _).map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) :=
    hs
  have h₁ : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map s) :=
    (HomologicalComplex.mem_quasiIso_iff _).1
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 hs')
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2
    ((HomologicalComplex.mem_quasiIso_iff s).2
      ((HomologicalComplex.quasiIso_map_iff_of_preservesHomology s F).1 h₁))

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] [F.Full] [F.Faithful] in
/-- The resolution property of `F`, read in the homotopy categories. -/
theorem exists_mapHomotopyCategory_resolution (hF : F.HasResolutionsOfEssImageHomology)
    {M : HomotopyCategory C₂ (ComplexShape.up ℤ)} {K : HomotopyCategory C₁ (ComplexShape.up ℤ)}
    (s : M ⟶ (F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
    (hs : HomotopyCategory.quasiIso C₂ (ComplexShape.up ℤ) s) :
    ∃ (N : HomotopyCategory C₁ (ComplexShape.up ℤ))
      (u : (F.mapHomotopyCategory (ComplexShape.up ℤ)).obj N ⟶ M),
      HomotopyCategory.quasiIso C₂ (ComplexShape.up ℤ) (u ≫ s) := by
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  replace hs : QuasiIso s := (HomologicalComplex.mem_quasiIso_iff _).1
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 hs)
  obtain ⟨N, t, ht⟩ := hF M (fun n ↦ (F.essImage_homology_mapHomologicalComplex_obj K n).ofIso
    (isoOfQuasiIsoAt s n).symm)
  refine ⟨(HomotopyCategory.quotient _ _).obj N, (HomotopyCategory.quotient _ _).map t, ?_⟩
  have h := (HomotopyCategory.quotient_map_mem_quasiIso_iff (t ≫ s)).2
    ((HomologicalComplex.mem_quasiIso_iff _).2 inferInstance)
  simp only [Functor.map_comp] at h
  exact h

/-- **`F.mapDerivedCategory` is full** for an exact fully faithful functor with the resolution
property. -/
theorem mapDerivedCategory_full_of_resolutions (hF : F.HasResolutionsOfEssImageHomology) :
    F.mapDerivedCategory.Full :=
  Localization.full_of_rightResolutions DerivedCategory.Qh
    (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ)) DerivedCategory.Qh
    (HomotopyCategory.quasiIso C₂ (ComplexShape.up ℤ)) (F.mapHomotopyCategory _)
    F.mapDerivedCategory F.mapDerivedCategoryFactorsh
    (fun s hs ↦ mem_quasiIso_of_mapHomotopyCategory_map s hs)
    (fun s hs ↦ exists_mapHomotopyCategory_resolution hF s hs)

/-- **`F.mapDerivedCategory` is faithful** for an exact fully faithful functor with the
resolution property. -/
theorem mapDerivedCategory_faithful_of_resolutions (hF : F.HasResolutionsOfEssImageHomology) :
    F.mapDerivedCategory.Faithful :=
  Localization.faithful_of_rightResolutions DerivedCategory.Qh
    (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ)) DerivedCategory.Qh
    (HomotopyCategory.quasiIso C₂ (ComplexShape.up ℤ)) (F.mapHomotopyCategory _)
    F.mapDerivedCategory F.mapDerivedCategoryFactorsh
    (fun s hs ↦ mem_quasiIso_of_mapHomotopyCategory_map s hs)
    (fun s hs ↦ exists_mapHomotopyCategory_resolution hF s hs)

omit [F.Full] [F.Faithful] in
/-- **The essential image of `F.mapDerivedCategory`** contains every object of `D(C₂)` all of
whose cohomology objects lie in the essential image of `F`, for an exact fully faithful functor
with the resolution property. -/
theorem exists_mapDerivedCategory_obj_iso_of_resolutions
    (hF : F.HasResolutionsOfEssImageHomology) (L : DerivedCategory C₂)
    (hL : ∀ n : ℤ, F.essImage ((DerivedCategory.homologyFunctor C₂ n).obj L)) :
    ∃ N : CochainComplex C₁ ℤ,
      Nonempty (F.mapDerivedCategory.obj (DerivedCategory.Q.obj N) ≅ L) := by
  let M := DerivedCategory.Q.objPreimage L
  let eM : DerivedCategory.Q.obj M ≅ L := DerivedCategory.Q.objObjPreimageIso L
  obtain ⟨N, t, ht⟩ := hF M (fun n ↦ (hL n).ofIso
    (((DerivedCategory.homologyFunctorFactors C₂ n).app M).symm ≪≫
      (DerivedCategory.homologyFunctor C₂ n).mapIso eM).symm)
  have : IsIso (DerivedCategory.Q.map t) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact ht
  exact ⟨N, ⟨F.mapDerivedCategoryFactors.app N ≪≫ asIso (DerivedCategory.Q.map t) ≪≫ eM⟩⟩

end CategoryTheory.Functor

end
