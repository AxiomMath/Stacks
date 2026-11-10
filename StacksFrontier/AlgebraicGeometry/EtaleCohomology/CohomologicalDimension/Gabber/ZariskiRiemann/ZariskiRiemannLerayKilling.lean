module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ZariskiRiemannLimitStep
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedBelowDerivedDirectImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.HomWindow
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorTruncationObstruction
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategorySingleFunctorShift

/-!
# The homological half of the Zariski–Riemann limit step

This file proves `AlgebraicGeometry.Scheme.ZariskiRiemann.LerayKilling B`: for every abelian sheaf
`F` on `η = Spec (Frac B)` and every degree `m`, if every class `c ∈ H^{m-q}(Y, R^q j_* F)`
(`q ≤ m`) on every proper model `Y` dies in some refinement `Y' ⟶ Y` under the transition map
`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.lerayTermMap` of the `E₂`-terms of
the Leray spectral sequences, then `H^m(η, F) = 0`.

## The argument

Write `K_Y = Rj_{Y*}F` and `H^m(Y, -) = Hom(ℤ_Y[-m], -)` on `D(Y_étale)`. The Leray filtration
of `H^m(η, F) ≅ H^m(Y, K_Y)` is the image of `H^m(Y, τ^{<n}K_Y)`. Call level `n` *nonzero* if
some model `Y` carries `y : ℤ_Y[-m] ⟶ τ^{<n}K_Y` whose image in `H^m(Y, K_Y)` is nonzero.

* If `H^m(η, F) ≠ 0`, level `m + 1` is nonzero: `H^m(Y, K_Y) ≅ H^m(η, F)` by adjunction, and a
  morphism out of `ℤ_Y[-m] ∈ D^{≤ m}` factors through `τ^{<m+1}`.
* Level `0` is never nonzero: `K_Y ∈ D^{≥ 0}`, so `τ^{<0}K_Y = 0`.
* If level `q + 1` is nonzero, so is level `q`. Let `y` witness it on `Y`. Its *obstruction*,
  `y` followed by `τ^{<q+1}K_Y ⟶ H^q(K_Y)[-q] ≅ (R^q j_* F)[-q]`, is a class
  `c ∈ H^{m-q}(Y, R^q j_* F)`; let `π : Y' ⟶ Y` kill it. Along `π`, the class `y` is carried to
  `π⁻¹ τ^{<q+1}K_Y ⟶ τ^{<q+1}K_{Y'}` (through the base change map `π⁻¹ Rj_* ⟶ Rj'_*`), and the
  obstruction of the result is the image of `c` under `lerayTermMap`
  (`Stacks.TruncationObstruction.liftMap_comp_obstructionMap` together with the comparison of
  `Ext` classes with morphisms into objects placed in degree `q`,
  `Stacks.EtaleCohomology.map_comp_eq_zero_of_sheafH_map_restriction_eq_zero`). So it vanishes,
  and the result lifts to `τ^{<q}K_{Y'}`. Its image in `H^m(Y', K_{Y'})` is still nonzero: the
  map `H^m(Y, K_Y) ⟶ H^m(Y', K_{Y'})` is compatible with the identifications with `H^m(η, F)`
  (`Stacks.EtaleCohomology.etaleDerivedCohomologyDirectImageEquiv_restriction_baseChange`, the
  base change map being the mate of the identification of inverse images), hence injective.

Descending from level `m + 1` to level `0` gives a contradiction.

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.lerayKilling`: `LerayKilling B` for every ring `B`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.fractionFieldVanishingBound_of_zariskiRiemannKilling'`:
  Exposé XVIII-A, Corollary 1.2, from `ZariskiRiemannKilling n` alone.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 0A4A](https://stacks.math.columbia.edu/tag/0A4A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

section Restriction

variable {η Y Y' : Scheme.{u}}

/-- The derived inverse image along an identity is faithful. -/
instance faithful_etaleAbelianDerivedInverseImage_id (X : Scheme.{u}) :
    (etaleAbelianDerivedInverseImage.{u, 0} (𝟙 X)).Faithful :=
  Stacks.HomWindow.faithful_mapDerivedCategory_of_iso (etaleAbelianInverseImage.{u, 0} (𝟙 X))
    (𝟭 _) (Functor.rightUnitor _ ≪≫ etaleAbelianInverseImageIdIso X)

/-- Restriction of `H^p` along an identity is injective. -/
theorem etaleDerivedCohomologyRestriction_id_injective (X : Scheme.{u}) (p : ℤ)
    (N : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    Function.Injective (etaleDerivedCohomologyRestriction.{u, 0} (𝟙 X) p N) := by
  intro a b h
  rw [etaleDerivedCohomologyRestriction_apply, etaleDerivedCohomologyRestriction_apply,
    cancel_epi] at h
  exact (etaleAbelianDerivedInverseImage.{u, 0} (𝟙 X)).map_injective h

/-- **Restriction followed by base change is compatible with `H^p(Y, Rj_* N) ≅ H^p(η, N)`.** For
`j = j' ≫ π`, restricting `x ∈ H^p(Y, Rj_* N)` along `π` and applying the base change map
`π⁻¹ Rj_* N ⟶ Rj'_* N` (of the square `𝟙 ≫ j = j' ≫ π`) gives, under the adjunction
identification for `j'`, the restriction along `𝟙_η` of the class `x` corresponds to. The base
change map is the mate of the identification of composite inverse images
(`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_eq_mateEquiv`), and the identifications
of the constant sheaves `ℤ[-p]` compose (`Stacks.EtaleCohomology.etaleConstantIntegersIso_comp`). -/
theorem etaleDerivedCohomologyDirectImageEquiv_restriction_baseChange (j : η ⟶ Y)
    (j' : η ⟶ Y') (π : Y' ⟶ Y) (hj : j' ≫ π = j) (p : ℤ)
    (N : DerivedCategory (Sheaf η.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (x : etaleDerivedCohomology.{u, 0} Y p ((etaleAbelianDerivedDirectImage.{u, 0} j).obj N)) :
    etaleDerivedCohomologyDirectImageEquiv.{u, 0} j' p _
        (etaleDerivedCohomologyRestriction.{u, 0} π p _ x ≫
          (etaleAbelianDerivedBaseChange.{u, 0} j π (𝟙 η) j'
            (by rw [Category.id_comp, hj])).app N) =
      etaleDerivedCohomologyRestriction.{u, 0} (𝟙 η) p N
        (etaleDerivedCohomologyDirectImageEquiv.{u, 0} j p N x) := by
  have hP₁ : j = 𝟙 η ≫ j := (Category.id_comp j).symm
  have hP₂ : j = j' ≫ π := hj.symm
  have hb := etaleAbelianDerivedBaseChange_eq_mateEquiv.{u, 0} j π (𝟙 η) j' j hP₁ hP₂
  rw [show etaleAbelianDerivedBaseChange.{u, 0} j π (𝟙 η) j' (by rw [Category.id_comp, hj]) =
    etaleAbelianDerivedBaseChange.{u, 0} j π (𝟙 η) j' (hP₁.symm.trans hP₂) from rfl, hb]
  have hc := mateEquiv_counit (etaleAbelianDerivedAdjunction.{u, 0} j)
    (etaleAbelianDerivedAdjunction.{u, 0} j')
    (etaleAbelianDerivedSquare.{u, 0} j π (𝟙 η) j' j hP₁ hP₂) N
  have hn := (etaleAbelianDerivedSquare.{u, 0} j π (𝟙 η) j' j hP₁ hP₂).naturality x
  dsimp only [Functor.comp_map] at hn
  have h₁ := etaleConstantIntegersIso_comp.{u, 0} j' π j hP₂ p
  have h₂ := etaleConstantIntegersIso_comp.{u, 0} (𝟙 η) j j hP₁ p
  rw [etaleDerivedCohomologyDirectImageEquiv_apply, etaleDerivedCohomologyDirectImageEquiv_apply,
    etaleDerivedCohomologyRestriction_apply, etaleDerivedCohomologyRestriction_apply,
    Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  rw [hc, reassoc_of% hn]
  have hα : (etaleAbelianDerivedSquare.{u, 0} j π (𝟙 η) j' j hP₁ hP₂).app
      (etaleConstantIntegers.{u, 0} Y p) =
      (etaleAbelianDerivedInverseImageCompIso'.{u, 0} j' π j hP₂).inv.app _ ≫
        (etaleAbelianDerivedInverseImageCompIso'.{u, 0} (𝟙 η) j j hP₁).hom.app _ := rfl
  rw [hα, ← reassoc_of% h₁]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% h₂]

end Restriction

section Shift

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasShift C ℤ] [HasShift D ℤ] [∀ a : ℤ, (shiftFunctor D a).Additive]

/-- A composite `G(u ≫ (v ≫ f)[a]) ≫ (G-shift comparison) ≫ T[a]` with `u`, `v` invertible
vanishes only if `G(f) ≫ T` does. -/
lemma eq_zero_of_map_comp_shift (G : C ⥤ D) [G.Additive] [G.CommShift ℤ] (a : ℤ)
    {X X' X'' Y : C} {Z : D} (u : X ⟶ X''⟦a⟧) (hu : IsIso u) (v : X'' ⟶ X') (hv : IsIso v)
    (f : X' ⟶ Y) (T : G.obj Y ⟶ Z)
    (h : G.map (u ≫ (v ≫ f)⟦a⟧') ≫ (G.commShiftIso a).hom.app Y ≫ T⟦a⟧' = 0) :
    G.map f ≫ T = 0 := by
  rw [G.map_comp, Category.assoc, Preadditive.IsIso.comp_left_eq_zero,
    Functor.commShiftIso_hom_naturality_assoc, Preadditive.IsIso.comp_left_eq_zero,
    ← Functor.map_comp] at h
  have h' := (shiftFunctor D a).map_injective (h.trans (Functor.map_zero _ _ _).symm)
  rwa [G.map_comp, Category.assoc, Preadditive.IsIso.comp_left_eq_zero] at h'

end Shift

section ExtClass

variable {Y Y' : Scheme.{u}}

/-- **The `Ext` class of a morphism into an object placed in degree `q`.** For `q ≤ m`, a
morphism `w : ℤ_Y[-m] ⟶ A[-q]` in `D(Y_étale)` is read as a class in
`H^{m-q}(Y, A) = Ext^{m-q}(ℤ_Y, A)`: identify `ℤ_Y[-m] ⟶ A[-q]` with `ℤ_Y[0] ⟶ A[-q][m]`
(`Stacks.EtaleCohomology.etaleDerivedCohomologyEquivShiftedHom`) and `A[-q]` with `(A[0])[-q]`. -/
def extClassOfHomSingle (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (m q : ℕ)
    (hq : q ≤ m)
    (w : etaleConstantIntegers.{u, 0} Y m ⟶ (DerivedCategory.singleFunctor _ q).obj A) :
    Sheaf.H.{u + 1} A (m - q) :=
  Abelian.Ext.homEquiv.symm ((etaleDerivedCohomologyEquivShiftedHom.{u, 0} Y m _ w).comp
    (((DerivedCategory.singleFunctors _).shiftIso (-(q : ℤ)) q 0 (by omega)).inv.app A)
    (by omega : -(q : ℤ) + (m : ℤ) = ((m - q : ℕ) : ℤ)))

/-- The identification `H^p(Y, M) ≅ Hom(ℤ_Y[0], M[p])`, written out. -/
lemma etaleDerivedCohomologyEquivShiftedHom_apply' (p : ℤ)
    {M : DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (w : etaleDerivedCohomology.{u, 0} Y p M) :
    etaleDerivedCohomologyEquivShiftedHom.{u, 0} Y p M w =
      (shiftEquiv' (DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) (-p) p
          (by omega)).unit.app _ ≫
        ((etaleConstantIntegersIsoShift.{u, 0} Y p).inv ≫ w)⟦p⟧' :=
  rfl

/-- **An `Ext` class killed by restriction and a map of sheaves gives a vanishing composite in the
derived category.** For `π : Y' ⟶ Y`, `w : ℤ_Y[-m] ⟶ A[-q]` and `ℓ : π⁻¹A ⟶ A₂`: if the image of
the class of `w` in `H^{m-q}(Y', A₂)` vanishes, then so does
`π⁻¹(w) ≫ (π⁻¹A[-q] ≅ (π⁻¹A)[-q]) ≫ ℓ[-q]`. -/
theorem map_comp_eq_zero_of_sheafH_map_restriction_eq_zero (π : Y' ⟶ Y)
    (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    {A₂ : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ℓ : (etaleAbelianInverseImage.{u, 0} π).obj A ⟶ A₂) (m q : ℕ) (hq : q ≤ m)
    (w : etaleConstantIntegers.{u, 0} Y m ⟶ (DerivedCategory.singleFunctor _ q).obj A)
    (h : Sheaf.H.map ℓ (m - q) (etaleCohomologyRestrictionMap.{u, 0, u + 1} π A (m - q)
      (extClassOfHomSingle A m q hq w)) = 0) :
    (etaleAbelianDerivedInverseImage.{u, 0} π).map w ≫
      ((etaleAbelianInverseImage.{u, 0} π).mapDerivedCategorySingleFunctor q).hom.app A ≫
      (DerivedCategory.singleFunctor _ q).map ℓ = 0 := by
  have hh : -(q : ℤ) + (m : ℤ) = ((m - q : ℕ) : ℤ) := by omega
  -- the class of `w`
  have heh : (extClassOfHomSingle A m q hq w).hom =
      (etaleDerivedCohomologyEquivShiftedHom.{u, 0} Y m _ w).comp
        (((DerivedCategory.singleFunctors _).shiftIso (-(q : ℤ)) q 0 (by omega)).inv.app A) hh := by
    unfold extClassOfHomSingle
    exact Equiv.apply_symm_apply _ _
  have hmap : Sheaf.H.map ℓ (m - q) (etaleCohomologyRestrictionMap.{u, 0, u + 1} π A (m - q)
      (extClassOfHomSingle A m q hq w)) = (etaleCohomologyRestrictionMap.{u, 0, u + 1} π A (m - q)
      (extClassOfHomSingle A m q hq w)).comp (Abelian.Ext.mk₀ ℓ) (add_zero _) := rfl
  rw [hmap, etaleCohomologyRestrictionMap_apply] at h
  -- the vanishing, read in the derived category
  have h1 := congrArg Abelian.Ext.hom h
  rw [Abelian.Ext.zero_hom, Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.comp_mk₀,
    Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.mk₀_comp,
    Abelian.Ext.mapExactFunctor_hom, heh, ShiftedHom.map_comp] at h1
  simp only [Category.assoc] at h1
  rw [Preadditive.IsIso.comp_left_eq_zero, Preadditive.IsIso.comp_left_eq_zero] at h1
  -- move the shift-addition isomorphism to the end
  have hadd := (shiftFunctorAdd' (DerivedCategory (Sheaf Y'.smallEtaleTopology
    AddCommGrpCat.{u + 1})) (-(q : ℤ)) m ((m - q : ℕ) : ℤ) hh).inv.naturality
    (((etaleAbelianInverseImage.{u, 0} π).mapDerivedCategorySingleFunctor 0).hom.app A ≫
      (DerivedCategory.singleFunctor _ 0).map ℓ)
  dsimp at hadd
  simp only [ShiftedHom.comp, Category.assoc] at h1
  rw [← Functor.map_comp, ← hadd, ← Functor.map_comp_assoc] at h1
  -- the shift compatibility of the single-functor comparisons
  have hS :=
    Stacks.MapDerivedCategorySingleShift.map_singleFunctors_shiftIso_inv_comp_commShiftIso_hom
    (etaleAbelianInverseImage.{u, 0} π) (q : ℤ) A
  have hnat := ((DerivedCategory.singleFunctors (Sheaf Y'.smallEtaleTopology
    AddCommGrpCat.{u + 1})).shiftIso (-(q : ℤ)) q 0 (by omega)).inv.naturality ℓ
  dsimp at hnat
  have hT : ShiftedHom.map
        (((DerivedCategory.singleFunctors _).shiftIso (-(q : ℤ)) q 0 (by omega)).inv.app A)
        (etaleAbelianInverseImage.{u, 0} π).mapDerivedCategory ≫
      (((etaleAbelianInverseImage.{u, 0} π).mapDerivedCategorySingleFunctor 0).hom.app A ≫
        (DerivedCategory.singleFunctor _ 0).map ℓ)⟦-(q : ℤ)⟧' =
      (((etaleAbelianInverseImage.{u, 0} π).mapDerivedCategorySingleFunctor q).hom.app A ≫
        (DerivedCategory.singleFunctor _ q).map ℓ) ≫
        ((DerivedCategory.singleFunctors _).shiftIso (-(q : ℤ)) q 0 (by omega)).inv.app A₂ := by
    rw [ShiftedHom.map, Functor.map_comp, Category.assoc, reassoc_of% hS]
    simp only [Category.assoc]
    congr 1
    exact hnat.symm
  rw [hT, Functor.map_comp, ← Category.assoc, ← Category.assoc,
    Preadditive.IsIso.comp_right_eq_zero, Preadditive.IsIso.comp_right_eq_zero] at h1
  -- unfold the class of `w` and move the shift comparison of the derived inverse image
  rw [ShiftedHom.map, etaleDerivedCohomologyEquivShiftedHom_apply', Category.assoc] at h1
  have hu : IsIso ((shiftEquiv' (DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (-(m : ℤ)) m (by omega)).unit.app ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift ℤ))))) :=
    inferInstanceAs (IsIso ((shiftEquiv' (DerivedCategory (Sheaf Y.smallEtaleTopology
      AddCommGrpCat.{u + 1})) (-(m : ℤ)) m (by omega)).unitIso.app _).hom)
  exact eq_zero_of_map_comp_shift _ _ _ hu _ (Iso.isIso_inv _) _ _ h1

end ExtClass

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

attribute [local instance] HasDerivedCategory.standard
attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

open Stacks.EtaleCohomology Stacks.TruncationObstruction DerivedCategory

variable {B : Type u} [CommRing B] [IsDomain B]

/-- `Rj_* F` on a proper model, `F` placed in degree `0`. -/
abbrev ProperModel.derivedDirectImage (M : ProperModel B)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    DerivedCategory (Sheaf M.Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  (etaleAbelianDerivedDirectImage.{u, 0} M.j).obj ((DerivedCategory.singleFunctor _ 0).obj F)

/-- **Level `n` of the Leray filtration of `H^m(η, F)` is nonzero**: some proper model `Y` carries
a class `y ∈ H^m(Y, τ^{<n} Rj_* F)` whose image in `H^m(Y, Rj_* F) ≅ H^m(η, F)` is nonzero. -/
def LerayLevelNonzero
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (m : ℕ)
    (n : ℤ) : Prop :=
  ∃ (M : ProperModel B) (y : etaleConstantIntegers.{u, 0} M.Y m ⟶
      (TStructure.t.truncLT n).obj (M.derivedDirectImage F)),
    y ≫ (TStructure.t.truncLTι n).app (M.derivedDirectImage F) ≠ 0

/-- `ℤ_Y[-m]` lies in `D^{≤ m}`. -/
lemma isLE_etaleConstantIntegers (Y : Scheme.{u}) (m : ℤ) :
    (etaleConstantIntegers.{u, 0} Y m).IsLE m :=
  isLE_mapDerivedCategory_obj (etaleAbelianInverseImage.{u, 0} (toSpecULiftZ Y)) _ m

omit [IsDomain B] in
/-- **The descent step.** If every class of every `E₂^{m-q,q}` dies in a refinement and level
`q + 1` of the Leray filtration of `H^m(η, F)` is nonzero, so is level `q`. -/
theorem lerayLevelNonzero_of_succ
    {F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}} {m : ℕ}
    (hL : ∀ (M : ProperModel B) (q : ℕ), q ≤ m →
      ∀ c : Sheaf.H.{u + 1} (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F) (m - q),
        ∃ (M' : ProperModel B) (φ : ProperModel.Refinement M' M),
          φ.lerayTermMap F (m - q) q c = 0)
    (q : ℕ) (hq : q ≤ m) (h : LerayLevelNonzero F m ((q : ℤ) + 1)) :
    LerayLevelNonzero F m q := by
  obtain ⟨M, y, hy⟩ := h
  -- the obstruction of `y`, as a class in `H^{m-q}(Y, R^q j_* F)`
  let eA := etaleAbelianRightDerivedDirectImageIsoHomology.{0, u} M.j q F
  let w : etaleConstantIntegers.{u, 0} M.Y m ⟶ (DerivedCategory.singleFunctor _ q).obj
      (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F) :=
    y ≫ obstructionMap (q : ℤ) (M.derivedDirectImage F) ≫
      (DerivedCategory.singleFunctor _ q).map eA.inv
  obtain ⟨M', φ, hφ⟩ := hL M q hq (extClassOfHomSingle _ m q hq w)
  have hj : 𝟙 _ ≫ M.j = M'.j ≫ φ.π := by rw [Category.id_comp, φ.fac]
  -- the transport of `y` to `Y'`
  let G := etaleAbelianInverseImage.{u, 0} φ.π
  let bc := etaleAbelianSheafDerivedBaseChange.{u, 0} M.j φ.π (𝟙 _) M'.j hj F
  let sI := ((etaleAbelianInverseImage.{u, 0}
    (𝟙 (Spec (.of (FractionRing B))))).mapDerivedCategorySingleFunctor 0).app F
  let b : G.mapDerivedCategory.obj (M.derivedDirectImage F) ⟶
      (etaleAbelianDerivedDirectImage.{u, 0} M'.j).obj ((DerivedCategory.singleFunctor _ 0).obj
        ((etaleAbelianInverseImage.{u, 0} (𝟙 (Spec (.of (FractionRing B))))).obj F)) :=
    bc ≫ (etaleAbelianDerivedDirectImage.{u, 0} M'.j).map sI.hom
  let y₂ := (etaleConstantIntegersIso.{u, 0} φ.π m).hom ≫ G.mapDerivedCategory.map y ≫
    liftMap G q b
  -- its obstruction vanishes
  have hw : G.mapDerivedCategory.map w ≫
      (G.mapDerivedCategorySingleFunctor q).hom.app _ ≫
      (DerivedCategory.singleFunctor _ q).map
        (etaleAbelianInverseImageRightDerivedDirectImageBaseChange.{u} M.j φ.π (𝟙 _) M'.j hj F
          q) = 0 :=
    map_comp_eq_zero_of_sheafH_map_restriction_eq_zero φ.π _ _ m q hq w hφ
  have hβ : G.map eA.inv ≫
      etaleAbelianInverseImageRightDerivedDirectImageBaseChange.{u} M.j φ.π (𝟙 _) M'.j hj F q ≫
      (etaleAbelianRightDerivedDirectImageIsoHomology.{0, u} M'.j q
        ((etaleAbelianInverseImage.{u, 0} (𝟙 (Spec (.of (FractionRing B))))).obj F)).hom =
      (G.mapDerivedCategoryHomologyIso q).inv.app (M.derivedDirectImage F) ≫
        (homologyFunctor _ q).map b := by
    simp only [etaleAbelianInverseImageRightDerivedDirectImageBaseChange, G, b, bc, sI, eA,
      Functor.mapIso_hom, Iso.app_inv, Category.assoc, Iso.inv_hom_id_map_assoc, Iso.inv_hom_id,
      Category.comp_id, Functor.map_comp]
  have hsI := (G.mapDerivedCategorySingleFunctor (q : ℤ)).hom.naturality eA.inv
  dsimp at hsI
  have hob : y₂ ≫ obstructionMap (q : ℤ) _ = 0 := by
    have e1 := liftMap_comp_obstructionMap G (q : ℤ) b
    calc y₂ ≫ obstructionMap (q : ℤ) _
        = (etaleConstantIntegersIso.{u, 0} φ.π m).hom ≫ G.mapDerivedCategory.map y ≫
            G.mapDerivedCategory.map (obstructionMap q (M.derivedDirectImage F)) ≫
            (G.mapDerivedCategorySingleFunctor q).hom.app _ ≫
            (DerivedCategory.singleFunctor _ q).map
              ((G.mapDerivedCategoryHomologyIso q).inv.app (M.derivedDirectImage F) ≫
                (homologyFunctor _ q).map b) := by
          simp only [y₂, Category.assoc, e1]
      _ = (etaleConstantIntegersIso.{u, 0} φ.π m).hom ≫ (G.mapDerivedCategory.map w ≫
            (G.mapDerivedCategorySingleFunctor q).hom.app _ ≫
            (DerivedCategory.singleFunctor _ q).map
              (etaleAbelianInverseImageRightDerivedDirectImageBaseChange.{u} M.j φ.π (𝟙 _) M'.j
                hj F q)) ≫
            (DerivedCategory.singleFunctor _ q).map
              (etaleAbelianRightDerivedDirectImageIsoHomology.{0, u} M'.j q
                ((etaleAbelianInverseImage.{u, 0}
                  (𝟙 (Spec (.of (FractionRing B))))).obj F)).hom := by
          rw [← hβ]
          simp only [w, Functor.map_comp, Category.assoc]
          rw [reassoc_of% hsI]
      _ = 0 := by rw [hw, zero_comp, comp_zero]
  -- so the transport lifts to `τ^{<q}`
  have hπ : y₂ ≫ (TStructure.t.truncGEπ q).app _ = 0 := by
    rwa [obstructionMap, ← Category.assoc, Preadditive.IsIso.comp_right_eq_zero] at hob
  obtain ⟨y₀, hy₀'⟩ : ∃ y₀ : etaleConstantIntegers.{u, 0} M'.Y m ⟶
      (TStructure.t.truncLT (q : ℤ)).obj ((TStructure.t.truncLT ((q : ℤ) + 1)).obj
        ((etaleAbelianDerivedDirectImage.{u, 0} M'.j).obj ((DerivedCategory.singleFunctor _ 0).obj
          ((etaleAbelianInverseImage.{u, 0} (𝟙 (Spec (.of (FractionRing B))))).obj F)))),
      y₂ = y₀ ≫ (TStructure.t.truncLTι q).app _ :=
    Triangle.coyoneda_exact₂ _ (TStructure.t.triangleLTGE_distinguished q _) y₂ hπ
  let ρ :=
    (etaleAbelianDerivedDirectImage.{u, 0} M'.j).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
      ((etaleAbelianInverseImageIdIso _).app F))
  refine ⟨M', y₀ ≫ (TStructure.t.truncLT q).map
    ((TStructure.t.truncLTι ((q : ℤ) + 1)).app _ ≫ ρ.hom), ?_⟩
  intro hzero
  apply hy
  have hnat := (TStructure.t.truncLTι (q : ℤ)).naturality
    ((TStructure.t.truncLTι ((q : ℤ) + 1)).app _ ≫ ρ.hom)
  dsimp at hnat
  have e2 : (y₀ ≫ (TStructure.t.truncLT q).map
      ((TStructure.t.truncLTι ((q : ℤ) + 1)).app _ ≫ ρ.hom)) ≫
        (TStructure.t.truncLTι q).app (M'.derivedDirectImage F) =
      (((etaleConstantIntegersIso.{u, 0} φ.π m).hom ≫ G.mapDerivedCategory.map
        (y ≫ (TStructure.t.truncLTι ((q : ℤ) + 1)).app (M.derivedDirectImage F))) ≫ bc) ≫
        (etaleAbelianDerivedDirectImage.{u, 0} M'.j).map sI.hom ≫ ρ.hom := by
    rw [Category.assoc y₀, hnat, ← Category.assoc y₀, ← hy₀']
    simp only [y₂, b, Category.assoc, liftMap_ι_assoc, Functor.map_comp]
  rw [e2, Preadditive.IsIso.comp_right_eq_zero] at hzero
  have hx := etaleDerivedCohomologyDirectImageEquiv_restriction_baseChange M.j M'.j φ.π φ.fac
    (m : ℤ) ((DerivedCategory.singleFunctor _ 0).obj F)
    (y ≫ (TStructure.t.truncLTι ((q : ℤ) + 1)).app (M.derivedDirectImage F))
  rw [etaleDerivedCohomologyRestriction_apply] at hx
  have hz : ((etaleConstantIntegersIso.{u, 0} φ.π m).hom ≫ G.mapDerivedCategory.map
      (y ≫ (TStructure.t.truncLTι ((q : ℤ) + 1)).app (M.derivedDirectImage F))) ≫
      (etaleAbelianDerivedBaseChange.{u, 0} M.j φ.π (𝟙 _) M'.j
        (by rw [Category.id_comp, φ.fac])).app ((DerivedCategory.singleFunctor _ 0).obj F) = 0 :=
    hzero
  rw [hz, map_zero] at hx
  have h0 := etaleDerivedCohomologyRestriction_id_injective _ (m : ℤ) _
    (hx.symm.trans (map_zero _).symm)
  exact (etaleDerivedCohomologyDirectImageEquiv.{u, 0} M.j m _).injective
    (h0.trans (map_zero _).symm)

omit [IsDomain B] in
/-- **The homological half of the Zariski–Riemann limit step** (Travaux de Gabber, Exposé
XVIII-A, last remark of §2): for every ring `B`, if on every proper model every class of every
`E₂`-term `H^{m-q}(Y, R^q j_* F)` with `q ≤ m` dies in a refinement, then `H^m(η, F) = 0`. -/
theorem lerayKilling : LerayKilling B := by
  intro F m hL
  rw [(Abelian.Ext.homEquiv).subsingleton_congr.trans
    (etaleDerivedCohomologyEquivShiftedHom.{u, 0} _ m _).toEquiv.subsingleton_congr.symm]
  by_contra hns
  rw [not_subsingleton_iff_nontrivial] at hns
  obtain ⟨x, hx⟩ := exists_ne (0 : etaleDerivedCohomology.{u, 0} (Spec (.of (FractionRing B))) m
    ((DerivedCategory.singleFunctor _ 0).obj F))
  have base : LerayLevelNonzero F m ((m : ℤ) + 1) := by
    have := isLE_etaleConstantIntegers (ProperModel.base (B := B)).Y m
    refine ⟨ProperModel.base, TStructure.t.liftTruncLT
      ((etaleDerivedCohomologyDirectImageEquiv.{u, 0} (ProperModel.base (B := B)).j m _).symm x)
      m (m + 1) rfl, ?_⟩
    rw [TStructure.t.liftTruncLT_ι]
    intro h0
    apply hx
    simpa using congrArg (etaleDerivedCohomologyDirectImageEquiv.{u, 0}
      (ProperModel.base (B := B)).j m _) h0
  have key : ∀ k : ℕ, k ≤ m + 1 → LerayLevelNonzero F m ((m : ℤ) + 1 - k) := by
    intro k
    induction k with
    | zero => intro _; simpa using base
    | succ k ih =>
      intro hk
      have h1 := lerayLevelNonzero_of_succ hL (m - k) (by omega) (by
        have h2 := ih (by omega)
        rwa [show ((m : ℤ) + 1 - (k : ℤ)) = (((m - k : ℕ) : ℤ) + 1) by omega] at h2)
      rwa [show (((m - k : ℕ) : ℤ)) = ((m : ℤ) + 1 - ((k + 1 : ℕ) : ℤ)) by omega] at h1
  have hlast := key (m + 1) le_rfl
  rw [show ((m : ℤ) + 1 - ((m + 1 : ℕ) : ℤ)) = 0 by omega] at hlast
  obtain ⟨M, y, hy⟩ := hlast
  have hK : (M.derivedDirectImage F).IsGE 0 :=
    isGE_etaleAbelianDerivedDirectImage_obj.{u, 0} M.j _ 0 inferInstance
  apply hy
  rw [(TStructure.t.isZero_truncLT_obj_of_isGE 0 _).eq_of_tgt y 0, zero_comp]

/-- **Exposé XVIII-A, Corollary 1.2, from the geometric half of the Zariski–Riemann limit step
alone**: the homological half `LerayKilling` holds for every domain (`lerayKilling`). -/
theorem fractionFieldVanishingBound_of_zariskiRiemannKilling' {n : ℕ}
    (hZR : ZariskiRiemannKilling.{u} n) : FractionFieldVanishingBound.{u} n :=
  fractionFieldVanishingBound_of_zariskiRiemannKilling hZR fun _ _ _ _ _ => lerayKilling

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
