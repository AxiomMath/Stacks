module

public import StacksFrontier.Homology.HomComplex.ShiftHom
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange
public import StacksFrontier.RingTheory.Dualizing.Normalized
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldShift
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Shifting a dualizing complex, and the uniqueness of the normalizing shift

Over a Noetherian local ring `A` a dualizing complex is normalized
(`Dualizing.IsNormalizedDualizingComplex`) when its derived Hom from the residue field is the
residue field in degree zero. This file proves that *exactly one* shift of a given dualizing
complex is normalized.

Both halves come out of [Stacks, Tag 0A7L] (`Dualizing.derivedHom_localResidueField_iso_shift`),
which says that `RHom_A(κ, K)` is isomorphic to `κ[0]⟦m⟧` for some `m`. Existence is then the
shift by `-m`, provided shifting preserves being a dualizing complex; uniqueness is the fact that
`κ[0]` is isomorphic to a shift of itself only in degree zero, which is
`Dualizing.residueSingle_shift_hom_eq_zero` applied through `Dualizing.residueSingle_id_ne_zero`
— here phrased directly on cohomology in `Dualizing.shift_eq_zero_of_nonempty_iso_single_shift`.

## Main results

* `Dualizing.isDualizingComplex_shift` — a shift of a dualizing complex is a dualizing complex.
  Each of the three conditions is shifted separately; the homothety condition is the one with
  content, because the identity cochain of `I` must be matched with the identity cochain of
  `I⟦n⟧`.
* `Dualizing.shift_eq_zero_of_nonempty_iso_single_shift` — a nonzero module in degree zero is
  isomorphic to a shift of itself only for the zero shift.
* `Dualizing.exists_isNormalizedDualizingComplex_shift` — some shift of a dualizing complex over
  a Noetherian local ring is normalized.
* `Dualizing.isNormalizedDualizingComplex_shift_iff_eq` — and only one: once one normalizing
  shift is known, a shift is normalized exactly when it is that one.
* `Dualizing.isNormalizedDualizingComplex_congr` — being normalized depends on the object only
  through its isomorphism class.

## Implementation notes

The homothety condition is `QuasiIso (Dualizing.homothety I)` quantified over bounded injective
representatives `I`, so shifting it means producing, from a representative of `K⟦n⟧`, a
representative of `K` whose homothety is a quasi-isomorphism, and transporting back. The transport
is `Dualizing.endomorphismComplexShiftIso`: simultaneously shifting source and target leaves the
endomorphism complex unchanged. That isomorphism is built degreewise from
`Dualizing.cochainSelfShiftEquiv`, the composite of
`CochainComplex.HomComplex.Cochain.rightShiftLinearEquiv` and
`CochainComplex.HomComplex.Cochain.leftShiftLinearEquiv`, corrected by the constant sign
`(n * (n - 1) / 2).negOnePow` (`CochainComplex.HomComplex.negOnePowLinearEquiv`) which cancels
the sign built into the left shift. The correction is what makes the square against
`Dualizing.homothety` commute on the nose, so that `Dualizing.homComplexSelfShiftIso` can carry
the scalar identity cochain to the scalar identity cochain.

The shift-stability half is stated at a **free** `[HasDerivedCategory (ModuleCat.{v} R)]` binder,
matching `Dualizing.IsDualizingComplex`, which takes one too. The normalization half cannot be:
`Dualizing.derivedHom` bakes `HasDerivedCategory.standard` into its type (four occurrences under
`set_option pp.explicit true`), so `Dualizing.IsNormalizedDualizingComplex` is pinned at the
standard model and every statement about it inherits the pin. That pin is forced and harmless
rather than weakening — over `ModuleCat A` the standard model is a legitimate derived category,
and the vacuity hazard of `HasDerivedCategory.standard` is specific to `SheafOfModules`, where it
destroys the coproducts of Tag 0A8G. A model-generic derived Hom does exist, as
`Dualizing.AnyModel.derivedHom`, but `Dualizing.IsNormalizedDualizingComplex` is stated against
the pinned `Dualizing.derivedHom`, so lifting the pin here would mean restating the normalization
condition rather than reproving anything below.

## References

* [Stacks Project, Tag 0AX1](https://stacks.math.columbia.edu/tag/0AX1)
* [Stacks Project, Tag 0A7L](https://stacks.math.columbia.edu/tag/0A7L)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Dualizing

section CochainShift

variable {R : Type u} [CommRing R]

/-- The degreewise equivalence of the two endomorphism complexes under a simultaneous shift of
source and target. The constant sign cancels the sign built into
`CochainComplex.HomComplex.Cochain.leftShiftLinearEquiv`. -/
def cochainSelfShiftEquiv
    (I : CochainComplex (ModuleCat.{v} R) ℤ) (n k : ℤ) :
    CochainComplex.HomComplex.Cochain I I k ≃ₗ[R]
      CochainComplex.HomComplex.Cochain (I⟦n⟧) (I⟦n⟧) k :=
  ((CochainComplex.HomComplex.Cochain.rightShiftLinearEquiv R I I k n (k - n)
      (by omega)).trans
    (CochainComplex.HomComplex.Cochain.leftShiftLinearEquiv R I (I⟦n⟧)
      (k - n) n k (by omega))).trans
    (CochainComplex.HomComplex.negOnePowLinearEquiv R _ (n * (n - 1) / 2))

/-- `Dualizing.cochainSelfShiftEquiv` commutes with the differential of the Hom complex. -/
theorem cochainSelfShiftEquiv_delta
    (I : CochainComplex (ModuleCat.{v} R) ℤ) (n k : ℤ)
    (z : CochainComplex.HomComplex.Cochain I I k) :
    CochainComplex.HomComplex.δ k (k + 1) (cochainSelfShiftEquiv I n k z) =
      cochainSelfShiftEquiv I n (k + 1)
        (CochainComplex.HomComplex.δ k (k + 1) z) := by
  simp only [cochainSelfShiftEquiv, LinearEquiv.trans_apply,
    CochainComplex.HomComplex.negOnePowLinearEquiv,
    CochainComplex.HomComplex.Cochain.rightShiftLinearEquiv_apply,
    CochainComplex.HomComplex.Cochain.leftShiftLinearEquiv_apply]
  show CochainComplex.HomComplex.δ k (k + 1)
    ((n * (n - 1) / 2).negOnePow •
      ((z.rightShift n (k - n) (by omega)).leftShift n k (by omega))) =
    (n * (n - 1) / 2).negOnePow •
      (((CochainComplex.HomComplex.δ k (k + 1) z).rightShift n
        (k + 1 - n) (by omega)).leftShift n (k + 1) (by omega))
  rw [CochainComplex.HomComplex.δ_units_smul,
    CochainComplex.HomComplex.Cochain.δ_leftShift _ n k (k + 1)
      (by omega) (k + 1 - n) (by omega),
    CochainComplex.HomComplex.Cochain.δ_rightShift _ n (k - n) (k + 1 - n)
      (by omega) (k + 1) (by omega), CochainComplex.HomComplex.Cochain.leftShift_units_smul]
  simp only [smul_smul, Int.units_mul_self, mul_one]

/-- Simultaneously shifting the source and the target preserves the Hom complex, together with
its scalar identity cochains in degree zero. -/
def homComplexSelfShiftIso
    (I : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) :
    { e : CochainComplex.HomComplexR R I I ≅
        CochainComplex.HomComplexR R (I⟦n⟧) (I⟦n⟧) //
      ∀ a : R, (e.hom.f 0).hom
        (a • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)) =
        a • CochainComplex.HomComplex.Cochain.ofHom (𝟙 (I⟦n⟧)) } := by
  let e : CochainComplex.HomComplexR R I I ≅
      CochainComplex.HomComplexR R (I⟦n⟧) (I⟦n⟧) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun k ↦ (cochainSelfShiftEquiv I n k).toModuleIso) (by
        intro i j hij
        obtain rfl : j = i + 1 := by simpa using hij.symm
        ext z
        change CochainComplex.HomComplex.Cochain I I i at z
        exact cochainSelfShiftEquiv_delta I n i z)
  refine ⟨e, fun a ↦ ?_⟩
  change cochainSelfShiftEquiv I n 0
    (a • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)) =
      a • CochainComplex.HomComplex.Cochain.ofHom (𝟙 (I⟦n⟧))
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  obtain rfl : q = p := by omega
  simp only [cochainSelfShiftEquiv, LinearEquiv.trans_apply,
    CochainComplex.HomComplex.negOnePowLinearEquiv,
    CochainComplex.HomComplex.Cochain.rightShiftLinearEquiv_apply,
    CochainComplex.HomComplex.Cochain.leftShiftLinearEquiv_apply]
  change (((n * (n - 1) / 2).negOnePow •
      ((a • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)).rightShift n (-n)
        (by omega)).leftShift n 0 (by omega))).v q q hpq = _
  rw [CochainComplex.HomComplex.Cochain.units_smul_v,
    CochainComplex.HomComplex.Cochain.leftShift_v _ n 0 (by omega)
      q q hpq (q + n) (by omega),
    CochainComplex.HomComplex.Cochain.rightShift_v _ n (-n) (by omega)
      (q + n) q (by omega) (q + n) (by omega)]
  simp only [mul_zero, zero_add, smul_smul, Int.units_mul_self, one_smul,
    CochainComplex.HomComplex.Cochain.smul_v,
    CochainComplex.HomComplex.Cochain.ofHom_v, HomologicalComplex.id_f]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp,
    Iso.hom_inv_id]
  rfl

/-- The universe-lifted endomorphism complex of `Dualizing.homothety` is unchanged by a
simultaneous shift of source and target. -/
def endomorphismComplexShiftIso
    (I : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) :
    liftedEndomorphismComplex I ≅ liftedEndomorphismComplex (I⟦n⟧) :=
  ((AddCommGrpCat.uliftFunctor.{u, v}).mapHomologicalComplex (.up ℤ)).mapIso
    (((forget₂ (ModuleCat.{v} R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).mapIso
      (homComplexSelfShiftIso I n).1)

/-- If the homothety of `I⟦-n⟧` is a quasi-isomorphism then so is the homothety of `I`. -/
theorem isDerivedHomothetyQuasiIso_of_shift
    (I : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    (hI : QuasiIso (homothety (I⟦-n⟧))) :
    QuasiIso (homothety I) := by
  let e := endomorphismComplexShiftIso I (-n)
  have hcomm : homothety I ≫ e.hom = homothety (I⟦-n⟧) := by
    apply HomologicalComplex.hom_ext
    intro i
    obtain rfl | hi := eq_or_ne i 0
    · rw [HomologicalComplex.comp_f]
      ext a
      change ULift.{v} R at a
      show (e.hom.f 0).hom (ULift.up
        (a.down • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I))) =
        ULift.up (a.down • CochainComplex.HomComplex.Cochain.ofHom (𝟙 (I⟦-n⟧)))
      exact congrArg ULift.up
        ((homComplexSelfShiftIso I (-n)).2 a.down)
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
        (AddCommGrpCat.of (ULift.{v} R)) i hi).eq_of_src _ _
  have : QuasiIso (homothety I ≫ e.hom) := by rwa [hcomm]
  exact quasiIso_of_comp_right (homothety I) e.hom

/-- Shifting a bounded complex of injectives gives a bounded complex of injectives. -/
private theorem shift_injective_isStrictlyGE_isStrictlyLE
    (I : CochainComplex (ModuleCat.{v} R) ℤ) (a b n : ℤ) (hGE : I.IsStrictlyGE a)
    (hLE : I.IsStrictlyLE b) (hI : ∀ i, Injective (I.X i)) :
    (∀ i, Injective ((I⟦n⟧).X i)) ∧ (I⟦n⟧).IsStrictlyGE (a - n) ∧ (I⟦n⟧).IsStrictlyLE (b - n) :=
  ⟨fun i ↦ Injective.of_iso (I.shiftFunctorObjXIso n i (n + i) (by abel)).symm (hI (n + i)),
    I.isStrictlyGE_shift a n (a - n) (by abel), I.isStrictlyLE_shift b n (b - n) (by abel)⟩

end CochainShift

section ShiftStability

variable {R : Type u} [CommRing R] [HasDerivedCategory (ModuleCat.{v} R)]

/-- A shift of a complex of finite injective dimension has finite injective dimension: shift a
bounded complex of injectives representing it. -/
@[sga "6 I 5.7" "partial"]
theorem hasFiniteInjectiveDimension_shift
    (K : DerivedCategory (ModuleCat.{v} R))
    (hK : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K) (n : ℤ) :
    StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension (K⟦n⟧) := by
  obtain ⟨a, b, I, hGE, hLE, hI, ⟨e⟩⟩ := hK
  obtain ⟨hI', hGE', hLE'⟩ := shift_injective_isStrictlyGE_isStrictlyLE I a b n hGE hLE hI
  exact ⟨a - n, b - n, I⟦n⟧, hGE', hLE', hI', ⟨(shiftFunctor _ n).mapIso e ≪≫
    ((DerivedCategory.Q.commShiftIso n).app I).symm⟩⟩

/-- A shift reindexes the cohomology modules, so finiteness of all of them is preserved. -/
theorem finite_homology_shift
    (K : DerivedCategory (ModuleCat.{v} R))
    (hK : ∀ i : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) (n : ℤ) :
    ∀ i : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj (K⟦n⟧)) := by
  intro i
  let e := ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).shiftIso
    n i (n + i) rfl).app K
  have : Module.Finite R (((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).shift
      (n + i)).obj K) := by
    rw [DerivedCategory.shift_homologyFunctor]
    exact hK (n + i)
  exact Module.Finite.of_surjective e.inv.hom
    ((ModuleCat.epi_iff_surjective e.inv).mp inferInstance)

/-- The homothety condition of a dualizing complex is preserved by shifts. -/
theorem isDerivedHomothetyQuasiIso_shift
    (K : DerivedCategory (ModuleCat.{v} R))
    (hK : IsDerivedHomothetyQuasiIso K) (n : ℤ) :
    IsDerivedHomothetyQuasiIso (K⟦n⟧) := by
  intro I ⟨e⟩ hI ⟨a, b, hGE, hLE⟩
  have hrep : Nonempty (DerivedCategory.Q.obj (I⟦-n⟧) ≅ K) :=
    ⟨(DerivedCategory.Q.commShiftIso (-n)).app I ≪≫
      (shiftFunctor _ (-n)).mapIso e ≪≫ (shiftEquiv _ n).unitIso.symm.app K⟩
  obtain ⟨hI', hGE', hLE'⟩ := shift_injective_isStrictlyGE_isStrictlyLE I a b (-n) hGE hLE hI
  exact isDerivedHomothetyQuasiIso_of_shift I n (hK _ hrep hI' ⟨_, _, hGE', hLE'⟩)

/-- **A shift of a dualizing complex is a dualizing complex.** -/
theorem isDualizingComplex_shift [IsNoetherianRing R]
    (K : DerivedCategory (ModuleCat.{v} R))
    (hK : IsDualizingComplex K) (n : ℤ) :
    IsDualizingComplex (K⟦n⟧) :=
  ⟨hasFiniteInjectiveDimension_shift K hK.finiteInjectiveDimension n,
    finite_homology_shift K hK.finiteCohomology n,
    isDerivedHomothetyQuasiIso_shift K hK.homothetyQuasiIso n⟩

end ShiftStability

/-- A nonzero module placed in degree zero is isomorphic to a shift of itself only for the zero
shift: the shifted object has its cohomology in degree `-d`, and a single complex has no
cohomology outside degree zero. -/
theorem shift_eq_zero_of_nonempty_iso_single_shift
    {R : Type u} [CommRing R] [HasDerivedCategory (ModuleCat.{v} R)]
    (κ : ModuleCat.{v} R) [Nontrivial κ]
    (d : ℤ) (h : Nonempty
      (((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj κ) ≅
        (((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj κ)⟦d⟧))) :
    d = 0 := by
  let C := ModuleCat.{v} R
  let S := (DerivedCategory.singleFunctor C 0).obj κ
  let H0 := DerivedCategory.homologyFunctor C 0
  have hzero : Nontrivial (H0.obj S) :=
    (((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app κ).toLinearEquiv.toEquiv
      |>.nontrivial_congr).mpr ‹Nontrivial κ›
  obtain ⟨e⟩ := h
  have hshift : Nontrivial (H0.obj (S⟦d⟧)) :=
    ((H0.mapIso e).toLinearEquiv.toEquiv.nontrivial_congr).mp hzero
  have hsource : Nontrivial ((H0.shift (0 : ℤ)).obj (S⟦d⟧)) :=
    (((H0.isoShiftZero ℤ).app (S⟦d⟧)).toLinearEquiv.toEquiv.nontrivial_congr).mpr hshift
  have hdegree : Nontrivial ((H0.shift d).obj S) :=
    (((H0.shiftIso d 0 d (by omega)).app S).toLinearEquiv.toEquiv.nontrivial_congr).mp hsource
  have hdegree' : Nontrivial
      ((DerivedCategory.homologyFunctor C d).obj S) := by
    rwa [← DerivedCategory.shift_homologyFunctor C d]
  by_contra hd
  have hz : IsZero ((DerivedCategory.homologyFunctor C d).obj S) :=
    IsZero.of_iso
      (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 κ d hd) <|
      ((DerivedCategory.homologyFunctor C d).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ C 0).app κ)).trans
      ((DerivedCategory.homologyFunctorFactors C d).app
        ((CochainComplex.singleFunctor C 0).obj κ))
  exact (not_nontrivial_iff_subsingleton.mpr
    (ModuleCat.isZero_iff_subsingleton.mp hz)) hdegree'

section Normalization

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- Being a normalized dualizing complex depends on the object only through its isomorphism
class. -/
theorem isNormalizedDualizingComplex_congr
    {K L : DerivedCategory (ModuleCat.{max v u} A)} (e : K ≅ L) :
    IsNormalizedDualizingComplex.{u, v} K ↔ IsNormalizedDualizingComplex.{u, v} L := by
  let F := derivedHom.{u, v} (IsLocalRing.residue A)
  exact ⟨fun hK ↦ ⟨isDualizingComplex_of_iso e hK.1, hK.2.map ((F.mapIso e).symm ≪≫ ·)⟩,
    fun hL ↦ ⟨isDualizingComplex_of_iso e.symm hL.1, hL.2.map (F.mapIso e ≪≫ ·)⟩⟩

/-- **Some shift of a dualizing complex over a Noetherian local ring is normalized.** By
[Stacks, Tag 0A7L] the derived Hom from the residue field is `κ[0]⟦m⟧`, and shifting by `-m`
moves it to `κ[0]`. -/
theorem exists_isNormalizedDualizingComplex_shift
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsDualizingComplex K) :
    ∃ m : ℤ, IsNormalizedDualizingComplex.{u, v} (K⟦-m⟧) := by
  let F := derivedHom.{u, v} (IsLocalRing.residue A)
  have : F.CommShift ℤ := by
    dsimp only [F, derivedHom]
    infer_instance
  obtain ⟨m, hm⟩ := derivedHom_localResidueField_iso_shift.{u, v} K hK
  let S := (DerivedCategory.singleFunctor
    (ModuleCat.{max v u} (IsLocalRing.ResidueField A)) 0).obj
      ((ModuleCat.uliftFunctor.{v} (IsLocalRing.ResidueField A)).obj
        (ModuleCat.of (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A)))
  have hnorm : Nonempty (F.obj (K⟦-m⟧) ≅ S) := by
    obtain ⟨e⟩ := hm
    exact ⟨(F.commShiftIso (-m)).app K ≪≫
      (shiftFunctor _ (-m)).mapIso e ≪≫
      (shiftFunctorCompIsoId
        (DerivedCategory (ModuleCat.{max v u} (IsLocalRing.ResidueField A))) m (-m)
        (by omega)).app S⟩
  exact ⟨m, ⟨isDualizingComplex_shift K hK (-m), hnorm⟩⟩

/-- **The normalizing shift is unique.** Given one shift `m` at which `K` is normalized, a shift
`n` is normalizing exactly when `n = m`: otherwise `κ[0]` would be isomorphic to its own shift by
`m - n`. -/
theorem isNormalizedDualizingComplex_shift_iff_eq
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (m : ℤ) (hm : IsNormalizedDualizingComplex.{u, v} (K⟦-m⟧))
    (n : ℤ) :
    IsNormalizedDualizingComplex.{u, v} (K⟦-n⟧) ↔ n = m := by
  let F := derivedHom.{u, v} (IsLocalRing.residue A)
  have : F.CommShift ℤ := by
    dsimp only [F, derivedHom]
    infer_instance
  let S := (DerivedCategory.singleFunctor
    (ModuleCat.{max v u} (IsLocalRing.ResidueField A)) 0).obj
      ((ModuleCat.uliftFunctor.{v} (IsLocalRing.ResidueField A)).obj
        (ModuleCat.of (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A)))
  refine ⟨fun hn ↦ ?_, by rintro rfl; exact hm⟩
  obtain ⟨em⟩ := hm.2
  obtain ⟨en⟩ := hn.2
  have hsingle : Nonempty (S ≅ S⟦m - n⟧) :=
    ⟨en.symm ≪≫ F.mapIso ((shiftFunctorAdd'
      (DerivedCategory (ModuleCat.{max v u} A)) (-m) (m - n) (-n) (by omega)).app K) ≪≫
      (F.commShiftIso (m - n)).app (K⟦-m⟧) ≪≫ (shiftFunctor _ (m - n)).mapIso em⟩
  have hmn : m - n = 0 := shift_eq_zero_of_nonempty_iso_single_shift
    (κ := (ModuleCat.uliftFunctor.{v} (IsLocalRing.ResidueField A)).obj
      (ModuleCat.of (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A)))
    (m - n) hsingle
  omega

end Normalization

end Dualizing

end
