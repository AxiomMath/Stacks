module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.AdditiveGroupSheafCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HStructureSheaf.StandardFppfCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.CechVanishingStandardCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCechVanishingTensorPresheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ColimitsOfAFiniteFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongACoefficientFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongAFunctor

/-!
# Čech cohomology of `𝒪^{perf}` on standard fppf coverings

Let `S` be a scheme over `𝔽_p` and let `(Sch/S)_h` be a big h site over `S`. On its underlying
category with the fppf topology, the positive degree Čech cohomology of the sheaf
`𝒪^{perf} = colim_F 𝒪` vanishes on every standard fppf covering of an object with affine
underlying scheme. This is the Čech input of the vanishing of the higher fppf cohomology of
`𝒪^{perf}` on affine objects, used in the proof of Stacks 0EWT.

The source deduces that vanishing from `H^i_{fppf}(X, 𝒪^{perf}) = colim_F H^i_{fppf}(X, 𝒪)`
(Stacks 0739) and `H^i_{fppf}(X, 𝒪) = H^i(X, 𝒪)` (Stacks 03DW). Here the same two facts enter at
the level of Čech complexes: the Čech complex of a filtered colimit of presheaves is the
colimit of the Čech complexes, and the Čech complex of the structure sheaf on a standard fppf
covering of an affine is exact in positive degrees (Stacks 03FJ, by the Amitsur complex).

## Main definitions

* `AlgebraicGeometry.BigHOver.addULift`: rings to abelian groups, with the universe raised to the
  coefficient universe of the big site.
* `AlgebraicGeometry.BigHOver.perfectionTower`: the Frobenius tower `𝒪 →^F 𝒪 →^F ⋯` of abelian
  presheaves.
* `AlgebraicGeometry.BigHOver.perfectionTowerDesc`: the map from its colimit to the abelian
  presheaf underlying `X ↦ Γ(Xᵃʷⁿ, 𝒪)`.

## Main results

* `AlgebraicGeometry.BigHOver.isIso_perfectionTowerDesc_app`: that map is invertible on objects
  with affine underlying scheme.
* `AlgebraicGeometry.BigHOver.isZero_cechCohomology_awn`: the positive degree Čech cohomology of
  `X ↦ Γ(Xᵃʷⁿ, 𝒪)` vanishes on standard fppf coverings.

## References

* [Stacks Project, Tag 0EWT](https://stacks.math.columbia.edu/tag/0EWT)
* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Commutative rings to abelian groups, with the universe raised to `u + 1`, the universe of
the objects of the big site and of its coefficients. -/
abbrev addULift : CommRingCat.{u} ⥤ AddCommGrpCat.{u + 1} :=
  forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat ⋙ AddCommGrpCat.uliftFunctor.{u + 1}

/-- The functor from the big h category over `S` to the slice of all schemes over `S`. -/
abbrev toOverS : BigHOver B S hS ⥤ Over S :=
  Over.post B.inclusion

/-- The functor from the big h category over `S` to the slice of all schemes over `S` preserves
fibre products: followed by the forgetful functor it is the inclusion of the site into schemes,
which preserves them, and the forgetful functor reflects connected limits. -/
instance preservesLimitsOfShape_walkingCospan_toOverS :
    PreservesLimitsOfShape WalkingCospan (toOverS B S hS) := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let : PreservesLimitsOfShape WalkingCospan (toOverS B S hS ⋙ Over.forget S) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (BigHOver.toScheme B S hS))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget S)

/-! ### The structure sheaf -/

variable {B S hS}

/-- **Čech vanishing for the structure sheaf.** On a standard fppf covering of an object of the
site with affine underlying scheme, the positive degree Čech cohomology of the abelian presheaf
of global functions, with its universe raised, vanishes. This is Stacks 03FJ, read on the slice
of all schemes over `S` along the functor from the site, which preserves the fibre products. -/
theorem isZero_cechCohomology_sections {U : BigHOver B S hS} {E : PreZeroHypercover.{u} U}
    (hE : IsStandardFppf B S hS E) (n : ℕ) (hn : 0 < n) :
    IsZero (Stacks.CechSite.cechCohomology E (sectionsRingPresheaf B S hS ⋙ addULift) n) := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  obtain ⟨hU, hstd⟩ := hE
  let Φ := toOverS B S hS
  have : IsAffine (Φ.obj U).left := hU
  have hcomp : ∀ (p : ℕ) (i : Fin (p + 1) → E.I₀),
      IsIso (Stacks.CechSite.cechProductMapOfFunctor Φ E p i) := by
    intro p i
    let : PreservesLimit (Discrete.functor (fun a ↦ Over.mk (E.f (i a)))) (Over.post (X := U) Φ) :=
      Stacks.Sites.preservesLimit_fibreProducts_overPost Φ E
        (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) p i
    exact Stacks.CechSite.isIso_cechProductMapOfFunctor Φ E p i
  have h₀ : IsZero (Stacks.CechSite.cechCohomology (E.map Φ)
      (quasiCoherentPresheafFunctor S (Scheme.unitModule S)) n) :=
    isZero_cechCohomology_succ_quasiCoherentPresheaf (Φ.obj U) .fppf (Scheme.unitModule S)
      (E.map Φ) hstd n hn
  have h₁ : IsZero (Stacks.CechSite.cechCohomology (E.map Φ) (globalFunctionsAddPresheaf S) n) :=
    h₀.of_iso ((HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((Stacks.CechSite.cechComplexFunctor (E.map Φ)).mapIso
        (quasiCoherentPresheafUnitIso S))).symm
  have h₂ : IsZero (Stacks.CechSite.cechCohomology E (Φ.op ⋙ globalFunctionsAddPresheaf S) n) :=
    Stacks.CechSite.cechCohomology_isZero_of_isZero_of_functor Φ E _ hcomp n h₁
  exact Stacks.CechSite.isZero_cechCohomology_comp_coefficients E
    AddCommGrpCat.uliftFunctor.{u + 1} (Φ.op ⋙ globalFunctionsAddPresheaf S) n h₂

/-! ### The Frobenius tower and its colimit -/

/-- The forgetful functor of abelian groups preserves sequential colimits. -/
instance preservesColimitsOfShape_nat_forget_addCommGrpCat :
    PreservesColimitsOfShape ℕ (CategoryTheory.forget AddCommGrpCat.{u + 1}) := by
  have : PreservesFilteredColimitsOfSize.{0, 0} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  infer_instance

section Perfection

variable (p : ℕ) [Fact p.Prime] (hSp : Stacks.Frobenius.IsInCharacteristic S p)

/-- A global function on an object with affine underlying scheme whose image at some stage of
the Frobenius colimit vanishes is nilpotent: the absolute weak normalization is surjective, so
the basic open of the function is empty. -/
theorem isNilpotent_of_awnStageFun_eq_zero {X : BigHOver B S hS}
    (hX : IsAffine ((BigHOver.toScheme B S hS).obj X)) (n : ℕ)
    (a : Γ((BigHOver.toScheme B S hS).obj X, ⊤)) (h : awnStageFun B S hS p hSp n X a = 0) :
    IsNilpotent a := by
  let Z := (BigHOver.toScheme B S hS).obj X
  have h0 : Z.absoluteWeakNormalizationHom.appTop a = 0 := by
    rw [← awnStageFun_pow B S hS p hSp n X a, h,
      zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero)]
  rw [Scheme.isNilpotent_iff_basicOpen_eq_bot]
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  obtain ⟨y, rfl⟩ := ((universalHomeomorphism_iff_integral_universallyInjective_surjective _).mp
    (universalHomeomorphism_absoluteWeakNormalizationHom Z)).2.2.surj x
  have hy : y ∈ Z.absoluteWeakNormalizationHom ⁻¹ᵁ Z.basicOpen a := hx
  rwa [Scheme.preimage_basicOpen_top, h0, Scheme.basicOpen_zero] at hy

variable (B S hS)

/-- **The Frobenius tower `𝒪 →^F 𝒪 →^F ⋯`** of abelian presheaves on the big h category over a
scheme over `𝔽_p`, with the universe raised to the coefficient universe of the site. -/
def perfectionTower : ℕ ⥤ ((BigHOver B S hS)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  Functor.ofSequence (X := fun _ ↦ sectionsRingPresheaf B S hS ⋙ addULift)
    (fun _ ↦ Functor.whiskerRight (frobeniusSections B S hS p hSp) addULift)

/-- Every transition map of the Frobenius tower is the Frobenius. -/
theorem perfectionTower_map_succ (n : ℕ) :
    (perfectionTower B S hS p hSp).map (homOfLE n.le_succ) =
      Functor.whiskerRight (frobeniusSections B S hS p hSp) addULift :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- The cocone on the Frobenius tower with vertex the abelian presheaf underlying
`X ↦ Γ(Xᵃʷⁿ, 𝒪)`, given by the stage maps. -/
def perfectionTowerCocone : Cocone (perfectionTower B S hS p hSp) where
  pt := (awnRingSheaf B S hS).obj ⋙ addULift
  ι := NatTrans.ofSequence
    (fun n ↦ Functor.whiskerRight (perfectionStage B S hS p hSp n) addULift)
    (fun n ↦ by
      rw [perfectionTower_map_succ]
      exact (Functor.whiskerRight_comp _ _ _).symm.trans
        ((congrArg (fun φ ↦ Functor.whiskerRight φ addULift)
          (frobeniusSections_comp_perfectionStage B S hS p hSp n)).trans
            (Category.comp_id _).symm))

/-- **The comparison `colim_F 𝒪 ⟶ 𝒪^{perf}`** of abelian presheaves, from the colimit of the
Frobenius tower to the abelian presheaf underlying `X ↦ Γ(Xᵃʷⁿ, 𝒪)`. -/
def perfectionTowerDesc :
    colimit (perfectionTower B S hS p hSp) ⟶ (awnRingSheaf B S hS).obj ⋙ addULift :=
  colimit.desc _ (perfectionTowerCocone B S hS p hSp)

/-- Moving a representative of the colimit of the Frobenius tower one stage up raises it to the
`p`-th power. -/
theorem perfectionTower_ι_app_succ (n : ℕ) (X : (BigHOver B S hS)ᵒᵖ)
    (a : (sectionsRingPresheaf B S hS).obj X) :
    (colimit.ι (perfectionTower B S hS p hSp) n).app X (ULift.up a) =
      (colimit.ι (perfectionTower B S hS p hSp) (n + 1)).app X (ULift.up (a ^ p)) := by
  have h := colimit.w (perfectionTower B S hS p hSp) (homOfLE n.le_succ)
  rw [perfectionTower_map_succ] at h
  refine (ConcreteCategory.congr_hom (congr_app h X) (ULift.up a)).symm.trans ?_
  show (colimit.ι (perfectionTower B S hS p hSp) (n + 1)).app X
    (ULift.up ((frobeniusSections B S hS p hSp).app X a)) = _
  rw [frobeniusSections_app_apply]

/-- Moving a representative `k` stages up raises it to the `pᵏ`-th power. -/
theorem perfectionTower_ι_app_add (n k : ℕ) (X : (BigHOver B S hS)ᵒᵖ)
    (a : (sectionsRingPresheaf B S hS).obj X) :
    (colimit.ι (perfectionTower B S hS p hSp) n).app X (ULift.up a) =
      (colimit.ι (perfectionTower B S hS p hSp) (n + k)).app X (ULift.up (a ^ p ^ k)) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_one]
    rfl
  | succ k ih =>
    rw [ih, perfectionTower_ι_app_succ, ← pow_mul, ← pow_succ]
    rfl

/-- The comparison sends the stage `n` representative of a global function to its stage `n`
image on the absolute weak normalization. -/
theorem perfectionTowerDesc_app_ι (n : ℕ) (X : (BigHOver B S hS)ᵒᵖ)
    (a : (sectionsRingPresheaf B S hS).obj X) :
    (perfectionTowerDesc B S hS p hSp).app X
        ((colimit.ι (perfectionTower B S hS p hSp) n).app X (ULift.up a)) =
      ULift.up (awnStageFun B S hS p hSp n X.unop a) :=
  (ConcreteCategory.congr_hom (congr_app (colimit.ι_desc (perfectionTowerCocone B S hS p hSp) n)
    X) (ULift.up a)).trans (congrArg ULift.up (perfectionStage_app_apply B S hS p hSp n X a))

/-- Every section of the colimit of the Frobenius tower is represented at some stage. -/
theorem exists_perfectionTower_ι_app_eq (X : (BigHOver B S hS)ᵒᵖ)
    (z : (colimit (perfectionTower B S hS p hSp)).obj X) :
    ∃ (n : ℕ) (a : (sectionsRingPresheaf B S hS).obj X),
      (colimit.ι (perfectionTower B S hS p hSp) n).app X (ULift.up a) = z := by
  let e := colimitObjIsoColimitCompEvaluation (perfectionTower B S hS p hSp) X
  obtain ⟨n, y, hy⟩ := Concrete.colimit_exists_rep
    (perfectionTower B S hS p hSp ⋙ (evaluation _ _).obj X) (e.hom z)
  exact ⟨n, y.down, (ConcreteCategory.congr_hom
    (colimitObjIsoColimitCompEvaluation_ι_inv (perfectionTower B S hS p hSp) n X) y).symm.trans
      ((congrArg e.inv hy).trans (e.hom_inv_id_apply z))⟩

/-- **`colim_F Γ(X, 𝒪) = Γ(Xᵃʷⁿ, 𝒪)` on affine objects.** The comparison from the colimit of the
Frobenius tower to the abelian presheaf underlying `X ↦ Γ(Xᵃʷⁿ, 𝒪)` is invertible on every
object with affine underlying scheme. -/
theorem isIso_perfectionTowerDesc_app (X : BigHOver B S hS)
    (hX : IsAffine ((BigHOver.toScheme B S hS).obj X)) :
    IsIso ((perfectionTowerDesc B S hS p hSp).app (op X)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨?_, fun y ↦ ?_⟩
  · refine (injective_iff_map_eq_zero ((perfectionTowerDesc B S hS p hSp).app (op X)).hom).mpr
      fun z hz ↦ ?_
    obtain ⟨n, a, rfl⟩ := exists_perfectionTower_ι_app_eq B S hS p hSp (op X) z
    have hz' : awnStageFun B S hS p hSp n X a = 0 :=
      congrArg ULift.down ((perfectionTowerDesc_app_ι B S hS p hSp n (op X) a).symm.trans hz)
    obtain ⟨m, hm⟩ := isNilpotent_of_awnStageFun_eq_zero p hSp hX n a hz'
    have hpm : a ^ p ^ m = 0 :=
      pow_eq_zero_of_le (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le hm
    rw [perfectionTower_ι_app_add B S hS p hSp n m, hpm]
    exact map_zero ((colimit.ι (perfectionTower B S hS p hSp) (n + m)).app (op X)).hom
  · obtain ⟨n, a, -, ha, -⟩ := exists_awnStageFun_eq_pair B S hS p hSp X hX y.down y.down
    exact ⟨(colimit.ι (perfectionTower B S hS p hSp) n).app (op X) (ULift.up a),
      (perfectionTowerDesc_app_ι B S hS p hSp n (op X) a).trans (congrArg ULift.up ha)⟩

/-- The big h category over `S` has finite wide pullbacks, so its slices have finite products:
the iterated fibre products of a family exist. -/
instance hasFiniteWidePullbacks_bigHOver : HasFiniteWidePullbacks (BigHOver B S hS) :=
  hasFiniteWidePullbacks_of_hasFiniteLimits _

include hSp in
variable {B S hS} in
/-- **Čech vanishing for `𝒪^{perf}`.** On a standard fppf covering of an object of the site with
affine underlying scheme, the positive degree Čech cohomology of the abelian presheaf underlying
`X ↦ Γ(Xᵃʷⁿ, 𝒪)`, with its universe raised, vanishes.

The iterated fibre products of the covering are affine, where `X ↦ Γ(Xᵃʷⁿ, 𝒪)` is the colimit
of the Frobenius tower; the Čech complex of that colimit is the colimit of the Čech complexes of
the structure sheaf, which are exact in positive degrees. -/
theorem isZero_cechCohomology_awn {U : BigHOver B S hS} {E : PreZeroHypercover.{u} U}
    (hE : IsStandardFppf B S hS E) (n : ℕ) (hn : 0 < n) :
    IsZero (Stacks.CechSite.cechCohomology E ((awnRingSheaf B S hS).obj ⋙ addULift) n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have := hE.finite
  obtain ⟨hU, hX⟩ := hE.isAffine
  have hcolim := Stacks.CechSite.exactAt_succ_cechComplex_colimit E
    (perfectionTower B S hS p hSp) k (fun j ↦ by
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact isZero_cechCohomology_sections hE (k + 1) (Nat.succ_pos k))
  have hiso := Stacks.CechSite.isIso_cechComplexFunctor_map (A := AddCommGrpCat.{u + 1}) E
    (perfectionTowerDesc B S hS p hSp)
    (fun m i ↦ isIso_perfectionTowerDesc_app B S hS p hSp _
      (isAffine_toScheme_piObj hU E hX m i))
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hcolim
  exact hcolim.of_iso ((HomologicalComplex.homologyFunctor _ _ (k + 1)).mapIso
    (asIso ((Stacks.CechSite.cechComplexFunctor E).map (perfectionTowerDesc B S hS p hSp)))).symm

end Perfection

end AlgebraicGeometry.BigHOver
