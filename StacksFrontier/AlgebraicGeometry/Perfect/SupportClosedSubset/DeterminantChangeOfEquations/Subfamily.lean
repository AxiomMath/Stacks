module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DerivedSupportInvertsAugmentation
public import
  StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.QuasicoherentSupportedComplexes
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedFractionMap

/-!
# Subfamily projections of the extended alternating Čech complex

The cofactor identity `cofactorSum_eq_zero`; the projection `subfamilyCplxMap` of the extended
alternating Čech complex of a family of equations onto that of a subfamily; the fact that derived
sections with support invert these projections, and the canonical comparison
`cechToDerivedSupport` of Stacks 0G7L; transport `prodTermCongr` along an equality of families.
Part of `StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DeterminantChangeOfEquations`.

* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 0G72](https://stacks.math.columbia.edu/tag/0G72)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ModuleLimits (homOfSections homOfSections_app)
open Stacks.Perfect.ExtendedAlternatingCech
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.SupportedFraction

attribute [local instance] Classical.propDecidable

variable {X : Scheme.{u}}

/-! ### A cofactor identity -/

/-- If the `c + 1` rows `v 0, …, v c` of a matrix with `c` columns are paired with a column
vector `f`, then the signed sum of the products `(v i ⬝ f) · det(v with row i removed)`
vanishes: the `(c + 1) × (c + 1)` matrix whose zeroth column is `v ⬝ f` and whose remaining
columns are `v` has a column that is a linear combination of the others, hence determinant
zero, and expanding that determinant along the zeroth column is the displayed sum. -/
public theorem cofactorSum_eq_zero {R : Type u} [CommRing R] {c : ℕ}
    (f : Fin c → R) (v : Fin (c + 1) → Fin c → R) :
    ∑ i : Fin (c + 1), (-1 : R) ^ (i : ℕ) * (∑ j, v i j * f j) *
      (Matrix.of (fun r j => v (i.succAbove r) j)).det = 0 := by
  let B : Matrix (Fin (c + 1)) (Fin (c + 1)) R := fun i =>
    Fin.cases (∑ j, v i j * f j) (v i)
  let d : Fin (c + 1) → R := Fin.cases 0 f
  have hcol : (fun i => ∑ j, d j * B i j) = B.col 0 := by
    funext i
    change (∑ j, d j * B i j) = B i 0
    calc
      (∑ j, d j * B i j) = ∑ j, f j * v i j := by
        simp [d, B, Fin.sum_univ_succ]
      _ = ∑ j, v i j * f j := Finset.sum_congr rfl fun _ _ => mul_comm _ _
      _ = B i 0 := by simp [B]
  have hu : B.updateCol 0 (fun k => ∑ i, d i • B k i) = B := by
    ext i j
    by_cases hj : j = 0
    · subst j
      rw [Matrix.updateCol_self]
      change (∑ k, d k * B i k) = B i 0
      simpa using congrFun hcol i
    · rw [Matrix.updateCol_apply]
      simp [hj]
  have hdet : B.det = 0 := by
    have h := Matrix.det_updateCol_sum B 0 d
    rw [hu] at h
    simpa [d] using h
  rw [Matrix.det_succ_column_zero B] at hdet
  simpa [B, Matrix.submatrix, Matrix.of, Fin.cases] using hdet

/-! ### Restricting the extended alternating Čech complex to a subfamily of the equations -/

section Subfamily

variable {m n : ℕ} (e : Fin n → Γ(X, ⊤)) (φ : Fin m ↪o Fin n) (F : X.Modules)

/-- An increasing tuple of indices of a subfamily, read as an increasing tuple of indices of
the whole family. -/
public def subfamilyIndex {p : ℕ} (q : CechCochains.OrdIndex (I := Fin m) p) :
    CechCochains.OrdIndex (I := Fin n) p :=
  ⟨φ ∘ q.1, φ.strictMono.comp q.2⟩

/-- The projection of a positive-degree term of the extended alternating Čech complex of a
family of equations onto the corresponding term for a subfamily: it keeps the components
indexed by tuples of indices of the subfamily. -/
public def subfamilyProd (p : ℕ) : prodTerm e F p ⟶ prodTerm (e ∘ φ) F p :=
  Pi.lift fun q => Pi.π (fun t : CechCochains.OrdIndex (I := Fin n) p =>
    restrictedModule e F p t) (subfamilyIndex φ q)

/-- On sections, the subfamily projection restricts a cochain to the tuples of indices of the
subfamily. -/
public theorem secIso_subfamilyProd (p : ℕ) (V : X.Opens) (x : Γ(prodTerm e F p, V))
    (q : CechCochains.OrdIndex (I := Fin m) p) :
    secIso (e ∘ φ) F p V ((subfamilyProd e φ F p).app V x) q =
      secIso e F p V x (subfamilyIndex φ q) := by
  have h₁ : subfamilyProd e φ F p ≫ Pi.π (fun t : CechCochains.OrdIndex (I := Fin m) p =>
        restrictedModule (e ∘ φ) F p t) q =
      Pi.π (fun t : CechCochains.OrdIndex (I := Fin n) p => restrictedModule e F p t)
        (subfamilyIndex φ q) := Pi.lift_comp_π _ q
  have hπ : (Pi.π (fun t : CechCochains.OrdIndex (I := Fin m) p =>
        restrictedModule (e ∘ φ) F p t) q).app V ((subfamilyProd e φ F p).app V x) =
      appApplyHom V x (subfamilyProd e φ F p ≫
        Pi.π (fun t : CechCochains.OrdIndex (I := Fin m) p =>
          restrictedModule (e ∘ φ) F p t) q) := rfl
  rw [secIso_apply, hπ, h₁, secIso_apply]
  rfl

/-- The subfamily projection is compatible with the augmentation out of the coefficient
module. -/
public theorem difZero_subfamilyProd :
    difZero e F ≫ subfamilyProd e φ F 0 = difZero (e ∘ φ) F := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
  refine (secIso (e ∘ φ) F 0 V).injective ?_
  funext q
  rw [comp_app_apply, secIso_subfamilyProd, secIso_difZero, secIso_difZero]
  exact map_eq_apply F _ _ x

/-- The subfamily projection is compatible with the signed alternating differentials. -/
public theorem difSucc_subfamilyProd (p : ℕ) :
    difSucc e F p ≫ subfamilyProd e φ F (p + 1) =
      subfamilyProd e φ F p ≫ difSucc (e ∘ φ) F p := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
  refine (secIso (e ∘ φ) F (p + 1) V).injective ?_
  funext t
  rw [comp_app_apply, comp_app_apply, secIso_subfamilyProd, secIso_difSucc, secIso_difSucc,
    ordD_apply, ordD_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [secIso_subfamilyProd]
  rfl

/-- The chain map between the extended alternating Čech complexes given in positive degrees by
the subfamily projections and in degree `0` by the identity of the coefficient module. -/
public def subfamilyCplxMap : cplx e F ⟶ cplx (e ∘ φ) F where
  f n := match n with
    | 0 => 𝟙 F
    | (p + 1) => subfamilyProd e φ F p
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    cases i with
    | zero =>
      rw [show (cplx (e ∘ φ) F).d 0 (0 + 1) = difZero (e ∘ φ) F from cplx_d_zero (e ∘ φ) F,
        show (cplx e F).d 0 (0 + 1) = difZero e F from cplx_d_zero e F]
      refine Eq.trans ?_ (difZero_subfamilyProd e φ F).symm
      exact Category.id_comp _
    | succ p =>
      rw [show (cplx (e ∘ φ) F).d (p + 1) (p + 1 + 1) = difSucc (e ∘ φ) F p from
          cplx_d_succ (e ∘ φ) F p,
        show (cplx e F).d (p + 1) (p + 1 + 1) = difSucc e F p from cplx_d_succ e F p]
      exact (difSucc_subfamilyProd e φ F p).symm

/-- The subfamily chain map is the identity in degree `0`. -/
public theorem subfamilyCplxMap_f_zero : (subfamilyCplxMap e φ F).f 0 = 𝟙 F := rfl

/-- The subfamily chain map is the subfamily projection in positive degrees. -/
public theorem subfamilyCplxMap_f_succ (p : ℕ) :
    (subfamilyCplxMap e φ F).f (p + 1) = subfamilyProd e φ F p := rfl

end Subfamily

/-! ### Derived sections with support invert the subfamily projections -/

section Derived

-- The locally small model of the derived category arrives as a *global* instance through the
-- imports, and a global instance beats a default-priority local one; every library statement
-- used here is elaborated at the standard model, so the standard model is given a priority
-- that wins.  This is the convention of `Stacks.Perfect.SupportedQuasicoherent`.
attribute [local instance 10000] HasDerivedCategory.standard

open ExtensionByZeroModules
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.CechDerivedSupport
open Stacks.Perfect.ExtendedAlternatingCech.Augmentation
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward
  derivedSupportedPushforwardUnit isZero_of_homology_isZero
  isIso_derivedSupportedSectionsToId_app_of_supported)

variable {m n : ℕ} (e : Fin n → Γ(X, ⊤)) (φ : Fin m ↪o Fin n) (F : X.Modules)

/-- The common zero locus of a family of equations is contained in the common zero locus of any
subfamily. -/
public theorem equationsClosedSet_subset_subfamily :
    equationsClosedSet e ⊆ equationsClosedSet (e ∘ φ) := by
  have hle : (⨆ i, X.basicOpen ((e ∘ φ) i)) ≤ (⨆ k, X.basicOpen (e k)) :=
    iSup_le fun i => le_iSup (fun k => X.basicOpen (e k)) (φ i)
  exact fun _ hx hx' => hx (hle hx')

/-- **Stacks Project, Tag 0G7M**, the step that uses quasi-coherence, for sections supported on
an arbitrary closed subset of the common zero locus of the equations rather than on the whole
locus.  This is the form needed when two families of equations are compared: the common zero
locus of the larger family is contained in that of either subfamily, so one derived functor
inverts the augmentations of all the complexes in play. -/
public theorem isIso_map_augmentation_of_subset {c : ℕ} (f : Fin c → Γ(X, ⊤)) (G : X.Modules)
    [G.IsQuasicoherent] {Z : Set X} (hZ : IsClosed Z) (hZsub : Z ⊆ equationsClosedSet f)
    (RH : DerivedCategory X.Modules ⥤
      DerivedCategory (SheafOfModules.{u}
        (structureSheafRing (closedSubsetRingedSpace X.toRingedSpace Z))))
    (αH : (schemeSupportedSectionsFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)
    (hRH : RH.IsRightDerivedFunctor αH
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))) :
    IsIso (RH.map (augmentation f G)) :=
  let _ := hRH
  Stacks.Perfect.CechAugmentation.isIso_map_augmentation_of_isZero_obj_single_restrictedModule
    f G (schemeSupportedSectionsFunctor X Z hZ) RH αH fun _ s =>
    isZero_obj_single_restrictedModule f G hZ hZsub s RH αH

/-- The subfamily projection commutes with the projections onto the degree-`0` term. -/
public theorem subfamilyCplxMap_comp_augmentationComplex :
    subfamilyCplxMap e φ F ≫ augmentationComplex (e ∘ φ) F = augmentationComplex e F := by
  refine HomologicalComplex.hom_ext _ _ fun k => ?_
  match k with
  | 0 =>
      refine Eq.trans (congrArg (fun ψ => ψ ≫ (augmentationComplex (e ∘ φ) F).f 0)
        (subfamilyCplxMap_f_zero e φ F)) ?_
      refine Eq.trans (Category.id_comp ((augmentationComplex (e ∘ φ) F).f 0)) ?_
      rfl
  | (p + 1) =>
      refine Eq.trans (congrArg (fun ψ => (subfamilyCplxMap e φ F).f (p + 1) ≫ ψ)
        (augmentationComplex_f_succ_eq_zero (e ∘ φ) F p)) ?_
      exact Eq.trans comp_zero (augmentationComplex_f_succ_eq_zero e F p).symm

/-- The subfamily projection is a morphism over the coefficient module: composed with the
augmentation of Stacks 0G7L for the subfamily it is the augmentation for the whole family. -/
public theorem Q_map_extendMap_subfamilyCplxMap_comp_augmentation :
    DerivedCategory.Q.map (HomologicalComplex.extendMap (subfamilyCplxMap e φ F)
        ComplexShape.embeddingUpNat) ≫ augmentation (e ∘ φ) F = augmentation e F := by
  refine (DerivedCategory.Q.map_comp _ _).symm.trans (congrArg DerivedCategory.Q.map ?_)
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) ((HomologicalComplex.extendMap_comp _ _
    _).symm.trans (congrArg (HomologicalComplex.extendMap · _)
      (subfamilyCplxMap_comp_augmentationComplex e φ F))))

/-- **The subfamily projection represents the identity on `i_*R𝓗_Z(ℱ)`**, the step of the proof
of Stacks 0G7S which says that the projections out of the mixed complex "represent the identity
on this object".

Let `Z` be the common zero locus of the whole family `e₁, …, e_n`, let `ℱ` be quasi-coherent and
let `R𝓗_Z` be a derived functor of sections supported on `Z`.  The projection from the extended
alternating Čech complex of `e₁, …, e_n` onto that of a subfamily becomes an isomorphism under
`R𝓗_Z`: both augmentations to `ℱ[0]` are inverted by `R𝓗_Z` — for the whole family because
`Z` is its zero locus, for the subfamily because `Z` is contained in its zero locus — and the
projection commutes with them. -/
public theorem isIso_map_Q_map_extendMap_subfamilyCplxMap [F.IsQuasicoherent]
    (RH : DerivedCategory X.Modules ⥤
      DerivedCategory (SheafOfModules.{u}
        (structureSheafRing (closedSubsetRingedSpace X.toRingedSpace (equationsClosedSet e)))))
    (αH : (schemeSupportedSectionsFunctor X (equationsClosedSet e)
        (isClosed_equationsClosedSet e)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)
    (hRH : RH.IsRightDerivedFunctor αH
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))) :
    IsIso (RH.map (DerivedCategory.Q.map (HomologicalComplex.extendMap
      (subfamilyCplxMap e φ F) ComplexShape.embeddingUpNat))) := by
  have h₁ : IsIso (RH.map (augmentation (e ∘ φ) F)) :=
    isIso_map_augmentation_of_subset (e ∘ φ) F (isClosed_equationsClosedSet e)
      (equationsClosedSet_subset_subfamily e φ) RH αH hRH
  have h₂ : IsIso (RH.map (augmentation e F)) :=
    isIso_map_augmentation_of_subset e F (isClosed_equationsClosedSet e) subset_rfl RH αH hRH
  have hcomp : RH.map (DerivedCategory.Q.map (HomologicalComplex.extendMap
          (subfamilyCplxMap e φ F) ComplexShape.embeddingUpNat)) ≫
        RH.map (augmentation (e ∘ φ) F) = RH.map (augmentation e F) :=
    Eq.trans (RH.map_comp _ _).symm
      (congrArg RH.map (Q_map_extendMap_subfamilyCplxMap_comp_augmentation e φ F))
  have h₄ : IsIso (RH.map (DerivedCategory.Q.map (HomologicalComplex.extendMap
      (subfamilyCplxMap e φ F) ComplexShape.embeddingUpNat)) ≫
      RH.map (augmentation (e ∘ φ) F)) := by
    rw [hcomp]
    exact h₂
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (RH.map (augmentation (e ∘ φ) F)) h₁ h₄

/-- **The subfamily projection represents the identity on `i_*R𝓗_Z(ℱ)`**, for the chosen total
right derived functor `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosed` of
sections supported on the common zero locus of the whole family. -/
public theorem isIso_derivedSupportedSectionsOnClosed_map_Q_map_extendMap_subfamilyCplxMap
    [F.IsQuasicoherent] :
    IsIso ((derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet e)
      (isClosed_equationsClosedSet e)).map (DerivedCategory.Q.map
        (HomologicalComplex.extendMap (subfamilyCplxMap e φ F)
          ComplexShape.embeddingUpNat))) :=
  isIso_map_Q_map_extendMap_subfamilyCplxMap e φ F
    (derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet e)
      (isClosed_equationsClosedSet e))
    (derivedSupportedSectionsOnClosedUnit X.toRingedSpace (equationsClosedSet e)
      (isClosed_equationsClosedSet e))
    (inferInstanceAs ((derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet e)
      (isClosed_equationsClosedSet e)).IsRightDerivedFunctor
        (derivedSupportedSectionsOnClosedUnit X.toRingedSpace (equationsClosedSet e)
          (isClosed_equationsClosedSet e))
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ))))

/-! ### The canonical comparison of Stacks 0G7L -/

/-- **The extended alternating Čech complex is supported on the common zero locus.** Every
cohomology sheaf of `𝓕^•` has vanishing stalks outside the common zero locus of the equations,
because `𝓕^•` restricted to the union of the principal opens is acyclic (Stacks 0G7K).

This is the first assertion of Remark 0G7L, `𝓕^• ∈ D_Z(𝒪_X)`: `CohomologySupportedOn` is the
property cutting out `D_Z(𝒪_X)` inside `D(𝒪_X)`, so membership in the supported derived category
*is* this statement, and it is what makes the adjunction of Stacks 0AEF applicable to `𝓕^•` in
the rest of the remark.  The remark deduces it from Stacks 0G7K, whose own carrier is
`cohomologySupportedOn_extendedAlternatingCech`; what is registered here is the deduction, at
the derived-category spelling that the remark's diagram and the comparison
`cechToDerivedSupport` below are stated at.  No hypothesis beyond the remark's is carried: `ℱ`
is an arbitrary `𝒪_X`-module and the equations are arbitrary. -/
@[stacks 0G7L "the first assertion of the remark: the cohomology sheaves of 𝓕^• are supported on
the common zero locus, hence 𝓕^• is an object of D_Z(𝒪_X).  Deduced from Stacks 0G7K, stated at
the derived-category spelling the remark's diagram uses, for an arbitrary 𝒪_X-module ℱ"]
public theorem cohomologySupportedOn_cech :
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace)
      (equationsClosedSet e)
      (DerivedCategory.Q.obj ((cplx e F).extend ComplexShape.embeddingUpNat)) := by
  set U : X.Opens := ⨆ i, X.basicOpen (e i) with hU
  set O := structureSheafRing X.toRingedSpace with hO
  set E := DerivedCategory.Q.obj ((cplx e F).extend ComplexShape.embeddingUpNat) with hE
  have hacy : (((jStar U O).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((cplx e F).extend ComplexShape.embeddingUpNat)).Acyclic :=
    Stacks.Perfect.CechSupportRepresentation.acyclic_jStar_extend_of_acyclic _
      (Stacks.Perfect.CechSupportRepresentation.acyclic_jStar_of_acyclic_modulePullback _
        (Stacks.Perfect.CechComplexComparison.acyclic_restrict (data e F)))
  have hzero : IsZero ((jStar U O).mapDerivedCategory.obj E) := by
    refine IsZero.of_iso ?_ (((jStar U O).mapDerivedCategoryFactors).app
      ((cplx e F).extend ComplexShape.embeddingUpNat))
    refine isZero_of_homology_isZero _ fun n => ?_
    refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors _ n).app _)
    rw [HomologicalComplex.acyclic_iff] at hacy
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ n).1 (hacy n)
  intro i x hx
  have hM : IsZero ((jStar U O).obj
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) i).obj E)) := by
    refine IsZero.of_iso (Functor.map_isZero
      (DerivedCategory.homologyFunctor (SheafOfModules.{u} (resRing U O)) i) hzero) ?_
    exact ((exactFunctorDerivedHomologyIso (jStar U O) i).app E).symm
  have hxU : x ∈ U := by simpa [hU, equationsClosedSet] using hx
  have hS := (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero
    ((SheafOfModules.toSheaf (resRing U O)).obj ((jStar U O).obj
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) i).obj E)))).mp
    (Functor.map_isZero (SheafOfModules.toSheaf (resRing U O)) hM) ⟨x, hxU⟩
  exact hS.of_iso (TopCat.Presheaf.stalkRestrictIso U
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) i).obj E).val.presheaf ⟨x, hxU⟩).symm

variable {T : Set X} (hT : IsClosed T)

/-- `i_* R𝓗_T : D(𝒪_X) ⥤ D(𝒪_X)`, the chosen derived functor of sections supported on the closed
subset `T` followed by the exact direct image from `T`. -/
public abbrev supportPush :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
  derivedSupportedPushforward X.toRingedSpace T hT

/-- The canonical map `i_* R𝓗_T(K) ⟶ K` of Stacks 0G72, the counit of the adjunction of
Stacks 0A3B. -/
public abbrev supportPushCounit : supportPush hT ⟶ Functor.id _ :=
  derivedSupportedSectionsToId X.toRingedSpace T (supportPush hT)
    (derivedSupportedPushforwardUnit X.toRingedSpace T hT)

/-- **Stacks 0G7M, the acyclicity half, with the comparison as a canonical term.** The counit
`i_* R𝓗_T(𝓕^•) ⟶ 𝓕^•` of Stacks 0G72 is invertible at the extended alternating Čech complex of
a family of equations whose common zero locus is contained in `T`: the complex is supported
there, so the third vertex `Rj_*(𝓕^•|_U)` of the triangle vanishes.

This is the content of `nonempty_pushforwardDerivedSupportCechIso`, with the isomorphism being
the canonical map rather than one produced on a chosen K-injective resolution; only the
invertibility is asserted, and invertibility is a proposition, so nothing is chosen. -/
@[stacks 0G7M "the canonical counit i_*RℋT(𝓕^•) ⟶ 𝓕^• of Stacks 0G72 is invertible at the
extended alternating Čech complex, for every closed T containing the common zero locus of the
equations.  The theorem nonempty_pushforwardDerivedSupportCechIso asserts the same isomorphism
without naming it, because it is produced on a chosen K-injective resolution; here only
invertibility of the canonical map is asserted, and invertibility is a proposition, so nothing
is chosen"]
public theorem isIso_derivedSupportedSectionsToId_cech (hTe : equationsClosedSet e ⊆ T) :
    IsIso ((supportPushCounit hT).app
      (DerivedCategory.Q.obj ((cplx e F).extend ComplexShape.embeddingUpNat))) :=
  isIso_derivedSupportedSectionsToId_app_of_supported X.toRingedSpace T hT _
    fun i x hx => cohomologySupportedOn_cech e F i x fun h => hx (hTe h)

/-- **The canonical comparison of Stacks 0G7L**, `𝓕^• ⟶ i_* R𝓗_T(ℱ)`.

It is the inverse of the counit `i_* R𝓗_T(𝓕^•) ⟶ 𝓕^•`, invertible by
`isIso_derivedSupportedSectionsToId_cech`, followed by `i_* R𝓗_T` applied to the augmentation
`𝓕^• ⟶ ℱ[0]` of Stacks 0G7L.  This is the map whose degree-`c` cohomology sheaf Stacks 0G7Q
uses to define `c_{f₁,…,f_c}`.

As in the source, `ℱ` is an arbitrary `𝒪_X`-module: the counit is invertible at `𝓕^•` because
`𝓕^•` is supported on the common zero locus of the equations, which is Stacks 0G7K and holds
for every `ℱ`.  Quasi-coherence enters only later, in Stacks 0G7M, where the *other* leg of the
triangle — `i_* R𝓗_T` applied to the augmentation — is shown to be invertible. -/
@[stacks 0G7L "the canonical comparison 𝓕^• ⟶ i_*RℋT(ℱ), built from the counit of Stacks 0G72
and the augmentation, for an arbitrary 𝒪_X-module ℱ"]
public def cechToDerivedSupport (hTe : equationsClosedSet e ⊆ T) :
    DerivedCategory.Q.obj ((cplx e F).extend ComplexShape.embeddingUpNat) ⟶
      (supportPush hT).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F) :=
  (@asIso _ _ _ _ _ (isIso_derivedSupportedSectionsToId_cech e F hT hTe)).inv ≫
    (supportPush hT).map (augmentation e F)

/-- **The comparison of Stacks 0G7L is characterised by the counit**: preceded by the counit
`i_* R𝓗_T(𝓕^•) ⟶ 𝓕^•` of Stacks 0G72 — invertible at `𝓕^•` by
`isIso_derivedSupportedSectionsToId_cech` — it is `i_* R𝓗_T` applied to the augmentation
`𝓕^• ⟶ ℱ[0]`.  This is how the comparison is built, and it determines it.

It is not the triangle the remark displays; that is
`cechToDerivedSupport_comp_derivedSupportedSectionsToId`, whose third edge is the counit at
`ℱ[0]` rather than at `𝓕^•`. -/
public theorem derivedSupportedSectionsToId_comp_cechToDerivedSupport
    (hTe : equationsClosedSet e ⊆ T) :
    (supportPushCounit hT).app
          (DerivedCategory.Q.obj ((cplx e F).extend ComplexShape.embeddingUpNat)) ≫
        cechToDerivedSupport e F hT hTe =
      (supportPush hT).map (augmentation e F) := by
  rw [cechToDerivedSupport]
  exact (@asIso _ _ _ _ _ (isIso_derivedSupportedSectionsToId_cech e F hT hTe)).hom_inv_id_assoc _

/-- **The commuting triangle of Stacks 0G7L**, in the shape the remark displays:

`𝓕^• ⟶ ℱ`, `𝓕^• ⟶ i_* R𝓗_T(ℱ)` and `i_* R𝓗_T(ℱ) ⟶ ℱ`

commute, the third edge being the counit of Stacks 0G72 at `ℱ[0]`.  So the canonical map
`𝓕^• ⟶ ℱ` of the remark — the augmentation, coming from the equality `𝓕^0 = ℱ` — factors
through `i_* R𝓗_T(ℱ)`, which is what the adjunction of Stacks 0A3B provides and what the remark
asserts. -/
@[stacks 0G7L "the commuting triangle 𝓕^• ⟶ ℱ, 𝓕^• ⟶ i_*RℋT(ℱ), i_*RℋT(ℱ) ⟶ ℱ of the remark's
diagram, for an arbitrary 𝒪_X-module ℱ"]
public theorem cechToDerivedSupport_comp_derivedSupportedSectionsToId
    (hTe : equationsClosedSet e ⊆ T) :
    cechToDerivedSupport e F hT hTe ≫
        (supportPushCounit hT).app ((DerivedCategory.singleFunctor X.Modules 0).obj F) =
      augmentation e F := by
  refine ((@asIso _ _ _ _ _
    (isIso_derivedSupportedSectionsToId_cech e F hT hTe)).cancel_iso_hom_left _ _).mp ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun ψ => ψ ≫ (supportPushCounit hT).app
      ((DerivedCategory.singleFunctor X.Modules 0).obj F))
    (derivedSupportedSectionsToId_comp_cechToDerivedSupport e F hT hTe)) ?_
  exact (supportPushCounit hT).naturality (augmentation e F)

/-- **The two projections of the source's proof are compatible with the comparison of Stacks
0G7L.** The projection of the extended alternating Čech complex of a family onto that of a
subfamily, followed by the comparison for the subfamily, is the comparison for the whole
family: both become, after the invertible counit, `i_* R𝓗_T` applied to the augmentation of the
whole family.

This is the step of the proof of Stacks 0G7S which says that the projections out of the mixed
complex "represent the identity on `i_* R𝓗_Z(ℱ)`". -/
public theorem Q_map_extendMap_subfamilyCplxMap_comp_cechToDerivedSupport
    (hTe : equationsClosedSet e ⊆ T) (hTeφ : equationsClosedSet (e ∘ φ) ⊆ T) :
    DerivedCategory.Q.map (HomologicalComplex.extendMap (subfamilyCplxMap e φ F)
          ComplexShape.embeddingUpNat) ≫ cechToDerivedSupport (e ∘ φ) F hT hTeφ =
      cechToDerivedSupport e F hT hTe := by
  refine ((@asIso _ _ _ _ _
    (isIso_derivedSupportedSectionsToId_cech e F hT hTe)).cancel_iso_hom_left _ _).mp ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun ψ => ψ ≫ cechToDerivedSupport (e ∘ φ) F hT hTeφ)
    ((supportPushCounit hT).naturality (DerivedCategory.Q.map
      (HomologicalComplex.extendMap (subfamilyCplxMap e φ F)
        ComplexShape.embeddingUpNat))).symm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun ψ => (supportPush hT).map (DerivedCategory.Q.map
      (HomologicalComplex.extendMap (subfamilyCplxMap e φ F) ComplexShape.embeddingUpNat)) ≫ ψ)
    (derivedSupportedSectionsToId_comp_cechToDerivedSupport (e ∘ φ) F hT hTeφ)) ?_
  refine Eq.trans ((supportPush hT).map_comp _ _).symm ?_
  refine Eq.trans (congrArg (supportPush hT).map
    (Q_map_extendMap_subfamilyCplxMap_comp_augmentation e φ F)) ?_
  exact (derivedSupportedSectionsToId_comp_cechToDerivedSupport e F hT hTe).symm

end Derived

/-! ### Transport along an equality of families of equations -/

section Congr

variable {m : ℕ} {e e' : Fin m → Γ(X, ⊤)}

/-- Two equal families of equations have equal positive-degree terms. -/
public def prodTermCongr (he : e = e') (F : X.Modules) (p : ℕ) :
    prodTerm e F p ⟶ prodTerm e' F p :=
  eqToHom (by rw [he])

/-- The transport along an equality of families of equations is the identity when the
equality is a reflexivity. -/
public theorem prodTermCongr_rfl (F : X.Modules) (p : ℕ) (he : e = e) :
    prodTermCongr he F p = 𝟙 (prodTerm e F p) := rfl

/-- Dividing by the product of the equations commutes with the transport along an equality of
families of equations. -/
public theorem fractionHom_prodTermCongr (he : e = e') (F : X.Modules) (p : ℕ) :
    fractionHom e F p ≫ prodTermCongr he F p = fractionHom e' F p := by
  subst he
  rw [prodTermCongr_rfl, Category.comp_id]

end Congr

end Stacks.Perfect.SupportedFraction

end
