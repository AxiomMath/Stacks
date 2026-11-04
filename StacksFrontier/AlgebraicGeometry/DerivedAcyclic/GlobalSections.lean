module

public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerived
public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedSections
public import StacksFrontier.AlgebraicGeometry.Cohomology.UniformVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.DerivedUpperBound
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived global sections of a complex with right-acyclic terms

Let `X` be a quasi-compact and quasi-separated scheme and let `K` be a cochain complex of
quasi-coherent `𝒪_X`-modules each of whose terms is right acyclic for `Γ(X, -)`. Then the
complex of global sections computes derived global sections: the canonical comparison
`Γ(X, K) ⟶ RΓ(X, K)` is an isomorphism in `D(Γ(X, 𝒪_X))`.

The shape of the proof is that of [Stacks, Tag 0G9N], with the target of the direct image
replaced by a point. What makes it run is a bound on the cohomological dimension of `RΓ(X, -)`
on complexes with quasi-coherent cohomology: a finite affine open covering of `X` has a
[Stacks, Tag 071L] degree `N` beyond which the cohomology of every quasi-coherent module
vanishes, and [Stacks, Tag 08D4] turns that into the statement that `RΓ(X, -)` carries `D^{≤d}`
with quasi-coherent cohomology into `D^{≤d+N-1}`. Given the bound, fix a cohomological degree `q`
and replace `K` by its stupid truncation `σ^{≥a}K` with `a < q` and `a + N ≤ q`: the truncation is
bounded below with right-acyclic terms, so the comparison is invertible there by Leray's
acyclicity criterion, and both `Γ(X, -)` and `RΓ(X, -)` see `σ^{≥a}K → K` as an isomorphism
on `H^q`.

The source proves this by applying [Stacks, Tag 0G9N] to the canonical morphism
`X ⟶ Spec Γ(X, 𝒪_X)`. That route needs the identification `H^i(X, F) ≅ Γ(Spec Γ(X, 𝒪_X),
R^i f_* F)` of [Stacks, Tag 01XK], which this library does not have; the route taken here uses
only the cohomological-dimension bound, which [Stacks, Tag 071L] and [Stacks, Tag 08D4] supply
directly for `Γ(X, -)`.

## Main results

* `AlgebraicGeometry.exists_isZero_hgroup_top`: on a quasi-compact and quasi-separated scheme the
  cohomology of every quasi-coherent module vanishes from one degree on, uniformly in the module.
* `AlgebraicGeometry.isLE_rightDerivedSections_obj_of_isQuasicoherent`: the resulting bound on
  the cohomological dimension of derived global sections.
* `AlgebraicGeometry.isIso_to_derivedGlobalSections_of_termwise_acyclic`: the canonical
  comparison from termwise global sections to any right derived global-sections functor is
  invertible at a complex of quasi-coherent modules with right-acyclic terms.

## Implementation notes

Global sections are `Stacks.Cohomology.sectionsFunctor X ⊤`, Mathlib's
`AlgebraicGeometry.SheafOfModules.evaluation` at the top open read with source the scheme-level
spelling `X.Modules` of the module category; the two spellings of that category are
definitionally equal but instance search does not cross them, so every declaration here stays
inside the scheme-level one.

[Stacks, Tag 08D4] is available for functors valued in abelian groups, so the bound is obtained
there and transported along the forgetful functor, which is exact and reflects zero objects. The
transport uses that a total right derived functor postcomposed with an exact functor derives the
composite, and that forgetting the module structure on global sections is the abelian-group-valued
sections functor on the nose.

## References

* [Stacks Project, Tag 0G9P](https://stacks.math.columbia.edu/tag/0G9P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology (sectionsFunctor)
open Stacks.Cohomology.SiteCohomologyPresheaf (totalRightDerivedMapDerivedCategoryIso)
open StacksDraft.PseudoCoherence (mapDerivedCategoryCompHomologyFunctorIso)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-! ### Abelian-group-valued global sections -/

/-- Global sections of an `𝒪_X`-module as an abelian group, read with source the scheme-level
spelling `X.Modules` of the category of `𝒪_X`-modules, which is the spelling
[Stacks, Tag 08D4] is stated for. -/
abbrev globalSectionsGroup (X : Scheme.{u}) : X.Modules ⥤ AddCommGrpCat.{u} :=
  secF.{u, u, u} X.ringCatSheaf (⊤ : X.Opens)

/-- Abelian-group-valued global sections is an additive functor. -/
instance globalSectionsGroup_additive (X : Scheme.{u}) : (globalSectionsGroup X).Additive :=
  ⟨rfl⟩

/-- Global sections commute with countable products, being evaluation of a sheaf of modules
followed by the forgetful functor to abelian groups. -/
instance globalSectionsGroup_preservesCountableProducts (X : Scheme.{u}) :
    PreservesLimitsOfShape (Discrete ℕ) (globalSectionsGroup X) :=
  inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ)
    (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens)) ⋙
      forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) AddCommGrpCat.{u}))

/-- Forgetting the module structure on global sections is abelian-group-valued global
sections. -/
theorem sectionsFunctor_top_comp_forget₂ (X : Scheme.{u}) :
    sectionsFunctor X ⊤ ⋙ forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} =
      globalSectionsGroup X :=
  rfl

/-- Forgetting the module structure reflects zero objects. -/
theorem isZero_of_isZero_forget₂ {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (h : IsZero ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M)) : IsZero M :=
  ModuleCat.isZero_iff_subsingleton.mpr (AddCommGrpCat.subsingleton_of_isZero h)

/-! ### A uniform vanishing degree for the cohomology of a quasi-compact quasi-separated scheme -/

/-- **A uniform vanishing degree for cohomology on a quasi-compact quasi-separated scheme.**
There is an `N` such that `H^p(X, F) = 0` for every quasi-coherent `𝒪_X`-module `F` and every
`p ≥ N`.

This is [Stacks, Tag 071L] for a finite affine open covering of `X`: such a covering exists
because `X` is quasi-compact, the intersection of two affine opens inside an affine open is
affine, and the degree is the covering's own bound. -/
theorem exists_isZero_hgroup_top (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ N : ℕ, ∀ (F : X.Modules), F.IsQuasicoherent → ∀ p : ℕ, N ≤ p →
      IsZero (Hgroup X.ringCatSheaf (⊤ : X.Opens) p F) := by
  obtain ⟨n, U, hUaff, hUcov⟩ := exists_finite_affineOpen_cover (⊤ : X.Opens)
    (by simpa using isCompact_univ (X := (X : Type u)))
  refine ⟨X.coverDegreeBound U, fun F hF p hp => ?_⟩
  have : F.IsQuasicoherent := hF
  refine isZero_cohomology_of_coverDegreeBound_le F U hUcov (fun i => (hUaff i).isCompact)
    (fun i A B hA hB hAaff hBaff => ?_) p hp
  have : IsAffine (U i).toScheme := hUaff i
  exact isAffineOpen_inf_of_le (U i) hAaff hBaff hA hB

/-- **A uniform vanishing degree for the global-sections functor.** The reading of
`AlgebraicGeometry.exists_isZero_hgroup_top` for the right derived functors of the
abelian-group-valued global-sections functor itself, in the `ℤ`-graded indexing. -/
theorem exists_isZero_rightDerivedPlus_globalSectionsGroup (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ N : ℕ, ∀ M : X.Modules, M.IsQuasicoherent → ∀ p : ℤ, (N : ℤ) ≤ p →
      IsZero (((globalSectionsGroup X).rightDerivedPlus p).obj M) := by
  obtain ⟨N, hN⟩ := exists_isZero_hgroup_top X
  refine ⟨N, fun M hM p hp => ?_⟩
  have : M.IsQuasicoherent := hM
  obtain ⟨k, hk⟩ : ∃ k : ℕ, p = (k : ℤ) :=
    ⟨p.toNat, (Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg N) hp)).symm⟩
  exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
    (globalSectionsGroup X) hk M).2 (hN M hM k (by omega))

/-! ### The cohomological dimension of derived global sections -/

/-- **An upper bound on derived global sections.** For `X` quasi-compact and quasi-separated
there is an `N`, depending only on `X`, such that `RΓ(X, -)` carries an object of `D(𝒪_X)` with
quasi-coherent cohomology lying in `D^{≤d}` into `D^{≤d+N-1}`.

The bound for abelian-group-valued global sections is [Stacks, Tag 08D4] applied to the uniform
vanishing degree of
`AlgebraicGeometry.exists_isZero_rightDerivedPlus_globalSectionsGroup`; forgetting the module
structure is exact, so it carries the chosen derived global sections to the chosen
abelian-group-valued one, and it reflects zero objects. -/
theorem isLE_rightDerivedSections_obj_of_isQuasicoherent (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (RΓ : DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(X, ⊤)))
    (α : (sectionsFunctor X ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RΓ)
    [RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))] :
    ∃ N : ℤ, ∀ (E : DerivedCategory X.Modules) (d : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) →
      E.IsLE d → (RΓ.obj E).IsLE (d + N - 1) := by
  obtain ⟨N, hN⟩ := exists_isZero_rightDerivedPlus_globalSectionsGroup X
  refine ⟨(N : ℤ), fun E d hcoh hE => ?_⟩
  let T := forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}
  let W := HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)
  let RG := ((sectionsFunctor X ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh W
  let αG := ((sectionsFunctor X ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh W
  let RGrp := ((globalSectionsGroup X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh W
  let αGrp := ((globalSectionsGroup X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh W
  have hbound : (RGrp.obj E).IsLE (d + (N : ℤ) - 1) :=
    isLE_rightDerivedFunctor_obj_addCommGrpCat X (globalSectionsGroup X) RGrp αGrp N hN E hcoh
      d hE
  let e : RΓ ≅ RG := Functor.rightDerivedUnique RΓ RG α αG W
  let eT : RG ⋙ T.mapDerivedCategory ≅ RGrp :=
    totalRightDerivedMapDerivedCategoryIso (sectionsFunctor X ⊤) T
  rw [DerivedCategory.isLE_iff]
  intro m hm
  have hz : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj (RGrp.obj E)) :=
    DerivedCategory.isZero_of_isLE _ (d + (N : ℤ) - 1) m (by omega)
  have hz' : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
      (T.mapDerivedCategory.obj (RΓ.obj E))) :=
    hz.of_iso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).mapIso
      (T.mapDerivedCategory.mapIso (e.app E) ≪≫ eT.app E))
  exact isZero_of_isZero_forget₂ _
    (hz'.of_iso ((mapDerivedCategoryCompHomologyFunctorIso T m).app (RΓ.obj E)).symm)

/-- Let `X` be a quasi-separated and quasi-compact scheme and let `K` be a complex of
quasi-coherent `𝒪_X`-modules each of which is right acyclic for `Γ(X, -)`. Then `Γ(X, K)`
represents `RΓ(X, K)` in `D(Γ(X, 𝒪_X))`: the canonical comparison from termwise global sections
to any right derived global-sections functor is an isomorphism at `K`. -/
@[stacks 0G9P]
theorem isIso_to_derivedGlobalSections_of_termwise_acyclic (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (K : CochainComplex X.Modules ℤ)
    (hqc : ∀ n, (K.X n).IsQuasicoherent)
    (hacyclic : ∀ n, (sectionsFunctor X ⊤).rightAcyclic (K.X n))
    (RΓ : DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(X, ⊤)))
    (α : (sectionsFunctor X ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RΓ)
    [RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))] :
    IsIso (α.app ((HomotopyCategory.quotient _ _).obj K)) := by
  let G := sectionsFunctor X ⊤
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤))
  let : RΓ.CommShift ℤ := Functor.IsRightDerivedFunctor.commShift RΓ α
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) ℤ
  have : RΓ.IsTriangulated :=
    Stacks.DerivedAcyclic.isTriangulated_of_isRightDerivedFunctor G RΓ α
  obtain ⟨N, hUpper⟩ := isLE_rightDerivedSections_obj_of_isQuasicoherent X RΓ α
  rw [DerivedCategory.isIso_iff]
  intro q
  obtain ⟨a, ha₁, ha₂⟩ : ∃ a : ℤ, a < q ∧ a + N ≤ q :=
    ⟨min (q - 1) (q - N), by omega, by omega⟩
  let g : _ ⟶ K := K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a)
  let v := (HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).map g
  have hleft : IsIso ((H q).map
      ((G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map v)) :=
    Stacks.DerivedAcyclic.isIso_homologyFunctor_map_termwise_stupidTrunc G K a q ha₁
  have hright : IsIso ((H q).map (RΓ.map (DerivedCategory.Qh.map v))) :=
    isIso_homologyFunctor_map_rightDerived_stupidTrunc RΓ N hUpper K hqc a q ha₂
  have htail : IsIso (α.app ((HomotopyCategory.quotient _ _).obj
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)))) :=
    Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic G RΓ α _
      (Stacks.DerivedAcyclic.plus_stupidTruncGE K a)
      (Stacks.DerivedAcyclic.rightAcyclic_stupidTruncGE G K hacyclic a)
  have hcomp : IsIso
      ((H q).map ((G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map v) ≫
        (H q).map (α.app ((HomotopyCategory.quotient _ _).obj K))) := by
    rw [← Functor.map_comp, α.naturality v, Functor.map_comp]
    show IsIso ((H q).map (α.app ((HomotopyCategory.quotient _ _).obj
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)))) ≫
      (H q).map (RΓ.map (DerivedCategory.Qh.map v)))
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((H q).map ((G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map v))
    ((H q).map (α.app ((HomotopyCategory.quotient _ _).obj K)))

end AlgebraicGeometry

end
