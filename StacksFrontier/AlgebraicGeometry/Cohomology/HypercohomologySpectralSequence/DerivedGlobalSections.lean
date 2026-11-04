module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.AlgebraicGeometry.Cohomology.UniformVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.DerivedBounds
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.DerivedUpperBound
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredComplexSpectralSequence.HypercohomologySpectralSequence

/-!
# Derived global sections of a scheme in abelian groups, and its range of degrees

Let `X` be a scheme. Global sections of `𝒪_X`-modules, composed with the forgetful functor to
abelian groups, is an additive functor `Γ(X, -) : Mod(𝒪_X) ⥤ Ab` commuting with countable
products. On a quasi-compact quasi-separated `X` its higher derived functors vanish beyond a
degree depending only on `X`, and that single bound controls the whole range of degrees in which
derived global sections of an object of `D(𝒪_X)` with quasi-coherent cohomology can live.

A derived global-sections functor `RΓ` on `D(𝒪_X)` valued in `Γ(X, 𝒪_X)`-modules — the one
carried by the canonical truncation spectral sequence of a complex of module sheaves — becomes a
derived functor of `Γ(X, -) : Mod(𝒪_X) ⥤ Ab` after composing with the forgetful functor, and the
bounds of [Stacks, Tag 08D4] then apply to it. Because the forgetful functor is faithful and
exact, vanishing read in abelian groups is vanishing of the hypercohomology module itself.

## Main definitions

* `AlgebraicGeometry.groupSections`: global sections of `𝒪_X`-modules, valued in abelian groups.
* `AlgebraicGeometry.groupDerivedSections`: a derived global-sections functor read in abelian
  groups, and `AlgebraicGeometry.groupDerivedSectionsUnit` its comparison from underived sections.

## Main results

* `AlgebraicGeometry.exists_isZero_rightDerivedPlus_groupSections`: **on a quasi-compact
  quasi-separated scheme the cohomology of quasi-coherent modules vanishes beyond a degree
  depending only on the scheme.**
* `AlgebraicGeometry.groupDerivedSections_isRightDerivedFunctor`: the composite really is the
  right derived functor of global sections in abelian groups.
* `AlgebraicGeometry.isGE_groupDerivedSections_obj`,
  `AlgebraicGeometry.isLE_groupDerivedSections_obj` and
  `AlgebraicGeometry.isIso_homology_groupDerivedSections_map_truncLEι`: [Stacks, Tag 08D4] for
  that functor.
* `AlgebraicGeometry.isZero_hypercohomology_of_isGE` and
  `AlgebraicGeometry.isZero_hypercohomology_of_isLE`: the resulting range of degrees of the
  hypercohomology modules themselves.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` wrapping `SheafOfModules`, carrying its own
category, preadditivity and abelianness instances. Those instances are definitionally the ones
`SheafOfModules` carries, but instance search does not cross between the two spellings. The
constructions below are phrased with the `SheafOfModules` spelling, which is the one the
canonical truncation spectral sequence uses, while [Stacks, Tag 08D4] is stated with the
scheme-theoretic one; the three transfer lemmas therefore apply it with its instance arguments
supplied explicitly.

## References

* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
* [Stacks Project, Tag 0BKK](https://stacks.math.columbia.edu/tag/0BKK)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.FilteredComplex

universe u

-- `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, reached through the import of
-- [Stacks, Tag 08D4], supplies a second `HasDerivedCategory` instance for module sheaves, with a
-- smaller hom universe. The derived global-sections functor of the canonical truncation spectral
-- sequence is built with the standard one, so the standard one is given priority here; without
-- that the two readings of `DerivedCategory (SheafOfModules 𝒪_X)` differ by a universe.
attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance]
  Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.evaluation_additive

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- The forgetful functor from modules over the ring of global functions of a scheme to abelian
groups. -/
abbrev sectionsToGroup :
    ModuleCat.{u} ((structureSheafRing X.toRingedSpace).obj.obj (op (⊤ : Opens X.carrier))) ⥤
      AddCommGrpCat.{u} :=
  forget₂ (ModuleCat.{u} ((structureSheafRing X.toRingedSpace).obj.obj (op (⊤ : Opens X.carrier))))
    AddCommGrpCat.{u}

/-- Global sections of `𝒪_X`-modules on a scheme, valued in abelian groups. -/
abbrev groupSections :
    SheafOfModules.{u} (structureSheafRing X.toRingedSpace) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.evaluation (structureSheafRing X.toRingedSpace) (op (⊤ : Opens X.carrier)) ⋙
    sectionsToGroup X

/-- An abelian group is zero as soon as it is zero after forgetting the module structure: the
forgetful functor is faithful and preserves the zero morphism. -/
theorem isZero_of_isZero_sectionsToGroup_obj
    {M : ModuleCat.{u} ((structureSheafRing X.toRingedSpace).obj.obj (op (⊤ : Opens X.carrier)))}
    (h : IsZero ((sectionsToGroup X).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply (sectionsToGroup X).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (IsZero.iff_id_eq_zero _).mp h

/-- **Uniform vanishing of the cohomology of quasi-coherent modules on a quasi-compact
quasi-separated scheme.** There is an `N`, depending only on `X`, with `H^p(X, F) = 0` for every
quasi-coherent `𝒪_X`-module `F` and every `p ≥ N`. -/
theorem exists_isZero_rightDerivedPlus_groupSections [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ N : ℕ, ∀ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)), M.IsQuasicoherent →
      ∀ p : ℤ, (N : ℤ) ≤ p → IsZero (((groupSections X).rightDerivedPlus p).obj M) := by
  obtain ⟨n, U, hUaff, hUcov⟩ :=
    exists_finite_affineOpen_cover (⊤ : X.Opens) (by simpa using isCompact_univ (X := X))
  refine ⟨X.coverDegreeBound U, fun M hM p hp => ?_⟩
  have hp0 : (0 : ℤ) ≤ p := le_trans (Int.natCast_nonneg _) hp
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ℤ) = p := ⟨p.toNat, Int.toNat_of_nonneg hp0⟩
  have hk : X.coverDegreeBound U ≤ k := by exact_mod_cast hp
  have hsep : ∀ i, (U i).toScheme.IsSeparated := fun i => by
    have : IsAffine (U i).toScheme := hUaff i
    infer_instance
  exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff (groupSections X)
    (rfl : (k : ℤ) = (k : ℕ)) M).2
      (@isZero_cohomology_of_coverDegreeBound_le_of_isSeparated X ‹_› ‹_› M hM n U hUcov
        (fun i => (hUaff i).isCompact) hsep k hk)

variable (L : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ)
  (T : CanonicalTruncationSpectralSequence X.toRingedSpace L)

/-- A derived global-sections functor on `D(𝒪_X)`, read in abelian groups. -/
abbrev groupDerivedSections :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  T.RΓ ⋙ (sectionsToGroup X).mapDerivedCategory

/-- The comparison from the complex of global sections, read in abelian groups, to derived
global sections: the comparison `T.α` of the spectral sequence datum, pushed through the
forgetful functor. -/
def groupDerivedSectionsUnit :
    (groupSections X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ groupDerivedSections X L T :=
  (Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso
          (F := SheafOfModules.evaluation (structureSheafRing X.toRingedSpace)
            (op (⊤ : Opens X.carrier)))
          (G := sectionsToGroup X) (H := groupSections X) (Iso.refl _)
          (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        ((SheafOfModules.evaluation (structureSheafRing X.toRingedSpace)
          (op (⊤ : Opens X.carrier))).mapHomotopyCategory (ComplexShape.up ℤ))
        (sectionsToGroup X).mapDerivedCategoryFactorsh.symm ≪≫
      (Functor.associator _ _ _).symm).hom ≫
    Functor.whiskerRight T.α (sectionsToGroup X).mapDerivedCategory ≫
    (Functor.associator _ _ _).hom

open Stacks.Injectives.KInjectiveResolution
  Stacks.Cohomology.HypercohomologyEdge.HomologyComparison in
/-- Derived global sections in abelian groups is the right derived functor of global sections in
abelian groups. -/
theorem groupDerivedSections_isRightDerivedFunctor :
    (groupDerivedSections X L T).IsRightDerivedFunctor (groupDerivedSectionsUnit X L T)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)) := by
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
    inferInstance
  refine isRightDerivedFunctor_of_isIso_app_quotient_isKInjective
    (exists_quasiIso_isKInjective_sheafOfModules (structureSheafRing X.toRingedSpace)) _ _ _
    (fun I hI => ?_)
  have := T.isRightDerived
  have := isIso_unit_app_of_isKInjective X.toRingedSpace T.RΓ T.α I hI
  dsimp only [groupDerivedSectionsUnit]
  simp only [NatTrans.comp_app, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  infer_instance

/-- **Stacks 08D4, part (3), the lower bound**, for derived global sections in abelian groups: an
object of `D(𝒪_X)` with quasi-coherent cohomology lying in degrees `≥ a` has derived global
sections in degrees `≥ a`. -/
theorem isGE_groupDerivedSections_obj
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj E).IsQuasicoherent)
    (a : ℤ) (hE : E.IsGE a) : ((groupDerivedSections X L T).obj E).IsGE a :=
  @AlgebraicGeometry.isGE_rightDerivedFunctor_obj X _ _ _ (HasDerivedCategory.standard _)
    (HasDerivedCategory.standard _) (groupSections X)
    (inferInstanceAs (groupSections X).Additive) (groupDerivedSections X L T)
    (groupDerivedSectionsUnit X L T) (groupDerivedSections_isRightDerivedFunctor X L T)
    E hcoh a hE

/-- **Stacks 08D4, part (3), the upper bound**, for derived global sections in abelian groups: if
the cohomology of quasi-coherent modules vanishes from degree `N` on, an object of `D(𝒪_X)` with
quasi-coherent cohomology lying in degrees `≤ b` has derived global sections in degrees
`≤ b + N - 1`. -/
theorem isLE_groupDerivedSections_obj (N : ℕ)
    (hN : ∀ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)), M.IsQuasicoherent →
      ∀ p : ℤ, (N : ℤ) ≤ p → IsZero (((groupSections X).rightDerivedPlus p).obj M))
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj E).IsQuasicoherent)
    (b : ℤ) (hE : E.IsLE b) : ((groupDerivedSections X L T).obj E).IsLE (b + (N : ℤ) - 1) :=
  @AlgebraicGeometry.isLE_rightDerivedFunctor_obj_addCommGrpCat X (groupSections X)
    (inferInstanceAs (groupSections X).Additive)
    (inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ) (groupSections X)))
    (groupDerivedSections X L T) (groupDerivedSectionsUnit X L T)
    (groupDerivedSections_isRightDerivedFunctor X L T) N hN E hcoh b hE

/-- **Stacks 08D4, part (1)**, for derived global sections in abelian groups: in degrees at most
`a` the derived global sections of an object with quasi-coherent cohomology and of its canonical
truncation in degrees at most `a` agree. -/
theorem isIso_homology_groupDerivedSections_map_truncLEι
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj E).IsQuasicoherent)
    (a i : ℤ) (hi : i ≤ a) :
    IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
      ((groupDerivedSections X L T).map ((DerivedCategory.TStructure.t.truncLEι a).app E))) :=
  @AlgebraicGeometry.isIso_homologyFunctor_map_rightDerivedFunctor_truncLEι X _ _ _
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) (groupSections X)
    (inferInstanceAs (groupSections X).Additive) (groupDerivedSections X L T)
    (groupDerivedSectionsUnit X L T) (groupDerivedSections_isRightDerivedFunctor X L T)
    E hE a i hi

/-- The hypercohomology module in degree `n`, read in abelian groups, is the degree `n` homology
of the derived global sections in abelian groups: the forgetful functor is exact and therefore
commutes with homology on the derived category. -/
def groupHypercohomologyIso
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) (n : ℤ) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((groupDerivedSections X L T).obj E) ≅
      (sectionsToGroup X).obj
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing X.toRingedSpace).obj.obj
            (op (⊤ : Opens X.carrier)))) n).obj (T.RΓ.obj E)) :=
  (Stacks.Homology.derivedHomologyIso (sectionsToGroup X) n).app (T.RΓ.obj E)

/-- A hypercohomology module vanishes as soon as it vanishes in abelian groups. -/
theorem isZero_homology_RΓ_obj_of_isZero
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) (n : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      ((groupDerivedSections X L T).obj E))) :
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing X.toRingedSpace).obj.obj
        (op (⊤ : Opens X.carrier)))) n).obj (T.RΓ.obj E)) :=
  isZero_of_isZero_sectionsToGroup_obj X
    (h.of_iso (groupHypercohomologyIso X L T E n).symm)

/-- **Hypercohomology vanishes below the range of an object with quasi-coherent cohomology.** -/
theorem isZero_hypercohomology_of_isGE
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj E).IsQuasicoherent)
    (a n : ℤ) (hE : E.IsGE a) (hn : n < a) :
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing X.toRingedSpace).obj.obj
        (op (⊤ : Opens X.carrier)))) n).obj (T.RΓ.obj E)) := by
  have := isGE_groupDerivedSections_obj X L T E hcoh a hE
  exact isZero_homology_RΓ_obj_of_isZero X L T E n
    (((groupDerivedSections X L T).obj E).isZero_of_isGE a n hn)

/-- **Hypercohomology vanishes above the range of an object with quasi-coherent cohomology**,
the degree of vanishing being shifted by the uniform bound `N` of
`AlgebraicGeometry.exists_isZero_rightDerivedPlus_groupSections`. -/
theorem isZero_hypercohomology_of_isLE (N : ℕ)
    (hN : ∀ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)), M.IsQuasicoherent →
      ∀ p : ℤ, (N : ℤ) ≤ p → IsZero (((groupSections X).rightDerivedPlus p).obj M))
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj E).IsQuasicoherent)
    (b n : ℤ) (hE : E.IsLE b) (hn : b + (N : ℤ) - 1 < n) :
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing X.toRingedSpace).obj.obj
        (op (⊤ : Opens X.carrier)))) n).obj (T.RΓ.obj E)) := by
  have := isLE_groupDerivedSections_obj X L T N hN E hcoh b hE
  exact isZero_homology_RΓ_obj_of_isZero X L T E n
    (((groupDerivedSections X L T).obj E).isZero_of_isLE (b + (N : ℤ) - 1) n hn)

/-- **In degrees at most `a` the hypercohomology of an object with quasi-coherent cohomology and
that of its canonical truncation in degrees at most `a` agree**: [Stacks, Tag 08D4] part (1),
read back through the faithful exact forgetful functor to abelian groups. -/
theorem isIso_homology_RΓ_map_truncLEι
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj E).IsQuasicoherent)
    (a i : ℤ) (hi : i ≤ a) :
    IsIso ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing X.toRingedSpace).obj.obj
        (op (⊤ : Opens X.carrier)))) i).map
      (T.RΓ.map ((DerivedCategory.TStructure.t.truncLEι a).app E))) := by
  have hgroup := isIso_homology_groupDerivedSections_map_truncLEι X L T E hE a i hi
  have hnat := (Stacks.Homology.derivedHomologyIso (sectionsToGroup X) i).hom.naturality
    (T.RΓ.map ((DerivedCategory.TStructure.t.truncLEι a).app E))
  have hcomp : IsIso
      ((groupHypercohomologyIso X L T
          ((DerivedCategory.TStructure.t.truncLE a).obj E) i).hom ≫
        (sectionsToGroup X).map ((DerivedCategory.homologyFunctor _ i).map
          (T.RΓ.map ((DerivedCategory.TStructure.t.truncLEι a).app E)))) := by
    erw [← hnat]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hgroup _
  have : IsIso ((sectionsToGroup X).map ((DerivedCategory.homologyFunctor _ i).map
      (T.RΓ.map ((DerivedCategory.TStructure.t.truncLEι a).app E)))) :=
    IsIso.of_isIso_comp_left (groupHypercohomologyIso X L T
      ((DerivedCategory.TStructure.t.truncLE a).obj E) i).hom _
  exact isIso_of_reflects_iso _ (sectionsToGroup X)

end AlgebraicGeometry

end
