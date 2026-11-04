module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopCohomologyCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.RelativeCurveTopIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopDirectImageBoundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopDirectImageForget
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ModuleSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafForgetAbelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorSingleObject

/-!
# `R² f_! ℤ/N ≅ ℤ/N` for an elementary fibration

Let `k` be an algebraically closed field, `N ≥ 1` invertible in `k`, and `f : U ⟶ S` an
elementary fibration (`AlgebraicGeometry.IsElementaryFibration`) over a `k`-scheme `S` which is
affine and smooth over `k`: `f = f̄ ∘ j` with `f̄ : X̄ ⟶ S` smooth projective of relative dimension
one with geometrically irreducible fibres and `j` the complement of a closed `Z` finite étale
over `S`. Then for every compactification of `f`,

`R² f_! (ℤ/N) ≅ ℤ/N`

as sheaves of `ℤ/N`-modules on `S_étale`
(`Stacks.EtaleCohomology.higherDirectImageTwoOfElementaryFibration`).

The proof:

* by the independence of `Rf_!` of the compactification (Tag 0F7I) the compactification may be
  taken to be `j : U ⟶ X̄` over `f̄`, and then `R² f_! = R² f̄_* ∘ j_!`;
* the boundary is finite over `S`, so `R² f̄_*(j_! ℤ/N) ≅ R² f̄_*(ℤ/N)`
  (`Stacks.EtaleCohomology.isIso_singleHomology_map_extensionByZero_counit`);
* the underlying abelian sheaf of `R² f̄_*(ℤ/N)` is `R² f̄_* μ_N`, through a primitive `N`-th root
  of unity of `k`
  (`Stacks.EtaleCohomology.nonempty_forget_singleHomology_two_iso_relativeTopSheaf`);
* `R² f̄_* μ_N ≅ ℤ/N` by the Kummer class of the diagonal of `X̄ ×_S X̄`
  (`Stacks.EtaleCohomology.nonempty_constantSheaf_zmod_iso_relativeTopSheaf`);
* an additive isomorphism of sheaves killed by `N` is `ℤ/N`-linear.

The derived categories are those of the standard model `HasDerivedCategory.standard`, in which
`Rf_!` (`Stacks.EtaleCohomology.derivedLowerShriek`) is stated.

## Main results

* `Stacks.EtaleCohomology.higherDirectImageTwoOfElementaryFibration`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open ExtensionTorsor

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k] [IsAlgClosed k] (N : ℕ) [NeZero N]

/-- **`R² f_! ℤ/N ≅ ℤ/N` for an elementary fibration** `f : U ⟶ S` over `S` affine and smooth
over an algebraically closed field `k`, for every compactification of `f`, when `N` is invertible
in `k`. -/
theorem higherDirectImageTwoOfElementaryFibration :
    HigherDirectImageTwoOfElementaryFibration k N := by
  intro hN U S q f e _ _ hf jf
  obtain ⟨Xbar, Z, j, fbar, i, hj, hjf, hsm, hproj, hgi, hi, -, hrange, hfin, -, -⟩ :=
    hf.exists_compactification
  have := hj
  have := hsm
  have := hgi
  have := hi
  have := hfin
  have : IsProper fbar := isProper_of_isProjectiveMorphism fbar hproj
  -- the scheme-level instances
  have : Smooth q := SmoothOfRelativeDimension.smooth e q
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherian S := ⟨⟩
  have : CompactSpace Xbar := ⟨by
    simpa using QuasiCompact.isCompact_preimage (f := fbar) Set.univ isOpen_univ isCompact_univ⟩
  have : IsLocallyNoetherian Xbar := LocallyOfFiniteType.isLocallyNoetherian fbar
  have : IsNoetherian Xbar := ⟨⟩
  have : TopologicalSpace.NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
  have : IsSeparated f := by rw [← hjf]; infer_instance
  have : LocallyOfFiniteType f := by rw [← hjf]; infer_instance
  have : QuasiCompact f := inferInstance
  -- the compactification of `f` given by the elementary fibration
  let jf₀ : CompactificationOf (Over.mk f) :=
    ⟨StructuredArrow.mk (Y := Over.mk fbar) (Over.homMk (U := Over.mk f) j hjf),
      ⟨hj, inferInstanceAs (IsProper fbar)⟩⟩
  -- units and a root of unity
  have hN0 : N ≠ 0 := NeZero.ne N
  have hX : IsUnit ((N : ℕ) : Γ(Xbar, ⊤)) := isUnit_natCast_sections k (fbar ≫ q) hN
  have hY : IsUnit ((N : ℕ) : Γ(pullback fbar fbar, ⊤)) :=
    isUnit_natCast_sections k (pullback.fst fbar fbar ≫ fbar ≫ q) hN
  have : NeZero (N : k) := ⟨hN.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k N
  -- Tag 0F7I
  have hK : isTorsionPlus.{u, 0} (ZMod N) U
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := U) N)) :=
    fun _ => isTorsionEtaleModule_of_natCast_eq_zero (ZMod N) N (Nat.pos_of_ne_zero hN0)
      (ZMod.natCast_self N) _
  let e₁ := (DerivedCategory.Plus.homologyFunctor _ 2).mapIso
    ((derivedLowerShriekCompactificationIso f jf jf₀ (ZMod N)).app ⟨_, hK⟩)
  -- `Rf_! = Rf̄_* ∘ j_!` on a sheaf
  let := etaleModules_enoughInjectives.{u, 0} (ZMod N) U
  let eU : unitSheaf (X := U) N ≅
      (etaleModuleRestriction.{u, 0} (ZMod N) j).obj (unitSheaf (X := Xbar) N) :=
    ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod N) j).app
        (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)))).symm ≪≫
      (etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod N) j).app (unitSheaf (X := Xbar) N)
  let Φ := etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar
  let e₂ : (DerivedCategory.Plus.homologyFunctor _ 2).obj ((derivedLowerShriek.{u, 0} f jf₀
        (ZMod N)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := U) N))) ≅
      (singleHomology Φ 2).obj ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj
        ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj (unitSheaf (X := Xbar) N))) :=
    (DerivedCategory.Plus.homologyFunctor _ 2).mapIso (Φ.mapIso
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).rightDerivedFunctorPlusObjSingleIso
        (unitSheaf (X := U) N) ≪≫
        (DerivedCategory.Plus.singleFunctor _ 0).mapIso
          ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).mapIso eU) ≪≫
        ((StacksDraft.DerivedSectionsComparison.singlePlusQIso _).app _).symm))
  -- the boundary
  have := isIso_singleHomology_map_extensionByZero_counit (ZMod N) i j
    (by rw [hrange, compl_compl]) fbar
    (unitSheaf (X := Xbar) N) 2 le_rfl
  let e₃ := asIso ((singleHomology Φ 2).map
    ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) j).counit.app (unitSheaf (X := Xbar) N)))
  -- the abelian computation
  obtain ⟨e₄⟩ := nonempty_forget_singleHomology_two_iso_relativeTopSheaf fbar (fbar ≫ q) hζ hN0
  obtain ⟨e₅⟩ := nonempty_constantSheaf_zmod_iso_relativeTopSheaf fbar hX hY
  let e₆ := (Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} (ZMod N) S.smallEtaleTopology).app
    (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)))
  let E : (etaleModuleForgetAb.{u, 0} (ZMod N) S).obj
      ((DerivedCategory.Plus.homologyFunctor _ 2).obj ((derivedLowerShriek.{u, 0} f jf
        (ZMod N)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := U) N)))) ≅
      (etaleModuleForgetAb.{u, 0} (ZMod N) S).obj (unitSheaf (X := S) N) :=
    (etaleModuleForgetAb.{u, 0} (ZMod N) S).mapIso (e₁ ≪≫ e₂ ≪≫ e₃) ≪≫ e₄ ≪≫ e₅.symm ≪≫ e₆.symm
  exact ⟨(Stacks.ArtinSchreier.etaleModuleForgetZModFullyFaithful S N).preimageIso E⟩

end Stacks.EtaleCohomology

end
