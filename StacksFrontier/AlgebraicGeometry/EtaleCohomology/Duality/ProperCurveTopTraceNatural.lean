module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopLowerShriekTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ElementaryFibrationLowerShriek
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The top-degree trace of a smooth projective curve: `R² f̄_*(f̄⁻¹ G) ≅ G`, naturally

Let `k` be a field, `N ≥ 1` invertible in `k` with a primitive `N`-th root of unity in `k`, and
`f̄ : X̄ ⟶ S` a proper morphism over `k`, smooth of relative dimension one with geometrically
irreducible fibres. Then

`R² f̄_*(f̄⁻¹ G) ≅ G`,

naturally in the sheaf `G` of `ℤ/N`-modules on `S_étale`
(`Stacks.EtaleCohomology.properCurveTopTraceOfRootOfUnity`). It is the top-degree trace of the
Kummer class of the diagonal of `X̄ ×_S X̄`, descended along `f̄`
(`Stacks.EtaleCohomology.TopTrace.topSheafIso`), read on sheaves of `ℤ/N`-modules through the fully
faithful forgetful functor to abelian sheaves. Over an algebraically closed field such a root of
unity exists (`Stacks.EtaleCohomology.nonempty_properCurveTopTrace`).

In particular `R² f̄_*` of an inverse image is an exact functor of the sheaf on `S`, which is what
the top-degree projection of `Rf̄_*` needs to be natural in the coefficients, in the proof of
relative Poincaré duality for `f̄` ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

The derived categories are those of the standard model `HasDerivedCategory.standard`, in which
`Rf̄_*` (`Stacks.EtaleCohomology.etaleModuleDerivedDirectImage`) is read by its consumers.

## Main definitions

* `Stacks.EtaleCohomology.properCurveTopTraceOfRootOfUnity`.
* `Stacks.EtaleCohomology.properCurveTopTrace`.

## Main results

* `Stacks.EtaleCohomology.nonempty_properCurveTopTrace`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] (N : ℕ) [NeZero N] (hN : IsUnit (N : k)) {S Xbar : Scheme.{u}}
  (q : S ⟶ Spec (.of k)) (fbar : Xbar ⟶ S) [IsProper fbar] [SmoothOfRelativeDimension 1 fbar]
  [GeometricallyIrreducible fbar]

include hN in
/-- **The top-degree trace of a smooth projective curve**, from a primitive `N`-th root of unity
of `k`: `R² f̄_*(f̄⁻¹ G) ≅ G`, naturally in the sheaf `G` of `ℤ/N`-modules on `S`. -/
@[sga "4½ Dualite 2.5" "more general"]
def properCurveTopTraceOfRootOfUnity {ζ : k} (hζ : IsPrimitiveRoot ζ N) :
    etaleModuleInverseImage.{u, 0} (ZMod N) fbar ⋙
        singleHomology (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar) 2 ≅
      𝟭 (EtaleModules.{u, 0} (ZMod N) S) :=
  letI := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse
  have hX : IsUnit ((N : ℕ) : Γ(Xbar, ⊤)) := isUnit_natCast_sections k (fbar ≫ q) hN
  have hY : IsUnit ((N : ℕ) : Γ(pullback fbar fbar, ⊤)) :=
    isUnit_natCast_sections k (pullback.fst fbar fbar ≫ fbar ≫ q) hN
  ((Stacks.ArtinSchreier.etaleModuleForgetZModFullyFaithful S N).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      TopTrace.moduleTopSheafIso fbar ≪≫
      (TopTrace.topSheafIso fbar hX hY (pullback.fst fbar fbar ≫ fbar ≫ q) hζ).symm ≪≫
      (Functor.leftUnitor _).symm)

include hN q in
/-- **`R² f̄_*(f̄⁻¹ G) ≅ G` for a smooth projective curve over an algebraically closed field**,
naturally in the sheaf `G` of `ℤ/N`-modules on `S`, `N` invertible in `k`. -/
theorem nonempty_properCurveTopTrace [IsAlgClosed k] :
    Nonempty (etaleModuleInverseImage.{u, 0} (ZMod N) fbar ⋙
        singleHomology (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar) 2 ≅
      𝟭 (EtaleModules.{u, 0} (ZMod N) S)) := by
  have : NeZero (N : k) := ⟨hN.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k N
  exact ⟨properCurveTopTraceOfRootOfUnity N hN q fbar hζ⟩

include hN q in
/-- **The top-degree trace of a smooth projective curve** `f̄ : X̄ ⟶ S` over an algebraically
closed field `k`, `N` invertible in `k`: `R² f̄_*(f̄⁻¹ G) ≅ G`, naturally in the sheaf `G` of
`ℤ/N`-modules on `S`, read as `H²(Rf̄_*(f̄⁻¹ G[0]))`. -/
def properCurveTopTrace [IsAlgClosed k] :
    etaleModuleInverseImage.{u, 0} (ZMod N) fbar ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
        etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙
          DerivedCategory.Plus.homologyFunctor _ 2 ≅
      𝟭 (EtaleModules.{u, 0} (ZMod N) S) :=
  Functor.isoWhiskerLeft (etaleModuleInverseImage.{u, 0} (ZMod N) fbar)
      (singleHomologyPlusSingleIso (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar) 2).symm ≪≫
    (nonempty_properCurveTopTrace N hN q fbar).some

end Stacks.EtaleCohomology

end
