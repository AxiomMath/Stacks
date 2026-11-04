module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Surjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Triangle
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSheafQuasicoherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The differentials of a smooth morphism are finite locally free

For a smooth morphism of schemes `f : X ⟶ S` the sheaf of relative differentials `Ω_{X/S}` is
finite locally free: every point of `X` has an open neighbourhood on which `Ω_{X/S}` is
isomorphic to a free sheaf of modules on a finite index type.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFree_relativeDifferentials`: the sheaf of
  relative differentials of a smooth morphism is finite locally free.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1)
* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- If `f` maps the affine open `U` into the affine open `V` and the induced map
`Γ(S, V) → Γ(X, U)` is standard smooth, then the restriction of the sheaf of relative differentials
of `f` to `U` is isomorphic to a free sheaf of modules on a finite index type. -/
private theorem exists_restrict_iso_free_of_isStandardSmooth (f : X ⟶ S) {U : X.Opens}
    (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V)
    (hstd : (f.appLE V U hUV).hom.IsStandardSmooth) :
    ∃ ρ : Type u, Finite ρ ∧
      Nonempty ((Scheme.Hom.relativeDifferentials f).restrict U.ι ≅
        SheafOfModules.free.{u} ρ) := by
  classical
  have hqc : (Scheme.Hom.relativeDifferentials f).IsQuasicoherent :=
    Scheme.Hom.isQuasicoherent_relativeDifferentials f
  have hUaff : IsAffine (U : Scheme.{u}) := hU
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have hsm : Algebra.IsStandardSmooth Γ(S, V) Γ(X, U) := hstd
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hsm.out
  let ρ : Type u := ULift.{u} ((Set.range P.map)ᶜ : Set ι)
  let b : Module.Basis ρ Γ(X, U) Ω[Γ(X, U)⁄Γ(S, V)] :=
    P.basisKaehler.reindex Equiv.ulift.symm
  refine ⟨ρ, inferInstance, ?_⟩
  let eAff := (Stacks.AlgebraicGeometry.AffineDifferentialsIso.existsUnique_affineDifferentialsIso
    f hU hUV hV).choose
  let eSections : ModuleCat.of Γ(X, U) Γ(Scheme.Hom.relativeDifferentials f, U) ≅
      ModuleCat.of Γ(X, U) (ρ →₀ Γ(X, U)) := eAff ≪≫ b.repr.toModuleIso
  let eFree : (Scheme.Hom.relativeDifferentials f).restrict hU.fromSpec ≅
      SheafOfModules.free (R := (Spec Γ(X, U)).ringCatSheaf) ρ :=
    (Stacks.Modules.tildeIsoRestrictFromSpec (Scheme.Hom.relativeDifferentials f) hU).symm ≪≫
      (tilde.functor Γ(X, U)).mapIso eSections ≪≫ tildeFinsupp ρ
  have hcomp : hU.isoSpec.hom ≫ hU.fromSpec = U.ι := by
    rw [← hU.isoSpec_inv_ι, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hopen : IsOpenImmersion hU.isoSpec.hom := IsOpenImmersion.of_isIso _
  exact ⟨(Scheme.Modules.restrictFunctorCongr hcomp).symm.app _ ≪≫
    (Scheme.Modules.restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app _ ≪≫
    (Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapIso eFree ≪≫
    (Stacks.Modules.freeRestrictIso hU.isoSpec.hom ρ).symm⟩

/-- The sheaf of relative differentials of a smooth morphism of
schemes is finite locally free. -/
@[stacks 02G1 "differentials_finite_locally_free",
  ega "IV 17.15.15" "necessity: Ω loc free",
  ega "IV 17.10.2" "locally free",
  sga "1 II 4.3" "(ii) local freeness",
  ega "IV 17.15.5" "a) => c) (free)",
  sga "3 XI 1.9" "finite locally free"]
theorem Scheme.Hom.isFiniteLocallyFree_relativeDifferentials (f : X ⟶ S) [Smooth f] :
    SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf)
      (Scheme.Hom.relativeDifferentials f) := by
  refine (Stacks.Modules.isFiniteLocallyFree_iff_localGenerators _).mp fun x => ?_
  obtain ⟨V, hV, U, hU, hxU, hUV, hstd⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨ρ, hρ, hiso⟩ := exists_restrict_iso_free_of_isStandardSmooth f hU hV hUV hstd
  exact ⟨U, hxU, ρ, hρ, hiso⟩

end AlgebraicGeometry

end
