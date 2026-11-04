module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Module
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf

/-!
# Sections of a finite locally free sheaf on an affine open

The sections of a quasi-coherent, finite locally free sheaf of modules over an affine open `U`
form a finite projective module over `Γ(X, U)`, and if the sheaf has constant rank `d` then that
module has rank `d` at every prime of `Γ(X, U)`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_sheaf`: a sheaf of modules
  finite locally free of rank `d` in the sense of Stacks Tag 01C6 (3) is pointwise finite
  locally free of rank `d`.
* `AlgebraicGeometry.moduleSpecΓ_finite_and_projective_of_isFiniteLocallyFree`: the global
  sections of a quasi-coherent, pointwise finite locally free sheaf on `Spec R` are finite and
  projective.
* `AlgebraicGeometry.SheafOfModules.module_finite_and_projective_sections`: the sections over an
  affine open of a quasi-coherent finite locally free sheaf are finite and projective.
* `AlgebraicGeometry.SheafOfModules.rankAtStalk_sections`: those sections have rank `d`
  everywhere when the sheaf has constant rank `d`.

## Implementation notes

The two transport lemmas for the constant-rank condition,
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso` and
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank.restrict`, are used below and
proved in `StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf`, which states the rank
as an implicit argument. `Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank` and
`Module.finite_and_projective_of_isFiniteLocallyFree`, the two module-level inputs, come from
`StacksFrontier.RingTheory.Norm.Projective`.

The bridge from the local-generators form of Stacks Tag 01C6 (3) to the pointwise form is the
constant-rank analogue of the `mpr` direction of
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff`, and uses the same flag-free
identification of a free sheaf under `AlgebraicGeometry.Scheme.Modules.overEquiv`: the
preservation of discrete colimits is supplied by
`CategoryTheory.Limits.preservesColimitsOfShape_of_discrete` and the unit comparison is
`Iso.refl`.

The passage from the sheaf to a module is through `AlgebraicGeometry.IsAffineOpen.fromSpec`, so
the ring of scalars is literally `Γ(X, U)` and no transport along a ring isomorphism is needed;
the sections themselves are identified by `AlgebraicGeometry.affineSectionsLinearEquiv`.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 00NW](https://stacks.math.columbia.edu/tag/00NW)
* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A sheaf of modules on a scheme that is finite locally free of rank `d` in the
local-generators sense of Stacks Tag 01C6 (3) is pointwise finite locally free of rank `d`. -/
theorem isFiniteLocallyFreeOfRank_of_sheaf {X : Scheme.{u}} (M : X.Modules) (d : ℕ)
    [h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M d] :
    IsFiniteLocallyFreeOfRank M d := by
  obtain ⟨q, hfree, hrank⟩ := h.exists_isFiniteLocallyFreeOfRankData
  intro x
  obtain ⟨i, hi⟩ := ((_root_.Opens.coversTop_iff X q.X).mp q.coversTop).exists_mem x
  let U : X.Opens := q.X i
  let I := (q.generators i).I
  refine ⟨U, hi, ⟨?_⟩⟩
  have hdisc : PreservesColimitsOfShape (Discrete I) (overEquiv (X := X) U).functor :=
    preservesColimitsOfShape_of_discrete _
  have hunit : SheafOfModules.unit (U.toScheme).ringCatSheaf ≅
      (overEquiv (X := X) U).functor.obj
        (SheafOfModules.unit (X.ringCatSheaf.over U)) := Iso.refl _
  have hπ : IsIso (q.generators i).π := hfree.isIso i
  let eFree := @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _
    (overEquiv (X := X) U).functor I hdisc hunit
  let eM := ((overEquiv (X := X) U).functor.mapIso (@asIso _ _ _ _ _ hπ)) ≪≫
    (overFunctorEquiv (X := X) U).app M |>.symm
  exact eM ≪≫ eFree.symm ≪≫
    (SheafOfModules.freeFunctor (R := (U.toScheme).ringCatSheaf)).mapIso
      ((hrank i).some.trans Equiv.ulift.symm).toIso

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The global sections of a quasi-coherent sheaf of modules on `Spec R` that is pointwise finite
locally free form a finite projective `R`-module. -/
theorem moduleSpecΓ_finite_and_projective_of_isFiniteLocallyFree
    {R : Type u} [CommRing R] (F : (Spec (CommRingCat.of R)).Modules)
    [F.IsQuasicoherent] (hF : Scheme.Modules.IsFiniteLocallyFree F) :
    Module.Finite R (AlgebraicGeometry.moduleSpecΓFunctor.obj F) ∧
      Module.Projective R (AlgebraicGeometry.moduleSpecΓFunctor.obj F) := by
  let M := AlgebraicGeometry.moduleSpecΓFunctor.obj F
  have hfrom : IsIso (F.fromTildeΓ) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := CommRingCat.of R) F
  let e : AlgebraicGeometry.tilde (R := CommRingCat.of R)
      (ModuleCat.of R (AlgebraicGeometry.moduleSpecΓFunctor.obj F)) ≅ F :=
    @asIso _ _ _ _ F.fromTildeΓ hfrom
  have htilde : (AlgebraicGeometry.tilde (R := CommRingCat.of R)
      (ModuleCat.of R (AlgebraicGeometry.moduleSpecΓFunctor.obj F))).IsFiniteLocallyFree := by
    intro x
    obtain ⟨U, hx, I, hI, ⟨eU⟩⟩ := hF x
    exact ⟨U, hx, I, hI, ⟨(Scheme.Modules.restrictFunctor (Scheme.Opens.ι U)).mapIso e ≪≫ eU⟩⟩
  exact Module.finite_and_projective_of_isFiniteLocallyFree
    ((tilde_isFiniteLocallyFree_iff R M).mp htilde)

end AlgebraicGeometry

namespace AlgebraicGeometry.SheafOfModules

/-- The sections over an affine open of a quasi-coherent finite locally free sheaf of modules
form a finite projective module over the ring of functions on that open. -/
theorem module_finite_and_projective_sections {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] [IsFiniteLocallyFree.{u, u, u} F] (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(F, U.1) ∧ Module.Projective Γ(X, U.1) Γ(F, U.1) := by
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let G := F.restrict U.2.fromSpec
  have hG : Scheme.Modules.IsFiniteLocallyFree G :=
    Scheme.Modules.IsFiniteLocallyFree.restrict U.2.fromSpec
      ((Scheme.Modules.isFiniteLocallyFree_iff F).mpr inferInstance)
  obtain ⟨h₁, h₂⟩ := moduleSpecΓ_finite_and_projective_of_isFiniteLocallyFree G hG
  have : Module.Finite Γ(X, U.1) Γ(G, ⊤) := h₁
  have : Module.Projective Γ(X, U.1) Γ(G, ⊤) := h₂
  have e := affineSectionsLinearEquiv F U.2
  exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩

/-- The sections over an affine open of a quasi-coherent sheaf of modules that is finite locally
free of rank `d` form a module of rank `d` at every prime. -/
theorem rankAtStalk_sections {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (d : ℕ) [IsFiniteLocallyFreeOfRank.{u, u, u} F d]
    (U : X.affineOpens) :
    ∀ p : PrimeSpectrum Γ(X, U.1), Module.rankAtStalk Γ(F, U.1) p = d := by
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let G := F.restrict U.2.fromSpec
  have hG : Scheme.Modules.IsFiniteLocallyFreeOfRank G d :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.restrict U.2.fromSpec
      (Scheme.Modules.isFiniteLocallyFreeOfRank_of_sheaf F d)
  have hfrom : IsIso G.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := CommRingCat.of Γ(X, U.1)) G
  have hM : Module.IsFiniteLocallyFreeOfRank Γ(X, U.1) (moduleSpecΓFunctor.obj G) d :=
    (tilde_isFiniteLocallyFreeOfRank_iff _ _ d).mp
      (Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso (@asIso _ _ _ _ _ hfrom).symm hG)
  exact fun p ↦
    (congrFun (Module.rankAtStalk_eq_of_equiv (affineSectionsLinearEquiv F U.2)) p).symm.trans
      (Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank d hM p)

end AlgebraicGeometry.SheafOfModules

end
