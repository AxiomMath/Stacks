module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ExtSheafStalkComputation
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.RingTheory.Dualizing.Complexes.Uniqueness
public import StacksFrontier.RingTheory.Dualizing.DualExtBaseChangeSingle
public import StacksFrontier.RingTheory.Dualizing.ExtRegularElement

/-!
# The stalk of the Ext sheaves of a dualizing complex as a normalized Ext module

Let `X` be a locally Noetherian scheme, `F` a coherent `𝒪_X`-module, `K` a dualizing complex on
`X` and `δ = Stacks.Duality.associatedShiftFunction K` its shift function. This file identifies
the stalk at `x` of the Ext sheaf `𝓔ⁱ = 𝓔xt^{-i}_{𝒪_X}(F, K)` with the extension module

`Ext^{δ(x) - i}_{𝒪_{X,x}}(F_x, ω)`,  where  `ω = (ω^•_{X,x})⟦-δ(x)⟧`

is the normalized derived stalk of `K` at `x`. This is the stalk reading of [Stacks, Tag 0A6H]
that the four clauses of [Stacks, Tag 0ECM] consume: it is exactly the `hstalk` hypothesis of
`Stacks.Duality.isStalkwiseDualExt_extSheafOf`, so feeding this theorem to that one produces the
bundle `Stacks.Duality.IsStalkwiseDualExt` for the actual Ext sheaves.

The route is an assembly of finished pieces. Pass to an affine open `U ∋ x`, write `A = Γ(X, U)`
and `B = 𝒪_{X,x}`, and let `f : A → B` be the germ map, which presents `B` as a localization of
`A` and is therefore flat. Over `U` the module `F` has a finite model `M` and `K` a dualizing
model `ω`, and then

* `Stacks.Duality.nonempty_stalk_extSheafOf_iso_extendScalars` makes the stalk of `𝓔ⁱ` the base
  change along `f` of `H^{-i}(RHom_A(M[0], ω))`;
* `AlgebraicGeometry.AffineExt.extLinearEquivHomologyDerivedHom` reads that cohomology module as
  `Ext^{-i}_{D(A)}(M[0], ω)`;
* `Dualizing.nonempty_ext_extendScalars_linearEquiv_of_flat` ([Stacks, Tag 0A6A]) base changes
  the extension module along the flat map `f`;
* `Stacks.Duality.nonempty_stalk_iso_extendScalars_of_affineModel` and
  `Stacks.Duality.nonempty_derivedStalkOfComplex_iso_extendScalars` rewrite the two arguments of
  the resulting `Ext` as `F_x` and the derived stalk of `K` at `x`;
* `Dualizing.nonempty_ext_shift_linearEquiv` moves the normalizing shift `-δ(x)` from the degree
  onto the target.

## Main results

* `Stacks.Duality.nonempty_stalk_extSheafOf_moduleExtInto` — the stalk at `x` of
  `𝓔xt^{-i}_{𝒪_X}(F, K)` is `Ext^{δ(x) - i}_{𝒪_{X,x}}(F_x, (ω^•_{X,x})⟦-δ(x)⟧)`.

## Implementation notes

The two sides of the linear equivalence live in different universes: the stalk is a `Type u`,
while an extension module in the derived category of `ModuleCat.{u} B` is a `Type (u + 1)`.
`LinearEquiv` allows that, and no universe lift appears in the statement.

Every intermediate type of the composite is written out. Left to inference, the elaborator has to
compute the objects of composite functors through `AlgebraicGeometry.Scheme.Modules`, which is a
`def` rather than an `abbrev`, and that exceeds the `whnf` heartbeat budget.

The base change of the extension module is taken in the form
`Dualizing.nonempty_ext_extendScalars_linearEquiv_of_flat`, whose right-hand side is an ordinary
tensor product, rather than `Dualizing.nonempty_extendScalars_ext_linearEquiv`, whose left-hand
side is an extension of scalars at the module universe `u + 1`: the identification of such an
extension of scalars with a tensor product is not available at that universe.

## References

* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0ECM](https://stacks.math.columbia.edu/tag/0ECM)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.Duality

-- Standard model only: `Stacks.Duality.associatedShiftFunction`,
--   `StacksDraft.DerivedHom.derivedHomAdjunction`.
attribute [local instance 10000] HasDerivedCategory.standard

/-- **The stalk of `𝓔xt^{-i}(F, K)` at `x` is the normalized Ext module of [Stacks, Tag 0A6H].**
For `F` coherent on a locally Noetherian scheme `X` and `K` a dualizing complex with shift
function `δ = Stacks.Duality.associatedShiftFunction K`, the stalk at `x` of the Ext sheaf
`𝓔ⁱ = 𝓔xt^{-i}_{𝒪_X}(F, K)` is `Ext^{δ(x) - i}_{𝒪_{X,x}}(F_x, (ω^•_{X,x})⟦-δ(x)⟧)`, where
`ω^•_{X,x}` is the derived stalk at `x` of the canonical representative of `K`.

This is the hypothesis `hstalk` of `Stacks.Duality.isStalkwiseDualExt_extSheafOf`, hence the last
input the four clauses of [Stacks, Tag 0ECM] were waiting for. -/
theorem nonempty_stalk_extSheafOf_moduleExtInto {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [_root_.SheafOfModules.IsCoherent F]
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (x : X) (i : ℤ) :
    Nonempty ((extSheafOf F K i).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      Dualizing.moduleExtInto (F.presheaf.stalk x)
        ((derivedStalkOfComplex x (DerivedCategory.Q.objPreimage K))⟦
          -associatedShiftFunction K x⟧)
        (associatedShiftFunction K x - i)) := by
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨M, hMfin, hM⟩ := exists_affineModel_of_isCoherent F hU
  obtain ⟨ω, hωd, hω⟩ := hK U hU
  let := (affineGermRingHom hU x hxU).toAlgebra
  have := isLocalization_affineGermRingHom hU x hxU
  have hflat : (affineGermRingHom hU x hxU).Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl)
  -- Extension of scalars along the flat map `f` is exact, so it acts on derived categories.
  have : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (affineGermRingHom hU x hxU)) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ hflat
  have : PreservesFiniteColimits
      (ModuleCat.extendScalars.{u, u, u} (affineGermRingHom hU x hxU)) :=
    ModuleCat.extendScalars_preservesFiniteColimits _
  -- The single complex on the affine model of `F`, and the affine Ext module in degree `-i`.
  let SM : DerivedCategory (ModuleCat.{u} Γ(X, U)) :=
    (DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj M
  let Nmod : ModuleCat.{u} Γ(X, U) :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) (-i)).obj
      ((StacksDraft.DerivedHom.derivedHomAdjunction (R := Γ(X, U))).hom.obj (Opposite.op SM, ω))
  -- The stalk of `F` and the derived stalk of `K`, over the local ring at `x`.
  let Fx : ModuleCat.{u} (X.presheaf.stalk x) :=
    (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj F
  let Dx : DerivedCategory (ModuleCat.{u} (X.presheaf.stalk x)) :=
    derivedStalkOfComplex x (DerivedCategory.Q.objPreimage K)
  -- Over the Noetherian ring `Γ(X, U)` a finite module is pseudo-coherent, [Stacks, Tag 066E].
  have hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent SM :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      SM 0 (M : Type u)).2.2.mpr hMfin
  -- A dualizing complex is cohomologically bounded, in particular bounded below.
  have hplus : (DerivedCategory.TStructure.t).plus ω :=
    (Dualizing.IsDualizingComplex.bounded hωd).1
  -- Step 1: the stalk of the Ext sheaf is the base change of the affine Ext module.
  have e1 : ((extSheafOf F K i).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
      ((ModuleCat.extendScalars.{u, u, u} (affineGermRingHom hU x hxU)).obj Nmod) :=
    (nonempty_stalk_extSheafOf_iso_extendScalars F K hU x hxU M ω hM hω hpc
      hplus i).some.toLinearEquiv
  -- Step 2: the base change is the ordinary tensor product.
  have e2 : ((ModuleCat.extendScalars.{u, u, u} (affineGermRingHom hU x hxU)).obj Nmod)
      ≃ₗ[X.presheaf.stalk x] TensorProduct Γ(X, U) (X.presheaf.stalk x) Nmod :=
    StacksDraft.DerivedHom.HomModuleBaseChange.extendScalarsObjTensorEquiv
      (R := Γ(X, U)) (A := X.presheaf.stalk x) Nmod
  -- Step 3: the affine cohomology module is the affine extension module.
  have e3 : TensorProduct Γ(X, U) (X.presheaf.stalk x) Nmod ≃ₗ[X.presheaf.stalk x]
      TensorProduct Γ(X, U) (X.presheaf.stalk x) (DerivedCategory.Ext SM ω (-i)) :=
    LinearEquiv.baseChange Γ(X, U) (X.presheaf.stalk x) Nmod
      (DerivedCategory.Ext SM ω (-i))
      (AlgebraicGeometry.AffineExt.extLinearEquivHomologyDerivedHom Γ(X, U) SM ω (-i))
  -- Step 4: [Stacks, Tag 0A6A]: the extension module base changes along the flat map `f`.
  have e4 : TensorProduct Γ(X, U) (X.presheaf.stalk x) (DerivedCategory.Ext SM ω (-i))
      ≃ₗ[X.presheaf.stalk x] DerivedCategory.Ext
        ((ModuleCat.extendScalars.{u, u, u}
          (affineGermRingHom hU x hxU)).mapDerivedCategory.obj SM)
        ((ModuleCat.extendScalars.{u, u, u}
          (affineGermRingHom hU x hxU)).mapDerivedCategory.obj ω) (-i) :=
    (Dualizing.nonempty_ext_extendScalars_linearEquiv_of_flat
      (affineGermRingHom hU x hxU) hflat SM ω hpc hplus (-i)).some.symm
  -- Step 5: the two arguments of that `Ext` are the stalk of `F` and the derived stalk of `K`.
  have iM : (DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj Fx ≅
      (ModuleCat.extendScalars.{u, u, u}
        (affineGermRingHom hU x hxU)).mapDerivedCategory.obj SM := by
    have iF : Fx ≅ (ModuleCat.extendScalars.{u, u, u} (affineGermRingHom hU x hxU)).obj M :=
      (nonempty_stalk_iso_extendScalars_of_affineModel hU x hxU F M hM).some
    have iS : (ModuleCat.extendScalars.{u, u, u}
          (affineGermRingHom hU x hxU)).mapDerivedCategory.obj SM ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj
          ((ModuleCat.extendScalars.{u, u, u} (affineGermRingHom hU x hxU)).obj M) :=
      ((ModuleCat.extendScalars.{u, u, u}
        (affineGermRingHom hU x hxU)).mapDerivedCategorySingleFunctor 0).app M
    exact (DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).mapIso iF ≪≫
      iS.symm
  have iω : (ModuleCat.extendScalars.{u, u, u}
      (affineGermRingHom hU x hxU)).mapDerivedCategory.obj ω ≅ Dx :=
    (nonempty_derivedStalkOfComplex_iso_extendScalars (DerivedCategory.Q.objPreimage K)
      ⟨DerivedCategory.Q.objObjPreimageIso K⟩ hU x hxU ω hω).some.symm
  have e5 : DerivedCategory.Ext
        ((ModuleCat.extendScalars.{u, u, u}
          (affineGermRingHom hU x hxU)).mapDerivedCategory.obj SM)
        ((ModuleCat.extendScalars.{u, u, u}
          (affineGermRingHom hU x hxU)).mapDerivedCategory.obj ω) (-i)
      ≃ₗ[X.presheaf.stalk x] DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj Fx) Dx (-i) :=
    StacksDraft.DerivedHom.HomModuleBaseChange.homCongrLinearEquiv (X.presheaf.stalk x) iM
      ((CategoryTheory.shiftFunctor
        (DerivedCategory (ModuleCat.{u} (X.presheaf.stalk x))) (-i)).mapIso iω)
  -- Step 6: move the normalizing shift from the degree onto the target.
  have e6 : DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj Fx) Dx (-i)
      ≃ₗ[X.presheaf.stalk x] DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj Fx)
        (Dx⟦-associatedShiftFunction K x⟧) (associatedShiftFunction K x + -i) :=
    (Dualizing.nonempty_ext_shift_linearEquiv
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj Fx) Dx
      (associatedShiftFunction K x) (-i)).some.symm
  -- Compose, one link at a time.
  have f2 : ((extSheafOf F K i).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
      TensorProduct Γ(X, U) (X.presheaf.stalk x) Nmod := e1.trans e2
  have f3 : ((extSheafOf F K i).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
      TensorProduct Γ(X, U) (X.presheaf.stalk x) (DerivedCategory.Ext SM ω (-i)) := f2.trans e3
  have f4 : ((extSheafOf F K i).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
      DerivedCategory.Ext
        ((ModuleCat.extendScalars.{u, u, u}
          (affineGermRingHom hU x hxU)).mapDerivedCategory.obj SM)
        ((ModuleCat.extendScalars.{u, u, u}
          (affineGermRingHom hU x hxU)).mapDerivedCategory.obj ω) (-i) := f3.trans e4
  have f5 : ((extSheafOf F K i).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj Fx) Dx (-i) :=
    f4.trans e5
  have f6 : ((extSheafOf F K i).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj Fx)
        (Dx⟦-associatedShiftFunction K x⟧) (associatedShiftFunction K x + -i) := f5.trans e6
  exact ⟨f6⟩

end Stacks.Duality

end
