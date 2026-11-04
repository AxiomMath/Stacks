module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDualizingSlice
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDualizingHomothetyOfIsIso
import StacksCore.Tactic.StacksAttribute

/-!
# The derived endomorphisms over an affine open, on the slice site

If the restriction to an affine open `V ⊆ W` of an object `K` of `D(𝒪_W)` is the complex
associated to a pseudo-coherent, bounded below `ω` with invertible derived homothety, then
`R𝓗om(K|_V, K|_V)` on the slice site `Opens(W)/V` is the structure sheaf in degree zero.

## Main results

* `Stacks.Duality.nonempty_derivedSheafHom_restrictD_self_iso_unit`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace AlgebraicGeometry Stacks.SheafOfModules

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor

namespace Stacks.Duality

/-- **The derived endomorphisms of a complex over an affine open, read on the slice site, are
the structure sheaf.** Let `V ⊆ W` be an affine open and `K` an object of `D(𝒪_W)` whose
restriction to `V` is the complex associated to an object `ω` of `D(Γ(W, V))`. If `ω` is
pseudo-coherent and bounded below and its derived homothety `Γ(W, V) ⟶ R𝐻om(ω, ω)` is
invertible, then `R𝓗om(K|_V, K|_V)` on the slice site `Opens(W)/V` is isomorphic to the
structure sheaf in degree zero.

Over `Spec Γ(W, V)` this is `Stacks.Duality.derivedTildeDerivedSheafHomSelfUnitIsoOfIsIso`; it
is carried to the open subscheme `V` along the pullback by `V ≅ Spec Γ(W, V)` and reflected to
the slice site along `overEquiv V`, which carry the derived internal hom to the derived internal
hom and the structure sheaf to the structure sheaf. -/
theorem nonempty_derivedSheafHom_restrictD_self_iso_unit
    {W : Scheme.{u}} (V : W.Opens) (hV : IsAffineOpen V)
    {ω : DerivedCategory (ModuleCat.{u} Γ(W, V))}
    (hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent ω)
    (hplus : (DerivedCategory.TStructure.t).plus ω)
    (hh : IsIso (Dualizing.derivedHomothety
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := (Γ(W, V) : Type u))).toDerivedHomAdjunction
      (DerivedCategory.Q.obj (𝟙_ (StacksDraft.DerivedHom.Model.Complex (Γ(W, V) : Type u))))
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := (Γ(W, V) : Type u))).tensorUnitLeft ω))
    (K : DerivedCategory W.Modules)
    (i : ((Scheme.Modules.overEquiv V).functor).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u} W.ringCatSheaf V).mapDerivedCategory.obj K) ≅
      (tilde.functor Γ(W, V) ⋙
        Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj ω) :
    Nonempty (((RingedSite.derivedSheafHomBifunctor ((ringedSite W.sheaf).over V)).obj
        (op ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite W.sheaf) V).obj K))).obj
          ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite W.sheaf) V).obj K) ≅
      (DerivedCategory.singleFunctor
          (Stacks.SheafOfModules.DerivedMonoidal.Mod (OverEquivTensor.sliceRingSheaf W V)) 0).obj
        (_root_.SheafOfModules.unit (Tensor.ringSheaf.{u, u, u}
          (OverEquivTensor.sliceRingSheaf W V)))) := by
  have a := i ≪≫ (Dualizing.mapDerivedCategoryComp (tilde.functor Γ(W, V))
      (Scheme.Modules.restrictFunctor hV.isoSpec.hom)).app ω ≪≫
    (PullbackIsoTensor.restrictFunctorDerivedIsoPullback hV.isoSpec.hom).app
      ((derivedTildeStructureSheafModules Γ(W, V)).obj ω)
  have h₁ := PullbackIsoTensor.exists_iso_and_isIso_derivedSheafHomCounit_iff
    hV.isoSpec.hom ((derivedTildeStructureSheafModules Γ(W, V)).obj ω)
      ((derivedTildeStructureSheafModules Γ(W, V)).obj ω)
  have h₂ := exists_iso_and_isIso_derivedSheafHomCounit_iff_of_iso V.toScheme.sheaf a a
  have h₃ := OverEquivTensor.exists_iso_and_isIso_derivedSheafHomCounit_iff W V
    ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite W.sheaf) V).obj K)
    ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite W.sheaf) V).obj K)
  have u₀ := derivedTildeDerivedSheafHomSelfUnitIsoOfIsIso Γ(W, V) hpc hplus hh
  have t := h₃.1.some ≪≫ h₂.1.some ≪≫ h₁.1.some.symm ≪≫
    (PullbackIsoTensor.pullbackEquivMod hV.isoSpec.hom).functor.mapDerivedCategory.mapIso u₀ ≪≫
    PullbackIsoTensor.pullbackDerivedUnitIso hV.isoSpec.hom ≪≫
    (OverEquivTensor.overEquivDerivedUnitIso W V).symm
  exact ⟨((OverEquivTensor.overEquivDerivedEquivalence W V).fullyFaithfulFunctor.preimageIso t)⟩

end Stacks.Duality

end
