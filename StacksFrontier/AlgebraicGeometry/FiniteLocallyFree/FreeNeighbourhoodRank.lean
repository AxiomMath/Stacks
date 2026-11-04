module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FreeNeighbourhood
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankBaseOpen

/-!
# A coherent module whose stalks are free of rank `r` is finite locally free of rank `r`

Let `X` be a locally Noetherian scheme and `M` a coherent `𝒪_X`-module. If the stalk `M_x` has a
basis indexed by `Fin r`, then `M` is free of rank `r` on an open neighbourhood of `x`; if this
holds at every point, `M` is finite locally free of rank `r`.

`AlgebraicGeometry.Scheme.Modules.exists_free_restrict_of_free_stalk` proves the first statement
with *some* finite rank, the rank of a basis it chooses; here the basis, and so the rank, is
given, which is what is needed to conclude finite local freeness of a prescribed rank.

## Main results

* `AlgebraicGeometry.Scheme.Modules.exists_free_restrict_of_stalk_basis`: a coherent module
  whose stalk at `x` has a basis indexed by `Fin r` is free of rank `r` near `x`.
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_forall_stalk_basis`: a coherent
  module all of whose stalks have a basis indexed by `Fin r` is finite locally free of rank `r`.

## References

* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **A coherent module on a locally Noetherian scheme whose stalk at `x` is free of rank `r` is
free of rank `r` on a neighbourhood of `x`.** This is [Stacks, Tag 0B8J] with the finite
presentation supplied by coherence; the basis of the stalk, given over the `CommRingCat` stalk
of the structure sheaf, is read over the `RingCat` stalk that Tag 0B8J uses by
`Module.Basis.mapCoeffs` along `Stacks.SemilinearStalk.commStalkRingEquiv`. -/
theorem exists_free_restrict_of_stalk_basis {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) (hM : _root_.SheafOfModules.IsCoherent.{u} M) (x : X) {r : ℕ}
    (b : Module.Basis (Fin r) (X.presheaf.stalk x)
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj M)) :
    ∃ (W : X.Opens) (_ : x ∈ W),
      Nonempty (M.restrict W.ι ≅ _root_.SheafOfModules.free.{u} (ULift.{u} (Fin r))) := by
  classical
  have := hM
  have hfp : M.IsFinitePresentation := isFinitePresentation_of_isCoherent M
  let A := ToType (X.presheaf.stalk x)
  let B := ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
    (X.sheaf.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x)
  let N := ToType (M.presheaf.stalk x)
  let : Module A N :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) M.val x
  let : Module B N :=
    PresheafOfModules.instModuleCarrierStalkRingCatCarrierAbPresheafOpensCarrier M.val x
  let bA : Module.Basis (Fin r) A N := b
  let eBA : B ≃+* A := SemilinearStalk.commStalkRingEquiv X.sheaf.obj x
  let eAB := eBA.symm
  have hsmul (t : B) (n : N) : eBA t • n = t • n :=
    SemilinearStalk.comm_smul_eq X.sheaf.obj x M.val t n
  let bB : Module.Basis (Fin r) B N := bA.mapCoeffs eAB fun a n => by
    simpa only [eAB, RingEquiv.apply_symm_apply] using (hsmul (eAB a) n).symm
  obtain ⟨W, hxW, ⟨eW⟩⟩ := Stacks.SheafOfModules.exists_iso_free_over_of_stalk_iso_free M hfp x r
    ⟨(bB.reindex Equiv.ulift.symm).repr⟩
  exact ⟨W, hxW, ⟨Stacks.Modules.restrictIsoFree W M (ULift.{u} (Fin r)) eW.symm⟩⟩

/-- **A coherent module on a locally Noetherian scheme all of whose stalks are free of rank `r`
is finite locally free of rank `r`.** This is
`AlgebraicGeometry.Scheme.Modules.exists_free_restrict_of_stalk_basis` at every point. -/
theorem isFiniteLocallyFreeOfRank_of_forall_stalk_basis {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) (hM : _root_.SheafOfModules.IsCoherent.{u} M) (r : ℕ)
    (b : ∀ x : X, Module.Basis (Fin r) (X.presheaf.stalk x)
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj M)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r :=
  isFiniteLocallyFreeOfRank_of_forall_restrictIso M r fun x => by
    obtain ⟨W, hxW, ⟨e⟩⟩ := exists_free_restrict_of_stalk_basis M hM x (b x)
    exact ⟨W, hxW, ULift.{u} (Fin r), ⟨Equiv.ulift⟩, ⟨e⟩⟩

end AlgebraicGeometry.Scheme.Modules

end
