module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyTrivialInvertible.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf

/-!
# The rank of a finite locally free module on an integral scheme is read off one point

The fibre rank of a finite locally free module is locally constant, and the underlying space of
an integral scheme is irreducible, hence preconnected. So on an integral scheme a finite locally
free module whose fibre rank equals `s` at a *single* point is finite locally free of rank `s`
everywhere; for `s = 1` it is therefore invertible.

Independently, every exterior power of a quasi-coherent sheaf of modules on a ringed space is
quasi-coherent: a presentation of the module over an open presents each of its exterior powers
over that same open, so the covering family presenting the module presents the exterior power.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq`: on an integral
  scheme, a finite locally free module with fibre rank `s` at one point is finite locally free
  of rank `s`.
* `AlgebraicGeometry.Scheme.Modules.isInvertible_of_fiberRank_eq_one`: the rank-one case, where
  the conclusion is invertibility.
* `Stacks.SheafOfModules.isQuasicoherent_exteriorPower`: each exterior power of a quasi-coherent
  sheaf of modules on a ringed space is quasi-coherent.

## Implementation notes

The first result carries no `@[stacks]` attribute: it is not a numbered item of the source at all
— the Stacks Project uses the constancy of the rank on an irreducible space inside proofs without
isolating it. The second is clause (5) of Tag 01CK for the exterior powers and is tagged as such;
the symmetric and tensor cases of that clause are
`Stacks.SheafOfModules.isQuasicoherent_symmetricPower` and `isQuasicoherent_tensorPower`.
Both exist as infrastructure for Tag 0B3T, whose invertibility assertion is that the reflexive
hull of the top exterior power of a coherent module of generic rank `r` on an integral regular
surface is a line bundle: the exterior power must be shown coherent before its hull can be
formed, and the hull, once known to be finite locally free, must be shown to have rank one
everywhere from having rank one on the open where the generic rank is attained.

Three points of friction in the first proof are worth recording.

* Local constancy of the fibre rank
  (`AlgebraicGeometry.Scheme.Modules.isLocallyConstant_fiberRank`) is stated with the spelling
  `Stacks.FiniteLocallyFree.IsFiniteLocallyFree`, a reducible abbreviation of the canonical class
  `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`. The instance is built with
  `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u}`: the anonymous constructor
  elaborates the `LocalGeneratorsData` field at universe zero and fails to unify with the
  extracted data.
* Preconnectedness of the space is not hypothesised. `IsIntegral` gives irreducibility, from
  which instance search supplies `PreconnectedSpace`, which is what
  `IsLocallyConstant.apply_eq_of_preconnectedSpace` consumes.
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_restrict_of_fiberRank_eq` concludes
  for the restriction `M.restrict U.ι` to an open, so with `U = ⊤` it gives the rank of a module
  on the open subscheme `⊤` rather than on `X`. The way back is not an isomorphism of modules but
  the one-member open cover: `isFiniteLocallyFreeOfRank_of_iSup_eq_top` glues the pointwise
  predicate `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank` over the cover
  `fun _ : PUnit => ⊤`, and `isFiniteLocallyFreeOfRank_iff` converts between that predicate and
  the class.

## References

* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **On an integral scheme the rank of a finite locally free module is determined by one
point.** The fibre rank of a finite locally free module is locally constant and the space is
preconnected, so a module whose fibre rank is `s` at a single point has fibre rank `s`
everywhere, and a finite locally free module of constant fibre rank `s` is finite locally free
of rank `s`. -/
theorem isFiniteLocallyFreeOfRank_of_fiberRank_eq {X : Scheme.{u}} [IsIntegral X]
    (M : X.Modules)
    [h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M]
    (s : ℕ) (x₀ : X) (hx₀ : fiberRank M x₀ = s) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M s := by
  obtain ⟨q, hq, hqft⟩ := h.exists_isFiniteLocallyFreeData
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u} ⟨q, hq, hqft⟩
  have hconst : ∀ x : X, fiberRank M x = s := fun x =>
    ((isLocallyConstant_fiberRank M).apply_eq_of_preconnectedSpace x x₀).trans hx₀
  have hres : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (M.restrict (⊤ : X.Opens).ι) s :=
    isFiniteLocallyFreeOfRank_restrict_of_fiberRank_eq M ⊤ s fun x _ => hconst x
  have htop : IsFiniteLocallyFreeOfRank M s :=
    isFiniteLocallyFreeOfRank_of_iSup_eq_top (ι := PUnit.{u + 1}) (fun _ => (⊤ : X.Opens))
      (by simp) fun _ => (isFiniteLocallyFreeOfRank_iff _ s).2 hres
  exact (isFiniteLocallyFreeOfRank_iff M s).1 htop

/-- **A finite locally free module on an integral scheme with a single fibre of dimension one is
invertible.** Its rank is one everywhere by
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq`, and a module of
rank one on a ringed space is invertible by clause 1 of Tag 0B8M. -/
theorem isInvertible_of_fiberRank_eq_one {X : Scheme.{u}} [IsIntegral X] (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M]
    (x₀ : X) (hx₀ : fiberRank M x₀ = 1) :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property M :=
  have := isFiniteLocallyFreeOfRank_of_fiberRank_eq M 1 x₀ hx₀
  Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace M

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.SheafOfModules

/-- **Each exterior power of a quasi-coherent sheaf of modules on a ringed space is
quasi-coherent.** A presentation of the module over an open presents every exterior power of it
over that same open, by `Stacks.SheafOfModules.nonempty_presentation_exteriorPower_over`, so the
covering family which presents the module presents the exterior power too. -/
@[stacks 01CK "exterior powers of a quasi-coherent module"]
theorem isQuasicoherent_exteriorPower {X : RingedSpace.{u, u}}
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) [F.IsQuasicoherent]
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier) F) (n : ℕ) :
    (A.exteriorPower n).IsQuasicoherent := by
  obtain ⟨c⟩ := _root_.SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := F)
  have q : _root_.SheafOfModules.QuasicoherentData.{u, u, u, u} (A.exteriorPower n) :=
    { I := c.I
      X := c.X
      coversTop := c.coversTop
      presentation := fun i =>
        (nonempty_presentation_exteriorPower_over (c.X i) F A (c.presentation i) n).some }
  exact q.isQuasicoherent

end Stacks.SheafOfModules

end
