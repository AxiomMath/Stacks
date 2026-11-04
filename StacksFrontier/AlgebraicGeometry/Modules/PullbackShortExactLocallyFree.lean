module

public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.KernelBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StalkSplittingLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackLocallySplit

/-!
# A short exact sequence with finite locally free quotient stays exact under every pullback

Let `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` be a short exact sequence of modules on a scheme `X` whose quotient
`ℰ₂` is finite locally free. Then for every morphism of schemes `g : X' ⟶ X`, with no flatness
assumed, the pulled-back sequence `0 ⟶ g^*ℰ₁ ⟶ g^*ℰ ⟶ g^*ℰ₂ ⟶ 0` is short exact.

The pullback of modules is a left adjoint, so it keeps the cokernel half of the sequence; the
content is that the first map stays a monomorphism. At every point the stalk of `ℰ₂` is a free,
hence projective, module, so the stalk of `ℰ ⟶ ℰ₂` splits, and a module pullback keeps the
kernel inclusion of a stalkwise-split surjection injective
(`Stacks.RingedSpace.mono_modulePullback_map_kernel_ι_of_isSplitEpi_stalk`).

## Main results

* `AlgebraicGeometry.Scheme.Modules.isSplitEpi_stalkFunctor_map_of_shortExact` — the stalks of
  the surjection of such a sequence split.
* `AlgebraicGeometry.Scheme.Modules.mono_pullback_map_of_shortExact` — the pullback of the first
  map is a monomorphism.

The short exactness of the pulled-back sequence itself is
`AlgebraicGeometry.Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree`
(`StacksFrontier.AlgebraicGeometry.Modules.PullbackLocallySplit`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (S : ShortComplex X.Modules) (hS : S.ShortExact)
  [hfl : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃]

include hS in
/-- **The stalks of the surjection of a short exact sequence with finite locally free quotient
split.** The stalk of a finite locally free module is projective, and the stalk sequence is short
exact. -/
theorem isSplitEpi_stalkFunctor_map_of_shortExact (x : X) :
    IsSplitEpi ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafRing X.toRingedSpace) x).map S.g) := by
  have hSE : (ShortComplex.mk S.f S.g S.zero).ShortExact := hS
  have hlf : _root_.SheafOfModules.IsLocallyFree.{u} S.X₃ :=
    hfl.exists_isFiniteLocallyFreeData.elim fun q h ↦ ⟨q, h.1⟩
  have hproj := Stacks.AlgebraicGeometry.ProjEulerSequence.projective_stalk_of_isLocallyFree
    X.sheaf S.X₃ (hM := hlf) x
  exact ⟨⟨_, (Stacks.AlgebraicGeometry.ProjEulerSequence.stalkSplittingOfProjectiveStalk X.sheaf
    S.zero hSE x hproj).s_g⟩⟩

include hS in
/-- **The pullback of the first map of a short exact sequence with finite locally free quotient
is a monomorphism**, along every morphism of schemes. -/
theorem mono_pullback_map_of_shortExact :
    Mono ((Scheme.Modules.pullback g).map S.f) := by
  have hk : Mono ((Scheme.Modules.pullback g).map (kernel.ι S.g)) :=
    Stacks.RingedSpace.mono_modulePullback_map_kernel_ι_of_isSplitEpi_stalk
      g.toLRSHom.toShHom S.g fun x => isSplitEpi_stalkFunctor_map_of_shortExact S hS _
  -- `S.f` is a kernel of `S.g`, so it factors as an isomorphism onto `kernel S.g`.
  have : IsIso (kernel.lift S.g S.f S.zero) :=
    (kernelIsKernel S.g).nonempty_isLimit_iff_isIso_lift.mp ⟨hS.fIsKernel⟩
  rw [← kernel.lift_ι (f := S.g) S.f S.zero, Functor.map_comp]
  exact mono_comp _ _

end AlgebraicGeometry.Scheme.Modules

end
