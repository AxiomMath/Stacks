module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AlgebraFibreProductQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.SubQuotient
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleFiniteness.FiniteType
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FpqcTopology.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.BiproductQuasicoherent
public import StacksFrontier.Topology.Sheaves.Functors.Module.FlatPullback
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Coherence of a fibre product of a module with the pushforward of a coherent submodule

Let `f : Y ⟶ X` be a flat, surjective, quasi-compact and quasi-separated morphism of locally
Noetherian schemes, let `F` be a quasi-coherent module on `X`, and let `G ⊆ f^*F` be a coherent
submodule. Then the fibre product of the unit `F ⟶ f_* f^* F` of the pullback-pushforward
adjunction with `f_* G ⟶ f_* f^* F` is coherent on `X`.

Quasi-coherence of that fibre product is formal and is supplied by
`Stacks.AlgebraicGeometry.AlgebraFibreProduct.isQuasicoherent_fibreProductModules`: the fibre
product of two morphisms into a common target is the kernel of the difference out of the
biproduct, and quasi-coherence is stable under biproducts, pullbacks, pushforwards along
quasi-compact quasi-separated morphisms and kernels. Finite type is the only place flatness is
used: pulling the fibre product back along `f` exhibits it as a submodule of `G`, which is
coherent, and `f` being flat the pullback functor is left exact, so the comparison morphism is
still a monomorphism. Finite type then descends along the fpqc covering `{f}` (Stacks 05AZ), and
coherence for a locally Noetherian scheme is quasi-coherence together with finite type
(Stacks 01XZ).

## Main results

* `AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat`: module pullback along a
  flat morphism of schemes is left exact.
* `AlgebraicGeometry.isCoherent_pullback_pushforward`: **Stacks 07TT**.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 05AZ](https://stacks.math.columbia.edu/tag/05AZ)
* [Stacks Project, Tag 07TT](https://stacks.math.columbia.edu/tag/07TT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- Module pullback along a flat morphism of schemes is left exact: on underlying ringed spaces
it is the module pullback of a flat morphism of ringed spaces. -/
theorem preservesFiniteLimits_modulesPullback_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    PreservesFiniteLimits (Scheme.Modules.pullback f) :=
  preservesFiniteLimits_modulePullback_of_isFlat f.toLRSHom.toShHom
    fun x => Flat.stalkMap f x

/-- **Stacks Project, Tag 07TT.** For a flat, surjective, quasi-compact and quasi-separated
morphism `f : Y ⟶ X` of locally Noetherian schemes, a quasi-coherent module `F` on `X` and a
coherent submodule `G` of `f^*F`, the fibre product of the unit `F ⟶ f_* f^* F` with the
pushforward of the inclusion is coherent. -/
@[stacks 07TT]
theorem isCoherent_pullback_pushforward {X Y : Scheme.{u}} (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [Flat f] [Surjective f]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (F : X.Modules) [F.IsQuasicoherent]
    (G : Y.Modules) [G.IsQuasicoherent] [G.IsCoherent]
    (φ : G ⟶ (Scheme.Modules.pullback f).obj F) [Mono φ] :
    (pullback ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F)
      ((Scheme.Modules.pushforward f).map φ)).IsCoherent := by
  have hFid : ((𝟭 X.Modules).obj F).IsQuasicoherent := inferInstanceAs F.IsQuasicoherent
  have hRL : ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward f).obj F
      ).IsQuasicoherent :=
    inferInstanceAs (((Scheme.Modules.pushforward f).obj
      ((Scheme.Modules.pullback f).obj F)).IsQuasicoherent)
  have hGid : ((𝟭 Y.Modules).obj G).IsCoherent := inferInstanceAs G.IsCoherent
  have hradj : (Scheme.Modules.pushforward f).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  have hnat : (Scheme.Modules.pullback f).map ((Scheme.Modules.pushforward f).map φ) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app
        ((Scheme.Modules.pullback f).obj F) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app G ≫ φ :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).counit.naturality φ
  set η := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F with hη
  set ψ := (Scheme.Modules.pushforward f).map φ with hψ
  have hPqc : (pullback η ψ).IsQuasicoherent := inferInstance
  have hmonoψ : Mono ψ := hψ ▸ Functor.map_mono _ φ
  have hexact : PreservesFiniteLimits (Scheme.Modules.pullback f) :=
    preservesFiniteLimits_modulesPullback_of_flat f
  have hdiag : (Scheme.Modules.pullback f).map (pullback.fst η ψ) =
      ((Scheme.Modules.pullback f).map (pullback.snd η ψ) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app G) ≫ φ := by
    have hmap : (Scheme.Modules.pullback f).map (pullback.fst η ψ) ≫
        (Scheme.Modules.pullback f).map η =
        (Scheme.Modules.pullback f).map (pullback.snd η ψ) ≫
          (Scheme.Modules.pullback f).map ψ := by
      simpa only [← Functor.map_comp] using
        congrArg (Scheme.Modules.pullback f).map pullback.condition
    calc (Scheme.Modules.pullback f).map (pullback.fst η ψ)
        = (Scheme.Modules.pullback f).map (pullback.fst η ψ) ≫
            (Scheme.Modules.pullback f).map η ≫
            (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app
              ((Scheme.Modules.pullback f).obj F) := by
          rw [hη, (Scheme.Modules.pullbackPushforwardAdjunction f).left_triangle_components F]
          exact (Category.comp_id _).symm
      _ = (Scheme.Modules.pullback f).map (pullback.snd η ψ) ≫
            (Scheme.Modules.pullback f).map ψ ≫
            (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app
              ((Scheme.Modules.pullback f).obj F) := by
          rw [← Category.assoc, hmap, Category.assoc]
      _ = (Scheme.Modules.pullback f).map (pullback.snd η ψ) ≫
            (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app G ≫ φ := by
          rw [hψ, hnat]
      _ = _ := (Category.assoc _ _ _).symm
  have ha : Mono ((Scheme.Modules.pullback f).map (pullback.fst η ψ)) :=
    Functor.map_mono _ (pullback.fst η ψ)
  have hm : Mono ((Scheme.Modules.pullback f).map (pullback.snd η ψ) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app G) := by
    refine ⟨fun {Z} g h hgh => ?_⟩
    refine (cancel_mono ((Scheme.Modules.pullback f).map (pullback.fst η ψ))).1 ?_
    calc g ≫ (Scheme.Modules.pullback f).map (pullback.fst η ψ)
        = (g ≫ ((Scheme.Modules.pullback f).map (pullback.snd η ψ) ≫
            (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app G)) ≫ φ := by
          rw [Category.assoc, hdiag]
      _ = (h ≫ ((Scheme.Modules.pullback f).map (pullback.snd η ψ) ≫
            (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app G)) ≫ φ := by rw [hgh]
      _ = h ≫ (Scheme.Modules.pullback f).map (pullback.fst η ψ) := by
          rw [Category.assoc, hdiag]
  have hPcoh : (((Scheme.Modules.pullback f).obj (pullback η ψ))).IsCoherent :=
    have : (pullback η ψ).IsQuasicoherent := hPqc
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_mono_of_isQuasicoherent
      ((Scheme.Modules.pullback f).map (pullback.snd η ψ) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app G)
  have hPft : (pullback η ψ).IsFiniteType := by
    have hcover : Presieve.ofArrows (fun _ : PUnit.{1} => Y) (fun _ => f) ∈
        Scheme.fpqcPrecoverage X := by
      rw [Presieve.ofArrows_pUnit.{0}]
      exact Scheme.Hom.singleton_mem_fpqcPrecoverage f
    refine isFiniteType_of_pullback_fpqc (pullback η ψ) hPqc (fun _ : PUnit.{1} => Y)
      (fun _ => f) hcover fun _ => ?_
    have : (((Scheme.Modules.pullback f).obj (pullback η ψ))).IsCoherent := hPcoh
    exact _root_.SheafOfModules.IsCoherent.isFiniteType
      (M := (Scheme.Modules.pullback f).obj (pullback η ψ))
  have : (pullback η ψ).IsQuasicoherent := hPqc
  have : (pullback η ψ).IsFiniteType := hPft
  exact Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType
    (pullback η ψ)

end AlgebraicGeometry

end
