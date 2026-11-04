module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtIdealPowerRestrict
public import StacksFrontier.AlgebraicGeometry.Duality.IdealPowerSubmoduleArtinRees

/-!
# A morphism surjective on `U` catches a power of the ideal filtration of its target

Let `X` be a Noetherian scheme, `𝓘` a quasi-coherent sheaf of ideals, `U = X ∖ V(𝓘)`, and let
`ψ : 𝓔 ⟶ 𝓕` be a morphism of `𝒪_X`-modules with `𝓕` coherent whose **restriction to `U` is an
epimorphism**. Then some member of the ideal-power filtration of `𝓕` is contained in the image
of `ψ`:

`𝓘^m 𝓕 ⊆ Im ψ`.

This is the fourth input of the surjectivity half of the induction on `i` in the core case of
[Stacks, Tag 0G2H]. There the morphism `ψ` is the extension across `j` of the coherent
effacement `𝓗 ↠ 𝓕|_U` supplied by [Stacks, Tag 01PI]: it is surjective on `U` by construction
and need not be surjective on `X`, and the chase can only proceed after replacing `𝓕` by a
member of its ideal-power filtration small enough to be hit.

## How it is proved

The quotient `𝓕 / Im ψ` is the categorical cokernel `𝓠 = coker ψ`, which is quasi-coherent, and
`Im ψ` is `AlgebraicGeometry.imageSubmodule ψ`, by definition the sectionwise kernel of the
projection `π : 𝓕 ⟶ 𝓠`. So the assertion is that `π` kills `𝓘^m 𝓕`, and since
`ψ ≫ π = 0` with `ψ|_U` an epimorphism, `π|_U = 0`.

That is exactly the hypothesis of the **injectivity half of the first display of**
[Stacks, Tag 01YB],
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_comp_eq_zero_of_restrictFunctor_map_eq_zero`,
applied to the composite `𝓘^0 𝓕 ⟶ 𝓕 ⟶ 𝓠`: a morphism out of a member of the filtration whose
restriction to `U` vanishes already vanishes on a later member. The inclusions of the filtration
compose to the inclusion, so what that produces is the vanishing of `𝓘^m 𝓕 ↪ 𝓕 ⟶ 𝓠`, which is
the containment.

[Stacks, Tag 01Y9] in the form
`AlgebraicGeometry.exists_idealPowerMultiple_eq_bot_iff_supp_subset` — some power of `𝓘`
annihilates a coherent module supported in `V(𝓘)` — is the same statement about `𝓠`, and would
reach the containment the same way through
`AlgebraicGeometry.imageSubmodule_idealPowerMultiple_of_epi`. The route taken here needs neither
the coherence of `𝓠` nor its support, only its quasi-coherence, and so puts no coherence
hypothesis on the source `𝓔`.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_idealPowerMultiple_le_imageSubmodule`: **a
  morphism into a coherent module whose restriction to `U` is an epimorphism contains a member
  of the ideal-power filtration of its target in its image.**

## Implementation notes

The composition of the two inclusions `𝓘^m 𝓕 ⟶ 𝓘^0 𝓕 ⟶ 𝓕` is made once with the submodules
kept as **variables**, in
`Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE_comp_submoduleι_comp`. Instantiated
at `Stacks.Algebraization.idealPowerMultiple`, which is an infimum of submodules, the same
statement proved by `rfl` sends the kernel into unfolding that infimum and it does not
terminate; the instantiated statement is only *used*, never re-proved.

All three of `submoduleι`, `submoduleHomOfLE` and `subMod` have their declared types at
`AlgebraicGeometry.Scheme.Modules`, which is what keeps the composites in the category the
ambient `Ext`-statements of [Stacks, Tag 0G2H] live in; `submoduleHomOfLE` is spelled with its
full name throughout because `AlgebraicGeometry.submoduleHomOfLE` is a second declaration of the
same name in the import closure.

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPower

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : _root_.AlgebraicGeometry.Scheme.{u}}

/-- **The inclusions of a chain of two submodules compose**, after a further morphism out of the
ambient module. The submodules are kept as variables: instantiated at a member of the
ideal-power filtration — an infimum of submodules — the same statement proved by `rfl` makes the
kernel unfold that infimum and does not terminate. -/
public theorem submoduleHomOfLE_comp_submoduleι_comp {L C : X.Modules} {N₁ N₂ : L.Submodule}
    (h : N₁ ≤ N₂) (g : L ⟶ C) :
    Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE h ≫ submoduleι N₂ ≫ g =
      submoduleι N₁ ≫ g :=
  (Category.assoc _ _ _).symm.trans (congrArg (fun k : subMod N₁ ⟶ L => k ≫ g)
    (submoduleHomOfLE_ι h))

/-- The inclusion `𝓘^m 𝓖 ⟶ 𝓘^n 𝓖` of the ideal-power filtration is the inclusion of one
submodule of `𝓖` into a larger one, at the `AlgebraicGeometry.Scheme.Modules` spelling. -/
public theorem idealPowSmulMap_eq_submoduleHomOfLE (I : X.IdealSheafData) (G : X.Modules)
    {n m : ℕ} (h : n ≤ m) :
    Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulMap I G h =
      Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleHomOfLE
        (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_antitone I G h) :=
  rfl

/-- **A submodule whose inclusion dies in the cokernel of `ψ` lies in the image of `ψ`.** The
image submodule is by definition the sectionwise kernel of the projection to the cokernel, and
the sectionwise image of the inclusion of `N` is `N`. -/
public theorem le_imageSubmodule_of_submoduleι_comp_cokernelπ_eq_zero {E L : X.Modules}
    (ψ : E ⟶ L) (N : L.Submodule)
    (h : submoduleι N ≫ cokernel.π (C := X.Modules) ψ = 0) :
    N ≤ _root_.AlgebraicGeometry.imageSubmodule ψ :=
  (le_of_eq (_root_.AlgebraicGeometry.imageSubmodule_subι N).symm).trans
    (_root_.AlgebraicGeometry.imageSubmodule_le_kernelSubmodule
      (_root_.AlgebraicGeometry.subι N) _ h)

/-- **A morphism into a coherent module whose restriction to `U` is an epimorphism contains a
member of the ideal-power filtration of its target in its image.** Let `X` be a Noetherian
scheme, `𝓘` a quasi-coherent sheaf of ideals, `U = X ∖ V(𝓘)` and `ψ : 𝓔 ⟶ 𝓕` a morphism of
`𝒪_X`-modules with `𝓕` coherent. If `ψ|_U` is an epimorphism then `𝓘^m 𝓕 ⊆ Im ψ` for some `m`.

This is the step of the surjectivity chase of [Stacks, Tag 0G2H] at which the effacement
extended from `U` across the open immersion becomes usable on `X`: it is surjective only on `U`,
and the containment says how far down the ideal-power filtration of `𝓕` one has to go for it to
be surjective onto. The module documentation describes the proof and its relation to
[Stacks, Tag 01Y9]. -/
public theorem exists_idealPowerMultiple_le_imageSubmodule
    [_root_.AlgebraicGeometry.IsNoetherian X] (I : X.IdealSheafData) (U : X.Opens)
    (hU : U = I.support.compl) {E F : X.Modules} [E.IsQuasicoherent] [F.IsCoherent] (ψ : E ⟶ F)
    (hψ : Epi ((Scheme.Modules.restrictFunctor U.ι).map ψ)) :
    ∃ m : ℕ, Stacks.Algebraization.idealPowerMultiple I m F ≤
      _root_.AlgebraicGeometry.imageSubmodule ψ := by
  have := hψ
  have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  have : (cokernel (C := X.Modules) ψ).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel ψ
  set π : F ⟶ cokernel (C := X.Modules) ψ := cokernel.π (C := X.Modules) ψ with hπdef
  -- `π` vanishes on `U`, because `ψ ≫ π = 0` and `ψ|_U` is an epimorphism.
  have hres : (Scheme.Modules.restrictFunctor U.ι).map ψ ≫
      (Scheme.Modules.restrictFunctor U.ι).map π = 0 := by
    rw [← Functor.map_comp, hπdef, cokernel.condition, Functor.map_zero]
  have hπU : (Scheme.Modules.restrictFunctor U.ι).map π = 0 := zero_of_epi_comp _ hres
  -- The composite `𝓘^0 𝓕 ⟶ 𝓕 ⟶ coker ψ` therefore vanishes on `U` as well.
  have hcomp : (Scheme.Modules.restrictFunctor U.ι).map
      (submoduleι (Stacks.Algebraization.idealPowerMultiple I 0 F) ≫ π) = 0 := by
    rw [Functor.map_comp, hπU, Limits.comp_zero]
  obtain ⟨m, hm⟩ := exists_comp_eq_zero_of_restrictFunctor_map_eq_zero I U hU
    (G := F) (F := cokernel (C := X.Modules) ψ)
    (ψ := submoduleι (Stacks.Algebraization.idealPowerMultiple I 0 F) ≫ π) hcomp
  -- The inclusions of the filtration compose to the inclusion of the later member, so what
  -- `hm` says is that `𝓘^m 𝓕 ↪ 𝓕 ⟶ coker ψ` vanishes.
  have hbr := submoduleHomOfLE_comp_submoduleι_comp
    (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_antitone I F
      (Nat.le_add_right 0 m)) π
  exact ⟨0 + m,
    le_imageSubmodule_of_submoduleι_comp_cokernelπ_eq_zero ψ _ (hbr.symm.trans hm)⟩

end Stacks.AlgebraicGeometry.IdealPowerColimit

end
