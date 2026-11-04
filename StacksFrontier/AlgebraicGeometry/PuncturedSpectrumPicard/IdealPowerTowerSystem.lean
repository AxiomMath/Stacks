module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicThickeningPushforwardSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.CompletionFiniteFreeStalks
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.StalkSupportBridges
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzSerreFreeStalk
public import StacksFrontier.AlgebraicGeometry.Thickenings.InfinitesimalTower
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.ImageBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Basic

/-!
# Coherent adic systems from modules on the closed subschemes cut out by powers of an ideal

Let `X` be a locally Noetherian scheme and `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals. Write
`Xₙ ⊆ X` for the closed subscheme cut out by `ℐ ⁿ⁺¹` and `cₙ : Xₙ ⟶ Xₙ₊₁` for the inclusions.
A family of coherent modules `ℒₙ` on `Xₙ` together with isomorphisms `cₙ^* ℒₙ₊₁ ≅ ℒₙ` gives an
object of `Coh(X, ℐ)`: the inverse system of direct images `(Xₙ ⟶ X)_* ℒₙ`. This is the way
the proof of [Stacks, Tag 0F2D] regards modules on the infinitesimal neighbourhoods as modules on
the ambient scheme ("by closed-immersion pushforward", [Stacks, Tag 01QY]).

When moreover every `ℒₙ` is finite locally free, the stalk of the `n`-th term at any point `y` is
a finite free `𝒪_{X,y} / ℐ_y ⁿ⁺¹`-module.

## Main definitions

* `Stacks.Coherent.IdealPowerStageModules`: the data `(ℒₙ, cₙ^* ℒₙ₊₁ ≅ ℒₙ)`.
* `Stacks.Coherent.IdealPowerStageModules.adicSystem`: the object of `Coh(X, ℐ)` it defines.

## Main results

* `Stacks.Coherent.IdealPowerStageModules.isCoherentAdicSystem_pushSystem`: the direct images
  form a coherent adic system.
* `Stacks.Coherent.IdealPowerStageModules.exists_stalk_linearEquiv_pi`: the stalks of the terms
  are finite free over the stalks of `𝒪_X / ℐ ⁿ⁺¹`.

## References

* [Stacks Project, Tag 0F2D](https://stacks.math.columbia.edu/tag/0F2D)
* [Stacks Project, Tag 01QY](https://stacks.math.columbia.edu/tag/01QY)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Descent (pushUnit pullbackCompHom)
open Stacks.Algebraization (idealPowerMultiple idealPowerQuotient)
open Stacks.ModuleSkyscraper (modulesStalkFunctor)

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X : Scheme.{u}} (J : X.IdealSheafData)

/-- The inclusion `Xₙ ⟶ Xₙ₊₁` of the closed subscheme cut out by `ℐ ⁿ⁺¹` into the one cut out by
`ℐ ⁿ⁺²`. -/
def idealPowerStageSucc (n : ℕ) :
    (J ^ (n + 1)).subscheme ⟶ (J ^ (n + 1 + 1)).subscheme :=
  Scheme.IdealSheafData.inclusion
    (Stacks.Thickenings.idealSheaf_pow_le_pow_right (I := J) (Nat.le_succ (n + 1)))

/-- The inclusions of the stages are compatible with the closed immersions into `X`. -/
theorem idealPowerStageSucc_subschemeι (n : ℕ) :
    idealPowerStageSucc J n ≫ (J ^ (n + 1 + 1)).subschemeι = (J ^ (n + 1)).subschemeι :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-- **A compatible family of coherent modules on the closed subschemes cut out by the powers of
an ideal sheaf**: a coherent module `ℒₙ` on `V(ℐ ⁿ⁺¹)` for every `n`, with isomorphisms
`cₙ^* ℒₙ₊₁ ≅ ℒₙ` along the inclusions `cₙ : V(ℐ ⁿ⁺¹) ⟶ V(ℐ ⁿ⁺²)`. -/
structure IdealPowerStageModules where
  /-- The module on the `n`-th stage. -/
  obj (n : ℕ) : (J ^ (n + 1)).subscheme.Modules
  /-- Every term is coherent. -/
  isCoherent (n : ℕ) : _root_.SheafOfModules.IsCoherent.{u} (obj n)
  /-- The transition isomorphism `cₙ^* ℒₙ₊₁ ≅ ℒₙ`. -/
  transitionIso (n : ℕ) :
    (Scheme.Modules.pullback (idealPowerStageSucc J n)).obj (obj (n + 1)) ≅ obj n

namespace IdealPowerStageModules

variable {J} (L : IdealPowerStageModules J)

/-- The direct image on `X` of the `n`-th term. -/
abbrev pushObj (n : ℕ) : X.Modules :=
  (Scheme.Modules.pushforward (J ^ (n + 1)).subschemeι).obj (L.obj n)

/-- The restriction to `Xₙ` of the direct image of `ℒₙ₊₁` is `ℒₙ`. -/
def pushPullbackIso (n : ℕ) :
    (Scheme.Modules.pullback (J ^ (n + 1)).subschemeι).obj (L.pushObj (n + 1)) ≅ L.obj n :=
  (asIso (pullbackCompHom (idealPowerStageSucc J n) (J ^ (n + 1 + 1)).subschemeι
      (J ^ (n + 1)).subschemeι (idealPowerStageSucc_subschemeι J n) (L.pushObj (n + 1)))).symm ≪≫
    ((Scheme.Modules.pullback (idealPowerStageSucc J n)).mapIso
        (closedImmersionCounitIso (J ^ (n + 1 + 1)).subschemeι (L.obj (n + 1))) ≪≫
      L.transitionIso n)

/-- `Stacks.Coherent.IdealPowerStageModules.pushPullbackIso` written out. -/
theorem pushPullbackIso_hom (n : ℕ) :
    (L.pushPullbackIso n).hom =
      CategoryTheory.inv (pullbackCompHom (idealPowerStageSucc J n) (J ^ (n + 1 + 1)).subschemeι
          (J ^ (n + 1)).subschemeι (idealPowerStageSucc_subschemeι J n) (L.pushObj (n + 1))) ≫
        ((Scheme.Modules.pullback (idealPowerStageSucc J n)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction
              (J ^ (n + 1 + 1)).subschemeι).counit.app (L.obj (n + 1))) ≫
          (L.transitionIso n).hom) :=
  rfl

/-- The transition `(Xₙ₊₁ ⟶ X)_* ℒₙ₊₁ ⟶ (Xₙ ⟶ X)_* ℒₙ` of the direct-image system. -/
def pushTransition (n : ℕ) : L.pushObj (n + 1) ⟶ L.pushObj n := by
  have u := (pushUnit (J ^ (n + 1 + 1)).subschemeι (idealPowerStageSucc J n)
    (J ^ (n + 1)).subschemeι (idealPowerStageSucc_subschemeι J n)).app (L.obj (n + 1))
  have v := (Scheme.Modules.pushforward (J ^ (n + 1)).subschemeι).map (L.transitionIso n).hom
  exact u ≫ v

/-- The transition of the direct-image system is the adjunction unit followed by the direct
image of `Stacks.Coherent.IdealPowerStageModules.pushPullbackIso`. -/
theorem unit_comp_map_pushPullbackIso (n : ℕ) :
    (Scheme.Modules.pullbackPushforwardAdjunction (J ^ (n + 1)).subschemeι).unit.app
          (L.pushObj (n + 1)) ≫
        (Scheme.Modules.pushforward (J ^ (n + 1)).subschemeι).map (L.pushPullbackIso n).hom =
      L.pushTransition n := by
  refine unit_comp_map_eq_pushUnit_comp_map (J ^ (n + 1 + 1)).subschemeι
    (idealPowerStageSucc J n) (idealPowerStageSucc_subschemeι J n) (L.obj (n + 1)) (L.obj n)
    (L.transitionIso n).hom (Θ := pullbackCompHom (idealPowerStageSucc J n)
      (J ^ (n + 1 + 1)).subschemeι (J ^ (n + 1)).subschemeι
      (idealPowerStageSucc_subschemeι J n) (L.pushObj (n + 1)))
    (ψ := (L.pushPullbackIso n).hom) rfl ?_
  rw [pushPullbackIso_hom]
  exact IsIso.hom_inv_id_assoc (pullbackCompHom (idealPowerStageSucc J n)
    (J ^ (n + 1 + 1)).subschemeι (J ^ (n + 1)).subschemeι
    (idealPowerStageSucc_subschemeι J n) (L.pushObj (n + 1))) _

/-- The inverse system on `X` of the direct images of the terms. -/
def pushSystem : ℕᵒᵖ ⥤ X.Modules :=
  Functor.ofOpSequence (X := fun n => L.pushObj n) (fun n => L.pushTransition n)

/-- The direct image of a coherent module on a closed subscheme is coherent. -/
theorem isCoherent_pushObj [IsLocallyNoetherian X] (n : ℕ) :
    _root_.SheafOfModules.IsCoherent.{u} (L.pushObj n) :=
  have := L.isCoherent n
  isCoherent_pushforward_of_isClosedImmersion (J ^ (n + 1)).subschemeι (L.obj n)

/-- The direct image of the `n`-th term is annihilated by `ℐ ⁿ⁺¹`. -/
theorem idealPowerMultiple_pushObj (n : ℕ) :
    idealPowerMultiple J (n + 1) (L.pushObj n) = ⊥ :=
  (Stacks.Algebraization.idealPowerMultiple_eq_bot_iff_affine_smul_top _ _ _).2
    (Stacks.Algebraization.idealPower_smul_pushforward_eq_bot_of_ker J (n + 1)
      (J ^ (n + 1)).subschemeι (Scheme.IdealSheafData.ker_subschemeι _) (L.obj n))

/-- The direct image of a coherent module on a closed subscheme is quasi-coherent. -/
private theorem isQuasicoherent_pushObj [IsLocallyNoetherian X] (n : ℕ) :
    (L.pushObj n).IsQuasicoherent :=
  have := L.isCoherent_pushObj n
  isQuasicoherent_of_isCoherent _

/-- The identification `(ℒₙ₊₁)_* / ℐ ⁿ⁺¹ (ℒₙ₊₁)_* ≅ (ℒₙ)_*` of the quotient of a term with the
previous term: [Stacks, Tag 0EL1] at the closed immersion `Xₙ ⟶ X` followed by
`Stacks.Coherent.IdealPowerStageModules.pushPullbackIso`. -/
def quotientIso [IsLocallyNoetherian X] (n : ℕ) :
    idealPowerQuotient J (n + 1) (L.pushObj (n + 1)) ≅ L.pushObj n :=
  have := L.isCoherent_pushObj (n + 1)
  have : (L.pushObj (n + 1)).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  Stacks.Algebraization.idealQuotientPushforwardIso J (n + 1) (L.pushObj (n + 1))
      (J ^ (n + 1)).subschemeι (Scheme.IdealSheafData.ker_subschemeι _) ≪≫
    (Scheme.Modules.pushforward (J ^ (n + 1)).subschemeι).mapIso (L.pushPullbackIso n)

/-- **The direct images of the terms form a coherent adic system.** -/
theorem isCoherentAdicSystem_pushSystem [IsLocallyNoetherian X] :
    IsCoherentAdicSystem J L.pushSystem := by
  refine ⟨fun n => L.isCoherent_pushObj n, fun n => L.idealPowerMultiple_pushObj n,
    fun n => ⟨L.quotientIso n, ?_⟩⟩
  have := isQuasicoherent_pushObj L (n + 1)
  refine Eq.trans (congrArg (fun z => cokernel.π (C := X.Modules)
      ((idealPowerMultiple J (n + 1) (L.pushObj (n + 1))).ι) ≫ z) (Iso.trans_hom _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫
      (Scheme.Modules.pushforward (J ^ (n + 1)).subschemeι).map (L.pushPullbackIso n).hom)
    (Stacks.Algebraization.idealQuotientPushforwardMap_π J (n + 1) (L.pushObj (n + 1))
      (J ^ (n + 1)).subschemeι (Scheme.IdealSheafData.ker_subschemeι _))) ?_
  exact (L.unit_comp_map_pushPullbackIso n).trans
    (Functor.ofOpSequence_map_homOfLE_succ _ n).symm

/-- The object of `Coh(X, ℐ)` defined by a compatible family of coherent modules on the
closed subschemes cut out by the powers of `ℐ`. -/
def adicSystem [IsLocallyNoetherian X] : CoherentAdicSystems J :=
  ⟨L.pushSystem, L.isCoherentAdicSystem_pushSystem⟩

/-- The `n`-th term of `Stacks.Coherent.IdealPowerStageModules.adicSystem` is the direct image of
`ℒₙ`. -/
theorem adicSystem_obj [IsLocallyNoetherian X] (n : ℕ) :
    L.adicSystem.obj.obj (op n) = L.pushObj n :=
  rfl

/-- **The stalks of the terms are finite free over the stalks of `𝒪_X / ℐ ⁿ⁺¹`.** If every `ℒₙ`
is finite locally free, then at every point `y` the stalk of `(Xₘ ⟶ X)_* ℒₘ` is isomorphic, as an
`𝒪_{X,y}`-module, to `(𝒪_{X,y} / ℐ_y ᵐ⁺¹)ʳ` for some `r`.

The stalk is that of `(ℒₘ₊₁)_* / ℐ ᵐ⁺¹ (ℒₘ₊₁)_*` by
`Stacks.Coherent.IdealPowerStageModules.quotientIso`, which is `M / ℐ_y ᵐ⁺¹ M` for `M` the stalk
of `(ℒₘ₊₁)_*` (`Stacks.Algebraization.idealPowerQuotientStalkLinearEquiv`). On the support of `ℐ`
that quotient is free over `𝒪_{X,y} / ℐ_y ᵐ⁺¹` by
`Stacks.Algebraization.free_quotient_stalk_of_pushforward_iso`; off it the ring
`𝒪_{X,y} / ℐ_y ᵐ⁺¹` is zero. It is finite because `(ℒₘ₊₁)_*` is coherent. -/
theorem exists_stalk_linearEquiv_pi [IsLocallyNoetherian X]
    (hfree : ∀ n, AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree (L.obj n)) (m : ℕ)
    (y : X) :
    ∃ r : ℕ, Nonempty ((modulesStalkFunctor X y).obj (L.pushObj m) ≃ₗ[X.presheaf.stalk y]
      (Fin r → X.presheaf.stalk y ⧸ IdealSheafData.stalk J y ^ (m + 1))) := by
  classical
  have := L.isCoherent_pushObj (m + 1)
  have := isQuasicoherent_pushObj L (m + 1)
  set M := (modulesStalkFunctor X y).obj (L.pushObj (m + 1))
  set R := X.presheaf.stalk y ⧸ IdealSheafData.stalk J y ^ (m + 1)
  let e1 := ((modulesStalkFunctor X y).mapIso (L.quotientIso m)).toLinearEquiv.symm ≪≫ₗ
    (Stacks.Algebraization.idealPowerQuotientStalkLinearEquiv J (m + 1) (L.pushObj (m + 1)) y).symm
  set Q := M ⧸ (IdealSheafData.stalk J y ^ (m + 1) • (⊤ : Submodule (X.presheaf.stalk y) M))
  have hfreeN : Module.Free R Q := by
    by_cases hy : y ∈ J.support
    · exact Stacks.Algebraization.free_quotient_stalk_of_pushforward_iso J (L.pushObj (m + 1))
        (Nat.succ_ne_zero m) hy (L.obj m) (hfree m) (L.quotientIso m)
    · have : Subsingleton R := by
        simp only [R]
        rw [(IdealSheafData.stalk_eq_top_iff_notMem_support J y).mpr hy, Ideal.top_pow]
        exact Ideal.Quotient.subsingleton_iff.mpr rfl
      exact Module.Free.of_subsingleton' _ _
  have : Module.Finite (X.presheaf.stalk y) M :=
    Stacks.Algebraization.finite_modulesStalk_of_isCoherent _ y
  have : Module.Finite R Q :=
    Module.Finite.of_restrictScalars_finite (X.presheaf.stalk y) _ _
  obtain ⟨r, ⟨ψ⟩⟩ := Stacks.FreeStalkQuotient.exists_linearEquiv_pi R Q
  exact ⟨r, ⟨e1.trans (ψ.restrictScalars (X.presheaf.stalk y))⟩⟩

/-- **Restricting an algebraization to the bottom stage.** Let `V ⊆ X` be an open containing
`V(ℐ)` and let `𝒢` be a coherent module on `V` whose completion along `ℐ|_V` is the restriction
to `V` of the system defined by the `ℒₙ`. Then `V(ℐ) ⟶ X` factors through `V`, and the
restriction of `𝒢` to `V(ℐ)` along the factorisation is `ℒ₀`.

The zeroth term of the completion is `𝒢 / ℐ𝒢`, whose restriction to `V(ℐ)` is that of `𝒢`
(`Stacks.Algebraization.isIso_pullback_map_cokernel_π_of_ker`); the zeroth term of the system is
the direct image of `ℒ₀`, whose restriction to `V(ℐ)` is `ℒ₀` because direct image along a closed
immersion is fully faithful (`AlgebraicGeometry.closedImmersionCounitIso`). -/
theorem exists_pullback_iso_of_completion_iso [IsLocallyNoetherian X] (V : X.Opens)
    (hV : Set.range (J ^ (0 + 1)).subschemeι.base ⊆ (V : Set X))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules V.toScheme.ringCatSheaf)
    (e : ((Stacks.Algebraization.completionFunctor V.toScheme (J.comap V.ι)).obj G).obj ≅
      (L.adicSystem.obj ⋙ Scheme.Modules.restrictFunctor V.ι)) :
    ∃ j : (J ^ (0 + 1)).subscheme ⟶ V.toScheme, j ≫ V.ι = (J ^ (0 + 1)).subschemeι ∧
      Nonempty ((Scheme.Modules.pullback j).obj G.obj ≅ L.obj 0) := by
  have hpre : (J ^ (0 + 1)).subschemeι ⁻¹ᵁ V = ⊤ :=
    top_unique fun z _ => hV ⟨z, rfl⟩
  let j : (J ^ (0 + 1)).subscheme ⟶ V.toScheme :=
    (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ hpre).inv ≫ ((J ^ (0 + 1)).subschemeι ∣_ V)
  have hj : j ≫ V.ι = (J ^ (0 + 1)).subschemeι := by
    simp only [j, Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_inv_ι_assoc,
      Scheme.toIso_inv_ι_assoc]
  have hker : j.ker = J.comap V.ι ^ (0 + 1) := by
    simp only [j]
    rw [Scheme.Hom.ker_comp_of_isIso, Scheme.Hom.ker_comp_of_isIso,
      Stacks.GenericFlatness.ker_eq_comap_of_isPullback_of_isOpenImmersion _ _ _ _
        (isPullback_morphismRestrict (J ^ (0 + 1)).subschemeι V),
      Scheme.IdealSheafData.ker_subschemeι, Stacks.IdealSheaf.comap_pow]
  have : IsClosedImmersion (j ≫ V.ι) := by rw [hj]; infer_instance
  have : IsClosedImmersion j := IsClosedImmersion.of_comp j V.ι
  have hπ := Stacks.Algebraization.isIso_pullback_map_cokernel_π_of_ker (J.comap V.ι) (0 + 1)
    G.obj j hker
  refine ⟨j, hj, ⟨asIso ((Scheme.Modules.pullback j).map (cokernel.π (C := V.toScheme.Modules)
      (idealPowerMultiple (J.comap V.ι) (0 + 1) G.obj).ι)) ≪≫
    (Scheme.Modules.pullback j).mapIso
      (eqToIso (Stacks.Algebraization.completionFunctor_obj V.toScheme (J.comap V.ι) G 0).symm ≪≫
        e.app (op 0) ≪≫ (Scheme.Modules.restrictFunctorIsoPullback V.ι).app (L.pushObj 0)) ≪≫
    (Scheme.Modules.pullbackComp j V.ι).app (L.pushObj 0) ≪≫
    (Scheme.Modules.pullbackCongr hj).app (L.pushObj 0) ≪≫
    closedImmersionCounitIso (J ^ (0 + 1)).subschemeι (L.obj 0)⟩⟩

end IdealPowerStageModules

end Stacks.Coherent

end
