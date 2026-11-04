module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible

/-!
# The internal hom out of a locally free sheaf of finite rank into a sheaf locally constant of
finite type

Let `F` be a sheaf of `Λ`-modules which is locally the constant sheaf on a finite free
`Λ`-module, and `G` a sheaf of `Λ`-modules which is locally constant of finite type
(`Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant`, Tag 03RW). Then the internal hom
`SheafHom_Λ(F, G)` is again locally constant of finite type: on a common refinement of the two
coverings it is the constant sheaf on `Hom_Λ(M, N)` (as in Tag 093T (3),
`Stacks.ConstantSheaf.isLocallyConstant_moduleSheafHom`), and `Hom_Λ(M, N)` is a finite
`Λ`-module when `M` is finite free and `N` is finite.

## Main definitions

* `Stacks.ConstantSheaf.IsFreeFiniteLocallyConstantModuleSheaf`.

## Main results

* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_moduleSheafHom`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v w x

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (Λ : Type w) [CommRing Λ]

/-- A sheaf of `Λ`-modules is *locally constant on a finite free module* when every object of
the site has a covering on each member of which it is the constant sheaf on a finite free
`Λ`-module. -/
def IsFreeFiniteLocallyConstantModuleSheaf (F : Sheaf J (ModuleCat.{max u v x} Λ)) : Prop :=
  ∀ U : C, ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
    Sieve.ofArrows V f ∈ J U ∧ ∀ i,
      ∃ E : ModuleCat.{max u v x} Λ, Module.Free Λ E ∧ Module.Finite Λ E ∧
        Nonempty ((constantSheaf (J.over (V i)) (ModuleCat.{max u v x} Λ)).obj E ≅
          (J.overPullback (ModuleCat.{max u v x} Λ) (V i)).obj F)

/-- **The internal hom out of a sheaf locally constant on a finite free module into a sheaf
locally constant of finite type is locally constant of finite type.** -/
theorem isFiniteTypeLocallyConstant_moduleSheafHom (F G : Sheaf J (ModuleCat.{max u v x} Λ))
    (hF : IsFreeFiniteLocallyConstantModuleSheaf J Λ F)
    (hG : IsFiniteTypeLocallyConstant Λ J G) :
    IsFiniteTypeLocallyConstant Λ J (moduleSheafHom J Λ F G) := by
  intro U
  obtain ⟨I, V, f, hf, hFV⟩ := hF U
  obtain ⟨I', W, g, hg, hGW⟩ := hG U
  obtain ⟨K, Z, p, hp⟩ := (Sieve.ofArrows V f ⊓ Sieve.ofArrows W g).exists_eq_ofArrows
  refine ⟨K, Z, p, hp ▸ J.intersection_covering hf hg, fun k => ?_⟩
  have hk : (Sieve.ofArrows V f ⊓ Sieve.ofArrows W g) (p k) := by
    rw [hp]; exact Sieve.ofArrows_mk Z p k
  obtain ⟨i, a, -⟩ := (Sieve.mem_ofArrows_iff V f (p k)).mp hk.1
  obtain ⟨j, b, -⟩ := (Sieve.mem_ofArrows_iff W g (p k)).mp hk.2
  obtain ⟨M, hMf, hMt, ⟨eF⟩⟩ := hFV i
  obtain ⟨N, hN, ⟨eG⟩⟩ := hGW j
  have : ∀ Y : Over (Z k),
      HasSheafify ((J.over (Z k)).over Y) (ModuleCat.{max u v x} Λ) := fun Y =>
    hasSheafify_over_moduleCat.{max u v, v, w, x} (J.over (Z k)) Λ Y
  have := hMf
  have := hMt
  have : Module.FinitePresentation Λ M := Module.finitePresentation_of_projective _ _
  have hMN : Module.Finite Λ (M ⟶ N) := by
    have : Module.Finite Λ N := hN
    exact Module.Finite.equiv (ModuleCat.homLinearEquiv (S := Λ)).symm
  exact ⟨ModuleCat.of Λ (M ⟶ N), hMN,
    ⟨constantSheafHomIsoOfHom (J.over (Z k)) Λ M N ≪≫
      (moduleSheafHomMapIso (J.over (Z k)) Λ
        (overPullbackIsoOfMapModule J a F M eF)
        (overPullbackIsoOfMapModule J b G N eG)) ≪≫
      (overPullbackModuleSheafHomIso J Λ (Z k) F G).symm⟩⟩

end Stacks.ConstantSheaf

end
