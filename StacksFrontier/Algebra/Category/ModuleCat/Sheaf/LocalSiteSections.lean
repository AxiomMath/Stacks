module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeOfIntRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitEndomorphisms

/-!
# Sheaves of modules on a site whose terminal object has only trivial coverings

Let `T` be a terminal object of a site such that every covering sieve of `T` contains the
identity. Then the global sections functor is exact: an epimorphism of sheaves is locally
surjective, and a covering of `T` has the identity as a member. Equivalently, the structure sheaf
is a projective sheaf of modules. Moreover a sheaf of modules which is locally free of rank `r`
has global sections free of rank `r`: some member of a trivialising covering admits a section
over `T`.

## Main results

* `Stacks.SheafOfModules.projective_unit_of_mem`: the structure sheaf is projective.
* `Stacks.SheafOfModules.homModuleUnitEquivSections`: `Hom(O, M) ≅ M(T)` as `O(T)`-modules.
* `Stacks.SheafOfModules.finrank_homModule_of_isFiniteLocallyFreeOfIntRank`: for `M` locally free
  of rank `r`, `r ≥ 0` and `Hom(O, M)` is free of rank `r` over `O(T)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v₁ u₁

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u}) [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {T : C} (hT : IsTerminal T) (hloc : ∀ R ∈ J T, R.arrows (𝟙 T))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
include hT hloc in
/-- **On a site whose terminal object has only trivial coverings, the structure sheaf is a
projective sheaf of modules**: a global section of the target of an epimorphism lifts over a
covering of the terminal object, which contains the identity. -/
theorem projective_unit_of_mem :
    Projective (_root_.SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf O))) where
  factors {M N} f g hg := by
    let eM := FiniteTypeKernel.sectionsEquivOfTerminal M hT
    let eN := FiniteTypeKernel.sectionsEquivOfTerminal N hT
    obtain ⟨S, hS, hlift⟩ := EpiMono.exists_covering_of_epi g (eN (N.unitHomEquiv f))
    obtain ⟨t, ht⟩ := hlift (𝟙 T) (hloc S hS)
    let t' : M.val.obj (op T) := t
    refine ⟨M.unitHomEquiv.symm (eM.symm t'), ?_⟩
    apply N.unitHomEquiv.injective
    apply eN.injective
    rw [_root_.SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply]
    show (g.val.app (op T)).hom (eM (eM.symm t')) = _
    rw [Equiv.apply_symm_apply]
    exact ht.trans (by simp only [op_id, CategoryTheory.Functor.map_id]; rfl)

end Stacks.SheafOfModules

end
