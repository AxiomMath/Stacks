module

public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.FlasqueComplexDerivedSections

/-!
# Cohomology of a module pushed forward from a point

Let `x : Spec K ⟶ X` be a morphism from the spectrum of a field. Every sheaf on the one-point
space `Spec K` is flasque, hence so is its direct image along `x`; a flasque module has vanishing
higher cohomology ([Stacks, Tag 09SY]). So `Hⁱ(X, x_* N) = 0` for `i > 0`, and more generally for
the direct image along any morphism factoring through `x`.

## Main results

* `Stacks.KunnethLowDegree.isFlasque_pushforward_of_spec_field`: `x_* N` is flasque.
* `Stacks.KunnethLowDegree.isZero_H_pushforward_of_spec_field`: `Hⁱ(X, x_* N) = 0` for `i > 0`.
* `Stacks.KunnethLowDegree.isZero_H_pushforward_pushforward_of_comp_eq`: the same for
  `π_* i_* N` when `i ≫ π` factors through `x`.

## References

* [Stacks Project, Tag 09SY](https://stacks.math.columbia.edu/tag/09SY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.KunnethLowDegree

variable {K : Type u} [Field K] {X : Scheme.{u}} (x : Spec (.of K) ⟶ X)

/-- An open subset of the spectrum of a field is empty or everything. -/
theorem opens_spec_field_eq_bot_or_eq_top (V : (Spec (.of K)).Opens) : V = ⊥ ∨ V = ⊤ := by
  by_cases h : (V : Set (Spec (.of K))).Nonempty
  · right
    obtain ⟨y, hy⟩ := h
    ext z
    simp only [Opens.coe_top, Set.mem_univ, iff_true]
    rwa [Subsingleton.elim z y]
  · left
    ext z
    simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hz => h ⟨z, hz⟩

/-- **The direct image of a module along a morphism out of the spectrum of a field is
flasque.** -/
theorem isFlasque_pushforward_of_spec_field (N : (Spec (.of K)).Modules) :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj ((Scheme.Modules.pushforward x).obj N)) where
  epi {U V} i := by
    let F := (SheafOfModules.toSheaf (Spec (.of K)).ringCatSheaf).obj N
    change Epi (F.obj.map ((Opens.map x.base).map i.unop).op)
    rcases opens_spec_field_eq_bot_or_eq_top ((Opens.map x.base).obj V.unop) with h | h
    · have hz : IsTerminal (F.obj.obj (op ((Opens.map x.base).obj V.unop))) := by
        rw [h]
        exact TopCat.Sheaf.isTerminalOfEmpty F
      exact hz.isZero.epi _
    · have hU : (Opens.map x.base).obj U.unop = ⊤ :=
        top_unique (h ▸ (Opens.map x.base).map i.unop |>.le)
      have hUV : (Opens.map x.base).obj U.unop = (Opens.map x.base).obj V.unop := hU.trans h.symm
      have : IsIso ((Opens.map x.base).map i.unop).op := by
        have : (Opens.map x.base).map i.unop = eqToHom hUV.symm := Subsingleton.elim _ _
        rw [this]
        infer_instance
      infer_instance

/-- **The higher cohomology of a module pushed forward from a point vanishes.** -/
theorem isZero_H_pushforward_of_spec_field (N : (Spec (.of K)).Modules) (i : ℕ) (hi : 0 < i) :
    IsZero (((moduleGlobalSections X).rightDerived i).obj ((Scheme.Modules.pushforward x).obj N)) :=
  Stacks.Cech.Flasque.isZero_rightDerived_evaluation_of_isFlasque X.toTopCat X.ringCatSheaf ⊤ _
    (isFlasque_pushforward_of_spec_field x N) i hi

/-- **The higher cohomology of a module pushed forward along a morphism factoring through a point
vanishes**: if `i ≫ π = g ≫ x` with `x` out of the spectrum of a field, then
`Hⁿ(X, π_* i_* N) = 0` for `n > 0`. -/
theorem isZero_H_pushforward_pushforward_of_comp_eq {Z T : Scheme.{u}} (i : Z ⟶ T) (π : T ⟶ X)
    (g : Z ⟶ Spec (.of K)) (h : i ≫ π = g ≫ x) (N : Z.Modules) (n : ℕ) (hn : 0 < n) :
    IsZero (((moduleGlobalSections X).rightDerived n).obj
      ((Scheme.Modules.pushforward π).obj ((Scheme.Modules.pushforward i).obj N))) :=
  (isZero_H_pushforward_of_spec_field x ((Scheme.Modules.pushforward g).obj N) n hn).of_iso
    (((moduleGlobalSections X).rightDerived n).mapIso
      ((Scheme.Modules.pushforwardComp i π).app N ≪≫
        (Scheme.Modules.pushforwardCongr h).app N ≪≫
        ((Scheme.Modules.pushforwardComp g x).app N).symm))

end Stacks.KunnethLowDegree

end
