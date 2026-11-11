module

public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites
public import StacksFrontier.CategoryTheory.Sites.Presheaf.AlgebraicStructure.AbelianVersusSetsCounterexample

/-!
# `u_p^{ab}` and `u_p` disagree for a morphism of sites

Stacks tag 00YU (Remark 7.44.4) under the remark's standing hypothesis: `u` is a continuous
functor which defines a morphism of sites.  The witness of
`Stacks.Presheaf.AbelianVersusSets.not_bijective_theta_empty` (the empty functor into `PUnit`)
becomes a morphism of sites in the sense of Stacks 00X1 (`CategoryTheory.Functor.IsMorphismOfSites`)
once `PUnit` carries the topology `⊤`, in which the empty family covers the point: continuity is
vacuous because the source category has no objects, and every sheaf of sets for `⊤` is terminal,
so `u_s` is exact.

## Main results

* `Stacks.Presheaf.AbelianVersusSets.exists_isMorphismOfSites_not_bijective_theta`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Presheaf.AbelianVersusSets

/-- **Stacks 00YU (Remark 7.44.4).** Even for a continuous functor defining a morphism of sites,
`u_p^{ab}` need not agree with `u_p` on underlying presheaves of sets: there exist sites
`(C, J)` and `(D, K)`, a continuous functor `u : C ⥤ D` which defines a morphism of sites
(`u_s` exact, Stacks 00X1), a presheaf of abelian groups `F` on `C` and an object `V` of `D`
such that the comparison map `θ_{F,V} : (u_p F^set)(V) → (u_p^{ab} F)(V)` is not a bijection.

The witness is the empty functor from the empty category to the one-point category `PUnit`,
which carries the topology `⊤` in which the empty family covers the point. -/
@[stacks 00YU "Under the remark's hypothesis: a continuous functor defining a morphism of
  sites for which `u_p^{ab}` does not agree with `u_p` on underlying sets."]
theorem exists_isMorphismOfSites_not_bijective_theta :
    ∃ (C D : Type) (_ : SmallCategory C) (_ : SmallCategory D)
      (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u' : C ⥤ D),
      u'.IsMorphismOfSites J K ∧
        ∃ (F : Cᵒᵖ ⥤ AddCommGrpCat.{0}) (V : Dᵒᵖ),
          ¬ Function.Bijective ((theta u' F).app V) := by
  refine ⟨Discrete PEmpty.{1}, PUnit.{1}, inferInstance, inferInstance, ⊤, ⊤,
    Functor.empty _, ?_, ?_⟩
  · have : (Functor.empty PUnit.{1}).IsContinuous (⊤ : GrothendieckTopology (Discrete PEmpty.{1}))
        (⊤ : GrothendieckTopology PUnit.{1}) :=
      ⟨fun _ => by intro X; exact X.as.elim⟩
    refine (Functor.isMorphismOfSites_iff_preservesFiniteLimits _ _ _).2
      ⟨fun _ _ _ => ⟨fun {_} => ⟨fun {_} _ => ⟨?_⟩⟩⟩⟩
    exact
      { lift := fun s => (Sheaf.isTerminalOfEqTop rfl _).from s.pt
        fac := fun _ _ => (Sheaf.isTerminalOfEqTop rfl _).hom_ext _ _
        uniq := fun _ _ _ => (Sheaf.isTerminalOfEqTop rfl _).hom_ext _ _ }
  · exact ⟨{ obj := fun X => X.unop.as.elim
             map := fun {X} => X.unop.as.elim
             map_id := fun X => X.unop.as.elim
             map_comp := fun {X} => X.unop.as.elim },
      Opposite.op PUnit.unit, not_bijective_theta_empty _⟩

end Stacks.Presheaf.AbelianVersusSets
