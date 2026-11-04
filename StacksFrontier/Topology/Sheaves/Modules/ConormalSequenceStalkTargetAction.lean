module

public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksFrontier.Topology.Sheaves.Modules.ConormalSheafStalk
public import StacksFrontier.Topology.Sheaves.Modules.TensorDifferentialsSheafStalk

/-!
# The two actions on the stalk of a term of the conormal sequence

Let `φ : A ⟶ B` be a locally surjective morphism of sheaves of commutative rings on a
topological space `X` and let `x` be a point of `X`.  The stalks at `x` of the terms `I/I²` and
`B ⊗[A] Ω[A/R]` of the conormal sequence of `φ` carry two actions: one of the stalk of the sheaf
of rings underlying `B`, and one of the stalk `Aₓ`
(`Stacks.Sites.Conormal.moduleStalkConormalSheaf`,
`Stacks.Sites.Conormal.moduleStalkTensorDifferentialsSheaf`).  The action of `Aₓ` is the action
of the image of its scalar under the stalk `Aₓ → Bₓ` of `φ`, read through
`SemilinearStalk.commStalkRingEquiv`.

## Main results

* `AlgebraicGeometry.SheafOfModules.exists_germ_eq_pair`: a scalar in the stalk of a presheaf of
  commutative rings and an element of the stalk of a presheaf of abelian groups are germs of
  sections over a *common* open neighbourhood.
* `Stacks.Sites.Conormal.conormalSheafStalk_ringCat_smul_eq` and
  `Stacks.Sites.Conormal.tensorDifferentialsSheafStalk_ringCat_smul_eq`: **the two actions
  agree.**

## References

* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.SheafOfModules

/-! ### Germs over a common neighbourhood -/

/-- **A scalar and a vector in a pair of stalks are germs over a common open.**  An element `b`
of the stalk of `R` at `z` and an element `w` of the stalk of `P` at `z` are the germs of sections
`r` and `m` over one open neighbourhood `U` of `z`. -/
theorem exists_germ_eq_pair {T : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} T)
    (P : TopCat.Presheaf AddCommGrpCat.{u} T) (z : T) (b : ToType (TopCat.Presheaf.stalk R z))
    (w : ToType (TopCat.Presheaf.stalk P z)) :
    ∃ (U : Opens T) (hz : z ∈ U) (r : ToType (R.obj (op U))) (m : ToType (P.obj (op U))),
      (TopCat.Presheaf.germ R U z hz).hom r = b ∧
        (TopCat.Presheaf.germ P U z hz).hom m = w := by
  obtain ⟨U₁, h₁, r₀, hr⟩ := TopCat.Presheaf.exists_germ_eq R b
  obtain ⟨U₂, h₂, m₀, hm⟩ := TopCat.Presheaf.exists_germ_eq P w
  refine ⟨U₁ ⊓ U₂, ⟨h₁, h₂⟩, (R.map (homOfLE inf_le_left).op).hom r₀,
    (P.map (homOfLE inf_le_right).op).hom m₀, ?_, ?_⟩
  · exact Eq.trans (TopCat.Presheaf.germ_res_apply R (homOfLE inf_le_left) z ⟨h₁, h₂⟩ r₀) hr
  · exact Eq.trans (TopCat.Presheaf.germ_res_apply P (homOfLE inf_le_right) z ⟨h₁, h₂⟩ m₀) hm

end AlgebraicGeometry.SheafOfModules

namespace Stacks.Sites.Conormal

open AlgebraicGeometry.SheafOfModules (exists_germ_eq_pair)

/-- **The two stalk actions agree on any sheaf of modules over `B`.**  A scalar of `Aₓ` acts on
the stalk of `M`, viewed over `A` by restriction of scalars along `A ⟶ A/I ⟶ B`, as its image in
`Bₓ` does. -/
private theorem stalk_smul_eq_ringCat_smul {X : TopCat.{u}}
    (A B : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (φ : A ⟶ B)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ.hom] (x : X)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B))
    (r : ToType (TopCat.Presheaf.stalk A.obj x))
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x)) :
    letI : Module (ToType (TopCat.Presheaf.stalk A.obj x))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x)) :=
      inferInstanceAs (Module (ToType (TopCat.Presheaf.stalk A.obj x))
        (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          ((PresheafOfModules.restrictScalars (toQuotientRingHom φ.hom)).obj
            ((PresheafOfModules.restrictScalars
              (quotientToRingSheaf (Opens.grothendieckTopology X) A B φ)).obj
              ((_root_.SheafOfModules.forget _).obj M))).presheaf x)))
    r • ξ = (show ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x) from
        (SemilinearStalk.commStalkRingEquiv B.obj x).symm
          (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ.hom).hom r)) • ξ := by
  obtain ⟨U, hU, r₀, ξ₀, rfl, rfl⟩ := exists_germ_eq_pair A.obj M.val.presheaf x r ξ
  refine Eq.trans (PresheafOfModules.germ_smul
    ((PresheafOfModules.restrictScalars (toQuotientRingHom φ.hom)).obj
      ((PresheafOfModules.restrictScalars
        (quotientToRingSheaf (Opens.grothendieckTopology X) A B φ)).obj
        ((_root_.SheafOfModules.forget _).obj M))) x U hU r₀ ξ₀).symm ?_
  refine Eq.trans (PresheafOfModules.germ_ringCat_smul M.val x U hU
    ((φ.hom.app (op U)).hom r₀) ξ₀) ?_
  refine congrArg (fun t : ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x) =>
    t • (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf U x hU).hom ξ₀) ?_
  refine (((SemilinearStalk.commStalkRingEquiv B.obj x).symm_apply_eq).mpr ?_).symm
  exact Eq.trans (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hU φ.hom r₀)
    (SemilinearStalk.commStalkRingEquiv_germ B.obj x U hU ((φ.hom.app (op U)).hom r₀)).symm

/-! ### The two actions on the stalk of the conormal sheaf -/

section Conormal

variable {X : TopCat.{u}} (A B : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    CommRingCat.{u}) (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ.hom] (x : X)

/-- **The two actions on the stalk of the conormal sheaf agree.**  The action of a scalar `r` of
the stalk `Aₓ` is the action of the image of `r` under the stalk `Aₓ → Bₓ` of `φ`, read through
`SemilinearStalk.commStalkRingEquiv` as a scalar of the stalk of the sheaf of rings underlying
`B`. -/
theorem conormalSheafStalk_ringCat_smul_eq (r : ToType (TopCat.Presheaf.stalk A.obj x))
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (conormalSheaf (Opens.grothendieckTopology X) A B φ).val.presheaf x)) :
    r • ξ = (show ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x) from
        (SemilinearStalk.commStalkRingEquiv B.obj x).symm
          (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ.hom).hom r)) • ξ := by
  exact stalk_smul_eq_ringCat_smul A B φ x _ r ξ

end Conormal

/-! ### The two actions on the stalk of the tensor-differentials sheaf -/

section Tensor

variable {X : TopCat.{u}} (R A B : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    CommRingCat.{u}) (a : R ⟶ A) (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ.hom] (x : X)

/-- **The two actions on the stalk of `B ⊗[A] Ω[A/R]` agree.**  The action of a scalar `r` of the
stalk `Aₓ` is the action of the image of `r` under the stalk `Aₓ → Bₓ` of `φ`, read through
`SemilinearStalk.commStalkRingEquiv`. -/
theorem tensorDifferentialsSheafStalk_ringCat_smul_eq
    (r : ToType (TopCat.Presheaf.stalk A.obj x))
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ).val.presheaf x)) :
    r • ξ = (show ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x) from
        (SemilinearStalk.commStalkRingEquiv B.obj x).symm
          (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ.hom).hom r)) • ξ := by
  exact stalk_smul_eq_ringCat_smul A B φ x _ r ξ

end Tensor

end Stacks.Sites.Conormal

end

end
