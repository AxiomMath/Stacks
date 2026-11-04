module

public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.Stalks
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# The germs of a trivializing family of sections are a basis of the stalk

Let `O_X` be a sheaf of rings on a topological space `X` and let `F` be a sheaf of
`O_X`-modules. A family `s : I → F.sections` of global sections determines a morphism
`F.freeHomEquiv.symm s` from the free sheaf of modules on `I`, and the family *trivializes* `F`
when that morphism is an isomorphism. This file records the consequence on stalks: the germs of
the `s i` at a point `x` form an `O_{X,x}`-basis of the stalk `F_x`.

The case `F = SheafOfModules.free I`, `s = SheafOfModules.freeSection`, is the statement that
the stalk of a free sheaf of modules is free *on the germs of its own tautological sections* —
as opposed to being abstractly isomorphic to `I →₀ O_{X,x}`, which is what
`LocallyFreeRank.Trivialization.stalk_free_linearEquiv` says.

## Main results

* `Stacks.SheafOfModules.exists_stalkBasis_germ_freeSection`: the germs at `x` of the
  tautological sections of `SheafOfModules.free I` are an `O_{X,x}`-basis of its stalk at `x`.
* `Stacks.SheafOfModules.exists_stalkBasis_of_generatingSections`: the same for the generating
  sections of any sheaf of modules whose generating morphism from a free sheaf is an
  isomorphism.
* `Stacks.SheafOfModules.exists_bijective_sum_smul_germ_of_isIso_freeHom`: the same fact in the
  form `(c i) ↦ ∑ i, c i • germ (s i)` is bijective, for a finite index type. This is the shape
  a stalkwise bijectivity argument consumes, and the rank-one case of it is the hypothesis
  `hbasis` of `Stacks.SheafOfModules.TensorStalkRingedSpace.bijective_stalkMapL_of_germ_basis`.

## Implementation notes

The mathematics is already in `StacksFrontier/AlgebraicGeometry/Cohomology/GlobalGeneration/`:
`AlgebraicGeometry.freeStalkLinearEquiv` identifies the stalk of the free sheaf with
`I →₀ O_{X,x}` (via `AlgebraicGeometry.SheafOfModules.stalkFunctor` preserving the coproduct
presentation of the free sheaf, which is Tag 01AH), and
`AlgebraicGeometry.freeHom_stalk_single_germ` computes where the basis vectors go. Both are
`private` to that module, so the basis itself is packaged there by
`AlgebraicGeometry.exists_stalkBasis_of_isIso_freeHom`; everything below is specialization of
that one statement.

Each statement is an existential over a `Module.Basis` whose members are then named. That is
not a weakening: a `Module.Basis` is determined by the family of its members, so pinning the
members pins the basis.

## References

* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Tag 01AN](https://stacks.math.columbia.edu/tag/01AN)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Limits Opposite

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
  {I : Type u}

/-- **The germs of the generating sections of a free sheaf of modules are a basis of its
stalk.** The germs at `x` of the tautological sections `SheafOfModules.freeSection i` of
`SheafOfModules.free I` form an `O_{X,x}`-basis of the stalk of `SheafOfModules.free I` at `x`.

The generating morphism is the identity here — `SheafOfModules.freeSection` is by definition
the image of `𝟙 (free I)` under `SheafOfModules.freeHomEquiv` — so the hypothesis of
`AlgebraicGeometry.exists_stalkBasis_of_isIso_freeHom` is satisfied for free. -/
theorem exists_stalkBasis_germ_freeSection (I : Type u) (x : X) :
    ∃ b : Module.Basis I ((TopCat.Presheaf.stalk O.obj x : RingCat) : Type u)
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor O x).obj
          (_root_.SheafOfModules.free I) : Type u),
      ∀ i : I, b i =
        (TopCat.Presheaf.Γgerm
            (_root_.SheafOfModules.free (R := O) I).val.presheaf x).hom
          ((_root_.SheafOfModules.freeSection i).eval (op ⊤)) := by
  have hid : (_root_.SheafOfModules.free (R := O) I).freeHomEquiv.symm
      (fun i => _root_.SheafOfModules.freeSection i) = 𝟙 _ :=
    Equiv.symm_apply_apply _ _
  have : IsIso ((_root_.SheafOfModules.free (R := O) I).freeHomEquiv.symm
      (fun i => _root_.SheafOfModules.freeSection i)) := by
    rw [hid]; infer_instance
  exact AlgebraicGeometry.exists_stalkBasis_of_isIso_freeHom O
    (_root_.SheafOfModules.free I) (fun i => _root_.SheafOfModules.freeSection i) x

/-- **The germs of a generating family that presents a sheaf of modules as a free one are a
basis of every stalk.** If `σ : M.GeneratingSections` has `σ.π` an isomorphism — which is
exactly the condition `SheafOfModules.LocalGeneratorsData.IsLocallyFreeData` imposes on each
member of a trivializing cover — then the germs of `σ.s` at any point `x` form an
`O_{X,x}`-basis of the stalk `M_x`. -/
theorem exists_stalkBasis_of_generatingSections {M : _root_.SheafOfModules.{u} O}
    (σ : M.GeneratingSections) [IsIso σ.π] (x : X) :
    ∃ b : Module.Basis σ.I ((TopCat.Presheaf.stalk O.obj x : RingCat) : Type u)
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor O x).obj M : Type u),
      ∀ i : σ.I, b i =
        (TopCat.Presheaf.Γgerm M.val.presheaf x).hom ((σ.s i).eval (op ⊤)) :=
  AlgebraicGeometry.exists_stalkBasis_of_isIso_freeHom O M σ.s x

/-- **A trivializing family of finitely many sections gives a bijection on the stalk.** For a
finite index type, the statement that the germs of `s` form a basis of the stalk at `x`, in the
form that the map sending a family of scalars `c` to `∑ i, c i • germ (s i)` is a bijection.

At a one-element index type this is the hypothesis `hbasis` of
`Stacks.SheafOfModules.TensorStalkRingedSpace.bijective_stalkMapL_of_germ_basis`. -/
theorem exists_bijective_sum_smul_germ_of_isIso_freeHom [Fintype I]
    {M : _root_.SheafOfModules.{u} O} (s : I → M.sections)
    [IsIso (M.freeHomEquiv.symm s)] (x : X) :
    Function.Bijective fun c : I → ((TopCat.Presheaf.stalk O.obj x : RingCat) : Type u) =>
      ∑ i : I, c i •
        (TopCat.Presheaf.Γgerm M.val.presheaf x).hom ((s i).eval (op ⊤)) := by
  obtain ⟨b, hb⟩ := AlgebraicGeometry.exists_stalkBasis_of_isIso_freeHom O M s x
  have hfun : (fun c : I → ((TopCat.Presheaf.stalk O.obj x : RingCat) : Type u) =>
      ∑ i : I, c i •
        (TopCat.Presheaf.Γgerm M.val.presheaf x).hom ((s i).eval (op ⊤)))
      = b.equivFun.symm := by
    funext c
    rw [b.equivFun_symm_apply]
    exact Finset.sum_congr rfl fun i _ => (congrArg (fun m => c i • m) (hb i)).symm
  rw [hfun]
  exact b.equivFun.symm.bijective

end Stacks.SheafOfModules

end
