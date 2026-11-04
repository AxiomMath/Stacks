module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.Defs
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalFiniteFreeSummand
import StacksCore.Tactic.StacksAttribute

/-!
# A module with a left dual is locally a finite free summand

Let `(X, O_X)` be a ringed space and let `F` be a sheaf of `O_X`-modules admitting a left
dual `G` in the monoidal category of `O_X`-modules. Stacks 0FNW (1) asserts that `F` is then
locally a direct summand of a finite free `O_X`-module.

This is the ringed-space case of the site-level
`Stacks.SheafOfModules.exists_cover_retract_finiteFree_of_exactPairing` (Stacks 0FNZ):
that theorem produces, for each object of the site, a covering on whose members `F` is a
retract of a free module on a finite index type, and here it is applied to the top open and
the covering is read as a neighbourhood of each point, with the index type re-indexed by
`Fin n`.

## Main results

* `Stacks.SheafOfModules.isLocallyFiniteFreeSummand_of_exactPairing`: Stacks 0FNW (1).

## Implementation notes

The monoidal structure is supplied as an explicit parameter `M` together with equations
pinning it to the concrete sheaf constructions, rather than taken from an instance, because
the category of sheaves of modules carries no global monoidal instance for the sheafified
tensor product. Six such equations are required: the unit and the tensor product on objects
and on morphisms, and the action of the associator and of **both** unitors on local pure
tensors.

The last three — `_hassociator`, `_hleftUnitor`, `_hrightUnitor` — come from the restatement of
Stacks 0FNZ with three coherence hypotheses (the associator and both unitors): the triangle
identity reassociates and then converts both ends to scalar multiplication. They are satisfied
in the setting the source works in: there the monoidal structure is the one of Stacks 01CA, whose
associator and unitors
are induced by those of the presheaf tensor product and so act on a local pure tensor exactly
as these equations say. Requiring them is therefore making explicit what the source leaves
implicit in the phrase "the monoidal category of `O_X`-modules", not a restriction of the
statement.

The hypotheses use the native `Stacks.SheafOfModules.Tensor.sheafTensor` and its component
and inner maps. This tensor product sheaf is the sheafification of the presheaf tensor product,
specialized here from a general ringed site to a ringed space.

`Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩` and
`structureSheafRing X` are the same sheaf of rings on
  the nose; both are the structure presheaf composed with
`forget₂ CommRingCat RingCat`, packaged with a proof of its sheaf condition. The sheaf condition
is therefore written throughout as the projection `(structureSheafRing X).property`; no named
lemma restates it, and which proof of it is supplied is irrelevant, since it is a proposition.
Being the same only up to that proof, the two spellings are interchangeable at default
transparency but not at the one instance search uses, so the monoidal structure `M` is seated
once at each spelling and the retract produced by Stacks 0FNZ is read back at the
`structureSheafRing` spelling; both are ascriptions of one term to two defeq types.

## References

* [Stacks Project, Tag 0FNW](https://stacks.math.columbia.edu/tag/0FNW)
* [Stacks Project, Tag 0FNZ](https://stacks.math.columbia.edu/tag/0FNZ)
-/

@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace

namespace Stacks.SheafOfModules

universe u

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- **Stacks Project, Tag 0FNW (1).** A sheaf of modules on a ringed space admitting a left
dual in the monoidal category of module sheaves is locally a direct summand of a finite free
module. -/
theorem isLocallyFiniteFreeSummand_of_exactPairing
    (F G : SheafOfModules.{u} (structureSheafRing X))
    (M : MonoidalCategory (SheafOfModules.{u}
      (structureSheafRing X))) :
    letI := M
    letI : MonoidalCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩)) := M
    ∀ (hunit : 𝟙_ (SheafOfModules.{u}
      (structureSheafRing X)) =
          SheafOfModules.unit (structureSheafRing X))
      (htensor : ∀ A B : SheafOfModules.{u}
        (structureSheafRing X),
          A ⊗ B = ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.presheaf, X.IsSheaf⟩).obj A).obj B)
      (_htensorMap : ∀ {A A' B B' : SheafOfModules.{u}
        (structureSheafRing X)}
          (f : A ⟶ A') (g : B ⟶ B'),
          eqToHom (htensor A B).symm ≫ (f ⊗ₘ g) ≫ eqToHom (htensor A' B') =
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨X.presheaf, X.IsSheaf⟩).map f).app B ≫
                ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                  ⟨X.presheaf, X.IsSheaf⟩).obj A').map g)
      (_hassociator : ∀ (A B D : SheafOfModules.{u}
        (structureSheafRing X))
          (V : (Opens X.carrier)ᵒᵖ) (a : A.val.obj V) (b : B.val.obj V) (c : D.val.obj V),
          (α_ A B D).hom.val.app V
              (tensorSection X.presheaf (structureSheafRing X).property htensor
                (A ⊗ B) D V
                (tensorSection X.presheaf (structureSheafRing X).property htensor A B V a b)
                c) =
            tensorSection X.presheaf (structureSheafRing X).property htensor A (B ⊗ D) V a
              (tensorSection X.presheaf (structureSheafRing X).property htensor B D V b c))
      (_hleftUnitor : ∀ (A : SheafOfModules.{u}
        (structureSheafRing X))
          (V : (Opens X.carrier)ᵒᵖ)
          (r : (structureSheafRing X).obj.obj V) (a :
            A.val.obj V),
          (λ_ A).hom.val.app V
              (tensorSection X.presheaf (structureSheafRing X).property htensor _ A V
                (unitTensorSection X.presheaf (structureSheafRing X).property hunit V r) a) =
            r • a)
      (_hrightUnitor : ∀ (A : SheafOfModules.{u}
        (structureSheafRing X))
          (V : (Opens X.carrier)ᵒᵖ) (a : A.val.obj V)
          (r : (structureSheafRing X).obj.obj V),
          (ρ_ A).hom.val.app V
              (tensorSection X.presheaf (structureSheafRing X).property htensor A _ V a
                (unitTensorSection X.presheaf (structureSheafRing X).property hunit V r)) =
            r • a)
      (_p : ExactPairing F G),
      IsLocallyFiniteFreeSummand X F := by
  intro hunit htensor htensorMap hassociator hleftUnitor hrightUnitor p
  obtain ⟨S, hS, hlocal⟩ :=
    exists_cover_retract_finiteFree_of_exactPairing X.presheaf
      (structureSheafRing X).property F G M hunit htensor htensorMap hassociator
      hleftUnitor hrightUnitor p ⊤
  intro x
  rw [Opens.mem_grothendieckTopology] at hS
  obtain ⟨U, i, hi, hxU⟩ := hS x (by simp)
  obtain ⟨I, hfinite, ⟨r₀⟩⟩ := hlocal U i hi
  have r : Retract (F.over U)
      (SheafOfModules.free (R := (structureSheafRing X).over U) I) := r₀
  let _ : Fintype I := Fintype.ofFinite I
  refine ⟨U, hxU, Fintype.card I, ⟨?_⟩⟩
  let e : I ≃ ULift.{u} (Fin (Fintype.card I)) :=
    (Fintype.equivFin I).trans Equiv.ulift.symm
  let eFree :
      SheafOfModules.free (R := (structureSheafRing
        X).over U) I ≅
        SheafOfModules.free (R := (structureSheafRing
          X).over U)
          (ULift.{u} (Fin (Fintype.card I))) :=
    (SheafOfModules.freeFunctor
      (R := (structureSheafRing X).over U)).mapIso
        (Equiv.toIso e)
  exact ⟨r.i ≫ eFree.hom, eFree.inv ≫ r.r, by
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact r.retract⟩

end Stacks.SheafOfModules
