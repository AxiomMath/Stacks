module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk

/-!
# A coherent module with a free stalk is finite free near that point

Let `X` be a locally Noetherian scheme and let `M` be a coherent `𝒪_X`-module. If the stalk
`M_x` is a free `𝒪_{X,x}`-module, then `M` is isomorphic to a finite free module after
restriction to some open neighbourhood of `x`. Coherence enters twice: through finite type, which
makes the stalk a finite module and hence free of some finite rank `r`, and through finite
presentation, which is the hypothesis of [Stacks, Tag 0B8J] spreading a basis of the stalk out to
a neighbourhood.

Quantifying over the point turns the statement into finite local freeness: a coherent module all
of whose stalks are free is finite locally free. This is the implication (2) ⟹ (4) of
[Stacks, Tag 05P2] in the presence of coherence, and the hypothesis is pointwise, so no global
rank or constancy input is needed.

## Main results

* `AlgebraicGeometry.Scheme.Modules.exists_free_restrict_of_free_stalk`: a coherent module whose
  stalk at `x` is free is free of some finite rank on an open neighbourhood of `x`.
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_forall_free_stalk`: a coherent module
  with free stalks is finite locally free.

## Implementation notes

The stalk of the structure sheaf is spelled twice and the two spellings have to be bridged.
Freeness of the stalk is given over `↑(X.presheaf.stalk x)`, the filtered colimit taken in
`CommRingCat`, while [Stacks, Tag 0B8J] phrases its hypothesis over the same colimit taken in
`RingCat`. These are different types, identified by
`Stacks.SemilinearStalk.commStalkRingEquiv`, whose compatibility with the two scalar actions on
the stalk of the module is `Stacks.SemilinearStalk.comm_smul_eq`. Reading the identity of the
stalk as a semilinear equivalence along that ring equivalence transports freeness and finiteness
from one spelling to the other, after which a chosen basis gives the linear equivalence with
finitely supported functions that Tag 0B8J consumes.

The two ways of restricting a module to an open live in different categories —
`M.over W` over the sliced sheaf of rings and `M.restrict W.ι` over the structure sheaf of the
open subscheme — and `Stacks.Modules.restrictIsoFree` is the passage between the corresponding
trivialisations.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **A coherent module on a locally Noetherian scheme whose stalk at a point is free is finite
free on a neighbourhood of that point.** This is [Stacks, Tag 0B8J] with the freeness and
finiteness of the stalk supplied by coherence: the stalk is a finite module, so a free stalk is
free of some finite rank `r`, and coherence also gives the finite presentation that Tag 0B8J
requires. -/
theorem exists_free_restrict_of_free_stalk {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) (hM : _root_.SheafOfModules.IsCoherent.{u} M) (x : X)
    (h : Module.Free (X.presheaf.stalk x)
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj M)) :
    ∃ (W : X.Opens) (_ : x ∈ W) (r : ℕ),
      Nonempty (M.restrict W.ι ≅ _root_.SheafOfModules.free.{u} (ULift.{u} (Fin r))) := by
  classical
  have := hM
  have : _root_.SheafOfModules.IsFiniteType.{u, u, u} M :=
    _root_.SheafOfModules.IsCoherent.isFiniteType (M := M)
  let A := ToType (X.presheaf.stalk x)
  let B := ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
    (X.sheaf.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x)
  let N := ToType (M.presheaf.stalk x)
  let : Module A N :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) M.val x
  let : Module B N :=
    PresheafOfModules.instModuleCarrierStalkRingCatCarrierAbPresheafOpensCarrier M.val x
  let : Module.Finite A N := _root_.SheafOfModules.finite_stalk X.sheaf M x
  let : Module.Free A N := h
  let eBA : B ≃+* A := SemilinearStalk.commStalkRingEquiv X.sheaf.obj x
  let eAB := eBA.symm
  let : RingHomInvPair (↑eAB : A →+* B) (↑eBA : B →+* A) := RingHomInvPair.of_ringEquiv eAB
  let : RingHomInvPair (↑eBA : B →+* A) (↑eAB : A →+* B) := RingHomInvPair.of_ringEquiv eBA
  have hsmul (t : B) (n : N) : eBA t • n = t • n :=
    SemilinearStalk.comm_smul_eq X.sheaf.obj x M.val t n
  let eN : N ≃ₛₗ[(↑eAB : A →+* B)] N :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' a n :=
        calc
          a • n = eBA (eAB a) • n := by rw [RingEquiv.apply_symm_apply]
          _ = eAB a • n := hsmul (eAB a) n }
  let : Module.Free B N := Module.Free.of_equiv eN
  let : Module.Finite B N :=
    Module.Finite.of_surjective (R := A) (S := B) (M := N) (P := N)
      (σ := (↑eAB : A →+* B)) eN eN.surjective
  let I := Module.Free.ChooseBasisIndex B N
  let : Fintype I := Fintype.ofFinite _
  let r := Fintype.card I
  let e := (Fintype.equivFin I).trans Equiv.ulift.symm
  obtain ⟨W, hxW, ⟨eW⟩⟩ := Stacks.SheafOfModules.exists_iso_free_over_of_stalk_iso_free M
    (isFinitePresentation_of_isCoherent M) x r ⟨((Module.Free.chooseBasis B N).reindex e).repr⟩
  exact ⟨W, hxW, r, ⟨Stacks.Modules.restrictIsoFree W M (ULift.{u} (Fin r)) eW.symm⟩⟩

/-- **A coherent module on a locally Noetherian scheme all of whose stalks are free is finite
locally free.** Finite local freeness is a pointwise condition, so this is
`AlgebraicGeometry.Scheme.Modules.exists_free_restrict_of_free_stalk` applied at every point;
it is the implication (2) ⟹ (4) of [Stacks, Tag 05P2] with coherence in place of finite
presentation. -/
theorem isFiniteLocallyFree_of_forall_free_stalk {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) (hM : _root_.SheafOfModules.IsCoherent.{u} M)
    (h : ∀ x : X, Module.Free (X.presheaf.stalk x)
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj M)) :
    IsFiniteLocallyFree M := fun x => by
  obtain ⟨W, hxW, r, e⟩ := exists_free_restrict_of_free_stalk M hM x (h x)
  exact ⟨W, hxW, ULift.{u} (Fin r), inferInstance, e⟩

end AlgebraicGeometry.Scheme.Modules

end
