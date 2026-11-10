module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.FiniteFreeSummands
public import StacksCore.Tactic.StacksAttribute

/-!
# Local lifting of maps from finite free summands

Let `E` be a direct summand of a finite free module on a ringed space. A map
from `E` through a surjective map of modules can be lifted after restricting
to a sufficiently small open neighbourhood of any point.

## Main definitions

There are no new definitions.

## Main results

* `StrictlyPerfect.LocalLifting.exists_local_lift` gives a lift on an open neighbourhood of each
  point.

## Implementation notes

Restriction to an open `U` is expressed by `SheafOfModules.over`, which regards
a sheaf of modules as a sheaf on the category of opens lying over `U`.
Surjectivity is expressed categorically by `Epi`.

The proof is the Stacks argument. Write `E` as a retract of `O_X^n`, which is the free
sheaf of modules on `I = ULift (Fin n)`; a map out of a free sheaf is a family of global
sections indexed by `I` (`SheafOfModules.freeHomEquiv`), each of which lifts through `p` over
some open `V i` because an epimorphism of sheaves of modules is locally surjective
(`Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi`). Since `I` is finite, the
intersection `U = ⨅ i, V i` is still an open neighbourhood of the given point, and over `U`
all the chosen preimages exist simultaneously, assembling to a lift of `O_X^n|_U ⟶ F|_U`.
Composing with the retract inclusion gives the lift of `f|_U`.

Identifying `(O_X^n)|_U` with the free sheaf of modules on `I` over the restricted ring uses
`SheafOfModules.mapFreeIso`, which needs restriction to preserve `I`-indexed coproducts. That
is supplied by `SheafOfModules.overFunctor_isLeftAdjoint`, which is also what makes
`SheafOfModules.ιFree_mapFreeIso_hom` applicable by `rw` rather than only up to unfolding.

The space and ring universes agree here, unlike in `StrictlyPerfect.IsDirectSummandOfFiniteFree`
itself: both the characterisation of epimorphisms as locally surjective maps and the free sheaf
of modules are only available when the module universe is the ring universe, and the
sheafification hypotheses they need are automatic only when the site universe matches too.

## References

* [Stacks Project, Tag 08C6](https://stacks.math.columbia.edu/tag/08C6)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits
open StrictlyPerfect

namespace StrictlyPerfect.LocalLifting

universe u

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}
variable {E F G : OXMod.{u, u} X} (f : E ⟶ F) (p : G ⟶ F)

/-- Sections over opens `V i ⊇ U` lifting the sections defining a map `q` out of a free sheaf
assemble to a lift of `q` over `U`. -/
theorem exists_lift_over_of_sections {I : Type u}
    (q : SheafOfModules.free (R := structureSheafOfRings X) I ⟶ F) (U : Opens X.carrier)
    (V : I → Opens X.carrier) (hUV : ∀ i, U ≤ V i) (a : ∀ i, G.val.obj (Opposite.op (V i)))
    (ha : ∀ i, p.val.app (Opposite.op (V i)) (a i) =
      F.val.map (homOfLE (le_top : V i ≤ ⊤)).op ((F.freeHomEquiv q i).val (Opposite.op ⊤))) :
    ∃ k : (SheafOfModules.free (R := structureSheafOfRings X) I).over U ⟶ G.over U,
      k ≫ p.over U = q.over U := by
  let t : I → (G.over U).sections := fun i =>
    { val := fun Y => G.val.map (Y.unop.hom ≫ homOfLE (hUV i)).op (a i)
      property := by
        intro Y Z g
        change G.val.map g.unop.left.op
          (G.val.map (Y.unop.hom ≫ homOfLE (hUV i)).op (a i)) = _
        rw [← G.val.map_comp_apply]
        congr 1 }
  let eU : SheafOfModules.free (R := (structureSheafOfRings X).over U) I ≅
      (SheafOfModules.free (R := structureSheafOfRings X) I).over U :=
    SheafOfModules.mapFreeIso (SheafOfModules.overFunctor (structureSheafOfRings X) U)
      I (Iso.refl _)
  refine ⟨eU.inv ≫ (SheafOfModules.freeHomEquiv (G.over U)).symm t, ?_⟩
  rw [← cancel_epi eU.hom]
  apply (SheafOfModules.freeHomEquiv (F.over U)).injective
  funext i
  simp only [Category.assoc, eU.hom_inv_id_assoc,
    SheafOfModules.freeHomEquiv_comp_apply, Equiv.apply_symm_apply]
  change SheafOfModules.sectionsMap (p.over U) (t i) =
    (F.over U).unitHomEquiv (SheafOfModules.ιFree i ≫ eU.hom ≫ q.over U)
  dsimp only [eU]
  rw [SheafOfModules.ιFree_mapFreeIso_hom_assoc
    (SheafOfModules.overFunctor (structureSheafOfRings X) U) I (Iso.refl _) i (q.over U)]
  simp only [Iso.refl_hom]
  apply PresheafOfModules.sections_ext
  intro Y
  change p.val.app (Opposite.op Y.unop.left)
    (G.val.map (Y.unop.hom ≫ homOfLE (hUV i)).op (a i)) =
    (F.freeHomEquiv q i).val (Opposite.op Y.unop.left)
  rw [PresheafOfModules.naturality_apply]
  change F.val.map (Y.unop.hom ≫ homOfLE (hUV i)).op
    (p.val.app (Opposite.op (V i)) (a i)) = _
  rw [ha i]
  exact (congrArg (fun z => F.val.map (Y.unop.hom ≫ homOfLE (hUV i)).op z)
    ((F.freeHomEquiv q i).property (homOfLE (le_top : V i ≤ ⊤)).op)).trans
      ((F.freeHomEquiv q i).property (Y.unop.hom ≫ homOfLE (hUV i)).op)

/-- A map from a finite free sheaf of modules lifts locally through any epimorphism of sheaves
of modules. -/
theorem exists_local_lift_of_free [Epi p] {I : Type u} [Finite I]
    (q : SheafOfModules.free (R := structureSheafOfRings X) I ⟶ F) (x : X.carrier) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ k : (SheafOfModules.free (R := structureSheafOfRings X) I).over U ⟶ G.over U,
        k ≫ p.over U = q.over U := by
  have hloc : PresheafOfModules.IsLocallySurjective
      (Opens.grothendieckTopology X.carrier) p.val :=
    Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi p
  choose V hV hs hxV using
    fun i : I => ((TopCat.Presheaf.isLocallySurjective_iff
      ((SheafOfModules.toSheaf (structureSheafOfRings X)).map p).hom).mp
      hloc (⊤) ((F.freeHomEquiv q i).val (Opposite.op ⊤)) x (by simp))
  choose a ha using hs
  change ∀ i, G.val.obj (Opposite.op (V i)) at a
  refine ⟨⨅ i, V i, ?_, exists_lift_over_of_sections p q _ V (iInf_le V) a ha⟩
  rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  exact hxV

/-- A map from a direct summand of a finite free module lifts locally through
any epimorphism of sheaves of modules. -/
@[stacks 08C6]
theorem exists_local_lift [Epi p] (hE : IsDirectSummandOfFiniteFree E) :
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ l : E.over U ⟶ G.over U, l ≫ p.over U = f.over U := by
  intro x
  obtain ⟨n, ⟨ρ⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract E).mp hE
  let e : finiteFree X n ≅
      SheafOfModules.free (R := structureSheafOfRings X) (ULift.{u} (Fin n)) := by
    change (⨁ fun _ : Fin n => SheafOfModules.unit (structureSheafOfRings X)) ≅
      ∐ (fun _ : ULift.{u} (Fin n) => SheafOfModules.unit (structureSheafOfRings X))
    exact (biproduct.whiskerEquiv
      (g := fun _ : ULift.{u} (Fin n) => SheafOfModules.unit (structureSheafOfRings X))
      Equiv.ulift.symm (fun _ => Iso.refl _)).trans (biproduct.isoCoproduct _)
  obtain ⟨U, hxU, k, hk⟩ := exists_local_lift_of_free p (e.inv ≫ ρ.r ≫ f) x
  refine ⟨U, hxU, ρ.i.over U ≫ e.hom.over U ≫ k, ?_⟩
  rw [Category.assoc, Category.assoc, hk]
  change (SheafOfModules.overFunctor (structureSheafOfRings X) U).map
    (ρ.i ≫ e.hom ≫ e.inv ≫ ρ.r ≫ f) = _
  congr 1
  simp only [e.hom_inv_id_assoc]
  rw [← Category.assoc, ρ.retract, Category.id_comp]

end StrictlyPerfect.LocalLifting

end
