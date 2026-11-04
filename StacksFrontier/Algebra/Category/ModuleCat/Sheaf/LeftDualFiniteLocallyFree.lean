module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualRingedSite
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# A finite locally free sheaf of modules admits a dual

Let `(C, 𝒪)` be a ringed site and let `F` be a sheaf of `𝒪`-modules which is finite locally free
in the sense of [Stacks, Tag 01C6] (2): on a family of objects covering the final object, `F`
restricts to a free module on a finite index type. Then `F` is in particular locally a *retract*
of a finite free module — trivially, the retraction being an isomorphism — so the duality of
[Stacks, Tag 0FNY] applies and `F^∨ = SheafHom(F, 𝒪)` is a left dual of `F`.

This is the hypothesis under which
`CategoryTheory.MonoidalClosed.isIso_tensorInternalEnd_of_exactPairing` applies to sheaves of
modules, so it is what makes `End(E) ⊗ End(F) ≅ End(E ⊗ F)` available for the finite locally
free sheaves occurring in the Brauer group of a scheme.

## Main definitions

* `Stacks.SheafOfModules.exactPairingDualSheafOfLocallyFreeData`: the exact pairing exhibiting
  `F^∨` as a left dual of `F`, from a family of local free presentations with finite index
  types.
* `Stacks.SheafOfModules.hasRightDualOfLocallyFreeData`: the same, read as
  `CategoryTheory.HasRightDual F`.

## Main results

* `Stacks.SheafOfModules.nonempty_hasRightDual_of_isFiniteLocallyFree`: **a finite locally free
  sheaf of modules admits a dual.** The conclusion is `Nonempty (HasRightDual F)` rather than
  `HasRightDual F` because `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` only asserts
  the existence of the local free presentations; the dual object `F^∨` itself is canonical, and
  it is only the exact pairing that is extracted from that existence statement. Consumers of the
  dual want a `Prop` — invertibility of a comparison morphism — so `Nonempty` is enough.

## Implementation notes

The index types of the local free presentations are `Finite` by
`SheafOfModules.LocalGeneratorsData.IsFiniteType`, whereas Tag 0FNY's duality consumes a
`Fintype` and a `DecidableEq`; both are supplied classically, which is why the definitions here
are noncomputable.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
-/

@[expose] public section

open CategoryTheory

noncomputable section

namespace Stacks.SheafOfModules

universe v u

attribute [local instance] Strict.monoidalCategory monoidalCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
  (h𝒪 : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (F : _root_.SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪))

/-- A local free presentation of `F` on an object exhibits `F` restricted there as a retract of
a finite free module: the retraction is the presentation itself, which is an isomorphism. -/
def retractOfLocallyFreeData (q : F.LocalGeneratorsData.{u}) [q.IsLocallyFreeData] (k : q.I) :
    Retract (F.over (q.X k))
      (_root_.SheafOfModules.free
        (R := (TensorSheafification.structureSheaf 𝒪 h𝒪).over (q.X k)) (q.generators k).I) where
  i := inv (q.generators k).π
  r := (q.generators k).π
  retract := IsIso.inv_hom_id _

/-- **The dual of a finite locally free sheaf of modules is a left dual**, from the local free
presentations. This is [Stacks, Tag 0FNY] with its local hypothesis supplied by local freeness. -/
@[instance_reducible]
def exactPairingDualSheafOfLocallyFreeData (q : F.LocalGeneratorsData.{u})
    [q.IsLocallyFreeData] [q.IsFiniteType] :
    ExactPairing F (dualSheaf 𝒪 h𝒪 F) :=
  letI : ∀ k : q.I, Finite (q.generators k).I := fun k =>
    (‹q.IsFiniteType›.isFiniteType k).finite
  letI : ∀ k : q.I, Fintype (q.generators k).I := fun k => Fintype.ofFinite _
  letI : ∀ k : q.I, DecidableEq (q.generators k).I := fun _ => Classical.decEq _
  exactPairingDualSheafOfRetract 𝒪 h𝒪 F q.coversTop
    (I := fun k => (q.generators k).I) (retractOfLocallyFreeData 𝒪 h𝒪 F q)

/-- `Stacks.SheafOfModules.exactPairingDualSheafOfLocallyFreeData` read as Mathlib's
`CategoryTheory.HasRightDual F`. -/
@[instance_reducible]
def hasRightDualOfLocallyFreeData (q : F.LocalGeneratorsData.{u})
    [q.IsLocallyFreeData] [q.IsFiniteType] : HasRightDual F where
  rightDual := dualSheaf 𝒪 h𝒪 F
  exact := exactPairingDualSheafOfLocallyFreeData 𝒪 h𝒪 F q

/-- **A finite locally free sheaf of modules admits a dual.** -/
theorem nonempty_hasRightDual_of_isFiniteLocallyFree
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{max u v, v, u} F) :
    Nonempty (HasRightDual F) := by
  obtain ⟨q, hq, hft⟩ := hF.exists_isFiniteLocallyFreeData
  exact ⟨hasRightDualOfLocallyFreeData 𝒪 h𝒪 F q⟩

end Stacks.SheafOfModules
