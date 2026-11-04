module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Recognising the rank of a finite locally free morphism from a basis of its sections

A morphism of schemes `p : Z ⟶ Spec R` with affine underlying morphism is finite locally free
of rank `r` as soon as the `R`-module of global sections of `Z` has a basis indexed by `Fin r`.
This is the converse of the passage from the sheaf-level rank condition to the module-level one,
`AlgebraicGeometry.finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank`, and it is what lets
a rank be *produced* rather than only consumed.

## Main results

* `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_free`: a free sheaf of modules on
  a type with `r` elements is finite locally free of rank `r`.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_of_basis`: a morphism to the spectrum of a ring
  whose underlying morphism is affine and whose global sections have a basis indexed by
  `Fin r` is finite locally free of rank `r`.

## Implementation notes

The sheaf-level lemma is deliberately stated for an arbitrary sheaf of rings on an arbitrary
site rather than for `AlgebraicGeometry.Scheme.Modules`. Stated for schemes, the definitional
unfolding of the site, of `Scheme.ringCatSheaf` and of the generating sections makes the
`IsIso` goals exceed the default heartbeat limit; with the site abstract nothing unfolds and
the proof goes through unchanged. It is then applied to a scheme by instantiation, which costs
nothing. The transport of the rank condition along an isomorphism is
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso`, proved where the rank
condition is defined.

The rank is produced from a basis through the quasi-coherence of the pushforward of the
structure sheaf along an affine morphism — the morphism is quasi-compact and quasi-separated,
so `AlgebraicGeometry.pushforward_isQuasicoherent` (Tag 01LC) applies to the quasi-coherent
`SheafOfModules.unit` — which identifies that pushforward with the module sheaf of its global
sections, and `AlgebraicGeometry.tilde_fixed_free_iff_basis` turns the basis into an
isomorphism of that module sheaf with a free sheaf on `ULift (Fin r)`.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v u₁

namespace AlgebraicGeometry.SheafOfModules

/-- The free sheaf of modules on a type with `r` elements is finite locally free of rank `r`:
its tautological generating sections are already an isomorphism. -/
theorem isFiniteLocallyFreeOfRank_free
    {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}] [HasBinaryProducts C]
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (r : ℕ) :
    IsFiniteLocallyFreeOfRank (_root_.SheafOfModules.free (R := R) (ULift.{u} (Fin r))) r :=
  ⟨(_root_.SheafOfModules.free.generatingSections (R := R)
      (ULift.{u} (Fin r))).localGeneratorsData,
    inferInstance, fun _ ↦ ⟨Equiv.ulift⟩⟩

end AlgebraicGeometry.SheafOfModules

namespace Stacks.Morphisms

open _root_.AlgebraicGeometry

/-- A morphism to the spectrum of a ring whose underlying morphism of schemes is affine and
whose module of global sections has a basis indexed by `Fin r` is finite locally free of
rank `r`.

The module structure on the global sections is the one induced by the morphism, as in
`AlgebraicGeometry.finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank`; it is written out
in the statement rather than introduced by a local instance, so that a caller can supply
the basis without first reproducing that instance. The base is taken to be an object of
`CommRingCat` rather than a type with a ring structure, so that the statement applies to
`AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField` without an intervening unfolding of
`CommRingCat.of`. -/
@[sga "1 I 4.10" "special case"]
theorem isFiniteLocallyFreeOfRank_of_basis {R : CommRingCat.{u}} {Z : Scheme.{u}}
    (p : Z ⟶ Spec R) [IsAffineHom p] (r : ℕ)
    (hb : Nonempty (@Module.Basis (Fin r) ↑R ↑Γ(Z, ⊤) _ _
      ((Scheme.ΓSpecIso R).inv ≫ p.appTop).hom.toAlgebra.toModule)) :
    IsFiniteLocallyFreeOfRank p r := by
  let : Algebra ↑R ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso R).inv ≫ p.appTop).hom.toAlgebra
  let M : (Spec R).Modules := pushforwardStructureSheaf p
  let : SheafOfModules.IsQuasicoherent.{u, u, u} (SheafOfModules.unit Z.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Z
  let : M.IsQuasicoherent := pushforward_isQuasicoherent p (SheafOfModules.unit Z.ringCatSheaf)
  have hIso : IsIso M.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ M).mp inferInstance
  obtain ⟨b⟩ := hb
  obtain ⟨eFree⟩ := (tilde_fixed_free_iff_basis ↑R (moduleSpecΓFunctor.obj M)
    (ULift.{u} (Fin r))).2 ⟨b.reindex Equiv.ulift.symm⟩
  exact .mk (toIsAffineHom := inferInstance) (toIsFiniteLocallyFreeOfRank :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (eFree.symm ≪≫ @asIso _ _ _ _ _ hIso)
      (SheafOfModules.isFiniteLocallyFreeOfRank_free (R := (Spec R).ringCatSheaf) r))

end Stacks.Morphisms

end
