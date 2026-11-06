module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealOrderIso
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentKernelOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# Dévissage of coherent modules on a Noetherian algebraic space

This file sets up the vocabulary in which Stacks 07UQ, 07UR, 07US and 08AN speak about a
coherent module on a Noetherian algebraic space `X`: the integral closed subspaces of `X`, the
direct image of a quasi-coherent sheaf of ideals on one of them, and the finite filtration whose
successive quotients are such direct images.

## Main definitions

* `AlgebraicGeometry.Space.closedSubfunctorSpace` and
  `AlgebraicGeometry.Space.closedSubfunctorι` read a closed subspace as an object of the category
  of algebraic spaces and its inclusion as a morphism there.
* `AlgebraicGeometry.Space.IsReducedIrreducible` is the condition "reduced with irreducible space
  of points" on a subfunctor.
* `AlgebraicGeometry.Space.HasIdealDevissage` is the conclusion of Stacks 07UR for a single
  module.
* `AlgebraicGeometry.Space.ClosedUnderCoherentExtensions` is hypothesis (1) of Stacks 07US and
  `AlgebraicGeometry.Space.TwoOutOfThreeCoherent` is hypothesis (1) of Stacks 08AN, which
  strengthens it to all three implications of the two-out-of-three condition.

## Main results

* `AlgebraicGeometry.Space.isCoherent_of_iso` transports coherence along an isomorphism.
* `AlgebraicGeometry.Space.property_of_forall_hasIdealDevissage`: a property closed under
  extensions, holding for zero modules and for the direct images of quasi-coherent sheaves of
  ideals on integral closed subspaces, holds for every coherent module which carries the
  filtration of Stacks 07UR.

## References

* [Stacks Project, Tag 07UR](https://stacks.math.columbia.edu/tag/07UR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Coherence of a module on an algebraic space is invariant under isomorphism: both of its
two clauses are, by `SheafOfModules.IsQuasicoherentOnSite.of_iso` and
`Stacks.SheafOfModules.isCoherentOnSite_of_iso`. -/
theorem isCoherent_of_iso {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {M N : Modules.{u, m} B S hS F hF} (e : M ≅ N)
    (hM : IsCoherent B S hS F hF M) : IsCoherent B S hS F hF N :=
  { __ := SheafOfModules.IsQuasicoherentOnSite.of_iso e hM.toIsQuasicoherentOnSite
    __ := Stacks.SheafOfModules.isCoherentOnSite_of_iso e hM.toIsCoherentOnSite }

variable {X : AlgebraicSpaces B S hS}

/-- A closed subspace of an algebraic space, read as an object of the category of algebraic
spaces over `S`.

This is `AlgebraicGeometry.Space.closedSubspaceToSpace` of
`StacksFrontier/AlgebraicGeometry/Spaces/SchemeTheoreticSupport.lean` with the closedness witness
taken as a separate argument rather than bundled into
`AlgebraicGeometry.Space.ClosedSubspaces`. -/
abbrev closedSubfunctorSpace {Z : Subfunctor X.1} (hZ : IsClosedSubspace B S hS Z) :
    AlgebraicSpaces B S hS :=
  ⟨Z.toFunctor, hZ.1⟩

/-- The inclusion `i : Z ⟶ X` of a closed subspace, read as a morphism of algebraic spaces
over `S`. -/
abbrev closedSubfunctorι {Z : Subfunctor X.1} (hZ : IsClosedSubspace B S hS Z) :
    closedSubfunctorSpace B S hS hZ ⟶ X :=
  ObjectProperty.homMk Z.ι

/-- A subfunctor `Z` of an algebraic space is *reduced and irreducible* when it is
étale-locally reduced and its space of points is irreducible.  Together with
`AlgebraicGeometry.Space.IsClosedSubspace` this is the shape in which Stacks 07UQ, 07UR, 07US
and 08AN speak of a "reduced closed subspace `Z ⊆ X` with `|Z|` irreducible". -/
abbrev IsReducedIrreducible (Z : Subfunctor X.1) : Prop :=
  HasEtaleLocalProperty B S hS Z.toFunctor (fun Y : Scheme.{u} => IsReduced Y) ∧
    @IrreducibleSpace (points B S hS Z.toFunctor) (pointTopology B S hS Z.toFunctor)

/-- **The conclusion of Stacks 07UR for one module.**  The module `M` on the algebraic space
`X` carries a finite filtration `0 = G 0 ⊆ … ⊆ G n = M` by coherent submodules such that for
each step there are an integral closed subspace `Z ⊆ X` and a quasi-coherent sheaf of ideals
`I ⊆ 𝒪_Z` with `G (j + 1) / G j ≅ i_* I`.

The successive quotient is presented as a cokernel cofork rather than through
`CategoryTheory.Limits.cokernel`, so that the statement needs no `HasCokernel` instance; that
the filtration ends at `M` is the inclusion `G n ⟶ M` being an isomorphism. -/
def HasIdealDevissage (X : AlgebraicSpaces B S hS) (M : Modules.{u, u} B S hS X.1 X.2) : Prop :=
  ∃ (n : ℕ) (G : Fin (n + 1) → Subobject M) (hG : Monotone G),
    IsZero (G 0 : Modules.{u, u} B S hS X.1 X.2) ∧
    IsIso (G (Fin.last n)).arrow ∧
    (∀ j : Fin (n + 1), IsCoherent B S hS X.1 X.2 (G j : Modules.{u, u} B S hS X.1 X.2)) ∧
    ∀ j : Fin n, ∃ (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z),
      IsReducedIrreducible B S hS Z ∧
      ∃ I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ),
        ∃ (q : (G j.succ : Modules.{u, u} B S hS X.1 X.2) ⟶
            (modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj
              I.1.toSheafOfModules)
          (hq : Subobject.ofLE (G j.castSucc) (G j.succ) (hG j.castSucc_le_succ) ≫ q = 0),
          Nonempty (IsColimit (CokernelCofork.ofπ q hq))

/-- Closure of a property of `𝒪_X`-modules under extensions of coherent modules: this is
hypothesis (1) of Stacks 07US. -/
def ClosedUnderCoherentExtensions (X : AlgebraicSpaces B S hS)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop) : Prop :=
  ∀ E : ShortComplex (Modules.{u, u} B S hS X.1 X.2), E.ShortExact →
    IsCoherent B S hS X.1 X.2 E.X₁ → IsCoherent B S hS X.1 X.2 E.X₂ →
    IsCoherent B S hS X.1 X.2 E.X₃ → P E.X₁ → P E.X₃ → P E.X₂

/-- **Hypothesis (1) of Stacks 08AN.**  For a short exact sequence of coherent modules on `X`,
if two out of the three terms have the property `P` then so does the third.

This is strictly stronger than hypothesis (1) of Stacks 07US,
`AlgebraicGeometry.Space.ClosedUnderCoherentExtensions`, which is the first of the three
implications on its own. -/
def TwoOutOfThreeCoherent (X : AlgebraicSpaces B S hS)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop) : Prop :=
  ∀ E : ShortComplex (Modules.{u, u} B S hS X.1 X.2), E.ShortExact →
    IsCoherent B S hS X.1 X.2 E.X₁ → IsCoherent B S hS X.1 X.2 E.X₂ →
    IsCoherent B S hS X.1 X.2 E.X₃ →
    (P E.X₁ → P E.X₃ → P E.X₂) ∧ (P E.X₂ → P E.X₃ → P E.X₁) ∧ (P E.X₁ → P E.X₂ → P E.X₃)

/-- A property holding on zero modules and closed under extensions of coherent modules is
invariant under isomorphism of coherent modules.

The source leaves this implicit; it is applied to `0 → M → N → 0 → 0`. -/
theorem property_of_iso (X : AlgebraicSpaces B S hS)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop)
    (hzero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (hext : ClosedUnderCoherentExtensions B S hS X P)
    {M N : Modules.{u, u} B S hS X.1 X.2} (hM : IsCoherent B S hS X.1 X.2 M)
    (hN : IsCoherent B S hS X.1 X.2 N) (e : M ≅ N) (h : P M) : P N := by
  obtain ⟨Zobj, hZobj⟩ := HasZeroObject.zero (C := Modules.{u, u} B S hS X.1 X.2)
  refine hext (ShortComplex.mk e.hom (0 : N ⟶ Zobj) (comp_zero)) ?_ hM hN
    (IsCoherent.of_isZero B S hS X.1 X.2 hZobj) h (hzero _ hZobj)
  refine ShortComplex.ShortExact.mk' ?_ inferInstance (hZobj.epi _)
  exact ShortComplex.exact_of_g_is_cokernel _
    (CokernelCofork.IsColimit.ofEpiOfIsZero _ (SplitEpi.epi ⟨e.inv, e.inv_hom_id⟩) hZobj)

/-- **The dévissage induction along the filtration of Stacks 07UR.**  Let `P` be a property of
`𝒪_X`-modules which holds for zero modules, is closed under extensions of coherent modules, and
holds for every direct image `i_*I` of a quasi-coherent sheaf of ideals on a reduced closed
subspace `i : Z → X` with `|Z|` irreducible.  If every coherent module carries the filtration of
Stacks 07UR, then `P` holds for every coherent module: it holds for the zero term of the
filtration and passes from each term to the next by an extension.

Stacks 07US, `AlgebraicGeometry.Space.property_of_ideal_pushforward_and_extensions`, is this
statement with the filtration supplied by Stacks 07UR. -/
theorem property_of_forall_hasIdealDevissage (X : AlgebraicSpaces B S hS)
    (hdev : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 M →
      HasIdealDevissage B S hS X M)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop)
    (hzero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (hext : ClosedUnderCoherentExtensions B S hS X P)
    (hideal : ∀ (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z),
      IsReducedIrreducible B S hS Z →
      ∀ I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ),
        P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules))
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M) : P M := by
  obtain ⟨n, G, hG, hG0, hGn, hGcoh, hGstep⟩ := hdev M hM
  have hP : ∀ j : Fin (n + 1), P (G j : Modules.{u, u} B S hS X.1 X.2) := by
    refine Fin.induction (hzero _ hG0) ?_
    intro j ih
    obtain ⟨Z, hZ, hint, I, q, hq, ⟨hcol⟩⟩ := hGstep j
    have hQcoh : IsCoherent B S hS X.1 X.2
        ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) :=
      isCoherent_of_iso B S hS X.2
        (IsColimit.coconePointUniqueUpToIso
          (cokernelIsCokernel
            (Subobject.ofLE (G j.castSucc) (G j.succ) (hG j.castSucc_le_succ))) hcol)
        (isCoherent_cokernel B S hS X.1 X.2 (hGcoh j.castSucc) (hGcoh j.succ) _)
    refine hext (ShortComplex.mk _ q hq) ?_ (hGcoh j.castSucc) (hGcoh j.succ) hQcoh ih
      (hideal Z hZ hint I)
    exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ hcol)
      inferInstance (epi_of_isColimit_cofork hcol)
  exact property_of_iso B S hS X P hzero hext (hGcoh (Fin.last n)) hM
    (asIso (G (Fin.last n)).arrow) (hP (Fin.last n))

end AlgebraicGeometry.Space

end
