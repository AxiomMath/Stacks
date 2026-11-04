module

public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LocalCohomologyDegreewise
public import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness along a vanishing locus in an affine spectrum

Let `A` be a ring, let `I ⊆ A` be an ideal, let `X = Spec A`, let `Z = V(I)` and let `U = X ∖ Z`.
For a finite `A`-module `M` the four-term exact sequence and the isomorphisms in degrees `≥ 1`
of [Stacks, Tag 0BK0] (2) turn finiteness of `H^p(U, M̃)` into finiteness of `H^{p+1}_Z(M)` and
back, in every degree `p ≥ 0`.  This is the equivalence of conditions (b) and (c) of that tag's
clause (3).  When in addition the canonical map `M ⟶ Γ(U, M̃)` is an isomorphism, the same
sequence forces `H⁰_Z(M)` and `H¹_Z(M)` to vanish; this is the conclusion of clause (4).

## Main results

* `Stacks.LocalCohomologySequence.finite_complementCohomologyBase_iff`: for a finite `A`-module
  `M` and any `p ≥ 0`, the `A`-module `H^p(U, M̃)` is finite exactly when `H^{p+1}_Z(X, M̃)` is.
* `Stacks.LocalCohomologySequence.finite_localCohomology_iff_span_singleton`: the same
  equivalence for a principal ideal, with the algebraic local cohomology of `M` in place of the
  cohomology of `M̃` with support.
* `Stacks.LocalCohomologySequence.isZero_cohomologyWithSupport_of_isIso`: if the canonical map
  `M ⟶ Γ(U, M̃)` is an isomorphism then `H⁰_Z(X, M̃)` and `H¹_Z(X, M̃)` are zero.

## Implementation notes

The terms of the sequence of `Stacks.LocalCohomologySequence.exact_cohomologyWithSupport_sequence`
are modules over the global functions `Γ(Spec A, 𝒪)`; the statement of the tag is about finite
`A`-modules, so everything here is read over `A` through the restriction of scalars
`Stacks.LocalCohomologyTilde.globalToBase`, which is an additive equivalence and therefore
carries the exactness, the monomorphisms and the epimorphisms of that sequence along with it.

In degrees `p ≥ 1` the equivalence is immediate from the isomorphism `H^p(U, M̃) ≅ H^{p+1}_Z(M̃)`.
In degree zero it is the four-term sequence: `H¹_Z(M̃)` is a quotient of `Γ(U, M̃)`, which gives
one direction, and `Γ(U, M̃)` sits in an exact sequence whose outer terms are `Γ(X, M̃) ≅ M` and
`H¹_Z(M̃)`, which gives the other through `Module.Finite.of_exact`.  This is the only place the
hypothesis that `M` is finite is used; no Noetherian hypothesis on `A` is needed.

Conditions (a) and (b) of clause (3) are not compared here.  Doing so needs the identification
of the global sections of `R^pj_*ℱ` with `H^p(U, ℱ)`, which the library does not have: the
higher direct image of Tag 01E4 is the sheafification of `V ↦ H^p(j^{-1}V, ℱ)` and nothing
evaluates that sheafification at `⊤`.

## References

* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0A6T](https://stacks.math.columbia.edu/tag/0A6T)
* [Stacks Project, Tag 0519](https://stacks.math.columbia.edu/tag/0519)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.SectionsWithSupport
open Stacks.LocalCohomologyTilde

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.LocalCohomologySequence

variable {A : CommRingCat.{u}}

/-! ### A finiteness criterion for modules -/

/-- **Finiteness in a right exact sequence.**  If `X₁ ⟶ X₂ ⟶ X₃` is exact and the second map is
an epimorphism, then `X₂` is a finite module as soon as `X₁` and `X₃` are. -/
theorem finite_X₂_of_exact {R : Type u} [Ring R] (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.Exact) (hg : Epi S.g) [Module.Finite R S.X₁] [Module.Finite R S.X₃] :
    Module.Finite R S.X₂ :=
  Module.Finite.of_exact (f := S.f.hom) (g := S.g.hom)
    (LinearMap.exact_iff.mpr hS.moduleCat_range_eq_ker.symm)
    ((ModuleCat.epi_iff_surjective S.g).mp hg)

/-! ### The terms of the sequence, read over the base ring -/

/-- `H^p(U, M̃)`, the cohomology of `M̃` on the complement of `V(I)`, read as an `A`-module. -/
abbrev complementCohomologyBase (I : Ideal A) (M : ModuleCat.{u} A) (p : ℕ) :
    ModuleCat.{u} A :=
  (globalToBase A).obj ((complementCohomology I p).obj (tildeSheaf M))

/-- `H^p_{V(I)}(Spec A, M̃)`, the cohomology of `M̃` with support in `V(I)`, read as an
`A`-module. -/
abbrev cohomologyWithSupportBase (I : Ideal A) (M : ModuleCat.{u} A) (p : ℕ) :
    ModuleCat.{u} A :=
  (globalToBase A).obj ((cohomologyWithSupport I p).obj (tildeSheaf M))

/-- `Γ(Spec A, M̃)`, read as an `A`-module, is `M`. -/
def ambientCohomologyZeroBaseIso (M : ModuleCat.{u} A) :
    (globalToBase A).obj ((ambientCohomology A 0).obj (tildeSheaf M)) ≅ M :=
  (globalToBase A).mapIso ((ambientCohomologyZeroIso (A := A)).app (tildeSheaf M)) ≪≫
    ((globalSectionsTildeIso A).app M).symm

/-- For a finite `A`-module `M`, the `A`-module `Γ(Spec A, M̃)` is finite. -/
instance finite_ambientCohomologyZeroBase (M : ModuleCat.{u} A) [Module.Finite A M] :
    Module.Finite A ((globalToBase A).obj ((ambientCohomology A 0).obj (tildeSheaf M))) :=
  Module.Finite.equiv (ambientCohomologyZeroBaseIso M).symm.toLinearEquiv

/-- The restriction map `Γ(Spec A, M̃) ⟶ Γ(U, M̃)`, read over `A`. -/
abbrev baseComplementRestriction (I : Ideal A) (M : ModuleCat.{u} A) :
    (globalToBase A).obj ((ambientCohomology A 0).obj (tildeSheaf M)) ⟶
      complementCohomologyBase I M 0 :=
  (globalToBase A).map ((complementRestriction I 0).app (tildeSheaf M))

/-- The canonical map `M ⟶ Γ(U, M̃)` of `A`-modules: the identification of `M` with the global
sections of `M̃` followed by restriction to the complement of `V(I)`. -/
def toComplementSections (I : Ideal A) (M : ModuleCat.{u} A) :
    M ⟶ complementCohomologyBase I M 0 :=
  (ambientCohomologyZeroBaseIso M).inv ≫ baseComplementRestriction I M

/-! ### Clause (3): the equivalence of (b) and (c) -/

/-- **Stacks Project, Tag 0BK0 (3), the equivalence of (b) and (c)**, with cohomology with
support in place of local cohomology.  Let `I` be an ideal of a ring `A`, let `X = Spec A`, let
`Z = V(I)` and let `U = X ∖ Z`.  For a finite `A`-module `M` and any `p ≥ 0` the `A`-module
`H^p(U, M̃)` is finite if and only if `H^{p+1}_Z(X, M̃)` is. -/
@[stacks 0BK0 "(3), (b) ⟺ (c), with cohomology with support in place of local cohomology"]
theorem finite_complementCohomologyBase_iff (I : Ideal A) (M : ModuleCat.{u} A)
    [Module.Finite A M] (p : ℕ) :
    Module.Finite A (complementCohomologyBase I M p) ↔
      Module.Finite A (cohomologyWithSupportBase I M (p + 1)) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · obtain ⟨delta, -, hexact, hepi, -⟩ := exact_cohomologyWithSupport_sequence I M
    have hz1 : (complementRestriction I 0).app (tildeSheaf M) ≫
        (delta 0).app (tildeSheaf M) = 0 := hexact.toIsComplex.zero 1
    have hzb : baseComplementRestriction I M ≫
        (globalToBase A).map ((delta 0).app (tildeSheaf M)) = 0 := by
      rw [← (globalToBase A).map_comp, hz1, (globalToBase A).map_zero]
    have hepi' : Epi ((globalToBase A).map ((delta 0).app (tildeSheaf M))) :=
      Functor.map_epi _ _
    have hex : (ShortComplex.mk (baseComplementRestriction I M)
        ((globalToBase A).map ((delta 0).app (tildeSheaf M))) hzb).Exact := by
      refine ShortComplex.exact_of_iso ?_ ((hexact.exact' 1 2 3).map (globalToBase A))
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by rfl) (by rfl)
    exact ⟨fun _ => Module.Finite.of_surjective
      ((globalToBase A).map ((delta 0).app (tildeSheaf M))).hom
      ((ModuleCat.epi_iff_surjective _).mp hepi'), fun _ => finite_X₂_of_exact _ hex hepi'⟩
  · obtain ⟨e⟩ := nonempty_iso_complementCohomology I M p hp
    exact Module.Finite.equiv_iff ((globalToBase A).mapIso e).toLinearEquiv

/-- **Stacks Project, Tag 0BK0 (3) for a principal ideal, the equivalence of (b) and (c).**  Let
`A` be a Noetherian ring, let `f : A`, let `X = Spec A`, let `Z = V(f)` and let `U = X ∖ Z`.  For
a finite `A`-module `M` and any `p ≥ 0` the `A`-module `H^p(U, M̃)` is finite if and only if the
local cohomology `H^{p+1}_Z(M)` is. -/
@[stacks 0BK0 "(3), (b) ⟺ (c), principal ideal"]
theorem finite_localCohomology_iff_span_singleton [IsNoetherianRing A] (f : A)
    (M : ModuleCat.{u} A) [Module.Finite A M] (p : ℕ) :
    Module.Finite A (complementCohomologyBase (Ideal.span {f}) M p) ↔
      Module.Finite A ((localCohomologySpanSingleton A f (p + 1)).obj M) := by
  rw [finite_complementCohomologyBase_iff (Ideal.span {f}) M p]
  exact Module.Finite.equiv_iff
    (cohomologyWithSupportTildeSpanSingletonIso f M (p + 1)).toLinearEquiv

/-! ### Clause (4): the vanishing -/

/-- **Stacks Project, Tag 0BK0 (4), the vanishing.**  Let `I` be an ideal of a ring `A`, let
`X = Spec A`, let `Z = V(I)` and let `U = X ∖ Z`.  If the canonical map `M ⟶ Γ(U, M̃)` is an
isomorphism — which is what taking `M = Γ(U, ℱ)` achieves — then `H⁰_Z(X, M̃) = 0` and
`H¹_Z(X, M̃) = 0`. -/
@[stacks 0BK0 "(4), the vanishing, for a module whose canonical map to the sections over the \
complement is an isomorphism"]
theorem isZero_cohomologyWithSupport_of_isIso (I : Ideal A) (M : ModuleCat.{u} A)
    (h : IsIso (toComplementSections I M)) :
    IsZero (cohomologyWithSupportBase I M 0) ∧ IsZero (cohomologyWithSupportBase I M 1) := by
  have hrb : IsIso (baseComplementRestriction I M) := by
    have hdef : baseComplementRestriction I M =
        (ambientCohomologyZeroBaseIso M).hom ≫ toComplementSections I M := by
      rw [show toComplementSections I M =
          (ambientCohomologyZeroBaseIso M).inv ≫ baseComplementRestriction I M from rfl,
        ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [hdef]
    infer_instance
  have hr : IsIso ((complementRestriction I 0).app (tildeSheaf M)) :=
    isIso_of_reflects_iso _ (globalToBase A)
  obtain ⟨delta, hmono, hexact, hepi, -⟩ := exact_cohomologyWithSupport_sequence I M
  have hz0 : (supportInclusion I 0).app (tildeSheaf M) ≫
      (complementRestriction I 0).app (tildeSheaf M) = 0 := hexact.toIsComplex.zero 0
  have hz1 : (complementRestriction I 0).app (tildeSheaf M) ≫
      (delta 0).app (tildeSheaf M) = 0 := hexact.toIsComplex.zero 1
  refine ⟨Functor.map_isZero _ ?_, Functor.map_isZero _ ?_⟩
  · have hi0 : (supportInclusion I 0).app (tildeSheaf M) = 0 := by
      rw [← Category.comp_id ((supportInclusion I 0).app (tildeSheaf M)),
        ← IsIso.hom_inv_id ((complementRestriction I 0).app (tildeSheaf M)),
        ← Category.assoc, hz0, zero_comp]
    rw [IsZero.iff_id_eq_zero]
    exact hmono.right_cancellation (𝟙 _) 0 (by rw [Category.id_comp, zero_comp, hi0])
  · have hd0 : (delta 0).app (tildeSheaf M) = 0 := by
      rw [← Category.id_comp ((delta 0).app (tildeSheaf M)),
        ← IsIso.inv_hom_id ((complementRestriction I 0).app (tildeSheaf M)),
        Category.assoc, hz1, comp_zero]
    rw [IsZero.iff_id_eq_zero]
    exact hepi.left_cancellation (𝟙 _) 0 (by rw [Category.comp_id, comp_zero, hd0])

/-- **Stacks Project, Tag 0BK0 (4) for a principal ideal, the vanishing.**  Let `A` be a
Noetherian ring, let `f : A`, let `X = Spec A`, let `Z = V(f)` and let `U = X ∖ Z`.  If the
canonical map `M ⟶ Γ(U, M̃)` is an isomorphism then the local cohomology modules `H⁰_Z(M)` and
`H¹_Z(M)` are zero. -/
@[stacks 0BK0 "(4), the vanishing, principal ideal, for a module whose canonical map to the \
sections over the complement is an isomorphism"]
theorem isZero_localCohomology_of_isIso_span_singleton [IsNoetherianRing A] (f : A)
    (M : ModuleCat.{u} A) (h : IsIso (toComplementSections (Ideal.span {f}) M)) :
    IsZero ((localCohomologySpanSingleton A f 0).obj M) ∧
      IsZero ((localCohomologySpanSingleton A f 1).obj M) := by
  obtain ⟨h0, h1⟩ := isZero_cohomologyWithSupport_of_isIso (Ideal.span {f}) M h
  exact ⟨h0.of_iso (cohomologyWithSupportTildeSpanSingletonIso f M 0).symm,
    h1.of_iso (cohomologyWithSupportTildeSpanSingletonIso f M 1).symm⟩

end Stacks.LocalCohomologySequence

end
