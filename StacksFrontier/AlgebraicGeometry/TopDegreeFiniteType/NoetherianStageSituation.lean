module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CohomologyFilteredColimits
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsUnitor
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.AffineModuleFinite
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.BaseChangeFinite

/-!
# The top-degree base-change situation of a proper morphism onto an affine base

Paragraph four of the proof of [Stacks, Tag 0EX4] — which is also the proof of
[Stacks, Tag 0EX5] — applies [Stacks, Tag 0EX3] to the morphism `g : X ⟶ S` of the Noetherian
stage. In this development the hypotheses of that tag are packaged as
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation`, so applying the tag means producing
such a structure. That structure is
`Stacks.AlgebraicGeometry.TopDegreeFiniteType.situation`; this file supplies the vanishing
hypothesis it takes, and then reconciles the `Γ(S, ⊤)`-module structure the structure imposes
on `H ᵈ (X, F)` with the one the rest of this development uses.

## Main results

* `Stacks.AlgebraicGeometry.NoetherianStageSituation.vanishes_above_of_forall_isCoherent`: the
  parameter `hvan` below, produced from the vanishing for **coherent** modules only. This is the
  adapter for [Stacks, Tag 02V7], which is stated for coherent modules and in terms of
  cohomology rather than of the sheaf.
* `Stacks.AlgebraicGeometry.NoetherianStageSituation.topDegreeCohomology_eq`: the
  Eilenberg-Watts module `H ᵈ (X, F)` of that situation **is** the cohomology of `F` restricted
  along `g.appTop`, not merely isomorphic to it.

## Implementation notes

**Why the vanishing is a parameter.** The vanishing above the fibre dimension is
[Stacks, Tag 0E7D] (equivalently, over a locally Noetherian base, [Stacks, Tag 02V7]), and at a
general `d` it is a theorem in its own right whose proof needs more than this file. It is
therefore carried as the parameter `hvan`, in exactly the shape of the `vanishes_above` field —
about the **sheaf** `R ʲ g_* G` on `S`, indexed by `ℤ`, for every quasi-coherent `G`. Over an
affine base that is interchangeable with the vanishing of `H ʲ (X, G)` by
`…TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_of_isZero_cohomology`.

**The two `Γ(S, ⊤)`-module structures on `H ᵈ (X, F)`, and why they agree on the nose.** The
situation presents `X` as a scheme over `Spec Γ(S, ⊤)` through
`S.isoSpec`, so the algebra structure it uses on `Γ(X, ⊤)` is
`AlgebraicGeometry.baseRingToSections` of `Over.mk (g ≫ S.isoSpec.hom)`, whereas the rest of
this development restricts scalars along `g.appTop` directly.
`baseRingToSections_eq_appTop` identifies the two ring maps, so `topDegreeCohomology_eq` is a
`congrArg` and not a transport.

That identification cannot be closed by rewriting in the category: `CommRingCat.of ↑Γ(S, ⊤)`
against `Γ(S, ⊤)`, and `(Over.mk (g ≫ S.isoSpec.hom)).left` against `X`, are `rfl`-equal but
not syntactically equal, so the proof drops to elements and restates the goal with `show`.
`AlgebraicGeometry.Scheme.toSpecΓ_appTop` also has to be applied with `rw` rather than
`simp only`, because it carries a `backward.defeqAttrib` option.

**`HasDerivedCategory.standard` is given priority `10000`.** With the plain local instance the
locally-small instance reached through the Eilenberg-Watts imports wins, and `rightDerivedPlus`
then elaborates at hom universes that do not match the library lemmas; the symptom is a
mismatch whose two sides print identically.

No `@[stacks]` attribute is attached. Nothing here is a statement the source makes: the
situation is this development's packaging of the hypotheses of [Stacks, Tag 0EX3], and the
module identification is bookkeeping.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 0EX5](https://stacks.math.columbia.edu/tag/0EX5)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

namespace Stacks.AlgebraicGeometry.NoetherianStageSituation

attribute [local instance 10000] HasDerivedCategory.standard

noncomputable section

variable {X S : Scheme.{u}} (g : X ⟶ S)

section AlgebraMap

variable [IsAffine S]

/-- **The two ring maps `Γ(S, ⊤) ⟶ Γ(X, ⊤)` agree.** The structure of `X` as a scheme over
`Spec Γ(S, ⊤)`, which is what makes `Γ(X, ⊤)` a `Γ(S, ⊤)`-algebra for the Eilenberg-Watts
machinery, induces on global sections the map `g` itself induces. -/
lemma baseRingToSections_eq_appTop :
    AlgebraicGeometry.baseRingToSections Γ(S, ⊤)
        (CategoryTheory.Over.mk (g ≫ S.isoSpec.hom)) (op ⊤) = g.appTop.hom := by
  have h1 : (Opens.leTop (⊤ : X.Opens)).op = 𝟙 (op (⊤ : X.Opens)) := Subsingleton.elim _ _
  rw [AlgebraicGeometry.baseRingToSections]
  simp only [CategoryTheory.Over.mk_hom, Scheme.Hom.comp_appTop, Scheme.isoSpec_hom]
  rw [Scheme.toSpecΓ_appTop]
  ext r
  change (X.ringCatSheaf.obj.map (Opens.leTop (⊤ : X.Opens)).op).hom
      (g.appTop.hom ((Scheme.ΓSpecIso Γ(S, ⊤)).hom.hom
        ((Scheme.ΓSpecIso Γ(S, ⊤)).inv.hom r))) = g.appTop.hom r
  rw [h1]
  simp
  rfl

end AlgebraMap

section Coherent

variable [IsProper g] [IsAffine S] [IsNoetherian S]

/-- For a proper morphism `g : X ⟶ S` to an affine Noetherian scheme, if `H ʲ (X, G) = 0` for
every coherent `G` and every natural number `j > i`, then `R ʲ g_* G = 0` for every
quasi-coherent `G` and every integer `j > i`. -/
theorem vanishes_above_of_forall_isCoherent (i : ℕ)
    (h : ∀ j : ℕ, i < j → ∀ G : X.Modules, G.IsCoherent →
      IsZero (((moduleGlobalSections X).rightDerivedPlus (j : ℤ)).obj G)) :
    ∀ j : ℤ, (i : ℤ) < j → ∀ G : X.Modules, G.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus j).obj G) := by
  have _ : CompactSpace (X : Type u) := QuasiCompact.compactSpace_of_compactSpace g
  have _ : QuasiSeparatedSpace (X : Type u) := quasiSeparatedSpace_of_quasiSeparated g
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  intro j hj G hG
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ℤ) = j :=
    ⟨j.toNat, Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg i) hj.le)⟩
  have hk : i < k := by exact_mod_cast hj
  have _ : G.IsQuasicoherent := hG
  refine isZero_rightDerivedPlus_pushforward_of_isZero_cohomology g (k : ℤ) G ?_
  refine isZero_rightDerivedPlus_moduleGlobalSections_of_forall_isFinitePresentation
    X k G fun G' hG' => ?_
  exact h k hk G'
    (Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation G' hG')

end Coherent

section Situation

variable [IsProper g] [IsAffine S] (i : ℕ)
  (hvan : ∀ j : ℤ, (i : ℤ) < j → ∀ G : X.Modules, G.IsQuasicoherent →
    IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus j).obj G))

/-- The base-changed source of the situation is `X` itself. -/
lemma situation_X' : (TopDegreeFiniteType.situation g i hvan).X' = X := rfl

/-- The base-changed base of the situation is `S` itself. -/
lemma situation_Y' : (TopDegreeFiniteType.situation g i hvan).Y' = S := rfl

/-- The degree of the situation is `i`. -/
lemma situation_d : (TopDegreeFiniteType.situation g i hvan).d = i := rfl

/-- **The Eilenberg-Watts module of the situation is the cohomology of `F` over `Γ(S, ⊤)`.** An
equality, not an isomorphism: the two `Γ(S, ⊤)`-algebra structures on `Γ(X, ⊤)` are the same
ring map by `baseRingToSections_eq_appTop`. -/
lemma topDegreeCohomology_eq (F : X.Modules) (hF : F.IsQuasicoherent) :
    (TopDegreeFiniteType.situation g i hvan).topDegreeCohomology ⟨F, hF⟩ =
      (ModuleCat.restrictScalars g.appTop.hom).obj
        (((moduleGlobalSections X).rightDerived i).obj F) :=
  congrArg (fun φ => (ModuleCat.restrictScalars φ).obj
    (((moduleGlobalSections X).rightDerived i).obj F)) (baseRingToSections_eq_appTop g)

end Situation

end

end Stacks.AlgebraicGeometry.NoetherianStageSituation

end
