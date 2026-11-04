module

public import StacksFrontier.AlgebraicGeometry.CardShape.Basic
public import StacksFrontier.AlgebraicGeometry.FinitelyPresentableComposition.AlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.SubalgebraSectionsResidue.Basic

/-!
# The finite-presentation half of [Stacks, Tag 0817], reduced to two propositions

Part (2) of [Stacks, Tag 0817] asks that an integral quasi-coherent algebra `A` on a
quasi-compact quasi-separated scheme be a directed colimit, over a preorder in `Type u`, of
quasi-coherent algebras that are **both finite and of finite presentation**.  It splits into three
pieces:

* the colimit over the finite quasi-coherent subalgebras of `A`, which is part (1);
* an approximation of each finite quasi-coherent algebra by finite, finitely presented ones,
  which is [Stacks, Tag 086N];
* the finite presentability, *as objects of `Stacks.RelativeSpec.AlgebraSheaf X`*, of the
  approximating algebras, which is [Stacks, Tag 01BS] — the hypothesis `hfp` of
  `Stacks.FinitelyPresentableComposition.exists_directed_index_algebraSheaf`.

This file composes them:
`Stacks.AlgebraicGeometry.Tag0817CardShape.exists_small_index_finite_of_isColimit` followed by
`Stacks.FinitelyPresentableComposition.exists_directed_index_algebraSheaf`, with the inner systems
chosen for the objects of the reindexed outer diagram, so that part (2) follows from part (1) and
the two propositions below.  Part (2) itself is
`Stacks.AlgebraicGeometry.Tag0817PartTwo.exists_small_index_finite_finitePresentation`.

## Main definitions

* `Tag086NForAlgebraSheaves X`: every quasi-coherent finite algebra sheaf on `X` is the colimit of
  a filtered system, indexed in `Type u`, of quasi-coherent finite finitely presented algebra
  sheaves.  This is [Stacks, Tag 086N] with the index universe [Stacks, Tag 0817] asks for.
* `Tag01BSForAlgebraSheaves X`: every quasi-coherent finite finitely presented algebra sheaf on
  `X` is a finitely presentable object of `Stacks.RelativeSpec.AlgebraSheaf X`.  This is
  [Stacks, Tag 01BS] in the vocabulary `CategoryTheory.IsFinitelyPresentable`.
* `FiniteApproximableByFinitePresentation X`: the two fused into one proposition — the
  approximating systems of `Tag086NForAlgebraSheaves` with their stages additionally finitely
  presentable.  It is **weaker** than the conjunction, since the presentability is asked only of
  the algebras that actually occur in an approximating system.

## Main results

* `exists_small_index_finite_finitePresentation_of_isColimit`: part (2) of [Stacks, Tag 0817]
  from part (1)'s colimit plus `FiniteApproximableByFinitePresentation`.  No hypothesis on `X` is
  used.
* `exists_small_index_finite_finitePresentation_of_affineCover_hit`: the same with part (1)'s
  colimit replaced by the hypothesis
  `Stacks.AlgebraicGeometry.SubalgebraSectionsResidue.HitByFiniteTypeAlgebra` at the members of an
  affine covering of `X`.
* `finiteApproximableByFinitePresentation_of`: the fused proposition from the two tags separately.
* `tag086NForAlgebraSheaves_of_finiteApproximableByFinitePresentation`: the fused proposition
  implies tag 086N's half.

## Implementation notes

The outer system has to be reindexed to `Type u` *before* the inner systems are chosen, not after:
`Stacks.FinitelyPresentableComposition.exists_directed_index_algebraSheaf` requires its outer index
to be a `CategoryTheory.SmallCategory` on a type in `Type u`, while the finite quasi-coherent
subalgebras of `A` form a full subcategory of `CategoryTheory.Subobject A`, which lies in
`Type (u + 1)`.  Reindexing first also means the inner systems are chosen for the objects of the
reindexed diagram, which is why `FiniteApproximableByFinitePresentation` quantifies over all
quasi-coherent finite algebra sheaves rather than over the subalgebras of `A`: after reindexing,
the objects of the outer diagram are only known to *be* quasi-coherent and finite.

`FiniteApproximableByFinitePresentation` puts the smallness of the inner index inside the
existential as `Type u` together with a `CategoryTheory.SmallCategory` witness, which is the shape
`Stacks.FinitelyPresentableComposition.exists_isColimit_of_twoStage` concludes in; the category
instance is then an ordinary local hypothesis, which instance search uses, so the functor binder
after it elaborates.

## References

* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 086N](https://stacks.math.columbia.edu/tag/086N)
* [Stacks Project, Tag 01BS](https://stacks.math.columbia.edu/tag/01BS)
* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeSpec Stacks.AlgebraicGeometry.FiniteSubalgebras

universe u

namespace Stacks.AlgebraicGeometry.Tag0817FinitePresentationResidue

attribute [local instance] Cardinal.fact_isRegular_aleph0

variable {X : Scheme.{u}}

/-- **[Stacks, Tag 086N] for algebra sheaves, with the index in the universe [Stacks, Tag 0817]
asks for.**

Every quasi-coherent finite sheaf of commutative `𝒪_X`-algebras is the colimit of a filtered
system, indexed by a small category in `Type u`, all of whose objects are quasi-coherent, finite
and of finite presentation. -/
def Tag086NForAlgebraSheaves (X : Scheme.{u}) : Prop :=
  ∀ B : AlgebraSheaf X, B.IsQuasicoherent → B.IsFinite →
    ∃ (K : Type u) (_ : SmallCategory K) (_ : IsFiltered K) (E : K ⥤ AlgebraSheaf X)
      (σ : E ⟶ (Functor.const K).obj B) (_ : IsColimit (Cocone.mk B σ)),
      ∀ k, (E.obj k).IsQuasicoherent ∧ (E.obj k).IsFinite ∧ (E.obj k).IsFinitePresentation

/-- **[Stacks, Tag 01BS] for algebra sheaves, in the vocabulary the composition consumes.**

Every quasi-coherent finite finitely presented sheaf of commutative `𝒪_X`-algebras is a finitely
presentable object of `Stacks.RelativeSpec.AlgebraSheaf X`, i.e. morphisms out of it into a
filtered colimit factor through a stage, essentially uniquely. -/
def Tag01BSForAlgebraSheaves (X : Scheme.{u}) : Prop :=
  ∀ C : AlgebraSheaf X, C.IsQuasicoherent → C.IsFinite → C.IsFinitePresentation →
    IsFinitelyPresentable.{u} C

/-- **The residue of the finite-presentation half of [Stacks, Tag 0817], as one proposition.**

Every quasi-coherent finite sheaf of commutative `𝒪_X`-algebras is the colimit of a filtered
system, indexed in `Type u`, of quasi-coherent finite finitely presented algebra sheaves **which
are finitely presentable objects**.

This is [Stacks, Tag 086N] with [Stacks, Tag 01BS] asked of the approximating algebras only, and
it is what `Stacks.FinitelyPresentableComposition.exists_directed_index_algebraSheaf` needs. -/
def FiniteApproximableByFinitePresentation (X : Scheme.{u}) : Prop :=
  ∀ B : AlgebraSheaf X, B.IsQuasicoherent → B.IsFinite →
    ∃ (K : Type u) (_ : SmallCategory K) (_ : IsFiltered K) (E : K ⥤ AlgebraSheaf X)
      (σ : E ⟶ (Functor.const K).obj B) (_ : IsColimit (Cocone.mk B σ)),
      ∀ k, ((E.obj k).IsQuasicoherent ∧ (E.obj k).IsFinite ∧ (E.obj k).IsFinitePresentation) ∧
        IsFinitelyPresentable.{u} (E.obj k)

/-- **The two tags separately give the fused residue.** -/
theorem finiteApproximableByFinitePresentation_of (h086N : Tag086NForAlgebraSheaves X)
    (h01BS : Tag01BSForAlgebraSheaves X) : FiniteApproximableByFinitePresentation X := by
  intro B hBqc hBfin
  obtain ⟨K, _, _, E, σ, hσ, hE⟩ := h086N B hBqc hBfin
  exact ⟨K, inferInstance, inferInstance, E, σ, hσ,
    fun k => ⟨hE k, h01BS _ (hE k).1 (hE k).2.1 (hE k).2.2⟩⟩

/-- **The fused residue implies [Stacks, Tag 086N]'s half of it**: what the composition needs is
the finite presentability of the algebras occurring in *some* approximating system, not of every
quasi-coherent finite finitely presented algebra sheaf. -/
theorem tag086NForAlgebraSheaves_of_finiteApproximableByFinitePresentation
    (h : FiniteApproximableByFinitePresentation X) : Tag086NForAlgebraSheaves X := by
  intro B hBqc hBfin
  obtain ⟨K, _, _, E, σ, hσ, hE⟩ := h B hBqc hBfin
  exact ⟨K, inferInstance, inferInstance, E, σ, hσ, fun k => (hE k).1⟩

/-- **Part (2) of [Stacks, Tag 0817], from part (1)'s colimit and the fused
proposition.**

Let `A` be an integral quasi-coherent sheaf of commutative `𝒪_X`-algebras whose canonical cocone
of finite quasi-coherent subalgebras is colimiting, and suppose every quasi-coherent finite
algebra sheaf on `X` is approximated by finitely presentable quasi-coherent finite finitely
presented ones.  Then there are an index type in `Type u`, a nonempty directed preorder on it, a
diagram of algebra sheaves and a colimiting cocone with vertex `A`, every object of the diagram
being quasi-coherent, finite and of finite presentation.

No hypothesis on `X` is used: neither quasi-compactness, nor quasi-separatedness, nor affineness.
-/
theorem exists_small_index_finite_finitePresentation_of_isColimit (A : AlgebraSheaf X)
    (hAqc : A.IsQuasicoherent) (hAint : A.IsIntegral)
    (hcolim : Nonempty (IsColimit (finiteSubalgebraCocone A)))
    (happrox : FiniteApproximableByFinitePresentation X) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf X) (s : F ⟶ (Functor.const I).obj A)
      (_ : IsColimit (Cocone.mk A s)),
      ∀ i, (F.obj i).IsQuasicoherent ∧ (F.obj i).IsFinite ∧
        (F.obj i).IsFinitePresentation := by
  obtain ⟨I, _, _, _, D, t, ht, hD⟩ :=
    Tag0817CardShape.exists_small_index_finite_of_isColimit A hAqc hAint hcolim
  choose K cat filt E σ hσ hE using fun i => happrox (D.obj i) (hD i).1 (hD i).2
  let _ : ∀ i, SmallCategory (K i) := cat
  let _ : ∀ i, IsFiltered (K i) := filt
  exact Stacks.FinitelyPresentableComposition.exists_directed_index_algebraSheaf t σ ht hσ
    (Stacks.FinitelyPresentableComposition.twoStagePresentable_of_isFinitelyPresentable t σ ht hσ
      fun i k => (hE i k).2)
    (fun B => B.IsQuasicoherent ∧ B.IsFinite ∧ B.IsFinitePresentation)
    (fun i k => (hE i k).1)

/-- **Part (2) of [Stacks, Tag 0817] from a sections hypothesis and the approximation.**

Part (1)'s colimit is replaced by
`Stacks.AlgebraicGeometry.SubalgebraSectionsResidue.HitByFiniteTypeAlgebra` at the members of a
covering of `X` by affine opens — a quasi-coherent algebra sheaf of finite type, any morphism to
`A`, and a section mapping to the given one.  No hypothesis on `X` is used. -/
theorem exists_small_index_finite_finitePresentation_of_affineCover_hit (A : AlgebraSheaf X)
    (hAqc : A.IsQuasicoherent) (hAint : A.IsIntegral)
    {ι : Type*} (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i))
    (hcover : ∀ p : X, ∃ i, p ∈ V i)
    (hhit : ∀ (i : ι) (m : (Under.right A).obj.obj (op (V i))),
      SubalgebraSectionsResidue.HitByFiniteTypeAlgebra A (V i) m)
    (happrox : FiniteApproximableByFinitePresentation X) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf X) (s : F ⟶ (Functor.const I).obj A)
      (_ : IsColimit (Cocone.mk A s)),
      ∀ i, (F.obj i).IsQuasicoherent ∧ (F.obj i).IsFinite ∧
        (F.obj i).IsFinitePresentation :=
  exists_small_index_finite_finitePresentation_of_isColimit A hAqc hAint
    (SubalgebraSectionsResidue.nonempty_isColimit_finiteSubalgebraCocone_of_affineCover_hit
      A hAqc hAint V hV hcover hhit) happrox

/-! ### Comparison with the source statement -/

/-- Part (2) of [Stacks, Tag 0817], binder for binder, with the two extra hypotheses `hcolim` and
`happrox` made explicit. -/
example (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (A : AlgebraSheaf X) (hAqc : AlgebraSheaf.IsQuasicoherent A)
    (hAint : AlgebraSheaf.IsIntegral A)
    (hcolim : Nonempty (IsColimit (finiteSubalgebraCocone A)))
    (happrox : FiniteApproximableByFinitePresentation X) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf X)
      (t : F ⟶ (Functor.const I).obj A) (_ : IsColimit (Cocone.mk A t)),
      ∀ i, AlgebraSheaf.IsQuasicoherent (F.obj i) ∧ AlgebraSheaf.IsFinite (F.obj i) ∧
        AlgebraSheaf.IsFinitePresentation (F.obj i) :=
  exists_small_index_finite_finitePresentation_of_isColimit A hAqc hAint hcolim happrox

end Stacks.AlgebraicGeometry.Tag0817FinitePresentationResidue

end
