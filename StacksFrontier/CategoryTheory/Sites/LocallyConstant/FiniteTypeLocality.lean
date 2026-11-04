module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
import StacksCore.Tactic.StacksAttribute

/-!
# Local constancy of finite type is a local condition on the site

Let `(C, J)` be a site and `Λ` a commutative ring. A sheaf of `Λ`-modules which, on each member
of a covering family of each object, restricts to a sheaf that is locally constant of finite
type is itself locally constant of finite type.

This is the statement that the condition of Tag 093U can be checked locally, and it is what
lets a conclusion reached on the members of a covering family — as in Tag 094G, whose
conclusion is a statement about the slice sites `C/V i` — be assembled into a statement on `C`.
Tag 094H needs it in exactly that shape.

## Main results

* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_of_local`: the condition of being
  a locally constant sheaf of `Λ`-modules of finite type is local on the site.

## Implementation notes

The content is the comparison between a slice of a slice and a slice. The hypothesis supplies,
for a covering family `U i ⟶ X`, a trivialization of the restricted sheaf over an object `Y` of
the slice category `Over (U i)` for the *localized* topology, that is, on the site
`(J.over (U i)).over Y`. The conclusion needs a trivialization on `J.over Y.left`. These two
sites are identified by `CategoryTheory.Over.iteratedSliceEquiv`, an equivalence of categories
which is a morphism of sites in both directions, and the identification carries constant sheaves
to constant sheaves on the same module: that is
`CategoryTheory.Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility`, which says that
pushing a presheaf forward along a dense subsite inclusion commutes with sheafification, applied
to a constant presheaf (whose pushforward along a functor is again the constant presheaf on the
same object).

No pullbacks and no final object are assumed in `C`. The covering family of the conclusion is
the family of composites `(V i j).left ⟶ U i ⟶ X`, and that it is covering is
`GrothendieckTopology.transitive`: pulling it back along a member `U i ⟶ X` of the outer family
contains the image under `Over.forget` of the inner family, which is covering for `J (U i)`
because `(J.over (U i))`-covers of `Over.mk (𝟙 (U i))` are exactly `J (U i)`-covers of `U i`.

The module universe is `max u v w`, as in
`Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf`. On the slice site `C/U` the same
universe is reached as `max (max u v) v w`, which is `max u v w`, so the hypothesis and the
conclusion are the same condition at the same module universe; only the index universe of the
covering families changes, from `max u v` to `max (max u v) v`, and those are equal too.

## References

* [Stacks Project, Tag 094H](https://stacks.math.columbia.edu/tag/094H)
* [Stacks Project, Tag 094G](https://stacks.math.columbia.edu/tag/094G)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ConstantSheaf

universe w v u

section IteratedSlice

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {D : Type*} [Category* D]

/-- Pushing sheaves forward along the equivalence identifying `Over Y`, for `Y` an object of
`Over X`, with `Over Y.left` is an equivalence of categories of sheaves. -/
@[sga "3 IV 4.5.4" "partial"]
theorem iteratedSliceBackward_sheafPushforward_isEquivalence (X : C) (Y : Over X) :
    (Y.iteratedSliceBackward.sheafPushforwardContinuous D
      (J.over Y.left) ((J.over X).over Y)).IsEquivalence :=
  (Equivalence.sheafCongr ((J.over X).over Y) (J.over Y.left)
    Y.iteratedSliceEquiv D).isEquivalence_functor

/-- The functor from `Over Y`, for `Y` an object of `Over X`, to `Over Y.left` is a dense
subsite for the localized topologies. -/
theorem iteratedSliceBackward_isDenseSubsite (X : C) (Y : Over X) :
    Y.iteratedSliceBackward.IsDenseSubsite (J.over Y.left) ((J.over X).over Y) :=
  inferInstanceAs (Y.iteratedSliceEquiv.inverse.IsDenseSubsite (J.over _) ((J.over _).over _))

attribute [local instance] iteratedSliceBackward_sheafPushforward_isEquivalence
  iteratedSliceBackward_isDenseSubsite

/-- Sheafification on a slice of a slice, transported from the slice it is equivalent to. -/
theorem hasWeakSheafify_over_over [∀ V : C, HasWeakSheafify (J.over V) D]
    (X : C) (Y : Over X) : HasWeakSheafify ((J.over X).over Y) D :=
  Functor.IsDenseSubsite.hasWeakSheafify_of_isEquivalence
    (J.over Y.left) ((J.over X).over Y) Y.iteratedSliceBackward D

attribute [local instance] hasWeakSheafify_over_over

/-- **A trivialization on a slice of a slice is a trivialization on a slice.** A sheaf whose
double restriction, first to `C/X` and then to `(C/X)/Y`, is the constant sheaf on `E` has
restriction to `C/Y.left` the constant sheaf on the same `E`. -/
def constantTrivializationFromIteratedSlice [∀ V : C, HasWeakSheafify (J.over V) D]
    (X : C) (Y : Over X) (F : Sheaf J D) (E : D)
    (e : (constantSheaf ((J.over X).over Y) D).obj E ≅ (F.over X).over Y) :
    (constantSheaf (J.over Y.left) D).obj E ≅ F.over Y.left :=
  (Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility
    (J.over Y.left) ((J.over X).over Y) Y.iteratedSliceBackward D).app
      ((Functor.const (Over Y)ᵒᵖ).obj E) ≪≫
    (Y.iteratedSliceBackward.sheafPushforwardContinuous D
      (J.over Y.left) ((J.over X).over Y)).mapIso e

end IteratedSlice

/-! ### Locality of the finite type locally constant condition -/

section Module

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type*) [CommRing Λ]

attribute [local instance] iteratedSliceBackward_sheafPushforward_isEquivalence

/-- **Being a locally constant sheaf of `Λ`-modules of finite type is a local condition.** If
every object `X` of the site has a covering family `U i ⟶ X` on each member of which the
restriction of `F` to `C/U i` is a locally constant sheaf of `Λ`-modules of finite type, then
`F` itself is one.

The covering family witnessing the conclusion at `X` is obtained by composing the given family
with, for each `i`, a family trivializing the restriction of `F` over the object
`Over.mk (𝟙 (U i))` of `Over (U i)`; its members' sources are objects of `C` lying over the
`U i`, and the trivializations transport along the slice-of-slice equivalence by
`Stacks.ConstantSheaf.constantTrivializationFromIteratedSlice`. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_of_local
    (F : Sheaf J (ModuleCat.{max u v w} Λ))
    (hF : ∀ X : C, ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧ ∀ i,
        IsFiniteTypeLocallyConstantModuleSheaf.{v, max u v, w} (J.over (U i)) Λ (F.over (U i))) :
    IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ F := by
  classical
  intro X
  obtain ⟨I, U, f, hf, hU⟩ := hF X
  choose I' V g hg hV using fun i => hU i (Over.mk (𝟙 (U i)))
  let V' (i : Σ j, I' j) : C := (V i.1 i.2).left
  let g' (i : Σ j, I' j) : V' i ⟶ X := (g i.1 i.2).left ≫ f i.1
  refine ⟨Σ i, I' i, V', g', ?_, ?_⟩
  · apply J.transitive hf
    intro Y a ha
    obtain ⟨Z, b, c, ⟨i⟩, rfl⟩ := ha
    rw [Sieve.pullback_comp]
    apply J.pullback_stable
    apply J.superset_covering (S := Sieve.ofArrows (fun j => (V i j).left)
      (fun j => (g i j).left))
    · intro Z a ha
      obtain ⟨W, b, c, ⟨j⟩, rfl⟩ := ha
      show (Sieve.ofArrows V' g') ((b ≫ (g i j).left) ≫ f i)
      rw [Category.assoc]
      exact (Sieve.ofArrows V' g').downward_closed
        (Sieve.le_generate _ _ _ ⟨⟨i, j⟩⟩) b
    · simpa only [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] using hg i
  · rintro ⟨i, j⟩
    obtain ⟨E, hE, ⟨e⟩⟩ := hV i j
    exact ⟨E, hE, ⟨constantTrivializationFromIteratedSlice J (U i) (V i j) F E e⟩⟩

end Module

end Stacks.ConstantSheaf

end
