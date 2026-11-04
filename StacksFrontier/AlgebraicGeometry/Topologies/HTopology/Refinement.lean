module

public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import StacksFrontier.CategoryTheory.Sites.Pretopology.CombinatorialEquivalence

/-!
# Base change, pushforward and reindexing of refinements

A family of morphisms with fixed target `S` in a category `C` is
`CategoryTheory.PreZeroHypercover S`, and a refinement of one family by another is
`CategoryTheory.PreZeroHypercover.Hom`.  Mathlib provides the two operations on families
themselves — base change `CategoryTheory.PreZeroHypercover.pullback₂` and composition with a
morphism of the targets `CategoryTheory.PreZeroHypercover.pushforward` — but not their effect
on refinements.  This file supplies that, together with the canonical refinement of a family
by the pushforward of its own base change.

## Main definitions

* `CategoryTheory.PreZeroHypercover.Hom.pushforward`: a refinement composed with a morphism
  of the targets.
* `CategoryTheory.PreZeroHypercover.Hom.pullback₂Map` and
  `CategoryTheory.PreZeroHypercover.Hom.pullback₂`: the base change of a refinement, by
  index and as a refinement.
* `CategoryTheory.PreZeroHypercover.pullback₂PushforwardHom`: the base change of a family
  along `g`, pushed forward along `g` again, refines the family; the refinement morphisms are
  the first projections.
* `CategoryTheory.PreZeroHypercover.Hom.toReindex`: a family refines any reindexing of itself
  along an equivalence of index types.

## Main results

* `CategoryTheory.PreZeroHypercover.eqToHom_f`: transporting along an equality of indices
  before applying the family returns the family.
* `CategoryTheory.PreZeroHypercover.combinatoriallyEquivalent_reindex`: a family is
  combinatorially equivalent to any reindexing of itself along an equivalence.

## Implementation notes

The two index universes of the families are kept independent, as they are for
`CategoryTheory.PreZeroHypercover.Hom` itself.  Base change and pushforward leave the index
type and the index map untouched; only the sources and the refinement morphisms change.

The component of the base-changed refinement is given a name of its own,
`CategoryTheory.PreZeroHypercover.Hom.pullback₂Map`, because its defining property is an
equation between morphisms out of a fibre product indexed by the index type of the *original*
family, while the field it fills is indexed by that of the base-changed family; the two agree
definitionally but not syntactically, so the fibre products of the base-changed family are
not available to instance synthesis.  For the same reason the hypothesis that the relevant
fibre products exist is named and applied explicitly.
-/

@[expose] public section

namespace CategoryTheory.PreZeroHypercover

open CategoryTheory.Limits

universe w w' v u

variable {C : Type u} [Category.{v} C]

/-- Transporting a source along an equality of indices and then applying the family returns
the family at the original index. -/
lemma eqToHom_f {S : C} {E : PreZeroHypercover.{w} S} {i j : E.I₀} (h : i = j) :
    eqToHom (congrArg E.X h) ≫ E.f j = E.f i := by
  cases h; simp

/-- A family refines any reindexing of itself along an equivalence of index types: the index
map is the inverse equivalence and the refinement morphisms are the transports. -/
def Hom.toReindex {S : C} (E : PreZeroHypercover.{w} S) {ι : Type w'} (e : ι ≃ E.I₀) :
    E.Hom (E.reindex e) where
  s₀ i := e.symm i
  h₀ i := eqToHom (congrArg E.X (e.apply_symm_apply i).symm)
  w₀ i := eqToHom_f (e.apply_symm_apply i).symm

/-- A family is combinatorially equivalent to any reindexing of itself along an equivalence
of index types. -/
lemma combinatoriallyEquivalent_reindex {S : C} (E : PreZeroHypercover.{w} S) {ι : Type w'}
    (e : ι ≃ E.I₀) : CombinatoriallyEquivalent E (E.reindex e) :=
  ⟨⟨fun i ↦ e.symm i, fun i ↦ congrArg E.X (e.apply_symm_apply i).symm,
      fun i ↦ (eqToHom_f (e.apply_symm_apply i).symm).symm⟩,
    ⟨fun j ↦ e j, fun _ ↦ rfl, fun _ ↦ (Category.id_comp _).symm⟩⟩

/-- A refinement of families with target `S`, composed with a morphism `g : S ⟶ T` of the
targets, is a refinement of the pushed-forward families. -/
def Hom.pushforward {S T : C} {E : PreZeroHypercover.{w} S} {F : PreZeroHypercover.{w'} S}
    (φ : E.Hom F) (g : S ⟶ T) : (E.pushforward g).Hom (F.pushforward g) where
  s₀ := φ.s₀
  h₀ := φ.h₀
  w₀ i := (Category.assoc (φ.h₀ i) (F.f (φ.s₀ i)) g).symm.trans
    (congrArg (fun k ↦ k ≫ g) (φ.w₀ i))

/-- The base change of a family along `g : S ⟶ T`, pushed forward along `g` again, refines
the original family: the refinement morphism at an index is the first projection of the
fibre product. -/
noncomputable def pullback₂PushforwardHom {S T : C} (g : S ⟶ T) (E : PreZeroHypercover.{w} T)
    [hpb : ∀ i, HasPullback (E.f i) g] : ((E.pullback₂ g).pushforward g).Hom E where
  s₀ i := i
  h₀ i := @pullback.fst _ _ _ _ _ (E.f i) g (hpb i)
  w₀ i := @pullback.condition _ _ _ _ _ (E.f i) g (hpb i)

/-- The component at one index of the base change of a refinement along `g`: the morphism of
fibre products induced by the refinement morphism `E.X i ⟶ F.X (φ.s₀ i)` over the target. -/
noncomputable def Hom.pullback₂Map {S T : C} (g : S ⟶ T) {E : PreZeroHypercover.{w} T}
    {F : PreZeroHypercover.{w'} T} [∀ i, HasPullback (E.f i) g]
    [∀ i, HasPullback (F.f i) g] (φ : E.Hom F) (i : E.I₀) :
    pullback (E.f i) g ⟶ pullback (F.f (φ.s₀ i)) g :=
  pullback.lift (pullback.fst (E.f i) g ≫ φ.h₀ i) (pullback.snd (E.f i) g)
    (by rw [Category.assoc, φ.w₀]; exact pullback.condition)

/-- Base change of a refinement along `g : S ⟶ T`: if `E` refines `F` over `T`, then the base
change of `E` refines the base change of `F` over `S`. -/
noncomputable def Hom.pullback₂ {S T : C} (g : S ⟶ T) {E : PreZeroHypercover.{w} T}
    {F : PreZeroHypercover.{w'} T} [∀ i, HasPullback (E.f i) g]
    [∀ i, HasPullback (F.f i) g] (φ : E.Hom F) :
    (E.pullback₂ g).Hom (F.pullback₂ g) where
  s₀ := φ.s₀
  h₀ i := φ.pullback₂Map g i
  w₀ _ := pullback.lift_snd _ _ _

end CategoryTheory.PreZeroHypercover
