module

import Mathlib.CategoryTheory.Filtered.Final
public import StacksFrontier.CategoryTheory.EssentiallyConstant.Biproducts
public import StacksFrontier.CategoryTheory.EssentiallyConstant.Cofinal
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
public import StacksFrontier.CategoryTheory.Functor.Derived.Triangle
public import StacksFrontier.CategoryTheory.Localization.Saturated.Closure
public import StacksFrontier.CategoryTheory.Triangulated.Elementary
public import StacksFrontier.CategoryTheory.Functor.Derived.Morphisms
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived functors and direct sums

This file collects the formalizations of [Stacks, Tag 05SD], [Stacks, Tag 05T0].

## References

* [Stacks, Tag 05SD](https://stacks.math.columbia.edu/tag/05SD)
* [Stacks, Tag 05T0](https://stacks.math.columbia.edu/tag/05T0)
-/

section

/-!
# Derived functors and direct sums

Let `F : 𝒟 ⥤ 𝒟'` be an exact functor of triangulated categories and let `W` be a saturated
multiplicative system in `𝒟` compatible with the triangulation (Situation 05S8). The right
derived functor `RF` is *defined at* an object `X` when the ind-object
$$ X/W ⟶ 𝒟', \qquad (s : X ⟶ X') ⟼ F(X'), $$
is essentially constant, its value being `RF(X)`; dually `LF` is defined at `X` when the
pro-object on `W/X` is essentially constant (Tag 05S9). This file records how definedness and
the values interact with a direct sum `X ⊕ Y`: definedness at `X` and at `Y` gives definedness
at `X ⊕ Y`; conversely, definedness at `X ⊕ Y` gives definedness at `X` and at `Y` as soon as
`𝒟'` is Karoubian; and whenever the derived functor is defined at all three objects,
`RF(X ⊕ Y) = RF(X) ⊕ RF(Y)`, the identification being the one induced by the two projections of
the direct sum. The same for `LF`.

## Main results

## Proof outline

## Implementation notes

*The four matrix identities.* The four composites `RF(biprod.inl) ≫ RF(biprod.fst)` and its
three companions are computed by `comp_eq_of_isDerivedMap`: a morphism between
values which is compatible with the coprojections along every square, in the sense of Tag 05SA,
is determined by that compatibility (a value is a retract of a term of the ind-object, so two
morphisms out of it agreeing after every coprojection agree), and a composite of two such
morphisms is again one, for the composite morphism of `C`. The identity of `RF(X)` is the
morphism attached to `𝟙 X` and the zero morphism is the one attached to `0`; the latter is where
the cancellation axiom MS3 of the multiplicative system enters, a square
`0 ≫ b.hom = a.hom ≫ g` giving `a.hom ≫ g = 0`, hence `g ≫ q = 0` for some `q` of `W`, and only
then `F(g) ≫ ι_b = 0`. All of this needs of `W` no more than a left calculus of fractions, and of
`F` no more than that it preserve zero morphisms.

*Splitting the triangle.* The passage from the four matrix identities to the isomorphism is one
statement about biproducts in a pretriangulated category,
`isIso_biprod_lift_of_distTriang`: if `Triangle.mk u p₂ w` is distinguished and the
four morphisms `u, u₂, p₁, p₂` satisfy those identities, then
`biprod.desc u u₂` is invertible by Tag 05QT (the identity `u₂ ≫ p₂ = 𝟙` is a splitting of `p₂`)
and `biprod.lift p₁ p₂` is its inverse, because the four identities say exactly that
`biprod.desc u u₂ ≫ biprod.lift p₁ p₂ = 𝟙`. It is used once for `RF` and once for `LF`.

*Duality.* Both halves of the lemma are mirrors of each other, and each is read off the
corresponding conjunct of Tag 05SC: part (1) for `LF` is the second conjunct applied to the same
triangle `X ⟶ X ⊞ Y ⟶ Y ⟶ X⟦1⟧`, and the identification `LF(X ⊞ Y) = LF(X) ⊞ LF(Y)` splits
the triangle of values that conjunct produces, by the same
`isIso_biprod_lift_of_distTriang`, the four matrix identities now coming from
`comp_eq_of_isDerivedMapLeft`. Definedness of `LF` at `X` is essential constancy of
the pro-object as a diagram on `(W.Over ⊤ X)ᵒᵖ` (`exists_isLeftDerivedValueAt_iff`),
which is how part (2) for `LF` is reduced to the ind-object case in `Hᵒᵖ`.

*Part (2).* The converse direction, over a Karoubian target, is the source's cofinality argument
for `X/W × Y/W ⟶ (X ⊞ Y)/W` together with Tag 0A2G, and is recorded as the separate statements
`exists_isRightDerivedValueAt_of_biprod` and
`exists_isLeftDerivedValueAt_of_biprod`. Both run through
`isEssentiallyConstantInd_of_retract_of_final`, which composes the two directions of
Tag 0A1S with Tag 0A2G; the retract data are the four natural transformations
`mapInl`, `mapFst`, `mapInr`, `mapSnd` on the
ind-side and their opposites `mapFstOp` and companions on the pro-side.


## Implementation notes

*Faithfulness.* (1) No hypothesis is dead: `hW` (MS4) is what makes `W` closed under the direct
sum of two of its members and, with `IsCompatibleWithTriangulation` and exactness of `F`, is
consumed by Tag 05SC in part (1); Karoubian-ness of `𝒟'` is a hypothesis of part (2) only, where
the source uses it through Tag 0A2G, and is carried by that conjunct rather than by the theorem.
(2) The data are the source's: one class `W` of morphisms of the *source* category `𝒟`, the index
categories `X/W`, `Y/W`, `(X ⊕ Y)/W` of morphisms of `W` out of (resp. into) the object in
question, and the diagram valued in `𝒟'` through `F` — no localization of `𝒟` and no change of
`W`. (3) The identification `RF(X ⊕ Y) = RF(X) ⊕ RF(Y)` is pinned, not merely asserted: the two
morphisms out of the value at `X ⊞ Y` are required to satisfy the characterisation of Tag 05SA
for the projections `biprod.fst` and `biprod.snd`, which determines each of them uniquely, and
it is the biproduct comparison map built from those two that is asserted to be an isomorphism.
(4) Not degenerate: for `W = MorphismProperty.isomorphisms 𝒟` the object `𝟙 X` is initial in
`X/W` and terminal in `W/X`, so `RF` and `LF` are defined at every object with value `F(X)`
(Tag 05S9); all six conjuncts then have satisfiable hypotheses, and the last two say the true
and non-trivial thing that `F(X ⊞ Y) ≅ F X ⊞ F Y` through `F(biprod.fst)` and `F(biprod.snd)`.

*Direct sums.* The source's `X ⊕ Y` is the biproduct `X ⊞ Y`. Situation 05S8 has `𝒟` and `𝒟'`
additive, hence with binary biproducts; in Mathlib these are automatic for a pretriangulated
category, so no biproduct hypothesis appears.

*Generality of part (2).* The source's proof of part (2) uses no triangulated structure and no
exactness: it goes through cofinality of `X/W × Y/W ⟶ (X ⊕ Y)/W` — which needs only that `W` is
a saturated multiplicative system — and Tag 0A2G, which needs `𝒟'` additive and Karoubian and
`F` additive (to identify `F(X' ⊕ Y')` with `F(X') ⊕ F(Y')`). So the two middle conjuncts hold
for an additive `F` between additive categories with `𝒟'` Karoubian. They are stated here under
Situation 05S8, which is the source's hypothesis for the lemma as a whole; the generalization is
a separate statement, and no conjunct below is weakened by it.

*Definedness and values.* Following Tag 05S9 as stated in this project, "`RF` is defined at `X`"
is `∃ c, F.IsRightDerivedValueAt W X c`; a value is a cocone `c` with
`F.IsRightDerivedValueAt W X c`, and `RF(X)` is its vertex `c.pt`. Dually for `LF`, with cones.
The map `RF(f)` of Tag 05SA is not a named declaration in this project, so its characterisation —
compatibility with the coprojections along every commutative square `f ≫ b.hom = a.hom ≫ g` with
`a ∈ X/W` and `b ∈ Y/W` — is written out, as in the statements of Tags 05SA and 05SB.

*Duality.* The assertions for `LF` are given directly in the pro-object form, as Tag 05S9 gives
`IsLeftDerivedValueAt`, rather than as the assertions for `F.op` and `W.op`; the two agree through
the equivalence `(W.Over ⊤ X)ᵒᵖ ≌ W.op.Under ⊤ (Opposite.op X)`, which is a separate lemma. The
biproduct is self-dual, so the conclusions are not dualized.

*Equality of values.* The source writes `RF(X ⊕ Y) = RF(X) ⊕ RF(Y)`, an equality by abuse of
notation between objects each determined only up to unique isomorphism. Here it is the assertion
that the comparison morphism to `RF(X) ⊞ RF(Y)` is an isomorphism, which is the content and gives
the source's statement for every choice of values.


## References

* [StacksProject 05SD](https://stacks.math.columbia.edu/tag/05SD); the situation is Tag 05S8,
  definedness and values are Tag 05S9, the map `RF(f)` is Tag 05SA, the triangulated input is
  Tags 05QT and 05SC, and the Karoubian input is Tag 0A2G.
-/

@[expose] public section

namespace DerivedFunctorBiprod

open CategoryTheory (coprj map_comp_coprj)
open DerivedFunctorDerivable (exists_over_sq)

open CategoryTheory Limits Pretriangulated CategoryTheory.EssentiallyConstantInd

universe v₁ v₂ u₁ u₂

section Ind

variable {C : Type u₁} [Category.{v₁} C] {H : Type u₂} [Category.{v₂} H]
  {W : MorphismProperty C} {F : C ⥤ H}

/-- The ind-object at `X` whose essential constancy is definedness of `RF` at `X`:
`X/W ⟶ H`, `(s : X ⟶ X') ↦ F(X')`. -/
private abbrev indDiag (F : C ⥤ H) (W : MorphismProperty C) (X : C) : W.Under ⊤ X ⥤ H :=
  MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F

/-- A value of `RF` at `X` is a retract of a term of the ind-object, so a morphism out of it is
determined by its composites with the coprojections. -/
private lemma eq_of_coprj_comp_eq {X : C}
    {c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)}
    (hc : F.IsRightDerivedValueAt W X c) {Z : H} {α β : c.pt ⟶ Z}
    (h : ∀ a : W.Under ⊤ X, coprj c a ≫ α = coprj c a ≫ β) : α = β := by
  obtain ⟨a₀, r, hr, -⟩ := hc
  have hr' : r ≫ coprj c a₀ = 𝟙 c.pt := hr
  calc α = (r ≫ coprj c a₀) ≫ α := by rw [hr', Category.id_comp]
    _ = r ≫ coprj c a₀ ≫ β := by rw [Category.assoc, h a₀]
    _ = β := by rw [← Category.assoc, hr', Category.id_comp]

/-- **MS3**: a morphism of `C` killed by an object of `X/W` is killed outright after enlarging
its target in `Y/W`. -/
private lemma exists_under_postcomp_eq_zero [W.HasLeftCalculusOfFractions] [HasZeroMorphisms C]
    {X Y : C} (a : W.Under ⊤ X) (b : W.Under ⊤ Y) (g : a.right ⟶ b.right)
    (hg : a.hom ≫ g = 0) :
    ∃ (b' : W.Under ⊤ Y) (q : b.right ⟶ b'.right), b.hom ≫ q = b'.hom ∧ g ≫ q = 0 := by
  obtain ⟨V, t, ht, hteq⟩ :=
    MorphismProperty.HasLeftCalculusOfFractions.ext g 0 a.hom a.prop (by simp [hg])
  exact ⟨MorphismProperty.Under.mk ⊤ (b.hom ≫ t) (W.comp_mem _ _ b.prop ht), t, rfl,
    hteq.trans Limits.zero_comp⟩

/-- The composite of a coprojection with the image of a morphism killed by an object of `X/W`
vanishes. -/
private lemma map_comp_coprj_eq_zero [W.HasLeftCalculusOfFractions] [HasZeroMorphisms C]
    [HasZeroMorphisms H] [F.PreservesZeroMorphisms] {X Y : C}
    (c : Cocone (MorphismProperty.Under.forget W ⊤ Y ⋙ Under.forget Y ⋙ F))
    (a : W.Under ⊤ X) (b : W.Under ⊤ Y) (g : a.right ⟶ b.right) (hg : a.hom ≫ g = 0) :
    F.map g ≫ coprj c b = 0 := by
  obtain ⟨b', q, hq, hgq⟩ := exists_under_postcomp_eq_zero a b g hg
  calc F.map g ≫ coprj c b = F.map g ≫ F.map q ≫ coprj c b' := by
        rw [map_comp_coprj _ c q hq]
    _ = F.map (g ≫ q) ≫ coprj c b' := by rw [F.map_comp, Category.assoc]
    _ = 0 := by rw [hgq, F.map_zero, Limits.zero_comp]

end Ind

section Pins

variable {C : Type u₁} [Category.{v₁} C] {H : Type u₂} [Category.{v₂} H]
  (W : MorphismProperty C) (F : C ⥤ H)

/-- The identity of a value of `RF` at `X` is compatible with the coprojections along every
square for `𝟙 X`: it is the morphism `RF(𝟙 X)` of Tag 05SA. -/
lemma isDerivedMap_id {X : C}
    (c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F))
    (a b : W.Under ⊤ X) (g : a.right ⟶ b.right) (hg : 𝟙 X ≫ b.hom = a.hom ≫ g) :
    coprj c a ≫ 𝟙 c.pt = F.map g ≫ coprj c b := by
  rw [Category.comp_id, map_comp_coprj _ c g (by rw [← hg, Category.id_comp])]

/-- The zero morphism between values of `RF` is compatible with the coprojections along every
square for `0 : X ⟶ Y`: it is the morphism `RF(0)` of Tag 05SA. -/
private lemma isDerivedMap_zero [W.HasLeftCalculusOfFractions] [HasZeroMorphisms C]
    [HasZeroMorphisms H] [F.PreservesZeroMorphisms] {X Y : C}
    (c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F))
    (d : Cocone (MorphismProperty.Under.forget W ⊤ Y ⋙ Under.forget Y ⋙ F))
    (a : W.Under ⊤ X) (b : W.Under ⊤ Y) (g : a.right ⟶ b.right)
    (hg : (0 : X ⟶ Y) ≫ b.hom = a.hom ≫ g) :
    coprj c a ≫ (0 : c.pt ⟶ d.pt) = F.map g ≫ coprj d b := by
  rw [map_comp_coprj_eq_zero d a b g (by rw [← hg, Limits.zero_comp]), Limits.comp_zero]

/-- **Stacks 05SA**, functoriality. A morphism between values of `RF` compatible with the
coprojections along every square, as in Tag 05SA, is determined by that compatibility; hence the
composite of the morphisms attached to `f` and to `g` is the morphism attached to `f ≫ g`. -/
private lemma comp_eq_of_isDerivedMap [W.HasLeftCalculusOfFractions] {X Y Z : C} {f : X ⟶ Y}
    {g : Y ⟶ Z} {fg : X ⟶ Z} (hfg : f ≫ g = fg)
    {c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)}
    {d : Cocone (MorphismProperty.Under.forget W ⊤ Y ⋙ Under.forget Y ⋙ F)}
    {e : Cocone (MorphismProperty.Under.forget W ⊤ Z ⋙ Under.forget Z ⋙ F)}
    (hc : F.IsRightDerivedValueAt W X c) {p : c.pt ⟶ d.pt} {q : d.pt ⟶ e.pt} {m : c.pt ⟶ e.pt}
    (hp : ∀ (a : W.Under ⊤ X) (b : W.Under ⊤ Y) (k : a.right ⟶ b.right),
      f ≫ b.hom = a.hom ≫ k → coprj c a ≫ p = F.map k ≫ coprj d b)
    (hq : ∀ (b : W.Under ⊤ Y) (b' : W.Under ⊤ Z) (k : b.right ⟶ b'.right),
      g ≫ b'.hom = b.hom ≫ k → coprj d b ≫ q = F.map k ≫ coprj e b')
    (hm : ∀ (a : W.Under ⊤ X) (b' : W.Under ⊤ Z) (k : a.right ⟶ b'.right),
      fg ≫ b'.hom = a.hom ≫ k → coprj c a ≫ m = F.map k ≫ coprj e b') :
    p ≫ q = m := by
  refine eq_of_coprj_comp_eq hc fun a => ?_
  obtain ⟨b, k, hk⟩ := DerivedFunctorValues.exists_leftSquare_under W f a
  obtain ⟨b', k', hk'⟩ := DerivedFunctorValues.exists_leftSquare_under W g b
  have hsq : fg ≫ b'.hom = a.hom ≫ k ≫ k' := by
    rw [← hfg, Category.assoc, hk', ← Category.assoc, hk, Category.assoc]
  calc coprj c a ≫ p ≫ q = (coprj c a ≫ p) ≫ q := by rw [Category.assoc]
    _ = F.map k ≫ coprj d b ≫ q := by rw [hp a b k hk, Category.assoc]
    _ = F.map (k ≫ k') ≫ coprj e b' := by rw [hq b b' k' hk', F.map_comp, Category.assoc]
    _ = coprj c a ≫ m := (hm a b' (k ≫ k') hsq).symm

end Pins

section Karoubian

/-- **Stacks 0A2G through Stacks 0A1S**, the shape in which both halves of part (2) use them: if
`Q` is essentially constant, the functors `p` and `G` out of `L` are cofinal, and `p ⋙ M` is a
retract of `G ⋙ Q` in the functor category, then `M` is essentially constant. -/
private lemma isEssentiallyConstantInd_of_retract_of_final {L I K : Type*} [Category L]
    [Category I] [Category K] [IsFiltered L] [IsFiltered I] [IsFiltered K] {A : Type*} [Category A]
    [IsIdempotentComplete A] (p : L ⥤ I) [p.Final] (G : L ⥤ K) [G.Final] {M : I ⥤ A} {Q : K ⥤ A}
    (α : p ⋙ M ⟶ G ⋙ Q) (β : G ⋙ Q ⟶ p ⋙ M) (hαβ : α ≫ β = 𝟙 (p ⋙ M))
    (h : IsEssentiallyConstantInd Q) : IsEssentiallyConstantInd M :=
  essentiallyConstant_of_comp_final p M
    (isEssentiallyConstantInd_of_retract α β hαβ (essentiallyConstant_comp_final_of G Q h))

end Karoubian

section Bridge

variable {C : Type u₁} [Category.{v₁} C] {H : Type u₂} [Category.{v₂} H]

/-- Being defined at `X` in the sense of Stacks 05S9 — the existence of a value of `RF` at `X` —
is essential constancy of the ind-object `X/W ⟶ H`, `(s : X ⟶ X') ↦ F(X')`, of Stacks 05PU(1);
the two are the same data, with the cocone packaged into `Cocone` on one side and split into its
vertex and its coprojections on the other. -/
@[sga "4 XVII 1.2.1" "(ii), special case"]
private lemma exists_isRightDerivedValueAt_iff (F : C ⥤ H) (W : MorphismProperty C) (X : C) :
    (∃ c, F.IsRightDerivedValueAt W X c) ↔
      IsEssentiallyConstantInd (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F) := by
  constructor
  · rintro ⟨c, s₀, r, hr, hcof⟩
    refine ⟨c, s₀, r, hr, fun s => ?_⟩
    obtain ⟨t, u, v, huv⟩ := hcof s
    exact ⟨t, v, u, huv⟩
  · rintro ⟨c, s₀, r, hr, hcof⟩
    refine ⟨c, s₀, r, hr, fun s => ?_⟩
    obtain ⟨t, v, u, huv⟩ := hcof s
    exact ⟨t, u, v, huv⟩

end Bridge

section Biprod

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]

/-- A saturated multiplicative system in a preadditive category is stable under direct sums of
morphisms.

This is the source's argument: by Stacks 05Q9 (`MorphismProperty.IsSaturated.invertedClosure_eq`)
`W` is the class of morphisms inverted by the additive localization functor `W.Q`, and an
additive functor takes the biproduct identities of `X ⊞ Y` to identities in the localization, so
`W.Q(s ⊞ s')` has the explicit inverse
`Q(fst) ≫ Q(s)⁻¹ ≫ Q(inl) + Q(snd) ≫ Q(s')⁻¹ ≫ Q(inr)`. No biproducts in the localization are
needed, only that `W.Q` preserves sums and identities. -/
private lemma mem_biprod_map {W : MorphismProperty C} (hW : W.IsSaturated) {X X' Y Y' : C}
    [HasBinaryBiproduct X Y] [HasBinaryBiproduct X' Y'] {s : X ⟶ X'} (hs : W s) {s' : Y ⟶ Y'}
    (hs' : W s') : W (biprod.map s s') := by
  have := hW.hasLeftCalculusOfFractions
  have := hW.hasRightCalculusOfFractions
  have := hW.isMultiplicative
  have hQs : IsIso (W.Q.map s) := Localization.inverts W.Q W _ hs
  have hQs' : IsIso (W.Q.map s') := Localization.inverts W.Q W _ hs'
  rw [← hW.invertedClosure_eq]
  show IsIso (W.Q.map (biprod.map s s'))
  have hfst : biprod.map s s' ≫ (biprod.fst : X' ⊞ Y' ⟶ X') = biprod.fst ≫ s := by simp
  have hsnd : biprod.map s s' ≫ (biprod.snd : X' ⊞ Y' ⟶ Y') = biprod.snd ≫ s' := by simp
  have hinl : (biprod.inl : X ⟶ X ⊞ Y) ≫ biprod.map s s' = s ≫ biprod.inl := by simp
  have hinr : (biprod.inr : Y ⟶ X ⊞ Y) ≫ biprod.map s s' = s' ≫ biprod.inr := by simp
  refine ⟨W.Q.map biprod.fst ≫ inv (W.Q.map s) ≫ W.Q.map biprod.inl +
    W.Q.map biprod.snd ≫ inv (W.Q.map s') ≫ W.Q.map biprod.inr, ?_, ?_⟩
  · rw [Preadditive.comp_add]
    simp only [← Category.assoc, ← Functor.map_comp, hfst, hsnd]
    simp only [Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, biprod.total, W.Q.map_id]
  · rw [Preadditive.add_comp]
    simp only [Category.assoc, ← Functor.map_comp, hinl, hinr]
    simp only [Functor.map_comp, IsIso.inv_hom_id_assoc]
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, biprod.total, W.Q.map_id]

/-- Composition of direct sums of morphisms. -/
private lemma biprod_map_comp {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C} [HasBinaryBiproduct X₁ X₂]
    [HasBinaryBiproduct Y₁ Y₂] [HasBinaryBiproduct Z₁ Z₂] (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    biprod.map f₁ f₂ ≫ biprod.map g₁ g₂ = biprod.map (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  refine biprod.hom_ext' _ _ ?_ ?_ <;> simp

variable [HasBinaryBiproducts C]

omit [HasBinaryBiproducts C] in
/-- The morphism to a direct sum produced by MS2 on the two projections: a commutative square
for `biprod.fst` and one for `biprod.snd` assemble into one for the direct sum. This is part (1)
of Stacks 04E6 for the functor `biprodUnder`, in terms of morphisms of `C`. -/
private lemma comp_biprod_lift_eq_biprod_map {D X₁ X₂ Y₁ Y₂ : C} [HasBinaryBiproduct X₁ X₂]
    [HasBinaryBiproduct Y₁ Y₂] (h : X₁ ⊞ X₂ ⟶ D) (f₁ : X₁ ⟶ Y₁) (g₁ : D ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (g₂ : D ⟶ Y₂) (h₁ : biprod.fst ≫ f₁ = h ≫ g₁) (h₂ : biprod.snd ≫ f₂ = h ≫ g₂) :
    h ≫ biprod.lift g₁ g₂ = biprod.map f₁ f₂ := by
  refine biprod.hom_ext _ _ ?_ ?_ <;> simp [← h₁, ← h₂]

/-- **MS3 for a direct sum**: two morphisms into `X₁ ⊞ X₂` equalized by a morphism of `W` are
equalized outright after enlarging each summand along `W`. This is part (2) of Stacks 04E6 for
the functor `biprodUnder`, in terms of morphisms of `C`. -/
private lemma exists_biprod_map_comp_eq (W : MorphismProperty C)
    [W.HasLeftCalculusOfFractions] {D Z X₁ X₂ : C} [HasBinaryBiproduct X₁ X₂] (h : Z ⟶ D)
    (hh : W h) (a b : D ⟶ X₁ ⊞ X₂) (hab : h ≫ a = h ≫ b) :
    ∃ (V₁ V₂ : C) (t₁ : X₁ ⟶ V₁) (t₂ : X₂ ⟶ V₂), W t₁ ∧ W t₂ ∧
      a ≫ biprod.map t₁ t₂ = b ≫ biprod.map t₁ t₂ := by
  obtain ⟨V₁, t₁, ht₁, he₁⟩ := MorphismProperty.HasLeftCalculusOfFractions.ext
    (a ≫ biprod.fst) (b ≫ biprod.fst) h hh (by rw [← Category.assoc, ← Category.assoc, hab])
  obtain ⟨V₂, t₂, ht₂, he₂⟩ := MorphismProperty.HasLeftCalculusOfFractions.ext
    (a ≫ biprod.snd) (b ≫ biprod.snd) h hh (by rw [← Category.assoc, ← Category.assoc, hab])
  refine ⟨V₁, V₂, t₁, t₂, ht₁, ht₂, biprod.hom_ext _ _ ?_ ?_⟩
  · simpa using he₁
  · simpa using he₂

/-- The direct sum of two morphisms of `W`, as a functor `X/W × Y/W ⥤ (X ⊞ Y)/W`. -/
private noncomputable def biprodUnder {W : MorphismProperty C} (hW : W.IsSaturated) (X Y : C) :
    (W.Under ⊤ X) × (W.Under ⊤ Y) ⥤ W.Under ⊤ (X ⊞ Y) where
  obj p := MorphismProperty.Under.mk ⊤ (biprod.map p.1.hom p.2.hom)
    (mem_biprod_map hW p.1.prop p.2.prop)
  map {p q} f := MorphismProperty.Under.homMk (biprod.map f.1.right f.2.right)
    (by
      change biprod.map p.1.hom p.2.hom ≫ biprod.map f.1.right f.2.right =
        biprod.map q.1.hom q.2.hom
      rw [biprod_map_comp, MorphismProperty.Under.w f.1, MorphismProperty.Under.w f.2]
      rfl)
  map_id p := MorphismProperty.Under.Hom.ext
    (CochainComplex.FilteredInjective.Hom.biprod_map_id _ _)
  map_comp f g := MorphismProperty.Under.Hom.ext
    (biprod_map_comp f.1.right f.2.right g.1.right g.2.right).symm

/-- **Cofinality of `X/W × Y/W ⟶ (X ⊞ Y)/W`.** Every `t : X ⊞ Y ⟶ Z` in `W` admits a morphism to
a direct sum `s ⊞ s'` (MS2 for `biprod.fst` and for `biprod.snd`, then `biprod.lift`), and two
parallel morphisms into a direct sum are equalized after enlarging both summands (MS3 on the two
components). This is Stacks 04E6 (1) and (2) for the displayed functor. -/
private lemma final_biprodUnder {W : MorphismProperty C} (hW : W.IsSaturated) (X Y : C) :
    haveI := hW.hasLeftCalculusOfFractions
    haveI := W.isFiltered_under_of_hasLeftCalculusOfFractions X
    haveI := W.isFiltered_under_of_hasLeftCalculusOfFractions Y
    (biprodUnder hW X Y).Final := by
  have := hW.hasLeftCalculusOfFractions
  have := W.isFiltered_under_of_hasLeftCalculusOfFractions X
  have := W.isFiltered_under_of_hasLeftCalculusOfFractions Y
  refine Functor.final_of_exists_of_isFiltered _ (fun d => ?_) (fun {d p} u v => ?_)
  · obtain ⟨b₁, g₁, h₁⟩ :=
      DerivedFunctorValues.exists_leftSquare_under W (biprod.fst : X ⊞ Y ⟶ X) d
    obtain ⟨b₂, g₂, h₂⟩ :=
      DerivedFunctorValues.exists_leftSquare_under W (biprod.snd : X ⊞ Y ⟶ Y) d
    exact ⟨(b₁, b₂), ⟨MorphismProperty.Under.homMk (biprod.lift g₁ g₂)
      (comp_biprod_lift_eq_biprod_map d.hom b₁.hom g₁ b₂.hom g₂ h₁ h₂)⟩⟩
  · obtain ⟨V₁, V₂, t₁, t₂, ht₁, ht₂, he⟩ := exists_biprod_map_comp_eq W d.hom d.prop
      u.right v.right ((MorphismProperty.Under.w u).trans (MorphismProperty.Under.w v).symm)
    exact ⟨(MorphismProperty.Under.mk ⊤ (p.1.hom ≫ t₁) (W.comp_mem _ _ p.1.prop ht₁),
      MorphismProperty.Under.mk ⊤ (p.2.hom ≫ t₂) (W.comp_mem _ _ p.2.prop ht₂)),
      (MorphismProperty.Under.homMk t₁ rfl, MorphismProperty.Under.homMk t₂ rfl),
      MorphismProperty.Under.Hom.ext he⟩

end Biprod

section Converse

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasBinaryBiproducts C]
  {H : Type u₂} [Category.{v₂} H]

/-- The first coprojection into the ind-object at `X ⊞ Y` restricted along `biprodUnder`, given
by `F(biprod.inl)`: it splits `mapFst`. -/
private noncomputable def mapInl (F : C ⥤ H) {W : MorphismProperty C} (hW : W.IsSaturated)
    (X Y : C) :
    CategoryTheory.Prod.fst (W.Under ⊤ X) (W.Under ⊤ Y) ⋙ indDiag F W X ⟶
      biprodUnder hW X Y ⋙ indDiag F W (X ⊞ Y) where
  app p := F.map (biprod.inl : p.1.right ⟶ p.1.right ⊞ p.2.right)
  naturality p q f := by
    change F.map f.1.right ≫ F.map (biprod.inl : q.1.right ⟶ q.1.right ⊞ q.2.right)
      = F.map (biprod.inl : p.1.right ⟶ p.1.right ⊞ p.2.right) ≫
        F.map (biprod.map f.1.right f.2.right)
    rw [← F.map_comp, ← F.map_comp, biprod.inl_map]

/-- The first projection of the ind-object at `X ⊞ Y` restricted along `biprodUnder`, given by
`F(biprod.fst)`. -/
private noncomputable def mapFst (F : C ⥤ H) {W : MorphismProperty C} (hW : W.IsSaturated)
    (X Y : C) :
    biprodUnder hW X Y ⋙ indDiag F W (X ⊞ Y) ⟶
      CategoryTheory.Prod.fst (W.Under ⊤ X) (W.Under ⊤ Y) ⋙ indDiag F W X where
  app p := F.map (biprod.fst : p.1.right ⊞ p.2.right ⟶ p.1.right)
  naturality p q f := by
    change F.map (biprod.map f.1.right f.2.right) ≫
        F.map (biprod.fst : q.1.right ⊞ q.2.right ⟶ q.1.right)
      = F.map (biprod.fst : p.1.right ⊞ p.2.right ⟶ p.1.right) ≫ F.map f.1.right
    rw [← F.map_comp, ← F.map_comp, biprod.map_fst]

/-- The second coprojection into the ind-object at `X ⊞ Y` restricted along `biprodUnder`, given
by `F(biprod.inr)`: it splits `mapSnd`. -/
private noncomputable def mapInr (F : C ⥤ H) {W : MorphismProperty C} (hW : W.IsSaturated)
    (X Y : C) :
    CategoryTheory.Prod.snd (W.Under ⊤ X) (W.Under ⊤ Y) ⋙ indDiag F W Y ⟶
      biprodUnder hW X Y ⋙ indDiag F W (X ⊞ Y) where
  app p := F.map (biprod.inr : p.2.right ⟶ p.1.right ⊞ p.2.right)
  naturality p q f := by
    change F.map f.2.right ≫ F.map (biprod.inr : q.2.right ⟶ q.1.right ⊞ q.2.right)
      = F.map (biprod.inr : p.2.right ⟶ p.1.right ⊞ p.2.right) ≫
        F.map (biprod.map f.1.right f.2.right)
    rw [← F.map_comp, ← F.map_comp, biprod.inr_map]

/-- The second projection of the ind-object at `X ⊞ Y` restricted along `biprodUnder`, given by
`F(biprod.snd)`. -/
private noncomputable def mapSnd (F : C ⥤ H) {W : MorphismProperty C} (hW : W.IsSaturated)
    (X Y : C) :
    biprodUnder hW X Y ⋙ indDiag F W (X ⊞ Y) ⟶
      CategoryTheory.Prod.snd (W.Under ⊤ X) (W.Under ⊤ Y) ⋙ indDiag F W Y where
  app p := F.map (biprod.snd : p.1.right ⊞ p.2.right ⟶ p.2.right)
  naturality p q f := by
    change F.map (biprod.map f.1.right f.2.right) ≫
        F.map (biprod.snd : q.1.right ⊞ q.2.right ⟶ q.2.right)
      = F.map (biprod.snd : p.1.right ⊞ p.2.right ⟶ p.2.right) ≫ F.map f.2.right
    rw [← F.map_comp, ← F.map_comp, biprod.map_snd]

private lemma mapInl_comp_mapFst (F : C ⥤ H) {W : MorphismProperty C} (hW : W.IsSaturated)
    (X Y : C) : mapInl F hW X Y ≫ mapFst F hW X Y = 𝟙 _ := by
  ext p
  show F.map (biprod.inl : p.1.right ⟶ p.1.right ⊞ p.2.right) ≫
      F.map (biprod.fst : p.1.right ⊞ p.2.right ⟶ p.1.right) = 𝟙 _
  rw [← F.map_comp, biprod.inl_fst, F.map_id]

private lemma mapInr_comp_mapSnd (F : C ⥤ H) {W : MorphismProperty C} (hW : W.IsSaturated)
    (X Y : C) : mapInr F hW X Y ≫ mapSnd F hW X Y = 𝟙 _ := by
  ext p
  show F.map (biprod.inr : p.2.right ⟶ p.1.right ⊞ p.2.right) ≫
      F.map (biprod.snd : p.1.right ⊞ p.2.right ⟶ p.2.right) = 𝟙 _
  rw [← F.map_comp, biprod.inr_snd, F.map_id]

/-- **Stacks 05SD (2)**: if the target is Karoubian and `RF` is defined at `X ⊞ Y`, then `RF` is
defined at `X` and at `Y`.

This is the source's argument, and it uses no triangulated structure and no exactness of `F`:
the functor `X/W × Y/W ⟶ (X ⊞ Y)/W` of `biprodUnder` is cofinal (`final_biprodUnder`), so
essential constancy of the ind-object at `X ⊞ Y` restricts to essential constancy of
`(a, b) ↦ F(a.right ⊞ b.right)` (Stacks 0A1S). The ind-object at `X` pulled back along the first
projection is a retract of that diagram, through `F(biprod.inl)` and `F(biprod.fst)`, hence is
essentially constant because `H` is Karoubian (`isEssentiallyConstantInd_of_retract`, Stacks 0A2G).
The first projection `X/W × Y/W ⟶ X/W` is cofinal (`IsFiltered.final_fst`, Stacks 0A2C), so the
ind-object at `X` is itself essentially constant. Likewise for `Y`, with `biprod.inr`,
`biprod.snd` and the second projection. -/
private theorem exists_isRightDerivedValueAt_of_biprod (F : C ⥤ H) (W : MorphismProperty C)
    (hW : W.IsSaturated) (X Y : C) :
    IsIdempotentComplete H → (∃ c, F.IsRightDerivedValueAt W (X ⊞ Y) c) →
      (∃ c, F.IsRightDerivedValueAt W X c) ∧ ∃ c, F.IsRightDerivedValueAt W Y c := by
  intro hkar hXY
  have := hW.hasLeftCalculusOfFractions
  have := W.isFiltered_under_of_hasLeftCalculusOfFractions X
  have := W.isFiltered_under_of_hasLeftCalculusOfFractions Y
  have := W.isFiltered_under_of_hasLeftCalculusOfFractions (X ⊞ Y)
  have := final_biprodUnder hW X Y
  have hEC := (exists_isRightDerivedValueAt_iff F W (X ⊞ Y)).mp hXY
  exact ⟨(exists_isRightDerivedValueAt_iff F W X).mpr
      (isEssentiallyConstantInd_of_retract_of_final (CategoryTheory.Prod.fst _ _)
        (biprodUnder hW X Y) (mapInl F hW X Y) (mapFst F hW X Y)
        (mapInl_comp_mapFst F hW X Y) hEC),
    (exists_isRightDerivedValueAt_iff F W Y).mpr
      (isEssentiallyConstantInd_of_retract_of_final (CategoryTheory.Prod.snd _ _)
        (biprodUnder hW X Y) (mapInr F hW X Y) (mapSnd F hW X Y)
        (mapInr_comp_mapSnd F hW X Y) hEC)⟩

end Converse

section Dual

variable {C : Type u₁} [Category.{v₁} C] {H : Type u₂} [Category.{v₂} H]

/-- Being defined at `X` in the sense of Stacks 05S9 for the left derived functor is essential
constancy of the *opposite* of the pro-object `W/X ⟶ H`, `(s : X' ⟶ X) ↦ F(X')`: the pro-object
condition of Stacks 05PU(2) at `X` is the ind-object condition of Stacks 05PU(1) for the opposite
diagram, a cone becoming a cocone under `Limits.Cone.op`. -/
private lemma exists_isLeftDerivedValueAt_iff (F : C ⥤ H) (W : MorphismProperty C) (X : C) :
    (∃ c, F.IsLeftDerivedValueAt W X c) ↔
      IsEssentiallyConstantInd (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F).op := by
  constructor
  · rintro ⟨c, s₀, r, hr, hcof⟩
    refine ⟨c.op, Opposite.op s₀, r.op, Quiver.Hom.unop_inj hr, fun j => ?_⟩
    obtain ⟨t, u, v, huv⟩ := hcof j.unop
    exact ⟨Opposite.op t, v.op, u.op,
      Quiver.Hom.unop_inj (huv.trans (Category.assoc _ _ _).symm)⟩
  · rintro ⟨c, i₀, b, hb, hcof⟩
    refine ⟨c.unop, i₀.unop, b.unop, Quiver.Hom.op_inj hb, fun s => ?_⟩
    obtain ⟨k, v, u, huv⟩ := hcof (Opposite.op s)
    refine ⟨k.unop, u.unop, v.unop, ?_⟩
    have h : (F.map u.unop.left).op
        = c.ι.app (Opposite.op s) ≫ b ≫ (F.map v.unop.left).op := huv
    exact Quiver.Hom.op_inj (h.trans (Category.assoc _ _ _).symm)

variable [Preadditive C] [HasBinaryBiproducts C]

/-- The morphism out of a direct sum produced by MS2 on the two coprojections: a commutative
square for `biprod.inl` and one for `biprod.inr` assemble into one for the direct sum. This is
the formal dual of `comp_biprod_lift_eq_biprod_map`. -/
private lemma biprod_desc_comp_eq_biprod_map {D X₁ X₂ Y₁ Y₂ : C} (h : D ⟶ Y₁ ⊞ Y₂)
    (f₁ : X₁ ⟶ Y₁) (g₁ : X₁ ⟶ D) (f₂ : X₂ ⟶ Y₂) (g₂ : X₂ ⟶ D)
    (h₁ : f₁ ≫ biprod.inl = g₁ ≫ h) (h₂ : f₂ ≫ biprod.inr = g₂ ≫ h) :
    biprod.desc g₁ g₂ ≫ h = biprod.map f₁ f₂ := by
  refine biprod.hom_ext' _ _ ?_ ?_ <;> simp [← h₁, ← h₂]

/-- **MS3 for a direct sum**, dual form: two morphisms out of `X₁ ⊞ X₂` equalized by a morphism
of `W` are equalized outright after shrinking each summand along `W`. This is the formal dual of
`exists_biprod_map_comp_eq`. -/
private lemma exists_comp_biprod_map_eq (W : MorphismProperty C)
    [W.HasRightCalculusOfFractions] {D Z X₁ X₂ : C} (h : D ⟶ Z) (hh : W h)
    (a b : X₁ ⊞ X₂ ⟶ D) (hab : a ≫ h = b ≫ h) :
    ∃ (V₁ V₂ : C) (t₁ : V₁ ⟶ X₁) (t₂ : V₂ ⟶ X₂), W t₁ ∧ W t₂ ∧
      biprod.map t₁ t₂ ≫ a = biprod.map t₁ t₂ ≫ b := by
  obtain ⟨V₁, t₁, ht₁, he₁⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
    (biprod.inl ≫ a) (biprod.inl ≫ b) h hh (by rw [Category.assoc, Category.assoc, hab])
  obtain ⟨V₂, t₂, ht₂, he₂⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
    (biprod.inr ≫ a) (biprod.inr ≫ b) h hh (by rw [Category.assoc, Category.assoc, hab])
  refine ⟨V₁, V₂, t₁, t₂, ht₁, ht₂, biprod.hom_ext' _ _ ?_ ?_⟩
  · simpa using he₁
  · simpa using he₂

/-- The direct sum of two morphisms of `W`, as a functor `W/X × W/Y ⥤ W/(X ⊞ Y)`. This is the
formal dual of `biprodUnder`. -/
private noncomputable def biprodOver {W : MorphismProperty C} (hW : W.IsSaturated) (X Y : C) :
    (W.Over ⊤ X) × (W.Over ⊤ Y) ⥤ W.Over ⊤ (X ⊞ Y) where
  obj p := MorphismProperty.Over.mk ⊤ (biprod.map p.1.hom p.2.hom)
    (mem_biprod_map hW p.1.prop p.2.prop)
  map {p q} f := MorphismProperty.Over.homMk (biprod.map f.1.left f.2.left)
    (by
      change biprod.map f.1.left f.2.left ≫ biprod.map q.1.hom q.2.hom =
        biprod.map p.1.hom p.2.hom
      rw [biprod_map_comp, MorphismProperty.Over.w f.1, MorphismProperty.Over.w f.2]
      rfl)
  map_id p := MorphismProperty.Over.Hom.ext
    (CochainComplex.FilteredInjective.Hom.biprod_map_id _ _)
  map_comp f g := MorphismProperty.Over.Hom.ext
    (biprod_map_comp f.1.left f.2.left g.1.left g.2.left).symm

/-- **Initiality of `W/X × W/Y ⟶ W/(X ⊞ Y)`**, the formal dual of `final_biprodUnder`: every
`t : Z ⟶ X ⊞ Y` in `W` receives a morphism from a direct sum `s ⊞ s'` (MS2 for `biprod.inl` and
for `biprod.inr`, then `biprod.desc`), and two parallel morphisms out of a direct sum are
equalized after shrinking both summands (MS3 on the two components). -/
private lemma initial_biprodOver {W : MorphismProperty C} (hW : W.IsSaturated) (X Y : C) :
    haveI := hW.hasRightCalculusOfFractions
    haveI : IsCofiltered (W.Over ⊤ X) := inferInstance
    haveI : IsCofiltered (W.Over ⊤ Y) := inferInstance
    (biprodOver hW X Y).Initial := by
  have := hW.hasRightCalculusOfFractions
  have : IsCofiltered (W.Over ⊤ X) := inferInstance
  have : IsCofiltered (W.Over ⊤ Y) := inferInstance
  refine Functor.initial_of_exists_of_isCofiltered _ (fun d => ?_) (fun {d p} u v => ?_)
  · obtain ⟨b₁, g₁, h₁⟩ := exists_over_sq (biprod.inl : X ⟶ X ⊞ Y) d
    replace h₁ := h₁.symm
    obtain ⟨b₂, g₂, h₂⟩ := exists_over_sq (biprod.inr : Y ⟶ X ⊞ Y) d
    replace h₂ := h₂.symm
    exact ⟨(b₁, b₂), ⟨MorphismProperty.Over.homMk (biprod.desc g₁ g₂)
      (biprod_desc_comp_eq_biprod_map d.hom b₁.hom g₁ b₂.hom g₂ h₁ h₂)⟩⟩
  · obtain ⟨V₁, V₂, t₁, t₂, ht₁, ht₂, he⟩ := exists_comp_biprod_map_eq W d.hom d.prop
      u.left v.left ((MorphismProperty.Over.w u).trans (MorphismProperty.Over.w v).symm)
    exact ⟨(MorphismProperty.Over.mk ⊤ (t₁ ≫ p.1.hom) (W.comp_mem _ _ ht₁ p.1.prop),
      MorphismProperty.Over.mk ⊤ (t₂ ≫ p.2.hom) (W.comp_mem _ _ ht₂ p.2.prop)),
      (MorphismProperty.Over.homMk t₁ rfl, MorphismProperty.Over.homMk t₂ rfl),
      MorphismProperty.Over.Hom.ext he⟩

/-- The pro-object at `X`, `(s : X' ⟶ X) ↦ F(X')`, read as a diagram on the *opposite* of its
index category: it is essential constancy of this that is definedness of `LF` at `X`
(`exists_isLeftDerivedValueAt_iff`). -/
@[sga "4 XVII 5.5.5" "partial"]
private abbrev proDiagOp (F : C ⥤ H) (W : MorphismProperty C) (X : C) :
    (W.Over ⊤ X)ᵒᵖ ⥤ Hᵒᵖ :=
  (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F).op

/-- The first projection of the pro-object at `X ⊞ Y` restricted along `biprodOver`: the
natural transformation from the pro-object at `X`, pulled back along the first projection of the
index category, given by `F(biprod.fst)`. -/
private noncomputable def mapFstOp (F : C ⥤ H) {W : MorphismProperty C} (hW : W.IsSaturated)
    (X Y : C) :
    (CategoryTheory.Prod.fst (W.Over ⊤ X) (W.Over ⊤ Y)).op ⋙ proDiagOp F W X ⟶
      (biprodOver hW X Y).op ⋙ proDiagOp F W (X ⊞ Y) where
  app p := (F.map (biprod.fst : p.unop.1.left ⊞ p.unop.2.left ⟶ p.unop.1.left)).op
  naturality p q f := Quiver.Hom.unop_inj (by
    change F.map (biprod.fst : q.unop.1.left ⊞ q.unop.2.left ⟶ q.unop.1.left) ≫
        F.map f.unop.1.left
      = F.map (biprod.map f.unop.1.left f.unop.2.left) ≫
        F.map (biprod.fst : p.unop.1.left ⊞ p.unop.2.left ⟶ p.unop.1.left)
    rw [← F.map_comp, ← F.map_comp, biprod.map_fst])

/-- The first coprojection into the pro-object at `X ⊞ Y` restricted along `biprodOver`, given by
`F(biprod.inl)`: it splits `mapFstOp`. -/
private noncomputable def mapInlOp (F : C ⥤ H) {W : MorphismProperty C} (hW : W.IsSaturated)
    (X Y : C) :
    (biprodOver hW X Y).op ⋙ proDiagOp F W (X ⊞ Y) ⟶
      (CategoryTheory.Prod.fst (W.Over ⊤ X) (W.Over ⊤ Y)).op ⋙ proDiagOp F W X where
  app p := (F.map (biprod.inl : p.unop.1.left ⟶ p.unop.1.left ⊞ p.unop.2.left)).op
  naturality p q f := Quiver.Hom.unop_inj (by
    change F.map (biprod.inl : q.unop.1.left ⟶ q.unop.1.left ⊞ q.unop.2.left) ≫
        F.map (biprod.map f.unop.1.left f.unop.2.left)
      = F.map f.unop.1.left ≫
        F.map (biprod.inl : p.unop.1.left ⟶ p.unop.1.left ⊞ p.unop.2.left)
    rw [← F.map_comp, ← F.map_comp, biprod.inl_map])

/-- The second projection of the pro-object at `X ⊞ Y` restricted along `biprodOver`, given by
`F(biprod.snd)`. -/
private noncomputable def mapSndOp (F : C ⥤ H) {W : MorphismProperty C} (hW : W.IsSaturated)
    (X Y : C) :
    (CategoryTheory.Prod.snd (W.Over ⊤ X) (W.Over ⊤ Y)).op ⋙ proDiagOp F W Y ⟶
      (biprodOver hW X Y).op ⋙ proDiagOp F W (X ⊞ Y) where
  app p := (F.map (biprod.snd : p.unop.1.left ⊞ p.unop.2.left ⟶ p.unop.2.left)).op
  naturality p q f := Quiver.Hom.unop_inj (by
    change F.map (biprod.snd : q.unop.1.left ⊞ q.unop.2.left ⟶ q.unop.2.left) ≫
        F.map f.unop.2.left
      = F.map (biprod.map f.unop.1.left f.unop.2.left) ≫
        F.map (biprod.snd : p.unop.1.left ⊞ p.unop.2.left ⟶ p.unop.2.left)
    rw [← F.map_comp, ← F.map_comp, biprod.map_snd])

/-- The second coprojection into the pro-object at `X ⊞ Y` restricted along `biprodOver`, given by
`F(biprod.inr)`: it splits `mapSndOp`. -/
private noncomputable def mapInrOp (F : C ⥤ H) {W : MorphismProperty C} (hW : W.IsSaturated)
    (X Y : C) :
    (biprodOver hW X Y).op ⋙ proDiagOp F W (X ⊞ Y) ⟶
      (CategoryTheory.Prod.snd (W.Over ⊤ X) (W.Over ⊤ Y)).op ⋙ proDiagOp F W Y where
  app p := (F.map (biprod.inr : p.unop.2.left ⟶ p.unop.1.left ⊞ p.unop.2.left)).op
  naturality p q f := Quiver.Hom.unop_inj (by
    change F.map (biprod.inr : q.unop.2.left ⟶ q.unop.1.left ⊞ q.unop.2.left) ≫
        F.map (biprod.map f.unop.1.left f.unop.2.left)
      = F.map f.unop.2.left ≫
        F.map (biprod.inr : p.unop.2.left ⟶ p.unop.1.left ⊞ p.unop.2.left)
    rw [← F.map_comp, ← F.map_comp, biprod.inr_map])

private lemma mapFstOp_comp_mapInlOp (F : C ⥤ H) {W : MorphismProperty C} (hW : W.IsSaturated)
    (X Y : C) : mapFstOp F hW X Y ≫ mapInlOp F hW X Y = 𝟙 _ := by
  ext p
  refine Quiver.Hom.unop_inj ?_
  show F.map (biprod.inl : p.unop.1.left ⟶ p.unop.1.left ⊞ p.unop.2.left) ≫
      F.map (biprod.fst : p.unop.1.left ⊞ p.unop.2.left ⟶ p.unop.1.left) = 𝟙 _
  rw [← F.map_comp, biprod.inl_fst, F.map_id]

private lemma mapSndOp_comp_mapInrOp (F : C ⥤ H) {W : MorphismProperty C} (hW : W.IsSaturated)
    (X Y : C) : mapSndOp F hW X Y ≫ mapInrOp F hW X Y = 𝟙 _ := by
  ext p
  refine Quiver.Hom.unop_inj ?_
  show F.map (biprod.inr : p.unop.2.left ⟶ p.unop.1.left ⊞ p.unop.2.left) ≫
      F.map (biprod.snd : p.unop.1.left ⊞ p.unop.2.left ⟶ p.unop.2.left) = 𝟙 _
  rw [← F.map_comp, biprod.inr_snd, F.map_id]

/-- **Stacks 05SD (2)** for the left derived functor, the formal dual of
`exists_isRightDerivedValueAt_of_biprod`: the pro-object at `X ⊞ Y` restricted along the cofinal
`biprodOver` has the pro-object at `X` pulled back along the first projection as a retract,
through `F(biprod.inl)` and `F(biprod.fst)`, and a Karoubian `H` has Karoubian opposite. -/
private theorem exists_isLeftDerivedValueAt_of_biprod (F : C ⥤ H) (W : MorphismProperty C)
    (hW : W.IsSaturated) (X Y : C) :
    IsIdempotentComplete H → (∃ c, F.IsLeftDerivedValueAt W (X ⊞ Y) c) →
      (∃ c, F.IsLeftDerivedValueAt W X c) ∧ ∃ c, F.IsLeftDerivedValueAt W Y c := by
  intro hkar hXY
  have : IsIdempotentComplete Hᵒᵖ := Idempotents.isIdempotentComplete_iff_opposite.mpr hkar
  have := hW.hasRightCalculusOfFractions
  have : IsCofiltered (W.Over ⊤ X) := inferInstance
  have : IsCofiltered (W.Over ⊤ Y) := inferInstance
  have : IsCofiltered (W.Over ⊤ (X ⊞ Y)) := inferInstance
  have := initial_biprodOver hW X Y
  have := Functor.final_op_of_initial (biprodOver hW X Y)
  have hfst : (CategoryTheory.Prod.fst (W.Over ⊤ X) (W.Over ⊤ Y)).Initial := IsFiltered.initial_fst
  have hsnd : (CategoryTheory.Prod.snd (W.Over ⊤ X) (W.Over ⊤ Y)).Initial := IsFiltered.initial_snd
  have := Functor.final_op_of_initial (CategoryTheory.Prod.fst (W.Over ⊤ X) (W.Over ⊤ Y))
  have := Functor.final_op_of_initial (CategoryTheory.Prod.snd (W.Over ⊤ X) (W.Over ⊤ Y))
  have hEC := (exists_isLeftDerivedValueAt_iff F W (X ⊞ Y)).mp hXY
  exact ⟨(exists_isLeftDerivedValueAt_iff F W X).mpr
      (isEssentiallyConstantInd_of_retract_of_final (CategoryTheory.Prod.fst _ _).op
        (biprodOver hW X Y).op (mapFstOp F hW X Y) (mapInlOp F hW X Y)
        (mapFstOp_comp_mapInlOp F hW X Y) hEC),
    (exists_isLeftDerivedValueAt_iff F W Y).mpr
      (isEssentiallyConstantInd_of_retract_of_final (CategoryTheory.Prod.snd _ _).op
        (biprodOver hW X Y).op (mapSndOp F hW X Y) (mapInrOp F hW X Y)
        (mapSndOp_comp_mapInrOp F hW X Y) hEC)⟩

end Dual

section LeftValues

variable {C : Type u₁} [Category.{v₁} C] {H : Type u₂} [Category.{v₂} H]
  {W : MorphismProperty C} {F : C ⥤ H}

/-- The pro-object at `X` whose essential constancy is definedness of `LF` at `X`:
`W/X ⟶ H`, `(s : X' ⟶ X) ↦ F(X')`. -/
private abbrev proDiag (F : C ⥤ H) (W : MorphismProperty C) (X : C) : W.Over ⊤ X ⥤ H :=
  MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F

/-- The projection of a cone on the pro-object at `X`, with its target written as `F(a.left)`. -/
private abbrev proj {X : C} (c : Cone (proDiag F W X)) (a : W.Over ⊤ X) : c.pt ⟶ F.obj a.left :=
  c.π.app a

/-- Compatibility of a cone on the pro-object at `X` with a morphism of `W/X`, written in terms
of morphisms of `C`. -/
private lemma proj_comp_map {X : C} (c : Cone (proDiag F W X)) {a a' : W.Over ⊤ X}
    (g : a.left ⟶ a'.left) (hg : g ≫ a'.hom = a.hom) : proj c a ≫ F.map g = proj c a' :=
  c.w (MorphismProperty.Over.homMk g hg)

/-- A value of `LF` at `X` is a retract of a term of the pro-object, so a morphism into it is
determined by its composites with the projections. -/
private lemma eq_of_comp_proj_eq {X : C} {c : Cone (proDiag F W X)}
    (hc : F.IsLeftDerivedValueAt W X c) {Z : H} {α β : Z ⟶ c.pt}
    (h : ∀ a : W.Over ⊤ X, α ≫ proj c a = β ≫ proj c a) : α = β := by
  obtain ⟨a₀, r, hr, -⟩ := hc
  have hr' : proj c a₀ ≫ r = 𝟙 c.pt := hr
  calc α = α ≫ proj c a₀ ≫ r := by rw [hr', Category.comp_id]
    _ = β ≫ proj c a₀ ≫ r := by rw [← Category.assoc, h a₀, Category.assoc]
    _ = β := by rw [hr', Category.comp_id]

/-- **MS3 for the pro-object**: a morphism of `C` killed by `b.hom` becomes zero after refining
its source in `W/X`. -/
private lemma exists_over_precomp_eq_zero [W.HasRightCalculusOfFractions] [HasZeroMorphisms C]
    {X Y : C} (a : W.Over ⊤ X) (b : W.Over ⊤ Y) (g : a.left ⟶ b.left) (hg : g ≫ b.hom = 0) :
    ∃ (a' : W.Over ⊤ X) (q : a'.left ⟶ a.left), q ≫ a.hom = a'.hom ∧ q ≫ g = 0 := by
  obtain ⟨V, t, ht, hteq⟩ :=
    MorphismProperty.HasRightCalculusOfFractions.ext g 0 b.hom b.prop (by simp [hg])
  exact ⟨MorphismProperty.Over.mk ⊤ (t ≫ a.hom) (W.comp_mem _ _ ht a.prop), t, rfl,
    hteq.trans Limits.comp_zero⟩

/-- The composite of a projection with the image of a morphism killed by `b.hom` vanishes. -/
private lemma proj_comp_map_eq_zero [W.HasRightCalculusOfFractions] [HasZeroMorphisms C]
    [HasZeroMorphisms H] [F.PreservesZeroMorphisms] {X Y : C} (c : Cone (proDiag F W X))
    (a : W.Over ⊤ X) (b : W.Over ⊤ Y) (g : a.left ⟶ b.left) (hg : g ≫ b.hom = 0) :
    proj c a ≫ F.map g = 0 := by
  obtain ⟨a', q, hq, hqg⟩ := exists_over_precomp_eq_zero a b g hg
  calc proj c a ≫ F.map g = (proj c a' ≫ F.map q) ≫ F.map g := by rw [proj_comp_map c q hq]
    _ = proj c a' ≫ F.map (q ≫ g) := by rw [F.map_comp, Category.assoc]
    _ = 0 := by rw [hqg, F.map_zero, Limits.comp_zero]

/-- The identity of a value of `LF` at `Z` is compatible with the projections along every square
for `𝟙 Z`: it is the morphism `LF(𝟙 Z)` dual to Tag 05SA. -/
private lemma isDerivedMapLeft_id {Z : C} (c : Cone (proDiag F W Z)) (a b : W.Over ⊤ Z)
    (g : a.left ⟶ b.left) (hg : g ≫ b.hom = a.hom ≫ 𝟙 Z) :
    𝟙 c.pt ≫ proj c b = proj c a ≫ F.map g := by
  rw [Category.id_comp, ← proj_comp_map c g (by simpa using hg)]

/-- The zero morphism between values of `LF` is compatible with the projections along every
square for `0 : Z ⟶ Z'`: it is the morphism `LF(0)` dual to Tag 05SA. -/
private lemma isDerivedMapLeft_zero [W.HasRightCalculusOfFractions] [HasZeroMorphisms C]
    [HasZeroMorphisms H] [F.PreservesZeroMorphisms] {Z Z' : C} (c : Cone (proDiag F W Z))
    (c' : Cone (proDiag F W Z')) (a : W.Over ⊤ Z) (b : W.Over ⊤ Z') (g : a.left ⟶ b.left)
    (hg : g ≫ b.hom = a.hom ≫ (0 : Z ⟶ Z')) :
    (0 : c.pt ⟶ c'.pt) ≫ proj c' b = proj c a ≫ F.map g := by
  rw [Limits.zero_comp, proj_comp_map_eq_zero c a b g (by simpa using hg)]

/-- **Functoriality of `LF`**, dual to `comp_eq_of_isDerivedMap`: the composite of
the morphisms attached to `f` and to `g` is the morphism attached to `f ≫ g`, a morphism into a
value being determined by its compatibility with the projections. -/
private lemma comp_eq_of_isDerivedMapLeft [W.HasRightCalculusOfFractions] {Z Z' Z'' : C}
    {f : Z ⟶ Z'} {g : Z' ⟶ Z''} {fg : Z ⟶ Z''} (hfg : f ≫ g = fg)
    {c : Cone (proDiag F W Z)} {c' : Cone (proDiag F W Z')} {c'' : Cone (proDiag F W Z'')}
    (hc'' : F.IsLeftDerivedValueAt W Z'' c'')
    {p : c.pt ⟶ c'.pt} {q : c'.pt ⟶ c''.pt} {m : c.pt ⟶ c''.pt}
    (hp : ∀ (a : W.Over ⊤ Z) (b : W.Over ⊤ Z') (k : a.left ⟶ b.left),
      k ≫ b.hom = a.hom ≫ f → p ≫ proj c' b = proj c a ≫ F.map k)
    (hq : ∀ (b : W.Over ⊤ Z') (b' : W.Over ⊤ Z'') (k : b.left ⟶ b'.left),
      k ≫ b'.hom = b.hom ≫ g → q ≫ proj c'' b' = proj c' b ≫ F.map k)
    (hm : ∀ (a : W.Over ⊤ Z) (b' : W.Over ⊤ Z'') (k : a.left ⟶ b'.left),
      k ≫ b'.hom = a.hom ≫ fg → m ≫ proj c'' b' = proj c a ≫ F.map k) :
    p ≫ q = m := by
  refine eq_of_comp_proj_eq hc'' fun b' => ?_
  obtain ⟨b, k', hk'⟩ := exists_over_sq g b'
  replace hk' := hk'.symm
  obtain ⟨a, k, hk⟩ := exists_over_sq f b
  replace hk := hk.symm
  have hsq : (k ≫ k') ≫ b'.hom = a.hom ≫ fg := by
    rw [← hfg, Category.assoc, ← hk', ← Category.assoc, ← hk, Category.assoc]
  calc (p ≫ q) ≫ proj c'' b' = p ≫ q ≫ proj c'' b' := by rw [Category.assoc]
    _ = p ≫ proj c' b ≫ F.map k' := by rw [hq b b' k' hk'.symm]
    _ = (proj c a ≫ F.map k) ≫ F.map k' := by rw [← Category.assoc, hp a b k hk.symm]
    _ = proj c a ≫ F.map (k ≫ k') := by rw [F.map_comp, Category.assoc]
    _ = m ≫ proj c'' b' := (hm a b' (k ≫ k') hsq).symm

end LeftValues

section Main

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {H : Type u₂} [Category.{v₂} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]

/-- The triangle `Y ⟶ X ⊞ Y ⟶ X ⟶ Y⟦1⟧` on the second and the first summand of a direct sum is
distinguished: it is Mathlib's `binaryBiproductTriangle Y X` transported along the braiding
`X ⊞ Y ≅ Y ⊞ X`. -/
private lemma binaryBiproductTriangle_inr_fst_distinguished (X Y : C) :
    Triangle.mk (biprod.inr : Y ⟶ X ⊞ Y) (biprod.fst : X ⊞ Y ⟶ X) 0 ∈ distTriang C := by
  refine isomorphic_distinguished _ (binaryBiproductTriangle_distinguished Y X) _
    (Triangle.isoMk _ _ (Iso.refl _) (biprod.braiding X Y) (Iso.refl _) ?_ ?_ ?_)
  · show (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.braiding X Y).hom = 𝟙 Y ≫ biprod.inl
    ext <;> simp [biprod.braiding]
  · show (biprod.fst : X ⊞ Y ⟶ X) ≫ 𝟙 X = (biprod.braiding X Y).hom ≫ biprod.snd
    simp [biprod.braiding]
  · show (0 : X ⟶ Y⟦(1 : ℤ)⟧) ≫ (shiftFunctor C (1 : ℤ)).map (Iso.refl Y).hom
      = (Iso.refl X).hom ≫ 0
    simp

/-- **Stacks 05QT**, in the form in which both halves of the lemma use it: a distinguished
triangle `P₁ ⟶ P ⟶ P₂ ⟶ P₁⟦1⟧` whose two maps `u`, `p₂` are matched by `p₁`, `u₂` in the four
identities of a biproduct is split by `biprod.desc u u₂`, and `biprod.lift p₁ p₂` is the inverse
of that splitting.

Only `u₂ ≫ p₂ = 𝟙` is fed to Tag 05QT; the four identities together say that
`biprod.desc u u₂ ≫ biprod.lift p₁ p₂` is the identity of `P₁ ⊞ P₂`, which turns the splitting
into the assertion about `biprod.lift p₁ p₂`. -/
private lemma isIso_biprod_lift_of_distTriang {P P₁ P₂ : H} {u : P₁ ⟶ P} {p₂ : P ⟶ P₂}
    {w : P₂ ⟶ P₁⟦(1 : ℤ)⟧} (hdist : Triangle.mk u p₂ w ∈ distTriang H) {u₂ : P₂ ⟶ P}
    {p₁ : P ⟶ P₁} (e₁ : u ≫ p₁ = 𝟙 P₁) (e₂ : u ≫ p₂ = 0) (e₃ : u₂ ≫ p₁ = 0)
    (e₄ : u₂ ≫ p₂ = 𝟙 P₂) : IsIso (biprod.lift p₁ p₂) := by
  have hdesc : IsIso (biprod.desc u u₂) :=
    isIso_biprod_desc_of_distTriang (Triangle.mk u p₂ w) hdist u₂ e₄
  have key : biprod.desc u u₂ ≫ biprod.lift p₁ p₂ = 𝟙 (P₁ ⊞ P₂) := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp [e₁, e₂, e₃, e₄]
  rw [show biprod.lift p₁ p₂ = inv (biprod.desc u u₂) by
    rw [← Category.id_comp (biprod.lift p₁ p₂), ← IsIso.inv_hom_id (biprod.desc u u₂),
      Category.assoc, key, Category.comp_id]]
  infer_instance


end Main

end DerivedFunctorBiprod

namespace CategoryTheory.Functor

open DerivedFunctorBiprod
open CategoryTheory Limits Pretriangulated

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {H : Type u₂} [Category.{v₂} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]

/-- **Stacks 05SD**. Let `F : C ⥤ H` be an exact functor of pretriangulated categories and let
`W` be a saturated multiplicative system in `C` (Stacks 05Q8) compatible with the triangulation.
Let `X` and `Y` be objects of `C` and write `X ⊞ Y` for their direct sum. Then, `RF` and `LF`
being the right and left derived functors of `F` with respect to `W` and definedness and values
being as in Stacks 05S9:

1. if `RF` is defined at `X` and at `Y`, then `RF` is defined at `X ⊞ Y`, and likewise for `LF`;
2. if `H` is Karoubian (`IsIdempotentComplete`) and `RF` is defined at `X ⊞ Y`, then `RF` is
   defined at `X` and at `Y`, and likewise for `LF`;

and in either case `RF(X ⊞ Y) = RF(X) ⊞ RF(Y)`: for values `cX`, `cY`, `cXY` of `RF` at `X`, `Y`
and `X ⊞ Y` there are morphisms `p₁ : RF(X ⊞ Y) ⟶ RF(X)` and `p₂ : RF(X ⊞ Y) ⟶ RF(Y)`, namely
the maps `RF(biprod.fst)` and `RF(biprod.snd)` of Stacks 05SA — each pinned by compatibility with
the coprojections along every commutative square, which determines it uniquely — such that
`biprod.lift p₁ p₂` is an isomorphism; and likewise for `LF`, with the projections of the
cones. -/
@[stacks 05SD]
public theorem exists_isDerivedValueAt_biprod_and_isIso_biprod_lift
    (F : C ⥤ H) [F.CommShift ℤ]
    [F.IsTriangulated] (W : MorphismProperty C) (hW : W.IsSaturated)
    [W.IsCompatibleWithTriangulation] (X Y : C) :
    -- (1) for `RF` and for `LF`
    ((∃ c, F.IsRightDerivedValueAt W X c) → (∃ c, F.IsRightDerivedValueAt W Y c) →
        ∃ c, F.IsRightDerivedValueAt W (X ⊞ Y) c) ∧
      ((∃ c, F.IsLeftDerivedValueAt W X c) → (∃ c, F.IsLeftDerivedValueAt W Y c) →
        ∃ c, F.IsLeftDerivedValueAt W (X ⊞ Y) c) ∧
      -- (2) for `RF` and for `LF`, over a Karoubian target
      (IsIdempotentComplete H → (∃ c, F.IsRightDerivedValueAt W (X ⊞ Y) c) →
        (∃ c, F.IsRightDerivedValueAt W X c) ∧ ∃ c, F.IsRightDerivedValueAt W Y c) ∧
      (IsIdempotentComplete H → (∃ c, F.IsLeftDerivedValueAt W (X ⊞ Y) c) →
        (∃ c, F.IsLeftDerivedValueAt W X c) ∧ ∃ c, F.IsLeftDerivedValueAt W Y c) ∧
      -- `RF(X ⊞ Y) = RF(X) ⊞ RF(Y)`
      (∀ (cX : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F))
        (_ : F.IsRightDerivedValueAt W X cX)
        (cY : Cocone (MorphismProperty.Under.forget W ⊤ Y ⋙ Under.forget Y ⋙ F))
        (_ : F.IsRightDerivedValueAt W Y cY)
        (cXY : Cocone (MorphismProperty.Under.forget W ⊤ (X ⊞ Y) ⋙ Under.forget (X ⊞ Y) ⋙ F))
        (_ : F.IsRightDerivedValueAt W (X ⊞ Y) cXY),
        ∃ (p₁ : cXY.pt ⟶ cX.pt) (p₂ : cXY.pt ⟶ cY.pt),
          (∀ (a : W.Under ⊤ (X ⊞ Y)) (b : W.Under ⊤ X) (g : a.right ⟶ b.right),
            biprod.fst ≫ b.hom = a.hom ≫ g → cXY.ι.app a ≫ p₁ = F.map g ≫ cX.ι.app b) ∧
          (∀ (a : W.Under ⊤ (X ⊞ Y)) (b : W.Under ⊤ Y) (g : a.right ⟶ b.right),
            biprod.snd ≫ b.hom = a.hom ≫ g → cXY.ι.app a ≫ p₂ = F.map g ≫ cY.ι.app b) ∧
          IsIso (biprod.lift p₁ p₂)) ∧
      -- `LF(X ⊞ Y) = LF(X) ⊞ LF(Y)`
      ∀ (cX : Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F))
        (_ : F.IsLeftDerivedValueAt W X cX)
        (cY : Cone (MorphismProperty.Over.forget W ⊤ Y ⋙ Over.forget Y ⋙ F))
        (_ : F.IsLeftDerivedValueAt W Y cY)
        (cXY : Cone (MorphismProperty.Over.forget W ⊤ (X ⊞ Y) ⋙ Over.forget (X ⊞ Y) ⋙ F))
        (_ : F.IsLeftDerivedValueAt W (X ⊞ Y) cXY),
        ∃ (p₁ : cXY.pt ⟶ cX.pt) (p₂ : cXY.pt ⟶ cY.pt),
          (∀ (a : W.Over ⊤ (X ⊞ Y)) (b : W.Over ⊤ X) (g : a.left ⟶ b.left),
            g ≫ b.hom = a.hom ≫ biprod.fst → p₁ ≫ cX.π.app b = cXY.π.app a ≫ F.map g) ∧
          (∀ (a : W.Over ⊤ (X ⊞ Y)) (b : W.Over ⊤ Y) (g : a.left ⟶ b.left),
            g ≫ b.hom = a.hom ≫ biprod.snd → p₂ ≫ cY.π.app b = cXY.π.app a ≫ F.map g) ∧
          IsIso (biprod.lift p₁ p₂) := by
  have := hW.hasLeftCalculusOfFractions
  have h₁ :=
    Functor.exists_isRightDerivedValueAt_and_isLeftDerivedValueAt_and_triangle_distinguished F W hW
    (Triangle.mk (biprod.inl : X ⟶ X ⊞ Y) (biprod.snd : X ⊞ Y ⟶ Y) 0)
    (binaryBiproductTriangle_distinguished X Y)
  have h₂ :=
    Functor.exists_isRightDerivedValueAt_and_isLeftDerivedValueAt_and_triangle_distinguished F W hW
    (Triangle.mk (biprod.inr : Y ⟶ X ⊞ Y) (biprod.fst : X ⊞ Y ⟶ X) 0)
    (binaryBiproductTriangle_inr_fst_distinguished X Y)
  refine ⟨fun hX hY => h₁.1.2.2.1 hY hX, fun hX hY => h₁.2.2.2.1 hY hX,
    exists_isRightDerivedValueAt_of_biprod F W hW X Y,
    exists_isLeftDerivedValueAt_of_biprod F W hW X Y, ?_, ?_⟩
  · intro cX hX cY hY cXY hXY
    obtain ⟨u, p₂, w, hdist, hu, hp₂, -⟩ := h₁.1.2.2.2 cX hX cXY hXY cY hY
    obtain ⟨u₂, p₁, -, -, hu₂, hp₁, -⟩ := h₂.1.2.2.2 cY hY cXY hXY cX hX
    exact ⟨p₁, p₂, hp₁, hp₂, isIso_biprod_lift_of_distTriang hdist
      (comp_eq_of_isDerivedMap W F (by simp) hX hu hp₁ (isDerivedMap_id W F cX))
      (comp_eq_of_isDerivedMap W F (by simp) hX hu hp₂ (isDerivedMap_zero W F cX cY))
      (comp_eq_of_isDerivedMap W F (by simp) hY hu₂ hp₁ (isDerivedMap_zero W F cY cX))
      (comp_eq_of_isDerivedMap W F (by simp) hY hu₂ hp₂ (isDerivedMap_id W F cY))⟩
  · have := hW.hasRightCalculusOfFractions
    intro cX hX cY hY cXY hXY
    obtain ⟨u, p₂, w, hdist, hu, hp₂, -⟩ := h₁.2.2.2.2 cX hX cXY hXY cY hY
    obtain ⟨u₂, p₁, -, -, hu₂, hp₁, -⟩ := h₂.2.2.2.2 cY hY cXY hXY cX hX
    -- the squares of Tag 05SC are written `a.hom ≫ f = k ≫ b.hom`, those of `LF(f)` the other
    -- way round
    have hu' := fun a b k h => hu a b k (Eq.symm h)
    have hu₂' := fun a b k h => hu₂ a b k (Eq.symm h)
    have hp₁' := fun a b k h => hp₁ a b k (Eq.symm h)
    have hp₂' := fun a b k h => hp₂ a b k (Eq.symm h)
    exact ⟨p₁, p₂, hp₁', hp₂', isIso_biprod_lift_of_distTriang hdist
      (comp_eq_of_isDerivedMapLeft (by simp) hX hu' hp₁' (isDerivedMapLeft_id cX))
      (comp_eq_of_isDerivedMapLeft (by simp) hY hu' hp₂' (isDerivedMapLeft_zero cX cY))
      (comp_eq_of_isDerivedMapLeft (by simp) hX hu₂' hp₁' (isDerivedMapLeft_zero cY cX))
      (comp_eq_of_isDerivedMapLeft (by simp) hY hu₂' hp₂' (isDerivedMapLeft_id cY))⟩


end CategoryTheory.Functor

end

end

section

/-!
# Direct summands of an object computing a derived functor compute it

Let `F : 𝒟 ⥤ 𝒟'` be a functor and let `W` be a saturated multiplicative system in `𝒟`
(Tag 05Q8). The right derived functor `RF` is *defined at* an object `X` when the ind-object
$$ X/W ⟶ 𝒟', \qquad (s : X ⟶ X') ⟼ F(X'), $$
is essentially constant, its value being `RF(X)`; the identity `𝟙 X` is one of the indices of
that ind-object, so a value carries a canonical map `F(X) ⟶ RF(X)`, and `X` *computes* `RF` when
`RF` is defined at `X` and this canonical map is an isomorphism. Dually, `LF` is defined at `X`
when the pro-object on `W/X` is essentially constant with value `LF(X)`, and `X` *computes* `LF`
when the canonical map `LF(X) ⟶ F(X)` is an isomorphism (Tags 05S9 and 05SX).

Computing a derived functor passes to direct summands: if `X ⊕ Y` computes `RF` then `X` and `Y`
compute `RF`, and likewise for `LF`. Indeed a value of `RF` at `X ⊕ Y` is then `F(X) ⊕ F(Y)`, the
functor `X/W × Y/W ⟶ (X ⊕ Y)/W`, `(s, s') ↦ s ⊕ s'`, is cofinal, and comparing the colimit of
`Hom(F(X' ⊕ Y'), Z)` with `Hom(F(X ⊕ Y), Z)` splits into the two summands.

## Main results

* `CategoryTheory.Functor.computesRightDerived_and_computesLeftDerived_of_biprod` (Tag 05T0):
  if `X ⊞ Y` computes `RF`, then `X` and `Y` compute `RF`; and the same for `LF`.

## Implementation notes

*Faithfulness.* (1) No hypothesis is dead: `hW` is used through both Ore conditions (the index
categories are filtered, resp. cofiltered), through MS1 (the identity index at which the
canonical map lives) and through MS4 (Tag 05Q9 identifies `W` with the morphisms inverted by the
localization functor, which is how `s ⊞ s'` is seen to lie in `W`); additivity of `F` is what
splits `F(X' ⊞ Y')` as `F(X') ⊞ F(Y')`; and binary biproducts in the source category are needed
to write `X ⊞ Y` at all. (2) The data are the source's: one class `W` of morphisms of the source
category, the index categories `X/W`, `Y/W`, `(X ⊞ Y)/W` of morphisms of `W` out of, resp. into,
the object in question, and the diagram valued in `𝒟'` through `F` — no localization of `𝒟` and
no change of `W`. (3) The canonical maps are pinned, not merely asserted to exist: "computes" is
Tag 05SX as stated in this project, invertibility of the coprojection, resp. projection, of the
value cocone, resp. cone, at the index `𝟙 X` — so the conclusion is about the source's map
`F(X) ⟶ RF(X)`, resp. `LF(X) ⟶ F(X)`, and not about the existence of some isomorphism.
(4) The instantiation is not degenerate: for `W = MorphismProperty.isomorphisms 𝒟` (a saturated
multiplicative system) every object computes `RF` and `LF`, so both hypotheses are satisfiable;
and both are genuine conditions, each implying that the derived functor is defined at `X ⊞ Y`.

*Generality: which part of Situation 05S8 is used.* The source states the lemma in Situation
05S8 — `F` exact between triangulated categories, `W` a saturated multiplicative system
compatible with the triangulated structure — but of that its proof uses only that `W` is a
saturated multiplicative system and that `F` is additive between additive categories: exactness
of `F`, the shifts, the distinguished triangles and compatibility with the triangulation appear
nowhere in it, the closure of `W` under `s ⊞ s'` coming from saturation via Tag 05Q9 and the
additivity of the localization functor rather than from the triangulation. So those hypotheses
are dropped and the statement is made for an additive functor between preadditive categories,
the source having binary biproducts; a pretriangulated category is preadditive with binary
biproducts, so the source's statement is the case of Situation 05S8. A zero object is not
assumed: a binary biproduct does not need one.

*No Karoubian hypothesis.* Tag 05SD(2) recovers *definedness* of `RF` at `X` and at `Y` from
definedness at `X ⊞ Y` only when `𝒟'` is Karoubian, through Tag 0A2G. Here no such hypothesis
appears, and none is needed: `X ⊞ Y` computing `RF` pins the value to be `F(X ⊞ Y)`, which
already is the direct sum of `F(X)` and `F(Y)`, so the summands need not be split off
abstractly. Adding `IsIdempotentComplete 𝒟'` would therefore be decoration.

*Direct sums, and both summands.* The source's `X ⊕ Y` is the biproduct `X ⊞ Y`. Both summands
are asserted, as in the source; deducing the assertion for `Y` from the one for `X` would need
invariance of "computes `RF`" under the isomorphism `X ⊞ Y ≅ Y ⊞ X`, which is a separate
statement.

*Why the identities instance.* `ComputesRightDerived` and `ComputesLeftDerived` need the index
`𝟙 X`, which `[W.ContainsIdentities]` provides. That instance is implied by `hW` (it is part of
MS1) and is taken as an instance argument only so that the two predicates elaborate, exactly as
in the statement for Tag 05SX; it is not an assumption beyond `hW`.

*Duality.* The assertion for `LF` is given directly in the pro-object form in which Tag 05S9
gives `IsLeftDerivedValueAt`, not as the assertion for `F.op` and `W.op`; the two agree through
the equivalence `(W.Over ⊤ X)ᵒᵖ ≌ W.op.Under ⊤ (Opposite.op X)`, which is a separate lemma. The
biproduct is self-dual, so the conclusion is not dualized.

*One theorem.* The two conjuncts are the tag's two assertions, for `RF` and for `LF`; they share
their hypotheses and are the same statement in dual index categories, so they are stated
together, as in the statement for Tag 05SD.

## Proof outline

# A direct summand of an object computing a derived functor computes it

Let `F : C ⥤ H` be a functor, `W` a saturated multiplicative system in `C` (Stacks 05Q8) and
`Z` an object of `C` isomorphic to a direct sum `A ⊞ B`. If `Z` computes the right derived
functor `RF` — the ind-object `Z/W ⟶ H`, `(s : Z ⟶ Z') ↦ F(Z')`, is essentially constant and
the canonical map `F(Z) ⟶ RF(Z)` is an isomorphism (Stacks 05SX) — then `A` computes `RF`, with
value `F(A)` and canonical map the identity. Dually for `LF`.

The proof does not go through the direct sum decomposition of the value. Writing `e` for the
canonical map `F(Z) ⟶ RF(Z)` and `θ : Z ≅ A ⊞ B` for the given isomorphism, each index
`a : A ⟶ A'` of `A/W` gives the index `θ ≫ (a ⊞ 𝟙_B)` of `Z/W`, whose coprojection composed with
`e⁻¹` is a retraction `ψ_a : F(A' ⊞ B) ⟶ F(Z)` of `F(θ ≫ (a ⊞ 𝟙_B))`; the maps
`F(A') ⟶ F(A' ⊞ B) ⟶ F(Z) ⟶ F(A)` built from `biprod.inl`, `ψ_a` and `θ ≫ biprod.fst` form a
cocone on the ind-object at `A` with vertex `F(A)` whose coprojection at the index `𝟙_A` is the
identity. That this cocone is again a value is `isRightDerivedValueAt_summandCocone`: essential
constancy of the ind-object at `Z` enlarges the twisted index `θ ≫ (a ⊞ 𝟙_B)` to an index
`w : Z ⟶ V` of `Z/W`, and the left Ore condition MS2 for `biprod.fst` turns `θ⁻¹ ≫ w` into a
square `biprod.fst ≫ α = (θ⁻¹ ≫ w) ≫ k` with `α ∈ W`; that `α` is the enlargement of `a` that
essential constancy of the ind-object at `A` asks for.

## Implementation notes

*One lemma for both summands.* The core is proved for an object `Z` *isomorphic* to `A ⊞ B` and
concludes about the first summand `A`; the assertion for the second summand of `X ⊞ Y` is then
the same lemma along the braiding `X ⊞ Y ≅ Y ⊞ X`, and no invariance of "computes `RF`" under
isomorphisms of the object is needed separately. Isomorphisms lie in `W` by MS4, which is what
makes the twisted index `θ ≫ (a ⊞ 𝟙_B)` an index at all.

*What the argument uses.* Of the hypotheses of Stacks 05T0 the argument uses that `W` is a
saturated multiplicative system — MS4 through `MorphismProperty.IsSaturated.invertedClosure_eq`,
which is how `a ⊞ b` is seen to lie in `W` (`mem_biprod_map`), and one Ore condition — and that
`C` is preadditive with binary biproducts. Additivity of `F` is not used: the value at the
summand is produced as `F(A)` with the identity as its canonical map, so the direct sum
decomposition `RF(X ⊞ Y) = F(X) ⊞ F(Y)` of the source's proof never has to be exhibited.

*Less than cofinality.* The source deduces essential constancy at the summand from cofinality of
`A/W × B/W ⟶ (A ⊞ B)/W`, `(a, b) ↦ a ⊞ b`. Only the first-summand half of that is used here, and
only in the form of a single Ore square: MS2 for `biprod.fst`, resp. for `biprod.inl`, applied to
one index of `(A ⊞ B)/W`, resp. of `W/(A ⊞ B)`. The second summand `β` and the assembly of
`α ⊞ β` by `biprod.lift`, resp. `biprod.desc`, never enter, because the candidate cocone is built
from `biprod.inl` and `biprod.fst` rather than from a decomposition of the value.

*Duality.* The two halves are written out separately, in the ind-object and the pro-object form
in which Stacks 05S9 states the two notions of value, rather than one being deduced from the
other in the opposite category.

## References

* [Stacks Project, Tag 05T0](https://stacks.math.columbia.edu/tag/05T0); the situation is
  Tag 05S8, definedness and values are Tag 05S9, "computes" is Tag 05SX, saturated
  multiplicative systems and their inverted closure are Tags 05Q8 and 05Q9, the direct sum
  statement for definedness is Tag 05SD, and the cofinality input is Tag 0A1S with the
  characterisation Tag 05PY(4).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public section

namespace DerivedFunctorBiprodComputes

open CochainComplex.FilteredInjective.Hom (biprod_map_id)


open CategoryTheory Limits
open DerivedFunctorBiprod

universe v₁ v₂ u₁ u₂

section Saturated

variable {C : Type u₁} [Category.{v₁} C] {W : MorphismProperty C}

/-- An isomorphism belongs to a saturated multiplicative system: MS4 applied to
`f⁻¹ ≫ f = 𝟙` and `f ≫ f⁻¹ = 𝟙`. -/
public lemma mem_of_isIso (hW : W.IsSaturated) {X Y : C} (f : X ⟶ Y)
    [IsIso f] : W f :=
  DerivedFunctorValues.isomorphisms_le_of_isSaturated hW f ‹IsIso f›

/-- **MS2, the left Ore condition**: a morphism `f : X ⟶ Y` and a morphism `w : X ⟶ V` of `W`
out of the same object fit into a square `f ≫ α = w ≫ k` with `α` again in `W`. -/
private lemma exists_leftOre (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] {X Y V : C}
    (f : X ⟶ Y) {w : X ⟶ V} (hw : W w) :
    ∃ (Y' : C) (α : Y ⟶ Y') (k : V ⟶ Y'), W α ∧ f ≫ α = w ≫ k := by
  obtain ⟨ψ, hψ⟩ := (MorphismProperty.RightFraction.mk w hw f).exists_leftFraction
  exact ⟨_, ψ.s, ψ.f, ψ.hs, hψ⟩

/-- **MS2, the right Ore condition**: a morphism `f : Y ⟶ X` and a morphism `w : V ⟶ X` of `W`
into the same object fit into a square `α ≫ f = k ≫ w` with `α` again in `W`. -/
private lemma exists_rightOre (W : MorphismProperty C) [W.HasRightCalculusOfFractions] {X Y V : C}
    (f : Y ⟶ X) {w : V ⟶ X} (hw : W w) :
    ∃ (Y' : C) (α : Y' ⟶ Y) (k : Y' ⟶ V), W α ∧ α ≫ f = k ≫ w := by
  obtain ⟨ψ, hψ⟩ := (MorphismProperty.LeftFraction.mk f w hw).exists_rightFraction
  exact ⟨_, ψ.s, ψ.f, ψ.hs, hψ⟩

end Saturated

section Biprod

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] {W : MorphismProperty C}

/-- The direct sum of two composites is the composite of the two direct sums. -/
private alias biprod_map_comp := DerivedFunctorBiprod.biprod_map_comp

/-- **A saturated multiplicative system is closed under direct sums.** Being saturated, `W` is
the class of morphisms inverted by the additive localization functor `W.Q`, and an additive
functor takes the biproduct identities of `X ⊞ Y` to identities in the localization, so
`W.Q(s ⊞ s')` has the explicit inverse
`Q(fst) ≫ Q(s)⁻¹ ≫ Q(inl) + Q(snd) ≫ Q(s')⁻¹ ≫ Q(inr)`. -/
private alias mem_biprod_map := DerivedFunctorBiprod.mem_biprod_map

end Biprod

section Values

variable {C : Type u₁} [Category.{v₁} C] {H : Type u₂} [Category.{v₂} H]
  {W : MorphismProperty C} {F : C ⥤ H}

/-- The projection of a cone on the pro-object at `Z`, with its target written as `F(b.left)`. -/
private abbrev proj {Z : C}
    (c : Cone (MorphismProperty.Over.forget W ⊤ Z ⋙ Over.forget Z ⋙ F))
    (b : W.Over ⊤ Z) : c.pt ⟶ F.obj b.left := c.π.app b

/-- A transition morphism of the ind-object at `Z`, followed by the coprojection at its target,
is the coprojection at its source. -/
private lemma map_right_comp_coprj {Z : C}
    (c : Cocone (MorphismProperty.Under.forget W ⊤ Z ⋙ Under.forget Z ⋙ F))
    {a b : W.Under ⊤ Z} (u : a ⟶ b) : F.map u.right ≫ coprj c b = coprj c a := c.w u

/-- The projection at the source of a transition morphism of the pro-object at `Z`, followed by
that morphism, is the projection at its target. -/
private lemma proj_comp_map_left {Z : C}
    (c : Cone (MorphismProperty.Over.forget W ⊤ Z ⋙ Over.forget Z ⋙ F))
    {a b : W.Over ⊤ Z} (u : a ⟶ b) : proj c a ≫ F.map u.left = proj c b := c.w u

variable [W.ContainsIdentities]

/-- The index `𝟙 Z` of the ind-object at `Z`, at which the canonical map `F(Z) ⟶ RF(Z)` lives. -/
private abbrev idUnder (W : MorphismProperty C) [W.ContainsIdentities] (Z : C) : W.Under ⊤ Z :=
  MorphismProperty.Under.mk ⊤ (𝟙 Z) (W.id_mem Z)

/-- The index `𝟙 Z` of the pro-object at `Z`, at which the canonical map `LF(Z) ⟶ F(Z)` lives. -/
private abbrev idOver (W : MorphismProperty C) [W.ContainsIdentities] (Z : C) : W.Over ⊤ Z :=
  MorphismProperty.Over.mk ⊤ (𝟙 Z) (W.id_mem Z)

@[local simp]
private lemma idUnder_hom (Z : C) : (idUnder W Z).hom = 𝟙 Z := rfl

@[local simp]
private lemma idOver_hom (Z : C) : (idOver W Z).hom = 𝟙 Z := rfl

/-- The canonical map `F(Z) ⟶ RF(Z)`: the coprojection at the index `𝟙 Z`. -/
private abbrev canCoprj {Z : C}
    (c : Cocone (MorphismProperty.Under.forget W ⊤ Z ⋙ Under.forget Z ⋙ F)) :
    F.obj Z ⟶ c.pt := c.ι.app (idUnder W Z)

/-- The canonical map `LF(Z) ⟶ F(Z)`: the projection at the index `𝟙 Z`. -/
private abbrev canProj {Z : C}
    (c : Cone (MorphismProperty.Over.forget W ⊤ Z ⋙ Over.forget Z ⋙ F)) :
    c.pt ⟶ F.obj Z := c.π.app (idOver W Z)

/-- Every coprojection of a cocone on the ind-object at `Z`, precomposed with the image of the
index, is the canonical map: the index `𝟙 Z` maps to every index. -/
private lemma map_hom_comp_coprj {Z : C}
    (c : Cocone (MorphismProperty.Under.forget W ⊤ Z ⋙ Under.forget Z ⋙ F)) (b : W.Under ⊤ Z) :
    F.map b.hom ≫ coprj c b = canCoprj c :=
  map_right_comp_coprj c
    (MorphismProperty.Under.homMk (A := idUnder W Z) (B := b) b.hom (Category.id_comp b.hom))

/-- Every projection of a cone on the pro-object at `Z`, postcomposed with the image of the
index, is the canonical map: every index maps to the index `𝟙 Z`. -/
private lemma proj_comp_map_hom {Z : C}
    (c : Cone (MorphismProperty.Over.forget W ⊤ Z ⋙ Over.forget Z ⋙ F)) (b : W.Over ⊤ Z) :
    proj c b ≫ F.map b.hom = canProj c :=
  proj_comp_map_left c
    (MorphismProperty.Over.homMk (A := b) (B := idOver W Z) b.hom (Category.comp_id b.hom))

/-- **Essential constancy of the ind-object at an object computing `RF`, read at the index
`𝟙 Z`.** Let `c` be a value of `RF` at `Z` and let `ρ` be a section of the canonical map
`F(Z) ⟶ RF(Z)`. Then every transition morphism of the ind-object factors, after enlarging its
target, through the retraction `c.ι.app b ≫ ρ` of `F(b.hom)`. -/
private lemma exists_map_right_eq_coprj_comp {Z : C}
    (c : Cocone (MorphismProperty.Under.forget W ⊤ Z ⋙ Under.forget Z ⋙ F))
    (hc : F.IsRightDerivedValueAt W Z c) (ρ : c.pt ⟶ F.obj Z) (hρ : ρ ≫ canCoprj c = 𝟙 c.pt)
    (b : W.Under ⊤ Z) :
    ∃ (t : W.Under ⊤ Z) (p : b ⟶ t), F.map p.right = coprj c b ≫ ρ ≫ F.map t.hom := by
  obtain ⟨z₁, r₁, -, hcof⟩ := hc
  obtain ⟨t, p, w, hpw⟩ := hcof b
  refine ⟨t, p, ?_⟩
  have hpw' : F.map p.right = coprj c b ≫ r₁ ≫ F.map w.right := hpw
  have h1 : canCoprj c ≫ r₁ ≫ F.map w.right = F.map t.hom :=
    calc canCoprj c ≫ r₁ ≫ F.map w.right
        = (F.map b.hom ≫ coprj c b) ≫ r₁ ≫ F.map w.right := by rw [map_hom_comp_coprj c b]
      _ = F.map b.hom ≫ F.map p.right := by rw [Category.assoc, ← hpw']
      _ = F.map t.hom := by rw [← F.map_comp, MorphismProperty.Under.w p]
  calc F.map p.right = coprj c b ≫ r₁ ≫ F.map w.right := hpw'
    _ = coprj c b ≫ (ρ ≫ canCoprj c) ≫ r₁ ≫ F.map w.right := by rw [hρ, Category.id_comp]
    _ = coprj c b ≫ ρ ≫ F.map t.hom := by rw [Category.assoc, h1]

/-- **Essential constancy of the pro-object at an object computing `LF`, read at the index
`𝟙 Z`**, the formal dual of `exists_map_right_eq_coprj_comp`. -/
private lemma exists_map_left_eq_comp_proj {Z : C}
    (c : Cone (MorphismProperty.Over.forget W ⊤ Z ⋙ Over.forget Z ⋙ F))
    (hc : F.IsLeftDerivedValueAt W Z c) (ρ : F.obj Z ⟶ c.pt) (hρ : canProj c ≫ ρ = 𝟙 c.pt)
    (b : W.Over ⊤ Z) :
    ∃ (t : W.Over ⊤ Z) (p : t ⟶ b), F.map p.left = F.map t.hom ≫ ρ ≫ proj c b := by
  obtain ⟨z₁, r₁, -, hcof⟩ := hc
  obtain ⟨t, p, w, hpw⟩ := hcof b
  refine ⟨t, p, ?_⟩
  have hpw' : F.map p.left = F.map w.left ≫ r₁ ≫ proj c b := hpw
  have h1 : F.map w.left ≫ r₁ ≫ canProj c = F.map t.hom :=
    calc F.map w.left ≫ r₁ ≫ canProj c
        = F.map w.left ≫ r₁ ≫ proj c b ≫ F.map b.hom := by rw [proj_comp_map_hom c b]
      _ = F.map p.left ≫ F.map b.hom := by rw [hpw', Category.assoc, Category.assoc]
      _ = F.map t.hom := by rw [← F.map_comp, MorphismProperty.Over.w p]
  calc F.map p.left = F.map w.left ≫ r₁ ≫ proj c b := hpw'
    _ = F.map w.left ≫ r₁ ≫ (canProj c ≫ ρ) ≫ proj c b := by rw [hρ, Category.id_comp]
    _ = F.map t.hom ≫ ρ ≫ proj c b := by rw [← h1]; simp only [Category.assoc]

end Values

section Core

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasBinaryBiproducts C]
  {H : Type u₂} [Category.{v₂} H] {F : C ⥤ H} {W : MorphismProperty C} [W.ContainsIdentities]
  {A B Z : C}

/-- The index `θ ≫ (a ⊞ 𝟙_B)` of `Z/W` attached to an index `a` of `A/W` by an isomorphism
`θ : Z ≅ A ⊞ B`. It lies in `W` because `W` is closed under direct sums and contains the
isomorphism `θ`. -/
private noncomputable def twistUnder (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B)
    (a : W.Under ⊤ A) : W.Under ⊤ Z :=
  haveI := hW.isMultiplicative
  MorphismProperty.Under.mk ⊤ (θ.hom ≫ biprod.map a.hom (𝟙 B))
    (W.comp_mem _ _ (mem_of_isIso hW θ.hom) (mem_biprod_map hW a.prop (W.id_mem B)))

@[local simp]
private lemma twistUnder_right (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B) (a : W.Under ⊤ A) :
    (twistUnder hW θ a).right = (a.right ⊞ B) := rfl

@[local simp]
private lemma twistUnder_hom (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B) (a : W.Under ⊤ A) :
    (twistUnder hW θ a).hom = θ.hom ≫ biprod.map a.hom (𝟙 B) := rfl

/-- The index `(a ⊞ 𝟙_B) ≫ θ⁻¹` of `W/Z` attached to an index `a` of `W/A` by an isomorphism
`θ : Z ≅ A ⊞ B`, the pro-side counterpart of `twistUnder`. -/
private noncomputable def twistOver (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B)
    (a : W.Over ⊤ A) : W.Over ⊤ Z :=
  haveI := hW.isMultiplicative
  MorphismProperty.Over.mk ⊤ (biprod.map a.hom (𝟙 B) ≫ θ.inv)
    (W.comp_mem _ _ (mem_biprod_map hW a.prop (W.id_mem B)) (mem_of_isIso hW θ.inv))

@[local simp]
private lemma twistOver_left (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B) (a : W.Over ⊤ A) :
    (twistOver hW θ a).left = (a.left ⊞ B) := rfl

@[local simp]
private lemma twistOver_hom (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B) (a : W.Over ⊤ A) :
    (twistOver hW θ a).hom = biprod.map a.hom (𝟙 B) ≫ θ.inv := rfl

/-- The candidate coprojection `F(A') ⟶ F(A)` of the value of `RF` at the summand `A`: the
composite of `biprod.inl`, of the retraction `c.ι.app (θ ≫ (a ⊞ 𝟙_B)) ≫ ρ` of
`F(θ ≫ (a ⊞ 𝟙_B))` and of `F(θ ≫ biprod.fst)`. -/
private noncomputable def summandCoprj (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B)
    (c : Cocone (MorphismProperty.Under.forget W ⊤ Z ⋙ Under.forget Z ⋙ F))
    (ρ : c.pt ⟶ F.obj Z) (a : W.Under ⊤ A) : F.obj a.right ⟶ F.obj A :=
  F.map biprod.inl ≫ coprj c (twistUnder hW θ a) ≫ ρ ≫ F.map (θ.hom ≫ biprod.fst)

private lemma summandCoprj_def (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B)
    (c : Cocone (MorphismProperty.Under.forget W ⊤ Z ⋙ Under.forget Z ⋙ F))
    (ρ : c.pt ⟶ F.obj Z) (a : W.Under ⊤ A) :
    summandCoprj hW θ c ρ a =
      F.map biprod.inl ≫ coprj c (twistUnder hW θ a) ≫ ρ ≫ F.map (θ.hom ≫ biprod.fst) := rfl

/-- The candidate projection `F(A) ⟶ F(A')` of the value of `LF` at the summand `A`, the pro-side
counterpart of `summandCoprj`. -/
private noncomputable def summandProj (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B)
    (c : Cone (MorphismProperty.Over.forget W ⊤ Z ⋙ Over.forget Z ⋙ F))
    (ρ : F.obj Z ⟶ c.pt) (a : W.Over ⊤ A) : F.obj A ⟶ F.obj a.left :=
  F.map (biprod.inl ≫ θ.inv) ≫ ρ ≫ proj c (twistOver hW θ a) ≫ F.map biprod.fst

private lemma summandProj_def (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B)
    (c : Cone (MorphismProperty.Over.forget W ⊤ Z ⋙ Over.forget Z ⋙ F))
    (ρ : F.obj Z ⟶ c.pt) (a : W.Over ⊤ A) :
    summandProj hW θ c ρ a =
      F.map (biprod.inl ≫ θ.inv) ≫ ρ ≫ proj c (twistOver hW θ a) ≫ F.map biprod.fst := rfl

/-- **The retraction at the index `𝟙 A` is `F(θ⁻¹)`.** The twisted index of `𝟙 A` is `θ` itself,
so the coprojection there composed with the inverse `ρ` of the canonical map is a retraction of
`F(θ)`, hence its inverse. -/
private lemma coprj_twistUnder_idUnder_comp (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B)
    (c : Cocone (MorphismProperty.Under.forget W ⊤ Z ⋙ Under.forget Z ⋙ F))
    (ρ : c.pt ⟶ F.obj Z) (hρ : canCoprj c ≫ ρ = 𝟙 (F.obj Z)) :
    coprj c (twistUnder hW θ (idUnder W A)) ≫ ρ = F.map θ.inv := by
  have hid : (twistUnder hW θ (idUnder W A)).hom = θ.hom := by
    show θ.hom ≫ biprod.map (𝟙 A) (𝟙 B) = θ.hom
    rw [biprod_map_id, Category.comp_id]
  have key : F.map θ.hom ≫ coprj c (twistUnder hW θ (idUnder W A)) ≫ ρ = 𝟙 (F.obj Z) := by
    rw [← hid, ← Category.assoc, map_hom_comp_coprj c (twistUnder hW θ (idUnder W A)), hρ]
  rw [← cancel_epi (F.map θ.hom), key, ← F.map_comp, θ.hom_inv_id, F.map_id]

/-- **The section at the index `𝟙 A` is `F(θ)`**, the pro-side counterpart of
`coprj_twistUnder_idUnder_comp`. -/
private lemma comp_proj_twistOver_idOver (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B)
    (c : Cone (MorphismProperty.Over.forget W ⊤ Z ⋙ Over.forget Z ⋙ F))
    (ρ : F.obj Z ⟶ c.pt) (hρ : ρ ≫ canProj c = 𝟙 (F.obj Z)) :
    ρ ≫ proj c (twistOver hW θ (idOver W A)) = F.map θ.hom := by
  have hid : (twistOver hW θ (idOver W A)).hom = θ.inv := by
    show biprod.map (𝟙 A) (𝟙 B) ≫ θ.inv = θ.inv
    rw [biprod_map_id, Category.id_comp]
  have key : ρ ≫ proj c (twistOver hW θ (idOver W A)) ≫ F.map θ.inv = 𝟙 (F.obj Z) := by
    rw [← hid, proj_comp_map_hom c (twistOver hW θ (idOver W A)), hρ]
  rw [← cancel_mono (F.map θ.inv), Category.assoc, key, ← F.map_comp, θ.hom_inv_id, F.map_id]

/-- The coprojection of the candidate value at the index `𝟙 A` is the identity of `F(A)`:
`biprod.inl ≫ θ⁻¹ ≫ θ ≫ biprod.fst = 𝟙 A`. -/
private lemma summandCoprj_idUnder (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B)
    (c : Cocone (MorphismProperty.Under.forget W ⊤ Z ⋙ Under.forget Z ⋙ F))
    (ρ : c.pt ⟶ F.obj Z) (hρ : canCoprj c ≫ ρ = 𝟙 (F.obj Z)) :
    summandCoprj hW θ c ρ (idUnder W A) = 𝟙 (F.obj A) := by
  have hcomp : (biprod.inl : A ⟶ A ⊞ B) ≫ θ.inv ≫ θ.hom ≫ biprod.fst = 𝟙 A := by simp
  rw [summandCoprj_def, reassoc_of% (coprj_twistUnder_idUnder_comp hW θ c ρ hρ),
    ← F.map_comp, ← F.map_comp]
  exact (Functor.congr_map F hcomp).trans (F.map_id A)

/-- The projection of the candidate value at the index `𝟙 A` is the identity of `F(A)`. -/
private lemma summandProj_idOver (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B)
    (c : Cone (MorphismProperty.Over.forget W ⊤ Z ⋙ Over.forget Z ⋙ F))
    (ρ : F.obj Z ⟶ c.pt) (hρ : ρ ≫ canProj c = 𝟙 (F.obj Z)) :
    summandProj hW θ c ρ (idOver W A) = 𝟙 (F.obj A) := by
  have hcomp : ((biprod.inl : A ⟶ A ⊞ B) ≫ θ.inv) ≫ θ.hom ≫ biprod.fst = 𝟙 A := by simp
  rw [summandProj_def, reassoc_of% (comp_proj_twistOver_idOver hW θ c ρ hρ),
    ← F.map_comp, ← F.map_comp]
  exact (Functor.congr_map F hcomp).trans (F.map_id A)

/-- The candidate coprojections form a cocone: a transition morphism `u` of `A/W` is carried to
the transition morphism `u ⊞ 𝟙_B` of `Z/W`, and `biprod.inl` is natural in `u`. -/
private lemma map_right_comp_summandCoprj (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B)
    (c : Cocone (MorphismProperty.Under.forget W ⊤ Z ⋙ Under.forget Z ⋙ F))
    (ρ : c.pt ⟶ F.obj Z) {a b : W.Under ⊤ A} (u : a ⟶ b) :
    F.map u.right ≫ summandCoprj hW θ c ρ b = summandCoprj hW θ c ρ a := by
  have hw : (twistUnder hW θ a).hom ≫ biprod.map u.right (𝟙 B) = (twistUnder hW θ b).hom := by
    show (θ.hom ≫ biprod.map a.hom (𝟙 B)) ≫ biprod.map u.right (𝟙 B)
      = θ.hom ≫ biprod.map b.hom (𝟙 B)
    rw [Category.assoc, biprod_map_comp, Category.comp_id, MorphismProperty.Under.w u]
    rfl
  have hcop : F.map (biprod.map u.right (𝟙 B)) ≫ coprj c (twistUnder hW θ b)
      = coprj c (twistUnder hW θ a) :=
    map_right_comp_coprj c (MorphismProperty.Under.homMk (A := twistUnder hW θ a)
      (B := twistUnder hW θ b) (biprod.map u.right (𝟙 B)) hw)
  simp only [summandCoprj_def]
  rw [← hcop]
  simp only [← Category.assoc, ← F.map_comp, biprod.inl_map]
  rfl

/-- The candidate projections form a cone, the pro-side counterpart of
`map_right_comp_summandCoprj`. -/
private lemma summandProj_comp_map_left (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B)
    (c : Cone (MorphismProperty.Over.forget W ⊤ Z ⋙ Over.forget Z ⋙ F))
    (ρ : F.obj Z ⟶ c.pt) {a b : W.Over ⊤ A} (u : a ⟶ b) :
    summandProj hW θ c ρ a ≫ F.map u.left = summandProj hW θ c ρ b := by
  have hw : biprod.map u.left (𝟙 B) ≫ (twistOver hW θ b).hom = (twistOver hW θ a).hom := by
    show biprod.map u.left (𝟙 B) ≫ biprod.map b.hom (𝟙 B) ≫ θ.inv
      = biprod.map a.hom (𝟙 B) ≫ θ.inv
    rw [← Category.assoc, biprod_map_comp, Category.comp_id, MorphismProperty.Over.w u]
    rfl
  have hproj : proj c (twistOver hW θ a) ≫ F.map (biprod.map u.left (𝟙 B))
      = proj c (twistOver hW θ b) :=
    proj_comp_map_left c (MorphismProperty.Over.homMk (A := twistOver hW θ a)
      (B := twistOver hW θ b) (biprod.map u.left (𝟙 B)) hw)
  simp only [summandProj_def]
  rw [← hproj]
  simp only [Category.assoc, ← F.map_comp, biprod.map_fst]

/-- The candidate value of `RF` at the summand `A`: the cocone on the ind-object at `A` with
vertex `F(A)` whose coprojections are the maps `summandCoprj`. -/
private noncomputable def summandCocone (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B)
    (c : Cocone (MorphismProperty.Under.forget W ⊤ Z ⋙ Under.forget Z ⋙ F))
    (ρ : c.pt ⟶ F.obj Z) :
    Cocone (MorphismProperty.Under.forget W ⊤ A ⋙ Under.forget A ⋙ F) where
  pt := F.obj A
  ι :=
    { app := fun a => summandCoprj hW θ c ρ a
      naturality := fun a b u => by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        exact map_right_comp_summandCoprj hW θ c ρ u }

@[local simp]
private lemma summandCocone_ι_app (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B)
    (c : Cocone (MorphismProperty.Under.forget W ⊤ Z ⋙ Under.forget Z ⋙ F))
    (ρ : c.pt ⟶ F.obj Z) (a : W.Under ⊤ A) :
    (summandCocone hW θ c ρ).ι.app a = summandCoprj hW θ c ρ a := rfl

/-- The candidate value of `LF` at the summand `A`: the cone on the pro-object at `A` with vertex
`F(A)` whose projections are the maps `summandProj`. -/
private noncomputable def summandCone (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B)
    (c : Cone (MorphismProperty.Over.forget W ⊤ Z ⋙ Over.forget Z ⋙ F))
    (ρ : F.obj Z ⟶ c.pt) :
    Cone (MorphismProperty.Over.forget W ⊤ A ⋙ Over.forget A ⋙ F) where
  pt := F.obj A
  π :=
    { app := fun a => summandProj hW θ c ρ a
      naturality := fun a b u => by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
        exact (summandProj_comp_map_left hW θ c ρ u).symm }

@[local simp]
private lemma summandCone_π_app (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B)
    (c : Cone (MorphismProperty.Over.forget W ⊤ Z ⋙ Over.forget Z ⋙ F))
    (ρ : F.obj Z ⟶ c.pt) (a : W.Over ⊤ A) :
    (summandCone hW θ c ρ).π.app a = summandProj hW θ c ρ a := rfl

/-- **The candidate value of `RF` at the summand is essentially constant.** This is the heart of
Stacks 05T0. Let `s : A ⟶ A'` be an index of `A/W`. Essential constancy of the ind-object at `Z`
enlarges the twisted index `θ ≫ (s ⊞ 𝟙_B)` to an index `w` of `Z/W`, by a morphism `p` whose
image under `F` is the retraction `ψ_s ≫ F(w)` (`exists_map_right_eq_coprj_comp`); the left Ore
condition MS2 for `biprod.fst` applied to the index `θ⁻¹ ≫ w` of `(A ⊞ B)/W` produces an index
`α : A ⟶ A''` of `A/W` and a `k` with `biprod.fst ≫ α = (θ⁻¹ ≫ w) ≫ k`. Then `α` enlarges `s`,
by `biprod.inl ≫ p ≫ k`, and `F` of that morphism factors through the candidate coprojection at
`s` as essential constancy at `A` demands. -/
private lemma isRightDerivedValueAt_summandCocone (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B)
    (c : Cocone (MorphismProperty.Under.forget W ⊤ Z ⋙ Under.forget Z ⋙ F))
    (hc : F.IsRightDerivedValueAt W Z c) (ρ : c.pt ⟶ F.obj Z)
    (hρ₁ : canCoprj c ≫ ρ = 𝟙 (F.obj Z)) (hρ₂ : ρ ≫ canCoprj c = 𝟙 c.pt) :
    F.IsRightDerivedValueAt W A (summandCocone hW θ c ρ) := by
  have := hW.isMultiplicative
  have := hW.hasLeftCalculusOfFractions
  refine ⟨idUnder W A, 𝟙 (F.obj A), ?_, fun s => ?_⟩
  · show 𝟙 (F.obj A) ≫ summandCoprj hW θ c ρ (idUnder W A) = 𝟙 (F.obj A)
    rw [Category.id_comp, summandCoprj_idUnder hW θ c ρ hρ₁]
  obtain ⟨w, p, hp⟩ := exists_map_right_eq_coprj_comp c hc ρ hρ₂ (twistUnder hW θ s)
  obtain ⟨A'', α, k, hα, hk⟩ := exists_leftOre W (biprod.fst : A ⊞ B ⟶ A)
    (W.comp_mem _ _ (mem_of_isIso hW θ.inv) w.prop)
  have hpw : biprod.map s.hom (𝟙 B) ≫ p.right = θ.inv ≫ w.hom := by
    rw [← MorphismProperty.Under.w p, twistUnder_hom]
    simp
  have hu : s.hom ≫ biprod.inl ≫ p.right ≫ k = α :=
    calc s.hom ≫ biprod.inl ≫ p.right ≫ k
        = biprod.inl ≫ (biprod.map s.hom (𝟙 B) ≫ p.right) ≫ k := by simp
      _ = biprod.inl ≫ biprod.fst ≫ α := by rw [hpw, ← hk]
      _ = α := by simp
  have hkey : F.map w.hom ≫ F.map k = F.map (θ.hom ≫ biprod.fst) ≫ F.map α := by
    rw [← F.map_comp, ← F.map_comp]
    exact Functor.congr_map F
      (calc w.hom ≫ k = θ.hom ≫ (θ.inv ≫ w.hom) ≫ k := by simp
        _ = (θ.hom ≫ biprod.fst) ≫ α := by rw [← hk]; simp)
  refine ⟨MorphismProperty.Under.mk ⊤ α hα,
    MorphismProperty.Under.homMk (biprod.inl ≫ p.right ≫ k) hu,
    MorphismProperty.Under.homMk α (Category.id_comp α), ?_⟩
  show F.map (biprod.inl ≫ p.right ≫ k)
    = summandCoprj hW θ c ρ s ≫ 𝟙 (F.obj A) ≫ F.map α
  rw [Category.id_comp, summandCoprj_def, F.map_comp, F.map_comp, hp]
  simp only [Category.assoc, hkey]

/-- **The candidate value of `LF` at the summand is essentially constant**, the pro-side
counterpart of `exists_map_right_eq_summandCoprj_comp`: the right Ore condition MS2 for
`biprod.inl` replaces the left one for `biprod.fst`. -/
private lemma isLeftDerivedValueAt_summandCone (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B)
    (c : Cone (MorphismProperty.Over.forget W ⊤ Z ⋙ Over.forget Z ⋙ F))
    (hc : F.IsLeftDerivedValueAt W Z c) (ρ : F.obj Z ⟶ c.pt)
    (hρ₁ : ρ ≫ canProj c = 𝟙 (F.obj Z)) (hρ₂ : canProj c ≫ ρ = 𝟙 c.pt) :
    F.IsLeftDerivedValueAt W A (summandCone hW θ c ρ) := by
  have := hW.isMultiplicative
  have := hW.hasRightCalculusOfFractions
  refine ⟨idOver W A, 𝟙 (F.obj A), ?_, fun s => ?_⟩
  · show summandProj hW θ c ρ (idOver W A) ≫ 𝟙 (F.obj A) = 𝟙 (F.obj A)
    rw [summandProj_idOver hW θ c ρ hρ₁, Category.id_comp]
  obtain ⟨w, p, hp⟩ := exists_map_left_eq_comp_proj c hc ρ hρ₂ (twistOver hW θ s)
  obtain ⟨A'', α, k, hα, hk⟩ := exists_rightOre W (biprod.inl : A ⟶ A ⊞ B)
    (W.comp_mem _ _ w.prop (mem_of_isIso hW θ.hom))
  have hpw : p.left ≫ biprod.map s.hom (𝟙 B) = w.hom ≫ θ.hom := by
    rw [← MorphismProperty.Over.w p, twistOver_hom]
    simp
  have hu : (k ≫ p.left ≫ biprod.fst) ≫ s.hom = α :=
    calc (k ≫ p.left ≫ biprod.fst) ≫ s.hom
        = (k ≫ p.left ≫ biprod.map s.hom (𝟙 B)) ≫ biprod.fst := by simp
      _ = (α ≫ biprod.inl) ≫ biprod.fst := by rw [hpw]; exact hk.symm =≫ biprod.fst
      _ = α := by simp
  have hkey : F.map k ≫ F.map w.hom = F.map α ≫ F.map (biprod.inl ≫ θ.inv) := by
    rw [← F.map_comp, ← F.map_comp]
    exact Functor.congr_map F
      (calc k ≫ w.hom = (k ≫ w.hom ≫ θ.hom) ≫ θ.inv := by simp
        _ = α ≫ biprod.inl ≫ θ.inv := by rw [← hk]; simp)
  refine ⟨MorphismProperty.Over.mk ⊤ α hα,
    MorphismProperty.Over.homMk (k ≫ p.left ≫ biprod.fst) hu,
    MorphismProperty.Over.homMk α (Category.comp_id α), ?_⟩
  show F.map (k ≫ p.left ≫ biprod.fst)
    = F.map α ≫ 𝟙 (F.obj A) ≫ summandProj hW θ c ρ s
  rw [Category.id_comp, summandProj_def, F.map_comp, F.map_comp, hp]
  simp only [Category.assoc]
  rw [reassoc_of% hkey]

/-- **Stacks 05T0 for `RF`, at the first summand.** Let `W` be a saturated multiplicative system
in `C` and let `Z` be an object isomorphic to a direct sum `A ⊞ B`. If `Z` computes the right
derived functor of `F` relative to `W`, then so does `A`, the value being `F(A)` with the
identity as its canonical map. -/
private theorem computesRightDerived_of_iso_biprod (F : C ⥤ H) (W : MorphismProperty C)
    [W.ContainsIdentities] (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B)
    (h : F.ComputesRightDerived W Z) : F.ComputesRightDerived W A := by
  obtain ⟨c, hc, hiso⟩ := h
  have : IsIso (canCoprj c) := hiso
  refine ⟨summandCocone hW θ c (inv (canCoprj c)),
    isRightDerivedValueAt_summandCocone hW θ c hc _ (IsIso.hom_inv_id _) (IsIso.inv_hom_id _), ?_⟩
  rw [summandCocone_ι_app,
    summandCoprj_idUnder hW θ c (inv (canCoprj c)) (IsIso.hom_inv_id _)]
  exact IsIso.id _

/-- **Stacks 05T0 for `LF`, at the first summand**, the formal dual of
`computesRightDerived_of_iso_biprod`. -/
private theorem computesLeftDerived_of_iso_biprod (F : C ⥤ H) (W : MorphismProperty C)
    [W.ContainsIdentities] (hW : W.IsSaturated) (θ : Z ≅ A ⊞ B)
    (h : F.ComputesLeftDerived W Z) : F.ComputesLeftDerived W A := by
  obtain ⟨c, hc, hiso⟩ := h
  have : IsIso (canProj c) := hiso
  refine ⟨summandCone hW θ c (inv (canProj c)),
    isLeftDerivedValueAt_summandCone hW θ c hc _ (IsIso.inv_hom_id _) (IsIso.hom_inv_id _), ?_⟩
  rw [summandCone_π_app, summandProj_idOver hW θ c (inv (canProj c)) (IsIso.inv_hom_id _)]
  exact IsIso.id _

end Core

end DerivedFunctorBiprodComputes

namespace CategoryTheory.Functor

open DerivedFunctorBiprodComputes
open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasBinaryBiproducts C]
  {H : Type u₂} [Category.{v₂} H] [Preadditive H]

/-- **Stacks 05T0**. Let `F : 𝒟 ⥤ 𝒟'` be an additive functor of preadditive categories, `𝒟`
having binary biproducts, and let `W` be a saturated multiplicative system in `𝒟` (Stacks 05Q8).
Let `X` and `Y` be objects of `𝒟`. If the direct sum `X ⊞ Y` computes the right derived functor
`RF` — that is, `RF` is defined at `X ⊞ Y` and the canonical map `F(X ⊞ Y) ⟶ RF(X ⊞ Y)` is an
isomorphism (Stacks 05SX) — then `X` and `Y` compute `RF`. Similarly, if `X ⊞ Y` computes `LF`,
then `X` and `Y` compute `LF`.

Situation 05S8's triangulated hypotheses are not needed; see the module docstring. -/
@[stacks 05T0]
public theorem computesRightDerived_and_computesLeftDerived_of_biprod (F : C ⥤ H) [F.Additive]
    (W : MorphismProperty C) [W.ContainsIdentities] (hW : W.IsSaturated) (X Y : C) :
    (F.ComputesRightDerived W (X ⊞ Y) →
        F.ComputesRightDerived W X ∧ F.ComputesRightDerived W Y) ∧
      (F.ComputesLeftDerived W (X ⊞ Y) →
        F.ComputesLeftDerived W X ∧ F.ComputesLeftDerived W Y) :=
  ⟨fun h => ⟨computesRightDerived_of_iso_biprod F W hW (Iso.refl (X ⊞ Y)) h,
      computesRightDerived_of_iso_biprod F W hW (biprod.braiding X Y) h⟩,
    fun h => ⟨computesLeftDerived_of_iso_biprod F W hW (Iso.refl (X ⊞ Y)) h,
      computesLeftDerived_of_iso_biprod F W hW (biprod.braiding X Y) h⟩⟩

end CategoryTheory.Functor

end

end
