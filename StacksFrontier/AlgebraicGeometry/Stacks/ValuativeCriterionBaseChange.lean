module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionUniqueness
public import StacksFrontier.CategoryTheory.FiberedInSetoids.Transfer
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting
public import StacksFrontier.Exercises.NonExercises.DottedArrowsBaseChange

/-!
# The valuative criteria for algebraic stacks are stable under base change (Stacks 0CLH, 0CLL)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` of a big fppf site and let
`g : 𝒴' ⟶ 𝒴` be arbitrary. A base change of `f` along `g` is the first projection `P.fst` of any
2-fibre product `P` of the cospan `(g, f)`. This file proves that both halves of the valuative
criterion pass from `f` to `P.fst`: the uniqueness half (**Stacks 0CLH**) and the existence half
(**Stacks 0CLL**).

## Main results

* `AlgebraicGeometry.Stack.valuativeCriterionUniqueness_baseChange`: **Stacks 0CLH**.
* `AlgebraicGeometry.Stack.valuativeCriterionExistence_baseChange`: **Stacks 0CLL**.

## Implementation notes

Both proofs run on the same two inputs and differ only in what they do with the dotted arrow they
obtain.

The first input is Stacks 0CLE,
`CategoryTheory.DottedArrowBaseChange.dottedArrows_baseChange_equivalence`: for a 2-cartesian
square, the category of dotted arrows of a square over the base change is *equivalent* to the
category of dotted arrows of the pasted square over `f`. Both criteria are conditions on those
categories — the uniqueness half asks that one be empty or a single isomorphism class, the
existence half asks that one be nonempty after an extension — so each transports along that
equivalence.

The second input is `AlgebraicGeometry.Stack.nonempty_isTwoCartesian_baseChange`: the
base-change square is 2-cartesian in the sense 0CLE asks for, namely it has the full
2-universal property `CategoryTheory.DottedArrowBaseChange.IsTwoCartesian`. A 2-fibre product
is given here as a terminal object of the category of 2-commutative squares (**Stacks 003Q**),
whose morphisms are taken modulo 2-isomorphism, so terminality has to be completed by the
uniqueness of the mediating 2-isomorphism; that is
`CategoryTheory.CatFiberedInGroupoids.hom₂_ext_of_whiskerRight_isTwoFibreProduct`, the
uniqueness half of the 2-universal property, available for an arbitrary 2-fibre product and not
only the canonical one. It is the only place the cartesianness of the square is used beyond
0CLE itself.

Both statements are made for an *arbitrary* 2-fibre product `P` of the cospan rather than for the
canonical model `AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare`, so that a
consumer holding a square it built some other way does not have to transport along a comparison
first.

### Why the argument stays in the 2-category of categories fibred in groupoids

A `ValuativeDiagram` and a `ValuativeSquare` have their generic point `x`, special point `y` and
left edge `j` as 1-morphisms of *categories fibred in groupoids*, not of algebraic stacks; so does
the 2-morphism `γ` filling them. Accordingly the base-change square is pushed down to that
2-category once, with
`AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids`, and the whole
argument happens there. Nothing has to be lifted back up: the conclusion is again a statement
about dotted arrows of categories fibred in groupoids.

The square is then transposed with `CategoryTheory.Bicategory.TwoCommSq.swap`, because the cospan
of `P` is `(g, f)` while Stacks 0CLE is stated with the morphism whose criterion is being
transported in the *second* position.

`CategoryTheory.CatFiberedInGroupoids.homGroupoid` makes the 2-category of categories fibred in
groupoids locally groupoidal, which is the `(2,1)`-hypothesis Stacks 0CLE is stated under, and
also what makes `γ` invertible so that `asIso` applies to it.

## References

* [Stacks Project, Tag 0CLH](https://stacks.math.columbia.edu/tag/0CLH)
* [Stacks Project, Tag 0CLL](https://stacks.math.columbia.edu/tag/0CLL)
* [Stacks Project, Tag 0CLE](https://stacks.math.columbia.edu/tag/0CLE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory

namespace CategoryTheory.CatFiberedInGroupoids

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

/-- **The pasting identity behind base change of the existence criterion.**

Paste a 2-commutative rectangle filled by `cc` and `γq` against a 2-commutative square filled
by `ψ`. Reading the rectangle first and then whiskering with `gg` gives the left-hand side;
reading the square into the rectangle's lower edge first gives the right-hand side. The two
agree.

Everything is formal. In the strict 2-category of categories fibred in groupoids every
associator in a pasting is an identity, so both sides reduce to a composite of whiskerings, and
on components the identity is functoriality of `gg` together with associativity. The statement
is made with every 1-morphism and 2-morphism a *variable*, because at the composites the
consumer supplies — projections of a dominating extension and of a 2-fibre product square —
neither `simp` nor `rfl` can see the functoriality step. -/
theorem pastedGamma
    {U T T₀ U₀ W X Y' Y : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} C}
    (jj : U ⟶ T) (aa : T ⟶ T₀) (kk : U ⟶ U₀) (jq : U₀ ⟶ T₀)
    (yy : T₀ ⟶ Y') (xx : U₀ ⟶ W) (pp : W ⟶ Y') (ss : W ⟶ X)
    (gg : Y' ⟶ Y) (ff : X ⟶ Y)
    (cc : (jj ≫ aa) ⟶ (kk ≫ jq)) (γq : (jq ≫ yy) ⟶ (xx ≫ pp))
    (ψ : (pp ≫ gg) ⟶ (ss ≫ ff)) :
    (α_ jj (aa ≫ yy) gg).inv ≫
        (((α_ jj aa yy).inv ≫ (cc ▷ yy) ≫ (α_ kk jq yy).hom ≫ (kk ◁ γq) ≫
          (α_ kk xx pp).inv) ▷ gg) ≫
        (α_ (kk ≫ xx) pp gg).hom ≫ ((kk ≫ xx) ◁ ψ) ≫ (α_ (kk ≫ xx) ss ff).inv
      = (α_ jj aa (yy ≫ gg)).inv ≫ (cc ▷ (yy ≫ gg)) ≫ (α_ kk jq (yy ≫ gg)).hom ≫
        (kk ◁ ((α_ jq yy gg).inv ≫ (γq ▷ gg) ≫ (α_ xx pp gg).hom ≫ (xx ◁ ψ) ≫
          (α_ xx ss ff).inv)) ≫ (α_ kk (xx ≫ ss) ff).inv := by
  repeat first
    | rw [assocInv_comp] | rw [assocHom_comp] | rw [comp_assocInv] | rw [comp_assocHom]
    | rw [assocInv_comp'] | rw [assocHom_comp'] | rw [comp_assocInv'] | rw [comp_assocHom']
  refine hom₂_ext_app fun A => ?_
  exact (congrArg
      (fun t => t ≫ ψ.hom.toNatTrans.app (xx.hom.toFunctor.obj (kk.hom.toFunctor.obj A)))
      (gg.hom.toFunctor.map_comp (yy.hom.toFunctor.map (cc.hom.toNatTrans.app A))
        (γq.hom.toNatTrans.app (kk.hom.toFunctor.obj A)))).trans (Category.assoc _ _ _)

end CategoryTheory.CatFiberedInGroupoids

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}

/-- **The filler of a 2-commutative square of algebraic stacks**, read in the 2-category of
categories fibred in groupoids: the `iso` field of
`AlgebraicGeometry.Stack.AlgebraicStacks.toCatFiberedInGroupoids`, transposed so that the
1-morphism whose criterion is being transported sits in the second position, which is where
Stacks 0CLE expects it. -/
def baseChangeFiller (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) (P : Bicategory.TwoCommSq g f) :
    (P.fst.hom ≫ g.hom) ≅ (P.snd.hom ≫ f.hom) where
  hom := P.iso.hom.hom
  inv := P.iso.inv.hom
  hom_inv_id := congrArg Bicategory.InducedBicategory.Hom₂.hom P.iso.hom_inv_id
  inv_hom_id := congrArg Bicategory.InducedBicategory.Hom₂.hom P.iso.inv_hom_id

/-- **The projections of a 2-fibre product of algebraic stacks jointly detect 2-isomorphisms**,
read in the 2-category of categories fibred in groupoids and transposed.

This is the uniqueness half of the 2-universal property, in the shape in which the
terminal-object form of a 2-fibre product (**Stacks 003Q**) has to be completed to the full
2-universal property: an equality of 2-isomorphisms rather than of 2-morphisms, and phrased
against the comparison 2-cells of two pre-morphisms of 2-commutative squares. The content is
`CategoryTheory.CatFiberedInGroupoids.hom₂_ext_of_whiskerRight_isTwoFibreProduct` after
cancelling those comparison 2-cells, which are invertible. -/
theorem preHom_iso_ext (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (T : Bicategory.TwoCommSq f.hom g.hom)
    (F G : Bicategory.TwoCommSq.PreHom T
      (AlgebraicStacks.toCatFiberedInGroupoids B S hS P).swap)
    (ρ σ : F.hom ≅ G.hom)
    (hρ : (F.isoFst.hom ≫ (ρ.hom ▷ P.snd.hom) = G.isoFst.hom) ∧
      (F.isoSnd.hom ≫ (ρ.hom ▷ P.fst.hom) = G.isoSnd.hom))
    (hσ : (F.isoFst.hom ≫ (σ.hom ▷ P.snd.hom) = G.isoFst.hom) ∧
      (F.isoSnd.hom ≫ (σ.hom ▷ P.fst.hom) = G.isoSnd.hom)) : ρ = σ := by
  refine Iso.ext
    (CatFiberedInGroupoids.hom₂_ext_of_whiskerRight_isTwoFibreProduct.{u, u, u + 1, u + 1}
      (Bicategory.isTwoFibreProduct_swap
        (AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids B S hS P hP)) ?_ ?_)
  · exact (cancel_epi F.isoFst.hom).1 (hρ.1.trans hσ.1.symm)
  · exact (cancel_epi F.isoSnd.hom).1 (hρ.2.trans hσ.2.symm)

/-- **A 2-fibre product of algebraic stacks is 2-cartesian**, read in the 2-category of
categories fibred in groupoids and transposed: it has the full 2-universal property
`CategoryTheory.DottedArrowBaseChange.IsTwoCartesian`, which is the hypothesis of Stacks 0CLE.

A 2-fibre product is given here as a terminal object of the category of 2-commutative squares
(**Stacks 003Q**), whose morphisms are taken modulo 2-isomorphism; so terminality has to be
completed by the uniqueness of the mediating 2-isomorphism, which is `preHom_iso_ext`. This is
the only place where that completion is needed: no statement downstream carries it. -/
theorem nonempty_isTwoCartesian_baseChange (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P) :
    Nonempty (CategoryTheory.DottedArrowBaseChange.IsTwoCartesian
      P.snd.hom P.fst.hom f.hom g.hom (baseChangeFiller B S hS f g P)) :=
  CategoryTheory.DottedArrowBaseChange.nonempty_isTwoCartesian_of_isTwoFibreProduct _
    (Bicategory.isTwoFibreProduct_swap
      (AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids B S hS P hP))
    (preHom_iso_ext B S hS f g P hP)

/-! ### Stacks 0CLH -/

/-- **Stacks 0CLH.** A base change of a 1-morphism of algebraic stacks satisfying the uniqueness
part of the valuative criterion satisfies it as well.

The base change of `f : 𝒳 ⟶ 𝒴` along `g : 𝒴' ⟶ 𝒴` is the first projection of a 2-fibre product
`P` of the cospan `(g, f)`. -/
@[stacks 0CLH]
theorem valuativeCriterionUniqueness_baseChange
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hf : ValuativeCriterion.Uniqueness B S hS f) :
    ValuativeCriterion.Uniqueness B S hS P.fst := by
  classical
  -- the filler of the base-change square, read in the 2-category of categories fibred in
  -- groupoids and transposed so that `f` sits in the second position, as Stacks 0CLE expects
  let φ := baseChangeFiller B S hS f g P
  -- the base-change square is 2-cartesian, which is all Stacks 0CLE asks of it
  obtain ⟨hcart⟩ := nonempty_isTwoCartesian_baseChange B S hS f g P hP
  intro D
  -- `γ` is invertible because the 2-category of categories fibred in groupoids is locally
  -- groupoidal, which is also the `(2,1)`-hypothesis Stacks 0CLE is stated under
  have hγ : IsIso D.γ := (CatFiberedInGroupoids.homGroupoid _ _).all_isIso D.γ
  -- the valuative diagram over `f` obtained by pasting `D` with the base-change square
  obtain ⟨hSetoid, hIso⟩ := hf
    { D with
      x := D.x ≫ P.snd.hom
      y := D.y ≫ g.hom
      γ := ((α_ D.j D.y g.hom).symm ≪≫
        Bicategory.whiskerRightIso (asIso D.γ) g.hom ≪≫
        (α_ D.x P.fst.hom g.hom) ≪≫
        Bicategory.whiskerLeftIso D.x φ ≪≫
        (α_ D.x P.snd.hom f.hom).symm).hom }
  obtain ⟨E⟩ := CategoryTheory.DottedArrowBaseChange.dottedArrows_baseChange_equivalence
    D.j D.x P.snd.hom P.fst.hom f.hom D.y g.hom φ (asIso D.γ) hcart
  have hE : E.functor.IsEquivalence := E.isEquivalence_functor
  -- the goal names the dotted-arrow category through `D.γ` and the equivalence through
  -- `(asIso D.γ).hom`; the two are the same category
  refine ⟨?_, ?_⟩
  · show IsSetoidCategory
      (CategoryTheory.DottedArrow D.x D.j P.fst.hom D.y (asIso D.γ).hom)
    exact IsSetoidCategory.of_faithful E.functor hE.faithful inferInstance hSetoid
  · show ∀ a b : CategoryTheory.DottedArrow D.x D.j P.fst.hom D.y (asIso D.γ).hom,
      Nonempty (a ≅ b)
    exact nonempty_iso_of_isEquivalence E.functor hE hIso

/-! ### Stacks 0CLL -/

/-- **Stacks 0CLL.** A base change of a 1-morphism of algebraic stacks satisfying the existence
part of the valuative criterion satisfies it as well.

The base change of `f : 𝒳 ⟶ 𝒴` along `g : 𝒴' ⟶ 𝒴` is the first projection of a 2-fibre product
`P` of the cospan `(g, f)`. -/
@[stacks 0CLL]
theorem valuativeCriterionExistence_baseChange
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hf : ValuativeCriterion.Existence B S hS f) :
    ValuativeCriterion.Existence B S hS P.fst := by
  classical
  let φ := baseChangeFiller B S hS f g P
  obtain ⟨hcart⟩ := nonempty_isTwoCartesian_baseChange B S hS f g P hP
  intro q
  -- the valuative square over `f` obtained by pasting `q` with the base-change square
  obtain ⟨e, ⟨d⟩⟩ := hf
    { q with
      x := q.x ≫ P.snd.hom
      y := q.y ≫ g.hom
      γ := (α_ q.j q.y g.hom).inv ≫ (q.γ ▷ g.hom) ≫
        (α_ q.x P.fst.hom g.hom).hom ≫ (q.x ◁ φ.hom) ≫
        (α_ q.x P.snd.hom f.hom).inv }
  -- the same dominating extension, read as one of `q`: `DominatingExtension` mentions its
  -- square only through `R`, `K`, `base`, the two site-membership proofs and `j`, all of which
  -- the pasted square shares with `q`
  let E : q.DominatingExtension :=
    { R' := e.R', commRing := e.commRing, domain := e.domain,
      valuationRing := e.valuationRing, K' := e.K', field := e.field, algebra := e.algebra,
      isFractionRing := e.isFractionRing, ringMap := e.ringMap, fieldMap := e.fieldMap,
      isLocalHom := e.isLocalHom, fraction_comm := e.fraction_comm,
      ring_mem := e.ring_mem, field_mem := e.field_mem,
      specialOver := e.specialOver, specialOver_left := e.specialOver_left,
      genericOver := e.genericOver, genericOver_left := e.genericOver_left,
      genericMap := e.genericMap, genericMap_left := e.genericMap_left,
      j := e.j, j_canonical := e.j_canonical, a := e.a, a_canonical := e.a_canonical,
      k := e.k, k_canonical := e.k_canonical, commute := e.commute }
  have hγ : IsIso E.inducedGamma :=
    (CatFiberedInGroupoids.homGroupoid _ _).all_isIso E.inducedGamma
  obtain ⟨E'⟩ := CategoryTheory.DottedArrowBaseChange.dottedArrows_baseChange_equivalence
    E.j (E.k ≫ q.x) P.snd.hom P.fst.hom f.hom (E.a ≫ q.y) g.hom φ
    (asIso E.inducedGamma) hcart
  -- the 2-cell of the outer rectangle for `E` is the one of the pasted square for `e`
  have hγeq : ((α_ E.j (E.a ≫ q.y) g.hom).symm ≪≫
      Bicategory.whiskerRightIso (asIso E.inducedGamma) g.hom ≪≫
      (α_ (E.k ≫ q.x) P.fst.hom g.hom) ≪≫
      Bicategory.whiskerLeftIso (E.k ≫ q.x) φ ≪≫
      (α_ (E.k ≫ q.x) P.snd.hom f.hom).symm).hom = e.inducedGamma := by
    dsimp only [ValuativeSquare.DominatingExtension.inducedGamma]
    simp only [Iso.trans_hom, Iso.symm_hom, Bicategory.whiskerRightIso_hom,
      Bicategory.whiskerLeftIso_hom]
    exact CatFiberedInGroupoids.pastedGamma e.j e.a e.k q.j q.y q.x P.fst.hom P.snd.hom
      g.hom f.hom e.commute q.γ φ.hom
  exact ⟨E, ⟨E'.inverse.obj
    { a := d.a, α := d.α, β := d.β, compat := hγeq.trans d.compat }⟩⟩

end AlgebraicGeometry.Stack

end
