module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposSquare
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.InverseImageComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposInverseImageExact
public import StacksFrontier.Deformation.ToposThickening.FlatLiftBaseRingComparison
public import StacksFrontier.Deformation.ToposThickening.FlatLiftIdealTensorBridge
public import StacksFrontier.Deformation.ToposThickening.FlatLiftPullbackIdealComparison
public import StacksFrontier.Deformation.ToposThickening.FlatThickeningBoundary
public import StacksFrontier.Deformation.ToposThickening.StrictFlatIdealMap
public import StacksFrontier.Deformation.ToposThickening.ThickeningComplexHorizontalHom

/-!
# The coefficient sequence of Stacks 08VY is short exact

In Situation **Stacks 08VX** — a short exact sequence of first order thickenings

```
  (Sh(C'₁), O'₁)     --h-->  (Sh(C'₂), O'₂)     ------>  (Sh(C'₃), O'₃)
      |                          |                           |
      f'₁                        f'₂                         f'₃
      v                          v                           v
  (Sh(B'₁), O_{ℬ'₁}) ---h_ℬ-->  (Sh(B'₂), O_{ℬ'₂}) ----->  (Sh(B'₃), O_{ℬ'₃})
```

over a short exact sequence of first order thickenings of the base, with each column strict and
each `f'ₖ` flat, and an `O`-module `ℱ` flat over `O_ℬ` — the coefficient sequence

`0 ⟶ I₃ ⊗_O ℱ ⟶ I₂ ⊗_O ℱ ⟶ I₁ ⊗_O ℱ ⟶ 0`

of the boundary map of Stacks 08VY is short exact. This file proves it: the predicate
`Deformation.ToposThickening.FirstOrderThickeningComplex.IsIdealTensorShortExact` of
`StacksFrontier/Deformation/ToposThickening/FlatThickeningBoundary.lean` holds with no hypothesis
beyond its own.

## Main results

* `Deformation.ToposThickening.FirstOrderThickeningComplex.isIdealTensorShortExact`: the
  predicate holds.
* `Deformation.ToposThickening.isIso_canonicalFirstFactor_of_isFlat`: **the first factor
  `f^*𝒥 ⊗_O ℱ ⟶ I ⊗_O ℱ` of the canonical map of Stacks 08MQ is an isomorphism** for a strict
  square with flat `f'`, with no flat lift of `ℱ` assumed. The whole of 08MQ is not needed for
  it: the map of defining ideals `f^*𝒥 ⟶ I` is itself invertible there, by
  `Deformation.ToposThickening.MorphismOfThickenings.isIso_idealMap`.
* `Deformation.ToposThickening.inverseImageBaseIdealToIdeal_naturality` and
  `Deformation.ToposThickening.canonicalFirstFactor_naturality`: the map of defining ideals
  `f⁻¹𝒥 ⟶ I` of Situation 08M7, and the first factor of Stacks 08MQ built from it, are natural
  along a morphism of first order thickenings — granted the horizontal square of structure maps.

## How the proof goes

The source's argument is that the sequence is the inverse image of `0 ⟶ 𝒥₃ ⟶ 𝒥₂ ⟶ 𝒥₁ ⟶ 0`
tensored over `f⁻¹O_ℬ` with the `f⁻¹O_ℬ`-flat module `ℱ`. Formally:

* `Stacks.Sheaves.RingedToposModules.shortExact_map_inverseImageModules` carries the short exact
  sequence of defining ideals of the lower row to a short exact sequence of `f⁻¹O_ℬ`-modules —
  the inverse image of sheaves of modules along a morphism of topoi is exact (Stacks 04JC);
* `Stacks.SheafOfModules.sheafTensorRight_shortExact_of_flat_factor` tensors that with `ℱ` read
  over `f⁻¹O_ℬ`, which is flat by
  `Deformation.ToposThickening.isFlat_reducedBaseModule_of_isFlatOverBase`;
* the result is carried onto `Iₖ ⊗_O ℱ` by the first factors
  `f⁻¹𝒥ₖ ⊗_{f⁻¹O_ℬ} ℱ ⟶ (Iₖ ⊗_O ℱ)|_{f⁻¹O_ℬ}` of Stacks 08MQ, which are isomorphisms and
  commute with the two maps of the sequence;
* and restriction of scalars along `f⁻¹O_ℬ ⟶ i_*O` reflects short exactness, by
  `Stacks.SheafOfModules.ChangeOfRings.shortExact_of_shortExact_map_restrictScalars`.

**Where the two horizontal squares enter.** The three columns' pullbacks `fₖ^*𝒥ₖ` are formed
along three different morphisms of ringed topoi, so without a comparison of those the three
first factors do not even live in one category. Each horizontal square of Situation 08VX is an
equality of morphisms of ringed topoi whose horizontal edges are the identity on topoi
(`AlgebraicGeometry.RingedToposHom.coefficientMorphism`), so it forces the two vertical arrows
it relates to have **one and the same underlying morphism of topoi**
(`Deformation.ToposThickening.FirstOrderThickeningComplex.toToposHom_eq_of_lowerSquare`). Each
vertical arrow is then rewritten as a morphism built from that one morphism of topoi
(`Deformation.ToposThickening.exists_eq_mk_of_toToposHom_eq`), after which the three columns'
base rings `f⁻¹O_ℬ`, base modules `ℱ|_{f⁻¹O_ℬ}` and structure maps `f⁻¹O_ℬ ⟶ i_*O` are the same
terms, not merely isomorphic ones.

Each square says more than that, and the rest of what it says is the commuting square of
structure maps
`(f'ₖ₊₁)^♯ ∘ h^♯_ℬ = h^♯ ∘ (f'ₖ)^♯`
(`Deformation.ToposThickening.FirstOrderThickeningComplex.fSharpInverseImage_lowerSquare`),
which is exactly what makes the map of defining ideals natural: a section `j` of `f⁻¹𝒥ₖ₊₁` has
`λ(j) = (f'ₖ₊₁)^♯(j)` inside `Iₖ₊₁`, and the two routes around the square agree on it.

## Implementation notes

The naturality statements are proved for a `Deformation.ToposThickening`
`.MorphismOfFirstOrderThickenings` upstairs and downstairs, so that one lemma serves both
horizontal arrows of the diagram: the second arrow is the first arrow of the complex read at its
second thickening (`Deformation.ToposThickening.FirstOrderThickeningComplex.upper`).

`Deformation.ToposThickening.FirstOrderThickeningComplex.canonicalFirstFactor_square_lower` and
`.canonicalFirstFactor_square_upper` restate the two naturality squares in the vocabulary of the
first column. That restatement is a definitional identity, but an expensive one — it unfolds the
structure map `f⁻¹O_ℬ ⟶ i_*O` of each column down to `Deformation.ToposThickening`
`.pushforwardStructureComparison` — so it is made once per square, in a declaration of its own,
rather than inside the main proof.

## References

* [Stacks Project, Tag 08VY](https://stacks.math.columbia.edu/tag/08VY)
* [Stacks Project, Tag 08VX](https://stacks.math.columbia.edu/tag/08VX)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08M9](https://stacks.math.columbia.edu/tag/08M9)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor inverseImageCommRingFunctor)

universe v u v₂ u₂ w vB uB wB vB' uB' wB' v' u' w'

namespace Deformation.ToposThickening

/-! ### Composing a morphism of topoi with the identity -/

/-- Composing a morphism of topoi with the identity on the source changes nothing. -/
theorem morphismOfTopoi_comp_id {E : Type u} [Category.{v} E] {F : Type u'} [Category.{v'} F]
    (m : MorphismOfTopoi E F) : m.comp (MorphismOfTopoi.id E) = m := by
  obtain ⟨p, q, a, l⟩ := m
  dsimp [MorphismOfTopoi.comp, MorphismOfTopoi.id]
  congr 1
  refine Adjunction.ext ?_
  ext Z
  simp [Adjunction.comp_unit_app]

/-- Composing a morphism of topoi with the identity on the target changes nothing. -/
theorem morphismOfTopoi_id_comp {E : Type u} [Category.{v} E] {F : Type u'} [Category.{v'} F]
    (m : MorphismOfTopoi E F) : (MorphismOfTopoi.id F).comp m = m := by
  obtain ⟨p, q, a, l⟩ := m
  dsimp [MorphismOfTopoi.comp, MorphismOfTopoi.id]
  congr 1
  refine Adjunction.ext ?_
  ext Z
  simp [Adjunction.comp_unit_app]

/-! ### Transporting the structure map along an equality of morphisms of ringed topoi -/

section Congr

variable {A : RingedTopos.{v, u, w}} {Z : RingedTopos.{v', u', w'}}
  [A.J.HasSheafCompose (forget RingCat.{w})] [Z.J.HasSheafCompose (forget RingCat.{w'})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- Two equal morphisms of ringed topoi have the same inverse-image structure map on underlying
sheaves of sets, up to the transport of the source along the equality of the two inverse
images. -/
theorem forgetRing_map_fSharpInverseImage_congr {m₁ m₂ : RingedToposHom A Z} (h : m₁ = m₂)
    {x : A.forgetRing.obj ((inverseImageCommRingFunctor m₂.toToposHom).obj Z.O) ⟶
      A.forgetRing.obj A.O}
    (hx : HEq (A.forgetRing.map m₁.fSharpInverseImage) x) :
    x = A.forgetRing.map m₂.fSharpInverseImage := by
  subst h
  exact (eq_of_heq hx).symm

/-- **A morphism of ringed topoi whose underlying morphism of topoi is a prescribed one is
literally built from that one.** This is what lets an equality of underlying morphisms of topoi
be used by substitution rather than by transport: after rewriting the vertical arrows of the
diagram into this shape, the three columns' inverse images are the same functor on the nose. -/
theorem exists_eq_mk_of_toToposHom_eq (m : RingedToposHom A Z)
    {P : MorphismOfTopoi A.Topos Z.Topos} (h : m.toToposHom = P) :
    ∃ s : Z.O ⟶ (pushforwardCommRingFunctor P).obj A.O, m = ⟨P, s⟩ := by
  subst h
  exact ⟨m.fSharp, rfl⟩

/-- A commuting square of morphisms of ringed topoi with the same underlying morphism of topoi
and coefficient-change horizontal arrows `a` and `b` gives a commuting square of structure maps
after inverse image. -/
private theorem fSharpInverseImage_square_of_coefficientMorphism_comp_eq
    {O O' : Sheaf A.J CommRingCat.{w}} {Q Q' : Sheaf Z.J CommRingCat.{w'}} (a : O ⟶ O')
    (b : Q ⟶ Q') (P : MorphismOfTopoi A.Topos Z.Topos)
    (s₁ : Q' ⟶ (pushforwardCommRingFunctor P).obj O')
    (s₂ : Q ⟶ (pushforwardCommRingFunctor P).obj O)
    (h : (RingedToposHom.mk P s₂ : RingedToposHom (reshape A O) (reshape Z Q)).comp
        (RingedToposHom.coefficientMorphism A.J a : RingedToposHom (reshape A O') (reshape A O)) =
      (RingedToposHom.coefficientMorphism Z.J b :
        RingedToposHom (reshape Z Q') (reshape Z Q)).comp
        (RingedToposHom.mk P s₁ : RingedToposHom (reshape A O') (reshape Z Q'))) :
    (RingedToposHom.mk P s₂ : RingedToposHom (reshape A O) (reshape Z Q)).fSharpInverseImage ≫
        a = (inverseImageCommRingFunctor P).map b ≫
      (RingedToposHom.mk P s₁ : RingedToposHom (reshape A O') (reshape Z Q')).fSharpInverseImage :=
  by
  have key := forgetRing_map_fSharpInverseImage_congr h HEq.rfl
  rw [AlgebraicGeometry.RingedToposHom.comp_fSharpInverseImage_forget,
    AlgebraicGeometry.RingedToposHom.comp_fSharpInverseImage_forget,
    AlgebraicGeometry.RingedToposHom.coefficientMorphism_fSharpInverseImage,
    AlgebraicGeometry.RingedToposHom.coefficientMorphism_fSharpInverseImage] at key
  simp only at key
  have e2 : (sheafCompose A.J (forget CommRingCat.{w})).map
        ((inverseImageCommRingFunctor P).map b) =
      P.inverseImage.map ((sheafCompose Z.J (forget CommRingCat.{w'})).map b) :=
    Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap
      (J := A.J) (K := Z.J) (Φ := P.inverseImage) b
  refine (sheafCompose A.J (forget CommRingCat.{w})).map_injective ?_
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, e2]
  exact key

end Congr

/-! ### The ambient situation -/

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v₂, u₂, w}}
  {B : RingedTopos.{vB, uB, wB}} {B' : RingedTopos.{vB', uB', wB'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{wB})] [B'.J.HasSheafCompose (forget RingCat.{wB'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  {i : RingedToposHom X Y} {t : RingedToposHom B B'}

namespace FirstOrderThickeningComplex

variable (S : FirstOrderThickeningComplex i) (T : FirstOrderThickeningComplex t)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] in
/-- **The first horizontal square identifies the underlying morphisms of topoi of its two
vertical arrows.** Both horizontal arrows are the identity on topoi, so the square reads
`g₂ ∘ 𝟙 = 𝟙 ∘ g₁`. -/
theorem toToposHom_eq_of_lowerSquare {g₁ : RingedToposHom Y B'}
    {g₂ : RingedToposHom (reshape Y S.lower.O₂) (reshape B' T.lower.O₂)}
    (h : g₂.comp S.lowerHorizontalHom = T.lowerHorizontalHom.comp g₁) :
    g₂.toToposHom = g₁.toToposHom := by
  have h1 := congrArg (fun m : RingedToposHom Y (reshape B' T.lower.O₂) ↦ m.toToposHom) h
  simpa only [RingedToposHom.comp_toToposHom,
    AlgebraicGeometry.RingedToposHom.coefficientMorphism_toToposHom,
    morphismOfTopoi_comp_id, morphismOfTopoi_id_comp] using h1

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] in
/-- **The second horizontal square identifies the underlying morphisms of topoi of its two
vertical arrows.** -/
theorem toToposHom_eq_of_upperSquare
    {g₂ : RingedToposHom (reshape Y S.lower.O₂) (reshape B' T.lower.O₂)}
    {g₃ : RingedToposHom (reshape Y S.O₃) (reshape B' T.O₃)}
    (h : g₃.comp S.upperHorizontalHom = T.upperHorizontalHom.comp g₂) :
    g₃.toToposHom = g₂.toToposHom := by
  have h1 := congrArg (fun m : RingedToposHom (reshape Y S.lower.O₂) (reshape B' T.O₃) ↦
    m.toToposHom) h
  simpa only [RingedToposHom.comp_toToposHom,
    AlgebraicGeometry.RingedToposHom.coefficientMorphism_toToposHom,
    morphismOfTopoi_comp_id, morphismOfTopoi_id_comp] using h1

section Squares

variable (P : MorphismOfTopoi Y.Topos B'.Topos)

/-- The vertical arrow of the first column, built from a prescribed underlying morphism of
topoi. -/
abbrev columnOne (s₁ : B'.O ⟶ (pushforwardCommRingFunctor P).obj Y.O) :
    RingedToposHom Y B' := ⟨P, s₁⟩

/-- The vertical arrow of the second column, built from a prescribed underlying morphism of
topoi. -/
abbrev columnTwo (s₂ : T.lower.O₂ ⟶ (pushforwardCommRingFunctor P).obj S.lower.O₂) :
    RingedToposHom (reshape Y S.lower.O₂) (reshape B' T.lower.O₂) := ⟨P, s₂⟩

/-- The vertical arrow of the third column, built from a prescribed underlying morphism of
topoi. -/
abbrev columnThree (s₃ : T.O₃ ⟶ (pushforwardCommRingFunctor P).obj S.O₃) :
    RingedToposHom (reshape Y S.O₃) (reshape B' T.O₃) := ⟨P, s₃⟩

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] in
/-- **The first horizontal square, read on structure maps.** The square of ringed topoi says
exactly that the inverse image of `h^♯_ℬ` followed by the structure map of the first column is
the structure map of the second column followed by `h^♯`.

The two vertical arrows are presented as morphisms of ringed topoi built from one and the same
underlying morphism of topoi, which is what the square forces them to be
(`Deformation.ToposThickening.FirstOrderThickeningComplex.toToposHom_eq_of_lowerSquare`); their
inverse images are then the same functor on the nose. -/
theorem fSharpInverseImage_lowerSquare
    (s₁ : B'.O ⟶ (pushforwardCommRingFunctor P).obj Y.O)
    (s₂ : T.lower.O₂ ⟶ (pushforwardCommRingFunctor P).obj S.lower.O₂)
    (h : (S.columnTwo T P s₂).comp S.lowerHorizontalHom =
      T.lowerHorizontalHom.comp (columnOne P s₁)) :
    (S.columnTwo T P s₂).fSharpInverseImage ≫ S.lower.hSharp =
      (inverseImageCommRingFunctor P).map T.lower.hSharp ≫
        (columnOne P s₁).fSharpInverseImage := by
  exact fSharpInverseImage_square_of_coefficientMorphism_comp_eq _ T.lower.hSharp P s₁ s₂ h

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] in
/-- **The second horizontal square, read on structure maps**, the counterpart of
`Deformation.ToposThickening.FirstOrderThickeningComplex.fSharpInverseImage_lowerSquare` for the
arrow `O'₃ ⟶ O'₂` of the upper row and `O_{ℬ'₃} ⟶ O_{ℬ'₂}` of the lower one. -/
theorem fSharpInverseImage_upperSquare
    (s₂ : T.lower.O₂ ⟶ (pushforwardCommRingFunctor P).obj S.lower.O₂)
    (s₃ : T.O₃ ⟶ (pushforwardCommRingFunctor P).obj S.O₃)
    (h : (S.columnThree T P s₃).comp S.upperHorizontalHom =
      T.upperHorizontalHom.comp (S.columnTwo T P s₂)) :
    (S.columnThree T P s₃).fSharpInverseImage ≫ S.h₃₂ =
      (inverseImageCommRingFunctor P).map T.h₃₂ ≫
        (S.columnTwo T P s₂).fSharpInverseImage := by
  exact fSharpInverseImage_square_of_coefficientMorphism_comp_eq _ T.h₃₂ P s₂ s₃ h

end Squares

end FirstOrderThickeningComplex

section Naturality

open Stacks.Sheaves.RingedToposModules (inverseImageModules)
open Stacks.SheafOfModules.FlatSquareZero (ringMap)

variable (D : MorphismOfFirstOrderThickenings i) (E : MorphismOfFirstOrderThickenings t)
  (f : RingedToposHom X B) (P : MorphismOfTopoi Y.Topos B'.Topos)
  (s₁ : B'.O ⟶ (pushforwardCommRingFunctor P).obj Y.O)
  (s₂ : E.O₂ ⟶ (pushforwardCommRingFunctor P).obj D.O₂)
  (comm₁ : (RingedToposHom.mk P s₁ : RingedToposHom Y B').comp i = t.comp f)
  (comm₂ : (RingedToposHom.mk P s₂ :
      RingedToposHom (reshape Y D.O₂) (reshape B' E.O₂)).comp (reshapeHom i D.O₂ D.fSharp₂) =
    (reshapeHom t E.O₂ E.fSharp₂).comp f)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})] in
/-- **The map of defining ideals `f⁻¹𝒥 ⟶ I` of Situation 08M7 is natural along a morphism of
first order thickenings**, granted the horizontal square of structure maps. -/
theorem inverseImageBaseIdealToIdeal_naturality
    (hsq : (RingedToposHom.mk P s₂ :
            RingedToposHom (reshape Y D.O₂) (reshape B' E.O₂)).fSharpInverseImage ≫ D.hSharp =
      (inverseImageCommRingFunctor P).map E.hSharp ≫
        (RingedToposHom.mk P s₁ : RingedToposHom Y B').fSharpInverseImage) :
    (inverseImageModules P (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing t))).map E.idealMap ≫
        inverseImageBaseIdealToIdeal i t f (RingedToposHom.mk P s₁) D.first E.first comm₁ =
      inverseImageBaseIdealToIdeal (reshapeHom i D.O₂ D.fSharp₂)
          (reshapeHom t E.O₂ E.fSharp₂) f (RingedToposHom.mk P s₂) D.second E.second comm₂ ≫
        (SheafOfModules.restrictScalars (ringMap
          (inverseImageReducedStructureMap i t f (RingedToposHom.mk P s₁) comm₁))).map
            D.idealMap := by
  have hsheaf : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing t))).map
        E.idealMap ≫ E.first.inclSheafSets =
      E.second.inclSheafSets ≫ (sheafCompose B'.J (forget CommRingCat.{wB'})).map E.hSharp :=
    Sheaf.hom_ext_sections fun V b ↦ E.inclOne_idealMap V b
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
    ModuleCat.hom_ext (LinearMap.ext fun z ↦ ?_))
  have star : (inverseImageBaseIdealIncl t (RingedToposHom.mk P s₁) E.first).val.app U
        (((inverseImageModules P (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing t))).map
          E.idealMap).val.app U z) =
      ((inverseImageCommRingFunctor P).map E.hSharp).hom.app U
        ((inverseImageBaseIdealIncl (reshapeHom t E.O₂ E.fSharp₂)
          (RingedToposHom.mk P s₂ :
            RingedToposHom (reshape Y D.O₂) (reshape B' E.O₂)) E.second).val.app U z) := by
    have h1 := inverseImageBaseIdealIncl_val_app (t := t) (f' := RingedToposHom.mk P s₁)
      E.first U (((inverseImageModules P (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing t))).map
        E.idealMap).val.app U z)
    have h2 := inverseImageBaseIdealIncl_val_app (t := reshapeHom t E.O₂ E.fSharp₂)
      (f' := (RingedToposHom.mk P s₂ :
        RingedToposHom (reshape Y D.O₂) (reshape B' E.O₂))) E.second U z
    have h3 : ((inverseImageModules P (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing t))).map
          E.idealMap).val.app U z =
        (Sheaf.sectionsFunctor Y.J U).map (P.inverseImage.map
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing t))).map
            E.idealMap)) z := by
      rw [← Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_inverseImageModules_map]
      rfl
    have h5 := congrArg
      (fun m ↦ (Sheaf.sectionsFunctor Y.J U).map (P.inverseImage.map m) z) hsheaf
    have hA : (Sheaf.sectionsFunctor Y.J U).map (P.inverseImage.map
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing t))).map
              E.idealMap ≫
            E.first.inclSheafSets)) z =
        (Sheaf.sectionsFunctor Y.J U).map (P.inverseImage.map E.first.inclSheafSets)
          ((Sheaf.sectionsFunctor Y.J U).map (P.inverseImage.map
            ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing t))).map
              E.idealMap)) z) :=
      (congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J U).map m z)
          (P.inverseImage.map_comp _ _)).trans
        ((Sheaf.sectionsFunctor Y.J U).map_comp_apply _ _ z)
    have hB : (Sheaf.sectionsFunctor Y.J U).map (P.inverseImage.map
          (E.second.inclSheafSets ≫
            (sheafCompose B'.J (forget CommRingCat.{wB'})).map E.hSharp)) z =
        (Sheaf.sectionsFunctor Y.J U).map (P.inverseImage.map
            ((sheafCompose B'.J (forget CommRingCat.{wB'})).map E.hSharp))
          ((Sheaf.sectionsFunctor Y.J U).map
            (P.inverseImage.map E.second.inclSheafSets) z) :=
      (congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J U).map m z)
          (P.inverseImage.map_comp _ _)).trans
        ((Sheaf.sectionsFunctor Y.J U).map_comp_apply _ _ z)
    have h6 : (sheafCompose Y.J (forget CommRingCat.{w})).map
          ((inverseImageCommRingFunctor P).map E.hSharp) =
        P.inverseImage.map ((sheafCompose B'.J (forget CommRingCat.{wB'})).map E.hSharp) :=
      Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap
        (J := Y.J) (K := B'.J) (Φ := P.inverseImage) E.hSharp
    have h7 : ∀ y, (Sheaf.sectionsFunctor Y.J U).map
          (P.inverseImage.map ((sheafCompose B'.J (forget CommRingCat.{wB'})).map E.hSharp)) y =
        ((inverseImageCommRingFunctor P).map E.hSharp).hom.app U y := by
      intro y
      rw [← h6]
      rfl
    rw [h1, h2, h3]
    exact hA.symm.trans (h5.trans (hB.trans (h7 _)))
  have hL := incl_inverseImageBaseIdealToIdeal_apply (i := i) (t := t) (f := f)
    (f' := RingedToposHom.mk P s₁) (hi := D.first) (ht := E.first) (comm := comm₁) U
    (((inverseImageModules P (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing t))).map
      E.idealMap).val.app U z)
  have hR := incl_inverseImageBaseIdealToIdeal_apply (i := reshapeHom i D.O₂ D.fSharp₂)
    (t := reshapeHom t E.O₂ E.fSharp₂) (f := f)
    (f' := (RingedToposHom.mk P s₂ :
      RingedToposHom (reshape Y D.O₂) (reshape B' E.O₂)))
    (hi := D.second) (ht := E.second) (comm := comm₂) U z
  have hidm := D.inclOne_idealMap U
    ((inverseImageBaseIdealToIdeal (reshapeHom i D.O₂ D.fSharp₂) (reshapeHom t E.O₂ E.fSharp₂) f
      (RingedToposHom.mk P s₂) D.second E.second comm₂).val.app U z)
  have hsqU : ∀ y, D.hSharp.hom.app U
        ((RingedToposHom.mk P s₂ :
          RingedToposHom (reshape Y D.O₂) (reshape B' E.O₂)).fSharpInverseImage.hom.app U y) =
      (RingedToposHom.mk P s₁ : RingedToposHom Y B').fSharpInverseImage.hom.app U
        (((inverseImageCommRingFunctor P).map E.hSharp).hom.app U y) :=
    fun y ↦ congrArg (fun m ↦ m.hom.app U y) hsq
  refine D.inclOne_injective U ?_
  refine hL.trans ?_
  refine (congrArg (fun y ↦ (RingedToposHom.mk P s₁ :
    RingedToposHom Y B').fSharpInverseImage.hom.app U y) star).trans ?_
  refine Eq.trans ?_ hidm.symm
  refine Eq.trans ?_ (congrArg (fun y ↦ D.ringMapH.hom.app U y) hR.symm)
  exact (hsqU _).symm

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})] in
/-- **The first factor `f^*𝒥 ⊗_O ℱ ⟶ I ⊗_O ℱ` of the canonical map of Stacks 08MQ is natural
along a morphism of first order thickenings**, granted the horizontal square of structure maps:
it is the map of defining ideals `f⁻¹𝒥 ⟶ I`, which is natural, tensored with `ℱ`, followed by
the reduction comparison, which is natural in the ideal. -/
theorem canonicalFirstFactor_naturality
    (hsq : (RingedToposHom.mk P s₂ :
            RingedToposHom (reshape Y D.O₂) (reshape B' E.O₂)).fSharpInverseImage ≫ D.hSharp =
      (inverseImageCommRingFunctor P).map E.hSharp ≫
        (RingedToposHom.mk P s₁ : RingedToposHom Y B').fSharpInverseImage)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageReducedBaseRing t (RingedToposHom.mk P
        s₁))).flip.obj (reducedBaseModule i t f (RingedToposHom.mk P s₁) comm₁ F)).map
        ((inverseImageModules P (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing t))).map
            E.idealMap) ≫
        canonicalFirstFactor i t f (RingedToposHom.mk P s₁) D.first E.first comm₁ F =
      canonicalFirstFactor (reshapeHom i D.O₂ D.fSharp₂) (reshapeHom t E.O₂ E.fSharp₂) f
          (RingedToposHom.mk P s₂) D.second E.second comm₂ F ≫
        (SheafOfModules.restrictScalars (ringMap
            (inverseImageReducedStructureMap i t f (RingedToposHom.mk P s₁) comm₁))).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map D.idealMap) :=
              by
  have hnat := inverseImageBaseIdealToIdeal_naturality D E f P s₁ s₂ comm₁ comm₂ hsq
  have hred := Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap_natural_left
    (inverseImageReducedStructureMap i t f (RingedToposHom.mk P s₁) comm₁) D.idealMap
    (reducedBaseModule i t f (RingedToposHom.mk P s₁) comm₁ F) F (𝟙 _)
  have hmc1 :
      ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageReducedBaseRing t (RingedToposHom.mk
          P s₁))).flip.obj (reducedBaseModule i t f (RingedToposHom.mk P s₁) comm₁ F)).map
          ((inverseImageModules P (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing t))).map
              E.idealMap) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageReducedBaseRing t
            (RingedToposHom.mk P s₁))).flip.obj (reducedBaseModule i t f (RingedToposHom.mk P s₁)
            comm₁ F)).map
          (inverseImageBaseIdealToIdeal i t f (RingedToposHom.mk P s₁) D.first E.first comm₁) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageReducedBaseRing t (RingedToposHom.mk
          P s₁))).flip.obj (reducedBaseModule i t f (RingedToposHom.mk P s₁) comm₁ F)).map
        (inverseImageBaseIdealToIdeal (reshapeHom i D.O₂ D.fSharp₂)
              (reshapeHom t E.O₂ E.fSharp₂) f (RingedToposHom.mk P s₂)
              D.second E.second comm₂ ≫
          (SheafOfModules.restrictScalars (ringMap
              (inverseImageReducedStructureMap i t f (RingedToposHom.mk P s₁) comm₁))).map
            D.idealMap) :=
    (((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageReducedBaseRing t (RingedToposHom.mk P
        s₁))).flip.obj (reducedBaseModule i t f (RingedToposHom.mk P s₁) comm₁ F)).map_comp _
        _).symm.trans
      (congrArg (fun m ↦ ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageReducedBaseRing t
          (RingedToposHom.mk P s₁))).flip.obj (reducedBaseModule i t f (RingedToposHom.mk P s₁)
          comm₁ F)).map m) hnat)
  have hmc2 :
      ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageReducedBaseRing t (RingedToposHom.mk
          P s₁))).flip.obj (reducedBaseModule i t f (RingedToposHom.mk P s₁) comm₁ F)).map
        (inverseImageBaseIdealToIdeal (reshapeHom i D.O₂ D.fSharp₂)
              (reshapeHom t E.O₂ E.fSharp₂) f (RingedToposHom.mk P s₂)
              D.second E.second comm₂ ≫
          (SheafOfModules.restrictScalars (ringMap
              (inverseImageReducedStructureMap i t f (RingedToposHom.mk P s₁) comm₁))).map
            D.idealMap) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageReducedBaseRing t (RingedToposHom.mk
          P s₁))).flip.obj (reducedBaseModule i t f (RingedToposHom.mk P s₁) comm₁ F)).map
          (inverseImageBaseIdealToIdeal (reshapeHom i D.O₂ D.fSharp₂)
            (reshapeHom t E.O₂ E.fSharp₂) f (RingedToposHom.mk P s₂)
            D.second E.second comm₂) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageReducedBaseRing t
            (RingedToposHom.mk P s₁))).flip.obj (reducedBaseModule i t f (RingedToposHom.mk P s₁)
            comm₁ F)).map
          ((SheafOfModules.restrictScalars (ringMap
              (inverseImageReducedStructureMap i t f (RingedToposHom.mk P s₁) comm₁))).map
            D.idealMap) :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageReducedBaseRing t (RingedToposHom.mk P
        s₁))).flip.obj (reducedBaseModule i t f (RingedToposHom.mk P s₁) comm₁ F)).map_comp _ _
  change ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageReducedBaseRing t
      (RingedToposHom.mk P s₁))).flip.obj
        (reducedBaseModule i t f (RingedToposHom.mk P s₁) comm₁ F)).map
        ((inverseImageModules P (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing t))).map
            E.idealMap) ≫
      (((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageReducedBaseRing t (RingedToposHom.mk
          P s₁))).flip.obj (reducedBaseModule i t f (RingedToposHom.mk P s₁) comm₁ F)).map
            (inverseImageBaseIdealToIdeal i t f (RingedToposHom.mk P s₁)
              D.first E.first comm₁) ≫
          Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap
            (inverseImageReducedStructureMap i t f (RingedToposHom.mk P s₁) comm₁) D.first.I
            (reducedBaseModule i t f (RingedToposHom.mk P s₁) comm₁ F) F (𝟙 _)) = _
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun m ↦ m ≫ Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap
    (inverseImageReducedStructureMap i t f (RingedToposHom.mk P s₁) comm₁) D.first.I
    (reducedBaseModule i t f (RingedToposHom.mk P s₁) comm₁ F) F (𝟙 _)) hmc1).trans ?_
  refine (congrArg (fun m ↦ m ≫ Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap
    (inverseImageReducedStructureMap i t f (RingedToposHom.mk P s₁) comm₁) D.first.I
    (reducedBaseModule i t f (RingedToposHom.mk P s₁) comm₁ F) F (𝟙 _)) hmc2).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun m ↦ ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageReducedBaseRing
      t (RingedToposHom.mk P s₁))).flip.obj (reducedBaseModule i t f (RingedToposHom.mk P s₁) comm₁
      F)).map
    (inverseImageBaseIdealToIdeal (reshapeHom i D.O₂ D.fSharp₂) (reshapeHom t E.O₂ E.fSharp₂)
      f (RingedToposHom.mk P s₂) D.second E.second comm₂) ≫ m) hred).trans ?_
  exact (Category.assoc _ _ _).symm
end Naturality

section FirstFactorIso

open Stacks.SheafOfModules.FlatSquareZero (ringMap)

/-- **The first factor `f^*𝒥 ⊗_O ℱ ⟶ I ⊗_O ℱ` of the canonical map of Stacks 08MQ is an
isomorphism** as soon as the vertical arrow `f'` is flat and the square is strict — no flat lift
of `ℱ` is needed.

The first factor is the map of defining ideals `f^*𝒥 ⟶ I` of Situation 08M7 tensored with `ℱ`,
and that map of ideals is itself an isomorphism under those two hypotheses, by
`Deformation.ToposThickening.MorphismOfThickenings.isIso_idealMap`. -/
theorem isIso_canonicalFirstFactor_of_isFlat (i' : RingedToposHom X Y)
    (t' : RingedToposHom B B') (f : RingedToposHom X B) (f' : RingedToposHom Y B')
    (hi : FirstOrderThickening i') (ht : FirstOrderThickening t') (comm : f'.comp i' = t'.comp f)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i')))
    (hflat : f'.IsFlat)
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i' t' f f' hi ht comm).IsStrict) :
    IsIso (canonicalFirstFactor i' t' f f' hi ht comm F) := by
  have hidealMap : IsIso
      (MorphismOfThickenings.ofFirstOrderThickenings i' t' f f' hi ht comm).idealMap :=
    MorphismOfThickenings.isIso_idealMap _ hflat hstrict
  have hx : pullbackBaseIdealMap i' t' f f' hi ht comm =
      (pullbackIdealIso t' f' ht).inv ≫
        (MorphismOfThickenings.ofFirstOrderThickenings i' t' f f' hi ht comm).idealMap := by
    rw [← pullbackIdealIso_hom_comp_pullbackBaseIdealMap i' t' f f' hi ht comm]
    exact ((pullbackIdealIso t' f' ht).inv_hom_id_assoc _).symm
  have hpb : IsIso (pullbackBaseIdealMap i' t' f f' hi ht comm) := by
    rw [hx]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _
      (inferInstance : IsIso (pullbackIdealIso t' f' ht).inv) hidealMap
  exact (isIso_tensor_pullbackBaseIdealMap_iff_isIso_canonicalFirstFactor
      i' t' f f' hi ht comm F).mp
    (Functor.isIso_map_of_isIso ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).flip.obj
        ((SheafOfModules.restrictScalars (ringMap i'.fSharp)).obj F)) _ hpb)

end FirstFactorIso

namespace FirstOrderThickeningComplex

variable (S : FirstOrderThickeningComplex i) (T : FirstOrderThickeningComplex t)

section ColumnSquares

open Stacks.Sheaves.RingedToposModules (inverseImageModules)
open Stacks.SheafOfModules.FlatSquareZero (ringMap)

variable (P : MorphismOfTopoi Y.Topos B'.Topos) (f : RingedToposHom X B)
  (s₁ : B'.O ⟶ (pushforwardCommRingFunctor P).obj Y.O)
  (s₂ : T.lower.O₂ ⟶ (pushforwardCommRingFunctor P).obj S.lower.O₂)
  (s₃ : T.O₃ ⟶ (pushforwardCommRingFunctor P).obj S.O₃)
  (commf₁ : (RingedToposHom.mk P s₁ : RingedToposHom Y B').comp i = t.comp f)
  (commf₂ : (RingedToposHom.mk P s₂ :
      RingedToposHom (reshape Y S.lower.O₂) (reshape B' T.lower.O₂)).comp
      (reshapeHom i S.lower.O₂ S.lower.fSharp₂) =
    (reshapeHom t T.lower.O₂ T.lower.fSharp₂).comp f)
  (commf₃ : (RingedToposHom.mk P s₃ :
      RingedToposHom (reshape Y S.O₃) (reshape B' T.O₃)).comp S.thirdHom = T.thirdHom.comp f)
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})] in
/-- **The naturality square of the first factors over the first horizontal arrow**, in the
vocabulary of the first column: the three columns share one base ring, one base module and one
structure map, because the squares force the three vertical arrows to have one underlying
morphism of topoi. -/
theorem canonicalFirstFactor_square_lower
    (hsq₁ : (S.columnTwo T P s₂).comp S.lowerHorizontalHom =
      T.lowerHorizontalHom.comp (columnOne P s₁)) :
    canonicalFirstFactor (reshapeHom i S.lower.O₂ S.lower.fSharp₂)
        (reshapeHom t T.lower.O₂ T.lower.fSharp₂) f (RingedToposHom.mk P s₂)
        S.lower.second T.lower.second commf₂ F ≫
        (SheafOfModules.restrictScalars (ringMap
            (inverseImageReducedStructureMap i t f (RingedToposHom.mk P s₁) commf₁))).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map S.idealMap₂₁) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageReducedBaseRing t (RingedToposHom.mk
          P s₁))).flip.obj (reducedBaseModule i t f (RingedToposHom.mk P s₁) commf₁ F)).map
          ((inverseImageModules P (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing t))).map
              T.idealMap₂₁) ≫
        canonicalFirstFactor i t f (RingedToposHom.mk P s₁) S.lower.first T.lower.first commf₁ F :=
  (canonicalFirstFactor_naturality S.lower T.lower f P s₁ s₂ commf₁ commf₂
    (S.fSharpInverseImage_lowerSquare T P s₁ s₂ hsq₁) F).symm

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})] in
/-- **The naturality square of the first factors over the second horizontal arrow**, in the
vocabulary of the first column. -/
theorem canonicalFirstFactor_square_upper
    (hsq₂ : (S.columnThree T P s₃).comp S.upperHorizontalHom =
      T.upperHorizontalHom.comp (S.columnTwo T P s₂)) :
    canonicalFirstFactor S.thirdHom T.thirdHom f (RingedToposHom.mk P s₃)
        S.third T.third commf₃ F ≫
        (SheafOfModules.restrictScalars (ringMap
            (inverseImageReducedStructureMap i t f (RingedToposHom.mk P s₁) commf₁))).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map S.idealMap₃₂) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageReducedBaseRing t (RingedToposHom.mk
          P s₁))).flip.obj (reducedBaseModule i t f (RingedToposHom.mk P s₁) commf₁ F)).map
          ((inverseImageModules P (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing t))).map
              T.idealMap₃₂) ≫
        canonicalFirstFactor (reshapeHom i S.lower.O₂ S.lower.fSharp₂)
        (reshapeHom t T.lower.O₂ T.lower.fSharp₂) f (RingedToposHom.mk P s₂)
        S.lower.second T.lower.second commf₂ F :=
  (canonicalFirstFactor_naturality (i := reshapeHom i S.lower.O₂ S.lower.fSharp₂)
    (t := reshapeHom t T.lower.O₂ T.lower.fSharp₂) S.upper T.upper f P s₂ s₃ commf₂ commf₃
    (S.fSharpInverseImage_upperSquare T P s₂ s₃ hsq₂) F).symm

end ColumnSquares

section Main

open Stacks.Sheaves.RingedToposModules (inverseImageModules)
open Stacks.SheafOfModules.FlatSquareZero (ringMap)

/-- **The coefficient sequence of Stacks 08VY is short exact**, i.e. the predicate
`Deformation.ToposThickening.FirstOrderThickeningComplex.IsIdealTensorShortExact` holds, with no
hypothesis beyond its own. -/
theorem isIdealTensorShortExact (hS : S.IsComplex) (f : RingedToposHom X B)
    (f₁ : RingedToposHom Y B')
    (f₂ : RingedToposHom (reshape Y S.lower.O₂) (reshape B' T.lower.O₂))
    (f₃ : RingedToposHom (reshape Y S.O₃) (reshape B' T.O₃))
    (commf₁ : f₁.comp i = t.comp f)
    (commf₂ : f₂.comp (reshapeHom i S.lower.O₂ S.lower.fSharp₂) =
      (reshapeHom t T.lower.O₂ T.lower.fSharp₂).comp f)
    (commf₃ : f₃.comp S.thirdHom = T.thirdHom.comp f)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))) :
    S.IsIdealTensorShortExact T f f₁ f₂ f₃ commf₁ commf₂ commf₃ F hS := by
  intro hT hTSE hF hstrict₁ hstrict₂ hstrict₃ hflat₁ hflat₂ hflat₃ hsq₁ hsq₂
  obtain ⟨P, hP⟩ : ∃ P, f₁.toToposHom = P := ⟨_, rfl⟩
  have hvert₂ : f₂.toToposHom = P := (S.toToposHom_eq_of_lowerSquare T hsq₁).trans hP
  have hvert₃ : f₃.toToposHom = P := (S.toToposHom_eq_of_upperSquare T hsq₂).trans hvert₂
  obtain ⟨s₁, rfl⟩ := exists_eq_mk_of_toToposHom_eq f₁ hP
  obtain ⟨s₂, rfl⟩ := exists_eq_mk_of_toToposHom_eq f₂ hvert₂
  obtain ⟨s₃, rfl⟩ := exists_eq_mk_of_toToposHom_eq f₃ hvert₃
  have hA₁ := isIso_canonicalFirstFactor_of_isFlat i t f (RingedToposHom.mk P s₁)
    S.lower.first T.lower.first commf₁ F hflat₁ hstrict₁
  have hA₂ := isIso_canonicalFirstFactor_of_isFlat (reshapeHom i S.lower.O₂ S.lower.fSharp₂)
    (reshapeHom t T.lower.O₂ T.lower.fSharp₂) f (RingedToposHom.mk P s₂)
    S.lower.second T.lower.second commf₂ F hflat₂ hstrict₂
  have hA₃ := isIso_canonicalFirstFactor_of_isFlat S.thirdHom T.thirdHom f
    (RingedToposHom.mk P s₃) S.third T.third commf₃ F hflat₃ hstrict₃
  have hF₀ : AlgebraicGeometry.SheafOfModules.IsFlat
      (reducedBaseModule i t f (RingedToposHom.mk P s₁) commf₁ F) :=
    isFlat_reducedBaseModule_of_isFlatOverBase i t f (RingedToposHom.mk P s₁)
      S.lower.first T.lower.first commf₁ F hF
  have := Stacks.Sheaves.RingedToposModules.inverseImageModules_isLeftAdjoint P
    (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing t))
  have hPSE := Stacks.Sheaves.RingedToposModules.shortExact_map_inverseImageModules P
    (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing t)) (ShortComplex.mk T.idealMap₃₂
        T.idealMap₂₁ hT) hTSE
  have hQ := Stacks.SheafOfModules.sheafTensorRight_shortExact_of_flat_factor _
    (reducedBaseModule i t f (RingedToposHom.mk P s₁) commf₁ F) hPSE hF₀
  obtain ⟨hz, hQSE⟩ := hQ
  refine Stacks.SheafOfModules.ChangeOfRings.shortExact_of_shortExact_map_restrictScalars
    (ringMap (inverseImageReducedStructureMap i t f (RingedToposHom.mk P s₁) commf₁)) ?_
  refine ShortComplex.shortExact_of_iso ?_ hQSE
  refine ShortComplex.isoMk
    (show ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageReducedBaseRing t
        (RingedToposHom.mk P s₁))).flip.obj (reducedBaseModule i t f (RingedToposHom.mk P s₁)
        commf₁ F)).obj
            ((inverseImageModules P (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing t))).obj
                T.third.I) ≅
        (SheafOfModules.restrictScalars (ringMap
            (inverseImageReducedStructureMap i t f (RingedToposHom.mk P s₁) commf₁))).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj S.third.I) from
              @asIso _ _ _ _ _ hA₃)
    (show ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageReducedBaseRing t
        (RingedToposHom.mk P s₁))).flip.obj (reducedBaseModule i t f (RingedToposHom.mk P s₁)
        commf₁ F)).obj
            ((inverseImageModules P (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing t))).obj
              T.lower.second.I) ≅
        (SheafOfModules.restrictScalars (ringMap
            (inverseImageReducedStructureMap i t f (RingedToposHom.mk P s₁) commf₁))).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
              S.lower.second.I) from @asIso _ _ _ _ _ hA₂)
    (show ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageReducedBaseRing t
        (RingedToposHom.mk P s₁))).flip.obj (reducedBaseModule i t f (RingedToposHom.mk P s₁)
        commf₁ F)).obj
            ((inverseImageModules P (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing t))).obj
                T.lower.first.I) ≅
        (SheafOfModules.restrictScalars (ringMap
            (inverseImageReducedStructureMap i t f (RingedToposHom.mk P s₁) commf₁))).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
              S.lower.first.I) from @asIso _ _ _ _ _ hA₁) ?_ ?_
  · exact S.canonicalFirstFactor_square_upper T P f s₁ s₂ s₃ commf₁ commf₂ commf₃ F hsq₂
  · exact S.canonicalFirstFactor_square_lower T P f s₁ s₂ commf₁ commf₂ F hsq₁

end Main

end FirstOrderThickeningComplex

end Deformation.ToposThickening

end
