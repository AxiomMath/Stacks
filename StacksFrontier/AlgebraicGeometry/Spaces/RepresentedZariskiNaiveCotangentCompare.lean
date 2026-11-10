module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiEpsilonSquare
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map into `\NL_{X/Y}` of Stacks 0D0X, for represented algebraic spaces

Let `S` be a scheme, let `φ : U ⟶ V` be a morphism of objects of the big fppf site over `S`, let
`f₀ : X₀ ⟶ Y₀` be the morphism of the underlying schemes, and let `X = h_U`, `Y = h_V` be the
algebraic spaces they represent, so that `f = f_small` is the morphism of small étale ringed topoi
of the represented morphism `h_φ : X ⟶ Y`.

This module builds the chain map of step 2 of the proof of Stacks 0D0X,

`\NL_{ε⁻¹𝒪_{X₀} / ε⁻¹f_0^{-1}𝒪_{Y₀}} ⟶ \NL_{X/Y}`,

out of the complex that Modules on Sites, Lemma 08TZ identifies with `ε⁻¹\NL_{X₀/Y₀}` and into the
naive cotangent complex of `h_φ`.  Both halves of the square of sheaves of commutative rings it is
attached to are now available: the `ε^♯` half was already in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiNaiveCotangentComplex.lean`, and the
other half comes from the square of Derived Categories of Spaces, Remark 08GH, which is
`AlgebraicGeometry.Space.representedEpsilonSquareTwoIso` in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiEpsilonSquare.lean`.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.TwoIso.inverseImageCommRingMate_hom_app_fSharpInverseImage`
  and its `inv` companion: **a 2-isomorphism of morphisms of ringed topoi identifies the
  inverse-image forms of the two structure maps.**  This is the direction of
  `AlgebraicGeometry.RingedToposHom.TwoIso.ofPushforwardIsoCommRing` that the library did not
  carry — that declaration takes the identification as a hypothesis and produces a 2-isomorphism,
  whereas the construction below has a 2-isomorphism and needs the identification.
* `AlgebraicGeometry.Space.representedEpsilonBaseRingIso`: **the missing half of the square**,
  the identification `ε⁻¹f_0^{-1}𝒪_{Y₀} ≅ f_{small}^{-1}ε_Y^{-1}𝒪_{Y₀}` of sheaves of commutative
  rings on the small étale site of `X`, read off the square of Stacks 08GH.
* `AlgebraicGeometry.Space.representedEpsilonBaseRingMap`: the bottom edge
  `ε⁻¹f_0^{-1}𝒪_{Y₀} ⟶ f_{small}^{-1}𝒪_Y` of the square the chain map is attached to, namely that
  identification followed by `f_{small}^{-1}(ε_Y^♯)`.
* `AlgebraicGeometry.Space.representedZariskiNaiveCotangentComplexCompare`: **the chain map of
  step 2 of the proof of Stacks 0D0X**, `\NL_{ε⁻¹𝒪_{X₀} / ε⁻¹f_0^{-1}𝒪_{Y₀}} ⟶ \NL_{X/Y}`, read
  in complexes of sheaves of `ε⁻¹𝒪_{X₀}`-modules by restriction of scalars along `ε^♯`.

## Main results

* `AlgebraicGeometry.Space.representedEpsilonNaiveCotangentSquare_commutes`: **the square of
  sheaves of commutative rings the chain map is attached to commutes.**  Both composites are the
  inverse-image form of the structure map of the composite morphism of ringed topoi
  `f₀ ∘ ε_X = ε_Y ∘ f_{small}` of Stacks 08GH, transported to the iterated inverse image
  `ε⁻¹f_0^{-1}𝒪_{Y₀}`.
* `AlgebraicGeometry.Space.representedSpaceNaiveCotangentComplex_eq`: **the target of the chain
  map is `\NL_{X/Y}`.**  The naive cotangent complex of Stacks 0D0V of the represented morphism
  `h_φ` is the naive cotangent complex, on the small étale site of `X`, of the structure map of
  `f_{small}` in inverse-image form, which is the form the chain map's target is written in.
* `AlgebraicGeometry.Space.eq_comp_of_retraction_factorizations`: the reassociation the proof of
  the commutativity of the square runs on, stated over abstract objects of an abstract category
  because the concrete composites mix the two spellings of the Zariski topology of `Y₀`.

## Implementation notes

The square the chain map of Stacks 08TX is attached to is
```
ε⁻¹𝒪_{X₀} ──────────ε^♯──────────▸ 𝒪_X
   ▲                                ▲
   │ ε⁻¹(f_0^♯)                     │ f_{small}^♯
ε⁻¹f_0^{-1}𝒪_{Y₀} ──────────────▸ f_{small}^{-1}𝒪_Y
```
whose bottom edge is `AlgebraicGeometry.Space.representedEpsilonBaseRingMap`.  Its commutativity
is proved by identifying both composites with the inverse-image form of the structure map of a
single morphism of ringed topoi.  Writing `ε_X` for the comparison at `U` and `ε_Y` for the one at
`V`, the two composites of Stacks 08GH are `f₀ ∘ ε_X` and `ε_Y ∘ f_{small}`; the composition law
of Stacks 01D3 (3), in the form
`AlgebraicGeometry.RingedToposHom.comp_fSharpInverseImage_eq`, factors the structure map of each
through the comparison
`Stacks.Sheaves.ToposPushforward.inverseImageCommRingComp` of the iterated inverse image with the
inverse image along the composite; the top row of the square is the first factorization and the
bottom row is the second, and
`AlgebraicGeometry.RingedToposHom.TwoIso.inverseImageCommRingMate_inv_app_fSharpInverseImage`
applied to `AlgebraicGeometry.Space.representedEpsilonSquareTwoIso` identifies the two structure
maps.

The universes do not move.  Every sheaf of rings in sight is a sheaf of `CommRingCat.{u}` on a
site whose objects form a `Type (u + 1)`, so the two complexes are complexes of sheaves of modules
with sections in `Type (u + 1)`, exactly as in
`AlgebraicGeometry.Space.representedZariskiInverseImageNaiveCotangentComplex` and
`AlgebraicGeometry.Space.naiveCotangentComplex`.

## Scope

This file supplies the chain map of step 2 of the proof of Stacks 0D0X in the form
`\NL_{ε⁻¹𝒪_{X₀} / ε⁻¹f_0^{-1}𝒪_{Y₀}} ⟶ \NL_{X/Y}`; it does not register the tag.  Stacks 0D0X
itself, the identification `\NL_{X/Y} = ε^*\NL_{X₀/Y₀}` in `D(𝒪_X)`, is
`AlgebraicGeometry.Space.quasiIso_representedEpsilonNaiveCotangentIdentification`, which builds
the canonical map through the adjunction `ε^* ⊣ ε_*` instead of through Modules on Sites,
Lemma 08TZ.

## References

* [Stacks Project, Tag 0D0X](https://stacks.math.columbia.edu/tag/0D0X), the lemma whose step 2
  is proved here.
* [Stacks Project, Tag 08GH](https://stacks.math.columbia.edu/tag/08GH), the square of ringed
  topoi, as `AlgebraicGeometry.Space.representedEpsilonSquareTwoIso`.
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX), functoriality of the
  naive cotangent complex in a square of sheaves of rings.
* [Stacks Project, Tag 08TZ](https://stacks.math.columbia.edu/tag/08TZ), the inverse image of the
  naive cotangent complex; not available at these universes.
* [Stacks Project, Tag 0D0V](https://stacks.math.columbia.edu/tag/0D0V), the naive cotangent
  complex of a morphism of algebraic spaces.
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3), morphisms of ringed
  topoi and their composition.
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC), 2-morphisms of morphisms
  of ringed topoi.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

namespace AlgebraicGeometry.RingedToposHom

universe v₁ u₁ w₁ v₂ u₂ w₂

variable {A : RingedTopos.{v₁, u₁, w₁}} {Bt : RingedTopos.{v₂, u₂, w₂}}
  [A.J.HasSheafCompose (forget RingCat.{w₁})]
  [Bt.J.HasSheafCompose (forget RingCat.{w₂})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [Bt.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]

/-- **A 2-isomorphism of morphisms of ringed topoi identifies the inverse-image forms of the two
structure maps.**  If `t : TwoIso f g` then the mate of its isomorphism of direct images carries
the inverse-image form of the structure map of `f` to that of `g`.

This is the converse of the implication packaged by
`AlgebraicGeometry.RingedToposHom.TwoIso.ofPushforwardIsoCommRing`, which takes this equation as
a hypothesis.  Both structure maps are adjuncts of their inverse-image forms, so the equation
`forgetFSharp f ≫ t.e.hom.app _ = forgetFSharp g` of the 2-isomorphism transposes to this one by
`AlgebraicGeometry.RingedToposHom.homEquiv_comp_pushforwardIso`; forgetting the ring operations of
a sheaf of commutative rings is faithful, so the transposed equation may be read back at the level
of sheaves of commutative rings. -/
theorem TwoIso.inverseImageCommRingMate_hom_app_fSharpInverseImage
    {f g : RingedToposHom A Bt} (t : TwoIso f g) :
    (inverseImageCommRingMate f g t.e).hom.app Bt.O ≫ f.fSharpInverseImage =
      g.fSharpInverseImage := by
  have hkey : (f.toToposHom.adj.homEquiv (Bt.forgetRing.obj Bt.O) (A.forgetRing.obj A.O))
        (A.forgetRing.map f.fSharpInverseImage) ≫ t.e.hom.app (A.forgetRing.obj A.O) =
      (g.toToposHom.adj.homEquiv (Bt.forgetRing.obj Bt.O) (A.forgetRing.obj A.O))
        (A.forgetRing.map g.fSharpInverseImage) :=
    (congrArg (fun m ↦ m ≫ t.e.hom.app (A.forgetRing.obj A.O))
        (forgetFSharp_eq_homEquiv f).symm).trans
      (t.commutes.trans (forgetFSharp_eq_homEquiv g))
  have hset := (g.toToposHom.adj.homEquiv (Bt.forgetRing.obj Bt.O)
    (A.forgetRing.obj A.O)).injective
      ((homEquiv_comp_pushforwardIso f g t.e (A.forgetRing.obj A.O)
        (A.forgetRing.map f.fSharpInverseImage)).symm.trans hkey)
  exact A.forgetRing.map_injective ((A.forgetRing.map_comp _ _).trans
    ((congrArg (fun m ↦ m ≫ A.forgetRing.map f.fSharpInverseImage)
      (forgetRing_map_inverseImageCommRingMate f g t.e)).trans hset))

/-- **`AlgebraicGeometry.RingedToposHom.TwoIso.inverseImageCommRingMate_hom_app_fSharpInverseImage`
read on the inverse of the mate**, which is the direction in which a square of sheaves of rings
built from a 2-isomorphism is checked. -/
theorem TwoIso.inverseImageCommRingMate_inv_app_fSharpInverseImage
    {f g : RingedToposHom A Bt} (t : TwoIso f g) :
    (inverseImageCommRingMate f g t.e).inv.app Bt.O ≫ g.fSharpInverseImage =
      f.fSharpInverseImage := by
  rw [← t.inverseImageCommRingMate_hom_app_fSharpInverseImage, ← Category.assoc,
    Iso.inv_hom_id_app, Category.id_comp]

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U V : BigFppfOver B S hS}
  (φ : U ⟶ V)

/-! ### The missing half of the square -/

/-- **The identification `ε⁻¹f_0^{-1}𝒪_{Y₀} ≅ f_{small}^{-1}ε_Y^{-1}𝒪_{Y₀}`** of sheaves of
commutative rings on the small étale site of `X = h_U`, read off the square of Stacks 08GH.

It is the comparison of the iterated inverse image along `ε_X` and `f₀` with the inverse image
along the composite `f₀ ∘ ε_X`, followed by the mate of the isomorphism of direct images of
`AlgebraicGeometry.Space.representedEpsilonSquareTwoIso`, followed backwards by the same
comparison for `ε_Y` and `f_{small}` and the composite `ε_Y ∘ f_{small}`.

This is the half of step 2 of the proof of Stacks 0D0X that needs the square of Remark 08GH. -/
def representedEpsilonBaseRingIso :
    representedZariskiInverseImageBaseRing B S hS φ ≅
      (inverseImageCommRingFunctor
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).toToposHom).obj
        ((representedZariskiInverseImageCommRing B S hS V).obj
          ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O) :=
  (inverseImageCommRingComp (representedZariskiSchemeHom B S hS φ).toToposHom
        (representedToSchemeZariskiRingedToposHom B S hS U).toToposHom).app
      ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O ≪≫
    ((AlgebraicGeometry.RingedToposHom.inverseImageCommRingMate
          (representedZariskiEpsilonCompLeft B S hS φ)
          (representedZariskiEpsilonCompRight B S hS φ)
          (representedEpsilonSquareTwoIso B S hS φ).e).app
        ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O).symm ≪≫
    ((inverseImageCommRingComp (representedToSchemeZariskiRingedToposHom B S hS V).toToposHom
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).toToposHom).app
        ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O).symm

/-- **The bottom edge `ε⁻¹f_0^{-1}𝒪_{Y₀} ⟶ f_{small}^{-1}𝒪_Y`** of the square of sheaves of
commutative rings on the small étale site of `X = h_U` that the chain map of Stacks 08TX is
attached to: the identification `AlgebraicGeometry.Space.representedEpsilonBaseRingIso` of the
square of Stacks 08GH, followed by the inverse image along `f_{small}` of the structure map of
`ε_Y`. -/
def representedEpsilonBaseRingMap :
    representedZariskiInverseImageBaseRing B S hS φ ⟶
      (inverseImageCommRingFunctor
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).toToposHom).obj
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O :=
  (representedEpsilonBaseRingIso B S hS φ).hom ≫
    (inverseImageCommRingFunctor
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).toToposHom).map
      (representedZariskiStructureSharpInverseImage B S hS V)

/-- `AlgebraicGeometry.Space.representedEpsilonBaseRingMap` written out: the three factors of
`AlgebraicGeometry.Space.representedEpsilonBaseRingIso` followed by `f_{small}^{-1}(ε_Y^♯)`. -/
theorem representedEpsilonBaseRingMap_eq :
    representedEpsilonBaseRingMap B S hS φ =
      (inverseImageCommRingComp (representedZariskiSchemeHom B S hS φ).toToposHom
            (representedToSchemeZariskiRingedToposHom B S hS U).toToposHom).hom.app
          ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O ≫
        (AlgebraicGeometry.RingedToposHom.inverseImageCommRingMate
              (representedZariskiEpsilonCompLeft B S hS φ)
              (representedZariskiEpsilonCompRight B S hS φ)
              (representedEpsilonSquareTwoIso B S hS φ).e).inv.app
            ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O ≫
          (inverseImageCommRingComp (representedToSchemeZariskiRingedToposHom B S hS V).toToposHom
                (smallEtaleRingedToposHom B S hS
                  (representedSpaceMap B S hS φ)).toToposHom).inv.app
              ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O ≫
            (inverseImageCommRingFunctor
                (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).toToposHom).map
              (representedZariskiStructureSharpInverseImage B S hS V) :=
  rfl

/-! ### The square commutes -/

/-- **The reassociation behind
`AlgebraicGeometry.Space.representedEpsilonNaiveCotangentSquare_commutes`, over abstract objects
of an abstract category.**  Two morphisms `cl : L ⟶ T` and `cr : R ⟶ T` identified by `mi : L ⟶ R`,
with `cr` factored as `p ≫ q ≫ s` and `cl` as `hinv ≫ m` for a retraction `h ≫ hinv = 𝟙`, give
`m = (h ≫ mi ≫ p ≫ q) ≫ s`.

It is stated abstractly on purpose.  In the concrete situation the sheaf of rings `𝒪_{Y₀}` is
reached through two different spellings of the Zariski topology of `Y₀` — through
`AlgebraicGeometry.RingedTopos.J` on one side and through
`TopologicalSpace.Opens.grothendieckTopology` on the other — so the composites are not
type-correct at the transparency `rewrite` works at and no rewriting can be done in the goal.  The
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiEpsilonSquare.lean` record the
discipline:
state the step over abstract objects and apply it with `exact`. -/
theorem eq_comp_of_retraction_factorizations {D : Type*} [Category D] {A L R P Q T : D}
    (h : A ⟶ L) (hinv : L ⟶ A) (mi : L ⟶ R) (p : R ⟶ P) (q : P ⟶ Q) (s : Q ⟶ T)
    (cl : L ⟶ T) (cr : R ⟶ T) (m : A ⟶ T) (hid : h ≫ hinv = 𝟙 A)
    (hr : cr = p ≫ q ≫ s) (ht : mi ≫ cr = cl) (hl : cl = hinv ≫ m) :
    m = (h ≫ mi ≫ p ≫ q) ≫ s := by
  rw [Category.assoc, Category.assoc, Category.assoc, ← hr, ht, hl, ← Category.assoc, hid,
    Category.id_comp]

/-- **The square of sheaves of commutative rings on the small étale site of `X = h_U` that the
chain map of Stacks 08TX is attached to commutes.**  Going down the `ε⁻¹𝒪_{X₀}` side,
`ε⁻¹(f_0^♯)` followed by `ε^♯`, is the same as going along the bottom,
`AlgebraicGeometry.Space.representedEpsilonBaseRingMap`, followed by the structure map of
`f_{small}` in inverse-image form.

Both sides are the inverse-image form of the structure map of a composite morphism of ringed
topoi, transported along the comparison of the iterated inverse image with the inverse image
along the composite: on the left the composite is `f₀ ∘ ε_X` and on the right it is
`ε_Y ∘ f_{small}`, and the square of Stacks 08GH identifies the two. -/
theorem representedEpsilonNaiveCotangentSquare_commutes :
    representedZariskiInverseImageSchemeSharp B S hS φ ≫
        representedZariskiStructureSharpInverseImage B S hS U =
      representedEpsilonBaseRingMap B S hS φ ≫
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).fSharpInverseImage := by
  have hL : (representedZariskiEpsilonCompLeft B S hS φ).fSharpInverseImage =
      (inverseImageCommRingComp (representedZariskiSchemeHom B S hS φ).toToposHom
            (representedToSchemeZariskiRingedToposHom B S hS U).toToposHom).inv.app
          ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O ≫
        representedZariskiBaseStructureMap B S hS φ :=
    representedZariskiBaseStructureMap_eq B S hS φ
  have hR : (representedZariskiEpsilonCompRight B S hS φ).fSharpInverseImage =
      (inverseImageCommRingComp (representedToSchemeZariskiRingedToposHom B S hS V).toToposHom
            (smallEtaleRingedToposHom B S hS
              (representedSpaceMap B S hS φ)).toToposHom).inv.app
          ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O ≫
        (inverseImageCommRingFunctor
              (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).toToposHom).map
            (representedZariskiStructureSharpInverseImage B S hS V) ≫
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).fSharpInverseImage :=
    AlgebraicGeometry.RingedToposHom.comp_fSharpInverseImage_eq
      (representedToSchemeZariskiRingedToposHom B S hS V)
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ))
  have hT :=
    AlgebraicGeometry.RingedToposHom.TwoIso.inverseImageCommRingMate_inv_app_fSharpInverseImage
      (representedEpsilonSquareTwoIso B S hS φ)
  rw [representedEpsilonBaseRingMap_eq]
  exact eq_comp_of_retraction_factorizations _ _ _ _ _ _ _ _ _
    (Iso.hom_inv_id_app _ _) hR hT hL

/-! ### The chain map of step 2 of the proof of Stacks 0D0X -/

/-- **`\NL_{X/Y}` for the represented morphism `h_φ`, written out.**  The naive cotangent complex
of Stacks 0D0V of `h_φ : X ⟶ Y` is the naive cotangent complex of sheaves of rings on the small
étale site of `X` of the structure map of `f_{small}` in inverse-image form; this is the form in
which it is the target of the chain map of Stacks 08TX below. -/
theorem representedSpaceNaiveCotangentComplex_eq :
    naiveCotangentComplex B S hS (representedSpaceMap B S hS φ) =
      Stacks.SheafOfModules.naiveCotangentComplex.{u, u + 1, u, u}
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J
        ((inverseImageCommRingFunctor
            (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).toToposHom).obj
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).fSharpInverseImage :=
  rfl

/-- **The canonical chain map of step 2 of the proof of Stacks 0D0X**

`\NL_{ε⁻¹𝒪_{X₀} / ε⁻¹f_0^{-1}𝒪_{Y₀}} ⟶ \NL_{X/Y}`,

for a morphism `φ : U ⟶ V` of objects of the big fppf site over `S`, the morphism
`f₀ : X₀ ⟶ Y₀` of the underlying schemes and the represented morphism `h_φ : X ⟶ Y` of algebraic
spaces.  It is the map of Stacks 08TX attached to the square of sheaves of commutative rings on
the small étale site of `X` whose top edge is `ε^♯ : ε⁻¹𝒪_{X₀} ⟶ 𝒪_X` and whose bottom edge is
`AlgebraicGeometry.Space.representedEpsilonBaseRingMap`, the identification
`ε⁻¹f_0^{-1}𝒪_{Y₀} ≅ f_{small}^{-1}ε_Y^{-1}𝒪_{Y₀}` of the square of Stacks 08GH followed by
`f_{small}^{-1}(ε_Y^♯)`.  The target is read in complexes of sheaves of `ε⁻¹𝒪_{X₀}`-modules by
restriction of scalars along `ε^♯`, which is the Lean reading of the source's assertion that the
map of Stacks 08TX is linear over the ring of its source.

The target is written at the naive cotangent complex of the structure map of `f_{small}` in
inverse-image form rather than as `AlgebraicGeometry.Space.naiveCotangentComplex` applied to
`h_φ`; the two are the same complex, which is
`AlgebraicGeometry.Space.representedSpaceNaiveCotangentComplex_eq`.  The written-out form is used
because unfolding `AlgebraicGeometry.Space.naiveCotangentComplex` underneath
`CategoryTheory.Functor.mapHomologicalComplex` exhausts the elaborator's budget.

The source of this map is the complex `\NL_{ε⁻¹𝒪_{X₀} / ε⁻¹f_0^{-1}𝒪_{Y₀}}` and not
`ε⁻¹\NL_{X₀/Y₀}`.  Stacks 0D0X itself is
`AlgebraicGeometry.Space.quasiIso_representedEpsilonNaiveCotangentIdentification`, which goes
through the adjunction `ε^* ⊣ ε_*` instead. -/
def representedZariskiNaiveCotangentComplexCompare :
    representedZariskiInverseImageNaiveCotangentComplex B S hS φ ⟶
      ((_root_.SheafOfModules.restrictScalars.{u + 1}
          (underlyingRingHomOfSite.{u, u + 1, u}
            (representedZariskiStructureSharpInverseImage B S hS U))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u + 1, u, u}
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J
          ((inverseImageCommRingFunctor
              (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).toToposHom).obj
            (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).fSharpInverseImage) :=
  Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare.{u, u + 1, u, u}
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J
    (representedZariskiInverseImageBaseRing B S hS φ)
    ((representedZariskiInverseImageCommRing B S hS U).obj
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O)
    (representedZariskiInverseImageSchemeSharp B S hS φ)
    ((inverseImageCommRingFunctor
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).fSharpInverseImage
    (representedEpsilonBaseRingMap B S hS φ)
    (representedZariskiStructureSharpInverseImage B S hS U)
    (representedEpsilonNaiveCotangentSquare_commutes B S hS φ)

end AlgebraicGeometry.Space

end
