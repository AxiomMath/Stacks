module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothDiagram
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductProjections
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented

/-!
# The étale-smooth diagram criterion at representable source and target (Stacks 0CIF)

Let `P` be a property of morphisms of algebraic spaces over `S` which is étale-smooth local on
the source-and-target in the sense of **Stacks 0CFZ**, and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S` whose source and target are representable by algebraic spaces `F` and
`G`. The second assertion of Stacks 0CIF says that `f` passes the existential étale-smooth
diagram test exactly when the induced morphism `F ⟶ G` of representing presheaves has `P`.

## Main results

* `AlgebraicGeometry.Stack.representingMap_preHom_comp_snd` and
  `AlgebraicGeometry.Stack.representingMap_preHom_comp_fst`: the two projections of a comparison
  1-morphism from an étale-smooth diagram's cone, read on representing presheaves.
* `AlgebraicGeometry.Stack.representingMap_twoFibreProductSquare_comm`: the canonical 2-fibre
  product square, read on representing presheaves, commutes.
* `AlgebraicGeometry.Stack.prop_representingMap_of_hasPropertyOnSomeEtaleSmoothDiagram` and
  `AlgebraicGeometry.Stack.hasPropertyOnSomeEtaleSmoothDiagram_of_prop_representingMap`, combined
  in `AlgebraicGeometry.Stack.hasPropertyOnSomeEtaleSmoothDiagram_iff_represented`:
  **Stacks 0CIF**, the assertion for representable source and target.

## Implementation notes

### The shape of the argument

Stacks disposes of this assertion in one sentence — *"if `𝒳` and `𝒴` are representable, then
Descent on Spaces, Lemma 0CG1 applies"* — and that is exactly what happens here, with
`AlgebraicGeometry.Space.prop_of_etale_smooth_surjective_square` (Stacks 0CG1, (c) ⇒ (a)) in the
forward direction and the diagram `U = F`, `V = G` in the backward one. The work is in moving a
*stack*-level diagram to a *space*-level one, and all of it is in the étale clause: the test asks
for the comparison 1-morphism to a 2-fibre product of `(b, f)` to be étale in the sense of
Stacks 04XB, while Stacks 0CG1 asks for the induced morphism `U ⟶ F ×_G V` of algebraic spaces to
be étale.

The bridge is in three steps. The comparison is taken against the **canonical** 2-fibre product
square `CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare`, whose apex is representable
by an algebraic space `T` by **Stacks 0300**; the bridge of §04XB at étaleness
(`AlgebraicGeometry.Stack.isRelativelyEtale_iff_isEtale_representingMap`) turns étaleness of the
comparison into étaleness of the induced morphism `U ⟶ T`; and `T` is identified with `F ×_G V`
compatibly with the two projections by
`AlgebraicGeometry.Stack.fibreProductIsoRepresenting_hom_comp_representingMap_fst` and `…_snd`,
which is what makes the composite `U ⟶ T ⟶ F ×_G V` the canonical comparison of the square and
not merely *some* morphism.

### Why the backward direction does not need the cone to be a 2-fibre product

The diagram the source prescribes is `U = F`, `V = G` with the two representing equivalences as
its vertical 1-morphisms, exactly as in **Stacks 06FM**
(`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_iff_represented`), whose four facts about
`AlgebraicGeometry.Stack.equivalenceOverInvMap` are reused unchanged — with surjectivity on
*points*, which the étale-smooth test asks for, obtained from surjectivity on objects through
**Stacks 04XI**.

For that diagram the comparison 1-morphism is morally an equivalence, so one would like to say
that the cone is itself a 2-fibre product and invoke
`AlgebraicGeometry.Stack.isRelativelyEtale_preHom_of_isTwoFibreProduct`. That route is **not**
taken: showing a 2-commutative square to be a 2-fibre product from a comparison with invertible
underlying 1-morphism needs the comparison 2-cells of the inverse to be *chosen* so that the two
`CategoryTheory.Bicategory.TwoCommSq.PreHom.Rel` equations hold, which is the coherence of an
adjoint equivalence in a bicategory and is not among this module's imports; it is
`CategoryTheory.Bicategory.isTwoFibreProduct_of_isEquivalence_to`, which the representable-morphism
case `StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismRelative` uses. Instead
everything is computed on representing presheaves, where the comparison is an honest
isomorphism: an arbitrary 2-fibre product `Q` is compared with the canonical one (the comparison
is invertible there by
`AlgebraicGeometry.Stack.isIso_representingMap`), and over the canonical one the identification of
the apex with `F ×_G G` has the second projection as a two-sided inverse of the comparison,
because the first leg of that fibre product is the identity of `G`.

### Elaboration pitfalls

`AlgebraicGeometry.Stack.representingMap` is a reducible abbreviation, so leaving the two
categories of `AlgebraicGeometry.Stack.representingMap_congr_twoIso` to unification exceeds
200,000 heartbeats with `timeout at whnf`, reported at the statement rather than at the tactic;
they are given by name throughout. And the apex of the canonical square is read against
`AlgebraicGeometry.Stack.twoFibreProduct` through a `let`, as the Stacks 06FM proof does:
Stacks 0300 is stated for the latter and the two agree only definitionally.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 02ZZ](https://stacks.math.columbia.edu/tag/02ZZ)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 0CFZ](https://stacks.math.columbia.edu/tag/0CFZ)
* [Stacks Project, Tag 0CG1](https://stacks.math.columbia.edu/tag/0CG1)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparison 1-morphism of an étale-smooth diagram, read on the second projection.** For
a morphism `k` of 2-commutative squares from the cone of a diagram over `f` to any 2-commutative
square `Q` over `(b, f)`, the induced morphism of representing presheaves followed by the one
induced by the second projection of `Q` is the one induced by the left vertical 1-morphism of the
diagram.

This is the comparison 2-cell `k.isoSnd`, which Stacks 04SW does not see, together with
functoriality. -/
theorem representingMap_preHom_comp_snd
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eX : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : fibredCategory B S hS U ⟶ 𝒳) (b : fibredCategory B S hS V ⟶ 𝒴) (h : U ⟶ V)
    (η : (associatedMap B S hS h).1 ≫ b ≅ a ≫ f)
    (Q : Bicategory.TwoCommSq b f)
    (k : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f a b h η) Q)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eT : StacksRepresentableCFG.EquivalenceOver
      Q.pt.val.p (presheafOfCategories (T ⋙ typeToCat)).p) :
    representingMap B S hS (fibredCategory B S hS U) Q.pt U T
          (StacksRepresentableCFG.EquivalenceOver.refl _) eT k.hom ≫
        representingMap B S hS Q.pt 𝒳 T F eT eX Q.snd =
      representingMap B S hS (fibredCategory B S hS U) 𝒳 U F
        (StacksRepresentableCFG.EquivalenceOver.refl _) eX a := by
  rw [← representingMap_comp (𝒜 := fibredCategory B S hS U) (ℬ := Q.pt) (𝒞 := 𝒳) B S hS U T F
    (StacksRepresentableCFG.EquivalenceOver.refl _) eT eX k.hom Q.snd]
  exact (representingMap_congr_twoIso (𝒜 := fibredCategory B S hS U) (𝒞 := 𝒳) B S hS U F
    (StacksRepresentableCFG.EquivalenceOver.refl _) eX k.isoSnd).symm

/-- **The comparison 1-morphism of an étale-smooth diagram, read on the first projection.** For a
morphism `k` of 2-commutative squares from the cone of a diagram over `f` to any 2-commutative
square `Q` over `(b, f)`, the induced morphism of representing presheaves followed by the one
induced by the first projection of `Q` is the top horizontal morphism `h` of the diagram.

This is the comparison 2-cell `k.isoFst` together with functoriality and
`AlgebraicGeometry.Stack.representingMap_associatedMap`. -/
theorem representingMap_preHom_comp_fst
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : fibredCategory B S hS U ⟶ 𝒳) (b : fibredCategory B S hS V ⟶ 𝒴) (h : U ⟶ V)
    (η : (associatedMap B S hS h).1 ≫ b ≅ a ≫ f)
    (Q : Bicategory.TwoCommSq b f)
    (k : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f a b h η) Q)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eT : StacksRepresentableCFG.EquivalenceOver
      Q.pt.val.p (presheafOfCategories (T ⋙ typeToCat)).p) :
    representingMap B S hS (fibredCategory B S hS U) Q.pt U T
          (StacksRepresentableCFG.EquivalenceOver.refl _) eT k.hom ≫
        representingMap B S hS Q.pt (fibredCategory B S hS V) T V eT
          (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst = h := by
  rw [← representingMap_comp (𝒜 := fibredCategory B S hS U) (ℬ := Q.pt)
    (𝒞 := fibredCategory B S hS V) B S hS U T V
    (StacksRepresentableCFG.EquivalenceOver.refl _) eT
    (StacksRepresentableCFG.EquivalenceOver.refl _) k.hom Q.fst,
    ← representingMap_congr_twoIso (𝒜 := fibredCategory B S hS U)
    (𝒞 := fibredCategory B S hS V) B S hS U V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) k.isoFst]
  exact representingMap_associatedMap B S hS U V h

/-- **The canonical 2-fibre product square commutes on representing presheaves.** The
2-commutativity of the canonical square over a cospan `(b, f)` of 1-morphisms between categories
representable by algebraic spaces becomes a commuting square of morphisms of representing
presheaves, Stacks 04SW not seeing the 2-cell. -/
theorem representingMap_twoFibreProductSquare_comm
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eX : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eY : StacksRepresentableCFG.EquivalenceOver
      𝒴.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (b : fibredCategory B S hS V ⟶ 𝒴)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eT : StacksRepresentableCFG.EquivalenceOver
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b f).pt.val.p
      (presheafOfCategories (T ⋙ typeToCat)).p) :
    representingMap B S hS
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b f).pt 𝒳 T F eT eX
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b f).snd ≫
        representingMap B S hS 𝒳 𝒴 F G eX eY f =
      representingMap B S hS
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b f).pt
          (fibredCategory B S hS V) T V eT
          (StacksRepresentableCFG.EquivalenceOver.refl _)
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b f).fst ≫
        representingMap B S hS (fibredCategory B S hS V) 𝒴 V G
          (StacksRepresentableCFG.EquivalenceOver.refl _) eY b := by
  rw [← representingMap_comp
    (𝒜 := (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b f).pt)
    (ℬ := 𝒳) (𝒞 := 𝒴) B S hS T F G eT eX eY _ f,
    ← representingMap_comp
    (𝒜 := (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b f).pt)
    (ℬ := fibredCategory B S hS V) (𝒞 := 𝒴) B S hS T V G eT
    (StacksRepresentableCFG.EquivalenceOver.refl _) eY _ b]
  exact (representingMap_congr_twoIso
    (𝒜 := (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b f).pt)
    (𝒞 := 𝒴) B S hS T G eT eY
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b f).iso).symm

/-- **A morphism to the chosen pullback whose two projections are those of the explicit fibre
product of presheaves is an isomorphism.** Both are limits of the same cospan, so the comparison
between them is invertible; the explicit fibre product enters through an isomorphism `e` because
it is the shape Stacks 04SD produces, while the étale-smooth criterion for algebraic spaces is
phrased through the chosen pullback. -/
theorem isIso_of_fibreProduct_projections
    {X Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (mF : X ⟶ Z) (mG : Y ⟶ Z) (c : W ⟶ pullback mG mF)
    (e : Presheaf.fibreProduct mF mG ≅ W)
    (h1 : e.hom ≫ c ≫ pullback.fst mG mF = Presheaf.fibreProductSnd mF mG)
    (h2 : e.hom ≫ c ≫ pullback.snd mG mF = Presheaf.fibreProductFst mF mG) :
    IsIso c := by
  set l := (Presheaf.isPullback_fibreProduct mF mG).lift (pullback.snd mG mF)
    (pullback.fst mG mF) pullback.condition.symm
  have hlf : l ≫ Presheaf.fibreProductFst mF mG = pullback.snd mG mF :=
    (Presheaf.isPullback_fibreProduct mF mG).lift_fst _ _ _
  have hls : l ≫ Presheaf.fibreProductSnd mF mG = pullback.fst mG mF :=
    (Presheaf.isPullback_fibreProduct mF mG).lift_snd _ _ _
  have hiso : IsIso (e.hom ≫ c) := by
    refine ⟨l, ?_, ?_⟩
    · refine (Presheaf.isPullback_fibreProduct mF mG).hom_ext ?_ ?_
      · rwa [Category.assoc, hlf, Category.id_comp, Category.assoc]
      · rwa [Category.assoc, hls, Category.id_comp, Category.assoc]
    · refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, h1, hls, Category.id_comp]
      · rw [Category.assoc, Category.assoc, h2, hlf, Category.id_comp]
  exact IsIso.of_isIso_comp_left e.hom c

section Represented

variable (P : MorphismProperty (AlgebraicSpaces B S hS))
  (hP : Space.IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
  (eX : StacksRepresentableCFG.EquivalenceOver 𝒳.val.val.p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (eY : StacksRepresentableCFG.EquivalenceOver 𝒴.val.val.p
    (presheafOfCategories (G ⋙ typeToCat)).p)
  (f : 𝒳 ⟶ 𝒴)

include hP in
/-- **The forward half of the second assertion of Stacks 0CIF.** If `𝒳` and `𝒴` are representable
by algebraic spaces `F` and `G` and `f : 𝒳 ⟶ 𝒴` passes the existential étale-smooth diagram test
for a property `P` étale-smooth local on the source-and-target, then the induced morphism `F ⟶ G`
of representing presheaves has `P`.

The given diagram becomes a square of morphisms of algebraic spaces: its right vertical
1-morphism becomes smooth by the §04XB bridge
(`AlgebraicGeometry.Stack.isRelativelySmooth_iff_isSmooth_representingMap`), its left vertical
1-morphism becomes surjective on points by **Stacks 04XI**, its 2-cell becomes a commuting square
by `AlgebraicGeometry.Stack.representingMap_square_comm`, and its comparison to the canonical
2-fibre product becomes the canonical comparison `U ⟶ F ×_G V`, which is étale. Stacks 0CG1,
(c) ⇒ (a) then applies. -/
theorem prop_representingMap_of_hasPropertyOnSomeEtaleSmoothDiagram
    (hsome : HasPropertyOnSomeEtaleSmoothDiagram B S hS P f) :
    P (ObjectProperty.homMk (representingMap B S hS 𝒳.val 𝒴.val F G eX eY f.hom) :
      (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩) := by
  obtain ⟨U, V, hU, hV, a, b, h, η, hsurj, hbsm, hcompar, hPh⟩ := hsome
  have hfrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS f.hom
      ⟨F, hF, ⟨eX⟩⟩ ⟨G, hG, ⟨eY⟩⟩
  have hQ : Bicategory.IsTwoFibreProduct
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom f.hom) :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      b.hom f.hom
  obtain ⟨T, hT, ⟨eT₀⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒴.val
    (fibredCategory B S hS V) 𝒳.val b.hom.hom f.hom.hom hfrep
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV)
  let eT : StacksRepresentableCFG.EquivalenceOver
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom f.hom).pt.val.p
    (presheafOfCategories (T ⋙ typeToCat)).p := eT₀
  -- the right vertical 1-morphism is a smooth morphism of algebraic spaces
  have hβsm : Space.IsSmooth B S hS
      (representingMap B S hS (fibredCategory B S hS V) 𝒴.val V G
        (StacksRepresentableCFG.EquivalenceOver.refl _) eY b.hom) :=
    (isRelativelySmooth_iff_isSmooth_representingMap B S hS b.hom hbsm.1 V G hV hG
      (StacksRepresentableCFG.EquivalenceOver.refl _) eY).1 hbsm
  -- the 2-cell becomes a commuting square
  have hcomm := representingMap_square_comm B S hS f.hom F G eX eY a.hom b.hom h η
  -- the left vertical 1-morphism is surjective on points
  have harep : IsRepresentableByAlgebraicSpaces B S hS a.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS a.hom
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU) ⟨F, hF, ⟨eX⟩⟩
  have hαsurj : Space.IsSurjective B S hS
      (representingMap B S hS (fibredCategory B S hS U) 𝒳.val U F
        (StacksRepresentableCFG.EquivalenceOver.refl _) eX a.hom) :=
    (hasRelativeProperty_iff_prop_representingMap.{u, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) a.hom harep U F hU hF
      (StacksRepresentableCFG.EquivalenceOver.refl _) eX).1
      ((pointsMap_surjective_iff_isRelativelySurjective.{u, w, u + 1} B S hS a harep).1 hsurj)
  -- the comparison to the canonical 2-fibre product, and its étaleness
  have hket := hcompar
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom f.hom) hQ
    (Quotient.out (hQ.from (diagramCone B S hS f.hom a.hom b.hom h η)))
  have hkrep : IsRepresentableByAlgebraicSpaces B S hS
      (Quotient.out (hQ.from (diagramCone B S hS f.hom a.hom b.hom h η))).hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS _
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU) ⟨T, hT, ⟨eT⟩⟩
  have hψ := isEtale_representingMap_of_isRelativelyEtale B S hS
    (Quotient.out (hQ.from (diagramCone B S hS f.hom a.hom b.hom h η))).hom hkrep U T hU hT
    (StacksRepresentableCFG.EquivalenceOver.refl _) eT hket
  -- the representing space of the canonical square is the fibre product of representing presheaves
  have hsq := representingMap_twoFibreProductSquare_comm B S hS f.hom F G eX eY b.hom T eT
  let _hfib : (twoFibreProductStructureFunctor B S hS (fibredCategory B S hS V) 𝒳.val 𝒴.val
      b.hom f.hom).IsFibered :=
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      b.hom f.hom).pt.property.isFibered
  have hκiso : IsIso (pullback.lift _ _ hsq) :=
    isIso_of_fibreProduct_projections B S hS
      (representingMap B S hS (fibredCategory B S hS V) 𝒴.val V G
        (StacksRepresentableCFG.EquivalenceOver.refl _) eY b.hom)
      (representingMap B S hS 𝒳.val 𝒴.val F G eX eY f.hom) _
      (fibreProductIsoRepresenting B S hS (fibredCategory B S hS V) 𝒳.val 𝒴.val V F G
        (StacksRepresentableCFG.EquivalenceOver.refl _) eX eY b.hom f.hom T eT)
      (by rw [pullback.lift_fst]
          exact fibreProductIsoRepresenting_hom_comp_representingMap_snd B S hS
            (fibredCategory B S hS V) 𝒳.val 𝒴.val V F G
            (StacksRepresentableCFG.EquivalenceOver.refl _) eX eY b.hom f.hom T eT)
      (by rw [pullback.lift_snd]
          exact fibreProductIsoRepresenting_hom_comp_representingMap_fst B S hS
            (fibredCategory B S hS V) 𝒳.val 𝒴.val V F G
            (StacksRepresentableCFG.EquivalenceOver.refl _) eX eY b.hom f.hom T eT)
  have hκet : Space.IsEtale B S hS (pullback.lift _ _ hsq) :=
    Space.isEtale_of_isIso B S hS _
  -- the composite is the canonical comparison of the square of algebraic spaces
  have hlift : representingMap B S hS (fibredCategory B S hS U)
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom f.hom).pt U T
        (StacksRepresentableCFG.EquivalenceOver.refl _) eT
        (Quotient.out (hQ.from (diagramCone B S hS f.hom a.hom b.hom h η))).hom ≫
      pullback.lift _ _ hsq =
      pullback.lift
        (representingMap B S hS (fibredCategory B S hS U) 𝒳.val U F
          (StacksRepresentableCFG.EquivalenceOver.refl _) eX a.hom) h hcomm.symm := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      exact representingMap_preHom_comp_snd B S hS f.hom F eX a.hom b.hom h η _
        (Quotient.out (hQ.from (diagramCone B S hS f.hom a.hom b.hom h η))) T eT
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
      exact representingMap_preHom_comp_fst B S hS f.hom a.hom b.hom h η _
        (Quotient.out (hQ.from (diagramCone B S hS f.hom a.hom b.hom h η))) T eT
  exact Space.prop_of_etale_smooth_surjective_square B S hS hP hF hG hU hV
    (representingMap B S hS 𝒳.val 𝒴.val F G eX eY f.hom)
    (representingMap B S hS (fibredCategory B S hS V) 𝒴.val V G
      (StacksRepresentableCFG.EquivalenceOver.refl _) eY b.hom)
    (representingMap B S hS (fibredCategory B S hS U) 𝒳.val U F
      (StacksRepresentableCFG.EquivalenceOver.refl _) eX a.hom)
    h hcomm.symm hβsm hαsurj (hlift ▸ Space.isEtale_comp B S hS hψ hκet) hPh

/-- **The converse half of the second assertion of Stacks 0CIF.** If `𝒳` and `𝒴` are
representable by algebraic spaces `F` and `G` and the induced morphism `F ⟶ G` of representing
presheaves has `P`, then `f` passes the existential étale-smooth diagram test.

The diagram is the source's own: `U = F`, `V = G`, with the two representing equivalences as its
vertical 1-morphisms and the induced morphism as its top horizontal morphism, exactly as in
Stacks 06FM. Smoothness of the right vertical 1-morphism and 2-commutativity are
`AlgebraicGeometry.Stack.isRelativelySmooth_equivalenceOverInvMap` and
`AlgebraicGeometry.Stack.nonempty_twoIso_equivalenceOverInvMap`; surjectivity on points comes from
surjectivity on objects by **Stacks 04XI**.

For the étale clause, see the implementation notes of this module: an arbitrary 2-fibre product
is compared with the canonical one, over which the morphism of representing presheaves induced by
the comparison is inverse to the second projection of `F ×_G G`, the first leg of that fibre
product being the identity of `G`. No hypothesis on `P` is needed in this direction. -/
theorem hasPropertyOnSomeEtaleSmoothDiagram_of_prop_representingMap
    (hprop : P (ObjectProperty.homMk (representingMap B S hS 𝒳.val 𝒴.val F G eX eY f.hom) :
      (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)) :
    HasPropertyOnSomeEtaleSmoothDiagram B S hS P f := by
  have hfrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS f.hom
      ⟨F, hF, ⟨eX⟩⟩ ⟨G, hG, ⟨eY⟩⟩
  have harep : IsRepresentableByAlgebraicSpaces B S hS
      (equivalenceOverInvMap B S hS F eX).hom :=
    isRepresentableByAlgebraicSpaces_equivalenceOverInvMap B S hS F hF eX
  refine ⟨F, G, hF, hG,
    Bicategory.InducedBicategory.mkHom (equivalenceOverInvMap B S hS F eX),
    Bicategory.InducedBicategory.mkHom (equivalenceOverInvMap B S hS G eY),
    representingMap B S hS 𝒳.val 𝒴.val F G eX eY f.hom,
    (nonempty_twoIso_equivalenceOverInvMap B S hS F G eX eY f.hom).some,
    ?_, isRelativelySmooth_equivalenceOverInvMap B S hS G hG eY, ?_, hprop⟩
  · exact (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u + 1} B S hS
      (Bicategory.InducedBicategory.mkHom (equivalenceOverInvMap B S hS F eX) :
        algebraicSpaceStack.{u, w} B S hS F hF ⟶ 𝒳) harep).2
      ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS
        (equivalenceOverInvMap B S hS F eX) harep).1
        (isSurjectiveOnObjects_equivalenceOverInvMap B S hS F eX))
  intro Q hQ k
  -- the canonical 2-fibre product square and its representing algebraic space
  have hQ₀ : Bicategory.IsTwoFibreProduct
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (equivalenceOverInvMap B S hS G eY) f.hom) :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (equivalenceOverInvMap B S hS G eY) f.hom
  obtain ⟨T, hT, ⟨eT₀'⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒴.val
    (fibredCategory B S hS G) 𝒳.val (equivalenceOverInvMap B S hS G eY).hom f.hom.hom hfrep
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS G hG)
  let eT : StacksRepresentableCFG.EquivalenceOver
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (equivalenceOverInvMap B S hS G eY) f.hom).pt.val.p
    (presheafOfCategories (T ⋙ typeToCat)).p := eT₀'
  -- the comparison of `Q` with the canonical square, invertible both ways
  obtain ⟨e₁, -, -⟩ := Quotient.exact (hQ.hom_ext
    (Quotient.mk _ ((Quotient.out (hQ₀.from Q)).comp
      (Quotient.out (hQ.from (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (equivalenceOverInvMap B S hS G eY) f.hom))))) (𝟙 Q))
  obtain ⟨e₂, -, -⟩ := Quotient.exact (hQ₀.hom_ext
    (Quotient.mk _ ((Quotient.out (hQ.from
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (equivalenceOverInvMap B S hS G eY) f.hom))).comp (Quotient.out (hQ₀.from Q))))
    (𝟙 (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (equivalenceOverInvMap B S hS G eY) f.hom)))
  have hmEquiv : Functor.IsEquivalence (Quotient.out (hQ₀.from Q)).hom.hom.toFunctor :=
    Bicategory.isEquivalence_of_isTwoFibreProduct hQ hQ₀ (Quotient.out (hQ₀.from Q))
  obtain ⟨eQ'⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    Q.pt.isFiberedInGroupoids
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (equivalenceOverInvMap B S hS G eY) f.hom).pt.isFiberedInGroupoids
    (Quotient.out (hQ₀.from Q)).hom.hom.toFunctor (Quotient.out (hQ₀.from Q)).hom.hom.w hmEquiv
  let eQ := eQ'.trans eT
  have hkrep : IsRepresentableByAlgebraicSpaces B S hS k.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS k.hom
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS F hF) ⟨T, hT, ⟨eQ⟩⟩
  refine isRelativelyEtale_of_isEtale_representingMap B S hS k.hom hkrep F T hF hT
    (StacksRepresentableCFG.EquivalenceOver.refl _) eQ ?_
  -- the morphism induced by the comparison with `Q` is invertible
  have hρm : IsIso (representingMap B S hS Q.pt
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (equivalenceOverInvMap B S hS G eY) f.hom).pt T T eQ eT
      (Quotient.out (hQ₀.from Q)).hom) :=
    isIso_representingMap B S hS (Quotient.out (hQ₀.from Q)).hom
      (Quotient.out (hQ.from (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (equivalenceOverInvMap B S hS G eY) f.hom))).hom e₁ e₂ T T eQ eT
  have hcompeq : representingMap B S hS (fibredCategory B S hS F)
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (equivalenceOverInvMap B S hS G eY) f.hom).pt F T
        (StacksRepresentableCFG.EquivalenceOver.refl _) eT
        (k.comp (Quotient.out (hQ₀.from Q))).hom =
      representingMap B S hS (fibredCategory B S hS F) Q.pt F T
          (StacksRepresentableCFG.EquivalenceOver.refl _) eQ k.hom ≫
        representingMap B S hS Q.pt
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
            (equivalenceOverInvMap B S hS G eY) f.hom).pt T T eQ eT
          (Quotient.out (hQ₀.from Q)).hom :=
    representingMap_comp (𝒜 := fibredCategory B S hS F) (ℬ := Q.pt)
      (𝒞 := (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (equivalenceOverInvMap B S hS G eY) f.hom).pt) B S hS F T T
      (StacksRepresentableCFG.EquivalenceOver.refl _) eQ eT k.hom (Quotient.out (hQ₀.from Q)).hom
  -- the two projections of the comparison with the canonical square
  have hsnd := representingMap_preHom_comp_snd B S hS f.hom F eX
    (equivalenceOverInvMap B S hS F eX) (equivalenceOverInvMap B S hS G eY)
    (representingMap B S hS 𝒳.val 𝒴.val F G eX eY f.hom)
    (nonempty_twoIso_equivalenceOverInvMap B S hS F G eX eY f.hom).some
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (equivalenceOverInvMap B S hS G eY) f.hom)
    (k.comp (Quotient.out (hQ₀.from Q))) T eT
  rw [representingMap_equivalenceOverInvMap] at hsnd
  have hfst := representingMap_preHom_comp_fst B S hS f.hom
    (equivalenceOverInvMap B S hS F eX) (equivalenceOverInvMap B S hS G eY)
    (representingMap B S hS 𝒳.val 𝒴.val F G eX eY f.hom)
    (nonempty_twoIso_equivalenceOverInvMap B S hS F G eX eY f.hom).some
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (equivalenceOverInvMap B S hS G eY) f.hom)
    (k.comp (Quotient.out (hQ₀.from Q))) T eT
  -- the representing space of the canonical square is `F ×_G G`
  let _hfib : (twoFibreProductStructureFunctor B S hS (fibredCategory B S hS G) 𝒳.val 𝒴.val
      (equivalenceOverInvMap B S hS G eY) f.hom).IsFibered :=
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (equivalenceOverInvMap B S hS G eY) f.hom).pt.property.isFibered
  have hιs := fibreProductIsoRepresenting_hom_comp_representingMap_snd B S hS
    (fibredCategory B S hS G) 𝒳.val 𝒴.val G F G
    (StacksRepresentableCFG.EquivalenceOver.refl _) eX eY
    (equivalenceOverInvMap B S hS G eY) f.hom T eT
  have hιf := fibreProductIsoRepresenting_hom_comp_representingMap_fst B S hS
    (fibredCategory B S hS G) 𝒳.val 𝒴.val G F G
    (StacksRepresentableCFG.EquivalenceOver.refl _) eX eY
    (equivalenceOverInvMap B S hS G eY) f.hom T eT
  -- short names for the four morphisms of representing presheaves in play
  set β := representingMap B S hS (fibredCategory B S hS G) 𝒴.val G G
    (StacksRepresentableCFG.EquivalenceOver.refl _) eY (equivalenceOverInvMap B S hS G eY)
    with hβdef
  set φ := representingMap B S hS 𝒳.val 𝒴.val F G eX eY f.hom with hφdef
  set ι := fibreProductIsoRepresenting B S hS (fibredCategory B S hS G) 𝒳.val 𝒴.val G F G
    (StacksRepresentableCFG.EquivalenceOver.refl _) eX eY
    (equivalenceOverInvMap B S hS G eY) f.hom T eT with hιdef
  set χ := representingMap B S hS (fibredCategory B S hS F)
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (equivalenceOverInvMap B S hS G eY) f.hom).pt F T
    (StacksRepresentableCFG.EquivalenceOver.refl _) eT
    (k.comp (Quotient.out (hQ₀.from Q))).hom with hχdef
  -- the first leg of the fibre product is the identity of `G`
  have hβid : β = 𝟙 G := representingMap_equivalenceOverInvMap B S hS G eY
  -- so the second projection of `F ×_G G` is a two-sided inverse of the comparison
  have hξs : (χ ≫ ι.inv) ≫ Presheaf.fibreProductSnd β φ = 𝟙 F := by
    rw [← hιs, Category.assoc, Iso.inv_hom_id_assoc]
    exact hsnd
  have hξf : (χ ≫ ι.inv) ≫ Presheaf.fibreProductFst β φ = φ := by
    rw [← hιf, Category.assoc, Iso.inv_hom_id_assoc]
    exact hfst
  have hξ2 : Presheaf.fibreProductSnd β φ ≫ (χ ≫ ι.inv) = 𝟙 _ := by
    refine (Presheaf.isPullback_fibreProduct β φ).hom_ext ?_ ?_
    · rw [Category.assoc, hξf, Category.id_comp,
        ← (Presheaf.isPullback_fibreProduct β φ).w, hβid, Category.comp_id]
    · rw [Category.assoc, hξs, Category.comp_id, Category.id_comp]
  have hξiso : IsIso (χ ≫ ι.inv) := ⟨Presheaf.fibreProductSnd β φ, hξs, hξ2⟩
  have hχiso : IsIso χ := by
    have hrw : χ = (χ ≫ ι.inv) ≫ ι.hom := by
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hrw]
    infer_instance
  rw [hcompeq] at hχiso
  have hψiso : IsIso (representingMap B S hS (fibredCategory B S hS F) Q.pt F T
      (StacksRepresentableCFG.EquivalenceOver.refl _) eQ k.hom) :=
    IsIso.of_isIso_comp_right _
      (representingMap B S hS Q.pt
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (equivalenceOverInvMap B S hS G eY) f.hom).pt T T eQ eT
        (Quotient.out (hQ₀.from Q)).hom)
  exact Space.isEtale_of_isIso B S hS _



include hP in
/-- **Stacks 0CIF, the assertion for representable source and target.** For a property `P` of
morphisms of algebraic spaces over `S` which is étale-smooth local on the source-and-target, and
a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` whose source and target are representable
by algebraic spaces `F` and `G`, the existential étale-smooth diagram test holds for `f` exactly
when the induced morphism `F ⟶ G` of representing presheaves has `P`.

Forward: the given diagram becomes a square of morphisms of algebraic spaces whose comparison to
the fibre product is étale, and Stacks 0CG1 applies. Backward: test the condition on the diagram
given by the two representing equivalences. -/
@[stacks 0CIF "representable source and target"]
theorem hasPropertyOnSomeEtaleSmoothDiagram_iff_represented :
    HasPropertyOnSomeEtaleSmoothDiagram B S hS P f ↔
      P (ObjectProperty.homMk (representingMap B S hS 𝒳.val 𝒴.val F G eX eY f.hom) :
        (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩) :=
  ⟨prop_representingMap_of_hasPropertyOnSomeEtaleSmoothDiagram B S hS P hP F G hF hG eX eY f,
    hasPropertyOnSomeEtaleSmoothDiagram_of_prop_representingMap B S hS P F G hF hG eX eY f⟩

end Represented

end AlgebraicGeometry.Stack

end
