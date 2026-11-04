module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InertiaQuotientStackSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonalInertia
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaMonomorphism
public import StacksFrontier.CategoryTheory.TwoFibreProduct.AbstractCancelSnd
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.JointlyFaithful
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# The stabilizer as the inertia of a presentation (Stacks 06PR)

Let `𝒳` be a stack over the big fppf site of `S` and let `[U/R] ⟶ 𝒳` be a presentation
(Stacks 04TI): a smooth groupoid `(U, R, s, t, c)` in algebraic spaces over `S` together with an
equivalence `[U/R] ⟶ 𝒳` over the site. Let `G/U` be the stabilizer group algebraic space of the
groupoid (Stacks 0448). Stacks 06PR says that

```
𝒮_G  ------>  𝒮_U
 |             |
 v             v
ℐ_𝒳  ------>  𝒳
```

is a fibre product diagram, the lower horizontal arrow being the composite
`𝒮_U ⟶ [U/R] ⟶ 𝒳`.

This file proves it given Groupoids in Spaces, Lemma 06PC, with the quotient stack `[G/R']` of the
inertia groupoid of Stacks 06PB in the lower-left corner, and the second assertion of Stacks 06PB,
`ℐ_{[U/R]} = [G/R']`, both collected in `AlgebraicGeometry.Stack.InertiaQuotientStackInput`. The
diagram is read in the 2-category `CategoryTheory.CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1}`
of categories fibred in groupoids over the big fppf site, with `𝒳` an arbitrary category fibred in
groupoids over the site admitting a presentation.

## Main definitions

* `AlgebraicGeometry.Stack.inertiaCatProjection`: the forgetful 1-morphism `ℐ_𝒳 ⟶ 𝒳`, read in the
  2-category of categories fibred in groupoids over the big fppf site.
* `AlgebraicGeometry.Stack.inertiaFullyFaithfulSquare`: the inertia square `ℐ_𝒬 ⟶ ℐ_𝒳` over
  `f : 𝒬 ⟶ 𝒳` of Stacks 06R5, for a 1-morphism whose underlying functor is fully faithful.
* `AlgebraicGeometry.Stack.precomposeFstSquare`: a 2-commutative square over a cospan `(c ≫ f, g)`,
  read over the cospan `(f, g)` by composing its first leg with `c`.
* `AlgebraicGeometry.Stack.InertiaQuotientStackInput`: the two hypotheses on the presenting
  groupoid.
* `AlgebraicGeometry.Stack.inertiaPresentationSquare`: the diagram of Stacks 06PR.

## Main results

* `AlgebraicGeometry.Stack.isTwoFibreProduct_inertiaFullyFaithfulSquare`: Stacks 06R5 in the
  2-category of categories fibred in groupoids — the inertia of the source of a fully faithful
  1-morphism is the base change of the inertia of its target.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_precomposeFstSquare`: changing the first factor of a
  2-fibre product along an equivalence preserves the universal property.
* `AlgebraicGeometry.Stack.InertiaQuotientStackInput.isTwoFibreProduct_square`: the square of
  Stacks 06PC with `ℐ_{[U/R]}` in its lower-left corner, from the two hypotheses.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_inertiaPresentationSquare` and
  `AlgebraicGeometry.Stack.nonempty_isTwoFibreProduct_inertiaPresentationSquare`: Stacks 06PR,
  the diagram of the stabilizer, the object space, the inertia of `𝒳` and `𝒳` is 2-cartesian.

## References

* [Stacks Project, Tag 0448](https://stacks.math.columbia.edu/tag/0448)
* [Stacks Project, Tag 04TI](https://stacks.math.columbia.edu/tag/04TI)
* [Stacks Project, Tag 06PB](https://stacks.math.columbia.edu/tag/06PB)
* [Stacks Project, Tag 06PC](https://stacks.math.columbia.edu/tag/06PC)
* [Stacks Project, Tag 06PR](https://stacks.math.columbia.edu/tag/06PR)
* [Stacks Project, Tag 06R5](https://stacks.math.columbia.edu/tag/06R5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Inertia

variable (𝒳 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS))

/-- The forgetful 1-morphism `ℐ_𝒳 ⟶ 𝒳`, `(x, α) ↦ x`, of the inertia of a category fibred in
groupoids over the big fppf site of `S`, read in the 2-category of categories fibred in groupoids.
Its underlying based functor is `CategoryTheory.RelativeInertia.basedProjection`. -/
abbrev inertiaCatProjection : inertia B S hS 𝒳 ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom
    (RelativeInertia.basedProjection (𝒴 := BasedCategory.ofFunctor (𝟭 (BigFppfOver B S hS)))
      ⟨𝒳.val.p, Functor.comp_id 𝒳.val.p⟩)

end Inertia

section FullyFaithful

variable {𝒬 𝒳 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS)}
  (f : 𝒬 ⟶ 𝒳)

/-- The canonical 2-commutative square of the cospan `ℐ_𝒳 ⟶ 𝒳 ⟵ 𝒬`, whose apex is the explicit
2-fibre product `ℐ_𝒳 ×_𝒳 𝒬` of Stacks 0040. -/
abbrev inertiaFullyFaithfulModel :
    Bicategory.TwoCommSq (inertiaCatProjection B S hS 𝒳) f :=
  CatFiberedInGroupoids.twoFibreProductSquare.{u, u + 1, u + 1, u + 1}
    (inertiaCatProjection B S hS 𝒳) f

/-- The canonical comparison `ℐ_𝒬 ⟶ ℐ_𝒳 ×_𝒳 𝒬` of Stacks 06R5, as a 1-morphism of categories fibred
in groupoids over the big fppf site. It is `CategoryTheory.inertiaPullbackComparison`, which sends
`(x, α)` to the quadruple `(p x, (f x, f α), x, id)`. -/
noncomputable def inertiaFullyFaithfulComparison (hf : f.hom.toFunctor.FullyFaithful) :
    inertia B S hS 𝒬 ⟶ (inertiaFullyFaithfulModel B S hS f).pt :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := inertiaPullbackComparison 𝒬.val.p 𝒳.val.p f.hom.toFunctor f.hom.w
      w := (inertiaPullbackComparison_isEquivalenceOver 𝒬.val.p 𝒳.val.p f.hom.toFunctor
        f.hom.w hf).elim (fun e => e.functor_over) }

/-- The inertia square of Stacks 06R5: for a 1-morphism `f : 𝒬 ⟶ 𝒳` of categories fibred in
groupoids over the big fppf site, the 2-commutative square

```
ℐ_𝒬 --ℐ_f--> ℐ_𝒳
 |            |
 v            v
 𝒬 ---f-----> 𝒳
```

with apex `ℐ_𝒬`, obtained by reindexing the canonical 2-fibre product square of the cospan
`(ℐ_𝒳 ⟶ 𝒳, f)` along the comparison 1-morphism of Stacks 06R5. -/
noncomputable def inertiaFullyFaithfulSquare (hf : f.hom.toFunctor.FullyFaithful) :
    Bicategory.TwoCommSq (inertiaCatProjection B S hS 𝒳) f :=
  (inertiaFullyFaithfulModel B S hS f).precompose
    (inertiaFullyFaithfulComparison B S hS f hf)

/-- The apex of the inertia square of Stacks 06R5 is the inertia of `𝒬`. -/
theorem inertiaFullyFaithfulSquare_pt (hf : f.hom.toFunctor.FullyFaithful) :
    (inertiaFullyFaithfulSquare B S hS f hf).pt = inertia B S hS 𝒬 := rfl

/-- The second leg of the inertia square of Stacks 06R5 is the forgetful 1-morphism `ℐ_𝒬 ⟶ 𝒬` on
the nose. -/
theorem inertiaFullyFaithfulSquare_snd (hf : f.hom.toFunctor.FullyFaithful) :
    (inertiaFullyFaithfulSquare B S hS f hf).snd = inertiaCatProjection B S hS 𝒬 := rfl

/-- If the underlying functor of `f : 𝒬 ⟶ 𝒳` is fully faithful, then the inertia of `𝒬` is the
base change of the inertia of `𝒳` along `f`, i.e. the square

```
ℐ_𝒬 --ℐ_f--> ℐ_𝒳
 |            |
 v            v
 𝒬 ---f-----> 𝒳
```

is 2-cartesian. -/
noncomputable def isTwoFibreProduct_inertiaFullyFaithfulSquare
    (hf : f.hom.toFunctor.FullyFaithful) :
    Bicategory.IsTwoFibreProduct (inertiaFullyFaithfulSquare B S hS f hf) :=
  Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _)
    (Bicategory.TwoCommSq.PreHom.ofPrecompose _ _)
    ((inertiaPullbackComparison_isEquivalenceOver 𝒬.val.p 𝒳.val.p f.hom.toFunctor
      f.hom.w hf).elim (fun e => e.isEquivalence))

end FullyFaithful

section CospanTransport

/-- If `u = v`, then `u ≫ H.map (𝟙 Bb) ≫ 𝟙 _ = F.map (𝟙 A) ≫ 𝟙 _ ≫ v`. -/
private theorem compat_of_filler_app_eq {D : Type*} [Category D] {E₁ E₂ : Type*} [Category E₁]
    [Category E₂] (F : E₁ ⥤ D) (H : E₂ ⥤ D) {A : E₁} {Bb : E₂} {u v : F.obj A ⟶ H.obj Bb}
    (h : u = v) :
    u ≫ H.map (𝟙 Bb) ≫ 𝟙 (H.obj Bb) = F.map (𝟙 A) ≫ 𝟙 (F.obj A) ≫ v := by
  subst h
  simp

variable {𝒜 𝒜' ℬ 𝒳 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS)}
  (f : 𝒜 ⟶ 𝒳) (g : ℬ ⟶ 𝒳) (c : 𝒜' ⟶ 𝒜)

/-- Changing the first factor of the canonical 2-fibre product of Stacks 003Q along a 1-morphism
`c : 𝒜' ⟶ 𝒜`: the 1-morphism `𝒜' ×_𝒳 ℬ ⟶ 𝒜 ×_𝒳 ℬ` of
`CategoryTheory.TwoFibreProductOver.precomposeFst`, read in the 2-category of categories fibred in
groupoids over the big fppf site. It is strictly compatible with both projections: composed with
the first it is the first projection followed by `c`, and composed with the second it is the second
projection, both on the nose. -/
noncomputable def precomposeFstMor :
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u + 1, u + 1, u + 1} (c ≫ f) g).pt ⟶
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u + 1, u + 1, u + 1} f g).pt :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.precomposeFst 𝒜'.val.p 𝒜.val.p ℬ.val.p 𝒳.val.p
        f.hom.toFunctor g.hom.toFunctor c.hom.toFunctor c.hom.w
      w := TwoFibreProductOver.precomposeFst_comp_structureFunctor .. }

/-- A 2-commutative square `P` over the cospan `(c ≫ f, g)`, read over the cospan `(f, g)`: its
apex and second leg are those of `P` and its first leg is the first leg of `P` followed by `c`; the
filler is the filler of the canonical 2-fibre product square of `(f, g)` read through the composite
of the canonical comparison of `P` with `AlgebraicGeometry.Stack.precomposeFstMor`. -/
noncomputable def precomposeFstSquare (P : Bicategory.TwoCommSq (c ≫ f) g) :
    Bicategory.TwoCommSq f g where
  pt := P.pt
  fst := P.fst ≫ c
  snd := P.snd
  iso := Bicategory.whiskerLeftIso
    ((CatFiberedInGroupoids.canonicalPreHom.{u, u + 1, u + 1, u + 1} (c ≫ f) g P).hom ≫
      precomposeFstMor B S hS f g c)
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u + 1, u + 1, u + 1} f g).iso

/-- The comparison of `AlgebraicGeometry.Stack.precomposeFstSquare` with the canonical 2-fibre
product square of the cospan `(f, g)`, as a pre-morphism of 2-commutative squares. Both comparison
2-cells are identities. -/
noncomputable def precomposeFstPreHom (P : Bicategory.TwoCommSq (c ≫ f) g) :
    Bicategory.TwoCommSq.PreHom (precomposeFstSquare B S hS f g c P)
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u + 1, u + 1, u + 1} f g) where
  hom := (CatFiberedInGroupoids.canonicalPreHom.{u, u + 1, u + 1, u + 1} (c ≫ f) g P).hom ≫
    precomposeFstMor B S hS f g c
  isoFst := Iso.refl _
  isoSnd := Iso.refl _
  compat := by
    apply Bicategory.InducedBicategory.hom₂_ext
    apply BasedNatTrans.ext
    ext X
    exact compat_of_filler_app_eq f.hom.toFunctor g.hom.toFunctor rfl

/-- If `P` is a 2-fibre product of the cospan `(c ≫ f, g)` and the underlying functor of
`c : 𝒜' ⟶ 𝒜` is an equivalence, then `P` with its first leg followed by `c` is a 2-fibre product of
the cospan `(f, g)`. -/
noncomputable def isTwoFibreProduct_precomposeFstSquare (hc : c.hom.toFunctor.IsEquivalence)
    (P : Bicategory.TwoCommSq (c ≫ f) g) (hP : Bicategory.IsTwoFibreProduct P) :
    Bicategory.IsTwoFibreProduct (precomposeFstSquare B S hS f g c P) := by
  have hcan : (CatFiberedInGroupoids.canonicalPreHom.{u, u + 1, u + 1, u + 1}
      (c ≫ f) g P).hom.hom.toFunctor.IsEquivalence :=
    Bicategory.isEquivalence_of_isTwoFibreProduct hP
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _)
      (CatFiberedInGroupoids.canonicalPreHom.{u, u + 1, u + 1, u + 1} (c ≫ f) g P)
  have hmor : (precomposeFstMor B S hS f g c).hom.toFunctor.IsEquivalence :=
    TwoFibreProductOver.isEquivalence_precomposeFst 𝒜'.val.p 𝒜.val.p ℬ.val.p 𝒳.val.p
      f.hom.toFunctor g.hom.toFunctor c.hom.toFunctor c.hom.w
      ℬ.isFiberedInGroupoids 𝒜'.isFiberedInGroupoids 𝒜.isFiberedInGroupoids hc f.hom.w
  refine Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1} f g)
    (precomposeFstPreHom B S hS f g c P) ?_
  exact inferInstanceAs (((CatFiberedInGroupoids.canonicalPreHom.{u, u + 1, u + 1, u + 1}
    (c ≫ f) g P).hom.hom.toFunctor ⋙ (precomposeFstMor B S hS f g c).hom.toFunctor).IsEquivalence)

end CospanTransport

section Presentation

variable {𝒳 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS)}
  (P : GroupoidPresentation B S hS 𝒳.val)

/-- The quotient stack `[U/R]` of the presenting groupoid of a presentation, as an object of the
2-category of categories fibred in groupoids over the big fppf site. -/
noncomputable abbrev presentationQuotientStack :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (quotientStack P.groupoid)
    (isFiberedInGroupoids_quotientStack P.groupoid)

/-- The stack `𝒮_U` of the object space of the presenting groupoid of a presentation. -/
noncomputable abbrev presentationObjectStack :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (liftedFibredCategory P.groupoid.objects)
    (isStackInGroupoids_liftedFibredCategory.{u, 0} P.groupoid.objects).isFiberedInGroupoids

/-- The stack `𝒮_G` of the stabilizer group algebraic space of Stacks 0448 of the presenting
groupoid of a presentation. -/
noncomputable abbrev presentationStabilizerStack :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk
    (liftedFibredCategory (GroupoidInAlgebraicSpaces.stabilizerOverBase P.groupoid))
    (isStackInGroupoids_liftedFibredCategory.{u, 0}
      (GroupoidInAlgebraicSpaces.stabilizerOverBase P.groupoid)).isFiberedInGroupoids

/-- The presenting 1-morphism `[U/R] ⟶ 𝒳` of a presentation (Stacks 04TI), read in the 2-category
of categories fibred in groupoids over the big fppf site. -/
noncomputable abbrev presentationMorphism : presentationQuotientStack B S hS P ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom P.basedFunctor

/-- The underlying functor of the presenting 1-morphism of a presentation is fully faithful: it is
an equivalence of categories. -/
noncomputable def fullyFaithful_presentationMorphism :
    (presentationMorphism B S hS P).hom.toFunctor.FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful P.basedFunctor.toFunctor

/-- The projection `𝒮_U ⟶ [U/R]` of Stacks 044R, read in the 2-category of categories fibred in
groupoids over the big fppf site. -/
noncomputable abbrev presentationObjectProjection :
    presentationObjectStack B S hS P ⟶ presentationQuotientStack B S hS P :=
  Bicategory.InducedBicategory.mkHom (liftedQuotientStackProjection P.groupoid)

/-- The 1-morphism `𝒮_G ⟶ 𝒮_U` induced by the structure morphism `G ⟶ U` of the stabilizer group
algebraic space of Stacks 0448, which is the object map of the forgetful morphism of the inertia
groupoid of Stacks 06PB. -/
noncomputable abbrev presentationStabilizerProjection :
    presentationStabilizerStack B S hS P ⟶ presentationObjectStack B S hS P :=
  Bicategory.InducedBicategory.mkHom
    (liftedAssociatedMap (GroupoidInAlgebraicSpaces.inertiaForgetful P.groupoid).objectsMap)

/-- The quotient stack `[G/R']` of the inertia groupoid `(G, R', s', t', c')` of Stacks 06PB of
the presenting groupoid of a presentation, as an object of the 2-category of categories fibred in
groupoids over the big fppf site. -/
noncomputable abbrev presentationInertiaGroupoidStack :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk
    (quotientStack (GroupoidInAlgebraicSpaces.inertiaGroupoid P.groupoid))
    (isFiberedInGroupoids_quotientStack (GroupoidInAlgebraicSpaces.inertiaGroupoid P.groupoid))

/-- The 1-morphism `[G/R'] ⟶ [U/R]` of Stacks 046Q induced by the forgetful morphism of groupoids
from the inertia groupoid of Stacks 06PB. -/
noncomputable abbrev presentationInertiaGroupoidMorphism :
    presentationInertiaGroupoidStack B S hS P ⟶ presentationQuotientStack B S hS P :=
  Bicategory.InducedBicategory.mkHom
    (quotientStackMap (GroupoidInAlgebraicSpaces.inertiaForgetful P.groupoid))

/-- The two inputs about the presenting groupoid `(U, R, s, t, c)` of a presentation from which
Stacks 06PR follows.

The first three fields are Groupoids in Spaces, Lemma 06PC, with the quotient stack `[G/R']` of the
inertia groupoid of Stacks 06PB in the lower-left corner: a 1-morphism `𝒮_G ⟶ [G/R']`, an
invertible 2-cell filling

```
𝒮_G  ------>  𝒮_U
 |             |
 v             v
[G/R'] ----> [U/R]
```

and the assertion that that square is 2-cartesian.

The last three fields are the second assertion of Stacks 06PB, `ℐ_{[U/R]} = [G/R']`: a comparison
1-morphism `[G/R'] ⟶ ℐ_{[U/R]}` over `[U/R]` whose underlying functor is an equivalence of
categories. -/
structure InertiaQuotientStackInput where
  /-- The left vertical arrow `𝒮_G ⟶ [G/R']` of the diagram of Stacks 06PC. -/
  toInertiaGroupoid : presentationStabilizerStack B S hS P ⟶
    presentationInertiaGroupoidStack B S hS P
  /-- The invertible 2-cell filling the diagram of Stacks 06PC. -/
  commutes : toInertiaGroupoid ≫ presentationInertiaGroupoidMorphism B S hS P ≅
    presentationStabilizerProjection B S hS P ≫ presentationObjectProjection B S hS P
  /-- Stacks 06PC: that diagram is 2-cartesian. -/
  cartesian : Bicategory.IsTwoFibreProduct
    (Bicategory.TwoCommSq.mk (presentationStabilizerStack B S hS P) toInertiaGroupoid
      (presentationStabilizerProjection B S hS P) commutes)
  /-- Stacks 06PB part 2: the comparison 1-morphism `[G/R'] ⟶ ℐ_{[U/R]}`. -/
  compare : presentationInertiaGroupoidStack B S hS P ⟶
    inertia B S hS (presentationQuotientStack B S hS P)
  /-- Stacks 06PB part 2: the comparison is a 1-morphism over `[U/R]`. -/
  compare_over : compare ≫ inertiaCatProjection B S hS (presentationQuotientStack B S hS P) ≅
    presentationInertiaGroupoidMorphism B S hS P
  /-- Stacks 06PB part 2: the comparison is an equivalence. -/
  compare_isEquivalence : compare.hom.toFunctor.IsEquivalence

namespace InertiaQuotientStackInput

variable {B S hS} {P}

/-- The diagram of Stacks 06PC, as a 2-commutative square over the cospan
`[G/R'] ⟶ [U/R] ⟵ 𝒮_U`. -/
noncomputable def groupoidSquare (Z : InertiaQuotientStackInput B S hS P) :
    Bicategory.TwoCommSq (presentationInertiaGroupoidMorphism B S hS P)
      (presentationObjectProjection B S hS P) :=
  Bicategory.TwoCommSq.mk (presentationStabilizerStack B S hS P) Z.toInertiaGroupoid
    (presentationStabilizerProjection B S hS P) Z.commutes

/-- The diagram of Stacks 06PC, read over the cospan whose first leg is the composite of the
comparison of Stacks 06PB part 2 with the forgetful 1-morphism of the inertia of `[U/R]`, with the
same apex and legs. -/
noncomputable def reindexedSquare (Z : InertiaQuotientStackInput B S hS P) :
    Bicategory.TwoCommSq
      (Z.compare ≫ inertiaCatProjection B S hS (presentationQuotientStack B S hS P))
      (presentationObjectProjection B S hS P) :=
  Z.groupoidSquare.reindexFst Z.compare_over.symm

/-- The diagram of Stacks 06PC with the inertia stack of `[U/R]` in its lower-left corner: its apex
is the stack of the stabilizer, its second leg is the 1-morphism `𝒮_G ⟶ 𝒮_U` induced by `G ⟶ U`,
and its first leg is the composite `𝒮_G ⟶ [G/R'] ⟶ ℐ_{[U/R]}` of the left arrow of the diagram of
Stacks 06PC with the comparison of Stacks 06PB part 2. -/
noncomputable def square (Z : InertiaQuotientStackInput B S hS P) :
    Bicategory.TwoCommSq (inertiaCatProjection B S hS (presentationQuotientStack B S hS P))
      (presentationObjectProjection B S hS P) :=
  precomposeFstSquare B S hS
    (inertiaCatProjection B S hS (presentationQuotientStack B S hS P))
    (presentationObjectProjection B S hS P) Z.compare Z.reindexedSquare

/-- The diagram of Stacks 06PC with the inertia stack of `[U/R]` in its lower-left corner is
2-cartesian. -/
noncomputable def isTwoFibreProduct_square (Z : InertiaQuotientStackInput B S hS P) :
    Bicategory.IsTwoFibreProduct Z.square :=
  isTwoFibreProduct_precomposeFstSquare B S hS
    (inertiaCatProjection B S hS (presentationQuotientStack B S hS P))
    (presentationObjectProjection B S hS P) Z.compare Z.compare_isEquivalence
    Z.reindexedSquare
    (Bicategory.isTwoFibreProduct_reindexFst Z.compare_over.symm Z.cartesian)

end InertiaQuotientStackInput

/-- The diagram of Stacks 06PR: for a presentation `[U/R] ⟶ 𝒳` with presenting groupoid
`(U, R, s, t, c)` and stabilizer group algebraic space `G/U` (Stacks 0448), the 2-commutative
square

```
𝒮_G  ------>  𝒮_U
 |             |
 v             v
ℐ_𝒳  ------>  𝒳
```

whose apex is the stack of the stabilizer, whose lower horizontal arrow is the composite
`𝒮_U ⟶ [U/R] ⟶ 𝒳` of the projection of Stacks 044R with the presenting 1-morphism, whose right
vertical arrow is the forgetful 1-morphism of the inertia of `𝒳`, and whose left vertical arrow is
the composite `𝒮_G ⟶ ℐ_{[U/R]} ⟶ ℐ_𝒳` of the left arrow of the diagram of Stacks 06PC with the
functoriality 1-morphism of the inertia along the presentation.

It is the diagram of Stacks 06PC pasted onto the inertia square of Stacks 06R5 for the
presentation, along their common edge `ℐ_{[U/R]} ⟶ [U/R]`. -/
noncomputable def inertiaPresentationSquare (Z : InertiaQuotientStackInput B S hS P) :
    Bicategory.TwoCommSq (inertiaCatProjection B S hS 𝒳)
      (presentationObjectProjection B S hS P ≫ presentationMorphism B S hS P) :=
  (inertiaFullyFaithfulSquare B S hS (presentationMorphism B S hS P)
    (fullyFaithful_presentationMorphism B S hS P)).paste Z.square

/-- The apex of the diagram of Stacks 06PR is the stack of the stabilizer group algebraic space
`G/U` of Stacks 0448. -/
theorem inertiaPresentationSquare_pt (Z : InertiaQuotientStackInput B S hS P) :
    (inertiaPresentationSquare B S hS P Z).pt = presentationStabilizerStack B S hS P := rfl

/-- The second leg of the diagram of Stacks 06PR is the 1-morphism `𝒮_G ⟶ 𝒮_U` induced by the
structure morphism `G ⟶ U` of the stabilizer, on the nose. -/
theorem inertiaPresentationSquare_snd (Z : InertiaQuotientStackInput B S hS P) :
    (inertiaPresentationSquare B S hS P Z).snd = presentationStabilizerProjection B S hS P := rfl

/-- The first leg of the diagram of Stacks 06PR is the composite
`𝒮_G ⟶ [G/R'] ⟶ ℐ_{[U/R]} ⟶ ℐ_𝒳` of the left arrow of the diagram of Stacks 06PC, the comparison
of Stacks 06PB part 2, and the functoriality of the inertia along the presentation. -/
theorem inertiaPresentationSquare_fst (Z : InertiaQuotientStackInput B S hS P) :
    (inertiaPresentationSquare B S hS P Z).fst =
      (Z.toInertiaGroupoid ≫ Z.compare) ≫
        (inertiaFullyFaithfulSquare B S hS (presentationMorphism B S hS P)
          (fullyFaithful_presentationMorphism B S hS P)).fst := rfl

/-- Let `[U/R] ⟶ 𝒳` be a presentation and let `G/U` be the stabilizer group
algebraic space of the presenting groupoid `(U, R, s, t, c)`. Then

```
𝒮_G  ------>  𝒮_U
 |             |
 v             v
ℐ_𝒳  ------>  𝒳
```

is a fibre product diagram, i.e. a 2-fibre product in the sense of Stacks 003Q, given Groupoids in
Spaces, Lemma 06PC and the second assertion of Stacks 06PB as the hypothesis `Z`. -/
@[stacks 06PR "the diagram is 2-cartesian, given Stacks 06PC and Stacks 06PB part 2"]
noncomputable def isTwoFibreProduct_inertiaPresentationSquare
    (Z : InertiaQuotientStackInput B S hS P) :
    Bicategory.IsTwoFibreProduct (inertiaPresentationSquare B S hS P Z) :=
  Bicategory.isTwoFibreProduct_paste
    (isTwoFibreProduct_inertiaFullyFaithfulSquare B S hS (presentationMorphism B S hS P)
      (fullyFaithful_presentationMorphism B S hS P))
    Z.isTwoFibreProduct_square

/-- The diagram of the stabilizer, the object space, the inertia of `𝒳` and `𝒳` attached to a
presentation `[U/R] ⟶ 𝒳` is a fibre product diagram, given Groupoids in Spaces, Lemma 06PC with the
inertia stack of `[U/R]` in its lower-left corner. -/
@[stacks 06PR "the diagram is a fibre product diagram"]
theorem nonempty_isTwoFibreProduct_inertiaPresentationSquare
    (Z : InertiaQuotientStackInput B S hS P) :
    Nonempty (Bicategory.IsTwoFibreProduct (inertiaPresentationSquare B S hS P Z)) :=
  ⟨isTwoFibreProduct_inertiaPresentationSquare B S hS P Z⟩

end Presentation

end AlgebraicGeometry.Stack

end
