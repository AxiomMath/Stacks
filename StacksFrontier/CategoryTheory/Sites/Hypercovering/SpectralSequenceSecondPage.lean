module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.RightDerivedSheafToPresheafNaturality
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequenceHypothesis
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequenceSmallSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The second page of the hypercovering spectral sequence of a small site

Clause (3) of [Stacks, Tag 01GY] asserts a first-quadrant `E₂` cohomological spectral sequence
`E₂^{p,q} = Ȟ^p(K, H^q(F)) ⇒ H^{p+q}(X, F)`, functorial in the coefficient sheaf `F` **and** in
the hypercovering `K`. `StacksFrontier/CategoryTheory/Sites/Hypercovering/SpectralSequenceSmallSite`
supplies the sequence; this file supplies the **identification of its second page** with
`Stacks.CategoryTheory.Hypercovering.pageTwoSmallSite`, naturally in both variables
simultaneously. The abutment is not here.

## The two halves of the identification

The spectral-sequence machinery gives `''E₂^{p,q} ≅ H^p_{II}(H^q_I(A^{•,•}))` for the Čech double
complex `A^{i,j}(K, F) = Č^j(K, I^i(F))` of the chosen injective resolution, naturally for the
chosen morphisms of double complexes: that is
`HomologicalComplex₂.pageTwoIso_naturality_of_homotopyClasses`, exactly as for the Čech spectral
sequence of [Stacks, Tag 01ES]. What has to be added is the **coefficient comparison**
`H^p_{II}(H^q_I(A^{•,•}(K, Y^•))) ≅ Ȟ^p(K, H^q(Y^•))` for a complex `Y^•` of sheaves, and then
the identification of `H^q` of the section complex of an injective resolution with the cohomology
presheaf, which is `Stacks.Cohomology.cohomologyPresheafIsoResolution` of [Stacks, Tag 03AY].

The coefficient comparison is "an exact functor commutes with homology" applied three times -- to
the two extensions by zero and to the Čech complex functor of `K`. The first two are independent
of `K`, so they assemble into `extendHomologyIIIso`, a natural isomorphism of functors of the
`ℕ × ℕ`-indexed double complex. The third is not: the functor `Č^•(K, -)` itself varies with `K`,
so the naturality of that step in the simplicial semi-representable object is naturality of the
comparison in the *functor*, which is
`CategoryTheory.Functor.mapHomologicalComplexHomologyIso_app_natTrans` below -- the one generic
ingredient this file adds, and the reason the two-variable second page costs anything at all over
the one-variable second page of [Stacks, Tag 01ES].

## Main definitions

* `CategoryTheory.Functor.mapHomologicalComplexHomologyIso_app_natTrans`: the comparison
  `H^i(E(Y^•)) ≅ E(H^i(Y^•))` for an exact functor `E` is natural in `E`.
* `Stacks.CategoryTheory.Hypercovering.Functorial.cechDoubleNatSheaf₂`: the Čech double complex of
  a simplicial semi-representable object and a complex of sheaves, before either index is extended
  to `ℤ`, as a functor of the pair.
* `Stacks.CategoryTheory.Hypercovering.Functorial.cechHomologyBifunctor`:
  `(K, Y^•) ↦ Ȟ^p(K, H^q(Y^•))`.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverDoubleHomologyNatIso`,
  `Stacks.CategoryTheory.Hypercovering.Functorial.cechNatHomologyNatIso`: the two halves of the
  coefficient comparison, and
  `Stacks.CategoryTheory.Hypercovering.Functorial.cechCoefficientNatIso` their composite.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverPageTwoIso`: **the second-page
  identification of clause (3) of [Stacks, Tag 01GY] for an arbitrary simplicial semi-representable
  object**, natural in the object and in the coefficient sheaf simultaneously.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoveringPageTwoIso`: the same restricted to
  the full subcategory of hypercoverings, which is the `pageTwoIso` of the assertion.

## Implementation notes

**Nothing here carries the tag `01GY`.** Its covering set is three claim-sites and the abutment of
clause (3) is still absent; a tag lands only when its whole covering set lands.

The naturality squares are proved for a general morphism `(f, φ)` of the product category rather
than separately in the two variables: `CategoryTheory.Functor.uncurry` spells the action on
`(f, φ)` as the composite of the two, so the two-variable square *is* the pasting of the two
one-variable squares and no separate argument is needed.

## Namespace

The declarations of this file live in `Stacks.CategoryTheory.Hypercovering.Functorial`, the
namespace of the small-site, two-variable-functorial development of clause (3) of
[Stacks, Tag 01GY]; the fixed-hypercovering development of
`StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequence` keeps the enclosing namespace
`Stacks.CategoryTheory.Hypercovering`. See the namespace note of
`StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequenceSmallSite`.

## References

* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
* [Stacks Project, Tag 01ES](https://stacks.math.columbia.edu/tag/01ES)
* [Stacks Project, Tag 03AY](https://stacks.math.columbia.edu/tag/03AY)
* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- **Two commuting squares paste**, stated about an abstract category so that it can be applied
where nothing matches syntactically. Reassociating by hand at the Čech spelling below is not
possible: the middle object of each composite is written through one uncurried bifunctor on one
side and through another on the other, so the composites are type-correct only up to unfolding
those definitions and no keyed rewrite finds even `Category.assoc`. Here every term is a
variable. -/
lemma comp_paste₂ {D : Type*} [Category* D] {a b c d e g : D} {M : a ⟶ b} {N : b ⟶ c}
    {N' : a ⟶ d} {P : d ⟶ c} {Q : c ⟶ e} {Q' : d ⟶ g} {R : g ⟶ e}
    (h₁ : M ≫ N = N' ≫ P) (h₂ : P ≫ Q = Q' ≫ R) : M ≫ N ≫ Q = (N' ≫ Q') ≫ R := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

end CategoryTheory

namespace CategoryTheory.Functor

variable {B : Type*} [Category* B] [Abelian B] {B' : Type*} [Category* B'] [Abelian B']

/-- **The comparison `H(E(S)) ⟶ E(H(S))` of an exact functor with the homology of a short complex
is natural in the functor.** This is `CategoryTheory.ShortComplex.homologyMap_mapNatTrans` read as
a commuting square rather than as a formula for `homologyMap`. -/
lemma _root_.CategoryTheory.ShortComplex.mapHomologyIso_hom_natTrans
    (S : ShortComplex B) [S.HasHomology] (E E' : B ⥤ B')
    [E.PreservesZeroMorphisms] [E'.PreservesZeroMorphisms]
    [E.PreservesHomology] [E'.PreservesHomology] (τ : E ⟶ E') :
    ShortComplex.homologyMap (S.mapNatTrans τ) ≫ (S.mapHomologyIso E').hom =
      (S.mapHomologyIso E).hom ≫ τ.app S.homology := by
  rw [ShortComplex.homologyMap_mapNatTrans S τ]
  simp

/-- **The comparison `H^i(E(Y^•)) ⟶ E(H^i(Y^•))` of an exact functor with homology is natural in
the functor.** For a natural transformation `α : E ⟶ E'` of additive homology-preserving functors,
the square formed by `α` on homology and `α` degreewise on the complex commutes.

This is `CategoryTheory.ShortComplex.homologyMap_mapNatTrans`, read through the definition of
`mapHomologicalComplexHomologyIso` as `ShortComplex.homologyFunctorIso` whiskered by the
short-complex functor of a homological complex. It is what makes the Čech half of the
second-page comparison of [Stacks, Tag 01GY] natural in the simplicial semi-representable
object, whose Čech complex functor is the varying `E`. -/
lemma mapHomologicalComplexHomologyIso_app_natTrans
    (E E' : B ⥤ B') [E.Additive] [E'.Additive] [E.PreservesHomology] [E'.PreservesHomology]
    (α : E ⟶ E') {ι : Type*} (c : ComplexShape ι) (i : ι) (Y : HomologicalComplex B c) :
    (HomologicalComplex.homologyFunctor B' c i).map
          ((NatTrans.mapHomologicalComplex α c).app Y) ≫
        (mapHomologicalComplexHomologyIso E' c i).hom.app Y =
      (mapHomologicalComplexHomologyIso E c i).hom.app Y ≫ α.app (Y.homology i) :=
  ShortComplex.mapHomologyIso_hom_natTrans
    ((HomologicalComplex.shortComplexFunctor B c i).obj Y) E E' α

/-- **The comparison of an exact functor with homology is natural in the functor and in the
complex at once.** For `α : E ⟶ E'` and `φ : Y^• ⟶ Z^•`, the square formed by the composite map
`E(Y^•) ⟶ E'(Y^•) ⟶ E'(Z^•)` -- which is how a bifunctor built by
`CategoryTheory.Functor.uncurry` acts on a morphism of the product category -- commutes with the
two comparisons.

This is the form the Čech half of the second-page comparison of [Stacks, Tag 01GY] needs, and it
is stated generically on purpose: at the Čech spelling the two sides of each reassociation are
typed through different uncurryings of the same data, so nothing matches syntactically there,
whereas here every term is a variable. -/
lemma mapHomologicalComplexHomologyIso_naturality₂
    (E E' : B ⥤ B') [E.Additive] [E'.Additive] [E.PreservesHomology] [E'.PreservesHomology]
    (α : E ⟶ E') {ι : Type*} (c : ComplexShape ι) (i : ι)
    {Y Z : HomologicalComplex B c} (φ : Y ⟶ Z) :
    (HomologicalComplex.homologyFunctor B' c i).map
          ((NatTrans.mapHomologicalComplex α c).app Y ≫
            (E'.mapHomologicalComplex c).map φ) ≫
        (mapHomologicalComplexHomologyIso E' c i).hom.app Z =
      (mapHomologicalComplexHomologyIso E c i).hom.app Y ≫
        α.app (Y.homology i) ≫
          E'.map ((HomologicalComplex.homologyFunctor B c i).map φ) := by
  have hn : (HomologicalComplex.homologyFunctor B' c i).map
        ((E'.mapHomologicalComplex c).map φ) ≫
        (mapHomologicalComplexHomologyIso E' c i).hom.app Z =
      (mapHomologicalComplexHomologyIso E' c i).hom.app Y ≫
        E'.map ((HomologicalComplex.homologyFunctor B c i).map φ) :=
    (mapHomologicalComplexHomologyIso E' c i).hom.naturality φ
  rw [CategoryTheory.Functor.map_comp, Category.assoc, hn, ← Category.assoc,
    mapHomologicalComplexHomologyIso_app_natTrans E E' α c i Y]
  exact Category.assoc _ _ _

variable {A₀ : Type*} [Category* A₀] {B₀ : Type*} [Category* B₀] {D₀ : Type*} [Category* D₀]
  {E₀ : Type*} [Category* E₀]

/-- **Uncurrying commutes with right whiskering.** The two functors agree on objects; on a
morphism `(f, g)` of the product the two differ by `H.map_comp`, which is why this is an
isomorphism rather than an equality. -/
def uncurryWhiskeringRightIso (F : A₀ ⥤ B₀ ⥤ D₀) (H : D₀ ⥤ E₀) :
    uncurry.obj (F ⋙ (whiskeringRight B₀ D₀ E₀).obj H) ≅ uncurry.obj F ⋙ H :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
    dsimp
    rw [Category.id_comp, Category.comp_id, H.map_comp])

end CategoryTheory.Functor

open scoped CategoryTheory.Prod

namespace Stacks.CategoryTheory.Hypercovering.Functorial

universe w v₁ u₁ v

section Exactness

variable {C : Type u₁} [Category.{v₁} C] (X : C)

/-- `preservesHomology_cechComplexOverBifunctor_obj`, restated for an arbitrary object of the
opposite category rather than one of the form `op K`; this is the form instance search needs when
the simplicial semi-representable object is itself a variable of a functor. -/
instance preservesHomology_cechComplexOverBifunctor_obj'
    (K : (SimplicialObject (Limits.FormalCoproduct.{w} (Over X)))ᵒᵖ) :
    ((cechComplexOverBifunctor.{w} X).obj K).PreservesHomology :=
  inferInstanceAs ((cechComplexOverBifunctor.{w} X).obj (op K.unop)).PreservesHomology

end Exactness

section SmallSite

variable {C : Type v} [SmallCategory C] (X : C) (J : GrothendieckTopology C)

/-- **Both extensions by zero commute with the two homologies of a double complex.** For a double
complex indexed by `ℕ × ℕ` and extended by zero to `ℤ × ℤ` in both indices,
`H^p_{II}(H^q_I(-))` at `((p : ℤ), (q : ℤ))` is the corresponding iterated homology of the
original, naturally in the `ℕ × ℕ`-indexed double complex.

This is the part of the coefficient comparison of [Stacks, Tag 01GY] which does not see the
simplicial semi-representable object. -/
def extendHomologyIIIso (p q : ℕ) :
    (ComplexShape.embeddingUpNat.extendFunctor (CochainComplex AddCommGrpCat.{v} ℕ) ⋙
          (ComplexShape.embeddingUpNat.extendFunctor
            AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
        HomologicalComplex₂.homologyIIHomologyIFunctor AddCommGrpCat.{v} (p : ℤ) (q : ℤ) ≅
      HomologicalComplex.homologyFunctor (CochainComplex AddCommGrpCat.{v} ℕ)
          (ComplexShape.up ℕ) q ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) p :=
  Functor.isoWhiskerLeft
      (ComplexShape.embeddingUpNat.extendFunctor (CochainComplex AddCommGrpCat.{v} ℕ))
      (Functor.isoWhiskerRight
          (Functor.mapHomologicalComplexHomologyIso
            (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{v})
            (ComplexShape.up ℤ) (q : ℤ))
          (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) (p : ℤ)) ≪≫
        Functor.isoWhiskerLeft
          (HomologicalComplex.homologyFunctor (CochainComplex AddCommGrpCat.{v} ℕ)
            (ComplexShape.up ℤ) (q : ℤ))
          (ComplexShape.embeddingUpNat.extendFunctorHomologyIso
            AddCommGrpCat.{v} p (p : ℤ) rfl)) ≪≫
    Functor.isoWhiskerRight
      (ComplexShape.embeddingUpNat.extendFunctorHomologyIso
        (CochainComplex AddCommGrpCat.{v} ℕ) q (q : ℤ) rfl)
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) p)

/-- **The Čech double complex of a simplicial semi-representable object and a complex of sheaves,
over `ℕ × ℕ`**, as a functor of the pair. This is `cechDoubleSheaf₂` before either index is
extended by zero to `ℤ`. -/
def cechDoubleNatSheaf₂ :
    (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
        CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ ⥤
      HomologicalComplex (CochainComplex AddCommGrpCat.{v} ℕ) (ComplexShape.up ℕ) :=
  Functor.uncurry.obj (cechDoubleNatBifunctor X ⋙
    (Functor.whiskeringLeft (CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ)
        (CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ℕ)
        (HomologicalComplex (CochainComplex AddCommGrpCat.{v} ℕ) (ComplexShape.up ℕ))).obj
      ((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)))

/-- **`(K, Y^•) ↦ Č^•(K, H^q(Y^•))`**: the Čech complex of a simplicial semi-representable object
over `X` with coefficients in the degree-`q` homology presheaf of a complex of abelian sheaves,
contravariantly in the object and covariantly in the complex. This is the coefficient comparison
one step before its homology is taken, and it is at this level that the comparison is proved:
`cechNatHomologyApp_inner` is its naturality square, and everything after it is a whiskering. -/
def cechInnerBifunctor (q : ℕ) :
    (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
        CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ ⥤ CochainComplex AddCommGrpCat.{v} ℕ :=
  Functor.uncurry.obj (cechComplexOverBifunctor.{v} X ⋙
    (Functor.whiskeringLeft (CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ)
        (Cᵒᵖ ⥤ AddCommGrpCat.{v}) (CochainComplex AddCommGrpCat.{v} ℕ)).obj
      ((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{v}) (ComplexShape.up ℕ) q))

/-- **`(K, Y^•) ↦ Ȟ^p(K, H^q(Y^•))`**: the degree-`p` Čech cohomology of a simplicial
semi-representable object over `X` with coefficients in the degree-`q` homology presheaf of a
complex of abelian sheaves, contravariantly in the object and covariantly in the complex. This is
the target of the coefficient comparison. -/
def cechHomologyBifunctor (p q : ℕ) :
    (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
        CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ ⥤ AddCommGrpCat.{v} :=
  cechInnerBifunctor.{v} X J q ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) p

-- The bifunctors above are the same data uncurried in different orders, so a composite whose
-- middle object is spelled through one of them and whose next factor is typed through another is
-- type-correct only up to unfolding them. They are therefore made reducible for the implicit
-- arguments, for the span of this file, so that the reassociations below go through without any
-- transparency override.
attribute [local implicit_reducible] cechDoubleNatSheaf₂ cechInnerBifunctor cechHomologyBifunctor

/-- The Čech double complex over `ℤ × ℤ` is the one over `ℕ × ℕ` with both indices extended by
zero, on morphisms as well as on objects. The two extensions are functors, so this is just their
functoriality; it is stated because `cechDoubleSheaf₂` and `cechDoubleNatSheaf₂` are separate
uncurryings and `CategoryTheory.Functor.uncurry` does not commute with right whiskering on the
nose. -/
lemma cechDoubleSheaf₂_map
    {KY LZ : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ} (fφ : KY ⟶ LZ) :
    (cechDoubleSheaf₂ X J).map fφ =
      (ComplexShape.embeddingUpNat.extendFunctor (CochainComplex AddCommGrpCat.{v} ℕ) ⋙
        (ComplexShape.embeddingUpNat.extendFunctor
          AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((cechDoubleNatSheaf₂ X J).map fφ) := by
  dsimp [cechDoubleSheaf₂, cechDoubleNatSheaf₂, cechDoubleSheafBifunctor, cechDoubleBifunctor,
    cechDoubleOuterBifunctor]
  rw [Functor.map_comp, Functor.map_comp]

/-- **The extension half of the coefficient comparison**, at the Čech double complex: taking
`H^p_{II}(H^q_I(-))` of the `ℤ × ℤ`-indexed Čech double complex of a pair is the iterated homology
of the `ℕ × ℕ`-indexed one, naturally in the pair. -/
def hypercoverDoubleHomologyNatIso (p q : ℕ) :
    cechDoubleSheaf₂ X J ⋙
        HomologicalComplex₂.homologyIIHomologyIFunctor AddCommGrpCat.{v} (p : ℤ) (q : ℤ) ≅
      cechDoubleNatSheaf₂ X J ⋙
        HomologicalComplex.homologyFunctor (CochainComplex AddCommGrpCat.{v} ℕ)
            (ComplexShape.up ℕ) q ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) p :=
  NatIso.ofComponents
    (fun KY => (extendHomologyIIIso.{v} p q).app ((cechDoubleNatSheaf₂ X J).obj KY))
    (fun {KY LZ} fφ => by
      dsimp only [Functor.comp_map]
      rw [cechDoubleSheaf₂_map X J fφ]
      exact (extendHomologyIIIso.{v} p q).hom.naturality ((cechDoubleNatSheaf₂ X J).map fφ))

/-- **The inner half of the Čech comparison square.** Before `H^p` is applied, the comparison
`H^q(Č^•(K, Y^•)) ≅ Č^•(K, H^q(Y^•))` already satisfies its naturality square in the pair, as a
square of morphisms of cochain complexes of abelian groups: the complex direction is naturality of
`CategoryTheory.Functor.mapHomologicalComplexHomologyIso` in the complex, and the object direction
is its naturality in the functor. -/
lemma cechNatHomologyApp_inner (q : ℕ)
    {KY LZ : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ} (fφ : KY ⟶ LZ) :
    (HomologicalComplex.homologyFunctor (CochainComplex AddCommGrpCat.{v} ℕ)
            (ComplexShape.up ℕ) q).map ((cechDoubleNatSheaf₂ X J).map fφ) ≫
        (Functor.mapHomologicalComplexHomologyIso
            ((cechComplexOverBifunctor.{v} X).obj LZ.1) (ComplexShape.up ℕ) q).hom.app
          (((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj LZ.2) =
      (Functor.mapHomologicalComplexHomologyIso
            ((cechComplexOverBifunctor.{v} X).obj KY.1) (ComplexShape.up ℕ) q).hom.app
          (((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj KY.2) ≫
        ((cechComplexOverBifunctor.{v} X).map fφ.1).app
            ((HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{v})
              (ComplexShape.up ℕ) q).obj
              (((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj KY.2)) ≫
          ((cechComplexOverBifunctor.{v} X).obj LZ.1).map
            ((HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{v})
              (ComplexShape.up ℕ) q).map
              (((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex
                (ComplexShape.up ℕ)).map fφ.2)) :=
  Functor.mapHomologicalComplexHomologyIso_naturality₂
    ((cechComplexOverBifunctor.{v} X).obj KY.1) ((cechComplexOverBifunctor.{v} X).obj LZ.1)
    ((cechComplexOverBifunctor.{v} X).map fφ.1) (ComplexShape.up ℕ) q
    (((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex
      (ComplexShape.up ℕ)).map fφ.2)

/-- **The Čech half of the coefficient comparison**, before `H^p`: the Čech complex functor of
a simplicial semi-representable object is exact, hence commutes with the homology of a complex of
presheaves, naturally in the object and in the complex. Naturality in the complex is naturality of
`CategoryTheory.Functor.mapHomologicalComplexHomologyIso` in the complex; naturality in the object
is its naturality in the *functor*,
`CategoryTheory.Functor.mapHomologicalComplexHomologyIso_app_natTrans`, the Čech complex functor
being what varies there. -/
def cechInnerNatIso (q : ℕ) :
    cechDoubleNatSheaf₂ X J ⋙
        HomologicalComplex.homologyFunctor (CochainComplex AddCommGrpCat.{v} ℕ)
          (ComplexShape.up ℕ) q ≅
      cechInnerBifunctor.{v} X J q :=
  NatIso.ofComponents
    (fun KY => (Functor.mapHomologicalComplexHomologyIso
        ((cechComplexOverBifunctor.{v} X).obj KY.1) (ComplexShape.up ℕ) q).app
      (((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj KY.2))
    (fun {_KY _LZ} fφ => cechNatHomologyApp_inner.{v} X J q fφ)

/-- **The Čech half of the coefficient comparison**: `H^p(H^q(Č^•(K, Y^•)))` is `Ȟ^p(K, H^q(Y^•))`,
naturally in the pair. This is `cechInnerNatIso` whiskered by `H^p`, so it needs no proof of its
own. -/
def cechNatHomologyNatIso (p q : ℕ) :
    cechDoubleNatSheaf₂ X J ⋙
        HomologicalComplex.homologyFunctor (CochainComplex AddCommGrpCat.{v} ℕ)
            (ComplexShape.up ℕ) q ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) p ≅
      cechHomologyBifunctor.{v} X J p q :=
  Functor.isoWhiskerRight (cechInnerNatIso.{v} X J q)
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) p)

/-- **The coefficient comparison of [Stacks, Tag 01GY]**: `H^p_{II}(H^q_I(A^{•,•}(K, Y^•)))` is
`Ȟ^p(K, H^q(Y^•))`, naturally in the simplicial semi-representable object and in the complex of
sheaves simultaneously. -/
def cechCoefficientNatIso (p q : ℕ) :
    cechDoubleSheaf₂ X J ⋙
        HomologicalComplex₂.homologyIIHomologyIFunctor AddCommGrpCat.{v} (p : ℤ) (q : ℤ) ≅
      cechHomologyBifunctor.{v} X J p q :=
  hypercoverDoubleHomologyNatIso.{v} X J p q ≪≫ cechNatHomologyNatIso.{v} X J p q

/-- **`(K, F) ↦ Č^•(K, H^q(F))`**: the second-page functor of [Stacks, Tag 01GY] before `H^p` is
taken, with the cohomology presheaf of the coefficient sheaf as coefficients. Its `H^p` is
`Stacks.CategoryTheory.Hypercovering.pageTwoSmallSite` objectwise, and on morphisms the two differ
only by `H^p.map_comp`. -/
def pageTwoInner (q : ℕ) :
    (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ × Sheaf J AddCommGrpCat.{v} ⥤
      CochainComplex AddCommGrpCat.{v} ℕ :=
  Functor.uncurry.obj (cechComplexOverBifunctor.{v} X ⋙
    (Functor.whiskeringLeft (Sheaf J AddCommGrpCat.{v}) (Cᵒᵖ ⥤ AddCommGrpCat.{v})
        (CochainComplex AddCommGrpCat.{v} ℕ)).obj (Sheaf.cohomologyPresheafFunctor J q))

/-- **`pageTwoSmallSite` is `H^p` of `pageTwoInner` on morphisms too**, up to `H^p.map_comp`:
the two are different uncurryings of the same data, and `CategoryTheory.Functor.uncurry` does not
commute with right whiskering on the nose. -/
lemma pageTwoSmallSite_map_eq (p q : ℕ)
    {KF LG : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v}} (fg : KF ⟶ LG) :
    (pageTwoSmallSite J X p q).map fg =
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) p).map
        ((pageTwoInner.{v} X J q).map fg) :=
  ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v}
    (ComplexShape.up ℕ) p).map_comp _ _).symm

section Resolution

/-- **The resolution half of the coefficient comparison, before `H^p`**: the degree-`q` homology
presheaf of the section complex of the chosen injective resolution of `F` is the degree-`q`
cohomology presheaf of `F` ([Stacks, Tag 03AY]), and `Č^•(K, -)` of that identification compares
the Čech complex of the resolution with the second-page coefficient. -/
def innerCoefficientIso (q : ℕ)
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v}) :
    (cechInnerBifunctor.{v} X J q).obj (KF.1, (injectiveResolution KF.2).cocomplex) ≅
      (pageTwoInner.{v} X J q).obj KF :=
  ((cechComplexOverBifunctor.{v} X).obj KF.1).mapIso
    (Stacks.Cohomology.cohomologyPresheafIsoResolution J KF.2 (injectiveResolution KF.2) q)

/-- `innerCoefficientIso` is the Čech complex functor applied to
`Stacks.Cohomology.cohomologyPresheafIsoResolution`, by definition. -/
lemma innerCoefficientIso_hom (q : ℕ)
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v}) :
    (innerCoefficientIso.{v} X J q KF).hom =
      ((cechComplexOverBifunctor.{v} X).obj KF.1).map
        (Stacks.Cohomology.cohomologyPresheafIsoResolution J KF.2
          (injectiveResolution KF.2) q).hom :=
  rfl

/-- A functor carries an equality of two composites to the equality of the composites of images. -/
private lemma map_comp_eq_map_comp {M N : Type*} [Category* M] [Category* N] (F : M ⥤ N)
    {a b c b' : M} {f : a ⟶ b} {g : b ⟶ c} {f' : a ⟶ b'} {g' : b' ⟶ c} (h : f ≫ g = f' ≫ g') :
    F.map f ≫ F.map g = F.map f' ≫ F.map g' := by
  rw [← F.map_comp, h, F.map_comp]

/-- **`innerCoefficientIso` is natural for the chosen descents of injective resolutions.** The
Čech direction is naturality of the Čech complex functor in the simplicial semi-representable
object; the coefficient direction is
`Stacks.Cohomology.cohomologyPresheafIsoResolution_hom_naturality`, i.e. [Stacks, Tag 03AY]
naturally in the sheaf. -/
lemma innerCoefficientIso_naturality (q : ℕ)
    {KF LG : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v}} (fg : KF ⟶ LG) :
    (cechInnerBifunctor.{v} X J q).map
          (fg.1, InjectiveResolution.desc fg.2 (injectiveResolution LG.2)
            (injectiveResolution KF.2)) ≫
        (innerCoefficientIso.{v} X J q LG).hom =
      (innerCoefficientIso.{v} X J q KF).hom ≫ (pageTwoInner.{v} X J q).map fg := by
  have key : ((cechComplexOverBifunctor.{v} X).obj LG.1).map
          ((HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{v})
            (ComplexShape.up ℕ) q).map
            (((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex
              (ComplexShape.up ℕ)).map
              (InjectiveResolution.desc fg.2 (injectiveResolution LG.2)
                (injectiveResolution KF.2)))) ≫
        ((cechComplexOverBifunctor.{v} X).obj LG.1).map
          (Stacks.Cohomology.cohomologyPresheafIsoResolution J LG.2
            (injectiveResolution LG.2) q).hom =
      ((cechComplexOverBifunctor.{v} X).obj LG.1).map
          (Stacks.Cohomology.cohomologyPresheafIsoResolution J KF.2
            (injectiveResolution KF.2) q).hom ≫
        ((cechComplexOverBifunctor.{v} X).obj LG.1).map
          ((Sheaf.cohomologyPresheafFunctor J q).map fg.2) := by
    refine map_comp_eq_map_comp _
      (Stacks.Cohomology.cohomologyPresheafIsoResolution_hom_naturality J fg.2
        (injectiveResolution KF.2) (injectiveResolution LG.2)
        ⟨InjectiveResolution.desc fg.2 _ _, by
          simpa using InjectiveResolution.desc_commutes_zero fg.2
            (injectiveResolution LG.2) (injectiveResolution KF.2)⟩ q)
  rw [innerCoefficientIso_hom, innerCoefficientIso_hom]
  dsimp only [cechInnerBifunctor, pageTwoInner, Functor.uncurry, Functor.comp_map,
    Functor.comp_obj, Functor.whiskeringLeft_obj_obj, Functor.whiskeringLeft_obj_map,
    Functor.whiskerLeft_app]
  rw [Category.assoc, key, ← Category.assoc,
    ← ((cechComplexOverBifunctor.{v} X).map fg.1).naturality
      (Stacks.Cohomology.cohomologyPresheafIsoResolution J KF.2
        (injectiveResolution KF.2) q).hom,
    Category.assoc]

/-- **The coefficient comparison at a sheaf**: `H^p_{II}(H^q_I(A^{•,•}(K, F)))` is
`Ȟ^p(K, H^q(F))`, which is the value of `Stacks.CategoryTheory.Hypercovering.pageTwoSmallSite`. -/
def hypercoverCoefficientIso (p q : ℕ)
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v}) :
    (HomologicalComplex₂.homologyIIHomologyIFunctor AddCommGrpCat.{v} (p : ℤ) (q : ℤ)).obj
        (hypercoverDouble X J KF) ≅ (pageTwoSmallSite J X p q).obj KF :=
  (cechCoefficientNatIso.{v} X J p q).app (KF.1, (injectiveResolution KF.2).cocomplex) ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) p).mapIso
      (innerCoefficientIso.{v} X J q KF)

/-- The two factors of `hypercoverCoefficientIso`, by definition. -/
lemma hypercoverCoefficientIso_hom (p q : ℕ)
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v}) :
    (hypercoverCoefficientIso.{v} X J p q KF).hom =
      (cechCoefficientNatIso.{v} X J p q).hom.app
          (KF.1, (injectiveResolution KF.2).cocomplex) ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) p).map
          (innerCoefficientIso.{v} X J q KF).hom :=
  rfl

/-- **The coefficient comparison is natural for the chosen morphisms `hypercoverDoubleMap` of
double complexes**, which is the form the second-page identification needs. -/
lemma hypercoverCoefficientIso_naturality (p q : ℕ)
    {KF LG : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v}} (fg : KF ⟶ LG) :
    (HomologicalComplex₂.homologyIIHomologyIFunctor AddCommGrpCat.{v} (p : ℤ) (q : ℤ)).map
          (hypercoverDoubleMap X J fg) ≫ (hypercoverCoefficientIso.{v} X J p q LG).hom =
      (hypercoverCoefficientIso.{v} X J p q KF).hom ≫ (pageTwoSmallSite J X p q).map fg := by
  have hnat : (HomologicalComplex₂.homologyIIHomologyIFunctor AddCommGrpCat.{v}
          (p : ℤ) (q : ℤ)).map (hypercoverDoubleMap X J fg) ≫
        (cechCoefficientNatIso.{v} X J p q).hom.app
          (LG.1, (injectiveResolution LG.2).cocomplex) =
      (cechCoefficientNatIso.{v} X J p q).hom.app
          (KF.1, (injectiveResolution KF.2).cocomplex) ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) p).map
          ((cechInnerBifunctor.{v} X J q).map
            (fg.1, InjectiveResolution.desc fg.2 (injectiveResolution LG.2)
              (injectiveResolution KF.2))) :=
    (cechCoefficientNatIso.{v} X J p q).hom.naturality _
  have hinner : (HomologicalComplex.homologyFunctor AddCommGrpCat.{v}
            (ComplexShape.up ℕ) p).map
          ((cechInnerBifunctor.{v} X J q).map
            (fg.1, InjectiveResolution.desc fg.2 (injectiveResolution LG.2)
              (injectiveResolution KF.2))) ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) p).map
          (innerCoefficientIso.{v} X J q LG).hom =
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) p).map
          (innerCoefficientIso.{v} X J q KF).hom ≫ (pageTwoSmallSite J X p q).map fg := by
    refine (map_comp_eq_map_comp _ (innerCoefficientIso_naturality.{v} X J q fg)).trans ?_
    rw [pageTwoSmallSite_map_eq.{v} X J p q fg]
    rfl
  rw [hypercoverCoefficientIso_hom, hypercoverCoefficientIso_hom]
  exact _root_.CategoryTheory.comp_paste₂ hnat hinner

/-- **[Stacks, Tag 0130] (6) for the hypercovering spectral sequence.** The second page of
`hypercoverE₂Functor` at `((p : ℤ), (q : ℤ))` is `H^p_{II}(H^q_I(A^{•,•}(K, F)))`. -/
def hypercoverPageTwoAppIso (p q : ℕ)
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v}) :
    (hypercoverE₂Functor X J ⋙
        CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
          HomologicalComplex.eval _ _ ((p : ℤ), (q : ℤ))).obj KF ≅
      (HomologicalComplex₂.homologyIIHomologyIFunctor AddCommGrpCat.{v} (p : ℤ) (q : ℤ)).obj
        (hypercoverDouble X J KF) :=
  HomologicalComplex₂.isoTwoPageTotalFiltration₂ (hypercoverDouble X J KF) _
    (HomologicalComplex₂.pageIso₂ _) (HomologicalComplex₂.exists_delta₂ _) (p : ℤ) (q : ℤ)

/-- `hypercoverPageTwoAppIso` is natural for the chosen morphisms `hypercoverDoubleMap` of double
complexes. This is `HomologicalComplex₂.pageTwoIso_naturality_of_homotopyClasses`, which is what
makes a second page functorial although the injective resolution it is built from is functorial
only up to homotopy. -/
lemma hypercoverPageTwoAppIso_naturality (p q : ℕ)
    {KF LG : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v}} (fg : KF ⟶ LG) :
    (hypercoverE₂Functor X J ⋙
          CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
            HomologicalComplex.eval _ _ ((p : ℤ), (q : ℤ))).map fg ≫
        (hypercoverPageTwoAppIso.{v} X J p q LG).hom =
      (hypercoverPageTwoAppIso.{v} X J p q KF).hom ≫
        (HomologicalComplex₂.homologyIIHomologyIFunctor AddCommGrpCat.{v} (p : ℤ) (q : ℤ)).map
          (hypercoverDoubleMap X J fg) :=
  HomologicalComplex₂.pageTwoIso_naturality_of_homotopyClasses (hypercoverDouble X J)
    (hypercoverDoubleMap X J) (filteredHomotopy₂_hypercoverDoubleMap_id X J)
    (fun f g => filteredHomotopy₂_hypercoverDoubleMap_comp X J f g) fg (p : ℤ) (q : ℤ)

/-- **The second page of the hypercovering spectral sequence on `ℤ × ℤ`**: at `((p : ℤ), (q : ℤ))`
it is `Ȟ^p(K, H^q(F))`, naturally in the simplicial semi-representable object and in the
coefficient sheaf simultaneously -- the spectral-sequence identification of [Stacks, Tag 0130] (6)
followed by the coefficient comparison. -/
def hypercoverPageTwoIsoInt (p q : ℕ) :
    hypercoverE₂Functor X J ⋙
        CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
          HomologicalComplex.eval _ _ ((p : ℤ), (q : ℤ)) ≅
      pageTwoSmallSite J X p q :=
  NatIso.ofComponents
    (fun KF => hypercoverPageTwoAppIso.{v} X J p q KF ≪≫
      hypercoverCoefficientIso.{v} X J p q KF)
    (fun fg => _root_.CategoryTheory.comp_paste₂
      (hypercoverPageTwoAppIso_naturality.{v} X J p q fg)
      (hypercoverCoefficientIso_naturality.{v} X J p q fg))

/-- **The second-page identification of clause (3) of [Stacks, Tag 01GY] for an arbitrary
simplicial semi-representable object**: the second page of
`Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverSpectralSequenceFunctor` at
`(p, q) : ℕ × ℕ` is
`Stacks.CategoryTheory.Hypercovering.pageTwoSmallSite`, i.e. `Ȟ^p(K, H^q(F))`, naturally in both
variables. The passage from `ℤ × ℤ` to `ℕ × ℕ` is on the nose, by
`CategoryTheory.SpectralSequence.natRestrictE₂Comp_pageTwoIso`. -/
def hypercoverPageTwoIso (p q : ℕ) :
    hypercoverSpectralSequenceFunctor X J ⋙
        CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
          HomologicalComplex.eval _ _ (p, q) ≅
      pageTwoSmallSite J X p q :=
  CategoryTheory.SpectralSequence.natRestrictE₂Comp_pageTwoIso (hypercoverE₂Functor X J)
      (isFirstQuadrant_hypercoverE₂Functor X J) p q ≪≫
    hypercoverPageTwoIsoInt.{v} X J p q

end Resolution

end SmallSite

section Hypercoverings

variable {C : Type v} [SmallCategory C] [HasPullbacks C] (X : C) (J : Pretopology C)

/-- **The second-page functor of clause (3) of [Stacks, Tag 01GY]**: `pageTwoSmallSite` restricted
to the full subcategory of hypercoverings of `X` for the pretopology `J`, which is the category
the assertion's spectral sequence is a functor on. -/
abbrev pageTwoHypercovering (p q : ℕ) :
    (HypercoveringCat X J)ᵒᵖ × Sheaf J.toGrothendieck AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v} :=
  (ObjectProperty.ι _).op.prod (𝟭 (Sheaf J.toGrothendieck AddCommGrpCat.{v})) ⋙
    pageTwoSmallSite J.toGrothendieck X p q

/-- **The `pageTwoIso` of clause (3) of [Stacks, Tag 01GY]**: the second page of
`Stacks.CategoryTheory.Hypercovering.Functorial.hypercoveringSpectralSequence` at `(p, q)` is
`Ȟ^p(K, H^q(F))`, naturally in the hypercovering and in the coefficient sheaf simultaneously.
It is `hypercoverPageTwoIso` restricted along the inclusion of the full subcategory of
hypercoverings, since nothing in the second-page identification uses the hypercovering
condition -- that is needed only for the abutment.

The source is written as the whiskering rather than as
`Stacks.CategoryTheory.Hypercovering.Functorial.hypercoveringSpectralSequence` composed with the
page
functor. The two are the same functor -- `hypercoveringSpectralSequence` *is* that whiskering,
and composition of functors is associative definitionally -- but checking that at the ambient
heartbeat budget means unfolding `CategoryTheory.SpectralSequence.natRestrictE₂Comp` inside a
functor-level defeq, which does not finish. -/
@[sga "4 V 7.4.0" "(7.4.0.3) E₂ page",
  sga "4 Vbis 2.5.6" "E_2 term"]
def hypercoveringPageTwoIso (p q : ℕ) :
    (ObjectProperty.ι (fun K : SimplicialObject (Limits.FormalCoproduct.{v} (Over X)) =>
            IsHypercovering J K)).op.prod
          (𝟭 (Sheaf J.toGrothendieck AddCommGrpCat.{v})) ⋙
        hypercoverSpectralSequenceFunctor X J.toGrothendieck ⋙
          CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
            HomologicalComplex.eval _ _ (p, q) ≅
      pageTwoHypercovering.{v} X J p q :=
  Functor.isoWhiskerLeft _ (hypercoverPageTwoIso.{v} X J.toGrothendieck p q)

end Hypercoverings

end Stacks.CategoryTheory.Hypercovering.Functorial

end
