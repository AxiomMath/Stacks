module

public import StacksFrontier.Homology.ExtendScalars.DerivedMonoidal

/-!
# The pentagon of the monoidality comparison of derived base change

Let `f : R → S` be a homomorphism of commutative rings and let
`β = - ⊗ᴸ_R S : D(R) ⥤ D(S)` be derived extension of scalars.  On K-flat representatives `β` is
monoidal: `CochainComplex.ExtendScalars.derivedMonoidalIso` compares `β (Q P ⊗ᴸ_R Q T)` with
`β (Q P) ⊗ᴸ_S β (Q T)`.  This file proves the one coherence of that comparison, the
Eilenberg--Kelly associativity law -- the pentagon -- at a triple of K-flat complexes.

The comparison is read here in the lax direction `β X ⊗ᴸ_S β Y ⟶ β (X ⊗ᴸ_R Y)`, which is the
inverse of `CochainComplex.ExtendScalars.derivedMonoidalIso` and the direction in which the
change-of-rings isomorphism of [stacks 0E1W] occurs with nothing inverted.

## The reduction

The pentagon has five factors on each side, and three of them on each side are K-flat comparisons.
What makes it provable is that the *whole* equation can be read through the comparison
isomorphisms of the derived tensor product over `S`, after which every factor is the class of a
chain map and the identity is the chain-level pentagon
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso_associativity`.

The reading is organized by the first half of this file, which is about an arbitrary
`CochainComplex.DerivedTensor.DerivedTensorProduct` and has nothing to do with base change: given
objects of `D(S)` presented as classes of K-flat complexes,
`CochainComplex.DerivedTensor.pairComparisonIso` and the two
`CochainComplex.DerivedTensor.tripleComparisonIsoLeft`,
`...tripleComparisonIsoRight` compare their derived tensor products with the classes of the total
tensor products of the representatives, and:

* `CochainComplex.DerivedTensor.derivedAssociatorIso_comp_tripleComparisonIsoRight` reads the
  canonical derived associator through those comparisons and finds the chain-level associator.
  This is `CochainComplex.DerivedTensor.derivedAssociatorIso_comparison` transported along
  isomorphisms of all three arguments, by naturality of the associator; it is the general form of
  the only property of the derived associator the pentagon uses.
* `CochainComplex.DerivedTensor.map_app_comp_pairComparisonIso` and
  `...obj_map_comp_pairComparisonIso` transport a morphism that is a comparison in disguise --- a
  `g` with `g ≫ d.hom = pairComparisonIso ≫ Q.map w` --- from a pair comparison to a triple
  comparison, in the first two and in the last two arguments respectively.  These are the two
  whiskerings of the pentagon.

Against those three lemmas the pentagon is the chain-level pentagon and nothing else; the only
input specific to base change is `derivedMonoidalMor_comp_kFlatComparisonIso`, which is
`CochainComplex.ExtendScalars.derivedMonoidalIso_comparison` solved for the lax structure map.

## Main definitions

* `CochainComplex.DerivedTensor.pairComparisonIso`,
  `CochainComplex.DerivedTensor.tripleComparisonIsoLeft`,
  `CochainComplex.DerivedTensor.tripleComparisonIsoRight`: the comparisons of iterated derived
  tensor products of classes of K-flat complexes with the classes of their total tensor products.
* `CochainComplex.ExtendScalars.derivedMonoidalMor`: the lax monoidal structure map of derived
  base change at a pair of K-flat complexes, with the class of `P ⊗ T` as its target.

## Main results

* `CochainComplex.DerivedTensor.derivedAssociatorIso_comp_tripleComparisonIsoRight`: the canonical
  derived associator, read through the triple comparisons, is the associator of total tensor
  products of complexes.
* `CochainComplex.ExtendScalars.derivedMonoidalMor_associativity`: **the pentagon**.
* `CochainComplex.ExtendScalars.derivedMonoidalIso_inv_associativity`: the same pentagon with the
  associator over `R` read as `CochainComplex.DerivedTensor.derivedAssociatorIso` rather than at
  chain level, which is the shape a coherence of `μ` is stated in.

## Implementation notes

The ring and module universes agree, as they must for
`CochainComplex.DerivedTensor.canonicalDerivedTensorProduct`, and the derived category is the
`HasDerivedCategory.standard` model, as in
`StacksFrontier.Homology.ExtendScalars.DerivedMonoidal` and
`StacksFrontier.Homology.Tor.DerivedTensor`.

`CochainComplex.ExtendScalars.kFlat_mapCochainComplex` restates
`CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars` with `mapCochainComplex` in its
conclusion.  The two are definitionally equal but not syntactically so, and an application of the
latter where K-flatness of a `mapCochainComplex` is wanted is ill-typed at `implicit`
transparency, which makes `rw` fail to see patterns that are present.

## References

* [The Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [The Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [The Stacks Project, Tag 0BYJ](https://stacks.math.columbia.edu/tag/0BYJ)
* [The Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CochainComplex.DerivedExtensionScalars CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CochainComplex.DerivedTensor

variable {S : Type u} [CommRing S] (T : DerivedTensorProduct S)

/-- Two objects of `D(S)` presented as classes of K-flat complexes: their derived tensor product
is compared with the class of the total tensor product of the representatives. -/
noncomputable def pairComparisonIso {A B : DObj S}
    (X Y : CochainComplex (ModuleCat.{u} S) ℤ) (hX : X.KFlat) (hY : Y.KFlat)
    (a : A ≅ DerivedCategory.Q.obj X) (b : B ≅ DerivedCategory.Q.obj Y) :
    (T.tensor.obj A).obj B ≅ DerivedCategory.Q.obj (X ⊗ Y) :=
  (T.tensor.obj A).mapIso b ≪≫ (T.tensor.mapIso a).app (DerivedCategory.Q.obj Y) ≪≫
    T.comparison X Y hX hY

/-- Three objects of `D(S)` presented as classes of K-flat complexes: the left-bracketed
derived triple product is compared with the class of the left-bracketed total triple product of
the representatives. -/
noncomputable def tripleComparisonIsoLeft {A B C : DObj S}
    (X Y Z : CochainComplex (ModuleCat.{u} S) ℤ) (hX : X.KFlat) (hY : Y.KFlat) (hZ : Z.KFlat)
    (a : A ≅ DerivedCategory.Q.obj X) (b : B ≅ DerivedCategory.Q.obj Y)
    (c : C ≅ DerivedCategory.Q.obj Z) :
    (T.tensor.obj ((T.tensor.obj A).obj B)).obj C ≅ DerivedCategory.Q.obj ((X ⊗ Y) ⊗ Z) :=
  (T.tensor.mapIso (pairComparisonIso T X Y hX hY a b)).app C ≪≫
    (T.tensor.obj (DerivedCategory.Q.obj (X ⊗ Y))).mapIso c ≪≫
    T.comparison (X ⊗ Y) Z (CochainComplex.KFlat.tensor S X Y hX hY) hZ

/-- Three objects of `D(S)` presented as classes of K-flat complexes: the right-bracketed
derived triple product is compared with the class of the right-bracketed total triple product of
the representatives. -/
noncomputable def tripleComparisonIsoRight {A B C : DObj S}
    (X Y Z : CochainComplex (ModuleCat.{u} S) ℤ) (hX : X.KFlat) (hY : Y.KFlat) (hZ : Z.KFlat)
    (a : A ≅ DerivedCategory.Q.obj X) (b : B ≅ DerivedCategory.Q.obj Y)
    (c : C ≅ DerivedCategory.Q.obj Z) :
    (T.tensor.obj A).obj ((T.tensor.obj B).obj C) ≅ DerivedCategory.Q.obj (X ⊗ Y ⊗ Z) :=
  (T.tensor.mapIso a).app ((T.tensor.obj B).obj C) ≪≫
    (T.tensor.obj (DerivedCategory.Q.obj X)).mapIso (pairComparisonIso T Y Z hY hZ b c) ≪≫
    T.comparison X (Y ⊗ Z) hX (CochainComplex.KFlat.tensor S Y Z hY hZ)

/-- The pair comparison, unfolded.  Stated so that it can be rewritten in one occurrence at a
time, which `dsimp only [pairComparisonIso]` cannot do. -/
private lemma pairComparisonIso_hom {A B : DObj S}
    (X Y : CochainComplex (ModuleCat.{u} S) ℤ) (hX : X.KFlat) (hY : Y.KFlat)
    (a : A ≅ DerivedCategory.Q.obj X) (b : B ≅ DerivedCategory.Q.obj Y) :
    (pairComparisonIso T X Y hX hY a b).hom =
      (T.tensor.obj A).map b.hom ≫ (T.tensor.map a.hom).app (DerivedCategory.Q.obj Y) ≫
        (T.comparison X Y hX hY).hom := rfl

/-- The left triple comparison, unfolded one step, with the pair comparison it is built from
left folded. -/
private lemma tripleComparisonIsoLeft_hom_pair {A B C : DObj S}
    (X Y Z : CochainComplex (ModuleCat.{u} S) ℤ) (hX : X.KFlat) (hY : Y.KFlat) (hZ : Z.KFlat)
    (a : A ≅ DerivedCategory.Q.obj X) (b : B ≅ DerivedCategory.Q.obj Y)
    (c : C ≅ DerivedCategory.Q.obj Z) :
    (tripleComparisonIsoLeft T X Y Z hX hY hZ a b c).hom =
      (T.tensor.map (pairComparisonIso T X Y hX hY a b).hom).app C ≫
        (T.tensor.obj (DerivedCategory.Q.obj (X ⊗ Y))).map c.hom ≫
        (T.comparison (X ⊗ Y) Z (CochainComplex.KFlat.tensor S X Y hX hY) hZ).hom := rfl

/-- The right triple comparison, unfolded one step, with the pair comparison it is built from
left folded. -/
private lemma tripleComparisonIsoRight_hom_pair {A B C : DObj S}
    (X Y Z : CochainComplex (ModuleCat.{u} S) ℤ) (hX : X.KFlat) (hY : Y.KFlat) (hZ : Z.KFlat)
    (a : A ≅ DerivedCategory.Q.obj X) (b : B ≅ DerivedCategory.Q.obj Y)
    (c : C ≅ DerivedCategory.Q.obj Z) :
    (tripleComparisonIsoRight T X Y Z hX hY hZ a b c).hom =
      (T.tensor.map a.hom).app ((T.tensor.obj B).obj C) ≫
        (T.tensor.obj (DerivedCategory.Q.obj X)).map
          (pairComparisonIso T Y Z hY hZ b c).hom ≫
        (T.comparison X (Y ⊗ Z) hX (CochainComplex.KFlat.tensor S Y Z hY hZ)).hom := rfl

/-- **Whiskering a comparison in disguise on the right.**  If `g : A ⊗ᴸ B ⟶ D` becomes the pair
comparison of `X` and `Y` followed by the class of a chain map `w : X ⊗ Y ⟶ W` when read through
`d : D ≅ Q W`, then `g` tensored with `C` on the right, followed by the pair comparison of `W` and
`Z`, is the left triple comparison followed by the class of `w ▷ Z`.

This is the left-hand whiskering of a lax monoidal comparison, for an arbitrary derived tensor
product and an arbitrary `g` with that property; it is naturality of the comparison of `T` in the
first variable together with naturality of `T.tensor` applied to `c`. -/
theorem map_app_comp_pairComparisonIso {A B C D : DObj S}
    (X Y Z W : CochainComplex (ModuleCat.{u} S) ℤ)
    (hX : X.KFlat) (hY : Y.KFlat) (hZ : Z.KFlat) (hW : W.KFlat)
    (a : A ≅ DerivedCategory.Q.obj X) (b : B ≅ DerivedCategory.Q.obj Y)
    (c : C ≅ DerivedCategory.Q.obj Z) (d : D ≅ DerivedCategory.Q.obj W)
    (g : (T.tensor.obj A).obj B ⟶ D) (w : X ⊗ Y ⟶ W)
    (hg : g ≫ d.hom = (pairComparisonIso T X Y hX hY a b).hom ≫ DerivedCategory.Q.map w) :
    (T.tensor.map g).app C ≫ (pairComparisonIso T W Z hW hZ d c).hom =
      (tripleComparisonIsoLeft T X Y Z hX hY hZ a b c).hom ≫
        DerivedCategory.Q.map (w ▷ Z) := by
  have hgd : (T.tensor.map g).app (DerivedCategory.Q.obj Z) ≫
      (T.tensor.map d.hom).app (DerivedCategory.Q.obj Z) =
      (T.tensor.map (pairComparisonIso T X Y hX hY a b).hom).app (DerivedCategory.Q.obj Z) ≫
        (T.tensor.map (DerivedCategory.Q.map w)).app (DerivedCategory.Q.obj Z) := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp, hg]
  have hcn := T.comparison_naturality w (𝟙 Z) (CochainComplex.KFlat.tensor S X Y hX hY) hW hZ hZ
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at hcn
  rw [pairComparisonIso_hom T W Z hW hZ d c, tripleComparisonIsoLeft_hom_pair,
    ← reassoc_of% ((T.tensor.map g).naturality c.hom), reassoc_of% hgd,
    reassoc_of% ((T.tensor.map (pairComparisonIso T X Y hX hY a b).hom).naturality c.hom), hcn,
    show HomologicalComplex.tensorHom w (𝟙 Z) = w ⊗ₘ (𝟙 Z) from rfl,
    MonoidalCategory.tensorHom_id]
  simp only [Category.assoc]

/-- **Whiskering a comparison in disguise on the left.**  If `g : B ⊗ᴸ C ⟶ D` becomes the pair
comparison of `Y` and `Z` followed by the class of a chain map `w : Y ⊗ Z ⟶ W` when read through
`d : D ≅ Q W`, then `A` tensored with `g` on the left, followed by the pair comparison of `X` and
`W`, is the right triple comparison followed by the class of `X ◁ w`.

This is the right-hand whiskering of a lax monoidal comparison; it is
`CochainComplex.DerivedTensor.map_app_comp_pairComparisonIso` in the other variable. -/
theorem obj_map_comp_pairComparisonIso {A B C D : DObj S}
    (X Y Z W : CochainComplex (ModuleCat.{u} S) ℤ)
    (hX : X.KFlat) (hY : Y.KFlat) (hZ : Z.KFlat) (hW : W.KFlat)
    (a : A ≅ DerivedCategory.Q.obj X) (b : B ≅ DerivedCategory.Q.obj Y)
    (c : C ≅ DerivedCategory.Q.obj Z) (d : D ≅ DerivedCategory.Q.obj W)
    (g : (T.tensor.obj B).obj C ⟶ D) (w : Y ⊗ Z ⟶ W)
    (hg : g ≫ d.hom = (pairComparisonIso T Y Z hY hZ b c).hom ≫ DerivedCategory.Q.map w) :
    (T.tensor.obj A).map g ≫ (pairComparisonIso T X W hX hW a d).hom =
      (tripleComparisonIsoRight T X Y Z hX hY hZ a b c).hom ≫
        DerivedCategory.Q.map (X ◁ w) := by
  have hcn := T.comparison_naturality (𝟙 X) w hX hX (CochainComplex.KFlat.tensor S Y Z hY hZ) hW
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at hcn
  rw [pairComparisonIso_hom T X W hX hW a d, tripleComparisonIsoRight_hom_pair,
    ← CategoryTheory.Functor.map_comp_assoc, hg, CategoryTheory.Functor.map_comp,
    Category.assoc, Category.assoc,
    reassoc_of% ((T.tensor.map a.hom).naturality (DerivedCategory.Q.map w)),
    reassoc_of% ((T.tensor.map a.hom).naturality (pairComparisonIso T Y Z hY hZ b c).hom),
    hcn, show HomologicalComplex.tensorHom (𝟙 X) w = (𝟙 X) ⊗ₘ w from rfl,
    MonoidalCategory.id_tensorHom]
  simp only [Category.assoc]

/-- The left triple comparison, split into the part that is naturality of the derived associator
along `(a, b, c)` and the part that is the comparison of `T` at the representatives. -/
private lemma tripleComparisonIsoLeft_hom {A B C : DObj S}
    (X Y Z : CochainComplex (ModuleCat.{u} S) ℤ) (hX : X.KFlat) (hY : Y.KFlat) (hZ : Z.KFlat)
    (a : A ≅ DerivedCategory.Q.obj X) (b : B ≅ DerivedCategory.Q.obj Y)
    (c : C ≅ DerivedCategory.Q.obj Z) :
    (tripleComparisonIsoLeft T X Y Z hX hY hZ a b c).hom =
      (T.tensor.map ((T.tensor.map a.hom).app B ≫
            (T.tensor.obj (DerivedCategory.Q.obj X)).map b.hom)).app C ≫
        (T.tensor.obj ((T.tensor.obj (DerivedCategory.Q.obj X)).obj
          (DerivedCategory.Q.obj Y))).map c.hom ≫
        (T.tensor.map (T.comparison X Y hX hY).hom).app (DerivedCategory.Q.obj Z) ≫
        (T.comparison (X ⊗ Y) Z (CochainComplex.KFlat.tensor S X Y hX hY) hZ).hom := by
  rw [tripleComparisonIsoLeft_hom_pair, pairComparisonIso_hom,
    reassoc_of% ((T.tensor.map a.hom).naturality b.hom), CategoryTheory.Functor.map_comp,
    NatTrans.comp_app, Category.assoc,
    reassoc_of% ((T.tensor.map (T.comparison X Y hX hY).hom).naturality c.hom)]
  simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc]

/-- The right triple comparison, split into the part that is naturality of the derived associator
along `(a, b, c)` and the part that is the comparison of `T` at the representatives. -/
private lemma tripleComparisonIsoRight_hom {A B C : DObj S}
    (X Y Z : CochainComplex (ModuleCat.{u} S) ℤ) (hX : X.KFlat) (hY : Y.KFlat) (hZ : Z.KFlat)
    (a : A ≅ DerivedCategory.Q.obj X) (b : B ≅ DerivedCategory.Q.obj Y)
    (c : C ≅ DerivedCategory.Q.obj Z) :
    (tripleComparisonIsoRight T X Y Z hX hY hZ a b c).hom =
      (T.tensor.map a.hom).app ((T.tensor.obj B).obj C) ≫
        (T.tensor.obj (DerivedCategory.Q.obj X)).map ((T.tensor.map b.hom).app C ≫
          (T.tensor.obj (DerivedCategory.Q.obj Y)).map c.hom) ≫
        (T.tensor.obj (DerivedCategory.Q.obj X)).map (T.comparison Y Z hY hZ).hom ≫
        (T.comparison X (Y ⊗ Z) hX (CochainComplex.KFlat.tensor S Y Z hY hZ)).hom := by
  rw [tripleComparisonIsoRight_hom_pair, pairComparisonIso_hom,
    reassoc_of% ((T.tensor.map b.hom).naturality c.hom)]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

/-- **The canonical derived associator, read through the triple comparisons at K-flat
representatives, is the associator of total tensor products of complexes.**

`CochainComplex.DerivedTensor.derivedAssociatorIso_comparison` says this for the three objects
`Q X`, `Q Y`, `Q Z` themselves; this says it for any three objects presented as classes of K-flat
complexes by isomorphisms `a`, `b`, `c`, the transport being naturality of
`CochainComplex.DerivedTensor.derivedAssociator` at the triple `(a.hom, b.hom, c.hom)`.

It is the only property of the derived associator that a coherence stated at K-flat
representatives needs, and the form in which it is needed: in such a coherence the three objects
are not the classes `Q X` but, say, their images under a functor. -/
theorem derivedAssociatorIso_comp_tripleComparisonIsoRight {A B C : DObj S}
    (X Y Z : CochainComplex (ModuleCat.{u} S) ℤ) (hX : X.KFlat) (hY : Y.KFlat) (hZ : Z.KFlat)
    (a : A ≅ DerivedCategory.Q.obj X) (b : B ≅ DerivedCategory.Q.obj Y)
    (c : C ≅ DerivedCategory.Q.obj Z) :
    (derivedAssociatorIso T A B C).hom ≫
        (tripleComparisonIsoRight T X Y Z hX hY hZ a b c).hom =
      (tripleComparisonIsoLeft T X Y Z hX hY hZ a b c).hom ≫
        DerivedCategory.Q.map (α_ X Y Z).hom := by
  rw [tripleComparisonIsoLeft_hom, tripleComparisonIsoRight_hom,
    show (α_ X Y Z).hom = (HomologicalComplex.associator X Y Z).hom from rfl,
    ← reassoc_of% (derivedAssociatorIso_naturality T a.hom b.hom c.hom),
    derivedAssociatorIso_comparison T X Y Z hX hY hZ]
  simp only [Category.assoc]

end CochainComplex.DerivedTensor

namespace CochainComplex.ExtendScalars

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Degreewise extension of scalars preserves K-flatness.  This is
`CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars`, restated with `mapCochainComplex` in
the conclusion: the two are definitionally equal, but only this spelling is type-correct where
K-flatness of a `mapCochainComplex` is required. -/
lemma kFlat_mapCochainComplex (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) :
    CochainComplex.KFlat.{u, u} ((mapCochainComplex f).obj P) :=
  CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f P hP

/-- **The lax monoidal structure map of derived base change at a pair of K-flat complexes.**
The inverse of `CochainComplex.ExtendScalars.derivedMonoidalIso`, followed by derived base change
of the K-flat comparison over `R`, so that its target is the derived base change of the class of
`P ⊗ T` rather than of the derived tensor product.

Written this way it is a K-flat comparison over `S` followed by the class of the degreewise
monoidality isomorphism, by
`CochainComplex.ExtendScalars.derivedMonoidalMor_comp_kFlatComparisonIso`:
every factor has a chain-level value, which is what makes its pentagon provable. -/
noncomputable def derivedMonoidalMor (P T : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) (hT : CochainComplex.KFlat.{u, u} T) :
    ((canonicalDerivedTensorProductFunctor S).obj
          ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
            (DerivedCategory.Q.obj P))).obj
        ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj (DerivedCategory.Q.obj T)) ⟶
      (derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj (DerivedCategory.Q.obj (P ⊗ T)) :=
  (derivedMonoidalIso f P T hP hT).inv ≫
    (derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
      ((canonicalDerivedTensorProduct R).comparison P T hP hT).hom

/-- **The lax structure map of derived base change, read through the K-flat comparisons, is the
degreewise monoidality isomorphism.**  This is
`CochainComplex.ExtendScalars.derivedMonoidalIso_comparison` solved for
`CochainComplex.ExtendScalars.derivedMonoidalMor`: the three comparisons that occur on the left
there are exactly `CochainComplex.DerivedTensor.pairComparisonIso` at the two K-flat comparisons
of derived base change, and what is left of the equation is the class of
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso`.

In the vocabulary of `CochainComplex.DerivedTensor.map_app_comp_pairComparisonIso` this says that
`derivedMonoidalMor` is a comparison in disguise, which is how the two whiskerings of the pentagon
are discharged. -/
lemma derivedMonoidalMor_comp_kFlatComparisonIso (P T : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) (hT : CochainComplex.KFlat.{u, u} T) :
    derivedMonoidalMor f P T hP hT ≫
        (kFlatComparisonIso f (P ⊗ T) (CochainComplex.KFlat.tensor R P T hP hT)).hom =
      (pairComparisonIso (canonicalDerivedTensorProduct S) ((mapCochainComplex f).obj P)
          ((mapCochainComplex f).obj T)
          (kFlat_mapCochainComplex f P hP) (kFlat_mapCochainComplex f T hT)
          (kFlatComparisonIso f P hP) (kFlatComparisonIso f T hT)).hom ≫
        DerivedCategory.Q.map (extendScalarsMonoidalIso f P T).hom := by
  have h := derivedMonoidalIso_comparison f P T hP hT
  simp only [derivedMonoidalMor, Category.assoc]
  rw [Iso.inv_comp_eq]
  dsimp only [pairComparisonIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  simp only [Category.assoc] at h ⊢
  rw [reassoc_of% h, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- **The pentagon of the monoidality comparison of derived base change, at a triple of K-flat
complexes.**  For K-flat `P`, `L`, `M` the lax monoidal structure map
`CochainComplex.ExtendScalars.derivedMonoidalMor` satisfies the Eilenberg--Kelly associativity
law: comparing the first two factors and then the result with the third, and finally
reassociating over `R` at chain level, agrees with reassociating over `S` first and then comparing
the last two factors and the first with the result.

This is the coherence of `CochainComplex.ExtendScalars.derivedMonoidalIso` --- the derived-level
counterpart of `CochainComplex.ExtendScalars.extendScalarsMonoidalIso_associativity`.

The associator over `R` appears here as the class of the chain-level associator rather than as
`CochainComplex.DerivedTensor.derivedAssociatorIso`. -/
theorem derivedMonoidalMor_associativity (P L M : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) (hL : CochainComplex.KFlat.{u, u} L)
    (hM : CochainComplex.KFlat.{u, u} M) :
    ((canonicalDerivedTensorProductFunctor S).map (derivedMonoidalMor f P L hP hL)).app
          ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
            (DerivedCategory.Q.obj M)) ≫
        derivedMonoidalMor f (P ⊗ L) M (CochainComplex.KFlat.tensor R P L hP hL) hM ≫
        (derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
          (DerivedCategory.Q.map (α_ P L M).hom) =
      (derivedAssociatorIso (canonicalDerivedTensorProduct S)
            ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj (DerivedCategory.Q.obj P))
            ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj (DerivedCategory.Q.obj L))
            ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
              (DerivedCategory.Q.obj M))).hom ≫
        ((canonicalDerivedTensorProductFunctor S).obj
            ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
              (DerivedCategory.Q.obj P))).map (derivedMonoidalMor f L M hL hM) ≫
        derivedMonoidalMor f P (L ⊗ M) hP (CochainComplex.KFlat.tensor R L M hL hM) := by
  rw [← Iso.cancel_iso_hom_right _ _ (kFlatComparisonIso f (P ⊗ L ⊗ M)
    (CochainComplex.KFlat.tensor R P (L ⊗ M) hP (CochainComplex.KFlat.tensor R L M hL hM)))]
  simp only [Category.assoc]
  rw [kFlatComparisonIso_naturality f
      (CochainComplex.KFlat.tensor R (P ⊗ L) M (CochainComplex.KFlat.tensor R P L hP hL) hM)
      (CochainComplex.KFlat.tensor R P (L ⊗ M) hP (CochainComplex.KFlat.tensor R L M hL hM))
      (α_ P L M).hom,
    reassoc_of% (derivedMonoidalMor_comp_kFlatComparisonIso f (P ⊗ L) M
      (CochainComplex.KFlat.tensor R P L hP hL) hM),
    reassoc_of% (map_app_comp_pairComparisonIso (canonicalDerivedTensorProduct S)
      ((mapCochainComplex f).obj P) ((mapCochainComplex f).obj L) ((mapCochainComplex f).obj M)
      ((mapCochainComplex f).obj (P ⊗ L)) _ _ _ _
      (kFlatComparisonIso f P hP) (kFlatComparisonIso f L hL) (kFlatComparisonIso f M hM)
      (kFlatComparisonIso f (P ⊗ L) (CochainComplex.KFlat.tensor R P L hP hL))
      (derivedMonoidalMor f P L hP hL) (extendScalarsMonoidalIso f P L).hom
      (derivedMonoidalMor_comp_kFlatComparisonIso f P L hP hL)),
    derivedMonoidalMor_comp_kFlatComparisonIso f P (L ⊗ M) hP
      (CochainComplex.KFlat.tensor R L M hL hM),
    reassoc_of% (obj_map_comp_pairComparisonIso (canonicalDerivedTensorProduct S)
      ((mapCochainComplex f).obj P) ((mapCochainComplex f).obj L) ((mapCochainComplex f).obj M)
      ((mapCochainComplex f).obj (L ⊗ M)) _ _ _ _
      (kFlatComparisonIso f P hP) (kFlatComparisonIso f L hL) (kFlatComparisonIso f M hM)
      (kFlatComparisonIso f (L ⊗ M) (CochainComplex.KFlat.tensor R L M hL hM))
      (derivedMonoidalMor f L M hL hM) (extendScalarsMonoidalIso f L M).hom
      (derivedMonoidalMor_comp_kFlatComparisonIso f L M hL hM)),
    reassoc_of% (derivedAssociatorIso_comp_tripleComparisonIsoRight
      (canonicalDerivedTensorProduct S) ((mapCochainComplex f).obj P)
      ((mapCochainComplex f).obj L) ((mapCochainComplex f).obj M) _ _ _
      (kFlatComparisonIso f P hP) (kFlatComparisonIso f L hL) (kFlatComparisonIso f M hM)),
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    extendScalarsMonoidalIso_associativity f P L M]

/-- **The pentagon with both associators read as derived associators.**  The same coherence as
`CochainComplex.ExtendScalars.derivedMonoidalMor_associativity`, with the structure map written as
the inverse of `CochainComplex.ExtendScalars.derivedMonoidalIso` and the associator over `R` as
`CochainComplex.DerivedTensor.derivedAssociatorIso`.

The two inner structure maps of a pentagon at `(Q P, Q L, Q M)` are needed at the pairs
`(Q P ⊗ᴸ_R Q L, Q M)` and `(Q P, Q L ⊗ᴸ_R Q M)`, whose first and second argument respectively is
not the class of a complex; `CochainComplex.ExtendScalars.derivedMonoidalIso` is therefore
conjugated by derived base change of the K-flat comparison over `R` in those two places.  That
conjugation and the chain-level reading of the associator over `R` cancel against each other, by
`CochainComplex.DerivedTensor.derivedAssociatorIso_comparison`, which is all this adds to
`derivedMonoidalMor_associativity`.

This is the shape a coherence of a lax monoidal structure map is stated in --- compare
`Dualizing.DerivedTensorBaseChangeAssoc`, whose reduction to K-flat representatives is
`Dualizing.derivedTensorBaseChangeAssoc_of_kFlat`. -/
theorem derivedMonoidalIso_inv_associativity (P L M : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) (hL : CochainComplex.KFlat.{u, u} L)
    (hM : CochainComplex.KFlat.{u, u} M) :
    ((canonicalDerivedTensorProductFunctor S).map
            (derivedMonoidalIso f P L hP hL).inv).app
          ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
            (DerivedCategory.Q.obj M)) ≫
        ((canonicalDerivedTensorProductFunctor S).map
            ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
              ((canonicalDerivedTensorProduct R).comparison P L hP hL).hom)).app
          ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
            (DerivedCategory.Q.obj M)) ≫
        (derivedMonoidalIso f (P ⊗ L) M (CochainComplex.KFlat.tensor R P L hP hL) hM).inv ≫
        (derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
          (((canonicalDerivedTensorProductFunctor R).map
            ((canonicalDerivedTensorProduct R).comparison P L hP hL).inv).app
              (DerivedCategory.Q.obj M)) ≫
        (derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
          (derivedAssociatorIso (canonicalDerivedTensorProduct R) (DerivedCategory.Q.obj P)
            (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)).hom =
      (derivedAssociatorIso (canonicalDerivedTensorProduct S)
            ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj (DerivedCategory.Q.obj P))
            ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj (DerivedCategory.Q.obj L))
            ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
              (DerivedCategory.Q.obj M))).hom ≫
        ((canonicalDerivedTensorProductFunctor S).obj
            ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
              (DerivedCategory.Q.obj P))).map (derivedMonoidalIso f L M hL hM).inv ≫
        ((canonicalDerivedTensorProductFunctor S).obj
            ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
              (DerivedCategory.Q.obj P))).map
          ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
            ((canonicalDerivedTensorProduct R).comparison L M hL hM).hom) ≫
        (derivedMonoidalIso f P (L ⊗ M) hP (CochainComplex.KFlat.tensor R L M hL hM)).inv ≫
        (derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
          (((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj P)).map
            ((canonicalDerivedTensorProduct R).comparison L M hL hM).inv) := by
  have hPL : CochainComplex.KFlat.{u, u} (P ⊗ L) := CochainComplex.KFlat.tensor R P L hP hL
  have hLM : CochainComplex.KFlat.{u, u} (L ⊗ M) := CochainComplex.KFlat.tensor R L M hL hM
  have h0 : ((canonicalDerivedTensorProductFunctor R).map
          ((canonicalDerivedTensorProduct R).comparison P L hP hL).inv).app
            (DerivedCategory.Q.obj M) ≫
        ((canonicalDerivedTensorProductFunctor R).map
          ((canonicalDerivedTensorProduct R).comparison P L hP hL).hom).app
            (DerivedCategory.Q.obj M) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, NatTrans.id_app]
  have h1 : ((canonicalDerivedTensorProductFunctor R).map
          ((canonicalDerivedTensorProduct R).comparison P L hP hL).inv).app
            (DerivedCategory.Q.obj M) ≫
        (derivedAssociatorIso (canonicalDerivedTensorProduct R) (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)).hom ≫
        ((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj P)).map
          ((canonicalDerivedTensorProduct R).comparison L M hL hM).hom ≫
        ((canonicalDerivedTensorProduct R).comparison P (L ⊗ M) hP hLM).hom =
      ((canonicalDerivedTensorProduct R).comparison (P ⊗ L) M hPL hM).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.associator P L M).hom := by
    rw [derivedAssociatorIso_comparison (canonicalDerivedTensorProduct R) P L M hP hL hM,
      reassoc_of% h0]
  have key := derivedMonoidalMor_associativity f P L M hP hL hM
  simp only [derivedMonoidalMor, CategoryTheory.Functor.map_comp, NatTrans.comp_app,
    Category.assoc] at key
  simp only [← CategoryTheory.Functor.map_comp] at key
  rw [← Iso.cancel_iso_hom_right _ _
      ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.mapIso
        (((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj P)).mapIso
          ((canonicalDerivedTensorProduct R).comparison L M hL hM))),
    ← Iso.cancel_iso_hom_right _ _
      ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.mapIso
        ((canonicalDerivedTensorProduct R).comparison P (L ⊗ M) hP hLM))]
  dsimp only [Functor.mapIso_hom]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp]
  rw [h1, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact key

end CochainComplex.ExtendScalars

end
