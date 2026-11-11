module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisGlueMapComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisGlueObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisRestrictComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Both assertions of the glueing lemma on an elementary distinguished square

Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S`, let `P = U ×_X V` be its intersection and write `(-)|_Y` for restriction of modules
along the étale morphism `j_Y : Y ⟶ X`.  Stacks 08HB says that an object `A` of `D(𝒪_U)`, an
object `B` of `D(𝒪_V)` and an isomorphism `c : A|_P ⟶ B|_P` are glued by an object `F` of
`D(𝒪_X)` and isomorphisms `f : F|_U ⟶ A`, `g : F|_V ⟶ B` with `c = g|_P ∘ f^{-1}|_P`; and
moreover that morphisms `a : A ⟶ E|_U` and `b : B ⟶ E|_V` into the restrictions of an object
`E` of `D(𝒪_X)` with `a|_P = b|_P ∘ c` are the two restrictions of one morphism `F ⟶ E`.

The induced morphism comes from the Mayer–Vietoris distinguished triangle

`j_{P!}F|_P ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F ⟶ (j_{P!}F|_P)[1]`

of Stacks 08GV part (2), built here in the spelling the argument consumes: its first map the two
canonical comparisons `CategoryTheory.mayerVietorisGlueMap` and its second the sum of the
counits of the derived adjunctions.

## Main results

* `AlgebraicGeometry.Space.mem_distTriang_mayerVietorisGlueMap`: the Mayer–Vietoris
  distinguished triangle of an elementary distinguished square, with its first map the two
  canonical comparisons of the iterated restrictions and its second the sum of the counits of
  the derived adjunctions.
* `AlgebraicGeometry.Space.exists_hom_of_glueData_of_isElementaryDistinguishedSquare`: the
  induced morphism of Stacks 08HB, for a glued datum over an elementary distinguished square,
  with no hypothesis beyond the square.
* `AlgebraicGeometry.Space.exists_glued_object_and_hom`: **Stacks 08HB**, the glued object
  together with the induced morphism.

## Implementation notes

The triangle of Stacks 08GV part (2) differs from the one the glueing argument consumes in
three ways.  Its second map is the derived form of the degreewise counits, which
`CategoryTheory.Adjunction.derivedCounit_app` identifies with the counit of the derived
adjunction.  Its first map is the derived form of the module-level comparisons
`AlgebraicGeometry.Space.edsShriekOpenComparison` and `…edsShriekEtaleComparison`, which
`AlgebraicGeometry.Space.mapDerivedCategory_edsShriekOpenComparison_app` and its étale companion
identify with the canonical comparisons of the derived adjunctions; those comparisons are built
on the identification of iterated restriction with restriction to `P` coming from the
composition comparison of Stacks 03LU, which
`AlgebraicGeometry.Space.edsDerivedRestrictCompOpen_eq` and `…edsDerivedRestrictCompEtale_eq`
identify with the strict one.  Finally the first two objects of the two triangles are
comparison-isomorphic through `CategoryTheory.Functor.mapDerivedCategoryComp`, so the two
triangles are compared through `CategoryTheory.Pretriangulated.Triangle.isoMk`.

## References

* [Stacks Project, Tag 08HB](https://stacks.math.columbia.edu/tag/08HB)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 08H9](https://stacks.math.columbia.edu/tag/08H9)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

-- The universe-polymorphic `Abelian` instance of `Stacks.Cohomology.SiteModules`, imported with
-- `AlgebraicGeometry.Space.Modules` undetermined; the instance of Mathlib is the one used here.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W : AlgebraicSpaces B S hS} {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : Ve ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

section Data

variable [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {shriekU : Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekV : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekP : Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  [shriekU.Additive] [PreservesFiniteLimits shriekU] [PreservesFiniteColimits shriekU]
  [shriekV.Additive] [PreservesFiniteLimits shriekV] [PreservesFiniteColimits shriekV]
  [shriekP.Additive] [PreservesFiniteLimits shriekP] [PreservesFiniteColimits shriekP]


/-- **Stacks 08GV part (2) with the canonical first map and the derived counits.**  Let
`(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a scheme
`S`, let `P = U ×_X V`, write `(-)|_Y` for restriction of modules along `j_Y : Y ⟶ X` and let
`j_{Y!}` be a left adjoint of it, extension by zero.  Then every object `F` of `D(𝒪_X)` sits in
a distinguished triangle

`j_{P!}F|_P ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F ⟶ (j_{P!}F|_P)[1]`

whose first map is the pair of canonical comparisons `CategoryTheory.mayerVietorisGlueMap`,
taken with the strict identifications of the iterated restrictions with the restriction to `P`,
and whose second map is the sum of the counits of the derived adjunctions. -/
theorem mem_distTriang_mayerVietorisGlueMap (adjU : shriekU ⊣ edsRestrictOpen B S hS hsq)
    (adjV : shriekV ⊣ edsRestrictEtale B S hS hsq)
    (adjP : shriekP ⊣ edsRestrictInter B S hS hsq)
    (F : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ δ, Triangle.mk
        (biprod.lift
          (mayerVietorisGlueMap adjP.mapDerivedCategory adjU.mapDerivedCategory
            (edsDerivedRestrictCompOpen B S hS hsq) F)
          (-(mayerVietorisGlueMap adjP.mapDerivedCategory adjV.mapDerivedCategory
            (edsDerivedRestrictCompEtale B S hS hsq) F)))
        (biprod.desc (adjU.mapDerivedCategory.counit.app F)
          (adjV.mapDerivedCategory.counit.app F)) δ ∈
      distTriang (DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) := by
  obtain ⟨δ, hδ⟩ := mem_distTriang_mayerVietoris B S hS hsq adjU adjV
    (edsShriekOpenComparison B S hS hsq adjU adjP)
    (edsShriekEtaleComparison B S hS hsq adjV adjP)
    (zero_edsShriekMayerVietoris B S hS hsq adjU adjV adjP)
    (fun G => shortExact_edsShriekMayerVietoris B S hS hsq adjU adjV adjP G) F
  have hU := mapDerivedCategory_edsShriekOpenComparison_app B S hS hsq adjU adjP F
  have hV := mapDerivedCategory_edsShriekEtaleComparison_app B S hS hsq adjV adjP F
  rw [edsDerivedRestrictCompOpen_eq] at hU
  rw [edsDerivedRestrictCompEtale_eq] at hV
  simp only [NatTrans.comp_app] at hU hV
  refine ⟨δ ≫ ((Functor.mapDerivedCategoryComp (edsRestrictInter B S hS hsq)
      shriekP).hom.app F)⟦(1 : ℤ)⟧', isomorphic_distinguished _ hδ _ (Triangle.isoMk _ _
    ((Functor.mapDerivedCategoryComp (edsRestrictInter B S hS hsq) shriekP).app F).symm
    (biprod.mapIso
      ((Functor.mapDerivedCategoryComp (edsRestrictOpen B S hS hsq) shriekU).app F).symm
      ((Functor.mapDerivedCategoryComp (edsRestrictEtale B S hS hsq) shriekV).app F).symm)
    (Iso.refl F) ?_ ?_ ?_)⟩
  · refine biprod.hom_ext _ _ ?_ ?_
    · simp [← hU]
    · simp [← hV]
  · exact biprod.hom_ext' _ _ (by simp [Adjunction.derivedCounit_app])
      (by simp [Adjunction.derivedCounit_app])
  · simp

/-- **Stacks 08HB, the induced morphism.**  Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over a scheme `S`, let `P = U ×_X V`, write `(-)|_Y`
for restriction along `j_Y : Y ⟶ X` and let `j_{Y!}` be a left adjoint of it, extension by
zero.  Let `F` be an object of `D(𝒪_X)` glueing an object `A` of `D(𝒪_U)` and an object `Bo`
of `D(𝒪_V)` along an isomorphism `c : A|_P ⟶ Bo|_P`: isomorphisms `f : F|_U ⟶ A` and
`g : F|_V ⟶ Bo` with `c = g|_P ∘ f^{-1}|_P`, which is the hypothesis `hc` and is exactly what
`AlgebraicGeometry.Space.exists_glued_object` produces.  Then for every object `E` of `D(𝒪_X)`
and all morphisms `a : A ⟶ E|_U` and `b : Bo ⟶ E|_V` with `a|_P = b|_P ∘ c` there is a morphism
`φ : F ⟶ E` whose restriction to `U` is `a ∘ f` and whose restriction to `V` is `b ∘ g`.

The Mayer–Vietoris distinguished triangle

`j_{P!}F|_P ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F ⟶ (j_{P!}F|_P)[1]`

the argument runs over is `AlgebraicGeometry.Space.mem_distTriang_mayerVietorisGlueMap`, Stacks
08GV part (2) with its first map the canonical comparisons of the iterated restrictions and its
second the sum of the counits of the derived adjunctions.

The source's object `B` of `D(𝒪_V)` is written `Bo` here, the letter `B` being the big fppf
site. -/
theorem exists_hom_of_glueData_of_isElementaryDistinguishedSquare
    (adjU : shriekU ⊣ edsRestrictOpen B S hS hsq)
    (adjV : shriekV ⊣ edsRestrictEtale B S hS hsq)
    (adjP : shriekP ⊣ edsRestrictInter B S hS hsq)
    (F E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    {A : DerivedCategory
      (Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2)}
    {Bo : DerivedCategory
      (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2)}
    (f : (edsRestrictOpen B S hS hsq).mapDerivedCategory.obj F ≅ A)
    (g : (edsRestrictEtale B S hS hsq).mapDerivedCategory.obj F ≅ Bo)
    (c : (edsRestrictFst B S hS hsq).mapDerivedCategory.obj A ≅
      (edsRestrictSnd B S hS hsq).mapDerivedCategory.obj Bo)
    (hc : c.hom = (edsRestrictFst B S hS hsq).mapDerivedCategory.map f.inv ≫
      (edsDerivedRestrictCompOpen B S hS hsq).hom.app F ≫
        (edsDerivedRestrictCompEtale B S hS hsq).inv.app F ≫
        (edsRestrictSnd B S hS hsq).mapDerivedCategory.map g.hom)
    (a : A ⟶ (edsRestrictOpen B S hS hsq).mapDerivedCategory.obj E)
    (b : Bo ⟶ (edsRestrictEtale B S hS hsq).mapDerivedCategory.obj E)
    (hab : (edsRestrictFst B S hS hsq).mapDerivedCategory.map a ≫
        (edsDerivedRestrictCompOpen B S hS hsq).hom.app E =
      c.hom ≫ (edsRestrictSnd B S hS hsq).mapDerivedCategory.map b ≫
        (edsDerivedRestrictCompEtale B S hS hsq).hom.app E) :
    ∃ φ : F ⟶ E,
      (edsRestrictOpen B S hS hsq).mapDerivedCategory.map φ = f.hom ≫ a ∧
        (edsRestrictEtale B S hS hsq).mapDerivedCategory.map φ = g.hom ≫ b := by
  obtain ⟨δ, hT⟩ := mem_distTriang_mayerVietorisGlueMap B S hS hsq adjU adjV adjP F
  have hff : (edsRestrictFst B S hS hsq).mapDerivedCategory.map f.hom ≫
      (edsRestrictFst B S hS hsq).mapDerivedCategory.map f.inv = 𝟙 _ := by
    rw [← Functor.map_comp, f.hom_inv_id, CategoryTheory.Functor.map_id]
  refine exists_hom_of_restrictionPair adjP.mapDerivedCategory adjU.mapDerivedCategory
    adjV.mapDerivedCategory (edsDerivedRestrictCompOpen B S hS hsq)
    (edsDerivedRestrictCompEtale B S hS hsq) δ hT _ _ ?_
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [hab, hc]
  simp only [Category.assoc]
  rw [reassoc_of% hff]
  simp

end Data

section Canonical

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

/-- **Stacks 08HB.**  Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of
algebraic spaces over a scheme `S`, let `P = U ×_X V` be its intersection and write `(-)|_Y`
for restriction of modules along the étale morphism `j_Y : Y ⟶ X`.  Then an object `A` of
`D(𝒪_U)`, an object `Bo` of `D(𝒪_V)` and an isomorphism `c : A|_P ⟶ Bo|_P` are glued by an
object `F` of `D(𝒪_X)` together with isomorphisms `f : F|_U ⟶ A` and `g : F|_V ⟶ Bo`
satisfying `c = g|_P ∘ f^{-1}|_P`; and moreover, for every object `E` of `D(𝒪_X)` and all
morphisms `a : A ⟶ E|_U` and `b : Bo ⟶ E|_V` with `a|_P = b|_P ∘ c`, there is a morphism
`φ : F ⟶ E` restricting to `a ∘ f` on `U` and to `b ∘ g` on `V`.

The glued object is the source's own, the fibre of
`Rj_{U,*}A ⊕ Rj_{V,*}Bo ⟶ Rj_{P,*}(Bo|_P)`, built in
`AlgebraicGeometry.Space.exists_glued_object`; the induced morphism is
`AlgebraicGeometry.Space.exists_hom_of_glueData_of_isElementaryDistinguishedSquare` at the
canonical extension by zero, whose hypothesis `hc` is in exactly the shape the first conclusion
has.  The compatibility over `P` is written with the identifications
`AlgebraicGeometry.Space.edsDerivedRestrictCompOpen` and `…edsDerivedRestrictCompEtale` of the
iterated restrictions with the restriction to `P`, which the source writes silently.

The source's object `B` of `D(𝒪_V)` is written `Bo` here, the letter `B` being the big fppf
site. -/
@[stacks 08HB "both assertions, for an elementary distinguished square (U ⊆ X, j_V : V ⟶ X) of
algebraic spaces over a scheme S with intersection P = U ×_X V and nothing else bound: for an
object A of D(O_U), an object Bo of D(O_V) and an isomorphism c : A|_P ≅ Bo|_P, an object F of
D(O_X) with isomorphisms f : F|_U ≅ A and g : F|_V ≅ Bo satisfying c = g|_P ∘ f⁻¹|_P, and, for
every object E of D(O_X) and all morphisms a : A ⟶ E|_U and b : Bo ⟶ E|_V with
a|_P = b|_P ∘ c, a morphism φ : F ⟶ E whose restriction to U is a ∘ f and whose restriction to
V is b ∘ g. The compatibility over P is written with the identifications edsDerivedRestrictCompOpen
and edsDerivedRestrictCompEtale of the iterated restrictions with the restriction to P"]
theorem exists_glued_object_and_hom
    (A : DerivedCategory
      (Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2))
    (Bo : DerivedCategory
      (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (c : (edsRestrictFst B S hS hsq).mapDerivedCategory.obj A ≅
      (edsRestrictSnd B S hS hsq).mapDerivedCategory.obj Bo) :
    ∃ (F : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
      (f : (edsRestrictOpen B S hS hsq).mapDerivedCategory.obj F ≅ A)
      (g : (edsRestrictEtale B S hS hsq).mapDerivedCategory.obj F ≅ Bo),
      c.hom = (edsRestrictFst B S hS hsq).mapDerivedCategory.map f.inv ≫
          (edsDerivedRestrictCompOpen B S hS hsq).hom.app F ≫
            (edsDerivedRestrictCompEtale B S hS hsq).inv.app F ≫
            (edsRestrictSnd B S hS hsq).mapDerivedCategory.map g.hom ∧
        ∀ (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
          (a : A ⟶ (edsRestrictOpen B S hS hsq).mapDerivedCategory.obj E)
          (b : Bo ⟶ (edsRestrictEtale B S hS hsq).mapDerivedCategory.obj E),
          (edsRestrictFst B S hS hsq).mapDerivedCategory.map a ≫
              (edsDerivedRestrictCompOpen B S hS hsq).hom.app E =
            c.hom ≫ (edsRestrictSnd B S hS hsq).mapDerivedCategory.map b ≫
              (edsDerivedRestrictCompEtale B S hS hsq).hom.app E →
          ∃ φ : F ⟶ E,
            (edsRestrictOpen B S hS hsq).mapDerivedCategory.map φ = f.hom ≫ a ∧
              (edsRestrictEtale B S hS hsq).mapDerivedCategory.map φ = g.hom ≫ b := by
  obtain ⟨F, f, g, hc⟩ := exists_glued_object B S hS hsq A Bo c
  exact ⟨F, f, g, hc, fun E a b hab =>
    exists_hom_of_glueData_of_isElementaryDistinguishedSquare B S hS hsq
      (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq))
      (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq))
      (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq)) F E f g c hc a b hab⟩

end Canonical

end AlgebraicGeometry.Space

end
