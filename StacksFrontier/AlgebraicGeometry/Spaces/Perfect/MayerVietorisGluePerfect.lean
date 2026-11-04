module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisGlueingTag
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SquareDerivedIsoLocality

/-!
# Glueing perfect objects along an elementary distinguished square

Let `(U ⊆ W, j_V : V ⟶ W)` be an elementary distinguished square of algebraic spaces over a
scheme `S`, let `P = U ×_W V` be its intersection and write `(-)|_Y` for restriction of modules
along the étale morphism `j_Y : Y ⟶ W`.  This file reads the glueing lemma Stacks 08HB
(`AlgebraicGeometry.Space.exists_glued_object_and_hom`) on *perfect* objects:

* the glued object of a glueing datum of perfect objects is perfect, perfectness being local for
  the square (`AlgebraicGeometry.Space.isPerfect_of_isPerfect_edsRestrict`);
* the morphism out of a glued object produced by the second assertion of Stacks 08HB is an
  *isomorphism* as soon as the two morphisms it glues are, invertibility being local for the
  square (`AlgebraicGeometry.Space.isIso_of_isIso_derivedRestrict_eds`).

## Main results

* `AlgebraicGeometry.Space.exists_hom_of_glueData_eds`: the second assertion of Stacks 08HB for
  an *arbitrary* glueing datum on an elementary distinguished square, at the canonical extension
  by zero.  `AlgebraicGeometry.Space.exists_glued_object_and_hom` states it only for the glued
  object its first assertion produces.
* `AlgebraicGeometry.Space.isPerfect_of_isPerfect_glueData`: an object of `D(𝒪_W)` glueing a
  perfect object of `D(𝒪_U)` and a perfect object of `D(𝒪_V)` is perfect.
* `AlgebraicGeometry.Space.exists_iso_of_glueData_of_isIso`: **glueing an isomorphism.**  If a
  glued object `F` and an object `E` of `D(𝒪_W)` are compared by isomorphisms `A ≅ E|_U` and
  `Bo ≅ E|_V` which agree over `P` through the glueing isomorphism `c`, then `F ≅ E`.
* `AlgebraicGeometry.Space.exists_iso_of_restrictIso_eds`: the same at the canonical glueing datum:
  isomorphisms `F|_U ≅ E|_U` and `F|_V ≅ E|_V` whose two induced morphisms `F|_P ⟶ E|_P` agree glue
  to an isomorphism `F ≅ E`.
* `AlgebraicGeometry.Space.exists_glued_isPerfect_object_and_hom`: **Stacks 08HB for perfect
  objects, both assertions.**  A perfect object `A` of `D(𝒪_U)`, a perfect object `Bo` of
  `D(𝒪_V)` and an isomorphism `c : A|_P ≅ Bo|_P` are glued by a *perfect* object `F` of
  `D(𝒪_W)`, and morphisms from `A` and `Bo` into the restrictions of an object `K` of `D(𝒪_W)`
  agreeing over `P` are the two restrictions of one morphism `F ⟶ K`.
* `AlgebraicGeometry.Space.exists_glued_isPerfect_object_and_iso`: the same with the two
  morphisms taken to be isomorphisms, in which case the glued morphism is an isomorphism.

## References

* [Stacks Project, Lemma 75.10.8 (Tag 08HB)](https://stacks.math.columbia.edu/tag/08HB)
* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Lemma 75.9.3 (Tag 08GP)](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Definition 36.11.1 (Tag 0F8I)](https://stacks.math.columbia.edu/tag/0F8I)
* [Stacks Project, Tag 08GN](https://stacks.math.columbia.edu/tag/08GN)
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
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W : AlgebraicSpaces B S hS} {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : Ve ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

variable {A : DerivedCategory
    (Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2)}
  {Bo : DerivedCategory
    (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2)}

/-- **The second assertion of Stacks 08HB for an arbitrary glueing datum.**  Let
`(U ⊆ W, j_V : V ⟶ W)` be an elementary distinguished square with intersection `P = U ×_W V`,
let `F` be an object of `D(𝒪_W)` glueing an object `A` of `D(𝒪_U)` and an object `Bo` of
`D(𝒪_V)` along an isomorphism `c : A|_P ≅ Bo|_P` — that is, with isomorphisms `f : F|_U ≅ A`
and `g : F|_V ≅ Bo` satisfying `c = g|_P ∘ f^{-1}|_P`, which is the hypothesis `hc`.  Then for
every object `E` of `D(𝒪_W)` and all morphisms `a : A ⟶ E|_U` and `b : Bo ⟶ E|_V` with
`a|_P = b|_P ∘ c` there is a morphism `φ : F ⟶ E` restricting to `a ∘ f` on `U` and to `b ∘ g`
on `V`. -/
theorem exists_hom_of_glueData_eds
    (F E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
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
        (edsRestrictEtale B S hS hsq).mapDerivedCategory.map φ = g.hom ≫ b :=
  exists_hom_of_glueData_of_isElementaryDistinguishedSquare B S hS hsq
    (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq))
    F E f g c hc a b hab

/-- **An object glueing two perfect objects along an elementary distinguished square is
perfect.**  If `F|_U ≅ A` and `F|_V ≅ Bo` with `A` and `Bo` perfect, then `F` is perfect. -/
theorem isPerfect_of_isPerfect_glueData
    (F : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (f : (edsRestrictOpen B S hS hsq).mapDerivedCategory.obj F ≅ A)
    (g : (edsRestrictEtale B S hS hsq).mapDerivedCategory.obj F ≅ Bo)
    (hA : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1
      (edsOpen B S hS hsq).2).IsPerfect A)
    (hBo : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2).IsPerfect Bo) :
    (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect F := by
  refine isPerfect_of_isPerfect_edsRestrict B S hS hsq F ?_ ?_
  · exact RingedSite.IsPerfect.of_iso
      (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2) hA f.symm
  · exact RingedSite.IsPerfect.of_iso
      (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2) hBo g.symm

/-- **Glueing an isomorphism along an elementary distinguished square.**  Let `F` be an object of
`D(𝒪_W)` glueing `A` on `U` and `Bo` on `V` along `c : A|_P ≅ Bo|_P`, and let `E` be another
object of `D(𝒪_W)` carrying the *same* glueing datum: isomorphisms `a : A ≅ E|_U` and
`b : Bo ≅ E|_V` whose restrictions to `P` agree through `c`.  Then `F` and `E` are isomorphic,
by an isomorphism restricting to `a ∘ f` on `U` and to `b ∘ g` on `V`.

The morphism is the one the second assertion of Stacks 08HB produces
(`AlgebraicGeometry.Space.exists_hom_of_glueData_eds`); its two restrictions are composites of
isomorphisms, so it is an isomorphism by
`AlgebraicGeometry.Space.isIso_of_isIso_derivedRestrict_eds`. -/
theorem exists_iso_of_glueData_of_isIso
    (F E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (f : (edsRestrictOpen B S hS hsq).mapDerivedCategory.obj F ≅ A)
    (g : (edsRestrictEtale B S hS hsq).mapDerivedCategory.obj F ≅ Bo)
    (c : (edsRestrictFst B S hS hsq).mapDerivedCategory.obj A ≅
      (edsRestrictSnd B S hS hsq).mapDerivedCategory.obj Bo)
    (hc : c.hom = (edsRestrictFst B S hS hsq).mapDerivedCategory.map f.inv ≫
      (edsDerivedRestrictCompOpen B S hS hsq).hom.app F ≫
        (edsDerivedRestrictCompEtale B S hS hsq).inv.app F ≫
        (edsRestrictSnd B S hS hsq).mapDerivedCategory.map g.hom)
    (a : A ≅ (edsRestrictOpen B S hS hsq).mapDerivedCategory.obj E)
    (b : Bo ≅ (edsRestrictEtale B S hS hsq).mapDerivedCategory.obj E)
    (hab : (edsRestrictFst B S hS hsq).mapDerivedCategory.map a.hom ≫
        (edsDerivedRestrictCompOpen B S hS hsq).hom.app E =
      c.hom ≫ (edsRestrictSnd B S hS hsq).mapDerivedCategory.map b.hom ≫
        (edsDerivedRestrictCompEtale B S hS hsq).hom.app E) :
    ∃ e : F ≅ E,
      (edsRestrictOpen B S hS hsq).mapDerivedCategory.map e.hom = f.hom ≫ a.hom ∧
        (edsRestrictEtale B S hS hsq).mapDerivedCategory.map e.hom = g.hom ≫ b.hom := by
  obtain ⟨φ, hφU, hφV⟩ :=
    exists_hom_of_glueData_eds B S hS hsq F E f g c hc a.hom b.hom hab
  have hU : IsIso ((edsRestrictOpen B S hS hsq).mapDerivedCategory.map φ) := by
    rw [hφU]; infer_instance
  have hV : IsIso ((edsRestrictEtale B S hS hsq).mapDerivedCategory.map φ) := by
    rw [hφV]; infer_instance
  have : IsIso φ := isIso_of_isIso_derivedRestrict_eds B S hS hsq φ hU hV
  exact ⟨asIso φ, hφU, hφV⟩

/-- **Stacks 08HB for perfect objects, both assertions.**  Let `(U ⊆ W, j_V : V ⟶ W)` be an
elementary distinguished square of algebraic spaces over a scheme `S` with intersection
`P = U ×_W V`.  Let `A` be a perfect object of `D(𝒪_U)`, let `Bo` be a perfect object of
`D(𝒪_V)` and let `c : A|_P ≅ Bo|_P` be an isomorphism.  Then there are a **perfect** object `F`
of `D(𝒪_W)` and isomorphisms `f : F|_U ≅ A`, `g : F|_V ≅ Bo` with `c = g|_P ∘ f^{-1}|_P`; and
for every object `K` of `D(𝒪_W)` and all morphisms `a : A ⟶ K|_U` and `b : Bo ⟶ K|_V` with
`a|_P = b|_P ∘ c` there is a morphism `F ⟶ K` restricting to `a ∘ f` on `U` and to `b ∘ g` on
`V`.

This is `AlgebraicGeometry.Space.exists_glued_object_and_hom` with the perfectness of the glued
object added, which is the step the source's proof of the essential surjectivity half of
Stacks 09RJ takes at an elementary distinguished square: Stacks 08HB produces an object with a
morphism into the pushforward of the object being descended, and "one checks that it is
perfect".

The source's object `B` of `D(𝒪_V)` is written `Bo` here, the letter `B` being the big fppf
site. -/
theorem exists_glued_isPerfect_object_and_hom
    (A : DerivedCategory
      (Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2))
    (Bo : DerivedCategory
      (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hA : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1
      (edsOpen B S hS hsq).2).IsPerfect A)
    (hBo : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2).IsPerfect Bo)
    (c : (edsRestrictFst B S hS hsq).mapDerivedCategory.obj A ≅
      (edsRestrictSnd B S hS hsq).mapDerivedCategory.obj Bo) :
    ∃ (F : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
      (f : (edsRestrictOpen B S hS hsq).mapDerivedCategory.obj F ≅ A)
      (g : (edsRestrictEtale B S hS hsq).mapDerivedCategory.obj F ≅ Bo),
      (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect F ∧
        c.hom = (edsRestrictFst B S hS hsq).mapDerivedCategory.map f.inv ≫
          (edsDerivedRestrictCompOpen B S hS hsq).hom.app F ≫
            (edsDerivedRestrictCompEtale B S hS hsq).inv.app F ≫
            (edsRestrictSnd B S hS hsq).mapDerivedCategory.map g.hom ∧
        ∀ (K : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
          (a : A ⟶ (edsRestrictOpen B S hS hsq).mapDerivedCategory.obj K)
          (b : Bo ⟶ (edsRestrictEtale B S hS hsq).mapDerivedCategory.obj K),
          (edsRestrictFst B S hS hsq).mapDerivedCategory.map a ≫
              (edsDerivedRestrictCompOpen B S hS hsq).hom.app K =
            c.hom ≫ (edsRestrictSnd B S hS hsq).mapDerivedCategory.map b ≫
              (edsDerivedRestrictCompEtale B S hS hsq).hom.app K →
          ∃ φ : F ⟶ K,
            (edsRestrictOpen B S hS hsq).mapDerivedCategory.map φ = f.hom ≫ a ∧
              (edsRestrictEtale B S hS hsq).mapDerivedCategory.map φ = g.hom ≫ b := by
  obtain ⟨F, f, g, hc, huniv⟩ := exists_glued_object_and_hom B S hS hsq A Bo c
  exact ⟨F, f, g, isPerfect_of_isPerfect_glueData B S hS hsq F f g hA hBo, hc, huniv⟩

/-- **An isomorphism given on the two members of an elementary distinguished square and agreeing
on their intersection glues.**  Let `F` and `E` be objects of `D(𝒪_W)` and let
`a : F|_U ≅ E|_U` and `b : F|_V ≅ E|_V` be isomorphisms whose two induced morphisms
`F|_P ⟶ E|_P` agree, which is the hypothesis `hab`, written with the identifications
`AlgebraicGeometry.Space.edsDerivedRestrictCompOpen` and `…edsDerivedRestrictCompEtale` of the
iterated restrictions with the restriction to `P`.  Then there is an isomorphism `F ≅ E`
restricting to `a` on `U` and to `b` on `V`.

This is `AlgebraicGeometry.Space.exists_iso_of_glueData_of_isIso` at the canonical glueing datum
`A = F|_U`, `Bo = F|_V` with `f` and `g` the identities and `c` the canonical identification
`(F|_U)|_P ≅ F|_P ≅ (F|_V)|_P`, for which the hypothesis `hc` holds by construction.  It is the
form in which the elementary-distinguished-square step of Stacks 09RJ recognises the glued
comparison morphism as an isomorphism. -/
theorem exists_iso_of_restrictIso_eds
    (F E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (a : (edsRestrictOpen B S hS hsq).mapDerivedCategory.obj F ≅
      (edsRestrictOpen B S hS hsq).mapDerivedCategory.obj E)
    (b : (edsRestrictEtale B S hS hsq).mapDerivedCategory.obj F ≅
      (edsRestrictEtale B S hS hsq).mapDerivedCategory.obj E)
    (hab : (edsRestrictFst B S hS hsq).mapDerivedCategory.map a.hom ≫
        (edsDerivedRestrictCompOpen B S hS hsq).hom.app E =
      (edsDerivedRestrictCompOpen B S hS hsq).hom.app F ≫
        (edsDerivedRestrictCompEtale B S hS hsq).inv.app F ≫
        (edsRestrictSnd B S hS hsq).mapDerivedCategory.map b.hom ≫
          (edsDerivedRestrictCompEtale B S hS hsq).hom.app E) :
    ∃ e : F ≅ E,
      (edsRestrictOpen B S hS hsq).mapDerivedCategory.map e.hom = a.hom ∧
        (edsRestrictEtale B S hS hsq).mapDerivedCategory.map e.hom = b.hom := by
  obtain ⟨e, heU, heV⟩ := exists_iso_of_glueData_of_isIso B S hS hsq F E (Iso.refl _) (Iso.refl _)
    ((edsDerivedRestrictCompOpen B S hS hsq).app F ≪≫
      ((edsDerivedRestrictCompEtale B S hS hsq).app F).symm) (by simp) a b (by simpa using hab)
  exact ⟨e, by simpa using heU, by simpa using heV⟩

/-- **Stacks 08HB for perfect objects.**  Let `(U ⊆ W, j_V : V ⟶ W)` be an elementary
distinguished square of algebraic spaces over a scheme `S` with intersection `P = U ×_W V`.  Let
`A` be a perfect object of `D(𝒪_U)`, let `Bo` be a perfect object of `D(𝒪_V)` and let
`c : A|_P ≅ Bo|_P` be an isomorphism.  Then there are a **perfect** object `F` of `D(𝒪_W)` and
isomorphisms `f : F|_U ≅ A`, `g : F|_V ≅ Bo` with `c = g|_P ∘ f^{-1}|_P`, and moreover every
object `E` of `D(𝒪_W)` carrying the same glueing datum — isomorphisms `a : A ≅ E|_U` and
`b : Bo ≅ E|_V` agreeing over `P` through `c` — is isomorphic to `F` compatibly with `f`, `g`,
`a` and `b`.

This is the whole of what the elementary-distinguished-square step of the essential surjectivity
half of Stacks 09RJ asks of Stacks 08HB: the glued object, its perfectness, and the recognition
that the glued comparison is an isomorphism.

The source's object `B` of `D(𝒪_V)` is written `Bo` here, the letter `B` being the big fppf
site. -/
theorem exists_glued_isPerfect_object_and_iso
    (A : DerivedCategory
      (Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2))
    (Bo : DerivedCategory
      (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hA : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1
      (edsOpen B S hS hsq).2).IsPerfect A)
    (hBo : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2).IsPerfect Bo)
    (c : (edsRestrictFst B S hS hsq).mapDerivedCategory.obj A ≅
      (edsRestrictSnd B S hS hsq).mapDerivedCategory.obj Bo) :
    ∃ (F : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
      (f : (edsRestrictOpen B S hS hsq).mapDerivedCategory.obj F ≅ A)
      (g : (edsRestrictEtale B S hS hsq).mapDerivedCategory.obj F ≅ Bo),
      (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect F ∧
        c.hom = (edsRestrictFst B S hS hsq).mapDerivedCategory.map f.inv ≫
          (edsDerivedRestrictCompOpen B S hS hsq).hom.app F ≫
            (edsDerivedRestrictCompEtale B S hS hsq).inv.app F ≫
            (edsRestrictSnd B S hS hsq).mapDerivedCategory.map g.hom ∧
        ∀ (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
          (a : A ≅ (edsRestrictOpen B S hS hsq).mapDerivedCategory.obj E)
          (b : Bo ≅ (edsRestrictEtale B S hS hsq).mapDerivedCategory.obj E),
          (edsRestrictFst B S hS hsq).mapDerivedCategory.map a.hom ≫
              (edsDerivedRestrictCompOpen B S hS hsq).hom.app E =
            c.hom ≫ (edsRestrictSnd B S hS hsq).mapDerivedCategory.map b.hom ≫
              (edsDerivedRestrictCompEtale B S hS hsq).hom.app E →
          ∃ e : F ≅ E,
            (edsRestrictOpen B S hS hsq).mapDerivedCategory.map e.hom = f.hom ≫ a.hom ∧
              (edsRestrictEtale B S hS hsq).mapDerivedCategory.map e.hom = g.hom ≫ b.hom := by
  obtain ⟨F, f, g, hc, -⟩ := exists_glued_object_and_hom B S hS hsq A Bo c
  exact ⟨F, f, g, isPerfect_of_isPerfect_glueData B S hS hsq F f g hA hBo, hc,
    fun E a b hab => exists_iso_of_glueData_of_isIso B S hS hsq F E f g c hc a b hab⟩

end AlgebraicGeometry.Space

end
