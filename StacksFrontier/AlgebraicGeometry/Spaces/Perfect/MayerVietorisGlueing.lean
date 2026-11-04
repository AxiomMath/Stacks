module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietoris
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompIsoEtaleRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Glueing morphisms out of a Mayer–Vietoris triangle on an elementary distinguished square

Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S`, let `P = U ×_X V` be its intersection, write `(-)|_Y` for restriction of modules
along the étale morphism `j_Y : Y ⟶ X` and `j_{Y!}` for a left adjoint of it, extension by
zero.  Stacks 08HB makes two assertions about objects `A` of `D(𝒪_U)`, `B` of `D(𝒪_V)` and an
isomorphism `c : A|_P ⟶ B|_P`: first that they are glued by an object `F` of `D(𝒪_X)` and
isomorphisms `f : F|_U ⟶ A`, `g : F|_V ⟶ B` with `c = g|_P ∘ f^{-1}|_P`, and second — the
"moreover" of the source — that morphisms `a : A ⟶ E|_U` and `b : B ⟶ E|_V` into the
restrictions of an object `E` of `D(𝒪_X)` with `a|_P = b|_P ∘ c` are induced by a morphism
`F ⟶ E`.

**Only the second assertion is proved here**, and the first is not: see the implementation
notes for what it needs and which of those inputs the library does not carry.  The second
assertion is the source's own deduction from the Mayer–Vietoris sequence for `Hom`, Stacks
08H9, and it is proved here directly from the Mayer–Vietoris distinguished triangle

`j_{P!}F|_P ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F ⟶ (j_{P!}F|_P)[1]`

of Stacks 08GV part (2), which enters as the hypothesis `hT`.

## Main definitions

* `CategoryTheory.mayerVietorisGlueMap` is the canonical first map
  `sh_P(r_P F) ⟶ sh_U(r_U F)` of a Mayer–Vietoris triangle: the morphism adjoint to the unit
  of `sh_U ⊣ r_U` read through an identification `r_U ⋙ r_{UP} ≅ r_P` of the iterated
  restriction with the restriction to the intersection.
* `AlgebraicGeometry.Space.etaleModulePullbackCongr` identifies the étale restrictions of
  modules along two equal morphisms.
* `AlgebraicGeometry.Space.edsRestrictOpen`, `…edsRestrictEtale`, `…edsRestrictInter`,
  `…edsRestrictFst` and `…edsRestrictSnd` are the five restriction functors of an elementary
  distinguished square, and `AlgebraicGeometry.Space.edsRestrictCompOpen`,
  `…edsRestrictCompEtale`, `…edsDerivedRestrictCompOpen` and `…edsDerivedRestrictCompEtale`
  are the two identifications of an iterated restriction with the restriction to the
  intersection, on modules and on unbounded derived categories.

## Main results

* `CategoryTheory.Adjunction.homEquiv_counit_comp`: the transpose of `counit ≫ φ` is the image
  of `φ` under the right adjoint.
* `CategoryTheory.homEquiv_mayerVietorisGlueMap_comp`: the transpose of
  `CategoryTheory.mayerVietorisGlueMap` against the transpose of a morphism
  `φ : r_U F ⟶ r_U E` is the restriction of `φ` to the intersection.  This is what turns the
  source's compatibility over `U ×_X V` into the vanishing that the triangle needs.
* `CategoryTheory.exists_hom_of_restrictionPair`: glueing a pair of morphisms along a
  Mayer–Vietoris triangle, in an arbitrary pretriangulated category with three adjunctions and
  the two identifications of iterated restrictions.
* `AlgebraicGeometry.Space.exists_hom_of_glueData`: **Stacks 08HB, the second assertion**, for
  an elementary distinguished square, granted a glued datum `(F, f, g)` and the Mayer–Vietoris
  distinguished triangle of Stacks 08GV part (2) at `F`.

## Implementation notes

*The compatibility over the intersection is in the conclusion, through the hypotheses.*  The
source's `c = g|_P ∘ f^{-1}|_P` and `a|_P = b|_P ∘ c` are the hypotheses `hc` and `hab` of
`AlgebraicGeometry.Space.exists_hom_of_glueData`, written with the two *constructed*
identifications `AlgebraicGeometry.Space.edsDerivedRestrictCompOpen` and
`…edsDerivedRestrictCompEtale` of the two iterated restrictions with the restriction to the
intersection; the source writes them silently.  Both are used: `hab` and `hc` together are
exactly what makes the pair `(a ∘ f, b ∘ g)` agree over `P`, which is the hypothesis `hagree`
of `CategoryTheory.exists_hom_of_restrictionPair`, and that agreement is what makes the pair
annihilate the first map of the triangle.  Without it the pair would not glue.

*Why the triangle is a hypothesis, and why the library's Stacks 08GV part (2) does not supply
it.*  `AlgebraicGeometry.Space.mem_distTriang_mayerVietoris` is stated for *arbitrary* natural
transformations `a`, `b` out of `j_{P!}((-)|_P)` constrained only by the short exactness of
part (1), and its second map is the derived transformation of the degreewise counits read
through `CategoryTheory.Functor.mapDerivedCategoryIdIso`.  The deduction here needs the two
maps to be the canonical ones — the transposes of the restriction comparisons, that is
`CategoryTheory.mayerVietorisGlueMap` — and the second map to be the counit of the derived
adjunction `CategoryTheory.Adjunction.mapDerivedCategory`, because that is what the adjunction
computation identifies with restriction of morphisms.  Nothing about arbitrary `a` and `b` can
produce the source's compatibility over `P`, so the triangle in its canonical spelling is the
named hypothesis `hT`.  It is Stacks 08GV part (2), which the source reaches through Stacks
08H9; part (1) of Stacks 08GV is itself a gap of the library, recorded as the hypothesis `hMV`
of `AlgebraicGeometry.Space.mem_distTriang_mayerVietoris`.

*Where the elementary distinguished square is used.*  The hypothesis `hsq` supplies the open
subspace, the étale algebraic space, the intersection and the five étale morphisms between
them, and — through `AlgebraicGeometry.Space.isPullback_edsInter` — that the intersection
really is `U ×_X V`, which is what
`AlgebraicGeometry.Space.edsRestrictCompEtale` needs in order to identify restriction through
`V` with restriction along `j_P`.  The *defining* condition of an elementary distinguished
square, that `j_V` induces an isomorphism over `|X| \ |U|`, is used only through `hT`: it is
what makes part (1) of Stacks 08GV true.  This is the same division of labour as in the
source, whose proof of the "moreover" part invokes nothing but Stacks 08H9.

*Extension by zero enters as data*, as in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/MayerVietoris.lean` and in Stacks 08HA: a
functor together with an adjunction exhibiting it as a left adjoint of restriction pins both
the functor and the counit `j_{Y!}(F|_Y) ⟶ F` up to a unique compatible isomorphism, and its
exactness — Stacks 03DJ — is carried by the instance arguments, which is what makes the
derived adjunction `CategoryTheory.Adjunction.mapDerivedCategory` available.

*What the first assertion needs and what is missing.*  The source builds `F` as the fibre of
`Rj_{U,*}A ⊕ Rj_{V,*}B ⟶ Rj_{U ×_X V,*}(B|_P)`, shows `F|_U ⟶ A` is an isomorphism using
Stacks 08GE, and then shows `F|_V ⟶ B` is an isomorphism by placing its cone `B'` in the
morphism of Mayer–Vietoris direct-image triangles, concluding `Rj_{V,*}B' = 0` by Stacks 014A
and then `B' = 0` by Stacks 08GG.  Three of those inputs are unavailable here.  Stacks 08GG
clauses (2)(a) and (2)(b) — the ones that turn `Rj_{V,*}B' = 0` into `B' = 0` — are *not*
proved by `StacksFrontier/AlgebraicGeometry/Spaces/Perfect/SupportedOnComplement.lean`, which
carries only clauses (1)(a), (1)(b) and (2)(c); their proof needs the base change of the
square along `j_V`, that is Stacks 08GN.  Stacks 08GW part (2), the direct-image triangle, is
available only in the existentially quantified form
`AlgebraicGeometry.Space.exists_mem_distTriang_edsDerivedRestrictPushMayerVietoris`, whose
maps are not exposed, so the morphism of triangles cannot be written down.  And the statement
that `B'` is supported on `j_V^{-1}(|X| \ |U|)` needs the commutation of derived restriction
with the cohomology sheaves, the gap recorded in the implementation notes of that same file.
So no attribute is placed for the first assertion.

## References

* [Stacks Project, Tag 08HB](https://stacks.math.columbia.edu/tag/08HB)
* [Stacks Project, Tag 08H9](https://stacks.math.columbia.edu/tag/08H9)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 08GE](https://stacks.math.columbia.edu/tag/08GE)
* [Stacks Project, Tag 08GG](https://stacks.math.columbia.edu/tag/08GG)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
* [Stacks Project, Tag 014A](https://stacks.math.columbia.edu/tag/014A)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

namespace CategoryTheory

section GlueMap

variable {DX : Type u₁} [Category.{v₁} DX] {DU : Type u₂} [Category.{v₂} DU]
  {DP : Type u₄} [Category.{v₄} DP]
  {rU : DX ⥤ DU} {shU : DU ⥤ DX} {rP : DX ⥤ DP} {shP : DP ⥤ DX} {rUP : DU ⥤ DP}

/-- The transpose of a morphism `F ⟶ E` under an adjunction `sh ⊣ r`, computed on the
composite of the counit with that morphism, is the image of the morphism under `r`. -/
theorem Adjunction.homEquiv_counit_comp (adj : shU ⊣ rU) {F E : DX} (φ : F ⟶ E) :
    adj.homEquiv _ _ (adj.counit.app F ≫ φ) = rU.map φ := by
  rw [adj.homEquiv_naturality_right, Adjunction.homEquiv_unit,
    Adjunction.right_triangle_components, Category.id_comp]

/-- **The canonical first map of a Mayer–Vietoris triangle.**  Given adjunctions `sh_P ⊣ r_P`
and `sh_U ⊣ r_U` and an identification `cmp : r_U ⋙ r_{UP} ≅ r_P` of the iterated restriction
with the restriction to the intersection, this is the morphism `sh_P(r_P F) ⟶ sh_U(r_U F)`
adjoint to the canonical map `r_P F ⟶ r_P (sh_U (r_U F))` obtained from the unit of
`sh_U ⊣ r_U` read through `cmp`. -/
def mayerVietorisGlueMap (adjP : shP ⊣ rP) (adjU : shU ⊣ rU) (cmp : rU ⋙ rUP ≅ rP) (F : DX) :
    shP.obj (rP.obj F) ⟶ shU.obj (rU.obj F) :=
  (adjP.homEquiv _ _).symm
    (cmp.inv.app F ≫ rUP.map (adjU.unit.app (rU.obj F)) ≫ cmp.hom.app (shU.obj (rU.obj F)))

/-- **The transpose of the canonical Mayer–Vietoris map against a restricted morphism is the
restriction of that morphism to the intersection.**  For `φ : r_U F ⟶ r_U E` the composite of
`CategoryTheory.mayerVietorisGlueMap` with the transpose of `φ` has, as its own transpose
under `sh_P ⊣ r_P`, the morphism `r_P F ⟶ r_P E` obtained from `r_{UP} φ` through `cmp`. -/
theorem homEquiv_mayerVietorisGlueMap_comp (adjP : shP ⊣ rP) (adjU : shU ⊣ rU)
    (cmp : rU ⋙ rUP ≅ rP) {F E : DX} (φ : rU.obj F ⟶ rU.obj E) :
    adjP.homEquiv _ _ (mayerVietorisGlueMap adjP adjU cmp F ≫
        (adjU.homEquiv _ _).symm φ) =
      cmp.inv.app F ≫ rUP.map φ ≫ cmp.hom.app E := by
  have e1 : cmp.hom.app (shU.obj (rU.obj F)) ≫ rP.map (shU.map φ) =
      rUP.map (rU.map (shU.map φ)) ≫ cmp.hom.app (shU.obj (rU.obj E)) :=
    (cmp.hom.naturality (shU.map φ)).symm
  have e2 : cmp.hom.app (shU.obj (rU.obj E)) ≫ rP.map (adjU.counit.app E) =
      rUP.map (rU.map (adjU.counit.app E)) ≫ cmp.hom.app E :=
    (cmp.hom.naturality (adjU.counit.app E)).symm
  have e3 : adjU.unit.app (rU.obj F) ≫ rU.map (shU.map φ) =
      φ ≫ adjU.unit.app (rU.obj E) := by
    have h := adjU.unit.naturality φ
    simp only [Functor.id_map, Functor.comp_map] at h
    exact h.symm
  have e4 : adjU.unit.app (rU.obj E) ≫ rU.map (adjU.counit.app E) = 𝟙 (rU.obj E) :=
    adjU.right_triangle_components E
  rw [Adjunction.homEquiv_counit, adjP.homEquiv_naturality_right, mayerVietorisGlueMap,
    Equiv.apply_symm_apply, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% e1, ← Functor.map_comp_assoc, e3, Functor.map_comp_assoc, e2,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, e4,
    Category.comp_id]

/-- A morphism whose composite with the counit is the transpose of `ψ` restricts to `ψ`. -/
private theorem map_eq_of_counit_comp_eq (adj : shU ⊣ rU) {F E : DX} (φ : F ⟶ E)
    (ψ : rU.obj F ⟶ rU.obj E) (h : (adj.homEquiv _ _).symm ψ = adj.counit.app F ≫ φ) :
    rU.map φ = ψ := by
  simpa [Adjunction.homEquiv_counit_comp] using congrArg (adj.homEquiv _ _) h.symm

end GlueMap

section Glue

variable {DX : Type u₁} [Category.{v₁} DX] [Preadditive DX] [HasZeroObject DX]
  [HasShift DX ℤ] [∀ n : ℤ, (shiftFunctor DX n).Additive] [Pretriangulated DX]
  {DU : Type u₂} [Category.{v₂} DU] {DV : Type u₃} [Category.{v₃} DV]
  {DP : Type u₄} [Category.{v₄} DP]
  {rU : DX ⥤ DU} {shU : DU ⥤ DX} {rV : DX ⥤ DV} {shV : DV ⥤ DX}
  {rP : DX ⥤ DP} {shP : DP ⥤ DX} {rUP : DU ⥤ DP} {rVP : DV ⥤ DP}

/-- **Glueing a pair of morphisms along a Mayer–Vietoris triangle.**  Let `sh_Y ⊣ r_Y` be
adjunctions for `Y = U, V, P`, let `cmp_U : r_U ⋙ r_{UP} ≅ r_P` and
`cmp_V : r_V ⋙ r_{VP} ≅ r_P` identify the two iterated restrictions with the restriction to
the intersection, and suppose

`sh_P(r_P F) ⟶ sh_U(r_U F) ⊕ sh_V(r_V F) ⟶ F ⟶ (sh_P(r_P F))[1]`

is a distinguished triangle whose first map is `(α_U, -α_V)` for the canonical maps
`CategoryTheory.mayerVietorisGlueMap` and whose second is the sum of the two counits.  Then a
pair of morphisms `φ_U : r_U F ⟶ r_U E` and `φ_V : r_V F ⟶ r_V E` whose restrictions to the
intersection agree is the pair of restrictions of a morphism `F ⟶ E`. -/
theorem exists_hom_of_restrictionPair (adjP : shP ⊣ rP) (adjU : shU ⊣ rU) (adjV : shV ⊣ rV)
    (cmpU : rU ⋙ rUP ≅ rP) (cmpV : rV ⋙ rVP ≅ rP) {F E : DX}
    [HasBinaryBiproduct (shU.obj (rU.obj F)) (shV.obj (rV.obj F))]
    (δ : F ⟶ (shP.obj (rP.obj F))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk
        (biprod.lift (mayerVietorisGlueMap adjP adjU cmpU F)
          (-(mayerVietorisGlueMap adjP adjV cmpV F)))
        (biprod.desc (adjU.counit.app F) (adjV.counit.app F)) δ ∈ distTriang DX)
    (φU : rU.obj F ⟶ rU.obj E) (φV : rV.obj F ⟶ rV.obj E)
    (hagree : cmpU.inv.app F ≫ rUP.map φU ≫ cmpU.hom.app E =
      cmpV.inv.app F ≫ rVP.map φV ≫ cmpV.hom.app E) :
    ∃ φ : F ⟶ E, rU.map φ = φU ∧ rV.map φ = φV := by
  have hzero : biprod.lift (mayerVietorisGlueMap adjP adjU cmpU F)
        (-(mayerVietorisGlueMap adjP adjV cmpV F)) ≫
      biprod.desc ((adjU.homEquiv _ _).symm φU) ((adjV.homEquiv _ _).symm φV) = 0 := by
    rw [biprod.lift_desc, Preadditive.neg_comp, ← sub_eq_add_neg, sub_eq_zero]
    exact (adjP.homEquiv _ _).injective
      ((homEquiv_mayerVietorisGlueMap_comp adjP adjU cmpU φU).trans
        (hagree.trans (homEquiv_mayerVietorisGlueMap_comp adjP adjV cmpV φV).symm))
  obtain ⟨φ, hφ⟩ := Triangle.yoneda_exact₂ _ hT _ hzero
  exact ⟨φ, map_eq_of_counit_comp_eq adjU φ φU (by simpa using congrArg (biprod.inl ≫ ·) hφ),
    map_eq_of_counit_comp_eq adjV φ φV (by simpa using congrArg (biprod.inr ≫ ·) hφ)⟩

end Glue

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Étale restriction of modules along two equal morphisms agrees. -/
def etaleModulePullbackCongr {X Y : AlgebraicSpaces B S hS} {f g : X ⟶ Y}
    (hf : IsEtale B S hS f.hom) (hg : IsEtale B S hS g.hom) (h : f = g) :
    etaleModulePullback.{u, u} B S hS f hf ≅ etaleModulePullback.{u, u} B S hS g hg := by
  subst h
  exact Iso.refl _

section Square

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable {W : AlgebraicSpaces B S hS} {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : Ve ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- Restriction of modules from the ambient space of an elementary distinguished square to its
open subspace. -/
abbrev edsRestrictOpen :=
  etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)

/-- Restriction of modules from the ambient space of an elementary distinguished square to its
étale algebraic space. -/
abbrev edsRestrictEtale :=
  etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)

/-- Restriction of modules from the ambient space of an elementary distinguished square to its
intersection `U ×_X V`. -/
abbrev edsRestrictInter :=
  etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq)

/-- Restriction of modules from the open subspace of an elementary distinguished square to its
intersection `U ×_X V`, along the first projection. -/
abbrev edsRestrictFst :=
  etaleModulePullback.{u, u} B S hS (edsFst B S hS hsq) (isEtale_edsFst B S hS hsq)

/-- Restriction of modules from the étale algebraic space of an elementary distinguished square
to its intersection `U ×_X V`, along the second projection. -/
abbrev edsRestrictSnd :=
  etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)

/-- Restricting a sheaf of modules to the open subspace of an elementary distinguished square
and then to the intersection is restricting it to the intersection. -/
def edsRestrictCompOpen :
    edsRestrictOpen B S hS hsq ⋙ edsRestrictFst B S hS hsq ≅ edsRestrictInter B S hS hsq :=
  etaleModulePullbackComp B S hS (edsFst B S hS hsq) (edsOpenHom B S hS hsq)
    (isEtale_edsFst B S hS hsq) (isEtale_edsOpenHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq)

/-- Restricting a sheaf of modules to the étale algebraic space of an elementary distinguished
square and then to the intersection is restricting it to the intersection.  This uses that the
square commutes. -/
def edsRestrictCompEtale :
    edsRestrictEtale B S hS hsq ⋙ edsRestrictSnd B S hS hsq ≅ edsRestrictInter B S hS hsq :=
  etaleModulePullbackComp B S hS (edsSnd B S hS hsq) (edsEtaleHom B S hS hsq)
      (isEtale_edsSnd B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
      (isEtale_comp B S hS (isEtale_edsSnd B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)) ≪≫
    etaleModulePullbackCongr B S hS
      (isEtale_comp B S hS (isEtale_edsSnd B S hS hsq) (isEtale_edsEtaleHom B S hS hsq))
      (isEtale_edsInterHom B S hS hsq) (isPullback_edsInter B S hS hsq).w.symm

/-- The derived form of `AlgebraicGeometry.Space.edsRestrictCompOpen`: on unbounded derived
categories, restricting to the open subspace and then to the intersection is restricting to the
intersection. -/
def edsDerivedRestrictCompOpen :
    (edsRestrictOpen B S hS hsq).mapDerivedCategory ⋙
        (edsRestrictFst B S hS hsq).mapDerivedCategory ≅
      (edsRestrictInter B S hS hsq).mapDerivedCategory :=
  (Functor.mapDerivedCategoryComp (edsRestrictOpen B S hS hsq)
      (edsRestrictFst B S hS hsq)).symm ≪≫
    asIso (NatTrans.mapDerivedCategory (edsRestrictCompOpen B S hS hsq).hom)

/-- The derived form of `AlgebraicGeometry.Space.edsRestrictCompEtale`: on unbounded derived
categories, restricting to the étale algebraic space and then to the intersection is restricting
to the intersection. -/
def edsDerivedRestrictCompEtale :
    (edsRestrictEtale B S hS hsq).mapDerivedCategory ⋙
        (edsRestrictSnd B S hS hsq).mapDerivedCategory ≅
      (edsRestrictInter B S hS hsq).mapDerivedCategory :=
  (Functor.mapDerivedCategoryComp (edsRestrictEtale B S hS hsq)
      (edsRestrictSnd B S hS hsq)).symm ≪≫
    asIso (NatTrans.mapDerivedCategory (edsRestrictCompEtale B S hS hsq).hom)

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

/-- **Stacks 08HB, the second assertion**, granted the Mayer–Vietoris distinguished triangle of
Stacks 08GV part (2).  Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of
algebraic spaces over a scheme `S`, let `P = U ×_X V`, write `(-)|_Y` for restriction along
`j_Y : Y ⟶ X` and let `j_{Y!}` be a left adjoint of it, extension by zero.  Let `F` be an
object of `D(𝒪_X)` glueing an object `A` of `D(𝒪_U)` and an object `Bo` of `D(𝒪_V)` along an
isomorphism `c : A|_P ⟶ Bo|_P`: isomorphisms `f : F|_U ⟶ A` and `g : F|_V ⟶ Bo` with
`c = g|_P ∘ f^{-1}|_P`, which is the hypothesis `hc`.  Suppose `F` sits in the Mayer–Vietoris
distinguished triangle

`j_{P!}F|_P ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F ⟶ (j_{P!}F|_P)[1]`

of Stacks 08GV part (2), whose second map is the sum of the two counits and whose first map is
built from the canonical comparisons of the iterated restrictions; this is the hypothesis `hT`.
Then for every object `E` of `D(𝒪_X)` and all morphisms `a : A ⟶ E|_U` and `b : Bo ⟶ E|_V` with
`a|_P = b|_P ∘ c` there is a morphism `φ : F ⟶ E` whose restriction to `U` is `a ∘ f` and whose
restriction to `V` is `b ∘ g`.

The source's object `B` of `D(𝒪_V)` is written `Bo` here, the letter `B` being the big fppf
site.  The first assertion of the source — the *existence* of a glueing `(F, f, g)` — is not
covered by this statement: `F`, `f` and `g` are hypotheses. -/
@[stacks 08HB "second assertion only (the induced morphism `F ⟶ E`), for a glued datum
`(F, f, g)` given as a hypothesis and granted the Mayer–Vietoris distinguished triangle of Tag
08GV part (2) at `F` as hT; the first assertion, existence of the glued object, is NOT covered"]
theorem exists_hom_of_glueData
    (adjU : shriekU ⊣ edsRestrictOpen B S hS hsq)
    (adjV : shriekV ⊣ edsRestrictEtale B S hS hsq)
    (adjP : shriekP ⊣ edsRestrictInter B S hS hsq)
    (F E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (δ : F ⟶ (shriekP.mapDerivedCategory.obj
      ((edsRestrictInter B S hS hsq).mapDerivedCategory.obj F))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk
        (biprod.lift
          (mayerVietorisGlueMap adjP.mapDerivedCategory adjU.mapDerivedCategory
            (edsDerivedRestrictCompOpen B S hS hsq) F)
          (-(mayerVietorisGlueMap adjP.mapDerivedCategory adjV.mapDerivedCategory
            (edsDerivedRestrictCompEtale B S hS hsq) F)))
        (biprod.desc (adjU.mapDerivedCategory.counit.app F)
          (adjV.mapDerivedCategory.counit.app F)) δ ∈
      distTriang (DerivedCategory (Modules.{u, u} B S hS W.1 W.2)))
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

end Square

end AlgebraicGeometry.Space

end
