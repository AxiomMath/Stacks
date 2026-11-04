module

public import StacksFrontier.AlgebraicGeometry.CompactOpenInduction.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.BigEtaleOpenSquares

/-!
# From affine opens to a quasi-compact quasi-separated base: the Mayer--Vietoris reduction

Let `X` be a scheme, let `(Y_i)` be a system of schemes over `X` indexed by `Iᵒᵖ`, and let `Y` be
a scheme over `X` with compatible morphisms `Y ⟶ Y_i`. Let `𝓕` be an abelian sheaf on the big
étale site. For an open subscheme `U` of `X` there is a canonical **comparison morphism**

`colim_i H^n(g_i⁻¹U, 𝓕) ⟶ H^n(g⁻¹U, 𝓕)`

from the colimit of the étale cohomology of `𝓕` over the preimages of `U` in the levels to the
étale cohomology of `𝓕` over the preimage of `U` in `Y`.

The main result is that the locus of opens where this comparison is invertible is **stable under
the Mayer--Vietoris step**: it contains `U ⊔ V` as soon as it contains `U`, `V` and `U ⊓ V`. That
statement is unconditional. Combined with [Stacks, Tag 08DR] it gives a reduction to the affine
opens: if the comparison is invertible over every *affine* open of `X`, then it is invertible over
`X` itself, as soon as `X` is quasi-compact and quasi-separated -- in particular for the source of
a quasi-compact quasi-separated morphism to an affine scheme.

The affine-open invertibility is a hypothesis of those two statements and is **not** a theorem at
the generality they are stated in; it is not the affine case of [Stacks, Tag 03Q6]. See the
implementation notes.

## Main definitions

* `Stacks.EtaleCohomology.QcqsReduction.levelDiagram`: the opens of `X`, pulled back to the
  levels of the system, as a diagram of functors into the big étale site.
* `Stacks.EtaleCohomology.QcqsReduction.comparison`: **the comparison morphism**
  `colim_i H^n(g_i⁻¹U, 𝓕) ⟶ H^n(g⁻¹U, 𝓕)`.

## Main results

* `Stacks.EtaleCohomology.QcqsReduction.isIso_comparison_sup`: **the Mayer--Vietoris step**, with
  no hypothesis beyond the three smaller opens. This is the compatibility of the Mayer--Vietoris
  sequences with the colimit, instantiated at the system of preimages.
* `Stacks.EtaleCohomology.QcqsReduction.isIso_comparison_top`: **the reduction to affine opens**
  for a quasi-compact quasi-separated `X`.
* `Stacks.EtaleCohomology.QcqsReduction.isIso_comparison_top_of_qcqs_over_affine`: the same, in
  the form in which the source applies it: `X` the source of a quasi-compact quasi-separated
  morphism to an affine scheme.

## Implementation notes

The transition morphisms between the preimages are `AlgebraicGeometry.Scheme.Hom.resLE`, whose
third argument is an inequality of opens rather than an equality, so no `eqToHom` enters: the
functoriality of the construction is `Scheme.Hom.resLE_comp_resLE`, `.map_resLE` and `.resLE_map`
together with proof irrelevance.

`comparison` is defined directly, independently of a second open, and the four comparison
morphisms attached to the Mayer--Vietoris square of a pair `U`, `V` are definitionally the
comparison morphisms of `U ⊓ V`, `U`, `V` and `U ⊔ V`, which is what lets the abstract descent
theorem apply with no transport.

### The affine-open hypothesis is a hypothesis, not a gap

`isIso_comparison_top` and `isIso_comparison_top_of_qcqs_over_affine` take the invertibility over
the affine opens as an honest hypothesis `haffine`, and they are untagged. That hypothesis cannot
be discharged, for two independent reasons, and neither is a missing piece of this library.

*The data of `comparison` is weaker than a limit.* The index `I` is an arbitrary category with
exact colimits of abelian groups -- not required filtered -- and `Y` carries a family of
morphisms `leg i : Y ⟶ g.obj i` compatible with the transitions, with no hypothesis making it a
limit cone of `g`. For `I` empty the colimit is `0` while the target is `𝓕` of an open of `Y`, so
`haffine` already fails there.

*The coefficients are wrong for [Stacks, Tag 03Q6], even at a genuine limit.* `𝓕` is an arbitrary
abelian sheaf on the big etale site of **all** schemes, whereas Tag 03Q6 takes the sheaves
`𝒢_i = (Y_i ⟶ X)^{-1}ℱ` of a single abelian sheaf `ℱ` on the small etale site of `X`. Taking `𝓕`
arbitrary makes the conclusion false. In degree zero `CategoryTheory.Sheaf.H' 𝓕 0 V` is `𝓕 V`
(the free abelian sheaf on `yoneda.obj V` corepresents the sections,
`Stacks.Cohomology.OverObjectCohomology.freeYonedaSheafHomEquiv`), so `haffine` in degree zero
asserts `colim_i 𝓕(g_i⁻¹U) = 𝓕(g⁻¹U)`. Take `X = Spec k` with its system of base changes along
`k[x_1, …, x_i] ⟶ k[x_1, x_2, …]`, so that `U = ⊤` is affine and `g⁻¹U = Spec k[x_1, x_2, …]` is
the limit of the `g_i⁻¹U = Spec k[x_1, …, x_i]`, and take `𝓕 = ∏_{n : ℕ} 𝒪` -- a product of
copies of the structure sheaf, which is a sheaf for the etale topology, products of sheaves being
sheaves. Then the section `(x_1, x_2, x_3, …)` of `𝓕` over `g⁻¹U` lies in no `𝓕(g_i⁻¹U)`, so the
comparison is not surjective. The condition that `𝓕` be an inverse image from the small etale
site of `X` is not expressible on the site of all schemes at all, a scheme carrying no morphism to
`X` in general.

What Tag 03Q6 at its own hypotheses does need is recorded at
`Stacks.EtaleCohomology.QcqsLimitCohomology.etaleCohomologyColimit_isColimit_affineOpen` and in
the implementation notes of that file; no Mayer--Vietoris reduction over the opens of `X` is
involved in either of the two routes named there. The affineness of the registered affine case of
Tag 03Q6 comes from one place only: `AlgebraicGeometry.hasTerminal_smallAffineEtale`, the terminal
object of the small *affine* etale site, which carries `[IsAffine S]`.

## References

* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 0A50](https://stacks.math.columbia.edu/tag/0A50)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open TopologicalSpace
open Stacks.Cohomology.MayerVietoris Stacks.EtaleCohomology.BigEtale

universe u v₁ u₁

namespace Stacks.EtaleCohomology.QcqsReduction

/-! ### Squares and natural transformations -/

section SquareNat

variable {C : Type*} [Category* C] {D : Type*} [Category* D]

/-- The morphism of squares induced by a natural transformation of functors. -/
def mapSquareNatTrans (sq : Square C) {F G : C ⥤ D} (α : F ⟶ G) : sq.map F ⟶ sq.map G where
  τ₁ := α.app sq.X₁
  τ₂ := α.app sq.X₂
  τ₃ := α.app sq.X₃
  τ₄ := α.app sq.X₄
  comm₁₂ := α.naturality sq.f₁₂
  comm₁₃ := α.naturality sq.f₁₃
  comm₂₄ := α.naturality sq.f₂₄
  comm₃₄ := α.naturality sq.f₃₄

/-- The image of a fixed square, as a functor of the functor it is pushed along. -/
def squareMapFunctor (sq : Square C) : (C ⥤ D) ⥤ Square D where
  obj F := sq.map F
  map α := mapSquareNatTrans sq α
  map_id _ := rfl
  map_comp _ _ := rfl

end SquareNat

/-! ### The system of preimages -/

section System

variable {X : Scheme.{u}} {I : Type u₁} [Category.{v₁} I]
  (g : Iᵒᵖ ⥤ Over X) (Y : Over X)
  (leg : ∀ i : Iᵒᵖ, Y ⟶ g.obj i)
  (hleg : ∀ ⦃i j : Iᵒᵖ⦄ (a : i ⟶ j), leg i ≫ g.map a = leg j)

/-- The restriction of a morphism of `X`-schemes to the preimages of an open of `X`. -/
def transitionRes {A B : Over X} (φ : A ⟶ B) (U : X.Opens) :
    ((A.hom ⁻¹ᵁ U : A.left.Opens) : Scheme.{u}) ⟶
      ((B.hom ⁻¹ᵁ U : B.left.Opens) : Scheme.{u}) :=
  φ.left.resLE (B.hom ⁻¹ᵁ U) (A.hom ⁻¹ᵁ U)
    (le_of_eq (by rw [← Scheme.Hom.comp_preimage, Over.w]))

/-- The restrictions to the preimages are compatible with the inclusions of opens: this is
`AlgebraicGeometry.Scheme.Hom.map_resLE` and `.resLE_map` together with proof irrelevance. -/
theorem transitionRes_naturality {A B : Over X} (φ : A ⟶ B) {U V : X.Opens} (k : U ≤ V) :
    A.left.homOfLE (Scheme.Hom.preimage_mono A.hom k) ≫ transitionRes φ V =
      transitionRes φ U ≫ B.left.homOfLE (Scheme.Hom.preimage_mono B.hom k) := by
  change A.left.homOfLE _ ≫ φ.left.resLE (B.hom ⁻¹ᵁ V) (A.hom ⁻¹ᵁ V) _ =
    φ.left.resLE (B.hom ⁻¹ᵁ U) (A.hom ⁻¹ᵁ U) _ ≫ B.left.homOfLE _
  rw [Scheme.Hom.map_resLE, Scheme.Hom.resLE_map]

/-- The restriction to the preimages of an identity is the identity. -/
theorem transitionRes_id (A : Over X) (U : X.Opens) : transitionRes (𝟙 A) U = 𝟙 _ := by
  have h : transitionRes (𝟙 A) U = A.left.homOfLE (le_refl (A.hom ⁻¹ᵁ U)) :=
    Scheme.Hom.resLE_id (le_refl (A.hom ⁻¹ᵁ U))
  rw [h, Scheme.homOfLE_rfl]

/-- The restrictions to the preimages compose. -/
theorem transitionRes_comp {A B D : Over X} (φ : A ⟶ B) (ψ : B ⟶ D) (U : X.Opens) :
    transitionRes (φ ≫ ψ) U = transitionRes φ U ≫ transitionRes ψ U := by
  change Scheme.Hom.resLE (φ.left ≫ ψ.left) (D.hom ⁻¹ᵁ U) (A.hom ⁻¹ᵁ U) _ =
    Scheme.Hom.resLE φ.left (B.hom ⁻¹ᵁ U) (A.hom ⁻¹ᵁ U) _ ≫
      Scheme.Hom.resLE ψ.left (D.hom ⁻¹ᵁ U) (B.hom ⁻¹ᵁ U) _
  rw [Scheme.Hom.resLE_comp_resLE]

/-- The restrictions to the preimages, as a natural transformation of functors into schemes. -/
def transitionNatScheme {A B : Over X} (φ : A ⟶ B) :
    Opens.map A.hom.base ⋙ A.left.restrictFunctor ⋙ Over.forget A.left ⟶
      Opens.map B.hom.base ⋙ B.left.restrictFunctor ⋙ Over.forget B.left where
  app U := transitionRes φ U
  naturality := fun _ _ k => transitionRes_naturality φ k.le

/-- `transitionNatScheme` sends the identity of `A` to the identity natural transformation. -/
theorem transitionNatScheme_id (A : Over X) : transitionNatScheme (𝟙 A) = 𝟙 _ :=
  NatTrans.ext (funext fun U => transitionRes_id A U)

/-- `transitionNatScheme` sends a composite of morphisms over `X` to the composite. -/
theorem transitionNatScheme_comp {A B D : Over X} (φ : A ⟶ B) (ψ : B ⟶ D) :
    transitionNatScheme (φ ≫ ψ) = transitionNatScheme φ ≫ transitionNatScheme ψ :=
  NatTrans.ext (funext fun U => transitionRes_comp φ ψ U)

/-- The restrictions to the preimages, as a natural transformation of functors into the big
étale site. -/
def transitionNat {A B : Over X} (φ : A ⟶ B) :
    preimageToSite A.hom ⟶ preimageToSite B.hom :=
  ((Functor.whiskeringRight X.Opens Scheme.{u} Site.{u}).obj AsSmall.up).map
    (transitionNatScheme φ)

/-- The restriction to the preimages of an identity is the identity. -/
theorem transitionNat_id (A : Over X) : transitionNat (𝟙 A) = 𝟙 _ := by
  change ((Functor.whiskeringRight X.Opens Scheme.{u} Site.{u}).obj AsSmall.up).map
      (transitionNatScheme (𝟙 A)) = 𝟙 _
  rw [transitionNatScheme_id, CategoryTheory.Functor.map_id]

/-- The restrictions to the preimages compose. -/
theorem transitionNat_comp {A B D : Over X} (φ : A ⟶ B) (ψ : B ⟶ D) :
    transitionNat (φ ≫ ψ) = transitionNat φ ≫ transitionNat ψ := by
  change ((Functor.whiskeringRight X.Opens Scheme.{u} Site.{u}).obj AsSmall.up).map
      (transitionNatScheme (φ ≫ ψ)) =
    ((Functor.whiskeringRight X.Opens Scheme.{u} Site.{u}).obj AsSmall.up).map
        (transitionNatScheme φ) ≫
      ((Functor.whiskeringRight X.Opens Scheme.{u} Site.{u}).obj AsSmall.up).map
        (transitionNatScheme ψ)
  rw [transitionNatScheme_comp, Functor.map_comp]

/-- **The opens of `X`, pulled back to the levels of the system.** -/
def levelDiagram : Iᵒᵖ ⥤ (X.Opens ⥤ Site.{u}) where
  obj i := preimageToSite (g.obj i).hom
  map a := transitionNat (g.map a)
  map_id i := by rw [g.map_id, transitionNat_id]
  map_comp a b := by rw [g.map_comp, transitionNat_comp]

/-- The system of Mayer--Vietoris squares attached to a pair of opens of `X`. -/
def mvSystem (U V : X.Opens) : MVFunctor topology.{u} I where
  functor := levelDiagram g ⋙ squareMapFunctor (opensSquare U V)
  mono_f₁₃ i := mono_preimageSquare_f₁₃ (g.obj i).hom U V
  isPushout i := preimageSquare_isPushout (g.obj i).hom U V

/-- The Mayer--Vietoris square of the preimages of a pair of opens in the vertex. -/
def limitSquare (U V : X.Opens) : topology.{u}.MayerVietorisSquare :=
  preimageMVSquare Y.hom U V

/-- The morphism of Mayer--Vietoris squares from the vertex to a level. -/
def legSquare (U V : X.Opens) (i : Iᵒᵖ) :
    (limitSquare Y U V).toSquare ⟶ (mvSystem g U V).functor.obj i :=
  mapSquareNatTrans (opensSquare U V) (transitionNat (leg i))

include hleg in
/-- The morphisms of Mayer--Vietoris squares from the vertex form a cone. -/
theorem legSquare_comp (U V : X.Opens) ⦃i j : Iᵒᵖ⦄ (a : i ⟶ j) :
    legSquare g Y leg U V i ≫ (mvSystem g U V).functor.map a = legSquare g Y leg U V j := by
  change (squareMapFunctor (D := Site.{u}) (opensSquare U V)).map (transitionNat (leg i)) ≫
      (squareMapFunctor (D := Site.{u}) (opensSquare U V)).map (transitionNat (g.map a)) =
    (squareMapFunctor (D := Site.{u}) (opensSquare U V)).map (transitionNat (leg j))
  rw [← Functor.map_comp, ← transitionNat_comp, hleg a]

/-! ### The comparison morphism -/

variable (𝓕 : Sheaf topology.{u} AddCommGrpCat.{u + 1})

/-- **The diagram of étale cohomology groups over the preimages of an open.** -/
def openDiagram (U : X.Opens) (n : ℕ) : I ⥤ AddCommGrpCat.{u + 1} :=
  (levelDiagram g ⋙ (evaluation X.Opens Site.{u}).obj U).rightOp ⋙
    𝓕.cohomologyPresheaf.{u + 1} n

include hleg in
/-- Restriction along a transition, then along a leg, is restriction along a leg. -/
theorem openDiagram_map_comp_leg (U : X.Opens) (n : ℕ) {i j : I} (a : i ⟶ j) :
    (openDiagram g 𝓕 U n).map a ≫
        (𝓕.cohomologyPresheaf.{u + 1} n).map ((transitionNat (leg (op j))).app U).op =
      (𝓕.cohomologyPresheaf.{u + 1} n).map ((transitionNat (leg (op i))).app U).op := by
  have key : ((transitionNat (g.map a.op)).app U).op ≫
      ((transitionNat (leg (op j))).app U).op =
      ((transitionNat (leg (op i))).app U).op := by
    rw [← op_comp, ← NatTrans.comp_app, ← transitionNat_comp, hleg a.op]
  exact ((𝓕.cohomologyPresheaf.{u + 1} n).map_comp _ _).symm.trans
    (congrArg (𝓕.cohomologyPresheaf.{u + 1} n).map key)

include hleg in
/-- The cocone of restrictions from the levels to the vertex. -/
def openCocone (U : X.Opens) (n : ℕ) : Cocone (openDiagram g 𝓕 U n) where
  pt := Sheaf.H'.{u + 1} 𝓕 n ((preimageToSite Y.hom).obj U)
  ι :=
    { app := fun i =>
        (𝓕.cohomologyPresheaf.{u + 1} n).map ((transitionNat (leg (op i))).app U).op
      naturality := fun _ _ a =>
        (openDiagram_map_comp_leg g Y leg hleg 𝓕 U n a).trans (Category.comp_id _).symm }

/-- **The comparison morphism** `colim_i H^n(g_i⁻¹U, 𝓕) ⟶ H^n(g⁻¹U, 𝓕)`. -/
def comparison [HasColimitsOfShape I AddCommGrpCat.{u + 1}] (U : X.Opens) (n : ℕ) :
    colimit (openDiagram g 𝓕 U n) ⟶ Sheaf.H'.{u + 1} 𝓕 n ((preimageToSite Y.hom).obj U) :=
  colimit.desc _ (openCocone g Y leg hleg 𝓕 U n)

/-! ### The Mayer--Vietoris step and the reduction -/

variable [HasColimitsOfShape I AddCommGrpCat.{u + 1}]
  [HasExactColimitsOfShape I AddCommGrpCat.{u + 1}]

include hleg in
/-- **The Mayer--Vietoris step.** If the comparison morphism is invertible over `U`, over `V` and
over `U ⊓ V` in every degree, then it is invertible over `U ⊔ V` in every degree.

There is no hypothesis beyond the three smaller opens: this is the compatibility of the
Mayer--Vietoris sequences of the levels with the colimit, through
`Stacks.Cohomology.MayerVietoris.isIso_cornerComparison_X₄`. -/
theorem isIso_comparison_sup (U V : X.Opens)
    (hU : ∀ n : ℕ, IsIso (comparison g Y leg hleg 𝓕 U n))
    (hV : ∀ n : ℕ, IsIso (comparison g Y leg hleg 𝓕 V n))
    (hUV : ∀ n : ℕ, IsIso (comparison g Y leg hleg 𝓕 (U ⊓ V) n)) :
    ∀ n : ℕ, IsIso (comparison g Y leg hleg 𝓕 (U ⊔ V) n) :=
  isIso_cornerComparison_X₄ 𝓕 (mvSystem g U V) (limitSquare Y U V)
    (legSquare g Y leg U V) (legSquare_comp g Y leg hleg U V) hUV hU hV

include hleg in
/-- **The reduction to affine opens.** For a quasi-compact quasi-separated scheme `X`, if the
comparison morphism is invertible over every affine open of `X` in every degree, then it is
invertible over `X` itself in every degree.

This is [Stacks, Tag 08DR] run on the Mayer--Vietoris step `isIso_comparison_sup`. -/
theorem isIso_comparison_top [QuasiSeparatedSpace X] [CompactSpace X]
    (haffine : ∀ U : X.Opens, IsAffineOpen U →
      ∀ n : ℕ, IsIso (comparison g Y leg hleg 𝓕 U n)) :
    ∀ n : ℕ, IsIso (comparison g Y leg hleg 𝓕 ⊤ n) :=
  Stacks.AlgebraicGeometry.CompactOpenInduction.top
    (P := fun U => ∀ n : ℕ, IsIso (comparison g Y leg hleg 𝓕 U n)) haffine
    fun U V _ _ hU hV hUV => isIso_comparison_sup g Y leg hleg 𝓕 U V hU hV hUV

include hleg in
/-- **The reduction to affine opens, for the source of a quasi-compact quasi-separated morphism
to an affine scheme.** If `X` is such a source and the comparison morphism is invertible over
every affine open of `X` in every degree, then it is invertible over `X` itself in every degree.

The hypothesis `haffine` is a genuine hypothesis of this statement and not a gap in the library:
`𝓕` is an arbitrary abelian sheaf on the big etale site of all schemes and `Y` is not required to
be a limit of the system, and at either of those generalities `haffine` is false. See the
implementation notes of this file. -/
theorem isIso_comparison_top_of_qcqs_over_affine {S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (haffine : ∀ U : X.Opens, IsAffineOpen U →
      ∀ n : ℕ, IsIso (comparison g Y leg hleg 𝓕 U n)) :
    ∀ n : ℕ, IsIso (comparison g Y leg hleg 𝓕 ⊤ n) :=
  Stacks.AlgebraicGeometry.CompactOpenInduction.top_of_qcqs_over_affine
    (P := fun U => ∀ n : ℕ, IsIso (comparison g Y leg hleg 𝓕 U n)) haffine
    (fun U V _ _ hU hV hUV => isIso_comparison_sup g Y leg hleg 𝓕 U V hU hV hUV) f

end System

end Stacks.EtaleCohomology.QcqsReduction

end
