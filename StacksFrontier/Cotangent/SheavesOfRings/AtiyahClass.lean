module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModules
public import StacksFrontier.CategoryTheory.Sites.Modules.PrincipalPartsSequenceStructure
public import StacksFrontier.Cotangent.SheavesOfRings.AtiyahClassDefinite
public import StacksFrontier.Cotangent.SheavesOfRings.CotangentComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The Atiyah class of a sheaf of modules

Let `C` be a site, let `f : A ⟶ B` be a morphism of sheaves of commutative rings on `C`, let `F`
be a sheaf of `B`-modules and let `P_• ⟶ B` be the standard resolution of `B` over `A`. In each
simplicial degree the sheaves of first principal parts of `P_n` over `A` give a short exact
sequence

`0 ⟶ Ω_{P_n/A} ⊗_{P_n} F ⟶ P¹_{P_n/A}(F) ⟶ F ⟶ 0`

of sheaves of `P_n`-modules, where `F` carries the `P_n`-action coming from the augmentation
`P_n ⟶ B`.

## Main definitions

* `CategoryTheory.Sheaf.resolutionCoefficients`: a sheaf of `B`-modules read as a sheaf of
  `P_n`-modules along the augmentation.
* `CategoryTheory.Sheaf.resolutionPrincipalParts`: the canonical functorial sequence of first
  principal parts of `P_n` over `A`.
* `CategoryTheory.Sheaf.resolutionPrincipalPartsShortComplex`: that sequence at the coefficient
  module, as a short complex.
* `CategoryTheory.Sheaf.resolutionRing` and `CategoryTheory.Sheaf.resolutionModules`: the
  simplicial sheaf of rings `P_•` and its category of simplicial modules.
* `CategoryTheory.Sheaf.atiyahTriangle`: the image under `Lπ_!` of the triangle of a short exact
  sequence of simplicial `P_•`-modules.
* `CategoryTheory.Sheaf.atiyahClassOfIso`: the last arrow of that triangle, read through
  identifications of its first and third terms.
* `CategoryTheory.Sheaf.atiyahClass`: **the Atiyah class of Tag 09DI**, `ℱ ⟶ (L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ)[1]`,
  which is `atiyahClassOfIso` at the library's own `Lπ_!`, short exact sequence and
  identifications.

## Main results

* `CategoryTheory.Sheaf.resolutionPrincipalPartsShortComplex_shortExact`: the sequence is short
  exact.
* `CategoryTheory.Sheaf.resolutionPrincipalPartsShortComplex_X₁` and
  `CategoryTheory.Sheaf.resolutionPrincipalPartsShortComplex_X₃`: its outer terms are the
  relative differentials tensored with the coefficient module, and the coefficient module.
* `CategoryTheory.Sheaf.atiyahTriangle_distinguished` and
  `CategoryTheory.Sheaf.atiyahTriangle_distinguished_of_iso`: the image of the triangle of a short
  exact sequence under an exact functor is distinguished, and stays so when its outer terms are
  replaced along arbitrary given isomorphisms. These are formal lemmas, not Tag 09DH itself: the
  triangle of [Stacks, Tag 09DH] at the standard resolution, with its outer terms identified by
  constructed isomorphisms, is `CategoryTheory.Sheaf.sheafAtiyahTriangle_distinguished`.
* `CategoryTheory.Sheaf.atiyahClassOfIso_mem_distinguished`: that arrow is the last arrow of the
  displayed triangle.
* `CategoryTheory.Sheaf.atiyahClass_mem_distinguished`: the Atiyah class is the last arrow of the
  distinguished triangle of Tag 09DH, and `CategoryTheory.Sheaf.atiyahClass_eq_sheafAtiyahClass`
  identifies it with `CategoryTheory.Sheaf.sheafAtiyahClass`.

## Implementation notes

The sequence is the one of Tag 09CW for the ring map `A ⟶ P_n`, instantiated at the restriction
of `F` along the augmentation; the content is therefore the instantiation, not a second proof of
exactness. The universes are those of the cotangent complex of a morphism of sheaves of rings:
the structure sheaves are `CommRingCat.{max u v w}`-valued, and the coefficient modules of Tag
09CW are taken in the free universe `w`, which places them in `SheafOfModules.{max u v w}`, the
universe in which the standard resolution and its sheaves of differentials live.

The Atiyah triangle is formed exactly as in the ring case
`StacksFrontier/Cotangent/AtiyahClass.lean`, which carries Tags 09DD and 09DE: an exact functor of
triangulated categories applied to the triangle of a short exact sequence. The declarations of the
section `Triangle` are stated for an arbitrary abelian category `M`, an arbitrary exact functor
`G : D(M) ⟶ D(B)`, an arbitrary short exact sequence `hS` in `M` and arbitrary identifications
`e₁`, `e₃` of the outer terms of the resulting triangle; they are the formal part of the
construction and make no claim about the standard resolution.

The construction of Tags 09DH and 09DI at the standard resolution itself is in
`StacksFrontier/Cotangent/SheavesOfRings/AtiyahTriangle.lean` and
`StacksFrontier/Cotangent/SheavesOfRings/AtiyahClassDefinite.lean`: the functor `Lπ_!` of Tag 09D3 is
`CategoryTheory.Sheaf.resolutionLowerShriek`, the short exact sequence of simplicial
`P_•`-modules is `CategoryTheory.Sheaf.simplicialPrincipalPartsShortComplex_shortExact`, the
identifications of the outer terms are `CategoryTheory.Sheaf.atiyahTriangleFirstTermIso` and
`CategoryTheory.Sheaf.atiyahTriangleThirdTermIso`, the distinguished triangle of Tag 09DH is
`CategoryTheory.Sheaf.sheafAtiyahTriangle_distinguished`. The last section feeds these into
`atiyahClassOfIso` to give the Atiyah class `CategoryTheory.Sheaf.atiyahClass` of Tag 09DI. That
section is stated, like those files, for a small site whose sheaves of rings and modules take
values in the universe of its objects, with cocontinuity of `π : Δ × C ⥤ C` (found by instance
search) and the covering-pullback clause `Stacks.Sites.PreservesCoveringPullbacks` for `π`, which
transcribes axiom (3) of a site, [Stacks, Tag 00VH].

## References

* [Stacks Project, Tag 09DG](https://stacks.math.columbia.edu/tag/09DG), the extension of
  principal parts of the standard resolution.
* [Stacks Project, Tag 09CW](https://stacks.math.columbia.edu/tag/09CW), the functorial sequence
  of first principal parts.
* [Stacks Project, Tag 08SR](https://stacks.math.columbia.edu/tag/08SR), the standard resolution.
* [Stacks Project, Tag 09DH](https://stacks.math.columbia.edu/tag/09DH), the Atiyah triangle, and
  [Tag 09DI](https://stacks.math.columbia.edu/tag/09DI), the Atiyah class.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.SheafOfModules (PrincipalPartsSequence principalPartsSequenceOfSite
  derivationsFunctor)

universe u v w u₁ v₁ w₁ t

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-- A sheaf of `B`-modules read as a sheaf of `P_n`-modules through the augmentation
`P_n ⟶ B` of the standard resolution. -/
abbrev resolutionCoefficients (n : SimplexCategoryᵒᵖ) (F : targetModules J B) :
    targetModules J (resolutionTerm J f n) :=
  (SheafOfModules.restrictScalars (resolutionAugmentationRing J f n)).obj F

/-- The canonical functorial sequence of first principal parts of a term of the standard
resolution over the base sheaf of rings. -/
abbrev resolutionPrincipalParts (n : SimplexCategoryᵒᵖ) :
    PrincipalPartsSequence.{v, u, max u v w, w} A (resolutionTerm J f n)
      (resolutionBase J f n) :=
  principalPartsSequenceOfSite.{v, u, max u v w, w} A (resolutionTerm J f n)
    (resolutionBase J f n)

/-- The inclusion `Ω_{P_n/A} ⊗_{P_n} F ⟶ P¹_{P_n/A}(F)` followed by the projection
`P¹_{P_n/A}(F) ⟶ F` vanishes. -/
theorem resolutionPrincipalParts_inclusion_comp_projection (n : SimplexCategoryᵒᵖ)
    (F : targetModules J B) :
    (resolutionPrincipalParts J f n).inclusion.app (resolutionCoefficients J f n F) ≫
      (resolutionPrincipalParts J f n).projection.app (resolutionCoefficients J f n F) = 0 :=
  ((resolutionPrincipalParts J f n).shortExact (resolutionCoefficients J f n F)).elim
    fun h _ => h

/-- The extension of principal parts in simplicial degree `n`: the sequence
`Ω_{P_n/A} ⊗_{P_n} F ⟶ P¹_{P_n/A}(F) ⟶ F`, as a short complex of sheaves of
`P_n`-modules. -/
def resolutionPrincipalPartsShortComplex (n : SimplexCategoryᵒᵖ) (F : targetModules J B) :
    ShortComplex (targetModules J (resolutionTerm J f n)) :=
  ShortComplex.mk _ _ (resolutionPrincipalParts_inclusion_comp_projection J f n F)

/-- **Stacks 09DG.** The extension of principal parts of a term of the standard resolution is
short exact: `0 ⟶ Ω_{P_n/A} ⊗_{P_n} F ⟶ P¹_{P_n/A}(F) ⟶ F ⟶ 0`. -/
@[stacks 09DG]
theorem resolutionPrincipalPartsShortComplex_shortExact (n : SimplexCategoryᵒᵖ)
    (F : targetModules J B) :
    (resolutionPrincipalPartsShortComplex J f n F).ShortExact :=
  ((resolutionPrincipalParts J f n).shortExact (resolutionCoefficients J f n F)).elim
    fun _ h => h

/-- The first term of the extension of principal parts is the relative differentials of `P_n`
over `A` tensored with the coefficient module. -/
theorem resolutionPrincipalPartsShortComplex_X₁ (n : SimplexCategoryᵒᵖ)
    (F : targetModules J B) :
    (resolutionPrincipalPartsShortComplex J f n F).X₁ =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (resolutionTerm J f n)).flip.obj
        (resolutionDifferentials J f n)).obj (resolutionCoefficients J f n F) :=
  rfl

/-- The third term of the extension of principal parts is the coefficient module. -/
theorem resolutionPrincipalPartsShortComplex_X₃ (n : SimplexCategoryᵒᵖ)
    (F : targetModules J B) :
    (resolutionPrincipalPartsShortComplex J f n F).X₃ = resolutionCoefficients J f n F :=
  rfl

/-! ### The Atiyah triangle -/

/-- The simplicial sheaf of rings `P_•` underlying the standard resolution of `B` over `A`. -/
abbrev resolutionRing : SimplicialObject (Sheaf J RingCat.{max u v w}) :=
  (standardResolution J f).left ⋙ Under.forget A ⋙
    sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})

/-- The category of simplicial `P_•`-modules of Tag 09D1, over the standard resolution. -/
abbrev resolutionModules :=
  Stacks.SimplicialModules.SimplicialModule.{max u v w, v, u, max u v w} J (resolutionRing J f)

section Triangle

variable {M : Type u₁} [Category.{v₁} M] [Abelian M] [HasDerivedCategory.{w₁} M]
  [HasDerivedCategory.{t} (targetModules J B)]

/-- The image under `Lπ_!` of the triangle attached to a short exact sequence of simplicial
`P_•`-modules: a triangle `Lπ_!(S.X₁) ⟶ Lπ_!(S.X₂) ⟶ Lπ_!(S.X₃) ⟶ Lπ_!(S.X₁)[1]` in `D(B)`. -/
def atiyahTriangle (G : DerivedCategory M ⥤ DerivedCategory (targetModules J B))
    [G.CommShift ℤ] [G.IsTriangulated] {S : ShortComplex M} (hS : S.ShortExact) :
    Triangle (DerivedCategory (targetModules J B)) :=
  G.mapTriangle.obj hS.singleTriangle

/-- The Atiyah triangle is distinguished: it is the image of a short exact sequence under an
exact functor of triangulated categories. -/
theorem atiyahTriangle_distinguished
    (G : DerivedCategory M ⥤ DerivedCategory (targetModules J B))
    [G.CommShift ℤ] [G.IsTriangulated] {S : ShortComplex M} (hS : S.ShortExact) :
    atiyahTriangle J G hS ∈ distinguishedTriangles :=
  G.map_distinguished _ hS.singleTriangle_distinguished

/-- The image under an exact functor `G` of the triangle of a short exact sequence, written with
its first and third terms replaced by objects `L` and `N` along given isomorphisms `e₁` and `e₃`,
is a distinguished triangle. This is a formal lemma about arbitrary `G`, `hS`, `e₁` and `e₃`, and
is not itself [Stacks, Tag 09DH]: the triangle of Tag 09DH, at the standard resolution with the
outer terms identified with `L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ` and `ℱ` by constructed isomorphisms and no
identification assumed, is `CategoryTheory.Sheaf.sheafAtiyahTriangle_distinguished`, which carries
the tag. -/
theorem atiyahTriangle_distinguished_of_iso
    (G : DerivedCategory M ⥤ DerivedCategory (targetModules J B))
    [G.CommShift ℤ] [G.IsTriangulated] {S : ShortComplex M} (hS : S.ShortExact)
    (L N : DerivedCategory (targetModules J B))
    (e₁ : (atiyahTriangle J G hS).obj₁ ≅ L) (e₃ : (atiyahTriangle J G hS).obj₃ ≅ N) :
    Triangle.mk (e₁.inv ≫ (atiyahTriangle J G hS).mor₁)
        ((atiyahTriangle J G hS).mor₂ ≫ e₃.hom)
        (e₃.inv ≫ (atiyahTriangle J G hS).mor₃ ≫
          (shiftFunctor (DerivedCategory (targetModules J B)) (1 : ℤ)).map e₁.hom) ∈
      distinguishedTriangles :=
  isomorphic_distinguished _ (atiyahTriangle_distinguished J G hS) _
    (Triangle.isoMk _ _ e₁.symm (Iso.refl _) e₃.symm (by simp) (by simp) (by simp))

/-- The last arrow `N ⟶ L[1]` of the triangle of `atiyahTriangle_distinguished_of_iso`, read
through the identifications `e₁` and `e₃` of its first and third terms. At the standard resolution,
with the library's inputs, this is the Atiyah class `CategoryTheory.Sheaf.atiyahClass` of
Tag 09DI. -/
def atiyahClassOfIso (G : DerivedCategory M ⥤ DerivedCategory (targetModules J B))
    [G.CommShift ℤ] [G.IsTriangulated] {S : ShortComplex M} (hS : S.ShortExact)
    (L N : DerivedCategory (targetModules J B))
    (e₁ : (atiyahTriangle J G hS).obj₁ ≅ L) (e₃ : (atiyahTriangle J G hS).obj₃ ≅ N) :
    N ⟶ L⟦(1 : ℤ)⟧ :=
  e₃.inv ≫ (atiyahTriangle J G hS).mor₃ ≫
    (shiftFunctor (DerivedCategory (targetModules J B)) (1 : ℤ)).map e₁.hom

/-- `atiyahClassOfIso` is the last arrow of the displayed distinguished triangle. -/
theorem atiyahClassOfIso_mem_distinguished
    (G : DerivedCategory M ⥤ DerivedCategory (targetModules J B))
    [G.CommShift ℤ] [G.IsTriangulated] {S : ShortComplex M} (hS : S.ShortExact)
    (L N : DerivedCategory (targetModules J B))
    (e₁ : (atiyahTriangle J G hS).obj₁ ≅ L) (e₃ : (atiyahTriangle J G hS).obj₃ ≅ N) :
    Triangle.mk (e₁.inv ≫ (atiyahTriangle J G hS).mor₁)
        ((atiyahTriangle J G hS).mor₂ ≫ e₃.hom) (atiyahClassOfIso J G hS L N e₁ e₃) ∈
      distinguishedTriangles :=
  atiyahTriangle_distinguished_of_iso J G hS L N e₁ e₃

end Triangle

/-! ### The Atiyah class -/

section AtiyahClass

open Stacks.SimplicialModules (projection projectionTopology)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [(projection C).IsCocontinuous (projectionTopology C J) J]
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B)

/-- **[Stacks, Tag 09DI], Definition 92.19.1: the Atiyah class of a sheaf of modules.** For a
homomorphism `f : 𝒜 ⟶ ℬ` of sheaves of commutative rings on a site and a sheaf of `ℬ`-modules `ℱ`,
the *Atiyah class* of `ℱ` is the morphism

`ℱ ⟶ (L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ)[1]`

of `D(ℬ)`, the last arrow of the triangle (92.19.0.2) of [Stacks, Tag 09DH]. It is
`atiyahClassOfIso` at the library's constructions: the functor `Lπ_!` of Tag 09D3
(`CategoryTheory.Sheaf.resolutionLowerShriek`), the short exact sequence of first principal parts
of the standard resolution as simplicial `P_•`-modules
(`CategoryTheory.Sheaf.simplicialPrincipalPartsShortComplex_shortExact`, Tag 09DG), and the
identifications of the outer terms with `L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ` and `ℱ`
(`CategoryTheory.Sheaf.atiyahTriangleFirstTermIso` and
`CategoryTheory.Sheaf.atiyahTriangleThirdTermIso`). -/
@[stacks 09DI "the Atiyah class `ℱ ⟶ (L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ)[1]` of a sheaf of `ℬ`-modules, the last \
arrow of the triangle of Tag 09DH, for any homomorphism of sheaves of commutative rings on a site"]
def atiyahClass (F : SheafOfModules.{u} (targetRing J (B := B))) :
    DerivedCategory.Q.obj
        ((HomologicalComplex.single (SheafOfModules.{u} (targetRing J (B := B)))
          (ComplexShape.up ℤ) 0).obj F) ⟶
      (((derivedTensorProductFunctor B).obj
          (DerivedCategory.Q.obj (cotangentComplex.{u, u, u} J f))).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules B)
            (ComplexShape.up ℤ) 0).obj F)))⟦(1 : ℤ)⟧ :=
  atiyahClassOfIso.{u, u, u} J (resolutionLowerShriek J f)
    (simplicialPrincipalPartsShortComplex_shortExact J f F) _ _
    (atiyahTriangleFirstTermIso J f F) (atiyahTriangleThirdTermIso J f F)

/-- The Atiyah class is the morphism `CategoryTheory.Sheaf.sheafAtiyahClass`. -/
theorem atiyahClass_eq_sheafAtiyahClass (F : SheafOfModules.{u} (targetRing J (B := B))) :
    atiyahClass J f F = sheafAtiyahClass J f F :=
  rfl

/-- **The Atiyah class is the last arrow of the distinguished triangle of [Stacks, Tag 09DH]**,
`L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ ⟶ Lπ_!(P¹_{𝒫/π^{-1}𝒜}(ℱ)) ⟶ ℱ ⟶ (L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ)[1]`. -/
theorem atiyahClass_mem_distinguished (F : SheafOfModules.{u} (targetRing J (B := B))) :
    Triangle.mk ((atiyahTriangleFirstTermIso J f F).inv ≫ (resolutionAtiyahTriangle J f F).mor₁)
        ((resolutionAtiyahTriangle J f F).mor₂ ≫ (atiyahTriangleThirdTermIso J f F).hom)
        (atiyahClass J f F) ∈ distinguishedTriangles :=
  sheafAtiyahClass_mem_distinguished J f F

end AtiyahClass

end CategoryTheory.Sheaf

end
