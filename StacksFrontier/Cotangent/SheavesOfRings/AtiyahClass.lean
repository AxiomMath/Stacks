module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModules
public import StacksFrontier.CategoryTheory.Sites.Modules.PrincipalPartsSequenceStructure
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
* `CategoryTheory.Sheaf.atiyahClass`: the last arrow of that triangle, read through the
  identifications of its first and third terms.

## Main results

* `CategoryTheory.Sheaf.resolutionPrincipalPartsShortComplex_shortExact`: the sequence is short
  exact.
* `CategoryTheory.Sheaf.resolutionPrincipalPartsShortComplex_X₁` and
  `CategoryTheory.Sheaf.resolutionPrincipalPartsShortComplex_X₃`: its outer terms are the
  relative differentials tensored with the coefficient module, and the coefficient module.
* `CategoryTheory.Sheaf.atiyahTriangle_distinguished` and
  `CategoryTheory.Sheaf.atiyahTriangle_distinguished_of_iso`: the Atiyah triangle is
  distinguished, and so is the triangle written in the form the source displays.
* `CategoryTheory.Sheaf.atiyahClass_mem_distinguished`: the Atiyah class is the last arrow of
  that displayed triangle.

## Implementation notes

The sequence is the one of Tag 09CW for the ring map `A ⟶ P_n`, instantiated at the restriction
of `F` along the augmentation; the content is therefore the instantiation, not a second proof of
exactness. The universes are those of the cotangent complex of a morphism of sheaves of rings:
the structure sheaves are `CommRingCat.{max u v w}`-valued, and the coefficient modules of Tag
09CW are taken in the free universe `w`, which places them in `SheafOfModules.{max u v w}`, the
universe in which the standard resolution and its sheaves of differentials live.

The Atiyah triangle is formed exactly as in the ring case
`StacksFrontier/Cotangent/AtiyahClass.lean`, which carries Tags 09DD and 09DE: an exact functor of
triangulated categories applied to the triangle of a short exact sequence. Five inputs of the
source are carried as explicit parameters, the library not yet having them.

* `M` is the category of simplicial `P_•`-modules of Tag 09D1, which is `resolutionModules` once
  that category is known to be abelian; it is kept as a parameter because the abelian structure
  of a category of simplicial modules is not in the library.
* `G` is the exact functor `Lπ_! : D(P_•) ⟶ D(B)` of Tag 09D3. Its construction is
  `Stacks.SimplicialModules.augmentedLowerShriek`, which is itself conditional on Tag 09CY.
* `hS` is the short exact sequence of simplicial `P_•`-modules whose degree `n` part is the
  sequence of Tag 09DG proved above; assembling the degreewise sequences into a simplicial one
  uses the functoriality of Tag 09CX.
* `e₁` and `e₃` are the source's identifications `Lπ_!(Ω_{P_•/A} ⊗_{P_•} F) = L_{B/A} ⊗_B^L F`
  of Tag 08PU and `Lπ_!(F) = F` of Tag 08QE. These are the same two hypotheses, in the same
  shape and with the same names, that the ring-case
  `CommAlgCat.polynomialAtiyahTriangle_distinguished_of_iso` of Tag 09DD carries.

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

/-- **Stacks 09DH.** The Atiyah triangle of a sheaf of `B`-modules, written with its first and
third terms replaced by objects identified with them: for `L` identified with
`Lπ_!(Ω_{P_•/A} ⊗_{P_•} F)` and `N` identified with `Lπ_!(F)`, the sequence
`L ⟶ Lπ_!(P¹_{P_•/A}(F)) ⟶ N ⟶ L[1]` is a distinguished triangle in `D(B)`. -/
@[stacks 09DH "the distinguished triangle; `M`, `G`, `hS`, `e₁` and `e₃` carry the inputs the \
library does not yet have — the category of simplicial `P_•`-modules known to be abelian, the \
functor Lπ_! of Tag 09D3, the simplicial short exact sequence of Tag 09DG, and the \
identifications of Tags 08PU and 08QE. See the implementation notes"]
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

/-- **Stacks 09DI.** The *Atiyah class* of a sheaf of `B`-modules: the map
`F ⟶ L_{B/A} ⊗_B^L F[1]`, realised as the last arrow `N ⟶ L[1]` of the Atiyah triangle of
Tag 09DH, read through the identifications of its first and third terms. -/
@[stacks 09DI "the Atiyah class, as the last arrow of the triangle of Tag 09DH; `M`, `G`, `hS`, \
`e₁` and `e₃` carry the same five inputs the library does not yet have that \
`atiyahTriangle_distinguished_of_iso` carries, so `N` stands for `F` and `L` for \
`L_{B/A} ⊗_B^L F`. See the implementation notes"]
def atiyahClass (G : DerivedCategory M ⥤ DerivedCategory (targetModules J B))
    [G.CommShift ℤ] [G.IsTriangulated] {S : ShortComplex M} (hS : S.ShortExact)
    (L N : DerivedCategory (targetModules J B))
    (e₁ : (atiyahTriangle J G hS).obj₁ ≅ L) (e₃ : (atiyahTriangle J G hS).obj₃ ≅ N) :
    N ⟶ L⟦(1 : ℤ)⟧ :=
  e₃.inv ≫ (atiyahTriangle J G hS).mor₃ ≫
    (shiftFunctor (DerivedCategory (targetModules J B)) (1 : ℤ)).map e₁.hom

/-- The Atiyah class is the last arrow of the displayed distinguished triangle. -/
theorem atiyahClass_mem_distinguished
    (G : DerivedCategory M ⥤ DerivedCategory (targetModules J B))
    [G.CommShift ℤ] [G.IsTriangulated] {S : ShortComplex M} (hS : S.ShortExact)
    (L N : DerivedCategory (targetModules J B))
    (e₁ : (atiyahTriangle J G hS).obj₁ ≅ L) (e₃ : (atiyahTriangle J G hS).obj₃ ≅ N) :
    Triangle.mk (e₁.inv ≫ (atiyahTriangle J G hS).mor₁)
        ((atiyahTriangle J G hS).mor₂ ≫ e₃.hom) (atiyahClass J G hS L N e₁ e₃) ∈
      distinguishedTriangles :=
  atiyahTriangle_distinguished_of_iso J G hS L N e₁ e₃

end Triangle

end CategoryTheory.Sheaf

end
