module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.AugmentationDerivedBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.ProjectionDerivedLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Modules.PrincipalPartsSequenceStructure
public import StacksFrontier.Cotangent.SheavesOfRings.CotangentComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The Atiyah triangle of a sheaf of modules

Let `C` be a site, let `f : 𝒜 ⟶ ℬ` be a morphism of sheaves of commutative rings on `C`, let `ℱ` be
a sheaf of `ℬ`-modules and let `P_• ⟶ ℬ` be the standard resolution of `ℬ` over `𝒜`. Applying the
functor `Lπ_! : D(P_•) ⟶ D(ℬ)` of Tag 09D3 to the short exact sequence of first principal parts of
`P_•` gives a distinguished triangle in `D(ℬ)`, writing `Ω = Ω_{𝒫/π^{-1}𝒜}` and
`P¹ = P¹_{𝒫/π^{-1}𝒜}`:

`Lπ_!(Ω ⊗_𝒫 ℱ) ⟶ Lπ_!(P¹(ℱ)) ⟶ Lπ_!(ℱ) ⟶ Lπ_!(Ω ⊗_𝒫 ℱ)[1]`

## Main definitions

* `CategoryTheory.Sheaf.resolutionCommRing`, `CategoryTheory.Sheaf.resolutionCommAugmentation` and
  `CategoryTheory.Sheaf.resolutionCommBase`: the standard resolution as a simplicial sheaf of
  commutative rings, its augmentation `ε : P_• ⟶ ℬ`, and the structure maps `𝒜 ⟶ P_n`.
* `CategoryTheory.Sheaf.simplicialBase`, `CategoryTheory.Sheaf.simplicialResolution` and
  `CategoryTheory.Sheaf.simplicialBaseMap`: `π^{-1}𝒜` and `𝒫`, the sheaves of commutative rings on
  `Δ × C` of the constant simplicial sheaf `𝒜` and of `P_•`, and the map between them.
* `CategoryTheory.Sheaf.simplicialPrincipalParts`: the sequence of first principal parts of
  Tag 09CW for `π^{-1}𝒜 ⟶ 𝒫`, taken on the site `Δ × C`.
* `CategoryTheory.Sheaf.projectionCoefficients` and `CategoryTheory.Sheaf.simplicialCoefficients`:
  `ℱ` read on `Δ × C`, and read there as a sheaf of `𝒫`-modules through the augmentation.
* `CategoryTheory.Sheaf.simplicialPrincipalPartsShortComplex`: that sequence at the coefficient
  module, as a short complex of simplicial `P_•`-modules.
* `CategoryTheory.Sheaf.resolutionLowerShriek`: the functor `Lπ_! : D(P_•) ⟶ D(ℬ)` of Tag 09D3.
* `CategoryTheory.Sheaf.resolutionAtiyahTriangle`: its image of the triangle of that short exact
  sequence.

## Main results

* `CategoryTheory.Sheaf.simplicialPrincipalPartsShortComplex_shortExact`: **Tag 09DG as a short
  exact sequence of simplicial `P_•`-modules.**
* `CategoryTheory.Sheaf.resolutionAtiyahTriangle_distinguished`: the Atiyah triangle is
  distinguished.
* `CategoryTheory.Sheaf.resolutionAtiyahTriangle_obj₁`, `resolutionAtiyahTriangle_obj₂` and
  `resolutionAtiyahTriangle_obj₃`: the three terms of the triangle are `Lπ_!` of the three terms of
  that sequence. The middle one is the middle term the source displays.
* `CategoryTheory.Sheaf.simplicialPrincipalPartsShortComplex_X₁`: its first term is
  `Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 ℱ`.
* `CategoryTheory.Sheaf.simplicialCoefficients_sections` and
  `CategoryTheory.Sheaf.simplicialPrincipalPartsShortComplex_X₃_sections`: the coefficient module
  on `Δ × C`, and so the third term of the sequence, has as its sections over `(n, U)` the sections
  of `ℱ` over `U`.

## Implementation notes

**The sequence is formed on `Δ × C`.** The source reads Tag 09DG in each simplicial degree `n` and
then invokes the functoriality of Tag 09CX to recognise the family as a sequence of simplicial
`P_•`-modules. Here `AlgebraicGeometry.SheafOfModules.principalPartsSequenceOfSite`, which is
stated for an arbitrary site, forms the sequence once, on the site `Δ × C`, over the sheaf of rings
`Stacks.SimplicialModules.simplicialCommRingSheaf` of `P_•`. Its simplicial structure is the one
`Δ × C` carries, the sheaf of differentials `Ω_{𝒫/π^{-1}𝒜}` on `Δ × C` is its first term, and short
exactness is its last field. Restricting to the fibre over a degree `n` returns the sequence of
Tag 09DG for the ring map `𝒜 ⟶ P_n`.

**The outer terms.** The source displays the triangle with its outer terms identified, as

`L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ ⟶ Lπ_!(P¹_{𝒫/𝒜}(ℱ)) ⟶ ℱ ⟶ L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ[1]`,

using `Lπ_!(Ω_{P_•/𝒜} ⊗_{P_•} ℱ) = L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ` (the first term, `e₁`) and `Lπ_!(ℱ) = ℱ` (the
third, `e₃`); this file states the triangle with its outer terms left as `Lπ_!` of what they are.
The two identifications are not Tags 08PU and 08QE: those are lemmas about a **ring map**, `π` in
both being the point morphism of the chaotic polynomial site `C_{B/A}` of Tag 08PR. What identifies
the outer terms is

* **Definition 08SS**, which *defines* `L_{ℬ/𝒜}` to be the complex of `ℬ`-modules associated to the
  simplicial module `Ω_{𝒫_•/𝒜} ⊗_{𝒫_•, ε} ℬ` — in this library
  `CategoryTheory.Sheaf.cotangentComplex`, the alternating-face-map complex of that simplicial
  module; and
* the untagged paragraph of Cohomology on Sites, Section 09D0, "Given a simplicial module `ℱ_•` the
  object `Lπ_!(ℱ_•)` is represented by the associated chain complex `s(ℱ_•)`", which the source
  states for an arbitrary site.

So both identifications are instances of one fact — `Lπ_!` of a simplicial module is the derived
image of its alternating-face-map complex — together, for the first term, with the termwise
freeness of `Ω_{𝒫_n/𝒜}` that turns `s(Ω ⊗_{𝒫_•} ℱ)` into `s(Ω ⊗_{𝒫_•} ℬ) ⊗^𝐋_ℬ ℱ`, and with the
bounded-above case of Tag 09D2,
`Stacks.SimplicialModules.nonempty_derivedProjectionLowerShriek_augmentationBaseChange_iso`.

**The hypotheses on the site.** `C` is small and its morphisms, the sections of the sheaves of
rings and the sections of the modules all lie in one universe `u`; that is forced by
`Stacks.Cohomology.derivedCoefficientChange`, which the `base` factor of Tag 09D3 rests on, and
which is stated at `AlgebraicGeometry.RingedTopos.{u, u, u}` because the derived pullback of ringed
topoi is. Smallness of `C` is the source's own — a Stacks site has a set of objects — but the
identification of the universe of the sections with the universe of `C` is not a hypothesis of
Section 92.19, which lets `𝒜`, `ℬ` and `ℱ` be arbitrary sheaves with no size relation to `C`. The
colimit-side constructions of Tag 08PS (`Stacks.CategoryHomology.totalDerivedColimit`,
`Stacks.CategoryHomology.diagramsEnoughProjectives` and
`Stacks.ChaoticSite.totalDerivedColimitEquivalenceIso`) carry no `[SmallCategory C]`; lifting the
single universe means restating `derivedCoefficientChange` at `RingedTopos.{u, v, w}`.

The sheaves of rings are `CommRingCat`-valued. The remaining instance arguments are cocontinuity of
`π` and the covering-pullback clause `Stacks.Sites.PreservesCoveringPullbacks` for `π`; continuity
needs no hypothesis (`Stacks.SimplicialModules.isContinuous_prodSnd_inheritedTopology`). Stacks,
Definition 00VH axiom (3) asserts that for a covering `{U_i → U}` and a morphism `V → U` the fibre
products `U_i ×_U V` exist and the base-changed family is a covering. Mathlib's
`GrothendieckTopology` omits that axiom, and `PreservesCoveringPullbacks` is where it returns;
together with clause (2) of Stacks, Definition 00WV it is the standing hypothesis "let `C` be a
site", transcribed.

## References

* [Stacks Project, Tag 09DH](https://stacks.math.columbia.edu/tag/09DH), the Atiyah triangle, and
  [Tag 09DI](https://stacks.math.columbia.edu/tag/09DI), the Atiyah class.
* [Stacks Project, Tag 09DG](https://stacks.math.columbia.edu/tag/09DG), the extension of principal
  parts of the standard resolution.
* [Stacks Project, Tag 09CW](https://stacks.math.columbia.edu/tag/09CW), the functorial sequence of
  first principal parts, and [Tag 09CX](https://stacks.math.columbia.edu/tag/09CX), its
  functoriality.
* [Stacks Project, Tag 09D3](https://stacks.math.columbia.edu/tag/09D3), the functor `Lπ_!`, and
  [Tag 09CY](https://stacks.math.columbia.edu/tag/09CY), its second factor.
* [Stacks Project, Tag 08SR](https://stacks.math.columbia.edu/tag/08SR), the standard resolution.
* [Stacks Project, Tag 00VH](https://stacks.math.columbia.edu/tag/00VH), the definition of a site,
  whose axiom (3) is what `PreservesCoveringPullbacks` transcribes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.SheafOfModules (PrincipalPartsSequence principalPartsSequenceOfSite
  moduleSheaves)
open Stacks.SimplicialModules (projectionTopology simplicialCommRingSheaf
  simplicialCommRingSheafMap projectionCommRing projectionRingSheaf augmentationCommRingMap
  projection)

universe u

namespace CategoryTheory.Sheaf

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [(projection C).IsCocontinuous (Stacks.SimplicialModules.projectionTopology C J) J]
  [Stacks.Sites.PreservesCoveringPullbacks
    (Stacks.SimplicialModules.projectionTopology C J) (projection C)]
  {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B)

/-- `P_•`, the standard resolution, as a simplicial sheaf of commutative rings. -/
abbrev resolutionCommRing : SimplicialObject (Sheaf J CommRingCat.{u}) :=
  (standardResolution J f).left ⋙ Under.forget A

/-- The augmentation `ε : P_• ⟶ ℬ`, of simplicial sheaves of commutative rings. -/
def resolutionCommAugmentation :
    resolutionCommRing J f ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B :=
  Functor.whiskerRight (standardResolution J f).hom (Under.forget A) ≫
    (Functor.constComp _ _ _).hom

/-- The structure maps `𝒜 ⟶ P_n`, as a map out of the constant simplicial sheaf of rings. -/
def resolutionCommBase :
    (Functor.const SimplexCategoryᵒᵖ).obj A ⟶ resolutionCommRing J f where
  app n := ((standardResolution J f).left.obj n).hom
  naturality i j g := by
    dsimp
    rw [Category.id_comp]
    exact (Under.w ((standardResolution J f).left.map g)).symm

/-- The sheaf of rings underlying `ℬ`. -/
abbrev targetRing : Sheaf J RingCat.{u} :=
  Stacks.SheafOfModules.Tensor.ringSheaf B

/-! ### The principal-parts sequence on `Δ × C` -/

/-- `π^{-1}𝒜` on `Δ × C`, written as the sheaf of rings of the constant simplicial sheaf of
commutative rings `𝒜`. -/
abbrev simplicialBase : Sheaf (projectionTopology C J) CommRingCat.{u} :=
  simplicialCommRingSheaf J ((Functor.const SimplexCategoryᵒᵖ).obj A)

/-- `𝒫`, the sheaf of commutative rings on `Δ × C` associated to the standard resolution. -/
abbrev simplicialResolution : Sheaf (projectionTopology C J) CommRingCat.{u} :=
  simplicialCommRingSheaf J (resolutionCommRing J f)

/-- The map `π^{-1}𝒜 ⟶ 𝒫` on `Δ × C` given by the `𝒜`-algebra structures of the terms of the
standard resolution. -/
def simplicialBaseMap : simplicialBase J (A := A) ⟶ simplicialResolution J f :=
  simplicialCommRingSheafMap J (resolutionCommBase J f)

/-- **The sequence of first principal parts of `𝒫` over `π^{-1}𝒜`, on the site `Δ × C`.** Its
restriction to the fibre over a simplicial degree `n` is the sequence of Tag 09DG for the ring map
`𝒜 ⟶ P_n`. -/
abbrev simplicialPrincipalParts :
    PrincipalPartsSequence.{u, u, u, u} (simplicialBase J (A := A)) (simplicialResolution J f)
      (simplicialBaseMap J f) :=
  principalPartsSequenceOfSite.{u, u, u, u} _ _ (simplicialBaseMap J f)

/-! ### The coefficient module on `Δ × C` -/

/-- `π^{-1}ℱ`, a sheaf of `ℬ`-modules on `C` read on `Δ × C`. -/
abbrev projectionCoefficients (F : SheafOfModules.{u} (targetRing J (B := B))) :
    SheafOfModules.{u} (_root_.Stacks.SheafOfModules.inverseImageRing
      (projectionTopology C J) J (projection C) (targetRing J (B := B))) :=
  (_root_.Stacks.SheafOfModules.inverseImage.{u} (projectionTopology C J) J (projection C)
    (targetRing J (B := B))).obj F

/-- `ℱ` read as a sheaf of `𝒫`-modules on `Δ × C`, through the augmentation `𝒫 ⟶ π^{-1}ℬ`. -/
abbrev simplicialCoefficients (F : SheafOfModules.{u} (targetRing J (B := B))) :
    moduleSheaves.{u, u, u, u} (simplicialResolution J f) :=
  (SheafOfModules.restrictScalars ((sheafCompose (projectionTopology C J)
    (forget₂ CommRingCat.{u} RingCat.{u})).map
      (augmentationCommRingMap J (resolutionCommAugmentation J f)))).obj
    (projectionCoefficients J (B := B) F)

/-! ### The short exact sequence of simplicial `P_•`-modules -/

/-- The inclusion `Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 ℱ ⟶ P¹_{𝒫/π^{-1}𝒜}(ℱ)` followed by the projection
`P¹_{𝒫/π^{-1}𝒜}(ℱ) ⟶ ℱ` vanishes. -/
theorem simplicialPrincipalParts_inclusion_comp_projection
    (F : SheafOfModules.{u} (targetRing J (B := B))) :
    (simplicialPrincipalParts J f).inclusion.app (simplicialCoefficients J f F) ≫
      (simplicialPrincipalParts J f).projection.app (simplicialCoefficients J f F) = 0 :=
  ((simplicialPrincipalParts J f).shortExact (simplicialCoefficients J f F)).elim fun h _ => h

/-- **The extension of principal parts of the standard resolution, as a sequence of simplicial
`P_•`-modules**: `0 ⟶ Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 ℱ ⟶ P¹_{𝒫/π^{-1}𝒜}(ℱ) ⟶ ℱ ⟶ 0` on `Δ × C`. -/
def simplicialPrincipalPartsShortComplex (F : SheafOfModules.{u} (targetRing J (B := B))) :
    ShortComplex (moduleSheaves.{u, u, u, u} (simplicialResolution J f)) :=
  ShortComplex.mk _ _ (simplicialPrincipalParts_inclusion_comp_projection J f F)

/-- **Stacks 09DG, as a sequence of simplicial `P_•`-modules.** The sequence of first principal
parts of the standard resolution is short exact on `Δ × C`; restricted to the fibre over a
simplicial degree `n` it is the sequence of Tag 09DG for the ring map `𝒜 ⟶ P_n`. -/
theorem simplicialPrincipalPartsShortComplex_shortExact
    (F : SheafOfModules.{u} (targetRing J (B := B))) :
    (simplicialPrincipalPartsShortComplex J f F).ShortExact :=
  ((simplicialPrincipalParts J f).shortExact (simplicialCoefficients J f F)).elim fun _ h => h

/-! ### `Lπ_!` and the Atiyah triangle -/

/-- **`Lπ_! : D(P_•) ⟶ D(ℬ)` of Tag 09D3** at the standard resolution: derived extension of scalars
along the augmentation, followed by the derived lower shriek of `π : Δ × C ⥤ C`. -/
def resolutionLowerShriek :
    DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Stacks.Cohomology.ringedTopos (projectionTopology C J)
            (simplicialResolution J f)).O)) ⥤
      DerivedCategory (SheafOfModules.{u} (targetRing J (B := B))) :=
  Stacks.SimplicialModules.derivedBaseChangeToProjectionRing J (resolutionCommAugmentation J f) ⋙
    Stacks.SimplicialModules.derivedProjectionLowerShriek C J (targetRing J (B := B))

/-- `Lπ_!` commutes with the shift. -/
instance resolutionLowerShriek_commShift : (resolutionLowerShriek J f).CommShift ℤ := by
  unfold resolutionLowerShriek; infer_instance

/-- `Lπ_!` is a triangulated functor. -/
instance resolutionLowerShriek_isTriangulated : (resolutionLowerShriek J f).IsTriangulated := by
  unfold resolutionLowerShriek; infer_instance

/-- The **Atiyah triangle** of a sheaf of `ℬ`-modules: the image under `Lπ_!` of the triangle of
the short exact sequence of principal parts. -/
def resolutionAtiyahTriangle (F : SheafOfModules.{u} (targetRing J (B := B))) :
    Triangle (DerivedCategory (SheafOfModules.{u} (targetRing J (B := B)))) :=
  (resolutionLowerShriek J f).mapTriangle.obj
    (simplicialPrincipalPartsShortComplex_shortExact J f F).singleTriangle

/-- The Atiyah triangle is distinguished. -/
theorem resolutionAtiyahTriangle_distinguished (F : SheafOfModules.{u} (targetRing J (B := B))) :
    resolutionAtiyahTriangle J f F ∈ distinguishedTriangles :=
  (resolutionLowerShriek J f).map_distinguished _
    (simplicialPrincipalPartsShortComplex_shortExact J f F).singleTriangle_distinguished

/-- The sections of the coefficient module over `(n, U)` are the sections of `ℱ` over `U`. -/
theorem simplicialCoefficients_sections (F : SheafOfModules.{u} (targetRing J (B := B)))
    (n : SimplexCategory) (U : Cᵒᵖ) :
    ((simplicialCoefficients J f F).val.obj (Opposite.op (n, U.unop)) : Type u) =
      (F.val.obj U : Type u) := rfl

/-- The third term of the sequence of principal parts is the coefficient module, sectionwise. -/
theorem simplicialPrincipalPartsShortComplex_X₃_sections
    (F : SheafOfModules.{u} (targetRing J (B := B))) (n : SimplexCategory) (U : Cᵒᵖ) :
    ((simplicialPrincipalPartsShortComplex J f F).X₃.val.obj (Opposite.op (n, U.unop)) :
      Type u) = (F.val.obj U : Type u) := rfl

/-- The first term of the sequence of principal parts is the sheaf of relative differentials of `𝒫`
over `π^{-1}𝒜` on `Δ × C`, tensored with the coefficient module. -/
theorem simplicialPrincipalPartsShortComplex_X₁ (F : SheafOfModules.{u} (targetRing J (B := B))) :
    (simplicialPrincipalPartsShortComplex J f F).X₁ =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (simplicialResolution J f)).flip.obj
        (AlgebraicGeometry.SheafOfModules.derivationsFunctor.{u} (simplicialBase J (A := A))
          (simplicialResolution J f) (simplicialBaseMap J f)).coreprX).obj
        (simplicialCoefficients J f F) := rfl

/-- The first term of the Atiyah triangle is `Lπ_!(Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 ℱ)`. -/
theorem resolutionAtiyahTriangle_obj₁ (F : SheafOfModules.{u} (targetRing J (B := B))) :
    (resolutionAtiyahTriangle J f F).obj₁ = (resolutionLowerShriek J f).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (simplicialPrincipalPartsShortComplex J f F).X₁) := rfl

/-- The second term of the Atiyah triangle is `Lπ_!(P¹_{𝒫/π^{-1}𝒜}(ℱ))`, which is the middle term
the source displays. -/
theorem resolutionAtiyahTriangle_obj₂ (F : SheafOfModules.{u} (targetRing J (B := B))) :
    (resolutionAtiyahTriangle J f F).obj₂ = (resolutionLowerShriek J f).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (simplicialPrincipalPartsShortComplex J f F).X₂) := rfl

/-- The third term of the Atiyah triangle is `Lπ_!(ℱ)`. -/
theorem resolutionAtiyahTriangle_obj₃ (F : SheafOfModules.{u} (targetRing J (B := B))) :
    (resolutionAtiyahTriangle J f F).obj₃ = (resolutionLowerShriek J f).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (simplicialPrincipalPartsShortComplex J f F).X₃) := rfl

end CategoryTheory.Sheaf

end
