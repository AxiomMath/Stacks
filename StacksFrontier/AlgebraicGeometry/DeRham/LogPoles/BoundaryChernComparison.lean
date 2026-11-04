module

public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.ResidueBoundary
public import StacksCore.Tactic.StacksAttribute

/-!
# The boundary map of the log poles sequence against cup product by the first Chern class

Let `f : X → S` be a morphism of schemes and let `Y ⊆ X` be an effective Cartier divisor for
which the de Rham complex of log poles is defined. Three morphisms of degree two are attached to
this situation.

* `δ : Ω^•_{Y/S} ⟶ Ω^•_{X/S}[2]`, the boundary map of the short exact sequence of Tag 0FMW,
  taken in the shifted presentation `0 → Ω^•_{X/S}[1] → Ω^•_{X/S}(log Y)[1] → Ω^•_{Y/S} → 0`
  with which the proof of Tag 0FUQ begins.
* `ξ' : Ω^•_{X/S} ⟶ Ω^•_{X/S}[2]`, the morphism of Tag 0FU7 attached to
  `ξ = c₁^{dR}(𝒪_X(-Y))`, which Tag 0FUG presents as the boundary map of the residue sequence
  of Tag 0FUF for the line bundle `ℒ = 𝒪_X(-Y)` on `X`.
* `ζ' : Ω^•_{Y/S} ⟶ Ω^•_{Y/S}[2]`, the morphism of Tag 0FU7 attached to
  `ζ = c₁^{dR}(𝒪_X(-Y)|_Y)`, which Tag 0FUG presents as the boundary map of the residue sequence
  of Tag 0FUF for the restricted line bundle `ℒ|_Y` on `Y`.

**Tag 0FUQ** says that the square built from `ξ'`, `ζ'` and the restriction of forms
`Ω^•_{X/S} ⟶ Ω^•_{Y/S}`, cut by `δ` along its diagonal, commutes: both triangles commute, and
hence so does the square.

The Stacks proof of each triangle is the functoriality of boundary maps along a morphism of short
exact sequences, the morphism being given by an explicit formula on local sections
(`ω' + d log (s) ∧ ω ↦ ω' + d log (t) ∧ ω` for the upper left triangle and
`ω' + d log (t) ∧ ω ↦ ω'|_Y + d log (t|_Y) ∧ ω|_Y` for the lower right one). That functoriality
is what this file proves and applies.

## Main definitions

* `Stacks.ShiftedBoundary.Sequence`: a short exact sequence of cochain complexes of the shape
  `0 → P[1] → M → N → 0`, the shifted presentation in which the proof of Tag 0FUQ reads both the
  log poles sequence of Tag 0FMW and the residue sequences of Tag 0FUF.
* `Stacks.ShiftedBoundary.Sequence.boundary`: **its boundary map `N ⟶ P[2]`** in the derived
  category, Mathlib's `DerivedCategory.triangleOfSESδ` with the localization functor commuted
  past the translation on `P[1]`.
* `Stacks.ShiftedBoundary.Morphism`: a morphism between two such sequences over a pair of maps on
  the outer terms.
* `AlgebraicGeometry.SheafOfModules.LogPolesResidueData`: **the parameter**, the three sequences
  of Tag 0FUQ together with the two morphisms between them that the Stacks proof constructs.

## Main results

* `Stacks.ShiftedBoundary.Morphism.boundary_naturality`: **the boundary maps of two shifted short
  exact sequences are compatible with a morphism between them.**
* `AlgebraicGeometry.SheafOfModules.LogPolesResidueData.ambientChernBoundary_eq`: **Tag 0FUQ,
  upper left triangle.** `ξ' = δ ∘ (restriction of forms)`.
* `AlgebraicGeometry.SheafOfModules.LogPolesResidueData.boundary_comp_shiftedRestriction`:
  **Tag 0FUQ, lower right triangle.** `(restriction of forms)[2] ∘ δ = ζ'`.
* `AlgebraicGeometry.SheafOfModules.LogPolesResidueData.commSq_chernBoundary`: **Tag 0FUQ, the
  square.** `(restriction of forms)[2] ∘ ξ' = ζ' ∘ (restriction of forms)`.
* `AlgebraicGeometry.SheafOfModules.LogPolesResidueData.deRhamClassDerivedMorphism_eq` and
  `AlgebraicGeometry.SheafOfModules.LogPolesResidueData.commSq_deRhamClassDerivedMorphism`: the
  same two statements with `ξ'` named as the morphism of Tag 0FU7 attached to
  `c₁^{dR}(𝒪_X(-Y))`, which is how Tag 0FUQ states it.

## Implementation notes

**The shifted presentation.** Mathlib's connecting morphism of a short exact sequence
`0 → Z₁ → Z₂ → Z₃ → 0` of cochain complexes is a map `Q Z₃ ⟶ (Q Z₁)[1]`. For a sequence whose
left-hand term is already a translate `P[1]` this is a map `Q N ⟶ (Q (P[1]))[1]`, and
`Stacks.ShiftedBoundary.Sequence.boundary` turns it into a map `Q N ⟶ (Q P)[2]` using the
commutation of the localization functor with the translation and the canonical isomorphism
`(Z[1])[1] ≅ Z[2]`. No sign is introduced. This is the presentation the source uses when it says
"more precisely, we define `δ` as the boundary map corresponding to the shifted short exact
sequence", and it is also the presentation in which the proof of Tag 0FUG reads `ξ'`.

**What is carried, and why.** Everything in
`AlgebraicGeometry.SheafOfModules.LogPolesResidueData` is carried, because the library has none
of it in global form.

* The de Rham complex `Ω^•_{Y/S}` of the divisor, read as a complex of sheaves of `A`-modules on
  the ambient space, and the restriction of forms `Ω^•_{X/S} ⟶ Ω^•_{Y/S}`. The source reads
  `Ω^p_{Y/S}` as a quasi-coherent `𝒪_X`-module throughout Section 50.15, pushing forward along
  the closed immersion `Y → X`; that pushforward is not in the library.
* The log poles sequence of Tag 0FMW in its shifted global form. What the library has is the
  affine local computation at the ring level,
  `Stacks.LogPoles.shortExact_map_eval_logShortComplex`, and the reindexing of it to `ℤ` in
  `StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.ResidueConnecting`, whose implementation notes
  record that the sheaf-level sequence does not exist in the library. Carrying the sequence is
  also why the hypotheses of Tag 0FUQ — that `Y` is an effective Cartier divisor and that the de
  Rham complex of log poles is defined for it, `AlgebraicGeometry.Scheme.Hom`
  `.HasLogPolesDeRhamComplex` of Tag 0FMV — do not appear as binders: they are the hypotheses
  under which the source produces the sequence, and here the sequence itself is the input.
* The two residue sequences of Tag 0FUF, for `ℒ = 𝒪_X(-Y)` on `X` and for `ℒ|_Y` on `Y`, again
  in shifted global form. The library carries the same sequence as a hypothesis in
  `AlgebraicGeometry.SheafOfModules.DeRhamResidueSequence` for exactly this reason.
* The two morphisms of short exact sequences. The source constructs them by a formula on local
  sections and observes that "the constructions of the maps in Lemmas 50.10.2 and 50.15.2 match
  exactly"; since the three sequences are themselves carried, no map between them can be
  constructed, so they are carried too. They are the only input to the proof of the two
  triangles, and both of their commutation fields are used.

**What is proved.** The commutativity of both triangles and of the square, from the
functoriality of Mathlib's connecting morphism, `DerivedCategory.triangleOfSESδ_naturality`,
transported across the shift bookkeeping of
`Stacks.ShiftedBoundary.Sequence.boundary`. The square is deduced from the two triangles exactly
as in the source.

**`ξ'` and `ζ'` as morphisms of Tag 0FU7.** For the ambient space the identification of the
boundary map with the morphism of Tag 0FU7 attached to `c₁^{dR}(ℒ)` is Tag 0FUG, and
`AlgebraicGeometry.SheafOfModules.LogPolesResidueData.deRhamClassDerivedMorphism_eq` performs it
through the uniqueness of Tag 0FU7,
`AlgebraicGeometry.SheafOfModules.eq_deRhamClassDerivedMorphism`, carrying the two inputs that
the library's own Tag 0FUG,
`AlgebraicGeometry.SheafOfModules.DeRhamResidueSequence.boundary_eq_deRhamClassDerivedMorphism`,
carries as well: that the boundary map lifts to the derived category of right differential graded
`Ω^•_{X/S}`-modules, and that its value at the unit is `c₁^{dR}(ℒ)`.

For the divisor the same identification is **not** covered here. The morphism of Tag 0FU7 is
constructed from the de Rham differential graded algebra of the ambient data `B`, `D`, so there
is no such morphism for the complex `Ω^•_{Y/S}` read on the ambient space, and the comparison
along the closed immersion that would supply one is not in the library. Accordingly `ζ'` appears
below only as the boundary map of the residue sequence of Tag 0FUF for `ℒ|_Y`, which is the
description Tag 0FUG gives of it and the description the proof of Tag 0FUQ uses.

## References

* [Stacks Project, Tag 0FUQ](https://stacks.math.columbia.edu/tag/0FUQ)
* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV)
* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF)
* [Stacks Project, Tag 0FUG](https://stacks.math.columbia.edu/tag/0FUG)
* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Opposite Pretriangulated TopologicalSpace

universe w v u

namespace Stacks.ShiftedBoundary

open DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-! ### Shifted short exact sequences and their boundary maps -/

/-- A short exact sequence of cochain complexes whose left-hand term is a translate,

`0 → P[1] → M → N → 0`.

This is the shifted presentation in which the proof of Stacks Tag 0FUQ reads both the log poles
sequence of Tag 0FMW and the residue sequences of Tag 0FUF, so that the boundary map has source
`N` and target `P[2]`. -/
structure Sequence (P N : CochainComplex C ℤ) where
  /-- The middle term of the sequence. -/
  middle : CochainComplex C ℤ
  /-- The injection `P[1] ⟶ M`. -/
  incl : P⟦(1 : ℤ)⟧ ⟶ middle
  /-- The surjection `M ⟶ N`. -/
  res : middle ⟶ N
  /-- The two maps compose to zero. -/
  incl_comp_res : incl ≫ res = 0
  /-- The sequence is short exact. -/
  shortExact : (ShortComplex.mk incl res incl_comp_res).ShortExact

namespace Sequence

variable {P N : CochainComplex C ℤ} (S : Sequence P N)

/-- A shifted short exact sequence read as a short complex of cochain complexes. -/
abbrev shortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk S.incl S.res S.incl_comp_res

/-- **The boundary map `N ⟶ P[2]`** of a shifted short exact sequence `0 → P[1] → M → N → 0` in
the derived category: Mathlib's connecting morphism `DerivedCategory.triangleOfSESδ`, whose target
is `(Q (P[1]))[1]`, with the localization functor commuted past the translation on `P[1]` and the
two translations by one added up to a translation by two. No sign is introduced. -/
def boundary : Q.obj N ⟶ (Q.obj P)⟦(2 : ℤ)⟧ :=
  triangleOfSESδ S.shortExact ≫
    ((Q.commShiftIso (1 : ℤ)).hom.app P)⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd' (DerivedCategory C) (1 : ℤ) 1 2 (by omega)).inv.app (Q.obj P)

end Sequence

/-! ### Morphisms of shifted short exact sequences -/

/-- A morphism between two shifted short exact sequences `0 → P₁[1] → M₁ → N₁ → 0` and
`0 → P₂[1] → M₂ → N₂ → 0` over given maps `p : P₁ ⟶ P₂` and `n : N₁ ⟶ N₂` on the outer terms:
a map on the middle terms making both squares commute. -/
structure Morphism {P₁ N₁ P₂ N₂ : CochainComplex C ℤ} (S₁ : Sequence P₁ N₁)
    (S₂ : Sequence P₂ N₂) (p : P₁ ⟶ P₂) (n : N₁ ⟶ N₂) where
  /-- The map on the middle terms. -/
  mid : S₁.middle ⟶ S₂.middle
  /-- The square on the left commutes. -/
  comm_incl : p⟦(1 : ℤ)⟧' ≫ S₂.incl = S₁.incl ≫ mid
  /-- The square on the right commutes. -/
  comm_res : mid ≫ S₂.res = S₁.res ≫ n

namespace Morphism

variable {P₁ N₁ P₂ N₂ : CochainComplex C ℤ} {S₁ : Sequence P₁ N₁} {S₂ : Sequence P₂ N₂}
  {p : P₁ ⟶ P₂} {n : N₁ ⟶ N₂}

/-- A morphism of shifted short exact sequences read as a morphism of short complexes, the map on
the left-hand terms being the translate `p[1]`. -/
def homShortComplex (f : Morphism S₁ S₂ p n) : S₁.shortComplex ⟶ S₂.shortComplex where
  τ₁ := p⟦(1 : ℤ)⟧'
  τ₂ := f.mid
  τ₃ := n
  comm₁₂ := f.comm_incl
  comm₂₃ := f.comm_res

/-- **The boundary maps of two shifted short exact sequences are compatible with a morphism
between them**: for a morphism over `p : P₁ ⟶ P₂` and `n : N₁ ⟶ N₂`,

`δ₁ ≫ p[2] = n ≫ δ₂`

in the derived category. This is the functoriality that the proof of Stacks Tag 0FUQ invokes for
each of its two triangles, deduced from Mathlib's
`DerivedCategory.triangleOfSESδ_naturality` by transporting it across the identifications that
turn the connecting morphism into a map `N ⟶ P[2]`. -/
theorem boundary_naturality (f : Morphism S₁ S₂ p n) :
    S₁.boundary ≫ (Q.map p)⟦(2 : ℤ)⟧' = Q.map n ≫ S₂.boundary := by
  have hnat := triangleOfSESδ_naturality S₁.shortExact S₂.shortExact (homShortComplex f)
  have hτ₁ : (homShortComplex f).τ₁ = p⟦(1 : ℤ)⟧' := rfl
  have hτ₃ : (homShortComplex f).τ₃ = n := rfl
  rw [hτ₁, hτ₃] at hnat
  have tail :
      ((Q.commShiftIso (1 : ℤ)).hom.app P₁)⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' (DerivedCategory C) (1 : ℤ) 1 2 (by omega)).inv.app (Q.obj P₁) ≫
            (Q.map p)⟦(2 : ℤ)⟧' =
        (Q.map (p⟦(1 : ℤ)⟧'))⟦(1 : ℤ)⟧' ≫ ((Q.commShiftIso (1 : ℤ)).hom.app P₂)⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' (DerivedCategory C) (1 : ℤ) 1 2 (by omega)).inv.app (Q.obj P₂) := by
    have hadd := (shiftFunctorAdd' (DerivedCategory C) (1 : ℤ) 1 2
      (by omega)).inv.naturality (Q.map p)
    dsimp only [Functor.comp_map] at hadd
    rw [← hadd, ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      ← Q.commShiftIso_hom_naturality p (1 : ℤ)]
  dsimp only [Sequence.boundary]
  rw [Category.assoc, Category.assoc, tail, ← Category.assoc, ← Category.assoc, hnat,
    Category.assoc, Category.assoc]

/-- The boundary map of a shifted short exact sequence factors through that of a second one with
the same left-hand term, along a morphism which is the identity there: `δ₁ = n ≫ δ₂`. -/
theorem boundary_eq_comp_boundary {P : CochainComplex C ℤ} {S₁ : Sequence P N₁}
    {S₂ : Sequence P N₂} (f : Morphism S₁ S₂ (𝟙 P) n) :
    S₁.boundary = Q.map n ≫ S₂.boundary := by
  simpa using boundary_naturality f

/-- The boundary map of a shifted short exact sequence composed with a translate recovers that of
a second one with the same right-hand term, along a morphism which is the identity there:
`δ₁ ≫ p[2] = δ₂`. -/
theorem boundary_comp_eq_boundary {N : CochainComplex C ℤ} {S₁ : Sequence P₁ N}
    {S₂ : Sequence P₂ N} (f : Morphism S₁ S₂ p (𝟙 N)) :
    S₁.boundary ≫ (Q.map p)⟦(2 : ℤ)⟧' = S₂.boundary := by
  simpa using boundary_naturality f

end Morphism

end Stacks.ShiftedBoundary

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

open Stacks.ShiftedBoundary

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-! ### The three sequences of Tag 0FUQ and the two morphisms between them -/

/-- **The input of Stacks Tag 0FUQ, as a hypothesis.** For an effective Cartier divisor `Y ⊆ X`
for which the de Rham complex of log poles is defined, this packages the three short exact
sequences the proof of Tag 0FUQ uses, each in the shifted presentation
`0 → P[1] → M → N → 0`, together with the two morphisms between them that the proof constructs
from an explicit formula on local sections.

None of this is in the library in global form; see the implementation notes of this file. The de
Rham complex of the divisor is read as a complex of sheaves of `A`-modules on the ambient space,
as the source reads `Ω^p_{Y/S}` as a quasi-coherent `𝒪_X`-module throughout Section 50.15. -/
structure LogPolesResidueData where
  /-- `Ω^•_{Y/S}`, the de Rham complex of the divisor, read on the ambient space. -/
  divisorDeRham : CochainComplex (_root_.SheafOfModules.{u} (underlyingRingSheaf A)) ℤ
  /-- The restriction of relative forms `Ω^•_{X/S} ⟶ Ω^•_{Y/S}`, the horizontal arrow of the
  square of Tag 0FUQ. -/
  restriction : deRhamComplexInt B D ⟶ divisorDeRham
  /-- **The log poles sequence of Tag 0FMW**, shifted:
  `0 → Ω^•_{X/S}[1] → Ω^•_{X/S}(log Y)[1] → Ω^•_{Y/S} → 0`. Its boundary map is the `δ` of Tag
  0FUQ. -/
  logPoles : Sequence (C := _root_.SheafOfModules.{u} (underlyingRingSheaf A))
    (deRhamComplexInt B D) divisorDeRham
  /-- **The residue sequence of Tag 0FUF for `ℒ = 𝒪_X(-Y)` on `X`**, shifted:
  `0 → Ω^•_{X/S}[1] → Ω^•_{L^⋆/S,0}[1] → Ω^•_{X/S} → 0`. By Tag 0FUG its boundary map is the
  `ξ'` of Tag 0FUQ. -/
  ambientChern : Sequence (C := _root_.SheafOfModules.{u} (underlyingRingSheaf A))
    (deRhamComplexInt B D) (deRhamComplexInt B D)
  /-- **The residue sequence of Tag 0FUF for the restriction `ℒ|_Y` to the divisor**, shifted:
  `0 → Ω^•_{Y/S}[1] → Ω^•_{L̄^⋆/S,0}[1] → Ω^•_{Y/S} → 0`. By Tag 0FUG its boundary map is the
  `ζ'` of Tag 0FUQ. -/
  divisorChern : Sequence (C := _root_.SheafOfModules.{u} (underlyingRingSheaf A))
    divisorDeRham divisorDeRham
  /-- **The morphism of short exact sequences of the upper left triangle**, from the residue
  sequence of `ℒ` on `X` to the log poles sequence, over the identity of `Ω^•_{X/S}` and the
  restriction of forms. The source defines its middle arrow by
  `ω' + d log (s) ∧ ω ↦ ω' + d log (t) ∧ ω`, for `s` a local generator of `ℒ` and `t` the
  corresponding local equation of `Y`. -/
  ambientMap : Morphism ambientChern logPoles (𝟙 (deRhamComplexInt B D)) restriction
  /-- **The morphism of short exact sequences of the lower right triangle**, from the log poles
  sequence to the residue sequence of `ℒ|_Y` on `Y`, over the restriction of forms and the
  identity of `Ω^•_{Y/S}`. The source defines its middle arrow by
  `ω' + d log (t) ∧ ω ↦ ω'|_Y + d log (t|_Y) ∧ ω|_Y`. -/
  divisorMap : Morphism logPoles divisorChern restriction (𝟙 divisorDeRham)

namespace LogPolesResidueData

variable {B D} (d : LogPolesResidueData B D)

/-- **The boundary map `δ : Ω^•_{Y/S} ⟶ Ω^•_{X/S}[2]`** of Stacks Tag 0FUQ: the boundary map of
the shifted log poles sequence of Tag 0FMW. -/
abbrev boundary : DerivedCategory.Q.obj d.divisorDeRham ⟶ (deRhamDerivedObject B D)⟦(2 : ℤ)⟧ :=
  d.logPoles.boundary

/-- **The map `ξ' : Ω^•_{X/S} ⟶ Ω^•_{X/S}[2]`** of Stacks Tag 0FUQ, in the description Tag 0FUG
gives of it: the boundary map of the shifted residue sequence of Tag 0FUF for `ℒ = 𝒪_X(-Y)` on
`X`. -/
abbrev ambientChernBoundary : deRhamDerivedObject B D ⟶ (deRhamDerivedObject B D)⟦(2 : ℤ)⟧ :=
  d.ambientChern.boundary

/-- **The map `ζ' : Ω^•_{Y/S} ⟶ Ω^•_{Y/S}[2]`** of Stacks Tag 0FUQ, in the description Tag 0FUG
gives of it: the boundary map of the shifted residue sequence of Tag 0FUF for the restriction
`ℒ|_Y` of `ℒ = 𝒪_X(-Y)` to the divisor. -/
abbrev divisorChernBoundary :
    DerivedCategory.Q.obj d.divisorDeRham ⟶ (DerivedCategory.Q.obj d.divisorDeRham)⟦(2 : ℤ)⟧ :=
  d.divisorChern.boundary

/-- **Stacks Project, Tag 0FUQ, the upper left triangle.**

`ξ' = δ ∘ (restriction of forms)`

in `D(f^{-1}𝒪_S)`: the map of Tag 0FU7 for `c₁^{dR}(𝒪_X(-Y))`, read through Tag 0FUG as the
boundary map of the residue sequence of Tag 0FUF for `𝒪_X(-Y)`, factors through the boundary map
of the log poles sequence of Tag 0FMW along the restriction of relative forms
`Ω^•_{X/S} ⟶ Ω^•_{Y/S}`.

This is the functoriality of boundary maps along the morphism of short exact sequences
`AlgebraicGeometry.SheafOfModules.LogPolesResidueData.ambientMap`, whose left arrow is the
identity. -/
@[stacks 0FUQ "upper left triangle of the diagram: the map of 0FU7 for c_1^dR(O_X(-Y)), in the
description 0FUG gives of it as the boundary map of the residue sequence of 0FUF, is the boundary
map of the log poles sequence of 0FMW composed with the restriction of relative forms; the three
short exact sequences in global form and the two morphisms between them that the source builds
from a formula on local sections are carried as the explicit named hypothesis
LogPolesResidueData, the library having none of them globally"]
theorem ambientChernBoundary_eq :
    d.ambientChernBoundary = DerivedCategory.Q.map d.restriction ≫ d.boundary :=
  Morphism.boundary_eq_comp_boundary d.ambientMap

/-- **Stacks Project, Tag 0FUQ, the lower right triangle.**

`(restriction of forms)[2] ∘ δ = ζ'`

in `D(f^{-1}𝒪_S)`: the boundary map of the log poles sequence of Tag 0FMW, followed by the
twofold translate of the restriction of relative forms, is the map of Tag 0FU7 for
`c₁^{dR}(𝒪_X(-Y)|_Y)`, read through Tag 0FUG as the boundary map of the residue sequence of Tag
0FUF for `𝒪_X(-Y)|_Y`.

This is the functoriality of boundary maps along the morphism of short exact sequences
`AlgebraicGeometry.SheafOfModules.LogPolesResidueData.divisorMap`, whose right arrow is the
identity. -/
@[stacks 0FUQ "lower right triangle of the diagram: the boundary map of the log poles sequence of
0FMW, followed by the twofold translate of the restriction of relative forms, is the map of 0FU7
for c_1^dR(O_X(-Y)|_Y) in the description 0FUG gives of it as the boundary map of the residue
sequence of 0FUF on the divisor; the sequences and the two morphisms between them are carried as
the explicit named hypothesis LogPolesResidueData"]
theorem boundary_comp_shiftedRestriction :
    d.boundary ≫ (DerivedCategory.Q.map d.restriction)⟦(2 : ℤ)⟧' = d.divisorChernBoundary :=
  Morphism.boundary_comp_eq_boundary d.divisorMap

/-- **Stacks Project, Tag 0FUQ, the square.**

`(restriction of forms)[2] ∘ ξ' = ζ' ∘ (restriction of forms)`

in `D(f^{-1}𝒪_S)`: the square built from the maps of Tag 0FU7 for `c₁^{dR}(𝒪_X(-Y))` and for its
restriction to the divisor, and from the restriction of relative forms in both degrees, commutes.
As in the source this is deduced from the commutativity of the two triangles cut out by the
boundary map `δ` of the log poles sequence of Tag 0FMW along the diagonal. -/
@[stacks 0FUQ "the square of the diagram, deduced from the two triangles exactly as in the
source: the restriction of relative forms, in degree zero and in degree two, carries the map of
0FU7 for c_1^dR(O_X(-Y)) to the one for its restriction to the divisor, both read through 0FUG as
boundary maps of residue sequences of 0FUF; the sequences and the two morphisms between them are
carried as the explicit named hypothesis LogPolesResidueData"]
theorem commSq_chernBoundary :
    d.ambientChernBoundary ≫ (DerivedCategory.Q.map d.restriction)⟦(2 : ℤ)⟧' =
      DerivedCategory.Q.map d.restriction ≫ d.divisorChernBoundary := by
  rw [d.ambientChernBoundary_eq, Category.assoc, d.boundary_comp_shiftedRestriction]

/-! ### The upper left triangle with `ξ'` named as the map of Tag 0FU7 -/

section Chern

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

/-- **Stacks Project, Tag 0FUQ, the upper left triangle, with `ξ'` named as in the statement of
Tag 0FUQ.**

`ξ' = δ ∘ (restriction of forms)`

in `D(f^{-1}𝒪_S)`, where `ξ'` is the morphism of Tag 0FU7 attached to the de Rham
first Chern class `ξ = c₁^{dR}(ℒ)` of the invertible module `ℒ`, which for Tag 0FUQ is
`𝒪_X(-Y)`, and `δ` is the boundary map of the shifted log poles sequence of Tag 0FMW.

The identification of the boundary map of the residue sequence of Tag 0FUF with `ξ'` is Tag 0FUG,
and it is made here through the uniqueness of Tag 0FU7,
`AlgebraicGeometry.SheafOfModules.eq_deRhamClassDerivedMorphism`, with the same two inputs that
the library's Tag 0FUG carries: `hlift`, that the boundary map lifts to the derived category of
right differential graded `Ω^•_{X/S}`-modules, and `hev`, that its value at the unit is
`c₁^{dR}(ℒ)`. The third input, `realizationComparison`, transports the first Chern class from the
abelian-sheaf realization of de Rham cohomology, in which it is constructed, to the
sheaf-of-modules realization in which the classes of Tag 0FU7 live. -/
@[stacks 0FUQ "upper left triangle with xi' named as the map of 0FU7 attached to the de Rham
first Chern class of O_X(-Y), the identification of 0FUG being made through the uniqueness in
0FU7; carried as explicit named hypotheses are LogPolesResidueData (the three short exact
sequences in global form and the two morphisms between them), together with the three inputs the
library's own 0FUG carries, namely hlift, hev and realizationComparison"]
theorem deRhamClassDerivedMorphism_eq (c : DeRhamDerivedModuleCorrespondence B D)
    (realizationComparison : deRhamCohomologyAbelian B D 2 →+ deRhamCohomology B D 2)
    (L : _root_.SheafOfModules.{u} (structureSheaf X.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L)
    (hlift : ∃ g : deRhamDerivedRegular B D ⟶ deRhamDerivedRegularShift B D 2,
      c.forget 2 g = d.ambientChernBoundary)
    (hev : c.evalOne 2 d.ambientChernBoundary =
      realizationComparison (deRhamFirstChernClassAbelianOf B D L hL)) :
    deRhamClassDerivedMorphism B D c 2
        (realizationComparison (deRhamFirstChernClassAbelianOf B D L hL)) =
      DerivedCategory.Q.map d.restriction ≫ d.boundary :=
  (eq_deRhamClassDerivedMorphism B D c 2 _ hlift hev).symm.trans d.ambientChernBoundary_eq

/-- **Stacks Project, Tag 0FUQ, the square, with `ξ'` named as in the statement of Tag 0FUQ.**

`(restriction of forms)[2] ∘ ξ' = ζ' ∘ (restriction of forms)`

in `D(f^{-1}𝒪_S)`, where `ξ'` is the morphism of Tag 0FU7 attached to `c₁^{dR}(ℒ)` for the
invertible module `ℒ`, which for Tag 0FUQ is `𝒪_X(-Y)`, and `ζ'` is the boundary map of the
shifted residue sequence of Tag 0FUF on the divisor, which is the description Tag 0FUG gives of
the morphism of Tag 0FU7 attached to `c₁^{dR}(ℒ|_Y)`. -/
@[stacks 0FUQ "the square with xi' named as the map of 0FU7 attached to the de Rham
first Chern class of O_X(-Y); zeta' stays in the description 0FUG gives of it as the boundary
map of the
residue sequence of 0FUF on the divisor, since the map of 0FU7 is built from the de Rham
differential graded algebra of the ambient data and the comparison along the closed immersion
that would supply one on the divisor is not in the library; carried as explicit named hypotheses
are LogPolesResidueData and the three inputs of 0FUG, namely hlift, hev and
realizationComparison"]
theorem commSq_deRhamClassDerivedMorphism (c : DeRhamDerivedModuleCorrespondence B D)
    (realizationComparison : deRhamCohomologyAbelian B D 2 →+ deRhamCohomology B D 2)
    (L : _root_.SheafOfModules.{u} (structureSheaf X.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L)
    (hlift : ∃ g : deRhamDerivedRegular B D ⟶ deRhamDerivedRegularShift B D 2,
      c.forget 2 g = d.ambientChernBoundary)
    (hev : c.evalOne 2 d.ambientChernBoundary =
      realizationComparison (deRhamFirstChernClassAbelianOf B D L hL)) :
    deRhamClassDerivedMorphism B D c 2
          (realizationComparison (deRhamFirstChernClassAbelianOf B D L hL)) ≫
        (DerivedCategory.Q.map d.restriction)⟦(2 : ℤ)⟧' =
      DerivedCategory.Q.map d.restriction ≫ d.divisorChernBoundary := by
  rw [← eq_deRhamClassDerivedMorphism B D c 2 _ hlift hev]
  exact d.commSq_chernBoundary

end Chern

end LogPolesResidueData

end AlgebraicGeometry.SheafOfModules

end
