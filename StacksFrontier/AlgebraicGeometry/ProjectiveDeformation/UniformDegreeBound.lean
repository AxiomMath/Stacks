module

public import StacksFrontier.AlgebraicGeometry.AmpleThickeningAscent.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTwistLimitVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Morphism.TwistEventual
public import StacksFrontier.AlgebraicGeometry.Perfect.VanishingHigherDirectImagesBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.VanishingHigherDirectImagesFlatness
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.SectionAlgebra
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.ProjIso
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.EventualBijective
public import StacksFrontier.AlgebraicGeometry.ThickeningVanishingAscent.Basic
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Deformations of projective schemes: the uniform degree bound

This file continues `StacksFrontier/AlgebraicGeometry/ProjectiveDeformation/Basic.lean`, whose data
— a polarized family `(f : X ⟶ S, ℒ)` and its admissible deformations
`(X', S', i, i', f', ℒ')` — it uses unchanged, and proves the parts of [Stacks, Tag 0D4F] that
that file takes as inputs.

## Main results

* `uniformHighTwistVanishing`: one degree bound for the vanishing of the higher direct images of
  the high powers of a relatively ample invertible module, over a quasi-compact base.
* `vanishingDescendsAlongThickening`: that vanishing ascends a thickening of the base.
* `exists_uniform_isZero_higherDirectImage`: conclusion (1) of [Stacks, Tag 0D4F], one degree
  bound for every deformation of a family.
* `isFiniteLocallyFree_sectionPiece_of_isZero`, `isIso_baseChange_sectionPiece_of_isZero`:
  conclusion (2) and the base-change compatibility, from conclusion (1) by [Stacks, Tag 0D4E].
* `PolarizedFamily.AdmissibleDeformation.fullSectionAlgebra`: `⨁_{d ≥ 0} 𝒜'_d`, the algebra of
  [Stacks, Tag 01VJ] (5), with the isomorphism `fullSectionProjHom` of [Stacks, Tag 0C6J] onto
  its relative `Proj`.
* `PolarizedFamily.AdmissibleDeformation.IsTruncatedSectionAlgebraWithComparison`: what it means
  for a graded algebra to be `𝒜' = 𝒪_{S'} ⊕ ⨁_{d ≥ d₀} 𝒜'_d`, *including* its comparison map
  into `fullSectionAlgebra`; and `truncatedSectionAlgebra`, which is one.
* `relativeProjTwistIdentification`: conclusions (4) and (5) of [Stacks, Tag 0D4F] for such an
  algebra, through [Stacks, Tags 07ZJ, 0C6J], from the degree-one twist comparison
  `RelativeAmpleTwistIdentification` for the full algebra.
* `relativelyAmpleLiftsAlongThickening`: [Stacks, Tag 0D2R] in the form the data of the tag
  provides, which makes `ℒ'` ample relative to `f'`.

## Implementation notes

The predicate `PolarizedFamily.AdmissibleDeformation.IsTruncatedSectionAlgebra` of `Basic.lean`
constrains only the homogeneous pieces of the algebra, and is satisfied by a graded algebra with
the right pieces and zero multiplication off the degree-zero row and column; the docstring of
`IsTruncatedSectionAlgebraWithComparison` explains why that makes it unusable for conclusions
(3) to (5).  For the same reason the statements `TruncatedSectionAlgebraFinitePresentation`,
`RelativeProjIdentification` and `TwistIdentification` of `Basic.lean`, which are phrased at that
predicate, are not used here: the first is false for the degenerate algebra, whose sections do not
form a finitely generated algebra, and the third quantifies over every isomorphism
`X' ≅ Proj_{S'}(𝒜')` over `S'` rather than the canonical one.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.Ample
open Stacks.AlgebraicGeometry.ChartTransRelativeProj
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.VanishingHigherDirectImages
open Stacks.RelativeAmple
open Stacks.Thickenings

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation

-- `HasDerivedCategory.standard` is raised above the locally-small model that this file's import
-- surface also offers, so that the derived category's hom universe in the statements below is the
-- one the statements of `Basic.lean` and the two conclusions of [Stacks, Tag 0D4E] are stated at.
attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Conclusion (1): the uniform vanishing -/

/-- **`UniformHighTwistVanishing` is a theorem.**  [Stacks, Tag 02O1] over a quasi-compact base,
with no Noetherian hypothesis, is
`Stacks.AlgebraicGeometry.AmpleTwistLimitVanishing`
`.exists_isZero_rightDerivedPlus_pushforward_tensorPowModule`: the affine base is written as the
limit of the spectra of the finitely generated subrings of its ring of functions, the polarized
family descends to a stage whose base is Noetherian ([Stacks, Tag 0D43]), [Stacks, Tag 02O1]
applies there with the structure sheaf as its coherent factor, and the vanishing comes back down
because the square is Tor independent, `g` being flat ([Stacks, Tag 08IB]).  Positivity of the
bound is arranged by replacing `d₀` with `d₀ + 1`. -/
public theorem uniformHighTwistVanishing : UniformHighTwistVanishing.{u} := by
  intro Y T g M hMinv hproper hflat hfp hcompact hample
  have := hMinv
  have := hproper
  have := hflat
  have := hcompact
  obtain ⟨d₀, hd₀⟩ :=
    AmpleTwistLimitVanishing.exists_isZero_rightDerivedPlus_pushforward_tensorPowModule g hfp M
      hample
  exact ⟨d₀ + 1, Nat.succ_pos _, fun d hd => hd₀ d (by omega)⟩


/-- **`VanishingDescendsAlongThickening` is a theorem.**  It is
`Stacks.AlgebraicGeometry.ThickeningVanishingAscent`
`.isZero_rightDerivedPlus_pushforward_of_isZero_pullback` at the invertible module
`(ℒ')^{⊗ d}`, whose pullback along `j'` is carried to `N^{⊗ d}` by
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` followed by
`Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso` at the granted isomorphism.

Surjectivity of `j` is the second half of `Stacks.Thickenings.IsThickening`; the
closed-immersion half is not used, and neither is the perfection half of [Stacks, Tag 0B91] nor
[Stacks, Tag 0BDK].  See the module docstring. -/
public theorem vanishingDescendsAlongThickening : VanishingDescendsAlongThickening.{u} := by
  intro Y Y' T T' g g' j j' hthick hsq hproper hflat hfp M' hM'inv N hNinv hiso d hvan p hp
  have := hM'inv
  have := hNinv
  have := hproper
  have := hflat
  have := hfp.1
  obtain ⟨e⟩ := hiso
  refine ThickeningVanishingAscent.isZero_rightDerivedPlus_pushforward_of_isZero_pullback
    ⟨hthick.2⟩ hsq (tensorPowModule Y' M' (d : ℤ)) (fun q hq => ?_) p hp
  refine (hvan q hq).of_iso (((Scheme.Modules.pushforward g).rightDerivedPlus q).mapIso ?_)
  exact Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso j' M' d ≪≫
    Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso Y
      ((Scheme.Modules.pullback j').obj M') N e.symm d


/-- **The mathematical content of [Stacks, Tag 0D4F]: one degree bound works for every
deformation.**  Let `(f, ℒ)` be a polarized family.  There is a positive `d₀`, depending only on
`(f, ℒ)` over `S`, such that for *every* admissible deformation `D` of the family and every
`d ≥ d₀` the higher direct images `R^p (f')_* (ℒ')^{⊗ d}` vanish for `p > 0`.

This is the step the source performs after *we claim that `d₀` works*: the bound is produced once,
on `S`, by [Stacks, Tag 0B5T], and then transported to each deformation.  Nothing about the
deformation is used to choose it, which is exactly what makes the construction of `𝒜'`, `r'` and
`θ'` functorial in the data.

Stated separately and now with no hypothesis at all, so that the uniformity is checkable on its
own: the bound on `S` is chosen by `uniformHighTwistVanishing`, which knows nothing of
deformations, and `vanishingDescendsAlongThickening` transports a vanishing statement across one
thickening at one degree and knows nothing of bounds.  Neither quantifies over the family and its
deformations together; the composition does, and that composition is this lemma. -/
public theorem exists_uniform_isZero_higherDirectImage (P : PolarizedFamily.{u}) :
    ∃ d₀ : ℕ, 0 < d₀ ∧ ∀ (D : P.AdmissibleDeformation) (d : ℕ), d₀ ≤ d → ∀ p : ℤ, 0 < p →
      IsZero (((Scheme.Modules.pushforward D.f').rightDerivedPlus p).obj
        (tensorPowModule D.X' D.L' (d : ℤ))) := by
  obtain ⟨d₀, hd₀pos, hd₀⟩ :=
    uniformHighTwistVanishing P.X P.S P.f P.L P.isProper P.flat P.finitePresentation
      P.compactSpace P.isRelativelyAmple
  exact ⟨d₀, hd₀pos, fun D d hd =>
    vanishingDescendsAlongThickening P.X D.X' P.S D.S' P.f D.f' D.i D.i' D.isThickening
      D.isPullback D.isProper D.flat
      D.finitePresentation D.L' P.L ⟨D.polarization⟩ d (hd₀ d hd)⟩


/-! ### Relative ampleness of the deformed polarization -/

/-- **[Stacks, Tag 0D2R] in the form the data of [Stacks, Tag 0D4F] provides.**  In a cartesian
square with `T ⊂ T'` a thickening, if an invertible module `N` isomorphic to `(j')^* M'` is ample
relative to `g`, then `M'` is ample relative to `g'`.

This is `Stacks.ThickeningInvertible.isRelativelyAmple_of_isRelativelyAmple_pullback` with the
`mp` half of [Stacks, Tag 09MW], `Stacks.AmpleThickeningAscent.ampleReflectedByThickening`,
together with two bridges: the immersion `j'` of total spaces is a thickening, being a base change
of `j` ([Stacks, Tag 09ZU], `Stacks.Thickenings.isThickening_of_isPullback`), and relative
ampleness is invariant under isomorphism of the module
(`Stacks.RelativeVeryAmple.isRelativelyAmple_congr`). -/
public theorem relativelyAmpleLiftsAlongThickening : RelativelyAmpleLiftsAlongThickening.{u} := by
  intro Y Y' T T' g g' j j' hj hsq M' _ N _ he hN
  have hj' : IsThickening j' := Stacks.Thickenings.isThickening_of_isPullback hsq hj
  have hN' : IsRelativelyAmple g ((Scheme.Modules.pullback j').obj M') :=
    (Stacks.RelativeVeryAmple.isRelativelyAmple_congr g N _ he.some).mp hN
  exact Stacks.ThickeningInvertible.isRelativelyAmple_of_isRelativelyAmple_pullback M'
    Stacks.AmpleThickeningAscent.ampleReflectedByThickening hj' hj hsq.w hN'

open PolarizedFamily PolarizedFamily.AdmissibleDeformation

/-! ### Conclusion (2), and the base-change compatibility behind the functoriality assertion -/

section SectionPieces

variable {P : PolarizedFamily.{u}} (D : P.AdmissibleDeformation)

/-- **Conclusion (2) of [Stacks, Tag 0D4F] from conclusion (1).**  If the higher direct images of
`(ℒ')^{⊗ d}` along `f'` vanish, then `𝒜'_d = (f')_* (ℒ')^{⊗ d}` is finite locally free.

This is the first conclusion of [Stacks, Tag 0D4E],
`VanishingHigherDirectImages.isFiniteLocallyFree_pushforward_of_isZero_higherDirectImage`,
applied to `f'` and `(ℒ')^{⊗ d}`: that module is of finite presentation and flat over `S'` because
it is invertible and `f'` is flat, and its support is proper over `S'` because `f'` is proper. -/
@[sga "6 III 5.7" "(iii), special case"]
public theorem isFiniteLocallyFree_sectionPiece_of_isZero (d : ℕ)
    (hvanish : ∀ p : ℤ, 0 < p →
      IsZero (((Scheme.Modules.pushforward D.f').rightDerivedPlus p).obj
        (tensorPowModule D.X' D.L' (d : ℤ)))) :
    _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := D.S'.ringCatSheaf) (D.sectionPiece d) :=
  have := D.isFinitePresentation_tensorPowModule d
  isFiniteLocallyFree_pushforward_of_isZero_higherDirectImage
    D.f' D.finitePresentation (tensorPowModule D.X' D.L' (d : ℤ))
    (D.isFlatOver_tensorPowModule d)
    (D.exists_isProperOver (tensorPowModule D.X' D.L' (d : ℤ))) hvanish

/-- **The formation of `𝒜'_d` commutes with arbitrary base change.**  For every cartesian square
over a morphism `h : T ⟶ S'`, the canonical comparison
`h^* (f')_* (ℒ')^{⊗ d} ⟶ (f_T)_* (h')^* (ℒ')^{⊗ d}` is an isomorphism.

This is what the functoriality assertion of [Stacks, Tag 0D4F] rests on: the source reads it off
cohomology and base change, and from it the identification `h^* 𝒜'_d = (f_T)_* ℒ_T^{⊗ d}`, hence
the base-change compatibility of `𝒜'`, `r'` and `θ'`.  The proof here is the second conclusion of
[Stacks, Tag 0D4E],
`VanishingHigherDirectImages.isIso_baseChange_app_of_isZero_higherDirectImage`,
applied to `f'` and `(ℒ')^{⊗ d}`. -/
public theorem isIso_baseChange_sectionPiece_of_isZero (d : ℕ)
    (hvanish : ∀ p : ℤ, 0 < p →
      IsZero (((Scheme.Modules.pushforward D.f').rightDerivedPlus p).obj
        (tensorPowModule D.X' D.L' (d : ℤ))))
    {T Y : Scheme.{u}} (h : T ⟶ D.S') (fT : Y ⟶ T) (h' : Y ⟶ D.X')
    (hsq : IsPullback h' fT D.f' h) :
    IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app
      (tensorPowModule D.X' D.L' (d : ℤ))) :=
  have := D.isFinitePresentation_tensorPowModule d
  isIso_baseChange_app_of_isZero_higherDirectImage
    D.f' h fT h' hsq
    (congrArg (fun k : Y ⟶ D.S' => k.toLRSHom.toShHom) hsq.w) D.finitePresentation
    (tensorPowModule D.X' D.L' (d : ℤ)) (D.isFlatOver_tensorPowModule d)
    (D.exists_isProperOver (tensorPowModule D.X' D.L' (d : ℤ))) hvanish


end SectionPieces

/-! ### The full and the truncated section algebra -/

namespace PolarizedFamily.AdmissibleDeformation

variable {P : PolarizedFamily.{u}} (D : P.AdmissibleDeformation)

/-- **The full graded section algebra `⨁_{d ≥ 0} 𝒜'_d` of a deformation.**  The algebra of clause
(5) of [Stacks, Tag 01VJ] for `f' : X' ⟶ S'` and `ℒ'`, which is
`Stacks.RelativeAmple.directImageAlgebra`: the direct image along `f'` of the Laurent algebra
`⨁_{n ∈ ℤ} (ℒ')^{⊗ n}` of [Stacks, Tag 01CU], truncated to the nonnegative degrees.

This is the algebra [Stacks, Tag 0C6J] identifies `X'` with the relative `Proj` of, and it is the
target of the comparison map that
`PolarizedFamily.AdmissibleDeformation.IsTruncatedSectionAlgebraWithComparison` demands; those two
facts together are conclusion (4). -/
public noncomputable def fullSectionAlgebra : SheafGradedAlgebra D.S' :=
  letI := D.finitePresentation.quasiCompact
  letI := D.finitePresentation.quasiSeparated
  Stacks.RelativeAmple.directImageAlgebra D.f' D.L'

/-- **In degree `d ≥ 0` the piece of the full section algebra is `𝒜'_d`.**  Both are the direct
image along `f'` of the `d`-th tensor power of `ℒ'`; the two spellings of that tensor power — the
one of [Stacks, Tag 01CU] that the Laurent algebra is built from, and
`Stacks.Ample.tensorPowModule` that the ampleness theory and the conclusions of
[Stacks, Tag 0D4E] are stated at — are compared by
`Stacks.PowerFamilyBridge.tensorPowerModuleIso`. -/
public noncomputable def fullSectionAlgebraPieceIso (d : ℕ) :
    D.fullSectionAlgebra.piece (d : ℤ) ≅ D.sectionPiece d :=
  letI := D.finitePresentation.quasiCompact
  letI := D.finitePresentation.quasiSeparated
  (Scheme.Modules.pushforward D.f').mapIso
    (Stacks.PowerFamilyBridge.tensorPowerModuleIso D.X' D.L' (d : ℤ))

/-- **[Stacks, Tag 0C6J]: the canonical morphism `X' ⟶ Proj_{S'}(⨁_{d ≥ 0} 𝒜'_d)`.**  The
morphism `r_{ℒ', ψ}` of [Stacks, Tag 01VJ], `Stacks.RelativeAmple.relativeAmpleProjHom`, read at
`fullSectionAlgebra`, which is the algebra it is built from.  It is an isomorphism by
[Stacks, Tag 0C6J], `Stacks.RelativeAmple.isIso_relativeAmpleProjHom`, `f'` being universally
closed because it is proper. -/
public noncomputable def fullSectionProjHom (hample : IsRelativelyAmple D.f' D.L') :
    D.X' ⟶ (relativeProj D.fullSectionAlgebra).scheme :=
  letI := D.finitePresentation.quasiCompact
  letI := D.finitePresentation.quasiSeparated
  relativeAmpleProjHom D.f' D.L' hample

/-- [Stacks, Tag 0C6J]: that morphism is an isomorphism. -/
public instance isIso_fullSectionProjHom (hample : IsRelativelyAmple D.f' D.L') :
    IsIso (D.fullSectionProjHom hample) :=
  letI := D.finitePresentation.quasiCompact
  letI := D.finitePresentation.quasiSeparated
  isIso_relativeAmpleProjHom D.f' D.L' hample

/-- That morphism is a morphism over `S'`. -/
public theorem fullSectionProjHom_comp_toBase (hample : IsRelativelyAmple D.f' D.L') :
    D.fullSectionProjHom hample ≫ (relativeProj D.fullSectionAlgebra).toBase = D.f' :=
  let := D.finitePresentation.quasiCompact
  let := D.finitePresentation.quasiSeparated
  relativeAmpleProjHom_toBase D.f' D.L' hample

/-- **The truncated section algebra of a deformation, characterised by its homogeneous pieces and
its comparison map into the full section algebra.**  A quasi-coherent graded `𝒪_{S'}`-algebra `A`
is the truncated section algebra of `D` at `d₀` when its degree-zero piece is the structure sheaf,
every piece outside `{0} ∪ [d₀, ∞)` vanishes, and it comes with a homomorphism of graded algebras
into the full section algebra `⨁_{d ≥ 0} 𝒜'_d` which is an isomorphism in every degree `d ≥ d₀`.
This is `𝒜' = 𝒪_{S'} ⊕ ⨁_{d ≥ d₀} 𝒜'_d` of [Stacks, Tag 0D4F] (3), together with the comparison
into the full algebra that the source's clauses (4) and (5) are proved through.

**The comparison map is not decoration: without it the predicate is unsound.**  A version
constraining only the homogeneous *pieces* — `A.piece 0 ≅ 𝒪_{S'}`, `A.piece d ≅ 𝒜'_d` for `d ≥ d₀`,
and `IsZero` elsewhere — says nothing relating the multiplication of `A` to the multiplication of
sections of the tensor powers of `ℒ'`, and a **degenerate witness** satisfies it: take those very
pieces and define the product to be the `𝒪_{S'}`-action in the degree-zero row and column and the
*zero* bilinear map in every other bidegree.  That is a legitimate `SheafGradedAlgebra`, every
associativity branch being either a law of the module action or a heterogeneous equality of two
zeros, and it has the prescribed pieces; but its degree-`d` sections do not multiply as sections of
`(ℒ')^{⊗ d}` do.  Since `exists_uniform_degreeBound_of_deformations` uses one `A`,
`truncatedSectionAlgebra`, and hands *that same* `A` to the identification of `Proj_{S'}(A)` with
`X'` and to the twist comparison, a degenerate witness would make those statements false, and a
false hypothesis makes the tag vacuous.

The comparison map rules the degenerate witness out exactly: for `d ≥ d₀` the law
`ψ_{2d}(a · b) = ψ_d(a) · ψ_d(b)` of a homomorphism of graded algebras, with `ψ_d` an
isomorphism, forces the product of `A` in bidegree `(d, d)` to be the genuine product of sections
of `(ℒ')^{⊗ d}` transported along `ψ`, and a zero product cannot match a nonzero one.

The weaker piecewise clause is recovered as `IsTruncatedSectionAlgebraWithComparison.piece_iso`, so
this is a strengthening and not a rewrite: every consumer that only needs `A.piece d ≅ 𝒜'_d` still
gets it. No separate clause is needed to say that the degree-zero component of `ψ` is the unit
`𝒪_{S'} ⟶ (f')_* 𝒪_{X'}`: the field `SheafGradedAlgebraHom.app_one` already forces `ψ_0 (1_A) =
1_{𝒜'}`, and the first clause makes `A.piece 0` the free module of rank one on `1_A`. -/
public def IsTruncatedSectionAlgebraWithComparison (d₀ : ℕ) (A : SheafGradedAlgebra D.S') : Prop :=
  Nonempty (A.piece 0 ≅ _root_.SheafOfModules.unit D.S'.ringCatSheaf) ∧
    (∃ ψ : Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom A
        D.fullSectionAlgebra, ∀ d : ℕ, d₀ ≤ d → IsIso (ψ.app (d : ℤ))) ∧
      ∀ n : ℤ, n ≠ 0 → n < (d₀ : ℤ) → IsZero (A.piece n)

/-- **The degree-`d` piece of a truncated section algebra is `𝒜'_d` for `d ≥ d₀`.**  This is the
weaker piecewise second clause, recovered from the comparison map: the degree-`d` component of the
comparison is an isomorphism onto the degree-`d` piece of the full section algebra, which is
`𝒜'_d` by `fullSectionAlgebraPieceIso`. -/
public theorem IsTruncatedSectionAlgebraWithComparison.piece_iso {d₀ : ℕ}
    {A : SheafGradedAlgebra D.S'}
    (hA : D.IsTruncatedSectionAlgebraWithComparison d₀ A) (d : ℕ) (hd : d₀ ≤ d) :
    Nonempty (A.piece (d : ℤ) ≅ D.sectionPiece d) := by
  obtain ⟨ψ, hψ⟩ := hA.2.1
  have := hψ d hd
  exact ⟨asIso (ψ.app (d : ℤ)) ≪≫ D.fullSectionAlgebraPieceIso d⟩

/-! ### The truncated section algebra, and its comparison into the full one -/

/-- **The `ℤ`-graded algebra `⨁_{n ∈ ℤ} (f')_* (ℒ')^{⊗ n}` of a deformation**: the direct image
along `f'` of the Laurent algebra of [Stacks, Tag 01CU] on `ℒ'`.  Both section algebras are
truncations of it — the full one at `0`, which is `fullSectionAlgebra` by definition, and `𝒜'` at
the variable cut `d₀` with `𝒪_{S'}` put in degree zero. -/
public noncomputable def laurentPushforward :
    SheafOfModules.GradedAlgebra.{u, u} D.S'.ringCatSheaf :=
  Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra D.f'
    (Stacks.RelativeAmple.laurentPowers D.L')

/-- The multiplication of `⨁_{n ∈ ℤ} (f')_* (ℒ')^{⊗ n}` commutes, that of the Laurent algebra
doing so. -/
public theorem isCommutative_laurentPushforward :
    Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.IsCommutative D.laurentPushforward :=
  Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.isCommutative_pushforwardGradedAlgebra _ _
    (Stacks.RelativeAmple.isCommutative_laurentPowers D.L')

/-- Every piece of `⨁_{n ∈ ℤ} (f')_* (ℒ')^{⊗ n}` is quasi-coherent: the tensor powers are, being
invertible, and [Stacks, Tag 01LC] applies to `f'`, which is quasi-compact and quasi-separated
because it is of finite presentation. -/
public theorem isQuasicoherent_laurentPushforward_piece (n : ℤ) :
    ((D.laurentPushforward.piece n : D.S'.Modules)).IsQuasicoherent :=
  let := D.finitePresentation.quasiCompact
  let := D.finitePresentation.quasiSeparated
  Stacks.RelativeAmple.isQuasicoherent_pushforward_laurentPowers D.f' D.L' n

/-- **The full section algebra is the nonnegative truncation of
`⨁_{n ∈ ℤ} (f')_* (ℒ')^{⊗ n}`**, by definition: that is what
`Stacks.RelativeAmple.directImageAlgebra` is. -/
public theorem fullSectionAlgebra_eq_nonnegTruncation :
    D.fullSectionAlgebra =
      Stacks.AlgebraicGeometry.NonnegTruncation.nonnegSheafGradedAlgebra D.laurentPushforward
        D.isCommutative_laurentPushforward D.isQuasicoherent_laurentPushforward_piece :=
  rfl

/-- **The truncated section algebra `𝒜' = 𝒪_{S'} ⊕ ⨁_{d ≥ d₀} 𝒜'_d`** of
[Stacks, Tag 0D4F] (3): the tail truncation of `⨁_{n ∈ ℤ} (f')_* (ℒ')^{⊗ n}` at the cut `d₀`,
with the structure sheaf in degree zero and a zero object in every degree outside
`{0} ∪ [d₀, ∞)`. -/
public noncomputable def truncatedSectionAlgebra (d₀ : ℕ) (hd : 0 < d₀) :
    SheafGradedAlgebra D.S' :=
  Stacks.AlgebraicGeometry.SectionAlgebra.tailSheafGradedAlgebra D.laurentPushforward d₀ hd
    D.isCommutative_laurentPushforward D.isQuasicoherent_laurentPushforward_piece

/-- **The comparison `𝒜' ⟶ ⨁_{d ≥ 0} 𝒜'_d`** of the second clause of
`IsTruncatedSectionAlgebraWithComparison`: the unit map `𝒪_{S'} ⟶ (f')_* 𝒪_{X'}` in degree zero,
the identification of the degree-`d` pieces for `d ≥ d₀`, and the zero morphism in the band
between, where the truncation vanishes.  This is
`Stacks.AlgebraicGeometry.SectionAlgebra.tailComparison` for `⨁_{n ∈ ℤ} (f')_* (ℒ')^{⊗ n}`, the
two truncations of which the two algebras are. -/
public noncomputable def sectionAlgebraComparison (d₀ : ℕ) (hd : 0 < d₀) :
    Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom
      (D.truncatedSectionAlgebra d₀ hd) D.fullSectionAlgebra :=
  Stacks.AlgebraicGeometry.SectionAlgebra.tailComparison D.laurentPushforward d₀ hd
    D.isCommutative_laurentPushforward D.isQuasicoherent_laurentPushforward_piece

/-- **The truncated section algebra is a truncated section algebra.**  Its degree-zero piece is
the structure sheaf (`tailPiece_eq_unit`), the comparison into the full algebra is
`sectionAlgebraComparison` and is an isomorphism in every degree `≥ d₀` (`isIso_tailCompApp`, the
comparison being a transport there), and every piece outside `{0} ∪ [d₀, ∞)` is a zero object
(`eq_zero_of_tailPiece`). -/
public theorem isTruncatedSectionAlgebraWithComparison_truncatedSectionAlgebra (d₀ : ℕ)
    (hd : 0 < d₀) :
    D.IsTruncatedSectionAlgebraWithComparison d₀ (D.truncatedSectionAlgebra d₀ hd) :=
  ⟨⟨eqToIso (Stacks.AlgebraicGeometry.SectionAlgebra.tailPiece_eq_unit
      D.laurentPushforward d₀ rfl)⟩,
    ⟨D.sectionAlgebraComparison d₀ hd, fun d hdd =>
      Stacks.AlgebraicGeometry.SectionAlgebra.isIso_tailCompApp D.laurentPushforward d₀ hd
        (show ¬ (d : ℤ) = 0 by omega) (show (d₀ : ℤ) ≤ (d : ℤ) by omega)
        (show (0 : ℤ) ≤ (d : ℤ) by omega)⟩,
    fun n hn0 hnd =>
      Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.isZero_of_forall_eq_zero _ fun U x =>
        Stacks.AlgebraicGeometry.SectionAlgebra.eq_zero_of_tailPiece D.laurentPushforward d₀
          hn0 (show ¬ (d₀ : ℤ) ≤ n by omega) (Opposite.op U) x⟩

end PolarizedFamily.AdmissibleDeformation

/-- **The degree-one case of the second claim of [Stacks, Tag 01QI], relative to a base.**  Let
`g : Y ⟶ T` be a proper morphism of finite presentation and `M` an invertible `𝒪_Y`-module ample
relative to `g`.  Then the canonical morphism `r_{M, ψ} : Y ⟶ Proj_T(⨁_{d ≥ 0} g_* M^{⊗ d})` of
[Stacks, Tag 01VJ] pulls the first Serre twist of that relative `Proj` back to `M`.

This is the map `θ` of [Stacks, Tag 01O9] in degree one — `GradedPowerMap.theta`, which *is*
constructed, for the datum `Stacks.RelativeAmple.directImagePowerMap g M` — together with the
assertion that it is an isomorphism, which is the content of the second claim of
[Stacks, Tag 01QI].  The absolute first claim of that tag is proved, as
`Stacks.SectionRingProjGoodOpen.projHomOfIsAmple_preimage_whereInvertible`; its second claim is
recorded as not addressed in the "What is not done" section of
`StacksFrontier/AlgebraicGeometry/SectionRingProjGoodOpen/Basic.lean`, and neither claim is
available over a base.  The one `IsIso (P.theta.app 1)` in the library,
`Stacks.VeryAmpleGlue.isIso_theta_one`, is for `P` a graded map out of the symmetric algebra of a
quasi-coherent module, where the degree-one twist of the relative `Proj` is invertible outright;
for `⨁_{d ≥ 0} g_* M^{⊗ d}` it need not be, which is exactly why [Stacks, Tag 01QI] runs through
the open `W_1` of [Stacks, Tag 01MU] and the multiplicativity of `θ`.

This statement mentions no thickening, no deformation, no truncation and no degree bound, so it
contains no part of the uniformity of `d₀`, which is the content of [Stacks, Tag 0D4F].

**`TwistIdentification` of `Basic.lean` is a different, refutable statement.**  It
quantified over *every* `r : X' ⟶ Proj_{S'}(𝒜')` with `IsIso r` and `r ≫ π = f'` and asserted the
twist comparison for all of them; but the source's conclusion (5) is about the *canonical* `r'`
that conclusion (4) produces.  Composing a witness with a nontrivial automorphism of
`Proj_{S'}(𝒜')` over `S'` gives another `r` satisfying both binders, and such an automorphism acts
on the graded pieces, so it need not carry `𝒪(1)` to `ℒ'`.  The universally quantified form
therefore asserted strictly more than the tag, and was false.  The repair is this one: the twist
clause is now stated at the canonical morphism and is *derived* for the `r` of conclusion (4), by
`relativeProjTwistIdentification`, from clause (3) of [Stacks, Tag 07ZJ] — the maps on twists,
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap`, invertible by
`…isIso_relativeTwistMap_of_eventually_isIso` — composed with this statement about the full
algebra.  Nothing of the tag's conclusion (5) is weakened: all that has changed is that `r` is
pinned to the morphism the tag's own conclusion (4) names. -/
public def RelativeAmpleTwistIdentification : Prop :=
  ∀ (Y T : Scheme.{u}) (g : Y ⟶ T) [QuasiCompact g] [QuasiSeparated g] (M : Y.Modules)
    [IsInvertibleModule Y M] (hM : IsRelativelyAmple g M),
    Nonempty ((Scheme.Modules.pullback (relativeAmpleProjHom g M hM)).obj
      (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist (directImageAlgebra g M) 1) ≅ M)

/-! ### Conclusions (4) and (5): the canonical identification of `X'` with `Proj_{S'}(𝒜')` -/

section ProjIdentification

variable {P : PolarizedFamily.{u}} {D : P.AdmissibleDeformation} {A : SheafGradedAlgebra D.S'}
  (ψ : Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom A
    D.fullSectionAlgebra)
  (hψ : ∀ᶠ d : ℕ in Filter.atTop, IsIso (ψ.app (d : ℤ)))

/-- **`U(ψ)` is the whole of `Proj_{S'}(⨁_{d ≥ 0} 𝒜'_d)`, read as a section of its inclusion.**
Clause (1) of [Stacks, Tag 07ZJ],
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.relativeMapDomain_eq_top_of_eventually_isIso`,
says the open on which `ψ` induces a morphism is everything; this is the resulting isomorphism
`Proj_{S'}(⨁_{d ≥ 0} 𝒜'_d) ≅ U(ψ)`, in the shape `Stacks.RelativeAmple.relativeAmpleProjHom` uses
for the same step. -/
public noncomputable def projDomainRetract :
    (relativeProj D.fullSectionAlgebra).scheme ⟶ ψ.relativeMapDomain.toScheme :=
  (Scheme.topIso _).inv ≫
    (((relativeProj D.fullSectionAlgebra).scheme).isoOfEq
      (Stacks.AlgebraicGeometry.RelativeProjMapDomain.relativeMapDomain_eq_top_of_eventually_isIso
        ψ hψ).symm).hom

/-- The retract is a section of the inclusion of `U(ψ)`. -/
public theorem projDomainRetract_comp_ι :
    projDomainRetract ψ hψ ≫ ψ.relativeMapDomain.ι =
      𝟙 (relativeProj D.fullSectionAlgebra).scheme := by
  rw [projDomainRetract, Category.assoc, Scheme.isoOfEq_hom_ι]
  simp

/-- The morphism `projDomainRetract` is an isomorphism. -/
instance isIso_projDomainRetract : IsIso (projDomainRetract ψ hψ) := by
  rw [projDomainRetract]; infer_instance

/-- **The isomorphism `Proj_{S'}(⨁_{d ≥ 0} 𝒜'_d) ⟶ Proj_{S'}(𝒜')` of [Stacks, Tag 07ZJ].**  The
morphism `r_ψ` of [Stacks, Tag 07ZG] attached to a comparison invertible in all large degrees,
read on the whole of its target. -/
public noncomputable def projTruncationComparison :
    (relativeProj D.fullSectionAlgebra).scheme ⟶ (relativeProj A).scheme :=
  projDomainRetract ψ hψ ≫ Stacks.AlgebraicGeometry.Tag07ZGMorphism.relativeMapHom ψ

/-- Clause (2) of [Stacks, Tag 07ZJ]: the comparison of relative `Proj` is an isomorphism. -/
instance isIso_projTruncationComparison : IsIso (projTruncationComparison ψ hψ) := by
  have := Stacks.AlgebraicGeometry.RelativeProjMapDomain.isIso_relativeMapHom_of_eventually_isIso
    ψ hψ
  rw [projTruncationComparison]
  infer_instance

/-- The comparison of relative `Proj` is a morphism over `S'`. -/
public theorem projTruncationComparison_comp_toBase :
    projTruncationComparison ψ hψ ≫ (relativeProj A).toBase =
      (relativeProj D.fullSectionAlgebra).toBase := by
  rw [projTruncationComparison, Category.assoc,
    Stacks.AlgebraicGeometry.Tag07ZGMorphism.relativeMapHom_comp_toBase,
    ← Category.assoc, projDomainRetract_comp_ι, Category.id_comp]

/-- **Clause (3) of [Stacks, Tag 07ZJ], globally: the comparison of relative `Proj` carries the
first Serre twist of `Proj_{S'}(𝒜')` to the first Serre twist of
`Proj_{S'}(⨁_{d ≥ 0} 𝒜'_d)`.**  The map is
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap` in degree one, an isomorphism by
`…isIso_relativeTwistMap_of_eventually_isIso`; the retract of the inclusion of `U(ψ)` turns the
restriction of the target into the twist itself. -/
public noncomputable def projTruncationTwistIso :
    (Scheme.Modules.pullback (projTruncationComparison ψ hψ)).obj
        (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist A 1) ≅
      Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist D.fullSectionAlgebra 1 :=
  haveI := Stacks.AlgebraicGeometry.Tag07ZGTwist.isIso_relativeTwistMap_of_eventually_isIso ψ hψ 1
  ((Scheme.Modules.pullbackComp (projDomainRetract ψ hψ)
        (Stacks.AlgebraicGeometry.Tag07ZGMorphism.relativeMapHom ψ)).app _).symm ≪≫
    (Scheme.Modules.pullback (projDomainRetract ψ hψ)).mapIso
      (asIso (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap ψ 1)) ≪≫
    (Scheme.Modules.pullbackComp (projDomainRetract ψ hψ) ψ.relativeMapDomain.ι).app _ ≪≫
    (Scheme.Modules.pullbackCongr (projDomainRetract_comp_ι ψ hψ)).app _ ≪≫
    (Scheme.Modules.pullbackId _).app _

end ProjIdentification

/-- **Conclusion (4) of [Stacks, Tag 0D4F], and conclusion (5) at the morphism conclusion (4)
produces.**  For a truncated section algebra `A` at a positive cut `d₀`, there is an isomorphism
`r' : X' ⟶ Proj_{S'}(A)` over `S'`, and it pulls the first Serre twist of `Proj_{S'}(A)` back to
`ℒ'`.

The two steps are the source's own.  `A` comes, by the second clause of
`IsTruncatedSectionAlgebraWithComparison`, with a homomorphism `ψ : A ⟶ ⨁_{d ≥ 0} 𝒜'_d` invertible
in every degree `≥ d₀`; [Stacks, Tag 07ZJ] turns that into an isomorphism
`Proj_{S'}(⨁_{d ≥ 0} 𝒜'_d) ⟶ Proj_{S'}(A)` over `S'` carrying the Serre twists to one another
(`projTruncationComparison`, `projTruncationTwistIso`), and [Stacks, Tag 0C6J] —
`Stacks.RelativeAmple.isIso_relativeAmpleProjHom`, for the morphism `r_{ℒ', ψ}` of [Stacks, Tag
01VJ] — identifies `X'` with `Proj_{S'}(⨁_{d ≥ 0} 𝒜'_d)`.  The twist clause of the second step is
`RelativeAmpleTwistIdentification`, which is [Stacks, Tag 01QI] (2) relativized and nothing more;
the rest carries no hypothesis.

The twist is `Stacks.AlgebraicGeometry.ChartTransRelativeProj.gluedTwist A 1`, which is
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist A 1` for the cocycle that
`Stacks.AlgebraicGeometry.ProjTwistCocycle.isNestedCocycle` discharges, the two agreeing because
`IsNestedCocycle A 1` is a proposition. -/
public theorem relativeProjTwistIdentification (htwist : RelativeAmpleTwistIdentification.{u})
    (P : PolarizedFamily.{u}) (D : P.AdmissibleDeformation) (d₀ : ℕ) (_hd₀ : 0 < d₀)
    (hample : IsRelativelyAmple D.f' D.L') (A : SheafGradedAlgebra D.S')
    (hA : D.IsTruncatedSectionAlgebraWithComparison d₀ A) :
    ∃ r : D.X' ⟶ (relativeProj A).scheme, IsIso r ∧
      r ≫ (relativeProj A).toBase = D.f' ∧
      ∀ hcoc : IsNestedCocycle A 1,
        Nonempty ((Scheme.Modules.pullback r).obj (gluedTwist A 1 hcoc) ≅ D.L') := by
  obtain ⟨-, ⟨ψ, hψd⟩, -⟩ := hA
  have hψ : ∀ᶠ d : ℕ in Filter.atTop, IsIso (ψ.app (d : ℤ)) :=
    Filter.eventually_atTop.2 ⟨d₀, hψd⟩
  have := D.finitePresentation.quasiCompact
  have := D.finitePresentation.quasiSeparated
  refine ⟨D.fullSectionProjHom hample ≫ projTruncationComparison ψ hψ, inferInstance, ?_,
    fun hcoc => ?_⟩
  · rw [Category.assoc, projTruncationComparison_comp_toBase ψ hψ]
    exact D.fullSectionProjHom_comp_toBase hample
  · obtain ⟨e⟩ := htwist D.X' D.S' D.f' D.L' hample
    exact ⟨((Scheme.Modules.pullbackComp (D.fullSectionProjHom hample)
        (projTruncationComparison ψ hψ)).app _).symm ≪≫
      (Scheme.Modules.pullback (D.fullSectionProjHom hample)).mapIso
        (projTruncationTwistIso ψ hψ) ≪≫ e⟩

/-! ### Conclusion (3) for a single deformation -/

/-- **Conclusion (3) of [Stacks, Tag 0D4F] for a single deformation.**  The truncated section
algebra `𝒜' = 𝒪_{S'} ⊕ ⨁_{d ≥ d₀} 𝒜'_d` is of finite presentation as a sheaf of
`𝒪_{S'}`-algebras — the notion of [Stacks, Section 01PD] — that is, over every affine open `U` of
`S'` the ring map `Γ(S', U) ⟶ Γ(U, 𝒜')` is of finite presentation.

It is stated at the algebra `truncatedSectionAlgebra` itself, and needs of the deformation only
that `ℒ'` is ample relative to `f'` and that the pieces `𝒜'_d`, `d ≥ d₀`, are finite locally
free. -/
public def TruncatedSectionAlgebraFinitePresentationOf : Prop :=
  ∀ (P : PolarizedFamily.{u}) (D : P.AdmissibleDeformation) (d₀ : ℕ) (hd₀ : 0 < d₀),
    IsRelativelyAmple D.f' D.L' →
    (∀ d : ℕ, d₀ ≤ d →
      _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (R := D.S'.ringCatSheaf) (D.sectionPiece d)) →
    ∀ U : D.S'.Opens, IsAffineOpen U →
      RingHom.FinitePresentation ((D.truncatedSectionAlgebra d₀ hd₀).strHom U)

end Stacks.AlgebraicGeometry.ProjectiveDeformation
