module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceFiniteFamilies
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.GradedPullback
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.KernelIdeal
public import StacksFrontier.AlgebraicGeometry.RelativeProjSeparated.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.Statement
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graded ideal of a closed subscheme of a relative Proj

Work in Situation 01NN: a scheme `S` and a quasi-coherent graded `𝒪_S`-algebra `𝒜` in the
sheaf-level form `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`. Write
`p : Proj_S(𝒜) ⟶ S` for the structure morphism and let `i : Z ⟶ Proj_S(𝒜)` be a closed
immersion. Stacks Tag 0801 forms the degreewise kernel

    ℐ_d = ker (𝒜_d ⟶ p_*((i_*𝒪_Z)(d))),

the map being the homogeneous-section map of Tag 01NR followed by the unit of the
pullback–pushforward adjunction at `i`, and the target being read through the projection formula
as `p_*(i_*(i^*𝒪(d)))`. **This file constructs that kernel as a graded ideal of `𝒜` with
quasi-coherent homogeneous pieces**, so that it can be fed to
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.quotAlgebra`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.restrictTwists`: `i^*` of the twists of
  `Proj_S(𝒜)`, as a sheaf of graded algebras on `Z`.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistTarget`: the target
  `𝒯_d = p_*(i_*(i^*𝒪(d)))`, and `twistTargetMul`, its multiplication.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistRestrictMap`: the degreewise map
  `𝒜_d ⟶ 𝒯_d`.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistMulCompatibleMaps`: the whole datum, as
  a `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.MulCompatibleMaps`.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistKerGradedIdeal`: **Tag 0801's graded
  ideal `ℐ`**, with quasi-coherent pieces.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistRestrictMap_mul`: **the degreewise maps
  are multiplicative.** This is the statement the implementation notes of
  `StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/Quotient.lean` recorded as the one
  genuinely open point of Tag 0801. It is the multiplicativity of the unit of the
  pullback–pushforward adjunction, `Stacks.Conormal.gradedPullback_mul_pullbackSection`, composed
  with the multiplicativity of the homogeneous-section map,
  `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.ψ_mul`.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.isQuasicoherent_twistTarget`: the targets are
  quasi-coherent — Tag 01BG at `i`, then Tag 01LC at `i` (a closed immersion is affine, hence
  quasi-compact and quasi-separated) and at `p` (quasi-compact by Tag 0801's own hypothesis,
  quasi-separated because `Stacks.AlgebraicGeometry.RelativeProjSeparated.isSeparated_toBase`
  makes it separated).
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.mem_twistKerGradedIdeal_iff`: a homogeneous
  local section of `𝒜` of degree `n ≥ 0` lies in `ℐ` over an open `U` of the base exactly when
  its homogeneous section of `𝒪(n)` over `p⁻¹(U)` restricts to zero on `Z`.

## Implementation notes

**Where the multiplication of the target comes from.** `𝒯_d` does **not** vanish in negative
degrees, so it is not a `SheafGradedAlgebra` and the degreewise map is not a
`SheafGradedAlgebraHom`; that is exactly why
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.MulCompatibleMaps` asks for less. What supplies
the multiplication is `Stacks.Conormal.gradedPullback`, the pullback of a sheaf of graded algebras
along a morphism of schemes, which is `Stacks.RingedSpace.pullbackGradedAlgebra` read in the
vocabulary of schemes: the twists of a relative `Proj` are a sheaf of graded algebras on
`Proj_S(𝒜)` by the `algebra` field of
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`, their pullback along `i` is one on `Z`,
and the two pushforwards only reindex the opens. Both this graded structure on `i^*` of the
twists and the compatibility of the adjunction unit with it are available, and are consumed here
rather than reproved.

**The scalars of a pushforward.** `Γ(f_*M, V)` is `Γ(M, f⁻¹V)` on the nose, and the action of
`r ∈ Γ(S, V)` on it is the action of `f^#(r)`, again on the nose, so the two linearity fields of
the `SheafBilinearMap` are the linearity fields of the pulled-back multiplication with the
scalar transported by hand. Nothing is rewritten.

**Degrees.** The homogeneous-section map `ψ` of a `TwistData` is indexed by `ℕ`, while a
`MulCompatibleMaps` asks for a map in every integer degree. The family is therefore defined by a
match on the constructors of `Int`, taking the zero morphism in negative degrees — where `𝒜`
vanishes anyway — exactly as `Stacks.RelativeAmple.gradedDirectImage` does. Because `Nat.cast`
into `ℤ` is `Int.ofNat` and `Int.add` reduces on that constructor, the degree-`(n + m)` map
reduces to the one built from `ψ (n + m)` with no transport, which is what makes
`twistRestrictMap_mul` a restatement of the nonnegative case.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)

## Not done here

No Stacks tag is claimed **in this file**. What this file supplies is the graded ideal, the first of
the two inputs named in the `Not done here` section of
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/Quotient.lean`, and with it
every hypothesis of `quotAlgebra`, `isFiniteType_quotPiece`,
`isGeneratedInDegreeOneAt_quotAlgebra` and `isClosedImmersion_projQuotientHom` for Tag 0801's
ideal.

**Tag 0801 itself is proved**, under the source's own hypotheses and nothing else, as
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.exists_iso_projQuotient_twistKer` of
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/Identification.lean`, which carries the
attribute. The rest of this section records how the remaining inputs are supplied.

The **chart comparison** is
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.sectionIdeal_eq_idealOfClosedSubscheme` of
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/ChartComparison.lean`, which says that over
an affine open `U` of the base the homogeneous ideal
`sectionIdeal 𝒜 (twistKerGradedIdeal 𝒜 D i) U` is the absolute ideal of equations
`Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.idealOfClosedSubscheme (𝒜.grading U) i'` of the
closed subscheme `i'` that `Z` cuts out of the chart `Proj Γ(U, 𝒜)`. Its three ingredients are
supplied there and in
`StacksFrontier/AlgebraicGeometry/ChartBaseChange/Basic.lean`: the base change `i'` and its being a
closed immersion (`Stacks.AlgebraicGeometry.ChartBaseChange.chartRestrict`,
`isClosedImmersion_chartRestrict`), the vanishing-restriction lemma at the
`AlgebraicGeometry.pullbackGlobalSections` spelling
(`pullbackGlobalSections_chartRestrict_eq_zero_iff`), and the transport of `ψ_chart`, which needs
no appeal to `TwistRigidity.mapSection_injective` — `ChartData.mapSection` at the open `⊤` is the
inverse chart identification on the nose, because
`AlgebraicGeometry.Scheme.Modules.restrictAppIso` at `⊤` is the identity by `rfl`.

What remains for Tag 0801 is the passage from that chartwise identification of
ideals to the equality of ideal sheaves `i.ker = (projQuotientHom 𝒜 ℐ).ker` that
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.exists_iso_projQuotient_iff_ker_eq` consumes.
It needs three things.

* **The absolute identification theorem at the right kind of grading.** The existing one is not.
  `Stacks.ProjQuotientFiniteCover.ker_eq_ker_ambientHom_of_cover` and its inputs
  `Stacks.ProjQuotientChartIdeal.saturationIdentification_of_app_awayMk_eq_ideal`,
  `ambientHom_eq_projMap` and `Stacks.ClosedSubschemeProjQuotient.ambientHom` all live in a
  `variable` block `{R S : Type u} [Algebra R S] (𝒮 : ℕ → Submodule R S) [GradedAlgebra 𝒮]`,
  whereas `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.grading` is
  `ℕ → AddSubgroup (𝒜.sectionRing U)`, a `GradedRing` and not a `GradedAlgebra` over a base ring.
  The restatement is
  `Stacks.ProjQuotientFiniteCover.ker_eq_ker_projMap_quotientMk_of_cover` of
  `StacksFrontier/AlgebraicGeometry/ProjQuotientFiniteCover/GradedRing.lean`. Nothing more is needed:
  the `GradedAlgebra` hypothesis
  in that chain buys exactly one thing, `ambientHom_eq_projMap`, which identifies the glued
  `Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop` with Mathlib's `AlgebraicGeometry.Proj.map`,
  so stating the conclusion at `Proj.map` of `Stacks.HomogeneousIdeal.quotientMk` from the start
  deletes the need for it. Every other input is already at `[GradedRing 𝒮]`.
* **A chart cover of a single degree.** A finite *degree-one* cover
  would need `𝒜` generated in degree one — a hypothesis Tag 0801 does not make, so a Tag 0801
  proved that way would carry an added hypothesis and could not be registered. What is used
  instead is `Stacks.ProjQuotientFiniteCover.exists_finite_uniform_degree_cover`: a quasi-compact
  `Proj 𝒮` is covered by the standard opens of finitely many homogeneous elements of **one**
  positive degree, extracted from `AlgebraicGeometry.Proj.compactSpace_iff` by raising each
  element to the power that makes its degree the product of all the degrees, which changes no
  standard open (`AlgebraicGeometry.Proj.basicOpen_pow`). That is the device of the source's own
  proof, which takes `f_0, …, f_n ∈ A_+` and passes to `d = lcm (deg f_i)`, and the whole
  absolute chart comparison is redone at that degree in
  `StacksFrontier/AlgebraicGeometry/ProjSaturation/UniformDegree.lean` and
  `StacksFrontier/AlgebraicGeometry/ProjQuotientFiniteCover/UniformDegree.lean`. The degree-one
  hypothesis buys exactly the invertibility of the twists, and the degree-`d` form of that is
  available: `Stacks.AlgebraicGeometry.ProjInvertibleLocus`
  `.isInvertible_twistingSheaf_of_ratioLocus_eq_top` against
  `Stacks.AlgebraicGeometry.ProjShared.basicOpen_le_ratioLocus`. Quasi-compactness of the chart
  is `compactSpace_proj_grading` of the sibling `ClosedSubscheme.lean`, which is Tag 0801's own
  hypothesis on `p`.
* **The glue from chartwise kernels to the ideal sheaf.** Neither a computation of
  `(I.comap W.ι).ideal` from `I.ideal` nor a ring-level argument with
  `AlgebraicGeometry.morphismRestrict_app` is needed:
  `AlgebraicGeometry.Scheme.ker_ideal_of_isPullback_of_isOpenImmersion` **is in Mathlib**
  (`Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean`) and computes exactly the comparison wanted
  — for a cartesian square whose vertical maps are open immersions, the ideal of `f'.ker` at an
  affine open `W` of the chart is the ideal of `f.ker` at `iV ''ᵁ W`, pulled back along the
  isomorphism `iV.appIso W`. Applied to `i` and to `projQuotientHom` over one chart and cancelled
  with `Ideal.comap_injective_of_surjective`, it turns the chartwise equality of kernel ideal
  sheaves into an equality of ideals at `chart ''ᵁ D₊(f)`, which
  `AlgebraicGeometry.Scheme.IdealSheafData.ext_of_iSup_eq_top` glues. `morphismRestrict_app` is
  not used.

No Tag 0801 and no Tag 0B45 attribute is attached **in this file**: what is here is the ideal,
not the identification.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

universe u

variable {S : Scheme.{u}} (𝒜 : SheafGradedAlgebra S) (D : TwistData 𝒜)
  {Z : Scheme.{u}} (i : Z ⟶ (relativeProj 𝒜).scheme)

/-! ### The restricted twists -/

/-- **`i^*` of the twists of `Proj_S(𝒜)`, as a sheaf of graded algebras on the closed
subscheme.** The twists are a sheaf of graded algebras on `Proj_S(𝒜)` by the `algebra` field of
a `TwistData`, and the pullback of such along a morphism of schemes is again one. -/
@[ega "II 8.14.6" "more general"]
abbrev restrictTwists : SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf :=
  Stacks.Conormal.gradedPullback i D.algebra

/-- The open of `Z` lying over an open of the base: `i⁻¹(p⁻¹(V))`. -/
abbrev twistOpen (V : S.Opens) : Z.Opens := i ⁻¹ᵁ ((relativeProj 𝒜).toBase ⁻¹ᵁ V)

/-- **Tag 0801's target `𝒯_d = p_*(i_*(i^*𝒪(d)))`.** Its sections over an open `V` of the base
are, on the nose, the sections of `i^*𝒪(d)` over `i⁻¹(p⁻¹(V))`. -/
def twistTarget (d : ℤ) : S.Modules :=
  (Scheme.Modules.pushforward (relativeProj 𝒜).toBase).obj
    ((Scheme.Modules.pushforward i).obj ((restrictTwists 𝒜 D i).piece d))

/-- **The multiplication of the targets.** It is the multiplication of the pulled-back graded
algebra, read on the sections over `i⁻¹(p⁻¹(V))`; the only thing to say is that a scalar of
`Γ(S, V)` acts through the two structure morphisms, which it does definitionally. -/
def twistTargetMul (d e : ℤ) :
    SheafBilinearMap (twistTarget 𝒜 D i d) (twistTarget 𝒜 D i e) (twistTarget 𝒜 D i (d + e)) where
  app V := ((restrictTwists 𝒜 D i).mul d e).app (op (twistOpen 𝒜 i V))
  map_smul_left V r x y :=
    ((restrictTwists 𝒜 D i).mul d e).map_smul_left (op (twistOpen 𝒜 i V))
      (i.app ((relativeProj 𝒜).toBase ⁻¹ᵁ V) ((relativeProj 𝒜).toBase.app V r)) x y
  map_smul_right V r x y :=
    ((restrictTwists 𝒜 D i).mul d e).map_smul_right (op (twistOpen 𝒜 i V))
      (i.app ((relativeProj 𝒜).toBase ⁻¹ᵁ V) ((relativeProj 𝒜).toBase.app V r)) x y
  naturality {V W} h x y := ((restrictTwists 𝒜 D i).mul d e).naturality
    (homOfLE (show twistOpen 𝒜 i V ≤ twistOpen 𝒜 i W from fun _ hz => h hz)).op x y

/-! ### Quasi-coherence of the targets -/

/-- **The targets are quasi-coherent.** The pullback of a quasi-coherent module is quasi-coherent
(Tag 01BG), and the pushforward along a quasi-compact quasi-separated morphism is (Tag 01LC):
along `i`, which is a closed immersion, and along `p`, which is quasi-compact by hypothesis and
separated by `Stacks.AlgebraicGeometry.RelativeProjSeparated.isSeparated_toBase`. -/
instance isQuasicoherent_twistTarget [IsClosedImmersion i]
    [QuasiCompact (relativeProj 𝒜).toBase] (d : ℤ) :
    (twistTarget 𝒜 D i d).IsQuasicoherent := by
  have : IsSeparated (relativeProj 𝒜).toBase :=
    Stacks.AlgebraicGeometry.RelativeProjSeparated.isSeparated_toBase 𝒜 (relativeProj 𝒜)
  have : ((restrictTwists 𝒜 D i).piece d).IsQuasicoherent :=
    Stacks.Conormal.gradedPullback_isQuasicoherent i D.algebra
      (fun n => D.isQuasicoherent n) d
  have : ((Scheme.Modules.pushforward i).obj ((restrictTwists 𝒜 D i).piece d)).IsQuasicoherent :=
    AlgebraicGeometry.pushforward_isQuasicoherent i ((restrictTwists 𝒜 D i).piece d)
  exact AlgebraicGeometry.pushforward_isQuasicoherent (relativeProj 𝒜).toBase
    ((Scheme.Modules.pushforward i).obj ((restrictTwists 𝒜 D i).piece d))

/-! ### The degreewise map -/

/-- The degreewise map `𝒜_n ⟶ p_*(i_*(i^*𝒪(n)))` in a nonnegative degree: the
homogeneous-section map of Tag 01NR followed by the unit of the pullback–pushforward adjunction
at the closed immersion. -/
def twistRestrictMapNat (n : ℕ) : 𝒜.piece (n : ℤ) ⟶ twistTarget 𝒜 D i (n : ℤ) :=
  D.ψ n ≫ (Scheme.Modules.pushforward (relativeProj 𝒜).toBase).map
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (D.algebra.piece (n : ℤ)))

/-- **Tag 0801's degreewise map `𝒜_d ⟶ p_*(i_*(i^*𝒪(d)))`**, in every integer degree: the map
above in a nonnegative degree, and the zero morphism in a negative one, where `𝒜` vanishes. -/
def twistRestrictMap : (d : ℤ) → (𝒜.piece d ⟶ twistTarget 𝒜 D i d)
  | (n : ℕ) => twistRestrictMapNat 𝒜 D i n
  | .negSucc _ => 0

/-- In a nonnegative degree, `twistRestrictMap` is the degreewise map `twistRestrictMapNat`. -/
@[simp]
theorem twistRestrictMap_natCast (n : ℕ) :
    twistRestrictMap 𝒜 D i (n : ℤ) = twistRestrictMapNat 𝒜 D i n := rfl

/-- On the sections over an open of the base the map is the pullback along `i`, in the sense of
`AlgebraicGeometry.Scheme.Modules.pullbackSection`, of the homogeneous section named by `ψ`. -/
theorem twistRestrictMapNat_app (n : ℕ) (U : S.Opens) (a : Γ(𝒜.piece (n : ℤ), U)) :
    (twistRestrictMapNat 𝒜 D i n).val.app (op U) a =
      Scheme.Modules.pullbackSection i (D.algebra.piece (n : ℤ))
        ((relativeProj 𝒜).toBase ⁻¹ᵁ U) (twistOpen 𝒜 i U) le_rfl
        ((D.ψ n).val.app (op U) a) :=
  (Stacks.Conormal.pullbackSection_self i (D.algebra.piece (n : ℤ))
    ((relativeProj 𝒜).toBase ⁻¹ᵁ U) ((D.ψ n).val.app (op U) a)).symm

/-! ### Multiplicativity -/

/-- **The degreewise maps are multiplicative, in nonnegative degrees.** The homogeneous-section
map carries the product of `𝒜` to the product of the twists (`TwistData.ψ_mul`), and the unit of
the pullback–pushforward adjunction carries that product to the product of the pulled-back graded
algebra (`Stacks.Conormal.gradedPullback_mul_pullbackSection`). -/
theorem twistRestrictMapNat_mul (n m : ℕ) (U : S.Opens) (a : Γ(𝒜.piece (n : ℤ), U))
    (b : Γ(𝒜.piece (m : ℤ), U)) :
    (twistRestrictMapNat 𝒜 D i (n + m)).val.app (op U) ((𝒜.mul (n : ℤ) (m : ℤ)).app U a b) =
      ((restrictTwists 𝒜 D i).mul (n : ℤ) (m : ℤ)).app (op (twistOpen 𝒜 i U))
        ((twistRestrictMapNat 𝒜 D i n).val.app (op U) a)
        ((twistRestrictMapNat 𝒜 D i m).val.app (op U) b) := by
  rw [twistRestrictMapNat_app 𝒜 D i n U a, twistRestrictMapNat_app 𝒜 D i m U b,
    Stacks.Conormal.gradedPullback_mul_pullbackSection i D.algebra (n : ℤ) (m : ℤ)
      ((relativeProj 𝒜).toBase ⁻¹ᵁ U) ((D.ψ n).val.app (op U) a)
      ((D.ψ m).val.app (op U) b)]
  exact (twistRestrictMapNat_app 𝒜 D i (n + m) U ((𝒜.mul (n : ℤ) (m : ℤ)).app U a b)).trans
    (congrArg (fun z : Γ(D.algebra.piece ((n : ℤ) + (m : ℤ)),
        (relativeProj 𝒜).toBase ⁻¹ᵁ U) =>
      Scheme.Modules.pullbackSection i (D.algebra.piece ((n : ℤ) + (m : ℤ)))
        ((relativeProj 𝒜).toBase ⁻¹ᵁ U) (twistOpen 𝒜 i U) le_rfl z)
      (eq_of_heq (D.ψ_mul U n m a b)))

/-- A homogeneous local section of a negative degree vanishes, the piece being a zero module. -/
private theorem piece_eq_zero_of_neg {d : ℤ} (hd : d < 0) (U : S.Opens)
    (x : Γ(𝒜.piece d, U)) : x = 0 :=
  Stacks.SheafOfModules.eq_zero_of_isZero (𝒜.negative_isZero d hd) (op U) x

/-- The degreewise map kills the zero section. -/
private theorem map_app_zero (c : ℤ) (U : S.Opens) :
    (twistRestrictMap 𝒜 D i c).val.app (op U) (0 : Γ(𝒜.piece c, U)) = 0 :=
  map_zero _

/-- A bilinear map of additive monoids vanishes when its first argument does. -/
private theorem bilinear_zero_left {M N P : Type*} [AddZeroClass M] [AddZeroClass N]
    [AddCommMonoid P] (f : M →+ N →+ P) (y : N) : f 0 y = 0 :=
  (DFunLike.congr_fun (map_zero f) y).trans (AddMonoidHom.zero_apply y)

/-- **The degreewise maps are multiplicative**, in every pair of integer degrees. In a negative
degree the relevant factor vanishes and both sides are zero. -/
theorem twistRestrictMap_mul (d e : ℤ) (U : S.Opens) (a : Γ(𝒜.piece d, U))
    (b : Γ(𝒜.piece e, U)) :
    (twistRestrictMap 𝒜 D i (d + e)).val.app (op U) ((𝒜.mul d e).app U a b) =
      (twistTargetMul 𝒜 D i d e).app U ((twistRestrictMap 𝒜 D i d).val.app (op U) a)
        ((twistRestrictMap 𝒜 D i e).val.app (op U) b) := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [piece_eq_zero_of_neg 𝒜 hd U a, bilinear_zero_left, map_app_zero 𝒜 D i (d + e) U,
      map_app_zero 𝒜 D i d U]
    exact (bilinear_zero_left _ _).symm
  rcases lt_or_ge e 0 with he | he
  · rw [piece_eq_zero_of_neg 𝒜 he U b, map_zero, map_app_zero 𝒜 D i (d + e) U,
      map_app_zero 𝒜 D i e U]
    exact (map_zero _).symm
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hd
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le he
  exact twistRestrictMapNat_mul 𝒜 D i n m U a b

/-! ### The graded ideal -/

/-- **Tag 0801's datum, as a `MulCompatibleMaps`.** The targets `p_*(i_*(i^*𝒪(d)))`, their
multiplication, the degreewise maps, and the multiplicativity of the latter. -/
def twistMulCompatibleMaps [IsClosedImmersion i] [QuasiCompact (relativeProj 𝒜).toBase] :
    MulCompatibleMaps 𝒜 where
  target d := twistTarget 𝒜 D i d
  isQuasicoherent d := isQuasicoherent_twistTarget 𝒜 D i d
  map d := twistRestrictMap 𝒜 D i d
  targetMul d e := twistTargetMul 𝒜 D i d e
  map_mul d e U a b := twistRestrictMap_mul 𝒜 D i d e U a b

/-- **The graded ideal of a closed subscheme of a relative Proj**, with quasi-coherent
homogeneous pieces: the degreewise kernel of `𝒜_d ⟶ p_*(i_*(i^*𝒪(d)))`. This is the ideal
Stacks Tag 0801 forms, and it is what
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.quotAlgebra` consumes. -/
def twistKerGradedIdeal [IsClosedImmersion i] [QuasiCompact (relativeProj 𝒜).toBase] :
    QcohGradedIdeal 𝒜 :=
  kerQcohGradedIdeal 𝒜 (twistMulCompatibleMaps 𝒜 D i)

/-- **Membership in the graded ideal**, in a nonnegative degree: a homogeneous local section `a`
of `𝒜_n` over an open `U` of the base is an equation for `Z` exactly when the section of `𝒪(n)`
over `p⁻¹(U)` that `ψ` names restricts to zero on `Z`. -/
theorem mem_twistKerGradedIdeal_iff [IsClosedImmersion i]
    [QuasiCompact (relativeProj 𝒜).toBase] (n : ℕ) (U : S.Opens)
    (a : Γ(𝒜.piece (n : ℤ), U)) :
    a ∈ ((twistKerGradedIdeal 𝒜 D i).piece (n : ℤ)).toSubmodule.obj (op U) ↔
      Scheme.Modules.pullbackSection i (D.algebra.piece (n : ℤ))
          ((relativeProj 𝒜).toBase ⁻¹ᵁ U) (twistOpen 𝒜 i U) le_rfl
          ((D.ψ n).val.app (op U) a) = 0 := by
  rw [twistKerGradedIdeal, kerQcohGradedIdeal_piece,
    mem_kerPiece_iff 𝒜 (twistMulCompatibleMaps 𝒜 D i) (n : ℤ) U a]
  exact Iff.of_eq (congrArg (fun z => z = 0) (twistRestrictMapNat_app 𝒜 D i n U a))

end Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

end
