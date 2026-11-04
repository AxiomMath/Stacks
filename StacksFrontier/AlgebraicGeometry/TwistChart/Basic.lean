module

public import StacksFrontier.AlgebraicGeometry.TwistGenerator.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.Basic
public import StacksFrontier.AlgebraicGeometry.ProjPolynomialSections.GradedIso
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeScaling
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwist
public import StacksFrontier.AlgebraicGeometry.RelativeProjGlue.Basic

/-!
# The chart comparison of a twisted graded algebra over a trivializing open

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra in the sense of Situation 01NN and
`ℒ` an invertible `𝒪_S`-module. The twist `ℬ = 𝒜 ⊗ ℒ^{⊗ •}` of Tag 02NB has the same relative
homogeneous spectrum as `𝒜`, and the isomorphism of Tag 02NC is glued from comparisons over the
affine opens of `S` on which `ℒ` is trivial. **This file builds one such chart comparison, and
proves the two facts that the glueing consumes.**

Over an open `W` trivializing `ℒ` the generator family `gen d` of
`StacksFrontier/AlgebraicGeometry/TwistGenerator/Basic.lean` gives, in every nonnegative degree at
once, a section of `ℒ^{⊗ d}` over `W` that generates it, and the family is multiplicative. So
`x ↦ x ⊗ gen d` is a bijection `Γ(𝒜_d, W) → Γ(ℬ_d, W)` in every degree, it carries the
multiplication of `𝒜` to that of `ℬ` and the unit to the unit, and therefore assembles into an
isomorphism of the graded rings of sections over `W`. Taking `Proj` of that isomorphism — over an
affine open `U`, where the graded ring of sections is what the relative construction consumes —
gives `chartProjIso`, an isomorphism of the chart of `Proj_S(ℬ)` over `U` with the chart of
`Proj_S(𝒜)` over `U`, and `chartProjIso_hom_toBase` says it is an isomorphism over the base.

The chart comparison depends on the chosen trivialization, but the isomorphism of charts does
not: two trivializations of `ℒ` over `W` differ by a unit `u` of `𝒪_S(W)`, so their generator
families differ by `u ^ d` in degree `d`, so the two graded ring isomorphisms differ by rescaling
the degree-`d` part by the degree-`0` unit `u ^ d` — which induces the *same* morphism of
projective spectra. That is `chartProjIso_eq`. Together with `chartProjIso_naturality`, the
commuting square relating the comparisons over `U' ⊆ U` with the transition morphisms of the
charts, these are exactly the two compatibilities a glueing over a trivializing cover of `S`
needs.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistChart.chartPiece`: **the degreewise comparison**
  `Γ(𝒜_d, W) → Γ(ℬ_d, W)`, tensoring with the degree-`d` generator.
* `Stacks.AlgebraicGeometry.TwistChart.chartRingHom` and `chartRingEquiv`: the comparison of the
  graded rings of sections over `W`, as a ring homomorphism and as a ring isomorphism.
* `Stacks.AlgebraicGeometry.TwistChart.chartGradedHom` and `chartGradedInv`: the comparison as a
  pair of mutually inverse homomorphisms of *internally graded* rings.
* `Stacks.AlgebraicGeometry.TwistChart.chartProjIso`: **the isomorphism of the two charts** over
  an affine open `U` of the base trivializing `ℒ`.

## Main results

* `Stacks.AlgebraicGeometry.TwistChart.bijective_chartPiece`,
  `Stacks.AlgebraicGeometry.TwistChart.chartPiece_mul` and `chartPiece_one`: the degreewise
  comparison is bijective, multiplicative and unital — the three inputs that turn it into an
  isomorphism of graded rings.
* `Stacks.AlgebraicGeometry.TwistChart.chartRingHom_strHom`: the comparison is an
  `𝒪_S(W)`-algebra map, that is, it carries one structure map to the other.
* `Stacks.AlgebraicGeometry.TwistChart.chartProjIso_hom_toSpecZero` and
  `strZero_comp_zeroHom_chartGradedHom`, hence
  `Stacks.AlgebraicGeometry.TwistChart.chartProjIso_hom_toBase`: **the chart isomorphism is an
  isomorphism over the base.**
* `Stacks.AlgebraicGeometry.TwistChart.chartProjIso_eq`: **the chart isomorphism does not depend
  on the trivialization.**
* `Stacks.AlgebraicGeometry.TwistChart.chartProjIso_naturality`: **the chart isomorphisms commute
  with the transition morphisms of the charts**, so they are natural in the affine open.

## Implementation notes

**No tag is claimed here.** The assertion of Tag 02NC is about the *glued* relative
spectra — an isomorphism `Proj_S(ℬ) ≅ Proj_S(𝒜)` over `S` — and nothing of that statement is
proved in this file: what is built here is one chart of it, together with the independence and
naturality that a later file consumes to glue. The attribute belongs on the assembled statement,
so it is attached there and not to anything below.

**The ring isomorphism is derived, not constructed twice.** `chartRingHom` is built with
`DirectSum.toSemiring` out of the degreewise comparisons, exactly as
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.resRingHom` is; its two
obligations are `chartPiece_one` and `chartPiece_mul`. Multiplicativity of the *inverse* is never
proved directly. Instead the inverse is assembled as an additive map `chartInvAddHom` from the
degreewise inverses, the two composites are identified by `DirectSum.induction_on`, and
`RingEquiv.ofBijective` turns the ring homomorphism plus bijectivity into `chartRingEquiv`. For
the same reason no statement below mentions `GradedMonoid.GMul.mul`: multiplicativity is stated in
the sheaf-level form `chartPiece_mul`, with `DirectSum.of_mul_of` and
`SheafGradedAlgebra.gMul_def` consumed inside the construction.

**Degree casts.** The two sides of `chartPiece_mul` sit in degrees `(i : ℤ) + (j : ℤ)` and
`((i + j : ℕ) : ℤ)`, which are the same term up to `whnf`, since `Nat.cast` into `ℤ` is `Int.ofNat`
and `Int.add` reduces on constructors. They are therefore bridged by `congrArg₂` at one spelling
and `exact` at the other, never by `rw`: the rewrite motive is not type-correct at `implicit`
transparency. `chartProjIso_hom_toBase` is written in term mode for the same reason — the
degree-zero part of a graded ring homomorphism reaches `CommRingCat.ofHom` through a `CommRing`
instance that `rw` cannot see is the one `strZero` uses.

**Two spellings of the ring of sections, and where each is forced.** `Γ(S, W)` and
`(structureRingPresheaf 𝒪_S).obj (op W)` are definitionally equal, but the scalar actions
attached to them are found by instance search at *different* spellings of the module: sections of
a tensor power written through `TwistGenerator.pow` take scalars from the latter, while the
homogeneous sections `SheafGradedAlgebra.sectionPieces`, written with the `Γ(M, W)` notation,
take them from the former. So `gen_eq_pow_smul` is stated with the second and
`exists_unit_chartPiece_eq` with the first, and the bridge is that a variable of either type is
accepted where the other is expected. For the same reason the scalar of a `•` written by hand is
always a variable or a lemma's own conclusion, never a type-ascribed compound term, whose inferred
type would be the spelling instance search cannot use.

**Independence of the trivialization** goes through `Proj` rather than through the graded rings:
the two comparisons are *not* equal, they differ by the degree-zero unit `u ^ d` in degree `d`, and
`Stacks.GradedRing.Proj_map_eq_of_target_degreeScale` is exactly the statement that such a pair
induces one morphism of projective spectra. The transfer between the glued morphism
`RelativeProj.mapHomOfTop` and Mathlib's `AlgebraicGeometry.Proj.map` is
`RelativeProj.mapHomOfTop_eq_map`, and equality of the isomorphisms follows from equality of their
`hom` parts by `Iso.ext`.

**Naturality** reduces to a square of graded ring homomorphisms that commutes *on the nose*:
restricting `x ⊗ gen d` along `W' ≤ W` gives `res x ⊗ gen' d` for the restricted trivialization,
by `GradedAlgebraTwist.tensorSectionsAt_naturality` and `TwistGenerator.res_gen`. The arbitrary
trivialization over the smaller open is replaced by the restricted one using `chartProjIso_eq`
first, and the square of graded ring homomorphisms is turned into a square of morphisms by
`ProjBundleSurjection.mapHomOfTop_comp` on each composite and
`ProjPolynomialSections.mapHomOfTop_congr`.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 02NB](https://stacks.math.columbia.edu/tag/02NB)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry DirectSum
open Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf structureSheaf)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist (twist)
open Stacks.AlgebraicGeometry.TwistGenerator (pow gen)

universe u

namespace Stacks.AlgebraicGeometry.TwistChart

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Scheme.{u}} (𝒜 : Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra S)
  (L : S.Modules) [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]
  {W : S.Opens} (e : L.over W ≅ SheafOfModules.unit (S.ringCatSheaf.over W))

/-! ### The degreewise comparison -/

/-- **The chart comparison in degree `d`**: a homogeneous section of `𝒜` of degree `d` over a
trivializing open `W` is sent to its tensor product with the degree-`d` member of the generator
family of the tensor powers of `ℒ`, a homogeneous section of the twist of the same degree.
Additivity is additivity of the tensor product of sections in its first argument. -/
def chartPiece (d : ℕ) : 𝒜.sectionPieces W d →+ (twist 𝒜 L).sectionPieces W d :=
  AddMonoidHom.mk'
    (fun x => tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op W) (𝒜.piece (d : ℤ))
      (pow L (d : ℤ)) x (gen L e d))
    (fun x y => GradedAlgebraTwist.tensorSectionsAt_add_left S.sheaf.obj
      S.ringCatSheaf.property (op W) (𝒜.piece (d : ℤ)) (pow L (d : ℤ)) x y (gen L e d))

/-- The defining formula of the degreewise comparison. -/
theorem chartPiece_apply (d : ℕ) (x : 𝒜.sectionPieces W d) :
    chartPiece 𝒜 L e d x = tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op W)
      (𝒜.piece (d : ℤ)) (pow L (d : ℤ)) x (gen L e d) := rfl

/-- **The degreewise comparison is bijective.** This is exactly the statement that the degree-`d`
member of the generator family generates `ℒ^{⊗ d}` over `W`, applied to the second factor
`𝒜_d`. -/
theorem bijective_chartPiece (d : ℕ) : Function.Bijective (chartPiece 𝒜 L e d) :=
  TwistGenerator.bijective_tensorSectionsAt_gen L e d (𝒜.piece (d : ℤ))

/-- **The degreewise comparison is multiplicative.** The multiplication of the twist on a pair of
pure sections multiplies the two sections of `𝒜` and the two generators separately, and the
generator family is multiplicative; so the product of the comparisons of `a` and `b` is the
comparison of the product.

The two sides lie in degrees `(i : ℤ) + (j : ℤ)` and `((i + j : ℕ) : ℤ)`, which are definitionally
equal; the `congrArg₂` is written at the first spelling and read at the second. -/
theorem chartPiece_mul (i j : ℕ) (a : 𝒜.sectionPieces W i) (b : 𝒜.sectionPieces W j) :
    ((twist 𝒜 L).mul (i : ℤ) (j : ℤ)).app W
        (chartPiece 𝒜 L e i a) (chartPiece 𝒜 L e j b) =
      chartPiece 𝒜 L e (i + j) ((𝒜.mul (i : ℤ) (j : ℤ)).app W a b) := by
  refine (GradedAlgebraTwist.mulSection_pure S.sheaf.obj S.ringCatSheaf.property
    𝒜.piece (GradedAlgebraTwist.mulHom 𝒜) L (i : ℤ) (j : ℤ) (op W) a (gen L e i) b
    (gen L e j)).trans ?_
  refine congrArg₂ (fun x y => tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op W)
    (𝒜.piece ((i : ℤ) + (j : ℤ))) (pow L ((i : ℤ) + (j : ℤ))) x y) ?_ ?_
  · exact GradedAlgebraTwist.mulHom_app 𝒜 (i : ℤ) (j : ℤ) (op W) a b
  · refine Eq.trans (GradedAlgebraTwist.coherentMulIso_app_eq_mulBilinear S.sheaf.obj
      S.ringCatSheaf.property L (i : ℤ) (j : ℤ) (op W) (gen L e i) (gen L e j)) ?_
    exact TwistGenerator.mulBilinear_gen L e i j

/-- **The degreewise comparison is unital.** The unit of the twist is the unit of `𝒜` tensored
with the unit section of the zeroth tensor power, which is the degree-`0` member of the generator
family. -/
theorem chartPiece_one : chartPiece 𝒜 L e 0 (𝒜.one W) = (twist 𝒜 L).one W :=
  congrArg (fun x => tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op W) (𝒜.piece 0)
      (pow L 0) x (gen L e 0))
    (GradedAlgebraTwist.oneHom_app 𝒜 (op W)).symm

/-! ### The comparison of the graded rings of sections -/

/-- **The comparison of the graded rings of sections over a trivializing open**, assembled from
the degreewise comparisons. Unitality is `chartPiece_one` and multiplicativity on the homogeneous
summands is `chartPiece_mul`. -/
def chartRingHom : 𝒜.sectionRing W →+* (twist 𝒜 L).sectionRing W :=
  DirectSum.toSemiring
    (fun n => (DirectSum.of ((twist 𝒜 L).sectionPieces W) n).comp (chartPiece 𝒜 L e n))
    ((congrArg (DirectSum.of ((twist 𝒜 L).sectionPieces W) 0) (chartPiece_one 𝒜 L e)).trans
      (DirectSum.one_def _).symm)
    (fun {i j} a b => by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply]
      rw [DirectSum.of_mul_of]
      exact congrArg (DirectSum.of ((twist 𝒜 L).sectionPieces W) (i + j))
        (chartPiece_mul 𝒜 L e i j a b).symm)

/-- The comparison on a homogeneous summand is the degreewise comparison. -/
theorem chartRingHom_of (n : ℕ) (y : 𝒜.sectionPieces W n) :
    chartRingHom 𝒜 L e (DirectSum.of (𝒜.sectionPieces W) n y) =
      DirectSum.of ((twist 𝒜 L).sectionPieces W) n (chartPiece 𝒜 L e n y) :=
  DirectSum.toSemiring_of _ _ _ n y

/-- The degreewise comparison read as an isomorphism of additive groups. -/
def chartPieceEquiv (d : ℕ) : 𝒜.sectionPieces W d ≃+ (twist 𝒜 L).sectionPieces W d :=
  AddEquiv.ofBijective (chartPiece 𝒜 L e d) (bijective_chartPiece 𝒜 L e d)

/-- The inverse comparison as an *additive* map, assembled from the degreewise inverses. Its
multiplicativity is never proved: it is obtained from `chartRingHom` and bijectivity instead. -/
def chartInvAddHom : (twist 𝒜 L).sectionRing W →+ 𝒜.sectionRing W :=
  DirectSum.toAddMonoid fun n => (DirectSum.of (𝒜.sectionPieces W) n).comp
    (chartPieceEquiv 𝒜 L e n).symm.toAddMonoidHom

/-- The additive inverse undoes the comparison. -/
theorem chartInvAddHom_chartRingHom (x : 𝒜.sectionRing W) :
    chartInvAddHom 𝒜 L e (chartRingHom 𝒜 L e x) = x := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of n y =>
      rw [chartRingHom_of, chartInvAddHom, DirectSum.toAddMonoid_of]
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
      exact congrArg (DirectSum.of (𝒜.sectionPieces W) n)
        ((chartPieceEquiv 𝒜 L e n).symm_apply_apply y)
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The comparison undoes the additive inverse. -/
theorem chartRingHom_chartInvAddHom (y : (twist 𝒜 L).sectionRing W) :
    chartRingHom 𝒜 L e (chartInvAddHom 𝒜 L e y) = y := by
  induction y using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of n z =>
      rw [chartInvAddHom, DirectSum.toAddMonoid_of]
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
      rw [chartRingHom_of]
      exact congrArg (DirectSum.of ((twist 𝒜 L).sectionPieces W) n)
        ((chartPieceEquiv 𝒜 L e n).apply_symm_apply z)
  | add y z hy hz => rw [map_add, map_add, hy, hz]

/-- **The comparison of the graded rings of sections is bijective.** -/
theorem bijective_chartRingHom : Function.Bijective (chartRingHom 𝒜 L e) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨chartInvAddHom 𝒜 L e, chartInvAddHom_chartRingHom 𝒜 L e, chartRingHom_chartInvAddHom 𝒜 L e⟩

/-- **The comparison of the graded rings of sections as a ring isomorphism.** -/
def chartRingEquiv : 𝒜.sectionRing W ≃+* (twist 𝒜 L).sectionRing W :=
  RingEquiv.ofBijective (chartRingHom 𝒜 L e) (bijective_chartRingHom 𝒜 L e)

/-- The ring isomorphism acts as the comparison homomorphism. -/
theorem chartRingEquiv_apply (x : 𝒜.sectionRing W) :
    chartRingEquiv 𝒜 L e x = chartRingHom 𝒜 L e x := rfl

/-- The underlying ring homomorphism of the ring isomorphism is the comparison. -/
theorem chartRingEquiv_toRingHom :
    (chartRingEquiv 𝒜 L e).toRingHom = chartRingHom 𝒜 L e := rfl

/-- The inverse isomorphism takes a homogeneous summand to the same homogeneous summand. This is
what makes the inverse comparison a homomorphism of *graded* rings. -/
theorem chartRingEquiv_symm_of (n : ℕ) (y : (twist 𝒜 L).sectionPieces W n) :
    (chartRingEquiv 𝒜 L e).symm (DirectSum.of ((twist 𝒜 L).sectionPieces W) n y) =
      DirectSum.of (𝒜.sectionPieces W) n ((chartPieceEquiv 𝒜 L e n).symm y) := by
  refine (chartRingEquiv 𝒜 L e).injective ?_
  rw [RingEquiv.apply_symm_apply, chartRingEquiv_apply, chartRingHom_of]
  exact (congrArg (DirectSum.of ((twist 𝒜 L).sectionPieces W) n)
    ((chartPieceEquiv 𝒜 L e n).apply_symm_apply y)).symm

/-! ### The comparison as a homomorphism of internally graded rings -/

/-- **The comparison as a graded ring homomorphism.** -/
def chartGradedHom : 𝒜.grading W →+*ᵍ (twist 𝒜 L).grading W where
  __ := chartRingHom 𝒜 L e
  map_mem := fun {_ _} hx => by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨_, (chartRingHom_of 𝒜 L e _ y).symm⟩

/-- **The inverse comparison as a graded ring homomorphism.** -/
def chartGradedInv : (twist 𝒜 L).grading W →+*ᵍ 𝒜.grading W where
  __ := (chartRingEquiv 𝒜 L e).symm.toRingHom
  map_mem := fun {n _} hx => by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨(chartPieceEquiv 𝒜 L e n).symm y, (chartRingEquiv_symm_of 𝒜 L e n y).symm⟩

/-- The two graded ring homomorphisms are mutually inverse, one way round. -/
theorem chartGradedHom_inv (x) :
    chartGradedHom 𝒜 L e (chartGradedInv 𝒜 L e x) = x :=
  (chartRingEquiv 𝒜 L e).apply_symm_apply x

/-- The two graded ring homomorphisms are mutually inverse, the other way round. -/
theorem chartGradedInv_hom (x) :
    chartGradedInv 𝒜 L e (chartGradedHom 𝒜 L e x) = x :=
  (chartRingEquiv 𝒜 L e).symm_apply_apply x

/-- **The comparison is an `𝒪_S(W)`-algebra map**: it carries the structure map of one graded
ring of sections to that of the other. Both structure maps send a function to its multiple of the
unit, the comparison is linear in the section of `𝒜`, and it is unital. -/
theorem chartRingHom_strHom (r : Γ(S, W)) :
    chartRingHom 𝒜 L e (𝒜.strHom W r) = (twist 𝒜 L).strHom W r := by
  rw [SheafGradedAlgebra.strHom_apply, chartRingHom_of, SheafGradedAlgebra.strHom_apply]
  refine congrArg (DirectSum.of ((twist 𝒜 L).sectionPieces W) 0) ?_
  refine Eq.trans ?_ (congrArg (fun y : (twist 𝒜 L).sectionPieces W 0 => r • y)
    (chartPiece_one 𝒜 L e))
  exact GradedAlgebraTwist.tensorSectionsAt_smul_left S.sheaf.obj
    S.ringCatSheaf.property (op W) (𝒜.piece 0) (pow L 0) r (𝒜.one W) (gen L e 0)

/-! ### The isomorphism of charts -/

/-- **The chart of `Proj_S(𝒜 ⊗ ℒ^{⊗ •})` over an affine open trivializing `ℒ` is the chart of
`Proj_S(𝒜)`.** This is one chart of [Stacks, Tag 02NC]; the statement is at the chart type of the
relative homogeneous spectrum, so that the glueing can consume it directly. -/
def chartProjIso (U : S.AffineZariskiSite)
    (e : L.over U.toOpens ≅ SheafOfModules.unit (S.ringCatSheaf.over U.toOpens)) :
    (twist 𝒜 L).toGradedAlgebra.projOver U ≅ 𝒜.toGradedAlgebra.projOver U :=
  ProjPolynomialSections.projIsoOfGradedSections _ _ (chartGradedHom 𝒜 L e)
    (chartGradedInv 𝒜 L e) (chartGradedHom_inv 𝒜 L e) (chartGradedInv_hom 𝒜 L e)

/-- The forward morphism of the chart isomorphism is the morphism of projective spectra induced
by the comparison, which is defined everywhere because the comparison has a graded section. -/
theorem chartProjIso_hom (U : S.AffineZariskiSite)
    (e : L.over U.toOpens ≅ SheafOfModules.unit (S.ringCatSheaf.over U.toOpens)) :
    (chartProjIso 𝒜 L U e).hom =
      ProjPolynomialSections.mapHomOfSection _ _ (chartGradedHom 𝒜 L e) (chartGradedInv 𝒜 L e)
        (chartGradedHom_inv 𝒜 L e) := rfl

/-! ### The chart isomorphism is an isomorphism over the base -/

/-- **The degree-zero part of the comparison carries one degree-zero identification of the base to
the other.** Both are the structure map of the graded ring of sections projected to degree zero,
and the comparison carries one structure map to the other by
`Stacks.AlgebraicGeometry.TwistChart.chartRingHom_strHom`. -/
theorem strZero_comp_zeroHom_chartGradedHom (U : S.AffineZariskiSite)
    (e : L.over U.toOpens ≅ SheafOfModules.unit (S.ringCatSheaf.over U.toOpens)) :
    𝒜.toGradedAlgebra.strZero U ≫ CommRingCat.ofHom
        (RelativeProj.zeroHom _ _ (chartGradedHom 𝒜 L e)) =
      (twist 𝒜 L).toGradedAlgebra.strZero U := by
  refine CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext ?_)
  refine Eq.trans (RelativeProj.coe_zeroHom_apply _ _ (chartGradedHom 𝒜 L e) _) ?_
  refine Eq.trans (congrArg (chartRingHom 𝒜 L e)
    (𝒜.toGradedAlgebra.coe_strZero_apply U r)) ?_
  refine Eq.trans (chartRingHom_strHom 𝒜 L e r) ?_
  exact ((twist 𝒜 L).toGradedAlgebra.coe_strZero_apply U r).symm

/-- The comparison of the graded rings of sections has full domain of definition on `Proj`. -/
private theorem mapDomain_chartGradedHom_eq_top :
    ProjShared.mapDomain (𝒜.grading W) ((twist 𝒜 L).grading W) (chartGradedHom 𝒜 L e) = ⊤ :=
  ProjShared.mapDomain_eq_top_of_irrelevant_le_map _ _ _
    (ProjPolynomialSections.irrelevant_le_map_of_graded_section _ _ (chartGradedHom 𝒜 L e)
      (chartGradedInv 𝒜 L e) (chartGradedHom_inv 𝒜 L e))

/-- **The chart isomorphism commutes with the structure morphisms to the spectra of the
degree-zero parts.** This is the commuting square of [Stacks, Tag 01NO] for the comparison. -/
theorem chartProjIso_hom_toSpecZero (U : S.AffineZariskiSite)
    (e : L.over U.toOpens ≅ SheafOfModules.unit (S.ringCatSheaf.over U.toOpens)) :
    (chartProjIso 𝒜 L U e).hom ≫
        AlgebraicGeometry.Proj.toSpecZero (𝒜.toGradedAlgebra.grading U) =
      AlgebraicGeometry.Proj.toSpecZero ((twist 𝒜 L).toGradedAlgebra.grading U) ≫
        Spec.map (CommRingCat.ofHom
          (RelativeProj.zeroHom _ _ (chartGradedHom 𝒜 L e))) :=
  RelativeProj.mapHomOfTop_toSpecZero _ _ (chartGradedHom 𝒜 L e)
    (mapDomain_chartGradedHom_eq_top 𝒜 L e)

/-- **The chart isomorphism is a morphism over the base**: it commutes with the structure
morphisms of the two charts to the base scheme. The structure morphism of a chart factors through
the spectrum of the degree-zero part and the spectrum of the sections of `𝒪_S` over the affine
open, so this is the square of [Stacks, Tag 01NO] followed by the contravariance of `Spec` applied
to `Stacks.AlgebraicGeometry.TwistChart.strZero_comp_zeroHom_chartGradedHom`.

This is the compatibility that the glueing of the charts over the base consumes. -/
theorem chartProjIso_hom_toBase (U : S.AffineZariskiSite)
    (e : L.over U.toOpens ≅ SheafOfModules.unit (S.ringCatSheaf.over U.toOpens)) :
    (chartProjIso 𝒜 L U e).hom ≫ 𝒜.toGradedAlgebra.toBase U =
      (twist 𝒜 L).toGradedAlgebra.toBase U := by
  have hzero : Spec.map (CommRingCat.ofHom
          (RelativeProj.zeroHom _ _ (chartGradedHom 𝒜 L e))) ≫
        Spec.map (𝒜.toGradedAlgebra.strZero U) ≫ U.2.fromSpec =
      Spec.map ((twist 𝒜 L).toGradedAlgebra.strZero U) ≫ U.2.fromSpec :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ U.2.fromSpec)
      ((Spec.map_comp (𝒜.toGradedAlgebra.strZero U) _).symm.trans
        (congrArg Spec.map (strZero_comp_zeroHom_chartGradedHom 𝒜 L U e))))
  show (chartProjIso 𝒜 L U e).hom ≫ AlgebraicGeometry.Proj.toSpecZero
        (𝒜.toGradedAlgebra.grading U) ≫ Spec.map (𝒜.toGradedAlgebra.strZero U) ≫ U.2.fromSpec =
      AlgebraicGeometry.Proj.toSpecZero ((twist 𝒜 L).toGradedAlgebra.grading U) ≫
        Spec.map ((twist 𝒜 L).toGradedAlgebra.strZero U) ≫ U.2.fromSpec
  refine Eq.trans (Category.assoc _ _ _).symm (Eq.trans (congrArg
    (fun f => f ≫ Spec.map (𝒜.toGradedAlgebra.strZero U) ≫ U.2.fromSpec)
    (chartProjIso_hom_toSpecZero 𝒜 L U e)) ?_)
  exact (Category.assoc _ _ _).trans (congrArg (fun f => AlgebraicGeometry.Proj.toSpecZero
    ((twist 𝒜 L).toGradedAlgebra.grading U) ≫ f) hzero)

/-! ### Independence of the trivialization -/

/-- **Two generator families differ by the powers of one unit.** If the degree-one generators of
two trivializations of `ℒ` over `W` differ by a scalar `u`, then their degree-`d` generators differ
by `u ^ d`, by induction through the multiplicativity of the families and the bilinearity of the
multiplication of the tensor powers. -/
theorem gen_eq_pow_smul (e e' : L.over W ≅ SheafOfModules.unit (S.ringCatSheaf.over W))
    (u : (structureRingPresheaf S.sheaf.obj).obj (op W))
    (hu : gen L e' 1 = u • gen L e 1) (d : ℕ) :
    gen L e' d = (u ^ d) • gen L e d := by
  induction d with
  | zero =>
      exact (one_smul _ (gen L e 0)).symm.trans
        (congrArg (fun r => r • gen L e 0) (pow_zero u).symm)
  | succ d ih =>
      refine Eq.trans (TwistGenerator.mulBilinear_gen L e' d 1).symm ?_
      refine Eq.trans (congrArg₂ (fun x y => (TensorPower.mulBilinear S.sheaf.obj
        S.ringCatSheaf.property L (d : ℤ) ((1 : ℕ) : ℤ)).app (op W) x y) ih hu) ?_
      refine Eq.trans ((TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L (d : ℤ)
        ((1 : ℕ) : ℤ)).map_smul_left (op W) (u ^ d) (gen L e d) (u • gen L e 1)) ?_
      refine Eq.trans (congrArg (fun z : (pow L ((d : ℤ) + ((1 : ℕ) : ℤ))).val.obj (op W) =>
        (u ^ d) • z) ((TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L (d : ℤ)
          ((1 : ℕ) : ℤ)).map_smul_right (op W) u (gen L e d) (gen L e 1))) ?_
      refine Eq.trans (congrArg (fun z : (pow L ((d : ℤ) + ((1 : ℕ) : ℤ))).val.obj (op W) =>
        (u ^ d) • (u • z)) (TwistGenerator.mulBilinear_gen L e d 1)) ?_
      exact (smul_smul (u ^ d) u (gen L e (d + 1))).trans
        (congrArg (fun r => r • gen L e (d + 1)) (pow_succ u d).symm)

/-- **Two trivializations give degreewise comparisons that differ by the powers of one unit of
`𝒪_S(W)`.** The two degree-one generators both generate `ℒ` over `W`, so they differ by a unit;
hence so do the degree-`d` generators, up to its `d`-th power, and the comparison is linear in the
generator. -/
theorem exists_unit_chartPiece_eq
    (e e' : L.over W ≅ SheafOfModules.unit (S.ringCatSheaf.over W)) :
    ∃ u : Γ(S, W)ˣ, ∀ (d : ℕ) (x : 𝒜.sectionPieces W d),
      chartPiece 𝒜 L e' d x = ((u : Γ(S, W)) ^ d) • chartPiece 𝒜 L e d x := by
  obtain ⟨u, hu⟩ := Stacks.GradedRing.exists_unit_smul_of_bijective_toSpanSingleton
    (TwistGenerator.bijective_toSpanSingleton_gen L e 1)
    (TwistGenerator.bijective_toSpanSingleton_gen L e' 1)
  refine ⟨⟨u.val, (u⁻¹).val, u.mul_inv, u.inv_mul⟩, fun d x => ?_⟩
  refine Eq.trans (congrArg (fun g => tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property
    (op W) (𝒜.piece (d : ℤ)) (pow L (d : ℤ)) x g)
    (gen_eq_pow_smul L e e' u.val hu d)) ?_
  exact GradedAlgebraTwist.tensorSectionsAt_smul_right S.sheaf.obj S.ringCatSheaf.property
    (op W) (𝒜.piece (d : ℤ)) (pow L (d : ℤ)) (u.val ^ d) x (gen L e d)

/-- **The two comparisons differ by rescaling the degree-`d` part by a degree-`0` unit.** On a
homogeneous element of degree `d` the comparison of one trivialization is the comparison of the
other multiplied by the `d`-th power of the degree-`0` section attached to the comparing unit.
Multiplication by a degree-`0` section is the module action, which is where
`Stacks.AlgebraicGeometry.TwistChart.exists_unit_chartPiece_eq` enters. -/
theorem chartRingHom_eq_mul (e e' : L.over W ≅ SheafOfModules.unit (S.ringCatSheaf.over W))
    (u : Γ(S, W)ˣ)
    (hu : ∀ (d : ℕ) (x : 𝒜.sectionPieces W d),
      chartPiece 𝒜 L e' d x = ((u : Γ(S, W)) ^ d) • chartPiece 𝒜 L e d x)
    (d : ℕ) (a : 𝒜.sectionRing W) (ha : a ∈ 𝒜.grading W d) :
    chartRingHom 𝒜 L e' a =
      ((twist 𝒜 L).strHom W (u : Γ(S, W))) ^ d * chartRingHom 𝒜 L e a := by
  obtain ⟨y, rfl⟩ := ha
  refine Eq.trans (chartRingHom_of 𝒜 L e' d y) ?_
  refine Eq.trans (congrArg (DirectSum.of ((twist 𝒜 L).sectionPieces W) d) (hu d y)) ?_
  refine Eq.trans ((twist 𝒜 L).strHom_mul_of W ((u : Γ(S, W)) ^ d)
    (chartPiece 𝒜 L e d y)).symm ?_
  exact congrArg₂ (fun p q => p * q) (map_pow ((twist 𝒜 L).strHom W) (u : Γ(S, W)) d)
    (chartRingHom_of 𝒜 L e d y).symm

/-- Mathlib's hypothesis for `AlgebraicGeometry.Proj.map` is free for the comparison: it has a
graded section. -/
theorem irrelevant_le_map_chartGradedHom :
    HomogeneousIdeal.irrelevant ((twist 𝒜 L).grading W) ≤
      (HomogeneousIdeal.irrelevant (𝒜.grading W)).map (chartGradedHom 𝒜 L e) :=
  ProjPolynomialSections.irrelevant_le_map_of_graded_section _ _ (chartGradedHom 𝒜 L e)
    (chartGradedInv 𝒜 L e) (chartGradedHom_inv 𝒜 L e)

/-- The forward morphism of the chart isomorphism is Mathlib's `AlgebraicGeometry.Proj.map`, which
is where the well-definedness criterion for a rescaled grading is stated. -/
theorem chartProjIso_hom_eq_map (U : S.AffineZariskiSite)
    (e : L.over U.toOpens ≅ SheafOfModules.unit (S.ringCatSheaf.over U.toOpens)) :
    (chartProjIso 𝒜 L U e).hom = AlgebraicGeometry.Proj.map (chartGradedHom 𝒜 L e)
      (irrelevant_le_map_chartGradedHom 𝒜 L e) :=
  RelativeProj.mapHomOfTop_eq_map _ _ (chartGradedHom 𝒜 L e)
    (irrelevant_le_map_chartGradedHom 𝒜 L e) (mapDomain_chartGradedHom_eq_top 𝒜 L e)

/-- **The chart isomorphism does not depend on the chosen trivialization of `ℒ`.** The two
comparisons differ by rescaling the degree-`d` part by the `d`-th power of an invertible
degree-`0` section, and such a pair of graded ring homomorphisms induces one and the same morphism
of projective spectra; an isomorphism is determined by its forward morphism.

This is what makes the chart isomorphism canonical, and it is the first of the two
compatibilities a glueing over a trivializing cover of the base consumes. -/
theorem chartProjIso_eq (U : S.AffineZariskiSite)
    (e e' : L.over U.toOpens ≅ SheafOfModules.unit (S.ringCatSheaf.over U.toOpens)) :
    chartProjIso 𝒜 L U e = chartProjIso 𝒜 L U e' := by
  obtain ⟨u, hu⟩ := exists_unit_chartPiece_eq 𝒜 L e e'
  refine Iso.ext (Eq.trans (chartProjIso_hom_eq_map 𝒜 L U e) ?_)
  refine Eq.trans ?_ (chartProjIso_hom_eq_map 𝒜 L U e').symm
  refine (Stacks.GradedRing.Proj_map_eq_of_target_degreeScale (𝒜.grading U.toOpens)
    ((twist 𝒜 L).strHom_mem U.toOpens (u : Γ(S, U.toOpens)))
    ((twist 𝒜 L).strHom_mem U.toOpens ((u⁻¹ : Γ(S, U.toOpens)ˣ) : Γ(S, U.toOpens)))
    ?_ (chartGradedHom 𝒜 L e) (chartGradedHom 𝒜 L e')
    (irrelevant_le_map_chartGradedHom 𝒜 L e) (irrelevant_le_map_chartGradedHom 𝒜 L e')
    fun i a ha => chartRingHom_eq_mul 𝒜 L e e' u hu i a ha).symm
  exact (map_mul ((twist 𝒜 L).strHom U.toOpens) _ _).symm.trans
    ((congrArg ((twist 𝒜 L).strHom U.toOpens) u.mul_inv).trans
      (map_one ((twist 𝒜 L).strHom U.toOpens)))

/-! ### Naturality in the open -/

/-- **The ring-level square commutes on the nose for the restricted trivialization.** Restricting
`x ⊗ gen d` along `W' ≤ W` is `res x ⊗ gen' d`, where `gen'` is the generator family of the
restricted trivialization: this is the compatibility of the tensor product of sections with
restriction together with
`Stacks.AlgebraicGeometry.TwistGenerator.res_gen`. -/
theorem res_comp_chartGradedHom {W' : S.Opens} (h : W' ≤ W) :
    ((twist 𝒜 L).res h).comp (chartGradedHom 𝒜 L e) =
      (chartGradedHom 𝒜 L (isoUnitOverOfHom L (homOfLE h) e)).comp (𝒜.res h) := by
  refine GradedRingHom.ext fun x => ?_
  show (twist 𝒜 L).resRingHom h (chartRingHom 𝒜 L e x) =
    chartRingHom 𝒜 L (isoUnitOverOfHom L (homOfLE h) e) (𝒜.resRingHom h x)
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | of n y =>
      rw [chartRingHom_of, SheafGradedAlgebra.resRingHom_of, SheafGradedAlgebra.resRingHom_of,
        chartRingHom_of]
      refine congrArg (DirectSum.of ((twist 𝒜 L).sectionPieces W') n) ?_
      refine Eq.trans (GradedAlgebraTwist.tensorSectionsAt_naturality S.sheaf.obj
        S.ringCatSheaf.property (𝒜.piece (n : ℤ)) (pow L (n : ℤ)) (homOfLE h).op y
        (gen L e n)) ?_
      exact congrArg (fun g => tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op W')
        (𝒜.piece (n : ℤ)) (pow L (n : ℤ)) ((𝒜.piece (n : ℤ)).val.map (homOfLE h).op y) g)
        (TwistGenerator.res_gen L e h n)
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-- **The chart isomorphisms are natural in the affine open.** For an inclusion `U' ⊆ U` of affine
opens of the base, both trivialized, the chart isomorphism over `U'` followed by the transition
morphism of the charts of `𝒜` is the transition morphism of the charts of the twist followed by
the chart isomorphism over `U`.

By `Stacks.AlgebraicGeometry.TwistChart.chartProjIso_eq` the trivialization over `U'` may be taken
to be the restriction of the one over `U`, for which the square of graded ring homomorphisms
commutes on the nose; functoriality of the induced morphism of projective spectra turns that into
the square of morphisms.

This is the second of the two compatibilities a glueing over a trivializing cover of the base
consumes. -/
theorem chartProjIso_naturality (U U' : S.AffineZariskiSite) (φ : U' ⟶ U)
    (e : L.over U.toOpens ≅ SheafOfModules.unit (S.ringCatSheaf.over U.toOpens))
    (e' : L.over U'.toOpens ≅ SheafOfModules.unit (S.ringCatSheaf.over U'.toOpens)) :
    (chartProjIso 𝒜 L U' e').hom ≫
        (RelativeProjGlue.chartFunctor 𝒜.toGradedAlgebra).map φ =
      (RelativeProjGlue.chartFunctor (twist 𝒜 L).toGradedAlgebra).map φ ≫
        (chartProjIso 𝒜 L U e).hom := by
  have h : U'.toOpens ≤ U.toOpens := Scheme.AffineZariskiSite.toOpens_mono φ.le
  have hres𝒜 := RelativeProjGlue.irrelevant_le_map_res_of_le 𝒜.toGradedAlgebra φ.le h
  have hresB := RelativeProjGlue.irrelevant_le_map_res_of_le (twist 𝒜 L).toGradedAlgebra φ.le h
  have hd1 : ProjShared.mapDomain (𝒜.grading U.toOpens) ((twist 𝒜 L).grading U'.toOpens)
      ((chartGradedHom 𝒜 L (isoUnitOverOfHom L (homOfLE h) e)).comp (𝒜.res h)) = ⊤ :=
    ProjShared.mapDomain_eq_top_of_irrelevant_le_map _ _ _
      (HomogeneousIdeal.irrelevant_le_map_comp hres𝒜
        (irrelevant_le_map_chartGradedHom 𝒜 L (isoUnitOverOfHom L (homOfLE h) e)))
  have hd2 : ProjShared.mapDomain (𝒜.grading U.toOpens) ((twist 𝒜 L).grading U'.toOpens)
      (((twist 𝒜 L).res h).comp (chartGradedHom 𝒜 L e)) = ⊤ :=
    ProjShared.mapDomain_eq_top_of_irrelevant_le_map _ _ _
      (HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map_chartGradedHom 𝒜 L e) hresB)
  rw [chartProjIso_eq 𝒜 L U' e' (isoUnitOverOfHom L (homOfLE h) e)]
  refine Eq.trans (ProjBundleSurjection.mapHomOfTop_comp (𝒜.grading U.toOpens)
    (𝒜.grading U'.toOpens) ((twist 𝒜 L).grading U'.toOpens) (𝒜.res h)
    (chartGradedHom 𝒜 L (isoUnitOverOfHom L (homOfLE h) e)) hres𝒜
    (irrelevant_le_map_chartGradedHom 𝒜 L (isoUnitOverOfHom L (homOfLE h) e))
    (RelativeProjGlue.mapDomain_res_eq_top_of_le 𝒜.toGradedAlgebra φ.le h)
    (mapDomain_chartGradedHom_eq_top 𝒜 L (isoUnitOverOfHom L (homOfLE h) e)) hd1).symm ?_
  refine Eq.trans (ProjPolynomialSections.mapHomOfTop_congr _ _
    (res_comp_chartGradedHom 𝒜 L e h).symm hd1 hd2) ?_
  exact ProjBundleSurjection.mapHomOfTop_comp (𝒜.grading U.toOpens)
    ((twist 𝒜 L).grading U.toOpens) ((twist 𝒜 L).grading U'.toOpens) (chartGradedHom 𝒜 L e)
    ((twist 𝒜 L).res h) (irrelevant_le_map_chartGradedHom 𝒜 L e) hresB
    (mapDomain_chartGradedHom_eq_top 𝒜 L e)
    (RelativeProjGlue.mapDomain_res_eq_top_of_le (twist 𝒜 L).toGradedAlgebra φ.le h) hd2

end Stacks.AlgebraicGeometry.TwistChart

end
