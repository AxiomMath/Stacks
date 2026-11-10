module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Topological
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Filtration
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine

/-!
# Affineness and integrality across a morphism of thickenings

For a morphism of thickenings — a commutative square

```
X --φ.left--→ S
|             |
i             j
↓             ↓
X' -φ.right-→ S'
```

whose horizontal arrows `i` and `j` are thickenings — the morphism `φ.left` of closed subschemes
is affine exactly when the morphism `φ.right` of ambient schemes is affine, and likewise for
integrality. These are parts (1) and (5) of [Stacks Project, Tag 09ZV].

Both rest on the fact that a thickening matches the affine opens of the closed subscheme with the
affine opens of the ambient scheme: an open of the ambient scheme is affine if and only if its
inverse image is, which is [Stacks Project, Tag 06AD] read over an arbitrary open. Integrality is
then affineness together with universal closedness, the latter already available for a morphism of
thickenings.

## Main results

* `Stacks.Thickenings.isAffineOpen_iff_isAffineOpen_preimage`: an open of the ambient scheme of a
  thickening is affine exactly when its inverse image in the closed subscheme is.
* `Stacks.Thickenings.isAffineHom_left_iff_right`: **part (1) of [Stacks Project, Tag 09ZV]**.
* `Stacks.Thickenings.isIntegralHom_left_iff_right`: **part (5) of [Stacks Project, Tag 09ZV]**.
* `Stacks.Thickenings.isQuasiAffineHom_left_of_right`: one implication of part (9) of
  [Stacks Project, Tag 09ZV]; see below.
* `Stacks.Thickenings.isQuasiAffine_of_isQuasiAffine_ambient`: the implication *ambient
  quasi-affine `⟹` closed subscheme quasi-affine* of [Stacks Project, Tag 0B7L], the input
  part (9) is assembled from.
* `Stacks.Thickenings.QuasiAffineAscendsAlongThickening` and
  `Stacks.Thickenings.isQuasiAffineHom_left_iff_right_of_ascends`: the converse implication of
  [Stacks Project, Tag 0B7L], isolated, and part (9) derived from it alone.
* `Stacks.Thickenings.AffineBasicOpenLifts` and
  `Stacks.Thickenings.isQuasiAffine_of_affineBasicOpenLifts`: that converse implication reduced
  further, to one elementary statement about global functions, with no Noetherian hypothesis; and
  `Stacks.Thickenings.AffineBasicOpenLiftsAlongThickening`,
  `Stacks.Thickenings.quasiAffineAscendsAlongThickening_of_affineBasicOpenLifts` and
  `Stacks.Thickenings.isQuasiAffineHom_left_iff_right_of_affineBasicOpenLifts`: part (9) from that
  statement alone.
* `Stacks.Thickenings.AffineBasicOpenLifts.comp` and
  `Stacks.Thickenings.affineBasicOpenLifts_of_isFirstOrderThickening`: that statement composes
  along a thickening, so for a finite-order thickening it reduces to the first-order case along
  the filtration by the powers of the ideal sheaf. The first-order case itself is proved in
  `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/QuasiAffineAscent.lean`, so the
  statement holds for every finite-order thickening and part (9) holds over a locally Noetherian
  ambient scheme. The general case is
  `Stacks.Thickenings.quasiAffineAscendsAlongThickening` of
  `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/QuasiAffineLimit.lean`, which
  discharges the `Prop` below by the limit argument of [Stacks Project, Tag 09MW] and so closes
  part (9) unconditionally.

## Implementation notes

The square is a `CategoryTheory.Arrow.Hom`, so its commutativity is the field `w` and no separate
hypothesis is needed; the identity it gives between inverse images along the two paths of the
square is the only way it enters.

Affine opens of the two schemes of a thickening are matched by
`Stacks.Thickenings.IsThickening.opensCongr`, whose inverse is taking inverse images; so the
quantification over affine opens of `S` in `AlgebraicGeometry.IsAffineHom` is turned into one
over affine opens of `S'` by passing to the matching open, and conversely by taking inverse
images.

## Part (9), quasi-affineness

Part (9) is the one part of [Stacks Project, Tag 09ZV] that is **not** claimed here, and the two
implications are in very different states.

The implication `φ.right` quasi-affine `⟹` `φ.left` quasi-affine is proved, as
`Stacks.Thickenings.isQuasiAffineHom_left_of_right`, and carries no tag attribute. It is the
elementary one: the inverse image of an affine open of `S'` is quasi-affine, and the inverse image
of the matching affine open of `S` is a closed subscheme of it, so
`AlgebraicGeometry.Scheme.IsQuasiAffine.of_isAffineHom` applies.

The source assembles part (9) out of the affine-open correspondence and
[Stacks Project, Tag 0B7L] — for a closed immersion that is a homeomorphism on points, the ambient
scheme is quasi-affine if and only if the closed subscheme is. That assembly is carried out here,
in both directions, with Tag 0B7L split into its two implications:

* *ambient `⟹` closed subscheme* is `Stacks.Thickenings.isQuasiAffine_of_isQuasiAffine_ambient`,
  proved unconditionally and carrying the corresponding clause of Tag 0B7L. It is what
  `Stacks.Thickenings.isQuasiAffineHom_left_of_right` is the relative form of.
* *closed subscheme `⟹` ambient* is isolated here as the `Prop`
  `Stacks.Thickenings.QuasiAffineAscendsAlongThickening`, and
  `Stacks.Thickenings.isQuasiAffineHom_left_iff_right_of_ascends` derives the whole of part (9)
  from that one statement and nothing else. It is proved — by the limit argument of
  [Stacks Project, Tag 09MW] — in
  `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/QuasiAffineLimit.lean`, which
  is
  where part (9) and the whole of Tag 0B7L are therefore registered. No declaration in *this* file
  claims part (9), because every statement here either carries that `Prop` as a hypothesis or is
  only one implication of it.

What blocks the missing implication, and how far it is reduced here. The source's route is
[Stacks Project, Tag 01QE] — a scheme is quasi-affine exactly when its structure sheaf is ample,
`Stacks.Ample.isQuasiAffine_iff_isAmple` — read through the converse half of
[Stacks Project, Tag 09MS]: it is ampleness of `𝒪_{X'}` that has to ascend. In this repository
that half is available only for a locally Noetherian ambient scheme and granted the cohomological
lift `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower`, as
`Stacks.AmpleSurjectiveThickening.isQuasiAffine_of_sectionsLiftAfterPower`, and
[Stacks Project, Tag 09MW] is the limit argument the source uses to remove the Noetherian
hypothesis there.

Neither hypothesis is needed to state the residue, and that is what is done here. At `L = 𝒪` a
global section of a tensor power is a global function and its nonvanishing locus a basic open, and
the affine opens of the two schemes of a thickening already correspond
(`Stacks.Thickenings.isAffineOpen_iff_isAffineOpen_preimage`), so the transport of ampleness that
Tag 09MS performs is free. What is left is
`Stacks.Thickenings.AffineBasicOpenLiftsAlongThickening`: for a thickening `k : Y ⟶ Y'` with `Y`
quasi-affine, every affine basic open `Y_r` of a global function is the inverse image of a basic
open of a global function on `Y'`. The ascent is derived from exactly that, for arbitrary schemes,
by `Stacks.Thickenings.quasiAffineAscendsAlongThickening_of_affineBasicOpenLifts`, so the
Noetherian hypothesis and the limit argument of Tag 09MW play no part in the reduction.

Of that residue, the *filtration* step of the source's argument is also carried out here. The
residue composes along a thickening — `Stacks.Thickenings.AffineBasicOpenLifts.comp`, which costs
nothing because what is lifted is an open and not a power of a function — so along the filtration
by the powers of the ideal sheaf it reduces, for a finite-order thickening, to the case of a
first-order one: `Stacks.Thickenings.affineBasicOpenLifts_of_isFirstOrderThickening`.

The square-zero case that remained is **proved**, in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/QuasiAffineAscent.lean`, as
`Stacks.Thickenings.affineBasicOpenLifts_of_isFirstOrderThickening_of_isQuasiAffine`, and without
cohomology: the obstruction to lifting `r` is a class in `H¹` of the ideal sheaf, but the Čech
cocycle representing it is handled directly by the two localization statements over an affine open
— `AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen` and
`AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact` — so neither
[Stacks Project, Tag 01XR] in degree one nor [Stacks Project, Tag 09MR] is needed. Together with
the filtration that gives the residue for every **finite-order** thickening, hence part (9) over a
locally Noetherian ambient scheme
(`Stacks.Thickenings.isQuasiAffineHom_left_iff_right_of_isLocallyNoetherian`), where a thickening
is automatically of finite order.

What is left for part (9) as the source states it is therefore a thickening of which no power of
the ideal sheaf vanishes, which exists only over an ambient scheme that is not locally Noetherian.
The filtration does not reach it — if `𝒥 ⊆ ℐ` and `ℐ / 𝒥` are nilpotent then so is `ℐ` — and the
source's route there is the limit argument of [Stacks Project, Tag 09MW].

## References

* [Stacks Project, Tag 09ZV](https://stacks.math.columbia.edu/tag/09ZV)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 01WM](https://stacks.math.columbia.edu/tag/01WM)
* [Stacks Project, Tag 0B7L](https://stacks.math.columbia.edu/tag/0B7L)
* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 09MW](https://stacks.math.columbia.edu/tag/09MW)
* [Stacks Project, Tag 01XR](https://stacks.math.columbia.edu/tag/01XR)
* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Stacks.Thickenings

universe u

/-- **An open of the ambient scheme of a thickening is affine exactly when its inverse image
is.** The inverse image of an affine open along a closed immersion is affine, and conversely a
thickening restricts to a thickening over any open, so [Stacks Project, Tag 06AD] — a thickening
of an affine scheme is affine, `Stacks.Thickenings.isAffine_of_isThickening` — applies to that
restriction.

No tag attribute: [Stacks Project, Tag 06AD] is the statement for the whole scheme, and it is
registered on `Stacks.Thickenings.isAffine_of_isThickening`. -/
theorem isAffineOpen_iff_isAffineOpen_preimage {X X' : Scheme.{u}} {i : X ⟶ X'}
    (hi : IsThickening i) (U : X'.Opens) :
    IsAffineOpen U ↔ IsAffineOpen (i ⁻¹ᵁ U) := by
  have : IsClosedImmersion i := hi.1
  refine ⟨fun hU ↦ hU.preimage i, fun hU ↦ ?_⟩
  have : IsAffine (i ⁻¹ᵁ U).toScheme := hU
  exact isAffine_of_isThickening (hi.morphismRestrict U)

/-- An open of the ambient scheme of a thickening is affine if its inverse image equals an affine
open. -/
private theorem isAffineOpen_of_preimage_eq {X X' : Scheme.{u}} {i : X ⟶ X'} (hi : IsThickening i)
    {U : X'.Opens} {V : X.Opens} (h : i ⁻¹ᵁ U = V) (hV : IsAffineOpen V) : IsAffineOpen U :=
  (isAffineOpen_iff_isAffineOpen_preimage hi U).mpr (h ▸ hV)

/-- The inverse image of an open of `S'` along the two paths of a morphism of thickenings agree:
`φ.left ⁻¹ᵁ (j ⁻¹ᵁ U') = i ⁻¹ᵁ (φ.right ⁻¹ᵁ U')`. This is the commutativity of the square. -/
theorem preimage_left_preimage_eq_preimage_preimage_right {X X' S S' : Scheme.{u}}
    {i : X ⟶ X'} {j : S ⟶ S'} (φ : Arrow.mk i ⟶ Arrow.mk j) (U' : S'.Opens) :
    φ.left ⁻¹ᵁ (j ⁻¹ᵁ U') = i ⁻¹ᵁ (φ.right ⁻¹ᵁ U') := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
  exact congrArg (fun k : X ⟶ S' ↦ k ⁻¹ᵁ U') (Arrow.w φ)

/-- The inverse image of an open `U` of `S` under `φ.left` is the inverse image along `i` of the
inverse image under `φ.right` of the matching open of `S'`. -/
private theorem preimage_left_eq_preimage_preimage_right_opensCongr {X X' S S' : Scheme.{u}}
    {i : X ⟶ X'} {j : S ⟶ S'} (hj : IsThickening j) (φ : Arrow.mk i ⟶ Arrow.mk j) (U : S.Opens) :
    φ.left ⁻¹ᵁ U = i ⁻¹ᵁ (φ.right ⁻¹ᵁ hj.opensCongr U) := by
  rw [← preimage_left_preimage_eq_preimage_preimage_right φ, hj.preimage_opensCongr]

/-- **Part (1) of [Stacks Project, Tag 09ZV].** For a morphism of thickenings, the morphism of
closed subschemes is affine if and only if the morphism of ambient schemes is affine.

Affineness of a morphism quantifies over the affine opens of its target, and
`Stacks.Thickenings.isAffineOpen_iff_isAffineOpen_preimage` matches the affine opens of `S` with
those of `S'`; the inverse images of matching opens along `φ.left` and `φ.right` are then matched
by the same criterion for the thickening `i`. -/
@[stacks 09ZV "affine"]
theorem isAffineHom_left_iff_right {X X' S S' : Scheme.{u}} {i : X ⟶ X'} {j : S ⟶ S'}
    (hi : IsThickening i) (hj : IsThickening j) (φ : Arrow.mk i ⟶ Arrow.mk j) :
    IsAffineHom φ.left ↔ IsAffineHom φ.right := by
  refine ⟨fun h ↦ ⟨fun U' hU' ↦ ?_⟩, fun h ↦ ⟨fun U hU ↦ ?_⟩⟩
  · have h₁ : IsAffineOpen (φ.left ⁻¹ᵁ (j ⁻¹ᵁ U')) :=
      IsAffineHom.isAffine_preimage _ ((isAffineOpen_iff_isAffineOpen_preimage hj U').mp hU')
    rw [preimage_left_preimage_eq_preimage_preimage_right φ U'] at h₁
    exact (isAffineOpen_iff_isAffineOpen_preimage hi (φ.right ⁻¹ᵁ U')).mpr h₁
  · have hU' : IsAffineOpen (hj.opensCongr U) :=
      isAffineOpen_of_preimage_eq hj (hj.preimage_opensCongr U) hU
    have h₁ : IsAffineOpen (i ⁻¹ᵁ (φ.right ⁻¹ᵁ hj.opensCongr U)) :=
      (isAffineOpen_iff_isAffineOpen_preimage hi _).mp (IsAffineHom.isAffine_preimage _ hU')
    rwa [← preimage_left_eq_preimage_preimage_right_opensCongr hj φ U] at h₁

/-- **Part (5) of [Stacks Project, Tag 09ZV].** For a morphism of thickenings, the morphism of
closed subschemes is integral if and only if the morphism of ambient schemes is integral.

A morphism is integral exactly when it is universally closed and affine — [Stacks Project, Tag
01WM], which is `AlgebraicGeometry.IsIntegralHom.iff_universallyClosed_and_isAffineHom` — so this
is part (4) of the tag together with part (1). -/
@[stacks 09ZV "integral"]
theorem isIntegralHom_left_iff_right {X X' S S' : Scheme.{u}} {i : X ⟶ X'} {j : S ⟶ S'}
    (hi : IsThickening i) (hj : IsThickening j) (φ : Arrow.mk i ⟶ Arrow.mk j) :
    IsIntegralHom φ.left ↔ IsIntegralHom φ.right := by
  simpa only [IsIntegralHom.iff_universallyClosed_and_isAffineHom] using
    and_congr (universallyClosed_left_iff_right φ hi hj) (isAffineHom_left_iff_right hi hj φ)

/-- **The elementary implication of part (9) of [Stacks Project, Tag 09ZV].** If the morphism of
ambient schemes of a morphism of thickenings is quasi-affine, then so is the morphism of closed
subschemes.

The inverse image under `φ.left` of an affine open `U` of `S` is the inverse image along the
thickening `i` of the inverse image under `φ.right` of the affine open of `S'` matching `U`, hence
a closed subscheme of a quasi-affine scheme, and a closed immersion is affine.

The reverse implication is [Stacks Project, Tag 0B7L] in the direction that holds here for a
finite-order thickening and is open in general; see the module documentation,
`Stacks.Thickenings.QuasiAffineAscendsAlongThickening` and
`Stacks.Thickenings.isQuasiAffineHom_right_of_left_of_isLocallyNoetherian`. No tag attribute is
attached here, because this is one implication of part (9) and not the part. -/
theorem isQuasiAffineHom_left_of_right {X X' S S' : Scheme.{u}} {i : X ⟶ X'} {j : S ⟶ S'}
    (hi : IsThickening i) (hj : IsThickening j) (φ : Arrow.mk i ⟶ Arrow.mk j)
    (h : IsQuasiAffineHom φ.right) : IsQuasiAffineHom φ.left := by
  have : IsClosedImmersion i := hi.1
  refine ⟨fun U hU ↦ ?_⟩
  have : Scheme.IsQuasiAffine (φ.right ⁻¹ᵁ hj.opensCongr U).toScheme :=
    h.isQuasiAffine_preimage _ (isAffineOpen_of_preimage_eq hj (hj.preimage_opensCongr U) hU)
  rw [preimage_left_eq_preimage_preimage_right_opensCongr hj φ U]
  exact Scheme.IsQuasiAffine.of_isAffineHom (i ∣_ φ.right ⁻¹ᵁ hj.opensCongr U)

/-- **The implication *ambient quasi-affine `⟹` closed subscheme quasi-affine* of
[Stacks Project, Tag 0B7L].** If the ambient scheme of a thickening `i : X ⟶ X'` is quasi-affine,
then so is the closed subscheme.

This is the implication the source calls elementary, and it is: a closed immersion is an affine
morphism, and `AlgebraicGeometry.Scheme.IsQuasiAffine.of_isAffineHom` says the source of an affine
morphism into a quasi-affine scheme is quasi-affine. Surjectivity of `i` is not used; it is
carried because it is half of the source's hypothesis, so that this is literally one implication
of the source statement.

The source's hypothesis that `i` is a closed immersion inducing a homeomorphism of underlying
spaces is `Stacks.Thickenings.IsThickening`: for a closed immersion, being a homeomorphism on
points is being surjective, which is
`Stacks.Thickenings.IsThickening.isHomeomorph`.

The reverse implication is the one part (9) of [Stacks Project, Tag 09ZV] needs. It is isolated as
`Stacks.Thickenings.QuasiAffineAscendsAlongThickening`, and it is proved for every **finite-order**
thickening in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/QuasiAffineAscent.lean`
(`Stacks.Thickenings.isQuasiAffine_of_isFiniteOrderThickening`), hence for every thickening of a
locally Noetherian scheme, and for an arbitrary thickening in
`Stacks.Thickenings.isQuasiAffine_of_isThickening` of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/QuasiAffineLimit.lean`. -/
@[stacks 0B7L "the implication: ambient quasi-affine ⟹ closed subscheme quasi-affine"]
theorem isQuasiAffine_of_isQuasiAffine_ambient {X X' : Scheme.{u}} {i : X ⟶ X'}
    (hi : IsThickening i) (hX' : Scheme.IsQuasiAffine X') : Scheme.IsQuasiAffine X :=
  have : IsClosedImmersion i := hi.1
  have := hX'
  Scheme.IsQuasiAffine.of_isAffineHom i

/-- **The implication part (9) of [Stacks Project, Tag 09ZV] is assembled from**: the implication
*closed subscheme quasi-affine `⟹` ambient quasi-affine* of [Stacks Project, Tag 0B7L], for an
arbitrary thickening.

It is isolated as a `Prop` so that the reduction of part (9) to it is a theorem rather than a
remark: `Stacks.Thickenings.isQuasiAffineHom_left_iff_right_of_ascends` derives part (9) from
this and nothing else, so discharging it closes part (9). It **is** discharged, by
`Stacks.Thickenings.quasiAffineAscendsAlongThickening` of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/QuasiAffineLimit.lean`, where
part (9) is registered. The opposite implication needs no hypothesis and is
`Stacks.Thickenings.isQuasiAffine_of_isQuasiAffine_ambient`.

It holds for every **finite-order** thickening, by
`Stacks.Thickenings.isQuasiAffine_of_isFiniteOrderThickening` of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/QuasiAffineAscent.lean`, hence
for every thickening whose ambient scheme is locally Noetherian; what it still quantifies over, and
all it still quantifies over, is a thickening no power of whose ideal sheaf vanishes.

It is itself reduced further, to a statement about global functions carrying no hypothesis the
source does not make:
`Stacks.Thickenings.quasiAffineAscendsAlongThickening_of_affineBasicOpenLifts` derives it from
`Stacks.Thickenings.AffineBasicOpenLiftsAlongThickening` alone. The source's own route is through
ampleness of `𝒪_{X'}` by [Stacks Project, Tag 01QE], which is the converse half of
[Stacks Project, Tag 09MS], available in this repository only for a locally Noetherian ambient
scheme and granted `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower` — see
`Stacks.AmpleSurjectiveThickening.isQuasiAffine_of_sectionsLiftAfterPower`. -/
def QuasiAffineAscendsAlongThickening : Prop :=
  ∀ (Y Y' : Scheme.{u}) (k : Y ⟶ Y'), IsThickening k → Scheme.IsQuasiAffine Y →
    Scheme.IsQuasiAffine Y'

/-! ### The ascent reduced to the lifting of one global function -/

/-- Every point of a quasi-affine scheme lies in the nonvanishing locus of a global function whose
nonvanishing locus is affine. This is `AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen`
read at the point, and it is the exact converse of
`AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen`. -/
theorem exists_isAffineOpen_basicOpen_mem (Y : Scheme.{u}) [Scheme.IsQuasiAffine Y] (y : Y) :
    ∃ r : Γ(Y, ⊤), IsAffineOpen (Y.basicOpen r) ∧ y ∈ Y.basicOpen r := by
  obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hyr, -⟩ :=
    (Scheme.IsQuasiAffine.isBasis_basicOpen Y).exists_subset_of_mem_open (Set.mem_univ y)
      isOpen_univ
  exact ⟨r, hr, hyr⟩

/-- **The property of a morphism that the ascent of quasi-affineness needs**: every affine
nonvanishing locus of a global function on the source is the inverse image of the nonvanishing
locus of a global function on the target.

This is the untwisted form, at `L = 𝒪`, of what
`Stacks.AmpleClosedImmersion.SectionsLiftAfterPower` asks of a closed immersion: there a global
section of a positive tensor power of `L` with affine nonvanishing locus is required to have that
locus pulled back from one upstairs, and for `L = 𝒪` a global section of a tensor power is a
global function and its nonvanishing locus a basic open. As there, only the *locus* is asked for,
not a lift of the function. -/
def AffineBasicOpenLifts {Y Y' : Scheme.{u}} (k : Y ⟶ Y') : Prop :=
  ∀ r : Γ(Y, ⊤), IsAffineOpen (Y.basicOpen r) →
    ∃ r' : Γ(Y', ⊤), k ⁻¹ᵁ Y'.basicOpen r' = Y.basicOpen r

/-- A morphism surjective on global functions lifts every basic open: take a preimage of the
function. In particular an isomorphism does. -/
theorem AffineBasicOpenLifts.of_surjective_appTop {Y Y' : Scheme.{u}} {k : Y ⟶ Y'}
    (hk : Function.Surjective k.appTop) : AffineBasicOpenLifts k := by
  intro r _
  obtain ⟨r', hr'⟩ := hk r
  exact ⟨r', by rw [Scheme.preimage_basicOpen_top, hr']⟩

/-- An isomorphism lifts every basic open: it is surjective on global functions. -/
theorem AffineBasicOpenLifts.of_isIso {Y Y' : Scheme.{u}} (k : Y ⟶ Y') [IsIso k] :
    AffineBasicOpenLifts k :=
  have : IsIso k.appTop := inferInstanceAs (IsIso (k.app ⊤))
  .of_surjective_appTop (ConcreteCategory.bijective_of_isIso k.appTop).2

/-- **The property composes along a thickening.** The basic open produced on the middle scheme has
affine inverse image, hence is itself affine by
`Stacks.Thickenings.isAffineOpen_iff_isAffineOpen_preimage`, so the second morphism can be fed
with it; inverse images along the composite are inverse images along the two factors in turn.

Unlike the lifting of a power of the function, where the exponents would multiply, this composes
with nothing to track: it is the statement that one *open* is pulled back from another. It is what
reduces the property for a finite-order thickening to the first-order case along the filtration of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/Filtration.lean`. -/
theorem AffineBasicOpenLifts.comp {Y W Y' : Scheme.{u}} {a : Y ⟶ W} {b : W ⟶ Y'}
    (ha : IsThickening a) (h₁ : AffineBasicOpenLifts a) (h₂ : AffineBasicOpenLifts b) :
    AffineBasicOpenLifts (a ≫ b) := by
  intro r hr
  obtain ⟨w, hw⟩ := h₁ r hr
  obtain ⟨r', hr'⟩ := h₂ w (isAffineOpen_of_preimage_eq ha hw hr)
  exact ⟨r', by rw [Scheme.Hom.comp_preimage, hr', hw]⟩

/-- **Quasi-affineness ascends along a thickening that lifts affine basic opens.** For a thickening
`k : Y ⟶ Y'` with `Y` quasi-affine, `Stacks.Thickenings.AffineBasicOpenLifts k` gives that `Y'` is
quasi-affine.

The argument is the source's route with ampleness untwisted. A quasi-affine scheme is covered by
the affine nonvanishing loci of its global functions
(`Stacks.Thickenings.exists_isAffineOpen_basicOpen_mem`), and a quasi-compact scheme covered by
such loci is quasi-affine
(`AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen`), so it suffices to
produce, for each point of `Y'`, a global function on `Y'` whose nonvanishing locus is affine and
contains that point. The hypothesis produces one over an affine nonvanishing locus of `Y` around a
preimage of the point — the thickening is a homeomorphism, so the point lies in the locus — and
`Stacks.Thickenings.isAffineOpen_iff_isAffineOpen_preimage`, which is [Stacks Project, Tag 06AD]
read over an open, carries affineness of the inverse image back up to `Y'`.

This is where the Noetherian hypothesis of
`Stacks.AmpleSurjectiveThickening.isQuasiAffine_of_sectionsLiftAfterPower` disappears. That route
goes through ampleness of an invertible module and needs the converse half of
[Stacks Project, Tag 09MS], which is Noetherian; at `L = 𝒪` the affine-open correspondence of a
thickening replaces it outright, so the limit argument of [Stacks Project, Tag 09MW] plays no part
in the reduction. -/
theorem isQuasiAffine_of_affineBasicOpenLifts {Y Y' : Scheme.{u}} {k : Y ⟶ Y'}
    (hk : IsThickening k) [Scheme.IsQuasiAffine Y] (hlift : AffineBasicOpenLifts k) :
    Scheme.IsQuasiAffine Y' := by
  have : CompactSpace Y' := hk.homeomorph.compactSpace
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen Y' fun y' ↦ ?_
  obtain ⟨y, hy⟩ := hk.2 y'
  obtain ⟨r, hr, hyr⟩ := exists_isAffineOpen_basicOpen_mem Y y
  obtain ⟨r', hpre⟩ := hlift r hr
  refine ⟨r', isAffineOpen_of_preimage_eq hk hpre hr, ?_⟩
  have hmem : y ∈ k ⁻¹ᵁ Y'.basicOpen r' := by rwa [hpre]
  exact hy ▸ hmem

/-- **For a finite-order thickening the property reduces to the first-order case.** Granted
`Stacks.Thickenings.AffineBasicOpenLifts` for every first-order thickening with quasi-affine
closed subscheme, it holds for every finite-order thickening with quasi-affine closed subscheme.

The filtration of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/Filtration.lean` writes `t` as
the canonical isomorphism onto level zero, followed by the first-order steps
`Stacks.Thickenings.PowerFiltration.baseStep`, followed by the inclusion of the last level, which
is an isomorphism because the relevant power of the ideal sheaf vanishes. Each level is
quasi-affine by `Stacks.Thickenings.isQuasiAffine_of_affineBasicOpenLifts` applied to the
composite reaching it — which is what lets the first-order hypothesis be applied at the next step
— and `Stacks.Thickenings.AffineBasicOpenLifts.comp` assembles the composite. The induction
carries the composite, its being a thickening, the property for it, and its factorisation of `t`.

This discharges the *filtration* step of the source's proof of [Stacks Project, Tag 09MS], which
reduces that proof to the square-zero case. That case is proved, as
`Stacks.Thickenings.affineBasicOpenLifts_of_isFirstOrderThickening_of_isQuasiAffine` in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/QuasiAffineAscent.lean`, so this
theorem's hypothesis is discharged there and the property holds for every finite-order thickening
(`Stacks.Thickenings.affineBasicOpenLifts_of_isFiniteOrderThickening`). What is left of part (9)
is a thickening with no vanishing power of its ideal sheaf, for which the source uses the limit
argument of [Stacks Project, Tag 09MW]. -/
theorem affineBasicOpenLifts_of_isFirstOrderThickening
    (hfirst : ∀ (Z Z' : Scheme.{u}) (m : Z ⟶ Z'), IsFirstOrderThickening m →
      Scheme.IsQuasiAffine Z → AffineBasicOpenLifts m)
    {Y Y' : Scheme.{u}} {t : Y ⟶ Y'} (ht : IsFiniteOrderThickening t)
    [Scheme.IsQuasiAffine Y] :
    AffineBasicOpenLifts t := by
  obtain ⟨hclosed, n, hn⟩ := ht
  have key : ∀ i : ℕ, ∃ c : Y ⟶ PowerFiltration.baseLevel t i,
      IsThickening c ∧ AffineBasicOpenLifts c ∧
        c ≫ PowerFiltration.baseInclusion t i = t := by
    intro i
    induction i with
    | zero =>
      have := PowerFiltration.baseInitialMap_isIso t hclosed
      exact ⟨PowerFiltration.baseInitialMap t, isThickening_of_isIso _,
        AffineBasicOpenLifts.of_isIso _, PowerFiltration.baseInitialMap_comp_inclusion t⟩
    | succ i ih =>
      obtain ⟨c, hc, hclift, hccomp⟩ := ih
      have : Scheme.IsQuasiAffine (PowerFiltration.baseLevel t i) :=
        isQuasiAffine_of_affineBasicOpenLifts hc hclift
      have hstep : IsFirstOrderThickening (PowerFiltration.baseStep t i) :=
        PowerFiltration.baseStep_firstOrder t i
      refine ⟨c ≫ PowerFiltration.baseStep t i, isThickening_comp hc hstep.isThickening,
        hclift.comp hc (hfirst _ _ _ hstep inferInstance), ?_⟩
      rw [Category.assoc, PowerFiltration.baseStep_comp_inclusion, hccomp]
  obtain ⟨c, hc, hclift, hccomp⟩ := key n
  have := PowerFiltration.baseInclusion_isIso t hn
  intro r hr
  obtain ⟨r', hr'⟩ :=
    hclift.comp hc (AffineBasicOpenLifts.of_isIso (PowerFiltration.baseInclusion t n)) r hr
  rw [hccomp] at hr'
  exact ⟨r', hr'⟩

/-- **A statement from which the ascent of quasi-affineness along a thickening follows**:
`Stacks.Thickenings.AffineBasicOpenLifts` for every thickening whose closed subscheme is
quasi-affine.

This is not the route by which the ascent is finally proved — that is the limit argument of
`Stacks.Thickenings.isQuasiAffine_of_isThickening` — but it is a sufficient elementary condition,
and it holds for every finite-order thickening.

`Stacks.Thickenings.quasiAffineAscendsAlongThickening_of_affineBasicOpenLifts` derives
`Stacks.Thickenings.QuasiAffineAscendsAlongThickening` — and hence, through
`Stacks.Thickenings.isQuasiAffineHom_left_iff_right_of_ascends`, part (9) of
[Stacks Project, Tag 09ZV] — from this and nothing else, **with no Noetherian hypothesis
anywhere**.

The hypotheses `Scheme.IsQuasiAffine Y` and `IsAffineOpen (Y.basicOpen r)` are what the proof
consumes: the first gives a finite cover by affine basic opens with affine pairwise
intersections, and the second makes the open over which the two local lifts of `r` are compared
affine.

It holds for every **finite-order** thickening:
`Stacks.Thickenings.affineBasicOpenLifts_of_isFiniteOrderThickening` of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/QuasiAffineAscent.lean`, where
the
first-order case is proved by an elementary Čech computation needing no cohomology group. What is
still quantified over here is a thickening no power of whose ideal sheaf vanishes. -/
def AffineBasicOpenLiftsAlongThickening : Prop :=
  ∀ (Y Y' : Scheme.{u}) (k : Y ⟶ Y'), IsThickening k → Scheme.IsQuasiAffine Y →
    AffineBasicOpenLifts k

/-- **The ascent of quasi-affineness along a thickening, reduced to one elementary statement about
global functions.** Granted `Stacks.Thickenings.AffineBasicOpenLiftsAlongThickening` and nothing
else, `Stacks.Thickenings.QuasiAffineAscendsAlongThickening` holds. This is
`Stacks.Thickenings.isQuasiAffine_of_affineBasicOpenLifts` quantified. -/
theorem quasiAffineAscendsAlongThickening_of_affineBasicOpenLifts
    (hlift : AffineBasicOpenLiftsAlongThickening.{u}) :
    QuasiAffineAscendsAlongThickening.{u} := fun Y Y' k hk hY ↦
  have := hY
  isQuasiAffine_of_affineBasicOpenLifts hk (hlift Y Y' k hk hY)

/-- **The literal lift of a power of a global function along a thickening.** For a thickening
`k : Y ⟶ Y'` with `Y` quasi-affine and a global function `r` on `Y` whose nonvanishing locus is
affine, some positive power of `r` is the restriction of a global function on `Y'`.

This is what the source's proof actually constructs — the obstruction to lifting `r` itself is an
`H¹` class of the ideal sheaf, killed by a power of `r` — and it is stronger than
`Stacks.Thickenings.AffineBasicOpenLiftsAlongThickening`, which is all the ascent needs. -/
def PowerOfSectionLiftsAlongThickening : Prop :=
  ∀ (Y Y' : Scheme.{u}) (k : Y ⟶ Y'), IsThickening k → Scheme.IsQuasiAffine Y →
    ∀ r : Γ(Y, ⊤), IsAffineOpen (Y.basicOpen r) →
      ∃ (n : ℕ) (r' : Γ(Y', ⊤)), k.appTop r' = r ^ (n + 1)

/-- **A lift of a power of the function lifts its nonvanishing locus.** A positive power has the
same nonvanishing locus as the function itself, and the nonvanishing locus of a global function
pulls back to that of its restriction. -/
theorem affineBasicOpenLifts_of_powerOfSectionLifts
    (hlift : PowerOfSectionLiftsAlongThickening.{u}) :
    AffineBasicOpenLiftsAlongThickening.{u} := by
  intro Y Y' k hk hY r hr
  obtain ⟨n, r', hr'⟩ := hlift Y Y' k hk hY r hr
  exact ⟨r', by rw [Scheme.preimage_basicOpen_top, hr', Y.basicOpen_pow r (Nat.succ_pos n)]⟩

/-- **The implication `φ.left` quasi-affine `⟹` `φ.right` quasi-affine of part (9) of
[Stacks Project, Tag 09ZV], reduced to the absolute statement.** Granted
`Stacks.Thickenings.QuasiAffineAscendsAlongThickening` and nothing else, quasi-affineness of the
morphism of closed subschemes gives quasi-affineness of the morphism of ambient schemes.

The reduction is the one the source performs: for an affine open `U'` of `S'` its inverse image
in `S` is affine, so `φ.left ⁻¹ᵁ (j ⁻¹ᵁ U')` is quasi-affine; that open is
`i ⁻¹ᵁ (φ.right ⁻¹ᵁ U')`, and `i` restricts over `φ.right ⁻¹ᵁ U'` to a thickening of it, so the
absolute statement applies.

No tag attribute: an implication carrying a hypothesis the source does not make is not the source
statement. -/
theorem isQuasiAffineHom_right_of_left (hasc : QuasiAffineAscendsAlongThickening.{u})
    {X X' S S' : Scheme.{u}} {i : X ⟶ X'} {j : S ⟶ S'}
    (hi : IsThickening i) (hj : IsThickening j) (φ : Arrow.mk i ⟶ Arrow.mk j)
    (h : IsQuasiAffineHom φ.left) : IsQuasiAffineHom φ.right := by
  refine ⟨fun U' hU' ↦ ?_⟩
  have hQA : Scheme.IsQuasiAffine (φ.left ⁻¹ᵁ (j ⁻¹ᵁ U')) :=
    h.isQuasiAffine_preimage _ ((isAffineOpen_iff_isAffineOpen_preimage hj U').mp hU')
  rw [preimage_left_preimage_eq_preimage_preimage_right φ U'] at hQA
  exact hasc _ _ (i ∣_ φ.right ⁻¹ᵁ U') (hi.morphismRestrict _) hQA

/-- **Part (9) of [Stacks Project, Tag 09ZV], reduced to the absolute statement.** Granted
`Stacks.Thickenings.QuasiAffineAscendsAlongThickening` and nothing else, the morphism of closed
subschemes of a morphism of thickenings is quasi-affine if and only if the morphism of ambient
schemes is.

The `mpr` half uses the hypothesis nowhere; it is
`Stacks.Thickenings.isQuasiAffineHom_left_of_right`.

No tag attribute: a biconditional carrying a hypothesis the source does not make is not the
source statement. The hypothesis is discharged by
`Stacks.Thickenings.quasiAffineAscendsAlongThickening`, and part (9) itself is the resulting
`Stacks.Thickenings.isQuasiAffineHom_left_iff_right`, both in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/QuasiAffineLimit.lean`. -/
theorem isQuasiAffineHom_left_iff_right_of_ascends (hasc : QuasiAffineAscendsAlongThickening.{u})
    {X X' S S' : Scheme.{u}} {i : X ⟶ X'} {j : S ⟶ S'}
    (hi : IsThickening i) (hj : IsThickening j) (φ : Arrow.mk i ⟶ Arrow.mk j) :
    IsQuasiAffineHom φ.left ↔ IsQuasiAffineHom φ.right :=
  ⟨isQuasiAffineHom_right_of_left hasc hi hj φ, isQuasiAffineHom_left_of_right hi hj φ⟩

/-- **Part (9) of [Stacks Project, Tag 09ZV], reduced to the lifting of one global function.**
Granted `Stacks.Thickenings.AffineBasicOpenLiftsAlongThickening` and nothing else, the morphism of
closed subschemes of a morphism of thickenings is quasi-affine if and only if the morphism of
ambient schemes is.

This is the composite of
`Stacks.Thickenings.quasiAffineAscendsAlongThickening_of_affineBasicOpenLifts` with
`Stacks.Thickenings.isQuasiAffineHom_left_iff_right_of_ascends`, recorded because it is the
statement of what part (9) still owes: one elementary lemma about global functions on a
thickening, with no Noetherian hypothesis and no ampleness.

No tag attribute, for the same reason as the previous statement: a biconditional carrying a
hypothesis the source does not make is not the source statement. Part (9) itself, with no
hypothesis, is `Stacks.Thickenings.isQuasiAffineHom_left_iff_right` of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/QuasiAffineLimit.lean`. -/
theorem isQuasiAffineHom_left_iff_right_of_affineBasicOpenLifts
    (hlift : AffineBasicOpenLiftsAlongThickening.{u})
    {X X' S S' : Scheme.{u}} {i : X ⟶ X'} {j : S ⟶ S'}
    (hi : IsThickening i) (hj : IsThickening j) (φ : Arrow.mk i ⟶ Arrow.mk j) :
    IsQuasiAffineHom φ.left ↔ IsQuasiAffineHom φ.right :=
  isQuasiAffineHom_left_iff_right_of_ascends
    (quasiAffineAscendsAlongThickening_of_affineBasicOpenLifts hlift) hi hj φ

end Stacks.Thickenings

end
