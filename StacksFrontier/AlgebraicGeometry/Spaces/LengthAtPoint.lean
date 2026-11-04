module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicityAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricLengthPointIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative

/-!
# The length of a quasi-coherent module at a point of an algebraic space

Let `X` be an algebraic space over a scheme `S`, let `F` be a quasi-coherent `𝒪_X`-module, let
`x` be a point of `|X|` and let `d ∈ ℕ∞ = {0, 1, 2, …, ∞}`. Then *`F` has length `d` at `x`*
when the length of the stalk `F_{x̄}` over the étale local ring `𝒪_{X, x̄}` is `d` for a
geometric point `x̄` lying over `x`. This is Stacks 0EE2, and it is well posed because that
length does not depend on the choice of `x̄` (Stacks 0EE1,
`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`).

Every point of `|X|` is the image of a geometric point
(`AlgebraicGeometry.Space.exists_geometricRepresentative`), so the condition on *some*
geometric point above `x` is equivalent to the condition on *every* one, and there is exactly
one `d` for which it holds; that value is
`AlgebraicGeometry.Space.lengthAt`.

## Main definitions

* `AlgebraicGeometry.Space.HasLengthAt`: **Stacks 0EE2** — the predicate "`F` has length `d`
  at `x`" for a point `x` of `|X|`.
* `AlgebraicGeometry.Space.lengthAt`: the length of `F` at `x`, the unique `d` for which
  `AlgebraicGeometry.Space.HasLengthAt` holds.

## Main results

* `AlgebraicGeometry.Space.hasLengthAt_iff_forall_geometricPoint`: the condition holds for
  some geometric point above `x` exactly when it holds for every one.
* `AlgebraicGeometry.Space.hasLengthAt_iff_exists_chartScheme` and
  `AlgebraicGeometry.Space.hasLengthAt_iff_forall_chartScheme`: conditions (2) and (3) of
  Stacks 0EE1 exactly as the source states them — the length is `d` at `x` exactly when
  `length_{𝒪_{U, u}} (F|_U)_u = d` for some, equivalently for every, étale morphism `U → X`
  with `U` a scheme and `u ∈ U` mapping to `x`.
* `AlgebraicGeometry.Space.tfae_hasLengthAt`: **Stacks 0EE1** at the point `x`, conditions
  (1), (2) and (3), so that `AlgebraicGeometry.Space.HasLengthAt` is "the equivalent conditions of
  Lemma 0EE1".
* `AlgebraicGeometry.Space.hasLengthAt_iff_exists_etaleChart` and
  `AlgebraicGeometry.Space.hasLengthAt_iff_forall_etaleChart`: the same chart conditions
  phrased through small étale neighbourhoods of geometric points above `x` — the Zariski stalk
  of `φ^* F` has length `d` at the point of some, equivalently of every, étale scheme chart
  neighbourhood of some, equivalently of every, geometric point above `x`.
* `AlgebraicGeometry.Space.hasLengthAt_iff_lengthAt_eq` and
  `AlgebraicGeometry.Space.HasLengthAt.unique`: there is exactly one length at `x`.

## Implementation notes

Stacks 0EE2 defines "`F` has length `d` at `x`" as the equivalent conditions of Stacks 0EE1.
The predicate is defined by condition (1), `length_{𝒪_{X, x̄}} F_{x̄} = d`, for a geometric
point `x̄` above `x`, in its existential form, which is the reading that does not become
vacuous if no geometric point were to lie over `x`; the universally quantified form is the
theorem `AlgebraicGeometry.Space.hasLengthAt_iff_forall_geometricPoint`. That the choice of
`x̄` does not matter is Stacks 0EE1 itself
(`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`). The other two conditions of
Stacks 0EE1 are the theorems `AlgebraicGeometry.Space.hasLengthAt_iff_exists_chartScheme` and
`AlgebraicGeometry.Space.hasLengthAt_iff_forall_chartScheme`, collected in
`AlgebraicGeometry.Space.tfae_hasLengthAt`. In those, an étale morphism `U → X` with `U` a
scheme is an étale scheme chart `W : SmallEtale B S hS X`, the scheme is `chartScheme W`, a
point `u` maps to `x` when `AlgebraicGeometry.Space.chartSchemeToPoints` sends it to `x`, and
`(F|_U)_u` is the ordinary stalk at `u` of `AlgebraicGeometry.Space.restrictToChart`.

Quasi-coherence of `F` is an instance argument of the definition itself, as in the source:
it is what makes the value independent of the geometric point, hence what makes the
definition a condition on `x` rather than on a geometric point above `x`. The module universe
is `u` for the same reason — Stacks 05VP, which drives the independence, is available there.

## References

* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE2](https://stacks.math.columbia.edu/tag/0EE2)
* [Stacks Project, Tag 0486](https://stacks.math.columbia.edu/tag/0486)
* [Stacks Project, Tag 05VN](https://stacks.math.columbia.edu/tag/05VN)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- **Stacks 0EE2: `F` has length `d` at `x`.** For a quasi-coherent `𝒪_X`-module `F`, a point
`x` of `|X|` and `d ∈ ℕ∞`, this says that the stalk `F_{x̄}` has length `d` over the étale local
ring `𝒪_{X, x̄}` for a geometric point `x̄` of `X` lying over `x`.

Stacks 0EE2 defines this as the equivalent conditions of Stacks 0EE1; the definition uses
condition (1), which by that lemma does not depend on the choice of `x̄`
(`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`, so the condition holds for some
`x̄` above `x` iff for every one: `AlgebraicGeometry.Space.hasLengthAt_iff_forall_geometricPoint`)
and is equivalent to conditions (2) and (3), the length of `(F|_U)_u` over `𝒪_{U, u}` for some,
respectively every, étale `U → X` from a scheme and `u ∈ U` over `x`
(`AlgebraicGeometry.Space.tfae_hasLengthAt`). -/
@[stacks 0EE2]
def HasLengthAt (F : Modules.{u, u} B S hS X hX) [F.IsQuasicoherentOnSite]
    (x : points B S hS X) (d : ℕ∞) : Prop :=
  ∃ xbar : GeometricPoint B S hS X,
    xbar.LiesOver x ∧ geometricLength B S hS ⟨X, hX⟩ xbar F = d

/-- **The length at a point may be tested on any geometric point above it.** A quasi-coherent
`F` has length `d` at `x` exactly when the stalk of `F` at *every* geometric point above `x`
has length `d` over the étale local ring there.

Two geometric points above `x` give the same length
(`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`), and there is one
(`AlgebraicGeometry.Space.exists_geometricRepresentative`). -/
theorem hasLengthAt_iff_forall_geometricPoint (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite] (x : points B S hS X) (d : ℕ∞) :
    HasLengthAt B S hS hX F x d ↔
      ∀ xbar : GeometricPoint B S hS X, xbar.LiesOver x →
        geometricLength B S hS ⟨X, hX⟩ xbar F = d := by
  refine ⟨fun ⟨ybar, hybar, hd⟩ xbar hxbar => ?_, fun h => ?_⟩
  · rw [geometricLength_eq_of_image_eq B S hS hX xbar ybar (hxbar.trans hybar.symm) F]
    exact hd
  · obtain ⟨xbar, hxbar⟩ := exists_geometricRepresentative B S hS X x
    exact ⟨xbar, hxbar, h xbar hxbar⟩

/-- The length of `F` at a geometric point above `x` is `d` iff the stalk at a chart point over `x`
has length `d`. -/
private theorem geometricLength_eq_iff_length_stalk_restrictToChart
    (F : Modules.{u, u} B S hS X hX) [F.IsQuasicoherentOnSite] {x : points B S hS X}
    {xbar : GeometricPoint B S hS X} (hxbar : xbar.LiesOver x) {W : SmallEtale B S hS X}
    {u : chartScheme W} (hu : chartSchemeToPoints B S hS X W u = x) {d : ℕ∞} :
    geometricLength B S hS ⟨X, hX⟩ xbar F = d ↔
      Module.length ((chartScheme W).presheaf.stalk u)
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          (restrictToChart B S hS hX F W).val.presheaf u) = d := by
  rw [geometricLength_eq_length_stalk_restrictToChart B S hS ⟨X, hX⟩ F xbar W u
    (hu.trans hxbar.symm)]

/-- **Stacks 0EE1, condition (2), at a point of `|X|`.** A quasi-coherent `F` has length `d`
at `x` exactly when, for some étale morphism `U → X` with `U` a scheme and some `u ∈ U`
mapping to `x`, the stalk `(F|_U)_u` has length `d` over `𝒪_{U, u}`.

For any such pair `(U, u)` and any geometric point `x̄` above `x`, the length of `F` at `x̄`
is the length of `(F|_U)_u`
(`AlgebraicGeometry.Space.geometricLength_eq_length_stalk_restrictToChart`, which uses
Stacks 05VN to see `u` as the point of a neighbourhood of `x̄`); a geometric point above `x`
exists (`AlgebraicGeometry.Space.exists_geometricRepresentative`), and so does a chart point
above `x` (`AlgebraicGeometry.Space.exists_chartSchemeToPoints_eq`). -/
theorem hasLengthAt_iff_exists_chartScheme (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite] (x : points B S hS X) (d : ℕ∞) :
    HasLengthAt B S hS hX F x d ↔
      ∃ (W : SmallEtale B S hS X) (u : chartScheme W), chartSchemeToPoints B S hS X W u = x ∧
        Module.length ((chartScheme W).presheaf.stalk u)
          (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
            (restrictToChart B S hS hX F W).val.presheaf u) = d := by
  refine ⟨fun ⟨xbar, hxbar, hd⟩ => ?_, fun ⟨W, u, hu, hd⟩ => ?_⟩
  · obtain ⟨W, u, hu⟩ := exists_chartSchemeToPoints_eq B S hS ⟨X, hX⟩ x
    exact ⟨W, u, hu,
      (geometricLength_eq_iff_length_stalk_restrictToChart B S hS hX F hxbar hu).1 hd⟩
  · obtain ⟨xbar, hxbar⟩ := exists_geometricRepresentative B S hS X x
    exact ⟨xbar, hxbar,
      (geometricLength_eq_iff_length_stalk_restrictToChart B S hS hX F hxbar hu).2 hd⟩

/-- **Stacks 0EE1, condition (3), at a point of `|X|`.** A quasi-coherent `F` has length `d`
at `x` exactly when, for every étale morphism `U → X` with `U` a scheme and every `u ∈ U`
mapping to `x`, the stalk `(F|_U)_u` has length `d` over `𝒪_{U, u}`.

Each such stalk has the length of `F` at a geometric point above `x`
(`AlgebraicGeometry.Space.geometricLength_eq_length_stalk_restrictToChart`), and a chart
point above `x` exists (`AlgebraicGeometry.Space.exists_chartSchemeToPoints_eq`), so the
universal condition implies the existential one of
`AlgebraicGeometry.Space.hasLengthAt_iff_exists_chartScheme`. -/
theorem hasLengthAt_iff_forall_chartScheme (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite] (x : points B S hS X) (d : ℕ∞) :
    HasLengthAt B S hS hX F x d ↔
      ∀ (W : SmallEtale B S hS X) (u : chartScheme W), chartSchemeToPoints B S hS X W u = x →
        Module.length ((chartScheme W).presheaf.stalk u)
          (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
            (restrictToChart B S hS hX F W).val.presheaf u) = d := by
  refine ⟨fun ⟨xbar, hxbar, hd⟩ W u hu => ?_, fun h => ?_⟩
  · exact (geometricLength_eq_iff_length_stalk_restrictToChart B S hS hX F hxbar hu).1 hd
  · obtain ⟨W, u, hu⟩ := exists_chartSchemeToPoints_eq B S hS ⟨X, hX⟩ x
    exact (hasLengthAt_iff_exists_chartScheme B S hS hX F x d).2 ⟨W, u, hu, h W u hu⟩

/-- **Stacks 0EE1 at a point `x` of `|X|`: conditions (1), (2) and (3) are equivalent.** For a
quasi-coherent `𝒪_X`-module `F`, a point `x ∈ |X|` and `d ∈ ℕ∞`, the following are
equivalent:

1. `length_{𝒪_{X, x̄}} F_{x̄} = d` for a geometric point `x̄` above `x`;
2. for some étale morphism `U → X` with `U` a scheme and `u ∈ U` mapping to `x`,
   `length_{𝒪_{U, u}} (F|_U)_u = d`;
3. for every étale morphism `U → X` with `U` a scheme and `u ∈ U` mapping to `x`,
   `length_{𝒪_{U, u}} (F|_U)_u = d`.

Condition (1) is `AlgebraicGeometry.Space.HasLengthAt` by definition, so this is the
statement that `AlgebraicGeometry.Space.HasLengthAt` is "the equivalent conditions of
Lemma 0EE1", as Stacks 0EE2 has it. Together with
`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq` (condition (1) does not depend on the
geometric point chosen above `x`) this is the whole of Stacks 0EE1. -/
@[stacks 0EE1]
theorem tfae_hasLengthAt (F : Modules.{u, u} B S hS X hX) [F.IsQuasicoherentOnSite]
    (x : points B S hS X) (d : ℕ∞) :
    List.TFAE
      [∃ xbar : GeometricPoint B S hS X,
          xbar.LiesOver x ∧ geometricLength B S hS ⟨X, hX⟩ xbar F = d,
        ∃ (W : SmallEtale B S hS X) (u : chartScheme W), chartSchemeToPoints B S hS X W u = x ∧
          Module.length ((chartScheme W).presheaf.stalk u)
            (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
              (restrictToChart B S hS hX F W).val.presheaf u) = d,
        ∀ (W : SmallEtale B S hS X) (u : chartScheme W), chartSchemeToPoints B S hS X W u = x →
          Module.length ((chartScheme W).presheaf.stalk u)
            (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
              (restrictToChart B S hS hX F W).val.presheaf u) = d] := by
  tfae_have 1 ↔ 2 := hasLengthAt_iff_exists_chartScheme B S hS hX F x d
  tfae_have 1 ↔ 3 := hasLengthAt_iff_forall_chartScheme B S hS hX F x d
  tfae_finish

/-- **Condition (2) of Stacks 0EE1 through neighbourhoods of geometric points.** A quasi-coherent
`F` has length `d` at `x` exactly when the Zariski stalk of `φ^* F` has length `d` at the point of
the chart of some small étale neighbourhood of some geometric point above `x`. -/
theorem hasLengthAt_iff_exists_etaleChart (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite] (x : points B S hS X) (d : ℕ∞) :
    HasLengthAt B S hS hX F x d ↔
      ∃ xbar : GeometricPoint B S hS X, xbar.LiesOver x ∧
        ∃ V : SmallEtaleNeighborhood xbar,
          chartZariskiLength.{u, u} B S hS hX V.chart (chartPoint B S hS X V) F = d := by
  refine ⟨fun ⟨xbar, hxbar, hd⟩ => ?_, fun ⟨xbar, hxbar, V, hV⟩ => ?_⟩
  · exact ⟨xbar, hxbar, (geometricLength_eq_iff_exists_etaleChart B S hS hX F d).1 hd⟩
  · exact ⟨xbar, hxbar, (geometricLength_eq_iff_exists_etaleChart B S hS hX F d).2 ⟨V, hV⟩⟩

/-- **Condition (3) of Stacks 0EE1 through neighbourhoods of geometric points.** A quasi-coherent
`F` has length `d` at `x` exactly when the Zariski stalk of `φ^* F` has length `d` at the point of
the chart of every small étale neighbourhood of every geometric point above `x`. -/
theorem hasLengthAt_iff_forall_etaleChart (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite] (x : points B S hS X) (d : ℕ∞) :
    HasLengthAt B S hS hX F x d ↔
      ∀ xbar : GeometricPoint B S hS X, xbar.LiesOver x →
        ∀ V : SmallEtaleNeighborhood xbar,
          chartZariskiLength.{u, u} B S hS hX V.chart (chartPoint B S hS X V) F = d := by
  rw [hasLengthAt_iff_forall_geometricPoint]
  exact forall_congr' fun xbar => forall_congr' fun _ =>
    geometricLength_eq_iff_forall_etaleChart B S hS hX F d

/-- **The length of a quasi-coherent `𝒪_X`-module at a point of `|X|`.** The length of the
stalk of `F` at a geometric point above `x` over the étale local ring there, a value in
`ℕ∞ = {0, 1, 2, …, ∞}`.

A geometric point above `x` exists
(`AlgebraicGeometry.Space.exists_geometricRepresentative`) and the length does not depend on
which one is chosen (`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`), so this is the
unique `d` with `AlgebraicGeometry.Space.HasLengthAt B S hS hX F x d`, by
`AlgebraicGeometry.Space.hasLengthAt_iff_lengthAt_eq`. -/
def lengthAt (F : Modules.{u, u} B S hS X hX) [F.IsQuasicoherentOnSite]
    (x : points B S hS X) : ℕ∞ :=
  geometricLength B S hS ⟨X, hX⟩ (exists_geometricRepresentative B S hS X x).choose F

/-- The length at `x` is `d` exactly when `F` has length `d` at `x`, so
`AlgebraicGeometry.Space.lengthAt` is the length of Stacks 0EE2. -/
theorem hasLengthAt_iff_lengthAt_eq (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite] (x : points B S hS X) (d : ℕ∞) :
    HasLengthAt B S hS hX F x d ↔ lengthAt B S hS hX F x = d := by
  refine ⟨fun h => ?_, fun h =>
    ⟨_, (exists_geometricRepresentative B S hS X x).choose_spec, h⟩⟩
  exact (hasLengthAt_iff_forall_geometricPoint B S hS hX F x d).1 h _
    (exists_geometricRepresentative B S hS X x).choose_spec

/-- **`F` has length `d` at `x` for exactly one `d`.** This is the well-posedness of
Stacks 0EE2 as a statement about the point `x`. -/
theorem HasLengthAt.unique {F : Modules.{u, u} B S hS X hX} [F.IsQuasicoherentOnSite]
    {x : points B S hS X} {d d' : ℕ∞} (h : HasLengthAt B S hS hX F x d)
    (h' : HasLengthAt B S hS hX F x d') : d = d' :=
  ((hasLengthAt_iff_lengthAt_eq B S hS hX F x d).1 h).symm.trans
    ((hasLengthAt_iff_lengthAt_eq B S hS hX F x d').1 h')

/-- **`F` has a length at every point of `|X|`**, namely
`AlgebraicGeometry.Space.lengthAt`. -/
theorem hasLengthAt_lengthAt (F : Modules.{u, u} B S hS X hX) [F.IsQuasicoherentOnSite]
    (x : points B S hS X) : HasLengthAt B S hS hX F x (lengthAt B S hS hX F x) :=
  (hasLengthAt_iff_lengthAt_eq B S hS hX F x _).2 rfl

end AlgebraicGeometry.Space

end
