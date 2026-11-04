module

public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.SliceUnramifiedAt
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.UnramifiedMinimalGenerators
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.DegreeTwoGeneration
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.DenseSeparableClosedPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The slicing point of the chart construction of Stacks 06N3

Let `q : V ⟶ U` be an unramified morphism of schemes and let `π : V ⟶ Spec k` be smooth over a
field, with `V` nonempty. This file produces the point at which the source of **Stacks 06N3**
slices its smooth chart, together with everything the two slicing lemmas read off it:

* a **closed** point `v` of `V` whose residue field is a finite separable extension of `k`
  (**Stacks 056U**);
* regularity of `𝒪_{V, v}`, `V` being smooth over a field (**Stacks 056S**, the scheme form of
  **Stacks 06M1**);
* the sequence `f₁, …, f_d` of regular functions on an affine open of `U` whose germs form a
  regular sequence generating `𝔪_v`, which is the hypothesis **Stacks 06MD** consumes
  (`AlgebraicGeometry.exists_isAffineOpen_isRegular_ofList_eq_maximalIdeal_stalk_of_unramifiedAt`);
* the residue field datum in the shape in which
  `Stacks.AlgebraicGeometry.unramifiedAt_comp_of_ofList_eq_maximalIdeal_stalk` consumes it, so
  that the slice along those functions is unramified over `Spec k` — which is the hypothesis
  **Stacks 06N2** consumes.

The last two items are stated over different renderings of the residue field extension, and
reconciling them is the content of
`Stacks.AlgebraicGeometry.finite_separable_residueFieldMap_of_finite_separable_Γevaluation`:
**Stacks 056U** delivers `κ(v)` as a `k`-algebra through evaluation of global sections of
`Spec k`, while the criterion of **Stacks 02GF** reads the extension over the residue field of
the base at the image point, through `AlgebraicGeometry.Scheme.Hom.residueFieldMap`. The two
algebra structures sit in one scalar tower, by
`AlgebraicGeometry.Scheme.Γevaluation_naturality`, and `k ⟶ κ(π v)` is the bottom step; so
finiteness passes up by `Module.Finite.of_restrictScalars_finite` and separability by
`Algebra.isSeparable_tower_top_of_isSeparable`.

## Main results

* `finite_separable_residueFieldMap_of_finite_separable_Γevaluation`: the residue field extension
  of **Stacks 056U**, read over the residue field of the base.
* `isRegularLocalRing_stalk_of_smooth_over_field`: the local ring of a scheme smooth over a field
  is regular.
* `exists_isClosed_isRegularLocalRing_finiteSeparable_of_smooth`: the closed point of
  **Stacks 056U** on a nonempty scheme smooth over a field, with its regular local ring and its
  residue field extension over the base.
* `unramifiedAt_comp_of_ofList_eq_maximalIdeal_stalk_over_field`: the slice of a scheme over the
  spectrum of a field, cut out by a sequence generating the maximal ideal, is unramified over that
  spectrum at the sliced point.
* `exists_isClosed_isAffineOpen_isRegular_ofList_eq_maximalIdeal_finiteSeparable_of_unramified`:
  the slicing point of **Stacks 06N3** with its slicing sequence and its residue field datum.

## Implementation notes

Nonemptiness of `V` enters only through `Dense.nonempty`: a dense subset of a nonempty space is
nonempty, which is how the closed point with finite separable residue field is extracted from the
density statement of **Stacks 056U**.

The regularity of `𝒪_{V, v}` is read off `AlgebraicGeometry.isRegular_of_smooth_over_field`
(**Stacks 056S**) through `AlgebraicGeometry.isRegular_iff_regular_stalks` (**Stacks 02IT**).
Regularity of the étale local ring of the fibre, which is where **Stacks 06MD** reads its
hypothesis, is obtained from this one by
`AlgebraicGeometry.Space.exists_fn_isRegular_ofList_eq_maximalIdeal_etaleLocalRing_of_unramifiedAt`
and is not repeated here.

No `@[stacks]` attribute is claimed: this is a step of the proof of **Stacks 06N3**, whose
registration sits on
`AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack_unconditional`, and the
individual tags it uses are registered on the declarations named above.

## References

* [Stacks Project, Tag 02GF](https://stacks.math.columbia.edu/tag/02GF)
* [Stacks Project, Tag 02IT](https://stacks.math.columbia.edu/tag/02IT)
* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
* [Stacks Project, Tag 06M1](https://stacks.math.columbia.edu/tag/06M1)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.AlgebraicGeometry

/-- **The residue field extension of Stacks 056U, read over the residue field of the base.**
**Stacks 056U** presents `κ(x)` as a `k`-algebra through the pullback of global sections of
`Spec k` followed by evaluation at `x`, while the unramifiedness criterion of **Stacks 02GF**
reads the extension over `κ(π x)`, the residue field of the base at the image point. If `κ(x)`
is a finite separable extension of `k` in the first sense then it is one of `κ(π x)` in the
second.

The two algebra structures sit in a scalar tower with `k ⟶ κ(π x)` at the bottom, by
`AlgebraicGeometry.Scheme.Γevaluation_naturality`. Finiteness then passes up the tower by
`Module.Finite.of_restrictScalars_finite` and separability by
`Algebra.isSeparable_tower_top_of_isSeparable`. -/
theorem finite_separable_residueFieldMap_of_finite_separable_Γevaluation
    {k : Type u} [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) (x : X)
    (h : letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Module.Finite k (X.residueField x) ∧ Algebra.IsSeparable k (X.residueField x)) :
    letI := (π.residueFieldMap x).hom.toAlgebra
    Module.Finite ((Spec (.of k)).residueField (π x)) (X.residueField x) ∧
      Algebra.IsSeparable ((Spec (.of k)).residueField (π x)) (X.residueField x) := by
  let algBot : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let algStep : Algebra k ((Spec (.of k)).residueField (π x)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (π x)).hom.toAlgebra
  let algTop : Algebra ((Spec (.of k)).residueField (π x)) (X.residueField x) :=
    (π.residueFieldMap x).hom.toAlgebra
  obtain ⟨hfin, hsep⟩ := h
  have hcomp : (Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop ≫ X.Γevaluation x =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (π x)) ≫
        π.residueFieldMap x := by
    rw [Category.assoc, Scheme.Γevaluation_naturality]
  have : IsScalarTower k ((Spec (.of k)).residueField (π x)) (X.residueField x) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      congrArg (fun m : (CommRingCat.of k) ⟶ X.residueField x => m.hom c) hcomp
  exact ⟨Module.Finite.of_restrictScalars_finite k ((Spec (.of k)).residueField (π x))
      (X.residueField x),
    Algebra.isSeparable_tower_top_of_isSeparable (F := k)
      (L := ((Spec (.of k)).residueField (π x))) (E := (X.residueField x))⟩

/-- **Stacks 056S on stalks.** The local ring of a scheme smooth over a field at any of its
points is a regular local ring.

This is the scheme form of the regularity **Stacks 06M1** asserts for algebraic spaces, read
through `AlgebraicGeometry.isRegular_iff_regular_stalks` (**Stacks 02IT**). -/
@[ega "IV 17.5.8" "(iii), special case",
  sga "1 II 3.1" "special case",
  sga "1 II 5.3" "special case"]
theorem isRegularLocalRing_stalk_of_smooth_over_field {k : Type u} [Field k] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of k)) [Smooth π] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  ((isRegular_iff_regular_stalks X).mp (isRegular_of_smooth_over_field π)).2 x

/-- **The closed point of Stacks 056U on a nonempty scheme smooth over a field**, with its
regular local ring and with its residue field extension read over the residue field of the base.

This is the point `v` at which the chart construction of **Stacks 06N3** slices: the density
statement of **Stacks 056U** supplies a closed point of `V` with `κ(v)/k` finite separable,
`V` is regular because it is smooth over a field, and the extension is transported to the
rendering of **Stacks 02GF** by
`Stacks.AlgebraicGeometry.finite_separable_residueFieldMap_of_finite_separable_Γevaluation`. -/
@[ega "IV 17.15.10" "partial"]
theorem exists_isClosed_isRegularLocalRing_finiteSeparable_of_smooth
    {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [Smooth π] [Nonempty V] :
    ∃ v : V, IsClosed ({v} : Set V) ∧ IsRegularLocalRing (V.presheaf.stalk v) ∧
      (letI := (π.residueFieldMap v).hom.toAlgebra;
        Module.Finite ((Spec (.of k)).residueField (π v)) (V.residueField v) ∧
          Algebra.IsSeparable ((Spec (.of k)).residueField (π v)) (V.residueField v)) := by
  obtain ⟨v, hvclosed, hvsep⟩ :=
    (dense_closedPoints_with_finite_separable_residueField_of_smooth π).nonempty
  exact ⟨v, hvclosed, isRegularLocalRing_stalk_of_smooth_over_field π v,
    finite_separable_residueFieldMap_of_finite_separable_Γevaluation π v hvsep⟩

/-- **The slice cut out by a sequence generating the maximal ideal is unramified over the
spectrum of a field.** This is
`Stacks.AlgebraicGeometry.unramifiedAt_comp_of_ofList_eq_maximalIdeal_stalk` with its hypothesis
on the base discharged: the local ring of `Spec k` at any point is the field itself, so its
maximal ideal vanishes (`AlgebraicGeometry.maximalIdeal_stalk_eq_bot_of_field`).

This is the shape in which the chart construction of **Stacks 06N3** uses the criterion, the
base of the source's cartesian diagram being the spectrum of a field. -/
@[sga "3 XI 1.3" "(ii)"]
theorem unramifiedAt_comp_of_ofList_eq_maximalIdeal_stalk_over_field
    {k : Type u} [Field k] {V Z : Scheme.{u}} (ι : Z ⟶ V) [IsPreimmersion ι]
    (π : V ⟶ Spec (.of k)) [LocallyOfFiniteType (ι ≫ π)] (z : Z)
    {r : ℕ} (h : Fin r → V.presheaf.stalk (ι z))
    (hzero : ∀ i, (ι.stalkMap z).hom (h i) = 0)
    (hgen : Ideal.ofList (List.ofFn h) = maximalIdeal (V.presheaf.stalk (ι z)))
    (hsep : letI := (π.residueFieldMap (ι z)).hom.toAlgebra
      Module.Finite ((Spec (.of k)).residueField (π (ι z))) (V.residueField (ι z)) ∧
        Algebra.IsSeparable ((Spec (.of k)).residueField (π (ι z))) (V.residueField (ι z))) :
    UnramifiedAt (ι ≫ π) z :=
  unramifiedAt_comp_of_ofList_eq_maximalIdeal_stalk ι π z
    (maximalIdeal_stalk_eq_bot_of_field k (π (ι z))) h hzero hgen hsep

/-- **The slicing point of the chart construction of Stacks 06N3, with its slicing sequence.**
Let `q : V ⟶ U` be a morphism of schemes locally of finite type and unramified, and let
`π : V ⟶ Spec k` be smooth with `V` nonempty. Then there are a **closed** point `v` of `V` whose
residue field is finite separable over the residue field of `Spec k`, an affine open `W ⊆ U`
containing `q v`, and regular functions `f₁, …, f_d ∈ Γ(U, W)` lying in `𝔪_{q v}` whose images
in `𝒪_{V, v}` form a regular sequence **generating** `𝔪_v`.

This is the source's run of its argument at one point: the closed point of `V` with finite
separable residue field is **Stacks 056U**, the regularity of `𝒪_{V, v}` is **Stacks 056S**
(the scheme form of **Stacks 06M1**), and the sequence is
`AlgebraicGeometry.exists_isAffineOpen_isRegular_ofList_eq_maximalIdeal_stalk_of_unramifiedAt`,
which selects a minimal generating family of `𝔪_v` inside `φ(𝔪_{q v})` — available because `q`
is unramified (**Stacks 02GF**) — and is a regular sequence because `𝒪_{V, v}` is regular
(**Stacks 00NQ**). The sequence is what **Stacks 06MD** consumes, after being carried to the
étale local ring of the fibre; the residue field datum is what **Stacks 06N2** consumes, through
`Stacks.AlgebraicGeometry.unramifiedAt_comp_of_ofList_eq_maximalIdeal_stalk_over_field`. -/
theorem exists_isClosed_isAffineOpen_isRegular_ofList_eq_maximalIdeal_finiteSeparable_of_unramified
    {k : Type u} [Field k] {V U : Scheme.{u}} (q : V ⟶ U) (π : V ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [Unramified q] [Smooth π] [Nonempty V] :
    ∃ (v : V) (d : ℕ) (W : U.Opens) (hW : q v ∈ W),
      IsClosed ({v} : Set V) ∧ IsAffineOpen W ∧
      IsRegularLocalRing (V.presheaf.stalk v) ∧
      (letI := (π.residueFieldMap v).hom.toAlgebra;
        Module.Finite ((Spec (.of k)).residueField (π v)) (V.residueField v) ∧
          Algebra.IsSeparable ((Spec (.of k)).residueField (π v)) (V.residueField v)) ∧
      ∃ g : Fin d → Γ(U, W),
        (∀ i, U.presheaf.germ W (q v) hW (g i) ∈ maximalIdeal (U.presheaf.stalk (q v))) ∧
          RingTheory.Sequence.IsRegular (V.presheaf.stalk v)
              (List.ofFn fun i =>
                (q.stalkMap v).hom (U.presheaf.germ W (q v) hW (g i))) ∧
            Ideal.ofList (List.ofFn fun i =>
                (q.stalkMap v).hom (U.presheaf.germ W (q v) hW (g i))) =
              maximalIdeal (V.presheaf.stalk v) := by
  obtain ⟨v, hvclosed, hvreg, hvsep⟩ :=
    exists_isClosed_isRegularLocalRing_finiteSeparable_of_smooth π
  obtain ⟨d, W, hW, hWaff, g, hgmem, hgreg, hgspan⟩ :=
    exists_isAffineOpen_isRegular_ofList_eq_maximalIdeal_stalk_of_unramifiedAt q v
      (Unramified.unramifiedAt v) hvreg
  exact ⟨v, d, W, hW, hvclosed, hWaff, hvreg, hvsep, g, hgmem, hgreg, hgspan⟩

end Stacks.AlgebraicGeometry

end
