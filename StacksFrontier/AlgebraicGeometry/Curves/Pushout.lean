module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointCodimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.PushoutSituation
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.CommonAffineOpenOfDimensionOnePointsFiniteComponents

/-!
# The pushout situation of a curve over a field

Let `k` be a field and consider a solid diagram of schemes over `k`

```
  Z ---i--> X
  |
  j
  |
  v
  Y
```

subject to the four conditions of [Stacks Project, Tag 0E35]:

* (a) `X` is separated of finite type over `k` of dimension `≤ 1`;
* (b) `i : Z ⟶ X` is a closed immersion;
* (c) `Z` and `Y` are finite over `Spec k`;
* (d) `j : Z ⟶ Y` is surjective.

The naming here follows the library's `PushoutAlongClosedImmersionAndIntegralSituation`, in which
the common source of the two morphisms is called `Z` and the target of the integral morphism is
called `Y`.  Against the notation of [Stacks Project, Tag 0E35] the translation is `Z = Z'`,
`X = X'` and `Y = Z`, so (c) is finiteness of both `Z` and `Y` and (d) is surjectivity of `j`.

What this file supplies is the passage from these four conditions to the standing situation of
[Stacks Project, Tag 0ECI], which is what the construction of the pushout
([Stacks Project, Tag 0E25]) and everything downstream of it take as input.  Two of 0ECI's three
assumptions have to be produced: that `j` is integral, and that each fibre of `j` maps under `i`
into a single affine open of `X`.

## Main definitions

* `AlgebraicGeometry.curvePushoutSituation`: the standing situation of
  [Stacks Project, Tag 0ECI] attached to the four conditions above.

## Implementation notes

Integrality of `j` is a cancellation: `j ≫ pY = pZ` is finite by (c) and `pY` is finite, hence
separated, so `j` itself is finite and in particular integral.

The affine-open condition is [Stacks Project, Tag 09NN], available here as
`AlgebraicGeometry.exists_isAffineOpen_containing_of_stalk_krullDimLE_one_of_finite_components`:
a finite family of points of a separated scheme whose quasi-compact opens have finitely many
irreducible components, and whose local rings are Noetherian of Krull dimension at most one, lies
in one affine open.  Each of its hypotheses comes from (a) and (c):

* the family is finite because `j` is finite, so its fibres are finite
  (`AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton`);
* `X` is separated as a scheme because it is separated over the affine scheme `Spec k`;
* `X` is locally Noetherian because it is locally of finite type over `Spec k`, which is
  Noetherian; a quasi-compact open of it is therefore a Noetherian scheme and so has finitely
  many irreducible components, and every local ring of it is Noetherian;
* the local rings have Krull dimension at most one because the Krull dimension of the local ring
  at a point is the codimension of that point
  (`AlgebraicGeometry.coheight_le_topologicalKrullDim` together with Mathlib's
  `AlgebraicGeometry.krullDimLE_of_coheight_le`), and the dimension of `X` bounds every
  codimension.

Separatedness of `X` over `k` is used only through `Scheme.IsSeparated X`, and the dimension
bound only through the codimension of the finitely many points in play; no stronger consequence
of (a) is needed.

## References

* [Stacks Project, Tag 0E35](https://stacks.math.columbia.edu/tag/0E35)
* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 09NN](https://stacks.math.columbia.edu/tag/09NN)
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0E35.** The four conditions of the section — `X` separated of finite
type over the field `k` of dimension `≤ 1`, `i` a closed immersion, `Z` and `Y` finite over
`Spec k`, and `j` surjective — put the diagram in the standing situation of
[Stacks Project, Tag 0ECI], so that the pushout `Y ⨿_Z X` of [Stacks Project, Tag 0E25] and
everything derived from it apply.

The content is the verification of the two assumptions of [Stacks Project, Tag 0ECI] that are not
hypotheses here: that `j` is integral, and that every fibre of `j` maps under `i` into a single
affine open of `X`.  The latter is [Stacks Project, Tag 09NN]. -/
@[stacks 0E35 "the verification that the assumptions of More on Morphisms, Proposition 0E25 \
are satisfied; the conclusions (1)-(7) are `AlgebraicGeometry.exists_pushout_of_curve`"]
def curvePushoutSituation
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) (pZ : Z ⟶ Spec (.of k))
    (i : Z ⟶ X) (j : Z ⟶ Y) (hi : i ≫ pX = pZ) (hj : j ≫ pY = pZ)
    [IsSeparated pX] [LocallyOfFiniteType pX] (hdim : topologicalKrullDim X ≤ 1)
    [IsClosedImmersion i] [IsFinite pY] [IsFinite pZ] [Surjective j] :
    PushoutAlongClosedImmersionAndIntegralSituation.{u} :=
  have hjFinite : IsFinite j := by
    have : IsFinite (j ≫ pY) := by rw [hj]; infer_instance
    exact IsFinite.of_comp j pY
  have hXsep : Scheme.IsSeparated X := Scheme.IsSeparated.of_isSeparated pX
  have hXnoeth : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  have hcomp : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite := by
    intro U hU
    have : CompactSpace U := isCompact_iff_compactSpace.mp hU
    have : IsNoetherian U.toScheme := ⟨⟩
    exact finite_irreducibleComponents_of_isNoetherian
  have hdimPt : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x) := by
    intro x
    refine krullDimLE_of_coheight_le (n := 1) ?_
    exact_mod_cast (coheight_le_topologicalKrullDim x).trans hdim
  { S := Spec (.of k)
    X := X
    Y := Y
    Z := Z
    pX := pX
    pY := pY
    pZ := pZ
    i := i
    j := j
    i_over := hi
    j_over := hj
    isIntegralHom_j := inferInstance
    fiber_preimage_subset_affine := by
      intro y
      have hfib : (j ⁻¹' {y}).Finite := j.finite_preimage_singleton y
      have : Finite (j ⁻¹' {y} : Set Z) := hfib.to_subtype
      obtain ⟨U, hU, hmem⟩ :=
        exists_isAffineOpen_containing_of_stalk_krullDimLE_one_of_finite_components
          X hcomp (fun z : (j ⁻¹' {y} : Set Z) ↦ i z.1)
          (fun _ ↦ inferInstance) (fun z ↦ hdimPt (i z.1))
      exact ⟨U, hU, fun z hz ↦ hmem ⟨z, hz⟩⟩ }

/-- The base scheme of `curvePushoutSituation` is `Spec k`. -/
@[simp]
lemma curvePushoutSituation_S
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) (pZ : Z ⟶ Spec (.of k))
    (i : Z ⟶ X) (j : Z ⟶ Y) (hi : i ≫ pX = pZ) (hj : j ≫ pY = pZ)
    [IsSeparated pX] [LocallyOfFiniteType pX] (hdim : topologicalKrullDim X ≤ 1)
    [IsClosedImmersion i] [IsFinite pY] [IsFinite pZ] [Surjective j] :
    (curvePushoutSituation k pX pY pZ i j hi hj hdim).S = Spec (.of k) := rfl

/-- The scheme `X` of `curvePushoutSituation` is the given curve `X`. -/
@[simp]
lemma curvePushoutSituation_X
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) (pZ : Z ⟶ Spec (.of k))
    (i : Z ⟶ X) (j : Z ⟶ Y) (hi : i ≫ pX = pZ) (hj : j ≫ pY = pZ)
    [IsSeparated pX] [LocallyOfFiniteType pX] (hdim : topologicalKrullDim X ≤ 1)
    [IsClosedImmersion i] [IsFinite pY] [IsFinite pZ] [Surjective j] :
    (curvePushoutSituation k pX pY pZ i j hi hj hdim).X = X := rfl

/-- The scheme `Y` of `curvePushoutSituation` is the given scheme `Y`. -/
@[simp]
lemma curvePushoutSituation_Y
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) (pZ : Z ⟶ Spec (.of k))
    (i : Z ⟶ X) (j : Z ⟶ Y) (hi : i ≫ pX = pZ) (hj : j ≫ pY = pZ)
    [IsSeparated pX] [LocallyOfFiniteType pX] (hdim : topologicalKrullDim X ≤ 1)
    [IsClosedImmersion i] [IsFinite pY] [IsFinite pZ] [Surjective j] :
    (curvePushoutSituation k pX pY pZ i j hi hj hdim).Y = Y := rfl

/-- The scheme `Z` of `curvePushoutSituation` is the given scheme `Z`. -/
@[simp]
lemma curvePushoutSituation_Z
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) (pZ : Z ⟶ Spec (.of k))
    (i : Z ⟶ X) (j : Z ⟶ Y) (hi : i ≫ pX = pZ) (hj : j ≫ pY = pZ)
    [IsSeparated pX] [LocallyOfFiniteType pX] (hdim : topologicalKrullDim X ≤ 1)
    [IsClosedImmersion i] [IsFinite pY] [IsFinite pZ] [Surjective j] :
    (curvePushoutSituation k pX pY pZ i j hi hj hdim).Z = Z := rfl

/-- The structure morphism `X ⟶ S` of `curvePushoutSituation` is `pX`. -/
@[simp]
lemma curvePushoutSituation_pX
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) (pZ : Z ⟶ Spec (.of k))
    (i : Z ⟶ X) (j : Z ⟶ Y) (hi : i ≫ pX = pZ) (hj : j ≫ pY = pZ)
    [IsSeparated pX] [LocallyOfFiniteType pX] (hdim : topologicalKrullDim X ≤ 1)
    [IsClosedImmersion i] [IsFinite pY] [IsFinite pZ] [Surjective j] :
    (curvePushoutSituation k pX pY pZ i j hi hj hdim).pX = pX := rfl

/-- The structure morphism `Y ⟶ S` of `curvePushoutSituation` is `pY`. -/
@[simp]
lemma curvePushoutSituation_pY
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) (pZ : Z ⟶ Spec (.of k))
    (i : Z ⟶ X) (j : Z ⟶ Y) (hi : i ≫ pX = pZ) (hj : j ≫ pY = pZ)
    [IsSeparated pX] [LocallyOfFiniteType pX] (hdim : topologicalKrullDim X ≤ 1)
    [IsClosedImmersion i] [IsFinite pY] [IsFinite pZ] [Surjective j] :
    (curvePushoutSituation k pX pY pZ i j hi hj hdim).pY = pY := rfl

/-- The structure morphism `Z ⟶ S` of `curvePushoutSituation` is `pZ`. -/
@[simp]
lemma curvePushoutSituation_pZ
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) (pZ : Z ⟶ Spec (.of k))
    (i : Z ⟶ X) (j : Z ⟶ Y) (hi : i ≫ pX = pZ) (hj : j ≫ pY = pZ)
    [IsSeparated pX] [LocallyOfFiniteType pX] (hdim : topologicalKrullDim X ≤ 1)
    [IsClosedImmersion i] [IsFinite pY] [IsFinite pZ] [Surjective j] :
    (curvePushoutSituation k pX pY pZ i j hi hj hdim).pZ = pZ := rfl

/-- The closed immersion `Z ⟶ X` of `curvePushoutSituation` is `i`. -/
@[simp]
lemma curvePushoutSituation_i
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) (pZ : Z ⟶ Spec (.of k))
    (i : Z ⟶ X) (j : Z ⟶ Y) (hi : i ≫ pX = pZ) (hj : j ≫ pY = pZ)
    [IsSeparated pX] [LocallyOfFiniteType pX] (hdim : topologicalKrullDim X ≤ 1)
    [IsClosedImmersion i] [IsFinite pY] [IsFinite pZ] [Surjective j] :
    (curvePushoutSituation k pX pY pZ i j hi hj hdim).i = i := rfl

/-- The integral morphism `Z ⟶ Y` of `curvePushoutSituation` is `j`. -/
@[simp]
lemma curvePushoutSituation_j
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) (pZ : Z ⟶ Spec (.of k))
    (i : Z ⟶ X) (j : Z ⟶ Y) (hi : i ≫ pX = pZ) (hj : j ≫ pY = pZ)
    [IsSeparated pX] [LocallyOfFiniteType pX] (hdim : topologicalKrullDim X ≤ 1)
    [IsClosedImmersion i] [IsFinite pY] [IsFinite pZ] [Surjective j] :
    (curvePushoutSituation k pX pY pZ i j hi hj hdim).j = j := rfl

end AlgebraicGeometry

end
