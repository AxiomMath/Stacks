module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.RingTheory.MvPolynomial.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Affine space with the origin doubled

Gluing two copies of affine `n`-space over a field along the complements of their origins, by
the identity on the coordinates, produces *affine space with the origin doubled*: a scheme
carrying two canonical affine charts that agree away from the origin but have distinct origins.

The coordinate functions agree on the overlap, so they descend to a morphism to affine space,
and that morphism carries each of the two chart origins to the origin of affine space.

## Main definitions

* `AlgebraicGeometry.puncturedAffineSpace`: the complement of the origin in affine `n`-space,
  as the union of the standard opens of the coordinate functions.
* `AlgebraicGeometry.doubledZeroPreGlueData`, `AlgebraicGeometry.doubledZeroGlueData`: the
  two-chart gluing datum whose off-diagonal overlap is punctured affine space and whose
  transition is the identity.
* `AlgebraicGeometry.affineSpaceWithDoubledZero`: the resulting scheme.
* `AlgebraicGeometry.chartInclusion`: its two canonical affine charts.
* `AlgebraicGeometry.coordinateMorphismData`, `AlgebraicGeometry.coordinateMorphism`: the
  morphism to affine space induced by the coordinates on either chart, with its chart equations.
* `AlgebraicGeometry.affineOrigin`: the origin of affine `n`-space.

## Main results

* `AlgebraicGeometry.coordinateMorphism_map_origin`: the coordinate morphism carries the origin
  of each chart to the origin of affine space.

## Implementation notes

The charts are indexed by `ULift (Fin 2)`, since Mathlib's scheme gluing datum places its index
type in the same universe as the schemes. Both copies use the same polynomial ring, so the
coordinate identification on the overlap is literally the identity morphism, and the auxiliary
`CategoryTheory.GlueData'` form makes the cocycle condition vacuous because three pairwise
distinct charts do not exist. The construction is meaningful in dimension zero as well, so no
positivity hypothesis on `n` is imposed; in dimension zero the two charts are disjoint. The
origin of affine space is presented as the prime ideal of polynomials with vanishing constant
term.

## References

* [Stacks Project, Tag 01JD](https://stacks.math.columbia.edu/tag/01JD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

add_to_stacks 01JD "affine_open_charts" AlgebraicGeometry.isAffineOpen_opensRange

namespace AlgebraicGeometry

/-- The complement of the origin in affine `n`-space, expressed as the union of the standard
opens of its coordinate functions. -/
noncomputable abbrev puncturedAffineSpace (k : Type u) [Field k] (n : ℕ) :
    (Spec (.of (MvPolynomial (Fin n) k))).Opens :=
  ⨆ i, PrimeSpectrum.basicOpen (MvPolynomial.X i : MvPolynomial (Fin n) k)

/-- Auxiliary gluing data in which only the off-diagonal intersections of the two affine charts
are specified. -/
@[implicit_reducible] noncomputable def doubledZeroPreGlueData
    (k : Type u) [Field k] (n : ℕ) :
    CategoryTheory.GlueData' Scheme.{u} where
  J := ULift.{u} (Fin 2)
  U _ := Spec (.of (MvPolynomial (Fin n) k))
  V _ _ _ := (puncturedAffineSpace k n).toScheme
  f _ _ _ := (puncturedAffineSpace k n).ι
  f_hasPullback := by intros; infer_instance
  t _ _ _ := 𝟙 _
  t' i j l hij hil hjl := by
    exfalso; obtain ⟨i⟩ := i; obtain ⟨j⟩ := j; obtain ⟨l⟩ := l
    fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all
  t_fac i j l hij hil hjl := by
    exfalso; obtain ⟨i⟩ := i; obtain ⟨j⟩ := j; obtain ⟨l⟩ := l
    fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all
  t_inv := by intros; simp
  cocycle i j l hij hil hjl := by
    exfalso; obtain ⟨i⟩ := i; obtain ⟨j⟩ := j; obtain ⟨l⟩ := l
    fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all

/-- The gluing datum for two copies of affine `n`-space identified away from the origin by the
identity on their coordinates. -/
@[implicit_reducible,
  ega "II 1.3.3", sga "3 VIB 5.6.4" "partial", sga "6 II 2.2.7.2" "more general"]
noncomputable def doubledZeroGlueData (k : Type u) [Field k] (n : ℕ) :
    Scheme.GlueData.{u} where
  toGlueData := CategoryTheory.GlueData.ofGlueData' (doubledZeroPreGlueData k n)
  f_open i j := by
    dsimp [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f',
      doubledZeroPreGlueData]
    split_ifs <;> infer_instance

/-- Affine `n`-space over `k` with its origin doubled, obtained by gluing two copies along the
complements of their origins via the coordinate identification. -/
@[stacks 01JD "doubled_zero_construction", ega "I 5.5.11" "doubled origin constr."]
noncomputable abbrev affineSpaceWithDoubledZero (k : Type u) [Field k] (n : ℕ) :
    Scheme.{u} :=
  (doubledZeroGlueData k n).glued

/-- Either canonical affine chart in affine space with doubled origin. -/
@[implicit_reducible] noncomputable def chartInclusion (k : Type u) [Field k] (n : ℕ)
    (i : Fin 2) :
    Spec (.of (MvPolynomial (Fin n) k)) ⟶ affineSpaceWithDoubledZero k n :=
  (doubledZeroGlueData k n).ι ⟨i⟩

/-- The canonical charts of affine space with doubled origin are open immersions. -/
instance chartInclusion_isOpenImmersion (k : Type u) [Field k] (n : ℕ)
    (i : Fin 2) : IsOpenImmersion (chartInclusion k n i) :=
  Scheme.GlueData.ι_isOpenImmersion (doubledZeroGlueData k n) ⟨i⟩

/-- The coordinate maps on the two charts of affine space with doubled origin glue to a scheme
morphism to affine space, restricting to the identity on each chart. -/
@[stacks 01JD "coordinate_morphism",
  ega "I 5.5.11" "morphism to Spec k[t]",
  sga "6 II 2.2.7.2" "more general"]
noncomputable def coordinateMorphismData (k : Type u) [Field k] (n : ℕ) :
    { f : affineSpaceWithDoubledZero k n ⟶
        Spec (.of (MvPolynomial (Fin n) k)) //
      ∀ i : Fin 2,
        chartInclusion k n i ≫ f = 𝟙 _ } := by
  classical
  let D := doubledZeroGlueData k n
  have hcompat : ∀ a : D.toGlueData.J × D.toGlueData.J,
      D.toGlueData.diagram.fst a ≫ (fun _ => 𝟙 _) _ =
        D.toGlueData.diagram.snd a ≫ (fun _ => 𝟙 _) _ := by
    rintro ⟨i, j⟩
    change D.f i j ≫ 𝟙 _ = D.t i j ≫ D.f j i ≫ 𝟙 _
    rcases i with ⟨i⟩; rcases j with ⟨j⟩
    fin_cases i <;> fin_cases j <;>
      simp [D, doubledZeroGlueData, GlueData.ofGlueData', doubledZeroPreGlueData,
        GlueData'.f']
  exact ⟨Multicoequalizer.desc D.toGlueData.diagram _ (fun _ => 𝟙 _) hcompat, fun i =>
    Multicoequalizer.π_desc D.toGlueData.diagram _ (fun _ => 𝟙 _) hcompat ⟨i⟩⟩

/-- The morphism from affine space with doubled origin to affine space induced by the
coordinates on either chart. -/
noncomputable abbrev coordinateMorphism (k : Type u) [Field k] (n : ℕ) :
    affineSpaceWithDoubledZero k n ⟶
      Spec (.of (MvPolynomial (Fin n) k)) :=
  (coordinateMorphismData k n).val

/-- The origin of affine space, corresponding to the ideal of polynomials with
zero constant coefficient. -/
noncomputable def affineOrigin (k : Type u) [Field k] (n : ℕ) :
    Spec (.of (MvPolynomial (Fin n) k)) :=
  ⟨RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k),
    RingHom.ker_isPrime _⟩

/-- The coordinate morphism maps the origin of each affine chart to the origin of affine
space. -/
@[stacks 01JD "origins_map_to_origin", ega "I 5.5.11" "two origins over 0"]
theorem coordinateMorphism_map_origin (k : Type u) [Field k] (n : ℕ)
    (i : Fin 2) :
    coordinateMorphism k n
        (chartInclusion k n i
          (affineOrigin k n)) = affineOrigin k n :=
  congrArg (fun g => g (affineOrigin k n))
    ((coordinateMorphismData k n).property i)

end AlgebraicGeometry

end
