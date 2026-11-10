module

public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.FiniteNearGenericPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Fibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.GenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.StalkDimension
public import StacksCore.Tactic.StacksAttribute

/-!
# Generically finite dominant morphisms of integral schemes

Let `f : X ⟶ Y` be a dominant morphism of integral schemes which is locally of finite type. Each
of the schemes has a single generic point, and `f` carries the one to the other. The following
conditions on `f` turn out to be equivalent:

* the induced extension of function fields `R(Y) ⊆ R(X)` has transcendence degree zero;
* that extension is finite;
* there are nonempty affine opens `U ⊆ X` and `V ⊆ Y` with `f(U) ⊆ V` over which `f` is finite;
* the generic point of `X` is the only point of `X` above the generic point of `Y`;
* if `f` is separated or quasi-compact, `f` is finite over some nonempty affine open of `Y`.

## Main results

* `AlgebraicGeometry.tfae_trdeg_functionField_eq_zero`: the first four conditions are all
  equivalent.
* `AlgebraicGeometry.eq_genericPoint_iff_finite_fibre`: the generic point of the source is the
  only point above the generic point of the target exactly when that fibre is finite.
* `AlgebraicGeometry.exists_affineOpens_isFinite_iff_eq_genericPoint`: finiteness on a pair of
  nonempty affine opens is equivalent to the same condition.
* `AlgebraicGeometry.exists_affineOpen_isFinite_restrict_iff_eq_genericPoint`: for a separated
  or quasi-compact morphism, so is finiteness over a nonempty affine open of the target.
* `AlgebraicGeometry.trdeg_functionField_eq_zero_of_eq_genericPoint`: the geometric conditions
  force the extension of function fields to have transcendence degree zero.
* `AlgebraicGeometry.eq_genericPoint_of_trdeg_functionField_eq_zero`: transcendence degree zero
  forces them back.
* `AlgebraicGeometry.trdeg_functionField_eq_zero_iff_finite`: transcendence degree zero is the
  same as finiteness of the extension.

## Implementation notes

The condition that the generic point of `X` be the only point above the generic point of `Y` is
the hinge. For an integral scheme the set of generic points of irreducible components is the
singleton of the generic point, so that condition is literally the first condition of
[Stacks Project, Tag 0BAH], and it is also literally finiteness of the fibre over the generic
point, which is the hypothesis of [Stacks Project, Tag 02NW]. The three equivalences are
therefore each half of one of those two lemmas:

* finiteness on a pair of affine opens is read off from the covering form of Tag 02NW in one
  direction, and in the other it gives quasi-finiteness of `f` at the generic point of `X`,
  which is the third condition of Tag 0BAH;
* finiteness over an affine open of the target comes from [Stacks Project, Tag 0BAI], whose
  "quasi-compact or separated" hypothesis is exactly the one the source imposes for this last
  condition, after shrinking the dense open it produces to an affine neighbourhood of the
  generic point; conversely a finite morphism has finite fibres.

Transcendence degree zero follows because quasi-finiteness at a point makes the residue field
extension there finite, and at the generic point the residue field extension is the extension of
function fields. This is `AlgebraicGeometry.Scheme.Hom.finite_residueField_of_quasiFiniteAt`
followed by `AlgebraicGeometry.isAlgebraic_functionField_of_finite_residueField_genericPoint`.

The containment `R(Y) ⊆ R(X)` is `AlgebraicGeometry.dominantFunctionFieldMap`, whose algebra
structure is supplied by a `letI` inside each statement so that it is the same instance
throughout. That map is the same as `AlgebraicGeometry.Scheme.Hom.functionFieldMap`, which is
how the compatibility of the extension with the maps of section rings into the function fields
becomes available here.

The two field-theoretic conditions are proved from the geometry of a single pair of affine opens
`U ⊆ X`, `V ⊆ Y` with `f(U) ⊆ V`, over which `Γ(Y, V) → Γ(X, U)` is an injective map of domains
of finite type whose extension of fraction fields is `R(Y) ⊆ R(X)`:

* transcendence degree zero makes `R(X)` algebraic over `R(Y)`, so the subfield of `R(X)`
  generated over `R(Y)` by the images of finitely many algebra generators of `Γ(X, U)` is finite
  over `R(Y)`, and being a field containing the image of `Γ(X, U)` it is all of `R(X)`; this
  replaces the source's denominator-clearing argument, which reaches condition (3) directly by
  inverting the leading coefficients of the polynomials killing those generators;
* a point of `X` above the generic point of `Y` cuts out a prime of `Γ(X, U)` contracting to the
  zero ideal of `Γ(Y, V)`, and over an algebraic extension of fraction fields such a prime is
  zero — a nonzero element of it satisfies a nonzero polynomial over `Γ(Y, V)` whose constant
  term is then a nonzero element of the contraction. The zero ideal is the prime cut out by the
  generic point of `X`, so the point is that generic point. This is the source's argument that
  `𝒪_{X,x}` is a field, Stacks Tag 00GS, read on a chart.

## References

* [Stacks Project, Tag 02NX](https://stacks.math.columbia.edu/tag/02NX)
* [Stacks Project, Tag 02NW](https://stacks.math.columbia.edu/tag/02NW)
* [Stacks Project, Tag 0BAH](https://stacks.math.columbia.edu/tag/0BAH)
* [Stacks Project, Tag 0BAI](https://stacks.math.columbia.edu/tag/0BAI)
* [Stacks Project, Tag 00GS](https://stacks.math.columbia.edu/tag/00GS)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
  [LocallyOfFiniteType f] [IsDominant f]

omit [LocallyOfFiniteType f] in
/-- A dominant morphism of integral schemes carries the generic point of its source to the
generic point of its target. -/
private theorem map_genericPoint : f (genericPoint X) = genericPoint Y :=
  ((tfae_isDominant_of_isIntegral f).out 1 2).mp (inferInstance : IsDominant f)

/-- The generic point of an integral scheme is the generic point of an irreducible
component. -/
private theorem genericPoint_mem_genericPoints (Z : Scheme.{u}) [IsIntegral Z] :
    genericPoint Z ∈ genericPoints Z := by
  rw [genericPoints_eq_singleton]; rfl

/-- The map on sections over a pair of affine opens induced by a morphism which is finite
between them is a finite ring map. -/
private theorem finite_appLE_of_isFinite_resLE {X' Y' : Scheme.{u}} (g : X' ⟶ Y')
    (U : X'.affineOpens) (V : Y'.affineOpens) (hUV : U.1 ≤ g ⁻¹ᵁ V.1)
    (h : IsFinite (g.resLE V.1 U.1 hUV)) : (g.appLE V.1 U.1 hUV).hom.Finite := by
  have : IsAffine V.1.toScheme := V.2
  have : IsFinite (g.resLE V.1 U.1 hUV) := h
  exact (RingHom.finite_respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso g V.1 U.1 hUV)).mp (g.resLE V.1 U.1 hUV).finite_appTop

/-- For a pair of domains `A ⊆ B` with fraction fields `K ⊆ L`, if `L` is algebraic over `K`
then `B` is algebraic over `A`. -/
private theorem isAlgebraic_of_isAlgebraic_fractionRing {A B K L : Type*} [CommRing A]
    [IsDomain A] [CommRing B] [IsDomain B] [Field K] [Field L] [Algebra A B] [Algebra A K]
    [IsFractionRing A K] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [Algebra.IsAlgebraic K L] :
    Algebra.IsAlgebraic A B := by
  refine ⟨fun b => ?_⟩
  exact (isAlgebraic_algebraMap_iff (IsFractionRing.injective B L)).mp
    ((IsFractionRing.isAlgebraic_iff A K L).mpr (Algebra.IsAlgebraic.isAlgebraic _))

/-- For a pair of domains `A ⊆ B` with fraction fields `K ⊆ L` and `L` algebraic over `K`, an
ideal of `B` contracting to zero in `A` is zero: a nonzero element of it satisfies a nonzero
polynomial over `A`, whose constant term is then a nonzero element of the contraction. -/
private theorem eq_bot_of_comap_eq_bot_of_isAlgebraic {A B K L : Type*} [CommRing A]
    [IsDomain A] [CommRing B] [IsDomain B] [Field K] [Field L] [Algebra A B] [Algebra A K]
    [IsFractionRing A K] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [Algebra.IsAlgebraic K L] (q : Ideal B)
    (hq : q.comap (algebraMap A B) = ⊥) : q = ⊥ := by
  have : Algebra.IsAlgebraic A B :=
    isAlgebraic_of_isAlgebraic_fractionRing (A := A) (B := B) (K := K) (L := L)
  refine eq_bot_iff.2 fun b hb => ?_
  rcases eq_or_ne b 0 with rfl | hb0
  · exact Ideal.zero_mem _
  · exact absurd hq (Ideal.under_ne_bot_of_algebraic_mem hb0 hb
      (Algebra.IsAlgebraic.isAlgebraic b))

/-- For a pair of domains `A ⊆ B` with fraction fields `K ⊆ L`, if `B` is a finite-type
`A`-algebra and `L` is algebraic over `K`, then `L` is finite over `K`: the subfield of `L`
generated over `K` by the images of finitely many algebra generators of `B` is finite over `K`,
and being a field containing the image of `B` it is all of `L`. -/
private theorem finite_fractionRing_of_finiteType_of_isAlgebraic {A B K L : Type*} [CommRing A]
    [IsDomain A] [CommRing B] [IsDomain B] [Field K] [Field L] [Algebra A B] [Algebra A K]
    [IsFractionRing A K] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [Algebra.FiniteType A B]
    [Algebra.IsAlgebraic K L] : Module.Finite K L := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A B).FG)
  set T : Set L := algebraMap B L '' (s : Set B)
  have : Finite T := (s.finite_toSet.image (algebraMap B L)).to_subtype
  have hfd : FiniteDimensional K (IntermediateField.adjoin K T) :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral
  have hmemB : ∀ b : B, algebraMap B L b ∈ IntermediateField.adjoin K T := by
    intro b
    have hb : b ∈ Algebra.adjoin A (s : Set B) := hs ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin K T ⟨x, hx, rfl⟩
    | algebraMap a =>
      rw [← IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A K L]
      exact (IntermediateField.adjoin K T).algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have htop : IntermediateField.adjoin K T = ⊤ := by
    refine top_le_iff.mp fun z _ => ?_
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := B) z
    exact div_mem (hmemB x) (hmemB y)
  rw [htop] at hfd
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

/-- Transporting a stalk map along an equality of its target point is composition with the
comparison of stalks along the corresponding specialization. -/
private theorem stalkMap_cast_hom_eq {X' Y' : Scheme.{u}} (g : X' ⟶ Y') (x : X') {y : Y'}
    (hxy : g x = y) (hspec : g x ⤳ y) :
    (hxy ▸ g.stalkMap x).hom =
      (Y'.presheaf.stalkSpecializes hspec ≫ g.stalkMap x).hom := by
  cases hxy
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  simp

omit [LocallyOfFiniteType f] in
/-- The two spellings of the extension of function fields of a dominant morphism of integral
schemes agree: `dominantFunctionFieldMap` transports the stalk map at the generic point along
the equality of its image with the generic point of the target, while
`AlgebraicGeometry.Scheme.Hom.functionFieldMap` precomposes it with the comparison of stalks
along that same specialization. -/
private theorem dominantFunctionFieldMap_eq_functionFieldMap :
    dominantFunctionFieldMap f = (Scheme.Hom.functionFieldMap f).hom :=
  stalkMap_cast_hom_eq f (genericPoint X) (map_genericPoint f)
    (specializes_genericPoint_of_isDominant f)

omit [LocallyOfFiniteType f] in
/-- The extension of function fields is compatible with the maps from the section rings over a
pair of nonempty opens `U ≤ f⁻¹ V` into the function fields. -/
private theorem dominantFunctionFieldMap_germToFunctionField {V : Y.Opens} {U : X.Opens}
    (hUV : U ≤ f ⁻¹ᵁ V) [Nonempty V] [Nonempty U] (a : Γ(Y, V)) :
    dominantFunctionFieldMap f (Y.germToFunctionField V a) =
      X.germToFunctionField U (f.appLE V U hUV a) := by
  rw [dominantFunctionFieldMap_eq_functionFieldMap f]
  exact f.functionFieldMap_germToFunctionField hUV a

/-- On an affine open of an integral scheme the generic point cuts out the zero ideal. -/
private theorem primeIdealOf_eq_bot_of_eq_genericPoint (Z : Scheme.{u}) [IsIntegral Z]
    {W : Z.Opens} (hW : IsAffineOpen W) [Nonempty W] (z : Z) (hz : z ∈ W)
    (hzgen : z = genericPoint Z) : (hW.primeIdealOf ⟨z, hz⟩).asIdeal = ⊥ := by
  subst hzgen
  have := IsIntegral.component_integral (X := Z) W
  rw [hW.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine, PrimeSpectrum.asIdeal_bot]

omit [IsDominant f] in
/-- **Stacks Project, Tag 02NX, condition (4) as finiteness of the generic fibre.** For a
morphism locally of finite type between integral schemes, the generic point of the source is the
only point above the generic point of the target exactly when that fibre is finite. -/
@[stacks 02NX "condition (4), restated as finiteness of the fibre over the generic point of the
target, which is the hypothesis of Tag 02NW"]
theorem eq_genericPoint_iff_finite_fibre :
    (∀ x : X, f x = genericPoint Y → x = genericPoint X) ↔
      (f ⁻¹' {genericPoint Y}).Finite := by
  refine ⟨fun h => (Set.finite_singleton (genericPoint X)).subset fun x hx => h x hx,
    fun hfin => ?_⟩
  have hdisc : DiscreteTopology (f.fiber (genericPoint Y)) := by
    have : Finite (f.fiber (genericPoint Y)) :=
      (f.fiberHomeo (genericPoint Y)).finite_iff.mpr hfin
    infer_instance
  have hsub : f ⁻¹' {genericPoint Y} ⊆ genericPoints X :=
    ((quasiFiniteAt_over_genericPoint_tfae f (genericPoint Y)
      (genericPoint_mem_genericPoints Y)).out 2 1).mp (by
        intro x hx
        refine ((quasiFiniteAt_tfae f x).out 2 1).mp ?_
        have : DiscreteTopology (f.fiber (f x)) := by rwa [hx]
        exact isOpen_discrete _)
  intro x hx
  simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hsub hx

/-- **Stacks Project, Tag 02NX, conditions (3) and (4).** For a dominant morphism locally of
finite type between integral schemes, finiteness on some pair of nonempty affine opens of the
source and target is equivalent to the generic point of the source being the only point above
the generic point of the target. -/
@[stacks 02NX "conditions (3) and (4)"]
theorem exists_affineOpens_isFinite_iff_eq_genericPoint :
    (∃ (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1),
        (U.1 : Set X).Nonempty ∧ (V.1 : Set Y).Nonempty ∧
          IsFinite (f.resLE V.1 U.1 hUV)) ↔
      (∀ x : X, f x = genericPoint Y → x = genericPoint X) := by
  have hgpY : genericPoint Y ∈ genericPoints Y := genericPoint_mem_genericPoints Y
  constructor
  · rintro ⟨U, V, hUV, hUne, hVne, hfin⟩
    have hxU : genericPoint X ∈ U.1 :=
      ((genericPoint_spec X).mem_open_set_iff U.1.2).mpr (by simpa using hUne)
    have happ : (f.appLE V.1 U.1 hUV).hom.Finite :=
      finite_appLE_of_isFinite_resLE f U V hUV hfin
    have hqf : quasiFiniteAt f (genericPoint X) :=
      (quasiFiniteAt_iff_exists_affineOpens f _).mpr
        ⟨V, U, hxU, hUV, happ.to_finiteType, by
          unfold RingHom.QuasiFiniteAt
          let : Algebra Γ(Y, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
          have : Module.Finite Γ(Y, V.1) Γ(X, U.1) := happ
          infer_instance⟩
    have hsub : f ⁻¹' {genericPoint Y} ⊆ genericPoints X :=
      ((quasiFiniteAt_over_genericPoint_tfae f (genericPoint Y) hgpY).out 3 1).mp (by
        intro ξ hξ _
        rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hξ
        exact hξ ▸ hqf)
    intro x hx
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hsub hx
  · intro h
    obtain ⟨n, U, V, hgpV, hcover, hfins⟩ :=
      (finite_preimage_singleton_iff_exists_affine_cover_isFinite f (genericPoint Y) hgpY).mp
        ((eq_genericPoint_iff_finite_fibre f).mp h)
    obtain ⟨i, hi⟩ :=
      Set.mem_iUnion.mp
        (hcover (show genericPoint X ∈ f ⁻¹' {genericPoint Y} from map_genericPoint f))
    obtain ⟨hUi, hfini⟩ := hfins i
    exact ⟨U i, V, hUi, ⟨genericPoint X, hi⟩, ⟨genericPoint Y, hgpV⟩, hfini⟩

/-- **Stacks Project, Tag 02NX, condition (5).** For a dominant morphism locally of finite type
between integral schemes which is separated or quasi-compact, finiteness over some nonempty
affine open of the target is equivalent to the generic point of the source being the only point
above the generic point of the target. -/
@[stacks 02NX "condition (5)"]
theorem exists_affineOpen_isFinite_restrict_iff_eq_genericPoint
    (hsep_or_qc : IsSeparated f ∨ QuasiCompact f) :
    (∃ V : Y.affineOpens, (V.1 : Set Y).Nonempty ∧ IsFinite (f ∣_ V.1)) ↔
      (∀ x : X, f x = genericPoint Y → x = genericPoint X) := by
  constructor
  · rintro ⟨V, hVne, hfin⟩
    have hgpV : genericPoint Y ∈ V.1 :=
      ((genericPoint_spec Y).mem_open_set_iff V.1.2).mpr (by simpa using hVne)
    have : IsFinite (f ∣_ V.1) := hfin
    have hf := (f ∣_ V.1).finite_preimage_singleton ⟨genericPoint Y, hgpV⟩
    refine (eq_genericPoint_iff_finite_fibre f).mpr ?_
    refine (hf.image fun x : (f ⁻¹ᵁ V.1 : Scheme) => x.1).subset ?_
    intro x hx
    have hfx : f x = genericPoint Y := by simpa using hx
    have hxV : x ∈ f ⁻¹ᵁ V.1 := by simpa [hfx] using hgpV
    exact ⟨⟨x, hxV⟩, Subtype.ext ((morphismRestrict_base_coe f V.1 ⟨x, hxV⟩).trans hfx), rfl⟩
  · intro h
    have hcompX : (irreducibleComponents X).Finite := by
      simp [irreducibleComponents_eq_singleton]
    have hcompY : (irreducibleComponents Y).Finite := by
      simp [irreducibleComponents_eq_singleton]
    have hgeneric : f ⁻¹' genericPoints Y = genericPoints X := by
      rw [genericPoints_eq_singleton (α := Y), genericPoints_eq_singleton (α := X)]
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨h x, fun hx => hx ▸ map_genericPoint f⟩
    obtain ⟨V, hVdense, hVfin⟩ := exists_dense_open_isFinite f
      (genericPoints.finite hcompX) (genericPoints.finite hcompY) hgeneric
      (hsep_or_qc.elim Or.inr Or.inl)
    obtain ⟨W, hgpW, hWfin⟩ :=
      exists_affineOpen_mem_isFinite_restrict_of_isFinite_restrict f hVfin
        (genericPoints_subset_of_dense_isOpen hcompY V.isOpen hVdense
          (genericPoint_mem_genericPoints Y))
    exact ⟨W, ⟨genericPoint Y, hgpW⟩, hWfin⟩

/-- **Stacks Project, Tag 02NX, the implication to condition (1).** If the generic point of the
source is the only point above the generic point of the target, then the induced extension of
function fields has transcendence degree zero. -/
@[stacks 02NX "the implication from condition (4) -- equivalently (3), or (5) -- to condition
(1)"]
theorem trdeg_functionField_eq_zero_of_eq_genericPoint
    (h : ∀ x : X, f x = genericPoint Y → x = genericPoint X) :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
    Algebra.trdeg Y.functionField X.functionField = 0 := by
  have hgpY : genericPoint Y ∈ genericPoints Y := genericPoint_mem_genericPoints Y
  have hsub : f ⁻¹' {genericPoint Y} ⊆ genericPoints X := by
    intro x hx
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff]
    exact h x hx
  have hall : ∀ ξ : X, ξ ∈ genericPoints X → f ξ = genericPoint Y → quasiFiniteAt f ξ :=
    ((quasiFiniteAt_over_genericPoint_tfae f (genericPoint Y) hgpY).out 1 3).mp hsub
  have hqf : quasiFiniteAt f (genericPoint X) :=
    hall (genericPoint X) (genericPoint_mem_genericPoints X) (map_genericPoint f)
  have hfd := f.finite_residueField_of_quasiFiniteAt (genericPoint X) hqf.2
  let : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  exact trdeg_eq_zero_iff.mpr
    (isAlgebraic_functionField_of_finite_residueField_genericPoint f hfd)

/-- Around any point `x` of the source, a pair of affine opens `x ∈ U ⊆ f⁻¹ V` has `R(Y)` and
`R(X)` as fraction fields of its section rings. So if the extension of function fields is
algebraic, it is finite, and if `x` lies over the generic point, it cuts out the zero ideal of
`Γ(X, U)`. -/
private theorem finite_and_primeIdealOf_eq_bot_of_isAlgebraic
    (halg : letI : Algebra Y.functionField X.functionField :=
        (dominantFunctionFieldMap f).toAlgebra
      Algebra.IsAlgebraic Y.functionField X.functionField) (x : X) :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
    Module.Finite Y.functionField X.functionField ∧
      ∃ (U : X.affineOpens) (hxU : x ∈ U.1),
        f x = genericPoint Y → (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal = ⊥ := by
  let : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  let : Algebra.IsAlgebraic Y.functionField X.functionField := halg
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV (f ⁻¹ᵁ V).2
  have : Nonempty V := ⟨⟨f x, hxV⟩⟩
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(Y, V) X.functionField :=
    (f.appLE V U hUV ≫ X.germToFunctionField U).hom.toAlgebra
  have : IsScalarTower Γ(Y, V) Γ(X, U) X.functionField := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, V) Y.functionField X.functionField :=
    .of_algebraMap_eq fun a => (dominantFunctionFieldMap_germToFunctionField f hUV a).symm
  have := functionField_isFractionRing_of_isAffineOpen Y V hV
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  have := IsIntegral.component_integral (X := Y) V
  have := IsIntegral.component_integral (X := X) U
  have : Algebra.FiniteType Γ(Y, V) Γ(X, U) := f.finiteType_appLE hV hU hUV
  refine ⟨finite_fractionRing_of_finiteType_of_isAlgebraic (A := Γ(Y, V)) (B := Γ(X, U)),
    ⟨U, hU⟩, hxU, fun hfx => ?_⟩
  refine eq_bot_of_comap_eq_bot_of_isAlgebraic (A := Γ(Y, V)) (K := Y.functionField)
    (L := X.functionField) _ ?_
  rw [show (algebraMap Γ(Y, V) Γ(X, U)) = (f.appLE V U hUV).hom from rfl,
    ← PrimeSpectrum.comap_asIdeal, IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV hxU]
  exact primeIdealOf_eq_bot_of_eq_genericPoint Y hV (f x) (hUV hxU) hfx

/-- **Stacks Project, Tag 02NX, conditions (1) and (2).** For a dominant morphism locally of
finite type between integral schemes, the extension of function fields `R(Y) ⊆ R(X)` has
transcendence degree zero exactly when it is finite. -/
@[stacks 02NX "conditions (1) and (2): the extension of function fields has transcendence degree
zero if and only if it is finite"]
theorem trdeg_functionField_eq_zero_iff_finite :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
    Algebra.trdeg Y.functionField X.functionField = 0 ↔
      Module.Finite Y.functionField X.functionField := by
  let : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  refine ⟨fun h => (finite_and_primeIdealOf_eq_bot_of_isAlgebraic f (trdeg_eq_zero_iff.mp h)
    (genericPoint X)).1, fun h => ?_⟩
  let : Module.Finite Y.functionField X.functionField := h
  exact trdeg_eq_zero_iff.mpr (Algebra.IsAlgebraic.of_finite _ _)

/-- **Stacks Project, Tag 02NX, the implication from condition (1) to condition (4).** If the
extension of function fields has transcendence degree zero, then the generic point of the source
is the only point above the generic point of the target: on a pair of affine opens the point in
question cuts out a prime contracting to the zero ideal, and over an algebraic extension of
fraction fields such a prime is zero, which is the prime cut out by the generic point. -/
@[stacks 02NX "the implication from condition (1) to condition (4)"]
theorem eq_genericPoint_of_trdeg_functionField_eq_zero
    (h : letI : Algebra Y.functionField X.functionField :=
        (dominantFunctionFieldMap f).toAlgebra
      Algebra.trdeg Y.functionField X.functionField = 0) :
    ∀ x : X, f x = genericPoint Y → x = genericPoint X := by
  let : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  intro x hfx
  obtain ⟨-, U, hxU, hbot⟩ :=
    finite_and_primeIdealOf_eq_bot_of_isAlgebraic f (trdeg_eq_zero_iff.mp h) x
  have hU := U.2
  have : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  have hgU : genericPoint X ∈ U.1 :=
    ((genericPoint_spec X).mem_open_set_iff U.1.2).mpr ⟨x, trivial, hxU⟩
  have hqbot := hbot hfx
  have hgbot : (hU.primeIdealOf ⟨genericPoint X, hgU⟩).asIdeal = ⊥ :=
    primeIdealOf_eq_bot_of_eq_genericPoint X hU (genericPoint X) hgU rfl
  calc x = hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) :=
        (hU.fromSpec_primeIdealOf ⟨x, hxU⟩).symm
    _ = hU.fromSpec (hU.primeIdealOf ⟨genericPoint X, hgU⟩) := by
        rw [PrimeSpectrum.ext (hqbot.trans hgbot.symm)]
    _ = genericPoint X := hU.fromSpec_primeIdealOf ⟨genericPoint X, hgU⟩

/-- **Stacks Project, Tag 02NX, conditions (1)–(4).** For a dominant morphism locally of finite
type between integral schemes the following are equivalent: the extension of function fields
`R(Y) ⊆ R(X)` has transcendence degree zero; that extension is finite; `f` is finite on some
pair of nonempty affine opens `U ⊆ X`, `V ⊆ Y` with `f(U) ⊆ V`; the generic point of `X` is the
only point of `X` above the generic point of `Y`. -/
@[stacks 02NX "the equivalence of conditions (1), (2), (3) and (4)", ega "II 6.1.8" "more general"]
theorem tfae_trdeg_functionField_eq_zero :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
    List.TFAE
      [Algebra.trdeg Y.functionField X.functionField = 0,
        Module.Finite Y.functionField X.functionField,
        ∃ (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1),
          (U.1 : Set X).Nonempty ∧ (V.1 : Set Y).Nonempty ∧ IsFinite (f.resLE V.1 U.1 hUV),
        ∀ x : X, f x = genericPoint Y → x = genericPoint X] := by
  let : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  tfae_have 1 ↔ 2 := trdeg_functionField_eq_zero_iff_finite f
  tfae_have 1 → 4 := eq_genericPoint_of_trdeg_functionField_eq_zero f
  tfae_have 4 → 1 := trdeg_functionField_eq_zero_of_eq_genericPoint f
  tfae_have 3 ↔ 4 := exists_affineOpens_isFinite_iff_eq_genericPoint f
  tfae_finish

end AlgebraicGeometry

end
