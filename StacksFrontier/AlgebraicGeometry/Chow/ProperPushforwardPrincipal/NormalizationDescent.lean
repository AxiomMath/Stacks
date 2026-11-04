module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.NormalCurveDegree
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationOverField

/-!
# Stacks 02RU: the degree of a principal divisor on a proper curve vanishes

Let `X` be an integral scheme of dimension one, proper over a field `k`. For a nonzero rational
function `f` on `X`,

  `∑_{x ∈ X} ord_x(f) · [κ(x) : k] = 0`.

The normal case is `Stacks.Chow.principalDivisorDegree_eq_zero_of_isNormal`. The general case
descends along the normalization `ν : X^ν ⟶ X`, which is finite (Stacks 0BXR), proper over `k`
(Stacks 0GK4), dominant and birational (Stacks 0BXC), with `X^ν` normal and again of dimension
one. The norm formula of Stacks 02RT, in the form
`Stacks.Chow.principalDivisorDegree_norm`, gives

  `deg div_{X^ν}(F) = deg div_X(Nm(F))`,

and because `ν` is birational the extension `R(X) ⟶ R(X^ν)` is an isomorphism, so the norm of the
image `F` of `f` is `f` itself. The left-hand side vanishes by the normal case.

## Main results

* `Stacks.Chow.bijective_dominantFunctionFieldMap_of_isBirational` — a birational dominant
  morphism of integral schemes induces an isomorphism of function fields.
* `Stacks.Chow.norm_algebraMap_of_bijective` — the norm of a field extension whose structure map
  is bijective is the inverse of that map.
* `Stacks.Chow.topologicalKrullDim_normalizationSchemeOverField` — the normalization of a scheme
  locally of finite type over a field has the same dimension.
* `Stacks.Chow.principalDivisorDegree_eq_zero` — **Stacks 02RU**.
* `Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_isCurve` — **Stacks 02RU** in
  its cycle form, `c_* div(f) = 0`.

## Implementation notes

The delta-dimension of the normalization is computed from Stacks 02QO
(`Stacks.Chow.topologicalKrullDim_eq_relativeDimension_toNat`) rather than from a general
statement that a finite surjective morphism preserves dimension: the relative dimension at the
generic point is unchanged because the residue field extension there is an isomorphism, which is
exactly what birationality provides, and over a field the dimension of an integral scheme is that
relative dimension.

The base scheme of `Stacks.Chow.fieldChowSituation k` is `Spec k` definitionally but not
reducibly, so the structure morphism has to be presented at both spellings and the instances
re-registered by hand at the second; that is what the local `let`s in the proof of Stacks 02RU
do.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 0BXC](https://stacks.math.columbia.edu/tag/0BXC)
* [Stacks Project, Tag 0BXR](https://stacks.math.columbia.edu/tag/0BXR)
* [Stacks Project, Tag 0GK4](https://stacks.math.columbia.edu/tag/0GK4)
* [Stacks Project, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Birational morphisms and function fields -/

/-- A morphism inducing an isomorphism on local rings at a point induces an isomorphism on
residue fields there. -/
theorem isIso_residueFieldMap_of_isIso_stalkMap {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    [IsIso (f.stalkMap x)] : IsIso (f.residueFieldMap x) :=
  (IsLocalRing.ResidueField.mapEquiv
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom

/-- A birational morphism of integral schemes is an isomorphism on stalks at the generic point. -/
private theorem isIso_stalkMap_genericPoint_of_isBirational {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIntegral X] (hf : IsBirational f) : IsIso (f.stalkMap (genericPoint X)) :=
  hf.2 _ (by rw [genericPoints_eq_singleton]; exact Set.mem_singleton _)

/-- **A birational dominant morphism of integral schemes induces an isomorphism of function
fields.** The extension is the stalk map at the generic point, transported along the
identification of its image with the generic point of the target, and birationality says exactly
that that stalk map is an isomorphism. -/
theorem bijective_dominantFunctionFieldMap_of_isBirational {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIntegral X] [IsIntegral S] [IsDominant f] (hf : IsBirational f) :
    Function.Bijective (dominantFunctionFieldMap f) := by
  have _ := isIso_stalkMap_genericPoint_of_isBirational f hf
  have key : ∀ (z : S) (h : f.base (genericPoint X) = z),
      Function.Bijective ((h ▸ f.stalkMap (genericPoint X)).hom) := by
    intro z h
    cases h
    exact ConcreteCategory.bijective_of_isIso _
  exact key _ _

/-- **The norm of a field extension whose structure map is bijective.** The degree is one, so the
norm of `algebraMap a` is `a`. -/
theorem norm_algebraMap_of_bijective {K L : Type u} [Field K] [Field L] [Algebra K L]
    (hbij : Function.Bijective (algebraMap K L)) (a : K) :
    Algebra.norm K (algebraMap K L a) = a := by
  have hrank : Module.finrank K L = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId K L) hbij).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  rw [Algebra.norm_algebraMap, hrank, pow_one]

/-! ### The dimension of the normalization -/

/-- **The normalization of a scheme locally of finite type over a field has the same
dimension.** The normalization is dominant and birational, so the generic point of the
normalization lies over the generic point and the residue field extension there is an
isomorphism; over a field the dimension of an integral scheme is the relative dimension at the
generic point, by Stacks 02QO. -/
theorem topologicalKrullDim_normalizationSchemeOverField {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ AlgebraicGeometry.Spec (.of k)) [LocallyOfFiniteType p]
    [AlgebraicGeometry.IsIntegral X] {n : ℕ}
    (hdim : topologicalKrullDim X = (n : WithBot ℕ∞))
    [AlgebraicGeometry.IsIntegral (normalizationSchemeOverField k p)] :
    topologicalKrullDim (normalizationSchemeOverField k p) = (n : WithBot ℕ∞) := by
  let c : X ⟶ (fieldChowSituation k).S := p
  have _ : LocallyOfFiniteType c := inferInstanceAs (LocallyOfFiniteType p)
  set Xν := normalizationSchemeOverField k p
  set ν : Xν ⟶ X := normalizationOverField k p
  have _ : IsDominant ν := isDominant_normalizationOverField k p
  have _ : IsFinite ν := isFinite_normalizationOverField k p
  have _ : LocallyOfFiniteType (ν ≫ c) := inferInstance
  have hbir : IsBirational ν :=
    Scheme.isBirational_normalization X
      (finite_irreducibleComponents_of_locallyOfFiniteType k p)
  have hgen : ν.base (genericPoint Xν) = genericPoint X :=
    ((tfae_isDominant_of_isIntegral ν).out 1 2).mp (inferInstance : IsDominant ν)
  have _ := isIso_stalkMap_genericPoint_of_isBirational ν hbir
  have _ : IsIso (ν.residueFieldMap (genericPoint Xν)) :=
    isIso_residueFieldMap_of_isIso_stalkMap ν (genericPoint Xν)
  have hrel : relativeDimension (fieldChowSituation k).dimensionFunction (ν ≫ c)
      (genericPoint Xν) =
      relativeDimension (fieldChowSituation k).dimensionFunction c (ν.base (genericPoint Xν)) :=
    relativeDimension_comp_of_bijective_residueFieldMap _ ν c (genericPoint Xν)
      (ConcreteCategory.bijective_of_isIso _)
  rw [topologicalKrullDim_eq_relativeDimension_toNat (fieldChowSituation k) (fun _ _ ↦ rfl)
      (ν ≫ c) (𝟙 Xν) (genericPoint Xν)
      ((IrreducibleSpace.isIrreducible_univ Xν).isGenericPoint_genericPoint isClosed_univ),
    show ((𝟙 Xν) : Xν ⟶ Xν).base (genericPoint Xν) = genericPoint Xν from rfl, hrel, hgen,
    relativeDimension_fieldChowSituation_genericPoint c hdim]
  simp

/-! ### Stacks 02RU -/

/-- **Stacks Project, Tag 02RU.** Let `X` be an integral scheme of dimension one, proper over a
field `k`. Then the degree of the principal divisor of a nonzero rational function `f` on `X`
vanishes:

  `∑_{x ∈ X} ord_x(f) · [κ(x) : k] = 0`.

The normalization `ν : X^ν ⟶ X` is a proper dominant birational morphism from a normal curve, so
the normal case applies to the image `F` of `f` in `R(X^ν)`, and the norm formula of Stacks 02RT
identifies `deg div_{X^ν}(F)` with `deg div_X(Nm(F)) = deg div_X(f)`. -/
@[stacks 02RU "the displayed sum"]
theorem principalDivisorDegree_eq_zero (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [IsCurve k (X ↘ AlgebraicGeometry.Spec (.of k))]
    [IsProper (X ↘ AlgebraicGeometry.Spec (.of k))] [IsLocallyNoetherian X]
    (f : X.functionField) (hf : f ≠ 0) :
    principalDivisorDegree (X ↘ AlgebraicGeometry.Spec (.of k)) f = 0 := by
  set p : X ⟶ AlgebraicGeometry.Spec (.of k) := X ↘ AlgebraicGeometry.Spec (.of k)
  have hdim : topologicalKrullDim X = ((1 : ℕ) : WithBot ℕ∞) :=
    IsCurve.topologicalKrullDim_eq_one (k := k) (f := p)
  -- the structure morphism of `X`, read over the base of the situation
  let c : X ⟶ (fieldChowSituation k).S := p
  have _ : IsProper c := inferInstanceAs (IsProper p)
  have hcY : schemeDeltaDimension (fieldChowSituation k) c = ((1 : ℤ) : EInt) :=
    schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq c hdim
  -- the normalization
  set Xν := normalizationSchemeOverField k p
  set ν : Xν ⟶ X := normalizationOverField k p
  have _ : IsFinite ν := isFinite_normalizationOverField k p
  have _ : IsDominant ν := isDominant_normalizationOverField k p
  have _ : IsVariety k (ν ≫ p) := isVariety_normalizationOverField k p
  have _ : IsProper (ν ≫ p) := isProper_normalizationOverField_comp k p
  have _ : IsNormal Xν :=
    Scheme.isNormal_normalizationScheme X
      (finite_irreducibleComponents_of_locallyOfFiniteType k p)
  have hνdim : topologicalKrullDim Xν = ((1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_normalizationSchemeOverField p hdim
  let _ : Xν.Over (AlgebraicGeometry.Spec (.of k)) := ⟨ν ≫ p⟩
  have _ : IsCurve k (Xν ↘ AlgebraicGeometry.Spec (.of k)) :=
    { toIsVariety := inferInstanceAs (IsVariety k (ν ≫ p))
      topologicalKrullDim_eq_one := hνdim }
  have _ : IsProper (Xν ↘ AlgebraicGeometry.Spec (.of k)) :=
    inferInstanceAs (IsProper (ν ≫ p))
  have _ : IsLocallyNoetherian Xν := LocallyOfFiniteType.isLocallyNoetherian (ν ≫ p)
  -- the function field of the normalization is that of `X`
  let _ : Algebra X.functionField Xν.functionField := (dominantFunctionFieldMap ν).toAlgebra
  have hbijff : Function.Bijective (algebraMap X.functionField Xν.functionField) :=
    bijective_dominantFunctionFieldMap_of_isBirational ν
      (Scheme.isBirational_normalization X
        (finite_irreducibleComponents_of_locallyOfFiniteType k p))
  have hFne : algebraMap X.functionField Xν.functionField f ≠ 0 :=
    (map_ne_zero_iff _ hbijff.1).2 hf
  have hνX : schemeDeltaDimension (fieldChowSituation k) (ν ≫ c) = ((1 : ℤ) : EInt) := by
    have _ : LocallyOfFiniteType (ν ≫ c) := inferInstance
    exact schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq (ν ≫ c) hνdim
  -- the norm formula of Stacks 02RT
  have hnorm := principalDivisorDegree_norm (fieldChowSituation k)
    (fieldChowSituation_dimensionFunction_eq_zero k) c ν hνX hcY
    (algebraMap X.functionField Xν.functionField f) hFne
  rw [norm_algebraMap_of_bijective hbijff f] at hnorm
  -- and Stacks 02RU for the normalization, which is normal
  exact hnorm.symm.trans (principalDivisorDegree_eq_zero_of_isNormal k Xν
    (algebraMap X.functionField Xν.functionField f) hFne)

/-- **Stacks Project, Tag 02RU**, in its cycle form: the proper pushforward to `Spec k` of the
principal divisor of a nonzero rational function on a proper integral curve vanishes. -/
@[stacks 02RU "the pushforward of the principal divisor"]
theorem properPushforward_principalDivisorCycle_eq_zero_of_isCurve (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [IsCurve k (X ↘ AlgebraicGeometry.Spec (.of k))]
    [IsProper (X ↘ AlgebraicGeometry.Spec (.of k))] [IsLocallyNoetherian X]
    (c : X ⟶ (fieldChowSituation k).S) [IsProper c]
    (hc : c = X ↘ AlgebraicGeometry.Spec (.of k))
    (hdim : schemeDeltaDimension (fieldChowSituation k) c = ((1 : ℤ) : EInt))
    (f : X.functionField) (hf : f ≠ 0) :
    properPushforward (fieldChowSituation k) c (𝟙 (fieldChowSituation k).S) c
        (Category.comp_id c) 0
      (principalDivisorCycle (fieldChowSituation k) c hdim f) = 0 := by
  refine (properPushforward_principalDivisorCycle_eq_zero_iff (fieldChowSituation k)
    (fieldChowSituation_dimensionFunction_eq_zero k) c hdim f).mpr ?_
  rw [hc]
  exact principalDivisorDegree_eq_zero k X f hf

end Stacks.Chow

end
