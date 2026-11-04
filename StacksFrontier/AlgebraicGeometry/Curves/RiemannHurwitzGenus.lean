module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerDegreeOne
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.RiemannHurwitz
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothBundle
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.PointwiseEtale
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PointClosureAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorTwistDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension

/-!
# The degree of the differentials of a generically étale morphism of curves

Let `f : X ⟶ Y` be a morphism of smooth proper curves over a field `k` satisfying the equivalent
conditions of [Stacks, Tag 0C1C], and let `R ⊆ X` be the effective Cartier divisor cut out by the
different of `f`. The discussion of [Stacks, Section 0C1B] computes

`deg(Ω_{X/k}) = deg(f^*Ω_{Y/k} ⊗ 𝒪_X(R)) = deg(f) · deg(Ω_{Y/k}) + deg(R)`,

and [Stacks, Tag 0C1D] then reads both degrees of differentials as `2g - 2` by
[Stacks, Tag 0C1A]. This file proves the displayed computation in full, and the Riemann–Hurwitz
formula of [Stacks, Tag 0C1D] from the two instances of the degree formula of 0C1A.

## Main results

* `AlgebraicGeometry.isInvertible_relativeDifferentials_of_isCurve`: `Ω_{X/k}` is invertible on a
  smooth curve, so that its degree `AlgebraicGeometry.invertibleCurveDegree` is defined.
* `AlgebraicGeometry.isEffectiveCartierDivisor_kaehlerDifferent_of_exists_etale_comp_ι`: the
  different of a morphism of smooth curves which is étale on a nonempty open cuts out an effective
  Cartier divisor.
* `AlgebraicGeometry.invertibleCurveDegree_relativeDifferentials_eq_degreeOver_mul_add`:
  `deg(Ω_{X/k}) = deg(f) · deg(Ω_{Y/k}) + deg(R)`.
* `AlgebraicGeometry.two_mul_genus_sub_two_eq_of_invertibleCurveDegree_relativeDifferentials`:
  `2g_X - 2 = (2g_Y - 2) · deg(f) + deg(R)` once `deg(Ω_{X/k}) = 2g_X - 2` and
  `deg(Ω_{Y/k}) = 2g_Y - 2`.

## Implementation notes

The condition of [Stacks, Tag 0C1C] used is (4), étaleness on a nonempty open. It gives
étaleness at the generic point of `X`, which is the only associated point of `X`; that is the
hypothesis under which [Stacks, Tag 0BWJ] makes `R` an effective Cartier divisor and gives the
bundle identity `f^*Ω^1_{Y/k} ⊗ 𝒪_X(R) ≅ Ω^1_{X/k}`
(`Stacks.Discriminant.nonempty_tensorIso_invertibleSheaf_kaehlerDifferent_of_etaleAt`). The
sheaves there are the first exterior powers of the differentials, identified with the
differentials by the degree-one generator of the exterior algebra.

`R` is the closed subscheme of the Kähler different of [Stacks, Tag 0BVW], as in the
registrations of [Stacks, Tag 0BWJ]; it is the different of [Stacks, Tag 0BW4] by
[Stacks, Tag 0BWG]. Its degree is `dim_k Γ(R, 𝒪_R)` and `deg(f) = [k(X) : k(Y)]` is
`AlgebraicGeometry.degreeOver`, the degree of [Stacks, Tag 0AYZ].

The degree identity is [Stacks, Tag 0AYY] for the twist of `f^*Ω_{Y/k}` by `𝒪_X(R)` followed by
[Stacks, Tag 0AYZ] for the pullback; the latter needs `f` nonconstant, which holds because `f`
is dominant and proper, hence surjective onto the positive-dimensional `Y`.

## References

* [Stacks Project, Section 0C1B](https://stacks.math.columbia.edu/tag/0C1B)
* [Stacks Project, Tag 0C1D](https://stacks.math.columbia.edu/tag/0C1D)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The sheaf of differentials of a smooth curve over a field is invertible. -/
instance isInvertible_relativeDifferentials_of_isCurve {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsCurve k p] [Smooth p] :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (Scheme.Hom.relativeDifferentials p) :=
  haveI := smoothOfRelativeDimension_one_of_isCurve _ p
  haveI := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials p 1
  Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace _

/-- A morphism which is étale on a nonempty open of an irreducible source is étale at the generic
point of the source. -/
theorem etaleAt_genericPoint_of_exists_etale_comp_ι {X Y : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ Y) (hgen : ∃ U : X.Opens, Nonempty U ∧ Etale (U.ι ≫ f)) :
    EtaleAt f (genericPoint X) := by
  obtain ⟨U, hU, hEt⟩ := hgen
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  exact Stacks.FundamentalGroup.ExtendedEtaleFold.etaleAt_of_etaleAt_isOpenImmersion_comp U.ι f
    ⟨_, hη⟩ ((etale_iff_forall_etaleAt _).mp hEt _)

/-- A morphism out of an integral locally Noetherian scheme which is étale on a nonempty open is
étale at the associated points of its source, the generic point being the only one. -/
theorem etaleAt_of_mem_schemeAssociatedPoints_of_exists_etale_comp_ι {X Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] (f : X ⟶ Y)
    (hgen : ∃ U : X.Opens, Nonempty U ∧ Etale (U.ι ≫ f)) :
    ∀ x ∈ Stacks.Divisors.schemeAssociatedPoints X, EtaleAt f x := by
  rw [schemeAssociatedPoints_eq_singleton_genericPoint X]
  rintro x rfl
  exact etaleAt_genericPoint_of_exists_etale_comp_ι f hgen

section RiemannHurwitz

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k))
  (pY : Y ⟶ Spec (.of k)) [IsCurve k pX] [IsCurve k pY] [Smooth pX] [Smooth pY]
  (f : X ⟶ Y)

/-- A morphism of smooth curves which is étale on a nonempty open is dominant: this is the
implication (4) ⟹ (5) of [Stacks, Tag 0C1C]. -/
theorem isDominant_of_exists_etale_comp_ι (hf : f ≫ pY = pX)
    (hgen : ∃ U : X.Opens, Nonempty U ∧ Etale (U.ι ≫ f)) : IsDominant f := by
  obtain ⟨h, -⟩ := ((genericallyEtale_tfae pX pY f hf).out 4 5).mp hgen
  exact h

/-- The ramification divisor: for a morphism of smooth curves over a field which is étale on a
nonempty open, the closed subscheme `R ⊆ X` cut out by the (Kähler) different of `f` is an
effective Cartier divisor ([Stacks, Tag 0BWJ]). -/
theorem isEffectiveCartierDivisor_kaehlerDifferent_of_exists_etale_comp_ι (hf : f ≫ pY = pX)
    (hgen : ∃ U : X.Opens, Nonempty U ∧ Etale (U.ι ≫ f)) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isCurve_comp k pX pY f hf
    Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Discriminant.kaehlerDifferent f) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  have hét := etaleAt_of_mem_schemeAssociatedPoints_of_exists_etale_comp_ι f hgen
  subst hf
  have := smoothOfRelativeDimension_one_of_isCurve _ pY
  have := smoothOfRelativeDimension_one_of_isCurve _ (f ≫ pY)
  exact Stacks.Discriminant.isEffectiveCartierDivisor_kaehlerDifferent_of_etaleAt pY f 1 hét

/-- A morphism of curves over a field which is étale on a nonempty open is not constant. -/
theorem not_constant_of_exists_etale_comp_ι [IsProper pX] [IsProper pY] (hf : f ≫ pY = pX)
    (hgen : ∃ U : X.Opens, Nonempty U ∧ Etale (U.ι ≫ f)) :
    ¬ ∃ y : Y, ∀ x : X, f.base x = y := by
  rintro ⟨y, hy⟩
  have := isDominant_of_exists_etale_comp_ι pX pY f hf hgen
  have : IsProper (f ≫ pY) := hf ▸ inferInstance
  have : IsProper f := IsProper.of_comp (f := f) (g := pY)
  have hsurj : Function.Surjective f.base := Surjective.surj
  have : Subsingleton Y := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨x', rfl⟩ := hsurj b
    rw [hy, hy]⟩
  have h1 := IsCurve.topologicalKrullDim_eq_one pY
  have h0 := topologicalKrullDim_zero_of_discreteTopology Y
  rw [h1] at h0
  exact absurd h0 (by decide)

/-- **The degree of the differentials of a generically étale morphism of smooth proper curves.**
Let `f : X ⟶ Y` be a morphism of smooth proper curves over a field `k` which is étale on a
nonempty open (one of the equivalent conditions of [Stacks, Tag 0C1C]) and let `R ⊆ X` be the
effective Cartier divisor cut out by the different of `f`. Then

`deg(Ω_{X/k}) = deg(f) · deg(Ω_{Y/k}) + deg(R)`,

where `deg(f) = [k(X) : k(Y)]` and `deg(R) = dim_k Γ(R, 𝒪_R)`. This is the computation of
[Stacks, Tag 0C1D] before the degrees of the differentials are evaluated by [Stacks, Tag 0C1A].

[Stacks, Tag 0BWJ] gives `f^*Ω_{Y/k} ⊗ 𝒪_X(R) ≅ Ω_{X/k}`; [Stacks, Tag 0AYY] evaluates the
degree of the twist by `𝒪_X(R)` and [Stacks, Tag 0AYZ] the degree of the pullback. -/
theorem invertibleCurveDegree_relativeDifferentials_eq_degreeOver_mul_add
    [IsProper pX] [IsProper pY] (hf : f ≫ pY = pX)
    (hgen : ∃ U : X.Opens, Nonempty U ∧ Etale (U.ι ≫ f)) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isCurve_comp k pX pY f hf
    letI : IsDominant f := isDominant_of_exists_etale_comp_ι pX pY f hf hgen
    letI : Algebra k Γ((Stacks.Discriminant.kaehlerDifferent f).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        ((Stacks.Discriminant.kaehlerDifferent f).subschemeι ≫ pX).appTop).hom.toAlgebra
    invertibleCurveDegree k pX (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := pX)))
        (Scheme.Hom.relativeDifferentials pX) =
      (degreeOver f : ℤ) *
          invertibleCurveDegree k pY (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := pY)))
            (Scheme.Hom.relativeDifferentials pY) +
        (Module.finrank k Γ((Stacks.Discriminant.kaehlerDifferent f).subscheme, ⊤) : ℤ) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  have hét := etaleAt_of_mem_schemeAssociatedPoints_of_exists_etale_comp_ι f hgen
  have hnc := not_constant_of_exists_etale_comp_ι pX pY f hf hgen
  have hcart := isEffectiveCartierDivisor_kaehlerDifferent_of_exists_etale_comp_ι pX pY f hf hgen
  subst hf
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f pY
  have := smoothOfRelativeDimension_one_of_isCurve _ pY
  have := smoothOfRelativeDimension_one_of_isCurve _ (f ≫ pY)
  have hΩY := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials pY 1
  have hΩX := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials (f ≫ pY) 1
  have hPΩY := isFiniteLocallyFreeOfRank_pullback f (Scheme.Hom.relativeDifferentials pY) 1
  obtain ⟨e⟩ :=
    Stacks.Discriminant.nonempty_tensorIso_invertibleSheaf_kaehlerDifferent_of_etaleAt pY f 1 hét
  -- `Ω ≅ Ω¹` on both curves
  let eY := (_root_.SheafOfModules.algebras _
    (Scheme.Hom.relativeDifferentials pY)).exteriorGeneratorIso
  let eX := (_root_.SheafOfModules.algebras _
    (Scheme.Hom.relativeDifferentials (f ≫ pY))).exteriorGeneratorIso
  -- `f^*Ω_{Y/k} ⊗ 𝒪_X(R) ≅ Ω_{X/k}`
  let e' : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
        ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials pY))).obj
          (Stacks.Divisors.invertibleSheaf' (Stacks.Discriminant.kaehlerDifferent f))) ≅
      Scheme.Hom.relativeDifferentials (f ≫ pY) :=
    Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMapIso (X := X.toRingedSpace)
    ((Scheme.Modules.pullback f).mapIso eY) (Iso.refl _) ≪≫ e ≪≫ eX.symm
  have hdimX : topologicalKrullDim X ≤ 1 :=
    le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f ≫ pY))
  have hT := isFiniteLocallyFreeOfRank_tensorSheaf_invertibleSheaf
    (Stacks.Discriminant.kaehlerDifferent f) ((Scheme.Modules.pullback f).obj
      (Scheme.Hom.relativeDifferentials pY)) 1
  have h0AYY := (isFinite_and_curveDegree_tensorSheaf_invertibleSheaf k (f ≫ pY) hdimX
    (Stacks.Discriminant.kaehlerDifferent f)
    ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials pY)) 1).2.2
  have h0AYZ := curveDegree_pullback_eq_degreeOver_mul k (f ≫ pY) pY f rfl hnc
    (Scheme.Hom.relativeDifferentials pY) 1
  have hiso := curveDegree_eq_of_iso k (f ≫ pY) hdimX 1 e'
  rw [invertibleCurveDegree_eq_curveDegree, invertibleCurveDegree_eq_curveDegree, ← hiso, h0AYY,
    h0AYZ]
  push_cast
  ring

/-- **Riemann–Hurwitz, from the degree of the differentials.** Let `f : X ⟶ Y` be a morphism of
smooth proper curves over a field `k` which is étale on a nonempty open, and let `R ⊆ X` be the
effective Cartier divisor cut out by the different of `f`. If the differentials of `X` and of
`Y` have degrees `2g_X - 2` and `2g_Y - 2`, then

`2g_X - 2 = (2g_Y - 2) · deg(f) + deg(R)`.

The two hypotheses `hX` and `hY` are the degree formula of [Stacks, Tag 0C1A] for `X` and for
`Y`; with them this is [Stacks, Tag 0C1D]. -/
theorem two_mul_genus_sub_two_eq_of_invertibleCurveDegree_relativeDifferentials
    [IsProper pX] [IsProper pY] (hf : f ≫ pY = pX)
    (hgen : ∃ U : X.Opens, Nonempty U ∧ Etale (U.ι ≫ f))
    (hX : invertibleCurveDegree k pX (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := pX)))
      (Scheme.Hom.relativeDifferentials pX) = 2 * genus pX - 2)
    (hY : invertibleCurveDegree k pY (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := pY)))
      (Scheme.Hom.relativeDifferentials pY) = 2 * genus pY - 2) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isCurve_comp k pX pY f hf
    letI : IsDominant f := isDominant_of_exists_etale_comp_ι pX pY f hf hgen
    letI : Algebra k Γ((Stacks.Discriminant.kaehlerDifferent f).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        ((Stacks.Discriminant.kaehlerDifferent f).subschemeι ≫ pX).appTop).hom.toAlgebra
    2 * (genus pX : ℤ) - 2 =
      (2 * (genus pY : ℤ) - 2) * (degreeOver f : ℤ) +
        (Module.finrank k Γ((Stacks.Discriminant.kaehlerDifferent f).subscheme, ⊤) : ℤ) := by
  have h := invertibleCurveDegree_relativeDifferentials_eq_degreeOver_mul_add pX pY f hf hgen
  rw [hX, hY] at h
  rw [h]
  ring

end RiemannHurwitz

end AlgebraicGeometry

end
