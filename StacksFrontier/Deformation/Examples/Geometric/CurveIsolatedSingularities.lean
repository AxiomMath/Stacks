module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Geometric.CurveStalkComparison
public import StacksFrontier.Deformation.Examples.Geometric.LocalRingChainTransport

/-!
# Deformations of a curve at its singular points

Let `X` be a separated scheme of finite type over a field `k` of dimension at most one which is
smooth over `k` away from finitely many closed points `p_1, …, p_n`. **Stacks 0DZP** (Lemma
93.16.3) considers the maps of deformation categories
`Def_X ⟶ ∏ Def_{𝒪_{X, p_i}} ⟶ ∏ Def_{𝒪^h_{X, p_i}} ⟶ ∏ Def_{𝒪^∧_{X, p_i}}`
and asserts that the first is smooth and that the second and third are smooth and induce
isomorphisms on tangent spaces.

## Main definitions

* `Deformation.Examples.localRingFunctors`: the first map, the product of the local-ring functors
  of Stacks 0DZM.
* `Deformation.Examples.stalkHenselizationFunctors`: the second map, the product of the
  henselization functors of Stacks 0DYT along the maximal ideals.
* `Deformation.Examples.stalkCompletionFunctors`: the third map, the product of the completion
  functors of Stacks 0DYV applied to the henselizations, read at the completions of the local
  rings themselves through the canonical isomorphism `(𝒪^h)^∧ ≅ 𝒪^∧`.

## Main results

* `Deformation.Examples.isSmooth_localRingFunctors_and_chain`: the first map is smooth, and the
  second and third are smooth and induce isomorphisms on tangent spaces.

## Implementation notes

The two-chart cover `X = U₁ ∪ U₂` with `U₂` affine containing every `p_i` and `U₁` affine
avoiding them is
`Deformation.Examples.exists_affineOpen_cover_avoiding_of_topologicalKrullDim_le_one'`; then `U₁`
and `U₁ ∩ U₂` are smooth over `k`, so Tag 0DZN makes `Def_X ⟶ Def_{U₂} = Def_{P₂}` smooth for
`P₂ = Γ(X, U₂)`, and Tag 0DZF applies to `P₂` at the maximal ideals `𝔪_i` of the points `p_i`.
The passage from `(P₂)_{𝔪_i}` to `𝒪_{X, p_i}` is as follows:

* for the first map, the composite of Tag 0DZN with the first map of Tag 0DZF at `P₂`,
  transported along `(P₂)_{𝔪_i} ≅ 𝒪_{X, p_i}`, is isomorphic to the product of the local-ring
  functors, by `Deformation.Examples.nonempty_iso_localRingDeformationFunctor`;
* for the second and third maps, the maps of Tag 0DZF at the `(P₂)_{𝔪_i}` are conjugate to the
  maps at the `𝒪_{X, p_i}` by transports along ring isomorphisms, by
  `Deformation.Examples.localRingChainAt_conclusions`.

The points are indexed by a finite type `ι` and are assumed pairwise distinct, which is how the
source's list `p_1, …, p_n` of *the* non-smooth points is to be read: with a repeated point the
first map would land in a product with two copies of one factor and could not be smooth.

## References

* [Stacks Project, Tag 0DZP](https://stacks.math.columbia.edu/tag/0DZP)
* [Stacks Project, Tag 0DZF](https://stacks.math.columbia.edu/tag/0DZF)
* [Stacks Project, Tag 0DZN](https://stacks.math.columbia.edu/tag/0DZN)
* [Stacks Project, Tag 0DZM](https://stacks.math.columbia.edu/tag/0DZM)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]


/-- The second component of the morphism `Def_X ⟶ Def_{P₁} × Def_{P₂}` of Tag 0DZN is restriction
to `U₂` followed by the identification `Def_{U₂} = Def_{P₂}` of Tag 0DYX. -/
theorem GluingSituation.toChartProductOfCover_comp_snd (S : GluingSituation Λ k) :
    BasedFunctor.comp (GluingSituation.toChartProductOfCover S)
      (cofiberedProductSnd (ringDeformationCategoryOver Λ k S.P₁)
        (ringDeformationCategoryOver Λ k S.P₂)) =
    BasedFunctor.comp (openRestrictionFunctor S.X S.U₂) (GluingSituation.chartRight S) :=
  rfl

/-! ### The three maps of the chain -/

section Curve

variable (X : Over (Spec (.of k))) {ι : Type u} (p : ι → X.left)

/-- **The first map of the chain of Stacks 0DZP**: take the local ring of a deformation of `X` at
each of the points `p i` (Stacks 0DZM). -/
noncomputable def localRingFunctors :
    letI : ∀ i, Algebra k (X.left.presheaf.stalk (p i)) := fun i => stalkAlgebraOver X (p i)
    BasedFunctor (schemeDeformationCategoryOver Λ k X)
      (piBasedCategory fun i => ringDeformationBasedCategory Λ k (X.left.presheaf.stalk (p i))) :=
  letI : ∀ i, Algebra k (X.left.presheaf.stalk (p i)) := fun i => stalkAlgebraOver X (p i)
  piLift fun i => localRingDeformationFunctor (Λ := Λ) X (p i)

attribute [local instance 100] henselizationAlgebra in
/-- **The second map of the chain of Stacks 0DZP**: henselize each local ring `𝒪_{X, p i}` along
its maximal ideal. -/
noncomputable def stalkHenselizationFunctors :
    letI : ∀ i, Algebra k (X.left.presheaf.stalk (p i)) := fun i => stalkAlgebraOver X (p i)
    BasedFunctor
      (piBasedCategory fun i => ringDeformationBasedCategory Λ k (X.left.presheaf.stalk (p i)))
      (piBasedCategory fun i => ringDeformationBasedCategory Λ k
        (henselization (X.left.presheaf.stalk (p i))
          (IsLocalRing.maximalIdeal (X.left.presheaf.stalk (p i))) : Type u)) :=
  letI : ∀ i, Algebra k (X.left.presheaf.stalk (p i)) := fun i => stalkAlgebraOver X (p i)
  henselizationFunctorsAt (Λ := Λ) (k := k) fun i => X.left.presheaf.stalk (p i)

attribute [local instance 100] henselizationAlgebra in
/-- **The third map of the chain of Stacks 0DZP**: complete each henselized local ring, and read
the result as the completion `𝒪^∧_{X, p i}` of the local ring. -/
noncomputable def stalkCompletionFunctors [IsLocallyNoetherian X.left] :
    letI : ∀ i, Algebra k (X.left.presheaf.stalk (p i)) := fun i => stalkAlgebraOver X (p i)
    BasedFunctor
      (piBasedCategory fun i => ringDeformationBasedCategory Λ k
        (henselization (X.left.presheaf.stalk (p i))
          (IsLocalRing.maximalIdeal (X.left.presheaf.stalk (p i))) : Type u))
      (piBasedCategory fun i => ringDeformationBasedCategory Λ k
        (AdicCompletion (IsLocalRing.maximalIdeal (X.left.presheaf.stalk (p i)))
          (X.left.presheaf.stalk (p i)))) :=
  letI : ∀ i, Algebra k (X.left.presheaf.stalk (p i)) := fun i => stalkAlgebraOver X (p i)
  completedLocalRingFunctorsAt (Λ := Λ) (k := k) fun i => X.left.presheaf.stalk (p i)

attribute [local instance 100] henselizationAlgebra in
/-- Let `X` be a separated scheme of finite type over `k` with `dim X ≤ 1`, and let `p_i` be
finitely many distinct closed points of `X` outside of which `X → Spec k` is smooth. In the chain
of deformation categories
`Def_X ⟶ ∏ Def_{𝒪_{X, p_i}} ⟶ ∏ Def_{𝒪^h_{X, p_i}} ⟶ ∏ Def_{𝒪^∧_{X, p_i}}`
the first map is smooth, and the second and third maps are smooth and induce isomorphisms
(bijections of `k`-vector spaces, by Stacks 06IJ) on tangent spaces. -/
@[stacks 0DZP]
theorem isSmooth_localRingFunctors_and_chain [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (hdim : topologicalKrullDim (X.left : Type u) ≤ 1) [Finite ι]
    (hinj : Function.Injective p) (hclosed : ∀ i, IsClosed ({p i} : Set X.left))
    (hsm : ∀ x : X.left, x ∉ Set.range p → x ∈ X.hom.smoothLocus) :
    letI : ∀ i, Algebra k (X.left.presheaf.stalk (p i)) := fun i => stalkAlgebraOver X (p i)
    haveI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    IsSmooth (localRingFunctors (Λ := Λ) X p) ∧
      IsSmooth (stalkHenselizationFunctors (Λ := Λ) X p) ∧
      Function.Bijective (differential
        (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
          fun i => X.left.presheaf.stalk (p i))
        (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
          fun i => (henselization (X.left.presheaf.stalk (p i))
            (IsLocalRing.maximalIdeal (X.left.presheaf.stalk (p i))) : Type u))
        (stalkHenselizationFunctors (Λ := Λ) X p)) ∧
      IsSmooth (stalkCompletionFunctors (Λ := Λ) X p) ∧
      Function.Bijective (differential
        (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
          fun i => (henselization (X.left.presheaf.stalk (p i))
            (IsLocalRing.maximalIdeal (X.left.presheaf.stalk (p i))) : Type u))
        (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
          fun i => AdicCompletion (IsLocalRing.maximalIdeal (X.left.presheaf.stalk (p i)))
            (X.left.presheaf.stalk (p i)))
        (stalkCompletionFunctors (Λ := Λ) X p)) := by
  classical
  let : ∀ i, Algebra k (X.left.presheaf.stalk (p i)) := fun i => stalkAlgebraOver X (p i)
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  obtain ⟨U₁, U₂, hU₁, hU₂, hcover, hEU₂, hdisj⟩ :=
    exists_affineOpen_cover_avoiding_of_topologicalKrullDim_le_one' X.hom hdim
      (Set.finite_range p) (Set.iUnion_singleton_eq_range p ▸ isClosed_iUnion_of_finite hclosed)
  have hU₁sm : U₁ ≤ X.hom.smoothLocus := fun x hx =>
    hsm x fun hxE => Set.disjoint_left.mp hdisj hxE hx
  have : X.left.IsSeparated :=
    Stacks.HQuasiProjectiveDimensionOne.isSeparated_of_isSeparated_over_field X.hom
  have : IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X.left)) := inferInstance
  have hU₁₂ : IsAffineOpen (U₁ ⊓ U₂) := hU₁.inf hU₂
  let S := gluingSituationOfAffineCover Λ X hU₁ hU₂ hU₁₂ hcover
  let := sectionsAlgebra X.hom U₁
  let := sectionsAlgebra X.hom U₂
  let := sectionsAlgebra X.hom (U₁ ⊓ U₂)
  have hP₁₂ : Algebra.Smooth k S.P₁₂ :=
    smooth_sectionsAlgebra_of_le_smoothLocus X.hom hU₁₂ (inf_le_left.trans hU₁sm)
  have hP₁sm : Algebra.Smooth k S.P₁ := smooth_sectionsAlgebra_of_le_smoothLocus X.hom hU₁ hU₁sm
  have hP₁ : IsLocalCompleteIntersection k S.P₁ := isLocalCompleteIntersection_of_smooth k S.P₁
  have hC := GluingSituation.isSmooth_toChartProductOfCover_comp_snd S hP₁₂ hP₁
  rw [GluingSituation.toChartProductOfCover_comp_snd] at hC
  have : Algebra.FiniteType k Γ(X.left, U₂) := finiteType_sectionsAlgebra X.hom hU₂
  let x : ι → U₂ := fun i => ⟨p i, hEU₂ ⟨i, rfl⟩⟩
  let m : ι → PrimeSpectrum Γ(X.left, U₂) := fun i => hU₂.primeIdealOf (x i)
  have hmax : ∀ i, (m i).asIdeal.IsMaximal := fun i =>
    hU₂.primeIdealOf_isMaximal_of_isClosed (x i) (hclosed i)
  have hminj : Function.Injective m := fun i j hij =>
    hinj (congrArg Subtype.val (primeIdealOf_injective hU₂ hij))
  have hmsm : ∀ q : PrimeSpectrum Γ(X.left, U₂), ¬ Algebra.IsSmoothAt k q.asIdeal →
      ∃ i, m i = q := by
    intro q hq
    obtain ⟨y, rfl⟩ := exists_primeIdealOf_eq hU₂ q
    obtain ⟨i, hi⟩ : (y : X.left) ∈ Set.range p :=
      Classical.byContradiction fun hy => hq (isSmoothAt_primeIdealOf X.hom hU₂ y (hsm _ hy))
    exact ⟨i, congrArg hU₂.primeIdealOf (Subtype.ext hi)⟩
  have hL := isSmooth_localizationFunctors (Λ := Λ) m hmax hminj hmsm
  have hT : IsSmooth (piMap fun i => ringDeformationTransport (Λ := Λ)
      (localRingAtEquivStalk X hU₂ (x i)) (localRingAtEquivStalk_algebraMap X hU₂ (x i))) :=
    piMap_isSmooth_of_components _ fun i => isSmooth_ringDeformationTransport _ _
  have hchain := localRingChainAt_conclusions (Λ := Λ) m hmax hminj hmsm
    (fun i => X.left.presheaf.stalk (p i)) (fun i => localRingAtEquivStalk X hU₂ (x i))
    (fun i => localRingAtEquivStalk_algebraMap X hU₂ (x i))
  exact ⟨isSmooth_of_iso (piLiftIsoOfComponents _ _ fun i =>
      (Classical.choice (nonempty_iso_localRingDeformationFunctor (Λ := Λ) X hU₂ (x i)))).symm
    (isSmooth_comp _ _ (isSmooth_comp _ _ hC hL) hT), hchain⟩

end Curve

end Deformation.Examples
