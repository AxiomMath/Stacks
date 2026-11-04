module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardOfCurve
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelBundle.ProjectiveBundle

/-!
# The Picard scheme of a smooth projective curve over a separably closed field (Stacks 0BA0)

[Stacks, Tag 0BA0] in full: `Stacks.RigidifiedPicard.exists_picardScheme_of_abelMorphismSmooth`
with the smoothness of the Abel morphisms of degree `d ≥ 2g - 1`
(`Stacks.RigidifiedPicard.abelMorphismSmooth`) supplied.

## Main results

* `Stacks.RigidifiedPicard.exists_picardScheme` — **[Stacks, Tag 0BA0]**.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.RigidifiedPicard

/-- **[Stacks, Tag 0BA0].** Let `k` be a separably closed field and `X` a smooth projective curve
of genus `g` over `k`. Choosing a rational point `σ`, the Picard functor is represented by a group
scheme `P` (`Pic_{X/k} ≅ Pic_{X/k,σ}`, [Stacks, Tag 0B9Z]), and:
1. `P` is the disjoint union of the open and closed `P^d`, `g`-dimensional smooth proper varieties;
2. the `k`-points of `P^d` are the invertible `𝒪_X`-modules of degree `d`;
3. `P^0` is an open and closed subgroup scheme;
4. for `d ≥ 0` there is the canonical Abel morphism `γ_d : Hilb^d_{X/k} ⟶ P^d`, classifying the
   rigidified class of `𝒪(D_univ)`;
5. `γ_d` is surjective for `d ≥ g` and smooth for `d ≥ 2g - 1`;
6. `γ_g` is birational. -/
@[stacks 0BA0]
theorem exists_picardScheme (k : Type u) [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] (hproj : IsProjectiveMorphism f) :
    haveI : IsProper f := isProper_of_isProjectiveMorphism f hproj
    haveI : GeometricallyIrreducible f := geometricallyIrreducible_of_isCurve_of_isSepClosed k f
    haveI : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve k f
    ∃ (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (P : Grp (Over (Spec (.of k))))
      (e : yonedaGrp.obj P ≅ functor f σ hσ),
      -- (1)
      (∀ d d' : ℤ, d ≠ d' → Disjoint
        (degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d : Set P.X.left)
        (degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d')) ∧
      (⨆ d, degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d = ⊤) ∧
      (∀ d : ℤ,
        IsClopen (degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d :
          Set P.X.left) ∧
        IsProperVariety k
          ((degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d).ι ≫
            P.X.hom) ∧
        SmoothOfRelativeDimension (genus f)
          ((degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d).ι ≫
            P.X.hom) ∧
        topologicalKrullDim
          (degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d) =
            (genus f : WithBot ℕ∞)) ∧
      -- (2)
      (∀ d : ℤ, Set.BijOn (pointClassOf f σ hσ P e)
        {r | Set.range r.left ⊆
          (degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d :
            Set P.X.left)}
        {c | invertibleCurveDegreeHom k f (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
          c = d}) ∧
      -- (3)
      (∃ K : OpenSubgroupScheme P, ∃ i : degreeLocusOver f
          (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e 0 ≅ K.carrier.X,
        degreeLocusι f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e 0 =
          i.hom ≫ K.ι.hom.hom) ∧
      ∀ (H : ℕ → Over (Spec (.of k)))
        (hH : ∀ d, Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) (H d) d),
        -- (4)
        (∀ d : ℕ,
          abelMorphismDegree f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e
              (hH d) ≫
            (degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d).ι =
              (abelMorphismFull f σ hσ (hH d) P e).left ∧
          ∀ {T : Over (Spec (.of k))} (m : T ⟶ H d),
            (e.hom.app (op T)).hom (m ≫ abelMorphismFull f σ hσ (hH d) P e) =
              abelElementFull f σ hσ (hH d) m) ∧
        -- (5), surjectivity
        (∀ d : ℕ, genus f ≤ d → Surjective
          (abelMorphismDegree f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e
            (hH d))) ∧
        -- (5), smoothness
        (∀ d : ℕ, 2 * (genus f : ℤ) - 1 ≤ d → Smooth
          (abelMorphismDegree f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e
            (hH d))) ∧
        -- (6)
        IsBirational (abelMorphismDegree f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ
          P e (hH (genus f))) :=
  exists_picardScheme_of_abelMorphismSmooth k f hproj abelMorphismSmooth

end Stacks.RigidifiedPicard

end
