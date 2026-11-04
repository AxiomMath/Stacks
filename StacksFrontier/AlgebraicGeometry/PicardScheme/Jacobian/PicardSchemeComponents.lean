module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardSchemeDegree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CurveBridges

/-!
# The degree components of a Picard scheme over a field are translates of `P⁰`

Let `P` represent the rigidified Picard functor of a curve over a field `k`. Translation by a
`k`-rational point `r` of `P` whose class has degree `d'` carries the component `P^d` onto
`P^{d+d'}`, since the class classified by `a · r` is the sum of the classes. So every component
`P^d` is isomorphic over `k` to `P⁰`, as used in the proof of [Stacks, Tag 0BA0] (1).

## Main results

* `Stacks.RigidifiedPicard.degreeLocusIsoOfPoint` — `P^d ≅ P^{d+d'}` over `k`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.RigidifiedPicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Flat f]
  [LocallyOfFinitePresentation f] [IsProper f] [LocallyOfFiniteType f]
  (hdim : ∀ s : Spec (.of k), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (P : Grp (Over (Spec (.of k))))
  (e : yonedaGrp.obj P ≅ functor f σ hσ)

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [LocallyOfFiniteType f] in
/-- The class classified by a translate is the sum of the classes. -/
theorem classOfElt_comp_grpTranslate {T : Over (Spec (.of k))} (a : T ⟶ P.X)
    (r : Over.mk (𝟙 (Spec (.of k))) ⟶ P.X) :
    classOfElt f σ hσ (homElt f σ hσ P e (a ≫ grpTranslate P r)) =
      Stacks.Picard.schemePullbackClass (bcMap f (grpToBase T))
        (classOfElt f σ hσ (homElt f σ hσ P e r)) + classOfElt f σ hσ (homElt f σ hσ P e a) := by
  rw [comp_grpTranslate, homElt_mul, classOfElt_mul, homElt_comp]
  congr 1
  exact smallEquiv_smallSchemePullbackClassHom _ _

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- The degree of a translate is the sum of the degrees. -/
theorem degree_comp_grpTranslate {T : Over (Spec (.of k))} (a : T ⟶ P.X)
    (r : Over.mk (𝟙 (Spec (.of k))) ⟶ P.X) (t : T.left) :
    relativeInvertibleDegreeHomAt (bcProj f T) (topologicalKrullDim_fiber_bcProj_le f hdim T) t
        (classOfElt f σ hσ (homElt f σ hσ P e (a ≫ grpTranslate P r))) =
      relativeInvertibleDegreeHomAt (bcProj f (Over.mk (𝟙 (Spec (.of k)))))
          (topologicalKrullDim_fiber_bcProj_le f hdim _) (T.hom t)
          (classOfElt f σ hσ (homElt f σ hσ P e r)) +
        relativeInvertibleDegreeHomAt (bcProj f T) (topologicalKrullDim_fiber_bcProj_le f hdim T) t
          (classOfElt f σ hσ (homElt f σ hσ P e a)) := by
  rw [classOfElt_comp_grpTranslate, map_add]
  congr 1
  exact relativeInvertibleDegreeHomAt_schemePullbackClass_of_isPullback
    (bcMap_isPullback_proj f (grpToBase T)) _ _ t _

variable {d' : ℤ} (r : Over.mk (𝟙 (Spec (.of k))) ⟶ P.X)
  (hr : ∀ s, relativeInvertibleDegreeHomAt (bcProj f (Over.mk (𝟙 (Spec (.of k)))))
    (topologicalKrullDim_fiber_bcProj_le f hdim _) s (classOfElt f σ hσ (homElt f σ hσ P e r)) = d')

include hr in
/-- Translation by `r` maps `P^d` into `P^{d+d'}`. -/
theorem exists_translate_degreeLocus (d : ℤ) :
    ∃ τ : degreeLocusOver f hdim σ hσ P e d ⟶ degreeLocusOver f hdim σ hσ P e (d + d'),
      τ ≫ degreeLocusι f hdim σ hσ P e (d + d') =
        degreeLocusι f hdim σ hσ P e d ≫ grpTranslate P r := by
  refine exists_lift_degreeLocus f hdim σ hσ P e _ _ fun t => ?_
  show relativeInvertibleDegreeHomAt _ _ t (classOfElt f σ hσ (homElt f σ hσ P e
    (degreeLocusι f hdim σ hσ P e d ≫ grpTranslate P r))) = _
  have := (range_subset_degreeLocus_iff f hdim σ hσ P e (degreeLocusι f hdim σ hσ P e d) d).1
    (by
      show Set.range (degreeLocus f hdim σ hσ P e d).ι.base ⊆ _
      rw [Scheme.Opens.range_ι]) t
  rw [degree_comp_grpTranslate f hdim σ hσ P e, hr, add_comm]
  exact congrArg (· + d') this

omit [Flat f] [LocallyOfFinitePresentation f] in
include hr in
/-- The class of `r⁻¹` has degree `-d'`. -/
theorem degree_inv (s : (Over.mk (𝟙 (Spec (.of k)))).left) :
    relativeInvertibleDegreeHomAt (bcProj f (Over.mk (𝟙 (Spec (.of k)))))
      (topologicalKrullDim_fiber_bcProj_le f hdim _) s (classOfElt f σ hσ (homElt f σ hσ P e r⁻¹)) =
      -d' := by
  rw [homElt_inv, classOfElt_inv, map_neg, hr]

/-- The degree of a morphism to `P` landing in `P^d` is `d`. -/
theorem degree_of_degreeLocus {T : Over (Spec (.of k))} (d : ℤ)
    (a : T ⟶ degreeLocusOver f hdim σ hσ P e d) (t : T.left) :
    relativeInvertibleDegreeHomAt (bcProj f T) (topologicalKrullDim_fiber_bcProj_le f hdim T) t
      (classOfElt f σ hσ (homElt f σ hσ P e (a ≫ degreeLocusι f hdim σ hσ P e d))) = d :=
  (range_subset_degreeLocus_iff f hdim σ hσ P e _ d).1 (by
    rintro _ ⟨x, rfl⟩
    rw [← Scheme.Opens.range_ι]
    exact ⟨a.left x, rfl⟩) t

include hr in
/-- **Translation by a rational point of degree `d'` is an isomorphism `P^d ≅ P^{d+d'}` over
`k`.** -/
theorem nonempty_degreeLocus_iso (d : ℤ) :
    Nonempty (degreeLocusOver f hdim σ hσ P e d ≅ degreeLocusOver f hdim σ hσ P e (d + d')) := by
  obtain ⟨τ, hτ⟩ := exists_translate_degreeLocus f hdim σ hσ P e r hr d
  obtain ⟨τ', hτ'⟩ := exists_lift_degreeLocus f hdim σ hσ P e
    (degreeLocusι f hdim σ hσ P e (d + d') ≫ grpTranslate P r⁻¹) d fun t => by
      show relativeInvertibleDegreeHomAt _ _ t (classOfElt f σ hσ (homElt f σ hσ P e
        (degreeLocusι f hdim σ hσ P e (d + d') ≫ grpTranslate P r⁻¹))) = d
      rw [degree_comp_grpTranslate f hdim σ hσ P e, degree_inv f hdim σ hσ P e r hr]
      have := degree_of_degreeLocus f hdim σ hσ P e (d + d') (𝟙 _) t
      rw [Category.id_comp] at this
      rw [this]; ring
  have hmono : ∀ d₀, Mono (degreeLocusι f hdim σ hσ P e d₀) := fun d₀ =>
    Over.mono_of_mono_left _
  refine ⟨⟨τ, τ', ?_, ?_⟩⟩
  · rw [← cancel_mono (degreeLocusι f hdim σ hσ P e d), Category.assoc, hτ', ← Category.assoc, hτ,
      Category.assoc, grpTranslate_comp_grpTranslate, inv_mul_cancel, grpTranslate_one,
      Category.comp_id, Category.id_comp]
  · rw [← cancel_mono (degreeLocusι f hdim σ hσ P e (d + d')), Category.assoc, hτ,
      ← Category.assoc, hτ', Category.assoc, grpTranslate_comp_grpTranslate, mul_inv_cancel,
      grpTranslate_one, Category.comp_id, Category.id_comp]

end Stacks.RigidifiedPicard

end
