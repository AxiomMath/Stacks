module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelMorphism
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardSchemeStructure
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardZeroAbelianVariety
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SeparableDegreeFibres

/-!
# The Abel morphism `γ_d` is onto `P^d` for `d ≥ g` (Stacks 0BA0 (5), surjectivity)

Let `P` represent the rigidified Picard functor of a proper smooth geometrically irreducible
curve `X` over a field `k` with a rational point, and let `γ_d : Hilb^d_{X/k} ⟶ P` be the Abel
morphism. Every point `y` of the degree-`d` component `P^d` is the image of a point of
`Hilb^d`, as soon as `d ≥ g`: over an algebraic closure `Ω` of `κ(y)`, the class classified by
`y` has degree `d ≥ g` on `X_Ω`, so by Riemann–Roch it is the class of an effective divisor of
degree `d` ([Stacks, Tag 0BA0], proof of (5)), which is an `Ω`-point of `Hilb^d` mapping to `y`.

## Main results

* `Stacks.RigidifiedPicard.degreeLocus_subset_range_abelMorphismFull` — `P^d ⊆ γ_d(Hilb^d)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.RigidifiedPicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
  [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f]
  (hdimX : topologicalKrullDim X ≤ 1)
  (hdim : ∀ s : Spec (.of k), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (P : Grp (Over (Spec (.of k))))
  (e : yonedaGrp.obj P ≅ functor f σ hσ) {d : ℕ} {H : Over (Spec (.of k))}
  (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d)

omit [Smooth f] [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f] in
include hdimX in
/-- The base change of `X` to a field has dimension at most one. -/
theorem topologicalKrullDim_bc_spec_le {Ω : Type u} [Field Ω]
    (g : Spec (.of Ω) ⟶ Spec (.of k)) : topologicalKrullDim (bc f (Over.mk g)) ≤ 1 := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  let : Algebra k Ω := φ.hom.toAlgebra
  exact (topologicalKrullDim_baseChange k Ω (pullback.fst f _) (pullback.snd f _) f
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))).trans_le hdimX

omit [Smooth f] [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f] in
/-- The base change of `X` to a field has the genus of `X`. -/
theorem genus_bc_spec {Ω : Type u} [Field Ω] (g : Spec (.of Ω) ⟶ Spec (.of k)) :
    genus (bcProj f (Over.mk g)) = genus f := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  exact genus_eq_of_isPullback k Ω φ.hom (pullback.fst f _) (pullback.snd f _) f
    (IsPullback.of_hasPullback f _)

include hdimX in
/-- **[Stacks, Tag 0BA0] (5), surjectivity of `γ_d` onto `P^d` for `d ≥ g`.** -/
theorem degreeLocus_subset_range_abelMorphismFull (hd : genus f ≤ d) :
    (degreeLocus f hdim σ hσ P e d : Set P.X.left) ⊆
      Set.range (abelMorphismFull f σ hσ hH P e).left := by
  intro y hy
  set Ω := AlgebraicClosure (P.X.left.residueField y)
  let b₀ : Spec (.of Ω) ⟶ P.X.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (P.X.left.residueField y) Ω)) ≫
      P.X.left.fromSpecResidueField y
  let g : Spec (.of Ω) ⟶ Spec (.of k) := b₀ ≫ P.X.hom
  let b : Over.mk g ⟶ P.X := Over.homMk b₀ rfl
  have : IsIntegral (bc f (Over.mk g)) := isIntegral_bc_spec f g
  have := isIso_globalSections_bc_spec f g
  obtain ⟨t⟩ : Nonempty (Spec (.of Ω)) := inferInstanceAs (Nonempty (PrimeSpectrum Ω))
  have hbt : b₀ t = y := by
    show (Spec.map _ ≫ P.X.left.fromSpecResidueField y).base t = y
    rw [Scheme.Hom.comp_base, TopCat.comp_app, Scheme.fromSpecResidueField_apply]
  have hdim₀ : topologicalKrullDim (bc f (Over.mk g)) ≤ 1 :=
    topologicalKrullDim_bc_spec_le f hdimX g
  have : Subsingleton (Over.mk g).left := inferInstanceAs (Subsingleton (Spec (.of Ω)))
  have hdim' := topologicalKrullDim_fiber_bcProj_le f hdim (Over.mk g)
  set c := classOfElt f σ hσ (homElt f σ hσ P e b)
  have hcd : invertibleCurveDegreeHom Ω (bcProj f (Over.mk g)) hdim₀ c = d := by
    rw [← relativeInvertibleDegreeHomAt_eq_invertibleCurveDegreeHom (bcProj f (Over.mk g)) hdim'
      hdim₀ t]
    exact (range_subset_degreeLocus_iff f hdim σ hσ P e b d).1 (by
      rintro _ ⟨t', rfl⟩
      obtain rfl : t' = t := Subsingleton.elim _ _
      show b₀ t' ∈ _
      rwa [hbt]) t
  have hdeg : (genus (bcProj f (Over.mk g)) : ℤ) ≤
      invertibleCurveDegreeHom Ω (bcProj f (Over.mk g)) hdim₀ c := by
    rw [hcd, genus_bc_spec]; exact_mod_cast hd
  obtain ⟨D, hD, d', hrank, hd', hclass⟩ :=
    exists_isEffectiveCartierDivisor_picardClass_eq Ω (bcProj f (Over.mk g)) hdim₀ c hdeg
  have hdd : d' = d := by rw [hcd] at hd'; exact_mod_cast hd'
  let Z : Stacks.Hilbert.HilbertFamily (Over.mk f) (Over.mk g) d := ⟨D, hdd ▸ hrank⟩
  let m : Over.mk g ⟶ H := hH.family.symm Z
  have hm : m ≫ abelMorphismFull f σ hσ hH P e = b := by
    apply homElt_injective f σ hσ P e
    refine ext_functor f σ hσ ?_
    show classOfElt f σ hσ ((e.hom.app (op _)).hom (m ≫ abelMorphismFull f σ hσ hH P e)) = c
    rw [abelMorphismFull_spec, classOfElt, smallEquiv_abelElementFull, abelNormalized,
      show hH.family m = Z from hH.family.apply_symm_apply Z]
    have h0 : ∀ (q : bc f (Over.mk g) ⟶ X),
        Stacks.Picard.schemePullbackClass q (0 : Stacks.Picard.ofScheme X) = 0 :=
      fun q => map_zero (Stacks.Picard.schemePullbackClassHom q)
    rw [h0, sub_zero]
    exact (normalize_eq_self f σ hσ (Over.mk g) _
      (Stacks.Picard.eq_zero_of_isField Ω _)).trans hclass
  refine ⟨m.left t, ?_⟩
  have h2 : (m.left ≫ (abelMorphismFull f σ hσ hH P e).left).base t = b₀ t := by
    rw [← Over.comp_left, hm]; rfl
  exact h2.trans hbt

end Stacks.RigidifiedPicard

end
