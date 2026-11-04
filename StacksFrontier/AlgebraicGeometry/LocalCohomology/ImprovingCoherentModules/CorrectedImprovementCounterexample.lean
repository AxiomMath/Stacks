module

public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.EssSurjRestrictOpen
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.CorrectedImprovement
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Witnesses

/-!
# The corrected conditions of [Stacks, Tag 0DX5] are not stable under open restriction

The corrected form `AlgebraicGeometry.existsUnique_isCorrectedImprovement` of [Stacks, Tag 0DX5]
replaces condition (3) at the points of `Z` generalizing a reached point by surjectivity and depth
at least one.  Its Cohen–Macaulay pullback, `AlgebraicGeometry.correctedImprovement_pullback`,
asks for depth two only on the inverse image of the points of `Z` generalizing no reached point
*downstairs*, rather than at the points generalizing no reached point *upstairs*, which is what
"the same properties with respect to `f^{-1}(Z)`" would say.  This module shows that the weaker
form is forced, on the counterexample of `ImprovementExistenceCounterexample.lean`.

Let `X = Spec k[u, v, w]`, `Z = V(u, v)`, `F = (u, v)~ ⊕ (k[u, v, w]/(u, w))~` and let
`D(w) ⊆ X` be the open where `w` does not vanish; it contains `(u, v)` but not the reached point
`(u, v, w)`, and the inclusion is an open immersion, hence a Cohen–Macaulay morphism with
Noetherian source.  On `D(w)` no point of `Z` is reached any more: the associated points of `F`
there are the generic point alone, and `(0) ⤳ 𝔮` is never immediate for `𝔮 ⊇ (u, v)`.  So the
corrected conditions for `F|_{D(w)}` ask for depth two at `(u, v)`.  But the corrected map of `F`
is surjective at `(u, v, w)`, hence at `(u, v)`, where its target is a nonzero quotient of the
maximal ideal of a two-dimensional regular local ring, of depth below two.

## Main results

* `Stacks.ImprovementCounterexample.not_generalizesReached_cexOpenPt`: on `D(w)`, the point
  `(u, v)` generalizes no reached point.
* `Stacks.ImprovementCounterexample.not_isCorrectedImprovement_pullback_cexOpen`: the restriction
  to `D(w)` of any map satisfying the corrected conditions along `Z` does not satisfy them along
  `Z ∩ D(w)`.
* `Stacks.ImprovementCounterexample.correctedImprovement_pullback_not_intrinsic`: the same,
  packaged with the existence of such a map and with the hypotheses of the pullback assertion
  for the inclusion of `D(w)`.

## References

* [Stacks Project, Tag 0DX5](https://stacks.math.columbia.edu/tag/0DX5)
-/

@[expose] public section

open CategoryTheory IsLocalRing TopologicalSpace
open AlgebraicGeometry Stacks.ModuleStalkSpecialization

universe u

namespace Stacks.ImprovementCounterexample

section Cex

variable (k : Type u) [Field k]

/-- The open `D(w)` of `X = Spec k[u, v, w]`, the complement of `V(w)`. -/
noncomputable abbrev cexOpen : (cexScheme k).Opens :=
  PrimeSpectrum.basicOpen (MvPolynomial.X 2 : MvPolynomial (Fin 3) k)

/-- The point `(u, v)` lies in `D(w)`. -/
theorem cexPt_uv_mem_cexOpen : cexPt k {0, 1} ∈ (cexOpen k : Set (cexScheme k)) :=
  X_notMem_span_image_X (by decide)

/-- `(u, v)` as a point of `D(w)`. -/
noncomputable abbrev cexOpenPt : (cexOpen k).toScheme := ⟨cexPt k {0, 1}, cexPt_uv_mem_cexOpen k⟩

/-- **On `D(w)` the point `(u, v)` generalizes no reached point.**  A point of `Z ∩ D(w)` reached
from outside for `F|_{D(w)}` would be reached from an associated point of `F` lying in `D(w)`, so
from the generic point — `(u, w)` contains `w` — and the specialization of the generic point to a
prime containing `(u, v)` factors through `(u)`, so is not immediate. -/
theorem not_generalizesReached_cexOpenPt :
    ¬ GeneralizesReached ((cexOpen k).ι.base ⁻¹' cexZ k)
      ((Scheme.Modules.pullback (cexOpen k).ι).obj (cexSheaf k)) (cexOpenPt k) := by
  rintro ⟨z, -, ⟨x', -, hx'A, himm⟩, hpz⟩
  rw [associatedPoints_pullback_opensι] at hx'A
  have himm' := himm.map_of_isOpenEmbedding (cexOpen k).ι.isOpenEmbedding
  have hle : (varPrime k {0, 1}).asIdeal ≤ ((cexOpen k).ι z : PrimeSpectrum _).asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr (hpz.map (cexOpen k).ι.base.hom.continuous)
  rcases (isAssociatedPoint_cexSheaf_iff k ((cexOpen k).ι x')).mp hx'A with h | h
  · refine not_isImmediateSpecialization_of_lt_of_lt himm' (varPrime k {0}) ?_
      (lt_of_lt_of_le ?_ hle)
    · rw [h, bot_lt_iff_ne_bot]
      intro hbot
      have hmem : (MvPolynomial.X 0 : MvPolynomial (Fin 3) k) ∈ (varPrime k {0}).asIdeal :=
        Ideal.subset_span (Set.mem_image_of_mem _ (by simp))
      rw [hbot, Ideal.mem_bot] at hmem
      exact MvPolynomial.X_ne_zero 0 hmem
    · exact span_image_X_lt (i := (1 : Fin 3)) (by decide) (by decide) (by decide)
  · have hx'U : (cexOpen k).ι x' ∈ (cexOpen k : Set (cexScheme k)) := x'.2
    exact hx'U (h ▸ Ideal.subset_span (Set.mem_image_of_mem _ (by decide)))

/-- The depth of a stalk of the pullback along the inclusion of an open subscheme is the depth of
the stalk below: the pullback is the restriction (`Scheme.Modules.restrictFunctorIsoPullback`),
whose stalks are those of the module (`Scheme.Modules.depth_stalk_restrict`). -/
theorem depth_stalk_pullback_opensι {X : Scheme.{u}} (U : X.Opens) (G : X.Modules)
    (y : U.toScheme) :
    letI : Module (U.toScheme.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pullback U.ι).obj G).val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := U.toScheme.presheaf) ((Scheme.Modules.pullback U.ι).obj G).val y
    letI : Module (X.presheaf.stalk (U.ι y))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (U.ι y)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) G.val (U.ι y)
    Module.depth (U.toScheme.presheaf.stalk y) (maximalIdeal (U.toScheme.presheaf.stalk y))
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pullback U.ι).obj G).val.presheaf y) =
      Module.depth (X.presheaf.stalk (U.ι y)) (maximalIdeal (X.presheaf.stalk (U.ι y)))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (U.ι y)) := by
  exact (Scheme.Modules.depth_stalk_congr
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app G) y).symm.trans
    (Scheme.Modules.depth_stalk_restrict U.ι G y)

/-- **The corrected conditions do not restrict to `D(w)`.**  For every map `φ` out of
`F = (u, v)~ ⊕ (k[u, v, w]/(u, w))~` satisfying the corrected conditions along `Z = V(u, v)`, the
restriction of `φ` to `D(w)` does not satisfy the corrected conditions along `Z ∩ D(w)`: they ask
for depth two at `(u, v)`, where the target of `φ` has depth below two by
`Stacks.ImprovementCounterexample.not_two_le_depth_stalk_of_linearEquiv_maximalIdeal`, `φ` being
surjective at the reached point `(u, v, w)`. -/
theorem not_isCorrectedImprovement_pullback_cexOpen {G : (cexScheme k).Modules}
    (φ : cexSheaf k ⟶ G) (hφ : IsCorrectedImprovement (cexZ k) φ) :
    ¬ IsCorrectedImprovement ((cexOpen k).ι.base ⁻¹' cexZ k)
      ((Scheme.Modules.pullback (cexOpen k).ι).map φ) := by
  intro h
  have : G.IsCoherent := hφ.1
  have hpZ : cexOpenPt k ∈ (cexOpen k).ι.base ⁻¹' cexZ k := cexPt_mem_cexZ k (le_refl _)
  have hup := h.2.2.2.2 (cexOpenPt k) hpZ (not_generalizesReached_cexOpenPt k)
  have hdown := depth_stalk_pullback_opensι (cexOpen k) G (cexOpenPt k)
  have hspec {s t : Finset (Fin 3)} (h : s ⊆ t) : cexPt k s ⤳ cexPt k t :=
    (PrimeSpectrum.le_iff_specializes _ _).mp (Ideal.span_mono (Set.image_mono (by simpa using h)))
  have hdim : ringKrullDim ((cexScheme k).presheaf.stalk (cexPt k {0, 1}))
      = (2 : WithBot ℕ∞) := by
    rw [ringKrullDim_stalk_cexPt, show ({0, 1} : Finset (Fin 3)).card = 2 by decide]
    rfl
  exact not_two_le_depth_stalk_of_linearEquiv_maximalIdeal φ (hspec (by decide)) (hspec (by decide))
    (hφ.2.1 _ (cexPt_notMem_cexZ k (by decide)))
    (hφ.2.2.1 _ (cexPt_mem_cexZ k (by decide)) (reachedFromOutside_cexSheaf_uvw k)).1 hdim
    (nontrivial_stalk_cexSheaf_generic k) (linearEquiv_stalk_cexSheaf_maximalIdeal k)
    (hdown ▸ hup)

/-- **The intrinsic Cohen–Macaulay pullback fails for the corrected conditions.**  For the
counterexample data, a map satisfying the corrected conditions exists
(`AlgebraicGeometry.existsUnique_isCorrectedImprovement`, all hypotheses witnessed in
`ImprovementExistenceCounterexample.lean`); the inclusion of `D(w)` is a Cohen–Macaulay morphism
with Noetherian source; and the pullback of any such map along it fails the corrected conditions
along the inverse image of `Z`.  This is why `AlgebraicGeometry.correctedImprovement_pullback`
asks for depth two on the inverse image of the points far from the reached points of `X`. -/
theorem correctedImprovement_pullback_not_intrinsic :
    (∃ (G : (cexScheme k).Modules) (φ : cexSheaf k ⟶ G), IsCorrectedImprovement (cexZ k) φ) ∧
      IsNoetherian (cexOpen k).toScheme ∧
      (∃ hfib : ∀ x : cexScheme k, IsLocallyNoetherian ((cexOpen k).ι.fiber x),
        (cexOpen k).ι.IsCohenMacaulay hfib) ∧
      ∀ (G : (cexScheme k).Modules) (φ : cexSheaf k ⟶ G), IsCorrectedImprovement (cexZ k) φ →
        ¬ IsCorrectedImprovement ((cexOpen k).ι.base ⁻¹' cexZ k)
          ((Scheme.Modules.pullback (cexOpen k).ι).map φ) := by
  obtain ⟨G, φ, hφ, -⟩ := existsUnique_isCorrectedImprovement (cexScheme k) (cexZ k)
    (isClosed_cexZ k) (cexSheaf k) (isUniversallyCatenary_cexScheme k)
    (hasSerreCondition_one_formalFibres_cexScheme k)
  have hfib : ∀ x : cexScheme k, IsLocallyNoetherian ((cexOpen k).ι.fiber x) :=
    fun x => isLocallyNoetherian_fiber_of_locallyOfFinitePresentation _ x
  exact ⟨⟨G, φ, hφ⟩, isNoetherian_opens_toScheme (cexOpen k),
    ⟨hfib, Scheme.Hom.isCohenMacaulay_of_isOpenImmersion _ hfib⟩,
    fun G φ hφ => not_isCorrectedImprovement_pullback_cexOpen k φ hφ⟩

end Cex

end Stacks.ImprovementCounterexample

end
