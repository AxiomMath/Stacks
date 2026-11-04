module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleSurjective
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOffExceptional
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.BlowupAmpleFamily.Noetherian
public import StacksFrontier.AlgebraicGeometry.Chow.DominantPrimeCycle
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.DvrCycleClasses
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FiberCycleFiniteSum
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.HilbertCycleOfClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.RestrictedBaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreFreeBlowup0811
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.LowerSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.GenericFlatnessIntegralBase

/-!
# Relative cycles are cycle classes after a proper completely decomposed cover

[Tag 0H59](https://stacks.math.columbia.edu/tag/0H59): let `f : X ⟶ S` be a finite type morphism
of schemes with `S` Noetherian, let `r ≥ 0` and let `α` be a relative `r`-cycle on `X/S`. Then
there is a proper, completely decomposed (Definition
[0GTI](https://stacks.math.columbia.edu/tag/0GTI)) morphism `g : S' ⟶ S` such that `g^*α` is in
the image of the cycle class map of Equation [0H58](https://stacks.math.columbia.edu/tag/0H58).

## Main results

* `Stacks.Chow.pullbackInCycleClassImage_of_baseChange` — a cycle class realising
  `b^*(ι^*α)` gives one realising `(b ≫ ι)^*α`.
* `Stacks.Chow.familyAssociatedToClosedSubscheme_pointClosure_genericPoint` — over an integral
  base, the closure in `X` of a point `y` of the generic fibre has `[y]` as its member over the
  generic point.
* `Stacks.Chow.exists_isProper_cycleClassMap_genericPoint_eq_of_isIntegral` — the construction
  of the integral case, for an arbitrary family of cycles: over an integral Noetherian base there
  is a proper surjective morphism `b : T ⟶ S` from an integral Noetherian scheme, an isomorphism
  over a dense open, and a cycle class on `X ×_S T / T` whose member over the generic point of `T`
  is that of `b^*α`.
* `Stacks.Chow.exists_isProper_pullbackInCycleClassImage_of_isIntegral` — **the integral case**:
  over an integral Noetherian base there is a proper morphism, an isomorphism over a dense open,
  after which `α` is a cycle class.
* `Stacks.Chow.exists_isProper_isCompletelyDecomposed_pullbackInCycleClassImage_of_isRelativeCycle`
  — Tag 0H59 with the cycle class map of Tag 0H6V.
* `Stacks.Chow.exists_isProper_isCompletelyDecomposed_relativeCycleClassMap_eq` — **Tag 0H59**.

## Implementation notes

The Noetherian induction is
`Stacks.Chow.exists_isProper_isCompletelyDecomposed_pullbackInCycleClassImage`, and this file
proves its integral case.

Over an integral `S` with generic point `η`, write `α_η = ∑ n_y [y]` over the finitely many points
`y` of the generic fibre carrying a coefficient, and let `Z_y ⊆ X` be the closure of the image of
`y` with its reduced structure. By generic flatness (Tag 052A) every `Z_y` is flat over a dense
open `U ⊆ S`, and by the flattening theorem of Tag 0815 for the structure sheaf (the content of
Tag 081R used by the source) each `Z_y` has a `U`-admissible blowup after which its strict
transform is flat. Tag 080N gives one `U`-admissible blowup `b : T ⟶ S` dominating all of them;
the base change to `T` of each flattened strict transform is a closed subscheme `W_y` of
`X ×_S T`, flat over `T`, and a member of `Hilb(X ×_S T / T, r)`. The class
`∑ n_y [W_y]` and `b^*α` agree over the generic point of `T`: there `W_y` is the base change of
`Z_y`, because the generic point of `T` lies off the exceptional divisors, and the member of
`[Z_y]` over `η` is `[y]`. This construction uses nothing about `α` beyond its member over `η`,
and is `Stacks.Chow.exists_isProper_cycleClassMap_genericPoint_eq_of_isIntegral`. When `α` is a
relative cycle, both are relative cycles on the integral scheme `T`, so by Tag 0H55 they agree.

## References

* [Stacks Project, Lemma 0H59](https://stacks.math.columbia.edu/tag/0H59)
* [Stacks Project, Equation 0H58](https://stacks.math.columbia.edu/tag/0H58)
* [Stacks Project, Definition 0GTI](https://stacks.math.columbia.edu/tag/0GTI)
* [Stacks Project, Proposition 052A](https://stacks.math.columbia.edu/tag/052A)
* [Stacks Project, Lemma 081R](https://stacks.math.columbia.edu/tag/081R)
* [Stacks Project, Lemma 080N](https://stacks.math.columbia.edu/tag/080N)
* [Stacks Project, Lemma 0H55](https://stacks.math.columbia.edu/tag/0H55)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Transferring a cycle class along an iterated base change -/

/-- **A cycle class for an iterated base change.** Let `ι : S₁ ⟶ S` and `b : T ⟶ S₁`. If
`b^*(ι^*α)` is in the image of the cycle class map of `(X ×_S S₁) ×_{S₁} T / T`, then
`(b ≫ ι)^*α` is in the image of the cycle class map of `X ×_S T / T`. -/
theorem pullbackInCycleClassImage_of_baseChange {X S S₁ T : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] (ι : S₁ ⟶ S) (b : T ⟶ S₁) (r : ℕ)
    (α : FamilyOfCycles f r)
    (H : PullbackInCycleClassImage (pullback.snd f ι) r (baseChangeFamily f ι r α) b) :
    PullbackInCycleClassImage f r α (b ≫ ι) := by
  obtain ⟨c₁, hc₁⟩ := H
  let e := pullbackLeftPullbackSndIso f ι b
  have h : e.hom ≫ pullback.snd f (b ≫ ι) = pullback.snd (pullback.snd f ι) b ≫ 𝟙 T := by
    rw [pullbackLeftPullbackSndIso_hom_snd, Category.comp_id]
  have h' : e.hom ≫ pullback.snd f (b ≫ ι) = pullback.snd (pullback.snd f ι) b :=
    pullbackLeftPullbackSndIso_hom_snd f ι b
  refine ⟨FreeAbelianGroup.map (fun Z ↦ HilbertCycleDatum.extend (pullback.snd f (b ≫ ι))
    (pullback.snd (pullback.snd f ι) b) e.hom (𝟙 T) r Z h) c₁, funext fun t ↦ ?_⟩
  refine fiberCycle_eq_of_restrictedFamily_apply_eq_of_isPullback (pullback.snd f (b ≫ ι))
    (pullback.snd (pullback.snd f ι) b) e.hom (𝟙 T) h (fun x _ ↦ ⟨e.inv x, by
      change (e.inv ≫ e.hom) x = x
      rw [Iso.inv_hom_id]
      rfl⟩) _ _ t ?_
  have hcls := congrFun (restrictedFamilyHom_cycleClassMap_map_extend (pullback.snd f (b ≫ ι))
    (pullback.snd (pullback.snd f ι) b) e.hom (𝟙 T) h r c₁) t
  rw [restrictedFamilyHom_apply] at hcls
  rw [hcls, hc₁, restrictedFamily_id_apply _ _ _ h h' r,
    baseChangeFamily_baseChangeFamily_of_locallyOfFiniteType f ι b r α t]

/-! ### The reduced closure of a point of the generic fibre -/

section PointClosure

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The fibre over `s` of the reduced closure of the image of a point `y` of `X_s` is, inside
`X_s`, the closure of `y`. -/
theorem range_fiberClosedImmersion_pointClosure (s : S) (y : f.fiber s) :
    Set.range (fiberClosedImmersion f
        (AlgebraicGeometry.reducedPointIdeal X (f.fiberι s y)).subschemeι s) =
      closure ({y} : Set (f.fiber s)) := by
  change Set.range (pullback.snd _ (f.fiberι s)) = _
  rw [Scheme.Pullback.range_snd, Scheme.IdealSheafData.range_subschemeι,
    coe_support_pointClosure, ← Set.image_singleton,
    ← (f.fiberι s).isEmbedding.isInducing.closure_eq_preimage_closure_image]

variable [IsIntegral S]

/-- Over an integral base, the reduced closure of the image of a point of the generic fibre
dominates the base. -/
theorem isDominant_pointClosure_comp (y : f.fiber (genericPoint S)) :
    IsDominant ((AlgebraicGeometry.reducedPointIdeal X
      (f.fiberι (genericPoint S) y)).subschemeι ≫ f) := by
  have hx : f (f.fiberι (genericPoint S) y) = genericPoint S :=
    (f.fiberHomeo (genericPoint S) y).2
  constructor
  rw [denseRange_iff_closure_range]
  refine Set.eq_univ_of_univ_subset ?_
  rw [← genericPoint_closure (α := S)]
  refine closure_mono (Set.singleton_subset_iff.mpr ⟨genericPoint _, ?_⟩)
  rw [Scheme.Hom.comp_apply, subschemeι_genericPoint_pointClosure, hx]

/-- Over an integral base, the generic fibre of the reduced closure of the image of a point of
the generic fibre is integral. -/
instance isIntegral_pullback_pointClosure_fiberι_genericPoint (y : f.fiber (genericPoint S)) :
    IsIntegral (pullback (AlgebraicGeometry.reducedPointIdeal X
      (f.fiberι (genericPoint S) y)).subschemeι (f.fiberι (genericPoint S)) : Scheme.{u}) := by
  have := isDominant_pointClosure_comp f y
  exact IsIntegral.of_isIso (compFiberIso (AlgebraicGeometry.reducedPointIdeal X
    (f.fiberι (genericPoint S) y)).subschemeι f (genericPoint S)).inv

/-- The generic point of the generic fibre of the reduced closure of `f.fiberι η y` is `y`. -/
theorem fiberClosedImmersion_genericPoint_pointClosure (y : f.fiber (genericPoint S)) :
    (fiberClosedImmersion f (AlgebraicGeometry.reducedPointIdeal X
        (f.fiberι (genericPoint S) y)).subschemeι (genericPoint S))
      (genericPoint (pullback (AlgebraicGeometry.reducedPointIdeal X
        (f.fiberι (genericPoint S) y)).subschemeι (f.fiberι (genericPoint S)) : Scheme.{u})) = y :=
  image_genericPoint_eq_of_range_eq_closure _ y
    (range_fiberClosedImmersion_pointClosure f (genericPoint S) y)

variable [LocallyOfFiniteType f]

/-- The generic fibre of the reduced closure of the image of a point `y` of relative dimension `r`
of the generic fibre has dimension `r`. -/
theorem topologicalKrullDim_pullback_pointClosure_genericPoint {r : ℕ}
    (y : f.fiber (genericPoint S))
    (hy : relativeDimension (fieldChowSituation (S.residueField (genericPoint S))).dimensionFunction
      (f.fiberToSpecResidueField (genericPoint S)) y = (r : ℤ)) :
    topologicalKrullDim (pullback (AlgebraicGeometry.reducedPointIdeal X
        (f.fiberι (genericPoint S) y)).subschemeι (f.fiberι (genericPoint S)) : Scheme.{u}) =
      (r : WithBot ℕ∞) := by
  have : JacobsonSpace (fieldChowSituation (S.residueField (genericPoint S))).S :=
    inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of (S.residueField (genericPoint S)))))
  rw [topologicalKrullDim_eq_relativeDimension_toNat
      (fieldChowSituation (S.residueField (genericPoint S))) (fun _ _ ↦ rfl)
      (f.fiberToSpecResidueField (genericPoint S))
      (fiberClosedImmersion f (AlgebraicGeometry.reducedPointIdeal X
        (f.fiberι (genericPoint S) y)).subschemeι (genericPoint S))
      _ (genericPoint_spec _),
    fiberClosedImmersion_genericPoint_pointClosure, hy]
  simp

/-- **The member over the generic point of the family of the closure of a point of the generic
fibre.** Over an integral base `S` with generic point `η`, let `y` be a point of `X_η` of
relative dimension `r`. The member over `η` of the family `[Z/X/S]_r` of the reduced closure `Z`
of the image of `y` in `X` is the prime cycle `[y]`. -/
theorem familyAssociatedToClosedSubscheme_pointClosure_genericPoint {r : ℕ}
    (y : f.fiber (genericPoint S))
    (hy : relativeDimension (fieldChowSituation (S.residueField (genericPoint S))).dimensionFunction
      (f.fiberToSpecResidueField (genericPoint S)) y = (r : ℤ)) :
    (familyAssociatedToClosedSubscheme f (AlgebraicGeometry.reducedPointIdeal X
        (f.fiberι (genericPoint S) y)).subschemeι r (genericPoint S) :
        AlgebraicCycle (f.fiber (genericPoint S)) ℤ) =
      @Function.locallyFinsuppWithin.single _ _ ℤ (Classical.decEq _) _ y (1 : ℤ) := by
  rw [familyAssociatedToClosedSubscheme_apply]
  have hgen := fiberClosedImmersion_genericPoint_pointClosure f y
  rw [cycleAssociatedToClosedSubscheme_eq_single _ _ _ (r : ℤ) (by rw [hgen]; exact hy), hgen]

end PointClosure

/-! ### Base change of an isomorphism over an open -/

/-- **A base change landing over an open where the morphism is an isomorphism is an
isomorphism.** In a cartesian square `t ≫ σ = m ≫ k`, if `σ` restricts to an isomorphism over an
open `O` and `k` lands in `O`, then `m` is an isomorphism. -/
theorem isIso_of_isPullback_of_isIso_morphismRestrict {P A B C : Scheme.{u}} {t : P ⟶ A}
    {m : P ⟶ C} {σ : A ⟶ B} {k : C ⟶ B} (sq : IsPullback t m σ k) (O : B.Opens)
    [IsIso (σ ∣_ O)] (hk : ∀ x, k x ∈ O) : IsIso m := by
  let k' : C ⟶ O.toScheme := IsOpenImmersion.lift O.ι k (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hk x)
  have hk' : k' ≫ O.ι = k := IsOpenImmersion.lift_fac _ _ _
  have big : IsPullback (pullback.fst (σ ∣_ O) k' ≫ (σ ⁻¹ᵁ O).ι) (pullback.snd (σ ∣_ O) k')
      σ k := by
    rw [← hk']
    exact (IsPullback.of_hasPullback (σ ∣_ O) k').paste_horiz
      (isPullback_morphismRestrict σ O).flip
  have : IsIso (pullback.snd (σ ∣_ O) k') := (IsPullback.of_hasPullback _ _).isIso_snd_of_isIso
  rw [← IsPullback.isoIsPullback_hom_snd _ _ sq big]
  infer_instance

/-! ### The base change of a flattened strict transform -/

/-- The fibre over `t` of a composite has the same dimension as the pullback of the first
morphism along the fibre inclusion of the second. -/
private theorem topologicalKrullDim_pullback_fiberι {A B C : Scheme.{u}} (p : A ⟶ B) (g : B ⟶ C)
    (t : C) :
    topologicalKrullDim (pullback p (g.fiberι t) : Scheme.{u}) =
      topologicalKrullDim ((p ≫ g).fiber t) :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (compFiberIso p g t)).isHomeomorph

/-- **The base change of a flat strict transform.** Let `i : Z ⟶ X` be a closed subscheme of a
scheme over `S`, let `ℐ` be an ideal sheaf on `S` such that the strict transform of `Z` along the
blowup `S_ℐ ⟶ S` is flat over `S_ℐ`, and let `b : T ⟶ S` factor through `S_ℐ`. The base change
to `T` of that strict transform is a closed subscheme `W` of `X ×_S T`, flat over `T`. Over a
point `t` of `T` whose image in `S` lies off the centre, the fibre of `W` is the fibre of the
plain base change `Z ×_X (X ×_S T)`, and both have the dimension of the fibre of `Z` over `b t`. -/
theorem exists_closedImmersion_flat_of_flat_strictTransformMap {X S Z T : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i] (ℐ : S.IdealSheafData)
    [hST : Flat (Stacks.Blowup.strictTransformMap (i ≫ f) ℐ)] (b : T ⟶ S)
    (g : T ⟶ Stacks.Blowup.blowUp ℐ) (hg : g ≫ Stacks.Blowup.blowUpToBase ℐ = b) (t : T)
    (ht : b t ∉ (ℐ.support : Set S)) :
    ∃ (W : Scheme.{u}) (w : W ⟶ pullback f b) (_ : IsClosedImmersion w),
      Flat (w ≫ pullback.snd f b) ∧
      ∃ e : (pullback w ((pullback.snd f b).fiberι t) : Scheme.{u}) ≅
          pullback (pullback.snd i (pullback.fst f b)) ((pullback.snd f b).fiberι t),
        e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
        topologicalKrullDim (pullback (pullback.snd i (pullback.fst f b))
            ((pullback.snd f b).fiberι t) : Scheme.{u}) =
          topologicalKrullDim (pullback i (f.fiberι (b t)) : Scheme.{u}) := by
  set φ := i ≫ f with hφ
  set β := Stacks.Blowup.blowUpToBase ℐ with hβ
  set σ := Stacks.Blowup.strictTransformι φ ℐ with hσ
  set p := pullback.snd i (pullback.fst f b) with hp
  let π : pullback i (pullback.fst f b) ⟶ pullback φ β :=
    pullback.lift (pullback.fst i (pullback.fst f b)) (p ≫ pullback.snd f b ≫ g) (by
      rw [Category.assoc, Category.assoc, hg, ← pullback.condition, hφ,
        pullback.condition_assoc])
  have hπfst : π ≫ pullback.fst φ β = pullback.fst i (pullback.fst f b) := pullback.lift_fst _ _ _
  have hπsnd : π ≫ pullback.snd φ β = p ≫ pullback.snd f b ≫ g := pullback.lift_snd _ _ _
  set q := pullback.snd σ π with hq
  have sq12 : IsPullback (pullback.fst i (pullback.fst f b)) (p ≫ pullback.snd f b) φ b :=
    (IsPullback.of_hasPullback i (pullback.fst f b)).paste_vert (IsPullback.of_hasPullback f b)
  have sq4 : IsPullback π (p ≫ pullback.snd f b) (pullback.snd φ β) g := by
    refine IsPullback.of_right (h₁₂ := pullback.fst φ β) (h₂₂ := β) ?_ ?_
      (IsPullback.of_hasPullback φ β)
    · rwa [hπfst, hg]
    · rw [hπsnd, Category.assoc]
  have sq5 : IsPullback (pullback.fst σ π) q σ π := IsPullback.of_hasPullback σ π
  have hflat : Flat (q ≫ p ≫ pullback.snd f b) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat) (sq5.paste_vert sq4) hST
  refine ⟨pullback σ π, q ≫ p, inferInstance, by rwa [Category.assoc], ?_⟩
  set ι := (pullback.snd f b).fiberι t with hι
  let m : (pullback (q ≫ p) ι : Scheme.{u}) ⟶ pullback p ι :=
    pullback.map (q ≫ p) ι p ι q (𝟙 _) (𝟙 _) (by rw [Category.comp_id]) (by simp)
  have hmfst : m ≫ pullback.fst p ι = pullback.fst (q ≫ p) ι ≫ q := pullback.lift_fst _ _ _
  have hmsnd : m ≫ pullback.snd p ι = pullback.snd (q ≫ p) ι := by
    rw [pullback.lift_snd, Category.comp_id]
  have sqC : IsPullback (pullback.fst (q ≫ p) ι) m q (pullback.fst p ι) :=
    IsPullback.of_bot (v₂₁ := pullback.snd p ι) (v₂₂ := p) (h₃₁ := ι)
      (by rw [hmsnd]; exact IsPullback.of_hasPullback (q ≫ p) ι) hmfst.symm
      (IsPullback.of_hasPullback p ι)
  have hk : ∀ x, (pullback.fst p ι ≫ π) x ∈
      Stacks.Blowup.exceptionalPullbackCompl φ ℐ := by
    intro x
    change _ ∉ Stacks.Blowup.exceptionalPullbackSet φ ℐ
    rw [Stacks.Blowup.exceptionalPullbackSet_eq_preimage_support, Set.mem_preimage,
      ← Scheme.Hom.comp_apply]
    have hcomp : (pullback.fst p ι ≫ π) ≫ Stacks.Blowup.blowUpPullbackToBlowUp φ ℐ ≫ β =
        pullback.snd p ι ≫ ι ≫ pullback.snd f b ≫ b := by
      change (pullback.fst p ι ≫ π) ≫ pullback.snd φ β ≫ β = _
      rw [Category.assoc, reassoc_of% hπsnd, ← pullback.condition_assoc, hg]
    rw [hcomp]
    have hfib : pullback.snd f b (ι (pullback.snd p ι x)) = t :=
      ((pullback.snd f b).range_fiberι t).subset ⟨_, rfl⟩
    simpa only [Scheme.Hom.comp_apply, hfib] using ht
  have : IsIso m := isIso_of_isPullback_of_isIso_morphismRestrict (sqC.paste_horiz sq5)
    (Stacks.Blowup.exceptionalPullbackCompl φ ℐ) hk
  refine ⟨asIso m, hmsnd, ?_⟩
  have h3 := congrFun (Scheme.Hom.fiberDimension_eq_of_isPullback sq12) t
  simp only [Scheme.Hom.fiberDimension, Function.comp_apply] at h3
  rw [topologicalKrullDim_pullback_fiberι p (pullback.snd f b) t, h3,
    ← topologicalKrullDim_pullback_fiberι i f (b t)]

/-! ### Admissible blowups of an integral scheme -/

/-- **An admissible blowup of an integral scheme is integral**, as soon as the open it is
admissible for is nonempty. -/
theorem isIntegral_of_isAdmissibleBlowup {X X' : Scheme.{u}} [IsIntegral X] {U : X.Opens}
    (hU : (U : Set X).Nonempty) {b : X' ⟶ X} (hb : Stacks.Blowup.IsAdmissibleBlowup U b) :
    IsIntegral X' := by
  obtain ⟨K, -, hKdisj, e, -⟩ := (Stacks.Blowup.isAdmissibleBlowup_iff U b).mp hb
  have hK : K ≠ ⊥ := by
    rintro rfl
    obtain ⟨x, hx⟩ := hU
    exact Set.disjoint_left.mp hKdisj hx (by simp [Scheme.IdealSheafData.support_bot])
  have := AlgebraicGeometry.isIntegral_blowUp K hK
  exact IsIntegral.of_isIso e.inv

/-! ### The integral case -/

/-- **The construction of the integral case of Tag 0H59.** Let `S` be an integral Noetherian
scheme, let `f : X ⟶ S` be of finite type and let `α` be a family of `r`-cycles on the fibres of
`f`. There is a proper surjective morphism `b : T ⟶ S` from an integral Noetherian scheme, an
isomorphism over a dense open of `S`, and a cycle class on `X ×_S T / T` whose member over the
generic point of `T` is the member of `b^*α` there. -/
theorem exists_isProper_cycleClassMap_genericPoint_eq_of_isIntegral {X S : Scheme.{u}}
    [IsNoetherian S] [IsIntegral S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (r : ℕ)
    (α : FamilyOfCycles f r) :
    ∃ (T : Scheme.{u}) (b : T ⟶ S) (_ : IsIntegral T) (_ : IsNoetherian T), IsProper b ∧
      Surjective b ∧ (∃ U : S.Opens, Dense (U : Set S) ∧ IsIso (b ∣_ U)) ∧
      ∃ c : FreeAbelianGroup (HilbertCycleDatum (pullback.snd f b) r),
        (relativeCycleClassMap (pullback.snd f b) c : FamilyOfCycles (pullback.snd f b) r)
            (genericPoint T) = baseChangeFamily f b r α (genericPoint T) := by
  set η := genericPoint S with hη
  let A : Finset (f.fiber η) := (finite_support_fiberCycle f η r (α η)).toFinset
  have hA : ∀ y ∈ A, (α η : AlgebraicCycle (f.fiber η) ℤ) y ≠ 0 := fun y hy ↦ by
    simpa using (Set.Finite.mem_toFinset _).1 hy
  have hAdim : ∀ y ∈ A,
      relativeDimension (fieldChowSituation (S.residueField η)).dimensionFunction
        (f.fiberToSpecResidueField η) y = (r : ℤ) := fun y hy ↦
    relativeDimension_of_fiberCycle_apply_ne_zero f η r (α η) (hA y hy)
  let Z : A → X.IdealSheafData := fun y ↦ AlgebraicGeometry.reducedPointIdeal X (f.fiberι η y.1)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hflat : ∀ y : A, ∃ U : S.Opens, Dense (U : Set S) ∧
      Flat (((Z y).subschemeι ≫ f).resLE U (((Z y).subschemeι ≫ f) ⁻¹ᵁ U) le_rfl) := fun y ↦ by
    have : (Scheme.unitModule (Z y).subscheme).IsFiniteType :=
      SheafOfModules.instIsFiniteTypeOfIsFinitePresentation.{u, u, u} _
    exact (exists_dense_open_flat_finitePresentation_of_isIntegral ((Z y).subschemeι ≫ f)
      (Scheme.unitModule (Z y).subscheme)).imp fun _ h ↦ ⟨h.1, h.2.1⟩
  choose U₀ hU₀ hflU₀ using hflat
  have hflatten : ∀ y : A, HasFlatteningBlowup ((Z y).subschemeι ≫ f) (U₀ y) := fun y ↦ by
    have : CompactSpace (Z y).subscheme :=
      QuasiCompact.compactSpace_of_compactSpace (Z y).subschemeι
    exact finitePresentationHasFlatteningBlowup _ _ (NoetherianSpace.isCompact _) (hflU₀ y)
  choose ℐ hℐfp hℐdisj hℐflat using hflatten
  let U : S.Opens := ⟨⋂ y : A, (U₀ y : Set S), isOpen_iInter_of_finite fun y ↦ (U₀ y).isOpen⟩
  have hUle : ∀ y, (U : Set S) ⊆ U₀ y := fun y _ hx ↦ Set.mem_iInter.mp hx y
  have hηU : η ∈ U := Set.mem_iInter.mpr fun y ↦
    ((genericPoint_spec S).mem_open_set_iff (U₀ y).isOpen).mpr
      (by simpa using (hU₀ y).nonempty)
  have hUdense : Dense (U : Set S) := U.isOpen.dense ⟨η, hηU⟩
  obtain ⟨T, b, hb, g, hg, -⟩ := Stacks.Blowup.exists_admissibleBlowup_dominating U
    (fun y : A ↦ Stacks.Blowup.blowUp (ℐ y)) (fun y ↦ Stacks.Blowup.blowUpToBase (ℐ y))
    (fun y ↦ Stacks.Blowup.isAdmissibleBlowup_blowUpToBase (hℐfp y)
      ((hℐdisj y).mono_left (hUle y)))
  have : IsProper b := hb.isProper
  have : IsIso (b ∣_ U) := Stacks.BlowupAmpleFamily.isIso_morphismRestrict_of_isAdmissibleBlowup hb
  have : IsIntegral T := isIntegral_of_isAdmissibleBlowup ⟨η, hηU⟩ hb
  have : IsNoetherian T := isNoetherian_source_of_isProper b
  refine ⟨T, b, inferInstance, inferInstance, inferInstance, hb.surjective hUdense,
    ⟨U, hUdense, inferInstance⟩, ?_⟩
  set ηT := genericPoint T with hηT
  have hbη : b ηT = η := genericPoint_image_of_isIso_morphismRestrict b U hUdense
  have hbηU : b ηT ∈ U := hbη ▸ hηU
  have : IsIso (b.residueFieldMap ηT) :=
    isIso_residueFieldMap_of_mem_isIso_morphismRestrict b U ηT hbηU
  have hW := fun y : A ↦
    have := hℐflat y
    exists_closedImmersion_flat_of_flat_strictTransformMap f (Z y).subschemeι (ℐ y) b
      (g y) (hg y) ηT fun hmem ↦ Set.disjoint_left.mp (hℐdisj y) (hUle y hbηU) hmem
  choose W w hw hwflat e he hdimP using hW
  have := hw
  have := hwflat
  have hdimη : ∀ y : A,
      topologicalKrullDim (pullback (Z y).subschemeι (f.fiberι η) : Scheme.{u}) = r :=
    fun y ↦ topologicalKrullDim_pullback_pointClosure_genericPoint f y.1 (hAdim y.1 y.2)
  have hdimP' : ∀ y : A, topologicalKrullDim (pullback (pullback.snd (Z y).subschemeι
      (pullback.fst f b)) ((pullback.snd f b).fiberι ηT) : Scheme.{u}) = r := fun y ↦ by
    rw [hdimP y, hbη, hdimη y]
  have hrel : ∀ y : A, RelativeDimensionLE (w y ≫ pullback.snd f b) r := fun y ↦ by
    have hfp : FinitePresentation (w y ≫ pullback.snd f b) :=
      ⟨inferInstance, inferInstance, inferInstance⟩
    have hclosed := (lowerSemicontinuous_fiberDimension (w y ≫ pullback.snd f b)
      hfp).isClosed_preimage (r : WithBot ℕ∞)
    have hgen : (w y ≫ pullback.snd f b).fiberDimension ηT ≤ (r : WithBot ℕ∞) := by
      refine le_of_eq ?_
      change topologicalKrullDim ((w y ≫ pullback.snd f b).fiber ηT) = _
      rw [← topologicalKrullDim_pullback_fiberι,
        IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (e y)).isHomeomorph, hdimP' y]
    have hall : ∀ t : T, (w y ≫ pullback.snd f b).fiberDimension t ≤ (r : WithBot ℕ∞) :=
      fun t ↦ ((genericPoint_spec T).mem_closed_set_iff hclosed).mp hgen (Set.mem_univ t)
    exact fun z ↦ (Scheme.Hom.fiberDimension_le_iff _ _ _).mp (hall _) z rfl
  let H : A → HilbertCycleDatum (pullback.snd f b) r := fun y ↦
    HilbertCycleDatum.ofClosedImmersion (pullback.snd f b) r (w y) (hrel y)
  let n : A → ℤ := fun y ↦ (α η : AlgebraicCycle (f.fiber η) ℤ) y.1
  refine ⟨∑ y : A, n y • FreeAbelianGroup.of (H y), ?_⟩
  rw [relativeCycleClassMap_val]
  have hcls : ∀ y : A, cycleClassMap (pullback.snd f b) r (FreeAbelianGroup.of (H y)) ηT =
      familyAssociatedToClosedSubscheme (pullback.snd f b)
        (pullback.snd (Z y).subschemeι (pullback.fst f b)) r ηT := fun y ↦ by
    rw [cycleClassMap_of, HilbertCycleDatum.cycleFamily_ofClosedImmersion,
      familyAssociatedToClosedSubscheme_apply, familyAssociatedToClosedSubscheme_apply]
    exact cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _ (e y) (he y) _
  have hsum' : (∑ y : A, n y • familyAssociatedToClosedSubscheme f (Z y).subschemeι r) (b ηT) =
      α (b ηT) := by
    rw [hbη]
    apply Subtype.ext
    rw [Finset.sum_apply, AddSubgroup.val_finsetSum, coe_fiberCycle_eq_sum_single f η r (α η),
      ← Finset.sum_coe_sort A]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [Pi.smul_apply, AddSubgroupClass.coe_zsmul,
      familyAssociatedToClosedSubscheme_pointClosure_genericPoint f y.1 (hAdim y.1 y.2)]
    exact (@single_eq_zsmul_single_one _ _ (Classical.decEq _) y.1 (n y)).symm
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  rw [baseChangeFamily_apply_of_isIso_residueFieldMap f b ηT r α x, ← hsum']
  simp only [map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply, AddSubgroup.val_finsetSum,
    AddSubgroupClass.coe_zsmul, Function.locallyFinsuppWithin.coe_sum,
    Function.locallyFinsuppWithin.coe_zsmul, smul_eq_mul]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [hcls y, familyAssociatedToClosedSubscheme_baseChange_apply_of_isIso f b (Z y).subschemeι r ηT
    ((hdimP y).symm.trans (hdimP' y)).le x]

/-- **The integral case of the Noetherian induction for Tag 0H59.** Let `S` be an integral
Noetherian scheme, let `f : X ⟶ S` be of finite type and let `α` be a relative `r`-cycle on
`X/S`. There is a proper morphism `b : T ⟶ S`, an isomorphism over a dense open of `S`, such
that `b^*α` is in the image of the cycle class map. -/
theorem exists_isProper_pullbackInCycleClassImage_of_isIntegral {X S : Scheme.{u}}
    [IsNoetherian S] [IsIntegral S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (r : ℕ)
    {α : FamilyOfCycles f r} (hα : IsRelativeCycle f r α) :
    ∃ (T : Scheme.{u}) (g : T ⟶ S), IsProper g ∧ PullbackInCycleClassImage f r α g ∧
      ∃ U : S.Opens, Dense (U : Set S) ∧ IsIso (g ∣_ U) := by
  obtain ⟨T, b, _, _, hb, -, ⟨U, hU, hiso⟩, c, hc⟩ :=
    exists_isProper_cycleClassMap_genericPoint_eq_of_isIntegral f r α
  refine ⟨T, b, hb, ⟨c, ?_⟩, U, hU, hiso⟩
  have hβrel : IsRelativeCycle (pullback.snd f b) r (cycleClassMap (pullback.snd f b) r c) := by
    rw [← relativeCycleClassMap_val]
    exact (relativeCycleClassMap (pullback.snd f b) c).2
  refine (IsRelativeCycle.eq_iff_eq_of_mem_genericPoints (pullback.snd f b) r hβrel
    (isRelativeCycle_baseChangeFamily f b r hα)).mpr fun t ht ↦ ?_
  rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at ht
  rw [ht, ← relativeCycleClassMap_val]
  exact hc

/-! ### Tag 0H59 -/

/-- **Stacks Project, Lemma 0H59, for the cycle class map of Tag 0H6V.** Let `f : X ⟶ S` be a
finite type morphism of schemes with `S` Noetherian, let `r ≥ 0` and let `α` be a relative
`r`-cycle on `X/S`. Then there is a proper, completely decomposed morphism `g : S' ⟶ S` such
that `g^*α` is in the image of the cycle class map. -/
theorem exists_isProper_isCompletelyDecomposed_pullbackInCycleClassImage_of_isRelativeCycle
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (r : ℕ) {α : FamilyOfCycles f r} (hα : IsRelativeCycle f r α) :
    ∃ (S' : Scheme.{u}) (g : S' ⟶ S),
      IsProper g ∧ PullbackInCycleClassImage f r α g ∧ IsCompletelyDecomposed g := by
  refine exists_isProper_isCompletelyDecomposed_pullbackInCycleClassImage f r α
    (fun g₁ g₂ H₁ H₂ ↦ pullbackInCycleClassImage_coprod_desc f r α g₁ g₂ H₁ H₂) fun I hI ↦ ?_
  have := hI
  have : IsNoetherian I.subscheme := isNoetherian_source_of_isProper I.subschemeι
  obtain ⟨T, g, hg, hP, U, hU, hiso⟩ := exists_isProper_pullbackInCycleClassImage_of_isIntegral
    (pullback.snd f I.subschemeι) r (isRelativeCycle_baseChangeFamily f I.subschemeι r hα)
  exact ⟨T, g, hg, pullbackInCycleClassImage_of_baseChange f I.subschemeι g r α hP, U, hU, hiso⟩

/-- Let `f : X ⟶ S` be a finite type morphism of schemes with `S` Noetherian, let `r ≥ 0` and
let `α` be a relative `r`-cycle on `X/S`. Then there is a proper, completely decomposed
(Definition 0GTI) morphism `g : S' ⟶ S` from a Noetherian scheme `S'` such that `g^*α` is in the
image of the cycle class map `FreeAbelianGroup (Hilb(X ×_S S' / S', r)) ⟶ z(X ×_S S' / S', r)` of
Equation 0H58. -/
@[stacks 0H59]
theorem exists_isProper_isCompletelyDecomposed_relativeCycleClassMap_eq {X S : Scheme.{u}}
    [IsNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (r : ℕ)
    (α : relativeCycles f r) :
    ∃ (S' : Scheme.{u}) (g : S' ⟶ S) (_ : IsNoetherian S'), IsProper g ∧
      IsCompletelyDecomposed g ∧
      ∃ c : FreeAbelianGroup (HilbertCycleDatum (pullback.snd f g) r),
        (relativeCycleClassMap (pullback.snd f g) c : FamilyOfCycles (pullback.snd f g) r) =
          baseChangeFamily f g r α := by
  obtain ⟨S', g, hg, ⟨c, hc⟩, hcd⟩ :=
    exists_isProper_isCompletelyDecomposed_pullbackInCycleClassImage_of_isRelativeCycle f r α.2
  have := hg
  have hN : IsNoetherian S' := isNoetherian_source_of_isProper g
  exact ⟨S', g, hN, hg, hcd, c, (relativeCycleClassMap_val _ c).trans hc⟩

end Stacks.Chow

end
