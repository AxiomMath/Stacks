module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesComparison
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreNormalConeIso

/-!
# The exceptional divisor of the blowup at infinity over an affine open

Let `i : Z ⟶ X` be a closed immersion, `b : W ⟶ 𝐏¹_X` the blowup of `𝐏¹_X` in the centre
`∞(Z)` and `E ⊆ W` its exceptional divisor. The centre `∞(Z)` is the image of the closed
immersion `∞ ∘ i : Z ⟶ 𝐏¹_X`, so `E = W ×_{𝐏¹_X} Z` is a scheme over `Z`.

Over an affine open `U = Spec A` of `X`, the centre lies in the chart at infinity
`V = Spec A[s]` of `𝐏¹_U`, and over `V` the blowup is `Proj` of the Rees algebra
`Γ(V)[𝒥(V) t]` of the ideal `𝒥(V) = (I, s)` of the centre (Stacks 0804). Since `Proj` commutes
with base change (Stacks 01N2), the part of `E` over `Z ∩ U` is

  `Proj (Γ(Z ∩ U) ⊗_{Γ(V)} Γ(V)[𝒥(V) t])`.

This file constructs that chart of `E`, proves that it is the part of `E` lying over `U`, and that
the charts are compatible with restriction to smaller affine opens of `X`.

## Main definitions

* `Stacks.Chow.exceptionalDivisorToCentre`: the projection `E ⟶ Z`.
* `Stacks.Chow.centreChartRing`: the graded ring `Γ(Z ∩ U) ⊗_{Γ(V)} Γ(V)[𝒥(V) t]`.
* `Stacks.Chow.exceptionalProjChart`: the chart `Proj (centreChartRing) ⟶ E` over `U`.
* `Stacks.Chow.centreChartRestrict`: the restriction of the graded rings from `U` to `V ⊆ U`.

## Main results

* `Stacks.Chow.isPullback_exceptionalDivisorToCentre`: `E = W ×_{𝐏¹_X} Z`.
* `Stacks.Chow.isPullback_exceptionalProjChart`: the chart over `U` is the part of `E` over `U`.
* `Stacks.Chow.exceptionalProjChartRestrict_exceptionalProjChart`: the charts are compatible with
  restriction.

## References

* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

/-! ### Maps of base changes of graded algebras -/

namespace Stacks.ProjBaseChange

variable {R A R₁ A₁ : Type u} [CommRing R] [CommRing A] [Algebra R A] [CommRing R₁] [CommRing A₁]
  [Algebra R₁ A₁] {𝒜 : ℕ → Submodule R A} [_root_.GradedAlgebra 𝒜] {ℬ : ℕ → Submodule R₁ A₁}
  [_root_.GradedAlgebra ℬ] {S T : Type u} [CommRing S] [Algebra R S] [CommRing T] [Algebra R₁ T]

/-- A homomorphism of graded rings carries the irrelevant ideal into the irrelevant ideal. -/
theorem _root_.HomogeneousIdeal.irrelevant_le_comap {B C σ τ : Type*} [CommRing B] [CommRing C]
    [SetLike σ B] [AddSubgroupClass σ B] [SetLike τ C] [AddSubgroupClass τ C] {𝒟 : ℕ → σ}
    {ℰ : ℕ → τ} [GradedRing 𝒟] [GradedRing ℰ] (q : 𝒟 →+*ᵍ ℰ) :
    HomogeneousIdeal.irrelevant 𝒟 ≤ (HomogeneousIdeal.irrelevant ℰ).comap q :=
  (HomogeneousIdeal.irrelevant_le _).2 fun _ hi _ hx =>
    HomogeneousIdeal.mem_irrelevant_of_mem _ hi (GradedRingHom.map_mem q hx)

/-- **The irrelevant ideals under a map of base changes**: a map `g` of base changes lying over a
map `f` of graded algebras satisfies the hypothesis of `AlgebraicGeometry.Proj.map` as soon as
`f` does. -/
theorem irrelevant_le_map_of_comp_includeRight (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (g : grading 𝒜 S →+*ᵍ grading ℬ T)
    (hg : g.comp (includeRight 𝒜 S) = (includeRight ℬ T).comp f) :
    HomogeneousIdeal.irrelevant (grading ℬ T) ≤
      (HomogeneousIdeal.irrelevant (grading 𝒜 S)).map g := by
  calc HomogeneousIdeal.irrelevant (grading ℬ T)
      ≤ (HomogeneousIdeal.irrelevant ℬ).map (includeRight ℬ T) := irrelevant_le_map _ _
    _ ≤ ((HomogeneousIdeal.irrelevant 𝒜).map f).map (includeRight ℬ T) :=
        HomogeneousIdeal.map_mono _ hf
    _ = ((HomogeneousIdeal.irrelevant 𝒜).map (includeRight 𝒜 S)).map g := by
        rw [HomogeneousIdeal.map_map, HomogeneousIdeal.map_map, hg]
    _ ≤ (HomogeneousIdeal.irrelevant (grading 𝒜 S)).map g :=
        HomogeneousIdeal.map_mono _ ((HomogeneousIdeal.map_le_iff_le_comap _).2
          (HomogeneousIdeal.irrelevant_le_comap _))

/-- **The morphism of projective spectra of a map of base changes** lying over a map `f` of
graded algebras. -/
def mapOfComp (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (g : grading 𝒜 S →+*ᵍ grading ℬ T)
    (hg : g.comp (includeRight 𝒜 S) = (includeRight ℬ T).comp f) :
    AlgebraicGeometry.Proj (grading ℬ T) ⟶ AlgebraicGeometry.Proj (grading 𝒜 S) :=
  Proj.map g (irrelevant_le_map_of_comp_includeRight f hf g hg)

/-- A map of base changes lying over a map of graded algebras commutes with the base-change
morphisms of projective spectra. -/
theorem mapOfComp_map (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (g : grading 𝒜 S →+*ᵍ grading ℬ T)
    (hg : g.comp (includeRight 𝒜 S) = (includeRight ℬ T).comp f) :
    mapOfComp f hf g hg ≫ map 𝒜 S = map ℬ T ≫ Proj.map f hf := by
  rw [mapOfComp, map, map, ← Proj.map_comp, ← Proj.map_comp]
  exact Proj.map_congr hg _ _

/-- A map of base changes lying over a ring map `ρ : S ⟶ T` commutes with the structure morphisms
to `Spec S` and `Spec T`. -/
theorem mapOfComp_toSpec (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (g : grading 𝒜 S →+*ᵍ grading ℬ T)
    (hg : g.comp (includeRight 𝒜 S) = (includeRight ℬ T).comp f) (ρ : S →+* T)
    (hρ : ∀ s : S, g (algebraMap S (S ⊗[R] A) s) = algebraMap T (T ⊗[R₁] A₁) (ρ s)) :
    mapOfComp f hf g hg ≫ Proj.toSpecZero (grading 𝒜 S) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S ↥(grading 𝒜 S 0))) =
      Proj.toSpecZero (grading ℬ T) ≫
        Spec.map (CommRingCat.ofHom (algebraMap T ↥(grading ℬ T 0))) ≫
          Spec.map (CommRingCat.ofHom ρ) := by
  rw [mapOfComp, AlgebraicGeometry.Proj.map_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext s
  exact hρ s

end Stacks.ProjBaseChange

namespace Stacks.Chow

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-! ### The exceptional divisor over the centre -/

omit [IsClosedImmersion i] in
/-- The centre `∞(Z)` is cut out by the kernel of `∞ ∘ i`. -/
theorem ker_comp_lineInfinitySection :
    (i ≫ lineInfinitySection X).ker = infinityCentreIdeal i.ker :=
  (Scheme.IdealSheafData.map_ker i (lineInfinitySection X)).symm

omit [IsClosedImmersion i] in
/-- `E ⟶ W ⟶ 𝐏¹_X` kills the ideal of the centre `∞(Z)`. -/
theorem ker_le_ker_exceptionalDivisorAtInfinity :
    (i ≫ lineInfinitySection X).ker ≤
      ((exceptionalIdealAtInfinity i.ker).subschemeι ≫ blowupAtInfinityToLine i.ker).ker := by
  rw [ker_comp_lineInfinitySection, ← Scheme.IdealSheafData.map_ker,
    Scheme.IdealSheafData.ker_subschemeι]
  exact Scheme.IdealSheafData.le_map_comap _ _

/-- **The projection `E ⟶ Z`** of the exceptional divisor of the blowup at infinity: `E` lies
over the centre `∞(Z)`, which is `Z` embedded by `∞ ∘ i`. -/
def exceptionalDivisorToCentre : (exceptionalIdealAtInfinity i.ker).subscheme ⟶ Z :=
  IsClosedImmersion.lift (i ≫ lineInfinitySection X)
    ((exceptionalIdealAtInfinity i.ker).subschemeι ≫ blowupAtInfinityToLine i.ker)
    (ker_le_ker_exceptionalDivisorAtInfinity i)

/-- `E ⟶ Z ⟶ 𝐏¹_X` is `E ⟶ W ⟶ 𝐏¹_X`. -/
@[reassoc]
theorem exceptionalDivisorToCentre_comp :
    exceptionalDivisorToCentre i ≫ i ≫ lineInfinitySection X =
      (exceptionalIdealAtInfinity i.ker).subschemeι ≫ blowupAtInfinityToLine i.ker :=
  IsClosedImmersion.lift_fac _ _ _

/-- `E ⟶ Z ⟶ X` is `E ⟶ W ⟶ X`. -/
@[reassoc]
theorem exceptionalDivisorToCentre_comp_toX :
    exceptionalDivisorToCentre i ≫ i =
      (exceptionalIdealAtInfinity i.ker).subschemeι ≫ blowupAtInfinityToBase i.ker := by
  rw [blowupAtInfinityToBase, ← Category.assoc, ← exceptionalDivisorToCentre_comp,
    Category.assoc, Category.assoc, lineInfinitySection_comp, Category.comp_id]

/-- **`E = W ×_{𝐏¹_X} Z`**: the exceptional divisor is the inverse image of the centre `∞(Z)`,
which is the closed subscheme `∞ ∘ i : Z ⟶ 𝐏¹_X`. -/
theorem isPullback_exceptionalDivisorToCentre :
    IsPullback (exceptionalIdealAtInfinity i.ker).subschemeι (exceptionalDivisorToCentre i)
      (blowupAtInfinityToLine i.ker) (i ≫ lineInfinitySection X) :=
  isPullback_of_isClosedImmersion _ _ _ _ (exceptionalDivisorToCentre_comp i).symm (by
    rw [Scheme.IdealSheafData.ker_subschemeι, ker_comp_lineInfinitySection]
    rfl)

/-! ### The charts of `W` by the Rees algebras -/

section ReesChart

variable {Y : Scheme.{u}} (𝒥 : Y.IdealSheafData)

/-- The chart `Proj Γ(V)[𝒥(V) t] ⟶ Bl_𝒥 Y` of a blowup over an affine open `V`, through the
comparison of the two constructions of the blowup. -/
def blowUpReesChart (V : Y.affineOpens) :
    AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading (𝒥.ideal V)) ⟶ blowUp 𝒥 :=
  Stacks.Blowup.blowUpChart 𝒥 V ≫ (AlgebraicGeometry.blowUpIso 𝒥).inv

/-- **The Rees chart over `V` is the part of the blowup over `V`.** -/
theorem isPullback_blowUpReesChart (V : Y.affineOpens) :
    IsPullback (Proj.toSpecZero _ ≫ Spec.map (Stacks.Blowup.reesBase 𝒥 V))
      (blowUpReesChart 𝒥 V) V.2.fromSpec (blowUpToBase 𝒥) := by
  refine IsPullback.of_iso (Stacks.Blowup.isPullback_blowUpChart 𝒥 V) (Iso.refl _) V.2.isoSpec
    (AlgebraicGeometry.blowUpIso 𝒥).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [Stacks.RelativeProj.chartToOpen]
  · simp [blowUpReesChart]
  · rw [Iso.refl_hom, Category.comp_id]
    exact (IsAffineOpen.isoSpec_hom_fromSpec _).symm
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom,
      ← AlgebraicGeometry.blowUpIso_hom_blowUpToBase, Iso.inv_hom_id_assoc]

/-- **The Rees charts are compatible with restriction.** -/
theorem projMap_reesRestrict_blowUpReesChart {V V' : Y.affineOpens} (h : V' ≤ V) :
    Proj.map (Stacks.Blowup.reesRestrict 𝒥 h) (Stacks.Blowup.reesIrrelevant_le 𝒥 h) ≫
      blowUpReesChart 𝒥 V = blowUpReesChart 𝒥 V' := by
  rw [blowUpReesChart, blowUpReesChart, ← Category.assoc]
  congr 1
  exact colimit.w (Stacks.Blowup.reesData 𝒥).gluingData.functor (homOfLE h)

end ReesChart

/-! ### The chart of `E` over an affine open of `X` -/

section Chart

variable (U : X.affineOpens)

/-- `Z ∩ U` is an affine open of `Z`. -/
theorem isAffineOpen_centrePreimage : IsAffineOpen (i ⁻¹ᵁ U.1) := U.2.preimage i

omit [IsClosedImmersion i] in
/-- `∞ ∘ i` carries `Z ∩ U` into the chart at infinity over `U`. -/
theorem preimage_le_infinityChartAffineOpen :
    i ⁻¹ᵁ U.1 ≤ (i ≫ lineInfinitySection X) ⁻¹ᵁ (infinityChartAffineOpen U).1 := by
  intro z hz
  obtain ⟨y, hy⟩ := (IsAffineOpen.range_fromSpec (U.2 : IsAffineOpen U.1)).ge hz
  refine ⟨Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : Γ(X, U.1)))) y, trivial, ?_⟩
  have := congrArg (fun φ => φ y) (congrArg (fun g => (g.base : _ → _))
    (specMap_evalZero_infinityChartOver U))
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at this
  show (infinityChartOver U) _ = (i ≫ lineInfinitySection X) z
  rw [this, hy]
  rfl

/-- The Rees chart of the blowup at infinity over the chart at infinity over `U`. -/
def infinityReesChart :
    AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading
      ((infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U))) ⟶
      blowupAtInfinity i.ker :=
  blowUpReesChart (infinityCentreIdeal i.ker) (infinityChartAffineOpen U)

omit [IsClosedImmersion i] in
/-- The Rees chart over the chart at infinity is the part of `W` over that chart. -/
theorem isPullback_infinityReesChart :
    IsPullback (infinityReesChart i U)
      (Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom (algebraMap
        Γ(relativeProjectiveLine X, (infinityChartAffineOpen U).1)
        ↥(Stacks.Blowup.reesGrading
          ((infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U)) 0))))
      (blowupAtInfinityToLine i.ker) (infinityChartAffineOpen U).2.fromSpec :=
  (isPullback_blowUpReesChart (infinityCentreIdeal i.ker) (infinityChartAffineOpen U)).flip

/-- The ring map `Γ(𝐏¹_X, V) ⟶ Γ(Z, Z ∩ U)` of `∞ ∘ i`, `V` the chart at infinity over `U`. -/
def centreChartRingHom :
    Γ(relativeProjectiveLine X, (infinityChartAffineOpen U).1) ⟶ Γ(Z, i ⁻¹ᵁ U.1) :=
  (i ≫ lineInfinitySection X).appLE _ _ (preimage_le_infinityChartAffineOpen i U)

/-- `Γ(Z, Z ∩ U)` as an algebra over `Γ(𝐏¹_X, V)`, along `∞ ∘ i`. -/
instance centreChartAlgebra :
    Algebra Γ(relativeProjectiveLine X, (infinityChartAffineOpen U).1) Γ(Z, i ⁻¹ᵁ U.1) :=
  (centreChartRingHom i U).hom.toAlgebra

omit [IsClosedImmersion i] in
/-- The algebra map `Γ(𝐏¹_X, V) ⟶ Γ(Z, Z ∩ U)` is `centreChartRingHom`. -/
theorem algebraMap_centreChart :
    CommRingCat.ofHom (algebraMap Γ(relativeProjectiveLine X, (infinityChartAffineOpen U).1)
      Γ(Z, i ⁻¹ᵁ U.1)) = centreChartRingHom i U := rfl

/-- The grading of the Rees algebra `Γ(V)[𝒥(V) t]` of the centre over the chart at infinity. -/
abbrev centreReesGrading :=
  Stacks.Blowup.reesGrading ((infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U))

/-- **The graded ring `Γ(Z ∩ U) ⊗_{Γ(V)} Γ(V)[𝒥(V) t]`** of the chart of `E` over `U`. -/
abbrev centreChartRing :=
  Γ(Z, i ⁻¹ᵁ U.1) ⊗[Γ(relativeProjectiveLine X, (infinityChartAffineOpen U).1)]
    reesAlgebra ((infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U))

/-- The grading of `centreChartRing`, base changed from that of the Rees algebra. -/
abbrev centreChartGrading :=
  Stacks.ProjBaseChange.grading (centreReesGrading i U) Γ(Z, i ⁻¹ᵁ U.1)

/-- The structure morphism `Proj (centreChartRing) ⟶ Spec Γ(Z ∩ U)`. -/
abbrev centreChartToSpec :
    AlgebraicGeometry.Proj (centreChartGrading i U) ⟶ Spec (CommRingCat.of Γ(Z, i ⁻¹ᵁ U.1)) :=
  Proj.toSpecZero (centreChartGrading i U) ≫
    Spec.map (CommRingCat.ofHom (algebraMap Γ(Z, i ⁻¹ᵁ U.1) ↥(centreChartGrading i U 0)))

/-- The composite `Spec Γ(Z ∩ U) ⟶ Spec Γ(V) ⟶ 𝐏¹_X` is `Spec Γ(Z ∩ U) ⟶ Z ⟶ 𝐏¹_X`. -/
theorem specMap_centreChartRingHom_fromSpec :
    Spec.map (centreChartRingHom i U) ≫ (infinityChartAffineOpen U).2.fromSpec =
      (isAffineOpen_centrePreimage i U).fromSpec ≫ i ≫ lineInfinitySection X :=
  IsAffineOpen.SpecMap_appLE_fromSpec _ _ _ _

/-- **The part of `W` over `Z ∩ U`.** -/
theorem isPullback_centreChart_blowup :
    IsPullback (Stacks.ProjBaseChange.map (centreReesGrading i U) Γ(Z, i ⁻¹ᵁ U.1) ≫
        infinityReesChart i U)
      (centreChartToSpec i U) (blowupAtInfinityToLine i.ker)
      ((isAffineOpen_centrePreimage i U).fromSpec ≫ i ≫ lineInfinitySection X) := by
  rw [← specMap_centreChartRingHom_fromSpec, ← algebraMap_centreChart]
  exact (Stacks.ProjBaseChange.isPullback_map_Spec (centreReesGrading i U)
    Γ(Z, i ⁻¹ᵁ U.1)).paste_horiz (isPullback_infinityReesChart i U)

/-- **The chart `Proj (Γ(Z ∩ U) ⊗_{Γ(V)} Γ(V)[𝒥(V) t]) ⟶ E` of the exceptional divisor over
`U`.** -/
def exceptionalProjChart :
    AlgebraicGeometry.Proj (centreChartGrading i U) ⟶
      (exceptionalIdealAtInfinity i.ker).subscheme :=
  (isPullback_exceptionalDivisorToCentre i).lift
    (Stacks.ProjBaseChange.map (centreReesGrading i U) Γ(Z, i ⁻¹ᵁ U.1) ≫
      infinityReesChart i U)
    (centreChartToSpec i U ≫ (isAffineOpen_centrePreimage i U).fromSpec)
    ((isPullback_centreChart_blowup i U).w.trans (Category.assoc _ _ _).symm)

/-- The chart `Proj B_U ⟶ E ⟶ W` is the base change of the Rees chart. -/
@[reassoc (attr := simp)]
theorem exceptionalProjChart_subschemeι :
    exceptionalProjChart i U ≫ (exceptionalIdealAtInfinity i.ker).subschemeι =
      Stacks.ProjBaseChange.map (centreReesGrading i U) Γ(Z, i ⁻¹ᵁ U.1) ≫
        infinityReesChart i U :=
  IsPullback.lift_fst _ _ _ _

/-- The chart `Proj B_U ⟶ E ⟶ Z` is the structure morphism to `Z ∩ U`. -/
@[reassoc (attr := simp)]
theorem exceptionalProjChart_toCentre :
    exceptionalProjChart i U ≫ exceptionalDivisorToCentre i =
      centreChartToSpec i U ≫ (isAffineOpen_centrePreimage i U).fromSpec :=
  IsPullback.lift_snd _ _ _ _

/-- The chart over `U` is the part of `E` over `Z ∩ U`, as a square over `Z`. -/
theorem isPullback_exceptionalProjChart_centre :
    IsPullback (exceptionalProjChart i U) (centreChartToSpec i U)
      (exceptionalDivisorToCentre i) (isAffineOpen_centrePreimage i U).fromSpec :=
  IsPullback.of_right (by simpa using isPullback_centreChart_blowup i U)
    (exceptionalProjChart_toCentre i U) (isPullback_exceptionalDivisorToCentre i)

/-- The structure morphism of the chart of `E` over `U`, to `U`. -/
def exceptionalProjChartToOpen : AlgebraicGeometry.Proj (centreChartGrading i U) ⟶ U.1.toScheme :=
  centreChartToSpec i U ≫ (isAffineOpen_centrePreimage i U).isoSpec.inv ≫ (i ∣_ U.1)

/-- **The chart of `E` over `U` is the part of `E` lying over `U`.** -/
theorem isPullback_exceptionalProjChart :
    IsPullback (exceptionalProjChartToOpen i U) (exceptionalProjChart i U) U.1.ι
      (exceptionalDivisorToCentre i ≫ i) := by
  have h2 : IsPullback (isAffineOpen_centrePreimage i U).fromSpec
      ((isAffineOpen_centrePreimage i U).isoSpec.inv ≫ (i ∣_ U.1)) i U.1.ι :=
    IsPullback.of_iso (isPullback_morphismRestrict i U.1).flip
      (isAffineOpen_centrePreimage i U).isoSpec (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.comp_id, IsAffineOpen.isoSpec_hom_fromSpec])
      (by simp) (by simp) (by simp)
  exact ((isPullback_exceptionalProjChart_centre i U).paste_vert h2).flip

/-- The chart of `E` over `U` is an open immersion into `E`. -/
instance (U : X.affineOpens) : IsOpenImmersion (exceptionalProjChart i U) :=
  MorphismProperty.of_isPullback (isPullback_exceptionalProjChart i U) inferInstance

end Chart

/-! ### The charts of `E` are compatible with restriction -/

section Restrict

variable {U V : X.affineOpens}

/-- The charts at infinity are nested. -/
theorem infinityChartAffineOpen_le (h : V.1 ≤ U.1) :
    (infinityChartAffineOpen V).1 ≤ (infinityChartAffineOpen U).1 := by
  rintro _ ⟨x, -, rfl⟩
  refine ⟨Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (affineRestrict h))) x, trivial, ?_⟩
  rw [← specMap_map_infinityChartOver h]
  rfl

/-- The charts at infinity are nested, as affine opens. -/
theorem infinityChartAffineOpen_mono (h : V.1 ≤ U.1) :
    infinityChartAffineOpen V ≤ infinityChartAffineOpen U :=
  infinityChartAffineOpen_le h

/-- The restriction `Γ(𝐏¹_X, V_U) ⟶ Γ(𝐏¹_X, V_V)` of the charts at infinity. -/
abbrev lineChartRestrict (h : V.1 ≤ U.1) :
    Γ(relativeProjectiveLine X, (infinityChartAffineOpen U).1) ⟶
      Γ(relativeProjectiveLine X, (infinityChartAffineOpen V).1) :=
  (relativeProjectiveLine X).presheaf.map (homOfLE (infinityChartAffineOpen_le h)).op

/-- The restriction `Γ(Z, Z ∩ U) ⟶ Γ(Z, Z ∩ V)`. -/
abbrev centreRestrict (h : V.1 ≤ U.1) : Γ(Z, i ⁻¹ᵁ U.1) ⟶ Γ(Z, i ⁻¹ᵁ V.1) :=
  Z.presheaf.map (homOfLE (i.preimage_mono h)).op

omit [IsClosedImmersion i] in
/-- `Γ(𝐏¹_X, V) ⟶ Γ(Z, Z ∩ U)` is compatible with restriction. -/
theorem centreChartRingHom_restrict (h : V.1 ≤ U.1) :
    lineChartRestrict h ≫ centreChartRingHom i V =
      centreChartRingHom i U ≫ centreRestrict i h := by
  rw [centreChartRingHom, centreChartRingHom, Scheme.Hom.map_appLE]
  exact (Scheme.Hom.appLE_map _ _ _).symm

/-- The Rees algebra of the centre, restricted from the chart at infinity over `U` to that over
`V`. -/
abbrev centreReesRestrict (h : V.1 ≤ U.1) : centreReesGrading i U →+*ᵍ centreReesGrading i V :=
  Stacks.Blowup.reesRestrict (infinityCentreIdeal i.ker) (infinityChartAffineOpen_mono h)

/-- The `Γ(𝐏¹_X, V_U)`-algebra structure of `centreChartRing i V` along the restriction. -/
abbrev centreChartRingAlgebra (h : V.1 ≤ U.1) :
    Algebra Γ(relativeProjectiveLine X, (infinityChartAffineOpen U).1) (centreChartRing i V) :=
  ((algebraMap Γ(relativeProjectiveLine X, (infinityChartAffineOpen V).1)
    (centreChartRing i V)).comp (lineChartRestrict h).hom).toAlgebra

/-- The `Γ(𝐏¹_X, V_U)`-algebra map `Γ(Z, Z ∩ U) ⟶ centreChartRing i V`, `s ↦ s|_V ⊗ 1`. -/
def centreChartRestrictLeft (h : V.1 ≤ U.1) :
    letI := centreChartRingAlgebra i h
    Γ(Z, i ⁻¹ᵁ U.1) →ₐ[Γ(relativeProjectiveLine X, (infinityChartAffineOpen U).1)]
      centreChartRing i V :=
  letI := centreChartRingAlgebra i h
  { toRingHom := (Algebra.TensorProduct.includeLeftRingHom (R :=
      Γ(relativeProjectiveLine X, (infinityChartAffineOpen V).1))).comp (centreRestrict i h).hom,
    commutes' := fun r => by
      change (centreRestrict i h).hom (algebraMap _ _ r) ⊗ₜ 1 =
        algebraMap Γ(relativeProjectiveLine X, (infinityChartAffineOpen V).1)
          (centreChartRing i V) ((lineChartRestrict h).hom r)
      rw [Algebra.TensorProduct.algebraMap_apply]
      congr 1
      exact (congrArg (fun φ => (CommRingCat.Hom.hom φ) r) (centreChartRingHom_restrict i h)).symm }

/-- The `Γ(𝐏¹_X, V_U)`-algebra map from the Rees algebra of the centre over `V_U` to
`centreChartRing i V`, `f ↦ 1 ⊗ f|_V`. -/
def centreChartRestrictRight (h : V.1 ≤ U.1) :
    letI := centreChartRingAlgebra i h
    reesAlgebra ((infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U)) →ₐ[
      Γ(relativeProjectiveLine X, (infinityChartAffineOpen U).1)] centreChartRing i V :=
  letI := centreChartRingAlgebra i h
  { toRingHom := (Algebra.TensorProduct.includeRight.toRingHom).comp
      (centreReesRestrict i h).toRingHom,
    commutes' := fun r => by
      change (1 : Γ(Z, i ⁻¹ᵁ V.1)) ⊗ₜ ((centreReesRestrict i h) (algebraMap _ _ r)) =
        algebraMap Γ(relativeProjectiveLine X, (infinityChartAffineOpen V).1)
          (centreChartRing i V) ((lineChartRestrict h).hom r)
      rw [Algebra.TensorProduct.algebraMap_apply']
      congr 1
      refine Subtype.ext ?_
      change Polynomial.map _ (Polynomial.C r) = Polynomial.C _
      rw [Polynomial.map_C]
      rfl }

/-- **The restriction of the graded rings of the charts of `E` from `U` to `V ⊆ U`**:
`s ⊗ f ↦ s|_V ⊗ f|_V`. -/
def centreChartRestrictRingHom (h : V.1 ≤ U.1) : centreChartRing i U →+* centreChartRing i V :=
  letI := centreChartRingAlgebra i h
  (Algebra.TensorProduct.lift (centreChartRestrictLeft i h) (centreChartRestrictRight i h)
    (fun _ _ => Commute.all _ _)).toRingHom

omit [IsClosedImmersion i] in
/-- `centreChartRestrictRingHom` on a pure tensor. -/
@[simp]
theorem centreChartRestrictRingHom_tmul (h : V.1 ≤ U.1) (s : Γ(Z, i ⁻¹ᵁ U.1))
    (f : reesAlgebra ((infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U))) :
    centreChartRestrictRingHom i h (s ⊗ₜ f) =
      (centreRestrict i h).hom s ⊗ₜ centreReesRestrict i h f := by
  show ((centreRestrict i h).hom s ⊗ₜ[Γ(relativeProjectiveLine X,
      (infinityChartAffineOpen V).1)] (1 : reesAlgebra ((infinityCentreIdeal i.ker).ideal
        (infinityChartAffineOpen V)))) * ((1 : Γ(Z, i ⁻¹ᵁ V.1)) ⊗ₜ centreReesRestrict i h f) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The restriction of the graded rings, as a homomorphism of graded rings. -/
def centreChartRestrict (h : V.1 ≤ U.1) : centreChartGrading i U →+*ᵍ centreChartGrading i V where
  toRingHom := centreChartRestrictRingHom i h
  map_mem := by
    rintro n _ ⟨w, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | tmul s y =>
      rw [LinearMap.baseChange_tmul]
      change centreChartRestrictRingHom i h (s ⊗ₜ (y : reesAlgebra _)) ∈ _
      rw [centreChartRestrictRingHom_tmul]
      exact Submodule.tmul_mem_baseChange_of_mem _ ((centreReesRestrict i h).map_mem y.2)
    | add w w' hw hw' => rw [map_add, map_add]; exact add_mem hw hw'

omit [IsClosedImmersion i] in
/-- `centreChartRestrict` is compatible with the inclusions of the Rees algebras. -/
theorem centreChartRestrict_comp_includeRight (h : V.1 ≤ U.1) :
    (centreChartRestrict i h).comp
      (Stacks.ProjBaseChange.includeRight (centreReesGrading i U) Γ(Z, i ⁻¹ᵁ U.1)) =
      (Stacks.ProjBaseChange.includeRight (centreReesGrading i V) Γ(Z, i ⁻¹ᵁ V.1)).comp
        (centreReesRestrict i h) :=
  GradedRingHom.ext fun f => by
    show centreChartRestrictRingHom i h (1 ⊗ₜ f) = _
    rw [centreChartRestrictRingHom_tmul, map_one]
    rfl

/-- **The restriction `Proj B_V ⟶ Proj B_U` of the charts of `E`.** -/
def exceptionalProjChartRestrict (h : V.1 ≤ U.1) :
    AlgebraicGeometry.Proj (centreChartGrading i V) ⟶
      AlgebraicGeometry.Proj (centreChartGrading i U) :=
  Stacks.ProjBaseChange.mapOfComp (centreReesRestrict i h)
    (Stacks.Blowup.reesIrrelevant_le (infinityCentreIdeal i.ker) (infinityChartAffineOpen_mono h))
    (centreChartRestrict i h) (centreChartRestrict_comp_includeRight i h)

omit [IsClosedImmersion i] in
/-- `centreChartRestrict` on scalars. -/
theorem centreChartRestrict_algebraMap (h : V.1 ≤ U.1) (s : Γ(Z, i ⁻¹ᵁ U.1)) :
    centreChartRestrict i h (algebraMap _ (centreChartRing i U) s) =
      algebraMap _ (centreChartRing i V) ((centreRestrict i h).hom s) := by
  show centreChartRestrictRingHom i h (s ⊗ₜ 1) = (centreRestrict i h).hom s ⊗ₜ 1
  rw [centreChartRestrictRingHom_tmul, map_one]

omit [IsClosedImmersion i] in
/-- `exceptionalProjChartRestrict` is compatible with the projections to `Proj` of the Rees
algebras. -/
theorem exceptionalProjChartRestrict_map (h : V.1 ≤ U.1) :
    exceptionalProjChartRestrict i h ≫
        Stacks.ProjBaseChange.map (centreReesGrading i U) Γ(Z, i ⁻¹ᵁ U.1) =
      Stacks.ProjBaseChange.map (centreReesGrading i V) Γ(Z, i ⁻¹ᵁ V.1) ≫
        Proj.map (centreReesRestrict i h) (Stacks.Blowup.reesIrrelevant_le
          (infinityCentreIdeal i.ker) (infinityChartAffineOpen_mono h)) :=
  Stacks.ProjBaseChange.mapOfComp_map _ _ _ _

/-- **The charts of `E` are compatible with restriction**: for affine opens `V ⊆ U` of `X`, the
chart over `V` is the restriction of the chart over `U`. -/
theorem exceptionalProjChartRestrict_exceptionalProjChart (h : V.1 ≤ U.1) :
    exceptionalProjChartRestrict i h ≫ exceptionalProjChart i U = exceptionalProjChart i V := by
  rw [← cancel_mono (exceptionalIdealAtInfinity i.ker).subschemeι, Category.assoc,
    exceptionalProjChart_subschemeι, exceptionalProjChart_subschemeι, ← Category.assoc,
    exceptionalProjChartRestrict_map, Category.assoc]
  exact congrArg (Stacks.ProjBaseChange.map (centreReesGrading i V) Γ(Z, i ⁻¹ᵁ V.1) ≫ ·)
    (projMap_reesRestrict_blowUpReesChart (infinityCentreIdeal i.ker) _)

end Restrict

end Stacks.Chow

end
