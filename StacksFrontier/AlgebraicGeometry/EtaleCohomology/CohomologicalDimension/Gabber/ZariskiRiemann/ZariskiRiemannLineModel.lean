module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ZariskiRiemannCenter
public import StacksFrontier.AlgebraicGeometry.TwoGeneratorProper

/-!
# Zariski's theorem: every element of `V` is regular at the center of some model

Let `B` be a domain with fraction field `K` and `V` a valuation subring of `K` containing `B`.
For every `x ∈ V` there is a proper model `Y ⟶ Spec B` of `Spec K` on which `x` is a regular
function at the center `y_Y(V)`: the image of `𝒪_{Y, y_Y(V)} ⟶ V` contains `x`. Together with
the monotonicity of these images along refinements
(`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.centerRange_mono`), this says that
`V` is the union, i.e. the filtered colimit over the models, of the images of the local rings at
the centers (Zariski–Samuel VI §17; the input of the Zariski–Riemann limit in the last remark of
Travaux de Gabber, Exposé XVIII-A, §2).

The model is the projective line `ℙ¹_B = Proj B[T₀,T₁]` with `η = Spec K` sent to the point
`[1 : x]`. Its chart `D₊(T₀) = Spec B[T₁/T₀]` receives `Spec V` through `T₁/T₀ ↦ x`, because
`x ∈ V`; by uniqueness of the center this is the center of `V`, and the function `T₁/T₀` on the
chart has value `x` at the center. (The graph of `x`, i.e. the blowup of the ideal `(1, x)`, is
the scheme-theoretic closure of `η` in `ℙ¹_B`; any proper model with a point at `η` will do for
the system of `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel`.)

`ℙ¹_B` is realized as `Proj (B[T₀,T₁]/(0·T₀ - 0·T₁))`, the two-generator modification of
`StacksFrontier/AlgebraicGeometry/TwoGeneratorSquare.lean` for `f₁ = f₂ = 0`, whose properness over
`Spec B` is `Stacks.AlmostBlowUp.isProper_modificationToBase`.

## Main definitions

* `AlgebraicGeometry.Scheme.ZariskiRiemann.lineChart` — the ring map
  `B[T₀,T₁]_{(T₀)} → S`, `T₁/T₀ ↦ s`, of the chart `D₊(T₀)` to a `B`-algebra `S`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.lineModel` — the model `ℙ¹_B` with `η ↦ [1 : x]`.

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.lineModel_center` — the center of `V` on `ℙ¹_B` is
  `Spec V ⟶ D₊(T₀) ⊆ ℙ¹_B`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.exists_mem_centerRange` — **Zariski's theorem**: every
  `x ∈ V` lies in the image of `𝒪_{Y, y_Y(V)} ⟶ V` for some model `Y`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.iSup_centerRange` — the images of the local rings at
  the centers exhaust `V`.

## References

* O. Zariski, P. Samuel, *Commutative Algebra*, Vol. II, Chapter VI, §17
* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing HomogeneousLocalization Stacks.AlmostBlowUp

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

/-- The image of `𝒪_{X, f 𝔪} ⟶ R` does not change when `f : Spec R ⟶ X` is followed by an open
immersion. -/
theorem range_stalkClosedPointTo_comp_of_isOpenImmersion {R : CommRingCat.{u}} [IsLocalRing R]
    {X Y : Scheme.{u}} (f : Spec R ⟶ X) (g : X ⟶ Y) [IsOpenImmersion g] :
    (Scheme.stalkClosedPointTo (f ≫ g)).hom.range = (Scheme.stalkClosedPointTo f).hom.range := by
  refine le_antisymm (range_stalkClosedPointTo_comp_le f g) ?_
  rintro _ ⟨a, rfl⟩
  -- the instance is named: a bare search for `IsIso (g.stalkMap _)` times out at `whnf`
  -- (still so with the instances of `Stacks.Models.RegularModelSituation` scoped away)
  have := IsOpenImmersion.instIsIsoCommRingCatStalkMap g (f (closedPoint R))
  have e : inv (g.stalkMap (f (closedPoint R))) ≫ Scheme.stalkClosedPointTo (f ≫ g) =
      Scheme.stalkClosedPointTo f := by
    rw [Scheme.stalkClosedPointTo_comp, IsIso.inv_hom_id_assoc]
  exact ⟨(inv (g.stalkMap (f (closedPoint R)))).hom a, congr($e a)⟩

/-- For a ring map `φ : R ⟶ S` to a local ring, every `φ r` is in the image of the local ring of
`Spec R` at the image of the closed point. -/
theorem mem_range_stalkClosedPointTo_specMap {R S : CommRingCat.{u}} [IsLocalRing S]
    (φ : R ⟶ S) (r : R) : φ.hom r ∈ (Scheme.stalkClosedPointTo (Spec.map φ)).hom.range := by
  refine ⟨((Spec R).presheaf.germ ⊤ ((Spec.map φ) (closedPoint S)) trivial).hom
    ((Scheme.ΓSpecIso R).inv.hom r), ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.germ_stalkClosedPointTo_Spec, ← CommRingCat.comp_apply,
    Iso.inv_hom_id_assoc]

section Line

variable (A : Type u) [CommRing A]

/-- The grading of `B[T₀,T₁]`, read as the two-generator relation quotient for `f₁ = f₂ = 0`. -/
@[reducible]
def lineGradedRing : GradedRing (modificationGrading A 0 0) :=
  (twoGeneratorSquare A 0 0).modificationGraded

attribute [local instance] lineGradedRing

/-- The coordinate `Tᵢ` of `B[T₀,T₁]`. -/
def lineT (i : Fin 2) : modificationRing A 0 0 :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

/-- The coordinates have degree one. -/
theorem lineT_mem (i : Fin 2) : lineT A i ∈ modificationGrading A 0 0 1 :=
  AddSubgroup.mem_map_of_mem _
    ((Submodule.mem_toAddSubgroup _).mpr
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X A i)))

/-- For `f₁ = f₂ = 0` the relation ideal `(0·T₀ - 0·T₁)` is zero. -/
theorem relationIdeal_zero_zero : relationIdeal A 0 0 = ⊥ := by
  simp [relationIdeal]

variable {A} {S S' : Type*} [CommRing S] [CommRing S']

/-- The evaluation `B[T₀,T₁] → S`, `T₀ ↦ 1`, `T₁ ↦ s`, over `g : B → S`. -/
def lineEval (g : A →+* S) (s : S) : modificationRing A 0 0 →+* S :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom g ![1, s]) fun a ha => by
    rw [relationIdeal_zero_zero] at ha
    rw [(Ideal.mem_bot).mp ha, map_zero]

/-- The evaluation sends the constant `a` to `g a`. -/
@[simp]
theorem lineEval_C (g : A →+* S) (s : S) (a : A) :
    lineEval g s (Ideal.Quotient.mk _ (MvPolynomial.C a)) = g a := by
  simp [lineEval]

/-- The evaluation sends `T₀` to `1` and `T₁` to `s`. -/
@[simp]
theorem lineEval_X (g : A →+* S) (s : S) (i : Fin 2) :
    lineEval g s (Ideal.Quotient.mk _ (MvPolynomial.X i)) = ![1, s] i := by
  simp [lineEval]

/-- The evaluation sends `T₀` to `1`. -/
theorem lineEval_lineT_zero (g : A →+* S) (s : S) : lineEval g s (lineT A 0) = 1 := by
  simp [lineT]

/-- The evaluation sends `T₁` to `s`. -/
theorem lineEval_lineT_one (g : A →+* S) (s : S) : lineEval g s (lineT A 1) = s := by
  simp [lineT]

/-- The image of `T₀` under the evaluation is a unit. -/
theorem isUnit_lineEval_lineT_zero (g : A →+* S) (s : S) : IsUnit (lineEval g s (lineT A 0)) := by
  rw [lineEval_lineT_zero]
  exact isUnit_one

/-- **The chart `D₊(T₀) = Spec B[T₁/T₀]` mapping to `Spec S`**: the ring map
`B[T₀,T₁]_{(T₀)} → S` with `T₁/T₀ ↦ s`, over `g : B → S`. -/
def lineChart (g : A →+* S) (s : S) : Away (modificationGrading A 0 0) (lineT A 0) →+* S :=
  (IsLocalization.Away.lift (lineT A 0) (isUnit_lineEval_lineT_zero g s)).comp
    (algebraMap _ (Localization.Away (lineT A 0)))

/-- The chart map is natural in the target. -/
theorem comp_lineChart (φ : S →+* S') (g : A →+* S) (s : S) :
    φ.comp (lineChart g s) = lineChart (φ.comp g) (φ s) := by
  simp only [lineChart, ← RingHom.comp_assoc]
  congr 1
  apply IsLocalization.ringHom_ext (Submonoid.powers (lineT A 0))
  rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, IsLocalization.Away.lift_comp]
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    fin_cases i <;> simp

/-- The chart map on the degree-zero part `B` is `g`. -/
theorem lineChart_comp_base (g : A →+* S) (s : S) :
    (lineChart g s).comp ((fromZeroRingHom (modificationGrading A 0 0)
      (Submonoid.powers (lineT A 0))).comp (baseRingHom A 0 0)) = g := by
  ext a
  have h : (fromZeroRingHom (modificationGrading A 0 0) (Submonoid.powers (lineT A 0))
      (baseRingHom A 0 0 a)).val =
        algebraMap (modificationRing A 0 0) (Localization.Away (lineT A 0))
          (Ideal.Quotient.mk _ (MvPolynomial.C a)) := by
    rw [← Localization.mk_one_eq_algebraMap]
    rfl
  simp only [lineChart, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, h,
    IsLocalization.Away.lift_eq, lineEval_C]

/-- The function `T₁/T₀` on the chart. -/
def lineCoord : Away (modificationGrading A 0 0) (lineT A 0) :=
  Away.mk _ (lineT_mem A 0) 1 (lineT A 1) (by simpa only [one_nsmul] using lineT_mem A 1)

/-- The chart map sends `T₁/T₀` to `s`. -/
theorem lineChart_lineCoord (g : A →+* S) (s : S) : lineChart g s lineCoord = s := by
  have key : ∀ z : Localization.Away (lineT A 0),
      z * algebraMap _ _ (lineT A 0 ^ 1) = algebraMap _ _ (lineT A 1) →
        IsLocalization.Away.lift (lineT A 0) (isUnit_lineEval_lineT_zero g s) z = s := by
    intro z hz
    have := congrArg (IsLocalization.Away.lift (lineT A 0) (isUnit_lineEval_lineT_zero g s)) hz
    simpa [lineEval_lineT_zero, lineEval_lineT_one] using this
  apply key
  simp only [lineCoord, HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  rw [Localization.mk_eq_mk']
  exact IsLocalization.mk'_spec _ _ _

/-- The chart `D₊(T₀) ⊆ ℙ¹_B`. -/
def lineChartι : Spec (.of (Away (modificationGrading A 0 0) (lineT A 0))) ⟶
    Proj (modificationGrading A 0 0) :=
  Proj.awayι _ (lineT A 0) (lineT_mem A 0) one_pos

/-- The chart `D₊(T₀) ⟶ ℙ¹_B` is an open immersion. -/
instance : IsOpenImmersion (lineChartι (A := A)) := by
  unfold lineChartι
  infer_instance

/-- The point `Spec S ⟶ D₊(T₀) ⊆ ℙ¹_B` lies over `Spec g : Spec S ⟶ Spec B`. -/
@[reassoc]
theorem lineChart_comp_toBase {S : Type u} [CommRing S] (g : A →+* S) (s : S) :
    Spec.map (CommRingCat.ofHom (lineChart g s)) ≫ lineChartι ≫ modificationToBase A 0 0 =
      Spec.map (CommRingCat.ofHom g) := by
  rw [lineChartι, modificationToBase, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  ext a
  exact congr($(lineChart_comp_base g s) a)

end Line

attribute [local instance] lineGradedRing

variable (B : Type u) [CommRing B] [IsDomain B]

/-- **The projective line model** `ℙ¹_B ⟶ Spec B` of `η = Spec (Frac B)`, with `η` sent to the
point `[1 : x]` of the chart `D₊(T₀)`. -/
abbrev lineModel (x : FractionRing B) : ProperModel B where
  Y := Proj (modificationGrading B 0 0)
  f := modificationToBase B 0 0
  isProper := isProper_modificationToBase B 0 0
  j := Spec.map (CommRingCat.ofHom (lineChart (algebraMap B (FractionRing B)) x)) ≫ lineChartι
  fac := by rw [Category.assoc, lineChart_comp_toBase]

variable {B} (V : ValuationSubring (FractionRing B))
  (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V)

/-- The map `B → V` followed by `V ⊆ Frac B` is the algebra map `B → Frac B`. -/
theorem algebraMap_comp_valuationSubringBaseMap :
    (algebraMap V (FractionRing B)).comp (valuationSubringBaseMap V hV) =
      algebraMap B (FractionRing B) :=
  RingHom.ext fun _ => rfl

/-- **The center of `V` on `ℙ¹_B` for `x ∈ V`** is `Spec V ⟶ D₊(T₀) ⊆ ℙ¹_B`, given by
`T₁/T₀ ↦ x`. -/
theorem lineModel_center (x : V) :
    Spec.map (CommRingCat.ofHom (lineChart (valuationSubringBaseMap V hV) x)) ≫ lineChartι =
      (lineModel B x).center V hV := by
  have h₁ : Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing B))) ≫
      Spec.map (CommRingCat.ofHom (lineChart (valuationSubringBaseMap V hV) x)) ≫ lineChartι =
        Spec.map (CommRingCat.ofHom (lineChart (algebraMap B (FractionRing B))
          (x : FractionRing B))) ≫ lineChartι := by
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, comp_lineChart,
      algebraMap_comp_valuationSubringBaseMap]
    rfl
  have h₂ : (Spec.map (CommRingCat.ofHom (lineChart (valuationSubringBaseMap V hV) x)) ≫
      lineChartι) ≫ modificationToBase B 0 0 =
        Spec.map (CommRingCat.ofHom (valuationSubringBaseMap V hV)) := by
    rw [Category.assoc, lineChart_comp_toBase]
  exact (lineModel B x).eq_center V hV h₁ h₂

/-- **Zariski's theorem** (Zariski–Samuel VI §17): for a valuation subring `V` of `Frac B`
containing `B`, every `x ∈ V` is the value at the center `y_Y(V)` of a regular function on some
proper model `Y`: it lies in the image of `𝒪_{Y, y_Y(V)} ⟶ V`. -/
theorem exists_mem_centerRange (x : V) : ∃ M : ProperModel B, x ∈ M.centerRange V hV := by
  refine ⟨lineModel B x, ?_⟩
  have h : lineChart (valuationSubringBaseMap V hV) x lineCoord ∈ (Scheme.stalkClosedPointTo
      (Spec.map (CommRingCat.ofHom (lineChart (valuationSubringBaseMap V hV) x)))).hom.range :=
    mem_range_stalkClosedPointTo_specMap
      (CommRingCat.ofHom (lineChart (valuationSubringBaseMap V hV) x)) lineCoord
  rw [lineChart_lineCoord] at h
  have key : ∀ l : Spec (.of V) ⟶ Proj (modificationGrading B 0 0),
      l = Spec.map (CommRingCat.ofHom (lineChart (valuationSubringBaseMap V hV) x)) ≫
        lineChartι → x ∈ (Scheme.stalkClosedPointTo l).hom.range := by
    rintro l rfl
    rw [range_stalkClosedPointTo_comp_of_isOpenImmersion]
    exact h
  exact key _ (lineModel_center V hV x).symm

/-- The images in `V` of the local rings `𝒪_{Y, y_Y(V)}` at the centers, over all proper models,
exhaust `V`. -/
theorem iSup_centerRange : ⨆ M : ProperModel B, M.centerRange V hV = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨M, hM⟩ := exists_mem_centerRange V hV x
  exact le_iSup (fun M : ProperModel B => M.centerRange V hV) M hM

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
