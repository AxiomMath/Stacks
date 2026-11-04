module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PowerSumNewtonComplex

/-!
# The power sums and the Chern character of a perfect object

Let `X` be locally of finite type over the base of chapter 42 and let `E ∈ D(𝒪_X)` be an object
whose Chern classes are defined (Stacks 0F9E (1)). Stacks 0GUD constructs, besides the total
Chern class, the power sums `P_p(E) ∈ A^p(X)` and the Chern character `ch_p(E) = P_p(E)/p!`:
`P_p(E)` is the unique class whose restriction along the envelope `f : Y ⟶ X` of a presentation
of `E` by a locally bounded complex `𝓔^•` of finite locally free `𝒪_Y`-modules is `P_p(𝓔^•)`.
This file carries out that construction for the power sums and proves restriction,
`P_p(0) = 0`, and `P_p(ℰ[0]) = P_p(ℰ)` for a finite locally free `ℰ`.

## Main results

* `Stacks.Chow.res_perfectPowerSum_eq_powerSumComplex`, `Stacks.Chow.eq_perfectPowerSum`,
  `Stacks.Chow.existsUnique_forall_res_eq_powerSumComplex` — Stacks 0GUD for `P_p`.
* `Stacks.Chow.res_perfectPowerSum_derivedPullback` — `res_g P_p(E) = P_p(Lg^*E)`.
* `Stacks.Chow.perfectPowerSum_of_isZero` — `P_p(0) = 0`.
* `Stacks.Chow.perfectPowerSum_eq_powerSumOfFiniteLocallyFree` — `P_p(ℰ[0]) = P_p(ℰ)`.

## Implementation notes

The class `P_p(E)` itself is `Stacks.Chow.perfectPowerSum`, defined by Newton's recursion of
Stacks 0F9B in the Chern classes of `E`, with components `Stacks.Chow.perfectPowerSumComponent`
and `Stacks.Chow.perfectChernCharacterComponent`. It restricts to the class
`Stacks.Chow.complexPowerSum` of a presenting complex, which is the alternating sum
`Stacks.Chow.powerSumComplex` of the source by `Stacks.Chow.powerSumComplex_eq_complexPowerSum`;
so the class this file characterizes is that one.

## References

* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

section PerfectPowerSum

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {E : DerivedCategory X.Modules}

/-- Pulling back two envelope presentations of `E` along morphisms with equal composites to `X`
gives complexes with the same power sums. -/
theorem powerSumComplex_pullbackComplex_eq (H H' : EnvelopePresentation E) {Z : Scheme.{u}}
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (h : Z ⟶ H.Y) (h' : Z ⟶ H'.Y)
    (e : h ≫ H.f = h' ≫ H'.f) (p : ℕ) :
    powerSumComplex C sZ
        (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback h H.P H.locallyBounded)
        p =
      powerSumComplex C sZ
        (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback h' H'.P
          H'.locallyBounded) p :=
  powerSumComplex_eq_of_iso C sZ _ _ (H.pullbackRepresentationIso H' h h' e) p

/-- The power sums of two presentations agree after restriction along morphisms with equal
composites to `X`. -/
theorem res_powerSumComplex_eq_res_powerSumComplex (H H' : EnvelopePresentation E)
    {Z : Scheme.{u}} {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] (h : Z ⟶ H.Y)
    [LocallyOfFiniteType h] (h' : Z ⟶ H'.Y) [LocallyOfFiniteType h'] (e : h ≫ H.f = h' ≫ H'.f)
    (hs : h ≫ (H.f ≫ sX) = sZ) (hs' : h' ≫ (H'.f ≫ sX) = sZ) (p : ℕ) :
    TotalChowClass.res h hs (powerSumComplex C (H.f ≫ sX) H.locallyBounded p) =
      TotalChowClass.res h' hs' (powerSumComplex C (H'.f ≫ sX) H'.locallyBounded p) := by
  rw [res_powerSumComplex, res_powerSumComplex]
  exact powerSumComplex_pullbackComplex_eq C H H' sZ h h' e p

/-- For an envelope presentation `H` of `E` there is a unique total class whose restriction along
the envelope `H.f` is the power sum `P_p` of the presenting complex. -/
theorem existsUnique_res_eq_powerSumComplex (H : EnvelopePresentation E) (p : ℕ) :
    ∃! c : TotalChowClass C sX,
      TotalChowClass.res H.f rfl c = powerSumComplex C (H.f ≫ sX) H.locallyBounded p :=
  TotalChowClass.existsUnique_res_eq_of_isEnvelope H.f H.envelope rfl _
    (res_powerSumComplex_eq_res_powerSumComplex C sX H H (pullback.fst H.f H.f)
      (pullback.snd H.f H.f) pullback.condition rfl _ p)

/-- **The characterization of `P_p(E)`, at every presentation**: `P_p(E)` restricts along the
envelope of a presentation to the alternating sum `P_p(ℰ^•) = ∑_n (-1)^n P_p(ℰ^n)` of the
presenting complex. -/
theorem res_perfectPowerSum_eq_powerSumComplex (hE : HasDefinedChernClasses E)
    (H : EnvelopePresentation E) (p : ℕ) :
    TotalChowClass.res H.f rfl (perfectPowerSum C sX hE p) =
      powerSumComplex C (H.f ≫ sX) H.locallyBounded p :=
  (res_perfectPowerSum C sX hE H p).trans
    (powerSumComplex_eq_complexPowerSum C (H.f ≫ sX) H.locallyBounded p).symm

/-- **Uniqueness of `P_p(E)`.** -/
theorem eq_perfectPowerSum (hE : HasDefinedChernClasses E) (H : EnvelopePresentation E) (p : ℕ)
    {c : TotalChowClass C sX}
    (hc : TotalChowClass.res H.f rfl c = powerSumComplex C (H.f ≫ sX) H.locallyBounded p) :
    c = perfectPowerSum C sX hE p :=
  TotalChowClass.res_injective_of_isEnvelope H.f H.envelope rfl
    (hc.trans (res_perfectPowerSum_eq_powerSumComplex C sX hE H p).symm)

/-- **Existence and uniqueness of `P_p(E)`.** If the Chern classes of `E` are defined, there is a
unique total class `P_p(E)` whose restriction along the envelope of every presentation of `E` by a
locally bounded complex `𝓔^•` of finite locally free modules is `P_p(𝓔^•)`. -/
theorem existsUnique_forall_res_eq_powerSumComplex (hE : HasDefinedChernClasses E) (p : ℕ) :
    ∃! c : TotalChowClass C sX, ∀ H : EnvelopePresentation E,
      TotalChowClass.res H.f rfl c = powerSumComplex C (H.f ≫ sX) H.locallyBounded p :=
  ⟨perfectPowerSum C sX hE p, fun H ↦ res_perfectPowerSum_eq_powerSumComplex C sX hE H p,
    fun _ hc ↦ eq_perfectPowerSum C sX hE hE.some p (hc hE.some)⟩

/-- **Restriction of `P_p(E)`**: `res_g P_p(E) = P_p(Lg^*E)` for `g : X' ⟶ X` locally of finite
type. -/
theorem res_perfectPowerSum_derivedPullback (hE : HasDefinedChernClasses E) {X' : Scheme.{u}}
    {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX'] (g : X' ⟶ X) [LocallyOfFiniteType g]
    (hs : g ≫ sX = sX')
    (hE' : HasDefinedChernClasses
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj E))
    (p : ℕ) :
    TotalChowClass.res g hs (perfectPowerSum C sX hE p) = perfectPowerSum C sX' hE' p := by
  set H := hE.some
  refine eq_perfectPowerSum C sX' hE' (H.derivedPullback g) p ?_
  have e : pullback.snd H.f g ≫ g = pullback.fst H.f g ≫ H.f :=
    (pullback.condition (f := H.f) (g := g)).symm
  have hs2 : pullback.fst H.f g ≫ (H.f ≫ sX) = pullback.snd H.f g ≫ sX' := by
    rw [← Category.assoc, ← e, Category.assoc, hs]
  exact ((TotalChowClass.res_res g hs (pullback.snd H.f g) rfl _).trans
    ((TotalChowClass.res_congr e _ (by rw [Category.assoc, hs2]) _).trans
      ((TotalChowClass.res_res H.f rfl (pullback.fst H.f g) hs2 _).symm.trans
        ((congrArg (TotalChowClass.res (pullback.fst H.f g) hs2)
          (res_perfectPowerSum_eq_powerSumComplex C sX hE H p)).trans
          (res_powerSumComplex C (H.f ≫ sX) H.locallyBounded (pullback.fst H.f g) hs2 p)))))

/-- **`P_p(E)` from a global representative**: if `E` is represented on `X` itself by a locally
bounded complex `𝓔^•` of finite locally free modules, then `P_p(E) = P_p(𝓔^•)`. -/
theorem perfectPowerSum_eq_powerSumComplex (hE : HasDefinedChernClasses E)
    {P : CochainComplex X.Modules ℤ} (hP : IsLocallyBoundedFiniteLocallyFree P)
    (e : E ≅ DerivedCategory.Q.obj P) (p : ℕ) :
    perfectPowerSum C sX hE p = powerSumComplex C sX hP p := by
  let H : EnvelopePresentation E :=
    { Y := X
      f := 𝟙 X
      envelope := ⟨inferInstance, isCompletelyDecomposed_id X⟩
      P := P
      locallyBounded := hP
      representation :=
        ⟨(Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso X.toRingedSpace).app E ≪≫ e⟩ }
  refine (eq_perfectPowerSum C sX hE H p ?_).symm
  refine (res_powerSumComplex C sX hP (𝟙 X) rfl p).trans ?_
  exact powerSumComplex_congr C _ _ hP (fun n ↦ (Scheme.Modules.pullbackId X).app (P.X n)) p

/-- **`P_p(0) = 0`**: the power sums of a zero object whose Chern classes are defined vanish. -/
theorem perfectPowerSum_of_isZero (hE : HasDefinedChernClasses E) (h0 : IsZero E) (p : ℕ) :
    perfectPowerSum C sX hE p = 0 := by
  have hZ : ∀ n, IsZero ((0 : CochainComplex X.Modules ℤ).X n) := fun n =>
    Functor.map_isZero (HomologicalComplex.eval _ _ n) (isZero_zero _)
  have hP := isLocallyBoundedFiniteLocallyFree_of_isZero_X hZ
  rw [perfectPowerSum_eq_powerSumComplex C sX hE hP
    (h0.iso (Functor.map_isZero DerivedCategory.Q (isZero_zero _))),
    powerSumComplex_of_isZero_X C sX hP hZ]

/-- **`P_p(ℰ[0]) = P_p(ℰ)`**: the power sums of a finite locally free module placed in degree
zero are those of the module. -/
theorem powerSumComplex_single (M : X.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] (p : ℕ) :
    powerSumComplex C sX (isLocallyBoundedFiniteLocallyFree_single M) p =
      powerSumOfFiniteLocallyFree C sX M p := by
  rw [powerSumComplex_eq_sum_Icc C sX (isLocallyBoundedFiniteLocallyFree_single M) 0 0
    (fun n hn => HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)) p,
    Finset.Icc_self, Finset.sum_singleton, Int.negOnePow_zero, Units.val_one, one_smul]
  have eX : ((CochainComplex.singleFunctor X.Modules 0).obj M).X 0 = M :=
    HomologicalComplex.single_obj_X_self _ _ _
  exact @powerSumOfFiniteLocallyFree_congr C _ sX _ _
    ((isLocallyBoundedFiniteLocallyFree_single M).1 0) M hM
    (eqToIso eX) p

/-- **`P_p(E) = P_p(ℰ)` for `E ≅ ℰ[0]`** with `ℰ` finite locally free. -/
theorem perfectPowerSum_eq_powerSumOfFiniteLocallyFree (hE : HasDefinedChernClasses E)
    (M : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M]
    (e : E ≅ (DerivedCategory.singleFunctor X.Modules 0).obj M) (p : ℕ) :
    perfectPowerSum C sX hE p = powerSumOfFiniteLocallyFree C sX M p := by
  rw [perfectPowerSum_eq_powerSumComplex C sX hE (isLocallyBoundedFiniteLocallyFree_single M)
    (e ≪≫ (DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app M), powerSumComplex_single]

end PerfectPowerSum

/-! ### Zero and acyclic complexes -/

section Acyclic

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- An acyclic complex is a zero object of the derived category. -/
theorem isZero_Q_obj_of_acyclic {P : CochainComplex Y.Modules ℤ} (h : P.Acyclic) :
    IsZero (DerivedCategory.Q.obj P) := by
  have : P.IsLE 0 := by
    rw [CochainComplex.isLE_iff]
    exact fun i _ => h i
  have : P.IsGE 1 := by
    rw [CochainComplex.isGE_iff]
    exact fun i _ => h i
  exact DerivedCategory.TStructure.t.isZero (DerivedCategory.Q.obj P) 0 1

/-- **The power sums of a complex which is zero in `D(𝒪_Y)` vanish.** -/
theorem powerSumComplex_of_isZero {P : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (h : IsZero (DerivedCategory.Q.obj P)) (p : ℕ) :
    powerSumComplex C sY hP p = 0 := by
  have hZ : ∀ n, IsZero ((0 : CochainComplex Y.Modules ℤ).X n) := fun n =>
    Functor.map_isZero (HomologicalComplex.eval _ _ n) (isZero_zero _)
  rw [powerSumComplex_eq_of_iso C sY hP (isLocallyBoundedFiniteLocallyFree_of_isZero_X hZ)
    (h.iso (Functor.map_isZero DerivedCategory.Q (isZero_zero _))) p,
    powerSumComplex_of_isZero_X C sY _ hZ p]

/-- **The total Chern class of an acyclic locally bounded complex of finite locally free modules
is `1`** — in particular of an acyclic bounded complex. -/
theorem complexChern_of_acyclic {P : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (h : P.Acyclic) : complexChern C sY hP = 1 :=
  complexChern_of_isZero C sY hP (isZero_Q_obj_of_acyclic h)

/-- **The power sums of an acyclic locally bounded complex of finite locally free modules
vanish** — in particular those of an acyclic bounded complex. -/
theorem powerSumComplex_of_acyclic {P : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (h : P.Acyclic) (p : ℕ) :
    powerSumComplex C sY hP p = 0 :=
  powerSumComplex_of_isZero C sY hP (isZero_Q_obj_of_acyclic h) p

end Acyclic

end Stacks.Chow

end
