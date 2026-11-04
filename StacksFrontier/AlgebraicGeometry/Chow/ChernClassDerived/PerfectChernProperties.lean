module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeChern
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PowerSumComplex
public import StacksFrontier.AlgebraicGeometry.Perfect.GenericFreeCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DerivedChernClasses

/-!
# Restriction and normalization of the Chern classes of a perfect object

Let `X` be locally of finite type over the base of chapter 42 and let `E ∈ D(𝒪_X)` be an object
whose Chern classes are defined (Stacks 0F9E (1)), with total Chern class
`c(E) = Stacks.Chow.perfectChernClass` of Stacks 0GUD. This file proves the properties of `c(E)`
the localized Chern classes of Section 42.48 of the source consume:

* **restriction**: for every `g : X' ⟶ X` locally of finite type the Chern classes of `Lg^*E`
  are defined (Stacks 0GUE (5)) and `res_g c(E) = c(Lg^*E)`;
* **normalization**: `c(E) = 1` when `E ≅ 0`; the total Chern class of a locally bounded complex
  of finite locally free modules which is zero in `D(𝒪_X)` — in particular of an acyclic bounded
  complex — is `1`, by Stacks 0ESZ;
* **a module in degree zero**: if `E ≅ ℰ[0]` for a finite locally free `ℰ`, then `c(E)` is the
  total Chern class `c(ℰ)` of Stacks 0ESW, and `c_p(E) = 0` as soon as the rank of `ℰ` is
  everywhere less than `p`.

## Main definitions

* `Stacks.Chow.EnvelopePresentation.derivedPullback` — the base change of an envelope
  presentation of `E` along `g`, an envelope presentation of `Lg^*E`.

## Main results

* `Stacks.Chow.res_perfectChernClass_derivedPullback_of_comp_eq` — `res_g c(E) = c(Lg^*E)`.
* `Stacks.Chow.complexChern_of_isZero`, `Stacks.Chow.perfectChernClass_of_isZero` — `c = 1` on
  zero objects.
* `Stacks.Chow.complexChern_single` — `c(ℰ[0]) = c(ℰ)`.
* `Stacks.Chow.perfectChernClass_apply_eq_zero_of_rankLT` — `c_p(E) = 0` for `E ≅ ℰ[0]` with the
  rank of `ℰ` everywhere `< p`.

## References

* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
* [Stacks Project, Tag 0GUE](https://stacks.math.columbia.edu/tag/0GUE)
* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Restriction along a morphism -/

section Pullback

variable {X : Scheme.{u}} {E : DerivedCategory X.Modules}

/-- **The base change of an envelope presentation.** For an envelope presentation `(f, 𝓔^•)` of
`E` and `g : X' ⟶ X`, the base change `Y ×_X X' ⟶ X'` of `f` is an envelope (Stacks 0GU7) and the
termwise pullback of `𝓔^•` along `Y ×_X X' ⟶ Y` represents `Lg^*E` on it. This is the
presentation of `Stacks.Chow.hasDefinedChernClasses_of_derivedPullback`, made explicit. -/
def EnvelopePresentation.derivedPullback (H : EnvelopePresentation E) {X' : Scheme.{u}}
    (g : X' ⟶ X) :
    EnvelopePresentation
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj E) where
  Y := pullback H.f g
  f := pullback.snd H.f g
  envelope := isEnvelope_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback H.f g) H.envelope
  P := pullbackComplex (pullback.fst H.f g) H.P
  locallyBounded := Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ H.P
    H.locallyBounded
  representation := by
    have hsq : (pullback.snd H.f g).toLRSHom.toShHom ≫ g.toLRSHom.toShHom =
        (pullback.fst H.f g).toLRSHom.toShHom ≫ H.f.toLRSHom.toShHom :=
      congrArg (fun f => f.toLRSHom.toShHom) (pullback.condition (f := H.f) (g := g)).symm
    exact ⟨(Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        (pullback.snd H.f g).toLRSHom.toShHom g.toLRSHom.toShHom).app E ≪≫
      (eqToIso (Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq hsq)).app E ≪≫
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        (pullback.fst H.f g).toLRSHom.toShHom H.f.toLRSHom.toShHom).app E).symm ≪≫
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.fst H.f g).toLRSHom.toShHom).mapIso H.representation.some ≪≫
      Cohomology.derivedPullbackIsoPullbackOfKFlat (pullback.fst H.f g).toLRSHom.toShHom H.P
        (Stacks.BlowUpComplexes.kFlatComplex_of_isLocallyBoundedFiniteLocallyFree H.P
          H.locallyBounded)⟩

/-- **Stacks 0GUE (5)**, for the derived pullback itself: if the Chern classes of `E` are defined,
so are those of `Lg^*E`. -/
theorem HasDefinedChernClasses.derivedPullback (hE : HasDefinedChernClasses E) {X' : Scheme.{u}}
    (g : X' ⟶ X) :
    HasDefinedChernClasses
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj E) :=
  ⟨hE.some.derivedPullback g⟩

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **Restriction of the total Chern class of a perfect object.** For `g : X' ⟶ X` locally of
finite type, `res_g c(E) = c(Lg^*E)`: both restrict along the envelope of the base-changed
presentation to the total Chern class of the pulled-back complex. -/
theorem res_perfectChernClass_derivedPullback_of_comp_eq (hE : HasDefinedChernClasses E)
    {X' : Scheme.{u}} {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX'] (g : X' ⟶ X)
    [LocallyOfFiniteType g]
    (hs : g ≫ sX = sX')
    (hE' : HasDefinedChernClasses
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj E)) :
    TotalChowClass.res g hs (perfectChernClass C sX hE) = perfectChernClass C sX' hE' := by
  set H := hE.some
  refine eq_perfectChernClass C sX' hE' (H.derivedPullback g) ?_
  have e : pullback.snd H.f g ≫ g = pullback.fst H.f g ≫ H.f :=
    (pullback.condition (f := H.f) (g := g)).symm
  have hs2 : pullback.fst H.f g ≫ (H.f ≫ sX) = pullback.snd H.f g ≫ sX' := by
    rw [← Category.assoc, ← e, Category.assoc, hs]
  exact ((TotalChowClass.res_res g hs (pullback.snd H.f g) rfl _).trans
    ((TotalChowClass.res_congr e _ (by rw [Category.assoc, hs2]) _).trans
      ((TotalChowClass.res_res H.f rfl (pullback.fst H.f g) hs2 _).symm.trans
        ((congrArg (TotalChowClass.res (pullback.fst H.f g) hs2)
          (res_perfectChernClass C sX hE H)).trans
          (res_complexChern C (H.f ≫ sX) H.locallyBounded (pullback.fst H.f g) hs2)))))

end Pullback

/-! ### A presentation along the identity -/

section Identity

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

end Identity

/-! ### Zero objects -/

section Zero

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- A zero module is finite locally free. -/
private theorem isFiniteLocallyFree_of_isZero {Y : Scheme.{u}} {M : Y.Modules} (h : IsZero M) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
  @AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ _ _ _
    _ _ M 0 (isFiniteLocallyFreeOfRank_zero_of_isZero h)

/-- All terms of the zero complex are zero. -/
private theorem isZero_zero_X (n : ℤ) : IsZero ((0 : CochainComplex Y.Modules ℤ).X n) :=
  Functor.map_isZero (HomologicalComplex.eval _ _ n) (isZero_zero _)

/-- A complex all of whose terms are zero is a locally bounded complex of finite locally free
modules. -/
theorem isLocallyBoundedFiniteLocallyFree_of_isZero_X {P : CochainComplex Y.Modules ℤ}
    (h : ∀ n, IsZero (P.X n)) : IsLocallyBoundedFiniteLocallyFree P := by
  exact ⟨fun n => isFiniteLocallyFree_of_isZero (h n),
    fun _ => ⟨⊤, trivial, 0, 0, fun n _ => Functor.map_isZero _ (h n)⟩⟩

/-- **The total Chern class of a complex with zero terms is `1`.** -/
theorem complexChern_of_isZero_X {P : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (h : ∀ n, IsZero (P.X n)) :
    complexChern C sY hP = 1 := by
  rw [complexChern_eq_complexChernBounded C sY hP 0
    (fun n => isFiniteLocallyFreeOfRank_zero_of_isZero (h n))]
  simp [complexChernBounded, complexChernProd]

/-- **The total Chern class of a complex which is zero in `D(𝒪_Y)` is `1`**: by Stacks 0ESZ it is
the total Chern class of the zero complex. This covers acyclic complexes. -/
theorem complexChern_of_isZero {P : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (h : IsZero (DerivedCategory.Q.obj P)) :
    complexChern C sY hP = 1 := by
  rw [complexChern_eq_of_iso C sY hP (isLocallyBoundedFiniteLocallyFree_of_isZero_X isZero_zero_X)
    (h.iso (Functor.map_isZero DerivedCategory.Q (isZero_zero _))),
    complexChern_of_isZero_X C sY _ isZero_zero_X]

/-- **`c(0) = 1`**: the total Chern class of a zero object of `D(𝒪_X)` whose Chern classes are
defined is `1`. -/
theorem perfectChernClass_of_isZero {E : DerivedCategory Y.Modules}
    (hE : HasDefinedChernClasses E) (h0 : IsZero E) : perfectChernClass C sY hE = 1 := by
  have hP := isLocallyBoundedFiniteLocallyFree_of_isZero_X (Y := Y) isZero_zero_X
  rw [perfectChernClass_eq_complexChern C sY hE hP
    (h0.iso (Functor.map_isZero DerivedCategory.Q (isZero_zero _))).symm,
    complexChern_of_isZero_X C sY hP isZero_zero_X]

end Zero

/-! ### A finite locally free module placed in degree zero -/

section Single

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **A finite locally free module in degree zero is a locally bounded complex of finite locally
free modules.** -/
theorem isLocallyBoundedFiniteLocallyFree_single (M : X.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    IsLocallyBoundedFiniteLocallyFree ((CochainComplex.singleFunctor X.Modules 0).obj M) := by
  refine ⟨fun n => ?_, fun _ => ⟨⊤, trivial, 0, 0, fun n hn => Functor.map_isZero _
    (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))⟩⟩
  by_cases hn : n = 0
  · subst hn
    show AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M).X 0)
    rw [HomologicalComplex.single_obj_X_self]
    exact hM
  · exact isFiniteLocallyFree_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)

/-- **`c(ℰ[0]) = c(ℰ)`**: the total Chern class of a finite locally free module placed in degree
zero is the total Chern class of the module, Stacks 0ESW. -/
theorem complexChern_single (M : X.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    complexChern C sX (isLocallyBoundedFiniteLocallyFree_single M) =
      totalChernOfFiniteLocallyFree C sX M := by
  set hS := isLocallyBoundedFiniteLocallyFree_single M
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_complexRankLoci hS) fun ρ ↦ ?_
  set S := (CochainComplex.singleFunctor X.Modules 0).obj M
  have hρ := isFiniteLocallyFreeOfRank_complexRankLocus hS ρ.down
  let ι := (complexRankLoci hS ρ).ι
  have eX : S.X 0 = M := HomologicalComplex.single_obj_X_self _ _ _
  let e : (pullbackComplex ι S).X 0 ≅ (Scheme.Modules.pullback ι).obj M :=
    (Scheme.Modules.pullback ι).mapIso (eqToIso eX)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback ι).obj M) (ρ.down 0) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e (hρ 0)
  rw [res_complexChern_complexRankLocus, res_totalChernOfFiniteLocallyFree_of_rank C sX M ι rfl
    (ρ.down 0)]
  rcases isEmpty_or_nonempty (complexRankLoci hS ρ : Scheme.{u}) with _ | ⟨⟨y⟩⟩
  · exact (TotalChowClass.subsingleton_of_isEmpty _).elim _ _
  · have hs : ∀ n ∉ ({0} : Finset ℤ), ρ.down n = 0 := fun n hn => by
      have hzero : IsZero ((pullbackComplex ι S).X n) := Functor.map_isZero _
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simpa using hn))
      exact Scheme.Modules.isFiniteLocallyFreeOfRank_unique _ (hρ n)
        (isFiniteLocallyFreeOfRank_zero_of_isZero hzero) y
    rw [complexChernBounded_eq_prod C _ _ ρ.down hρ {0} hs, complexChernProd]
    simp only [Finset.sort_singleton, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, complexChernFactor, Int.negOnePow_zero, Units.val_one, zpow_one,
      val_totalChernUnit]
    exact totalChern_congr C _ e rfl

/-- The rank of a finite locally free module whose rank is everywhere less than `p`, in the sense
of `Stacks.Chow.IsFiniteLocallyFreeOfRankLT`, is less than `p` at every point. -/
theorem moduleRank_lt_of_isFiniteLocallyFreeOfRankLT {M : X.Modules} {p : ℕ}
    (hM : IsFiniteLocallyFreeOfRankLT (X := X.toRingedSpace) M p)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] (x : X) :
    moduleRank M x < p := by
  obtain ⟨U₀, hx, r, hr, hU⟩ := hM.2 x
  let U : X.Opens := U₀
  have h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.restrictFunctor U.ι).obj M) r :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict X U).app M) hU
  have h2 := Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank
    ((Scheme.Modules.restrictFunctor U.ι).obj M) r (⟨x, hx⟩ : (U : Scheme.{u}))
  rw [show (Scheme.Modules.restrictFunctor U.ι).obj M = M.restrict U.ι from rfl,
    Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict U.ι M ⟨x, hx⟩] at h2
  rw [← fiberRank_eq_moduleRank M x]
  exact h2 ▸ hr

/-- A perfect object isomorphic to `ℰ[0]` has total Chern class `c(ℰ[0])`. -/
private theorem perfectChernClass_eq_complexChern_single {E : DerivedCategory X.Modules}
    (hE : HasDefinedChernClasses E) (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M]
    (e : E ≅ (DerivedCategory.singleFunctor X.Modules 0).obj M) :
    perfectChernClass C sX hE = totalChernOfFiniteLocallyFree C sX M := by
  rw [perfectChernClass_eq_complexChern C sX hE (isLocallyBoundedFiniteLocallyFree_single M)
    (e ≪≫ (DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app M).symm, complexChern_single]

/-- **`c_p(E) = 0` above the rank of a module in degree zero.** If `E ≅ ℰ[0]` for a finite
locally free `ℰ` whose rank is everywhere less than `p`, then `c_p(E) = 0`. -/
theorem perfectChernClass_apply_eq_zero_of_rankLT {E : DerivedCategory X.Modules}
    (hE : HasDefinedChernClasses E) {M : X.Modules}
    (e : E ≅ (DerivedCategory.singleFunctor X.Modules 0).obj M) {p : ℕ}
    (hM : IsFiniteLocallyFreeOfRankLT (X := X.toRingedSpace) M p) :
    perfectChernClass C sX hE p = 0 := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M := hM.1
  rw [perfectChernClass_eq_complexChern_single C sX hE M e]
  exact totalChernOfFiniteLocallyFree_apply_eq_zero C sX M
    (moduleRank_lt_of_isFiniteLocallyFreeOfRankLT hM)

/-- **`c(ℰ[0]) = c(ℰ)` for a perfect object.** If `E ≅ ℰ[0]` for a finite locally free `ℰ`, then
`c(E)` is the total Chern class of `ℰ` of Stacks 0ESW. -/
theorem perfectChernClass_eq_totalChernOfFiniteLocallyFree {E : DerivedCategory X.Modules}
    (hE : HasDefinedChernClasses E) (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M]
    (e : E ≅ (DerivedCategory.singleFunctor X.Modules 0).obj M) :
    perfectChernClass C sX hE = totalChernOfFiniteLocallyFree C sX M :=
  perfectChernClass_eq_complexChern_single C sX hE M e

end Single

end Stacks.Chow

end
