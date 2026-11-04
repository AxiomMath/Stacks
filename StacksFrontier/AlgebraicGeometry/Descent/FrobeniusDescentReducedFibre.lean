module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitThickeningInvariance
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusDescentTransfer

/-!
# From freeness on a reduced fibre to freeness after a Frobenius power

Let `p` be a prime and `f : T ⟶ B` a morphism of schemes in characteristic `p` whose target `B`
has a single point `b`, for instance the spectrum of a field or of an Artinian local ring. Then
`T_red` is the reduced fibre `(T_b)_red`, so the fibre condition of Stacks Tag 0EXH at `b` says
that some Frobenius power pullback `F^{m,*}ℰ` is free on `T_red`. When `T` is Noetherian a
further Frobenius power kills the nilradical of `T`, so that `F^{N,*}ℰ` is free on `T` itself.

## Main results

* `AlgebraicGeometry.Scheme.exists_reduction_lift_of_surjective`: the reduction of the target of
  a surjective closed immersion factors through the reduction of its source.
* `AlgebraicGeometry.Scheme.Vect.IsFreeOnReducedFibresAfterFrobenius.exists_free_reduction`:
  over a one-point base the fibre condition gives freeness on `T_red`.
* `AlgebraicGeometry.Scheme.Vect.exists_free_of_free_reduction`: on a Noetherian scheme freeness
  on the reduction becomes freeness after a Frobenius power.
* `AlgebraicGeometry.Scheme.Vect.IsFreeOnReducedFibresAfterFrobenius.exists_free`: the two
  together.

## References

* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable {p : ℕ} [Fact p.Prime]

/-- **The reduction of the target of a surjective closed immersion factors through the reduction
of its source.** -/
theorem Scheme.exists_reduction_lift_of_surjective {F T : Scheme.{u}} (i : F ⟶ T)
    [IsClosedImmersion i] [Surjective i] :
    ∃ r : T.reduction ⟶ F.reduction, r ≫ F.reductionι ≫ i = T.reductionι := by
  have hker : i.ker ≤ T.reductionι.ker := by
    change i.ker ≤ T.nilradical.subschemeι.ker
    rw [Scheme.IdealSheafData.ker_subschemeι, ← Scheme.IdealSheafData.vanishingIdeal_top,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    intro x _
    change x ∈ (i.ker.support : Set T)
    rw [Scheme.Hom.support_ker]
    exact subset_closure (i.surjective x)
  obtain ⟨r, hr, -⟩ :=
    Scheme.existsUnique_lift_nilradical_subschemeι (IsClosedImmersion.lift i T.reductionι hker)
  refine ⟨(r : T.reduction ⟶ F.reduction), ?_⟩
  change r ≫ F.nilradical.subschemeι ≫ i = _
  rw [← Category.assoc, hr]
  exact IsClosedImmersion.lift_fac i T.reductionι hker

namespace Scheme.Vect

/-- **Over a one-point base the fibre condition of Stacks Tag 0EXH gives freeness on the
reduction of the source.** -/
theorem IsFreeOnReducedFibresAfterFrobenius.exists_free_reduction {T B : Scheme.{u}}
    {f : T ⟶ B} [Subsingleton B] (b : B) (hT : IsInCharacteristic T p) {E : T.Vect}
    (h : IsFreeOnReducedFibresAfterFrobenius f p hT E) :
    ∃ m r : ℕ, Nonempty ((Scheme.Modules.pullback T.reductionι).obj
      ((frobeniusPullbackIter T p hT m).obj E).obj ≅ SheafOfModules.free (ULift.{u} (Fin r))) := by
  obtain ⟨m, r, ⟨e⟩⟩ := h b
  have : IsClosedImmersion (B.fromSpecResidueField b) :=
    isClosed_singleton_iff_isClosedImmersion.mp (by
      rw [show ({b} : Set B) = Set.univ from Set.eq_univ_of_forall fun x ↦ Subsingleton.elim x b]
      exact isClosed_univ)
  have : IsClosedImmersion (f.fiberι b) := by
    rw [Scheme.Hom.fiberι]
    exact IsClosedImmersion.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (B.fromSpecResidueField b)).flip inferInstance
  have : Surjective (f.fiberι b) := ⟨fun x ↦ show x ∈ Set.range (f.fiberι b) by
    rw [Scheme.Hom.range_fiberι]
    exact Subsingleton.elim _ _⟩
  obtain ⟨ρ, hρ⟩ := Scheme.exists_reduction_lift_of_surjective (f.fiberι b)
  exact ⟨m, r, ⟨(Scheme.Modules.pullbackCongr hρ.symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp ρ _).app _).symm ≪≫
      (Scheme.Modules.pullback ρ).mapIso e ≪≫ Scheme.Modules.pullbackFreeIso ρ _⟩⟩

/-- **On a Noetherian scheme in characteristic `p`, a vector bundle free on the reduction is free
after a Frobenius power pullback.** -/
theorem exists_free_of_free_reduction {T : Scheme.{u}} [IsNoetherian T]
    (hT : IsInCharacteristic T p) (E : T.Vect) (r : ℕ)
    (e : (Scheme.Modules.pullback T.reductionι).obj E.obj ≅
      SheafOfModules.free (ULift.{u} (Fin r))) :
    ∃ N : ℕ, Nonempty (((frobeniusPullbackIter T p hT N).obj E).obj ≅
      SheafOfModules.free (ULift.{u} (Fin r))) := by
  obtain ⟨n, hn⟩ := exists_le_ker_frobPow_of_isFiniteType_of_le_nilradical p hT T.nilradical
    (fun U ↦ by
      have : IsNoetherianRing Γ(T, U) := IsLocallyNoetherian.component_noetherian U
      exact IsNoetherian.noetherian _) le_rfl
  let g : T ⟶ T.reduction := Scheme.IdealSheafData.subschemeLift _ hn
  have hg : g ≫ T.reductionι = frobPow p hT (𝟙 T) n :=
    Scheme.IdealSheafData.subschemeLift_subschemeι _ hn
  exact ⟨n, ⟨(ObjectProperty.ι _).mapIso
      (vectPullbackPullbackIsoEndoIter g T.reductionι p hT n hg E).symm ≪≫
    (Scheme.Modules.pullback g).mapIso e ≪≫ Scheme.Modules.pullbackFreeIso g _⟩⟩

/-- Frobenius power pullbacks compose: `F^{a,*} F^{b,*} ℰ ≅ F^{a + b,*} ℰ`, up to the order of
the exponents. -/
def frobeniusPullbackIterAddIso (T : Scheme.{u}) (hT : IsInCharacteristic T p) (a b : ℕ)
    (E : T.Vect) :
    (frobeniusPullbackIter T p hT a).obj ((frobeniusPullbackIter T p hT b).obj E) ≅
      (frobeniusPullbackIter T p hT (b + a)).obj E :=
  match a with
  | 0 => Iso.refl _
  | a + 1 => (frobeniusPullback T p hT).mapIso (frobeniusPullbackIterAddIso T hT a b E)

/-- **Over a one-point base with Noetherian source the fibre condition of Stacks Tag 0EXH gives
freeness after a Frobenius power.** -/
theorem IsFreeOnReducedFibresAfterFrobenius.exists_free {T B : Scheme.{u}} [IsNoetherian T]
    {f : T ⟶ B} [Subsingleton B] (b : B) (hT : IsInCharacteristic T p) {E : T.Vect}
    (h : IsFreeOnReducedFibresAfterFrobenius f p hT E) :
    ∃ N r : ℕ, Nonempty (((frobeniusPullbackIter T p hT N).obj E).obj ≅
      SheafOfModules.free (ULift.{u} (Fin r))) := by
  obtain ⟨m, r, ⟨e⟩⟩ := h.exists_free_reduction b
  obtain ⟨N, ⟨e'⟩⟩ := exists_free_of_free_reduction hT _ r e
  exact ⟨m + N, r, ⟨(ObjectProperty.ι _).mapIso
    (frobeniusPullbackIterAddIso T hT N m E).symm ≪≫ e'⟩⟩

end Scheme.Vect

end AlgebraicGeometry

end
