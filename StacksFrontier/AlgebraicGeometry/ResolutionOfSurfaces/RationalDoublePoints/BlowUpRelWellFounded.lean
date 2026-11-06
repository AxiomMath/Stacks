module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.StageInduction
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.PointBlowupStalkCompat
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ChartTripleRootTermination
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.GoodCoordinateExistence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.CompletionSituation
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.CompletionComparison
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowupStepSequence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpPointRational
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.EmbeddingDimensionThree

/-!
# Termination: the relation `≺` between rational double points is well founded

`T ≺ S` (`AlgebraicGeometry.RationalDoublePointSituation.BlowUpRel`) when the completion of `T`
is that of the local ring at a singular point of the blowup of a ring with the completion of `S`.
The relation `≺` is well founded, given the propagation of good coordinates (case I): this is the
termination half of [Stacks, Tag 0BGE].

## Main definitions

* `AlgebraicGeometry.RationalDoublePointSituation.NotAccWith`: the local ring at a point is that
  of a non-accessible situation, in which a given element satisfies a coordinate predicate.
* `AlgebraicGeometry.RationalDoublePointSituation.CoordinatePropagates`: a coordinate predicate
  propagates to every non-accessible singular point of a blowup.

## Main results

* `AlgebraicGeometry.RationalDoublePointSituation.acc_of_coordinate`: a coordinate predicate
  propagated to every non-accessible singular point forces accessibility.
* `AlgebraicGeometry.RationalDoublePointSituation.wellFounded_blowUpRel_of_isGoodCoordinate`:
  well-foundedness from the case I propagation and the dimensions of the graded pieces.
* `AlgebraicGeometry.RationalDoublePointSituation.wellFounded_blowUpRel_of_propagation`:
  well-foundedness from the case I propagation alone.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry

section Transfer

variable {B : Type u} [CommRing B] [IsLocalRing B] {B' : Type u} [CommRing B'] [IsLocalRing B']

/-- A unit-special coordinate is carried along a local homomorphism extending the maximal ideal
to the maximal ideal. -/
theorem IsUnitSpecialCoordinate.map (φ : B →+* B') [IsLocalHom φ]
    (hmax : Ideal.map φ (maximalIdeal B) = maximalIdeal B') {e : B}
    (h : IsUnitSpecialCoordinate B e) : IsUnitSpecialCoordinate B' (φ e) := by
  obtain ⟨x, q, hx0, hspan, hq, hrel⟩ := h
  refine ⟨fun i => φ (x i), fun i j => φ (q i j), by simp [hx0],
    span_range_map_eq_maximalIdeal φ hmax hspan, fun hm => hq ?_, ?_⟩
  · by_contra hn
    exact (mem_maximalIdeal _).mp hm ((notMem_maximalIdeal.mp hn).map φ)
  · simpa [map_sum, map_mul, map_add] using map_mem_maximalIdeal_pow_of_map_eq φ hmax hrel

/-- A first generator of a good relation is carried along a ring isomorphism. -/
theorem IsFirstGeneratorOfGoodRelation.of_ringEquiv (f : B ≃+* B') {e : B}
    (h : IsFirstGeneratorOfGoodRelation B e) :
    IsFirstGeneratorOfGoodRelation B' (f e) :=
  h.map (f : B →+* B') (map_ringEquiv_maximalIdeal f) (ResidueField.mapEquiv f).bijective

end Transfer

namespace RationalDoublePointSituation

/-- `T ≺ S` only depends on the completion of `S`. -/
theorem blowUpRel_congr_right {T S S₂ : RationalDoublePointSituation.{u}}
    (E : localCompletion S.A ≃+* localCompletion S₂.A) (h : BlowUpRel T S) : BlowUpRel T S₂ := by
  obtain ⟨S', ⟨e⟩, x, hx, hT⟩ := h
  exact ⟨S', ⟨e.trans E⟩, x, hx, hT⟩

/-- Accessibility for `≺` only depends on the completion. -/
theorem acc_congr {S S₂ : RationalDoublePointSituation.{u}}
    (E : localCompletion S.A ≃+* localCompletion S₂.A) (h : Acc BlowUpRel S) : Acc BlowUpRel S₂ :=
  ⟨S₂, fun _ hT => h.inv (blowUpRel_congr_right E.symm hT)⟩

/-- A non-accessible situation has a singular point on its blowup at which every situation with
that local ring is non-accessible. -/
theorem exists_mem_singularLocus_not_acc (S : RationalDoublePointSituation.{u})
    (hS : ¬ Acc BlowUpRel S) :
    ∃ x ∈ singularLocus (blowUp (maximalIdealSheaf S.A)),
      ∀ T : RationalDoublePointSituation.{u},
        Nonempty (T.A ≃+* (blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) →
          ¬ Acc BlowUpRel T := by
  obtain ⟨T, hTS, hT⟩ : ∃ T, BlowUpRel T S ∧ ¬ Acc BlowUpRel T := by
    by_contra h
    push Not at h
    exact hS ⟨S, h⟩
  obtain ⟨S', ⟨E⟩, x', hx', ⟨F⟩⟩ := hTS
  obtain ⟨x, hx, ⟨G⟩⟩ := exists_mem_singularLocus_of_completion_ringEquiv S S' E.symm x' hx'
  refine ⟨x, hx, fun T₀ ⟨f⟩ hT₀ => hT (acc_congr ?_ hT₀)⟩
  exact (StacksDraft.exists_adicCompletion_ringEquiv_of_ringEquiv f).choose.trans
    (G.trans F.symm)

/-- A non-accessible situation has a closed singular point on its blowup over the closed point,
whose local ring is that of a non-accessible situation. -/
private theorem exists_closed_singular_point_not_acc (hL : RationalDoublePointBlowUpProperties.{u})
    (T : RationalDoublePointSituation.{u}) (hT : ¬ Acc BlowUpRel T) :
    ∃ x ∈ singularLocus (blowUp (maximalIdealSheaf T.A)),
      IsClosed ({x} : Set (blowUp (maximalIdealSheaf T.A))) ∧
        blowUpToBase (maximalIdealSheaf T.A) x = IsLocalRing.closedPoint T.A ∧
        ∃ T' : RationalDoublePointSituation.{u},
          ∃ _ : T'.A ≃+* (blowUp (maximalIdealSheaf T.A)).presheaf.stalk x, ¬ Acc BlowUpRel T' := by
  obtain ⟨x, hx, hxT⟩ := exists_mem_singularLocus_not_acc T hT
  obtain ⟨hxc, hxo, T', ⟨e'⟩⟩ := (hL T).2.2 x hx
  exact ⟨x, hx, hxc, hxo, T', e', hxT T' ⟨e'⟩⟩

/-- `NotAccWith R Y q s`: the local ring of `Y` at `q` is isomorphic to the ring of a
non-accessible situation, in which the element corresponding to `s` satisfies the coordinate
predicate `R`. -/
def NotAccWith (R : ∀ (B : Type u) [CommRing B] [IsLocalRing B], B → Prop) (Y : Scheme.{u})
    (q : Y) (s : Y.presheaf.stalk q) : Prop :=
  ∃ (T : RationalDoublePointSituation.{u}) (e : T.A ≃+* Y.presheaf.stalk q),
    ¬ Acc BlowUpRel T ∧ R T.A (e.symm s)

/-- A coordinate predicate `R` propagates if, for every element `g` satisfying `R` in the ring of
a situation and every singular point of its blowup whose local ring is that of a non-accessible
situation, the maximal ideal extends to the ideal generated by the image of `g`, the residue
field is unchanged, and the image of `g` satisfies `R`. -/
def CoordinatePropagates (R : ∀ (B : Type u) [CommRing B] [IsLocalRing B], B → Prop) : Prop :=
  ∀ (T : RationalDoublePointSituation.{u}) (g : T.A), R T.A g →
    ∀ x ∈ singularLocus (blowUp (maximalIdealSheaf T.A)),
    (∃ T' : RationalDoublePointSituation.{u},
      Nonempty (T'.A ≃+* (blowUp (maximalIdealSheaf T.A)).presheaf.stalk x) ∧
        ¬ Acc BlowUpRel T') →
    Ideal.map (blowUpStalkHom T.A x) (IsLocalRing.maximalIdeal T.A) =
        Ideal.span {blowUpStalkHom T.A x g} ∧
      Function.Surjective ((residue ((blowUp (maximalIdealSheaf T.A)).presheaf.stalk x)).comp
        (blowUpStalkHom T.A x)) ∧
      R ((blowUp (maximalIdealSheaf T.A)).presheaf.stalk x) (blowUpStalkHom T.A x g)

/-- If the coordinate predicate `R` is carried by ring isomorphisms and propagates
(`CoordinatePropagates`), then for a closed point `y` satisfying `NotAccWith R` there is a closed
point `q` over `y` of the blowup in `y` with unchanged residue field, at which the maximal ideal
at `y` extends to the ideal generated by the image of `s₀`, and which satisfies `NotAccWith R`
with that image. -/
theorem exists_next_notAccWith_of_isClosed (hL : RationalDoublePointBlowUpProperties.{u})
    (R : ∀ (B : Type u) [CommRing B] [IsLocalRing B], B → Prop)
    (hRequiv : ∀ (B B' : Type u) [CommRing B] [IsLocalRing B] [CommRing B'] [IsLocalRing B']
      (ρ : B ≃+* B') (b : B), R B b → R B' (ρ b))
    (hstep : CoordinatePropagates R) {Y : Scheme.{u}} (y : Y) (hy : IsClosed ({y} : Set Y))
    (s₀ : Y.presheaf.stalk y) (hs₀ : NotAccWith R Y y s₀) :
    ∃ q : blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)),
      ∃ hq : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) q = y,
      IsClosed ({q} : Set (blowUp
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)))) ∧
      IsIso ((blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))).residueFieldMap q) ∧
      Ideal.map ((blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))).stalkMap q).hom
          (hq.symm ▸ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) =
        Ideal.span
          {((blowUpToBase
              (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))).stalkMap q).hom
              (hq.symm ▸ s₀)} ∧
      NotAccWith R (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))) q
        (((blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))).stalkMap q).hom
            (hq.symm ▸ s₀)) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y) with hI
  obtain ⟨T, e, hT, hR⟩ := hs₀
  obtain ⟨x, hx, hxc, hxo, T', e', hT'⟩ := exists_closed_singular_point_not_acc hL T hT
  obtain ⟨hmap, hres, hRx⟩ := hstep T (e.symm s₀) hR x hx ⟨T', ⟨e'⟩, hT'⟩
  obtain ⟨ψ, -, hψiso, hψover, -, hψclosed, hψw⟩ :=
    exists_hom_blowUp_maximalIdealSheaf_localization T.A y hy e
  have hq : blowUpToBase I (ψ x) = y := (hψover x).mpr hxo
  have : IsLocalHom ((CommRingCat.ofHom (e.symm : ↑(Y.presheaf.stalk y) →+* T.A)).hom) :=
    IsLocalHom.of_surjective _ e.symm.surjective
  have := hψiso x
  let α := (asIso (ψ.stalkMap x)).commRingCatIsoToRingEquiv
  have hcompat := @stalkMap_stalkMap_cast_of_comm Y (blowUp (maximalIdealSheaf T.A)) (blowUp I)
    T.A _ _ y (CommRingCat.ofHom (e.symm : ↑(Y.presheaf.stalk y) →+* T.A)) _ ψ
    (blowUpToBase _) (blowUpToBase I) hψw x hq
  obtain ⟨hiso, hspan⟩ := isIso_residueFieldMap_and_map_maximalIdeal_of_compat
    (blowUpToBase I) (ψ x) y hq e α (blowUpStalkHom T.A x) hcompat (e.symm s₀) hmap hres
  rw [RingEquiv.apply_symm_apply] at hspan
  refine ⟨ψ x, hq, (hψclosed x hxo).mpr hxc, hiso, hspan, T', e'.trans α.symm, hT', ?_⟩
  have h1 : (e'.trans α.symm).symm
      (((blowUpToBase I).stalkMap (ψ x)).hom (hq.symm ▸ s₀)) =
      e'.symm (blowUpStalkHom T.A x (e.symm s₀)) := by
    rw [RingEquiv.symm_trans_apply, RingEquiv.symm_symm]
    exact congrArg e'.symm (hcompat s₀)
  rw [h1]
  exact hRequiv _ _ e'.symm _ hRx

/-- **A propagating coordinate predicate forces accessibility.** Let `R` be a coordinate predicate
carried along local homomorphisms which extend the maximal ideal to the maximal ideal and induce
isomorphisms of residue fields (in particular to the completion), satisfied only by elements of
the maximal ideal, and propagating to non-accessible singular points of blowups. Then a situation
with an `R`-coordinate is accessible for `≺`. -/
theorem acc_of_coordinate (hL : RationalDoublePointBlowUpProperties.{u})
    (R : ∀ (B : Type u) [CommRing B] [IsLocalRing B], B → Prop)
    (hRmap : ∀ (B B' : Type u) [CommRing B] [IsLocalRing B] [CommRing B'] [IsLocalRing B']
      (φ : B →+* B') [IsLocalHom φ], Ideal.map φ (IsLocalRing.maximalIdeal B) =
        IsLocalRing.maximalIdeal B' → Function.Bijective (ResidueField.map φ) →
        ∀ b, R B b → R B' (φ b))
    (hRmem : ∀ (B : Type u) [CommRing B] [IsLocalRing B] (b : B), R B b →
      b ∈ IsLocalRing.maximalIdeal B)
    (hstep : CoordinatePropagates R) (T : RationalDoublePointSituation.{u}) (g : T.A)
    (hg : R T.A g) : Acc BlowUpRel T := by
  by_contra hT
  have hRequiv : ∀ (B B' : Type u) [CommRing B] [IsLocalRing B] [CommRing B'] [IsLocalRing B']
      (ρ : B ≃+* B') (b : B), R B b → R B' (ρ b) := fun B B' _ _ _ _ ρ b h =>
    hRmap B B' (ρ : B →+* B') (map_ringEquiv_maximalIdeal ρ) (ResidueField.mapEquiv ρ).bijective
      b h
  let Tc := T.completion
  have : IsAdicComplete (IsLocalRing.maximalIdeal Tc.A) Tc.A :=
    inferInstanceAs (IsAdicComplete (IsLocalRing.maximalIdeal
      (AdicCompletion (IsLocalRing.maximalIdeal T.A) T.A))
      (AdicCompletion (IsLocalRing.maximalIdeal T.A) T.A))
  have hTc : ¬ Acc BlowUpRel Tc := fun h => hT (acc_congr
    (AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal Tc.A)).toRingEquiv.symm h)
  let gc : Tc.A := algebraMap T.A (AdicCompletion (IsLocalRing.maximalIdeal T.A) T.A) g
  have hgc : R Tc.A gc := hRmap T.A (AdicCompletion (IsLocalRing.maximalIdeal T.A) T.A)
    (algebraMap T.A (AdicCompletion (IsLocalRing.maximalIdeal T.A) T.A))
    AdicCompletion.maximalIdeal_eq_map.symm (AdicCompletion.residueField_map_bijective T.A) g hg
  let t : PointBlowupStep.{u} (NotAccWith R) := PointBlowupStep.ofForallExists fun d =>
    exists_next_notAccWith_of_isClosed hL R hRequiv hstep d.point d.point_closed d.elem d.prop
  let ι := (stalkClosedPointIso (.of Tc.A)).commRingCatIsoToRingEquiv
  let d₀ : PointBlowupStage.{u} (NotAccWith R) :=
    { scheme := Spec (.of Tc.A)
      point := IsLocalRing.closedPoint Tc.A
      point_closed := IsLocalRing.isClosed_singleton_closedPoint Tc.A
      elem := ι.symm gc
      prop := ⟨Tc, ι.symm, hTc, by simpa using hgc⟩ }
  have hx : d₀.elem ∈ IsLocalRing.maximalIdeal (d₀.scheme.presheaf.stalk d₀.point) := fun hu =>
    hRmem _ gc hgc (ι.apply_symm_apply gc ▸ (hu.map (ι : _ →+* Tc.A) : IsUnit (ι (ι.symm gc))))
  obtain ⟨Y, q, y, ⟨S, e, -, -⟩, hreg⟩ :=
    exists_isRegularLocalRing_of_pointBlowupStep Tc.A Tc.dimension_two t d₀ (Iso.refl _) rfl hx
  exact S.not_isRegularLocalRing (IsRegularLocalRing.of_ringEquiv e.symm)

/-- A first generator of a good relation lies in the maximal ideal. -/
theorem mem_maximalIdeal_of_isGoodCoordinate {B : Type u} [CommRing B] [IsLocalRing B] {b : B}
    (h : IsFirstGeneratorOfGoodRelation B b) : b ∈ IsLocalRing.maximalIdeal B := by
  obtain ⟨x, a, rfl, hspan, -⟩ := h
  exact hspan ▸ Ideal.subset_span ⟨0, rfl⟩

/-- A unit-special coordinate lies in the maximal ideal. -/
theorem mem_maximalIdeal_of_isUnitSpecialCoordinate {B : Type u} [CommRing B] [IsLocalRing B]
    {b : B} (h : IsUnitSpecialCoordinate B b) : b ∈ IsLocalRing.maximalIdeal B := by
  obtain ⟨x, q, rfl, hspan, -⟩ := h
  exact hspan ▸ Ideal.subset_span ⟨0, rfl⟩

/-- **The relation `≺` is well founded** (the termination half of [Stacks, Tag 0BGE]), from the
local information on blowups of rational double points, the propagation of good coordinates
(case I), and the dimension formula `dim 𝔪ⁿ/𝔪ⁿ⁺¹ = 2n + 1`. -/
theorem wellFounded_blowUpRel_of_isGoodCoordinate (hL : RationalDoublePointBlowUpProperties.{u})
    (hA2 : ∀ (S : RationalDoublePointSituation.{u}) {e : S.A},
      IsFirstGeneratorOfGoodRelation S.A e →
      ∀ (x : blowUp (maximalIdealSheaf S.A)),
      ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) →
      Ideal.map (blowUpStalkHom S.A x) (IsLocalRing.maximalIdeal S.A) =
          Ideal.span {blowUpStalkHom S.A x e} ∧
        Function.Surjective ((residue ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)).comp
          (blowUpStalkHom S.A x)) ∧
        IsFirstGeneratorOfGoodRelation ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)
          (blowUpStalkHom S.A x e))
    (hdim : ∀ (S : RationalDoublePointSituation.{u}) (n : ℕ),
      Module.finrank (ResidueField S.A) (IsLocalRing.gradedPiece S.A n) = 2 * n + 1) :
    WellFounded BlowUpRel.{u} := by
  refine ⟨fun S => ?_⟩
  by_contra hS
  by_cases hI : ∃ T : RationalDoublePointSituation.{u}, ¬ Acc BlowUpRel T ∧ IsCaseOne T.A
  · obtain ⟨T, hT, hc⟩ := hI
    obtain ⟨x, hx, -⟩ := exists_mem_singularLocus_not_acc T hT
    obtain ⟨g, hg⟩ := T.exists_isGoodCoordinate hc x hx
    exact hT (acc_of_coordinate hL IsFirstGeneratorOfGoodRelation
      (fun _ _ _ _ _ _ φ _ hmax hres _ h => h.map φ hmax hres)
      (fun _ _ _ _ h => mem_maximalIdeal_of_isGoodCoordinate h)
      (fun T _ hg x hx _ => hA2 T hg x hx) T g hg)
  push Not at hI
  have hII : CoordinatePropagates IsUnitSpecialCoordinate := by
    rintro T g hg x hx ⟨T', ⟨e'⟩, hT'⟩
    exact (T.isCaseOne_or_isUnitSpecialCoordinate_stalk_blowUp hg x hx).resolve_left
      fun hc => hI T' hT' (hc.of_ringEquiv e'.symm)
  have key : ∀ (T : RationalDoublePointSituation.{u}), ¬ Acc BlowUpRel T →
      ∀ (B : Type u) [CommRing B] [IsLocalRing B] (e : T.A ≃+* B),
      (IsCaseOne B ∨ ∃ c, IsUnitSpecialCoordinate B c) → False := by
    rintro T hT B _ _ e (hc | ⟨c, hc⟩)
    · exact hI T hT (hc.of_ringEquiv e.symm)
    · exact hT (acc_of_coordinate hL IsUnitSpecialCoordinate
        (fun _ _ _ _ _ _ φ _ hmax _ _ h => h.map φ hmax)
        (fun _ _ _ _ h => mem_maximalIdeal_of_isUnitSpecialCoordinate h) hII T (e.symm c)
        (hc.of_ringEquiv e.symm))
  obtain ⟨x₁, hx₁, -, -, T₁, e₁, hT₁⟩ := exists_closed_singular_point_not_acc hL S hS
  obtain ⟨x₂, hx₂, -, -, T₂, e₂, hT₂⟩ := exists_closed_singular_point_not_acc hL T₁ hT₁
  obtain ⟨x₃, hx₃, -, -, T₃, e₃, hT₃⟩ := exists_closed_singular_point_not_acc hL T₂ hT₂
  rcases S.exists_isCaseOne_or_isUnitSpecialCoordinate_of_three_blowUps (hdim S) (hI S hS)
      x₁ hx₁ T₁ e₁ x₂ hx₂ T₂ e₂ x₃ hx₃ with h | h | h
  · exact key T₁ hT₁ _ e₁ h
  · exact key T₂ hT₂ _ e₂ h
  · exact key T₃ hT₃ _ e₃ h


end RationalDoublePointSituation

/-- **The local information on the blowup of a rational double point**: the blowup of `Spec(A)`
in its maximal ideal is normal with finitely many singular points, each closed, over the closed
point, and a rational double point again. -/
theorem rationalDoublePointBlowUpProperties : RationalDoublePointBlowUpProperties.{u} :=
  rationalDoublePointBlowUpProperties_of_exists_span fun S => S.exists_span_range_eq_maximalIdeal

namespace RationalDoublePointSituation

/-- **The relation `≺` is well founded, given the propagation of good coordinates (case I).** -/
theorem wellFounded_blowUpRel_of_propagation
    (hA2 : ∀ (S : RationalDoublePointSituation.{u}) {e : S.A},
      IsFirstGeneratorOfGoodRelation S.A e →
      ∀ (x : blowUp (maximalIdealSheaf S.A)),
      ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) →
      Ideal.map (blowUpStalkHom S.A x) (IsLocalRing.maximalIdeal S.A) =
          Ideal.span {blowUpStalkHom S.A x e} ∧
        Function.Surjective ((residue ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)).comp
          (blowUpStalkHom S.A x)) ∧
        IsFirstGeneratorOfGoodRelation ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)
          (blowUpStalkHom S.A x e)) :
    WellFounded BlowUpRel.{u} :=
  wellFounded_blowUpRel_of_isGoodCoordinate rationalDoublePointBlowUpProperties hA2
    fun S n => S.finrank_gradedPiece_eq_two_mul_add_one n

end RationalDoublePointSituation

end AlgebraicGeometry

end
