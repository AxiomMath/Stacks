module

public import StacksFrontier.AlgebraicGeometry.Limits.ResidueFieldSpreading
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusDescentTransfer
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusDescentReducedFibre
public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.ModuleSupport
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FibreConnectedComponents.Constructible
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ConnectedComponents
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricallyConnectedFibres
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.Basic
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.FiniteLocallyFreeUnconditional
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageLocalCase
public import Mathlib.Data.ZMod.QuotientRing

/-!
# Stacks Tag 0EXH: reduction of the essential-image half to the base of finite type over `𝐅_p`

Let `p` be a prime, `Y` a quasi-compact quasi-separated scheme in characteristic `p` and
`f : X ⟶ Y` proper, surjective, of finite presentation, with geometrically connected fibres.
The proof of [Stacks, Tag 0EXH] first reduces the description of the essential image of
`colim_F Vect(Y) ⥤ colim_F Vect(X)` to the case where `Y` is of finite type over `𝐅_p`, by
absolute Noetherian approximation of the whole configuration. This file carries out that
reduction.

Write `Y = lim Y_i` with `Y_i` of finite presentation over `𝐅_p` and affine transition morphisms
([Stacks, Tag 09MV]); descend `f` to a stage ([Stacks, Tag 01ZM]) and the finite locally free
`ℰ` to a later one ([Stacks, Tag 0B8W]); then at a still later stage `i` the descended morphism
`f_i : X_i ⟶ Y_i` is proper ([Stacks, Tag 081F]) with geometrically connected fibres
([Stacks, Tags 055I, 055E, 05F4]), and the fibre condition of the essential-image half holds for
`ℰ_i` at every point of `Y_i`.

The last point is where the source is terse. The condition holds at every point of `Y`, but a
point of `Y_i` need not come from `Y`. Over the fibre `X_y` (Noetherian), freeness on the reduced
fibre gives freeness after a Frobenius power; the isomorphism `F^{n,*}ℰ|_{X_y} ≅ 𝒪^{⊕r}` then
spreads out to a locally closed piece `V(𝔭) ∩ D(g)` of a stage through which all points of a
locally constructible neighbourhood of the image of `y` factor
(`AlgebraicGeometry.exists_isLocallyConstructible_isoAlong`), and finitely many of these
neighbourhoods cover a late enough stage (`AlgebraicGeometry.exists_stage_forall_isoAlong`).
No residue field extension enters.

## Main results

* `AlgebraicGeometry.exists_isProper_pullback_snd`: properness descends to a stage.
* `AlgebraicGeometry.exists_geometricallyConnected_pullback_snd`: so does geometric connectedness
  of the fibres.
* `AlgebraicGeometry.descendsAfterFrobenius_of_forall_finiteType`: **the reduction**. If the
  essential-image half of Stacks Tag 0EXH holds for every base of finite type over a field (in
  characteristic `p`), it holds for every quasi-compact quasi-separated base.

## References

* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- A property stable under base change passes from `X₀ ×_S Y` to `X₀ ×_S W` for any `W ⟶ Y`. -/
lemma pullback_snd_comp_of {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    {X₀ S T W : Scheme.{u}} (g₀ : X₀ ⟶ S) (w : T ⟶ S) (v : W ⟶ T) (h : P (pullback.snd g₀ w)) :
    P (pullback.snd g₀ (v ≫ w)) := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine (MorphismProperty.cancel_left_of_respectsIso P
    (pullbackLeftPullbackSndIso g₀ w v).hom _).mp ?_
  rw [pullbackLeftPullbackSndIso_hom_snd]
  exact MorphismProperty.pullback_snd _ _ h

section Stage

/-- A property stable under base change holds for `pullback.snd g₀ π` if it holds for a
morphism `f` forming a pullback square with `g₀` and `π`. -/
private lemma snd_of_isPullback {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    {X₀ S Y X : Scheme.{u}} {g₀ : X₀ ⟶ S} {π : Y ⟶ S} {a : X ⟶ X₀} {f : X ⟶ Y}
    (sq : IsPullback a f g₀ π) (h : P f) : P (pullback.snd g₀ π) := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (MorphismProperty.cancel_left_of_respectsIso P sq.isoPullback.hom _).mp
    (by rwa [sq.isoPullback_hom_snd])

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤ Scheme.{u})
  [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D) (hc : IsLimit c) {i₀ : I}
  {X X₀ : Scheme.{u}} {f : X ⟶ c.pt} {g₀ : X₀ ⟶ D.obj (op i₀)} {a : X ⟶ X₀}

/-- The transition morphism `S_j ⟶ S_{i₀}` for `i₀ ≤ j`. -/
abbrev transition {j : I} (h : i₀ ≤ j) : D.obj (op j) ⟶ D.obj (op i₀) := D.map (homOfLE h).op

include hc in
/-- **Properness descends to a stage** ([Stacks, Tag 081F]): if `f` is the base change of
`g₀ : X₀ ⟶ S_{i₀}` to the limit and `f` is proper, then the base change of `g₀` to some later
stage is proper. -/
theorem exists_isProper_pullback_snd (sq : IsPullback a f g₀ (c.π.app (op i₀))) [IsProper f]
    [LocallyOfFiniteType g₀] [CompactSpace X₀] [QuasiSeparatedSpace X₀] :
    ∃ (j : I) (h : i₀ ≤ j), IsProper (pullback.snd g₀ (transition D h)) := by
  have : Nonempty I := ⟨i₀⟩
  let X' : Over (D.obj (op i₀)) := Over.mk g₀
  let Y' : Over (D.obj (op i₀)) := Over.mk (𝟙 _)
  let f' : X' ⟶ Y' := Over.homMk g₀ (Category.comp_id _)
  have key : ∀ {T : Scheme.{u}} (g : T ⟶ D.obj (op i₀)),
      IsProper ((Over.pullback g).map f').left ↔ IsProper (pullback.snd g₀ g) := by
    intro T g
    have hw : ((Over.pullback g).map f').left ≫ pullback.snd (𝟙 _) g = pullback.snd g₀ g :=
      Over.w ((Over.pullback g).map f')
    rw [← hw, MorphismProperty.cancel_right_of_respectsIso (P := @IsProper)]
  have : IsProper ((Over.pullback (c.π.app (op i₀))).map f').left :=
    (key _).mpr (snd_of_isPullback (P := @IsProper) sq ‹_›)
  have : CompactSpace X'.left := ‹_›
  have : QuasiSeparatedSpace X'.left := ‹_›
  have : CompactSpace Y'.left := inferInstanceAs (CompactSpace (D.obj (op i₀)))
  have : QuasiSeparatedSpace Y'.left := inferInstanceAs (QuasiSeparatedSpace (D.obj (op i₀)))
  have : LocallyOfFiniteType f'.left := ‹_›
  obtain ⟨i, hi, hp⟩ := exists_isProper_baseChange_of_isLimit D c (op i₀) hc X' Y' f'
  exact ⟨i.unop, leOfHom hi.unop, (key _).mp hp⟩

include hc in
/-- **Geometric connectedness of the fibres descends to a stage** ([Stacks, Tags 055I, 055E,
05F4]): the locus where the fibres of `g₀` are geometrically connected is locally constructible,
contains the image of the limit, hence the image of a late enough stage. -/
theorem exists_geometricallyConnected_pullback_snd (sq : IsPullback a f g₀ (c.π.app (op i₀)))
    [GeometricallyConnected f] (hg₀ : FinitePresentation g₀) :
    ∃ (j : I) (h : i₀ ≤ j), GeometricallyConnected (pullback.snd g₀ (transition D h)) := by
  let L : Set (D.obj (op i₀)) := {y | GeometricallyConnected (g₀.fiberToSpecResidueField y)}
  have hL : IsLocallyConstructible L := by
    convert isLocallyConstructible_numGeometricConnectedComponents g₀ hg₀ 1 using 1
    ext y
    exact geometricallyConnected_iff_numGeometricConnectedComponents_eq_one g₀ y
  have : Nonempty I := ⟨i₀⟩
  have hlim : GeometricallyConnected (pullback.snd g₀ (c.π.app (op i₀))) :=
    snd_of_isPullback (P := @GeometricallyConnected) sq ‹_›
  have hrange : Set.range (c.π.app (op i₀)) ⊆ L := by
    rintro _ ⟨y, rfl⟩
    have h2 : y ∈ {y' | GeometricallyConnected
        ((pullback.snd g₀ (c.π.app (op i₀))).fiberToSpecResidueField y')} :=
      (GeometricallyConnected.iff_geometricallyConnected_fiber _).mp hlim y
    rwa [geometricallyConnected_fiber_locus_pullback] at h2
  let DS : DescentSituation.{u, u} I :=
    { system := D
      transition_affine := fun f => inferInstance
      quasiCompact := fun i => inferInstance
      quasiSeparated := fun i => inferInstance
      limitCone := c
      isLimit := hc
      base := i₀ }
  obtain ⟨j, hj, hjr⟩ := (eventually_range_transition_subset_of_isLocallyConstructible DS L hL
    hrange).exists
  refine ⟨j, hj, (GeometricallyConnected.iff_geometricallyConnected_fiber _).mpr fun y' => ?_⟩
  have : y' ∈ transition D hj ⁻¹' L := hjr ⟨y', rfl⟩
  rwa [← geometricallyConnected_fiber_locus_pullback] at this

end Stage

/-! ### The fibre condition at the limit and at the stages -/

section FibreCondition

variable (p : ℕ) [Fact p.Prime]

/-- The pullback of the free vector bundle of rank `r` is free of rank `r`. -/
def Scheme.Vect.pullbackFreeRankIso {X Y : Scheme.{u}} (g : X ⟶ Y) (r : ℕ) :
    (Scheme.Vect.pullback g).obj (Scheme.Vect.freeRank Y r) ≅ Scheme.Vect.freeRank X r :=
  ObjectProperty.isoMk _ (Scheme.Modules.pullbackFreeIso g (ULift.{u} (Fin r)))

open ResidueFieldSpreading in
/-- **At a point of the limit, the fibre condition of Stacks Tag 0EXH gives an isomorphism on the
whole scheme-theoretic fibre of the model.** If `f` is the base change of `g₀` along `π`, `ℰ` is
the pullback of `ℰ₀`, and `F^{n,*}ℰ` is free on the reduced fibre `X_{y,red}`, then for some
`N, r` the pullback of `F^{N,*}ℰ₀` to `X₀ ×_S Spec κ(y)` is free of rank `r`: the fibre `X_y`
is Noetherian, so freeness on its reduction gives freeness after a Frobenius power. -/
theorem exists_isoAlong_of_isFreeOnReducedFibres {X Y X₀ S : Scheme.{u}} {f : X ⟶ Y}
    [LocallyOfFiniteType f] [QuasiCompact f] {g₀ : X₀ ⟶ S} {a : X ⟶ X₀} {π : Y ⟶ S}
    (sq : IsPullback a f g₀ π) (hX : IsInCharacteristic X p) (hX₀ : IsInCharacteristic X₀ p)
    {E : X.Vect} {E₀ : X₀.Vect} (eE : E ≅ (Scheme.Vect.pullback a).obj E₀)
    (hE : Scheme.Vect.IsFreeOnReducedFibresAfterFrobenius f p hX E) (y : Y) :
    ∃ n r : ℕ, IsoAlong g₀ ((frobeniusPullbackIter X₀ p hX₀ n).obj E₀).obj
      (Scheme.Vect.freeRank X₀ r).obj (Y.fromSpecResidueField y ≫ π) := by
  have hT : IsInCharacteristic (f.fiber y) p := isInCharacteristic_of_hom (f.fiberι y) p hX
  have hcond : Scheme.Vect.IsFreeOnReducedFibresAfterFrobenius (f.fiberToSpecResidueField y) p hT
      ((Scheme.Vect.pullback (f.fiberι y)).obj E) :=
    Scheme.Vect.IsFreeOnReducedFibresAfterFrobenius.pullback (Scheme.Hom.fiber_fac f y) hX hT hE
  have : IsNoetherian (f.fiber y) :=
    isNoetherian_of_locallyOfFiniteType (f.fiberToSpecResidueField y)
  obtain ⟨N, r, ⟨e⟩⟩ := hcond.exists_free (default : Spec (Y.residueField y))
  refine ⟨N, r, ⟨?_⟩⟩
  let q := Y.fromSpecResidueField y ≫ π
  have hP : IsInCharacteristic (pullback q g₀) p :=
    isInCharacteristic_of_hom (pullback.snd q g₀) p hX₀
  let ℓ : pullback q g₀ ⟶ X := sq.lift (pullback.snd q g₀)
    (pullback.fst q g₀ ≫ Y.fromSpecResidueField y)
    (by rw [Category.assoc, ← pullback.condition])
  let ν : pullback q g₀ ⟶ f.fiber y := pullback.lift ℓ (pullback.fst q g₀) (by
    rw [IsPullback.lift_snd])
  have hν₀ : ν ≫ f.fiberι y = ℓ := pullback.lift_fst _ _ _
  have hν : ν ≫ f.fiberι y ≫ a = pullback.snd q g₀ := by
    rw [← Category.assoc, hν₀, IsPullback.lift_fst]
  let eV : (Scheme.Vect.pullback (pullback.snd q g₀)).obj
      ((frobeniusPullbackIter X₀ p hX₀ N).obj E₀) ≅
      (Scheme.Vect.pullback (pullback.snd q g₀)).obj (Scheme.Vect.freeRank X₀ r) :=
    (Scheme.Vect.pullbackCongr hν).symm.app _ ≪≫
      ((Scheme.Vect.pullbackComp ν (f.fiberι y ≫ a)).app _).symm ≪≫
      (Scheme.Vect.pullback ν).mapIso
        (frobeniusPullbackIterPullbackIso (f.fiberι y ≫ a) p hT hX₀ N E₀ ≪≫
          (frobeniusPullbackIter _ p hT N).mapIso
            (((Scheme.Vect.pullbackComp (f.fiberι y) a).app E₀).symm ≪≫
              (Scheme.Vect.pullback (f.fiberι y)).mapIso eE.symm) ≪≫
          ObjectProperty.isoMk _ e) ≪≫
      Scheme.Vect.pullbackFreeRankIso ν r ≪≫
      (Scheme.Vect.pullbackFreeRankIso (pullback.snd q g₀) r).symm
  exact (ObjectProperty.ι _).mapIso eV

open ResidueFieldSpreading in
/-- **At a stage, isomorphisms on the scheme-theoretic fibres of the model give the fibre
condition of Stacks Tag 0EXH for the base change.** If over every point `t` of `T` the pullback
of some `F^{n,*}ℰ₀` to `X₀ ×_S Spec κ(t)` is free, then the base change of `ℰ₀` to `X₀ ×_S T`
satisfies the fibre condition over `T`: the reduced fibre over `t` maps to `X₀ ×_S Spec κ(t)`. -/
theorem isFreeOnReducedFibresAfterFrobenius_of_isoAlong {X₀ S T : Scheme.{u}} (g₀ : X₀ ⟶ S)
    (q : T ⟶ S) (hX₀ : IsInCharacteristic X₀ p) (hX' : IsInCharacteristic (pullback g₀ q) p)
    (E₀ : X₀.Vect)
    (h : ∀ t : T, ∃ n r : ℕ, IsoAlong g₀ ((frobeniusPullbackIter X₀ p hX₀ n).obj E₀).obj
      (Scheme.Vect.freeRank X₀ r).obj (T.fromSpecResidueField t ≫ q)) :
    Scheme.Vect.IsFreeOnReducedFibresAfterFrobenius (pullback.snd g₀ q) p hX'
      ((Scheme.Vect.pullback (pullback.fst g₀ q)).obj E₀) := by
  intro t
  obtain ⟨n, r, ⟨e⟩⟩ := h t
  refine ⟨n, r, ⟨?_⟩⟩
  let fj := pullback.snd g₀ q
  let κ : fj.fiber t ⟶ pullback (T.fromSpecResidueField t ≫ q) g₀ :=
    pullback.lift (fj.fiberToSpecResidueField t) (fj.fiberι t ≫ pullback.fst g₀ q) (by
      rw [← Category.assoc, ← Scheme.Hom.fiber_fac, Category.assoc, Category.assoc,
        pullback.condition])
  let ρ := (fj.fiber t).reductionι ≫ fj.fiberι t
  have hκ : ρ ≫ pullback.fst g₀ q = ((fj.fiber t).reductionι ≫ κ) ≫ pullback.snd _ g₀ := by
    simp only [ρ, κ, Category.assoc, pullback.lift_snd]
  exact (Scheme.Modules.pullback ρ).mapIso ((ObjectProperty.ι _).mapIso
      (frobeniusPullbackIterPullbackIso (pullback.fst g₀ q) p hX' hX₀ n E₀).symm) ≪≫
    (Scheme.Modules.pullbackComp ρ (pullback.fst g₀ q)).app _ ≪≫
    (Scheme.Modules.pullbackCongr hκ).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ (pullback.snd _ g₀)).app _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso e ≪≫
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    Scheme.Modules.pullbackFreeIso _ _

end FibreCondition

/-! ### The reduction -/

section Reduction

variable (p : ℕ) [Fact p.Prime]

/-- The ring map `𝐅_p → R` to a commutative ring in which `p` vanishes. -/
def primeFieldHom (R : Type u) [CommRing R] (hR : (p : R) = 0) : ULift.{u} (ZMod p) →+* R :=
  ((Ideal.Quotient.lift (Ideal.span {(p : ℤ)}) (Int.castRingHom R) fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [hR]).comp (Int.quotientSpanNatEquivZMod p).symm.toRingHom).comp
    ULift.ringEquiv.toRingHom

/-- The structure morphism `Y ⟶ Spec 𝐅_p` of a scheme in characteristic `p`. -/
def toSpecPrimeField {Y : Scheme.{u}} (hY : IsInCharacteristic Y p) :
    Y ⟶ Spec (.of (ULift.{u} (ZMod p))) :=
  Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (primeFieldHom p Γ(Y, ⊤) hY))

/-- The spectrum `Spec 𝐅_p` of the prime field is a scheme in characteristic `p`. -/
lemma isInCharacteristic_spec_primeField :
    IsInCharacteristic (Spec (.of (ULift.{u} (ZMod p)))) p := by
  change (p : Γ(Spec (.of (ULift.{u} (ZMod p))), ⊤)) = 0
  rw [← map_natCast (Scheme.ΓSpecIso (.of (ULift.{u} (ZMod p)))).inv.hom p,
    show ((p : ℕ) : ULift.{u} (ZMod p)) = 0 from ULift.ext (by simp), map_zero]

open ResidueFieldSpreading in
/-- **Stacks Tag 0EXH, essential-image half: reduction to a base of finite type over a field.**

Let `p` be a prime, `Y` a quasi-compact quasi-separated scheme in characteristic `p` and
`f : X ⟶ Y` proper, surjective, of finite presentation, with geometrically connected fibres. Let
`ℰ` be a finite locally free `𝒪_X`-module such that for every `y ∈ Y` some `F^{n_y,*}ℰ` is free
on the reduced fibre `X_{y,red}`. If the essential-image half of Stacks Tag 0EXH holds over every
base of finite type over a field (the hypothesis `H`, discharged by the finite-type case of the
proof), then some `F^{n,*}ℰ` is the pullback of a finite locally free `𝒪_Y`-module.

The proof is the absolute Noetherian approximation of the source: `Y = lim Y_i` over `𝐅_p`
([Stacks, Tag 09MV]); `f` descends ([Stacks, Tag 01ZM]) and `ℰ` descends
([Stacks, Tag 0B8W]); properness ([Stacks, Tag 081F]) and geometric connectedness of the fibres
([Stacks, Tags 055I, 055E, 05F4]) hold at a later stage; and the fibre condition, upgraded on the
Noetherian fibres of `f` to freeness on the scheme-theoretic fibres, spreads out to every point
of a still later stage (`AlgebraicGeometry.exists_stage_forall_isoAlong`). -/
theorem descendsAfterFrobenius_of_forall_finiteType
    (H : ∀ (k : Type u) [Field k] {X₀ Y₀ : Scheme.{u}} (s : Y₀ ⟶ Spec (.of k))
      [LocallyOfFiniteType s] [CompactSpace Y₀] (f₀ : X₀ ⟶ Y₀) [IsProper f₀] [Surjective f₀]
      [GeometricallyConnected f₀] (hX₀ : IsInCharacteristic X₀ p),
      IsInCharacteristic Y₀ p → ∀ (E₀ : X₀.Vect),
      Scheme.Vect.IsFreeOnReducedFibresAfterFrobenius f₀ p hX₀ E₀ →
        Scheme.Vect.DescendsAfterFrobenius f₀ p hX₀ E₀)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f]
    [Surjective f] [LocallyOfFinitePresentation f] [GeometricallyConnected f]
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (E : X.Vect)
    (hE : Scheme.Vect.IsFreeOnReducedFibresAfterFrobenius f p hX E) :
    Scheme.Vect.DescendsAfterFrobenius f p hX E := by
  classical
  -- absolute Noetherian approximation of `Y` over `𝐅_p`
  obtain ⟨I, _, _, _, D, t, π, hlim, -, hfp, hqcqs, haff⟩ :=
    exists_isLimit_finitePresentation (toSpecPrimeField p hY)
  let c : Cone D := ⟨Y, π⟩
  have hc : IsLimit c := hlim
  have : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g) := fun g => haff g
  have : ∀ i, CompactSpace (D.obj i) := fun i => (hqcqs i).1
  have : ∀ i, QuasiSeparatedSpace (D.obj i) := fun i => (hqcqs i).2
  have : ∀ i : I, CompactSpace (D.obj (op i)) := fun i => inferInstance
  have : ∀ i : I, QuasiSeparatedSpace (D.obj (op i)) := fun i => inferInstance
  have hlft : ∀ i, LocallyOfFiniteType (t.app i) := fun i => by
    have := (hfp i).1
    infer_instance
  have hD : ∀ i, IsInCharacteristic (D.obj i) p := fun i =>
    isInCharacteristic_of_hom (t.app i) p (isInCharacteristic_spec_primeField p)
  have : ∀ i, TopologicalSpace.NoetherianSpace (D.obj i) := fun i => by
    have := (hfp i).2.1
    have := hlft i
    have : IsNoetherian (Spec (.of (ULift.{u} (ZMod p)))) := inferInstance
    have : IsNoetherian (D.obj i) :=
      isNoetherian_of_locallyOfFiniteType (Y := Spec (.of (ULift.{u} (ZMod p)))) (t.app i)
    infer_instance
  -- a model of `f` over a stage
  have hffp : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨i₁, X₁, hX₁, ⟨e₁⟩⟩ :=
    LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall D c hc (Over.mk f) hffp
  have := hX₁.1
  have := hX₁.2.1
  have := hX₁.2.2
  let a₁ : X ⟶ X₁.left := e₁.hom.left ≫ pullback.fst X₁.hom (c.π.app i₁)
  have he₁ : e₁.hom.left ≫ pullback.snd X₁.hom (c.π.app i₁) = f := Over.w e₁.hom
  have sq₁ : IsPullback a₁ f X₁.hom (c.π.app i₁) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ ((Over.forget _).mapIso e₁) rfl he₁
    rw [Category.assoc, pullback.condition, ← Category.assoc, he₁]
  -- the inverse system of the base changes of the model, and the descent of `ℰ`
  let F : Over i₁ ⥤ Scheme.{u} := Over.post D ⋙ Over.pullback X₁.hom ⋙ Over.forget X₁.left
  let cX : Cone F :=
    (Over.pullback X₁.hom ⋙ Over.forget X₁.left).mapCone ((Over.conePost D i₁).obj c)
  have hcX : IsLimit cX := isLimitOfPreserves _ (Over.isLimitConePost i₁ hc)
  have : ∀ {k k' : Over i₁} (m : k ⟶ k'), IsAffineHom (F.map m) := fun m =>
    MorphismProperty.overPullbackMap (P := @IsAffineHom) X₁.hom ((Over.post D).map m)
      (haff m.left)
  have : ∀ k, CompactSpace (F.obj k) := fun k => by
    change CompactSpace ↥(pullback (D.map k.hom) X₁.hom)
    infer_instance
  have : ∀ k, QuasiSeparatedSpace (F.obj k) := fun k => by
    change QuasiSeparatedSpace ↥(pullback (D.map k.hom) X₁.hom)
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst (D.map k.hom) X₁.hom)
  let ψ : X ≅ cX.pt := sq₁.flip.isoPullback
  obtain ⟨kE, E₂, hE₂, ⟨eE₂⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isFiniteLocallyFree_pullback_iso F cX hcX
      ((Scheme.Modules.pullback ψ.inv).obj E.obj)
      (SheafOfModules.IsFiniteLocallyFree.pullback_scheme ψ.inv E.obj E.property)
  -- re-base at the stage of `kE`
  let j₀ : I := kE.left.unop
  let X₀ : Scheme.{u} := pullback (D.map kE.hom) X₁.hom
  let g₀ : X₀ ⟶ D.obj (op j₀) := pullback.fst (D.map kE.hom) X₁.hom
  let E₀ : X₀.Vect := ⟨E₂, hE₂⟩
  let a : X ⟶ X₀ := ψ.hom ≫ cX.π.app kE
  have hcXsnd : cX.π.app kE ≫ pullback.snd (D.map kE.hom) X₁.hom =
      pullback.snd (c.π.app i₁) X₁.hom :=
    Over.w ((Over.pullback X₁.hom).map (((Over.conePost D i₁).obj c).π.app kE))
  have hcXfst : cX.π.app kE ≫ pullback.fst (D.map kE.hom) X₁.hom =
      pullback.fst (c.π.app i₁) X₁.hom ≫ c.π.app kE.left := by
    simp only [cX, Functor.mapCone_π_app, Functor.comp_map, Over.forget_map,
      Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have ha₁ : a ≫ pullback.snd (D.map kE.hom) X₁.hom = a₁ := by
    change ψ.hom ≫ cX.π.app kE ≫ pullback.snd (D.map kE.hom) X₁.hom = a₁
    rw [hcXsnd]
    exact sq₁.flip.isoPullback_hom_snd
  have hag : a ≫ g₀ = f ≫ c.π.app (op j₀) := by
    change ψ.hom ≫ cX.π.app kE ≫ pullback.fst (D.map kE.hom) X₁.hom = _
    rw [hcXfst]
    exact sq₁.flip.isoPullback_hom_fst_assoc _
  have sq : IsPullback a f g₀ (c.π.app (op j₀)) := by
    refine IsPullback.of_right (h₁₂ := pullback.snd (D.map kE.hom) X₁.hom)
      (h₂₂ := D.map kE.hom) (v₁₃ := X₁.hom) ?_ hag
      (IsPullback.of_hasPullback (D.map kE.hom) X₁.hom).flip
    rw [ha₁, show c.π.app (op j₀) ≫ D.map kE.hom = c.π.app i₁ from c.w kE.hom]
    exact sq₁
  have eE : E ≅ (Scheme.Vect.pullback a).obj E₀ := ObjectProperty.isoMk _
    ((Scheme.Modules.pullbackId X).symm.app E.obj ≪≫
      (Scheme.Modules.pullbackCongr ψ.hom_inv_id.symm).app E.obj ≪≫
      ((Scheme.Modules.pullbackComp ψ.hom ψ.inv).app E.obj).symm ≪≫
      (Scheme.Modules.pullback ψ.hom).mapIso eE₂ ≪≫
      (Scheme.Modules.pullbackComp ψ.hom (cX.π.app kE)).app E₂)
  -- properness and geometric connectedness at a stage
  have : CompactSpace X₀ := inferInstance
  have : QuasiSeparatedSpace X₀ :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst (D.map kE.hom) X₁.hom)
  obtain ⟨j₁, h₁, hpr⟩ := exists_isProper_pullback_snd D c hc sq
  obtain ⟨j₂, h₂, hgc⟩ := exists_geometricallyConnected_pullback_snd D c hc sq
    ⟨inferInstance, inferInstance, inferInstance⟩
  -- the fibre condition at every point of a stage
  have hX₀ : IsInCharacteristic X₀ p := isInCharacteristic_of_hom g₀ p (hD _)
  obtain ⟨j₃, h₃, hj₃⟩ := exists_stage_forall_isoAlong D c hc j₀ g₀ (ι := ℕ × ℕ)
    (fun nr => ((frobeniusPullbackIter X₀ p hX₀ nr.1).obj E₀).obj)
    (fun nr => (Scheme.Vect.freeRank X₀ nr.2).obj)
    (fun nr => ((frobeniusPullbackIter X₀ p hX₀ nr.1).obj E₀).property)
    (fun nr => (Scheme.Vect.freeRank X₀ nr.2).property)
    (fun y => by
      obtain ⟨n, r, h⟩ := exists_isoAlong_of_isFreeOnReducedFibres p sq hX hX₀ eE hE y
      exact ⟨(n, r), h⟩)
  -- a common later stage
  obtain ⟨j₄, hj₁₄, hj₂₄⟩ := exists_ge_ge j₁ j₂
  obtain ⟨j, hj₄, hj₃j⟩ := exists_ge_ge j₄ j₃
  have hj : j₀ ≤ j := h₁.trans (hj₁₄.trans hj₄)
  have htr : ∀ {j' : I} (h' : j₀ ≤ j') (h'' : j' ≤ j),
      transition D hj = D.map (homOfLE h'').op ≫ transition D h' := fun h' h'' => by
    rw [← D.map_comp]
    rfl
  have : IsProper (pullback.snd g₀ (transition D hj)) := by
    rw [htr h₁ (hj₁₄.trans hj₄)]
    exact pullback_snd_comp_of (P := @IsProper) g₀ _ _ hpr
  have : GeometricallyConnected (pullback.snd g₀ (transition D hj)) := by
    rw [htr h₂ (hj₂₄.trans hj₄)]
    exact pullback_snd_comp_of (P := @GeometricallyConnected) g₀ _ _ hgc
  have hfib : ∀ t' : D.obj (op j), ∃ n r : ℕ,
      IsoAlong g₀ ((frobeniusPullbackIter X₀ p hX₀ n).obj E₀).obj
        (Scheme.Vect.freeRank X₀ r).obj ((D.obj (op j)).fromSpecResidueField t' ≫
          transition D hj) := fun t' => by
    obtain ⟨⟨n, r⟩, hnr⟩ := hj₃ (D.map (homOfLE hj₃j).op t')
    refine ⟨n, r, ?_⟩
    exact (IsoAlong.of_residueField (D.map (homOfLE hj₃j).op) (transition D h₃) t' hnr).of_eq
      (by rw [htr h₃ hj₃j])
  -- the finite type case
  have hXj : IsInCharacteristic (pullback g₀ (transition D hj)) p :=
    isInCharacteristic_of_hom (pullback.fst _ _) p hX₀
  have := hlft (op j)
  have hdesc := H (ULift.{u} (ZMod p)) (t.app (op j)) (pullback.snd g₀ (transition D hj)) hXj
    (hD _) _ (isFreeOnReducedFibresAfterFrobenius_of_isoAlong p g₀ _ hX₀ hXj E₀ hfib)
  -- back to `f`
  let aj : X ⟶ pullback g₀ (transition D hj) := pullback.lift a (f ≫ c.π.app (op j)) (by
    rw [hag, Category.assoc]
    congr 1
    exact (c.w (homOfLE hj).op).symm)
  have w : aj ≫ pullback.snd g₀ (transition D hj) = f ≫ c.π.app (op j) := pullback.lift_snd _ _ _
  refine (hdesc.pullback w hXj hX).of_iso hX ?_
  exact (Scheme.Vect.pullbackComp aj (pullback.fst _ _)).app E₀ ≪≫
    (Scheme.Vect.pullbackCongr (pullback.lift_fst _ _ _)).app E₀ ≪≫ eE.symm

end Reduction

end AlgebraicGeometry

end
