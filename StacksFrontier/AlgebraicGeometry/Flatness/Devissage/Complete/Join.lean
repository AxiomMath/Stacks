module

public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.BaseChangeAt
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.ShrinkingSource
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.StageRestriction
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.EtaleNeighborhoodComplete
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# Joining a one-step dévissage to a complete dévissage of its cokernel

This module carries out the last paragraph of the proof of Stacks 05HR: the situation its
induction produces — a one-step dévissage of `F/X/S` at `x` with a generically invertible map
`α` out of a free module on its smooth scheme `Y`, an open immersion of `Y` into a scheme `X₁`
over `S` carrying a module whose restriction to `Y` is the cokernel of `α`, and a complete
dévissage of that module at the image of the distinguished point `y` — already yields the
conclusion of Stacks 05HR.

## Main results

* `AlgebraicGeometry.exists_etaleNeighborhood_completeDevissageAt_of_cokernelDevissage`: the
  conclusion of Stacks 05HR in that situation.

## Implementation notes

The complete dévissage of the module on `X₁` is first shrunk, by Stacks 05HM (3) in the form
`AlgebraicGeometry.NonemptyCompleteDevissageAt.exists_standardShrinking_source`, so that its
source open `X'₁` lies inside the open `Y ⊆ X₁`. Then the one-step dévissage is shrunk, by
Stacks 05HA (2) in the form `AlgebraicGeometry.exists_shrinkingOpens_smooth`, so that its smooth
open is the open of `Y` cut out by `X'₁`, and its base is cut down further to a standard open
`S''` contained in the base of the shrunk complete dévissage — which is
`AlgebraicGeometry.OneStepDevissage.ShrinkingOpens.restrict`, so that the two shrinkings of
Stacks 05HA the source performs become one.

The shrunk one-step dévissage then is the first stage of a complete dévissage,
by `AlgebraicGeometry.exists_stageIsStandardRestriction_of_shrinkingOpens`, which also
identifies the cokernel of its free-module map with the inverse image of the cokernel of `α`;
and the smooth scheme of that stage sits in a cartesian square over `X'₁`, because both
horizontal morphisms are open immersions and the smooth open is exactly the part of `X'₁` lying
over `S''`. So Stacks 05HK base-changes the shrunk complete dévissage of the cokernel to it and
the two join into one chain. The source open and the base open of the result are open
subschemes, hence elementary étale neighbourhoods.

The empty complete dévissage is the one case in which no shrinking is needed at all: the module
on `X₁` is then zero, so the cokernel of `α` is zero, and the one-step dévissage is already a
complete dévissage of length one on all of `X` over all of `S`.

The shape of the proof is dictated by elaboration rather than by the mathematics. The two
standard opens cut out of `S` and of `X`, the four opens of the shrinking, the open immersion of
the smooth scheme of the shrunk stage and the two comparison morphisms are all introduced as
opaque local constants carrying exactly the properties that are used, because the explicit terms
for them are large and every occurrence of one re-runs the instance search for its open
immersion, for the affineness of its scheme and for the finiteness conditions on the modules
over it. For the same reason the join of the two dévissages is a separate declaration: the two
together exceed the heartbeat budget of one.

Two transports are needed for reasons of elaboration alone. The range of an open immersion takes
the openness as an instance argument, so a rewrite underneath it has no type-correct motive; and
Stacks 05HK produces the base-changed chain at the image of the distinguished point of the stage
above it, which is the base point of the dévissage only up to an equality of points.

## References

* [Stacks Project, Tag 05HR](https://stacks.math.columbia.edu/tag/05HR)
* [Stacks Project, Tag 05HA](https://stacks.math.columbia.edu/tag/05HA)
* [Stacks Project, Tag 05HK](https://stacks.math.columbia.edu/tag/05HK)
* [Stacks Project, Tag 05HM](https://stacks.math.columbia.edu/tag/05HM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Equal open immersions have the same range. This is needed because the range of an open
immersion carries the openness as an instance argument, so that a rewrite underneath it has no
type-correct motive. -/
private lemma opensRange_congr {A B : Scheme.{u}} {u v : A ⟶ B} [IsOpenImmersion u]
    [IsOpenImmersion v] (h : u = v) : u.opensRange = v.opensRange := by
  subst h
  rfl

/-- Quasi-coherence and finite type pass from a module to anything isomorphic to its inverse image
along an open immersion. -/
private lemma isQuasicoherent_and_isFiniteType_of_pullback_iso {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (M : X.Modules) [hq : M.IsQuasicoherent] [M.IsFiniteType] {N : Y.Modules}
    (e : (Scheme.Modules.pullback j).obj M ≅ N) : N.IsQuasicoherent ∧ N.IsFiniteType :=
  ⟨SheafOfModules.isQuasicoherent_of_iso e (Stacks.Modules.isQuasicoherent_pullback j M hq),
    SheafOfModules.isFiniteType_of_iso e
      (SheafOfModules.pullback_isFiniteType j.toLRSHom.toShHom M)⟩

/-- Evaluating both sides of an equation of composites at a point. -/
private lemma apply_eq_of_comp_eq {X Y Z : Scheme.{u}} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Z}
    (h : a ≫ b = c) (p : X) : b (a p) = c p := by
  subst h
  rfl

/-- A chain of stages, and its compatible distinguished points, transported along an equality of
the base point of the dévissage. The base point enters only as an index, so the transport is a
substitution; it is needed because Stacks 05HK produces the base-changed chain at the image of
the distinguished point of the stage above it, which is the base point of the dévissage only up
to that equality. -/
private def chainCongrPoint {S : Scheme.{u}} {s t : S} (h : s = t) {X : Scheme.{u}}
    {f : X ⟶ S} {F : X.Modules} {hl : LocallyOfFiniteType f} {hq : F.IsQuasicoherent}
    {ht : F.IsFiniteType} {x : X} (C : DevissageChain s X f F hl hq ht)
    (P : PointedDevissageChain s X f F hl hq ht x C) :
    Σ' C' : DevissageChain t X f F hl hq ht,
      PointedDevissageChain t X f F hl hq ht x C' := by
  subst h
  exact ⟨C, P⟩

/-- The join itself. A stage of a complete dévissage of `F/X/S` at `x`, whose smooth scheme sits
in a cartesian square over the source of a complete dévissage of a module identified with the
cokernel of the stage's free-module map, extends that dévissage to a complete dévissage of
`F/X/S` at `x`: Stacks 05HK carries the given dévissage along the square, and the stage is
prepended to the result. -/
private theorem exists_nonemptyCompleteDevissageAt_of_stage {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    [IsAffine S] {s : S} (hfx : f x = s) (D' : DevissageStage f F s)
    (P' : PointedDevissageStage f F s x D') (hqC : D'.coker.IsQuasicoherent)
    (htC : D'.coker.IsFiniteType) (hlY : LocallyOfFiniteType D'.oneStep.g)
    {X₁ S₁ : Scheme.{u}} {f₁ : X₁ ⟶ S₁} {F₁ : X₁.Modules} (hl₁ : LocallyOfFiniteType f₁)
    (hq₁ : F₁.IsQuasicoherent) (ht₁ : F₁.IsFiniteType) {x₁ : X₁}
    (CD : @NonemptyCompleteDevissageAt X₁ S₁ f₁ F₁ x₁ hl₁ hq₁ ht₁) (h : S ⟶ S₁)
    (hres : IsIso (h.residueFieldMap (D'.oneStep.g P'.y))) (pX : D'.oneStep.Y ⟶ X₁)
    (hsq : IsPullback pX D'.oneStep.g f₁ h) (hs : h (D'.oneStep.g P'.y) = f₁ x₁)
    (hx : pX P'.y = x₁) (eF : (Scheme.Modules.pullback pX).obj F₁ ≅ D'.coker) :
    Nonempty (NonemptyCompleteDevissageAt f F x) := by
  subst hfx
  have := hl₁
  have := hq₁
  have := ht₁
  have := hqC
  have := htC
  have := hlY
  obtain ⟨CH, hbc⟩ := exists_completeDevissage_baseChange (h := h)
    (s' := D'.oneStep.g P'.y) hs CD.toNonemptyCompleteDevissage pX hsq eF
  obtain ⟨DAt, -, -⟩ := exists_completeDevissageAt_baseChange (h := h) (x' := P'.y) hs hres
    CD pX hsq eF hx CH hbc
  obtain ⟨tail, tailP⟩ :=
    chainCongrPoint (P'.g_y rfl) DAt.toNonemptyCompleteDevissage.chain DAt.pointed
  exact ⟨⟨⟨DevissageChain.more D' hqC htC hlY tail⟩,
    PointedDevissageChain.more x D' hqC htC hlY tail P' tailP⟩⟩

/-- **The final paragraph of the proof of Stacks Project, Tag 05HR.** Suppose given a one-step
dévissage `D` of `F/X/S` at `x`, a map `α` from a free module of rank `r` on its smooth scheme
`Y` to the direct image of its module which is an isomorphism over the residue field of the
generic point of the distinguished fibre of `Y`, an open immersion of `Y` into a scheme `X₁` over
`S` carrying a module `F₁` whose restriction to `Y` is the cokernel of `α`, and a complete
dévissage of `F₁/X₁/S` at the image of the distinguished point `y` of `D`. Then `F/X/S` acquires
a complete dévissage at `x` after elementary étale neighbourhoods of `x` and of its image —
namely on a standard open of `X` over a standard open of `S`. -/
theorem exists_etaleNeighborhood_completeDevissageAt_of_cokernelDevissage {X S : Scheme.{u}}
    (f : X ⟶ S) (F : X.Modules) (x : X) [hlf : LocallyOfFiniteType f] [hqf : F.IsQuasicoherent]
    [htf : F.IsFiniteType] (D : OneStepDevissageAt f F x) (r : ℕ)
    (α : SheafOfModules.free (R := D.toOneStepDevissage.Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
      (Scheme.Modules.pushforward D.toOneStepDevissage.π).obj D.toOneStepDevissage.G)
    (hα : IsIso ((Scheme.Modules.pullback (D.toOneStepDevissage.Y.fromSpecResidueField
      (D.toOneStepDevissage.g.fiberι (f x)
        D.toOneStepDevissage.fiberGenericPoint))).map α))
    {X₁ : Scheme.{u}} (f₁ : X₁ ⟶ S) (F₁ : X₁.Modules)
    (hl₁ : LocallyOfFiniteType f₁) (hq₁ : F₁.IsQuasicoherent) (ht₁ : F₁.IsFiniteType)
    (jY : D.toOneStepDevissage.Y ⟶ X₁) (hjY : IsOpenImmersion jY)
    (hjf : jY ≫ f₁ = D.toOneStepDevissage.g)
    (hcok : letI := hl₁; letI := hq₁; letI := ht₁
      Nonempty ((Scheme.Modules.pullback jY).obj F₁ ≅ cokernel α))
    (hCD : letI := hl₁; letI := hq₁; letI := ht₁
      Nonempty (CompleteDevissageAt f₁ F₁ (jY D.y))) :
    ∃ (U : EtaleNeighborhood X x) (V : EtaleNeighborhood S (f x)) (h : U.scheme ⟶ V.scheme),
      U.IsElementary ∧ V.IsElementary ∧ (U.toBase ≫ f = h ≫ V.toBase) ∧ (h U.point = V.point) ∧
        ∃ (hft : LocallyOfFiniteType h)
          (hq : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent)
          (hf : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType),
          letI : LocallyOfFiniteType h := hft
          letI : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent := hq
          letI : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType := hf
          Nonempty (CompleteDevissageAt h
            ((Scheme.Modules.pullback U.toBase).obj F) U.point) := by
  classical
  have := hl₁
  have := hq₁
  have := ht₁
  have := hjY
  obtain ⟨eC⟩ := hcok
  obtain ⟨CD⟩ := hCD
  obtain ⟨hcq, hct⟩ := isQuasicoherent_and_isFiniteType_of_pullback_iso jY F₁ eC
  have hfjY : ∀ p : D.toOneStepDevissage.Y, f₁ (jY p) = D.toOneStepDevissage.g p :=
    apply_eq_of_comp_eq hjf
  cases CD with
  | empty hzero =>
    -- The module on `X₁` is zero, so the cokernel of `α` is zero and the one-step dévissage is
    -- already a complete dévissage of `F/X/S` at `x`.
    have hz : IsZero (cokernel α) :=
      ((Scheme.Modules.pullback jY).map_isZero hzero).of_iso eC.symm
    obtain ⟨hqI, hfI⟩ := isQuasicoherent_and_isFiniteType_of_pullback_iso (𝟙 X) F (Iso.refl _)
    refine ⟨EtaleNeighborhood.self X x, EtaleNeighborhood.self S (f x), f,
      EtaleNeighborhood.isElementary_self X x, EtaleNeighborhood.isElementary_self S (f x),
      (Category.id_comp f).trans (Category.comp_id f).symm, rfl, hlf, hqI, hfI, ⟨?_⟩⟩
    exact @CompleteDevissageAt.ofModuleIso X S f F ((Scheme.Modules.pullback (𝟙 X)).obj F)
      hlf hqf htf hqI hfI x
      (.nonempty (NonemptyCompleteDevissageAt.ofOneStepDevissageAt D r α hα hz))
      ((Scheme.Modules.pullbackId X).app F)
  | nonempty data =>
    -- Stacks 05HM (3): shrink the complete dévissage so that its source lies inside `Y`.
    obtain ⟨E, hEsub⟩ := NonemptyCompleteDevissageAt.exists_standardShrinking_source f₁ F₁
      (jY D.y) data jY.opensRange ⟨D.y, rfl⟩
    have := E.locally_finite_type
    have := E.quasi_coherent
    have := E.finite_type
    have hbaseE : f x ∈ E.S' := by
      have h := E.mem_base
      rwa [hfjY D.y, D.g_y] at h
    -- Stacks 05HA (2): shrink the one-step dévissage so that its smooth open is the open of `Y`
    -- cut out by the source of the shrunk complete dévissage.
    have hW : jY ⁻¹ᵁ E.X' =
        D.toOneStepDevissage.Y.basicOpen (jY.appTop E.source_section) := by
      rw [E.source_standard, Scheme.preimage_basicOpen_top]
    obtain ⟨S₂, X₂, A, hAY⟩ := exists_shrinkingOpens_smooth f F x D (jY ⁻¹ᵁ E.X')
      (jY.appTop E.source_section) hW E.mem_source
    -- Cut the base down to a standard open inside the base of the shrunk complete dévissage.
    obtain ⟨SU, XU, A', hA'Y, hSUle, hSUaff⟩ :
        ∃ (SU : S.Opens) (XU : X.Opens)
          (A' : D.toOneStepDevissage.ShrinkingOpens x D.y SU XU),
          A'.Y' = (jY ⁻¹ᵁ E.X') ⊓ D.toOneStepDevissage.g ⁻¹ᵁ SU ∧ SU ≤ E.S' ∧
            IsAffine SU.toScheme := by
      have hSU : S₂ ⊓ E.S' = S.basicOpen (A.base_section * E.base_section) := by
        rw [Scheme.basicOpen_mul, ← A.base_standard, ← E.base_standard]
      have hSaff : IsAffine S := D.toOneStepDevissage.affine_S
      refine ⟨S₂ ⊓ E.S', X₂ ⊓ f ⁻¹ᵁ (S₂ ⊓ E.S'),
        A.restrict (S₂ ⊓ E.S') (A.base_section * E.base_section) hSU inf_le_left
          ⟨A.mem_base, hbaseE⟩ D.g_y, ?_, inf_le_right, ?_⟩
      · change A.Y' ⊓ D.toOneStepDevissage.g ⁻¹ᵁ (S₂ ⊓ E.S') = _
        rw [hAY, inf_assoc,
          inf_eq_right.mpr (D.toOneStepDevissage.g.preimage_mono (inf_le_left :
            S₂ ⊓ E.S' ≤ S₂))]
      · rw [hSU]
        infer_instance
    -- The stage the shrunk one-step dévissage and the restriction of `α` define.
    let stage : DevissageStage f F (f x) := DevissageStage.ofOneStepDevissageAt D r α hα
    let P : PointedDevissageStage f F (f x) x stage :=
      PointedDevissageStage.ofOneStepDevissageAt D r α hα
    have hqM : (F.restrict XU.ι).IsQuasicoherent := inferInstance
    have hfM : (F.restrict XU.ι).IsFiniteType :=
      Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict _ F
    obtain ⟨D', P', R, hpoint, hcart, hYeq, hjYheq, -, -⟩ :=
      exists_stageIsStandardRestriction_of_shrinkingOpens stage P A'
        (F.restrict XU.ι) (Iso.refl _)
    -- The open immersion of the smooth scheme of the first stage into the smooth scheme of the
    -- one-step dévissage, with the four properties of it the join uses.
    obtain ⟨jR, hoR, hjRrange, hjRsm, hjRy, ⟨ecok⟩⟩ :
        ∃ (j : D'.oneStep.Y ⟶ D.toOneStepDevissage.Y) (hj : IsOpenImmersion j),
          @Scheme.Hom.opensRange _ _ j hj = A'.Y' ∧
            j ≫ D.toOneStepDevissage.g = D'.oneStep.g ≫ SU.ι ∧
            j P'.y = D.y ∧
            Nonempty ((Scheme.Modules.pullback j).obj (cokernel α) ≅ D'.coker) :=
      ⟨R.jY, R.openImmersion_jY,
        @opensRange_eq_of_heq_ι _ _ A'.Y' R.jY R.openImmersion_jY hYeq hjYheq,
        R.smooth_comm, hpoint.y_eq,
        ⟨cokernelIsoOfStageIsStandardRestriction R hcart⟩⟩
    have := hoR
    have hlY : LocallyOfFiniteType D'.oneStep.g :=
      have := D'.oneStep.smooth
      inferInstance
    -- The cokernel of the first stage is the inverse image of the cokernel of `α`.
    obtain ⟨hqC, htC⟩ := isQuasicoherent_and_isFiniteType_of_pullback_iso jR (cokernel α) ecok
    -- The smooth scheme of the first stage sits over the source of the shrunk chain.
    have hrangeLe : (jR ≫ jY).opensRange ≤ E.X' := by
      rw [Scheme.Hom.opensRange_comp, hjRrange, hA'Y]
      exact le_trans (jY.image_mono inf_le_left)
        ((jY.image_preimage_eq_opensRange_inf E.X').trans_le inf_le_right)
    have hsub : Set.range (jR ≫ jY).base ⊆ Set.range E.X'.ι.base := by
      rintro z ⟨w, rfl⟩
      exact ⟨⟨_, hrangeLe ⟨w, rfl⟩⟩, rfl⟩
    obtain ⟨pX, hoX, hpXfac⟩ :
        ∃ p : D'.oneStep.Y ⟶ E.X'.toScheme, IsOpenImmersion p ∧ p ≫ E.X'.ι = jR ≫ jY :=
      ⟨IsOpenImmersion.lift E.X'.ι (jR ≫ jY) hsub, inferInstance,
        IsOpenImmersion.lift_fac _ _ _⟩
    have := hoX
    have hf₁r : E.restricted_morphism ≫ E.S'.ι = E.X'.ι ≫ f₁ := by
      rw [E.restricted_morphism_eq]
      exact Scheme.Hom.resLE_comp_ι f₁ E.source_over_base
    obtain ⟨jS, hoS, hjSι, hjSr⟩ :
        ∃ (j : SU.toScheme ⟶ E.S'.toScheme) (hj : IsOpenImmersion j),
          j ≫ E.S'.ι = SU.ι ∧
            @Scheme.Hom.opensRange _ _ j hj = E.S'.ι ⁻¹ᵁ SU :=
      ⟨S.homOfLE hSUle, inferInstance, Scheme.homOfLE_ι S _,
        Scheme.opensRange_homOfLE _⟩
    have := hoS
    -- The square of the two open immersions is cartesian.
    have hgpre : D.toOneStepDevissage.g ⁻¹ᵁ SU =
        jY ⁻¹ᵁ (f₁ ⁻¹ᵁ SU) := by
      rw [← Scheme.Hom.comp_preimage, hjf]
    have hpXr : E.X'.ι ''ᵁ pX.opensRange = E.X' ⊓ f₁ ⁻¹ᵁ SU :=
      calc E.X'.ι ''ᵁ pX.opensRange
          = (pX ≫ E.X'.ι).opensRange := (Scheme.Hom.opensRange_comp pX E.X'.ι).symm
        _ = (jR ≫ jY).opensRange := opensRange_congr hpXfac
        _ = jY ''ᵁ jR.opensRange := Scheme.Hom.opensRange_comp jR jY
        _ = jY ''ᵁ (jY ⁻¹ᵁ (E.X' ⊓ f₁ ⁻¹ᵁ SU)) := by
            rw [hjRrange, hA'Y, hgpre, ← Scheme.Hom.preimage_inf]
        _ = E.X' ⊓ f₁ ⁻¹ᵁ SU := by
            rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
              inf_eq_right.mpr (le_trans inf_le_left hEsub)]
    have hH' : E.restricted_morphism ⁻¹ᵁ jS.opensRange = pX.opensRange := by
      have hlhs : E.X'.ι ''ᵁ (E.restricted_morphism ⁻¹ᵁ jS.opensRange) =
          E.X' ⊓ f₁ ⁻¹ᵁ SU := by
        rw [hjSr, ← Scheme.Hom.comp_preimage, hf₁r, Scheme.Hom.comp_preimage,
          Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact E.X'.ι.image_injective (hlhs.trans hpXr.symm)
    have hcomm : pX ≫ E.restricted_morphism = D'.oneStep.g ≫ jS := by
      apply (cancel_mono E.S'.ι).mp
      have h1 : (pX ≫ E.restricted_morphism) ≫ E.S'.ι = jR ≫ D.toOneStepDevissage.g := by
        rw [Category.assoc, hf₁r, ← Category.assoc, hpXfac, Category.assoc, hjf]
      have h2 : (D'.oneStep.g ≫ jS) ≫ E.S'.ι = jR ≫ D.toOneStepDevissage.g := by
        rw [Category.assoc, hjSι]
        exact hjRsm.symm
      exact h1.trans h2.symm
    have hsq : IsPullback pX D'.oneStep.g E.restricted_morphism jS :=
      (IsOpenImmersion.isPullback D'.oneStep.g pX jS E.restricted_morphism hcomm hH').flip
    -- Identify the module on the smooth scheme of the first stage with its cokernel.
    have eF : (Scheme.Modules.pullback pX).obj (F₁.restrict E.X'.ι) ≅ D'.coker :=
      (Scheme.Modules.pullback pX).mapIso
          ((Scheme.Modules.restrictFunctorIsoPullback E.X'.ι).app F₁) ≪≫
        (Scheme.Modules.pullbackComp pX E.X'.ι).app F₁ ≪≫
        (Scheme.Modules.pullbackCongr hpXfac).app F₁ ≪≫
        ((Scheme.Modules.pullbackComp jR jY).app F₁).symm ≪≫
        (Scheme.Modules.pullback jR).mapIso eC ≪≫ ecok
    -- The base points.
    have hpt : f.resLE SU XU A'.source_over_base
          ⟨x, A'.mem_source⟩ = (⟨f x, A'.mem_base⟩ : SU.toScheme) :=
      Subtype.ext (Scheme.Hom.coe_resLE_apply f A'.source_over_base ⟨x, A'.mem_source⟩)
    have hsbase : jS (D'.oneStep.g P'.y) = E.restricted_morphism ⟨jY D.y, E.mem_source⟩ := by
      apply E.S'.ι.isOpenEmbedding.injective
      have h1 : E.S'.ι (jS (D'.oneStep.g P'.y)) = f x := by
        exact (apply_eq_of_comp_eq hjSι _).trans (congrArg SU.ι (P'.g_y hpt))
      have h2 : E.S'.ι (E.restricted_morphism ⟨jY D.y, E.mem_source⟩) = f x :=
        (apply_eq_of_comp_eq hf₁r ⟨jY D.y, E.mem_source⟩).trans
          ((hfjY D.y).trans D.g_y)
      exact h1.trans h2.symm
    have hxpt : pX P'.y = (⟨jY D.y, E.mem_source⟩ : E.X'.toScheme) := by
      apply E.X'.ι.isOpenEmbedding.injective
      exact (apply_eq_of_comp_eq hpXfac P'.y).trans (congrArg jY hjRy)
    -- Stacks 05HK carries the shrunk complete dévissage to the smooth scheme of the first
    -- stage, and the first stage is prepended to it.
    have hlfU := locallyOfFiniteType_resLE f SU XU A'.source_over_base
    obtain ⟨DJ⟩ := exists_nonemptyCompleteDevissageAt_of_stage
      (f.resLE SU XU A'.source_over_base)
      (F.restrict XU.ι) ⟨x, A'.mem_source⟩ hpt D' P' hqC htC hlY
      E.locally_finite_type E.quasi_coherent E.finite_type E.restricted_devissage jS
      inferInstance pX hsq hsbase hxpt eF
    obtain ⟨hqU, hfU⟩ := isQuasicoherent_and_isFiniteType_of_pullback_iso XU.ι F (Iso.refl _)
    refine ⟨EtaleNeighborhood.ofEtale XU.ι ⟨x, A'.mem_source⟩,
      EtaleNeighborhood.ofEtale SU.ι ⟨f x, A'.mem_base⟩,
      f.resLE SU XU A'.source_over_base,
      EtaleNeighborhood.isElementary_ofEtale_of_isOpenImmersion _ _,
      EtaleNeighborhood.isElementary_ofEtale_of_isOpenImmersion _ _,
      (Scheme.Hom.resLE_comp_ι f A'.source_over_base).symm, hpt, hlfU, hqU, hfU, ⟨?_⟩⟩
    exact @CompleteDevissageAt.ofModuleIso XU.toScheme SU.toScheme
      (f.resLE SU XU A'.source_over_base) (F.restrict XU.ι) ((Scheme.Modules.pullback XU.ι).obj F)
      hlfU hqM hfM hqU hfU ⟨x, A'.mem_source⟩ (.nonempty DJ)
      ((Scheme.Modules.restrictFunctorIsoPullback XU.ι).app F).symm

end AlgebraicGeometry

end
