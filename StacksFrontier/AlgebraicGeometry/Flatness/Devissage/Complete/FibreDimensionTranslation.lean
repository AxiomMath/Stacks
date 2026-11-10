module

public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.SpecTranslation
public import StacksFrontier.RingTheory.Flat.CompleteDevissageFibreDimension

/-!
# A scheme-theoretic complete dévissage at a point has fibres of the relative dimension

The smooth scheme `Y` of a one-step dévissage of `ℱ/X/S` has, by Stacks 05H4 (5), fibres of
dimension `dim(Supp(ℱ_s))` over every point of `S`
(`AlgebraicGeometry.OneStepDevissage.fiber_dimension`). Read on rings, every fibre of
`Spec Γ(Y, ⊤) → Spec Γ(S, ⊤)` has the relative dimension of `Γ(S, ⊤) → Γ(Y, ⊤)`, which is
`Module.DevissageStageData.FibresHaveRelativeDimension` for the algebraic stage built from the
one-step dévissage. This file carries that condition through the translation of a geometric
complete dévissage at a point into an algebraic one, on global sections and then for a ring map.

## Main results

* `AlgebraicGeometry.OneStepDevissage.fibresHaveRelativeDimension_toDevissageStage`: the
  algebraic stage of a one-step dévissage has fibres of its relative dimension.
* `Module.exists_completeDevissageAt_fibresHaveRelativeDimension_of_completeDevissageAt`: a
  complete dévissage of `ℱ/X/S` at `x` gives a complete dévissage of
  `Γ(ℱ, ⊤)/Γ(X, ⊤)/Γ(S, ⊤)` at the prime of `x` whose stages have fibres of their relative
  dimension.
* `AlgebraicGeometry.exists_completeDevissageAt_fibresHaveRelativeDimension_of_spec`: the same
  for `Ñ/Spec B/Spec A` and `N/B/A`.

## References

* [Stacks Project, Tag 05H4](https://stacks.math.columbia.edu/tag/05H4)
* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The algebraic stage of a one-step dévissage has fibres of its relative dimension.** Every
fibre of `Spec Γ(Y, ⊤) → Spec Γ(S, ⊤)` has the dimension of the support of `ℱ_s`, by
`AlgebraicGeometry.OneStepDevissage.fiber_dimension`, and so does the relative dimension. -/
public theorem OneStepDevissage.fibresHaveRelativeDimension_toDevissageStage {X S : Scheme.{u}}
    {f : X ⟶ S} {F : X.Modules} {s : S} [LocallyOfFiniteType f] [F.IsQuasicoherent]
    [F.IsFiniteType] (D : OneStepDevissage f F s) (r : Ideal Γ(S, ⊤))
    [r.IsPrime] (multiplicity : ℕ)
    (alpha :
      letI := D.algebraSmooth
      letI : Module Γ(D.Y, ⊤) Γ(D.G, ⊤) := Module.compHom Γ(D.G, ⊤) D.π.appTop.hom
      (Fin multiplicity →₀ Γ(D.Y, ⊤)) →ₗ[Γ(D.Y, ⊤)] Γ(D.G, ⊤))
    (fiber_bijective :
      letI := D.algebraSmooth
      letI : Module Γ(D.Y, ⊤) Γ(D.G, ⊤) := Module.compHom Γ(D.G, ⊤) D.π.appTop.hom
      letI : (Ideal.map (algebraMap Γ(S, ⊤) Γ(D.Y, ⊤)) r).IsPrime := D.map_isPrime_g_appTop r
      Function.Bijective
        (alpha.baseChange (Ideal.map (algebraMap Γ(S, ⊤) Γ(D.Y, ⊤)) r).ResidueField)) :
    (D.toDevissageStage r multiplicity alpha fiber_bijective).FibresHaveRelativeDimension :=
  fun p => (D.topologicalKrullDim_fiber_eq_topologicalKrullDim_supp p).trans
    D.relativeDimension_eq_topologicalKrullDim_supp.symm

/-- **The pointed algebraic dévissage translated from a chain of stages with compatible
distinguished points has fibres of the relative dimension at every stage.** Each stage is the
algebraic stage of a one-step dévissage. -/
public theorem PointedDevissageChain.fibresHaveRelativeDimension_toPointedCompleteDevissage
    {S : Scheme.{u}} [IsAffine S] {s : S} (r : Ideal Γ(S, ⊤)) [r.IsPrime]
    (hr : (S.isoSpec.hom s).asIdeal = r) :
    {X : Scheme.{u}} → [IsAffine X] → {f : X ⟶ S} → {F : X.Modules} →
      {hl : LocallyOfFiniteType f} → {hq : F.IsQuasicoherent} → {ht : F.IsFiniteType} →
      {x : X} → (q : Ideal Γ(X, ⊤)) → (hqp : q.IsPrime) →
      (hqx : (X.isoSpec.hom x).asIdeal = q) → (hfx : f x = s) →
      {chain : DevissageChain s X f F hl hq ht} →
      (P : PointedDevissageChain s X f F hl hq ht x chain) →
      letI := f.appTop.hom.toAlgebra
      letI : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) :=
        HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f hl
      letI : Module.Finite Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) :=
        letI := hq
        letI := ht
        Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
      letI := hqp
      (P.toPointedCompleteDevissage r hr q hqp hqx
        hfx).toCompleteDevissage.FibresHaveRelativeDimension
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .last _ stage _hzero _pointed =>
      fun _ => stage.oneStep.fibresHaveRelativeDimension_toDevissageStage r stage.rank
        stage.sectionsAlpha (stage.fiber_bijective_sectionsAlpha r hr)
  | X, _, f, F, hl, hq, ht, _x, q, hqp, hqx, hfx, _,
      .more _ stage hqc hft _hlft _chain pointed tail =>
      let := f.appTop.hom.toAlgebra
      let : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) :=
        HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f hl
      let : Module.Finite Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) :=
        let := hq
        let := ht
        Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
      let := hqp
      let := stage.oneStep.affine_Y
      let : Module.Finite Γ(stage.oneStep.Y, ⊤) Γ(stage.coker, (⊤ : stage.oneStep.Y.Opens)) :=
        let := hqc
        let := hft
        Stacks.AlgebraicGeometry.CoherentFinite.finite_sections stage.coker
          (isAffineOpen_top stage.oneStep.Y)
      let hP := pointed.exists_toPointed hfx r hr q hqp hqx
      @Module.CompleteDevissage.fibresHaveRelativeDimension_consStageData _ _ _ _ _ _ _ _ _ _ _ _
        (stage.oneStep.toDevissageStage r stage.rank stage.sectionsAlpha
          (stage.fiber_bijective_sectionsAlpha r hr)) _ _ _ _
        Γ(stage.coker, (⊤ : stage.oneStep.Y.Opens)) inferInstance
        (inferInstanceAs
          (Module Γ(stage.oneStep.Y, ⊤) Γ(stage.coker, (⊤ : stage.oneStep.Y.Opens))))
        (inferInstanceAs
          (Module.Finite Γ(stage.oneStep.Y, ⊤) Γ(stage.coker, (⊤ : stage.oneStep.Y.Opens))))
        _ _
        (stage.oneStep.fibresHaveRelativeDimension_toDevissageStage r stage.rank
          stage.sectionsAlpha (stage.fiber_bijective_sectionsAlpha r hr))
        (tail.fibresHaveRelativeDimension_toPointedCompleteDevissage r hr hP.choose.lowerPrime
          hP.choose.lowerPrime_isPrime hP.choose_spec.1.symm (pointed.g_y hfx))

end AlgebraicGeometry

namespace Module

/-- **A complete dévissage of `ℱ/X/S` at `x` gives a complete dévissage of
`Γ(ℱ, ⊤)/Γ(X, ⊤)/Γ(S, ⊤)` at the prime of `x` whose stages have fibres of their relative
dimension.** This is `Module.nonempty_completeDevissageAt_of_completeDevissageAt` together with
the fibre-dimension condition of Stacks 05H4 (5) for every stage, read on rings. -/
public theorem exists_completeDevissageAt_fibresHaveRelativeDimension_of_completeDevissageAt
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] {f : X ⟶ S} {F : X.Modules} {x : X}
    [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent] [ht : F.IsFiniteType]
    (q : Ideal Γ(X, ⊤)) (hqp : q.IsPrime) (hqx : (X.isoSpec.hom x).asIdeal = q)
    (D : AlgebraicGeometry.CompleteDevissageAt f F x) :
    letI := f.appTop.hom.toAlgebra
    letI : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) :=
      HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f hl
    letI : Module.Finite Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) :=
      Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
    letI := hqp
    ∃ E : Module.CompleteDevissageAt Γ(S, ⊤) Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) q,
      E.FibresHaveRelativeDimension := by
  let _ := f.appTop.hom.toAlgebra
  let _ : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f hl
  let _ : Module.Finite Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
  let _ := hqp
  cases D with
  | empty hF =>
      exact ⟨.empty (Stacks.Algebraization.subsingleton_sections_of_isZero hF ⊤), trivial⟩
  | nonempty data =>
      let _ := (S.isoSpec.hom (f x)).isPrime
      exact ⟨.nonempty ((data.pointed.toPointedCompleteDevissage (S.isoSpec.hom (f x)).asIdeal
          rfl q hqp hqx rfl).toNonemptyCompleteDevissageAt
          (AlgebraicGeometry.comap_asIdeal_isoSpec_hom f x (f x) rfl q hqx
            (S.isoSpec.hom (f x)).asIdeal rfl)),
        PointedCompleteDevissage.fibresHaveRelativeDimension_toNonemptyCompleteDevissageAt _ _
          (data.pointed.fibresHaveRelativeDimension_toPointedCompleteDevissage
            (S.isoSpec.hom (f x)).asIdeal rfl q hqp hqx rfl)⟩

end Module

namespace AlgebraicGeometry

/-- **A complete dévissage of `Ñ/Spec B/Spec A` at the point of `q` gives a complete dévissage of
`N/B/A` at `q` whose stages have fibres of their relative dimension.** This is
`AlgebraicGeometry.geometricCompleteDevissageAtGivesAlgebraic` together with the fibre-dimension
condition of Stacks 05H4 (5) for every stage, read on rings: the dévissage is translated on
global sections and carried back to `A`, `B` and `N` by
`Module.CompleteDevissageAt.ofRingEquiv`, which does not change the stage algebras. -/
public theorem exists_completeDevissageAt_fibresHaveRelativeDimension_of_spec (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B] (N : Type u)
    [AddCommGroup N] [Module B N] [Module.Finite B N] (q : PrimeSpectrum B)
    (hD : Nonempty (@CompleteDevissageAt (Spec (.of B)) (Spec (.of A))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (tilde (R := .of B) (ModuleCat.of B N)) q
      (locallyOfFiniteType_specMap_algebraMap A B) inferInstance
      ((tilde_isFiniteType_iff (R := .of B) (ModuleCat.of B N)).2 inferInstance))) :
    ∃ E : @Module.CompleteDevissageAt A B N _ _ _ _ _ _ _ q.asIdeal q.isPrime,
      E.FibresHaveRelativeDimension := by
  obtain ⟨D⟩ := hD
  have hqp : q.asIdeal.IsPrime := q.isPrime
  set X : Scheme.{u} := Spec (CommRingCat.of B)
  set S : Scheme.{u} := Spec (CommRingCat.of A)
  set M : ModuleCat.{u} (CommRingCat.of B) := ModuleCat.of B N
  set f : X ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap A B))
  set F : X.Modules := tilde M
  have hl : LocallyOfFiniteType f := locallyOfFiniteType_specMap_algebraMap A B
  have ht : F.IsFiniteType := (tilde_isFiniteType_iff M).2 inferInstance
  have hQp : ((X.isoSpec.hom q).asIdeal).IsPrime := (X.isoSpec.hom q).isPrime
  obtain ⟨E, hE⟩ :=
    @Module.exists_completeDevissageAt_fibresHaveRelativeDimension_of_completeDevissageAt
      X S _ _ f F q hl _ ht (X.isoSpec.hom q).asIdeal hQp rfl D
  let eR : ↥Γ(S, ⊤) ≃+* A := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  let eS : ↥Γ(X, ⊤) ≃+* B := (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv
  let eN : ↥Γ(F, (⊤ : X.Opens)) ≃+ N := (tilde.isoTop M).toLinearEquiv.symm.toAddEquiv
  let algΓ : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := (Scheme.Hom.appTop f).hom.toAlgebra
  let ftΓ : Algebra.FiniteType ↥Γ(S, ⊤) ↥Γ(X, ⊤) :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f hl
  let finΓ : Module.Finite ↥Γ(X, ⊤) ↥Γ(F, (⊤ : X.Opens)) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
  let instB : Module B ↥Γ(F, (⊤ : X.Opens)) :=
    inferInstanceAs (Module ↥(CommRingCat.of B) ↥(moduleSpecΓFunctor.obj F))
  have halg : ∀ x : ↥Γ(S, ⊤), algebraMap A B (eR x) = eS (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤) x) :=
    fun x => (congrArg (fun k : Γ(S, ⊤) ⟶ CommRingCat.of B => k.hom x)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B)))).symm
  have hinv : ∀ s : ↥Γ(X, ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (eS s) = s := fun s =>
    congrArg (fun k : Γ(X, ⊤) ⟶ Γ(X, ⊤) => k.hom s)
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom_inv_id
  have hsmul : ∀ (s : ↥Γ(X, ⊤)) (n : ↥Γ(F, (⊤ : X.Opens))), eN (s • n) = eS s • eN n := by
    intro s n
    have hact : (eS s) • n = s • n := by
      change ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (eS s)) • n = s • n
      rw [hinv]
    rw [← hact]
    exact (tilde.isoTop M).toLinearEquiv.symm.map_smul (eS s) n
  have hprime : (X.isoSpec.hom q).asIdeal = Ideal.comap eS.toRingHom q.asIdeal :=
    asIdeal_isoSpec_hom_spec q
  exact ⟨E.ofRingEquiv eR eS eN halg hsmul hprime,
    Module.CompleteDevissageAt.fibresHaveRelativeDimension_ofRingEquiv eR eS eN halg hsmul
      hprime E hE⟩

end AlgebraicGeometry

end
