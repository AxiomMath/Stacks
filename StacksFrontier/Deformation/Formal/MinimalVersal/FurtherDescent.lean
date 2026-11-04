module

public import StacksFrontier.Deformation.Formal.MinimalVersal.PushforwardMinimality

/-!
# The descended formal object has no proper further descent

Every morphism of formal objects into the descended object is surjective on bases: on each term of
the stage tower the composite with the projection is surjective, because the stage is a minimal
descent object, and the projections of the inverse limit detect surjectivity.

## Main results

* `Deformation.surjective_base_of_hom_to_stageBaseTowerFormalObject`: every morphism of formal
  objects into the descended formal object is surjective on bases.

## References

* [Stacks Project, Tag 06T2](https://stacks.math.columbia.edu/tag/06T2)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w uF vF

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- Every morphism of formal objects into the descended formal object is surjective on bases, so
the descended object admits no proper further formal descent. -/
theorem surjective_base_of_hom_to_stageBaseTowerFormalObject
    [IsNoetherianRing Λ] [Module.Finite Λ k]
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (η : FormalObject p) (f : η ⟶ stageBaseTowerFormalObject hp hS1 ξ hbound) :
    Function.Surjective f.base.hom := by
  classical
  let F₀ := stageBaseTowerFormalObject hp hS1 ξ hbound
  let incl := stageBaseTowerFormalObjectHom hp hS1 ξ hbound
  let I := stageBaseTowerIdealFiltration hp hS1 ξ hbound
  let R := stageBaseTowerCompleteLocal hp hS1 ξ hbound
  have hFbase : F₀.base = R := by rfl
  let A := stageBaseTower hp hS1 ξ
  let τ := stageBaseTowerTransition hp hS1 ξ
  let π (n : ℕ) := inverseLimitProj A τ n
  let fR : η.base ⟶ R := f.base ≫ eqToHom hFbase
  let πR (n : ℕ) : R →ₐ[Λ] A n := by
    change (inverseLimit A τ) →ₐ[Λ] A n
    exact π n
  let q (n : ℕ) := stageBaseTowerFormalLevelProjection hp hS1 ξ hbound n
  let j (n : ℕ) := stageBaseTowerInclusion hp hS1 ξ n
  have hproj (n : ℕ) : q n ≫ j n = p.map (incl.app n) := by
    simpa [q, j, incl, stageBaseTowerFormalObjectHom] using
      stageBaseTowerFormalObjectApp_projection_fac hp hS1 ξ hbound n
  have hq_mk (n : ℕ) (r : R) :
      (q n).hom ((eqToHom (F₀.level_eq n).symm).hom
        (Ideal.Quotient.mk (AdicTruncation.ideal R n) r)) = π n r := by
    dsimp only [q, stageBaseTowerFormalLevelProjection]
    rw [ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply]
    have hcancel (y) :
        (eqToHom (F₀.level_eq n)).hom ((eqToHom (F₀.level_eq n).symm).hom y) = y := by
      simp [← AlgHom.comp_apply, ← ArtinianLocalAlgCat.comp_hom]
    erw [hcancel]
    exact Ideal.Quotient.lift_mk _ _ _
  have hq (n : ℕ) : Function.Surjective (q n).hom := by
    intro y
    obtain ⟨r, hr⟩ := stageBaseTowerProjection_surjective hp hS1 ξ n y
    let rR : R := by
      change inverseLimit A τ
      exact r
    refine ⟨(eqToHom (F₀.level_eq n).symm).hom
      (Ideal.Quotient.mk (AdicTruncation.ideal R n) rR), ?_⟩
    rw [hq_mk]
    exact hr
  have hstage (n : ℕ) : Function.Surjective
      ((π n).toRingHom.comp f.base.hom.toRingHom) := by
    let Y := ξ.level n
    let Z := F₀.level n
    let g := incl.app n
    let D := descentPushforward p hp g
    let idZ := identityDescent (p := p) Z
    let W := D.functor.obj idZ
    let d := D.inclusion idZ
    let v := W.obj.hom
    let a := eqToHom (ξ.level_eq n).symm
    let b := eqToHom (F₀.level_eq n).symm ≫ p.map d
    have ha : p.IsHomLift a (𝟙 Y) :=
      IsHomLift.id_lift_eqToHom_domain (ξ.level_eq n).symm (ξ.level_eq n)
    have hb : p.IsHomLift b d := by
      have : p.IsHomLift
          (eqToHom (F₀.level_eq n).symm) (𝟙 Z) :=
        IsHomLift.id_lift_eqToHom_domain
          (F₀.level_eq n).symm
          (F₀.level_eq n)
      have : p.IsHomLift (p.map d) d := IsHomLift.map p d
      infer_instance
    have hcomp : p.IsHomLift
        (AdicTruncation.map incl.base n ≫ a) (g ≫ 𝟙 Y) :=
      @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _
        (AdicTruncation.map incl.base n) a (incl.app n) (𝟙 Y)
        (incl.app_lift n) ha
    have hbaseRange : AlgHom.range (p.map g).hom =
        AlgHom.range ((AdicTruncation.map incl.base n ≫ a).hom) := by
      rw [algHom_range_eq_of_isHomLift _ _ hcomp, Category.comp_id]
    have hrange : AlgHom.range (p.map v).hom =
        AlgHom.range ((AdicTruncation.map incl.base n ≫ a).hom) := by
      calc
        AlgHom.range (p.map v).hom =
            AlgHom.range (p.map (idZ.obj.hom ≫ g)).hom := D.base_range idZ
        _ = AlgHom.range (p.map g).hom := by simp [idZ, identityDescent]
        _ = AlgHom.range ((AdicTruncation.map incl.base n ≫ a).hom) := hbaseRange
    have hinc : d ≫ v = incl.app n := by
      simpa [d, v, idZ, identityDescent, g] using D.inclusion_fac idZ
    have hWmin : IsMinimalObject W :=
      isMinimalObject_of_stageBaseTowerFormalObject hp hS1 ξ hbound n
      (a := a) (b := b) (toX := 𝟙 Y) (toY := d) (g := v)
      ha hb (isStronglyCocartesian_of_isCofiberedInGroupoids hp a _ ha)
      (isStronglyCocartesian_of_isCofiberedInGroupoids hp b d hb)
      (by rw [hinc, Category.comp_id])
      hrange W.property
    let u := f.app n ≫ d
    have hu : Function.Surjective (p.map u).hom :=
      map_surjective_into_minimalDescent hp W hWmin u
    -- The image descent is canonically isomorphic to the `n`th tower quotient.
    have hImage : AlgHom.range (p.map v).hom = AlgHom.range (j n).hom := by
      calc
        AlgHom.range (p.map v).hom = AlgHom.range (p.map g).hom :=
          hrange.trans hbaseRange.symm
        _ = AlgHom.range ((q n ≫ j n).hom) := by rw [← hproj]
        _ = AlgHom.range (j n).hom := by
          rw [ArtinianLocalAlgCat.comp_hom]
          exact algHom_range_comp_eq_of_surjective (q n).hom (j n).hom (hq n)
    have hJinj : Function.Injective (j n).hom :=
      stageBaseTowerInclusion_injective hp hS1 ξ n
    have : Mono (j n) := ⟨fun g₁ g₂ h ↦ ArtinianLocalAlgCat.hom_ext <| AlgHom.ext fun x ↦
      hJinj (DFunLike.congr_fun (congrArg ArtinianLocalAlgCat.Hom.hom h) x)⟩
    let e := ArtinianLocalAlgCat.isoOfRangeEq (p.map v) (j n) W.property hJinj hImage
    have hefac : e.hom ≫ j n = p.map v :=
      ArtinianLocalAlgCat.isoOfRangeEq_hom_fac (p.map v) (j n) W.property hJinj hImage
    have hdeq : p.map d ≫ e.hom = q n := by
      rw [← cancel_mono (j n), Category.assoc, hefac, ← p.map_comp, hinc, hproj]
    let qf := p.map u ≫ e.hom
    have hqf_eq : qf = p.map (f.app n) ≫ q n := by
      simp only [qf, u, Functor.map_comp, Category.assoc, hdeq]
    have hqf : Function.Surjective qf.hom := by
      rw [ArtinianLocalAlgCat.comp_hom]
      exact (artinianHom_surjective_of_isIso e.hom).comp hu
    -- A finite quotient of the target base is therefore covered by `f`.
    intro y'
    obtain ⟨z, hz⟩ := hqf y'
    let zη := (eqToHom (η.level_eq n)).hom z
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective zη
    have hr' : (Ideal.Quotient.mk (AdicTruncation.ideal η.base n) r :
        AdicTruncation.obj η.base n) = zη := hr
    have happ : p.map (f.app n) =
        eqToHom (η.level_eq n) ≫ AdicTruncation.map f.base n ≫
          eqToHom (F₀.level_eq n).symm := by
      let : p.IsHomLift (AdicTruncation.map f.base n) (f.app n) := f.app_lift n
      exact IsHomLift.fac' p (AdicTruncation.map f.base n) (f.app n)
    have hmap : (q n).hom ((p.map (f.app n)).hom z) =
        π n (f.base.hom r) := by
      have hv := congrArg
        (fun t : p.obj (η.level n) ⟶
          p.obj (F₀.level n) => t.hom z) happ
      have hv' : (p.map (f.app n)).hom z =
          (eqToHom (F₀.level_eq n).symm).hom
            ((AdicTruncation.map f.base n).hom zη) := by
        simpa [ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply] using hv
      rw [← hr'] at hv'
      change (p.map (f.app n)).hom z =
        (eqToHom (F₀.level_eq n).symm).hom
          ((AdicTruncation.map f.base n).hom
            (Ideal.Quotient.mk (AdicTruncation.ideal η.base n) r :
              AdicTruncation.obj η.base n)) at hv'
      have hmk' : (AdicTruncation.map f.base n).hom
          (Ideal.Quotient.mk (AdicTruncation.ideal η.base n) r :
            AdicTruncation.obj η.base n) =
        Ideal.Quotient.mk (AdicTruncation.ideal F₀.base n) (f.base.hom r) :=
        adicTruncationMap_mk f.base n r
      rw [hv', hmk']
      exact hq_mk n (f.base.hom r)
    rw [hqf_eq] at hz
    exact ⟨r, hmap.symm.trans hz⟩
  have hstageR (n : ℕ) : Function.Surjective
      ((πR n).toRingHom.comp fR.hom.toRingHom) := by
    have hmap : (πR n).toRingHom.comp fR.hom.toRingHom =
        (π n).toRingHom.comp f.base.hom.toRingHom := by
      cases hFbase
      rfl
    rw [hmap]
    exact hstage n
  -- Cofinality of the inverse-limit kernels transfers finite-stage surjectivity to
  -- surjectivity modulo the square of the target maximal ideal.
  have hmodSquare : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal R ^ 2)).comp fR.hom.toRingHom) := by
    obtain ⟨m, hm⟩ := I.le_pow 1
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, hx⟩ := hstageR m (πR m r)
    refine ⟨x, ?_⟩
    apply Ideal.Quotient.eq.mpr
    have hx' : (πR m) (fR.hom x) = (πR m) r := hx
    have hker : fR.hom x - r ∈ I.ideal m := by
      change (πR m) (fR.hom x - r) = 0
      rw [map_sub, hx', sub_self]
    exact hm hker
  have hmem : maximalIdeal η.base = (maximalIdeal R).comap fR.hom := by
    let _ : IsLocalHom fR.hom.toRingHom := fR.isLocal
    exact (maximalIdeal_comap fR.hom.toRingHom).symm
  have hcot : Function.Surjective
      (Ideal.mapCotangent (maximalIdeal η.base) (maximalIdeal R) fR.hom
        hmem.le) := by
    intro c
    obtain ⟨b, rfl⟩ := (maximalIdeal R).toCotangent_surjective c
    obtain ⟨a, ha⟩ := hmodSquare
      (Ideal.Quotient.mk (maximalIdeal R ^ 2) (b : R))
    have hdiff : fR.hom a - b ∈ maximalIdeal R ^ 2 :=
      (Ideal.Quotient.eq.mp ha)
    have hfa : fR.hom a ∈ maximalIdeal R := by
      simpa using (maximalIdeal R).add_mem (Ideal.pow_le_self two_ne_zero hdiff) b.2
    refine ⟨(maximalIdeal η.base).toCotangent ⟨a, hmem ▸ hfa⟩, ?_⟩
    rw [Ideal.mapCotangent_toCotangent]
    exact (Ideal.toCotangent_eq (maximalIdeal R)).mpr hdiff
  have hfR : Function.Surjective fR.hom :=
    (surjective_iff_surjective_cotangentSpaceMap fR).2 hcot
  intro y
  obtain ⟨x, hx⟩ := hfR ((eqToHom hFbase).hom y)
  refine ⟨x, ?_⟩
  have hcast : (eqToHom hFbase).hom (f.base.hom x) =
      (eqToHom hFbase).hom y := by
    simpa [fR, CompleteLocalAlgCat.comp_hom] using hx
  have hinj : Function.Injective (eqToHom hFbase).hom := by
    cases hFbase
    exact fun _ _ h ↦ h
  exact hinj hcast

end Deformation

end
