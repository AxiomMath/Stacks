module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassinTwo.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Impurities
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.FiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.Open.Generizing
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Locus

/-!
# A quasi-finite impurity occurs over an elementary étale neighbourhood

An impurity whose test family is quasi-finite over the base at the distinguished point can be
replaced by one whose test family is an elementary étale neighbourhood of the distinguished
point of the base.

The test family is first restricted to the open locus of quasi-finiteness, where the
distinguished point becomes isolated in its fibre; making a quasi-finite morphism finite by an
elementary étale base change then produces an elementary étale neighbourhood `U` of the
distinguished point and an open `V` of the base change which is finite over `U` and has exactly
one point `v` above the distinguished point of `U`. Since `V ⟶ T` is étale, hence open, the
given specialization lifts to a generalization `v'` of `v`, and the chosen point of the impurity
lifts to a point of the base change along `V`, which stays in the relative assassin because an
étale base change pulls the relative assassin back exactly. Its image in the base change along
`U` is still in the relative assassin, and the closure of that image misses the fibre over the
distinguished point of `U` because `V ⟶ U` is finite with `v` as its only point there.

## Main results

* `AlgebraicGeometry.exists_isImpurity_elementaryEtaleNeighborhood_of_quasiFiniteAt` is the
  source's statement.
* `AlgebraicGeometry.mem_relativeAssassin_map_of_isIso`: an isomorphism of schemes over a base
  carries the relative assassin of a pulled-back module to that of the module itself.

## Implementation notes

The elementary étale neighbourhood produced is the one attached to the quasi-finite locus, with
its distinguished point transported to the distinguished point of the base along
`AlgebraicGeometry.ImpurityDiagram.mapsToChosenPoint`; the conclusion records elementariness of
the neighbourhood built from the fields of the resulting impurity diagram, which is the form in
which the other descent statements for impurities are phrased.

The test family of the resulting impurity diagram is Mathlib's chosen fibre product of the
morphism of the pre-pure situation with the structure morphism of the neighbourhood. Membership
in its relative assassin is obtained from membership over `V` by transporting along the
isomorphism which the cartesian square of `V` over `U` provides.

## References

* [Stacks Project, Tag 05J0](https://stacks.math.columbia.edu/tag/05J0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- An isomorphism of schemes over a base carries the relative assassin of the pullback of a
module to the relative assassin of the module itself. -/
theorem mem_relativeAssassin_map_of_isIso {Z Z' T : Scheme.{u}} (e : Z ⟶ Z') [IsIso e]
    (h : Z' ⟶ T) [LocallyOfFiniteType h] (G : Z'.Modules) [G.IsQuasicoherent] {z : Z}
    (hz : z ∈ Stacks.Divisors.relativeAssassin (e ≫ h)
      ((Scheme.Modules.pullback e).obj G)) :
    e.base z ∈ Stacks.Divisors.relativeAssassin h G := by
  have hiso : (Scheme.Modules.pushforward e).obj ((Scheme.Modules.pullback e).obj G) ≅ G :=
    (asIso ((Scheme.Modules.pullbackPushforwardAdjunction e).unit.app G)).symm
  rw [← relativeAssassin_eq_of_moduleIso h hiso,
    relativeAssassin_pushforward_eq_image e h ((Scheme.Modules.pullback e).obj G)]
  exact ⟨z, hz, rfl⟩

/-- An impurity which, after restriction of its test family to an open subset containing the
distinguished point, admits a finite neighbourhood of that point over an elementary étale
neighbourhood of the base point, occurs over that elementary étale neighbourhood. -/
private theorem exists_isImpurity_of_finiteNeighborhoodAt (P : PrePureSituation.{u})
    (D : ImpurityDiagram P) (hD : IsImpurity P D) (Q : D.T.Opens) (htQ : D.t ∈ Q)
    (N : Stacks.Flatness.FiniteNeighborhoodAt (Q.ι ≫ D.g) (⟨D.t, htQ⟩ : Q.toScheme)) :
    ∃ (D' : ImpurityDiagram P) (hD' : Etale D'.g), IsImpurity P D' ∧
      EtaleNeighborhood.IsElementary
        ({ scheme := D'.T
           point := D'.t
           toBase := D'.g
           etale_toBase := hD'
           map_point := D'.mapsToChosenPoint } : EtaleNeighborhood P.S P.s) := by
  classical
  have hLFT : LocallyOfFiniteType D.toT :=
    MorphismProperty.of_isPullback D.isPullback inferInstance
  let tQ : Q.toScheme := ⟨D.t, htQ⟩
  let gQ : Q.toScheme ⟶ P.S := Q.ι ≫ D.g
  have hgQ : gQ.base tQ = P.s := D.mapsToChosenPoint
  let U : EtaleNeighborhood P.S P.s :=
    { scheme := N.neighborhood.scheme
      point := N.neighborhood.point
      toBase := N.neighborhood.toBase
      etale_toBase := N.neighborhood.etale_toBase
      map_point := N.neighborhood.map_point.trans hgQ }
  have hUelem : U.IsElementary := by
    rw [EtaleNeighborhood.isElementary_iff]
    exact (EtaleNeighborhood.isElementary_iff N.neighborhood).mp N.elementary
  let V : (pullback gQ U.toBase).Opens := N.openSubscheme
  obtain ⟨hVfinite, ⟨v, hv, hvuniq⟩, hvspec⟩ := N.spec
  have hb : ∀ {A B : Scheme.{u}} {f g : A ⟶ B}, f = g → ∀ x, f.base x = g.base x :=
    fun h x ↦ by rw [h]
  /- The two projections of `V`. -/
  let pVT : V.toScheme ⟶ D.T := V.ι ≫ pullback.fst gQ U.toBase ≫ Q.ι
  let pVU : V.toScheme ⟶ U.scheme := V.ι ≫ pullback.snd gQ U.toBase
  have hEtalePVT : Etale pVT := inferInstance
  have hLFTPVT : LocallyOfFiniteType pVT := inferInstance
  have hLQFPVT : LocallyQuasiFinite pVT := inferInstance
  have hFinitePVU : IsFinite pVU := hVfinite
  have hvt : pVT.base v = D.t := by
    change Q.ι.base ((V.ι ≫ pullback.fst gQ U.toBase).base v) = D.t
    rw [(hvspec v hv).1]
    rfl
  have hpVTU : pVT ≫ D.g = pVU ≫ U.toBase := by
    change V.ι ≫ (pullback.fst gQ U.toBase ≫ Q.ι) ≫ D.g =
      (V.ι ≫ pullback.snd gQ U.toBase) ≫ U.toBase
    rw [Category.assoc, Category.assoc]
    exact congrArg (fun k : (pullback gQ U.toBase : Scheme.{u}) ⟶ P.S ↦ V.ι ≫ k)
      (pullback.condition (f := gQ) (g := U.toBase))
  /- Lift the specialization along the étale, hence open, morphism `pVT`. -/
  obtain ⟨v', hv'spec, hv't⟩ :=
    liftsGeneralizations_of_isOpenMap pVT pVT.isOpenMap hvt D.specializes
  have huu' : pVU.base v' ⤳ U.point := by
    have := hv'spec.map pVU.continuous
    rwa [hv] at this
  /- Lift the chosen point of the impurity to the base change along `V`. -/
  let W := pullback D.toT pVT
  let r : W ⟶ D.X_T := pullback.fst D.toT pVT
  let q : W ⟶ V.toScheme := pullback.snd D.toT pVT
  obtain ⟨ζ, hζr₀, hζq₀⟩ := Scheme.Pullback.exists_preimage_pullback D.xi v'
    (show D.toT.base D.xi = pVT.base v' by rw [D.xi_liesOver, hv't])
  have hζr : r.base ζ = D.xi := hζr₀
  have hζq : q.base ζ = v' := hζq₀
  have hWcond : ∀ w : W, D.toT.base (r.base w) = pVT.base (q.base w) := fun w ↦
    hb (pullback.condition (f := D.toT) (g := pVT)) w
  have hζass : ζ ∈ Stacks.Divisors.relativeAssassin q
      ((Scheme.Modules.pullback r).obj (D.pulledBack P)) := by
    refine preimage_relativeAssassin_eq_pullback_of_locallyQuasiFinite D.toT pVT
      (D.pulledBack P) ▸ ?_
    change r.base ζ ∈ Stacks.Divisors.relativeAssassin D.toT (D.pulledBack P)
    rw [hζr]
    exact hD.1
  /- Compare with the base change along `U`. -/
  let XU := pullback P.f U.toBase
  let b : XU ⟶ U.scheme := pullback.snd P.f U.toBase
  let G := (Scheme.Modules.pullback (pullback.fst P.f U.toBase)).obj P.F
  have hcompX : (r ≫ D.toX) ≫ P.f = (q ≫ pVU) ≫ U.toBase :=
    calc
      (r ≫ D.toX) ≫ P.f = r ≫ D.toT ≫ D.g := by rw [Category.assoc, D.isPullback.w]
      _ = (r ≫ D.toT) ≫ D.g := (Category.assoc _ _ _).symm
      _ = (q ≫ pVT) ≫ D.g := by rw [pullback.condition (f := D.toT) (g := pVT)]
      _ = q ≫ pVT ≫ D.g := Category.assoc _ _ _
      _ = q ≫ pVU ≫ U.toBase := by rw [hpVTU]
      _ = (q ≫ pVU) ≫ U.toBase := (Category.assoc _ _ _).symm
  let xmap : W ⟶ XU := pullback.lift (r ≫ D.toX) (q ≫ pVU) hcompX
  have hmapfst : xmap ≫ pullback.fst P.f U.toBase = r ≫ D.toX := pullback.lift_fst _ _ _
  have hmapsnd : xmap ≫ b = q ≫ pVU := pullback.lift_snd _ _ _
  have hbq : ∀ w : W, b.base (xmap.base w) = pVU.base (q.base w) := hb hmapsnd
  have hsq : IsPullback xmap q b pVU := by
    have houter : IsPullback (r ≫ D.toX) q P.f (pVT ≫ D.g) :=
      (IsPullback.of_hasPullback D.toT pVT).paste_horiz D.isPullback
    rw [hpVTU, ← hmapfst] at houter
    exact IsPullback.of_right houter hmapsnd (IsPullback.of_hasPullback P.f U.toBase)
  have hFiniteXmap : IsFinite xmap := MorphismProperty.of_isPullback hsq.flip inferInstance
  have hζassU : ζ ∈ Stacks.Divisors.relativeAssassin q
      ((Scheme.Modules.pullback xmap).obj G) := by
    refine relativeAssassin_eq_of_moduleIso q
      ((Scheme.Modules.pullbackComp xmap (pullback.fst P.f U.toBase)).app P.F ≪≫
        (Scheme.Modules.pullbackCongr hmapfst).app P.F ≪≫
          (Scheme.Modules.pullbackComp r D.toX).symm.app P.F) ▸ hζass
  have hθ : xmap.base ζ ∈ Stacks.Divisors.relativeAssassin b G := by
    let e : W ≅ pullback b pVU := hsq.isoPullback
    have hefst : e.hom ≫ pullback.fst b pVU = xmap := hsq.isoPullback_hom_fst
    have hesnd : e.hom ≫ pullback.snd b pVU = q := hsq.isoPullback_hom_snd
    have hmem : e.hom.base ζ ∈ Stacks.Divisors.relativeAssassin (pullback.snd b pVU)
        ((Scheme.Modules.pullback (pullback.fst b pVU)).obj G) := by
      have eIso : (Scheme.Modules.pullback e.hom).obj
          ((Scheme.Modules.pullback (pullback.fst b pVU)).obj G) ≅
            (Scheme.Modules.pullback xmap).obj G :=
        (Scheme.Modules.pullbackComp e.hom (pullback.fst b pVU)).app G ≪≫
          (Scheme.Modules.pullbackCongr hefst).app G
      refine mem_relativeAssassin_map_of_isIso e.hom (pullback.snd b pVU) _ ?_
      rw [hesnd, relativeAssassin_eq_of_moduleIso q eIso]
      exact hζassU
    have hpre := relativeAssassin_pullback_subset_preimage b pVU G hmem
    exact hb hefst ζ ▸ Set.mem_preimage.mp hpre
  /- The closure of the new chosen point misses the fibre over the distinguished point. -/
  have hdis : closure {xmap.base ζ} ∩ Set.range (b.fiberι U.point) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun y hy ↦ ?_
    obtain ⟨z, hzclose, hzy⟩ : y ∈ xmap.base '' closure ({ζ} : Set W) := by
      rw [← xmap.isClosedMap.closure_image_eq_of_continuous xmap.continuous,
        Set.image_singleton]
      exact hy.1
    have hby : b.base y = U.point := by
      rw [b.range_fiberι] at hy
      exact hy.2
    have hqz : q.base z = v := by
      refine hvuniq (q.base z) ?_
      exact (hbq z).symm.trans ((congrArg b.base hzy).trans hby)
    refine Set.eq_empty_iff_forall_notMem.mp hD.2 (r.base z) ⟨?_, ?_⟩
    · refine specializes_iff_mem_closure.mp ?_
      have hspec : r.base ζ ⤳ r.base z :=
        (specializes_iff_mem_closure.mpr hzclose).map r.continuous
      rwa [hζr] at hspec
    · rw [D.toT.range_fiberι]
      exact Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr
        ((hWcond z).trans (by rw [hqz, hvt])))
  refine ⟨{ T := U.scheme
            g := U.toBase
            t' := pVU.base v'
            t := U.point
            specializes := huu'
            mapsToChosenPoint := U.map_point
            X_T := XU
            toX := pullback.fst P.f U.toBase
            toT := b
            isPullback := IsPullback.of_hasPullback P.f U.toBase
            xi := xmap.base ζ
            xi_liesOver := by rw [hbq, hζq] }, inferInstance, ⟨hθ, hdis⟩, hUelem⟩

/-- **Stacks Project, Tag 05J0.** If a pre-pure situation admits an impurity whose test family
is quasi-finite over the base at the distinguished point, then it admits one whose test family,
pointed at the distinguished point, is an elementary étale neighbourhood of the chosen point of
the base. -/
@[stacks 05J0]
theorem exists_isImpurity_elementaryEtaleNeighborhood_of_quasiFiniteAt
    (P : PrePureSituation.{u})
    (h : ∃ D : ImpurityDiagram P, IsImpurity P D ∧ quasiFiniteAt D.g D.t) :
    ∃ (D : ImpurityDiagram P) (hD : Etale D.g), IsImpurity P D ∧
      EtaleNeighborhood.IsElementary
        ({ scheme := D.T
           point := D.t
           toBase := D.g
           etale_toBase := hD
           map_point := D.mapsToChosenPoint } : EtaleNeighborhood P.S P.s) := by
  obtain ⟨D, hD, hqf⟩ := h
  have htQ : D.t ∈ quasiFiniteLocus D.g := (mem_quasiFiniteLocus_iff D.g D.t).2 hqf
  have hiso : IsIsolatedPoint (((quasiFiniteLocus D.g).ι ≫ D.g).asFiber
      (⟨D.t, htQ⟩ : (quasiFiniteLocus D.g).toScheme)) :=
    ((quasiFiniteAt_tfae ((quasiFiniteLocus D.g).ι ≫ D.g)
        (⟨D.t, htQ⟩ : (quasiFiniteLocus D.g).toScheme)).out 1 2).mp
      ((forall_quasiFiniteAt_iff ((quasiFiniteLocus D.g).ι ≫ D.g)).2
        ⟨inferInstance, inferInstance⟩ _)
  exact exists_isImpurity_of_finiteNeighborhoodAt P D hD (quasiFiniteLocus D.g) htQ
    (Stacks.Flatness.finiteNeighborhoodAt ((quasiFiniteLocus D.g).ι ≫ D.g) _ hiso)

end AlgebraicGeometry

end
