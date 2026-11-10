module

public import StacksFrontier.AlgebraicGeometry.Flatness.Impurity.QuasiFiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.LocallyOfFiniteTypePurity

/-!
# Quasi-finite impurities without quasi-compactness

The argument of [Stacks, Tag 05J0], which replaces an impurity with a quasi-finite test family by
one whose test family is an elementary étale neighbourhood, run for an
`AlgebraicGeometry.ImpurityData`: a morphism only locally of finite type, with no
quasi-compactness hypothesis, which [Stacks, Tag 05J5] observes that the argument never uses.

## Main results

* `AlgebraicGeometry.exists_impurityData_elementaryEtaleNeighborhood_of_quasiFiniteAt`: the
  argument of Tag 05J0 for a morphism which is only locally of finite type.
* `AlgebraicGeometry.exists_isImpurity_elementaryEtaleNeighborhood_iff_quasiFiniteAt`: Tag 05J3,
  parts (2) and (3), the equivalence of the two kinds of test family for a pre-pure situation.
* `AlgebraicGeometry.noElementaryEtaleImpurity_iff_noQuasiFiniteImpurity`: Tag 05J5, the
  equivalence of conditions (1) and (2) for a morphism which is only locally of finite type.

## Implementation notes

The elementary étale neighbourhood produced is the one attached to the quasi-finite locus, with
its distinguished point transported to the distinguished point of the base along
`AlgebraicGeometry.ImpurityData.mapsToChosenPoint`. The test family of the resulting impurity
datum is Mathlib's chosen fibre product of the given morphism with the structure morphism of the
neighbourhood; membership in its relative assassin is transported along the isomorphism which
the cartesian square over the neighbourhood provides
(`AlgebraicGeometry.mem_relativeAssassin_map_of_isIso`).

## References

* [Stacks Project, Tag 05J0](https://stacks.math.columbia.edu/tag/05J0)
* [Stacks Project, Tag 05J3](https://stacks.math.columbia.edu/tag/05J3)
* [Stacks Project, Tag 05J5](https://stacks.math.columbia.edu/tag/05J5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

/-- Pointwise form of a commuting square of morphisms of schemes. -/
private theorem base_comp_apply_eq_of_comp_eq {W X₁ X₂ Z : Scheme.{u}} {a : W ⟶ X₁} {b : X₁ ⟶ Z}
    {c : W ⟶ X₂} {d : X₂ ⟶ Z} (h : a ≫ b = c ≫ d) (w : W) :
    b.base (a.base w) = d.base (c.base w) :=
  congrArg (fun m : W ⟶ Z ↦ m.base w) h

/-- The relative assassin of a module pulled back along `b` and then `a` only depends on the
composite `a ≫ b`. -/
private theorem relativeAssassin_pullback_pullback_eq {A B C D : Scheme.{u}} {a : A ⟶ B}
    {b : B ⟶ C} {c : A ⟶ C} (hc : a ≫ b = c) (q : A ⟶ D) (G : C.Modules) :
    Stacks.Divisors.relativeAssassin q ((Scheme.Modules.pullback a).obj
      ((Scheme.Modules.pullback b).obj G)) =
    Stacks.Divisors.relativeAssassin q ((Scheme.Modules.pullback c).obj G) :=
  relativeAssassin_eq_of_moduleIso q ((Scheme.Modules.pullbackComp a b).app G ≪≫
    (Scheme.Modules.pullbackCongr hc).app G)

/-- In a cartesian square, a point in the relative assassin of the pulled-back module maps into
the relative assassin of the original module. -/
private theorem mem_relativeAssassin_of_isPullback {W Y V U : Scheme.{u}} {fst : W ⟶ Y}
    {snd : W ⟶ V} {f : Y ⟶ U} {g : V ⟶ U} (h : IsPullback fst snd f g) [LocallyOfFiniteType f]
    (G : Y.Modules) [G.IsQuasicoherent] {w : W}
    (hw : w ∈ Stacks.Divisors.relativeAssassin snd ((Scheme.Modules.pullback fst).obj G)) :
    fst.base w ∈ Stacks.Divisors.relativeAssassin f G := by
  let e : W ≅ pullback f g := h.isoPullback
  have hefst : e.hom ≫ pullback.fst f g = fst := h.isoPullback_hom_fst
  have hmem : e.hom.base w ∈ Stacks.Divisors.relativeAssassin (pullback.snd f g)
      ((Scheme.Modules.pullback (pullback.fst f g)).obj G) := by
    refine mem_relativeAssassin_map_of_isIso e.hom (pullback.snd f g) _ ?_
    rwa [h.isoPullback_hom_snd, relativeAssassin_pullback_pullback_eq hefst]
  have hpt : (pullback.fst f g).base (e.hom.base w) = fst.base w :=
    congrArg (fun k : W ⟶ Y ↦ k.base w) hefst
  exact hpt ▸ Set.mem_preimage.mp (relativeAssassin_pullback_subset_preimage f g G hmem)

/-- Given two commutative squares `r ≫ toT = q ≫ p` and `x ≫ b = q ≫ e` with `x` finite, if `v`
is the only point of `V` over `u`, lying over `t`, and the closure of `r ζ` misses the fibre of
`toT` over `t`, then the closure of `x ζ` misses the fibre of `b` over `u`. -/
private theorem closure_inter_range_fiberι_eq_empty_of_isFinite {W X₁ X₂ V T U : Scheme.{u}}
    {r : W ⟶ X₁} {q : W ⟶ V} {toT : X₁ ⟶ T} {p : V ⟶ T} (hrq : r ≫ toT = q ≫ p)
    {x : W ⟶ X₂} [IsFinite x] {b : X₂ ⟶ U} {e : V ⟶ U} (hxb : x ≫ b = q ≫ e) {u : U} {v : V}
    {t : T} (hv : ∀ y, e.base y = u → y = v) (hvt : p.base v = t) {ζ : W}
    (hζ : closure {r.base ζ} ∩ Set.range (toT.fiberι t) = ∅) :
    closure {x.base ζ} ∩ Set.range (b.fiberι u) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun y hy ↦ ?_
  obtain ⟨z, hzclose, hzy⟩ : y ∈ x.base '' closure ({ζ} : Set W) := by
    rw [← x.isClosedMap.closure_image_eq_of_continuous x.continuous, Set.image_singleton]
    exact hy.1
  have hby : b.base y = u := by
    rw [b.range_fiberι] at hy
    exact hy.2
  have hqz : q.base z = v := by
    refine hv (q.base z) ?_
    have hm := base_comp_apply_eq_of_comp_eq hxb z
    rw [hzy, hby] at hm
    exact hm.symm
  have hrz := base_comp_apply_eq_of_comp_eq hrq z
  refine Set.eq_empty_iff_forall_notMem.mp hζ (r.base z) ⟨?_, ?_⟩
  · exact specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr hzclose).map r.continuous)
  · rw [toT.range_fiberι]
    exact Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr (hrz.trans (by rw [hqz, hvt])))

/-- Let `D` be an impurity and `V` a scheme, locally quasi-finite over the test family `T` of
`D` and finite over a scheme `U` over the base, compatibly. If `v` is the only point of `V` over
`u ∈ U`, lies over the distinguished point of `D`, and `v'` lies over the point `t'` of `D`,
then the base change along `U` has an impure point above `e v'`. -/
private theorem ImpurityData.exists_mem_relativeAssassin_pullback_of_isFinite {f : X ⟶ S}
    [LocallyOfFiniteType f] {F : X.Modules} [F.IsQuasicoherent] {s : S}
    (D : ImpurityData f s) (hD : D.IsImpurity F) {U V : Scheme.{u}} (g : U ⟶ S) (p : V ⟶ D.T)
    (e : V ⟶ U) [LocallyOfFiniteType p] [LocallyQuasiFinite p] [IsFinite e]
    (h : p ≫ D.g = e ≫ g) {u : U} {v v' : V} (hv : ∀ y, e.base y = u → y = v)
    (hvt : p.base v = D.t) (hv't : p.base v' = D.t') :
    ∃ ξ : (pullback f g : Scheme.{u}), ξ ∈ Stacks.Divisors.relativeAssassin (pullback.snd f g)
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F) ∧
      (pullback.snd f g).base ξ = e.base v' ∧
      closure {ξ} ∩ Set.range ((pullback.snd f g).fiberι u) = ∅ := by
  have hLFT : LocallyOfFiniteType D.toT :=
    MorphismProperty.of_isPullback D.isPullback inferInstance
  let W := pullback D.toT p
  let r : W ⟶ D.X_T := pullback.fst D.toT p
  let q : W ⟶ V := pullback.snd D.toT p
  obtain ⟨ζ, hζr, hζq⟩ : ∃ ζ : W, r.base ζ = D.xi ∧ q.base ζ = v' :=
    Scheme.Pullback.exists_preimage_pullback D.xi v' (by rw [D.xi_liesOver, hv't])
  have hζass : ζ ∈ Stacks.Divisors.relativeAssassin q
      ((Scheme.Modules.pullback r).obj (D.pulledBack F)) := by
    refine preimage_relativeAssassin_eq_pullback_of_locallyQuasiFinite D.toT p
      (D.pulledBack F) ▸ ?_
    change r.base ζ ∈ Stacks.Divisors.relativeAssassin D.toT (D.pulledBack F)
    rw [hζr]
    exact hD.1
  let x : W ⟶ pullback f g := pullback.lift (r ≫ D.toX) (q ≫ e)
    (by simp only [r, q, Category.assoc, D.isPullback.w, pullback.condition_assoc, h])
  have hxfst : x ≫ pullback.fst f g = r ≫ D.toX := pullback.lift_fst _ _ _
  have hxsnd : x ≫ pullback.snd f g = q ≫ e := pullback.lift_snd _ _ _
  have hsq : IsPullback x q (pullback.snd f g) e := by
    have houter : IsPullback (r ≫ D.toX) q f (p ≫ D.g) :=
      (IsPullback.of_hasPullback D.toT p).paste_horiz D.isPullback
    rw [h, ← hxfst] at houter
    exact IsPullback.of_right houter hxsnd (IsPullback.of_hasPullback f g)
  have : IsFinite x := MorphismProperty.of_isPullback hsq.flip inferInstance
  refine ⟨x.base ζ, mem_relativeAssassin_of_isPullback hsq _ ?_, ?_,
    closure_inter_range_fiberι_eq_empty_of_isFinite (pullback.condition (f := D.toT) (g := p))
      hxsnd hv hvt (by rw [hζr]; exact hD.2)⟩
  · exact ((relativeAssassin_pullback_pullback_eq hxfst q F).trans
      (relativeAssassin_pullback_pullback_eq rfl q F).symm) ▸ hζass
  · simpa only [hζq] using base_comp_apply_eq_of_comp_eq hxsnd ζ

/-- An impurity which, after restriction of its test family to an open subset containing the
distinguished point, admits a finite neighbourhood of that point over an elementary étale
neighbourhood of the base point, occurs over that elementary étale neighbourhood. -/
private theorem exists_impurityData_of_finiteNeighborhoodAt {f : X ⟶ S}
    [LocallyOfFiniteType f] {F : X.Modules} [F.IsQuasicoherent] {s : S}
    (D : ImpurityData f s) (hD : D.IsImpurity F) (Q : D.T.Opens) (htQ : D.t ∈ Q)
    (N : Stacks.Flatness.FiniteNeighborhoodAt (Q.ι ≫ D.g) (⟨D.t, htQ⟩ : Q.toScheme)) :
    ∃ (D' : ImpurityData f s) (hD' : Etale D'.g), D'.IsImpurity F ∧
      EtaleNeighborhood.IsElementary
        ({ scheme := D'.T
           point := D'.t
           toBase := D'.g
           etale_toBase := hD'
           map_point := D'.mapsToChosenPoint } : EtaleNeighborhood S s) := by
  let gQ : Q.toScheme ⟶ S := Q.ι ≫ D.g
  have hgQ : gQ.base ⟨D.t, htQ⟩ = s := D.mapsToChosenPoint
  let U : EtaleNeighborhood S s :=
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
  let pVT : V.toScheme ⟶ D.T := V.ι ≫ pullback.fst gQ U.toBase ≫ Q.ι
  let pVU : V.toScheme ⟶ U.scheme := V.ι ≫ pullback.snd gQ U.toBase
  have : IsFinite pVU := hVfinite
  have hvt : pVT.base v = D.t := by
    change Q.ι.base ((V.ι ≫ pullback.fst gQ U.toBase).base v) = D.t
    rw [(hvspec v hv).1]
    rfl
  have hpVTU : pVT ≫ D.g = pVU ≫ U.toBase := by
    change V.ι ≫ (pullback.fst gQ U.toBase ≫ Q.ι) ≫ D.g =
      (V.ι ≫ pullback.snd gQ U.toBase) ≫ U.toBase
    rw [Category.assoc, Category.assoc]
    exact V.ι ≫= pullback.condition (f := gQ) (g := U.toBase)
  obtain ⟨v', hv'spec, hv't⟩ :=
    liftsGeneralizations_of_isOpenMap pVT pVT.isOpenMap hvt D.specializes
  have huu' : pVU.base v' ⤳ U.point := by
    have := hv'spec.map pVU.continuous
    rwa [show pVU.base v = U.point from hv] at this
  obtain ⟨ξ, hξ, hξv', hdis⟩ := D.exists_mem_relativeAssassin_pullback_of_isFinite hD U.toBase
    pVT pVU hpVTU (u := U.point) hvuniq hvt hv't
  exact ⟨{ T := U.scheme
           g := U.toBase
           t' := pVU.base v'
           t := U.point
           specializes := huu'
           mapsToChosenPoint := U.map_point
           X_T := pullback f U.toBase
           toX := pullback.fst f U.toBase
           toT := pullback.snd f U.toBase
           isPullback := IsPullback.of_hasPullback f U.toBase
           xi := ξ
           xi_liesOver := hξv' }, inferInstance, ⟨hξ, hdis⟩, hUelem⟩

/-- If a morphism which is only locally of finite type admits an impurity whose test family is
quasi-finite over the base at the distinguished point, then it admits one whose test family,
pointed at the distinguished point, is an elementary étale neighbourhood of the chosen point of
the base.

This is the argument of [Stacks, Tag 05J0] run without a quasi-compactness hypothesis on the
morphism, which [Stacks, Tag 05J5] observes that it never uses. -/
theorem exists_impurityData_elementaryEtaleNeighborhood_of_quasiFiniteAt {f : X ⟶ S}
    [LocallyOfFiniteType f] {F : X.Modules} [F.IsQuasicoherent] {s : S}
    (h : ∃ D : ImpurityData f s, D.IsImpurity F ∧ quasiFiniteAt D.g D.t) :
    ∃ (D : ImpurityData f s) (hD : Etale D.g), D.IsImpurity F ∧
      EtaleNeighborhood.IsElementary
        ({ scheme := D.T
           point := D.t
           toBase := D.g
           etale_toBase := hD
           map_point := D.mapsToChosenPoint } : EtaleNeighborhood S s) := by
  obtain ⟨D, hD, hqf⟩ := h
  have htQ : D.t ∈ quasiFiniteLocus D.g := (mem_quasiFiniteLocus_iff D.g D.t).2 hqf
  have hiso : IsIsolatedPoint (((quasiFiniteLocus D.g).ι ≫ D.g).asFiber
      (⟨D.t, htQ⟩ : (quasiFiniteLocus D.g).toScheme)) :=
    ((quasiFiniteAt_tfae ((quasiFiniteLocus D.g).ι ≫ D.g)
        (⟨D.t, htQ⟩ : (quasiFiniteLocus D.g).toScheme)).out 1 2).mp
      ((forall_quasiFiniteAt_iff ((quasiFiniteLocus D.g).ι ≫ D.g)).2
        ⟨inferInstance, inferInstance⟩ _)
  exact exists_impurityData_of_finiteNeighborhoodAt D hD (quasiFiniteLocus D.g) htQ
    (Stacks.Flatness.finiteNeighborhoodAt ((quasiFiniteLocus D.g).ι ≫ D.g) _ hiso)

/-- **Stacks Project, Tag 05J3, parts (2) and (3).** A pre-pure situation admits an impurity
whose test family, pointed at the distinguished point, is an elementary étale neighbourhood of
the chosen point of the base if and only if it admits one whose test family is quasi-finite over
the base at the distinguished point. -/
@[stacks 05J3 "parts (2) and (3)"]
theorem exists_isImpurity_elementaryEtaleNeighborhood_iff_quasiFiniteAt
    (P : PrePureSituation.{u}) :
    (∃ (D : ImpurityDiagram P) (hD : Etale D.g), IsImpurity P D ∧
      EtaleNeighborhood.IsElementary
        ({ scheme := D.T
           point := D.t
           toBase := D.g
           etale_toBase := hD
           map_point := D.mapsToChosenPoint } : EtaleNeighborhood P.S P.s)) ↔
    (∃ D : ImpurityDiagram P, IsImpurity P D ∧ quasiFiniteAt D.g D.t) := by
  refine ⟨?_, exists_isImpurity_elementaryEtaleNeighborhood_of_quasiFiniteAt P⟩
  rintro ⟨D, hD, hImp, -⟩
  have : Etale D.g := hD
  exact ⟨D, hImp, (forall_quasiFiniteAt_iff D.g).2 ⟨inferInstance, inferInstance⟩ D.t⟩

/-! ### The equivalence of conditions (1) and (2) of Tag 05J5 -/

/-- Condition (1) implies condition (2): a quasi-finite impurity can be replaced by one over an
elementary étale neighbourhood, by the argument of Tag 05J0, which never uses
quasi-compactness. -/
theorem noQuasiFiniteImpurity_of_noElementaryEtaleImpurity {f : X ⟶ S} [LocallyOfFiniteType f]
    {F : X.Modules} [F.IsQuasicoherent] {s : S} (h : NoElementaryEtaleImpurity f F s) :
    NoQuasiFiniteImpurity f F s := by
  intro D hqf hD
  obtain ⟨D', het, hD'imp, helem⟩ :=
    exists_impurityData_elementaryEtaleNeighborhood_of_quasiFiniteAt ⟨D, hD, hqf⟩
  exact h D' het helem hD'imp

/-- **Stacks Project, Tag 05J5.** For a morphism which is only locally of finite type,
conditions (1) and (2) are still equivalent: an impurity above `s` whose test family is merely
quasi-finite at its distinguished point can be replaced by one whose test family is an
elementary étale neighbourhood of `s`.

This is the half of the remark which asserts that the proof of Tag 05J0 does not use
quasi-compactness of the morphism: that proof is run here for impurity data, which carry no
such hypothesis. -/
@[stacks 05J5 "conditions (1) and (2) are equivalent"]
theorem noElementaryEtaleImpurity_iff_noQuasiFiniteImpurity {f : X ⟶ S} [LocallyOfFiniteType f]
    {F : X.Modules} [F.IsQuasicoherent] {s : S} :
    NoElementaryEtaleImpurity f F s ↔ NoQuasiFiniteImpurity f F s :=
  ⟨noQuasiFiniteImpurity_of_noElementaryEtaleImpurity,
    noElementaryEtaleImpurity_of_noQuasiFiniteImpurity⟩

end AlgebraicGeometry

end
