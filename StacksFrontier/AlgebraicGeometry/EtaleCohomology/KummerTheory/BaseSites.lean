module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Etale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.FppfAndSyntomic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Sequence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenCoarserSites
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Kummer sequence on the localized big sites of a chosen big fppf site

A chosen big fppf site carries five topologies on one and the same category of schemes, and
hence five localized topologies `AlgebraicGeometry.BigFppfOver.baseOverTopology` on the big
fppf category over a contained base scheme `S`.  The multiplicative presheaf is a sheaf for
all five, and the Kummer complex `0 ⟶ μ_n ⟶ 𝐆_m ⟶ 𝐆_m ⟶ 0` of abelian sheaves is short exact
for the fppf and the syntomic one when `n` is positive, and for the étale one when `n` is
invertible on `S`.

## Main results

* `AlgebraicGeometry.unitsPresheaf_isSheaf_base` — the units of global functions form a sheaf
  for each of the five localized topologies.
* `AlgebraicGeometry.kummerSequence_shortExact_base_fppf`,
  `AlgebraicGeometry.kummerSequence_shortExact_base_syntomic` — the Kummer sequence is short
  exact on the localized big fppf and big syntomic topologies, for `n` positive.
* `AlgebraicGeometry.kummerSequence_shortExact_base_etale` — the Kummer sequence is short exact
  on the localized big étale topology, for `n` invertible on the base.

## Implementation notes

The sheaf condition is inherited: each of the five localized topologies is coarser than the
localized fppf one by `AlgebraicGeometry.BigFppfOver.baseOverTopology_le_fppf`, so
`AlgebraicGeometry.unitsPresheaf_isSheaf_fppf` restricts along it.  The fppf member of the
indexed family of localized topologies *is* `AlgebraicGeometry.BigFppfOver.topology`, so the
fppf case of short exactness is `AlgebraicGeometry.kummerSequence_shortExact_fppf` verbatim.

For the two coarser cases the work is local surjectivity of the `n`-th power map, which
`AlgebraicGeometry.kummerSequence_shortExact_of_isLocallySurjective` then turns into short
exactness.  A unit on an object `U` of the site acquires an `n`-th root on a one-member
covering of the scheme underlying `U` — syntomic by adjoining a root of `X ^ n - a`, étale by
the same polynomial when `n` is invertible — and that covering, whose source need not satisfy
the site's size cutoff, is refined by a covering family internal to the size-bounded category
of schemes.  Those refinements are the ones already available for the bundled big syntomic and
big étale sites carried by the fppf site: these have its own cutoff and covering bound, so their
covering families are recognised as the chosen syntomic and étale families of Stacks 03FF with
no transport.

The étale argument has a degenerate case the syntomic one does not: surjectivity of the root
cover needs the global functions of the object to be nontrivial.  When they are not, the unit is
the only element of its own unit group and the identity covering already carries a root.

## References

* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL)
* [Stacks Project, Tag 040N](https://stacks.math.columbia.edu/tag/040N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- **The units presheaf is a sheaf for each of the five localized big topologies.** Every one
of them is coarser than the localized fppf topology, so the fppf sheaf condition restricts along
it. -/
public theorem unitsPresheaf_isSheaf_base (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (τ : SiteKind) :
    Presheaf.IsSheaf (BigFppfOver.baseOverTopology B S hS τ)
      (unitsPresheaf (BigFppfOver.toScheme B S hS)) :=
  (unitsPresheaf_isSheaf_fppf B S hS).of_le
    (BigFppfOver.baseOverTopology_le_fppf B S hS τ)

/-- An `n`-th root of a unit on a scheme over `X` is inherited by any scheme factoring
through it: pull the root back along the factoring morphism. -/
private theorem exists_root_of_factorisation {X Y P : Scheme.{u}} (n : ℕ)
    (q : P ⟶ X) (a : (Γ(X, ⊤))ˣ) (b : (Γ(P, ⊤))ˣ)
    (hb : b ^ n = Units.map q.appTop.hom a)
    (g : Y ⟶ X) (c : Y ⟶ P) (hc : c ≫ q = g) :
    ∃ d : (Γ(Y, ⊤))ˣ, d ^ n = Units.map g.appTop.hom a := by
  refine ⟨Units.map c.appTop.hom.toMonoidHom b, ?_⟩
  apply Units.ext
  have hring : g.appTop.hom = (c.appTop.hom).comp q.appTop.hom := by
    have h1 : q.appTop ≫ c.appTop = g.appTop := by
      simpa only [Scheme.Hom.comp_appTop] using congrArg (fun k : Y ⟶ X => k.appTop) hc
    simpa only [CommRingCat.hom_comp] using
      congrArg (fun k : Γ(X, ⊤) ⟶ Γ(Y, ⊤) => k.hom) h1.symm
  have hbval : b.val ^ n = q.appTop.hom a.val := congrArg Units.val hb
  change (c.appTop.hom b.val) ^ n = g.appTop.hom a.val
  rw [← map_pow, hbval, hring, RingHom.comp_apply]

/-- **A covering family of the base topology whose members carry `n`-th roots of a unit makes
the image sieve of that unit covering.** The family lives on the scheme underlying an object `U`
of the big fppf category over `S`; the sieve it generates upstairs is its preimage under the
localization equivalence of sieves, and each of its arrows carries a preimage of the unit under
the `n`-th power map. -/
private theorem imageSieve_mem_of_rootFamily (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (τ : SiteKind) (n : ℕ) {U : BigFppfOver B S hS}
    (a : (Γ(B.inclusion.obj U.left, ⊤))ˣ)
    (V : PreZeroHypercover.{u + 1} U.left)
    (hV : Sieve.generate V.presieve₀ ∈ B.baseTopology τ U.left)
    (hb : ∀ i, ∃ b : (Γ(B.inclusion.obj (V.X i), ⊤))ˣ,
      b ^ n = Units.map (B.inclusion.map (V.f i)).appTop.hom a) :
    Presheaf.imageSieve (powerPresheaf (BigFppfOver.toScheme B S hS) n) a
      ∈ BigFppfOver.baseOverTopology B S hS τ U := by
  let J := BigFppfOver.baseOverTopology B S hS τ
  have hcover : (Sieve.overEquiv U).symm (Sieve.generate V.presieve₀) ∈ J U := by
    rw [GrothendieckTopology.mem_over_iff]
    simpa using hV
  refine J.superset_covering ?_ hcover
  rw [← (Sieve.overEquiv U).symm.apply_symm_apply
    (Presheaf.imageSieve (powerPresheaf (BigFppfOver.toScheme B S hS) n) a),
    (Sieve.overEquiv U).symm.map_rel_iff]
  simp only [OrderIso.symm_symm]
  rw [PreZeroHypercover.presieve₀, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  obtain ⟨b, hbi⟩ := hb i
  rw [Sieve.overEquiv_iff]
  exact ⟨b, hbi⟩

/-- A unit that acquires roots on a one-member covering `q` of the scheme underlying `U`, refined
by a covering family `V` of the site, has a covering image sieve for the base topology. -/
private theorem imageSieve_mem_of_refined_root_cover (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (τ : SiteKind) (n : ℕ) {U : BigFppfOver B S hS}
    (a : (Γ(B.inclusion.obj U.left, ⊤))ˣ) {P : Scheme.{u}} (q : P ⟶ B.inclusion.obj U.left)
    (b : (Γ(P, ⊤))ˣ) (hb : b ^ n = Units.map q.appTop.hom a)
    (V : PreZeroHypercover.{u + 1} U.left)
    (hV : Sieve.generate V.presieve₀ ∈ B.baseTopology τ U.left)
    (ref : (V.map B.inclusion).Hom (PreZeroHypercover.singleton.{u + 1} q)) :
    Presheaf.imageSieve (powerPresheaf (BigFppfOver.toScheme B S hS) n) a
      ∈ BigFppfOver.baseOverTopology B S hS τ U :=
  imageSieve_mem_of_rootFamily B S hS τ n a V hV
    fun i => exists_root_of_factorisation n q a b hb _ (ref.h₀ i) (ref.w₀ i)

/-- **The `n`-th power map on the units presheaf is locally surjective for the localized big
syntomic topology**, for `n` positive. A unit acquires an `n`-th root on a one-member syntomic
covering, which is refined by a chosen syntomic covering family of the size-bounded category. -/
public theorem syntomic_power_isLocallySurjective_base (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (n : ℕ) (hn : 0 < n) :
    Presheaf.IsLocallySurjective (BigFppfOver.baseOverTopology B S hS .syntomic)
      (powerPresheaf (BigFppfOver.toScheme B S hS) n) := by
  refine ⟨?_⟩
  intro U s
  let a : (Γ(B.inclusion.obj U.left, ⊤))ˣ := s
  obtain ⟨P, q, hq, b, hb⟩ :=
    exists_syntomic_cover_with_root n hn (X := B.inclusion.obj U.left) a
  let E : PreZeroHypercover.{u + 1} (B.inclusion.obj U.left) :=
    PreZeroHypercover.singleton.{u + 1} q
  have hE : IsSyntomicCovering E.X E.f := by
    refine ⟨fun _ => hq.1 (), Set.eq_univ_of_forall fun x => ?_⟩
    obtain ⟨_, y, hy⟩ := Set.mem_iUnion.mp ((Set.eq_univ_iff_forall.mp hq.2) x)
    exact Set.mem_iUnion.mpr ⟨PUnit.unit, Set.mem_range.mpr ⟨y, hy⟩⟩
  obtain ⟨V, hV, ⟨ref⟩⟩ := exists_siteCovering_refining B.toBigSyntomicSite U.left E hE
  exact imageSieve_mem_of_refined_root_cover B S hS .syntomic n a q b hb V
    (Precoverage.generate_mem_toGrothendieck
      ⟨V, rfl, (B.toBigSyntomicSite_isCovering_iff ⟨U.left, V⟩).mp hV⟩) ref

/-- **A unit on a scheme with nontrivial global functions acquires an `n`-th root on a
surjective étale cover**, when `n` is invertible there. This is the étale counterpart of
`AlgebraicGeometry.exists_syntomic_cover_with_root`: the étale root cover of the affine scheme of
global functions, `Stacks.Kummer.exists_etale_surjective_pow`, pulled back along
`AlgebraicGeometry.Scheme.toSpecΓ`. -/
private theorem exists_etale_root_cover {T : Scheme.{u}}
    (a : (Γ(T, ⊤))ˣ) (n : ℕ) (hn : IsUnit (n : Γ(T, ⊤)))
    (hT : Nontrivial (Γ(T, ⊤))) :
    ∃ (P : Scheme.{u}) (q : P ⟶ T), Etale q ∧ Surjective q ∧
      ∃ b : (Γ(P, ⊤))ˣ, b ^ n = Units.map q.appTop.hom a := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn.ne_zero (by simp)
  let R : CommRingCat.{u} := Γ(T, ⊤)
  let y : (Γ(Spec R, ⊤))ˣ := Units.map (Scheme.ΓSpecIso R).inv.hom.toMonoidHom a
  obtain ⟨S, ϕ, hϕ, hsurj, w, hw⟩ := Stacks.Kummer.exists_etale_surjective_pow R hn0 hn y
  let f := Spec.map ϕ
  let g := T.toSpecΓ
  have : Etale f := hϕ
  have : Surjective f := ⟨hsurj⟩
  obtain ⟨d, hd⟩ := exists_root_of_factorisation n f y w hw (pullback.fst f g ≫ f)
    (pullback.fst f g) rfl
  refine ⟨pullback f g, pullback.snd f g, inferInstance, inferInstance, d, ?_⟩
  rw [hd, pullback.condition]
  apply Units.ext
  change (pullback.snd f g).appTop.hom (g.appTop.hom ((Scheme.ΓSpecIso R).inv.hom a.val)) = _
  rw [Scheme.toSpecΓ_appTop]
  change (pullback.snd f g).appTop.hom (((Scheme.ΓSpecIso R).inv ≫ (Scheme.ΓSpecIso R).hom).hom
    a.val) = _
  rw [Iso.inv_hom_id]
  rfl

/-- **The `n`-th power map on the units presheaf is locally surjective for the localized big
étale topology**, when `n` is invertible on the base. The root cover of
`AlgebraicGeometry.exists_etale_root_cover` is refined by a chosen étale covering family of the
size-bounded category; when the global functions of the object are trivial the unit is `1` and
the identity covering already carries a root. -/
@[sga "4½ Arcata 2.2.5" "more general"]
public theorem etale_power_isLocallySurjective_base (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (n : ℕ) (hn : IsUnit (n : Scheme.Γ.obj (Opposite.op S))) :
    Presheaf.IsLocallySurjective (BigFppfOver.baseOverTopology B S hS .etale)
      (powerPresheaf (BigFppfOver.toScheme B S hS) n) := by
  classical
  refine ⟨?_⟩
  intro U s
  let a : (Γ(B.inclusion.obj U.left, ⊤))ˣ := s
  by_cases hR : Nontrivial (Γ(B.inclusion.obj U.left, ⊤))
  · have hnT : IsUnit (n : Γ(B.inclusion.obj U.left, ⊤)) := by
      rw [← map_natCast (B.inclusion.map U.hom).appTop.hom n]
      exact hn.map _
    obtain ⟨P, q, hqet, hqsurj, b, hb⟩ := exists_etale_root_cover a n hnT hR
    let E : PreZeroHypercover.{u + 1} (B.inclusion.obj U.left) :=
      PreZeroHypercover.singleton.{u + 1} q
    have hE : E.presieve₀ ∈ Scheme.etalePrecoverage (B.inclusion.obj U.left) :=
      (Scheme.presieve₀_mem_precoverage_iff E).2
        ⟨fun x => ⟨PUnit.unit, hqsurj.surj x⟩, fun _ => hqet⟩
    obtain ⟨V, hV, ⟨ref⟩⟩ :=
      BigEtaleSite.exists_covering_refining_etale_cover B.toBigEtaleSite (T := U.left) E hE
    exact imageSieve_mem_of_refined_root_cover B S hS .etale n a q b hb V
      (Precoverage.generate_mem_toGrothendieck
        ⟨V, rfl, (B.toBigEtaleSite_isCovering_iff ⟨U.left, V⟩).mp hV⟩) ref
  · have hsub : Subsingleton (Γ(B.inclusion.obj U.left, ⊤)) :=
      not_nontrivial_iff_subsingleton.mp hR
    let V : PreZeroHypercover.{u + 1} U.left := PreZeroHypercover.singleton.{u + 1} (𝟙 U.left)
    have htop : Sieve.generate V.presieve₀ = ⊤ := by
      rw [PreZeroHypercover.presieve₀_singleton]
      ext Y g
      simp only [Sieve.top_apply, iff_true]
      exact ⟨U.left, g, 𝟙 U.left, Presieve.singleton_self _, by simp⟩
    refine imageSieve_mem_of_rootFamily B S hS .etale n a V
      (htop ▸ (B.baseTopology .etale).top_mem _) ?_
    intro i
    have : Subsingleton (Γ(B.inclusion.obj (V.X i), ⊤)) := hsub
    exact ⟨1, Units.ext (Subsingleton.elim _ _)⟩

/-- **The Kummer sequence is short exact on the localized big fppf topology** of a chosen big
fppf site, for `n` positive. The fppf member of the indexed family of localized topologies is
the localized fppf topology, so this is `AlgebraicGeometry.kummerSequence_shortExact_fppf`. -/
@[sga "7 IX 14.3" "special case", sga "7 IX 9.4.3"]
public theorem kummerSequence_shortExact_base_fppf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (n : ℕ) (hn : 0 < n) :
    (kummerSequence (BigFppfOver.baseOverTopology B S hS .fppf)
      (BigFppfOver.toScheme B S hS)
      (unitsPresheaf_isSheaf_base B S hS .fppf) n).ShortExact :=
  kummerSequence_shortExact_fppf B S hS n hn

/-- **The Kummer sequence is short exact on the localized big syntomic topology** of a chosen
big fppf site, for `n` positive. -/
@[sga "7 IX 14.3" "special case"]
public theorem kummerSequence_shortExact_base_syntomic (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (n : ℕ) (hn : 0 < n) :
    (kummerSequence (BigFppfOver.baseOverTopology B S hS .syntomic)
      (BigFppfOver.toScheme B S hS)
      (unitsPresheaf_isSheaf_base B S hS .syntomic) n).ShortExact :=
  kummerSequence_shortExact_of_isLocallySurjective _ (BigFppfOver.toScheme B S hS)
    (unitsPresheaf_isSheaf_base B S hS .syntomic) n
    (syntomic_power_isLocallySurjective_base B S hS n hn)

/-- **The Kummer sequence is short exact on the localized big étale topology** of a chosen big
fppf site, when `n` is invertible on the base. -/
@[sga "4½ Arcata 2.2.5" "more general",
  sga "4½ Sommes_trig 4.7" "special case",
  sga "7 IX 14.3" "special case"]
public theorem kummerSequence_shortExact_base_etale (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (n : ℕ) (hn : IsUnit (n : Scheme.Γ.obj (Opposite.op S))) :
    (kummerSequence (BigFppfOver.baseOverTopology B S hS .etale)
      (BigFppfOver.toScheme B S hS)
      (unitsPresheaf_isSheaf_base B S hS .etale) n).ShortExact :=
  kummerSequence_shortExact_of_isLocallySurjective _ (BigFppfOver.toScheme B S hS)
    (unitsPresheaf_isSheaf_base B S hS .etale) n
    (etale_power_isLocallySurjective_base B S hS n hn)

/-- **The `n`-th power map on the units presheaf is locally surjective for the localized big
fppf topology**, for `n` positive.  A syntomic covering is an fppf covering, so this is the
syntomic statement read on the finer topology. -/
public theorem fppf_power_isLocallySurjective_base (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (n : ℕ) (hn : 0 < n) :
    Presheaf.IsLocallySurjective (BigFppfOver.baseOverTopology B S hS .fppf)
      (powerPresheaf (BigFppfOver.toScheme B S hS) n) :=
  Presheaf.isLocallySurjective_of_le
    (BigFppfOver.baseOverTopology_le_fppf B S hS .syntomic)
    (powerPresheaf (BigFppfOver.toScheme B S hS) n)
    (syntomic_power_isLocallySurjective_base B S hS n hn)

end AlgebraicGeometry

end
