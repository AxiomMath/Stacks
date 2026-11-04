module

public import StacksFrontier.AlgebraicGeometry.Morphisms.StandardForm.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.SyntomicScheme
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.StandardRefinement
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksCore.Tactic.StacksAttribute

/-!
# Descent along morphisms in standard form

For the étale, smooth and syntomic topologies, a property of morphisms of schemes which is
Zariski local on the target and stable under base change along morphisms of the relevant class
is local on the target for that topology as soon as it descends along *surjective standard*
morphisms of affine schemes — standard étale, standard smooth, or standard syntomic
respectively. Descent only has to be checked along the morphisms in standard form, which are
the ones explicitly presented by equations.

## Main results

* `AlgebraicGeometry.isLocalAtTarget_of_standardRefinement` is the criterion the three cases
  share, stated for an arbitrary topology and an arbitrary class of descent morphisms.
* `AlgebraicGeometry.isLocalAtTarget_etale_of_standard_descent` gives the étale case.
* `AlgebraicGeometry.isLocalAtTarget_smooth_of_standard_descent` gives the smooth case.
* `AlgebraicGeometry.isLocalAtTarget_syntomic_of_standard_descent` gives the syntomic case.

## Implementation notes

The three statements share one criterion, `isLocalAtTarget_of_standardRefinement`, which is
stated for an arbitrary morphism property `Q` cutting out the topology and an arbitrary class
`R` of morphisms of affine schemes playing the role of the morphisms in standard form. Beyond
Zariski locality and stability under base change along `Q`, it asks that open immersions belong
to `Q`, that `R` be stable under base change between affine schemes and consist of open maps,
and that every `Q`-covering of an affine scheme be refined, through open immersions, by a
covering by affine schemes whose structure morphisms lie in `R`. Such a refinement is Tag 0222
for the smooth topology and Tag 0228 for the syntomic one; for the étale topology it is
`exists_affine_standardEtale_refinement` below, which is Tag 02GT applied around each point.

A disjoint union of morphisms in standard form is not in standard form, so unlike the general
affine descent criterion for these topologies the proof cannot replace the refinement by a
single morphism from a coproduct. Instead `descent_of_standardCover` keeps the refinement as a
family: the open images of its members form a Zariski covering of the affine target, each
member becomes *surjective* after base change to an affine open contained in the image of the
corresponding refining morphism, and Zariski locality on the target reassembles the pieces. The
base changes of a fixed morphism along two morphisms with the same composite to the base are
identified by `pullback_snd_parallel_iff`, which is what lets the surjective base change of the
refining morphism be used in place of the refining morphism itself.

## References

* [Stacks Project, Tag 034G](https://stacks.math.columbia.edu/tag/034G)
* [Stacks Project, Tag 0222](https://stacks.math.columbia.edu/tag/0222)
* [Stacks Project, Tag 0228](https://stacks.math.columbia.edu/tag/0228)
* [Stacks Project, Tag 02GT](https://stacks.math.columbia.edu/tag/02GT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

variable (P : MorphismProperty Scheme.{u})

/-- Base changing `f` along `u` and then along `h` is base changing it along `h ≫ u`. -/
private theorem pullback_snd_comp_iff [P.RespectsIso]
    {X S U W : Scheme.{u}} (f : X ⟶ S) (u : U ⟶ S) (h : W ⟶ U) :
    P (pullback.snd (pullback.snd f u) h) ↔ P (pullback.snd f (h ≫ u)) := by
  simpa using P.cancel_left_of_respectsIso (pullbackLeftPullbackSndIso f u h).hom
    (pullback.snd f (h ≫ u))

/-- `P` is preserved by base change of `f` along a `Q`-morphism, when `P` is stable under base
change against `Q`. -/
private theorem pullback_snd_of_isStableUnderBaseChangeAgainst {Q : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChangeAgainst Q] {X S Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (hg : Q g) (hf : P f) : P (pullback.snd f g) :=
  (MorphismProperty.IsStableUnderBaseChangeAgainst.isStableUnderBaseChangeAlong
    g hg).of_isPullback (IsPullback.of_hasPullback f g) hf

/-- Refining the morphism one base changes along by a `Q`-morphism preserves `P`. -/
private theorem pullback_snd_refine {Q : MorphismProperty Scheme.{u}}
    [P.RespectsIso] [P.IsStableUnderBaseChangeAgainst Q]
    {X S S' Y : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (e : Y ⟶ S')
    (he : Q e) (hp : P (pullback.snd f g)) :
    P (pullback.snd f (e ≫ g)) :=
  (pullback_snd_comp_iff (P := P) f g e).mp
    (pullback_snd_of_isStableUnderBaseChangeAgainst P _ e he hp)

/-- Two iterated base changes of `f` along morphisms with the same composite to the base agree
on `P`. -/
private theorem pullback_snd_parallel_iff [P.RespectsIso]
    {X S U W A : Scheme.{u}} (f : X ⟶ S) (u : U ⟶ S) (w : W ⟶ S)
    (h : A ⟶ U) (q : A ⟶ W) (heq : h ≫ u = q ≫ w) :
    P (pullback.snd (pullback.snd f u) h) ↔ P (pullback.snd (pullback.snd f w) q) := by
  calc
    _ ↔ P (pullback.snd f (h ≫ u)) := pullback_snd_comp_iff P f u h
    _ = P (pullback.snd f (q ≫ w)) := by rw [heq]
    _ ↔ _ := (pullback_snd_comp_iff P f w q).symm

/-- Descent along a covering of an affine scheme by affine schemes whose structure morphisms are
in the class `R` reduces to descent along *surjective* `R`-morphisms: the open image of each
member of the covering is covered by affine opens over which the member becomes surjective after
base change. -/
private theorem descent_of_standardCover
    {Q R : MorphismProperty Scheme.{u}}
    [Q.IsStableUnderBaseChange]
    [P.IsStableUnderBaseChangeAgainst Q]
    [P.IsLocalAtTarget Scheme.zariskiPrecoverage]
    (hdesc : ∀ {S S' X : Scheme.{u}} [IsAffine S] [IsAffine S']
      (g : S' ⟶ S) [Surjective g] (_ : R g) (f : X ⟶ S),
        P (pullback.snd f g) → P f)
    (hopenQ : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y), IsOpenImmersion g → Q g)
    (hRbase : ∀ {U S W : Scheme.{u}} [IsAffine U] [IsAffine S] [IsAffine W]
      (g : U ⟶ S) (w : W ⟶ S), R g → R (pullback.fst w g))
    (hRopen : ∀ {U S : Scheme.{u}} [IsAffine U] [IsAffine S]
      (g : U ⟶ S), R g → IsOpenMap g)
    {S X : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    (V : S.Cover.{v} (Scheme.precoverage Q))
    (hAffine : ∀ j, IsAffine (V.X j))
    (hR : ∀ j, R (V.f j))
    (hdata : ∀ j, P (pullback.snd f (V.f j))) : P f := by
  let U (j : V.I₀) : S.Opens := by
    have : IsAffine (V.X j) := hAffine j
    exact ⟨Set.range (V.f j).base, (hRopen (V.f j) (hR j)).isOpen_range⟩
  let O : S.Cover.{v} Scheme.zariskiPrecoverage :=
    Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) V.I₀
      (fun j => (U j).toScheme) (fun j => (U j).ι)
      (fun s => by
        obtain ⟨y, hy⟩ := V.covers s
        exact ⟨V.idx s, ⟨s, ⟨y, hy⟩⟩, rfl⟩)
  have hO (j : O.I₀) : P (pullback.snd f (O.f j)) := by
    have : IsAffine (V.X j) := hAffine j
    let B := (O.X j).affineCover
    have hB (i : B.I₀) : P (pullback.snd (pullback.snd f (O.f j)) (B.f i)) := by
      let w := B.f i ≫ O.f j
      let q := pullback.fst w (V.f j)
      let q' := pullback.snd w (V.f j)
      have : IsOpenImmersion (O.f j) := O.map_prop j
      have : IsOpenImmersion (B.f i) := B.map_prop i
      have hQ : Q q' :=
        Q.of_isPullback (IsPullback.of_hasPullback w (V.f j)) (hopenQ w inferInstance)
      have hpull : P (pullback.snd (pullback.snd f (V.f j)) q') :=
        pullback_snd_of_isStableUnderBaseChangeAgainst P _ q' hQ (hdata j)
      have hsurj : Surjective q := by
        rw [surjective_iff]
        intro x
        obtain ⟨y, hy⟩ : ∃ y, (V.f j).base y = w.base x := (B.f i x).property
        obtain ⟨z, hz₁, -⟩ :=
          Scheme.exists_preimage_of_isPullback
            (IsPullback.of_hasPullback w (V.f j)) x y hy.symm
        exact ⟨z, hz₁⟩
      refine (pullback_snd_comp_iff (P := P) f (O.f j) (B.f i)).mpr ?_
      simpa [w] using hdesc q (hRbase (V.f j) w (hR j)) (pullback.snd f w)
        ((pullback_snd_parallel_iff (P := P) f (V.f j) w q' q pullback.condition.symm).mp hpull)
    exact (inferInstance : P.IsLocalAtTarget Scheme.zariskiPrecoverage).of_zeroHypercover B hB
  exact (inferInstance : P.IsLocalAtTarget Scheme.zariskiPrecoverage).of_zeroHypercover O hO

/-- The criterion behind the three cases of Tag 034G: a property which is Zariski local on the
target, stable under base change along `Q`, and which descends along surjective `R`-morphisms of
affine schemes, is local on the target for the topology generated by `Q`, provided every
`Q`-covering of an affine scheme is refined through open immersions by a covering by affine
schemes with structure morphisms in `R`. -/
theorem isLocalAtTarget_of_standardRefinement
    {Q R : MorphismProperty Scheme.{u}}
    [Q.IsStableUnderBaseChange]
    [P.IsStableUnderBaseChangeAgainst Q]
    [P.IsLocalAtTarget Scheme.zariskiPrecoverage]
    (hdesc : ∀ {S S' X : Scheme.{u}} [IsAffine S] [IsAffine S']
      (g : S' ⟶ S) [Surjective g] (_ : R g) (f : X ⟶ S),
        P (pullback.snd f g) → P f)
    (hopenQ : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y), IsOpenImmersion g → Q g)
    (hRbase : ∀ {U S W : Scheme.{u}} [IsAffine U] [IsAffine S] [IsAffine W]
      (g : U ⟶ S) (w : W ⟶ S), R g → R (pullback.fst w g))
    (hRopen : ∀ {U S : Scheme.{u}} [IsAffine U] [IsAffine S]
      (g : U ⟶ S), R g → IsOpenMap g)
    (hrefine : ∀ {T : Scheme.{u}} [IsAffine T] (W : T.Cover.{u} (Scheme.precoverage Q)),
      ∃ (V : T.Cover.{u} (Scheme.precoverage Q))
        (r : V.toPreZeroHypercover.Hom W.toPreZeroHypercover),
        (∀ j, IsAffine (V.X j)) ∧ (∀ j, R (V.f j)) ∧
          ∀ j, IsOpenImmersion (r.h₀ j)) :
    P.IsLocalAtTarget (Scheme.precoverage Q) := by
  have := precoverage_isStableUnderBaseChange Q
  refine MorphismProperty.IsLocalAtTarget.mk_of_small
    (P := P) (K := Scheme.precoverage Q) (fun {X Y f} 𝒲 hf i => ?_) (fun {X Y f} 𝒲 hdata => ?_)
  · have hq : Q (𝒲.f i) :=
      ((Scheme.presieve₀_mem_precoverage_iff 𝒲.toPreZeroHypercover).mp 𝒲.mem₀).2 i
    exact pullback_snd_of_isStableUnderBaseChangeAgainst P f (𝒲.f i) hq hf
  · let A := Y.affineCover
    rw [MorphismProperty.IsLocalAtTarget.iff_of_zeroHypercover (P := P) A]
    intro i
    let v := A.f i
    let W := 𝒲.pullback₁ v
    have hdata' (j : W.I₀) : P (pullback.snd (pullback.snd f v) (W.f j)) := by
      have hcomp : P (pullback.snd f (pullback.snd v (𝒲.f j) ≫ 𝒲.f j)) :=
        pullback_snd_refine P f (𝒲.f j) _ (hopenQ _ inferInstance) (hdata j)
      rw [(pullback.condition (f := v) (g := 𝒲.f j)).symm] at hcomp
      exact (pullback_snd_comp_iff (P := P) f v (pullback.fst v (𝒲.f j))).mpr hcomp
    obtain ⟨V, r, hAffine, hR, hopen⟩ := hrefine W
    refine descent_of_standardCover P hdesc hopenQ hRbase hRopen
      (pullback.snd f v) V hAffine hR (fun j => ?_)
    rw [← r.w₀ j]
    exact pullback_snd_refine P _ (W.f (r.s₀ j)) (r.h₀ j)
      (hopenQ _ (hopen j)) (hdata' (r.s₀ j))

/-- An étale covering of an affine scheme is refined, through open immersions, by a covering by
affine schemes which are standard étale over the target. This is the étale analogue of Tags
0222 and 0228, and follows from the local structure of an étale morphism, Tag 02GT. -/
theorem exists_affine_standardEtale_refinement {T : Scheme.{u}} [IsAffine T]
    (W : T.Cover.{u} Scheme.etalePrecoverage) :
    ∃ (V : T.Cover.{u} Scheme.etalePrecoverage)
      (r : V.toPreZeroHypercover.Hom W.toPreZeroHypercover),
      (∀ j, IsAffine (V.X j)) ∧
        (∀ j, ∀ (_ : IsAffine (V.X j)) (_ : IsAffine T), IsStandardEtale (V.f j)) ∧
          ∀ j, IsOpenImmersion (r.h₀ j) := by
  obtain ⟨hcov, hEt⟩ := (Scheme.presieve₀_mem_precoverage_iff W.toPreZeroHypercover).mp W.mem₀
  have : IsAffine (⊤ : T.Opens).toScheme := isAffineOpen_top T
  choose idx pt hpt using hcov
  choose O hO hmem hle hstd using fun t =>
    (etaleAt_iff_exists_isStandardEtale_restrict (W.f (idx t)) (pt t) ⊤
      (isAffineOpen_top T) (by simp)).mp
      ((etale_iff_forall_etaleAt (W.f (idx t))).mp (hEt (idx t)) (pt t))
  have : ∀ t : T, IsAffine (O t).toScheme := hO
  let chart (t : T) : (O t).toScheme ⟶ T :=
    (W.f (idx t)).resLE (⊤ : T.Opens) (O t) (hle t) ≫ T.topIso.hom
  have hfactor (t : T) : (O t).ι ≫ W.f (idx t) = chart t :=
    ((W.f (idx t)).resLE_comp_ι (hle t)).symm
  have hchart (t : T) : IsStandardEtale (chart t) := by
    refine (isStandardEtale_iff_of_arrow_iso (chart t)
      ((W.f (idx t)).resLE (⊤ : T.Opens) (O t) (hle t))
      (Arrow.isoMk (Iso.refl _) T.topIso.symm ?_)).mpr (hstd t)
    dsimp only [Arrow.mk_hom, Iso.refl_hom, Iso.symm_hom]
    rw [Category.id_comp, Category.assoc, T.topIso.hom_inv_id, Category.comp_id]
  have hetale (t : T) : Etale (chart t) := by
    rw [← hfactor t]
    have : Etale (W.f (idx t)) := hEt (idx t)
    infer_instance
  have hcovers (t : T) : ∃ j y, (chart j) y = t := by
    refine ⟨t, ⟨pt t, hmem t⟩, ?_⟩
    rw [← hfactor t]
    exact hpt t
  exact ⟨Scheme.Cover.mkOfCovers (P := @Etale) (T : Type u)
      (fun t => (O t).toScheme) chart hcovers hetale,
    ⟨idx, fun t => (O t).ι, hfactor⟩, hO,
    fun t _ _ => hchart t, fun t => show IsOpenImmersion (O t).ι from inferInstance⟩

/-- **Stacks Project, Tag 034G, étale case.** A property of morphisms of schemes which is
Zariski local on the target and stable under étale base change is étale local on the target as
soon as it descends along surjective standard étale morphisms of affine schemes. -/
@[stacks 034G "étale case"]
theorem isLocalAtTarget_etale_of_standard_descent
    [P.IsStableUnderBaseChangeAgainst (@Etale)]
    [P.IsLocalAtTarget Scheme.zariskiPrecoverage]
    (h : ∀ {S S' X : Scheme.{u}} [IsAffine S] [IsAffine S']
      (g : S' ⟶ S) [Surjective g] (_hg : IsStandardEtale g)
      (f : X ⟶ S), P (pullback.snd f g) → P f) :
    P.IsLocalAtTarget Scheme.etalePrecoverage := by
  refine isLocalAtTarget_of_standardRefinement P (Q := @Etale)
    (R := fun {A B} g => ∀ (_ : IsAffine A) (_ : IsAffine B), IsStandardEtale g)
    (fun {A B Y} _ _ g _ hg f hp => h g (hg inferInstance inferInstance) f hp)
    (fun {A B} g hi => by have : IsOpenImmersion g := hi; infer_instance)
    (fun {A B C} _ _ _ g w hg _ _ =>
      isStandardEtale_pullback_fst g w (hg inferInstance inferInstance))
    (fun {A B} _ _ g hg => ?_) (fun {T} _ W => ?_)
  · let : Algebra Γ(B, ⊤) Γ(A, ⊤) := g.appTop.hom.toAlgebra
    let : Algebra.IsStandardEtale Γ(B, ⊤) Γ(A, ⊤) := hg inferInstance inferInstance
    have hring : g.appTop.hom.Etale :=
      RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale _ _)
    have : Etale g := (HasRingHomProperty.iff_of_isAffine (P := @Etale)).2 hring
    exact g.isOpenMap
  · exact exists_affine_standardEtale_refinement W

/-- **Stacks Project, Tag 034G, smooth case.** A property of morphisms of schemes which is
Zariski local on the target and stable under smooth base change is smooth local on the target as
soon as it descends along surjective standard smooth morphisms of affine schemes. -/
@[stacks 034G "smooth case"]
theorem isLocalAtTarget_smooth_of_standard_descent
    [P.IsStableUnderBaseChangeAgainst (@Smooth)]
    [P.IsLocalAtTarget Scheme.zariskiPrecoverage]
    (h : ∀ {S S' X : Scheme.{u}} [IsAffine S] [IsAffine S']
      (g : S' ⟶ S) [Surjective g] (_hg : IsStandardSmooth g)
      (f : X ⟶ S), P (pullback.snd f g) → P f) :
    P.IsLocalAtTarget (Scheme.precoverage (@Smooth)) := by
  refine isLocalAtTarget_of_standardRefinement P (Q := @Smooth)
    (R := fun {A B} g => ∀ (_ : IsAffine A) (_ : IsAffine B), IsStandardSmooth g)
    (fun {A B Y} _ _ g _ hg f hp => h g (hg inferInstance inferInstance) f hp)
    (fun {A B} g hi => by have : IsOpenImmersion g := hi; infer_instance)
    (fun {A B C} _ _ _ g w hg _ _ =>
      isStandardSmooth_pullback_fst g w (hg inferInstance inferInstance))
    (fun {A B} _ _ g hg => ?_) (fun {T} _ W => ?_)
  · have : Smooth g :=
      (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).2
        (RingHom.IsStandardSmooth.smooth (hg inferInstance inferInstance))
    exact g.isOpenMap
  · obtain ⟨V, r, -, hstd, hopen⟩ := exists_finite_affine_standardSmooth_refinement W
    exact ⟨V.cover, r, fun j => inferInstanceAs (IsAffine (Spec (V.X j))),
      fun j _ _ => hstd j, hopen⟩

/-- **Stacks Project, Tag 034G, syntomic case.** A property of morphisms of schemes which is
Zariski local on the target and stable under syntomic base change is syntomic local on the
target as soon as it descends along surjective standard syntomic morphisms of affine
schemes. -/
@[stacks 034G "syntomic case"]
theorem isLocalAtTarget_syntomic_of_standard_descent
    [P.IsStableUnderBaseChangeAgainst (@Syntomic)]
    [P.IsLocalAtTarget Scheme.zariskiPrecoverage]
    (h : ∀ {S S' X : Scheme.{u}} [IsAffine S] [IsAffine S']
      (g : S' ⟶ S) [Surjective g] (_hg : IsStandardSyntomic g)
      (f : X ⟶ S), P (pullback.snd f g) → P f) :
    P.IsLocalAtTarget (Scheme.precoverage (@Syntomic)) := by
  refine isLocalAtTarget_of_standardRefinement P (Q := @Syntomic)
    (R := fun {A B} g => ∀ (_ : IsAffine A) (_ : IsAffine B), IsStandardSyntomic g)
    (fun {A B Y} _ _ g _ hg f hp => h g (hg inferInstance inferInstance) f hp)
    (fun {A B} g hi => by have : IsOpenImmersion g := hi; exact syntomic_of_isOpenImmersion g)
    (fun {A B C} _ _ _ g w hg _ _ =>
      isStandardSyntomic_pullback_fst g w (hg inferInstance inferInstance))
    (fun {A B} _ _ g hg => ?_) (fun {T} _ W => ?_)
  · have : UniversallyOpen g :=
      universallyOpen_of_syntomic
        (syntomic_of_standardSyntomic (hg inferInstance inferInstance))
    exact g.isOpenMap
  · have hcover : IsSyntomicCovering W.X W.f := by
      obtain ⟨hcov, hsyn⟩ :=
        (Scheme.presieve₀_mem_precoverage_iff W.toPreZeroHypercover).mp W.mem₀
      exact ⟨hsyn, Set.eq_univ_iff_forall.mpr fun x => Set.mem_iUnion.mpr (hcov x)⟩
    obtain ⟨V, r, -, hstd, hopen⟩ :=
      exists_finite_affine_standardSyntomic_refinement W.toPreZeroHypercover hcover
    exact ⟨V.cover, r, fun j => inferInstanceAs (IsAffine (Spec (V.X j))),
      fun j _ _ => hstd j, hopen⟩

end AlgebraicGeometry
