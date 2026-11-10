module

public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
public import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhSiteCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction
public import StacksFrontier.CategoryTheory.Sites.Descent.SheafForTransArrows
public import StacksFrontier.CategoryTheory.Sites.Pretopology.TautologicalRelaxed

/-!
# Sheaves on the big ph site

A presheaf of sets on the big ph site over a scheme `S` is a sheaf precisely when it satisfies
Zariski descent and descent along every proper surjective morphism of the site. Granted
Zariski descent, the proper-surjective condition need only be tested over affine targets.

## Main definitions

* `AlgebraicGeometry.IsZariskiSheaf`, `AlgebraicGeometry.IsProperSurjectiveSheaf` and
  `AlgebraicGeometry.IsAffineProperSurjectiveSheaf` — the three descent conditions.

## Main results

* `AlgebraicGeometry.isSheaf_iff_zariski_and_properSurjective` — the characterization of ph
  sheaves.
* `AlgebraicGeometry.properSurjective_iff_affine` — the reduction of proper-surjective descent
  to affine targets.

## Implementation notes

Descent along a single proper surjective morphism is the sheaf condition for its singleton
presieve, which for a set-valued presheaf is exactly the equalizer bijection
`F(U) ≃ eq(F(V) ⇉ F(V ×_U V))` of the source.

The forward implication of the characterization is immediate: a proper surjection is a ph
covering (Stacks 0DES) and a Zariski covering is a ph covering, and both are realized inside
the site by Stacks 0DBK. The converse goes through a coverage whose covering families are the
Zariski coverings together with the proper surjections; the two generate the ph topology, and
the coverage criterion for sheaves then only requires the sheaf condition for those two
families and their base changes, which is where the affine reduction is used.

## References

* [Stacks Project, Tag 0DBQ](https://stacks.math.columbia.edu/tag/0DBQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u w v v'

namespace AlgebraicGeometry


variable (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (F : (BigPHOver B S hS)ᵒᵖ ⥤ Type w)

/-- Zariski descent for every family of objects of the big ph slice whose
underlying family is a Zariski covering of schemes. -/
public def IsZariskiSheaf : Prop :=
  ∀ (X : BigPHOver B S hS)
    (E : PreZeroHypercover.{u + 1} X),
    (E.map (BigPHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((BigPHOver.toScheme B S hS).obj X) →
      Presieve.IsSheafFor F E.presieve₀

/-- Descent for every proper surjective morphism of the big ph slice. -/
public def IsProperSurjectiveSheaf : Prop :=
  ∀ (X Y : BigPHOver B S hS) (f : Y ⟶ X),
    IsProper ((BigPHOver.toScheme B S hS).map f) →
    Surjective ((BigPHOver.toScheme B S hS).map f) →
    Presieve.IsSheafFor F (Presieve.ofArrows (fun _ : Unit ↦ Y) (fun _ ↦ f))

/-- Descent for proper surjective morphisms with affine target. -/
public def IsAffineProperSurjectiveSheaf : Prop :=
  ∀ (X Y : BigPHOver B S hS) (f : Y ⟶ X),
    IsAffine ((BigPHOver.toScheme B S hS).obj X) →
    IsProper ((BigPHOver.toScheme B S hS).map f) →
    Surjective ((BigPHOver.toScheme B S hS).map f) →
    Presieve.IsSheafFor F (Presieve.ofArrows (fun _ : Unit ↦ Y) (fun _ ↦ f))

private theorem properSurjective_singleton_mem
    {B : BigPHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : BigPHOver B S hS} (f : Y ⟶ X)
    (hproper : IsProper ((BigPHOver.toScheme B S hS).map f))
    (hsurj : Surjective ((BigPHOver.toScheme B S hS).map f)) :
    Sieve.generate (Presieve.singleton f) ∈ BigPHOver.topology B S hS X := by
  let p := BigPHOver.forget B S hS
  let T := p.obj X
  let Q : PreZeroHypercover.{u + 1} T :=
    ⟨PUnit.{u + 2}, fun _ ↦ p.obj Y, fun _ ↦ p.map f⟩
  let QS : PreZeroHypercover.{u + 1} (B.inclusion.obj T) :=
    ⟨PUnit.{u + 2}, fun _ ↦ B.inclusion.obj (p.obj Y),
      fun _ ↦ B.inclusion.map (p.map f)⟩
  have hp' : IsProper (B.inclusion.map (p.map f)) := hproper
  have hs' : Surjective (B.inclusion.map (p.map f)) := hsurj
  have hph₀ : IsPHCovering (fun _ : Unit ↦ B.inclusion.obj (p.obj Y))
      (fun _ ↦ B.inclusion.map (p.map f)) :=
    surjective_proper_isPHCovering (B.inclusion.map (p.map f))
  have hph : IsPHCoveringInCutoff ⟨T, Q⟩ := by
    change IsPHCovering QS.X QS.f
    unfold IsPHCovering at hph₀ ⊢
    obtain ⟨hlft, hloc⟩ := hph₀
    refine ⟨fun _ ↦ hlft (), fun U hU ↦ ?_⟩
    obtain ⟨P, hP, ⟨φ⟩⟩ := hloc U hU
    let e : PUnit.{u + 2} ≃ PUnit := Equiv.punitEquivPUnit
    let ψ : P.Hom (QS.pullback₂ U.ι) :=
      { s₀ := fun i ↦ e.symm (φ.s₀ i)
        h₀ := fun i ↦ φ.h₀ i
        w₀ := fun i ↦ φ.w₀ i }
    exact ⟨P, hP, ⟨ψ⟩⟩
  obtain ⟨V, hV, hcomb⟩ := B.covering_representative ⟨T, Q⟩ hph
  rcases hcomb with ⟨hT, hcomb⟩
  rcases V with ⟨Vbase, Vfam⟩
  change T = Vbase at hT
  subst Vbase
  have hpres : Q.presieve₀ = Vfam.presieve₀ :=
    PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb
  have hgenT : Sieve.generate Q.presieve₀ ∈ B.topology T := by
    rw [hpres]
    exact Precoverage.generate_mem_toGrothendieck ((B.mem_precoverage_iff).2 ⟨Vfam, rfl, hV⟩)
  rw [BigPHOver.topology, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_generate]
  change Sieve.generate (Presieve.functorPushforward p (Presieve.singleton f)) ∈
    B.topology (p.obj X)
  rw [← Sieve.arrows_generate_map_eq_functorPushforward, Presieve.map_singleton]
  simpa [Q, T, p, PreZeroHypercover.presieve₀,
    Presieve.ofArrows_pUnit] using hgenT

private theorem zariski_presieve_mem
    {B : BigPHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : BigPHOver B S hS} (E : PreZeroHypercover.{u + 1} X)
    (hE : (E.map (BigPHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((BigPHOver.toScheme B S hS).obj X)) :
    Sieve.generate E.presieve₀ ∈ BigPHOver.topology B S hS X := by
  let p := BigPHOver.forget B S hS
  let T := p.obj X
  let Eb := E.map p
  let Es := (E.map p).map B.inclusion
  have hEs : Es.presieve₀ ∈ Scheme.zariskiPrecoverage (B.inclusion.obj T) := by
    simpa [Es, p, T, BigPHOver.toScheme,
      BigPHOver.forget, PreZeroHypercover.map] using hE
  let U : Scheme.OpenCover.{u + 1} (B.inclusion.obj T) := ⟨Es, hEs⟩
  obtain ⟨V, hV, hEq⟩ := openCover_tautologicallyEquivalent B T U
  let : B.inclusion.Full := ObjectProperty.full_ι (schemeSizeBelow B.cutoff)
  let : B.inclusion.Faithful := ObjectProperty.faithful_ι (schemeSizeBelow B.cutoff)
  have hgenV : Sieve.generate V.presieve₀ ∈ B.topology T :=
    Precoverage.generate_mem_toGrothendieck ((B.mem_precoverage_iff).2 ⟨V, rfl, hV⟩)
  have hFF : B.inclusion.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful B.inclusion
  have hEqScheme : PreZeroHypercover.TautologicallyEquivalent
      (Eb.map B.inclusion) (V.map B.inclusion) := by
    simpa [U, Es, Eb] using hEq
  have hEqB : PreZeroHypercover.TautologicallyEquivalent Eb V := by
    rcases hEqScheme with ⟨⟨α, hα⟩, ⟨β, hβ⟩⟩
    constructor
    · refine ⟨α, fun i => ?_⟩
      obtain ⟨e, he⟩ := hα i
      let eB : B.inclusion.obj (Eb.X i) ≅ B.inclusion.obj (V.X (α i)) := e
      refine ⟨hFF.preimageIso eB, ?_⟩
      have hmap : B.inclusion.map (hFF.preimageIso eB).hom = eB.hom :=
        hFF.map_preimage eB.hom
      apply B.inclusion.map_injective
      rw [Functor.map_comp, hmap]
      simpa [PreZeroHypercover.map] using he
    · refine ⟨β, fun j => ?_⟩
      obtain ⟨e, he⟩ := hβ j
      let eB : B.inclusion.obj (V.X j) ≅ B.inclusion.obj (Eb.X (β j)) := e
      refine ⟨hFF.preimageIso eB, ?_⟩
      have hmap : B.inclusion.map (hFF.preimageIso eB).hom = eB.hom :=
        hFF.map_preimage eB.hom
      apply B.inclusion.map_injective
      rw [Functor.map_comp, hmap]
      simpa [PreZeroHypercover.map] using he
  have hgenEb : Sieve.generate Eb.presieve₀ ∈ B.topology T := by
    rw [PreZeroHypercover.generate_presieve₀_eq_of_tautologicallyEquivalent Eb V hEqB]
    exact hgenV
  rw [BigPHOver.topology, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_generate]
  change Sieve.generate (Presieve.functorPushforward p E.presieve₀) ∈ B.topology (p.obj X)
  rw [← Sieve.arrows_generate_map_eq_functorPushforward]
  simpa [Eb, T, p, PreZeroHypercover.presieve₀, PreZeroHypercover.presieve₀_map]
    using hgenEb

private noncomputable def openCoverOver
    {B : BigPHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : BigPHOver B S hS}
    (U : ((BigPHOver.toScheme B S hS).obj X).OpenCover) :
    PreZeroHypercover.{u + 1} X :=
  let T := (BigPHOver.forget B S hS).obj X
  { I₀ := U.I₀
    X i := Over.mk
      ((ObjectProperty.homMk (U.f i) :
        (B.obj (U.X i) (Scheme.size_lt_of_isOpenImmersion (U.f i) T.2)) ⟶ T) ≫ X.hom)
    f i := Over.homMk (ObjectProperty.homMk (U.f i)) (by simp) }

/-- The family `openCoverOver U` is a Zariski covering of the underlying scheme. -/
private theorem openCoverOver_presieve₀_mem
    {B : BigPHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : BigPHOver B S hS}
    (U : ((BigPHOver.toScheme B S hS).obj X).OpenCover) :
    ((openCoverOver U).map (BigPHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((BigPHOver.toScheme B S hS).obj X) := by
  simpa [openCoverOver, PreZeroHypercover.presieve₀, PreZeroHypercover.map] using U.mem₀

private theorem openCoverOver_isSheafFor
    {B : BigPHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigPHOver B S hS)ᵒᵖ ⥤ Type w}
    (hF : IsZariskiSheaf B S hS F)
    (X : BigPHOver B S hS)
    (U : ((BigPHOver.toScheme B S hS).obj X).OpenCover) :
    Presieve.IsSheafFor F (openCoverOver U).presieve₀ :=
  hF X (openCoverOver U) (openCoverOver_presieve₀_mem U)

/-- A Zariski sheaf is strongly a sheaf for the one-hypercover of any open cover. -/
private theorem openCoverOver_isStronglySheafFor
    {B : BigPHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigPHOver B S hS)ᵒᵖ ⥤ Type w}
    (hF : IsZariskiSheaf B S hS F)
    (X : BigPHOver B S hS)
    (U : ((BigPHOver.toScheme B S hS).obj X).OpenCover) :
    (openCoverOver U).toPreOneHypercover.IsStronglySheafFor F := by
  refine ⟨openCoverOver_isSheafFor hF X U, ?_⟩
  intro i j W a b hab
  have hid : ((openCoverOver U).toPreOneHypercover.sieve₁ a b) (𝟙 W) := by
    refine ⟨PUnit.unit, Limits.pullback.lift a b hab, ?_, ?_⟩
    · rw [Category.id_comp]
      exact (Limits.pullback.lift_fst a b hab).symm
    · rw [Category.id_comp]
      exact (Limits.pullback.lift_snd a b hab).symm
  intro x t₁ t₂ ht₁ ht₂
  simpa using (ht₁ (𝟙 W) hid).trans (ht₂ (𝟙 W) hid).symm

private theorem zariskiCover_pullback_isSheafFor
    {B : BigPHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigPHOver B S hS)ᵒᵖ ⥤ Type w}
    (hZ : IsZariskiSheaf B S hS F)
    {X Y : BigPHOver B S hS}
    (E : PreZeroHypercover.{u + 1} X)
    (hE : (E.map (BigPHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((BigPHOver.toScheme B S hS).obj X))
    (g : Y ⟶ X) :
    Presieve.IsSheafFor F ((Sieve.generate E.presieve₀).pullback g).arrows := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let Eb := E.map (BigPHOver.toScheme B S hS)
  let Eb' := Eb.pullback₂ ((BigPHOver.toScheme B S hS).map g)
  let E' := E.pullback₂ g
  have hmem : Eb'.presieve₀ ∈ Scheme.zariskiPrecoverage
      ((BigPHOver.toScheme B S hS).obj Y) :=
    Scheme.zariskiPrecoverage.mem_coverings_of_isPullback Eb.f (by simpa [Eb] using hE)
      ((BigPHOver.toScheme B S hS).map g)
      (fun i => Limits.pullback.snd (Eb.f i)
        ((BigPHOver.toScheme B S hS).map g))
      (fun i => Limits.pullback.fst (Eb.f i)
        ((BigPHOver.toScheme B S hS).map g))
      (fun i => (IsPullback.of_hasPullback (Eb.f i)
        ((BigPHOver.toScheme B S hS).map g)).flip)
  let hIso : E'.map (BigPHOver.toScheme B S hS) ≅ Eb' :=
    PreZeroHypercover.isoMk (Equiv.refl E'.I₀)
      (fun i => Limits.PreservesPullback.iso
        (BigPHOver.toScheme B S hS) (E.f i) g)
      (fun i => Limits.PreservesPullback.iso_hom_snd
        (BigPHOver.toScheme B S hS) (E.f i) g)
  rw [← Sieve.pullbackArrows_comm,
    ← Presieve.isSheafFor_iff_generate,
    ← PreZeroHypercover.presieve₀_pullback₁]
  exact hZ Y E' (Eb'.presieve₀_mem_of_iso hIso.symm hmem)

private theorem isSheafFor_pushforward_of_properSurjective
    {B : BigPHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigPHOver B S hS)ᵒᵖ ⥤ Type w}
    (hP : IsProperSurjectiveSheaf B S hS F)
    {U X : BigPHOver B S hS} (g : U ⟶ X)
    (O : Sieve U)
    (hO : ∀ ⦃Y : BigPHOver B S hS⦄ (a : Y ⟶ U),
      Presieve.IsSheafFor F (O.pullback a).arrows)
    (hproper : IsProper ((BigPHOver.toScheme B S hS).map g))
    (hsurj : Surjective ((BigPHOver.toScheme B S hS).map g)) :
    Presieve.IsSheafFor F (O.pushforward g : Presieve X) := by
  classical
  let R := Sieve.generateSingleton g
  let lift : ∀ {Y : BigPHOver B S hS} (f : Y ⟶ X), R f → (Y ⟶ U) :=
    fun {Y} f hf => if hs : O.pushforward g f then Classical.choose hs else Classical.choose hf
  have hlift : ∀ {Y : BigPHOver B S hS} (f : Y ⟶ X) (hf : R f),
      lift f hf ≫ g = f := by
    intro Y f hf
    dsimp [lift]
    split_ifs with hs
    · exact (Classical.choose_spec hs).1
    · exact Classical.choose_spec hf
  have hliftO : ∀ {Y : BigPHOver B S hS} (f : Y ⟶ X)
      (hf : R f), O.pushforward g f → O (lift f hf) := by
    intro Y f hf hs
    dsimp [lift]
    simp only [dite_eq_left hs]
    exact (Classical.choose_spec hs).2
  let D : ∀ ⦃Y : BigPHOver B S hS⦄ ⦃f : Y ⟶ X⦄, R f → Sieve Y :=
    fun {Y} {f} hf => O.pullback (lift f hf)
  have hR : Presieve.IsSheafFor F (R : Presieve X) := by
    have hsing : Presieve.IsSheafFor F (Presieve.singleton g) := by
      simpa [Presieve.ofArrows_pUnit] using hP X U g hproper hsurj
    simpa [R, Sieve.generateSingleton_eq] using
      (Presieve.isSheafFor_iff_generate (Presieve.singleton g)).1 hsing
  have hbind := Presieve.isSheafFor_bind F R D hR
    (fun {_} {_} hf => hO (lift _ hf))
    (by
      intro Y f hf Z q
      simpa [D, Sieve.pullback_comp] using (hO (q ≫ lift f hf)).isSeparatedFor)
  have hEq : Sieve.bind R D = O.pushforward g := by
    ext Y f
    constructor
    · rintro ⟨Z, q, r, hq, hr, rfl⟩
      change ∃ a, a ≫ g = q ≫ r ∧ O a
      refine ⟨q ≫ lift r hq, ?_, ?_⟩
      · rw [Category.assoc, hlift]
      · exact hr
    · rintro ⟨a, rfl, ha⟩
      refine ⟨Y, 𝟙 Y, a ≫ g, ?_, ?_, by simp⟩
      · exact ⟨a, rfl⟩
      · change O (𝟙 Y ≫ lift (a ≫ g) ⟨a, rfl⟩)
        exact hliftO (a ≫ g) ⟨a, rfl⟩ ⟨a, rfl, ha⟩
  simpa [hEq] using hbind

private theorem isSheafFor_composite_of_properSurjective
    {B : BigPHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigPHOver B S hS)ᵒᵖ ⥤ Type w}
    (hP : IsProperSurjectiveSheaf B S hS F)
    {U X : BigPHOver B S hS} (g : U ⟶ X)
    {I : Type (u + 1)} {V : I → BigPHOver B S hS}
    (j : ∀ i, V i ⟶ U)
    (hO : ∀ ⦃Y : BigPHOver B S hS⦄ (a : Y ⟶ U),
      Presieve.IsSheafFor F
        ((Sieve.generate (Presieve.ofArrows V j)).pullback a).arrows)
    (hproper : IsProper ((BigPHOver.toScheme B S hS).map g))
    (hsurj : Surjective ((BigPHOver.toScheme B S hS).map g)) :
    Presieve.IsSheafFor F (Presieve.ofArrows V (fun i ↦ j i ≫ g)) := by
  let O : Sieve U := Sieve.generate (Presieve.ofArrows V j)
  have hpush := isSheafFor_pushforward_of_properSurjective hP g O hO hproper hsurj
  have hEq : Sieve.generate (Presieve.ofArrows V (fun i ↦ j i ≫ g)) = O.pushforward g := by
    rw [← Sieve.generate_pushforward, Presieve.pushforward_ofArrows]
  have hgen : Presieve.IsSheafFor F
      (Sieve.generate (Presieve.ofArrows V (fun i ↦ j i ≫ g)) : Presieve X) := by
    rw [hEq]
    exact hpush
  exact (Presieve.isSheafFor_iff_generate _).2 hgen

private theorem standardPHCovering_of_sourceIso
    {T : Scheme.{u}} [IsAffine T] {I : Type v}
    {X Y : I → Scheme.{u}} {f : ∀ i, X i ⟶ T} {g : ∀ i, Y i ⟶ T}
    (e : ∀ i, X i ≅ Y i)
    (he : ∀ i, (e i).hom ≫ g i = f i)
    (hY : StandardPHCovering g) :
    StandardPHCovering f := by
  obtain ⟨U, p, j, hp, hsurj, hj, hcover, hcomp⟩ := hY.exists_presentation
  let : Finite I := hY.finite
  refine StandardPHCovering.of_presentation f (fun i ↦ ?_)
    p (fun i ↦ (e i).hom ≫ j i) hp hsurj (fun i ↦ by infer_instance) ?_ ?_
  · let : IsAffine (Y i) := hY.isAffine i
    exact IsAffine.of_isIso (e i).hom
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    have hx : x ∈ ⋃ i, Set.range (j i) := by
      rw [hcover]
      exact Set.mem_univ x
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    refine ⟨(e i).inv y, ?_⟩
    rw [← hy]
    simp
  · intro i
    simp [hcomp, he]

private theorem standardPHCovering_reindex
    {T : Scheme.{u}} [IsAffine T] {I : Type v} {J : Type v'}
    (e : I ≃ J) {X : J → Scheme.{u}} {f : ∀ j, X j ⟶ T}
    (hX : StandardPHCovering f) :
    StandardPHCovering (fun i ↦ f (e i)) := by
  obtain ⟨U, p, j, hp, hsurj, hj, hcover, hcomp⟩ := hX.exists_presentation
  let : Finite J := hX.finite
  let : Finite I := Finite.of_equiv J e.symm
  refine StandardPHCovering.of_presentation _
    (fun i ↦ ?_) p (fun i ↦ j (e i)) hp hsurj (fun i ↦ hj (e i)) ?_ ?_
  · exact hX.isAffine (e i)
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    have hUnion : (⋃ i, Set.range (j (e i))) = ⋃ k, Set.range (j k) := by
      symm
      exact Set.iUnion_congr_of_surjective (fun k ↦ e.symm k)
        e.symm.surjective (fun k ↦ by rw [e.apply_symm_apply])
    rw [hUnion, hcover]
    exact Set.mem_univ x
  · intro i
    exact hcomp (e i)

private theorem standardPHCovering_postcomposeIso
    {T T' : Scheme.{u}} [IsAffine T] (e : T ≅ T')
    {I : Type v} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T}
    (h : StandardPHCovering f) :
    @StandardPHCovering I T' (IsAffine.of_isIso e.inv) X
      (fun i ↦ f i ≫ e.hom) := by
  let : IsAffine T' := IsAffine.of_isIso e.inv
  obtain ⟨U, p, j, hp, hsurj, hj, hcover, hcomp⟩ := h.exists_presentation
  let : Finite I := h.finite
  let : IsProper (p ≫ e.hom) := by infer_instance
  let : Surjective (p ≫ e.hom) := by infer_instance
  refine StandardPHCovering.of_presentation (fun i ↦ f i ≫ e.hom)
    h.isAffine (p ≫ e.hom) j inferInstance inferInstance hj hcover ?_
  exact fun i ↦ by rw [← Category.assoc, hcomp]


/-- The base change of a proper surjective morphism of the slice is proper and surjective on
underlying schemes. -/
private theorem toScheme_map_pullback_snd_properSurjective
    {B : BigPHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : BigPHOver B S hS} (f : Y ⟶ X) (g : Z ⟶ X)
    (hproper : IsProper ((BigPHOver.toScheme B S hS).map f))
    (hsurj : Surjective ((BigPHOver.toScheme B S hS).map f)) :
    IsProper ((BigPHOver.toScheme B S hS).map (Limits.pullback.snd f g)) ∧
      Surjective ((BigPHOver.toScheme B S hS).map (Limits.pullback.snd f g)) := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let : IsProper ((BigPHOver.toScheme B S hS).map f) := hproper
  let : Surjective ((BigPHOver.toScheme B S hS).map f) := hsurj
  rw [← Limits.pullbackComparison_comp_snd]
  exact ⟨(MorphismProperty.cancel_left_of_respectsIso (P := @IsProper) _ _).2 inferInstance,
    (MorphismProperty.cancel_left_of_respectsIso (P := @Surjective) _ _).2 inferInstance⟩

private theorem affineProperSurjective_pullback_isSheafFor
    {B : BigPHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigPHOver B S hS)ᵒᵖ ⥤ Type w}
    (hA : IsAffineProperSurjectiveSheaf B S hS F)
    {X Y Z : BigPHOver B S hS} (f : Y ⟶ X) (g : Z ⟶ X)
    (hAffine : IsAffine ((BigPHOver.toScheme B S hS).obj Z))
    (hproper : IsProper ((BigPHOver.toScheme B S hS).map f))
    (hsurj : Surjective ((BigPHOver.toScheme B S hS).map f)) :
    Presieve.IsSheafFor F (Presieve.singleton (Limits.pullback.snd f g)) := by
  obtain ⟨hp, hs⟩ := toScheme_map_pullback_snd_properSurjective f g hproper hsurj
  simpa [IsAffineProperSurjectiveSheaf, Presieve.ofArrows_pUnit] using
    hA Z (Limits.pullback f g) (Limits.pullback.snd f g) hAffine hp hs

private theorem properSurjective_pullback_isSeparated
    {B : BigPHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigPHOver B S hS)ᵒᵖ ⥤ Type w}
    (hZ : IsZariskiSheaf B S hS F)
    (hA : IsAffineProperSurjectiveSheaf B S hS F)
    {X Y Z : BigPHOver B S hS} (f : Y ⟶ X) (g : Z ⟶ X)
    (hproper : IsProper ((BigPHOver.toScheme B S hS).map f))
    (hsurj : Surjective ((BigPHOver.toScheme B S hS).map f)) :
    Presieve.IsSeparatedFor F
      (Presieve.singleton (Limits.pullback.snd f g)) := by
  let p := Limits.pullback.snd f g
  let U0 := (Scheme.affineOpenCover.{u}
    ((BigPHOver.toScheme B S hS).obj Z)).openCover
  let U : Scheme.OpenCover.{u + 1, u}
      ((BigPHOver.toScheme B S hS).obj Z) :=
    U0.reindex (Equiv.ulift.{u + 1, u})
  let E := openCoverOver U
  have hE := openCoverOver_isSheafFor hZ Z U
  intro x t₁ t₂ ht₁ ht₂
  have hxy : F.map p.op t₁ = F.map p.op t₂ := by
    exact (ht₁ _ (Presieve.singleton_self _)).trans
      (ht₂ _ (Presieve.singleton_self _)).symm
  apply hE.isSeparatedFor.ext
  intro W q hq
  rcases hq with ⟨i⟩
  let q₁ := E.f i
  let pᵢ := Limits.pullback.snd p q₁
  have hAffine : IsAffine ((BigPHOver.toScheme B S hS).obj (E.X i)) := by
    dsimp [E, openCoverOver, U]
    change IsAffine (U0.X (Equiv.ulift.{u + 1, u} i))
    exact Scheme.isAffine_affineOpenCover _ _ (Equiv.ulift.{u + 1, u} i)
  obtain ⟨hp, hs⟩ := toScheme_map_pullback_snd_properSurjective f g hproper hsurj
  have hlocal := affineProperSurjective_pullback_isSheafFor hA p q₁ hAffine hp hs
  have hlocalEq : F.map pᵢ.op (F.map q₁.op t₁) =
      F.map pᵢ.op (F.map q₁.op t₂) := by
    have hh := congrArg (F.map (Limits.pullback.fst p q₁).op) hxy
    have hcomp : pᵢ ≫ q₁ = Limits.pullback.fst p q₁ ≫ p := by
      exact Limits.pullback.condition.symm
    have hh' : F.map (Limits.pullback.fst p q₁ ≫ p).op t₁ =
        F.map (Limits.pullback.fst p q₁ ≫ p).op t₂ := by
      calc
        F.map (Limits.pullback.fst p q₁ ≫ p).op t₁ =
            F.map (Limits.pullback.fst p q₁).op (F.map p.op t₁) := by simp
        _ = F.map (Limits.pullback.fst p q₁).op (F.map p.op t₂) := hh
        _ = F.map (Limits.pullback.fst p q₁ ≫ p).op t₂ := by simp
    have hleft : F.map pᵢ.op (F.map q₁.op t₁) = F.map (pᵢ ≫ q₁).op t₁ := by
      rw [← types_comp_apply (F.map q₁.op) (F.map pᵢ.op),
        ← Functor.map_comp, ← op_comp]
    have hright : F.map pᵢ.op (F.map q₁.op t₂) = F.map (pᵢ ≫ q₁).op t₂ := by
      rw [← types_comp_apply (F.map q₁.op) (F.map pᵢ.op),
        ← Functor.map_comp, ← op_comp]
    rw [hleft, hright, hcomp]
    exact hh'
  have hq₁ : F.map q₁.op t₁ = F.map q₁.op t₂ := by
    apply hlocal.isSeparatedFor.ext
    intro T a ha
    rcases ha with ⟨⟩
    exact hlocalEq
  simpa [E, q₁, openCoverOver] using hq₁

private theorem properSurjective_of_affine
    {B : BigPHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigPHOver B S hS)ᵒᵖ ⥤ Type w}
    (hZ : IsZariskiSheaf B S hS F)
    (hA : IsAffineProperSurjectiveSheaf B S hS F) :
    IsProperSurjectiveSheaf B S hS F := by
  intro X Y f hproper hsurj
  let Xs := (BigPHOver.toScheme B S hS).obj X
  let U0 := (Scheme.affineOpenCover.{u} Xs).openCover
  let U : Scheme.OpenCover.{u + 1, u} Xs := U0.reindex (Equiv.ulift.{u + 1, u})
  let E := openCoverOver U
  let E₁ := E.toPreOneHypercover
  have hstrong : E₁.IsStronglySheafFor F := openCoverOver_isStronglySheafFor hZ X U
  have h₂ : ∀ ⦃Z : BigPHOver B S hS⦄ (g : Z ⟶ X),
      Presieve.IsSeparatedFor F (E₁.sieve₀.pullback g).arrows := by
    intro Z g
    have hlocal := zariskiCover_pullback_isSheafFor hZ E (openCoverOver_presieve₀_mem U) g
    simpa [E₁, E] using hlocal.isSeparatedFor
  have hlocal (i : E₁.I₀) :
      Presieve.IsSheafFor F
        ((Sieve.generate (Presieve.singleton f)).pullback (E₁.f i)).arrows := by
    have hAffine : IsAffine
        ((BigPHOver.toScheme B S hS).obj (E₁.X i)) := by
      dsimp [E₁, E, openCoverOver, U]
      change IsAffine (U0.X (Equiv.ulift.{u + 1, u} i))
      exact Scheme.isAffine_affineOpenCover _ _ (Equiv.ulift.{u + 1, u} i)
    have hbase := affineProperSurjective_pullback_isSheafFor
      hA f (E₁.f i) hAffine hproper hsurj
    rw [← Sieve.pullbackArrows_comm, Presieve.pullback_singleton,
      ← Presieve.isSheafFor_iff_generate]
    exact hbase
  have hlocal' ⦃i j : E₁.I₀⦄ (k : E₁.I₁ i j) :
      Presieve.IsSeparatedFor F
        ((Sieve.generate (Presieve.singleton f)).pullback
          (E₁.p₁ k ≫ E₁.f i)).arrows := by
    have hbase := properSurjective_pullback_isSeparated hZ hA f
      (E₁.p₁ k ≫ E₁.f i) hproper hsurj
    rw [← Sieve.pullbackArrows_comm, Presieve.pullback_singleton,
      ← Presieve.isSeparatedFor_iff_generate]
    exact hbase
  have hresult := PreOneHypercover.IsStronglySheafFor.isSheafFor_of_pullback
    hstrong h₂ (R := Presieve.singleton f) hlocal hlocal'
  simpa [IsProperSurjectiveSheaf, Presieve.ofArrows_pUnit] using hresult

private theorem standardPHCovering_isSheafFor
    {B : BigPHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigPHOver B S hS)ᵒᵖ ⥤ Type w}
    (hZ : IsZariskiSheaf B S hS F)
    (hA : IsAffineProperSurjectiveSheaf B S hS F)
    {X : BigPHOver B S hS} [IsAffine
      ((BigPHOver.toScheme B S hS).obj X)]
    (E : PreZeroHypercover.{u + 1} X)
    (hE : StandardPHCovering
      (E.map (BigPHOver.toScheme B S hS)).f) :
    Presieve.IsSheafFor F E.presieve₀ := by
  classical
  obtain ⟨U, g, j, hproper, hsurj, hj, hcover, hcomp⟩ := hE.exists_presentation
  have hT : ((BigPHOver.toScheme B S hS).obj X).size < B.cutoff :=
    (BigPHOver.forget B S hS).obj X |>.property
  have hU : U.size < B.cutoff :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact g hT
  let Uobj : BigPHOver B S hS :=
    Over.mk ((ObjectProperty.homMk g : B.obj U hU ⟶
      (BigPHOver.forget B S hS).obj X) ≫ X.hom)
  let G : Uobj ⟶ X := Over.homMk (ObjectProperty.homMk g) (by simp [Uobj])
  have hidx : (E.map (BigPHOver.toScheme B S hS)).I₀ = E.I₀ := rfl
  let Eopen : PreZeroHypercover.{u + 1} Uobj := {
    I₀ := (E.map (BigPHOver.toScheme B S hS)).I₀
    X i := E.X (hidx ▸ i)
    f i := Over.homMk (ObjectProperty.homMk (j i)) (by
      apply B.inclusion.map_injective
      change j i ≫ g ≫ B.inclusion.map X.hom =
        B.inclusion.map (E.X (hidx ▸ i)).hom
      rw [← Category.assoc, hcomp i]
      simp only [BigPHOver.toScheme, BigPHOver.forget]
      change B.inclusion.map ((E.f (hidx ▸ i)).left ≫ X.hom) =
        B.inclusion.map (E.X (hidx ▸ i)).hom
      exact congrArg B.inclusion.map (Over.w (E.f (hidx ▸ i)))) }
  have hmem : (Eopen.map (BigPHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage
        ((BigPHOver.toScheme B S hS).obj Uobj) := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro x
      have hx : x ∈ ⋃ i, Set.range (j i) := by
        rw [hcover]
        exact Set.mem_univ x
      obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
      exact ⟨i, y, rfl⟩
    · exact hj
  have hO : ∀ ⦃Y : BigPHOver B S hS⦄ (a : Y ⟶ Uobj),
      Presieve.IsSheafFor F
        ((Sieve.generate Eopen.presieve₀).pullback a).arrows := by
    intro Y a
    exact zariskiCover_pullback_isSheafFor hZ Eopen hmem a
  have hcompSheaf := isSheafFor_composite_of_properSurjective
    (properSurjective_of_affine hZ hA) G Eopen.f hO hproper hsurj
  have hcompOver (i : E.I₀) : Eopen.f i ≫ G = E.f i :=
    Over.OverMorphism.ext (B.inclusion.map_injective (hcomp i))
  have hEq : Presieve.ofArrows E.X (fun i ↦ Eopen.f i ≫ G) = E.presieve₀ := by
    simp [PreZeroHypercover.presieve₀, hcompOver]
  rw [← hEq]
  exact hcompSheaf

private theorem standardPHCovering_pullback_isSeparatedFor
    {B : BigPHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigPHOver B S hS)ᵒᵖ ⥤ Type w}
    (hZ : IsZariskiSheaf B S hS F)
    (hA : IsAffineProperSurjectiveSheaf B S hS F)
    {X Y : BigPHOver B S hS} [IsAffine
      ((BigPHOver.toScheme B S hS).obj X)]
    (E : PreZeroHypercover.{u + 1} X)
    (hE : StandardPHCovering
      (E.map (BigPHOver.toScheme B S hS)).f)
    (q : Y ⟶ X) :
    Presieve.IsSeparatedFor F
      ((Sieve.generate E.presieve₀).pullback q).arrows := by
  classical
  let yscheme := (BigPHOver.toScheme B S hS).obj Y
  let U0 := (Scheme.affineOpenCover.{u} yscheme).openCover
  let U : Scheme.OpenCover.{u + 1, u} yscheme :=
    U0.reindex (Equiv.ulift.{u + 1, u})
  let Ec := openCoverOver U
  have hEc := openCoverOver_isSheafFor hZ Y U
  intro x t₁ t₂ ht₁ ht₂
  apply hEc.isSeparatedFor.ext
  intro W a ha
  rcases ha with ⟨i⟩
  let b := Ec.f i ≫ q
  let E' := E.pullback₂ b
  let D := (E.map (BigPHOver.toScheme B S hS)).pullback₂
    ((BigPHOver.toScheme B S hS).map b)
  have hAffine : IsAffine ((BigPHOver.toScheme B S hS).obj (Ec.X i)) :=
    Scheme.isAffine_affineOpenCover _ _ (Equiv.ulift.{u + 1, u} i)
  have hDB : StandardPHCovering D.f :=
    StandardPHCovering.pullback hE ((BigPHOver.toScheme B S hS).map b)
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let hIso : E'.map (BigPHOver.toScheme B S hS) ≅ D :=
    PreZeroHypercover.isoMk (Equiv.refl E'.I₀)
      (fun k ↦ Limits.PreservesPullback.iso
        (BigPHOver.toScheme B S hS) (E.f k) b)
      (fun k ↦ Limits.PreservesPullback.iso_hom_snd
        (BigPHOver.toScheme B S hS) (E.f k) b)
  have hD' : StandardPHCovering
      (E'.map (BigPHOver.toScheme B S hS)).f := by
    let e : E'.I₀ ≃ D.I₀ := Equiv.refl E'.I₀
    have hDB' := standardPHCovering_reindex e hDB
    exact standardPHCovering_of_sourceIso
      (fun k ↦ asIso (hIso.hom.h₀ k)) (fun k ↦ hIso.hom.w₀ k) hDB'
  have hlocal := standardPHCovering_isSheafFor hZ hA E' hD'
  have hlocalEq' : F.map (Ec.f i).op t₁ = F.map (Ec.f i).op t₂ := by
    apply hlocal.isSeparatedFor.ext
    intro Z r hr
    rcases hr with ⟨k⟩
    have hk : E'.f k ≫ b = Limits.pullback.fst (E.f k) b ≫ E.f k := by
      rw [PreZeroHypercover.pullback₂_f b E k]
      exact Limits.pullback.condition.symm
    have hmem : ((Sieve.generate E.presieve₀).pullback q)
        (E'.f k ≫ Ec.f i) := by
      change (Sieve.generate E.presieve₀) (E'.f k ≫ (Ec.f i ≫ q))
      refine ⟨E.X k, Limits.pullback.fst (E.f k) b, E.f k, ⟨k⟩, ?_⟩
      change Limits.pullback.fst (E.f k) b ≫ E.f k = E'.f k ≫ b
      exact hk.symm
    simpa only [← types_comp_apply, ← F.map_comp, ← op_comp] using
      (ht₁ _ hmem).trans (ht₂ _ hmem).symm
  simpa [Ec] using hlocalEq'

private theorem isSheafFor_phCovering_affine
    {B : BigPHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigPHOver B S hS)ᵒᵖ ⥤ Type w}
    (hZ : IsZariskiSheaf B S hS F)
    (hA : IsAffineProperSurjectiveSheaf B S hS F)
    {X : BigPHOver B S hS}
    [IsAffine ((BigPHOver.toScheme B S hS).obj X)]
    (E : PreZeroHypercover.{u + 1} X)
    (hE : IsPHCovering
      (E.map (BigPHOver.toScheme B S hS)).X
      (E.map (BigPHOver.toScheme B S hS)).f) :
    Presieve.IsSheafFor F E.presieve₀ := by
  classical
  let T := (BigPHOver.toScheme B S hS).obj X
  let U : T.Opens := ⊤
  have hU : IsAffineOpen U := isAffineOpen_top T
  let : IsAffine U.toScheme := hU
  obtain ⟨V, hV, ⟨ρ⟩⟩ := (isPHCovering_iff _ _).mp hE |>.2 U hU
  let J := ULift.{u + 1, u} V.I₀
  let e : J ≃ V.I₀ := Equiv.ulift
  let V' := V.reindex e
  let ρ' : V'.Hom
      ((E.map (BigPHOver.toScheme B S hS)).pullback₂ U.ι) :=
    { s₀ i := ρ.s₀ (e i)
      h₀ i := ρ.h₀ (e i)
      w₀ i := ρ.w₀ (e i) }
  have hV' : StandardPHCovering V'.f :=
    standardPHCovering_reindex e hV
  obtain ⟨P, p, j, hp, hsurj, hj, hcover, hcomp⟩ := hV'.exists_presentation
  let : IsProper p := hp
  let : LocallyOfFiniteType p := inferInstance
  let : QuasiCompact p := inferInstance
  have hTsize : T.size < B.cutoff := X.left.property
  have hUsize : U.toScheme.size < B.cutoff :=
    Scheme.size_lt_of_isOpenImmersion U.ι hTsize
  have hPsize : P.size < B.cutoff :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact p hUsize
  have hVsize (i : V'.I₀) : (V'.X i).size < B.cutoff := by
    let : IsOpenImmersion (j i) := hj i
    exact Scheme.size_lt_of_isOpenImmersion (j i) hPsize
  let Vover : PreZeroHypercover.{u + 1} X := {
    I₀ := V'.I₀
    X i := Over.mk
      ((ObjectProperty.homMk (V'.f i ≫ U.ι) :
        B.obj (V'.X i) (hVsize i) ⟶ X.left) ≫ X.hom)
    f i := Over.homMk (ObjectProperty.homMk (V'.f i ≫ U.ι) :
      B.obj (V'.X i) (hVsize i) ⟶ X.left) (by simp) }
  have hVover : StandardPHCovering
      (Vover.map (BigPHOver.toScheme B S hS)).f := by
    change @StandardPHCovering V'.I₀ T _ V'.X
      (fun i ↦ V'.f i ≫ U.ι)
    exact standardPHCovering_postcomposeIso T.topIso hV'
  have hVsheaf := standardPHCovering_isSheafFor hZ hA Vover hVover
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  have : Limits.PreservesLimitsOfShape Limits.WalkingCospan
      (BigPHOver.toScheme B S hS) := inferInstance
  let α : V'.I₀ → E.I₀ := ρ'.s₀
  have hcomm (i : V'.I₀) :
      ρ'.h₀ i ≫ Limits.pullback.fst
          ((E.map (BigPHOver.toScheme B S hS)).f (ρ'.s₀ i)) U.ι ≫
        (E.map (BigPHOver.toScheme B S hS)).f (ρ'.s₀ i) =
      V'.f i ≫ U.ι := by
    have hw : ρ'.h₀ i ≫ Limits.pullback.snd
        ((E.map (BigPHOver.toScheme B S hS)).f (ρ'.s₀ i)) U.ι =
        V'.f i := ρ'.w₀ i
    calc
      _ = ρ'.h₀ i ≫ Limits.pullback.snd
            ((E.map (BigPHOver.toScheme B S hS)).f (ρ'.s₀ i)) U.ι ≫ U.ι :=
        congrArg (fun a ↦ ρ'.h₀ i ≫ a) Limits.pullback.condition
      _ = (ρ'.h₀ i ≫ Limits.pullback.snd
            ((E.map (BigPHOver.toScheme B S hS)).f (ρ'.s₀ i)) U.ι) ≫ U.ι :=
        (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun a ↦ a ≫ U.ι) hw
  let f : ∀ i, Vover.X i ⟶ E.X (α i) := fun i =>
    Over.homMk
      (ObjectProperty.homMk
        (ρ'.h₀ i ≫ Limits.pullback.fst
          ((E.map (BigPHOver.toScheme B S hS)).f (α i)) U.ι) :
        (B.obj (V'.X i) (hVsize i)) ⟶ (BigPHOver.forget B S hS).obj (E.X (α i)))
      (by
        apply B.inclusion.map_injective
        have he := congrArg B.inclusion.map (Over.w (E.f (α i)))
        change ((E.f (α i)).left).hom ≫ X.hom.hom = (E.X (α i)).hom.hom at he
        change (ρ'.h₀ i ≫ Limits.pullback.fst _ _) ≫ (E.X (α i)).hom.hom =
          (V'.f i ≫ U.ι) ≫ X.hom.hom
        rw [← he]
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun a ↦ a ≫ X.hom.hom) ((Category.assoc _ _ _).trans (hcomm i))))
  have hf : ∀ i, f i ≫ E.f (α i) = Vover.f i := by
    intro i
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    dsimp [f, Vover, BigPHOver.toScheme, BigPHOver.forget]
    exact hcomm i
  let UV : ∀ (_ : E.I₀) (_ : V'.I₀), BigPHOver B S hS :=
    fun i j => Limits.pullback (Vover.f j) (E.f i)
  let uvToV : ∀ i j, UV i j ⟶ Vover.X j :=
    fun i j => Limits.pullback.fst (Vover.f j) (E.f i)
  let uvToU : ∀ i j, UV i j ⟶ E.X i :=
    fun i j => Limits.pullback.snd (Vover.f j) (E.f i)
  have huv : ∀ i j, uvToV i j ≫ Vover.f j = uvToU i j ≫ E.f i := by
    intro i j
    exact Limits.pullback.condition
  have hsep (i : E.I₀) : Presieve.IsSeparatedFor F
      (Presieve.ofArrows (fun j : V'.I₀ => UV i j) (uvToU i)) := by
    have hs := standardPHCovering_pullback_isSeparatedFor hZ hA Vover hVover (E.f i)
    intro x t₁ t₂ ht₁ ht₂
    apply hs.ext
    intro Z q hq
    rcases hq with ⟨W, a, b, hb, hab⟩
    rcases hb with ⟨j⟩
    let k : Z ⟶ UV i j := Limits.pullback.lift a q (by simpa using hab)
    have heq := (ht₁ (uvToU i j) (Presieve.ofArrows.mk j)).trans
      (ht₂ (uvToU i j) (Presieve.ofArrows.mk j)).symm
    have hk := congrArg (F.map k.op) heq
    simpa [k, uvToU, ← types_comp_apply, ← F.map_comp, ← op_comp,
      Limits.pullback.lift_snd] using hk
  have hUU : ∀ i i', Limits.HasPullback (E.f i) (E.f i') := by infer_instance
  have hVV : ∀ i i', Limits.HasPullback (Vover.f i) (Vover.f i') := by infer_instance
  have hUV (i : E.I₀) (j : V'.I₀) : Limits.IsLimit
      (Limits.PullbackCone.mk (uvToV i j) (uvToU i j) (huv i j)) := by
    exact Limits.pullbackIsPullback _ _
  have hinj (i : E.I₀) : Function.Injective
      (fun s : F.obj (.op (E.X i)) => fun j : V'.I₀ => F.map (uvToU i j).op s) := by
    intro s t hst
    let x : Presieve.FamilyOfElements F
        (Presieve.ofArrows (fun j : V'.I₀ => UV i j) (uvToU i)) :=
      fun _ f _ => F.map f.op s
    apply hsep i x s t
    · intro Y g hg
      rfl
    · intro Y g hg
      rcases hg with ⟨j⟩
      exact (congrFun hst j).symm
  exact isSheafFor_ofArrows_of_refinement E.X Vover.X UV E.f Vover.f α f hf
    uvToV uvToU huv
    hUU hUV hVV F hVsheaf hinj


private theorem isSeparatedFor_of_affine_pullbacks
    {B : BigPHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigPHOver B S hS)ᵒᵖ ⥤ Type w}
    (hZ : IsZariskiSheaf B S hS F)
    {X : BigPHOver B S hS} (R : Sieve X)
    (H : ∀ (Y : BigPHOver B S hS) (f : Y ⟶ X),
      IsAffine ((BigPHOver.toScheme B S hS).obj Y) →
      Presieve.IsSheafFor F (R.pullback f).arrows) :
    Presieve.IsSeparatedFor F R.arrows := by
  let U₀ := (Scheme.affineOpenCover.{u}
    ((BigPHOver.toScheme B S hS).obj X)).openCover
  let U := U₀.reindex (Equiv.ulift.{u + 1, u})
  let E := openCoverOver U
  intro x s t hs ht
  apply (openCoverOver_isSheafFor hZ X U).isSeparatedFor.ext
  rintro Y f ⟨i⟩
  have hA : IsAffine ((BigPHOver.toScheme B S hS).obj (E.X i)) :=
    Scheme.isAffine_affineOpenCover _ _ (Equiv.ulift.{u + 1, u} i)
  apply (H (E.X i) (E.f i) hA).isSeparatedFor.ext
  intro Z g hg
  simpa only [← types_comp_apply, ← F.map_comp, ← op_comp] using
    (hs (g ≫ E.f i) hg).trans (ht (g ≫ E.f i) hg).symm

private theorem isSheafFor_of_affine_pullbacks
    {B : BigPHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigPHOver B S hS)ᵒᵖ ⥤ Type w}
    (hZ : IsZariskiSheaf B S hS F)
    {X : BigPHOver B S hS} (R : Sieve X)
    (H : ∀ (Y : BigPHOver B S hS) (f : Y ⟶ X),
      IsAffine ((BigPHOver.toScheme B S hS).obj Y) →
      Presieve.IsSheafFor F (R.pullback f).arrows) :
    Presieve.IsSheafFor F R.arrows := by
  let U₀ := (Scheme.affineOpenCover.{u}
    ((BigPHOver.toScheme B S hS).obj X)).openCover
  let U := U₀.reindex (Equiv.ulift.{u + 1, u})
  let E := openCoverOver U
  apply (openCoverOver_isStronglySheafFor hZ X U).isSheafFor_sieve_of_pullback
  · intro Y f
    exact (zariskiCover_pullback_isSheafFor hZ E (openCoverOver_presieve₀_mem U) f).isSeparatedFor
  · intro i
    exact H (E.X i) (E.f i)
      (Scheme.isAffine_affineOpenCover _ _ (Equiv.ulift.{u + 1, u} i))
  · intro i j k
    apply isSeparatedFor_of_affine_pullbacks hZ
    intro Y f hY
    rw [← Sieve.pullback_comp]
    exact H Y _ hY

private def phCoverage (B : BigPHSite.{u}) : Coverage B.Schemes where
  toPrecoverage := B.precoverage
  pullback := by
    intro X Y f R hR
    obtain ⟨E, rfl, hE⟩ := (B.mem_precoverage_iff).mp hR
    obtain ⟨P, p, q, hpq, hP⟩ := B.isSite.2.2 ⟨X, E⟩ hE Y f
    refine ⟨Presieve.ofArrows P q, ⟨⟨E.I₀, P, q⟩, rfl, hP⟩, ?_⟩
    rintro Z g ⟨i⟩
    exact ⟨E.X i, p i, E.f i, ⟨i⟩, (hpq i).w⟩

/-- A localized coverage criterion: to compare the localization at `X` of the topology
generated by a coverage `K` with a topology `J` on the slice at `X`, it suffices to check the
sieves generated by the covering families of `K`, read on the slice.

This is pure category theory, and it is the form in which the comparison is used: it avoids
proving two topologies equal, needing only the covering families of a coverage rather than
every sieve of the topology it generates. -/
public theorem over_le_of_coverage
    {C : Type v} [Category.{v'} C] (K : Coverage C) (X : C)
    (J : GrothendieckTopology (Over X))
    (H : ∀ (Y : Over X) (R : Presieve Y.left), R ∈ K Y.left →
      (Sieve.overEquiv Y).symm (Sieve.generate R) ∈ J Y) :
    K.toGrothendieck.over X ≤ J := by
  intro ⟨Y, right, s⟩ R hR
  obtain ⟨(R : Sieve Y), rfl⟩ := (Sieve.overEquiv _).symm.surjective R
  simp only [GrothendieckTopology.mem_over_iff, OrderIso.apply_symm_apply,
    Coverage.mem_toGrothendieck, Over.left] at hR
  change K.Saturate Y R at hR
  induction hR with
  | of Z R hR => exact H (Over.mk s) R hR
  | top => simp
  | transitive Y R T hR hT ih ih' =>
    refine J.transitive (ih s) _ fun Z g hg ↦ ?_
    obtain rfl : right = Z.right := Subsingleton.elim _ _
    rw [← Sieve.overEquiv_symm_pullback]
    exact ih' hg Z.hom

private theorem isSheafFor_covering_over_affine_pullback
    {B : BigPHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigPHOver B S hS)ᵒᵖ ⥤ Type w}
    (hZ : IsZariskiSheaf B S hS F)
    (hA : IsAffineProperSurjectiveSheaf B S hS F)
    {X Y : BigPHOver B S hS}
    (E : PreZeroHypercover.{u + 1} X.left) (hE : B.IsCovering ⟨X.left, E⟩)
    (f : Y ⟶ X) (hY : IsAffine ((BigPHOver.toScheme B S hS).obj Y)) :
    Presieve.IsSheafFor F
      (((Sieve.overEquiv X).symm (Sieve.generate E.presieve₀)).pullback f).arrows := by
  obtain ⟨P, p, q, hpq, hP⟩ := B.isSite.2.2 ⟨X.left, E⟩ hE Y.left f.left
  let D : PreZeroHypercover.{u + 1} Y :=
    { I₀ := E.I₀
      X i := Over.mk (q i ≫ Y.hom)
      f i := Over.homMk (q i) }
  have hD : IsPHCovering
      (D.map (BigPHOver.toScheme B S hS)).X
      (D.map (BigPHOver.toScheme B S hS)).f := hP.ph
  have hsheaf := (Presieve.isSheafFor_iff_generate D.presieve₀).mp
    (isSheafFor_phCovering_affine hZ hA D hD)
  convert hsheaf using 1
  congr 1
  ext Z g
  rw [Sieve.pullback_apply, Sieve.overEquiv_symm_iff]
  constructor
  · rintro ⟨W, a, b, ⟨i⟩, hab⟩
    have hw : a ≫ E.f i = g.left ≫ f.left := hab
    let l := (hpq i).lift a g.left hw
    have hl : l ≫ q i = g.left := (hpq i).lift_snd _ _ _
    let k : Z ⟶ D.X i := Over.homMk l (by
      dsimp [D]
      rw [← Category.assoc, hl, Over.w])
    exact ⟨D.X i, k, D.f i, ⟨i⟩, Over.OverMorphism.ext hl⟩
  · rintro ⟨W, a, b, ⟨i⟩, hab⟩
    refine ⟨E.X i, a.left ≫ p i, E.f i, ⟨i⟩, ?_⟩
    have hw : a.left ≫ q i = g.left := congrArg Over.Hom.left hab
    rw [Category.assoc, (hpq i).w, ← Category.assoc, hw]
    rfl

private theorem isSheaf_of_zariski_and_affineProperSurjective
    {B : BigPHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigPHOver B S hS)ᵒᵖ ⥤ Type w}
    (hZ : IsZariskiSheaf B S hS F)
    (hA : IsAffineProperSurjectiveSheaf B S hS F) :
    Presieve.IsSheaf (BigPHOver.topology B S hS) F := by
  have hle : BigPHOver.topology B S hS ≤ Sheaf.finestTopologySingle F := by
    change B.precoverage.toGrothendieck.over (B.obj S hS) ≤ _
    change (phCoverage B).toPrecoverage.toGrothendieck.over (B.obj S hS) ≤ _
    rw [Coverage.toGrothendieck_toPrecoverage]
    apply over_le_of_coverage
    intro X R hR
    obtain ⟨E, rfl, hE⟩ := (B.mem_precoverage_iff).mp hR
    intro Y f
    apply isSheafFor_of_affine_pullbacks hZ
    intro Z g hZ'
    rw [← Sieve.pullback_comp]
    exact isSheafFor_covering_over_affine_pullback hZ hA E hE (g ≫ f) hZ'
  intro X R hR
  simpa using hle X hR X (𝟙 X)

/-- **Stacks 0DBQ, characterization.** The ph sheaf condition is equivalent
to Zariski descent together with proper-surjective descent. -/
@[stacks 0DBQ "sheaf characterization"]
public theorem isSheaf_iff_zariski_and_properSurjective :
    Presieve.IsSheaf (BigPHOver.topology B S hS) F ↔
      (IsZariskiSheaf B S hS F ∧ IsProperSurjectiveSheaf B S hS F) := by
  constructor
  · intro hF
    constructor
    · intro X E hE
      exact (Presieve.isSheafFor_iff_generate E.presieve₀).2
        (hF (Sieve.generate E.presieve₀)
          (zariski_presieve_mem E hE))
    · intro X Y f hproper hsurj
      have hgen := hF (Sieve.generate (Presieve.singleton f))
        (properSurjective_singleton_mem f hproper hsurj)
      simpa [Presieve.ofArrows_pUnit] using
        (Presieve.isSheafFor_iff_generate (Presieve.singleton f)).2 hgen
  · rintro ⟨hZ, hP⟩
    exact isSheaf_of_zariski_and_affineProperSurjective hZ
      (fun X Y f _ ↦ hP X Y f)

/-- **Stacks 0DBQ, affine reduction.** Under Zariski descent, proper-surjective
descent may be checked only when the target is affine. -/
@[stacks 0DBQ "affine reduction"]
public theorem properSurjective_iff_affine (hF : IsZariskiSheaf B S hS F) :
    IsProperSurjectiveSheaf B S hS F ↔
      IsAffineProperSurjectiveSheaf B S hS F := by
  constructor
  · intro hP X Y f hAffine hproper hsurj
    exact hP X Y f hproper hsurj
  · intro hAffine X Y f hproper hsurj
    exact properSurjective_of_affine hF hAffine X Y f hproper hsurj

end AlgebraicGeometry
