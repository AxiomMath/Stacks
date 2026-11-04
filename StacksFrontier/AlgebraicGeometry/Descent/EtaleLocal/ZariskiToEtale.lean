module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Criterion

/-!
# Upgrading Zariski locality to étale locality

A property of morphisms of schemes which is Zariski local on the source becomes étale local on the
source as soon as it is preserved by precomposition with an étale morphism and descends along a
surjective étale morphism of sources. Dually, a property which is Zariski local on the target,
stable under base change and preserved by postcomposition with an étale morphism becomes étale
local on the target, using the same descent along a surjective étale morphism of sources. Together
with the criterion of Tag 04R2 the two upgrades give
`AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget`.

## Main results

* `AlgebraicGeometry.exists_surjective_etale_onto_openImage`: an étale morphism factors as a
  surjective étale morphism onto its open image followed by the inclusion of that image.
* `AlgebraicGeometry.isLocalAtSource_etalePrecoverage_of_zariski_of_descent`: the upgrade from
  Zariski to étale locality on the source.
* `AlgebraicGeometry.isLocalAtTarget_etalePrecoverage_of_zariski_of_descent`: the upgrade from
  Zariski to étale locality on the target.
* `AlgebraicGeometry.respectsRight_isOpenImmersion_of_etale_postcomp`: a property preserved by
  postcomposition with an étale morphism is preserved by postcomposition with an open immersion.
* `AlgebraicGeometry.isEtaleLocalOnSourceAndTarget_of_zariski_of_descent`: such a property is étale
  local on the source and target.

## References

* [Stacks Project, Tag 04R2](https://stacks.math.columbia.edu/tag/04R2)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

universe u

/-- An étale morphism factors as a surjective étale morphism onto the open subscheme which is its
image, followed by the inclusion of that open subscheme. -/
theorem exists_surjective_etale_onto_openImage
    {V X : Scheme.{u}} (g : V ⟶ X) [Etale g] :
    ∃ (O : X.Opens) (gO : V ⟶ O.toScheme),
      (∀ x : X, x ∈ Set.range g.base → x ∈ O) ∧
        Surjective gO ∧ Etale gO ∧ gO ≫ O.ι = g := by
  let O : X.Opens := ⟨Set.range g.base, g.isOpenMap.isOpen_range⟩
  have hgRange : (⊤ : V.Opens) ≤ g ⁻¹ᵁ O := fun y _ => ⟨y, rfl⟩
  let gO : V ⟶ O.toScheme := V.topIso.inv ≫ g.resLE O ⊤ hgRange
  have hgOι : gO ≫ O.ι = g := by
    show V.topIso.inv ≫ (g.resLE O ⊤ hgRange ≫ O.ι) = g
    rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]
  have hEt : Etale gO := by
    have : Etale (g.resLE O ⊤ hgRange) := inferInstance
    dsimp only [gO]
    infer_instance
  have hsurj : Surjective gO := ⟨fun z ↦ by
    obtain ⟨y, hy⟩ := z.2
    exact ⟨y, Subtype.ext ((congrArg (fun a : V ⟶ X => a y) hgOι).trans hy)⟩⟩
  exact ⟨O, gO, fun _ hx => hx, hsurj, hEt, hgOι⟩

/-- A property of morphisms of schemes preserved by postcomposition with an étale morphism is
preserved by postcomposition with an open immersion. -/
theorem respectsRight_isOpenImmersion_of_etale_postcomp
    (P : MorphismProperty Scheme.{u})
    (hpost : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z), P f → Etale g → P (f ≫ g)) :
    MorphismProperty.RespectsRight P (@IsOpenImmersion : MorphismProperty Scheme.{u}) where
  postcomp g hg f hf := hpost f g hf (have : IsOpenImmersion g := hg; inferInstance)

/-- Every point of the base of an étale covering sieve is in the open image of a member of the
covering, which factors through that open image by a surjective étale morphism. -/
private theorem exists_surjective_etale_of_mem_etalePrecoverage
    {X : Scheme.{u}} {R : Presieve X} (hR : R ∈ Scheme.etalePrecoverage X) (x : X) :
    ∃ (O : X.Opens) (V : Scheme.{u}) (gO : V ⟶ O.toScheme) (g : V ⟶ X),
      R g ∧ x ∈ O ∧ Surjective gO ∧ Etale gO ∧ gO ≫ O.ι = g := by
  obtain ⟨ι, Z, fam, rfl⟩ := R.exists_eq_ofArrows
  have hR' : Presieve.ofArrows Z fam ∈ Scheme.precoverage (@Etale.{u}) X := hR
  obtain ⟨hjs, het⟩ := Iff.mp (Scheme.ofArrows_mem_precoverage_iff (@Etale.{u})) hR'
  obtain ⟨j, hj⟩ := hjs x
  have : Etale (fam j) := het _
  obtain ⟨O, gO, hmem, hsurjO, hEtO, hfac⟩ := exists_surjective_etale_onto_openImage (fam j)
  exact ⟨O, _, gO, _, ⟨j⟩, hmem x hj, hsurjO, hEtO, hfac⟩

/-- A property of morphisms of schemes which is Zariski local on the source, is preserved by
precomposition with an étale morphism and descends along a surjective étale morphism of sources is
étale local on the source. -/
theorem isLocalAtSource_etalePrecoverage_of_zariski_of_descent
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    (hpre : ∀ {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z), Etale g → P f → P (g ≫ f))
    (hdesc : ∀ {X Y Z : Scheme.{u}} (α : X ⟶ Y) (k : Y ⟶ Z), Surjective α → Etale α →
      P (α ≫ k) → P k) :
    MorphismProperty.IsLocalAtSource P Scheme.etalePrecoverage := by
  refine MorphismProperty.IsLocalAtSource.mk_of_iff ?_
  intro X Y f R hR
  constructor
  · intro hf U g hg
    exact hpre g f (hR.2 hg) hf
  · intro h
    have key : ∀ x : X, ∃ O : X.Opens, x ∈ O ∧ P (O.ι ≫ f) := by
      intro x
      obtain ⟨O, V, gO, g, hg, hxO, hsurjO, hEtO, hfac⟩ :=
        exists_surjective_etale_of_mem_etalePrecoverage hR x
      refine ⟨O, hxO, hdesc gO (O.ι ≫ f) hsurjO hEtO ?_⟩
      rw [← Category.assoc, hfac]
      exact h hg
    choose O hxO hO using key
    exact IsZariskiLocalAtSource.of_iSup_eq_top (P := P) O
      (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxO x⟩) hO

/-- A property of morphisms of schemes which is stable under base change, preserved by
postcomposition with an étale morphism and descends along a surjective étale morphism of sources
descends along a surjective étale base change: for a cartesian square `IsPullback p q f g` with `g`
surjective and étale, `P q` implies `P f`. -/
private theorem of_isPullback_of_surjective_etale
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    (hpost : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z), P f → Etale g → P (f ≫ g))
    (hdesc : ∀ {X Y Z : Scheme.{u}} (α : X ⟶ Y) (k : Y ⟶ Z), Surjective α → Etale α →
      P (α ≫ k) → P k)
    {W X Y Y' : Scheme.{u}} {p : W ⟶ X} {q : W ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback p q f g) (hsurj : Surjective g) (het : Etale g) (hq : P q) : P f := by
  have hpS : Surjective p :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@Surjective.{u} : MorphismProperty Scheme.{u})) sq.flip hsurj
  have hpE : Etale p :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@Etale.{u} : MorphismProperty Scheme.{u})) sq.flip het
  exact hdesc p f hpS hpE (by rw [sq.w]; exact hpost q g hq het)

/-- A property of morphisms of schemes which is Zariski local on the target, stable under base
change, preserved by postcomposition with an étale morphism and descends along a surjective étale
morphism of sources is étale local on the target. -/
theorem isLocalAtTarget_etalePrecoverage_of_zariski_of_descent
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P] [P.IsStableUnderBaseChange]
    (hpost : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z), P f → Etale g → P (f ≫ g))
    (hdesc : ∀ {X Y Z : Scheme.{u}} (α : X ⟶ Y) (k : Y ⟶ Z), Surjective α → Etale α →
      P (α ≫ k) → P k) :
    MorphismProperty.IsLocalAtTarget P Scheme.etalePrecoverage := by
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff ?_
  intro X Y f R hR
  constructor
  · intro hf U g _ _
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f g) hf
  · intro h
    refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := P) fun y => ?_
    obtain ⟨O, V, gO, g, hg, hmem, hsurjO, hEtO, hfac⟩ :=
      exists_surjective_etale_of_mem_etalePrecoverage hR y
    refine ⟨O, hmem, ?_⟩
    have hbot : IsPullback (pullback.snd f O.ι) (pullback.fst f O.ι) O.ι f :=
      (IsPullback.of_hasPullback f O.ι).flip
    have htot : IsPullback (pullback.snd f g) (pullback.fst f g)
        (gO ≫ O.ι) f := by
      rw [hfac]
      exact (IsPullback.of_hasPullback f g).flip
    have hres : P (f ∣_ O.ι.opensRange) :=
      (MorphismProperty.arrow_mk_iso_iff P (morphismRestrictOpensRange f O.ι)).mpr <|
        of_isPullback_of_surjective_etale hpost hdesc (IsPullback.of_bot' htot hbot).flip hsurjO
          hEtO (h _ hg)
    rwa [Scheme.Opens.opensRange_ι] at hres

/-- A property of morphisms of schemes which is Zariski local on the source and on the target,
stable under base change, preserved by precomposition and by postcomposition with an étale
morphism, and descends along a surjective étale morphism of sources is étale local on the source
and target. -/
theorem isEtaleLocalOnSourceAndTarget_of_zariski_of_descent
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P] [IsZariskiLocalAtTarget P]
    [P.IsStableUnderBaseChange]
    (hpre : ∀ {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z), Etale g → P f → P (g ≫ f))
    (hpost : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z), P f → Etale g → P (f ≫ g))
    (hdesc : ∀ {X Y Z : Scheme.{u}} (α : X ⟶ Y) (k : Y ⟶ Z), Surjective α → Etale α →
      P (α ≫ k) → P k) :
    IsEtaleLocalOnSourceAndTarget P :=
  have _ : MorphismProperty.IsLocalAtSource P Scheme.etalePrecoverage :=
    isLocalAtSource_etalePrecoverage_of_zariski_of_descent P hpre hdesc
  have _ : MorphismProperty.IsLocalAtTarget P Scheme.etalePrecoverage :=
    isLocalAtTarget_etalePrecoverage_of_zariski_of_descent P hpost hdesc
  have _ : MorphismProperty.RespectsRight P (@IsOpenImmersion : MorphismProperty Scheme.{u}) :=
    respectsRight_isOpenImmersion_of_etale_postcomp P hpost
  isEtaleLocalOnSourceAndTarget_of_isLocalAtSource_isLocalAtTarget P

end AlgebraicGeometry

end
