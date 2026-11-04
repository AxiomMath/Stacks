module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSitePostcomposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactQuasiSeparatedPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleSection

/-!
# Sections of an étale morphism across a thickening, in the value universe of the sheaves

Let `S` be a scheme contained in a big fppf site `B`. Stacks 05ZH, in the general-thickening
form proved in `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/EtaleSection.lean`, says that
a section of an étale morphism of algebraic spaces prescribed over a thickening of the base
extends uniquely. That statement lives among the presheaves of `Type u`, which is where the
algebraic spaces of this library live, and it takes the thickening as a *subspace* of the base:
a `CategoryTheory.Subfunctor` satisfying `AlgebraicGeometry.Space.IsThickening`.

A formal algebraic space is a sheaf of `Type (u + 1)`, so the morphisms that have to be lifted
in the proof of Stacks 0DEG are morphisms of presheaves of `Type (u + 1)`, and the thickening
arrives as a morphism `k : T₀ ⟶ T` of *schemes of the site*. This file performs that transport
once: the base is `yoneda.obj T ⋙ uliftFunctor`, the thickening subspace is the range of
`yoneda.map k`, and the étale morphism is descended to `Type u` by the full faithfulness of the
universe lift.

## Main results

* `AlgebraicGeometry.FormalSpace.existsUnique_section_uliftYoneda_of_isThickening`: the unique
  extension of a section, for an étale morphism onto the universe-lifted Yoneda presheaf of a
  scheme of the site and a thickening of that scheme.

## Implementation notes

The target is written `yoneda.obj T ⋙ uliftFunctor` rather than `uliftYoneda.obj T`. The two
are definitionally equal — `CategoryTheory.uliftYoneda` is `yoneda` whiskered with
`uliftFunctor` — but only the unfolded form lets `rw` see the universe lift as the image of the
whiskering functor whose full faithfulness, `AlgebraicGeometry.FormalSpace.liftFullyFaithful`,
is what descends `pr` and the prescribed section to `Type u`. Consumers holding `uliftYoneda`
terms can still apply the result directly.

Étaleness is descended along the chain already used for Stacks 0DED: the étale condition of
Stacks 03FR on a morphism whose target is a universe-lifted Yoneda presheaf gives the
every-étale-chart condition of Stacks 03MJ
(`AlgebraicGeometry.FormalSpace.holdsOnEveryEtaleChartULift_of_isEtaleULift_over_site`), that
condition is invariant under the comparison isomorphism
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChartULift_precomp`) and descends through
`AlgebraicGeometry.Space.holdsOnEveryEtaleChartULift_whiskerRight_iff`, and a surjective étale
chart square then gives `AlgebraicGeometry.Space.IsEtale`.

The thickening subspace is produced by
`AlgebraicGeometry.FormalSpace.isThickeningHom_yonedaSpace_map`, which turns a thickening of
schemes of the site into a thickening of the represented algebraic spaces, unbundled through
`AlgebraicGeometry.Space.IsThickeningHom.mono` and the second component of
`AlgebraicGeometry.Space.IsThickeningHom`. The subspace is stated over `yoneda.obj T` rather
than over `(schemeSpaceFunctor B S hS).obj T`: the two are definitionally equal, but the
`CategoryTheory.Subfunctor` carries its ambient presheaf as an argument, so the spelling of
that argument decides whether the inclusion `ι` produced by the lifting lemma is syntactically
the one the rest of the proof rewrites with.

## References

* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 05ZP](https://stacks.math.columbia.edu/tag/05ZP)
* [Stacks Project, Tag 0DEG](https://stacks.math.columbia.edu/tag/0DEG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of presheaves of `Type (u + 1)` between universe lifts is the lift of its
preimage. -/
private theorem whiskerRight_preimage_liftFullyFaithful
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⋙ uliftFunctor.{u + 1} ⟶ Y ⋙ uliftFunctor.{u + 1}) :
    Functor.whiskerRight ((liftFullyFaithful B S hS).preimage f) uliftFunctor.{u + 1} = f :=
  (liftFullyFaithful B S hS).map_preimage _

/-- Two morphisms of presheaves of `Type u` with the same universe lift are equal. -/
private theorem eq_of_whiskerRight_eq {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f g : X ⟶ Y}
    (h : Functor.whiskerRight f uliftFunctor.{u + 1} =
      Functor.whiskerRight g uliftFunctor.{u + 1}) :
    f = g :=
  (liftFullyFaithful B S hS).map_injective h

/-- The descent of an étale morphism onto a universe-lifted scheme of the site to `Type u`
is étale. -/
private theorem isEtale_preimage_of_isEtaleULift {T : BigFppfOver B S hS}
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hA : IsAlgebraicSpace B S hS A)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (e : A ⋙ uliftFunctor.{u + 1} ≅ P)
    (pr : P ⟶ yoneda.obj T ⋙ uliftFunctor.{u + 1})
    (hpr : Space.IsEtaleULift.{u + 1} B S hS pr) :
    Space.IsEtale B S hS ((liftFullyFaithful B S hS).preimage (e.hom ≫ pr)) := by
  have hyT : IsAlgebraicSpace B S hS (yoneda.obj T) :=
    ((schemeSpaceFunctor B S hS).obj T).property
  have hLa := whiskerRight_preimage_liftFullyFaithful B S hS (e.hom ≫ pr)
  set a : A ⟶ yoneda.obj T := (liftFullyFaithful B S hS).preimage (e.hom ≫ pr) with ha_def
  have hchartU' : Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (Functor.whiskerRight a uliftFunctor.{u + 1}) := by
    rw [hLa]
    exact Space.holdsOnEveryEtaleChartULift_precomp B S hS _ e.hom pr
      (holdsOnEveryEtaleChartULift_of_isEtaleULift_over_site B S hS _ (fun _ h ↦ h) pr hpr)
  obtain ⟨U', V', α, β, h', hα, hβ, hαS, hw, hhE⟩ :=
    (Space.holdsOnEveryEtaleChart_iff_surjectiveChart B S hS _
      AlgebraicGeometry.etale_isEtaleLocalOnSourceAndTarget hA hyT a).mp
      ((Space.holdsOnEveryEtaleChartULift_whiskerRight_iff.{u + 1} B S hS _ a).mp hchartU')
  exact (Space.isEtale_iff_exists_etale_chart_square B S hS hA hyT a).mpr
    ⟨U', V', α, β, h', hw.symm, hαS, hα, hβ, hhE⟩

/-- A section of an étale morphism of algebraic spaces onto a scheme of the site, prescribed
over a thickening of that scheme, extends uniquely. -/
private theorem existsUnique_section_yoneda_of_isThickening
    {T₀ T : BigFppfOver B S hS} (k : T₀ ⟶ T)
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hA : IsAlgebraicSpace B S hS A)
    {a : A ⟶ yoneda.obj T} (ha : Space.IsEtale B S hS a)
    (τ₀ : yoneda.obj T₀ ⟶ A) (hτ₀ : τ₀ ≫ a = yoneda.map k) :
    ∃! τ : yoneda.obj T ⟶ A, τ ≫ a = 𝟙 _ ∧ yoneda.map k ≫ τ = τ₀ := by
  classical
  have hyT : IsAlgebraicSpace B S hS (yoneda.obj T) :=
    ((schemeSpaceFunctor B S hS).obj T).property
  have hth := isThickeningHom_yonedaSpace_map B S hS k hk
  have hmono : Mono (yoneda.map k) := hth.mono
  have hG : Space.IsThickening B S hS (⟨yoneda.obj T, hyT⟩ : AlgebraicSpaces B S hS)
      (Subfunctor.range (yoneda.map k)) := hth.2
  have hι : ∀ x : yoneda.obj T ⟶ A,
      Subfunctor.toRange (yoneda.map k) ≫ (Subfunctor.range (yoneda.map k)).ι ≫ x
        = yoneda.map k ≫ x := fun x ↦ by rw [← Category.assoc, Subfunctor.toRange_ι]
  obtain ⟨τ, ⟨hτ1, hτ2⟩, hτu⟩ :=
    Space.existsUnique_section_of_isThickening B S hS hyT hA hG ha
      (inv (Subfunctor.toRange (yoneda.map k)) ≫ τ₀) (by
        rw [Category.assoc, hτ₀, IsIso.inv_comp_eq]
        exact (Subfunctor.toRange_ι (yoneda.map k)).symm)
  refine ⟨τ, ⟨hτ1, ?_⟩, fun ρ ⟨hρa, hkρ⟩ ↦ hτu ρ ⟨hρa, ?_⟩⟩
  · rw [← hι, hτ2, IsIso.hom_inv_id_assoc]
  · rw [IsIso.eq_inv_comp, hι, hkρ]

/-- **A section of an étale morphism onto a scheme of the site, prescribed over a thickening
of that scheme, extends uniquely.** This is
`AlgebraicGeometry.Space.existsUnique_section_of_isThickening` read in the value universe of
the formal algebraic spaces, with the thickening given as a morphism of schemes of the site.

The target is written as `yoneda.obj T ⋙ uliftFunctor`, which is `uliftYoneda.obj T` unfolded;
the unfolded form is what makes the universe descent rewritable. -/
theorem existsUnique_section_uliftYoneda_of_isThickening
    {T₀ T : BigFppfOver B S hS} (k : T₀ ⟶ T)
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hP : Space.IsAlgebraicSpaceULift.{u + 1} B S hS P)
    (pr : P ⟶ yoneda.obj T ⋙ uliftFunctor.{u + 1})
    (hpr : Space.IsEtaleULift.{u + 1} B S hS pr)
    (σ₀ : yoneda.obj T₀ ⋙ uliftFunctor.{u + 1} ⟶ P)
    (hσ₀ : σ₀ ≫ pr = Functor.whiskerRight (yoneda.map k) uliftFunctor.{u + 1}) :
    ∃! σ : yoneda.obj T ⋙ uliftFunctor.{u + 1} ⟶ P,
      σ ≫ pr = 𝟙 _ ∧ Functor.whiskerRight (yoneda.map k) uliftFunctor.{u + 1} ≫ σ = σ₀ := by
  classical
  obtain ⟨A, hA, ⟨e⟩⟩ := Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hP
  have hLa := whiskerRight_preimage_liftFullyFaithful B S hS (e.hom ≫ pr)
  have hLτ₀ := whiskerRight_preimage_liftFullyFaithful B S hS (σ₀ ≫ e.inv)
  have hae := isEtale_preimage_of_isEtaleULift B S hS hA e pr hpr
  set a : A ⟶ yoneda.obj T := (liftFullyFaithful B S hS).preimage (e.hom ≫ pr) with ha_def
  set τ₀ : yoneda.obj T₀ ⟶ A := (liftFullyFaithful B S hS).preimage (σ₀ ≫ e.inv) with hτ₀_def
  have hτ₀a : τ₀ ≫ a = yoneda.map k := by
    apply eq_of_whiskerRight_eq B S hS
    rwa [Functor.whiskerRight_comp, hLa, hLτ₀, Category.assoc, Iso.inv_hom_id_assoc]
  obtain ⟨τ, ⟨hτ1, hkτ⟩, hτu⟩ :=
    existsUnique_section_yoneda_of_isThickening B S hS k hk hA hae τ₀ hτ₀a
  refine ⟨Functor.whiskerRight τ uliftFunctor.{u + 1} ≫ e.hom, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, ← hLa, ← Functor.whiskerRight_comp, hτ1]
    simp
  · rw [← Category.assoc, ← Functor.whiskerRight_comp, hkτ, hLτ₀, Category.assoc,
      e.inv_hom_id, Category.comp_id]
  · rintro σ ⟨hs1, hs2⟩
    have hLρ := whiskerRight_preimage_liftFullyFaithful B S hS (σ ≫ e.inv)
    set ρ : yoneda.obj T ⟶ A := (liftFullyFaithful B S hS).preimage (σ ≫ e.inv) with hρ_def
    have hρa : ρ ≫ a = 𝟙 _ := by
      apply eq_of_whiskerRight_eq B S hS
      rw [Functor.whiskerRight_comp, hLa, hLρ, Category.assoc, Iso.inv_hom_id_assoc, hs1]
      simp
    have hkρ : yoneda.map k ≫ ρ = τ₀ := by
      apply eq_of_whiskerRight_eq B S hS
      rw [Functor.whiskerRight_comp, hLρ, hLτ₀, ← Category.assoc, hs2]
    rw [← hτu ρ ⟨hρa, hkρ⟩, hLρ, Category.assoc, e.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.FormalSpace

end
