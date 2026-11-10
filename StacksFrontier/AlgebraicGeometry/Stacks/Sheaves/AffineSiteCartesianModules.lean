module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLift
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteFlatCovers
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianOfGlobalPresentation
public import StacksFrontier.CategoryTheory.Sites.Modules.CartesianLocalOnCover

/-!
# Cartesian modules on the affine site of a category fibred in groupoids

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `τ` be one of the five
topologies of Stacks 0H0A. On the associated affine site `𝒳_{affine, τ}`, whose structure
presheaf of rings sends `x` to the ring of global functions on the affine scheme it lies over, a
presheaf of modules is *cartesian* when all its base-change comparisons
`𝒪(x) ⊗_{𝒪(x')} 𝓕(x') ⟶ 𝓕(x)` are isomorphisms. This file proves the two halves of the
equivalence between being cartesian and being a quasi-coherent sheaf.

## Main results

* `AlgebraicGeometry.Stack.AffineCategory.isSheaf_of_cartesian`: **a cartesian presheaf of
  modules on `𝒳_{affine}` is a sheaf for each of the five topologies.** The coverings of
  `𝒳_{affine, τ}` are refined by finite flat coverings of affine schemes, along which a
  cartesian module satisfies the sheaf axiom by faithfully flat descent, Stacks 023M.
* `AlgebraicGeometry.Stack.AffineCategory.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`:
  **a quasi-coherent sheaf of modules on `𝒳_{affine, τ}` is cartesian.**

## Implementation notes

The proof that a quasi-coherent sheaf is cartesian runs in three steps. On a slice
`𝒳_{affine}/x` on which the module has a global presentation it is a cokernel of a map between
direct sums of the structure sheaf, and is cartesian there by
`Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_hasGlobalPresentation`. Over a flat
arrow `y ⟶ x` the condition descends from a finite flat covering of `x` on whose members the
module is globally presented, by `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_cover`.
An arbitrary arrow `f : y ⟶ x` of `𝒳_{affine}` need not be flat; the covering of `x` is pulled
back to a finite flat covering `y_k ⟶ y` of `y`, the module is cartesian over each composite
`y_k ⟶ y ⟶ x` because that composite also factors as `y_k ⟶ x_k ⟶ x` through a slice and a flat
arrow, and the condition descends along the faithfully flat ring map
`𝒪(y) ⟶ ∏ 𝒪(y_k)` by `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_faithfullyFlat`.

The structure presheaf is not fixed but passed as a presheaf `R` together with the hypothesis
`R = (toScheme B S hS p).op ⋙ Scheme.Γ`, so that a consumer whose structure sheaf arrives by
another route can use these statements after a single rewriting step.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GZV](https://stacks.math.columbia.edu/tag/0GZV)
* [Stacks Project, Tag 0H0E](https://stacks.math.columbia.edu/tag/0H0E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.PresheafOfModules

universe u v w m

/-- Flatness of morphisms of schemes, named as a `MorphismProperty` so that instance search finds
the stability instances of its precoverage. -/
private abbrev AlgebraicGeometry.flatMorphismsOfSchemes :
    MorphismProperty AlgebraicGeometry.Scheme.{u} :=
  @AlgebraicGeometry.Flat

namespace AlgebraicGeometry.Stack.AffineCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- The associated affine topology of Stacks 0H0A for the topology indexed by `τ`. -/
local notation "𝒥" τ => associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS τ)

/-! ### The rings of functions -/

section Rings

variable (R : (AffineCategory B S hS p)ᵒᵖ ⥤ CommRingCat.{u})
  (hR : R = (toScheme B S hS p).op ⋙ Scheme.Γ)
include hR

/-- The ring of functions is flat along an arrow whose underlying morphism of schemes is
flat. -/
theorem flat_map_of_flat {x y : AffineCategory B S hS p} (f : y ⟶ x)
    (hf : Flat ((toScheme B S hS p).map f)) : (R.map f.op).hom.Flat := by
  subst hR
  have := isAffine_toScheme_obj B S hS p x
  have := isAffine_toScheme_obj B S hS p y
  exact HasRingHomProperty.appTop (P := @Flat) ((toScheme B S hS p).map f) hf

/-- Along a finite family which is a flat covering of the underlying affine schemes, the product
of the ring maps is faithfully flat. -/
theorem faithfullyFlat_pi_map {x : AffineCategory B S hS p} (E : PreZeroHypercover.{m} x)
    (hfin : Finite E.I₀)
    (hE : (E.map (toScheme B S hS p)).presieve₀ ∈
      Scheme.precoverage @Flat ((toScheme B S hS p).obj x)) :
    (RingHom.pi (fun k => (R.map (E.f k).op).hom)).FaithfullyFlat := by
  subst hR
  have := isAffine_toScheme_obj B S hS p x
  have (k : E.I₀) := isAffine_toScheme_obj B S hS p (E.X k)
  obtain ⟨hcov, hfl⟩ := (Scheme.presieve₀_mem_precoverage_iff
    (E.map (toScheme B S hS p))).mp hE
  have _ (k : E.I₀) : Flat ((toScheme B S hS p).map (E.f k)) := hfl k
  exact Scheme.faithfullyFlat_pi_appTop (fun k => (toScheme B S hS p).obj (E.X k))
    (fun k => (toScheme B S hS p).map (E.f k)) hcov

/-- A fibre product square of the affine subcategory becomes a pushout square of rings. -/
theorem isPushout_map (hp : p.IsFiberedInGroupoids) {X Y Z P : AffineCategory B S hS p}
    {fst : P ⟶ X} {snd : P ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z} (h : IsPullback fst snd a b) :
    IsPushout (R.map a.op) (R.map b.op) (R.map fst.op) (R.map snd.op) := by
  subst hR
  have := preservesPullbacks_toScheme B S hS p hp
  change IsPushout ((toScheme B S hS p).map a).appTop ((toScheme B S hS p).map b).appTop
    ((toScheme B S hS p).map fst).appTop ((toScheme B S hS p).map snd).appTop
  exact isPushout_appTop_of_isPullback (Functor.map_isPullback (toScheme B S hS p) h)

/-- A fibre product square of a slice of the affine subcategory becomes a pushout square of the
restricted rings. -/
theorem isPushout_map_over (hp : p.IsFiberedInGroupoids) (x : AffineCategory B S hS p)
    {X Y Z P : Over x}
    {fst : P ⟶ X} {snd : P ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z} (h : IsPullback fst snd a b) :
    IsPushout (((Over.forget x).op ⋙ R).map a.op) (((Over.forget x).op ⋙ R).map b.op)
      (((Over.forget x).op ⋙ R).map fst.op) (((Over.forget x).op ⋙ R).map snd.op) :=
  have := hasPullbacks B S hS p hp
  isPushout_map B S hS p R hR hp (Functor.map_isPullback (Over.forget x) h)

end Rings

/-! ### A cartesian module is a sheaf -/

section Sheaf

variable (R : (AffineCategory B S hS p)ᵒᵖ ⥤ CommRingCat.{u})
  (hR : R = (toScheme B S hS p).op ⋙ Scheme.Γ)
include hR

/-- **A cartesian presheaf of modules on the affine subcategory is a sheaf** for each of the five
associated affine topologies of Stacks 0H0A. -/
theorem isSheaf_of_cartesian (hp : p.IsFiberedInGroupoids) (τ : SiteKind)
    (M : PresheafOfModules.{max m u} (R ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : (AffineCategory B S hS p)ᵒᵖ} (f : X ⟶ Y),
      IsIso (restrictionBaseChange.{v, w, u, m} M f)) :
    Presheaf.IsSheaf (𝒥 τ) M.presheaf := by
  have := hasPullbacks B S hS p hp
  have := preservesPullbacks_toScheme B S hS p hp
  refine isSheaf_of_cartesian_of_flat_refinements'.{u, v, u, m, w, u + 1}
    (toScheme B S hS p) R ?_ ?_ M hM (𝒥 τ) ?_
  · intro x E hfin hE
    exact faithfullyFlat_pi_map B S hS p R hR E hfin hE
  · intro _ _ _ _ _ _ _ _ h
    exact isPushout_map B S hS p R hR hp h
  · intro x T hT
    obtain ⟨E, hfin, hE, -, hle⟩ := exists_finite_flat_covering B S hS p hp τ T hT
    exact ⟨E, hfin, hE, hle⟩

/-- **A cartesian presheaf of modules on a slice of the affine subcategory is a sheaf** for the
localization of each of the five associated affine topologies. -/
theorem isSheaf_over_of_cartesian (hp : p.IsFiberedInGroupoids) (τ : SiteKind)
    (x : AffineCategory B S hS p)
    (M : PresheafOfModules.{max m u}
      ((Over.forget x).op ⋙ R ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : (Over x)ᵒᵖ} (f : X ⟶ Y),
      IsIso (restrictionBaseChange.{max v w, w, u, m} (R := (Over.forget x).op ⋙ R) M f)) :
    Presheaf.IsSheaf ((𝒥 τ).over x) M.presheaf := by
  have := hasPullbacks B S hS p hp
  have := preservesPullbacks_toScheme B S hS p hp
  have : PreservesLimitsOfShape WalkingCospan (Over.forget x ⋙ toScheme B S hS p) := by
    apply comp_preservesLimitsOfShape
  refine isSheaf_of_cartesian_of_flat_refinements'.{u, max v w, u, m, w, u + 1}
    (Over.forget x ⋙ toScheme B S hS p) ((Over.forget x).op ⋙ R) ?_ ?_ M hM _ ?_
  · intro V E hfin hE
    exact faithfullyFlat_pi_map B S hS p R hR (E.map (Over.forget x)) hfin hE
  · intro _ _ _ _ _ _ _ _ h
    exact isPushout_map_over B S hS p R hR hp x h
  · intro V T hT
    obtain ⟨E, hfin, hE, -, hle⟩ :=
      exists_finite_flat_covering B S hS p hp τ (Sieve.overEquiv V T) hT
    let E' : PreZeroHypercover.{u + 1} V :=
      { I₀ := E.I₀, X := fun i => Over.mk (E.f i ≫ V.hom),
        f := fun i => Over.homMk (E.f i) }
    refine ⟨E', hfin, hE, ?_⟩
    refine (Sieve.generate_le_iff _ _).mpr ?_
    rintro W f ⟨i⟩
    rw [← (Sieve.overEquiv V).symm_apply_apply T]
    exact hle _ (Sieve.le_generate E.presieve₀ _ _ (Presieve.ofArrows.mk i))

end Sheaf

/-! ### A quasi-coherent sheaf of modules is cartesian -/

section Cartesian

variable (R : (AffineCategory B S hS p)ᵒᵖ ⥤ CommRingCat.{u})
  (hR : R = (toScheme B S hS p).op ⋙ Scheme.Γ)
include hR

/-- **A quasi-coherent sheaf of modules on `𝒳_{affine, τ}` is cartesian, at a module universe
containing the site.** See `isIso_restrictionBaseChange_of_isQuasicoherentOnSite` for the
statement at an arbitrary module universe. -/
theorem isIso_restrictionBaseChange_of_isQuasicoherentOnSite_large
    (hp : p.IsFiberedInGroupoids) (τ : SiteKind)
    (hRs : Presheaf.IsSheaf (𝒥 τ) (R ⋙ forget₂ CommRingCat RingCat))
    (N : SheafOfModules.{max m u v w}
      (⟨R ⋙ forget₂ CommRingCat RingCat, hRs⟩ : Sheaf (𝒥 τ) RingCat.{u}))
    (hN : N.IsQuasicoherentOnSite)
    {X Y : (AffineCategory B S hS p)ᵒᵖ} (f : X ⟶ Y) :
    IsIso (restrictionBaseChange.{v, w, u, max m v w} N.val f) := by
  classical
  have := hasPullbacks B S hS p hp
  have := preservesPullbacks_toScheme B S hS p hp
  -- the module is cartesian over every arrow of a slice on which it has a global presentation
  have hcart : ∀ (W : AffineCategory B S hS p), (N.over W).HasGlobalPresentation →
      ∀ {A A' : AffineCategory B S hS p} (a : A ⟶ W) (a' : A' ⟶ W) (b : A ⟶ A'), b ≫ a' = a →
        IsIso (restrictionBaseChange.{v, w, u, max m v w} N.val b.op) := by
    intro W hW A A' a a' b hb
    exact isIso_restrictionBaseChange_of_hasGlobalPresentation.{max v w, w, u, m}
      ((Over.forget W).op ⋙ R)
      (Sheaf.over (⟨R ⋙ forget₂ CommRingCat RingCat, hRs⟩ : Sheaf (𝒥 τ) RingCat.{u}) W).property
      (fun M' hM' => isSheaf_over_of_cartesian.{u, v, w, max m v w} B S hS p R hR hp τ W M' hM')
      (N.over W) hW
      (Quiver.Hom.op (Over.homMk (U := Over.mk a) (V := Over.mk a') b hb))
  -- every object has a finite flat covering on whose members the module is globally presented
  have hcov : ∀ V : AffineCategory B S hS p, ∃ E : PreZeroHypercover.{u + 1} V, Finite E.I₀ ∧
      (E.map (toScheme B S hS p)).presieve₀ ∈
        Scheme.precoverage @Flat ((toScheme B S hS p).obj V) ∧
      E.sieve₀ ∈ (𝒥 τ) V ∧ ∀ k, (N.over (E.X k)).HasGlobalPresentation := by
    intro V
    obtain ⟨I, Vs, fs, hcover, hpres⟩ := hN.locally_hasGlobalPresentation V
    obtain ⟨E, hfin, hE, hEcov, hle⟩ := exists_finite_flat_covering B S hS p hp τ _ hcover
    refine ⟨E, hfin, hE, hEcov, fun k => ?_⟩
    obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp (hle _ (Sieve.ofArrows_mk _ _ k))
    exact Stacks.SheafOfModules.hasGlobalPresentation_overMap N a (hpres i)
  -- the sheaf condition on the underlying presheaf of sets
  have hsT : Presieve.IsSheaf (𝒥 τ) (N.val.presheaf ⋙ forget AddCommGrpCat) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact (Presheaf.isSheaf_iff_isSheaf_comp (𝒥 τ) N.val.presheaf
      (forget AddCommGrpCat)).mp N.isSheaf
  -- the module is cartesian over every arrow which is flat on the underlying schemes
  have hflat : ∀ {U V : AffineCategory B S hS p} (g : U ⟶ V),
      Flat ((toScheme B S hS p).map g) →
        IsIso (restrictionBaseChange.{v, w, u, max m v w} N.val g.op) := by
    intro U V g hg
    obtain ⟨E, hfin, -, hEcov, hpres⟩ := hcov V
    have hcoverU : Sieve.ofArrows (fun i => pullback g (E.f i))
        (fun i => pullback.fst g (E.f i)) ∈ (𝒥 τ) U := by
      refine GrothendieckTopology.superset_covering _ ?_
        (GrothendieckTopology.pullback_stable _ g hEcov)
      rintro Z h ⟨Y', g₁, g₂, ⟨i⟩, hgg⟩
      have hmem := (Sieve.ofArrows (fun i => pullback g (E.f i))
          (fun i => pullback.fst g (E.f i))).downward_closed
        (Sieve.ofArrows_mk (fun i => pullback g (E.f i)) (fun i => pullback.fst g (E.f i)) i)
        (pullback.lift h g₁ hgg.symm)
      rwa [pullback.lift_fst] at hmem
    have hsfV : Presieve.IsSheafFor (N.val.presheaf ⋙ forget AddCommGrpCat)
        (Presieve.ofArrows E.X E.f) :=
      (Presieve.isSheafFor_iff_generate _).mpr (hsT _ hEcov)
    have hsfU : Presieve.IsSheafFor (N.val.presheaf ⋙ forget AddCommGrpCat)
        (Presieve.ofArrows (fun i => pullback g (E.f i)) (fun i => pullback.fst g (E.f i))) :=
      (Presieve.isSheafFor_iff_generate _).mpr (hsT _ hcoverU)
    exact isIso_restrictionBaseChange_of_cover N.val g E.X E.f
      (flat_map_of_flat B S hS p R hR g hg) hsfV hsfU
      (fun i => isPushout_map B S hS p R hR hp (IsPullback.of_hasPullback g (E.f i)))
      (fun c => isPushout_map B S hS p R hR hp (IsPullback.of_hasPullback g _))
      (fun i => hcart _ (hpres i) (pullback.snd g (E.f i)) (𝟙 _) (pullback.snd g (E.f i)) (by simp))
      (fun c => hcart _ (hpres c.1) (pullback.snd g (pullback.fst (E.f c.1) (E.f c.2) ≫ E.f c.1) ≫
        pullback.fst (E.f c.1) (E.f c.2)) (pullback.fst (E.f c.1) (E.f c.2))
        (pullback.snd g (pullback.fst (E.f c.1) (E.f c.2) ≫ E.f c.1)) rfl)
  -- an arbitrary arrow: descend along the pulled back covering, which is faithfully flat
  obtain ⟨E, hfin, hE, -, hpres⟩ := hcov X.unop
  let g : Y.unop ⟶ X.unop := f.unop
  let K := (Scheme.precoverage @Flat).comap (toScheme B S hS p)
  have : K.IsStableUnderBaseChange := inferInstanceAs (Precoverage.IsStableUnderBaseChange
    ((Scheme.precoverage flatMorphismsOfSchemes.{u}).comap (toScheme B S hS p)))
  have he : E.presieve₀ ∈ K X.unop := by
    change E.presieve₀.map (toScheme B S hS p) ∈ Scheme.precoverage @Flat _
    rwa [← PreZeroHypercover.presieve₀_map]
  have he' : (E.pullback₂ g).presieve₀ ∈ K Y.unop :=
    K.mem_coverings_of_isPullback _ he _ _ _
      (fun i => (IsPullback.of_hasPullback (E.f i) g).flip)
  have he'' : ((E.pullback₂ g).map (toScheme B S hS p)).presieve₀ ∈
      Scheme.precoverage @Flat ((toScheme B S hS p).obj Y.unop) := by
    rw [PreZeroHypercover.presieve₀_map]
    exact he'
  obtain ⟨-, hfl⟩ := (Scheme.presieve₀_mem_precoverage_iff _).mp he''
  have hff := faithfullyFlat_pi_map B S hS p R hR (E.pullback₂ g) hfin he''
  refine isIso_restrictionBaseChange_of_faithfullyFlat N.val f
    (fun k => op (pullback (E.f k) g)) (fun k => (pullback.snd (E.f k) g).op) hff
    (fun k => hflat _ (hfl k)) (fun k => ?_)
  have hcomp : f ≫ (pullback.snd (E.f k) g).op =
      (E.f k).op ≫ (pullback.fst (E.f k) g).op := by
    change g.op ≫ _ = _
    rw [← op_comp, ← op_comp, pullback.condition]
  rw [hcomp]
  refine isIso_restrictionBaseChange_comp N.val _ _ (hflat _ ?_) ?_
  · obtain ⟨-, hfl'⟩ := (Scheme.presieve₀_mem_precoverage_iff _).mp hE
    exact hfl' k
  · exact hcart _ (hpres k) (pullback.fst (E.f k) g) (𝟙 _) _ (by simp)

/-- **A quasi-coherent sheaf of modules on `𝒳_{affine, τ}` is cartesian**: for every arrow
`x ⟶ x'` of `𝒳_{affine}` the base-change comparison `𝒪(x) ⊗_{𝒪(x')} 𝓕(x') ⟶ 𝓕(x)` is an
isomorphism. The sections are first raised to a universe containing the site, where global
presentations live, and bijectivity of the comparison descends back. -/
theorem isIso_restrictionBaseChange_of_isQuasicoherentOnSite
    (hp : p.IsFiberedInGroupoids) (τ : SiteKind)
    (hRs : Presheaf.IsSheaf (𝒥 τ) (R ⋙ forget₂ CommRingCat RingCat))
    (F : SheafOfModules.{u}
      (⟨R ⋙ forget₂ CommRingCat RingCat, hRs⟩ : Sheaf (𝒥 τ) RingCat.{u}))
    (hF : F.IsQuasicoherentOnSite)
    {X Y : (AffineCategory B S hS p)ᵒᵖ} (f : X ⟶ Y) :
    IsIso (restrictionBaseChange.{v, w, u, u} F.val f) := by
  have h := isIso_restrictionBaseChange_of_isQuasicoherentOnSite_large.{u, v, w, u}
    B S hS p R hR hp τ hRs
    (SheafOfModules.uliftForPresentation.{v, w, u, u, max v w u} F)
    (SheafOfModules.isQuasicoherentOnSite_uliftForPresentation hF) f
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_restrictionBaseChange_of_uliftForPresentation.{v, w, u, u, max v w u}
    R hRs F f h

end Cartesian

end AlgebraicGeometry.Stack.AffineCategory

end
