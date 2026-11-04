module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianComposition
public import StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteCartesianSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianOfGlobalPresentation
public import StacksFrontier.CategoryTheory.Sites.Modules.CartesianCancellation
public import StacksFrontier.CategoryTheory.Sites.Modules.CartesianLocalOnCover

/-!
# A quasi-coherent module on a site of affine schemes with flat coverings is cartesian

Let `C` be a category with pullbacks carrying a functor `L : C ⥤ Scheme` with affine values which
preserves fibre products, and a precoverage all of whose covering families are finite and flat on
the underlying schemes, with the presheaf of global regular functions of `L` as structure sheaf.
A quasi-coherent sheaf of modules on that ringed site is **cartesian**: every base-change
comparison `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` is an isomorphism.

This is the converse of Stacks 0GZV, conditions (2)–(6) back to condition (1), and the five big
affine sites `(Aff/S)_τ` of that lemma are the five instances recorded at the end of the file.
Together with `StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteCartesianSheaf` and
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines`, which prove the two
conjuncts of each of (2)–(6) from condition (1), this makes **condition (1) equivalent to each of
conditions (2)–(6)**.

The argument is Stacks 0H04, run with the flatness hypothesis of its descent step discharged in a
different way. The step `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_cover` requires
the ring map of the morphism being descended along to be flat; on a small Zariski or étale site
every morphism is, while on `(Aff/S)_τ` the morphisms are arbitrary morphisms of affine schemes
over `S`. So that step is used only for the *flat* morphisms, which is enough because the
covering morphisms are flat, and the general case is then obtained by reflecting along a
faithfully flat base change with
`Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_faithfullyFlat_family`: on a covering
`T i ⟶ U` of the source, pulled back from a covering of the target on whose slices the module has
a global presentation, the module is cartesian over `T i ⟶ U` (a flat morphism) and over
`T i ⟶ U ⟶ V` (the composite of a slice morphism and a covering morphism), and that reflects
cartesianness over the given morphism.

## Main results

* `Stacks.PresheafOfModules.isPushout_schemeGamma_over` and
  `Stacks.PresheafOfModules.isSheaf_of_cartesian_schemeGamma_over`: the slice versions of the two
  facts about the structure presheaf that flat descent uses.
* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_over_of_hasGlobalPresentation`: a global
  presentation on a slice makes the module cartesian there.
* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_schemeGamma_of_cover`: being cartesian
  over a morphism with flat ring map is local on a covering of its target.
* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_isQuasicoherentOnSite_flat`: **a
  quasi-coherent module is cartesian over every morphism with flat ring map.**
* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`: **a
  quasi-coherent module is cartesian over every morphism.**
* `AlgebraicGeometry.bigAffineFppf_isIso_canonicalMap_of_isQuasicoherentOnSite` and its Zariski,
  étale, smooth and syntomic counterparts: Stacks 0GZV, each of conditions (2)–(6) implies
  condition (1).
* `AlgebraicGeometry.bigAffineFppf_isQuasicoherentOnSite_iff_canonicalMap_isIso` and its four
  counterparts: **Stacks 0GZV, condition (1) is equivalent to each of conditions (2)–(6)**, for a
  sheaf of modules, the sheaf conjunct of (2)–(6) being carried by the type.

## Implementation notes

The covering used for the reflection step is produced by
`Stacks.Sites.exists_finite_flat_refinement`, which refines a covering sieve of the generated
topology by a finite family that is a flat covering of the schemes; the global presentations
survive the refinement because a global presentation on a slice restricts along a morphism of the
site, `Stacks.SheafOfModules.hasGlobalPresentation_overMap`. That refinement does *not* record
membership in the precoverage, and it does not have to: the reflection step needs the family only
for its faithful flatness, the sheaf conditions being used inside the flat case, which takes its
covering from `Stacks.SheafOfModules.exists_finite_globalPresentation_cover` instead.

## References

* [Stacks Project, Tag 0GZV](https://stacks.math.columbia.edu/tag/0GZV)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u m

/-- Flatness of morphisms of schemes, named as a `MorphismProperty` so that the stability
instances of its precoverage can be located by instance search. -/
private abbrev flatPropertyOfAffineSite :
    MorphismProperty AlgebraicGeometry.Scheme.{u} :=
  @AlgebraicGeometry.Flat

namespace Stacks.PresheafOfModules

open AlgebraicGeometry

variable {C : Type (u + 1)} [Category.{u} C] [HasPullbacks C]
    (L : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan L] [∀ X, IsAffine (L.obj X)]

omit [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan L] in
/-- The restriction map of the structure presheaf along a morphism with flat underlying morphism
of schemes is flat. -/
theorem flat_schemeGamma_map {X Y : C} (a : X ⟶ Y) (ha : Flat (L.map a)) :
    ((L.op ⋙ Scheme.Γ).map a.op).hom.Flat :=
  HasRingHomProperty.appTop (P := @Flat) (L.map a) ha

omit [HasPullbacks C] in
/-- A fibre product square of a slice of the site becomes a pushout square of the restricted
structure presheaf. -/
theorem isPushout_schemeGamma_over (U : C) {X Y Z W : Over U}
    {fst : W ⟶ X} {snd : W ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z} (h : IsPullback fst snd a b) :
    IsPushout (((Over.forget U).op ⋙ L.op ⋙ Scheme.Γ).map a.op)
      (((Over.forget U).op ⋙ L.op ⋙ Scheme.Γ).map b.op)
      (((Over.forget U).op ⋙ L.op ⋙ Scheme.Γ).map fst.op)
      (((Over.forget U).op ⋙ L.op ⋙ Scheme.Γ).map snd.op) := by
  have _ : PreservesLimitsOfShape WalkingCospan (Over.forget U ⋙ L) := by
    apply comp_preservesLimitsOfShape
  have _ : ∀ T : Over U, IsAffine ((Over.forget U ⋙ L).obj T) := fun T =>
    inferInstanceAs (IsAffine (L.obj T.left))
  exact isPushout_schemeGamma (Over.forget U ⋙ L) h

/-- **A cartesian presheaf of modules over the structure presheaf of a slice of the site is a
sheaf**, for a topology generated by finite flat covering families. -/
theorem isSheaf_of_cartesian_schemeGamma_over (P : Precoverage C)
    (hP : ∀ {U : C} (S : Presieve U), S ∈ P U →
      S.uncurry.Finite ∧ S.map L ∈ Scheme.precoverage @Flat (L.obj U))
    (U : C)
    (M : PresheafOfModules.{max m (u + 1)}
      (((Over.forget U).op ⋙ L.op ⋙ Scheme.Γ) ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y),
      IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)}
        (R := (Over.forget U).op ⋙ L.op ⋙ Scheme.Γ) M f)) :
    Presheaf.IsSheaf (P.toGrothendieck.over U) M.presheaf := by
  have _ : PreservesLimitsOfShape WalkingCospan (Over.forget U ⋙ L) := by
    apply comp_preservesLimitsOfShape
  have _ : ∀ T : Over U, IsAffine ((Over.forget U ⋙ L).obj T) := fun T =>
    inferInstanceAs (IsAffine (L.obj T.left))
  exact isSheaf_of_cartesian_of_flat_refinements.{u, u + 1, u, m, u}
    (Over.forget U ⋙ L) ((Over.forget U).op ⋙ L.op ⋙ Scheme.Γ)
    (fun E _ hE => faithfullyFlat_pi_schemeGamma (Over.forget U ⋙ L) E hE)
    (fun h => isPushout_schemeGamma_over L U h) M hM _
    (fun S hS => Stacks.Sites.exists_finite_flat_refinement_over L P hP U S hS)

/-- **A global presentation on a slice makes the module cartesian there.** -/
theorem isIso_restrictionBaseChange_over_of_hasGlobalPresentation (P : Precoverage C)
    (hP : ∀ {U : C} (S : Presieve U), S ∈ P U →
      S.uncurry.Finite ∧ S.map L ∈ Scheme.precoverage @Flat (L.obj U))
    (hRing : Presheaf.IsSheaf P.toGrothendieck
      ((L.op ⋙ Scheme.Γ) ⋙ forget₂ CommRingCat RingCat))
    (M : SheafOfModules.{max m (u + 1)}
      (⟨(L.op ⋙ Scheme.Γ) ⋙ forget₂ CommRingCat RingCat, hRing⟩ :
        Sheaf P.toGrothendieck RingCat.{u}))
    (U : C) (hM : (M.over U).HasGlobalPresentation) {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)}
      (R := (Over.forget U).op ⋙ L.op ⋙ Scheme.Γ) (M.over U).val f) :=
  isIso_restrictionBaseChange_of_hasGlobalPresentation.{u + 1, u, u, m}
    ((Over.forget U).op ⋙ L.op ⋙ Scheme.Γ)
    (Sheaf.over (⟨(L.op ⋙ Scheme.Γ) ⋙ forget₂ CommRingCat RingCat, hRing⟩ :
      Sheaf P.toGrothendieck RingCat.{u}) U).property
    (fun N hN => isSheaf_of_cartesian_schemeGamma_over L P hP U N hN)
    (M.over U) hM f

/-- **Being cartesian over a morphism with flat ring map is local on a covering of its
target.** -/
theorem isIso_restrictionBaseChange_schemeGamma_of_cover (P : Precoverage C)
    (_hP : ∀ {U : C} (S : Presieve U), S ∈ P U →
      S.uncurry.Finite ∧ S.map L ∈ Scheme.precoverage @Flat (L.obj U))
    (M : PresheafOfModules.{max m (u + 1)} ((L.op ⋙ Scheme.Γ) ⋙ forget₂ CommRingCat RingCat))
    (hs : Presheaf.IsSheaf P.toGrothendieck M.presheaf)
    {V : C} {I : Type (u + 1)} [Finite I] (W : I → C) (gw : ∀ i, W i ⟶ V)
    (hcover : Sieve.ofArrows W gw ∈ P.toGrothendieck V)
    (hcart : ∀ (i : I) {X Y : C} (x : X ⟶ W i) (y : Y ⟶ W i) (a : X ⟶ Y), a ≫ y = x →
      IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)} M a.op))
    {U : C} (f : U ⟶ V) (hflat : ((L.op ⋙ Scheme.Γ).map f.op).hom.Flat) :
    IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)} M f.op) := by
  classical
  have hsT : Presieve.IsSheaf P.toGrothendieck (M.presheaf ⋙ forget AddCommGrpCat) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact (Presheaf.isSheaf_iff_isSheaf_comp P.toGrothendieck M.presheaf
      (forget AddCommGrpCat)).mp hs
  have hcoverU : Sieve.ofArrows (fun i => pullback f (gw i))
      (fun i => pullback.fst f (gw i)) ∈ P.toGrothendieck U := by
    refine P.toGrothendieck.superset_covering ?_ (P.toGrothendieck.pullback_stable f hcover)
    rintro Z h ⟨Y, g₁, g₂, ⟨i⟩, hg⟩
    have hmem := (Sieve.ofArrows (fun i => pullback f (gw i))
        (fun i => pullback.fst f (gw i))).downward_closed
      (Sieve.ofArrows_mk (fun i => pullback f (gw i)) (fun i => pullback.fst f (gw i)) i)
      (pullback.lift h g₁ hg.symm)
    rwa [pullback.lift_fst] at hmem
  have hsfV : Presieve.IsSheafFor (M.presheaf ⋙ forget AddCommGrpCat)
      (Presieve.ofArrows W gw) :=
    (Presieve.isSheafFor_iff_generate _).mpr (hsT _ hcover)
  have hsfU : Presieve.IsSheafFor (M.presheaf ⋙ forget AddCommGrpCat)
      (Presieve.ofArrows (fun i => pullback f (gw i)) (fun i => pullback.fst f (gw i))) :=
    (Presieve.isSheafFor_iff_generate _).mpr (hsT _ hcoverU)
  exact isIso_restrictionBaseChange_of_cover M f W gw hflat hsfV hsfU
    (fun i => isPushout_schemeGamma L (IsPullback.of_hasPullback f (gw i)))
    (fun c => isPushout_schemeGamma L (IsPullback.of_hasPullback f _))
    (fun i => hcart i (pullback.snd f (gw i)) (𝟙 _) (pullback.snd f (gw i)) (by simp))
    (fun c => hcart c.1 (pullback.snd f (pullback.fst (gw c.1) (gw c.2) ≫ gw c.1) ≫
      pullback.fst (gw c.1) (gw c.2)) (pullback.fst (gw c.1) (gw c.2))
      (pullback.snd f (pullback.fst (gw c.1) (gw c.2) ≫ gw c.1)) rfl)

/-- **A quasi-coherent module on a site of affine schemes with flat coverings is cartesian over
every morphism whose ring map is flat.**  This is Stacks 0H04 verbatim. -/
theorem isIso_restrictionBaseChange_of_isQuasicoherentOnSite_flat (P : Precoverage C)
    (hP : ∀ {U : C} (S : Presieve U), S ∈ P U →
      S.uncurry.Finite ∧ S.map L ∈ Scheme.precoverage @Flat (L.obj U))
    (hRing : Presheaf.IsSheaf P.toGrothendieck
      ((L.op ⋙ Scheme.Γ) ⋙ forget₂ CommRingCat RingCat))
    (M : SheafOfModules.{max m (u + 1)}
      (⟨(L.op ⋙ Scheme.Γ) ⋙ forget₂ CommRingCat RingCat, hRing⟩ :
        Sheaf P.toGrothendieck RingCat.{u}))
    (hM : M.IsQuasicoherentOnSite) {U V : C} (f : U ⟶ V)
    (hflat : ((L.op ⋙ Scheme.Γ).map f.op).hom.Flat) :
    IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)} M.val f.op) := by
  classical
  obtain ⟨I, hI, W, g, hcover, hpres⟩ :=
    Stacks.SheafOfModules.exists_finite_globalPresentation_cover.{u + 1, u, u, m}
      P (fun S hS => (hP S hS).1) M hM V
  have _ := hI
  exact isIso_restrictionBaseChange_schemeGamma_of_cover L P hP M.val M.isSheaf W g hcover
    (fun i _ _ x y a ha => isIso_restrictionBaseChange_over_of_hasGlobalPresentation L P hP hRing
      M (W i) (hpres i) (Quiver.Hom.op (Over.homMk (U := Over.mk x) (V := Over.mk y) a ha)))
    f hflat

/-- **A quasi-coherent module on a site of affine schemes with flat coverings is cartesian.**

The morphism `f : U ⟶ V` is arbitrary.  A finite flat covering `W i ⟶ V` on whose slices the
module has a global presentation is pulled back to a covering `T i ⟶ U`; the module is cartesian
over `T i ⟶ U`, a flat morphism, and over the composite `T i ⟶ U ⟶ V`, which factors as the
slice morphism `T i ⟶ W i` followed by the covering morphism `W i ⟶ V`.  Faithful flatness of
the `𝒪(T i)` over `𝒪(U)` then reflects cartesianness over `f`. -/
theorem isIso_restrictionBaseChange_of_isQuasicoherentOnSite (P : Precoverage C)
    (hP : ∀ {U : C} (S : Presieve U), S ∈ P U →
      S.uncurry.Finite ∧ S.map L ∈ Scheme.precoverage @Flat (L.obj U))
    (hRing : Presheaf.IsSheaf P.toGrothendieck
      ((L.op ⋙ Scheme.Γ) ⋙ forget₂ CommRingCat RingCat))
    (M : SheafOfModules.{max m (u + 1)}
      (⟨(L.op ⋙ Scheme.Γ) ⋙ forget₂ CommRingCat RingCat, hRing⟩ :
        Sheaf P.toGrothendieck RingCat.{u}))
    (hM : M.IsQuasicoherentOnSite) {U V : C} (f : U ⟶ V) :
    IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)} M.val f.op) := by
  classical
  -- a finite flat covering of `V` on whose slices `M` has a global presentation
  obtain ⟨I, W, g, hcover, hpres⟩ := hM.locally_hasGlobalPresentation V
  obtain ⟨E, hfin, hEflat, hES⟩ := Stacks.Sites.exists_finite_flat_refinement L P hP
    (Sieve.ofArrows W g) hcover
  have _ := hfin
  have hEpres : ∀ i, ((M.over (E.X i)).HasGlobalPresentation) := by
    intro i
    obtain ⟨Z, a, b, ⟨j⟩, hab⟩ :=
      hES _ (Sieve.le_generate E.presieve₀ _ _ (Presieve.ofArrows.mk i))
    exact Stacks.SheafOfModules.hasGlobalPresentation_overMap.{u + 1, u, u, max m (u + 1)}
      M a (hpres j)
  -- the members of `E` are flat, and so are their base changes to `U`
  obtain ⟨hEsurj, hEflat'⟩ := (Scheme.presieve₀_mem_precoverage_iff (E.map L)).mp hEflat
  -- `M` is cartesian over the flat morphisms
  have hflatCart : ∀ {X Y : C} (a : X ⟶ Y), ((L.op ⋙ Scheme.Γ).map a.op).hom.Flat →
      IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)} M.val a.op) :=
    isIso_restrictionBaseChange_of_isQuasicoherentOnSite_flat L P hP hRing M hM
  -- cartesian over the base-changed covering, and over its composites with `f`
  have hc : ∀ i, IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)} M.val
      (pullback.snd (E.f i) f ≫ f).op) := by
    intro i
    rw [← pullback.condition]
    exact isIso_restrictionBaseChange_comp M.val (E.f i).op (pullback.fst (E.f i) f).op
      (hflatCart _ (flat_schemeGamma_map L (E.f i) (hEflat' i)))
      (isIso_restrictionBaseChange_over_of_hasGlobalPresentation L P hP hRing M (E.X i)
        (hEpres i) (Quiver.Hom.op (Over.homMk (U := Over.mk (pullback.fst (E.f i) f))
          (V := Over.mk (𝟙 (E.X i))) (pullback.fst (E.f i) f) (by simp))))
  -- faithful flatness of the base-changed covering
  have hff : (RingHom.pi (fun i =>
      ((L.op ⋙ Scheme.Γ).map (pullback.snd (E.f i) f).op).hom)).FaithfullyFlat := by
    let K := (Scheme.precoverage @Flat).comap L
    have _ : K.IsStableUnderBaseChange :=
      inferInstanceAs (Precoverage.IsStableUnderBaseChange
        ((Scheme.precoverage flatPropertyOfAffineSite.{u}).comap L))
    have he : E.presieve₀ ∈ K V := by
      simpa only [K, Precoverage.mem_comap_iff, PreZeroHypercover.presieve₀_map] using hEflat
    have he' : (E.pullback₂ f).presieve₀ ∈ K U :=
      K.mem_coverings_of_isPullback _ he _ _ _
        (fun i => (IsPullback.of_hasPullback (E.f i) f).flip)
    have _ : Finite (E.pullback₂ f).I₀ := hfin
    exact faithfullyFlat_pi_schemeGamma L (E.pullback₂ f)
      (by simpa only [K, Precoverage.mem_comap_iff, PreZeroHypercover.presieve₀_map] using he')
  exact isIso_restrictionBaseChange_of_faithfullyFlat_family M.val f
    (fun i => pullback (E.f i) f) (fun i => pullback.snd (E.f i) f) hff
    (fun i => hflatCart _ (flat_schemeGamma_map L _ (MorphismProperty.of_isPullback
      (Functor.map_isPullback L (IsPullback.of_hasPullback (E.f i) f)) (hEflat' i)))) hc

end Stacks.PresheafOfModules

namespace AlgebraicGeometry

open Stacks.PresheafOfModules

/-! ### The five big affine sites of Stacks 0GZV -/

/-- **Stacks 0GZV, condition (6) implies condition (1).** A sheaf of `𝒪_Aff`-modules on
`(Aff/S)_fppf` which is quasi-coherent on the ringed site `((Aff/S)_fppf, 𝒪_Aff)` has all its
base-change maps `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` isomorphisms. -/
@[stacks 0GZV "(6) ⇒ (1), from the quasi-coherence conjunct of (6)"]
theorem bigAffineFppf_isIso_canonicalMap_of_isQuasicoherentOnSite
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineFppfRingedSite B S hS).O))
    (hM : M.IsQuasicoherentOnSite) {U V : BigAffineFppf B S hS} (f : U ⟶ V) :
    IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineFppfRingedSite B S hS) M f) := by
  have h2 := SheafOfModules.isQuasicoherentOnSite_uliftForPresentation hM
  have h3 := isIso_restrictionBaseChange_of_isQuasicoherentOnSite.{u, u}
    (BigAffineFppf.toScheme B S hS) (BigAffineFppf.precoverage B S hS)
    (bigAffineFppf_covering_finite_flat B S hS) _ _ h2 f
  have h4 := bijective_restrictionBaseChange_of_uliftForPresentation
    (bigAffineFppfRingedSite B S hS).O.obj _ M f.op h3
  exact (ConcreteCategory.isIso_iff_bijective _).mpr h4

/-- A finite family whose image under `L` is a flat covering of schemes is a finite covering
presieve with flat image. -/
private theorem uncurry_finite_and_map_mem_flat {D : Type*} [Category D] (L : D ⥤ Scheme.{u})
    {U : D} (E : PreZeroHypercover.{u + 1} U) (hfin : Finite E.I₀)
    (hflat : (E.map L).presieve₀ ∈ Scheme.precoverage @Flat (L.obj U)) :
    E.presieve₀.uncurry.Finite ∧ E.presieve₀.map L ∈ Scheme.precoverage @Flat (L.obj U) :=
  ⟨Precoverage.ofArrows_mem_finite _ _, by rwa [← PreZeroHypercover.presieve₀_map]⟩

/-- A covering presieve of the big affine Zariski site is finite, and its image under
`BigAffineZariski.toScheme` is a covering for the flat precoverage of schemes. -/
theorem bigAffineZariski_covering_finite_flat (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {U : BigAffineZariski B S hS} (P : Presieve U)
    (hP : P ∈ BigAffineZariski.precoverage B S hS U) :
    P.uncurry.Finite ∧ P.map (BigAffineZariski.toScheme B S hS) ∈
      Scheme.precoverage @Flat ((BigAffineZariski.toScheme B S hS).obj U) := by
  obtain ⟨E, rfl, hE⟩ := hP
  obtain ⟨hfin, hflat⟩ := bigAffineZariski_covering_flat B S hS E hE
  exact uncurry_finite_and_map_mem_flat _ E hfin hflat

/-- A covering presieve of the big affine étale site is finite, and its image under
`BigAffineEtale.toScheme` is a covering for the flat precoverage of schemes. -/
theorem bigAffineEtale_covering_finite_flat (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {U : BigAffineEtale B S hS} (P : Presieve U)
    (hP : P ∈ BigAffineEtale.precoverage B S hS U) :
    P.uncurry.Finite ∧ P.map (BigAffineEtale.toScheme B S hS) ∈
      Scheme.precoverage @Flat ((BigAffineEtale.toScheme B S hS).obj U) := by
  obtain ⟨E, rfl, hE⟩ := hP
  obtain ⟨hfin, hflat⟩ := bigAffineEtale_covering_flat B S hS E hE
  exact uncurry_finite_and_map_mem_flat _ E hfin hflat

/-- A covering presieve of the big affine smooth site is finite, and its image under
`BigAffineSmooth.toScheme` is a covering for the flat precoverage of schemes. -/
theorem bigAffineSmooth_covering_finite_flat (B : BigSmoothSite.{u}) (S : Scheme.{u})
    (hS : S.size < B.cutoff) {U : BigAffineSmooth B S hS} (P : Presieve U)
    (hP : P ∈ BigAffineSmooth.precoverage B S hS U) :
    P.uncurry.Finite ∧ P.map (BigAffineSmooth.toScheme B S hS) ∈
      Scheme.precoverage @Flat ((BigAffineSmooth.toScheme B S hS).obj U) := by
  obtain ⟨E, rfl, hE⟩ := hP
  obtain ⟨hfin, hflat⟩ := bigAffineSmooth_covering_flat B S hS E hE
  exact uncurry_finite_and_map_mem_flat _ E hfin hflat

/-- A covering presieve of the big affine syntomic site is finite, and its image under
`BigAffineSyntomic.toScheme` is a covering for the flat precoverage of schemes. -/
theorem bigAffineSyntomic_covering_finite_flat (B : BigSyntomicSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {U : BigAffineSyntomic B S hS} (P : Presieve U)
    (hP : P ∈ BigAffineSyntomic.precoverage B S hS U) :
    P.uncurry.Finite ∧ P.map (BigAffineSyntomic.toScheme B S hS) ∈
      Scheme.precoverage @Flat ((BigAffineSyntomic.toScheme B S hS).obj U) := by
  obtain ⟨E, rfl, hE⟩ := hP
  obtain ⟨hfin, hflat⟩ := bigAffineSyntomic_covering_flat B S hS E hE
  exact uncurry_finite_and_map_mem_flat _ E hfin hflat

/-- **Stacks 0GZV, condition (2) implies condition (1).** A sheaf of `𝒪_Aff`-modules on
`(Aff/S)_Zar` which is quasi-coherent on the ringed site `((Aff/S)_Zar, 𝒪_Aff)` has all its
base-change maps `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` isomorphisms. -/
@[stacks 0GZV "(2) ⇒ (1), from the quasi-coherence conjunct of (2)"]
theorem bigAffineZariski_isIso_canonicalMap_of_isQuasicoherentOnSite
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineZariskiRingedSite B S hS).O))
    (hM : M.IsQuasicoherentOnSite) {U V : BigAffineZariski B S hS} (f : U ⟶ V) :
    IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineZariskiRingedSite B S hS) M f) := by
  have h2 := SheafOfModules.isQuasicoherentOnSite_uliftForPresentation hM
  have h3 := isIso_restrictionBaseChange_of_isQuasicoherentOnSite.{u, u}
    (BigAffineZariski.toScheme B S hS) (BigAffineZariski.precoverage B S hS)
    (bigAffineZariski_covering_finite_flat B S hS) _ _ h2 f
  have h4 := bijective_restrictionBaseChange_of_uliftForPresentation
    (bigAffineZariskiRingedSite B S hS).O.obj _ M f.op h3
  exact (ConcreteCategory.isIso_iff_bijective _).mpr h4

/-- **Stacks 0GZV, condition (3) implies condition (1).** A sheaf of `𝒪_Aff`-modules on
`(Aff/S)_étale` which is quasi-coherent on the ringed site `((Aff/S)_étale, 𝒪_Aff)` has all its
base-change maps `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` isomorphisms. -/
@[stacks 0GZV "(3) ⇒ (1), from the quasi-coherence conjunct of (3)"]
theorem bigAffineEtale_isIso_canonicalMap_of_isQuasicoherentOnSite
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineEtaleRingedSite B S hS).O))
    (hM : M.IsQuasicoherentOnSite) {U V : BigAffineEtale B S hS} (f : U ⟶ V) :
    IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineEtaleRingedSite B S hS) M f) := by
  have h2 := SheafOfModules.isQuasicoherentOnSite_uliftForPresentation hM
  have h3 := isIso_restrictionBaseChange_of_isQuasicoherentOnSite.{u, u}
    (BigAffineEtale.toScheme B S hS) (BigAffineEtale.precoverage B S hS)
    (bigAffineEtale_covering_finite_flat B S hS) _ _ h2 f
  have h4 := bijective_restrictionBaseChange_of_uliftForPresentation
    (bigAffineEtaleRingedSite B S hS).O.obj _ M f.op h3
  exact (ConcreteCategory.isIso_iff_bijective _).mpr h4

/-- **Stacks 0GZV, condition (4) implies condition (1).** A sheaf of `𝒪_Aff`-modules on
`(Aff/S)_smooth` which is quasi-coherent on the ringed site `((Aff/S)_smooth, 𝒪_Aff)` has all its
base-change maps `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` isomorphisms. -/
@[stacks 0GZV "(4) ⇒ (1), from the quasi-coherence conjunct of (4)"]
theorem bigAffineSmooth_isIso_canonicalMap_of_isQuasicoherentOnSite
    (B : BigSmoothSite.{u}) (S : Scheme.{u}) (hS : S.size < B.cutoff)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineSmoothRingedSite B S hS).O))
    (hM : M.IsQuasicoherentOnSite) {U V : BigAffineSmooth B S hS} (f : U ⟶ V) :
    IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineSmoothRingedSite B S hS) M f) := by
  have h2 := SheafOfModules.isQuasicoherentOnSite_uliftForPresentation hM
  have h3 := isIso_restrictionBaseChange_of_isQuasicoherentOnSite.{u, u}
    (BigAffineSmooth.toScheme B S hS) (BigAffineSmooth.precoverage B S hS)
    (bigAffineSmooth_covering_finite_flat B S hS) _ _ h2 f
  have h4 := bijective_restrictionBaseChange_of_uliftForPresentation
    (bigAffineSmoothRingedSite B S hS).O.obj _ M f.op h3
  exact (ConcreteCategory.isIso_iff_bijective _).mpr h4

/-- **Stacks 0GZV, condition (5) implies condition (1).** A sheaf of `𝒪_Aff`-modules on
`(Aff/S)_syntomic` which is quasi-coherent on the ringed site `((Aff/S)_syntomic, 𝒪_Aff)` has all
its base-change maps `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` isomorphisms. -/
@[stacks 0GZV "(5) ⇒ (1), from the quasi-coherence conjunct of (5)"]
theorem bigAffineSyntomic_isIso_canonicalMap_of_isQuasicoherentOnSite
    (B : BigSyntomicSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineSyntomicRingedSite B S hS).O))
    (hM : M.IsQuasicoherentOnSite) {U V : BigAffineSyntomic B S hS} (f : U ⟶ V) :
    IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineSyntomicRingedSite B S hS) M f) := by
  have h2 := SheafOfModules.isQuasicoherentOnSite_uliftForPresentation hM
  have h3 := isIso_restrictionBaseChange_of_isQuasicoherentOnSite.{u, u}
    (BigAffineSyntomic.toScheme B S hS) (BigAffineSyntomic.precoverage B S hS)
    (bigAffineSyntomic_covering_finite_flat B S hS) _ _ h2 f
  have h4 := bijective_restrictionBaseChange_of_uliftForPresentation
    (bigAffineSyntomicRingedSite B S hS).O.obj _ M f.op h3
  exact (ConcreteCategory.isIso_iff_bijective _).mpr h4

/-- **Stacks 0GZV, (1) ⇔ (6), for a sheaf of modules.** A sheaf of `𝒪_Aff`-modules on
`(Aff/S)_fppf` is quasi-coherent on the ringed site `((Aff/S)_fppf, 𝒪_Aff)` exactly when all of
its base-change maps `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are isomorphisms.

The sheaf conjunct of condition (6) is carried by the type of `M`; for a presheaf of modules it
is `AlgebraicGeometry.bigAffineFppf_isSheaf_of_cartesian`. -/
@[stacks 0GZV "(1) ⇔ (6), for a sheaf of modules"]
theorem bigAffineFppf_isQuasicoherentOnSite_iff_canonicalMap_isIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineFppfRingedSite B S hS).O)) :
    M.IsQuasicoherentOnSite ↔
      ∀ ⦃U V : BigAffineFppf B S hS⦄ (f : U ⟶ V),
        IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineFppfRingedSite B S hS) M f) :=
  ⟨fun hM _ _ f => bigAffineFppf_isIso_canonicalMap_of_isQuasicoherentOnSite B S hS M hM f,
    fun h => bigAffineFppf_isQuasicoherentOnSite_of_canonicalMap_isIso B S hS M h⟩

/-- **Stacks 0GZV, (1) ⇔ (2), for a sheaf of modules.** A sheaf of `𝒪_Aff`-modules on
`(Aff/S)_Zar` is quasi-coherent on the ringed site `((Aff/S)_Zar, 𝒪_Aff)` exactly when all of
its base-change maps `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are isomorphisms.

The sheaf conjunct of condition (2) is carried by the type of `M`; for a presheaf of modules it
is `AlgebraicGeometry.bigAffineZariski_isSheaf_of_cartesian`. -/
@[stacks 0GZV "(1) ⇔ (2), for a sheaf of modules"]
theorem bigAffineZariski_isQuasicoherentOnSite_iff_canonicalMap_isIso
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineZariskiRingedSite B S hS).O)) :
    M.IsQuasicoherentOnSite ↔
      ∀ ⦃U V : BigAffineZariski B S hS⦄ (f : U ⟶ V),
        IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineZariskiRingedSite B S hS) M f) :=
  ⟨fun hM _ _ f => bigAffineZariski_isIso_canonicalMap_of_isQuasicoherentOnSite B S hS M hM f,
    fun h => bigAffineZariski_isQuasicoherentOnSite_of_canonicalMap_isIso B S hS M h⟩

/-- **Stacks 0GZV, (1) ⇔ (3), for a sheaf of modules.** A sheaf of `𝒪_Aff`-modules on
`(Aff/S)_étale` is quasi-coherent on the ringed site `((Aff/S)_étale, 𝒪_Aff)` exactly when all of
its base-change maps `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are isomorphisms.

The sheaf conjunct of condition (3) is carried by the type of `M`; for a presheaf of modules it
is `AlgebraicGeometry.bigAffineEtale_isSheaf_of_cartesian`. -/
@[stacks 0GZV "(1) ⇔ (3), for a sheaf of modules"]
theorem bigAffineEtale_isQuasicoherentOnSite_iff_canonicalMap_isIso
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineEtaleRingedSite B S hS).O)) :
    M.IsQuasicoherentOnSite ↔
      ∀ ⦃U V : BigAffineEtale B S hS⦄ (f : U ⟶ V),
        IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineEtaleRingedSite B S hS) M f) :=
  ⟨fun hM _ _ f => bigAffineEtale_isIso_canonicalMap_of_isQuasicoherentOnSite B S hS M hM f,
    fun h => bigAffineEtale_isQuasicoherentOnSite_of_canonicalMap_isIso B S hS M h⟩

/-- **Stacks 0GZV, (1) ⇔ (4), for a sheaf of modules.** A sheaf of `𝒪_Aff`-modules on
`(Aff/S)_smooth` is quasi-coherent on the ringed site `((Aff/S)_smooth, 𝒪_Aff)` exactly when all of
its base-change maps `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are isomorphisms.

The sheaf conjunct of condition (4) is carried by the type of `M`; for a presheaf of modules it
is `AlgebraicGeometry.bigAffineSmooth_isSheaf_of_cartesian`. -/
@[stacks 0GZV "(1) ⇔ (4), for a sheaf of modules"]
theorem bigAffineSmooth_isQuasicoherentOnSite_iff_canonicalMap_isIso
    (B : BigSmoothSite.{u}) (S : Scheme.{u}) (hS : S.size < B.cutoff)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineSmoothRingedSite B S hS).O)) :
    M.IsQuasicoherentOnSite ↔
      ∀ ⦃U V : BigAffineSmooth B S hS⦄ (f : U ⟶ V),
        IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineSmoothRingedSite B S hS) M f) :=
  ⟨fun hM _ _ f => bigAffineSmooth_isIso_canonicalMap_of_isQuasicoherentOnSite B S hS M hM f,
    fun h => bigAffineSmooth_isQuasicoherentOnSite_of_canonicalMap_isIso B S hS M h⟩

/-- **Stacks 0GZV, (1) ⇔ (5), for a sheaf of modules.** A sheaf of `𝒪_Aff`-modules on
`(Aff/S)_syntomic` is quasi-coherent on the ringed site `((Aff/S)_syntomic, 𝒪_Aff)` exactly when
all of its base-change maps `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are isomorphisms.

The sheaf conjunct of condition (5) is carried by the type of `M`; for a presheaf of modules it
is `AlgebraicGeometry.bigAffineSyntomic_isSheaf_of_cartesian`. -/
@[stacks 0GZV "(1) ⇔ (5), for a sheaf of modules"]
theorem bigAffineSyntomic_isQuasicoherentOnSite_iff_canonicalMap_isIso
    (B : BigSyntomicSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineSyntomicRingedSite B S hS).O)) :
    M.IsQuasicoherentOnSite ↔
      ∀ ⦃U V : BigAffineSyntomic B S hS⦄ (f : U ⟶ V),
        IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineSyntomicRingedSite B S hS) M f) :=
  ⟨fun hM _ _ f => bigAffineSyntomic_isIso_canonicalMap_of_isQuasicoherentOnSite B S hS M hM f,
    fun h => bigAffineSyntomic_isQuasicoherentOnSite_of_canonicalMap_isIso B S hS M h⟩

end AlgebraicGeometry

end
