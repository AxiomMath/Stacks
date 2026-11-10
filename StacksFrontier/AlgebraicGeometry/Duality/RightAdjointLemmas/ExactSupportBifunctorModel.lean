module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedInternalHomBifunctor
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedTrace
public import
  StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportHomComplexSingleSource
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportKInjectiveCounit

/-!
# The bifunctor model of Tag 0A77 at a K-injective complex, and its trace

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces and `I` a K-injective cochain
complex of `𝒪_X`-modules.  Four identifications, none of which involves a choice, compose to

`Ri_* R ℰom(𝒪_Z, Q I) ≅ R ℰom_{𝒪_X}((i_* 𝒪_Z)[0], Q I)`:

the K-injective model `R ℰom(𝒪_Z, Q I) ≅ Q(ℰom^•(𝒪_Z, I))` of
[Stacks, Tag 0A76] pushed forward, the factorisation of `Ri_*` through pushforward of complexes,
the degreewise identification `i_* ℰom^•(𝒪_Z, I) ≅ SheafHom^•_{𝒪_X}((i_* 𝒪_Z)[0], I)` of
[Stacks, Tag 0A75], and the K-injective model of the derived internal Hom.

This is a model of the isomorphism of [Stacks, Tag 0A77], and the reason to build it rather
than use the library's one is the **trace**: the counit of [Stacks, Tag 0A76] at `Q I` is this
identification followed by precomposition with a map `𝒪_X[0] ⟶ (i_* 𝒪_Z)[0]` carrying the unit
section to the unit section and by the identification `R ℰom_{𝒪_X}(𝒪_X, Q I) ≅ Q I`.  No
naturality of the bifunctor in its source variable, and no chosen cochain representative of
`Ri_* 𝒪_Z`, enters: the trace identity is the degreewise one
(`…exactSupportHomComplexIso_comp_evaluation`) carried across the two K-injective models.

All names below live in the namespace
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`.

The structure sheaf placed in degree zero is not K-injective, so the identification at it — the
one the triangle of [Stacks, Tag 08I0] meets — is obtained by transporting the above along the
chosen K-injective resolution of `𝒪_X[0]`.  That is `structureBifunctorModelIso`, and it is the
isomorphism of [Stacks, Tag 0A77] that
`StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierCanonicalIso` consumes.

## Main definitions

* `structureEvaluation`: the identification `R ℰom_{𝒪_X}(𝒪_X[0], Q I) ⟶ Q I`, the K-injective
  model of the derived internal Hom followed by evaluation at the unit section.
* `kInjectiveBifunctorModelIso`: the identification
  `Ri_* R ℰom(𝒪_Z, Q I) ≅ R ℰom_{𝒪_X}((i_* 𝒪_Z)[0], Q I)`.
* `structureKInjective` and `structureKInjectiveAugmentation`: the chosen K-injective resolution
  of `𝒪_X[0]` and the augmentation into it.
* `structureBifunctorModelIso`: the identification
  `Ri_* R ℰom(𝒪_Z, 𝒪_X) ≅ R ℰom_{𝒪_X}((i_* 𝒪_Z)[0], 𝒪_X)` obtained by transporting
  `kInjectiveBifunctorModelIso` along that augmentation.

## Main results

* `kInjectiveBifunctorModelIso_trace`: **the trace description.** The identification, followed
  by precomposition with `w : 𝒪_X[0] ⟶ (i_* 𝒪_Z)[0]` and by `structureEvaluation`, is the
  counit of [Stacks, Tag 0A76] at `Q I`.
* `structureEvaluation_naturality`: `structureEvaluation` is the transport along the resolution
  of an identification `R ℰom_{𝒪_X}(𝒪_X[0], 𝒪_X[0]) ⟶ 𝒪_X[0]` which the comparison to the
  derived internal Hom turns into evaluation at the unit section.
* `structureBifunctorModelIso_trace`: **the trace description at the structure sheaf**, which is
  the form the triangle of [Stacks, Tag 08I0] consumes.

## Implementation notes

The category of `𝒪_X`-modules carries two definitionally equal spellings here, as it does in
`RightAdjointLemmas.ExactSupportDerivedInternalHomBifunctor`:
sheaf Hom with exact support and the derived adjunction of [Stacks, Tag 0A76] are stated over
`structureSheafRing`, the internal Hom complex over
`Stacks.SheafOfModules.StructureSheafModules`.  The two meet only once `sheafCompose` and
`AlgebraicGeometry.SheafedSpace.sheaf` are unfolded, so both are made locally
`instance_reducible`, and K-injectivity of the target complex is restated once in the second
spelling — `isKInjective_structureSheafModules` — so that instance search finds it there; without
that restatement the K-injective model of the derived internal Hom does not even elaborate.

For the same reason the trace identities are proved in term mode, with the rewrites carried by
`Eq.trans` and `congrArg` rather than by `rewrite`: every intermediate goal mentions objects in
both spellings, and `rewrite` refuses such a target even when the displayed pattern occurs in
it.  The three bookkeeping steps that are pure category theory — cancelling an epimorphism
across a square, regrouping a five-factor composite, and pasting the four squares that carry an
identification along a resolution — are therefore isolated as private lemmas about an abstract
category, where `calc` and `rewrite` do work.

## References

* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian


universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

/-- **Transporting an identification of `R ℰom_{𝒪_X}(𝒪_X[0], -)` with the identity along a
morphism.**  Abstractly: if `v` is epi, `u` is split by `ch`, and the three squares `k1`, `k2`,
`k4` commute, then `hα` and `sdi` agree across `α`.  It is stated for an abstract category,
where `calc` and `rewrite` are available, because every composite it is used on mixes the two
spellings of the category of `𝒪_X`-modules. -/
private theorem comp_cancel_epi_square {C : Type*} [Category C] {V W U₀ U₁ O J : C}
    (v : V ⟶ U₀) (u : W ⟶ U₁) (ch : U₁ ⟶ W) (q : V ⟶ W) (r : V ⟶ O) (s : W ⟶ J)
    (hα : U₀ ⟶ U₁) (sdi : U₀ ⟶ O) (α : O ⟶ J) (hv : Epi v)
    (k1 : v ≫ sdi = r) (k2 : q ≫ u = v ≫ hα) (k3 : u ≫ ch = 𝟙 W) (k4 : q ≫ s = r ≫ α) :
    hα ≫ ch ≫ s = sdi ≫ α := by
  rw [← cancel_epi v, ← reassoc_of% k2, reassoc_of% k3, k4, reassoc_of% k1]

/-- **Transporting a trace description along a resolution.** Abstractly: given the four commuting
squares `h1`–`h4`, a splitting `h5` of `gh` and a splitting `h6` of `α`, the composite
`(f ≫ m ≫ gi) ≫ p₀ ≫ sdi` is `c₀`.  It is stated for an abstract category, where `calc` and
`rewrite` are available, because every composite it is used on mixes the two spellings of the
category of `𝒪_X`-modules. -/
private theorem comp_transport_square {C : Type*} [Category C]
    {S₀ S₁ T₀ T₁ U₀ U₁ O J : C} (f : S₀ ⟶ S₁) (m : S₁ ⟶ T₁) (gi : T₁ ⟶ T₀) (gh : T₀ ⟶ T₁)
    (p₀ : T₀ ⟶ U₀) (p₁ : T₁ ⟶ U₁) (hα : U₀ ⟶ U₁) (sE : U₁ ⟶ J) (sdi : U₀ ⟶ O)
    (α : O ⟶ J) (αi : J ⟶ O) (c₀ : S₀ ⟶ O) (c₁ : S₁ ⟶ J)
    (h1 : hα ≫ sE = sdi ≫ α) (h2 : gh ≫ p₁ = p₀ ≫ hα) (h3 : m ≫ p₁ ≫ sE = c₁)
    (h4 : f ≫ c₁ = c₀ ≫ α) (h5 : gi ≫ gh = 𝟙 T₁) (h6 : α ≫ αi = 𝟙 O) :
    (f ≫ m ≫ gi) ≫ p₀ ≫ sdi = c₀ := by
  have : Mono α := mono_of_mono_fac h6
  rw [← cancel_mono α]
  simp only [Category.assoc, ← h1, ← reassoc_of% h2, reassoc_of% h5, h3, h4]

/-- Regrouping a five-factor composite: the last three factors may be treated together. It is
stated for an abstract category, where `rewrite` is available, because the composites it is used
on mix the two spellings of the category of `𝒪_X`-modules. -/
private theorem comp_assoc₃ {C : Type*} [Category C] {a b c d e f : C}
    (p : a ⟶ b) (q : b ⟶ c) (r : c ⟶ d) (s : d ⟶ e) (x : e ⟶ f) {y : c ⟶ f}
    (hy : (r ≫ s) ≫ x = y) : (p ≫ q ≫ r ≫ s) ≫ x = p ≫ q ≫ y := by
  simp [← hy]

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})
  (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective]

/-- K-injectivity of a cochain complex of `𝒪_X`-modules, read in the vocabulary of the internal
Hom complex: the category of `𝒪_X`-modules appears there as
`Stacks.SheafOfModules.StructureSheafModules S.X.sheaf`. -/
instance isKInjective_structureSheafModules :
    CochainComplex.IsKInjective
      (C := Stacks.SheafOfModules.StructureSheafModules S.X.sheaf)
      (show CochainComplex (Stacks.SheafOfModules.StructureSheafModules S.X.sheaf) ℤ from I) :=
  ‹I.IsKInjective›

/-- **The identification `R ℰom_{𝒪_X}(𝒪_X[0], Q I) ≅ Q I` at a K-injective complex**: the
K-injective model of the derived internal Hom, followed by evaluation at the unit section. -/
def structureEvaluation :
    ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
          (op (AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSiteX S)))).obj
        (DerivedCategory.Q.obj I) ⟶
      DerivedCategory.Q.obj I :=
  (Stacks.SheafOfModules.derivedSheafHomComparison S.X.sheaf
      (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S)) I).hom ≫
    DerivedCategory.Q.map
      (AlgebraicGeometry.RingedSite.structureSheafHomEvaluation (ringedSiteX S) I)

/-- **The bifunctor model of [Stacks, Tag 0A77] at a K-injective complex:**

`Ri_* R ℰom(𝒪_Z, Q I) ≅ R ℰom_{𝒪_X}((i_* 𝒪_Z)[0], Q I)`.

The K-injective model of [Stacks, Tag 0A76] pushed forward, the factorisation of `Ri_*` through
pushforward of complexes, the degreewise identification of [Stacks, Tag 0A75] and the
K-injective model of the derived internal Hom, composed. -/
def kInjectiveBifunctorModelIso :
    (modulePushforward S.i).mapDerivedCategory.obj
        (S.derivedSheafHomExactSupport.obj (DerivedCategory.Q.obj I)) ≅
      ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
          (op (DerivedCategory.Q.obj (pushforwardStructureSingleComplex S)))).obj
        (DerivedCategory.Q.obj I) :=
  (modulePushforward S.i).mapDerivedCategory.mapIso
      (S.derivedSheafHomExactSupportKInjectiveIso I) ≪≫
    (modulePushforward S.i).mapDerivedCategoryFactors.app
        ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≪≫
      DerivedCategory.Q.mapIso (exactSupportHomComplexIso S I) ≪≫
        (Stacks.SheafOfModules.derivedSheafHomComparison S.X.sheaf
          (pushforwardStructureSingleComplex S) I).symm

/-- Precomposition with `Q w` on the derived internal Hom, read through the two K-injective
models, is precomposition with `w` on internal Hom complexes. This is the naturality of the
K-injective model in its source variable, with the identity in the target variable cancelled. -/
theorem derivedSheafHomComparison_inv_comp_pre
    (w : AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S) ⟶
      pushforwardStructureSingleComplex S) :
    (Stacks.SheafOfModules.derivedSheafHomComparison S.X.sheaf
            (pushforwardStructureSingleComplex S) I).inv ≫
        ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).map
            (DerivedCategory.Q.map w).op).app (DerivedCategory.Q.obj I) ≫
          structureEvaluation S I =
      DerivedCategory.Q.map (AlgebraicGeometry.RingedSite.homMap (ringedSiteX S) w (𝟙 I) ≫
        AlgebraicGeometry.RingedSite.structureSheafHomEvaluation (ringedSiteX S) I) := by
  have hnat := RingedSpaceModuleAdjunction.derivedSheafHomComparison_naturality_source S.X w I
  refine Eq.trans (congrArg
    (fun t => (Stacks.SheafOfModules.derivedSheafHomComparison S.X.sheaf
      (pushforwardStructureSingleComplex S) I).inv ≫ t) (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (congrArg
    (fun t => (Stacks.SheafOfModules.derivedSheafHomComparison S.X.sheaf
      (pushforwardStructureSingleComplex S) I).inv ≫ t ≫
        DerivedCategory.Q.map
          (AlgebraicGeometry.RingedSite.structureSheafHomEvaluation (ringedSiteX S) I))
    hnat) ?_
  refine Eq.trans (congrArg
    (fun t => (Stacks.SheafOfModules.derivedSheafHomComparison S.X.sheaf
      (pushforwardStructureSingleComplex S) I).inv ≫ t) (Category.assoc _ _ _)) ?_
  exact Eq.trans
    ((Stacks.SheafOfModules.derivedSheafHomComparison S.X.sheaf
      (pushforwardStructureSingleComplex S) I).inv_hom_id_assoc _)
    (DerivedCategory.Q.map_comp _ _).symm

/-- The components of the identification: the four factors, written out. -/
theorem kInjectiveBifunctorModelIso_hom :
    (kInjectiveBifunctorModelIso S I).hom =
      (modulePushforward S.i).mapDerivedCategory.map
          (S.derivedSheafHomExactSupportKInjectiveIso I).hom ≫
        (modulePushforward S.i).mapDerivedCategoryFactors.hom.app
            ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
          DerivedCategory.Q.map (exactSupportHomComplexIso S I).hom ≫
            (Stacks.SheafOfModules.derivedSheafHomComparison S.X.sheaf
              (pushforwardStructureSingleComplex S) I).inv :=
  rfl

/-- **The counit of [Stacks, Tag 0A76] at the class of a K-injective complex, read through the
K-injective model.**  This is
`…derivedSheafHomExactSupportKInjectiveIso_inv_comp_counit` with the model isomorphism moved to
the other side. -/
alias counit_app_eq_of_isKInjective :=
  derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app_Q_of_isKInjective

omit [I.IsKInjective] in
/-- The degreewise trace identity of [Stacks, Tag 0A75], carried into the derived category. -/
theorem Q_map_exactSupportHomComplexIso_comp
    (w : AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S) ⟶
      pushforwardStructureSingleComplex S)
    (hw : ∀ U : Opens S.X, ((w.f 0).val.app (op U))
        (AlgebraicGeometry.RingedSite.structureSheafOne (ringedSiteX S) U) =
      (1 : (S.pushedRingSheaf.obj.obj (op U) : Type u))) :
    DerivedCategory.Q.map (exactSupportHomComplexIso S I).hom ≫
        DerivedCategory.Q.map (AlgebraicGeometry.RingedSite.homMap (ringedSiteX S) w (𝟙 I) ≫
          AlgebraicGeometry.RingedSite.structureSheafHomEvaluation (ringedSiteX S) I) =
      DerivedCategory.Q.map
        ((Adjunction.mapHomologicalComplexAdjunction
          S.modulePushforwardSheafHomExactSupportAdjunction (ComplexShape.up ℤ)).counit.app I) :=
  Eq.trans (DerivedCategory.Q.map_comp _ _).symm
    (congrArg (fun t => DerivedCategory.Q.map t)
      (exactSupportHomComplexIso_comp_evaluation S I w hw))

/-- **The trace, on internal Hom complexes carried into the derived category.** The degreewise
identification of [Stacks, Tag 0A75], followed by the K-injective model of the derived internal
Hom, by precomposition with `Q w` and by the identification
`R ℰom_{𝒪_X}(𝒪_X[0], Q I) ≅ Q I`, is the class of the degreewise counit.

This is the degreewise trace identity `…exactSupportHomComplexIso_comp_evaluation` composed with
`derivedSheafHomComparison_inv_comp_pre`. -/
theorem exactSupportHomComplexIso_comp_derivedTrace
    (w : AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S) ⟶
      pushforwardStructureSingleComplex S)
    (hw : ∀ U : Opens S.X, ((w.f 0).val.app (op U))
        (AlgebraicGeometry.RingedSite.structureSheafOne (ringedSiteX S) U) =
      (1 : (S.pushedRingSheaf.obj.obj (op U) : Type u))) :
    (DerivedCategory.Q.map (exactSupportHomComplexIso S I).hom ≫
          (Stacks.SheafOfModules.derivedSheafHomComparison S.X.sheaf
            (pushforwardStructureSingleComplex S) I).inv) ≫
        (((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).map
              (DerivedCategory.Q.map w).op).app (DerivedCategory.Q.obj I) ≫
          structureEvaluation S I) =
      DerivedCategory.Q.map
        ((Adjunction.mapHomologicalComplexAdjunction
          S.modulePushforwardSheafHomExactSupportAdjunction (ComplexShape.up ℤ)).counit.app I) :=
  Eq.trans (Category.assoc _ _ _)
    (Eq.trans
      (congrArg (fun t => DerivedCategory.Q.map (exactSupportHomComplexIso S I).hom ≫ t)
        (derivedSheafHomComparison_inv_comp_pre S I w))
      (Q_map_exactSupportHomComplexIso_comp S I w hw))

/-- **The trace description of the bifunctor model.** At a K-injective complex `I` of
`𝒪_X`-modules the counit of [Stacks, Tag 0A76] is `kInjectiveBifunctorModelIso`, followed by
precomposition with a map `w : 𝒪_X[0] ⟶ (i_* 𝒪_Z)[0]` carrying the unit section to the unit
section, followed by the identification `R ℰom_{𝒪_X}(𝒪_X[0], Q I) ≅ Q I`.

The content is the degreewise trace identity
`…exactSupportHomComplexIso_comp_evaluation`, carried across the K-injective model of
[Stacks, Tag 0A76] by `counit_app_eq_of_isKInjective` and across the K-injective model of the
derived internal Hom by `derivedSheafHomComparison_inv_comp_pre`. -/
theorem kInjectiveBifunctorModelIso_trace
    (w : AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S) ⟶
      pushforwardStructureSingleComplex S)
    (hw : ∀ U : Opens S.X, ((w.f 0).val.app (op U))
        (AlgebraicGeometry.RingedSite.structureSheafOne (ringedSiteX S) U) =
      (1 : (S.pushedRingSheaf.obj.obj (op U) : Type u))) :
    (kInjectiveBifunctorModelIso S I).hom ≫
        ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).map
            (DerivedCategory.Q.map w).op).app (DerivedCategory.Q.obj I) ≫
          structureEvaluation S I =
      S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
        (DerivedCategory.Q.obj I) :=
  Eq.trans
    (Eq.trans
      (congrArg
        (fun t => t ≫ ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).map
            (DerivedCategory.Q.map w).op).app (DerivedCategory.Q.obj I) ≫
          structureEvaluation S I)
        (kInjectiveBifunctorModelIso_hom S I))
      (comp_assoc₃ _ _ _ _ _ (exactSupportHomComplexIso_comp_derivedTrace S I w hw)))
    (counit_app_eq_of_isKInjective S I).symm

/-- The identification `R ℰom_{𝒪_X}(𝒪_X[0], Q I) ⟶ Q I` is the K-injective model followed by
evaluation at the unit section. This is its definition, named so that the statements below can
be rewritten by it across the two spellings of the category of `𝒪_X`-modules. -/
theorem structureEvaluation_eq :
    structureEvaluation S I =
      (Stacks.SheafOfModules.derivedSheafHomComparison S.X.sheaf
          (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S)) I).hom ≫
        DerivedCategory.Q.map
          (AlgebraicGeometry.RingedSite.structureSheafHomEvaluation (ringedSiteX S) I) :=
  rfl

/-- **`structureEvaluation` is the transport along a resolution of an identification at the
structure sheaf.** Let `a : 𝒪_X^• ⟶ I` be a morphism of complexes and
`t : R ℰom_{𝒪_X}(𝒪_X[0], 𝒪_X[0]) ⟶ 𝒪_X[0]` a morphism which the comparison
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison` turns into evaluation at the unit
section. Then `t` and `structureEvaluation` agree across `a`.

The comparison is natural in the source for an arbitrary morphism of complexes
(`…strictlyPerfectHomComparison_naturality`) and is the inverse of the K-injective model at a
K-injective target (`…strictlyPerfectHomComparison_eq_homComparison_inv`), so after cancelling it
what is left is the naturality of evaluation at the unit section,
`…structureSheafHomEvaluation_naturality`. -/
theorem structureEvaluation_naturality
    (a : AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S) ⟶ I)
    (t : ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
          (op (AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSiteX S)))).obj
        (AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSiteX S)) ⟶
      AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSiteX S))
    (hepi : Epi (AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison (ringedSiteX S)
      (Stacks.SheafOfModules.derivedInternalHom S.X.sheaf)
      (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S))
      (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S))))
    (ht : AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison (ringedSiteX S)
          (Stacks.SheafOfModules.derivedInternalHom S.X.sheaf)
          (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S))
          (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S)) ≫ t =
        DerivedCategory.Q.map (AlgebraicGeometry.RingedSite.structureSheafHomEvaluation
          (ringedSiteX S) (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S)))) :
    ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
          (op (AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSiteX S)))).map
        (DerivedCategory.Q.map a) ≫ structureEvaluation S I =
      t ≫ DerivedCategory.Q.map a := by
  -- `I` is K-injective in the spelling of the structure sheaf of `S.X`; the lemmas over the ringed
  -- site ask it of the same complex read over `Tensor.ringSheaf` of the site.
  have : CochainComplex.IsKInjective
      (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSiteX S).O))
      (show CochainComplex (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSiteX S).O)) ℤ from I) := ‹I.IsKInjective›
  have hid : ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).map
      (DerivedCategory.Q.map
        (𝟙 (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S)))).op).app
      (DerivedCategory.Q.obj
        (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S))) = 𝟙 _ := by
    rw [CategoryTheory.Functor.map_id, op_id]
    exact (congrArg (fun φ => NatTrans.app φ _) (CategoryTheory.Functor.map_id _ _)).trans rfl
  have k2 : DerivedCategory.Q.map (AlgebraicGeometry.RingedSite.homMap (ringedSiteX S)
            (𝟙 (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S))) a) ≫
          AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison (ringedSiteX S)
            (Stacks.SheafOfModules.derivedInternalHom S.X.sheaf)
            (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S)) I =
        AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison (ringedSiteX S)
              (Stacks.SheafOfModules.derivedInternalHom S.X.sheaf)
              (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S))
              (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S)) ≫
          ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
              (op (AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSiteX S)))).map
            (DerivedCategory.Q.map a) :=
    Eq.trans
      (AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_naturality (ringedSiteX S)
        (Stacks.SheafOfModules.derivedInternalHom S.X.sheaf) _ _ _ _
        (𝟙 (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S))) a)
      (congrArg
        (fun z => AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison (ringedSiteX S)
            (Stacks.SheafOfModules.derivedInternalHom S.X.sheaf)
            (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S))
            (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S)) ≫ z)
        (Eq.trans
          (congrArg
            (fun z => z ≫ ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
                (op (AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSiteX S)))).map
              (DerivedCategory.Q.map a))
            hid)
          (Category.id_comp _)))
  have k3 : AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison (ringedSiteX S)
          (Stacks.SheafOfModules.derivedInternalHom S.X.sheaf)
          (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S)) I ≫
        (Stacks.SheafOfModules.derivedSheafHomComparison S.X.sheaf
          (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S)) I).hom =
      𝟙 _ :=
    Eq.trans
      (congrArg
        (fun z => z ≫ (Stacks.SheafOfModules.derivedSheafHomComparison S.X.sheaf
          (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S)) I).hom)
        (AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_eq_homComparison_inv
          (ringedSiteX S) (Stacks.SheafOfModules.derivedInternalHom S.X.sheaf)
          (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S)) I))
      (Stacks.SheafOfModules.derivedSheafHomComparison S.X.sheaf
        (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S)) I).inv_hom_id
  have k4 : DerivedCategory.Q.map (AlgebraicGeometry.RingedSite.homMap (ringedSiteX S)
            (𝟙 (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S))) a) ≫
          DerivedCategory.Q.map
            (AlgebraicGeometry.RingedSite.structureSheafHomEvaluation (ringedSiteX S) I) =
        DerivedCategory.Q.map (AlgebraicGeometry.RingedSite.structureSheafHomEvaluation
            (ringedSiteX S)
            (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S))) ≫
          DerivedCategory.Q.map a :=
    Eq.trans (DerivedCategory.Q.map_comp _ _).symm
      (Eq.trans
        (congrArg (fun z => DerivedCategory.Q.map z)
          (AlgebraicGeometry.RingedSite.structureSheafHomEvaluation_naturality (ringedSiteX S) a))
        (DerivedCategory.Q.map_comp _ _))
  exact Eq.trans
    (congrArg
      (fun z => ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
            (op (AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSiteX S)))).map
          (DerivedCategory.Q.map a) ≫ z)
      (structureEvaluation_eq S I))
    (comp_cancel_epi_square _ _ _ _ _ _ _ _ _ hepi ht k2 k3 k4)

/-! ### The chosen K-injective resolution of the structure sheaf -/

/-- The chosen K-injective resolution of the structure sheaf of `X` placed in degree zero. -/
abbrev structureKInjective :=
  (AlgebraicGeometry.RingedSite.kInjectiveResolution (ringedSiteX S)).obj
    (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S))

/-- The augmentation of the structure sheaf placed in degree zero into
`structureKInjective`. -/
abbrev structureKInjectiveAugmentation :=
  (AlgebraicGeometry.RingedSite.kInjectiveAugmentation (ringedSiteX S)).app
    (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S))

/-- The chosen resolution is K-injective, in the spelling in which sheaf Hom with exact support
and the adjunction of [Stacks, Tag 0A76] are stated.  It is restated here because the resolution
functor is indexed by the ringed site, so instance search produces K-injectivity only in the
other spelling. -/
instance isKInjective_structureKInjective :
    CochainComplex.IsKInjective (C := SheafOfModules.{u} (structureSheafRing S.X))
      (show CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ from
        structureKInjective S) :=
  Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective _ _

/-- The augmentation into the chosen K-injective resolution is a quasi-isomorphism, so its class
in the derived category is invertible.  Like the K-injectivity instance above, it is stated in
the spelling in which sheaf Hom with exact support is stated, the one in which the model
identifications below are read. -/
instance isIso_Q_map_structureKInjectiveAugmentation :
    IsIso ((DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing S.X))).map
      (structureKInjectiveAugmentation S)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (show QuasiIso (C := SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSiteX S).O))
      (structureKInjectiveAugmentation S) from
      Stacks.Injectives.kInjectiveResolutionInclusion_quasiIso _ _)

/-- The class of the augmentation in the derived category, as an isomorphism out of the structure
sheaf placed in degree zero. -/
def structureKInjectiveAugmentationIso :
    (AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSiteX S) :
        DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) ≅
      DerivedCategory.Q.obj (structureKInjective S) :=
  @asIso _ _ _ _ (DerivedCategory.Q.map (structureKInjectiveAugmentation S))
    (isIso_Q_map_structureKInjectiveAugmentation S)

/-! ### The model at the structure sheaf -/

/-- **The bifunctor model of [Stacks, Tag 0A77] at the structure sheaf:**

`Ri_* R ℰom(𝒪_Z, 𝒪_X) ≅ R ℰom_{𝒪_X}((i_* 𝒪_Z)[0], 𝒪_X)`.

It is `kInjectiveBifunctorModelIso` at the chosen K-injective resolution of the structure sheaf
placed in degree zero, transported along the augmentation into that resolution, whose class in
the derived category is invertible. -/
def structureBifunctorModelIso :
    (modulePushforward S.i).mapDerivedCategory.obj
        (S.derivedSheafHomExactSupport.obj
          (AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSiteX S))) ≅
      ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
          (op (DerivedCategory.Q.obj (pushforwardStructureSingleComplex S)))).obj
        (AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSiteX S)) :=
  (modulePushforward S.i).mapDerivedCategory.mapIso
      (S.derivedSheafHomExactSupport.mapIso
        (structureKInjectiveAugmentationIso S)) ≪≫
    kInjectiveBifunctorModelIso S (structureKInjective S) ≪≫
      (((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
            (op (DerivedCategory.Q.obj (pushforwardStructureSingleComplex S)))).mapIso
          (structureKInjectiveAugmentationIso S)).symm

/-- The three factors of `structureBifunctorModelIso`, written out. -/
theorem structureBifunctorModelIso_hom :
    (structureBifunctorModelIso S).hom =
      (modulePushforward S.i).mapDerivedCategory.map
          (S.derivedSheafHomExactSupport.map
            (DerivedCategory.Q.map (structureKInjectiveAugmentation S))) ≫
        (kInjectiveBifunctorModelIso S (structureKInjective S)).hom ≫
          ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
              (op (DerivedCategory.Q.obj (pushforwardStructureSingleComplex S)))).map
            (structureKInjectiveAugmentationIso S).inv :=
  rfl

/-- **The trace description of `structureBifunctorModelIso`.** Let
`w : 𝒪_X[0] ⟶ (i_* 𝒪_Z)[0]` carry the unit section to the unit section, and let
`t : R ℰom_{𝒪_X}(𝒪_X[0], 𝒪_X[0]) ⟶ 𝒪_X[0]` be a morphism which the comparison to the derived
internal Hom turns into evaluation at the unit section.  Then the model identification, followed
by precomposition with `Q w` and by `t`, is the counit of [Stacks, Tag 0A76] at the structure
sheaf.

This is `kInjectiveBifunctorModelIso_trace` carried along the chosen resolution by four
commuting squares: the naturality of the derived counit, the naturality of precomposition with
`Q w` in the target variable, `structureEvaluation_naturality`, and the invertibility of the
class of the augmentation. -/
theorem structureBifunctorModelIso_trace
    (w : AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S) ⟶
      pushforwardStructureSingleComplex S)
    (hw : ∀ U : Opens S.X, ((w.f 0).val.app (op U))
        (AlgebraicGeometry.RingedSite.structureSheafOne (ringedSiteX S) U) =
      (1 : (S.pushedRingSheaf.obj.obj (op U) : Type u)))
    (t : ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
          (op (AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSiteX S)))).obj
        (AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSiteX S)) ⟶
      AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSiteX S))
    (hepi : Epi (AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison (ringedSiteX S)
      (Stacks.SheafOfModules.derivedInternalHom S.X.sheaf)
      (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S))
      (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S))))
    (ht : AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison (ringedSiteX S)
          (Stacks.SheafOfModules.derivedInternalHom S.X.sheaf)
          (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S))
          (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S)) ≫ t =
        DerivedCategory.Q.map (AlgebraicGeometry.RingedSite.structureSheafHomEvaluation
          (ringedSiteX S) (AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S)))) :
    (structureBifunctorModelIso S).hom ≫
        ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).map
            (DerivedCategory.Q.map w).op).app
          (AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSiteX S)) ≫ t =
      S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
        (AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSiteX S)) :=
  have h1 := structureEvaluation_naturality S (structureKInjective S)
    (structureKInjectiveAugmentation S) t hepi ht
  have h2 := ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).map
    (DerivedCategory.Q.map w).op).naturality
      (DerivedCategory.Q.map (structureKInjectiveAugmentation S))
  have h3 := kInjectiveBifunctorModelIso_trace S (structureKInjective S) w hw
  have h4 := S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.naturality
    (DerivedCategory.Q.map (structureKInjectiveAugmentation S))
  have h5 := (((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
      (op (DerivedCategory.Q.obj (pushforwardStructureSingleComplex S)))).mapIso
    (structureKInjectiveAugmentationIso S)).inv_hom_id
  have h6 := (structureKInjectiveAugmentationIso S).hom_inv_id
  Eq.trans
    (congrArg
      (fun z => z ≫ ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).map
          (DerivedCategory.Q.map w).op).app
        (AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSiteX S)) ≫ t)
      (structureBifunctorModelIso_hom S))
    (comp_transport_square _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6)

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
