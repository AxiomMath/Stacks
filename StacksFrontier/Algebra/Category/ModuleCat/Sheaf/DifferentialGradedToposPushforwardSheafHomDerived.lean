module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushforwardSheafHomDerived
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDerivedPushforwardForget
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDeltaFunctorTriangle
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposPushforwardSheafHomExact

/-!
# The right derived extension of `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` along a morphism of ringed topoi

Let `(f, f♯) : (Sh(𝒞), O_𝒞) ⟶ (Sh(𝒟), O_𝒟)` be a morphism of ringed topoi, let `𝒜` and `𝒜'` be
sheaves of differential graded `O_𝒞`-algebras, let `ℬ` be one of `O_𝒟`-algebras, let
`φ : ℬ ⟶ f_*𝒜` be a homomorphism and let `𝒩` be a differential graded `(𝒜, 𝒜')`-bimodule. Let
`RT : D(𝒜', d) ⥤ D(ℬ, d)` be the right derived extension of the exact functor
`ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` of [Stacks, Tag 0FTS](https://stacks.math.columbia.edu/tag/0FTS).
Then `RT(ℳ) = Rf_* RSheafHom^dg_{𝒜'}(𝒩, ℳ)` functorially in `ℳ`, which is
[Stacks, Tag 0FTT](https://stacks.math.columbia.edu/tag/0FTT).

## Main definitions

* `SheafOfModules.DifferentialGradedModule.derivedToposPushforwardSheafHom`: `RT`, with its
  comparison map `derivedToposPushforwardSheafHomUnit`.

## Main results

* `SheafOfModules.DifferentialGradedModule.acyclic_toposPushforward_obj`: the direct image of a
  module receiving only the zero morphism from flat and K-flat modules is acyclic.
* `SheafOfModules.DifferentialGradedModule.isIso_derivedToposPushforwardUnit_app_sheafHom`: the
  derived pushforward is computed by the direct image on `SheafHom^dg_{𝒜'}(𝒩, ℐ)` for `ℐ` graded
  injective and K-injective.
* `SheafOfModules.DifferentialGradedModule.exists_iso_derivedToposPushforwardSheafHom`:
  **Tag 0FTT**, `RT ≅ derivedSheafHom 𝒩 ⋙ derivedToposPushforward f 𝒜 ℬ φ hφ`, and
  `exists_iso_derivedToposPushforwardSheafHom_fac` its compatibility with the comparison maps.

## Implementation notes

The source argues by uniqueness of adjoints, both functors being right adjoint to
`Lf^*(-) ⊗^{L}_𝒜 𝒩`. Here both are shown to be right derived functors of
`ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)`, which needs `Rf_*` to be computed on `ℋ = SheafHom^dg_{𝒜'}(𝒩, ℐ)`.
By the tensor-hom adjunction and clause (1) of [Stacks, Tag 0FSI], `ℋ` is local for the
quasi-isomorphisms between flat and K-flat modules
(`SheafOfModules.DifferentialGradedModule.isLocalOn_sheafHom`), so the cone `𝒞` of a graded
injective K-injective resolution `ℋ ⟶ 𝒥` receives only the zero morphism from such modules. A good
`ℬ`-module ([Stacks, Tag 0FSA]) resolving `f_*𝒞` ([Stacks, Tag 0FSH]) has a flat and K-flat base
change along `(f, 𝒜, φ)` by condition (3) of goodness, which corepresents morphisms into the
direct image up to homotopy; hence the resolution is null-homotopic and `f_*𝒞` is acyclic. This is
the adjunction `f^* ⊣ f_*` of the source used on good modules only, and needs no derived tensor
product.

The ringed topoi have their sites, morphisms and structure sheaves in one universe `u`, the setting
of the resolutions of [Stacks, Tag 0FT0] and [Stacks, Tag 0FSH]; the compatibility of the
forgetful functor from commutative rings to rings with sheaves is a local instance, true of every
ringed topos.

## References

* [Stacks Project, Tag 0FTT](https://stacks.math.columbia.edu/tag/0FTT)
* [Stacks Project, Tag 0FTS](https://stacks.math.columbia.edu/tag/0FTS)
* [Stacks Project, Tag 0FTP](https://stacks.math.columbia.edu/tag/0FTP)
* [Stacks Project, Tag 0FTQ](https://stacks.math.columbia.edu/tag/0FTQ)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Sheaf

universe u

namespace SheafOfModules.DifferentialGradedModule

open Stacks.Sheaves.RingedToposModules

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory
  AlgebraicGeometry.RingedTopos.hasSheafify_addCommGrpCat
  AlgebraicGeometry.RingedTopos.wEqualsLocallyBijective_addCommGrpCat
  AlgebraicGeometry.RingedTopos.hasSheafCompose_forget₂_ringCat

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  {f : RingedToposHom X Y}
  {A A' : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  {B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
  {φ : B ⟶ toposPushforwardAlgebra (Osharp := X.O) (Psharp := Y.O)
    (toposDirectImageModules (X := X) (Y := Y) f) A} {hφ : φ.IsUnital}

variable (φ hφ) in
/-- **The direct image of a module receiving only the zero morphism from flat modules is
acyclic.** A good module resolving the direct image (Tag 0FSH) has a base change along
`(f, 𝒜, φ)` which is flat and K-flat, by condition (3) of Tag 0FSA; homotopy classes of morphisms
out of the base change are those out of the good module into the direct image, so the resolving
quasi-isomorphism is null-homotopic. -/
theorem acyclic_toposPushforward_obj (C : DifferentialGradedModule.{u, u, u} A)
    (h : ∀ P : DifferentialGradedModule.{u, u, u} A,
      IsFlatObj (X := X.toRingedSite) ((HomotopyCategory.quotient A).obj P) →
        ∀ g : (HomotopyCategory.quotient A).obj P ⟶ (HomotopyCategory.quotient A).obj C, g = 0) :
    ((toposPushforward (toposDirectImageModules (X := X) (Y := Y) f) φ hφ).obj
      C).complex.Acyclic := by
  obtain ⟨P, s, hs, hP⟩ := exists_good_quasiIso.{u, u, u} (A := B)
    ((toposPushforward (toposDirectImageModules (X := X) (Y := Y) f) φ hφ).obj C)
  obtain ⟨⟨T, ⟨e⟩⟩, hT⟩ := hP.baseChange f A φ hφ
  have hsub : Subsingleton ((HomotopyCategory.quotient A).obj T ⟶
      (HomotopyCategory.quotient A).obj C) :=
    ⟨fun a b => (h T (hT T e) a).trans (h T (hT T e) b).symm⟩
  have h0 : (HomotopyCategory.quotient B).map s = (HomotopyCategory.quotient B).map 0 :=
    (homotopyHomEquiv (toposDirectImageModules (X := X) (Y := Y) f) φ hφ e C).symm.injective
      (Subsingleton.elim _ _)
  obtain ⟨H⟩ := (HomotopyCategory.quotient_map_eq_iff _ _).1 h0
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hi : IsIso (HomologicalComplex.homologyMap s.toHomologicalComplex n) := by
    have := hs
    infer_instance
  have e0 : HomologicalComplex.homologyMap s.toHomologicalComplex n = 0 :=
    (H.toComplexHomotopy.homologyMap_eq n).trans (HomologicalComplex.homologyMap_zero _ _ _)
  rw [e0] at hi
  exact IsZero.of_epi_zero (HomologicalComplex.homology P.complex n) _

variable (φ hφ) in
/-- **The direct image carries a quasi-isomorphism between objects local for the
quasi-isomorphisms between flat objects to a quasi-isomorphism.** The cone of the
quasi-isomorphism receives only the zero morphism from a flat module, so its direct image is
acyclic, and that direct image is the cone of the direct image of the quasi-isomorphism. -/
theorem quasiIso_toposPushforward_map {H J : DifferentialGradedModule.{u, u, u} A}
    (hH : (quasiIsomorphisms.{u, u, u} A).IsLocalOn (IsFlatObj (X := X.toRingedSite))
      ((HomotopyCategory.quotient A).obj H))
    (hJ : (quasiIsomorphisms.{u, u, u} A).IsLocalOn (IsFlatObj (X := X.toRingedSite))
      ((HomotopyCategory.quotient A).obj J))
    (s : H ⟶ J) (hs : QuasiIso s.toHomologicalComplex) :
    QuasiIso ((toposPushforward (toposDirectImageModules (X := X) (Y := Y) f) φ hφ).map
      s).toHomologicalComplex := by
  have hC := acyclic_toposPushforward_obj φ hφ (cone s)
    (eq_zero_of_isLocalOn_cone (X := X.toRingedSite) hH hJ s hs)
  have hC' : (((toposDirectImageModules (X := X) (Y := Y) f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (cone s).complex).Acyclic := hC
  rw [(conePackage s).cone_complex] at hC'
  rw [← acyclic_cone_iff_quasiIso B, (conePackage _).cone_complex]
  exact fun n => (hC' n).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso s.toHomologicalComplex _)

variable (f φ hφ) in
/-- **The derived pushforward along a morphism of ringed topoi is computed on
`SheafHom^dg_{𝒜'}(𝒩, ℐ)`** for `ℐ` graded injective and K-injective: its comparison map is
invertible there. Resolve `SheafHom^dg_{𝒜'}(𝒩, ℐ)` by a graded injective K-injective module `𝒥`;
both are local for the quasi-isomorphisms between flat objects, so the direct image of the
resolution is a quasi-isomorphism, and the comparison map is invertible at `𝒥`. -/
theorem isIso_derivedToposPushforwardUnit_app_sheafHom
    (N : DifferentialGradedBimodule.{u, u, u} A A')
    {I : DifferentialGradedModule.{u, u, u} A'} (hI : IsDGInjective I) :
    IsIso ((derivedToposPushforwardUnit f A B φ hφ).app
      ((HomotopyCategory.quotient A).obj ((sheafHomFunctor N).obj I))) := by
  obtain ⟨J, s, hs, hKJ, hGJ⟩ := exists_quasiIso_isDGInjective_topos X A
    ((HomotopyCategory.quotient A).obj ((sheafHomFunctor N).obj I))
  obtain ⟨s₀, rfl⟩ := (HomotopyCategory.quotient A).map_surjective s
  have hs₀ := (quasiIsomorphisms_quotient_map_iff s₀).1 hs
  have h₁ : IsIso ((derivedToposPushforwardUnit f A B φ hφ).app J) :=
    isIso_derivedToposPushforwardUnit_app f A B φ hφ (I := J.as) ⟨hGJ, hKJ⟩
  have h₂ : IsIso ((toposPushforwardToDerived f A B φ hφ).map
      ((HomotopyCategory.quotient A).map s₀)) :=
    Localization.inverts (toDerivedCategory.{u, u, u} B) (quasiIsomorphisms.{u, u, u} B) _
      ((quasiIsomorphisms_quotient_map_iff _).2
        (quasiIso_toposPushforward_map φ hφ (isLocalOn_sheafHom (X := X.toRingedSite) N hI)
          (fun _ _ t ht _ _ => isLocal_quotient_obj_of_isKInjective.{u, u, u}
            (X := X.toRingedSite) (A := A) hKJ hGJ t ht) s₀ hs₀))
  have h₃ : IsIso ((toDerivedCategory.{u, u, u} A ⋙ derivedToposPushforward f A B φ hφ).map
      ((HomotopyCategory.quotient A).map s₀)) := by
    have := Localization.inverts (toDerivedCategory.{u, u, u} A)
      (quasiIsomorphisms.{u, u, u} A) _ hs
    exact inferInstanceAs (IsIso ((derivedToposPushforward f A B φ hφ).map
      ((toDerivedCategory.{u, u, u} A).map ((HomotopyCategory.quotient A).map s₀))))
  have hnat := (derivedToposPushforwardUnit f A B φ hφ).naturality
    ((HomotopyCategory.quotient A).map s₀)
  have : IsIso ((derivedToposPushforwardUnit f A B φ hφ).app _ ≫
      (toDerivedCategory.{u, u, u} A ⋙ derivedToposPushforward f A B φ hφ).map
        ((HomotopyCategory.quotient A).map s₀)) := by
    rw [← hnat]
    exact IsIso.comp_isIso' h₂ h₁
  exact IsIso.of_isIso_comp_right _ ((toDerivedCategory.{u, u, u} A ⋙
    derivedToposPushforward f A B φ hφ).map ((HomotopyCategory.quotient A).map s₀))

variable (f φ hφ) in
/-- The functor `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` of homotopy categories of [Stacks, Tag 0FTS] is
`K(SheafHom^dg_{𝒜'}(𝒩, -))` followed by `K(f_*)`. -/
theorem homotopyToposPushforwardSheafHom_eq_comp (N : DifferentialGradedBimodule.{u, u, u} A A') :
    homotopyToposPushforwardSheafHom f φ hφ N =
      homotopySheafHomFunctor (sheafHomHomotopyExtension N) ⋙
        homotopyToposPushforward (toposDirectImageModules (X := X) (Y := Y) f) φ hφ :=
  (HomotopyCategory.eq_descend _ (PreservesHomotopic.comp
      (sheafHomHomotopyExtension N).preservesHomotopic
      (preservesHomotopic_toposPushforward (toposDirectImageModules (X := X) (Y := Y) f) φ hφ)) _
      (quotient_comp_homotopyToposPushforwardSheafHom f φ hφ N)).trans
    (HomotopyCategory.descend_comp _ _ _ _)

variable (f φ hφ) in
/-- **`RT(ℳ) = Rf_* RSheafHom^dg_{𝒜'}(𝒩, ℳ)` for arbitrary right derived functors**, with their
comparison maps, of `K(SheafHom^dg_{𝒜'}(𝒩, -)) ⋙ K(f_*)` and of `K(SheafHom^dg_{𝒜'}(𝒩, -))`,
along a morphism of ringed topoi. The composite `RSheafHom^dg_{𝒜'}(𝒩, -) ⋙ Rf_*` is a right
derived functor of `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)`, because `RSheafHom^dg_{𝒜'}(𝒩, -)` is
computed on graded injective K-injective modules `ℐ` and `Rf_*` on `SheafHom^dg_{𝒜'}(𝒩, ℐ)`. -/
theorem exists_iso_rightDerived_toposPushforward_comp_sheafHom
    (N : DifferentialGradedBimodule.{u, u, u} A A')
    (RT : derivedCategory.{u, u, u} A' ⥤ derivedCategory.{u, u, u} B)
    (βT : (homotopySheafHomFunctor (sheafHomHomotopyExtension N) ⋙
        homotopyToposPushforward (toposDirectImageModules (X := X) (Y := Y) f) φ hφ) ⋙
          toDerivedCategory.{u, u, u} B ⟶ toDerivedCategory.{u, u, u} A' ⋙ RT)
    [RT.IsRightDerivedFunctor βT (quasiIsomorphisms.{u, u, u} A')]
    (RH : derivedCategory.{u, u, u} A' ⥤ derivedCategory.{u, u, u} A)
    (βH : homotopySheafHomFunctor (sheafHomHomotopyExtension N) ⋙ toDerivedCategory.{u, u, u} A ⟶
      toDerivedCategory.{u, u, u} A' ⋙ RH)
    (hRH : RH.IsRightDerivedFunctor βH (quasiIsomorphisms.{u, u, u} A')) :
    ∃ e : RT ≅ RH ⋙ derivedToposPushforward f A B φ hφ, ∀ K : HomotopyCategory.{u, u, u} A',
      βT.app K ≫ e.hom.app ((toDerivedCategory.{u, u, u} A').obj K) =
        (Functor.rightDerivedCompUnit βH (derivedToposPushforwardUnit f A B φ hφ)).app K := by
  have : (RH ⋙ derivedToposPushforward f A B φ hφ).IsRightDerivedFunctor
      (Functor.rightDerivedCompUnit βH (derivedToposPushforwardUnit f A B φ hφ))
      (quasiIsomorphisms.{u, u, u} A') :=
    Functor.isRightDerivedFunctor_comp_of_isIso (quasiIsomorphisms.{u, u, u} A') βH
      (derivedToposPushforwardUnit f A B φ hφ)
      (fun Z => IsKInjective Z.as ∧ GradedInjective Z.as)
      (exists_quasiIso_isDGInjective_topos X A')
      (fun I hI Z => bijective_toDerivedCategory_map_topos I hI Z)
      (fun I hI => isIso_app_of_isRightDerivedFunctor' (X := X.toRingedSite) RH βH hRH
        (I := I.as) ⟨hI.2, hI.1⟩)
      (fun I hI => isIso_derivedToposPushforwardUnit_app_sheafHom f φ hφ N (I := I.as)
        ⟨hI.2, hI.1⟩)
  refine ⟨Functor.rightDerivedUnique RT (RH ⋙ derivedToposPushforward f A B φ hφ) βT
    (Functor.rightDerivedCompUnit βH (derivedToposPushforwardUnit f A B φ hφ))
    (quasiIsomorphisms.{u, u, u} A'), fun K => ?_⟩
  rw [Functor.rightDerivedNatIso_hom, Functor.rightDerivedNatTrans_app, Iso.refl_hom,
    NatTrans.id_app]
  exact Category.id_comp _

variable (f φ hφ) in
/-- **`RT(ℳ) = Rf_* RSheafHom^dg_{𝒜'}(𝒩, ℳ)` for arbitrary right derived functors** of the functor
`ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` of [Stacks, Tag 0FTS] and of `K(SheafHom^dg_{𝒜'}(𝒩, -))`, with
their comparison maps, along a morphism of ringed topoi. -/
theorem exists_iso_rightDerived_toposPushforwardSheafHom
    (N : DifferentialGradedBimodule.{u, u, u} A A')
    (RT : derivedCategory.{u, u, u} A' ⥤ derivedCategory.{u, u, u} B)
    (βT : homotopyToposPushforwardSheafHom f φ hφ N ⋙ toDerivedCategory.{u, u, u} B ⟶
      toDerivedCategory.{u, u, u} A' ⋙ RT)
    [RT.IsRightDerivedFunctor βT (quasiIsomorphisms.{u, u, u} A')]
    (RH : derivedCategory.{u, u, u} A' ⥤ derivedCategory.{u, u, u} A)
    (βH : homotopySheafHomFunctor (sheafHomHomotopyExtension N) ⋙ toDerivedCategory.{u, u, u} A ⟶
      toDerivedCategory.{u, u, u} A' ⋙ RH)
    (hRH : RH.IsRightDerivedFunctor βH (quasiIsomorphisms.{u, u, u} A')) :
    ∃ e : RT ≅ RH ⋙ derivedToposPushforward f A B φ hφ, ∀ K : HomotopyCategory.{u, u, u} A',
      βT.app K ≫ e.hom.app ((toDerivedCategory.{u, u, u} A').obj K) =
        eqToHom (by rw [homotopyToposPushforwardSheafHom_eq_comp]) ≫
          (Functor.rightDerivedCompUnit βH (derivedToposPushforwardUnit f A B φ hφ)).app K := by
  have key : ∀ (T : HomotopyCategory.{u, u, u} A' ⥤ HomotopyCategory.{u, u, u} B)
      (hT : T = homotopySheafHomFunctor (sheafHomHomotopyExtension N) ⋙
        homotopyToposPushforward (toposDirectImageModules (X := X) (Y := Y) f) φ hφ)
      (RT : derivedCategory.{u, u, u} A' ⥤ derivedCategory.{u, u, u} B)
      (βT : T ⋙ toDerivedCategory.{u, u, u} B ⟶ toDerivedCategory.{u, u, u} A' ⋙ RT)
      [RT.IsRightDerivedFunctor βT (quasiIsomorphisms.{u, u, u} A')],
      ∃ e : RT ≅ RH ⋙ derivedToposPushforward f A B φ hφ, ∀ K : HomotopyCategory.{u, u, u} A',
        βT.app K ≫ e.hom.app ((toDerivedCategory.{u, u, u} A').obj K) =
          eqToHom (by rw [hT]) ≫
            (Functor.rightDerivedCompUnit βH (derivedToposPushforwardUnit f A B φ hφ)).app K := by
    intro T hT RT βT _
    subst hT
    obtain ⟨e, he⟩ :=
      exists_iso_rightDerived_toposPushforward_comp_sheafHom f φ hφ N RT βT RH βH hRH
    exact ⟨e, fun K => (he K).trans (Category.id_comp _).symm⟩
  exact key _ (homotopyToposPushforwardSheafHom_eq_comp f φ hφ N) RT βT

variable (f φ hφ) in
/-- The functor `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` of [Stacks, Tag 0FTS] followed by the
localization `K(Mod(ℬ, d)) ⥤ D(ℬ, d)`. -/
noncomputable abbrev toposPushforwardSheafHomToDerived
    (N : DifferentialGradedBimodule.{u, u, u} A A') :
    HomotopyCategory.{u, u, u} A' ⥤ derivedCategory.{u, u, u} B :=
  homotopyToposPushforwardSheafHom f φ hφ N ⋙ toDerivedCategory.{u, u, u} B

variable (f φ hφ) in
/-- **The right derived extension `RT : D(𝒜', d) ⥤ D(ℬ, d)` of the functor
`ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` of [Stacks, Tag 0FTS]** along a morphism of ringed topoi,
followed by the localization, as constructed in [Stacks, Tag 0FTN]. -/
noncomputable def derivedToposPushforwardSheafHom
    (N : DifferentialGradedBimodule.{u, u, u} A A') :
    derivedCategory.{u, u, u} A' ⥤ derivedCategory.{u, u, u} B :=
  rightDerivedExtension.{u, u, u} (X := X.toRingedSite) (A := A')
    (toposPushforwardSheafHomToDerived f φ hφ N)

variable (f φ hφ) in
/-- The comparison map `f_*SheafHom^dg_{𝒜'}(𝒩, ℳ) ⟶ RT(ℳ)`. -/
noncomputable def derivedToposPushforwardSheafHomUnit
    (N : DifferentialGradedBimodule.{u, u, u} A A') :
    toposPushforwardSheafHomToDerived f φ hφ N ⟶
      toDerivedCategory.{u, u, u} A' ⋙ derivedToposPushforwardSheafHom f φ hφ N :=
  rightDerivedExtensionUnit.{u, u, u} (X := X.toRingedSite) (A := A') _

/-- The comparison map `SheafHom^dg_{𝒜'}(𝒩, ℳ) ⟶ RSheafHom^dg_{𝒜'}(𝒩, ℳ)` of the derived internal
hom of [Stacks, Tag 0FTQ], over the site of a ringed topos. -/
noncomputable abbrev derivedSheafHomUnitTopos (N : DifferentialGradedBimodule.{u, u, u} A A') :
    homotopySheafHomFunctor (sheafHomHomotopyExtension N) ⋙ toDerivedCategory.{u, u, u} A ⟶
      toDerivedCategory.{u, u, u} A' ⋙ derivedSheafHom (X := X.toRingedSite) N :=
  derivedSheafHomUnit (X := X.toRingedSite) N

variable (f φ hφ) in
/-- **The isomorphism `RT ≅ RSheafHom^dg_{𝒜'}(𝒩, -) ⋙ Rf_*` of Tag 0FTT is compatible with the
comparison maps**: through the identification `homotopyToposPushforwardSheafHom_eq_comp` of the
functor of Tag 0FTS with `K(SheafHom^dg_{𝒜'}(𝒩, -)) ⋙ K(f_*)`, the comparison map of `RT` followed
by the isomorphism is the comparison map of the composite, whose value at `ℳ` is the comparison
map of `Rf_*` at `SheafHom^dg_{𝒜'}(𝒩, ℳ)` followed by `Rf_*` of that of
`RSheafHom^dg_{𝒜'}(𝒩, -)` at `ℳ` (`CategoryTheory.Functor.rightDerivedCompUnit_app`). -/
theorem exists_iso_derivedToposPushforwardSheafHom_fac
    (N : DifferentialGradedBimodule.{u, u, u} A A') :
    ∃ e : derivedToposPushforwardSheafHom f φ hφ N ≅
        derivedSheafHom (X := X.toRingedSite) N ⋙ derivedToposPushforward f A B φ hφ,
      ∀ K : HomotopyCategory.{u, u, u} A',
        (derivedToposPushforwardSheafHomUnit f φ hφ N).app K ≫
            e.hom.app ((toDerivedCategory.{u, u, u} A').obj K) =
          eqToHom (congrArg (fun T => (T ⋙ toDerivedCategory.{u, u, u} B).obj K)
              (homotopyToposPushforwardSheafHom_eq_comp f φ hφ N)) ≫
            (Functor.rightDerivedCompUnit (derivedSheafHomUnitTopos N)
              (derivedToposPushforwardUnit f A B φ hφ)).app K := by
  have : (derivedToposPushforwardSheafHom f φ hφ N).IsRightDerivedFunctor
      (derivedToposPushforwardSheafHomUnit f φ hφ N) (quasiIsomorphisms.{u, u, u} A') :=
    isRightDerivedFunctor_rightDerivedExtension.{u, u, u} (X := X.toRingedSite) (A := A') _
  obtain ⟨e, he⟩ := exists_iso_rightDerived_toposPushforwardSheafHom f φ hφ N _
    (derivedToposPushforwardSheafHomUnit f φ hφ N) _ (derivedSheafHomUnitTopos N)
    (isRightDerivedFunctor_derivedSheafHom (X := X.toRingedSite) N)
  exact ⟨e, he⟩

variable (f φ hφ) in
/-- **Stacks 0FTT.** Let `(f, f♯) : (Sh(𝒞), O_𝒞) ⟶ (Sh(𝒟), O_𝒟)` be a morphism of ringed topoi,
let `𝒜` and `𝒜'` be sheaves of differential graded `O_𝒞`-algebras, let `ℬ` be a sheaf of
differential graded `O_𝒟`-algebras, let `φ : ℬ ⟶ f_*𝒜` be a homomorphism and let `𝒩` be a
differential graded `(𝒜, 𝒜')`-bimodule. Let `RT : D(𝒜', d) ⥤ D(ℬ, d)` be the right derived
extension of the functor `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` of [Stacks, Tag 0FTS], let
`RSheafHom^dg_{𝒜'}(𝒩, -)` be the derived internal hom and `Rf_*` the derived pushforward of
[Stacks, Tag 0FTP]. Then

`RT(ℳ) = Rf_* RSheafHom^dg_{𝒜'}(𝒩, ℳ)`

functorially in `ℳ`: there is an isomorphism of functors `RT ≅ RSheafHom^dg_{𝒜'}(𝒩, -) ⋙ Rf_*`,
and it may be chosen compatible with the comparison maps, which is
`exists_iso_derivedToposPushforwardSheafHom_fac`.

The homomorphism `φ` is unital, as a homomorphism of differential graded algebras is in the
source; the direct image `f_*` is that of sheaves of modules along `(f, f♯)`. -/
@[stacks 0FTT]
theorem exists_iso_derivedToposPushforwardSheafHom
    (N : DifferentialGradedBimodule.{u, u, u} A A') :
    Nonempty (derivedToposPushforwardSheafHom f φ hφ N ≅
      derivedSheafHom (X := X.toRingedSite) N ⋙ derivedToposPushforward f A B φ hφ) :=
  ⟨(exists_iso_derivedToposPushforwardSheafHom_fac f φ hφ N).choose⟩

end SheafOfModules.DifferentialGradedModule

