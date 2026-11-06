module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLift
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeModuleOfAction
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyCollapseUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemEtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperModuleCohomologyFiniteAffine
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.Homology.DerivedLinear
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.RelativeSpecRepresentability.Basic

/-!
# Finiteness of cohomology of modules over an algebra, along a proper morphism

[Stacks, Tag 08AT] says: let `A` be a Noetherian ring, `B` a finitely generated graded
`A`-algebra, `f : X ⟶ Spec A` a proper morphism of algebraic spaces and `𝓑 = f^* B̃`; then for a
quasi-coherent graded `𝓑`-module `ℱ` of finite type, every `Hᵖ(X, ℱ)` is a finite `B`-module.

The grading plays no role in the source's proof, and this file proves the ungraded statement,
which is more general.  A `𝓑`-module is an `𝒪_X`-module `ℱ` together with a ring map
`ρ : B →+* End(ℱ)` which on `A` is multiplication by the pulled-back functions; `B` then acts on
`Hᵖ(X, ℱ)` by functoriality.  Finite type over `𝓑` is the condition that over every affine
étale chart `U` of `X` the sections `ℱ(U)` are generated over `𝒪(U)` by the `ρ(B)`-translates of
finitely many sections — that is, that `ℱ(U)` is a finite module over `𝒪(U) ⊗_A B`.

The proof is the source's.  Let `X' = Spec B ×_{Spec A} X` with projections `π : X' ⟶ X` and
`f' : X' ⟶ Spec B`.  Then `f'` is proper and `X'` is Noetherian; `ℱ = π_* ℱ'` for the
`𝒪_{X'}`-module `ℱ'` of `AlgebraicGeometry.Space.moduleOfAction`, which is coherent; and since
`π` is affine, `Hᵖ(X, ℱ) = Hᵖ(X', ℱ')` (Stacks 0D2U), compatibly with the action of `B`, so the
statement is Stacks 08AS for `f'`.

## Main definitions

* `CategoryTheory.Functor.endActionModule`: the module structure on `G X` over a ring acting on
  `X`.

## Main results

* `AlgebraicGeometry.Space.moduleFinite_cohomology_of_isProper_of_action`: the statement over
  affine schemes `W ⟶ V` of the site, with `W` Noetherian.
* `AlgebraicGeometry.Space.moduleFinite_cohomology_of_isProper_of_algebra_of_isAffine`: the
  same over an affine object `V` of the site over an arbitrary base, the functions on `V` being
  identified with a Noetherian ring `A`, for a finitely generated `A`-algebra `R`.
* `AlgebraicGeometry.Space.moduleFinite_cohomology_of_isProper_of_algebra`:
  **[Stacks, Tag 08AT]**, ungraded: `A` Noetherian, `R` a finitely generated `A`-algebra.
* `CategoryTheory.Functor.moduleFinite_endActionModule_of_iso`: finiteness of a module with an
  action transports along an equivariant comparison of additive groups.

## References

* [Stacks Project, Tag 08AT](https://stacks.math.columbia.edu/tag/08AT)
* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

private theorem comp_comp_eq_of_comm {C : Type*} [Category C] {P Q R : C} {a : P ⟶ P}
    {b : P ⟶ Q} {c : Q ⟶ Q} {k : Q ⟶ R} {d : R ⟶ R} (h1 : a ≫ b = b ≫ c)
    (h2 : c ≫ k = k ≫ d) : a ≫ b ≫ k = b ≫ k ≫ d := by
  rw [reassoc_of% h1, h2]

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]

/-- The module structure on `G.obj X` over a ring `R` acting on `X` by endomorphisms, for an
additive functor `G` into modules. -/
abbrev endActionModule {k : Type*} [Ring k] {R : Type*} [Semiring R] (G : C ⥤ ModuleCat k)
    [G.Additive] {X : C} (ρ : R →+* End X) : Module R (G.obj X) :=
  Module.compHom (G.obj X)
    ((ModuleCat.endRingEquiv (G.obj X)).toRingHom.comp
      ((Stacks.ModuleCatLift.mapEndRingHom G X).comp ρ))

/-- For the module structure `endActionModule G ρ`, the scalar `r` acts on `G.obj X` as the
endomorphism `G.map (ρ r)`. -/
theorem endActionModule_smul {k : Type*} [Ring k] {R : Type*} [Semiring R]
    (G : C ⥤ ModuleCat k) [G.Additive] {X : C} (ρ : R →+* End X) (r : R) (x : G.obj X) :
    letI := G.endActionModule ρ
    r • x = (G.map (ρ r).asHom).hom x :=
  rfl

/-- **Finiteness transported along an equivariant comparison.**  Let `ρ` be an action of `R` on
`X`, compatible through an isomorphism `e : X ≅ Y` with endomorphisms `σ r` of `Y`, and let `N` be
a module over `k'` whose additive group is identified with that of `G.obj Y` by `D`, compatibly
with endomorphisms `τ r` of `N` acting as the scalars `κ r`.  If `N` is finite over `R` through
`κ`, then `G.obj X` is finite over `R`. -/
theorem moduleFinite_endActionModule_of_iso {k k' R : Type*} [Ring k] [CommRing k']
    [CommRing R] (G : C ⥤ ModuleCat k) [G.Additive] {X Y : C} (ρ : R →+* End X) (e : X ≅ Y)
    (σ : R → End Y) (he : ∀ r, (ρ r).asHom ≫ e.hom = e.hom ≫ (σ r).asHom) (N : ModuleCat k') (κ : R →+* k')
    (τ : R → End N) (hτ : ∀ r y, (τ r).asHom.hom y = κ r • y)
    (D : (forget₂ (ModuleCat k') AddCommGrpCat).obj N ≅
      (forget₂ (ModuleCat k) AddCommGrpCat).obj (G.obj Y))
    (hD : ∀ r, (forget₂ (ModuleCat k') AddCommGrpCat).map (τ r).asHom ≫ D.hom =
      D.hom ≫ (forget₂ (ModuleCat k) AddCommGrpCat).map (G.map (σ r).asHom))
    [Module.Finite R ((ModuleCat.restrictScalars κ).obj N)] :
    letI := G.endActionModule ρ
    Module.Finite R (G.obj X) := by
  let := G.endActionModule ρ
  let I := (forget₂ (ModuleCat k) AddCommGrpCat).mapIso (G.mapIso e) ≪≫ D.symm
  have hI : ∀ r, (forget₂ (ModuleCat k) AddCommGrpCat).map (G.map (ρ r).asHom) ≫ I.hom =
      I.hom ≫ (forget₂ (ModuleCat k') AddCommGrpCat).map (τ r).asHom := by
    intro r
    have h1 := congrArg (fun φ => (forget₂ (ModuleCat k) AddCommGrpCat).map (G.map φ)) (he r)
    simp only [Functor.map_comp] at h1
    have h2 : (forget₂ (ModuleCat k) AddCommGrpCat).map (G.map (σ r).asHom) ≫ D.inv =
        D.inv ≫ (forget₂ (ModuleCat k') AddCommGrpCat).map (τ r).asHom := by
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
      exact (hD r).symm
    simp only [I, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    exact (comp_comp_eq_of_comm h1 h2).trans (Category.assoc _ _ _).symm
  let Ψ : G.obj X ≃ₗ[R] (ModuleCat.restrictScalars κ).obj N :=
    { I.addCommGroupIsoToAddEquiv with
      map_smul' := fun r x => (ConcreteCategory.congr_hom (hI r) x).trans (hτ r _) }
  exact Module.Finite.equiv Ψ.symm

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] hasInjectiveResolutions_modules

/-- The cohomology `Hⁱ(X, -)` of `𝒪_X`-modules on an algebraic space. -/
abbrev spaceCohomology (X : AlgebraicSpaces B S hS) (i : ℕ) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ ModuleCat.{u + 1}
      ↥(GlobalSectionRing
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) :=
  (globalSectionsFunctor.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O))).rightDerived i

/-- **Finiteness of cohomology of a module over an algebra, along a proper morphism to an affine
scheme.**  Let `q : W ⟶ V` be a morphism of affine schemes of the site with `W` locally
Noetherian, let `p : X ⟶ V` be proper and let `F` be a quasi-coherent `𝒪_X`-module with an action
`ρ` of `Γ(W)` which on `Γ(V)` is multiplication by the pulled-back functions, of finite type: over
every affine étale chart `U` of `X` the sections `F(U)` are generated over `Γ(U)` by the
`ρ(Γ(W))`-translates of finitely many sections.  Then `Hⁱ(X, F)` is a finite `Γ(W)`-module. -/
theorem moduleFinite_cohomology_of_isProper_of_action
    {V W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W)]
    (q : W ⟶ V) {X : AlgebraicSpaces B S hS} (p : X ⟶ schemeSpace V)
    (hp : IsProper B S hS p.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (ρ : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) →+* End F)
    (hρ : ∀ a, (ρ (((BigFppfOver.toScheme B S hS).map q).appTop a)).asHom =
      globalSmul _ (pullbackToGlobalFunctions B S hS X V p a) F)
    (hfin : ∀ U : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
      ∃ g : Finset (F.val.obj (op U)), Submodule.span (chartRing B S hS X.1 X.2 U)
        {x | ∃ r, ∃ y ∈ g, x = (ρ r).asHom.val.app (op U) y} = ⊤)
    (i : ℕ) :
    letI := (spaceCohomology B S hS X i).endActionModule ρ
    Module.Finite Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)
      ((spaceCohomology B S hS X i).obj F) := by
  -- the base change `X' = W ×_V X`
  let X' := pullback (schemeSpaceMap q) p
  let pr' : X' ⟶ schemeSpace W := pullback.fst _ _
  let pr : X' ⟶ X := pullback.snd _ _
  have sq : IsPullback pr' pr (schemeSpaceMap q) p := IsPullback.of_hasPullback _ _
  have hpr : IsAffineHom B S hS pr.hom :=
    IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom _ _ _ sq)
      (isAffineHom_yoneda_map B S hS q)
  have hrep := relativelyRepresentable_of_isAffineHom B S hS pr hpr
  have hpr' : IsProper B S hS pr'.hom :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback sq.flip hp
  have hN := isNoetherian_of_isProper_toAffine B S hS W inferInstance pr' hpr'
  have : Fact (HasEtaleLocalProperty B S hS X'.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hN.2.2⟩
  -- an affine étale chart of `X` surjective on points
  have hqc : IsQuasiCompactSpace B S hS X.1 :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS (isAlgebraicSpace_yoneda B S hS V)
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS V inferInstance) hp.2.1.2
  obtain ⟨U₀, f₀, het, hsurj⟩ := exists_affine_isSurjective_etaleChart B S hS X.1 X.2 hqc
  let U : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk f₀, het⟩
  obtain ⟨g, hg⟩ := hfin U U₀.property
  -- the module `F'` on `X'`, with `pr_* F' ≅ F`
  have hcoh := isCoherent_moduleOfAction B S hS p q F ρ sq hF hρ U U₀.property hsurj g hg
  have hF' := isQuasicoherentOnSite_moduleOfAction B S hS pr' pr F ρ hF
  have := isIso_toPushforwardModuleOfAction B S hS p q F ρ hrep sq hF hρ
  let F' := moduleOfAction B S hS pr' pr F ρ
  let s : ∀ r, F' ⟶ F' := fun r => globalSmul _ (pullbackFunction B S hS pr' r) F'
  let e : F ≅ (modulePushforward B S hS pr).obj F' :=
    asIso (toPushforwardModuleOfAction B S hS pr' pr F ρ hrep) ≪≫
      ((modulePushforwardChartIso B S hS pr hrep).app F').symm
  have he : ∀ r, (ρ r).asHom ≫ e.hom = e.hom ≫ (modulePushforward B S hS pr).map (s r) := by
    intro r
    show (ρ r).asHom ≫ toPushforwardModuleOfAction B S hS pr' pr F ρ hrep ≫
        (modulePushforwardChartIso B S hS pr hrep).inv.app F' =
      (toPushforwardModuleOfAction B S hS pr' pr F ρ hrep ≫
        (modulePushforwardChartIso B S hS pr hrep).inv.app F') ≫ _
    exact (comp_comp_eq_of_comm
      (toPushforwardModuleOfAction_comp_globalSmul B S hS pr' pr F ρ hrep r).symm
      ((modulePushforwardChartIso B S hS pr hrep).inv.naturality (s r))).trans
      (Category.assoc _ _ _).symm
  -- finiteness upstairs, by Stacks 08AS over `W`
  have := moduleFinite_cohomology_of_isProper_of_isAffine B W pr' hpr' F' i
  have := enoughInjectives_modules B S hS X'.1 X'.2
  have : Functor.Linear ↥(GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)))
      (spaceCohomology B S hS X' i) :=
    Stacks.DerivedLinear.rightDerived_linear (globalSectionsFunctor.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O))) i
  have hmap : ∀ r, (spaceCohomology B S hS X' i).map (s r) =
      pullbackFunction B S hS pr' r • 𝟙 _ :=
    fun r => (congrArg (spaceCohomology B S hS X' i).map
      (globalSmul_eq_smul_id _ (pullbackFunction B S hS pr' r) F')).trans
      ((Functor.map_smul (spaceCohomology B S hS X' i) (pullbackFunction B S hS pr' r)
        (𝟙 F')).trans (congrArg (pullbackFunction B S hS pr' r • ·)
          ((spaceCohomology B S hS X' i).map_id F')))
  -- the comparison of the cohomologies, by Stacks 0D2U
  exact (spaceCohomology B S hS X i).moduleFinite_endActionModule_of_iso ρ e
    (fun r => End.of ((modulePushforward B S hS pr).map (s r)))
    he ((spaceCohomology B S hS X' i).obj F') (pullbackRingHom B W pr')
    (fun r => End.of ((spaceCohomology B S hS X' i).map (s r)))
    (fun r y => by rw [hmap]; rfl)
    (cohomologyIsoOfIsAffineHom B S hS pr hpr F' hF' i)
    (fun r => cohomologyIsoOfIsAffineHom_hom_naturality B S hS pr hpr (s r) hF' hF' i)

section AffineAlgebra

variable {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  (A : Type u) [CommRing A] (α : A ≃+* Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
  (R : Type u) [CommRing R] [Algebra A R] [Algebra.FiniteType A R]

/-- The structure morphism `Spec R ⟶ V` of a finitely generated algebra over the functions on an
affine object `V` of the site, the functions on `V` being identified with `A` by `α`. -/
noncomputable def specAlgebraToAffine : Spec (.of R) ⟶ (BigFppfOver.toScheme B S hS).obj V :=
  Spec.map (CommRingCat.ofHom ((algebraMap A R).comp α.symm.toRingHom)) ≫
    ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv

include hS α in
/-- The spectrum of a finitely generated algebra over the functions on an affine object of the
site is an object of the site: it is of finite type over that object. -/
theorem contains_spec_of_isAffine : B.Contains (Spec (.of R)) := by
  have : LocallyOfFiniteType (specAlgebraToAffine B S hS A α R) := by
    have : (CommRingCat.ofHom ((algebraMap A R).comp α.symm.toRingHom)).hom.FiniteType :=
      RingHom.FiniteType.comp (RingHom.finiteType_algebraMap.2 inferInstance)
        (RingHom.FiniteType.of_surjective _ α.symm.surjective)
    have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom ((algebraMap A R).comp
        α.symm.toRingHom))) := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 this
    exact inferInstanceAs (LocallyOfFiniteType (_ ≫ _))
  exact (Scheme.size_le_of_locallyOfFiniteType (specAlgebraToAffine B S hS A α R)).trans_lt
    V.left.2

/-- The spectrum of a finitely generated algebra over the functions on an affine object `V`, as
an object of the big fppf site over `S`. -/
noncomputable abbrev specAlgebraObjectOver : BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (specAlgebraToAffine B S hS A α R ≫ B.inclusion.map V.hom) :
    B.obj (contains_spec_of_isAffine B S hS A α R) ⟶ B.obj hS)

/-- The structure morphism of `Spec R` over `V`. -/
noncomputable abbrev specAlgebraMapOver : specAlgebraObjectOver B S hS A α R ⟶ V :=
  Over.homMk (ObjectProperty.homMk (specAlgebraToAffine B S hS A α R)) rfl

omit [Algebra.FiniteType A R] in
/-- On global sections, the morphism `Spec R ⟶ V` sends a function `x` on `V` to the image in
`Γ(Spec R)` of `algebraMap A R (α.symm x)`. -/
theorem specAlgebraToAffine_appTop (x : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    (specAlgebraToAffine B S hS A α R).appTop x =
      (Scheme.ΓSpecIso (.of R)).inv (algebraMap A R (α.symm x)) := by
  rw [specAlgebraToAffine, Scheme.Hom.comp_appTop, Stacks.RelativeSpec.isoSpec_inv_appTop]
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ((algebraMap A R).comp
      α.symm.toRingHom))).symm x

/-- **Stacks 08AT over an affine object of the site.**  Let `V` be an affine object of the big
fppf site over `S` whose functions are identified with a Noetherian ring `A` by `α`, let `R` be a
finitely generated `A`-algebra and `p : X ⟶ V` a proper morphism of algebraic spaces.  Let `F` be
a quasi-coherent `𝒪_X`-module with an action `ρ : R →+* End F` restricting on `A` to
multiplication by the pulled-back functions, such that over every affine étale chart `U` of `X`
the sections `F(U)` are generated over `𝒪(U)` by the `ρ(R)`-translates of finitely many sections.
Then `Hⁱ(X, F)` is a finite `R`-module for every `i`. -/
theorem moduleFinite_cohomology_of_isProper_of_algebra_of_isAffine [IsNoetherianRing A]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V) (hf : IsProper B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) (ρ : R →+* End F)
    (hρ : ∀ a, (ρ (algebraMap A R a)).asHom =
      globalSmul _ (pullbackToGlobalFunctions B S hS X V f (α a)) F)
    (hfin : ∀ U : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
      ∃ g : Finset (F.val.obj (op U)), Submodule.span (chartRing B S hS X.1 X.2 U)
        {x | ∃ r, ∃ y ∈ g, x = (ρ r).asHom.val.app (op U) y} = ⊤)
    (i : ℕ) :
    letI := (spaceCohomology B S hS X i).endActionModule ρ
    Module.Finite R ((spaceCohomology B S hS X i).obj F) := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing A R
  let e : Γ((BigFppfOver.toScheme B S hS).obj (specAlgebraObjectOver B S hS A α R), ⊤) →+* R :=
    (Scheme.ΓSpecIso (.of R)).hom.hom
  have he : Function.Bijective e :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (specAlgebraObjectOver B S hS A α R)) :=
    inferInstanceAs (IsAffine (Spec (.of R)))
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj
      (specAlgebraObjectOver B S hS A α R)) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of R)))
  have hρ' : ∀ x, ((ρ.comp e) (((BigFppfOver.toScheme B S hS).map
      (specAlgebraMapOver B S hS A α R)).appTop x)).asHom =
      globalSmul _ (pullbackToGlobalFunctions B S hS X V f x) F := by
    intro x
    show (ρ (e ((specAlgebraToAffine B S hS A α R).appTop x))).asHom = _
    rw [specAlgebraToAffine_appTop]
    show (ρ ((Scheme.ΓSpecIso (.of R)).hom.hom ((Scheme.ΓSpecIso (.of R)).inv.hom
      (algebraMap A R (α.symm x))))).asHom = _
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, hρ, α.apply_symm_apply]
  have hfin' := moduleFinite_cohomology_of_isProper_of_action B S hS
    (specAlgebraMapOver B S hS A α R) f hf F hF (ρ.comp e) hρ' (fun U hU => by
      obtain ⟨g, hg⟩ := hfin U hU
      refine ⟨g, top_unique ?_⟩
      rw [← hg]
      refine Submodule.span_mono ?_
      rintro _ ⟨r, y, hy, rfl⟩
      obtain ⟨r', rfl⟩ := he.2 r
      exact ⟨r', y, hy, rfl⟩) i
  let := (spaceCohomology B S hS X i).endActionModule (ρ.comp e)
  let := (spaceCohomology B S hS X i).endActionModule ρ
  have : RingHomSurjective e := ⟨he.2⟩
  let l : @LinearMap _ _ _ _ e ((spaceCohomology B S hS X i).obj F)
      ((spaceCohomology B S hS X i).obj F) _ _
      ((spaceCohomology B S hS X i).endActionModule (ρ.comp e))
      ((spaceCohomology B S hS X i).endActionModule ρ) :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (l.finite_iff_of_bijective Function.bijective_id).1 hfin'

end AffineAlgebra

section Algebra

variable (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A))) (R : Type u) [CommRing R]
  [Algebra A R] [Algebra.FiniteType A R]

/-- A function on an object of the site over `Spec A` pulled back from the base is the scalar of
`A`, read through `Γ(Spec A) ≅ A`. -/
theorem pullbackToGlobalFunctions_baseObject {X : AlgebraicSpaces B (Spec (.of A)) hA}
    (p : X ⟶ schemeSpace (baseObject A B hA)) (a : A) :
    pullbackToGlobalFunctions B (Spec (.of A)) hA X (baseObject A B hA) p
      ((Scheme.ΓSpecIso (.of A)).inv a) = baseRingHom A B hA X.1 X.2 a := by
  refine Subtype.ext (funext fun U => ?_)
  have hw : (yoneda.preimage (U.unop.1.hom ≫ p.hom)).left =
      ((SmallEtale.toOver B (Spec (.of A)) hA X.1).obj U.unop).hom :=
    (Category.comp_id _).symm.trans (Over.w (yoneda.preimage (U.unop.1.hom ≫ p.hom)))
  show (Scheme.Γ.map (B.inclusion.map (yoneda.preimage (U.unop.1.hom ≫ p.hom)).left).op)
      ((Scheme.ΓSpecIso (.of A)).inv a) = _
  exact (congrArg (fun g : ((SmallEtale.toOver B (Spec (.of A)) hA X.1).obj U.unop).left ⟶
      B.obj hA => (Scheme.Γ.map (B.inclusion.map g).op)
    ((Scheme.ΓSpecIso (.of A)).inv a)) hw)

/-- **Stacks 08AT.**  Let `A` be a Noetherian ring, `R` a finitely generated `A`-algebra and
`f : X ⟶ Spec A` a proper morphism of algebraic spaces.  Let `F` be a quasi-coherent
`𝒪_X`-module which is a module over `f^* R̃` of finite type: an action `ρ : R →+* End F`
restricting on `A` to multiplication by the scalars, such that over every affine étale chart `U`
of `X` the sections `F(U)` are generated over `𝒪(U)` by the `ρ(R)`-translates of finitely many
sections.
Then `Hⁱ(X, F)` is a finite `R`-module for every `i`.

The source states this for a graded `R` and a graded module; the grading is not used, and the
graded module `Hⁱ(X, F)` of the source is the cohomology of the total module `F` here. -/
@[stacks 08AT "ungraded, which is more general: the grading is never used by the proof"]
theorem moduleFinite_cohomology_of_isProper_of_algebra [IsNoetherianRing A]
    {X : AlgebraicSpaces B (Spec (.of A)) hA} (f : X ⟶ schemeSpace (baseObject A B hA))
    (hf : IsProper B (Spec (.of A)) hA f.hom) (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (ρ : R →+* End F)
    (hρ : ∀ a, (ρ (algebraMap A R a)).asHom = globalSmul _ (baseRingHom A B hA X.1 X.2 a) F)
    (hfin : ∀ U : SmallEtale B (Spec (.of A)) hA X.1,
      IsAffine ((SmallEtale.toOver B (Spec (.of A)) hA X.1 ⋙
        BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) →
      ∃ g : Finset (F.val.obj (op U)), Submodule.span (chartRing B (Spec (.of A)) hA X.1 X.2 U)
        {x | ∃ r, ∃ y ∈ g, x = (ρ r).asHom.val.app (op U) y} = ⊤)
    (i : ℕ) :
    letI := (spaceCohomology B (Spec (.of A)) hA X i).endActionModule ρ
    Module.Finite R ((spaceCohomology B (Spec (.of A)) hA X i).obj F) := by
  have : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (baseObject A B hA)) :=
    inferInstanceAs (IsAffine (Spec (.of A)))
  refine moduleFinite_cohomology_of_isProper_of_algebra_of_isAffine B (Spec (.of A)) hA
    (V := baseObject A B hA) A (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv R f hf F
    hF ρ (fun a => ?_) hfin i
  rw [hρ a]
  exact congrArg (fun φ => globalSmul _ φ F)
    (pullbackToGlobalFunctions_baseObject B A hA f a).symm

end Algebra

end AlgebraicGeometry.Space

end
