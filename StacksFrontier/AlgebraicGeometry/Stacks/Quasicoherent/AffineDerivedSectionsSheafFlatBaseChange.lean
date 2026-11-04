module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleQuasicoherentDerivedChainTriangulated
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineCoveringFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatObjectAtlasCovers
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDerivedSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentSemiorthogonalDecompositionSucc
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineFppfDerivedModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteCartesianModules
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesSheafAnyUniverse

/-!
# The base change property of Stacks 0H15 forces `D_{LQCoh^fbc}(𝒪_𝒳)`

Let `𝒳` be an algebraic stack and `K` an object of `D(𝒳_{fppf}, 𝒪)` with module sections in
`Type (u + 1)` having the base change property of Stacks 0H15
(`AlgebraicGeometry.Stack.FlatFppf.HasAffineDerivedSectionsBaseChange`): the maps
`RΓ(x', K) ⊗^L_{𝒪(x')} 𝒪(x) ⟶ RΓ(x, K)` are quasi-isomorphisms along the morphisms of
`𝒳_{affine}`. This file proves that every cohomology sheaf of `K` then lies in
`LQCoh^fbc(𝒪_𝒳)`: over the affine objects the cohomology sheaves are computed by `RΓ`, and they
are cartesian along flat arrows; a presheaf of modules cartesian along flat arrows of `𝒳_{affine}`
is an fppf sheaf (faithfully flat descent). This is Step 1 of the proof of Stacks 0H16, and it is
used in the proof of Stacks 0H15 itself (the case of an affine scheme).

## Main results

* `AlgebraicGeometry.Stack.AffineCategory.isSheaf_of_isIso_restrictionBaseChange_flat`: a presheaf
  of modules on `𝒳_{affine}` cartesian along flat arrows is an fppf sheaf.
* `Stacks.Sites.isIso_toSheafify_app_of_isSheaf_comp`: the sheafification unit is invertible on a
  dense subsite where the presheaf is a sheaf.

In the namespace `AlgebraicGeometry.Stack.FlatFppf`:

* `isIso_hypercohomologyEdge_app_of_hasAffineDerivedSectionsBaseChange`: with the base change
  property, `H^q(y, K) ≅ Γ(y, H^q K)` over affine objects `y`.
* `derivedCategoryB_sheafFlatBaseChangeModulesSucc_of_hasAffineDerivedSectionsBaseChange`: the
  base change property forces `K ∈ D_{LQCoh^fbc}(𝒪_𝒳)`.

## References

* [Stacks Project, Tag 0H15](https://stacks.math.columbia.edu/tag/0H15)
* [Stacks Project, Tag 0H16](https://stacks.math.columbia.edu/tag/0H16)
* [Stacks Project, Tag 0H0B](https://stacks.math.columbia.edu/tag/0H0B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u v w t r m i

/-! ### Cartesian along flat arrows: the sheaf condition on affine sites -/

/-- Flatness of morphisms of schemes as a `MorphismProperty`, so that instance search finds the
stability instances of its precoverage. -/
private abbrev flatSchemeMorphisms : MorphismProperty AlgebraicGeometry.Scheme.{u} :=
  @AlgebraicGeometry.Flat

namespace Stacks.PresheafOfModules

open _root_.AlgebraicGeometry

/-- **A presheaf of modules which is cartesian along the arrows lying over flat morphisms is a
sheaf for a topology all of whose covering sieves are refined by finite flat covering families.**

This is `Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_refinements'` with the cartesian
condition asked only along flat arrows: the descent argument
(`Stacks.PresheafOfModules.isSheafFor_of_isIso_restrictionBaseChange`) uses it only along the
arrows of a flat covering family and along the arrows from its double overlaps, which are flat. -/
theorem isSheaf_of_isIso_restrictionBaseChange_flat_of_flat_refinements
    {C : Type v} [Category.{w} C] [HasPullbacks C]
    (L : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan L]
    (R : Cᵒᵖ ⥤ CommRingCat.{r})
    (hff : ∀ {U : C} (E : PreZeroHypercover.{i} U), Finite E.I₀ →
      (E.map L).presieve₀ ∈ Scheme.precoverage @Flat (L.obj U) →
      (RingHom.pi (fun k => (R.map (E.f k).op).hom)).FaithfullyFlat)
    (hpo : ∀ {X Y Z P : C} {fst : P ⟶ X} {snd : P ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z},
      IsPullback fst snd a b →
      IsPushout (R.map a.op) (R.map b.op) (R.map fst.op) (R.map snd.op))
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : C} (f : X ⟶ Y), Flat (L.map f) →
      IsIso (restrictionBaseChange.{v, w, r, m} M f.op))
    (J : GrothendieckTopology C)
    (hJ : ∀ {U : C} (S : Sieve U), S ∈ J U →
      ∃ E : PreZeroHypercover.{i} U, Finite E.I₀ ∧
        (E.map L).presieve₀ ∈ Scheme.precoverage @Flat (L.obj U) ∧ E.sieve₀ ≤ S) :
    Presheaf.IsSheaf J M.presheaf := by
  apply Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget
  intro U S hS
  obtain ⟨E, hfin, hE, hES⟩ := hJ S hS
  let _ := hfin
  apply Presieve.isSheafFor_subsieve _ hES
  intro V f
  let K := (Scheme.precoverage @Flat).comap L
  let _ : K.IsStableUnderBaseChange :=
    inferInstanceAs (Precoverage.IsStableUnderBaseChange
      ((Scheme.precoverage flatSchemeMorphisms.{u}).comap L))
  have he : E.presieve₀ ∈ K U := by
    show E.presieve₀.map L ∈ (Scheme.precoverage @Flat) (L.obj U)
    simpa only [PreZeroHypercover.presieve₀_map] using hE
  have he' : (E.pullback₂ f).presieve₀ ∈ K V :=
    K.mem_coverings_of_isPullback _ he _ _ _
      (fun i => (IsPullback.of_hasPullback (E.f i) f).flip)
  let _ : Finite (E.pullback₂ f).I₀ := hfin
  have he'' : ((E.pullback₂ f).map L).presieve₀ ∈ Scheme.precoverage @Flat (L.obj V) := by
    simpa only [K, Precoverage.mem_comap_iff, PreZeroHypercover.presieve₀_map] using he'
  have hfl : ∀ k, Flat (L.map ((E.pullback₂ f).f k)) :=
    ((Scheme.presieve₀_mem_precoverage_iff _).1 he'').2
  let g := (E.pullback₂ f).f
  have hfst : ∀ k l, Flat (L.map (pullback.fst (g k) (g l) ≫ g k)) := fun k l => by
    have hsq := ((IsPullback.of_hasPullback (g k) (g l)).map L).flip
    have : Flat (L.map (pullback.fst (g k) (g l))) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat) hsq (hfl l)
    have := hfl k
    rw [L.map_comp]
    infer_instance
  have h := isSheafFor_of_isIso_restrictionBaseChange R M (E.pullback₂ f).X g
    (fun k l => pullback (g k) (g l)) (fun k l => pullback.fst (g k) (g l))
    (fun k l => pullback.snd (g k) (g l)) (fun _ _ => pullback.condition)
    (hff (E.pullback₂ f) inferInstance he'')
    (fun k l => hpo (IsPullback.of_hasPullback (g k) (g l))) (fun k => hM _ (hfl k))
    (fun k l => hM _ (hfst k l))
  change Presieve.IsSheafFor _ (E.pullback₂ f).presieve₀ at h
  rw [PreZeroHypercover.presieve₀_pullback₁, Presieve.isSheafFor_iff_generate,
    Sieve.pullbackArrows_comm] at h
  exact h

end Stacks.PresheafOfModules

namespace AlgebraicGeometry.Stack.AffineCategory

open Stacks.PresheafOfModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (R : (AffineCategory B S hS p)ᵒᵖ ⥤ CommRingCat.{u})
  (hR : R = (toScheme B S hS p).op ⋙ Scheme.Γ)
include hR

/-- **A presheaf of modules on the affine subcategory which is cartesian along the arrows lying
over flat morphisms is a sheaf** for each of the five associated affine topologies of Stacks
0H0A; `AlgebraicGeometry.Stack.AffineCategory.isSheaf_of_cartesian` asks for all arrows. -/
theorem isSheaf_of_isIso_restrictionBaseChange_flat (hp : p.IsFiberedInGroupoids) (τ : SiteKind)
    (M : PresheafOfModules.{max m u} (R ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {x y : AffineCategory B S hS p} (f : x ⟶ y), Flat ((toScheme B S hS p).map f) →
      IsIso (restrictionBaseChange.{v, w, u, m} M f.op)) :
    Presheaf.IsSheaf (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS τ))
      M.presheaf := by
  have := hasPullbacks B S hS p hp
  have := preservesPullbacks_toScheme B S hS p hp
  refine isSheaf_of_isIso_restrictionBaseChange_flat_of_flat_refinements
    (toScheme B S hS p) R ?_ ?_ M hM _ ?_
  · intro x E hfin hE
    exact faithfullyFlat_pi_map B S hS p R hR E hfin hE
  · intro _ _ _ _ _ _ _ _ h
    exact isPushout_map B S hS p R hR hp h
  · intro x T hT
    obtain ⟨E, hfin, hE, -, hle⟩ := exists_finite_flat_covering B S hS p hp τ T hT
    exact ⟨E, hfin, hE, hle⟩

end AlgebraicGeometry.Stack.AffineCategory


/-! ### Sheafification along a dense subsite -/

namespace Stacks.Sites

/-- **The sheafification unit is invertible at the objects of a dense subsite on which the
presheaf is already a sheaf.** Let `G : C ⥤ D` be a dense subsite and `A` an abelian presheaf on
`D` whose restriction `G^* A` is a sheaf. The unit `A ⟶ A^#` is locally bijective, hence so is its
restriction `G^* A ⟶ G^* A^#` (`G` being cocontinuous), a morphism between sheaves, which is
therefore an isomorphism; on sections over `G X` it is the unit. -/
theorem isIso_toSheafify_app_of_isSheaf_comp {C : Type*} [Category* C] {D : Type*} [Category* D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D) [G.IsDenseSubsite J K]
    {A : Type*} [Category* A] {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    [HasSheafify K A] [K.WEqualsLocallyBijective A] [(forget A).ReflectsIsomorphisms]
    [J.HasSheafCompose (forget A)]
    (P : Dᵒᵖ ⥤ A) (hP : Presheaf.IsSheaf J (G.op ⋙ P)) (X : C) :
    IsIso ((toSheafify K P).app (op (G.obj X))) := by
  obtain ⟨h₁, h₂⟩ := (K.W_iff_isLocallyBijective (toSheafify K P)).1 (K.W_toSheafify P)
  have i₁ : Presheaf.IsLocallyInjective J (Functor.whiskerLeft G.op (toSheafify K P)) :=
    Presheaf.isLocallyInjective_whisker J K G _
  have i₂ : Presheaf.IsLocallySurjective J (Functor.whiskerLeft G.op (toSheafify K P)) :=
    Presheaf.isLocallySurjective_whisker J K G _
  let φ : (⟨G.op ⋙ P, hP⟩ : Sheaf J A) ⟶ ⟨G.op ⋙ (sheafify K P), G.op_comp_isSheaf J K _⟩ :=
    ⟨Functor.whiskerLeft G.op (toSheafify K P)⟩
  have : IsIso φ := (Sheaf.isLocallyBijective_iff_isIso φ).1 ⟨i₁, i₂⟩
  have : IsIso φ.hom := inferInstanceAs (IsIso ((sheafToPresheaf J A).map φ))
  exact inferInstanceAs (IsIso (φ.hom.app (op X)))

end Stacks.Sites

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

section SheafFlatBaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasSheafify_fppfTopology_largeSections
  wEqualsLocallyBijective_fppfTopology_largeSections

attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

open Stacks.Cohomology.HypercohomologyEdge
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange

attribute [local instance] isGrothendieckAbelian_ambientModulesSucc

-- the small-Hom model of the derived category of presheaves of modules has a free universe,
-- which instance search cannot solve; the edge morphism is read at the standard model
attribute [-instance] Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)

/-! ### Step 1: the base change property forces `D_{LQCoh^fbc}` -/

/-- The adjoint transpose of `f = α ≫ β ≫ G γ` is invertible if `α` and `γ` are and the transpose
of `β` is. -/
private theorem isIso_homEquiv_symm_of_eq_comp {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X Y : C} {Z W : D} (f : X ⟶ G.obj W) (α : X ⟶ Y)
    (β : Y ⟶ G.obj Z) (γ : Z ⟶ W) [IsIso α] [IsIso γ] (hβ : IsIso ((adj.homEquiv _ _).symm β))
    (e : f = α ≫ β ≫ G.map γ) : IsIso ((adj.homEquiv _ _).symm f) := by
  rw [e, Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm]
  infer_instance

/-- **Along a flat arrow of `𝒳_{affine}`, the base change property of Stacks 0H15 makes the
cohomology of `RΓ(-, K)` cartesian**: for `a : x ⟶ x'` over a flat morphism of affine schemes,
the adjoint transpose `H^q(x', K) ⊗_{𝒪(x')} 𝒪(x) ⟶ H^q(x, K)` of the derived restriction is an
isomorphism, being `H^q(x', K) ⊗ 𝒪(x) ≅ H^q(RΓ(x', K) ⊗^L 𝒪(x))` (flat base change commutes with
cohomology) followed by `H^q` of the base change map. -/
theorem isIso_homEquiv_symm_derivedSectionsRestrictHomology_of_flat
    (K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
    (hK : HasAffineDerivedSectionsBaseChange B S hS 𝒳 K)
    {x x' : 𝒳.val.val.obj} (a : x ⟶ x')
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)))
    (hx' : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x')))
    (ha : Flat (B.inclusion.map (𝒳.val.val.p.map a).left)) (q : ℤ) :
    haveI : IsGrothendieckAbelian.{u + 1}
        (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) :=
      SheafOfModules.isGrothendieckAbelian_of_univLE.{u + 1} _
    haveI : PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1}
        ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.op).hom) :=
      Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteLimits _
    haveI : PreservesFiniteColimits (ModuleCat.restrictScalars.{u + 1}
        ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.op).hom) :=
      Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteColimits _
    IsIso (((moduleBaseChangeAdj.{u, u + 1} ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.op)
        (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x')
        (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x)).homEquiv _ _).symm
      ((derivedSectionsRestrictHomology.{_, _, _, u + 1, u + 1}
        (ambientRingStructureSheaf B S hS 𝒳) a q).app K)) := by
  have : IsGrothendieckAbelian.{u + 1}
      (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) :=
    SheafOfModules.isGrothendieckAbelian_of_univLE.{u + 1} _
  let O := ambientRingStructureSheaf B S hS 𝒳
  have : PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1} (O.obj.map a.op).hom) :=
    Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteLimits _
  have : PreservesFiniteColimits (ModuleCat.restrictScalars.{u + 1} (O.obj.map a.op).hom) :=
    Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteColimits _
  have h := homEquiv_symm_homology_eq.{u, u + 1} (O.obj.map a.op)
    (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x') (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x)
    ((derivedSections.{_, _, _, u + 1, u + 1} O x').obj K)
    ((derivedSections.{_, _, _, u + 1, u + 1} O x).obj K)
    ((derivedSectionsRestrict.{_, _, _, u + 1, u + 1} O a).app K) q
  have := isIso_baseChangeHomologyComparison_of_flat.{u, u + 1} (O.obj.map a.op)
    (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x') (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x)
    (flat_structureSheaf_map_of_flat B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      B.topology le_rfl a ha hx hx') ((derivedSections.{_, _, _, u + 1, u + 1} O x').obj K) q
  have := hK a hx hx'
  have hbc : IsIso ((DerivedCategory.homologyFunctor _ q).map
      (((dBaseChangeAdj.{u, u + 1} (O.obj.map a.op) (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x')
        (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x)).homEquiv _ _).symm
          ((derivedSectionsRestrict.{_, _, _, u + 1, u + 1} O a).app K))) :=
    Functor.map_isIso _ (derivedSectionsBaseChange B S hS 𝒳 a K)
  exact (congrArg IsIso h).mpr inferInstance

/-- **Over an affine object, the base change property of Stacks 0H15 makes hypercohomology the
sections of the cohomology sheaves**: if `K` has the base change property, the edge morphism
`H^q(y, K) ⟶ Γ(y, H^q K)` is an isomorphism for every `y` lying over an affine scheme.

The edge morphism is the sheafification unit of the presheaf `P = H^q(RΓ(-, K))`
(`Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_iff`). By the base change
property `P` is cartesian along flat arrows of `𝒳_{affine}`
(`isIso_homEquiv_symm_derivedSectionsRestrictHomology_of_flat`), so its restriction to the affine
subsite is an fppf sheaf (faithfully flat descent,
`AlgebraicGeometry.Stack.AffineCategory.isSheaf_of_isIso_restrictionBaseChange_flat`), and the
sheafification unit is invertible there (`Stacks.Sites.isIso_toSheafify_app_of_isSheaf_comp`,
the affine subsite being dense, Stacks 0H0B). -/
theorem isIso_hypercohomologyEdge_app_of_hasAffineDerivedSectionsBaseChange
    (K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
    (hK : HasAffineDerivedSectionsBaseChange B S hS 𝒳 K)
    (y : 𝒳.val.val.obj) (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y)))
    (q : ℤ) :
    IsIso ((hypercohomologyEdge.{_, _, _, u + 1, u + 1} (ambientRingStructureSheaf B S hS 𝒳) y
      q).app K) := by
  let O := ambientRingStructureSheaf B S hS 𝒳
  let P := (DerivedCategory.homologyFunctor (PresheafOfModules.{u + 1} O.obj) q).obj
    ((derivedSectionsPresheaf.{_, _, _, u + 1, u + 1} O).obj K)
  -- `P` is cartesian along flat arrows between objects lying over affine schemes
  have hcart : ∀ {x x' : 𝒳.val.val.obj} (a : x ⟶ x'),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x')) →
      Flat (B.inclusion.map (𝒳.val.val.p.map a).left) →
      IsIso (((moduleBaseChangeAdj.{u, u + 1} (O.obj.map a.op)
        (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x')
        (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x)).homEquiv _ _).symm
          ((PresheafOfModules.restriction O.obj a.op).app P)) := by
    intro x x' a hx hx' ha
    have : PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1} (O.obj.map a.op).hom) :=
      Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteLimits _
    have : PreservesFiniteColimits (ModuleCat.restrictScalars.{u + 1} (O.obj.map a.op).hom) :=
      Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteColimits _
    have hD := isIso_homEquiv_symm_derivedSectionsRestrictHomology_of_flat B S hS 𝒳 K hK a hx hx'
      ha q
    have h1 := sectionsEvaluationIso_restrict.{_, _, _, u + 1, u + 1} O a q K
    have e : (PresheafOfModules.restriction O.obj a.op).app P =
        (sectionsEvaluationIso O x' q).hom.app K ≫ (derivedSectionsRestrictHomology O a q).app K ≫
          (ModuleCat.restrictScalars.{u + 1} (O.obj.map a.op).hom).map
            ((sectionsEvaluationIso O x q).inv.app K) := by
      rw [reassoc_of% h1, ← Functor.map_comp, Iso.hom_inv_id_app]
      exact ((congrArg (fun m => (PresheafOfModules.restriction O.obj a.op).app P ≫ m)
        ((ModuleCat.restrictScalars.{u + 1} (O.obj.map a.op).hom).map_id _)).trans
          (Category.comp_id _)).symm
    exact isIso_homEquiv_symm_of_eq_comp _ _ _ _ _ hD e
  -- so its restriction to the affine subsite is an fppf sheaf
  have hPs : Presheaf.IsSheaf (affineFppfRingedSite B S hS 𝒳).J
      ((AffineCategory.inclusion B S hS 𝒳.val.val.p).op ⋙ P.presheaf) :=
    AffineCategory.isSheaf_of_isIso_restrictionBaseChange_flat B S hS 𝒳.val.val.p
      (affineStructureCommPresheaf B S hS 𝒳.val.val.p) rfl 𝒳.val.isFiberedInGroupoids .fppf
      ((PresheafOfModules.pushforward₀ (AffineCategory.inclusion B S hS 𝒳.val.val.p) O.obj).obj P)
      fun {z z'} f hf => hcart f.hom z.property z'.property hf
  rw [isIso_hypercohomologyEdge_app_iff, cohomologyPresheafUnit_app]
  have hiso := Stacks.Sites.isIso_toSheafify_app_of_isSheaf_comp (affineFppfRingedSite B S hS 𝒳).J
    (fppfTopology B S hS 𝒳) (AffineCategory.inclusion B S hS 𝒳.val.val.p) P.presheaf hPs ⟨y, hy⟩
  have : IsIso ((forget₂ (ModuleCat.{u + 1} (O.obj.obj (op y))) AddCommGrpCat.{u + 1}).map
      ((PresheafOfModules.evaluation O.obj (op y)).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).unit.app P))) := hiso
  exact @isIso_of_reflects_iso _ _ _ _ _ _ _
    (forget₂ (ModuleCat.{u + 1} (O.obj.obj (op y))) AddCommGrpCat.{u + 1}) this _

/-- **Step 1 of the proof of Stacks 0H16, in the form `HasAffineDerivedSectionsBaseChange K ⟹
K ∈ D_{LQCoh^fbc}(𝒪_𝒳)`.** If `K` has the base change property of Stacks 0H15, every cohomology
sheaf `H^q K` lies in `LQCoh^fbc(𝒪_𝒳)`.

Over objects lying over affine schemes `Γ(-, H^q K) = H^q(RΓ(-, K))`
(`isIso_hypercohomologyEdge_app_of_hasAffineDerivedSectionsBaseChange`), compatibly with
restriction (`derivedSectionsRestrictHomology_app_comp_hypercohomologyEdge`), and the latter is
cartesian along flat arrows (`isIso_homEquiv_symm_derivedSectionsRestrictHomology_of_flat`). So
`H^q K` is an fppf, hence étale, sheaf cartesian on flat arrows between affine objects, which is
membership in `LQCoh^fbc(𝒪_𝒳)`
(`isLocallyQuasicoherentWithSheafFlatBaseChange_of_isCartesianOnFlatAffineArrows`). -/
theorem derivedCategoryB_sheafFlatBaseChangeModulesSucc_of_hasAffineDerivedSectionsBaseChange
    (K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
    (hK : HasAffineDerivedSectionsBaseChange B S hS 𝒳 K) :
    DerivedCategoryB.derivedCategoryB (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) K := by
  intro q
  let O := ambientRingStructureSheaf B S hS 𝒳
  let F := (DerivedCategory.homologyFunctor (SheafOfModules.{u + 1} O) q).obj K
  have hsh : Presheaf.IsSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      F.val.presheaf :=
    F.isSheaf.of_le (associatedTopology_mono B S hS 𝒳.val.val.p (etaleTopology_le_topology B))
  refine isLocallyQuasicoherentWithSheafFlatBaseChange_of_isCartesianOnFlatAffineArrows.{u, u + 1,
    u, u} B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F.val hsh
    fun x x' a ha hx hx' => ?_
  rw [← ConcreteCategory.isIso_iff_bijective]
  have : PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1} (O.obj.map a.op).hom) :=
    Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteLimits _
  have : PreservesFiniteColimits (ModuleCat.restrictScalars.{u + 1} (O.obj.map a.op).hom) :=
    Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteColimits _
  have hD := isIso_homEquiv_symm_derivedSectionsRestrictHomology_of_flat B S hS 𝒳 K hK a hx hx'
    ha q
  have := isIso_hypercohomologyEdge_app_of_hasAffineDerivedSectionsBaseChange B S hS 𝒳 K hK x hx q
  have := isIso_hypercohomologyEdge_app_of_hasAffineDerivedSectionsBaseChange B S hS 𝒳 K hK x'
    hx' q
  have hsq := derivedSectionsRestrictHomology_app_comp_hypercohomologyEdge.{_, _, _, u + 1, u + 1}
    O a q K
  have e : (sectionsRestrict O a).app F = inv ((hypercohomologyEdge O x' q).app K) ≫
      (derivedSectionsRestrictHomology O a q).app K ≫
        (ModuleCat.restrictScalars.{u + 1} (O.obj.map a.op).hom).map
          ((hypercohomologyEdge O x q).app K) := by
    rw [eq_comm, IsIso.inv_comp_eq, hsq]
  exact (isIso_homEquiv_symm_of_eq_comp _ _ _ _ _ hD e :)

end SheafFlatBaseChange

end AlgebraicGeometry.Stack.FlatFppf

end
