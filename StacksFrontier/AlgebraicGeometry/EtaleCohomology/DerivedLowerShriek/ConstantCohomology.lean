module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ConstantFiniteModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.QuasiFiniteConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.NoetherianInduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage

/-!
# Complexes whose cohomology sheaves are a constant sheaf or zero

The proof of Stacks 0GKX computes `Rf_! M` for the constant sheaf `M` on a finite module through
a chain of restrictions to opens, inverse images to closed subschemes and base changes. Each of
these functors is exact and carries constant sheaves to constant sheaves, so all the complexes in
the chain have the property recorded here: every cohomology sheaf is zero or the constant sheaf on
`M`.

## Main definitions

* `Stacks.EtaleCohomology.HasConstantCohomologyPlus Λ M K`: every cohomology sheaf of `K` in
  `D⁺(X_étale, Λ)` is zero or isomorphic to the constant sheaf on `M`.

## Main results

* `Stacks.EtaleCohomology.hasConstantCohomologyPlus_singleFunctor`: the constant sheaf in
  degree `0`.
* `Stacks.EtaleCohomology.HasConstantCohomologyPlus.inverseImage` and
  `Stacks.EtaleCohomology.HasConstantCohomologyPlus.restriction`: stability under inverse image
  and under restriction along an étale morphism.
* `Stacks.EtaleCohomology.HasConstantCohomologyPlus.isConstructible_and_isTorsion`: over a
  torsion Noetherian ring and for a finite module, the cohomology sheaves are constructible and
  torsion.
* `Stacks.EtaleCohomology.prop_homology_obj₁_of_distTriang_plus`: a weak Serre class containing
  the cohomology of the second and third vertices of a distinguished triangle of `D⁺` contains
  that of the first.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

section Triangle

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- **The first vertex of a distinguished triangle of `D⁺`.** A weak Serre class containing all
cohomology objects of the second and third vertices of a distinguished triangle of `D⁺(C)`
contains those of the first, by the five term exact sequence
`H^{n-1}(T₂) → H^{n-1}(T₃) → H^n(T₁) → H^n(T₂) → H^n(T₃)`. -/
theorem prop_homology_obj₁_of_distTriang_plus (P : ObjectProperty C) [P.IsWeakSerreClass]
    (T : Pretriangulated.Triangle (DerivedCategory.Plus C)) (hT : T ∈ distTriang _)
    (h₂ : ∀ i : ℤ, P ((DerivedCategory.Plus.homologyFunctor C i).obj T.obj₂))
    (h₃ : ∀ i : ℤ, P ((DerivedCategory.Plus.homologyFunctor C i).obj T.obj₃)) (n : ℤ) :
    P ((DerivedCategory.Plus.homologyFunctor C n).obj T.obj₁) := by
  let T' := DerivedCategory.Plus.ι.mapTriangle.obj T
  have hT' : T' ∈ distTriang _ := DerivedCategory.Plus.ι.map_distinguished T hT
  have h₂' : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor C i).obj T'.obj₂) := h₂
  have h₃' : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor C i).obj T'.obj₃) := h₃
  show P ((DerivedCategory.homologyFunctor C n).obj T'.obj₁)
  exact ObjectProperty.prop_mid_of_exact₄
    (fun S hS a b c d => P.prop_obj₂_of_exact S hS a b c d)
    (f₀ := (DerivedCategory.homologyFunctor C (n - 1)).map T'.mor₂)
    (f₁ := DerivedCategory.HomologySequence.δ T' (n - 1) n (by omega))
    (f₂ := (DerivedCategory.homologyFunctor C n).map T'.mor₁)
    (f₃ := (DerivedCategory.homologyFunctor C n).map T'.mor₂)
    (DerivedCategory.HomologySequence.comp_δ T' hT' (n - 1) n (by omega))
    (DerivedCategory.HomologySequence.δ_comp T' hT' (n - 1) n (by omega))
    (by rw [← Functor.map_comp, Pretriangulated.comp_distTriang_mor_zero₁₂ _ hT',
      Functor.map_zero])
    (DerivedCategory.HomologySequence.exact₃ T' hT' (n - 1) n (by omega))
    (DerivedCategory.HomologySequence.exact₁ T' hT' (n - 1) n (by omega))
    (DerivedCategory.HomologySequence.exact₂ T' hT' n)
    (h₂' (n - 1)) (h₃' (n - 1)) (h₂' n) (h₃' n)

end Triangle

attribute [local instance] HasDerivedCategory.standard
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type r) [Ring Λ] {X : Scheme.{u}} (M : ModuleCat.{max (u + 1) r} Λ)

/-- **Cohomology sheaves zero or constant.** Every cohomology sheaf of `K` in
`D⁺(X_étale, Λ)` is zero or isomorphic to the constant sheaf on the module `M`. -/
def HasConstantCohomologyPlus (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)) : Prop :=
  ∀ q : ℤ, IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj K) ∨
    Nonempty ((DerivedCategory.Plus.homologyFunctor _ q).obj K ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M)

/-- The constant sheaf on `M` in degree `0` has constant cohomology. -/
theorem hasConstantCohomologyPlus_singleFunctor :
    HasConstantCohomologyPlus Λ M ((DerivedCategory.Plus.singleFunctor
      (EtaleModules.{u, r} Λ X) 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M)) := by
  intro q
  let K := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M)
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · exact Or.inl (DerivedCategory.Plus.isZero_homology_of_isGE K 0 q hq)
  · exact Or.inr ⟨(DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).app _⟩
  · exact Or.inl (DerivedCategory.Plus.isZero_homology_of_isLE K 0 q hq)

variable {Λ M}

/-- Constant cohomology is invariant under isomorphism. -/
theorem HasConstantCohomologyPlus.of_iso {K L : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)}
    (hK : HasConstantCohomologyPlus Λ M K) (e : K ≅ L) : HasConstantCohomologyPlus Λ M L := by
  intro q
  let e' := (DerivedCategory.Plus.homologyFunctor _ q).mapIso e
  exact (hK q).elim (fun h => Or.inl (h.of_iso e'.symm)) (fun ⟨e''⟩ => Or.inr ⟨e'.symm ≪≫ e''⟩)

/-- A functor preserving zero morphisms turns "zero or isomorphic to `b`" into "zero or isomorphic
to `d`", given isomorphisms `c ≅ F a` and `F b ≅ d`. -/
private theorem isZero_or_nonempty_iso_of_functor {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms] {a b : C}
    {c d : D} (h : IsZero a ∨ Nonempty (a ≅ b)) (e : c ≅ F.obj a) (e₂ : F.obj b ≅ d) :
    IsZero c ∨ Nonempty (c ≅ d) :=
  h.elim (fun h => Or.inl ((F.map_isZero h).of_iso e))
    (fun ⟨e'⟩ => Or.inr ⟨e ≪≫ F.mapIso e' ≪≫ e₂⟩)

/-- **Inverse image keeps constant cohomology**: inverse image is exact and carries the constant
sheaf on `M` to the constant sheaf on `M`. -/
theorem HasConstantCohomologyPlus.inverseImage {Y : Scheme.{u}} (g : Y ⟶ X)
    {K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)} (hK : HasConstantCohomologyPlus Λ M K) :
    HasConstantCohomologyPlus Λ M
      ((etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategoryPlus.obj K) := by
  intro q
  obtain ⟨e⟩ := nonempty_homology_etaleModuleDerivedInverseImagePlus_iso Λ g K q
  exact isZero_or_nonempty_iso_of_functor _ (hK q) e
    ((etaleModuleInverseImageConstantIso.{u, r} Λ g).app M)

/-- **Restriction along an étale morphism keeps constant cohomology**: restriction is exact and
agrees with inverse image. -/
theorem HasConstantCohomologyPlus.restriction {U : Scheme.{u}} (j : U ⟶ X) [Etale j]
    {K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)} (hK : HasConstantCohomologyPlus Λ M K) :
    HasConstantCohomologyPlus Λ M
      ((etaleModuleRestriction.{u, r} Λ j).mapDerivedCategoryPlus.obj K) := by
  intro q
  let e : (DerivedCategory.Plus.homologyFunctor _ q).obj
      ((etaleModuleRestriction.{u, r} Λ j).mapDerivedCategoryPlus.obj K) ≅
      (etaleModuleRestriction.{u, r} Λ j).obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K) :=
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (etaleModuleRestriction.{u, r} Λ j) q).app (DerivedCategory.Plus.ι.obj K)
  exact isZero_or_nonempty_iso_of_functor _ (hK q) e
    ((etaleModuleInverseImageRestrictionIso.{u, r} Λ j).symm.app _ ≪≫
      (etaleModuleInverseImageConstantIso.{u, r} Λ j).app M)

/-- A functor of étale modules carries a complex isomorphic to `A` in degree `0` to a complex
isomorphic to `B` in degree `0`, given an isomorphism `F A ≅ B`. -/
private theorem nonempty_mapDerivedCategoryPlus_singleFunctor_iso {Y : Scheme.{u}}
    (F : EtaleModules.{u, r} Λ X ⥤ EtaleModules.{u, r} Λ Y) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)}
    {A : EtaleModules.{u, r} Λ X} {B : EtaleModules.{u, r} Λ Y}
    (e : K ≅ (DerivedCategory.Plus.singleFunctor _ 0).obj A) (c : F.obj A ≅ B) :
    Nonempty (F.mapDerivedCategoryPlus.obj K ≅ (DerivedCategory.Plus.singleFunctor _ 0).obj B) :=
  let e₁ : DerivedCategory.Plus.ι.obj (F.mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj A)) ≅
      DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj (F.obj A)) :=
    (F.mapDerivedCategorySingleFunctor 0).app A
  ⟨F.mapDerivedCategoryPlus.mapIso e ≪≫ DerivedCategory.Plus.ι.preimageIso e₁ ≪≫
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso c⟩

/-- **Inverse image of the constant sheaf in degree `0`.** For `g : Y ⟶ X`, the derived inverse
image of a complex isomorphic to the constant sheaf on `M` in degree `0` is isomorphic to the
constant sheaf on `M` in degree `0`. -/
theorem nonempty_inverseImage_singleFunctor_constantSheaf_iso {Y : Scheme.{u}} (g : Y ⟶ X)
    {K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)}
    (hK : Nonempty (K ≅ (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M))) :
    Nonempty ((etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategoryPlus.obj K ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M)) := by
  obtain ⟨e⟩ := hK
  exact nonempty_mapDerivedCategoryPlus_singleFunctor_iso _ e
    ((etaleModuleInverseImageConstantIso.{u, r} Λ g).app M)

/-- **Étale restriction of the constant sheaf in degree `0`.** For `j : U ⟶ X` étale, the
restriction of a complex isomorphic to the constant sheaf on `M` in degree `0` is isomorphic to
the constant sheaf on `M` in degree `0`. -/
theorem nonempty_restriction_singleFunctor_constantSheaf_iso {U : Scheme.{u}} (j : U ⟶ X) [Etale j]
    {K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)}
    (hK : Nonempty (K ≅ (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M))) :
    Nonempty ((etaleModuleRestriction.{u, r} Λ j).mapDerivedCategoryPlus.obj K ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((constantSheaf U.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M)) := by
  obtain ⟨e⟩ := hK
  exact nonempty_mapDerivedCategoryPlus_singleFunctor_iso _ e
    ((etaleModuleInverseImageRestrictionIso.{u, r} Λ j).symm.app _ ≪≫
      (etaleModuleInverseImageConstantIso.{u, r} Λ j).app M)

/-- A complex isomorphic to the constant sheaf on `M` in degree `0` has constant cohomology. -/
theorem hasConstantCohomologyPlus_of_iso_singleFunctor
    {K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)}
    (hK : Nonempty (K ≅ (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M))) :
    HasConstantCohomologyPlus Λ M K :=
  (hasConstantCohomologyPlus_singleFunctor Λ M).of_iso hK.some.symm

attribute [local instance] moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- **Constant cohomology on a finite module over a torsion Noetherian ring is constructible and
torsion**, on a quasi-compact quasi-separated scheme of a big étale site. -/
theorem HasConstantCohomologyPlus.isConstructible_and_isTorsion (B : BigEtaleSite.{u})
    {Λ : Type} [CommRing Λ] [IsNoetherianRing Λ] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    {X : B.Scheme} [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] {M : ModuleCat.{u + 1} Λ}
    (hM : Module.Finite Λ M) {K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X.obj)}
    (hK : HasConstantCohomologyPlus Λ M K) (q : ℤ) :
    IsBigSiteConstructibleEtaleModule B X Λ ((DerivedCategory.Plus.homologyFunctor _ q).obj K) ∧
      IsTorsionEtaleModule Λ X.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K) :=
  ⟨(hK q).elim (fun h => isConstructibleEtaleModule_of_isZero B Λ X h)
      (fun ⟨e⟩ => IsBigSiteConstructibleEtaleModule.of_iso B Λ e.symm
        (isConstructibleEtaleModule_constantSheaf_of_finite B X Λ M hM)),
    isTorsionEtaleModule_of_natCast_eq_zero Λ m hm hΛ _⟩

end Stacks.EtaleCohomology

end
