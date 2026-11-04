module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionSheafHomRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction
public import StacksFrontier.RingTheory.Dualizing.RelativeGeneratorUniversal
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexAffineChart
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.ClosedImmersionStalkVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.AlongAnIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange

/-!
# Excision for objects supported in an open

Let `j : V ⟶ Z` be the inclusion of an open of a scheme and `F` an object of `D(𝒪_Z)` which is a
module in degree zero whose stalks vanish off `V`. Then restriction to `V` is bijective on
morphisms out of `F`: `Hom(F, L) ≅ Hom(F|_V, L|_V)` for every `L`. Indeed `j_! j^* F ⟶ F` is an
isomorphism, and restriction of a morphism `ζ : F ⟶ L` is its adjoint under `j_! ⊣ j^*`
(Stacks 08BT) after precomposition with this counit.

Consequently a morphism out of `F` generates its Hom group under precomposition by endomorphisms
of `F` exactly when its restriction to `V` does.

## Main results

* `CategoryTheory.Adjunction.rightAdjoint_map_bijective_of_isIso_counit`:
  a right adjoint is bijective on morphisms out of an object at which the counit is invertible.
* `CategoryTheory.Adjunction.isIso_mapDerivedCategory_counit_app_single`: the counit of the
  derived adjunction is invertible at a module in degree zero at which the counit is invertible.
* `Dualizing.IsPostcompGenerator.map_iff_of_bijective`: generators transfer along a functor
  bijective on the relevant morphism groups.
* `AlgebraicGeometry.Scheme.Modules.bijective_restrict_of_stalk_isZero`: excision.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- Applying the right adjoint to `ζ : X ⟶ Y` is the adjoint of `ζ` precomposed with the counit
at `X`. -/
theorem map_eq_homEquiv_counit_comp {X Y : D} (ζ : X ⟶ Y) :
    G.map ζ = adj.homEquiv _ _ (adj.counit.app X ≫ ζ) := by
  rw [adj.homEquiv_unit, G.map_comp, ← Category.assoc, adj.right_triangle_components,
    Category.id_comp]

/-- **A right adjoint is bijective on morphisms out of an object at which the counit is
invertible.** -/
theorem rightAdjoint_map_bijective_of_isIso_counit {X : D} [IsIso (adj.counit.app X)] (Y : D) :
    Function.Bijective (fun ζ : X ⟶ Y => G.map ζ) := by
  have h : (fun ζ : X ⟶ Y => G.map ζ) =
      (adj.homEquiv _ _) ∘ (fun ζ : X ⟶ Y => adj.counit.app X ≫ ζ) :=
    funext fun ζ => map_eq_homEquiv_counit_comp adj ζ
  rw [h]
  exact (adj.homEquiv _ _).bijective.comp
    ((isIso_iff_coyoneda_map_bijective (adj.counit.app X)).1 inferInstance Y)

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : F ⊣ G)

/-- The counit of the derived adjunction, on the image of a complex. -/
theorem mapDerivedCategory_counit_app_Q (Y : CochainComplex D ℤ) :
    (CategoryTheory.Adjunction.mapDerivedCategory adj).counit.app (DerivedCategory.Q.obj Y) =
      F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app Y) ≫
        F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj Y) ≫
          DerivedCategory.Q.map ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app Y) := by
  simp only [CategoryTheory.Adjunction.mapDerivedCategory, Adjunction.localization_counit_app]
  rfl

/-- **The counit of the derived adjunction is invertible at a module in degree zero** at which
the counit of the adjunction is invertible. -/
theorem isIso_mapDerivedCategory_counit_app_single (M : D) [IsIso (adj.counit.app M)] :
    IsIso ((CategoryTheory.Adjunction.mapDerivedCategory adj).counit.app
      ((DerivedCategory.singleFunctor D 0).obj M)) := by
  let K := (HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj M
  have hK : IsIso ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K) := by
    refine @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ _ fun n => ?_
    show IsIso (adj.counit.app (K.X n))
    by_cases hn : n = 0
    · subst hn
      rw [NatTrans.isIso_app_iff_of_iso adj.counit
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M)]
      infer_instance
    · have hz : IsZero (K.X n) := HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
      exact isIso_of_source_target_iso_zero _
        ((G ⋙ F).map_isZero hz).isoZero hz.isoZero
  have hQ : IsIso ((CategoryTheory.Adjunction.mapDerivedCategory adj).counit.app
      (DerivedCategory.Q.obj K)) := by
    rw [mapDerivedCategory_counit_app_Q]
    infer_instance
  exact (NatTrans.isIso_app_iff_of_iso _ ((DerivedCategory.singleFunctorIsoCompQ D 0).app M)).2 hQ

end CategoryTheory.Adjunction

namespace Dualizing.IsPostcompGenerator

variable {C D : Type*} [Category* C] [Category* D]

/-- **Generators transfer along a functor bijective on the relevant morphism groups.** If `G` is
bijective on `Hom(X, Y)` and surjective on `End(X)`, then `G.map ξ` is a postcomposition
generator exactly when `ξ` is. -/
theorem map_iff_of_bijective (G : D ⥤ C) {X Y : D} (ξ : X ⟶ Y)
    (h₁ : Function.Bijective (fun ζ : X ⟶ Y => G.map ζ))
    (h₂ : Function.Surjective (fun a : X ⟶ X => G.map a)) :
    IsPostcompGenerator (G.map ξ) ↔ IsPostcompGenerator ξ := by
  constructor
  · intro h ζ
    obtain ⟨a, ha⟩ := h (G.map ζ)
    obtain ⟨a₀, rfl⟩ := h₂ a
    refine ⟨a₀, h₁.1 ?_⟩
    dsimp only at ha ⊢
    rw [G.map_comp, ha]
  · intro h ζ
    obtain ⟨ζ₀, rfl⟩ := h₁.2 ζ
    obtain ⟨a, ha⟩ := h ζ₀
    refine ⟨G.map a, ?_⟩
    dsimp only at ha ⊢
    rw [← G.map_comp, ha]

/-- Conjugating by isomorphisms of the source and the target neither creates nor destroys the
property. -/
theorem conj_iff {X X' Y Y' : D} (eX : X ≅ X') (eY : Y ≅ Y') (ξ : X ⟶ Y) :
    IsPostcompGenerator (eX.inv ≫ ξ ≫ eY.hom) ↔ IsPostcompGenerator ξ :=
  ⟨fun h => h.of_conj eX.symm eY.symm (by simp), fun h => h.conj eX eY⟩

end Dualizing.IsPostcompGenerator

/-! ### Excision on schemes -/

section Excision

open AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

/-- A functor bijective on `Hom(X', Y)` is bijective on `Hom(X, Y)` for `X ≅ X'`. -/
theorem _root_.CategoryTheory.Functor.bijective_map_of_iso_left {C D : Type*} [Category* C]
    [Category* D] (G : D ⥤ C) {X X' Y : D} (e : X ≅ X')
    (h : Function.Bijective (fun ζ : X' ⟶ Y => G.map ζ)) :
    Function.Bijective (fun ζ : X ⟶ Y => G.map ζ) := by
  have hc : (fun ζ : X ⟶ Y => G.map ζ) =
      (fun t : G.obj X' ⟶ G.obj Y => G.map e.hom ≫ t) ∘ (fun ζ : X' ⟶ Y => G.map ζ) ∘
        (fun ζ : X ⟶ Y => e.inv ≫ ζ) := by
    funext ζ
    show G.map ζ = G.map e.hom ≫ G.map (e.inv ≫ ζ)
    rw [← G.map_comp, Iso.hom_inv_id_assoc]
  rw [hc]
  exact (((isIso_iff_coyoneda_map_bijective (G.map e.hom)).1 inferInstance _).comp h).comp
    ((isIso_iff_coyoneda_map_bijective e.inv).1 inferInstance Y)

/-- Bijectivity on a morphism group transfers along a natural isomorphism of functors. -/
theorem _root_.CategoryTheory.Functor.bijective_map_of_natIso {C D : Type*} [Category* C]
    [Category* D] {G H : D ⥤ C} (α : G ≅ H) {X Y : D}
    (h : Function.Bijective (fun ζ : X ⟶ Y => G.map ζ)) :
    Function.Bijective (fun ζ : X ⟶ Y => H.map ζ) := by
  have hc : (fun ζ : X ⟶ Y => H.map ζ) =
      (fun t : G.obj X ⟶ G.obj Y => α.inv.app X ≫ t ≫ α.hom.app Y) ∘
        (fun ζ : X ⟶ Y => G.map ζ) :=
    funext fun ζ => (NatIso.naturality_1 α ζ).symm
  rw [hc]
  exact ((α.app X).homCongr (α.app Y)).bijective.comp h

/-- **Excision on a scheme.** Let `V ⊆ Z` be open and `M` a module on `Z` whose stalks vanish
off `V`. Restriction to `V` is bijective on morphisms of `D(𝒪_Z)` out of `M` in degree zero. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.bijective_restrict_of_stalk_isZero
    {Z : Scheme.{u}} (V : Z.Opens) (M : Z.Modules)
    (hM : ∀ x : Z, x ∉ V → IsZero (TopCat.Presheaf.stalk (X := Z.toRingedSpace.carrier)
      M.val.presheaf x))
    (L : DerivedCategory Z.Modules) :
    Function.Bijective (fun ζ : (DerivedCategory.singleFunctor Z.Modules 0).obj M ⟶ L =>
      (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.map ζ) := by
  have := Stacks.Duality.ClosedImmersionRestriction.isIso_jShriekAdjunction_counit_app V M hM
  have h := (Stacks.Duality.ClosedImmersionRestriction.jShriekAdjunction
    V).isIso_mapDerivedCategory_counit_app_single M
  exact @Adjunction.rightAdjoint_map_bijective_of_isIso_counit _ _ _ _ _ _
    (Stacks.Duality.ClosedImmersionRestriction.derivedJShriekAdjunction V) _ h L

/-- A composite of a functor bijective on `Hom(X, Y)` and a fully faithful one is bijective on
`Hom(X, Y)`. -/
theorem _root_.CategoryTheory.Functor.bijective_map_comp {C D E : Type*} [Category* C]
    [Category* D] [Category* E] (G₁ : D ⥤ C) (G₂ : C ⥤ E) (hG₂ : G₂.FullyFaithful) {X Y : D}
    (h : Function.Bijective (fun ζ : X ⟶ Y => G₁.map ζ)) :
    Function.Bijective (fun ζ : X ⟶ Y => (G₁ ⋙ G₂).map ζ) :=
  hG₂.map_bijective _ _ |>.comp h

/-- The isomorphism of ringed spaces underlying an isomorphism of schemes. -/
def _root_.AlgebraicGeometry.Scheme.toRingedSpaceIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    X.toRingedSpace ≅ Y.toRingedSpace where
  hom := e.hom.toLRSHom.toShHom
  inv := e.inv.toLRSHom.toShHom
  hom_inv_id := by
    rw [← LocallyRingedSpace.comp_toShHom, ← Scheme.Hom.comp_toLRSHom, e.hom_inv_id]
    exact LocallyRingedSpace.id_toShHom' _
  inv_hom_id := by
    rw [← LocallyRingedSpace.comp_toShHom, ← Scheme.Hom.comp_toLRSHom, e.inv_hom_id]
    exact LocallyRingedSpace.id_toShHom' _

/-- Derived pullback along an open immersion `j` is restriction to its image followed by derived
pullback along the isomorphism onto the image. -/
noncomputable def _root_.AlgebraicGeometry.Scheme.Hom.derivedPullbackOpensRangeIso
    {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctor j.opensRange.ι).mapDerivedCategory ⋙
        derivedPullback (Scheme.toRingedSpaceIso j.isoOpensRange).hom ≅
      derivedPullback j.toLRSHom.toShHom := by
  have h : (Scheme.toRingedSpaceIso j.isoOpensRange).hom ≫ j.opensRange.ι.toLRSHom.toShHom =
      j.toLRSHom.toShHom := by
    change j.isoOpensRange.hom.toLRSHom.toShHom ≫ j.opensRange.ι.toLRSHom.toShHom = _
    rw [← LocallyRingedSpace.comp_toShHom, ← Scheme.Hom.comp_toLRSHom,
      Scheme.Hom.isoOpensRange_hom_ι]
  let e₁ : (Scheme.Modules.restrictFunctor j.opensRange.ι).mapDerivedCategory ⋙
        derivedPullback (Scheme.toRingedSpaceIso j.isoOpensRange).hom ≅
      derivedPullback j.opensRange.ι.toLRSHom.toShHom ⋙
        derivedPullback (Scheme.toRingedSpaceIso j.isoOpensRange).hom :=
    Functor.isoWhiskerRight (Scheme.Modules.derivedRestrictIsoDerivedPullback j.opensRange.ι) _
  let e₂ : derivedPullback j.opensRange.ι.toLRSHom.toShHom ⋙
        derivedPullback (Scheme.toRingedSpaceIso j.isoOpensRange).hom ≅
      derivedPullback ((Scheme.toRingedSpaceIso j.isoOpensRange).hom ≫
        j.opensRange.ι.toLRSHom.toShHom) :=
    Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical _ _
  exact e₁ ≪≫ e₂ ≪≫ eqToIso (by rw [h])

/-- `Δ_*𝒪_X` is a module in degree zero. -/
noncomputable def _root_.AlgebraicGeometry.Scheme.Hom.DiagonalOpen.diagonalObjectSingleIso
    {X S : Scheme.{u}} {f : X ⟶ S} (D : Scheme.Hom.DiagonalOpen f) :
    D.diagonalObject ≅ (DerivedCategory.singleFunctor D.W.Modules 0).obj
      ((RingedSpaceModuleAdjunction.modulePushforward D.diagQuotient.i).obj
        (SheafOfModules.unit X.ringCatSheaf)) :=
  D.diagonalObjectIso ≪≫
    ((RingedSpaceModuleAdjunction.modulePushforward
      D.diagQuotient.i).mapDerivedCategorySingleFunctor 0).app _

/-- The stalks of `Δ_*𝒪_X` vanish off the image of an open immersion through which the diagonal
factors. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isZero_stalk_diagonalModule
    {X S : Scheme.{u}} {f : X ⟶ S} (D₁ D₂ : Scheme.Hom.DiagonalOpen f) (j : D₁.W ⟶ D₂.W)
    [IsOpenImmersion j] (hj : D₁.diag ≫ j = D₂.diag) (x : D₂.W) (hx : x ∉ j.opensRange) :
    IsZero (TopCat.Presheaf.stalk (X := D₂.W.toRingedSpace.carrier)
      ((RingedSpaceModuleAdjunction.modulePushforward D₂.diagQuotient.i).obj
        (SheafOfModules.unit X.ringCatSheaf)).val.presheaf x) := by
  have := D₂.isClosedImmersion
  have hr : x ∉ Set.range (ConcreteCategory.hom D₂.diag.base) := by
    rintro ⟨z, rfl⟩
    apply hx
    rw [← hj]
    exact ⟨D₁.diag.base z, rfl⟩
  exact @AddCommGrpCat.isZero_of_subsingleton _
    (subsingleton_stalk_pushforward_of_notMemRange' D₂.diag
      (SheafOfModules.unit X.ringCatSheaf) x hr)

/-- **Excision for the diagonal.** Let `D₁`, `D₂` be diagonal opens of `f` and `j : W₁ ⟶ W₂` an
open immersion with `Δ₂ = Δ₁ ≫ j`. Derived pullback along `j` is bijective on morphisms of
`D(𝒪_{W₂})` out of `Δ₂_*𝒪_X`: such a morphism is determined by, and can be prescribed on, the
open `W₁` containing the support of `Δ₂_*𝒪_X`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.DiagonalOpen.bijective_derivedPullback_diagonalObject
    {X S : Scheme.{u}} {f : X ⟶ S} (D₁ D₂ : Scheme.Hom.DiagonalOpen f) (j : D₁.W ⟶ D₂.W)
    [IsOpenImmersion j] (hj : D₁.diag ≫ j = D₂.diag) (L : DerivedCategory D₂.W.Modules) :
    Function.Bijective (fun ζ : D₂.diagonalObject ⟶ L =>
      (derivedPullback j.toLRSHom.toShHom).map ζ) := by
  have h₁ := Scheme.Modules.bijective_restrict_of_stalk_isZero j.opensRange _
    (D₁.isZero_stalk_diagonalModule D₂ j hj) L
  have h₂ := Functor.bijective_map_of_iso_left _ D₂.diagonalObjectSingleIso h₁
  have h₃ := Functor.bijective_map_comp _ _
    (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackEquivalence
      (Scheme.toRingedSpaceIso j.isoOpensRange)).fullyFaithfulFunctor h₂
  exact Functor.bijective_map_of_natIso j.derivedPullbackOpensRangeIso h₃

/-- **Generators and excision for the diagonal.** With `j : W₁ ⟶ W₂` as in
`bijective_derivedPullback_diagonalObject`, a morphism out of `Δ₂_*𝒪_X` is a generator exactly
when its derived pullback along `j` is. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isPostcompGenerator_derivedPullback_iff
    {X S : Scheme.{u}} {f : X ⟶ S} (D₁ D₂ : Scheme.Hom.DiagonalOpen f) (j : D₁.W ⟶ D₂.W)
    [IsOpenImmersion j] (hj : D₁.diag ≫ j = D₂.diag) {L : DerivedCategory D₂.W.Modules}
    (ζ : D₂.diagonalObject ⟶ L) :
    Dualizing.IsPostcompGenerator ((derivedPullback j.toLRSHom.toShHom).map ζ) ↔
      Dualizing.IsPostcompGenerator ζ :=
  Dualizing.IsPostcompGenerator.map_iff_of_bijective _ ζ
    (D₁.bijective_derivedPullback_diagonalObject D₂ j hj L)
    (D₁.bijective_derivedPullback_diagonalObject D₂ j hj D₂.diagonalObject).2

/-- Every morphism out of `Δ₁_*𝒪_X` on `W₁` is, up to the identifications `θ₁`, `θ₂`, the derived
pullback of a morphism out of `Δ₂_*𝒪_X` on `W₂`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.DiagonalOpen.exists_derivedPullback_eq
    {X S : Scheme.{u}} {f : X ⟶ S} (D₁ D₂ : Scheme.Hom.DiagonalOpen f) (j : D₁.W ⟶ D₂.W)
    [IsOpenImmersion j] (hj : D₁.diag ≫ j = D₂.diag) {L : DerivedCategory D₂.W.Modules}
    {L₁ : DerivedCategory D₁.W.Modules}
    (θ₁ : (derivedPullback j.toLRSHom.toShHom).obj D₂.diagonalObject ≅ D₁.diagonalObject)
    (θ₂ : (derivedPullback j.toLRSHom.toShHom).obj L ≅ L₁) (ξ : D₁.diagonalObject ⟶ L₁) :
    ∃ ξ₂ : D₂.diagonalObject ⟶ L,
      (derivedPullback j.toLRSHom.toShHom).map ξ₂ = θ₁.hom ≫ ξ ≫ θ₂.inv :=
  (D₁.bijective_derivedPullback_diagonalObject D₂ j hj L).2 _

end Excision

end
