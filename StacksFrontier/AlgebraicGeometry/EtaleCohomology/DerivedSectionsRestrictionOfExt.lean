module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedSectionsRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitUnboundedIsIsoAbelian

/-!
# Restriction of derived sections is detected on `Ext` out of the constant sheaf

Let `h : W ⟶ Y` be a morphism of schemes and `G` an abelian sheaf on the small étale site of `Y`.
The restriction of unbounded derived global sections `RΓ(Y, G) ⟶ RΓ(W, h⁻¹G)` is an isomorphism
as soon as the inverse image `h⁻¹` is bijective on `Ext^n(ℤ_Y, G)` in every degree `n`, that is,
as soon as restriction of étale cohomology `Hⁿ(Y, G) ⟶ Hⁿ(W, h⁻¹G)` is bijective.

The argument: the restriction is `RΓ(Y, -)` of the unit `G ⟶ Rh_* h⁻¹G` followed by Leray
(`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsRestriction_app`). A morphism of `D(Ab)`
is an isomorphism when it is bijective on morphisms out of `ℤ[q]` for every `q`, `ℤ` being a
projective generator (`DerivedCategory.homologyFromSingleAddEquiv`). Morphisms out of `ℤ[q]` into
`RΓ(Y, M)` are morphisms out of `ℤ_Y[q]` into `M`, by the derived adjunction between the constant
sheaf functor and `RΓ(Y, -)`; and composing with the unit of `h⁻¹ ⊣ Rh_*` is, through that
adjunction, applying `h⁻¹`.

## Main results

* `isIso_of_bijective_comp_singleFunctor_uliftInt`: `ℤ` detects isomorphisms of `D(Ab)`.
* `smallEtaleConstantDerivedAdjunction`: the constant sheaf functor is left adjoint to `RΓ(Y, -)`
  on unbounded derived categories.
* `isIso_smallEtaleDerivedGlobalSectionsRestriction_single_of_isBijectiveOnExt`: the criterion
  above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme Opposite

universe u

namespace Stacks.EtaleCohomology

/-- The constant abelian group `ℤ`, at the coefficient universe of abelian étale sheaves. -/
abbrev uliftIntAb : AddCommGrpCat.{u + 1} := AddCommGrpCat.of (ULift.{u + 1} ℤ)

attribute [local instance] Stacks.ChaoticSite.projective_uliftIntAddCommGrp

/-- **`ℤ` detects isomorphisms of `D(Ab)`.** A morphism `ψ` of the unbounded derived category of
abelian groups which is bijective on morphisms out of `ℤ` placed in every degree `q` is an
isomorphism: by `DerivedCategory.homologyFromSingleAddEquiv`, `ℤ` being projective, those
morphisms are the morphisms `ℤ ⟶ H^q(-)`, that is the elements of `H^q(-)`. -/
theorem isIso_of_bijective_comp_singleFunctor_uliftInt [HasDerivedCategory AddCommGrpCat.{u + 1}]
    {B B' : DerivedCategory AddCommGrpCat.{u + 1}}
    (ψ : B ⟶ B')
    (h : ∀ q : ℤ, Function.Bijective
      (fun x : (DerivedCategory.singleFunctor AddCommGrpCat.{u + 1} q).obj uliftIntAb ⟶ B =>
        x ≫ ψ)) :
    IsIso ψ := by
  rw [DerivedCategory.isIso_iff]
  intro q
  have hq : Function.Bijective (fun y : uliftIntAb.{u} ⟶
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj B =>
        y ≫ (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).map ψ) := by
    let e := fun Z => DerivedCategory.homologyFromSingleAddEquiv uliftIntAb.{u} Z q
    have hcomm : (fun y : uliftIntAb.{u} ⟶
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj B =>
          y ≫ (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).map ψ) =
        (e B') ∘ (fun x => x ≫ ψ) ∘ (e B).symm := by
      funext y
      simp only [Function.comp_apply, e]
      rw [DerivedCategory.homologyFromSingleAddEquiv_comp, AddEquiv.apply_symm_apply]
    rw [hcomm]
    exact (e B').bijective.comp ((h q).comp (e B).symm.bijective)
  set φ := (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).map ψ
  have hφ : Function.Bijective φ := by
    let y : ∀ G : AddCommGrpCat.{u + 1}, G → (uliftIntAb.{u} ⟶ G) := fun G a =>
      AddCommGrpCat.ofHom ((zmultiplesHom G a).comp (AddEquiv.ulift : ULift.{u + 1} ℤ ≃+ ℤ))
    have hy : ∀ (G : AddCommGrpCat.{u + 1}) (a : G), (y G a) (ULift.up 1) = a :=
      fun G a => one_smul ℤ a
    have hyφ : ∀ a, y _ a ≫ φ = y _ (φ a) := by
      intro a
      ext ⟨n⟩
      simp [y]
    refine ⟨fun a b hab => ?_, fun b' => ?_⟩
    · have h1 : y _ a ≫ φ = y _ b ≫ φ := by rw [hyφ, hyφ, hab]
      rw [← hy _ a, ← hy _ b]
      exact congrArg (fun f => f (ULift.up 1)) (hq.1 h1)
    · obtain ⟨x, hx⟩ := hq.2 (y _ b')
      refine ⟨x (ULift.up 1), ?_⟩
      simpa [hy] using congrArg (fun f => f (ULift.up 1)) hx
  exact (ConcreteCategory.isIso_iff_bijective φ).2 hφ

section Etale

-- `RΓ(Y, -)`, its restriction maps and Leray are defined in the standard model of the derived
-- category in the library, so the statements about them are made there.
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable (Y : Scheme.{u})

/-- The constant sheaf functor preserves finite limits: the constant-presheaf functor does, and
sheafification is left exact. -/
instance constantSheaf_smallEtale_preservesFiniteLimits :
    PreservesFiniteLimits (constantSheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :=
  comp_preservesFiniteLimits (Functor.const _) (presheafToSheaf _ _)

/-- The constant sheaf functor preserves finite colimits, being a left adjoint. -/
instance constantSheaf_smallEtale_preservesFiniteColimits :
    PreservesFiniteColimits (constantSheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :=
  have := (constantSheafΓAdj (smallEtaleTopology Y) AddCommGrpCat.{u + 1}).isLeftAdjoint
  inferInstance

/-- **The constant sheaf functor is left adjoint to `RΓ(Y, -)`** on unbounded derived categories
of abelian sheaves on the small étale site: the constant sheaf functor is exact and left adjoint
to global sections, and every complex has a K-injective resolution
(`Stacks.DerivedFunctor.derivedAdjunction`, [Stacks, Tag 09T5]). -/
def smallEtaleConstantDerivedAdjunction :
    (constantSheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}).mapDerivedCategory ⊣
      smallEtaleDerivedGlobalSections Y :=
  Stacks.DerivedFunctor.derivedAdjunction
    (constantSheafΓAdj (smallEtaleTopology Y) AddCommGrpCat.{u + 1})
    (smallEtaleDerivedGlobalSections Y) (smallEtaleDerivedGlobalSectionsUnit Y)
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective

/-- The constant sheaf `ℤ_Y`. -/
abbrev smallEtaleConstantInt : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} :=
  (constantSheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}).obj uliftIntAb

variable {Y}

/-- Composing with `φ` is bijective on morphisms out of `ℤ_Y[q]` iff composing with `RΓ(Y, φ)` is
bijective on morphisms out of `ℤ[q]`, by the derived adjunction. -/
private theorem bijective_comp_iff_bijective_comp_derivedGlobalSections_map
    {M N : smallEtaleDerivedCategory Y} (φ : M ⟶ N) (q : ℤ) :
    Function.Bijective
      (fun x : (DerivedCategory.singleFunctor _ q).obj (smallEtaleConstantInt Y) ⟶ M => x ≫ φ) ↔
    Function.Bijective
      (fun y : (DerivedCategory.singleFunctor AddCommGrpCat.{u + 1} q).obj uliftIntAb ⟶
        (smallEtaleDerivedGlobalSections Y).obj M =>
        y ≫ (smallEtaleDerivedGlobalSections Y).map φ) := by
  let adj := smallEtaleConstantDerivedAdjunction Y
  let c := (constantSheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})
  let e : c.mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor AddCommGrpCat.{u + 1} q).obj uliftIntAb) ≅
      (DerivedCategory.singleFunctor _ q).obj (smallEtaleConstantInt Y) :=
    (c.mapDerivedCategorySingleFunctor q).app uliftIntAb
  let E : ∀ Z : smallEtaleDerivedCategory Y,
      ((DerivedCategory.singleFunctor _ q).obj (smallEtaleConstantInt Y) ⟶ Z) ≃
        ((DerivedCategory.singleFunctor AddCommGrpCat.{u + 1} q).obj uliftIntAb ⟶
          (smallEtaleDerivedGlobalSections Y).obj Z) := fun Z =>
    (e.homCongr (Iso.refl Z)).symm.trans (adj.homEquiv _ Z)
  have hcomm : (fun y : (DerivedCategory.singleFunctor AddCommGrpCat.{u + 1} q).obj uliftIntAb ⟶
      (smallEtaleDerivedGlobalSections Y).obj M => y ≫ (smallEtaleDerivedGlobalSections Y).map φ) =
      (E N) ∘ (fun x => x ≫ φ) ∘ (E M).symm := by
    funext y
    simp only [Function.comp_apply, E, Equiv.symm_trans_apply, Equiv.trans_apply,
      Iso.homCongr_apply, Iso.homCongr_symm, Iso.symm_inv, Iso.symm_symm_eq, Iso.refl_symm,
      Iso.refl_hom, Category.comp_id, Category.assoc, Iso.hom_inv_id_assoc]
    rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
  rw [hcomm, Function.Bijective.of_comp_iff' (E N).bijective,
    Function.Bijective.of_comp_iff _ (E M).symm.bijective]

/-- **`RΓ(Y, -)` inverts a morphism bijective on morphisms out of `ℤ_Y[q]`.** If composing with
`φ : M ⟶ N` is bijective on morphisms out of `ℤ_Y` placed in degree `q`, for every `q`, then
`RΓ(Y, φ)` is an isomorphism. -/
theorem isIso_smallEtaleDerivedGlobalSections_map_of_bijective {M N : smallEtaleDerivedCategory Y}
    (φ : M ⟶ N)
    (h : ∀ q : ℤ, Function.Bijective
      (fun x : (DerivedCategory.singleFunctor _ q).obj (smallEtaleConstantInt Y) ⟶ M => x ≫ φ)) :
    IsIso ((smallEtaleDerivedGlobalSections Y).map φ) :=
  isIso_of_bijective_comp_singleFunctor_uliftInt _ fun q =>
    (bijective_comp_iff_bijective_comp_derivedGlobalSections_map φ q).1 (h q)

/-- **Converse**: if `RΓ(Y, φ)` is an isomorphism, composing with `φ` is bijective on morphisms out
of `ℤ_Y[q]` for every `q`. -/
theorem bijective_of_isIso_smallEtaleDerivedGlobalSections_map {M N : smallEtaleDerivedCategory Y}
    (φ : M ⟶ N) [IsIso ((smallEtaleDerivedGlobalSections Y).map φ)] (q : ℤ) :
    Function.Bijective
      (fun x : (DerivedCategory.singleFunctor _ q).obj (smallEtaleConstantInt Y) ⟶ M => x ≫ φ) :=
  (bijective_comp_iff_bijective_comp_derivedGlobalSections_map φ q).2
    ⟨fun a b hab => (cancel_mono _).1 hab,
      fun z => ⟨z ≫ inv ((smallEtaleDerivedGlobalSections Y).map φ), by simp⟩⟩

end Etale

/-- **Bijectivity of a functor on morphisms is invariant under shifting both ends**, for a functor
commuting with the shift. -/
theorem map_bijective_iff_shift {C D : Type*} [Category C] [Category D] [HasShift C ℤ]
    [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ] (X Y : C) (n : ℤ) :
    Function.Bijective (F.map : (X ⟶ Y) → _) ↔
      Function.Bijective (F.map : (X⟦n⟧ ⟶ Y⟦n⟧) → _) := by
  have h : (F.map : (X⟦n⟧ ⟶ Y⟦n⟧) → _) ∘ (shiftFunctor C n).map =
      (Iso.homCongr ((F.commShiftIso n).app X).symm ((F.commShiftIso n).app Y).symm) ∘
        (shiftFunctor D n).map ∘ F.map := by
    funext f
    simp only [Function.comp_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.app_hom, Iso.symm_hom,
      Iso.app_inv]
    rw [← Category.assoc, ← Functor.commShiftIso_hom_naturality, Category.assoc,
      Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have hC : Function.Bijective ((shiftFunctor C n).map : (X ⟶ Y) → _) :=
    (shiftEquiv C n).fullyFaithfulFunctor.map_bijective X Y
  have hD : Function.Bijective
      ((shiftFunctor D n).map : (F.obj X ⟶ F.obj Y) → _) :=
    (shiftEquiv D n).fullyFaithfulFunctor.map_bijective _ _
  rw [← Function.Bijective.of_comp_iff _ hC, h,
    Function.Bijective.of_comp_iff' (Iso.homCongr _ _).bijective,
    Function.Bijective.of_comp_iff' hD]

section Single

variable {𝒜 ℬ : Type*} [Category 𝒜] [Abelian 𝒜] [Category ℬ] [Abelian ℬ]
  [HasDerivedCategory 𝒜] [HasDerivedCategory ℬ]
  (F₀ : 𝒜 ⥤ ℬ) [F₀.Additive] [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]

/-- **An exact functor is bijective on morphisms from `A[q]` to `B[0]`** for `q < 0`, where both
sides vanish, and for `q ≥ 0` as soon as it is bijective on `Ext^q(A, B)`, that is on morphisms
from `A[0]` to `B[0]⟦q⟧`. -/
theorem map_bijective_singleFunctor_of_isBijectiveOnExt (A B : 𝒜) (q : ℤ)
    (hext : ∀ n : ℕ, Function.Bijective (F₀.mapDerivedCategory.map :
      ((DerivedCategory.singleFunctor 𝒜 0).obj A ⟶
        ((DerivedCategory.singleFunctor 𝒜 0).obj B)⟦(n : ℤ)⟧) → _)) :
    Function.Bijective (F₀.mapDerivedCategory.map :
      ((DerivedCategory.singleFunctor 𝒜 q).obj A ⟶ (DerivedCategory.singleFunctor 𝒜 0).obj B) →
        _) := by
  rcases lt_or_ge q 0 with hq | hq
  · have h0 : ∀ f : (DerivedCategory.singleFunctor 𝒜 q).obj A ⟶
        (DerivedCategory.singleFunctor 𝒜 0).obj B, f = 0 := fun f =>
      DerivedCategory.TStructure.t.zero f q 0 hq
    have h1 : ∀ g : F₀.mapDerivedCategory.obj ((DerivedCategory.singleFunctor 𝒜 q).obj A) ⟶
        F₀.mapDerivedCategory.obj ((DerivedCategory.singleFunctor 𝒜 0).obj B), g = 0 := by
      intro g
      let e₁ := (F₀.mapDerivedCategorySingleFunctor q).app A
      let e₂ := (F₀.mapDerivedCategorySingleFunctor 0).app B
      have : (e₁.inv ≫ g ≫ e₂.hom : (DerivedCategory.singleFunctor ℬ q).obj (F₀.obj A) ⟶
          (DerivedCategory.singleFunctor ℬ 0).obj (F₀.obj B)) = 0 :=
        DerivedCategory.TStructure.t.zero _ q 0 hq
      simpa using congrArg (fun k => e₁.hom ≫ k ≫ e₂.inv) this
    refine ⟨fun a b _ => (h0 a).trans (h0 b).symm, fun g => ⟨0, ?_⟩⟩
    rw [Functor.map_zero, h1 g]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    rw [map_bijective_iff_shift F₀.mapDerivedCategory _ _ (n : ℤ),
      map_bijective_iff_of_objIso F₀.mapDerivedCategory
        (((DerivedCategory.singleFunctors 𝒜).shiftIso (n : ℤ) 0 n (by simp)).app A)
        (Iso.refl _)]
    exact hext n

/-- **Converse, in degree `n ≥ 0`**: bijectivity on morphisms from `A` placed in degree `n` to
`B` placed in degree `0` is bijectivity on `Ext^n(A, B)`. -/
theorem map_bijective_shift_of_map_bijective_singleFunctor (A B : 𝒜) (n : ℕ)
    (h : Function.Bijective (F₀.mapDerivedCategory.map :
      ((DerivedCategory.singleFunctor 𝒜 n).obj A ⟶ (DerivedCategory.singleFunctor 𝒜 0).obj B) →
        _)) :
    Function.Bijective (F₀.mapDerivedCategory.map :
      ((DerivedCategory.singleFunctor 𝒜 0).obj A ⟶
        ((DerivedCategory.singleFunctor 𝒜 0).obj B)⟦(n : ℤ)⟧) → _) := by
  rwa [map_bijective_iff_shift F₀.mapDerivedCategory _ _ (n : ℤ),
    map_bijective_iff_of_objIso F₀.mapDerivedCategory
      (((DerivedCategory.singleFunctors 𝒜).shiftIso (n : ℤ) 0 n (by simp)).app A)
      (Iso.refl _)] at h

/-- Composing with the unit of an adjunction `F ⊣ G` is applying `F` followed by the adjunction
bijection. -/
private theorem comp_unit_app_eq_homEquiv_comp_map {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (X Z : C) :
    (fun x : X ⟶ Z => x ≫ adj.unit.app Z) = adj.homEquiv X (F.obj Z) ∘ F.map := by
  funext x
  simp [Adjunction.homEquiv_unit]

end Single

section Etale

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {Y W : Scheme.{u}}

/-- **Restriction of derived sections at an abelian sheaf is invertible when it is bijective on
`Ext` out of the constant sheaf.** For `h : W ⟶ Y` and an abelian sheaf `G` on the small étale
site of `Y`, if the inverse image `h⁻¹` is bijective on `Ext^n(ℤ_Y, G)` for every `n`, then
`RΓ(Y, G) ⟶ RΓ(W, h⁻¹G)` is an isomorphism. -/
theorem isIso_smallEtaleDerivedGlobalSectionsRestriction_single_of_isBijectiveOnExt
    (h : W ⟶ Y) (G : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})
    (hG : ∀ n : ℕ, IsBijectiveOnExt (smallEtalePullbackAb h) (smallEtaleConstantInt Y) G n) :
    IsIso ((smallEtaleDerivedGlobalSectionsRestriction h).app
      ((DerivedCategory.singleFunctor _ 0).obj G)) := by
  rw [smallEtaleDerivedGlobalSectionsRestriction_app]
  refine IsIso.comp_isIso' ?_ inferInstance
  refine isIso_smallEtaleDerivedGlobalSections_map_of_bijective _ fun q => ?_
  exact (congrArg Function.Bijective
    (comp_unit_app_eq_homEquiv_comp_map (smallEtaleDerivedAdjunctionAb h) _ _)).mpr
    ((Equiv.bijective _).comp
      (map_bijective_singleFunctor_of_isBijectiveOnExt (smallEtalePullbackAb h) _ G q hG))

/-- **Converse**: if restriction of derived sections at `G` is invertible, then `h⁻¹` is
bijective on `Ext^n(ℤ_Y, G)` for every `n`. -/
theorem isBijectiveOnExt_of_isIso_smallEtaleDerivedGlobalSectionsRestriction_single
    (h : W ⟶ Y) (G : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})
    (hiso : IsIso ((smallEtaleDerivedGlobalSectionsRestriction h).app
      ((DerivedCategory.singleFunctor _ 0).obj G))) (n : ℕ) :
    IsBijectiveOnExt (smallEtalePullbackAb h) (smallEtaleConstantInt Y) G n := by
  rw [smallEtaleDerivedGlobalSectionsRestriction_app] at hiso
  have : IsIso ((smallEtaleDerivedGlobalSections Y).map ((smallEtaleDerivedAdjunctionAb h).unit.app
      ((DerivedCategory.singleFunctor _ 0).obj G))) :=
    IsIso.of_isIso_comp_right _ ((smallEtaleDerivedPushforwardGlobalSectionsIso h).hom.app _)
  have hb := (congrArg Function.Bijective
    (comp_unit_app_eq_homEquiv_comp_map (smallEtaleDerivedAdjunctionAb h) _ _)).mp
    (bijective_of_isIso_smallEtaleDerivedGlobalSections_map
      ((smallEtaleDerivedAdjunctionAb h).unit.app ((DerivedCategory.singleFunctor _ 0).obj G)) n)
  exact map_bijective_shift_of_map_bijective_singleFunctor (smallEtalePullbackAb h) _ G n
    ((Function.Bijective.of_comp_iff' (Equiv.bijective _) _).mp hb)

end Etale

end Stacks.EtaleCohomology

end
