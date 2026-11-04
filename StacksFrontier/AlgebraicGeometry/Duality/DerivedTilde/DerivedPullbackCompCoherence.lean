module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionCoherence

/-!
# Coherence of the composition isomorphisms of derived pullback on schemes

The composition isomorphisms `Stacks.Duality.derivedPullbackCompIso` of Stacks 0D5S for
morphisms of schemes satisfy the cocycle identity. Together with the unit isomorphism
`L(𝟙 X)^* ≅ 𝟭` of `Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIsoGeneral`, they
also satisfy both unit laws, so `X ↦ D(𝒪_X)`, `f ↦ Lf^*` is a pseudofunctor. A consequence is the
coherence for a commutative square of retractions,
`Stacks.Duality.derivedPullbackCompIso_retraction_square`.

## Main results

* `Stacks.Duality.derivedPullbackCompIso_hom_app_assoc`: the cocycle identity.
* `Stacks.Duality.exists_derivedPullbackIdIso_unit_laws`: a unit isomorphism satisfying both unit
  laws.
* `Stacks.Duality.derivedPullbackCompIso_retraction_square`: coherence for a square of
  retractions.

All statements are at the locally small model, the global instance
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. They are read off from the statements at
an arbitrary model in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionCoherence`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

noncomputable section

variable {X Y Z W : Scheme.{u}}

/-- **The cocycle identity of Stacks 0D5S for schemes**, at an object, with the two bracketings
of the threefold composite identified by `Category.assoc`. -/
@[reassoc]
theorem derivedPullbackCompIso_hom_app_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (M : DerivedCategory W.Modules) :
    (derivedPullbackCompIso f g).hom.app ((derivedPullback h).obj M) ≫
        (derivedPullbackCompIso (f ≫ g) h).hom.app M ≫
        eqToHom (congrArg (fun t : X ⟶ W => (derivedPullback t).obj M) (Category.assoc f g h)) =
      (derivedPullback f).map ((derivedPullbackCompIso g h).hom.app M) ≫
        (derivedPullbackCompIso f (g ≫ h)).hom.app M := by
  have key : (derivedPullbackCompIso f g).hom.app ((derivedPullback h).obj M) ≫
        (derivedPullbackCompIso (f ≫ g) h).hom.app M =
      (derivedPullback f).map ((derivedPullbackCompIso g h).hom.app M) ≫
        (derivedPullbackCompIso f (g ≫ h)).hom.app M :=
    (NatTrans.congr_app
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical_hom_assoc
        f.toLRSHom.toShHom g.toLRSHom.toShHom h.toLRSHom.toShHom) M).trans (Category.id_comp _)
  exact (Category.assoc _ _ _).symm.trans ((Category.comp_id _).trans key)

/-- The cocycle identity of Stacks 0D5S for schemes, read in the other direction. -/
@[reassoc]
theorem derivedPullbackCompIso_hom_app_assoc' (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (M : DerivedCategory W.Modules) :
    (derivedPullbackCompIso f g).hom.app ((derivedPullback h).obj M) ≫
        (derivedPullbackCompIso (f ≫ g) h).hom.app M =
      (derivedPullback f).map ((derivedPullbackCompIso g h).hom.app M) ≫
        (derivedPullbackCompIso f (g ≫ h)).hom.app M ≫
        eqToHom (congrArg (fun t : X ⟶ W => (derivedPullback t).obj M)
          (Category.assoc f g h).symm) := by
  rw [← derivedPullbackCompIso_hom_app_assoc_assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

/-- **The left unit law of Stacks 0D5S for schemes**, at an object. -/
theorem derivedPullbackCompIso_hom_app_id_comp (g : Y ⟶ Z) (M : DerivedCategory Z.Modules) :
    (derivedPullbackCompIso (𝟙 Y) g).hom.app M =
      (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIsoGeneral
          Y.toRingedSpace).hom.app ((derivedPullback g).obj M) ≫
        eqToHom (congrArg (fun t : Y ⟶ Z => (derivedPullback t).obj M) (Category.id_comp g).symm) :=
  ((NatTrans.congr_app
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical_hom_id_comp
      g.toLRSHom.toShHom) M).trans (Category.comp_id _)).trans (Category.comp_id _).symm

/-- **The right unit law of Stacks 0D5S for schemes**, at an object. -/
theorem derivedPullbackCompIso_hom_app_comp_id (f : X ⟶ Y) (M : DerivedCategory Y.Modules) :
    (derivedPullbackCompIso f (𝟙 Y)).hom.app M =
      (derivedPullback f).map
          ((Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIsoGeneral
            Y.toRingedSpace).hom.app M) ≫
        eqToHom (congrArg (fun t : X ⟶ Y => (derivedPullback t).obj M) (Category.comp_id f).symm) :=
  ((NatTrans.congr_app
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical_hom_comp_id
      f.toLRSHom.toShHom) M).trans (Category.comp_id _)).trans (Category.comp_id _).symm

/-- **Derived pullback along the identity is the identity, compatibly with Stacks 0D5S**: there
is an isomorphism `L(𝟙 X)^* ≅ 𝟭` satisfying both unit laws against the composition isomorphisms
`derivedPullbackCompIso`. -/
theorem exists_derivedPullbackIdIso_unit_laws (X : Scheme.{u}) :
    ∃ ι : derivedPullback (𝟙 X) ≅ 𝟭 (DerivedCategory X.Modules),
      (∀ {Y : Scheme.{u}} (f : Y ⟶ X) (M : DerivedCategory X.Modules),
        (derivedPullbackCompIso f (𝟙 X)).hom.app M = (derivedPullback f).map (ι.hom.app M) ≫
          eqToHom (congrArg (fun t : Y ⟶ X => (derivedPullback t).obj M)
            (Category.comp_id f).symm)) ∧
      (∀ {Z : Scheme.{u}} (g : X ⟶ Z) (M : DerivedCategory Z.Modules),
        (derivedPullbackCompIso (𝟙 X) g).hom.app M = ι.hom.app ((derivedPullback g).obj M) ≫
          eqToHom (congrArg (fun t : X ⟶ Z => (derivedPullback t).obj M)
            (Category.id_comp g).symm)) :=
  ⟨Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIsoGeneral X.toRingedSpace,
    fun f M => derivedPullbackCompIso_hom_app_comp_id f M,
    fun g M => derivedPullbackCompIso_hom_app_id_comp g M⟩

/-- Transport along an equality of the second morphism commutes with the composition
isomorphism. -/
@[reassoc]
theorem derivedPullback_map_eqToHom_comp_derivedPullbackCompIso_hom_app (f : X ⟶ Y)
    {h₁ h₂ : Y ⟶ Z} (hh : h₁ = h₂) (M : DerivedCategory Z.Modules) :
    (derivedPullback f).map
        (eqToHom (congrArg (fun t : Y ⟶ Z => (derivedPullback t).obj M) hh)) ≫
        (derivedPullbackCompIso f h₂).hom.app M =
      (derivedPullbackCompIso f h₁).hom.app M ≫
        eqToHom (congrArg (fun t : Y ⟶ Z => (derivedPullback (f ≫ t)).obj M) hh) := by
  subst hh
  simp

/-- Transport along an equality of the first morphism commutes with the composition
isomorphism. -/
@[reassoc]
theorem eqToHom_comp_derivedPullbackCompIso_hom_app {f₁ f₂ : X ⟶ Y} (hf : f₁ = f₂) (h : Y ⟶ Z)
    (M : DerivedCategory Z.Modules) :
    eqToHom (congrArg (fun t : X ⟶ Y => (derivedPullback t).obj ((derivedPullback h).obj M)) hf) ≫
        (derivedPullbackCompIso f₂ h).hom.app M =
      (derivedPullbackCompIso f₁ h).hom.app M ≫
        eqToHom (congrArg (fun t : X ⟶ Y => (derivedPullback (t ≫ h)).obj M) hf) := by
  subst hf
  simp

/-- **Coherence for a square of retractions.** Let `i ≫ r = 𝟙` and `i' ≫ r' = 𝟙`, and let
`c ≫ i = i' ≫ q` and `q ≫ r = r' ≫ c`. Then the two identifications of `L(c)^*M` with
`L(i')^* L(r')^* L(c)^* M` built from the composition isomorphisms of Stacks 0D5S and unit
isomorphisms `ι, ι'` satisfying the unit laws agree. -/
theorem derivedPullbackCompIso_retraction_square {A A' P P' : Scheme.{u}} (c : A' ⟶ A)
    (i : A ⟶ P) (r : P ⟶ A) (i' : A' ⟶ P') (q : P' ⟶ P) (r' : P' ⟶ A') (hr : i ≫ r = 𝟙 A)
    (hr' : i' ≫ r' = 𝟙 A') (w₁ : c ≫ i = i' ≫ q) (w₂ : q ≫ r = r' ≫ c)
    (ι : derivedPullback (𝟙 A) ≅ 𝟭 _) (ι' : derivedPullback (𝟙 A') ≅ 𝟭 _)
    (hι : ∀ M, (derivedPullbackCompIso c (𝟙 A)).hom.app M = (derivedPullback c).map (ι.hom.app M) ≫
      eqToHom (congrArg (fun t : A' ⟶ A => (derivedPullback t).obj M) (Category.comp_id c).symm))
    (hι' : ∀ M, (derivedPullbackCompIso (𝟙 A') c).hom.app M =
      ι'.hom.app ((derivedPullback c).obj M) ≫
        eqToHom (congrArg (fun t : A' ⟶ A => (derivedPullback t).obj M) (Category.id_comp c).symm))
    (M : DerivedCategory A.Modules) :
    (derivedPullback c).map (ι.inv.app M ≫
          eqToHom (congrArg (fun t : A ⟶ A => (derivedPullback t).obj M) hr.symm) ≫
          (derivedPullbackCompIso i r).inv.app M) ≫
        (derivedPullbackCompIso c i).hom.app ((derivedPullback r).obj M) ≫
        eqToHom (congrArg (fun t : A' ⟶ P => (derivedPullback t).obj ((derivedPullback r).obj M))
          w₁) ≫
        (derivedPullbackCompIso i' q).inv.app ((derivedPullback r).obj M) ≫
        (derivedPullback i').map ((derivedPullbackCompIso q r).hom.app M ≫
          eqToHom (congrArg (fun t : P' ⟶ A => (derivedPullback t).obj M) w₂) ≫
          (derivedPullbackCompIso r' c).inv.app M) =
      ι'.inv.app ((derivedPullback c).obj M) ≫
        eqToHom (congrArg (fun t : A' ⟶ A' => (derivedPullback t).obj ((derivedPullback c).obj M))
          hr'.symm) ≫
        (derivedPullbackCompIso i' r').inv.app ((derivedPullback c).obj M) := by
  rw [← cancel_mono ((derivedPullback i').map ((derivedPullbackCompIso r' c).hom.app M) ≫
    (derivedPullbackCompIso i' (r' ≫ c)).hom.app M)]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (derivedPullback i') ((derivedPullbackCompIso r' c).inv.app M),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    derivedPullback_map_eqToHom_comp_derivedPullbackCompIso_hom_app i' w₂ M,
    ← derivedPullbackCompIso_hom_app_assoc_assoc i' q r M, Iso.inv_hom_id_app_assoc,
    eqToHom_comp_derivedPullbackCompIso_hom_app_assoc w₁ r M,
    derivedPullbackCompIso_hom_app_assoc'_assoc c i r M,
    ← Functor.map_comp_assoc (derivedPullback c) ((derivedPullbackCompIso i r).inv.app M),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    derivedPullback_map_eqToHom_comp_derivedPullbackCompIso_hom_app_assoc c hr.symm M, hι]
  rw [Category.assoc, ← Functor.map_comp_assoc (derivedPullback c) (ι.inv.app M),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← derivedPullbackCompIso_hom_app_assoc i' r' c M, Iso.inv_hom_id_app_assoc,
    eqToHom_comp_derivedPullbackCompIso_hom_app_assoc hr'.symm c M, hι']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, eqToHom_trans]

/-- Transport along an equality of morphisms commutes with derived pullback of a morphism. -/
@[reassoc]
theorem derivedPullback_map_comp_eqToHom {t₁ t₂ : Y ⟶ X} (h : t₁ = t₂)
    {K K₂ : DerivedCategory X.Modules} (e : K ⟶ K₂) :
    (derivedPullback t₁).map e ≫
        eqToHom (congrArg (fun t : Y ⟶ X => (derivedPullback t).obj K₂) h) =
      eqToHom (congrArg (fun t : Y ⟶ X => (derivedPullback t).obj K) h) ≫
        (derivedPullback t₂).map e := by
  subst h
  simp

/-- For a retraction `i ≫ r = 𝟙`, the identification `M ≅ L(i)^* L(r)^* M` built from a unit
isomorphism `L(𝟙)^* ≅ 𝟭` and the composition isomorphism is natural in `M`. -/
theorem derivedPullbackCompIso_retraction_naturality {A P : Scheme.{u}} (i : A ⟶ P) (r : P ⟶ A)
    (hr : i ≫ r = 𝟙 A) (ι : derivedPullback (𝟙 A) ≅ 𝟭 _) {M M' : DerivedCategory A.Modules}
    (q : M ⟶ M') :
    q ≫ ι.inv.app M' ≫ eqToHom (congrArg (fun t : A ⟶ A => (derivedPullback t).obj M') hr.symm) ≫
        (derivedPullbackCompIso i r).inv.app M' =
      (ι.inv.app M ≫ eqToHom (congrArg (fun t : A ⟶ A => (derivedPullback t).obj M) hr.symm) ≫
        (derivedPullbackCompIso i r).inv.app M) ≫
          (derivedPullback i).map ((derivedPullback r).map q) := by
  have h₁ := ι.inv.naturality q
  have h₃ := (derivedPullbackCompIso i r).inv.naturality q
  simp only [Functor.id_map, Functor.comp_map] at h₁ h₃
  rw [reassoc_of% h₁]
  simp only [Category.assoc]
  rw [← h₃]
  rw [derivedPullback_map_comp_eqToHom_assoc hr.symm q]

end

end Stacks.Duality
