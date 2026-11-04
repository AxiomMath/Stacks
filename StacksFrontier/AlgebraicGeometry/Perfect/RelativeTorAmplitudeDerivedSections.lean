module

public import StacksFrontier.AlgebraicGeometry.Perfect.InverseImageTorAmplitudeStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeAtPoint
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkCompact
public import Mathlib.Tactic.TFAE
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectDerivedSections
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictFunctorAlongIso
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineSectionsComparison

/-!
# Relative Tor amplitude on an affine open and the derived sections

Let `f : X ⟶ S` be a morphism of schemes, `E` an object of `D(𝒪_X)` with quasi-coherent
cohomology sheaves, and `U ⊆ f ⁻¹ᵁ V` a compatible pair of affine opens. Then `RΓ(U, E)`, read
over `Γ(S, V)`, has Tor amplitude in `[a, b]` exactly when `E_y` has Tor amplitude in `[a, b]`
over `𝒪_{S, f y}` for every `y ∈ U`: on `Spec Γ(X, U)` the object `E|_U` is the sheaf associated
to `RΓ(U, E)` (Stacks 06Z0), and Stacks 0DHY reads Tor amplitude over the base of an associated
sheaf on the module side.

With the stalkwise criterion of
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeStalkwise` this gives the Tor clause
of Stacks 0DI2: `E` locally has finite Tor dimension over `f^{-1}𝒪_S` if and only if `RΓ(U, E)`
has finite Tor dimension over `Γ(S, V)` for every compatible pair of affine opens, if and only if
this holds on the members of an affine open covering.

## Main results

* `AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeAtPoint_pullback_iff`: the stalkwise condition is
  unchanged by restriction to an open subscheme.
* `AlgebraicGeometry.Scheme.Hom.forall_hasTorAmplitudeAtPoint_iff_derivedSections`: the affine
  comparison.
* `AlgebraicGeometry.Scheme.Hom.torDimension_derivedSections_tfae`: the Tor clause of Stacks 0DI2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open StacksDraft.TorAmplitude
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A property of objects that transports along isomorphisms holds for isomorphic objects
simultaneously. -/
private theorem iff_of_iso_of_imp {C : Type*} [Category C] {P : C → Prop}
    (hP : ∀ {A B : C}, (A ≅ B) → P A → P B) {A B : C} (e : A ≅ B) : P A ↔ P B :=
  ⟨hP e, hP e.symm⟩

/-- The stalkwise condition is invariant under isomorphism in `D(𝒪_X)`, as an equivalence. -/
private theorem hasTorAmplitudeAtPoint_iff_of_iso {E E' : DerivedCategory X.Modules} (e : E ≅ E')
    {x : X} {a b : ℤ} : HasTorAmplitudeAtPoint f E x a b ↔ HasTorAmplitudeAtPoint f E' x a b :=
  iff_of_iso_of_imp (fun e => HasTorAmplitudeAtPoint.of_iso f e) e

/-- **The stalkwise condition under composition with an open immersion of the base.** -/
theorem hasTorAmplitudeAtPoint_comp_iff {V : Scheme.{u}} (k : S ⟶ V) [IsOpenImmersion k]
    (E : DerivedCategory X.Modules) (x : X) (a b : ℤ) :
    HasTorAmplitudeAtPoint (f ≫ k) E x a b ↔ HasTorAmplitudeAtPoint f E x a b := by
  let K := DerivedCategory.Q.objPreimage E
  have eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have key := hasTorAmplitudeCanonicalLift_restrictScalars_comp_iff (f.stalkMap x).hom
    (k.stalkMap (f.base x)).hom ((f ≫ k).stalkMap x).hom
    (stalkRingEquivOfIsOpenImmersion k (f.base x)) rfl
    (Stacks.ModuleSkyscraper.stalkMap_hom_comp f k x)
    (((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) a b
  rw [← hasTorAmplitudeAtPoint_iff_of_iso f eK, ← hasTorAmplitudeAtPoint_iff_of_iso (f ≫ k) eK,
    hasTorAmplitudeAtPoint_Q_iff, hasTorAmplitudeAtPoint_Q_iff, hasTorAmplitudeCanonical_iff_lift,
    hasTorAmplitudeCanonical_iff_lift]
  exact key

/-- **The stalkwise condition is unchanged by restriction to an open subscheme.** For an open
immersion `j : V ⟶ X`, a complex `K` of `𝒪_X`-modules and `y ∈ V`, the relative stalk of `j^*K`
at `y` over `j ≫ f` has the Tor amplitude of the relative stalk of `K` at `j y` over `f`. -/
theorem hasTorAmplitudeAtPoint_pullback_iff {V : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    (K : CochainComplex X.Modules ℤ) (y : V) (a b : ℤ) :
    HasTorAmplitudeAtPoint (j ≫ f)
        (DerivedCategory.Q.obj (((Scheme.Modules.pullback j).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) y a b ↔
      HasTorAmplitudeAtPoint f (DerivedCategory.Q.obj K) (j.base y) a b := by
  rw [hasTorAmplitudeAtPoint_Q_iff, hasTorAmplitudeAtPoint_Q_iff,
    hasTorAmplitudeCanonical_iff_lift, hasTorAmplitudeCanonical_iff_lift]
  let e := ((ModuleCat.restrictScalars ((j ≫ f).stalkMap y).hom).mapHomologicalComplex
    (ComplexShape.up ℤ)).mapIso (pullbackRelativeStalkObjIso j y K)
  refine Iff.trans (iff_of_iso_of_imp (fun e => hasTorAmplitudeCanonicalLift_of_iso e a b)
    (DerivedCategory.Q.mapIso e)) ?_
  exact hasTorAmplitudeCanonicalLift_restrictScalars_extendScalars_iff
    (f.stalkMap (j.base y)).hom (j.stalkMap y).hom ((j ≫ f).stalkMap y).hom
    (stalkRingEquivOfIsOpenImmersion j y) rfl (Stacks.ModuleSkyscraper.stalkMap_hom_comp j f y)
    (((Stacks.ModuleSkyscraper.modulesStalkFunctor X (j.base y)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) a b

/-- **The stalkwise condition is unchanged by restriction to an open subscheme**, for an object of
the derived category restricted by `AlgebraicGeometry.Scheme.Modules.restrictFunctor`. -/
theorem hasTorAmplitudeAtPoint_restrictFunctor_iff {V : Scheme.{u}} (j : V ⟶ X)
    [IsOpenImmersion j] (E : DerivedCategory X.Modules) (y : V) (a b : ℤ) :
    HasTorAmplitudeAtPoint (j ≫ f)
        ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj E) y a b ↔
      HasTorAmplitudeAtPoint f E (j.base y) a b := by
  let K := DerivedCategory.Q.objPreimage E
  have eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let eR : (Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj E ≅
      DerivedCategory.Q.obj (((Scheme.Modules.pullback j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) :=
    (Scheme.Modules.restrictFunctor j).mapDerivedCategory.mapIso eK.symm ≪≫
      (Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactors.app K ≪≫
      DerivedCategory.Q.mapIso (HomologicalComplex.Hom.isoOfComponents
        (fun i => (Scheme.Modules.restrictFunctorIsoPullback j).app (K.X i))
        (fun i k _ =>
          ((Scheme.Modules.restrictFunctorIsoPullback j).hom.naturality (K.d i k)).symm))
  rw [hasTorAmplitudeAtPoint_iff_of_iso (j ≫ f) eR, hasTorAmplitudeAtPoint_pullback_iff,
    hasTorAmplitudeAtPoint_iff_of_iso f eK.symm]

/-- Restriction along an open immersion undoes pushforward along it, on derived categories. -/
def restrictFunctorPushforwardObjIso {A B : Scheme.{u}} (g : A ⟶ B) [IsIso g]
    (F : DerivedCategory A.Modules) :
    (Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj
        ((Scheme.Modules.pushforward g).mapDerivedCategory.obj F) ≅ F :=
  let L := DerivedCategory.Q.objPreimage F
  let eL : DerivedCategory.Q.obj L ≅ F := DerivedCategory.Q.objObjPreimageIso F
  (Scheme.Modules.restrictFunctor g).mapDerivedCategory.mapIso
      ((Scheme.Modules.pushforward g).mapDerivedCategory.mapIso eL.symm ≪≫
        (Scheme.Modules.pushforward g).mapDerivedCategoryFactors.app L) ≪≫
    (Scheme.Modules.restrictFunctor g).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso (HomologicalComplex.Hom.isoOfComponents
      (C₁ := ((Scheme.Modules.restrictFunctor g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((Scheme.Modules.pushforward g).mapHomologicalComplex (ComplexShape.up ℤ)).obj L))
      (C₂ := L)
      (fun i => (Scheme.Modules.restrictFunctorAdjCounitIso g).app (L.X i))
      (fun i k _ => ((Scheme.Modules.restrictFunctorAdjCounitIso g).hom.naturality
        (L.d i k)).symm)) ≪≫ eL

/-- **Relative Tor amplitude on a compatible pair of affine opens is Tor amplitude of the derived
sections.** For `E` with quasi-coherent cohomology sheaves and affine opens `U ⊆ f ⁻¹ᵁ V`, the
complex `RΓ(U, E)`, read over `Γ(S, V)`, has Tor amplitude in `[a, b]` exactly when `E_y` has Tor
amplitude in `[a, b]` over `𝒪_{S, f y}` for every `y ∈ U`. -/
theorem forall_hasTorAmplitudeAtPoint_iff_derivedSections (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)
    (a b : ℤ) :
    (∀ y : X, y ∈ U → HasTorAmplitudeAtPoint f E y a b) ↔
      HasTorAmplitudeCanonical Γ(S, V)
        ((ModuleCat.restrictScalars (f.appLE V U e).hom).mapDerivedCategory.obj
          ((derivedSectionsUnbounded X U).obj E)) a b := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  obtain ⟨Kd, ⟨e₁⟩, ⟨e₂⟩⟩ := affineDerivedSectionsPresentation E hE U hU
  let E' := (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E
  let M := DerivedCategory.Q.objPreimage ((derivedSectionsUnbounded X U).obj E)
  have eM : DerivedCategory.Q.obj M ≅ (derivedSectionsUnbounded X U).obj E :=
    DerivedCategory.Q.objObjPreimageIso _
  let eT : (derivedPullback hU.isoSpec.inv.toLRSHom.toShHom).obj E' ≅
      DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex M) :=
    Scheme.Modules.derivedPullbackObjIsoRestrictFunctor hU.isoSpec.inv E' ≪≫
      (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapDerivedCategory.mapIso e₁ ≪≫
      restrictFunctorPushforwardObjIso hU.isoSpec.inv _ ≪≫
      (tilde.functor Γ(X, U)).mapDerivedCategory.mapIso (e₂ ≪≫ eM.symm) ≪≫
      (tilde.functor Γ(X, U)).mapDerivedCategoryFactors.app M
  have h1 : (∀ y : X, y ∈ U → HasTorAmplitudeAtPoint f E y a b) ↔
      ∀ y : U.toScheme, HasTorAmplitudeAtPoint (U.ι ≫ f) E' y a b :=
    ⟨fun h y => (hasTorAmplitudeAtPoint_restrictFunctor_iff f U.ι E y a b).2 (h _ y.2),
      fun h y hy => (hasTorAmplitudeAtPoint_restrictFunctor_iff f U.ι E ⟨y, hy⟩ a b).1
        (h ⟨y, hy⟩)⟩
  refine h1.trans ((hasTorAmplitudeOver_iff_forall_hasTorAmplitudeAtPoint _ E' a b).symm.trans ?_)
  rw [← Scheme.Hom.resLE_comp_ι f e, hasTorAmplitudeOver_comp_iff_of_isOpenImmersion,
    ← hasTorAmplitudeOver_resLE_iff f hV hU e E' a b]
  refine Iff.trans (iff_of_iso_of_imp (fun e => hasTorAmplitudeOver_of_iso e a b) eT) ?_
  refine (AffineRelativeTorAmplitude.hasTorAmplitudeOver_tildeComplex_iff
      Γ(S, V) Γ(X, U) M a b).trans
    (iff_of_iso_of_imp
      (fun e => AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e a b)
      (((ModuleCat.restrictScalars (f.appLE V U e).hom).mapDerivedCategoryFactors.app M).symm ≪≫
        (ModuleCat.restrictScalars (f.appLE V U e).hom).mapDerivedCategory.mapIso eM))

/-- **The Tor clause of Stacks 0DI2.** Let `f : X ⟶ S` be a morphism of schemes and `E` an object
of `D(𝒪_X)` with quasi-coherent cohomology sheaves. The following are equivalent:
1. `E`, read in `D(f^{-1}𝒪_S)`, locally has finite Tor dimension, for a family of certificates
   pinned to the genuine tensor product;
2. for every affine open `V ⊆ S` and every affine open `U ⊆ f ⁻¹ᵁ V`, the complex `RΓ(U, E)` has
   finite Tor dimension over `Γ(S, V)`;
3. there are an affine open covering of `S` and, over each of its members `V i`, an affine open
   covering of `f ⁻¹ᵁ V i` such that `RΓ(U, E)` has finite Tor dimension over `Γ(S, V i)` for each
   member `U` of the latter. -/
theorem torDimension_derivedSections_tfae
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f D) (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) :
    List.TFAE
      [RingedSpace.LocallyHasFiniteTorDimension
          (RingedSpace.inverseImage S.toRingedSpace f.base) D ((derivedScalarRestriction f).obj E),
        ∀ (U : X.Opens), IsAffineOpen U → ∀ (V : S.Opens), IsAffineOpen V →
          ∀ e : U ≤ f ⁻¹ᵁ V, HasFiniteTorDimensionCanonical Γ(S, V)
            ((ModuleCat.restrictScalars (f.appLE V U e).hom).mapDerivedCategory.obj
              ((derivedSectionsUnbounded X U).obj E)),
        ∃ (ι : Type u) (V : ι → S.affineOpens),
          (⨆ i, (V i : S.Opens)) = ⊤ ∧
            ∀ i, ∃ (κ : Type u) (U : κ → X.affineOpens),
              (⨆ j, (U j : X.Opens)) = f ⁻¹ᵁ (V i).1 ∧
                ∀ j, ∃ e : (U j : X.Opens) ≤ f ⁻¹ᵁ (V i).1, HasFiniteTorDimensionCanonical Γ(S, V i)
                  ((ModuleCat.restrictScalars (f.appLE (V i) (U j) e).hom).mapDerivedCategory.obj
                    ((derivedSectionsUnbounded X (U j)).obj E))] := by
  tfae_have 1 → 2 := by
    intro h U hU V hV e
    obtain ⟨a, b, hab⟩ := exists_stalkTorAmplitude_of_locallyHasFiniteTorDimension_of_isCompact
      f D hD E h U hU.isCompact
    exact (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical _ _).2
      ⟨a, b, (forall_hasTorAmplitudeAtPoint_iff_derivedSections f E hE hU hV e a b).1
        fun y hy =>
          (hasTorAmplitudeCanonical_stalk_derivedScalarRestriction_iff_hasTorAmplitudeAtPoint
            f y E a b).1 (hab y hy)⟩
  tfae_have 2 → 3 := by
    intro h
    refine ⟨S.affineOpens, id, iSup_affineOpens_eq_top S, fun V => ?_⟩
    exact ⟨{U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ (V : S.Opens)}, fun U => U.1,
      iSup_affineOpens_subtype_eq _, fun U => ⟨U.2, h _ U.1.2 _ V.2 U.2⟩⟩
  tfae_have 3 → 1 := by
    rintro ⟨ι, V, hVtop, hcov⟩
    choose κ U hU hfin using hcov
    refine (locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover f D hD E).2
      ⟨Σ i, κ i, fun p => ((U p.1 p.2 : X.Opens) : TopologicalSpace.Opens X), ?_, fun p => ?_⟩
    · refine le_antisymm le_top fun x _ => ?_
      have hx : f.base x ∈ (⨆ i, (V i : S.Opens)) := by rw [hVtop]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      have hx' : x ∈ (⨆ j, (U i j : X.Opens)) := by rw [hU i]; exact hi
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, j⟩, hj⟩
    · obtain ⟨e, hp⟩ := hfin p.1 p.2
      obtain ⟨a, b, hab⟩ :=
        (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical _ _).1 hp
      exact ⟨a, b, fun y hy =>
        (hasTorAmplitudeCanonical_stalk_derivedScalarRestriction_iff_hasTorAmplitudeAtPoint
          f y E a b).2 ((forall_hasTorAmplitudeAtPoint_iff_derivedSections f E hE (U p.1 p.2).2
          (V p.1).2 e a b).2 hab y hy)⟩
  tfae_finish

end AlgebraicGeometry.Scheme.Hom

end
