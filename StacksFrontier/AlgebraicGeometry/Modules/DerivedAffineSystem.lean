module

public import StacksFrontier.LinearAlgebra.ExteriorPower.SemilinearDerivedLongExact
public import StacksFrontier.AlgebraicGeometry.Blowup.AffineOpenRestriction
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Sections
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.RingTheory.Length.LocalizationModelIndependence
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic

/-!
# Semilinear derived functors of a quasi-coherent arrow

Let `Y` be a scheme and `f : F' ⟶ F` a morphism of quasi-coherent `𝒪_Y`-modules. Over an affine
open `U` its sections form an arrow `X_U = (Γ(F', U) → Γ(F, U))` of `Γ(Y, U)`-modules, and for
affine opens `V ≤ U` restriction is a morphism `X_U ⟶ ρ^* X_V` of arrows into the restriction of
scalars along `ρ : Γ(Y, U) → Γ(Y, V)`, whose adjoint `Γ(Y, V) ⊗ X_U → X_V` is an isomorphism
because `F'` and `F` are quasi-coherent.

Let `Φ` be a semilinear functor on arrows of modules which commutes with flat base change on
projective arrows. The restriction maps `ρ` are flat, so the derived semilinear maps
`Lⱼ Φ(X_U) → Lⱼ Φ(X_V)` are defined, functorial, and exhibit `Lⱼ Φ(X_V)` as the base change of
`Lⱼ Φ(X_U)`: the modules `Lⱼ Φ(X_U)` form an affine-local quasi-coherent system, and glue to a
quasi-coherent `𝒪_Y`-module `Lⱼ Φ(f)` whose sections over every affine open `U` are
`Lⱼ Φ(X_U)`.

This construction is functorial in `Φ` and in commutative squares of quasi-coherent arrows, and
a short exact sequence `0 → Φ₁ → Φ₂ → Φ₃ → 0` of semilinear functors gives a long exact sequence
`⋯ → Lⱼ₊₁ Φ₃(f) → Lⱼ Φ₁(f) → Lⱼ Φ₂(f) → Lⱼ Φ₃(f) → ⋯ → L₀ Φ₃(f) → 0` of quasi-coherent modules,
since exactness of a sequence of glued modules is tested on affine opens. On a locally
Noetherian scheme `Lⱼ Φ(f)` is coherent as soon as `F'` and `F` are of finite type and `Φ`
preserves finiteness over Noetherian rings. The stalk of `Lⱼ Φ(f)` at a point `y` of an affine
open `U` with prime `𝔭 ⊆ Γ(Y, U)` has the length of the derived module of `Φ` at the localized
arrow `X_U ⊗ Γ(Y, U)_𝔭`, by flat base change along `Γ(Y, U) → Γ(Y, U)_𝔭`; in particular, if `Φ`
vanishes on arrows with zero terms, `Lⱼ Φ(f)` is supported in `supp F' ∪ supp F`.

## Main definitions

* `Stacks.Modules.arrowSections`, `Stacks.Modules.arrowSectionsRes`: the arrow of sections of a
  morphism of `𝒪_Y`-modules over an affine open, and its restriction maps.
* `Stacks.SemilinearArrowFunctor.derivedAffineSystem`: the affine-local system `U ↦ Lⱼ Φ(X_U)`.
* `Stacks.SemilinearArrowFunctor.derivedSheaf`: the quasi-coherent module `Lⱼ Φ(f)`, with the
  identifications `Stacks.SemilinearArrowFunctor.derivedSheafSectionsEquiv` of its sections over
  affine opens.
* `Stacks.SemilinearArrowFunctor.derivedSheafMap`,
  `Stacks.SemilinearArrowFunctor.derivedSheafMapOfSquare` and
  `Stacks.SemilinearArrowFunctor.derivedSheafδ`: the morphisms induced by a morphism of
  semilinear functors, by a commutative square of quasi-coherent arrows, and the connecting
  morphisms of a short exact sequence of semilinear functors.

## Main results

* `Stacks.Modules.AffineSystem.isIso_sheafMap_of_bijective`: a morphism of affine-local systems
  which is bijective on every affine open induces an isomorphism of glued modules.
* `Stacks.SemilinearArrowFunctor.isIso_derivedSheafMap`,
  `Stacks.SemilinearArrowFunctor.isIso_derivedSheafMapOfSquare`: the induced morphisms are
  isomorphisms as soon as they are on every affine open.
* `Stacks.SemilinearArrowFunctor.exact_derivedSheafMap`,
  `Stacks.SemilinearArrowFunctor.exact_derivedSheafMap_derivedSheafδ`,
  `Stacks.SemilinearArrowFunctor.exact_derivedSheafδ_derivedSheafMap` and
  `Stacks.SemilinearArrowFunctor.epi_derivedSheafMap_zero`: the long exact sequence.
* `Stacks.SemilinearArrowFunctor.isCoherent_derivedSheaf`: coherence.
* `Stacks.ModuleStalkSpecialization.sheafMultiplicity_eq_length_localizedModule`: the length of
  the stalk of a quasi-coherent module at a point of an affine open `U` is the length of the
  localization of its sections over `U`.
* `Stacks.SemilinearArrowFunctor.sheafMultiplicity_derivedSheaf` and
  `Stacks.SemilinearArrowFunctor.sheafMultiplicity_derivedSheaf_eq_length_extendScalarsArrow`:
  the length of the stalk of `Lⱼ Φ(f)` is the length of the derived module of `Φ` at the
  localized arrow, computed with any simplicial projective resolution.
* `Stacks.SemilinearArrowFunctor.supp_derivedSheaf_subset`: the support of `Lⱼ Φ(f)`.

## Implementation notes

A simplicial projective resolution of `X_U` is chosen once for every affine open `U`, by
`Stacks.Modules.arrowSectionsResolution`; it depends on `f` and `U` only, so that the morphisms
induced by a morphism of semilinear functors and the connecting morphisms are computed with the
same resolutions on both sides. Independence of the choice is
`Stacks.SimplicialProjectiveResolution.derivedIso` and the compatibility of the derived
semilinear maps with it.

The restriction map `Γ(Y, U) → Γ(Y, V)` along the identity of an affine open is the identity only
up to `Functor.map_id`, and that of a composite inclusion is the composite only up to
`Functor.map_comp`; the identity and transitivity of the derived semilinear maps are applied
through `Stacks.SemilinearArrowFunctor.derivedSemilinearMap_apply_of_eq_id` and the form of
`Stacks.SemilinearArrowFunctor.derivedSemilinearMap_comp_apply` taking a ring map equal to the
composite.

Lengths of stalks and of localizations are compared through
`Module.length_eq_of_isLocalization_of_isLocalizedModule`: the stalk at `y` is a localization of
the sections over `U` (`Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ`), and a base
change along `Γ(Y, U) → Γ(Y, U)_𝔭` is a localization of modules
(`isLocalizedModule_iff_isBaseChange`).

## References

* A. Dold, D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961), 201–312.
* L. Illusie, *Complexe cotangent et déformations I*, Lecture Notes in Math. 239 (1971),
  chapitre I, §4.
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9), for the base change
  property of the sections of a quasi-coherent module over nested affine opens.
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX), for the length of a
  stalk.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Modules

/-! ### Base changes of modules -/

/-- **A base change has invertible linearization**: the converse of
`Stacks.Modules.isBaseChangeAlong_of_isIso`. If a `φ`-semilinear map `g : M →ₛₗ[φ] N` exhibits `N`
as the base change of `M`, the adjoint `S ⊗_R M ⟶ N` of `g` is an isomorphism. -/
theorem isIso_homEquiv_symm_of_isBaseChangeAlong {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {M : ModuleCat.{u} R} {N : ModuleCat.{u} S} (g : M →ₛₗ[φ] N)
    (hg : IsBaseChangeAlong φ g) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv M N).symm
      (ModuleCat.semilinearMapAddEquiv φ M N g)) := by
  unfold IsBaseChangeAlong at hg
  let := φ.toAlgebra
  let := Module.compHom N φ
  let : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let v := ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv M N).symm
    (ModuleCat.semilinearMapAddEquiv φ M N g)
  let e : (ModuleCat.extendScalars φ).obj M ≃ₗ[S] N := hg.equiv
  have hv : v = e.toModuleIso.hom := by
    refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
    have h₁ := ModuleCat.extendRestrictScalarsAdj_homEquiv_apply v m
    rw [Equiv.apply_symm_apply] at h₁
    exact h₁.symm.trans ((hg.equiv_tmul (1 : S) m).trans (one_smul _ _)).symm
  change IsIso v
  rw [hv]
  infer_instance

/-- **The length of a base change to a localization.** Let `T` be a localization of `A` at `S`
and `g : M →ₛₗ[A → T] N` exhibit the `T`-module `N` as the base change of the `A`-module `M`.
Then `N` has the length over `T` of the localization `S⁻¹M` over `S⁻¹A`. -/
theorem length_localizedModule_eq_of_isBaseChangeAlong {A : Type*} [CommRing A]
    (S : Submonoid A) {T : Type*} [CommRing T] [Algebra A T] [IsLocalization S T]
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module T N]
    (g : M →ₛₗ[algebraMap A T] N) (hg : IsBaseChangeAlong (algebraMap A T) g) :
    Module.length (Localization S) (LocalizedModule S M) = Module.length T N := by
  let := Module.compHom N (algebraMap A T)
  have : IsScalarTower A T N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsLocalizedModule S (semilinearToLinear (algebraMap A T) g) := by
    unfold IsBaseChangeAlong at hg
    have hT : @IsLocalization A _ S T _ (algebraMap A T).toAlgebra :=
      (@isLocalization_iff_isLocalizationMap A _ S T _ (algebraMap A T).toAlgebra).2
        ((isLocalization_iff_isLocalizationMap S T).1 ‹IsLocalization S T›)
    let alg : Algebra A T := (algebraMap A T).toAlgebra
    have : IsScalarTower A T N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    exact (isLocalizedModule_iff_isBaseChange S T _).2 hg
  exact Module.length_eq_of_isLocalization_of_isLocalizedModule S T
    (semilinearToLinear (algebraMap A T) g)

/-! ### Isomorphisms of affine-local systems -/

namespace AffineSystem

variable {Y : Scheme.{u}} {T T' : AffineSystem Y}

/-- The inverse of a morphism of affine-local systems which is bijective on every affine open. -/
def invOfBijective (g : T ⟶ T') (hg : ∀ U, Function.Bijective (g.app U)) : T' ⟶ T where
  app U := (LinearEquiv.ofBijective (g.app U) (hg U)).symm.toLinearMap
  naturality {U V} h x := (hg V).1 (by
    change g.app V ((LinearEquiv.ofBijective (g.app V) (hg V)).symm (T'.map h x)) =
      g.app V (T.map h ((LinearEquiv.ofBijective (g.app U) (hg U)).symm x))
    refine ((LinearEquiv.ofBijective (g.app V) (hg V)).apply_symm_apply (T'.map h x)).trans ?_
    rw [g.naturality]
    exact congrArg (T'.map h) ((LinearEquiv.ofBijective (g.app U) (hg U)).apply_symm_apply x).symm)

/-- A morphism of affine-local systems which is bijective on every affine open is an
isomorphism. -/
theorem isIso_of_bijective (g : T ⟶ T') (hg : ∀ U, Function.Bijective (g.app U)) : IsIso g :=
  ⟨invOfBijective g hg,
    hom_ext fun U => LinearMap.ext fun x =>
      (LinearEquiv.ofBijective (g.app U) (hg U)).symm_apply_apply x,
    hom_ext fun U => LinearMap.ext fun x =>
      (LinearEquiv.ofBijective (g.app U) (hg U)).apply_symm_apply x⟩

/-- **Isomorphisms are detected on affine opens**: a morphism of affine-local systems which is
bijective on every affine open induces an isomorphism of the glued quasi-coherent modules. -/
theorem isIso_sheafMap_of_bijective (g : T ⟶ T') (hg : ∀ U, Function.Bijective (g.app U)) :
    IsIso (sheafMap g) := by
  have := isIso_of_bijective g hg
  exact (sheafFunctor Y).map_isIso g

end AffineSystem

/-! ### The arrow of sections of a morphism of quasi-coherent modules -/

variable {Y : Scheme.{u}} {F' F : Y.Modules} (f : F' ⟶ F)

/-- The arrow `Γ(F', U) ⟶ Γ(F, U)` of `Γ(Y, U)`-modules given by a morphism `f : F' ⟶ F` of
`𝒪_Y`-modules over an affine open `U`. -/
abbrev arrowSections (U : Y.affineOpens) : ComposableArrows (ModuleCat.{u} Γ(Y, U)) 1 :=
  ComposableArrows.mk₁ (ModuleCat.ofHom (Stacks.AlgebraicGeometry.QcohLimits.appₗ f U) :
    ModuleCat.of Γ(Y, U) Γ(F', U) ⟶ ModuleCat.of Γ(Y, U) Γ(F, U))

variable (Y) in
/-- The simplicial projective resolution of the arrow of sections over an affine open with which
the derived modules over that open are computed, chosen once and for all. -/
def arrowSectionsResolution (U : Y.affineOpens) :
    SimplicialProjectiveResolution (arrowSections f U) :=
  Classical.arbitrary _

variable {f} in
/-- The morphism of arrows of sections over an affine open induced by a commutative square
`f ≫ b = a ≫ g` of `𝒪_Y`-modules. -/
def arrowSectionsMap {G' G : Y.Modules} {g : G' ⟶ G} (a : F' ⟶ G') (b : F ⟶ G)
    (w : f ≫ b = a ≫ g) (U : Y.affineOpens) : arrowSections f U ⟶ arrowSections g U :=
  ComposableArrows.homMk₁ (ModuleCat.ofHom (Stacks.AlgebraicGeometry.QcohLimits.appₗ a U))
    (ModuleCat.ofHom (Stacks.AlgebraicGeometry.QcohLimits.appₗ b U)) (by
      ext (x : Γ(F', (U : Y.Opens)))
      exact congrArg (fun t => (Scheme.Modules.Hom.app t U).hom x) w)

variable {f} in
/-- If the square consists of isomorphisms, so does the morphism of arrows of sections. -/
instance isIso_arrowSectionsMap {G' G : Y.Modules} {g : G' ⟶ G} (a : F' ⟶ G') (b : F ⟶ G)
    (w : f ≫ b = a ≫ g) [IsIso a] [IsIso b] (U : Y.affineOpens) :
    IsIso (arrowSectionsMap a b w U) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun i => ?_
  fin_cases i
  · exact ⟨ModuleCat.ofHom (Stacks.AlgebraicGeometry.QcohLimits.appₗ (inv a) U),
      by ext (x : Γ(F', (U : Y.Opens)))
         exact congrArg (fun t => (Scheme.Modules.Hom.app t U).hom x) (IsIso.hom_inv_id a),
      by ext (x : Γ(G', (U : Y.Opens)))
         exact congrArg (fun t => (Scheme.Modules.Hom.app t U).hom x) (IsIso.inv_hom_id a)⟩
  · exact ⟨ModuleCat.ofHom (Stacks.AlgebraicGeometry.QcohLimits.appₗ (inv b) U),
      by ext (x : Γ(F, (U : Y.Opens)))
         exact congrArg (fun t => (Scheme.Modules.Hom.app t U).hom x) (IsIso.hom_inv_id b),
      by ext (x : Γ(G, (U : Y.Opens)))
         exact congrArg (fun t => (Scheme.Modules.Hom.app t U).hom x) (IsIso.inv_hom_id b)⟩

variable [F'.IsQuasicoherent] [F.IsQuasicoherent]

/-- **Restriction of the arrow of sections.** For affine opens `V ≤ U`, the restriction maps of
`F'` and `F`, as a morphism `X_U ⟶ ρ^* X_V` into the restriction of scalars along
`ρ : Γ(Y, U) → Γ(Y, V)`. -/
def arrowSectionsRes {U V : Y.affineOpens} (h : (V : Y.Opens) ≤ U) :
    arrowSections f U ⟶ (restrictScalarsArrow (Y.presheaf.map (homOfLE h).op).hom).obj
      (arrowSections f V) :=
  ComposableArrows.homMk₁
    (ModuleCat.semilinearMapAddEquiv _ _ _ ((AffineSystem.ofQuasicoherent F').map h))
    (ModuleCat.semilinearMapAddEquiv _ _ _ ((AffineSystem.ofQuasicoherent F).map h)) (by
      ext x
      exact (Stacks.AlgebraicGeometry.QcohLimits.app_naturality f h x).symm)

/-- **Quasi-coherence of the arrow of sections**: the adjoint `Γ(Y, V) ⊗ X_U ⟶ X_V` of the
restriction is an isomorphism (Stacks 01I9). -/
theorem isIso_homEquiv_symm_arrowSectionsRes {U V : Y.affineOpens} (h : (V : Y.Opens) ≤ U) :
    IsIso (((extendRestrictScalarsArrowAdj (Y.presheaf.map (homOfLE h).op).hom).homEquiv _ _).symm
      (arrowSectionsRes f h)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun i => ?_
  rw [extendRestrictScalarsArrowAdj, Adjunction.whiskerRight_homEquiv_symm_app]
  fin_cases i
  · exact isIso_homEquiv_symm_of_isBaseChangeAlong _ _
      ((AffineSystem.ofQuasicoherent F').isBaseChange h)
  · exact isIso_homEquiv_symm_of_isBaseChangeAlong _ _
      ((AffineSystem.ofQuasicoherent F).isBaseChange h)

/-- Restriction of the arrow of sections to the same affine open is the identity, under the
identification of the restriction of scalars along `Γ(Y, U) → Γ(Y, U)` with the identity. -/
lemma arrowSectionsRes_refl (U : Y.affineOpens) :
    arrowSectionsRes f (le_refl (U : Y.Opens)) ≫
      (restrictScalarsArrowId' (Y.presheaf.map (homOfLE (le_refl (U : Y.Opens))).op).hom
        (by rw [show (homOfLE (le_refl (U : Y.Opens))).op = 𝟙 _ from rfl, Y.presheaf.map_id];
            rfl)).hom.app _ = 𝟙 _ := by
  ext x
  · exact (AffineSystem.ofQuasicoherent F').map_id U x
  · exact (AffineSystem.ofQuasicoherent F).map_id U x

/-- Restriction of the arrow of sections is transitive, under the identification of the
restriction of scalars along a composite with the composite of the restrictions. -/
lemma arrowSectionsRes_trans {U V W : Y.affineOpens} (h₁ : (V : Y.Opens) ≤ U)
    (h₂ : (W : Y.Opens) ≤ V) :
    arrowSectionsRes f (h₂.trans h₁) = arrowSectionsRes f h₁ ≫
      (restrictScalarsArrow (Y.presheaf.map (homOfLE h₁).op).hom).map (arrowSectionsRes f h₂) ≫
      (restrictScalarsArrowComp' (Y.presheaf.map (homOfLE h₁).op).hom
        (Y.presheaf.map (homOfLE h₂).op).hom (Y.presheaf.map (homOfLE (h₂.trans h₁)).op).hom
        (by rw [← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)).inv.app _ := by
  ext x
  · exact ((AffineSystem.ofQuasicoherent F').map_comp h₁ h₂ x).symm
  · exact ((AffineSystem.ofQuasicoherent F).map_comp h₁ h₂ x).symm

variable {f} in
/-- The morphisms of arrows of sections induced by a commutative square commute with
restriction. -/
lemma arrowSectionsMap_comp_arrowSectionsRes {G' G : Y.Modules} [G'.IsQuasicoherent]
    [G.IsQuasicoherent] {g : G' ⟶ G} (a : F' ⟶ G') (b : F ⟶ G) (w : f ≫ b = a ≫ g)
    {U V : Y.affineOpens} (h : (V : Y.Opens) ≤ U) :
    arrowSectionsMap a b w U ≫ arrowSectionsRes g h =
      arrowSectionsRes f h ≫
        (restrictScalarsArrow (Y.presheaf.map (homOfLE h).op).hom).map
          (arrowSectionsMap a b w V) := by
  ext x
  · exact (Stacks.AlgebraicGeometry.QcohLimits.app_naturality a h x).symm
  · exact (Stacks.AlgebraicGeometry.QcohLimits.app_naturality b h x).symm

end Stacks.Modules

/-! ### Stalks of quasi-coherent modules and localizations -/

namespace Stacks.ModuleStalkSpecialization

variable {X : Scheme.{u}}

/-- **The length of a stalk is the length of a localization.** For a quasi-coherent module `F`
and a point `x` of an affine open `U` with prime `𝔭 ⊆ Γ(X, U)`, the length of `F_x` over `𝒪_{X,x}`
is the length of `Γ(F, U)_𝔭` over `Γ(X, U)_𝔭`. -/
theorem length_stalk_eq_length_localizedModule (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    Module.length (X.presheaf.stalk x) (F.presheaf.stalk x) =
      Module.length (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
        (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U)) := by
  let := (X.presheaf.germ U x hx).hom.toAlgebra
  let := stalkModule F x
  let := sectionsStalkModule F hx
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  have := isScalarTower_sectionsStalk F hx
  have := isLocalizedModule_germₗ F hU hx
  exact (Module.length_eq_of_isLocalization_of_isLocalizedModule _ _ (germₗ F hx)).symm

/-- **The multiplicity of a quasi-coherent module at a point of an affine open** `U` with prime
`𝔭` is the length of `Γ(F, U)_𝔭` over `Γ(X, U)_𝔭`. -/
theorem sheafMultiplicity_eq_length_localizedModule (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    Chow.sheafMultiplicity F x =
      (Module.length (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
        (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U))).toNat := by
  rw [Chow.sheafMultiplicity, length_stalk_eq_length_localizedModule F hU hx]

end Stacks.ModuleStalkSpecialization

/-! ### The degree zero end of a long exact sequence of derived objects -/

namespace Stacks.ShortExactOnProjectives

open SimplicialProjectiveResolution

variable {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
  {F₁ F₂ F₃ : C ⥤ D} {α : F₁ ⟶ F₂} {β : F₂ ⟶ F₃}

/-- **The long exact sequence ends with an epimorphism** `L₀F₂(X) ⟶ L₀F₃(X)`: in degree zero the
map of complexes `s(F₂(P)) ⟶ s(F₃(P))` is an epimorphism and no differential leaves degree
zero. -/
theorem epi_derivedHomologyMap_zero (h : ShortExactOnProjectives α β) {X : C}
    (P : SimplicialProjectiveResolution X) : Epi (derivedHomologyMap β P 0) := by
  have : Epi (((AlgebraicTopology.alternatingFaceMapComplex D).map
      (Functor.whiskerLeft P.obj β)).f 0) := by
    rw [AlgebraicTopology.alternatingFaceMapComplex_map_f]
    exact (h.shortExact _ (P.projective 0)).epi_g
  exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ 0 fun j hj => by simp at hj

end Stacks.ShortExactOnProjectives

/-! ### The glued derived modules -/

namespace Stacks.SemilinearArrowFunctor

open Modules Modules.AffineSystem SimplicialProjectiveResolution

variable (Φ : SemilinearArrowFunctor.{u})

/-- **The derived semilinear map along a ring map equal to the identity** is the derived map of
the corresponding morphism of arrows. -/
theorem derivedSemilinearMap_apply_of_eq_id {A : CommRingCat.{u}} (φ : A ⟶ A) (hφ : φ = 𝟙 A)
    (hφf : φ.hom.Flat) {X Y : ComposableArrows (ModuleCat.{u} A) 1}
    (f : X ⟶ (restrictScalarsArrow φ.hom).obj Y) (P : SimplicialProjectiveResolution X)
    (Q : SimplicialProjectiveResolution Y) (j : ℕ)
    (x : P.derivedHomology (D := ModuleCat.{u} A) (Φ.obj A) j) :
    Φ.derivedSemilinearMap φ hφf f P Q j x =
      (SimplicialProjectiveResolution.derivedMap (Φ.obj A)
        (f ≫ (restrictScalarsArrowId' φ.hom (by rw [hφ]; rfl)).hom.app Y) P Q j).hom x := by
  subst hφ
  exact Φ.derivedSemilinearMap_id_apply f P Q j x

variable {Y : Scheme.{u}} {F' F : Y.Modules} [F'.IsQuasicoherent] [F.IsQuasicoherent]
  (f : F' ⟶ F)

/-- **The affine-local system of derived modules** of a semilinear functor `Φ` commuting with flat
base change at a morphism `f : F' ⟶ F` of quasi-coherent modules: over an affine open `U` the
`j`-th derived module `Lⱼ Φ(X_U)` of the arrow of sections, with the derived semilinear maps of
the restrictions. -/
def derivedAffineSystem (hΦ : Φ.HasFlatBaseChange) (j : ℕ) : AffineSystem Y where
  obj U := (arrowSectionsResolution Y f U).derivedHomology (Φ.obj Γ(Y, U)) j
  map {U V} h := Φ.derivedSemilinearMap (Y.presheaf.map (homOfLE h).op)
    (Scheme.flat_presheaf_map_of_isAffineOpen V.2 U.2 h) (arrowSectionsRes f h) _ _ j
  map_id U x := by
    rw [Φ.derivedSemilinearMap_apply_of_eq_id _
      (by rw [show (homOfLE (le_refl (U : Y.Opens))).op = 𝟙 _ from rfl, Y.presheaf.map_id]),
      arrowSectionsRes_refl, SimplicialProjectiveResolution.derivedMap_id]
    rfl
  map_comp {U V W} h₁ h₂ x := by
    rw [arrowSectionsRes_trans f h₁ h₂]
    exact (Φ.derivedSemilinearMap_comp_apply _ _ _ _
      (by rw [← Functor.map_comp]; rfl) _ _ _ _ _ _ _ _ x).symm
  isBaseChange h := isBaseChangeAlong_derivedSemilinearMap _ _ hΦ _
    (isIso_homEquiv_symm_arrowSectionsRes f h) _ _ j

/-- The modules of the derived system are the derived modules of the arrows of sections. -/
@[simp]
lemma derivedAffineSystem_obj (hΦ : Φ.HasFlatBaseChange) (j : ℕ) (U : Y.affineOpens) :
    (Φ.derivedAffineSystem f hΦ j).obj U =
      (arrowSectionsResolution Y f U).derivedHomology (Φ.obj Γ(Y, U)) j :=
  rfl

/-- The restriction maps of the derived system are the derived semilinear maps. -/
lemma derivedAffineSystem_map (hΦ : Φ.HasFlatBaseChange) (j : ℕ) {U V : Y.affineOpens}
    (h : (V : Y.Opens) ≤ U) :
    (Φ.derivedAffineSystem f hΦ j).map h = Φ.derivedSemilinearMap (Y.presheaf.map (homOfLE h).op)
      (Scheme.flat_presheaf_map_of_isAffineOpen V.2 U.2 h) (arrowSectionsRes f h) _ _ j :=
  rfl

/-- **The `j`-th derived module `Lⱼ Φ(f)`** of a semilinear functor `Φ` commuting with flat base
change at a morphism `f : F' ⟶ F` of quasi-coherent modules: the quasi-coherent module glued from
the derived modules `Lⱼ Φ(X_U)` of the arrows of sections over the affine opens `U`. -/
def derivedSheaf (hΦ : Φ.HasFlatBaseChange) (j : ℕ) : Y.Modules :=
  (Φ.derivedAffineSystem f hΦ j).sheaf

/-- `Lⱼ Φ(f)` is quasi-coherent. -/
instance isQuasicoherent_derivedSheaf (hΦ : Φ.HasFlatBaseChange) (j : ℕ) :
    (Φ.derivedSheaf f hΦ j).IsQuasicoherent :=
  isQuasicoherent_sheaf _

/-- **The sections of `Lⱼ Φ(f)` over an affine open `U` are `Lⱼ Φ(X_U)`**, `Γ(Y, U)`-linearly,
compatibly with restriction (`Stacks.Modules.AffineSystem.sectionsEquiv_res`). -/
def derivedSheafSectionsEquiv (hΦ : Φ.HasFlatBaseChange) (j : ℕ) (U : Y.affineOpens) :
    Γ(Φ.derivedSheaf f hΦ j, U) ≃ₗ[Γ(Y, U)]
      (arrowSectionsResolution Y f U).derivedHomology (D := ModuleCat.{u} Γ(Y, U))
        (Φ.obj Γ(Y, U)) j :=
  (Φ.derivedAffineSystem f hΦ j).sectionsEquiv U

/-! ### Morphisms of semilinear functors -/

variable {Φ} {Ψ : SemilinearArrowFunctor.{u}}

/-- The morphism of derived systems induced by a morphism `α : Φ ⟶ Ψ` of semilinear functors:
over an affine open `U` the derived map `Lⱼ Φ(X_U) ⟶ Lⱼ Ψ(X_U)` of `α`. -/
def derivedAffineSystemMap (α : Φ ⟶ Ψ) (hΦ : Φ.HasFlatBaseChange) (hΨ : Ψ.HasFlatBaseChange)
    (j : ℕ) : Φ.derivedAffineSystem f hΦ j ⟶ Ψ.derivedAffineSystem f hΨ j where
  app U := (derivedHomologyMap (α.app Γ(Y, U)) (arrowSectionsResolution Y f U) j).hom
  naturality {U V} h x := (congrArg (fun t => t.hom x)
    (Φ.derivedHomologyMap_comp_derivedMap (Y.presheaf.map (homOfLE h).op)
      (Scheme.flat_presheaf_map_of_isAffineOpen V.2 U.2 h) α (arrowSectionsRes f h)
      (arrowSectionsResolution Y f U) (arrowSectionsResolution Y f V) j)).symm

/-- **The morphism `Lⱼ Φ(f) ⟶ Lⱼ Ψ(f)` induced by a morphism `α : Φ ⟶ Ψ` of semilinear
functors.** -/
def derivedSheafMap (α : Φ ⟶ Ψ) (hΦ : Φ.HasFlatBaseChange) (hΨ : Ψ.HasFlatBaseChange)
    (j : ℕ) : Φ.derivedSheaf f hΦ j ⟶ Ψ.derivedSheaf f hΨ j :=
  sheafMap (derivedAffineSystemMap f α hΦ hΨ j)

/-- On the sections over an affine open `U`, `derivedSheafMap` is the derived map of `α` at the
arrow of sections. -/
@[simp]
theorem derivedSheafSectionsEquiv_derivedSheafMap_app (α : Φ ⟶ Ψ) (hΦ : Φ.HasFlatBaseChange)
    (hΨ : Ψ.HasFlatBaseChange) (j : ℕ) (U : Y.affineOpens) (s : Γ(Φ.derivedSheaf f hΦ j, U)) :
    Ψ.derivedSheafSectionsEquiv f hΨ j U ((derivedSheafMap f α hΦ hΨ j).app U s) =
      (derivedHomologyMap (α.app Γ(Y, U)) (arrowSectionsResolution Y f U) j).hom
        (Φ.derivedSheafSectionsEquiv f hΦ j U s) :=
  sectionsEquiv_sheafMap_app _ U s

/-- `derivedSheafMap α` is an isomorphism as soon as the derived maps of `α` at the arrows of
sections over all affine opens are. -/
theorem isIso_derivedSheafMap (α : Φ ⟶ Ψ) (hΦ : Φ.HasFlatBaseChange) (hΨ : Ψ.HasFlatBaseChange)
    (j : ℕ) (hα : ∀ U : Y.affineOpens,
      IsIso (derivedHomologyMap (α.app Γ(Y, U)) (arrowSectionsResolution Y f U) j)) :
    IsIso (derivedSheafMap f α hΦ hΨ j) :=
  isIso_sheafMap_of_bijective _ fun U => ConcreteCategory.bijective_of_isIso
    (derivedHomologyMap (α.app Γ(Y, U)) (arrowSectionsResolution Y f U) j)

/-! ### Morphisms of quasi-coherent arrows -/

variable (Φ) {f} {G' G : Y.Modules} [G'.IsQuasicoherent] [G.IsQuasicoherent] {g : G' ⟶ G}

/-- The morphism of derived systems induced by a commutative square `f ≫ b = a ≫ g` of
quasi-coherent modules: over an affine open `U` the derived map of the morphism of arrows of
sections. -/
def derivedAffineSystemMapOfSquare (hΦ : Φ.HasFlatBaseChange) (a : F' ⟶ G') (b : F ⟶ G)
    (w : f ≫ b = a ≫ g) (j : ℕ) : Φ.derivedAffineSystem f hΦ j ⟶ Φ.derivedAffineSystem g hΦ j where
  app U := (SimplicialProjectiveResolution.derivedMap (Φ.obj Γ(Y, U)) (arrowSectionsMap a b w U)
    (arrowSectionsResolution Y f U) (arrowSectionsResolution Y g U) j).hom
  naturality {U V} h x := by
    have hρ := Scheme.flat_presheaf_map_of_isAffineOpen V.2 U.2 h
    refine (congrArg (fun t => t.hom x) (Φ.derivedMap_comp_map_derivedMap
      (Y.presheaf.map (homOfLE h).op) hρ (arrowSectionsRes f h) (arrowSectionsResolution Y f U)
      (arrowSectionsResolution Y f V) (arrowSectionsMap a b w V)
      (arrowSectionsResolution Y g V) j)).trans
      ((congrArg (fun t => t.hom x) (Φ.derivedMap_comp_derivedMap
        (Y.presheaf.map (homOfLE h).op) hρ (arrowSectionsMap a b w U)
        (arrowSectionsResolution Y f U) (arrowSectionsRes g h) (arrowSectionsResolution Y g U)
        (arrowSectionsResolution Y g V) j)).trans ?_).symm
    rw [arrowSectionsMap_comp_arrowSectionsRes]

/-- **The morphism `Lⱼ Φ(f) ⟶ Lⱼ Φ(g)` induced by a commutative square** `f ≫ b = a ≫ g` of
quasi-coherent modules. -/
def derivedSheafMapOfSquare (hΦ : Φ.HasFlatBaseChange) (a : F' ⟶ G') (b : F ⟶ G)
    (w : f ≫ b = a ≫ g) (j : ℕ) : Φ.derivedSheaf f hΦ j ⟶ Φ.derivedSheaf g hΦ j :=
  sheafMap (Φ.derivedAffineSystemMapOfSquare hΦ a b w j)

/-- On the sections over an affine open `U`, `derivedSheafMapOfSquare` is the derived map of the
morphism of arrows of sections. -/
@[simp]
theorem derivedSheafSectionsEquiv_derivedSheafMapOfSquare_app (hΦ : Φ.HasFlatBaseChange)
    (a : F' ⟶ G') (b : F ⟶ G) (w : f ≫ b = a ≫ g) (j : ℕ) (U : Y.affineOpens)
    (s : Γ(Φ.derivedSheaf f hΦ j, U)) :
    Φ.derivedSheafSectionsEquiv g hΦ j U ((Φ.derivedSheafMapOfSquare hΦ a b w j).app U s) =
      (SimplicialProjectiveResolution.derivedMap (Φ.obj Γ(Y, U)) (arrowSectionsMap a b w U)
        (arrowSectionsResolution Y f U) (arrowSectionsResolution Y g U) j).hom
        (Φ.derivedSheafSectionsEquiv f hΦ j U s) :=
  sectionsEquiv_sheafMap_app _ U s

/-- `derivedSheafMapOfSquare` is an isomorphism as soon as the derived maps of the morphisms of
arrows of sections over all affine opens are. -/
theorem isIso_derivedSheafMapOfSquare (hΦ : Φ.HasFlatBaseChange) (a : F' ⟶ G') (b : F ⟶ G)
    (w : f ≫ b = a ≫ g) (j : ℕ) (hab : ∀ U : Y.affineOpens,
      IsIso (SimplicialProjectiveResolution.derivedMap (Φ.obj Γ(Y, U)) (arrowSectionsMap a b w U)
        (arrowSectionsResolution Y f U) (arrowSectionsResolution Y g U) j)) :
    IsIso (Φ.derivedSheafMapOfSquare hΦ a b w j) :=
  isIso_sheafMap_of_bijective _ fun U => ConcreteCategory.bijective_of_isIso
    (SimplicialProjectiveResolution.derivedMap (Φ.obj Γ(Y, U)) (arrowSectionsMap a b w U)
      (arrowSectionsResolution Y f U) (arrowSectionsResolution Y g U) j)

/-- A square of isomorphisms induces an isomorphism `Lⱼ Φ(f) ≅ Lⱼ Φ(g)`. -/
instance isIso_derivedSheafMapOfSquare_of_isIso (hΦ : Φ.HasFlatBaseChange) (a : F' ⟶ G')
    (b : F ⟶ G) (w : f ≫ b = a ≫ g) [IsIso a] [IsIso b] (j : ℕ) :
    IsIso (Φ.derivedSheafMapOfSquare hΦ a b w j) :=
  Φ.isIso_derivedSheafMapOfSquare hΦ a b w j fun _ => inferInstance

/-! ### Connecting morphisms and the long exact sequence -/

variable {Φ₁ Φ₂ Φ₃ : SemilinearArrowFunctor.{u}} {α : Φ₁ ⟶ Φ₂} {β : Φ₂ ⟶ Φ₃}

variable (f) in
/-- The morphism of derived systems given over every affine open by the connecting morphism
`Lⱼ₊₁ Φ₃(X_U) ⟶ Lⱼ Φ₁(X_U)` of a short exact sequence of semilinear functors. -/
def derivedAffineSystemδ (h : ShortExact α β) (hΦ₁ : Φ₁.HasFlatBaseChange)
    (hΦ₃ : Φ₃.HasFlatBaseChange) (j : ℕ) :
    Φ₃.derivedAffineSystem f hΦ₃ (j + 1) ⟶ Φ₁.derivedAffineSystem f hΦ₁ j where
  app U := ((h.shortExactOnProjectives Γ(Y, U)).derivedδ (arrowSectionsResolution Y f U) j).hom
  naturality {U V} h' x := (h.derivedSemilinearMap_derivedδ (Y.presheaf.map (homOfLE h').op)
    (Scheme.flat_presheaf_map_of_isAffineOpen V.2 U.2 h') (arrowSectionsRes f h')
    (arrowSectionsResolution Y f U) (arrowSectionsResolution Y f V) j x).symm

variable (f) in
/-- **The connecting morphism `δ : Lⱼ₊₁ Φ₃(f) ⟶ Lⱼ Φ₁(f)`** of a short exact sequence
`0 → Φ₁ → Φ₂ → Φ₃ → 0` of semilinear functors. -/
def derivedSheafδ (h : ShortExact α β) (hΦ₁ : Φ₁.HasFlatBaseChange)
    (hΦ₃ : Φ₃.HasFlatBaseChange) (j : ℕ) :
    Φ₃.derivedSheaf f hΦ₃ (j + 1) ⟶ Φ₁.derivedSheaf f hΦ₁ j :=
  sheafMap (derivedAffineSystemδ f h hΦ₁ hΦ₃ j)

variable (f) in
/-- On the sections over an affine open `U`, `derivedSheafδ` is the connecting morphism at the
arrow of sections. -/
@[simp]
theorem derivedSheafSectionsEquiv_derivedSheafδ_app (h : ShortExact α β)
    (hΦ₁ : Φ₁.HasFlatBaseChange) (hΦ₃ : Φ₃.HasFlatBaseChange) (j : ℕ) (U : Y.affineOpens)
    (s : Γ(Φ₃.derivedSheaf f hΦ₃ (j + 1), U)) :
    Φ₁.derivedSheafSectionsEquiv f hΦ₁ j U ((derivedSheafδ f h hΦ₁ hΦ₃ j).app U s) =
      ((h.shortExactOnProjectives Γ(Y, U)).derivedδ (arrowSectionsResolution Y f U) j).hom
        (Φ₃.derivedSheafSectionsEquiv f hΦ₃ (j + 1) U s) :=
  sectionsEquiv_sheafMap_app _ U s

variable (f) in
/-- Two consecutive maps of the long exact sequence compose to zero. -/
@[reassoc (attr := simp)]
theorem derivedSheafMap_comp_derivedSheafMap (h : ShortExact α β) (hΦ₁ : Φ₁.HasFlatBaseChange)
    (hΦ₂ : Φ₂.HasFlatBaseChange) (hΦ₃ : Φ₃.HasFlatBaseChange) (j : ℕ) :
    derivedSheafMap f α hΦ₁ hΦ₂ j ≫ derivedSheafMap f β hΦ₂ hΦ₃ j = 0 :=
  sheafMap_comp_eq_zero _ _ fun U x => congrArg (fun t => t.hom x)
    ((h.shortExactOnProjectives Γ(Y, U)).derivedHomologyMap_comp_derivedHomologyMap
      (arrowSectionsResolution Y f U) j)

variable (f) in
/-- Two consecutive maps of the long exact sequence compose to zero. -/
@[reassoc (attr := simp)]
theorem derivedSheafMap_comp_derivedSheafδ (h : ShortExact α β) (hΦ₁ : Φ₁.HasFlatBaseChange)
    (hΦ₂ : Φ₂.HasFlatBaseChange) (hΦ₃ : Φ₃.HasFlatBaseChange) (j : ℕ) :
    derivedSheafMap f β hΦ₂ hΦ₃ (j + 1) ≫ derivedSheafδ f h hΦ₁ hΦ₃ j = 0 :=
  sheafMap_comp_eq_zero _ _ fun U x => congrArg (fun t => t.hom x)
    ((h.shortExactOnProjectives Γ(Y, U)).derivedHomologyMap_comp_derivedδ
      (arrowSectionsResolution Y f U) j)

variable (f) in
/-- Two consecutive maps of the long exact sequence compose to zero. -/
@[reassoc (attr := simp)]
theorem derivedSheafδ_comp_derivedSheafMap (h : ShortExact α β) (hΦ₁ : Φ₁.HasFlatBaseChange)
    (hΦ₂ : Φ₂.HasFlatBaseChange) (hΦ₃ : Φ₃.HasFlatBaseChange) (j : ℕ) :
    derivedSheafδ f h hΦ₁ hΦ₃ j ≫ derivedSheafMap f α hΦ₁ hΦ₂ j = 0 :=
  sheafMap_comp_eq_zero _ _ fun U x => congrArg (fun t => t.hom x)
    ((h.shortExactOnProjectives Γ(Y, U)).derivedδ_comp_derivedHomologyMap
      (arrowSectionsResolution Y f U) j)

variable (f) in
/-- **Exactness of the long exact sequence** at `Lⱼ Φ₂(f)`:
`Lⱼ Φ₁(f) ⟶ Lⱼ Φ₂(f) ⟶ Lⱼ Φ₃(f)` is exact. -/
theorem exact_derivedSheafMap (h : ShortExact α β) (hΦ₁ : Φ₁.HasFlatBaseChange)
    (hΦ₂ : Φ₂.HasFlatBaseChange) (hΦ₃ : Φ₃.HasFlatBaseChange) (j : ℕ) :
    (ShortComplex.mk _ _ (derivedSheafMap_comp_derivedSheafMap f h hΦ₁ hΦ₂ hΦ₃ j)).Exact :=
  exact_sheafMap _ _ fun U =>
    (h.shortExactOnProjectives Γ(Y, U)).function_exact_derivedHomologyMap
      (arrowSectionsResolution Y f U) j

variable (f) in
/-- **Exactness of the long exact sequence** at `Lⱼ₊₁ Φ₃(f)`:
`Lⱼ₊₁ Φ₂(f) ⟶ Lⱼ₊₁ Φ₃(f) ⟶ Lⱼ Φ₁(f)` is exact. -/
theorem exact_derivedSheafMap_derivedSheafδ (h : ShortExact α β) (hΦ₁ : Φ₁.HasFlatBaseChange)
    (hΦ₂ : Φ₂.HasFlatBaseChange) (hΦ₃ : Φ₃.HasFlatBaseChange) (j : ℕ) :
    (ShortComplex.mk _ _ (derivedSheafMap_comp_derivedSheafδ f h hΦ₁ hΦ₂ hΦ₃ j)).Exact :=
  exact_sheafMap _ _ fun U =>
    (h.shortExactOnProjectives Γ(Y, U)).function_exact_derivedHomologyMap_derivedδ
      (arrowSectionsResolution Y f U) j

variable (f) in
/-- **Exactness of the long exact sequence** at `Lⱼ Φ₁(f)`:
`Lⱼ₊₁ Φ₃(f) ⟶ Lⱼ Φ₁(f) ⟶ Lⱼ Φ₂(f)` is exact. -/
theorem exact_derivedSheafδ_derivedSheafMap (h : ShortExact α β) (hΦ₁ : Φ₁.HasFlatBaseChange)
    (hΦ₂ : Φ₂.HasFlatBaseChange) (hΦ₃ : Φ₃.HasFlatBaseChange) (j : ℕ) :
    (ShortComplex.mk _ _ (derivedSheafδ_comp_derivedSheafMap f h hΦ₁ hΦ₂ hΦ₃ j)).Exact :=
  exact_sheafMap _ _ fun U =>
    (h.shortExactOnProjectives Γ(Y, U)).function_exact_derivedδ_derivedHomologyMap
      (arrowSectionsResolution Y f U) j

variable (f) in
/-- **The long exact sequence ends with an epimorphism** `L₀ Φ₂(f) ⟶ L₀ Φ₃(f)`. -/
theorem epi_derivedSheafMap_zero (h : ShortExact α β) (hΦ₂ : Φ₂.HasFlatBaseChange)
    (hΦ₃ : Φ₃.HasFlatBaseChange) : Epi (derivedSheafMap f β hΦ₂ hΦ₃ 0) :=
  epi_sheafMap _ fun U => (ModuleCat.epi_iff_surjective _).1
    ((h.shortExactOnProjectives Γ(Y, U)).epi_derivedHomologyMap_zero
      (arrowSectionsResolution Y f U))

/-! ### Coherence -/

variable (f)

/-- **Coherence.** On a locally Noetherian scheme, `Lⱼ Φ(f)` is coherent when `F'` and `F` are of
finite type and `Φ` has finite `j`-th derived modules at arrows of finite modules over Noetherian
rings. -/
theorem isCoherent_derivedSheaf [IsLocallyNoetherian Y] [F'.IsFiniteType] [F.IsFiniteType]
    (hΦ : Φ.HasFlatBaseChange) (j : ℕ)
    (hfin : ∀ (A : CommRingCat.{u}), IsNoetherianRing A →
      ∀ (X : ComposableArrows (ModuleCat.{u} A) 1), Module.Finite A X.left →
        Module.Finite A X.right → ∀ P : SimplicialProjectiveResolution X,
          Module.Finite A (P.derivedHomology (D := ModuleCat.{u} A) (Φ.obj A) j)) :
    _root_.SheafOfModules.IsCoherent (Φ.derivedSheaf f hΦ j) :=
  isCoherent_sheaf _ fun U => hfin _ (IsLocallyNoetherian.component_noetherian U) _
    (AlgebraicGeometry.CoherentFinite.finite_sections F' U.2)
    (AlgebraicGeometry.CoherentFinite.finite_sections F U.2) _

/-! ### Stalks and support -/

variable {Φ}

/-- **The length of a stalk of `Lⱼ Φ(f)`.** Let `y` be a point of an affine open `U` with prime
`𝔭 ⊆ Γ(Y, U)`, let `Z` be an arrow of `Γ(Y, U)_𝔭`-modules and `g : X_U ⟶ Z` a morphism into its
restriction of scalars whose adjoint `Γ(Y, U)_𝔭 ⊗ X_U ⟶ Z` is an isomorphism. Then the stalk of
`Lⱼ Φ(f)` at `y` has the length of `Lⱼ Φ(Z)`, computed with any resolution `Q` of `Z`. -/
theorem length_stalk_derivedSheaf (hΦ : Φ.HasFlatBaseChange) (j : ℕ) (U : Y.affineOpens) {y : Y}
    (hy : y ∈ (U : Y.Opens))
    {Z : ComposableArrows (ModuleCat.{u}
      (CommRingCat.of (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal))) 1}
    (g : arrowSections f U ⟶ (restrictScalarsArrow (algebraMap Γ(Y, U)
      (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal))).obj Z)
    (hg : IsIso (((extendRestrictScalarsArrowAdj _).homEquiv _ _).symm g))
    (Q : SimplicialProjectiveResolution Z) :
    Module.length (Y.presheaf.stalk y) ((Φ.derivedSheaf f hΦ j).presheaf.stalk y) =
      Module.length (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)
        (Q.derivedHomology (D := ModuleCat.{u} _)
          (Φ.obj (CommRingCat.of (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)))
            j) := by
  set 𝔭 := (U.2.primeIdealOf ⟨y, hy⟩).asIdeal
  let φ : Γ(Y, U) ⟶ CommRingCat.of (Localization.AtPrime 𝔭) :=
    CommRingCat.ofHom (algebraMap Γ(Y, U) (Localization.AtPrime 𝔭))
  have hb := isBaseChangeAlong_derivedSemilinearMap φ
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ 𝔭.primeCompl)) hΦ g hg
    (arrowSectionsResolution Y f U) Q j
  rw [ModuleStalkSpecialization.length_stalk_eq_length_localizedModule _ U.2 hy,
    ← length_localizedModule_eq_of_isBaseChangeAlong 𝔭.primeCompl _ hb]
  exact (LinearEquiv.ofBijective
    (LocalizedModule.map 𝔭.primeCompl (Φ.derivedSheafSectionsEquiv f hΦ j U).toLinearMap)
    ⟨LocalizedModule.map_injective _ _ (Φ.derivedSheafSectionsEquiv f hΦ j U).injective,
      LocalizedModule.map_surjective _ _
        (Φ.derivedSheafSectionsEquiv f hΦ j U).surjective⟩).length_eq

/-- The length of a stalk of `Lⱼ Φ(f)` is the length of `Lⱼ Φ` at the localized arrow
`X_U ⊗ Γ(Y, U)_𝔭`, computed with any resolution. -/
private theorem length_stalk_derivedSheaf_extendScalarsArrow (hΦ : Φ.HasFlatBaseChange) (j : ℕ)
    (U : Y.affineOpens) {y : Y} (hy : y ∈ (U : Y.Opens))
    (Q : SimplicialProjectiveResolution ((extendScalarsArrow (algebraMap Γ(Y, U)
      (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal))).obj (arrowSections f U))) :
    Module.length (Y.presheaf.stalk y) ((Φ.derivedSheaf f hΦ j).presheaf.stalk y) =
      Module.length (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)
        (Q.derivedHomology (D := ModuleCat.{u} _)
          (Φ.obj (CommRingCat.of (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)))
            j) :=
  length_stalk_derivedSheaf f hΦ j U hy
    ((extendRestrictScalarsArrowAdj _).unit.app (arrowSections f U)) (by
      rw [Adjunction.homEquiv_symm_unit]
      infer_instance) Q

/-- **The multiplicity of `Lⱼ Φ(f)` at a point** `y` of an affine open `U` with prime `𝔭` is the
length of `Lⱼ Φ(Z)` for any arrow `Z` of `Γ(Y, U)_𝔭`-modules which is the base change of `X_U`,
computed with any resolution. -/
theorem sheafMultiplicity_derivedSheaf (hΦ : Φ.HasFlatBaseChange) (j : ℕ) (U : Y.affineOpens)
    {y : Y} (hy : y ∈ (U : Y.Opens))
    {Z : ComposableArrows (ModuleCat.{u}
      (CommRingCat.of (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal))) 1}
    (g : arrowSections f U ⟶ (restrictScalarsArrow (algebraMap Γ(Y, U)
      (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal))).obj Z)
    (hg : IsIso (((extendRestrictScalarsArrowAdj _).homEquiv _ _).symm g))
    (Q : SimplicialProjectiveResolution Z) :
    Chow.sheafMultiplicity (Φ.derivedSheaf f hΦ j) y =
      (Module.length (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)
        (Q.derivedHomology (D := ModuleCat.{u} _)
          (Φ.obj (CommRingCat.of (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)))
            j)).toNat := by
  rw [Chow.sheafMultiplicity, length_stalk_derivedSheaf f hΦ j U hy g hg Q]

/-- **The multiplicity of `Lⱼ Φ(f)` at a point** `y` of an affine open `U` with prime `𝔭` is the
length of `Lⱼ Φ` at the localized arrow `X_U ⊗ Γ(Y, U)_𝔭`, computed with any resolution. -/
theorem sheafMultiplicity_derivedSheaf_eq_length_extendScalarsArrow (hΦ : Φ.HasFlatBaseChange)
    (j : ℕ) (U : Y.affineOpens) {y : Y} (hy : y ∈ (U : Y.Opens))
    (Q : SimplicialProjectiveResolution ((extendScalarsArrow (algebraMap Γ(Y, U)
      (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal))).obj (arrowSections f U))) :
    Chow.sheafMultiplicity (Φ.derivedSheaf f hΦ j) y =
      (Module.length (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)
        (Q.derivedHomology (D := ModuleCat.{u} _)
          (Φ.obj (CommRingCat.of (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)))
            j)).toNat :=
  by rw [Chow.sheafMultiplicity, length_stalk_derivedSheaf_extendScalarsArrow f hΦ j U hy Q]

/-- **Support.** If the `j`-th derived module of `Φ` vanishes at every arrow with zero source and
target, then `Lⱼ Φ(f)` is supported in `supp F' ∪ supp F`. -/
theorem supp_derivedSheaf_subset (hΦ : Φ.HasFlatBaseChange) (j : ℕ)
    (hzero : ∀ (A : CommRingCat.{u}) (X : ComposableArrows (ModuleCat.{u} A) 1),
      IsZero X.left → IsZero X.right → ∀ P : SimplicialProjectiveResolution X,
        IsZero (P.derivedHomology (D := ModuleCat.{u} A) (Φ.obj A) j)) :
    SheafOfModules.supp (Φ.derivedSheaf f hΦ j) ⊆
      SheafOfModules.supp F' ∪ SheafOfModules.supp F := by
  intro y hy
  by_contra hyZ
  rw [Set.mem_union, not_or] at hyZ
  obtain ⟨V, hV, hyV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show y ∈ (⊤ : Y.Opens) from trivial)
  let U : Y.affineOpens := ⟨V, hV⟩
  set 𝔭 := (U.2.primeIdealOf ⟨y, hyV⟩).asIdeal
  let φ : Γ(Y, U) ⟶ CommRingCat.of (Localization.AtPrime 𝔭) :=
    CommRingCat.ofHom (algebraMap Γ(Y, U) (Localization.AtPrime 𝔭))
  -- The terms of the localized arrow of sections vanish, since the stalks of `F'` and `F` do.
  have hterm : ∀ (G : Y.Modules) [G.IsQuasicoherent], y ∉ SheafOfModules.supp G →
      IsZero ((ModuleCat.extendScalars φ.hom).obj
        (ModuleCat.of Γ(Y, U) Γ(G, (U : Y.Opens)))) := by
    intro G _ hG
    let M := ModuleCat.of Γ(Y, U) Γ(G, (U : Y.Opens))
    have hu : IsIso (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv M
        ((ModuleCat.extendScalars φ.hom).obj M)).symm
        ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M)) := by
      rw [Adjunction.homEquiv_symm_unit]
      infer_instance
    have hb := @Stacks.Modules.isBaseChangeAlong_of_isIso _ _ _ _ φ.hom _ _
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M) hu
    have hl := length_localizedModule_eq_of_isBaseChangeAlong 𝔭.primeCompl
      (T := Localization.AtPrime 𝔭) _ hb
    have h0 : Module.length (Y.presheaf.stalk y) (G.presheaf.stalk y) = 0 :=
      Module.length_eq_zero_iff.2 <| not_nontrivial_iff_subsingleton.1
        fun h => hG ((SheafOfModules.mem_supp_iff_nontrivial_stalk G y).2 h)
    have h1 := hl.symm.trans
      ((ModuleStalkSpecialization.length_stalk_eq_length_localizedModule G U.2 hyV).symm.trans h0)
    exact @ModuleCat.isZero_of_subsingleton _ _ _ (Module.length_eq_zero_iff.1 h1)
  let Q : SimplicialProjectiveResolution
      ((extendScalarsArrow φ.hom).obj (arrowSections f U)) := Classical.arbitrary _
  have hlen := length_stalk_derivedSheaf_extendScalarsArrow f hΦ j U hyV Q
  have hz := hzero (CommRingCat.of (Localization.AtPrime 𝔭)) _ (hterm F' hyZ.1) (hterm F hyZ.2) Q
  have h0 := hlen.trans (Module.length_eq_zero_iff (R := Localization.AtPrime 𝔭).2
    (ModuleCat.isZero_iff_subsingleton.1 hz))
  exact (not_nontrivial_iff_subsingleton.2 (Module.length_eq_zero_iff.1 h0))
    ((SheafOfModules.mem_supp_iff_nontrivial_stalk _ y).1 hy)

/-- **Support**, relative to a set: if the `j`-th derived module of `Φ` vanishes at every arrow
with zero source and target and `W` contains the supports of `F'` and `F`, then `Lⱼ Φ(f)` is
supported in `W`. -/
theorem supp_derivedSheaf_subset_of_subset (hΦ : Φ.HasFlatBaseChange) (j : ℕ)
    (hzero : ∀ (A : CommRingCat.{u}) (X : ComposableArrows (ModuleCat.{u} A) 1),
      IsZero X.left → IsZero X.right → ∀ P : SimplicialProjectiveResolution X,
        IsZero (P.derivedHomology (D := ModuleCat.{u} A) (Φ.obj A) j))
    {W : Set Y} (hF' : SheafOfModules.supp F' ⊆ W) (hF : SheafOfModules.supp F ⊆ W) :
    SheafOfModules.supp (Φ.derivedSheaf f hΦ j) ⊆ W :=
  (supp_derivedSheaf_subset f hΦ j hzero).trans (Set.union_subset hF' hF)

end Stacks.SemilinearArrowFunctor
