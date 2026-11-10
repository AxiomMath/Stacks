module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.Topology.Sheaves.Abelian
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Surjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Vanishing of relative differentials descends along a surjective étale morphism

Let `g : X ⟶ Y` be a morphism of schemes and let `f : X' ⟶ X` be surjective and étale.  If the
sheaf of relative differentials of `f ≫ g` is zero, then so is that of `g`.

## Main results

* `AlgebraicGeometry.isZero_relativeDifferentials_of_surjective_etale`: the descent statement
  above.
* `AlgebraicGeometry.formallyUnramified_iff_isZero_relativeDifferentials`: a morphism of schemes
  is formally unramified exactly when its sheaf of relative differentials vanishes.

## Implementation notes

Vanishing is the intrinsic categorical predicate `CategoryTheory.Limits.IsZero`, not equality
with a chosen zero object, and relative differentials are
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials`.

Both directions of the vanishing criterion are affine-local and go through
[Stacks, Tag 01UT]: over affine opens `U ≤ f ⁻¹ᵁ V` the sections of the sheaf of relative
differentials are the Kähler differentials of `Γ(S, V) ⟶ Γ(X, U)`, so their vanishing is
`Algebra.FormallyUnramified` of that ring map.  Globalizing from the affine opens to the sheaf
uses that a sheaf of modules on a scheme is zero as soon as all its stalks are, and that the
affine opens form a basis.

Descent itself is pointwise on stalks.  Formal unramifiedness of a ring map has the local
property `RingHom.FormallyUnramified.ofLocalizationPrime`, so it suffices to treat the map of
local rings `𝒪_{Y,g(f x')} ⟶ 𝒪_{X,f x'}`; the composite to `𝒪_{X',x'}` is formally unramified
by hypothesis, and `𝒪_{X,f x'} ⟶ 𝒪_{X',x'}` is formally étale and faithfully flat because `f` is
étale and a local homomorphism, so the Kähler differentials of the middle map are killed after a
faithfully flat base change and therefore already zero.

## References

* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 02HM](https://stacks.math.columbia.edu/tag/02HM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### Formal unramifiedness and the vanishing of relative differentials -/

/-- Sections of the sheaf of relative differentials over an affine open vanish exactly when the
map on sections is formally unramified. -/
private theorem isZero_relativeDifferentials_app_iff {X S : Scheme.{u}} (f : X ⟶ S)
    {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) :
    IsZero ((Scheme.Hom.relativeDifferentials f).val.obj (.op U)) ↔
      RingHom.FormallyUnramified (f.appLE V U hUV).hom := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  obtain ⟨e, -⟩ :=
    Stacks.AlgebraicGeometry.AffineDifferentialsIso.existsUnique_affineDifferentialsIso
      f hU hUV hV
  change _ ↔ RingHom.FormallyUnramified (algebraMap Γ(S, V) Γ(X, U))
  rw [RingHom.formallyUnramified_algebraMap, Algebra.formallyUnramified_iff]
  exact ⟨fun h => ModuleCat.isZero_iff_subsingleton.mp (h.of_iso e.symm),
    fun h => (ModuleCat.isZero_iff_subsingleton.mpr h).of_iso e⟩

/-- A morphism of schemes whose sheaf of relative differentials vanishes is formally
unramified: over affine opens the sections of that sheaf are the Kähler differentials of the
map on sections, by [Stacks, Tag 01UT]. -/
@[ega "IV 17.2.1" "Sufficiency"]
theorem formallyUnramified_of_isZero_relativeDifferentials {X S : Scheme.{u}} (f : X ⟶ S)
    (hz : IsZero (Scheme.Hom.relativeDifferentials f)) : FormallyUnramified f :=
  ⟨fun {_} hV {U} hU hUV => (isZero_relativeDifferentials_app_iff f hU hV hUV).mp
    (Functor.map_isZero (PresheafOfModules.evaluation X.ringCatSheaf.obj (.op U))
      (Functor.map_isZero (Scheme.Modules.toPresheafOfModules X) hz))⟩

/-- For a formally unramified morphism the sections of the sheaf of relative differentials
vanish over every affine open contained in the preimage of an affine open of the base. -/
theorem isZero_relativeDifferentials_app_of_formallyUnramified {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : FormallyUnramified f) {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens}
    (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) :
    IsZero ((Scheme.Hom.relativeDifferentials f).val.obj (.op U)) :=
  (isZero_relativeDifferentials_app_iff f hU hV hUV).mpr (f.formallyUnramified_appLE hV hU hUV)

/-- A formally unramified morphism of schemes has vanishing sheaf of relative differentials:
the sections vanish over a basis of affine opens, so every germ vanishes. -/
@[ega "IV 17.2.1" "Necessity"]
theorem isZero_relativeDifferentials_of_formallyUnramified {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : FormallyUnramified f) : IsZero (Scheme.Hom.relativeDifferentials f) := by
  let M := Scheme.Hom.relativeDifferentials f
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  have hF : IsZero F := by
    rw [TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
    intro x
    change IsZero (M.presheaf.stalk x)
    rw [IsZero.iff_id_eq_zero]
    apply TopCat.Presheaf.stalk_hom_ext (F := M.presheaf)
    intro W hxW
    ext s
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ W ⊓ f ⁻¹ᵁ V from ⟨hxW, hxV⟩)
        (W.2.inter (V.2.preimage f.continuous))
    have hzU := isZero_relativeDifferentials_app_of_formallyUnramified f hf hU hV
      (hUW.trans inf_le_right)
    have : Subsingleton (M.presheaf.obj (.op U)) := ModuleCat.isZero_iff_subsingleton.mp hzU
    let i : U ⟶ W := homOfLE (show U ≤ W from hUW.trans inf_le_left)
    change M.presheaf.germ W x hxW s = 0
    rw [← M.presheaf.germ_res_apply i x hxU s, Subsingleton.elim (M.presheaf.map i.op s) 0]
    simp
  have hP' : IsZero M.presheaf := by
    simpa [TopCat.Sheaf.forget, F] using Functor.map_isZero (TopCat.Sheaf.forget Ab X) hF
  refine (IsZero.iff_id_eq_zero _).mpr ((Scheme.Modules.toPresheaf X).map_injective ?_)
  change 𝟙 ((Scheme.Modules.toPresheaf X).obj M) = 0
  change IsZero ((Scheme.Modules.toPresheaf X).obj M) at hP'
  exact (IsZero.iff_id_eq_zero _).mp hP'

/-- A morphism of schemes is formally unramified exactly when its sheaf of relative
differentials vanishes. -/
@[ega "IV 17.2.1"]
theorem formallyUnramified_iff_isZero_relativeDifferentials {X S : Scheme.{u}} (f : X ⟶ S) :
    FormallyUnramified f ↔ IsZero (Scheme.Hom.relativeDifferentials f) :=
  ⟨isZero_relativeDifferentials_of_formallyUnramified f,
    formallyUnramified_of_isZero_relativeDifferentials f⟩

/-! ### Formal étaleness as a local property of ring maps -/

/-- Formal unramifiedness descends along a faithfully flat formally étale algebra: the Kähler
differentials of `A` over `R` become those of `B` over `R` after the base change to `B`, which
is faithfully flat. -/
@[ega "IV 17.7.7" "special case"]
theorem Algebra.formallyUnramified_of_faithfullyFlat_formallyEtale {R A B : Type u} [CommRing R]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FormallyEtale A B] [Module.FaithfullyFlat A B]
    (h : Algebra.FormallyUnramified R B) : Algebra.FormallyUnramified R A :=
  have : Subsingleton (Ω[B⁄R]) := h.subsingleton_kaehlerDifferential
  have : Subsingleton (B ⊗[A] Ω[A⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B).injective.subsingleton
  ⟨Module.FaithfullyFlat.lTensor_reflects_triviality A B (Ω[A⁄R])⟩

/-- Formal étaleness of ring maps is stable under composition. -/
theorem formallyEtale_stableUnderComposition :
    RingHom.StableUnderComposition RingHom.FormallyEtale :=
  fun _ _ _ _ _ _ _ _ hf hg => RingHom.FormallyEtale.comp hf hg

/-- Formal étaleness of ring maps respects isomorphisms. -/
theorem formallyEtale_respectsIso : RingHom.RespectsIso RingHom.FormallyEtale := by
  apply formallyEtale_stableUnderComposition.respectsIso
  intro R S _ _ e
  let : Algebra R S := e.toRingHom.toAlgebra
  change Algebra.FormallyEtale R S
  exact Algebra.FormallyEtale.of_equiv (A := R) (AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl)

/-- A localization map is formally étale. -/
theorem formallyEtale_holdsForLocalization :
    RingHom.HoldsForLocalization RingHom.FormallyEtale := by
  intro R S _ _ _ M _
  rw [RingHom.formallyEtale_algebraMap]
  exact Algebra.FormallyEtale.of_isLocalization M

/-- Formal étaleness of ring maps is preserved by localization at a submonoid of the source. -/
theorem formallyEtale_localizationPreserves :
    RingHom.LocalizationPreserves RingHom.FormallyEtale := by
  intro R S _ _ φ M R' S' _ _ _ _ _ _ hφ
  let ψ : R' →+* S' := IsLocalization.map S' φ (Submonoid.le_comap_map M)
  algebraize [φ, ψ]
  let : Algebra R S' := Algebra.compHom S' (algebraMap R S)
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq' (by
    calc algebraMap R S' = (algebraMap S S').comp φ := rfl
      _ = ψ.comp (algebraMap R R') :=
        (IsLocalization.map_comp (Submonoid.le_comap_map M)).symm
      _ = (algebraMap R' S').comp (algebraMap R R') := rfl)
  have : Algebra.FormallyEtale R S := by
    rw [← RingHom.formallyEtale_algebraMap]
    exact hφ
  change Algebra.FormallyEtale R' S'
  exact Algebra.FormallyEtale.localization_map (R := R) (S := S) (Rₘ := R') (Sₘ := S') M

/-- The map of local rings induced by an étale ring map at a prime is formally étale. -/
theorem formallyEtale_of_etale_localRingHom {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : RingHom.Etale φ) (J : Ideal S) (hJ : J.IsPrime) :
    RingHom.FormallyEtale (Localization.localRingHom (J.comap φ) J φ rfl) :=
  have hφ' : RingHom.FormallyEtale φ := by
    algebraize [φ]
    change (algebraMap R S).Etale at hφ
    exact ((RingHom.etale_algebraMap).mp hφ).formallyEtale
  RingHom.HoldsForLocalization.localRingHom formallyEtale_stableUnderComposition
    formallyEtale_localizationPreserves formallyEtale_holdsForLocalization rfl hφ'

/-! ### The descent statement -/

/-- **Vanishing of the sheaf of relative differentials descends along a surjective étale
morphism.** -/
theorem isZero_relativeDifferentials_of_surjective_etale {X' X Y : Scheme.{u}} (g : X ⟶ Y)
    (f : X' ⟶ X) [Surjective f] [Etale f]
    (h : IsZero (Scheme.Hom.relativeDifferentials (f ≫ g))) :
    IsZero (Scheme.Hom.relativeDifferentials g) := by
  have : FormallyUnramified (f ≫ g) :=
    formallyUnramified_of_isZero_relativeDifferentials (f ≫ g) h
  refine isZero_relativeDifferentials_of_formallyUnramified g ?_
  apply HasRingHomProperty.of_stalkMap RingHom.FormallyUnramified.ofLocalizationPrime
  intro x
  obtain ⟨x', rfl⟩ := f.surjective x
  have hComp : RingHom.FormallyUnramified
      ((f.stalkMap x').hom.comp (g.stalkMap (f x')).hom) := by
    have h₀ := FormallyUnramified.stalkMap (f ≫ g) x'
    rw [congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp f g x')] at h₀
    rwa [← CommRingCat.hom_comp]
  have hEtale : RingHom.FormallyEtale (f.stalkMap x').hom :=
    HasRingHomProperty.stalkMap_of_respectsIso formallyEtale_respectsIso
      formallyEtale_of_etale_localRingHom ‹Etale f› x'
  algebraize [(g.stalkMap (f x')).hom, (f.stalkMap x').hom,
    (f.stalkMap x').hom.comp (g.stalkMap (f x')).hom]
  have hComp' :
      Algebra.FormallyUnramified (Y.presheaf.stalk (g (f x'))) (X'.presheaf.stalk x') := by
    rw [← RingHom.formallyUnramified_algebraMap]
    simpa only [RingHom.algebraMap_toAlgebra] using hComp
  have : Algebra.FormallyEtale (X.presheaf.stalk (f x')) (X'.presheaf.stalk x') := by
    rw [← RingHom.formallyEtale_algebraMap]
    exact hEtale
  have : IsLocalHom (algebraMap (X.presheaf.stalk (f x')) (X'.presheaf.stalk x')) :=
    f.toLRSHom.prop x'
  have : Module.Flat (X.presheaf.stalk (f x')) (X'.presheaf.stalk x') :=
    RingHom.flat_algebraMap_iff.mp (Flat.stalkMap f x')
  have : Module.FaithfullyFlat (X.presheaf.stalk (f x')) (X'.presheaf.stalk x') :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  change RingHom.FormallyUnramified
    (algebraMap (Y.presheaf.stalk (g (f x'))) (X.presheaf.stalk (f x')))
  rw [RingHom.formallyUnramified_algebraMap]
  exact Algebra.formallyUnramified_of_faithfullyFlat_formallyEtale hComp'

end AlgebraicGeometry

end
