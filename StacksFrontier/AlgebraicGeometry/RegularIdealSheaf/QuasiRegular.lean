module

public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Algebra
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Affine-local characterization of quasi-regular ideal sheaves

Let `X` be a scheme and `J ⊆ O_X` a sheaf of ideals.  Then `J` is quasi-regular if and only if,
around each point of the support of `O_X / J`, it is generated on an affine open by a sequence
which is quasi-regular in the ring of sections of that open.

## Main results

* `isQuasiRegularMapIso_iff_forall_germ`: the sheaf quasi-regularity morphism of a family of
  sections of an open `U` is an isomorphism exactly when the elementary relation condition holds
  at every stalk over `U`.
* `forall_isQuasiRegularRel_germ_iff`: over an affine open those stalkwise conditions are
  quasi-regularity of the sequence in the ring of sections.
* `isQuasiRegularIdealSheaf_iff_exists_affine_generators`: a sheaf of ideals is quasi-regular
  exactly when, near each point of the support of its quotient, it is generated on an affine open
  by a quasi-regular sequence in the ring of sections.

## References

* [Stacks Project, Lemma 31.20.2 (Tag 063G)](https://stacks.math.columbia.edu/tag/063G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.RingTheory.QuasiRegular
open Stacks.RingTheory.RegularIdealSheaf
open Stacks.AlgebraicGeometry.QuasiRegular
open Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

section Stalkwise

variable (X : RingedSpace.{u}) {r : ℕ}

/-- On each stalk the quasi-regularity morphism of Stacks tag 063B is, up to the canonical
identifications, the ring-level quasi-regularity map of the germs. -/
theorem bijective_stalkFunctor_map_iff
    (f : Fin r → X.presheaf.obj (op (⊤ : Opens X))) (x : X) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (quasiRegularMap X f).hom.hom) ↔
      Function.Bijective (associatedGradedMap (germSequence X f x)) := by
  have hA : Function.Bijective
      (ConcreteCategory.hom ((quasiRegularMap X f).associatedGradedStalkIso x).hom) :=
    ConcreteCategory.bijective_of_isIso _
  have hB : Function.Bijective
      (ConcreteCategory.hom ((quasiRegularMap X f).polynomialStalkIso x).hom) :=
    ConcreteCategory.bijective_of_isIso _
  have heq : (ConcreteCategory.hom ((quasiRegularMap X f).associatedGradedStalkIso x).hom) ∘
        (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
          (quasiRegularMap X f).hom.hom))
      = (associatedGradedMap (germSequence X f x)) ∘
        (ConcreteCategory.hom ((quasiRegularMap X f).polynomialStalkIso x).hom) :=
    funext ((quasiRegularMap X f).stalk_map x)
  exact (Function.Bijective.of_comp_iff' hA _).symm.trans
    ((iff_of_eq (congrArg Function.Bijective heq)).trans (Function.Bijective.of_comp_iff _ hB))

/-- The quasi-regularity morphism of Stacks tag 063B is an isomorphism exactly when the
ring-level quasi-regularity map is bijective at every stalk. -/
theorem isIso_quasiRegularMap_hom_iff (f : Fin r → X.presheaf.obj (op (⊤ : Opens X))) :
    IsIso (quasiRegularMap X f).hom ↔
      ∀ x : X, Function.Bijective (associatedGradedMap (germSequence X f x)) := by
  constructor
  · intro hiso x
    refine (bijective_stalkFunctor_map_iff X f x).mp ?_
    have : IsIso (quasiRegularMap X f).hom.hom :=
      inferInstanceAs
        (IsIso ((TopCat.Sheaf.forget CommRingCat.{u} X).map (quasiRegularMap X f).hom))
    exact ConcreteCategory.bijective_of_isIso _
  · intro h
    have hst : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (quasiRegularMap X f).hom.hom) := fun x =>
      (ConcreteCategory.isIso_iff_bijective _).mpr
        ((bijective_stalkFunctor_map_iff X f x).mpr (h x))
    exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso (quasiRegularMap X f).hom

/-- The quasi-regularity morphism of a family
of sections over an open `U`, read on `X` restricted to `U`, is an isomorphism exactly when the
germs of the family satisfy the elementary relation condition at every point of `U`. -/
theorem isQuasiRegularMapIso_iff_forall_germ (U : Opens X)
    (f : Fin r → X.presheaf.obj (op U)) :
    IsIso (quasiRegularMap (X.restrict U.isOpenEmbedding)
        (fun i => sectionOnRestriction X U (f i))).hom ↔
      ∀ (y : X) (hy : y ∈ U), IsQuasiRegularRel (germFamily X U f y hy) := by
  rw [isIso_quasiRegularMap_hom_iff]
  constructor
  · intro h y hy
    refine isQuasiRegularRel_congr ?_
      (isQuasiRegularRel_ringEquiv (restrictStalkEquiv X U y hy) _
        ((isQuasiRegularRel_iff_bijective _).mpr (h ⟨y, hy⟩)))
    funext i
    exact restrictStalkEquiv_germSequence X U f y hy i
  · intro h z
    refine (isQuasiRegularRel_iff_bijective _).mp (isQuasiRegularRel_congr ?_
      (isQuasiRegularRel_ringEquiv (restrictStalkEquiv X U z.1 z.2).symm _ (h z.1 z.2)))
    funext i
    rw [← restrictStalkEquiv_germSequence X U f z.1 z.2 i, RingEquiv.symm_apply_apply]
    rfl

end Stalkwise

section Affine

/-- Over an affine open the stalkwise elementary relation conditions
on the germs of a family of sections are exactly quasi-regularity of the family in the ring of
sections of that open. -/
theorem forall_isQuasiRegularRel_germ_iff (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    {r : ℕ} (f : Fin r → Γ(X, U)) :
    (∀ (y : X) (hy : y ∈ U), IsQuasiRegularRel (germFamily X.toRingedSpace U f y hy)) ↔
      RingTheory.Sequence.IsQuasiRegular Γ(X, U) (List.ofFn f) := by
  constructor
  · intro h
    rw [isQuasiRegular_ofFn_iff, ← isQuasiRegularRel_iff_bijective]
    intro p T hT hd e
    refine mem_of_forall_maximal (Jid f) _ fun m hm => ?_
    obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
      (Scheme.forgetToTop.map hU.isoSpec.hom)).2 (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(X, U))
    let _ := X.presheaf.algebra_section_stalk z
    have _ := hU.isLocalization_stalk z
    have hmz : (hU.primeIdealOf z).asIdeal = m := congrArg PrimeSpectrum.asIdeal hz
    obtain ⟨t, htT, hta⟩ := exists_mul_coeff_mem_of_localization
      (hU.primeIdealOf z).asIdeal.primeCompl (X.presheaf.stalk z.1) f (h z.1 z.2) p T hT hd e
    exact ⟨t, hmz ▸ htT, hta⟩
  · intro hqr y hy
    let _ := X.presheaf.algebra_section_stalk (⟨y, hy⟩ : ↥U)
    have _ := hU.isLocalization_stalk (⟨y, hy⟩ : ↥U)
    exact IsQuasiRegularRel.localization f
      (hU.primeIdealOf (⟨y, hy⟩ : ↥U)).asIdeal.primeCompl (X.presheaf.stalk y)
      ((isQuasiRegularRel_iff_bijective f).mpr ((isQuasiRegular_ofFn_iff f).mp hqr))

end Affine

/-- A sheaf of ideals on a scheme is quasi-regular
if and only if, around each point of the support of its quotient, it is generated on an affine
open by a quasi-regular sequence in the ring of sections of that open. -/
@[stacks 063G "quasi_regular"]
theorem isQuasiRegularIdealSheaf_iff_exists_affine_generators (X : Scheme.{u})
    (J : (structureSheafModule X.toRingedSpace).Submodule) :
    IsQuasiRegularIdealSheaf X.toRingedSpace J ↔
      ∀ x : X, x ∈ idealQuotientSupport X.toRingedSpace J →
        ∃ (U : X.affineOpens) (_hx : x ∈ (U : Set X)) (r : ℕ)
          (f : Fin r → X.toRingedSpace.presheaf.obj (op U.1)),
          IsGeneratedByOn X.toRingedSpace J U.1 f ∧
            RingTheory.Sequence.IsQuasiRegular
              (X.toRingedSpace.presheaf.obj (op U.1)) (List.ofFn f) := by
  constructor
  · intro h x hx
    obtain ⟨U₀, hxU₀, r, f, hiso, hgen⟩ := h x hx
    obtain ⟨V, hV, hxV, hVU₀⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU₀
    refine ⟨⟨V, hV⟩, hxV, r, fun i => X.presheaf.map (homOfLE hVU₀).op (f i),
      isGeneratedByOn_of_le U₀ f hgen V hVU₀, ?_⟩
    refine (forall_isQuasiRegularRel_germ_iff X V hV _).mp fun y hy => ?_
    rw [germFamily_res U₀ V hVU₀ f y hy]
    exact (isQuasiRegularMapIso_iff_forall_germ X.toRingedSpace U₀ f).mp hiso y (hVU₀ hy)
  · intro h x hx
    obtain ⟨U, hxU, r, f, hgen, hqr⟩ := h x hx
    exact ⟨U.1, hxU, r, f,
      (isQuasiRegularMapIso_iff_forall_germ X.toRingedSpace U.1 f).mpr
        ((forall_isQuasiRegularRel_germ_iff X U.1 U.2 f).mpr hqr), hgen⟩

end Stacks.AlgebraicGeometry.RegularIdealSheaf
