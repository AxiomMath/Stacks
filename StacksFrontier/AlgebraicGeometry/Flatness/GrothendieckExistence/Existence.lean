module

public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite

/-!
# Grothendieck's existence theorem in its derived form

In Situation [Stacks, Tag 0DIB] there is a pseudo-coherent `K ∈ D(𝒪_X)` with
`K ⊗ᴸ_{𝒪_X} 𝒪_{Xₙ} ≅ Kₙ` for all `n`, compatibly with the maps `φₙ`
([Stacks, Tag 0DIG]). The source's `K` is `DQ_X(R lim R(iₙ)_* Kₙ)` ([Stacks, Tag 0DIC]); it is
pseudo-coherent by [Stacks, Tag 0DIE], and its restriction to `Xₙ` is `Kₙ` by
[Stacks, Tag 0DIF] on affine opens.

This module records the formal part of the argument: how maps `πₙ : K ⟶ R(iₙ)_* Kₙ` out of an
object of `D(𝒪_X)` which are compatible with the tower of derived direct images give, by
adjunction, maps `βₙ : L(iₙ)^* K ⟶ Kₙ` compatible with the `φₙ`.

## Main definitions

* `AlgebraicGeometry.GrothendieckExistence.pushforwardTransition`: for `h = f ≫ g` and
  `φ : Lf^* M ⟶ L`, the map `Rg_* M ⟶ Rh_* L` adjoint to `φ` under `Lf^* ⊣ Rf_*` and pushed
  forward along `g`.
* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.levelInclusion`,
  `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.levelTransition`: the closed
  immersions `iₙ : Xₙ ⟶ X` and `jₙ : Xₙ ⟶ Xₙ₊₁` as morphisms of ringed spaces.
* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.towerTransition`: the
  transition `R(iₙ₊₁)_* Kₙ₊₁ ⟶ R(iₙ)_* Kₙ` of the tower of derived direct images.

## Main results

* `AlgebraicGeometry.GrothendieckExistence.derivedPullbackCompIso_hom_app_comp_homEquiv_symm`:
  adjoints of maps compatible with a `pushforwardTransition` are compatible with `φ`.
* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.`
  `exists_derivedPullback_iso_of_isIso`:
  a pseudo-coherent `K` with compatible maps `πₙ` whose adjoints are invertible satisfies the
  conclusion of [Stacks, Tag 0DIG].

## Implementation notes

The derived tensor product `K ⊗ᴸ_{𝒪_X} 𝒪_{Xₙ}`, an object on the closed subscheme `Xₙ`, is the
derived pullback `L(iₙ)^* K`, the same reading Situation 0DIB gives the derived restriction in
`φₙ`. The compatibility with `φₙ` is the commutativity of
`L(jₙ)^* L(iₙ₊₁)^* K ≅ L(iₙ)^* K ⟶ Kₙ` with `L(jₙ)^* L(iₙ₊₁)^* K ⟶ L(jₙ)^* Kₙ₊₁ ⟶ Kₙ`, where
the first isomorphism is the composition isomorphism of derived pullbacks along `iₙ₊₁ ∘ jₙ = iₙ`.

## References

* [Stacks Project, Tag 0DIG](https://stacks.math.columbia.edu/tag/0DIG)
* [Stacks Project, Tag 0DIB](https://stacks.math.columbia.edu/tag/0DIB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces RingedSpaceModuleAdjunction

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.GrothendieckExistence

section Compatibility

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h)

/-- The map `Rg_* M ⟶ Rh_* L` determined by a map `φ : Lf^* M ⟶ L`, where `h = f ≫ g`: the
image under `Rg_*` of the adjoint `M ⟶ Rf_* L` of `φ`, followed by the composition isomorphism
`Rg_* Rf_* ≅ R(f ≫ g)_* = Rh_*`. -/
def pushforwardTransition {M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
    {L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (φ : (derivedPullback f).obj M ⟶ L) :
    (derivedPushforward g).obj M ⟶ (derivedPushforward h).obj L :=
  (derivedPushforward g).map ((derivedAdjunction f).homEquiv _ _ φ) ≫
    (derivedPushforwardCompIso f g).hom.app L ≫
      eqToHom (congrArg (fun t : X ⟶ Z => (derivedPushforward t).obj L) hfg)

/-- **Compatibility of adjoints along a composite.** Let `h = f ≫ g`, let `φ : Lf^* M ⟶ L`, and
let `π' : K ⟶ Rg_* M`, `π : K ⟶ Rh_* L` be maps out of `K ∈ D(𝒪_Z)` with `π` the composite of
`π'` and `pushforwardTransition f g h hfg φ`. Then the adjoints `β' : Lg^* K ⟶ M` and
`β : Lh^* K ⟶ L` satisfy `Lf^*Lg^* K ≅ Lh^* K ⟶ L  =  Lf^*Lg^* K ⟶ Lf^* M ⟶ L`. -/
theorem derivedPullbackCompIso_hom_app_comp_homEquiv_symm
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))}
    {M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
    {L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (φ : (derivedPullback f).obj M ⟶ L)
    (π' : K ⟶ (derivedPushforward g).obj M) (π : K ⟶ (derivedPushforward h).obj L)
    (hπ : π' ≫ pushforwardTransition f g h hfg φ = π) :
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom.app K ≫
        eqToHom (congrArg (fun t : X ⟶ Z => (derivedPullback t).obj K) hfg) ≫
          ((derivedAdjunction h).homEquiv _ _).symm π =
      (derivedPullback f).map (((derivedAdjunction g).homEquiv _ _).symm π') ≫ φ := by
  subst hfg
  have key : (derivedAdjunction (f ≫ g)).homEquiv _ _
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).inv.app K ≫
        (derivedPullback f).map (((derivedAdjunction g).homEquiv _ _).symm π') ≫ φ) = π := by
    rw [← derivedAdjunction_comp_homEquiv, Iso.hom_inv_id_app_assoc,
      Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simp only [Equiv.apply_symm_apply, ← hπ, pushforwardTransition, eqToHom_refl,
      Category.comp_id, Category.assoc]
  have key' := congrArg ((derivedAdjunction (f ≫ g)).homEquiv K L).symm key
  simp only [Equiv.symm_apply_apply] at key'
  simp only [eqToHom_refl, Category.id_comp, ← key', Iso.hom_inv_id_app_assoc]

end Compatibility

namespace DerivedExistenceSituation

variable (S : DerivedExistenceSituation.{u})

/-- The closed immersion `iₙ : Xₙ ⟶ X` of the base change at level `n`, as a morphism of ringed
spaces. -/
abbrev levelInclusion (n : ℕ) :
    (schemeAt S.system S.X n).toRingedSpace ⟶ S.X.left.toRingedSpace :=
  (schemeProjection S.system S.X n).toLRSHom.toShHom

/-- The closed immersion `jₙ : Xₙ ⟶ Xₙ₊₁` between consecutive base changes, as a morphism of
ringed spaces. -/
abbrev levelTransition (n : ℕ) :
    (schemeAt S.system S.X n).toRingedSpace ⟶ (schemeAt S.system S.X (n + 1)).toRingedSpace :=
  (S.transitionScheme n).toLRSHom.toShHom

/-- `iₙ₊₁ ∘ jₙ = iₙ` as morphisms of ringed spaces: the transition between consecutive base
changes lies over `X`. -/
theorem levelTransition_comp_levelInclusion (n : ℕ) :
    S.levelTransition n ≫ S.levelInclusion (n + 1) = S.levelInclusion n := by
  simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
    congrArg (fun t : schemeAt S.system S.X n ⟶ S.X.left => t.toLRSHom.toShHom)
      (S.transition_fst n)

/-- The transition `R(iₙ₊₁)_* Kₙ₊₁ ⟶ R(iₙ)_* Kₙ` of the tower of derived direct images on `X`:
`R(iₙ₊₁)_*` of the adjoint `Kₙ₊₁ ⟶ R(jₙ)_* Kₙ` of `φₙ`, followed by
`R(iₙ₊₁)_* R(jₙ)_* ≅ R(iₙ₊₁ ∘ jₙ)_* = R(iₙ)_*`. -/
abbrev towerTransition (n : ℕ) :
    (derivedPushforward (S.levelInclusion (n + 1))).obj (S.K (n + 1)) ⟶
      (derivedPushforward (S.levelInclusion n)).obj (S.K n) :=
  pushforwardTransition (S.levelTransition n) (S.levelInclusion (n + 1)) (S.levelInclusion n)
    (S.levelTransition_comp_levelInclusion n) (S.φ n)

/-- **The algebraization criterion.** Let `K ∈ D(𝒪_X)` be pseudo-coherent and let
`πₙ : K ⟶ R(iₙ)_* Kₙ` be maps compatible with the transitions of the tower of derived direct
images. If every adjoint `βₙ : L(iₙ)^* K ⟶ Kₙ` of `πₙ` is an isomorphism, then `K` satisfies the
conclusion of Grothendieck's existence theorem: the `βₙ` are isomorphisms
`K ⊗ᴸ 𝒪_{Xₙ} ≅ Kₙ` compatible with the `φₙ`. -/
theorem exists_derivedPullback_iso_of_isIso
    (K : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} S.X.left.toRingedSpace))
    (hK : RingedSpace.IsPseudoCoherent (X := S.X.left.toRingedSpace) K)
    (π : ∀ n : ℕ, K ⟶ (derivedPushforward (S.levelInclusion n)).obj (S.K n))
    (hπ : ∀ n : ℕ, π (n + 1) ≫ S.towerTransition n = π n)
    (hiso : ∀ n : ℕ, IsIso (((derivedAdjunction (S.levelInclusion n)).homEquiv _ _).symm (π n))) :
    ∃ K : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} S.X.left.toRingedSpace),
      RingedSpace.IsPseudoCoherent (X := S.X.left.toRingedSpace) K ∧
        ∃ β : ∀ n : ℕ, (derivedPullback (S.levelInclusion n)).obj K ≅ S.K n,
          ∀ n : ℕ,
            (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
                (S.levelTransition n) (S.levelInclusion (n + 1))).hom.app K ≫
              eqToHom (congrArg (fun t : (schemeAt S.system S.X n).toRingedSpace ⟶
                  S.X.left.toRingedSpace => (derivedPullback t).obj K)
                (S.levelTransition_comp_levelInclusion n)) ≫ (β n).hom =
            (derivedPullback (S.levelTransition n)).map (β (n + 1)).hom ≫ S.φ n :=
  ⟨K, hK, fun n => asIso (((derivedAdjunction (S.levelInclusion n)).homEquiv _ _).symm (π n)),
    fun n => derivedPullbackCompIso_hom_app_comp_homEquiv_symm _ _ _ _ (S.φ n) (π (n + 1)) (π n)
      (hπ n)⟩

end DerivedExistenceSituation

end AlgebraicGeometry.GrothendieckExistence
