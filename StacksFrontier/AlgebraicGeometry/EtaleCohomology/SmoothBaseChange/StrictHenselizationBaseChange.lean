module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationConeBase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationSize
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.BaseChangeTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictlyHenselianStrictHenselization

/-!
# Base change to the strict henselization of the base

Let `f : X ⟶ S` be a morphism of schemes of a big étale site, `x` a geometric point of `X` and
`S₁ = Spec 𝒪^{sh}_{S,f(x)}` the strict henselization of `S` at the image of `x`. The proof of
Proposition 0GJQ replaces `f` by its base change `X₁ = X ×_S S₁ ⟶ S₁` at the geometric point `x₁`
of `X₁` determined by `x` and the canonical geometric point of `S₁`. This file records that base
change and the square of étale local rings at `x₁`, which is a pushout: `S₁` is the limit of the
affine étale neighbourhoods of `f(x)` (Stacks 0GIP (2)).

## Main definitions

* `Stacks.EtaleCohomology.SmoothBaseChange.strictHenselizationBaseChangePoint` — the geometric
  point `x₁` of `X ×_S S₁`.

## Main results

* `Stacks.EtaleCohomology.SmoothBaseChange.isPushout_strictHenselizationBaseChange` — the square
  of étale local rings at `x₁` is a pushout.

## References

* [Stacks Project, Tag 0GJQ](https://stacks.math.columbia.edu/tag/0GJQ)
* [Stacks Project, Tag 0GIP](https://stacks.math.columbia.edu/tag/0GIP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (x : GeometricPoint X)

/-- **The geometric point of `X ×_S Spec 𝒪^{sh}_{S,f(x)}` determined by `x`** and the canonical
geometric point of the strict henselization. -/
def strictHenselizationBaseChangePoint :
    GeometricPoint (pullback f (strictHenselizationToBase B S hS (x.map f))) :=
  ⟨x.residueField, pullback.lift x.hom (geometricPointToStrictHenselization B S hS (x.map f))
    (geometricPointToStrictHenselization_comp B S hS (x.map f)).symm⟩

include hX in
/-- The base change `X ×_S Spec 𝒪^{sh}_{S,f(x)}` is contained in the big étale site. -/
theorem contains_strictHenselizationBaseChange :
    B.Contains (pullback f (strictHenselizationToBase B S hS (x.map f))) :=
  Scheme.size_pullback_lt _ _ hX (contains_strictHenselization B S hS (x.map f))

/-- **The square of étale local rings of the base change to the strict henselization is a
pushout** (Stacks 0GIP (2)): `Spec 𝒪^{sh}_{S,f(x)}` is the limit of the affine étale
neighbourhoods of `f(x)`, which are étale, hence locally of finite type and locally
quasi-finite, over `S`, with affine transition morphisms. -/
theorem isPushout_strictHenselizationBaseChange :
    IsPushout (CommRingCat.ofHom (baseChangeEtaleLocalRingHom B hS
        (contains_strictHenselization B S hS (x.map f))
        (IsPullback.of_hasPullback f (strictHenselizationToBase B S hS (x.map f)))
        (strictHenselizationBaseChangePoint B hS f x)))
      (CommRingCat.ofHom (etaleLocalRingHom B hX hS f
        ((strictHenselizationBaseChangePoint B hS f x).map (pullback.fst _ _))))
      (CommRingCat.ofHom (etaleLocalRingHom B (contains_strictHenselizationBaseChange B hX hS f x)
        (contains_strictHenselization B S hS (x.map f)) (pullback.snd _ _)
        (strictHenselizationBaseChangePoint B hS f x)))
      (CommRingCat.ofHom (etaleLocalRingHom B (contains_strictHenselizationBaseChange B hX hS f x)
        hX (pullback.fst _ _) (strictHenselizationBaseChangePoint B hS f x))) := by
  let s := x.map f
  let p : ∀ a : etaleNeighborhoodAffineIndex B S hS s,
      (etaleNeighborhoodAffineDiagram B S hS s).obj a ⟶ S :=
    fun a => B.inclusion.map ((etaleNeighborhoodAffineInclusion B S hS s).obj a).1.obj.hom
  have : ∀ a, LocallyOfFiniteType (p a) := fun a => inferInstance
  have : ∀ a, LocallyQuasiFinite (p a) := fun a => (locallyQuasiFinite_of_etale (p a)).2
  exact isPushout_etaleLocalRingHom_of_limit B hX hS
    (strictHenselizationAffineConeIsLimit B S hS s)
    (contains_strictHenselization B S hS s) (contains_strictHenselizationBaseChange B hX hS f x)
    (IsPullback.of_hasPullback f (strictHenselizationToBase B S hS s)) p
    (strictHenselizationAffineCone_π_comp_hom_eq B S hS s)
    (fun {i j} a => (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map
      ((etaleNeighborhoodAffineInclusion B S hS s).map a).1.hom.w))
    (strictHenselizationBaseChangePoint B hS f x)

/-! ### The strict henselizations of the base agree -/

section Iso

variable {B} {hS}

/-- Transport of strict henselizations along an equality of geometric points lies over the
base. -/
theorem eqToHom_strictHenselizationToBase {a b : GeometricPoint S} (e : a = b) :
    eqToHom (congrArg (strictHenselization B S hS) e) ≫ strictHenselizationToBase B S hS b =
      strictHenselizationToBase B S hS a := by
  subst e
  simp

/-- Transport of strict henselizations along an equality of geometric points carries the
canonical geometric point to the canonical geometric point. -/
theorem geometricPointToStrictHenselization_eqToHom {a b : GeometricPoint S} (e : a = b) :
    geometricPointToStrictHenselization B S hS a ≫
        eqToHom (congrArg (strictHenselization B S hS) e) =
      eqToHom (by rw [e]) ≫ geometricPointToStrictHenselization B S hS b := by
  subst e
  simp

/-- Invertibility of the spectrum of a transported homomorphism of étale local rings does not
depend on the transport. -/
theorem isIso_SpecMap_etaleLocalRingHomCongr_iff {T : Type u} [CommRing T]
    {a b : GeometricPoint S} (e : a = b) (φ : ↥(etaleLocalRing B S hS a) →+* T) :
    IsIso (Spec.map (CommRingCat.ofHom (etaleLocalRingHomCongr B hS e φ))) ↔
      IsIso (Spec.map (CommRingCat.ofHom φ)) := by
  subst e
  rfl

end Iso

/-- **The strict henselization of the base change at `x₁` is the strict henselization of the base
at `f(x)`.** The induced morphism of strict henselizations of the bases is an isomorphism. -/
theorem isIso_baseChangeStrictHenselizationMap :
    IsIso (baseChangeStrictHenselizationMap B hS (contains_strictHenselization B S hS (x.map f))
      (IsPullback.of_hasPullback f (strictHenselizationToBase B S hS (x.map f)))
      (strictHenselizationBaseChangePoint B hS f x)) := by
  let s := x.map f
  let π := strictHenselizationToBase B S hS s
  let hS₁ := contains_strictHenselization B S hS s
  let σ := (strictHenselizationBaseChangePoint B hS f x).map (pullback.snd f π)
  have hσ : σ.hom = geometricPointToStrictHenselization B S hS s := pullback.lift_snd _ _ _
  have e : σ.map π = s :=
    congrArg (fun m : Spec (.of x.residueField) ⟶ S => GeometricPoint.mk x.residueField m)
      (hσ ▸ geometricPointToStrictHenselization_comp B S hS s)
  have hθ : IsIso (strictHenselizationToBase B _ hS₁ σ) := by
    refine isIso_strictHenselizationToBase_of_strictlyHenselian B _ hS₁ σ ?_
    show σ.hom default = _
    rw [hσ]
    exact geometricPointToStrictHenselization_base_default B S hS s
  have hsq : strictHenselizationSquareMap B hS₁ hS π σ =
      strictHenselizationToBase B _ hS₁ σ ≫
        eqToHom (congrArg (strictHenselization B S hS) e.symm) := by
    refine (existsUnique_strictHenselizationSquareMap B hS₁ hS π σ).unique
      ⟨strictHenselizationSquareMap_comp B hS₁ hS π σ,
        geometricPointToStrictHenselization_strictHenselizationSquareMap B hS₁ hS π σ⟩ ⟨?_, ?_⟩
    · rw [Category.assoc, eqToHom_strictHenselizationToBase e.symm]
    · rw [← Category.assoc, geometricPointToStrictHenselization_comp, hσ]
      exact (geometricPointToStrictHenselization_eqToHom (B := B) (hS := hS) e.symm).trans
        ((congrArg (· ≫ geometricPointToStrictHenselization B S hS (σ.map π))
          (eqToHom_refl _ _)).trans (Category.id_comp _))
  have : IsIso (strictHenselizationSquareMap B hS₁ hS π σ) := by
    rw [hsq]
    infer_instance
  exact (isIso_SpecMap_etaleLocalRingHomCongr_iff _ _).2 this

end Stacks.EtaleCohomology.SmoothBaseChange

end
