module

public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.DescentDatumMap

/-!
# Effectivity of descent transports along an equivalence over the base

Given an equivalence `e : BasedCategory.Equivalence 𝒳 𝒴` of fibred categories over `𝒞`, this
file proves that if every descent datum in `𝒳` relative to a covering sieve is effective
(condition (3) of Stacks 026F), then so is every descent datum in `𝒴`.

## Main results

* `CategoryTheory.BasedCategory.Equivalence.hasEffectiveDescent`: Stacks 026F (3) transported along
  an equivalence over `𝒞`.
-/

@[expose] public section

-- The declarations below relate `p` and `𝒴.p` through `BasedFunctor.comp`, whose instance
-- arguments are only found after unfolding the composite.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

namespace BasedCategory.Equivalence

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒞} {𝒴 : BasedCategory.{v₃, u₃} 𝒞}
  (e : BasedCategory.Equivalence 𝒳 𝒴)

-- Every declaration below is a statement about `e`, but several mention it only in their proofs.
include e

open _root_.CategoryTheory.Functor

/-- The component of the inverse of the counit at `y`, a morphism `y ⟶ F (G y)` lying over an
identity. -/
noncomputable abbrev counitInv (y : 𝒴.obj) : y ⟶ e.functor.obj (e.inverse.obj y) :=
  e.counitIso.inv.toNatTrans.app y

/-- The inverse of the counit of an equivalence over `𝒞` has components lying over identities. -/
instance isHomLift_counitInv (y : 𝒴.obj) : 𝒴.p.IsHomLift (𝟙 (𝒴.p.obj y)) (e.counitInv y) :=
  e.counitIso.inv.app_isHomLift y

/-- Each component of the inverse of the counit of an equivalence over `𝒞` is an isomorphism. -/
instance isIso_counitInv (y : 𝒴.obj) : IsIso (e.counitInv y) := by
  refine ⟨e.counitIso.hom.toNatTrans.app y, ?_, ?_⟩
  · change (e.counitIso.inv ≫ e.counitIso.hom).toNatTrans.app y = _
    rw [e.counitIso.inv_hom_id]; rfl
  · change (e.counitIso.hom ≫ e.counitIso.inv).toNatTrans.app y = _
    rw [e.counitIso.hom_inv_id]; rfl

/-- Naturality of the inverse of the counit. -/
lemma counitInv_naturality {y y' : 𝒴.obj} (m : y ⟶ y') :
    m ≫ e.counitInv y' = e.counitInv y ≫ e.functor.map (e.inverse.map m) :=
  e.counitIso.inv.toNatTrans.naturality m

/-- **Stacks 026F (3) transports along an equivalence over `𝒞`.** If every descent datum in `𝒳`
relative to a covering sieve of `J` is effective, then so is every descent datum in `𝒴`. -/
theorem hasEffectiveDescent [𝒳.p.IsFibered] [𝒴.p.IsFibered] (J : GrothendieckTopology 𝒞)
    (h : HasEffectiveDescent 𝒳.p J) : HasEffectiveDescent 𝒴.p J := by
  intro U R hR D
  obtain ⟨x, ζ, hζcart, hglue⟩ := h R hR (SieveDescentDatum.mapEquiv e.symm D)
  refine ⟨e.fiberMap x, fun V f hf => e.counitInv (D.obj f hf).1 ≫ e.functor.map (ζ f hf), ?_, ?_⟩
  · intro V f hf
    have := hζcart f hf
    have : 𝒳.p.IsStronglyCartesian f (ζ f hf) := inferInstance
    have := e.isStronglyCartesian_map f (ζ f hf)
    have : 𝒴.p.IsHomLift (𝟙 V) (e.counitInv (D.obj f hf).1) := by
      have h0 := e.isHomLift_counitInv (D.obj f hf).1
      rwa [(D.obj f hf).2] at h0
    have : 𝒴.p.IsStronglyCartesian (𝟙 V) (e.counitInv (D.obj f hf).1) :=
      IsStronglyCartesian.of_isIso 𝒴.p (𝟙 V) _
    have hcomp : 𝒴.p.IsStronglyCartesian (𝟙 V ≫ f)
        (e.counitInv (D.obj f hf).1 ≫ e.functor.map (ζ f hf)) := IsStronglyCartesian.comp 𝒴.p
    rw [Category.id_comp] at hcomp
    exact inferInstance
  · intro V W Z f hf g hg ε ε' heq
    have hg' := (e.symm.pullbackFiberFunctorIso (D.obj f hf) ε).hom ≫= hglue hf hg ε ε' heq
    simp only [SieveDescentDatum.mapEquiv_iso, SieveDescentDatum.mapEquiv_obj, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
      fiberInclusion_map_pullbackFiberFunctorFiberIso_hom,
      fiberInclusion_map_pullbackFiberFunctorFiberIso_inv, fiberInclusion_map_fiberMapFunctor_map,
      Iso.hom_inv_id_assoc, symm_functor, pullbackFiberFunctorIso_hom_fac_assoc] at hg'
    calc Functor.Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom ≫
            IsPreFibered.pullbackMap (D.obj g hg).2 ε' ≫
            (e.counitInv (D.obj g hg).1 ≫ e.functor.map (ζ g hg))
        = (Functor.Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom ≫
            IsPreFibered.pullbackMap (D.obj g hg).2 ε' ≫
            e.counitInv (D.obj g hg).1) ≫ e.functor.map (ζ g hg) := by
          simp [Category.assoc]
      _ = (e.counitInv (Functor.pullbackFiber 𝒴.p (D.obj f hf) ε).1 ≫
            e.functor.map (e.inverse.map (Functor.Fiber.fiberInclusion.map
              (D.iso hf hg ε ε' heq).hom ≫
              IsPreFibered.pullbackMap (D.obj g hg).2 ε'))) ≫ e.functor.map (ζ g hg) := by
          rw [← Category.assoc, e.counitInv_naturality]
          rfl
      _ = e.counitInv (Functor.pullbackFiber 𝒴.p (D.obj f hf) ε).1 ≫
            e.functor.map (e.inverse.map (Functor.Fiber.fiberInclusion.map
              (D.iso hf hg ε ε' heq).hom ≫
              IsPreFibered.pullbackMap (D.obj g hg).2 ε') ≫ ζ g hg) := by
          rw [Category.assoc, ← Functor.map_comp]
      _ = e.counitInv (Functor.pullbackFiber 𝒴.p (D.obj f hf) ε).1 ≫
            e.functor.map (e.inverse.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε) ≫
              ζ f hf) := by
          congr 2
          rw [Functor.map_comp, Category.assoc]
          exact hg'
      _ = IsPreFibered.pullbackMap (D.obj f hf).2 ε ≫
            (e.counitInv (D.obj f hf).1 ≫ e.functor.map (ζ f hf)) := by
          rw [Functor.map_comp, ← Category.assoc, ← e.counitInv_naturality]
          simp [Category.assoc]

end BasedCategory.Equivalence

end CategoryTheory
