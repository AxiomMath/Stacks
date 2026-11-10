module

public import StacksFrontier.RingTheory.Dualizing.LocalizationTransport
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModule
public import StacksFrontier.RingTheory.Dualizing.QuotientExtConcentration

/-!
# Dualizing modules along an isomorphism of rings

* `Stacks.Duality.isDualizingRingModule_of_ringEquiv`: if `σ : C ≃+* C'` and `g : M ≃+ M'` is
  `σ`-semilinear, a dualizing `C`-module `M` gives a dualizing `C'`-module `M'`.
* `Stacks.Duality.isDualizingRingModule_map_ringEquiv`: for `φ : B →+* C` and an ideal `J ⊆ B`,
  if `J·C` is a dualizing `C`-module then `J·C'` is a dualizing `C'`-module, `C'` being `C` along
  `σ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

/-- **A dualizing module stays dualizing along a semilinear isomorphism over a ring
isomorphism.** -/
theorem isDualizingRingModule_of_ringEquiv {C C' : Type u} [CommRing C] [CommRing C']
    [IsNoetherianRing C] [IsNoetherianRing C'] (σ : C ≃+* C') (M M' : Type u) [AddCommGroup M]
    [Module C M] [AddCommGroup M'] [Module C' M'] (g : M ≃+ M')
    (hg : ∀ (c : C) (m : M), g (c • m) = σ c • g m) (h : IsDualizingRingModule C M) :
    IsDualizingRingModule C' M' := by
  obtain ⟨hfin, n, hn⟩ := h
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ.symm
  let F := ModuleCat.extendScalars.{u, u, u} (σ : C →+* C')
  have he : σ.symm.symm.toRingHom = (σ : C →+* C') := rfl
  let r : E.inverse ≅ ModuleCat.restrictScalars (σ : C →+* C') :=
    eqToIso (congrArg ModuleCat.restrictScalars he)
  let t : E.functor ≅ F := Adjunction.leftAdjointUniq
    (E.toAdjunction.ofNatIsoRight r) (ModuleCat.extendRestrictScalarsAdj _)
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_natIso t
  -- the semilinear isomorphism as a `C'`-linear isomorphism out of the restricted module
  let gl : (E.functor.obj (ModuleCat.of C M)) ≃ₗ[C'] M' :=
    { g with
      map_smul' := fun c' m => by
        change g (σ.symm c' • (show M from m)) = c' • g m
        rw [hg, RingEquiv.apply_symm_apply] }
  refine ⟨?_, n, ?_⟩
  · classical
    obtain ⟨S, hS⟩ := hfin.fg_top
    refine ⟨⟨S.image g, eq_top_iff.2 fun m' _ => ?_⟩⟩
    have key : ∀ m ∈ Submodule.span C (S : Set M),
        g m ∈ Submodule.span C' ((S.image g : Finset M') : Set M') := by
      intro m hm
      induction hm using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem g hx))
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul c x _ hx => rw [hg]; exact Submodule.smul_mem _ _ hx
    simpa using key (g.symm m') (by rw [hS]; trivial)
  · have h₁ := Dualizing.isDualizingComplex_of_ringEquiv σ _ hn
    have h₂ := (Dualizing.isDualizingComplex_iff_of_iso
      ((Dualizing.mapDerivedCategoryNatIso E.functor F t).app _).symm).1 h₁
    exact (Dualizing.isDualizingComplex_iff_of_iso
      (((E.functor.mapDerivedCategorySingleFunctor n).app (ModuleCat.of C M)) ≪≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} C') n).mapIso gl.toModuleIso)).1 h₂

/-- **The extension of an ideal stays dualizing along a ring isomorphism.** -/
theorem isDualizingRingModule_map_ringEquiv {B C C' : Type u} [CommRing B] [CommRing C]
    [CommRing C'] [IsNoetherianRing C] [IsNoetherianRing C'] (φ : B →+* C) (σ : C ≃+* C')
    (J : Ideal B) (h : IsDualizingRingModule C (J.map φ)) :
    IsDualizingRingModule C' (J.map ((σ : C →+* C').comp φ)) := by
  have hmap : J.map ((σ : C →+* C').comp φ) = (J.map φ).map (σ : C →+* C') := by
    rw [Ideal.map_map]
  have hmem : ∀ x : C, x ∈ J.map φ ↔ σ x ∈ J.map ((σ : C →+* C').comp φ) := fun x => by
    rw [hmap, Ideal.map_comap_of_equiv, Ideal.mem_comap]
    simp
  let g : (J.map φ) ≃+ (J.map ((σ : C →+* C').comp φ)) :=
    { toFun := fun x => ⟨σ x, (hmem x).1 x.2⟩
      invFun := fun y => ⟨σ.symm y, (hmem _).2 (by simp)⟩
      left_inv := fun x => Subtype.ext (σ.symm_apply_apply (x : C))
      right_inv := fun y => Subtype.ext (σ.apply_symm_apply (y : C'))
      map_add' := fun x y => Subtype.ext (map_add σ (x : C) y) }
  exact isDualizingRingModule_of_ringEquiv σ _ _ g
    (fun c m => Subtype.ext (map_mul σ c (m : C))) h

end Stacks.Duality
