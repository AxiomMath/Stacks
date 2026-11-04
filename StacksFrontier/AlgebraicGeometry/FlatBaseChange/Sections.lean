module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic

/-!
# Flat base change preserves finiteness of the sections over a qcqs open

Let `φ : A ⟶ B` be a flat ring map and `V` an open of `Spec A` whose underlying scheme is
quasi-compact and quasi-separated. Then

  `Module.Finite A Γ(Spec A, V) → Module.Finite B Γ(Spec B, Spec.map φ ⁻¹ᵁ V)`.

This is a degree-zero consequence of [Stacks, Tag 02KH].

## Main results

* `Stacks.AlgebraicGeometry.FlatBaseChange.module_finite_of_ringEquiv`: finiteness of a module
  transports along a ring isomorphism and a compatible additive isomorphism.
* `Stacks.AlgebraicGeometry.FlatBaseChange.topIso_hom_appLE_top_apply`: the restriction of scalars
  along `V.ι.appLE ⊤ ⊤`, read through `AlgebraicGeometry.Scheme.Opens.topIso`, is the canonical
  `R`-algebra structure of `Γ(Spec R, V)`.
* `Stacks.AlgebraicGeometry.FlatBaseChange.module_finite_baseModule_iff`: for a module on
  `V.toScheme` isomorphic to the structure sheaf, the finiteness of its global sections over the
  scalars of [Stacks, Tag 02KH] is the finiteness of `Γ(Spec R, V)` over `R`.
* `Stacks.AlgebraicGeometry.FlatBaseChange.module_finite_sections_preimage_of_flat`: flat base
  change preserves finiteness of the sections over a qcqs open.

## Implementation notes

* The scalar structures of [Stacks, Tag 02KH] are restrictions of scalars along
  `AlgebraicGeometry.Scheme.Hom.appLE ⊤ ⊤` and are not instances. The module structures of
  `module_finite_baseModule_iff` and `module_finite_of_ringEquiv` are therefore *explicit*
  arguments, so that no rewriting happens underneath an instance argument.
* The site functor `TopologicalSpace.Opens.map ψ.base` of a morphism of schemes is
  `CategoryTheory.Functor.Final`, and
  `(SheafOfModules.pushforward ψ.toRingCatSheafHom).IsRightAdjoint` holds by
  `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`; neither is found by instance
  search at the spelling `SheafOfModules.pullbackObjUnitToUnit` needs, so both are restated here.

## References

* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.SectionsBaseChange
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.FlatBaseChange

/-! ### Transporting finiteness along a ring isomorphism -/

/-- **Finiteness transports along a ring isomorphism.** If `eR : R ≃+* R'` and `eM : M ≃+ M'`
satisfy `eM (r • x) = eR r • eM x`, then `M'` is a finite `R'`-module as soon as `M` is a finite
`R`-module. -/
theorem module_finite_of_ringEquiv {R R' M M' : Type u} [CommRing R] [CommRing R']
    [AddCommGroup M] [AddCommGroup M'] (iM : Module R M) (iM' : Module R' M')
    (eR : R ≃+* R') (eM : M ≃+ M')
    (h : letI := iM; letI := iM'; ∀ (r : R) (x : M), eM (r • x) = eR r • eM x)
    (hfin : letI := iM; Module.Finite R M) :
    letI := iM'; Module.Finite R' M' := by
  let := iM
  let := iM'
  classical
  obtain ⟨s, hs⟩ := hfin.fg_top
  refine ⟨⟨s.image eM, eq_top_iff.mpr ?_⟩⟩
  have key : ∀ x ∈ Submodule.span R (s : Set M),
      eM x ∈ Submodule.span R' ((s.image eM : Finset M') : Set M') := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem u hu => exact Submodule.subset_span (by simpa using Set.mem_image_of_mem eM hu)
    | zero => simpa only [map_zero] using Submodule.zero_mem _
    | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
    | smul r a _ ha => simpa only [h r a] using Submodule.smul_mem _ _ ha
  intro y _
  have hy : eM.symm y ∈ Submodule.span R (s : Set M) := by rw [hs]; trivial
  simpa only [AddEquiv.apply_symm_apply] using key _ hy

/-! ### The scalar structure on the sections over an open of an affine scheme -/

/-- **Restricting a global function to an open is `appLE` followed by `topIso`.** For an open `V`
of a scheme `X`, the map `Γ(X, ⊤) ⟶ Γ(V.toScheme, ⊤)` induced by `V.ι`, followed by the
identification `AlgebraicGeometry.Scheme.Opens.topIso` of `Γ(V.toScheme, ⊤)` with `Γ(X, V)`, is
restriction along `V ≤ ⊤`. -/
theorem appLE_top_topIso_hom {X : Scheme.{u}} (V : X.Opens) :
    V.ι.appLE ⊤ ⊤ (le_preimage_top V.ι ⊤) ≫ V.topIso.hom = X.presheaf.map V.leTop.op := by
  rw [show V.ι.appLE ⊤ ⊤ (le_preimage_top V.ι ⊤) = V.ι.app ⊤ from
    Scheme.Hom.appLE_eq_app V.ι]
  exact (X.presheaf.map_comp _ _).symm

/-- **The scalars of [Stacks, Tag 02KH] on the sections over an open of an affine scheme are
`algebraMap`.** For `V` an open of `Spec R`, the restriction of scalars along `V.ι.appLE ⊤ ⊤`,
read through `AlgebraicGeometry.Scheme.Opens.topIso`, is the canonical `R`-algebra structure of
`Γ(Spec R, V)`. -/
theorem topIso_hom_appLE_top_apply (R : CommRingCat.{u}) (V : (Spec R).Opens)
    (r : ToType Γ(Spec R, (⊤ : (Spec R).Opens))) :
    V.topIso.hom ((V.ι.appLE ⊤ ⊤ (le_preimage_top V.ι ⊤)).hom r) =
      algebraMap R Γ(Spec R, V) ((Scheme.ΓSpecIso R).hom r) := by
  have h := ConcreteCategory.congr_hom (appLE_top_topIso_hom (X := Spec R) V) r
  have h' := ConcreteCategory.congr_hom (Scheme.ΓSpecIso R).hom_inv_id r
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_id, RingHom.coe_id, id_eq] at h h'
  rw [h, IsAffineOpen.algebraMap_Spec_obj]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [h']
  rfl

/-- **The scalars of [Stacks, Tag 02KH] see the same finiteness.** Let `V` be an open of `Spec R`
and `G` a module on `V.toScheme` isomorphic to the structure sheaf. Then `Γ(G, ⊤)` is a finite
module for the `Γ(Spec R, ⊤)`-structure of [Stacks, Tag 02KH] — restriction of scalars along
`V.ι.appLE ⊤ ⊤` — exactly when `Γ(Spec R, V)` is a finite `R`-module. -/
theorem module_finite_baseModule_iff {R : CommRingCat.{u}} (V : (Spec R).Opens)
    (G : V.toScheme.Modules) (iso : G ≅ SheafOfModules.unit.{u} V.toScheme.ringCatSheaf) :
    @Module.Finite _ _ _ _ (baseModule V.ι G ⊤) ↔
      Module.Finite (ToType R) Γ(Spec R, V) := by
  let iG : Module Γ(Spec R, (⊤ : (Spec R).Opens)) Γ(G, (⊤ : V.toScheme.Opens)) :=
    baseModule V.ι G ⊤
  let e1 : Γ(G, (⊤ : V.toScheme.Opens)) ≃ₗ[Γ(V.toScheme, (⊤ : V.toScheme.Opens))]
      ToType Γ(V.toScheme, (⊤ : V.toScheme.Opens)) :=
    AlgebraicGeometry.sectionsLinearEquivOfIso iso ⊤
  let ee : Γ(G, (⊤ : V.toScheme.Opens)) ≃+ ToType Γ(Spec R, V) :=
    e1.toAddEquiv.trans V.topIso.commRingCatIsoToRingEquiv.toAddEquiv
  have hsm : ∀ (r : ToType Γ(Spec R, (⊤ : (Spec R).Opens))) (x : Γ(G, (⊤ : V.toScheme.Opens))),
      ee (r • x) = (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv r • ee x := by
    intro r x
    rw [Algebra.smul_def]
    show V.topIso.hom.hom (e1 ((V.ι.appLE ⊤ ⊤ (le_preimage_top V.ι ⊤)).hom r • x)) =
      algebraMap (ToType R) Γ(Spec R, V) ((Scheme.ΓSpecIso R).hom.hom r) *
        V.topIso.hom.hom (e1 x)
    rw [map_smul, smul_eq_mul, map_mul, topIso_hom_appLE_top_apply]
  refine ⟨fun h => module_finite_of_ringEquiv iG _
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv ee hsm h, fun h => ?_⟩
  refine module_finite_of_ringEquiv _ iG
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm ee.symm ?_ h
  intro r y
  refine ee.injective ?_
  rw [AddEquiv.apply_symm_apply, hsm, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-! ### The pullback of the structure sheaf -/

/-- The direct image functor on sheaves of modules along a morphism of schemes is a right
adjoint. -/
instance isRightAdjoint_pushforward_toRingCatSheafHom {Y Z : Scheme.{u}} (ψ : Y ⟶ Z) :
    (SheafOfModules.pushforward.{u} ψ.toRingCatSheafHom).IsRightAdjoint :=
  (Scheme.Modules.pullbackPushforwardAdjunction ψ).isRightAdjoint

/-- The canonical comparison out of the pullback of the structure sheaf is an isomorphism, for any
morphism of schemes. -/
instance isIso_pullbackObjUnitToUnit {Y Z : Scheme.{u}} (ψ : Y ⟶ Z) :
    IsIso (SheafOfModules.pullbackObjUnitToUnit ψ.toRingCatSheafHom) :=
  letI : (Opens.map ψ.base).Final := final_of_representablyFlat _
  SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _

/-! ### Quasi-compactness and quasi-separatedness of an open of a Noetherian scheme -/

/-- **An open subscheme of a scheme with Noetherian underlying space has Noetherian underlying
space.** -/
theorem noetherianSpace_opens {X : Scheme.{u}} [NoetherianSpace X] (V : X.Opens) :
    NoetherianSpace V.toScheme :=
  NoetherianSpace.set (V : Set X)

/-! ### Flat base change of the sections over a qcqs open -/

/-- **Flat base change preserves finiteness of the sections over a qcqs open.** Let `φ : A ⟶ B` be
a flat ring map and `V` an open of `Spec A` whose underlying scheme is quasi-compact and
quasi-separated. If `Γ(Spec A, V)` is a finite `A`-module then `Γ(Spec B, Spec.map φ ⁻¹ᵁ V)` is a
finite `B`-module. -/
theorem module_finite_sections_preimage_of_flat {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (hφ : φ.hom.Flat) (V : (Spec A).Opens)
    [CompactSpace V.toScheme] [QuasiSeparatedSpace V.toScheme]
    (hfin : Module.Finite (ToType A) Γ(Spec A, V)) :
    Module.Finite (ToType B) Γ(Spec B, Spec.map φ ⁻¹ᵁ V) := by
  have : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hφ
  have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit V.toScheme
  let : Algebra Γ(Spec A, (⊤ : (Spec A).Opens)) Γ(Spec B, (⊤ : (Spec B).Opens)) :=
    baseAlgebra (Spec.map φ)
  let : Module Γ(Spec A, (⊤ : (Spec A).Opens))
      Γ(SheafOfModules.unit.{u} V.toScheme.ringCatSheaf, (⊤ : V.toScheme.Opens)) :=
    baseModule V.ι (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf) ⊤
  let : Module Γ(Spec B, (⊤ : (Spec B).Opens))
      Γ((Scheme.Modules.pullback (Spec.map φ ∣_ V)).obj
          (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf),
        (⊤ : (Spec.map φ ⁻¹ᵁ V).toScheme.Opens)) :=
    baseModule (Spec.map φ ⁻¹ᵁ V).ι
      ((Scheme.Modules.pullback (Spec.map φ ∣_ V)).obj
        (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf)) ⊤
  have := (module_finite_baseModule_iff V
    (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf) (Iso.refl _)).mpr hfin
  obtain ⟨e, -⟩ := exists_linearEquiv_sections_baseChange
    (AlgebraicGeometry.isPullback_morphismRestrict (Spec.map φ) V)
    (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf)
  exact (module_finite_baseModule_iff (Spec.map φ ⁻¹ᵁ V)
    ((Scheme.Modules.pullback (Spec.map φ ∣_ V)).obj
      (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf))
    (Scheme.Modules.pullbackUnitIso (Spec.map φ ∣_ V))).mp (Module.Finite.equiv e)

end Stacks.AlgebraicGeometry.FlatBaseChange

end
