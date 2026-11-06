module

public import StacksFrontier.Homology.RelativelyPerfect.Colimit.FiniteDescent
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.ExtensionScalars
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.RingColimit
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.FiniteDescent

/-!
# Descent of bounded flat complexes

Filtered colimits of tensor products, descent of bounded complexes of flat finitely presented
modules to a stage, and the derived base change comparison for flat and Tor independent
inputs.

This is part 4 of 10 of `StacksFrontier.Homology.RelativelyPerfect.Colimit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject
open CochainComplex.DerivedExtensionScalars
open StacksDraft.TorAmplitude
open scoped TensorProduct

open Stacks.HomologyColimit

namespace PseudoCoherence

open StacksDraft.RelativelyPerfect (finite_homCochain_support homCochainBaseChange
    homCochainBaseChange_bijective homCochainBaseChange_tmul homCochainExtendScalars
    homCochainRestrict homComplexBaseChange linearMap_isBaseChange_of_finiteFree)

universe uI uJ uR uA uM

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] CochainComplex.DerivedTensor.instAdditiveModuleCatExtensionScalars
  CochainComplex.DerivedTensor.instIsLeftAdjointModuleCatExtensionScalars

section TensorColimits

universe u v w

private def tensorModuleFunctor {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    CommAlgCat.{w} R ⥤ ModuleCat.{max w v} R where
  obj S := ModuleCat.of R (S ⊗[R] M)
  map f := ModuleCat.ofHom (LinearMap.rTensor M f.hom.toLinearMap)
  map_id S := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext s m
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext s m
    rfl

set_option backward.isDefEq.respectTransparency false in
private def isColimit_tensorModuleFunctor_of_isColimit_forget {R : Type u} [CommRing R]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    {F : I ⥤ CommAlgCat.{w} R} {c : Cocone F}
    (hc : IsColimit ((forget (CommAlgCat.{w} R)).mapCocone c))
    (M : Type v) [AddCommGroup M] [Module R M] :
    IsColimit (((tensorModuleFunctor M) ⋙ forget _).mapCocone c) := by
  classical
  apply Classical.choice
  obtain ⟨J, _, _, _, G, _⟩ := exists_directed_final I
  suffices h : Nonempty (IsColimit ((((tensorModuleFunctor M) ⋙
    forget _).mapCocone c).whisker G)) by
    exact ⟨(Functor.Final.isColimitWhiskerEquiv G _) h.some⟩
  have hG := (Functor.Final.isColimitWhiskerEquiv G _).symm hc
  let S : J → Type w := fun j ↦ F.obj (G.obj j)
  let f : ∀ i j : J, i ≤ j → S i →ₐ[R] S j :=
    fun i j h ↦ (F.map (G.map (homOfLE h))).hom
  let : ∀ j : J, Algebra (S j) c.pt := fun j ↦ (c.ι.app (G.obj j)).hom.toRingHom.toAlgebra
  let : ∀ j : J, IsScalarTower R (S j) c.pt := fun j ↦
    IsScalarTower.of_algebraMap_eq fun r ↦ ((c.ι.app (G.obj j)).hom.commutes r).symm
  have : DirectedSystem S fun i j h ↦ ⇑(f i j h) := by
    constructor
    · intro i x
      change (F.map (G.map (homOfLE (le_refl i)))).hom x = x
      simp
    · intro i j k hij hjk x
      change (F.map (G.map (homOfLE hjk))).hom ((F.map (G.map (homOfLE hij))).hom x) =
        (F.map (G.map (homOfLE (hij.trans hjk)))).hom x
      rw [← CommAlgCat.comp_apply, ← F.map_comp, ← G.map_comp]
      rfl
  have hf : ∀ (i j : J) (h : i ≤ j) (x : S i),
      algebraMap (S j) c.pt (f i j h x) = algebraMap (S i) c.pt x := by
    intro i j h x
    exact congrArg (fun a : F.obj (G.obj i) ⟶ c.pt ↦ a.hom x)
      (c.w (G.map (homOfLE h)))
  have hsurj : ∀ x : c.pt, ∃ j : J, ∃ y : S j, algebraMap (S j) c.pt y = x := by
    intro x
    obtain ⟨j, y, hy⟩ := Types.jointly_surjective _ hG x
    exact ⟨j, y, hy⟩
  have hinj : ∀ (j : J) (x : S j), algebraMap (S j) c.pt x = 0 →
      ∃ k : J, ∃ h : j ≤ k, f j k h x = 0 := by
    intro j x hx
    have hx' : (c.ι.app (G.obj j)).hom x = (c.ι.app (G.obj j)).hom (0 : S j) := by
      change (c.ι.app (G.obj j)).hom x = 0 at hx
      simpa only [map_zero] using hx
    obtain ⟨k, h, hh⟩ := (Types.FilteredColimit.isColimit_eq_iff' hG x (0 : S j)).mp hx'
    refine ⟨k, leOfHom h, ?_⟩
    change f j k (leOfHom h) x = f j k (leOfHom h) (0 : S j) at hh
    exact hh.trans (map_zero _)
  have hM := Stacks.ColimitPresentation.FPModules.isModuleColimit f hf hsurj hinj M
  refine ⟨Types.FilteredColimit.isColimitOf' _ _ ?_ ?_⟩
  · intro x
    obtain ⟨j, y, hy⟩ := hM.jointly_surjective x
    exact ⟨j, y, hy.symm⟩
  · intro j x y hxy
    obtain ⟨k, h, hh⟩ := hM.exists_eq_of_canonMod_eq j x y hxy
    exact ⟨k, homOfLE h, hh⟩

private def isColimit_tensorModuleFunctor {R : Type u} [CommRing R]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    {F : I ⥤ CommAlgCat.{u} R} {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, u, u} R).mapCocone c))
    (M : Type v) [AddCommGroup M] [Module R M] :
    IsColimit (((tensorModuleFunctor M) ⋙ forget _).mapCocone c) := by
  apply isColimit_tensorModuleFunctor_of_isColimit_forget (M := M)
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨i, y, hy⟩ := exists_stage_element hc x
    exact ⟨i, y, hy.symm⟩
  · intro i x y hxy
    exact (stage_elements_eq_iff' hc x y).mp hxy

end TensorColimits


/-- Base change along a tower of algebras preserves an equivariance relation of an equivalence. -/
private theorem baseChange_cancelBaseChange_equivariant {B₁ B₂ R M N : Type*}
    [CommRing B₁] [CommRing B₂] [CommRing R] [Algebra B₁ B₂] [Algebra B₁ R] [Algebra B₂ R]
    [IsScalarTower B₁ B₂ R] [AddCommGroup M] [Module B₁ M] [AddCommGroup N] [Module R N]
    (α : R ⊗[B₁] M ≃ₗ[R] N) (g : M →ₗ[B₁] M) (h : N →ₗ[R] N)
    (hα : ∀ x, α (g.baseChange R x) = h (α x)) (x : R ⊗[B₂] (B₂ ⊗[B₁] M)) :
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange B₁ B₂ R R M).trans α)
      ((g.baseChange B₂).baseChange R x) =
    h (((TensorProduct.AlgebraTensorModule.cancelBaseChange B₁ B₂ R R M).trans α) x) := by
  rw [LinearMap.baseChange_baseChange]
  simpa using hα (TensorProduct.AlgebraTensorModule.cancelBaseChange B₁ B₂ R R M x)

set_option synthInstance.maxHeartbeats 200000 in
-- the module structures on the stage tensor products are found through long scalar towers
private theorem exists_directed_stage_complex_operators {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I] {F : I ⥤ CommAlgCat.{uR} R₀}
    {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
    {K : Type*} [PartialOrder K] [IsDirectedOrder K] [Nonempty K] (G : K ⥤ I) [G.Final]
    (N : Type (max uR uA uM)) [AddCommGroup N] [Module (c.pt ⊗[R₀] A₀) N]
    [Module.FinitePresentation (c.pt ⊗[R₀] A₀) N]
    (s : Finset ℤ) (e : ℤ → N →ₗ[c.pt ⊗[R₀] A₀] N) (d : N →ₗ[c.pt ⊗[R₀] A₀] N)
    (hs : ∀ n ∉ s, e n = 0) (he : ∀ n, IsIdempotentElem (e n))
    (hd : ∀ n, d ∘ₗ e n = e (n + 1) ∘ₗ d) (hdd : d ∘ₗ d = 0) :
    ∃ (i : K) (M : Type (max uR uA uM)) (_ : AddCommGroup M)
      (_ : Module (stageAlgebra F A₀ (G.obj i)) M)
      (e' : ℤ → M →ₗ[stageAlgebra F A₀ (G.obj i)] M) (d' : M →ₗ[stageAlgebra F A₀ (G.obj i)] M),
      letI := (stageToLimitMap c A₀ (G.obj i)).toAlgebra
      Module.FinitePresentation (stageAlgebra F A₀ (G.obj i)) M ∧
      (∀ n ∉ s, e' n = 0) ∧ (∀ n, IsIdempotentElem (e' n)) ∧
      (∀ n, d' ∘ₗ e' n = e' (n + 1) ∘ₗ d') ∧ d' ∘ₗ d' = 0 ∧
      ∃ f : (c.pt ⊗[R₀] A₀) ⊗[stageAlgebra F A₀ (G.obj i)] M ≃ₗ[c.pt ⊗[R₀] A₀] N,
        (∀ n x, f ((e' n).baseChange (c.pt ⊗[R₀] A₀) x) = e n (f x)) ∧
        (∀ x, f (d'.baseChange (c.pt ⊗[R₀] A₀) x) = d (f x)) := by
  classical
  let R := c.pt ⊗[R₀] A₀
  let B := fun k : K ↦ stageAlgebra F A₀ (G.obj k)
  obtain ⟨k, Mk, _, _, hMk, ⟨αk⟩⟩ :=
    exists_directed_stage_finitePresentation_baseChange hc A₀ G N
  let : Algebra (B k) R := (stageToLimitMap c A₀ (G.obj k)).toAlgebra
  let := hMk
  let M := ULift.{uM} Mk
  let : Module.FinitePresentation (B k) M :=
    Module.FinitePresentation.of_equiv (ULift.moduleEquiv : M ≃ₗ[B k] Mk).symm
  let α : R ⊗[B k] M ≃ₗ[R] N :=
    (LinearEquiv.baseChange (B k) R M Mk ULift.moduleEquiv).trans αk
  let T := Option ↥s
  let φ : T → N →ₗ[R] N
    | none => d
    | some n => e n
  let := fun l : {l : K // k ≤ l} ↦
    (stageDirectedMap F A₀ G k l.1 l.2).toRingHom.toAlgebra
  let := fun l : {l : K // k ≤ l} ↦ (stageToLimitMap c A₀ (G.obj l.1)).toAlgebra
  obtain ⟨htower, hmap, -⟩ :=
    stage_above_finitePresentation_baseChange hc A₀ G k
  let := htower
  obtain ⟨l, ψ, hψ⟩ := exists_endomorphism_family_baseChange (hmap M (T → M)) α φ
  let Ml := B l.1 ⊗[B k] M
  let αl : R ⊗[B l.1] Ml ≃ₗ[R] N :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (B k) (B l.1) R R M).trans α
  let el : ℤ → Ml →ₗ[B l.1] Ml := fun n ↦ if hn : n ∈ s then ψ (some ⟨n, hn⟩) else 0
  let dl : Ml →ₗ[B l.1] Ml := ψ none
  have hel : ∀ n, (el n).baseChange R = αl.symm.conj (e n) := by
    intro n
    by_cases hn : n ∈ s
    · simpa [el, hn, αl, φ] using hψ (some ⟨n, hn⟩)
    · simp [el, hn, hs n hn]
  have hdl : dl.baseChange R = αl.symm.conj d := hψ none
  have hsel : ∀ n ∉ s, el n = 0 := fun n hn ↦ by simp [el, hn]
  have hel' : ∀ n, IsIdempotentElem ((el n).baseChange R) := by
    intro n
    rw [hel]
    show αl.symm.conj (e n) ∘ₗ αl.symm.conj (e n) = αl.symm.conj (e n)
    rw [← LinearEquiv.conj_comp]
    exact congrArg αl.symm.conj (he n)
  have hdel : ∀ n, dl.baseChange R ∘ₗ (el n).baseChange R =
      (el (n + 1)).baseChange R ∘ₗ dl.baseChange R := by
    intro n
    rw [hel, hel, hdl, ← LinearEquiv.conj_comp, ← LinearEquiv.conj_comp, hd]
  have hddl : dl.baseChange R ∘ₗ dl.baseChange R = 0 := by
    rw [hdl, ← LinearEquiv.conj_comp, hdd, map_zero]
  let := fun m : {m : K // l.1 ≤ m} ↦
    (stageDirectedMap F A₀ G l.1 m.1 m.2).toRingHom.toAlgebra
  let := fun m : {m : K // l.1 ≤ m} ↦ (stageToLimitMap c A₀ (G.obj m.1)).toAlgebra
  obtain ⟨htower', -, heq⟩ :=
    stage_above_finitePresentation_baseChange hc A₀ G l.1
  let := htower'
  obtain ⟨m, hem, hdm, hddm⟩ :=
    exists_baseChange_complex_relations (heq Ml) s el dl hsel hel' hdel hddl
  let : IsScalarTower (B l.1) (B m.1) R := htower' m
  let Mm := B m.1 ⊗[B l.1] Ml
  let em := fun n ↦ (el n).baseChange (B m.1)
  let dm := dl.baseChange (B m.1)
  let αm : R ⊗[B m.1] Mm ≃ₗ[R] N :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (B l.1) (B m.1) R R Ml).trans αl
  refine ⟨m.1, Mm, inferInstance, inferInstance, em, dm, inferInstance,
    (fun n hn ↦ by simp [em, hsel n hn]), hem, hdm, hddm, αm, ?_, ?_⟩
  · exact fun n ↦ baseChange_cancelBaseChange_equivariant αl (el n) (e n) fun x ↦ by
      rw [hel]; simp [LinearEquiv.conj_apply_apply]
  · exact baseChange_cancelBaseChange_equivariant αl dl d fun x ↦ by
      rw [hdl]; simp [LinearEquiv.conj_apply_apply]


private theorem exists_stage_complex_operators {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I] {F : I ⥤ CommAlgCat.{uR} R₀}
    {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
    (N : Type (max uR uA uM)) [AddCommGroup N] [Module (c.pt ⊗[R₀] A₀) N]
    [Module.FinitePresentation (c.pt ⊗[R₀] A₀) N]
    (s : Finset ℤ) (e : ℤ → N →ₗ[c.pt ⊗[R₀] A₀] N) (d : N →ₗ[c.pt ⊗[R₀] A₀] N)
    (hs : ∀ n ∉ s, e n = 0) (he : ∀ n, IsIdempotentElem (e n))
    (hd : ∀ n, d ∘ₗ e n = e (n + 1) ∘ₗ d) (hdd : d ∘ₗ d = 0) :
    ∃ (i : I) (M : Type (max uR uA uM)) (_ : AddCommGroup M)
      (_ : Module (stageAlgebra F A₀ i) M)
      (e' : ℤ → M →ₗ[stageAlgebra F A₀ i] M) (d' : M →ₗ[stageAlgebra F A₀ i] M),
      letI := (stageToLimitMap c A₀ i).toAlgebra
      Module.FinitePresentation (stageAlgebra F A₀ i) M ∧
      (∀ n ∉ s, e' n = 0) ∧ (∀ n, IsIdempotentElem (e' n)) ∧
      (∀ n, d' ∘ₗ e' n = e' (n + 1) ∘ₗ d') ∧ d' ∘ₗ d' = 0 ∧
      ∃ f : (c.pt ⊗[R₀] A₀) ⊗[stageAlgebra F A₀ i] M ≃ₗ[c.pt ⊗[R₀] A₀] N,
        (∀ n x, f ((e' n).baseChange (c.pt ⊗[R₀] A₀) x) = e n (f x)) ∧
        (∀ x, f (d'.baseChange (c.pt ⊗[R₀] A₀) x) = d (f x)) := by
  obtain ⟨K, _, _, _, G, _⟩ := exists_directed_final I
  obtain ⟨i, hi⟩ :=
    exists_directed_stage_complex_operators.{uI, uJ, uR, uA, uM} hc A₀ G N s e d hs he hd hdd
  exact ⟨G.obj i, hi⟩


/-- A bounded complex has subsingleton terms outside the interval of its bounds. -/
private theorem subsingleton_X_of_notMem_Icc {R : Type*} [Ring R]
    (P : CochainComplex (ModuleCat R) ℤ) (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b] :
    ∀ n ∉ Finset.Icc a b, Subsingleton (P.X n) := by
  intro n hn
  apply ModuleCat.isZero_iff_subsingleton.mp
  by_cases ha : n < a
  · exact P.isZero_of_isStrictlyGE a n ha
  · exact P.isZero_of_isStrictlyLE b n (by simp only [Finset.mem_Icc] at hn; omega)

private theorem exists_stage_bounded_finitePresentation_complex
    {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I] {F : I ⥤ CommAlgCat.{uR} R₀}
    {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
    (P : CochainComplex (ModuleCat.{max uR uA uM} (c.pt ⊗[R₀] A₀)) ℤ)
    (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hP : ∀ n, Module.FinitePresentation (c.pt ⊗[R₀] A₀) (P.X n)) :
    ∃ (i : I) (Q : CochainComplex (ModuleCat.{max uR uA uM} (stageAlgebra F A₀ i)) ℤ),
      letI : (ModuleCat.extendScalars.{max uR uA, max uR uA, max uR uA uM}
        (stageToLimitMap c A₀ i)).IsLeftAdjoint :=
        (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM, max uR uA, max uR uA}
          (stageToLimitMap c A₀ i)).isLeftAdjoint
      Q.IsStrictlyGE a ∧ Q.IsStrictlyLE b ∧
      (∀ n, Module.FinitePresentation (stageAlgebra F A₀ i) (Q.X n)) ∧
      Nonempty (((ModuleCat.extendScalars.{max uR uA, max uR uA, max uR uA uM}
        (stageToLimitMap c A₀ i)).mapHomologicalComplex (.up ℤ)).obj Q ≅ P) := by
  classical
  let s := Finset.Icc a b
  have hs := subsingleton_X_of_notMem_Icc P a b
  let := hP
  have hse : ∀ n ∉ s, totalIdem.{max uR uA, max uR uA uM} P s n = 0 := by
    intro n hn
    simp [totalIdem, totalInc_eq_zero hn]
  obtain ⟨i, M, _, _, e, d, hM, hse', he, hd, hdd, f, hf, hfd⟩ :=
    exists_stage_complex_operators.{uI, uJ, uR, uA, uM} hc A₀
      (totalModule.{max uR uA, max uR uA uM} P s) s (totalIdem.{max uR uA, max uR uA uM} P s)
      (totalDiff.{max uR uA, max uR uA uM} P s) hse
        (isIdempotentElem_totalIdem.{max uR uA, max uR uA uM} hs)
      (totalDiff_comp_totalIdem.{max uR uA, max uR uA uM} hs)
        (totalDiff_comp_totalDiff.{max uR uA, max uR uA uM} hs)
  let := (stageToLimitMap c A₀ i).toAlgebra
  let := hM
  let : (ModuleCat.extendScalars.{max uR uA, max uR uA, max uR uA uM}
    (stageToLimitMap c A₀ i)).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM, max uR uA, max uR uA}
      (stageToLimitMap c A₀ i)).isLeftAdjoint
  refine ⟨i, complexOfIdempotents M e d hd hdd, ?_, ?_, ?_, ?_⟩
  · exact isStrictlyGE_complexOfIdempotents hd hdd a fun n hn ↦
      hse' n (by simp only [s, Finset.mem_Icc]; omega)
  · exact isStrictlyLE_complexOfIdempotents hd hdd b fun n hn ↦
      hse' n (by simp only [s, Finset.mem_Icc]; omega)
  · intro n
    exact finitePresentation_range_of_isIdempotentElem (he n)
  · exact ⟨extendScalarsComplexOfIdempotentsIso.{max uR uA, uM} (stageToLimitMap c A₀ i) he hd hdd
    ≪≫
      complexOfIdempotentsCongr f
        (baseChange_comp_eq_of_comp_eq _ hd) (baseChange_comp_self_eq_zero _ hdd)
        (totalDiff_comp_totalIdem.{max uR uA, max uR uA uM} hs)
          (totalDiff_comp_totalDiff.{max uR uA, max uR uA uM} hs) hf hfd ≪≫
      complexOfIdempotentsTotalIso.{max uR uA, max uR uA uM} hs⟩


private theorem exists_stage_flat_complex_operators {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I] {F : I ⥤ CommAlgCat.{uR} R₀}
    {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀] [Algebra.FinitePresentation R₀
      A₀]
    (N : Type (max uR uA uM)) [AddCommGroup N] [Module (c.pt ⊗[R₀] A₀) N]
    [Module.FinitePresentation (c.pt ⊗[R₀] A₀) N]
    [Module c.pt N] [IsScalarTower c.pt (c.pt ⊗[R₀] A₀) N] [Module.Flat c.pt N]
    (s : Finset ℤ) (e : ℤ → N →ₗ[c.pt ⊗[R₀] A₀] N) (d : N →ₗ[c.pt ⊗[R₀] A₀] N)
    (hs : ∀ n ∉ s, e n = 0) (he : ∀ n, IsIdempotentElem (e n))
    (hd : ∀ n, d ∘ₗ e n = e (n + 1) ∘ₗ d) (hdd : d ∘ₗ d = 0) :
    ∃ (i : I) (M : Type (max uR uA uM)) (_ : AddCommGroup M)
      (_ : Module (stageAlgebra F A₀ i) M)
      (e' : ℤ → M →ₗ[stageAlgebra F A₀ i] M) (d' : M →ₗ[stageAlgebra F A₀ i] M),
      letI := (stageToLimitMap c A₀ i).toAlgebra
      Module.FinitePresentation (stageAlgebra F A₀ i) M ∧
      (letI : Module (F.obj i) M := Module.compHom M (algebraMap (F.obj i) (stageAlgebra F A₀ i))
       Module.Flat (F.obj i) M) ∧
      (∀ n ∉ s, e' n = 0) ∧ (∀ n, IsIdempotentElem (e' n)) ∧
      (∀ n, d' ∘ₗ e' n = e' (n + 1) ∘ₗ d') ∧ d' ∘ₗ d' = 0 ∧
      ∃ f : (c.pt ⊗[R₀] A₀) ⊗[stageAlgebra F A₀ i] M ≃ₗ[c.pt ⊗[R₀] A₀] N,
        (∀ n x, f ((e' n).baseChange (c.pt ⊗[R₀] A₀) x) = e n (f x)) ∧
        (∀ x, f (d'.baseChange (c.pt ⊗[R₀] A₀) x) = d (f x)) := by
  classical
  let R := c.pt ⊗[R₀] A₀
  obtain ⟨K, _, _, _, G, _⟩ := exists_directed_final I
  let B := fun k : K ↦ stageAlgebra F A₀ (G.obj k)
  obtain ⟨k, M, _, _, e', d', hfp, hse, he', hd', hdd', α, hαe, hαd⟩ :=
    exists_directed_stage_complex_operators.{uI, uJ, uR, uA, uM} hc A₀ G N s e d hs he hd hdd
  let := hfp
  let := (stageToLimitMap c A₀ (G.obj k)).toAlgebra
  have hflat : Module.Flat c.pt (R ⊗[B k] M) :=
    Module.Flat.of_linearEquiv (α.restrictScalars c.pt)
  obtain ⟨l, hkl, hl⟩ := exists_stage_flat_baseChange hc A₀ G k M hflat
  let := (stageDirectedMap F A₀ G k l hkl).toRingHom.toAlgebra
  let := (stageToLimitMap c A₀ (G.obj l)).toAlgebra
  let := (stage_above_finitePresentation_baseChange.{uI, uJ, uR, uA, uM, uM} hc A₀ G k).1 ⟨l, hkl⟩
  let Ml := B l ⊗[B k] M
  let el := fun n ↦ (e' n).baseChange (B l)
  let dl := d'.baseChange (B l)
  let αl : R ⊗[B l] Ml ≃ₗ[R] N :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (B k) (B l) R R M).trans α
  refine ⟨G.obj l, Ml, inferInstance, inferInstance, el, dl, inferInstance, ?_,
    (fun n hn ↦ by simp [el, hse n hn]), (fun n ↦ isIdempotentElem_baseChange (B l) (he' n)),
    baseChange_comp_eq_of_comp_eq (B l) hd', baseChange_comp_self_eq_zero (B l) hdd', αl, ?_, ?_⟩
  · have hm : Module.compHom Ml (algebraMap (F.obj (G.obj l)) (B l)) =
        (inferInstance : Module (F.obj (G.obj l)) Ml) := by
      apply Module.ext'
      intro r x
      exact IsScalarTower.algebraMap_smul (B l) r x
    rw [hm]
    exact hl
  · exact fun n ↦ baseChange_cancelBaseChange_equivariant α (e' n) (e n) (hαe n)
  · exact baseChange_cancelBaseChange_equivariant α d' d hαd
private theorem exists_stage_bounded_flat_finitePresentation_complex
    {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I] {F : I ⥤ CommAlgCat.{uR} R₀}
    {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀] [Algebra.FinitePresentation R₀
      A₀]
    (P : CochainComplex (ModuleCat.{max uR uA uM} (c.pt ⊗[R₀] A₀)) ℤ)
    (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hP : ∀ n, Module.Flat c.pt ((ModuleCat.restrictScalars
      (algebraMap c.pt (c.pt ⊗[R₀] A₀))).obj (P.X n)) ∧
      Module.FinitePresentation (c.pt ⊗[R₀] A₀) (P.X n)) :
    ∃ (i : I) (Q : CochainComplex (ModuleCat.{max uR uA uM} (stageAlgebra F A₀ i)) ℤ),
      letI : (ModuleCat.extendScalars.{max uR uA, max uR uA, max uR uA uM}
        (stageToLimitMap c A₀ i)).IsLeftAdjoint :=
        (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM, max uR uA, max uR uA}
          (stageToLimitMap c A₀ i)).isLeftAdjoint
      letI : (ModuleCat.extendScalars.{max uR uA, max uR uA, max uR uA uM}
        (stageToLimitMap c A₀ i)).Additive :=
        CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
          (by change PreservesFiniteColimits _; infer_instance)
      Q.IsStrictlyGE a ∧ Q.IsStrictlyLE b ∧
      (∀ n, Module.Flat (F.obj i) ((ModuleCat.restrictScalars
        (algebraMap (F.obj i) (stageAlgebra F A₀ i))).obj (Q.X n)) ∧
        Module.FinitePresentation (stageAlgebra F A₀ i) (Q.X n)) ∧
      Nonempty (((ModuleCat.extendScalars.{max uR uA, max uR uA, max uR uA uM}
        (stageToLimitMap c A₀ i)).mapHomologicalComplex (.up ℤ)).obj Q ≅ P) := by
  classical
  let s := Finset.Icc a b
  have hs := subsingleton_X_of_notMem_Icc P a b
  let := fun n ↦ (hP n).2
  let := fun n : ℤ ↦ Module.compHom (P.X n) (algebraMap c.pt (c.pt ⊗[R₀] A₀))
  let : ∀ n : ℤ, Module.Flat c.pt (P.X n) := fun n ↦ (hP n).1
  let : ∀ n : s, Module.Flat c.pt (P.X n) := fun n ↦ (hP n).1
  let : ∀ n : ℤ, IsScalarTower c.pt (c.pt ⊗[R₀] A₀) (P.X n) :=
    fun n ↦ IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module.Flat c.pt (totalModule P s) := flat_pi_of_finite (fun n : s ↦ P.X n)
  have hse : ∀ n ∉ s, totalIdem.{max uR uA, max uR uA uM} P s n = 0 := by
    intro n hn
    simp [totalIdem, totalInc_eq_zero hn]
  obtain ⟨i, M, _, _, e, d, hM, hflatM, hse', he, hd, hdd, f, hf, hfd⟩ :=
    exists_stage_flat_complex_operators.{uI, uJ, uR, uA, uM} hc A₀
      (totalModule.{max uR uA, max uR uA uM} P s) s (totalIdem.{max uR uA, max uR uA uM} P s)
      (totalDiff.{max uR uA, max uR uA uM} P s) hse
        (isIdempotentElem_totalIdem.{max uR uA, max uR uA uM} hs)
      (totalDiff_comp_totalIdem.{max uR uA, max uR uA uM} hs)
        (totalDiff_comp_totalDiff.{max uR uA, max uR uA uM} hs)
  let := (stageToLimitMap c A₀ i).toAlgebra
  let := hM
  let : Module (F.obj i) M := Module.compHom M (algebraMap (F.obj i) (stageAlgebra F A₀ i))
  let : IsScalarTower (F.obj i) (stageAlgebra F A₀ i) M :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let := hflatM
  let : (ModuleCat.extendScalars.{max uR uA, max uR uA, max uR uA uM}
    (stageToLimitMap c A₀ i)).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM, max uR uA, max uR uA}
      (stageToLimitMap c A₀ i)).isLeftAdjoint
  let : (ModuleCat.extendScalars.{max uR uA, max uR uA, max uR uA uM}
    (stageToLimitMap c A₀ i)).Additive :=
    CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (by change PreservesFiniteColimits _; infer_instance)
  refine ⟨i, complexOfIdempotents M e d hd hdd, ?_, ?_, ?_, ?_⟩
  · exact isStrictlyGE_complexOfIdempotents hd hdd a fun n hn ↦
      hse' n (by simp only [s, Finset.mem_Icc]; omega)
  · exact isStrictlyLE_complexOfIdempotents hd hdd b fun n hn ↦
      hse' n (by simp only [s, Finset.mem_Icc]; omega)
  · intro n
    exact ⟨flat_range_of_isIdempotentElem (he n),
      finitePresentation_range_of_isIdempotentElem (he n)⟩
  · exact ⟨extendScalarsComplexOfIdempotentsIso.{max uR uA, uM} (stageToLimitMap c A₀ i) he hd hdd
    ≪≫
      complexOfIdempotentsCongr f
        (baseChange_comp_eq_of_comp_eq _ hd) (baseChange_comp_self_eq_zero _ hdd)
        (totalDiff_comp_totalIdem.{max uR uA, max uR uA uM} hs)
          (totalDiff_comp_totalDiff.{max uR uA, max uR uA uM} hs) hf hfd ≪≫
      complexOfIdempotentsTotalIso.{max uR uA, max uR uA uM} hs⟩

section DerivedReflection

universe u v u' v' w w'
private lemma isIso_of_mapDerivedCategory_map
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [F.ReflectsIsomorphisms]
    {X Y : DerivedCategory C} (f : X ⟶ Y)
    [IsIso (F.mapDerivedCategory.map f)] : IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro n
  have hi : IsIso ((F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n).map f) := by
    show IsIso ((DerivedCategory.homologyFunctor D n).map (F.mapDerivedCategory.map f))
    infer_instance
  have : IsIso (F.map ((DerivedCategory.homologyFunctor C n).map f)) :=
    (NatIso.isIso_map_iff
      (_root_.StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F n) f).mp hi
  exact isIso_of_reflects_iso ((DerivedCategory.homologyFunctor C n).map f) F


end DerivedReflection

section FlatTor

universe uB
open MonoidalCategory

private lemma torIndependent_of_flat
    {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Flat R A] :
    RingTheory.TorIndependence.TorIndependent R A B := by
  unfold RingTheory.TorIndependence.TorIndependent
  let R' := ULift.{max uR uA uB} R
  let A' := ULift.{max uR uA uB} A
  let B' := ULift.{max uR uA uB} B
  let : Algebra R' A' := ULift.algebra' R A'
  let : Algebra R' B' := ULift.algebra' R B'
  let : Module.Flat R' A' := Module.Flat.ulift_left_iff.mpr inferInstance
  intro p hp
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  let P := ModuleCat.of R' A'
  let N := ModuleCat.of R' B'
  have hiso := (projectiveResolution N).isoLeftDerivedObj (tensorLeft P) (n + 1)
  refine IsZero.of_iso ?_ hiso
  have hexact : ((projectiveResolution N).complex.sc (n + 1)).Exact :=
    (HomologicalComplex.exactAt_iff _ _).mp
      ((projectiveResolution N).complex_exactAt_succ n)
  have hmap : (((tensorLeft P).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (projectiveResolution N).complex).ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff]
    exact hexact.map_of_preservesLeftHomologyOf (tensorLeft P)
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hmap

end FlatTor

section UnderivedBaseChange

universe uS uB v
open scoped ChangeOfRings

set_option backward.isDefEq.respectTransparency false in
private lemma isIso_baseChangeComparison_app
    {R : Type uR} {A : Type uA} {S : Type uS} {B : Type uB}
    [CommRing R] [CommRing A] [CommRing S] [CommRing B]
    [Algebra R A] [Algebra R S] [Algebra R B] [Algebra A B] [Algebra S B]
    [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
    (τ : ModuleCat.restrictScalars.{max v uR uA uS uB} (algebraMap R A) ⋙
        ModuleCat.extendScalars (algebraMap R S) ⟶
      ModuleCat.extendScalars (algebraMap A B) ⋙ ModuleCat.restrictScalars (algebraMap S B))
    (hτ : ∀ (M : ModuleCat.{max v uR uA uS uB} A) (s : S) (m : M),
      τ.app M (s ⊗ₜ[R,algebraMap R S] m) =
        (algebraMap S B s) ⊗ₜ[A,algebraMap A B] m)
    (M : ModuleCat.{max v uR uA uS uB} A) : IsIso (τ.app M) := by
  let : Module R M := Module.compHom M (algebraMap R A)
  let : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eS : (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) ≃ₗ[R] S :=
    { AddEquiv.refl S with
      map_smul' := fun r s ↦ (Algebra.smul_def (R := R) (A := S) r s).symm }
  let eB : (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) ≃ₗ[A] B :=
    { AddEquiv.refl B with
      map_smul' := fun a b ↦ (Algebra.smul_def (R := A) (A := B) a b).symm }
  let u := TensorProduct.congr eS (LinearEquiv.refl R M)
  let w := TensorProduct.congr eB (LinearEquiv.refl A M)
  let e := (Algebra.IsPushout.cancelBaseChange R S A B M).symm
  let ψ := w.toAddEquiv.toAddMonoidHom.comp
    ((τ.app M).hom.toAddMonoidHom.comp u.symm.toAddEquiv.toAddMonoidHom)
  have hψ : (ψ : _ → _) = ⇑e := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      show w (τ.app M (s ⊗ₜ[R,algebraMap R S] m)) = e (s ⊗ₜ[R] m)
      rw [hτ]
      exact (Algebra.IsPushout.cancelBaseChange_symm_tmul R S A B M s m).symm
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  apply (ConcreteCategory.isIso_iff_bijective (τ.app M)).mpr
  have he : (τ.app M : _ → _) = w.symm ∘ ψ ∘ u := by
    funext x
    show τ.app M x = w.symm (w (τ.app M (u.symm (u x))))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  rw [he]
  exact w.symm.bijective.comp ((hψ.symm ▸ e.bijective).comp u.bijective)

end UnderivedBaseChange

section RelativeFlatComparison

universe uS uB v
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] TotalDerivedExtensionScalars.isLeftDerived
open scoped ChangeOfRings

-- elaborating the composite natural transformations of derived functors below
set_option backward.isDefEq.respectTransparency false in
private lemma isIso_comparison_app_of_torIndependent
    {R : Type uR} {A : Type uA} {S : Type uS} {B : Type uB}
    [CommRing R] [CommRing A] [CommRing S] [CommRing B]
    [Algebra R A] [Algebra R S] [Algebra R B] [Algebra A B] [Algebra S B]
    [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R A S B]
    (hTor : RingTheory.TorIndependence.TorIndependent R A S)
    (LR : DerivedCategory (ModuleCat.{max v uR uA uS uB} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uS uB} S))
    (LA : DerivedCategory (ModuleCat.{max v uR uA uS uB} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uS uB} B))
    (αR : DerivedCategory.Q ⋙ LR ⟶
      extensionOfScalarsComplexGeneral.{uR, max v uA uB, uS} (algebraMap R S))
    (αA : DerivedCategory.Q ⋙ LA ⟶
      extensionOfScalarsComplexGeneral.{uA, max v uR uS, uB} (algebraMap A B))
    [LR.IsLeftDerivedFunctor αR (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uS uB} R) (.up
      ℤ))]
    [LA.IsLeftDerivedFunctor αA (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uS uB} A) (.up
      ℤ))]
    (P : CochainComplex (ModuleCat.{max v uR uA uS uB} A) ℤ)
    [IsIso (αR.app (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (.up
      ℤ)).obj P))] :
    IsIso (αA.app P) := by
  let Res := ModuleCat.restrictScalars.{max v uR uA uS uB} (algebraMap R A)
  let Res' := ModuleCat.restrictScalars.{max v uR uA uS uB} (algebraMap S B)
  let : Res.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max v uR uA uS uB, uR, uA} _).isLeftAdjoint
  let : Res.IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uS uB, uR, uA} _).isRightAdjoint
  let : Res'.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max v uR uA uS uB, uS, uB} _).isLeftAdjoint
  let : Res'.IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uS uB, uS, uB} _).isRightAdjoint
  let : (ModuleCat.extendScalars.{uA, uB, max v uR uA uS uB} (algebraMap A B)).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uS uB, uA, uB} _).isLeftAdjoint
  let : (ModuleCat.extendScalars.{uR, uS, max v uR uA uS uB} (algebraMap R S)).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uS uB, uR, uS} _).isLeftAdjoint
  let : (ModuleCat.extendScalars.{uA, uB, max v uR uA uS uB} (algebraMap A B)).Additive :=
    CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (by change PreservesFiniteColimits _; infer_instance)
  let : (ModuleCat.extendScalars.{uR, uS, max v uR uA uS uB} (algebraMap R S)).Additive :=
    CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (by change PreservesFiniteColimits _; infer_instance)
  let sq : (algebraMap A B).comp (algebraMap R A) =
      (algebraMap S B).comp (algebraMap R S) :=
    (IsScalarTower.algebraMap_eq R A B).symm.trans (IsScalarTower.algebraMap_eq R S B)
  let τ := RingTheory.TorIndependence.derivedBaseChangeComparison.{uR, uA, uS, uB, v}
    (algebraMap R A) (algebraMap R S) (algebraMap A B) (algebraMap S B) sq
    LR LA αR αA
  have : IsIso τ.2.1 :=
    RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent.{uR,
      uA, uS, uB, v} hTor LR LA αR αA
  let : Algebra.IsPushout R S A B := Algebra.IsPushout.symm inferInstance
  have : ∀ M, IsIso (τ.1.app M) := fun M ↦ isIso_baseChangeComparison_app τ.1 τ.2.2.1 M
  have : IsIso τ.1 := NatIso.isIso_of_isIso_app τ.1
  have : IsIso ((NatTrans.mapHomologicalComplex τ.1 (.up ℤ)).app P) := by
    show IsIso ((NatIso.mapHomologicalComplex (asIso τ.1) (.up ℤ)).hom.app P)
    infer_instance
  have hh := congrArg (fun α ↦ α.app P) τ.2.2.2
  dsimp only [Functor.whiskerLeft_app, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app] at hh
  simp only [Category.id_comp] at hh
  have ht : IsIso (Res'.mapDerivedCategory.map (αA.app P)) := by
    have hi := IsIso.of_isIso_fac_left hh
    simpa only [isIso_comp_right_iff] using hi
  let := ht
  exact isIso_of_mapDerivedCategory_map Res' (αA.app P)

end RelativeFlatComparison

set_option backward.isDefEq.respectTransparency false in
lemma isIso_stage_comparison_app_of_flat
    {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] {F : I ⥤ CommAlgCat.{uR} R₀}
    (c : Cocone F) (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
    (i : I) (P : CochainComplex (ModuleCat.{max uR uA uM} (stageAlgebra F A₀ i)) ℤ)
    (b : ℤ) [P.IsStrictlyLE b]
    [∀ n, Module.Flat (F.obj i) ((ModuleCat.restrictScalars
      (algebraMap (F.obj i) (stageAlgebra F A₀ i))).obj (P.X n))] :
    IsIso ((totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
      (stageToLimitMap c A₀ i)).comparison.app P) := by
  let Ri := F.obj i
  let A := stageAlgebra F A₀ i
  let B := c.pt ⊗[R₀] A₀
  let : Algebra Ri c.pt := (c.ι.app i).hom.toRingHom.toAlgebra
  let : IsScalarTower R₀ Ri c.pt :=
    IsScalarTower.of_algebraMap_eq fun x ↦ ((c.ι.app i).hom.commutes x).symm
  let : Algebra A B := (stageToLimitMap c A₀ i).toAlgebra
  let : IsScalarTower Ri A B := IsScalarTower.of_algebraMap_eq fun x ↦ by
    show (c.ι.app i).hom x ⊗ₜ[R₀] 1 = stageToLimitMap c A₀ i (x ⊗ₜ[R₀] 1)
    simp [stageToLimitMap]
  have hp : Algebra.IsPushout Ri c.pt A B :=
    @Algebra.IsPushout.tensorProduct_tensorProduct R₀ A₀ Ri c.pt
      _ _ _ _ _ _ _ _ _ ((stageToLimitMap c A₀ i).toAlgebra) inferInstance (by
        ext x
        show stageToLimitMap c A₀ i (1 ⊗ₜ[R₀] x) = 1 ⊗ₜ[R₀] x
        simp [stageToLimitMap]
        exact congrArg (· ⊗ₜ[R₀] x) (c.ι.app i).hom.map_one')
  let : Algebra.IsPushout Ri A c.pt B := Algebra.IsPushout.symm hp
  let DR := totalDerivedExtensionScalars.{uR, uR, max uA uM} (algebraMap Ri c.pt)
  let DA := totalDerivedExtensionScalars.{max uR uA, max uR uA, uM} (stageToLimitMap c A₀ i)
  let : DR.functor.IsLeftDerivedFunctor DR.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} Ri) (.up ℤ)) := DR.isLeftDerived
  let : DA.functor.IsLeftDerivedFunctor DA.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} A) (.up ℤ)) := DA.isLeftDerived
  let P' : CochainComplex (ModuleCat.{max uR uA uM} Ri) ℤ :=
    ((ModuleCat.restrictScalars (algebraMap Ri A)).mapHomologicalComplex (.up ℤ)).obj P
  let : ∀ n, Module.Flat Ri (P'.X n) := fun n ↦
    inferInstanceAs (Module.Flat (F.obj i) ((ModuleCat.restrictScalars
      (algebraMap (F.obj i) (stageAlgebra F A₀ i))).obj (P.X n)))
  let : P'.IsStrictlyLE b := inferInstance
  let : IsIso (DR.comparison.app P') :=
    isIso_comparison_app_of_isStrictlyLE_flat.{uR, max uA uM, uR} DR P' b
  exact isIso_comparison_app_of_torIndependent.{uR, max uR uA, uR, max uR uA, uM}
    (torIndependent_of_flat (R := Ri) (A := A) (B := c.pt))
    DR.functor DA.functor DR.comparison DA.comparison P

end PseudoCoherence

end
