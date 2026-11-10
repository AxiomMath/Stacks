module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DualizingExtSystemChartImage
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteModuleModelLocalizedAdicSystem
public import StacksFrontier.RingTheory.Noetherian.DirectSystemTransitionImagePrimeKernel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The vertex of the chart cocone of Stacks 0EHK

Over a chart `D(f)` of the punctured spectrum, with `B = (A_f)^∧_{I A_f}`, the finite module
model `(M_n)` becomes the tower of adic quotients of one finite `B`-module, the vertex
`X = (lim M_{n,f})^∧` of
`Stacks.Algebraization.finite_adicCompletion_limit_localizedModuleFunctor_of_isFiniteModuleModel`.
This file identifies the transport of `(M_n)` to `B` with that tower, as a system of `B`-modules,
and reduces the stabilisation of the images of the transition maps of the `Ext` system over `B` to
a statement at the primes of `B` containing `I B`: that the kernel of
`Ext^{-i}_B(X/I^{n+1}X, ω_B) → Ext^{-i}_B(X, ω_B)` dies in a later term after localizing there.

## Main results

* `Stacks.Algebraization.isIso_extendRestrictScalarsAdj_counit_app_of_torsion` — along the
  completion `R → R^∧`, the counit of extension and restriction of scalars is invertible at a
  module killed by a power of the ideal.
* `Stacks.Algebraization.chartTransportSystemIsoTower` — the transported model is the adic tower
  of the vertex.
* `Stacks.Algebraization.exists_range_eq_chartTransport_of_forall_prime` — the reduction.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

section Counit

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (J : Ideal R)

/-- **Along the completion, the unit of extension of scalars is bijective on a power torsion
module.** -/
@[sga "2 IV 4.6" "more general"]
public theorem bijective_extendRestrictScalarsAdj_unit_app_of_torsion (P : ModuleCat.{u} R)
    (hP : IsIPowerTorsion R P J) :
    Function.Bijective ((ModuleCat.extendRestrictScalarsAdj
      (algebraMap R (AdicCompletion J R))).unit.app P).hom := by
  have hb := IPowerTorsion.one_tmul_bijective
    ((IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective R (AdicCompletion J R) J
      inferInstance).mpr (AdicCompletion.quotientMap_bijective J J.fg_of_isNoetherianRing) P hP)
  have h : ((extendScalarsObjIso J P).hom.hom) ∘
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap R (AdicCompletion J R))).unit.app P).hom =
      TensorProduct.mk R (AdicCompletion J R) P 1 := by
    funext m
    rfl
  rw [← h] at hb
  exact (Function.Bijective.of_comp_iff'
    (ConcreteCategory.bijective_of_isIso (extendScalarsObjIso J P).hom) _).mp hb

/-- **Along the completion, the counit of extension and restriction of scalars is invertible at
a module killed by a power of the ideal.** -/
public theorem isIso_extendRestrictScalarsAdj_counit_app_of_torsion
    (Q : ModuleCat.{u} (AdicCompletion J R)) (k : ℕ)
    (hQ : (J.map (algebraMap R (AdicCompletion J R))) ^ k •
      (⊤ : Submodule (AdicCompletion J R) Q) = ⊥) :
    IsIso ((ModuleCat.extendRestrictScalarsAdj
      (algebraMap R (AdicCompletion J R))).counit.app Q) := by
  let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap R (AdicCompletion J R))
  let G := ModuleCat.restrictScalars (algebraMap R (AdicCompletion J R))
  have hP : IsIPowerTorsion R (G.obj Q) J := by
    intro x
    refine ⟨k + 1, Nat.succ_pos k, fun a ha => ?_⟩
    have ha' : algebraMap R (AdicCompletion J R) a ∈
        (J.map (algebraMap R (AdicCompletion J R))) ^ k := by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (Ideal.pow_le_pow_right (Nat.le_succ k) ha)
    let x' : Q := x
    have hmem : (algebraMap R (AdicCompletion J R) a) • x' ∈
        (J.map (algebraMap R (AdicCompletion J R))) ^ k •
          (⊤ : Submodule (AdicCompletion J R) Q) :=
      Submodule.smul_mem_smul ha' Submodule.mem_top
    rw [hQ] at hmem
    exact (Submodule.mem_bot _).mp hmem
  have hη := bijective_extendRestrictScalarsAdj_unit_app_of_torsion J (G.obj Q) hP
  have hid : (G.map (adj.counit.app Q)).hom ∘ (adj.unit.app (G.obj Q)).hom = id := by
    funext x
    exact congrArg (fun φ => φ.hom x) (adj.right_triangle_components Q)
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (Function.Bijective.of_comp_iff (G.map (adj.counit.app Q)).hom hη).mp
    (hid ▸ Function.bijective_id)

/-- A quotient `Q ⧸ Jᵏ Q` is killed by `Jᵏ`. -/
public theorem pow_smul_top_quotient_eq_bot {T : Type u} [CommRing T] (K : Ideal T)
    (X : Type u) [AddCommGroup X] [Module T X] (k : ℕ) :
    K ^ k • (⊤ : Submodule T (X ⧸ (K ^ k • (⊤ : Submodule T X)))) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [Submodule.smul_le]
  intro r hr x _
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    rw [Submodule.mem_bot, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top

/-- **Over the completion, the counit of extension and restriction of scalars is invertible on
the adic tower of a module.** -/
public def adicQuotientTowerCounitIso (X : ModuleCat.{u} (AdicCompletion J R)) :
    (Stacks.Examples.adicQuotientTower (J.map (algebraMap R (AdicCompletion J R))) X ⋙
        ModuleCat.restrictScalars (algebraMap R (AdicCompletion J R))) ⋙
      ModuleCat.extendScalars.{u, u, u} (algebraMap R (AdicCompletion J R)) ≅
      Stacks.Examples.adicQuotientTower (J.map (algebraMap R (AdicCompletion J R))) X :=
  NatIso.ofComponents (fun n =>
    haveI := isIso_extendRestrictScalarsAdj_counit_app_of_torsion J
      ((Stacks.Examples.adicQuotientTower (J.map (algebraMap R (AdicCompletion J R))) X).obj n)
      (n.unop + 1) (pow_smul_top_quotient_eq_bot _ _ _)
    asIso ((ModuleCat.extendRestrictScalarsAdj (algebraMap R (AdicCompletion J R))).counit.app
      ((Stacks.Examples.adicQuotientTower (J.map (algebraMap R (AdicCompletion J R))) X).obj n)))
    (fun _ => (ModuleCat.extendRestrictScalarsAdj
      (algebraMap R (AdicCompletion J R))).counit.naturality _)

end Counit

section Vertex

variable (S : AlgebraizationSituation.{u}) (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A) (f : S.A)

/-- **The vertex of the chart cocone**: the completed limit `(lim M_{n,f})^∧` over
`B = (A_f)^∧_{I A_f}`. -/
public abbrev chartVertex :
    ModuleCat.{u} (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
      (Localization.Away f)) :=
  ModuleCat.of _ (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
    (CategoryTheory.Limits.limit (M ⋙ ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers f)) :
      ModuleCat.{u} (Localization (Submonoid.powers f))))

/-- The tower of adic quotients of the chart vertex. -/
public abbrev chartVertexTower :
    ℕᵒᵖ ⥤ ModuleCat.{u} (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
      (Localization.Away f)) :=
  Stacks.Examples.adicQuotientTower
    ((S.I.map (algebraMap S.A (Localization.Away f))).map (algebraMap (Localization.Away f)
      (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f))) (Localization.Away f))))
    (chartVertex S M f)

/-- **The transport of a finite module model to the chart ring is the adic tower of the chart
vertex.** -/
public def chartTransportSystemIsoTower (hM : IsFiniteModuleModel S M) (hf : f ∈ S.a) :
    chartTransportSystem S.I f M ≅ chartVertexTower S M f :=
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft M
      (extendScalars_iso_localizedModuleFunctor.{u, u} (Submonoid.powers f)) ≪≫
        (localizedModuleFunctorAdicQuotientNatIso S M hM hf).symm)
      (ModuleCat.extendScalars.{u, u, u} (algebraMap (Localization.Away f)
        (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
          (Localization.Away f)))) ≪≫
    adicQuotientTowerCounitIso (S.I.map (algebraMap S.A (Localization.Away f)))
      (chartVertex S M f)

end Vertex

section ExtIso

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- An isomorphism of inverse systems induces an isomorphism of their `Ext` systems. -/
public def dualizingExtSystemMapIso {M₁ M₂ : ℕᵒᵖ ⥤ ModuleCat.{u} R} (e : M₁ ≅ M₂)
    (ω : DerivedCategory (ModuleCat.{u} R)) (i : ℤ) :
    dualizingExtSystem M₁ ω i ≅ dualizingExtSystem M₂ ω i :=
  NatIso.ofComponents (fun n => ((dualizingExtFunctor ω i).mapIso (e.app (op n)).op).symm)
    (fun {m n} h => by
      simp only [Iso.symm_hom, Functor.mapIso_inv, Iso.op_inv]
      change (dualizingExtFunctor ω i).map (M₁.map (homOfLE (leOfHom h)).op).op ≫ _ =
        _ ≫ (dualizingExtFunctor ω i).map (M₂.map (homOfLE (leOfHom h)).op).op
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
      congr 2
      exact (e.inv.naturality (homOfLE (leOfHom h)).op).symm)

end ExtIso

section Reduction

variable (S : AlgebraizationSituation.{u}) (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A) (f : S.A)

/-- The quotient maps from the chart vertex onto its adic tower. -/
public abbrev chartVertexProj (n : ℕ) : chartVertex S M f ⟶ (chartVertexTower S M f).obj (op n) :=
  ModuleCat.ofHom (Submodule.mkQ _)

/-- The maps `β_n = Ext^{-i}(X ↠ X/I^{n+1}X, ω_B)` into `Ext^{-i}_B(X, ω_B)`. -/
public abbrev chartCocone
    (ω : DerivedCategory (ModuleCat.{u} (AdicCompletion (S.I.map (algebraMap S.A
      (Localization.Away f))) (Localization.Away f))))
    (i : ℤ) (n : ℕ) :=
  ((dualizingExtFunctor ω i).map (chartVertexProj S M f n).op).hom

/-- The maps `β_n` form a cocone on the `Ext` system of the tower. -/
public theorem chartCocone_comp
    (ω : DerivedCategory (ModuleCat.{u} (AdicCompletion (S.I.map (algebraMap S.A
      (Localization.Away f))) (Localization.Away f))))
    (i : ℤ) {m n : ℕ} (h : m ≤ n) :
    chartCocone S M f ω i n ∘ₗ
        ((dualizingExtSystem (chartVertexTower S M f) ω i).map (homOfLE h)).hom =
      chartCocone S M f ω i m := by
  have key : (dualizingExtSystem (chartVertexTower S M f) ω i).map (homOfLE h) ≫
      (dualizingExtFunctor ω i).map (chartVertexProj S M f n).op =
        (dualizingExtFunctor ω i).map (chartVertexProj S M f m).op := by
    change (dualizingExtFunctor ω i).map ((chartVertexTower S M f).map (homOfLE h).op).op ≫
      (dualizingExtFunctor ω i).map (chartVertexProj S M f n).op = _
    rw [← Functor.map_comp, ← op_comp]
    congr 2
  exact congrArg ModuleCat.Hom.hom key

end Reduction

end Stacks.Algebraization

end
