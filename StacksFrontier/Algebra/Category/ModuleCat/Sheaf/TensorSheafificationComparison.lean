module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Colimit.TensorProduct
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Order.CompletePartialOrder
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheafification and the tensor product of presheaves of modules

Let `(C, J)` be a site and `𝒪` a presheaf of commutative rings on `C` whose underlying presheaf
of rings is a sheaf. For presheaves of `𝒪`-modules `F'` and `G'`, the sections of the tensor
product presheaf `F' ⊗ G'` over `U` are `F'(U) ⊗_{𝒪(U)} G'(U)`. Writing `P^#` for the
sheafification of a presheaf of modules `P`, the sheafification units `F' → F'^#` and
`G' → G'^#` induce a morphism `(F' ⊗ G')^# ⟶ (F'^# ⊗ G'^#)^#`, and this morphism is an
isomorphism of sheaves of `𝒪`-modules.

## Main definitions

* `structureSheaf`: the sheaf of rings underlying `𝒪`.
* `sheafify`: the sheafification functor from presheaves of `𝒪`-modules to sheaves of
  `𝒪`-modules.
* `toSheafify`: the unit `P ⟶ P^#` of sheafification.
* `tensorSheafifyComparison`: the morphism `(F' ⊗ G')^# ⟶ (F'^# ⊗ G'^#)^#`.
* `tensorSheafifyIso`: the isomorphism `(F' ⊗ G')^# ≅ (F'^# ⊗ G'^#)^#`.

## Main results

* `isIso_sheafify_map_toSheafify`: sheafification inverts each unit `P ⟶ P^#`.
* `W_whiskerRight`: if `f` is a local isomorphism of presheaves of modules, then so is
  `f ▷ X`.
* `isIso_sheafify_map_whiskerRight`, `isIso_sheafify_map_whiskerLeft`: a morphism inverted by
  sheafification remains so after tensoring with a fixed presheaf of modules.
* `tensor_sheafify_isIso`: the morphism `tensorSheafifyComparison` is an isomorphism.

## References

* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u w

namespace Stacks.SheafOfModules.TensorSheafification

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- The structure sheaf of a ringed space, modelled as a presheaf of commutative rings on the
site `(C, J)`. For a topological space `X` one takes `C = Opens X` and
`J = Opens.grothendieckTopology X`. -/
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})

/-- The underlying presheaf of (not-necessarily-commutative) rings of the structure sheaf. -/
abbrev structureRingPresheaf : Cᵒᵖ ⥤ RingCat.{w} := 𝒪 ⋙ forget₂ CommRingCat.{w} RingCat.{w}

/- The sheaf condition making `(C, J, 𝒪)` a ringed space: `𝒪` is a sheaf of rings. -/
variable (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))

/-- The structure sheaf packaged as a genuine sheaf of rings `Osh : Sheaf J RingCat`. This is
the sheaf of rings `𝒪_X` of the ringed space `(X, 𝒪_X)`. -/
def structureSheaf : Sheaf J RingCat.{w} := ⟨structureRingPresheaf 𝒪, h𝒪⟩

/-- The underlying presheaf of `structureSheaf 𝒪 h𝒪` is `structureRingPresheaf 𝒪`. -/
@[simp] lemma structureSheaf_obj :
    (structureSheaf 𝒪 h𝒪).obj = structureRingPresheaf 𝒪 := rfl

attribute [local implicit_reducible] structureSheaf
  PresheafOfModules.toPresheaf PresheafOfModulesOfCommRing.Monoidal.tensorObj

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The sheafification functor `(-)^# : PresheafOfModules 𝒪 ⥤ SheafOfModules 𝒪`. -/
noncomputable def sheafify :
    PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj ⥤ SheafOfModules.{w} (structureSheaf 𝒪 h𝒪) :=
  PresheafOfModules.sheafification (𝟙 (structureSheaf 𝒪 h𝒪).obj)

/-- The sheafification adjunction; its unit gives the canonical map `P → P^#`. -/
noncomputable def sheafifyAdjunction :
    sheafify 𝒪 h𝒪 ⊣
      SheafOfModules.forget (structureSheaf 𝒪 h𝒪) ⋙
        PresheafOfModules.restrictScalars (𝟙 (structureSheaf 𝒪 h𝒪).obj) :=
  PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf 𝒪 h𝒪).obj)

/-- The canonical unit map `P → P^#` (the underlying presheaf-of-modules map of the
sheafification of `P`). -/
noncomputable def toSheafify (P : PresheafOfModules.{w} (structureRingPresheaf 𝒪)) :
    P ⟶ (SheafOfModules.forget (structureSheaf 𝒪 h𝒪) ⋙
          PresheafOfModules.restrictScalars (𝟙 (structureSheaf 𝒪 h𝒪).obj)).obj
        ((sheafify 𝒪 h𝒪).obj P) :=
  (sheafifyAdjunction 𝒪 h𝒪).unit.app P

attribute [local implicit_reducible] sheafify sheafifyAdjunction toSheafify

/-- The morphism of presheaves of modules `F' ⊗ G' ⟶ (F')^# ⊗ (G')^#` obtained from the
sheafification units `η_{F'}`, `η_{G'}` by the monoidal product. (Here `(F')^#`, `(G')^#`
denote the underlying presheaves of modules of the sheafifications.) -/
noncomputable def tensorUnitMap
    (F' G' : PresheafOfModules.{w} (structureRingPresheaf 𝒪)) :
    PresheafOfModules.tensorObj (O := 𝒪) F' G' ⟶
      PresheafOfModules.tensorObj (O := 𝒪)
        ((SheafOfModules.forget (structureSheaf 𝒪 h𝒪) ⋙
            PresheafOfModules.restrictScalars (𝟙 (structureSheaf 𝒪 h𝒪).obj)).obj
          ((sheafify 𝒪 h𝒪).obj F'))
        ((SheafOfModules.forget (structureSheaf 𝒪 h𝒪) ⋙
            PresheafOfModules.restrictScalars (𝟙 (structureSheaf 𝒪 h𝒪).obj)).obj
          ((sheafify 𝒪 h𝒪).obj G')) :=
  PresheafOfModules.tensorHom (toSheafify 𝒪 h𝒪 F') (toSheafify 𝒪 h𝒪 G')

/-- The canonical comparison morphism of sheaves of modules
`(F' ⊗_{p} G')^# ⟶ ((F')^# ⊗_{p} (G')^#)^#`, obtained by sheafifying `tensorUnitMap`. -/
noncomputable def tensorSheafifyComparison
    (F' G' : PresheafOfModules.{w} (structureRingPresheaf 𝒪)) :
    (sheafify 𝒪 h𝒪).obj (PresheafOfModules.tensorObj (O := 𝒪) F' G') ⟶
      (sheafify 𝒪 h𝒪).obj
        (PresheafOfModules.tensorObj (O := 𝒪)
          ((SheafOfModules.forget (structureSheaf 𝒪 h𝒪) ⋙
              PresheafOfModules.restrictScalars (𝟙 (structureSheaf 𝒪 h𝒪).obj)).obj
            ((sheafify 𝒪 h𝒪).obj F'))
          ((SheafOfModules.forget (structureSheaf 𝒪 h𝒪) ⋙
              PresheafOfModules.restrictScalars (𝟙 (structureSheaf 𝒪 h𝒪).obj)).obj
            ((sheafify 𝒪 h𝒪).obj G'))) :=
  (sheafify 𝒪 h𝒪).map (tensorUnitMap 𝒪 h𝒪 F' G')

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Sheafification sends the unit `P ⟶ P^#` to an isomorphism. -/
theorem isIso_sheafify_map_toSheafify
    (P : PresheafOfModules.{w} (structureRingPresheaf 𝒪)) :
    IsIso ((sheafify 𝒪 h𝒪).map (toSheafify 𝒪 h𝒪 P)) := by
  have h := (sheafifyAdjunction 𝒪 h𝒪).left_triangle_components P
  have hb : IsIso ((sheafifyAdjunction 𝒪 h𝒪).counit.app ((sheafify 𝒪 h𝒪).obj P)) :=
    inferInstance
  have ha : (sheafify 𝒪 h𝒪).map (toSheafify 𝒪 h𝒪 P)
      = inv ((sheafifyAdjunction 𝒪 h𝒪).counit.app ((sheafify 𝒪 h𝒪).obj P)) := by
    rwa [← cancel_mono ((sheafifyAdjunction 𝒪 h𝒪).counit.app ((sheafify 𝒪 h𝒪).obj P)),
      IsIso.inv_hom_id]
  rw [ha]
  infer_instance

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [J.WEqualsLocallyBijective AddCommGrpCat]
    [HasWeakSheafify J AddCommGrpCat] in
/-- If the underlying presheaf map of `f` is locally surjective, then so is that of `f ▷ X`. -/
theorem W_whiskerRight_isLocallySurjective
    {A B : PresheafOfModules.{w} (structureRingPresheaf 𝒪)} (f : A ⟶ B)
    (X : PresheafOfModules.{w} (structureRingPresheaf 𝒪))
    (hf : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map f)) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map (f ▷ X)) := by
  have simple : ∀ {U : C} (b : B.obj (.op U)) (x : X.obj (.op U)),
      Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map f) b ≤
        Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map (f ▷ X))
          (b ⊗ₜ[𝒪.obj (.op U)] x) := by
    intro U b x V φ ⟨a, ha⟩
    refine ⟨a ⊗ₜ[𝒪.obj (.op V)] (X.map φ.op).hom x, ?_⟩
    change ((f ▷ X).app (.op V)).hom (a ⊗ₜ[𝒪.obj (.op V)] (X.map φ.op).hom x)
        = ((B ⊗ X).map φ.op).hom (b ⊗ₜ[𝒪.obj (.op U)] x)
    have imageEquality : (f.app (.op V)).hom a = (B.map φ.op).hom b := ha
    exact (ModuleCat.MonoidalCategory.whiskerRight_apply (f.app (.op V))
      (X.obj (.op V)) a ((X.map φ.op).hom x)).trans
      ((congrArg (fun value : B.obj (.op V) =>
        value ⊗ₜ[𝒪.obj (.op V)] (X.map φ.op).hom x) imageEquality).trans
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul φ.op b x).symm)
  constructor
  intro U t
  change Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map (f ▷ X)) t ∈ J U
  induction t using TensorProduct.inductionOn with
  | tmul b x =>
    exact J.superset_covering (simple b x) (hf.imageSieve_mem b)
  | add s t hs ht =>
    refine J.superset_covering ?_ (J.intersection_covering hs ht)
    rintro V φ ⟨⟨a, ha⟩, ⟨c, hc⟩⟩
    refine ⟨a + c, ?_⟩
    rw [map_add, ha, hc]
    exact (map_add _ _ _).symm

/-- For a surjective `R`-linear map `g : M → N` and any module `Q`, an element `z ∈ M ⊗ Q`
with `(g ⊗ 1)(z) = 0` is a finite sum of pure tensors `kᵣ ⊗ yᵣ` with each `kᵣ ∈ ker g`. -/
theorem rTensor_ker_decomp {R : Type w} [CommRing R] {M N : Type w} [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] (g : M →ₗ[R] N) (hg : Function.Surjective g)
    (Q : Type w) [AddCommGroup Q] [Module R Q] (z : TensorProduct R M Q)
    (hz : LinearMap.rTensor Q g z = 0) :
    ∃ S : Finset (M × Q), (∀ p ∈ S, g p.1 = 0) ∧ z = ∑ p ∈ S, p.1 ⊗ₜ[R] p.2 := by
  classical
  have hexact : Function.Exact (LinearMap.ker g).subtype g := LinearMap.exact_subtype_ker_map g
  have hT := rTensor_exact Q hexact hg
  rw [LinearMap.exact_iff] at hT
  have hmem : z ∈ LinearMap.range (LinearMap.rTensor Q (LinearMap.ker g).subtype) := by
    rw [← hT]; exact hz
  obtain ⟨w, hw⟩ := hmem
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset w
  let emb : (LinearMap.ker g × Q) ↪ (M × Q) :=
    ⟨fun p => ((p.1 : M), p.2), by
      intro a b hab
      simp only [Prod.mk.injEq, Subtype.coe_inj] at hab
      exact Prod.ext hab.1 hab.2⟩
  refine ⟨S.map emb, ?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_map, emb] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact q.1.2
  · rw [← hw, hS, map_sum, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [emb, LinearMap.rTensor_tmul, Submodule.subtype_apply]
    rfl

/-- Restricting a pure tensor `k ⊗ₜ y` along `ψ` where `k` restricts to `0` gives `0`. -/
theorem restrict_tmul_ker_eq_zero
    {A : PresheafOfModules.{w} (structureRingPresheaf 𝒪)}
    (X : PresheafOfModules.{w} (structureRingPresheaf 𝒪))
    {V : C} (k : A.obj (.op V)) (y : X.obj (.op V)) {W : C} (ψ : W ⟶ V)
    (hψ : (ConcreteCategory.hom (A.map ψ.op)) k = 0) :
    ((A ⊗ X).map ψ.op).hom (k ⊗ₜ[𝒪.obj (.op V)] y) = 0 := by
  have restrictedZero : (A.map ψ.op).hom k = (0 : A.obj (.op W)) := hψ
  exact (PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul ψ.op k y).trans
    ((congrArg (fun value : A.obj (.op W) =>
      value ⊗ₜ[𝒪.obj (.op W)] (X.map ψ.op).hom y) restrictedZero).trans
      (by simp only [TensorProduct.zero_tmul]; rfl))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [J.WEqualsLocallyBijective AddCommGrpCat]
    [HasWeakSheafify J AddCommGrpCat] in
/-- If `f` is locally injective and `f.app V` kills `k`, then the section `k ⊗ₜ y` restricts to
`0` on a covering sieve of `V`. -/
theorem c3_single
    {A B : PresheafOfModules.{w} (structureRingPresheaf 𝒪)} (f : A ⟶ B)
    (X : PresheafOfModules.{w} (structureRingPresheaf 𝒪))
    (hinj : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map f))
    {V : C} (k : A.obj (.op V)) (y : X.obj (.op V))
    (hk : (f.app (.op V)).hom k = 0) :
    Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).obj (A ⊗ X))
      (X := .op V)
      (k ⊗ₜ[𝒪.obj (.op V)] y) 0 ∈ J V := by
  have hcov : Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).obj A) (X := .op V)
      k 0 ∈ J V := by
    apply Presheaf.IsLocallyInjective.equalizerSieve_mem
      (φ := (PresheafOfModules.toPresheaf _).map f)
    change (f.app (.op V)).hom k = (f.app (.op V)).hom 0
    rw [hk, map_zero]
  refine J.superset_covering ?_ hcov
  intro W ψ hψ
  change (A.map ψ.op).hom k = (A.map ψ.op).hom 0 at hψ
  change ((A ⊗ X).map ψ.op).hom (k ⊗ₜ[𝒪.obj (.op V)] y) =
    ((A ⊗ X).map ψ.op).hom 0
  exact (restrict_tmul_ker_eq_zero 𝒪 X k y ψ
    (hψ.trans (map_zero _))).trans (map_zero _).symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [J.WEqualsLocallyBijective AddCommGrpCat]
    [HasWeakSheafify J AddCommGrpCat] in
/-- The equalizer sieve of `0` against itself is the whole (covering) sieve. -/
theorem eq_sieve_zero
    {A : PresheafOfModules.{w} (structureRingPresheaf 𝒪)}
    (X : PresheafOfModules.{w} (structureRingPresheaf 𝒪)) (V : C) :
    Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).obj (A ⊗ X)) (X := .op V)
      (0 : (A ⊗ X).obj (.op V)) 0 ∈ J V := by
  have h := Presheaf.equalizerSieve_self_eq_top
    (F := (PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).obj (A ⊗ X)) (X := .op V)
    (0 : (A ⊗ X).obj (.op V))
  exact h ▸ J.top_mem V

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [J.WEqualsLocallyBijective AddCommGrpCat]
    [HasWeakSheafify J AddCommGrpCat] in
/-- If `u` and `v` both restrict to `0` on covering sieves, so does `u + v`. -/
theorem eq_sieve_add
    {A : PresheafOfModules.{w} (structureRingPresheaf 𝒪)}
    (X : PresheafOfModules.{w} (structureRingPresheaf 𝒪))
    {V : C} (u v : (A ⊗ X).obj (.op V))
    (hu : Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).obj (A ⊗ X)) (X := .op V)
      u 0 ∈ J V)
    (hv : Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).obj (A ⊗ X)) (X := .op V)
      v 0 ∈ J V) :
    Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).obj (A ⊗ X)) (X := .op V)
      (u + v) 0 ∈ J V := by
  refine J.superset_covering ?_ (J.intersection_covering hu hv)
  intro W ψ ⟨h1, h2⟩
  change ((A ⊗ X).map ψ.op).hom u = ((A ⊗ X).map ψ.op).hom 0 at h1
  change ((A ⊗ X).map ψ.op).hom v = ((A ⊗ X).map ψ.op).hom 0 at h2
  change ((A ⊗ X).map ψ.op).hom (u + v) = ((A ⊗ X).map ψ.op).hom 0
  have firstZero := h1.trans (map_zero _)
  have secondZero := h2.trans (map_zero _)
  calc ((A ⊗ X).map ψ.op).hom (u + v)
      = ((A ⊗ X).map ψ.op).hom u + ((A ⊗ X).map ψ.op).hom v := map_add _ u v
    _ = (0 : _) + 0 := congrArg₂ (· + ·) firstZero secondZero
    _ = 0 := add_zero 0
    _ = ((A ⊗ X).map ψ.op).hom 0 := (map_zero _).symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [J.WEqualsLocallyBijective AddCommGrpCat]
    [HasWeakSheafify J AddCommGrpCat] in
/-- If `f` is locally injective, a finite sum of pure tensors `kᵣ ⊗ yᵣ` with each `kᵣ` in
`ker (f.app V)` restricts to `0` on a covering sieve of `V`. -/
theorem c3_sum
    {A B : PresheafOfModules.{w} (structureRingPresheaf 𝒪)} (f : A ⟶ B)
    (X : PresheafOfModules.{w} (structureRingPresheaf 𝒪))
    (hinj : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map f))
    {V : C} (S : Finset (A.obj (.op V) × X.obj (.op V)))
    (hS : ∀ p ∈ S, (f.app (.op V)).hom p.1 = 0) :
    Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).obj (A ⊗ X)) (X := .op V)
      (∑ p ∈ S, p.1 ⊗ₜ[𝒪.obj (.op V)] p.2) 0 ∈ J V := by
  classical
  induction S using Finset.induction with
  | empty => exact eq_sieve_zero 𝒪 X V
  | insert a s ha ih =>
    apply (congrArg (fun sectionValue : (A ⊗ X).obj (.op V) =>
      Presheaf.equalizerSieve
        (F := (PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).obj (A ⊗ X))
        (X := .op V) sectionValue 0 ∈ J V) (Finset.sum_insert ha)).mpr
    refine eq_sieve_add 𝒪 X _ _ ?_ (ih (fun p hp => hS p (Finset.mem_insert_of_mem hp)))
    exact c3_single 𝒪 f X hinj a.1 a.2 (hS a (Finset.mem_insert_self a s))

/-- Let `ρ : RU →+* RV` be a ring hom, `fU`, `fV` linear maps and `rA`, `rB`, `rX`
`ρ`-semilinear maps with `rB ∘ fU = fV ∘ rA`. Suppose `∑ᵢ fU(aᵢ) ⊗ₜ xᵢ = 0` already holds in
`P ⊗ XU` for a submodule `P` of `BU` containing every `fU(aᵢ)`, and that `rB` maps `P` into the
range of `fV`. Then `∑ᵢ rA(aᵢ) ⊗ₜ rX(xᵢ)` is a finite sum of pure tensors `kᵣ ⊗ₜ yᵣ` with each
`kᵣ ∈ ker fV`. -/
theorem sum_tmul_restrict_ker_decomp
    {RU RV : Type w} [CommRing RU] [CommRing RV] (ρ : RU →+* RV)
    {AU BU XU AV BV XV : Type w}
    [AddCommGroup AU] [AddCommGroup BU] [AddCommGroup XU]
    [AddCommGroup AV] [AddCommGroup BV] [AddCommGroup XV]
    [Module RU AU] [Module RU BU] [Module RU XU]
    [Module RV AV] [Module RV BV] [Module RV XV]
    (fU : AU →ₗ[RU] BU) (fV : AV →ₗ[RV] BV)
    (rA : AU →ₛₗ[ρ] AV) (rB : BU →ₛₗ[ρ] BV) (rX : XU →ₛₗ[ρ] XV)
    (hnat : ∀ a, rB (fU a) = fV (rA a))
    {ι : Type w} [Fintype ι] (a : ι → AU) (x : ι → XU)
    (P : Submodule RU BU)
    (hmemP : ∀ i, fU (a i) ∈ P)
    (hsum0 : ∑ i, (⟨fU (a i), hmemP i⟩ : ↥P) ⊗ₜ[RU] x i = 0)
    (hlift : ∀ b : ↥P, rB b ∈ LinearMap.range fV) :
    ∃ S : Finset (AV × XV), (∀ p ∈ S, fV p.1 = 0) ∧
      ∑ i, (rA (a i)) ⊗ₜ[RV] (rX (x i)) = ∑ p ∈ S, p.1 ⊗ₜ[RV] p.2 := by
  classical
  let σ : ↥P →ₛₗ[ρ] ↥(LinearMap.range fV) :=
    { toFun := fun b => ⟨rB b, hlift b⟩
      map_add' := by intro b c; apply Subtype.ext; simp [map_add]
      map_smul' := by intro r b; apply Subtype.ext; simp [map_smulₛₗ] }
  let Φ := TensorProduct.map σ rX
  have hΦ0 : Φ (∑ i, (⟨fU (a i), hmemP i⟩ : ↥P) ⊗ₜ[RU] x i) = 0 := by
    rw [hsum0, map_zero]
  have hΦval : Φ (∑ i, (⟨fU (a i), hmemP i⟩ : ↥P) ⊗ₜ[RU] x i)
      = ∑ i, (fV.rangeRestrict (rA (a i))) ⊗ₜ[RV] (rX (x i)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change TensorProduct.map σ rX (_ ⊗ₜ _) = _
    rw [TensorProduct.map_tmul]
    congr 1
    apply Subtype.ext
    exact hnat (a i)
  have hzero : ∑ i, (fV.rangeRestrict (rA (a i))) ⊗ₜ[RV] (rX (x i)) = 0 := by
    rw [← hΦval, hΦ0]
  set z' : TensorProduct RV AV XV := ∑ i, (rA (a i)) ⊗ₜ[RV] (rX (x i)) with hz'
  have hrt : LinearMap.rTensor XV fV.rangeRestrict z' = 0 := by
    rw [hz', map_sum, ← hzero]
    apply Finset.sum_congr rfl
    intro i _
    rw [LinearMap.rTensor_tmul]
  obtain ⟨S, hS, hSeq⟩ := rTensor_ker_decomp fV.rangeRestrict
    (LinearMap.surjective_rangeRestrict fV) XV z' hrt
  exact ⟨S, fun p hp => by simpa using congrArg Subtype.val (hS p hp), hSeq⟩

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [J.WEqualsLocallyBijective AddCommGrpCat]
    [HasWeakSheafify J AddCommGrpCat] in
/-- A finite intersection (over a `Finset`) of covering sieves is covering. -/
@[sga "4 II 1.1.1"]
theorem iInf_finset_covering {U : C} {β : Type w} (s : Finset β) (Gs : β → Sieve U)
    (hGs : ∀ b ∈ s, Gs b ∈ J U) : (⨅ b ∈ s, Gs b) ∈ J U := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.iInf_insert]
    exact J.intersection_covering (hGs b (Finset.mem_insert_self b s))
      (ih (fun x hx => hGs x (Finset.mem_insert_of_mem hx)))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasWeakSheafify J AddCommGrpCat] in
/-- Let `f` be a local isomorphism. For a section `z` of `A ⊗ X` over `U` annihilated by
`f ▷ X`, there is a covering sieve `G` of `U` such that on every arrow `ψ : V ⟶ U` of `G`, the
restriction `z|ψ` is a finite sum of pure tensors `kᵣ ⊗ yᵣ` with each `kᵣ ∈ ker (f.app V)`. -/
theorem exists_locally_ker_decomp
    {A B : PresheafOfModules.{w} (structureRingPresheaf 𝒪)} (f : A ⟶ B)
    (X : PresheafOfModules.{w} (structureRingPresheaf 𝒪))
    (hf : J.W ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map f))
    (U : C) (z : (A ⊗ X).obj (.op U))
    (hz : ((f ▷ X).app (.op U)).hom z = 0) :
    ∃ G : Sieve U, G ∈ J U ∧
      ∀ ⦃V : C⦄ (ψ : V ⟶ U), G.arrows ψ →
        ∃ S : Finset (A.obj (.op V) × X.obj (.op V)),
          (∀ p ∈ S, (f.app (.op V)).hom p.1 = 0) ∧
          ((A ⊗ X).map ψ.op).hom z = ∑ p ∈ S, p.1 ⊗ₜ[𝒪.obj (.op V)] p.2 := by
  classical
  have inst : J.WEqualsLocallyBijective AddCommGrpCat.{w} := inferInstance
  obtain ⟨_, hsurj⟩ :=
    (inst.iff ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map f)).1 hf
  obtain ⟨S₀, hS₀⟩ := TensorProduct.exists_finset z
  set aa : {p : A.obj (.op U) × X.obj (.op U) // p ∈ S₀} → A.obj (.op U) :=
    fun p => (p : A.obj (.op U) × X.obj (.op U)).1 with haa
  set xx : {p : A.obj (.op U) × X.obj (.op U) // p ∈ S₀} → X.obj (.op U) :=
    fun p => (p : A.obj (.op U) × X.obj (.op U)).2 with hxx
  have hzsum : z = ∑ i, aa i ⊗ₜ[𝒪.obj (.op U)] xx i := by
    rw [hS₀]
    exact (Finset.sum_coe_sort S₀ (fun p => p.1 ⊗ₜ[𝒪.obj (.op U)] p.2)).symm
  have hzero0 : ∑ i, (f.app (.op U)).hom (aa i) ⊗ₜ[𝒪.obj (.op U)] xx i = 0 := by
    have hcalc : ((f ▷ X).app (.op U)).hom z
        = ∑ i, (f.app (.op U)).hom (aa i) ⊗ₜ[𝒪.obj (.op U)] xx i := by
      rw [hzsum, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact ModuleCat.MonoidalCategory.whiskerRight_apply
        (f.app (.op U)) (X.obj (.op U)) (aa i) (xx i)
    rw [← hcalc, hz]
  set N₀ : Submodule (𝒪.obj (.op U)) (B.obj (.op U)) :=
    Submodule.span (𝒪.obj (.op U)) (Set.range (fun i => (f.app (.op U)).hom (aa i))) with hN₀
  have hmem0 : ∀ i, (f.app (.op U)).hom (aa i) ∈ N₀ :=
    fun i => Submodule.subset_span (Set.mem_range_self i)
  set t₀ : TensorProduct (𝒪.obj (.op U)) (↥N₀) (X.obj (.op U)) :=
    ∑ i, (⟨(f.app (.op U)).hom (aa i), hmem0 i⟩ : ↥N₀) ⊗ₜ[𝒪.obj (.op U)] xx i with ht₀
  have hsub : (LinearMap.rTensor (X.obj (.op U)) N₀.subtype) t₀
      = (LinearMap.rTensor (X.obj (.op U)) N₀.subtype) 0 := by
    rw [ht₀, map_sum, map_zero]
    simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply]
    exact hzero0
  obtain ⟨N', hN'fg, hle, hN'eq⟩ :=
    (Submodule.fg_span (Set.finite_range _)).exists_rTensor_fg_inclusion_eq hsub
  have hmemP : ∀ i, (f.app (.op U)).hom (aa i) ∈ N' := fun i => hle (hmem0 i)
  have hsum0 : ∑ i, (⟨(f.app (.op U)).hom (aa i), hmemP i⟩ : ↥N') ⊗ₜ[𝒪.obj (.op U)] xx i = 0 := by
    have e1 : (LinearMap.rTensor (X.obj (.op U)) (Submodule.inclusion hle)) t₀
        = ∑ i, (⟨(f.app (.op U)).hom (aa i), hmemP i⟩ : ↥N') ⊗ₜ[𝒪.obj (.op U)] xx i := by
      rw [ht₀, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [LinearMap.rTensor_tmul]
      rfl
    rw [← e1, hN'eq, map_zero]
  obtain ⟨gens, hgens⟩ := hN'fg
  set G : Sieve U := ⨅ g ∈ gens, Presheaf.imageSieve
    ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map f) g with hG
  have hGcov : G ∈ J U :=
    iInf_finset_covering gens _ (fun g _ => hsurj.imageSieve_mem g)
  refine ⟨G, hGcov, ?_⟩
  intro V ψ hψ
  have hliftgen : ∀ g ∈ gens, (B.map ψ.op).hom g ∈ LinearMap.range (f.app (.op V)).hom := by
    intro g hg
    have hgψ : (Presheaf.imageSieve
        ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map f) g).arrows ψ := by
      have hle2 : G ≤ Presheaf.imageSieve
          ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map f) g :=
        iInf_le_of_le g (iInf_le _ hg)
      exact hle2 _ hψ
    obtain ⟨a', ha'⟩ := hgψ
    exact ⟨a', ha'⟩
  have hlift : ∀ b : ↥N',
      (B.restrictₛₗ ψ.op) (b : B.obj (.op U)) ∈ LinearMap.range (f.app (.op V)).hom := by
    rintro ⟨b, hb⟩
    change (B.map ψ.op).hom b ∈ _
    rw [← hgens] at hb
    induction hb using Submodule.span_induction with
    | mem g hg => exact hliftgen g hg
    | zero => rw [map_zero]; exact zero_mem _
    | add u v hu hv ihu ihv => rw [map_add]; exact add_mem ihu ihv
    | smul r u hu ihu => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ ihu
  obtain ⟨S, hSker, hSdec⟩ := sum_tmul_restrict_ker_decomp
    (ρ := ((structureRingPresheaf 𝒪).map ψ.op).hom)
    (fU := (f.app (.op U)).hom) (fV := (f.app (.op V)).hom)
    (rA := A.restrictₛₗ ψ.op) (rB := B.restrictₛₗ ψ.op)
    (rX := X.restrictₛₗ ψ.op)
    (hnat := fun a => (PresheafOfModules.naturality_apply f ψ.op a).symm)
    (a := aa) (x := xx) (P := N') (hmemP := hmemP) (hsum0 := hsum0) (hlift := hlift)
  refine ⟨S, hSker, ?_⟩
  rw [hzsum, map_sum]
  have hterm : ∑ i, ((A ⊗ X).map ψ.op).hom (aa i ⊗ₜ[𝒪.obj (.op U)] xx i)
      = ∑ i, (A.restrictₛₗ ψ.op) (aa i) ⊗ₜ[𝒪.obj (.op V)]
          (X.restrictₛₗ ψ.op) (xx i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul ψ.op (aa i) (xx i)
  exact hterm.trans hSdec

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasWeakSheafify J AddCommGrpCat] in
/-- Let `f` be a local isomorphism. A section `z` of `A ⊗ X` over `U` annihilated by `f ▷ X`
restricts to `0` on a covering sieve of `U`. -/
theorem equalizerSieve_zero_mem_of_whiskerRight_eq_zero
    {A B : PresheafOfModules.{w} (structureRingPresheaf 𝒪)} (f : A ⟶ B)
    (X : PresheafOfModules.{w} (structureRingPresheaf 𝒪))
    (hf : J.W ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map f))
    (hinj : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map f))
    (U : C) (z : (A ⊗ X).obj (.op U))
    (hz : ((f ▷ X).app (.op U)).hom z = 0) :
    Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).obj (A ⊗ X)) (X := .op U)
      z 0 ∈ J U := by
  obtain ⟨G, hG, hGdec⟩ := exists_locally_ker_decomp 𝒪 f X hf U z hz
  apply J.transitive hG
  intro V ψ hψ
  obtain ⟨S, hSker, hSdec⟩ := hGdec ψ hψ
  refine J.superset_covering ?_ (c3_sum 𝒪 f X hinj S hSker)
  intro W φ hφ
  change ((A ⊗ X).map φ.op).hom
      (∑ p ∈ S, p.1 ⊗ₜ[𝒪.obj (.op V)] p.2) = ((A ⊗ X).map φ.op).hom 0 at hφ
  change ((A ⊗ X).map (φ ≫ ψ).op).hom z = ((A ⊗ X).map (φ ≫ ψ).op).hom 0
  have restrictComposition : ((A ⊗ X).map (φ ≫ ψ).op).hom z =
      ((A ⊗ X).map φ.op).hom (((A ⊗ X).map ψ.op).hom z) :=
    congrArg (fun morphism => (ConcreteCategory.hom morphism) z)
      (((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).obj (A ⊗ X)).map_comp
        ψ.op φ.op)
  exact (restrictComposition.trans
    ((congrArg (fun value => ((A ⊗ X).map φ.op).hom value) hSdec).trans
      (hφ.trans (map_zero _)))).trans (map_zero _).symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasWeakSheafify J AddCommGrpCat] in
/-- If the underlying presheaf map of `f` is a local isomorphism, then the underlying presheaf
map of `f ▷ X` is locally injective. -/
theorem W_whiskerRight_isLocallyInjective_of_W
    {A B : PresheafOfModules.{w} (structureRingPresheaf 𝒪)} (f : A ⟶ B)
    (X : PresheafOfModules.{w} (structureRingPresheaf 𝒪))
    (hf : J.W ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map f)) :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map (f ▷ X)) := by
  have inst : J.WEqualsLocallyBijective AddCommGrpCat.{w} := inferInstance
  obtain ⟨hinj, _⟩ :=
    (inst.iff ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map f)).1 hf
  apply Presheaf.IsLocallyInjective.mk
  intro U z₁ z₂ hz
  have hzeq : Presheaf.equalizerSieve z₁ z₂
      = Presheaf.equalizerSieve
          (F := (PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).obj (A ⊗ X)) (X := U)
          (z₁ - z₂) 0 := by
    apply Sieve.ext
    intro W ψ
    rw [Presheaf.equalizerSieve_apply, Presheaf.equalizerSieve_apply]
    constructor
    · intro h
      rw [map_sub, map_zero, sub_eq_zero]; exact h
    · intro h
      rw [map_sub, map_zero, sub_eq_zero] at h; exact h
  rw [hzeq]
  have hz' : ((f ▷ X).app U).hom (z₁ - z₂) = 0 :=
    (map_sub ((f ▷ X).app U).hom z₁ z₂).trans (sub_eq_zero.mpr hz)
  exact equalizerSieve_zero_mem_of_whiskerRight_eq_zero 𝒪 f X hf hinj (Opposite.unop U)
    (z₁ - z₂) (by simpa using hz')

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasWeakSheafify J AddCommGrpCat] in
/-- If the underlying presheaf map of `f` is a local isomorphism, then so is the underlying
presheaf map of `f ▷ X`. -/
theorem W_whiskerRight
    {A B : PresheafOfModules.{w} (structureRingPresheaf 𝒪)} (f : A ⟶ B)
    (X : PresheafOfModules.{w} (structureRingPresheaf 𝒪))
    (hf : J.W ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map f)) :
    J.W ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map (f ▷ X)) := by
  have inst : J.WEqualsLocallyBijective AddCommGrpCat.{w} := inferInstance
  obtain ⟨_, hsurj⟩ :=
    (inst.iff ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map f)).1 hf
  exact (inst.iff ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map (f ▷ X))).2
    ⟨W_whiskerRight_isLocallyInjective_of_W 𝒪 f X hf,
      W_whiskerRight_isLocallySurjective 𝒪 f X hsurj⟩

/-- If sheafification sends `f` and `g` to isomorphisms, then it sends `f ⊗ g` to one. -/
private theorem isIso_sheafify_map_tensorHom
    {A B A' B' : PresheafOfModules.{w} (structureRingPresheaf 𝒪)} (f : A ⟶ B) (g : A' ⟶ B')
    (hf : IsIso ((sheafify 𝒪 h𝒪).map f)) (hg : IsIso ((sheafify 𝒪 h𝒪).map g)) :
    IsIso ((sheafify 𝒪 h𝒪).map (PresheafOfModules.tensorHom f g)) := by
  let coefficientSheaf : Sheaf J CommRingCat.{w} :=
    ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩
  have mappedTensor : IsIso
      ((Functor.prod
          (PresheafOfModules.moduleSheafification (Osharp := coefficientSheaf) J (𝟙 𝒪))
          (PresheafOfModules.moduleSheafification (Osharp := coefficientSheaf) J (𝟙 𝒪)) ⋙
        Functor.uncurry.obj (Tensor.sheafTensor.{u, v, w, w, w} coefficientSheaf)).map
          ((f, g) : (A, A') ⟶ (B, B'))) :=
    ((Functor.uncurry.obj (Tensor.sheafTensor.{u, v, w, w, w} coefficientSheaf)).mapIso
      (Iso.prod
        (@asIso _ _ _ _ ((PresheafOfModules.moduleSheafification
          (Osharp := coefficientSheaf) J (𝟙 𝒪)).map f) hf)
        (@asIso _ _ _ _ ((PresheafOfModules.moduleSheafification
          (Osharp := coefficientSheaf) J (𝟙 𝒪)).map g) hg))).isIso_hom
  have presheafTensor := (NatIso.isIso_map_iff
    (PresheafOfModules.sheafificationTensorIso.{v, u, w, w, w}
      (Osharp := coefficientSheaf) J (𝟙 𝒪))
    ((f, g) : (A, A') ⟶ (B, B'))).mp mappedTensor
  have mapEquality := congrArg (sheafify 𝒪 h𝒪).map
    (PresheafOfModules.tensorBifunctor_uncurry_map f g)
  exact mapEquality ▸ presheafTensor

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- If sheafification sends `f` to an isomorphism, then it sends `f ⊗ 𝟙 X` to an
isomorphism. -/
theorem isIso_sheafify_map_whiskerRight
    {A B : PresheafOfModules.{w} (structureRingPresheaf 𝒪)} (f : A ⟶ B)
    (X : PresheafOfModules.{w} (structureRingPresheaf 𝒪))
    (hf : IsIso ((sheafify 𝒪 h𝒪).map f)) :
    IsIso ((sheafify 𝒪 h𝒪).map (PresheafOfModules.tensorHom f (𝟙 X))) := by
  let := Stacks.hasSheafCompose_forget₂_commRingCat.{w, v, u} J
  exact isIso_sheafify_map_tensorHom 𝒪 h𝒪 f (𝟙 X) hf inferInstance

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- If sheafification sends `f` to an isomorphism, then it sends `𝟙 X ⊗ f` to an
isomorphism. -/
theorem isIso_sheafify_map_whiskerLeft
    (X : PresheafOfModules.{w} (structureRingPresheaf 𝒪))
    {A B : PresheafOfModules.{w} (structureRingPresheaf 𝒪)} (f : A ⟶ B)
    (hf : IsIso ((sheafify 𝒪 h𝒪).map f)) :
    IsIso ((sheafify 𝒪 h𝒪).map (PresheafOfModules.tensorHom (𝟙 X) f)) := by
  let := Stacks.hasSheafCompose_forget₂_commRingCat.{w, v, u} J
  exact isIso_sheafify_map_tensorHom 𝒪 h𝒪 (𝟙 X) f inferInstance hf

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Sheafification inverts the tensor product of its units. -/
theorem tensor_sheafify_isIso
    (F' G' : PresheafOfModules.{w} (structureRingPresheaf 𝒪)) :
    IsIso (tensorSheafifyComparison 𝒪 h𝒪 F' G') := by
  let := Stacks.hasSheafCompose_forget₂_commRingCat.{w, v, u} J
  let coefficientSheaf : Sheaf J CommRingCat.{w} :=
    ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩
  exact PresheafOfModules.isIso_sheafification_tensor_units.{v, u, w, w, w}
    (Osharp := coefficientSheaf) J (𝟙 𝒪) F' G'

/-- The canonical isomorphism of sheaves of `𝒪`-modules
`(F' ⊗ G')^# ≅ ((F')^# ⊗ (G')^#)^#` induced by the sheafification units. -/
@[stacks 05NA]
noncomputable def tensorSheafifyIso
    (F' G' : PresheafOfModules.{w} (structureRingPresheaf 𝒪)) :
    (sheafify 𝒪 h𝒪).obj (PresheafOfModules.tensorObj (O := 𝒪) F' G') ≅
      (sheafify 𝒪 h𝒪).obj
        (PresheafOfModules.tensorObj (O := 𝒪)
          ((SheafOfModules.forget (structureSheaf 𝒪 h𝒪) ⋙
              PresheafOfModules.restrictScalars (𝟙 (structureSheaf 𝒪 h𝒪).obj)).obj
            ((sheafify 𝒪 h𝒪).obj F'))
          ((SheafOfModules.forget (structureSheaf 𝒪 h𝒪) ⋙
              PresheafOfModules.restrictScalars (𝟙 (structureSheaf 𝒪 h𝒪).obj)).obj
            ((sheafify 𝒪 h𝒪).obj G'))) :=
  have := tensor_sheafify_isIso 𝒪 h𝒪 F' G'
  asIso (tensorSheafifyComparison 𝒪 h𝒪 F' G')

end Stacks.SheafOfModules.TensorSheafification

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))

/-- The monoidal structure on presheaves of modules over the structure sheaf. It is the
monoidal structure over the underlying presheaf of rings, which is literally the same
category; only the way the index is spelled differs. -/
noncomputable local instance monoidalCategoryPresheafOfModules : MonoidalCategory
    (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj) :=
      by
  change MonoidalCategory (PresheafOfModules.{w}
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  infer_instance

/-- That monoidal structure is symmetric, because `O` is commutative. -/
noncomputable local instance symmetricCategoryPresheafOfModules : SymmetricCategory
    (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj) :=
      by
  change SymmetricCategory (PresheafOfModules.{w}
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  infer_instance

end Stacks.SheafOfModules
