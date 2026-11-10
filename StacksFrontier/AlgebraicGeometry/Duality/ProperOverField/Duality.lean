module

public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import StacksFrontier.Algebra.Homology.DerivedCategory.HomToSingleInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsLinear
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.LerayOverField
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.CategoryTheory.Shift.ShiftSequenceShiftedHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Duality for proper schemes over a field

Let `X` be a proper scheme over a field `k`, with structure morphism `f : X ⟶ Spec k`, and let
`ω_X^• = a(𝒪_{Spec k})` be its relative dualizing complex, the value at `𝒪_{Spec k}` of the right
adjoint `a` of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_{Spec k})`. Part (5) of [Stacks, Tag 0FVV] asserts
that for `K` in `D_QCoh(𝒪_X)` there are functorial isomorphisms
`Ext^i_X(K, ω_X^•) = Hom_k(H^{-i}(X, K), k)`, compatible with shifts and distinguished triangles.

The isomorphism is `α ↦ t ∘ H^{-i}(X, α)`, where `H^n(X, -) = H^n ∘ RΓ(X, -)` is `k`-linear
hypercohomology and `t : H⁰(X, ω_X^•) ⟶ k` is the trace, the degree-zero cohomology of the counit
`Rf_* ω_X^• ⟶ 𝒪_{Spec k}` read through `RΓ(X, -) = RΓ(Spec k, Rf_* -)` and `Γ(Spec k, 𝒪) = k`.
Functoriality and the compatibility with shifts and triangles are then formal. Bijectivity is the
source's argument: in degree zero, `Hom(K, ω_X^•) = Hom(Rf_* K, 𝒪_{Spec k})` by adjunction, this is
`Hom_{D(k)}(RΓ(X, K), k)` because `RΓ(Spec k, -)` is fully faithful on `D_QCoh(𝒪_{Spec k})`
([Stacks, Tag 06Z0]) and the Leray isomorphism, and that is `Hom_k(H⁰(X, K), k)` since `k` is an
injective `k`-module; the other degrees follow by shifting.

## Main definitions

* `Stacks.Duality.traceOverField` — the trace `t : H⁰(X, ω_X^•) ⟶ k`.
* `Stacks.Duality.dualityPairing` — `α ↦ t ∘ H^{-i}(X, α)`.
* `Stacks.Duality.dualityLinearMap` — the same as a `k`-linear map.
* `Stacks.Duality.dualityEquiv` — **part (5) of [Stacks, Tag 0FVV]**, the `k`-linear isomorphism
  `Ext^i_X(K, ω_X^•) ≃ Hom_k(H^{-i}(X, K), k)` for `K` in `D_QCoh(𝒪_X)`.

## Main results

* `Stacks.Duality.bijective_dualityPairing` — the pairing is bijective in every degree.
* `Stacks.Duality.dualityEquiv_comp` — naturality in `K`.
* `Stacks.Duality.dualityEquiv_shiftedHomComp` — compatibility with composition by shifted
  morphisms `Ext^j_X(L, K)`, which contains the compatibility with shifts
  (`Stacks.Duality.dualityLinearMap_shift`) and with distinguished triangles
  (`Stacks.Duality.dualityLinearMap_triangle`).

## Implementation notes

The derived categories are the locally small models, at which `AlgebraicGeometry.derivedTilde` is
an equivalence and the right adjoint of [Stacks, Tag 0A9E] exists. `k` acts on `Ext` through the
`k`-linear structure `AlgebraicGeometry.Scheme.linearOver f` on `𝒪_X`-modules.

## References

* [Stacks Project, Tag 0FVV](https://stacks.math.columbia.edu/tag/0FVV)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

/-- For a quasi-compact quasi-separated morphism to a quasi-compact quasi-separated scheme, the
restriction of `Rf_*` to `D_QCoh` has a right adjoint ([Stacks, Tag 0A9E]); the source is
quasi-compact and quasi-separated because the morphism and the target are. -/
instance isLeftAdjoint_quasiCoherentDerivedPushforward_of_quasiCompact {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent) :
    (quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint :=
  have := QuasiCompact.compactSpace_of_compactSpace f
  have := quasiSeparatedSpace_of_quasiSeparated f
  inferInstance

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- The relative dualizing complex `ω_X^• = a(𝒪_{Spec k})` of `f : X ⟶ Spec k`. -/
local notation "ωX" =>
  relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))

/-- Degree-zero cohomology on `D(k)`. -/
local notation "H⁰" => DerivedCategory.homologyFunctor (ModuleCat k) 0

/-- Degree-zero cohomology of `Γ(Spec k, 𝒪)` placed in degree zero is `k`. -/
def specFieldUnitHomologyIso :
    (H⁰).obj ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
      ((globalSectionsOver (𝟙 (Spec (.of k)))).obj
        (SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf))) ≅ ModuleCat.of k k :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).app _ ≪≫
    (globalSectionsOverSpecFieldUnitEquiv k).toModuleIso

/-- **The trace map** `t : H⁰(X, ω_X^•) ⟶ k`: degree-zero cohomology of the counit
`Rf_* ω_X^• ⟶ 𝒪_{Spec k}` of `Rf_* ⊣ a`, read through `RΓ(X, -) ≅ RΓ(Spec k, Rf_* -)` and
`Γ(Spec k, 𝒪) = k`. -/
def traceOverField :
    (H⁰).obj ((derivedGlobalSectionsOver f).obj (ωX).obj) ⟶ ModuleCat.of k k :=
  (H⁰).map ((derivedGlobalSectionsOverLerayIso f).hom.app (ωX).obj ≫
      (derivedGlobalSectionsOver (𝟙 (Spec (.of k)))).map
        (relativeDualizingComplexTrace f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))).hom ≫
      (derivedGlobalSectionsOverSpecFieldSingleIso k _).hom) ≫
    (specFieldUnitHomologyIso (k := k)).hom

/-- The adjunction `Rf_* ⊣ a` on Hom-sets of `D(𝒪_X)`: a map `L ⟶ ω_X^•` corresponds to the map
`Rf_* L ⟶ 𝒪_{Spec k}` obtained by composing its direct image with the trace. -/
@[sga "5 III 6.1" "(6.1.1), special case"]
private theorem bijective_derivedPushforward_map_comp_trace (L : quasiCoherentDerivedCategory X) :
    Function.Bijective (fun g : L.obj ⟶ (ωX).obj ↦ (derivedPushforward f).map g ≫
      (relativeDualizingComplexTrace f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))).hom) := by
  let e := ((ObjectProperty.fullyFaithfulι _).homEquiv.symm.trans
    ((relativeDualizingComplexHomEquiv f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k))) L).trans
        (ObjectProperty.fullyFaithfulι _).homEquiv))
  convert e.bijective using 1
  funext g
  simp [e, relativeDualizingComplexHomEquiv_apply]
  rfl

/-- Postcomposition with an isomorphism is bijective. -/
private theorem bijective_comp_iso {C : Type*} [Category C] {A B B' : C} (e : B ⟶ B') [IsIso e] :
    Function.Bijective (fun g : A ⟶ B ↦ g ≫ e) :=
  ⟨fun _ _ h ↦ (cancel_mono e).1 h, fun g ↦ ⟨g ≫ inv e, by simp⟩⟩

/-- Precomposition with an isomorphism is bijective. -/
private theorem bijective_iso_comp {C : Type*} [Category C] {A A' B : C} (e : A ⟶ A') [IsIso e] :
    Function.Bijective (fun g : A' ⟶ B ↦ e ≫ g) :=
  ⟨fun _ _ h ↦ (cancel_epi e).1 h, fun g ↦ ⟨inv e ≫ g, by simp⟩⟩

/-- Rearranging a composite along a commutative square `a ≫ λ' = λ ≫ G(r)`. -/
private theorem comp_map_comp_eq {C D E : Type*} [Category C] [Category D] [Category E]
    (G : C ⥤ D) (H : D ⥤ E) {A A' : D} {P P' O : C} {T : D} {Z : E}
    (a : A ⟶ A') (lam : A ⟶ G.obj P) (lam' : A' ⟶ G.obj P') (r : P ⟶ P') (e : P' ⟶ O)
    (s : G.obj O ⟶ T) (c : H.obj T ⟶ Z) (h : a ≫ lam' = lam ≫ G.map r) :
    H.map a ≫ (H.map (lam' ≫ G.map e ≫ s) ≫ c) =
      H.map lam ≫ (H.map (G.map (r ≫ e) ≫ s) ≫ c) := by
  rw [← Category.assoc, ← H.map_comp, ← Category.assoc a, h]
  simp

/-- **Degree-zero duality.** For `L` in `D_QCoh(𝒪_X)`, a map `L ⟶ ω_X^•` is determined by the
linear form `H⁰(X, L) ⟶ H⁰(X, ω_X^•) ⟶ k` it induces, and every linear form arises. -/
theorem bijective_homologyFunctor_map_comp_traceOverField (L : quasiCoherentDerivedCategory X) :
    Function.Bijective (fun g : L.obj ⟶ (ωX).obj ↦
      (H⁰).map ((derivedGlobalSectionsOver f).map g) ≫ traceOverField f) := by
  let ε := (relativeDualizingComplexTrace f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k))))
  let G := derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of k)))
  let sI := derivedGlobalSectionsOverSpecFieldSingleIso k
    (SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf)
  let c := (specFieldUnitHomologyIso (k := k)).hom
  -- the four bijective steps
  have h₁ := bijective_derivedPushforward_map_comp_trace f L
  have h₂ : Function.Bijective (fun β : (derivedPushforward f).obj L.obj ⟶
      (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k))).obj ↦ G.map β) := by
    have := derivedGlobalSectionsQuasicoherent_isEquivalence (CommRingCat.of k)
    have hF := (Functor.FullyFaithful.ofFullyFaithful
      (derivedGlobalSectionsQuasicoherent (CommRingCat.of k))).map_bijective
      ((quasiCoherentDerivedPushforward f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj L)
      (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))
    have := hF.comp (ObjectProperty.fullyFaithfulι _).homEquiv.symm.bijective
    exact this
  have h₃ := bijective_comp_iso (A := G.obj ((derivedPushforward f).obj L.obj)) sI.hom
  have : Injective ((globalSectionsOver (𝟙 (Spec (.of k)))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf)) :=
    Module.injective_object_of_injective_module k ((globalSectionsOver (𝟙 (Spec (.of k)))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf))
      (inj := Module.injective_of_isSemisimpleRing k _)
  have h₄ : Function.Bijective (fun m : G.obj ((derivedPushforward f).obj L.obj) ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
        ((globalSectionsOver (𝟙 (Spec (.of k)))).obj
          (SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf)) ↦ (H⁰).map m ≫ c) :=
    (bijective_comp_iso c).comp
      (DerivedCategory.bijective_homologyFunctor_map_singleFunctor_of_injective _ _)
  have h₅ := bijective_iso_comp (B := ModuleCat.of k k)
    ((H⁰).map ((derivedGlobalSectionsOverLerayIso f).hom.app L.obj))
  convert h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁))) using 1
  funext g
  change (H⁰).map ((derivedGlobalSectionsOver f).map g) ≫ traceOverField f =
    (H⁰).map ((derivedGlobalSectionsOverLerayIso f).hom.app L.obj) ≫
      ((H⁰).map (G.map ((derivedPushforward f).map g ≫ ε.hom) ≫ sI.hom) ≫ c)
  rw [traceOverField]
  exact comp_map_comp_eq G (H⁰) ((derivedGlobalSectionsOver f).map g)
    ((derivedGlobalSectionsOverLerayIso f).hom.app L.obj)
    ((derivedGlobalSectionsOverLerayIso f).hom.app (ωX).obj) ((derivedPushforward f).map g)
    ε.hom sI.hom c ((derivedGlobalSectionsOverLerayIso f).hom.naturality g)

/-! ### The duality pairing in every degree -/

/-- `H⁰(X, -) = H⁰ ∘ RΓ(X, -)` on `D(𝒪_X)`, with values in `k`-vector spaces; its shift sequence
is `H^n(X, -) = H^n ∘ RΓ(X, -)`. -/
local notation "HX" => derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat k) 0

/-- **The duality pairing.** For `α ∈ Ext^i_X(K, ω_X^•)` the linear form
`H^{-i}(X, K) ⟶ H⁰(X, ω_X^•) ⟶ k` given by the map `α` induces on hypercohomology followed by
the trace. -/
def dualityPairing (K : DerivedCategory X.Modules) (i : ℤ)
    (α : DerivedCategory.Ext K (ωX).obj i) :
    (DerivedCategory.homologyFunctor (ModuleCat k) (-i)).obj
      ((derivedGlobalSectionsOver f).obj K) ⟶ ModuleCat.of k k :=
  (HX).shiftMap α (-i) 0 (by omega) ≫ traceOverField f

/-- **Naturality of the duality pairing in the complex.** -/
theorem dualityPairing_comp {K L : DerivedCategory X.Modules} (g : K ⟶ L) (i : ℤ)
    (α : DerivedCategory.Ext L (ωX).obj i) :
    dualityPairing f K i (g ≫ α) =
      (DerivedCategory.homologyFunctor (ModuleCat k) (-i)).map
        ((derivedGlobalSectionsOver f).map g) ≫ dualityPairing f L i α := by
  exact Functor.shiftMap_comp'_assoc (HX) g α (-i) 0 (by omega) (traceOverField f)

/-- **The duality pairing is compatible with composition by shifted morphisms.** For
`β ∈ Ext^j_X(L, K)` and `α ∈ Ext^i_X(K, ω_X^•)`, the pairing of the Yoneda product
`β.comp α ∈ Ext^{i+j}_X(L, ω_X^•)` is the pairing of `α` precomposed with the map
`H^{-(i+j)}(X, L) ⟶ H^{-i}(X, K)` that `β` induces on hypercohomology. -/
theorem dualityPairing_shiftedHomComp {L K : DerivedCategory X.Modules} {i j c : ℤ}
    (β : DerivedCategory.Ext L K j) (α : DerivedCategory.Ext K (ωX).obj i) (h : i + j = c) :
    dualityPairing f L c (β.comp α h) =
      (HX).shiftMap β (-c) (-i) (by omega) ≫ dualityPairing f K i α := by
  exact (congrArg (· ≫ traceOverField f)
    (Functor.shiftMap_shiftedHomComp (HX) β α h (-c) (-i) 0 (by omega) (by omega))).trans
      (Category.assoc _ _ _)

/-- On a morphism `g : K ⟶ ω_X^•` of degree zero the pairing is `H⁰(X, g)` followed by the
trace. -/
theorem dualityPairing_mk₀ {K : DerivedCategory X.Modules} (g : K ⟶ (ωX).obj) :
    dualityPairing f K 0 (ShiftedHom.mk₀ (0 : ℤ) rfl g) =
      (DerivedCategory.homologyFunctor (ModuleCat k) 0).map
        ((derivedGlobalSectionsOver f).map g) ≫ traceOverField f := by
  rw [dualityPairing]
  have := Functor.shiftMap_mk₀ (HX) g (0 : ℤ)
  exact congrArg (· ≫ traceOverField f) this

/-- **Duality in degree zero, for the pairing.** -/
theorem bijective_dualityPairing_zero (L : quasiCoherentDerivedCategory X) :
    Function.Bijective (dualityPairing f L.obj 0) := by
  have h := (bijective_homologyFunctor_map_comp_traceOverField f L).comp
    (ShiftedHom.homEquiv (X := L.obj) (Y := (ωX).obj) (0 : ℤ) rfl).symm.bijective
  have key : ∀ α, dualityPairing f L.obj 0 α =
      ((fun g : L.obj ⟶ (ωX).obj ↦ (H⁰).map ((derivedGlobalSectionsOver f).map g) ≫
        traceOverField f) ∘ (ShiftedHom.homEquiv (0 : ℤ) rfl).symm) α := by
    intro α
    obtain ⟨g, rfl⟩ :=
      (ShiftedHom.homEquiv (X := L.obj) (Y := (ωX).obj) (0 : ℤ) rfl).surjective α
    exact (dualityPairing_mk₀ f g).trans (by simp only [Function.comp_apply,
      Equiv.symm_apply_apply])
  rw [show dualityPairing f L.obj 0 = _ from funext key]
  exact h

/-- **Duality in every degree, for the pairing.** For `K` in `D_QCoh(𝒪_X)` and every `i`, the
pairing `Ext^i_X(K, ω_X^•) ⟶ Hom_k(H^{-i}(X, K), k)` is bijective. It is reduced to degree zero
by pairing against the identity of `K⟦-i⟧`, regarded as an element of `Ext^{-i}_X(K⟦-i⟧, K)`. -/
theorem bijective_dualityPairing (K : quasiCoherentDerivedCategory X) (i : ℤ) :
    Function.Bijective (dualityPairing f K.obj i) := by
  have hs := DerivedCategoryB.derivedCategoryB_isStableUnderShift (A := X.Modules) _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)
  let K' : quasiCoherentDerivedCategory X :=
    ⟨K.obj⟦-i⟧, ObjectProperty.le_shift _ (-i) K.obj K.property⟩
  let β : DerivedCategory.Ext K'.obj K.obj (-i) := 𝟙 _
  have hcomp : Function.Bijective (fun α : DerivedCategory.Ext K.obj (ωX).obj i ↦
      β.comp α (add_neg_cancel i)) := by
    have e₁ := (Functor.FullyFaithful.ofFullyFaithful
      (shiftFunctor (DerivedCategory X.Modules) (-i))).map_bijective K.obj ((ωX).obj⟦i⟧)
    have e₂ := bijective_comp_iso (A := K.obj⟦-i⟧)
      ((shiftFunctorAdd' (DerivedCategory X.Modules) i (-i) 0 (add_neg_cancel i)).inv.app
        (ωX).obj)
    have e₃ := bijective_iso_comp (B := (ωX).obj⟦(0 : ℤ)⟧) (𝟙 (K.obj⟦-i⟧))
    exact e₃.comp (e₂.comp e₁)
  have hshift : IsIso ((HX).shiftMap β (-0) (-i) (by omega)) := by
    dsimp only [Functor.shiftMap, β]
    infer_instance
  have key : (fun α ↦ dualityPairing f K'.obj 0 (β.comp α (add_neg_cancel i))) =
      (fun φ ↦ (HX).shiftMap β (-0) (-i) (by omega) ≫ φ) ∘ dualityPairing f K.obj i := by
    funext α
    exact dualityPairing_shiftedHomComp f β α (add_neg_cancel i)
  have h := (bijective_dualityPairing_zero f K').comp hcomp
  rw [show (dualityPairing f K'.obj 0 ∘ fun α ↦ β.comp α (add_neg_cancel i)) =
    (fun α ↦ dualityPairing f K'.obj 0 (β.comp α (add_neg_cancel i))) from rfl, key] at h
  have hc : Function.Bijective
      (fun φ : (DerivedCategory.homologyFunctor (ModuleCat k) (-i)).obj
          ((derivedGlobalSectionsOver f).obj K.obj) ⟶ ModuleCat.of k k ↦
        (HX).shiftMap β (-0) (-i) (by omega) ≫ φ) :=
    @bijective_iso_comp _ _ _ _ _ _ hshift
  exact (Function.Bijective.of_comp_iff' hc _).1 h

omit [IsProper f] in
/-- `H^n(X, -)` is `k`-linear. -/
theorem linear_shift_derivedGlobalSectionsOver_comp_homologyFunctor (n : ℤ) :
    letI := Scheme.linearOver f
    Functor.Linear k ((HX).shift n) := by
  let := Scheme.linearOver f
  have h₁ : Functor.Linear k (derivedGlobalSectionsOver f) := derivedGlobalSectionsOver_linearOver f
  have h₂ : Functor.Linear k (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n) :=
    DerivedCategory.homologyFunctor_linear k n
  exact inferInstanceAs (Functor.Linear k
    (derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat k) n))

omit [IsProper f] in
/-- Additivity of the pairing in the shifted morphism, for any target `Z` and linear form `t`. -/
theorem shiftMap_comp_hom_add {K Z : DerivedCategory X.Modules} {i : ℤ}
    (t : ((HX).shift (0 : ℤ)).obj Z ⟶ ModuleCat.of k k)
    (α₁ α₂ : DerivedCategory.Ext K Z i) :
    ((HX).shiftMap (α₁ + α₂) (-i) 0 (by omega) ≫ t).hom =
      ((HX).shiftMap α₁ (-i) 0 (by omega) ≫ t).hom +
        ((HX).shiftMap α₂ (-i) 0 (by omega) ≫ t).hom := by
  simp only [Functor.shiftMap, Functor.map_add]
  rw [Preadditive.add_comp, Preadditive.add_comp, ModuleCat.hom_add]

omit [IsProper f] in
/-- Linearity of the pairing in the shifted morphism, for any target `Z` and linear form `t`. -/
theorem shiftMap_comp_hom_smul {K Z : DerivedCategory X.Modules} {i : ℤ}
    (t : ((HX).shift (0 : ℤ)).obj Z ⟶ ModuleCat.of k k) (c : k)
    (α : letI := Scheme.linearOver f; DerivedCategory.Ext K Z i) :
    letI := Scheme.linearOver f
    ((HX).shiftMap (c • α) (-i) 0 (by omega) ≫ t).hom =
      c • ((HX).shiftMap α (-i) 0 (by omega) ≫ t).hom := by
  let := Scheme.linearOver f
  have := linear_shift_derivedGlobalSectionsOver_comp_homologyFunctor f (-i)
  simp only [Functor.shiftMap, Functor.map_smul]
  rw [Linear.smul_comp, Linear.smul_comp, ModuleCat.hom_smul]

/-- **The duality map** `Ext^i_X(K, ω_X^•) ⟶ Hom_k(H^{-i}(X, K), k)`, `α ↦ t ∘ H^{-i}(X, α)`, as a
`k`-linear map. -/
def dualityLinearMap (K : DerivedCategory X.Modules) (i : ℤ) :
    letI := Scheme.linearOver f
    DerivedCategory.Ext K (ωX).obj i →ₗ[k]
      ((DerivedCategory.homologyFunctor (ModuleCat k) (-i)).obj
        ((derivedGlobalSectionsOver f).obj K) →ₗ[k] k) :=
  let := Scheme.linearOver f
  { toFun α := (dualityPairing f K i α).hom
    map_add' α₁ α₂ := shiftMap_comp_hom_add f (traceOverField f) α₁ α₂
    map_smul' c α := shiftMap_comp_hom_smul f (traceOverField f) c α }

/-- `dualityLinearMap f K i` sends `α` to the underlying linear map of `dualityPairing f K i α`. -/
@[simp]
theorem dualityLinearMap_apply (K : DerivedCategory X.Modules) (i : ℤ)
    (α : DerivedCategory.Ext K (ωX).obj i) :
    letI := Scheme.linearOver f
    dualityLinearMap f K i α = (dualityPairing f K i α).hom := by
  rfl

/-- **The duality isomorphisms.** Let `X` be a proper scheme over a field `k` and
`ω_X^• = a(𝒪_{Spec k})` its relative dualizing complex. For `K` in `D_QCoh(𝒪_X)` and every `i`
there is a `k`-linear isomorphism `Ext^i_X(K, ω_X^•) ≅ Hom_k(H^{-i}(X, K), k)`, sending `α` to
`t ∘ H^{-i}(X, α)` with `t : H⁰(X, ω_X^•) ⟶ k` the trace (`Stacks.Duality.traceOverField`); it is
natural in `K` (`Stacks.Duality.dualityEquiv_comp`) and compatible with shifts and distinguished
triangles (`Stacks.Duality.dualityEquiv_shiftedHomComp`,
`Stacks.Duality.dualityEquiv_triangle`). -/
@[stacks 0FVV "part (5): the isomorphisms Ext^i_X(K, ω_X) = Hom_k(H^{-i}(X, K), k)"]
def dualityEquiv (K : quasiCoherentDerivedCategory X) (i : ℤ) :
    letI := Scheme.linearOver f
    DerivedCategory.Ext K.obj (ωX).obj i ≃ₗ[k]
      ((DerivedCategory.homologyFunctor (ModuleCat k) (-i)).obj
        ((derivedGlobalSectionsOver f).obj K.obj) →ₗ[k] k) :=
  let := Scheme.linearOver f
  LinearEquiv.ofBijective (dualityLinearMap f K.obj i)
    ((ModuleCat.homLinearEquiv (S := k)).bijective.comp (bijective_dualityPairing f K i))

/-- The duality isomorphism is the duality map. -/
theorem dualityEquiv_apply (K : quasiCoherentDerivedCategory X) (i : ℤ)
    (α : DerivedCategory.Ext K.obj (ωX).obj i)
    (x : (DerivedCategory.homologyFunctor (ModuleCat k) (-i)).obj
      ((derivedGlobalSectionsOver f).obj K.obj)) :
    letI := Scheme.linearOver f
    dualityEquiv f K i α x = (dualityPairing f K.obj i α).hom x := by
  rfl

/-- **Part (5) of [Stacks, Tag 0FVV], functoriality.** The duality isomorphisms are natural in
`K`: for `g : K ⟶ L` in `D(𝒪_X)` and `α ∈ Ext^i_X(L, ω_X^•)`, the linear form attached to
`g ≫ α` is the one attached to `α` precomposed with `H^{-i}(X, g)`. -/
@[stacks 0FVV "part (5): the isomorphisms are functorial in K"]
theorem dualityEquiv_comp (K L : quasiCoherentDerivedCategory X) (i : ℤ) (g : K.obj ⟶ L.obj)
    (α : DerivedCategory.Ext L.obj (ωX).obj i)
    (x : (DerivedCategory.homologyFunctor (ModuleCat k) (-i)).obj
      ((derivedGlobalSectionsOver f).obj K.obj)) :
    letI := Scheme.linearOver f
    dualityEquiv f K i (g ≫ α) x =
      dualityEquiv f L i α
        ((DerivedCategory.homologyFunctor (ModuleCat k) (-i)).map
          ((derivedGlobalSectionsOver f).map g) x) := by
  rw [dualityEquiv_apply, dualityEquiv_apply, dualityPairing_comp]
  rfl

/-- **Part (5) of [Stacks, Tag 0FVV], compatibility with shifted morphisms.** For
`β ∈ Ext^j_X(L, K)` and `α ∈ Ext^i_X(K, ω_X^•)`, the linear form on `H^{-(i+j)}(X, L)` attached to
the product `β.comp α ∈ Ext^{i+j}_X(L, ω_X^•)` is the one attached to `α` precomposed with the map
`H^{-(i+j)}(X, L) ⟶ H^{-i}(X, K)` induced by `β`. Taking for `β` the identity of `K⟦n⟧` gives
compatibility with shifts (`Stacks.Duality.dualityLinearMap_shift`), and taking for `β` the third
morphism of a distinguished triangle gives compatibility with its connecting maps
(`Stacks.Duality.dualityLinearMap_triangle`). -/
@[stacks 0FVV "part (5): compatibility with shifts and distinguished triangles"]
theorem dualityEquiv_shiftedHomComp (K L : quasiCoherentDerivedCategory X) {i j c : ℤ}
    (β : DerivedCategory.Ext L.obj K.obj j) (α : DerivedCategory.Ext K.obj (ωX).obj i)
    (h : i + j = c)
    (x : (DerivedCategory.homologyFunctor (ModuleCat k) (-c)).obj
      ((derivedGlobalSectionsOver f).obj L.obj)) :
    letI := Scheme.linearOver f
    dualityEquiv f L c (β.comp α h) x =
      dualityEquiv f K i α ((HX).shiftMap β (-c) (-i) (by omega) x) := by
  simp only [dualityEquiv_apply]
  rw [dualityPairing_shiftedHomComp f β α h]
  rfl

/-- **Compatibility of the duality map with shifts.** Under `Ext^{i+n}_X(K⟦n⟧, ω_X^•) =
Ext^i_X(K, ω_X^•)` (composition with the identity of `K⟦n⟧`, an element of `Ext^n_X(K⟦n⟧, K)`) and
the canonical isomorphism `H^{-(i+n)}(X, K⟦n⟧) ≅ H^{-i}(X, K)`, the duality maps of `K⟦n⟧` and
of `K` agree. -/
@[stacks 0FVV "part (5): compatibility with shifts"]
theorem dualityLinearMap_shift (K : DerivedCategory X.Modules) (i n : ℤ)
    (α : DerivedCategory.Ext K (ωX).obj i)
    (x : (DerivedCategory.homologyFunctor (ModuleCat k) (-(i + n))).obj
      ((derivedGlobalSectionsOver f).obj (K⟦n⟧))) :
    letI := Scheme.linearOver f
    dualityLinearMap f (K⟦n⟧) (i + n)
        (ShiftedHom.comp (𝟙 (K⟦n⟧)) α rfl) x =
      dualityLinearMap f K i α
        (((HX).shiftIso n (-(i + n)) (-i) (by omega)).hom.app K x) := by
  rw [dualityLinearMap_apply, dualityLinearMap_apply,
    dualityPairing_shiftedHomComp f _ α rfl, Functor.shiftMap_id]
  rfl

/-- **Compatibility of the duality map with distinguished triangles.** For a triangle
`K ⟶ L ⟶ M ⟶ K⟦1⟧` of `D(𝒪_X)`, the duality maps intertwine composition with its third morphism,
`Ext^i_X(K, ω_X^•) ⟶ Ext^{i+1}_X(M, ω_X^•)`, and the connecting morphism
`H^{-(i+1)}(X, M) ⟶ H^{-i}(X, K)` of the long exact cohomology sequence. -/
@[stacks 0FVV "part (5): compatibility with distinguished triangles"]
theorem dualityLinearMap_triangle (T : Pretriangulated.Triangle (DerivedCategory X.Modules))
    (i : ℤ) (α : DerivedCategory.Ext T.obj₁ (ωX).obj i)
    (x : (DerivedCategory.homologyFunctor (ModuleCat k) (-(i + 1))).obj
      ((derivedGlobalSectionsOver f).obj T.obj₃)) :
    letI := Scheme.linearOver f
    dualityLinearMap f T.obj₃ (i + 1)
        (ShiftedHom.comp (T.mor₃ : DerivedCategory.Ext T.obj₃ T.obj₁ 1) α rfl) x =
      dualityLinearMap f T.obj₁ i α
        ((HX).homologySequenceδ T (-(i + 1)) (-i) (by omega) x) := by
  rw [dualityLinearMap_apply, dualityLinearMap_apply, dualityPairing_shiftedHomComp f _ α rfl]
  rfl

end Stacks.Duality
