/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.Algebra.Module.TwoTermComplex.ShortExactCoker
public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.ModuleIso
public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.SectionCochain
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleSheafExactFunctor

/-!
# `H¹` of the kernel of a short exact sequence, on a two-affine cover

Let `f : X ⟶ Spec A` be separated, covered by two affine opens, and let
`0 ⟶ M ⟶ P ⟶ Q ⟶ 0` be a short exact sequence of quasi-coherent `𝒪_X`-modules. The sequence is
short exact on sections over the affine opens of the cover and their intersection, so it gives
exact columns between the two-term Čech complexes. If the Čech differential of `P` is onto
(`H¹(X, P) = 0`), the snake lemma identifies the cokernel of the Čech differential of `M`,
which is `H¹(X, M)`, with `H⁰(X, Q) / (image of H⁰(X, P))`.

## Main results

* `Stacks.TwoAffineCech.cokerEquivOfShortExact`: `coker d_M ≃ ker d_Q / β(ker d_P)`.
* `Stacks.TwoAffineCech.kerMap_sectionCocycle`: the map `ker d_P ⟶ ker d_Q` is the map of global
  sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.TwoAffineCech

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (U : Cover.{u} → X.Opens)

/-- The degree-`p` map of two-term Čech complexes induced by a morphism of modules. -/
abbrev cechMap {F G : X.Modules} (φ : F ⟶ G) (p : ℕ) :
    (Stacks.Cech.alternatingCechModuleComplex f U F).X p →ₗ[A]
      (Stacks.Cech.alternatingCechModuleComplex f U G).X p :=
  Stacks.Cech.alternatingCechModuleObjLinearMap f U φ p

/-- The maps of Čech cochains induced by a morphism of modules commute with the Čech
differential. -/
theorem cechD_comp_cechMap {F G : X.Modules} (φ : F ⟶ G) :
    cechD f U G ∘ₗ cechMap f U φ 0 = cechMap f U φ 1 ∘ₗ cechD f U F := by
  ext s
  exact (Stacks.Cech.alternatingCechModuleObjLinearMap_d f U φ 0 s).symm

/-- A morphism of modules that is injective on the sections over every intersection of the
cover is injective on Čech cochains. -/
theorem injective_cechMap {F G : X.Modules} (φ : F ⟶ G) (p : ℕ)
    (h : ∀ i : Fin (p + 1) → Cover.{u}, Function.Injective (φ.app (CechCochains.inter U i))) :
    Function.Injective (cechMap f U φ p) := fun _ _ hst =>
  Subtype.ext <| funext fun i =>
    h i (congrArg (fun z : (Stacks.Cech.alternatingCechModuleComplex f U G).X p => z.1 i) hst)

/-- Exactness of Čech cochains from exactness of sections over every intersection, the first
map being injective on sections. -/
theorem exact_cechMap {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) (p : ℕ)
    (hinj : ∀ i : Fin (p + 1) → Cover.{u}, Function.Injective (φ.app (CechCochains.inter U i)))
    (hex : ∀ i : Fin (p + 1) → Cover.{u},
      Function.Exact (φ.app (CechCochains.inter U i)) (ψ.app (CechCochains.inter U i))) :
    Function.Exact (cechMap f U φ p) (cechMap f U ψ p) := by
  refine fun s => ⟨fun hs => ?_, ?_⟩
  · choose m hm using fun i => (hex i (s.1 i)).1
      (congrArg (fun z : (Stacks.Cech.alternatingCechModuleComplex f U H).X p => z.1 i) hs)
    have halt : CechCochains.IsAlternating U F.presheaf m := by
      refine ⟨fun i hi => hinj i ?_, fun i a b hab => hinj _ ?_⟩
      · rw [hm i, map_zero]
        exact s.2.1 i hi
      · rw [hm, map_neg]
        refine (s.2.2 i a b hab).trans ?_
        congr 1
        rw [← hm i]
        exact (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality _) (m i)).symm
    exact ⟨⟨m, halt⟩, Subtype.ext (funext hm)⟩
  · rintro ⟨m, rfl⟩
    exact Subtype.ext (funext fun i => (hex i _).2 ⟨m.1 i, rfl⟩)

/-- In degree zero, a morphism of modules onto on the sections over each open of the cover is
onto on Čech cochains. -/
theorem surjective_cechMap_zero {F G : X.Modules} (φ : F ⟶ G)
    (h : ∀ i : Fin 1 → Cover.{u}, Function.Surjective (φ.app (CechCochains.inter U i))) :
    Function.Surjective (cechMap f U φ 0) := by
  intro s
  choose m hm using fun i => h i (s.1 i)
  have h1 : ∀ a b : Fin (0 + 1), a = b := fun a b => Fin.ext (by have := a.2; have := b.2; omega)
  have halt : CechCochains.IsAlternating U F.presheaf m :=
    ⟨fun i hi => (hi fun a b _ => h1 a b).elim, fun i a b hab => (hab (h1 a b)).elim⟩
  exact ⟨⟨m, halt⟩, Subtype.ext (funext hm)⟩

variable [IsSeparated f] (hUaff : ∀ i, IsAffineOpen (U i)) (C : ShortComplex X.Modules)
  [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent] [C.X₃.IsQuasicoherent] (hC : C.ShortExact)

include f hUaff hC

/-- A short exact sequence of quasi-coherent modules is short exact on the sections over every
intersection of opens of the cover. -/
theorem shortExact_app_inter {p : ℕ} (i : Fin (p + 1) → Cover.{u}) :
    Function.Injective (C.f.app (CechCochains.inter U i)) ∧
      Function.Exact (C.f.app (CechCochains.inter U i)) (C.g.app (CechCochains.inter U i)) ∧
        Function.Surjective (C.g.app (CechCochains.inter U i)) :=
  Stacks.AlgebraicGeometry.QcohLimits.shortExact_app_of_isAffineOpen C hC
    (Stacks.Cech.inter_isAffineOpen f U hUaff i)

/-- **`coker d_M ≃ ker d_Q / β(ker d_P)`** for a short exact sequence `0 ⟶ M ⟶ P ⟶ Q ⟶ 0` of
quasi-coherent modules with `H¹(X, P) = 0`. -/
def cokerEquivOfShortExact (hP : Function.Surjective (cechD f U C.X₂)) :
    ((Stacks.Cech.alternatingCechModuleComplex f U C.X₁).X 1 ⧸ LinearMap.range (cechD f U C.X₁))
      ≃ₗ[A] (LinearMap.ker (cechD f U C.X₃) ⧸
        LinearMap.range (Stacks.TwoTermComplex.kerMap (cechD_comp_cechMap f U C.g))) :=
  Stacks.TwoTermComplex.cokerEquivOfExact (cechD_comp_cechMap f U C.g)
    (cechD_comp_cechMap f U C.f)
    (injective_cechMap f U C.f 1 fun i => (shortExact_app_inter f U hUaff C hC i).1)
    (exact_cechMap f U C.f C.g 0 (fun i => (shortExact_app_inter f U hUaff C hC i).1)
      fun i => (shortExact_app_inter f U hUaff C hC i).2.1)
    (exact_cechMap f U C.f C.g 1 (fun i => (shortExact_app_inter f U hUaff C hC i).1)
      fun i => (shortExact_app_inter f U hUaff C hC i).2.1)
    (surjective_cechMap_zero f U C.g fun i => (shortExact_app_inter f U hUaff C hC i).2.2) hP

omit hUaff hC [IsSeparated f] [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent]
  [C.X₃.IsQuasicoherent] in
/-- The map `ker d_P ⟶ ker d_Q` is the map of global sections. -/
theorem kerMap_sectionCocycle {F G : X.Modules} (φ : F ⟶ G) (s : Γ(F, ⊤)) :
    Stacks.TwoTermComplex.kerMap (cechD_comp_cechMap f U φ) (sectionCocycle f U F s) =
      sectionCocycle f U G (φ.app ⊤ s) := by
  refine Subtype.ext (Subtype.ext (funext fun i => ?_))
  show φ.app _ (F.presheaf.map (homOfLE le_top).op s) = G.presheaf.map (homOfLE le_top).op _
  exact ConcreteCategory.congr_hom (φ.mapPresheaf.naturality
    (homOfLE (le_top : CechCochains.inter U i ≤ ⊤)).op) s

end Stacks.TwoAffineCech

end
