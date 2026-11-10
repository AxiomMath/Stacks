module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedAbove
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentTriangle
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedColimits
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.AlgebraicGeometry.Duality.DetectingBoundednessOfAPerfectComplex
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.QuasiCompactQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.Homology.DerivedCategory.Bridge.Basic
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.Homology.Perfect.ModelIndependence
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardAndRestriction
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Pseudo-coherent objects as homotopy colimits of perfect objects

Let `X` be a quasi-compact and quasi-separated scheme and `K` an object of `D(𝒪_X)`.
[Stacks, Tag 0DJN] says that `K` is pseudo-coherent if and only if `K = hocolim Kₙ` for a system
of perfect objects `Kₙ` such that `τ_{≥ -n} Kₙ ⟶ τ_{≥ -n} K` is an isomorphism for all `n`.

## Main results

* `Stacks.PseudoCoherentHocolim.isPseudoCoherent_iff_exists_perfect_hocolim`:
  **[Stacks, Tag 0DJN]**, at an arbitrary model of `D(𝒪_X)`.
* `Stacks.PseudoCoherentHocolim.isPseudoCoherent_of_isHomotopyColimitWith_perfect`: the
  implication (2) ⟹ (1), on an arbitrary ringed space, as the source remarks.
* `Stacks.PseudoCoherentHocolim.exists_perfect_hocolim_of_isPseudoCoherent_of_supportedOn`: the
  implication (1) ⟹ (2) for `K` supported on a closed `T ⊆ X` with quasi-compact complement, the
  `Kₙ` being supported on `T` as well. This is the form [Stacks, Tag 0DJP] consumes; `T = X`
  gives (1) ⟹ (2) of 0DJN.
* `Stacks.PseudoCoherentHocolim.isHomotopyColimitWith_approximationTower`: an abstract tower of
  maps `Kₙ ⟶ K`, each an isomorphism on cohomology in degrees `≥ -n`, has `K` as its homotopy
  colimit, in the derived category of an abelian category with exact colimits over `ℕ` whose
  cohomology functors commute with countable direct sums.

## The proof

(2) ⟹ (1): the cone of `Kₙ ⟶ K` has no cohomology in degrees `≥ -n`, so it is
`(-n)`-pseudo-coherent; `Kₙ` is pseudo-coherent (Stacks 08CQ), so `K` is `(-n)`-pseudo-coherent
(Stacks 08CD), for every `n`.

(1) ⟹ (2): follow the source. Choose a perfect approximation `K₁ ⟶ K` (Stacks 08ES). Given
`Kₙ ⟶ K`, choose `a ≤ b` for the perfect `Kₙ` as in Stacks 09M4 and an approximation
`Kₙ₊₁ ⟶ K` in degrees above `min (a - 1) (-n - 2)`; its cone lies in `D_QCoh(𝒪_X)` and has no
cohomology in degrees `≥ a`, so `Kₙ ⟶ K` factors through `Kₙ₊₁` (Lemma 0149). The homotopy
colimit of the resulting system is `K` by Lemma 0CRK applied to the cohomology functors.

## Implementation notes

`K = hocolim Kₙ` is `CategoryTheory.Pretriangulated.IsHomotopyColimitWith F K c` (Definition
090Z), which records the coprojections `cₙ : Kₙ ⟶ K` of the defining triangle; the map
`τ_{≥ -n} Kₙ ⟶ τ_{≥ -n} K` of the source is the truncation of `cₙ`.

The derived category is an arbitrary model `[HasDerivedCategory.{w} X.Modules]`. The inputs 08ES
and 09M4 are stated at `CategoryTheory.HasDerivedCategory.standard`; they are moved to the chosen
model along the comparison `StacksDraft.DerivedModel.modelEquiv`, which commutes with cohomology
and with the localization functors. Instance search does not identify `X.Modules` with its other
spellings `SheafOfModules X.ringCatSheaf` and `OXMod X.toRingedSpace`, so the chosen model is
passed explicitly in the statements and re-read at those spellings by two local instances.

## References

* [Stacks Project, Tag 0DJN](https://stacks.math.columbia.edu/tag/0DJN)
* [Stacks Project, Tag 0DJP](https://stacks.math.columbia.edu/tag/0DJP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open AlgebraicGeometry StrictlyPerfect

universe w u

namespace Stacks.PseudoCoherentHocolim

/-! ### Truncation in degrees `≥ a` and cohomology -/

section Truncation

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- The truncation map `K ⟶ τ_{≥ a} K` induces isomorphisms on cohomology in every degree
`j ≥ a`. -/
theorem isIso_homologyFunctor_map_truncGEπ_app (K : DerivedCategory C) (a j : ℤ) (hj : a ≤ j) :
    IsIso ((DerivedCategory.homologyFunctor C j).map
      ((DerivedCategory.TStructure.t.truncGEπ a).app K)) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let T := (t.triangleLEGE (a - 1) a (by omega)).obj K
  have hT := t.triangleLEGE_distinguished (a - 1) a (by omega) K
  have hEpi : Epi ((DerivedCategory.homologyFunctor C j).map T.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT j (j + 1) (by omega)).2
      ((DerivedCategory.isZero_of_isLE ((t.truncLE (a - 1)).obj K) (a - 1) (j + 1)
        (by omega)).eq_of_tgt _ _)
  have hMono : Mono ((DerivedCategory.homologyFunctor C j).map T.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT j).2
      ((DerivedCategory.isZero_of_isLE ((t.truncLE (a - 1)).obj K) (a - 1) j
        (by omega)).eq_of_src _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor C j).map T.mor₂)

/-- A morphism of the derived category becomes an isomorphism after the truncation `τ_{≥ a}`
exactly when it induces isomorphisms on cohomology in every degree `i ≥ a`. -/
theorem isIso_truncGE_map_iff {A K : DerivedCategory C} (f : A ⟶ K) (a : ℤ) :
    IsIso ((DerivedCategory.TStructure.t.truncGE a).map f) ↔
      ∀ i : ℤ, a ≤ i → IsIso ((DerivedCategory.homologyFunctor C i).map f) := by
  let t := DerivedCategory.TStructure.t (C := C)
  have hsq : ∀ i : ℤ, (DerivedCategory.homologyFunctor C i).map f ≫
      (DerivedCategory.homologyFunctor C i).map ((t.truncGEπ a).app K) =
      (DerivedCategory.homologyFunctor C i).map ((t.truncGEπ a).app A) ≫
        (DerivedCategory.homologyFunctor C i).map ((t.truncGE a).map f) := fun i => by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (by simp)
  constructor
  · intro h i hi
    have := isIso_homologyFunctor_map_truncGEπ_app A a i hi
    have := isIso_homologyFunctor_map_truncGEπ_app K a i hi
    exact IsIso.of_isIso_fac_right (hsq i)
  · intro h
    rw [DerivedCategory.isIso_iff]
    intro i
    by_cases hi : a ≤ i
    · have := isIso_homologyFunctor_map_truncGEπ_app A a i hi
      have := isIso_homologyFunctor_map_truncGEπ_app K a i hi
      have := h i hi
      exact IsIso.of_isIso_fac_left (hsq i).symm
    · exact (DerivedCategory.isZero_of_isGE ((t.truncGE a).obj A) a i (by omega)).isIso
        (DerivedCategory.isZero_of_isGE ((t.truncGE a).obj K) a i (by omega)) _

/-- The third vertex of a distinguished triangle whose first morphism induces isomorphisms on
cohomology in every degree `i ≥ a` has no cohomology in degrees `≥ a`. -/
theorem isZero_homologyFunctor_obj₃_of_isIso (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (a : ℤ)
    (h : ∀ i : ℤ, a ≤ i → IsIso ((DerivedCategory.homologyFunctor C i).map T.mor₁))
    (i : ℤ) (hi : a ≤ i) : IsZero ((DerivedCategory.homologyFunctor C i).obj T.obj₃) := by
  have := h i hi
  have := h (i + 1) (by omega)
  have h₂ : (DerivedCategory.homologyFunctor C i).map T.mor₂ = 0 :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).1 inferInstance
  have hδ : DerivedCategory.HomologySequence.δ T i (i + 1) (by omega) = 0 :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT i (i + 1) (by omega)).1
      inferInstance
  have : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1) (by omega)).2 hδ
  exact IsZero.of_epi_eq_zero _ h₂

end Truncation

/-! ### From a homotopy colimit of perfect objects to pseudo-coherence -/

section RingedSpace

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{w} (OXMod.{u, u} X)]

/-- An object `K` of `D(𝒪_X)` which, for every `m`, receives a map from a perfect object inducing
isomorphisms on cohomology in all degrees `≥ m`, is pseudo-coherent.

For a perfect `P` with `P ⟶ K` an isomorphism on cohomology in degrees `≥ m`, the cone `C` of the
map has no cohomology in degrees `≥ m`, hence is `m`-pseudo-coherent; `P` is pseudo-coherent
(Stacks 08CQ); and Stacks 08CD part (2) applied to `P ⟶ K ⟶ C ⟶ P⟦1⟧` makes `K`
`m`-pseudo-coherent. -/
theorem isPseudoCoherent_of_forall_exists_perfect_isIso
    (K : DerivedCategory (OXMod.{u, u} X))
    (h : ∀ m : ℤ, ∃ (P : DerivedCategory (OXMod.{u, u} X)) (f : P ⟶ K),
      Stacks.Cohomology.PerfectComplexes.IsPerfect P ∧
        ∀ i : ℤ, m ≤ i → IsIso ((DerivedCategory.homologyFunctor _ i).map f)) :
    RingedSpace.IsPseudoCoherent K := by
  refine (RingedSpace.isPseudoCoherent_iff_forall K).2 fun m => ?_
  obtain ⟨P, f, hP, hf⟩ := h m
  obtain ⟨Cn, g, δ, hT⟩ := distinguished_cocone_triangle f
  have hPpc : RingedSpace.IsPseudoCoherentFrom P m := by
    obtain ⟨E, hE, e⟩ :=
      Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect P hP
    exact ⟨E, hE m, e⟩
  have hCpc : RingedSpace.IsPseudoCoherentFrom Cn m :=
    RingedSpace.isPseudoCoherentFrom_of_isZero_homology_ge Cn m fun j hj =>
      isZero_homologyFunctor_obj₃_of_isIso _ hT m hf j hj
  exact RingedSpace.isPseudoCoherentFrom_obj₂_of_distinguished m _ hT hPpc hCpc

/-- **[Stacks, Tag 0DJN], (2) ⟹ (1), on any ringed space.** Let `K` be an object of `D(𝒪_X)`
and let `F : ℕ ⥤ D(𝒪_X)` be a system of perfect objects `Kₙ = F.obj n` with coprojections
`cₙ : Kₙ ⟶ K` such that `τ_{≥ -n} cₙ : τ_{≥ -n} Kₙ ⟶ τ_{≥ -n} K` is an isomorphism for every
`n`. Then `K` is pseudo-coherent. The homotopy colimit structure plays no role in this
direction; it is the statement of the source that is recorded in
`isPseudoCoherent_of_isHomotopyColimitWith_perfect`. -/
theorem isPseudoCoherent_of_perfect_truncGE_isIso (K : DerivedCategory (OXMod.{u, u} X))
    (F : ℕ ⥤ DerivedCategory (OXMod.{u, u} X)) (c : ∀ n, F.obj n ⟶ K)
    (hF : ∀ n, Stacks.Cohomology.PerfectComplexes.IsPerfect (F.obj n))
    (hc : ∀ n : ℕ, IsIso ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).map (c n))) :
    RingedSpace.IsPseudoCoherent K := by
  refine isPseudoCoherent_of_forall_exists_perfect_isIso K fun m => ?_
  refine ⟨F.obj m.natAbs, c m.natAbs, hF _, fun i hi => ?_⟩
  exact (isIso_truncGE_map_iff (c m.natAbs) _).1 (hc m.natAbs) i (by omega)

/-- **[Stacks, Tag 0DJN], (2) ⟹ (1), on any ringed space**, in the source's form: if `K` is a
homotopy colimit `hocolim Kₙ` of perfect objects with coprojections `cₙ : Kₙ ⟶ K` such that
`τ_{≥ -n} Kₙ ⟶ τ_{≥ -n} K` is an isomorphism for every `n`, then `K` is pseudo-coherent. -/
theorem isPseudoCoherent_of_isHomotopyColimitWith_perfect
    (K : DerivedCategory (OXMod.{u, u} X)) (F : ℕ ⥤ DerivedCategory (OXMod.{u, u} X))
    [HasCoproduct F.obj] (c : ∀ n, F.obj n ⟶ K)
    (hF : ∀ n, Stacks.Cohomology.PerfectComplexes.IsPerfect (F.obj n))
    (_hK : IsHomotopyColimitWith F K c)
    (hc : ∀ n : ℕ, IsIso ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).map (c n))) :
    RingedSpace.IsPseudoCoherent K :=
  isPseudoCoherent_of_perfect_truncGE_isIso K F c hF hc

end RingedSpace


/-! ### An abstract tower of approximations and its homotopy colimit -/

section Tower

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- A stage of a tower of approximations of `K` at level `n`: an object satisfying `Good`,
together with a map to `K` inducing isomorphisms on cohomology in every degree `≥ -n`. -/
def ApproximationStage (Good : DerivedCategory C → Prop) (K : DerivedCategory C) (n : ℕ) :
    Type _ :=
  { p : Σ P : DerivedCategory C, P ⟶ K // Good p.1 ∧
      ∀ i : ℤ, -(n : ℤ) ≤ i → IsIso ((DerivedCategory.homologyFunctor C i).map p.2) }

variable {Good : DerivedCategory C → Prop} {K : DerivedCategory C}
  (start : ApproximationStage Good K 0)
  (step : ∀ (n : ℕ) (s : ApproximationStage Good K n),
    ∃ (s' : ApproximationStage Good K (n + 1)) (g : s.1.1 ⟶ s'.1.1), g ≫ s'.1.2 = s.1.2)

/-- The tower of stages built from a first stage by choosing a successor at every level. -/
def approximationTower : ∀ n : ℕ, ApproximationStage Good K n :=
  Nat.rec start fun n s => (step n s).choose

/-- The transition maps of `approximationTower`. -/
def approximationTowerMap (n : ℕ) :
    (approximationTower start step n).1.1 ⟶ (approximationTower start step (n + 1)).1.1 :=
  (step n (approximationTower start step n)).choose_spec.choose

/-- The system `ℕ ⥤ D(C)` of the tower. -/
def approximationTowerFunctor : ℕ ⥤ DerivedCategory C :=
  Functor.ofSequence (approximationTowerMap start step)

/-- The transition map `Kₙ ⟶ Kₙ₊₁` of the system is the chosen one. -/
theorem approximationTowerFunctor_map_succ (n : ℕ) :
    (approximationTowerFunctor start step).map (homOfLE (Nat.le_succ n)) =
      approximationTowerMap start step n :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- The maps of the system to `K`. -/
def approximationTowerι (n : ℕ) : (approximationTowerFunctor start step).obj n ⟶ K :=
  (approximationTower start step n).1.2

/-- The chosen transition maps are compatible with the maps to `K`. -/
theorem approximationTowerMap_comp_ι (n : ℕ) :
    approximationTowerMap start step n ≫ approximationTowerι start step (n + 1) =
      approximationTowerι start step n :=
  (step n (approximationTower start step n)).choose_spec.choose_spec

/-- The transition map `Kₙ ⟶ Kₙ₊₁` followed by `Kₙ₊₁ ⟶ K` is `Kₙ ⟶ K`. -/
theorem approximationTowerFunctor_map_succ_comp_ι (n : ℕ) :
    (approximationTowerFunctor start step).map (homOfLE (Nat.le_succ n)) ≫
      approximationTowerι start step (n + 1) = approximationTowerι start step n :=
  (congrArg (· ≫ approximationTowerι start step (n + 1))
    (approximationTowerFunctor_map_succ start step n)).trans
    (approximationTowerMap_comp_ι start step n)

/-- The maps `Kₙ ⟶ K` form a cocone on the system. -/
theorem approximationTowerFunctor_map_comp_ι {n j : ℕ} (f : n ⟶ j) :
    (approximationTowerFunctor start step).map f ≫ approximationTowerι start step j =
      approximationTowerι start step n := by
  let F := approximationTowerFunctor start step
  have key : ∀ (j : ℕ) (h : n ≤ j), F.map (homOfLE h) ≫
      approximationTowerι start step j = approximationTowerι start step n := by
    intro j h
    induction j, h using Nat.le_induction with
    | base =>
      exact (congrArg (· ≫ approximationTowerι start step n) (F.map_id n)).trans
        (Category.id_comp _)
    | succ j hj ih =>
      calc F.map (homOfLE (hj.trans (Nat.le_succ j))) ≫ approximationTowerι start step (j + 1)
          = F.map (homOfLE hj) ≫ (F.map (homOfLE (Nat.le_succ j)) ≫
              approximationTowerι start step (j + 1)) := by
            rw [← F.map_comp_assoc]
            rfl
        _ = F.map (homOfLE hj) ≫ approximationTowerι start step j := by
              rw [approximationTowerFunctor_map_succ_comp_ι]
        _ = approximationTowerι start step n := ih
  exact key j (leOfHom f)

/-- The map `Kₙ ⟶ K` is an isomorphism on cohomology in every degree `≥ -n`. -/
theorem isIso_homologyFunctor_map_approximationTowerι (n : ℕ) (i : ℤ) (hi : -(n : ℤ) ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor C i).map (approximationTowerι start step n)) :=
  (approximationTower start step n).2.2 i hi

/-- Every member of the system satisfies `Good`. -/
theorem good_approximationTowerFunctor_obj (n : ℕ) :
    Good ((approximationTowerFunctor start step).obj n) :=
  (approximationTower start step n).2.1

/-- The cocone on the cohomology of the tower given by the cohomology of its maps to `K`. -/
def approximationTowerHomologyCocone (i : ℤ) :
    Cocone (approximationTowerFunctor start step ⋙ DerivedCategory.homologyFunctor C i) where
  pt := (DerivedCategory.homologyFunctor C i).obj K
  ι :=
    { app := fun n => (DerivedCategory.homologyFunctor C i).map (approximationTowerι start step n)
      naturality := fun n j f => by
        simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.comp_map,
          Functor.const_obj_map, Category.comp_id, ← Functor.map_comp,
          approximationTowerFunctor_map_comp_ι] }

/-- The cocone `approximationTowerHomologyCocone` is a colimit: the cohomology of the tower in a
fixed degree is eventually constant, with value the cohomology of `K`. -/
def isColimitApproximationTowerHomologyCocone (i : ℤ) :
    IsColimit (approximationTowerHomologyCocone start step i) := by
  let H := DerivedCategory.homologyFunctor C i
  have hev : (approximationTowerFunctor start step ⋙ H).IsEventuallyConstantFrom i.natAbs := by
    intro j f
    have h₁ := isIso_homologyFunctor_map_approximationTowerι start step i.natAbs i (by omega)
    have h₂ := isIso_homologyFunctor_map_approximationTowerι start step j i
      (by have := leOfHom f; omega)
    change IsIso (H.map ((approximationTowerFunctor start step).map f))
    have : IsIso (H.map ((approximationTowerFunctor start step).map f) ≫
        H.map (approximationTowerι start step j)) := by
      rw [← Functor.map_comp, approximationTowerFunctor_map_comp_ι]
      exact h₁
    exact IsIso.of_isIso_comp_right _ (H.map (approximationTowerι start step j))
  have : IsIso ((approximationTowerHomologyCocone start step i).ι.app i.natAbs) :=
    isIso_homologyFunctor_map_approximationTowerι start step i.natAbs i (by omega)
  exact hev.isColimitOfIsIso _

variable [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
  [HasColimitsOfShape (Discrete ℕ) (DerivedCategory C)]
  [∀ i : ℤ, PreservesColimitsOfShape (Discrete ℕ) (DerivedCategory.homologyFunctor C i)]

/-- **The tower of approximations has `K` as its homotopy colimit**, with the given maps to `K`
as coprojections. Complete `1 - f : ⊕ Kₙ ⟶ ⊕ Kₙ` to a distinguished triangle with third vertex
`L`; the maps `Kₙ ⟶ K` are compatible with the transition maps, so their sum factors through
`⊕ Kₙ ⟶ L` by a map `b : L ⟶ K`. In each degree `i`, the cohomology of `L` is the colimit of the
cohomology of the `Kₙ` (Stacks 0CRK), and so is the cohomology of `K`, since the cohomology of
the tower is eventually constant with value `H^i(K)`; and `H^i(b)` is the comparison of the two
colimits. So `b` is an isomorphism, and `K` is a homotopy colimit. -/
theorem isHomotopyColimitWith_approximationTower :
    IsHomotopyColimitWith (approximationTowerFunctor start step) K
      (approximationTowerι start step) := by
  let F := approximationTowerFunctor start step
  let c := approximationTowerι start step
  let φ : ∐ F.obj ⟶ ∐ F.obj := Sigma.desc fun n ↦ Sigma.ι F.obj n -
      F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1)
  obtain ⟨L, p₀, q₀, hT₀⟩ := distinguished_cocone_triangle φ
  have hφ : φ ≫ Sigma.desc c = 0 := by
    refine Sigma.hom_ext _ _ fun n => ?_
    simp only [φ, colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_ι_app,
      Preadditive.sub_comp, Category.assoc, colimit.ι_desc, comp_zero]
    rw [approximationTowerFunctor_map_comp_ι, sub_self]
  obtain ⟨b, hb⟩ := Triangle.yoneda_exact₂ _ hT₀ (Sigma.desc c) hφ
  have hιb : ∀ n, Sigma.ι F.obj n ≫ p₀ ≫ b = c n := fun n => by
    change Sigma.ι F.obj n ≫ (Triangle.mk φ p₀ q₀).mor₂ ≫ b = c n
    rw [← hb, Sigma.ι_comp_desc]
  have hbiso : IsIso b := by
    rw [DerivedCategory.isIso_iff]
    intro i
    let H := DerivedCategory.homologyFunctor C i
    obtain ⟨e, he⟩ := exists_iso_colimit_of_isHomotopyColimit F H p₀ q₀ hT₀
    have hdesc : colimit.desc (F ⋙ H) (approximationTowerHomologyCocone start step i) =
        e.hom ≫ H.map b := by
      refine colimit.hom_ext fun n => ?_
      rw [colimit.ι_desc]
      change H.map (c n) = colimit.ι (F ⋙ H) n ≫ e.hom ≫ H.map b
      rw [reassoc_of% (he n), ← H.map_comp, Category.assoc, hιb]
    have h₁ : IsIso (colimit.desc (F ⋙ H) (approximationTowerHomologyCocone start step i)) :=
      inferInstanceAs (IsIso ((colimit.isColimit _).coconePointUniqueUpToIso
        (isColimitApproximationTowerHomologyCocone start step i)).hom)
    have : IsIso (e.hom ≫ H.map b) := hdesc ▸ h₁
    exact IsIso.of_isIso_comp_left e.hom (H.map b)
  refine ⟨p₀ ≫ b, inv b ≫ q₀, isomorphic_distinguished _ hT₀ _ ?_, hιb⟩
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso b).symm
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl) (by simp)
    (by simp)

end Tower

/-! ### Countable direct sums in the derived category of `𝒪_X`-modules -/

section SchemeCoproducts

variable (X : Scheme.{u})

/-- Colimits over `ℕ` of `𝒪_X`-modules are exact. -/
theorem hasExactColimitsOfShape_nat_modules : HasExactColimitsOfShape ℕ X.Modules := by
  have : AB5OfSize.{u, u} X.Modules :=
    AlgebraicGeometry.SheafOfModules.instAB5SheafOfModules X.ringCatSheaf
  have : AB5OfSize.{0, 0} X.Modules := AB5OfSize_shrink.{0, 0, u, u} X.Modules
  exact AB5OfSize.ofShape ℕ

variable [HasDerivedCategory.{w} X.Modules]

/-- The derived category of `𝒪_X`-modules, at any model, has direct sums indexed by `ℕ`. -/
theorem hasColimitsOfShape_discrete_nat_derivedCategory :
    HasColimitsOfShape (Discrete ℕ) (DerivedCategory X.Modules) := by
  have := Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory X.Modules
    (ULift.{u} ℕ)
  exact hasColimitsOfShape_of_equivalence (Discrete.equivalence (Equiv.ulift.{u, 0} (α := ℕ)))

/-- The cohomology sheaves of an object of the derived category of `𝒪_X`-modules, at any model,
commute with direct sums indexed by `ℕ`. -/
theorem preservesColimitsOfShape_discrete_nat_homologyFunctor (i : ℤ) :
    PreservesColimitsOfShape (Discrete ℕ) (DerivedCategory.homologyFunctor X.Modules i) := by
  have := Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts X.Modules (ULift.{u} ℕ)
  have := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor (A := X.Modules)
    (J := Discrete (ULift.{u} ℕ)) (ComplexShape.up ℤ) i
  have : PreservesColimitsOfShape (Discrete (ULift.{u} ℕ))
      (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor X.Modules i) :=
    preservesColimitsOfShape_of_natIso (DerivedCategory.homologyFunctorFactors X.Modules i).symm
  have := preservesColimitsOfShape_discrete_of_essSurj_comp DerivedCategory.Q
    (DerivedCategory.homologyFunctor X.Modules i) (ULift.{u} ℕ)
  exact preservesColimitsOfShape_of_equiv (Discrete.equivalence (Equiv.ulift.{u, 0} (α := ℕ))) _

end SchemeCoproducts

/-! ### Moving the inputs from the standard model to an arbitrary model -/

section SchemeTransport

open StacksDraft.DerivedModel

variable (X : Scheme.{u}) [h : HasDerivedCategory.{w} X.Modules]

/-- The comparison of the chosen derived category of `𝒪_X`-modules with the standard model, in
which [Stacks, Tag 08ES] and [Stacks, Tag 09M4] are stated. -/
abbrev toStandardModel :
    DerivedCategory X.Modules ≌ @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _) :=
  modelEquiv h (HasDerivedCategory.standard _)

variable {X}

/-- The comparison with the standard model commutes with cohomology. -/
abbrev toStandardModelHomologyIso (n : ℤ) (K : DerivedCategory X.Modules) :
    (@DerivedCategory.homologyFunctor X.Modules _ _ (HasDerivedCategory.standard _) n).obj
        ((toStandardModel X).functor.obj K) ≅
      (DerivedCategory.homologyFunctor X.Modules n).obj K :=
  (modelHomologyFunctorIso h (HasDerivedCategory.standard _) n).app K

/-- A morphism induces an isomorphism on a cohomology sheaf exactly when its comparison with the
standard model does. -/
theorem isIso_homologyFunctor_map_toStandardModel_iff {K L : DerivedCategory X.Modules}
    (f : K ⟶ L) (n : ℤ) :
    IsIso ((@DerivedCategory.homologyFunctor X.Modules _ _ (HasDerivedCategory.standard _) n).map
        ((toStandardModel X).functor.map f)) ↔
      IsIso ((DerivedCategory.homologyFunctor X.Modules n).map f) :=
  NatIso.isIso_map_iff (modelHomologyFunctorIso h (HasDerivedCategory.standard _) n) f

omit h in
/-- Vanishing of a stalk is invariant under isomorphism of `𝒪_X`-modules. -/
theorem isZero_stalk_of_iso {M N : X.Modules} (e : M ≅ N) (x : X)
    (hM : IsZero (TopCat.Presheaf.stalk (X := X) M.val.presheaf x)) :
    IsZero (TopCat.Presheaf.stalk (X := X) N.val.presheaf x) :=
  hM.of_iso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
    ((PresheafOfModules.toPresheaf _).mapIso ((SheafOfModules.forget _).mapIso e))).symm

/-- The comparison with the standard model preserves pseudo-coherence. -/
theorem isPseudoCoherent_toStandardModel_obj {K : DerivedCategory X.Modules}
    (hK : @RingedSpace.IsPseudoCoherent X.toRingedSpace h K) :
    @RingedSpace.IsPseudoCoherent X.toRingedSpace (HasDerivedCategory.standard _)
      ((toStandardModel X).functor.obj K) := by
  obtain ⟨Kc, hKc, ⟨e⟩⟩ := hK
  exact ⟨Kc, hKc, ⟨((modelCompQIso h (HasDerivedCategory.standard _)).app Kc).symm ≪≫
    (toStandardModel X).functor.mapIso e⟩⟩

/-- An object is perfect exactly when its comparison with the standard model is. -/
theorem isPerfect_toStandardModel_obj_iff (K : DerivedCategory X.Modules) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace (HasDerivedCategory.standard _)
        ((toStandardModel X).functor.obj K) ↔
      @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h K :=
  (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_of_model h (HasDerivedCategory.standard _)
    (DerivedCategory.Q.objObjPreimageIso K)
    (((modelCompQIso h (HasDerivedCategory.standard _)).app _).symm ≪≫
      (toStandardModel X).functor.mapIso (DerivedCategory.Q.objObjPreimageIso K))).symm

end SchemeTransport

/-! ### The inputs at an arbitrary model, and [Stacks, Tag 0DJN] -/

section Scheme

open StacksDraft.DerivedModel

variable {X : Scheme.{u}} [h : HasDerivedCategory.{w} X.Modules]

/-- The chosen model of `D(𝒪_X)`, read at the spelling `SheafOfModules X.ringCatSheaf` of the
category of `𝒪_X`-modules, which instance search does not identify with `X.Modules`. -/
local instance instHasDerivedCategorySheafOfModules :
    HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf) := h

/-- The chosen model of `D(𝒪_X)`, read at the ringed-space spelling of the category of
`𝒪_X`-modules. -/
local instance instHasDerivedCategoryOXMod :
    HasDerivedCategory.{w} (OXMod.{u, u} X.toRingedSpace) := h

/-- A perfect object of `D(𝒪_X)` is pseudo-coherent (Stacks 08CQ), at any model. -/
theorem isPseudoCoherent_of_isPerfect {P : DerivedCategory X.Modules}
    (hP : @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h P) :
    @RingedSpace.IsPseudoCoherent X.toRingedSpace h P := by
  obtain ⟨E, hE, e⟩ := Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect P hP
  exact ⟨E, hE, e⟩

/-- The cohomology sheaves of a pseudo-coherent object of `D(𝒪_X)` are quasi-coherent
(Stacks 08E5), at any model. -/
theorem isQuasicoherent_homology_of_isPseudoCoherent {K : DerivedCategory X.Modules}
    (hK : @RingedSpace.IsPseudoCoherent X.toRingedSpace h K) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent :=
  @isQuasicoherentDerived_of_isPseudoCoherent X h K hK i

/-- **[Stacks, Tag 08ES] at an arbitrary model.** Let `X` be quasi-compact and quasi-separated,
`T ⊆ X` closed with quasi-compact complement, and `K` a pseudo-coherent object of `D(𝒪_X)` whose
cohomology is supported on `T`. Then for every `m` there is a perfect object `P` supported on `T`
and a map `P ⟶ K` inducing isomorphisms on cohomology in every degree `> m`. -/
theorem exists_perfect_approximation_of_isPseudoCoherent [CompactSpace X] [QuasiSeparatedSpace X]
    {T : Set X} (hT : IsClosed T) (hTc : IsCompact Tᶜ) {K : DerivedCategory X.Modules}
    (hK : @Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn _ X.ringCatSheaf h T K)
    (hpc : @RingedSpace.IsPseudoCoherent X.toRingedSpace h K) (m : ℤ) :
    ∃ (P : DerivedCategory X.Modules) (α : P ⟶ K),
      @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h P ∧
      @Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn _ X.ringCatSheaf h T P ∧
      ∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor X.Modules i).map α) := by
  let E := toStandardModel X
  obtain ⟨r, hr⟩ := AlgebraicGeometry.PerfectApproximation.hasApproximationByPerfectComplexes X T
    hT (hTc.isRetrocompact hT.isOpen_compl)
  have hpc₀ := isPseudoCoherent_toStandardModel_obj hpc
  obtain ⟨P₀, hP₀, hP₀T, α₀, hα₀, -⟩ := hr (E.functor.obj K) m
    (fun i => (AlgebraicGeometry.isQuasicoherentModules X).prop_of_iso
      (toStandardModelHomologyIso i K).symm (isQuasicoherent_homology_of_isPseudoCoherent hpc i))
    ((@RingedSpace.isPseudoCoherent_iff_forall X.toRingedSpace (HasDerivedCategory.standard _)
      _).1 hpc₀ (m - r))
    (fun i x _ hx => isZero_stalk_of_iso (toStandardModelHomologyIso i K).symm x (hK i x hx))
  refine ⟨E.inverse.obj P₀, E.inverse.map α₀ ≫ E.unitInv.app K, ?_, fun i x hx => ?_,
    fun i hi => ?_⟩
  · refine (isPerfect_toStandardModel_obj_iff _).1 ?_
    obtain ⟨Pc, hPc, ⟨e⟩⟩ := hP₀
    exact ⟨Pc, hPc, ⟨e ≪≫ (E.counitIso.app P₀).symm⟩⟩
  · exact isZero_stalk_of_iso
      ((@DerivedCategory.homologyFunctor X.Modules _ _ (HasDerivedCategory.standard _) i).mapIso
        (E.counitIso.app P₀).symm ≪≫ toStandardModelHomologyIso i (E.inverse.obj P₀)) x
      (hP₀T i x hx)
  · rw [← isIso_homologyFunctor_map_toStandardModel_iff, Functor.map_comp,
      Equivalence.fun_inv_map]
    have := hα₀ i hi
    simp only [Functor.map_comp]
    infer_instance

/-- **[Stacks, Tag 09M4] part (1) at an arbitrary model.** For a perfect object `P` of `D(𝒪_X)`,
`X` quasi-compact and quasi-separated, there are `a ≤ b` such that `P` admits no nonzero map to
any `L` in `D_QCoh(𝒪_X)` with no cohomology in degrees `a, …, b`. -/
theorem exists_window_subsingleton_hom_of_isPerfect [CompactSpace X] [QuasiSeparatedSpace X]
    {P : DerivedCategory X.Modules}
    (hP : @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h P) :
    ∃ a b : ℤ, a ≤ b ∧
      ∀ L : DerivedCategory X.Modules,
        (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsQuasicoherent) →
        (∀ i : ℤ, a ≤ i → i ≤ b → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj L)) →
        Subsingleton (P ⟶ L) := by
  let E := toStandardModel X
  obtain ⟨a, b, hab, hw⟩ := Stacks.DerivedQCoh.exists_window_subsingleton_hom_of_isPerfect_qcqs X
    (E.functor.obj P) ((isPerfect_toStandardModel_obj_iff P).2 hP)
  refine ⟨a, b, hab, fun L hLqc hLz => ?_⟩
  have := hw (E.functor.obj L)
    (fun i => (AlgebraicGeometry.isQuasicoherentModules X).prop_of_iso
      (toStandardModelHomologyIso i L).symm (hLqc i))
    (fun i h₁ h₂ => (hLz i h₁ h₂).of_iso (toStandardModelHomologyIso i L))
  exact E.fullyFaithfulFunctor.homEquiv.subsingleton_congr.2 this

/-- The third vertex of a distinguished triangle in `D(𝒪_X)` whose first two vertices have
quasi-coherent cohomology has quasi-coherent cohomology. -/
theorem isQuasicoherent_homology_obj₃ (T : Triangle (DerivedCategory X.Modules))
    (hT : T ∈ distTriang (DerivedCategory X.Modules))
    (h₁ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj T.obj₁).IsQuasicoherent)
    (h₂ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj T.obj₂).IsQuasicoherent)
    (i : ℤ) : ((DerivedCategory.homologyFunctor X.Modules i).obj T.obj₃).IsQuasicoherent :=
  have := @DerivedCategoryB.derivedCategoryB_isTriangulated X.Modules _ _ h _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)
  have := @DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms X.Modules _ _ h _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)
  (@DerivedCategoryB.derivedCategoryB X.Modules _ _ h
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ext_of_isTriangulatedClosed₃ _ hT h₁ h₂ i

/-- **The induction step of [Stacks, Tag 0DJN].** Let `K` be pseudo-coherent and supported on `T`
and let `α : P ⟶ K` be a map from a perfect object. Then `α` factors through a perfect object `P'`
supported on `T` whose map to `K` is an isomorphism on cohomology in every degree `≥ -(n + 1)`.

Choose `a ≤ b` for `P` as in 09M4 and an approximation `β : P' ⟶ K` in degrees above
`min (a - 1) (-n - 2)` (08ES); the cone `C` of `β` lies in `D_QCoh(𝒪_X)` and has no cohomology in
degrees `≥ a`, so `P ⟶ K ⟶ C` vanishes and `α` factors through `β` (Lemma 0149). -/
theorem exists_approximation_step [CompactSpace X] [QuasiSeparatedSpace X]
    {T : Set X} (hT : IsClosed T) (hTc : IsCompact Tᶜ) {K : DerivedCategory X.Modules}
    (hK : @Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn _ X.ringCatSheaf h T K)
    (hpc : @RingedSpace.IsPseudoCoherent X.toRingedSpace h K) (n : ℕ)
    {P : DerivedCategory X.Modules} (α : P ⟶ K)
    (hP : @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h P) :
    ∃ (P' : DerivedCategory X.Modules) (α' : P' ⟶ K) (g : P ⟶ P'),
      (@Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h P' ∧
        @Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn _ X.ringCatSheaf h T P') ∧
      (∀ i : ℤ, -((n : ℤ) + 1) ≤ i →
        IsIso ((DerivedCategory.homologyFunctor X.Modules i).map α')) ∧ g ≫ α' = α := by
  obtain ⟨a, b, -, hw⟩ := exists_window_subsingleton_hom_of_isPerfect hP
  obtain ⟨P', β, hP', hP'T, hβ⟩ :=
    exists_perfect_approximation_of_isPseudoCoherent hT hTc hK hpc (min (a - 1) (-(n : ℤ) - 2))
  obtain ⟨Cn, γ, δ, hTr⟩ := distinguished_cocone_triangle β
  have hCqc := isQuasicoherent_homology_obj₃ _ hTr
    (isQuasicoherent_homology_of_isPseudoCoherent (isPseudoCoherent_of_isPerfect hP'))
    (isQuasicoherent_homology_of_isPseudoCoherent hpc)
  have hzero : Subsingleton (P ⟶ Cn) := hw Cn hCqc fun i hi _ =>
    isZero_homologyFunctor_obj₃_of_isIso _ hTr (min (a - 1) (-(n : ℤ) - 2) + 1)
      (fun j hj => hβ j (by omega)) i (by omega)
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ hTr α (hzero.elim _ _)
  exact ⟨P', β, g, ⟨hP', hP'T⟩, fun i hi => hβ i (by omega), hg.symm⟩

/-! ### [Stacks, Tag 0DJN] -/

/-- **[Stacks, Tag 0DJN], (1) ⟹ (2), with support** (the form [Stacks, Tag 0DJP] uses). Let `X`
be a quasi-compact and quasi-separated scheme, `T ⊆ X` a closed subset with quasi-compact
complement, and `K` a pseudo-coherent object of `D(𝒪_X)` whose cohomology is supported on `T`.
Then `K = hocolim Kₙ` for a system of perfect objects `Kₙ` supported on `T` whose coprojections
`cₙ : Kₙ ⟶ K` induce isomorphisms `τ_{≥ -n} Kₙ ⟶ τ_{≥ -n} K` for every `n`. -/
theorem exists_perfect_hocolim_of_isPseudoCoherent_of_supportedOn [CompactSpace X]
    [QuasiSeparatedSpace X] (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (K : DerivedCategory X.Modules)
    (hK : @Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn _ X.ringCatSheaf h T K)
    (hpc : @RingedSpace.IsPseudoCoherent X.toRingedSpace h K) :
    ∃ (F : ℕ ⥤ DerivedCategory X.Modules) (_ : HasCoproduct F.obj) (c : ∀ n, F.obj n ⟶ K),
      (∀ n, @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h (F.obj n)) ∧
      (∀ n, @Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn _ X.ringCatSheaf h T
        (F.obj n)) ∧
      IsHomotopyColimitWith F K c ∧
      ∀ n : ℕ, IsIso ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).map (c n)) := by
  let Good : DerivedCategory X.Modules → Prop := fun P =>
    @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h P ∧
      @Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn _ X.ringCatSheaf h T P
  obtain ⟨P₀, α₀, hP₀, hP₀T, hα₀⟩ :=
    exists_perfect_approximation_of_isPseudoCoherent hT hTc hK hpc (-1)
  let start : ApproximationStage Good K 0 :=
    ⟨⟨P₀, α₀⟩, ⟨hP₀, hP₀T⟩, fun i hi => hα₀ i (by omega)⟩
  have step : ∀ (n : ℕ) (s : ApproximationStage Good K n),
      ∃ (s' : ApproximationStage Good K (n + 1)) (g : s.1.1 ⟶ s'.1.1), g ≫ s'.1.2 = s.1.2 := by
    intro n s
    obtain ⟨P', α', g, hgood, hiso, hcomm⟩ :=
      exists_approximation_step hT hTc hK hpc n s.1.2 s.2.1.1
    exact ⟨⟨⟨P', α'⟩, hgood, fun i hi => hiso i (by omega)⟩, g, hcomm⟩
  have := hasColimitsOfShape_discrete_nat_derivedCategory X
  have := hasExactColimitsOfShape_nat_modules X
  have := preservesColimitsOfShape_discrete_nat_homologyFunctor X
  refine ⟨approximationTowerFunctor start step, inferInstance, approximationTowerι start step,
    fun n => (good_approximationTowerFunctor_obj start step n).1,
    fun n => (good_approximationTowerFunctor_obj start step n).2,
    isHomotopyColimitWith_approximationTower start step,
    fun n => (isIso_truncGE_map_iff _ _).2
      (isIso_homologyFunctor_map_approximationTowerι start step n)⟩

/-- **[Stacks, Tag 0DJN].** Let `X` be a quasi-compact and quasi-separated scheme and let `K` be an
object of `D(𝒪_X)`. The following are equivalent:
1. `K` is pseudo-coherent;
2. `K = hocolim Kₙ` where each `Kₙ` is perfect and `τ_{≥ -n} Kₙ ⟶ τ_{≥ -n} K` is an
   isomorphism for all `n`.

Here `K = hocolim Kₙ` is `CategoryTheory.Pretriangulated.IsHomotopyColimitWith F K c` (Definition
090Z, recording the coprojections `cₙ : Kₙ ⟶ K`), the map `τ_{≥ -n} Kₙ ⟶ τ_{≥ -n} K` is the
truncation of the coprojection `cₙ`, and the derived category is an arbitrary model of `D(𝒪_X)`.
The system is indexed by `n = 0, 1, 2, …`, as in Definition 090Z; a system `K₁ ⟶ K₂ ⟶ ⋯` indexed
from `1` as in the source's proof is the case `Kₙ ↦ Kₙ₊₁`, which satisfies the condition at `n`
because it does at `n + 1`. -/
@[stacks 0DJN]
theorem isPseudoCoherent_iff_exists_perfect_hocolim [CompactSpace X] [QuasiSeparatedSpace X]
    (K : DerivedCategory X.Modules) :
    @RingedSpace.IsPseudoCoherent X.toRingedSpace h K ↔
      ∃ (F : ℕ ⥤ DerivedCategory X.Modules) (_ : HasCoproduct F.obj) (c : ∀ n, F.obj n ⟶ K),
        (∀ n, @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h (F.obj n)) ∧
        IsHomotopyColimitWith F K c ∧
        ∀ n : ℕ, IsIso ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).map (c n)) := by
  refine ⟨fun hpc => ?_, fun ⟨F, hF, c, hP, hc, htr⟩ =>
    @isPseudoCoherent_of_isHomotopyColimitWith_perfect X.toRingedSpace h K F hF c hP hc htr⟩
  obtain ⟨F, hF, c, hP, -, hc, htr⟩ :=
    exists_perfect_hocolim_of_isPseudoCoherent_of_supportedOn Set.univ isClosed_univ
      (by simp) K (fun _ _ hx => absurd trivial hx) hpc
  exact ⟨F, hF, c, hP, hc, htr⟩

end Scheme

end Stacks.PseudoCoherentHocolim

end
