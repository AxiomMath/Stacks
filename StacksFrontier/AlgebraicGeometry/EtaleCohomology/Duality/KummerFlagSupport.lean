module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerFlagTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CyclicCoverSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionStalkTrace

/-!
# The support of the flag sheaf

Let `D` be a flag of `d` divisor data `(j_m : V_m ⟶ U, i_m : W_m ⟶ U, a_m)` on `U` and
`F = E_0 ⋯ E_{d-1} Λ_U`, `E_m = i_{m*} i_m⁻¹`, the sheaf carrying the Kummer flag class
(`Stacks.EtaleCohomology.KummerFlag.flagSheaf`). This file computes `F` on the closed part and on
the open parts.

* If `g : S ⟶ U` factors through every `W_m`, the inverse image along `g` of the canonical map
  `Λ_U ⟶ F` is an isomorphism (`isIso_inverseImage_map_flagUnit`): `i⁻¹` of the unit of
  `i⁻¹ ⊣ i_*` is invertible for a closed immersion, and `i⁻¹ i_* ≅ 𝟭`.
* If `g` factors through some `V_m`, then `g⁻¹ F = 0` (`isZero_inverseImage_flagSheaf`): for
  `m = 0` because `j_0⁻¹ i_{0*} = 0`, and for `m > 0` because `g⁻¹ E_0 ≅ E'_0 g⁻¹` for the
  divisor datum pulled back along `g` (`Stacks.EtaleCohomology.closedRestrictionInverseImageIso`).
* Hence if `k : T ⟶ U` is a closed immersion through every `W_m` whose complement is covered by
  the `V_m`, then `F ≅ k_* Λ_T` (`nonempty_flagSheaf_iso`), the unit `F ⟶ k_* k⁻¹ F` being
  invertible after inverse image along `k` and along every `j_m`; and for `T` nonempty the
  canonical map `Λ_U ⟶ F` is nonzero (`flagUnit_ne_zero`).

## Main results

* `Stacks.EtaleCohomology.KummerFlag.isIso_inverseImage_map_flagUnit`
* `Stacks.EtaleCohomology.KummerFlag.isZero_inverseImage_flagSheaf`
* `Stacks.EtaleCohomology.KummerFlag.nonempty_flagSheaf_iso`
* `Stacks.EtaleCohomology.KummerFlag.flagUnit_ne_zero`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology.KummerFlag

attribute [local instance] moduleCat_hasLimitsOfSize

variable {N : ℕ} {U : Scheme.{u}}

section ClosedImmersion

variable {W : Scheme.{u}} (i : W ⟶ U) [IsClosedImmersion i]

/-- `i⁻¹` of the unit of `i⁻¹ ⊣ i_*` is invertible along a closed immersion `i`. -/
theorem isIso_inverseImage_map_unit_app (A : EtaleModules.{u, 0} (ZMod N) U) :
    IsIso ((etaleModuleInverseImage.{u, 0} (ZMod N) i).map
      ((etaleModuleInverseImageAdj.{u, 0} (ZMod N) i).unit.app A)) := by
  let adj := etaleModuleInverseImageAdj.{u, 0} (ZMod N) i
  let L := etaleModuleInverseImage.{u, 0} (ZMod N) i
  have h : L.map (adj.unit.app A) ≫ adj.counit.app (L.obj A) = 𝟙 (L.obj A) :=
    adj.left_triangle_components A
  have : IsIso (L.map (adj.unit.app A) ≫ adj.counit.app (L.obj A)) := by
    rw [h]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_right _ (adj.counit.app (L.obj A))

/-- The inverse image along a map through `i` of the unit of `i⁻¹ ⊣ i_*` is invertible. -/
theorem isIso_inverseImage_comp_map_unit_app {S : Scheme.{u}} (g' : S ⟶ W)
    (A : EtaleModules.{u, 0} (ZMod N) U) :
    IsIso ((etaleModuleInverseImage.{u, 0} (ZMod N) (g' ≫ i)).map
      ((etaleModuleInverseImageAdj.{u, 0} (ZMod N) i).unit.app A)) := by
  rw [NatIso.isIso_map_iff (etaleModuleInverseImageCompIso.{u, 0} (ZMod N) g' i)]
  have := isIso_inverseImage_map_unit_app (N := N) i A
  show IsIso ((etaleModuleInverseImage.{u, 0} (ZMod N) g').map
    ((etaleModuleInverseImage.{u, 0} (ZMod N) i).map
      ((etaleModuleInverseImageAdj.{u, 0} (ZMod N) i).unit.app A)))
  infer_instance

/-- The inverse image along a map through `i` of `E(f) = i_* i⁻¹ f` is invertible when that of
`f` is. -/
theorem isIso_inverseImage_comp_map_closedRestriction_map {S : Scheme.{u}} (g' : S ⟶ W)
    {A B : EtaleModules.{u, 0} (ZMod N) U} (f : A ⟶ B)
    (hf : IsIso ((etaleModuleInverseImage.{u, 0} (ZMod N) (g' ≫ i)).map f)) :
    IsIso ((etaleModuleInverseImage.{u, 0} (ZMod N) (g' ≫ i)).map
      ((closedRestriction (N := N) i).map f)) := by
  rw [NatIso.isIso_map_iff (etaleModuleInverseImageCompIso.{u, 0} (ZMod N) g' i)] at hf ⊢
  let adj := etaleModuleInverseImageAdj.{u, 0} (ZMod N) i
  let G := etaleModuleInverseImage.{u, 0} (ZMod N) g'
  let x := (etaleModuleInverseImage.{u, 0} (ZMod N) i).map f
  have hx : IsIso (G.map x) := hf
  have key : G.map ((etaleModuleInverseImage.{u, 0} (ZMod N) i).map
      ((etaleModuleDirectImage.{u, 0} (ZMod N) i).map x)) ≫ G.map (adj.counit.app _) =
      G.map (adj.counit.app _) ≫ G.map x := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg G.map (adj.counit.naturality x)
  have : IsIso (G.map ((etaleModuleInverseImage.{u, 0} (ZMod N) i).map
      ((etaleModuleDirectImage.{u, 0} (ZMod N) i).map x)) ≫ G.map (adj.counit.app _)) := by
    rw [key]
    infer_instance
  show IsIso (G.map ((etaleModuleInverseImage.{u, 0} (ZMod N) i).map
      ((etaleModuleDirectImage.{u, 0} (ZMod N) i).map x)))
  exact IsIso.of_isIso_comp_right _ (G.map (adj.counit.app _))

end ClosedImmersion

/-- **The canonical map `Λ_U ⟶ E_0 ⋯ E_{d-1} Λ_U` is invertible on the closed part**: its
inverse image along any `g` factoring through every `W_m` is an isomorphism. -/
theorem isIso_inverseImage_map_flagUnit : ∀ {d : ℕ} (D : Fin d → DivisorDatum U)
    {S : Scheme.{u}} (g : S ⟶ U), (∀ m, ∃ g' : S ⟶ (D m).W, g' ≫ (D m).i = g) →
    IsIso ((etaleModuleInverseImage.{u, 0} (ZMod N) g).map (flagUnit (N := N) D))
  | 0, D, S, g, _ => by
    show IsIso ((etaleModuleInverseImage.{u, 0} (ZMod N) g).map (𝟙 _))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  | d + 1, D, S, g, hg => by
    obtain ⟨g', rfl⟩ := hg 0
    show IsIso ((etaleModuleInverseImage.{u, 0} (ZMod N) (g' ≫ (D 0).i)).map
      ((etaleModuleInverseImageAdj.{u, 0} (ZMod N) (D 0).i).unit.app (unitSheaf N) ≫
        (closedRestriction (N := N) (D 0).i).map (flagUnit (fun m => D m.succ))))
    rw [CategoryTheory.Functor.map_comp]
    have h1 := isIso_inverseImage_comp_map_unit_app (N := N) (D 0).i g' (unitSheaf N)
    have h2 := isIso_inverseImage_comp_map_closedRestriction_map (N := N) (D 0).i g'
      (flagUnit (N := N) (fun m => D m.succ))
      (isIso_inverseImage_map_flagUnit (fun m => D m.succ) (g' ≫ (D 0).i) (fun m => hg m.succ))
    infer_instance

/-- The inverse image along an étale `j` of a direct image along `i` is zero when the ranges of
`i` and `j` are disjoint. -/
private theorem isZero_inverseImage_directImage_of_disjoint {Z S : Scheme.{u}} (i : Z ⟶ U)
    (j : S ⟶ U) [Etale j] (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (A : EtaleModules.{u, 0} (ZMod N) Z) :
    IsZero ((etaleModuleInverseImage.{u, 0} (ZMod N) j).obj
      ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj A)) :=
  (isZero_etaleModuleRestriction_etaleModuleDirectImage_of_disjoint (ZMod N) i j hij _).of_iso
    ((etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod N) j).app _)

/-- **The flag sheaf vanishes on the open parts**: its inverse image along any `g` factoring
through some `V_m` is zero. -/
theorem isZero_inverseImage_flagSheaf : ∀ {d : ℕ} (D : Fin d → DivisorDatum U)
    {S : Scheme.{u}} (g : S ⟶ U) (m : Fin d), (∃ g' : S ⟶ (D m).V, g' ≫ (D m).j = g) →
    IsZero ((etaleModuleInverseImage.{u, 0} (ZMod N) g).obj (flagSheaf (N := N) D))
  | 0, _, _, _, m, _ => m.elim0
  | d + 1, D, S, g, m, hm => by
    show IsZero ((etaleModuleInverseImage.{u, 0} (ZMod N) g).obj
      ((closedRestriction (N := N) (D 0).i).obj (flagSheaf (N := N) (fun m => D m.succ))))
    induction m using Fin.cases with
    | zero =>
      obtain ⟨g', rfl⟩ := hm
      refine IsZero.of_iso ?_ ((etaleModuleInverseImageCompIso.{u, 0} (ZMod N) g' (D 0).j).app _)
      refine (etaleModuleInverseImage.{u, 0} (ZMod N) g').map_isZero ?_
      refine isZero_inverseImage_directImage_of_disjoint _ _ ?_ _
      rw [(D 0).range_eq]
      exact disjoint_compl_right
    | succ m =>
      have hrange : Set.range (pullback.snd (D 0).j g).base =
          (Set.range (pullback.snd (D 0).i g).base)ᶜ := by
        rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, ← Set.preimage_compl]
        congr 1
        exact (D 0).range_eq
      refine IsZero.of_iso ?_ ((closedRestrictionInverseImageIso (ZMod N) g (D 0).i (D 0).j
        (D 0).range_eq (pullback.snd (D 0).i g) (pullback.snd (D 0).j g) hrange
        (pullback.fst (D 0).i g) pullback.condition.symm (pullback.fst (D 0).j g)
        pullback.condition.symm).app (flagSheaf (N := N) (fun m => D m.succ)))
      exact (closedRestrictionFunctor (ZMod N) (pullback.snd (D 0).i g)).map_isZero
        (isZero_inverseImage_flagSheaf (fun m => D m.succ) g m hm)

section Iso

variable {d : ℕ} (D : Fin d → DivisorDatum U) {T : Scheme.{u}} (k : T ⟶ U) [IsClosedImmersion k]
  (hk : ∀ m, ∃ g' : T ⟶ (D m).W, g' ≫ (D m).i = k)

include hk in
/-- **The flag sheaf is the direct image of the constant sheaf of the closed part**: for a
closed immersion `k : T ⟶ U` through every `W_m` whose complement is covered by the `V_m`,
`E_0 ⋯ E_{d-1} Λ_U ≅ k_* Λ_T`. -/
theorem nonempty_flagSheaf_iso
    (hcov : ∀ x : U, x ∉ Set.range k.base → ∃ m, x ∈ Set.range (D m).j.base) :
    Nonempty (flagSheaf (N := N) D ≅
      (etaleModuleDirectImage.{u, 0} (ZMod N) k).obj (unitSheaf (X := T) N)) := by
  let adj := etaleModuleInverseImageAdj.{u, 0} (ZMod N) k
  let F := flagSheaf (N := N) D
  have hunit : IsIso (adj.unit.app F) := by
    let Tf : Option (ULift.{u} (Fin d)) → Scheme.{u} := fun a => a.elim T fun m => (D m.down).V
    let gf : ∀ a, Tf a ⟶ U := fun a => match a with
      | none => k
      | some m => (D m.down).j
    refine isIso_of_isIso_etaleModuleInverseImage_family (ZMod N) gf ?_ _ fun a => ?_
    · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
      by_cases hx : x ∈ Set.range k.base
      · exact ⟨none, hx⟩
      · obtain ⟨m, hm⟩ := hcov x hx
        exact ⟨some (ULift.up m), hm⟩
    · match a with
      | none =>
        exact isIso_inverseImage_map_unit_app (N := N) k F
      | some m =>
        have h₁ : IsZero ((etaleModuleInverseImage.{u, 0} (ZMod N) (D m.down).j).obj F) :=
          isZero_inverseImage_flagSheaf D (D m.down).j m.down ⟨𝟙 _, Category.id_comp _⟩
        have hdisj : Disjoint (Set.range k.base) (Set.range (D m.down).j.base) := by
          rw [(D m.down).range_eq, Set.disjoint_compl_right_iff_subset]
          rintro _ ⟨t, rfl⟩
          obtain ⟨g', hg'⟩ := hk m.down
          exact ⟨g'.base t, by rw [← hg']; rfl⟩
        have h₂ := isZero_inverseImage_directImage_of_disjoint k (D m.down).j hdisj
          ((etaleModuleInverseImage.{u, 0} (ZMod N) k).obj F)
        exact isIso_of_source_target_iso_zero _ h₁.isoZero h₂.isoZero
  have hu := isIso_inverseImage_map_flagUnit (N := N) D k hk
  exact ⟨asIso (adj.unit.app F) ≪≫ (etaleModuleDirectImage.{u, 0} (ZMod N) k).mapIso
    ((asIso ((etaleModuleInverseImage.{u, 0} (ZMod N) k).map (flagUnit (N := N) D))).symm ≪≫
      (constantInverseImageIso (ZMod N) k).symm)⟩

end Iso

/-- The identity of the constant sheaf `ℤ/N` on a nonempty scheme is nonzero. -/
theorem id_unitSheaf_ne_zero [Fact (1 < N)] (T : Scheme.{u}) [Nonempty T] :
    𝟙 (unitSheaf (X := T) N) ≠ 0 := by
  intro h0
  have hsub : Subsingleton (unitSheaf (X := T) N ⟶ unitSheaf (X := T) N) :=
    ⟨fun a b => by rw [← Category.comp_id a, ← Category.comp_id b, h0, comp_zero, comp_zero]⟩
  have h1 : Nat.card (unitSheaf (X := T) N ⟶ unitSheaf (X := T) N) = 1 :=
    Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨𝟙 _⟩⟩
  rw [natCard_hom_unitSheaf_unitSheaf] at h1
  have : Subsingleton (LocallyConstant T (ZMod N)) := (Nat.card_eq_one_iff_unique.1 h1).1
  obtain ⟨t⟩ := ‹Nonempty T›
  simpa using congrArg (fun f : LocallyConstant T (ZMod N) => f t)
    (Subsingleton.elim (LocallyConstant.const T (0 : ZMod N)) (LocallyConstant.const T 1))

/-- **The canonical map `Λ_U ⟶ E_0 ⋯ E_{d-1} Λ_U` is nonzero** as soon as the closed parts meet
in a nonempty `T`. -/
theorem flagUnit_ne_zero [Fact (1 < N)] {d : ℕ} (D : Fin d → DivisorDatum U) {T : Scheme.{u}}
    [Nonempty T] (k : T ⟶ U) (hk : ∀ m, ∃ g' : T ⟶ (D m).W, g' ≫ (D m).i = k) :
    flagUnit (N := N) D ≠ 0 := by
  intro h0
  have hu := isIso_inverseImage_map_flagUnit (N := N) D k hk
  rw [h0, CategoryTheory.Functor.map_zero] at hu
  exact id_unitSheaf_ne_zero T (((IsZero.of_mono_zero _
    ((etaleModuleInverseImage.{u, 0} (ZMod N) k).obj (flagSheaf (N := N) D))).of_iso
    (constantInverseImageIso (ZMod N) k)).eq_of_src _ _)

end Stacks.EtaleCohomology.KummerFlag

end
