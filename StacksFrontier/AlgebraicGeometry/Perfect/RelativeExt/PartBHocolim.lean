module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.PartBSystem
public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.TorsionFreeAndDivisibleSystems

/-!
# The homotopy colimit `L = hocolim Lₙ` of [Stacks, Tag 08IF] (B) and its unit

In the situation of `Stacks.Cohomology.RelativeExt.PartBApproxSystem`, let `L = hocolim Lₙ` in
`D(𝒪_S)` with coprojections `dₙ`, and suppose that the cohomology sheaves of `L` are the
colimits of those of the `Lₙ` ([Stacks, Tag 0CRK]). Then:

* `dₙ` induces an isomorphism on `τ_{≥ k}` for `k ≥ -n - b`, since the transition maps do from
  `n` on;
* the units `uₙ : Eₙ ⟶ Φ(Lₙ)` glue to `η : E ⟶ Φ(L)` with `cₙ ≫ η = uₙ ≫ Φ(dₙ)`;
* for every such `η` and every `N ∈ D^+_QCoh(𝒪_S)`, composition with `η` identifies `Hom(L, N)`
  with `Hom(E, Φ N)`.

This is the source's "the mapping property of homotopy colimits gives that
`Ext^i(L, ℱ) = Ext^i(L_n, ℱ)`".

## Main results

* `Stacks.Cohomology.RelativeExt.isIso_truncGE_partBCoprojection`
* `Stacks.Cohomology.RelativeExt.exists_partBHocolimUnit`
* `Stacks.Cohomology.RelativeExt.bijective_partBHocolimUnit_comp`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe u

namespace Stacks.Cohomology.RelativeExt

attribute [local instance] HasDerivedCategory.standard hasSheafifyOpensSpace
  wEqualsLocallyBijectiveOpensSpace

variable {U S : Scheme.{u}} {g : U ⟶ S} {G : CochainComplex (TModules U.toRingedSpace) ℤ}
  {E : DStd U} (D : PartBApproxSystem g G E) (hG : IsBoundedFlatOver g.toLRSHom.toShHom G)
  [HasCoproduct (partBSystem D).obj] {L : DStd S} {d : ∀ n, (partBSystem D).obj n ⟶ L}
  (hL : IsHomotopyColimitWith (partBSystem D) L d)

/-- A map out of `∐ Fₙ` kills `1 - fₙ` iff its restrictions to the summands are compatible. -/
private theorem desc_sub_comp_eq_zero_iff {C : Type*} [Category C] [Preadditive C] {F : ℕ ⥤ C}
    [HasCoproduct F.obj] {Z : C} (p : ∐ F.obj ⟶ Z) :
    (Limits.Sigma.desc fun n ↦ Limits.Sigma.ι F.obj n -
      F.map (homOfLE (Nat.le_succ n)) ≫ Limits.Sigma.ι F.obj (n + 1)) ≫ p = 0 ↔
    ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ Limits.Sigma.ι F.obj (n + 1) ≫ p =
      Limits.Sigma.ι F.obj n ≫ p := by
  refine ⟨fun h n ↦ ?_, fun h ↦ Limits.Sigma.hom_ext _ _ fun n ↦ ?_⟩
  · have h1 := congrArg (fun k ↦ Limits.Sigma.ι F.obj n ≫ k) h
    rw [comp_zero, ← Category.assoc, Limits.Sigma.ι_comp_desc, Preadditive.sub_comp,
      Category.assoc, sub_eq_zero] at h1
    exact h1.symm
  · rw [← Category.assoc, Limits.Sigma.ι_comp_desc, Preadditive.sub_comp, Category.assoc, h n,
      sub_self, comp_zero]

include hL in
/-- The coprojections of `L = hocolim Lₙ` are compatible with the transition maps. -/
theorem partBTransition_comp_coprojection (n : ℕ) :
    partBTransition D n ≫ d (n + 1) = d n := by
  obtain ⟨p, q, hT, hc⟩ := hL
  have h1 := (desc_sub_comp_eq_zero_iff p).1 (comp_distTriang_mor_zero₁₂ _ hT) n
  rwa [hc, hc, partBSystem_map_succ] at h1

include hG hL in
/-- **The units glue to `η : E ⟶ Φ(L)`** with `cₙ ≫ η = uₙ ≫ Φ(dₙ)`. -/
theorem exists_partBHocolimUnit :
    ∃ η : E ⟶ (partBΦ hG).obj L, ∀ n, D.c n ≫ η = partBUnit D hG n ≫ (partBΦ hG).map (d n) := by
  have := D.hasCoproduct
  obtain ⟨p, q, hT, hc⟩ := D.hocolim
  let x : ∀ n, D.sys.obj n ⟶ (partBΦ hG).obj L := fun n ↦ partBUnit D hG n ≫ (partBΦ hG).map (d n)
  have hx : ∀ n, D.sys.map (homOfLE (Nat.le_succ n)) ≫ x (n + 1) = x n := fun n ↦
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
      (partBUnit_comp_transition D hG n)).trans ((Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) (((partBΦ hG).map_comp _ _).symm.trans
          (congrArg (partBΦ hG).map (partBTransition_comp_coprojection D hL n))))))
  have hw := (desc_sub_comp_eq_zero_iff (Limits.Sigma.desc x)).2 fun n ↦ by
    simpa only [Limits.Sigma.ι_comp_desc] using hx n
  obtain ⟨y, hy⟩ := Triangle.yoneda_exact₂ _ hT (Limits.Sigma.desc x) hw
  refine ⟨y, fun n ↦ ?_⟩
  have h1 := congrArg (fun k ↦ Limits.Sigma.ι D.sys.obj n ≫ k) hy
  simp only [Triangle.mk_mor₂, Limits.Sigma.ι_comp_desc] at h1
  exact ((congrArg (· ≫ y) (hc n)).symm.trans (Category.assoc _ _ _)).trans h1.symm

/-- **The cohomology of `L` is the colimit of the cohomology of the `Lₙ`** ([Stacks, Tag 0CRK]),
with the colimit legs the images of the coprojections. -/
def PartBHomologyColimit [∀ i : ℤ, HasColimit
    (partBSystem D ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing S.toRingedSpace)) i)] (L₀ : DStd S)
    (d₀ : ∀ n, (partBSystem D).obj n ⟶ L₀) : Prop :=
  ∀ i : ℤ, ∃ e : colimit (partBSystem D ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing S.toRingedSpace)) i) ≅
      (DerivedCategory.homologyFunctor _ i).obj L₀, ∀ n : ℕ,
    colimit.ι (partBSystem D ⋙ DerivedCategory.homologyFunctor _ i) n ≫ e.hom =
      (DerivedCategory.homologyFunctor _ i).map (d₀ n)

include hG in
omit [HasCoproduct (partBSystem D).obj] in
/-- **`dₙ : Lₙ ⟶ L` induces an isomorphism on `τ_{≥ k}` for `k ≥ -n - b`**, `𝒢` living in degrees
`≥ b`: the transition maps do from `n` on, and the cohomology of `L` is their colimit. -/
theorem isIso_truncGE_partBCoprojection (b : ℤ) (hb : G.IsStrictlyGE b)
    [∀ i : ℤ, HasColimit (partBSystem D ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing S.toRingedSpace)) i)]
    (hcolim : PartBHomologyColimit D L d) (n : ℕ) (k : ℤ) (hk : -(n : ℤ) - b ≤ k) :
    IsIso ((DerivedCategory.TStructure.t.truncGE k).map (d n)) := by
  refine (isIso_truncGE_map_iff_isIso_homology (d n) k).2 fun i hi => ?_
  obtain ⟨e, he⟩ := hcolim i
  have : IsIso (colimit.ι (partBSystem D ⋙ DerivedCategory.homologyFunctor _ i) n) :=
    Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.DivColim.isIso_colimit_ι_of_eventually_iso
      _ n fun m hm => by
        change IsIso ((DerivedCategory.homologyFunctor _ i).map
          ((partBSystem D).map (homOfLE (Nat.le_succ m))))
        rw [partBSystem_map_succ]
        exact (isIso_truncGE_map_iff_isIso_homology (partBTransition D m) k).1
          (isIso_truncGE_partBTransition D hG b hb m k (by omega)) i hi
  rw [← he n]
  infer_instance

include hG in
omit [HasCoproduct (partBSystem D).obj] in
/-- **The unit `η : E ⟶ Φ(L)` identifies `Hom(L, N)` with `Hom(E, Φ N)` for every
`N ∈ D^+_QCoh(𝒪_S)`.** -/
theorem bijective_partBHocolimUnit_comp (b : ℤ) (hb : G.IsStrictlyGE b)
    [∀ i : ℤ, HasColimit (partBSystem D ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing S.toRingedSpace)) i)]
    (hcolim : PartBHomologyColimit D L d) (η : E ⟶ (partBΦ hG).obj L)
    (hη : ∀ n, D.c n ≫ η = partBUnit D hG n ≫ (partBΦ hG).map (d n))
    (N : DStd S) (hN : qcohDerived S N) (m : ℤ) (hm : N.IsGE m) :
    Function.Bijective (fun ψ : L ⟶ N ↦ η ≫ (partBΦ hG).map ψ) := by
  let k := min m (m + b)
  let n : ℕ := (-k).toNat + (-k - b).toNat
  have hk₁ := Int.self_le_toNat (-k)
  have hk₂ := Int.self_le_toNat (-k - b)
  have hn : -(n : ℤ) ≤ k ∧ -(n : ℤ) - b ≤ k := by
    simp only [n]
    push_cast
    omega
  have hc := isIso_truncGE_map_of_le (D.c n) hn.1 (D.trunc n)
  have hd := isIso_truncGE_partBCoprojection D hG b hb hcolim n k hn.2
  have hNk : N.IsGE k := DerivedCategory.TStructure.t.isGE_of_ge N k m (min_le_left _ _)
  have hΦN : ((partBΦ hG).obj N).IsGE (m + b) :=
    @Stacks.Cohomology.RelativeExtCanonical.isGE_pullbackTensorDerivedFunctor_obj _ _
      g.toLRSHom.toShHom _ hG b hb N m hm
  have hΦNk : ((partBΦ hG).obj N).IsGE k :=
    DerivedCategory.TStructure.t.isGE_of_ge _ k (m + b) (min_le_right _ _)
  have h1 := bijective_comp_of_isIso_truncGE (d n) k hd N hNk
  have h2 := bijective_comp_of_isIso_truncGE (D.c n) k hc _ hΦNk
  have hcomm : (fun x : E ⟶ (partBΦ hG).obj N ↦ D.c n ≫ x) ∘
      (fun ψ : L ⟶ N ↦ η ≫ (partBΦ hG).map ψ) =
      (fun ψ : partBL D n ⟶ N ↦ partBUnit D hG n ≫ (partBΦ hG).map ψ) ∘
        (fun x : L ⟶ N ↦ d n ≫ x) := by
    funext ψ
    simp only [Function.comp_apply]
    rw [← Category.assoc, hη, Category.assoc]
    exact congrArg (_ ≫ ·) ((partBΦ hG).map_comp _ _).symm
  refine (Function.Bijective.of_comp_iff' h2 _).1 ?_
  rw [hcomm]
  exact (bijective_partBUnit_comp D hG n N hN).comp h1

end Stacks.Cohomology.RelativeExt

end
