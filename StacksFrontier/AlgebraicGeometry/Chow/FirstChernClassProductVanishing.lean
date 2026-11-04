module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.TotalClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapDimensionInduction
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernClassBivariant

/-!
# Products of first Chern classes vanish above the dimension

Let `(S, δ)` be as in Situation 02QL of the Stacks Project, and let `X` be a scheme of finite type
over `S` which has an ample invertible module and has dimension `d < ∞`. Stacks 0FDX says that for
invertible `𝒪_X`-modules `ℒ_1, …, ℒ_{d+1}`

  `c₁(ℒ_1) ∘ ⋯ ∘ c₁(ℒ_{d+1}) = 0`   in `A^{d+1}(X)`.

Here `c₁(ℒ) ∈ A^1(X)` is the bivariant first Chern class of Stacks 0B77
(`Stacks.Chow.GenuineChern.firstChernClass`), and the product is the composition of bivariant
classes of Stacks 0B75 at the Gysin system of the first Chern class rule, read as a product of
Chow cohomology classes of `X` (`Stacks.Chow.BivariantClass.mulId`).

## Main definitions

* `Stacks.Chow.firstChernClassProduct` — the product `c₁(ℒ_0) ∘ c₁(ℒ_1) ∘ ⋯ ∘ c₁(ℒ_n)` in
  `A^{n+1}(X)` of the first Chern classes of a family of invertible modules.

## Main results

* `Stacks.Chow.idRule_firstChernClassProduct` — on a test scheme `g : T ⟶ X` the product acts as
  the iterated cap product `c₁(g^*ℒ_0) ∩ ⋯ ∩ c₁(g^*ℒ_n) ∩ -`.
* `Stacks.Chow.firstChernClassProduct_eq_zero_of_topologicalKrullDim_le` — **Stacks 0FDX**.

## Implementation notes

A Chow cohomology class is determined by its operations on all test schemes
(`Stacks.Chow.BivariantClass.eq_of_idRule_eq`), and the operation of the product is the iterated
cap product, so the vanishing reduces to the vanishing of
`c₁(g^*ℒ_1) ∩ ⋯ ∩ c₁(g^*ℒ_{d+1}) ∩ -` on **every** test scheme `g : T ⟶ X` locally of finite type,
with no bound on the dimension of `T`. That is the source's induction on `d`,
`Stacks.Chow.iteratedChernCapOnChow_ofFn_eq_zero_of_topologicalKrullDim_le`. Its Noetherian
hypothesis holds because an ample invertible module forces `X` to be quasi-compact (Stacks 01PS)
and `X` is locally Noetherian, being locally of finite type over the locally Noetherian `S`.

The dimension hypothesis is taken as `dim X ≤ d`, which contains the case `dim X = d` of the
source.

## References

* [Stacks Project, Tag 0FDX](https://stacks.math.columbia.edu/tag/0FDX)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B77](https://stacks.math.columbia.edu/tag/0B77)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The product of the first Chern classes of a family of invertible modules.** For invertible
`𝒪_X`-modules `ℒ_0, …, ℒ_n` this is `c₁(ℒ_0) ∘ (c₁(ℒ_1) ∘ ⋯ ∘ c₁(ℒ_n)) ∈ A^{n+1}(X)`, the
iterated product of Chow cohomology classes (Stacks 0B75) of the bivariant first Chern classes of
Stacks 0B77. -/
def firstChernClassProduct : (n : ℕ) → (L : Fin (n + 1) → X.Modules) →
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (L i)] →
    BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX)
      ((n + 1 : ℕ) : ℤ)
  | 0, L, _ =>
      bivariantClassDegreeCongr C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX)
        (by simp) (GenuineChern.firstChernClass C sX (L 0))
  | n + 1, L, _ =>
      bivariantClassDegreeCongr C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX)
        (by push_cast; ring)
        ((GenuineChern.firstChernClass C sX (L 0)).mulId C sX
          (firstChernClassProduct n fun i => L i.succ))

/-- Two degree transports of the same Chow class are heterogeneously equal. -/
private theorem chowGroupCast_heq_chowGroupCast (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (q : Y ⟶ C.S) [LocallyOfFiniteType q] {a b c : ℤ} (h : a = b) (h' : a = c)
    (x : chowGroup C q a) : chowGroupCast C q h x ≍ chowGroupCast C q h' x :=
  (chowGroupCast_heq C q h x).trans (chowGroupCast_heq C q h' x).symm

/-- Rewriting the list of operators of an iterated cap product, up to a degree transport. -/
private theorem heq_iteratedChernCapOnChow_of_eq (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (q : Y ⟶ C.S) [LocallyOfFiniteType q] {Os Os' : List (ChernCapOperator C q)} (hO : Os = Os')
    (d : ℤ) (x : chowGroup C q (d + (Os.length : ℤ))) {z : Type _} {a : z}
    (h : a ≍ iteratedChernCapOnChow C q Os' d
      (chowGroupCast C q (by rw [hO]) x)) :
    a ≍ iteratedChernCapOnChow C q Os d x :=
  h.trans (iteratedChernCapOnChow_heq_of_eq C q hO d (chowGroupCast_heq C q _ x).symm).symm

open scoped Stacks.AlgebraicGeometry.AmpleLimit in
/-- **The operation of a product of first Chern classes is the iterated cap product.** On a test
scheme `g : T ⟶ X` locally of finite type, `c₁(ℒ_0) ∘ ⋯ ∘ c₁(ℒ_n)` acts as

  `c₁(g^*ℒ_0) ∩ ⋯ ∩ c₁(g^*ℒ_n) ∩ -`,

the operator of `ℒ_n` acting first; the two sides lie in Chow groups of equal but not identical
degrees, whence the heterogeneous equality. -/
theorem idRule_firstChernClassProduct (n : ℕ) (L : Fin (n + 1) → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L i)]
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (β : chowGroup C (g ≫ sX)
      (k + ((List.ofFn fun i => invCap C (g ≫ sX) ((Scheme.Modules.pullback g).obj (L i))).length :
        ℤ))) :
    (firstChernClassProduct C sX n L).idRule C sX (gysinSystemOfInvertible C) g _ β ≍
      iteratedChernCapOnChow C (g ≫ sX)
        (List.ofFn fun i => invCap C (g ≫ sX) ((Scheme.Modules.pullback g).obj (L i))) k β := by
  induction n generalizing k with
  | zero =>
    have hO : (List.ofFn fun i => invCap C (g ≫ sX) ((Scheme.Modules.pullback g).obj (L i))) =
        [invCap C (g ≫ sX) ((Scheme.Modules.pullback g).obj (L 0))] := by
      simp [List.ofFn_succ]
    have hk : k + ((List.ofFn fun i =>
        invCap C (g ≫ sX) ((Scheme.Modules.pullback g).obj (L i))).length : ℤ) = k + 1 := by
      simp
    refine (BivariantClass.idRule_bivariantClassDegreeCongr C (gysinSystemOfInvertible C) sX
      (by simp) (GenuineChern.firstChernClass C sX (L 0)) g _ β).trans ?_
    rw [GenuineChern.idRule_firstChernClass]
    refine heq_iteratedChernCapOnChow_of_eq C (g ≫ sX) hO k β ?_
    rw [iteratedChernCapOnChow_singleton_eq C (g ≫ sX) _ k _ (chowGroupCast C (g ≫ sX) hk β)
      (chowGroupCast_heq_chowGroupCast C (g ≫ sX) _ hk β)]
    exact capOnChow_heq C (g ≫ sX) _ (by simp) (chowGroupCast_heq_chowGroupCast C (g ≫ sX) _ hk β)
  | succ n ih =>
    set Ot := List.ofFn fun i : Fin (n + 1) =>
      invCap C (g ≫ sX) ((Scheme.Modules.pullback g).obj (L i.succ)) with hOt
    have hO : (List.ofFn fun i => invCap C (g ≫ sX) ((Scheme.Modules.pullback g).obj (L i))) =
        invCap C (g ≫ sX) ((Scheme.Modules.pullback g).obj (L 0)) :: Ot := by
      rw [List.ofFn_succ]
    have hlen : ((List.ofFn fun i =>
        invCap C (g ≫ sX) ((Scheme.Modules.pullback g).obj (L i))).length : ℤ) =
        (Ot.length : ℤ) + 1 := by
      simp [hOt]
    have hk : k + ((List.ofFn fun i =>
        invCap C (g ≫ sX) ((Scheme.Modules.pullback g).obj (L i))).length : ℤ) =
        k + 1 + (Ot.length : ℤ) := by
      rw [hlen]; ring
    have hlt : (Ot.length : ℤ) = ((n + 1 : ℕ) : ℤ) := by simp [hOt]
    -- the tail product, by the inductive hypothesis
    have htail := ih (fun i => L i.succ) (k + 1) (chowGroupCast C (g ≫ sX) hk β)
    -- unfold the product: `c₁(ℒ_0)` after the tail product
    refine (BivariantClass.idRule_bivariantClassDegreeCongr C (gysinSystemOfInvertible C) sX
      (by push_cast; ring) _ g _ β).trans ?_
    refine (BivariantClass.idRule_mulId C sX _ _ g _ β).trans ?_
    rw [GenuineChern.idRule_firstChernClass]
    refine heq_iteratedChernCapOnChow_of_eq C (g ≫ sX) hO k β ?_
    rw [iteratedChernCapOnChow_cons_eq C (g ≫ sX) _ Ot k _ (chowGroupCast C (g ≫ sX) hk β)
      (chowGroupCast_heq_chowGroupCast C (g ≫ sX) _ hk β)]
    refine capOnChow_heq C (g ≫ sX) _ (by rw [hk, hlt]; ring) ?_
    refine (chowGroupCast_heq C (g ≫ sX) _ _).trans ?_
    refine HEq.trans ?_ htail
    exact IdentityCapRule.heq_congr C sX _ rfl hk (chowGroupCast_heq C (g ≫ sX) hk β).symm

/-- **Stacks 0FDX.** Let `X` be a scheme of finite type over the base scheme `S` of chapter 42
which has an ample invertible module `A`, and let `dim X ≤ d`. Then for invertible
`𝒪_X`-modules `ℒ_1, …, ℒ_{d+1}` on `X`

  `c₁(ℒ_1) ∘ ⋯ ∘ c₁(ℒ_{d+1}) = 0`   in `A^{d+1}(X)`,

the product being the composition of Stacks 0B75 of the bivariant first Chern classes of
Stacks 0B77, at the Gysin system of the first Chern class rule. -/
@[stacks 0FDX]
theorem firstChernClassProduct_eq_zero_of_topologicalKrullDim_le [QuasiCompact sX]
    (A : X.Modules) [Stacks.Ample.IsInvertibleModule X A] (hA : Stacks.Ample.IsAmple X A)
    (d : ℕ) (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (L : Fin (d + 1) → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L i)] :
    firstChernClassProduct C sX d L = 0 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := hA.compactSpace
  have : IsNoetherian X := { }
  refine BivariantClass.eq_of_idRule_eq C sX (gysinSystemOfInvertible C) _ _ ?_
  intro T g _ k α
  rw [BivariantClass.idRule_zero]
  set Os := List.ofFn fun i => invCap C (g ≫ sX) ((Scheme.Modules.pullback g).obj (L i)) with hOs
  have hk : k = k - (Os.length : ℤ) + (Os.length : ℤ) := by ring
  have hdeg : k - ((d + 1 : ℕ) : ℤ) = k - (Os.length : ℤ) := by simp [hOs]
  have key : (firstChernClassProduct C sX d L).idRule C sX (gysinSystemOfInvertible C) g k α ≍
      (0 : chowGroup C (g ≫ sX) (k - (Os.length : ℤ))) := by
    refine (IdentityCapRule.heq_congr C sX _ rfl hk (chowGroupCast_heq C (g ≫ sX) hk α).symm).trans
      ?_
    refine (idRule_firstChernClassProduct C sX d L g _ _).trans ?_
    rw [iteratedChernCapOnChow_ofFn_eq_zero_of_topologicalKrullDim_le C d sX A hA hdim L g
      (g ≫ sX) rfl]
  revert key
  generalize (firstChernClassProduct C sX d L).idRule C sX (gysinSystemOfInvertible C) g k α = x
  revert x
  rw [hdeg]
  intro x hx
  exact eq_of_heq hx

end Stacks.Chow

end
