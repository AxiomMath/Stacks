module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Additivity
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Support
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.JacobsonDimension
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.IdealFiltration
public import StacksFrontier.AlgebraicGeometry.CoherentDevissageGlue.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Abelian
public import StacksFrontier.AlgebraicGeometry.ConfinedDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.FullSupport.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Functoriality
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.EulerPolynomialProper
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Exactness
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.PushforwardTwist
public import StacksFrontier.AlgebraicGeometry.TwistedSheafEuler.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Dimension.ClosedSubsetDimension

/-!
# The leading term of the Euler-characteristic polynomial of a coherent module

Let `X` be proper over a field `k`, let `ℱ` be a coherent `𝒪_X`-module, let `𝓛_1, …, 𝓛_r` be
invertible `𝒪_X`-modules, and let `d = dim Supp ℱ`. Writing `Z_1, …, Z_t` for the irreducible
components of `Supp ℱ` of dimension `d`, with generic points `ξ_i` and multiplicities
`m_i = length_{𝒪_{X, ξ_i}} ℱ_{ξ_i}`, the function

`(n_1, …, n_r) ↦ χ(X, ℱ ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r})
  − ∑_i m_i · χ(Z_i, 𝒪_{Z_i} ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r})`

is a numerical polynomial of total degree strictly less than `d`. In other words the
leading-degree part of the numerical polynomial of [Stacks, Tag 0BEM] depends only on the
top-dimensional part of the cycle of `ℱ`.

## Main definitions

* `AlgebraicGeometry.TopDimIntegralSubscheme`: the integral closed subschemes of `X` contained
  in `Supp ℱ` and of the same dimension as it — the top-dimensional irreducible components of
  the support, with their reduced induced structures.
* `AlgebraicGeometry.TopDimIntegralSubscheme.genericPt`: the generic point of such a component,
  read in `X`.
* `AlgebraicGeometry.componentTwistEulerCharacteristic`: the Euler characteristic
  `χ(Z, 𝒪_Z ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r})` of a twist of the structure sheaf of such a
  component.

## Main results

* `AlgebraicGeometry.exists_eulerPolynomial_sub_topDimComponents_totalDegree_lt`:
  **[Stacks, Tag 0BEN].**

## Implementation notes

The sum over components is a `finsum` indexed by `TopDimIntegralSubscheme ℱ`, which is finite,
and the multiplicity `m_i` is `Stacks.Chow.sheafMultiplicity`, the length of the stalk at the
generic point. The components are indexed by their reduced closed subscheme structures rather
than by irreducible components of the support, so that the Euler characteristic of a component
can be formed; the two indexings agree because such a subscheme is reduced, hence determined by
its underlying closed set.

The proof follows the source. The difference above is read as a `correctionPolynomial`, built
from the canonical polynomial of [Stacks, Tag 0BEM] attached to a coherent module by
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_isProper` and its uniqueness
(`MvPolynomial.eq_of_eval_intCast`). That correction is additive along short exact sequences of
coherent modules supported in `Supp ℱ`, so the dévissage of [Stacks, Tag 01YF] reduces the
degree bound to the direct images `i_* ℐ` of nonzero coherent sheaves of ideals on integral
closed subschemes `i : Y ⟶ X`. If the image of `i` has dimension less than `d` the weights
vanish and the bound is [Stacks, Tag 0BEM]; otherwise the image is one of the components, and
the sequence `0 → i_* ℐ → i_* 𝒪_Y → i_*(𝒪_Y/ℐ) → 0` reduces the claim to the two facts that
`i_* 𝒪_Y` has correction zero — only the component cut out by `i` contributes, with weight one,
and the projection formula identifies the two Euler characteristics — and that `𝒪_Y/ℐ` is
supported in dimension smaller than `Y`.

## References

* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 0BEN](https://stacks.math.columbia.edu/tag/0BEN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] twistedSheaf_isCoherent isCoherent_pushforward_of_isClosedImmersion
  Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent

/-! ### Krull dimension of subspaces -/

/-- A subset of a space is homeomorphic to its preimage in any larger subspace. -/
def subsetInclusionHomeomorph {T : Type*} [TopologicalSpace T] {A B : Set T}
    (hAB : A ⊆ B) : A ≃ₜ ((Subtype.val : B → T) ⁻¹' A) where
  toFun x := ⟨⟨x.1, hAB x.2⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The Krull dimension of an irreducible closed subset is its height in the lattice of
irreducible closed subsets. -/
theorem topologicalKrullDim_irreducibleCloseds {T : Type*} [TopologicalSpace T]
    (Z : IrreducibleCloseds T) :
    topologicalKrullDim (Z : Set T) = (Order.height Z : WithBot ℕ∞) := by
  rw [Order.height_eq_krullDim_Iic]
  apply le_antisymm
  · let e : IrreducibleCloseds (Z : Set T) ↪o Set.Iic Z :=
      OrderEmbedding.ofMapLEIff
        (fun W ↦ ⟨⟨Subtype.val '' (W : Set (Z : Set T)),
          W.isIrreducible.image _ continuous_subtype_val.continuousOn,
          Z.isClosed.isClosedEmbedding_subtypeVal.isClosedMap _ W.isClosed⟩,
          by rintro _ ⟨x, _, rfl⟩; exact x.2⟩)
        (fun A B ↦ Set.image_subset_image_iff Subtype.val_injective)
    exact Order.krullDim_le_of_strictMono e e.strictMono
  · let e : Set.Iic Z ↪o IrreducibleCloseds (Z : Set T) :=
      OrderEmbedding.ofMapLEIff
        (fun W ↦ ⟨Subtype.val ⁻¹' (W.1 : Set T),
          isIrreducible_preimage_subtypeVal W.1.isIrreducible W.2,
          W.1.isClosed.preimage continuous_subtype_val⟩)
        (fun A B ↦ ⟨fun h x hx ↦ h (show (⟨x, A.2 hx⟩ : (Z : Set T)) ∈ _ from hx),
          fun h _ hx ↦ h hx⟩)
    exact Order.krullDim_le_of_strictMono e e.strictMono

/-- A proper closed subset of an irreducible space of finite Krull dimension has strictly
smaller Krull dimension. -/
theorem topologicalKrullDim_lt_of_isClosed_ne_univ {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] {A : Set T} (hA : IsClosed A) (hne : A ≠ Set.univ)
    (hfin : topologicalKrullDim T < ⊤) :
    topologicalKrullDim A < topologicalKrullDim T := by
  let topT : IrreducibleCloseds T :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ T, isClosed_univ⟩
  let : Nonempty (IrreducibleCloseds T) := ⟨topT⟩
  let : FiniteDimensionalOrder (IrreducibleCloseds T) :=
    Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mpr
      ⟨Order.krullDim_ne_bot_iff.mpr inferInstance, ne_of_lt hfin⟩
  show Order.krullDim (IrreducibleCloseds A) < Order.krullDim (IrreducibleCloseds T)
  rw [Order.krullDim_eq_length_of_finiteDimensionalOrder (α := IrreducibleCloseds T)]
  refine Order.krullDim_lt_coe_iff.mpr fun l ↦ ?_
  let e : IrreducibleCloseds A ↪o IrreducibleCloseds T :=
    OrderEmbedding.ofMapLEIff
      (fun W ↦ ⟨Subtype.val '' (W : Set A),
        W.isIrreducible.image _ continuous_subtype_val.continuousOn,
        hA.isClosedEmbedding_subtypeVal.isClosedMap _ W.isClosed⟩)
      (fun W V ↦ Set.image_subset_image_iff Subtype.val_injective)
  have hlt : (l.map e e.strictMono).last < topT := by
    refine lt_of_le_not_ge (Set.subset_univ _) fun h ↦ hne ?_
    refine Set.eq_univ_of_univ_subset fun x hx ↦ ?_
    obtain ⟨y, _, rfl⟩ := h hx
    exact y.2
  exact Nat.lt_of_succ_le (LTSeries.longestOf_is_longest ((l.map e e.strictMono).snoc topT hlt))

/-- An irreducible closed subset of finite Krull dimension equal to the Krull dimension of the
ambient space is an irreducible component. -/
theorem mem_irreducibleComponents_of_topologicalKrullDim_eq {T : Type*}
    [TopologicalSpace T] {A : Set T} (hirr : IsIrreducible A) (hcl : IsClosed A)
    (hfin : topologicalKrullDim A < ⊤) (hdim : topologicalKrullDim A = topologicalKrullDim T) :
    A ∈ irreducibleComponents T := by
  let Z : IrreducibleCloseds T := ⟨A, hirr, hcl⟩
  have hZA : topologicalKrullDim A = (Order.height Z : WithBot ℕ∞) :=
    topologicalKrullDim_irreducibleCloseds Z
  rw [irreducibleComponents_eq_maximals_closed]
  refine ⟨⟨hcl, hirr⟩, fun W hW hZW ↦ ?_⟩
  by_contra hWZ
  let W' : IrreducibleCloseds T := ⟨W, hW.2, hW.1⟩
  have hfin' : Order.height Z < ⊤ := WithBot.coe_lt_coe.mp (hZA ▸ hfin)
  have hlt' : (Order.height Z : WithBot ℕ∞) < Order.height W' :=
    WithBot.coe_lt_coe.mpr
      (Order.height_strictMono (show Z < W' from lt_of_le_not_ge hZW hWZ) hfin')
  rw [← hZA, hdim] at hlt'
  exact (not_lt_of_ge (Order.height_le_krullDim W')) hlt'

/-- An empty space has Krull dimension `⊥`. -/
private theorem topologicalKrullDim_eq_bot_of_isEmpty {T : Type*} [TopologicalSpace T]
    {A : Set T} (hA : A = ∅) : topologicalKrullDim A = ⊥ := by
  let : IsEmpty (IrreducibleCloseds A) :=
    ⟨fun Z ↦ by obtain ⟨x, _⟩ := Z.isIrreducible.nonempty; exact (hA ▸ x.2 : (x : T) ∈ (∅ : Set T))⟩
  exact Order.krullDim_eq_bot

/-! ### Closed subschemes and their generic points -/

/-- The support of a closed subscheme and the closed subscheme itself have the same Krull
dimension. -/
theorem topologicalKrullDim_support_eq {X : Scheme.{u}} (I : X.IdealSheafData) :
    topologicalKrullDim (I.support : Set X) = topologicalKrullDim I.subscheme := by
  rw [← I.range_subschemeι]
  exact (I.subschemeι.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq _).symm

/-- The range of a closed immersion and its source have the same Krull dimension. -/
theorem topologicalKrullDim_range_eq {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] : topologicalKrullDim (Set.range i.base) = topologicalKrullDim Y :=
  (i.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq _).symm

/-! ### Supports and multiplicities along a short exact sequence -/

/-- The stalks of a short exact sequence of modules form a short exact sequence of modules over
the stalk of the structure sheaf. -/
private theorem exists_stalk_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (x : X) :
    ∃ (α : S.X₁.presheaf.stalk x →ₗ[X.presheaf.stalk x] S.X₂.presheaf.stalk x)
      (β : S.X₂.presheaf.stalk x →ₗ[X.presheaf.stalk x] S.X₃.presheaf.stalk x),
      Function.Injective α ∧ Function.Exact α β ∧ Function.Surjective β :=
  Stacks.SheafOfModules.FlatShortExact.stalkShortExact S hS x

/-- The support of the middle term of a short exact sequence of modules is the union of the
supports of the two outer terms. -/
private theorem supp_eq_union_of_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) :
    _root_.SheafOfModules.supp S.X₂ =
      _root_.SheafOfModules.supp S.X₁ ∪ _root_.SheafOfModules.supp S.X₃ := by
  ext x
  obtain ⟨α, β, hinj, hex, hsurj⟩ := exists_stalk_shortExact hS x
  refine ⟨fun h₂ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨a, ha⟩ := h₂
    by_cases hβ : β a = 0
    · obtain ⟨b, hb⟩ := (hex a).mp hβ
      exact Or.inl ⟨b, fun hb0 ↦ ha (by rw [← hb, hb0]; exact map_zero α)⟩
    · exact Or.inr ⟨β a, hβ⟩
  · rcases h with ⟨a, ha⟩ | ⟨c, hc⟩
    · exact ⟨α a, fun h0 ↦ ha (hinj (h0.trans (map_zero α).symm))⟩
    · obtain ⟨a, rfl⟩ := hsurj c
      exact ⟨a, fun h0 ↦ hc (by rw [h0]; exact map_zero β)⟩

/-- If the middle term of a short exact sequence of modules is supported inside a set, so are the
two outer terms. -/
private theorem supp_subset_of_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) {T : Set X} (h : _root_.SheafOfModules.supp S.X₂ ⊆ T) :
    _root_.SheafOfModules.supp S.X₁ ⊆ T ∧ _root_.SheafOfModules.supp S.X₃ ⊆ T := by
  rw [supp_eq_union_of_shortExact hS] at h
  exact Set.union_subset_iff.mp h

/-- At a point where the two outer stalks have finite length, the multiplicity of the middle
term of a short exact sequence is the sum of the multiplicities of the outer terms. -/
private theorem sheafMultiplicity_add_of_shortExact {X : Scheme.{u}}
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (x : X)
    (h₁ : IsFiniteLength (X.presheaf.stalk x) (S.X₁.presheaf.stalk x))
    (h₃ : IsFiniteLength (X.presheaf.stalk x) (S.X₃.presheaf.stalk x)) :
    Stacks.Chow.sheafMultiplicity S.X₂ x =
      Stacks.Chow.sheafMultiplicity S.X₁ x + Stacks.Chow.sheafMultiplicity S.X₃ x := by
  obtain ⟨α, β, hinj, hex, hsurj⟩ := exists_stalk_shortExact hS x
  simp only [Stacks.Chow.sheafMultiplicity]
  rw [Module.length_eq_add_of_exact α β hinj hsurj hex,
    ENat.toNat_add (Module.length_ne_top_iff.mpr h₁) (Module.length_ne_top_iff.mpr h₃)]
  push_cast
  rfl

/-- A point outside the support of a module has multiplicity zero there, so a module with no
support has multiplicity zero everywhere. -/
private theorem sheafMultiplicity_eq_zero_of_isZero {X : Scheme.{u}} (G : X.Modules)
    (hG : IsZero G) (x : X) : Stacks.Chow.sheafMultiplicity G x = 0 :=
  Stacks.Chow.sheafMultiplicity_eq_zero_of_notMem_supp G
    (by rw [Stacks.AlgebraicGeometry.ConfinedDevissage.supp_eq_empty_of_isZero G hG]; exact id)

/-! ### Degree bounds for sums of polynomials -/

/-- The cast of the natural numbers into `WithBot ℕ∞` is monotone. -/
private theorem natCast_le_natCast_withBot {m n : ℕ} (h : m ≤ n) :
    ((m : ℕ) : WithBot ℕ∞) ≤ ((n : ℕ) : WithBot ℕ∞) :=
  WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr h)

/-- A finite sum of polynomials, each either zero or of total degree below a bound, is either
zero or of total degree below that bound. -/
private theorem mvPolynomial_sum_totalDegree_lt {α : Type*} (s : Finset α) {r : ℕ}
    {d : WithBot ℕ∞} (P : α → MvPolynomial (Fin r) ℚ)
    (hP : ∀ a ∈ s, P a = 0 ∨ ((P a).totalDegree : WithBot ℕ∞) < d) :
    s.sum P = 0 ∨ ((s.sum P).totalDegree : WithBot ℕ∞) < d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    rcases hP a (Finset.mem_insert_self a s) with hzero | hdeg
    · simpa [hzero] using ih fun b hb ↦ hP b (Finset.mem_insert_of_mem hb)
    · rcases ih (fun b hb ↦ hP b (Finset.mem_insert_of_mem hb)) with hsz | hsd
      · exact Or.inr (by simpa [hsz] using hdeg)
      · refine Or.inr ?_
        have h := MvPolynomial.totalDegree_add (P a) (s.sum P)
        rcases le_total (P a).totalDegree (s.sum P).totalDegree with hle | hle
        · exact lt_of_le_of_lt
            (natCast_le_natCast_withBot (h.trans (max_le hle le_rfl))) hsd
        · exact lt_of_le_of_lt
            (natCast_le_natCast_withBot (h.trans (max_le le_rfl hle))) hdeg

/-- A sum of two polynomials, each either zero or of total degree below a bound, is either zero
or of total degree below that bound. -/
private theorem mvPolynomial_add_totalDegree_lt {r : ℕ} {d : WithBot ℕ∞}
    {P Q : MvPolynomial (Fin r) ℚ} (hP : P = 0 ∨ ((P.totalDegree : ℕ) : WithBot ℕ∞) < d)
    (hQ : Q = 0 ∨ ((Q.totalDegree : ℕ) : WithBot ℕ∞) < d) :
    P + Q = 0 ∨ (((P + Q).totalDegree : ℕ) : WithBot ℕ∞) < d := by
  classical
  simpa using mvPolynomial_sum_totalDegree_lt (Finset.univ : Finset Bool)
    (fun b ↦ if b then P else Q) (by intro b _; cases b <;> simpa)

/-! ### Top-dimensional integral closed subschemes of a support -/

/-- The integral closed subschemes of `X` contained in the support of a module `ℱ` and of the
same dimension as it: the top-dimensional irreducible components of `Supp ℱ`, carrying their
reduced induced closed-subscheme structures. -/
abbrev TopDimIntegralSubscheme {X : Scheme.{u}} (F : X.Modules) : Type u :=
  {Z : X.IdealSheafData // IsIntegral Z.subscheme ∧
    (Z.support : Set X) ⊆ _root_.SheafOfModules.supp F ∧
    topologicalKrullDim Z.subscheme = topologicalKrullDim (_root_.SheafOfModules.supp F)}

namespace TopDimIntegralSubscheme

variable {X : Scheme.{u}} {F : X.Modules}

/-- The generic point of a top-dimensional integral component of `Supp ℱ`, read as a point of
the ambient scheme. -/
def genericPt (Z : TopDimIntegralSubscheme F) : X :=
  have := Z.2.1
  Z.1.subschemeι (genericPoint Z.1.subscheme)

/-- The generic point of a top-dimensional integral component of `Supp ℱ` is a generic point of
the support of that component. -/
private theorem isGenericPoint_genericPt (Z : TopDimIntegralSubscheme F) :
    IsGenericPoint Z.genericPt (Z.1.support : Set X) :=
  have := Z.2.1
  Stacks.AlgebraicGeometry.CoherentDevissageGlue.isGenericPoint_subschemeι_genericPoint Z.1

/-- If the generic point of a top-dimensional integral component lies in the support of a
coherent module, the whole component does. -/
private theorem support_subset_supp_of_genericPt_mem (Z : TopDimIntegralSubscheme F)
    (G : X.Modules) [G.IsCoherent] (h : Z.genericPt ∈ _root_.SheafOfModules.supp G) :
    (Z.1.support : Set X) ⊆ _root_.SheafOfModules.supp G :=
  have := Stacks.Chow.isFiniteType_of_isCoherent G
  ((isGenericPoint_genericPt Z).mem_closed_set_iff (_root_.SheafOfModules.isClosed_supp G)).mp h

/-- A top-dimensional integral component of `Supp ℱ` is determined by its underlying closed
set: the component is reduced, so it is the vanishing ideal of that set. -/
theorem val_injective (F : X.Modules) :
    Function.Injective fun Z : TopDimIntegralSubscheme F ↦ (Z.1.support : Set X) := by
  intro Z W h
  refine Subtype.ext ?_
  have := Z.2.1
  have := W.2.1
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme Z.1 Z.1.support rfl,
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme W.1 W.1.support rfl]
  exact congrArg Scheme.IdealSheafData.vanishingIdeal (Closeds.ext h)

/-- Two top-dimensional integral components of `Supp ℱ` with the same preimage in `Supp ℱ` are
equal. -/
private theorem eq_of_preimage_support_eq {Z W : TopDimIntegralSubscheme F}
    (h : (Subtype.val : _root_.SheafOfModules.supp F → X) ⁻¹' (Z.1.support : Set X) =
      Subtype.val ⁻¹' (W.1.support : Set X)) : Z = W := by
  refine val_injective F ?_
  ext x
  exact ⟨fun hx ↦ (Set.ext_iff.mp h ⟨x, Z.2.2.1 hx⟩).mp hx,
    fun hx ↦ (Set.ext_iff.mp h ⟨x, W.2.2.1 hx⟩).mpr hx⟩

end TopDimIntegralSubscheme

/-- The Euler characteristic of the twist of the structure sheaf of a top-dimensional integral
component `Z` of `Supp ℱ` by the restrictions to `Z` of the invertible modules `𝓛_i`. -/
def componentTwistEulerCharacteristic (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] {F : X.Modules} {r : ℕ} (L : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]
    (Z : TopDimIntegralSubscheme F) (n : Fin r → ℤ) : ℤ :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian Z.1.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion Z.1.subschemeι
  have : ∀ i, SheafOfModules.IsInvertible Z.1.subscheme.presheaf Z.1.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback Z.1.subschemeι).obj (L i)) :=
    fun i ↦ SheafOfModules.isInvertible_pullback Z.1.subschemeι (L i)
  eulerCharacteristic k (Z.1.subschemeι ≫ f)
    (twistedSheaf (Stacks.Ample.unitModule Z.1.subscheme)
      (fun i ↦ (Scheme.Modules.pullback Z.1.subschemeι).obj (L i)) n)

/-! ### The polynomial of [Stacks, Tag 0BEM] as a function of the module -/

section EulerPolynomial

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] {r : ℕ}
  (L : Fin r → X.Modules) [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]

/-- The polynomial of [Stacks, Tag 0BEM] attached to a coherent module: its value at an integer
vector `n` is the Euler characteristic of the `n`-th twist of that module. -/
@[ega "III 2.5.3" "(i), special case", sga "6 X 2.3.1"]
private def eulerPolynomial (G : X.Modules) [G.IsCoherent] : MvPolynomial (Fin r) ℚ :=
  (exists_eulerPolynomial_twistedSheaf_of_isProper k f L G inferInstance).choose

/-- The defining properties of `AlgebraicGeometry.eulerPolynomial`: its total degree is at most
the dimension of the support, and its values are the Euler characteristics of the twists. -/
private theorem eulerPolynomial_spec (G : X.Modules) [G.IsCoherent] :
    (eulerPolynomial k f L G = 0 ∨
        ((eulerPolynomial k f L G).totalDegree : WithBot ℕ∞) ≤
          topologicalKrullDim (_root_.SheafOfModules.supp G)) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j ↦ (n j : ℚ)) (eulerPolynomial k f L G) =
        (eulerCharacteristic k f (twistedSheaf G L n) : ℚ) :=
  (exists_eulerPolynomial_twistedSheaf_of_isProper k f L G inferInstance).choose_spec

/-- The value of the polynomial of [Stacks, Tag 0BEM] at an integer vector is the Euler
characteristic of the corresponding twist. -/
@[ega "III 2.5.3" "(i), special case", ega "III 7.9.11" "special case"]
private theorem eulerPolynomial_eval (G : X.Modules) [G.IsCoherent] (n : Fin r → ℤ) :
    MvPolynomial.eval (fun j ↦ (n j : ℚ)) (eulerPolynomial k f L G) =
      (eulerCharacteristic k f (twistedSheaf G L n) : ℚ) :=
  (eulerPolynomial_spec k f L G).2 n

/-- The polynomial of [Stacks, Tag 0BEM] is the only polynomial taking the Euler
characteristics of the twists as its values at integer vectors. -/
@[ega "III 2.5.3" "(i), special case"]
private theorem eq_eulerPolynomial (G : X.Modules) [G.IsCoherent] (P : MvPolynomial (Fin r) ℚ)
    (h : ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j ↦ (n j : ℚ)) P =
      (eulerCharacteristic k f (twistedSheaf G L n) : ℚ)) :
    P = eulerPolynomial k f L G :=
  MvPolynomial.eq_of_eval_intCast fun n ↦ (h n).trans (eulerPolynomial_eval k f L G n).symm

/-- The total degree of the polynomial of [Stacks, Tag 0BEM] is below any bound that strictly
exceeds the dimension of the support. -/
private theorem eulerPolynomial_totalDegree_lt (G : X.Modules) [G.IsCoherent] {d : WithBot ℕ∞}
    (hd : topologicalKrullDim (_root_.SheafOfModules.supp G) < d) :
    eulerPolynomial k f L G = 0 ∨
      ((eulerPolynomial k f L G).totalDegree : WithBot ℕ∞) < d :=
  (eulerPolynomial_spec k f L G).1.imp id fun h ↦ lt_of_le_of_lt h hd

/-- The polynomial of [Stacks, Tag 0BEM] is additive along a short exact sequence of coherent
modules. -/
private theorem eulerPolynomial_add_of_shortExact {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent] :
    eulerPolynomial k f L S.X₂ = eulerPolynomial k f L S.X₁ + eulerPolynomial k f L S.X₃ := by
  refine (eq_eulerPolynomial k f L S.X₂ _ fun n ↦ ?_).symm
  have h := eulerCharacteristic_twistedSheaf_add_of_shortExact k f L
    (forall_finiteDimensional_cohomologyOverField_of_isProper k f) hS inferInstance inferInstance
    inferInstance n
  rw [MvPolynomial.eval_add, eulerPolynomial_eval, eulerPolynomial_eval]
  exact_mod_cast congrArg (fun m : ℤ ↦ (m : ℚ)) h.symm

/-- Isomorphic coherent modules have the same polynomial of [Stacks, Tag 0BEM]. -/
private theorem eulerPolynomial_eq_of_iso {G H : X.Modules} [G.IsCoherent] [H.IsCoherent]
    (e : G ≅ H) : eulerPolynomial k f L G = eulerPolynomial k f L H := by
  refine eq_eulerPolynomial k f L H _ fun n ↦ ?_
  rw [eulerPolynomial_eval]
  exact_mod_cast congrArg (fun m : ℤ ↦ (m : ℚ))
    (eulerCharacteristic_twistedSheaf_eq_of_iso k f L inferInstance inferInstance e n)

/-- The polynomial of [Stacks, Tag 0BEM] of a zero module vanishes: the support is empty, so no
nonzero polynomial can satisfy the degree bound. -/
private theorem eulerPolynomial_eq_zero_of_isZero (G : X.Modules) [G.IsCoherent]
    (hG : IsZero G) : eulerPolynomial k f L G = 0 := by
  rcases (eulerPolynomial_spec k f L G).1 with h | h
  · exact h
  · rw [topologicalKrullDim_eq_bot_of_isEmpty
      (Stacks.AlgebraicGeometry.ConfinedDevissage.supp_eq_empty_of_isZero G hG)] at h
    exact absurd (le_bot_iff.mp h) (WithBot.coe_ne_bot)

end EulerPolynomial

/-! ### Top-dimensional components are irreducible components, and there are finitely many -/

/-- An integral closed subscheme of a scheme locally of finite type over a field has finite
Krull dimension. -/
theorem topologicalKrullDim_lt_top_of_isIntegral (k : Type u) [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (i : Y ⟶ X)
    [IsClosedImmersion i] [IsIntegral Y] : topologicalKrullDim Y < ⊤ := by
  have : JacobsonSpace (Stacks.Chow.fieldChowSituation k).S :=
    inferInstanceAs (JacobsonSpace (Spec (.of k)))
  rw [Stacks.Chow.topologicalKrullDim_eq_relativeDimension_toNat
    (Stacks.Chow.fieldChowSituation k) (fun s _ ↦ rfl) f i (genericPoint Y)
    (genericPoint_spec Y)]
  exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _)

/-- The preimage in a subset `S` of the support of a top-dimensional integral component is an
irreducible component of `S`, provided `S` has no larger dimension than the component. -/
private theorem preimage_support_mem_irreducibleComponents (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {F : X.Modules}
    (Z : TopDimIntegralSubscheme F) {S : Set X} (hZS : (Z.1.support : Set X) ⊆ S)
    (hS : topologicalKrullDim S ≤ topologicalKrullDim Z.1.subscheme) :
    (Subtype.val : S → X) ⁻¹' (Z.1.support : Set X) ∈ irreducibleComponents S := by
  have := Z.2.1
  have hdim : topologicalKrullDim ((Subtype.val : S → X) ⁻¹' (Z.1.support : Set X)) =
      topologicalKrullDim Z.1.subscheme := by
    rw [← topologicalKrullDim_support_eq]
    exact ((subsetInclusionHomeomorph hZS).isHomeomorph.topologicalKrullDim_eq _).symm
  refine mem_irreducibleComponents_of_topologicalKrullDim_eq
    (isIrreducible_preimage_subtypeVal
      (TopDimIntegralSubscheme.isGenericPoint_genericPt Z).isIrreducible hZS)
    (Z.1.support.isClosed.preimage continuous_subtype_val) ?_
    (le_antisymm (topologicalKrullDim_subspace_le _ _) (hS.trans_eq hdim.symm))
  rw [hdim]
  exact topologicalKrullDim_lt_top_of_isIntegral k f Z.1.subschemeι

/-- The preimage in `Supp ℱ` of a top-dimensional integral component is an irreducible
component of `Supp ℱ`: it is irreducible and closed of the full dimension. -/
theorem mem_irreducibleComponents_preimage_support (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (F : X.Modules)
    (Z : TopDimIntegralSubscheme F) :
    (Subtype.val : _root_.SheafOfModules.supp F → X) ⁻¹' (Z.1.support : Set X) ∈
      irreducibleComponents (_root_.SheafOfModules.supp F) :=
  preimage_support_mem_irreducibleComponents k f Z Z.2.2.1 Z.2.2.2.ge

/-- A coherent module on a Noetherian scheme over a field has only finitely many
top-dimensional integral components of its support. -/
theorem finite_topDimIntegralSubscheme (k : Type u) [Field k] {X : Scheme.{u}}
    [NoetherianSpace X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (F : X.Modules) :
    Finite (TopDimIntegralSubscheme F) := by
  have : Finite (irreducibleComponents (_root_.SheafOfModules.supp F)) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  exact Finite.of_injective
    (fun Z : TopDimIntegralSubscheme F ↦
      (⟨_, mem_irreducibleComponents_preimage_support k f F Z⟩ :
        irreducibleComponents (_root_.SheafOfModules.supp F)))
    fun Z W h ↦ TopDimIntegralSubscheme.eq_of_preimage_support_eq (congrArg Subtype.val h)

/-- Two top-dimensional integral components of `Supp ℱ` sharing a point that is generic for the
first are equal: both are irreducible components of `Supp ℱ`, hence maximal. -/
private theorem topDimIntegralSubscheme_eq_of_genericPt_mem (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (F : X.Modules)
    (Z W : TopDimIntegralSubscheme F) (h : Z.genericPt ∈ (W.1.support : Set X)) : Z = W := by
  have hZW : (Z.1.support : Set X) ⊆ (W.1.support : Set X) :=
    ((TopDimIntegralSubscheme.isGenericPoint_genericPt Z).mem_closed_set_iff
      W.1.support.isClosed).mp h
  have hZ := mem_irreducibleComponents_preimage_support k f F Z
  have hW := mem_irreducibleComponents_preimage_support k f F W
  have heq := Set.Subset.antisymm (Set.preimage_mono hZW)
    (hZ.2 hW.1 (Set.preimage_mono hZW))
  exact TopDimIntegralSubscheme.eq_of_preimage_support_eq heq

/-- At the generic point of a top-dimensional integral component of `Supp ℱ`, the stalk of any
coherent module supported inside `Supp ℱ` has finite length. -/
@[ega "IV 4.7.7" "special case"]
private theorem isFiniteLength_stalk_genericPt (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] {F : X.Modules} (Z : TopDimIntegralSubscheme F)
    (G : X.Modules) [G.IsCoherent]
    (hGF : _root_.SheafOfModules.supp G ⊆ _root_.SheafOfModules.supp F) :
    IsFiniteLength (X.presheaf.stalk Z.genericPt) (G.presheaf.stalk Z.genericPt) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := Stacks.Chow.isFiniteType_of_isCoherent G
  by_cases hx : Z.genericPt ∈ _root_.SheafOfModules.supp G
  · have hZG := TopDimIntegralSubscheme.support_subset_supp_of_genericPt_mem Z G hx
    have himg : (Subtype.val : _root_.SheafOfModules.supp G → X) ''
        (Subtype.val ⁻¹' (Z.1.support : Set X)) = (Z.1.support : Set X) := by
      rw [Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype]
      exact Set.inter_eq_left.mpr hZG
    have hC := preimage_support_mem_irreducibleComponents k f Z hZG
      ((topologicalKrullDim_le_of_subset hGF).trans Z.2.2.2.ge)
    refine Stacks.Chow.isFiniteLength_stalk_of_isGenericPoint_component_supp G ⟨_, hC⟩
      Z.genericPt ?_
    rw [himg]
    exact TopDimIntegralSubscheme.isGenericPoint_genericPt Z
  · have : Subsingleton (G.presheaf.stalk Z.genericPt) :=
      not_nontrivial_iff_subsingleton.mp fun hn ↦
        hx ((_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk G Z.genericPt).mpr hn)
    exact IsFiniteLength.of_subsingleton

/-- A coherent module supported in dimension smaller than `Supp ℱ` contributes no multiplicity
at the generic point of a top-dimensional component of `Supp ℱ`. -/
private theorem sheafMultiplicity_genericPt_eq_zero {X : Scheme.{u}} {F : X.Modules}
    (G : X.Modules) [G.IsCoherent] (Z : TopDimIntegralSubscheme F)
    (hd : topologicalKrullDim (_root_.SheafOfModules.supp G) <
      topologicalKrullDim (_root_.SheafOfModules.supp F)) :
    Stacks.Chow.sheafMultiplicity G Z.genericPt = 0 := by
  refine Stacks.Chow.sheafMultiplicity_eq_zero_of_notMem_supp G fun hmem ↦ ?_
  have := Stacks.Chow.isFiniteType_of_isCoherent G
  have hle := topologicalKrullDim_le_of_subset
    (TopDimIntegralSubscheme.support_subset_supp_of_genericPt_mem Z G hmem)
  rw [topologicalKrullDim_support_eq, Z.2.2.2] at hle
  exact absurd hd (not_lt_of_ge hle)

/-! ### Nonzero submodules of the structure sheaf of an integral scheme -/

/-- An injective map into a module isomorphic to the base field, out of a nonzero module, is
surjective: its image is a nonzero submodule of a one-dimensional space. -/
private theorem range_eq_top_of_injective_of_isField {R M N : Type*} [CommRing R]
    (hR : IsField R) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : N ≃ₗ[R] R) (α : M →ₗ[R] N) (hinj : Function.Injective α) [Nontrivial M] :
    LinearMap.range α = ⊤ := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have hαm : e (α m) ≠ 0 := fun h ↦ hm
    (hinj ((e.injective (h.trans (map_zero e).symm)).trans (map_zero α).symm))
  obtain ⟨b, hb⟩ := hR.mul_inv_cancel hαm
  refine LinearMap.range_eq_top.mpr fun y ↦ ⟨(b * e y) • m, e.injective ?_⟩
  rw [map_smul, map_smul, smul_eq_mul]
  calc (b * e y) * e (α m) = e y * (e (α m) * b) := by ring
    _ = e y := by rw [hb, mul_one]

/-- The cokernel sequence of a monomorphism of modules on a scheme is short exact. -/
private theorem shortExact_cokernelSequence {Y : Scheme.{u}} {A B : Y.Modules} (φ : A ⟶ B)
    (hφ : Mono φ) : (ShortComplex.cokernelSequence φ).ShortExact :=
  have := hφ
  { exact := ShortComplex.cokernelSequence_exact φ
    mono_f := by dsimp [ShortComplex.cokernelSequence]; infer_instance
    epi_g := by dsimp [ShortComplex.cokernelSequence]; infer_instance }

/-- The direct image along a closed immersion of a cokernel sequence is short exact: the direct
image is exact. -/
private theorem shortExact_map_pushforward_cokernelSequence {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] {A B : Y.Modules} (φ : A ⟶ B) (hφ : Mono φ) :
    ((ShortComplex.cokernelSequence φ).map (Scheme.Modules.pushforward i)).ShortExact :=
  have := Stacks.SchemeCohomology.pushforward_preservesFiniteLimits i
  (shortExact_cokernelSequence φ hφ).map_of_exact (Scheme.Modules.pushforward i)

/-- **The direct image along a closed immersion of a cokernel sequence is short exact.** This is
`shortExact_map_pushforward_cokernelSequence` above, made available to other modules: the
Noetherian induction of [Stacks, Tag 01YF] in
`StacksFrontier.AlgebraicGeometry.CoherentDevissage.StructureSheafCriterion` descends its property
along exactly this sequence, from outside this file. -/
public alias shortExact_map_pushforward_cokernelSequence_of_mono := shortExact_map_pushforward_cokernelSequence

/-- On an integral scheme the quotient of the structure sheaf by a submodule whose stalk at the
generic point is nonzero vanishes at the generic point: that stalk is a nonzero submodule of a
field. -/
private theorem notMem_supp_cokernel_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    {A : Y.Modules} (φ : A ⟶ Stacks.Ample.unitModule Y) (hφ : Mono φ)
    (hA : genericPoint Y ∈ _root_.SheafOfModules.supp A) :
    genericPoint Y ∉ _root_.SheafOfModules.supp (cokernel φ) := by
  have := hφ
  let S := ShortComplex.cokernelSequence φ
  have hS : S.ShortExact := shortExact_cokernelSequence φ hφ
  obtain ⟨α, β, hinj, hex, hsurj⟩ := exists_stalk_shortExact hS (genericPoint Y)
  have hR : IsField (Y.presheaf.stalk (genericPoint Y)) :=
    let : Field (Y.presheaf.stalk (genericPoint Y)) := inferInstanceAs (Field Y.functionField)
    Field.toIsField _
  obtain ⟨a, ha⟩ := hA
  have : Nontrivial (S.X₁.presheaf.stalk (genericPoint Y)) := nontrivial_of_ne a 0 ha
  have htop : LinearMap.range α = ⊤ :=
    range_eq_top_of_injective_of_isField hR
      (Stacks.Ample.unitStalkEquiv Y (genericPoint Y)) α hinj
  rintro ⟨c, hc⟩
  obtain ⟨m, rfl⟩ := hsurj c
  exact hc ((hex m).mpr (LinearMap.mem_range.mp (htop.ge Submodule.mem_top)))

/-- **On an integral scheme the quotient of the structure sheaf by a submodule whose stalk at
the generic point is nonzero vanishes at the generic point.** This is
`notMem_supp_cokernel_genericPoint` above, made available to other modules: the Noetherian
induction of [Stacks, Tag 01YF] in
`StacksFrontier.AlgebraicGeometry.CoherentDevissage.StructureSheafCriterion` needs the quotient
term of the cokernel sequence to have strictly smaller support, and reads that from outside this
file. -/
public alias notMem_supp_cokernel_genericPoint_of_mono := notMem_supp_cokernel_genericPoint

/-- On an integral scheme locally of finite type over a field, the quotient of the structure
sheaf by a coherent submodule of full support is supported in strictly smaller dimension. -/
private theorem topologicalKrullDim_supp_cokernel_lt (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (i : Y ⟶ X) [IsClosedImmersion i]
    [IsIntegral Y] [IsLocallyNoetherian Y] {A : Y.Modules} [A.IsCoherent]
    (φ : A ⟶ Stacks.Ample.unitModule Y) (hφ : Mono φ)
    (hA : _root_.SheafOfModules.supp A = Set.univ) :
    topologicalKrullDim (_root_.SheafOfModules.supp (cokernel φ)) < topologicalKrullDim Y := by
  have : IrreducibleSpace Y := irreducibleSpace_of_isIntegral Y
  refine topologicalKrullDim_lt_of_isClosed_ne_univ
    (Stacks.AlgebraicGeometry.DevissageNoetherian.isClosed_supp_of_isCoherent (cokernel φ)
      (_root_.SheafOfModules.cokernel_isCoherent φ)) (fun h ↦ ?_)
    (topologicalKrullDim_lt_top_of_isIntegral k f i)
  exact notMem_supp_cokernel_genericPoint φ hφ (hA.symm.subset (Set.mem_univ _))
    (h.symm.subset (Set.mem_univ _))

/-! ### The image of a closed immersion as a component of the support -/

/-- The underlying closed set of the kernel ideal of a closed immersion is its range. -/
private theorem ker_support_eq_range {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] :
    (i.ker.support : Set X) = Set.range i.base := by
  rw [Scheme.Hom.support_ker]
  exact i.isClosedEmbedding.isClosed_range.closure_eq

/-- The image of the generic point of an integral scheme under a closed immersion is a generic
point of the range. -/
private theorem isGenericPoint_range {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
    [IsIntegral Y] : IsGenericPoint (i (genericPoint Y)) (Set.range i.base) := by
  simpa only [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] using
    (genericPoint_spec Y).image i.continuous

/-- A closed immersion of an integral scheme whose range is a top-dimensional subset of
`Supp ℱ` cuts out a top-dimensional integral component of `Supp ℱ`. -/
private def topDimIntegralSubschemeOfClosedImmersion {X Y : Scheme.{u}} (F : X.Modules)
    (i : Y ⟶ X) [IsClosedImmersion i] [IsIntegral Y]
    (hsup : Set.range i.base ⊆ _root_.SheafOfModules.supp F)
    (hdim : topologicalKrullDim Y = topologicalKrullDim (_root_.SheafOfModules.supp F)) :
    TopDimIntegralSubscheme F :=
  ⟨i.ker, IsIntegral.of_isIso i.toImage, by rwa [ker_support_eq_range i], by
    rw [← topologicalKrullDim_support_eq, ker_support_eq_range i, topologicalKrullDim_range_eq i]
    exact hdim⟩

/-- A morphism that is an isomorphism identifies the structure sheaf of its target with the
direct image of the structure sheaf of its source. -/
private theorem isIso_unitToPushforwardObjUnit {Y Z : Scheme.{u}} (e : Y ⟶ Z) [IsIso e] :
    IsIso (_root_.SheafOfModules.unitToPushforwardObjUnit e.toRingCatSheafHom) := by
  refine (Scheme.Modules.Hom.isIso_iff_isIso_app).2 fun V ↦ ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  show Function.Bijective (e.app V).hom
  exact (ConcreteCategory.isIso_iff_bijective (e.app V)).mp inferInstance

/-- The direct image of the structure sheaf along a closed immersion is the direct image of the
structure sheaf of its scheme-theoretic image. -/
private def pushforwardUnitIsoImage {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
    {I : X.IdealSheafData} (hI : I = i.ker) :
    (Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Y) ≅
      (Scheme.Modules.pushforward I.subschemeι).obj (Stacks.Ample.unitModule I.subscheme) := by
  subst hI
  have : IsIso (_root_.SheafOfModules.unitToPushforwardObjUnit i.toImage.toRingCatSheafHom) :=
    isIso_unitToPushforwardObjUnit i.toImage
  exact (Scheme.Modules.pushforwardCongr i.toImage_imageι).symm.app _ ≪≫
    (Scheme.Modules.pushforwardComp i.toImage i.ker.subschemeι).symm.app _ ≪≫
      (Scheme.Modules.pushforward i.ker.subschemeι).mapIso
        (asIso (_root_.SheafOfModules.unitToPushforwardObjUnit
          i.toImage.toRingCatSheafHom)).symm

/-- The direct image of the structure sheaf of an integral closed subscheme has multiplicity
one at the image of the generic point. -/
private theorem sheafMultiplicity_pushforward_unit_genericPoint {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] [IsIntegral Y] :
    Stacks.Chow.sheafMultiplicity
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Y))
        (i (genericPoint Y)) = 1 := by
  rw [Stacks.Chow.sheafMultiplicity_pushforwardStructureSheaf i
    ⟨genericPoint Y, Stacks.Chow.genericPoint_mem_genericPoints Y⟩]
  exact Stacks.Chow.componentMultiplicity_eq_one i (Stacks.Chow.genericPoint_mem_genericPoints Y)

/-! ### Dévissage along the filtration of [Stacks, Tag 01YF] -/

/-- Coherence of modules on a scheme is invariant under isomorphism. -/
private theorem isCoherent_of_iso {X : Scheme.{u}} {G H : X.Modules} [G.IsCoherent]
    (e : G ≅ H) : H.IsCoherent := by
  have := isWeakSerreClass_coherentModules X
  exact ObjectProperty.prop_of_iso (P := fun M : X.Modules ↦ M.IsCoherent) e inferInstance

/-- **Dévissage.** A property of modules on a Noetherian scheme that holds for zero modules, is
invariant under isomorphism, is stable under extensions of coherent modules, and holds for the
direct images of nonzero coherent sheaves of ideals on integral closed subschemes holds for
every coherent module. -/
private theorem of_integral_ideal_pushforwards {X : Scheme.{u}} [IsNoetherian X]
    (P : X.Modules → Prop) (hzero : ∀ G : X.Modules, IsZero G → P G)
    (hiso : ∀ {G H : X.Modules}, (G ≅ H) → P G → P H)
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact → S.X₁.IsCoherent → S.X₂.IsCoherent →
      S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ (Y : Scheme.{u}) (i : Y ⟶ X), IsClosedImmersion i → IsIntegral Y →
      ∀ I : (_root_.SheafOfModules.unit Y.ringCatSheaf).Submodule,
        I.toSheafOfModules.IsCoherent → ¬ IsZero I.toSheafOfModules →
        P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    (F : X.Modules) [F.IsCoherent] : P F := by
  obtain ⟨n, G, hG, hbot, htop, hcoh, hfac⟩ :=
    Stacks.AlgebraicGeometry.CoherentDevissage.exists_filtration_by_integral_ideal_pushforwards
      X F
  have hP : ∀ j : Fin (n + 1), P (G j : X.Modules) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      refine hzero _ ?_
      rw [hbot]
      exact IsZero.of_iso (isZero_zero _) Subobject.botCoeIsoZero
    | succ j ih =>
      have h₁ : (G j.castSucc : X.Modules).IsCoherent := hcoh j.castSucc
      have h₂ : (G j.succ : X.Modules).IsCoherent := hcoh j.succ
      refine hext _ (shortExact_cokernelSequence
          (Subobject.ofLE (G j.castSucc) (G j.succ) (hG j.castSucc_le_succ)) inferInstance)
        h₁ h₂ (_root_.SheafOfModules.cokernel_isCoherent _) ih ?_
      obtain ⟨Y, i, hi, hY, I, hI, hne, ⟨e⟩⟩ := hfac j
      exact hiso e.symm (hideal Y i hi hY I hI hne)
  have hlast := hP (Fin.last n)
  rw [htop] at hlast
  exact hiso (asIso (⊤ : Subobject F).arrow) hlast

/-! ### The correction polynomial -/

section Correction

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] {r : ℕ}
  (L : Fin r → X.Modules) [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]
  (F : X.Modules) [Fintype (TopDimIntegralSubscheme F)]
  (Q : TopDimIntegralSubscheme F → MvPolynomial (Fin r) ℚ)

/-- The polynomial of [Stacks, Tag 0BEM] of a coherent module minus the multiplicity-weighted
sum, over the top-dimensional integral components of `Supp ℱ`, of the polynomials `Q`. -/
private def correctionPolynomial (G : X.Modules) [G.IsCoherent] : MvPolynomial (Fin r) ℚ :=
  eulerPolynomial k f L G -
    ∑ Z : TopDimIntegralSubscheme F,
      MvPolynomial.C (Stacks.Chow.sheafMultiplicity G Z.genericPt : ℚ) * Q Z

/-- The correction polynomial is additive along a short exact sequence of coherent modules whose
middle term is supported inside `Supp ℱ`. -/
private theorem correctionPolynomial_add_of_shortExact {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent]
    (hSF : _root_.SheafOfModules.supp S.X₂ ⊆ _root_.SheafOfModules.supp F) :
    correctionPolynomial k f L F Q S.X₂ =
      correctionPolynomial k f L F Q S.X₁ + correctionPolynomial k f L F Q S.X₃ := by
  obtain ⟨h₁, h₃⟩ := supp_subset_of_shortExact hS hSF
  have hm : ∀ Z : TopDimIntegralSubscheme F,
      (Stacks.Chow.sheafMultiplicity S.X₂ Z.genericPt : ℚ) =
        (Stacks.Chow.sheafMultiplicity S.X₁ Z.genericPt : ℚ) +
          (Stacks.Chow.sheafMultiplicity S.X₃ Z.genericPt : ℚ) := fun Z ↦ by
    exact_mod_cast sheafMultiplicity_add_of_shortExact hS Z.genericPt
      (isFiniteLength_stalk_genericPt k f Z S.X₁ h₁)
      (isFiniteLength_stalk_genericPt k f Z S.X₃ h₃)
  unfold correctionPolynomial
  rw [eulerPolynomial_add_of_shortExact k f L hS]
  simp_rw [hm, map_add, add_mul, Finset.sum_add_distrib]
  ring

/-- Isomorphic coherent modules have the same correction polynomial. -/
private theorem correctionPolynomial_eq_of_iso {G H : X.Modules} [G.IsCoherent] [H.IsCoherent]
    (e : G ≅ H) : correctionPolynomial k f L F Q G = correctionPolynomial k f L F Q H := by
  have hm : ∀ Z : TopDimIntegralSubscheme F, Stacks.Chow.sheafMultiplicity G Z.genericPt =
      Stacks.Chow.sheafMultiplicity H Z.genericPt :=
    fun Z ↦ Stacks.Chow.sheafMultiplicity_eq_of_iso e _
  unfold correctionPolynomial
  rw [eulerPolynomial_eq_of_iso k f L e]
  simp_rw [hm]

/-- The correction polynomial of a zero module vanishes. -/
private theorem correctionPolynomial_eq_zero_of_isZero (G : X.Modules) [G.IsCoherent]
    (hG : IsZero G) : correctionPolynomial k f L F Q G = 0 := by
  unfold correctionPolynomial
  rw [eulerPolynomial_eq_zero_of_isZero k f L G hG]
  simp [sheafMultiplicity_eq_zero_of_isZero G hG]

/-- For a coherent module supported in dimension smaller than `Supp ℱ` the correction polynomial
is the polynomial of [Stacks, Tag 0BEM], hence has total degree below the dimension of
`Supp ℱ`. -/
private theorem correctionPolynomial_totalDegree_lt_of_supp_dim_lt (G : X.Modules)
    [G.IsCoherent]
    (hd : topologicalKrullDim (_root_.SheafOfModules.supp G) <
      topologicalKrullDim (_root_.SheafOfModules.supp F)) :
    correctionPolynomial k f L F Q G = 0 ∨
      ((correctionPolynomial k f L F Q G).totalDegree : WithBot ℕ∞) <
        topologicalKrullDim (_root_.SheafOfModules.supp F) := by
  have heq : correctionPolynomial k f L F Q G = eulerPolynomial k f L G := by
    unfold correctionPolynomial
    simp [fun Z ↦ sheafMultiplicity_genericPt_eq_zero (F := F) G Z hd]
  rw [heq]
  exact eulerPolynomial_totalDegree_lt k f L G hd

end Correction

/-! ### The polynomial of a top-dimensional component -/

/-- The polynomial of [Stacks, Tag 0BEM] for the structure sheaf of a top-dimensional integral
component of `Supp ℱ`, twisted by the restrictions of the invertible modules. -/
private def componentEulerPolynomial (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] {F : X.Modules} {r : ℕ} (L : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]
    (Z : TopDimIntegralSubscheme F) : MvPolynomial (Fin r) ℚ :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian Z.1.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion Z.1.subschemeι
  have : ∀ i, SheafOfModules.IsInvertible Z.1.subscheme.presheaf Z.1.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback Z.1.subschemeι).obj (L i)) :=
    fun i ↦ SheafOfModules.isInvertible_pullback Z.1.subschemeι (L i)
  eulerPolynomial k (Z.1.subschemeι ≫ f)
    (fun i ↦ (Scheme.Modules.pullback Z.1.subschemeι).obj (L i))
    (Stacks.Ample.unitModule Z.1.subscheme)

/-- The component polynomial takes the component Euler characteristics as its values. -/
private theorem componentEulerPolynomial_eval (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] {F : X.Modules} {r : ℕ} (L : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]
    (Z : TopDimIntegralSubscheme F) (n : Fin r → ℤ) :
    MvPolynomial.eval (fun j ↦ (n j : ℚ)) (componentEulerPolynomial k f L Z) =
      (componentTwistEulerCharacteristic k f L Z n : ℚ) :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian Z.1.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion Z.1.subschemeι
  have : ∀ i, SheafOfModules.IsInvertible Z.1.subscheme.presheaf Z.1.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback Z.1.subschemeι).obj (L i)) :=
    fun i ↦ SheafOfModules.isInvertible_pullback Z.1.subschemeι (L i)
  eulerPolynomial_eval k (Z.1.subschemeι ≫ f)
    (fun i ↦ (Scheme.Modules.pullback Z.1.subschemeι).obj (L i))
    (Stacks.Ample.unitModule Z.1.subscheme) n

/-! ### The ideal case of the dévissage -/

/-- **The ideal case.** Let `i : Y ⟶ X` be a closed immersion of an integral scheme whose range
is a top-dimensional subset of `Supp ℱ`, and let `𝒜 ⊆ 𝒪_Y` be a coherent submodule of full
support. The correction polynomial of `i_* 𝒜` vanishes or has total degree below the dimension
of `Supp ℱ`: the structure sheaf contributes exactly the component cut out by `i`, and the
quotient `𝒪_Y / 𝒜` is supported in smaller dimension. -/
private theorem correctionPolynomial_pushforward_totalDegree_lt (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsLocallyNoetherian X] {r : ℕ}
    (L : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]
    (F : X.Modules) [Fintype (TopDimIntegralSubscheme F)]
    {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] [IsIntegral Y]
    {A : Y.Modules} [A.IsCoherent] (φ : A ⟶ Stacks.Ample.unitModule Y) (hφ : Mono φ)
    (hA : _root_.SheafOfModules.supp A = Set.univ)
    (hsup : Set.range i.base ⊆ _root_.SheafOfModules.supp F)
    (hdimY : topologicalKrullDim Y = topologicalKrullDim (_root_.SheafOfModules.supp F)) :
    correctionPolynomial k f L F (componentEulerPolynomial k f L)
        ((Scheme.Modules.pushforward i).obj A) = 0 ∨
      ((correctionPolynomial k f L F (componentEulerPolynomial k f L)
          ((Scheme.Modules.pushforward i).obj A)).totalDegree : WithBot ℕ∞) <
        topologicalKrullDim (_root_.SheafOfModules.supp F) := by
  have hYn : IsLocallyNoetherian Y := isLocallyNoetherian_of_isClosedImmersion i
  have hCcoh : (cokernel φ).IsCoherent := _root_.SheafOfModules.cokernel_isCoherent φ
  let Z₀ : TopDimIntegralSubscheme F := topDimIntegralSubschemeOfClosedImmersion F i hsup hdimY
  have hZ₀supp : (Z₀.1.support : Set X) = Set.range i.base := ker_support_eq_range i
  have hZ₀gen : Z₀.genericPt = i (genericPoint Y) := by
    refine IsGenericPoint.eq ?_ (isGenericPoint_range i)
    rw [← hZ₀supp]
    exact TopDimIntegralSubscheme.isGenericPoint_genericPt Z₀
  have hUzero : correctionPolynomial k f L F (componentEulerPolynomial k f L)
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Y)) = 0 := by
    have hpoly : eulerPolynomial k f L
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Y)) =
          componentEulerPolynomial k f L Z₀ := by
      refine (eq_eulerPolynomial k f L _ (componentEulerPolynomial k f L Z₀) fun n ↦ ?_).symm
      rw [componentEulerPolynomial_eval]
      refine congrArg (fun m : ℤ ↦ (m : ℚ)) ?_
      have hZ₀n : IsLocallyNoetherian Z₀.1.subscheme :=
        isLocallyNoetherian_of_isClosedImmersion Z₀.1.subschemeι
      have hZ₀inv : ∀ t, SheafOfModules.IsInvertible Z₀.1.subscheme.presheaf
          Z₀.1.subscheme.ringCatSheaf.2
          ((Scheme.Modules.pullback Z₀.1.subschemeι).obj (L t)) :=
        fun t ↦ SheafOfModules.isInvertible_pullback Z₀.1.subschemeι (L t)
      show eulerCharacteristic k (Z₀.1.subschemeι ≫ f)
          (twistedSheaf (Stacks.Ample.unitModule Z₀.1.subscheme)
            (fun t ↦ (Scheme.Modules.pullback Z₀.1.subschemeι).obj (L t)) n) = _
      rw [← eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion k
        Z₀.1.subschemeι f L (Stacks.Ample.unitModule Z₀.1.subscheme) n inferInstance
        inferInstance]
      exact (eulerCharacteristic_twistedSheaf_eq_of_iso k f L inferInstance inferInstance
        (pushforwardUnitIsoImage i (I := Z₀.1) rfl) n).symm
    have hm₀ : Stacks.Chow.sheafMultiplicity
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Y)) Z₀.genericPt = 1 := by
      rw [hZ₀gen]
      exact sheafMultiplicity_pushforward_unit_genericPoint i
    have hmW : ∀ W : TopDimIntegralSubscheme F, W ≠ Z₀ →
        Stacks.Chow.sheafMultiplicity
          ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Y)) W.genericPt = 0 := by
      intro W hW
      refine Stacks.Chow.sheafMultiplicity_eq_zero_of_notMem_supp _ fun hmem ↦ hW ?_
      rw [Stacks.Chow.supp_pushforwardStructureSheaf i, ← hZ₀supp] at hmem
      exact topDimIntegralSubscheme_eq_of_genericPt_mem k f F W Z₀ hmem
    unfold correctionPolynomial
    rw [hpoly, Finset.sum_eq_single Z₀ (fun W _ hW ↦ by rw [hmW W hW]; simp)
      (fun h ↦ absurd (Finset.mem_univ Z₀) h), hm₀]
    simp
  have hCdim : topologicalKrullDim (_root_.SheafOfModules.supp
      ((Scheme.Modules.pushforward i).obj (cokernel φ))) <
      topologicalKrullDim (_root_.SheafOfModules.supp F) := by
    rw [topologicalKrullDim_supp_pushforward_of_isClosedImmersion i (cokernel φ), ← hdimY]
    exact topologicalKrullDim_supp_cokernel_lt k f i φ hφ hA
  have hCdeg := correctionPolynomial_totalDegree_lt_of_supp_dim_lt k f L F
    (componentEulerPolynomial k f L) ((Scheme.Modules.pushforward i).obj (cokernel φ)) hCdim
  have hTU : _root_.SheafOfModules.supp
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Y)) ⊆
      _root_.SheafOfModules.supp F := by
    rwa [Stacks.Chow.supp_pushforwardStructureSheaf i]
  have hT₁ : ((ShortComplex.cokernelSequence φ).map
      (Scheme.Modules.pushforward i)).X₁.IsCoherent :=
    inferInstanceAs (((Scheme.Modules.pushforward i).obj A).IsCoherent)
  have hT₂ : ((ShortComplex.cokernelSequence φ).map
      (Scheme.Modules.pushforward i)).X₂.IsCoherent :=
    inferInstanceAs
      (((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Y)).IsCoherent)
  have hT₃ : ((ShortComplex.cokernelSequence φ).map
      (Scheme.Modules.pushforward i)).X₃.IsCoherent :=
    inferInstanceAs (((Scheme.Modules.pushforward i).obj (cokernel φ)).IsCoherent)
  have hadd : correctionPolynomial k f L F (componentEulerPolynomial k f L)
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Y)) =
      correctionPolynomial k f L F (componentEulerPolynomial k f L)
          ((Scheme.Modules.pushforward i).obj A) +
        correctionPolynomial k f L F (componentEulerPolynomial k f L)
          ((Scheme.Modules.pushforward i).obj (cokernel φ)) :=
    correctionPolynomial_add_of_shortExact k f L F (componentEulerPolynomial k f L)
      (shortExact_map_pushforward_cokernelSequence i φ hφ) hTU
  rw [hUzero] at hadd
  have heq : correctionPolynomial k f L F (componentEulerPolynomial k f L)
      ((Scheme.Modules.pushforward i).obj A) =
      -correctionPolynomial k f L F (componentEulerPolynomial k f L)
        ((Scheme.Modules.pushforward i).obj (cokernel φ)) := by
    linear_combination -hadd
  rw [heq]
  simpa only [neg_eq_zero, MvPolynomial.totalDegree_neg] using hCdeg

/-! ### Tag 0BEN -/

/-- **[Stacks, Tag 0BEN].** For `X` proper over a field `k`, a coherent `𝒪_X`-module `ℱ` and
invertible `𝒪_X`-modules `𝓛_1, …, 𝓛_r`, the difference between
`χ(X, ℱ ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r})` and the sum over the top-dimensional integral
components `Z` of `Supp ℱ`, weighted by the length of `ℱ` at the generic point of `Z`, of
`χ(Z, 𝒪_Z ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r})` is a numerical polynomial in `n_1, …, n_r` of
total degree strictly less than `dim Supp ℱ`. -/
@[stacks 0BEN "the Euler characteristic minus the length-weighted Euler characteristics of the
top-dimensional components of the support is a numerical polynomial of lower total degree"]
theorem exists_eulerPolynomial_sub_topDimComponents_totalDegree_lt (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] {r : ℕ} (L : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]
    (F : X.Modules) [F.IsCoherent] :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ ((P.totalDegree : ℕ) : WithBot ℕ∞) <
        topologicalKrullDim (_root_.SheafOfModules.supp F)) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j ↦ (n j : ℚ)) P =
        (eulerCharacteristic k f (twistedSheaf F L n) : ℚ) -
          ∑ᶠ Z : TopDimIntegralSubscheme F,
            (Stacks.Chow.sheafMultiplicity F Z.genericPt : ℚ) *
              (componentTwistEulerCharacteristic k f L Z n : ℚ) := by
  classical
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hcpt : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hnoe : IsNoetherian X := ⟨⟩
  have hfinite : Finite (TopDimIntegralSubscheme F) := finite_topDimIntegralSubscheme k f F
  have hft : Fintype (TopDimIntegralSubscheme F) := Fintype.ofFinite _
  refine ⟨correctionPolynomial k f L F (componentEulerPolynomial k f L) F, ?_, fun n ↦ ?_⟩
  · refine of_integral_ideal_pushforwards
      (fun G ↦ ∀ hG : G.IsCoherent,
        _root_.SheafOfModules.supp G ⊆ _root_.SheafOfModules.supp F →
        correctionPolynomial k f L F (componentEulerPolynomial k f L) G = 0 ∨
          ((correctionPolynomial k f L F (componentEulerPolynomial k f L) G).totalDegree :
              WithBot ℕ∞) < topologicalKrullDim (_root_.SheafOfModules.supp F))
      ?_ ?_ ?_ ?_ F inferInstance Set.Subset.rfl
    · intro G hGz hGc _
      exact Or.inl (correctionPolynomial_eq_zero_of_isZero k f L F
        (componentEulerPolynomial k f L) G hGz)
    · intro G H e hPG hHc hHs
      have hGc : G.IsCoherent := isCoherent_of_iso e.symm
      rw [← correctionPolynomial_eq_of_iso k f L F (componentEulerPolynomial k f L) e]
      exact hPG hGc (by rw [_root_.SheafOfModules.supp_eq_of_iso e]; exact hHs)
    · intro S hS h₁ h₂ h₃ hP₁ hP₃ _ hSF
      obtain ⟨hF₁, hF₃⟩ := supp_subset_of_shortExact hS hSF
      rw [correctionPolynomial_add_of_shortExact k f L F (componentEulerPolynomial k f L) hS hSF]
      exact mvPolynomial_add_totalDegree_lt (hP₁ h₁ hF₁) (hP₃ h₃ hF₃)
    · intro Y i hi hY I hI hne hGc hsup
      have hIq : I.toSheafOfModules.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent _
      have hsuppA : _root_.SheafOfModules.supp I.toSheafOfModules = Set.univ :=
        Stacks.AlgebraicGeometry.Tag01YHFullSupport.supp_eq_univ_of_not_isZero I hIq hne
      by_cases hdim : topologicalKrullDim (_root_.SheafOfModules.supp
          ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)) <
            topologicalKrullDim (_root_.SheafOfModules.supp F)
      · exact correctionPolynomial_totalDegree_lt_of_supp_dim_lt k f L F
          (componentEulerPolynomial k f L) _ hdim
      · have hsupp : _root_.SheafOfModules.supp
            ((Scheme.Modules.pushforward i).obj I.toSheafOfModules) = Set.range i.base := by
          rw [supp_pushforward_of_isClosedImmersion i I.toSheafOfModules, hsuppA, Set.image_univ]
        have hdimG : topologicalKrullDim (_root_.SheafOfModules.supp
            ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)) =
            topologicalKrullDim (_root_.SheafOfModules.supp F) :=
          le_antisymm (topologicalKrullDim_le_of_subset hsup) (le_of_not_gt hdim)
        have hdimY : topologicalKrullDim Y =
            topologicalKrullDim (_root_.SheafOfModules.supp F) := by
          rw [← topologicalKrullDim_range_eq i, ← hsupp]
          exact hdimG
        exact correctionPolynomial_pushforward_totalDegree_lt k f L F i I.ι
          (inferInstanceAs (Mono (C := _root_.SheafOfModules Y.ringCatSheaf) I.ι))
          hsuppA (hsupp.symm.subset.trans hsup) hdimY
  · rw [finsum_eq_sum_of_fintype]
    unfold correctionPolynomial
    rw [MvPolynomial.eval_sub, eulerPolynomial_eval, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun Z _ ↦ ?_
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, componentEulerPolynomial_eval]

end AlgebraicGeometry

end
