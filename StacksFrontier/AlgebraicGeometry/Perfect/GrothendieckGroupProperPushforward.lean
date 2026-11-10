module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.UniformVanishing
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroup
public import StacksFrontier.AlgebraicGeometry.ProjectiveCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.CategoryTheory.Abelian.SigmaExactness
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.KTheory.SerreQuotient
import StacksCore.Tactic.StacksAttribute

/-!
# Proper pushforward on the Grothendieck group of coherent sheaves

Let `f : X ⟶ Y` be a proper morphism of locally Noetherian schemes. The even and odd sums

  `E(ℱ) = ⨁_{i ≥ 0} R ²ⁱ f_* ℱ`   and   `O(ℱ) = ⨁_{i ≥ 0} R ²ⁱ⁺¹ f_* ℱ`

of the higher direct images of a coherent `𝒪_X`-module `ℱ` are again coherent `𝒪_Y`-modules, and
`ℱ ↦ [E(ℱ)] − [O(ℱ)]` is additive along short exact sequences, so it descends to a homomorphism

  `f_* : K'₀(X) ⟶ K'₀(Y)`

of Grothendieck groups of coherent sheaves.

## Main definitions

* `AlgebraicGeometry.ProperPushforwardKZero.parityDirectImageSum`: the sum
  `⨁_{i ≥ 0} R ^(2i+r) f_* ℱ` of the higher direct images of one parity.
* `AlgebraicGeometry.ProperPushforwardKZero.parityObject`: that sum as an object of the category
  of coherent `𝒪_Y`-modules.
* `AlgebraicGeometry.ProperPushforwardKZero.ExactHexagon`: an exact cycle of six objects of an
  abelian category.
* `AlgebraicGeometry.ProperPushforwardKZero.HasParityHexagons`: the property that every short
  exact sequence of coherent `𝒪_X`-modules produces an exact hexagon of parity sums.
* `AlgebraicGeometry.ProperPushforwardKZero.higherDirectImageDeltaFunctor`: the higher direct
  images along `f` as a cohomological `δ`-functor, i.e. with their long exact sequence.
* `AlgebraicGeometry.ProperPushforwardKZero.properPushforward`: the homomorphism
  `f_* : K'₀(X) ⟶ K'₀(Y)`.

## Main results

* `AlgebraicGeometry.ProperPushforwardKZero.isCoherent_parityDirectImageSum`: the even and odd
  sums of higher direct images of a coherent module along a proper morphism are coherent.
* `AlgebraicGeometry.ProperPushforwardKZero.properPushforward_mk`: the value of `f_*` on the
  class of a coherent module is `[E(ℱ)] − [O(ℱ)]`, for any coherent modules realizing the even
  and odd sums.
* `AlgebraicGeometry.ProperPushforwardKZero.hasParityHexagons`: every short exact sequence of
  coherent `𝒪_X`-modules does produce such a hexagon.
* `AlgebraicGeometry.ProperPushforwardKZero.existsUnique_properPushforward`: **[Stacks, Tag
  0FDL]**: there is exactly one homomorphism `K'₀(X) ⟶ K'₀(Y)` sending `[ℱ]` to
  `[E(ℱ)] − [O(ℱ)]`.
* `AlgebraicGeometry.ProperPushforwardKZero.exists_isZero_higherDirectImage_of_compactSpace`: for
  a quasi-compact target the higher direct images vanish in all large degrees, uniformly in the
  module, so that the two sums are finite.

## Implementation notes

**Coherence of the two sums is proved, not assumed.** Each `R ⁱ f_* ℱ` is coherent by
[Stacks, Tag 02O5], which this repository proves in
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherent`. Over an affine open `V`
of `Y` the restriction of `f` is again proper, hence quasi-compact and quasi-separated over a
quasi-compact base, so the uniform vanishing of [Stacks, Tag 01XJ] gives one degree beyond which
all higher direct images along `f ∣_ V` vanish; the comparison of
[Stacks, Tag 01E5] transports that to the restriction of `R ⁱ f_* ℱ` to `V`. The sum therefore
restricts to a *finite* coproduct of coherent modules on each affine open, which is coherent, and
coherence is local on `Y`. That is the content of
`isCoherent_sigma_of_locally_eventually_isZero` and of
`isCoherent_parityDirectImageSum`, and it is the source's reasons "the sheaves `R ⁱ f_* ℱ` are
coherent" and "locally only a finite number are nonzero".

**The long exact sequence.** The remaining reason the source gives — "a short exact sequence of
coherent sheaves on `X` produces a long exact sequence of `R ⁱ f_*` on `Y`" — is the cohomological
`δ`-functor of [Stacks, Tag 05TE] for the right derived functors of `Scheme.Modules.pushforward f`,
which `Stacks.DerivedIndexing.rightDerivedPlusDeltaFunctor` provides: that is
`higherDirectImageDeltaFunctor`. Splitting that long exact sequence by the parity of the degree
and summing produces the exact hexagon

  `E(ℱ₁) ⟶ E(ℱ₂) ⟶ E(ℱ₃) ⟶ O(ℱ₁) ⟶ O(ℱ₂) ⟶ O(ℱ₃) ⟶ E(ℱ₁)`,

whose two connecting arrows are the connecting maps of the long exact sequence; the last one is
followed by the inclusion of `⨁_{i ≥ 0} R ^(2i+2) f_* ℱ₁` into `E(ℱ₁)`, which is where exactness
uses that `R ⁰ f_* ℱ₁ ⟶ R ⁰ f_* ℱ₂` is a monomorphism. That the sums of the exact short complexes
are again exact is exactness of coproducts, Grothendieck's axiom AB4, which holds in a category
of sheaves of modules because it is Grothendieck abelian; the summing is
`Stacks.SigmaExactness.exact_sigmaMap`. The resulting hexagon lives in all sheaves of modules and
is pulled back along the fully faithful exact inclusion of the coherent ones by
`nonempty_exactHexagon_of_obj`. Together these give `hasParityHexagons`, and from it the
additivity of `ℱ ↦ [E(ℱ)] − [O(ℱ)]`, which is a computation in the Grothendieck group —
`ExactHexagon.mk_add_eq`, six applications of `KZero.mk_homology_add_mk_X₁` around the cycle — and
then the homomorphism itself.

**How the source's two halves are divided between two modules.** The map and its value on classes
is the first assertion of the remark, and is this module. The second, the restatement
`f_*[ℱ] = ∑ (−1)ⁱ [R ⁱ f_* ℱ] = [R f_* ℱ]` for quasi-compact `Y`, is
`StacksFrontier/AlgebraicGeometry/Perfect/GrothendieckGroupProperPushforwardDerived.lean`, where
`properPushforward_mk_eq_finsum` is the alternating-sum identity — the finiteness that makes the
sum finite is `exists_isZero_higherDirectImage_of_compactSpace`, below — and
`properPushforward_mk_eq_derivedClass` is the identity `f_*[ℱ] = [Rf_* ℱ]` under the
identification of `K'₀(Y)` with `K₀(D^b_Coh(𝒪_Y))` of [Stacks, Tag 0FDF].

## References

* [Stacks Project, Tag 0FDL](https://stacks.math.columbia.edu/tag/0FDL)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 0FDF](https://stacks.math.columbia.edu/tag/0FDF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProperPushforwardKZero

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Exact hexagons and their Grothendieck classes -/

/-- **An exact hexagon**: a cycle of six objects and six morphisms of an abelian category, each
pair of consecutive morphisms composing to zero and the resulting two-term complex being exact.
This is the shape in which the long exact sequence of a short exact sequence closes up after the
degrees have been collected into two sums by parity. -/
structure ExactHexagon {A : Type*} [Category A] [Abelian A] (M₀ M₁ M₂ M₃ M₄ M₅ : A) where
  /-- the arrow `M₀ ⟶ M₁` -/
  d₀ : M₀ ⟶ M₁
  /-- the arrow `M₁ ⟶ M₂` -/
  d₁ : M₁ ⟶ M₂
  /-- the arrow `M₂ ⟶ M₃` -/
  d₂ : M₂ ⟶ M₃
  /-- the arrow `M₃ ⟶ M₄` -/
  d₃ : M₃ ⟶ M₄
  /-- the arrow `M₄ ⟶ M₅` -/
  d₄ : M₄ ⟶ M₅
  /-- the arrow `M₅ ⟶ M₀` closing the cycle -/
  d₅ : M₅ ⟶ M₀
  /-- `d₀` and `d₁` compose to zero -/
  w₀ : d₀ ≫ d₁ = 0
  /-- `d₁` and `d₂` compose to zero -/
  w₁ : d₁ ≫ d₂ = 0
  /-- `d₂` and `d₃` compose to zero -/
  w₂ : d₂ ≫ d₃ = 0
  /-- `d₃` and `d₄` compose to zero -/
  w₃ : d₃ ≫ d₄ = 0
  /-- `d₄` and `d₅` compose to zero -/
  w₄ : d₄ ≫ d₅ = 0
  /-- `d₅` and `d₀` compose to zero -/
  w₅ : d₅ ≫ d₀ = 0
  /-- exactness at `M₁` -/
  exact₀ : (ShortComplex.mk d₀ d₁ w₀).Exact
  /-- exactness at `M₂` -/
  exact₁ : (ShortComplex.mk d₁ d₂ w₁).Exact
  /-- exactness at `M₃` -/
  exact₂ : (ShortComplex.mk d₂ d₃ w₂).Exact
  /-- exactness at `M₄` -/
  exact₃ : (ShortComplex.mk d₃ d₄ w₃).Exact
  /-- exactness at `M₅` -/
  exact₄ : (ShortComplex.mk d₄ d₅ w₄).Exact
  /-- exactness at `M₀` -/
  exact₅ : (ShortComplex.mk d₅ d₀ w₅).Exact

/-- **The alternating class identity of an exact hexagon.** Going around an exact hexagon, the
sum of the classes of the objects in even position equals the sum of the classes of the objects
in odd position.

At each vertex exactness makes the homology of the two-term complex vanish, so
`KZero.mk_homology_add_mk_X₁` reads `[Mⱼ] = [ker dⱼ] + [ker dⱼ₊₁]`; adding the six identities,
each kernel occurs once on each side. -/
theorem ExactHexagon.mk_add_eq (A : Type*) [Category A] [Abelian A]
    {M₀ M₁ M₂ M₃ M₄ M₅ : A} (H : ExactHexagon M₀ M₁ M₂ M₃ M₄ M₅) :
    KZero.mk A M₀ + KZero.mk A M₂ + KZero.mk A M₄ =
      KZero.mk A M₁ + KZero.mk A M₃ + KZero.mk A M₅ := by
  have aux {P Q R : A} (p : P ⟶ Q) (q : Q ⟶ R) (hpq : p ≫ q = 0)
      (he : (ShortComplex.mk p q hpq).Exact) :
      KZero.mk A P = KZero.mk A (kernel p) + KZero.mk A (kernel q) := by
    have hz := (ShortComplex.mk p q hpq).exact_iff_isZero_homology.mp he
    have h := KZero.mk_homology_add_mk_X₁ (ShortComplex.mk p q hpq)
    rwa [KZero.mk_eq_zero_of_isZero hz, zero_add] at h
  rw [aux H.d₀ H.d₁ H.w₀ H.exact₀, aux H.d₁ H.d₂ H.w₁ H.exact₁,
    aux H.d₂ H.d₃ H.w₂ H.exact₂, aux H.d₃ H.d₄ H.w₃ H.exact₃,
    aux H.d₄ H.d₅ H.w₄ H.exact₄, aux H.d₅ H.d₀ H.w₅ H.exact₅]
  abel

/-! ### Coproducts over `ℕ` with a shifted summand -/

/-- The inclusion of the summands of positive degree into a coproduct indexed by `ℕ` is a split
monomorphism. -/
theorem mono_sigmaDesc_ι_succ {C : Type*} [Category C] [HasZeroMorphisms C] (F : ℕ → C)
    [HasCoproduct F] [HasCoproduct fun i => F (i + 1)] :
    Mono (Sigma.desc fun i => Sigma.ι F (i + 1) : (∐ fun i => F (i + 1)) ⟶ ∐ F) :=
  SplitMono.mono
    { retraction := Sigma.desc fun j => match j with
        | 0 => 0
        | k + 1 => Sigma.ι (fun i => F (i + 1)) k
      id := Sigma.hom_ext _ _ fun i => by
        rw [Sigma.ι_comp_desc_assoc, Category.comp_id]
        exact Sigma.ι_comp_desc _ _ }

/-- If the degree `0` term of a family indexed by `ℕ` is zero, the inclusion of the summands of
positive degree into its coproduct is a split epimorphism. -/
theorem epi_sigmaDesc_ι_succ {C : Type*} [Category C] [HasZeroMorphisms C] (G : ℕ → C)
    [HasCoproduct G] [HasCoproduct fun i => G (i + 1)] (hG : IsZero (G 0)) :
    Epi (Sigma.desc fun i => Sigma.ι G (i + 1) : (∐ fun i => G (i + 1)) ⟶ ∐ G) :=
  SplitEpi.epi
    { section_ := Sigma.desc fun j => match j with
        | 0 => 0
        | k + 1 => Sigma.ι (fun i => G (i + 1)) k
      id := Sigma.hom_ext _ _ fun j => by
        cases j with
        | zero => exact hG.eq_of_src _ _
        | succ k =>
          rw [Sigma.ι_comp_desc_assoc, Category.comp_id]
          exact Sigma.ι_comp_desc _ _ }

/-- The sums of two composable families of morphisms compose to zero if each pair does. -/
private theorem sigmaMap_comp_sigmaMap_eq_zero {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B D : ℕ → C} [HasCoproduct A] [HasCoproduct B] [HasCoproduct D]
    (f : ∀ i, A i ⟶ B i) (g : ∀ i, B i ⟶ D i) (h : ∀ i, f i ≫ g i = 0) :
    Limits.Sigma.map f ≫ Limits.Sigma.map g = 0 := by
  rw [Limits.Sigma.map_comp_map]
  exact Sigma.hom_ext _ _ fun i => by simp [h i]

/-- **Exactness at the source of morphisms raising the degree.** If `a i` and `c i` form an exact
complex for every `i`, where `c i` lands in `F (i + 1)`, then the sum of the `a i` and the sum of
the `c i` followed by the inclusion of the summands of positive degree of `∐ F` form an exact
complex. -/
theorem exact_sigmaMap_sigmaDesc_succ {C : Type*} [Category C] [Abelian C]
    [HasCoproductsOfShape ℕ C] [HasExactColimitsOfShape (Discrete ℕ) C]
    {X Y F : ℕ → C} (a : ∀ i, X i ⟶ Y i) (c : ∀ i, Y i ⟶ F (i + 1))
    (hac : ∀ i, a i ≫ c i = 0) (he : ∀ i, (ShortComplex.mk (a i) (c i) (hac i)).Exact) :
    (ShortComplex.mk (Limits.Sigma.map a) (Sigma.desc fun i => c i ≫ Sigma.ι F (i + 1))
      (Sigma.hom_ext _ _ fun i => by simp [reassoc_of% hac i])).Exact := by
  have hz : Limits.Sigma.map a ≫ Sigma.desc (fun i => c i ≫ Sigma.ι F (i + 1)) = 0 :=
    Sigma.hom_ext _ _ fun i => by simp [reassoc_of% hac i]
  have hz' := sigmaMap_comp_sigmaMap_eq_zero a c hac
  let φ : ShortComplex.mk _ _ hz' ⟶ ShortComplex.mk _ _ hz :=
    ShortComplex.homMk (𝟙 _) (𝟙 _) (Sigma.desc fun i => Sigma.ι F (i + 1)) (by simp)
      (Sigma.hom_ext _ _ fun i => by simp)
  have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 _))
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono φ.τ₃ := mono_sigmaDesc_ι_succ F
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
    (Stacks.SigmaExactness.exact_sigmaMap _ _ _ a c hac he)

/-- **Exactness at the target of morphisms raising the degree.** If `c i` and `b (i + 1)` form an
exact complex for every `i`, where `c i` lands in `F (i + 1)`, and `b 0` is a monomorphism, then
the sum of the `c i` followed by the inclusion of the summands of positive degree of `∐ F` and the
sum of the `b i` form an exact complex. -/
theorem exact_sigmaDesc_succ_sigmaMap {C : Type*} [Category C] [Abelian C]
    [HasCoproductsOfShape ℕ C] [HasExactColimitsOfShape (Discrete ℕ) C]
    {X F G : ℕ → C} (c : ∀ i, X i ⟶ F (i + 1)) (b : ∀ i, F i ⟶ G i)
    (hcb : ∀ i, c i ≫ b (i + 1) = 0)
    (he : ∀ i, (ShortComplex.mk (c i) (b (i + 1)) (hcb i)).Exact) (hb : Mono (b 0)) :
    (ShortComplex.mk (Sigma.desc fun i => c i ≫ Sigma.ι F (i + 1)) (Limits.Sigma.map b)
      (Sigma.hom_ext _ _ fun i => by simp [reassoc_of% hcb i])).Exact := by
  let X' : ℕ → C := Stacks.SigmaExactness.shiftZero X
  let d : ∀ i, X' i ⟶ F i := fun i => match i with | 0 => 0 | j + 1 => c j
  have hd : ∀ i, d i ≫ b i = 0 := fun i => by
    cases i with
    | zero => simp [d]
    | succ j => exact hcb j
  have hde : ∀ i, (ShortComplex.mk (d i) (b i) (hd i)).Exact := fun i => by
    cases i with
    | zero => exact (ShortComplex.exact_iff_mono _ (by simp [d])).2 hb
    | succ j => exact he j
  have hz : Sigma.desc (fun i => c i ≫ Sigma.ι F (i + 1)) ≫ Limits.Sigma.map b = 0 :=
    Sigma.hom_ext _ _ fun i => by simp [reassoc_of% hcb i]
  have hs : (Sigma.desc fun i => Sigma.ι X' (i + 1) : ∐ X ⟶ ∐ X') ≫ Limits.Sigma.map d =
      Sigma.desc fun i => c i ≫ Sigma.ι F (i + 1) :=
    Sigma.hom_ext _ _ fun i =>
      (Sigma.ι_comp_desc_assoc (f := X) (fun i => Sigma.ι X' (i + 1)) i _).trans <|
        (Sigma.ι_map d (i + 1)).trans (Sigma.ι_comp_desc (fun i => c i ≫ Sigma.ι F (i + 1)) i).symm
  have hz' := sigmaMap_comp_sigmaMap_eq_zero d b hd
  let ψ : ShortComplex.mk _ _ hz ⟶ ShortComplex.mk _ _ hz' :=
    ShortComplex.homMk (Sigma.desc fun i => Sigma.ι X' (i + 1)) (𝟙 _) (𝟙 _)
      (by simp [hs]) (by simp)
  have : Epi ψ.τ₁ := epi_sigmaDesc_ι_succ X' (isZero_zero C)
  have : IsIso ψ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono ψ.τ₃ := inferInstanceAs (Mono (𝟙 _))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2
    (Stacks.SigmaExactness.exact_sigmaMap _ _ _ d b hd hde)

/-- **A long exact sequence closes up into an exact hexagon after summing by parity.** Let

  `⋯ ⟶ A₀ n ⟶ A₁ n ⟶ A₂ n ⟶ A₀ (n+1) ⟶ A₁ (n+1) ⟶ ⋯`

be exact at every term, with `A₀ 0 ⟶ A₁ 0` a monomorphism, in an abelian category whose
coproducts indexed by `ℕ` are exact. Collecting the degrees by parity and summing gives an exact
hexagon on the six sums.

Four of the six vertices are sums of exact short complexes taken degree by degree. At the two
remaining vertices the sums are shifted: the connecting morphism out of `A₂ (2i+1)` lands in
`A₀ (2i+2)`, the `(i+1)`-st even summand, so the sixth arrow is the sum of the connecting
morphisms followed by the inclusion of the summands of positive even degree. Exactness at the
even sum of `A₀` is therefore the sum of the complexes `A₂ (2i+1) ⟶ A₀ (2i+2) ⟶ A₁ (2i+2)`
together with `0 ⟶ A₀ 0 ⟶ A₁ 0`, which is exact precisely because `A₀ 0 ⟶ A₁ 0` is a
monomorphism. -/
theorem nonempty_exactHexagon_of_longExact {C : Type*} [Category C] [Abelian C]
    [HasCoproductsOfShape ℕ C] [HasExactColimitsOfShape (Discrete ℕ) C]
    (A₀ A₁ A₂ : ℕ → C) (u : ∀ n, A₀ n ⟶ A₁ n) (v : ∀ n, A₁ n ⟶ A₂ n)
    (w : ∀ n, A₂ n ⟶ A₀ (n + 1))
    (huv : ∀ n, u n ≫ v n = 0) (hvw : ∀ n, v n ≫ w n = 0) (hwu : ∀ n, w n ≫ u (n + 1) = 0)
    (euv : ∀ n, (ShortComplex.mk (u n) (v n) (huv n)).Exact)
    (evw : ∀ n, (ShortComplex.mk (v n) (w n) (hvw n)).Exact)
    (ewu : ∀ n, (ShortComplex.mk (w n) (u (n + 1)) (hwu n)).Exact)
    (hmono : Mono (u 0)) :
    Nonempty (ExactHexagon (∐ fun i => A₀ (2 * i)) (∐ fun i => A₁ (2 * i))
      (∐ fun i => A₂ (2 * i)) (∐ fun i => A₀ (2 * i + 1)) (∐ fun i => A₁ (2 * i + 1))
      (∐ fun i => A₂ (2 * i + 1))) := by
  have hp : ∀ i : ℕ, 2 * i + 1 + 1 = 2 * (i + 1) := fun i => by lia
  let c : ∀ i : ℕ, A₂ (2 * i + 1) ⟶ A₀ (2 * (i + 1)) := fun i =>
    w (2 * i + 1) ≫ eqToHom (congrArg A₀ (hp i))
  have hvc : ∀ i, v (2 * i + 1) ≫ c i = 0 := fun i => by
    simp only [c, ← Category.assoc, hvw, zero_comp]
  have hcu : ∀ i, c i ≫ u (2 * (i + 1)) = 0 := fun i =>
    Stacks.SigmaExactness.comp_eqToHom_eq_zero (A := A₀) (B := A₁) (hp i) (w (2 * i + 1)) u
      (hwu (2 * i + 1))
  exact ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _,
    Stacks.SigmaExactness.exact_sigmaMap _ _ _ (fun i => u (2 * i)) (fun i => v (2 * i))
      (fun i => huv (2 * i)) fun i => euv (2 * i),
    Stacks.SigmaExactness.exact_sigmaMap _ _ _ (fun i => v (2 * i)) (fun i => w (2 * i))
      (fun i => hvw (2 * i)) fun i => evw (2 * i),
    Stacks.SigmaExactness.exact_sigmaMap _ _ _ (fun i => w (2 * i)) (fun i => u (2 * i + 1))
      (fun i => hwu (2 * i)) fun i => ewu (2 * i),
    Stacks.SigmaExactness.exact_sigmaMap _ _ _ (fun i => u (2 * i + 1)) (fun i => v (2 * i + 1))
      (fun i => huv (2 * i + 1)) fun i => euv (2 * i + 1),
    exact_sigmaMap_sigmaDesc_succ (F := fun j => A₀ (2 * j)) (fun i => v (2 * i + 1)) c hvc
      fun i => Stacks.SigmaExactness.exact_comp_eqToHom (D := A₀) (hp i) (v (2 * i + 1))
        (w (2 * i + 1)) (hvw (2 * i + 1)) (evw (2 * i + 1)),
    exact_sigmaDesc_succ_sigmaMap (F := fun j => A₀ (2 * j)) c (fun i => u (2 * i)) hcu
      (fun i => Stacks.SigmaExactness.exact_eqToHom_comp (A := A₀) (B := A₁) (hp i)
        (w (2 * i + 1)) u (hwu (2 * i + 1)) (ewu (2 * i + 1))) hmono⟩⟩

/-! ### Coproducts over `ℕ` with a vanishing tail -/

/-- A coproduct over `ℕ` all of whose terms in degree `≥ N` vanish is the coproduct of its first
`N` terms. -/
def sigmaFinIsoOfIsZeroTail {C : Type*} [Category C] [HasZeroMorphisms C]
    (F : ℕ → C) [HasCoproduct F] (N : ℕ) [HasCoproduct fun i : Fin N => F i.val]
    (hzero : ∀ i, N ≤ i → IsZero (F i)) : (∐ fun i : Fin N => F i.val) ≅ ∐ F := by
  classical
  let c : Cofan F := Cofan.mk _ fun i =>
    if hi : i < N then Sigma.ι (fun j : Fin N => F j.val) ⟨i, hi⟩ else 0
  have hc : IsColimit c := by
    refine Cofan.IsColimit.mk c (fun t => Sigma.desc fun j : Fin N => t.inj j.val) ?_ ?_
    · intro t i
      by_cases hi : i < N
      · simp [c, hi]
      · exact (hzero i (by lia)).eq_of_src _ _
    · intro t m hm
      refine Sigma.hom_ext m (Sigma.desc fun j : Fin N => t.inj j.val) fun j => ?_
      simpa [c, j.isLt] using hm j.val
  exact hc.coconePointUniqueUpToIso (colimit.isColimit (Discrete.functor F))

/-- **A locally finite coproduct of coherent modules is coherent.** Let `A` be a family of
coherent `𝒪_Y`-modules indexed by `ℕ` such that over every affine open of `Y` all but finitely
many of them vanish. Then `⨁ A` is coherent: its restriction to an affine open is a finite
coproduct of coherent modules, and coherence is local on `Y` by
`AlgebraicGeometry.Modules.isCoherent_of_restrict`. -/
theorem isCoherent_sigma_of_locally_eventually_isZero {Y : Scheme.{u}} (A : ℕ → Y.Modules)
    (hA : ∀ i, (A i).IsCoherent)
    (hzero : ∀ V : Y.Opens, IsAffineOpen V → ∃ N : ℕ, ∀ i, N ≤ i →
      IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (A i))) :
    (∐ A).IsCoherent := by
  refine Modules.isCoherent_of_restrict (∐ A) (fun V : Y.affineOpens => (V : Y.Opens))
    (iSup_affineOpens_eq_top Y) fun V => ?_
  obtain ⟨N, hN⟩ := hzero (V : Y.Opens) V.2
  let R := Scheme.Modules.restrictFunctor (V : Y.Opens).ι
  have hiso : R.obj (∐ A) ≅ ∐ fun i => R.obj (A i) :=
    preservesColimitIso R (Discrete.functor A) ≪≫
      HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _)
  have hfin : (∐ fun i : Fin N => R.obj (A i.val)).IsCoherent :=
    CoherentAbelian.isCoherent_of_stacksIsCoherent
      (Stacks.SheafOfModules.isCoherent_sigma _ fun j =>
        CoherentAbelian.stacksIsCoherent_of_isCoherent
          (Modules.isCoherent_restrict (hM := hA j.val) (A j.val) _))
  exact ObjectProperty.prop_of_iso (P := fun M => SheafOfModules.IsCoherent M)
    ((sigmaFinIsoOfIsZeroTail (fun i => R.obj (A i)) N hN).trans hiso.symm) hfin

/-! ### The higher direct images and their sums by parity -/

variable {X Y : Scheme.{u}}

/-- The `i`-th higher direct image `R ⁱ f_* F` of a sheaf of modules, as the `i`-th right derived
functor of the direct image on the bounded below derived category. -/
def higherDirectImage (f : X ⟶ Y) (F : X.Modules) (i : ℕ) : Y.Modules :=
  ((Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj F

/-- **[Stacks, Tag 02O5].** Every higher direct image of a coherent module along a proper
morphism to a locally Noetherian scheme is coherent. This is
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherent`. -/
theorem isCoherent_higherDirectImage (f : X ⟶ Y) [IsLocallyNoetherian Y] [IsProper f]
    (F : X.Modules) [F.IsCoherent] (i : ℕ) : (higherDirectImage f F i).IsCoherent :=
  ProperCoherenceWitness.higherDirectImageIsCoherent X Y f ‹_› ‹_› F ‹_› i

/-- **The higher direct images of a coherent module vanish locally in all large degrees.** Over
an affine open `V` of the target the restriction of a proper morphism is proper, hence
quasi-compact and quasi-separated with quasi-compact target, so [Stacks, Tag 01XJ] provides one
degree beyond which every higher direct image along `f ∣_ V` of a quasi-coherent module vanishes;
[Stacks, Tag 01E5] identifies those with the restrictions to `V` of the higher direct images
along `f`. -/
theorem exists_isZero_restrict_higherDirectImage (f : X ⟶ Y) [IsProper f] (F : X.Modules)
    [F.IsCoherent] (V : Y.Opens) (hV : IsAffineOpen V) :
    ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
      IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (higherDirectImage f F i)) := by
  have : IsAffine V.toScheme := hV
  have : IsProper (f ∣_ V) := inferInstance
  obtain ⟨N, hN⟩ :=
    Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerived_of_isAffine_target
      (f ∣_ V)
  refine ⟨N, fun i hi => ?_⟩
  have : ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F).IsCoherent :=
    Modules.isCoherent_restrict F _
  have hqc : ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  exact (ProjectiveCoherentImage.higherDirectImageRestrictObjIso f V F i).symm.isZero_iff.mpr
    ((Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
      (Scheme.Modules.pushforward (f ∣_ V)) i
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)).1 (hN _ hqc i hi))

/-- The sum `⨁_{i ≥ 0} R ^(2i+r) f_* F` of the higher direct images of `F` in the degrees
congruent to `r` modulo `2`; the even sum for `r = 0` and the odd sum for `r = 1`. -/
def parityDirectImageSum (f : X ⟶ Y) (F : X.Modules) (r : ℕ) : Y.Modules :=
  ∐ fun i : ℕ => higherDirectImage f F (2 * i + r)

/-- **The even and odd sums of higher direct images are coherent.** Each summand is coherent by
[Stacks, Tag 02O5] and, over an affine open of the target, all but finitely many vanish by
[Stacks, Tag 01XJ]; `isCoherent_sigma_of_locally_eventually_isZero` concludes. -/
theorem isCoherent_parityDirectImageSum (f : X ⟶ Y) [IsLocallyNoetherian Y] [IsProper f]
    (F : X.Modules) [F.IsCoherent] (r : ℕ) : (parityDirectImageSum f F r).IsCoherent := by
  refine isCoherent_sigma_of_locally_eventually_isZero _
    (fun i => isCoherent_higherDirectImage f F (2 * i + r)) fun V hV => ?_
  obtain ⟨N, hN⟩ := exists_isZero_restrict_higherDirectImage f F V hV
  exact ⟨N, fun i hi => hN (2 * i + r) (by omega)⟩

/-- The `i`-th higher direct image of a coherent module along a proper morphism, as an object of
the category of coherent `𝒪_Y`-modules. -/
def coherentHigherDirectImage (f : X ⟶ Y) [IsLocallyNoetherian Y] [IsProper f]
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) (i : ℕ) :
    Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf :=
  ⟨higherDirectImage f F.obj i,
    have : F.obj.IsCoherent := CoherentAbelian.isCoherent_of_stacksIsCoherent F.property
    CoherentAbelian.stacksIsCoherent_of_isCoherent (isCoherent_higherDirectImage f F.obj i)⟩

/-- The sum `⨁_{i ≥ 0} R ^(2i+r) f_* F` as an object of the category of coherent
`𝒪_Y`-modules. -/
def parityObject (f : X ⟶ Y) [IsLocallyNoetherian Y] [IsProper f]
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) (r : ℕ) :
    Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf :=
  ⟨parityDirectImageSum f F.obj r,
    have : F.obj.IsCoherent := CoherentAbelian.isCoherent_of_stacksIsCoherent F.property
    CoherentAbelian.stacksIsCoherent_of_isCoherent
      (isCoherent_parityDirectImageSum f F.obj r)⟩

/-- The underlying sheaf of modules of `parityObject f F r` is `parityDirectImageSum f F.obj r`. -/
@[simp]
theorem parityObject_obj (f : X ⟶ Y) [IsLocallyNoetherian Y] [IsProper f]
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) (r : ℕ) :
    (parityObject f F r).obj = parityDirectImageSum f F.obj r :=
  rfl

/-- The class `[⨁ R ²ⁱ f_* ℱ] − [⨁ R ²ⁱ⁺¹ f_* ℱ]` in `K'₀(Y)`, the value the source prescribes
for `f_*[ℱ]`. -/
def parityClass (f : X ⟶ Y) [IsLocallyNoetherian Y] [IsProper f]
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) : CoherentKZero Y :=
  KZero.mk _ (parityObject f F 0) - KZero.mk _ (parityObject f F 1)

/-! ### The homomorphism on Grothendieck groups -/

/-- **The long exact sequence input of [Stacks, Tag 0FDL].** Every short exact sequence
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of coherent `𝒪_X`-modules produces an exact hexagon

  `E(ℱ₁) ⟶ E(ℱ₂) ⟶ E(ℱ₃) ⟶ O(ℱ₁) ⟶ O(ℱ₂) ⟶ O(ℱ₃) ⟶ E(ℱ₁)`

of even and odd sums of higher direct images. This is the source's third reason for well
definedness — the long exact sequence of the `R ⁱ f_*` — with its terms collected by the parity
of the degree. It holds: see `hasParityHexagons`. -/
def HasParityHexagons (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsProper f] : Prop :=
  ∀ S : ShortComplex (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf), S.ShortExact →
    Nonempty (ExactHexagon (parityObject f S.X₁ 0) (parityObject f S.X₂ 0)
      (parityObject f S.X₃ 0) (parityObject f S.X₁ 1) (parityObject f S.X₂ 1)
      (parityObject f S.X₃ 1))

/-- **An exact hexagon of coherent modules from one of the underlying sheaves of modules.** The
inclusion of the coherent modules is fully faithful and exact, so it reflects both the vanishing
of a composite and the exactness of a short complex. -/
theorem nonempty_exactHexagon_of_obj [IsLocallyNoetherian Y]
    (M₀ M₁ M₂ M₃ M₄ M₅ : Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (H : ExactHexagon M₀.obj M₁.obj M₂.obj M₃.obj M₄.obj M₅.obj) :
    Nonempty (ExactHexagon M₀ M₁ M₂ M₃ M₄ M₅) := by
  let P : ObjectProperty (SheafOfModules.{u} Y.ringCatSheaf) :=
    Stacks.SheafOfModules.coherentModules Y.ringCatSheaf
  have : PreservesFiniteLimits P.ι := ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _
  have : PreservesFiniteColimits P.ι :=
    ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _
  have hzero : ∀ {A B C : Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf}
      (a : A ⟶ B) (b : B ⟶ C), P.ι.map a ≫ P.ι.map b = 0 → a ≫ b = 0 := fun a b hab =>
    P.ι.map_injective (by rw [P.ι.map_comp, hab, P.ι.map_zero])
  have hexact : ∀ {A B C : Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf}
      (a : A ⟶ B) (b : B ⟶ C) (hab : a ≫ b = 0),
      (ShortComplex.mk (P.ι.map a) (P.ι.map b) (by rw [← P.ι.map_comp, hab, P.ι.map_zero])).Exact →
        (ShortComplex.mk a b hab).Exact := fun a b hab he =>
    Stacks.SigmaExactness.exact_of_exact_map P.ι (ShortComplex.mk a b hab) he
  exact ⟨{ d₀ := ObjectProperty.homMk H.d₀, d₁ := ObjectProperty.homMk H.d₁
           d₂ := ObjectProperty.homMk H.d₂, d₃ := ObjectProperty.homMk H.d₃
           d₄ := ObjectProperty.homMk H.d₄, d₅ := ObjectProperty.homMk H.d₅
           w₀ := hzero _ _ H.w₀, w₁ := hzero _ _ H.w₁, w₂ := hzero _ _ H.w₂
           w₃ := hzero _ _ H.w₃, w₄ := hzero _ _ H.w₄, w₅ := hzero _ _ H.w₅
           exact₀ := hexact _ _ _ H.exact₀, exact₁ := hexact _ _ _ H.exact₁
           exact₂ := hexact _ _ _ H.exact₂, exact₃ := hexact _ _ _ H.exact₃
           exact₄ := hexact _ _ _ H.exact₄, exact₅ := hexact _ _ _ H.exact₅ }⟩

/-- **The higher direct images along `f` as a cohomological `δ`-functor**: the long exact
sequence of [Stacks, Tag 05TE] for the right derived functors of the direct image, whose
`n`-th functor is `R ⁿ f_*` on the nose. -/
def higherDirectImageDeltaFunctor (f : X ⟶ Y) : DeltaFunctor X.Modules Y.Modules :=
  Stacks.DerivedIndexing.rightDerivedPlusDeltaFunctor (Scheme.Modules.pushforward f)
    (Stacks.DerivedIndexing.derivedDeltaFunctorStructure _)
    (Stacks.DerivedIndexing.canonicalδ _) fun _ _ => rfl

/-- The `n`-th functor of `higherDirectImageDeltaFunctor f` sends `F` to `higherDirectImage f F n`.
-/
@[simp]
theorem higherDirectImageDeltaFunctor_functor_obj (f : X ⟶ Y) (F : X.Modules) (n : ℕ) :
    ((higherDirectImageDeltaFunctor f).functor n).obj F = higherDirectImage f F n :=
  rfl

/-- **The exact hexagon of a short exact sequence of sheaves of modules.** For a short exact
sequence `T` of `𝒪_X`-modules, the even and odd sums of its higher direct images form an exact
hexagon: `higherDirectImageDeltaFunctor` supplies the long exact sequence of the `R ⁱ f_*`, with
`R ⁰ f_* T.X₁ ⟶ R ⁰ f_* T.X₂` a monomorphism, and
`nonempty_exactHexagon_of_longExact` sums it by parity, using that coproducts in a category of
sheaves of modules are exact. -/
theorem nonempty_exactHexagon_higherDirectImage (f : X ⟶ Y) (T : ShortComplex X.Modules)
    (hT : T.ShortExact) :
    Nonempty (ExactHexagon
      (∐ fun i => higherDirectImage f T.X₁ (2 * i))
      (∐ fun i => higherDirectImage f T.X₂ (2 * i))
      (∐ fun i => higherDirectImage f T.X₃ (2 * i))
      (∐ fun i => higherDirectImage f T.X₁ (2 * i + 1))
      (∐ fun i => higherDirectImage f T.X₂ (2 * i + 1))
      (∐ fun i => higherDirectImage f T.X₃ (2 * i + 1))) := by
  let D := higherDirectImageDeltaFunctor f
  exact nonempty_exactHexagon_of_longExact
    (fun n => higherDirectImage f T.X₁ n) (fun n => higherDirectImage f T.X₂ n)
    (fun n => higherDirectImage f T.X₃ n)
    (fun n => (D.functor n).map T.f) (fun n => (D.functor n).map T.g) (fun n => D.δ hT n)
    (fun n => D.map_f_comp_map_g (S := T) n) (fun n => D.map_g_δ hT n)
    (fun n => D.δ_map_f hT n) (fun n => D.exact_map hT n) (fun n => D.exact_δ₁ hT n)
    (fun n => D.exact_δ₂ hT n) (D.mono_map_f hT)

/-- **[Stacks, Tag 0FDL]: the long exact sequence input, proved.** Every short exact sequence of
coherent `𝒪_X`-modules produces the exact hexagon of even and odd sums of higher direct images.

The short exact sequence is pushed into all sheaves of modules along the exact inclusion of the
coherent ones, where `nonempty_exactHexagon_higherDirectImage` builds the hexagon, and
`nonempty_exactHexagon_of_obj` brings it back to the coherent modules.

The image of the sequence under the inclusion is named only by being the subject of
`CategoryTheory.ShortComplex.ShortExact.map_of_exact`, and is passed on as a variable: the
category of coherent modules carries two descriptions of its zero morphisms, so a second,
independent elaboration of that image can be formed over the other one, for which the inclusion
then preserves no zero morphisms. -/
theorem hasParityHexagons (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsProper f] : HasParityHexagons f := by
  intro S hS
  let P : ObjectProperty (SheafOfModules.{u} X.ringCatSheaf) :=
    Stacks.SheafOfModules.coherentModules X.ringCatSheaf
  have : PreservesFiniteLimits P.ι := ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _
  have : PreservesFiniteColimits P.ι :=
    ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _
  obtain ⟨H⟩ := nonempty_exactHexagon_higherDirectImage f _ (hS.map_of_exact P.ι)
  exact nonempty_exactHexagon_of_obj (parityObject f S.X₁ 0) (parityObject f S.X₂ 0)
    (parityObject f S.X₃ 0) (parityObject f S.X₁ 1) (parityObject f S.X₂ 1)
    (parityObject f S.X₃ 1) H

/-- **`ℱ ↦ [E(ℱ)] − [O(ℱ)]` is additive along short exact sequences.** This is the
exact-hexagon identity `ExactHexagon.mk_add_eq` rearranged. -/
theorem parityClass_add_of_shortExact (f : X ⟶ Y) [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [IsProper f]
    (S : ShortComplex (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf))
    (hS : S.ShortExact) :
    parityClass f S.X₂ = parityClass f S.X₁ + parityClass f S.X₃ := by
  obtain ⟨H⟩ := hasParityHexagons f S hS
  simp only [parityClass]
  linear_combination (norm := abel) -(H.mk_add_eq _)

/-- **[Stacks, Tag 0FDL]: proper pushforward on `K'₀`.** For a proper morphism `f : X ⟶ Y` of
locally Noetherian schemes, the homomorphism `f_* : K'₀(X) ⟶ K'₀(Y)` of Grothendieck groups of
coherent sheaves determined by `f_*[ℱ] = [⨁_{i ≥ 0} R ²ⁱ f_* ℱ] − [⨁_{i ≥ 0} R ²ⁱ⁺¹ f_* ℱ]`.

Its existence is `KZero.lift` applied to `parityClass_add_of_shortExact`; the coherence of the
two sums, which is what makes the right-hand side a difference of classes in `K'₀(Y)`, is
`isCoherent_parityDirectImageSum`. -/
@[stacks 0FDL "the map f_* : K'₀(X) ⟶ K'₀(Y). All three of the source's reasons for well \
definedness are proved: coherence of the R ⁱ f_* ℱ (Tag 02O5), local finiteness of the nonzero \
ones, and the long exact sequence of the R ⁱ f_* with its terms collected by the parity of the \
degree (`hasParityHexagons`). The remark's quasi-compact restatement \
f_*[ℱ] = ∑ (-1)ⁱ [R ⁱ f_* ℱ] = [Rf_* ℱ] is \
`AlgebraicGeometry.ProperPushforwardKZero.properPushforward_mk_eq_finsum` and \
`AlgebraicGeometry.ProperPushforwardKZero.properPushforward_mk_eq_derivedClass`",
  sga "6 0 3.1",
  sga "6 X 1.1.8"]
def properPushforward (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsProper f] :
    CoherentKZero X →+ CoherentKZero Y :=
  KZero.lift (parityClass f) (parityClass_add_of_shortExact f)

/-- **[Stacks, Tag 0FDL]: the value of `f_*` on the class of a coherent sheaf.** For coherent
`𝒪_Y`-modules `E` and `O` isomorphic to `⨁_{i ≥ 0} R ²ⁱ f_* ℱ` and `⨁_{i ≥ 0} R ²ⁱ⁺¹ f_* ℱ`,

  `f_*[ℱ] = [E] − [O]`. -/
@[stacks 0FDL "the value f_*[ℱ] = [⨁ R ²ⁱ f_* ℱ] - [⨁ R ²ⁱ⁺¹ f_* ℱ] of f_* on the class of a \
coherent sheaf, the first assertion of the remark"]
theorem properPushforward_mk (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsProper f]
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)
    (E O : Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (hE : E.obj ≅ parityDirectImageSum f F.obj 0)
    (hO : O.obj ≅ parityDirectImageSum f F.obj 1) :
    properPushforward f (KZero.mk _ F) = KZero.mk _ E - KZero.mk _ O := by
  have hE' : E ≅ parityObject f F 0 := (Stacks.SheafOfModules.coherentModules
    Y.ringCatSheaf).ι.preimageIso hE
  have hO' : O ≅ parityObject f F 1 := (Stacks.SheafOfModules.coherentModules
    Y.ringCatSheaf).ι.preimageIso hO
  have hval : properPushforward f (KZero.mk _ F) = parityClass f F :=
    KZero.lift_mk (parityClass f) (parityClass_add_of_shortExact f) F
  rw [hval, parityClass, KZero.mk_eq_of_iso hE', KZero.mk_eq_of_iso hO']

/-- **[Stacks, Tag 0FDL].** For a proper morphism `f : X ⟶ Y` of locally Noetherian schemes there
is exactly one homomorphism `f_* : K'₀(X) ⟶ K'₀(Y)` with

  `f_*[ℱ] = [⨁_{i ≥ 0} R ²ⁱ f_* ℱ] − [⨁_{i ≥ 0} R ²ⁱ⁺¹ f_* ℱ]`

for every coherent `𝒪_X`-module `ℱ`, the two sums being read at any coherent `𝒪_Y`-modules
isomorphic to them. -/
@[stacks 0FDL "the existence and uniqueness of the map f_* : K'₀(X) ⟶ K'₀(Y) with the value the \
remark prescribes on the class of a coherent sheaf"]
theorem existsUnique_properPushforward (f : X ⟶ Y) [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [IsProper f] :
    ∃! φ : CoherentKZero X →+ CoherentKZero Y,
      ∀ (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)
        (E O : Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf),
        (E.obj ≅ parityDirectImageSum f F.obj 0) →
        (O.obj ≅ parityDirectImageSum f F.obj 1) →
          φ (KZero.mk _ F) = KZero.mk _ E - KZero.mk _ O := by
  refine ⟨properPushforward f, properPushforward_mk f, fun φ hφ => ?_⟩
  refine KZero.hom_ext fun F => ?_
  rw [hφ F (parityObject f F 0) (parityObject f F 1) (Iso.refl _) (Iso.refl _),
    properPushforward_mk f F (parityObject f F 0) (parityObject f F 1) (Iso.refl _)
      (Iso.refl _)]

/-- **A quasi-compact target makes the two sums finite.** If `Y` is quasi-compact then
[Stacks, Tag 01XJ] bounds the degrees in which the higher direct images along `f` are nonzero,
uniformly in the coherent module, so each of `⨁_{i ≥ 0} R ²ⁱ f_* ℱ` and
`⨁_{i ≥ 0} R ²ⁱ⁺¹ f_* ℱ` has only finitely many nonzero summands. -/
theorem exists_isZero_higherDirectImage_of_compactSpace (f : X ⟶ Y) [IsProper f]
    [CompactSpace Y] : ∃ N : ℕ, ∀ (F : X.Modules), F.IsCoherent → ∀ i : ℕ, N ≤ i →
      IsZero (higherDirectImage f F i) := by
  obtain ⟨N, hN⟩ :=
    Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerivedNat_pushforward f
  refine ⟨N, fun F hF i hi => ?_⟩
  have : F.IsCoherent := hF
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
    (Scheme.Modules.pushforward f) i F).1 (hN F (isQuasicoherent_of_isCoherent F) i hi)

end AlgebraicGeometry.ProperPushforwardKZero

end
