module

public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroup
public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupProperPushforward
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImageUnconditional
public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Proper pushforward on `K'₀` for a quasi-compact target

Let `f : X ⟶ Y` be a proper morphism of locally Noetherian schemes with `Y` quasi-compact. The
homomorphism `f_* : K'₀(X) ⟶ K'₀(Y)` of
`AlgebraicGeometry.ProperPushforwardKZero.properPushforward` is then the alternating sum of the
higher direct images,

  `f_*[ℱ] = ∑ (−1)ⁱ [R ⁱ f_* ℱ]`,

and, under the identification `K'₀(Y) = K₀(D^b_Coh(𝒪_Y))` of [Stacks, Tag 0FDF], it is the class
of the total derived direct image,

  `f_*[ℱ] = [Rf_* ℱ]`.

This is the second half of [Stacks, Tag 0FDL]; the first half — the map itself and its value
`[⨁ R ²ⁱ f_* ℱ] − [⨁ R ²ⁱ⁺¹ f_* ℱ]` on the class of a coherent sheaf — is
`StacksFrontier/AlgebraicGeometry/Perfect/GrothendieckGroupProperPushforward.lean`.

## Main results

* `AlgebraicGeometry.ProperPushforwardKZero.properPushforward_mk_eq_finsum`: **[Stacks, Tag
  0FDL]**, the identity `f_*[ℱ] = ∑ (−1)ⁱ [R ⁱ f_* ℱ]` for a quasi-compact target.
* `AlgebraicGeometry.ProperPushforwardKZero.properPushforward_mk_eq_derivedClass`,
  `AlgebraicGeometry.ProperPushforwardKZero.exists_addEquiv_properPushforward_eq_derivedClass`:
  **[Stacks, Tag 0FDL]**, the identity `f_*[ℱ] = [Rf_* ℱ]` under the identification
  `K'₀(Y) = K₀(D^b_Coh(𝒪_Y))`.
* `AlgebraicGeometry.ProperPushforwardKZero.derivedCategoryBBounded_derivedPushforward_single`:
  `Rf_*(ℱ[0])` is an object of `D^b_Coh(𝒪_Y)`, from [Stacks, Tag 08E2].

## Implementation notes

**The alternating sum.** With `Y` quasi-compact the higher direct images vanish in all degrees
beyond one bound `N`, uniformly in the coherent module
(`exists_isZero_higherDirectImage_of_compactSpace`), so each of the two parity sums is a *finite*
coproduct: `sigmaFinIsoOfIsZeroTail` identifies `⨁_{i ≥ 0} R ^(2i+r) f_* ℱ` with the coproduct of
its first `N` terms, which is a finite biproduct of coherent sheaves, and the class of a finite
biproduct is the sum of the classes of its factors (`mk_biproduct_sum`, an induction on the index
type over the split short exact sequence of a binary biproduct). Splitting the alternating sum
over `Finset.range (2N)` by the parity of the degree (`alternating_sum_range`) turns
`[E(ℱ)] − [O(ℱ)]` into `∑ (−1)ⁱ [R ⁱ f_* ℱ]`.

**The derived class.** `K'₀(Y) = K₀(D^b_Coh(𝒪_Y))` is [Stacks, Tag 0FDF], here
`AlgebraicGeometry.exists_addEquiv_coherentKZero_K0`, an isomorphism `e` characterised by
`e[𝒢] = [𝒢[0]]`. Its inverse is the Euler characteristic: the zeroth homology functor
`D^b_Coh(𝒪_Y) ⥤ Coh(𝒪_Y)` is homological (`coherentZeroHomologyFunctor_isHomological`), and only
finitely many of its shifts are nonzero on a bounded object, so [Stacks, Tag 0FCR] —
`K0_homomorphism_of_homological` — produces `φ : K₀(D^b_Coh(𝒪_Y)) ⟶ K'₀(Y)` with
`φ[K] = ∑ (−1)ⁱ [H ⁱ(K)]`. On the class of a sheaf placed in degree `0` that sum has the single
term `[𝒢]`, so `φ ∘ e` is the identity; `e` being bijective, `φ` is its inverse and therefore
`e (∑ (−1)ⁱ [H ⁱ(K)]) = [K]` for every `K`. Applied to `K = Rf_*(ℱ[0])`, whose `i`-th cohomology
sheaf is `R ⁱ f_* ℱ`, this turns the alternating sum into `[Rf_* ℱ]`.

**That `Rf_*(ℱ[0])` lies in `D^b_Coh(𝒪_Y)`** is [Stacks, Tag 08E2], in the unconditional form
of the lemma, in the namespace `Stacks.AlgebraicGeometry`,
`ProperSupportCoherent.derivedCategoryBBounded_derivedPushforward_of_properSupp`: the cohomology
sheaves of `ℱ[0]` are `ℱ` and zero, hence coherent, and for a proper `f` every closed subset of
`X` is proper over `Y`, so in particular the supports are.

## References

* [Stacks Project, Tag 0FDL](https://stacks.math.columbia.edu/tag/0FDL)
* [Stacks Project, Tag 0FDF](https://stacks.math.columbia.edu/tag/0FDF)
* [Stacks Project, Tag 0FCR](https://stacks.math.columbia.edu/tag/0FCR)
* [Stacks Project, Tag 08E2](https://stacks.math.columbia.edu/tag/08E2)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v

namespace AlgebraicGeometry.ProperPushforwardKZero

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Classes of biproducts in a Grothendieck group -/

/-- **Any two abelian structures on a category coincide.** The preadditive structure underlying an
abelian structure is unique, and the remaining data of `Abelian` is a proposition. This is used to
identify an abelian structure supplied as an instance argument with the one instance search finds,
so that the additivity of the inclusion of a full subcategory is available. -/
theorem abelian_eq {C : Type*} [Category C] (a b : Abelian C) : a = b := by
  let : Abelian C := a
  let : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  have hp : a.toPreadditive = b.toPreadditive := Subsingleton.elim _ _
  cases a
  cases b
  cases hp
  rfl

/-- The class of a binary biproduct is the sum of the classes of its two factors: the biproduct
is the middle term of a split short exact sequence. -/
theorem mk_biprod {C : Type*} [Category C] [Abelian C] (A B : C) [HasBinaryBiproduct A B] :
    KZero.mk C (A ⊞ B) = KZero.mk C A + KZero.mk C B :=
  KZero.mk_of_splitting (ShortComplex.Splitting.ofHasBinaryBiproduct A B)

/-- A biproduct indexed by the empty type is a zero object. -/
theorem isZero_biproduct_pempty {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasFiniteBiproducts C] (f : PEmpty.{v + 1} → C) : IsZero (⨁ f) := by
  refine ⟨fun Y => ⟨Unique.mk ⟨(0 : (⨁ f) ⟶ Y)⟩ fun g => ?_⟩,
    fun Y => ⟨Unique.mk ⟨(0 : Y ⟶ (⨁ f))⟩ fun g => ?_⟩⟩
  · exact (biproduct.isColimit f).hom_ext fun j => PEmpty.elim j.as
  · exact (biproduct.isLimit f).hom_ext fun j => PEmpty.elim j.as

/-- A biproduct indexed by `Option α` splits off the summand at `none`. -/
def biproductOptionIso {C : Type*} [Category C] [Abelian C] [HasFiniteBiproducts C]
    {α : Type v} [Fintype α] (f : Option α → C) :
    (⨁ f) ≅ f none ⊞ (⨁ fun a : α => f (some a)) := by
  let g : α → C := fun a => f (some a)
  let toMap : (⨁ f) ⟶ f none ⊞ ⨁ g :=
    biproduct.desc fun i => match i with
      | none => biprod.inl
      | some a => biproduct.ι g a ≫ biprod.inr
  let fromMap : f none ⊞ ⨁ g ⟶ ⨁ f :=
    biprod.desc (biproduct.ι f none) (biproduct.desc fun a => biproduct.ι f (some a))
  refine ⟨toMap, fromMap, ?_, ?_⟩
  · refine (biproduct.isColimit f).hom_ext ?_
    rintro ⟨i⟩
    cases i <;> simp [toMap, fromMap, g]
  · refine biprod.ext_from_iff.mpr ⟨by simp [toMap, fromMap, g], ?_⟩
    refine (biproduct.isColimit g).hom_ext ?_
    rintro ⟨i⟩
    simp [toMap, fromMap, g]

/-- **The class of a finite biproduct is the sum of the classes of its factors.** An induction on
the index type, through the empty type and the addition of one element, over `mk_biprod`. -/
theorem mk_biproduct_sum {C : Type*} [Category C] [Abelian C] [HasFiniteBiproducts C]
    (α : Type v) [Fintype α] (f : α → C) : KZero.mk C (⨁ f) = ∑ i, KZero.mk C (f i) := by
  classical
  let P : ∀ (α : Type v) [Fintype α], Prop := fun α _ =>
    ∀ f : α → C, KZero.mk C (⨁ f) = ∑ i, KZero.mk C (f i)
  refine Fintype.induction_empty_option (P := P) ?equiv ?empty ?option α f
  · intro α β _ e h g
    let : Fintype α := Fintype.ofEquiv β e.symm
    calc KZero.mk C (⨁ g) = KZero.mk C (⨁ fun i => g (e i)) :=
          (KZero.mk_eq_of_iso (biproduct.whiskerEquiv e fun i => Iso.refl (g (e i)))).symm
      _ = ∑ i : α, KZero.mk C (g (e i)) := h _
      _ = ∑ i : β, KZero.mk C (g i) := Fintype.sum_equiv e _ _ fun i => rfl
  · intro f
    rw [KZero.mk_eq_zero_of_isZero (isZero_biproduct_pempty f)]
    simp
  · intro α _ h f
    rw [KZero.mk_eq_of_iso (biproductOptionIso f), mk_biprod, h fun a => f (some a)]
    simp

/-- **The class of a coproduct with a vanishing tail.** Let `B` be a weak Serre subcategory of an
abelian category `A` and let `C` be a family of objects of `B`, indexed by `ℕ`, which vanishes in
all degrees `≥ N`. An object of `B` whose underlying object of `A` is the coproduct of the family
has class `∑_{i < N} [C i]`: the coproduct is the coproduct of its first `N` terms by
`sigmaFinIsoOfIsZeroTail`, that is a finite biproduct formed in `B`, and `mk_biproduct_sum`
computes its class. -/
theorem mk_eq_sum_range_of_iso_sigma {A : Type*} [Category A] [Abelian A]
    (B : ObjectProperty A) [B.IsWeakSerreClass] [hA : Abelian B.FullSubcategory]
    (C : ℕ → B.FullSubcategory) [HasCoproduct fun i : ℕ => (C i).obj] (N : ℕ)
    [HasCoproduct fun i : Fin N => (C i.val).obj] (E : B.FullSubcategory)
    (e : E.obj ≅ ∐ fun i : ℕ => (C i).obj) (hz : ∀ i, N ≤ i → IsZero ((C i).obj)) :
    KZero.mk B.FullSubcategory E =
      ∑ i ∈ Finset.range N, KZero.mk B.FullSubcategory (C i) := by
  have hab := abelian_eq hA
    (ObjectProperty.instAbelianFullSubcategoryOfContainsZeroOfIsClosedUnderKernelsOfIsClosedUnderCokernelsOfIsClosedUnderFiniteProducts
      B)
  subst hA
  classical
  let : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  let : HasFiniteBiproducts B.FullSubcategory :=
    Abelian.hasFiniteBiproducts (C := B.FullSubcategory)
  let : PreservesFiniteBiproducts B.ι := Functor.preservesFiniteBiproductsOfAdditive B.ι
  let G : Fin N → B.FullSubcategory := fun i => C i.val
  have hidx : (fun i : Fin N => (C i.val).obj) = B.ι.obj ∘ G := rfl
  let i₂ : (∐ fun i : Fin N => (C i.val).obj) ≅ B.ι.obj (⨁ G) :=
    eqToIso (congrArg (fun F : Fin N → A => ∐ F) hidx) ≪≫
      (biproduct.isoCoproduct (B.ι.obj ∘ G)).symm ≪≫ (B.ι.mapBiproduct G).symm
  calc KZero.mk B.FullSubcategory E = KZero.mk B.FullSubcategory (⨁ G) :=
        KZero.mk_eq_of_iso (ObjectProperty.isoMk B
          (e ≪≫ (sigmaFinIsoOfIsZeroTail (fun i : ℕ => (C i).obj) N hz).symm ≪≫ i₂))
    _ = ∑ i : Fin N, KZero.mk B.FullSubcategory (G i) := mk_biproduct_sum (Fin N) G
    _ = ∑ i ∈ Finset.range N, KZero.mk B.FullSubcategory (C i) :=
        Fin.sum_univ_eq_sum_range (fun i => KZero.mk B.FullSubcategory (C i)) N

/-! ### Finite sums -/

/-- A sum over `ℕ` whose terms vanish from `N` on is the sum over `Finset.range N`. -/
theorem finsum_eq_sum_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) (N : ℕ)
    (h : ∀ n, N ≤ n → g n = 0) : ∑ᶠ n, g n = ∑ n ∈ Finset.range N, g n := by
  refine finsum_eq_sum_of_support_subset _ fun n hn => ?_
  simp only [Function.mem_support] at hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hlt
  exact hn (h n (by omega))

/-- The degrees `0, …, N − 1`, as a subtype of `ℤ` and as a subtype of `ℕ`. -/
def intIccEquivNatRange (N : ℕ) :
    {i : ℤ // i ∈ Finset.Icc (0 : ℤ) ((N : ℤ) - 1)} ≃ {n : ℕ // n ∈ Finset.range N} where
  toFun i := ⟨i.1.toNat, by
    have hi := Finset.mem_Icc.mp i.2
    simp only [Finset.mem_range]
    omega⟩
  invFun n := ⟨(n.1 : ℤ), by
    refine Finset.mem_Icc.mpr ⟨by exact_mod_cast Nat.zero_le n.1, ?_⟩
    have hn := Finset.mem_range.mp n.2
    exact_mod_cast (show (n.1 : ℤ) ≤ (N : ℤ) - 1 by omega)⟩
  left_inv i := Subtype.ext (Int.toNat_of_nonneg (Finset.mem_Icc.mp i.2).1)
  right_inv n := Subtype.ext rfl

/-- A sum over `ℤ` whose terms vanish in negative degrees and from `N` on is the sum of its
restriction to `ℕ`. -/
theorem finsum_int_eq_nat_of_bounds {M : Type*} [AddCommMonoid M] (g : ℤ → M) (N : ℕ)
    (hneg : ∀ i, i < 0 → g i = 0) (hhigh : ∀ i, (N : ℤ) ≤ i → g i = 0) :
    ∑ᶠ i : ℤ, g i = ∑ᶠ n : ℕ, g n := by
  classical
  have hs : ∑ᶠ i : ℤ, g i = ∑ i ∈ Finset.Icc (0 : ℤ) ((N : ℤ) - 1), g i := by
    refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
    simp only [Function.mem_support] at hi
    simp only [Finset.mem_coe, Finset.mem_Icc]
    refine ⟨by by_contra hnot; exact hi (hneg i (by omega)), ?_⟩
    by_contra hnot
    exact hi (hhigh i (by omega))
  have hn : ∑ᶠ n : ℕ, g n = ∑ n ∈ Finset.range N, g n :=
    finsum_eq_sum_range (fun n => g (n : ℤ)) N fun n hn => hhigh n (by exact_mod_cast hn)
  have heq : (∑ i ∈ Finset.Icc (0 : ℤ) ((N : ℤ) - 1), g i) = ∑ n ∈ Finset.range N, g (n : ℤ) :=
    calc _ = ∑ i : {i : ℤ // i ∈ Finset.Icc (0 : ℤ) ((N : ℤ) - 1)}, g i :=
          (Finset.sum_attach (Finset.Icc (0 : ℤ) ((N : ℤ) - 1)) fun i => g i).symm
      _ = ∑ n : {n : ℕ // n ∈ Finset.range N}, g (n : ℤ) :=
          Fintype.sum_equiv (intIccEquivNatRange N) _ _ fun i =>
            congrArg g (Int.toNat_of_nonneg (Finset.mem_Icc.mp i.2).1).symm
      _ = _ := Finset.sum_attach (Finset.range N) fun n => g (n : ℤ)
  exact hs.trans (heq.trans hn.symm)

/-- **Splitting an alternating sum by parity.** The alternating sum over the first `2N` degrees is
the sum of the even terms minus the sum of the odd ones. -/
theorem alternating_sum_range {M : Type*} [AddCommGroup M] (g : ℕ → M) (N : ℕ) :
    (∑ n ∈ Finset.range (2 * N), (((n : ℤ).negOnePow : ℤ) • g n)) =
      (∑ n ∈ Finset.range N, g (2 * n)) - ∑ n ∈ Finset.range N, g (2 * n + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hEven : ((((2 * N : ℕ) : ℤ).negOnePow : ℤ)) = 1 := by
      show (((2 * (N : ℤ)).negOnePow : ℤ)) = 1
      simp [Int.negOnePow_two_mul]
    have hOdd : ((((2 * N + 1 : ℕ) : ℤ).negOnePow : ℤ)) = -1 := by
      show (((2 * (N : ℤ) + 1).negOnePow : ℤ)) = -1
      simp [Int.negOnePow_two_mul_add_one]
    have hL : (∑ n ∈ Finset.range (2 * (N + 1)), (((n : ℤ).negOnePow : ℤ) • g n)) =
        (∑ n ∈ Finset.range (2 * N), (((n : ℤ).negOnePow : ℤ) • g n)) +
          (((2 * N : ℕ) : ℤ).negOnePow : ℤ) • g (2 * N) +
            (((2 * N + 1 : ℕ) : ℤ).negOnePow : ℤ) • g (2 * N + 1) := by
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega, Finset.sum_range_succ,
        show 2 * N + 1 = (2 * N) + 1 by omega, Finset.sum_range_succ]
    rw [hL, ih, Finset.sum_range_succ (fun n => g (2 * n)),
      Finset.sum_range_succ fun n => g (2 * n + 1)]
    simp only [hEven, hOdd, one_smul, neg_smul]
    abel

/-! ### The alternating sum of the higher direct images -/

/-- A term of an alternating sum vanishes when the underlying object is zero. -/
private theorem negOnePow_smul_mk_eq_zero_of_isZero {A : Type*} [Category A] [Abelian A]
    (B : ObjectProperty A) [B.IsWeakSerreClass] [Abelian B.FullSubcategory] (n : ℤ)
    (G : B.FullSubcategory) (h : IsZero G.obj) :
    (n.negOnePow : ℤ) • KZero.mk B.FullSubcategory G = 0 := by
  rw [KZero.mk_eq_zero_of_isZero (IsZero.of_full_of_faithful_of_isZero B.ι _ h), smul_zero]

variable {X Y : Scheme.{u}}

/-- **[Stacks, Tag 0FDL]: the quasi-compact restatement `f_*[ℱ] = ∑ (−1)ⁱ [R ⁱ f_* ℱ]`.** For a
proper morphism `f : X ⟶ Y` of locally Noetherian schemes with `Y` quasi-compact, the proper
pushforward of the class of a coherent `𝒪_X`-module is the alternating sum of the classes of its
higher direct images; the sum is finite because they vanish in all large degrees.

The value of `f_*` on `[ℱ]` is `[⨁_{i ≥ 0} R ²ⁱ f_* ℱ] − [⨁_{i ≥ 0} R ²ⁱ⁺¹ f_* ℱ]`
(`properPushforward_mk`); each of the two sums has only finitely many nonzero summands by
`exists_isZero_higherDirectImage_of_compactSpace`, so `mk_eq_sum_range_of_iso_sigma` expands its
class as a finite sum, and `alternating_sum_range` recombines the two finite sums by parity. -/
@[stacks 0FDL "the quasi-compact restatement f_*[ℱ] = ∑ (-1)ⁱ [R ⁱ f_* ℱ] of the remark"]
theorem properPushforward_mk_eq_finsum (f : X ⟶ Y) [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [IsProper f] [CompactSpace Y]
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :
    properPushforward f (KZero.mk _ F) =
      ∑ᶠ i : ℕ, ((i : ℤ).negOnePow : ℤ) • KZero.mk _ (coherentHigherDirectImage f F i) := by
  obtain ⟨N, hN⟩ := exists_isZero_higherDirectImage_of_compactSpace f
  have hvanish : ∀ i : ℕ, N ≤ i → IsZero (higherDirectImage f F.obj i) :=
    hN F.obj (CoherentAbelian.isCoherent_of_stacksIsCoherent F.property)
  have hparity : ∀ r : ℕ, KZero.mk _ (parityObject f F r) =
      ∑ i ∈ Finset.range N, KZero.mk _ (coherentHigherDirectImage f F (2 * i + r)) := fun r =>
    mk_eq_sum_range_of_iso_sigma (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf)
      (fun i => coherentHigherDirectImage f F (2 * i + r)) N (parityObject f F r)
      (Iso.refl _) fun i hi => hvanish (2 * i + r) (by omega)
  have hterm : ∀ i : ℕ, N ≤ i →
      ((i : ℤ).negOnePow : ℤ) • KZero.mk _ (coherentHigherDirectImage f F i) = 0 := fun i hi =>
    negOnePow_smul_mk_eq_zero_of_isZero _ _ _ (hvanish i hi)
  calc properPushforward f (KZero.mk _ F)
      = KZero.mk _ (parityObject f F 0) - KZero.mk _ (parityObject f F 1) :=
        properPushforward_mk f F _ _ (Iso.refl _) (Iso.refl _)
    _ = (∑ i ∈ Finset.range N, KZero.mk _ (coherentHigherDirectImage f F (2 * i + 0))) -
          ∑ i ∈ Finset.range N, KZero.mk _ (coherentHigherDirectImage f F (2 * i + 1)) := by
        rw [hparity 0, hparity 1]
    _ = ∑ n ∈ Finset.range (2 * N),
          ((n : ℤ).negOnePow : ℤ) • KZero.mk _ (coherentHigherDirectImage f F n) := by
        rw [alternating_sum_range
          (fun n => KZero.mk _ (coherentHigherDirectImage f F n)) N]
        simp
    _ = ∑ᶠ i : ℕ, ((i : ℤ).negOnePow : ℤ) • KZero.mk _ (coherentHigherDirectImage f F i) :=
        (finsum_eq_sum_range _ (2 * N) fun n hn => hterm n (by omega)).symm

/-! ### The zeroth homology functor of `D^b_B(A)` and its Euler characteristic -/

section Euler

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  (B : ObjectProperty A) (P : ObjectProperty (DerivedCategory A))

/-- The zeroth homology functor `D^b_B(A) ⥤ B`, for a subcategory `P` of `D(A)` all of whose
objects have their zeroth homology in `B`. -/
def coherentZeroHomologyFunctor
    (hB : ∀ E : P.FullSubcategory, B ((DerivedCategory.homologyFunctor A 0).obj E.obj)) :
    P.FullSubcategory ⥤ B.FullSubcategory :=
  ObjectProperty.lift B (P.ι ⋙ DerivedCategory.homologyFunctor A 0) hB

/-- On the `n`-th shift of an object of `P`, the zeroth homology functor is the `n`-th homology of
that object. -/
def coherentZeroHomologyFunctorShiftIso [P.IsTriangulated]
    (hB : ∀ E : P.FullSubcategory, B ((DerivedCategory.homologyFunctor A 0).obj E.obj))
    (E : P.FullSubcategory) (n : ℤ) :
    B.ι.obj ((coherentZeroHomologyFunctor B P hB).obj
        ((shiftFunctor P.FullSubcategory n).obj E)) ≅
      (DerivedCategory.homologyFunctor A n).obj E.obj := by
  change (DerivedCategory.homologyFunctor A 0).obj
      (P.ι.obj ((shiftFunctor P.FullSubcategory n).obj E)) ≅ _
  calc _ ≅ (DerivedCategory.homologyFunctor A 0).obj
        ((shiftFunctor (DerivedCategory A) n).obj E.obj) :=
      (DerivedCategory.homologyFunctor A 0).mapIso ((P.ι.commShiftIso n).app E)
    _ ≅ ((DerivedCategory.homologyFunctor A 0).shift n).obj E.obj :=
      ((DerivedCategory.homologyFunctor A 0).isoShift n).app E.obj
    _ = (DerivedCategory.homologyFunctor A n).obj E.obj := by
      rw [DerivedCategory.shift_homologyFunctor]

/-- The zeroth homology functor vanishes on the `n`-th shift of an object whose `n`-th homology
vanishes. -/
theorem isZero_coherentZeroHomologyFunctor_obj_shift [P.IsTriangulated]
    (hB : ∀ E : P.FullSubcategory, B ((DerivedCategory.homologyFunctor A 0).obj E.obj))
    (E : P.FullSubcategory) (n : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor A n).obj E.obj)) :
    IsZero ((coherentZeroHomologyFunctor B P hB).obj
      ((shiftFunctor P.FullSubcategory n).obj E)) :=
  IsZero.of_full_of_faithful_of_isZero B.ι _
    (IsZero.of_iso h (coherentZeroHomologyFunctorShiftIso B P hB E n))

/-- **The zeroth homology functor `D^b_B(A) ⥤ B` is homological.** Composed with the inclusion of
`B` it is the composite of the triangulated inclusion of `P` with the homological functor `H ⁰` of
`D(A)`, hence homological; and the inclusion of `B` is exact and faithful, so it reflects the
exactness of a short complex. -/
theorem coherentZeroHomologyFunctor_isHomological [B.IsWeakSerreClass]
    [hA : Abelian B.FullSubcategory] [P.IsTriangulated]
    (hB : ∀ E : P.FullSubcategory, B ((DerivedCategory.homologyFunctor A 0).obj E.obj)) :
    (coherentZeroHomologyFunctor B P hB).IsHomological := by
  have hab := abelian_eq hA
    (ObjectProperty.instAbelianFullSubcategoryOfContainsZeroOfIsClosedUnderKernelsOfIsClosedUnderCokernelsOfIsClosedUnderFiniteProducts
      B)
  subst hA
  classical
  let H := coherentZeroHomologyFunctor B P hB
  have : H.PreservesZeroMorphisms := by
    refine ⟨fun X Y => ?_⟩
    apply ObjectProperty.hom_ext
    show (P.ι ⋙ DerivedCategory.homologyFunctor A 0).map (0 : X ⟶ Y) = 0
    simp
  have : PreservesFiniteLimits B.ι := B.preservesFiniteLimits_ι_of_isWeakSerreClass
  have : PreservesFiniteColimits B.ι := B.preservesFiniteColimits_ι_of_isWeakSerreClass
  have : B.ι.PreservesHomology := Functor.preservesHomologyOfExact B.ι
  have hIncl : (H ⋙ B.ι).IsHomological := by
    have : (P.ι ⋙ DerivedCategory.homologyFunctor A 0).IsHomological := inferInstance
    exact Functor.IsHomological.of_iso
      (ObjectProperty.liftCompιIso B (P.ι ⋙ DerivedCategory.homologyFunctor A 0) hB).symm
  refine Functor.IsHomological.mk' H fun T hT => ⟨T, Iso.refl _, ?_⟩
  let S := Pretriangulated.shortComplexOfDistTriangle T hT
  have hS : ((S.map H).map B.ι).Exact := by
    simpa [S] using (Functor.IsHomological.exact T hT : (S.map (H ⋙ B.ι)).Exact)
  exact ((S.map H).exact_map_iff_of_faithful B.ι).mp hS

/-- **The Euler characteristic of [Stacks, Tag 0FCR] for the zeroth homology functor** is the
alternating sum of the classes of the homology objects. -/
theorem coherentEulerClass_eq_homologyFinsum [P.IsTriangulated] [B.IsWeakSerreClass]
    [Abelian B.FullSubcategory]
    (hB : ∀ E : P.FullSubcategory, B ((DerivedCategory.homologyFunctor A 0).obj E.obj))
    (E : P.FullSubcategory)
    (hE : ∀ i : ℤ, B ((DerivedCategory.homologyFunctor A i).obj E.obj)) :
    _root_.eulerClass P.FullSubcategory B.FullSubcategory
        (coherentZeroHomologyFunctor B P hB) E =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • KZero.mk B.FullSubcategory
        ⟨(DerivedCategory.homologyFunctor A i).obj E.obj, hE i⟩ := by
  classical
  unfold _root_.eulerClass
  refine finsum_congr fun i => ?_
  have hIso : ((coherentZeroHomologyFunctor B P hB).obj
      ((shiftFunctor P.FullSubcategory i).obj E)).obj ≅
      (⟨(DerivedCategory.homologyFunctor A i).obj E.obj, hE i⟩ : B.FullSubcategory).obj :=
    coherentZeroHomologyFunctorShiftIso B P hB E i
  rw [KZero.mk_eq_of_iso (ObjectProperty.isoMk B hIso),
    show (i.negOnePow : ℤ) = (-1 : ℤ) ^ i.natAbs by cases i <;> rfl]

/-- The homology of an object that is both `≥ 0` and `≤ 0` vanishes outside degree zero. -/
private theorem isZero_homologyFunctor_obj_of_isGE_of_isLE (K : DerivedCategory A)
    [K.IsGE 0] [K.IsLE 0] (j : ℤ) (hj : j ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor A j).obj K) := by
  rcases hj.lt_or_gt with h | h
  · exact DerivedCategory.isZero_of_isGE _ 0 j h
  · exact DerivedCategory.isZero_of_isLE _ 0 j h

/-- **The Euler characteristic of a sheaf placed in degree zero is its class.** All but the
zeroth homology of such an object vanish. -/
theorem coherentEulerClass_eq_mk_of_iso_single [P.IsTriangulated] [B.IsWeakSerreClass]
    [Abelian B.FullSubcategory]
    (hB : ∀ E : P.FullSubcategory, B ((DerivedCategory.homologyFunctor A 0).obj E.obj))
    (E : P.FullSubcategory) (G : B.FullSubcategory)
    (e : E.obj ≅ (DerivedCategory.singleFunctor A 0).obj G.obj) :
    _root_.eulerClass P.FullSubcategory B.FullSubcategory
      (coherentZeroHomologyFunctor B P hB) E = KZero.mk _ G := by
  classical
  have : ((DerivedCategory.singleFunctor A (0 : ℤ)).obj G.obj).IsGE 0 := inferInstance
  have : ((DerivedCategory.singleFunctor A (0 : ℤ)).obj G.obj).IsLE 0 := inferInstance
  have hGE : E.obj.IsGE 0 := DerivedCategory.TStructure.t.isGE_of_iso e.symm 0
  have hLE : E.obj.IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso e.symm 0
  have hz : ∀ i : ℤ, i ≠ 0 → IsZero ((coherentZeroHomologyFunctor B P hB).obj
      ((shiftFunctor P.FullSubcategory i).obj E)) := by
    intro i hi
    exact isZero_coherentZeroHomologyFunctor_obj_shift B P hB E i
      (isZero_homologyFunctor_obj_of_isGE_of_isLE E.obj i hi)
  have h0 : B.ι.obj ((coherentZeroHomologyFunctor B P hB).obj
      ((shiftFunctor P.FullSubcategory (0 : ℤ)).obj E)) ≅ G.obj :=
    coherentZeroHomologyFunctorShiftIso B P hB E (0 : ℤ) ≪≫
      (DerivedCategory.homologyFunctor A 0).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app G.obj
  calc _ = ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • KZero.mk B.FullSubcategory
          ((coherentZeroHomologyFunctor B P hB).obj
            ((shiftFunctor P.FullSubcategory i).obj E)) := by
        unfold _root_.eulerClass
        refine finsum_congr fun i => ?_
        cases i <;> simp [Int.negOnePow]
    _ = KZero.mk B.FullSubcategory ((coherentZeroHomologyFunctor B P hB).obj
          ((shiftFunctor P.FullSubcategory (0 : ℤ)).obj E)) := by
        rw [finsum_eq_single (fun i : ℤ => (i.negOnePow : ℤ) • KZero.mk B.FullSubcategory
            ((coherentZeroHomologyFunctor B P hB).obj
              ((shiftFunctor P.FullSubcategory i).obj E))) 0 fun i hi => by
          rw [KZero.mk_eq_zero_of_isZero (hz i hi), smul_zero]]
        simp
    _ = KZero.mk B.FullSubcategory G := KZero.mk_eq_of_iso (ObjectProperty.isoMk B h0)

/-- **The identification `K₀(B) = K₀(D^b_B(A))` of [Stacks, Tag 0FCS] inverts the Euler
characteristic.** Let `e` be an isomorphism from the Grothendieck group of `B` to the zeroth
`K`-group of a triangulated subcategory `P` of `D(A)` whose objects have bounded homology in `B`,
and assume that `e` sends the class of an object of `B` to the class of that object placed in
degree `0`, every object of `B` having such a representative in `P`. Then `e` takes the
alternating sum `∑ (−1)ⁱ [H ⁱ(K)]` to `[K]`, for every object `K` of `P`.

The alternating sum is the Euler characteristic of the zeroth homology functor, so
[Stacks, Tag 0FCR] produces a homomorphism `φ : K₀(P) ⟶ K₀(B)` computing it. On the class of an
object of `B` placed in degree `0` the alternating sum has the single term that object, so
`φ ∘ e` agrees with the identity on the classes of objects, hence is the identity; `e` being
bijective, `φ` is its inverse. -/
theorem addEquiv_eulerClass_eq_cls [B.IsWeakSerreClass] [Abelian B.FullSubcategory]
    [P.IsTriangulated]
    (hBmem : ∀ E : P.FullSubcategory, B ((DerivedCategory.homologyFunctor A 0).obj E.obj))
    (hbdd : ∀ E : P.FullSubcategory, ∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor A i).obj E.obj))
    (e : KZero B.FullSubcategory ≃+ Pretriangulated.K0 P.FullSubcategory)
    (hexists : ∀ G : B.FullSubcategory, ∃ D : P.FullSubcategory,
      Nonempty (D.obj ≅ (DerivedCategory.singleFunctor A 0).obj G.obj))
    (hchar : ∀ (G : B.FullSubcategory) (D : P.FullSubcategory),
      (D.obj ≅ (DerivedCategory.singleFunctor A 0).obj G.obj) →
        e (KZero.mk B.FullSubcategory G) = Pretriangulated.K0.cls D)
    (E : P.FullSubcategory) :
    e (_root_.eulerClass P.FullSubcategory B.FullSubcategory
        (coherentZeroHomologyFunctor B P hBmem) E) = Pretriangulated.K0.cls E := by
  classical
  have hfinite : ∀ E : P.FullSubcategory,
      {i : ℤ | ¬ IsZero ((coherentZeroHomologyFunctor B P hBmem).obj
        ((shiftFunctor P.FullSubcategory i).obj E))}.Finite := by
    intro E
    obtain ⟨a, b, hab⟩ := hbdd E
    refine Set.Finite.subset (Set.finite_Icc a b) fun i hi => ?_
    simp only [Set.mem_ofPred_eq] at hi
    by_contra hnot
    have hnot' : ¬ (a ≤ i ∧ i ≤ b) := by simpa only [Set.mem_Icc] using hnot
    exact hi (isZero_coherentZeroHomologyFunctor_obj_shift B P hBmem E i (hab i (by omega)))
  obtain ⟨φ, hφ⟩ := K0_homomorphism_of_homological (D := P.FullSubcategory)
    (A := B.FullSubcategory) (coherentZeroHomologyFunctor B P hBmem)
    (coherentZeroHomologyFunctor_isHomological B P hBmem) hfinite
  have hcomp : ∀ x : KZero B.FullSubcategory, φ (e x) = x := by
    have hc : φ.comp e.toAddMonoidHom = AddMonoidHom.id (KZero B.FullSubcategory) := by
      refine KZero.hom_ext fun G => ?_
      obtain ⟨D0, ⟨iso⟩⟩ := hexists G
      calc φ (e (KZero.mk B.FullSubcategory G)) = φ (Pretriangulated.K0.cls D0) := by
            rw [hchar G D0 iso]
        _ = _root_.eulerClass P.FullSubcategory B.FullSubcategory
              (coherentZeroHomologyFunctor B P hBmem) D0 := hφ D0
        _ = KZero.mk B.FullSubcategory G :=
            coherentEulerClass_eq_mk_of_iso_single B P hBmem D0 G iso
    intro x
    exact DFunLike.congr_fun hc x
  obtain ⟨x, hx⟩ := e.surjective (Pretriangulated.K0.cls E)
  rw [← hφ E, ← hx, hcomp x]

/-- All but the zeroth homology of an object placed in degree zero vanish. -/
theorem isZero_homologyFunctor_obj_singleFunctor_obj (M : A) (j : ℤ) (hj : j ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor A j).obj
      ((DerivedCategory.singleFunctor A 0).obj M)) := by
  exact isZero_homologyFunctor_obj_of_isGE_of_isLE _ j hj

/-- The homology of an object of `D^b_B(A)` vanishes outside a bounded range of degrees. -/
theorem exists_isZero_homology_of_derivedCategoryBBounded
    (E : (DerivedCategoryB.derivedCategoryBBounded B).FullSubcategory) :
    ∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor A i).obj E.obj) := by
  obtain ⟨a, ha⟩ := E.property.1.1
  obtain ⟨b, hb⟩ := E.property.1.2
  exact ⟨a, b, fun i hi => hi.elim (ha i) (hb i)⟩

end Euler

/-! ### The class of the total derived direct image -/

variable {X Y : Scheme.{u}}

/-- **[Stacks, Tag 08E2] for a coherent sheaf placed in degree zero.** For a proper morphism
`f : X ⟶ Y` to a Noetherian scheme and a coherent `𝒪_X`-module `ℱ`, the total derived direct
image `Rf_*(ℱ[0])` is an object of `D^b_Coh(𝒪_Y)`.

The cohomology sheaves of `ℱ[0]` are `ℱ` in degree `0` and zero elsewhere, hence coherent, and
every closed subset of the source of a proper morphism is proper over the target, so
[Stacks, Tag 08E2] — `derivedCategoryBBounded_derivedPushforward_of_properSupp` — applies. -/
@[sga "6 0 3.1" "partial", sga "6 III 2.2.1" "special case", sga "6 IV 2.11.1" "special case"]
theorem derivedCategoryBBounded_derivedPushforward_single (f : X ⟶ Y) [IsLocallyNoetherian Y]
    [IsProper f] [CompactSpace Y] (F : X.Modules) [F.IsCoherent] :
    DerivedCategoryB.derivedCategoryBBounded (fun N : Y.Modules => N.IsCoherent)
      ((derivedPushforwardModules f).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F)) := by
  have : IsNoetherian Y := IsNoetherian.mk
  have hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj F)).IsCoherent := by
    intro j
    rcases eq_or_ne j 0 with rfl | hj
    · have e : (DerivedCategory.homologyFunctor X.Modules 0).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≅ F :=
        (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app F
      exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso (R := X.ringCatSheaf) e
    · exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero
        (R := X.ringCatSheaf) (isZero_homologyFunctor_obj_singleFunctor_obj F j hj)
  refine Stacks.AlgebraicGeometry.ProperSupportCoherent.derivedCategoryBBounded_derivedPushforward_of_properSupp
    f _ hcoh (fun j => ?_) 0 0 inferInstance inferInstance
  show IsProper ((Scheme.IdealSheafData.vanishingIdeal _).subschemeι ≫ f)
  infer_instance

/-- **[Stacks, Tag 08E2] for a coherent sheaf placed in degree zero**, at the spelling of
coherence that `AlgebraicGeometry.CoherentKZero` is formed over. -/
theorem derivedCategoryBBounded_derivedPushforward_single_coherentModules (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [IsProper f] [CompactSpace Y] (F : X.Modules) [F.IsCoherent] :
    DerivedCategoryB.derivedCategoryBBounded
        (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf)
      ((derivedPushforwardModules f).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F)) := by
  obtain ⟨hb, hc⟩ := derivedCategoryBBounded_derivedPushforward_single f F
  exact ⟨hb, fun n => CoherentAbelian.stacksIsCoherent_of_isCoherent (hc n)⟩

/-- **The higher direct images vanish in all large integer degrees.** For a proper `f` to a
quasi-compact target there is one bound `N` with `R ⁱ f_* ℱ = 0` for every coherent `ℱ` and every
integer `i ≥ N`. -/
theorem exists_isZero_rightDerivedPlus_of_compactSpace (f : X ⟶ Y) [IsProper f]
    [CompactSpace Y] : ∃ N : ℕ, ∀ F : X.Modules, F.IsCoherent → ∀ i : ℤ, (N : ℤ) ≤ i →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F) := by
  obtain ⟨N, hN⟩ := exists_isZero_higherDirectImage_of_compactSpace f
  refine ⟨N, fun F hF i hi => ?_⟩
  have h : IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus
      ((i.toNat : ℕ) : ℤ)).obj F) := hN F hF i.toNat (by omega)
  rwa [show ((i.toNat : ℤ)) = i from Int.toNat_of_nonneg (by omega)] at h

/-- **`f_*[ℱ]` is the class of any object with the cohomology sheaves of `Rf_* ℱ`.** Under an
identification `K'₀(Y) = K₀(D^b_Coh(𝒪_Y))` sending the class of a coherent sheaf to the class of
that sheaf placed in degree `0`, the class `f_*[ℱ]` is the class of every object `D` of
`D^b_Coh(𝒪_Y)` whose `i`-th cohomology sheaf is `R ⁱ f_* ℱ` for all `i`. -/
theorem properPushforward_mk_eq_cls_of_homology_iso (f : X ⟶ Y) [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [IsProper f] [CompactSpace Y]
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)
    (D : (DerivedCategoryB.derivedCategoryBBounded
        (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf)).FullSubcategory)
    (hD : ∀ i : ℤ, Nonempty ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} Y.ringCatSheaf) i).obj D.obj ≅
      ((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F.obj))
    (e : CoherentKZero Y ≃+ Pretriangulated.K0 (DerivedCategoryB.derivedCategoryBBounded
        (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf)).FullSubcategory)
    (he : ∀ (G : Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf)
        (D' : (DerivedCategoryB.derivedCategoryBBounded
          (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf)).FullSubcategory),
        (D'.obj ≅ (DerivedCategory.singleFunctor
          (SheafOfModules.{u} Y.ringCatSheaf) 0).obj G.obj) →
          e (KZero.mk _ G) = Pretriangulated.K0.cls D') :
    e (properPushforward f (KZero.mk _ F)) = Pretriangulated.K0.cls D := by
  classical
  have hFcoh : F.obj.IsCoherent := CoherentAbelian.isCoherent_of_stacksIsCoherent F.property
  obtain ⟨-, hexists, -⟩ := exists_addEquiv_coherentKZero_K0 Y
  obtain ⟨N, hN⟩ := exists_isZero_rightDerivedPlus_of_compactSpace f
  have hBmem : ∀ E : (DerivedCategoryB.derivedCategoryBBounded
        (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf)).FullSubcategory,
      Stacks.SheafOfModules.coherentModules Y.ringCatSheaf
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} Y.ringCatSheaf) 0).obj E.obj) :=
    fun E => E.property.2 0
  have hiso : ∀ i : ℤ, (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} Y.ringCatSheaf) i).obj D.obj ≅
      ((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F.obj := fun i => (hD i).some
  have hzero : ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} Y.ringCatSheaf) i).obj D.obj) →
      ((i.negOnePow : ℤ) • KZero.mk
        (Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf)
        ⟨(DerivedCategory.homologyFunctor (SheafOfModules.{u} Y.ringCatSheaf) i).obj D.obj,
          D.property.2 i⟩) = 0 := by
    intro i h
    exact negOnePow_smul_mk_eq_zero_of_isZero _ _ _ h
  have heuler : _root_.eulerClass _ (Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf)
      (coherentZeroHomologyFunctor _ _ hBmem) D =
      ∑ᶠ i : ℕ, ((i : ℤ).negOnePow : ℤ) •
        KZero.mk _ (coherentHigherDirectImage f F i) := by
    refine (coherentEulerClass_eq_homologyFinsum _ _ hBmem D fun i => D.property.2 i).trans ?_
    refine (finsum_int_eq_nat_of_bounds _ N (fun i hi => hzero i ?_)
      fun i hi => hzero i ?_).trans (finsum_congr fun i => ?_)
    · exact IsZero.of_iso
        (Stacks.AlgebraicGeometry.HigherDirectImage.isZero_higherDirectImage_of_neg
          f F.obj i hi) (hiso i)
    · exact IsZero.of_iso (hN F.obj hFcoh i hi) (hiso i)
    · exact congrArg (fun z => (((i : ℤ)).negOnePow : ℤ) • z)
        (KZero.mk_eq_of_iso (ObjectProperty.isoMk _ (hiso (i : ℤ))))
  rw [properPushforward_mk_eq_finsum f F, ← heuler]
  exact addEquiv_eulerClass_eq_cls _ _ hBmem
    (exists_isZero_homology_of_derivedCategoryBBounded _) e hexists he D

/-- **[Stacks, Tag 0FDL]: the quasi-compact restatement `f_*[ℱ] = [Rf_* ℱ]`.** For a proper
morphism `f : X ⟶ Y` of locally Noetherian schemes with `Y` quasi-compact and a coherent
`𝒪_X`-module `ℱ`, the total derived direct image `Rf_*(ℱ[0])` is an object of `D^b_Coh(𝒪_Y)`, and
under every identification `K'₀(Y) = K₀(D^b_Coh(𝒪_Y))` which sends the class of a coherent sheaf
to the class of that sheaf placed in degree `0` — the identification of [Stacks, Tag 0FDF] —
the class `f_*[ℱ]` is the class of `Rf_*(ℱ[0])`.

The identity `f_*[ℱ] = ∑ (−1)ⁱ [R ⁱ f_* ℱ]` is `properPushforward_mk_eq_finsum`, and
`∑ (−1)ⁱ [H ⁱ(K)] ↦ [K]` is the inverse of the identification: the homomorphism `φ` of
[Stacks, Tag 0FCR] for the zeroth homology functor takes `[K]` to `∑ (−1)ⁱ [H ⁱ(K)]`, and the
composite of the identification with `φ` is the identity on the classes of coherent sheaves,
hence the identity. -/
@[stacks 0FDL "the quasi-compact restatement f_*[ℱ] = [Rf_* ℱ] of the remark, under the \
identification K'₀(Y) = K₀(D^b_Coh(𝒪_Y)) of Tag 0FDF"]
theorem properPushforward_mk_eq_derivedClass (f : X ⟶ Y) [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [IsProper f] [CompactSpace Y]
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :
    ∃ E : (DerivedCategoryB.derivedCategoryBBounded
        (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf)).FullSubcategory,
      Nonempty (E.obj ≅ (derivedPushforwardModules f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F.obj)) ∧
        ∀ e : CoherentKZero Y ≃+ Pretriangulated.K0 (DerivedCategoryB.derivedCategoryBBounded
            (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf)).FullSubcategory,
          (∀ (G : Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf)
              (D : (DerivedCategoryB.derivedCategoryBBounded
                (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf)).FullSubcategory),
              (D.obj ≅ (DerivedCategory.singleFunctor
                (SheafOfModules.{u} Y.ringCatSheaf) 0).obj G.obj) →
                e (KZero.mk _ G) = Pretriangulated.K0.cls D) →
            e (properPushforward f (KZero.mk _ F)) = Pretriangulated.K0.cls E := by
  have : F.obj.IsCoherent := CoherentAbelian.isCoherent_of_stacksIsCoherent F.property
  exact ⟨⟨_, derivedCategoryBBounded_derivedPushforward_single_coherentModules f F.obj⟩,
    ⟨Iso.refl _⟩, properPushforward_mk_eq_cls_of_homology_iso f F _ fun i =>
    Stacks.AlgebraicGeometry.ProperSupportCoherent.nonempty_homology_derivedPushforward_single_zero
      f F.obj i⟩

/-- **[Stacks, Tag 0FDL]: the quasi-compact restatement `f_*[ℱ] = [Rf_* ℱ]`**, with the
identification `K'₀(Y) = K₀(D^b_Coh(𝒪_Y))` of [Stacks, Tag 0FDF] exhibited. -/
@[stacks 0FDL "the quasi-compact restatement f_*[ℱ] = [Rf_* ℱ] of the remark, with the \
identification K'₀(Y) = K₀(D^b_Coh(𝒪_Y)) of Tag 0FDF exhibited"]
theorem exists_addEquiv_properPushforward_eq_derivedClass (f : X ⟶ Y) [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [IsProper f] [CompactSpace Y] :
    ∃ e : CoherentKZero Y ≃+ Pretriangulated.K0 (DerivedCategoryB.derivedCategoryBBounded
        (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf)).FullSubcategory,
      (∀ (G : Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf)
          (D : (DerivedCategoryB.derivedCategoryBBounded
            (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf)).FullSubcategory),
          (D.obj ≅ (DerivedCategory.singleFunctor
            (SheafOfModules.{u} Y.ringCatSheaf) 0).obj G.obj) →
            e (KZero.mk _ G) = Pretriangulated.K0.cls D) ∧
        ∀ F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf,
          ∃ E : (DerivedCategoryB.derivedCategoryBBounded
              (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf)).FullSubcategory,
            Nonempty (E.obj ≅ (derivedPushforwardModules f).obj
                ((DerivedCategory.singleFunctor X.Modules 0).obj F.obj)) ∧
              e (properPushforward f (KZero.mk _ F)) = Pretriangulated.K0.cls E := by
  obtain ⟨e0, hexists, hsingle⟩ := exists_addEquiv_coherentKZero_K0 Y
  refine ⟨e0, hsingle, fun F => ?_⟩
  obtain ⟨E, hE, hval⟩ := properPushforward_mk_eq_derivedClass f F
  exact ⟨E, hE, hval e0 hsingle⟩

end AlgebraicGeometry.ProperPushforwardKZero

end
