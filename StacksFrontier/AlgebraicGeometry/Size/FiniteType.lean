module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Algebra.MvPolynomial.Cardinal

public import StacksFrontier.AlgebraicGeometry.Size.Basic

/-!
# Size of a scheme of finite type over a base

For a morphism `f : X ⟶ S` that is locally of finite type with `X` quasi-compact, the cardinal
`Scheme.size X` is at most `Scheme.size S` (Stacks 04T7). Here `Scheme.size X` is the maximum of
`ℵ₀`, the number of affine opens of `X`, and the supremum of `#Γ(X, U)` over affine opens `U`.

## Main results

* `Cardinal.mk_le_of_algebra_finiteType`: a finitely generated commutative `R`-algebra `A`
  satisfies `#A ≤ max ℵ₀ #R`.
* `AlgebraicGeometry.Scheme.size_le_of_finite_affine_cover`: if `X` is covered by finitely many
  affine opens `U k` with `#Γ(X, U k) ≤ c` for an infinite cardinal `c`, then `size X ≤ c`.
* `AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType`: if `f : X ⟶ S` is locally of
  finite type and `X` is quasi-compact, then `size X ≤ size S`.
-/

@[expose] public section

open CategoryTheory Cardinal Opposite TopologicalSpace

universe u

namespace Cardinal

/-- A finitely generated commutative `R`-algebra `A` satisfies `#A ≤ max ℵ₀ #R`. -/
lemma mk_le_of_algebra_finiteType (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A] : #A ≤ max ℵ₀ #R := by
  obtain ⟨s, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial (R := R) (S := A)).mp inferInstance
  calc #A ≤ #(MvPolynomial s R) := mk_le_of_surjective hf
    _ ≤ #R ⊔ #(s : Type u) ⊔ ℵ₀ := MvPolynomial.cardinalMk_le_max
    _ ≤ max ℵ₀ #R := sup_le (sup_le (le_max_right _ _)
        (mk_le_aleph0.trans (le_max_left _ _))) (le_max_left _ _)

/-- A finite product of types, each of cardinality at most an infinite cardinal `c`, has
cardinality at most `c`. -/
private lemma mk_pi_fin_le {m : ℕ} (α : Fin m → Type*) (c : Cardinal) (hc0 : ℵ₀ ≤ c)
    (hα : ∀ l, #(α l) ≤ c) : #(∀ l : Fin m, α l) ≤ c := by
  rw [mk_pi]
  calc Cardinal.prod (fun i => #(α i))
      ≤ Cardinal.prod (fun _ : Fin m => c) := prod_le_prod _ _ hα
    _ = Cardinal.lift c ^ Cardinal.lift #(Fin m) := prod_const _ _
    _ = c ^ (m : Cardinal) := by simp
    _ ≤ c := power_nat_le hc0

end Cardinal

namespace AlgebraicGeometry

/-- `#Γ(X, U) ≤ max ℵ₀ #Γ(S, V)` for affine opens `U ⊆ X`, `V ⊆ S` with `U ≤ f⁻¹ᵁ V` and `f`
locally of finite type. -/
private lemma mk_sections_le_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (V : S.affineOpens) (U : X.affineOpens)
    (e : U.1 ≤ f ⁻¹ᵁ V.1) :
    #Γ(X, U.1) ≤ max ℵ₀ #Γ(S, V.1) := by
  have hFT := f.finiteType_appLE V.2 U.2 e
  let : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 e).hom.toAlgebra
  have : Algebra.FiniteType Γ(S, V.1) Γ(X, U.1) := hFT
  exact mk_le_of_algebra_finiteType Γ(S, V.1) Γ(X, U.1)

/-- For any morphism `f : X ⟶ S` and any point `x : X`, there exist an affine open
`U : X.affineOpens` containing `x` and an affine open `V : S.affineOpens` with `U ≤ f⁻¹ᵁ V`. -/
private lemma exists_subordinate_affineOpen {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    ∃ (U : X.affineOpens) (V : S.affineOpens), x ∈ U.1 ∧ U.1 ≤ f ⁻¹ᵁ V.1 := by
  obtain ⟨V₀, hV_aff, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (x := f.base x) (U := (⊤ : S.Opens)) trivial
  obtain ⟨U₀, hU_aff, hxU, hUsub⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := f ⁻¹ᵁ V₀) hxV
  exact ⟨⟨U₀, hU_aff⟩, ⟨V₀, hV_aff⟩, hxU, hUsub⟩

/-- If a family `U' : Fin n → X.Opens` covers `X` set-theoretically, then it covers `X` in the
lattice of opens. -/
private lemma iSup_eq_top_of_carrier_cover {X : Scheme.{u}} {n : ℕ} (U' : Fin n → X.Opens)
    (hcov : Set.univ ⊆ ⋃ k, (U' k).carrier) :
    (⨆ k, U' k) = ⊤ :=
  Opens.ext <| by
    rw [Opens.coe_iSup, Opens.coe_top]; exact Set.eq_univ_of_univ_subset hcov

/-- For an open subset `W` and a finite family `V : Fin m → X.Opens` covering `W` from below,
`W = ⨆ l, V l`. -/
private lemma opens_eq_iSup_of_carrier_cover {X : Scheme.{u}} (W : X.Opens) {m : ℕ}
    (V : Fin m → X.Opens) (hV : ∀ l, V l ≤ W)
    (hcov : (W.carrier : Set X) ⊆ ⋃ l, (V l).carrier) :
    W = ⨆ l, V l :=
  Opens.ext <| by
    rw [Opens.coe_iSup]; exact Set.Subset.antisymm hcov (Set.iUnion_subset hV)

/-- A compact set covered by open sets `O i` is covered by finitely many of them, indexed by
`Fin m`. -/
private lemma exists_fin_subcover {X : Type*} [TopologicalSpace X] {ι : Type*} {K : Set X}
    (hK : IsCompact K) (O : ι → Set X) (hO : ∀ i, IsOpen (O i)) (hcov : K ⊆ ⋃ i, O i) :
    ∃ (m : ℕ) (i : Fin m → ι), K ⊆ ⋃ l, O (i l) := by
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover O hO hcov
  refine ⟨t.card, fun l => (t.equivFin.symm l).1, fun x hx => ?_⟩
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact Set.mem_iUnion.mpr ⟨t.equivFin ⟨y, hyt⟩, by simpa using hxy⟩

/-- If `X` is quasi-compact and every point `x` lies in an affine open `U x` contained in the
preimage of an affine open `V x` of `S`, then finitely many of the `U x` cover `X`. -/
private lemma exists_finite_subordinate_cover {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace X] (U : X → X.affineOpens) (V : X → S.affineOpens)
    (hx_mem : ∀ x, x ∈ (U x).1)
    (hUV : ∀ x, (U x).1 ≤ f ⁻¹ᵁ (V x).1) :
    ∃ (n : ℕ) (U' : Fin n → X.affineOpens) (V' : Fin n → S.affineOpens),
      (⨆ k, (U' k).1) = ⊤ ∧ ∀ k, (U' k).1 ≤ f ⁻¹ᵁ (V' k).1 := by
  obtain ⟨n, i, hi⟩ := exists_fin_subcover isCompact_univ (fun x => ((U x).1 : Set X))
    (fun x => (U x).1.isOpen) fun x _ => Set.mem_iUnion.mpr ⟨x, hx_mem x⟩
  exact ⟨n, U ∘ i, V ∘ i, iSup_eq_top_of_carrier_cover _ hi, fun k => hUV _⟩

/-- A finite affine cover of `X` subordinate to `f : X ⟶ S`, for `f` locally of finite type and `X`
quasi-compact. -/
private lemma exists_finite_subordinate_cover_of_locallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [CompactSpace X] :
    ∃ (n : ℕ) (U : Fin n → X.affineOpens) (V : Fin n → S.affineOpens),
      (⨆ k, (U k).1) = ⊤ ∧ ∀ k, (U k).1 ≤ f ⁻¹ᵁ (V k).1 := by
  choose U V hxU hUV using exists_subordinate_affineOpen f
  exact exists_finite_subordinate_cover f U V hxU hUV

/-- Inside an affine open `U`, every point of an arbitrary open `W` lies in a basic open `D(g)`
with `g ∈ Γ(X, U)` that is contained in both `W` and `U`. -/
private lemma exists_basicOpen_subset_of_mem {X : Scheme.{u}} (U : X.affineOpens)
    (W : X.Opens) {x : X.toPresheafedSpace} (hxU : x ∈ U.1) (hxW : x ∈ W) :
    ∃ g : Γ(X, U.1),
      x ∈ X.basicOpen g ∧ X.basicOpen g ≤ W ∧ X.basicOpen g ≤ U.1 := by
  obtain ⟨g, hg_le, hxg⟩ :=
    U.2.exists_basicOpen_le (V := W ⊓ U.1) ⟨x, hxW, hxU⟩ hxU
  exact ⟨g, hxg, hg_le.trans inf_le_left, hg_le.trans inf_le_right⟩

/-- Given a finite affine cover `U k` of `X` and any affine open `W ⊆ X`, `W` is the union of
finitely many basic opens drawn from the `U k`, each contained in `W`. -/
private lemma exists_finite_basicOpen_subcover {X : Scheme.{u}} {n : ℕ}
    (U : Fin n → X.affineOpens) (hU : (⨆ k, (U k).1) = ⊤) (W : X.affineOpens) :
    ∃ (m : ℕ) (k : Fin m → Fin n) (g : (l : Fin m) → Γ(X, (U (k l)).1)),
      W.1 = (⨆ l, X.basicOpen (g l)) ∧ ∀ l, X.basicOpen (g l) ≤ W.1 := by
  have h_pt : ∀ x : (W.1.carrier : Set X),
      ∃ (k : Fin n) (g : Γ(X, (U k).1)),
        (x : X) ∈ X.basicOpen g ∧ X.basicOpen g ≤ W.1 := by
    rintro ⟨x, hxW⟩
    obtain ⟨k, hxk⟩ := Opens.mem_iSup.mp (by rw [hU]; trivial : x ∈ ⨆ k, (U k).1)
    obtain ⟨g, hxg, hgW, -⟩ := exists_basicOpen_subset_of_mem (U k) W.1 hxk hxW
    exact ⟨k, g, hxg, hgW⟩
  choose k_fn g_fn h_mem h_sub using h_pt
  obtain ⟨m, i, hi⟩ := exists_fin_subcover W.2.isCompact
    (fun y : W.1.carrier => ((X.basicOpen (g_fn y)).carrier : Set X))
    (fun _ => (X.basicOpen _).isOpen)
    fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, h_mem ⟨x, hx⟩⟩
  exact ⟨m, fun l => k_fn (i l), fun l => g_fn (i l),
    opens_eq_iSup_of_carrier_cover W.1 (fun l => X.basicOpen (g_fn (i l)))
      (fun l => h_sub (i l)) hi, fun l => h_sub (i l)⟩

/-- For a finite cover `V` of `W`, the product of the restriction maps `Γ(X, W) → ∏ l, Γ(X, V l)`
is injective, so `#Γ(X, W) ≤ #(∏ l, Γ(X, V l))`. -/
private lemma mk_sections_le_pi_of_cover {X : Scheme.{u}} {m : ℕ} (W : X.Opens)
    (V : Fin m → X.Opens) (hVle : ∀ l, V l ≤ W) (hVcov : W = ⨆ l, V l) :
    #Γ(X, W) ≤ #(∀ l : Fin m, Γ(X, V l)) := by
  subst hVcov
  exact mk_le_of_injective (f := fun s l => X.presheaf.map (homOfLE (hVle l)).op s)
    fun s t hst => TopCat.Sheaf.eq_of_locally_eq X.sheaf V s t (congr_fun hst)

/-- For an affine open `U` and a section `g` over `U`, `#Γ(X, D(g)) ≤ max ℵ₀ #Γ(X, U)`. -/
private lemma mk_sections_basicOpen_le {X : Scheme.{u}} (U : X.affineOpens)
    (g : Γ(X, U.1)) :
    #Γ(X, X.basicOpen g) ≤ max ℵ₀ #Γ(X, U.1) := by
  have : IsLocalization.Away g Γ(X, X.basicOpen g) := U.2.isLocalization_basicOpen g
  have : Algebra.FiniteType Γ(X, U.1) Γ(X, X.basicOpen g) :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers g) _
  exact mk_le_of_algebra_finiteType _ _

/-- Sections over an affine open `W` with a finite cover whose pieces are all bounded by an
infinite cardinal `c` are themselves bounded by `c`. -/
private lemma mk_sections_le_of_finiteCover {X : Scheme.{u}} {m : ℕ} (W : X.affineOpens)
    (V : Fin m → X.Opens) (hVle : ∀ l, V l ≤ W.1) (hVcov : W.1 = ⨆ l, V l)
    (c : Cardinal) (hc0 : ℵ₀ ≤ c) (hcV : ∀ l, #Γ(X, V l) ≤ c) :
    #Γ(X, W.1) ≤ c :=
  (mk_sections_le_pi_of_cover W.1 V hVle hVcov).trans (mk_pi_fin_le _ c hc0 hcV)

/-- For any affine open `W` of `X`, `#Γ(X, W) ≤ c` given a finite affine cover by `U k` with each
`#Γ(X, U k) ≤ c` and `ℵ₀ ≤ c`. -/
private lemma mk_sections_le_of_cover {X : Scheme.{u}} {n : ℕ}
    (U : Fin n → X.affineOpens) (hU : (⨆ k, (U k).1) = ⊤) (c : Cardinal) (hc0 : ℵ₀ ≤ c)
    (hcU : ∀ k, #Γ(X, (U k).1) ≤ c) (W : X.affineOpens) : #Γ(X, W.1) ≤ c := by
  obtain ⟨m, k, g, hgcov, hgleW⟩ := exists_finite_basicOpen_subcover U hU W
  refine mk_sections_le_of_finiteCover W (fun l => X.basicOpen (g l)) hgleW hgcov c hc0
    fun l => (mk_sections_basicOpen_le (U (k l)) (g l)).trans (max_le hc0 (hcU (k l)))

/-- If `X` is covered by finitely many affine opens `U k` with each `#Γ(X, U k) ≤ c` and `ℵ₀ ≤ c`,
then `#X.affineOpens ≤ c`. -/
private lemma mk_affineOpens_le_of_cover {X : Scheme.{u}} {n : ℕ}
    (U : Fin n → X.affineOpens) (hU : (⨆ k, (U k).1) = ⊤) (c : Cardinal.{u})
    (hc0 : ℵ₀ ≤ c) (hcU : ∀ k, #Γ(X, (U k).1) ≤ c) :
    #X.affineOpens ≤ c := by
  let D : Type u := Σ k : Fin n, Γ(X, (U k).1)
  choose mFun kFun gFun hcovEq _ using
    fun W : X.affineOpens => exists_finite_basicOpen_subcover U hU W
  let enc : X.affineOpens → List D := fun W =>
    List.ofFn fun l : Fin (mFun W) => (⟨kFun W l, gFun W l⟩ : D)
  have hrec : ∀ W : X.affineOpens, (⨆ d ∈ enc W, X.basicOpen d.2) = W.1 := fun W => by
    rw [hcovEq W]
    refine le_antisymm (iSup_le fun d => iSup_le fun hd => ?_)
      (iSup_le fun l => le_iSup_of_le ⟨kFun W l, gFun W l⟩ <|
        le_iSup_of_le (List.mem_ofFn.mpr ⟨l, rfl⟩) le_rfl)
    obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hd
    exact le_iSup_of_le l le_rfl
  have hinj : Function.Injective enc := fun W W' h =>
    Subtype.ext <| by rw [← hrec W, ← hrec W', h]
  refine (mk_le_of_injective hinj).trans ?_
  calc #(List D) ≤ max ℵ₀ #D := mk_list_le_max D
    _ ≤ c := by
        refine max_le hc0 ?_
        rw [show #D = Cardinal.sum fun k : Fin n => #Γ(X, (U k).1) from mk_sigma _]
        refine (sum_le_sum _ (fun _ => c) hcU).trans ?_
        rw [sum_const, lift_uzero, mk_fin, lift_natCast]
        exact (mul_le_max_of_aleph0_le_right hc0).trans
          (max_eq_right (natCast_le_aleph0.trans hc0)).le

/-- If `X` is covered by finitely many affine opens `U k` and each `#Γ(X, U k) ≤ c` with `ℵ₀ ≤ c`,
then `Scheme.size X ≤ c`. -/
lemma Scheme.size_le_of_finite_affine_cover {X : Scheme.{u}} {n : ℕ}
    (U : Fin n → X.affineOpens) (hU : (⨆ k, (U k).1) = ⊤)
    (c : Cardinal.{u}) (hc0 : ℵ₀ ≤ c) (hcU : ∀ k, #Γ(X, (U k).1) ≤ c) :
    Scheme.size X ≤ c :=
  max_le hc0 (max_le (mk_affineOpens_le_of_cover U hU c hc0 hcU)
    (ciSup_le' (mk_sections_le_of_cover U hU c hc0 hcU)))

/-- If `f : X ⟶ S` is locally of finite type and `X` is quasi-compact, then
`Scheme.size X ≤ Scheme.size S`. -/
@[stacks 04T7]
theorem Scheme.size_le_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [CompactSpace X] :
    Scheme.size X ≤ Scheme.size S := by
  obtain ⟨n, U, V, hcov, hsub⟩ := exists_finite_subordinate_cover_of_locallyOfFiniteType f
  exact Scheme.size_le_of_finite_affine_cover U hcov (Scheme.size S)
    (Scheme.aleph0_le_size S) fun k =>
      (mk_sections_le_of_locallyOfFiniteType f (V k) (U k) (hsub k)).trans
        (max_le (Scheme.aleph0_le_size S) (Scheme.mk_sections_le_size S (V k)))

end AlgebraicGeometry
