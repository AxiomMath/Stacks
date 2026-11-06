module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFullyFaithful
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveTruncationTower
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGETower
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationTower
import StacksCore.Tactic.StacksAttribute

-- The identifications `(𝓘 ⋙ Q).obj n = Q.obj (𝓘.obj n)` and the independence of `∏ᶜ` from the
-- supplied `HasProduct` proof hold by `rfl` once these definitions may be unfolded.
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.Localization
import all Mathlib.CategoryTheory.Discrete.Basic
import all Mathlib.CategoryTheory.Functor.Basic
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# K-injective resolutions by towers, and exact functors preserving them

Let `A` be an abelian category and `K` a cochain complex in `A`. Resolving the truncations
`τ_{≥ -n} K` by bounded below complexes of injectives with degreewise split transition maps
(Stacks 070F) and passing to the limit gives a K-injective complex `lim 𝓘` (Stacks 070L) with a
canonical map `K ⟶ lim 𝓘` (Stacks 070P). This file proves, in an abelian category with
arbitrary universes, that this map is a quasi-isomorphism as soon as `Q K` is the derived limit
of its truncations `τ_{≥ -n} (Q K)` (the hypothesis Stacks 070Q derives from cohomology
vanishing on a site), and that an exact functor `F` which preserves injective objects and
countable inverse limits carries the resulting K-injective resolution to a K-injective complex.
For `F` fully faithful, `F` is then bijective on derived morphisms into `Q K`.

## Main results

* `Stacks.KInjectiveTower.quasiIso_to_limit_of_truncGE_resolutions_of_isIso`: the canonical map
  into the limit of the tower is a quasi-isomorphism, given the convergence of the truncations.
* `Stacks.KInjectiveTower.exists_quasiIso_isKInjective_map_isKInjective`: a K-injective
  resolution `K ⟶ I` with `F I` K-injective.
* `Stacks.KInjectiveTower.exists_iso_truncGE_Q_obj`: `Q (τ_{≥ n} K) ≅ τ_{≥ n} (Q K)` under `Q K`.
* `Stacks.KInjectiveTower.bijective_mapDerivedCategory_map_Q_of_isKInjective`: for `F` exact and
  fully faithful, `F` is bijective on `Hom(X, Q I)` when `I` and `F I` are K-injective.
* `Stacks.KInjectiveTower.bijective_mapDerivedCategory_map_of_truncGEConvergent`: hence bijective
  on `Hom(X, Q K)` for every `X`, given the convergence of the truncations of `Q K`.

## Implementation notes

The first result is the abstract half of Stacks 070Q
(`Stacks.Cohomology.quasiIso_to_limit_of_truncGE_resolutions`), whose statement fixes a site and
a ring sheaf with objects, morphisms and sections in one universe; here the convergence of the
truncations (Stacks 0D6P, 08F6) is a hypothesis.

## References

* [Stacks Project, Tag 070F](https://stacks.math.columbia.edu/tag/070F)
* [Stacks Project, Tag 070L](https://stacks.math.columbia.edu/tag/070L)
* [Stacks Project, Tag 070Q](https://stacks.math.columbia.edu/tag/070Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u wC vC uC vD uD wD

namespace Stacks.KInjectiveTower

section TruncationComparison


variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- **The complex-level truncation `τ_{≥ n} K` represents the t-structure truncation
`τ_{≥ n} (Q K)`**, by an isomorphism compatible with the canonical maps out of `Q K`. -/
theorem exists_iso_truncGE_Q_obj (K : CochainComplex A ℤ) (n : ℤ) :
    ∃ e : (DerivedCategory.TStructure.t.truncGE n).obj (DerivedCategory.Q.obj K) ≅
        DerivedCategory.Q.obj (K.truncGE n),
      (DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj K) ≫ e.hom =
        DerivedCategory.Q.map (K.πTruncGE n) := by
  have hn : n - 1 + 1 = n := by omega
  have hS := K.shortComplexTruncLE_shortExact (n - 1)
  let e₃ := asIso (DerivedCategory.Q.map (K.shortComplexTruncLEX₃ToTruncGE (n - 1) n hn))
  have h₃ : DerivedCategory.TStructure.t.IsGE (DerivedCategory.triangleOfSES hS).obj₃ n :=
    DerivedCategory.TStructure.t.isGE_of_iso e₃.symm n
  have hex := DerivedCategory.TStructure.t.triangle_iso_exists
    (DerivedCategory.TStructure.t.triangleLTGE_distinguished n (DerivedCategory.Q.obj K))
    (DerivedCategory.triangleOfSES_distinguished hS) (Iso.refl _) (n - 1) n
    (by infer_instance) (by infer_instance)
    (by
      show DerivedCategory.TStructure.t.IsLE
        (DerivedCategory.Q.obj (K.truncLE (n - 1))) (n - 1)
      infer_instance) h₃
  have he := Classical.choose_spec hex
  -- the comparison of the two triangles is the identity on the middle vertex, so it carries the
  -- canonical map of the t-structure to the canonical map of complexes
  have h₁ : (DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj K) ≫
      (Classical.choose hex).hom.hom₃ =
        DerivedCategory.Q.map (K.shortComplexTruncLE (n - 1)).g :=
    (Classical.choose hex).hom.comm₂.trans
      ((congrArg (fun z => z ≫ DerivedCategory.Q.map (K.shortComplexTruncLE (n - 1)).g) he).trans
        (Category.id_comp _))
  have h₂ : DerivedCategory.Q.map (K.shortComplexTruncLE (n - 1)).g ≫
      DerivedCategory.Q.map (K.shortComplexTruncLEX₃ToTruncGE (n - 1) n hn) =
        DerivedCategory.Q.map (K.πTruncGE n) :=
    (DerivedCategory.Q.map_comp _ _).symm.trans
      (congrArg (fun z => DerivedCategory.Q.map z)
        (K.g_shortComplexTruncLEX₃ToTruncGE (n - 1) n hn))
  exact ⟨Triangle.π₃.mapIso (Classical.choose hex) ≪≫ e₃,
    ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ DerivedCategory.Q.map
      (K.shortComplexTruncLEX₃ToTruncGE (n - 1) n hn)) h₁)).trans h₂⟩

end TruncationComparison

variable {A : Type u} [Category.{v} A] [Abelian A] [HasProductsOfShape ℕ A]
  [HasDerivedCategory.{w} A]

/-- **The truncations of `E` converge to `E`**: every map from `E` to a derived limit of the tower
of truncations `τ_{≥ -n} E`, compatible with the projections, is an isomorphism. This is the
conclusion of Stacks 0D6P and 08F6, the input of Stacks 070Q. -/
def TruncGEConvergent (E : DerivedCategory A) : Prop :=
  ∀ [HasProduct fun n : ℕ =>
        (Stacks.DerivedLimit.truncGETower A E).obj ⟨n⟩]
      (L : DerivedCategory A) (c : E ⟶ L)
      (p : L ⟶ ∏ᶜ fun n : ℕ =>
        (Stacks.DerivedLimit.truncGETower A E).obj ⟨n⟩)
      (δ : (∏ᶜ fun n : ℕ =>
        (Stacks.DerivedLimit.truncGETower A E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧),
      Triangle.mk p (Pi.lift fun n : ℕ =>
          Pi.π (fun n : ℕ =>
            (Stacks.DerivedLimit.truncGETower A E).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ =>
            (Stacks.DerivedLimit.truncGETower A E).obj ⟨n⟩) (n + 1) ≫
            (Stacks.DerivedLimit.truncGETower A E).map
              (homOfLE (Nat.le_succ n)).op) δ ∈ distTriang (DerivedCategory A) →
      (∀ n : ℕ, c ≫ p ≫ Pi.π (fun n : ℕ =>
          (Stacks.DerivedLimit.truncGETower A E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) →
      IsIso c

/-- **The canonical map into the limit of a tower of K-injective resolutions of the truncations
is a quasi-isomorphism once the truncations converge.** Let `𝓘` be an inverse system of
K-injective complexes with degreewise split transition maps and `f n : τ_{≥ -n} K ⟶ 𝓘ₙ`
quasi-isomorphisms forming a ladder over the canonical maps; if every map from `Q K` to a derived
limit of the truncations `τ_{≥ -n} (Q K)` compatible with the projections is an isomorphism,
then the canonical map `γ : K ⟶ lim 𝓘` is a quasi-isomorphism. -/
theorem quasiIso_to_limit_of_truncGE_resolutions_of_isIso
    (K : CochainComplex A ℤ) (𝓘 : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (f : ∀ n : ℕ, K.truncGE (-(n : ℤ)) ⟶ 𝓘.obj ⟨n⟩)
    (hf : ∀ n : ℕ, QuasiIso (f n))
    (hcompat : ∀ n : ℕ,
      K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ f (n + 1) ≫ 𝓘.map (homOfLE (Nat.le_succ n)).op =
        K.πTruncGE (-(n : ℤ)) ≫ f n)
    (h𝓘 : ∀ n : ℕ, (𝓘.obj ⟨n⟩).IsKInjective)
    (hsplit : ∀ (n : ℕ) (i : ℤ), IsSplitEpi ((𝓘.map (homOfLE (Nat.le_succ n)).op).f i))
    [HasLimit 𝓘] (γ : K ⟶ limit 𝓘)
    (hγ : ∀ n : ℕ, γ ≫ limit.π 𝓘 ⟨n⟩ = K.πTruncGE (-(n : ℤ)) ≫ f n)
    (hconv : TruncGEConvergent (DerivedCategory.Q.obj K)) :
    QuasiIso γ := by
  choose eT heT using fun m : ℤ => exists_iso_truncGE_Q_obj K m
  have heT' (m : ℤ) : DerivedCategory.Q.map (K.πTruncGE m) ≫ (eT m).inv =
      (DerivedCategory.TStructure.t.truncGEπ m).app (DerivedCategory.Q.obj K) := by
    rw [← heT m]
    simp [Category.assoc]
  obtain ⟨_, hprod, _, _, hmain⟩ :=
    CochainComplex.isKInjective_limit_and_isDerivedLimit_of_isSplitEpi 𝓘 h𝓘 hsplit
  have hprod' := hprod
  obtain ⟨γ₀, hγ₀, hiff⟩ := hmain K f hf hcompat
  rw [show γ = γ₀ from limit.hom_ext fun ⟨n⟩ => by rw [hγ n, hγ₀ n]]
  refine hiff.mpr fun L c p δ hT hc => ?_
  -- the canonical maps `Q K ⟶ τ_{≥ -n} (Q K)` form a cone over the truncation tower
  have hπG (n : ℕ) :
      (DerivedCategory.TStructure.t.truncGEπ
            (-((n + 1 : ℕ) : ℤ))).app (DerivedCategory.Q.obj K) ≫
          (Stacks.DerivedLimit.truncGETower A
            (DerivedCategory.Q.obj K)).map (homOfLE (Nat.le_succ n)).op =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app (DerivedCategory.Q.obj K) := by
    rw [Stacks.DerivedLimit.truncGETower_map_homOfLE_succ]
    exact DerivedCategory.TStructure.t.π_natTransTruncGEOfLE_app
      (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega) (DerivedCategory.Q.obj K)
  -- both legs of the ladder square, composed with the canonical map out of `Q K`, are the
  -- image of `K ⟶ τ_{≥ -n} K ⟶ 𝓘ₙ`
  have hlad (n : ℕ) :
      (DerivedCategory.TStructure.t.truncGEπ
            (-((n + 1 : ℕ) : ℤ))).app (DerivedCategory.Q.obj K) ≫
          (Stacks.DerivedLimit.truncGETower A
              (DerivedCategory.Q.obj K)).map (homOfLE (Nat.le_succ n)).op ≫
            (eT (-(n : ℤ))).hom ≫ DerivedCategory.Q.map (f n) =
        (DerivedCategory.TStructure.t.truncGEπ
            (-((n + 1 : ℕ) : ℤ))).app (DerivedCategory.Q.obj K) ≫
          ((eT (-((n + 1 : ℕ) : ℤ))).hom ≫ DerivedCategory.Q.map (f (n + 1))) ≫
            DerivedCategory.Q.map (𝓘.map (homOfLE (Nat.le_succ n)).op) := by
    have hL : (DerivedCategory.TStructure.t.truncGEπ
            (-((n + 1 : ℕ) : ℤ))).app (DerivedCategory.Q.obj K) ≫
          (Stacks.DerivedLimit.truncGETower A
              (DerivedCategory.Q.obj K)).map (homOfLE (Nat.le_succ n)).op ≫
            (eT (-(n : ℤ))).hom ≫ DerivedCategory.Q.map (f n) =
          DerivedCategory.Q.map (K.πTruncGE (-(n : ℤ)) ≫ f n) := by
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun z => z ≫ (eT (-(n : ℤ))).hom ≫
        DerivedCategory.Q.map (f n)) (hπG n)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun z => z ≫ DerivedCategory.Q.map (f n))
        (heT (-(n : ℤ)))).trans ?_
      exact (DerivedCategory.Q.map_comp _ _).symm
    have hR : (DerivedCategory.TStructure.t.truncGEπ
            (-((n + 1 : ℕ) : ℤ))).app (DerivedCategory.Q.obj K) ≫
          ((eT (-((n + 1 : ℕ) : ℤ))).hom ≫ DerivedCategory.Q.map (f (n + 1))) ≫
            DerivedCategory.Q.map (𝓘.map (homOfLE (Nat.le_succ n)).op) =
          DerivedCategory.Q.map (K.πTruncGE (-(n : ℤ)) ≫ f n) := by
      refine (congrArg (fun z => (DerivedCategory.TStructure.t.truncGEπ
        (-((n + 1 : ℕ) : ℤ))).app (DerivedCategory.Q.obj K) ≫ z)
          (Category.assoc _ _ _)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun z => z ≫ DerivedCategory.Q.map (f (n + 1)) ≫
        DerivedCategory.Q.map (𝓘.map (homOfLE (Nat.le_succ n)).op))
          (heT (-((n + 1 : ℕ) : ℤ)))).trans ?_
      refine (congrArg (fun z => DerivedCategory.Q.map
        (K.πTruncGE (-((n + 1 : ℕ) : ℤ))) ≫ z)
          (DerivedCategory.Q.map_comp (f (n + 1))
            (𝓘.map (homOfLE (Nat.le_succ n)).op)).symm).trans ?_
      refine (DerivedCategory.Q.map_comp _ _).symm.trans ?_
      exact congrArg (fun z => DerivedCategory.Q.map z) (hcompat n)
    exact hL.trans hR.symm
  let E : DerivedCategory A := DerivedCategory.Q.obj K
  let G : ℕᵒᵖ ⥤ DerivedCategory A :=
    Stacks.DerivedLimit.truncGETower A E
  let H : ℕᵒᵖ ⥤ DerivedCategory A := 𝓘 ⋙ DerivedCategory.Q
  let a (n : ℕ) : G.obj ⟨n⟩ ⟶ H.obj ⟨n⟩ := (eT (-(n : ℤ))).hom ≫ DerivedCategory.Q.map (f n)
  have ha (n : ℕ) : IsIso (a n) := by
    have := hf n
    exact IsIso.comp_isIso' (eT (-(n : ℤ))).isIso_hom inferInstance
  -- the comparison isomorphisms form a ladder between the two towers
  have ha_step (n : ℕ) : G.map (homOfLE (Nat.le_succ n)).op ≫ a n =
      a (n + 1) ≫ H.map (homOfLE (Nat.le_succ n)).op := by
    have := ha n
    have h₀ : DerivedCategory.TStructure.t.IsGE (G.obj ⟨n⟩) (-(n : ℤ)) := by
      show DerivedCategory.TStructure.t.IsGE
        ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E) (-(n : ℤ))
      infer_instance
    have h₁ : DerivedCategory.TStructure.t.IsGE (H.obj ⟨n⟩) (-(n : ℤ)) :=
      DerivedCategory.TStructure.t.isGE_of_iso (asIso (a n)) _
    have h₂ : DerivedCategory.TStructure.t.IsGE (H.obj ⟨n⟩) (-((n + 1 : ℕ) : ℤ)) :=
      DerivedCategory.TStructure.t.isGE_of_ge (H.obj ⟨n⟩) (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
        (by omega)
    exact DerivedCategory.TStructure.t.from_truncGE_obj_ext (hlad n)
  let ainv (n : ℕ) : H.obj ⟨n⟩ ⟶ G.obj ⟨n⟩ := inv (a n)
  let e : Discrete.functor (fun n : ℕ => H.obj ⟨n⟩) ≅ Discrete.functor (fun n : ℕ => G.obj ⟨n⟩) :=
    Discrete.natIso fun n => asIso (ainv n.as)
  have hprodG : HasProduct fun n : ℕ => G.obj ⟨n⟩ := hasLimit_of_iso e
  -- transport the presentation of the derived limit along the comparison
  let p' : L ⟶ ∏ᶜ fun n : ℕ => G.obj ⟨n⟩ := p ≫ CategoryTheory.Limits.Pi.map fun n : ℕ => ainv n
  have hp' : ∃ δ', Triangle.mk p'
      (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => G.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => G.obj ⟨n⟩) (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op) δ' ∈
      distTriang _ := by
    let q : (∏ᶜ fun n : ℕ => H.obj ⟨n⟩) ≅ ∏ᶜ fun n : ℕ => G.obj ⟨n⟩ :=
      { hom := CategoryTheory.Limits.Pi.map fun n : ℕ => ainv n
        inv := CategoryTheory.Limits.Pi.map fun n : ℕ => a n
        hom_inv_id := by ext n; simp [ainv, a]
        inv_hom_id := by ext n; simp [ainv, a] }
    have hstep (n : ℕ) : H.map (homOfLE (Nat.le_succ n)).op ≫ ainv n =
        ainv (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op := by
      have := ha n
      have := ha (n + 1)
      calc H.map (homOfLE (Nat.le_succ n)).op ≫ ainv n =
            (ainv (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op ≫ a n) ≫ ainv n := by
              rw [ha_step n]; simp [ainv, a]
        _ = ainv (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op := by
              simp [ainv, a, Category.assoc]
    let sG := Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => G.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ => G.obj ⟨n⟩) (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op
    let sH := Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => H.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ => H.obj ⟨n⟩) (n + 1) ≫ H.map (homOfLE (Nat.le_succ n)).op
    have hs : sH ≫ q.hom = q.hom ≫ sG := by
      refine Pi.hom_ext _ _ fun n => ?_
      simp only [q, sH, sG, Category.assoc, Pi.map_π, Pi.map_π_assoc, Pi.lift_comp_π,
        Pi.lift_comp_π_assoc, Preadditive.comp_sub, Preadditive.sub_comp]
      rw [hstep n]
    refine ⟨q.inv ≫ δ, isomorphic_distinguished _ hT _
      (Triangle.isoMk (Triangle.mk p sH δ) (Triangle.mk p' sG (q.inv ≫ δ))
        (Iso.refl _) q q (by simp [p', q]) hs (by simp)).symm⟩
  obtain ⟨δ', hT'⟩ := hp'
  have hc' (n : ℕ) : c ≫ p' ≫ Pi.π (fun n : ℕ => G.obj ⟨n⟩) n =
      (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E := by
    have hcancel : DerivedCategory.Q.map (f n) ≫ ainv n = (eT (-(n : ℤ))).inv := by
      have := ha n
      refine (cancel_epi (eT (-(n : ℤ))).hom).1 ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact (IsIso.hom_inv_id (a n)).trans (eT (-(n : ℤ))).hom_inv_id.symm
    have h1 : c ≫ p' ≫ Pi.π (fun n : ℕ => G.obj ⟨n⟩) n =
        (c ≫ p ≫ Pi.π (fun n : ℕ => H.obj ⟨n⟩) n) ≫ ainv n := by
      simp [p', H, Category.assoc, Pi.map_π, Functor.comp_obj]
    refine h1.trans ((congrArg (fun z => z ≫ ainv n) (hc n)).trans ?_)
    refine (congrArg (fun z => z ≫ ainv n) (DerivedCategory.Q.map_comp _ _)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun z => DerivedCategory.Q.map (K.πTruncGE (-(n : ℤ))) ≫ z) hcancel).trans ?_
    exact heT' (-(n : ℤ))
  exact hconv L c p' δ' hT' hc'

section Map

variable {C : Type uC} [Category.{vC} C] [Abelian C] [EnoughInjectives C]
  [HasProductsOfShape ℕ C] [HasLimitsOfShape ℕᵒᵖ C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D]

open ZeroObject in
/-- **A K-injective resolution which an exact functor preserving injectives and countable inverse
limits carries to a K-injective complex**: the limit of the tower of injective resolutions of the
truncations of `K`, when those truncations converge. -/
theorem exists_quasiIso_isKInjective_map_isKInjective
    (F : C ⥤ D) [F.Additive] [F.Faithful] [F.PreservesInjectiveObjects]
    [PreservesLimitsOfShape ℕᵒᵖ F] (K : CochainComplex C ℤ)
    (hconv : TruncGEConvergent (DerivedCategory.Q.obj K)) :
    ∃ (I : CochainComplex C ℤ) (γ : K ⟶ I), QuasiIso γ ∧ I.IsKInjective ∧
      CochainComplex.IsKInjective ((F.mapHomologicalComplex (.up ℤ)).obj I) := by
  let T := F.mapHomologicalComplex (.up ℤ)
  have : PreservesLimitsOfShape ℕᵒᵖ T := by
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro i
    show PreservesLimitsOfShape ℕᵒᵖ ((HomologicalComplex.eval C (.up ℤ) i) ⋙ F)
    infer_instance
  have : ObjectProperty.ContainsZero (C := C) (fun X ↦ Injective X) :=
    ⟨⟨0, isZero_zero _, inferInstance⟩⟩
  obtain ⟨I, f, g, hf, -, hGE, hinj, hsplit, hladder⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncGE (fun X : C ↦ Injective X)
      (fun X Y hX hY ↦ by have := hX; have := hY; infer_instance)
      (fun X ↦ ⟨Injective.under X, inferInstance, Injective.ι X, inferInstance⟩) K
  let tower := Functor.ofOpSequence g
  have hmap (n : ℕ) : tower.map (homOfLE (Nat.le_succ n)).op = g n :=
    Functor.ofOpSequence_map_homOfLE_succ g n
  have hg (n : ℕ) (i : ℤ) : IsSplitEpi ((tower.map (homOfLE (Nat.le_succ n)).op).f i) := by
    rw [hmap]
    obtain ⟨W, _, e, he⟩ := hsplit n i
    exact IsSplitEpi.mk' ⟨biprod.inl ≫ e.inv,
      (Category.assoc _ _ _).trans ((congrArg _ he).trans biprod.inl_fst)⟩
  have hKI (n : ℕ) : (tower.obj ⟨n⟩).IsKInjective := by
    have := hGE n
    have : ∀ i : ℤ, Injective ((I n).X i) := hinj n
    exact CochainComplex.isKInjective_of_injective (I n) (-(n : ℤ))
  obtain ⟨_, _, hlimKI, _, _⟩ :=
    CochainComplex.isKInjective_limit_and_isDerivedLimit_of_isSplitEpi tower hKI hg
  have hcompat (n : ℕ) : K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ f (n + 1) ≫
      tower.map (homOfLE (Nat.le_succ n)).op = K.πTruncGE (-(n : ℤ)) ≫ f n := by
    rw [hmap]
    exact hladder n
  let c : Cone tower := {
    pt := K
    π := NatTrans.ofOpSequence (fun n ↦ K.πTruncGE (-(n : ℤ)) ≫ f n)
      (fun n ↦ by
        dsimp only [Functor.const_obj_map]
        refine (Category.id_comp _).trans ?_
        rw [hmap n]
        show K.πTruncGE (-(n : ℤ)) ≫ f n =
          (K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ f (n + 1)) ≫ g n
        exact (hladder n).symm.trans (Category.assoc _ _ _).symm) }
  let γ := limit.lift tower c
  have hγ (n : ℕ) : γ ≫ limit.π tower ⟨n⟩ = K.πTruncGE (-(n : ℤ)) ≫ f n :=
    limit.lift_π c ⟨n⟩
  have hγq : QuasiIso γ :=
    quasiIso_to_limit_of_truncGE_resolutions_of_isIso K tower f hf hcompat hKI hg γ hγ hconv
  have hTKI (n : ℕ) : CochainComplex.IsKInjective ((tower ⋙ T).obj ⟨n⟩) := by
    have : CochainComplex.IsStrictlyGE (T.obj (I n)) (-(n : ℤ)) :=
      (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff (I n) F _).2 (hGE n)
    have : ∀ i : ℤ, Injective ((T.obj (I n)).X i) := fun i ↦
      (Functor.PreservesInjectiveObjects.injective_obj (hinj n i) : Injective (F.obj ((I n).X i)))
    exact CochainComplex.isKInjective_of_injective (T.obj (I n)) (-(n : ℤ))
  have hTg (n : ℕ) (i : ℤ) :
      IsSplitEpi (((tower ⋙ T).map (homOfLE (Nat.le_succ n)).op).f i) := by
    have := hg n i
    exact inferInstanceAs (IsSplitEpi (F.map ((tower.map (homOfLE (Nat.le_succ n)).op).f i)))
  have : HasLimit (tower ⋙ T) :=
    ⟨⟨⟨T.mapCone (limit.cone tower), isLimitOfPreserves T (limit.isLimit tower)⟩⟩⟩
  have : CochainComplex.IsKInjective (limit (tower ⋙ T)) :=
    isKInjective_limit_of_inverseSystem (tower ⋙ T) hTKI hTg
  exact ⟨limit tower, γ, hγq, hlimKI,
    CochainComplex.isKInjective_of_iso (preservesLimitIso T tower).symm⟩

variable [HasDerivedCategory.{wD} D]

omit [EnoughInjectives C] [HasProductsOfShape ℕ C] [HasLimitsOfShape ℕᵒᵖ C] in
/-- **An exact fully faithful functor is bijective on derived morphisms into a K-injective
complex which it carries to a K-injective complex.** -/
theorem bijective_mapDerivedCategory_map_Q_of_isKInjective
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (X : DerivedCategory C) (I : CochainComplex C ℤ) [I.IsKInjective]
    [CochainComplex.IsKInjective ((F.mapHomologicalComplex (.up ℤ)).obj I)] :
    Function.Bijective (F.mapDerivedCategory.map : (X ⟶ DerivedCategory.Q.obj I) → _) := by
  let X' := DerivedCategory.Qh.objPreimage X
  let Y' := (HomotopyCategory.quotient C (.up ℤ)).obj I
  refine F.mapDerivedCategory.bijective_map_of_iso
    (DerivedCategory.Qh.objObjPreimageIso X)
    ((DerivedCategory.quotientCompQhIso C).app I) ?_
  have hQ' : Function.Bijective (DerivedCategory.Qh.map :
      ((F.mapHomotopyCategory (.up ℤ)).obj X' ⟶ (F.mapHomotopyCategory (.up ℤ)).obj Y') → _) :=
    CochainComplex.IsKInjective.Qh_map_bijective _ ((F.mapHomologicalComplex (.up ℤ)).obj I)
  let e := F.mapDerivedCategoryFactorsh
  have hcomp : (F.mapDerivedCategory.map : _ → _) ∘ (DerivedCategory.Qh.map : (X' ⟶ Y') → _) =
      ((e.app X').homCongr (e.app Y')).symm ∘ (DerivedCategory.Qh.map) ∘
        (F.mapHomotopyCategory (.up ℤ)).map := by
    funext φ
    simp only [Function.comp_apply, Iso.homCongr, Equiv.coe_fn_symm_mk, Iso.app_inv, Iso.app_hom]
    have := e.hom.naturality φ
    simp only [Functor.comp_map] at this
    rw [← Category.assoc, ← this, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hb : Function.Bijective ((F.mapDerivedCategory.map : _ → _) ∘
      (DerivedCategory.Qh.map : (X' ⟶ Y') → _)) := by
    rw [hcomp]
    exact (Equiv.bijective _).comp (hQ'.comp
      ⟨(F.mapHomotopyCategory (.up ℤ)).map_injective,
        (F.mapHomotopyCategory (.up ℤ)).map_surjective⟩)
  exact (Function.Bijective.of_comp_iff _ (CochainComplex.IsKInjective.Qh_map_bijective X' I)).1 hb

/-- **An exact fully faithful functor preserving injectives and countable inverse limits is
bijective on derived morphisms into an object whose truncations converge.** -/
theorem bijective_mapDerivedCategory_map_of_truncGEConvergent
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [F.PreservesInjectiveObjects] [PreservesLimitsOfShape ℕᵒᵖ F]
    (X : DerivedCategory C) (K : CochainComplex C ℤ)
    (hconv : TruncGEConvergent (DerivedCategory.Q.obj K)) :
    Function.Bijective (F.mapDerivedCategory.map : (X ⟶ DerivedCategory.Q.obj K) → _) := by
  obtain ⟨I, γ, hγ, hI, hFI⟩ := exists_quasiIso_isKInjective_map_isKInjective F K hconv
  exact F.mapDerivedCategory.bijective_map_of_iso (Iso.refl X)
    (asIso (DerivedCategory.Q.map γ)).symm
    (bijective_mapDerivedCategory_map_Q_of_isKInjective F X I)

end Map

end Stacks.KInjectiveTower
