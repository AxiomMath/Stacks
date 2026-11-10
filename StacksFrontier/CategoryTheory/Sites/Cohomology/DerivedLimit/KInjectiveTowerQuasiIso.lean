module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationTower
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationConvergenceUnderBounds
import StacksCore.Tactic.StacksAttribute

-- The identifications `(𝓘 ⋙ Q).obj n = Q.obj (𝓘.obj n)` and the independence of `∏ᶜ` from the
-- supplied `HasProduct` proof hold by `rfl`, but only once `Qh`, `Functor.comp` and `getLimitCone`
-- may be unfolded.
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.Localization
import all Mathlib.CategoryTheory.Discrete.Basic
import all Mathlib.CategoryTheory.Functor.Basic
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# The limit of a tower of K-injective resolutions of the truncations of a complex

Let `O` be a sheaf of rings on a site `C` and let `K` be a cochain complex of `O`-modules.
Suppose given an inverse system `𝓘 : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules O) ℤ` of K-injective
complexes whose transition maps are degreewise split epimorphisms, together with
quasi-isomorphisms `fₙ : τ_{≥ -n} K ⟶ 𝓘ₙ` forming a commutative ladder over the canonical maps
`K ⟶ τ_{≥ -n} K`. Then the canonical map `γ : K ⟶ lim 𝓘` is a quasi-isomorphism as soon as
there are a subset `B` of the objects of `C` covering every object and a natural number `d` with
`H^p(V, H^q(K)) = 0` for every `V ∈ B`, every `p > d` and every `q < 0`.

## Main results

* `Stacks.Cohomology.quasiIso_to_limit_of_truncGE_resolutions`: the canonical map to the limit
  of the tower is a quasi-isomorphism.

## References

* [Stacks Project, Tag 070Q](https://stacks.math.columbia.edu/tag/070Q)
* [Stacks Project, Tag 070M](https://stacks.math.columbia.edu/tag/070M)
* [Stacks Project, Tag 0D6P](https://stacks.math.columbia.edu/tag/0D6P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace Stacks.Cohomology

attribute [local instance] HasDerivedCategory.standard

section TruncationComparison

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The complex-level truncation `τ_{≥ n} K` represents the t-structure truncation
`τ_{≥ n} (Q K)`, by an isomorphism compatible with the canonical maps out of `Q K`. -/
private def truncGEQIsoData (K : CochainComplex A ℤ) (n : ℤ) :
    { e : (DerivedCategory.TStructure.t.truncGE n).obj (DerivedCategory.Q.obj K) ≅
        DerivedCategory.Q.obj (K.truncGE n) //
      (DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj K) ≫ e.hom =
        DerivedCategory.Q.map (K.πTruncGE n) } := by
  have hn : n - 1 + 1 = n := by omega
  have hS := K.shortComplexTruncLE_shortExact (n - 1)
  have hε : (K.shortComplexTruncLE (n - 1)).g ≫
      K.shortComplexTruncLEX₃ToTruncGE (n - 1) n hn = K.πTruncGE n :=
    K.g_shortComplexTruncLEX₃ToTruncGE (n - 1) n hn
  have hiso : IsIso (DerivedCategory.Q.map (K.shortComplexTruncLEX₃ToTruncGE (n - 1) n hn)) :=
    inferInstance
  let e₃ := asIso (DerivedCategory.Q.map (K.shortComplexTruncLEX₃ToTruncGE (n - 1) n hn))
  have h₃ : DerivedCategory.TStructure.t.IsGE (DerivedCategory.triangleOfSES hS).obj₃ n :=
    DerivedCategory.TStructure.t.isGE_of_iso e₃.symm n
  have hex := DerivedCategory.TStructure.t.triangle_iso_exists
    (DerivedCategory.TStructure.t.triangleLTGE_distinguished n (DerivedCategory.Q.obj K))
    (DerivedCategory.triangleOfSES_distinguished hS) (Iso.refl _) (n - 1) n
    (by infer_instance) (by infer_instance)
    (by
      change DerivedCategory.TStructure.t.IsLE
        (DerivedCategory.Q.obj (K.truncLE (n - 1))) (n - 1)
      infer_instance) h₃
  have he := Classical.choose_spec hex
  have h₁ : (DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj K) ≫
      (Classical.choose hex).hom.hom₃ =
        DerivedCategory.Q.map (K.shortComplexTruncLE (n - 1)).g :=
    (Classical.choose hex).hom.comm₂.trans
      ((congrArg (fun z ↦ z ≫ DerivedCategory.Q.map (K.shortComplexTruncLE (n - 1)).g) he).trans
        (Category.id_comp _))
  have h₂ : DerivedCategory.Q.map (K.shortComplexTruncLE (n - 1)).g ≫
      DerivedCategory.Q.map (K.shortComplexTruncLEX₃ToTruncGE (n - 1) n hn) =
        DerivedCategory.Q.map (K.πTruncGE n) :=
    (DerivedCategory.Q.map_comp _ _).symm.trans
      (congrArg (fun z ↦ DerivedCategory.Q.map z) hε)
  refine ⟨Triangle.π₃.mapIso (Classical.choose hex) ≪≫ e₃, ?_⟩
  exact ((Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫ DerivedCategory.Q.map
    (K.shortComplexTruncLEX₃ToTruncGE (n - 1) n hn)) h₁)).trans h₂

/-- The image in the derived category of the complex-level truncation `τ_{≥ n} K` is the
t-structure truncation `τ_{≥ n} (Q K)`. -/
private def truncGEQIso (K : CochainComplex A ℤ) (n : ℤ) :
    (DerivedCategory.TStructure.t.truncGE n).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (K.truncGE n) :=
  (truncGEQIsoData K n).1

/-- `truncGEQIso` identifies the canonical map `Q K ⟶ τ_{≥ n} (Q K)` of the t-structure with the
canonical map `K ⟶ τ_{≥ n} K` of complexes. -/
private lemma truncGEπ_comp_truncGEQIso_hom (K : CochainComplex A ℤ) (n : ℤ) :
    (DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj K) ≫
      (truncGEQIso K n).hom = DerivedCategory.Q.map (K.πTruncGE n) :=
  (truncGEQIsoData K n).2

/-- The inverse form of `truncGEπ_comp_truncGEQIso_hom`. -/
private lemma Q_map_πTruncGE_comp_truncGEQIso_inv (K : CochainComplex A ℤ) (n : ℤ) :
    DerivedCategory.Q.map (K.πTruncGE n) ≫ (truncGEQIso K n).inv =
      (DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj K) := by
  rw [← truncGEπ_comp_truncGEQIso_hom K n]
  simp [Category.assoc]

end TruncationComparison

/-- Let `O` be a sheaf of rings on a site, let `K` be a cochain complex of `O`-modules, and let
`𝓘` be an inverse system of K-injective complexes with degreewise split-epimorphic transition
maps resolving the truncations `τ_{≥ -n} K` compatibly with the canonical maps
`K ⟶ τ_{≥ -n} K`. If a subset `B` of the objects of the site covers every object and
`H^p(V, H^q(K)) = 0` for every `V ∈ B`, every `p > d` and every `q < 0`, then the canonical map
`γ : K ⟶ lim 𝓘` is a quasi-isomorphism. -/
@[stacks 070Q]
theorem quasiIso_to_limit_of_truncGE_resolutions {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} (O : Sheaf J RingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [EnoughInjectives (SheafOfModules.{u} O)]
    (K : CochainComplex (SheafOfModules.{u} O) ℤ)
    (𝓘 : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{u} O) ℤ)
    (f : ∀ n : ℕ, K.truncGE (-(n : ℤ)) ⟶ 𝓘.obj ⟨n⟩)
    (hf : ∀ n : ℕ, QuasiIso (f n))
    (hcompat : ∀ n : ℕ,
      K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ f (n + 1) ≫ 𝓘.map (homOfLE (Nat.le_succ n)).op =
        K.πTruncGE (-(n : ℤ)) ≫ f n)
    (h𝓘 : ∀ n : ℕ, (𝓘.obj ⟨n⟩).IsKInjective)
    (hsplit : ∀ (n : ℕ) (i : ℤ), IsSplitEpi ((𝓘.map (homOfLE (Nat.le_succ n)).op).f i))
    [HasLimit 𝓘] (γ : K ⟶ limit 𝓘)
    (hγ : ∀ n : ℕ, γ ≫ limit.π 𝓘 ⟨n⟩ = K.πTruncGE (-(n : ℤ)) ≫ f n)
    (B : Set C) (d : ℕ)
    (hB : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{u} U, 𝒰.sieve₀ ∈ J U ∧ ∀ i, B (𝒰.X i))
    (hvan : ∀ V : C, B V → ∀ p : ℕ, d < p → ∀ q : ℤ, q < 0 →
      IsZero (moduleCohomology O V p
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) q).obj
          (DerivedCategory.Q.obj K)))) :
    QuasiIso γ := by
  obtain ⟨_, hprod, _, _, hmain⟩ :=
    CochainComplex.isKInjective_limit_and_isDerivedLimit_of_isSplitEpi 𝓘 h𝓘 hsplit
  obtain ⟨γ₀, hγ₀, hiff⟩ := hmain K f hf hcompat
  rw [show γ = γ₀ from limit.hom_ext fun ⟨n⟩ ↦ by rw [hγ n, hγ₀ n]]
  refine hiff.mpr fun L c p δ hT hc ↦ ?_
  have hπG (n : ℕ) :
      (DerivedCategory.TStructure.t.truncGEπ
            (-((n + 1 : ℕ) : ℤ))).app (DerivedCategory.Q.obj K) ≫
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O)
            (DerivedCategory.Q.obj K)).map (homOfLE (Nat.le_succ n)).op =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app (DerivedCategory.Q.obj K) := by
    rw [Stacks.DerivedLimit.truncGETower_map_homOfLE_succ]
    exact DerivedCategory.TStructure.t.π_natTransTruncGEOfLE_app
      (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega) (DerivedCategory.Q.obj K)
  have hlad (n : ℕ) :
      (DerivedCategory.TStructure.t.truncGEπ
            (-((n + 1 : ℕ) : ℤ))).app (DerivedCategory.Q.obj K) ≫
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O)
              (DerivedCategory.Q.obj K)).map (homOfLE (Nat.le_succ n)).op ≫
            (truncGEQIso K (-(n : ℤ))).hom ≫ DerivedCategory.Q.map (f n) =
        (DerivedCategory.TStructure.t.truncGEπ
            (-((n + 1 : ℕ) : ℤ))).app (DerivedCategory.Q.obj K) ≫
          ((truncGEQIso K (-((n + 1 : ℕ) : ℤ))).hom ≫ DerivedCategory.Q.map (f (n + 1))) ≫
            DerivedCategory.Q.map (𝓘.map (homOfLE (Nat.le_succ n)).op) := by
    have hL : (DerivedCategory.TStructure.t.truncGEπ
            (-((n + 1 : ℕ) : ℤ))).app (DerivedCategory.Q.obj K) ≫
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O)
              (DerivedCategory.Q.obj K)).map (homOfLE (Nat.le_succ n)).op ≫
            (truncGEQIso K (-(n : ℤ))).hom ≫ DerivedCategory.Q.map (f n) =
          DerivedCategory.Q.map (K.πTruncGE (-(n : ℤ)) ≫ f n) := by
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun z ↦ z ≫ (truncGEQIso K (-(n : ℤ))).hom ≫
        DerivedCategory.Q.map (f n)) (hπG n)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun z ↦ z ≫ DerivedCategory.Q.map (f n))
        (truncGEπ_comp_truncGEQIso_hom K (-(n : ℤ)))).trans ?_
      exact (DerivedCategory.Q.map_comp _ _).symm
    have hR : (DerivedCategory.TStructure.t.truncGEπ
            (-((n + 1 : ℕ) : ℤ))).app (DerivedCategory.Q.obj K) ≫
          ((truncGEQIso K (-((n + 1 : ℕ) : ℤ))).hom ≫ DerivedCategory.Q.map (f (n + 1))) ≫
            DerivedCategory.Q.map (𝓘.map (homOfLE (Nat.le_succ n)).op) =
          DerivedCategory.Q.map (K.πTruncGE (-(n : ℤ)) ≫ f n) := by
      rw [Category.assoc, reassoc_of% (truncGEπ_comp_truncGEQIso_hom K _), ← Functor.map_comp,
        ← Functor.map_comp, hcompat]
    exact hL.trans hR.symm
  let E : DerivedCategory (SheafOfModules.{u} O) := DerivedCategory.Q.obj K
  let G : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} O) :=
    Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E
  let H : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} O) := 𝓘 ⋙ DerivedCategory.Q
  let b (n : ℕ) : G.obj ⟨n⟩ ⟶ DerivedCategory.Q.obj (K.truncGE (-(n : ℤ))) :=
    (truncGEQIso K (-(n : ℤ))).hom
  let a (n : ℕ) : G.obj ⟨n⟩ ⟶ H.obj ⟨n⟩ := b n ≫ DerivedCategory.Q.map (f n)
  have ha (n : ℕ) : IsIso (a n) := by
    have := hf n
    exact IsIso.comp_isIso' (truncGEQIso K (-(n : ℤ))).isIso_hom inferInstance
  have ha_step (n : ℕ) : G.map (homOfLE (Nat.le_succ n)).op ≫ a n =
      a (n + 1) ≫ H.map (homOfLE (Nat.le_succ n)).op := by
    have := ha n
    have h₀ : DerivedCategory.TStructure.t.IsGE (G.obj ⟨n⟩) (-(n : ℤ)) := by
      change DerivedCategory.TStructure.t.IsGE
        ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E) (-(n : ℤ))
      infer_instance
    have h₁ : DerivedCategory.TStructure.t.IsGE (H.obj ⟨n⟩) (-(n : ℤ)) :=
      DerivedCategory.TStructure.t.isGE_of_iso (asIso (a n)) _
    have h₂ : DerivedCategory.TStructure.t.IsGE (H.obj ⟨n⟩) (-((n + 1 : ℕ) : ℤ)) :=
      DerivedCategory.TStructure.t.isGE_of_ge (H.obj ⟨n⟩) (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
        (by omega)
    exact DerivedCategory.TStructure.t.from_truncGE_obj_ext (hlad n)
  let ainv (n : ℕ) : H.obj ⟨n⟩ ⟶ G.obj ⟨n⟩ := inv (a n)
  let e : Discrete.functor (fun n : ℕ ↦ H.obj ⟨n⟩) ≅ Discrete.functor (fun n : ℕ ↦ G.obj ⟨n⟩) :=
    Discrete.natIso fun n ↦ asIso (ainv n.as)
  have hprodG : HasProduct fun n : ℕ ↦ G.obj ⟨n⟩ := hasLimit_of_iso e
  let p' : L ⟶ ∏ᶜ fun n : ℕ ↦ G.obj ⟨n⟩ := p ≫ CategoryTheory.Limits.Pi.map fun n : ℕ ↦ ainv n
  have hp' : ∃ δ', Triangle.mk p'
      (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op) δ' ∈
      distTriang _ := by
    let q : (∏ᶜ fun n : ℕ ↦ H.obj ⟨n⟩) ≅ ∏ᶜ fun n : ℕ ↦ G.obj ⟨n⟩ :=
      { hom := CategoryTheory.Limits.Pi.map fun n : ℕ ↦ ainv n
        inv := CategoryTheory.Limits.Pi.map fun n : ℕ ↦ a n
        hom_inv_id := by ext n; simp [ainv, a]
        inv_hom_id := by ext n; simp [ainv, a] }
    have hstep (n : ℕ) : H.map (homOfLE (Nat.le_succ n)).op ≫ ainv n =
        ainv (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op := by
      have := ha n
      have := ha (n + 1)
      calc H.map (homOfLE (Nat.le_succ n)).op ≫ ainv n =
            (ainv (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op ≫ a n) ≫ ainv n := by
              rw [ha_step n]; simp [ainv, a, Category.assoc]
        _ = ainv (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op := by
              simp [ainv, a, Category.assoc]
    let sG := Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op
    let sH := Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ H.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ H.obj ⟨n⟩) (n + 1) ≫ H.map (homOfLE (Nat.le_succ n)).op
    have hs : sH ≫ q.hom = q.hom ≫ sG := by
      refine Pi.hom_ext _ _ fun n ↦ ?_
      simp only [q, sH, sG, Category.assoc, Pi.map_π, Pi.map_π_assoc, Pi.lift_comp_π,
        Pi.lift_comp_π_assoc, Preadditive.comp_sub, Preadditive.sub_comp]
      rw [hstep n]
    refine ⟨q.inv ≫ δ, isomorphic_distinguished _ hT _
      (Triangle.isoMk (Triangle.mk p sH δ) (Triangle.mk p' sG (q.inv ≫ δ))
        (Iso.refl _) q q (by simp [p', q]) hs (by simp)).symm⟩
  obtain ⟨δ', hT'⟩ := hp'
  have hc' (n : ℕ) : c ≫ p' ≫ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) n =
      (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E := by
    have hcancel : DerivedCategory.Q.map (f n) ≫ ainv n = (truncGEQIso K (-(n : ℤ))).inv := by
      have := ha n
      refine (cancel_epi (truncGEQIso K (-(n : ℤ))).hom).1 ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact (IsIso.hom_inv_id (a n)).trans (truncGEQIso K (-(n : ℤ))).hom_inv_id.symm
    have h1 : c ≫ p' ≫ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) n =
        (c ≫ p ≫ Pi.π (fun n : ℕ ↦ H.obj ⟨n⟩) n) ≫ ainv n := by
      simp [p', H, Category.assoc, Pi.map_π, Functor.comp_obj]
    refine h1.trans ((congrArg (· ≫ ainv n) (hc n)).trans ?_)
    rw [Functor.map_comp, Category.assoc, hcancel]
    exact Q_map_πTruncGE_comp_truncGEQIso_inv K (-(n : ℤ))
  exact isIso_to_isDerivedLimit_truncGETower_of_cohomology_vanishing O E (d : ℤ)
    (by omega) B hB
    (fun V hV p hp q hq ↦ hvan V hV p (by exact_mod_cast hp) q hq)
    L p' ⟨δ', hT'⟩ c hc'

end Stacks.Cohomology

end
