module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.Deformation.ToposThickening.FinitePresentationFlatLift

/-!
# A relation with coefficients in an ideal, over a flat stalk, is locally trivial

Let `N` be a presheaf of modules over a presheaf of commutative rings `O` on a space `X`, let
`x` be a point, and let `A` be a ring acting on the stalk `N_x` through a ring map
`σ : A ⟶ O_x` and on the sections of `N` through a ring map `α : A ⟶ O(X)` compatible with `σ`.
If `N_x` is flat over `A`, then a relation `∑ α(b_k) t_k = 0` among global sections `t_k` with
coefficients `b_k` in an ideal `J ⊆ A` is trivial near `x` in the following sense: on some open
neighbourhood `V` of `x`, every biadditive map `β : J × N(V) → P` balanced over `A` kills
`∑ b_k ⊗ t_k|_V`.  For `β` the tensor product this is the vanishing of `∑ b_k ⊗ t_k|_V` in
`J ⊗_A N(V)`.

The proof is the equational criterion for vanishing of tensors: flatness makes
`∑ b_k ⊗ germ(t_k)` vanish in `J ⊗_A N_x`, the criterion writes this vanishing through finitely
many relations in `N_x`, and those relations hold on a neighbourhood of `x`.

## Main results

* `AlgebraicGeometry.sum_balanced_eq_zero_of_relations`: an expression which vanishes trivially
  is killed by every balanced biadditive map.
* `AlgebraicGeometry.exists_mem_sum_balanced_eq_zero_of_flat_stalk`: the statement above.

## References

* [Stacks Project, Tag 00HK](https://stacks.math.columbia.edu/tag/00HK)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace TensorProduct

universe u

namespace AlgebraicGeometry

/-- **An expression that vanishes trivially is killed by every balanced biadditive map.**  If
`e_j = ∑_κ a_{jκ} f_κ`, `∑_κ a'_{lκ} f_κ = 0` and `∑_j a_{jκ} y_j + ∑_l a'_{lκ} z_l = 0`, then
`∑_j β(e_j, y_j) = 0` for every biadditive `β` with `β(r e, y) = β(e, r y)`. -/
theorem sum_balanced_eq_zero_of_relations {A : Type*} [CommRing A] {P : Type*} [AddCommGroup P]
    [Module A P] {Q : Type*} [AddCommGroup Q] [Module A Q] {G : Type*} [AddCommGroup G]
    (β : P →+ Q →+ G) (hβ : ∀ (r : A) (p : P) (q : Q), β (r • p) q = β p (r • q))
    {n r k : ℕ} (e : Fin n → P) (y : Fin n → Q) (z : Fin r → Q) (a : Fin n → Fin k → A)
    (a' : Fin r → Fin k → A) (f : Fin k → P) (he : ∀ j, e j = ∑ κ, a j κ • f κ)
    (ha' : ∀ l, ∑ κ, a' l κ • f κ = 0)
    (hrel : ∀ κ, ∑ j, a j κ • y j + ∑ l, a' l κ • z l = 0) :
    ∑ j, β (e j) (y j) = 0 := by
  have h1 : ∑ j, β (e j) (y j) = ∑ κ, β (f κ) (∑ j, a j κ • y j) := by
    simp_rw [he, map_sum, AddMonoidHom.finsetSum_apply, hβ]
    rw [Finset.sum_comm]
  have h2 : ∀ κ, ∑ j, a j κ • y j = -∑ l, a' l κ • z l := fun κ =>
    eq_neg_of_add_eq_zero_left (hrel κ)
  simp_rw [h1, h2, map_neg, map_sum, ← hβ, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  simp_rw [← AddMonoidHom.finsetSum_apply, ← map_sum, ha', map_zero, AddMonoidHom.zero_apply,
    Finset.sum_const_zero, neg_zero]

section Stalk

variable {X : TopCat.{u}} {O : X.Presheaf CommRingCat.{u}}
  (N : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat)) (x : X)

/-- The restriction of the sections of `O` from `X` to an open `V`. -/
noncomputable abbrev topRestr (V : Opens X) : O.obj (op ⊤) →+* O.obj (op V) :=
  (O.map (homOfLE le_top).op).hom

/-- The germ of a scalar multiple, with the scalar read through a ring map compatible with the
germ map. -/
theorem germ_smul_of_compat {A : Type u} [CommRing A] (α : A →+* O.obj (op ⊤))
    (σ : A →+* O.stalk x) (hσ : ∀ r, σ r = O.germ ⊤ x trivial (α r)) (V : Opens X) (hV : x ∈ V)
    (r : A) (m : N.obj (op V)) :
    letI : Module A (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x) :=
      Module.compHom _ σ
    TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf V x hV
        ((show (O ⋙ forget₂ CommRingCat RingCat).obj (op V) from topRestr V (α r)) • m) =
      r • TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf V x hV m := by
  let : Module A (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x) :=
    Module.compHom _ σ
  rw [PresheafOfModules.germ_smul]
  show _ = σ r • (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf V x hV m)
  rw [hσ, ← TopCat.Presheaf.germ_res_apply O (homOfLE le_top) x hV]

/-- Restriction of sections of a presheaf of modules along an inclusion of opens, with its
target spelled as the sections over the smaller open. -/
noncomputable def presheafRes {U V : Opens X} (h : V ≤ U) (m : N.obj (op U)) : N.obj (op V) :=
  N.map (homOfLE h).op m

/-- Restriction sends the zero section to zero. -/
theorem presheafRes_zero {U V : Opens X} (h : V ≤ U) : presheafRes N h 0 = 0 :=
  map_zero (N.map (homOfLE h).op).hom

/-- Restriction of sections is additive. -/
theorem presheafRes_add {U V : Opens X} (h : V ≤ U) (m m' : N.obj (op U)) :
    presheafRes N h (m + m') = presheafRes N h m + presheafRes N h m' :=
  map_add (N.map (homOfLE h).op).hom m m'

/-- Restriction of sections commutes with finite sums. -/
theorem presheafRes_sum {U V : Opens X} (h : V ≤ U) {ι : Type*} (s : Finset ι)
    (m : ι → N.obj (op U)) : presheafRes N h (∑ i ∈ s, m i) = ∑ i ∈ s, presheafRes N h (m i) :=
  map_sum (N.map (homOfLE h).op).hom m s

/-- Restricting from `U` to `V` and then from `V` to `W` is the restriction from `U` to `W`. -/
theorem presheafRes_res {U V W : Opens X} (h₁ : W ≤ V) (h₂ : V ≤ U) (m : N.obj (op U)) :
    presheafRes N h₁ (presheafRes N h₂ m) = presheafRes N (h₁.trans h₂) m :=
  (PresheafOfModules.map_comp_apply N (homOfLE h₂).op (homOfLE h₁).op m).symm

/-- Restricting a scalar multiple of a restricted section, with the scalar restricted from `X`. -/
theorem presheafRes_smul {V' V : Opens X} (h₁ : V ≤ V') (c : O.obj (op ⊤))
    (m : N.obj (op V')) :
    presheafRes N h₁
        ((show (O ⋙ forget₂ CommRingCat RingCat).obj (op V') from topRestr V' c) • m) =
      (show (O ⋙ forget₂ CommRingCat RingCat).obj (op V) from topRestr V c) •
        presheafRes N h₁ m := by
  unfold presheafRes
  rw [PresheafOfModules.map_smul]
  congr 1
  show (O.map (homOfLE h₁).op).hom ((O.map (homOfLE le_top).op).hom c) =
    (O.map (homOfLE le_top).op).hom c
  rw [← CommRingCat.comp_apply, ← O.map_comp]
  rfl

/-- A point lies in a finite infimum of opens if it lies in each of them. -/
private theorem mem_finset_univ_inf_of_forall {ι : Type*} [Fintype ι] {W : ι → Opens X} {x : X}
    (hW : ∀ i, x ∈ W i) : x ∈ Finset.univ.inf W := by
  have : x ∈ (↑(Finset.univ.inf W) : Set X) := by
    rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf]
    simp only [Function.comp_apply, Finset.mem_univ, iInf_pos, Set.iInf_eq_iInter,
      Set.mem_iInter]
    exact hW
  exact this

/-- The germ of a combination of sections with scalars read through `α` is the corresponding
combination of germs, with scalars acting through `σ`. -/
private theorem germ_sum_smul_add_sum_smul {A : Type u} [CommRing A] (α : A →+* O.obj (op ⊤))
    (σ : A →+* O.stalk x) (hσ : ∀ r, σ r = O.germ ⊤ x trivial (α r)) (V : Opens X) (hV : x ∈ V)
    {n r : ℕ} (c : Fin n → A) (d : Fin r → A) (u : Fin n → N.obj (op V))
    (v : Fin r → N.obj (op V)) :
    letI : Module A (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x) :=
      Module.compHom _ σ
    TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf V x hV
        (∑ j, (show (O ⋙ forget₂ CommRingCat RingCat).obj (op V) from topRestr V (α (c j))) •
            u j +
          ∑ l, (show (O ⋙ forget₂ CommRingCat RingCat).obj (op V) from topRestr V (α (d l))) •
            v l) =
      ∑ j, c j • TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf V x hV (u j) +
        ∑ l, d l • TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf V x hV (v l) := by
  refine (map_add (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf V x hV).hom
    _ _).trans ?_
  congr 1 <;>
    exact (map_sum (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf V x hV).hom
      _ _).trans (Finset.sum_congr rfl fun _ _ => germ_smul_of_compat N x α σ hσ V hV _ _)

/-- Over a flat stalk, a relation `∑ α(b_k) t_k = 0` with coefficients in `J` gives the vanishing
of `∑ b_k ⊗ germ(t_k)` in `J ⊗_A N_x`. -/
private theorem sum_tmul_germ_eq_zero_of_flat {A : Type u} [CommRing A]
    (α : A →+* O.obj (op ⊤)) (σ : A →+* O.stalk x)
    (hσ : ∀ r, σ r = O.germ ⊤ x trivial (α r))
    (hflat : letI : Module A (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x) :=
        Module.compHom _ σ
      Module.Flat A (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x))
    (J : Ideal A) {n : ℕ} (b : Fin n → J) (t : Fin n → N.obj (op ⊤))
    (hrel : ∑ k, (show (O ⋙ forget₂ CommRingCat RingCat).obj (op ⊤) from α (b k)) • t k = 0) :
    letI : Module A (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x) :=
      Module.compHom _ σ
    ∑ k, b k ⊗ₜ[A] TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf ⊤ x trivial (t k) =
      0 := by
  let : Module A (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x) :=
    Module.compHom _ σ
  have := hflat
  have h1 : ∑ k, (b k : A) •
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf ⊤ x trivial (t k) = 0 := by
    have h := ((map_sum (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf ⊤ x trivial).hom
      (fun k => (show (O ⋙ forget₂ CommRingCat RingCat).obj (op ⊤) from α (b k)) • t k)
      Finset.univ).symm.trans (congrArg _ hrel)).trans (map_zero _)
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h
    show σ (b k) • TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf ⊤ x trivial (t k) =
      _
    rw [hσ]
    exact (PresheafOfModules.germ_smul N x ⊤ trivial (α (b k)) (t k)).symm
  apply Module.Flat.rTensor_preserves_injective_linearMap
    (M := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x)
    J.subtype Subtype.val_injective
  rw [map_sum, map_zero]
  apply (TensorProduct.lid A
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x)).injective
  rw [map_sum, map_zero]
  simpa only [LinearMap.rTensor_tmul, Submodule.coe_subtype, TensorProduct.lid_tmul] using h1

/-- **A relation with coefficients in an ideal, over a flat stalk, is locally trivial.**  If the
stalk `N_x` is flat over `A` (acting through `σ`), and `∑ α(b_k) t_k = 0` with `b_k ∈ J`, then
on some open neighbourhood `V` of `x` every biadditive map `J × N(V) → P` balanced over `A`
(acting on `N(V)` through `α`) kills `∑ b_k ⊗ t_k|_V`. -/
theorem exists_mem_sum_balanced_eq_zero_of_flat_stalk {A : Type u} [CommRing A]
    (α : A →+* O.obj (op ⊤)) (σ : A →+* O.stalk x)
    (hσ : ∀ r, σ r = O.germ ⊤ x trivial (α r))
    (hflat : letI : Module A (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x) :=
        Module.compHom _ σ
      Module.Flat A (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x))
    (J : Ideal A) {n : ℕ} (b : Fin n → J) (t : Fin n → N.obj (op ⊤))
    (hrel : ∑ k, (show (O ⋙ forget₂ CommRingCat RingCat).obj (op ⊤) from α (b k)) • t k = 0) :
    ∃ (V : Opens X) (_ : x ∈ V), ∀ (P : Type u) [AddCommGroup P] (β : J →+ N.obj (op V) →+ P),
      (∀ (r : A) (c : J) (m : N.obj (op V)),
        β (r • c) m = β c ((show (O ⋙ forget₂ CommRingCat RingCat).obj (op V) from
          topRestr V (α r)) • m)) →
      ∑ k, β (b k) (N.map (homOfLE le_top).op (t k)) = 0 := by
  classical
  let : Module A (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x) :=
    Module.compHom _ σ
  obtain ⟨r, z, k, a, a', f, he, ha', hrel'⟩ :=
    Deformation.ToposThickening.exists_relations_of_sum_tmul_eq_zero b _
      (sum_tmul_germ_eq_zero_of_flat N x α σ hσ hflat J b t hrel)
  have hz : ∀ l, ∃ (U : Opens X) (hU : x ∈ U) (s : N.obj (op U)),
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf U x hU s = z l :=
    fun l => TopCat.Presheaf.exists_germ_eq N.presheaf (z l)
  choose Uz hUz sz hsz using hz
  let V₀ : Opens X := Finset.univ.inf Uz
  have hxV₀ : x ∈ V₀ := mem_finset_univ_inf_of_forall hUz
  have hV₀ : ∀ l, V₀ ≤ Uz l := fun l => Finset.inf_le (Finset.mem_univ l)
  let ρ : Fin k → N.obj (op V₀) := fun κ =>
    ∑ j, (show (O ⋙ forget₂ CommRingCat RingCat).obj (op V₀) from topRestr V₀ (α (a j κ))) •
        presheafRes N le_top (t j) +
      ∑ l, (show (O ⋙ forget₂ CommRingCat RingCat).obj (op V₀) from topRestr V₀ (α (a' l κ))) •
        presheafRes N (hV₀ l) (sz l)
  have hρ : ∀ κ, TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf V₀ x hxV₀ (ρ κ) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf V₀ x hxV₀ 0 := fun κ => by
    refine (germ_sum_smul_add_sum_smul N x α σ hσ V₀ hxV₀ _ _ _ _).trans
      (Eq.trans ?_ ((hrel' κ).trans (map_zero _).symm))
    congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_ <;> congr 1
    · exact TopCat.Presheaf.germ_res_apply N.presheaf (homOfLE le_top) x hxV₀ (t j)
    · exact (TopCat.Presheaf.germ_res_apply N.presheaf (homOfLE (hV₀ j)) x hxV₀ (sz j)).trans
        (hsz j)
  choose W hxW iW iW' hW using fun κ =>
    TopCat.Presheaf.germ_eq N.presheaf x hxV₀ hxV₀ (ρ κ) 0 (hρ κ)
  let V : Opens X := V₀ ⊓ Finset.univ.inf W
  have hVV₀ : V ≤ V₀ := inf_le_left
  have hVW : ∀ κ, V ≤ W κ := fun κ => inf_le_right.trans (Finset.inf_le (Finset.mem_univ κ))
  refine ⟨V, ⟨hxV₀, mem_finset_univ_inf_of_forall hxW⟩, fun P _ β hβ => ?_⟩
  let : Module A (N.obj (op V)) := Module.compHom _
    (show A →+* (O ⋙ forget₂ CommRingCat RingCat).obj (op V) from (topRestr V).comp α)
  have hrelV : ∀ κ, ∑ j, a j κ • presheafRes N le_top (t j) +
      ∑ l, a' l κ • presheafRes N (hVV₀.trans (hV₀ l)) (sz l) = 0 := by
    intro κ
    have h0 : presheafRes N hVV₀ (ρ κ) = 0 :=
      calc presheafRes N hVV₀ (ρ κ)
          = presheafRes N (hVW κ) (presheafRes N (iW κ).le (ρ κ)) :=
            (presheafRes_res N (hVW κ) (iW κ).le (ρ κ)).symm
        _ = presheafRes N (hVW κ) (presheafRes N (iW' κ).le 0) := congrArg _ (hW κ)
        _ = 0 := by rw [presheafRes_zero, presheafRes_zero]
    refine Eq.trans ?_ h0
    simp only [ρ]
    rw [presheafRes_add, presheafRes_sum, presheafRes_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun _ _ => ?_ <;>
      rw [presheafRes_smul, presheafRes_res] <;> rfl
  exact sum_balanced_eq_zero_of_relations β hβ b (fun j => presheafRes N le_top (t j))
    (fun l => presheafRes N (hVV₀.trans (hV₀ l)) (sz l)) a a' f he ha' hrelV

end Stalk

end AlgebraicGeometry

end
