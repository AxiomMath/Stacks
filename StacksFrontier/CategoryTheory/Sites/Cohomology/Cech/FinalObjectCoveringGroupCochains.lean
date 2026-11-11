module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FinalObjectCovering
public import StacksFrontier.RingTheory.GroupCohomology.TrivialCochainPairing

/-!
# Čech cochains of an object with a group of automorphisms and group cochains

Let `U` be an object of a category whose finite powers `U^{n+1}` exist, and let `τ : G → End(U)`
be a multiplicative map from a group. A tuple `t = (t₁, …, tₙ)` of elements of `G` gives the
morphism

`σ_t = (1, τ(t₁), τ(t₁t₂), …, τ(t₁⋯tₙ)) : U ⟶ U^{n+1}`

whose components are the partial products of `t`. For a presheaf `P` on which `τ` acts trivially
(`P(τ(g)) = 1` for every `g`), restricting along `σ_t` sends the Čech complex of `P` for `U` to the
complex of inhomogeneous cochains of `G` with coefficients in `P(U)`, for the trivial action: the
faces of the Čech nerve become the faces of the bar construction, because dropping the `j`-th
partial product is taking the partial products of the tuple whose `j`-th and `(j+1)`-th entries
are multiplied (`Fin.partialProd_contractNth`), and dropping the first one is translating by
`τ(t₁)`.

This is the comparison behind Stacks 07DC: for the classifying stack of a finite group over an
affine scheme, with `U` the trivial torsor, `G = Aut(U)`.

## Main definitions

* `Stacks.CechTop.groupCochainPoint`: the morphism `σ_t : U ⟶ U^{n+1}`.

## Main results

* `Stacks.CechTop.groupCochainPoint_δ_zero`, `Stacks.CechTop.groupCochainPoint_δ_succ`: the faces
  of the Čech nerve on the `σ_t`.
* `Stacks.CechTop.map_groupCochainPoint_cechComplex_d`: restriction along the `σ_t` turns the
  Čech differential into the trivial coboundary
  `Stacks.GroupCohomology.TrivialCochains.trivialCoboundary`.

## References

* [Stacks Project, Tag 07DC](https://stacks.math.columbia.edu/tag/07DC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u u'

namespace Stacks.CechTop

variable {C : Type u'} [Category.{u} C] (U : C) [∀ n : ℕ, HasProduct (fun _ : Fin (n + 1) => U)]
  {G : Type*} [Group G] (τ : G → (U ⟶ U))

/-- **The morphism `σ_t = (1, τ(t₁), τ(t₁t₂), …) : U ⟶ U^{n+1}`** attached to a tuple `t` of
elements of `G`: its components are `τ` of the partial products of `t`. -/
def groupCochainPoint (n : ℕ) (t : Fin n → G) : U ⟶ (cechNerve U).obj (op ⦋n⦌) :=
  Pi.lift fun i => τ (Fin.partialProd t i)

/-- The `i`-th component of `σ_t` is `τ` of the `i`-th partial product of `t`. -/
@[reassoc (attr := simp)]
theorem groupCochainPoint_π (n : ℕ) (t : Fin n → G) (i : Fin (n + 1)) :
    groupCochainPoint U τ n t ≫ cechπ U n i = τ (Fin.partialProd t i) :=
  Pi.lift_comp_π _ _

/-- **Dropping a later vertex**: the face `δ (a + 1)` of the Čech nerve sends `σ_t` to `σ` of the
tuple in which the `a`-th and `(a + 1)`-th entries of `t` are multiplied. -/
theorem groupCochainPoint_δ_succ (n : ℕ) (t : Fin (n + 1) → G) (a : Fin (n + 1)) :
    groupCochainPoint U τ (n + 1) t ≫ (cechNerve U).map (SimplexCategory.δ a.succ).op =
      groupCochainPoint U τ n (Fin.contractNth a (· * ·) t) := by
  refine cechNerve_hom_ext U fun i => ?_
  rw [Category.assoc, cechNerve_map_cechπ, groupCochainPoint_π, groupCochainPoint_π,
    Fin.partialProd_contractNth]
  rfl

variable {τ} in
/-- **Dropping the first vertex**: the face `δ 0` of the Čech nerve sends `σ_t` to `σ` of the
tail of `t`, translated by `τ(t₁)`. -/
theorem groupCochainPoint_δ_zero (hτ : ∀ a b, τ (a * b) = τ a ≫ τ b) (n : ℕ)
    (t : Fin (n + 1) → G) :
    groupCochainPoint U τ (n + 1) t ≫ (cechNerve U).map (SimplexCategory.δ 0).op =
      τ (t 0) ≫ groupCochainPoint U τ n (Fin.tail t) := by
  refine cechNerve_hom_ext U fun i => ?_
  rw [Category.assoc, cechNerve_map_cechπ, groupCochainPoint_π, Category.assoc,
    groupCochainPoint_π, ← hτ, ← Fin.partialProd_succ']
  rfl

variable {τ} in
/-- **Restriction along the `σ_t` turns the Čech differential into the trivial coboundary.** Let
`τ : G → End(U)` be multiplicative and let `P` be a presheaf of abelian groups on which every
`τ(g)` acts trivially. For a Čech `n`-cochain `x` of `P` and `t ∈ G^{n+1}`,
`σ_t^*(dx) = (d c)(t)` where `c` is the `G`-cochain `t' ↦ σ_{t'}^* x` with values in `P(U)` and
`d` the coboundary of inhomogeneous cochains for the trivial action. -/
theorem map_groupCochainPoint_cechComplex_d (hτ : ∀ a b, τ (a * b) = τ a ≫ τ b)
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (hP : ∀ g, P.map (τ g).op = 𝟙 _) (n : ℕ)
    (x : P.obj (op ((cechNerve U).obj (op ⦋n⦌)))) (t : Fin (n + 1) → G) :
    P.map (groupCochainPoint U τ (n + 1) t).op ((cechComplex U P).d n (n + 1) x) =
      Stacks.GroupCohomology.TrivialCochains.trivialCoboundary (P.obj (op U)) n
        (fun t' => P.map (groupCochainPoint U τ n t').op x) t := by
  have hface : ∀ (i : Fin (n + 2)), P.map (groupCochainPoint U τ (n + 1) t).op
      (P.map ((cechNerve U).map (SimplexCategory.δ i).op).op x) =
        P.map (groupCochainPoint U τ (n + 1) t ≫
          (cechNerve U).map (SimplexCategory.δ i).op).op x := by
    intro i
    rw [op_comp, Functor.map_comp, AddCommGrpCat.comp_apply]
  have hd : (cechComplex U P).d n (n + 1) x = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      P.map ((cechNerve U).map (SimplexCategory.δ i).op).op x := by
    rw [cechComplex_d]
    have hsum : ∀ (s : Finset (Fin (n + 2)))
        (g : Fin (n + 2) → (P.obj (op ((cechNerve U).obj (op ⦋n⦌))) ⟶
          P.obj (op ((cechNerve U).obj (op ⦋n + 1⦌))))),
        (∑ i ∈ s, g i) x = ∑ i ∈ s, g i x := by
      intro s g
      induction s using Finset.cons_induction with
      | empty => rfl
      | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, AddCommGrpCat.hom_add_apply, ih]
    exact hsum Finset.univ _
  rw [hd, map_sum, Fin.sum_univ_succ,
    Stacks.GroupCohomology.TrivialCochains.trivialCoboundary_apply]
  congr 1
  · rw [map_zsmul, hface, groupCochainPoint_δ_zero U hτ, op_comp,
      Functor.map_comp, AddCommGrpCat.comp_apply, hP]
    simp
    rfl
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_zsmul, hface, groupCochainPoint_δ_succ]
    simp

/-! ### Homology classes of the Čech complex over a base ring -/

section Site

open Stacks.Cohomology.SiteModules

variable {J : GrothendieckTopology C} (O : Sheaf J RingCat.{u}) {A : Type u} [CommRing A]
  (ρ : A →+* GlobalSectionRing O) (M : SheafOfModules.{u} O)

/-- **A degree-`m` Čech cocycle and a linear form on `m`-cochains killing the coboundaries give
a homology class and a linear form on the Čech cohomology**, with the value of the form on the
class the value on the cocycle. -/
theorem exists_homology_cechFunctorOverBase_linearMap (m i : ℕ)
    (hi : (ComplexShape.up ℕ).prev m = i)
    (z : (cechComplexOverBase U O ρ M).X m)
    (hz : (cechComplexOverBase U O ρ M).d m (m + 1) z = 0)
    (L : (cechComplexOverBase U O ρ M).X m ⟶ sectionsOverBaseObj O ρ M (op U))
    (hL : ∀ y, L ((cechComplexOverBase U O ρ M).d i m y) = 0) :
    ∃ (e : ((cechFunctorOverBase U O ρ).obj M).homology m)
      (ψ : ((cechFunctorOverBase U O ρ).obj M).homology m ⟶
        (ModuleCat.uliftFunctor.{u'} A).obj (sectionsOverBaseObj O ρ M (op U))),
      ψ e = ULift.up (L z) := by
  set K := ((cechFunctorOverBase U O ρ).obj M)
  let g : K.X m ⟶ (ModuleCat.uliftFunctor.{u'} A).obj (sectionsOverBaseObj O ρ M (op U)) :=
    (ModuleCat.uliftFunctor.{u'} A).map L
  have hg : K.d i m ≫ g = 0 := by
    have h0 : (cechComplexOverBase U O ρ M).d i m ≫ L = 0 := by
      ext y
      exact hL y
    change (ModuleCat.uliftFunctor.{u'} A).map ((cechComplexOverBase U O ρ M).d i m) ≫
      (ModuleCat.uliftFunctor.{u'} A).map L = 0
    rw [← Functor.map_comp, h0, Functor.map_zero]
  have hx : ((forget₂ (ModuleCat A) Ab).map (K.d m (m + 1)))
      (ULift.up z : (forget₂ (ModuleCat A) Ab).obj (K.X m)) = 0 := by
    change ULift.up ((cechComplexOverBase U O ρ M).d m (m + 1) z) = ULift.up 0
    rw [hz]
  let Ψ := K.homologyι m ≫ K.descOpcycles g i hi hg
  refine ⟨K.homologyπ m (K.cyclesMk (ULift.up z) (m + 1) (by simp) hx), Ψ, ?_⟩
  have h : K.homologyπ m ≫ Ψ = K.iCycles m ≫ g := by
    simp only [Ψ, HomologicalComplex.homology_π_ι_assoc, HomologicalComplex.p_descOpcycles]
  have h' := congrArg (fun φ => φ (K.cyclesMk (ULift.up z) (m + 1) (by simp) hx)) h
  simp only [ModuleCat.comp_apply] at h'
  refine h'.trans ?_
  have hi' := K.i_cyclesMk (ULift.up z : (forget₂ (ModuleCat A) Ab).obj (K.X m)) (m + 1)
    (by simp) hx
  change g (K.iCycles m (K.cyclesMk (ULift.up z) (m + 1) (by simp) hx)) = _
  rw [show K.iCycles m (K.cyclesMk (ULift.up z) (m + 1) (by simp) hx) = ULift.up z from hi']
  rfl

variable {U τ}

open Stacks.GroupCohomology.TrivialCochains in
/-- **A group cocycle with a dual weight gives a Čech class with a linear form.** Let `τ` act
trivially on a sheaf of modules `M`, and suppose that restriction along the `σ_t` identifies the
Čech `(n+1)`-cochains of `M` with the `G`-cochains valued in `M(U)` (surjective in degree `n + 1`,
injective in degree `n + 2`). A trivial cocycle `c` and weights `ℓ` killing the coboundaries with
`⟨ℓ, c⟩ = 1` give, for every `r ∈ M(U)`, a class `e` in the `(n+1)`-st Čech cohomology and an
`A`-linear form `ψ` to `M(U)` with `ψ e = r`. -/
theorem exists_homology_cechFunctorOverBase_succ [Fintype G]
    (hτ : ∀ a b, τ (a * b) = τ a ≫ τ b) (hM : ∀ g, M.val.presheaf.map (τ g).op = 𝟙 _) (n : ℕ)
    (hinj : ∀ x : M.val.obj (op ((cechNerve U).obj (op ⦋n + 2⦌))),
      (∀ t, M.val.map (groupCochainPoint U τ (n + 2) t).op x = 0) → x = 0)
    (hsurj : ∀ v : (Fin (n + 1) → G) → M.val.obj (op U),
      ∃ x : M.val.obj (op ((cechNerve U).obj (op ⦋n + 1⦌))),
        ∀ t, M.val.map (groupCochainPoint U τ (n + 1) t).op x = v t)
    (c ℓ : (Fin (n + 1) → G) → A) (hc : trivialCoboundary A (n + 1) c = 0)
    (hℓ : ∀ w : (Fin n → G) → A, pairing ℓ (trivialCoboundary A n w) = 0)
    (hcℓ : pairing ℓ c = 1) (r : M.val.obj (op U)) :
    ∃ (e : ((cechFunctorOverBase U O ρ).obj M).homology (n + 1))
      (ψ : ((cechFunctorOverBase U O ρ).obj M).homology (n + 1) ⟶
        (ModuleCat.uliftFunctor.{u'} A).obj (sectionsOverBaseObj O ρ M (op U))),
      ψ e = ULift.up r := by
  classical
  obtain ⟨x, hx⟩ := hsurj fun t =>
    @HSMul.hSMul (O.obj.obj (op U)) (M.val.obj (op U)) (M.val.obj (op U)) _
      (baseToSections O ρ (op U) (c t)) r
  let _ : Module A (M.val.presheaf.obj (op U)) :=
    Module.compHom (M.val.obj (op U)) (baseToSections O ρ (op U))
  let r' : M.val.presheaf.obj (op U) := r
  have h2 : (fun t' => M.val.presheaf.map (groupCochainPoint U τ (n + 1) t').op x) =
      fun t' => c t' • r' := funext fun t' => (hx t' :)
  have hdx : (cechComplexOverBase U O ρ M).d (n + 1) (n + 2) x = 0 := by
    refine hinj _ fun t => ?_
    have h := map_groupCochainPoint_cechComplex_d U hτ M.val.presheaf hM (n + 1) x t
    rw [h2, trivialCoboundary_smul_right_eq_zero c hc] at h
    exact (congrArg (fun z => (M.val.map (groupCochainPoint U τ (n + 2) t).op).hom z)
      (cechComplexOverBase_d_apply U O ρ M (n + 1)
        (show (cechComplexOverBase U O ρ M).X (n + 1) from x))).trans h
  let L : (sectionsOverBase O ρ M).obj (op ((cechNerve U).obj (op ⦋n + 1⦌))) ⟶
      (sectionsOverBase O ρ M).obj (op U) :=
    ∑ t, ℓ t • (sectionsOverBase O ρ M).map (groupCochainPoint U τ (n + 1) t).op
  have hLapply : ∀ y : (sectionsOverBase O ρ M).obj (op ((cechNerve U).obj (op ⦋n + 1⦌))),
      L y = ∑ t, ℓ t • (M.val.presheaf.map (groupCochainPoint U τ (n + 1) t).op y :
        M.val.presheaf.obj (op U)) := by
    intro y
    change (∑ t, ℓ t • (sectionsOverBase O ρ M).map (groupCochainPoint U τ (n + 1) t).op).hom y = _
    rw [ModuleCat.hom_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [ModuleCat.hom_smul, LinearMap.smul_apply]
    rfl
  obtain ⟨e, ψ, he⟩ := exists_homology_cechFunctorOverBase_linearMap U O ρ M (n + 1) n (by simp)
    x hdx L (fun y => by
      refine (hLapply _).trans ?_
      have key := pairing_trivialCoboundary_eq_zero (R := M.val.presheaf.obj (op U)) ℓ hℓ
        (fun t' => M.val.presheaf.map (groupCochainPoint U τ n t').op y)
      rw [← funext (map_groupCochainPoint_cechComplex_d U hτ M.val.presheaf hM n y)] at key
      refine Eq.trans ?_ key
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [cechComplexOverBase_d_apply])
  refine ⟨e, ψ, he.trans ?_⟩
  congr 1
  refine (hLapply x).trans ?_
  have key := pairing_smul_right_of_eq_one (R := M.val.presheaf.obj (op U)) ℓ c hcℓ r'
  refine Eq.trans ?_ key
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [show M.val.presheaf.map (groupCochainPoint U τ (n + 1) t).op x = c t • r' from
    congrFun h2 t]

open Stacks.GroupCohomology.TrivialCochains in
/-- **The Čech class of a global section in degree zero.** If restriction along the `σ_t`
is surjective on Čech `0`-cochains and injective on Čech `1`-cochains, then every `r ∈ M(U)` is
the value of an `A`-linear form on the degree-zero Čech cohomology at a class. -/
theorem exists_homology_cechFunctorOverBase_zero (hτ : ∀ a b, τ (a * b) = τ a ≫ τ b)
    (hM : ∀ g, M.val.presheaf.map (τ g).op = 𝟙 _)
    (hinj : ∀ x : M.val.obj (op ((cechNerve U).obj (op ⦋1⦌))),
      (∀ t, M.val.map (groupCochainPoint U τ 1 t).op x = 0) → x = 0)
    (hsurj : ∀ v : (Fin 0 → G) → M.val.obj (op U),
      ∃ x : M.val.obj (op ((cechNerve U).obj (op ⦋0⦌))),
        ∀ t, M.val.map (groupCochainPoint U τ 0 t).op x = v t)
    (r : M.val.obj (op U)) :
    ∃ (e : ((cechFunctorOverBase U O ρ).obj M).homology 0)
      (ψ : ((cechFunctorOverBase U O ρ).obj M).homology 0 ⟶
        (ModuleCat.uliftFunctor.{u'} A).obj (sectionsOverBaseObj O ρ M (op U))),
      ψ e = ULift.up r := by
  obtain ⟨x, hx⟩ := hsurj fun _ => r
  let r' : M.val.presheaf.obj (op U) := r
  have h2 : (fun t' => M.val.presheaf.map (groupCochainPoint U τ 0 t').op x) = fun _ => r' :=
    funext fun t' => (hx t' :)
  have hdx : (cechComplexOverBase U O ρ M).d 0 1 x = 0 := by
    refine hinj _ fun t => ?_
    have h := map_groupCochainPoint_cechComplex_d U hτ M.val.presheaf hM 0 x t
    have h0 : r' + ∑ j : Fin (0 + 1), ((-1 : ℤ) ^ ((j : ℕ) + 1)) • r' = 0 := by
      rw [Fin.sum_univ_one]
      simp only [Fin.val_zero, zero_add, pow_one]
      abel
    rw [h2, trivialCoboundary_apply, h0] at h
    exact (congrArg (fun z => (M.val.map (groupCochainPoint U τ 1 t).op).hom z)
      (cechComplexOverBase_d_apply U O ρ M 0
        (show (cechComplexOverBase U O ρ M).X 0 from x))).trans h
  let t₀ : Fin 0 → G := Fin.elim0
  let L : (cechComplexOverBase U O ρ M).X 0 ⟶ sectionsOverBaseObj O ρ M (op U) :=
    (sectionsOverBase O ρ M).map (groupCochainPoint U τ 0 t₀).op
  obtain ⟨e, ψ, he⟩ := exists_homology_cechFunctorOverBase_linearMap U O ρ M 0 0 (by simp)
    x hdx L (fun y => by
      rw [(cechComplexOverBase U O ρ M).shape 0 0 (by simp)]
      simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero])
  exact ⟨e, ψ, he.trans (congrArg ULift.up (hx t₀))⟩

end Site

end Stacks.CechTop
