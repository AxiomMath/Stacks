module

public import StacksFrontier.Algebra.Homology.AugmentedTowerLimitExact
public import StacksFrontier.CategoryTheory.Sites.CechToCohomology

/-!
# Čech cohomology of the limit of a tower of abelian sheaves with surjective transitions

Let `F₀ ← F₁ ← F₂ ← ⋯` be a tower of abelian sheaves on a site and `F = lim Fₙ`, the limit taken
in presheaves. Let `{Uᵢ ⟶ U}` be a covering family whose finite fibre products exist. If every
`Fₙ` has vanishing higher Čech cohomology on the covering, and the transition maps `Fₙ₊₁ ⟶ Fₙ` are
surjective on the sections over every object, then `F` has vanishing higher Čech cohomology on the
covering as well.

The Čech complex of `F` is the limit of the Čech complexes of the `Fₙ`, degreewise, because it is
built from products of sections. Each of those is exact in positive degrees, and augmented by
the sections over `U` exactly in degree zero, because `Fₙ` is a sheaf. The transition maps of the
complexes are products of transition maps of sections, hence surjective, so the Mittag-Leffler
argument `Stacks.AugmentedTower.exactAt_succ` applies.

This is the step of the proof of Stacks 0DEL which passes from the stages `Spec(A/Jₙ)` of a
countably indexed affine formal algebraic space to the space itself.

## Main results

* `Stacks.CechSite.isZero_cechCohomology_of_isLimit_tower`: the statement above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe a w v u

namespace Stacks.CechSite

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [HasProducts.{w} AddCommGrpCat.{a}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]

omit [HasProducts AddCommGrpCat] in
/-- A compatible family of elements of a tower of abelian groups lifts through a limit cone. -/
theorem exists_lift_of_isLimit_tower (G : ℕᵒᵖ ⥤ AddCommGrpCat.{a}) (c : Cone G) (hc : IsLimit c)
    (y : ∀ n, G.obj (op n)) (hy : ∀ n, G.map (homOfLE (Nat.le_succ n)).op (y (n + 1)) = y n) :
    ∃ x : c.pt, ∀ n, c.π.app (op n) x = y n := by
  have hc' := isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{a}) hc
  have hcomp : ∀ (i j : ℕ) (h : i ≤ j), G.map (homOfLE h).op (y j) = y i := by
    intro i j h
    induction j, h using Nat.le_induction with
    | base =>
      rw [show (homOfLE (le_refl i)).op = 𝟙 (op i) from rfl, G.map_id]
      rfl
    | succ j hij ih =>
      rw [show (homOfLE (hij.trans (Nat.le_succ j))).op =
          (homOfLE (Nat.le_succ j)).op ≫ (homOfLE hij).op from rfl, G.map_comp,
        ConcreteCategory.comp_apply, hy j, ih]
  let sec : (G ⋙ CategoryTheory.forget AddCommGrpCat.{a}).sections :=
    ⟨fun j ↦ y j.unop, fun {j j'} g ↦ hcomp j'.unop j.unop (leOfHom g.unop)⟩
  exact ⟨(Types.isLimitEquivSections hc').symm sec,
    fun n ↦ Types.isLimitEquivSections_symm_apply hc' sec (op n)⟩

omit [HasProducts AddCommGrpCat] in
/-- A complex of abelian groups whose homology vanishes in degree `q + 1` is exact there, on
elements. -/
theorem exists_d_eq_of_isZero_homology (L : CochainComplex AddCommGrpCat.{a} ℕ) (q : ℕ)
    (h : IsZero (L.homology (q + 1))) (z : L.X (q + 1)) (hz : L.d (q + 1) (q + 2) z = 0) :
    ∃ y, L.d q (q + 1) y = z := by
  have hex : L.ExactAt (q + 1) := (L.exactAt_iff_isZero_homology (q + 1)).mpr h
  rw [HomologicalComplex.exactAt_iff' L q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff] at hex
  exact hex z hz

/-- For an abelian sheaf and a covering family, every degree-zero Čech cocycle is the cochain of
a section over the covered object. -/
theorem exists_sectionsToCochain_eq_of_isSheaf (J : GrothendieckTopology C)
    (hE : E.sieve₀ ∈ J X) (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) (hF : Presheaf.IsSheaf J F)
    (z : (cechComplex E F).X 0) (hz : (cechComplex E F).d 0 1 z = 0) :
    ∃ s, sectionsToCochain E F s = z := by
  have hm : PreZeroHypercover.IsMatching (F ⋙ CategoryTheory.forget AddCommGrpCat.{a}) E
      (cochainToFamily E F z) := by
    rwa [← differential_eq_zero_iff E F, familyToCochain_cochainToFamily]
  obtain ⟨s, hs⟩ := (cechRestriction_bijective_of_isSheaf J F hF E hE).2
    ⟨cochainToFamily E F z, hm⟩
  refine ⟨s, ?_⟩
  change familyToCochain E F (cechRestriction E F s).1 = z
  rw [hs, familyToCochain_cochainToFamily]

/-- An element of a Čech cochain group given by a family of coordinates maps to the element with
the image coordinates. -/
private theorem cechComplexFunctor_map_f_symm_eq {F G : Cᵒᵖ ⥤ AddCommGrpCat.{a}} (φ : F ⟶ G)
    (q : ℕ) (s : ∀ k : Fin (q + 1) → E.I₀, cochainFactor E F q k) (y : (cechComplex E G).X q)
    (h : ∀ k, φ.app _ (s k) = Pi.π (cochainFactor E G q) k y) :
    ((cechComplexFunctor E).map φ).f q ((productAddEquiv (cochainFactor E F q)).symm s) = y := by
  apply (productAddEquiv (cochainFactor E G q)).injective
  funext k
  have hk : Pi.π (cochainFactor E F q) k ((productAddEquiv (cochainFactor E F q)).symm s) = s k :=
    congrFun ((productAddEquiv (cochainFactor E F q)).apply_symm_apply s) k
  refine (cechComplexFunctor_map_f_π_apply E φ q k _).trans ?_
  exact (congrArg (φ.app _) hk).trans (h k)

/-- **Čech vanishing passes to the limit of a tower of sheaves with surjective transitions.**
Let `Q` be a tower of abelian presheaves on a site, each a sheaf with vanishing higher Čech
cohomology on a covering family `E`, with transition maps surjective on the sections over every
object, and let `c` be a limit cone over `Q`. Then the cone point has vanishing higher Čech
cohomology on `E`. -/
theorem isZero_cechCohomology_of_isLimit_tower (J : GrothendieckTopology C)
    (hE : E.sieve₀ ∈ J X) (Q : ℕᵒᵖ ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{a})) (c : Cone Q) (hc : IsLimit c)
    (hsheaf : ∀ n, Presheaf.IsSheaf J (Q.obj (op n)))
    (hcech : ∀ n p, 0 < p → IsZero (cechCohomology E (Q.obj (op n)) p))
    (hsurj : ∀ (n : ℕ) (T : C),
      Function.Surjective ((Q.map (homOfLE (Nat.le_succ n)).op).app (op T)))
    (p : ℕ) (hp : 0 < p) : IsZero (cechCohomology E c.pt p) := by
  obtain ⟨p, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  let K := Q ⋙ cechComplexFunctor E
  let c' := (cechComplexFunctor E).mapCone c
  have hev : ∀ T : C, IsLimit (((evaluation Cᵒᵖ AddCommGrpCat.{a}).obj (op T)).mapCone c) :=
    fun T ↦ isLimitOfPreserves _ hc
  -- the cone projections of the Čech complexes are jointly injective
  have hinj : ∀ (q : ℕ) (x y : c'.pt.X q),
      (∀ n, (c'.π.app (op n)).f q x = (c'.π.app (op n)).f q y) → x = y := by
    intro q x y h
    refine (productAddEquiv (cochainFactor E c.pt q)).injective (funext fun k ↦ ?_)
    apply Concrete.isLimit_ext _ (hev _)
    rintro ⟨n⟩
    have h₁ := congrArg (Pi.π (cochainFactor E (Q.obj (op n)) q) k) (h n)
    change Pi.π (cochainFactor E (Q.obj (op n)) q) k
        (((cechComplexFunctor E).map (c.π.app (op n))).f q x) =
      Pi.π (cochainFactor E (Q.obj (op n)) q) k
        (((cechComplexFunctor E).map (c.π.app (op n))).f q y) at h₁
    rwa [cechComplexFunctor_map_f_π_apply, cechComplexFunctor_map_f_π_apply] at h₁
  -- compatible families of Čech cochains lift
  have hlift : ∀ (q : ℕ) (y : ∀ n, (K.obj (op n)).X q),
      (∀ n, (Stacks.AugmentedTower.tr K n).f q (y (n + 1)) = y n) →
        ∃ x : c'.pt.X q, ∀ n, (c'.π.app (op n)).f q x = y n := by
    intro q y hy
    have hcomp : ∀ (k : Fin (q + 1) → E.I₀) n,
        (Q.map (homOfLE (Nat.le_succ n)).op).app _
          (Pi.π (cochainFactor E (Q.obj (op (n + 1))) q) k (y (n + 1))) =
        Pi.π (cochainFactor E (Q.obj (op n)) q) k (y n) := by
      intro k n
      rw [← hy n]
      exact (cechComplexFunctor_map_f_π_apply E _ q k (y (n + 1))).symm
    choose s hs using fun k ↦ exists_lift_of_isLimit_tower _ _ (hev _)
      (fun n ↦ Pi.π (cochainFactor E (Q.obj (op n)) q) k (y n)) (hcomp k)
    exact ⟨(productAddEquiv (cochainFactor E c.pt q)).symm s, fun n ↦
      cechComplexFunctor_map_f_symm_eq E (c.π.app (op n)) q s (y n) fun k ↦ hs k n⟩
  -- the augmentations
  let A : ℕ → AddCommGrpCat.{a} := fun n ↦ (Q.obj (op n)).obj (op X)
  let a : ∀ n, A (n + 1) ⟶ A n := fun n ↦ (Q.map (homOfLE (Nat.le_succ n)).op).app (op X)
  let ε : ∀ n, A n ⟶ (K.obj (op n)).X 0 :=
    fun n ↦ AddCommGrpCat.ofHom (sectionsToCochain E (Q.obj (op n)))
  have hε : ∀ n (s : A (n + 1)), ε n (a n s) = (Stacks.AugmentedTower.tr K n).f 0 (ε (n + 1) s) :=
    fun n s ↦ ConcreteCategory.congr_hom
      (sectionsToCochain_naturality E (Q.map (homOfLE (Nat.le_succ n)).op)) s
  have hεd : ∀ n (s : A n), (K.obj (op n)).d 0 1 (ε n s) = 0 :=
    fun n s ↦ d_sectionsToCochain E (Q.obj (op n)) s
  have hexact₀ : ∀ n (z : (K.obj (op n)).X 0), (K.obj (op n)).d 0 1 z = 0 → ∃ s, ε n s = z :=
    fun n z hz ↦ exists_sectionsToCochain_eq_of_isSheaf E J hE (Q.obj (op n)) (hsheaf n) z hz
  have hexact : ∀ n q (z : (K.obj (op n)).X (q + 1)),
      (K.obj (op n)).d (q + 1) (q + 2) z = 0 → ∃ y, (K.obj (op n)).d q (q + 1) y = z :=
    fun n q z hz ↦ exists_d_eq_of_isZero_homology _ q (hcech n (q + 1) (by omega)) z hz
  have hsurjK : ∀ n q, Function.Surjective ((Stacks.AugmentedTower.tr K n).f q) := by
    intro n q y
    choose s hs using fun k : Fin (q + 1) → E.I₀ ↦ hsurj n _
      (Pi.π (cochainFactor E (Q.obj (op n)) q) k y)
    exact ⟨(productAddEquiv (cochainFactor E (Q.obj (op (n + 1))) q)).symm s,
      cechComplexFunctor_map_f_symm_eq E (Q.map (homOfLE (Nat.le_succ n)).op) q s y hs⟩
  have hex := Stacks.AugmentedTower.exactAt_succ c' hinj hlift A a ε hε hεd hexact₀ hexact
    (fun n ↦ hsurj n X) hsurjK p
  exact (c'.pt.exactAt_iff_isZero_homology (p + 1)).mp hex

end Stacks.CechSite

end
