module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.BaseChangeBijective
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.AxiomsBasic
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChangeData

/-!
# The comparison data of Lemma 0FVT for Hodge cohomology

Let `k ⟶ K` be an extension of fields. Remark 0FWE of the Stacks project reduces the axioms for
Hodge cohomology over `k` to those over `K` "in exactly the same manner" as Section 0FWC does for
de Rham cohomology, through Lemma 0FVT, whose hypothesis (3)
(`Stacks.WeilDeRham.FieldBaseChangeData`) asks for an isomorphism `F(1) ⊗_F F' ≅ F'(1)` and
functorial isomorphisms of graded algebras `H^*(X) ⊗_F F' ≅ (H')^*(X_K)` compatible with the first
Chern classes. For Hodge cohomology `F = k`, `F' = K`, `F(1) = k`, `F'(1) = K`, and the isomorphism
is the `K`-linear extension `K ⊗_k H^*_{Hodge}(X/k) ⟶ H^*_{Hodge}(X_K/K)` of the pullback `pr^*`
along the cartesian square `(pr : X_K ⟶ X, Spec K ⟶ Spec k)`. The pullback is a map of graded
rings, natural in `X` (pasting squares) and compatible with `c₁^{Hodge}` (Tag 0FMD for any
commutative square).

Since `H^*_{Hodge}(X/k) = ⨁_n ⨁_{p + q = n} H^q(X, Ω^p_{X/k})` and the pullback respects this
decomposition, the comparison map is bijective as soon as each
`K ⊗_k H^q(X, Ω^p_{X/k}) ⟶ H^q(X_K, Ω^p_{X_K/K})` is
(`Stacks.HodgeWeil.bijective_hodgeAlgebraBaseChangeLinear_of_bijective`), because the tensor
product commutes with direct sums (`Stacks.HodgeWeil.bijective_of_tmul_of_of`).

## Main definitions

* `Stacks.HodgeWeil.hodgeAlgebraBaseChange`: the base change ring map
  `H^*_{Hodge}(X/k) ⟶ H^*_{Hodge}(X_K/K)`.
* `Stacks.HodgeWeil.hodgeAlgebraBaseChangeLinear`: its `K`-linear extension
  `K ⊗_k H^*_{Hodge}(X/k) ⟶ H^*_{Hodge}(X_K/K)`.
* `Stacks.HodgeWeil.hodgeAlgebraBaseChangeAlgEquivOfBijective`: the same map, an isomorphism of
  `K`-algebras when each `K ⊗_k H^q(X, Ω^p_{X/k}) ⟶ H^q(X_K, Ω^p_{X_K/K})` is bijective.
* `Stacks.HodgeWeil.hodgeFieldBaseChangeDataOfBijective`: **the comparison data of Lemma 0FVT for
  Hodge cohomology along `k ⟶ K`**, given that bijectivity.
* `Stacks.HodgeWeil.hodgeFieldBaseChangeData`: **the comparison data of Lemma 0FVT for Hodge
  cohomology along `k ⟶ K`**, the bijectivity being flat base change
  (`Stacks.HodgeWeil.bijective_hodgeBaseChangeLinear`).

## Main results

* `Stacks.HodgeWeil.bijective_of_tmul_of_of`: a map `P ⊗ ⨁_i ⨁_j M_{ij} ⟶ ⨁_i ⨁_j N_{ij}` which is
  a bijection `P ⊗ M_{ij} ⟶ N_{ij}` on each summand is bijective.
* `Stacks.HodgeWeil.bijective_hodgeAlgebraBaseChangeLinear_of_bijective`: the comparison map is
  bijective if it is so on each `K ⊗_k H^q(X, Ω^p_{X/k})`.
* `Stacks.HodgeWeil.hodgeAlgebraBaseChange_hodgePullbackOf`: the base change map is natural.
* `Stacks.HodgeWeil.hodgeAlgebraBaseChange_hodgeFirstChernClassPiece`: the base change map
  carries `c₁^{Hodge}(ℒ)` to `c₁^{Hodge}(pr^*ℒ)`.
* `Stacks.HodgeWeil.twistEquiv_hodgeFirstChernClassTw`: the same on the twists by the Tate lines,
  the compatibility with `c₁` asked for by Lemma 0FVT.

## References

* [Stacks Project, Tag 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
* [Stacks Project, Section 0FWC](https://stacks.math.columbia.edu/tag/0FWC)
* [Stacks Project, Tag 0FMD](https://stacks.math.columbia.edu/tag/0FMD)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Stacks.WeilCohomology
open Stacks.WeilDeRham
open Stacks.WeilCohomology.SmoothProjectiveScheme hiding specStructure
open AlgebraicGeometry.SheafOfModules (hodgeCohomologyComponent)
open scoped TensorProduct DirectSum

universe u

namespace Stacks.HodgeWeil

/-! ### Tensor products of double direct sums -/

section DirectSum

variable {R : Type*} [CommSemiring R] {P : Type*} [AddCommMonoid P] [Module R P]
  {ι : Type*} [DecidableEq ι] {κ : ι → Type*} [∀ i, DecidableEq (κ i)]
  {M : ∀ i, κ i → Type*} [∀ i j, AddCommMonoid (M i j)] [∀ i j, Module R (M i j)]
  {N : ∀ i, κ i → Type*} [∀ i j, AddCommMonoid (N i j)]

/-- **A summandwise bijection out of the tensor product with a double direct sum is a
bijection**: if an additive map `T : P ⊗_R ⨁_i ⨁_j M_{ij} ⟶ ⨁_i ⨁_j N_{ij}` sends
`c ⊗ x` for `x ∈ M_{ij}` to `φ_{ij}(c ⊗ x) ∈ N_{ij}`, with every `φ_{ij} : P ⊗_R M_{ij} ⟶ N_{ij}`
bijective, then `T` is bijective. -/
theorem bijective_of_tmul_of_of (φ : ∀ i j, P ⊗[R] M i j →+ N i j)
    (hφ : ∀ i j, Function.Bijective (φ i j))
    (T : P ⊗[R] (⨁ i, ⨁ j, M i j) →+ ⨁ i, ⨁ j, N i j)
    (hT : ∀ (c : P) (i : ι) (j : κ i) (x : M i j),
      T (c ⊗ₜ DirectSum.of (fun i => ⨁ j, M i j) i (DirectSum.of (M i) j x)) =
        DirectSum.of (fun i => ⨁ j, N i j) i (DirectSum.of (N i) j (φ i j (c ⊗ₜ x)))) :
    Function.Bijective T := by
  let e : P ⊗[R] (⨁ i, ⨁ j, M i j) ≃+ ⨁ i, ⨁ j, N i j :=
    (TensorProduct.directSumRight R R P fun i => ⨁ j, M i j).toAddEquiv.trans
      (DFinsupp.mapRange.addEquiv fun i =>
        (TensorProduct.directSumRight R R P (M i)).toAddEquiv.trans
          (DFinsupp.mapRange.addEquiv fun j => AddEquiv.ofBijective (φ i j) (hφ i j)))
  have h : ⇑T = ⇑e := by
    funext t
    induction t using TensorProduct.inductionOn with
    | add s t hs ht => rw [map_add, map_add, hs, ht]
    | tmul c a =>
      induction a using DirectSum.induction_on with
      | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
      | add a b ha hb => rw [TensorProduct.tmul_add, map_add, map_add, ha, hb]
      | of i a =>
        induction a using DirectSum.induction_on with
        | zero => rw [map_zero, TensorProduct.tmul_zero, map_zero, map_zero]
        | add a b ha hb => rw [map_add, TensorProduct.tmul_add, map_add, map_add, ha, hb]
        | of j x =>
          rw [hT]
          change _ = DFinsupp.mapRange.addEquiv _
            (TensorProduct.directSumRight R R P (fun i => ⨁ j, M i j)
              (c ⊗ₜ DirectSum.lof R ι (fun i => ⨁ j, M i j) i (DirectSum.lof R (κ i) (M i) j x)))
          rw [TensorProduct.directSumRight_tmul_lof]
          change _ = DFinsupp.mapRange.addEquiv _
            (DFinsupp.single (β := fun i => P ⊗[R] ⨁ j, M i j) i
              (c ⊗ₜ DirectSum.lof R (κ i) (M i) j x))
          rw [DFinsupp.mapRange.addEquiv_apply, DFinsupp.mapRange_single]
          change _ = DirectSum.of (fun i => ⨁ j, N i j) i (DFinsupp.mapRange.addEquiv _
            (TensorProduct.directSumRight R R P (M i) (c ⊗ₜ DirectSum.lof R (κ i) (M i) j x)))
          rw [TensorProduct.directSumRight_tmul_lof]
          change _ = DirectSum.of (fun i => ⨁ j, N i j) i
            (DFinsupp.mapRange.addEquiv _ (DFinsupp.single (β := fun j => P ⊗[R] M i j) j (c ⊗ₜ x)))
          rw [DFinsupp.mapRange.addEquiv_apply, DFinsupp.mapRange_single]
          rfl
  rw [h]
  exact e.bijective

end DirectSum

/-! ### The comparison map -/

section BaseChange

attribute [local instance] RestrictScalars.moduleOrig

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
  (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- **The base change ring map `pr^* : H^*_{Hodge}(X/k) ⟶ H^*_{Hodge}(X_K/K)`**: pullback along the
cartesian square `(pr : X_K ⟶ X, Spec K ⟶ Spec k)`. -/
abbrev hodgeAlgebraBaseChange :
    hodgeAlgebraOf X →+* hodgeAlgebraOf ((fieldBaseChange k K).obj X) :=
  hodgeAlgebraPullback (fieldBaseChangeProj X) ((fieldBaseChange k K).obj X).obj.hom X.obj.hom
    (specStructure k K) (fieldBaseChangeProj_comp_hom X)

/-- The base change map on a homogeneous class of degree `n` is the pullback on `H^n_{Hodge}`. -/
private theorem hodgeAlgebraBaseChange_of (n : ℤ) (x : hodgePiece (formsAlgebras X.obj.hom) n) :
    hodgeAlgebraBaseChange K X (DirectSum.of (hodgePiece (formsAlgebras X.obj.hom)) n x) =
      DirectSum.of (hodgePiece (formsAlgebras ((fieldBaseChange k K).obj X).obj.hom)) n
        (hodgePiecePullback (fieldBaseChangeProj X) ((fieldBaseChange k K).obj X).obj.hom
          X.obj.hom (specStructure k K) (fieldBaseChangeProj_comp_hom X) n x) :=
  hodgeAlgebraPullback_of (fieldBaseChangeProj X) ((fieldBaseChange k K).obj X).obj.hom
    X.obj.hom (specStructure k K) (fieldBaseChangeProj_comp_hom X) n x

/-- On a class of `H^q(X, Ω^p_{X/k})` the base change map is the base change map
`Stacks.HodgeWeil.hodgeBaseChange` of that summand. -/
theorem hodgeAlgebraBaseChange_of_of (n : ℤ) (i : HodgeBidegreeInt n)
    (x : hodgeCohomologyComponent (formsAlgebras X.obj.hom) i.1.1 (i.1.2 : ℤ)) :
    hodgeAlgebraBaseChange K X (DirectSum.of (hodgePiece (formsAlgebras X.obj.hom)) n
        (DirectSum.of (fun i : HodgeBidegreeInt n => (hodgeCohomologyComponent
          (formsAlgebras X.obj.hom) i.1.1 (i.1.2 : ℤ) : Type u)) i x)) =
      DirectSum.of (hodgePiece (formsAlgebras ((fieldBaseChange k K).obj X).obj.hom)) n
        (DirectSum.of (fun i : HodgeBidegreeInt n => (hodgeCohomologyComponent
          (formsAlgebras ((fieldBaseChange k K).obj X).obj.hom) i.1.1 (i.1.2 : ℤ) : Type u)) i
          (hodgeBaseChange K X i.1.1 (i.1.2 : ℤ) x)) :=
  (hodgeAlgebraBaseChange_of K X n _).trans
  (congrArg (DirectSum.of (hodgePiece (formsAlgebras ((fieldBaseChange k K).obj X).obj.hom)) n)
    (hodgePiecePullback_of (fieldBaseChangeProj X) ((fieldBaseChange k K).obj X).obj.hom
      X.obj.hom (specStructure k K) (fieldBaseChangeProj_comp_hom X) n i x))

/-- The base change map carries the scalar `c ∈ k` to the scalar `c ∈ K`. -/
theorem hodgeAlgebraBaseChange_algebraMap (c : k) :
    hodgeAlgebraBaseChange K X (algebraMap k (hodgeAlgebraOf X) c) =
      algebraMap K (hodgeAlgebraOf ((fieldBaseChange k K).obj X)) (algebraMap k K c) :=
  hodgeAlgebraPullback_scalarClass _ _ _ _ (fieldBaseChangeProj_comp_hom X)
    (hodgeScalarsOverField X.obj.hom)
    ((hodgeScalarsOverField ((fieldBaseChange k K).obj X).obj.hom).comp (algebraMap k K))
    (hodgeBaseRingHom_comp_hodgeScalarsOverField K X) c

/-- The base change map as a `k`-linear map into `H^*_{Hodge}(X_K/K)` with scalars restricted to
`k`. -/
def hodgeAlgebraBaseChangeRestrict :
    hodgeAlgebraOf X →ₗ[k]
      RestrictScalars k K (hodgeAlgebraOf ((fieldBaseChange k K).obj X)) where
  toFun a := (RestrictScalars.addEquiv k K _).symm (hodgeAlgebraBaseChange K X a)
  map_add' a b := by rw [map_add, map_add]
  map_smul' c a := by
    rw [Algebra.smul_def, map_mul, hodgeAlgebraBaseChange_algebraMap, RingHom.id_apply,
      RestrictScalars.smul_def, ← Algebra.smul_def]
    rfl

/-- **The comparison map `K ⊗_k H^*_{Hodge}(X/k) ⟶ H^*_{Hodge}(X_K/K)`**, `c ⊗ a ↦ c · pr^* a`, the
`K`-linear extension of the base change map. -/
def hodgeAlgebraBaseChangeLinear :
    K ⊗[k] hodgeAlgebraOf X →ₗ[K] hodgeAlgebraOf ((fieldBaseChange k K).obj X) where
  toFun t :=
    RestrictScalars.addEquiv k K _ ((hodgeAlgebraBaseChangeRestrict K X).liftBaseChange K t)
  map_add' s t := by rw [map_add, map_add]
  map_smul' c t := by
    rw [map_smul]
    rfl

/-- The comparison map on `c ⊗ a` is `c · pr^* a`. -/
theorem hodgeAlgebraBaseChangeLinear_tmul (c : K) (a : hodgeAlgebraOf X) :
    hodgeAlgebraBaseChangeLinear K X (c ⊗ₜ a) = c • hodgeAlgebraBaseChange K X a :=
  rfl

/-- **The comparison map is bijective if it is so on each summand**: if every
`K ⊗_k H^q(X, Ω^p_{X/k}) ⟶ H^q(X_K, Ω^p_{X_K/K})` is bijective, so is
`K ⊗_k H^*_{Hodge}(X/k) ⟶ H^*_{Hodge}(X_K/K)`, the tensor product commuting with the direct sum
`H^*_{Hodge} = ⨁_n ⨁_{p + q = n} H^q(-, Ω^p)`. -/
theorem bijective_hodgeAlgebraBaseChangeLinear_of_bijective
    (h : ∀ (p : ℕ) (q : ℤ), Function.Bijective (hodgeBaseChangeLinear K X p q)) :
    Function.Bijective (hodgeAlgebraBaseChangeLinear K X) :=
  bijective_of_tmul_of_of
    (fun n (i : HodgeBidegreeInt n) =>
      (hodgeBaseChangeLinear K X i.1.1 (i.1.2 : ℤ)).toAddMonoidHom)
    (fun _ i => h i.1.1 (i.1.2 : ℤ)) (hodgeAlgebraBaseChangeLinear K X).toAddMonoidHom
    (fun c n i x => by
      change hodgeAlgebraBaseChangeLinear K X (c ⊗ₜ _) = _
      rw [hodgeAlgebraBaseChangeLinear_tmul, hodgeAlgebraBaseChange_of_of]
      let : ∀ n, Module K (hodgePiece (formsAlgebras ((fieldBaseChange k K).obj X).obj.hom) n) :=
        hodgePieceModule _ (hodgeScalarsOverField ((fieldBaseChange k K).obj X).obj.hom)
      refine (DirectSum.of_smul K n c _).symm.trans ?_
      exact congrArg (DirectSum.of _ n) (DirectSum.of_smul _ i _ _).symm)

/-- **The comparison map, an isomorphism of `K`-algebras**
`K ⊗_k H^*_{Hodge}(X/k) ≅ H^*_{Hodge}(X_K/K)`, when each
`K ⊗_k H^q(X, Ω^p_{X/k}) ⟶ H^q(X_K, Ω^p_{X_K/K})` is bijective: the base change map is a ring map,
so its `K`-linear extension is a map of `K`-algebras. -/
def hodgeAlgebraBaseChangeAlgEquivOfBijective
    (h : ∀ (p : ℕ) (q : ℤ), Function.Bijective (hodgeBaseChangeLinear K X p q)) :
    K ⊗[k] hodgeAlgebraOf X ≃ₐ[K] hodgeAlgebraOf ((fieldBaseChange k K).obj X) :=
  AlgEquiv.ofBijective
    (Algebra.TensorProduct.algHomOfLinearMapTensorProduct (hodgeAlgebraBaseChangeLinear K X)
      (fun c₁ c₂ a₁ a₂ => by
        rw [hodgeAlgebraBaseChangeLinear_tmul, hodgeAlgebraBaseChangeLinear_tmul,
          hodgeAlgebraBaseChangeLinear_tmul, map_mul, smul_mul_smul_comm])
      (by rw [hodgeAlgebraBaseChangeLinear_tmul, map_one, one_smul]))
    (bijective_hodgeAlgebraBaseChangeLinear_of_bijective K X h)

/-- The comparison isomorphism on `1 ⊗ a` is the base change map `pr^* a`. -/
theorem hodgeAlgebraBaseChangeAlgEquivOfBijective_one_tmul
    (h : ∀ (p : ℕ) (q : ℤ), Function.Bijective (hodgeBaseChangeLinear K X p q))
    (a : hodgeAlgebraOf X) :
    hodgeAlgebraBaseChangeAlgEquivOfBijective K X h (1 ⊗ₜ a) = hodgeAlgebraBaseChange K X a :=
  one_smul K _

/-- **The base change map preserves the grading**: it carries `H^n_{Hodge}(X/k)` into
`H^n_{Hodge}(X_K/K)`. -/
theorem hodgeAlgebraBaseChange_mem_hodgeGradeOf {n : ℤ} {a : hodgeAlgebraOf X}
    (ha : a ∈ hodgeGradeOf X n) :
    hodgeAlgebraBaseChange K X a ∈ hodgeGradeOf ((fieldBaseChange k K).obj X) n := by
  obtain ⟨x, rfl⟩ := (mem_hodgeGrade _ (hodgeScalarsOverField X.obj.hom) n a).1 ha
  exact (hodgeAlgebraBaseChange_of K X n x).symm ▸ of_mem_hodgeGrade _ _ n _

/-- The pullback on `H^*_{Hodge}` along a commutative square depends on its two horizontal
morphisms only through the morphisms themselves. -/
theorem hodgeAlgebraPullback_congr {X X' S S' : Scheme.{u}} {g'₁ g'₂ : X' ⟶ X} (hg' : g'₁ = g'₂)
    (f' : X' ⟶ S') (f : X ⟶ S) {g₁ g₂ : S' ⟶ S} (hg : g₁ = g₂) (w₁ : g'₁ ≫ f = f' ≫ g₁)
    (w₂ : g'₂ ≫ f = f' ≫ g₂) :
    hodgeAlgebraPullback g'₁ f' f g₁ w₁ = hodgeAlgebraPullback g'₂ f' f g₂ w₂ := by
  subst hg' hg
  rfl

variable {X} in
/-- **The base change map is natural**: `(f_K)^* ∘ pr^* = pr^* ∘ f^*` on `H^*_{Hodge}(Y/k)`, for a
morphism `f : X ⟶ Y` of smooth projective schemes over `k`. Both sides are the pullback along the
pasted square `X_K ⟶ Y`. -/
theorem hodgeAlgebraBaseChange_hodgePullbackOf {Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) (a : hodgeAlgebraOf Y) :
    hodgeAlgebraBaseChange K X (hodgePullbackOf f a) =
      hodgePullbackOf ((fieldBaseChange k K).map f) (hodgeAlgebraBaseChange K Y a) := by
  have w₁ : (fieldBaseChangeProj X ≫ f.hom.left) ≫ Y.obj.hom =
      ((fieldBaseChange k K).obj X).obj.hom ≫ (specStructure k K ≫ 𝟙 _) := by
    rw [Category.comp_id, Category.assoc, hodgeSquare_w f, Category.comp_id]
    exact fieldBaseChangeProj_comp_hom X
  have w₂ : (((fieldBaseChange k K).map f).hom.left ≫ fieldBaseChangeProj Y) ≫ Y.obj.hom =
      ((fieldBaseChange k K).obj X).obj.hom ≫ (𝟙 _ ≫ specStructure k K) := by
    rw [Category.id_comp, Category.assoc, fieldBaseChangeProj_comp_hom, ← Category.assoc,
      hodgeSquare_w, Category.comp_id]
  have h₁ := hodgeAlgebraPullback_comp f.hom.left X.obj.hom Y.obj.hom (𝟙 _) (hodgeSquare_w f)
    (fieldBaseChangeProj X) ((fieldBaseChange k K).obj X).obj.hom (specStructure k K)
    (fieldBaseChangeProj_comp_hom X) w₁
  have h₂ := hodgeAlgebraPullback_comp (fieldBaseChangeProj Y)
    ((fieldBaseChange k K).obj Y).obj.hom Y.obj.hom (specStructure k K)
    (fieldBaseChangeProj_comp_hom Y) ((fieldBaseChange k K).map f).hom.left
    ((fieldBaseChange k K).obj X).obj.hom (𝟙 _) (hodgeSquare_w _) w₂
  have h₃ : hodgeAlgebraPullback (fieldBaseChangeProj X ≫ f.hom.left)
      ((fieldBaseChange k K).obj X).obj.hom Y.obj.hom (specStructure k K ≫ 𝟙 _) w₁ =
      hodgeAlgebraPullback (((fieldBaseChange k K).map f).hom.left ≫ fieldBaseChangeProj Y)
        ((fieldBaseChange k K).obj X).obj.hom Y.obj.hom (𝟙 _ ≫ specStructure k K) w₂ :=
    hodgeAlgebraPullback_congr (fieldBaseChange_map_comp_proj f).symm
    ((fieldBaseChange k K).obj X).obj.hom Y.obj.hom
    ((Category.comp_id _).trans (Category.id_comp _).symm) w₁ w₂
  have e₁ : hodgePullbackOf f a =
      hodgeAlgebraPullback f.hom.left X.obj.hom Y.obj.hom (𝟙 _) (hodgeSquare_w f) a :=
    hodgeAlgebraPullbackOverBase_apply _ _ _ _ _ a
  have e₂ : ∀ b, hodgePullbackOf ((fieldBaseChange k K).map f) b =
      hodgeAlgebraPullback ((fieldBaseChange k K).map f).hom.left
        ((fieldBaseChange k K).obj X).obj.hom ((fieldBaseChange k K).obj Y).obj.hom (𝟙 _)
        (hodgeSquare_w _) b :=
    fun b => hodgeAlgebraPullbackOverBase_apply _ _ _ _ _ b
  rw [e₁, e₂, ← RingHom.comp_apply, ← RingHom.comp_apply, ← h₁, ← h₂, h₃]

/-- **The base change map carries `c₁^{Hodge}(ℒ)` to `c₁^{Hodge}(pr^*ℒ)`** in
`H^2_{Hodge}(X_K/K)`, for an invertible module `ℒ` on `X` (Tag 0FMD for the square
`(pr, Spec K ⟶ Spec k)`). -/
theorem hodgeAlgebraBaseChange_hodgeFirstChernClassPiece (L : ((toScheme k).obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible ((toScheme k).obj X).presheaf
      ((toScheme k).obj X).ringCatSheaf.2 L) :
    hodgeAlgebraBaseChange K X (DirectSum.of (hodgePiece (formsAlgebras X.obj.hom)) 2
        (hodgeFirstChernClassPiece X (picardClassOf _ L hL))) =
      DirectSum.of (hodgePiece (formsAlgebras ((fieldBaseChange k K).obj X).obj.hom)) 2
        (hodgeFirstChernClassPiece ((fieldBaseChange k K).obj X) (picardClassOf _
          ((Scheme.Modules.pullback (fieldBaseChangeProj X)).obj L)
          (isInvertible_pullback_obj _ L hL))) :=
  (hodgeAlgebraBaseChange_of K X 2 (hodgeFirstChernClassPiece X (picardClassOf _ L hL))).trans
  (congrArg (DirectSum.of (hodgePiece (formsAlgebras ((fieldBaseChange k K).obj X).obj.hom)) 2)
    ((hodgePiecePullback_of (fieldBaseChangeProj X) ((fieldBaseChange k K).obj X).obj.hom
      X.obj.hom (specStructure k K) (fieldBaseChangeProj_comp_hom X) 2 bidegreeOneOne
      (hodgeFirstChernClassModule X.obj.hom (picardClassOf _ L hL))).trans
    (congrArg (DirectSum.of (fun i : HodgeBidegreeInt 2 => (hodgeCohomologyComponent
        (formsAlgebras ((fieldBaseChange k K).obj X).obj.hom) i.1.1 (i.1.2 : ℤ) : Type u))
        bidegreeOneOne)
      (hodgePullback_hodgeFirstChernClassModule_picardClassOf (fieldBaseChangeProj X)
        ((fieldBaseChange k K).obj X).obj.hom X.obj.hom (specStructure k K)
        (fieldBaseChangeProj_comp_hom X) L hL))))

/-- **The comparison isomorphisms carry `c₁^{Hodge}(ℒ)` to `c₁^{Hodge}(pr^*ℒ)`** in
`H^*_{Hodge}(X_K/K)(1)`, through the map `H^*_{Hodge}(X/k)(1) ⟶ H^*_{Hodge}(X_K/K)(1)` they
induce. -/
theorem twistEquiv_hodgeFirstChernClassTw
    (hbij : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (p : ℕ) (q : ℤ),
      Function.Bijective (hodgeBaseChangeLinear K X p q))
    (L : ((toScheme k).obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible ((toScheme k).obj X).presheaf
      ((toScheme k).obj X).ringCatSheaf.2 L) :
    twistEquiv (hodgeFirstChernClassData k) (hodgeFirstChernClassData K)
        (TensorProduct.AlgebraTensorModule.rid k K K)
        (fun X => hodgeAlgebraBaseChangeAlgEquivOfBijective K X (hbij X)) X 1
        (1 ⊗ₜ hodgeFirstChernClassTw X (picardClassOf _ L hL)) =
      hodgeFirstChernClassTw ((fieldBaseChange k K).obj X)
        (picardClassOf _ ((Scheme.Modules.pullback (fieldBaseChangeProj X)).obj L)
          (isInvertible_pullback_obj _ L hL)) := by
  change twistEquiv (hodgeFirstChernClassData k) (hodgeFirstChernClassData K)
        (TensorProduct.AlgebraTensorModule.rid k K K)
        (fun X => hodgeAlgebraBaseChangeAlgEquivOfBijective K X (hbij X)) X 1
        (1 ⊗ₜ (Stacks.DeRhamWeil.untwist (k := k) (hodgeAlgebraOf X) 1).symm
          (DirectSum.of (hodgePiece (formsAlgebras X.obj.hom)) 2
            (hodgeFirstChernClassPiece X (picardClassOf _ L hL)))) =
      (Stacks.DeRhamWeil.untwist (k := K) (hodgeAlgebraOf ((fieldBaseChange k K).obj X)) 1).symm
        (DirectSum.of (hodgePiece (formsAlgebras ((fieldBaseChange k K).obj X).obj.hom)) 2
          (hodgeFirstChernClassPiece ((fieldBaseChange k K).obj X)
            (picardClassOf _ ((Scheme.Modules.pullback (fieldBaseChangeProj X)).obj L)
              (isInvertible_pullback_obj _ L hL))))
  have untwist_symm_eq_tmul : ∀ {F : Type u} [Field F] (V : Type u) [AddCommGroup V]
      [Module F V] (v : V), (Stacks.DeRhamWeil.untwist V 1).symm v =
        (v ⊗ₜ PiTensorProduct.tprod F (fun _ : Fin 1 => (1 : F)) : tateTwist F F V 1) := by
    intro F _ V _ _ v
    apply (Stacks.DeRhamWeil.untwist V 1).injective
    rw [LinearEquiv.apply_symm_apply, Stacks.DeRhamWeil.untwist, tateTwistCoordinates_tmul]
    change v = tensorPowerCoordinates _ 1 _ • v
    simp [tensorPowerCoordinates]
  rw [untwist_symm_eq_tmul, untwist_symm_eq_tmul]
  refine (twistEquiv_one_tmul _ _ X _ _).trans ?_
  have hrid : TensorProduct.AlgebraTensorModule.rid k K K (1 ⊗ₜ (1 : k)) = (1 : K) := by simp
  exact congrArg₂ (fun (b : hodgeAlgebraOf ((fieldBaseChange k K).obj X)) (l : K) =>
      (b ⊗ₜ PiTensorProduct.tprod K (fun _ : Fin 1 => l) :
        tateTwist K K (hodgeAlgebraOf ((fieldBaseChange k K).obj X)) 1))
    ((hodgeAlgebraBaseChangeAlgEquivOfBijective_one_tmul K X (hbij X) _).trans
      (hodgeAlgebraBaseChange_hodgeFirstChernClassPiece K X L hL)) hrid

variable (k) in
/-- **The comparison data of Lemma 0FVT for Hodge cohomology** along an extension `K` of `k`
(Remark 0FWE), given that every `K ⊗_k H^q(X, Ω^p_{X/k}) ⟶ H^q(X_K, Ω^p_{X_K/K})` is bijective:
`k ⊗_k K = K` on the Tate lines, and on cohomology the `K`-linear extension
`K ⊗_k H^*_{Hodge}(X/k) ≅ H^*_{Hodge}(X_K/K)` of the base change map, which is natural, graded and
compatible with `c₁^{Hodge}`. -/
def hodgeFieldBaseChangeDataOfBijective
    (hbij : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (p : ℕ) (q : ℤ),
      Function.Bijective (hodgeBaseChangeLinear K X p q)) :
    FieldBaseChangeData (hodgeFirstChernClassData k) (hodgeFirstChernClassData K) where
  tateEquiv := TensorProduct.AlgebraTensorModule.rid k K K
  cohEquiv X := hodgeAlgebraBaseChangeAlgEquivOfBijective K X (hbij X)
  cohEquiv_pull {X Y} f a :=
    (hodgeAlgebraBaseChangeAlgEquivOfBijective_one_tmul K X (hbij X) _).trans
      ((hodgeAlgebraBaseChange_hodgePullbackOf K f a).trans
        (congrArg (hodgePullbackOf ((fieldBaseChange k K).map f))
          (hodgeAlgebraBaseChangeAlgEquivOfBijective_one_tmul K Y (hbij Y) a).symm))
  cohEquiv_grade X _ a ha :=
    (hodgeAlgebraBaseChangeAlgEquivOfBijective_one_tmul K X (hbij X) a).symm ▸
      hodgeAlgebraBaseChange_mem_hodgeGradeOf K X ha
  c₁_compat X L hL := twistEquiv_hodgeFirstChernClassTw K X hbij L hL

variable (k) in
/-- **The comparison data of Lemma 0FVT for Hodge cohomology** along an extension `K` of `k`
(Remark 0FWE): `k ⊗_k K = K` on the Tate lines, and on cohomology the isomorphisms
`K ⊗_k H^*_{Hodge}(X/k) ≅ H^*_{Hodge}(X_K/K)` of flat base change
(`Stacks.HodgeWeil.bijective_hodgeBaseChangeLinear`), natural, graded and compatible with
`c₁^{Hodge}`. -/
def hodgeFieldBaseChangeData :
    FieldBaseChangeData (hodgeFirstChernClassData k) (hodgeFirstChernClassData K) :=
  hodgeFieldBaseChangeDataOfBijective k K fun X p q => bijective_hodgeBaseChangeLinear K X p q

end BaseChange

end Stacks.HodgeWeil

end
