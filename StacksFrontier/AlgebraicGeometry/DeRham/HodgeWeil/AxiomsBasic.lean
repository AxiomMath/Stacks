module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Data
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Coproduct
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.GlobalSections
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.FirstChernClassPullback
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeilCohomologyTheory
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GlobalSectionsAxiom

/-!
# The axioms (A1), (A2) and (A8) for Hodge cohomology

Let `k` be a field. Remark 0FWE of the Stacks project considers Hodge cohomology
`X ↦ H^*_{Hodge}(X/k) = ⨁_n ⨁_{p + q = n} H^q(X, Ω^p_{X/k})` with the Hodge first Chern class,
the data `Stacks.HodgeWeil.hodgeFirstChernClassData k` of Weil Cohomology Theories, Section 0FID.
This file proves three of the axioms of that section for these data, by assembling the
corresponding statements on the groups `H^q(X, Ω^p_{X/k})`:

* (A1) `H^*_{Hodge}(∅/k) = 0`, and for a coproduct `Z = X ⨿ Y` with coprojections `i`, `j` the
  map `(i^*, j^*) : H^*_{Hodge}(Z/k) ⟶ H^*_{Hodge}(X/k) × H^*_{Hodge}(Y/k)` is bijective. Both
  hold summand by summand, since `H^q(-, Ω^p)` of the empty scheme vanishes and
  `H^q(Z, Ω^p) ⟶ H^q(X, Ω^p) × H^q(Y, Ω^p)` is bijective.
* (A2) `f^*c₁^{Hodge}(ℒ) = c₁^{Hodge}(f^*ℒ)`: the pullback commutes with the canonical coordinate
  of the twist by the trivial line `k` and with the inclusion of the summand
  `H^1(X, Ω^1) ⊂ H^2_{Hodge}(X/k)`, and on `H^1(X, Ω^1)` this is the compatibility of the Hodge
  first Chern class with pullback.
* (A8) for `g : X ⟶ S` with `g^♯ : Γ(S, 𝒪_S) ⟶ Γ(X, 𝒪_X)` an isomorphism, the pullback
  `H^0_{Hodge}(S/k) ⟶ H^0_{Hodge}(X/k)` is bijective; the only bidegree of total degree `0` is
  `(0, 0)`, and `H^0(-, Ω^0)` is the ring of global functions. For the canonical morphism
  `X ⟶ Spec Γ(X, 𝒪_X)` this is (A8).

## Main definitions

* `Stacks.HodgeWeil.hodgeGradeEquiv`: the degree-`n` part of `H^*_{Hodge}(X/k)` is
  `H^n_{Hodge}(X/k) = ⨁_{p + q = n} H^q(X, Ω^p_{X/k})`, as `k`-vector spaces.

## Main results

* `Stacks.HodgeWeil.bijective_directSum_map_prod`: a family of maps `M i ⟶ N i × P i` that are
  bijective induces a bijection `⨁ M i ⟶ (⨁ N i) × (⨁ P i)`.
* `Stacks.HodgeWeil.hodgePullbackOf_of`: the pullback on `H^*_{Hodge}` is, in degree `n`, the
  pullback on `H^n_{Hodge}`.
* `Stacks.HodgeWeil.hodge_coproductAxiom`: **axiom (A1)** for Hodge cohomology.
* `Stacks.HodgeWeil.hodge_pullbackAxiom`: **axiom (A2)** for Hodge cohomology.
* `Stacks.HodgeWeil.hodge_globalSectionsAxiom`: **axiom (A8)** for Hodge cohomology.

## Implementation notes

The condition (A8), `Stacks.WeilCohomology.FirstChernClassData.GlobalSectionsAxiom`, is about the
canonical morphism `Stacks.WeilCohomology.SmoothProjectiveScheme.toSpecGlobalSections`
`X ⟶ Spec Γ(X, 𝒪_X)`. For Hodge cohomology it is proved for every morphism `g : X ⟶ S` of smooth
projective schemes inducing an isomorphism on global functions
(`bijective_gradedPieceMap_hodgePullbackOf_zero`), with no affineness hypothesis on `S`; the
canonical morphism is one, since `Γ(Spec A, 𝒪) = A`.

## References

* [Stacks Project, Tag 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.WeilCohomology
open Stacks.WeilCohomology.SmoothProjectiveScheme
open AlgebraicGeometry.SheafOfModules (hodgeCohomologyComponent)

universe u

namespace Stacks.HodgeWeil

/-! ### Bijections of direct sums -/

section DirectSum

variable {ι : Type*} [DecidableEq ι] {M N P : ι → Type*} [∀ i, AddCommMonoid (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, AddCommMonoid (P i)]

/-- An additive map out of `⨁ R i` takes values in a submonoid if it does so on each summand. -/
private theorem mem_of_forall_directSum_of_mem {R : ι → Type*} [∀ i, AddCommMonoid (R i)]
    {A : Type*} [AddCommMonoid A] (S : AddSubmonoid A) (e : DirectSum ι R →+ A)
    (h : ∀ i r, e (DirectSum.of R i r) ∈ S) (a : DirectSum ι R) : e a ∈ S := by
  induction a using DirectSum.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | add a a' ha ha' => rw [map_add]; exact add_mem ha ha'
  | of i r => exact h i r

omit [DecidableEq ι] in
/-- **A summandwise bijection into a product is a bijection of direct sums**: if each
`x ↦ (φ_i x, ψ_i x) : M i ⟶ N i × P i` is bijective, so is
`x ↦ (φ x, ψ x) : ⨁ M i ⟶ (⨁ N i) × (⨁ P i)`. -/
theorem bijective_directSum_map_prod (φ : ∀ i, M i →+ N i) (ψ : ∀ i, M i →+ P i)
    (h : ∀ i, Function.Bijective fun x : M i => (φ i x, ψ i x)) :
    Function.Bijective fun x : DirectSum ι M => (DirectSum.map φ x, DirectSum.map ψ x) := by
  classical
  refine ⟨fun x y hxy => DFinsupp.ext fun i => (h i).1 (Prod.ext ?_ ?_), ?_⟩
  · have := congrArg (fun z => z.1 i) hxy
    simpa only [DirectSum.map_apply] using this
  · have := congrArg (fun z => z.2 i) hxy
    simpa only [DirectSum.map_apply] using this
  let F := (DirectSum.map φ).prod (DirectSum.map ψ)
  have hF : ∀ x, F x = (DirectSum.map φ x, DirectSum.map ψ x) := fun _ => rfl
  have hl : ∀ a : DirectSum ι N, (a, 0) ∈ AddMonoidHom.mrange F := fun a =>
    mem_of_forall_directSum_of_mem (AddMonoidHom.mrange F) (.inl _ _) (fun i n => by
      obtain ⟨m, hm⟩ := (h i).2 (n, 0)
      refine ⟨DirectSum.of M i m, ?_⟩
      rw [hF, DirectSum.map_of, DirectSum.map_of, show φ i m = n from congrArg Prod.fst hm,
        show ψ i m = 0 from congrArg Prod.snd hm, map_zero]
      rfl) a
  have hr : ∀ b : DirectSum ι P, (0, b) ∈ AddMonoidHom.mrange F := fun b =>
    mem_of_forall_directSum_of_mem (AddMonoidHom.mrange F) (.inr _ _) (fun i p => by
      obtain ⟨m, hm⟩ := (h i).2 (0, p)
      refine ⟨DirectSum.of M i m, ?_⟩
      rw [hF, DirectSum.map_of, DirectSum.map_of, show φ i m = 0 from congrArg Prod.fst hm,
        show ψ i m = p from congrArg Prod.snd hm, map_zero]
      rfl) b
  rintro ⟨a, b⟩
  have := add_mem (hl a) (hr b)
  rw [Prod.mk_add_mk, add_zero, zero_add] at this
  exact this

end DirectSum

variable {k : Type u} [Field k]

/-! ### The grading -/

section Grade

variable (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- **The degree-`n` part of `H^*_{Hodge}(X/k)` is `H^n_{Hodge}(X/k)`**
`= ⨁_{p + q = n} H^q(X, Ω^p_{X/k})`, as `k`-vector spaces. -/
def hodgeGradeEquiv (n : ℤ) :
    letI := hodgePieceModule (formsAlgebras X.obj.hom) (hodgeScalarsOverField X.obj.hom) n
    hodgeGradeOf X n ≃ₗ[k] hodgePiece (formsAlgebras X.obj.hom) n :=
  letI : ∀ n, Module k (hodgePiece (formsAlgebras X.obj.hom) n) :=
    hodgePieceModule _ (hodgeScalarsOverField X.obj.hom)
  DirectSum.rangeGradingEquiv k (hodgePiece (formsAlgebras X.obj.hom)) n

/-- `hodgeGradeEquiv` reads off the class of `H^n_{Hodge}(X/k)` representing a class of the
degree-`n` part. -/
theorem hodgeGradeEquiv_eq_of_coe_eq {n : ℤ} (z : hodgeGradeOf X n)
    (x : hodgePiece (formsAlgebras X.obj.hom) n)
    (hz : (z : hodgeAlgebraOf X) = DirectSum.of (hodgePiece (formsAlgebras X.obj.hom)) n x) :
    hodgeGradeEquiv X n z = x :=
  let : ∀ n, Module k (hodgePiece (formsAlgebras X.obj.hom) n) :=
    hodgePieceModule _ (hodgeScalarsOverField X.obj.hom)
  DirectSum.rangeGradingEquiv_eq_of_coe_eq k (hodgePiece (formsAlgebras X.obj.hom)) z x hz

/-- `hodgeGradeEquiv` on the inclusion of a class of `H^n_{Hodge}(X/k)`. -/
theorem hodgeGradeEquiv_apply_of {n : ℤ} (x : hodgePiece (formsAlgebras X.obj.hom) n) :
    hodgeGradeEquiv X n ⟨DirectSum.of (hodgePiece (formsAlgebras X.obj.hom)) n x,
      of_mem_hodgeGrade _ _ n x⟩ = x :=
  hodgeGradeEquiv_eq_of_coe_eq X _ x rfl

/-- The inverse of `hodgeGradeEquiv` is the inclusion of `H^n_{Hodge}(X/k)` in
`H^*_{Hodge}(X/k)`. -/
theorem coe_hodgeGradeEquiv_symm_apply {n : ℤ} (x : hodgePiece (formsAlgebras X.obj.hom) n) :
    ((hodgeGradeEquiv X n).symm x : hodgeAlgebraOf X) =
      DirectSum.of (hodgePiece (formsAlgebras X.obj.hom)) n x :=
  congrArg Subtype.val ((LinearEquiv.symm_apply_eq _).2 (hodgeGradeEquiv_apply_of X x).symm)

end Grade

/-! ### The pullback in each degree -/

variable {X Y : (SmoothProjectiveScheme k).FullSubcategory}

/-- On a class of `H^n_{Hodge}(Y/k)` the pullback `f^*` is the pullback on `H^n_{Hodge}`. -/
theorem hodgePullbackOf_of (f : X ⟶ Y) (n : ℤ) (x : hodgePiece (formsAlgebras Y.obj.hom) n) :
    hodgePullbackOf f (DirectSum.of (hodgePiece (formsAlgebras Y.obj.hom)) n x) =
      DirectSum.of (hodgePiece (formsAlgebras X.obj.hom)) n
        (hodgePiecePullback f.hom.left X.obj.hom Y.obj.hom (𝟙 _) (hodgeSquare_w f) n x) :=
  hodgeAlgebraPullback_of _ _ _ _ _ n x

/-- The pullback `f^*` on `H^*_{Hodge}` is the direct sum of the pullbacks on the
`H^n_{Hodge}`. -/
theorem hodgePullbackOf_eq_map (f : X ⟶ Y) (a : hodgeAlgebraOf Y) :
    hodgePullbackOf f a = DirectSum.map (fun n =>
      hodgePiecePullback f.hom.left X.obj.hom Y.obj.hom (𝟙 _) (hodgeSquare_w f) n) a := by
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add a a' ha ha' => rw [map_add, map_add, ha, ha']
  | of n x => rw [hodgePullbackOf_of, DirectSum.map_of]

/-! ### The axiom (A1) -/

/-- **`H^*_{Hodge}(∅/k) = 0`.** -/
theorem subsingleton_hodgeAlgebraOf_of_isEmpty (X : (SmoothProjectiveScheme k).FullSubcategory)
    [IsEmpty ((toScheme k).obj X)] : Subsingleton (hodgeAlgebraOf X) := by
  have : IsEmpty X.obj.left := ‹IsEmpty ((toScheme k).obj X)›
  exact ⟨fun a b => DFinsupp.ext fun n => DFinsupp.ext fun i =>
    (subsingleton_hodgeCohomologyComponent_of_isEmpty X.obj.hom i.1.1 (i.1.2 : ℤ)).elim _ _⟩

/-- **`(i^*, j^*) : H^*_{Hodge}(Z/k) ⟶ H^*_{Hodge}(X/k) × H^*_{Hodge}(Y/k)` is bijective** for
a coproduct `Z = X ⨿ Y` of smooth projective `k`-schemes with coprojections `i`, `j`. -/
theorem bijective_hodgePullbackOf_prod {Z : (SmoothProjectiveScheme k).FullSubcategory}
    (i : X ⟶ Z) (j : Y ⟶ Z)
    (hc : IsColimit (BinaryCofan.mk ((toScheme k).map i) ((toScheme k).map j))) :
    Function.Bijective fun a : hodgeAlgebraOf Z => (hodgePullbackOf i a, hodgePullbackOf j a) := by
  have h := bijective_directSum_map_prod
    (fun n => hodgePiecePullback i.hom.left X.obj.hom Z.obj.hom (𝟙 _) (hodgeSquare_w i) n)
    (fun n => hodgePiecePullback j.hom.left Y.obj.hom Z.obj.hom (𝟙 _) (hodgeSquare_w j) n)
    fun n => bijective_directSum_map_prod _ _ fun b =>
      bijective_hodgePullback_prod_of_isColimit Z.obj.hom X.obj.hom Y.obj.hom i.hom.left
        j.hom.left hc (hodgeSquare_w i) (hodgeSquare_w j) b.1.1 (b.1.2 : ℤ)
  convert h using 2 with a
  rw [hodgePullbackOf_eq_map, hodgePullbackOf_eq_map]

variable (k) in
/-- **The axiom (A1) for Hodge cohomology** (Remark 0FWE): `H^*_{Hodge}(∅/k) = 0`, and
`(i^*, j^*) : H^*_{Hodge}(X ⨿ Y/k) ⟶ H^*_{Hodge}(X/k) × H^*_{Hodge}(Y/k)` is bijective. -/
theorem hodge_coproductAxiom : (hodgeFirstChernClassData k).CoproductAxiom :=
  ⟨fun X hX => have := hX; subsingleton_hodgeAlgebraOf_of_isEmpty X,
    fun _ _ _ i j ⟨hc⟩ => bijective_hodgePullbackOf_prod i j hc⟩

/-! ### The axiom (A2) -/

/-- **`f^*c₁^{Hodge}(ℒ) = c₁^{Hodge}(f^*ℒ)`** in `H^2_{Hodge}(X/k)`, for an invertible module
`ℒ` on `Y`. -/
theorem hodgePullbackOf_hodgeFirstChernClassPiece (f : X ⟶ Y)
    (L : ((toScheme k).obj Y).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible ((toScheme k).obj Y).presheaf
      ((toScheme k).obj Y).ringCatSheaf.2 L) :
    hodgePullbackOf f (DirectSum.of (hodgePiece (formsAlgebras Y.obj.hom)) 2
        (hodgeFirstChernClassPiece Y (picardClassOf _ L hL))) =
      DirectSum.of (hodgePiece (formsAlgebras X.obj.hom)) 2
        (hodgeFirstChernClassPiece X (picardClassOf _
          ((Scheme.Modules.pullback ((toScheme k).map f)).obj L)
          (isInvertible_pullback_obj _ L hL))) := by
  rw [hodgePullbackOf_of]
  congr 1
  refine (hodgePiecePullback_of _ _ _ _ _ 2 bidegreeOneOne _).trans ?_
  exact congrArg (DirectSum.of (fun i : HodgeBidegreeInt 2 =>
      (hodgeCohomologyComponent (formsAlgebras X.obj.hom) i.1.1 (i.1.2 : ℤ) : Type u))
      bidegreeOneOne)
    (hodgePullback_hodgeFirstChernClassModule_picardClassOf f.hom.left X.obj.hom Y.obj.hom
      (𝟙 _) (hodgeSquare_w f) L hL)

variable (k) in
/-- **The axiom (A2) for Hodge cohomology** (Remark 0FWE): the Hodge first Chern class is
compatible with pullbacks, `f^*c₁^{Hodge}(ℒ) = c₁^{Hodge}(f^*ℒ)`. -/
theorem hodge_pullbackAxiom : (hodgeFirstChernClassData k).PullbackAxiom := by
  intro X Y f L hL
  change tateTwistMap (hodgePullbackOf f).toLinearMap 1 (hodgeFirstChernClassTw Y _) =
    hodgeFirstChernClassTw X _
  apply (Stacks.DeRhamWeil.untwist (k := k) (hodgeAlgebraOf X) 1).injective
  refine (tateTwistCoordinates_map (F := k) (L := k) (LinearEquiv.refl k k) 1
    (hodgePullbackOf f).toLinearMap _).trans ?_
  have e : ∀ (W : (SmoothProjectiveScheme k).FullSubcategory)
      (c : ((toScheme k).obj W).picardGroup),
      Stacks.DeRhamWeil.untwist (k := k) (hodgeAlgebraOf W) 1 (hodgeFirstChernClassTw W c) =
      DirectSum.of (hodgePiece (formsAlgebras W.obj.hom)) 2 (hodgeFirstChernClassPiece W c) :=
    fun W _ => (Stacks.DeRhamWeil.untwist (k := k) (hodgeAlgebraOf W) 1).apply_symm_apply _
  exact (congrArg (hodgePullbackOf f) (e Y _)).trans
    ((hodgePullbackOf_hodgeFirstChernClassPiece f L hL).trans (e X _).symm)

/-! ### The axiom (A8) -/

/-- **The pullback `g^* : H^0_{Hodge}(S/k) ⟶ H^0_{Hodge}(X/k)` is bijective** when
`g^♯ : Γ(S, 𝒪_S) ⟶ Γ(X, 𝒪_X)` is an isomorphism. -/
theorem bijective_gradedPieceMap_hodgePullbackOf_zero
    {S : (SmoothProjectiveScheme k).FullSubcategory} (g : X ⟶ S)
    (hg : IsIso ((toScheme k).map g).appTop) :
    Function.Bijective (gradedPieceMap (hodgeGradeOf S) (hodgeGradeOf X) (hodgePullbackOf g)
      (hodgePullbackOf_mem_grade g) 0) := by
  have hP := bijective_hodgePiece_zero_map g.hom.left X.obj.hom S.obj.hom (𝟙 _)
    (hodgeSquare_w g) (ConcreteCategory.bijective_of_isIso ((toScheme k).map g).appTop)
  have hcomm : ∀ z : hodgeGradeOf S 0, hodgeGradeEquiv X 0 (gradedPieceMap (hodgeGradeOf S)
      (hodgeGradeOf X) (hodgePullbackOf g) (hodgePullbackOf_mem_grade g) 0 z) =
      hodgePiecePullback g.hom.left X.obj.hom S.obj.hom (𝟙 _) (hodgeSquare_w g) 0
        (hodgeGradeEquiv S 0 z) := by
    intro z
    refine hodgeGradeEquiv_eq_of_coe_eq X _ _ ?_
    obtain ⟨x, hx⟩ := (mem_hodgeGrade _ _ 0 _).1 z.2
    change hodgePullbackOf g (z : hodgeAlgebraOf S) = _
    rw [hx, hodgePullbackOf_of, hodgeGradeEquiv_eq_of_coe_eq S z x hx]
  have hcomp : (hodgeGradeEquiv X 0) ∘ (gradedPieceMap (hodgeGradeOf S) (hodgeGradeOf X)
      (hodgePullbackOf g) (hodgePullbackOf_mem_grade g) 0) =
      (hodgePiecePullback g.hom.left X.obj.hom S.obj.hom (𝟙 _) (hodgeSquare_w g) 0) ∘
        (hodgeGradeEquiv S 0) :=
    funext hcomm
  have h2 : Function.Bijective ((hodgeGradeEquiv X 0) ∘ (gradedPieceMap (hodgeGradeOf S)
      (hodgeGradeOf X) (hodgePullbackOf g) (hodgePullbackOf_mem_grade g) 0)) := by
    rw [hcomp]
    exact hP.comp (hodgeGradeEquiv S 0).bijective
  exact (Function.Bijective.of_comp_iff' (hodgeGradeEquiv X 0).bijective _).1 h2

variable (k) in
/-- **The axiom (A8) for Hodge cohomology** (Remark 0FWE): for `X` smooth projective over `k` and
`k' = Γ(X, 𝒪_X)`, the pullback `H^0_{Hodge}(Spec k'/k) ⟶ H^0_{Hodge}(X/k)` along the canonical
morphism `X ⟶ Spec k'` is bijective. That morphism induces `Γ(Spec k', 𝒪) = k' ≅ Γ(X, 𝒪_X)`,
so this is `bijective_gradedPieceMap_hodgePullbackOf_zero`. -/
theorem hodge_globalSectionsAxiom : (hodgeFirstChernClassData k).GlobalSectionsAxiom := fun X =>
  bijective_gradedPieceMap_hodgePullbackOf_zero (toSpecGlobalSections X) (by
    change IsIso X.obj.left.toSpecΓ.appTop
    rw [Scheme.toSpecΓ_appTop]
    infer_instance)

end Stacks.HodgeWeil

end
