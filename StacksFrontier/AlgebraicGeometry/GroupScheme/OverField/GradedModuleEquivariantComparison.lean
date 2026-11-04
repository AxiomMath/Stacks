module

public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import
  StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GradedModuleGradingOfEquivariantModule

/-!
# The canonical grading of the global sections of an equivariant module

Let `A` be an integer-graded commutative ring, let `X = Spec A` and let the multiplicative
group `𝐆ₘ` act on `X` through the grading.  For a `𝐆ₘ`-equivariant quasi-coherent `𝒪_X`-module
`F` the canonical homogeneous pieces of `M = Γ(X, F)` decompose `M`: they make it an internal
direct sum.

The coordinate ring of the scheme of arrows `𝐆ₘ × X` is `ℤ[x,x⁻¹] ⊗ A`, which is free over `A`
on the Laurent monomials `xⁿ`, so the descent morphism `α` of the equivariant structure writes
the canonical pullback section of a global section `m` *uniquely* as `∑ xⁿ · (cₙ(m) ⊗ 1)`.  The
resulting coefficient map `c` is a family of finite-support projections: the normalization of
`α` along the unit section says that the coefficients of `m` sum to `m`, and the cocycle law of
`α`, read over the model `(ℤ[x,x⁻¹] ⊗ ℤ[y,y⁻¹]) ⊗ A` of a composable pair of arrows, says that
they are mutually orthogonal.  The pieces cut out by `c` are the canonical homogeneous pieces,
so those decompose `M`.

## Main definitions

* `AlgebraicGeometry.GmEquivariant.laurentCoeffEquiv` and
  `AlgebraicGeometry.GmEquivariant.laurentDoubleCoeffEquiv` identify a single and a double
  Laurent base change of `A` with finitely supported families over `A`.
* `AlgebraicGeometry.GmEquivariant.doubleCoefficients` is a coefficient map iterated twice.
* `AlgebraicGeometry.GmEquivariant.doubleArrowPair` is the model of a composable pair of arrows
  of the action, a point of the scheme of composable pairs with coordinate ring
  `(ℤ[x,x⁻¹] ⊗ ℤ[y,y⁻¹]) ⊗ A`.
* `AlgebraicGeometry.GmEquivariant.coefficients` is the Laurent coefficient map of an
  equivariant module.

## Main results

* `AlgebraicGeometry.GmEquivariant.bijective_sectionsCombination_laurentCoordinate`: a global
  section of the pullback of a quasi-coherent module along the projection of the scheme of
  arrows has unique Laurent coefficients.
* `AlgebraicGeometry.GmEquivariant.identityAction_apply_of_sectionsCombination` and
  `AlgebraicGeometry.GmEquivariant.isDescentCocycle_sectionsCombination` read the normalization
  along the unit section and the cocycle law of a descent morphism on coefficients.
* `AlgebraicGeometry.GmEquivariant.sum_coefficients` and
  `AlgebraicGeometry.GmEquivariant.coefficients_coefficients` are those two laws for the Laurent
  coefficient map, and `AlgebraicGeometry.GmEquivariant.piece_coefficients` identifies the
  pieces it cuts out with the canonical homogeneous pieces.
* `AlgebraicGeometry.GmEquivariant.homogeneousPartDecomposition` is the resulting internal
  direct sum decomposition of the global sections.

## Implementation notes

The cocycle law is used in the form `Stacks.Groupoids.IsDescentCocycle`, whose three structure
morphisms out of the scheme of composable pairs are ordinary morphisms of schemes rather than
morphisms over the base; the composites appearing in it are then spelled exactly as the
reindexing of a descent morphism spells them, which is what makes the five-step evaluation of
the law on a section go through.

The nested tensor product `(ℤ[x,x⁻¹] ⊗ ℤ[y,y⁻¹]) ⊗ A` over the universe-lifted integers needs
its ring and algebra instances declared by hand: the lifted base ring makes the search for them
exceed the depth allowed for pending instances.

## References

* [Stacks Project, Tag 0EKL](https://stacks.math.columbia.edu/tag/0EKL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Stacks.Groupoids
open scoped DirectSum CategoryTheory.MonObj ChangeOfRings

universe u v w

namespace AlgebraicGeometry.GmEquivariant

/-! ### Free base change along a Laurent-polynomial algebra -/

section FreeLaurent

variable (R₀ : Type u) [CommRing R₀] (A : Type u) [CommRing A] [Algebra R₀ A]

/-- The coefficients of a Laurent polynomial with coefficients extended along `R₀ → A`. -/
noncomputable def laurentCoeffEquiv :
    TensorProduct R₀ (LaurentPolynomial R₀) A ≃ₗ[R₀] (ℤ →₀ A) :=
  ((AddMonoidAlgebra.coeffLinearEquiv R₀).rTensor A).trans
    (TensorProduct.finsuppScalarLeft R₀ A ℤ)

/-- The Laurent base change is semilinear over `A`. -/
theorem laurentCoeffEquiv_smul (a : A) (x : TensorProduct R₀ (LaurentPolynomial R₀) A) :
    laurentCoeffEquiv R₀ A (((1 : LaurentPolynomial R₀) ⊗ₜ[R₀] a) * x) =
      a • laurentCoeffEquiv R₀ A x := by
  induction x with
  | zero => simp
  | tmul l b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      ext i
      simp [laurentCoeffEquiv, smul_eq_mul]
  | add x y hx hy => rw [mul_add, map_add, map_add, hx, hy, smul_add]

/-- The Laurent monomials are a basis of the Laurent base change. -/
theorem laurentCoeffEquiv_T_tmul_one (n : ℤ) :
    laurentCoeffEquiv R₀ A (LaurentPolynomial.T n ⊗ₜ[R₀] (1 : A)) = Finsupp.single n 1 := by
  change TensorProduct.finsuppScalarLeft R₀ A ℤ
    ((AddMonoidAlgebra.coeffLinearEquiv R₀) (LaurentPolynomial.T n) ⊗ₜ[R₀] (1 : A)) = _
  rw [show (AddMonoidAlgebra.coeffLinearEquiv R₀) (LaurentPolynomial.T n) =
      Finsupp.single n (1 : R₀) from rfl]
  exact finsuppScalarLeft_single_one_tmul n (1 : A)

/-- The coefficients of a pair of Laurent polynomials with coefficients extended along
`R₀ → A`. -/
noncomputable def laurentDoubleCoeffEquiv :
    TensorProduct R₀ (TensorProduct R₀ (LaurentPolynomial R₀) (LaurentPolynomial R₀)) A
      ≃ₗ[R₀] ((ℤ × ℤ) →₀ A) :=
  (((AddMonoidAlgebra.tensorEquiv R₀).rTensor A).trans
    ((AddMonoidAlgebra.coeffLinearEquiv R₀).rTensor A)).trans
    (TensorProduct.finsuppScalarLeft R₀ A (ℤ × ℤ))

/-- The double Laurent base change is semilinear over `A`. -/
theorem laurentDoubleCoeffEquiv_smul (a : A)
    (x : TensorProduct R₀ (TensorProduct R₀ (LaurentPolynomial R₀) (LaurentPolynomial R₀)) A) :
    laurentDoubleCoeffEquiv R₀ A
        (((1 : TensorProduct R₀ (LaurentPolynomial R₀) (LaurentPolynomial R₀))
          ⊗ₜ[R₀] a) * x) =
      a • laurentDoubleCoeffEquiv R₀ A x := by
  induction x with
  | zero => simp
  | tmul l b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      ext i
      simp [laurentDoubleCoeffEquiv, smul_eq_mul]
  | add x y hx hy => rw [mul_add, map_add, map_add, hx, hy, smul_add]

/-- The pairs of Laurent monomials are a basis of the double Laurent base change. -/
theorem laurentDoubleCoeffEquiv_T_tmul_one (n k : ℤ) :
    laurentDoubleCoeffEquiv R₀ A
        ((LaurentPolynomial.T n ⊗ₜ[R₀] LaurentPolynomial.T k) ⊗ₜ[R₀] (1 : A)) =
      Finsupp.single (n, k) 1 := by
  change TensorProduct.finsuppScalarLeft R₀ A (ℤ × ℤ)
    ((AddMonoidAlgebra.coeffLinearEquiv R₀)
      ((AddMonoidAlgebra.tensorEquiv R₀)
        (LaurentPolynomial.T n ⊗ₜ[R₀] LaurentPolynomial.T k)) ⊗ₜ[R₀] (1 : A)) = _
  rw [show LaurentPolynomial.T n = AddMonoidAlgebra.single n (1 : R₀) from rfl,
    show LaurentPolynomial.T k = AddMonoidAlgebra.single k (1 : R₀) from rfl,
    AddMonoidAlgebra.tensorEquiv_single_tmul_single,
    AddMonoidAlgebra.coeffLinearEquiv_apply, one_mul]
  exact finsuppScalarLeft_single_one_tmul (n, k) (1 : A)

end FreeLaurent

attribute [local instance 100] ULift.algebra'

attribute [local implicit_reducible] CategoryTheory.OverClass.asOver

/-! ### Combinations of canonical pullback sections, continued -/

section Combinations

/-- A combination of canonical pullback sections with trivial coefficients is the canonical
pullback section of the sum of the coefficients. -/
theorem sectionsCombination_one {W Z : Scheme.{u}} (p : W ⟶ Z) (F : Z.Modules)
    {Idx : Type*} (x : Idx →₀ Γ(F, ⊤)) :
    sectionsCombination p F (fun _ => 1) x = pullbackSection p F (x.sum fun _ b => b) := by
  rw [sectionsCombination_apply]
  simp only [one_smul]
  exact (map_finsuppSum (pullbackSectionHom p F) x fun _ b => b).symm

/-- Reindexing the coefficients of a combination of canonical pullback sections. -/
theorem sectionsCombination_comp_mapDomain {W Z : Scheme.{u}} (p : W ⟶ Z) (F : Z.Modules)
    {Idx Jdx : Type*} (ρ : Jdx → Γ(W, ⊤)) (f : Idx → Jdx) :
    (sectionsCombination p F ρ).comp (Finsupp.mapDomain.addMonoidHom f) =
      sectionsCombination p F (ρ ∘ f) := by
  apply Finsupp.addHom_ext
  intro i b
  rw [AddMonoidHom.comp_apply]
  change sectionsCombination p F ρ (Finsupp.mapDomain f (Finsupp.single i b)) = _
  rw [Finsupp.mapDomain_single, sectionsCombination_single, sectionsCombination_single]
  rfl

/-- The comparison of the pullbacks along two equal morphisms carries a combination of canonical
pullback sections to the corresponding combination. -/
theorem app_sectionsCombination_of_congr {W Z : Scheme.{u}} {f g : W ⟶ Z} (h : f = g)
    (F : Z.Modules) {Idx : Type*} (r : Idx → Γ(W, ⊤)) (x : Idx →₀ Γ(F, ⊤)) :
    ((Scheme.Modules.pullbackCongr h).hom.app F).app ⊤ (sectionsCombination f F r x) =
      sectionsCombination g F r x := by
  subst h
  rfl

/-- A morphism out of a pullback carries a combination of canonical pullback sections to the
combination of its values on them. -/
theorem app_sectionsCombination {W Z : Scheme.{u}} (p : W ⟶ Z) (F : Z.Modules)
    {N : W.Modules} (k : (Scheme.Modules.pullback p).obj F ⟶ N)
    {Idx : Type*} (r : Idx → Γ(W, ⊤)) (x : Idx →₀ Γ(F, ⊤)) :
    k.app ⊤ (sectionsCombination p F r x) =
      x.sum fun i b => r i • k.app ⊤ (pullbackSection p F b) := by
  let K : Γ((Scheme.Modules.pullback p).obj F, ⊤) →+ Γ(N, ⊤) :=
    { toFun := fun z => k.app ⊤ z
      map_zero' := map_zero _
      map_add' := fun z w => map_add _ _ _ }
  rw [sectionsCombination_apply]
  change K _ = _
  rw [map_finsuppSum K]
  exact Finsupp.sum_congr fun i _ => k.app_smul _ _

/-- Iterating a coefficient map twice, as a finitely supported family indexed by pairs. -/
noncomputable def doubleCoefficients {M : Type w} [AddCommGroup M] {Idx : Type*}
    (c : M →+ (Idx →₀ M)) (m : M) : (Idx × Idx) →₀ M :=
  (c m).sum fun i b => (c b).sum fun j d => Finsupp.single (i, j) d

/-- A combination of canonical pullback sections indexed by the twice-iterated coefficients. -/
theorem sectionsCombination_doubleCoefficients {W Z : Scheme.{u}} (p : W ⟶ Z) (F : Z.Modules)
    {Idx : Type*} (ρ : Idx × Idx → Γ(W, ⊤)) (c : Γ(F, ⊤) →+ (Idx →₀ Γ(F, ⊤)))
    (m : Γ(F, ⊤)) :
    sectionsCombination p F ρ (doubleCoefficients c m) =
      (c m).sum fun i b => (c b).sum fun j d => ρ (i, j) • pullbackSection p F d := by
  rw [doubleCoefficients, map_finsuppSum (sectionsCombination p F ρ)]
  refine Finsupp.sum_congr fun i _ => ?_
  rw [map_finsuppSum (sectionsCombination p F ρ)]
  exact Finsupp.sum_congr fun j _ => sectionsCombination_single p F ρ (i, j) _

/-- Reindexing a descent morphism preserves the property of writing a canonical pullback section
as a combination of canonical pullback sections, the coefficients being pulled back as well. -/
theorem reindexHom_sectionsCombination {W Z Z' : Scheme.{u}} (f : W ⟶ Z) {g h : Z ⟶ Z'}
    {F : Z'.Modules}
    (a : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback h).obj F)
    (s : Γ(F, ⊤)) {Idx : Type*} (r : Idx → Γ(Z, ⊤)) (x : Idx →₀ Γ(F, ⊤))
    (ha : a.app ⊤ (pullbackSection g F s) = sectionsCombination h F r x) :
    (reindexHom f a).app ⊤ (pullbackSection (f ≫ g) F s) =
      sectionsCombination (f ≫ h) F (fun i => f.appTop (r i)) x := by
  simp only [reindexHom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    pullbackSection_comp_inv]
  rw [pullbackSection_naturality f a, ha]
  exact DFunLike.congr_fun (pullbackTransport_sectionsCombination f h F r) x

/-- Chaining two known values of morphisms of modules on global sections. -/
private alias comp_app_trans := comp_app_of_eq

end Combinations

/-! ### The two action laws, read on coefficients -/

section ActionLaws

variable {S : Scheme.{u}} (Y : Over S) (G X : Over Y.left) [GrpObj G] [ModObj G X]

/-- A descent morphism which writes a canonical pullback section as a combination of canonical
pullback sections, with coefficients trivial along the unit section, restricts along that
section to the sum of the coefficients. -/
theorem identityAction_apply_of_sectionsCombination {F : X.left.Modules}
    (α : (Scheme.Modules.pullback γ[G,X].left).obj F ⟶
      (Scheme.Modules.pullback (snd G X).left).obj F)
    (s : Γ(F, ⊤)) {Idx : Type*} (r : Idx → Γ((G ⊗ X).left, ⊤)) (x : Idx →₀ Γ(F, ⊤))
    (ha : α.app ⊤ (pullbackSection γ[G,X].left F s) =
      sectionsCombination (snd G X).left F r x)
    (hr : ∀ i, (Stacks.Groupoids.ActionGroupoid.identity G X).left.appTop (r i) = 1) :
    (identityAction Y G X α).app ⊤ s = x.sum fun _ b => b := by
  have h₀ := pullbackSection_id_inv X.left F s
  have h₁ := pullbackSection_congr (actionIdentity_target_left Y G X).symm F s
  have h₂ : (reindexHom (Stacks.Groupoids.ActionGroupoid.identity G X).left α).app ⊤
      (pullbackSection ((Stacks.Groupoids.ActionGroupoid.identity G X).left ≫ γ[G,X].left) F s) =
      pullbackSection ((Stacks.Groupoids.ActionGroupoid.identity G X).left ≫ (snd G X).left) F
        (x.sum fun _ b => b) := by
    rw [reindexHom_sectionsCombination
        (Stacks.Groupoids.ActionGroupoid.identity G X).left α s r x ha,
      show (fun i => (Stacks.Groupoids.ActionGroupoid.identity G X).left.appTop (r i)) =
          (fun _ => (1 : Γ(X.left, ⊤))) from funext hr, sectionsCombination_one]
  have h₃ := pullbackSection_congr (actionIdentity_source_left Y G X) F
    (x.sum fun _ b => b)
  have h₄ := pullbackSection_id_hom X.left F (x.sum fun _ b => b)
  exact comp_app_trans _ _ h₀ (comp_app_trans _ _ h₁
    (comp_app_trans _ _ h₂ (comp_app_trans _ _ h₃ h₄)))

/-- A descent morphism satisfying the cocycle condition, read on coefficients: the
twice-iterated coefficients with the product functions and the coefficients with the composite
functions are the same combination of canonical pullback sections. -/
theorem isDescentCocycle_sectionsCombination {D R U : Scheme.{u}} (p q cm : D ⟶ R) (t s : R ⟶ U)
    (ht : cm ≫ t = p ≫ t) (hm : p ≫ s = q ≫ t) (hs : cm ≫ s = q ≫ s) {F : U.Modules}
    (α : (Scheme.Modules.pullback t).obj F ⟶ (Scheme.Modules.pullback s).obj F)
    (hcoc : IsDescentCocycle p q cm t s ht hm hs α)
    {Idx : Type*} (r : Idx → Γ(R, ⊤)) (c : Γ(F, ⊤) →+ (Idx →₀ Γ(F, ⊤)))
    (ha : ∀ z, α.app ⊤ (pullbackSection t F z) = sectionsCombination s F r (c z))
    (m : Γ(F, ⊤)) :
    sectionsCombination (cm ≫ s) F
        (fun ij : Idx × Idx => p.appTop (r ij.1) * q.appTop (r ij.2))
        (doubleCoefficients c m) =
      sectionsCombination (cm ≫ s) F (fun i => cm.appTop (r i)) (c m) := by
  have h₀ := pullbackSection_congr ht F m
  have h₁ := reindexHom_sectionsCombination p α m r (c m) (ha m)
  have h₂ := app_sectionsCombination_of_congr hm F (fun i => p.appTop (r i)) (c m)
  have h₃ : (reindexHom q α).app ⊤
      (sectionsCombination (q ≫ t) F (fun i => p.appTop (r i)) (c m)) =
      sectionsCombination (q ≫ s) F
        (fun ij : Idx × Idx => p.appTop (r ij.1) * q.appTop (r ij.2))
        (doubleCoefficients c m) := by
    rw [app_sectionsCombination, sectionsCombination_doubleCoefficients]
    refine Finsupp.sum_congr fun i _ => ?_
    rw [reindexHom_sectionsCombination q α _ r (c _) (ha _), sectionsCombination_apply,
      Finsupp.smul_sum]
    exact Finsupp.sum_congr fun j _ => smul_smul _ _ _
  have h₄ := app_sectionsCombination_of_congr hs.symm F
    (fun ij : Idx × Idx => p.appTop (r ij.1) * q.appTop (r ij.2)) (doubleCoefficients c m)
  have hD := comp_app_trans _ _ h₀ (comp_app_trans _ _ h₁
    (comp_app_trans _ _ h₂ (comp_app_trans _ _ h₃ h₄)))
  rw [← hD, hcoc]
  exact reindexHom_sectionsCombination cm α m r (c m) (ha m)

end ActionLaws

/-! ### Unique Laurent coefficients of a section of the pullback along the projection -/

section Coefficients

variable {A : Type u} [CommRing A]

/-- The inclusion of the coordinate ring of `Spec A` into that of the scheme of arrows. -/
noncomputable abbrev projectionRingHom (A : Type u) [CommRing A] :
    CommRingCat.of A ⟶
      CommRingCat.of (TensorProduct (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A) :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := ULift.{u} ℤ)
    (A := LaurentPolynomial (ULift.{u} ℤ)) (B := A)).toRingHom

/-- The projection of the scheme of arrows factors the affine fibre-product identification
through the inclusion of the second tensor factor. -/
theorem snd_gm_left_eq :
    (snd gm.{u} (specAOver A)).left =
      (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).hom ≫
        Spec.map (projectionRingHom A) :=
  (pullbackSpecIso_hom_snd (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).symm

/-- The Laurent monomial `xⁿ`, read in the coordinate ring of the scheme of arrows. -/
theorem laurentCoordinate_eq (n : ℤ) :
    laurentCoordinate A n =
      (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).hom.appTop
        ((Scheme.ΓSpecIso (.of (TensorProduct (ULift.{u} ℤ)
            (LaurentPolynomial (ULift.{u} ℤ)) A))).inv
          (LaurentPolynomial.T n ⊗ₜ[ULift.{u} ℤ] (1 : A))) := by
  have hf : (fst gm.{u} (specAOver A)).left =
      (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).hom ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := ULift.{u} ℤ)
            (A := LaurentPolynomial (ULift.{u} ℤ)) (B := A))) :=
    (pullbackSpecIso_hom_fst (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).symm
  change (fst gm.{u} (specAOver A)).left.appTop _ = _
  rw [hf]
  exact comp_specMap_appTop_inv _ _ _

/-- **Unique Laurent coefficients.** Every global section of the pullback of a quasi-coherent
module along the projection of the scheme of arrows is uniquely a combination of the canonical
pullback sections with the characters `xⁿ` as coefficients. -/
theorem bijective_sectionsCombination_laurentCoordinate
    (F : (Spec (.of A)).Modules) [F.IsQuasicoherent] :
    Function.Bijective
      (sectionsCombination (snd gm.{u} (specAOver A)).left F (laurentCoordinate A)) := by
  set e := pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A with he
  set t : ℤ → TensorProduct (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A :=
    fun n => LaurentPolynomial.T n ⊗ₜ[ULift.{u} ℤ] (1 : A) with hteq
  have heta : ∀ (a : A)
      (x : TensorProduct (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A),
      laurentCoeffEquiv (ULift.{u} ℤ) A (projectionRingHom A a * x) =
        a • laurentCoeffEquiv (ULift.{u} ℤ) A x := fun a x =>
    laurentCoeffEquiv_smul (ULift.{u} ℤ) A a x
  have hbij : Function.Bijective (sectionsCombination (Spec.map (projectionRingHom A)) F
      fun n => (Scheme.ΓSpecIso (.of (TensorProduct (ULift.{u} ℤ)
        (LaurentPolynomial (ULift.{u} ℤ)) A))).inv (t n)) :=
    bijective_sectionsCombination_specMap (projectionRingHom A) F
      (laurentCoeffEquiv (ULift.{u} ℤ) A).toAddEquiv heta t
      (laurentCoeffEquiv_T_tmul_one (ULift.{u} ℤ) A)
  have hb : Function.Bijective
      ((pullbackTransport e.hom (Spec.map (projectionRingHom A)) F).comp
        (sectionsCombination (Spec.map (projectionRingHom A)) F
          fun n => (Scheme.ΓSpecIso (.of (TensorProduct (ULift.{u} ℤ)
            (LaurentPolynomial (ULift.{u} ℤ)) A))).inv (t n))) :=
    (bijective_pullbackTransport e.hom (Spec.map (projectionRingHom A)) F).comp hbij
  rw [pullbackTransport_sectionsCombination] at hb
  rw [snd_gm_left_eq, show (laurentCoordinate A) =
    fun n => e.hom.appTop ((Scheme.ΓSpecIso (.of (TensorProduct (ULift.{u} ℤ)
      (LaurentPolynomial (ULift.{u} ℤ)) A))).inv (t n)) from funext laurentCoordinate_eq]
  exact hb

end Coefficients

/-! ### The scheme of composable pairs of arrows, modelled on a double Laurent ring -/

section DoubleArrow

variable (A : Type u) [CommRing A]

/-- The coordinate ring of a composable pair of arrows is a commutative ring.  The instance is
declared because the nested tensor product exceeds the search depth for pending instances. -/
noncomputable instance instCommRingDoubleLaurent :
    CommRing (TensorProduct (ULift.{u} ℤ) (TensorProduct (ULift.{u} ℤ)
      (LaurentPolynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ))) A) :=
  Algebra.TensorProduct.instCommRing

/-- The coordinate ring of a composable pair of arrows is an algebra over the integers. -/
noncomputable instance instAlgebraDoubleLaurent :
    Algebra (ULift.{u} ℤ) (TensorProduct (ULift.{u} ℤ) (TensorProduct (ULift.{u} ℤ)
      (LaurentPolynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ))) A) :=
  Algebra.TensorProduct.instAlgebra

/-- The spectrum of the coordinate ring of a composable pair of arrows of a `𝐆ₘ`-action on
`Spec A` — two Laurent variables and the ring — as a scheme over `Spec ℤ`. -/
noncomputable abbrev doubleArrowOver : Over (Spec (.of (ULift.{u} ℤ))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ)
    (TensorProduct (ULift.{u} ℤ) (TensorProduct (ULift.{u} ℤ)
      (LaurentPolynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ))) A))))

/-- The first Laurent variable of a composable pair: `x ↦ (x ⊗ 1) ⊗ 1`. -/
noncomputable def doubleArrowFirstHom :
    LaurentPolynomial (ULift.{u} ℤ) →ₐ[ULift.{u} ℤ]
      TensorProduct (ULift.{u} ℤ) (TensorProduct (ULift.{u} ℤ)
        (LaurentPolynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ))) A :=
  (Algebra.TensorProduct.includeLeft (R := ULift.{u} ℤ) (S := ULift.{u} ℤ)
      (A := TensorProduct (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ))
        (LaurentPolynomial (ULift.{u} ℤ))) (B := A)).comp
    (Algebra.TensorProduct.includeLeft (R := ULift.{u} ℤ) (S := ULift.{u} ℤ)
      (A := LaurentPolynomial (ULift.{u} ℤ)) (B := LaurentPolynomial (ULift.{u} ℤ)))

/-- The second Laurent variable of a composable pair: `y ↦ (1 ⊗ y) ⊗ 1`. -/
noncomputable def doubleArrowSecondHom :
    LaurentPolynomial (ULift.{u} ℤ) →ₐ[ULift.{u} ℤ]
      TensorProduct (ULift.{u} ℤ) (TensorProduct (ULift.{u} ℤ)
        (LaurentPolynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ))) A :=
  (Algebra.TensorProduct.includeLeft (R := ULift.{u} ℤ) (S := ULift.{u} ℤ)
      (A := TensorProduct (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ))
        (LaurentPolynomial (ULift.{u} ℤ))) (B := A)).comp
    (Algebra.TensorProduct.includeRight (R := ULift.{u} ℤ)
      (A := LaurentPolynomial (ULift.{u} ℤ)) (B := LaurentPolynomial (ULift.{u} ℤ)))

/-- The ring of the scheme acted on, read in the coordinate ring of a composable pair:
`a ↦ 1 ⊗ a`. -/
noncomputable def doubleArrowBaseHom :
    A →ₐ[ULift.{u} ℤ]
      TensorProduct (ULift.{u} ℤ) (TensorProduct (ULift.{u} ℤ)
        (LaurentPolynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ))) A :=
  Algebra.TensorProduct.includeRight

/-- The first Laurent variable, as a morphism to the multiplicative group over `Spec ℤ`. -/
noncomputable def doubleArrowFirst : doubleArrowOver A ⟶ gm.{u} :=
  Over.homMk (Spec.map (CommRingCat.ofHom (doubleArrowFirstHom A).toRingHom))
    (by
      change Spec.map (CommRingCat.ofHom (doubleArrowFirstHom A).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (LaurentPolynomial.C (R := ULift.{u} ℤ))) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      refine congrArg Spec.map (congrArg CommRingCat.ofHom ?_)
      ext x
      exact (doubleArrowFirstHom A).commutes x)

/-- The second Laurent variable, as a morphism to the multiplicative group over `Spec ℤ`. -/
noncomputable def doubleArrowSecond : doubleArrowOver A ⟶ gm.{u} :=
  Over.homMk (Spec.map (CommRingCat.ofHom (doubleArrowSecondHom A).toRingHom))
    (by
      change Spec.map (CommRingCat.ofHom (doubleArrowSecondHom A).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (LaurentPolynomial.C (R := ULift.{u} ℤ))) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      refine congrArg Spec.map (congrArg CommRingCat.ofHom ?_)
      ext x
      exact (doubleArrowSecondHom A).commutes x)

/-- The ring of the scheme acted on, as a morphism from the model of a composable pair. -/
noncomputable def doubleArrowBase : doubleArrowOver A ⟶ specAOver A :=
  Over.homMk (Spec.map (CommRingCat.ofHom (doubleArrowBaseHom A).toRingHom))
    (by
      rw [show (specAOver A).hom =
          Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A)) from
        specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      refine congrArg Spec.map (congrArg CommRingCat.ofHom ?_)
      ext x
      exact (doubleArrowBaseHom A).commutes x)

/-- The character `xⁿ` of an arrow of the scheme of arrows, pulled back to the model of a
composable pair, in terms of the Laurent variable giving that arrow. -/
private theorem appTop_laurentCoordinate_of_comp_fst (f : doubleArrowOver A ⟶ gm.{u} ⊗ specAOver A)
    (g : doubleArrowOver A ⟶ gm.{u}) (hf : f ≫ fst gm.{u} (specAOver A) = g)
    (φ : LaurentPolynomial (ULift.{u} ℤ) →ₐ[ULift.{u} ℤ]
      TensorProduct (ULift.{u} ℤ) (TensorProduct (ULift.{u} ℤ)
        (LaurentPolynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ))) A)
    (hφ : g.left = Spec.map (CommRingCat.ofHom φ.toRingHom)) (n : ℤ) :
    f.left.appTop (laurentCoordinate A n) =
      (Scheme.ΓSpecIso (.of (TensorProduct (ULift.{u} ℤ) (TensorProduct (ULift.{u} ℤ)
        (LaurentPolynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ))) A))).inv
        (φ (LaurentPolynomial.T n)) := by
  rw [show laurentCoordinate A n = (fst gm.{u} (specAOver A)).left.appTop
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial (ULift.{u} ℤ)))).inv
        (LaurentPolynomial.T n)) from rfl,
    ← appTop_comp_left, hf, hφ]
  exact specMap_appTop_inv _ _

/-- Over the model of a composable pair, the coefficients of a pair of Laurent monomials are
unique. -/
theorem injective_sectionsCombination_doubleArrow (F : (Spec (.of A)).Modules)
    [F.IsQuasicoherent] :
    Function.Injective (sectionsCombination
      (Spec.map (CommRingCat.ofHom (doubleArrowBaseHom A).toRingHom)) F
      (fun ij : ℤ × ℤ =>
        (Scheme.ΓSpecIso (.of (TensorProduct (ULift.{u} ℤ) (TensorProduct (ULift.{u} ℤ)
          (LaurentPolynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ))) A))).inv
          ((LaurentPolynomial.T ij.1 ⊗ₜ[ULift.{u} ℤ] LaurentPolynomial.T ij.2)
            ⊗ₜ[ULift.{u} ℤ] (1 : A)))) :=
  (bijective_sectionsCombination_specMap
    (CommRingCat.ofHom (doubleArrowBaseHom A).toRingHom) F
    (laurentDoubleCoeffEquiv (ULift.{u} ℤ) A).toAddEquiv
    (fun a x => laurentDoubleCoeffEquiv_smul (ULift.{u} ℤ) A a x)
    (fun ij : ℤ × ℤ => (LaurentPolynomial.T ij.1 ⊗ₜ[ULift.{u} ℤ]
      LaurentPolynomial.T ij.2) ⊗ₜ[ULift.{u} ℤ] (1 : A))
    (fun ij => laurentDoubleCoeffEquiv_T_tmul_one (ULift.{u} ℤ) A ij.1 ij.2)).injective

end DoubleArrow

/-! ### The canonical grading of the global sections -/

section Grading

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℤ → σ) [GradedRing 𝒜]

/-- The underlying module of a `𝐆ₘ`-equivariant quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherent_underlyingModule (F : GradedEquivariantModule.{u} 𝒜) :
    (underlyingModule 𝒜 F).IsQuasicoherent :=
  @EquivariantModule.isQuasicoherent _ base.{u} gm.{u} (specAOver A)
    AlgebraicGeometry.instGrpObjSpecAsOverSpec (gradedGmAction 𝒜).action F

/-- Every global section of the pullback of the underlying module along the projection of the
scheme of arrows has unique Laurent coefficients. -/
theorem bijective_laurentCombination (F : GradedEquivariantModule.{u} 𝒜) :
    Function.Bijective (sectionsCombination (snd gm.{u} (specAOver A)).left
      (underlyingModule 𝒜 F) (laurentCoordinate A)) :=
  @bijective_sectionsCombination_laurentCoordinate A _ (underlyingModule 𝒜 F)
    (isQuasicoherent_underlyingModule 𝒜 F)

/-- The Laurent coefficient map of a `𝐆ₘ`-equivariant quasi-coherent module: the unique
coefficients writing the descent morphism of a canonical pullback section as a combination of
canonical pullback sections with the characters `xⁿ`. -/
noncomputable def coefficients (F : GradedEquivariantModule.{u} 𝒜) :
    Γ(underlyingModule 𝒜 F, ⊤) →+ (ℤ →₀ Γ(underlyingModule 𝒜 F, ⊤)) :=
  (AddEquiv.ofBijective _ (bijective_laurentCombination 𝒜 F)).symm.toAddMonoidHom.comp
    (((descentMorphism 𝒜 F).app ⊤).hom.comp
      (pullbackSectionHom (gradedGmAction 𝒜).action.smul.left (underlyingModule 𝒜 F)))

/-- The Laurent coefficients do write the descent morphism of a canonical pullback section as a
combination of canonical pullback sections. -/
theorem sectionsCombination_coefficients (F : GradedEquivariantModule.{u} 𝒜)
    (m : Γ(underlyingModule 𝒜 F, ⊤)) :
    sectionsCombination (snd gm.{u} (specAOver A)).left (underlyingModule 𝒜 F)
        (laurentCoordinate A) (coefficients 𝒜 F m) =
      (descentMorphism 𝒜 F).app ⊤
        (pullbackSection (gradedGmAction 𝒜).action.smul.left (underlyingModule 𝒜 F) m) :=
  (AddEquiv.ofBijective _ (bijective_laurentCombination 𝒜 F)).apply_symm_apply _

/-- A section lies in the `n`-th piece cut out by the Laurent coefficients exactly when it lies
in the canonical degree-`n` piece. -/
theorem mem_piece_coefficients_iff (F : GradedEquivariantModule.{u} 𝒜) (n : ℤ)
    (m : Γ(underlyingModule 𝒜 F, ⊤)) :
    m ∈ piece (coefficients 𝒜 F) n ↔ m ∈ homogeneousPart 𝒜 F n :=
  (mem_piece_iff (coefficients 𝒜 F) n m).trans
    (Iff.trans
      ⟨fun h => by rw [← sectionsCombination_coefficients 𝒜 F m, h,
          sectionsCombination_single],
        fun h => (bijective_laurentCombination 𝒜 F).injective (by
          rw [sectionsCombination_coefficients 𝒜 F m, h, sectionsCombination_single])⟩
      (mem_homogeneousPart_iff 𝒜 F n m).symm)

/-- The pieces cut out by the Laurent coefficients are the canonical homogeneous pieces. -/
theorem piece_coefficients (F : GradedEquivariantModule.{u} 𝒜) :
    piece (coefficients 𝒜 F) = homogeneousPart 𝒜 F :=
  funext fun n => AddSubgroup.ext fun m => mem_piece_coefficients_iff 𝒜 F n m

/-- **The Laurent coefficients sum to the section.** This is the normalization of the descent
morphism along the unit section of the action, read on coefficients. -/
theorem sum_coefficients (F : GradedEquivariantModule.{u} 𝒜)
    (m : Γ(underlyingModule 𝒜 F, ⊤)) :
    (coefficients 𝒜 F m).sum (fun _ b => b) = m := by
  let : GrpObj (gm.{u} : Over base.{u}.left) := AlgebraicGeometry.instGrpObjSpecAsOverSpec
  let : ModObj (gm.{u} : Over base.{u}.left) (specAOver A : Over base.{u}.left) :=
    (gradedGmAction 𝒜).action
  have hr : ∀ n : ℤ, (Stacks.Groupoids.ActionGroupoid.identity gm.{u} (specAOver A)).left.appTop
      (laurentCoordinate A n) = 1 := fun n =>
    actionIdentity_appTop_fst_appTop base.{u} gm.{u} (specAOver A)
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial (ULift.{u} ℤ)))).inv (LaurentPolynomial.T n))
      (gm_one_appTop_laurent n)
  have h := identityAction_apply_of_sectionsCombination base.{u} gm.{u} (specAOver A)
    (descentMorphism 𝒜 F) m (laurentCoordinate A) (coefficients 𝒜 F m)
    (sectionsCombination_coefficients 𝒜 F m).symm hr
  rw [@EquivariantModule.identity _ base.{u} gm.{u} (specAOver A) _ _ F] at h
  simpa using h.symm

end Grading

/-! ### The model of a composable pair, as a point of the scheme of composable pairs -/

section CocycleModel

variable {A : Type u} [CommRing A]
  [grp : GrpObj (gm.{u} : Over base.{u}.left)]
  [act : ModObj (gm.{u} : Over base.{u}.left) (specAOver A : Over base.{u}.left)]

include grp act

/-- The model of a composable pair of arrows, as a morphism to the scheme of composable pairs
of the action: the two Laurent variables are the two arrows. -/
noncomputable def doubleArrowPair :
    doubleArrowOver A ⟶ pullback (snd gm.{u} (specAOver A)) γ[gm.{u}, specAOver A] :=
  pullback.lift
    (lift (doubleArrowFirst A)
      (lift (doubleArrowSecond A) (doubleArrowBase A) ≫ γ[gm.{u}, specAOver A]))
    (lift (doubleArrowSecond A) (doubleArrowBase A)) (lift_snd _ _)

omit grp in
/-- The first arrow of the composable pair `doubleArrowPair` is `doubleArrowFirst A`. -/
@[simp] theorem doubleArrowPair_fst :
    (doubleArrowPair (A := A) ≫
        pullback.fst (snd gm.{u} (specAOver A)) γ[gm.{u}, specAOver A]) ≫
      fst gm.{u} (specAOver A) = doubleArrowFirst A := by
  rw [doubleArrowPair, pullback.lift_fst, lift_fst]

omit grp in
/-- The second arrow of the composable pair `doubleArrowPair` is `doubleArrowSecond A`. -/
@[simp] theorem doubleArrowPair_snd_fst :
    (doubleArrowPair (A := A) ≫
        pullback.snd (snd gm.{u} (specAOver A)) γ[gm.{u}, specAOver A]) ≫
      fst gm.{u} (specAOver A) = doubleArrowSecond A := by
  rw [doubleArrowPair, pullback.lift_snd, lift_fst]

omit grp in
/-- The source point of the composable pair `doubleArrowPair` is `doubleArrowBase A`. -/
@[simp] theorem doubleArrowPair_snd_snd :
    (doubleArrowPair (A := A) ≫
        pullback.snd (snd gm.{u} (specAOver A)) γ[gm.{u}, specAOver A]) ≫
      snd gm.{u} (specAOver A) = doubleArrowBase A := by
  rw [doubleArrowPair, pullback.lift_snd, lift_snd]

omit grp in
/-- The character `xⁿ` of the first arrow, read on the model of a composable pair. -/
theorem doubleArrowPair_appTop_first (n : ℤ) :
    ((doubleArrowPair (A := A)).left ≫ (pullback.fst (snd gm.{u} (specAOver A))
        γ[gm.{u}, specAOver A]).left).appTop (laurentCoordinate A n) =
      (Scheme.ΓSpecIso (.of (TensorProduct (ULift.{u} ℤ) (TensorProduct (ULift.{u} ℤ)
        (LaurentPolynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ))) A))).inv
        (doubleArrowFirstHom A (LaurentPolynomial.T n)) :=
  appTop_laurentCoordinate_of_comp_fst A _ _ doubleArrowPair_fst _ rfl n

omit grp in
/-- The character `xⁿ` of the second arrow, read on the model of a composable pair. -/
theorem doubleArrowPair_appTop_second (n : ℤ) :
    ((doubleArrowPair (A := A)).left ≫ (pullback.snd (snd gm.{u} (specAOver A))
        γ[gm.{u}, specAOver A]).left).appTop (laurentCoordinate A n) =
      (Scheme.ΓSpecIso (.of (TensorProduct (ULift.{u} ℤ) (TensorProduct (ULift.{u} ℤ)
        (LaurentPolynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ))) A))).inv
        (doubleArrowSecondHom A (LaurentPolynomial.T n)) :=
  appTop_laurentCoordinate_of_comp_fst A _ _ doubleArrowPair_snd_fst _ rfl n

omit grp in
/-- The product of the two characters, read on the model of a composable pair. -/
theorem doubleArrowPair_appTop_mul (ij : ℤ × ℤ) :
    ((doubleArrowPair (A := A)).left ≫ (pullback.fst (snd gm.{u} (specAOver A))
          γ[gm.{u}, specAOver A]).left).appTop (laurentCoordinate A ij.1) *
        ((doubleArrowPair (A := A)).left ≫ (pullback.snd (snd gm.{u} (specAOver A))
          γ[gm.{u}, specAOver A]).left).appTop (laurentCoordinate A ij.2) =
      (Scheme.ΓSpecIso (.of (TensorProduct (ULift.{u} ℤ) (TensorProduct (ULift.{u} ℤ)
        (LaurentPolynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ))) A))).inv
        ((LaurentPolynomial.T ij.1 ⊗ₜ[ULift.{u} ℤ] LaurentPolynomial.T ij.2)
          ⊗ₜ[ULift.{u} ℤ] (1 : A)) := by
  rw [doubleArrowPair_appTop_first, doubleArrowPair_appTop_second, ← map_mul]
  refine congrArg _ ?_
  change ((LaurentPolynomial.T ij.1 ⊗ₜ[ULift.{u} ℤ]
        (1 : LaurentPolynomial (ULift.{u} ℤ))) ⊗ₜ[ULift.{u} ℤ] (1 : A)) *
      (((1 : LaurentPolynomial (ULift.{u} ℤ)) ⊗ₜ[ULift.{u} ℤ]
        LaurentPolynomial.T ij.2) ⊗ₜ[ULift.{u} ℤ] (1 : A)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul, mul_one]

end CocycleModel
/-! ### The cocycle law, read on Laurent coefficients -/

section Cocycle

/-- Iterating a finite-support coefficient map twice and evaluating a pair of coefficients. -/
private theorem doubleCoefficients_apply {M : Type w} [AddCommGroup M]
    (c : M →+ ℤ →₀ M) (m : M) (i j : ℤ) :
    doubleCoefficients c m (i, j) = c (c m i) j := by
  classical
  simp [doubleCoefficients, Finsupp.sum, Finsupp.single_apply, ite_and]
  split_ifs with h <;> simp_all

/-- Pushing a finitely supported family forward along the diagonal of `ℤ` concentrates it on
the diagonal. -/
private theorem mapDomain_diag_apply {M : Type w} [AddCommGroup M] (f : ℤ →₀ M) (i j : ℤ) :
    Finsupp.mapDomain (fun n : ℤ => (n, n)) f (i, j) = Finsupp.single i (f i) j := by
  classical
  by_cases h : i = j
  · subst j
    rw [Finsupp.mapDomain_apply (show Function.Injective (fun n : ℤ => (n, n)) from
      fun a b h => congrArg Prod.fst h)]
    simp
  · rw [Finsupp.mapDomain_of_notMem_range]
    · simp [h]
    · rintro ⟨n, hn⟩
      exact h ((congrArg Prod.fst hn).symm.trans (congrArg Prod.snd hn))

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℤ → σ) [GradedRing 𝒜]

/-- **The Laurent coefficients are mutually orthogonal projections.** This is the cocycle law of
the descent morphism, read on coefficients over the model of a composable pair of arrows. -/
theorem coefficients_coefficients (F : GradedEquivariantModule.{u} 𝒜)
    (m : Γ(underlyingModule 𝒜 F, ⊤)) (n : ℤ) :
    coefficients 𝒜 F (coefficients 𝒜 F m n) =
      Finsupp.single n (coefficients 𝒜 F m n) := by
  let : GrpObj (gm.{u} : Over base.{u}.left) := AlgebraicGeometry.instGrpObjSpecAsOverSpec
  let : ModObj (gm.{u} : Over base.{u}.left) (specAOver A : Over base.{u}.left) :=
    (gradedGmAction 𝒜).action
  have hcompchar : ∀ nn : ℤ,
      ((doubleArrowPair (A := A)).left ≫
          (Stacks.Groupoids.ActionGroupoid.composition gm.{u} (specAOver A)).left).appTop
          (laurentCoordinate A nn) =
      ((doubleArrowPair (A := A)).left ≫ (pullback.fst (snd gm.{u} (specAOver A))
          γ[gm.{u}, specAOver A]).left).appTop (laurentCoordinate A nn) *
        ((doubleArrowPair (A := A)).left ≫ (pullback.snd (snd gm.{u} (specAOver A))
          γ[gm.{u}, specAOver A]).left).appTop (laurentCoordinate A nn) := by
    intro nn
    rw [Scheme.Hom.comp_appTop, CategoryTheory.ConcreteCategory.comp_apply,
      show laurentCoordinate A nn = (fst gm.{u} (specAOver A)).left.appTop
        ((Scheme.ΓSpecIso (.of (LaurentPolynomial (ULift.{u} ℤ)))).inv
          (LaurentPolynomial.T nn)) from rfl,
      actionComposition_appTop_fst_appTop base.{u} gm.{u} (specAOver A)
        ((Scheme.ΓSpecIso (.of (LaurentPolynomial (ULift.{u} ℤ)))).inv
          (LaurentPolynomial.T nn)) (gm_mul_appTop_laurent nn),
      map_mul, Scheme.Hom.comp_appTop, CategoryTheory.ConcreteCategory.comp_apply,
      Scheme.Hom.comp_appTop, CategoryTheory.ConcreteCategory.comp_apply]
  have hbase : ((doubleArrowPair (A := A)).left ≫
        (Stacks.Groupoids.ActionGroupoid.composition gm.{u} (specAOver A)).left) ≫
      (snd gm.{u} (specAOver A)).left =
      Spec.map (CommRingCat.ofHom (doubleArrowBaseHom A).toRingHom) := by
    rw [Category.assoc,
      show (Stacks.Groupoids.ActionGroupoid.composition gm.{u} (specAOver A)).left ≫
        (snd gm.{u} (specAOver A)).left =
        (pullback.snd (snd gm.{u} (specAOver A)) γ[gm.{u}, specAOver A]).left ≫
          (snd gm.{u} (specAOver A)).left from
      congrArg Over.Hom.left (actionComposition_source base.{u} gm.{u} (specAOver A)),
      ← Category.assoc]
    exact congrArg Over.Hom.left (doubleArrowPair_snd_snd (A := A))
  have hcoc := isDescentCocycle_precomp (doubleArrowPair (A := A)).left
    (pullback.fst (snd gm.{u} (specAOver A)) γ[gm.{u}, specAOver A]).left
    (pullback.snd (snd gm.{u} (specAOver A)) γ[gm.{u}, specAOver A]).left
    (Stacks.Groupoids.ActionGroupoid.composition gm.{u} (specAOver A)).left
    γ[gm.{u}, specAOver A].left (snd gm.{u} (specAOver A)).left _ _ _
    (descentMorphism 𝒜 F)
    ((isDescentCocycle_iff_successiveAction_eq base.{u} gm.{u} (specAOver A)
      (descentMorphism 𝒜 F)).mpr
      (@EquivariantModule.cocycle _ base.{u} gm.{u} (specAOver A) _ _ F))
    _ _ _ rfl rfl rfl
    (by simp only [Category.assoc, ← Over.comp_left]
        rw [actionComposition_target base.{u} gm.{u} (specAOver A)])
    (by simp only [Category.assoc, ← Over.comp_left, pullback.condition])
    (by simp only [Category.assoc, ← Over.comp_left]
        rw [actionComposition_source base.{u} gm.{u} (specAOver A)])
  have key := isDescentCocycle_sectionsCombination _ _ _ _ _ _ _ _ (descentMorphism 𝒜 F) hcoc
    (laurentCoordinate A) (coefficients 𝒜 F)
    (fun z => (sectionsCombination_coefficients 𝒜 F z).symm) m
  rw [hbase,
    show (fun ij : ℤ × ℤ =>
        ((doubleArrowPair (A := A)).left ≫ (pullback.fst (snd gm.{u} (specAOver A))
            γ[gm.{u}, specAOver A]).left).appTop (laurentCoordinate A ij.1) *
          ((doubleArrowPair (A := A)).left ≫ (pullback.snd (snd gm.{u} (specAOver A))
            γ[gm.{u}, specAOver A]).left).appTop (laurentCoordinate A ij.2)) =
      (fun ij : ℤ × ℤ =>
        (Scheme.ΓSpecIso (.of (TensorProduct (ULift.{u} ℤ) (TensorProduct (ULift.{u} ℤ)
          (LaurentPolynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ))) A))).inv
          ((LaurentPolynomial.T ij.1 ⊗ₜ[ULift.{u} ℤ] LaurentPolynomial.T ij.2)
            ⊗ₜ[ULift.{u} ℤ] (1 : A))) from funext doubleArrowPair_appTop_mul,
    show (fun i : ℤ => ((doubleArrowPair (A := A)).left ≫
          (Stacks.Groupoids.ActionGroupoid.composition gm.{u} (specAOver A)).left).appTop
        (laurentCoordinate A i)) =
      ((fun ij : ℤ × ℤ =>
        (Scheme.ΓSpecIso (.of (TensorProduct (ULift.{u} ℤ) (TensorProduct (ULift.{u} ℤ)
          (LaurentPolynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ))) A))).inv
          ((LaurentPolynomial.T ij.1 ⊗ₜ[ULift.{u} ℤ] LaurentPolynomial.T ij.2)
            ⊗ₜ[ULift.{u} ℤ] (1 : A))) ∘ (fun i : ℤ => (i, i))) from
      funext fun i => (hcompchar i).trans (doubleArrowPair_appTop_mul (i, i))] at key
  have hmap := DFunLike.congr_fun (sectionsCombination_comp_mapDomain
    (Spec.map (CommRingCat.ofHom (doubleArrowBaseHom A).toRingHom))
    (underlyingModule 𝒜 F)
    (fun ij : ℤ × ℤ =>
      (Scheme.ΓSpecIso (.of (TensorProduct (ULift.{u} ℤ) (TensorProduct (ULift.{u} ℤ)
        (LaurentPolynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ))) A))).inv
        ((LaurentPolynomial.T ij.1 ⊗ₜ[ULift.{u} ℤ] LaurentPolynomial.T ij.2)
          ⊗ₜ[ULift.{u} ℤ] (1 : A)))
    (fun i : ℤ => (i, i))) (coefficients 𝒜 F m)
  have heq : doubleCoefficients (coefficients 𝒜 F) m =
      Finsupp.mapDomain (fun nn : ℤ => (nn, nn)) (coefficients 𝒜 F m) :=
    (@injective_sectionsCombination_doubleArrow A _ (underlyingModule 𝒜 F)
      (isQuasicoherent_underlyingModule 𝒜 F)) (key.trans hmap.symm)
  ext k
  rw [← doubleCoefficients_apply (coefficients 𝒜 F) m n k, heq, mapDomain_diag_apply]

/-- **Stacks Project, Tag 0EKL.** The canonical grading of the global sections of a
`𝐆ₘ`-equivariant quasi-coherent module on `Spec A`: the canonical homogeneous pieces decompose
the global sections as an internal direct sum. -/
@[stacks 0EKL "the canonical grading of the global sections", instance_reducible]
noncomputable def homogeneousPartDecomposition (F : GradedEquivariantModule.{u} 𝒜) :
    DirectSum.Decomposition (homogeneousPart 𝒜 F) :=
  piece_coefficients 𝒜 F ▸ decompositionOfCoefficients (coefficients 𝒜 F)
    (fun m n => (mem_piece_iff (coefficients 𝒜 F) n (coefficients 𝒜 F m n)).mpr
      (coefficients_coefficients 𝒜 F m n))
    (sum_coefficients 𝒜 F)

end Cocycle

end AlgebraicGeometry.GmEquivariant

end
