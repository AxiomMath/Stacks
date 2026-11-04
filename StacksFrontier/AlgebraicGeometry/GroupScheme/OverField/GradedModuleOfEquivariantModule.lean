module

public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GradedAction
public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.EquivariantModule

/-!
# The canonical grading on the global sections of an equivariant module

Let `A` be an integer-graded commutative ring, let `X = Spec A` and let the multiplicative
group `𝐆ₘ` act on `X` through the grading.  For a `𝐆ₘ`-equivariant quasi-coherent `𝒪_X`-module
`F`, the global sections `M = Γ(X, F)` carry a canonical family of homogeneous pieces: the
degree-`n` piece is the set of sections on which the descent morphism of the equivariant
structure acts by the character `x ↦ xⁿ` of `𝐆ₘ`.  These pieces are compatible with the
grading of `A`, so that a homogeneous function of degree `i` carries the degree-`n` piece into
the degree-`i + n` piece.

## Main definitions

* `AlgebraicGeometry.GmEquivariant.laurentCoordinate` is the global function `xⁿ` on the scheme
  of arrows `𝐆ₘ × X`, pulled back from `𝐆ₘ`.
* `AlgebraicGeometry.GmEquivariant.pullbackSection` is the canonical image of a global section
  of a module in the global sections of a pullback of that module.
* `AlgebraicGeometry.GmEquivariant.characterPart` is, for a global function `r` on the scheme
  of arrows, the eigenspace of `r` for the descent morphism of an equivariant module.
* `AlgebraicGeometry.GmEquivariant.homogeneousPart` is the canonical degree-`n` piece of the
  global sections of a `𝐆ₘ`-equivariant module, namely the eigenspace of the character `xⁿ`.
* `AlgebraicGeometry.GmEquivariant.piece` is the degree-`n` piece cut out by a coefficient map
  on an abstract module.

## Main results

* `AlgebraicGeometry.GmEquivariant.mem_homogeneousPart_iff` characterises the canonical pieces.
* `AlgebraicGeometry.GmEquivariant.action_appTop_eq_laurentCoordinate_mul`: the action morphism
  multiplies a homogeneous function of degree `i` by the character `xⁱ`.
* `AlgebraicGeometry.GmEquivariant.gradedSMul_homogeneousPart`: the canonical pieces satisfy
  the graded scalar-multiplication law over the graded ring `A`.
* `AlgebraicGeometry.GmEquivariant.decompositionOfCoefficients`: mutually orthogonal
  finite-support projections on a module give an internal direct sum, and
  `AlgebraicGeometry.GmEquivariant.gradedSMul_piece` the corresponding graded
  scalar-multiplication law.
* `AlgebraicGeometry.GmEquivariant.specMap_appTop_inv` and
  `AlgebraicGeometry.GmEquivariant.comp_specMap_appTop_inv` read a global function of a ring
  through `Spec` of a ring map, and through a morphism factoring through such a `Spec.map`.

## Implementation notes

The degree-`n` piece is *constructed*, not asserted to exist: it is the additive subgroup of
`Γ(X, F)` on which the descent morphism `α` of the equivariant structure multiplies the
canonical pullback section by the Laurent monomial `xⁿ`.  Equivalently it is the subspace on
which `𝐆ₘ` acts through the character `x ↦ xⁿ`, read off the coaction, and it is the grading of
the source.

The eigenspace description is written directly in terms of the action morphism and the
projection, as in the definition of an equivariant module, so no identification of the sections
of a pullback with a tensor product enters the statement.  Such an identification does enter
the internal direct sum: the pieces of a module carrying a coefficient map decompose it by
`decompositionOfCoefficients`, whose hypotheses are the counit and coassociativity laws of the
coaction read on coefficients.

## References

* [Stacks Project, Tag 0EKL](https://stacks.math.columbia.edu/tag/0EKL)
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped DirectSum CategoryTheory.MonObj

universe u v w

namespace AlgebraicGeometry.GmEquivariant

attribute [local instance 100] ULift.algebra'

attribute [local implicit_reducible] CategoryTheory.OverClass.asOver

/-! ### The canonical pieces cut out by a coefficient map -/

section Coefficients

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubmonoidClass σ A]
  {M : Type w} [AddCommGroup M] [Module A M]

/-- The degree-`n` piece cut out by a coefficient map `c`: the sections whose only nonzero
coefficient is the `n`-th one, which is the section itself. -/
def piece (c : M →+ (ℤ →₀ M)) (n : ℤ) : AddSubgroup M where
  carrier := {m | c m = Finsupp.single n m}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_add, ha, hb, Finsupp.single_add]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_neg, ha, Finsupp.single_neg]

/-- A section `m` lies in the degree-`n` piece exactly when its coefficients are
`Finsupp.single n m`. -/
theorem mem_piece_iff (c : M →+ (ℤ →₀ M)) (n : ℤ) (m : M) :
    m ∈ piece c n ↔ c m = Finsupp.single n m := Iff.rfl

/-- Mutually orthogonal finite-support projections give an internal direct sum. -/
@[instance_reducible]
noncomputable def decompositionOfCoefficients (c : M →+ ℤ →₀ M)
    (hc : ∀ m n, c m n ∈ piece c n)
    (hs : ∀ m, (c m).sum (fun _ b => b) = m) : DirectSum.Decomposition (piece c) := by
  classical
  let d : M →+ ⨁ n, piece c n :=
    { toFun := fun m => ⟨fun n => ⟨c m n, hc m n⟩,
        Trunc.mk ⟨(c m).support.val, fun n => by
          by_cases hn : n ∈ (c m).support
          · exact Or.inl hn
          · exact Or.inr (Subtype.ext (Finsupp.notMem_support_iff.mp hn))⟩⟩
      map_zero' := by
        ext n
        simp
      map_add' := by
        intro a b
        ext n
        simp }
  have hd (m : M) (n : ℤ) : (d m n : M) = c m n := rfl
  apply DirectSum.Decomposition.ofAddHom (piece c) d
  · ext m
    change DirectSum.coeAddMonoidHom (piece c) (d m) = m
    rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum]
    have hsupport : (d m).support = (c m).support := by
      ext n
      simp only [DFinsupp.mem_support_toFun, Finsupp.mem_support_iff]
      exact not_congr Subtype.ext_iff
    simpa only [DFinsupp.sum, hsupport, hd, Finsupp.sum] using hs m
  · refine DirectSum.addHom_ext fun n m => ?_
    change d (DirectSum.coeAddMonoidHom (piece c) (DirectSum.of (fun n => piece c n) n m)) = _
    rw [DirectSum.coeAddMonoidHom_of]
    ext k
    change c (m : M) k = _
    rw [show c (m : M) = Finsupp.single n (m : M) from m.property]
    by_cases h : n = k <;> simp [DirectSum.coe_of_apply, h]

/-- A coefficient map which is semilinear over the coaction of a graded ring cuts out pieces
satisfying the graded scalar-multiplication law. -/
theorem gradedSMul_piece (𝒜 : ℤ → σ) [GradedRing 𝒜] (c : M →+ (ℤ →₀ M))
    (hsmul : ∀ (i : ℤ) (a : A), a ∈ 𝒜 i → ∀ (m : M) (k : ℤ), c (a • m) k = a • c m (k - i)) :
    SetLike.GradedSMul 𝒜 (piece c) := by
  constructor
  intro i n a m ha hm
  rw [mem_piece_iff] at hm ⊢
  ext k
  rw [hsmul i a ha m k, hm]
  by_cases h : k = i + n
  · subst k
    simp
  · simp [h, show k - i ≠ n by omega]

end Coefficients

/-! ### Sections of a pullback -/

/-- The canonical image of a global section of a module in the global sections of its pullback,
i.e. its image under the unit of the pullback--pushforward adjunction. -/
noncomputable def pullbackSection {W Z : Scheme.{u}} (h : W ⟶ Z) (F : Z.Modules) (s : Γ(F, ⊤)) :
    Γ((Scheme.Modules.pullback h).obj F, ⊤) :=
  Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app F) ⊤ s

/-- The canonical section of a pullback of the zero section is zero. -/
@[simp] theorem pullbackSection_zero {W Z : Scheme.{u}} (h : W ⟶ Z) (F : Z.Modules) :
    pullbackSection h F 0 = 0 := map_zero _

/-- The canonical section of a pullback is additive. -/
theorem pullbackSection_add {W Z : Scheme.{u}} (h : W ⟶ Z) (F : Z.Modules) (s t : Γ(F, ⊤)) :
    pullbackSection h F (s + t) = pullbackSection h F s + pullbackSection h F t := map_add _ _ _

/-- The canonical section of a pullback commutes with negation. -/
theorem pullbackSection_neg {W Z : Scheme.{u}} (h : W ⟶ Z) (F : Z.Modules) (s : Γ(F, ⊤)) :
    pullbackSection h F (-s) = -pullbackSection h F s := map_neg _ _

/-- The canonical section of a pullback is compatible with scalar multiplication. -/
theorem pullbackSection_smul {W Z : Scheme.{u}} (h : W ⟶ Z) (F : Z.Modules) (r : Γ(Z, ⊤))
    (s : Γ(F, ⊤)) :
    pullbackSection h F (r • s) = h.appTop r • pullbackSection h F s :=
  ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app F).app_smul r s

/-! ### The pieces cut out by a character of the acting group -/

section Character

variable {S : Scheme.{u}} (Y : Over S) (G X : Over Y.left) [GrpObj G] [ModObj G X]

/-- The sections of an equivariant module on which the descent morphism multiplies the
canonical pullback section by a prescribed global function `r` on the scheme of arrows. For
`r` a character of the acting group this is the eigenspace of that character. -/
noncomputable def characterPart (F : EquivariantModule Y G X) (r : Γ((G ⊗ X).left, ⊤)) :
    AddSubgroup Γ(F.module, ⊤) where
  carrier := {m | F.alpha.app ⊤ (pullbackSection γ[G, X].left F.module m) =
    r • pullbackSection (snd G X).left F.module m}
  zero_mem' := by simp only [Set.mem_ofPred_eq, pullbackSection_zero, map_zero, smul_zero]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [pullbackSection_add, map_add, ha, hb, pullbackSection_add, smul_add]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [pullbackSection_neg, map_neg, ha, pullbackSection_neg, smul_neg]

/-- A section lies in `characterPart Y G X F r` exactly when the descent morphism sends its
pullback along the action to `r` times its pullback along the projection. -/
theorem mem_characterPart_iff (F : EquivariantModule Y G X) (r : Γ((G ⊗ X).left, ⊤))
    (m : Γ(F.module, ⊤)) :
    m ∈ characterPart Y G X F r ↔
      F.alpha.app ⊤ (pullbackSection γ[G, X].left F.module m) =
        r • pullbackSection (snd G X).left F.module m := Iff.rfl

end Character

/-! ### The canonical grading on the sections of a `𝐆ₘ`-equivariant module -/

section Gm

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubmonoidClass σ A]

/-- `Spec ℤ`, viewed as a scheme over itself. -/
noncomputable abbrev base : Over (Spec (.of (ULift.{u} ℤ))) := Over.mk (𝟙 _)

/-- The multiplicative group scheme, as a scheme over `Spec ℤ`. -/
@[sga "3 I 4.3.2"]
noncomputable abbrev gm : Over (Spec (.of (ULift.{u} ℤ))) :=
  multiplicativeGroupULift.{u}.asOver (Spec (.of (ULift.{u} ℤ)))

/-- `Spec A`, as a scheme over `Spec ℤ`. -/
noncomputable abbrev specAOver (A : Type u) [CommRing A] : Over (Spec (.of (ULift.{u} ℤ))) :=
  (Spec (.of A)).asOver (Spec (.of (ULift.{u} ℤ)))

/-- The global function `xⁿ` on the scheme of arrows `𝐆ₘ × Spec A`: the pullback along the
first projection of the Laurent monomial `xⁿ` on `𝐆ₘ`. -/
noncomputable def laurentCoordinate (A : Type u) [CommRing A] (n : ℤ) :
    Γ((gm.{u} ⊗ specAOver A).left, ⊤) :=
  (fst gm.{u} (specAOver A)).left.appTop
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial (ULift.{u} ℤ)))).inv (LaurentPolynomial.T n))

variable (𝒜 : ℤ → σ) [GradedRing 𝒜]

/-- `𝐆ₘ`-equivariant quasi-coherent modules on `Spec A`, for the action attached to an integer
grading of `A`. -/
noncomputable abbrev GradedEquivariantModule : Type _ :=
  letI : GrpObj (gm.{u} : Over base.{u}.left) := AlgebraicGeometry.instGrpObjSpecAsOverSpec
  letI : ModObj (gm.{u} : Over base.{u}.left) (specAOver A : Over base.{u}.left) :=
    (gradedGmAction 𝒜).action
  EquivariantModule base.{u} gm.{u} (specAOver A)

/-- The underlying quasi-coherent module on `Spec A` of a `𝐆ₘ`-equivariant module. -/
noncomputable abbrev underlyingModule (F : GradedEquivariantModule.{u} 𝒜) :=
  @EquivariantModule.module _ base.{u} gm.{u} (specAOver A)
    AlgebraicGeometry.instGrpObjSpecAsOverSpec (gradedGmAction 𝒜).action F

/-- The descent morphism of a `𝐆ₘ`-equivariant module: it compares the pullback of the module
along the action with its pullback along the projection. -/
noncomputable abbrev descentMorphism (F : GradedEquivariantModule.{u} 𝒜) :=
  @EquivariantModule.alpha _ base.{u} gm.{u} (specAOver A)
    AlgebraicGeometry.instGrpObjSpecAsOverSpec (gradedGmAction 𝒜).action F

/-- The canonical degree-`n` piece of the global sections of a `𝐆ₘ`-equivariant quasi-coherent
module on `Spec A`: the sections on which the descent morphism of the equivariant structure
multiplies the canonical pullback section by the character `x ↦ xⁿ` of `𝐆ₘ`. -/
@[stacks 0EKL "the canonical homogeneous pieces of the global sections"]
noncomputable def homogeneousPart (F : GradedEquivariantModule.{u} 𝒜) (n : ℤ) :
    AddSubgroup ((moduleSpecΓFunctor (R := .of A)).obj (underlyingModule 𝒜 F)) :=
  @characterPart _ base.{u} gm.{u} (specAOver A) AlgebraicGeometry.instGrpObjSpecAsOverSpec
    (gradedGmAction 𝒜).action F (laurentCoordinate A n)

/-- A section lies in the degree-`n` piece exactly when the descent morphism sends its pullback
along the action to `laurentCoordinate A n` times its pullback along the projection. -/
theorem mem_homogeneousPart_iff (F : GradedEquivariantModule.{u} 𝒜) (n : ℤ)
    (m : (moduleSpecΓFunctor (R := .of A)).obj (underlyingModule 𝒜 F)) :
    m ∈ homogeneousPart 𝒜 F n ↔
      (descentMorphism 𝒜 F).app ⊤
          (pullbackSection (gradedGmAction 𝒜).action.smul.left (underlyingModule 𝒜 F) m) =
        laurentCoordinate A n •
          pullbackSection (snd gm.{u} (specAOver A)).left (underlyingModule 𝒜 F) m :=
  Iff.rfl

/-! ### Compatibility of the action with the grading of `A` -/

/-- Global sections of `Spec` and the identification of a ring with them are compatible. -/
theorem specMap_appTop_inv {R' S' : CommRingCat.{u}} (φ : R' ⟶ S') (x : R') :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R').inv x) = (Scheme.ΓSpecIso S').inv (φ x) :=
  (congrArg (fun k : R' ⟶ Γ(Spec S', ⊤) => ConcreteCategory.hom k x)
    (Scheme.ΓSpecIso_inv_naturality φ)).symm

/-- Reading a global function through a morphism that factors through `Spec` of a ring map. -/
theorem comp_specMap_appTop_inv {W : Scheme.{u}} {R' S' : CommRingCat.{u}}
    (g : W ⟶ Spec S') (φ : R' ⟶ S') (x : R') :
    (g ≫ Spec.map φ).appTop ((Scheme.ΓSpecIso R').inv x) =
      g.appTop ((Scheme.ΓSpecIso S').inv (φ x)) := by
  rw [Scheme.Hom.comp_appTop, CategoryTheory.ConcreteCategory.comp_apply, specMap_appTop_inv]

/-- The Laurent monomial `xⁿ`, read in the coordinate ring of the scheme of arrows. -/
private theorem laurentCoordinate_eq (n : ℤ) :
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
  show (fst gm.{u} (specAOver A)).left.appTop _ = _
  rw [hf]
  exact comp_specMap_appTop_inv _ _ _

/-- The projection, read on global sections, is the inclusion of the second tensor factor. -/
private theorem projection_appTop_eq (a : A) :
    (snd gm.{u} (specAOver A)).left.appTop ((Scheme.ΓSpecIso (.of A)).inv a) =
      (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).hom.appTop
        ((Scheme.ΓSpecIso (.of (TensorProduct (ULift.{u} ℤ)
            (LaurentPolynomial (ULift.{u} ℤ)) A))).inv
          ((1 : LaurentPolynomial (ULift.{u} ℤ)) ⊗ₜ[ULift.{u} ℤ] a)) := by
  have hs : (snd gm.{u} (specAOver A)).left =
      (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).hom ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := ULift.{u} ℤ)
            (A := LaurentPolynomial (ULift.{u} ℤ)) (B := A)).toRingHom) :=
    (pullbackSpecIso_hom_snd (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).symm
  rw [hs]
  exact comp_specMap_appTop_inv _ _ _

/-- The action morphism, read on global sections, sends a homogeneous element of degree `i`
to `xⁱ ⊗ a`. -/
private theorem action_appTop_homogeneous (i : ℤ) (a : A) (ha : a ∈ 𝒜 i) :
    (gradedGmAction 𝒜).action.smul.left.appTop ((Scheme.ΓSpecIso (.of A)).inv a) =
      (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).hom.appTop
        ((Scheme.ΓSpecIso (.of (TensorProduct (ULift.{u} ℤ)
            (LaurentPolynomial (ULift.{u} ℤ)) A))).inv
          (LaurentPolynomial.T i ⊗ₜ[ULift.{u} ℤ] a)) := by
  rw [(gradedGmAction 𝒜).action_eq_spec_map]
  refine (comp_specMap_appTop_inv _ _ _).trans ?_
  congr 2
  show (Algebra.TensorProduct.comm (ULift.{u} ℤ) A (LaurentPolynomial (ULift.{u} ℤ)))
    ((gradedActionTensorMap A) ((gradedGmAction 𝒜).μ a)) = _
  rw [(gradedGmAction 𝒜).μ_homogeneous i a ha, gradedActionTensorMap_tmul_T]
  rfl

/-- **The action is compatible with the grading of `A`.** On a homogeneous function of degree
`i`, the action morphism is multiplication by the character `x ↦ xⁱ` of `𝐆ₘ` composed with the
projection. -/
theorem action_appTop_eq_laurentCoordinate_mul (i : ℤ) (a : A) (ha : a ∈ 𝒜 i) :
    (gradedGmAction 𝒜).action.smul.left.appTop ((Scheme.ΓSpecIso (.of A)).inv a) =
      laurentCoordinate A i *
        (snd gm.{u} (specAOver A)).left.appTop ((Scheme.ΓSpecIso (.of A)).inv a) := by
  have h : (LaurentPolynomial.T i ⊗ₜ[ULift.{u} ℤ] (1 : A)) *
      ((1 : LaurentPolynomial (ULift.{u} ℤ)) ⊗ₜ[ULift.{u} ℤ] a) =
      LaurentPolynomial.T i ⊗ₜ[ULift.{u} ℤ] a := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [action_appTop_homogeneous 𝒜 i a ha, laurentCoordinate_eq, projection_appTop_eq, ← h,
    map_mul, map_mul]
  rfl

/-- Scalar multiplication by a ring element, read on sections of a pullback. -/
private theorem pullbackSection_smul_base {W : Scheme.{u}} (h : W ⟶ Spec (.of A))
    (F : (Spec (.of A)).Modules) (r : A)
    (z : (moduleSpecΓFunctor (R := .of A)).obj F) :
    pullbackSection h F (r • z) =
      h.appTop ((Scheme.ΓSpecIso (.of A)).inv r) • pullbackSection h F z :=
  pullbackSection_smul h F _ z

/-- The characters of `𝐆ₘ` multiply: `x^(i+n) = xⁱ · xⁿ`. -/
theorem laurentCoordinate_add (i n : ℤ) :
    laurentCoordinate A (i + n) = laurentCoordinate A i * laurentCoordinate A n := by
  simp only [laurentCoordinate, LaurentPolynomial.T_add, map_mul]

/-- The canonical homogeneous pieces of the global sections of a `𝐆ₘ`-equivariant quasi-coherent
module on `Spec A` are compatible with the grading of `A`: a homogeneous function of degree `i`
carries the degree-`n` piece into the degree-`i + n` piece. -/
@[stacks 0EKL "compatibility of the canonical homogeneous pieces with the grading of A"]
theorem gradedSMul_homogeneousPart (F : GradedEquivariantModule.{u} 𝒜) :
    SetLike.GradedSMul 𝒜 (homogeneousPart 𝒜 F) := by
  constructor
  intro i n a m ha hm
  rw [mem_homogeneousPart_iff] at hm ⊢
  rw [show (i +ᵥ n) = i + n from rfl, pullbackSection_smul_base,
    Scheme.Modules.Hom.app_smul, hm,
    action_appTop_eq_laurentCoordinate_mul 𝒜 i (a : A) ha, pullbackSection_smul_base,
    laurentCoordinate_add, ← mul_smul, ← mul_smul]
  congr 1
  ring

end Gm

end AlgebraicGeometry.GmEquivariant

end
