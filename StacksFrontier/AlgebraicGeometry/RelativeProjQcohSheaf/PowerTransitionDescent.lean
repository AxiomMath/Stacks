module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.PowerTransition
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionPullback

/-!
# The transition from degree `d` to a multiple of `d`, descended to the strict equivalence classes

Let `S` be a scheme, `𝒜` a graded `𝒪_S`-algebra (Situation 01NN) and `T` a test scheme.
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.scale` carries a quadruple
`(d, f, L, ψ)` of Section 01NS to the quadruple `(a d, f, L^{⊗ a}, ψ^{(a)})` for `a` positive.
This file descends that transition to the sets `F_d(T)` of strict equivalence classes, which is
the map the Stacks source calls `F_d → F_{d'}` for `d ∣ d'`.

## The square that had to commute

A strict equivalence of two quadruples over the same morphism `f` is, by
`...Quadruple.strictlyEquivalent_iff_exists_hom`, an isomorphism `γ : ⨁_n L^{⊗ n} ≅ ⨁_n (L')^{⊗ n}`
of the Laurent algebras with `ψ_n ≫ γ_n = ψ'_n` in every degree `n`. Descending the transition
asks for an isomorphism `γ^{(a)}` of the Laurent algebras of `L^{⊗ a}` and `(L')^{⊗ a}` with
`ψ^{(a)}_i ≫ γ^{(a)}_i = (ψ')^{(a)}_i`, and since `ψ^{(a)}_i` is `ψ_{i a}` followed by the
power-of-a-power comparison of `...powPowIso`, that condition is exactly the commuting square

`(powPowIso L a i).hom ≫ γ^{(a)}_i = γ_{i a} ≫ (powPowIso (L') a i).hom`,  `i : ℤ`.

The comparison is built by a two-sided recursion on `i` whose negative arm is a cancellation
rather than a computation, so proving that square for a *given* `γ^{(a)}` would be a second
induction of the same shape as `...scaledIso_mul`. It is not needed: strict equivalence asks only
for the *existence* of `γ^{(a)}`, so the square can be taken as the **definition** of its
components,

`γ^{(a)}_i = (powPowIso L a i).inv ≫ γ_{i a} ≫ (powPowIso (L') a i).hom`,

and what is then left to prove is that this degreewise family is multiplicative, hence a
homomorphism of sheaves of graded algebras. That is a finite calculation: the two instances of
`...powPowIso_mul`, for `L` and for `L'`, turn the multiplication of the Laurent algebra of
`L^{⊗ a}` in the bidegree `(i, j)` into the multiplication of the Laurent algebra of `L` in the
bidegree `(i a, j a)`, and in that bidegree the multiplicativity is the one `γ` already has.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.scaleCongrApp`: **the degreewise comparison
  `(L^{⊗ a})^{⊗ i} ⟶ ((L')^{⊗ a})^{⊗ i}` induced by a homomorphism `γ` of the Laurent algebras of
  `L` and `L'`**, and `...scaleCongrHom` and `...scaleCongrIso` the homomorphism and the
  isomorphism of sheaves of graded algebras it assembles into.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.scale`: **the transition
  `F_d(T) → F_{a d}(T)`** for `a` positive.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.powPowIso_scaleCongrApp`: **the comparison is
  natural in the invertible module**, which is the square displayed above.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.scaleCongrApp_mulSheaf`: the induced degreewise
  comparison is multiplicative in every integral bidegree.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.StrictlyEquivalent.scale`: **the
  transition of a quadruple respects strict equivalence**, which is what makes `Fd.scale` well
  defined.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.compatibleAt_scale` and
  `...Quadruple.equivalent_scale`: **a quadruple is compatible with its transition at the common
  multiple `a d` of the two degrees, hence equivalent to it.** The comparison is the
  power-of-a-power comparison itself, so this needs no new input: the transition of `ψ` is
  defined to be `ψ` followed by that comparison.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.toF_scale`: **the canonical maps
  `F_d(T) → F(T)` to the union of the display 01NX identify a class with its transition**, so
  the union is a candidate for the colimit of the `F_d(T)` along the transitions.

## Not done here

The transition is not compared with the pullback along a morphism of test schemes, so it is not
yet a map of functors `F_d ⟶ F_{a d}`, and the union of the display 01NX is not *identified* with
the colimit of the `F_d` along the transitions — only shown to receive compatible maps from them.
Tag 01NY remains without a carrier: nothing below asserts the representability of `F`.

## References

* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback

attribute [local instance] isInvertible_piece

/-! ### Conjugating a multiplicativity square by a comparison of the two gradings -/

/-- **A multiplicative morphism conjugated by two comparisons of the gradings is again
multiplicative.** The hypotheses `hA` and `hA'` identify the multiplication `mB` with `mA` and
`mB'` with `mA'` through the comparisons `p` and `q`; `key` is the multiplicativity of `g` for
`mA` and `mA'`; the conclusion is the multiplicativity of the conjugate of `g` for `mB` and
`mB'`.

Stated in a bare monoidal category, with all four multiplications free morphisms, so that the
proof never has to look at `SheafOfModules.GradedAlgebra.mulSheaf`, whose instance argument
defeats `rw` on a goal that names it. -/
theorem conj_mul_square {C : Type*} [Category C] [MonoidalCategory C]
    {A₁ A₂ A₃ B₁ B₂ B₃ A₁' A₂' A₃' B₁' B₂' B₃' : C}
    (p₁ : A₁ ≅ B₁) (p₂ : A₂ ≅ B₂) (p₃ : A₃ ≅ B₃)
    (q₁ : A₁' ≅ B₁') (q₂ : A₂' ≅ B₂') (q₃ : A₃' ≅ B₃')
    (mA : A₁ ⊗ A₂ ⟶ A₃) (mB : B₁ ⊗ B₂ ⟶ B₃) (mA' : A₁' ⊗ A₂' ⟶ A₃') (mB' : B₁' ⊗ B₂' ⟶ B₃')
    (g₁ : A₁ ⟶ A₁') (g₂ : A₂ ⟶ A₂') (g₃ : A₃ ⟶ A₃')
    (hA : mA ≫ p₃.hom = (p₁.hom ⊗ₘ p₂.hom) ≫ mB)
    (hA' : mA' ≫ q₃.hom = (q₁.hom ⊗ₘ q₂.hom) ≫ mB')
    (key : mA ≫ g₃ = (g₁ ⊗ₘ g₂) ≫ mA') :
    mB ≫ p₃.inv ≫ g₃ ≫ q₃.hom =
      ((p₁.inv ≫ g₁ ≫ q₁.hom) ⊗ₘ (p₂.inv ≫ g₂ ≫ q₂.hom)) ≫ mB' := by
  have hpp : (p₁.inv ⊗ₘ p₂.inv) ≫ (p₁.hom ⊗ₘ p₂.hom) = CategoryStruct.id (B₁ ⊗ B₂) :=
    (MonoidalCategory.tensorIso p₁ p₂).inv_hom_id
  have h1 : mB ≫ p₃.inv = (p₁.inv ⊗ₘ p₂.inv) ≫ mA := by
    rw [← Category.id_comp (mB ≫ p₃.inv), ← hpp, Category.assoc,
      ← Category.assoc (p₁.hom ⊗ₘ p₂.hom), ← hA, Category.assoc, p₃.hom_inv_id, Category.comp_id]
  have e1 : mB ≫ p₃.inv ≫ g₃ ≫ q₃.hom = (p₁.inv ⊗ₘ p₂.inv) ≫ mA ≫ g₃ ≫ q₃.hom := by
    rw [← Category.assoc, h1, Category.assoc]
  have e2 : mA ≫ g₃ ≫ q₃.hom = (g₁ ⊗ₘ g₂) ≫ (q₁.hom ⊗ₘ q₂.hom) ≫ mB' := by
    rw [← Category.assoc, key, Category.assoc, hA']
  rw [e1, e2, ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.assoc]

/-! ### The comparison induced on the Laurent algebras of the `a`-th powers -/

section ScaleCongr

variable {T : Scheme.{u}}
  {L L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']

/-- **The homogeneous components of a homomorphism of Laurent algebras are compatible with
reindexing the degree.** -/
theorem laurentHom_app_reindex (γ : laurent L ⟶ laurent L') {n m : ℤ} (h : n = m) :
    (reindexIso L h).hom ≫ γ.app m = γ.app n ≫ (reindexIso L' h).hom := by
  subst h
  show CategoryStruct.id _ ≫ _ = _ ≫ CategoryStruct.id _
  rw [Category.id_comp, Category.comp_id]

/-- **A homomorphism of Laurent algebras is multiplicative for the multiplication with its total
degree prescribed**, in the bidegree `(i a, j a)` with total degree `(i + j) a`. This is the
`map_mul` law of `γ` in that bidegree followed by `laurentHom_app_reindex`, which moves `γ` across
the identification of the degree `i a + j a` with `(i + j) a`. -/
theorem mulPairIso_app (γ : laurent L ⟶ laurent L') (a i j : ℤ) :
    (mulPairIso L (degMul (rfl : i + j = i + j) a)).hom ≫ γ.app ((i + j) * a) =
      (γ.app (i * a) ⊗ₘ γ.app (j * a)) ≫
        (mulPairIso L' (degMul (rfl : i + j = i + j) a)).hom := by
  have hγ := mulSheaf_comp_app (laurent L) (laurent L') γ (i * a) (j * a)
  rw [mulSheaf_laurent, mulSheaf_laurent] at hγ
  show ((mulIso L (i * a) (j * a)).hom ≫
      (reindexIso L (degMul (rfl : i + j = i + j) a)).hom) ≫ γ.app ((i + j) * a) =
    (γ.app (i * a) ⊗ₘ γ.app (j * a)) ≫ ((mulIso L' (i * a) (j * a)).hom ≫
      (reindexIso L' (degMul (rfl : i + j = i + j) a)).hom)
  rw [Category.assoc, laurentHom_app_reindex γ (degMul (rfl : i + j = i + j) a),
    ← Category.assoc]
  exact Eq.trans
    (congrArg (fun z => z ≫ (reindexIso L' (degMul (rfl : i + j = i + j) a)).hom) hγ)
    (Category.assoc _ _ _)

/-- **The degreewise comparison `(L^{⊗ a})^{⊗ i} ⟶ ((L')^{⊗ a})^{⊗ i}` induced by a homomorphism
`γ` of the Laurent algebras of `L` and `L'`**: the power-of-a-power comparison of
`...powPowIso` read backwards, the degree-`i a` component of `γ`, and the power-of-a-power
comparison on the `L'` side.

Taking the comparison this way rather than as the family induced by the degree-`a` component of
`γ` is what makes its naturality in the invertible module (`powPowIso_scaleCongrApp`) hold by
definition instead of by a second two-sided induction on `i`. -/
def scaleCongrApp (γ : laurent L ⟶ laurent L') (a i : ℤ) :
    (laurent (powModule L a)).piece i ⟶ (laurent (powModule L' a)).piece i :=
  (powPowIso L a i).inv ≫ γ.app (i * a) ≫ (powPowIso L' a i).hom

/-- **The power-of-a-power comparison is natural in the invertible module.** This is the square
whose commuting is what descending the transition of a quadruple to the strict equivalence
classes needs; the induced comparison is *defined* so that it holds. -/
theorem powPowIso_scaleCongrApp (γ : laurent L ⟶ laurent L') (a i : ℤ) :
    (powPowIso L a i).hom ≫ scaleCongrApp γ a i =
      γ.app (i * a) ≫ (powPowIso L' a i).hom := by
  rw [scaleCongrApp]
  exact (powPowIso L a i).hom_inv_id_assoc _

/-- **The induced degreewise comparison is multiplicative in every integral bidegree**, which is
the `map_mul` law of a homomorphism of sheaves of graded algebras.

The two instances of `...powPowIso_mul`, for `L` and for `L'`, identify the multiplication of the
Laurent algebra of the `a`-th power in the bidegree `(i, j)` with the multiplication of the
Laurent algebra of the module itself in the bidegree `(i a, j a)`, and `mulPairIso_app` is the
multiplicativity of `γ` in that bidegree; `conj_mul_square` is the composition algebra that puts
the three together. -/
theorem scaleCongrApp_mulSheaf (γ : laurent L ⟶ laurent L') (a i j : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf (laurent (powModule L a)) i j ≫
        scaleCongrApp γ a (i + j) =
      (scaleCongrApp γ a i ⊗ₘ scaleCongrApp γ a j) ≫
        SheafOfModules.GradedAlgebra.mulSheaf (laurent (powModule L' a)) i j :=
  conj_mul_square (powPowIso L a i) (powPowIso L a j) (powPowIso L a (i + j))
    (powPowIso L' a i) (powPowIso L' a j) (powPowIso L' a (i + j)) _ _ _ _
    (γ.app (i * a)) (γ.app (j * a)) (γ.app ((i + j) * a))
    (powPowIso_mul L a i j) (powPowIso_mul L' a i j) (mulPairIso_app γ a i j)

/-- **The induced comparison, as a homomorphism of the Laurent algebras of the `a`-th powers.** -/
def scaleCongrHom (γ : laurent L ⟶ laurent L') (a : ℤ) :
    laurent (powModule L a) ⟶ laurent (powModule L' a) :=
  homOfMulSheaf _ _ (scaleCongrApp γ a) (scaleCongrApp_mulSheaf γ a)

/-- The degree-`i` component of `scaleCongrHom γ a` is `scaleCongrApp γ a i`. -/
@[simp] theorem scaleCongrHom_app (γ : laurent L ⟶ laurent L') (a i : ℤ) :
    (scaleCongrHom γ a).app i = scaleCongrApp γ a i := rfl

/-- **An isomorphism of the Laurent algebras of `L` and `L'` induces an isomorphism of the Laurent
algebras of their `a`-th powers.** The two directions are the conjugates of the two directions of
the given isomorphism, and they are mutually inverse degreewise because the conjugating
power-of-a-power comparisons cancel. -/
def scaleCongrIso (γ : laurent L ≅ laurent L') (a : ℤ) :
    laurent (powModule L a) ≅ laurent (powModule L' a) where
  hom := scaleCongrHom γ.hom a
  inv := scaleCongrHom γ.inv a
  hom_inv_id := SheafOfModules.GradedAlgebra.Hom.ext fun i => by
    have h : γ.hom.app (i * a) ≫ γ.inv.app (i * a) =
        CategoryStruct.id ((laurent L).piece (i * a)) :=
      congrArg (fun φ : laurent L ⟶ laurent L => φ.app (i * a)) γ.hom_inv_id
    change scaleCongrApp γ.hom a i ≫ scaleCongrApp γ.inv a i =
      CategoryStruct.id ((laurent (powModule L a)).piece i)
    simp only [scaleCongrApp, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (γ.hom.app (i * a)), h, Category.id_comp, Iso.inv_hom_id]
  inv_hom_id := SheafOfModules.GradedAlgebra.Hom.ext fun i => by
    have h : γ.inv.app (i * a) ≫ γ.hom.app (i * a) =
        CategoryStruct.id ((laurent L').piece (i * a)) :=
      congrArg (fun φ : laurent L' ⟶ laurent L' => φ.app (i * a)) γ.inv_hom_id
    change scaleCongrApp γ.inv a i ≫ scaleCongrApp γ.hom a i =
      CategoryStruct.id ((laurent (powModule L' a)).piece i)
    simp only [scaleCongrApp, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (γ.inv.app (i * a)), h, Category.id_comp, Iso.inv_hom_id]

/-- The degree-`i` component of the forward map of `scaleCongrIso γ a` is
`scaleCongrApp γ.hom a i`. -/
@[simp] theorem scaleCongrIso_app (γ : laurent L ≅ laurent L') (a i : ℤ) :
    (scaleCongrIso γ a).hom.app i = scaleCongrApp γ.hom a i := rfl

end ScaleCongr

/-! ### The transition of the map `ψ` across the induced comparison -/

section Scale

variable {T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {L L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']

namespace Twisting

/-- **The induced comparison carries the transition of `ψ` to the transition of `ψ'`.** The
degree-`i` component of the transition ends in the power-of-a-power comparison, which cancels
against the copy inside `scaleCongrApp`; what is left is the hypothesis in the degree `i a`. -/
theorem scaleApp_comp_scaleCongrApp (ψ : Twisting f A d L) (ψ' : Twisting f A d L')
    (γ : laurent L ⟶ laurent L') (hγ : ∀ n : ℤ, ψ.app n ≫ γ.app n = ψ'.app n) (a i : ℤ) :
    ψ.scaleApp a i ≫ scaleCongrApp γ a i = ψ'.scaleApp a i := by
  simp only [scaleApp, Category.assoc]
  rw [powPowIso_scaleCongrApp, ← Category.assoc (ψ.app (i * a)), hγ (i * a)]

end Twisting

namespace Quadruple

/-- **The transition of a quadruple from the degree `d` to the degree `a d` respects strict
equivalence.** A strict equivalence is an isomorphism `γ` of the Laurent algebras carrying `ψ` to
`ψ'`; `scaleCongrIso` carries that witness to one for the two transitions, and
`Twisting.scaleApp_comp_scaleCongrApp` is the compatibility with `ψ`. -/
theorem StrictlyEquivalent.scale {P Q : Quadruple f A d} (h : StrictlyEquivalent P Q) {a : ℤ}
    (ha : 0 < a) : StrictlyEquivalent (P.scale ha) (Q.scale ha) := by
  obtain ⟨γ, hψ⟩ := (strictlyEquivalent_iff_exists_hom P Q).mp h
  refine (strictlyEquivalent_iff_exists_hom _ _).mpr ⟨scaleCongrIso γ a, fun i => ?_⟩
  exact Twisting.scaleApp_comp_scaleCongrApp P.twisting Q.twisting γ.hom
    (fun n => hψ n) a i

/-- On a common multiple `(p, q)` of the pair `(a, 1)` the first degree is `a` times the
second. -/
private theorem eq_mul_of_isScaledPair_one {a p q : ℤ} (h : IsScaledPair a 1 p q) :
    p = q * a := by
  obtain ⟨n, hp, hq⟩ := h
  subst hp
  subst hq
  ring

/-- **A quadruple and its transition to the degree `a d` are compatible at the pair `(a, 1)`**,
that is, at the common multiple `a d` of their degrees, which is the smallest one.

The comparison in a pair of degrees `(q a, q)` is the power-of-a-power comparison `powPairIso`;
its multiplicativity is `powPairIso_mul`, its unit clause is `powPairIso_oneHom`, and its
compatibility with `ψ` holds because the transition of `ψ` is *defined* as `ψ` in the degree
`q a` followed by that comparison. -/
theorem compatibleAt_scale (P : Quadruple f A d) {a : ℤ} (ha : 0 < a) :
    CompatibleAt P (P.scale ha) a 1 := by
  refine ⟨by ring, fun p q h => powPairIso P.L a (eq_mul_of_isScaledPair_one h), ?_, ?_, ?_⟩
  · intro p q p' q' h h'
    have hs : p + p' = (q + q') * a := by
      rw [eq_mul_of_isScaledPair_one h, eq_mul_of_isScaledPair_one h']; ring
    have hpm := powPairIso_mul P.L a (eq_mul_of_isScaledPair_one h)
      (eq_mul_of_isScaledPair_one h') hs (rfl : p + p' = p + p')
    have he : (mulPairIso P.L (rfl : p + p' = p + p')).hom =
        SheafOfModules.GradedAlgebra.mulSheaf (laurent P.L) p p' := by
      rw [mulSheaf_laurent]
      exact Category.comp_id _
    exact hpm.symm.trans (congrArg (fun z => z ≫ (powPairIso P.L a hs).hom) he)
  · exact powPairIso_oneHom P.L a
  · intro p q h
    have hp : p = q * a := eq_mul_of_isScaledPair_one h
    have hr := P.twisting.app_reindex hp
    have key : P.twisting.app p ≫ (powPairIso P.L a hp).hom =
        (pullbackFunctor (ringedSpaceHom f)).map
            (eqToHom (congrArg A.piece (show p * d = q * (a * d) by rw [hp]; ring))) ≫
          P.twisting.scaleApp a q := by
      simp only [Twisting.scaleApp, powPairIso, Iso.trans_hom,
        CategoryTheory.eqToHom_map, eqToHom_trans_assoc]
      rw [← Category.assoc, hr, Category.assoc]
      simp only [CategoryTheory.eqToHom_map]
    exact key

/-- **A quadruple is equivalent to its transition to the degree `a d`**, in the sense of Section
01NS: the two are compatible at the common multiple `a d` of their degrees, hence also at the
more divisible common multiple `d (a d)` that equivalence is stated at
(`CompatibleAt.mul_left`). So the transitions are collapsed by the union of the display 01NX:
the two quadruples already have the same point of `F(T)`. -/
theorem equivalent_scale (P : Quadruple f A d) {a : ℤ} (ha : 0 < a) :
    Equivalent P (P.scale ha) := by
  have h := (P.compatibleAt_scale ha).mul_left d
  rw [mul_comm d a, mul_one] at h
  exact h

end Quadruple

/-- **The transition `F_d(T) → F_{a d}(T)` for `a` positive**, the map the Stacks source writes
`F_d → F_{d'}` for `d ∣ d'`: the class of a quadruple `(d, f, L, ψ)` goes to the class of
`(a d, f, L^{⊗ a}, ψ^{(a)})`. It is well defined because the transition of a quadruple respects
strict equivalence (`Quadruple.StrictlyEquivalent.scale`), and it leaves the morphism `f : T ⟶ S`
that a class is fibred over unchanged. -/
def Fd.scale {S T : Scheme.{u}}
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d a : ℤ}
    (ha : 0 < a) (ξ : Fd A d T) : Fd A (a * d) T :=
  ⟨ξ.1,
    Quotient.map (sa := Quadruple.setoid ξ.1 A d) (sb := Quadruple.setoid ξ.1 A (a * d))
      (fun P => P.scale ha) (fun _ _ h => Quadruple.StrictlyEquivalent.scale h ha) ξ.2⟩

/-- The transition sends the class of a quadruple to the class of its transition. -/
@[simp] theorem Fd.scale_mk {S T : Scheme.{u}}
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d a : ℤ}
    (ha : 0 < a) (f : T ⟶ S) (P : Quadruple f A d) :
    Fd.scale ha (Fd.mk f P) = Fd.mk f (P.scale ha) := rfl

/-- The transition leaves the morphism to `S` recorded by a class unchanged. -/
@[simp] theorem Fd.scale_fst {S T : Scheme.{u}}
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d a : ℤ}
    (ha : 0 < a) (ξ : Fd A d T) : (Fd.scale ha ξ).1 = ξ.1 := rfl

/-- **The transition is collapsed by the union of the display 01NX**: a quadruple and its
transition to the degree `a d` have the same point of `F(T)`, because the two are equivalent
(`Quadruple.equivalent_scale`). -/
theorem F.mk_scale {S T : Scheme.{u}}
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
    (hd : 0 < d) {f : T ⟶ S} (P : Quadruple f A d) {a : ℤ} (ha : 0 < a) :
    F.mk f hd P = F.mk f (mul_pos ha hd) (P.scale ha) :=
  F.mk_eq_mk_of_equivalent hd (mul_pos ha hd) (P.equivalent_scale ha)

/-- **The canonical maps to the union identify a class with its transition**: the triangle
`F_d(T) → F_{a d}(T) → F(T)` commutes with `F_d(T) → F(T)`. This is what makes `F(T)` a
candidate for the colimit of the `F_d(T)` along the transitions. -/
theorem Fd.toF_scale {S T : Scheme.{u}}
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d a : ℤ}
    (hd : 0 < d) (ha : 0 < a) (ξ : Fd A d T) :
    Fd.toF (mul_pos ha hd) (Fd.scale ha ξ) = Fd.toF hd ξ := by
  obtain ⟨f, x⟩ := ξ
  induction x using Quotient.ind with
  | _ P => exact (F.mk_scale hd P ha).symm

end Scale

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
