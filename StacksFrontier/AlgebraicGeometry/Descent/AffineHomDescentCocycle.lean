module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDatum
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.AlgebraCocycle
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineFppfFaithfullyFlat

/-!
# The cocycle condition of the descent datum of an affine morphism

`AlgebraicGeometry.Space.exists_affineDescentDatum_of_isPullback` reads a Cartesian square of
presheaves on the big fppf site of `S`, with one leg representable by an affine morphism, as a
descent datum of affine schemes: an object `v` of the site, affine over the chart `c`, and an
isomorphism between the two base changes of `v` to `c ×_a c`. On global sections, by
`AlgebraicGeometry.exists_transition_of_isPullback`, this becomes a transition isomorphism
`τ : Γ(v) ⊗[Γ(a)] Γ(c) ≃ Γ(c) ⊗[Γ(a)] Γ(v)` of the kind that
`ModuleCat.bijective_productMap_descentInvariants_of_unitCoassoc` — effective descent for
algebras — consumes. One hypothesis of that theorem was still owed: the cocycle condition, in the
form of coassociativity of the unit `σ b = τ (b ⊗ 1)`. **This file supplies it, and concludes
that the datum is effective.**

*Why the cocycle condition holds.* Write `w : v ⟶ c` for the structure morphism and `Fst` for the
leg to `X` of the Cartesian square presenting `yoneda.obj v` as the base change of `f`. Then for
every object `d` of the site, every `g : d ⟶ c` and every `t : d ⟶ v` with
`g ≫ q = t ≫ w ≫ q` there is a *unique* `u : d ⟶ v` with `u ≫ w = g` which agrees with `t`
over `X`, i.e. `yoneda.map u ≫ Fst = yoneda.map t ≫ Fst`; this is nothing but the universal
property of that Cartesian square, and is
`AlgebraicGeometry.Space.exists_descentAction` together with
`AlgebraicGeometry.Space.descentAction_unique`. Taking `d = c ×_a v`, `g` the first projection and
`t` the second gives the *action* `s : c ×_a v ⟶ v` of the groupoid `c ×_a c` on `v`, which is the
descent datum: the comparison isomorphism `φ` of
`AlgebraicGeometry.Space.exists_affineDescentDatum_of_isPullback` is recovered from `s` as a lift
into a fibre product, and is an isomorphism because the action is invertible.

The cocycle condition is then `AlgebraicGeometry.Space.descentAction_assoc`: for `l` and `l'` the
two morphisms `c ×_a (c ×_a v) ⟶ c ×_a v` given by `(x₁, x₂, y) ↦ (x₁, x₂ · y)` and
`(x₁, x₂, y) ↦ (x₁, y)`, one has `l ≫ s = l' ≫ s`, i.e. `x₁ · (x₂ · y) = x₁ · y`. Both sides are
morphisms `c ×_a (c ×_a v) ⟶ v` lying over the first projection to `c`, so by uniqueness it is
enough that they agree over `X`, and over `X` the action is the identity — which is the single
property `yoneda.map s ≫ Fst = yoneda.map ρ₂ ≫ Fst` of `s`, applied twice. **No triple fibre
product has to be identified with a triple tensor product on the nose**: only one comparison of
`Γ(c ×_a (c ×_a v))` with `Γ(c) ⊗ (Γ(c) ⊗ Γ(v))` is needed, and it is made by the same three
ingredients as the double one, `AlgebraicGeometry.isPushout_appTop_of_flat`,
`CommRingCat.isPushout_tensorProduct` and `CategoryTheory.IsPushout.isoIsPushout`.

## Main results

* `AlgebraicGeometry.exists_transition_unitCoassoc_of_isPushout`: **the algebraic heart.** Three
  pushout presentations of `Γ` of `v ×_a c`, of `c ×_a v` and of `c ×_a (c ×_a v)`, an isomorphism
  between the first two over `c ×_a c`, and the geometric cocycle identity between the two
  morphisms `c ×_a (c ×_a v) ⟶ c ×_a v`, produce the transition isomorphism `τ` together with
  *both* hypotheses of `ModuleCat.bijective_productMap_descentInvariants_of_unitCoassoc`.
* `AlgebraicGeometry.exists_descentPushout_of_isPullback`: **effective descent on global
  sections for a descent datum, at the level of schemes.** A descent datum of quasi-compact
  quasi-separated schemes along a flat surjection `Q : Sc ⟶ Sa` of affines, presented by its
  action `s` and the cocycle identity, descends: there is a `Γ(Sa)`-algebra `C` with
  `Γ(Sv) = Γ(Sc) ⊗_{Γ(Sa)} C`, as a pushout square of rings. For `Sv` affine this is Stacks 0245
  for one chart, in ring-theoretic form; in general it is the descent of the affine hull, which
  is the first half of Stacks 0247.
* `AlgebraicGeometry.Space.exists_descentAction`, `AlgebraicGeometry.Space.descentAction_unique`
  and `AlgebraicGeometry.Space.descentAction_assoc`: existence, uniqueness and associativity of
  the action of the groupoid of a chart on the object of a representable descent datum.
* `AlgebraicGeometry.Space.exists_descentAction_of_isPullback`: the datum of
  `AlgebraicGeometry.Space.exists_descentDatum_of_isPullback`, together with its action `s`
  and the property of `s` which makes the cocycle condition hold.
* `AlgebraicGeometry.Space.exists_affineDescentAction_of_isPullback`: the same at the affine
  morphisms over an affine chart, where the representing object is itself an affine scheme.
* `AlgebraicGeometry.Space.exists_descentPushout_appTop_of_isPullback`: **the two halves joined.**
  A Cartesian square of presheaves whose base change along an affine chart is representable by a
  quasi-compact quasi-separated morphism produces the descended algebra `C` over `Γ(a)` with
  `Γ(v) = Γ(c) ⊗_{Γ(a)} C`, together with the action `s` and the equation
  `p ≫ s.appTop = p ≫ ρ₂.appTop` saying that the action is a morphism over `Spec C`.

## Implementation notes

The transition isomorphism is *not* produced here as the isomorphism on global sections induced by
`φ`, but from the action: `τ` is `Algebra.TensorProduct.lift` of the coaction
`σ : Γ(v) → Γ(c) ⊗ Γ(v)` and of `a ↦ 1 ⊗ a`, which makes the compatibility of `τ` with the two
structure morphisms immediate from the single triangle `s ≫ w = ρ₁`, and makes
`σ b = τ (b ⊗ 1)` true by construction rather than by a computation. That `τ` is bijective is
then the only thing `φ` is used for.

The conclusion of the two effectivity statements is a pushout square in `CommRingCat` rather than
a Cartesian square of schemes or a representing object of the site. This keeps them free of
`Spec`, of `isoSpec` and of the size bookkeeping of the site: `AlgebraicGeometry.Pullbacks` turns
such a pushout back into a Cartesian square of affine schemes whenever that is what is wanted.

What is still owed for Stacks 0245 itself, i.e. for
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` at
`AlgebraicGeometry.IsAffineHom`, is the passage from the descended algebra `C` back to the site:
`Spec C` has to be made an object of the big fppf site over `S` — its size is bounded by
`AlgebraicGeometry.Scheme.size_Spec_lt_of_subring`, since `C` is a subring of `Γ(v)`, and
`AlgebraicGeometry.BigFppfOver.mk` then makes it an object over `S` — and the resulting morphism
of presheaves from `pullback f h` has to be shown locally bijective, exactly as
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isOpenImmersion` does for open
immersions.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 023G](https://stacks.math.columbia.edu/tag/023G)
* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
* [Stacks Project, Tag 01S6](https://stacks.math.columbia.edu/tag/01S6)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct CommRingCat

namespace AlgebraicGeometry


/-! ### The transition isomorphism together with its cocycle condition -/

/-- **An algebra descent datum presented by its action satisfies the cocycle condition.** Let
`R → A → T` be a tower of rings, let `Q₁` present `T ⊗[R] A`, let `Q₂` present `A ⊗[R] T` and let
`Q₃` present `A ⊗[R] (A ⊗[R] T)`, each as a pushout, and let `χ : Q₁ ≅ Q₂` be an isomorphism
compatible with the structure morphisms as in
`AlgebraicGeometry.exists_transition_of_isPushout`. Write `ς = i₁ ≫ χ.hom` for the coaction
`T → Q₂` that `χ` determines. Let `Λ, Λ' : Q₂ ⟶ Q₃` be the two morphisms determined by
`i₂ ≫ Λ = i₃`, `j₂ ≫ Λ = ς ≫ j₃` and `i₂ ≫ Λ' = i₃`, `j₂ ≫ Λ' = j₂ ≫ j₃`. If `ς ≫ Λ = ς ≫ Λ'`
then there is a transition isomorphism `τ : T ⊗[R] A ≃ₐ[R] A ⊗[R] T` which satisfies both
hypotheses of `ModuleCat.bijective_productMap_descentInvariants_of_unitCoassoc`: it lies over
`A ⊗[R] A`, and its unit `σ b = τ (b ⊗ 1)` is coassociative.

Geometrically `Q₁`, `Q₂`, `Q₃` are the rings of `v ×_a c`, `c ×_a v` and `c ×_a (c ×_a v)`, `ς` is
the action `c ×_a v ⟶ v` of the groupoid `c ×_a c` on `v`, and `Λ`, `Λ'` are the two morphisms
`c ×_a (c ×_a v) ⟶ c ×_a v` sending `(x₁, x₂, y)` to `(x₁, x₂ · y)` and to `(x₁, y)`. The
hypothesis `hcoc` is then associativity of the action, `x₁ · (x₂ · y) = x₁ · y`, which is
`AlgebraicGeometry.Space.descentAction_assoc`.

`τ` is built from the coaction rather than from `χ`, by `Algebra.TensorProduct.lift`; `χ` enters
only through the bijectivity of the result. -/
theorem exists_transition_unitCoassoc_of_isPushout
    {R A T : Type u} [CommRing R] [CommRing A] [CommRing T]
    [Algebra R A] [Algebra A T] [Algebra R T] [IsScalarTower R A T]
    {Q₁ Q₂ Q₃ : CommRingCat.{u}}
    {i₁ : CommRingCat.of T ⟶ Q₁} {j₁ : CommRingCat.of A ⟶ Q₁}
    (po₁ : IsPushout (ofHom (algebraMap R T)) (ofHom (algebraMap R A)) i₁ j₁)
    {i₂ : CommRingCat.of A ⟶ Q₂} {j₂ : CommRingCat.of T ⟶ Q₂}
    (po₂ : IsPushout (ofHom (algebraMap R A)) (ofHom (algebraMap R T)) i₂ j₂)
    {i₃ : CommRingCat.of A ⟶ Q₃} {j₃ : Q₂ ⟶ Q₃}
    (po₃ : IsPushout (ofHom (algebraMap R A)) (ofHom (algebraMap R A) ≫ i₂) i₃ j₃)
    (χ : Q₁ ≅ Q₂)
    (h1 : ofHom (algebraMap A T) ≫ i₁ ≫ χ.hom = i₂)
    (h2 : j₁ ≫ χ.hom = ofHom (algebraMap A T) ≫ j₂)
    {Λ Λ' : Q₂ ⟶ Q₃}
    (hΛ₁ : i₂ ≫ Λ = i₃) (hΛ₂ : j₂ ≫ Λ = (i₁ ≫ χ.hom) ≫ j₃)
    (hΛ₁' : i₂ ≫ Λ' = i₃) (hΛ₂' : j₂ ≫ Λ' = j₂ ≫ j₃)
    (hcoc : (i₁ ≫ χ.hom) ≫ Λ = (i₁ ≫ χ.hom) ≫ Λ') :
    ∃ τ : (T ⊗[R] A) ≃ₐ[R] (A ⊗[R] T),
      (∀ a b : A, τ (algebraMap A T a ⊗ₜ[R] b) = a ⊗ₜ[R] algebraMap A T b) ∧
      (∀ b : T, τ (b ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] b →
        (i₁ ≫ χ.hom).hom b = j₂.hom b) ∧
      ∀ b : T,
        LinearMap.lTensor A (ModuleCat.algebraUnitTransition R A T τ)
            (ModuleCat.algebraUnitTransition R A T τ b)
          = LinearMap.lTensor A (TensorProduct.mk R A T 1)
              (ModuleCat.algebraUnitTransition R A T τ b) := by
  have pt₁ := CommRingCat.isPushout_tensorProduct R T A
  have pt₂ := CommRingCat.isPushout_tensorProduct R A T
  have pt₃ := CommRingCat.isPushout_tensorProduct R A (A ⊗[R] T)
  set κ₁ := po₁.isoIsPushout (CommRingCat.of T) (CommRingCat.of A) pt₁ with hκ₁
  set κ₂ := po₂.isoIsPushout (CommRingCat.of A) (CommRingCat.of T) pt₂ with hκ₂
  have hi₁ : i₁ ≫ κ₁.hom =
      ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := T) (B := A)) :=
    po₁.inl_isoIsPushout_hom _ _ pt₁
  have hj₁ : j₁ ≫ κ₁.hom =
      ofHom (Algebra.TensorProduct.includeRight (R := R) (A := T) (B := A)).toRingHom :=
    po₁.inr_isoIsPushout_hom _ _ pt₁
  have hi₂ : i₂ ≫ κ₂.hom =
      ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := T)) :=
    po₂.inl_isoIsPushout_hom _ _ pt₂
  have hj₂ : j₂ ≫ κ₂.hom =
      ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := T)).toRingHom :=
    po₂.inr_isoIsPushout_hom _ _ pt₂
  -- the coaction, as an `R`-algebra map
  have hunit : ∀ a : A, ((i₁ ≫ χ.hom) ≫ κ₂.hom).hom (algebraMap A T a)
      = a ⊗ₜ[R] (1 : T) := by
    intro a
    have e : ofHom (algebraMap A T) ≫ (i₁ ≫ χ.hom) ≫ κ₂.hom = i₂ ≫ κ₂.hom := by
      rw [← Category.assoc, h1]
    have := congrArg (fun (g : CommRingCat.of A ⟶ CommRingCat.of (A ⊗[R] T)) => g.hom a) e
    simpa [hi₂] using this
  obtain ⟨σ, hσ⟩ : ∃ σ : T →ₐ[R] (A ⊗[R] T),
      ∀ b : T, σ b = ((i₁ ≫ χ.hom) ≫ κ₂.hom).hom b := by
    refine ⟨{ toRingHom := ((i₁ ≫ χ.hom) ≫ κ₂.hom).hom, commutes' := fun r => ?_ }, fun _ => rfl⟩
    show ((i₁ ≫ χ.hom) ≫ κ₂.hom).hom (algebraMap R T r) = _
    rw [IsScalarTower.algebraMap_apply R A T, hunit, Algebra.TensorProduct.algebraMap_apply]
  have hσ1 : σ 1 = 1 := map_one σ
  -- the transition isomorphism
  set ψ : A →ₐ[R] (A ⊗[R] T) :=
    (Algebra.TensorProduct.includeRight).comp (IsScalarTower.toAlgHom R A T) with hψ
  have hψapp : ∀ a : A, ψ a = (1 : A) ⊗ₜ[R] algebraMap A T a := fun _ => rfl
  set τ₀ : (T ⊗[R] A) →ₐ[R] (A ⊗[R] T) :=
    Algebra.TensorProduct.lift σ ψ (fun _ _ => Commute.all _ _) with hτ₀
  have hτ₀tmul : ∀ (b : T) (a : A), τ₀ (b ⊗ₜ[R] a) = σ b * ψ a := fun _ _ => rfl
  have hkey₁ : κ₁.hom ≫ ofHom τ₀.toRingHom = χ.hom ≫ κ₂.hom := by
    refine po₁.hom_ext ?_ ?_
    · rw [← Category.assoc, hi₁, ← Category.assoc]
      ext b
      show τ₀ (b ⊗ₜ[R] (1 : A)) = ((i₁ ≫ χ.hom) ≫ κ₂.hom).hom b
      rw [hτ₀tmul, map_one, mul_one, hσ]
    · rw [← Category.assoc, hj₁, ← Category.assoc, h2, Category.assoc, hj₂]
      ext a
      show τ₀ ((1 : T) ⊗ₜ[R] a) = _
      rw [hτ₀tmul, hσ1, one_mul, hψapp]
      rfl
  have hiso : IsIso (ofHom τ₀.toRingHom) := by
    have : ofHom τ₀.toRingHom = κ₁.inv ≫ χ.hom ≫ κ₂.hom := by
      rw [← hkey₁, Iso.inv_hom_id_assoc]
    rw [this]
    infer_instance
  have hbij : Function.Bijective τ₀ := by
    have := ConcreteCategory.bijective_of_isIso (ofHom τ₀.toRingHom)
    exact this
  refine ⟨AlgEquiv.ofBijective τ₀ hbij, ?_, ?_, ?_⟩
  · intro a b
    show τ₀ (algebraMap A T a ⊗ₜ[R] b) = _
    rw [hτ₀tmul, hσ, hunit, hψapp, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  · -- an invariant element is carried to the same place by the coaction and by `j₂`
    intro b hb
    have hτ₀b : τ₀ (b ⊗ₜ[R] (1 : A)) = σ b := by rw [hτ₀tmul, map_one, mul_one]
    have hσb : σ b = (1 : A) ⊗ₜ[R] b := by rw [← hτ₀b]; exact hb
    refine (ConcreteCategory.bijective_of_isIso κ₂.hom).1 ?_
    show ((i₁ ≫ χ.hom) ≫ κ₂.hom).hom b = (j₂ ≫ κ₂.hom).hom b
    rw [← hσ, hσb, hj₂]
    rfl
  · -- the cocycle condition, in the form of coassociativity of the unit
    set τ := AlgEquiv.ofBijective τ₀ hbij with hτ
    have hu : ∀ b : T, ModuleCat.algebraUnitTransition R A T τ b = σ b := by
      intro b
      rw [ModuleCat.algebraUnitTransition_apply]
      show τ₀ (b ⊗ₜ[R] (1 : A)) = σ b
      rw [hτ₀tmul, map_one, mul_one]
    have hlin : (ModuleCat.algebraUnitTransition R A T τ) = σ.toLinearMap :=
      LinearMap.ext hu
    -- the third pushout presentation
    have po₃' : IsPushout (ofHom (algebraMap R A))
        (ofHom (algebraMap R (A ⊗[R] T))) i₃ (κ₂.inv ≫ j₃) := by
      refine po₃.of_iso (Iso.refl _) (Iso.refl _) κ₂ (Iso.refl _) (by simp) ?_ (by simp) (by simp)
      rw [Iso.refl_hom, Category.id_comp, Category.assoc, hi₂]
      ext r
      show (algebraMap R A r) ⊗ₜ[R] (1 : T) = algebraMap R (A ⊗[R] T) r
      rw [Algebra.TensorProduct.algebraMap_apply]
    set κ₃ := po₃'.isoIsPushout (CommRingCat.of A) (CommRingCat.of (A ⊗[R] T)) pt₃ with hκ₃
    have hi₃ : i₃ ≫ κ₃.hom = ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := A) (B := A ⊗[R] T)) :=
      po₃'.inl_isoIsPushout_hom _ _ pt₃
    have hj₃ : j₃ ≫ κ₃.hom = κ₂.hom ≫ ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := A) (B := A ⊗[R] T)).toRingHom := by
      have := po₃'.inr_isoIsPushout_hom (CommRingCat.of A)
        (CommRingCat.of (A ⊗[R] T)) pt₃
      rw [Category.assoc] at this
      rw [← this, Iso.hom_inv_id_assoc]
    -- `κ₂ ≫ (id ⊗ g)` is determined by the two composites `i₂ ≫ Λ` and `j₂ ≫ Λ`
    have hmap : ∀ (g : T →ₐ[R] (A ⊗[R] T)) (M : Q₂ ⟶ Q₃), i₂ ≫ M = i₃ →
        (∀ b : T, (j₂ ≫ M ≫ κ₃.hom).hom b = (1 : A) ⊗ₜ[R] g b) →
        κ₂.hom ≫ ofHom (Algebra.TensorProduct.map (AlgHom.id R A) g).toRingHom = M ≫ κ₃.hom := by
      intro g M hM₁ hM₂
      refine po₂.hom_ext ?_ ?_
      · rw [← Category.assoc, hi₂, ← Category.assoc, hM₁, hi₃]
        ext a
        show Algebra.TensorProduct.map (AlgHom.id R A) g (a ⊗ₜ[R] (1 : T)) = a ⊗ₜ[R] (1 : A ⊗[R] T)
        rw [Algebra.TensorProduct.map_tmul, map_one]
        rfl
      · rw [← Category.assoc, hj₂, ← Category.assoc]
        ext b
        refine Eq.trans ?_ (hM₂ b).symm
        show Algebra.TensorProduct.map (AlgHom.id R A) g ((1 : A) ⊗ₜ[R] b) = _
        rw [Algebra.TensorProduct.map_tmul]
        rfl
    have hlTensor : ∀ (g : T →ₐ[R] (A ⊗[R] T)) (x : A ⊗[R] T),
        LinearMap.lTensor A g.toLinearMap x = Algebra.TensorProduct.map (AlgHom.id R A) g x := by
      intro g x
      induction x with
      | zero => simp
      | add u v hu' hv' => rw [map_add, map_add, hu', hv']
      | tmul a b => rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.map_tmul]; rfl
    have hleft := hmap σ Λ hΛ₁ fun b => by
      rw [← Category.assoc, hΛ₂, Category.assoc, hj₃]
      show (1 : A) ⊗ₜ[R] ((i₁ ≫ χ.hom) ≫ κ₂.hom).hom b = _
      rw [hσ]
    have hright := hmap Algebra.TensorProduct.includeRight Λ' hΛ₁' fun b => by
      rw [← Category.assoc, hΛ₂', Category.assoc, hj₃, ← Category.assoc, hj₂]
      rfl
    have e1 := congrArg ((i₁ ≫ χ.hom) ≫ ·) hleft
    have e2 := congrArg ((i₁ ≫ χ.hom) ≫ ·) hright
    have e3 : (i₁ ≫ χ.hom) ≫ Λ ≫ κ₃.hom = (i₁ ≫ χ.hom) ≫ Λ' ≫ κ₃.hom := by
      rw [← Category.assoc, hcoc, Category.assoc]
    intro b
    rw [hlin, hlTensor σ, show TensorProduct.mk R A T 1 =
      (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := T)).toLinearMap from rfl,
      hlTensor]
    simp only [AlgHom.toLinearMap_apply]
    rw [hσ]
    show ((i₁ ≫ χ.hom) ≫ κ₂.hom ≫ ofHom (Algebra.TensorProduct.map (AlgHom.id R A) σ).toRingHom).hom
        b = ((i₁ ≫ χ.hom) ≫ κ₂.hom ≫ ofHom (Algebra.TensorProduct.map (AlgHom.id R A)
          Algebra.TensorProduct.includeRight).toRingHom).hom b
    rw [e1, e2, e3]


/-! ### Effective descent for a datum of affine schemes -/

/-- **The global sections of a descent datum along a flat surjection of affine schemes
descend.** Let `Q : Sc ⟶ Sa` be a flat surjection of affine schemes, let `w : Sv ⟶ Sc` with `Sv`
quasi-compact and quasi-separated, and let `P₁` present `Sv ×_{Sa} Sc`, `P₂` present
`Sc ×_{Sa} Sv` and `W` present `Sc ×_{Sa} P₂`. Suppose given the descent datum in the form of
its action `s : P₂ ⟶ Sv` over the first projection, the isomorphism `φ : P₁ ≅ P₂` it induces,
and the two morphisms `l, l' : W ⟶ P₂` of the cocycle condition, which `s` carries to the same
morphism `W ⟶ Sv`. Then the datum descends on global sections: there is a ring `C` under
`Γ(Sa)` and injectively over `Γ(Sv)`, with `Γ(Sv)` the pushout of `Γ(Sc) ← Γ(Sa) → C`.

For `Sv` affine this says `Sv = Sc ×_{Sa} Spec C`, and it is the affine case of Stacks 0245. For
`Sv` merely quasi-compact and quasi-separated it says instead that the *affine hull* of `Sv` is
`Sc ×_{Sa} Spec C`, which is the first half of Stacks 0247; the three pushout squares of global
sections are then no longer Cartesian squares of affine schemes but instances of flat base
change in degree zero, `AlgebraicGeometry.isPushout_appTop_of_flat`, which is Stacks 02KH at
`i = 0`. Flatness of `Q` is what makes them available, and it is used for nothing else here.

The descended ring is the subalgebra of invariants `ModuleCat.descentInvariants` of the
transition isomorphism, and the pushout square is the bijectivity of the canonical map
`Γ(Sc) ⊗_{Γ(Sa)} C → Γ(Sv)`, which is
`ModuleCat.bijective_productMap_descentInvariants_of_unitCoassoc` fed by
`AlgebraicGeometry.exists_transition_unitCoassoc_of_isPushout`. Faithful flatness of
`Γ(Sa) → Γ(Sc)` is `AlgebraicGeometry.faithfullyFlat_appTop_of_flat_of_surjective`. -/
theorem exists_descentPushout_of_isPullback
    {Sa Sc Sv P₁ P₂ W : Scheme.{u}} [IsAffine Sa] [IsAffine Sc]
    [CompactSpace Sv] [QuasiSeparatedSpace Sv]
    {Q : Sc ⟶ Sa} {w : Sv ⟶ Sc} (hQs : Surjective Q) (hQf : Flat Q)
    {π₁ : P₁ ⟶ Sv} {π₂ : P₁ ⟶ Sc} (sq₁ : IsPullback π₁ π₂ (w ≫ Q) Q)
    {ρ₁ : P₂ ⟶ Sc} {ρ₂ : P₂ ⟶ Sv} (sq₂ : IsPullback ρ₁ ρ₂ Q (w ≫ Q))
    {ω₁ : W ⟶ Sc} {ω₂ : W ⟶ P₂} (sq₃ : IsPullback ω₁ ω₂ Q (ρ₁ ≫ Q))
    {s : P₂ ⟶ Sv} {φ : P₁ ≅ P₂}
    (hs₁ : s ≫ w = ρ₁) (hφ₁ : φ.inv ≫ π₁ = s) (hφ₂ : φ.inv ≫ π₂ = ρ₂ ≫ w)
    {l l' : W ⟶ P₂}
    (hl₁ : l ≫ ρ₁ = ω₁) (hl₂ : l ≫ ρ₂ = ω₂ ≫ s)
    (hl₁' : l' ≫ ρ₁ = ω₁) (hl₂' : l' ≫ ρ₂ = ω₂ ≫ ρ₂)
    (hcoc : l ≫ s = l' ≫ s) :
    ∃ (C : CommRingCat.{u}) (k : Γ(Sa, ⊤) ⟶ C) (p : C ⟶ Γ(Sv, ⊤)),
      Function.Injective p.hom ∧ p ≫ s.appTop = p ≫ ρ₂.appTop ∧
        IsPushout Q.appTop k w.appTop p := by
  have _ : Flat Q := hQf
  have _ : _root_.AlgebraicGeometry.IsAffineHom ρ₂ :=
    MorphismProperty.of_isPullback sq₂ (_root_.AlgebraicGeometry.isAffineHom_of_isAffine Q)
  have _ : CompactSpace P₂ := QuasiCompact.compactSpace_of_compactSpace ρ₂
  have _ : QuasiSeparatedSpace P₂ := quasiSeparatedSpace_of_quasiSeparated ρ₂
  let _ : Algebra ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤) := Q.appTop.hom.toAlgebra
  let _ : Algebra ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤) := w.appTop.hom.toAlgebra
  let _ : Algebra ↥Γ(Sa, ⊤) ↥Γ(Sv, ⊤) := (w ≫ Q).appTop.hom.toAlgebra
  have hQ : algebraMap ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤) = Q.appTop.hom :=
    Q.appTop.hom.algebraMap_toAlgebra
  have hW : algebraMap ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤) = w.appTop.hom :=
    w.appTop.hom.algebraMap_toAlgebra
  have hWQ : algebraMap ↥Γ(Sa, ⊤) ↥Γ(Sv, ⊤) = (w ≫ Q).appTop.hom :=
    (w ≫ Q).appTop.hom.algebraMap_toAlgebra
  have : IsScalarTower ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [hQ, hW, hWQ, Scheme.Hom.comp_appTop]
    rfl
  have hQ' : (ofHom (algebraMap ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤)) : Γ(Sa, ⊤) ⟶ Γ(Sc, ⊤)) = Q.appTop := by
    rw [hQ]; rfl
  have hW' : (ofHom (algebraMap ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤)) : Γ(Sc, ⊤) ⟶ Γ(Sv, ⊤)) = w.appTop := by
    rw [hW]; rfl
  have hWQ' : (ofHom (algebraMap ↥Γ(Sa, ⊤) ↥Γ(Sv, ⊤)) : Γ(Sa, ⊤) ⟶ Γ(Sv, ⊤))
      = (w ≫ Q).appTop := by
    rw [hWQ]; rfl
  have po₁ := isPushout_appTop_of_flat sq₁
  have po₂ := (isPushout_appTop_of_flat sq₂.flip).flip
  have po₃ := (isPushout_appTop_of_flat sq₃.flip).flip
  rw [← hWQ', ← hQ'] at po₁
  rw [← hWQ', ← hQ'] at po₂
  rw [Scheme.Hom.comp_appTop, ← hQ'] at po₃
  have happIso : (Scheme.appTopIso φ).hom = φ.inv.appTop := rfl
  have hsapp : π₁.appTop ≫ φ.inv.appTop = s.appTop := by
    rw [← Scheme.Hom.comp_appTop, hφ₁]
  have h1 : (ofHom (algebraMap ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤)) : Γ(Sc, ⊤) ⟶ Γ(Sv, ⊤)) ≫
      π₁.appTop ≫ (Scheme.appTopIso φ).hom = ρ₁.appTop := by
    rw [hW', happIso, hsapp, ← Scheme.Hom.comp_appTop, hs₁]
  have h2 : π₂.appTop ≫ (Scheme.appTopIso φ).hom
      = (ofHom (algebraMap ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤)) : Γ(Sc, ⊤) ⟶ Γ(Sv, ⊤)) ≫ ρ₂.appTop := by
    rw [hW', happIso, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hφ₂]
  have hΛ₁ : ρ₁.appTop ≫ l.appTop = ω₁.appTop := by
    rw [← Scheme.Hom.comp_appTop, hl₁]
  have hΛ₂ : ρ₂.appTop ≫ l.appTop = (π₁.appTop ≫ (Scheme.appTopIso φ).hom) ≫ ω₂.appTop := by
    rw [happIso, hsapp, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hl₂]
  have hΛ₁' : ρ₁.appTop ≫ l'.appTop = ω₁.appTop := by
    rw [← Scheme.Hom.comp_appTop, hl₁']
  have hΛ₂' : ρ₂.appTop ≫ l'.appTop = ρ₂.appTop ≫ ω₂.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hl₂']
  have hcocr : (π₁.appTop ≫ (Scheme.appTopIso φ).hom) ≫ l.appTop
      = (π₁.appTop ≫ (Scheme.appTopIso φ).hom) ≫ l'.appTop := by
    rw [happIso, hsapp, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hcoc]
  obtain ⟨τ, hτ, hinv, hkey⟩ := exists_transition_unitCoassoc_of_isPushout po₁ po₂ po₃
    (Scheme.appTopIso φ) h1 h2 hΛ₁ hΛ₂ hΛ₁' hΛ₂' hcocr
  have hff : Module.FaithfullyFlat ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤) :=
    RingHom.faithfullyFlat_algebraMap_iff.1
      (by
        have _ : Flat Q := hQf
        have _ : Surjective Q := hQs
        rw [hQ]
        exact faithfullyFlat_appTop_of_flat_of_surjective Q)
  have hbij := ModuleCat.bijective_productMap_descentInvariants_of_unitCoassoc
    ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤) τ hτ hkey
  refine ⟨CommRingCat.of ↥(ModuleCat.descentInvariants ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤) τ),
    ofHom (algebraMap ↥Γ(Sa, ⊤)
      ↥(ModuleCat.descentInvariants ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤) τ)),
    ofHom (ModuleCat.descentInvariants ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤) τ).val.toRingHom,
    Subtype.val_injective, ?_, ?_⟩
  · ext x
    have hx := hinv x.val x.2
    rw [happIso, hsapp] at hx
    exact hx
  refine (CommRingCat.isPushout_tensorProduct ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤)
      ↥(ModuleCat.descentInvariants ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤) τ)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((AlgEquiv.ofBijective _ hbij).toRingEquiv.toCommRingCatIso) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp, hQ']
  · simp
  · rw [Iso.refl_hom, Category.id_comp, ← hW']
    ext x
    show (AlgEquiv.ofBijective _ hbij) (x ⊗ₜ[↥Γ(Sa, ⊤)] (1 : _)) = _
    show Algebra.TensorProduct.productMap _ _ (x ⊗ₜ[↥Γ(Sa, ⊤)] (1 : _)) = _
    rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
    rfl
  · rw [Iso.refl_hom, Category.id_comp]
    ext x
    show Algebra.TensorProduct.productMap _ _ ((1 : ↥Γ(Sc, ⊤)) ⊗ₜ[↥Γ(Sa, ⊤)] x) = _
    rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
    rfl



namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {a c v : BigFppfOver B S hS} {h : yoneda.obj a ⟶ Y} {q : c ⟶ a} {w : v ⟶ c}
    {Fst : yoneda.obj v ⟶ X}

/-! ### The action of the groupoid of a chart on the object of a descent datum -/

/-- **The action of the groupoid of a chart on the object of a descent datum.** Let
`vsq` present `yoneda.obj v` as the base change of `f` along `yoneda.map q ≫ h`, with legs `Fst`
to `X` and `yoneda.map w` to `yoneda.obj c`. Given an object `d` of the site, a morphism
`g : d ⟶ c` and a morphism `t : d ⟶ v` which agree after `q`, there is a morphism `u : d ⟶ v`
lying over `g` and agreeing with `t` over `X`.

Thinking of `q : c ⟶ a` as a chart and of `c ×_a c` as a groupoid acting on `v`, `u` is the
translate of `t` to the fibre over `g`. It is unique by
`AlgebraicGeometry.Space.descentAction_unique`, and that uniqueness is the whole content of the
descent datum: the comparison isomorphism and the cocycle condition both follow from it. -/
theorem exists_descentAction (vsq : IsPullback Fst (yoneda.map w) f (yoneda.map q ≫ h))
    {d : BigFppfOver B S hS} (g : d ⟶ c) (t : d ⟶ v) (hgt : g ≫ q = t ≫ w ≫ q) :
    ∃ u : d ⟶ v, u ≫ w = g ∧ yoneda.map u ≫ Fst = yoneda.map t ≫ Fst := by
  have hcomm : (yoneda.map t ≫ Fst) ≫ f = yoneda.map g ≫ yoneda.map q ≫ h := by
    rw [Category.assoc, vsq.w, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
      ← Functor.map_comp_assoc, hgt, Category.assoc]
  refine ⟨yoneda.preimage (vsq.lift (yoneda.map t ≫ Fst) (yoneda.map g) hcomm), ?_, ?_⟩
  · refine yoneda.map_injective ?_
    rw [Functor.map_comp, Functor.map_preimage]
    exact vsq.lift_snd _ _ hcomm
  · rw [Functor.map_preimage]
    exact vsq.lift_fst _ _ hcomm

/-- **The action is unique.** Two morphisms `d ⟶ v` which lie over the same morphism to `c` and
agree over `X` are equal, because `yoneda.obj v` is a fibre product of `X` and `yoneda.obj c`. -/
theorem descentAction_unique (vsq : IsPullback Fst (yoneda.map w) f (yoneda.map q ≫ h))
    {d : BigFppfOver B S hS} {u u' : d ⟶ v} (h1 : u ≫ w = u' ≫ w)
    (h2 : yoneda.map u ≫ Fst = yoneda.map u' ≫ Fst) : u = u' := by
  refine yoneda.map_injective (vsq.hom_ext h2 ?_)
  rw [← Functor.map_comp, ← Functor.map_comp, h1]

/-- **The cocycle condition: the action is associative.** Let `s : P ⟶ v` be a morphism lying over
`ρ₁ : P ⟶ c` and agreeing with `ρ₂ : P ⟶ v` over `X` — the action of
`AlgebraicGeometry.Space.exists_descentAction` for the pair `(ρ₁, ρ₂)`. Let `l, l' : W ⟶ P` be two
morphisms lying over the same `ω₁ : W ⟶ c`, with `l` the translate of `ω₂` by `s` and `l'` the
plain `ω₂`. Then `l ≫ s = l' ≫ s`.

With `P = c ×_a v` and `W = c ×_a (c ×_a v)` this says `x₁ · (x₂ · y) = x₁ · y`: translating `y`
first to the fibre over `x₂` and then to the fibre over `x₁` is translating it to the fibre over
`x₁` directly. It is the cocycle condition of the descent datum, and it holds because both sides
lie over `ω₁` and agree over `X` — over `X` the action does nothing. -/
theorem descentAction_assoc (vsq : IsPullback Fst (yoneda.map w) f (yoneda.map q ≫ h))
    {P : BigFppfOver B S hS} {ρ₁ : P ⟶ c} {ρ₂ s : P ⟶ v}
    (hs₁ : s ≫ w = ρ₁) (hs₂ : yoneda.map s ≫ Fst = yoneda.map ρ₂ ≫ Fst)
    {W : BigFppfOver B S hS} {ω₁ : W ⟶ c} {ω₂ : W ⟶ P} {l l' : W ⟶ P}
    (hl₁ : l ≫ ρ₁ = ω₁) (hl₂ : l ≫ ρ₂ = ω₂ ≫ s)
    (hl₁' : l' ≫ ρ₁ = ω₁) (hl₂' : l' ≫ ρ₂ = ω₂ ≫ ρ₂) :
    l ≫ s = l' ≫ s := by
  have key : ∀ k : W ⟶ P, yoneda.map (k ≫ s) ≫ Fst = yoneda.map (k ≫ ρ₂) ≫ Fst := by
    intro k
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hs₂]
  refine descentAction_unique vsq ?_ ?_
  · rw [Category.assoc, Category.assoc, hs₁, hl₁, hl₁']
  · rw [key l, key l', hl₂, hl₂', key ω₂]

variable {A₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A₀ ⟶ X} {r : A₀ ⟶ yoneda.obj c}

/-! ### The descent datum of a representable morphism, with its action -/

/-- Transporting a Cartesian square along an isomorphism of its source. -/
private theorem isPullback_inv_comp_of_iso (sq : IsPullback m r f (yoneda.map q ≫ h))
    (e : A₀ ≅ yoneda.obj v) (hew : e.hom ≫ yoneda.map w = r) :
    IsPullback (e.inv ≫ m) (yoneda.map w) f (yoneda.map q ≫ h) := by
  refine sq.of_iso e (Iso.refl X) (Iso.refl (yoneda.obj c)) (Iso.refl Y) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
  · rw [Iso.refl_hom, Category.comp_id, hew]
  · simp
  · simp

/-- **The presheaf-level datum of a representable morphism, together with its action.** This is
`AlgebraicGeometry.Space.exists_descentDatum_of_isPullback` with the comparison isomorphism
`φ` replaced by the data it comes from: the action `s : P₂ ⟶ v` of the groupoid `c ×_a c` on `v`,
which lies over the first projection `ρ₁` and agrees with the second projection `ρ₂` over `X`,
and the two triangles identifying `φ.inv` with the pair `(s, ρ₂ ≫ w)`.

The extra output over the earlier statement is the single equation
`yoneda.map s ≫ e.inv ≫ m = yoneda.map ρ₂ ≫ e.inv ≫ m`, and it is what makes the cocycle
condition available: feed it to `AlgebraicGeometry.Space.descentAction_assoc`. The isomorphism
`φ` is here constructed from `s` and from the action `s'` of the opposite pair, rather than taken
from `CategoryTheory.IsPullback.isoIsPullback`; the two agree, by uniqueness of the action. -/
theorem exists_descentAction_of_isPullback {P : MorphismProperty Scheme.{u}}
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hr : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf r) :
    ∃ (v : BigFppfOver B S hS) (w : v ⟶ c) (e : A₀ ≅ yoneda.obj v),
      P ((BigFppfOver.toScheme B S hS).map w) ∧
      e.hom ≫ yoneda.map w = r ∧
      ∃ (P₁ P₂ : BigFppfOver B S hS) (π₁ : P₁ ⟶ v) (π₂ : P₁ ⟶ c)
        (ρ₁ : P₂ ⟶ c) (ρ₂ s : P₂ ⟶ v) (φ : P₁ ≅ P₂),
        IsPullback π₁ π₂ (w ≫ q) q ∧ IsPullback ρ₁ ρ₂ q (w ≫ q) ∧
        s ≫ w = ρ₁ ∧
        yoneda.map s ≫ e.inv ≫ m = yoneda.map ρ₂ ≫ e.inv ≫ m ∧
        φ.inv ≫ π₁ = s ∧ φ.inv ≫ π₂ = ρ₂ ≫ w := by
  obtain ⟨v, w, e, hwaff, hew, P₁, P₂, π₁, π₂, ρ₁, ρ₂, -, sq₁, sq₂, -, -⟩ :=
    exists_descentDatum_of_isPullback sq hr
  have vsq := isPullback_inv_comp_of_iso sq e hew
  obtain ⟨s, hs₁, hs₂⟩ := exists_descentAction vsq ρ₁ ρ₂ sq₂.w
  obtain ⟨s', hs₁', hs₂'⟩ := exists_descentAction vsq π₂ π₁ sq₁.w.symm
  have hcondh : (π₁ ≫ w) ≫ q = s' ≫ w ≫ q := by
    rw [← Category.assoc, hs₁', Category.assoc]; exact sq₁.w
  have hcondi : s ≫ w ≫ q = (ρ₂ ≫ w) ≫ q := by
    rw [← Category.assoc, hs₁, Category.assoc]; exact sq₂.w
  have hΦ₁ : sq₂.lift (π₁ ≫ w) s' hcondh ≫ ρ₁ = π₁ ≫ w := sq₂.lift_fst _ _ hcondh
  have hΦ₂ : sq₂.lift (π₁ ≫ w) s' hcondh ≫ ρ₂ = s' := sq₂.lift_snd _ _ hcondh
  have hΦ₃ : sq₁.lift s (ρ₂ ≫ w) hcondi ≫ π₁ = s := sq₁.lift_fst _ _ hcondi
  have hΦ₄ : sq₁.lift s (ρ₂ ≫ w) hcondi ≫ π₂ = ρ₂ ≫ w := sq₁.lift_snd _ _ hcondi
  have hA : sq₂.lift (π₁ ≫ w) s' hcondh ≫ s = π₁ := by
    refine descentAction_unique vsq ?_ ?_
    · rw [Category.assoc, hs₁, hΦ₁]
    · rw [Functor.map_comp, Category.assoc, hs₂, ← Category.assoc, ← Functor.map_comp, hΦ₂, hs₂']
  have hBb : sq₁.lift s (ρ₂ ≫ w) hcondi ≫ s' = ρ₂ := by
    refine descentAction_unique vsq ?_ ?_
    · rw [Category.assoc, hs₁', hΦ₄]
    · rw [Functor.map_comp, Category.assoc, hs₂', ← Category.assoc, ← Functor.map_comp, hΦ₃, hs₂]
  refine ⟨v, w, e, hwaff, hew, P₁, P₂, π₁, π₂, ρ₁, ρ₂, s,
    ⟨sq₂.lift (π₁ ≫ w) s' hcondh, sq₁.lift s (ρ₂ ≫ w) hcondi, ?_, ?_⟩, sq₁, sq₂,
    hs₁, hs₂, hΦ₃, hΦ₄⟩
  · refine sq₁.hom_ext ?_ ?_
    · rw [Category.assoc, hΦ₃, hA, Category.id_comp]
    · rw [Category.assoc, hΦ₄, ← Category.assoc, hΦ₂, hs₁', Category.id_comp]
  · refine sq₂.hom_ext ?_ ?_
    · rw [Category.assoc, hΦ₁, ← Category.assoc, hΦ₃, hs₁, Category.id_comp]
    · rw [Category.assoc, hΦ₂, hBb, Category.id_comp]

/-- **The presheaf-level datum of an affine morphism, together with its action.** This is
`AlgebraicGeometry.Space.exists_descentAction_of_isPullback` at the affine morphisms, over an
affine `c`, with the extra record that the representing object `v` is then itself an affine
scheme. That affineness is a consequence of the property — `v` is affine over `c` and `c` is
affine — and not of the datum, which is why the property-generic statement does not carry it.

It stands to `AlgebraicGeometry.Space.exists_affineDescentDatum_of_isPullback` as
`AlgebraicGeometry.Space.exists_descentAction_of_isPullback` stands to
`AlgebraicGeometry.Space.exists_descentDatum_of_isPullback`: the comparison isomorphism `φ` is
replaced by the data it comes from, the action `s : P₂ ⟶ v` of the groupoid `c ×_a c` on `v`,
which lies over the first projection `ρ₁` and agrees with the second projection `ρ₂` over `X`,
together with the two triangles identifying `φ.inv` with the pair `(s, ρ₂ ≫ w)`.

The extra output over the datum alone is the single equation
`yoneda.map s ≫ e.inv ≫ m = yoneda.map ρ₂ ≫ e.inv ≫ m`, and it is what makes the cocycle
condition available: feed it to `AlgebraicGeometry.Space.descentAction_assoc`. -/
theorem exists_affineDescentAction_of_isPullback
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hr : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsAffineHom.{u})
      (BigFppfOver.toScheme B S hS)).presheaf r)
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c)) :
    ∃ (v : BigFppfOver B S hS) (w : v ⟶ c) (e : A₀ ≅ yoneda.obj v),
      IsAffine ((BigFppfOver.toScheme B S hS).obj v) ∧
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map w) ∧
      e.hom ≫ yoneda.map w = r ∧
      ∃ (P₁ P₂ : BigFppfOver B S hS) (π₁ : P₁ ⟶ v) (π₂ : P₁ ⟶ c)
        (ρ₁ : P₂ ⟶ c) (ρ₂ s : P₂ ⟶ v) (φ : P₁ ≅ P₂),
        IsPullback π₁ π₂ (w ≫ q) q ∧ IsPullback ρ₁ ρ₂ q (w ≫ q) ∧
        s ≫ w = ρ₁ ∧
        yoneda.map s ≫ e.inv ≫ m = yoneda.map ρ₂ ≫ e.inv ≫ m ∧
        φ.inv ≫ π₁ = s ∧ φ.inv ≫ π₂ = ρ₂ ≫ w := by
  obtain ⟨v, w, e, hwaff, hew, rest⟩ := exists_descentAction_of_isPullback sq hr
  exact ⟨v, w, e, isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map w), hwaff, hew,
    rest⟩

/-- **Effective descent on global sections for the datum of a quasi-compact quasi-separated
morphism over an affine chart.** Let `f : X ⟶ Y` be a morphism of presheaves on the big fppf
site of `S`, let `h : yoneda.obj a ⟶ Y` with `a` affine, let `q : c ⟶ a` be a flat surjection of
the site with `c` affine, and let `m, r` present `A₀` as the base change of `f` along
`yoneda.map q ≫ h`, with `r` representable by morphisms with `P`, a property below the
quasi-compact quasi-separated ones. Then the datum descends on global sections: the representing
object `v` of `A₀` carries `P` over `c`, and there is a ring `C` under `Γ(a)` and inside `Γ(v)`
with `Γ(v)` the pushout of `Γ(c) ← Γ(a) → C`.

For `P` the affine morphisms this says `v = c ×_a Spec C`; in general it says that the affine
hull of `v` is `c ×_a Spec C`, which is what Stacks 0247 descends. See
`AlgebraicGeometry.exists_descentPushout_of_isPullback`.

The action `s : P₂ ⟶ v` of the groupoid `c ×_a c` on `v` is returned alongside, with the two
properties that characterise it — it lies over the first projection, and it agrees with the
second projection over `X` — and with the one property that ties it to `C`: the inclusion
`p : C ⟶ Γ(v)` is equalized by `s` and by the second projection. That equation says the action
is a morphism *over* `Spec C`, which is what identifies `P₂` with `v ×_{Spec C} v` and makes
the descent datum on `v` the canonical one; it holds because `C` is by construction the ring of
invariants of the coaction that `s` induces.

This is Stacks 0245 for a single affine chart, and the whole of the affine descent argument:
`AlgebraicGeometry.Space.exists_descentAction_of_isPullback` produces the datum and its
action, `AlgebraicGeometry.Space.descentAction_assoc` the cocycle condition, and
`AlgebraicGeometry.exists_descentPushout_of_isPullback` the descended algebra. What it does not
do is put `Spec C` back into the site; see the implementation notes of this file. The action and
its equation over `Spec C` are consumed by
`AlgebraicGeometry.Space.descentSection_eq_of_comp_eq` of
`StacksFrontier.AlgebraicGeometry.Descent.AffineHomEffectiveDescent`. -/
theorem exists_descentPushout_appTop_of_isPullback {P : MorphismProperty Scheme.{u}}
    (hPqc : P ≤ (@QuasiCompact.{u} : MorphismProperty Scheme.{u}))
    (hPqs : P ≤ (@QuasiSeparated.{u} : MorphismProperty Scheme.{u}))
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hr : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf r)
    (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a))
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q)) :
    ∃ (v : BigFppfOver B S hS) (w : v ⟶ c) (e : A₀ ≅ yoneda.obj v),
      P ((BigFppfOver.toScheme B S hS).map w) ∧
      e.hom ≫ yoneda.map w = r ∧
      ∃ (P₂ : BigFppfOver B S hS) (ρ₁ : P₂ ⟶ c) (ρ₂ s : P₂ ⟶ v),
        IsPullback ρ₁ ρ₂ q (w ≫ q) ∧ s ≫ w = ρ₁ ∧
        yoneda.map s ≫ e.inv ≫ m = yoneda.map ρ₂ ≫ e.inv ≫ m ∧
      ∃ (C : CommRingCat.{u}) (k : Γ((BigFppfOver.toScheme B S hS).obj a, ⊤) ⟶ C)
        (p : C ⟶ Γ((BigFppfOver.toScheme B S hS).obj v, ⊤)),
        Function.Injective p.hom ∧
        p ≫ ((BigFppfOver.toScheme B S hS).map s).appTop =
          p ≫ ((BigFppfOver.toScheme B S hS).map ρ₂).appTop ∧
        IsPushout ((BigFppfOver.toScheme B S hS).map q).appTop k
          ((BigFppfOver.toScheme B S hS).map w).appTop p := by
  obtain ⟨v, w, e, hwaff, hew, P₁, P₂, π₁, π₂, ρ₁, ρ₂, s, φ, sq₁, sq₂,
    hs₁, hs₂, hφ₁, hφ₂⟩ := exists_descentAction_of_isPullback sq hr
  refine ⟨v, w, e, hwaff, hew, P₂, ρ₁, ρ₂, s, sq₂, hs₁, hs₂, ?_⟩
  have vsq := isPullback_inv_comp_of_iso sq e hew
  -- the triple fibre product, and the two morphisms to `P₂` whose images under `s` agree
  obtain ⟨T₀, ω₁, ω₂, sq₃⟩ : ∃ (T₀ : BigFppfOver B S hS) (ω₁ : T₀ ⟶ c) (ω₂ : T₀ ⟶ P₂),
      IsPullback ω₁ ω₂ q (ρ₁ ≫ q) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l : T₀ ⟶ P₂, l ≫ ρ₁ = ω₁ ∧ l ≫ ρ₂ = ω₂ ≫ s := by
    have cond : ω₁ ≫ q = (ω₂ ≫ s) ≫ w ≫ q := by
      rw [Category.assoc, ← Category.assoc s, hs₁]; exact sq₃.w
    exact ⟨sq₂.lift _ _ cond, sq₂.lift_fst _ _ cond, sq₂.lift_snd _ _ cond⟩
  obtain ⟨l', hl₁', hl₂'⟩ : ∃ l' : T₀ ⟶ P₂, l' ≫ ρ₁ = ω₁ ∧ l' ≫ ρ₂ = ω₂ ≫ ρ₂ := by
    have cond : ω₁ ≫ q = (ω₂ ≫ ρ₂) ≫ w ≫ q := by
      rw [Category.assoc, ← sq₂.w]; exact sq₃.w
    exact ⟨sq₂.lift _ _ cond, sq₂.lift_fst _ _ cond, sq₂.lift_snd _ _ cond⟩
  have hcoc : l ≫ s = l' ≫ s :=
    descentAction_assoc vsq hs₁ hs₂ hl₁ hl₂ hl₁' hl₂'
  -- pass to schemes
  have _ : QuasiCompact ((BigFppfOver.toScheme B S hS).map w) := hPqc _ hwaff
  have _ : QuasiSeparated ((BigFppfOver.toScheme B S hS).map w) := hPqs _ hwaff
  have _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj v) :=
    QuasiCompact.compactSpace_of_compactSpace ((BigFppfOver.toScheme B S hS).map w)
  have _ : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj v) :=
    quasiSeparatedSpace_of_quasiSeparated ((BigFppfOver.toScheme B S hS).map w)
  set F := BigFppfOver.toScheme B S hS with hF
  have msq₁ : IsPullback (F.map π₁) (F.map π₂) (F.map w ≫ F.map q) (F.map q) := by
    rw [← Functor.map_comp]; exact sq₁.map F
  have msq₂ : IsPullback (F.map ρ₁) (F.map ρ₂) (F.map q) (F.map w ≫ F.map q) := by
    rw [← Functor.map_comp]; exact sq₂.map F
  have msq₃ : IsPullback (F.map ω₁) (F.map ω₂) (F.map q) (F.map ρ₁ ≫ F.map q) := by
    rw [← Functor.map_comp]; exact sq₃.map F
  exact exists_descentPushout_of_isPullback hqs hqf msq₁ msq₂ msq₃
    (by rw [← F.map_comp, hs₁]) (by rw [Functor.mapIso_inv, ← F.map_comp, hφ₁])
    (by rw [Functor.mapIso_inv, ← F.map_comp, ← F.map_comp, hφ₂])
    (by rw [← F.map_comp, hl₁]) (by rw [← F.map_comp, ← F.map_comp, hl₂])
    (by rw [← F.map_comp, hl₁']) (by rw [← F.map_comp, ← F.map_comp, hl₂'])
    (by rw [← F.map_comp, ← F.map_comp, hcoc])

end Space

end AlgebraicGeometry

end
