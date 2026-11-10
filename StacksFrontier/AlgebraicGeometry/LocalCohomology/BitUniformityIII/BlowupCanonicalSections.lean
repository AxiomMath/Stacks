module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupTwistedPullbackModuleSituation
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.SupportedAnnihilation
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical maps `I^q ⊗_A M ⟶ H⁰(X, p^*M(q))` on the blowup

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `p : X ⟶ Spec(A)` the blowup of `Spec(A)` in
`I`. This file builds the last two fields of
`Stacks.LocalCohomology.UniformityIII.TwistedModuleSituation` on that blowup: the canonical map
`secM` of [Stacks, Tag 0GAA] clause (4) and its compatibility `secM_freeSections` with the
chosen finite free presentation.

## The construction

`secM` goes out of `Stacks.LocalCohomology.UniformityIII.powTensor I n q M`, which is
`(I^q/I^{q+n}) ⊗_A M`, so it is a map out of a tensor product and is built by
`TensorProduct.lift` from an `A`-bilinear map. The bilinear map is the composite of two things
that are already available:

* on the left factor, the canonical map `I^q/I^{q+n} ⟶ H⁰(X, 𝒪_{Yₙ}(q))` — the field `cdiv` of
  the Situation, `Stacks.LocalCohomology.UniformityIII.cdivMod` — read back into
  `H⁰(X, 𝒪_X(q) ⊗ p^*((A/Iⁿ)~))` along
  `Stacks.LocalCohomology.UniformityIII.blowupHmodTwistedPullbackQuotientEquiv`;
* on the right factor, an element `m` of `M` read as the `A ⧸ Iⁿ`-linear map `A ⧸ Iⁿ ⟶ M`,
  `x ↦ x·m` (`resSmulHom`), pushed through `Hⁱ(X, 𝒪_X(q) ⊗ p^*(-))`.

So `secM (a ⊗ m)` is the image of the section `a` of `𝒪_{Yₙ}(q)` under the map of sheaves that
`x ↦ x·m` induces. Nothing here is a new geometric input; what has to be checked is that the
assignment is *bilinear*, and that is where linearity rather than additivity of the functor is
used.

## Why `A`-linearity of the cohomology functor is the crux

Additivity of `N ↦ Hⁱ(X, 𝒪_X(q) ⊗ p^*Ñ)` gives additivity of `secM` in `m`; for the scalar
`r : A` one needs `Hⁱ(X, 𝒪_X(q) ⊗ p^*(r · φ)) = r · Hⁱ(X, 𝒪_X(q) ⊗ p^*φ)`, because `x ↦ x·(r·m)`
is `r` times `x ↦ x·m`. That is `CategoryTheory.Functor.Linear`, and both halves of it are
proved: `Stacks.LocalCohomology.UniformityIII.linear_twistedPullbackFunctor` for the twisted
pullback and, for the cohomology, `Stacks.Blowup.linear_globalSectionsOver` composed with
`CategoryTheory.Functor.linear_rightDerived`. The two linear structures on sheaves of modules on
the blowup — the one the `AlgebraicGeometry.Scheme.Modules` view carries and the one the
`CategoryTheory.SheafOfModules` view is stated at — are definitionally equal, so the transport is
the same device as
`Stacks.LocalCohomology.UniformityIII.additive_twistedPullbackFunctor`.

`linear_twistedPullbackCohomologyFunctor` below is stated with *no* exotic instance in its type:
its source and target are both `ModuleCat A`, whose `CategoryTheory.Linear` structure is
Mathlib's. The non-instance linear structure on the sheaves appears only inside the proof.

## Why the free presentation has to be matched coordinatewise

The field `secM_freeSections` compares `secM` on the image of
`Stacks.LocalCohomology.UniformityIII.ANCPresentation.freeTensor` with the composite through
`H⁰(X, (𝒪_{Yₙ})^{⊕r}(q))`. The field `freeIso` of
`Stacks.LocalCohomology.UniformityIII.ModuleSituation` is
`Stacks.LocalCohomology.UniformityIII.blowupFreeIso`, built from
`Stacks.LocalCohomology.UniformityIII.blowupHmodTwistedPullbackPiEquiv`, which is in turn the
preservation of a biproduct by an additive functor. So the comparison needs that equivalence
read on elements, in both directions:

* `blowupHmodTwistedPullbackPiEquiv_apply`, each coordinate of the forward map is the functor
  applied to a projection — proved from `CategoryTheory.Limits.biproduct.lift_π` and
  `ModuleCat.biproductIsoPi_inv_comp_π`;
* `blowupHmodTwistedPullbackPiEquiv_symm_apply`, the inverse is the sum over the coordinates of
  the functor applied to the inclusions — deduced from the first by injectivity, since the
  forward map carries the `j`-th inclusion to `Pi.single j` (additivity makes the off-diagonal
  terms vanish).

With that, `secM_freeSections` is the coordinatewise identity
`P.proj ∘ (Pi.single j) = (x ↦ x · P.proj (Pi.single j 1))`, which is `A ⧸ Iⁿ`-linearity of the
presentation's surjection.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.resSmulHom`: `A ⧸ Iⁿ ⟶ M`, `x ↦ x·m`, over `A`.
* `Stacks.LocalCohomology.UniformityIII.twistedPullbackSecM`: **the field `secM`**, the canonical
  map `(I^q/I^{q+n}) ⊗_A M →ₗ[A] H⁰(X, 𝒪_X(q) ⊗ p^*M̃)`, at the blowup's `ModuleSituation`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.linear_twistedPullbackCohomologyFunctor`:
  **`N ↦ Hⁱ(X, 𝒪_X(q) ⊗ p^*Ñ)` is `A`-linear.**
* `Stacks.LocalCohomology.UniformityIII.blowupHmodTwistedPullbackPiEquiv_apply` and
  `…_symm_apply`: the finite-direct-sum comparison read on elements.
* `Stacks.LocalCohomology.UniformityIII.twistedPullbackSecM_freeSections`: **the field
  `secM_freeSections`**, at the blowup's `ModuleSituation`.

## References

* [Stacks Project, Tag 0GAA](https://stacks.math.columbia.edu/tag/0GAA)
* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal' modulesEnoughInjectives
attribute [local instance] sheafSectionsPreservesFiniteLimits secFPreservesFiniteLimits
attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### `Hⁱ(X, 𝒪_X(q) ⊗ p^*(-))` is `A`-linear -/

/-- **`A`-linear global sections on the blowup is `A`-linear**, at the
`CategoryTheory.SheafOfModules` view of the category of sheaves of modules.

The term is `Stacks.Blowup.linear_globalSectionsOver` itself, which typechecks here because
`blowupΓmod` is `AlgebraicGeometry.globalSectionsOver` of `Stacks.Blowup.toSpec` and the two
views of the category are definitionally equal; the restatement is the same device as
`additive_twistedPullbackFunctor`. -/
theorem linear_blowupΓmod :
    letI : Linear A (_root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf) :=
      Stacks.Blowup.blowUpModulesLinear I
    (blowupΓmod I).Linear A :=
  let : Linear A (_root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf) :=
    Stacks.Blowup.blowUpModulesLinear I
  Stacks.Blowup.linear_globalSectionsOver I

/-- **`Hⁱ(X, -)` on the blowup is `A`-linear.** A right derived functor of an `A`-linear functor
is `A`-linear (`CategoryTheory.Functor.linear_rightDerived`), and the underived functor is
`linear_blowupΓmod`. -/
theorem linear_rightDerived_blowupΓmod (i : ℕ) :
    letI : Linear A (_root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf) :=
      Stacks.Blowup.blowUpModulesLinear I
    ((blowupΓmod I).rightDerived i).Linear A := by
  let : Linear A (_root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf) :=
    Stacks.Blowup.blowUpModulesLinear I
  let : (blowupΓmod I).Linear A := linear_blowupΓmod I
  exact Functor.linear_rightDerived _ i

/-- **`N ↦ Hⁱ(X, 𝒪_X(q) ⊗ p^*Ñ)` is an `A`-linear functor `Mod(A) ⥤ Mod(A)`.** -/
theorem linear_twistedPullbackCohomologyFunctor (i : ℕ) (q : ℤ) :
    (twistedPullbackCohomologyFunctor I i q).Linear A := by
  let : Linear A (_root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf) :=
    Stacks.Blowup.blowUpModulesLinear I
  let : (twistedPullbackFunctor I q).Linear A := linear_twistedPullbackFunctor I q
  let : ((blowupΓmod I).rightDerived i).Linear A := linear_rightDerived_blowupΓmod I i
  exact inferInstanceAs
    ((twistedPullbackFunctor I q ⋙ (blowupΓmod I).rightDerived i).Linear A)

/-! ### The finite-direct-sum comparison on elements -/

section Pi

variable (N : ModuleCat.{u} A) (r i : ℕ) (q : ℤ)

/-- **Each coordinate of `Hⁱ(X, 𝒪_X(q) ⊗ p^*((N^{⊕r})~)) ≅ (Hⁱ(X, 𝒪_X(q) ⊗ p^*Ñ))^{⊕r}` is the
functor applied to a projection.**

`blowupHmodTwistedPullbackPiEquiv` is the composite of three isomorphisms, and the three steps
of the proof are one each: `ModuleCat.biproductIsoPi_inv_comp_π` turns the projection out of the
function type into the biproduct's projection, `CategoryTheory.Functor.mapBiproduct_hom` with
`CategoryTheory.Limits.biproduct.lift_π` carries that projection through the functor, and
`ModuleCat.biproductIsoPi_inv_comp_π` again turns the biproduct's projection on the source back
into the projection out of the function type. -/
theorem blowupHmodTwistedPullbackPiEquiv_apply
    (x : blowupHmodTwistedPullback I (ModuleCat.of A (Fin r → N)) i q) (k : Fin r) :
    blowupHmodTwistedPullbackPiEquiv I N r i q x k =
      (twistedPullbackCohomologyFunctor I i q).map
        (ModuleCat.ofHom (LinearMap.proj k : ((_ : Fin r) → N) →ₗ[A] N)) x := by
  have hA : (ModuleCat.biproductIsoPi
        ((twistedPullbackCohomologyFunctor I i q).obj ∘ fun _ : Fin r => N)).hom ≫
      ModuleCat.ofHom (LinearMap.proj k) =
        biproduct.π ((twistedPullbackCohomologyFunctor I i q).obj ∘ fun _ : Fin r => N) k := by
    rw [← ModuleCat.biproductIsoPi_inv_comp_π, Iso.hom_inv_id_assoc]
  have hB : ((twistedPullbackCohomologyFunctor I i q).mapBiproduct
        (fun _ : Fin r => N)).hom ≫
      biproduct.π ((twistedPullbackCohomologyFunctor I i q).obj ∘ fun _ : Fin r => N) k =
        (twistedPullbackCohomologyFunctor I i q).map (biproduct.π (fun _ : Fin r => N) k) := by
    rw [CategoryTheory.Functor.mapBiproduct_hom]
    exact biproduct.lift_π _ k
  have key : ((twistedPullbackCohomologyFunctor I i q).mapIso
          (ModuleCat.biproductIsoPi (fun _ : Fin r => N)).symm ≪≫
        (twistedPullbackCohomologyFunctor I i q).mapBiproduct (fun _ : Fin r => N) ≪≫
        ModuleCat.biproductIsoPi
          ((twistedPullbackCohomologyFunctor I i q).obj ∘ fun _ : Fin r => N)).hom ≫
      ModuleCat.ofHom (LinearMap.proj k) =
        (twistedPullbackCohomologyFunctor I i q).map
          (ModuleCat.ofHom (LinearMap.proj k : ((_ : Fin r) → N) →ₗ[A] N)) := by
    rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc, hA, hB,
      CategoryTheory.Functor.mapIso_hom, Iso.symm_hom, ← CategoryTheory.Functor.map_comp,
      ModuleCat.biproductIsoPi_inv_comp_π]
  exact ConcreteCategory.congr_hom key x

/-- **The inverse of the finite-direct-sum comparison is the sum over the coordinates of the
functor applied to the inclusions.**

By `blowupHmodTwistedPullbackPiEquiv_apply` the forward map carries
`Hⁱ(X, 𝒪_X(q) ⊗ p^*(single j)~)` to `Pi.single j`: the `k`-th coordinate is the functor applied
to `LinearMap.proj k ∘ LinearMap.single j`, which is the identity for `k = j` and zero
otherwise, and the functor is additive so it kills the zero map. Since
`Finset.univ_sum_single` reassembles a function from its coordinates, applying the (injective)
forward map identifies the two sides. -/
theorem blowupHmodTwistedPullbackPiEquiv_symm_apply
    (w : Fin r → blowupHmodTwistedPullback I N i q) :
    (blowupHmodTwistedPullbackPiEquiv I N r i q).symm w =
      ∑ j : Fin r, (twistedPullbackCohomologyFunctor I i q).map
        (ModuleCat.ofHom (LinearMap.single A (fun _ : Fin r => (N : Type u)) j)) (w j) := by
  refine ((blowupHmodTwistedPullbackPiEquiv I N r i q).symm_apply_eq).2 (funext fun k => ?_).symm
  rw [map_sum]
  have hcoord : ∀ j : Fin r,
      blowupHmodTwistedPullbackPiEquiv I N r i q
          ((twistedPullbackCohomologyFunctor I i q).map
            (ModuleCat.ofHom (LinearMap.single A (fun _ : Fin r => (N : Type u)) j)) (w j)) =
        Pi.single j (w j) := by
    intro j
    funext k'
    rw [blowupHmodTwistedPullbackPiEquiv_apply, ← CategoryTheory.comp_apply,
      ← CategoryTheory.Functor.map_comp, ← ModuleCat.ofHom_comp]
    by_cases hk : k' = j
    · subst hk
      rw [LinearMap.proj_comp_single_same, ModuleCat.ofHom_id, CategoryTheory.Functor.map_id,
        Pi.single_eq_same]
      rfl
    · rw [LinearMap.proj_comp_single_ne A _ k' j hk, ModuleCat.ofHom_zero,
        CategoryTheory.Functor.map_zero, Pi.single_eq_of_ne hk]
      rfl
  calc (∑ j : Fin r, blowupHmodTwistedPullbackPiEquiv I N r i q
          ((twistedPullbackCohomologyFunctor I i q).map
            (ModuleCat.ofHom (LinearMap.single A (fun _ : Fin r => (N : Type u)) j)) (w j))) k
      = (∑ j : Fin r, Pi.single j (w j)) k := by
        rw [Finset.sum_congr rfl fun j _ => hcoord j]
    _ = w k := by rw [Finset.univ_sum_single]

end Pi

/-! ### An element of `M` read as a map `A ⧸ Iⁿ ⟶ M` -/

section Smul

variable (n : ℕ) (M : ModuleCat.{u} (A ⧸ I ^ n))

/-- **An element `m` of an `A ⧸ Iⁿ`-module read as the map `A ⧸ Iⁿ ⟶ M`, `x ↦ x·m`**, over `A`.

This is the right-hand factor of the canonical map of [Stacks, Tag 0GAA] clause (4): pushing it
through `𝒪_X(q) ⊗ p^*(-)` turns a section of `𝒪_{Yₙ}(q)` into a section of `𝒪_X(q) ⊗ p^*M̃`. It
is `A`-linear because it is `A ⧸ Iⁿ`-linear, the `A`-action on both sides being the one along
`A → A ⧸ Iⁿ`. -/
def resSmulLin (m : resModule I n M) : (A ⧸ I ^ n) →ₗ[A] resModule I n M where
  toFun x := x • show (M : Type u) from m
  map_add' x y := add_smul x y _
  map_smul' a x := mul_smul (Ideal.Quotient.mk (I ^ n) a) x _

/-- `resSmulLin` as a morphism of `A`-modules. -/
def resSmulHom (m : resModule I n M) :
    ModuleCat.of A (A ⧸ I ^ n) ⟶ resModule I n M :=
  ConcreteCategory.ofHom (resSmulLin I n M m)

/-- The map `resSmulHom` on an element: the `show` is the identity on carriers, moving `m`
from the `A`-module `resModule I n M` to the `A ⧸ Iⁿ`-module `M` so that the scalar `x` acts. -/
theorem resSmulHom_hom_apply (m : resModule I n M) (x : A ⧸ I ^ n) :
    (resSmulHom I n M m).hom x = x • show (M : Type u) from m := rfl

/-- `x ↦ x·m` is additive in `m`. -/
theorem resSmulHom_add (m₁ m₂ : resModule I n M) :
    resSmulHom I n M (m₁ + m₂) = resSmulHom I n M m₁ + resSmulHom I n M m₂ :=
  ModuleCat.hom_ext (LinearMap.ext fun x => smul_add x _ _)

/-- `x ↦ x·m` is `A`-linear in `m`: the scalar can be moved past `x` because `A ⧸ Iⁿ` is
commutative. -/
theorem resSmulHom_smul (a : A) (m : resModule I n M) :
    resSmulHom I n M (a • m) = a • resSmulHom I n M m :=
  ModuleCat.hom_ext (LinearMap.ext fun x => by
    change x • (Ideal.Quotient.mk (I ^ n) a • show (M : Type u) from m) =
      Ideal.Quotient.mk (I ^ n) a • (x • show (M : Type u) from m)
    rw [smul_smul, smul_smul, mul_comm])

end Smul

/-! ### The field `secM` -/

section SecM

variable [IsNoetherianRing A]

/-- **`m ↦ Hⁱ(X, 𝒪_X(q) ⊗ p^*(x ↦ x·m))` as an `A`-linear map**, the second factor of the
canonical map of [Stacks, Tag 0GAA] clause (4).

Additivity in `m` is `resSmulHom_add` with additivity of the functor; `A`-linearity in `m` is
`resSmulHom_smul` with `linear_twistedPullbackCohomologyFunctor`, and that is the one place
where linearity rather than additivity of the cohomology of the twisted pullback is used. -/
def blowupSecEval (n : ℕ) (M : ModuleCat.{u} (A ⧸ I ^ n)) (q : ℤ) :
    resModule I n M →ₗ[A]
      (blowupHmodTwistedPullback I (ModuleCat.of A (A ⧸ I ^ n)) 0 q →ₗ[A]
        blowupHmodTwistedPullback I (resModule I n M) 0 q) where
  toFun m := ((twistedPullbackCohomologyFunctor I 0 q).map (resSmulHom I n M m)).hom
  map_add' m₁ m₂ := by
    rw [resSmulHom_add, CategoryTheory.Functor.map_add]
    rfl
  map_smul' a m := by
    let := linear_twistedPullbackCohomologyFunctor I 0 q
    rw [resSmulHom_smul, Functor.Linear.map_smul]
    rfl

/-- **The field `secM` of `Stacks.LocalCohomology.UniformityIII.TwistedModuleSituation`, on the
blowup**: the canonical `A`-linear map

`(I^q/I^{q+n}) ⊗_A M ⟶ H⁰(X, 𝒪_X(q) ⊗ p^*M̃)`.

On a generator `a ⊗ m` it is the section of `𝒪_X(q) ⊗ p^*M̃` obtained from the section `a` of
`𝒪_{Yₙ}(q)` — that is the field `cdiv` of the Situation,
`Stacks.LocalCohomology.UniformityIII.cdivMod`, read back along
`Stacks.LocalCohomology.UniformityIII.blowupHmodTwistedPullbackQuotientEquiv` — by applying
`𝒪_X(q) ⊗ p^*(-)` to `x ↦ x·m`.

The source is the tensor product and not the submodule `I^qM` of `M`; see
`Stacks.LocalCohomology.UniformityIII.powTensor` for why the clause is false for the submodule.
At `n = 0` the field `cdiv` of `blowupSituationOf` is the zero map — the source defines `Yₙ`
only for `n ≥ 1` and `A ⧸ I⁰` is the zero ring — so this map is zero there, which is consistent
because its target then vanishes too. -/
def twistedPullbackSecM (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ) (hcn : c ≤ n)
    (M : ANCModule I n c) (q : ℕ) :
    powTensor I n q M.1 →ₗ[A] (blowupModuleSituationOf I q₀ h n c hcn).H M 0 (q : ℤ) :=
  TensorProduct.lift
    ((blowupSecEval I n M.1 (q : ℤ)).flip.comp
      (((blowupHmodTwistedPullbackQuotientEquiv I n 0 q).symm.toLinearMap).comp
        ((blowupSituationOf I q₀ h).cdiv n q)))

/-- **`twistedPullbackSecM` on a generator**: `a ⊗ m` goes to the image of the section `a` of
`𝒪_{Yₙ}(q)` under `𝒪_X(q) ⊗ p^*(x ↦ x·m)`. This is the definition unfolded, and it is what
`twistedPullbackSecM_freeSections` is proved from. -/
theorem twistedPullbackSecM_tmul (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ) (hcn : c ≤ n)
    (M : ANCModule I n c) (q : ℕ) (a : powQuot I q n) (m : resModule I n M.1) :
    twistedPullbackSecM I q₀ h n c hcn M q (a ⊗ₜ[A] m) =
      (twistedPullbackCohomologyFunctor I 0 (q : ℤ)).map (resSmulHom I n M.1 m)
        ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q).symm
          ((blowupSituationOf I q₀ h).cdiv n q a)) := rfl

omit [IsNoetherianRing A] in
/-- **The `j`-th coordinate of the chosen presentation is `x ↦ x·(the image of the `j`-th basis
vector)`.** Composing the inclusion of the `j`-th summand `A ⧸ Iⁿ ⟶ (A ⧸ Iⁿ)^{⊕r}` with the
presentation's surjection gives `x ↦ P.proj (Pi.single j x)`, and
`Pi.single j x = x · Pi.single j 1`, so `A ⧸ Iⁿ`-linearity of `P.proj` moves the scalar out.

This is the one computation `twistedPullbackSecM_freeSections` rests on; everything else there is
bookkeeping about the two comparison isomorphisms. -/
theorem single_comp_resShortComplex_g (n c : ℕ) {M : ANCModule I n c}
    (P : ANCPresentation I n c M) (j : Fin P.rank) :
    ModuleCat.ofHom (LinearMap.single A (fun _ : Fin P.rank => (A ⧸ I ^ n)) j) ≫
        P.resShortComplex.g =
      resSmulHom I n M.1 (P.proj (Pi.single j 1)) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  have hs : (Pi.single j x : Fin P.rank → A ⧸ I ^ n) = x • Pi.single j (1 : A ⧸ I ^ n) := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp
    · simp [Pi.single_eq_of_ne hk]
  exact (congrArg (fun y => P.proj y) hs).trans (map_smul P.proj x _)

/-- **The field `secM_freeSections` of
`Stacks.LocalCohomology.UniformityIII.TwistedModuleSituation`, on the blowup**: the canonical
map is compatible with the chosen finite free presentation.

Both sides are a sum over the `r` coordinates of the presentation.
`ANCPresentation.freeTensor_apply` writes the left-hand side's argument as
`∑ⱼ vⱼ ⊗ P.proj(eⱼ)`, and `blowupHmodTwistedPullbackPiEquiv_symm_apply` writes the right-hand
side's as `∑ⱼ Hⁱ(X, 𝒪_X(q) ⊗ p^*(single j)~)(vⱼ)`; the two agree coordinatewise by
`single_comp_resShortComplex_g`. -/
theorem twistedPullbackSecM_freeSections (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ)
    (hcn : c ≤ n) (M : ANCModule I n c) (q : ℕ)
    (v : Fin (blowupANCPres I n c M).rank → powQuot I q n) :
    twistedPullbackSecM I q₀ h n c hcn M q ((blowupANCPres I n c M).freeTensor q v) =
      (blowupModuleSituationOf I q₀ h n c hcn).freeToPullback M 0 (q : ℤ)
        (((blowupModuleSituationOf I q₀ h n c hcn).freeIso M 0 q).symm
          fun j => (blowupModuleSituationOf I q₀ h n c hcn).cdiv n q (v j)) := by
  have hfree : ((blowupModuleSituationOf I q₀ h n c hcn).freeIso M 0 q).symm
        (fun j => (blowupModuleSituationOf I q₀ h n c hcn).cdiv n q (v j)) =
      ∑ j : Fin (blowupANCPres I n c M).rank,
        (twistedPullbackCohomologyFunctor I 0 (q : ℤ)).map
          (ModuleCat.ofHom (LinearMap.single A
            (fun _ : Fin (blowupANCPres I n c M).rank => (A ⧸ I ^ n)) j))
          ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q).symm
            ((blowupSituationOf I q₀ h).cdiv n q (v j))) := by
    have hr : ((blowupModuleSituationOf I q₀ h n c hcn).freeIso M 0 q).symm
          (fun j => (blowupModuleSituationOf I q₀ h n c hcn).cdiv n q (v j)) =
        (blowupHmodTwistedPullbackPiEquiv I (ModuleCat.of A (A ⧸ I ^ n))
            (blowupANCPres I n c M).rank 0 (q : ℤ)).symm
          (fun j => (blowupHmodTwistedPullbackQuotientEquiv I n 0 q).symm
            ((blowupSituationOf I q₀ h).cdiv n q (v j))) := rfl
    rw [hr, blowupHmodTwistedPullbackPiEquiv_symm_apply]
  calc twistedPullbackSecM I q₀ h n c hcn M q ((blowupANCPres I n c M).freeTensor q v)
      = ∑ j : Fin (blowupANCPres I n c M).rank, twistedPullbackSecM I q₀ h n c hcn M q
          ((v j ⊗ₜ[A] (blowupANCPres I n c M).proj (Pi.single j 1) :
            powTensor I n q M.1)) := by
        rw [ANCPresentation.freeTensor_apply, map_sum]
    _ = ∑ j : Fin (blowupANCPres I n c M).rank,
          (blowupModuleSituationOf I q₀ h n c hcn).freeToPullback M 0 (q : ℤ)
            ((twistedPullbackCohomologyFunctor I 0 (q : ℤ)).map
              (ModuleCat.ofHom (LinearMap.single A
                (fun _ : Fin (blowupANCPres I n c M).rank => (A ⧸ I ^ n)) j))
              ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q).symm
                ((blowupSituationOf I q₀ h).cdiv n q (v j)))) :=
        Finset.sum_congr rfl fun j _ =>
          ConcreteCategory.congr_hom
            ((congrArg (fun φ : ModuleCat.of A (A ⧸ I ^ n) ⟶ resModule I n M.1 =>
                  (twistedPullbackCohomologyFunctor I 0 (q : ℤ)).map φ)
                (single_comp_resShortComplex_g I n c (blowupANCPres I n c M) j)).symm.trans
              (CategoryTheory.Functor.map_comp (twistedPullbackCohomologyFunctor I 0 (q : ℤ))
                (ModuleCat.ofHom (LinearMap.single A
                  (fun _ : Fin (blowupANCPres I n c M).rank => (A ⧸ I ^ n)) j))
                (blowupANCPres I n c M).resShortComplex.g))
            ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q).symm
              ((blowupSituationOf I q₀ h).cdiv n q (v j)))
    _ = (blowupModuleSituationOf I q₀ h n c hcn).freeToPullback M 0 (q : ℤ)
          (∑ j : Fin (blowupANCPres I n c M).rank,
            (twistedPullbackCohomologyFunctor I 0 (q : ℤ)).map
              (ModuleCat.ofHom (LinearMap.single A
                (fun _ : Fin (blowupANCPres I n c M).rank => (A ⧸ I ^ n)) j))
              ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q).symm
                ((blowupSituationOf I q₀ h).cdiv n q (v j)))) :=
        (map_sum _ _ _).symm
    _ = _ := congrArg _ hfree.symm

end SecM

end Stacks.LocalCohomology.UniformityIII

end
