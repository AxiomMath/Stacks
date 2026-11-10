module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.BigradedFormsZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamDoubleComplex

/-!
# The column `a = 0` of the double complex `K` is the cosimplicial module `M(•)`

The proof of [Stacks, Proposition 60.21.3, Tag 07LG] runs over the double complex

`K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}`,

which
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CosimplicialDeRhamDoubleComplex.lean`
builds as `Crystalline.CosimplicialCompletedPair.doubleComplex` out of a
`Crystalline.CosimplicialCompletedModule` — a cosimplicial module over the completed cosimplicial
rings `D̂(*)` — together with a connection in each cosimplicial degree.  Its two edges are read in
exterior degree zero, and this module identifies one of them: **the column `a = 0` of `K` is the
cosimplicial module `M(•)` itself**, as `Crystalline.CosimplicialCompletedModule.columnZeroIso`.

That is the first half of the hypothesis `hcolumn0` of
`...SmallSite.computes07LG_of_doubleComplex`.  What `hcolumn0` asks for is an identification of the
cohomology of the Moore complex of `K^{0,•}` with the cohomology of
`...SmallSite.sectionsComplex`, the complex `M(0) → M(1) → M(2) → ⋯` of
[Stacks, Proposition 60.20.1, Tag 07JN]; the identification proved here reduces that to the same
statement about `M(•)` itself, where no forms and no completed tensor product appear and the only
remaining content is the crystal property
`...SmallSite.IsCrystalLevelQuotient`.  The reduction is
`Crystalline.CosimplicialCompletedModule.mooreHomologyColumnZeroIso`.

## The two inputs, and the one hypothesis

The algebra of a single cosimplicial degree is
`Crystalline.completedTensorUnitAddEquivOfComplete`: for a module of forms identified with the
ring and a `p`-adically complete module, `M ⊗̂_D Ω ≅ M`.  Its two hypotheses here are

* `Ω^0_{D(b)} ≅ D̂(b)`, which is `Crystalline.CosimplicialDPAlgebra.formsZeroEquiv`; and
* `IsAdicComplete (pAdicIdeal p) (M(b))`, which is **carried**.  It is not a property of the
  bookkeeping: it is the completeness of [Stacks, Tag 07JB], and for the cosimplicial module of
  the crystalline situation it is where `...SmallSite.IsCrystalLevelQuotient` enters, the levels
  of `...SmallSite.wholeSpaceSystem` being `D(n)/(p)^{N+e}`.

What is *not* available before this module is the compatibility of that identification with the
cosimplicial direction, and it needs both halves of the following.

* `Crystalline.CosimplicialDPAlgebra.formsZeroEquiv_formsMap` — **in exterior degree zero the
  transition maps of the forms are the transition maps of the ring**, for every element of the
  completed forms.  `Crystalline.CosimplicialDPAlgebra.formsZeroEquiv_formsMap_of` proves this on
  the `p`-adically dense image of the uncompleted forms only, which does not suffice: an additive
  map out of a completion is not determined by its values on that image.  Both sides are
  composites of completions of maps of the *uncompleted* objects, so
  `Crystalline.adicCompletionMapₛₗ_comp_apply` reduces the identity to the uncompleted
  `Crystalline.mapDifferentialFormsOfDPMorphism_zero`, where it holds for every form.
* `Crystalline.CompletedDeRham.comparisonValues_unitEquiv` — **in exterior degree zero a
  semilinear comparison of completed tensor products is the comparison of the modules**.  This is
  the degree-zero companion of
  `Crystalline.CompletedDeRham.differential_comparisonValues`, and like it is stated over abstract
  rings and forms with the completed comparison passed as a variable plus the equation defining
  it: instantiated directly at the envelopes the nested `AdicCompletion`s unfold during
  unification and the proof does not elaborate within the heartbeat limit.

## Main definitions

* `Crystalline.CosimplicialCompletedModule.carrierCosimplicial` — **the cosimplicial module
  `M(•)` as a cosimplicial abelian group**, in the universe the double complex lives in.
* `Crystalline.CosimplicialCompletedModule.columnZeroEquiv` — **`M(b) ⊗̂_{D(b)} Ω^0_{D(b)} ≅
  M(b)`** in each cosimplicial degree.
* `Crystalline.CosimplicialCompletedModule.columnZeroIso` — **the column `a = 0` of `K` is
  `M(•)`**, as an isomorphism of cosimplicial abelian groups.
* `Crystalline.CosimplicialCompletedModule.mooreHomologyColumnZeroIso` and
  `Crystalline.CosimplicialCompletedPair.mooreHomologyDoubleComplexXZeroIso` — the induced
  identification of the cohomology of the two Moore complexes, which is the shape the hypothesis
  `hcolumn0` of `...SmallSite.computes07LG_of_doubleComplex` is stated in.

## Main results

* `Crystalline.CompletedDeRham.comparisonValues_unitEquiv` — a semilinear comparison of completed
  tensor products in exterior degree zero is the comparison of the modules.
* `Crystalline.CosimplicialDPAlgebra.formsZeroEquiv_formsMap` — in exterior degree zero the
  transition maps of the forms are the transition maps of the ring, on the whole of the completed
  forms.
* `Crystalline.CosimplicialCompletedModule.columnZeroEquiv_tensorMap` — **the identification of
  the degree-zero column is compatible with the cosimplicial direction**, which is what makes it
  an isomorphism of cosimplicial objects rather than a family of isomorphisms.
* `Crystalline.CosimplicialCompletedModule.columnZeroEquiv_of_tmul` — the equation pinning the
  degree-zero identification down: `m ⊗ ω ↦ ω · m`.

## What is and is not proved

**No `@[stacks …]` attribute is placed.**  [Stacks, Tag 07LG] is
`...SmallSite.crystalPairDeRhamComplex_computesCohomology` of
`SmallSite/CrystalDeRhamComputesCohomology.lean`.  Towards the earlier reduction
`...SmallSite.computes07LG_of_doubleComplex`, this module discharges the first half of one of its
five hypotheses, and the other four — the acyclicity of the columns, the rowwise comparison, the
identification of the row `b = 0`, and the kernel clause of the crystal property — are untouched.
Nor does this module construct a `Crystalline.CosimplicialCompletedPair`; for a general crystal one
is `...SmallSite.crystalCosimplicialPair` of `SmallSite/CrystalCosimplicialPair.lean`.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Tag 019I](https://stacks.math.columbia.edu/tag/019I)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology
open DividedPowers
open scoped TensorProduct

universe u v w uD uD' uM uM' uO uO'

namespace Crystalline

/-! ### A semilinear comparison of completed tensor products in exterior degree zero

`Crystalline.CompletedDeRham.differential_comparisonValues` says that a semilinear comparison of
completed de Rham complexes is a chain map.  The cosimplicial direction of the double complex of
[Stacks, Proposition 60.21.3, Tag 07LG] needs one thing more of the comparison in exterior degree
zero: that *through* the identification of the degree-zero term with the module, it is the
comparison of the modules.  This section is that statement.

As there, it is stated over abstract rings and forms, with the comparison passed as a variable
plus the equation defining it.  Instantiated directly at the completed envelopes the nested
`AdicCompletion`s unfold during unification and nothing elaborates within the heartbeat limit. -/

/-- Two factorisations of a semilinear map through adic completions agree on the completion. -/
private theorem adicCompletionMapₛₗ_comp_eq {R S₁ S₂ T P Q₁ Q₂ V : Type*} [CommRing R]
    [CommRing S₁] [CommRing S₂] [CommRing T] [AddCommGroup P] [Module R P] [AddCommGroup Q₁]
    [Module S₁ Q₁] [AddCommGroup Q₂] [Module S₂ Q₂] [AddCommGroup V] [Module T V]
    {σ₁ : R →+* S₁} {σ₂ : R →+* S₂} {τ₁ : S₁ →+* T} {τ₂ : S₂ →+* T} {ρ : R →+* T}
    {I : Ideal R} {J₁ : Ideal S₁} {J₂ : Ideal S₂} {L : Ideal T}
    (g₁ : P →ₛₗ[σ₁] Q₁) (k₁ : Q₁ →ₛₗ[τ₁] V) (g₂ : P →ₛₗ[σ₂] Q₂) (k₂ : Q₂ →ₛₗ[τ₂] V)
    (l : P →ₛₗ[ρ] V) (hg₁ : I.map σ₁ ≤ J₁) (hk₁ : J₁.map τ₁ ≤ L) (hg₂ : I.map σ₂ ≤ J₂)
    (hk₂ : J₂.map τ₂ ≤ L) (hl : I.map ρ ≤ L) (h₁ : ∀ x, l x = k₁ (g₁ x))
    (h₂ : ∀ x, l x = k₂ (g₂ x)) (x : AdicCompletion I P) :
    adicCompletionMapₛₗ k₁ hk₁ (adicCompletionMapₛₗ g₁ hg₁ x) =
      adicCompletionMapₛₗ k₂ hk₂ (adicCompletionMapₛₗ g₂ hg₂ x) :=
  (adicCompletionMapₛₗ_comp_apply g₁ k₁ l hg₁ hk₁ hl h₁ x).symm.trans
    (adicCompletionMapₛₗ_comp_apply g₂ k₂ l hg₂ hk₂ hl h₂ x)

namespace CompletedDeRham

section DegreeZeroComparison

variable (p : ℕ) (D : Type uD) [CommRing D] (D' : Type uD') [CommRing D'] (σ : D →+* D')
  (M : Type uM) [AddCommGroup M] [Module D M]
  (M' : Type uM') [AddCommGroup M'] [Module D' M'] (mu : M →ₛₗ[σ] M')
  (Om : Type uO) [AddCommGroup Om] [Module D Om]
  (Om' : Type uO') [AddCommGroup Om'] [Module D' Om'] (psi : Om →ₛₗ[σ] Om')
  (e : Om ≃ₗ[D] D) (e' : Om' ≃ₗ[D'] D')

/-- The `D`-linear map `M ⊗_D Ω → M`, `m ⊗ ω ↦ e ω · m`, whose `p`-adic completion
`Crystalline.completedTensorUnitEquiv` is. -/
private def unitMap : (M ⊗[D] Om) →ₗ[D] M :=
  ((TensorProduct.congr (LinearEquiv.refl D M) e).trans (TensorProduct.rid D M)).toLinearMap

private theorem unitMap_tmul (m : M) (omega : Om) :
    unitMap D M Om e (m ⊗ₜ[D] omega) = e omega • m := by
  simp [unitMap]

/-- The identification `M ⊗̂_D Ω ≅ M̂` of exterior degree zero, read as the completion of a
semilinear map so that `Crystalline.adicCompletionMapₛₗ_comp_apply` applies to it. -/
private theorem completedTensorUnitEquiv_eq_mapₛₗ (x : CompletedTensor p D Om M) :
    completedTensorUnitEquiv p D Om M e x =
      adicCompletionMapₛₗ (unitMap D M Om e)
        (le_of_eq (Ideal.map_id (pAdicIdeal (A := D) p))) x := by
  rw [completedTensorUnitEquiv, AdicCompletion.congr_apply]
  exact adicCompletionMap_eq_mapₛₗ _ _ x

/-- The image in the completion of the value of the identification of exterior degree zero is the
identification before the completion is undone. -/
private theorem of_completedTensorUnitAddEquivOfComplete
    [IsAdicComplete (pAdicIdeal (A := D) p) M] (x : CompletedTensor p D Om M) :
    AdicCompletion.of (pAdicIdeal (A := D) p) M
        (completedTensorUnitAddEquivOfComplete p D Om M e x) =
      completedTensorUnitEquiv p D Om M e x :=
  (adicCompletionOfAddEquiv p D M).apply_symm_apply _

variable [IsAdicComplete (pAdicIdeal (A := D) p) M] [IsAdicComplete (pAdicIdeal (A := D') p) M']

/-- **In exterior degree zero a semilinear comparison of completed tensor products is the
comparison of the modules.**

The comparison `cmp` is the completion of `m ⊗ ω ↦ μ m ⊗ ψ ω`, passed as a variable with that
equation; `Crystalline.CompletedDeRham.comparisonValues` in exterior degree zero and
`Crystalline.CosimplicialCompletedModule.tensorMap` in exterior degree zero are both of that
shape.  The hypothesis `hpsi` is that `ψ` is the ring map `σ` through the two identifications of
the degree-zero forms with the rings, which for the cosimplicial forms is
`Crystalline.CosimplicialDPAlgebra.formsZeroEquiv_formsMap`.

Both sides are completions of maps out of the uncompleted `M ⊗_D Ω`, and they are the completions
of the same map — on a pure tensor both are `σ (e ω) · μ m` — so the identity holds by
`Crystalline.adicCompletionMapₛₗ_comp_apply`.  The completion is undone at both ends because the
two modules are `p`-adically complete. -/
theorem comparisonValues_unitEquiv
    (cmp : CompletedTensor p D Om M →ₛₗ[σ] CompletedTensor p D' Om' M')
    (hcmp : ∀ x, cmp x =
      adicCompletionMapₛₗ (TensorProduct.map mu psi) (map_pAdicIdeal_le p σ) x)
    (hpsi : ∀ omega : Om, e' (psi omega) = σ (e omega)) (x : CompletedTensor p D Om M) :
    completedTensorUnitAddEquivOfComplete p D' Om' M' e' (cmp x) =
      mu (completedTensorUnitAddEquivOfComplete p D Om M e x) := by
  have hcompose : ∀ y : M ⊗[D] Om,
      (mu.comp (unitMap D M Om e)) y = unitMap D' M' Om' e' (TensorProduct.map mu psi y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul m omega =>
      change mu (unitMap D M Om e (m ⊗ₜ[D] omega)) = _
      rw [unitMap_tmul, TensorProduct.map_tmul, unitMap_tmul, mu.map_smulₛₗ, hpsi]
    | add y z hy hz => simp only [map_add, hy, hz]
  refine (adicCompletionOfAddEquiv p D' M').injective ?_
  change AdicCompletion.of (pAdicIdeal (A := D') p) M'
      (completedTensorUnitAddEquivOfComplete p D' Om' M' e' (cmp x)) =
    AdicCompletion.of (pAdicIdeal (A := D') p) M'
      (mu (completedTensorUnitAddEquivOfComplete p D Om M e x))
  rw [of_completedTensorUnitAddEquivOfComplete,
    ← adicCompletionMapₛₗ_of mu (map_pAdicIdeal_le p σ),
    of_completedTensorUnitAddEquivOfComplete, hcmp,
    completedTensorUnitEquiv_eq_mapₛₗ, completedTensorUnitEquiv_eq_mapₛₗ]
  exact adicCompletionMapₛₗ_comp_eq (TensorProduct.map mu psi) (unitMap D' M' Om' e')
    (unitMap D M Om e) mu (mu.comp (unitMap D M Om e)) (map_pAdicIdeal_le p σ)
    (le_of_eq (Ideal.map_id _)) (le_of_eq (Ideal.map_id _)) (map_pAdicIdeal_le p σ)
    (map_pAdicIdeal_le p σ) hcompose (fun _ => rfl) x

end DegreeZeroComparison

end CompletedDeRham

/-! ### The transition maps of the forms in exterior degree zero, on the whole completion -/

namespace CosimplicialDPAlgebra

variable {A : Type u} [CommRing A] (E : CosimplicialDPAlgebra.{u, v} A) (p : ℕ)

/-- The identification `Ω^0_{D(b)} ≅ D̂(b)`, read as the completion of a semilinear map so that
`Crystalline.adicCompletionMapₛₗ_comp_apply` applies to it. -/
private theorem formsZeroEquiv_eq_mapₛₗ (b : ℕ) (x : E.forms p 0 b) :
    E.formsZeroEquiv p b x =
      adicCompletionMapₛₗ
        (exteriorPower.zeroEquiv (E.carrier b)
          (dividedPowerDifferentials (A := A) (E.dividedPowers b))).toLinearMap
        (le_of_eq (Ideal.map_id (pAdicIdeal (A := E.carrier b) p))) x :=
  adicCompletionMap_eq_mapₛₗ _ _ x

/-- **In exterior degree zero the transition maps of the forms are the transition maps of the
ring**, for every element of the completed forms.

`Crystalline.CosimplicialDPAlgebra.formsZeroEquiv_formsMap_of` proves this on the `p`-adically
dense image of the uncompleted forms, which is not enough to identify the two additive maps.  Both
of them are composites of completions of maps between the *uncompleted* objects, so
`Crystalline.adicCompletionMapₛₗ_comp_apply` reduces the identity to the uncompleted
`Crystalline.mapDifferentialFormsOfDPMorphism_zero`, which holds for every form. -/
theorem formsZeroEquiv_formsMap {m n : SimplexCategory} (phi : m ⟶ n) (omega : E.forms p 0 m.len) :
    E.formsZeroEquiv p n.len (E.formsMap p phi 0 omega) =
      E.completedRingMap p phi (E.formsZeroEquiv p m.len omega) := by
  rw [formsZeroEquiv_eq_mapₛₗ, formsZeroEquiv_eq_mapₛₗ]
  exact adicCompletionMapₛₗ_comp_eq _ _ _ _
    ((ringHomₛₗ (E.map phi).toRingHom).comp
      (exteriorPower.zeroEquiv (E.carrier m.len)
        (dividedPowerDifferentials (A := A) (E.dividedPowers m.len))).toLinearMap)
    _ _ _ _ (map_pAdicIdeal_le p (E.map phi).toRingHom)
    (fun y => (mapDifferentialFormsOfDPMorphism_zero A (E.dividedPowers m.len)
      (E.dividedPowers n.len) (E.map phi) (E.map_isDPMorphism phi) y).symm)
    (fun _ => rfl) omega

end CosimplicialDPAlgebra

/-! ### The column `a = 0` of the double complex -/

namespace CosimplicialCompletedModule

variable {A : Type u} [CommRing A] {E : CosimplicialDPAlgebra.{u, v} A} {p : ℕ}
  (W : CosimplicialCompletedModule.{u, v, w} E p)

/-- The cosimplicial module `M(•)` as a cosimplicial abelian group. -/
def carrierCosimplicialSmall : CosimplicialObject AddCommGrpCat.{w} where
  obj n := AddCommGrpCat.of (W.carrier n.len)
  map phi := AddCommGrpCat.ofHom (W.map phi).toAddMonoidHom
  map_id n := AddCommGrpCat.ext fun x => W.map_id_apply n x
  map_comp phi psi := AddCommGrpCat.ext fun x => W.map_comp_apply phi psi x

/-- **The cosimplicial module `M(•)` as a cosimplicial abelian group**, in the universe the
double complex `K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` lives in: the terms of `K` are completions of
tensor products of a module by a module of forms, so they live one universe-maximum up from the
modules themselves, and the identification of the column `a = 0` with `M(•)` is an identification
of cosimplicial objects of that larger category. -/
def carrierCosimplicial : CosimplicialObject AddCommGrpCat.{max v w} :=
  W.carrierCosimplicialSmall ⋙ AddCommGrpCat.uliftFunctor

variable [∀ b, IsAdicComplete (pAdicIdeal (A := E.completedRing p b) p) (W.carrier b)]

/-- **The degree-`(0, b)` term of the double complex is `M(b)`**:
`M(b) ⊗̂_{D(b)} Ω^0_{D(b)} ≅ M(b)`.

This is `Crystalline.completedTensorUnitAddEquivOfComplete`, whose two hypotheses are
`Crystalline.CosimplicialDPAlgebra.formsZeroEquiv` — the forms in exterior degree zero are the
ring — and the `p`-adic completeness of `M(b)`, which is carried. -/
def columnZeroEquiv (b : ℕ) : W.obj 0 b ≃+ W.carrier b :=
  completedTensorUnitAddEquivOfComplete p (E.completedRing p b) (E.forms p 0 b) (W.carrier b)
    (E.formsZeroEquiv p b)

/-- **The equation pinning the degree-zero identification down**: it carries the image of the
pure tensor `m ⊗ ω` to `ω · m`, the zero-form `ω` read as a scalar.  The pure tensors span the
uncompleted tensor product and their images are `p`-adically dense, so no second additive map
satisfies this. -/
theorem columnZeroEquiv_of_tmul (b : ℕ) (x : W.carrier b) (omega : E.forms p 0 b) :
    W.columnZeroEquiv b (toCompletedTensor p (E.completedRing p b) (E.forms p 0 b)
        (W.carrier b) (x ⊗ₜ[E.completedRing p b] omega)) =
      E.formsZeroEquiv p b omega • x :=
  completedTensorUnitAddEquivOfComplete_of_tmul p (E.completedRing p b) (E.forms p 0 b)
    (W.carrier b) (E.formsZeroEquiv p b) x omega

/-- **The identification of the degree-zero column is compatible with the cosimplicial
direction.**

This is `Crystalline.CompletedDeRham.comparisonValues_unitEquiv`, the degree-zero statement about
a semilinear comparison of completed tensor products, applied to the cosimplicial transition; the
compatibility it asks of the comparison of forms is
`Crystalline.CosimplicialDPAlgebra.formsZeroEquiv_formsMap`. -/
theorem columnZeroEquiv_tensorMap {m n : SimplexCategory} (phi : m ⟶ n) (x : W.obj 0 m.len) :
    W.columnZeroEquiv n.len (W.tensorMap phi 0 x) = W.map phi (W.columnZeroEquiv m.len x) :=
  CompletedDeRham.comparisonValues_unitEquiv p (E.completedRing p m.len)
    (E.completedRing p n.len) (E.completedRingMap p phi) (W.carrier m.len) (W.carrier n.len)
    (W.map phi) (E.forms p 0 m.len) (E.forms p 0 n.len) (E.formsMapCompleted p phi 0)
    (E.formsZeroEquiv p m.len) (E.formsZeroEquiv p n.len) (W.tensorMap phi 0) (fun _ => rfl)
    (fun omega => E.formsZeroEquiv_formsMap p phi omega) x

/-- **The column `a = 0` of the double complex is the cosimplicial module `M(•)`.**

In each cosimplicial degree this is `Crystalline.CosimplicialCompletedModule.columnZeroEquiv`, and
that it is an isomorphism of cosimplicial objects and not merely a family of isomorphisms is
`Crystalline.CosimplicialCompletedModule.columnZeroEquiv_tensorMap`. -/
def columnZeroIso : W.column 0 ≅ W.carrierCosimplicial :=
  NatIso.ofComponents
    (fun n => AddEquiv.toAddCommGrpIso ((W.columnZeroEquiv n.len).trans AddEquiv.ulift.symm))
    (fun {_ _} phi => AddCommGrpCat.ext fun x =>
      ULift.ext (W.columnZeroEquiv_tensorMap phi x))

/-- **The cohomology of the Moore complex of the column `a = 0` of the double complex is the
cohomology of the Moore complex of `M(•)`.**

This is the shape the hypothesis `hcolumn0` of `...SmallSite.computes07LG_of_doubleComplex` is
stated in: what that hypothesis still asks for, after this identification, is the comparison of
the Moore complex of `M(•)` with `...SmallSite.sectionsComplex`, which carries no forms and no
completed tensor product and is where `...SmallSite.IsCrystalLevelQuotient` enters. -/
def mooreHomologyColumnZeroIso (j : ℕ) :
    ((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj (W.column 0)).homology j ≅
      ((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj
        W.carrierCosimplicial).homology j :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{max v w} (ComplexShape.up ℕ) j).mapIso
    ((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).mapIso W.columnZeroIso)

end CosimplicialCompletedModule

namespace CosimplicialCompletedPair

variable {A : Type u} [CommRing A] {E : CosimplicialDPAlgebra.{u, v} A} {p : ℕ}
  (W : CosimplicialCompletedPair.{u, v, w} E p)
  [∀ b, IsAdicComplete (pAdicIdeal (A := E.completedRing p b) p) (W.carrier b)]

/-- **The exterior degree zero of the double complex `K` is the cosimplicial module `M(•)`.** -/
def doubleComplexXZeroIso :
    W.doubleComplex.X 0 ≅ W.toCosimplicialCompletedModule.carrierCosimplicial :=
  W.toCosimplicialCompletedModule.columnZeroIso

/-- **The cohomology of the Moore complex of the exterior degree zero of `K` is the cohomology of
the Moore complex of `M(•)`**, which is the first half of the hypothesis `hcolumn0` of
`...SmallSite.computes07LG_of_doubleComplex`. -/
def mooreHomologyDoubleComplexXZeroIso (j : ℕ) :
    ((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj
        (W.doubleComplex.X 0)).homology j ≅
      ((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj
        W.toCosimplicialCompletedModule.carrierCosimplicial).homology j :=
  W.toCosimplicialCompletedModule.mooreHomologyColumnZeroIso j

end CosimplicialCompletedPair

end Crystalline

end
