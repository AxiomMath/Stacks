module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.H1Vanishing
public import StacksFrontier.RingTheory.Descent.AmitsurComplex

/-!
# The Čech complex of a single covering morphism, and the Amitsur complex

Let `h : W ⟶ U` be a morphism of a site, let `V` be a double self-product of `W` over `U` with
projections `q₁, q₂ : V ⟶ W`, and let `V₃` be a triple one with the three projections
`t₁₂, t₁₃, t₂₃ : V₃ ⟶ V` onto the double products.  The alternating sums of the restriction maps
along these arrows are the first two differentials of the Čech complex of the one-element
covering `{h}` with values in a presheaf of modules, and this file identifies that complex with
the Amitsur complex of `Module.Descent` and transports the exactness of the latter back to
sections.

The identification is taken as data, in the shape the identification actually comes in: three
maps from the terms `B ⊗[A] M`, `B ⊗[A] (B ⊗[A] M)` and `B ⊗[A] (B ⊗[A] (B ⊗[A] M))` of the
Amitsur complex of an `A`-module `M` along `A → B` to the sections of the presheaf over `W`, `V`
and `V₃`, together with the two equations saying that the Čech differentials correspond to the
Amitsur differentials.  Those two equations are the whole content of the identification: over an
affine object with ring `A`, covered by an affine object with ring `B`, the double and triple
products have rings `B ⊗[A] B` and `B ⊗[A] B ⊗[A] B`, the first projection of the double product
is `b ⊗ₜ m ↦ b ⊗ₜ (1 ⊗ₜ m)` and the second is `x ↦ 1 ⊗ₜ x`, so their difference is
`Module.Descent.amitsurDiff₀`, and likewise the three projections of the triple product insert a
`1` into the three slots, so their alternating sum is `Module.Descent.amitsurDiff₁`.

Nothing here assumes that the presheaf of modules is a sheaf, that `U`, `W`, `V` and `V₃` are
affine, or that `{h}` is a covering.  What the results below do with the identification is
exactly what the Amitsur complex supplies: in degree zero, that a section over `W` on which the
two projections agree is the restriction of a section over `U`, which is the sheaf condition for
the one-element covering; and in degree one, that a `1`-cocycle over `V` is the Čech coboundary
of a section over `W`, which is the vanishing of the first Čech cohomology of the covering.  Both
are stated in element form and as the surjectivity of a map of sections onto the cocycles.

The last result is the passage from the first Čech cohomology to the descent of sections.  A
section of the target of a morphism `b` which lifts over `W` gives a `1`-cocycle with values in
the kernel of `b`, namely the Čech coboundary of the lift; a `1`-cocycle of the kernel which is a
coboundary corrects the lift to one that descends; and the lift that descends has an image over
`U` which agrees with the given section after restriction, hence agrees with it.  So the
vanishing of the first Čech cohomology **of the kernel** of `b`, and not of its source, is what
makes `b` surjective on sections.

## Main definitions

* `PresheafOfModules.cechDiff₀`: the Čech differential `P.obj (op W) →+ P.obj (op V)`, the
  difference of the restrictions along the two projections.
* `PresheafOfModules.cechDiff₁`: the Čech differential `P.obj (op V) →+ P.obj (op V₃)`, the
  alternating sum of the restrictions along the three projections.
* `PresheafOfModules.toCechCocycleZero` and `PresheafOfModules.toCechCocycleOne`: restriction
  along `h`, and the degree-zero Čech differential, viewed as maps into the Čech cocycles.
* `Module.Descent.amitsurInsert₁`, `Module.Descent.amitsurInsert₂` and
  `Module.Descent.amitsurInsert₃`: the three ring maps `B ⊗[A] B → B ⊗[A] B ⊗[A] B` of the
  projections of a triple self-product onto a double one, each inserting a `1` into one slot.
* `Module.Descent.amitsurTripleAssoc`: the comparison between the degree-two term of the Amitsur
  complex and its spelling as a base change of `M` along the ring of a triple self-product.
* `Module.Descent.finsuppBaseChange` and `Module.Descent.directSumBaseChange`: the base change
  along `A → B` of a free `A`-module on an index type, in the finitely supported and the direct
  sum spelling.

## Main results

* `PresheafOfModules.cechDiff₁_cechDiff₀_apply`: the Čech complex is a complex.
* `PresheafOfModules.cechDiff₁_cechDiff₀_apply_of_amitsurDiff`: the same conclusion from the
  identification instead of from the equations between the arrows, which checks that the signs
  and the index order of the identification match those of the Amitsur differentials.
* `PresheafOfModules.exists_restrictₛₗ_eq_of_cechDiff₀_eq_zero` and
  `PresheafOfModules.surjective_toCechCocycleZero`: **the sheaf condition for a one-element
  covering**, from degree-zero exactness of the Amitsur complex.
* `PresheafOfModules.exists_cechDiff₀_eq` and
  `PresheafOfModules.surjective_toCechCocycleOne`: **the vanishing of the first Čech cohomology
  of a one-element covering**, from degree-one exactness of the Amitsur complex.
* `PresheafOfModules.exact_cechDiff`: the same vanishing together with the complex property, as
  exactness of the two Čech differentials.
* `SheafOfModules.detectsRange_of_cechH1Vanishing`: **a morphism whose kernel has vanishing
  first Čech cohomology along a covering morphism has its images detected by that morphism.**
* `Module.Descent.amitsurDiff₀_eq_assoc_rTensor` and `Module.Descent.amitsurDiff₁_comp_assoc`:
  the two Amitsur differentials as base changes of maps between the rings of the self-products,
  which is the whole of the slot bookkeeping of the identification in two statements.
* `PresheafOfModules.cechDiff₀_eq_amitsurDiff₀` and
  `PresheafOfModules.cechDiff₁_eq_amitsurDiff₁`: the identification hypotheses `hd₀` and `hd₁`
  assembled from one description per projection, which is the form in which a consumer has them.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe u v r m

namespace Module.Descent

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
variable (M : Type*) [AddCommGroup M] [Module A M]

/-- The ring map of the projection of a triple self-product onto its last two factors,
`x ↦ 1 ⊗ₜ x`: it inserts a `1` into the first slot. -/
noncomputable abbrev amitsurInsert₁ : B ⊗[A] B →ₗ[A] B ⊗[A] (B ⊗[A] B) :=
  (Algebra.TensorProduct.includeRight : (B ⊗[A] B) →ₐ[A] B ⊗[A] (B ⊗[A] B)).toLinearMap

/-- The ring map of the projection of a triple self-product onto its outer two factors,
`s ⊗ₜ t ↦ s ⊗ₜ (1 ⊗ₜ t)`: it inserts a `1` into the second slot. -/
noncomputable abbrev amitsurInsert₂ : B ⊗[A] B →ₗ[A] B ⊗[A] (B ⊗[A] B) :=
  LinearMap.lTensor B (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toLinearMap

/-- The ring map of the projection of a triple self-product onto its first two factors,
`s ⊗ₜ t ↦ s ⊗ₜ (t ⊗ₜ 1)`: it inserts a `1` into the third slot. -/
noncomputable abbrev amitsurInsert₃ : B ⊗[A] B →ₗ[A] B ⊗[A] (B ⊗[A] B) :=
  LinearMap.lTensor B (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toLinearMap

/-- The identification of the degree-two term of the Amitsur complex with its spelling as a base
change of `M` along `A → B ⊗[A] B ⊗[A] B`, which is the ring of a triple self-product. -/
noncomputable def amitsurTripleAssoc :
    (B ⊗[A] (B ⊗[A] B)) ⊗[A] M ≃ₗ[A] B ⊗[A] (B ⊗[A] (B ⊗[A] M)) :=
  TensorProduct.assoc A B (B ⊗[A] B) M ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl A B) (TensorProduct.assoc A B B M)

/-- **The degree-zero Amitsur differential is the base change of
`Algebra.TensorProduct.includeLeftSubRight`.**  In the spelling in which the sections of a
quasi-coherent module over a double self-product are a base change of `M` along
`A → B ⊗[A] B`, the two projections induce base change along `Algebra.TensorProduct.includeLeft`
and `Algebra.TensorProduct.includeRight`, so their difference induces base change along
`Algebra.TensorProduct.includeLeftSubRight`, the map degree-zero Amitsur exactness is itself
stated against. -/
theorem amitsurDiff₀_eq_assoc_rTensor :
    amitsurDiff₀ A B M = (TensorProduct.assoc A B B M).toLinearMap ∘ₗ
      LinearMap.rTensor M (Algebra.TensorProduct.includeLeftSubRight A B) := by
  ext b m
  simp [TensorProduct.sub_tmul]

/-- `Algebra.TensorProduct.includeLeftSubRight` base changed, as the difference of the base
changes of `Algebra.TensorProduct.includeLeft` and `Algebra.TensorProduct.includeRight`. -/
theorem rTensor_includeLeftSubRight :
    LinearMap.rTensor M (Algebra.TensorProduct.includeLeftSubRight A B) =
      LinearMap.rTensor M
          (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toLinearMap -
        LinearMap.rTensor M
          (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toLinearMap := by
  ext b m
  simp [TensorProduct.sub_tmul]

/-- **The degree-one Amitsur differential is the alternating sum of the base changes of the three
slot insertions.**  This is the whole of the slot bookkeeping of the triple self-product, in one
statement: the three projections `t₂₃`, `t₁₃`, `t₁₂` of a triple self-product onto a double one
induce base change along `Module.Descent.amitsurInsert₁`, `Module.Descent.amitsurInsert₂` and
`Module.Descent.amitsurInsert₃` respectively, and the alternating sum of those is
`Module.Descent.amitsurDiff₁` read through
`Module.Descent.amitsurTripleAssoc` and `TensorProduct.assoc`. -/
theorem amitsurDiff₁_comp_assoc :
    amitsurDiff₁ A B M ∘ₗ (TensorProduct.assoc A B B M).toLinearMap =
      (amitsurTripleAssoc A B M).toLinearMap ∘ₗ
            LinearMap.rTensor M (amitsurInsert₁ A B) -
          (amitsurTripleAssoc A B M).toLinearMap ∘ₗ
            LinearMap.rTensor M (amitsurInsert₂ A B) +
        (amitsurTripleAssoc A B M).toLinearMap ∘ₗ
          LinearMap.rTensor M (amitsurInsert₃ A B) := by
  ext s t m
  simp [amitsurTripleAssoc]

section Coproduct

variable (I : Type*) [DecidableEq I]

/-- **The index-shape adapter for a coproduct of copies of the structure sheaf**, in the
finitely supported spelling: the base change along `A → B` of the free `A`-module on `I` is the
free `B`-module on `I`.  It is `TensorProduct.finsuppScalarRight` at the module `B`, named here
because it is what the identification hypotheses of this file need from the affine
coproduct-sections lemma and nothing in the Mathlib name says so. -/
noncomputable def finsuppBaseChange : B ⊗[A] (I →₀ A) ≃ₗ[B] (I →₀ B) :=
  TensorProduct.finsuppScalarRight A B B I

/-- `Module.Descent.finsuppBaseChange` on a pure tensor, coordinatewise. -/
@[simp]
lemma finsuppBaseChange_tmul_apply (b : B) (p : I →₀ A) (i : I) :
    finsuppBaseChange A B I (b ⊗ₜ[A] p) i = p i • b := by
  simp [finsuppBaseChange]

/-- **The index-shape adapter for a coproduct of copies of the structure sheaf**, in the direct
sum spelling: the base change along `A → B` of a direct sum of copies of `A` indexed by `I` is
the direct sum of copies of `B`.  A coproduct in a category of modules is a direct sum, so this
is the spelling in which the sections of a coproduct of copies of the structure sheaf arrive;
it differs from `Module.Descent.finsuppBaseChange` only by
`Finsupp.finsuppLEquivDirectSum` on each side. -/
noncomputable def directSumBaseChange :
    B ⊗[A] (DirectSum I fun _ : I => A) ≃ₗ[B] DirectSum I fun _ : I => B :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (finsuppLEquivDirectSum A A I).symm ≪≫ₗ
    finsuppBaseChange A B I ≪≫ₗ finsuppLEquivDirectSum B B I

end Coproduct

end Module.Descent

namespace PresheafOfModules

section Cech

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{r}} (P : PresheafOfModules.{m} R)

/-- Restriction along a composite is the composite of the restrictions.  This is
`PresheafOfModules.map_comp_apply` for arrows of `C` rather than of `Cᵒᵖ`, and in the
`PresheafOfModules.restrictₛₗ` spelling the submodule lemmas apply to.

Named with the `_op` suffix because `PresheafOfModules.restrictₛₗ_restrictₛₗ` already exists
for arrows of `Cᵒᵖ` with the module universe pinned to the ring universe, which this form is
not; the two are different statements, not duplicates. -/
lemma restrictₛₗ_restrictₛₗ_op {U W V : C} (a : V ⟶ W) (g : W ⟶ U) (x : P.obj (op U)) :
    P.restrictₛₗ a.op (P.restrictₛₗ g.op x) = P.restrictₛₗ (a ≫ g).op x := by
  simp only [restrictₛₗ_apply, op_comp]
  exact (P.map_comp_apply g.op a.op x).symm

/-- The degree-zero differential of the Čech complex of the one-element covering `{W ⟶ U}` with
values in `P`: the difference of the restrictions along the two projections `q₁, q₂ : V ⟶ W` of a
double self-product of `W` over `U`.

It is only additive, not semilinear: the two restrictions are semilinear along the two different
ring maps `R.map q₁.op` and `R.map q₂.op`. -/
noncomputable def cechDiff₀ {W V : C} (q₁ q₂ : V ⟶ W) : P.obj (op W) →+ P.obj (op V) :=
  (P.restrictₛₗ q₁.op).toAddMonoidHom - (P.restrictₛₗ q₂.op).toAddMonoidHom

/-- `PresheafOfModules.cechDiff₀` on a section. -/
lemma cechDiff₀_apply {W V : C} (q₁ q₂ : V ⟶ W) (p : P.obj (op W)) :
    P.cechDiff₀ q₁ q₂ p = P.restrictₛₗ q₁.op p - P.restrictₛₗ q₂.op p := rfl

/-- The degree-one differential of the Čech complex of the one-element covering `{W ⟶ U}` with
values in `P`: the alternating sum of the restrictions along the three projections
`t₁₂, t₁₃, t₂₃ : V₃ ⟶ V` of a triple self-product of `W` over `U` onto a double one. -/
noncomputable def cechDiff₁ {V V₃ : C} (t₁₂ t₁₃ t₂₃ : V₃ ⟶ V) : P.obj (op V) →+ P.obj (op V₃) :=
  (P.restrictₛₗ t₂₃.op).toAddMonoidHom - (P.restrictₛₗ t₁₃.op).toAddMonoidHom +
    (P.restrictₛₗ t₁₂.op).toAddMonoidHom

/-- `PresheafOfModules.cechDiff₁` on a section. -/
lemma cechDiff₁_apply {V V₃ : C} (t₁₂ t₁₃ t₂₃ : V₃ ⟶ V) (x : P.obj (op V)) :
    P.cechDiff₁ t₁₂ t₁₃ t₂₃ x =
      P.restrictₛₗ t₂₃.op x - P.restrictₛₗ t₁₃.op x + P.restrictₛₗ t₁₂.op x := rfl

/-- The degree-zero Čech differential kills the restrictions from the base: the two projections
of a double self-product agree after composing with the covering morphism. -/
lemma cechDiff₀_restrictₛₗ {U W V : C} (h : W ⟶ U) (q₁ q₂ : V ⟶ W) (hq : q₁ ≫ h = q₂ ≫ h)
    (n : P.obj (op U)) : P.cechDiff₀ q₁ q₂ (P.restrictₛₗ h.op n) = 0 := by
  rw [cechDiff₀_apply, P.restrictₛₗ_restrictₛₗ_op, P.restrictₛₗ_restrictₛₗ_op, hq, sub_self]

/-- Restriction along a double projection carries the degree-zero Čech differential to the
difference of the restrictions along the two composites. -/
lemma restrictₛₗ_cechDiff₀ {W V V₃ : C} (q₁ q₂ : V ⟶ W) (t : V₃ ⟶ V) (p : P.obj (op W)) :
    P.restrictₛₗ t.op (P.cechDiff₀ q₁ q₂ p) =
      P.restrictₛₗ (t ≫ q₁).op p - P.restrictₛₗ (t ≫ q₂).op p := by
  rw [cechDiff₀_apply, map_sub, P.restrictₛₗ_restrictₛₗ_op, P.restrictₛₗ_restrictₛₗ_op]

/-- **The Čech complex is a complex.**  The three equations are the identifications of the three
projections of a triple self-product onto `W`: `t₁₂ ≫ q₁` and `t₁₃ ≫ q₁` are both the first,
`t₁₂ ≫ q₂` and `t₂₃ ≫ q₁` are both the second, and `t₁₃ ≫ q₂` and `t₂₃ ≫ q₂` are both the
third. -/
lemma cechDiff₁_cechDiff₀_apply {W V V₃ : C} (q₁ q₂ : V ⟶ W) (t₁₂ t₁₃ t₂₃ : V₃ ⟶ V)
    (hq₁ : t₁₂ ≫ q₁ = t₁₃ ≫ q₁) (hq₂ : t₁₂ ≫ q₂ = t₂₃ ≫ q₁) (hq₃ : t₁₃ ≫ q₂ = t₂₃ ≫ q₂)
    (p : P.obj (op W)) : P.cechDiff₁ t₁₂ t₁₃ t₂₃ (P.cechDiff₀ q₁ q₂ p) = 0 := by
  rw [cechDiff₁_apply, P.restrictₛₗ_cechDiff₀, P.restrictₛₗ_cechDiff₀, P.restrictₛₗ_cechDiff₀,
    ← hq₁, ← hq₂, ← hq₃]
  abel

/-- Restriction along the covering morphism, viewed as a map into the degree-zero Čech
cocycles. -/
noncomputable def toCechCocycleZero {U W V : C} (h : W ⟶ U) (q₁ q₂ : V ⟶ W)
    (hq : q₁ ≫ h = q₂ ≫ h) : P.obj (op U) →+ (P.cechDiff₀ q₁ q₂).ker :=
  AddMonoidHom.codRestrict (P.restrictₛₗ h.op).toAddMonoidHom _ fun n =>
    AddMonoidHom.mem_ker.2 (P.cechDiff₀_restrictₛₗ h q₁ q₂ hq n)

/-- `PresheafOfModules.toCechCocycleZero` followed by the inclusion of the cocycles. -/
lemma coe_toCechCocycleZero {U W V : C} (h : W ⟶ U) (q₁ q₂ : V ⟶ W) (hq : q₁ ≫ h = q₂ ≫ h)
    (n : P.obj (op U)) :
    (P.toCechCocycleZero h q₁ q₂ hq n : P.obj (op W)) = P.restrictₛₗ h.op n := rfl

/-- The degree-zero Čech differential, viewed as a map into the degree-one Čech cocycles. -/
noncomputable def toCechCocycleOne {W V V₃ : C} (q₁ q₂ : V ⟶ W) (t₁₂ t₁₃ t₂₃ : V₃ ⟶ V)
    (hq₁ : t₁₂ ≫ q₁ = t₁₃ ≫ q₁) (hq₂ : t₁₂ ≫ q₂ = t₂₃ ≫ q₁) (hq₃ : t₁₃ ≫ q₂ = t₂₃ ≫ q₂) :
    P.obj (op W) →+ (P.cechDiff₁ t₁₂ t₁₃ t₂₃).ker :=
  AddMonoidHom.codRestrict (P.cechDiff₀ q₁ q₂) _ fun p =>
    AddMonoidHom.mem_ker.2 (P.cechDiff₁_cechDiff₀_apply q₁ q₂ t₁₂ t₁₃ t₂₃ hq₁ hq₂ hq₃ p)

/-- `PresheafOfModules.toCechCocycleOne` followed by the inclusion of the cocycles. -/
lemma coe_toCechCocycleOne {W V V₃ : C} (q₁ q₂ : V ⟶ W) (t₁₂ t₁₃ t₂₃ : V₃ ⟶ V)
    (hq₁ : t₁₂ ≫ q₁ = t₁₃ ≫ q₁) (hq₂ : t₁₂ ≫ q₂ = t₂₃ ≫ q₁) (hq₃ : t₁₃ ≫ q₂ = t₂₃ ≫ q₂)
    (p : P.obj (op W)) :
    (P.toCechCocycleOne q₁ q₂ t₁₂ t₁₃ t₂₃ hq₁ hq₂ hq₃ p : P.obj (op V)) =
      P.cechDiff₀ q₁ q₂ p := rfl

end Cech

section Amitsur

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{r}} (P : PresheafOfModules.{m} R)
variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
variable (M : Type*) [AddCommGroup M] [Module A M]

omit [Module.FaithfullyFlat A B] in
/-- **The degree-zero identification, from the two projections taken separately.**  A consumer
does not have the Čech differential identified with `Module.Descent.amitsurDiff₀`; it has one
description per projection, each saying that restriction along that projection is base change of
the sections along the corresponding ring map of a double self-product.  This lemma assembles the
two into the `hd₀` hypothesis of the results below, so that the slot bookkeeping is done once.

`e₂` identifies the sections over the double self-product with the base change of `M` along
`A → B ⊗[A] B`, which is the ring of that object, and `he` is the associativity comparison between
that spelling and the iterated one the Amitsur complex is written in.  The two projections induce
base change along `Algebra.TensorProduct.includeLeft` and `Algebra.TensorProduct.includeRight`. -/
lemma cechDiff₀_eq_amitsurDiff₀ {W V : C} (q₁ q₂ : V ⟶ W)
    (eW : B ⊗[A] M →+ P.obj (op W)) (eV : B ⊗[A] (B ⊗[A] M) →+ P.obj (op V))
    (e₂ : (B ⊗[A] B) ⊗[A] M →+ P.obj (op V))
    (he : ∀ y, eV (TensorProduct.assoc A B B M y) = e₂ y)
    (h₁ : ∀ y, P.restrictₛₗ q₁.op (eW y) =
      e₂ (LinearMap.rTensor M
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toLinearMap y))
    (h₂ : ∀ y, P.restrictₛₗ q₂.op (eW y) =
      e₂ (LinearMap.rTensor M
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toLinearMap y))
    (x : B ⊗[A] M) :
    P.cechDiff₀ q₁ q₂ (eW x) = eV (Module.Descent.amitsurDiff₀ A B M x) := by
  have hr := congr($(Module.Descent.rTensor_includeLeftSubRight A B M) x)
  rw [LinearMap.sub_apply] at hr
  rw [cechDiff₀_apply, h₁, h₂, ← map_sub, ← hr,
    Module.Descent.amitsurDiff₀_eq_assoc_rTensor, LinearMap.comp_apply, LinearEquiv.coe_coe, he]

omit [Module.FaithfullyFlat A B] in
/-- **The degree-one identification, from the three projections taken separately.**  The
companion of `PresheafOfModules.cechDiff₀_eq_amitsurDiff₀` one degree up, and the place where a
slot error is least visible: `e₃` identifies the sections over the triple self-product with the
base change of `M` along `A → B ⊗[A] B ⊗[A] B`, `he₃` is the associativity comparison, and the
three projections onto the double self-product induce base change along
`Module.Descent.amitsurInsert₁`, `Module.Descent.amitsurInsert₂` and
`Module.Descent.amitsurInsert₃`, which insert a `1` into the first, second and third slot. -/
lemma cechDiff₁_eq_amitsurDiff₁ {V V₃ : C} (t₁₂ t₁₃ t₂₃ : V₃ ⟶ V)
    (eV : B ⊗[A] (B ⊗[A] M) →+ P.obj (op V))
    (eV₃ : B ⊗[A] (B ⊗[A] (B ⊗[A] M)) →+ P.obj (op V₃))
    (e₂ : (B ⊗[A] B) ⊗[A] M →+ P.obj (op V))
    (e₃ : (B ⊗[A] (B ⊗[A] B)) ⊗[A] M →+ P.obj (op V₃))
    (he : ∀ y, eV (TensorProduct.assoc A B B M y) = e₂ y)
    (he₃ : ∀ y, eV₃ (Module.Descent.amitsurTripleAssoc A B M y) = e₃ y)
    (h₂₃ : ∀ y, P.restrictₛₗ t₂₃.op (e₂ y) =
      e₃ (LinearMap.rTensor M (Module.Descent.amitsurInsert₁ A B) y))
    (h₁₃ : ∀ y, P.restrictₛₗ t₁₃.op (e₂ y) =
      e₃ (LinearMap.rTensor M (Module.Descent.amitsurInsert₂ A B) y))
    (h₁₂ : ∀ y, P.restrictₛₗ t₁₂.op (e₂ y) =
      e₃ (LinearMap.rTensor M (Module.Descent.amitsurInsert₃ A B) y))
    (x : B ⊗[A] (B ⊗[A] M)) :
    P.cechDiff₁ t₁₂ t₁₃ t₂₃ (eV x) = eV₃ (Module.Descent.amitsurDiff₁ A B M x) := by
  obtain ⟨y, rfl⟩ := (TensorProduct.assoc A B B M).surjective x
  have hd := congr($(Module.Descent.amitsurDiff₁_comp_assoc A B M) y)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.add_apply,
    LinearMap.sub_apply] at hd
  rw [cechDiff₁_apply, he, h₂₃, h₁₃, h₁₂, hd, map_add, map_sub, he₃, he₃, he₃]

/-- **The sheaf condition for a one-element covering**, from degree-zero exactness of the Amitsur
complex.  Let the sections of `P` over the base be a quotient of `M`, those over `W` a quotient of
`B ⊗[A] M` and those over the double self-product `V` an extension of `B ⊗[A] (B ⊗[A] M)`, in such
a way that restriction along `h` is the augmentation `m ↦ 1 ⊗ₜ m` and the degree-zero Čech
differential is `Module.Descent.amitsurDiff₀`.  Then a section over `W` on which the two
projections agree is the restriction of a section over the base.

Only surjectivity of `eW` and injectivity of `eV` are used; `eU` need not be either. -/
theorem exists_restrictₛₗ_eq_of_cechDiff₀_eq_zero {U W V : C} (h : W ⟶ U) (q₁ q₂ : V ⟶ W)
    (eU : M →+ P.obj (op U)) (eW : B ⊗[A] M →+ P.obj (op W))
    (eV : B ⊗[A] (B ⊗[A] M) →+ P.obj (op V))
    (heW : Function.Surjective eW) (heV : Function.Injective eV)
    (haug : ∀ m, P.restrictₛₗ h.op (eU m) = eW (Module.Descent.amitsurAug A B M m))
    (hd₀ : ∀ x, P.cechDiff₀ q₁ q₂ (eW x) = eV (Module.Descent.amitsurDiff₀ A B M x))
    {x : P.obj (op W)} (hx : P.cechDiff₀ q₁ q₂ x = 0) :
    ∃ n : P.obj (op U), P.restrictₛₗ h.op n = x := by
  obtain ⟨y, rfl⟩ := heW x
  have hy : Module.Descent.amitsurDiff₀ A B M y = 0 := heV (by rw [← hd₀, hx, map_zero])
  obtain ⟨mm, hm⟩ := (Module.Descent.exact_amitsur_degree_zero A B M y).1 hy
  exact ⟨eU mm, by rw [haug, hm]⟩

/-- **The sheaf condition for a one-element covering**, as the surjectivity of restriction onto
the degree-zero Čech cocycles.  This is
`PresheafOfModules.exists_restrictₛₗ_eq_of_cechDiff₀_eq_zero` in the shape a consumer which needs
a map of sections to be surjective uses. -/
theorem surjective_toCechCocycleZero {U W V : C} (h : W ⟶ U) (q₁ q₂ : V ⟶ W)
    (hq : q₁ ≫ h = q₂ ≫ h)
    (eU : M →+ P.obj (op U)) (eW : B ⊗[A] M →+ P.obj (op W))
    (eV : B ⊗[A] (B ⊗[A] M) →+ P.obj (op V))
    (heW : Function.Surjective eW) (heV : Function.Injective eV)
    (haug : ∀ m, P.restrictₛₗ h.op (eU m) = eW (Module.Descent.amitsurAug A B M m))
    (hd₀ : ∀ x, P.cechDiff₀ q₁ q₂ (eW x) = eV (Module.Descent.amitsurDiff₀ A B M x)) :
    Function.Surjective (P.toCechCocycleZero h q₁ q₂ hq) := fun x =>
  (P.exists_restrictₛₗ_eq_of_cechDiff₀_eq_zero A B M h q₁ q₂ eU eW eV heW heV haug hd₀
    (AddMonoidHom.mem_ker.1 x.2)).imp fun _ hn => Subtype.ext hn

omit [Module.FaithfullyFlat A B] in
/-- **The identification forces the Čech complex to be a complex**, with no hypothesis on the
arrows.  This is a consistency check on the signs and the index order of the identification: the
composite of the two Čech differentials is the composite of the two Amitsur differentials read
through the identification, and that composite vanishes by
`Module.Descent.amitsurDiff₁_comp_amitsurDiff₀`.  So the three equations between the arrows which
`PresheafOfModules.cechDiff₁_cechDiff₀_apply` asks for are not an extra assumption beyond the
identification; were the alternating signs or the order of the three projections of the triple
self-product not matched to those of `Module.Descent.amitsurDiff₁`, the two routes to this
statement would disagree. -/
lemma cechDiff₁_cechDiff₀_apply_of_amitsurDiff {W V V₃ : C} (q₁ q₂ : V ⟶ W)
    (t₁₂ t₁₃ t₂₃ : V₃ ⟶ V)
    (eW : B ⊗[A] M →+ P.obj (op W)) (eV : B ⊗[A] (B ⊗[A] M) →+ P.obj (op V))
    (eV₃ : B ⊗[A] (B ⊗[A] (B ⊗[A] M)) →+ P.obj (op V₃))
    (heW : Function.Surjective eW)
    (hd₀ : ∀ x, P.cechDiff₀ q₁ q₂ (eW x) = eV (Module.Descent.amitsurDiff₀ A B M x))
    (hd₁ : ∀ x, P.cechDiff₁ t₁₂ t₁₃ t₂₃ (eV x) = eV₃ (Module.Descent.amitsurDiff₁ A B M x))
    (p : P.obj (op W)) : P.cechDiff₁ t₁₂ t₁₃ t₂₃ (P.cechDiff₀ q₁ q₂ p) = 0 := by
  obtain ⟨y, rfl⟩ := heW p
  rw [hd₀, hd₁, ← LinearMap.comp_apply, Module.Descent.amitsurDiff₁_comp_amitsurDiff₀,
    LinearMap.zero_apply, map_zero]

/-- **The vanishing of the first Čech cohomology of a one-element covering**, from degree-one
exactness of the Amitsur complex.  This result is *not* on the critical path of Stacks 06WN, and
the reason is worth stating so that it is not re-derived: making a presenting morphism
`b : P ⟶ N` surjective on sections over the base needs the first Čech cohomology of the **kernel**
of `b` to vanish, not that of `P`, as `SheafOfModules.detectsRange_of_cechH1Vanishing` shows.
Applied to `P` itself the vanishing returns the obstruction cocycle in the form it was already
given, since that cocycle is by construction a degree-zero Čech coboundary in `P`; and the kernel
of a morphism out of a coproduct of copies of the structure sheaf is not again such a coproduct,
so the vanishing does not propagate to it.  What does make a presenting morphism surjective on
sections over an affine object is the degree-**zero** statement
`PresheafOfModules.exists_restrictₛₗ_eq_of_cechDiff₀_eq_zero`: it exhibits the presheaf cokernel
of a presentation as a sheaf, and a presheaf cokernel is surjective on sections by construction.

Let the sections of `P` over `W` be a quotient of `B ⊗[A] M`,
those over the double self-product `V` a quotient of `B ⊗[A] (B ⊗[A] M)` and those over the triple
self-product `V₃` an extension of `B ⊗[A] (B ⊗[A] (B ⊗[A] M))`, in such a way that the two Čech
differentials are `Module.Descent.amitsurDiff₀` and `Module.Descent.amitsurDiff₁`.  Then a section
over `V` killed by the degree-one Čech differential is the degree-zero Čech differential of a
section over `W`.

Only surjectivity of `eV` and injectivity of `eV₃` are used; `eW` need not be either.  For `P` a
coproduct of copies of the structure sheaf of a ringed site, over an affine object with ring `A`
covered by an affine object with ring `B`, the three maps are the identifications of the sections
of that coproduct over the three affine objects `W`, `V` and `V₃` with direct sums of copies of
their rings. -/
theorem exists_cechDiff₀_eq {W V V₃ : C} (q₁ q₂ : V ⟶ W) (t₁₂ t₁₃ t₂₃ : V₃ ⟶ V)
    (eW : B ⊗[A] M →+ P.obj (op W)) (eV : B ⊗[A] (B ⊗[A] M) →+ P.obj (op V))
    (eV₃ : B ⊗[A] (B ⊗[A] (B ⊗[A] M)) →+ P.obj (op V₃))
    (heV : Function.Surjective eV) (heV₃ : Function.Injective eV₃)
    (hd₀ : ∀ x, P.cechDiff₀ q₁ q₂ (eW x) = eV (Module.Descent.amitsurDiff₀ A B M x))
    (hd₁ : ∀ x, P.cechDiff₁ t₁₂ t₁₃ t₂₃ (eV x) = eV₃ (Module.Descent.amitsurDiff₁ A B M x))
    {x : P.obj (op V)} (hx : P.cechDiff₁ t₁₂ t₁₃ t₂₃ x = 0) :
    ∃ p : P.obj (op W), P.cechDiff₀ q₁ q₂ p = x := by
  obtain ⟨y, rfl⟩ := heV x
  have hy : Module.Descent.amitsurDiff₁ A B M y = 0 := heV₃ (by rw [← hd₁, hx, map_zero])
  obtain ⟨z, hz⟩ := Module.Descent.exists_amitsurDiff₀_eq A B M hy
  exact ⟨eW z, by rw [hd₀, hz]⟩

/-- **The vanishing of the first Čech cohomology of a one-element covering**, as the surjectivity
of the degree-zero Čech differential onto the degree-one Čech cocycles.  This is
`PresheafOfModules.exists_cechDiff₀_eq` in the shape a consumer which needs a map of sections to
be surjective uses. -/
theorem surjective_toCechCocycleOne {W V V₃ : C} (q₁ q₂ : V ⟶ W) (t₁₂ t₁₃ t₂₃ : V₃ ⟶ V)
    (hq₁ : t₁₂ ≫ q₁ = t₁₃ ≫ q₁) (hq₂ : t₁₂ ≫ q₂ = t₂₃ ≫ q₁) (hq₃ : t₁₃ ≫ q₂ = t₂₃ ≫ q₂)
    (eW : B ⊗[A] M →+ P.obj (op W)) (eV : B ⊗[A] (B ⊗[A] M) →+ P.obj (op V))
    (eV₃ : B ⊗[A] (B ⊗[A] (B ⊗[A] M)) →+ P.obj (op V₃))
    (heV : Function.Surjective eV) (heV₃ : Function.Injective eV₃)
    (hd₀ : ∀ x, P.cechDiff₀ q₁ q₂ (eW x) = eV (Module.Descent.amitsurDiff₀ A B M x))
    (hd₁ : ∀ x, P.cechDiff₁ t₁₂ t₁₃ t₂₃ (eV x) = eV₃ (Module.Descent.amitsurDiff₁ A B M x)) :
    Function.Surjective (P.toCechCocycleOne q₁ q₂ t₁₂ t₁₃ t₂₃ hq₁ hq₂ hq₃) := fun x =>
  (P.exists_cechDiff₀_eq A B M q₁ q₂ t₁₂ t₁₃ t₂₃ eW eV eV₃ heV heV₃ hd₀ hd₁
    (AddMonoidHom.mem_ker.1 x.2)).imp fun _ hp => Subtype.ext hp

/-- **The Čech complex of a one-element covering is exact in degree one**, the statement of
`PresheafOfModules.exists_cechDiff₀_eq` together with
`PresheafOfModules.cechDiff₁_cechDiff₀_apply`. -/
theorem exact_cechDiff {W V V₃ : C} (q₁ q₂ : V ⟶ W) (t₁₂ t₁₃ t₂₃ : V₃ ⟶ V)
    (hq₁ : t₁₂ ≫ q₁ = t₁₃ ≫ q₁) (hq₂ : t₁₂ ≫ q₂ = t₂₃ ≫ q₁) (hq₃ : t₁₃ ≫ q₂ = t₂₃ ≫ q₂)
    (eW : B ⊗[A] M →+ P.obj (op W)) (eV : B ⊗[A] (B ⊗[A] M) →+ P.obj (op V))
    (eV₃ : B ⊗[A] (B ⊗[A] (B ⊗[A] M)) →+ P.obj (op V₃))
    (heV : Function.Surjective eV) (heV₃ : Function.Injective eV₃)
    (hd₀ : ∀ x, P.cechDiff₀ q₁ q₂ (eW x) = eV (Module.Descent.amitsurDiff₀ A B M x))
    (hd₁ : ∀ x, P.cechDiff₁ t₁₂ t₁₃ t₂₃ (eV x) = eV₃ (Module.Descent.amitsurDiff₁ A B M x)) :
    Function.Exact (P.cechDiff₀ q₁ q₂) (P.cechDiff₁ t₁₂ t₁₃ t₂₃) := by
  intro x
  refine ⟨fun hx => P.exists_cechDiff₀_eq A B M q₁ q₂ t₁₂ t₁₃ t₂₃ eW eV eV₃ heV heV₃ hd₀ hd₁ hx,
    ?_⟩
  rintro ⟨p, rfl⟩
  exact P.cechDiff₁_cechDiff₀_apply q₁ q₂ t₁₂ t₁₃ t₂₃ hq₁ hq₂ hq₃ p

end Amitsur

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **A morphism whose kernel has vanishing first Čech cohomology along a covering morphism has
its images detected by that morphism.**  Let `b : P ⟶ N`, let `h : W ⟶ T`, and let `V` and `V₃` be
a double and a triple self-product of `W` over `T`.  The hypotheses are: that every degree-one
Čech cocycle over `V` which `b` kills is the Čech coboundary of a section over `W` which `b`
kills, the vanishing of the first Čech cohomology of the kernel of `b`; that a section of `P` over
`W` killed by the degree-zero Čech differential descends to `T`, the sheaf condition for `P`; and
that restriction along `h` is injective on the sections of `N` over `T`, the separatedness half of
the sheaf condition for `N`.

The proof is the classical one.  A section `n` of `N` over `T` whose restriction is `b` of a
section `p` over `W` has `P.cechDiff₀ p` killed by `b`, because the restriction of `n` to `W` is
already killed by the degree-zero Čech differential; so the cohomology hypothesis corrects `p` by
a section `z` of the kernel to a section which descends to a section `p₀` over `T`; and `b p₀`
restricts to the same section over `W` as `n` does, hence equals `n`.

This is the form of the vanishing of the first cohomology of a quasi-coherent module on an affine
which does **not** take a base-change identification for the target as data: the identification
enters, if at all, only in verifying the cohomological hypothesis for the kernel.  It supersedes
`SheafOfModules.detectsRange_of_baseChangeEquiv` for that purpose, which reaches the same
conclusion with no cohomology at all but takes identifications of the sections over the covering
object with a base change for **both** the source and the target, the second of which is the
statement the whole reduction is trying to prove.

Composed with `SheafOfModules.surjective_val_app_of_epi_of_detectsRange` this gives surjectivity
of an epimorphism on sections over a terminal object. -/
theorem detectsRange_of_cechH1Vanishing {P N : SheafOfModules.{m} R} (b : P ⟶ N)
    {T W V V₃ : C} (h : W ⟶ T) (q₁ q₂ : V ⟶ W) (t₁₂ t₁₃ t₂₃ : V₃ ⟶ V)
    (hq : q₁ ≫ h = q₂ ≫ h)
    (hq₁ : t₁₂ ≫ q₁ = t₁₃ ≫ q₁) (hq₂ : t₁₂ ≫ q₂ = t₂₃ ≫ q₁) (hq₃ : t₁₃ ≫ q₂ = t₂₃ ≫ q₂)
    (hker : ∀ ζ : P.val.obj (op V), b.val.app (op V) ζ = 0 →
      P.val.cechDiff₁ t₁₂ t₁₃ t₂₃ ζ = 0 →
        ∃ z : P.val.obj (op W), b.val.app (op W) z = 0 ∧ P.val.cechDiff₀ q₁ q₂ z = ζ)
    (hdesc : ∀ p : P.val.obj (op W), P.val.cechDiff₀ q₁ q₂ p = 0 →
      ∃ p₀ : P.val.obj (op T), P.val.restrictₛₗ h.op p₀ = p)
    (hinj : Function.Injective (N.val.restrictₛₗ h.op)) :
    DetectsRange b h := by
  intro n hn
  obtain ⟨p, hp⟩ := hn
  have hb : ∀ (X Y : Cᵒᵖ) (f : X ⟶ Y) (x : P.val.obj X),
      b.val.app Y (P.val.restrictₛₗ f x) = N.val.restrictₛₗ f (b.val.app X x) := fun _ _ f x =>
    PresheafOfModules.naturality_apply b.val f x
  have hcomm : ∀ x : P.val.obj (op W), b.val.app (op V) (P.val.cechDiff₀ q₁ q₂ x) =
      N.val.cechDiff₀ q₁ q₂ (b.val.app (op W) x) := fun x => by
    rw [PresheafOfModules.cechDiff₀_apply, PresheafOfModules.cechDiff₀_apply, map_sub, hb, hb]
  obtain ⟨z, hz, hzd⟩ := hker (P.val.cechDiff₀ q₁ q₂ p) (by
      rw [hcomm, hp, N.val.cechDiff₀_restrictₛₗ h q₁ q₂ hq])
    (P.val.cechDiff₁_cechDiff₀_apply q₁ q₂ t₁₂ t₁₃ t₂₃ hq₁ hq₂ hq₃ p)
  obtain ⟨p₀, hp₀⟩ := hdesc (p - z) (by rw [map_sub, hzd, sub_self])
  refine ⟨p₀, hinj ?_⟩
  rw [← hb, hp₀, map_sub, hz, sub_zero]
  exact hp

end SheafOfModules

end
