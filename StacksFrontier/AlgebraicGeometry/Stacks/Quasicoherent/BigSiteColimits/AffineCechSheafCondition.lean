module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.IsTensorProduct
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCokernelDescent
public import
StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineLocallySpannedDischarge

/-!
# The degree-zero data of the Amitsur complex of a covering family

The sheaf condition for a covering family `{Yᵢ ⟶ T}` with values in a presheaf of modules whose
sections are computed by base change is degree-zero exactness of the Amitsur complex of the
*product* of the coefficient rings of the members:
`PresheafOfModules.isSheafFor_ofArrows_of_amitsurDiff₀` asks for a faithfully flat algebra `Sa`
over the ring `A` acting on the sections over `T`, an identification of `Sa ⊗[A] N(T)` with the
product of the sections over the members, an injection of `Sa ⊗[A] (Sa ⊗[A] N(T))` into the
product of the sections over a family of objects mapping to pairs of members, and the equation
identifying the degree-zero Amitsur differential with the difference of the two restrictions.

This file produces all four from the member-wise base-change comparisons, with `Sa` the product
`∀ i, Bᵢ` of the coefficient rings.  Two observations make it mechanical.

*The product splits off.*  A finite product of rings base changes a module into the product of its
base changes (`TensorProduct.piRight` conjugated by `TensorProduct.comm`), so
`Sa ⊗[A] N(T) ≃ ∀ i, Bᵢ ⊗[A] N(T)` and, applying the same identification twice and reassociating,
`Sa ⊗[A] (Sa ⊗[A] N(T)) ≃ ∀ i j, (Bᵢ ⊗[A] Bⱼ) ⊗[A] N(T)`.  Both identifications take a pure tensor
to the expected coordinate expression definitionally, so the degree-zero Amitsur differential,
whose value on a pure tensor is a difference of two pure tensors, is read off coordinatewise.

*The comparison at a pair is determined, not chosen.*  A base-change comparison `Bᵢ ⊗[A] N(T) ≃
N(Yᵢ)` which is `Bᵢ`-linear and takes `1 ⊗ₜ n` to the restriction of `n` takes `b ⊗ₜ n` to
`b • (restriction of n)`, because `b ⊗ₜ n = b • (1 ⊗ₜ n)`.  So restricting it further along a
morphism into `Yᵢ` is forced: restriction is semilinear along the induced map of coefficient
rings, and the composite restriction is the restriction along the composite.  Nothing therefore
has to be assumed of the comparisons beyond their linearity and their value on `1 ⊗ₜ n`, and the
two "slot" equations `hnat₁` and `hnat₂` below — which is where the index order and the signs of
the Amitsur differential could go wrong — are theorems rather than hypotheses.

The coefficient ring of a pair is not assumed to be `Bᵢ ⊗[A] Bⱼ` on the nose: it is a ring `D`
with `Algebra.IsPushout A Bᵢ Bⱼ D`, which is what the ring of global functions on a fibre product
of affine objects satisfies.  The statement is for one pair at a time, so that the two algebra
structures `Algebra Bᵢ D` and `Algebra Bⱼ D` are on two different type variables; stated for a
whole family at once they would collide on the diagonal and leave instance search with a diamond.

The second half of the file supplies that data on the slices of the fppf site associated with a
category fibred in groupoids over a big fppf category of schemes, for the cokernel of a presenting
morphism computed in presheaves of modules.  Over an affine object covered by a finite family of
affine objects whose image in schemes is an fppf covering family, the coefficient rings are the
rings of global functions on the underlying schemes, the base change of the sections over the
object covered along a member is its sections over that member, the ring of global functions on a
fibre product of two members is the tensor product of their rings, and the product of the rings of
the members is faithfully flat.  So the sheaf condition for such a family holds; and a covering
family of affine objects which is not assumed flat is reduced to that case by refinement.  Both of
the hypotheses of
`AlgebraicGeometry.FibredSite.surjective_val_app_of_isSheafFor_affine_of_isColimit` are then
discharged, and a presenting morphism of a presentation is surjective on the sections over an
affine object.

## Main results

* `PresheafOfModules.restrictₛₗ_baseChange_tmul`: **restricting a base-change comparison along a
  morphism is the comparison over the target read through the induced map of coefficient rings**,
  which is where every slot equation of this file comes from.
* `PresheafOfModules.exists_pairBaseChange`: **the sections over an object mapping to two members
  of a family receive the base change of the sections over the base along the tensor product of
  the two coefficient rings**, injectively and compatibly with the two restrictions, as soon as
  the coefficient ring of that object is a pushout of the two.
* `PresheafOfModules.exists_amitsurDiff₀_data`: **the four pieces of degree-zero Amitsur data for
  a finite covering family**, from the member-wise base-change comparisons and the pairwise
  comparisons of the preceding result: an additive equivalence onto the product of the sections
  over the members carrying `1 ⊗ₜ n` to the restrictions of `n`, an injection of the next term of
  the complex into the product of the sections over the pairwise objects, and the identification
  of the degree-zero Amitsur differential with the difference of the two restrictions.
* `PresheafOfModules.exists_amitsurDiff₁_data`: **the degree-one Amitsur data for a finite
  covering family**, the same one degree up: the comparison onto the product of the sections over
  the double overlaps is now bijective, the next term of the complex injects into the product of
  the sections over the triple overlaps, and the degree-one Amitsur differential is identified
  with the alternating sum of the three restrictions onto a triple overlap.
* `PresheafOfModules.exists_familyBaseChange`: **the pairwise and triple comparisons of a covering
  family together with all five slot equations**, from the rings of the double and triple overlaps
  presented as tensor products with their two structure maps given explicitly, which is what
  `PresheafOfModules.exists_amitsurDiff₁_data` has to be fed.
* `AlgebraicGeometry.FibredSite.isSheafFor_ofArrows_of_isPresheafCokernel_of_fppf` and
  `AlgebraicGeometry.FibredSite.isSheafFor_ofArrows_cokernel_of_fppf`: **the sheaf condition for a
  finite family of affine objects whose image in schemes is an fppf covering family, for the
  presheaf cokernel of a presentation over an affine object.**
* `AlgebraicGeometry.FibredSite.isSheafFor_cokernel_of_isAffineOver`: **the same for an arbitrary
  finite covering family of affine objects**, with no flatness assumption, which is the sheaf
  condition hypothesis of
  `AlgebraicGeometry.FibredSite.surjective_val_app_of_isSheafFor_affine_of_isColimit`.
* `AlgebraicGeometry.FibredSite.surjective_val_app_of_isColimit_of_isAffineOver`: **a presenting
  morphism of a presentation of a sheaf of modules on a slice of the associated fppf site is
  surjective on the sections over an affine object**, with no hypothesis beyond the presentation.
* `AlgebraicGeometry.FibredSite.globalSectionSpan_eq_top_of_hasGlobalPresentation_of_isAffineOver`:
  **the sections of a globally presented sheaf of modules over an affine object of the slice site
  at an affine object are spanned by the restrictions of its sections over that affine object**,
  with no hypothesis beyond the presentation.

## Implementation notes

The comparisons are `Module`-linear equivalences where linearity is used and additive maps where
it is not: `PresheafOfModules.exists_amitsurDiff₀_data` consumes the member-wise comparisons as
additive equivalences and the pairwise ones as injective additive maps, since the base change
along the product is a module over the product while each factor's base change is a module over
that factor, and no single ring is available over which one linear comparison could be stated.

The module structures over the rings of global functions on the slices are introduced as
`let`-bound local definitions rather than through an auxiliary statement taking them as instance
arguments: an instance argument for the action of the ring of global functions on a module of
sections is opaque, and the sections of a presheaf of modules carry their own action over the ring
of sections of the coefficient sheaf of rings, which the two being definitionally the same ring
does not reconcile once one of them is a variable.  For the same reason the underlying schemes are
written out rather than abbreviated: a `let`-bound scheme is lifted into an auxiliary definition
together with the module structures mentioning it, and the lifting does not survive the kernel.

No instance is created.  Every ring acting on a module of sections is an instance argument, and
the equations identifying the `algebraMap` of an algebra structure with a map of coefficient
rings are hypotheses, so that a caller supplies the structures its own consumers are stated for.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 0238](https://stacks.math.columbia.edu/tag/0238)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe y z v w u t

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{z}}

/-- **Restricting a base-change comparison along a morphism is the comparison over the target
read through the induced map of coefficient rings.**

If the sections over `U` are the base change of the sections over `T` along `A → BU` by a
comparison taking `1 ⊗ₜ n` to the restriction of `n`, then that comparison takes `b ⊗ₜ n` to
`b • (restriction of n)`, because `b ⊗ₜ n = b • (1 ⊗ₜ n)`.  So its restriction along `h : W ⟶ U`
is determined by how restriction along `h` moves the action: if restriction along `h` is
semilinear along a map `φ : BU → BW`, as it is whenever `φ` is the induced map of coefficient
rings, then restricting the comparison over `U` along `h` is the comparison over `W` precomposed
with `φ` in the ring slot.

Nothing is asked of `φ` beyond the semilinearity `hφ`: the computation never multiplies two of
its values.  This is the step at which every "slot" equation of this file is proved rather than
assumed, for the two projections of a double overlap and for the three projections of a triple
overlap onto the double ones alike. -/
theorem restrictₛₗ_baseChange_tmul {N : PresheafOfModules.{y} R} {T U W : C} (gU : U ⟶ T)
    (h : W ⟶ U) (A BU BW : Type*) [CommRing A] [CommRing BU] [CommRing BW]
    [Module A (N.obj (op T))] [Module BU (N.obj (op U))] [Module BW (N.obj (op W))]
    [Algebra A BU] [Algebra A BW]
    (eU : BU ⊗[A] N.obj (op T) ≃ₗ[BU] N.obj (op U))
    (heU : ∀ n, eU ((1 : BU) ⊗ₜ[A] n) = N.restrictₛₗ gU.op n)
    (eW : BW ⊗[A] N.obj (op T) ≃ₗ[BW] N.obj (op W))
    (heW : ∀ n, eW ((1 : BW) ⊗ₜ[A] n) = N.restrictₛₗ (h ≫ gU).op n)
    (φ : BU → BW)
    (hφ : ∀ (b : BU) (x : N.obj (op U)),
      N.restrictₛₗ h.op (b • x) = φ b • N.restrictₛₗ h.op x)
    (b : BU) (n : N.obj (op T)) :
    N.restrictₛₗ h.op (eU (b ⊗ₜ[A] n)) = eW (φ b ⊗ₜ[A] n) := by
  have h1 : eU (b ⊗ₜ[A] n) = b • N.restrictₛₗ gU.op n := by
    rw [← heU n, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, hφ, N.restrictₛₗ_restrictₛₗ_op, ← heW n, ← map_smul, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

/-- **The sections over an object mapping to two members of a family receive the base change of
the sections over the base along the tensor product of the two coefficient rings**, injectively,
and compatibly with the restrictions along the two morphisms.

Let `g₁ : Y₁ ⟶ T` and `g₂ : Y₂ ⟶ T`, let `q₁ : Pb ⟶ Y₁` and `q₂ : Pb ⟶ Y₂` have equal composites
with them, and let the sections over `T`, `Y₁`, `Y₂` and `Pb` be modules over `A`, `B₁`, `B₂` and
`D`, where `D` is a pushout of `B₁` and `B₂` over `A`.  Given base-change comparisons over the
three objects, the comparison over `Pb` composed with the identification `B₁ ⊗[A] B₂ ≃ D` is the
required injection, and the two restrictions are its values on the two kinds of pure tensor.

This is the step at which the two "slot" equations are proved rather than assumed.  A
`B₁`-linear comparison taking `1 ⊗ₜ n` to the restriction of `n` takes `b ⊗ₜ n` to
`b • (restriction of n)`, restriction along `q₁` is semilinear along `algebraMap B₁ D`, and the
composite restriction is the restriction along the composite; so restricting the comparison over
`Y₁` along `q₁` is the comparison over `Pb` precomposed with `b ⊗ₜ c ↦ algebraMap B₁ D b`, and
symmetrically for `q₂`.  The equality of the two composites is what makes the second computation
land in the same module as the first. -/
theorem exists_pairBaseChange {N : PresheafOfModules.{y} R} {T Y₁ Y₂ Pb : C} (g₁ : Y₁ ⟶ T)
    (g₂ : Y₂ ⟶ T) (q₁ : Pb ⟶ Y₁) (q₂ : Pb ⟶ Y₂) (hq : q₁ ≫ g₁ = q₂ ≫ g₂)
    (A B₁ B₂ D : Type*) [CommRing A] [CommRing B₁] [CommRing B₂] [CommRing D]
    [Algebra A B₁] [Algebra A B₂] [Algebra A D] [Algebra B₁ D] [Algebra B₂ D]
    [IsScalarTower A B₁ D] [IsScalarTower A B₂ D] [Algebra.IsPushout A B₁ B₂ D]
    [Module A (N.obj (op T))] [Module B₁ (N.obj (op Y₁))] [Module B₂ (N.obj (op Y₂))]
    [Module D (N.obj (op Pb))]
    (e₁ : B₁ ⊗[A] N.obj (op T) ≃ₗ[B₁] N.obj (op Y₁))
    (he₁ : ∀ n, e₁ ((1 : B₁) ⊗ₜ[A] n) = N.restrictₛₗ g₁.op n)
    (e₂ : B₂ ⊗[A] N.obj (op T) ≃ₗ[B₂] N.obj (op Y₂))
    (he₂ : ∀ n, e₂ ((1 : B₂) ⊗ₜ[A] n) = N.restrictₛₗ g₂.op n)
    (eP : D ⊗[A] N.obj (op T) ≃ₗ[D] N.obj (op Pb))
    (heP : ∀ n, eP ((1 : D) ⊗ₜ[A] n) = N.restrictₛₗ (q₁ ≫ g₁).op n)
    (hsm₁ : ∀ (b : B₁) (u : N.obj (op Y₁)),
      N.restrictₛₗ q₁.op (b • u) = algebraMap B₁ D b • N.restrictₛₗ q₁.op u)
    (hsm₂ : ∀ (b : B₂) (u : N.obj (op Y₂)),
      N.restrictₛₗ q₂.op (b • u) = algebraMap B₂ D b • N.restrictₛₗ q₂.op u) :
    ∃ f : (B₁ ⊗[A] B₂) ⊗[A] N.obj (op T) →+ N.obj (op Pb),
      Function.Injective f ∧
        (∀ (b : B₁) (n), N.restrictₛₗ q₁.op (e₁ (b ⊗ₜ[A] n)) = f ((b ⊗ₜ[A] (1 : B₂)) ⊗ₜ[A] n)) ∧
          ∀ (b : B₂) (n), N.restrictₛₗ q₂.op (e₂ (b ⊗ₜ[A] n)) = f (((1 : B₁) ⊗ₜ[A] b) ⊗ₜ[A] n) := by
  let ψ : B₁ ⊗[A] B₂ ≃ₗ[A] D :=
    ((Algebra.IsPushout.equiv A B₁ B₂ D).restrictScalars A).toLinearEquiv
  have hψ : ∀ (b : B₁) (c : B₂), ψ (b ⊗ₜ[A] c) = algebraMap B₁ D b * algebraMap B₂ D c :=
    fun b c => Algebra.IsPushout.equiv_tmul A B₁ B₂ D b c
  let F : (B₁ ⊗[A] B₂) ⊗[A] N.obj (op T) ≃+ N.obj (op Pb) :=
    (TensorProduct.congr ψ (LinearEquiv.refl A (N.obj (op T)))).toAddEquiv.trans eP.toAddEquiv
  have hF : ∀ (x : B₁ ⊗[A] B₂) (n : N.obj (op T)), F (x ⊗ₜ[A] n) = eP (ψ x ⊗ₜ[A] n) :=
    fun _ _ => rfl
  refine ⟨F.toAddMonoidHom, F.bijective.1, fun b n => ?_, fun b n => ?_⟩
  · rw [restrictₛₗ_baseChange_tmul g₁ q₁ A B₁ D e₁ he₁ eP heP (algebraMap B₁ D) hsm₁ b n]
    change _ = F ((b ⊗ₜ[A] (1 : B₂)) ⊗ₜ[A] n)
    rw [hF, hψ, map_one, mul_one]
  · rw [restrictₛₗ_baseChange_tmul g₂ q₂ A B₂ D e₂ he₂ eP
      (fun n => (heP n).trans (by rw [hq])) (algebraMap B₂ D) hsm₂ b n]
    change _ = F (((1 : B₁) ⊗ₜ[A] b) ⊗ₜ[A] n)
    rw [hF, hψ, map_one, one_mul]

/-- A finite product of rings base changes a module into the product of its base changes. -/
private noncomputable def piTensorEquiv (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Bi : ι → Type*) [∀ i, CommRing (Bi i)]
    [∀ i, Algebra A (Bi i)] : (∀ i, Bi i) ⊗[A] M ≃ₗ[A] ∀ i, Bi i ⊗[A] M :=
  (TensorProduct.comm A (∀ i, Bi i) M).trans
    ((TensorProduct.piRight A A M Bi).trans
      (LinearEquiv.piCongrRight fun i => TensorProduct.comm A M (Bi i)))

/-- Applying `piTensorEquiv` twice and reassociating splits the second base change of a module
over a finite product of rings coordinatewise over pairs. -/
private noncomputable def pairTensorEquiv (A M : Type*) [CommRing A] [AddCommGroup M]
    [Module A M] {ι : Type*} [Fintype ι] [DecidableEq ι] (Bi : ι → Type*)
    [∀ i, CommRing (Bi i)] [∀ i, Algebra A (Bi i)] :
    (∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] M) ≃ₗ[A] ∀ i j, (Bi i ⊗[A] Bi j) ⊗[A] M :=
  (piTensorEquiv A _ Bi).trans (LinearEquiv.piCongrRight fun i =>
    (TensorProduct.congr (LinearEquiv.refl A (Bi i)) (piTensorEquiv A M Bi)).trans
      ((TensorProduct.piRight A A (Bi i) fun j => Bi j ⊗[A] M).trans
        (LinearEquiv.piCongrRight fun j => (TensorProduct.assoc A (Bi i) (Bi j) M).symm)))

/-- The degree-zero Amitsur differential of the product of the coefficient rings is the difference
of the two restrictions, from the coordinate descriptions of the two assembled comparisons alone.

Only additivity of the assembled comparisons `eW` and `eV` is used, and nothing is asked of the
member-wise comparison `e` and the pairwise comparison `f` beyond the two "slot" equations, so
neither has to be a map of modules.  The assembled comparisons of the degree-zero data of
`PresheafOfModules.exists_amitsurDiff₀_data` and of the degree-one data of
`PresheafOfModules.exists_amitsurDiff₁_data` agree in these two degrees and differ only above
them, so both get this computation from here. -/
private theorem amitsurDiff₀_eq_sub_restrictₛₗ {N : PresheafOfModules.{y} R} {T : C}
    {ιi : Type*} {Y : ιi → C} {Pb : ιi → ιi → C} (pr₁ : ∀ i j, Pb i j ⟶ Y i)
    (pr₂ : ∀ i j, Pb i j ⟶ Y j) (A : Type*) [CommRing A] [Module A (N.obj (op T))]
    (Bi : ιi → Type*) [∀ i, CommRing (Bi i)] [∀ i, Algebra A (Bi i)]
    (e : ∀ i, Bi i ⊗[A] N.obj (op T) → N.obj (op (Y i)))
    (f : ∀ i j, (Bi i ⊗[A] Bi j) ⊗[A] N.obj (op T) → N.obj (op (Pb i j)))
    (eW : (∀ i, Bi i) ⊗[A] N.obj (op T) →+ (∀ i, N.obj (op (Y i))))
    (eV : (∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] N.obj (op T)) →+ (∀ i j, N.obj (op (Pb i j))))
    (heW : ∀ (u : ∀ i, Bi i) (m : N.obj (op T)) (i), eW (u ⊗ₜ[A] m) i = e i (u i ⊗ₜ[A] m))
    (heV : ∀ (u v : ∀ i, Bi i) (m : N.obj (op T)) (i j),
      eV (u ⊗ₜ[A] (v ⊗ₜ[A] m)) i j = f i j ((u i ⊗ₜ[A] v j) ⊗ₜ[A] m))
    (hnat₁ : ∀ (i j) (b : Bi i) (n : N.obj (op T)),
      N.restrictₛₗ (pr₁ i j).op (e i (b ⊗ₜ[A] n)) = f i j ((b ⊗ₜ[A] (1 : Bi j)) ⊗ₜ[A] n))
    (hnat₂ : ∀ (i j) (b : Bi j) (n : N.obj (op T)),
      N.restrictₛₗ (pr₂ i j).op (e j (b ⊗ₜ[A] n)) = f i j (((1 : Bi i) ⊗ₜ[A] b) ⊗ₜ[A] n))
    (c : (∀ i, Bi i) ⊗[A] N.obj (op T)) (i j : ιi) :
    eV (Module.Descent.amitsurDiff₀ A (∀ i, Bi i) (N.obj (op T)) c) i j =
      N.restrictₛₗ (pr₁ i j).op (eW c i) - N.restrictₛₗ (pr₂ i j).op (eW c j) := by
  induction c with
  | add c c' hc hc' =>
    rw [map_add, map_add]
    change eV (Module.Descent.amitsurDiff₀ A (∀ i, Bi i) (N.obj (op T)) c) i j +
        eV (Module.Descent.amitsurDiff₀ A (∀ i, Bi i) (N.obj (op T)) c') i j = _
    rw [hc, hc', show eW (c + c') i = eW c i + eW c' i from congrFun (map_add eW c c') i,
      show eW (c + c') j = eW c j + eW c' j from congrFun (map_add eW c c') j, map_add, map_add]
    abel
  | tmul u m =>
    rw [Module.Descent.amitsurDiff₀_tmul, map_sub]
    change eV (u ⊗ₜ[A] ((1 : ∀ i, Bi i) ⊗ₜ[A] m)) i j -
        eV ((1 : ∀ i, Bi i) ⊗ₜ[A] (u ⊗ₜ[A] m)) i j = _
    rw [heV, heV, heW, heW]
    change f i j ((u i ⊗ₜ[A] (1 : Bi j)) ⊗ₜ[A] m) - f i j (((1 : Bi i) ⊗ₜ[A] u j) ⊗ₜ[A] m) =
      N.restrictₛₗ (pr₁ i j).op (e i (u i ⊗ₜ[A] m)) -
        N.restrictₛₗ (pr₂ i j).op (e j (u j ⊗ₜ[A] m))
    rw [hnat₁ i j (u i) m, hnat₂ i j (u j) m]

/-- **The four pieces of degree-zero Amitsur data for a finite covering family**, from the
member-wise base-change comparisons of the sections of a presheaf of modules and the pairwise
comparisons of `PresheafOfModules.exists_pairBaseChange`.

For a finite family `g i : Y i ⟶ T` and objects `Pb i j` mapping to `Y i` and `Y j`, with the
sections over `T` a module over `A` and the sections over `Y i` identified with the base change
along `A → Bᵢ`, the product `∀ i, Bᵢ` is the algebra whose Amitsur complex computes the sheaf
condition for the family.  Its degree-one term is the product of the sections over the members
and its degree-two term injects into the product of the sections over the `Pb i j`, both because
a finite product of rings base changes a module into the product of its base changes; and the
degree-zero differential becomes the difference of the two restrictions.

The conclusion is exactly the four hypotheses `heW`, `heWone`, `heV` and `hd₀` of
`PresheafOfModules.isSheafFor_ofArrows_of_amitsurDiff₀`, so that with faithful flatness of the
product this is the sheaf condition for the family.  Nothing here is a sheaf, nothing is a
scheme, and no topology occurs. -/
theorem exists_amitsurDiff₀_data {N : PresheafOfModules.{y} R} {T : C} {ιi : Type*} [Finite ιi]
    {Y : ιi → C} (g : ∀ i, Y i ⟶ T) {Pb : ιi → ιi → C} (pr₁ : ∀ i j, Pb i j ⟶ Y i)
    (pr₂ : ∀ i j, Pb i j ⟶ Y j) (A : Type*) [CommRing A] [Module A (N.obj (op T))]
    (Bi : ιi → Type*) [∀ i, CommRing (Bi i)] [∀ i, Algebra A (Bi i)]
    (e : ∀ i, Bi i ⊗[A] N.obj (op T) ≃+ N.obj (op (Y i)))
    (he : ∀ (i) (n : N.obj (op T)), e i ((1 : Bi i) ⊗ₜ[A] n) = N.map (g i).op n)
    (f : ∀ i j, (Bi i ⊗[A] Bi j) ⊗[A] N.obj (op T) →+ N.obj (op (Pb i j)))
    (hf : ∀ i j, Function.Injective (f i j))
    (hnat₁ : ∀ (i j) (b : Bi i) (n : N.obj (op T)),
      N.restrictₛₗ (pr₁ i j).op (e i (b ⊗ₜ[A] n)) = f i j ((b ⊗ₜ[A] (1 : Bi j)) ⊗ₜ[A] n))
    (hnat₂ : ∀ (i j) (b : Bi j) (n : N.obj (op T)),
      N.restrictₛₗ (pr₂ i j).op (e j (b ⊗ₜ[A] n)) = f i j (((1 : Bi i) ⊗ₜ[A] b) ⊗ₜ[A] n)) :
    ∃ (eW : (∀ i, Bi i) ⊗[A] N.obj (op T) →+ (∀ i, N.obj (op (Y i))))
      (eV : (∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] N.obj (op T)) →+ (∀ i j, N.obj (op (Pb i j)))),
      Function.Bijective eW ∧
        (∀ (n : N.obj (op T)) (i), eW ((1 : ∀ i, Bi i) ⊗ₜ[A] n) i = N.map (g i).op n) ∧
        Function.Injective eV ∧
          ∀ (c : (∀ i, Bi i) ⊗[A] N.obj (op T)) (i j),
            eV (Module.Descent.amitsurDiff₀ A (∀ i, Bi i) (N.obj (op T)) c) i j =
              N.restrictₛₗ (pr₁ i j).op (eW c i) - N.restrictₛₗ (pr₂ i j).op (eW c j) := by
  classical
  have _ := Fintype.ofFinite ιi
  let Xi := pairTensorEquiv A (N.obj (op T)) Bi
  let eW : (∀ i, Bi i) ⊗[A] N.obj (op T) ≃+ ∀ i, N.obj (op (Y i)) :=
    (piTensorEquiv A (N.obj (op T)) Bi).toAddEquiv.trans (AddEquiv.piCongrRight e)
  have hXi : ∀ (s t : ∀ i, Bi i) (m : N.obj (op T)) (i j : ιi),
      Xi (s ⊗ₜ[A] (t ⊗ₜ[A] m)) i j = (s i ⊗ₜ[A] t j) ⊗ₜ[A] m := fun _ _ _ _ _ => rfl
  have heW : ∀ (s : ∀ i, Bi i) (m : N.obj (op T)) (i : ιi),
      eW (s ⊗ₜ[A] m) i = e i (s i ⊗ₜ[A] m) := fun _ _ _ => rfl
  let eV : (∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] N.obj (op T)) →+
      ∀ i j, N.obj (op (Pb i j)) :=
    AddMonoidHom.mk' (fun d i j => f i j (Xi d i j)) fun d d' =>
      funext fun i => funext fun j => by simp only [map_add, Pi.add_apply]
  have heV : ∀ (d : (∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] N.obj (op T))) (i j : ιi),
      eV d i j = f i j (Xi d i j) := fun _ _ _ => rfl
  refine ⟨eW.toAddMonoidHom, eV, eW.bijective, fun n i => (heW 1 n i).trans (he i n),
    fun d d' hdd' => ?_,
    fun c i j => amitsurDiff₀_eq_sub_restrictₛₗ pr₁ pr₂ A Bi (fun i => (e i : _ → _))
      (fun i j => (f i j : _ → _)) eW.toAddMonoidHom eV heW
      (fun u v m i j => (heV _ i j).trans (congrArg (f i j) (hXi u v m i j))) hnat₁ hnat₂ c i j⟩
  refine Xi.injective (funext fun i => funext fun j => hf i j ?_)
  rw [← heV, ← heV, hdd']

/-- **The degree-one Amitsur data for a finite covering family**, from the member-wise
base-change comparisons of the sections of a presheaf of modules, the pairwise comparisons at the
double overlaps and the triple comparisons at the triple overlaps.

This is the degree-one companion of `PresheafOfModules.exists_amitsurDiff₀_data`, and it differs
from it in exactly the three places the vanishing of the first Čech cohomology needs more than the
sheaf condition does.  The comparisons `f i j` at the double overlaps are asked to be bijective
and not merely injective, so that the assembled `eV` is onto the product of the sections over the
double overlaps: a degree-one Čech cocycle of the family has to be *lifted* to the degree-one term
of the Amitsur complex, where the sheaf condition only had to push a coboundary down.  The next
term of the complex has to be compared with the product of the sections over the triple overlaps,
injectively, which is the comparison `f₃`.  And the degree-one differential has to be identified
with the alternating sum of the three restrictions, which is the three "slot" equations `hs₁`,
`hs₂` and `hs₃`: each says that restricting a pairwise comparison along one of the three
projections of a triple overlap onto a double one is the triple comparison with a `1` inserted
into the corresponding slot.

The degree-two term of the complex is identified with the product over triples of the base change
of the sections over `T` along `A → Bᵢ ⊗[A] (Bⱼ ⊗[A] Bₖ)`, right-associated, which is the
spelling `AlgebraicGeometry.algEquivTensorAppTopOfIsPullback₃` produces for the ring of a triple
overlap: a triple overlap is a fibre product of a member with a double overlap, so its ring is
`Bᵢ ⊗[A] Dⱼₖ` with `Dⱼₖ` the ring of the double overlap, and no associativity comparison is
needed.

The conclusion is exactly the data `eW`, `eV`, `eV₃`, `heV`, `heV₃`, `hd₀` and `hd₁` of
`PresheafOfModules.exists_familyCechDiff₀_eq`, so that with faithful flatness of the product this
is the vanishing of the first Čech cohomology of the family.  Nothing here is a sheaf, nothing is
a scheme, no topology occurs and no covering property of the family is used. -/
theorem exists_amitsurDiff₁_data {N : PresheafOfModules.{y} R} {T : C} {ιi : Type*} [Finite ιi]
    {Y : ιi → C} (g : ∀ i, Y i ⟶ T) {Pb : ιi → ιi → C} {Pb₃ : ιi → ιi → ιi → C}
    (pr₁ : ∀ i j, Pb i j ⟶ Y i) (pr₂ : ∀ i j, Pb i j ⟶ Y j)
    (s₁ : ∀ i j k, Pb₃ i j k ⟶ Pb j k) (s₂ : ∀ i j k, Pb₃ i j k ⟶ Pb i k)
    (s₃ : ∀ i j k, Pb₃ i j k ⟶ Pb i j)
    (A : Type*) [CommRing A] [Module A (N.obj (op T))]
    (Bi : ιi → Type*) [∀ i, CommRing (Bi i)] [∀ i, Algebra A (Bi i)]
    (e : ∀ i, Bi i ⊗[A] N.obj (op T) ≃+ N.obj (op (Y i)))
    (he : ∀ (i) (n : N.obj (op T)), e i ((1 : Bi i) ⊗ₜ[A] n) = N.map (g i).op n)
    (f : ∀ i j, (Bi i ⊗[A] Bi j) ⊗[A] N.obj (op T) ≃+ N.obj (op (Pb i j)))
    (f₃ : ∀ i j k,
      (Bi i ⊗[A] (Bi j ⊗[A] Bi k)) ⊗[A] N.obj (op T) →+ N.obj (op (Pb₃ i j k)))
    (hf₃ : ∀ i j k, Function.Injective (f₃ i j k))
    (hnat₁ : ∀ (i j) (b : Bi i) (n : N.obj (op T)),
      N.restrictₛₗ (pr₁ i j).op (e i (b ⊗ₜ[A] n)) = f i j ((b ⊗ₜ[A] (1 : Bi j)) ⊗ₜ[A] n))
    (hnat₂ : ∀ (i j) (b : Bi j) (n : N.obj (op T)),
      N.restrictₛₗ (pr₂ i j).op (e j (b ⊗ₜ[A] n)) = f i j (((1 : Bi i) ⊗ₜ[A] b) ⊗ₜ[A] n))
    (hs₁ : ∀ (i j k) (b : Bi j) (c : Bi k) (n : N.obj (op T)),
      N.restrictₛₗ (s₁ i j k).op (f j k ((b ⊗ₜ[A] c) ⊗ₜ[A] n)) =
        f₃ i j k (((1 : Bi i) ⊗ₜ[A] (b ⊗ₜ[A] c)) ⊗ₜ[A] n))
    (hs₂ : ∀ (i j k) (b : Bi i) (c : Bi k) (n : N.obj (op T)),
      N.restrictₛₗ (s₂ i j k).op (f i k ((b ⊗ₜ[A] c) ⊗ₜ[A] n)) =
        f₃ i j k ((b ⊗ₜ[A] ((1 : Bi j) ⊗ₜ[A] c)) ⊗ₜ[A] n))
    (hs₃ : ∀ (i j k) (b : Bi i) (c : Bi j) (n : N.obj (op T)),
      N.restrictₛₗ (s₃ i j k).op (f i j ((b ⊗ₜ[A] c) ⊗ₜ[A] n)) =
        f₃ i j k ((b ⊗ₜ[A] (c ⊗ₜ[A] (1 : Bi k))) ⊗ₜ[A] n)) :
    ∃ (eW : (∀ i, Bi i) ⊗[A] N.obj (op T) →+ (∀ i, N.obj (op (Y i))))
      (eV : (∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] N.obj (op T)) →+ (∀ i j, N.obj (op (Pb i j))))
      (eV₃ : (∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] N.obj (op T))) →+
        (∀ i j k, N.obj (op (Pb₃ i j k)))),
      Function.Bijective eW ∧
        (∀ (n : N.obj (op T)) (i), eW ((1 : ∀ i, Bi i) ⊗ₜ[A] n) i = N.map (g i).op n) ∧
        Function.Surjective eV ∧ Function.Injective eV₃ ∧
        (∀ (c : (∀ i, Bi i) ⊗[A] N.obj (op T)) (i j),
          eV (Module.Descent.amitsurDiff₀ A (∀ i, Bi i) (N.obj (op T)) c) i j =
            N.restrictₛₗ (pr₁ i j).op (eW c i) - N.restrictₛₗ (pr₂ i j).op (eW c j)) ∧
          ∀ (x : (∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] N.obj (op T))) (i j k),
            eV₃ (Module.Descent.amitsurDiff₁ A (∀ i, Bi i) (N.obj (op T)) x) i j k =
              N.restrictₛₗ (s₁ i j k).op (eV x j k) - N.restrictₛₗ (s₂ i j k).op (eV x i k) +
                N.restrictₛₗ (s₃ i j k).op (eV x i j) := by
  classical
  have _ := Fintype.ofFinite ιi
  let Xi := pairTensorEquiv A (N.obj (op T)) Bi
  let Xi₃ : (∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] N.obj (op T))) ≃ₗ[A]
      ∀ i j k, (Bi i ⊗[A] (Bi j ⊗[A] Bi k)) ⊗[A] N.obj (op T) :=
    (piTensorEquiv A _ Bi).trans (LinearEquiv.piCongrRight fun i =>
      (TensorProduct.congr (LinearEquiv.refl A (Bi i)) Xi).trans
        ((TensorProduct.piRight A A (Bi i)
            fun j => ∀ k, (Bi j ⊗[A] Bi k) ⊗[A] N.obj (op T)).trans
          (LinearEquiv.piCongrRight fun j =>
            (TensorProduct.piRight A A (Bi i)
                fun k => (Bi j ⊗[A] Bi k) ⊗[A] N.obj (op T)).trans
              (LinearEquiv.piCongrRight fun k =>
                (TensorProduct.assoc A (Bi i) (Bi j ⊗[A] Bi k) (N.obj (op T))).symm))))
  have hXi : ∀ (u v : ∀ i, Bi i) (m : N.obj (op T)) (i j : ιi),
      Xi (u ⊗ₜ[A] (v ⊗ₜ[A] m)) i j = (u i ⊗ₜ[A] v j) ⊗ₜ[A] m := fun _ _ _ _ _ => rfl
  let eW : (∀ i, Bi i) ⊗[A] N.obj (op T) ≃+ ∀ i, N.obj (op (Y i)) :=
    (piTensorEquiv A (N.obj (op T)) Bi).toAddEquiv.trans (AddEquiv.piCongrRight e)
  have heW : ∀ (u : ∀ i, Bi i) (m : N.obj (op T)) (i : ιi),
      eW (u ⊗ₜ[A] m) i = e i (u i ⊗ₜ[A] m) := fun _ _ _ => rfl
  let eV : (∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] N.obj (op T)) ≃+
      ∀ i j, N.obj (op (Pb i j)) :=
    Xi.toAddEquiv.trans (AddEquiv.piCongrRight fun i => AddEquiv.piCongrRight fun j => f i j)
  have heV : ∀ (d : (∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] N.obj (op T))) (i j : ιi),
      eV d i j = f i j (Xi d i j) := fun _ _ _ => rfl
  let eV₃ : (∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] N.obj (op T))) →+
      ∀ i j k, N.obj (op (Pb₃ i j k)) :=
    AddMonoidHom.mk' (fun d i j k => f₃ i j k (Xi₃ d i j k)) fun d d' =>
      funext fun i => funext fun j => funext fun k => by simp only [map_add, Pi.add_apply]
  have heV₃ : ∀ (d : (∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] N.obj (op T))))
      (i j k : ιi), eV₃ d i j k = f₃ i j k (Xi₃ d i j k) := fun _ _ _ _ => rfl
  have hz₃ : ∀ i j k : ιi, eV₃ 0 i j k = 0 := fun i j k =>
    congrFun (congrFun (congrFun (map_zero eV₃) i) j) k
  have ha₃ : ∀ (d d' : (∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] N.obj (op T))))
      (i j k : ιi), eV₃ (d + d') i j k = eV₃ d i j k + eV₃ d' i j k := fun d d' i j k =>
    congrFun (congrFun (congrFun (map_add eV₃ d d') i) j) k
  have hs₃' : ∀ (d d' : (∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] N.obj (op T))))
      (i j k : ιi), eV₃ (d - d') i j k = eV₃ d i j k - eV₃ d' i j k := fun d d' i j k =>
    congrFun (congrFun (congrFun (map_sub eV₃ d d') i) j) k
  have hzV : ∀ i j : ιi, eV 0 i j = 0 := fun i j =>
    congrFun (congrFun (map_zero eV) i) j
  have haV : ∀ (d d' : (∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] N.obj (op T))) (i j : ιi),
      eV (d + d') i j = eV d i j + eV d' i j := fun d d' i j =>
    congrFun (congrFun (map_add eV d d') i) j
  have key : ∀ (u : ∀ i, Bi i) (y : (∀ i, Bi i) ⊗[A] N.obj (op T)) (i j k : ιi),
      eV₃ (Module.Descent.amitsurDiff₁ A (∀ i, Bi i) (N.obj (op T)) (u ⊗ₜ[A] y)) i j k =
        N.restrictₛₗ (s₁ i j k).op (eV (u ⊗ₜ[A] y) j k) -
            N.restrictₛₗ (s₂ i j k).op (eV (u ⊗ₜ[A] y) i k) +
          N.restrictₛₗ (s₃ i j k).op (eV (u ⊗ₜ[A] y) i j) := by
    intro u y
    induction y with
    | add y y' hy hy' =>
      intro i j k
      rw [TensorProduct.tmul_add, map_add, ha₃, hy, hy', haV, haV, haV, map_add, map_add, map_add]
      abel
    | tmul v m =>
      intro i j k
      rw [Module.Descent.amitsurDiff₁_tmul, ha₃, hs₃']
      change f₃ i j k (((1 : Bi i) ⊗ₜ[A] (u j ⊗ₜ[A] v k)) ⊗ₜ[A] m) -
            f₃ i j k ((u i ⊗ₜ[A] ((1 : Bi j) ⊗ₜ[A] v k)) ⊗ₜ[A] m) +
          f₃ i j k ((u i ⊗ₜ[A] (v j ⊗ₜ[A] (1 : Bi k))) ⊗ₜ[A] m) =
        N.restrictₛₗ (s₁ i j k).op (f j k ((u j ⊗ₜ[A] v k) ⊗ₜ[A] m)) -
            N.restrictₛₗ (s₂ i j k).op (f i k ((u i ⊗ₜ[A] v k) ⊗ₜ[A] m)) +
          N.restrictₛₗ (s₃ i j k).op (f i j ((u i ⊗ₜ[A] v j) ⊗ₜ[A] m))
      rw [hs₁ i j k (u j) (v k) m, hs₂ i j k (u i) (v k) m, hs₃ i j k (u i) (v j) m]
  have hall : ∀ (x : (∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] N.obj (op T))) (i j k : ιi),
      eV₃ (Module.Descent.amitsurDiff₁ A (∀ i, Bi i) (N.obj (op T)) x) i j k =
        N.restrictₛₗ (s₁ i j k).op (eV x j k) - N.restrictₛₗ (s₂ i j k).op (eV x i k) +
          N.restrictₛₗ (s₃ i j k).op (eV x i j) := by
    intro x
    induction x with
    | add x x' hx hx' =>
      intro i j k
      rw [map_add, ha₃, hx, hx', haV, haV, haV, map_add, map_add, map_add]
      abel
    | tmul u y => exact key u y
  refine ⟨eW.toAddMonoidHom, eV.toAddMonoidHom, eV₃, eW.bijective,
    fun n i => (heW 1 n i).trans (he i n), eV.surjective, fun d d' hdd' => ?_,
    fun c i j => amitsurDiff₀_eq_sub_restrictₛₗ pr₁ pr₂ A Bi (fun i => (e i : _ → _))
      (fun i j => (f i j : _ → _)) eW.toAddMonoidHom eV.toAddMonoidHom heW
      (fun u v m i j => (heV _ i j).trans (congrArg (f i j) (hXi u v m i j))) hnat₁ hnat₂ c i j,
    hall⟩
  refine Xi₃.injective (funext fun i => funext fun j => funext fun k => hf₃ i j k ?_)
  rw [← heV₃, ← heV₃, hdd']

/-- **The pairwise and triple base-change comparisons of a covering family, with all five slot
equations**, from the rings of the double and triple overlaps presented as tensor products.

This is the triple-overlap companion of `PresheafOfModules.exists_pairBaseChange`, and it is
stated for a whole family at once, which that result could not be: there the two maps of the
pushout are the algebra structures `Algebra B₁ D` and `Algebra B₂ D`, which on the diagonal of a
family would be two instances for one pair of types.  Here the two maps into the ring of a double
overlap are the explicit algebra maps `u i j` and `v i j`, and the identification of that ring
with `Bᵢ ⊗[A] Bⱼ` is the datum `ψ i j`, in exactly the shape
`AlgebraicGeometry.Space.SmallEtale.exists_ringEquivTensorGamma_of_isPullback` produces it: a ring
isomorphism together with its value on a pure tensor.  The ring of a triple overlap is identified
with `Bᵢ ⊗[A] Dⱼₖ` the same way, a triple overlap being a fibre product of a member with a double
overlap, which is why the triple term is right-associated.

The three maps `σ₂`, `σ₃` and `v₃` are the maps of coefficient rings induced by the three
projections of a triple overlap onto the double overlaps, and the four equations `hσ₂u`, `hσ₂v`,
`hσ₃u` and `hσ₃v` are exactly the four commutations
`CategoryTheory.IsPullback.exists_familyCechProjections` produces, read on rings.  Everything else
is forced: `PresheafOfModules.restrictₛₗ_baseChange_tmul` computes each restriction of a
comparison from the semilinearity of restriction alone, so the five slot equations are theorems.

The conclusion is exactly the hypotheses `f`, `f₃`, `hf₃`, `hnat₁`, `hnat₂`, `hs₁`, `hs₂` and
`hs₃` of `PresheafOfModules.exists_amitsurDiff₁_data`. -/
theorem exists_familyBaseChange {N : PresheafOfModules.{y} R} {T : C} {ιi : Type*}
    {Y : ιi → C} {Pb : ιi → ιi → C} {Pb₃ : ιi → ιi → ιi → C} (g : ∀ i, Y i ⟶ T)
    (pr₁ : ∀ i j, Pb i j ⟶ Y i) (pr₂ : ∀ i j, Pb i j ⟶ Y j)
    (s₁ : ∀ i j k, Pb₃ i j k ⟶ Pb j k) (s₂ : ∀ i j k, Pb₃ i j k ⟶ Pb i k)
    (s₃ : ∀ i j k, Pb₃ i j k ⟶ Pb i j)
    (A : Type*) [CommRing A] [Module A (N.obj (op T))]
    (Bi : ιi → Type*) [∀ i, CommRing (Bi i)] [∀ i, Algebra A (Bi i)]
    (D : ιi → ιi → Type*) [∀ i j, CommRing (D i j)] [∀ i j, Algebra A (D i j)]
    (E : ιi → ιi → ιi → Type*) [∀ i j k, CommRing (E i j k)]
    [∀ i j k, Algebra A (E i j k)]
    [∀ i, Module (Bi i) (N.obj (op (Y i)))] [∀ i j, Module (D i j) (N.obj (op (Pb i j)))]
    [∀ i j k, Module (E i j k) (N.obj (op (Pb₃ i j k)))]
    (e : ∀ i, Bi i ⊗[A] N.obj (op T) ≃ₗ[Bi i] N.obj (op (Y i)))
    (he : ∀ (i) (n : N.obj (op T)),
      e i ((1 : Bi i) ⊗ₜ[A] n) = N.restrictₛₗ (g i).op n)
    (eD : ∀ i j, D i j ⊗[A] N.obj (op T) ≃ₗ[D i j] N.obj (op (Pb i j)))
    (heD : ∀ (i j) (n : N.obj (op T)),
      eD i j ((1 : D i j) ⊗ₜ[A] n) = N.restrictₛₗ (pr₁ i j ≫ g i).op n)
    (eE : ∀ i j k, E i j k ⊗[A] N.obj (op T) ≃ₗ[E i j k] N.obj (op (Pb₃ i j k)))
    (heE : ∀ (i j k) (n : N.obj (op T)), eE i j k ((1 : E i j k) ⊗ₜ[A] n) =
      N.restrictₛₗ (s₁ i j k ≫ pr₁ j k ≫ g j).op n)
    (u : ∀ i j, Bi i →ₐ[A] D i j) (v : ∀ i j, Bi j →ₐ[A] D i j)
    (ψ : ∀ i j, Bi i ⊗[A] Bi j ≃+* D i j)
    (hψ : ∀ (i j) (b : Bi i) (c : Bi j), ψ i j (b ⊗ₜ[A] c) = u i j b * v i j c)
    (u₃ : ∀ i j k, Bi i →ₐ[A] E i j k) (v₃ : ∀ i j k, D j k →ₐ[A] E i j k)
    (ψ₃ : ∀ i j k, Bi i ⊗[A] D j k ≃+* E i j k)
    (hψ₃ : ∀ (i j k) (b : Bi i) (d : D j k),
      ψ₃ i j k (b ⊗ₜ[A] d) = u₃ i j k b * v₃ i j k d)
    (σ₂ : ∀ i j k, D i k →+* E i j k) (σ₃ : ∀ i j k, D i j →+* E i j k)
    (hw : ∀ i j, pr₁ i j ≫ g i = pr₂ i j ≫ g j)
    (hw₂ : ∀ i j k, s₂ i j k ≫ pr₁ i k ≫ g i = s₁ i j k ≫ pr₁ j k ≫ g j)
    (hw₃ : ∀ i j k, s₃ i j k ≫ pr₁ i j ≫ g i = s₁ i j k ≫ pr₁ j k ≫ g j)
    (hsm₁ : ∀ (i j) (b : Bi i) (x : N.obj (op (Y i))),
      N.restrictₛₗ (pr₁ i j).op (b • x) = u i j b • N.restrictₛₗ (pr₁ i j).op x)
    (hsm₂ : ∀ (i j) (b : Bi j) (x : N.obj (op (Y j))),
      N.restrictₛₗ (pr₂ i j).op (b • x) = v i j b • N.restrictₛₗ (pr₂ i j).op x)
    (hsmt₁ : ∀ (i j k) (d : D j k) (x : N.obj (op (Pb j k))),
      N.restrictₛₗ (s₁ i j k).op (d • x) = v₃ i j k d • N.restrictₛₗ (s₁ i j k).op x)
    (hsmt₂ : ∀ (i j k) (d : D i k) (x : N.obj (op (Pb i k))),
      N.restrictₛₗ (s₂ i j k).op (d • x) = σ₂ i j k d • N.restrictₛₗ (s₂ i j k).op x)
    (hsmt₃ : ∀ (i j k) (d : D i j) (x : N.obj (op (Pb i j))),
      N.restrictₛₗ (s₃ i j k).op (d • x) = σ₃ i j k d • N.restrictₛₗ (s₃ i j k).op x)
    (hσ₂u : ∀ (i j k) (b : Bi i), σ₂ i j k (u i k b) = u₃ i j k b)
    (hσ₂v : ∀ (i j k) (c : Bi k), σ₂ i j k (v i k c) = v₃ i j k (v j k c))
    (hσ₃u : ∀ (i j k) (b : Bi i), σ₃ i j k (u i j b) = u₃ i j k b)
    (hσ₃v : ∀ (i j k) (c : Bi j), σ₃ i j k (v i j c) = v₃ i j k (u j k c)) :
    ∃ (f : ∀ i j, (Bi i ⊗[A] Bi j) ⊗[A] N.obj (op T) ≃+ N.obj (op (Pb i j)))
      (f₃ : ∀ i j k,
        (Bi i ⊗[A] (Bi j ⊗[A] Bi k)) ⊗[A] N.obj (op T) →+ N.obj (op (Pb₃ i j k))),
      (∀ i j k, Function.Injective (f₃ i j k)) ∧
      (∀ (i j) (b : Bi i) (n : N.obj (op T)),
        N.restrictₛₗ (pr₁ i j).op (e i (b ⊗ₜ[A] n)) =
          f i j ((b ⊗ₜ[A] (1 : Bi j)) ⊗ₜ[A] n)) ∧
      (∀ (i j) (b : Bi j) (n : N.obj (op T)),
        N.restrictₛₗ (pr₂ i j).op (e j (b ⊗ₜ[A] n)) =
          f i j (((1 : Bi i) ⊗ₜ[A] b) ⊗ₜ[A] n)) ∧
      (∀ (i j k) (b : Bi j) (c : Bi k) (n : N.obj (op T)),
        N.restrictₛₗ (s₁ i j k).op (f j k ((b ⊗ₜ[A] c) ⊗ₜ[A] n)) =
          f₃ i j k (((1 : Bi i) ⊗ₜ[A] (b ⊗ₜ[A] c)) ⊗ₜ[A] n)) ∧
      (∀ (i j k) (b : Bi i) (c : Bi k) (n : N.obj (op T)),
        N.restrictₛₗ (s₂ i j k).op (f i k ((b ⊗ₜ[A] c) ⊗ₜ[A] n)) =
          f₃ i j k ((b ⊗ₜ[A] ((1 : Bi j) ⊗ₜ[A] c)) ⊗ₜ[A] n)) ∧
      ∀ (i j k) (b : Bi i) (c : Bi j) (n : N.obj (op T)),
        N.restrictₛₗ (s₃ i j k).op (f i j ((b ⊗ₜ[A] c) ⊗ₜ[A] n)) =
          f₃ i j k ((b ⊗ₜ[A] (c ⊗ₜ[A] (1 : Bi k))) ⊗ₜ[A] n) := by
  let ψA : ∀ i j, Bi i ⊗[A] Bi j ≃ₐ[A] D i j := fun i j =>
    AlgEquiv.ofRingEquiv (f := ψ i j) fun a => by
      rw [Algebra.TensorProduct.algebraMap_apply, hψ, map_one, mul_one, AlgHom.commutes]
  let ψ₃A : ∀ i j k, Bi i ⊗[A] D j k ≃ₐ[A] E i j k := fun i j k =>
    AlgEquiv.ofRingEquiv (f := ψ₃ i j k) fun a => by
      rw [Algebra.TensorProduct.algebraMap_apply, hψ₃, map_one, mul_one, AlgHom.commutes]
  let Ψ : ∀ i j k, Bi i ⊗[A] (Bi j ⊗[A] Bi k) ≃ₐ[A] E i j k := fun i j k =>
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := A) (A₁ := Bi i)) (ψA j k)).trans
      (ψ₃A i j k)
  have hΨ : ∀ (i j k) (b : Bi i) (c : Bi j) (d : Bi k), Ψ i j k (b ⊗ₜ[A] (c ⊗ₜ[A] d)) =
      u₃ i j k b * v₃ i j k (u j k c * v j k d) := by
    intro i j k b c d
    change ψ₃ i j k (b ⊗ₜ[A] ψ j k (c ⊗ₜ[A] d)) = _
    rw [hψ, hψ₃]
  let fP : ∀ i j, (Bi i ⊗[A] Bi j) ⊗[A] N.obj (op T) ≃+ N.obj (op (Pb i j)) := fun i j =>
    (TensorProduct.congr (ψA i j).toLinearEquiv
      (LinearEquiv.refl A (N.obj (op T)))).toAddEquiv.trans (eD i j).toAddEquiv
  have hfP : ∀ (i j) (x : Bi i ⊗[A] Bi j) (n : N.obj (op T)),
      fP i j (x ⊗ₜ[A] n) = eD i j (ψ i j x ⊗ₜ[A] n) := fun _ _ _ _ => rfl
  let fT : ∀ i j k, (Bi i ⊗[A] (Bi j ⊗[A] Bi k)) ⊗[A] N.obj (op T) ≃+
      N.obj (op (Pb₃ i j k)) := fun i j k =>
    (TensorProduct.congr (Ψ i j k).toLinearEquiv
      (LinearEquiv.refl A (N.obj (op T)))).toAddEquiv.trans (eE i j k).toAddEquiv
  let fTh : ∀ i j k, (Bi i ⊗[A] (Bi j ⊗[A] Bi k)) ⊗[A] N.obj (op T) →+
      N.obj (op (Pb₃ i j k)) := fun i j k => (fT i j k).toAddMonoidHom
  have hfT : ∀ (i j k) (x : Bi i ⊗[A] (Bi j ⊗[A] Bi k)) (n : N.obj (op T)),
      fTh i j k (x ⊗ₜ[A] n) = eE i j k (Ψ i j k x ⊗ₜ[A] n) := fun _ _ _ _ _ => rfl
  refine ⟨fP, fTh, fun i j k => (fT i j k).injective,
    fun i j b n => ?_, fun i j b n => ?_, fun i j k b c n => ?_, fun i j k b c n => ?_,
    fun i j k b c n => ?_⟩
  · rw [restrictₛₗ_baseChange_tmul (g i) (pr₁ i j) A (Bi i) (D i j) (e i) (he i) (eD i j)
      (heD i j) (u i j) (hsm₁ i j) b n, hfP, hψ, map_one, mul_one]
  · rw [restrictₛₗ_baseChange_tmul (g j) (pr₂ i j) A (Bi j) (D i j) (e j) (he j) (eD i j)
      (fun n => (heD i j n).trans (by rw [hw i j])) (v i j) (hsm₂ i j) b n,
      hfP, hψ, map_one, one_mul]
  · rw [hfP, restrictₛₗ_baseChange_tmul (pr₁ j k ≫ g j) (s₁ i j k) A (D j k) (E i j k)
      (eD j k) (heD j k) (eE i j k) (heE i j k) (v₃ i j k) (hsmt₁ i j k) _ n,
      hfT, hΨ, hψ j k b c, map_one, one_mul]
  · rw [hfP, restrictₛₗ_baseChange_tmul (pr₁ i k ≫ g i) (s₂ i j k) A (D i k) (E i j k)
      (eD i k) (heD i k) (eE i j k) (fun n => (heE i j k n).trans (by rw [hw₂ i j k]))
      (σ₂ i j k) (hsmt₂ i j k) _ n,
      hfT, hΨ, hψ i k b c, map_mul, hσ₂u, hσ₂v, map_one, one_mul]
  · rw [hfP, restrictₛₗ_baseChange_tmul (pr₁ i j ≫ g i) (s₃ i j k) A (D i j) (E i j k)
      (eD i j) (heD i j) (eE i j k) (fun n => (heE i j k n).trans (by rw [hw₃ i j k]))
      (σ₃ i j k) (hsmt₃ i j k) _ n,
      hfT, hΨ, hψ i j b c, map_mul, hσ₃u, hσ₃v, map_one, mul_one]

end PresheafOfModules

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  {x : 𝒳}

variable {K I : Type y}
  {Q P : SheafOfModules.{max t u} ((ringStructureSheafCore B S hS p hp .fppf).over x)}
  {N : PresheafOfModules.{max t u} ((ringStructureSheafCore B S hS p hp .fppf).over x).obj}
  (κ : ∀ _ : K, SheafOfModules.uliftForPresentation.{max v w, w, u, u, t}
    (SheafOfModules.unit ((ringStructureSheafCore B S hS p hp .fppf).over x)) ⟶ Q)
  (ι : ∀ _ : I, SheafOfModules.uliftForPresentation.{max v w, w, u, u, t}
    (SheafOfModules.unit ((ringStructureSheafCore B S hS p hp .fppf).over x)) ⟶ P)
  (hQ : IsColimit (Cofan.mk Q κ)) (hP : IsColimit (Cofan.mk P ι))
  (a : Q ⟶ P) (π : P.val ⟶ N) (hπ : PresheafOfModules.IsPresheafCokernel a.val π)

include hp κ ι hQ hP hπ in
/-- **The sheaf condition for a finite family of affine objects whose image in schemes is an fppf
covering family, for the presheaf cokernel of a presentation over an affine object.**

Every ring in sight is a ring of global functions on an underlying scheme, every module of
sections is a module over the ring of sections of the coefficient sheaf of rings at the same
object, and the two are the same ring definitionally
(`AlgebraicGeometry.FibredSite.ringStructureSheafCore_over_obj_obj`).  Over a member of the family
and over a fibre product of two members the ring of global functions on the object covered acts
through the induced map of global functions, so the restriction maps are linear.

The three inputs are: the base-change comparison of the sections of the presheaf cokernel at each
member and at each fibre product of two members
(`SheafOfModules.exists_baseChangeEquiv_of_isPresheafCokernel`, whose bases are
`AlgebraicGeometry.FibredSite.tautBasisOfIsAffineOverCoeffs` and whose objects are affine, the
fibre products by `AlgebraicGeometry.FibredSite.isAffineOver_pullback`); the identification of the
ring of global functions on a fibre product of two members with the tensor product of their rings
(`AlgebraicGeometry.FibredSite.algebra_isPushout_gamma_of_isPullback`); and faithful flatness of
the product of the rings of the members over the ring of the object covered
(`AlgebraicGeometry.FibredSite.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage`).
`PresheafOfModules.exists_pairBaseChange` and
`PresheafOfModules.exists_amitsurDiff₀_data` turn the first two into the degree-zero data of the
Amitsur complex of that product, and
`PresheafOfModules.isSheafFor_ofArrows_of_amitsurDiff₀` concludes.

No coproduct is formed inside the site and no cohomology occurs: the single faithfully flat
algebra of the descent is the finite product of the rings of global functions on the members, and
the double self-products of the covering are the fibre products of pairs of members. -/
theorem isSheafFor_ofArrows_of_isPresheafCokernel_of_fppf {ιi : Type*} [Finite ιi] (W : Over x)
    (hW : IsAffineOver B S hS (p.obj W.left)) (Y : ιi → Over x) (g : ∀ i, Y i ⟶ W)
    (hY : ∀ i, IsAffineOver B S hS (p.obj (Y i).left))
    (hfppf : Presieve.ofArrows (fun i => (BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left))
        (fun i => (BigFppfOver.toScheme B S hS).map (p.map (g i).left)) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj (p.obj W.left))) :
    Presieve.IsSheafFor (N.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{max t u})
      (Presieve.ofArrows Y g) := by
  have hpbs : HasPullbacks 𝒳 := BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS p hp
  let Pb : ιi → ιi → Over x := fun i j => pullback (g i) (g j)
  let q₁ : ∀ i j, Pb i j ⟶ Y i := fun i j => pullback.fst (g i) (g j)
  let q₂ : ∀ i j, Pb i j ⟶ Y j := fun i j => pullback.snd (g i) (g j)
  have hq : ∀ i j, q₁ i j ≫ g i = q₂ i j ≫ g j := fun i j => pullback.condition
  have hPaff : ∀ i j, IsAffineOver B S hS (p.obj (Pb i j).left) := fun i j =>
    isAffineOver_pullback B S hS p hp (g i) (g j) hW (hY i) (hY j)
  let algY : ∀ i, Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤) := fun i =>
    RingHom.toAlgebra ((BigFppfOver.toScheme B S hS).map (p.map (g i).left)).appTop.hom
  let algP : ∀ i j, Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤) := fun i j =>
    RingHom.toAlgebra
      ((BigFppfOver.toScheme B S hS).map (p.map (q₁ i j ≫ g i).left)).appTop.hom
  let mQW : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) (Q.val.obj (op W)) :=
    inferInstanceAs (Module
      (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W)) (Q.val.obj (op W)))
  let mPW : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) (P.val.obj (op W)) :=
    inferInstanceAs (Module
      (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W)) (P.val.obj (op W)))
  let mNW : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) (N.obj (op W)) :=
    inferInstanceAs (Module
      (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W)) (N.obj (op W)))
  let mQY : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
      (Q.val.obj (op (Y i))) := fun i =>
    inferInstanceAs (Module
      (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Y i)))
      (Q.val.obj (op (Y i))))
  let mPY : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
      (P.val.obj (op (Y i))) := fun i =>
    inferInstanceAs (Module
      (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Y i)))
      (P.val.obj (op (Y i))))
  let mNY : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
      (N.obj (op (Y i))) := fun i =>
    inferInstanceAs (Module
      (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Y i)))
      (N.obj (op (Y i))))
  let mQY' : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (Q.val.obj (op (Y i))) := fun i =>
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤))
  let mPY' : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (P.val.obj (op (Y i))) := fun i =>
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤))
  let mNY' : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) (N.obj (op (Y i)))
      := fun i =>
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤))
  have twQY : ∀ i, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤) (Q.val.obj (op (Y i))) := fun _ =>
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twPY : ∀ i, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤) (P.val.obj (op (Y i))) := fun _ =>
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twNY : ∀ i, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤) (N.obj (op (Y i))) := fun _ =>
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let mQP : ∀ i j, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤)
      (Q.val.obj (op (Pb i j))) := fun i j =>
    inferInstanceAs (Module
      (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Pb i j)))
      (Q.val.obj (op (Pb i j))))
  let mPP : ∀ i j, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤)
      (P.val.obj (op (Pb i j))) := fun i j =>
    inferInstanceAs (Module
      (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Pb i j)))
      (P.val.obj (op (Pb i j))))
  let mNP : ∀ i j, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤)
      (N.obj (op (Pb i j))) := fun i j =>
    inferInstanceAs (Module
      (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Pb i j)))
      (N.obj (op (Pb i j))))
  let mQP' : ∀ i j, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (Q.val.obj (op (Pb i j))) := fun i j =>
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤))
  let mPP' : ∀ i j, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (P.val.obj (op (Pb i j))) := fun i j =>
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤))
  let mNP' : ∀ i j, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (N.obj (op (Pb i j))) := fun i j =>
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤))
  have twQP : ∀ i j, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤) (Q.val.obj (op (Pb i j))) := fun
      _ _ =>
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twPP : ∀ i j, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤) (P.val.obj (op (Pb i j))) := fun
      _ _ =>
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twNP : ∀ i j, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤) (N.obj (op (Pb i j))) := fun _ _
      =>
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hmem : ∀ i, ∃ e : Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
      ⊗[Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)] (N.obj (op W))
      ≃ₗ[Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)] N.obj (op (Y i)),
      ∀ n, e ((1 : Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)) ⊗ₜ n) = N.restrictₛₗ
          (g i).op n := fun i =>
    SheafOfModules.exists_baseChangeEquiv_of_isPresheafCokernel (N := N) κ ι (g i)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
      (tautBasisOfIsAffineOverCoeffs B S hS p hp κ hQ W hW
        (sectionRingEquivGamma B S hS p hp .fppf W) (fun _ _ => rfl))
      (tautBasisOfIsAffineOverCoeffs B S hS p hp κ hQ (Y i) (hY i)
        (sectionRingEquivGamma B S hS p hp .fppf (Y i)) (fun _ _ => rfl))
      (tautBasisOfIsAffineOverCoeffs B S hS p hp ι hP W hW
        (sectionRingEquivGamma B S hS p hp .fppf W) (fun _ _ => rfl))
      (tautBasisOfIsAffineOverCoeffs B S hS p hp ι hP (Y i) (hY i)
        (sectionRingEquivGamma B S hS p hp .fppf (Y i)) (fun _ _ => rfl))
      (fun k => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp κ hQ W hW _ _ k)
      (fun k => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp κ hQ (Y i) (hY i) _ _ k)
      (fun j => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp ι hP W hW _ _ j)
      (fun j => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp ι hP (Y i) (hY i) _ _ j)
      { toFun := fun c => Q.val.map (g i).op c
        map_add' := map_add (Q.val.map (g i).op).hom
        map_smul' := fun c u => (Q.val.map_smul (g i).op c u).symm ▸ rfl }
      (fun _ => rfl)
      { toFun := fun c => P.val.map (g i).op c
        map_add' := map_add (P.val.map (g i).op).hom
        map_smul' := fun c u => (P.val.map_smul (g i).op c u).symm ▸ rfl }
      (fun _ => rfl)
      { toFun := fun c => N.map (g i).op c
        map_add' := map_add (N.map (g i).op).hom
        map_smul' := fun c u => (N.map_smul (g i).op c u).symm ▸ rfl }
      (fun _ => rfl) a π hπ
      (a.val.app (op W)).hom (fun _ => rfl)
      (π.app (op W)).hom (fun _ => rfl)
      (a.val.app (op (Y i))).hom (fun _ => rfl)
      (π.app (op (Y i))).hom (fun _ => rfl)
  have hpair : ∀ i j,
      ∃ e : Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤)
          ⊗[Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)] (N.obj (op W))
          ≃ₗ[Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤)] N.obj (op (Pb i j)),
      ∀ n, e ((1 : Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤)) ⊗ₜ n) =
          N.restrictₛₗ (q₁ i j ≫ g i).op n := fun i j =>
    SheafOfModules.exists_baseChangeEquiv_of_isPresheafCokernel (N := N) κ ι (q₁ i j ≫ g i)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤)
      (tautBasisOfIsAffineOverCoeffs B S hS p hp κ hQ W hW
        (sectionRingEquivGamma B S hS p hp .fppf W) (fun _ _ => rfl))
      (tautBasisOfIsAffineOverCoeffs B S hS p hp κ hQ (Pb i j) (hPaff i j)
        (sectionRingEquivGamma B S hS p hp .fppf (Pb i j)) (fun _ _ => rfl))
      (tautBasisOfIsAffineOverCoeffs B S hS p hp ι hP W hW
        (sectionRingEquivGamma B S hS p hp .fppf W) (fun _ _ => rfl))
      (tautBasisOfIsAffineOverCoeffs B S hS p hp ι hP (Pb i j) (hPaff i j)
        (sectionRingEquivGamma B S hS p hp .fppf (Pb i j)) (fun _ _ => rfl))
      (fun k => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp κ hQ W hW _ _ k)
      (fun k => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp κ hQ (Pb i j) (hPaff i j) _ _ k)
      (fun l => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp ι hP W hW _ _ l)
      (fun l => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp ι hP (Pb i j) (hPaff i j) _ _ l)
      { toFun := fun c => Q.val.map (q₁ i j ≫ g i).op c
        map_add' := map_add (Q.val.map (q₁ i j ≫ g i).op).hom
        map_smul' := fun c u => (Q.val.map_smul (q₁ i j ≫ g i).op c u).symm ▸ rfl }
      (fun _ => rfl)
      { toFun := fun c => P.val.map (q₁ i j ≫ g i).op c
        map_add' := map_add (P.val.map (q₁ i j ≫ g i).op).hom
        map_smul' := fun c u => (P.val.map_smul (q₁ i j ≫ g i).op c u).symm ▸ rfl }
      (fun _ => rfl)
      { toFun := fun c => N.map (q₁ i j ≫ g i).op c
        map_add' := map_add (N.map (q₁ i j ≫ g i).op).hom
        map_smul' := fun c u => (N.map_smul (q₁ i j ≫ g i).op c u).symm ▸ rfl }
      (fun _ => rfl) a π hπ
      (a.val.app (op W)).hom (fun _ => rfl)
      (π.app (op W)).hom (fun _ => rfl)
      (a.val.app (op (Pb i j))).hom (fun _ => rfl)
      (π.app (op (Pb i j))).hom (fun _ => rfl)
  choose em hem using hmem
  choose ep hep using hpair
  have hpairf : ∀ i j, ∃ F : (Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
      ⊗[Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)]
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y j).left), ⊤))
            ⊗[Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)] (N.obj (op W)) →+ N.obj (op
            (Pb i j)),
      Function.Injective F ∧
        (∀ (b : Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)) (n),
          N.restrictₛₗ (q₁ i j).op (em i (b ⊗ₜ n)) =
            F ((b ⊗ₜ[Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)]
                (1 : Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y j).left), ⊤))) ⊗ₜ n)) ∧
          ∀ (b : Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y j).left), ⊤)) (n),
            N.restrictₛₗ (q₂ i j).op (em j (b ⊗ₜ n)) =
              F (((1 : Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤))
                  ⊗ₜ[Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)] b) ⊗ₜ n) := fun i j =>
                  by
    let a₁ : Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤) :=
      RingHom.toAlgebra
        ((BigFppfOver.toScheme B S hS).map (p.map (q₁ i j).left)).appTop.hom
    let a₂ : Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y j).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤) :=
      RingHom.toAlgebra
        ((BigFppfOver.toScheme B S hS).map (p.map (q₂ i j).left)).appTop.hom
    have t₁ : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤) :=
      IsScalarTower.of_algebraMap_eq fun c => by
        change (((BigFppfOver.toScheme B S hS).map (p.map (q₁ i j ≫ g i).left)).appTop) c = _
        rw [Over.comp_left, Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_appTop]
        rfl
    have t₂ : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y j).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤) :=
      IsScalarTower.of_algebraMap_eq fun c => by
        change (((BigFppfOver.toScheme B S hS).map (p.map (q₁ i j ≫ g i).left)).appTop) c = _
        rw [hq i j, Over.comp_left, Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_appTop]
        rfl
    have hpush : Algebra.IsPushout Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y j).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤) :=
      algebra_isPushout_gamma_of_isPullback B S hS p hp
        (IsPullback.of_hasPullback (g i) (g j)) hW (hY i) (hY j) rfl rfl rfl rfl
    exact PresheafOfModules.exists_pairBaseChange (g i) (g j) (q₁ i j) (q₂ i j) (hq i j)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y j).left), ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤)
      (em i) (hem i) (em j) (hem j) (ep i j) (hep i j)
      (fun b u => N.map_smul (q₁ i j).op b u) (fun b u => N.map_smul (q₂ i j).op b u)
  choose F hFinj hnat₁ hnat₂ using hpairf
  obtain ⟨eW, eV, hbijW, honeW, hinjV, hd₀⟩ :=
    PresheafOfModules.exists_amitsurDiff₀_data (N := N) g q₁ q₂
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (fun i => Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤))
      (fun i => (em i).toAddEquiv) (fun i n => hem i n) F hFinj hnat₁ hnat₂
  have hff : Module.FaithfullyFlat Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (∀ i, Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)) :=
    faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage B S hS p Y g hW hY hfppf fun _ => rfl
  exact PresheafOfModules.isSheafFor_ofArrows_of_amitsurDiff₀ g
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
    (∀ i, Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)) Pb q₁ q₂ hq
    eW hbijW honeW eV hinjV hd₀

include hp κ ι hQ hP in
/-- **The same for the cokernel of the presenting morphism computed in presheaves of modules**,
whose projection is a presheaf cokernel by
`PresheafOfModules.isPresheafCokernel_cokernelπ`.  The preceding statement is for a morphism with
that property rather than for the categorical cokernel because its proof introduces module
structures on the sections, which a statement about a `noncomputable` construction cannot carry
inside a theorem. -/
theorem isSheafFor_ofArrows_cokernel_of_fppf {ιi : Type*} [Finite ιi] (W : Over x)
    (hW : IsAffineOver B S hS (p.obj W.left)) (Y : ιi → Over x) (g : ∀ i, Y i ⟶ W)
    (hY : ∀ i, IsAffineOver B S hS (p.obj (Y i).left))
    (hfppf : Presieve.ofArrows (fun i => (BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left))
        (fun i => (BigFppfOver.toScheme B S hS).map (p.map (g i).left)) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj (p.obj W.left))) :
    Presieve.IsSheafFor
      ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{max t u})
      (Presieve.ofArrows Y g) :=
  isSheafFor_ofArrows_of_isPresheafCokernel_of_fppf B S hS p hp κ ι hQ hP a (cokernel.π a.val)
    (PresheafOfModules.isPresheafCokernel_cokernelπ a.val) W hW Y g hY hfppf

include hp κ ι hQ hP in
/-- **The sheaf condition for the cokernel of a presenting morphism computed in presheaves of
modules, for every finite covering family of affine objects of an affine object of a slice of the
associated fppf site.**  Neither flatness nor any fppf-ness of the family is assumed.

This is the hypothesis `hsheaf` of
`AlgebraicGeometry.FibredSite.surjective_val_app_of_isSheafFor_affine_of_isColimit`, in the shape
that statement asks for it.  The reduction to the fppf case is
`AlgebraicGeometry.FibredSite.isSheafFor_cokernel_affine_of_isSheafFor_fppf`: a covering sieve of
an affine object contains a finite family of affine objects which is fppf in schemes, and the
amalgamation produced over that refinement is identified with the one asked for by separatedness
at the members, which are affine.  The fppf case is
`AlgebraicGeometry.FibredSite.isSheafFor_ofArrows_cokernel_of_fppf`. -/
theorem isSheafFor_cokernel_of_isAffineOver (W : Over x)
    (hW : IsAffineOver B S hS (p.obj W.left)) :
    ∀ (k : ℕ) (Y : Fin k → Over x) (g : ∀ i, Y i ⟶ W),
      (∀ i, IsAffineOver B S hS (p.obj (Y i).left)) →
      Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) W →
        Presieve.IsSheafFor
          ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{max t u})
          (Presieve.ofArrows Y g) :=
  isSheafFor_cokernel_affine_of_isSheafFor_fppf B S hS p hp κ ι hQ hP a W hW
    fun _ Y' g' hY' _ hfp =>
      isSheafFor_ofArrows_cokernel_of_fppf B S hS p hp κ ι hQ hP a W hW Y' g' hY' hfp


section Surjectivity

variable [HasSheafify ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
    AddCommGrpCat.{max t u}]
  [((BigFppfOver.associatedTopology B S hS p .fppf).over x).WEqualsLocallyBijective
    AddCommGrpCat.{max t u}]
  {M : SheafOfModules.{max t u} ((ringStructureSheafCore B S hS p hp .fppf).over x)}
  (b : P ⟶ M) [Epi b] (hab' : a.val ≫ b.val = 0)

include hp κ ι hQ hP hab' in
/-- **The presenting morphism of a presentation of a sheaf of modules on a slice of the associated
fppf site is surjective on the sections over an affine object**, with no hypothesis beyond the
presentation itself.

This is `AlgebraicGeometry.FibredSite.surjective_val_app_of_isSheafFor_affine_of_isColimit` with
both of its hypotheses discharged: the sheaf condition for the presheaf cokernel by
`AlgebraicGeometry.FibredSite.isSheafFor_cokernel_of_isAffineOver`, and injectivity of restriction
to the members of a covering family by
`AlgebraicGeometry.FibredSite.injective_map_cokernel_of_isAffineOver`.

The two coproducts of the presentation carry their tautological generators and the witnesses that
they are coproducts, because the base-change comparison for the presheaf cokernel uses the
generators of the relations as well as the generators of the module. -/
theorem surjective_val_app_of_isColimit_of_isAffineOver (hab : a ≫ b = 0)
    (hM : IsColimit (CokernelCofork.ofπ b hab)) (W : Over x)
    (hW : IsAffineOver B S hS (p.obj W.left)) :
    Function.Surjective (b.val.app (op W)) :=
  surjective_val_app_of_isSheafFor_affine_of_isColimit B S hS p hp a b hab' hab hM W hW
    (isSheafFor_cokernel_of_isAffineOver B S hS p hp κ ι hQ hP a W hW)
    (injective_map_cokernel_of_isAffineOver B S hS p hp κ ι hQ hP a)

end Surjectivity


include hp in
/-- **The sections of a globally presented sheaf of modules over an affine object of the slice site
at an affine object are spanned by the restrictions of its sections over that affine object**, with
no hypothesis beyond the presentation.

This is `AlgebraicGeometry.FibredSite.globalSectionSpan_eq_top_of_hasGlobalPresentation` with its
sheaf-condition hypothesis discharged by
`AlgebraicGeometry.FibredSite.isSheafFor_cokernel_of_isAffineOver`, which is the form that
hypothesis is stated in.

It is the hypothesis `hgen` of
`AlgebraicGeometry.FibredSite.isAffineLocallySpanned_of_globalSectionSpan_eq_top` with
quasi-coherence of the module replaced by a global presentation on the slice itself.  The two are
not the same condition: `SheafOfModules.IsQuasicoherentOnSite` supplies global presentations only
after restriction to the members of a covering family of an object, never over the object
itself. -/
theorem globalSectionSpan_eq_top_of_hasGlobalPresentation_of_isAffineOver
    (hx : IsAffineOver B S hS (p.obj x))
    (M : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x))
    (hM : M.HasGlobalPresentation) (W : Over x)
    (hW : IsAffineOver B S hS (p.obj W.left)) :
    M.globalSectionSpan (Over.mkIdTerminal (X := x)) W = ⊤ :=
  globalSectionSpan_eq_top_of_hasGlobalPresentation B S hS p hp hx M hM
    (fun κ' ι' hQ' hP' a' V hV k Y' g' hY' hcov =>
      isSheafFor_cokernel_of_isAffineOver B S hS p hp κ' ι' hQ' hP' a' V hV k Y' g' hY' hcov) W hW


end AlgebraicGeometry.FibredSite

end
