module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.RingTheory.Regular.Category
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.RingTheory.Dualizing.ExtRegularElement
public import StacksFrontier.RingTheory.Dualizing.MaximalIdealPowerTorsion

/-!
# The contravariant long exact Ext sequence of a short exact sequence of modules

A short exact sequence `0 → M₁ → M₂ → M₃ → 0` of modules over a commutative ring `A` becomes,
in the derived category of `A`-modules, a distinguished triangle on the complexes concentrated
in degree `0`. Applying the additive Yoneda functor into a fixed object `K` of the derived
category turns that triangle into a long exact sequence of the integer-graded groups
`Ext^i(Mⱼ, K)`, contravariant in the module variable. This file records that sequence, the
precomposition maps that appear in it, and the two bijectivity criteria it yields when the
groups attached to one of the three modules vanish in two consecutive degrees.

`StacksFrontier.RingTheory.Dualizing.ExtRegularElement` already contains this sequence for the
single short exact sequence `0 → M →^f M → M/fM → 0` attached to an `M`-regular element `f`.
The statements here are the same ones with that sequence replaced by an arbitrary short exact
short complex, and `ExtRegularElement`'s maps are exhibited as instances of the general ones.

## Main definitions

* `Dualizing.objExtInto` is integer-graded Ext from an object of `ModuleCat A` into an object
  of the derived category; it agrees with `Dualizing.moduleExtInto` on `ModuleCat.of A M`.
* `Dualizing.objExtPrecomp` is the contravariant map on Ext induced by a morphism of modules.
* `Dualizing.extSESConnecting` is the connecting map of a short exact short complex.

## Main results

* `Dualizing.objExtPrecomp_id` and `Dualizing.objExtPrecomp_comp` give the contravariant
  functoriality of precomposition and `Dualizing.objExtPrecomp_smul` its linearity in the
  morphism; `Dualizing.objExtPrecomp_smul_id` is the resulting value on a scalar multiple of
  the identity.
* `Dualizing.exact_objExtPrecomp_g_objExtPrecomp_f`,
  `Dualizing.exact_objExtPrecomp_f_extSESConnecting` and
  `Dualizing.exact_extSESConnecting_objExtPrecomp_g` are the three recurring exactness conditions
  of the long exact sequence.
* `Dualizing.bijective_objExtPrecomp_f_of_subsingleton_third` and
  `Dualizing.bijective_extSESConnecting_of_subsingleton_second` are the bijectivity criteria.
* `Dualizing.extFromQuotient_eq_objExtPrecomp` and
  `Dualizing.extSESConnecting_eq_extConnecting` identify the maps of
  `StacksFrontier.RingTheory.Dualizing.ExtRegularElement` with the general ones.

## Implementation notes

The objects of a `CategoryTheory.ShortComplex (ModuleCat A)` are objects of `ModuleCat A`, not
bare types, so the Ext groups are indexed here by `Dualizing.objExtInto`, which takes an object
of `ModuleCat A`. On `ModuleCat.of A M` this is `Dualizing.moduleExtInto M` by definition, so
nothing has to be transported: `Dualizing.moduleExtInto_eq_objExtInto`,
`Dualizing.extFromQuotient_eq_objExtPrecomp` and `Dualizing.extSESConnecting_eq_extConnecting` all
hold by `rfl`.

`Dualizing.extPrecomp` in `StacksFrontier.RingTheory.Dualizing.MaximalIdealPowerTorsion` is the
same construction for a linear map of bare types, taken as an additive map;
`Dualizing.extPrecomp_eq_objExtPrecomp` records that it is the underlying additive map of the
one here. The version here is `A`-linear, and it is stated for a morphism of `ModuleCat A`, which
is what a `CategoryTheory.ShortComplex` supplies.

The long exact sequence is expressed by its three exactness conditions rather than by an
`Mathlib.Algebra.Homology.ComposableArrows`-style object, matching the form used in
`StacksFrontier.RingTheory.Dualizing.ExtRegularElement`. No boundedness or finiteness hypothesis
is needed: the target `K` is an arbitrary object of the derived category.

## References

* [Stacks Project, Lemma 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated Pretriangulated.Opposite DerivedCategory
open Pointwise

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Dualizing

variable {A : Type u} [CommRing A]

/-- The integer-graded Ext group from an object `M` of `ModuleCat A` into an object `K` of the
derived category of `A`-modules. -/
noncomputable abbrev objExtInto (M : ModuleCat.{v} A)
    (K : DerivedCategory (ModuleCat.{v} A)) (i : ℤ) :=
  DerivedCategory.Ext ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) K i

/-- Ext out of an `A`-module and Ext out of the corresponding object of `ModuleCat A` are the
same group. -/
theorem moduleExtInto_eq_objExtInto (M : Type v) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (i : ℤ) :
    moduleExtInto M K i = objExtInto (ModuleCat.of A M) K i :=
  rfl

/-- The map on Ext induced contravariantly by a morphism `φ : M ⟶ N` of `A`-modules, given by
precomposition with `φ` in the derived category. -/
@[simps]
noncomputable def objExtPrecomp {M N : ModuleCat.{v} A} (φ : M ⟶ N)
    (K : DerivedCategory (ModuleCat.{v} A)) (i : ℤ) :
    objExtInto N K i →ₗ[A] objExtInto M K i where
  toFun x := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map φ ≫ x
  map_add' := by intros; simp
  map_smul' := by intros; simp

/-- Precomposition with the identity is the identity on Ext. -/
@[simp]
theorem objExtPrecomp_id (M : ModuleCat.{v} A) (K : DerivedCategory (ModuleCat.{v} A)) (i : ℤ) :
    objExtPrecomp (𝟙 M) K i = LinearMap.id := by
  ext x
  simp

/-- Precomposition on Ext is contravariantly functorial. -/
theorem objExtPrecomp_comp {M N P : ModuleCat.{v} A} (φ : M ⟶ N) (ψ : N ⟶ P)
    (K : DerivedCategory (ModuleCat.{v} A)) (i : ℤ) :
    objExtPrecomp (φ ≫ ψ) K i = (objExtPrecomp φ K i).comp (objExtPrecomp ψ K i) := by
  ext x
  simp

/-- Precomposition on Ext is `A`-linear in the morphism it precomposes with. -/
theorem objExtPrecomp_smul {M N : ModuleCat.{v} A} (a : A) (φ : M ⟶ N)
    (K : DerivedCategory (ModuleCat.{v} A)) (i : ℤ) :
    objExtPrecomp (a • φ) K i = a • objExtPrecomp φ K i := by
  ext x
  simp [Functor.map_smul, Linear.smul_comp]

/-- Precomposition with a scalar multiple of the identity is that scalar acting on Ext. -/
theorem objExtPrecomp_smul_id (M : ModuleCat.{v} A) (K : DerivedCategory (ModuleCat.{v} A))
    (a : A) (i : ℤ) :
    objExtPrecomp (a • (𝟙 M)) K i = LinearMap.lsmul A (objExtInto M K i) a := by
  rw [objExtPrecomp_smul, objExtPrecomp_id]
  ext x
  simp

/-- The connecting map of the contravariant long exact Ext sequence of a short exact short
complex of `A`-modules, obtained from the third map of the associated distinguished triangle. -/
noncomputable def extSESConnecting {S : ShortComplex (ModuleCat.{v} A)} (hS : S.ShortExact)
    (K : DerivedCategory (ModuleCat.{v} A)) (i : ℤ) :
    objExtInto S.X₁ K i →ₗ[A] objExtInto S.X₃ K (i + 1) :=
  (Linear.leftComp A _ hS.singleTriangle.mor₃).comp
    ((Linear.rightComp A _
      ((shiftFunctorAdd' (DerivedCategory (ModuleCat.{v} A)) i 1 (i + 1) rfl).inv.app K)).comp
        ((shiftFunctor (DerivedCategory (ModuleCat.{v} A)) 1).mapLinearMap A))

section

variable {S : ShortComplex (ModuleCat.{v} A)} (hS : S.ShortExact)
  (K : DerivedCategory (ModuleCat.{v} A)) (i : ℤ)

/-- The additive Yoneda functor into `K` turns the opposite of the distinguished triangle of a
short exact sequence into a homology sequence, so its exactness statements are those of `Ext`. -/
private theorem singleTriangle_op_distinguished (hS : S.ShortExact) :
    (Pretriangulated.triangleOpEquivalence _).functor.obj (Opposite.op hS.singleTriangle) ∈
      distTriang (DerivedCategory (ModuleCat.{v} A))ᵒᵖ :=
  Pretriangulated.op_distinguished _ hS.singleTriangle_distinguished

/-- The connecting map is the connecting map of the homology sequence of the Yoneda functor. -/
private theorem coe_extSESConnecting_eq (hS : S.ShortExact) :
    ⇑(extSESConnecting hS K i) = ⇑((preadditiveYoneda.obj K).homologySequenceδ
      ((Pretriangulated.triangleOpEquivalence _).functor.obj (Opposite.op hS.singleTriangle))
      i (i + 1) rfl) := by
  funext x
  exact (Pretriangulated.preadditiveYoneda_homologySequenceδ_apply
    (T := hS.singleTriangle) i (i + 1) rfl x).symm

include hS in
/-- Exactness of the long exact sequence at the Ext group of the middle module. -/
theorem exact_objExtPrecomp_g_objExtPrecomp_f :
    Function.Exact (objExtPrecomp S.g K i) (objExtPrecomp S.f K i) := by
  have h := (preadditiveYoneda.obj K).homologySequence_exact₂ _
    (singleTriangle_op_distinguished hS) i
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/-- Exactness of the long exact sequence at the Ext group of the first module. -/
theorem exact_objExtPrecomp_f_extSESConnecting :
    Function.Exact (objExtPrecomp S.f K i) (extSESConnecting hS K i) := by
  have h := (preadditiveYoneda.obj K).homologySequence_exact₃ _
    (singleTriangle_op_distinguished hS) i (i + 1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  rwa [coe_extSESConnecting_eq]

/-- Exactness of the long exact sequence at the Ext group of the third module. -/
theorem exact_extSESConnecting_objExtPrecomp_g :
    Function.Exact (extSESConnecting hS K i) (objExtPrecomp S.g K (i + 1)) := by
  have h := (preadditiveYoneda.obj K).homologySequence_exact₁ _
    (singleTriangle_op_distinguished hS) i (i + 1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  rwa [coe_extSESConnecting_eq]

/-- A linear map whose source is a subsingleton is injective when the previous map is exact. -/
private theorem injective_of_exact_of_subsingleton {M N P : Type*} [AddCommGroup M]
    [AddCommGroup N] [AddCommGroup P] [Module A M] [Module A N] [Module A P] {f : M →ₗ[A] N}
    {g : N →ₗ[A] P} (hfg : Function.Exact f g) (h : Subsingleton M) : Function.Injective g := by
  intro x y hxy
  obtain ⟨z, hz⟩ := hfg (x - y) |>.mp (by rw [map_sub, hxy, sub_self])
  rw [h.elim z 0, map_zero] at hz
  exact sub_eq_zero.mp hz.symm

include hS in
/-- **Injectivity at the left end of the long exact sequence.** If the Ext groups of the first
module of a short exact sequence vanish in degree `i`, then precomposition with the second map of
the sequence is injective on Ext in degree `j = i + 1`: the kernel of that precomposition is the
range of the connecting map out of degree `i`. -/
theorem injective_objExtPrecomp_g_of_subsingleton_first (i j : ℤ) (hij : i + 1 = j)
    (h : Subsingleton (objExtInto S.X₁ K i)) :
    Function.Injective (objExtPrecomp S.g K j) := by
  subst hij
  exact injective_of_exact_of_subsingleton (exact_extSESConnecting_objExtPrecomp_g hS K i) h

include hS in
/-- **Surjectivity at the right end of the long exact sequence.** If the Ext groups of the third
module of a short exact sequence vanish in degree `j = i + 1`, then precomposition with the first
map of the sequence is surjective on Ext in degree `i`: its range is the kernel of the connecting
map out of degree `i`. -/
theorem surjective_objExtPrecomp_f_of_subsingleton_third (i j : ℤ) (hij : i + 1 = j)
    (h : Subsingleton (objExtInto S.X₃ K j)) :
    Function.Surjective (objExtPrecomp S.f K i) := by
  subst hij
  intro y
  exact (exact_objExtPrecomp_f_extSESConnecting hS K i y).mp (h.elim _ 0)

include hS in
/-- If the Ext groups of the third module vanish in degrees `i` and `i + 1`, then
precomposition with the first map of the short exact sequence is bijective on Ext in
degree `i`.

Its surjectivity half is `surjective_objExtPrecomp_f_of_subsingleton_third` above, which is the
same statement one-sided; only the kernel computation is particular to this lemma. -/
theorem bijective_objExtPrecomp_f_of_subsingleton_third
    (h₀ : Subsingleton (objExtInto S.X₃ K i))
    (h₁ : Subsingleton (objExtInto S.X₃ K (i + 1))) :
    Function.Bijective (objExtPrecomp S.f K i) := by
  exact ⟨injective_of_exact_of_subsingleton (exact_objExtPrecomp_g_objExtPrecomp_f hS K i) h₀,
    surjective_objExtPrecomp_f_of_subsingleton_third hS K i (i + 1) rfl h₁⟩

/-- If the Ext groups of the middle module vanish in degrees `i` and `i + 1`, then the
connecting map out of degree `i` is bijective. -/
theorem bijective_extSESConnecting_of_subsingleton_second
    (h₀ : Subsingleton (objExtInto S.X₂ K i))
    (h₁ : Subsingleton (objExtInto S.X₂ K (i + 1))) :
    Function.Bijective (extSESConnecting hS K i) := by
  refine ⟨injective_of_exact_of_subsingleton
    (exact_objExtPrecomp_f_extSESConnecting hS K i) h₀, fun y => ?_⟩
  exact (exact_extSESConnecting_objExtPrecomp_g hS K i y).mp (h₁.elim _ 0)

end

/-- The map on Ext induced by the quotient `M → M/fM` is the precomposition map of that
quotient morphism. -/
theorem extFromQuotient_eq_objExtPrecomp (M : Type v) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (f : A) (i : ℤ) :
    extFromQuotient M K f i =
      objExtPrecomp (ModuleCat.ofHom (f • (⊤ : Submodule A M)).mkQ) K i :=
  rfl

/-- **The additive precomposition map of a linear map is the underlying additive map of the
`A`-linear precomposition map of the corresponding morphism of `ModuleCat A`.** The two are the
same construction, written once for bare types and once for objects of `ModuleCat A`. -/
theorem extPrecomp_eq_objExtPrecomp {N N' : Type u} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (φ : N →ₗ[A] N')
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    extPrecomp φ K i = (objExtPrecomp (ModuleCat.ofHom φ) K i).toAddMonoidHom :=
  AddMonoidHom.ext fun x => ShiftedHom.mk₀_comp _ _ _ x

/-- The connecting map of the short exact sequence `0 → M →^f M → M/fM → 0` attached to an
`M`-regular element `f` is the connecting map of that short exact sequence. -/
theorem extSESConnecting_eq_extConnecting (M : Type v) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (f : A) (hreg : IsSMulRegular M f) (i : ℤ) :
    extSESConnecting (hreg.smulShortComplex_shortExact (M := ModuleCat.of A M)) K i =
      extConnecting M K f hreg i :=
  rfl

end Dualizing

end
