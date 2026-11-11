module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.Algebra.Module.BalancedTensorProduct
public import StacksFrontier.Homology.Perfect.FiniteTorDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The balanced derived tensor product over a possibly noncommutative ring

Let `Λ` be a ring, not assumed commutative. Tensoring a right `Λ`-module with a left `Λ`-module
is the balanced tensor product `N ⊗_Λ M` of
`StacksDraft.BalancedTensorProduct`, and it is the object part of a bifunctor

`ModuleCat Λᵐᵒᵖ ⥤ ModuleCat Λ ⥤ ModuleCat ℤ`

which, for fixed `N`, is a left adjoint — its right adjoint sends an abelian group `Q` to the
left `Λ`-module `Hom_ℤ(N, Q)` with `(a · f)(n) = f(n a)`. Being a left adjoint it is right exact
and commutes with the countable colimits needed for Stacks 0794, so it has a total left derived
functor on the unbounded derived category `D(Λ)`. The resulting bifunctor, together with the
comparison exhibiting it as that total left derived functor, is a term of
`StacksDraft.Perfect.BalancedDerivedTensoring Λ`.

## Main definitions

* `StacksDraft.Perfect.balancedTensorFunctor`: the ordinary balanced tensoring bifunctor
  `ModuleCat Λᵐᵒᵖ ⥤ ModuleCat Λ ⥤ ModuleCat ℤ`.
* `StacksDraft.Perfect.balancedDerivedTensoring`: a term of `BalancedDerivedTensoring Λ`, for an
  arbitrary ring `Λ` whose underlying type has a copy in the module universe.
* `StacksDraft.Perfect.HasFiniteTorDimensionCanonical` ([stacks 03TN]): finite Tor dimension of
  an object of `D(Λ)`, read off that construction and so taking no parameter.

## Main results

* `StacksDraft.Perfect.preservesColimits_balancedTensorFunctor_obj` ([stacks 09LL]): tensoring
  with a fixed right `Λ`-module commutes with arbitrary colimits, in particular it is right
  exact.
* `StacksDraft.Perfect.preservesColimits_balancedTensorFunctor_flip_obj` ([stacks 09LL]):
  tensoring with a fixed left `Λ`-module commutes with arbitrary colimits, in particular it is
  right exact.
* `StacksDraft.Perfect.nonempty_balancedDerivedTensoring`: the hypothesis structure of
  `StacksDraft.Perfect.isPerfect_iff_hasFiniteTorDimension_and_finite_homology` ([stacks 03TO])
  is inhabited.
* `StacksDraft.Perfect.isPerfect_iff_hasFiniteTorDimension_balancedDerivedTensoring`
  ([stacks 03TO]): that characterization of the perfect objects with its parameter supplied.
* `StacksDraft.Perfect.hasFiniteTorDimensionCanonical_iff`: the parameter-free finite Tor
  dimension agrees with the parameterized one at every parameter.

## Implementation notes

The ordinary bifunctor is built from the universal property of the balanced tensor product: a
morphism out of `N ⊗_Λ M` is produced by lifting a balanced biadditive map, and two morphisms out
of it which agree on pure tensors are equal. The right adjoint is `Q ↦ Hom_ℤ(N, Q)` and the
adjunction is the currying bijection of the universal property, which is what supplies the
exactness hypotheses of Stacks 0794.

The derived functor is obtained in two steps. Stacks 0794 produces a *pointwise* left derived
functor along `Qh : K(Λ) ⥤ D(Λ)` for the class `P` of projective modules, using that a bounded
above acyclic complex of projectives is K-projective and hence annihilated by every additive
functor up to homotopy. That is then transported from the homotopy category to the category of
complexes: the two localizations `Qh` and `Q` differ by the quotient functor
`K(Λ) ⥤ D(Λ)`, and a right Kan extension along a localization stays one after precomposition
with a functor whose whiskering is fully faithful, which is `isRightKanExtension_precomp` below.
Naturality in the right module is packaged by `leftDerivedBifunctor`, which derives a bifunctor
one variable at a time.

An abelian group is the same thing as a `ℤ`-module, but the `Module ℤ` structure obtained from
an `AddCommGroup` and the one carried by an object of `ModuleCat ℤ` are not syntactically the
same, so `intLinearMapOfAddHom` turns an additive map into a `ℤ`-linear one for whichever
pair of structures is at hand.

`Small.{v} Λ` is needed only here, at the construction: the regular right module and the module
`Hom_ℤ(N, Q)` have to live in the module universe for `ModuleCat.{v} Λ` to have enough
projectives. It is not a field of `BalancedDerivedTensoring`.

## References

* [Stacks Project, Tag 09LL](https://stacks.math.columbia.edu/tag/09LL)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 03TN](https://stacks.math.columbia.edu/tag/03TN)
* [Stacks Project, Tag 03TO](https://stacks.math.columbia.edu/tag/03TO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

universe u v

variable (Λ : Type u) [Ring Λ]

/-! ### The ordinary balanced tensor bifunctor -/

/-- An additive map between abelian groups as a `ℤ`-linear map, for any `ℤ`-module structures
on the source and the target. -/
def intLinearMapOfAddHom {X Y : Type*}
    [AddCommGroup X] [AddCommGroup Y] [Module ℤ X] [Module ℤ Y]
    (f : X →+ Y) : X →ₗ[ℤ] Y where
  __ := f
  map_smul' z x := by
    convert! f.map_zsmul z x <;> ext <;> apply int_smul_eq_zsmul

/-- The balanced tensor product `N ⊗_Λ M` of a right and a left `Λ`-module, as an object of
`ModuleCat ℤ`. -/
def balancedTensorObject
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ) : ModuleCat.{v} ℤ :=
  ModuleCat.of ℤ (StacksDraft.BalancedTensorProduct ℤ Λ N M)

/-- The pure tensor `n ⊗ m`. -/
def balancedTensorPure
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ) :
    N →ₗ[ℤ] M →ₗ[ℤ] balancedTensorObject Λ N M :=
  StacksDraft.BalancedTensorProduct.tmul ℤ Λ N M

/-- Pure tensors are balanced: `n a ⊗ m = n ⊗ a m`. -/
theorem balancedTensorPure_balanced
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ)
    (n : N) (a : Λ) (m : M) :
    balancedTensorPure Λ N M (MulOpposite.op a • n) m =
      balancedTensorPure Λ N M n (a • m) :=
  StacksDraft.BalancedTensorProduct.tmul_balanced ℤ Λ N M n a m

/-- An additive map between abelian groups is homogeneous for any `ℤ`-module structures on its
source and target, because the `ℤ`-action on an abelian group is unique. The target's structure
is an explicit argument: on an object of `ModuleCat ℤ` it is not the one instance search finds. -/
theorem addHom_map_int_smul {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module ℤ X] (iY : Module ℤ Y) (f : X →+ Y) (z : ℤ) (x : X) :
    f (z • x) = iY.smul z (f x) := by
  convert! f.map_zsmul z x
  ext
  apply int_smul_eq_zsmul

/-- A `ℤ`-bilinear map of objects of `ModuleCat` read as a biadditive map, which is the shape
the universal property of the balanced tensor product is applied in. -/
def balancedTensorBiadditive
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ)
    (Q : ModuleCat.{v} ℤ) (f : N →ₗ[ℤ] M →ₗ[ℤ] Q) : (N : Type v) →+ ((M : Type v) →+ (Q : Type v))
    where
  toFun n := (f n).toAddMonoidHom
  map_zero' := by ext m; exact DFunLike.congr_fun (map_zero f) m
  map_add' n n' := by ext m; exact DFunLike.congr_fun (map_add f n n') m

/-- Evaluation of a `ℤ`-bilinear map at a fixed second argument, as an additive map. -/
def balancedTensorEval
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ)
    (Q : ModuleCat.{v} ℤ) (f : N →ₗ[ℤ] M →ₗ[ℤ] Q) (m : M) :
    (N : Type v) →+ (Q : Type v) :=
  AddMonoidHom.mk' (fun n => f n m) fun n n' => DFunLike.congr_fun (map_add f n n') m

/-- The morphism out of `N ⊗_Λ M` determined by a balanced biadditive map. -/
def balancedTensorLift
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ)
    (Q : ModuleCat.{v} ℤ) (f : N →ₗ[ℤ] M →ₗ[ℤ] Q)
    (hf : ∀ (n : N) (a : Λ) (m : M), f (MulOpposite.op a • n) m = f n (a • m)) :
    balancedTensorObject Λ N M ⟶ Q :=
  ModuleCat.ofHom (StacksDraft.BalancedTensorProduct.liftBiadditive
    (A := Λ) (balancedTensorBiadditive Λ N M Q f)
    (fun z n m => addHom_map_int_smul Q.isModule (balancedTensorEval Λ N M Q f m) z n)
    (fun z n m => addHom_map_int_smul Q.isModule
      (balancedTensorBiadditive Λ N M Q f n) z m) hf)

/-- The lifted morphism sends the pure tensor `n ⊗ m` to `f n m`. -/
theorem balancedTensorLift_pure
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ)
    (Q : ModuleCat.{v} ℤ) (f : N →ₗ[ℤ] M →ₗ[ℤ] Q)
    (hf : ∀ (n : N) (a : Λ) (m : M), f (MulOpposite.op a • n) m = f n (a • m))
    (n : N) (m : M) :
    balancedTensorLift Λ N M Q f hf (balancedTensorPure Λ N M n m) = f n m :=
  rfl

/-- Two morphisms out of `N ⊗_Λ M` agreeing on pure tensors are equal. -/
theorem balancedTensor_hom_ext
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ)
    (Q : ModuleCat.{v} ℤ) (f g : balancedTensorObject Λ N M ⟶ Q)
    (h : ∀ (n : N) (m : M), f (balancedTensorPure Λ N M n m) =
      g (balancedTensorPure Λ N M n m)) : f = g :=
  ModuleCat.hom_ext
    (StacksDraft.BalancedTensorProduct.hom_ext ℤ Λ N M f.hom g.hom h)

/-- The universal property of the balanced tensor product, in the form the parameter structure
`BalancedDerivedTensoring` asks for. -/
theorem balancedTensorUniversal
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ)
    (Q : ModuleCat.{v} ℤ) (f : N →ₗ[ℤ] M →ₗ[ℤ] Q)
    (hf : ∀ (n : N) (a : Λ) (m : M), f (MulOpposite.op a • n) m = f n (a • m)) :
    ∃! g : balancedTensorObject Λ N M ⟶ Q,
      ∀ (n : N) (m : M), g (balancedTensorPure Λ N M n m) = f n m :=
  ⟨balancedTensorLift Λ N M Q f hf, fun _ _ => rfl, fun g hg =>
    balancedTensor_hom_ext Λ N M Q g _ fun n m =>
      (hg n m).trans (balancedTensorLift_pure Λ N M Q f hf n m).symm⟩

/-- The balanced biadditive map `(n, m) ↦ f n ⊗ g m` attached to a pair of module maps. -/
def balancedTensorMapPure
    {N N' : ModuleCat.{v} (MulOpposite Λ)} (f : N ⟶ N')
    {M M' : ModuleCat.{v} Λ} (g : M ⟶ M') :
    N →ₗ[ℤ] M →ₗ[ℤ] balancedTensorObject Λ N' M' := by
  apply intLinearMapOfAddHom
  refine
    { toFun := fun n => @intLinearMapOfAddHom _ _ _ _ _ _
        ((balancedTensorPure Λ N' M' (f n)).toAddMonoidHom.comp g.hom.toAddMonoidHom)
      map_zero' := ?_
      map_add' := ?_ }
  · ext m
    change balancedTensorPure Λ N' M' (f 0) (g m) = 0
    simp only [map_zero, LinearMap.zero_apply]
  · intro n n'; ext m
    change balancedTensorPure Λ N' M' (f (n + n')) (g m) =
      balancedTensorPure Λ N' M' (f n) (g m) + balancedTensorPure Λ N' M' (f n') (g m)
    simp only [map_add, LinearMap.add_apply]

/-- The map `(n, m) ↦ f n ⊗ g m` is balanced, because `f` and `g` are
module maps. -/
theorem balancedTensorMapPure_balanced
    {N N' : ModuleCat.{v} (MulOpposite Λ)} (f : N ⟶ N')
    {M M' : ModuleCat.{v} Λ} (g : M ⟶ M')
    (n : N) (a : Λ) (m : M) :
    balancedTensorMapPure Λ f g (MulOpposite.op a • n) m =
      balancedTensorMapPure Λ f g n (a • m) := by
  change balancedTensorPure Λ N' M' (f (MulOpposite.op a • n)) (g m) =
    balancedTensorPure Λ N' M' (f n) (g (a • m))
  rw [f.hom.map_smul, g.hom.map_smul]
  exact balancedTensorPure_balanced Λ N' M' (f n) a (g m)

/-- Functoriality of the balanced tensor product in both variables. -/
def balancedTensorMap
    {N N' : ModuleCat.{v} (MulOpposite Λ)} (f : N ⟶ N')
    {M M' : ModuleCat.{v} Λ} (g : M ⟶ M') :
    balancedTensorObject Λ N M ⟶ balancedTensorObject Λ N' M' :=
  balancedTensorLift Λ N M _ (balancedTensorMapPure Λ f g)
    (balancedTensorMapPure_balanced Λ f g)

/-- Functoriality on pure tensors: `n ⊗ m` is sent to `f n ⊗ g m`. -/
theorem balancedTensorMap_pure
    {N N' : ModuleCat.{v} (MulOpposite Λ)} (f : N ⟶ N')
    {M M' : ModuleCat.{v} Λ} (g : M ⟶ M') (n : N) (m : M) :
    balancedTensorMap Λ f g (balancedTensorPure Λ N M n m) =
      balancedTensorPure Λ N' M' (f n) (g m) :=
  balancedTensorLift_pure Λ N M _ (balancedTensorMapPure Λ f g)
    (balancedTensorMapPure_balanced Λ f g) n m

/-- The pair of identity maps induces the identity of `N ⊗_Λ M`. -/
theorem balancedTensorMap_id
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ) :
    balancedTensorMap Λ (𝟙 N) (𝟙 M) = 𝟙 (balancedTensorObject Λ N M) :=
  balancedTensor_hom_ext Λ N M _ _ _
    (fun n m => balancedTensorMap_pure Λ (𝟙 N) (𝟙 M) n m)

/-- Functoriality is compatible with composition in both variables. -/
theorem balancedTensorMap_comp
    {N N' N'' : ModuleCat.{v} (MulOpposite Λ)} (f : N ⟶ N') (f' : N' ⟶ N'')
    {M M' M'' : ModuleCat.{v} Λ} (g : M ⟶ M') (g' : M' ⟶ M'') :
    balancedTensorMap Λ (f ≫ f') (g ≫ g') =
      balancedTensorMap Λ f g ≫ balancedTensorMap Λ f' g' :=
  balancedTensor_hom_ext Λ N M _ _ _
    (fun n m => by simp only [ModuleCat.comp_apply, balancedTensorMap_pure])

/-- Balanced tensoring of a right `Λ`-module with a left `Λ`-module, as a bifunctor into the
category of abelian groups. -/
def balancedTensorFunctor :
    ModuleCat.{v} (MulOpposite Λ) ⥤ ModuleCat.{v} Λ ⥤ ModuleCat.{v} ℤ where
  obj N :=
    { obj := fun M => balancedTensorObject Λ N M
      map := fun f => balancedTensorMap Λ (𝟙 N) f
      map_id := balancedTensorMap_id Λ N
      map_comp := fun f g => by
        simpa only [Category.id_comp] using balancedTensorMap_comp Λ (𝟙 N) (𝟙 N) f g }
  map f :=
    { app := fun M => balancedTensorMap Λ f (𝟙 M)
      naturality := fun M M' g => by
        change balancedTensorMap Λ (𝟙 _) g ≫ balancedTensorMap Λ f (𝟙 _) =
          balancedTensorMap Λ f (𝟙 _) ≫ balancedTensorMap Λ (𝟙 _) g
        simp only [← balancedTensorMap_comp, Category.id_comp, Category.comp_id] }
  map_id N := NatTrans.ext (funext (balancedTensorMap_id Λ N))
  map_comp f g := NatTrans.ext <| funext fun M => by
    change balancedTensorMap Λ (f ≫ g) (𝟙 M) =
      balancedTensorMap Λ f (𝟙 M) ≫ balancedTensorMap Λ g (𝟙 M)
    simpa only [Category.id_comp] using balancedTensorMap_comp Λ f g (𝟙 M) (𝟙 M)

/-- Balanced tensoring with a fixed right `Λ`-module is additive. -/
theorem balancedTensorFunctor_additive (N : ModuleCat.{v} (MulOpposite Λ)) :
    ((balancedTensorFunctor Λ).obj N).Additive where
  map_add {M M'} {f g} := balancedTensor_hom_ext Λ N M _ _ _ fun n m => by
    change balancedTensorMap Λ (𝟙 N) (f + g) (balancedTensorPure Λ N M n m) =
      balancedTensorMap Λ (𝟙 N) f (balancedTensorPure Λ N M n m) +
        balancedTensorMap Λ (𝟙 N) g (balancedTensorPure Λ N M n m)
    simp only [balancedTensorMap_pure]
    exact (balancedTensorPure Λ N M' n).map_add (f m) (g m)

attribute [local instance] balancedTensorFunctor_additive

/-! ### The tensor–hom adjunction -/

/-- The left `Λ`-module structure on the additive maps `N → Q` out of a right `Λ`-module,
given by `(a · f)(n) = f(n a)`. -/
@[ega "III 7.2.2" "more general"]
abbrev balancedTensorHomModule (N : ModuleCat.{v} (MulOpposite Λ)) (Q : ModuleCat.{v} ℤ) :
    Module Λ (N →+ Q) where
  smul a f :=
    { toFun := fun n => f (MulOpposite.op a • n)
      map_zero' := by simp
      map_add' := by intros; simp }
  one_smul f := by ext n; change f (MulOpposite.op (1 : Λ) • n) = f n; simp
  mul_smul a b f := by
    ext n
    change f (MulOpposite.op (a * b) • n) =
      f (MulOpposite.op b • (MulOpposite.op a • n))
    simp [MulOpposite.op_mul, mul_smul]
  smul_zero a := by ext n; rfl
  smul_add a f g := by ext n; rfl
  add_smul a b f := by
    ext n
    change f (MulOpposite.op (a + b) • n) =
      f (MulOpposite.op a • n) + f (MulOpposite.op b • n)
    simp [add_smul]
  zero_smul f := by ext n; change f (MulOpposite.op (0 : Λ) • n) = 0; simp

/-- The left `Λ`-module `Hom_ℤ(N, Q)`, the value of the right adjoint of balanced tensoring
with `N`. -/
abbrev balancedTensorHomObject (N : ModuleCat.{v} (MulOpposite Λ)) (Q : ModuleCat.{v} ℤ) :
    ModuleCat.{v} Λ :=
  letI := balancedTensorHomModule Λ N Q
  ModuleCat.of Λ (N →+ Q)

/-- Currying a morphism out of `N ⊗_Λ M`. -/
def balancedTensorHomCurry
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ) (Q : ModuleCat.{v} ℤ)
    (g : balancedTensorObject Λ N M ⟶ Q) : M ⟶ balancedTensorHomObject Λ N Q := by
  letI := balancedTensorHomModule Λ N Q
  apply ModuleCat.ofHom
  refine
    { toFun := fun m =>
        { toFun := fun n => g (balancedTensorPure Λ N M n m)
          map_zero' := by simp
          map_add' := by intros; simp }
      map_add' := ?_
      map_smul' := ?_ }
  · intro m m'
    ext n
    change g (balancedTensorPure Λ N M n (m + m')) = _
    simp only [map_add]
    rfl
  · intro a m
    ext n
    change g (balancedTensorPure Λ N M n (a • m)) =
      g (balancedTensorPure Λ N M (MulOpposite.op a • n) m)
    rw [balancedTensorPure_balanced]

/-- The balanced biadditive map underlying an uncurried morphism into `Hom_ℤ(N, Q)`. -/
def balancedTensorHomUncurryPure
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ) (Q : ModuleCat.{v} ℤ)
    (g : M ⟶ balancedTensorHomObject Λ N Q) : N →ₗ[ℤ] M →ₗ[ℤ] Q := by
  apply intLinearMapOfAddHom
  refine
    { toFun := fun n => @intLinearMapOfAddHom _ _ _ _ _ _
        { toFun := fun m => g m n
          map_zero' := by simp
          map_add' := by intros; simp }
      map_zero' := ?_
      map_add' := ?_ }
  · ext m; exact map_zero (g m)
  · intro n n'; ext m; exact map_add (g m) n n'

/-- The uncurried map is balanced, which is the `Λ`-linearity of the
curried one. -/
@[ega "III 7.2.1" "partial"]
theorem balancedTensorHomUncurryPure_balanced
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ) (Q : ModuleCat.{v} ℤ)
    (g : M ⟶ balancedTensorHomObject Λ N Q) (n : N) (a : Λ) (m : M) :
    balancedTensorHomUncurryPure Λ N M Q g (MulOpposite.op a • n) m =
      balancedTensorHomUncurryPure Λ N M Q g n (a • m) := by
  let := balancedTensorHomModule Λ N Q
  exact (DFunLike.congr_fun (g.hom.map_smul a m) n).symm

/-- Uncurrying a morphism into `Hom_ℤ(N, Q)`. -/
def balancedTensorHomUncurry
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ) (Q : ModuleCat.{v} ℤ)
    (g : M ⟶ balancedTensorHomObject Λ N Q) : balancedTensorObject Λ N M ⟶ Q :=
  balancedTensorLift Λ N M Q (balancedTensorHomUncurryPure Λ N M Q g)
    (balancedTensorHomUncurryPure_balanced Λ N M Q g)

/-- Uncurrying is computed on pure tensors by `n ⊗ m ↦ g m n`. -/
theorem balancedTensorHomUncurry_pure
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ) (Q : ModuleCat.{v} ℤ)
    (g : M ⟶ balancedTensorHomObject Λ N Q) (n : N) (m : M) :
    balancedTensorHomUncurry Λ N M Q g (balancedTensorPure Λ N M n m) = g m n :=
  balancedTensorLift_pure Λ N M Q (balancedTensorHomUncurryPure Λ N M Q g)
    (balancedTensorHomUncurryPure_balanced Λ N M Q g) n m

/-- The currying bijection of the tensor–hom adjunction. -/
def balancedTensorHomEquiv
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ) (Q : ModuleCat.{v} ℤ) :
    (balancedTensorObject Λ N M ⟶ Q) ≃ (M ⟶ balancedTensorHomObject Λ N Q) where
  toFun := balancedTensorHomCurry Λ N M Q
  invFun := balancedTensorHomUncurry Λ N M Q
  left_inv g := balancedTensor_hom_ext Λ N M Q _ _ fun n m =>
    balancedTensorHomUncurry_pure Λ N M Q (balancedTensorHomCurry Λ N M Q g) n m
  right_inv g := by
    let := balancedTensorHomModule Λ N Q
    ext m n
    exact balancedTensorHomUncurry_pure Λ N M Q g n m

/-- Balanced tensoring with a fixed right `Λ`-module is a left adjoint, its
right adjoint being `Q ↦ Hom_ℤ(N, Q)`. -/
theorem balancedTensorFunctor_isLeftAdjoint (N : ModuleCat.{v} (MulOpposite Λ)) :
    ((balancedTensorFunctor Λ).obj N).IsLeftAdjoint := by
  let e : ∀ (M : ModuleCat.{v} Λ) (Q : ModuleCat.{v} ℤ),
      (((balancedTensorFunctor Λ).obj N).obj M ⟶ Q) ≃ (M ⟶ balancedTensorHomObject Λ N Q) :=
    balancedTensorHomEquiv Λ N
  have he : ∀ M' M Q f g, e M' Q (((balancedTensorFunctor Λ).obj N).map f ≫ g) =
      f ≫ e M Q g := by
    intro M' M Q f g
    let := balancedTensorHomModule Λ N Q
    ext m n
    change g (balancedTensorMap Λ (𝟙 N) f (balancedTensorPure Λ N M' n m)) =
      g (balancedTensorPure Λ N M n (f m))
    rw [balancedTensorMap_pure]
    rfl
  exact ⟨Adjunction.rightAdjointOfEquiv e he, ⟨Adjunction.adjunctionOfEquivRight e he⟩⟩

attribute [local instance] balancedTensorFunctor_isLeftAdjoint

/-- Balanced tensoring with a fixed right `Λ`-module commutes with arbitrary colimits; in
particular it is right exact. This is because it is a left adjoint, its right adjoint being
`Q ↦ Hom_ℤ(N, Q)`. Colimits of `R`-modules are computed on the underlying abelian groups, so
this is also the statement for the `R`-module `N ⊗_Λ M` when `Λ` is an `R`-algebra. -/
@[stacks 09LL "right exactness and commutation with colimits in the left-module variable"]
theorem preservesColimits_balancedTensorFunctor_obj (N : ModuleCat.{v} (MulOpposite Λ)) :
    PreservesColimits ((balancedTensorFunctor Λ).obj N) :=
  inferInstance

/-! ### The tensor–hom adjunction in the right-module variable -/

/-- The right `Λ`-module structure on the additive maps `M → Q` out of a left `Λ`-module,
given by `(f · a)(m) = f(a m)`. -/
abbrev balancedTensorFlipHomModule (M : ModuleCat.{v} Λ) (Q : ModuleCat.{v} ℤ) :
    Module (MulOpposite Λ) (M →+ Q) where
  smul a f :=
    { toFun := fun m => f (a.unop • m)
      map_zero' := by simp
      map_add' := by intros; simp }
  one_smul f := by ext m; change f ((1 : Λᵐᵒᵖ).unop • m) = f m; simp
  mul_smul a b f := by
    ext m
    change f ((a * b).unop • m) = f (b.unop • (a.unop • m))
    simp [MulOpposite.unop_mul, mul_smul]
  smul_zero a := by ext m; rfl
  smul_add a f g := by ext m; rfl
  add_smul a b f := by
    ext m
    change f ((a + b).unop • m) = f (a.unop • m) + f (b.unop • m)
    simp [add_smul]
  zero_smul f := by ext m; change f ((0 : Λᵐᵒᵖ).unop • m) = 0; simp

/-- The right `Λ`-module `Hom_ℤ(M, Q)`, the value of the right adjoint of balanced tensoring
with a fixed left module `M`. -/
abbrev balancedTensorFlipHomObject (M : ModuleCat.{v} Λ) (Q : ModuleCat.{v} ℤ) :
    ModuleCat.{v} (MulOpposite Λ) :=
  letI := balancedTensorFlipHomModule Λ M Q
  ModuleCat.of (MulOpposite Λ) (M →+ Q)

/-- Currying a morphism out of `N ⊗_Λ M` in the right-module variable. -/
def balancedTensorFlipHomCurry
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ) (Q : ModuleCat.{v} ℤ)
    (g : balancedTensorObject Λ N M ⟶ Q) : N ⟶ balancedTensorFlipHomObject Λ M Q := by
  letI := balancedTensorFlipHomModule Λ M Q
  apply ModuleCat.ofHom
  refine
    { toFun := fun n =>
        { toFun := fun m => g (balancedTensorPure Λ N M n m)
          map_zero' := by simp
          map_add' := by intros; simp }
      map_add' := ?_
      map_smul' := ?_ }
  · intro n n'
    ext m
    change g (balancedTensorPure Λ N M (n + n') m) = _
    simp only [map_add, LinearMap.add_apply]
    rfl
  · intro a n
    ext m
    change g (balancedTensorPure Λ N M (a • n) m) =
      g (balancedTensorPure Λ N M n (a.unop • m))
    rw [← balancedTensorPure_balanced]
    rfl

/-- The balanced bilinear map underlying an uncurried morphism into `Hom_ℤ(M, Q)`. -/
def balancedTensorFlipHomUncurryPure
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ) (Q : ModuleCat.{v} ℤ)
    (g : N ⟶ balancedTensorFlipHomObject Λ M Q) : N →ₗ[ℤ] M →ₗ[ℤ] Q := by
  apply intLinearMapOfAddHom
  refine
    { toFun := fun n => @intLinearMapOfAddHom _ _ _ _ _ _ (g.hom n)
      map_zero' := ?_
      map_add' := ?_ }
  · ext m; exact DFunLike.congr_fun (map_zero g.hom) m
  · intro n n'; ext m; exact DFunLike.congr_fun (map_add g.hom n n') m

/-- The uncurried map is balanced, which is the `Λ`-linearity of the curried one. -/
theorem balancedTensorFlipHomUncurryPure_balanced
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ) (Q : ModuleCat.{v} ℤ)
    (g : N ⟶ balancedTensorFlipHomObject Λ M Q) (n : N) (a : Λ) (m : M) :
    balancedTensorFlipHomUncurryPure Λ N M Q g (MulOpposite.op a • n) m =
      balancedTensorFlipHomUncurryPure Λ N M Q g n (a • m) := by
  let := balancedTensorFlipHomModule Λ M Q
  exact DFunLike.congr_fun (g.hom.map_smul (MulOpposite.op a) n) m

/-- Uncurrying a morphism into `Hom_ℤ(M, Q)`. -/
def balancedTensorFlipHomUncurry
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ) (Q : ModuleCat.{v} ℤ)
    (g : N ⟶ balancedTensorFlipHomObject Λ M Q) : balancedTensorObject Λ N M ⟶ Q :=
  balancedTensorLift Λ N M Q (balancedTensorFlipHomUncurryPure Λ N M Q g)
    (balancedTensorFlipHomUncurryPure_balanced Λ N M Q g)

/-- Uncurrying is computed on pure tensors by `n ⊗ m ↦ g n m`. -/
theorem balancedTensorFlipHomUncurry_pure
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ) (Q : ModuleCat.{v} ℤ)
    (g : N ⟶ balancedTensorFlipHomObject Λ M Q) (n : N) (m : M) :
    balancedTensorFlipHomUncurry Λ N M Q g (balancedTensorPure Λ N M n m) = g n m :=
  balancedTensorLift_pure Λ N M Q (balancedTensorFlipHomUncurryPure Λ N M Q g)
    (balancedTensorFlipHomUncurryPure_balanced Λ N M Q g) n m

/-- The currying bijection of the tensor–hom adjunction in the right-module variable. -/
def balancedTensorFlipHomEquiv
    (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ) (Q : ModuleCat.{v} ℤ) :
    (balancedTensorObject Λ N M ⟶ Q) ≃ (N ⟶ balancedTensorFlipHomObject Λ M Q) where
  toFun := balancedTensorFlipHomCurry Λ N M Q
  invFun := balancedTensorFlipHomUncurry Λ N M Q
  left_inv g := balancedTensor_hom_ext Λ N M Q _ _ fun n m =>
    balancedTensorFlipHomUncurry_pure Λ N M Q (balancedTensorFlipHomCurry Λ N M Q g) n m
  right_inv g := by
    let := balancedTensorFlipHomModule Λ M Q
    ext n m
    exact balancedTensorFlipHomUncurry_pure Λ N M Q g n m

/-- Balanced tensoring with a fixed left `Λ`-module is a left adjoint, its right adjoint being
`Q ↦ Hom_ℤ(M, Q)`. -/
theorem balancedTensorFunctor_flip_isLeftAdjoint (M : ModuleCat.{v} Λ) :
    ((balancedTensorFunctor Λ).flip.obj M).IsLeftAdjoint := by
  let e : ∀ (N : ModuleCat.{v} (MulOpposite Λ)) (Q : ModuleCat.{v} ℤ),
      (((balancedTensorFunctor Λ).flip.obj M).obj N ⟶ Q) ≃
        (N ⟶ balancedTensorFlipHomObject Λ M Q) :=
    fun N Q => balancedTensorFlipHomEquiv Λ N M Q
  have he : ∀ N' N Q f g, e N' Q (((balancedTensorFunctor Λ).flip.obj M).map f ≫ g) =
      f ≫ e N Q g := by
    intro N' N Q f g
    let := balancedTensorFlipHomModule Λ M Q
    ext n m
    change g (balancedTensorMap Λ f (𝟙 M) (balancedTensorPure Λ N' M n m)) =
      g (balancedTensorPure Λ N M (f n) m)
    rw [balancedTensorMap_pure]
    rfl
  exact ⟨Adjunction.rightAdjointOfEquiv e he, ⟨Adjunction.adjunctionOfEquivRight e he⟩⟩

/-- Balanced tensoring with a fixed left `Λ`-module commutes with arbitrary colimits; in
particular it is right exact. This is because it is a left adjoint, its right adjoint being
`Q ↦ Hom_ℤ(M, Q)`. Together with `preservesColimits_balancedTensorFunctor_obj` this is the
statement in each variable. -/
@[stacks 09LL "right exactness and commutation with colimits in the right-module variable"]
theorem preservesColimits_balancedTensorFunctor_flip_obj (M : ModuleCat.{v} Λ) :
    PreservesColimits ((balancedTensorFunctor Λ).flip.obj M) :=
  have := balancedTensorFunctor_flip_isLeftAdjoint Λ M
  inferInstance

/-! ### The derived bifunctor -/

/-- Termwise balanced tensoring of complexes of left `Λ`-modules, viewed in `D(ℤ)`. -/
def balancedTensorComplexFunctor :
    ModuleCat.{v} (MulOpposite Λ) ⥤
      CochainComplex (ModuleCat.{v} Λ) ℤ ⥤ DerivedCategory (ModuleCat.{v} ℤ) := by
  letI (N : ModuleCat.{v} (MulOpposite Λ)) := balancedTensorFunctor_additive Λ N
  exact
    { obj := fun N => ((balancedTensorFunctor Λ).obj N).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q
      map := fun f => Functor.whiskerRight
        (((balancedTensorFunctor Λ).map f).mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      map_id := fun N => by simp
      map_comp := fun f g => by simp [NatTrans.mapHomologicalComplex_comp] }

open ZeroObject in
/-- Stacks 0794 applies to balanced tensoring at the class of projective modules: a bounded
above acyclic complex of projectives is K-projective, hence zero in the homotopy category, hence
annihilated by every additive functor. -/
theorem hasPointwiseLeftDerivedFunctor_tensor_of_small [Small.{v} Λ]
    (N : ModuleCat.{v} (MulOpposite Λ)) :
    ((((balancedTensorFunctor Λ).obj N).mapHomotopyCategory (.up ℤ)) ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
        (HomotopyCategory.quasiIso (ModuleCat.{v} Λ) (.up ℤ)) := by
  let F := (balancedTensorFunctor Λ).obj N
  let := balancedTensorFunctor_additive Λ N
  let := balancedTensorFunctor_isLeftAdjoint Λ N
  let : AB5OfSize.{0, 0} AddCommGrpCat.{v} := AB5OfSize_shrink AddCommGrpCat.{v}
  let : HasExactColimitsOfShape ℕ (ModuleCat.{v} Λ) :=
    HasExactColimitsOfShape.domain_of_functor ℕ (forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v})
  let : HasExactColimitsOfShape ℕ (ModuleCat.{v} ℤ) :=
    HasExactColimitsOfShape.domain_of_functor ℕ (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v})
  let P : ObjectProperty (ModuleCat.{v} Λ) := fun M => Projective M
  let : P.ContainsZero := ⟨⟨0, isZero_zero _, inferInstance⟩⟩
  apply Functor.hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex F P
  · intro M M' hM hM'
    let : Projective M := hM
    let : Projective M' := hM'
    exact inferInstanceAs (Projective (M ⊞ M'))
  · intro M
    exact ⟨Projective.over M, inferInstance, Projective.π M, inferInstance⟩
  · intro a K hK hproj hac
    let := hK
    let (i : ℤ) : Projective (K.X i) := hproj i
    let : K.IsKProjective := CochainComplex.isKProjective_of_projective K a
    have hz : IsZero ((HomotopyCategory.quotient (ModuleCat.{v} Λ) (.up ℤ)).obj K) := by
      rw [IsZero.iff_id_eq_zero]
      exact CochainComplex.IsKProjective.leftOrthogonal K (𝟙 _)
        ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic K).2 hac)
    have hz' := (F.mapHomotopyCategory (.up ℤ)).map_isZero hz
    rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
    exact (HomotopyCategory.subcategoryAcyclic (ModuleCat.{v} ℤ)).prop_of_isZero hz'

open Functor in
/-- A right Kan extension along a localization stays a right Kan extension after precomposing
with a functor whose whiskering is fully faithful. -/
theorem isRightKanExtension_precomp
    {C C' D H : Type*} [Category C] [Category C'] [Category D] [Category H]
    (E : C' ⥤ C) [((whiskeringLeft C' C H).obj E).Full]
    [((whiskeringLeft C' C H).obj E).Faithful]
    (L : C ⥤ D) (F : C ⥤ H) (G : D ⥤ H) (α : L ⋙ G ⟶ F)
    [G.IsRightKanExtension α] :
    G.IsRightKanExtension ((Functor.associator E L G).hom ≫ whiskerLeft E α) := by
  have : (RightExtension.precomp L F E).IsEquivalence := by
    dsimp only [RightExtension.precomp]
    infer_instance
  let h := (IsTerminal.isTerminalIffObj (RightExtension.precomp L F E)
    (RightExtension.mk G α)).1 (G.isUniversalOfIsRightKanExtension α)
  exact ⟨⟨IsTerminal.ofIso h (CostructuredArrow.isoMk (Iso.refl G))⟩⟩

open Functor in
/-- Transport of the existence of a total left derived functor from the homotopy category to
the category of complexes. -/
theorem hasLeftDerivedFunctor_of_homotopy
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
    [(F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (.up ℤ))] :
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
  let E := HomotopyCategory.quotient A (.up ℤ)
  let U := F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  let Uh := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  let G := Uh.totalLeftDerived DerivedCategory.Qh W
  let α := Uh.totalLeftDerivedCounit DerivedCategory.Qh W
  let e : E ⋙ Uh ≅ U :=
    Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).symm DerivedCategory.Qh ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ)) (DerivedCategory.quotientCompQhIso B)
  let β : DerivedCategory.Q ⋙ G ⟶ U :=
    whiskerRight (DerivedCategory.quotientCompQhIso A).inv G ≫ whiskerLeft E α ≫ e.hom
  have hβ : whiskerLeft E α =
      whiskerRight (DerivedCategory.quotientCompQhIso A).hom G ≫ β ≫ e.inv := by
    ext X
    dsimp only [β, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
    rw [Category.assoc, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    simp
  have : G.IsRightKanExtension α := IsLeftDerivedFunctor.isRightKanExtension G α W
  have hk := isRightKanExtension_precomp E DerivedCategory.Qh Uh G α
  have hke : G.IsRightKanExtension
      (whiskerRight (DerivedCategory.quotientCompQhIso A).hom G ≫ β) := by
    apply (Functor.isRightKanExtension_iff_of_iso₂
      ((Functor.associator E DerivedCategory.Qh G).hom ≫ whiskerLeft E α)
      (whiskerRight (DerivedCategory.quotientCompQhIso A).hom G ≫ β) e (Iso.refl G) ?_).mp hk
    rw [hβ]
    ext X
    simp
  have : G.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso A (.up ℤ)) := by
    rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension]
    apply (Functor.isRightKanExtension_iff_postcomp₁ (𝟭 _)
      ((E ⋙ DerivedCategory.Qh).rightUnitor ≪≫ DerivedCategory.quotientCompQhIso A) β).2
    have := hke
    apply Functor.isRightKanExtension_of_iso G.leftUnitor.symm
      (whiskerRight (DerivedCategory.quotientCompQhIso A).hom G ≫ β)
    ext X
    simp [E]
  exact Functor.HasLeftDerivedFunctor.mk' G β

/-- Termwise balanced tensoring of complexes of left `Λ`-modules has a total
left derived functor along the localization at the quasi-isomorphisms of complexes. -/
theorem hasLeftDerivedFunctor_tensor_of_small [Small.{v} Λ]
    (N : ModuleCat.{v} (MulOpposite Λ)) :
    ((balancedTensorComplexFunctor Λ).obj N).HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso (ModuleCat.{v} Λ) (.up ℤ)) := by
  let := balancedTensorFunctor_additive Λ N
  let := hasPointwiseLeftDerivedFunctor_tensor_of_small Λ N
  let := Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor
    (((balancedTensorFunctor Λ).obj N).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (HomotopyCategory.quasiIso (ModuleCat.{v} Λ) (.up ℤ))
  exact hasLeftDerivedFunctor_of_homotopy ((balancedTensorFunctor Λ).obj N)

/-- Deriving a bifunctor in its second variable, one object of the first variable at a time. -/
def leftDerivedBifunctor
    {S C D H : Type*} [Category S] [Category C] [Category D] [Category H]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (F : S ⥤ C ⥤ H) [∀ s, (F.obj s).HasLeftDerivedFunctor W] : S ⥤ D ⥤ H where
  obj s := (F.obj s).totalLeftDerived L W
  map {s t} f := Functor.leftDerivedNatTrans
    ((F.obj s).totalLeftDerived L W) ((F.obj t).totalLeftDerived L W)
    ((F.obj s).totalLeftDerivedCounit L W) ((F.obj t).totalLeftDerivedCounit L W) W
    (F.map f)
  map_id s := by rw [F.map_id, Functor.leftDerivedNatTrans_id]
  map_comp f g := by rw [F.map_comp, Functor.leftDerivedNatTrans_comp]

/-! ### The term -/

/-- The balanced tensor product of a right and a left `Λ`-module together with its total left
derived functor, for an arbitrary ring `Λ` with a copy of its underlying type in the module
universe. This inhabits the parameter structure of
`StacksDraft.Perfect.isPerfect_iff_hasFiniteTorDimension_and_finite_homology`. -/
def balancedDerivedTensoring [Small.{v} Λ] : BalancedDerivedTensoring.{u, v} Λ := by
  letI := hasLeftDerivedFunctor_tensor_of_small Λ
  exact
    { ordinary := balancedTensorFunctor Λ
      pure := balancedTensorPure Λ
      balanced := balancedTensorPure_balanced Λ
      universal := balancedTensorUniversal Λ
      natural_left := fun {N N'} f M n m => balancedTensorMap_pure Λ f (𝟙 M) n m
      natural_right := fun N {M M'} f n m => balancedTensorMap_pure Λ (𝟙 N) f n m
      additive := balancedTensorFunctor_additive Λ
      derived := leftDerivedBifunctor DerivedCategory.Q
        (HomologicalComplex.quasiIso (ModuleCat.{v} Λ) (.up ℤ)) (balancedTensorComplexFunctor Λ)
      comparison := fun N => ((balancedTensorComplexFunctor Λ).obj N).totalLeftDerivedCounit
        DerivedCategory.Q (HomologicalComplex.quasiIso (ModuleCat.{v} Λ) (.up ℤ))
      isLeftDerived := fun N => by
        let : ((balancedTensorComplexFunctor Λ).obj N).HasLeftDerivedFunctor
            (HomologicalComplex.quasiIso (ModuleCat.{v} Λ) (.up ℤ)) :=
          hasLeftDerivedFunctor_tensor_of_small Λ N
        let := Functor.HasLeftDerivedFunctor.hasRightKanExtension
          ((balancedTensorComplexFunctor Λ).obj N) DerivedCategory.Q
          (HomologicalComplex.quasiIso (ModuleCat.{v} Λ) (.up ℤ))
        have hterm : IsTerminal (⊤_ (Functor.RightExtension DerivedCategory.Q
            ((balancedTensorComplexFunctor Λ).obj N))) := terminalIsTerminal
        dsimp only [leftDerivedBifunctor]
        refine ⟨?_⟩
        dsimp [Functor.totalLeftDerived, Functor.totalLeftDerivedCounit]
        exact ⟨⟨hterm⟩⟩ }

/-- The parameter structure of
`StacksDraft.Perfect.isPerfect_iff_hasFiniteTorDimension_and_finite_homology` is inhabited, so
that theorem is not vacuous. -/
theorem nonempty_balancedDerivedTensoring [Small.{v} Λ] :
    Nonempty (BalancedDerivedTensoring.{u, v} Λ) :=
  ⟨balancedDerivedTensoring Λ⟩

/-- An object `K` of `D(Λ)` has *finite Tor dimension* if there are integers `a, b` such that
`Hⁱ(N ⊗ᴸ[Λ] K) = 0` for every right `Λ`-module `N` and every `i ∉ [a, b]`. This is the definition
at the balanced derived tensor product constructed here, so it takes no parameter; by
`hasFiniteTorDimensionCanonical_iff` it is the same condition as
`StacksDraft.Perfect.HasFiniteTorDimension` at any term of `BalancedDerivedTensoring Λ`. -/
@[stacks 03TN, sga "4½ Rapport 4.5" "finite tor dimension"]
def HasFiniteTorDimensionCanonical [Small.{v} Λ] (K : DerivedCategory (ModuleCat.{v} Λ)) : Prop :=
  HasFiniteTorDimension (balancedDerivedTensoring Λ) K

/-- The parameter-free form of finite Tor dimension is the parameterized form read off any
term of `BalancedDerivedTensoring Λ`. -/
theorem hasFiniteTorDimensionCanonical_iff [Small.{v} Λ]
    (D : BalancedDerivedTensoring.{u, v} Λ) (K : DerivedCategory (ModuleCat.{v} Λ)) :
    HasFiniteTorDimensionCanonical Λ K ↔ HasFiniteTorDimension D K :=
  hasFiniteTorDimension_iff_of_balancedDerivedTensoring (balancedDerivedTensoring Λ) D K

/-- Let `Λ` be a left Noetherian ring and let `K` be an object of `D(Λ)`. Then `K` is perfect if
and only if `K` has finite Tor dimension and `Hⁱ(K)` is a finite `Λ`-module for every `i`. This is
`StacksDraft.Perfect.isPerfect_iff_hasFiniteTorDimension_and_finite_homology` with its parameter
supplied by `balancedDerivedTensoring`, so no datum is assumed. -/
@[stacks 03TO, sga "5 VIII 8.1" "Noetherian case", sga "4½ Rapport 4.5.1"]
theorem isPerfect_iff_hasFiniteTorDimension_balancedDerivedTensoring
    [IsNoetherianRing Λ] [Small.{v} Λ] (K : DerivedCategory (ModuleCat.{v} Λ)) :
    IsPerfect K ↔
      (HasFiniteTorDimensionCanonical Λ K ∧
        ∀ i : ℤ,
          Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{v} Λ) i).obj K)) :=
  isPerfect_iff_hasFiniteTorDimension_and_finite_homology (balancedDerivedTensoring Λ) K

end StacksDraft.Perfect

end
