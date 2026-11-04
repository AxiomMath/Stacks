module

public import StacksFrontier.AlgebraicGeometry.GradedAlgebraTwist.Basic
public import StacksFrontier.AlgebraicGeometry.TensorPowerTrivialize.GeneralModule
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TrivializingAffineCover

/-!
# The multiplicative generator family of the tensor powers over a trivializing open

Let `S` be a scheme and `ℒ` an invertible `𝒪_S`-module. Over an open `W` on which `ℒ` is
trivial — the data of such a trivialization being an isomorphism
`e : ℒ|_W ≅ 𝒪_W` of sheaves of modules on the localized site over `W` — each integer tensor
power `ℒ^{⊗ d}` of Tag 01CU is trivial over `W` too, and a choice of `e` pins down a *single*
section `gen d` of `ℒ^{⊗ d}` over `W` in every nonnegative degree at once.

The point of making the whole family at once, rather than one trivialization per degree, is that
it is **multiplicative**: the Laurent multiplication of the tensor powers carries `gen i` and
`gen j` to `gen (i + j)`, with `gen 0 = 1`. That is exactly what is needed to turn a
trivialization of `ℒ` over `W` into an isomorphism of *graded* rings of sections, and thence into
the chart-local comparison `relativeProj (𝒜 ⊗ ℒ^{⊗ •}) ≅ relativeProj 𝒜` of Tag 02NC over a
base scheme. Nothing about a graded algebra `𝒜` or about `Proj` appears here: this file is purely
about `ℒ`, its tensor powers, and their sections over `W`.

The second half of the file records that `gen d` really is a generator: tensoring with it is a
bijection on sections over `W`, both after tensoring with an arbitrary module `F`
(`bijective_tensorSectionsAt_gen`) and in the scalar form `r ↦ r • gen d`
(`bijective_toSpanSingleton_gen`). Finally `res_gen` says the family is compatible with
restriction: restricting `gen d` along `W' ≤ W` gives the family of the restricted
trivialization, which is what lets the chart-local comparisons be glued.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistGenerator.pow`: `ℒ^{⊗ d}` for `d : ℤ`, the tensor power of
  Tag 01CU on a scheme.
* `Stacks.AlgebraicGeometry.TwistGenerator.powOneTriv`: a trivialization of `ℒ` over `W`
  transported to one of `ℒ^{⊗ 1}`.
* `Stacks.AlgebraicGeometry.TwistGenerator.genOne`: the section of `ℒ^{⊗ 1}` over `W` that the
  transported trivialization sends to `1`.
* `Stacks.AlgebraicGeometry.TwistGenerator.gen`: **the generator family**, defined by recursion
  through the Laurent multiplication: `gen 0 = 1` and `gen (d + 1) = gen d * genOne`.

## Main results

* `Stacks.AlgebraicGeometry.TwistGenerator.mulBilinear_gen`: **the family is multiplicative**,
  `gen i * gen j = gen (i + j)`.
* `Stacks.AlgebraicGeometry.TwistGenerator.bijective_tensorSectionsAt_gen`: **tensoring with
  `gen d` is bijective on sections**, `Γ(F, W) ≃ Γ(F ⊗ ℒ^{⊗ d}, W)`, for an arbitrary
  `𝒪_S`-module `F`.
* `Stacks.AlgebraicGeometry.TwistGenerator.bijective_toSpanSingleton_gen` and
  `Stacks.AlgebraicGeometry.TwistGenerator.bijective_toSpanSingleton_res_gen`: `gen d` generates
  `ℒ^{⊗ d}` over `W`, and its restriction generates over a smaller open.
* `Stacks.AlgebraicGeometry.TwistGenerator.res_gen`: **the family is compatible with
  restriction**; restricting along `W' ≤ W` gives the family of the restricted trivialization
  `Stacks.SheafOfModules.isoUnitOverOfHom`.

## Implementation notes

Degree casts are discharged by definitional equality and never rewritten. The successor clause of
`gen` produces a section of `ℒ^{⊗ ((d : ℤ) + 1)}` where the declared type asks for
`ℒ^{⊗ ((d + 1 : ℕ) : ℤ)}`; `Nat.cast` into `ℤ` is `Int.ofNat` and `Int.add` reduces on
constructors, so the two are the same term up to `whnf` and a `show` suffices. For the same
reason the associativity and unit laws of the Laurent multiplication, which are heterogeneous
equalities between degrees `(i + j) + 1` and `i + (j + 1)`, are consumed by `eq_of_heq` with no
reindexing isomorphism in sight.

`rw` is avoided in the two places where the goal mentions a module of sections both as
`S.Modules` and as `SheafOfModules (structureSheaf 𝒪 h𝒪)`: the rewrite motive is not
type-correct at `implicit` transparency even though the two spellings are definitionally equal,
so the rewrites are performed by `congrArg` and `Eq.trans` instead.

The scalar in `bijective_toSpanSingleton_gen` is spelled
`(structureRingPresheaf S.sheaf.obj).obj (op W)` rather than `Γ(S, W)`. The module of sections of
a sheaf of modules on `S` is a module over the former, and with the latter — a `CommRingCat`
rather than a `RingCat` — the scalar action is not found by instance search.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf structureSheaf)
open Stacks.AlgebraicGeometry.GradedAlgebraTwist (tensorMap_app
  tensorSections_rightUnitorInvAt)

universe u

namespace Stacks.AlgebraicGeometry.TwistGenerator

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]

/-- The `d`-th integer tensor power `ℒ^{⊗ d}` of Tag 01CU, on a scheme. -/
abbrev pow (d : ℤ) : S.Modules :=
  TensorPower.tensorPower S.sheaf.obj S.ringCatSheaf.property L d

/-- Bijectivity transfers along a pointwise equality of functions. -/
private theorem bijective_of_forall_eq {α β : Type*} {f g : α → β} (h : ∀ x, f x = g x)
    (hg : Function.Bijective g) : Function.Bijective f :=
  funext h ▸ hg

/-- **An isomorphism of sheaves of modules acts bijectively on sections** over any open: the
component of the isomorphism is an isomorphism of modules, hence a linear equivalence. -/
theorem bijective_app_of_iso {M N : S.Modules} (φ : M ≅ N) (U : S.Opensᵒᵖ) :
    Function.Bijective (fun x : M.val.obj U => φ.hom.val.app U x) :=
  ((SheafOfModules.forget S.ringCatSheaf ⋙
    PresheafOfModules.evaluation _ U).mapIso φ).toLinearEquiv.bijective

/-- **The section of a trivialized module corresponding to `1` restricts to the one of the
restricted trivialization.** Both sides are the image of `1` under the inverse of a
trivialization, and the restricted trivialization `Stacks.SheafOfModules.isoUnitOverOfHom` is
built from identity comparisons, so this is one application of the naturality of `ε.hom`
followed by `map_one`. -/
theorem res_generator {M : S.Modules} {W W' : S.Opens} (h : W' ≤ W)
    (ε : M.over W ≅ SheafOfModules.unit (S.ringCatSheaf.over W)) :
    M.val.map (homOfLE h).op
        (TensorGenerator.generator S.sheaf.obj S.ringCatSheaf.property W M ε) =
      TensorGenerator.generator S.sheaf.obj S.ringCatSheaf.property W' M
        (isoUnitOverOfHom M (homOfLE h) ε) := by
  have h1 : ε.hom.val.app (op (Over.mk (𝟙 W)))
        (TensorGenerator.generator S.sheaf.obj S.ringCatSheaf.property W M ε) =
      (1 : (S.ringCatSheaf.over W).obj.obj (op (Over.mk (𝟙 W)))) :=
    congrArg (fun φ : SheafOfModules.unit (S.ringCatSheaf.over W) ⟶
      SheafOfModules.unit (S.ringCatSheaf.over W) =>
      φ.val.app (op (Over.mk (𝟙 W)))
        (1 : (S.ringCatSheaf.over W).obj.obj (op (Over.mk (𝟙 W))))) ε.inv_hom_id
  have h2 : (isoUnitOverOfHom M (homOfLE h) ε).hom.val.app (op (Over.mk (𝟙 W')))
        (M.val.map (homOfLE h).op
          (TensorGenerator.generator S.sheaf.obj S.ringCatSheaf.property W M ε)) =
      (1 : (S.ringCatSheaf.over W').obj.obj (op (Over.mk (𝟙 W')))) :=
    (congrArg (fun k => k (TensorGenerator.generator S.sheaf.obj S.ringCatSheaf.property W M ε))
      (ε.hom.val.naturality (Over.homMk (homOfLE h) :
        Over.mk (homOfLE h) ⟶ Over.mk (𝟙 W)).op)).trans
      ((congrArg (fun y => S.presheaf.map (homOfLE h).op y) h1).trans (map_one _))
  refine Eq.trans ?_ (congrArg (fun y => (isoUnitOverOfHom M (homOfLE h) ε).inv.val.app
    (op (Over.mk (𝟙 W'))) y) h2)
  exact (congrArg (fun φ : M.over W' ⟶ M.over W' => φ.val.app (op (Over.mk (𝟙 W')))
    (M.val.map (homOfLE h).op
      (TensorGenerator.generator S.sheaf.obj S.ringCatSheaf.property W M ε)))
    (isoUnitOverOfHom M (homOfLE h) ε).hom_inv_id).symm

variable {W : S.Opens} (e : L.over W ≅ SheafOfModules.unit (S.ringCatSheaf.over W))

/-- A trivialization of `ℒ` over `W` read as one of `ℒ^{⊗ 1}`, by transport along the
comparison `ℒ^{⊗ 1} ≅ ℒ`. -/
def powOneTriv : (pow L 1).over W ≅ SheafOfModules.unit (S.ringCatSheaf.over W) :=
  (SheafOfModules.overFunctor S.ringCatSheaf W).mapIso
    (TensorPower.tensorPowerOneIso S.sheaf.obj S.ringCatSheaf.property L) ≪≫ e

/-- **The degree-one generator**: the section of `ℒ^{⊗ 1}` over `W` that the transported
trivialization sends to `1`. -/
def genOne : (pow L 1).val.obj (op W) :=
  TensorGenerator.generator S.sheaf.obj S.ringCatSheaf.property W (pow L 1) (powOneTriv L e)

/-- **The generator family of the tensor powers of `ℒ` over a trivializing open `W`.** In
degree `0` it is the section `1` of the structure sheaf, and each successive degree is obtained
from the previous one by multiplying with the degree-one generator in the Laurent algebra of the
tensor powers. -/
def gen : (d : ℕ) → (pow L (d : ℤ)).val.obj (op W)
  | 0 => (1 : Γ(S, W))
  | d + 1 => show (pow L ((d : ℤ) + 1)).val.obj (op W) from
      (TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L (d : ℤ) 1).app (op W)
        (gen d) (genOne L e)

/-- The generator in degree `0` is the unit section of the structure sheaf. -/
theorem gen_zero : gen L e 0 = (1 : Γ(S, W)) := rfl

/-- The defining recursion: the generator in degree `d + 1` is the product of the generator in
degree `d` with the degree-one generator. -/
theorem gen_succ (d : ℕ) :
    gen L e (d + 1) =
      (TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L (d : ℤ) 1).app (op W)
        (gen L e d) (genOne L e) := rfl

/-- **The generator family is multiplicative.** The Laurent multiplication of the tensor powers
carries the generators of degrees `i` and `j` to the generator of degree `i + j`. Together with
`gen_zero` this says that `d ↦ gen d` is a monoid homomorphism from `ℕ` into the graded ring of
sections of the tensor powers over `W`. -/
theorem mulBilinear_gen (i j : ℕ) :
    (TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L (i : ℤ) (j : ℤ)).app (op W)
        (gen L e i) (gen L e j) =
      gen L e (i + j) := by
  induction j with
  | zero =>
      exact eq_of_heq (TensorPower.mulBilinear_mul_one S.sheaf.obj S.ringCatSheaf.property L
        (i : ℤ) (op W) (gen L e i))
  | succ j ih =>
      have hassoc := TensorPower.mulBilinear_assoc S.sheaf.obj S.ringCatSheaf.property L
        (i : ℤ) (j : ℤ) 1 (op W) (gen L e i) (gen L e j) (genOne L e)
      have h1 : (TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L
              (i : ℤ) ((j : ℤ) + 1)).app (op W) (gen L e i)
            ((TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L (j : ℤ) 1).app (op W)
              (gen L e j) (genOne L e)) =
          (TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L
              ((i : ℤ) + (j : ℤ)) 1).app (op W)
            ((TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L
              (i : ℤ) (j : ℤ)).app (op W) (gen L e i) (gen L e j)) (genOne L e) :=
        (eq_of_heq hassoc).symm
      refine Eq.trans h1 (Eq.trans (congrArg (fun y =>
        (TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L
          ((i : ℤ) + (j : ℤ)) 1).app (op W) y (genOne L e)) ih) ?_)
      exact (gen_succ L e (i + j)).symm

/-- **Tensoring a section of `F` with a product of two sections of tensor powers factors
through the associator.** The section `x ⊗ (a * b)` of `F ⊗ ℒ^{⊗ (n + m)}` is the image of
`(x ⊗ a) ⊗ b` under the associator followed by the coherent multiplication of the tensor powers.
This is what makes the bijectivity of tensoring with `gen (d + 1)` a composite of the bijection
for `gen d` and the bijection for `genOne`. -/
theorem tensorSectionsAt_mulBilinear (F : S.Modules) (n m : ℤ)
    (x : F.val.obj (op W)) (a : (pow L n).val.obj (op W)) (b : (pow L m).val.obj (op W)) :
    tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op W) F (pow L (n + m)) x
        ((TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L n m).app (op W) a b) =
      (GradedAlgebraTwist.tensorMap S.sheaf.obj S.ringCatSheaf.property (𝟙 F)
          (TensorPower.coherentMulIso S.sheaf.obj
            S.ringCatSheaf.property L n m).hom).val.app (op W)
        ((Invertible.tensorProductAssociator S.sheaf.obj S.ringCatSheaf.property F
            (pow L n) (pow L m)).hom.val.app (op W)
          (tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op W)
            ((((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨S.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (S.sheaf.obj)
                  (forget₂ CommRingCat RingCat) (S.ringCatSheaf.property)⟩).obj (F)).obj
                ((pow L n)))) (pow L m)
            (tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op W) F (pow L n) x a) b)) :=
  ((congrArg (fun y =>
      (GradedAlgebraTwist.tensorMap S.sheaf.obj S.ringCatSheaf.property (𝟙 F)
          (TensorPower.coherentMulIso S.sheaf.obj
            S.ringCatSheaf.property L n m).hom).val.app (op W) y)
      (tensorSections_associatorAt S.sheaf.obj S.ringCatSheaf.property (op W) F
        (pow L n) (pow L m) x a b)).trans
    (tensorMap_app S.sheaf.obj S.ringCatSheaf.property (𝟙 F)
      (TensorPower.coherentMulIso S.sheaf.obj S.ringCatSheaf.property L n m).hom (op W) x
      (tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op W)
        (pow L n) (pow L m) a b))).symm

/-- **Tensoring with the degree-one generator is bijective on sections over `W`** for an
arbitrary second module: this is the trivialization of `ℒ^{⊗ 1}` over `W`, tensored with `A`. -/
theorem bijective_tensorSectionsAt_genOne (A : S.Modules) :
    Function.Bijective (fun y : A.val.obj (op W) =>
      tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op W) A (pow L 1) y (genOne L e)) :=
  bijective_of_forall_eq (fun y =>
      (TensorGenerator.tensorSectionsEquiv_apply S.sheaf.obj S.ringCatSheaf.property W A
        (pow L 1) (powOneTriv L e) y).symm)
    (TensorGenerator.tensorSectionsEquiv S.sheaf.obj S.ringCatSheaf.property W A (pow L 1)
      (powOneTriv L e)).bijective

/-- **Tensoring with the generator of degree `d` is a bijection `Γ(F, W) → Γ(F ⊗ ℒ^{⊗ d}, W)`**
for every `𝒪_S`-module `F`. The induction runs with `F` universally quantified, because the
inductive step applies the hypothesis to `F ⊗ ℒ^{⊗ d}` rather than to `F`. -/
theorem bijective_tensorSectionsAt_gen (d : ℕ) (F : S.Modules) :
    Function.Bijective (fun x : F.val.obj (op W) =>
      tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op W) F (pow L (d : ℤ)) x
        (gen L e d)) := by
  induction d generalizing F with
  | zero =>
      refine bijective_of_forall_eq (fun x =>
        (tensorSections_rightUnitorInvAt S.sheaf.obj S.ringCatSheaf.property
          (op W) F x).symm) ?_
      exact bijective_app_of_iso
        (Invertible.tensorProductRightUnitor S.sheaf.obj S.ringCatSheaf.property F).symm (op W)
  | succ d ih =>
      refine bijective_of_forall_eq (fun x =>
        tensorSectionsAt_mulBilinear L F (d : ℤ) 1 x (gen L e d) (genOne L e)) ?_
      exact (bijective_app_of_iso
          (Invertible.tensorProductIso S.sheaf.obj S.ringCatSheaf.property (Iso.refl F)
            (TensorPower.coherentMulIso S.sheaf.obj S.ringCatSheaf.property L (d : ℤ) 1))
          (op W)).comp
        (((bijective_app_of_iso (Invertible.tensorProductAssociator S.sheaf.obj
              S.ringCatSheaf.property F (pow L (d : ℤ)) (pow L 1)) (op W)).comp
          (bijective_tensorSectionsAt_genOne L e
            ((((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨S.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (S.sheaf.obj)
                  (forget₂ CommRingCat RingCat) (S.ringCatSheaf.property)⟩).obj (F)).obj
                ((pow L (d : ℤ))))))).comp (ih F))

/-- The degree-one generator is the image of the generator of `ℒ` under the comparison
`ℒ ≅ ℒ^{⊗ 1}`. This holds on the nose, because restriction to the localized site over `W`
evaluated at the terminal object `𝟙 W` is evaluation at `W`. -/
theorem genOne_eq :
    genOne L e = (TensorPower.tensorPowerOneIso S.sheaf.obj
        S.ringCatSheaf.property L).inv.val.app (op W)
      (TensorGenerator.generator S.sheaf.obj S.ringCatSheaf.property W L e) := rfl

/-- The degree-one generator restricts to the degree-one generator of the restricted
trivialization. -/
theorem res_genOne {W' : S.Opens} (h : W' ≤ W) :
    (pow L 1).val.map (homOfLE h).op (genOne L e) =
      genOne L (isoUnitOverOfHom L (homOfLE h) e) :=
  (congrArg (fun k => k (TensorGenerator.generator S.sheaf.obj S.ringCatSheaf.property W L e))
      ((TensorPower.tensorPowerOneIso S.sheaf.obj
        S.ringCatSheaf.property L).inv.val.naturality (homOfLE h).op)).symm.trans
    (congrArg (fun y => (TensorPower.tensorPowerOneIso S.sheaf.obj
      S.ringCatSheaf.property L).inv.val.app (op W') y) (res_generator h e))

/-- **The generator family is compatible with restriction.** Restricting `gen d` along
`W' ≤ W` gives the degree-`d` generator of the trivialization restricted to `W'`. This is what
lets the chart-local comparisons built from these generators be glued over a trivializing
cover. -/
theorem res_gen {W' : S.Opens} (h : W' ≤ W) (d : ℕ) :
    (pow L (d : ℤ)).val.map (homOfLE h).op (gen L e d) =
      gen L (isoUnitOverOfHom L (homOfLE h) e) d := by
  induction d with
  | zero =>
      exact (TensorPower.oneSection S.sheaf.obj S.ringCatSheaf.property L).property
        (homOfLE h).op
  | succ d ih =>
      refine Eq.trans ((TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L
        (d : ℤ) 1).naturality (homOfLE h).op (gen L e d) (genOne L e)) ?_
      exact congrArg₂ (fun x y => (TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L
        (d : ℤ) 1).app (op W') x y) ih (res_genOne L e h)

/-- Multiplying a section of `ℒ^{⊗ d}` by the degree-one generator is a bijection onto the
sections of `ℒ^{⊗ (d + 1)}` over `W`. -/
theorem bijective_mulBilinear_genOne (d : ℤ) :
    Function.Bijective (fun a : (pow L d).val.obj (op W) =>
      (TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L d 1).app (op W) a
        (genOne L e)) :=
  bijective_of_forall_eq (fun a =>
      TensorPower.mulBilinear_app S.sheaf.obj S.ringCatSheaf.property L d 1 (op W) a
        (genOne L e))
    ((bijective_app_of_iso (TensorPower.coherentMulIso S.sheaf.obj S.ringCatSheaf.property L d 1)
      (op W)).comp (bijective_tensorSectionsAt_genOne L e (pow L d)))

/-- **`gen d` generates `ℒ^{⊗ d}` over `W`**: scalar multiplication by it is a bijection from
the ring of sections of the structure sheaf onto the sections of `ℒ^{⊗ d}`. -/
theorem bijective_toSpanSingleton_gen (d : ℕ) :
    Function.Bijective (fun r : (structureRingPresheaf S.sheaf.obj).obj (op W) =>
      r • gen L e d) := by
  induction d with
  | zero =>
      exact bijective_of_forall_eq (fun r => mul_one r) Function.bijective_id
  | succ d ih =>
      exact bijective_of_forall_eq (fun r =>
        ((TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L (d : ℤ) 1).map_smul_left
          (op W) r (gen L e d) (genOne L e)).symm)
        ((bijective_mulBilinear_genOne L e (d : ℤ)).comp ih)

/-- **The restriction of `gen d` generates `ℒ^{⊗ d}` over a smaller open**, by `res_gen` and
`bijective_toSpanSingleton_gen` for the restricted trivialization. -/
theorem bijective_toSpanSingleton_res_gen {W' : S.Opens} (h : W' ≤ W) (d : ℕ) :
    Function.Bijective (fun r : (structureRingPresheaf S.sheaf.obj).obj (op W') =>
      r • (pow L (d : ℤ)).val.map (homOfLE h).op (gen L e d)) :=
  bijective_of_forall_eq (fun r => congrArg (fun y => r • y) (res_gen L e h d))
    (bijective_toSpanSingleton_gen L (isoUnitOverOfHom L (homOfLE h) e) d)

end Stacks.AlgebraicGeometry.TwistGenerator

end
