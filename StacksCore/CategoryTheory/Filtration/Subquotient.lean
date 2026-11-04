module

public import StacksCore.CategoryTheory.Abelian.CommSq
public import StacksCore.CategoryTheory.Abelian.Subobject
public import StacksCore.CategoryTheory.Filtration.Limits
public import StacksCore.CategoryTheory.Filtration.Strict
import StacksCore.Tactic.StacksAttribute

/-! # Subquotients of filtered objects: Stacks 0129

Stacks 0129: let `𝒜` be an abelian category, `(A, F)` a filtered object of `𝒜` and `X ⊂ Y ⊂ A`
subobjects. On `Y/X = Ker(A/X → A/Y)` the quotient filtration coming from the induced filtration
on `Y` and the filtration induced from the quotient filtration on `A/X` agree, and each of the
morphisms `X → Y`, `X → A`, `Y → A`, `Y → A/X`, `Y → Y/X`, `Y/X → A/X` is strict (for the
induced and quotient filtrations). Stacks' proof computes `F^p(Y/X) = F^pY/F^pX` both ways and
uses `Y ∩ (F^pA + X) = (Y ∩ F^pA) + X`, the modular law in `Subobject A`.

The setting is `A : FilteredObject C I` over an abelian category `C` and an arbitrary index
category `I`, with `k : X ⟶ Y` and `n : Y ⟶ A.X` both arbitrary; the subobject `X ⊆ A` is
`k ≫ n`. The agreement of the two filtrations and all six strictness claims hold with no
hypothesis on `k` or `n` (for `k`, `n` not monomorphisms, `Y/X` is `Y/Im(k)` and "induced" means
pulled back along `Y/X → A/X`); `[Mono n]` is assumed only for the third isomorphism theorem
`Y/X = Ker(A/X → A/Y)` and its transport to filtered objects, `subquotientIsoKernelObj`.

* `subquotientObj A k n` is `Y/X = Coker k` with the quotient filtration of the induced
  filtration on `Y`, `F^i(Y/X) = π(Y ∩ F^iA)` (`subquotientObj_subobject`); it is definitionally
  `cokernelObj (pullbackObjHom A k n)`, the explicit model of the cokernel of `X → Y` in `Fil(𝒜)`
  (`subquotientObj_eq_cokernelObj`; `cokernelIsoCokernelObj` compares it with Mathlib's chosen
  `cokernel`). `subquotientHom A k n : Y/X ⟶ A/X` and `quotientHom A k n : A/X ⟶ A/Y` are the
  induced morphisms of filtered objects, `A/X` and `A/Y` carrying their quotient filtrations
  (`pushforwardMap` of `StacksCore.CategoryTheory.Filtration.Basic` for the squares
  `Y → A → A/X = Y → Y/X → A/X` and `A → A/X → A/Y = A → A/Y`;
  `pushforwardHom_comp_subquotientHom`, `pushforwardHom_comp_quotientHom`), and
  `Y/X → A/X → A/Y` is zero (`subquotientHom_comp_quotientHom`).
* On the underlying objects, the third isomorphism theorem lives in
  `StacksCore.CategoryTheory.Abelian.CommSq`: for a monomorphism `n`, `Y/X ⟶ A/X` is a monomorphism
  (`Abelian.mono_cokernel_map_comp`), `A/X ⟶ A/Y` is a cokernel of it
  (`Abelian.isColimitCokernelCoforkCokernelMap`, no hypothesis), hence `Y/X ⟶ A/X` is a kernel
  of `A/X ⟶ A/Y` (`Abelian.isLimitKernelForkCokernelMap`, `Abelian.cokernelIsoKernelCokernelMap`).
* The tag: `isStrictHom_subquotientHom`, `Y/X ⟶ A/X` is cartesian, i.e. the quotient filtration
  on `Y/X` is the filtration induced from `A/X`; `subquotientObj_subobject_eq_pullback` is the
  same statement on the steps, `F^i(Y/X) = q⁻¹(F^i(A/X))` along `q : Y/X → A/X`. Behind it is
  the lattice identity `π(Y ∩ F^iA) = q⁻¹(π'(F^iA))` in `Subobject (Y/X)`, for the quotient maps
  `π : Y → Y/X` and `π' : A → A/X` (`Abelian.Subobject.exists_pullback_eq_pullback_exists`),
  which after pulling back along the epimorphism `π` reads `n⁻¹(F^iA + X) = n⁻¹(F^iA) + X` in
  `Subobject Y` (`Abelian.Subobject.pullback_sup_exists`, for any `n`): the modular law
  `Y ∩ (F^iA + X) = (Y ∩ F^iA) + X` of Stacks' proof, read through `n`, from the instance
  `IsModularLattice (Subobject A)` ported from mathlib#41424 in
  `StacksCore.CategoryTheory.Abelian.Subobject` (delete-on-bump). `subquotientIsoPullbackObj` and
  `subquotientIsoKernelObj` are the literal forms: `Y/X` with the quotient filtration is
  `q⁻¹(A/X)`, the pullback along `q` of the quotient filtration on `A/X` (for a monomorphism `n`:
  the subobject `Y/X ⊆ A/X` with its induced filtration), and, for a monomorphism `n`,
  `Ker(A/X → A/Y)` with its induced filtration; both are isomorphisms in `Fil(𝒜)` over `A/X`
  (`subquotientIsoPullbackObj_hom_pullbackHom`, `subquotientIsoKernelObj_hom_kernelι`).
* The six strictness claims, all without hypothesis on `k`, `n`. `X → Y`, `X → A` (which is
  `pullbackHom A (k ≫ n)`) and `Y/X → A/X` are cartesian, by the instances
  `isStrictHom_pullbackObjHom` and `isStrictHom_pullbackHom` of
  `StacksCore.CategoryTheory.Filtration.Basic` and by the tag `isStrictHom_subquotientHom`, hence
  strict through the instance `IsStrictHom.isStrict`, which type class search applies. The
  instance `isStrict_pullbackHom` of `StacksCore.CategoryTheory.Filtration.Strict` covers `Y → A`
  (and `X → A` when `X ⊆ A`), the instance `isStrict_pushforwardHom` covers `Y → Y/X`, and
  `isStrict_pullbackHom_comp_pushforwardHom` covers `Y → A/X`. Only `Y → A/X` has
  content: it is the strict morphism `Y → A` (a strict monomorphism when `n` is) followed by the
  strict epimorphism `A → A/X`, and by Stacks 05SJ (1) such a composite need not be strict; here
  it is, because it is also the strict epimorphism `Y → Y/X` followed by the strict `Y/X → A/X`,
  to which 05SJ (3) applies (for a monomorphism `n` the latter is a strict monomorphism and
  05SJ (2) applies as well). `isStrict_quotientHom` (`A/X → A/Y`) is not part of the tag.
* Stacks 0128 applies this to a complex `α : A ⟶ B`, `β : B ⟶ D` in `Fil(𝒜)` with `Y := Ker β`
  and `X := Im α` inside `B`: `Ker β / Im α` with its (two equal) filtrations is
  `subquotientObj B (kernel.lift β.hom α.hom _) (kernel.ι β.hom)`, the cokernel of `A ⟶ Ker β`,
  which is Mathlib's model of homology (`ShortComplex.homologyIsoCokernelLift`); nothing is
  required of `kernel.lift β.hom α.hom _`, so everything above applies with no further hypothesis.

The functoriality of the induced and image filtrations in a commutative square, `pullbackMap`
and `pushforwardMap` in `StacksCore.CategoryTheory.Filtration.Basic`, is the general vocabulary
behind `subquotientHom`, `quotientHom` and the transport `subquotientIsoKernelObj`; it holds in
any category with pullbacks, resp. with images and image maps.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] {I : Type*} [Category* I]

namespace FilteredObject

section Subquotient

variable [Abelian C] (A : FilteredObject C I) {X Y : C} (k : X ⟶ Y) (n : Y ⟶ A.X)

/-- The subquotient `Y/X = Coker k` with the quotient filtration of the induced filtration on
`Y`, `F^i(Y/X) = π(Y ∩ F^iA)`; definitionally `cokernelObj (pullbackObjHom A k n)`, the explicit
model of the cokernel of `X → Y` in `Fil(𝒜)`. -/
noncomputable abbrev subquotientObj : FilteredObject C I :=
  pushforwardObj (pullbackObj A n) (cokernel.π k)

/-- `Y/X` with its quotient filtration is the cokernel of `X → Y` in `Fil(𝒜)` (as an explicit
model; `cokernelIsoCokernelObj` compares it with Mathlib's chosen cokernel). -/
theorem subquotientObj_eq_cokernelObj :
    subquotientObj A k n = cokernelObj (pullbackObjHom A k n) := rfl

/-- The steps of `Y/X`: the images in `Y/X` of the steps `Y ∩ F^iA` of `Y`. -/
lemma subquotientObj_subobject (i : I) :
    (subquotientObj A k n).subobject i =
      (Subobject.exists (cokernel.π k)).obj ((Subobject.pullback n).obj (A.subobject i)) := by
  rw [pushforwardObj_subobject, pullbackObj_subobject]

/-- `Y/X ⟶ A/X` as a morphism of filtered objects, `Y/X` with the quotient filtration of the
induced filtration on `Y` and `A/X` with the quotient filtration; its underlying morphism is
`Coker k ⟶ Coker (k ≫ n)`, and its level maps `π(Y ∩ F^iA) ⟶ π'(F^iA)` are induced on images
(`pushforwardMap`), for the quotient maps `π : Y → Y/X` and `π' : A → A/X`. -/
@[implicit_reducible]
noncomputable def subquotientHom : subquotientObj A k n ⟶ pushforwardObj A (cokernel.π (k ≫ n)) :=
  pushforwardMap (pullbackHom A n) (cokernel.π k) (cokernel.π (k ≫ n))
    (cokernel.map k (k ≫ n) (𝟙 X) n (by simp)) (by simp)

/-- The underlying morphism of `Y/X ⟶ A/X` is `Coker k ⟶ Coker (k ≫ n)`. -/
@[simp] lemma subquotientHom_hom :
    (subquotientHom A k n).hom = cokernel.map k (k ≫ n) (𝟙 X) n (by simp) := rfl

/-- `Y/X ⟶ A/X` is a monomorphism on the underlying objects when `n` is. (An instance:
`subquotientHom` is a `def`, so type class search cannot derive this from
`Abelian.mono_cokernel_map_comp`; `Mono (subquotientHom A k n)` itself is `mono_of_mono_hom _`.) -/
instance mono_subquotientHom_hom [Mono n] : Mono (subquotientHom A k n).hom :=
  inferInstanceAs (Mono (cokernel.map k (k ≫ n) (𝟙 X) n (by simp)))

/-- `Y → Y/X → A/X` is `Y → A → A/X`. -/
@[reassoc (attr := simp)]
lemma pushforwardHom_comp_subquotientHom :
    pushforwardHom (pullbackObj A n) (cokernel.π k) ≫ subquotientHom A k n =
      pullbackHom A n ≫ pushforwardHom A (cokernel.π (k ≫ n)) :=
  pushforwardHom_comp_pushforwardMap _ _ _ _ _

/-- `A/X ⟶ A/Y` as a morphism of filtered objects, both with their quotient filtrations; its
underlying morphism is `Coker (k ≫ n) ⟶ Coker n`, spelled `cokernel.map (k ≫ n) n k (𝟙 A)` as in
Mathlib's `kernelCokernelCompSequence` (`pushforwardMap` for `u = 𝟙 A`). -/
@[implicit_reducible]
noncomputable def quotientHom :
    pushforwardObj A (cokernel.π (k ≫ n)) ⟶ pushforwardObj A (cokernel.π n) :=
  pushforwardMap (𝟙 A) (cokernel.π (k ≫ n)) (cokernel.π n)
    (cokernel.map (k ≫ n) n k (𝟙 A.X) (by simp)) (by simp)

/-- The underlying morphism of `A/X ⟶ A/Y` is `Coker (k ≫ n) ⟶ Coker n`. -/
@[simp] lemma quotientHom_hom :
    (quotientHom A k n).hom = cokernel.map (k ≫ n) n k (𝟙 A.X) (by simp) := rfl

/-- `A → A/X → A/Y` is `A → A/Y`. -/
@[reassoc (attr := simp)]
lemma pushforwardHom_comp_quotientHom :
    pushforwardHom A (cokernel.π (k ≫ n)) ≫ quotientHom A k n = pushforwardHom A (cokernel.π n) :=
  hom_ext (by simp)

/-- `Y/X → A/X → A/Y` is zero. -/
@[reassoc (attr := simp)]
lemma subquotientHom_comp_quotientHom : subquotientHom A k n ≫ quotientHom A k n = 0 :=
  hom_ext (by simp)

/-- Stacks 0129: the two filtrations on `Y/X` agree, i.e. `Y/X ⟶ A/X` is cartesian: the quotient
filtration on `Y/X` (from the induced filtration on `Y`) is the filtration induced along
`Y/X ⟶ A/X` from the quotient filtration on `A/X`. On the steps this is the identity
`π(Y ∩ F^iA) = q⁻¹(π'(F^iA))`, `π : Y → Y/X`, `π' : A → A/X`, `q : Y/X → A/X`, the modular law
read in `Subobject (Y/X)`. No hypothesis on `k` or `n`: for a monomorphism `n` (Stacks' `Y ⊆ A`)
this is the statement of 0129; in general "induced" means pulled back along `Y/X → A/X`, and
`Mono n` enters only for `Y/X = Ker(A/X → A/Y)`. -/
@[stacks 0129 "`Y/X`'s quotient filtration is the one induced from `A/X`, so `Y/X → A/X` is
  strict; any `k`, `n`, any `I`"]
instance isStrictHom_subquotientHom : IsStrictHom (subquotientHom A k n) :=
  (isStrictHom_iff _).2 fun i => by
    rw [subquotientHom_hom, pushforwardObj_subobject, subquotientObj_subobject,
      Abelian.Subobject.exists_pullback_eq_pullback_exists]

/-- Stacks 0129 on the steps: `F^i(Y/X) = q⁻¹(F^i(A/X))`, the quotient filtration on `Y/X` is
the one induced from the quotient filtration on `A/X` along `q : Y/X ⟶ A/X`. -/
theorem subquotientObj_subobject_eq_pullback (i : I) :
    (subquotientObj A k n).subobject i =
      (Subobject.pullback (cokernel.map k (k ≫ n) (𝟙 X) n (by simp))).obj
        ((pushforwardObj A (cokernel.π (k ≫ n))).subobject i) :=
  ((isStrictHom_iff (subquotientHom A k n)).1 inferInstance i).symm

/-- Stacks 0129, literally: `Y/X` with the quotient filtration is `q⁻¹(A/X)`, the pullback along
`q : Y/X ⟶ A/X` of the quotient filtration on `A/X` (for a monomorphism `n`: the subobject
`Y/X ⊆ A/X` with its induced filtration), as filtered objects over `A/X`
(`subquotientIsoPullbackObj_hom_pullbackHom`). -/
@[stacks 0129 "`Y/X` with the quotient filtration is the pullback along `Y/X → A/X` of `A/X`"]
noncomputable def subquotientIsoPullbackObj :
    subquotientObj A k n ≅
      pullbackObj (pushforwardObj A (cokernel.π (k ≫ n)))
        (cokernel.map k (k ≫ n) (𝟙 X) n (by simp)) :=
  isoPullbackObj (subquotientHom A k n)

/-- `subquotientIsoPullbackObj` is an isomorphism over `A/X`. -/
@[reassoc (attr := simp)]
lemma subquotientIsoPullbackObj_hom_pullbackHom :
    (subquotientIsoPullbackObj A k n).hom ≫
        pullbackHom (pushforwardObj A (cokernel.π (k ≫ n)))
          (cokernel.map k (k ≫ n) (𝟙 X) n (by simp)) =
      subquotientHom A k n :=
  isoPullbackObj_hom_pullbackHom _

/-- The underlying morphism of `subquotientIsoPullbackObj` is the identity. -/
@[simp] lemma subquotientIsoPullbackObj_hom_hom :
    (subquotientIsoPullbackObj A k n).hom.hom = 𝟙 _ := rfl

/-- The underlying morphism of the inverse of `subquotientIsoPullbackObj` is the identity. -/
@[simp] lemma subquotientIsoPullbackObj_inv_hom :
    (subquotientIsoPullbackObj A k n).inv.hom = 𝟙 _ := rfl

/-- Stacks 0129, literally: `Y/X` with the quotient filtration is `Ker(A/X → A/Y)` with the
induced filtration, as filtered objects over `A/X` (`subquotientIsoKernelObj_hom_kernelι`); the
underlying isomorphism is the third isomorphism theorem `Abelian.cokernelIsoKernelCokernelMap`. -/
@[stacks 0129 "`Y/X` with the quotient filtration is `Ker(A/X → A/Y)` with the induced filtration"]
noncomputable def subquotientIsoKernelObj [Mono n] :
    subquotientObj A k n ≅ kernelObj (quotientHom A k n) :=
  subquotientIsoPullbackObj A k n ≪≫
    pullbackMapIso (Iso.refl _) (cokernel.map k (k ≫ n) (𝟙 X) n (by simp))
      (kernel.ι (quotientHom A k n).hom) (Abelian.cokernelIsoKernelCokernelMap k n) (by simp)

/-- `subquotientIsoKernelObj` is an isomorphism over `A/X`: followed by the kernel inclusion
`Ker(A/X → A/Y) ⟶ A/X` it is `Y/X ⟶ A/X`. -/
@[reassoc (attr := simp)]
lemma subquotientIsoKernelObj_hom_kernelι [Mono n] :
    (subquotientIsoKernelObj A k n).hom ≫ kernelι (quotientHom A k n) = subquotientHom A k n :=
  hom_ext (by
    simp only [subquotientIsoKernelObj, Iso.trans_hom, comp_hom,
      subquotientIsoPullbackObj_hom_hom, Category.id_comp]
    exact Abelian.cokernelIsoKernelCokernelMap_hom_comp_ι k n)

/-- Stacks 0129: `Y → A/X` is strict. This is the one claim with content: `Y → A/X` is the strict
morphism `Y → A` (a strict monomorphism when `n` is) followed by the strict epimorphism
`A → A/X`, and by Stacks 05SJ (1) such a composite need not be strict. Here it is, because it is
also the strict epimorphism `Y → Y/X` followed by the strict (cartesian) morphism `Y/X → A/X`, to
which Stacks 05SJ (3) applies (for a monomorphism `n` the latter is a strict monomorphism and
05SJ (2) applies as well). No hypothesis on `k`, `n`. -/
@[stacks 0129 "`Y → A/X` is strict; the case that is not formal from 05SJ"]
theorem isStrict_pullbackHom_comp_pushforwardHom :
    IsStrict (pullbackHom A n ≫ pushforwardHom A (cokernel.π (k ≫ n))) := by
  have : Epi (pushforwardHom (pullbackObj A n) (cokernel.π k)).hom :=
    inferInstanceAs (Epi (cokernel.π k))
  rw [← pushforwardHom_comp_subquotientHom]
  infer_instance

/-- `A/X → A/Y` is strict (not part of the tag): `A → A/X → A/Y` is the strict epimorphism
`A → A/Y`, and `A → A/X` is a strict epimorphism (Stacks 05SJ (3)). An instance: `quotientHom` is
a `def` and is not cartesian, so type class search cannot derive it. -/
instance isStrict_quotientHom : IsStrict (quotientHom A k n) := by
  have : Epi (pushforwardHom A (cokernel.π (k ≫ n))).hom := inferInstanceAs (Epi (cokernel.π _))
  rw [← isStrict_comp_iff_of_epi (pushforwardHom A (cokernel.π (k ≫ n))),
    pushforwardHom_comp_quotientHom]
  infer_instance

end Subquotient

end FilteredObject

end CategoryTheory
