module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import StacksFrontier.RingTheory.Localization.Glueing.CategoricalPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Gluing modules along a cartesian square of rings

A commutative square of commutative rings
```
B' --> B
 |     |
 v     v
A' --> A
```
lets one compare `B'`-modules with pairs of a `B`-module and an `A'`-module carrying a chosen
identification of their scalar extensions to `A`.  Such a pair is a *compatible pair*, an object
of the categorical pullback `Mod B ×_{Mod A} Mod A'`, and extension of scalars along the two maps
out of `B'` is the comparison functor.  This file constructs that functor and its right adjoint,
which glues a compatible pair into the `B'`-module of pairs that agree over `A`.

## Main definitions

* `ModuleGlueing.extendScalarsComp` compares extension of scalars along a composite with the
  composite of the two extensions, for rings in independent universes.
* `ModuleGlueing.extensionOfScalarsToPullback` is Stacks Tags 08KI and 0D2E: the comparison
  functor `Mod B' ⥤ Mod B ×_{Mod A} Mod A'`.
* `MilnorPatching.CompatiblePairs` is the submodule of pairs agreeing over `A`, and
  `MilnorPatching.compatiblePairsModule` the resulting `B'`-module.

## Main results

* `MilnorPatching.exists_rightAdjoint_extensionOfScalarsToPullback` is Stacks Tag 0D2F: the
  comparison functor has a right adjoint, whose value on a compatible pair is the module of
  compatible pairs and whose projections are the two component maps.

## Implementation notes

Mathlib models extension of scalars from `R` to `S` as `S ⊗[R] M`, reversing the displayed order
of tensor factors in the Stacks source; the comparison isomorphism for a composite is assembled
from the adjunctions defining extension of scalars.  The rings live in independent universes,
while the module categories share one upper universe together with an independent module
universe parameter.  Tag 0D2E is the same construction as Tag 08KI, so the two tags sit on one
declaration rather than on an alias.  The adjunction is produced from a hom-set equivalence
(`Adjunction.CoreHomEquiv`), which is what makes the unit and counit computable on elements.

## References

* [Stacks Project, Tag 08KI](https://stacks.math.columbia.edu/tag/08KI)
* [Stacks Project, Tag 0D2E](https://stacks.math.columbia.edu/tag/0D2E)
* [Stacks Project, Tag 0D2F](https://stacks.math.columbia.edu/tag/0D2F)
-/

section

open Submodule LinearEquiv

namespace MilnorPatching

open ModuleGlueing

@[expose] public section

/-- For a surjection `f : R →+* S` and an `R`-module `M`, the kernel of `m ↦ 1 ⊗ₜ m` is
`(ker f) • ⊤`; that is, `S ⊗[R] M` is `M / (ker f) M`. -/
lemma ker_tensorProductMk_of_surjective
    {R S M : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    (f : R →+* S) (hf : Function.Surjective f) :
    letI : Algebra R S := f.toAlgebra
    LinearMap.ker (TensorProduct.mk R S M 1) = RingHom.ker f • ⊤ := by
  let : Algebra R S := f.toAlgebra
  apply Submodule.comap_injective_of_surjective (TensorProduct.lid R M).surjective
  rw [← LinearMap.ker_comp]
  convert! (show LinearMap.ker (LinearMap.rTensor M (Algebra.linearMap R S)) =
      LinearMap.range (LinearMap.rTensor M (LinearMap.ker (Algebra.linearMap R S)).subtype) by
    rw [← LinearMap.exact_iff]
    exact rTensor_exact M
      (LinearMap.exact_subtype_ker_map (Algebra.linearMap R S)) hf)
  · ext
    simp
  · rw [Submodule.comap_equiv_eq_map_symm, map_symm_eq_iff,
      map_range_rTensor_subtype_lid]
    congr 1

end

end MilnorPatching
end

section

open CategoryTheory
open CategoryTheory.Limits
open scoped ChangeOfRings

namespace MilnorPatching

open ModuleGlueing
@[expose] public section

end

end MilnorPatching

end

section

section

open CategoryTheory
open CategoryTheory.Limits
open scoped ChangeOfRings

universe u uB' uB uR' uR

namespace MilnorPatching

open ModuleGlueing
@[expose] public section

/-- The compatible pairs underlying the module `N ×_φ M'`: a pair belongs to this type when
its two scalar extensions agree under the gluing isomorphism. -/
abbrev CompatiblePairs
    {B : Type uB} {R' : Type uR'} {R : Type uR}
    [CommRing B] [CommRing R'] [CommRing R]
    (BtoR : B →+* R) (R'toR : R' →+* R)
    (X : CategoricalPullback
      (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
      (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR)) :=
  { p : X.fst × X.snd //
    X.iso.hom ((1 : R) ⊗ₜ[B,BtoR] p.1) = (1 : R) ⊗ₜ[R',R'toR] p.2 }

variable {B' : Type uB'} {B : Type uB} {R' : Type uR'} {R : Type uR}
    [CommRing B'] [CommRing B] [CommRing R'] [CommRing R]
    (toB : B' →+* B) (toR' : B' →+* R') (BtoR : B →+* R) (R'toR : R' →+* R)
    (comm : BtoR.comp toB = R'toR.comp toR')

set_option backward.isDefEq.respectTransparency false in
/-- The zero pair is compatible: both scalar extensions of `0` are `0`. -/
public lemma compatible_zero (X : CategoricalPullback
    (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
    (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR)) :
    X.iso.hom ((1 : R) ⊗ₜ[B,BtoR] (0 : X.fst)) =
      (1 : R) ⊗ₜ[R',R'toR] (0 : X.snd) := by
  let : Module B R := Module.compHom R BtoR
  let : Module R' R := Module.compHom R R'toR
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The sum of two compatible pairs is compatible. -/
public lemma compatible_add (X : CategoricalPullback
    (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
    (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR))
    (x y : X.fst × X.snd)
    (hx : X.iso.hom ((1 : R) ⊗ₜ[B,BtoR] x.1) = (1 : R) ⊗ₜ[R',R'toR] x.2)
    (hy : X.iso.hom ((1 : R) ⊗ₜ[B,BtoR] y.1) = (1 : R) ⊗ₜ[R',R'toR] y.2) :
    X.iso.hom ((1 : R) ⊗ₜ[B,BtoR] (x.1 + y.1)) =
      (1 : R) ⊗ₜ[R',R'toR] (x.2 + y.2) := by
  let : Module B R := Module.compHom R BtoR
  let : Module R' R := Module.compHom R R'toR
  rw [TensorProduct.tmul_add (R := B), TensorProduct.tmul_add (R := R'), map_add]
  exact congrArg₂ (· + ·) hx hy

set_option backward.isDefEq.respectTransparency false in
/-- A compatible pair stays compatible after scaling by `b ∈ B'`, acting on the first component
through `toB` and on the second through `toR'`. -/
public lemma compatible_smul (X : CategoricalPullback
    (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
    (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR))
    (b : B') (x : X.fst × X.snd)
    (hx : X.iso.hom ((1 : R) ⊗ₜ[B,BtoR] x.1) = (1 : R) ⊗ₜ[R',R'toR] x.2) :
    (hcomm : BtoR.comp toB = R'toR.comp toR') →
    X.iso.hom ((1 : R) ⊗ₜ[B,BtoR] (toB b • x.1)) =
      (1 : R) ⊗ₜ[R',R'toR] (toR' b • x.2) := by
  intro hcomm
  let : Module B R := Module.compHom R BtoR
  let : Module R' R := Module.compHom R R'toR
  rw [TensorProduct.tmul_smul (R := B) (R' := B),
    TensorProduct.tmul_smul (R := R') (R' := R')]
  change X.iso.hom ((BtoR (toB b)) • ((1 : R) ⊗ₜ[B,BtoR] x.1)) =
    (R'toR (toR' b)) • ((1 : R) ⊗ₜ[R',R'toR] x.2)
  rw [X.iso.hom.hom.map_smul, hx]
  exact congrArg (fun r : R ↦ r • ((1 : R) ⊗ₜ[R',R'toR] x.2))
    (DFunLike.congr_fun hcomm b)

/-- The submodule of the product of the two restricted modules cut out by the gluing equation. -/
public noncomputable def compatibleSubmodule (X : CategoricalPullback
    (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
    (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR)) :
    letI : Module B' X.fst := Module.compHom X.fst toB
    letI : Module B' X.snd := Module.compHom X.snd toR'
    Submodule B' (X.fst × X.snd) := by
  letI : Module B' X.fst := Module.compHom X.fst toB
  letI : Module B' X.snd := Module.compHom X.snd toR'
  refine
    { carrier := { p | X.iso.hom ((1 : R) ⊗ₜ[B,BtoR] p.1) =
          (1 : R) ⊗ₜ[R',R'toR] p.2 }
      zero_mem' := compatible_zero.{u} BtoR R'toR X
      add_mem' := ?_
      smul_mem' := ?_ }
  · intro x y hx hy
    exact compatible_add.{u} BtoR R'toR X x y hx hy
  · intro b x hx
    exact compatible_smul.{u} toB toR' BtoR R'toR X b x hx comm

/-- The canonical `B'`-module of compatible pairs in a commutative square. Its underlying
type is `CompatiblePairs BtoR R'toR X`, addition is componentwise, and `b : B'` acts by
`(n, m') ↦ (toB b • n, toR' b • m')`. -/
public noncomputable abbrev compatiblePairsModule (X : CategoricalPullback
    (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
    (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR)) :
    ModuleCat.{max u uB uR' uR} B' :=
  letI : Module B' X.fst := Module.compHom X.fst toB
  letI : Module B' X.snd := Module.compHom X.snd toR'
  ModuleCat.of B' (compatibleSubmodule.{u} toB toR' BtoR R'toR comm X)

end
end MilnorPatching
end
section

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

universe u uB' uB uR' uR uA uS

namespace MilnorPatching

open ModuleGlueing
variable {B' : Type uB'} {B : Type uB} {R' : Type uR'} {R : Type uR}
    [CommRing B'] [CommRing B] [CommRing R'] [CommRing R]
    (toB : B' →+* B) (toR' : B' →+* R') (BtoR : B →+* R) (R'toR : R' →+* R)
    (comm : BtoR.comp toB = R'toR.comp toR')

set_option backward.isDefEq.respectTransparency false in
private lemma compatible_map {X Y : CategoricalPullback
    (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
    (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR)}
    (f : X ⟶ Y) (p : X.fst × X.snd)
    (hp : X.iso.hom ((1 : R) ⊗ₜ[B,BtoR] p.1) =
      (1 : R) ⊗ₜ[R',R'toR] p.2) :
    Y.iso.hom ((1 : R) ⊗ₜ[B,BtoR] (f.fst p.1)) =
      (1 : R) ⊗ₜ[R',R'toR] (f.snd p.2) := by
  have hw := DFunLike.congr_fun (congrArg ConcreteCategory.hom f.w)
    ((1 : R) ⊗ₜ[B,BtoR] p.1)
  change Y.iso.hom ((1 : R) ⊗ₜ[B,BtoR] (f.fst p.1)) =
    (ModuleCat.extendScalars R'toR).map f.snd
      (X.iso.hom ((1 : R) ⊗ₜ[B,BtoR] p.1)) at hw
  rw [hp] at hw
  exact hw

private noncomputable def compatiblePairsFunctor :
    CategoryTheory.Functor
      (CategoricalPullback (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
        (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR))
      (ModuleCat.{max u uB uR' uR} B') where
  obj X := by
    letI : Module B' X.fst := Module.compHom X.fst toB
    letI : Module B' X.snd := Module.compHom X.snd toR'
    exact compatiblePairsModule.{u} toB toR' BtoR R'toR comm X
  map {X Y} f := by
    letI : Module B' X.fst := Module.compHom X.fst toB
    letI : Module B' X.snd := Module.compHom X.snd toR'
    letI : Module B' Y.fst := Module.compHom Y.fst toB
    letI : Module B' Y.snd := Module.compHom Y.snd toR'
    exact ModuleCat.ofHom {
      toFun := fun p ↦ ⟨(f.fst p.1.1, f.snd p.1.2),
        compatible_map.{u} BtoR R'toR f p.1 p.2⟩
      map_add' := by intros; ext <;> simp
      map_smul' := by
        intro b p
        ext
        · change f.fst (toB b • p.1.1) = toB b • f.fst p.1.1
          rw [map_smul]
        · change f.snd (toR' b • p.1.2) = toR' b • f.snd p.1.2
          rw [map_smul] }
  map_id X := by ext p <;> rfl
  map_comp f g := by ext p <;> rfl

private lemma eqToIso_extendScalars_one_tmul
    {A : Type uA} {S : Type uS} [CommRing A] [CommRing S]
    (f g : A →+* S) (h : f = g) (L : ModuleCat.{u} A) (l : L) :
    ((eqToIso (congrArg ModuleCat.extendScalars h)).hom.app L)
        ((1 : S) ⊗ₜ[A,f] l) = (1 : S) ⊗ₜ[A,g] l := by
  cases h
  rfl

/-- The inverse of the extension-restriction hom-equivalence is evaluated on `1 ⊗ₜ l` by the
original map. -/
private lemma extendRestrictScalarsAdj_symm_apply_one_tmul.{v₁, a, s}
    {A : Type a} {S : Type s} [CommRing A] [CommRing S] (f : A →+* S)
    (L : ModuleCat.{max v₁ s} A) (M : ModuleCat.{max v₁ s} S)
    (k : L ⟶ (ModuleCat.restrictScalars f).obj M) (l : L) :
    ((ModuleCat.extendRestrictScalarsAdj.{v₁} f).homEquiv L M).symm k
      ((1 : S) ⊗ₜ[A,f] l) = k l := by
  have hh := congrArg (fun k : L ⟶ (ModuleCat.restrictScalars f).obj M ↦ k l)
    (((ModuleCat.extendRestrictScalarsAdj.{v₁} f).homEquiv L M).apply_symm_apply k)
  simp only [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
private lemma source_iso_one_tmul_one_tmul (L : ModuleCat.{max u uB uR' uR} B') (l : L) :
    ((extensionOfScalarsToPullback.{u} toB toR' BtoR R'toR comm).obj L).iso.hom
      ((1 : R) ⊗ₜ[B,BtoR] ((1 : B) ⊗ₜ[B',toB] l)) =
        (1 : R) ⊗ₜ[R',R'toR] ((1 : R') ⊗ₜ[B',toR'] l) := by
  change (((extendScalarsComp.{max u uB uR' uR} toB BtoR).symm ≪≫
      eqToIso (congrArg ModuleCat.extendScalars comm) ≪≫
      extendScalarsComp.{max u uB uR' uR} toR' R'toR).hom.app L)
        ((1 : R) ⊗ₜ[B,BtoR] ((1 : B) ⊗ₜ[B',toB] l)) = _
  let z : (ModuleCat.extendScalars (BtoR.comp toB)).obj L :=
    (1 : R) ⊗ₜ[B',BtoR.comp toB] l
  have hz : (extendScalarsComp.{max u uB uR' uR} toB BtoR).hom.app L z =
      (1 : R) ⊗ₜ[B,BtoR] ((1 : B) ⊗ₜ[B',toB] l) :=
    extendScalarsComp_hom_app_one_tmul.{max u uB uR' uR} toB BtoR L l
  have hi : (extendScalarsComp.{max u uB uR' uR} toB BtoR).inv.app L
      ((extendScalarsComp.{max u uB uR' uR} toB BtoR).hom.app L z) = z := by
    have h := (extendScalarsComp.{max u uB uR' uR} toB BtoR).hom_inv_id_app L
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
      DFunLike.congr_fun (congrArg ConcreteCategory.hom h) z
  simp only [Iso.trans_hom, NatTrans.comp_app, ConcreteCategory.comp_apply]
  erw [← hz, hi]
  rw [eqToIso_extendScalars_one_tmul.{max u uB uR' uR} (BtoR.comp toB) (R'toR.comp toR') comm L l]
  exact extendScalarsComp_hom_app_one_tmul.{max u uB uR' uR} toR' R'toR L l

set_option backward.isDefEq.respectTransparency false in
private lemma compatible_of_hom
    (L : ModuleCat.{max u uB uR' uR} B')
    (X : CategoricalPullback (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
      (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR))
    (f : (extensionOfScalarsToPullback.{u} toB toR' BtoR R'toR comm).obj L ⟶ X)
    (l : L) :
    X.iso.hom ((1 : R) ⊗ₜ[B,BtoR] (f.fst ((1 : B) ⊗ₜ[B',toB] l))) =
      (1 : R) ⊗ₜ[R',R'toR] (f.snd ((1 : R') ⊗ₜ[B',toR'] l)) := by
  have hw := DFunLike.congr_fun (congrArg ConcreteCategory.hom f.w)
    ((1 : R) ⊗ₜ[B,BtoR] ((1 : B) ⊗ₜ[B',toB] l))
  change X.iso.hom ((ModuleCat.extendScalars BtoR).map f.fst
      ((1 : R) ⊗ₜ[B,BtoR] ((1 : B) ⊗ₜ[B',toB] l))) =
    (ModuleCat.extendScalars R'toR).map f.snd
      (((extensionOfScalarsToPullback.{u} toB toR' BtoR R'toR comm).obj L).iso.hom
        ((1 : R) ⊗ₜ[B,BtoR] ((1 : B) ⊗ₜ[B',toB] l))) at hw
  rw [ModuleCat.ExtendScalars.map_tmul,
    source_iso_one_tmul_one_tmul.{u} toB toR' BtoR R'toR comm L l,
    ModuleCat.ExtendScalars.map_tmul] at hw
  exact hw

private noncomputable def compatibleFst
    (X : CategoricalPullback (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
      (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR)) :
    (compatiblePairsFunctor.{u} toB toR' BtoR R'toR comm).obj X ⟶
      (ModuleCat.restrictScalars toB).obj X.fst := by
  letI : Module B' X.fst := Module.compHom X.fst toB
  letI : Module B' X.snd := Module.compHom X.snd toR'
  exact ModuleCat.ofHom {
    toFun := fun p ↦ p.1.1
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

private noncomputable def compatibleSnd
    (X : CategoricalPullback (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
      (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR)) :
    (compatiblePairsFunctor.{u} toB toR' BtoR R'toR comm).obj X ⟶
      (ModuleCat.restrictScalars toR').obj X.snd := by
  letI : Module B' X.fst := Module.compHom X.fst toB
  letI : Module B' X.snd := Module.compHom X.snd toR'
  exact ModuleCat.ofHom {
    toFun := fun p ↦ p.1.2
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

set_option backward.isDefEq.respectTransparency false in
private noncomputable def homToCompatiblePairs
    (L : ModuleCat.{max u uB uR' uR} B')
    (X : CategoricalPullback (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
      (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR))
    (f : (extensionOfScalarsToPullback.{u} toB toR' BtoR R'toR comm).obj L ⟶ X) :
    L ⟶ (compatiblePairsFunctor.{u} toB toR' BtoR R'toR comm).obj X := by
  letI : Module B' X.fst := Module.compHom X.fst toB
  letI : Module B' X.snd := Module.compHom X.snd toR'
  let gB := (ModuleCat.extendRestrictScalarsAdj.{max u uB uR' uR} toB).homEquiv L X.fst f.fst
  let gR := (ModuleCat.extendRestrictScalarsAdj.{max u uB uR' uR} toR').homEquiv L X.snd f.snd
  exact ModuleCat.ofHom {
    toFun := fun l ↦ ⟨(gB l, gR l), by
      exact compatible_of_hom.{u} toB toR' BtoR R'toR comm L X f l⟩
    map_add' := by
      intro x y
      ext <;> simp [gB, gR]
    map_smul' := by
      intro b x
      ext
      · change gB (b • x) = b • gB x
        exact gB.hom.map_smul b x
      · change gR (b • x) = b • gR x
        exact gR.hom.map_smul b x }

set_option backward.isDefEq.respectTransparency false in
private lemma double_hom_ext (L : ModuleCat.{max u uB uR} B') (N : ModuleCat.{max u uB uR} R)
    {f g : ((ModuleCat.extendScalars BtoR).obj
      ((ModuleCat.extendScalars toB).obj L)) ⟶ N}
    (h : ∀ l : L, f ((1 : R) ⊗ₜ[B,BtoR] ((1 : B) ⊗ₜ[B',toB] l)) =
      g ((1 : R) ⊗ₜ[B,BtoR] ((1 : B) ⊗ₜ[B',toB] l))) : f = g := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  induction m using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  | tmul b l =>
    change B at b
    have hb : (b ⊗ₜ[B',toB] l : (ModuleCat.extendScalars toB).obj L) =
        b • ((1 : B) ⊗ₜ[B',toB] l) := by
      rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
    rw [hb, TensorProduct.tmul_smul (R := B) (R' := B)]
    change f ((BtoR b) • ((1 : R) ⊗ₜ[B,BtoR] ((1 : B) ⊗ₜ[B',toB] l))) =
      g ((BtoR b) • ((1 : R) ⊗ₜ[B,BtoR] ((1 : B) ⊗ₜ[B',toB] l)))
    rw [map_smul, map_smul, h l]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def compatiblePairsToHom
    (L : ModuleCat.{max u uB uR' uR} B')
    (X : CategoricalPullback (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
      (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR))
    (h : L ⟶ (compatiblePairsFunctor.{u} toB toR' BtoR R'toR comm).obj X) :
    (extensionOfScalarsToPullback.{u} toB toR' BtoR R'toR comm).obj L ⟶ X := by
  let fB := ((ModuleCat.extendRestrictScalarsAdj.{max u uB uR' uR} toB).homEquiv L X.fst).symm
    (h ≫ compatibleFst.{u} toB toR' BtoR R'toR comm X)
  let fR := ((ModuleCat.extendRestrictScalarsAdj.{max u uB uR' uR} toR').homEquiv L X.snd).symm
    (h ≫ compatibleSnd.{u} toB toR' BtoR R'toR comm X)
  have hB (l : L) : fB ((1 : B) ⊗ₜ[B',toB] l) = (h l).1.1 :=
    extendRestrictScalarsAdj_symm_apply_one_tmul.{max u uB uR' uR, _, _} toB L X.fst _ l
  have hR (l : L) : fR ((1 : R') ⊗ₜ[B',toR'] l) = (h l).1.2 :=
    extendRestrictScalarsAdj_symm_apply_one_tmul.{max u uB uR' uR, _, _} toR' L X.snd _ l
  exact {
    fst := fB
    snd := fR
    w := by
      apply double_hom_ext.{max u uR'} toB BtoR L _
      intro l
      change X.iso.hom ((ModuleCat.extendScalars BtoR).map fB
        ((1 : R) ⊗ₜ[B,BtoR] ((1 : B) ⊗ₜ[B',toB] l))) =
        (ModuleCat.extendScalars R'toR).map fR
          (((extensionOfScalarsToPullback.{u} toB toR' BtoR R'toR comm).obj L).iso.hom
            ((1 : R) ⊗ₜ[B,BtoR] ((1 : B) ⊗ₜ[B',toB] l)))
      rw [ModuleCat.ExtendScalars.map_tmul,
        source_iso_one_tmul_one_tmul.{u} toB toR' BtoR R'toR comm L l,
        ModuleCat.ExtendScalars.map_tmul, hB, hR]
      exact (h l).2 }

set_option backward.isDefEq.respectTransparency false in
private lemma compatiblePairsToHom_fst_one_tmul
    (L : ModuleCat.{max u uB uR' uR} B')
    (X : CategoricalPullback (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
      (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR))
    (h : L ⟶ (compatiblePairsFunctor.{u} toB toR' BtoR R'toR comm).obj X)
    (l : L) :
    (compatiblePairsToHom.{u} toB toR' BtoR R'toR comm L X h).fst
      ((1 : B) ⊗ₜ[B',toB] l) = (h l).1.1 := by
  exact extendRestrictScalarsAdj_symm_apply_one_tmul.{max u uB uR' uR, _, _} toB L X.fst _ l

set_option backward.isDefEq.respectTransparency false in
private lemma compatiblePairsToHom_snd_one_tmul
    (L : ModuleCat.{max u uB uR' uR} B')
    (X : CategoricalPullback (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
      (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR))
    (h : L ⟶ (compatiblePairsFunctor.{u} toB toR' BtoR R'toR comm).obj X)
    (l : L) :
    (compatiblePairsToHom.{u} toB toR' BtoR R'toR comm L X h).snd
      ((1 : R') ⊗ₜ[B',toR'] l) = (h l).1.2 := by
  exact extendRestrictScalarsAdj_symm_apply_one_tmul.{max u uB uR' uR, _, _} toR' L X.snd _ l

set_option backward.isDefEq.respectTransparency false in
private lemma compatiblePairsToHom_right_inv
    (L : ModuleCat.{max u uB uR' uR} B')
    (X : CategoricalPullback (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
      (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR))
    (h : L ⟶ (compatiblePairsFunctor.{u} toB toR' BtoR R'toR comm).obj X) :
    homToCompatiblePairs.{u} toB toR' BtoR R'toR comm L X
      (compatiblePairsToHom.{u} toB toR' BtoR R'toR comm L X h) = h := by
  apply ConcreteCategory.hom_ext
  intro l
  apply Subtype.ext
  apply Prod.ext
  · change ((ModuleCat.extendRestrictScalarsAdj.{max u uB uR' uR} toB).homEquiv L X.fst
        (compatiblePairsToHom.{u} toB toR' BtoR R'toR comm L X h).fst) l = (h l).1.1
    rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
    exact compatiblePairsToHom_fst_one_tmul.{u} toB toR' BtoR R'toR comm L X h l
  · change ((ModuleCat.extendRestrictScalarsAdj.{max u uB uR' uR} toR').homEquiv L X.snd
        (compatiblePairsToHom.{u} toB toR' BtoR R'toR comm L X h).snd) l = (h l).1.2
    rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
    exact compatiblePairsToHom_snd_one_tmul.{u} toB toR' BtoR R'toR comm L X h l

set_option backward.isDefEq.respectTransparency false in
private lemma compatiblePairsToHom_left_inv
    (L : ModuleCat.{max u uB uR' uR} B')
    (X : CategoricalPullback (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
      (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR))
    (f : (extensionOfScalarsToPullback.{u} toB toR' BtoR R'toR comm).obj L ⟶ X) :
    compatiblePairsToHom.{u} toB toR' BtoR R'toR comm L X
      (homToCompatiblePairs.{u} toB toR' BtoR R'toR comm L X f) = f := by
  apply CategoricalPullback.hom_ext
  · apply ModuleCat.ExtendScalars.hom_ext
    intro l
    change (compatiblePairsToHom.{u} toB toR' BtoR R'toR comm L X
        (homToCompatiblePairs.{u} toB toR' BtoR R'toR comm L X f)).fst
          ((1 : B) ⊗ₜ[B',toB] l) = f.fst ((1 : B) ⊗ₜ[B',toB] l)
    calc
      _ = ((homToCompatiblePairs.{u} toB toR' BtoR R'toR comm L X f) l).1.1 :=
        compatiblePairsToHom_fst_one_tmul.{u} toB toR' BtoR R'toR comm L X _ l
      _ = _ := rfl
  · apply ModuleCat.ExtendScalars.hom_ext
    intro l
    change (compatiblePairsToHom.{u} toB toR' BtoR R'toR comm L X
        (homToCompatiblePairs.{u} toB toR' BtoR R'toR comm L X f)).snd
          ((1 : R') ⊗ₜ[B',toR'] l) = f.snd ((1 : R') ⊗ₜ[B',toR'] l)
    calc
      _ = ((homToCompatiblePairs.{u} toB toR' BtoR R'toR comm L X f) l).1.2 :=
        compatiblePairsToHom_snd_one_tmul.{u} toB toR' BtoR R'toR comm L X _ l
      _ = _ := rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def compatiblePairsHomEquiv
    (L : ModuleCat.{max u uB uR' uR} B')
    (X : CategoricalPullback (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
      (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR)) :
    ((extensionOfScalarsToPullback.{u} toB toR' BtoR R'toR comm).obj L ⟶ X) ≃
      (L ⟶ (compatiblePairsFunctor.{u} toB toR' BtoR R'toR comm).obj X) where
  toFun := homToCompatiblePairs.{u} toB toR' BtoR R'toR comm L X
  invFun := compatiblePairsToHom.{u} toB toR' BtoR R'toR comm L X
  left_inv := compatiblePairsToHom_left_inv.{u} toB toR' BtoR R'toR comm L X
  right_inv := compatiblePairsToHom_right_inv.{u} toB toR' BtoR R'toR comm L X

set_option backward.isDefEq.respectTransparency false in
private lemma compatiblePairsHomEquiv_naturality_left_symm
    {L' L : ModuleCat.{max u uB uR' uR} B'}
    (a : L' ⟶ L)
    (X : CategoricalPullback (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
      (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR))
    (h : L ⟶ (compatiblePairsFunctor.{u} toB toR' BtoR R'toR comm).obj X) :
    (compatiblePairsHomEquiv.{u} toB toR' BtoR R'toR comm L' X).symm (a ≫ h) =
      (extensionOfScalarsToPullback.{u} toB toR' BtoR R'toR comm).map a ≫
        (compatiblePairsHomEquiv.{u} toB toR' BtoR R'toR comm L X).symm h := by
  apply CategoricalPullback.hom_ext
  · apply ModuleCat.ExtendScalars.hom_ext
    intro l
    change (compatiblePairsToHom.{u} toB toR' BtoR R'toR comm L' X (a ≫ h)).fst
        ((1 : B) ⊗ₜ[B',toB] l) =
      (compatiblePairsToHom.{u} toB toR' BtoR R'toR comm L X h).fst
        ((ModuleCat.extendScalars toB).map a ((1 : B) ⊗ₜ[B',toB] l))
    rw [ModuleCat.ExtendScalars.map_tmul]
    calc
      _ = ((a ≫ h) l).1.1 :=
        compatiblePairsToHom_fst_one_tmul.{u} toB toR' BtoR R'toR comm L' X _ l
      _ = (h (a l)).1.1 := rfl
      _ = _ := (compatiblePairsToHom_fst_one_tmul.{u} toB toR' BtoR R'toR comm L X h (a l)).symm
  · apply ModuleCat.ExtendScalars.hom_ext
    intro l
    change (compatiblePairsToHom.{u} toB toR' BtoR R'toR comm L' X (a ≫ h)).snd
        ((1 : R') ⊗ₜ[B',toR'] l) =
      (compatiblePairsToHom.{u} toB toR' BtoR R'toR comm L X h).snd
        ((ModuleCat.extendScalars toR').map a ((1 : R') ⊗ₜ[B',toR'] l))
    rw [ModuleCat.ExtendScalars.map_tmul]
    calc
      _ = ((a ≫ h) l).1.2 :=
        compatiblePairsToHom_snd_one_tmul.{u} toB toR' BtoR R'toR comm L' X _ l
      _ = (h (a l)).1.2 := rfl
      _ = _ := (compatiblePairsToHom_snd_one_tmul.{u} toB toR' BtoR R'toR comm L X h (a l)).symm

set_option backward.isDefEq.respectTransparency false in
private lemma compatiblePairsHomEquiv_naturality_right
    (L : ModuleCat.{max u uB uR' uR} B')
    {X Y : CategoricalPullback (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
      (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR)}
    (f : (extensionOfScalarsToPullback.{u} toB toR' BtoR R'toR comm).obj L ⟶ X)
    (g : X ⟶ Y) :
    (compatiblePairsHomEquiv.{u} toB toR' BtoR R'toR comm L Y) (f ≫ g) =
      (compatiblePairsHomEquiv.{u} toB toR' BtoR R'toR comm L X) f ≫
        (compatiblePairsFunctor.{u} toB toR' BtoR R'toR comm).map g := by
  apply ConcreteCategory.hom_ext
  intro l
  apply Subtype.ext
  apply Prod.ext
  · change ((ModuleCat.extendRestrictScalarsAdj.{max u uB uR' uR} toB).homEquiv L Y.fst
        (f ≫ g).fst) l =
      g.fst (((ModuleCat.extendRestrictScalarsAdj.{max u uB uR' uR} toB).homEquiv L X.fst f.fst) l)
    simp only [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
    rfl
  · change ((ModuleCat.extendRestrictScalarsAdj.{max u uB uR' uR} toR').homEquiv L Y.snd
        (f ≫ g).snd) l =
      g.snd (((ModuleCat.extendRestrictScalarsAdj.{max u uB uR' uR} toR').homEquiv L X.snd f.snd) l)
    simp only [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
    rfl

private noncomputable def compatiblePairsCore : Adjunction.CoreHomEquiv
    (extensionOfScalarsToPullback.{u} toB toR' BtoR R'toR comm)
    (compatiblePairsFunctor.{u} toB toR' BtoR R'toR comm) where
  homEquiv := compatiblePairsHomEquiv.{u} toB toR' BtoR R'toR comm
  homEquiv_naturality_left_symm := by
    intro L' L X a h
    exact compatiblePairsHomEquiv_naturality_left_symm.{u}
      toB toR' BtoR R'toR comm a X h
  homEquiv_naturality_right := by
    intro L X Y f g
    exact compatiblePairsHomEquiv_naturality_right.{u}
      toB toR' BtoR R'toR comm L f g

set_option backward.isDefEq.respectTransparency false in
/-- **Stacks Project, Tag 0D2F.** The extension-of-scalars functor associated to a commutative
square of rings has a right adjoint.  Its value on `(N, M', φ)` is naturally the `B'`-module
`N ×_φ M'` of compatible pairs. -/
@[stacks 0D2F]
public theorem exists_rightAdjoint_extensionOfScalarsToPullback
    {B' : Type uB'} {B : Type uB} {R' : Type uR'} {R : Type uR}
    [CommRing B'] [CommRing B] [CommRing R'] [CommRing R]
    (toB : B' →+* B) (toR' : B' →+* R') (BtoR : B →+* R) (R'toR : R' →+* R)
    (comm : BtoR.comp toB = R'toR.comp toR') :
    ∃ (F : CategoricalPullback (ModuleCat.extendScalars.{uB, uR, max u uB uR' uR} BtoR)
        (ModuleCat.extendScalars.{uR', uR, max u uB uR' uR} R'toR) ⥤ ModuleCat.{max u uB uR' uR} B')
      (e : ∀ X, F.obj X ≃ₗ[B']
        compatiblePairsModule.{u} toB toR' BtoR R'toR comm X)
      (adj : extensionOfScalarsToPullback.{u} toB toR' BtoR R'toR comm ⊣ F),
      (∀ {X Y} (f : X ⟶ Y) (p : F.obj X),
        (e Y (F.map f p)).1.1 = f.fst (e X p).1.1 ∧
          (e Y (F.map f p)).1.2 = f.snd (e X p).1.2) ∧
      ∀ (L : ModuleCat.{max u uB uR' uR} B') (X) (h : L ⟶ F.obj X) (l : L),
        (e X (h l)).1.1 =
            ((adj.homEquiv L X).symm h).fst ((1 : B) ⊗ₜ[B',toB] l) ∧
          (e X (h l)).1.2 =
            ((adj.homEquiv L X).symm h).snd ((1 : R') ⊗ₜ[B',toR'] l) := by
  let F := compatiblePairsFunctor.{u} toB toR' BtoR R'toR comm
  let core := compatiblePairsCore.{u} toB toR' BtoR R'toR comm
  let adj := Adjunction.mkOfHomEquiv core
  refine ⟨F, (fun X ↦ LinearEquiv.refl B' _), adj, ?_, ?_⟩
  · intro X Y f p
    exact ⟨rfl, rfl⟩
  intro L X h l
  have ha : (adj.homEquiv L X).symm h =
      compatiblePairsToHom.{u} toB toR' BtoR R'toR comm L X h := by
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  rw [ha]
  constructor
  · exact (compatiblePairsToHom_fst_one_tmul.{u}
      toB toR' BtoR R'toR comm L X h l).symm
  · exact (compatiblePairsToHom_snd_one_tmul.{u}
      toB toR' BtoR R'toR comm L X h l).symm

end MilnorPatching
end

end
