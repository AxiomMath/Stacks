module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Retract
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# A left-dual sheaf of modules is locally a direct summand of a finite free module

Let `(C, 𝒪)` be a ringed site: a site `(C, J)` together with a sheaf of commutative rings `𝒪`.
The category of sheaves of `𝒪`-modules carries the tensor product of Tag 01CA, the
sheafification of the objectwise tensor product, and is symmetric monoidal for it. Stacks Tag
0FNZ (1) says that if a sheaf of `𝒪`-modules `F` has a left dual `G` in that monoidal category,
then every object `U` of `C` has a covering on whose members `F` restricts to a direct summand
of a finite free module. This file proves that statement, together with the local dual-basis
identity that carries it.

The argument is the one in the source. The coevaluation `η : 𝒪 ⟶ F ⊗ G` is a section of a
*sheafified* tensor product, so after passing to a covering of `U` it becomes a finite sum of
pure tensors `η(1) = ∑ f j ⊗ g j`. Feeding that expansion into the first triangle identity of
the duality, and reading the identity on local sections, gives for every object `W` over `U` and
every section `x` of `F` over `W` the dual-basis formula
`x = ∑ j, ε(g j|_W ⊗ x) • f j|_W`. The `n` coordinate functions `x ↦ ε(g j|_W ⊗ x)` and the `n`
sections `f j` then assemble into a splitting of `F` restricted to the slice site over `U_i`
through the free module on `n` generators.

## Main definitions

* `Stacks.SheafOfModules.tensorSheafMap`: the map of tensor product sheaves induced by maps on
  the two factors.
* `Stacks.SheafOfModules.tensorSection` and `Stacks.SheafOfModules.unitTensorSection`: the pure
tensor
  of two local sections, and a local section of the structure sheaf read in the tensor unit, for
  a monoidal structure whose tensor product is the tensor product sheaf and whose unit is the
  structure sheaf.
* `Stacks.SheafOfModules.dualCoord`: the coordinate function attached by a left-dual pairing to
  a local section of the dual, as a map of modules of sections.
* `Stacks.SheafOfModules.dualCoordOver`: the same, as a morphism of sheaves of modules on the
  slice site over an object of `C`.
* `Stacks.SheafOfModules.overGlobalSection`: a section of `F` over `V`, read as a global section of
  the restriction of `F` to the slice site over `V`.

## Main results

* `Stacks.SheafOfModules.exists_cover_localDualBasis`: the local dual-basis identity. On a
  covering of any object the coevaluation of a left-dual pairing is a finite sum of pure tensors,
  and every local section of `F` is the corresponding dual-basis combination.
* `Stacks.SheafOfModules.nonempty_retract_free_of_localDualBasis`: a dual basis over `V` makes
  the restriction of `F` to the slice site over `V` a retract of a finite free module.
* `Stacks.SheafOfModules.exists_cover_retract_finiteFree_of_exactPairing`: **Tag 0FNZ (1)**.

Parts (2) and (3) of Tag 0FNZ — the identification of the dual with the sheaf of
homomorphisms into `𝒪`, and the evaluation formula — are not in this file. They are proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualSheafHomIso`, as
`Stacks.SheafOfModules.dualSheafIsoOfLeftDual` with
`dualSheafIsoOfLeftDual_hom_val_app` and
`Stacks.SheafOfModules.evaluation_eq_dualEval_dualSheafIsoOfLeftDual_inv`, from the
coherence-hypothesis-free form of part (1) and the uniqueness of a left dual.

## Implementation notes

**There is an assumption-free carrier of this tag elsewhere.**
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections` proves
`exists_cover_retract_finiteFree_of_exactPairing_tensorSheaf`, which carries
`@[stacks 0FNZ "local_finite_free_summand"]` with the **same conclusion** as the theorem below
and **six binders fewer**: no `M`, no `hunit`/`htensor`/`htensorMap`, and none of the three
coherence hypotheses. It is stated at the fixed `Strict.monoidalCategory`, whose associator and
unitors have sectionwise formulas.

The theorem below is kept, and its hypotheses are *not* removable, for a reason worth stating:
its `M` is an **explicit argument**, so the statement is "for every monoidal structure". The
three identifications pin down the tensor bifunctor and the unit but say nothing about `M`'s
associator, and deriving that would be the rigidity question — is a monoidal structure
determined by its tensor bifunctor and unit? — which needs an Eilenberg–Watts-style
identification of the natural automorphisms of the triple tensor functor plus pentagon/triangle
forcing the scalar to 1. That is not in this tree. So this declaration stays, general in `M`
and honest about its assumptions, as the engine of the other; the tag is carried there, on the
assumption-free statement at the structure Stacks actually means.

**The monoidal structure here is hypothesized, with its associator and unitors.** The pinned
Mathlib has no `MonoidalCategory (SheafOfModules R)` instance, so the monoidal structure is taken
as an argument `M` together with equations identifying its unit with `SheafOfModules.unit`, its
tensor product with `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, and its tensor of
  morphisms with `tensorSheafMap`.
Those identifications do **not** determine the associator or the unitors, and the proof genuinely
uses
all three: the triangle identity of a left dual reassociates `F ⊗ G ⊗ F`, and the two unitors are
what turn the identity into scalar multiplication. So three further hypotheses are assumed,
saying that the associator and the two unitors act on local pure tensors in the usual way. These
are not conveniences: they are part of the data of the symmetric monoidal structure of Tag 01CA
in which the source states the lemma, and with the tensor bifunctor alone pinned down the
statement is not provable.

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal` does construct an honest
`MonoidalCategory (SheafOfModules _)` on this branch, by localizing the presheaf monoidal
structure along sheafification using Tag 05NA. It is not used here: that construction produces
its associator and unitors from the universal property of the localization, so their action on
local pure tensors is not available, and `tensorObjIso` identifies the tensor product with
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` only up to isomorphism, not by the
  equality the hypotheses state. The
hypothesized form is also the more general statement.

**The spelling of the structure sheaf of rings.** Everything below is indexed at
`Stacks.SheafOfModules.Tensor.ringSheaf ⟨𝒪, _⟩`, the sheaf of rings
`𝒪 ⋙ forget₂ CommRingCat RingCat` of the ringed site, at the anonymous-constructor index `⟨𝒪, _⟩`
that this file's tensor products (`Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, _⟩`) are
themselves indexed at; the sheaf condition is supplied as
`Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪`, the reflection of the
sheaf condition along the forgetful functor. That spelling is load-bearing twice over. Mathlib's
monoidal structure on presheaves of modules, and the commutativity of the rings of sections it
rests on, are stated for a ring presheaf of the syntactic shape `𝒪 ⋙ forget₂ CommRingCat RingCat`,
and instance search does not see that shape through the `Sheaf` packaging performed by a plain
definition; with the `Stacks.SheafOfModules.TensorSheafification.structureSheaf` spelling the
sections of a tensor product and the sections of its factors end up indexed by two different
spellings of one ring and no scalar-multiplication or tensor lemma applies. This is the same
difficulty recorded in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleLocalSummand`. Since
`Stacks.SheafOfModules.Tensor.ringSheaf` is itself a plain `def`, it is declared
`local implicit_reducible` below: without that, `PresheafOfModules.tensorObj A.val` is rejected
with "not type-correct under the `implicit` transparency level", `A.val` being a presheaf of
modules over the canonical index rather than over `structureRingPresheaf 𝒪` literally. One place
needs more: in `tensorSection_smul_right` the base ring of `TensorProduct.tmul_smul` is left for
instance search to pick, and it picks the unfolded presheaf, so the index is written out there.

**The slice site.** The retract is built directly from the coordinate functions rather than by
restricting a tensor product to the slice site, which is what lets this file avoid the
comparison of the restriction of a tensor product of presheaves of modules with the tensor
product of the restrictions — the missing ingredient recorded in `InvertibleLocalSummand`. The
restriction `F.over V` is pushforward along `Over.forget V`, so its sections over `W : Over V`
are the sections of `F` over `W.left` and its restriction maps are those of `F`; both
identifications are definitional, and `dualCoordOver` is assembled from the ambient coordinate
functions using only that. The map into the free module is the finite sum
`∑ j, dualCoordOver (b j) ≫ ιFree j`, which needs no identification of a finite coproduct with a
product: `SheafOfModules` is preadditive, and that is enough.

**Universes.** The site has objects in `u` and morphisms in `v`, independent. The module universe
is forced to equal the universe `w` of the rings of sections: Mathlib's monoidal structure on
presheaves of modules exists only there, so the tensor product sheaf of Tag 05NA, and hence this
statement, is available at no other module universe. The index type of the finite free module is
`ULift.{w} (Fin n)`, the smallest `Type w` of the right cardinality.

## References

* [Stacks Project, Tag 0FNZ](https://stacks.math.columbia.edu/tag/0FNZ)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP) — left duals in a
  monoidal category.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
-/

@[expose] public section

open CategoryTheory Limits Opposite MonoidalCategory

open scoped TensorProduct

universe v u w

namespace Stacks.SheafOfModules

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

section EqToHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

private lemma eqToHom_symm_val_app_apply {A B : SheafOfModules.{w} R} (h : A = B) (V : Cᵒᵖ)
    (z : A.val.obj V) :
    (eqToHom h.symm).val.app V ((eqToHom h).val.app V z) = z := by
  subst h; simp

private lemma app_sum_apply {A B : SheafOfModules.{w} R} (φ : A ⟶ B) (V : Cᵒᵖ) {n : ℕ}
    (z : Fin n → A.val.obj V) :
    φ.val.app V (∑ j, z j) = ∑ j, φ.val.app V (z j) :=
  map_sum (φ.val.app V).hom _ Finset.univ

private lemma map_sum_apply (A : SheafOfModules.{w} R) {V W : Cᵒᵖ} (k : V ⟶ W) {n : ℕ}
    (z : Fin n → A.val.obj V) :
    A.val.map k (∑ j, z j) = ∑ j, A.val.map k (z j) :=
  map_sum (A.val.map k).hom _ Finset.univ

/-- A sum of morphisms of sheaves of modules, evaluated on a local section. -/
private lemma sum_val_app_apply {A B : SheafOfModules.{w} R} {ι : Type*}
    (t : Finset ι) (φ : ι → (A ⟶ B)) (V : Cᵒᵖ) (z : A.val.obj V) :
    (∑ i ∈ t, φ i).val.app V z = ∑ i ∈ t, (φ i).val.app V z := by
  classical
  induction t using Finset.induction with
  | empty => rfl
  | insert a u ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; simp

private lemma unitHomEquiv_symm_val_app_apply {A : SheafOfModules.{w} R}
    (t : A.sections) (V : Cᵒᵖ) (c : R.obj.obj V) :
    (A.unitHomEquiv.symm t).val.app V c = c • t.eval V := rfl

end EqToHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

private lemma sheafification_map_unit
    {P Q : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      𝒪)}
    (f : P ⟶ Q) (V : Cᵒᵖ) (x : P.obj V) :
    ((Stacks.SheafOfModules.TensorSheafification.sheafify 𝒪 h𝒪).map f).val.app V
      ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 P).app V x) =
      (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 Q).app V (f.app V x) :=
  (congrArg (fun k ↦ k.app V x) ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪
    h𝒪).unit.naturality f)).symm

private lemma toSheafify_naturality
    (P : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
      {V W : Cᵒᵖ} (k : V ⟶ W)
    (z : P.obj V) :
    ((Stacks.SheafOfModules.TensorSheafification.sheafify 𝒪 h𝒪).obj P).val.map k
      ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 P).app V z) =
      (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 P).app W (P.map k z) :=
  (PresheafOfModules.naturality_apply (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 P)
    k z).symm

section

variable [MonoidalCategory (SheafOfModules.{w} (Tensor.ringSheaf
    ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))]

/-- The pure tensor of two local sections. -/
noncomputable def tensorSection
    (htensor : ∀ A B : SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩),
      A ⊗ B = ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj A).obj B)
    (A B : SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)) (V : Cᵒᵖ)
    (a : A.val.obj V) (b : B.val.obj V) : (A ⊗ B).val.obj V :=
  (eqToHom (htensor A B).symm).val.app V
    ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (A.val ⊗ B.val)).app V (a
      ⊗ₜ[(Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V] b))

/-- A local section of the structure sheaf, viewed in the tensor unit.

Named `unitTensorSection` rather than `unitSection` to avoid a name clash in this namespace:
`…Sheaf.FinitePresentationStalk` declares a `unitSection`, and two declarations of one name make
the modules impossible to co-import. DEDUP OWED, three spellings of two notions:
`…Sheaf.StalkFreeCover.toUnit` is this construction without the `hunit` transport, and
`StalkFreeCover.unitOne` / `FinitePresentationStalk.unitSection` are both the section `1` (at
site and `Opens` level respectively). The right merge is onto `toUnit` and `unitOne`. -/
noncomputable def unitTensorSection
    (hunit : 𝟙_ (SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)) =
      SheafOfModules.unit (Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))
    (V : Cᵒᵖ) (r : (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V) :
    (𝟙_ (SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))).val.obj V :=
  (eqToHom hunit.symm).val.app V r

section Lemmas

variable {htensor : ∀ A B : SheafOfModules.{w} (Tensor.ringSheaf
    ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩),
    A ⊗ B = ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj A).obj B}

/-- The tensor of two morphisms acts on pure tensors of local sections in the obvious way. -/
lemma tensorSection_map
    (htensorMap : ∀ {A A' B B' : SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)}
      (f : A ⟶ A') (g : B ⟶ B'),
      eqToHom (htensor A B).symm ≫ (f ⊗ₘ g) ≫ eqToHom (htensor A' B') =
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)).map ((f, g) : (_, _) ⟶ (_, _)))
    {A A' B B' : SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)}
    (f : A ⟶ A') (g : B ⟶ B') (V : Cᵒᵖ) (x : A.val.obj V) (y : B.val.obj V) :
    (f ⊗ₘ g).val.app V (tensorSection 𝒪 h𝒪 htensor A B V x y) =
      tensorSection 𝒪 h𝒪 htensor A' B' V (f.val.app V x) (g.val.app V y) := by
  have h1 := congrArg
    (fun φ : ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj A).obj B ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj A').obj B' ↦
      φ.val.app V ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (A.val ⊗ B.val)).app
        V
        (x ⊗ₜ[(Tensor.ringSheaf
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V] y)))
    ((htensorMap f g).trans
      (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map.{u, v, w, w, w}
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩ f g))
  have h2 := sheafification_map_unit 𝒪 h𝒪
    (PresheafOfModules.tensorHom (O := 𝒪) f.val g.val) V
      (x ⊗ₜ[(Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V] y)
  have mappedPureTensor := congrArg
    (fun value => (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
      (PresheafOfModules.tensorObj (O := 𝒪) A'.val B'.val)).app V value)
    (PresheafOfModules.tensorHom_tmul (O := 𝒪) f.val g.val V x y)
  have step : (eqToHom (htensor A' B')).val.app V
        ((f ⊗ₘ g).val.app V (tensorSection 𝒪 h𝒪 htensor A B V x y)) =
      (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (A'.val ⊗ B'.val)).app V
        (f.val.app V x ⊗ₜ[(Tensor.ringSheaf
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V] g.val.app V y) :=
    h1.trans (h2.trans mappedPureTensor)
  exact (eqToHom_symm_val_app_apply (htensor A' B') V _).symm.trans
    (congrArg ((eqToHom (htensor A' B').symm).val.app V) step)

/-- Right whiskering acts on pure tensors of local sections. -/
lemma tensorSection_whiskerRight
    (htensorMap : ∀ {A A' B B' : SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)}
      (f : A ⟶ A') (g : B ⟶ B'),
      eqToHom (htensor A B).symm ≫ (f ⊗ₘ g) ≫ eqToHom (htensor A' B') =
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)).map ((f, g) : (_, _) ⟶ (_, _)))
    {A A' B : SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)}
    (f : A ⟶ A') (V : Cᵒᵖ) (x : A.val.obj V) (y : B.val.obj V) :
    (f ▷ B).val.app V (tensorSection 𝒪 h𝒪 htensor A B V x y) =
      tensorSection 𝒪 h𝒪 htensor A' B V (f.val.app V x) y := by
  have h := tensorSection_map 𝒪 h𝒪 htensorMap f (𝟙 B) V x y
  rw [MonoidalCategory.tensorHom_id] at h
  exact h

/-- Left whiskering acts on pure tensors of local sections. -/
lemma tensorSection_whiskerLeft
    (htensorMap : ∀ {A A' B B' : SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)}
      (f : A ⟶ A') (g : B ⟶ B'),
      eqToHom (htensor A B).symm ≫ (f ⊗ₘ g) ≫ eqToHom (htensor A' B') =
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)).map ((f, g) : (_, _) ⟶ (_, _)))
    {A B B' : SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)}
    (g : B ⟶ B') (V : Cᵒᵖ) (x : A.val.obj V) (y : B.val.obj V) :
    (A ◁ g).val.app V (tensorSection 𝒪 h𝒪 htensor A B V x y) =
      tensorSection 𝒪 h𝒪 htensor A B' V x (g.val.app V y) := by
  have h := tensorSection_map 𝒪 h𝒪 htensorMap (𝟙 A) g V x y
  rw [MonoidalCategory.id_tensorHom] at h
  exact h

/-- A sum of pure tensors of local sections, read in the tensor product. -/
lemma tensorSection_sum
    (A B : SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)) (V : Cᵒᵖ) {n : ℕ}
    (a : Fin n → A.val.obj V) (b : Fin n → B.val.obj V) :
    (eqToHom (htensor A B).symm).val.app V
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (A.val ⊗ B.val)).app V
          (∑ j, a j ⊗ₜ[(Tensor.ringSheaf
              ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V] b j)) =
      ∑ j, tensorSection 𝒪 h𝒪 htensor A B V (a j) (b j) := by
  refine (congrArg ((eqToHom (htensor A B).symm).val.app V)
    (map_sum ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (A.val ⊗ B.val)).app
      V).hom
      _ Finset.univ)).trans ?_
  exact map_sum ((eqToHom (htensor A B).symm).val.app V).hom _ Finset.univ

/-- Restriction of a pure tensor of local sections is the pure tensor of the restrictions. -/
lemma tensorSection_restrict
    (A B : SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)) {V W : Cᵒᵖ} (k : V ⟶ W)
    (x : A.val.obj V) (y : B.val.obj V) :
    (A ⊗ B).val.map k (tensorSection 𝒪 h𝒪 htensor A B V x y) =
      tensorSection 𝒪 h𝒪 htensor A B W (A.val.map k x) (B.val.map k y) :=
  ((PresheafOfModules.naturality_apply (eqToHom (htensor A B).symm).val k
      ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (A.val ⊗ B.val)).app V
        (x ⊗ₜ[(Tensor.ringSheaf
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V] y))).symm).trans
    (congrArg ((eqToHom (htensor A B).symm).val.app W)
      (toSheafify_naturality 𝒪 h𝒪 (A.val ⊗ B.val) k (x ⊗ₜ[(Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V] y)))

/-- A pure tensor is additive in its first argument. -/
lemma tensorSection_sum_left
    (A B : SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)) (V : Cᵒᵖ)
    {n : ℕ} (a : Fin n → A.val.obj V) (b : B.val.obj V) :
    tensorSection 𝒪 h𝒪 htensor A B V (∑ j, a j) b =
      ∑ j, tensorSection 𝒪 h𝒪 htensor A B V (a j) b := by
  dsimp only [tensorSection]
  rw [TensorProduct.sum_tmul]
  exact tensorSection_sum 𝒪 h𝒪 (htensor := htensor) A B V a fun _ ↦ b

/-- A pure tensor is additive in its second argument. -/
lemma tensorSection_add_right
    (A B : SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)) (V : Cᵒᵖ)
    (x : A.val.obj V) (y y' : B.val.obj V) :
    tensorSection 𝒪 h𝒪 htensor A B V x (y + y') =
      tensorSection 𝒪 h𝒪 htensor A B V x y + tensorSection 𝒪 h𝒪 htensor A B V x y' := by
  dsimp only [tensorSection]
  rw [TensorProduct.tmul_add]
  refine (congrArg ((eqToHom (htensor A B).symm).val.app V)
    (map_add ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (A.val ⊗ B.val)).app
      V).hom _ _)).trans ?_
  exact map_add ((eqToHom (htensor A B).symm).val.app V).hom _ _

/-- A pure tensor is homogeneous in its second argument. -/
lemma tensorSection_smul_right
    (A B : SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)) (V : Cᵒᵖ)
    (c : (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V)
    (x : A.val.obj V) (y : B.val.obj V) :
    tensorSection 𝒪 h𝒪 htensor A B V x (c • y) =
      c • tensorSection 𝒪 h𝒪 htensor A B V x y := by
  dsimp only [tensorSection]
  refine (congrArg (fun z ↦ (eqToHom (htensor A B).symm).val.app V
      ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (A.val ⊗ B.val)).app V z))
    (TensorProduct.tmul_smul (R := ((Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V))
      c x y)).trans ?_
  refine (congrArg ((eqToHom (htensor A B).symm).val.app V)
    (map_smul ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (A.val ⊗ B.val)).app
      V).hom c _)).trans ?_
  exact map_smul ((eqToHom (htensor A B).symm).val.app V).hom c _

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Restriction of the local section of the tensor unit attached to a section of the
structure sheaf. -/
lemma unitSection_map
    (hunit : 𝟙_ (SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)) =
      SheafOfModules.unit (Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))
    {V W : Cᵒᵖ} (k : V ⟶ W) (r : (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V) :
    (𝟙_ (SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))).val.map k
        (unitTensorSection 𝒪 h𝒪 hunit V r) =
      unitTensorSection 𝒪 h𝒪 hunit W ((Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.map k r) :=
  (PresheafOfModules.naturality_apply (eqToHom hunit.symm).val k r).symm

end Lemmas

end

/-- **The local dual-basis identity.** Let `F` and `G` be sheaves of modules on a ringed site,
with `G` a left dual of `F` for a monoidal structure whose tensor product is the tensor product
sheaf and whose unit is the structure sheaf. Then every object `U` of the site has a covering on
whose members the coevaluation is a finite sum of pure tensors `∑ f j ⊗ g j`, and the first
triangle identity turns this into a dual-basis formula for every local section of `F`.

The three coherence hypotheses say that the associator and the two unitors of the monoidal
structure act on local pure tensors in the usual way; this is part of the data of the symmetric
monoidal structure on modules on a ringed site which the source assumes. -/
theorem exists_cover_localDualBasis
    (F G : SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))
    (M : MonoidalCategory (SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))) :
    letI := M
    ∀ (hunit : 𝟙_ (SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)) =
          SheafOfModules.unit (Tensor.ringSheaf
              ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))
      (htensor : ∀ A B : SheafOfModules.{w} (Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩),
          A ⊗ B = ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj A).obj B)
      (_htensorMap : ∀ {A A' B B' : SheafOfModules.{w} (Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)}
          (f : A ⟶ A') (g : B ⟶ B'),
          eqToHom (htensor A B).symm ≫ (f ⊗ₘ g) ≫ eqToHom (htensor A' B') =
            (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)).map ((f, g) : (_, _) ⟶ (_, _)))
      (_hassociator : ∀ (A B D : SheafOfModules.{w} (Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))
          (V : Cᵒᵖ) (a : A.val.obj V) (b : B.val.obj V) (c : D.val.obj V),
          (α_ A B D).hom.val.app V
              (tensorSection 𝒪 h𝒪 htensor (A ⊗ B) D V
                (tensorSection 𝒪 h𝒪 htensor A B V a b) c) =
            tensorSection 𝒪 h𝒪 htensor A (B ⊗ D) V a
              (tensorSection 𝒪 h𝒪 htensor B D V b c))
      (_hleftUnitor : ∀ (A : SheafOfModules.{w} (Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)) (V : Cᵒᵖ)
          (r : (Tensor.ringSheaf
              ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V) (a : A.val.obj V),
          (λ_ A).hom.val.app V
              (tensorSection 𝒪 h𝒪 htensor _ A V (unitTensorSection 𝒪 h𝒪 hunit V r) a) = r • a)
      (_hrightUnitor : ∀ (A : SheafOfModules.{w} (Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)) (V : Cᵒᵖ)
          (a : A.val.obj V) (r : (Tensor.ringSheaf
              ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V),
          (ρ_ A).hom.val.app V
              (tensorSection 𝒪 h𝒪 htensor A _ V a (unitTensorSection 𝒪 h𝒪 hunit V r)) = r • a)
      (_p : ExactPairing F G) (U : C),
      let coev (V : Cᵒᵖ) : (F ⊗ G).val.obj V :=
        (ExactPairing.coevaluation F G).val.app V (unitTensorSection 𝒪 h𝒪 hunit V 1)
      let eval (V : Cᵒᵖ) (t : (G ⊗ F).val.obj V) :
          (Tensor.ringSheaf
              ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V :=
        (eqToHom hunit).val.app V ((ExactPairing.evaluation F G).val.app V t)
      ∃ S : Sieve U, S ∈ J U ∧
        ∀ (V : C) (i : V ⟶ U), S i →
          ∃ n : ℕ, ∃ (f : Fin n → F.val.obj (op V)) (g : Fin n → G.val.obj (op V)),
            coev (op V) = ∑ j, tensorSection 𝒪 h𝒪 htensor F G (op V) (f j) (g j) ∧
            ∀ (W : C) (k : W ⟶ V) (x : F.val.obj (op W)),
              x = ∑ j, @SMul.smul ((Tensor.ringSheaf
                  ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj (op W))
                  (F.val.obj (op W)) _
                  (eval (op W) (tensorSection 𝒪 h𝒪 htensor G F (op W)
                    (G.val.map k.op (g j)) x))
                  (F.val.map k.op (f j)) := by
  classical
  intro hunit htensor htensorMap hassociator hleftUnitor hrightUnitor p U
  have tsMap : ∀ {A A' B B' : SheafOfModules.{w} (Tensor.ringSheaf
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)}
      (a : A ⟶ A') (b : B ⟶ B') (V : Cᵒᵖ) (x : A.val.obj V) (y : B.val.obj V),
      (a ⊗ₘ b).val.app V (tensorSection 𝒪 h𝒪 htensor A B V x y) =
        tensorSection 𝒪 h𝒪 htensor A' B' V (a.val.app V x) (b.val.app V y) :=
    fun a b V x y ↦ tensorSection_map 𝒪 h𝒪 htensorMap a b V x y
  have tsRes := tensorSection_restrict 𝒪 h𝒪 (htensor := htensor)
  have tsSum := tensorSection_sum_left 𝒪 h𝒪 (htensor := htensor)
  have uMap : ∀ {V₁ V₂ : Cᵒᵖ} (k : V₁ ⟶ V₂) (r : (Tensor.ringSheaf
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V₁),
      (𝟙_ (SheafOfModules.{w} (Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))).val.map k
          (unitTensorSection 𝒪 h𝒪 hunit V₁ r) =
        unitTensorSection 𝒪 h𝒪 hunit V₂ ((Tensor.ringSheaf
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.map k r) :=
    fun k r ↦ unitSection_map 𝒪 h𝒪 hunit k r
  -- the coevaluation, read in the tensor product sheaf
  have hcoevRestrict : ∀ {V₁ V₂ : Cᵒᵖ} (k : V₁ ⟶ V₂),
      (F ⊗ G).val.map k
          ((ExactPairing.coevaluation F G).val.app V₁ (unitTensorSection 𝒪 h𝒪 hunit V₁ 1)) =
        (ExactPairing.coevaluation F G).val.app V₂ (unitTensorSection 𝒪 h𝒪 hunit V₂ 1) := by
    intro V₁ V₂ k
    refine ((PresheafOfModules.naturality_apply (ExactPairing.coevaluation F G).val k
      (unitTensorSection 𝒪 h𝒪 hunit V₁ 1)).symm).trans ?_
    refine congrArg ((ExactPairing.coevaluation F G).val.app V₂) ?_
    rw [uMap]
    exact congrArg (unitTensorSection 𝒪 h𝒪 hunit V₂) (map_one _)
  have hcRestrict : ∀ {V₁ V₂ : Cᵒᵖ} (k : V₁ ⟶ V₂),
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj F).obj G).val.map k
          ((eqToHom (htensor F G)).val.app V₁
            ((ExactPairing.coevaluation F G).val.app V₁ (unitTensorSection 𝒪 h𝒪 hunit V₁ 1))) =
        (eqToHom (htensor F G)).val.app V₂
          ((ExactPairing.coevaluation F G).val.app V₂ (unitTensorSection 𝒪 h𝒪 hunit V₂ 1)) := by
    intro V₁ V₂ k
    refine ((PresheafOfModules.naturality_apply (eqToHom (htensor F G)).val k _).symm).trans ?_
    exact congrArg ((eqToHom (htensor F G)).val.app V₂) (hcoevRestrict k)
  have hsurj : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf (Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj).map
        (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (F.val ⊗ G.val))) := by
    change Presheaf.IsLocallySurjective J
      (CategoryTheory.toSheafify J
        ((PresheafOfModules.toPresheaf (Tensor.ringSheaf
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj).obj
          (PresheafOfModules.tensorObj (O := 𝒪) F.val G.val)))
    infer_instance
  refine ⟨_, hsurj.imageSieve_mem
    ((eqToHom (htensor F G)).val.app (op U)
      ((ExactPairing.coevaluation F G).val.app (op U)
        (unitTensorSection 𝒪 h𝒪 hunit (op U) 1))), ?_⟩
  intro V i hi
  obtain ⟨t, ht⟩ := hi
  obtain ⟨n, f, g, htens⟩ := TensorProduct.exists_sum_tmul_eq t
  have hct : (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (F.val ⊗ G.val)).app (op V)
    t =
      (eqToHom (htensor F G)).val.app (op V)
        ((ExactPairing.coevaluation F G).val.app (op V) (unitTensorSection 𝒪 h𝒪 hunit (op V) 1)) :=
    ht.trans (hcRestrict i.op)
  have hA : (eqToHom (htensor F G).symm).val.app (op V)
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (F.val ⊗ G.val)).app (op V) t)
          =
      (ExactPairing.coevaluation F G).val.app (op V) (unitTensorSection 𝒪 h𝒪 hunit (op V) 1) :=
    (congrArg ((eqToHom (htensor F G).symm).val.app (op V)) hct).trans
      (eqToHom_symm_val_app_apply (htensor F G) (op V) _)
  have hB : (eqToHom (htensor F G).symm).val.app (op V)
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (F.val ⊗ G.val)).app (op V) t)
          =
      ∑ j, tensorSection 𝒪 h𝒪 htensor F G (op V) (f j) (g j) := by
    rw [htens]
    exact tensorSection_sum 𝒪 h𝒪 F G (op V) f g
  have hfin := hA.symm.trans hB
  refine ⟨n, f, g, hfin, ?_⟩
  intro W k x
  have hcoeW : (ExactPairing.coevaluation F G).val.app (op W)
        (unitTensorSection 𝒪 h𝒪 hunit (op W) 1) =
      ∑ j, tensorSection 𝒪 h𝒪 htensor F G (op W)
        (F.val.map k.op (f j)) (G.val.map k.op (g j)) := by
    rw [← hcoevRestrict k.op, hfin, map_sum_apply]
    exact Finset.sum_congr rfl fun j _ ↦ tsRes F G k.op (f j) (g j)
  have htriEnd : (λ_ F).inv ≫ (η_ F G ▷ F) ≫ (α_ F G F).hom ≫ (F ◁ ε_ F G) ≫ (ρ_ F).hom
      = 𝟙 F := by
    calc
      (λ_ F).inv ≫ (η_ F G ▷ F) ≫ (α_ F G F).hom ≫ (F ◁ ε_ F G) ≫ (ρ_ F).hom
          = (λ_ F).inv ≫ ((η_ F G ▷ F) ≫ (α_ F G F).hom ≫ (F ◁ ε_ F G)) ≫ (ρ_ F).hom := by
            simp [Category.assoc]
      _ = (λ_ F).inv ≫ ((λ_ F).hom ≫ (ρ_ F).inv) ≫ (ρ_ F).hom := by
            rw [ExactPairing.evaluation_coevaluation F G]
      _ = 𝟙 F := by simp
  have htriX := congrArg (fun φ : F ⟶ F ↦ φ.val.app (op W) x) htriEnd
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply] at htriX
  have hleft : (λ_ F).inv.val.app (op W) x =
      tensorSection 𝒪 h𝒪 htensor (𝟙_ _) F (op W) (unitTensorSection 𝒪 h𝒪 hunit (op W) 1) x := by
    have hcatVal : (λ_ F).hom.val ≫ (λ_ F).inv.val = 𝟙 (𝟙_ _ ⊗ F).val :=
      congrArg (fun φ : (𝟙_ _ ⊗ F) ⟶ (𝟙_ _ ⊗ F) ↦ φ.val) (Iso.hom_inv_id (λ_ F))
    have happ := congrArg
      (fun φ : (𝟙_ _ ⊗ F).val ⟶ (𝟙_ _ ⊗ F).val ↦ φ.app (op W)
        (tensorSection 𝒪 h𝒪 htensor (𝟙_ _) F (op W)
          (unitTensorSection 𝒪 h𝒪 hunit (op W) 1) x)) hcatVal
    have hh := congrArg ((λ_ F).inv.val.app (op W)) (hleftUnitor F (op W) 1 x)
    simp only [PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
      PresheafOfModules.id_app, ConcreteCategory.id_apply, one_smul] at happ hh
    exact hh.symm.trans happ
  have hηpure : (η_ F G ▷ F).val.app (op W)
        (tensorSection 𝒪 h𝒪 htensor (𝟙_ _) F (op W) (unitTensorSection 𝒪 h𝒪 hunit (op W) 1) x) =
      ∑ j, tensorSection 𝒪 h𝒪 htensor (F ⊗ G) F (op W)
        (tensorSection 𝒪 h𝒪 htensor F G (op W)
          (F.val.map k.op (f j)) (G.val.map k.op (g j))) x := by
    calc
      _ = tensorSection 𝒪 h𝒪 htensor (F ⊗ G) F (op W)
            ((ExactPairing.coevaluation F G).val.app (op W)
              (unitTensorSection 𝒪 h𝒪 hunit (op W) 1)) x := by
          exact tensorSection_whiskerRight 𝒪 h𝒪 htensorMap (ExactPairing.coevaluation F G)
            (op W) (unitTensorSection 𝒪 h𝒪 hunit (op W) 1) x
      _ = tensorSection 𝒪 h𝒪 htensor (F ⊗ G) F (op W)
            (∑ j, tensorSection 𝒪 h𝒪 htensor F G (op W)
              (F.val.map k.op (f j)) (G.val.map k.op (g j))) x := by rw [hcoeW]
      _ = _ := tsSum (F ⊗ G) F (op W) _ x
  have hαsum : (α_ F G F).hom.val.app (op W)
        (∑ j, tensorSection 𝒪 h𝒪 htensor (F ⊗ G) F (op W)
          (tensorSection 𝒪 h𝒪 htensor F G (op W)
            (F.val.map k.op (f j)) (G.val.map k.op (g j))) x) =
      ∑ j, tensorSection 𝒪 h𝒪 htensor F (G ⊗ F) (op W) (F.val.map k.op (f j))
        (tensorSection 𝒪 h𝒪 htensor G F (op W) (G.val.map k.op (g j)) x) := by
    rw [app_sum_apply]
    exact Finset.sum_congr rfl fun j _ ↦
      hassociator F G F (op W) (F.val.map k.op (f j)) (G.val.map k.op (g j)) x
  have hεsum : (F ◁ ε_ F G).val.app (op W)
        (∑ j, tensorSection 𝒪 h𝒪 htensor F (G ⊗ F) (op W) (F.val.map k.op (f j))
          (tensorSection 𝒪 h𝒪 htensor G F (op W) (G.val.map k.op (g j)) x)) =
      ∑ j, tensorSection 𝒪 h𝒪 htensor F (𝟙_ _) (op W) (F.val.map k.op (f j))
        (unitTensorSection 𝒪 h𝒪 hunit (op W)
          ((eqToHom hunit).val.app (op W)
            ((ExactPairing.evaluation F G).val.app (op W)
              (tensorSection 𝒪 h𝒪 htensor G F (op W) (G.val.map k.op (g j)) x)))) := by
    rw [app_sum_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    refine (tensorSection_whiskerLeft 𝒪 h𝒪 htensorMap (ExactPairing.evaluation F G) (op W)
      (F.val.map k.op (f j)) _).trans ?_
    exact congrArg (tensorSection 𝒪 h𝒪 htensor F (𝟙_ _) (op W) (F.val.map k.op (f j)))
      (eqToHom_symm_val_app_apply hunit (op W) _).symm
  have hρsum : (ρ_ F).hom.val.app (op W)
        (∑ j, tensorSection 𝒪 h𝒪 htensor F (𝟙_ _) (op W) (F.val.map k.op (f j))
          (unitTensorSection 𝒪 h𝒪 hunit (op W)
            ((eqToHom hunit).val.app (op W)
              ((ExactPairing.evaluation F G).val.app (op W)
                (tensorSection 𝒪 h𝒪 htensor G F (op W) (G.val.map k.op (g j)) x))))) =
      ∑ j, @SMul.smul ((Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj (op W)) (F.val.obj (op W)) _
        ((eqToHom hunit).val.app (op W)
          ((ExactPairing.evaluation F G).val.app (op W)
            (tensorSection 𝒪 h𝒪 htensor G F (op W) (G.val.map k.op (g j)) x)))
        (F.val.map k.op (f j)) := by
    rw [app_sum_apply]
    exact Finset.sum_congr rfl fun j _ ↦
      hrightUnitor F (op W) (F.val.map k.op (f j)) _
  refine htriX.symm.trans ?_
  rw [hleft, hηpure, hαsum, hεsum]
  exact hρsum

section Retract

variable (F G : SheafOfModules.{w} (Tensor.ringSheaf
    ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))

/-- A local section of `F` over `V`, viewed as a global section of the restriction of `F` to
the slice site over `V`. -/
noncomputable def overGlobalSection (V : C) (a : F.val.obj (op V)) : (F.over V).sections :=
  PresheafOfModules.sectionsMk (fun X ↦ F.val.map X.unop.hom.op a) (by
    intro X Y φ
    change F.val.map φ.unop.left.op (F.val.map X.unop.hom.op a) = F.val.map Y.unop.hom.op a
    rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w])

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
@[simp]
lemma overSection_eval (V : C) (a : F.val.obj (op V)) (X : (Over V)ᵒᵖ) :
    (overGlobalSection 𝒪 h𝒪 F V a).eval X = F.val.map X.unop.hom.op a := rfl

section

variable [MonoidalCategory (SheafOfModules.{w} (Tensor.ringSheaf
    ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))]
  (hunit : 𝟙_ (SheafOfModules.{w} (Tensor.ringSheaf
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)) =
    SheafOfModules.unit (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))
  (htensor : ∀ A B : SheafOfModules.{w} (Tensor.ringSheaf
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩),
    A ⊗ B = ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj A).obj B)

/-- Contraction of a local section of `F` against a local section `b` of a left dual `G` of
`F`: the coordinate function of the duality pairing attached to `b`. -/
noncomputable def dualCoord [ExactPairing F G] (V : Cᵒᵖ) (b : G.val.obj V) :
    F.val.obj V ⟶ (SheafOfModules.unit (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)).val.obj V :=
  ModuleCat.ofHom
    { toFun := fun y ↦ (eqToHom hunit).val.app V
        ((ExactPairing.evaluation F G).val.app V (tensorSection 𝒪 h𝒪 htensor G F V b y))
      map_add' := fun y y' ↦ by
        rw [tensorSection_add_right, map_add, map_add]
        rfl
      map_smul' := fun c y ↦ by
        rw [tensorSection_smul_right, map_smul, map_smul]
        rfl }

lemma dualCoord_apply [ExactPairing F G] (V : Cᵒᵖ) (b : G.val.obj V) (y : F.val.obj V) :
    dualCoord 𝒪 h𝒪 F G hunit htensor V b y =
      (eqToHom hunit).val.app V ((ExactPairing.evaluation F G).val.app V
        (tensorSection 𝒪 h𝒪 htensor G F V b y)) := rfl

/-- The coordinate function of the duality pairing is compatible with restriction. -/
lemma dualCoord_naturality [ExactPairing F G] {V₁ V₂ : Cᵒᵖ} (k : V₁ ⟶ V₂)
    (b : G.val.obj V₁) (y : F.val.obj V₁) :
    (SheafOfModules.unit (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)).val.map k
        (dualCoord 𝒪 h𝒪 F G hunit htensor V₁ b y) =
      dualCoord 𝒪 h𝒪 F G hunit htensor V₂ (G.val.map k b) (F.val.map k y) := by
  refine ((PresheafOfModules.naturality_apply (eqToHom hunit).val k _).symm).trans ?_
  refine congrArg ((eqToHom hunit).val.app V₂) ?_
  refine ((PresheafOfModules.naturality_apply
    (ExactPairing.evaluation F G).val k _).symm).trans ?_
  exact congrArg ((ExactPairing.evaluation F G).val.app V₂)
    (tensorSection_restrict 𝒪 h𝒪 (htensor := htensor) G F k b y)

/-- The coordinate morphism on the slice site over `V` attached to a section of the left dual
over `V`. -/
noncomputable def dualCoordOver [ExactPairing F G] (V : C) (b : G.val.obj (op V)) :
    F.over V ⟶ SheafOfModules.unit ((Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).over V) where
  val :=
    { app := fun X ↦ dualCoord 𝒪 h𝒪 F G hunit htensor (op X.unop.left)
        (G.val.map X.unop.hom.op b)
      naturality := by
        intro X Y φ
        refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
        have hb : G.val.map φ.unop.left.op (G.val.map X.unop.hom.op b) =
            G.val.map Y.unop.hom.op b := by
          rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w]
        exact (congrArg (fun z ↦ dualCoord 𝒪 h𝒪 F G hunit htensor (op Y.unop.left) z
            (F.val.map φ.unop.left.op y)) hb.symm).trans
          (dualCoord_naturality 𝒪 h𝒪 F G hunit htensor φ.unop.left.op
            (G.val.map X.unop.hom.op b) y).symm }

@[simp]
lemma dualCoordOver_val_app_apply [ExactPairing F G] (V : C) (b : G.val.obj (op V))
    (X : (Over V)ᵒᵖ) (y : (F.over V).val.obj X) :
    (dualCoordOver 𝒪 h𝒪 F G hunit htensor V b).val.app X y =
      dualCoord 𝒪 h𝒪 F G hunit htensor (op X.unop.left)
        (G.val.map X.unop.hom.op b) y := rfl

variable [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A dual basis for the duality pairing over `V` exhibits the restriction of `F` to the slice
site over `V` as a direct summand of a finite free module. -/
theorem nonempty_retract_free_of_localDualBasis [ExactPairing F G] (V : C) {n : ℕ}
    (a : Fin n → F.val.obj (op V)) (b : Fin n → G.val.obj (op V))
    (hab : ∀ (W : C) (k : W ⟶ V) (y : F.val.obj (op W)),
      y = ∑ j, @SMul.smul ((Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj (op W))
        (F.val.obj (op W)) _
        (dualCoord 𝒪 h𝒪 F G hunit htensor (op W) (G.val.map k.op (b j)) y)
        (F.val.map k.op (a j))) :
    Nonempty (Retract (F.over V)
      (SheafOfModules.free (R := (Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).over V)
        (ULift.{w} (Fin n)))) := by
  classical
  refine ⟨{ i := ∑ j : ULift.{w} (Fin n),
              dualCoordOver 𝒪 h𝒪 F G hunit htensor V (b j.down) ≫ SheafOfModules.ιFree j
            r := (SheafOfModules.freeHomEquiv (F.over V)).symm
              fun j ↦ overGlobalSection 𝒪 h𝒪 F V (a j.down)
            retract := ?_ }⟩
  have hr : ∀ j : ULift.{w} (Fin n),
      SheafOfModules.ιFree j ≫ (SheafOfModules.freeHomEquiv (F.over V)).symm
          (fun j' ↦ overGlobalSection 𝒪 h𝒪 F V (a j'.down)) =
        (F.over V).unitHomEquiv.symm (overGlobalSection 𝒪 h𝒪 F V (a j.down)) := fun j ↦ by
    rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply,
      (SheafOfModules.freeHomEquiv (F.over V)).apply_symm_apply]
  rw [Preadditive.sum_comp]
  refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun X ↦
    ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_))
  rw [sum_val_app_apply]
  have hterm : ∀ j : ULift.{w} (Fin n),
      ((dualCoordOver 𝒪 h𝒪 F G hunit htensor V (b j.down) ≫ SheafOfModules.ιFree j) ≫
          (SheafOfModules.freeHomEquiv (F.over V)).symm
            fun j' ↦ overGlobalSection 𝒪 h𝒪 F V (a j'.down)).val.app X y =
        @SMul.smul ((Tensor.ringSheaf
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj (op X.unop.left))
          (F.val.obj (op X.unop.left)) _
          (dualCoord 𝒪 h𝒪 F G hunit htensor (op X.unop.left)
            (G.val.map X.unop.hom.op (b j.down)) y)
          (F.val.map X.unop.hom.op (a j.down)) := fun j ↦ by
    rw [Category.assoc, hr j]
    exact unitHomEquiv_symm_val_app_apply _ X _
  refine (Finset.sum_congr rfl fun j _ ↦ hterm j).trans ?_
  refine (Fintype.sum_equiv Equiv.ulift _
    (fun j : Fin n ↦ @SMul.smul ((Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj (op X.unop.left))
      (F.val.obj (op X.unop.left)) _
      (dualCoord 𝒪 h𝒪 F G hunit htensor (op X.unop.left)
        (G.val.map X.unop.hom.op (b j)) y)
      (F.val.map X.unop.hom.op (a j))) fun _ ↦ rfl).trans ?_
  exact (hab X.unop.left X.unop.hom y).symm

end

end Retract

/-- **Stacks Project, Tag 0FNZ (1).** Let `(C, 𝒪)` be a ringed site and let `F` be a sheaf of
`𝒪`-modules with a left dual `G` in the monoidal category of `𝒪`-modules. Then every object `U`
of the site has a covering on whose members `F` restricts to a direct summand of a finite free
module.

The monoidal structure is the one of Tag 01CA: its tensor product is the tensor product sheaf
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` and its unit is the structure sheaf. The
  three coherence hypotheses
record the action of the associator and of the two unitors on local pure tensors; they are part
of the data of the monoidal structure the source works in, and the associator is what the
source's proof uses when it reassociates `F ⊗ G ⊗ F`. -/
theorem exists_cover_retract_finiteFree_of_exactPairing
    [HasSheafify J AddCommGrpCat.{w}]
    [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (F G : SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))
    (M : MonoidalCategory (SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))) :
    letI := M
    ∀ (hunit : 𝟙_ (SheafOfModules.{w} (Tensor.ringSheaf
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)) =
          SheafOfModules.unit (Tensor.ringSheaf
              ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))
      (htensor : ∀ A B : SheafOfModules.{w} (Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩),
          A ⊗ B = ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj A).obj B)
      (_htensorMap : ∀ {A A' B B' : SheafOfModules.{w} (Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)}
          (f : A ⟶ A') (g : B ⟶ B'),
          eqToHom (htensor A B).symm ≫ (f ⊗ₘ g) ≫ eqToHom (htensor A' B') =
            (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)).map ((f, g) : (_, _) ⟶ (_, _)))
      (_hassociator : ∀ (A B D : SheafOfModules.{w} (Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))
          (V : Cᵒᵖ) (a : A.val.obj V) (b : B.val.obj V) (c : D.val.obj V),
          (α_ A B D).hom.val.app V
              (tensorSection 𝒪 h𝒪 htensor (A ⊗ B) D V
                (tensorSection 𝒪 h𝒪 htensor A B V a b) c) =
            tensorSection 𝒪 h𝒪 htensor A (B ⊗ D) V a
              (tensorSection 𝒪 h𝒪 htensor B D V b c))
      (_hleftUnitor : ∀ (A : SheafOfModules.{w} (Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)) (V : Cᵒᵖ)
          (r : (Tensor.ringSheaf
              ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V) (a : A.val.obj V),
          (λ_ A).hom.val.app V
              (tensorSection 𝒪 h𝒪 htensor _ A V (unitTensorSection 𝒪 h𝒪 hunit V r) a) = r • a)
      (_hrightUnitor : ∀ (A : SheafOfModules.{w} (Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)) (V : Cᵒᵖ)
          (a : A.val.obj V) (r : (Tensor.ringSheaf
              ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V),
          (ρ_ A).hom.val.app V
              (tensorSection 𝒪 h𝒪 htensor A _ V a (unitTensorSection 𝒪 h𝒪 hunit V r)) = r • a)
      (_p : ExactPairing F G) (U : C),
      ∃ S : Sieve U, S ∈ J U ∧
        ∀ (V : C) (i : V ⟶ U), S i →
          ∃ I : Type w, Finite I ∧
            Nonempty (Retract (F.over V)
              (SheafOfModules.free (R := (Tensor.ringSheaf
                  ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).over V) I)) := by
  intro hunit htensor htensorMap hassociator hleftUnitor hrightUnitor p U
  obtain ⟨S, hS, hcov⟩ := exists_cover_localDualBasis 𝒪 h𝒪 F G M hunit htensor htensorMap
    hassociator hleftUnitor hrightUnitor p U
  refine ⟨S, hS, fun V i hi ↦ ?_⟩
  obtain ⟨n, f, g, -, hdb⟩ := hcov V i hi
  exact ⟨ULift.{w} (Fin n), inferInstance,
    nonempty_retract_free_of_localDualBasis 𝒪 h𝒪 F G hunit htensor V f g hdb⟩

end Stacks.SheafOfModules

end
