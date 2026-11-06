module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.SchlessingerConditions.CofiberedLifts
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.Groupoid.BaseCategory
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Predeformation categories and prorepresentable functors

A predeformation category is a category cofibered in groupoids over the base
category whose fibre over the residue field `k` is trivial. This file defines predeformation
categories, the localization of a cofibered category at an object, and prorepresentability of a
functor on the base category.

## Main definitions

* `residueFieldObject` is the object `k` of `𝒞_Λ`.
* `residueFieldObject_residue` identifies its residue field with `k`.
* `residuePoint` is the point of a complete local algebra over the residue field.
* `IsPredeformationCategory` says that a chosen functor to `𝒞_Λ` is a
  predeformation category.
* `CategoryTheory.Over` is the category whose objects are arrows with target `x` and whose
  morphisms are commuting triangles over `x`.
* `objectsOverFunctor` is its structure functor to the
  base category.
* `IsPredeformationFunctor` is the singleton condition
  at the residue-field object.
* `restrictedCoyoneda` is the restriction to Artinian local algebras of
  the covariant functor represented by a complete local algebra.
* `IsProrepresentable` is the predicate that a functor is naturally
  isomorphic to one of these restricted representable functors.

## Main results

* `isPredeformationCategory_objectsOverFunctor` asserts that the
  localized category is a predeformation category.
* `isPredeformationCategory_iff` identifies this
  condition with the predeformation-category condition on the category of elements.

## Implementation notes

### Predeformation categories

The notion is a property of a specified projection functor, rather than a new bundled category,
so it applies directly to categories and functors already under consideration. We use the
universe lift of `k` to represent the residue-field object, leaving the carrier universe of
`𝒞_Λ` independent. The condition on the special fibre is expressed by an equivalence with
`Discrete PUnit`.
By `CategoryTheory.equiv_punit_iff_unique`, this says exactly that the fibre is nonempty and
has a unique morphism between every two objects. The existing `BasedFunctor` imposes no
condition beyond being a morphism over `𝒞_Λ`, as required by the source.

### The category of objects over a fixed object

The source's category `ℱ_x` is Mathlib's slice category `Over x`, which is registered
directly rather than given a duplicate alias.  The functor `p_x` is the composite of
`Over.forget x` with `p`.  Neither construction requires the cofibered-in-groupoids condition,
so both are stated for an arbitrary functor.

### Localizing a category cofibered in groupoids at an object

An object of the special fibre is represented by a term of `p.Fiber k`.
The localized category and its projection are the slice category `Over x`
and `objectsOverFunctor p x`. The conclusion includes both the cofibered-in-
groupoids property and equivalence of the special fibre with `Discrete PUnit`.

### Predeformation functors

The singleton condition is `Nonempty (Unique _)`, a proposition that clients may use
through the existing `Unique` API. The associated cofibered set is the category of
elements, with its canonical projection to the base category.

### Prorepresentable functors

The canonical inclusion of Artinian local algebras into complete local algebras
is `artinianToComplete`. The restriction is literally the composite
of this inclusion with Mathlib's covariant Yoneda functor; its elements are
compatible local algebra maps from the representing complete algebra.

## References

* [Stacks Project, Tag 06GS](https://stacks.math.columbia.edu/tag/06GS)
* [Stacks Project, Tag 06GT](https://stacks.math.columbia.edu/tag/06GT)
* [Stacks Project, Tag 06GU](https://stacks.math.columbia.edu/tag/06GU)
* [Stacks Project, Tag 06GX](https://stacks.math.columbia.edu/tag/06GX)
-/

@[expose] public section

namespace Deformation

/-! ### Predeformation categories -/

section
open CategoryTheory
universe u v w v₁ u₁

/-- The residue field `k`, regarded as an object of the category `𝒞_Λ` of Artinian local
`Λ`-algebras with residue field `k`. -/
@[implicit_reducible] noncomputable def residueFieldObject (Λ : Type u) (k : Type w) [CommRing Λ]
  [Field k] [Algebra Λ k] : ArtinianLocalAlgCat.{u, max v w, w} Λ k where
  carrier := ULift.{v} k
  residueEquiv := (Ideal.quotientEquivAlgOfEq Λ (IsLocalRing.maximalIdeal_eq_bot (R := ULift.{v}
    k))).trans ((AlgEquiv.quotientBot Λ (ULift.{v} k)).trans (ULift.algEquiv (R := Λ) (A := k)))

/-- The residue-field identification of the residue-field object sends the class of `a` to
the element `a` of `k` underneath it. -/
public theorem residueFieldObject_residue
    (Λ : Type u) (k : Type w) [CommRing Λ] [Field k] [Algebra Λ k]
    (a : ↑(residueFieldObject.{u, v, w} Λ k)) :
    (residueFieldObject.{u, v, w} Λ k).residueEquiv
        (IsLocalRing.residue _ a) = a.down := by
  let A := residueFieldObject.{u, v, w} Λ k
  let : Field (↑A) := ULift.field
  have hmax : IsLocalRing.maximalIdeal (↑A) = ⊥ := IsLocalRing.maximalIdeal_eq_bot
  show ULift.algEquiv (R := Λ) (A := k)
      ((AlgEquiv.quotientBot Λ (↑A))
        ((Ideal.quotientEquivAlgOfEq Λ hmax)
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (↑A)) a))) = a.down
  rw [Ideal.quotientEquivAlgOfEq_mk, AlgEquiv.quotientBot_mk]
  rfl

/-- A functor to `𝒞_Λ` presents a predeformation category when it is cofibered in
groupoids and its fibre over the residue field `k` is equivalent to the category with one
object and one morphism. -/
@[stacks 06GS "objects"]
structure IsPredeformationCategory {Λ : Type u} {k : Type w} [CommRing Λ]
  [Field k] [Algebra Λ k] {F : Type u₁} [Category.{v₁} F] (p : F ⥤ ArtinianLocalAlgCat.{u, max v w,
    w} Λ k) : Prop where
  /-- The projection is cofibered in groupoids. -/
  cofibered : IsCofiberedInGroupoids p
  /-- The fibre over `k` is equivalent to the category with one object and one morphism. -/
  specialFiber : Nonempty (p.Fiber (residueFieldObject Λ k) ≌ Discrete PUnit.{u₁ + 1})

add_to_stacks 06GS "morphisms" BasedFunctor

end

/-! ### The canonical point over the residue field -/

section
open CategoryTheory
universe u v w

/-- Each component of a natural isomorphism of set-valued functors is injective. -/
public theorem natIso_app_injective {C : Type u} [Category.{v} C] {F G : C ⥤ Type w}
    (e : F ≅ G) (A : C) : Function.Injective (e.hom.app A) :=
  (e.app A).toEquiv.injective

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The residue-field object, viewed as a complete local algebra, has residue map the inverse
universe lift. -/
theorem completeResidueFieldObject_residue_symm (y : k) :
    (artinianToComplete.obj (residueFieldObject.{u, v, w} Λ k)).residueEquiv
      (IsLocalRing.residue (artinianToComplete.obj
        (residueFieldObject.{u, v, w} Λ k)).carrier
        ((ULift.algEquiv.{u, w, v} (R := Λ) (A := k)).symm y)) = y :=
  rfl

/-- The residue map of the residue-field object, viewed as a complete local algebra, is the
universe lift. -/
theorem completeResidueFieldObject_residue
    (z : (artinianToComplete.obj (residueFieldObject.{u, v, w} Λ k)).carrier) :
    (artinianToComplete.obj (residueFieldObject.{u, v, w} Λ k)).residueEquiv
      (IsLocalRing.residue (artinianToComplete.obj
        (residueFieldObject.{u, v, w} Λ k)).carrier z) =
      ULift.algEquiv.{u, w, v} (R := Λ) (A := k) z := by
  cases z
  rfl

/-- The canonical map from a complete local algebra to the residue-field object. -/
noncomputable def residuePoint (R : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    R ⟶ artinianToComplete.obj (residueFieldObject.{u, v, w} Λ k) := by
  let f : R.carrier →ₐ[Λ] (residueFieldObject.{u, v, w} Λ k).carrier :=
    (ULift.algEquiv.{u, w, v} (R := Λ) (A := k)).symm.toAlgHom.comp
      (R.residueEquiv.toAlgHom.comp
        (Ideal.Quotient.mkₐ Λ (IsLocalRing.maximalIdeal R.carrier)))
  let : IsLocalHom
      (Ideal.Quotient.mkₐ Λ (IsLocalRing.maximalIdeal R.carrier)).toRingHom := by
    change IsLocalHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R.carrier))
    exact IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  refine { hom := f, isLocal := ?_, residue_comm := ?_ }
  · constructor
    intro x hx
    have hfx : f x ≠ 0 := hx.ne_zero
    have hr : IsLocalRing.residue R.carrier x ≠ 0 := by
      intro hz
      have hz' : R.residueEquiv (IsLocalRing.residue R.carrier x) = 0 := by
        rw [hz]
        simp
      have hmid : (R.residueEquiv.toAlgHom.comp
          (Ideal.Quotient.mkₐ Λ (IsLocalRing.maximalIdeal R.carrier))) x = 0 := hz'
      apply hfx
      change (ULift.algEquiv.{u, w, v} (R := Λ) (A := k)).symm
        ((R.residueEquiv.toAlgHom.comp
          (Ideal.Quotient.mkₐ Λ (IsLocalRing.maximalIdeal R.carrier))) x) = 0
      rw [hmid]
      simp
    exact (IsLocalRing.residue_ne_zero_iff_isUnit x).mp hr
  · intro x
    change (artinianToComplete.obj (residueFieldObject.{u, v, w} Λ k)).residueEquiv
      (IsLocalRing.residue (artinianToComplete.obj (residueFieldObject.{u, v, w} Λ k))
        ((ULift.algEquiv.{u, w, v} (R := Λ) (A := k)).symm
          (R.residueEquiv (IsLocalRing.residue R.carrier x)))) = _
    exact completeResidueFieldObject_residue_symm
      (R.residueEquiv (IsLocalRing.residue R.carrier x))

end

/-! ### The category of objects over a fixed object -/

section
open CategoryTheory
universe v₁ v₂ u₁ u₂

add_to_stacks 06GU "category_of_objects_over_x" CategoryTheory.Over
add_to_sga "1 V 6.13" CategoryTheory.Over
add_to_sga "1 VIII 5.2" "fiber over S" CategoryTheory.Over
add_to_sga "3 I 1.3" CategoryTheory.Over
add_to_sga "3 VIIA 4.0" "more general" CategoryTheory.Over
add_to_sga "3 VIII 1.0.3" CategoryTheory.Over
add_to_sga "4 III 5.1" "special case" CategoryTheory.Over
add_to_sga "4 IV 5.1" CategoryTheory.Over
add_to_sga "4 IV 7.1.8" "more general" CategoryTheory.Over
add_to_sga "4 VI 4.1" "partial" CategoryTheory.Over
add_to_sga "4½ Arcata 1.6.4" "partial" CategoryTheory.Over
add_to_sga "7 VI 3.1(a)" "partial" CategoryTheory.Over
add_to_ega "I 10.4.7" CategoryTheory.Over
add_to_ega "I 2.5.1" CategoryTheory.Over
add_to_ega "I 3.3.1" CategoryTheory.Over
add_to_ega "IV 14.5.8" CategoryTheory.Over

variable {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]

/-- The structure functor on the category of arrows in `F` with target `x`, obtained by
forgetting the arrow to `x` and then applying `p`. -/
@[stacks 06GU "category_of_objects_over_x", implicit_reducible]
def objectsOverFunctor (p : F ⥤ C)
  (x : F) : Over x ⥤ C := Over.forget x ⋙ p

/-- The structure functor `objectsOverFunctor p x` sends an object `y ⟶ x` to `p.obj y.left`. -/
@[simp] theorem objectsOverFunctor_obj (p : F ⥤ C) (x : F) (y : Over x) : (objectsOverFunctor p
  x).obj y = p.obj y.left := rfl

/-- The structure functor `objectsOverFunctor p x` sends a morphism `f` over `x` to
`p.map f.left`. -/
@[simp] theorem objectsOverFunctor_map (p : F ⥤ C) (x : F) {y z : Over x} (f : y ⟶ z) :
  (objectsOverFunctor p x).map f = p.map f.left := rfl

end

/-! ### Localizing a category cofibered in groupoids at an object -/

section
open CategoryTheory
universe u v w v₁ u₁ u₂ v₂



private theorem cofibered_left_cancel
    {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]
    {p : F ⥤ C} (hp : p.op.IsFiberedInGroupoids)
    {a b c : F} (f : a ⟶ b) {g h : b ⟶ c}
    (hmap : p.map g = p.map h) (hcomp : f ≫ g = f ≫ h) : g = h := by
  obtain ⟨χ, hχ, huniq⟩ := existsUnique_factor_of_isHomLift hp f (f ≫ g) (p.map g) (by simp)
  have hg : g = χ := huniq g ⟨rfl, by simp⟩
  have hh : h = χ := huniq h ⟨hmap.symm, hcomp.symm⟩
  exact hg.trans hh.symm

/-- In a category cofibered in groupoids, every morphism `f : A ⟶ B` of the base lifts out of
a given object `a` over `A`: there is an object over `B` and a morphism `a ⟶ b` lying over `f`.
This is the pushforward of `a` along `f`, read off from the lifting property of `p.op`. -/
theorem cofibered_lift
    {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]
    {p : F ⥤ C} (hp : p.op.IsFiberedInGroupoids)
    {a : F} {A B : C} (ha : p.obj a = A) (f : A ⟶ B) :
    ∃ (b : F) (φ : a ⟶ b), p.obj b = B ∧ p.IsHomLift f φ := by
  subst A
  obtain ⟨bop, φop, hφ⟩ := hp.exists_lift f.op (Opposite.op a) rfl
  let b := Opposite.unop bop
  let φ : a ⟶ b := φop.unop
  have hb : p.obj b = B := by
    have h := IsHomLift.domain_eq (p := p.op) f.op φop
    exact congrArg Opposite.unop h
  exact ⟨b, φ, hb, isHomLift_unop p f.op φ.op (inst := hφ)⟩

private noncomputable def residueMorphism
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) :
    A ⟶ residueFieldObject.{u, v, w} Λ k := by
  let resAlg : A →ₐ[Λ] IsLocalRing.ResidueField A :=
    IsScalarTower.toAlgHom Λ A (IsLocalRing.ResidueField A)
  let e : A →ₐ[Λ] ULift.{v} k :=
    (ULift.algEquiv (R := Λ) (A := k)).symm.toAlgHom.comp
      (A.residueEquiv.toAlgHom.comp resAlg)
  exact
    { hom := e
      isLocal := by
        refine ⟨fun a ha => ?_⟩
        have hr : IsUnit (IsLocalRing.residue A a) :=
          (MulEquiv.isUnit_map A.residueEquiv).mp
            ((MulEquiv.isUnit_map (ULift.algEquiv (R := Λ) (A := k)).symm).mp ha)
        exact (inferInstance : IsLocalHom (IsLocalRing.residue A)).map_nonunit a hr
      residue_comm := by
        intro a
        have hK : IsLocalRing.maximalIdeal
            ↑(residueFieldObject.{u, v, w} Λ k) = ⊥ := by
          change IsLocalRing.maximalIdeal (ULift.{v} k) = ⊥
          exact IsLocalRing.maximalIdeal_eq_bot
        change
          ((Ideal.quotientEquivAlgOfEq Λ hK).trans
              ((AlgEquiv.quotientBot Λ (ULift.{v} k)).trans
                (ULift.algEquiv (R := Λ) (A := k))))
              (IsLocalRing.residue (residueFieldObject.{u, v, w} Λ k) (e a)) =
            A.residueEquiv (IsLocalRing.residue A a)
        rw [IsLocalRing.residue_def]
        simp only [AlgEquiv.trans_apply]
        rw [Ideal.quotientEquivAlgOfEq_mk, AlgEquiv.quotientBot_mk]
        simp [e, resAlg, AlgHom.comp_apply,
          IsLocalRing.ResidueField.algebraMap_eq] }

private lemma residueMorphism_eq
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (f : A ⟶ residueFieldObject.{u, v, w} Λ k) :
    f = residueMorphism A := by
  apply ArtinianLocalAlgCat.hom_ext
  ext a
  have hf := f.residue_comm a
  have hq := (residueMorphism A).residue_comm a
  have hres : IsLocalRing.residue (residueFieldObject.{u, v, w} Λ k)
      (f.hom a) = IsLocalRing.residue (residueFieldObject.{u, v, w} Λ k)
        ((residueMorphism A).hom a) :=
    (residueFieldObject.{u, v, w} Λ k).residueEquiv.injective (hf.trans hq.symm)
  have hzero : IsLocalRing.residue (residueFieldObject.{u, v, w} Λ k)
      (f.hom a - (residueMorphism A).hom a) = 0 := by
    rw [map_sub, hres, sub_self]
  have hin := (IsLocalRing.residue_eq_zero_iff _).mp hzero
  have hmax : IsLocalRing.maximalIdeal
      ↑(residueFieldObject.{u, v, w} Λ k) = ⊥ := by
    show IsLocalRing.maximalIdeal (ULift.{v} k) = ⊥
    exact IsLocalRing.maximalIdeal_eq_bot
  have hz : f.hom a - (residueMorphism A).hom a = 0 := by
    rw [hmax] at hin
    simpa using hin
  exact sub_eq_zero.mp hz

/-- Any two morphisms into the residue-field object agree. -/
private lemma residueMorphism_unique
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f g : A ⟶ residueFieldObject.{u, v, w} Λ k) : f = g :=
  (residueMorphism_eq A f).trans (residueMorphism_eq A g).symm

private lemma objectsOver_arrow_map
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (x : p.Fiber (residueFieldObject.{u, v, w} Λ k))
    (y : Over x.1)
    (hy : p.obj y.left = residueFieldObject.{u, v, w} Λ k) :
    p.map y.hom = eqToHom hy ≫ eqToHom x.property.symm := by
  have hR : eqToHom hy.symm ≫ p.map y.hom ≫ eqToHom x.property = 𝟙 _ :=
    residueMorphism_unique _ _
  apply (cancel_epi (eqToHom hy.symm)).mp
  apply (cancel_mono (eqToHom x.property)).mp
  simpa [Category.assoc] using hR

private lemma objectsOver_arrow_isIso
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : p.op.IsFiberedInGroupoids)
    (x : p.Fiber (residueFieldObject.{u, v, w} Λ k))
    (y : Over x.1)
    (hy : p.obj y.left = residueFieldObject.{u, v, w} Λ k) : IsIso y.hom := by
  have hmap := objectsOver_arrow_map p x y hy
  let : IsIso (p.map y.hom) := hmap ▸ inferInstance
  let : IsIso (p.op.map y.hom.op) := by simpa using isIso_op (p.map y.hom)
  let : p.op.IsStronglyCartesian (p.op.map y.hom.op) y.hom.op :=
    hp.isStronglyCartesian _
  have hIso : IsIso y.hom.op :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso (p := p.op)
      (f := p.op.map y.hom.op) y.hom.op
  exact isIso_of_op y.hom

/-- Localizing a category cofibered in groupoids at an object of its special
fibre gives a predeformation category. -/
@[stacks 06GU]
public theorem isPredeformationCategory_objectsOverFunctor
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (x : p.Fiber (residueFieldObject.{u, v, w} Λ k)) :
    IsPredeformationCategory
      (objectsOverFunctor p x.1) := by
  classical
  let q := objectsOverFunctor p x.1
  refine ⟨?_, ?_⟩
  · show q.op.IsFiberedInGroupoids
    refine ⟨?_, ?_⟩
    · intro V U f a ha
      let a0 : Over x.1 := Opposite.unop a
      have ha' : p.obj a0.left = Opposite.unop U := by
        simpa [q] using congrArg Opposite.unop ha
      obtain ⟨b, φ, hb, hφ⟩ := cofibered_lift hp ha' f.unop
      have htriR : p.map φ ≫ residueMorphism (p.obj b) =
          p.map a0.hom ≫ eqToHom x.property := residueMorphism_unique _ _
      have htri : p.map φ ≫ (residueMorphism (p.obj b) ≫ eqToHom x.property.symm) =
          p.map a0.hom := by
        calc
          p.map φ ≫ (residueMorphism (p.obj b) ≫ eqToHom x.property.symm) =
              (p.map φ ≫ residueMorphism (p.obj b)) ≫ eqToHom x.property.symm := by
                simp [Category.assoc]
          _ = (p.map a0.hom ≫ eqToHom x.property) ≫ eqToHom x.property.symm := by rw [htriR]
          _ = p.map a0.hom := by simp
      obtain ⟨β, hβ, _⟩ :=
        existsUnique_factor_of_isHomLift hp φ a0.hom
          (residueMorphism (p.obj b) ≫ eqToHom x.property.symm) htri
      let b0 : Over x.1 := Over.mk β
      let g : a0 ⟶ b0 := Over.homMk φ hβ.2
      have hg : q.IsHomLift f.unop g := by
        let := hφ
        apply IsHomLift.of_fac' q f.unop g ha' hb
        simpa [q, g] using IsHomLift.fac' p f.unop φ
      have hgop : q.op.IsHomLift f g.op := by
        simpa using isHomLift_op q f.unop g (inst := hg)
      refine ⟨Opposite.op b0, g.op, ?_⟩
      simpa using hgop
    · intro a b c φ ψ f h
      let a0 : Over x.1 := Opposite.unop a
      let b0 : Over x.1 := Opposite.unop b
      let c0 : Over x.1 := Opposite.unop c
      have hbase : q.map φ.unop ≫ f.unop = q.map ψ.unop := by
        simpa using congrArg Quiver.Hom.unop h
      have hpbase : p.map φ.unop.left ≫ f.unop = p.map ψ.unop.left := by
        simpa [q] using hbase
      obtain ⟨χ, hχ, hχuniq⟩ :=
        existsUnique_factor_of_isHomLift hp φ.unop.left ψ.unop.left f.unop hpbase
      have hmapR : p.map (χ ≫ c0.hom) ≫ eqToHom x.property =
          p.map b0.hom ≫ eqToHom x.property := residueMorphism_unique _ _
      have hmap : p.map (χ ≫ c0.hom) = p.map b0.hom :=
        (cancel_mono (eqToHom x.property)).mp hmapR
      have hcomp : φ.unop.left ≫ (χ ≫ c0.hom) = φ.unop.left ≫ b0.hom := by
        calc
          φ.unop.left ≫ (χ ≫ c0.hom) = (φ.unop.left ≫ χ) ≫ c0.hom := by
            simp [Category.assoc]
          _ = ψ.unop.left ≫ c0.hom := by rw [hχ.2]
          _ = a0.hom := Over.w ψ.unop
          _ = φ.unop.left ≫ b0.hom := (Over.w φ.unop).symm
      have hOver : χ ≫ c0.hom = b0.hom := cofibered_left_cancel hp _ hmap hcomp
      let g : b0 ⟶ c0 := Over.homMk χ hOver
      have hgmap : q.map g = f.unop := by
        simpa [q, g, b0, c0] using hχ.1
      have hgf : φ.unop ≫ g = ψ.unop := Over.OverMorphism.ext hχ.2
      refine ⟨g.op, ?_, ?_⟩
      · constructor
        · simpa using congrArg Quiver.Hom.op hgmap
        · exact congrArg Quiver.Hom.op hgf
      · intro g' ⟨hg'map, hg'comp⟩
        have hmap' : p.map g'.unop.left = f.unop := by
          have hqmap' := congrArg Quiver.Hom.unop hg'map
          simpa [q, b0, c0] using hqmap'
        have hcomp' : φ.unop.left ≫ g'.unop.left = ψ.unop.left := by
          have hqcomp' : φ.unop ≫ g'.unop = ψ.unop := by
            simpa using congrArg Quiver.Hom.unop hg'comp
          simpa using congrArg (fun t : a0 ⟶ c0 => t.left) hqcomp'
        have hleft := hχuniq g'.unop.left ⟨hmap', hcomp'⟩
        have heq : g'.unop = g := Over.OverMorphism.ext hleft
        simpa using congrArg Quiver.Hom.op heq
  · apply (CategoryTheory.equiv_punit_iff_unique (q.Fiber
      (residueFieldObject.{u, v, w} Λ k))).2
    refine ⟨?_, ?_⟩
    · refine ⟨⟨Over.mk (𝟙 x.1), ?_⟩⟩
      simpa [q] using x.property
    · intro y z
      let y0 : Over x.1 := y.1
      let z0 : Over x.1 := z.1
      have hy : p.obj y0.left = residueFieldObject.{u, v, w} Λ k := by
        simpa [q, y0] using y.property
      have hz : p.obj z0.left = residueFieldObject.{u, v, w} Λ k := by
        simpa [q, z0] using z.property
      have hyMap := objectsOver_arrow_map p x y0 hy
      have hzMap := objectsOver_arrow_map p x z0 hz
      let : IsIso z0.hom := objectsOver_arrow_isIso p hp x z0 hz
      let α : y0.left ⟶ z0.left := y0.hom ≫ inv z0.hom
      have hα : p.map α = eqToHom hy ≫ eqToHom hz.symm := by
        simp [α, hyMap, hzMap]
      have htriangle : α ≫ z0.hom = y0.hom := by
        simp [α]
      let m : y0 ⟶ z0 := Over.homMk α htriangle
      have hm : q.IsHomLift
          (𝟙 (residueFieldObject.{u, v, w} Λ k)) m := by
        have hqm : q.map m = eqToHom y.property ≫
            𝟙 (residueFieldObject.{u, v, w} Λ k) ≫ eqToHom z.property.symm := by
          simpa [q, m] using hα
        exact IsHomLift.of_fac' q _ m y.property z.property hqm
      let mF : y ⟶ z := ⟨m, hm⟩
      refine ⟨{ default := mF, uniq := ?_ }⟩
      intro f
      apply Functor.Fiber.hom_ext
      apply Over.OverMorphism.ext
      show f.1.left = mF.1.left
      exact (cancel_mono z0.hom).mp (by rw [Over.w f.1, Over.w mF.1])

end

/-! ### Predeformation functors -/

section
open CategoryTheory
universe u v w t

/-- The projection from the category of elements of a functor `F : C ⥤ Type t` to `C` is
cofibered in groupoids. -/
public theorem categoryOfElements_π_isCofibered
    {C : Type u} [Category.{v} C] (F : C ⥤ Type t) :
    IsCofiberedInGroupoids (Functor.Elements.π F) := by
  show Functor.IsFiberedInGroupoids (Functor.Elements.π F).op
  constructor
  · intro V U f x hx
    rcases V with ⟨V⟩
    rcases U with ⟨U⟩
    rcases x with ⟨x⟩
    change Opposite.op ((Functor.Elements.π F).obj x) = Opposite.op U at hx
    cases hx
    let y := F.elementsMk V (F.map f.unop x.2)
    let g : x ⟶ y := Functor.Elements.homMk (x := x) (y := y) f.unop rfl
    refine ⟨Opposite.op y, g.op, ?_⟩
    have hmap : (Functor.Elements.π F).op.map g.op = f := by
      apply Quiver.Hom.opEquiv.injective; simp [g, Functor.Elements.π]
    rw [← hmap]
    exact inferInstance
  · intro x y z φ ψ f hf
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    rcases z with ⟨z⟩
    have hbase : φ.unop.hom ≫ f.unop = ψ.unop.hom := by
      simpa using congrArg Quiver.Hom.unop hf
    let g : y ⟶ z := Functor.Elements.homMk (x := y) (y := z) f.unop (by
      calc
        F.map f.unop y.2 = F.map f.unop (F.map φ.unop.hom x.2) := by
          rw [Functor.Elements.Hom.map_val]
        _ = F.map (φ.unop.hom ≫ f.unop) x.2 := by rw [Functor.map_comp_apply]
        _ = F.map ψ.unop.hom x.2 := by rw [hbase]
        _ = z.2 := Functor.Elements.Hom.map_val ψ.unop)
    refine ⟨g.op, ⟨?_, ?_⟩, ?_⟩
    · have hmap : (Functor.Elements.π F).op.map g.op = f := by
        apply Quiver.Hom.opEquiv.injective; simp [g, Functor.Elements.π]
      exact hmap
    · apply Quiver.Hom.opEquiv.symm.injective
      apply Functor.Elements.hom_ext
      exact hbase
    · intro χ hχ
      apply Quiver.Hom.opEquiv.symm.injective
      apply Functor.Elements.hom_ext
      have hh := congrArg Quiver.Hom.unop hχ.1
      change χ.unop.hom = f.unop at hh
      show χ.unop.hom = f.unop
      exact hh

private theorem categoryOfElements_fiber_hom_subsingleton
    {C : Type u} [Category.{v} C] (F : C ⥤ Type t)
    (S : C) {X Y : (Functor.Elements.π F).Fiber S} (f g : X ⟶ Y) : f = g := by
  apply Functor.Fiber.hom_ext; apply Functor.map_injective (Functor.Elements.π F)
  let : (Functor.Elements.π F).IsHomLift (𝟙 S)
      (Functor.Fiber.fiberInclusion.map f) := f.2
  let : (Functor.Elements.π F).IsHomLift (𝟙 S)
      (Functor.Fiber.fiberInclusion.map g) := g.2
  have hf := IsHomLift.fac' (Functor.Elements.π F) (𝟙 S) (Functor.Fiber.fiberInclusion.map f)
  have hg := IsHomLift.fac' (Functor.Elements.π F) (𝟙 S) (Functor.Fiber.fiberInclusion.map g)
  rw [hf, hg]

private def categoryOfElements_fiberIso
    {C : Type u} [Category.{v} C] (F : C ⥤ Type t)
    (S : C) (X : (Functor.Elements.π F).Fiber S) (a : F.obj S)
    (ha : F.map (eqToHom X.2) X.1.2 = a) :
    X ≅ (⟨F.elementsMk S a, rfl⟩ : (Functor.Elements.π F).Fiber S) := by
  let Y := F.elementsMk S a
  let e : X.1 ≅ Y := Functor.Elements.isoMk (x := X.1) (y := Y) (eqToIso X.2) ha
  have hhom : (Functor.Elements.π F).IsHomLift (𝟙 S) e.hom := by
    apply IsHomLift.of_fac' (Functor.Elements.π F) (𝟙 S) e.hom X.2 rfl
    simp [e, Functor.Elements.isoMk, Functor.Elements.homMk, Functor.Elements.π]
  have hinv : (Functor.Elements.π F).IsHomLift (𝟙 S) e.inv := by
    apply IsHomLift.of_fac' (Functor.Elements.π F) (𝟙 S) e.inv rfl X.2
    simp [e, Functor.Elements.isoMk, Functor.Elements.homMk, Functor.Elements.π]
  let Z : (Functor.Elements.π F).Fiber S := ⟨Y, rfl⟩
  let hom : X ⟶ Z := ⟨e.hom, hhom⟩
  let inv : Z ⟶ X := ⟨e.inv, hinv⟩
  refine ⟨hom, inv, ?_, ?_⟩
  · exact Functor.Fiber.hom_ext e.hom_inv_id
  · exact Functor.Fiber.hom_ext e.inv_hom_id

/-- A set-valued functor on `𝒞_Λ` is a predeformation functor when its value at
the residue field `k` is a one-element set. -/
@[stacks 06GT "predeformation_functor"]
public abbrev IsPredeformationFunctor
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (F : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type t) : Prop :=
  Nonempty (Unique (F.obj (residueFieldObject Λ k)))

/-- A functor is a predeformation functor exactly when its associated cofibered
set, the category of elements, is a predeformation category. -/
@[stacks 06GT "predeformation_functor"]
public theorem isPredeformationCategory_iff
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (F : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type t) :
    IsPredeformationCategory (Functor.Elements.π F) ↔
      IsPredeformationFunctor F := by
  let p := Functor.Elements.π F
  constructor
  · intro h
    rcases h.specialFiber with ⟨e⟩
    let : Subsingleton (Discrete PUnit) := inferInstance
    have hs : Subsingleton (F.obj (residueFieldObject Λ k)) := by
      constructor
      intro a b
      let X : p.Fiber (residueFieldObject Λ k) :=
        ⟨F.elementsMk _ a, rfl⟩
      let Y : p.Fiber (residueFieldObject Λ k) :=
        ⟨F.elementsMk _ b, rfl⟩
      have hab : e.functor.obj X = e.functor.obj Y := Subsingleton.elim _ _
      let f : e.functor.obj X ⟶ e.functor.obj Y := eqToHom hab
      let g : X ⟶ Y := e.functor.preimage f
      have hbase' : p.map (Functor.Fiber.fiberInclusion.map g) =
          𝟙 (residueFieldObject Λ k) := by
        let : p.IsHomLift (𝟙 (residueFieldObject Λ k))
            (Functor.Fiber.fiberInclusion.map g) := g.2
        have hfac := IsHomLift.fac' p (𝟙 (residueFieldObject Λ k))
          (Functor.Fiber.fiberInclusion.map g)
        have hX : X.2 = rfl := Subsingleton.elim _ _
        have hY : Y.2 = rfl := Subsingleton.elim _ _
        change p.map (Functor.Fiber.fiberInclusion.map g) =
          eqToHom X.2 ≫ 𝟙 (residueFieldObject Λ k) ≫ eqToHom Y.2.symm at hfac
        rw [hX, hY] at hfac
        simpa [X, Y, p, Functor.Elements.π] using hfac
      have hval := Functor.Elements.Hom.map_val (Functor.Fiber.fiberInclusion.map g)
      change F.map (p.map (Functor.Fiber.fiberInclusion.map g)) a = b at hval
      rw [hbase'] at hval
      exact (Functor.map_id_apply F (residueFieldObject Λ k) a).symm.trans hval
    have hn : Nonempty (F.obj (residueFieldObject Λ k)) := by
      let X := e.inverse.obj (Discrete.mk PUnit.unit)
      exact ⟨F.map (eqToHom X.2) X.1.2⟩
    let : Subsingleton (F.obj (residueFieldObject Λ k)) := hs
    exact nonempty_unique _
  · intro h
    let : Unique (F.obj (residueFieldObject Λ k)) := h.some
    let a : F.obj (residueFieldObject Λ k) := default
    let S := residueFieldObject Λ k
    let y : p.Fiber S := ⟨F.elementsMk S a, rfl⟩
    let forward : p.Fiber S ⥤ Discrete PUnit :=
      (Functor.const (p.Fiber S)).obj (Discrete.mk PUnit.unit)
    let backward : Discrete PUnit ⥤ p.Fiber S := (Functor.const _).obj y
    let unitIso : 𝟭 (p.Fiber S) ≅ forward ⋙ backward :=
      NatIso.ofComponents (fun X =>
        categoryOfElements_fiberIso F S X a (Subsingleton.elim _ _)) (by
        intro X Y f
        apply categoryOfElements_fiber_hom_subsingleton F S)
    let counitIso : backward ⋙ forward ≅ 𝟭 (Discrete PUnit) :=
      Discrete.natIso (fun X => eqToIso (congrArg Discrete.mk (Subsingleton.elim _ _)))
    exact ⟨categoryOfElements_π_isCofibered F,
      ⟨CategoryTheory.Equivalence.mk forward backward unitIso counitIso⟩⟩

end

/-! ### Prorepresentable functors -/

section
open CategoryTheory
universe u v w x


/-- The restriction to Artinian local algebras of the covariant representable
functor associated to a complete local algebra `R`. -/
abbrev restrictedCoyoneda {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v :=
  artinianToComplete ⋙ coyoneda.obj (Opposite.op R)

/-- A restricted covariant representable functor evaluates to the hom-set
from its representing complete algebra. -/
@[simp]
theorem restrictedCoyoneda_obj {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    (restrictedCoyoneda R).obj A = (R ⟶ artinianToComplete.obj A) :=
  rfl

/-- The underlying algebra map of the image under the restricted covariant
Yoneda functor is given by postcomposition. -/
@[simp]
theorem restrictedCoyoneda_map_hom {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ B)
    (g : R ⟶ artinianToComplete.obj A) :
    ((restrictedCoyoneda R).map f g).hom = f.hom.comp g.hom :=
  rfl

/-- A functor on Artinian local `Λ`-algebras is prorepresentable if it is
naturally isomorphic to the restriction of the covariant representable functor
of some Noetherian complete local `Λ`-algebra. -/
@[stacks 06GX]
abbrev IsProrepresentable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v) : Prop :=
  ∃ R : CompleteLocalAlgCat.{u, v, w} Λ k, Nonempty (F ≅ restrictedCoyoneda R)

/-- Prorepresentability of a functor whose values lie in a universe `x` unrelated to the
morphism universe `v` of `ArtinianLocalAlgCat`, compared after raising both sides to
`Type (max v x)`.

`IsProrepresentable` cannot be stated for such a functor: a representable functor takes its
values in the hom-universe, so `F ≅ restrictedCoyoneda R` is a universe error unless `x = v`.
This is the form a statement with an independent value universe has to use, and
`isProrepresentableULift_iff` says it is the same notion at `x = v`. -/
abbrev IsProrepresentableULift {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type x) : Prop :=
  ∃ R : CompleteLocalAlgCat.{u, v, w} Λ k,
    Nonempty (F ⋙ uliftFunctor.{v, x} ≅ restrictedCoyoneda R ⋙ uliftFunctor.{x, v})

/-- At `x = v` the universe-raised notion of prorepresentability is the original one, so
nothing is gained or lost by stating a result about `ArtinianLocalAlgCat.{u, v, w}`-functors
valued in an independent universe and then specializing. -/
theorem isProrepresentableULift_iff {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v) :
    IsProrepresentableULift.{u, v, w, v} F ↔ IsProrepresentable F := by
  constructor
  · rintro ⟨R, ⟨e⟩⟩
    exact ⟨R, ⟨Functor.isoWhiskerLeft F uliftFunctorTrivial.symm ≪≫ e ≪≫
      Functor.isoWhiskerLeft (restrictedCoyoneda R) uliftFunctorTrivial⟩⟩
  · rintro ⟨R, ⟨e⟩⟩
    exact ⟨R, ⟨Functor.isoWhiskerRight e uliftFunctor.{v, v}⟩⟩

end

end Deformation
