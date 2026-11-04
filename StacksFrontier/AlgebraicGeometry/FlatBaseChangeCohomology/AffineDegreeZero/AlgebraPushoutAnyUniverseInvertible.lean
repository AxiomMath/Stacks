module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.AlgebraPushoutAnyUniverse
public import StacksFrontier.CategoryTheory.Sites.Point.CommRingPushout
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# The comparison with the extension of scalars is invertible

Let `(C, J)` be a site, `φ : R ⟶ R'` a morphism of sheaves of commutative rings on it and `B`
a sheaf of commutative `R`-algebras. The canonical comparison

`R' ⊗_R (module underlying B) ⟶ module underlying (B ⊗_R R')`

of `Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.extendScalarsComparison` is invertible, for
an arbitrary site and with no finiteness, flatness or affineness hypothesis. This identifies the
module underlying `B ⊗_R R'` with the extension of scalars of the module underlying `B`.

## Main definitions

* `Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.presheafPushout`: the pushout of the span
  `B ⟵ R ⟶ R'` formed in *presheaves* of commutative rings, where it is computed objectwise.
* `Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.presheafPushoutCompare`: the canonical
  morphism from that presheaf pushout to the underlying presheaf of the sheaf pushout.
* `Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.presheafExtendScalarsComparison`: the
  sectionwise form of the comparison, `a ⊗ x ↦ inr(a) · inl(x)`, obtained as the transpose of the
  inclusion of the first factor across the sectionwise change-of-rings adjunction of
  [Stacks, Tag 03CU].

## Main results

* `Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.w_presheafPushoutCompare`: the comparison out
  of the presheaf pushout is inverted by sheafification.
* `Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.exists_objectwiseFactorisation`: over each
  object the sectionwise comparison is that comparison read through a bijection, natural in the
  object.
* `…isLocallyInjective_presheafExtendScalarsComparison` and
  `…isLocallySurjective_presheafExtendScalarsComparison`: the sectionwise comparison is locally
  bijective.
* `Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.bijective_pushoutInlModuleMap_comp`: the
  inclusion of the first factor exhibits the module underlying `B ⊗_R R'` as the extension of
  scalars.
* `Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.isIso_extendScalarsComparison`: the
  comparison is invertible, and `…underlyingModuleExtendScalarsIso` is the resulting
  identification.

## Implementation notes

The argument is objectwise rather than through the fibres at points of the site, so it needs no
hypothesis that the site has enough points. It runs in three steps.

1. `w_presheafPushoutCompare`. The pushout of the span in presheaves of commutative rings has
   the same morphisms into a *sheaf* as the sheaf pushout does — both are pairs of morphisms
   out of the two corners agreeing on the apex, and `CategoryTheory.sheafToPresheaf` is fully
   faithful. That is exactly membership in `CategoryTheory.GrothendieckTopology.W`, which for
   `J.WEqualsLocallyBijective CommRingCat` is local bijectivity. Stating it this way avoids
   identifying the sheaf pushout with the sheafification of the presheaf pushout, which would
   have meant transporting the two legs across the counit of sheafification.
2. `exists_objectwiseFactorisation`. Over each object the presheaf pushout is a pushout of
   commutative rings, because evaluation preserves colimits of presheaves, hence is the tensor
   product by `Stacks.Sites.CommRingPushout.exists_ringEquiv_tensorProduct_of_isPushout`
   applied to the *flipped* square; and the sectionwise extension of scalars is the same
   tensor product, by construction of
   `Stacks.PresheafOfModules.ChangeOfRings.changeOfRings`. The bijection matching them is
   natural because the two legs of the presheaf pushout are.
3. `bijective_pushoutInlModuleMap_comp`, and then invertibility by corepresentability. A
   locally bijective morphism of presheaves of modules is inverted on morphisms into a sheaf
   (`PresheafOfModules.homEquivOfIsLocallyBijective`), so morphisms out of the module
   underlying `B ⊗_R R'` are morphisms out of the sectionwise extension of scalars, which by
   [Stacks, Tag 03CU] are the `R`-linear morphisms out of the module underlying `B`. That
   composite bijection is composition with
   `Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.pushoutInlModuleMap`, so
   `CategoryTheory.isIso_of_coyoneda_map_bijective` applies to the comparison, whose transpose
   is that inclusion.

`Stacks.FlatChangeOfRings.extendScalarsAdjunction` is built from
`Classical.choice (… changeOfRings_adjoint_restrictScalars …)`, so its unit cannot be computed
with. Step 3 uses only the *naturality* of its hom-equivalence together with
`Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.homEquiv_extendScalarsComparison`, both of
which hold for any choice of adjunction. At the sectionwise level, where a computation on pure
tensors is needed, the explicit
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction` is used instead.

`Stacks.FlatChangeOfRings.presheafExtendScalars φ` is `changeOfRings φ.hom` retyped, which puts
its coefficient presheaves in the form `(CategoryTheory.sheafToPresheaf J CommRingCat).obj R`.
Statements about its sections are written in that form: `R.obj` is definitionally equal but is
not found by instance search, and a tensor product written over it fails to elaborate.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.FlatChangeOfRings

universe w v u

namespace Stacks.SheafOfModules.AlgebraPushoutAnyUniverse

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R R' : Sheaf J CommRingCat.{w}}

section Presheaf

variable (φ : R ⟶ R') [HasPushoutsAlong φ] (B : Under R)

/-- The pushout, formed in presheaves of commutative rings, of the span whose sheaf pushout is
the algebra pushout `B ⊗_R R'`. -/
public abbrev presheafPushout : Cᵒᵖ ⥤ CommRingCat.{w} :=
  pushout B.hom.hom φ.hom

/-- The canonical comparison from the presheaf pushout to the underlying presheaf of the sheaf
pushout: the morphism determined by the two legs of the sheaf pushout. -/
public def presheafPushoutCompare :
    presheafPushout φ B ⟶ (pushout B.hom φ).obj :=
  pushout.desc (pushout.inl B.hom φ).hom (pushout.inr B.hom φ).hom
    ((sheafToPresheaf J CommRingCat.{w}).congr_map
      (pushout.condition (f := B.hom) (g := φ)))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The comparison from the presheaf pushout restricts along the first leg to the first leg of
the sheaf pushout. -/
@[simp]
public theorem inl_presheafPushoutCompare :
    pushout.inl B.hom.hom φ.hom ≫ presheafPushoutCompare φ B =
      (pushout.inl B.hom φ).hom :=
  pushout.inl_desc _ _ _

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The comparison from the presheaf pushout restricts along the second leg to the second leg of
the sheaf pushout. -/
@[simp]
public theorem inr_presheafPushoutCompare :
    pushout.inr B.hom.hom φ.hom ≫ presheafPushoutCompare φ B =
      (pushout.inr B.hom φ).hom :=
  pushout.inr_desc _ _ _

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The presheaf pushout becomes the sheaf pushout after sheafification.**  Morphisms into a
sheaf of commutative rings out of the underlying presheaf of the sheaf pushout are the same
thing as morphisms out of the presheaf pushout, both being pairs of morphisms out of the two
corners of the span that agree on the apex. -/
public theorem w_presheafPushoutCompare : J.W (presheafPushoutCompare φ B) := by
  intro Z hZ
  let Zs : Sheaf J CommRingCat.{w} := ⟨Z, hZ⟩
  refine ⟨fun g₁ g₂ hg => ?_, fun h => ?_⟩
  · replace hg : presheafPushoutCompare φ B ≫ g₁ = presheafPushoutCompare φ B ≫ g₂ := hg
    have e₁ : (pushout.inl B.hom φ).hom ≫ g₁ = (pushout.inl B.hom φ).hom ≫ g₂ := by
      rw [← inl_presheafPushoutCompare φ B, Category.assoc, Category.assoc, hg]
    have e₂ : (pushout.inr B.hom φ).hom ≫ g₁ = (pushout.inr B.hom φ).hom ≫ g₂ := by
      rw [← inr_presheafPushoutCompare φ B, Category.assoc, Category.assoc, hg]
    have h₁ : pushout.inl B.hom φ ≫ (Sheaf.Hom.mk g₁ : pushout B.hom φ ⟶ Zs) =
        pushout.inl B.hom φ ≫ Sheaf.Hom.mk g₂ := Sheaf.hom_ext e₁
    have h₂ : pushout.inr B.hom φ ≫ (Sheaf.Hom.mk g₁ : pushout B.hom φ ⟶ Zs) =
        pushout.inr B.hom φ ≫ Sheaf.Hom.mk g₂ := Sheaf.hom_ext e₂
    exact congrArg (fun t : (pushout B.hom φ ⟶ Zs) => t.hom) (pushout.hom_ext h₁ h₂)
  · have hcomm : B.hom ≫ (Sheaf.Hom.mk (pushout.inl B.hom.hom φ.hom ≫ h) : B.right ⟶ Zs) =
        φ ≫ Sheaf.Hom.mk (pushout.inr B.hom.hom φ.hom ≫ h) := by
      refine Sheaf.hom_ext ?_
      show B.hom.hom ≫ pushout.inl B.hom.hom φ.hom ≫ h =
        φ.hom ≫ pushout.inr B.hom.hom φ.hom ≫ h
      rw [← Category.assoc, ← Category.assoc, pushout.condition]
    refine ⟨(pushout.desc _ _ hcomm).hom, ?_⟩
    show presheafPushoutCompare φ B ≫ (pushout.desc _ _ hcomm).hom = h
    refine pushout.hom_ext ?_ ?_
    · rw [← Category.assoc, inl_presheafPushoutCompare]
      exact congrArg (fun t : (B.right ⟶ Zs) => t.hom) (pushout.inl_desc _ _ hcomm)
    · rw [← Category.assoc, inr_presheafPushoutCompare]
      exact congrArg (fun t : (R' ⟶ Zs) => t.hom) (pushout.inr_desc _ _ hcomm)

end Presheaf

section Comparison

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (φ : R ⟶ R') [HasPushoutsAlong φ] (B : Under R)

open Stacks.PresheafOfModules.ChangeOfRings in
/-- **The comparison of the sectionwise extension of scalars with the module underlying the
pushout.**  Over each object it is the map `a ⊗ x ↦ inr(a) · inl(x)` into the sections of the
pushout; it is the transpose, across the sectionwise change-of-rings adjunction, of the
inclusion of the first factor. -/
public def presheafExtendScalarsComparison :
    (presheafExtendScalars φ).obj (underlyingModule B).val ⟶
      (underlyingModule ((Under.pushout φ).obj B)).val :=
  counitHom ((sheafToPresheaf J CommRingCat.{w}).map φ) (pushoutInlModuleMap φ B).val

omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
open Stacks.PresheafOfModules.ChangeOfRings in
/-- **The comparison on pure tensors**: `a ⊗ x ↦ inr(a) · inl(x)`. -/
public theorem presheafExtendScalarsComparison_app_tmul (U : Cᵒᵖ)
    (a : R'.obj.obj U)
    (x : (underlyingModule B).val.obj U) :
    letI := (φ.hom.app U).hom.toAlgebra
    ((presheafExtendScalarsComparison φ B).app U).hom
        (a ⊗ₜ[R.obj.obj U] x) =
      ((pushout.inr B.hom φ).hom.app U).hom a *
        ((pushout.inl B.hom φ).hom.app U).hom x := by
  let := (φ.hom.app U).hom.toAlgebra
  exact (counitApp_tmul ((sheafToPresheaf J CommRingCat.{w}).map φ)
    (pushoutInlModuleMap φ B).val U a x).trans rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasPushoutsAlong φ] in
open scoped TensorProduct in
open Stacks.Sites.CommRingPushout in
/-- **The sections of the presheaf pushout are the sectionwise tensor product.**  Over each
object the presheaf pushout is a pushout of commutative rings, hence the tensor product, with
its two legs as the inclusions. -/
public theorem exists_pushoutTensorEquiv (U : Cᵒᵖ) :
    letI := (((sheafToPresheaf J CommRingCat.{w}).map φ).app U).hom.toAlgebra
    letI := (((sheafToPresheaf J CommRingCat.{w}).map B.hom).app U).hom.toAlgebra
    ∃ e : (((sheafToPresheaf J CommRingCat.{w}).obj R').obj U ⊗[
        ((sheafToPresheaf J CommRingCat.{w}).obj R).obj U]
        ((sheafToPresheaf J CommRingCat.{w}).obj B.right).obj U) ≃+*
          (presheafPushout φ B).obj U,
      ∀ a x, e (a ⊗ₜ x) = ((pushout.inr B.hom.hom φ.hom).app U).hom a *
          ((pushout.inl B.hom.hom φ.hom).app U).hom x :=
  exists_ringEquiv_tensorProduct_of_isPushout
    (((IsPushout.of_hasPushout B.hom.hom φ.hom).map
      ((evaluation Cᵒᵖ CommRingCat.{w}).obj U)).flip)

omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
open scoped TensorProduct in
open Stacks.PresheafOfModules.ChangeOfRings in
/-- **The sectionwise comparison is the comparison from the presheaf pushout, read through an
objectwise bijection.**  Over each object the sectionwise extension of scalars is the tensor
product, the presheaf pushout is the same tensor product, and the two are matched by the
bijection that carries `a ⊗ x` to `inr(a) · inl(x)`;  that bijection is natural, because the
two legs of the presheaf pushout are. -/
public theorem exists_objectwiseFactorisation :
    ∃ e : ∀ U : Cᵒᵖ, ((presheafExtendScalars φ).obj (underlyingModule B).val).obj U →
        (presheafPushout φ B).obj U,
      (∀ U, Function.Bijective (e U)) ∧
      (∀ (U : Cᵒᵖ) t, ((presheafExtendScalarsComparison φ B).app U).hom t =
        ((presheafPushoutCompare φ B).app U).hom (e U t)) ∧
      (∀ (U V : Cᵒᵖ) (f : U ⟶ V) t, ((presheafPushout φ B).map f).hom (e U t) =
        e V ((((presheafExtendScalars φ).obj (underlyingModule B).val).map f).hom t)) := by
  choose e he using exists_pushoutTensorEquiv φ B
  have hinl : ∀ (U : Cᵒᵖ) (x : ((sheafToPresheaf J CommRingCat.{w}).obj B.right).obj U),
      ((presheafPushoutCompare φ B).app U).hom
          (((pushout.inl B.hom.hom φ.hom).app U).hom x) =
        ((pushout.inl B.hom φ).hom.app U).hom x := fun U x =>
    ConcreteCategory.congr_hom
      (congrArg (fun t : (B.right.obj ⟶ (pushout B.hom φ).obj) => t.app U)
        (inl_presheafPushoutCompare φ B)) x
  have hinr : ∀ (U : Cᵒᵖ) (a : ((sheafToPresheaf J CommRingCat.{w}).obj R').obj U),
      ((presheafPushoutCompare φ B).app U).hom
          (((pushout.inr B.hom.hom φ.hom).app U).hom a) =
        ((pushout.inr B.hom φ).hom.app U).hom a := fun U a =>
    ConcreteCategory.congr_hom
      (congrArg (fun t : (R'.obj ⟶ (pushout B.hom φ).obj) => t.app U)
        (inr_presheafPushoutCompare φ B)) a
  have hfac : ∀ (U : Cᵒᵖ)
      (t : ((presheafExtendScalars φ).obj (underlyingModule B).val).obj U),
      ((presheafExtendScalarsComparison φ B).app U).hom t =
        ((presheafPushoutCompare φ B).app U).hom (e U t) := by
    intro U t
    induction t using TensorProduct.induction_on with
    | zero =>
      have h2 : ((presheafPushoutCompare φ B).app U).hom (e U 0) = 0 :=
        (congrArg _ (map_zero (e U))).trans (map_zero _)
      exact (map_zero _).trans h2.symm
    | add s t hs ht =>
      have h2 : ((presheafPushoutCompare φ B).app U).hom (e U (s + t)) =
          ((presheafPushoutCompare φ B).app U).hom (e U s) +
            ((presheafPushoutCompare φ B).app U).hom (e U t) :=
        (congrArg _ (map_add (e U) s t)).trans (map_add _ _ _)
      exact (map_add _ s t).trans ((congrArg₂ (· + ·) hs ht).trans h2.symm)
    | tmul a x =>
      have hm : ((presheafPushoutCompare φ B).app U).hom
            (((pushout.inr B.hom.hom φ.hom).app U).hom a *
              ((pushout.inl B.hom.hom φ.hom).app U).hom x) =
          ((pushout.inr B.hom φ).hom.app U).hom a *
            ((pushout.inl B.hom φ).hom.app U).hom x :=
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (hinr U a) (hinl U x))
      refine (presheafExtendScalarsComparison_app_tmul φ B U a x).trans ?_
      exact hm.symm.trans (congrArg _ (he U a x)).symm
  have hnat : ∀ (U V : Cᵒᵖ) (f : U ⟶ V)
      (t : ((presheafExtendScalars φ).obj (underlyingModule B).val).obj U),
      ((presheafPushout φ B).map f).hom (e U t) =
        e V ((((presheafExtendScalars φ).obj (underlyingModule B).val).map f).hom t) := by
    intro U V f t
    induction t using TensorProduct.induction_on with
    | zero =>
      have h1 : ((presheafPushout φ B).map f).hom (e U 0) = 0 :=
        (congrArg _ (map_zero (e U))).trans (map_zero _)
      have h2 : e V ((((presheafExtendScalars φ).obj (underlyingModule B).val).map f).hom 0)
          = 0 := (congrArg _ (map_zero _)).trans (map_zero (e V))
      exact h1.trans h2.symm
    | add s t hs ht =>
      have h1 : ((presheafPushout φ B).map f).hom (e U (s + t)) =
          ((presheafPushout φ B).map f).hom (e U s) +
            ((presheafPushout φ B).map f).hom (e U t) :=
        (congrArg _ (map_add (e U) s t)).trans (map_add _ _ _)
      have h2 : e V ((((presheafExtendScalars φ).obj (underlyingModule B).val).map f).hom
            (s + t)) =
          e V ((((presheafExtendScalars φ).obj (underlyingModule B).val).map f).hom s) +
            e V ((((presheafExtendScalars φ).obj (underlyingModule B).val).map f).hom t) :=
        (congrArg _ (map_add _ s t)).trans (map_add (e V) _ _)
      exact h1.trans ((congrArg₂ (· + ·) hs ht).trans h2.symm)
    | tmul a x =>
      have hnl : ((pushout.inl B.hom.hom φ.hom).app V).hom
            (((underlyingModule B).val.map f).hom x) =
          ((presheafPushout φ B).map f).hom
            (((pushout.inl B.hom.hom φ.hom).app U).hom x) :=
        ConcreteCategory.congr_hom ((pushout.inl B.hom.hom φ.hom).naturality f) x
      have hnr : ((pushout.inr B.hom.hom φ.hom).app V).hom
            ((((sheafToPresheaf J CommRingCat.{w}).obj R').map f).hom a) =
          ((presheafPushout φ B).map f).hom
            (((pushout.inr B.hom.hom φ.hom).app U).hom a) :=
        ConcreteCategory.congr_hom ((pushout.inr B.hom.hom φ.hom).naturality f) a
      refine Eq.trans (congrArg _ (he U a x)) ?_
      refine Eq.trans (map_mul _ _ _) ?_
      refine Eq.trans ?_ (congrArg (e V) (cofMap_tmul φ.hom (underlyingModule B).val f a x)).symm
      refine Eq.trans ?_ (he V _ _).symm
      exact (congrArg₂ (· * ·) hnr hnl).symm
  exact ⟨fun U t => e U t, fun U => (e U).bijective, hfac, hnat⟩

section LocallyBijective

variable [HasSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]

/-- **The sectionwise comparison is locally injective**: it is the locally injective comparison
from the presheaf pushout, read through an objectwise bijection. -/
public instance isLocallyInjective_presheafExtendScalarsComparison :
    PresheafOfModules.IsLocallyInjective J (presheafExtendScalarsComparison φ B) := by
  obtain ⟨e, hbij, hfac, hnat⟩ := exists_objectwiseFactorisation φ B
  have := (w_presheafPushoutCompare φ B).isLocallyInjective
  constructor
  intro U t₁ t₂ h
  have h' : ((presheafPushoutCompare φ B).app U).hom (e U t₁) =
      ((presheafPushoutCompare φ B).app U).hom (e U t₂) :=
    ((hfac U t₁).symm.trans h).trans (hfac U t₂)
  refine J.superset_covering ?_
    (Presheaf.IsLocallyInjective.equalizerSieve_mem (J := J)
      (φ := presheafPushoutCompare φ B) (e U t₁) (e U t₂) h')
  intro V g hg
  exact (hbij (op V)).1
    (((hnat U (op V) g.op t₁).symm.trans hg).trans (hnat U (op V) g.op t₂))

/-- **The sectionwise comparison is locally surjective**: it is the locally surjective
comparison from the presheaf pushout, read through an objectwise bijection. -/
public instance isLocallySurjective_presheafExtendScalarsComparison :
    PresheafOfModules.IsLocallySurjective J (presheafExtendScalarsComparison φ B) := by
  obtain ⟨e, hbij, hfac, hnat⟩ := exists_objectwiseFactorisation φ B
  have := (w_presheafPushoutCompare φ B).isLocallySurjective
  constructor
  intro U s
  refine J.superset_covering ?_
    (Presheaf.IsLocallySurjective.imageSieve_mem (J := J)
      (f := presheafPushoutCompare φ B)
      (show CategoryTheory.ToType ((pushout B.hom φ).obj.obj (op U)) from s))
  rintro V g ⟨p, hp⟩
  obtain ⟨t, ht⟩ := (hbij (op V)).2 p
  exact ⟨t, ((hfac (op V) t).trans (congrArg _ ht)).trans hp⟩

/-! ### Invertibility of the comparison -/

omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}] in
open Stacks.PresheafOfModules.ChangeOfRings in
/-- The transpose of the sectionwise comparison, across the sectionwise change-of-rings
adjunction, is the inclusion of the first factor of the pushout. -/
public theorem homEquiv_presheafExtendScalarsComparison :
    ((changeOfRingsAdjunction ((sheafToPresheaf J CommRingCat.{w}).map φ)).homEquiv
        (underlyingModule B).val (underlyingModule ((Under.pushout φ).obj B)).val)
      (presheafExtendScalarsComparison φ B) = (pushoutInlModuleMap φ B).val := by
  have h : ∀ G F, (changeOfRingsAdjunction ((sheafToPresheaf J CommRingCat.{w}).map φ)).homEquiv
      G F = homEquivCore ((sheafToPresheaf J CommRingCat.{w}).map φ) G F := fun G F =>
    congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) G) F
  exact (DFunLike.congr_fun (h _ _) (presheafExtendScalarsComparison φ B)).trans
    (Equiv.apply_symm_apply _ _)

omit [HasWeakSheafify J AddCommGrpCat.{w}] [HasSheafify J CommRingCat.{w}] in
open Stacks.PresheafOfModules.ChangeOfRings in
/-- **The inclusion of the first factor exhibits the module underlying the pushout as the
extension of scalars.**  Composing with it is a bijection from the morphisms of `R'`-modules
out of the module underlying `B ⊗_R R'` to the `R`-linear morphisms out of the module
underlying `B`:  the sectionwise comparison is locally bijective, so a morphism out of the
sheaf is a morphism out of the sectionwise extension of scalars, and those are the `R`-linear
morphisms out of `B` by the sectionwise change-of-rings adjunction. -/
public theorem bijective_pushoutInlModuleMap_comp
    (T : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R')) :
    Function.Bijective (fun v : underlyingModule ((Under.pushout φ).obj B) ⟶ T =>
      pushoutInlModuleMap φ B ≫
        (_root_.SheafOfModules.restrictScalars.{w} (ringSheafMap φ)).map v) := by
  have hE : ∀ v : underlyingModule ((Under.pushout φ).obj B) ⟶ T,
      (pushoutInlModuleMap φ B ≫
          (_root_.SheafOfModules.restrictScalars.{w} (ringSheafMap φ)).map v).val =
        ((changeOfRingsAdjunction ((sheafToPresheaf J CommRingCat.{w}).map φ)).homEquiv _ _)
          ((PresheafOfModules.homEquivOfIsLocallyBijective (presheafExtendScalarsComparison φ B)
            T.isSheaf) v.val) := by
    intro v
    refine Eq.trans ?_ (congrArg _ (PresheafOfModules.homEquivOfIsLocallyBijective_apply
      (presheafExtendScalarsComparison φ B) T.isSheaf v.val)).symm
    exact ((Adjunction.homEquiv_naturality_right _ (presheafExtendScalarsComparison φ B)
      v.val).trans (congrArg (fun z => z ≫ _) (homEquiv_presheafExtendScalarsComparison φ B))).symm
  refine ⟨fun v₁ v₂ hv => ?_, fun u => ?_⟩
  · refine (_root_.SheafOfModules.fullyFaithfulForget
      (Stacks.SheafOfModules.Tensor.ringSheaf R')).map_injective ?_
    refine (PresheafOfModules.homEquivOfIsLocallyBijective (presheafExtendScalarsComparison φ B)
      T.isSheaf).injective ?_
    refine ((changeOfRingsAdjunction ((sheafToPresheaf J CommRingCat.{w}).map φ)).homEquiv
      _ _).injective ?_
    exact ((hE v₁).symm.trans (congrArg (fun z => z.val) hv)).trans (hE v₂)
  · refine ⟨⟨(PresheafOfModules.homEquivOfIsLocallyBijective
        (presheafExtendScalarsComparison φ B) T.isSheaf).symm
        (((changeOfRingsAdjunction ((sheafToPresheaf J CommRingCat.{w}).map φ)).homEquiv
          _ _).symm u.val)⟩, ?_⟩
    refine (_root_.SheafOfModules.fullyFaithfulForget
      (Stacks.SheafOfModules.Tensor.ringSheaf R)).map_injective ?_
    exact (hE _).trans <| (congrArg _ (Equiv.apply_symm_apply _ _)).trans
      (Equiv.apply_symm_apply _ _)

omit [HasSheafify J CommRingCat.{w}] in
/-- **The canonical comparison of the extension of scalars with the module underlying the
pushout is invertible**, for a morphism of sheaves of commutative rings on an arbitrary site
and a sheaf of commutative algebras over its source.

Both sides corepresent the same functor:  composing with the inclusion of the first factor of
the pushout is a bijection by `bijective_pushoutInlModuleMap_comp`, and composing with the
comparison is that bijection read through the extension-of-scalars adjunction. -/
public theorem isIso_extendScalarsComparison :
    IsIso (extendScalarsComparison φ B) := by
  refine isIso_of_coyoneda_map_bijective _ fun T => ?_
  have key : (fun v : underlyingModule ((Under.pushout φ).obj B) ⟶ T =>
      extendScalarsComparison φ B ≫ v) =
      (fun u => ((extendScalarsAdjunction φ).homEquiv _ _).symm u) ∘
        (fun v : underlyingModule ((Under.pushout φ).obj B) ⟶ T =>
          pushoutInlModuleMap φ B ≫
            (_root_.SheafOfModules.restrictScalars.{w} (ringSheafMap φ)).map v) := by
    funext v
    refine ((extendScalarsAdjunction φ).homEquiv _ _).injective ?_
    refine Eq.trans ?_ (Equiv.apply_symm_apply _ _).symm
    exact (Adjunction.homEquiv_naturality_right _ (extendScalarsComparison φ B) v).trans
      (congrArg (fun z => z ≫ _) (homEquiv_extendScalarsComparison φ B))
  exact key ▸ (((extendScalarsAdjunction φ).homEquiv _ _).symm.bijective).comp
    (bijective_pushoutInlModuleMap_comp φ B T)

/-- **The module underlying the pushout `B ⊗_R R'` is the extension of scalars along `φ` of
the module underlying `B`**, on an arbitrary site. -/
public noncomputable def underlyingModuleExtendScalarsIso :
    underlyingModule ((Under.pushout φ).obj B) ≅
      (extendScalars φ).obj (underlyingModule B) :=
  underlyingModulePushoutIso φ B (isIso_extendScalarsComparison φ B)

end LocallyBijective

end Comparison

end Stacks.SheafOfModules.AlgebraPushoutAnyUniverse

end
