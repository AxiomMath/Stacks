module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietorisAndHom.HomComplexEvaluation

/-!
# Composition of internal Hom complexes on a ringed site

Let `(C, O)` be a ringed site and let `K`, `L`, `M` be complexes of `O`-modules. Composition of
local maps induces a morphism from the total tensor product of the internal Hom complex from
`L` to `M` with the internal Hom complex from `K` to `L` to the internal Hom complex from `K`
to `M`. This file constructs that morphism.

Since the total tensor complex is sheafified degreewise, a general section of it is only
locally a sum of homogeneous pure tensors, so the composition morphism is pinned down by its
effect on those: a tensor `β ⊗ γ` of a degree-`p` and a degree-`q` local Hom section is sent to
the degree-`(p + q)` section acting by `β ∘ γ`, with no extra sign.
`CompositionConstruction` records that characterisation and `compositionConstruction` supplies
a morphism satisfying it.

## Main definitions

* `Stacks.Cohomology.composeLocalHomSections` and
  `Stacks.Cohomology.composeLocalHomSectionsAt`: the composite of two homogeneous local Hom
  sections, in degree `p + q` and in a prescribed total degree.
* `Stacks.Cohomology.CompositionConstruction`: composition morphisms, specified by their action
  on all homogeneous local pure tensors.
* `Stacks.Cohomology.compositionConstruction` (Stacks 0A91): the canonical composition
  morphism.

## Main results

* `Stacks.Cohomology.apply_composeLocalHomSections`: the composite acts by composition.
* `Stacks.Cohomology.composeLocalHomSections_add_left`, `_add_right`, `_smul_left` and
  `_smul_right`: composition of local Hom sections is `O(U)`-bilinear.
* `Stacks.Cohomology.composeLocalHomSections_restrict`: composition commutes with restriction
  along an arrow of the site.
* `Stacks.Cohomology.composeLocalHomSectionsAt_differential`: the Leibniz rule for the
  differential of the internal Hom complex on a composite.
* `Stacks.Cohomology.exists_composition`: a composition morphism exists.

## Implementation notes

Composition is first defined on local sections, through the identification of the sections of
an internal Hom complex over an object with Mathlib's `CochainComplex.HomComplex` of the
restrictions to the slice site, where it is `CochainComplex.HomComplex.Cochain.comp`. Its
additivity and `O(U)`-bilinearity give a map out of the degreewise tensor product of the
underlying presheaves of modules; the Leibniz rule for the Hom-complex differential
(`CochainComplex.HomComplex.δ_comp`) makes that a map of complexes of presheaves; and
`AlgebraicGeometry.RingedSite.sheafifyLift` lifts it to the sheafified total complex.

The coercions this material needs are all carried by the result types of abbreviations set up
alongside the evaluation morphism of Stacks 0A92, namely
`Stacks.Cohomology.restrictSection`, `Stacks.Cohomology.sheafSection` and
`Stacks.Cohomology.applyHomSectionOver`; see the implementation notes there.

The degreewise composition map is taken into degree `p + q` and transported along the index
equation by pattern matching on that equation rather than by an `eqToHom`, which is what keeps
the compatibility with the differentials free of transport terms.

## References

* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.RingedSite
open CochainComplex.HomComplex
open Stacks.Cohomology.InternalHom

universe u

namespace Stacks.Cohomology

variable (X : RingedSite.{u, u, u})

/-- The ring of sections of the structure sheaf over `U`, as a commutative ring. -/
noncomputable local instance (U : X.Cᵒᵖ) :
    CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) :=
  inferInstanceAs (CommRing (X.O.obj.obj U))

/-- The monoidal structure on presheaves of modules over the structure sheaf of `X`. -/
noncomputable local instance :
    MonoidalCategory (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.O.obj)

/-- Tensoring presheaves of modules preserves zero morphisms in the left variable. -/
local instance :
    (curriedTensor (PresheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).PreservesZeroMorphisms where
  map_zero {A B} := by
    apply NatTrans.ext
    funext C
    ext U : 1
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a c
    change (0 : B.obj U) ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] c = 0
    exact TensorProduct.zero_tmul _ _

/-- Tensoring presheaves of modules preserves zero morphisms in the right variable. -/
local instance (A : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :
    ((curriedTensor (PresheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj A).PreservesZeroMorphisms where
  map_zero {B C} := by
    ext U : 1
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a b
    change a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] (0 : C.obj U) = 0
    exact TensorProduct.tmul_zero _ _

/-- The ring `(X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U` is commutative. -/
noncomputable local instance (U : X.Cᵒᵖ) :
    CommRing ((X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U) :=
  inferInstanceAs (CommRing (X.O.obj.obj U))

/-- The sections over `U` of a presheaf of modules, as a module over
`(X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U`. -/
noncomputable local instance
    (A : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) (U : X.Cᵒᵖ) :
    Module ((X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U) (A.obj U) :=
  inferInstanceAs (Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (A.obj U))

/-- The two actions of `(X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U` on the sections over `U`
of a presheaf of modules commute. -/
noncomputable local instance
    (A : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) (U : X.Cᵒᵖ) :
    SMulCommClass ((X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U)
      ((X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U) (A.obj U) :=
  inferInstanceAs (SMulCommClass ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (A.obj U))

/-- A composition morphism characterized on every local homogeneous pure tensor. -/
structure CompositionConstruction where
  /-- The morphism of complexes induced by composition. -/
  comp (K L M :
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    tensorTotal X (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj ⟶
      (sheafHomComplex X K M).obj
  /-- Homogeneous tensors act by composition, with no additional sign. -/
  comp_tmul : ∀ (K L M : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (U : X.C)
      (p q r s : ℤ) (hrs : r + q = s) (hsp : s + p = r + q + p)
      (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
      (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U))
      (x : (K.X r).val.obj (op U)),
    applyHomSection X (sheafHomComplex X K M) U (p + q) r (r + q + p)
      (by omega)
      (((comp K L M).f (p + q)).val.app (op U)
        (tensorTotalSection X (sheafHomComplex X L M).obj
          (sheafHomComplex X K L).obj U p q β γ)) x =
      applyHomSection X (sheafHomComplex X L M) U p s (r + q + p) hsp β
        (applyHomSection X (sheafHomComplex X K L) U q r s hrs γ x)

/-- The composite of a degree-`p` and a degree-`q` local section of the internal Hom
complexes, as a local section of a prescribed total degree. -/
noncomputable def composeLocalHomSectionsAt
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (p q n : ℤ)
    (hn : q + p = n)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    ((sheafHomComplex X K M).obj.X n).val.obj (op U) :=
  (((sheafHomComplex X K M).sectionsIso U).inv.f n).hom
    (Cochain.comp (moduleCochainOfHomSection X (sheafHomComplex X K L) U q γ)
      (moduleCochainOfHomSection X (sheafHomComplex X L M) U p β) hn)

/-- The composite of a degree-`p` and a degree-`q` local section of the internal Hom
complexes, as a degree-`(p + q)` local section. -/
noncomputable def composeLocalHomSections
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (p q : ℤ)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    ((sheafHomComplex X K M).obj.X (p + q)).val.obj (op U) :=
  (((sheafHomComplex X K M).sectionsIso U).inv.f (p + q)).hom
    (Cochain.comp (moduleCochainOfHomSection X (sheafHomComplex X K L) U q γ)
      (moduleCochainOfHomSection X (sheafHomComplex X L M) U p β) (by omega))

/-- The composite in degree `p + q` is the composite in the prescribed total degree `p + q`. -/
lemma composeLocalHomSections_eq_at
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (p q : ℤ)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    composeLocalHomSections X K L M U p q β γ =
      composeLocalHomSectionsAt X K L M U p q (p + q) (by omega) β γ := rfl

/-- The cochain of a composite of local Hom sections is the composite of their cochains. -/
lemma composeLocalHomSectionsAt_cochain
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (p q n : ℤ)
    (hn : q + p = n)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    moduleCochainOfHomSection X (sheafHomComplex X K M) U n
        (composeLocalHomSectionsAt X K L M U p q n hn β γ) =
      Cochain.comp (moduleCochainOfHomSection X (sheafHomComplex X K L) U q γ)
        (moduleCochainOfHomSection X (sheafHomComplex X L M) U p β) hn :=
  ((HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) n).mapIso
    ((sheafHomComplex X K M).sectionsIso U)).inv_hom_id_apply _

/-- The cochain of a composite of local Hom sections in degree `p + q`. -/
lemma composeLocalHomSections_cochain
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (p q : ℤ)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    moduleCochainOfHomSection X (sheafHomComplex X K M) U (p + q)
        (composeLocalHomSections X K L M U p q β γ) =
      Cochain.comp (moduleCochainOfHomSection X (sheafHomComplex X K L) U q γ)
        (moduleCochainOfHomSection X (sheafHomComplex X L M) U p β) (by omega) :=
  composeLocalHomSectionsAt_cochain X K L M U p q (p + q) (by omega) β γ

/-- A local Hom section is determined by its cochain on the slice site. -/
private lemma homSection_of_cochain_eq
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U : X.C) (n : ℤ)
    {f g : (H.obj.X n).val.obj (op U)}
    (h : moduleCochainOfHomSection X H U n f = moduleCochainOfHomSection X H U n g) :
    f = g := by
  let e := (HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) n).mapIso
    (H.sectionsIso U)
  exact (e.hom_inv_id_apply f).symm.trans ((congrArg e.inv.hom h).trans (e.hom_inv_id_apply g))

/-- The action over an object of the slice of a restricted local Hom section is the action of
the original section over the composite arrow. -/
private lemma applyHomSectionOver_restrictSection
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) {U V W : X.C} (i : V ⟶ U) (j : W ⟶ V)
    (n p q : ℤ) (hpq : p + n = q)
    (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op W)) :
    applyHomSectionOver X H V W j n p q hpq (restrictSection X (H.obj.X n) i f) x =
      applyHomSectionOver X H U W (j ≫ i) n p q hpq f x :=
  (H.restrict_natural i n p q hpq f j x).symm

/-- The composite of local Hom sections acts over every object of the slice by composing the
actions of its factors. -/
lemma composeLocalHomSections_applyOver
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U V : X.C) (i : V ⟶ U)
    (p q r s t : ℤ) (hrs : r + q = s) (hst : s + p = t)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U))
    (x : (K.X r).val.obj (op V)) :
    applyHomSectionOver X (sheafHomComplex X K M) U V i (p + q) r t (by omega)
        (composeLocalHomSections X K L M U p q β γ) x =
      applyHomSectionOver X (sheafHomComplex X L M) U V i p s t hst β
        (applyHomSectionOver X (sheafHomComplex X K L) U V i q r s hrs γ x) := by
  refine Eq.trans (congrArg
    (fun w : Cochain (restrictComplex X K U) (restrictComplex X M U) (p + q) =>
      (ModuleCat.Hom.hom ((w.v r t (by omega)).val.app (op (Over.mk i)))) x)
    (composeLocalHomSections_cochain X K L M U p q β γ)) ?_
  refine Eq.trans (congrArg
    (fun w : (restrictComplex X K U).X r ⟶ (restrictComplex X M U).X t =>
      (ModuleCat.Hom.hom (w.val.app (op (Over.mk i)))) x)
    (Cochain.comp_v (moduleCochainOfHomSection X (sheafHomComplex X K L) U q γ)
      (moduleCochainOfHomSection X (sheafHomComplex X L M) U p β)
      (show q + p = p + q by omega) r s t hrs hst)) ?_
  rfl

/-- The composite of local Hom sections acts over every object of the slice by composing the
actions of its factors, with the intermediate degree `r + q`. -/
private lemma composeLocalHomSections_applyOver_add
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U V : X.C) (i : V ⟶ U) (p q r t : ℤ) (ht : r + q + p = t)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U))
    (x : (K.X r).val.obj (op V)) :
    applyHomSectionOver X (sheafHomComplex X K M) U V i (p + q) r t (by omega)
        (composeLocalHomSections X K L M U p q β γ) x =
      applyHomSectionOver X (sheafHomComplex X L M) U V i p (r + q) t ht β
        (applyHomSectionOver X (sheafHomComplex X K L) U V i q r (r + q) rfl γ x) :=
  composeLocalHomSections_applyOver X K L M U V i p q r (r + q) t rfl ht β γ x

/-- The composite of local Hom sections acts by composing their actions. -/
theorem apply_composeLocalHomSections
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C)
    (p q r s t : ℤ) (hrs : r + q = s) (hst : s + p = t)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U))
    (x : (K.X r).val.obj (op U)) :
    applyHomSection X (sheafHomComplex X K M) U (p + q) r t (by omega)
        (composeLocalHomSections X K L M U p q β γ) x =
      applyHomSection X (sheafHomComplex X L M) U p s t hst β
        (applyHomSection X (sheafHomComplex X K L) U q r s hrs γ x) :=
  composeLocalHomSections_applyOver X K L M U U (𝟙 U) p q r s t hrs hst β γ x

/-- Composition of local Hom sections is additive in the outer factor. -/
theorem composeLocalHomSections_add_left
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (p q : ℤ)
    (β β' : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    composeLocalHomSections X K L M U p q (β + β') γ =
      composeLocalHomSections X K L M U p q β γ +
        composeLocalHomSections X K L M U p q β' γ := by
  refine homSection_of_cochain_eq X (sheafHomComplex X K M) U (p + q) ?_
  rw [composeLocalHomSections_cochain, moduleCochainOfHomSection_add, Cochain.comp_add,
    moduleCochainOfHomSection_add, composeLocalHomSections_cochain,
    composeLocalHomSections_cochain]

/-- Composition of local Hom sections is additive in the inner factor. -/
theorem composeLocalHomSections_add_right
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (p q : ℤ)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ γ' : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    composeLocalHomSections X K L M U p q β (γ + γ') =
      composeLocalHomSections X K L M U p q β γ +
        composeLocalHomSections X K L M U p q β γ' := by
  refine homSection_of_cochain_eq X (sheafHomComplex X K M) U (p + q) ?_
  rw [composeLocalHomSections_cochain, moduleCochainOfHomSection_add, Cochain.add_comp,
    moduleCochainOfHomSection_add, composeLocalHomSections_cochain,
    composeLocalHomSections_cochain]

/-- Composition of local Hom sections is linear in the outer factor. -/
theorem composeLocalHomSections_smul_left
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (p q : ℤ)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    composeLocalHomSections X K L M U p q (a • β) γ =
      a • composeLocalHomSections X K L M U p q β γ := by
  refine homSection_ext X (sheafHomComplex X K M) U (p + q) ?_
  intro r t hrt V i x
  rw [applyHomSectionOver_smul_left,
    composeLocalHomSections_applyOver_add X K L M U V i p q r t (by omega),
    composeLocalHomSections_applyOver_add X K L M U V i p q r t (by omega),
    applyHomSectionOver_smul_left]

/-- Composition of local Hom sections is linear in the inner factor. -/
theorem composeLocalHomSections_smul_right
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (p q : ℤ)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    composeLocalHomSections X K L M U p q β (a • γ) =
      a • composeLocalHomSections X K L M U p q β γ := by
  refine homSection_ext X (sheafHomComplex X K M) U (p + q) ?_
  intro r t hrt V i x
  rw [applyHomSectionOver_smul_left,
    composeLocalHomSections_applyOver_add X K L M U V i p q r t (by omega),
    composeLocalHomSections_applyOver_add X K L M U V i p q r t (by omega),
    applyHomSectionOver_smul_left, applyHomSectionOver_smul_right]

/-- Composition of local Hom sections commutes with restriction along an arrow of the site. -/
lemma composeLocalHomSections_restrict
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U V : X.C) (i : V ⟶ U)
    (p q : ℤ)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    restrictSection X ((sheafHomComplex X K M).obj.X (p + q)) i
        (composeLocalHomSections X K L M U p q β γ) =
      composeLocalHomSections X K L M V p q
        (restrictSection X ((sheafHomComplex X L M).obj.X p) i β)
        (restrictSection X ((sheafHomComplex X K L).obj.X q) i γ) := by
  refine homSection_ext X (sheafHomComplex X K M) V (p + q) ?_
  intro r t hrt W j x
  rw [applyHomSectionOver_restrictSection,
    composeLocalHomSections_applyOver_add X K L M U W (j ≫ i) p q r t (by omega),
    composeLocalHomSections_applyOver_add X K L M V W j p q r t (by omega),
    applyHomSectionOver_restrictSection, applyHomSectionOver_restrictSection]

/-- The Leibniz rule for the differential of the internal Hom complex on a composite of local
Hom sections. -/
lemma composeLocalHomSectionsAt_differential
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (p q : ℤ)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    ((sheafHomComplex X K M).obj.d (p + q) (p + q + 1)).val.app (op U)
        (composeLocalHomSectionsAt X K L M U p q (p + q) (by omega) β γ) =
      composeLocalHomSectionsAt X K L M U (p + 1) q (p + q + 1) (by omega)
          (((sheafHomComplex X L M).obj.d p (p + 1)).val.app (op U) β) γ +
        (p.negOnePow : ℤ) •
          composeLocalHomSectionsAt X K L M U p (q + 1) (p + q + 1) (by omega) β
            (((sheafHomComplex X K L).obj.d q (q + 1)).val.app (op U) γ) := by
  refine homSection_of_cochain_eq X (sheafHomComplex X K M) U (p + q + 1) ?_
  rw [moduleCochainOfHomSection_d X (sheafHomComplex X K M) U (p + q)
      (composeLocalHomSectionsAt X K L M U p q (p + q) (by omega) β γ),
    composeLocalHomSectionsAt_cochain, moduleCochainOfHomSection_add,
    moduleCochainOfHomSection_zsmul, composeLocalHomSectionsAt_cochain,
    composeLocalHomSectionsAt_cochain,
    moduleCochainOfHomSection_d X (sheafHomComplex X L M) U p β,
    moduleCochainOfHomSection_d X (sheafHomComplex X K L) U q γ,
    δ_comp (moduleCochainOfHomSection X (sheafHomComplex X K L) U q γ)
      (moduleCochainOfHomSection X (sheafHomComplex X L M) U p β)
      (show q + p = p + q by omega) (q + 1) (p + 1) (p + q + 1) (by omega) rfl rfl,
    Units.smul_def]

/-- The `O(U)`-bilinear map that composition induces on local sections: it sends `β` and `γ`
to the Hom section `composeLocalHomSections`. Its source and target are spelled as modules
over `X.O.obj ⋙ forget₂ CommRingCat RingCat`, the ring the monoidal structure on presheaves of
modules uses, rather than over `X.ringSheaf.obj`. -/
private noncomputable def compositionBilinear
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (p q : ℤ) (U : X.Cᵒᵖ) :
    ((underlyingPresheafComplex X (sheafHomComplex X L M).obj).X p).obj U →ₗ[
        (X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U]
      ((underlyingPresheafComplex X (sheafHomComplex X K L).obj).X q).obj U →ₗ[
          (X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U]
        ((underlyingPresheafComplex X (sheafHomComplex X K M).obj).X (p + q)).obj U where
  toFun β :=
    { toFun := fun γ => composeLocalHomSections X K L M U.unop p q β γ
      map_add' := composeLocalHomSections_add_right X K L M U.unop p q β
      map_smul' := fun c γ => composeLocalHomSections_smul_right X K L M U.unop p q c β γ }
  map_add' β β' := LinearMap.ext fun γ =>
    composeLocalHomSections_add_left X K L M U.unop p q β β' γ
  map_smul' c β := LinearMap.ext fun γ =>
    composeLocalHomSections_smul_left X K L M U.unop p q c β γ

/-- The degreewise composition map out of a single tensor summand of the total complex of
presheaves of modules. -/
private noncomputable def compositionSummandMap
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (p q : ℤ) :
    ((curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj
      ((underlyingPresheafComplex X (sheafHomComplex X L M).obj).X p)).obj
        ((underlyingPresheafComplex X (sheafHomComplex X K L).obj).X q) ⟶
      (underlyingPresheafComplex X (sheafHomComplex X K M).obj).X (p + q) := by
  refine {
    app := fun U => ModuleCat.ofHom (TensorProduct.lift (compositionBilinear X p q U))
    naturality := ?_ }
  intro U V f
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro β γ
  change composeLocalHomSections X K L M V.unop p q
      (restrictSection X ((sheafHomComplex X L M).obj.X p) f.unop β)
      (restrictSection X ((sheafHomComplex X K L).obj.X q) f.unop γ) =
    restrictSection X ((sheafHomComplex X K M).obj.X (p + q)) f.unop
      (composeLocalHomSections X K L M U.unop p q β γ)
  exact (composeLocalHomSections_restrict X K L M U.unop V.unop f.unop p q β γ).symm

/-- The degreewise composition map of complexes of presheaves of modules. -/
private noncomputable def compositionFun
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    (HomologicalComplex.mapBifunctor
      (underlyingPresheafComplex X (sheafHomComplex X L M).obj)
      (underlyingPresheafComplex X (sheafHomComplex X K L).obj)
      (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
      (ComplexShape.up ℤ)).X n ⟶
    (underlyingPresheafComplex X (sheafHomComplex X K M).obj).X n :=
  HomologicalComplex.mapBifunctorDesc fun p q h =>
    match h with
    | rfl => compositionSummandMap X p q

/-- The value of the degreewise composition map of presheaves of modules on a homogeneous pure
tensor of local sections, with the modules of sections of the sheaves as its argument and
result types. -/
private noncomputable abbrev compositionTensor
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (p q n : ℤ) (h : p + q = n) (U : X.Cᵒᵖ)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj U)
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj U) :
    ((sheafHomComplex X K M).obj.X n).val.obj U :=
  (compositionFun X K L M n).app U
    ((HomologicalComplex.ιMapBifunctor (underlyingPresheafComplex X (sheafHomComplex X L M).obj)
      (underlyingPresheafComplex X (sheafHomComplex X K L).obj)
      (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
      (ComplexShape.up ℤ) p q n h).app U
        (β ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] γ))

private lemma compositionSummandMap_tmul
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (U : X.C) (p q : ℤ)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    (compositionSummandMap X p q).app (op U)
      (β ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] γ) =
      composeLocalHomSections X K L M U p q β γ := by
  with_unfolding_all rfl

private lemma compositionFun_tmul
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C)
    (p q n : ℤ) (h : p + q = n)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    (compositionFun X K L M n).app (op U)
      (((HomologicalComplex.ιMapBifunctor
        (underlyingPresheafComplex X (sheafHomComplex X L M).obj)
        (underlyingPresheafComplex X (sheafHomComplex X K L).obj)
        (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
        (ComplexShape.up ℤ)
        p q n h).app (op U))
        (β ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] γ)) =
      h ▸ composeLocalHomSections X K L M U p q β γ := by
  subst n
  change ((HomologicalComplex.ιMapBifunctor
      (underlyingPresheafComplex X (sheafHomComplex X L M).obj)
      (underlyingPresheafComplex X (sheafHomComplex X K L).obj)
      (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
      (ComplexShape.up ℤ)
      p q (p + q) rfl ≫ compositionFun X K L M (p + q)).app (op U))
      (β ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] γ) =
        composeLocalHomSections X K L M U p q β γ
  rw [compositionFun, HomologicalComplex.ι_mapBifunctorDesc]
  exact compositionSummandMap_tmul X U p q β γ

/-- The degreewise composition map sends the pure tensor `β ⊗ γ` to the composite of `β` and
`γ`. -/
private lemma compositionTensor_eq
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (p q n : ℤ) (h : p + q = n) (U : X.Cᵒᵖ)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj U)
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj U) :
    compositionTensor X K L M p q n h U β γ =
      composeLocalHomSectionsAt X K L M U.unop p q n (by omega) β γ := by
  subst n
  exact compositionFun_tmul X K L M U.unop p q (p + q) rfl β γ

/-- The degreewise composition map is compatible with the differentials on homogeneous pure
tensors, which is the Leibniz rule for composition. -/
private lemma compositionTensor_differential
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (p q : ℤ) (U : X.Cᵒᵖ)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj U)
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj U) :
    ((sheafHomComplex X K M).obj.d (p + q) (p + q + 1)).val.app U
        (compositionTensor X K L M p q (p + q) rfl U β γ) =
      compositionTensor X K L M (p + 1) q (p + q + 1) (by omega) U
          (((sheafHomComplex X L M).obj.d p (p + 1)).val.app U β) γ +
        (p.negOnePow : ℤ) • compositionTensor X K L M p (q + 1) (p + q + 1) (by omega) U β
          (((sheafHomComplex X K L).obj.d q (q + 1)).val.app U γ) := by
  simp only [compositionTensor_eq]
  exact composeLocalHomSectionsAt_differential X K L M U.unop p q β γ

/-- The composition map of complexes of presheaves of modules. -/
private noncomputable def compositionPresheaf
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    HomologicalComplex.mapBifunctor
      (underlyingPresheafComplex X (sheafHomComplex X L M).obj)
      (underlyingPresheafComplex X (sheafHomComplex X K L).obj)
      (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
      (ComplexShape.up ℤ) ⟶
      underlyingPresheafComplex X (sheafHomComplex X K M).obj where
  f := compositionFun X K L M
  comm' n m hnm := by
    obtain rfl : n + 1 = m := hnm
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    change p + q = n at h
    subst n
    let A := underlyingPresheafComplex X (sheafHomComplex X L M).obj
    let B := underlyingPresheafComplex X (sheafHomComplex X K L).obj
    let F := curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    change _ = (HomologicalComplex.ιMapBifunctor A B F (ComplexShape.up ℤ)
      p q (p + q) rfl ≫ (HomologicalComplex.mapBifunctor A B F
        (ComplexShape.up ℤ)).d (p + q) (p + q + 1)) ≫ _
    have hP : HomologicalComplex.ιMapBifunctor A B F (ComplexShape.up ℤ) p q (p + q) rfl ≫
        (HomologicalComplex.mapBifunctor A B F (ComplexShape.up ℤ)).d (p + q) (p + q + 1) =
        (F.map (A.d p (p + 1))).app (B.X q) ≫
            HomologicalComplex.ιMapBifunctor A B F (ComplexShape.up ℤ) (p + 1) q (p + q + 1)
              (by dsimp; omega) +
          p.negOnePow • ((F.obj (A.X p)).map (B.d q (q + 1)) ≫
            HomologicalComplex.ιMapBifunctor A B F (ComplexShape.up ℤ) p (q + 1) (p + q + 1)
              (by dsimp; omega)) := by
      rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
        HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
        HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
          (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl) _ _ (by dsimp; omega),
        HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _
          (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl) _ (by dsimp; omega)]
      simp only [ComplexShape.ε₁, TotalComplexShape.ε₁, one_smul]
      rfl
    rw [hP]
    simp only [Preadditive.add_comp, Units.smul_def, Preadditive.zsmul_comp,
      Category.assoc]
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro β γ
    simp only [PresheafOfModules.add_app, PresheafOfModules.zsmul_app,
      PresheafOfModules.comp_app]
    exact compositionTensor_differential X K L M p q U
      (sheafSection X (sheafHomComplex X L M).obj p U β)
      (sheafSection X (sheafHomComplex X K L).obj q U γ)

/-- There is a composition morphism for every three complexes of `O`-modules. -/
theorem exists_composition : Nonempty (CompositionConstruction X) :=
  ⟨{ comp := fun K L M => sheafifyLift X (compositionPresheaf X K L M)
     comp_tmul := by
       intro K L M U p q r s hrs hsp β γ x
       unfold tensorTotalSection
       rw [sheafifyLift_unit_apply]
       change applyHomSection X _ U (p + q) r (r + q + p) _
         ((compositionFun X K L M (p + q)).app (op U) _) x = _
       rw [compositionFun_tmul]
       exact apply_composeLocalHomSections X K L M U p q r s (r + q + p) hrs hsp β γ x }⟩

/-- The canonical composition of internal Hom complexes of module sheaves. -/
@[stacks 0A91]
noncomputable def compositionConstruction : CompositionConstruction X :=
  Classical.choice (exists_composition X)

end Stacks.Cohomology

end
