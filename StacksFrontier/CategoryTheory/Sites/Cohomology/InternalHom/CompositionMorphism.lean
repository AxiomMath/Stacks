module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluatingSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplex
import StacksCore.Tactic.StacksAttribute

/-! # The composition morphism of internal Hom complexes on a ringed site

Let `(C, O)` be a ringed site and let `K`, `L` and `M` be complexes of `O`-modules. Composing a
homogeneous local section of `SheafHom(L, M)` with one of `SheafHom(K, L)` gives a homogeneous
local section of `SheafHom(K, M)`, and that operation is `O`-bilinear and compatible with
restriction along arrows of the site. This file assembles it into the canonical morphism of
complexes of `O`-modules of Stacks 0A91,

`Tot(SheafHom(L, M) ⊗_O SheafHom(K, L)) ⟶ SheafHom(K, M)`,

and characterises it by its values on homogeneous local pure tensors: the pure tensor of a
degree-`p` section `β` of `SheafHom(L, M)` and a degree-`q` section `γ` of `SheafHom(K, L)` goes
to their composite, with no extra sign.

## Main definitions

* `AlgebraicGeometry.RingedSite.compositionCochain` and
  `AlgebraicGeometry.RingedSite.compositionSection`: the composite of two homogeneous local
  sections, as a cochain and as a section of `SheafHom(K, M)`.
* `AlgebraicGeometry.RingedSite.compositionMap`: the composition morphism of Stacks 0A91.
* `AlgebraicGeometry.RingedSite.CompositionConstruction`: the composition morphism together
  with its characterisation on homogeneous local pure tensors.

## Main results

* `AlgebraicGeometry.RingedSite.compositionSection_apply`: evaluating a composite section is
  evaluating the two factors in turn, with no sign.
* `AlgebraicGeometry.RingedSite.compositionSection_d`: the Leibniz rule for composition.
* `AlgebraicGeometry.RingedSite.compositionMap_tensorTotalSection`: the characterisation of
  `compositionMap` on homogeneous local pure tensors.
* `AlgebraicGeometry.RingedSite.compositionConstruction`: **Stacks 0A91**, hence also the
  ringed space case **Stacks 0A8N**.

## Implementation notes

The construction has three stages. Composition of homogeneous local sections is defined through
the characterising identification `SheafHomComplex.sectionsEquiv` of the sections of an internal
Hom complex with ordinary cochains, so that `Cochain.comp` and its Leibniz rule `δ_comp` supply
the algebra; everything about it is then proved in the evaluation vocabulary of
`StacksDraft.Ch21.Sec34.HomSectionEvaluation`, through
`AlgebraicGeometry.RingedSite.homSection_ext`. Its `O`-bilinearity makes it a morphism out of
the degreewise tensor product of presheaves, and the Leibniz rule makes the resulting family a
morphism out of the total complex of the double complex of those tensor products. Finally
`AlgebraicGeometry.RingedSite.sheafifyLift` passes from that presheaf-level morphism to one out
of the degreewise sheafification, which is `AlgebraicGeometry.RingedSite.tensorTotal`.

The monoidal structure on presheaves of modules is over the presheaf of *commutative* rings
`O`; it is switched on file-locally from
`StacksDraft.Ch21.Sec34.RingedSiteMonoidalInstances`, at the spelling `X.ringSheaf.obj` at
which sheaves of modules are indexed, exactly as in
`StacksDraft.Ch21.Sec34.TensorTotalComplex`; the two spellings of the ring are definitionally
equal.

## References

* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0A8N](https://stacks.math.columbia.edu/tag/0A8N)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A8I](https://stacks.math.columbia.edu/tag/0A8I)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

section Sections

variable
  {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The cochain from `K|_U` to `M|_U` obtained by composing a degree-`q` section `γ` of
`SheafHom(K, L)` over `U` with a degree-`p` section `β` of `SheafHom(L, M)` over `U`. -/
noncomputable def compositionCochain (U : X.C) (p q n : ℤ) (hn : p + q = n)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    Cochain (restrictComplex X K U) (restrictComplex X M U) n :=
  Cochain.comp ((sheafHomComplex X K L).sectionsEquiv U q γ)
    ((sheafHomComplex X L M).sectionsEquiv U p β) (by omega)

/-- The degree-`n` section of `SheafHom(K, M)` over `U` obtained by composing a degree-`q`
section `γ` of `SheafHom(K, L)` with a degree-`p` section `β` of `SheafHom(L, M)`, where
`p + q = n`. -/
noncomputable def compositionSection (U : X.C) (p q n : ℤ) (hn : p + q = n)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    ((sheafHomComplex X K M).obj.X n).val.obj (op U) :=
  ((sheafHomComplex X K M).sectionsEquiv U n).symm (compositionCochain X U p q n hn β γ)

/-- The cochain of `compositionSection` is `compositionCochain`. -/
lemma compositionSection_cochain (U : X.C) (p q n : ℤ) (hn : p + q = n)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    (sheafHomComplex X K M).sectionsEquiv U n (compositionSection X U p q n hn β γ) =
      compositionCochain X U p q n hn β γ :=
  ((sheafHomComplex X K M).sectionsEquiv U n).apply_symm_apply _

/-- Evaluating a composite section over an object of the slice site over `U` is evaluating the
two factors in turn, with no extra sign. -/
lemma compositionSection_applyOver (U V : X.C) (i : V ⟶ U) (p q n r s t : ℤ) (hn : p + q = n)
    (hrs : r + q = s) (hst : s + p = t)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) (x : (K.X r).val.obj (op V)) :
    applyHomSectionOver X (sheafHomComplex X K M) U V i n r t (by omega)
        (compositionSection X U p q n hn β γ) x =
      applyHomSectionOver X (sheafHomComplex X L M) U V i p s t hst β
        (applyHomSectionOver X (sheafHomComplex X K L) U V i q r s hrs γ x) := by
  change (((sheafHomComplex X K M).sectionsEquiv U n
      (compositionSection X U p q n hn β γ)).v r t (by omega)).val.app (op (Over.mk i)) x = _
  rw [compositionSection_cochain, compositionCochain,
    Cochain.comp_v _ _ (show q + p = n by omega) r s t hrs hst]
  rfl

/-- Evaluating a composite section over `U` is evaluating the two factors in turn, with no extra
sign. -/
lemma compositionSection_apply (U : X.C) (p q n r s t : ℤ) (hn : p + q = n)
    (hrs : r + q = s) (hst : s + p = t)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) (x : (K.X r).val.obj (op U)) :
    applyHomSection X (sheafHomComplex X K M) U n r t (by omega)
        (compositionSection X U p q n hn β γ) x =
      applyHomSection X (sheafHomComplex X L M) U p s t hst β
        (applyHomSection X (sheafHomComplex X K L) U q r s hrs γ x) :=
  compositionSection_applyOver X U U (𝟙 U) p q n r s t hn hrs hst β γ x

/-- `compositionSection_applyOver` with the intermediate degree `r + q`. -/
private lemma compositionSection_applyOver_add (U V : X.C) (i : V ⟶ U) (p q n r t : ℤ)
    (hn : p + q = n) (hrt : r + n = t)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) (x : (K.X r).val.obj (op V)) :
    applyHomSectionOver X (sheafHomComplex X K M) U V i n r t hrt
        (compositionSection X U p q n hn β γ) x =
      applyHomSectionOver X (sheafHomComplex X L M) U V i p (r + q) t (by omega) β
        (applyHomSectionOver X (sheafHomComplex X K L) U V i q r (r + q) rfl γ x) :=
  compositionSection_applyOver X U V i p q n r (r + q) t hn rfl (by omega) β γ x

/-- Composition is additive in the section of `SheafHom(L, M)`. -/
lemma compositionSection_add_left (U : X.C) (p q n : ℤ) (hn : p + q = n)
    (β β' : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    compositionSection X U p q n hn (β + β') γ =
      compositionSection X U p q n hn β γ + compositionSection X U p q n hn β' γ := by
  refine homSection_ext X (sheafHomComplex X K M) U n fun r t hrt V i x ↦ ?_
  rw [applyHomSectionOver_add_left, compositionSection_applyOver_add,
    compositionSection_applyOver_add, compositionSection_applyOver_add,
    applyHomSectionOver_add_left]

/-- Composition is additive in the section of `SheafHom(K, L)`. -/
lemma compositionSection_add_right (U : X.C) (p q n : ℤ) (hn : p + q = n)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ γ' : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    compositionSection X U p q n hn β (γ + γ') =
      compositionSection X U p q n hn β γ + compositionSection X U p q n hn β γ' := by
  refine homSection_ext X (sheafHomComplex X K M) U n fun r t hrt V i x ↦ ?_
  rw [applyHomSectionOver_add_left, compositionSection_applyOver_add,
    compositionSection_applyOver_add, compositionSection_applyOver_add,
    applyHomSectionOver_add_left, applyHomSectionOver_add_right]

/-- Composition is `O(U)`-linear in the section of `SheafHom(L, M)`. -/
lemma compositionSection_smul_left (U : X.C) (p q n : ℤ) (hn : p + q = n)
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    compositionSection X U p q n hn (c • β) γ = c • compositionSection X U p q n hn β γ := by
  refine homSection_ext X (sheafHomComplex X K M) U n fun r t hrt V i x ↦ ?_
  rw [applyHomSectionOver_smul_left, compositionSection_applyOver_add,
    compositionSection_applyOver_add, applyHomSectionOver_smul_left]

/-- Composition is `O(U)`-linear in the section of `SheafHom(K, L)`. -/
lemma compositionSection_smul_right (U : X.C) (p q n : ℤ) (hn : p + q = n)
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    compositionSection X U p q n hn β (c • γ) = c • compositionSection X U p q n hn β γ := by
  refine homSection_ext X (sheafHomComplex X K M) U n fun r t hrt V i x ↦ ?_
  rw [applyHomSectionOver_smul_left, compositionSection_applyOver_add,
    compositionSection_applyOver_add, applyHomSectionOver_smul_left, applyHomSectionOver_smul_right]

/-- Composition is compatible with restriction along an arrow of the site. -/
lemma compositionSection_restrict (U V : X.C) (i : V ⟶ U) (p q n : ℤ) (hn : p + q = n)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    ((sheafHomComplex X K M).obj.X n).val.map i.op (compositionSection X U p q n hn β γ) =
      compositionSection X V p q n hn (((sheafHomComplex X L M).obj.X p).val.map i.op β)
        (((sheafHomComplex X K L).obj.X q).val.map i.op γ) := by
  refine homSection_ext X (sheafHomComplex X K M) V n fun r t hrt W g x ↦ ?_
  rw [compositionSection_applyOver_add X V W g p q n r t hn hrt
      (((sheafHomComplex X L M).obj.X p).val.map i.op β)
      (((sheafHomComplex X K L).obj.X q).val.map i.op γ) x,
    ← applyHomSectionOver_restrict_comp X (sheafHomComplex X K M) U V W i g n r t hrt,
    compositionSection_applyOver_add, applyHomSectionOver_restrict_comp,
    applyHomSectionOver_restrict_comp]

/-- **The Leibniz rule for composition**, at the level of cochains: the differential of a
composite is the composite with the differential of the outer factor, plus the composite with
the differential of the inner factor up to the sign `(-1)^p`. -/
lemma compositionCochain_δ (U : X.C) (p q n n' : ℤ) (hn : p + q = n) (hn' : n + 1 = n')
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    δ n n' (compositionCochain X U p q n hn β γ) =
      compositionCochain X U (p + 1) q n' (by omega)
          (((sheafHomComplex X L M).obj.d p (p + 1)).val.app (op U) β) γ +
        p.negOnePow • compositionCochain X U p (q + 1) n' (by omega) β
          (((sheafHomComplex X K L).obj.d q (q + 1)).val.app (op U) γ) := by
  rw [compositionCochain, compositionCochain, compositionCochain,
    (sheafHomComplex X L M).sectionsEquiv_d, (sheafHomComplex X K L).sectionsEquiv_d]
  exact δ_comp _ _ _ (q + 1) (p + 1) n' hn' rfl rfl

/-- **The Leibniz rule for composition.** The differential of a composite section is the
composite with the differential of the outer factor, plus the composite with the differential of
the inner factor up to the sign `(-1)^p`. -/
lemma compositionSection_d (U : X.C) (p q n n' : ℤ) (hn : p + q = n) (hn' : n + 1 = n')
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    ((sheafHomComplex X K M).obj.d n n').val.app (op U)
        (compositionSection X U p q n hn β γ) =
      compositionSection X U (p + 1) q n' (by omega)
          (((sheafHomComplex X L M).obj.d p (p + 1)).val.app (op U) β) γ +
        p.negOnePow • compositionSection X U p (q + 1) n' (by omega) β
          (((sheafHomComplex X K L).obj.d q (q + 1)).val.app (op U) γ) := by
  refine ((sheafHomComplex X K M).sectionsEquiv U n').injective ?_
  rw [(sheafHomComplex X K M).sectionsEquiv_d, compositionSection_cochain,
    compositionCochain_δ X U p q n n' hn hn' β γ, map_add, compositionSection_cochain]
  simp only [Units.smul_def]
  rw [map_zsmul, compositionSection_cochain]

/-- Composition of homogeneous local sections, as a morphism out of the degreewise tensor
product of the underlying presheaves of modules of the two internal Hom complexes. -/
noncomputable def compositionTensorMap (p q n : ℤ) (hn : p + q = n) :
    (underlyingPresheafComplex X (sheafHomComplex X L M).obj).X p ⊗
        (underlyingPresheafComplex X (sheafHomComplex X K L).obj).X q ⟶
      (underlyingPresheafComplex X (sheafHomComplex X K M).obj).X n where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun β γ ↦ compositionSection X U.unop p q n hn β γ)
    (fun β β' γ ↦ compositionSection_add_left X U.unop p q n hn β β' γ)
    (fun c β γ ↦ compositionSection_smul_left X U.unop p q n hn c β γ)
    (fun β γ γ' ↦ compositionSection_add_right X U.unop p q n hn β γ γ')
    (fun c β γ ↦ compositionSection_smul_right X U.unop p q n hn c β γ)
  naturality {U V} f := ModuleCat.MonoidalCategory.tensor_ext fun β γ ↦
    (compositionSection_restrict X U.unop V.unop f.unop p q n hn β γ).symm

/-- `compositionTensorMap` sends a local pure tensor of homogeneous sections to their
composite. -/
lemma compositionTensorMap_tmul (p q n : ℤ) (hn : p + q = n) (U : X.Cᵒᵖ)
    (β : ((underlyingPresheafComplex X (sheafHomComplex X L M).obj).X p).obj U)
    (γ : ((underlyingPresheafComplex X (sheafHomComplex X K L).obj).X q).obj U) :
    (compositionTensorMap X p q n hn).app U
        (β ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] γ) =
      compositionSection X U.unop p q n hn β γ := rfl

end Sections

section Morphism

variable
  (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The presheaf-level source of the composition morphism: the total complex of the double
complex of pointwise tensor products of the underlying presheaves of the two internal Hom
complexes. -/
noncomputable abbrev compositionPresheafSource :
    CochainComplex (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) ℤ :=
  tensorTotalPresheaf X (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj

/-- The degree-`n` component of the presheaf-level composition morphism, assembled from the
degreewise composition maps on the summands of the total complex. -/
noncomputable def compositionPresheafDegree (n : ℤ) :
    (compositionPresheafSource X K L M).X n ⟶
      (underlyingPresheafComplex X (sheafHomComplex X K M).obj).X n :=
  HomologicalComplex.mapBifunctorDesc fun p q h ↦ compositionTensorMap X p q n (by simpa using h)

/-- `compositionPresheafDegree` restricts to `compositionTensorMap` on each summand. -/
lemma ι_compositionPresheafDegree (p q n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιMapBifunctor
          (underlyingPresheafComplex X (sheafHomComplex X L M).obj)
          (underlyingPresheafComplex X (sheafHomComplex X K L).obj)
          (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
          (ComplexShape.up ℤ) p q n h ≫
        compositionPresheafDegree X K L M n =
      compositionTensorMap X p q n (by simpa using h) :=
  HomologicalComplex.ι_mapBifunctorDesc _ p q h

/-- The presheaf-level composition morphism. -/
noncomputable def compositionPresheafMap :
    compositionPresheafSource X K L M ⟶
      underlyingPresheafComplex X (sheafHomComplex X K M).obj where
  f n := compositionPresheafDegree X K L M n
  comm' n n' hnn := by
    obtain rfl : n + 1 = n' := hnn
    refine HomologicalComplex.mapBifunctor.hom_ext fun p q hpq ↦ ?_
    have hpq' : p + q = n := by simpa using hpq
    rw [← Category.assoc, ι_compositionPresheafDegree, ← Category.assoc,
      HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (ComplexShape.up_mk p (p + 1) rfl) q (n + 1)
        (show p + 1 + q = n + 1 by omega),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p (ComplexShape.up_mk q (q + 1) rfl) (n + 1)
        (show p + (q + 1) = n + 1 by omega),
      Preadditive.add_comp, Linear.units_smul_comp, Linear.units_smul_comp, Category.assoc,
      Category.assoc, ι_compositionPresheafDegree, ι_compositionPresheafDegree]
    have hε₁ : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (p, q) = 1 := rfl
    have hε₂ : ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (p, q) = p.negOnePow := rfl
    rw [hε₁, hε₂, one_smul]
    refine PresheafOfModules.hom_ext fun U ↦ ?_
    refine ModuleCat.MonoidalCategory.tensor_ext fun β γ ↦ ?_
    simp only [PresheafOfModules.comp_app, PresheafOfModules.add_app, Units.smul_def,
      PresheafOfModules.zsmul_app]
    exact compositionSection_d X U.unop p q n (n + 1) hpq' rfl β γ

/-- `compositionPresheafMap` sends a local pure tensor of homogeneous sections, included into
the total complex, to their composite. -/
lemma compositionPresheafMap_tmul (p q n : ℤ) (hn : p + q = n) (U : X.C)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    ModuleCat.Hom.hom (((compositionPresheafMap X K L M).f n).app (op U))
        ((HomologicalComplex.ιMapBifunctor
          (underlyingPresheafComplex X (sheafHomComplex X L M).obj)
          (underlyingPresheafComplex X (sheafHomComplex X K L).obj)
          (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
          (ComplexShape.up ℤ) p q n (by simpa using hn)).app (op U)
            (β ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] γ)) =
      compositionSection X U p q n hn β γ :=
  (congrArg (fun f ↦ ModuleCat.Hom.hom (f.app (op U))
      (β ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] γ))
    (ι_compositionPresheafDegree X K L M p q n (by simpa using hn))).trans
      (compositionTensorMap_tmul X p q n hn (op U) β γ)

/-- **The composition morphism of internal Hom complexes** of Stacks 0A91:

`Tot(SheafHom(L, M) ⊗_O SheafHom(K, L)) ⟶ SheafHom(K, M)`.

It is the morphism out of the degreewise sheafification determined by the presheaf-level
composition morphism. -/
noncomputable def compositionMap :
    tensorTotal X (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj ⟶
      (sheafHomComplex X K M).obj :=
  sheafifyLift X (compositionPresheafMap X K L M)

/-- The characterisation of `compositionMap`: it sends the homogeneous local pure tensor of a
degree-`p` section `β` of `SheafHom(L, M)` and a degree-`q` section `γ` of `SheafHom(K, L)` to
their composite, with no extra sign. -/
lemma compositionMap_tensorTotalSection (U : X.C) (p q : ℤ)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    ((compositionMap X K L M).f (p + q)).val.app (op U)
        (tensorTotalSection X (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj U p q
          β γ) =
      compositionSection X U p q (p + q) rfl β γ :=
  (sheafifyLift_unit_apply X (compositionPresheafMap X K L M) (p + q) (op U) _).trans
    (compositionPresheafMap_tmul X K L M p q (p + q) rfl U β γ)

end Morphism

/-- A composition morphism of internal Hom complexes, characterised by its action on every
homogeneous local pure tensor: the pure tensor of a degree-`p` section of `SheafHom(L, M)` and
a degree-`q` section of `SheafHom(K, L)` is sent to their ordinary composite, with no extra
sign. -/
structure CompositionConstruction where
  /-- The morphism of complexes of `O`-modules induced by composition. -/
  comp (K L M :
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    tensorTotal X (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj ⟶
      (sheafHomComplex X K M).obj
  /-- Homogeneous local pure tensors act by composition, with no additional sign. -/
  comp_tmul : ∀ (K L M :
        CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (U : X.C) (p q r s : ℤ) (hrs : r + q = s) (hsp : s + p = r + q + p)
      (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
      (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U))
      (x : (K.X r).val.obj (op U)),
    applyHomSection X (sheafHomComplex X K M) U (p + q) r (r + q + p) (by omega)
        (((comp K L M).f (p + q)).val.app (op U)
          (tensorTotalSection X (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj U p q
            β γ)) x =
      applyHomSection X (sheafHomComplex X L M) U p s (r + q + p) hsp β
        (applyHomSection X (sheafHomComplex X K L) U q r s hrs γ x)

/-- **Stacks 0A91.** For complexes `K`, `L`, `M` of modules on a ringed site there is a
canonical morphism of complexes of `O`-modules

`Tot(SheafHom(L, M) ⊗_O SheafHom(K, L)) ⟶ SheafHom(K, M)`,

namely the one sending each homogeneous local pure tensor to the composite of its two factors,
with no extra sign.

A ringed space is a ringed site, namely the site of its opens with the open-cover topology, so
this also gives the composition morphism for complexes of modules on a ringed space. -/
@[stacks 0A91, stacks 0A8N "the ringed space case"]
noncomputable def compositionConstruction : CompositionConstruction X where
  comp K L M := compositionMap X K L M
  comp_tmul K L M U p q r s hrs hsp β γ x := by
    rw [compositionMap_tensorTotalSection]
    exact compositionSection_apply X U p q (p + q) r s (r + q + p) rfl hrs hsp β γ x

end AlgebraicGeometry.RingedSite

end
