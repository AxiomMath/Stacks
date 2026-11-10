module

public import StacksFrontier.Deformation.AlgebraExtension.NaiveCotangentExt

/-!
# Pushout of extensions along a map of modules: full faithfulness

Let `a : 𝒜 ⟶ 𝒪` be a morphism of sheaves of commutative rings on a small site and let
`φ : ℳ ⟶ 𝒩` be a morphism of `𝒪`-modules. *Pushout along `φ`* is a functor
`F` from extensions of `𝒜`-algebras of `𝒪` by `ℳ` to extensions by `𝒩`, characterised by a
morphism of extensions `P ⟶ F(P)` along `φ`, natural in `P`, through which every morphism of
extensions out of `P` along `φ` factors uniquely. This is the functor `F` of the situation
preceding [Stacks Project, Tag 0D3P].

This file proves the fully faithful half of that tag at the level of a site: if `φ` induces an
isomorphism on `Ext⁰(NL_{𝒪/𝒜}, −)` and an injection on `Ext¹(NL_{𝒪/𝒜}, −)`, then `F` is fully
faithful. The argument is the source's (via [Stacks Project, Tag 08UG]): two extensions are
compared on the generators `ℰ = 𝒪'₁ ×_𝒪 𝒪'₂`, which lift to both; the obstruction to a morphism
is the class of the difference `δ₁ - δ₂ : ℐ/ℐ² ⟶ ℳ` of the two conormal maps, and the
morphisms, when they exist, form a torsor under the morphisms `Ω ⟶ ℳ` killing `ℐ/ℐ²`.

## Main definitions

* `Deformation.AlgebraExtension.fibreGenerators`: the generators `𝒪'₁ ×_𝒪 𝒪'₂`.

## Main results

* `Deformation.AlgebraExtension.IsPushoutFunctor.faithful`
* `Deformation.AlgebraExtension.IsPushoutFunctor.full`

## References

* [Stacks Project, Tag 0D3P](https://stacks.math.columbia.edu/tag/0D3P)
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.Differentials (underlyingRingSheaf)
open Stacks.Sites.Conormal (kernelIdeal)
open Stacks.Sites.FreeAlgebra
open Stacks.SheafOfModules (presentation presentationConormalSequence naiveCotangentComplex)

universe t u

namespace Deformation.AlgebraExtension

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasWeakSheafify J CommRingCat.{u}]
  {A O : Sheaf J CommRingCat.{u}} {a : A ⟶ O}
  {M N : SheafOfModules.{u} (underlyingRingSheaf O)}

/-! ### The generators `𝒪'₁ ×_𝒪 𝒪'₂` -/

section Fibre

variable (P : AlgebraExtension a M) (Q : AlgebraExtension a N)

/-- The presheaf of sets `𝒪'_P ×_𝒪 𝒪'_Q`. -/
noncomputable def fibreGenerators : Cᵒᵖ ⥤ Type u where
  obj U := {p : P.extension.obj.obj U × Q.extension.obj.obj U //
    P.reduction.hom.app U p.1 = Q.reduction.hom.app U p.2}
  map {U V} f := TypeCat.ofHom fun p => ⟨(P.extension.obj.map f p.1.1, Q.extension.obj.map f p.1.2),
    by rw [NatTrans.naturality_apply P.reduction.hom f, NatTrans.naturality_apply Q.reduction.hom f,
      p.2]⟩
  map_id U := by
    ext p
    · change (P.extension.obj.map (𝟙 U)).hom p.1.1 = p.1.1
      rw [CategoryTheory.Functor.map_id]
      rfl
    · change (Q.extension.obj.map (𝟙 U)).hom p.1.2 = p.1.2
      rw [CategoryTheory.Functor.map_id]
      rfl
  map_comp f g := by
    ext p
    · change (P.extension.obj.map (f ≫ g)).hom p.1.1 = _
      rw [CategoryTheory.Functor.map_comp]
      rfl
    · change (Q.extension.obj.map (f ≫ g)).hom p.1.2 = _
      rw [CategoryTheory.Functor.map_comp]
      rfl

/-- The map `𝒪'_P ×_𝒪 𝒪'_Q ⟶ 𝒪`. -/
noncomputable def fibreMap : fibreGenerators P Q ⟶ underlyingPresheaf J O where
  app U := TypeCat.ofHom fun p => P.reduction.hom.app U p.1.1
  naturality U V f := by
    ext p
    exact NatTrans.naturality_apply P.reduction.hom f p.1.1

/-- The first projection, a lift of the generators to `P`. -/
noncomputable def fibreFst : GeneratorLift (fibreMap P Q) P where
  lift :=
    { app := fun _ => TypeCat.ofHom fun p => p.1.1
      naturality := fun _ _ _ => rfl }
  lift_comp := rfl

/-- The second projection, a lift of the generators to `Q`. -/
noncomputable def fibreSnd : GeneratorLift (fibreMap P Q) Q where
  lift :=
    { app := fun U => TypeCat.ofHom fun p => p.1.2
      naturality := fun _ _ _ => rfl }
  lift_comp := by
    ext U p
    exact p.2.symm

omit [HasWeakSheafify J CommRingCat.{u}] in
/-- The map `𝒪'_P ×_𝒪 𝒪'_Q ⟶ 𝒪` is locally surjective. -/
theorem isLocallySurjective_fibreMap :
    Presheaf.IsLocallySurjective J (fibreMap P Q) := by
  have hP := (Presheaf.isLocallySurjective_iff_whisker_forget J P.reduction.hom).1
    P.locallySurjective
  have hQ := Q.locallySurjective
  have hfst : Presheaf.IsLocallySurjective J (fibreFst P Q).lift := ⟨fun {U} x => by
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J Q.reduction.hom
      (P.reduction.hom.app (op U) x))
    rintro Y f ⟨y, hy⟩
    refine ⟨⟨(P.extension.obj.map f.op x, y), ?_⟩, rfl⟩
    exact (NatTrans.naturality_apply P.reduction.hom f.op x).trans hy.symm⟩
  rw [show fibreMap P Q = (fibreFst P Q).lift ≫
      Functor.whiskerRight P.reduction.hom (forget CommRingCat.{u}) from rfl]
  infer_instance

/-- The presentation of `𝒪` on the generators `𝒪'_P ×_𝒪 𝒪'_Q` is locally surjective. -/
instance isLocallySurjective_presentation_fibreMap :
    Presheaf.IsLocallySurjective J
      (presentation J A O a (fibreGenerators P Q) (fibreMap P Q)).hom :=
  haveI := isLocallySurjective_fibreMap P Q
  (Presheaf.isLocallySurjective_iff_whisker_forget J _).mpr
    (Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
      (freeAlgebraSheafVariable_comp_desc J A O (fibreGenerators P Q) a (fibreMap P Q)))

end Fibre

/-! ### Full faithfulness -/

section FullyFaithful

/-- If one lift is the shift of another by `θ`, then `d ≫ θ` is the difference of their
conormal maps. -/
private theorem presentationConormalSequence_f_comp_eq_sub {E : Cᵒᵖ ⥤ Type u}
    {α : E ⟶ underlyingPresheaf J O} [Presheaf.IsLocallySurjective J (presentation J A O a E α).hom]
    {P : AlgebraExtension a M} {β₁ β₂ : GeneratorLift α P}
    {θ : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₂ ⟶ tensorModule M}
    (h : β₂ = β₁.shift θ) :
    (presentationConormalSequence.{u, u, u, u} J A O a E α).f ≫ θ =
      β₂.conormalHom - β₁.conormalHom := by
  rw [h, GeneratorLift.conormalHom_shift, add_sub_cancel_left]

variable [J.WEqualsLocallyBijective CommRingCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms]
  [HasDerivedCategory.{t} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  {φ : M ⟶ N} {F : AlgebraExtension a M ⥤ AlgebraExtension a N}

omit [J.WEqualsLocallyBijective CommRingCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms]
  [HasDerivedCategory.{t} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))] in
/-- Two lifts of the generators with the same conormal map agree on the relations. -/
theorem GeneratorLift.restriction_eq_of_conormalHom_eq {E : Cᵒᵖ ⥤ Type u}
    {α : E ⟶ underlyingPresheaf J O} [Presheaf.IsLocallySurjective J (presentation J A O a E α).hom]
    {P₁ P₂ : AlgebraExtension a M} {β₁ : GeneratorLift α P₁} {β₂ : GeneratorLift α P₂}
    (h : β₁.conormalHom = β₂.conormalHom) (U : Cᵒᵖ)
    (g : kernelIdeal (presentation J A O a E α).hom U) :
    β₁.restriction U g = β₂.restriction U g :=
  (β₁.conormalHom_relClass U g).symm.trans
    ((congrArg (fun f => f.val.app U (GeneratorLift.relClass U g)) h).trans
      (β₂.conormalHom_relClass U g))

namespace IsPushoutFunctor

variable (hF : IsPushoutFunctor φ F)
include hF

omit [HasWeakSheafify J CommRingCat.{u}] [J.WEqualsLocallyBijective CommRingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms]
  [HasDerivedCategory.{t} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))] in
/-- The naturality of `ι`, as an equality of morphisms of extensions along `φ`. -/
theorem comp_ι {P P' : AlgebraExtension a M} (k : P ⟶ P') :
    MapAlong.comp k (hF.ι P') (Category.id_comp φ) =
      MapAlong.comp (hF.ι P) (F.map k) (Category.comp_id φ) :=
  MapAlong.ext (hF.naturality k).symm

omit [J.HasSheafCompose (forget CommRingCat.{u})] [(forget CommRingCat.{u}).ReflectsIsomorphisms] in
/-- **Pushout along `φ` is faithful** as soon as `φ` induces an injection on
`Ext⁰(NL_{𝒪/𝒜}, −)`. -/
theorem faithful
    (h0 : Function.Injective (fun ξ : DerivedCategory.Q.obj
        (naiveCotangentComplex.{u, u, u, u} J A O a) ⟶ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).obj (tensorModule M) =>
      ξ ≫ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).map (tensorMap φ))) :
    F.Faithful where
  map_injective {P P'} k₁ k₂ hk := by
    let β := fibreFst P P
    obtain ⟨θ, hθ⟩ := (β.comp k₁).exists_eq_shift (β.comp k₂)
    have hd : (presentationConormalSequence.{u, u, u, u} J A O a _ (fibreMap P P)).f ≫ θ = 0 := by
      rw [presentationConormalSequence_f_comp_eq_sub hθ, GeneratorLift.conormalHom_comp,
        GeneratorLift.conormalHom_comp, sub_self]
    have h2 : (β.comp k₂).comp (hF.ι P') = (β.comp k₁).comp (hF.ι P') := by
      change β.comp (MapAlong.comp k₂ (hF.ι P') (Category.id_comp φ)) =
        β.comp (MapAlong.comp k₁ (hF.ι P') (Category.id_comp φ))
      rw [hF.comp_ι, hF.comp_ι, hk]
    have hφ : θ ≫ tensorMap φ = 0 := by
      have h1 : (β.comp k₂).comp (hF.ι P') =
          ((β.comp k₁).comp (hF.ι P')).shift (θ ≫ tensorMap φ) := by
        rw [hθ, GeneratorLift.shift_comp]
      exact (GeneratorLift.shift_injective _
        (((β.comp k₁).comp (hF.ι P')).shift_zero.trans (h2.symm.trans h1))).symm
    rw [eq_zero_of_naiveCotangent_injective φ h0 θ hd hφ, GeneratorLift.shift_zero] at hθ
    exact MapAlong.ext_of_comp β hθ.symm

/-- **Pushout along `φ` is full** as soon as `φ` induces a surjection on `Ext⁰(NL_{𝒪/𝒜}, −)`
and an injection on `Ext¹(NL_{𝒪/𝒜}, −)`. -/
theorem full
    (h0 : Function.Surjective (fun ξ : DerivedCategory.Q.obj
        (naiveCotangentComplex.{u, u, u, u} J A O a) ⟶ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).obj (tensorModule M) =>
      ξ ≫ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).map (tensorMap φ)))
    (h1 : Function.Injective (fun ξ : DerivedCategory.Q.obj
        (naiveCotangentComplex.{u, u, u, u} J A O a) ⟶ ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).obj
          (tensorModule M))⟦(1 : ℤ)⟧ =>
      ξ ≫ ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).map
          (tensorMap φ))⟦(1 : ℤ)⟧')) :
    F.Full where
  map_surjective {P P'} g := by
    let β := fibreFst P P'
    let β' := fibreSnd P P'
    let h : MapAlong φ P (F.obj P') := MapAlong.comp (hF.ι P) g (Category.comp_id φ)
    obtain ⟨θ₁, hθ₁⟩ := (β'.comp (hF.ι P')).exists_eq_shift (β.comp h)
    have e1 : (presentationConormalSequence.{u, u, u, u} J A O a _ (fibreMap P P')).f ≫ θ₁ =
        (β.conormalHom - β'.conormalHom) ≫ tensorMap φ := by
      rw [presentationConormalSequence_f_comp_eq_sub hθ₁, GeneratorLift.conormalHom_comp,
        GeneratorLift.conormalHom_comp, Preadditive.sub_comp]
    obtain ⟨θ₀, hθ₀⟩ := exists_d_comp_eq_of_naiveCotangent_injective φ h1 _ ⟨θ₁, e1⟩
    have e2 : (presentationConormalSequence.{u, u, u, u} J A O a _ (fibreMap P P')).f ≫
        (θ₁ - θ₀ ≫ tensorMap φ) = 0 := by
      rw [Preadditive.comp_sub, e1, ← Category.assoc, hθ₀, sub_self]
    obtain ⟨θ₃, hθ₃, hθ₃φ⟩ := exists_comp_eq_of_naiveCotangent_surjective φ h0 _ e2
    have hc : (β'.shift (θ₀ + θ₃)).conormalHom = β.conormalHom := by
      rw [GeneratorLift.conormalHom_shift, Preadditive.comp_add, hθ₀, hθ₃, add_zero,
        add_sub_cancel]
    obtain ⟨k, hk⟩ := GeneratorLift.exists_hom_comp_eq β (β'.shift (θ₀ + θ₃))
      (GeneratorLift.restriction_eq_of_conormalHom_eq hc)
    refine ⟨k, ?_⟩
    have hkj : MapAlong.comp k (hF.ι P') (Category.id_comp φ) = h := MapAlong.ext_of_comp β (by
      change (β.comp k).comp (hF.ι P') = β.comp h
      rw [hk, GeneratorLift.shift_comp, hθ₁]
      congr 1
      rw [Preadditive.add_comp, hθ₃φ]
      abel)
    obtain ⟨_, -, huniq⟩ := hF.desc_unique P (F.obj P') h
    have e3 : (hF.ι P).hom ≫ (F.map k).hom = h.hom := by
      rw [hF.naturality]
      exact congrArg MapAlong.hom hkj
    exact (huniq _ e3).trans (huniq g rfl).symm

end IsPushoutFunctor

end FullyFaithful

end Deformation.AlgebraExtension

end
