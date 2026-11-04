module

public import StacksFrontier.Deformation.AlgebraExtension.PushoutEssSurj
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraMapLocallySurjective

/-!
# The class of an extension of algebras in `Ext¹(NL_{𝒪/𝒜}, ℳ)`

Let `a : 𝒜 ⟶ 𝒪` be a morphism of sheaves of commutative rings on a small site and let `ℳ` be an
`𝒪`-module. Every extension of `𝒜`-algebras

`0 ⟶ ℳ ⟶ 𝒪' ⟶ 𝒪 ⟶ 0`

with `ℳ` an ideal of square zero has a class in `Ext¹_𝒪(NL_{𝒪/𝒜}, ℳ)`: present `𝒪` by any
family of generators `α : ℰ ⟶ 𝒪` which lifts to `𝒪'`, take the conormal map `ℐ/ℐ² ⟶ ℳ` of the
lift, and read its class in `Ext¹(NL(α), ℳ)` through the quasi-isomorphism
`NL(α) ≅ NL_{𝒪/𝒜}` of [Stacks Project, Tag 08TY]. The class does not depend on the presentation
or on the lift. This is the canonical bijection of [Stacks Project, Tag 0GQ5] between the
isomorphism classes of such extensions and `Ext¹_𝒪(NL_{𝒪/𝒜}, ℳ)`, which is proved here in full:
the class is invariant under isomorphism, injective on isomorphism classes, and every class is
attained.

The class is moreover natural in `ℳ`: a morphism of extensions along `φ : ℳ ⟶ 𝒩` carries the
class of the source to the class of the target pushed along `φ`.

## Main definitions

* `Deformation.AlgebraExtension.extClass`: the class of an extension.
* `Deformation.AlgebraExtension.extClassEquiv`: the bijection of [Stacks Project, Tag 0GQ5].

## Main results

* `Deformation.AlgebraExtension.extClass_eq_of_lift`: the class computed on any presentation
  with a lift.
* `Deformation.AlgebraExtension.extClass_mapAlong`: naturality in the module.
* `Deformation.AlgebraExtension.nonempty_iso_of_extClass_eq`: injectivity on isomorphism
  classes.
* `Deformation.AlgebraExtension.exists_extClass_eq`: surjectivity.

## Implementation notes

The source states [Stacks Project, Tag 0GQ5] for `𝒜 = f⁻¹𝒪_ℬ` attached to a morphism of ringed
topoi `f`; nothing about `f` is used beyond the ring map `f⁻¹𝒪_ℬ ⟶ 𝒪`, so the statement here is
for an arbitrary morphism `a : 𝒜 ⟶ 𝒪` of sheaves of commutative rings on a small site.

The class is *defined* on the generators `ℰ = 𝒪'` of the extension itself
(`Deformation.AlgebraExtension.fibreGenerators P P`), which always lift, so that no choice is
made; `Deformation.AlgebraExtension.extClass_eq_of_lift` then computes it on any other
presentation with a lift, by comparing both with the fibre product of the two presentations.

## References

* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.Differentials (underlyingRingSheaf)
open Stacks.Sites.FreeAlgebra
open Stacks.SheafOfModules (presentation presentationConormalSequence naiveCotangentComplex
  presentationConormalMap)

universe t u

namespace Deformation.AlgebraExtension

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasWeakSheafify J CommRingCat.{u}]
  [J.WEqualsLocallyBijective CommRingCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms]
  {A O : Sheaf J CommRingCat.{u}} {a : A ⟶ O}
  [HasDerivedCategory.{t} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  {M N : SheafOfModules.{u} (underlyingRingSheaf O)}

variable (a) in
/-- The target `Ext¹(NL_{𝒪/𝒜}, ℳ) = Hom(NL_{𝒪/𝒜}, ℳ[1])` of the class of an extension by `ℳ`,
in the derived category of `𝒪`-modules. -/
abbrev ExtOne (M : SheafOfModules.{u} (underlyingRingSheaf O)) : Type _ :=
  DerivedCategory.Q.obj (naiveCotangentComplex.{u, u, u, u} J A O a) ⟶
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).obj
        (tensorModule M))⟦(1 : ℤ)⟧

/-- The map `Ext¹(NL_{𝒪/𝒜}, ℳ) ⟶ Ext¹(NL_{𝒪/𝒜}, 𝒩)` induced by `φ : ℳ ⟶ 𝒩`. -/
noncomputable abbrev extOneMap (φ : M ⟶ N) (ξ : ExtOne a M) : ExtOne a N :=
  ξ ≫ ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).map
      (tensorMap φ))⟦(1 : ℤ)⟧'

/-- The class in `Ext¹(NL_{𝒪/𝒜}, ℳ)` of a lift `β` of a presentation `α` to an extension: the
class of its conormal map `ℐ/ℐ² ⟶ ℳ` in `Ext¹(NL(α), ℳ)`, read through `NL(α) ≅ NL_{𝒪/𝒜}`. -/
noncomputable def liftClass {E : Cᵒᵖ ⥤ Type u} {α : E ⟶ underlyingPresheaf J O}
    [Presheaf.IsLocallySurjective J (presentation J A O a E α).hom] {P : AlgebraExtension a M}
    (β : GeneratorLift α P) : ExtOne a M :=
  (presentationTwoTermIso a E α).inv ≫
    (presentationTwoTerm a E α).conormalExtClass _ β.conormalHom

omit [J.HasSheafCompose (forget CommRingCat)] [(forget CommRingCat).ReflectsIsomorphisms] in
/-- Two lifts of the same presentation have the same class: they differ by a shift `θ`, which
changes the conormal map by `θ ∘ d`. -/
theorem liftClass_eq_liftClass {E : Cᵒᵖ ⥤ Type u} {α : E ⟶ underlyingPresheaf J O}
    [Presheaf.IsLocallySurjective J (presentation J A O a E α).hom] {P : AlgebraExtension a M}
    (β β' : GeneratorLift α P) : liftClass β = liftClass β' := by
  obtain ⟨θ, rfl⟩ := β.exists_eq_shift β'
  have h0 : (presentationTwoTerm a E α).conormalExtClass (tensorModule M)
      ((presentationConormalSequence.{u, u, u, u} J A O a E α).f ≫ θ) = 0 :=
    ((presentationTwoTerm a E α).conormalExtClass_eq_zero_iff _ _).2 ⟨θ, rfl⟩
  have hsub : (presentationTwoTerm a E α).conormalExtClass (tensorModule M)
      (β.shift θ).conormalHom - (presentationTwoTerm a E α).conormalExtClass (tensorModule M)
      β.conormalHom = 0 :=
    (conormalExtClass_sub (tensorModule M) _ _).symm.trans
      ((congrArg ((presentationTwoTerm a E α).conormalExtClass (tensorModule M))
        ((congrArg (· - β.conormalHom) (GeneratorLift.conormalHom_shift β θ)).trans
          (add_sub_cancel_left _ _))).trans h0)
  exact congrArg ((presentationTwoTermIso a E α).inv ≫ ·) (eq_of_sub_eq_zero hsub).symm

omit [J.HasSheafCompose (forget CommRingCat)] [(forget CommRingCat).ReflectsIsomorphisms] in
/-- The class of a lift is unchanged by precomposing with a morphism of presentations. -/
theorem liftClass_precomp {E₁ E₂ : Cᵒᵖ ⥤ Type u} (h : E₁ ⟶ E₂)
    {α₁ : E₁ ⟶ underlyingPresheaf J O} {α₂ : E₂ ⟶ underlyingPresheaf J O} (hα : h ≫ α₂ = α₁)
    [Presheaf.IsLocallySurjective J (presentation J A O a E₁ α₁).hom]
    [Presheaf.IsLocallySurjective J (presentation J A O a E₂ α₂).hom] {P : AlgebraExtension a M}
    (β : GeneratorLift α₂ P) : liftClass (β.precomp h hα) = liftClass β := by
  have hc : DerivedCategory.Q.map (Stacks.SheafOfModules.presentationNaiveCotangentComplexMap.{u,
      u, u, u} J A E₁ E₂ h O a α₁ α₂ hα) ≫ (presentationTwoTermIso a E₂ α₂).hom =
      (presentationTwoTermIso a E₁ α₁).hom :=
    (DerivedCategory.Q.map_comp _ _).symm.trans (congrArg DerivedCategory.Q.map
      (Stacks.SheafOfModules.naiveCotangentComplexComparison_naturality (J := J) (A := A)
        (B := O) (a := a) (h := h) (hα := hα)))
  calc liftClass (β.precomp h hα)
      = (presentationTwoTermIso a E₁ α₁).inv ≫
          (presentationTwoTerm a E₁ α₁).conormalExtClass (tensorModule M)
            (presentationConormalMap.{u, u, u, u} J A E₁ E₂ h O a α₁ α₂ hα ≫
              β.conormalHom) :=
        by rw [liftClass, GeneratorLift.conormalHom_precomp]; rfl
    _ = (presentationTwoTermIso a E₁ α₁).inv ≫ (DerivedCategory.Q.map
          (Stacks.SheafOfModules.presentationNaiveCotangentComplexMap.{u, u, u, u} J A E₁ E₂ h O a
            α₁ α₂ hα) ≫ (presentationTwoTerm a E₂ α₂).conormalExtClass (tensorModule M)
              β.conormalHom) :=
        congrArg ((presentationTwoTermIso a E₁ α₁).inv ≫ ·)
          (conormalExtClass_naturality (tensorModule M) h hα β.conormalHom).symm
    _ = liftClass β :=
        (congrArg (fun X => (presentationTwoTermIso a E₁ α₁).inv ≫ DerivedCategory.Q.map
            (Stacks.SheafOfModules.presentationNaiveCotangentComplexMap.{u, u, u, u} J A E₁ E₂ h O
              a α₁ α₂ hα) ≫ X)
          ((presentationTwoTermIso a E₂ α₂).hom_inv_id_assoc _).symm).trans
        ((congrArg ((presentationTwoTermIso a E₁ α₁).inv ≫ ·)
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hc))).trans
          ((presentationTwoTermIso a E₁ α₁).inv_hom_id_assoc _))

omit [J.HasSheafCompose (forget CommRingCat)] [(forget CommRingCat).ReflectsIsomorphisms] in
/-- Any two presentations with lifts to the same extension give the same class: both are
compared with the fibre product of the two presentations. -/
theorem liftClass_eq_of_lifts {E₁ E₂ : Cᵒᵖ ⥤ Type u} {α₁ : E₁ ⟶ underlyingPresheaf J O}
    {α₂ : E₂ ⟶ underlyingPresheaf J O}
    [Presheaf.IsLocallySurjective J (presentation J A O a E₁ α₁).hom]
    [Presheaf.IsLocallySurjective J (presentation J A O a E₂ α₂).hom]
    [Presheaf.IsLocallySurjective J α₂] {P : AlgebraExtension a M}
    (β₁ : GeneratorLift α₁ P) (β₂ : GeneratorLift α₂ P) : liftClass β₁ = liftClass β₂ := by
  have := isLocallySurjective_fibrePresentationFst (J := J) α₁ α₂
  have : Presheaf.IsLocallySurjective J (presentation J A O a (fibrePresentation α₁ α₂)
      (fibrePresentationFst α₁ α₂ ≫ α₁)).hom :=
    Stacks.Sites.FreeAlgebra.isLocallySurjective_presentation_comp (J := J) (A := A) (h := _)
      (a := a) (α := α₁)
  rw [← liftClass_precomp (fibrePresentationFst α₁ α₂) rfl β₁,
    ← liftClass_precomp (fibrePresentationSnd α₁ α₂) (fibrePresentation_condition α₁ α₂) β₂]
  exact liftClass_eq_liftClass _ _

/-- **The class of an extension** `0 ⟶ ℳ ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` of `𝒜`-algebras in
`Ext¹(NL_{𝒪/𝒜}, ℳ)`, computed on the generators `ℰ = 𝒪'` of the extension itself. -/
noncomputable def extClass (P : AlgebraExtension a M) : ExtOne a M :=
  haveI := isLocallySurjective_fibreMap P P
  liftClass (fibreFst P P)

omit [J.HasSheafCompose (forget CommRingCat)] [(forget CommRingCat).ReflectsIsomorphisms] in
/-- **The class of an extension computed on any presentation which lifts to it.** -/
theorem extClass_eq_of_lift {E : Cᵒᵖ ⥤ Type u} {α : E ⟶ underlyingPresheaf J O}
    [Presheaf.IsLocallySurjective J (presentation J A O a E α).hom] {P : AlgebraExtension a M}
    (β : GeneratorLift α P) : extClass P = liftClass β := by
  have := isLocallySurjective_fibreMap P P
  exact (liftClass_eq_of_lifts β (fibreFst P P)).symm

omit [J.HasSheafCompose (forget CommRingCat)] [(forget CommRingCat).ReflectsIsomorphisms] in
/-- **Naturality of the class in the module.** A morphism of extensions along `φ : ℳ ⟶ 𝒩`
carries the class of its source to the class of its target. -/
theorem extClass_mapAlong {φ : M ⟶ N} {P : AlgebraExtension a M} {Q : AlgebraExtension a N}
    (k : MapAlong φ P Q) : extClass Q = extOneMap φ (extClass P) := by
  have := isLocallySurjective_fibreMap P P
  refine (extClass_eq_of_lift ((fibreFst P P).comp k)).trans ?_
  exact (by rw [liftClass, GeneratorLift.conormalHom_comp]; rfl : liftClass _ = _).trans
    ((congrArg ((presentationTwoTermIso a _ _).inv ≫ ·)
      (conormalExtClass_comp (tensorModule M) (fibreFst P P).conormalHom (tensorMap φ)).symm).trans
      (Category.assoc _ _ _).symm)

omit [J.HasSheafCompose (forget CommRingCat)] [(forget CommRingCat).ReflectsIsomorphisms] in
/-- Isomorphic extensions have the same class. -/
theorem extClass_eq_of_iso {P Q : AlgebraExtension a M} (e : P ≅ Q) :
    extClass P = extClass Q := by
  have h1 : ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).map
        (tensorMap (𝟙 M)))⟦(1 : ℤ)⟧' = 𝟙 _ :=
    (congrArg (fun f => f⟦(1 : ℤ)⟧') ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).map_id
        (tensorModule M))).trans (CategoryTheory.Functor.map_id _ _)
  exact (Category.comp_id _).symm.trans
    ((congrArg (extClass P ≫ ·) h1.symm).trans (extClass_mapAlong e.hom).symm)

/-- **Injectivity on isomorphism classes**: two extensions by `ℳ` with the same class are
isomorphic. They are compared on the generators `𝒪'_P ×_𝒪 𝒪'_Q`, which lift to both: equal
classes make the two conormal maps differ by `θ ∘ d`, and shifting one lift by `θ` makes them
agree, whence a morphism of extensions ([Stacks Project, Tag 08UG], Step 3). -/
theorem nonempty_iso_of_extClass_eq {P Q : AlgebraExtension a M}
    (h : extClass P = extClass Q) : Nonempty (P ≅ Q) := by
  have := isLocallySurjective_fibreMap P Q
  have h' := (cancel_epi (presentationTwoTermIso a _ (fibreMap P Q)).inv).1
    ((extClass_eq_of_lift (fibreFst P Q)).symm.trans (h.trans (extClass_eq_of_lift (fibreSnd P Q))))
  obtain ⟨θ, hθ⟩ := exists_d_comp_eq_sub_of_conormalExtClass_eq _ h'
  have hc : ((fibreSnd P Q).shift θ).conormalHom = (fibreFst P Q).conormalHom := by
    rw [GeneratorLift.conormalHom_shift, hθ, add_sub_cancel]
  obtain ⟨k, -⟩ := GeneratorLift.exists_hom_comp_eq (fibreFst P Q) ((fibreSnd P Q).shift θ)
    (GeneratorLift.restriction_eq_of_conormalHom_eq hc)
  exact ⟨asIso k⟩

omit [J.HasSheafCompose (forget CommRingCat)] [(forget CommRingCat).ReflectsIsomorphisms] in
/-- **Surjectivity**: every class in `Ext¹(NL_{𝒪/𝒜}, ℳ)` is the class of an extension. By
[Stacks Project, Tag 08UJ] the class is that of a morphism `δ : ℐ/ℐ² ⟶ ℳ` on some presentation,
up to sign, and the square-zero pushout of the presentation along `-δ` has conormal map `-δ`. -/
theorem exists_extClass_eq (ξ : ExtOne a M) : ∃ P : AlgebraExtension a M, extClass P = ξ := by
  obtain ⟨E₁, α₁, hs₁, f₁, hf₁⟩ :=
    Stacks.SheafOfModules.exists_presentation_conormalExtClass.{u, u, u, t} J A O a
      (tensorModule M) ξ
  have := hs₁
  refine ⟨(conormalPushout (M := M) (-f₁)).extension, ?_⟩
  refine (extClass_eq_of_lift (conormalPushoutLift (M := M) (-f₁))).trans ?_
  calc liftClass (conormalPushoutLift (M := M) (-f₁))
      = (presentationTwoTermIso a E₁.obj α₁).inv ≫
          (presentationTwoTerm a E₁.obj α₁).conormalExtClass (tensorModule M) (-f₁) :=
        by rw [liftClass, conormalHom_conormalPushoutLift]
    _ = (presentationTwoTermIso a E₁.obj α₁).inv ≫ ((presentationTwoTermIso a E₁.obj α₁).hom ≫ ξ) :=
        congrArg ((presentationTwoTermIso a E₁.obj α₁).inv ≫ ·)
          ((conormalExtClass_neg (tensorModule M) f₁).trans
            ((presentationConormalExtClass_eq_neg (tensorModule M) f₁).symm.trans hf₁.symm))
    _ = ξ := (presentationTwoTermIso a E₁.obj α₁).inv_hom_id_assoc ξ

variable (a M) in
/-- **[Stacks Project, Tag 0GQ5]**: the isomorphism classes of extensions
`0 ⟶ ℳ ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` of `𝒜`-algebras, `ℳ` an ideal of square zero, are in canonical bijection
with `Ext¹_𝒪(NL_{𝒪/𝒜}, ℳ)`, by the class `Deformation.AlgebraExtension.extClass`.

The source takes `𝒜 = f⁻¹𝒪_ℬ` for a morphism of ringed topoi `f`; only the ring map
`f⁻¹𝒪_ℬ ⟶ 𝒪` enters, and the statement here is for any morphism `a : 𝒜 ⟶ 𝒪` of sheaves of
commutative rings on a small site. -/
noncomputable def extClassEquiv :
    Quotient (isIsomorphicSetoid (AlgebraExtension a M)) ≃ ExtOne a M :=
  Equiv.ofBijective
    (Quotient.lift extClass fun _ _ ⟨e⟩ => extClass_eq_of_iso e)
    ⟨fun P Q h => by
      induction P using Quotient.inductionOn
      induction Q using Quotient.inductionOn
      exact Quotient.sound (nonempty_iso_of_extClass_eq h),
    fun ξ => let ⟨P, hP⟩ := exists_extClass_eq ξ; ⟨⟦P⟧, hP⟩⟩

/-- The bijection of [Stacks Project, Tag 0GQ5] sends the class of an extension to its class. -/
@[simp]
theorem extClassEquiv_mk (P : AlgebraExtension a M) :
    extClassEquiv a M ⟦P⟧ = extClass P :=
  rfl

/-! ### Scalars acting on `Ext¹(NL_{𝒪/𝒜}, ℳ)` -/

section Scalars

variable {R : Type*} [CommRing R]

/-- **The `R`-module structure on `Ext¹(NL_{𝒪/𝒜}, ℳ)`** induced by a ring homomorphism
`κ : R → End(ℳ)` (for instance `R = k` acting on an `𝒪`-module through `k → Γ(𝒪)`): a scalar
`r` acts by pushing a class along `κ r : ℳ ⟶ ℳ`. This is the module structure for which
[Stacks Project, Tag 0D0T] asserts finiteness. -/
@[reducible]
noncomputable def extOneModule (κ : R →+* End (tensorModule M)) : Module R (ExtOne a M) where
  smul r ξ := ξ ≫ ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).map (κ r))⟦(1 : ℤ)⟧'
  one_smul ξ := by
    change ξ ≫ _ = ξ
    rw [map_one, End.one_def, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  mul_smul r s ξ := by
    change ξ ≫ _ = (ξ ≫ _) ≫ _
    rw [map_mul, End.mul_def, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      Category.assoc]
  smul_zero r := Limits.zero_comp
  smul_add r ξ η := Preadditive.add_comp _ _ _ _ _ _
  add_smul r s ξ := by
    change ξ ≫ _ = ξ ≫ _ + ξ ≫ _
    rw [map_add, Functor.map_add, Functor.map_add, Preadditive.comp_add]
  zero_smul ξ := by
    change ξ ≫ _ = 0
    rw [map_zero, Functor.map_zero, Functor.map_zero, Limits.comp_zero]

end Scalars

end Deformation.AlgebraExtension

end
