module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.ClassicalCase
public import StacksFrontier.Deformation.Formal.VersalObject.IsomorphismClassesHull
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Schlessinger.VersalExistence
public import StacksFrontier.Deformation.SchlessingerConditions.SetValuedFunctor

/-!
# Schlessinger's theorems for a set-valued predeformation functor

Let `F : 𝒞_Λ ⥤ Sets` be a predeformation functor. Stacks 06HY identifies Schlessinger's
conditions (H1) and (H2) with the conditions (S1) and (S2) on the category of elements of `F`,
and Stacks 06GT identifies the predeformation condition on `F` with the predeformation
condition on that category; the remaining condition `dim_k TF < ∞` is Schlessinger's (H3).
Stacks 06IW and 06IX, applied to the category of elements, therefore say

    (H1) + (H2) + (H3) ⟹ there exists a versal formal object,

which is Stacks 0D3G, and — in the classical case, or whenever `k` is separable over the image
field of `Λ` —

    (H1) + (H2) + (H3) ⟹ there exists a hull,

which is the last clause of Stacks 06IY and recovers Schlessinger's theorem on the existence
of hulls. A *hull* is `Deformation.IsHull`: a versal formal object whose differential is an
isomorphism.

## Main definitions

* `Deformation.classOfElement`: the isomorphism class of an element of `F(A)`, viewed as an
  object of the fibre of the category of elements of `F` over `A`.
* `Deformation.elementsIsomorphismClassesEquiv`: the canonical bijection
  `F(A) → \overline{F}(A)` onto the functor of fibrewise isomorphism classes of the category
  of elements of `F`.
* `Deformation.setValuedTangentSpaceAddCommGroup` and
  `Deformation.setValuedTangentSpaceModule`: the canonical `k`-vector-space structure of
  Stacks 06IH on `TF = F(k[ε])`, transported along that bijection.
* `Deformation.setValuedTangentSpaceAddEquiv` and
  `Deformation.setValuedTangentSpaceLinearEquiv`: that bijection at the dual numbers,
  as an additive and as a `k`-linear equivalence.

## Main results

* `Deformation.bijective_classOfElement`: a category of elements is its own functor of
  fibrewise isomorphism classes — the class map `F(A) → \overline{F}(A)` is bijective.
* `Deformation.elementsIsomorphismClassesEquiv_naturality`: that bijection is natural in `A`.
* `Deformation.finiteDimensional_tangentSpace_isomorphismClasses_of_setValued`: Schlessinger's
  (H3), the finite-dimensionality of `TF`, is the finite-dimensionality of the tangent space
  of `\overline{F}` that Stacks 06IW and 06IX ask for.
* `Deformation.exists_versalFormalObject_of_schlessingerConditions`: **Stacks 0D3G**, a
  set-valued predeformation functor satisfying (H1), (H2) and (H3) has a versal formal object.
* `Deformation.exists_hull_of_schlessingerConditions` and
  `Deformation.exists_hull_of_schlessingerConditions_isClassical`: **Stacks 06IY**, such a
  functor has a hull when `k` is separable over the image field of `Λ`, in particular in the
  classical case.

## Implementation notes

A category cofibered in sets over `𝒞_Λ` is represented, as in Stacks 06HJ and 06HY, by the
category of elements `F.Elements` of a set-valued functor together with its projection
`CategoryOfElements.π F`; `CategoryTheory.BasedCategory.ofFunctor` turns that projection into
a based category, and it is made locally `implicit_reducible` as in
`StacksFrontier.Deformation.Formal.VersalObject.IsomorphismClasses`, because a based category and
the based category of its own structure functor agree only up to unfolding that definition.

Stacks 06IH puts the canonical `k`-vector-space structure on the tangent space of the
*associated functor of isomorphism classes* of that category of elements, which is the form
Stacks 06IW and 06IX consume. That tangent space is a copy of `TF` as a `k`-vector space — the
canonical bijection is natural in the Artinian point, so it transports the whole structure,
which is `Deformation.setValuedTangentSpaceLinearEquiv` — and
`Deformation.finiteDimensional_tangentSpace_isomorphismClasses_of_setValued` turns the
finite-dimensionality of `TF` itself into the form those two tags want.

Condition (H3) of the three existence theorems below is therefore stated where Stacks 0D3G and
06IY state it, about `TF = F(k[ε])`, and transported inside each proof. The predeformation and
(S2) properties that the vector-space structure needs are consequences of `hpre` and `hH2`, by
Stacks 06GT and 06HY followed by
`Deformation.schlessingerConditionS2_of_isIsomorphismClasses`, so each statement installs them
itself in the `letI` prefix of that hypothesis rather than taking them as binders.

## References

* [Stacks Project, Tag 0D3G](https://stacks.math.columbia.edu/tag/0D3G)
* [Stacks Project, Tag 06IY](https://stacks.math.columbia.edu/tag/06IY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace Deformation

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u v w t uF vF

/-! ### A category of elements is its own functor of isomorphism classes -/

section

variable {C : Type u} [Category.{v} C]

/-- The fibrewise isomorphism class of an element of `F(A)`, that element being viewed as an
object of the fibre of the category of elements of `F` over `A`. -/
public noncomputable def classOfElement (F : C ⥤ Type t)
    (hq : IsCofiberedInGroupoids (CategoryOfElements.π F)) {A : C} (a : F.obj A) :
    (isomorphismClasses (BasedCategory.ofFunctor (CategoryOfElements.π F)) hq).obj A :=
  classOf (BasedCategory.ofFunctor (CategoryOfElements.π F)) hq ⟨F.elementsMk A a, rfl⟩

/-- A category of elements is its own functor of fibrewise isomorphism classes: taking the
class of an element is a bijection `F(A) → \overline{F}(A)`.

It is surjective because every object of the fibre over `A` is an element of `F(A)`, and
injective because an isomorphism in that fibre lies over the identity of `A`, so the
functoriality equation it carries identifies its two elements. -/
public theorem bijective_classOfElement (F : C ⥤ Type t)
    (hq : IsCofiberedInGroupoids (CategoryOfElements.π F)) (A : C) :
    Function.Bijective (classOfElement F hq (A := A)) := by
  refine ⟨fun a b hab ↦ ?_, fun z ↦ ?_⟩
  · have hcast := congrArg (cast (isomorphismClasses_obj
      (BasedCategory.ofFunctor (CategoryOfElements.π F)) hq A)) hab
    have hqa := classOf_eq (BasedCategory.ofFunctor (CategoryOfElements.π F)) hq
      (A := A) ⟨F.elementsMk A a, rfl⟩
    have hqb := classOf_eq (BasedCategory.ofFunctor (CategoryOfElements.π F)) hq
      (A := A) ⟨F.elementsMk A b, rfl⟩
    rw [classOfElement, classOfElement, hqa, hqb] at hcast
    obtain ⟨i⟩ := Quotient.exact hcast
    have hbase : i.hom.1.hom = 𝟙 A := by
      have : (CategoryOfElements.π F).IsHomLift (𝟙 A) i.hom.1 := i.hom.2
      have h := (IsHomLift.fac (p := CategoryOfElements.π F) (𝟙 A) i.hom.1).symm
      simp only [CategoryOfElements.π] at h
      erw [eqToHom_refl, Category.id_comp, Category.comp_id] at h
      exact h
    simpa [hbase] using i.hom.1.map_val
  · obtain ⟨⟨@⟨B, b⟩, hB⟩, hx⟩ :=
      classOf_surjective (BasedCategory.ofFunctor (CategoryOfElements.π F)) hq A z
    change B = A at hB
    cases hB
    exact ⟨b, hx⟩

/-- The canonical bijection from the value of a set-valued functor at `A` to the value at `A`
of the functor of fibrewise isomorphism classes of its category of elements. -/
public noncomputable def elementsIsomorphismClassesEquiv (F : C ⥤ Type t)
    (hq : IsCofiberedInGroupoids (CategoryOfElements.π F)) (A : C) :
    F.obj A ≃
      (isomorphismClasses (BasedCategory.ofFunctor (CategoryOfElements.π F)) hq).obj A :=
  Equiv.ofBijective _ (bijective_classOfElement F hq A)

/-- The canonical bijection of `Deformation.elementsIsomorphismClassesEquiv` is natural: the
class of a functorial image is the image of a class. -/
public theorem elementsIsomorphismClassesEquiv_naturality (F : C ⥤ Type t)
    (hq : IsCofiberedInGroupoids (CategoryOfElements.π F)) {A B : C} (f : A ⟶ B)
    (a : F.obj A) :
    elementsIsomorphismClassesEquiv F hq B (F.map f a) =
      (isomorphismClasses (BasedCategory.ofFunctor (CategoryOfElements.π F)) hq).map f
        (elementsIsomorphismClassesEquiv F hq A a) := by
  let g : F.elementsMk A a ⟶ F.elementsMk B (F.map f a) :=
    Functor.Elements.homMk f rfl
  have : (BasedCategory.ofFunctor (CategoryOfElements.π F)).p.IsHomLift f g :=
    IsHomLift.of_fac' (CategoryOfElements.π F) f g rfl rfl
      (by
        simp only [g, Functor.Elements.homMk, CategoryOfElements.π]
        erw [eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl)
  exact (map_classOf (BasedCategory.ofFunctor (CategoryOfElements.π F)) hq f
    ⟨F.elementsMk A a, rfl⟩ ⟨F.elementsMk B (F.map f a), rfl⟩ g).symm

end

/-! ### The tangent space of a set-valued functor -/

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

variable (F : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type t)
    (hpre : IsPredeformationCategory.{u, v, w}
      (BasedCategory.ofFunctor (CategoryOfElements.π F)).p)
    [Fact (IsPredeformationCategory.{u, v, w}
      (BasedCategory.ofFunctor (CategoryOfElements.π F)).p)]
    [Fact (SchlessingerConditionS2 (CategoryOfElements.π
      (isomorphismClasses (BasedCategory.ofFunctor (CategoryOfElements.π F))
        hpre.cofibered)))]

/-- The additive group underlying the canonical `k`-vector-space structure of Stacks 06IH on
the tangent space `TF = F(k[ε])` of a set-valued predeformation functor whose
isomorphism-class functor satisfies Schlessinger's condition (S2).

Stacks 06IH puts that structure on the tangent space of the associated functor of isomorphism
classes of the category of elements of `F`; here it is transported along the canonical
bijection `Deformation.elementsIsomorphismClassesEquiv`, which is natural in the Artinian
point and so carries the whole of the structure, not merely its underlying set. -/
@[instance_reducible]
public noncomputable def setValuedTangentSpaceAddCommGroup :
    AddCommGroup (tangentSpaceArtinian.{u, w, v} Λ k F) :=
  (elementsIsomorphismClassesEquiv F hpre.cofibered
    (artinianDualNumbers Λ k)).addCommGroup

/-- The canonical bijection of `Deformation.elementsIsomorphismClassesEquiv` at the dual
numbers is additive for the transported structure of
`Deformation.setValuedTangentSpaceAddCommGroup`, by construction of that structure. -/
public noncomputable def setValuedTangentSpaceAddEquiv :
    letI := setValuedTangentSpaceAddCommGroup.{u, v, w, t} F hpre
    tangentSpaceArtinian.{u, w, v} Λ k F ≃+
      tangentSpaceArtinian.{u, w, v} Λ k
        (isomorphismClasses (BasedCategory.ofFunctor (CategoryOfElements.π F))
          hpre.cofibered) :=
  letI := setValuedTangentSpaceAddCommGroup.{u, v, w, t} F hpre
  ⟨elementsIsomorphismClassesEquiv F hpre.cofibered (artinianDualNumbers Λ k),
    fun _ _ ↦ Equiv.apply_symm_apply _ _⟩

/-- The canonical scalar action of the residue field on the tangent space
`TF = F(k[ε])` of a set-valued predeformation functor, transported from Stacks 06IH along
`Deformation.setValuedTangentSpaceAddEquiv`. -/
@[instance_reducible]
public noncomputable def setValuedTangentSpaceModule :
    letI := setValuedTangentSpaceAddCommGroup.{u, v, w, t} F hpre
    Module k (tangentSpaceArtinian.{u, w, v} Λ k F) :=
  letI := setValuedTangentSpaceAddCommGroup.{u, v, w, t} F hpre
  (setValuedTangentSpaceAddEquiv.{u, v, w, t} F hpre).module k

/-- The canonical bijection of `Deformation.elementsIsomorphismClassesEquiv` at the dual
numbers is `k`-linear for the transported structure: the tangent space of a set-valued
predeformation functor and the tangent space of the associated functor of isomorphism classes
of its category of elements are a copy of one another as `k`-vector spaces. -/
public noncomputable def setValuedTangentSpaceLinearEquiv :
    letI := setValuedTangentSpaceAddCommGroup.{u, v, w, t} F hpre
    letI := setValuedTangentSpaceModule.{u, v, w, t} F hpre
    tangentSpaceArtinian.{u, w, v} Λ k F ≃ₗ[k]
      tangentSpaceArtinian.{u, w, v} Λ k
        (isomorphismClasses (BasedCategory.ofFunctor (CategoryOfElements.π F))
          hpre.cofibered) :=
  letI := setValuedTangentSpaceAddCommGroup.{u, v, w, t} F hpre
  letI := setValuedTangentSpaceModule.{u, v, w, t} F hpre
  (setValuedTangentSpaceAddEquiv.{u, v, w, t} F hpre).linearEquiv k

/-- **Schlessinger's condition (H3) is the finite-dimensionality of the tangent space of the
functor of isomorphism classes.** If the tangent space `TF = F(k[ε])` of a set-valued
predeformation functor is finite dimensional for its canonical structure of Stacks 06IH, then
so is the tangent space of the associated functor of isomorphism classes of the category of
elements of `F`, which is the form in which Stacks 06IW and 06IX consume the hypothesis.

The two are a copy of one another by
`Deformation.setValuedTangentSpaceLinearEquiv`. -/
public theorem finiteDimensional_tangentSpace_isomorphismClasses_of_setValued
    (h : letI := setValuedTangentSpaceAddCommGroup.{u, v, w, t} F hpre
         letI := setValuedTangentSpaceModule.{u, v, w, t} F hpre
         FiniteDimensional k (tangentSpaceArtinian.{u, w, v} Λ k F)) :
    FiniteDimensional k (tangentSpaceArtinian.{u, w, v} Λ k
      (isomorphismClasses (BasedCategory.ofFunctor (CategoryOfElements.π F))
        hpre.cofibered)) :=
  @LinearEquiv.finiteDimensional k (tangentSpaceArtinian.{u, w, v} Λ k F) _
    (setValuedTangentSpaceAddCommGroup.{u, v, w, t} F hpre)
    (setValuedTangentSpaceModule.{u, v, w, t} F hpre) _ _ _
    (setValuedTangentSpaceLinearEquiv.{u, v, w, t} F hpre) h

end

/-! ### Schlessinger's existence theorems for a set-valued functor -/

section

/-- The predeformation and (S2) facts that the vector-space structure on `TF` needs, for a
set-valued predeformation functor satisfying (H2). -/
private theorem facts_elements_isomorphismClasses
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (F : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type t)
    (hpre : IsPredeformationFunctor.{u, v, w, t} F)
    (hH2 : ∀ ⦃A A₀ Aε B : ArtinianLocalAlgCat.{u, max v w, w} Λ k⦄
      (d : A ⟶ A₀) (e : Aε ⟶ A₀), IsDualNumberProjection e →
        ∀ (g : B ⟶ A) (gε : B ⟶ Aε) (hPB : IsPullback gε g e d),
          Function.Bijective (fibreProductComparison F g gε d e hPB.w)) :
    Fact (IsPredeformationCategory.{u, v, w}
        (BasedCategory.ofFunctor (CategoryOfElements.π F)).p) ∧
      Fact (SchlessingerConditionS2 (CategoryOfElements.π
        (isomorphismClasses (BasedCategory.ofFunctor (CategoryOfElements.π F))
          ((isPredeformationCategory_iff F).2 hpre).cofibered))) :=
  ⟨⟨(isPredeformationCategory_iff F).2 hpre⟩,
    ⟨schlessingerConditionS2_of_isIsomorphismClasses
      (BasedCategory.ofFunctor (CategoryOfElements.π F))
      ((isPredeformationCategory_iff F).2 hpre).cofibered
      ((schlessingerConditionS2_elements_iff F).2 hH2)
      (Or.inl ((isPredeformationCategory_iff F).2 hpre))⟩⟩

/-- **Stacks Project, Tag 0D3G.** A set-valued predeformation functor on `𝒞_Λ` satisfying
Schlessinger's conditions (H1) and (H2) — that is, (S1) and (S2) in the elementary form of
Stacks 06HY — and his condition (H3), the finite-dimensionality of the tangent space, has a
versal formal object.

This is Stacks 06IW read through the identifications of Stacks 06GT and 06HY: the category of
elements of `F` is a predeformation category satisfying (S1) and (S2), and its functor of
isomorphism classes is a copy of `F` by `Deformation.elementsIsomorphismClassesEquiv`, so the
tangent space whose dimension is bounded is `TF`.

Condition (H3) is stated about `TF = F(k[ε])` itself, for the canonical `k`-vector-space
structure of Stacks 06IH transported to it by
`Deformation.setValuedTangentSpaceLinearEquiv`; the form Stacks 06IW consumes is obtained
inside the proof by `Deformation.finiteDimensional_tangentSpace_isomorphismClasses_of_setValued`.
The predeformation and (S2) properties that structure needs are the images of `hpre` and `hH2`
under Stacks 06GT and 06HY, the latter followed by
`Deformation.schlessingerConditionS2_of_isIsomorphismClasses`, so the statement installs them
itself rather than assuming them. -/
@[stacks 0D3G "(H1) + (H2) + (H3) implies a versal formal object exists",
  sga "7 VI 1.11" "set-valued functor"]
public theorem exists_versalFormalObject_of_schlessingerConditions
    (Λ : Type u) (k : Type w) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    (F : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type t)
    (hpre : IsPredeformationFunctor.{u, v, w, t} F)
    (hH1 : ∀ ⦃A₁ A₂ A A₁₂ : ArtinianLocalAlgCat.{u, max v w, w} Λ k⦄
      (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A), Function.Surjective f₂.hom →
        ∀ (g₁ : A₁₂ ⟶ A₁) (g₂ : A₁₂ ⟶ A₂) (hPB : IsPullback g₂ g₁ f₂ f₁),
          Function.Surjective (fibreProductComparison F g₁ g₂ f₁ f₂ hPB.w))
    (hH2 : ∀ ⦃A A₀ Aε B : ArtinianLocalAlgCat.{u, max v w, w} Λ k⦄
      (d : A ⟶ A₀) (e : Aε ⟶ A₀), IsDualNumberProjection e →
        ∀ (g : B ⟶ A) (gε : B ⟶ Aε) (hPB : IsPullback gε g e d),
          Function.Bijective (fibreProductComparison F g gε d e hPB.w))
    (hH3 :
      letI : Fact (IsPredeformationCategory.{u, v, w}
          (BasedCategory.ofFunctor (CategoryOfElements.π F)).p) :=
        ⟨(isPredeformationCategory_iff F).2 hpre⟩
      letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π
          (isomorphismClasses (BasedCategory.ofFunctor (CategoryOfElements.π F))
            ((isPredeformationCategory_iff F).2 hpre).cofibered))) :=
        ⟨schlessingerConditionS2_of_isIsomorphismClasses
          (BasedCategory.ofFunctor (CategoryOfElements.π F))
          ((isPredeformationCategory_iff F).2 hpre).cofibered
          ((schlessingerConditionS2_elements_iff F).2 hH2)
          (Or.inl ((isPredeformationCategory_iff F).2 hpre))⟩
      letI := setValuedTangentSpaceAddCommGroup.{u, v, w, t} F
        ((isPredeformationCategory_iff F).2 hpre)
      letI := setValuedTangentSpaceModule.{u, v, w, t} F
        ((isPredeformationCategory_iff F).2 hpre)
      FiniteDimensional k (tangentSpaceArtinian.{u, w, v} Λ k F)) :
    ∃ ξ : FormalObject (CategoryOfElements.π F),
      IsVersal ((isPredeformationCategory_iff F).2 hpre).cofibered ξ := by
  obtain ⟨_, _⟩ := facts_elements_isomorphismClasses.{u, v, w, t} F hpre hH2
  exact exists_versalFormalObject Λ k (BasedCategory.ofFunctor (CategoryOfElements.π F))
    ((isPredeformationCategory_iff F).2 hpre)
    ((schlessingerConditionS1_elements_iff F).2 hH1)
    ((schlessingerConditionS2_elements_iff F).2 hH2)
    (finiteDimensional_tangentSpace_isomorphismClasses_of_setValued.{u, v, w, t} F
      ((isPredeformationCategory_iff F).2 hpre) hH3)

/-- **Stacks Project, Tag 06IY.** A set-valued predeformation functor on `𝒞_Λ` satisfying
Schlessinger's conditions (H1), (H2) and (H3) has a hull, provided `k` is separable over the
image field of `Λ`: a versal formal object whose differential is an isomorphism.

This is Schlessinger's theorem on the existence of hulls. It is Stacks 06IX read through the
identifications of Stacks 06GT and 06HY, exactly as
`Deformation.exists_versalFormalObject_of_schlessingerConditions` is Stacks 06IW, and (H3) is
stated and discharged in the same way: about `TF = F(k[ε])` itself, transported inside the
proof by `Deformation.finiteDimensional_tangentSpace_isomorphismClasses_of_setValued`. -/
@[stacks 06IY "(H1) + (H2) + (H3) implies a hull exists",
  sga "7 VI 1.20" "set-valued functor"]
public theorem exists_hull_of_schlessingerConditions
    (Λ : Type u) (k : Type w) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] [Algebra.IsSeparable (residueImageField Λ k) k]
    (F : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type t)
    (hpre : IsPredeformationFunctor.{u, v, w, t} F)
    (hH1 : ∀ ⦃A₁ A₂ A A₁₂ : ArtinianLocalAlgCat.{u, max v w, w} Λ k⦄
      (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A), Function.Surjective f₂.hom →
        ∀ (g₁ : A₁₂ ⟶ A₁) (g₂ : A₁₂ ⟶ A₂) (hPB : IsPullback g₂ g₁ f₂ f₁),
          Function.Surjective (fibreProductComparison F g₁ g₂ f₁ f₂ hPB.w))
    (hH2 : ∀ ⦃A A₀ Aε B : ArtinianLocalAlgCat.{u, max v w, w} Λ k⦄
      (d : A ⟶ A₀) (e : Aε ⟶ A₀), IsDualNumberProjection e →
        ∀ (g : B ⟶ A) (gε : B ⟶ Aε) (hPB : IsPullback gε g e d),
          Function.Bijective (fibreProductComparison F g gε d e hPB.w))
    (hH3 :
      letI : Fact (IsPredeformationCategory.{u, v, w}
          (BasedCategory.ofFunctor (CategoryOfElements.π F)).p) :=
        ⟨(isPredeformationCategory_iff F).2 hpre⟩
      letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π
          (isomorphismClasses (BasedCategory.ofFunctor (CategoryOfElements.π F))
            ((isPredeformationCategory_iff F).2 hpre).cofibered))) :=
        ⟨schlessingerConditionS2_of_isIsomorphismClasses
          (BasedCategory.ofFunctor (CategoryOfElements.π F))
          ((isPredeformationCategory_iff F).2 hpre).cofibered
          ((schlessingerConditionS2_elements_iff F).2 hH2)
          (Or.inl ((isPredeformationCategory_iff F).2 hpre))⟩
      letI := setValuedTangentSpaceAddCommGroup.{u, v, w, t} F
        ((isPredeformationCategory_iff F).2 hpre)
      letI := setValuedTangentSpaceModule.{u, v, w, t} F
        ((isPredeformationCategory_iff F).2 hpre)
      FiniteDimensional k (tangentSpaceArtinian.{u, w, v} Λ k F)) :
    ∃ ξ : FormalObject (CategoryOfElements.π F),
      IsHull ((isPredeformationCategory_iff F).2 hpre).cofibered ξ := by
  obtain ⟨_, _⟩ := facts_elements_isomorphismClasses.{u, v, w, t} F hpre hH2
  obtain ⟨ξ, hminimal, hbijective⟩ :=
    exists_minimalVersal_hasBijectiveDifferential_of_separable
      (BasedCategory.ofFunctor (CategoryOfElements.π F))
      ((isPredeformationCategory_iff F).2 hpre)
      (exists_minimalVersal_hasBijectiveDifferentialOnDerivationOrbits Λ k
        (BasedCategory.ofFunctor (CategoryOfElements.π F))
        ((isPredeformationCategory_iff F).2 hpre)
        ((schlessingerConditionS1_elements_iff F).2 hH1)
        ((schlessingerConditionS2_elements_iff F).2 hH2)
        (finiteDimensional_tangentSpace_isomorphismClasses_of_setValued.{u, v, w, t} F
          ((isPredeformationCategory_iff F).2 hpre) hH3))
  exact ⟨ξ, hminimal.1, hbijective⟩

/-- **Stacks Project, Tag 06IY.** In the classical case — `Λ` a Noetherian complete local ring
whose residue field is identified with `k` — a set-valued predeformation functor satisfying
Schlessinger's conditions (H1), (H2) and (H3) has a hull.

A classical base satisfies the three standing hypotheses of
`Deformation.exists_hull_of_schlessingerConditions`: it is Noetherian, `k` is a finite
`Λ`-module, and `k` is separable over the image field of `Λ` because that image field is all
of `k`. -/
@[stacks 06IY "(H1) + (H2) + (H3) implies a hull exists, classical case",
  sga "7 VI 1.20" "special case"]
public theorem exists_hull_of_schlessingerConditions_isClassical
    (Λ : Type u) (k : Type w) [CommRing Λ] [Field k] [Algebra Λ k] (hΛ : IsClassical Λ k)
    (F : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type t)
    (hpre : IsPredeformationFunctor.{u, v, w, t} F)
    (hH1 : ∀ ⦃A₁ A₂ A A₁₂ : ArtinianLocalAlgCat.{u, max v w, w} Λ k⦄
      (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A), Function.Surjective f₂.hom →
        ∀ (g₁ : A₁₂ ⟶ A₁) (g₂ : A₁₂ ⟶ A₂) (hPB : IsPullback g₂ g₁ f₂ f₁),
          Function.Surjective (fibreProductComparison F g₁ g₂ f₁ f₂ hPB.w))
    (hH2 : ∀ ⦃A A₀ Aε B : ArtinianLocalAlgCat.{u, max v w, w} Λ k⦄
      (d : A ⟶ A₀) (e : Aε ⟶ A₀), IsDualNumberProjection e →
        ∀ (g : B ⟶ A) (gε : B ⟶ Aε) (hPB : IsPullback gε g e d),
          Function.Bijective (fibreProductComparison F g gε d e hPB.w))
    (hH3 :
      letI : Fact (IsPredeformationCategory.{u, v, w}
          (BasedCategory.ofFunctor (CategoryOfElements.π F)).p) :=
        ⟨(isPredeformationCategory_iff F).2 hpre⟩
      letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π
          (isomorphismClasses (BasedCategory.ofFunctor (CategoryOfElements.π F))
            ((isPredeformationCategory_iff F).2 hpre).cofibered))) :=
        ⟨schlessingerConditionS2_of_isIsomorphismClasses
          (BasedCategory.ofFunctor (CategoryOfElements.π F))
          ((isPredeformationCategory_iff F).2 hpre).cofibered
          ((schlessingerConditionS2_elements_iff F).2 hH2)
          (Or.inl ((isPredeformationCategory_iff F).2 hpre))⟩
      letI := setValuedTangentSpaceAddCommGroup.{u, v, w, t} F
        ((isPredeformationCategory_iff F).2 hpre)
      letI := setValuedTangentSpaceModule.{u, v, w, t} F
        ((isPredeformationCategory_iff F).2 hpre)
      FiniteDimensional k (tangentSpaceArtinian.{u, w, v} Λ k F)) :
    ∃ ξ : FormalObject (CategoryOfElements.π F),
      IsHull ((isPredeformationCategory_iff F).2 hpre).cofibered ξ := by
  let : IsNoetherianRing Λ := hΛ.isNoetherianRing
  let : Module.Finite Λ k := hΛ.moduleFinite
  let : Algebra.IsSeparable (residueImageField Λ k) k := hΛ.isSeparable
  exact exists_hull_of_schlessingerConditions.{u, v, w, t} Λ k F hpre hH1 hH2 hH3

end

end Deformation

end
