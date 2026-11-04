module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksFrontier.CategoryTheory.TwoFibreProductOver
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smooth morphisms of categories cofibered in groupoids

A morphism of categories cofibered in groupoids over the base category is smooth
when objects lift along surjections, together with a compatible morphism. This file gives the
definition and shows smoothness is stable under composition and base change.

## Main definitions

* `IsSmooth` is the lifting property defining a smooth morphism of
  categories over `\mathcal C_\Lambda`.
* `twoFibreProductBasedCategory` regards the standard
  2-fibre product over the base as a based category.
* `twoFibreProductSnd` is its second projection as a
  based functor.

## Main results

* `isSmooth_comp` says that smooth morphisms are closed
  under composition.
* `isSmooth_twoFibreProductSnd` states that smoothness is
  preserved by base change.
* `isSmooth_of_essSurj_comp`
  says that if `φ` is essentially surjective and `φ` followed by `ψ` is smooth,
  then `ψ` is smooth.

## Implementation notes

### Smooth morphisms of categories cofibered in groupoids

Categories over the base and their morphisms are represented by Mathlib's
`BasedCategory` and `BasedFunctor`. The predicate is stated for all categories
over `\mathcal C_\Lambda`; the assumption that the two structure functors are
cofibered in groupoids belongs to the context in which smoothness is used and
is not needed to formulate the lifting property itself. The predicate
`Functor.IsHomLift` simultaneously records that the endpoints lie over the
specified base objects and that a morphism lies over the specified base
morphism.

### Composition of smooth morphisms of categories

Categories over the base and their morphisms are represented by `BasedCategory`
and `BasedFunctor`. As in the definition of smoothness, the result is stated for
arbitrary categories over `\mathcal C_\Lambda`: the cofibered-in-groupoids
hypotheses in the source are not used by the lifting argument.

### Smoothness and base change

The 2-fibre product is the explicit category `CategoryTheory.TwoFibreProductOver`.
Its comparison isomorphism is required to be vertical over the common object of the
base category.  The auxiliary based category and projection only package the existing
structure functor and second projection for use with `IsSmooth`.
Only the common target is assumed cofibered in groupoids: this is what makes the
vertical comparison produced by smoothness invertible.  The source proof uses no
cofiberedness assumption on either factor.

### Smoothness after an essentially surjective morphism

Categories over the base and their morphisms are represented by `BasedCategory`
and `BasedFunctor`. Essential surjectivity is Mathlib's
`CategoryTheory.Functor.EssSurj` for the underlying functor. Only the source
structure functor needs to be cofibered in groupoids: this transports an
isomorphic preimage into the required fibre. The other two cofiberedness
assumptions from the source context are not used by this argument.

## References

* [Stacks Project, Tag 06HG](https://stacks.math.columbia.edu/tag/06HG)
* [Stacks Project, Tag 06HM](https://stacks.math.columbia.edu/tag/06HM)
-/

@[expose] public section

namespace Deformation

/-! ### Smooth morphisms of categories cofibered in groupoids -/

section
open CategoryTheory
universe u v w u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A morphism of categories over `\mathcal C_\Lambda` is smooth if every
lifting problem over a surjective map `B \to A` has a compatible solution over
`B`. -/
@[stacks 06HG,
  stacks 06HP "smoothness of the structure morphism, i.e. an unobstructed cofibered category",
  sga "7 VI 2.1" "smooth"]
public abbrev IsSmooth {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, v, w} Λ
  k)} {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, v, w} Λ k)} (φ : BasedFunctor 𝓕 𝓖) : Prop
    := ∀ ⦃B A : ArtinianLocalAlgCat.{u, v, w} Λ k⦄ (f : B ⟶ A), Function.Surjective f.hom → ∀ (y :
      𝓖.obj) (x : 𝓕.obj) (g : y ⟶ φ.obj x), 𝓖.p.IsHomLift f g → ∃ (x' : 𝓕.obj) (h : x' ⟶ x) (a :
        φ.obj x' ⟶ y), 𝓕.p.IsHomLift f h ∧ 𝓖.p.IsHomLift (𝟙 B) a ∧ φ.map h = a ≫ g

end

/-! ### Composition of smooth morphisms of categories -/

section
open CategoryTheory
universe u v w u₁ v₁ u₂ v₂ u₃ v₃


variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The composite of two smooth morphisms of categories over
`\mathcal C_\Lambda` is smooth. -/
@[stacks 06HM "smooth_comp", sga "7 VI 2.3" "(a)"]
public theorem isSmooth_comp
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓗 : BasedCategory.{v₃, u₃} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (φ : BasedFunctor 𝓕 𝓖) (ψ : BasedFunctor 𝓖 𝓗)
    (hφ : IsSmooth φ) (hψ : IsSmooth ψ) :
    IsSmooth (BasedFunctor.comp φ ψ) := by
  intro B A f hf y x g hg; obtain ⟨y', h, a, hh, ha, hψeq⟩ := hψ f hf y (φ.obj x) g hg
  obtain ⟨x', h', b, hh', hb, hφeq⟩ := hφ f hf y' x h hh
  refine ⟨x', h', ψ.map b ≫ a, hh', ?_, ?_⟩
  · let _ := hb; let _ := ha; exact IsHomLift.comp_of_lift_id 𝓗.p B (ψ.map b) a
  · show ψ.map (φ.map h') = (ψ.map b ≫ a) ≫ g; rw [hφeq, ψ.map_comp, hψeq, Category.assoc]; rfl

end

/-! ### Smoothness and base change -/

section
open CategoryTheory
universe u v w uF vF uG vG uG' vG'


variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]


private noncomputable def isoOfVertical
    {C D : Type*} [Category C] [Category D] (q : C ⥤ D)
    (hq : q.op.IsFiberedInGroupoids) {A : D} {x y : C}
    (f : x ⟶ y)
    (hf : q.IsHomLift (𝟙 A) f) : x ≅ y := by
  haveI : q.op.IsHomLift (𝟙 (Opposite.op A)) f.op := by
    simpa using isHomLift_op q (𝟙 A) f (inst := hf)
  haveI := hq.isStronglyCartesian_homLift (𝟙 (Opposite.op A)) f.op
  haveI : IsIso f.op := Functor.IsStronglyCartesian.isIso_of_base_isIso q.op (𝟙 (Opposite.op A))
    f.op
  haveI : IsIso f := isIso_of_op f
  exact asIso f

/-- The standard 2-fibre product of two based functors with common target, regarded as
a category over their common base. -/
public def twoFibreProductBasedCategory
    {𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓖 : BasedCategory.{vG, uG} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓖' : BasedCategory.{vG', uG'} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (φ : BasedFunctor 𝓕 𝓖) (θ : BasedFunctor 𝓖' 𝓖) :
    BasedCategory (ArtinianLocalAlgCat.{u, v, w} Λ k) :=
  BasedCategory.ofFunctor
    (TwoFibreProductOver.structureFunctor 𝓕.p 𝓖'.p 𝓖.p φ.toFunctor θ.toFunctor)

/-- The second projection from the standard 2-fibre product, as a functor over the
base. -/
public def twoFibreProductSnd
    {𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓖 : BasedCategory.{vG, uG} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓖' : BasedCategory.{vG', uG'} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (φ : BasedFunctor 𝓕 𝓖) (θ : BasedFunctor 𝓖' 𝓖) :
    BasedFunctor (twoFibreProductBasedCategory φ θ) 𝓖' where
  toFunctor := TwoFibreProductOver.snd 𝓕.p 𝓖'.p 𝓖.p φ.toFunctor θ.toFunctor
  w := TwoFibreProductOver.snd_comp_eq

/-- A base change of a smooth morphism of categories cofibered in groupoids is smooth. -/
@[stacks 06HM "smooth_base_change"]
public theorem isSmooth_twoFibreProductSnd
    {𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓖 : BasedCategory.{vG, uG} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓖' : BasedCategory.{vG', uG'} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖) (θ : BasedFunctor 𝓖' 𝓖)
    (hφ : IsSmooth φ) : IsSmooth (twoFibreProductSnd φ θ) := by
  intro B A f hf y P g hg
  let pProd := TwoFibreProductOver.structureFunctor 𝓕.p 𝓖'.p 𝓖.p
    φ.toFunctor θ.toFunctor
  change TwoFibreProductOver 𝓕.p 𝓖'.p 𝓖.p φ.toFunctor θ.toFunctor at P
  change y ⟶ P.y at g
  change 𝓖'.p.IsHomLift f g at hg
  let gG : θ.obj y ⟶ φ.obj P.x := θ.toFunctor.map g ≫ P.iso.inv
  have hgG : 𝓖.p.IsHomLift f gG := by
    let : 𝓖'.p.IsHomLift f g := hg
    let : 𝓖.p.IsHomLift f (θ.toFunctor.map g) :=
      Functor.isHomLift_map_of_comp_eq θ.w f g
    let : 𝓖.p.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
    let : 𝓖.p.IsHomLift (𝟙 P.base) P.iso.inv :=
      IsHomLift.lift_id_inv 𝓖.p P.base P.iso
    exact IsHomLift.comp_lift_id_right' 𝓖.p f (θ.toFunctor.map g) P.base P.iso.inv
  obtain ⟨x', h, a, hh, ha, hcomm⟩ := hφ f hf (θ.obj y) P.x gG hgG
  have hx' : 𝓕.p.obj x' = B := IsHomLift.domain_eq 𝓕.p f h
  have hy : 𝓖'.p.obj y = B := IsHomLift.domain_eq 𝓖'.p f g
  let aIso := isoOfVertical 𝓖.p h𝓖 a ha
  have hbase : P.base = A := P.hy.symm.trans (IsHomLift.codomain_eq 𝓖'.p f g)
  let P' : TwoFibreProductOver 𝓕.p 𝓖'.p 𝓖.p φ.toFunctor θ.toFunctor :=
    { base := B, x := x', y := y, hx := hx', hy := hy, iso := aIso,
      vertical := ha }
  let hbaseArrow : B ⟶ P.base := f ≫ eqToHom hbase.symm
  let H : P' ⟶ P :=
    { hbase := hbaseArrow, a := h, b := g,
      ha := by
        let _ := hh
        exact inferInstanceAs (𝓕.p.IsHomLift (f ≫ eqToHom hbase.symm) h)
      hb := by
        let _ : 𝓖'.p.IsHomLift f g := hg
        exact inferInstanceAs (𝓖'.p.IsHomLift (f ≫ eqToHom hbase.symm) g)
      w := by
        calc
          φ.toFunctor.map h ≫ P.iso.hom = (a ≫ gG) ≫ P.iso.hom := by rw [hcomm]
          _ = a ≫ θ.toFunctor.map g := by simp [gG, Category.assoc]
          _ = aIso.hom ≫ θ.toFunctor.map g := by rfl }
  have hH : pProd.IsHomLift f H := by
    apply IsHomLift.of_fac' pProd f H rfl hbase
    show H.hbase = eqToHom rfl ≫ f ≫ eqToHom hbase.symm
    simp [H, hbaseArrow]
  exact ⟨P', H, 𝟙 y, hH, IsHomLift.id hy, (Category.id_comp g).symm⟩

end

/-! ### Smoothness after an essentially surjective morphism -/

section
open CategoryTheory
universe u v w u₁ v₁ u₂ v₂ u₃ v₃


variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- If the first of two morphisms of categories cofibered in groupoids is
essentially surjective and their composite is smooth, then the second morphism
is smooth. -/
@[stacks 06HM "smooth_of_essentially_surjective_smooth_comp", sga "7 VI 2.3" "(b)"]
public theorem isSmooth_of_essSurj_comp
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓗 : BasedCategory.{v₃, u₃} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p)
    (φ : BasedFunctor 𝓕 𝓖) (ψ : BasedFunctor 𝓖 𝓗) [φ.toFunctor.EssSurj]
    (h : IsSmooth (BasedFunctor.comp φ ψ)) : IsSmooth ψ := by
  intro B A f hf y x g hg
  let : 𝓗.p.IsHomLift f g := hg
  have hA : 𝓖.p.obj x = A := (BasedFunctor.w_obj ψ x).symm.trans
    (IsHomLift.codomain_eq 𝓗.p f g)
  subst A
  let x₀ := φ.toFunctor.objPreimage x
  let e := φ.toFunctor.objObjPreimageIso x
  let q := 𝓖.p.mapIso e
  have hf' : Function.Surjective (f ≫ q.inv).hom := by
    show Function.Surjective (q.inv.hom.comp f.hom)
    apply Function.Surjective.comp _ hf
    intro z
    refine ⟨q.hom.hom z, ?_⟩
    show (q.hom ≫ q.inv).hom z = z
    simp
  have hg' : 𝓗.p.IsHomLift (f ≫ q.inv) (g ≫ ψ.map e.inv) := by
    let : 𝓖.p.IsHomLift q.inv e.inv := inferInstanceAs (𝓖.p.IsHomLift (𝓖.p.map e.inv) e.inv)
    let : 𝓗.p.IsHomLift q.inv (ψ.map e.inv) :=
      BasedFunctor.preserves_isHomLift ψ q.inv e.inv
    exact inferInstance
  obtain ⟨x₁, h₁, a, hh₁, ha, hfac⟩ := h (f ≫ q.inv) hf' y x₀
    (g ≫ ψ.map e.inv) hg'
  have hh : 𝓖.p.IsHomLift f (φ.map h₁ ≫ e.hom) := by
    let : 𝓖.p.IsHomLift (f ≫ q.inv) (φ.map h₁) :=
      BasedFunctor.preserves_isHomLift φ (f ≫ q.inv) h₁
    let : 𝓖.p.IsHomLift q.hom e.hom := inferInstanceAs (𝓖.p.IsHomLift (𝓖.p.map e.hom) e.hom)
    simpa [Category.assoc] using
      (inferInstance : 𝓖.p.IsHomLift ((f ≫ q.inv) ≫ q.hom) (φ.map h₁ ≫ e.hom))
  have hfac' : ψ.map (φ.map h₁ ≫ e.hom) = a ≫ g := by
    change ψ.map (φ.map h₁) = a ≫ (g ≫ ψ.map e.inv) at hfac
    change ψ.obj (φ.obj x₁) ⟶ y at a
    have hcancel : (g ≫ ψ.map e.inv) ≫ ψ.map e.hom = g := by
      calc
        (g ≫ ψ.map e.inv) ≫ ψ.map e.hom = g ≫ (ψ.map e.inv ≫ ψ.map e.hom) := by
          rw [Category.assoc]
        _ = g := by rw [← ψ.map_comp, e.inv_hom_id, ψ.map_id, Category.comp_id]
    calc
      ψ.map (φ.map h₁ ≫ e.hom) = ψ.map (φ.map h₁) ≫ ψ.map e.hom := ψ.map_comp _ _
      _ = (a ≫ (g ≫ ψ.map e.inv)) ≫ ψ.map e.hom :=
        congrArg (fun z => z ≫ ψ.map e.hom) hfac
      _ = a ≫ g := by rw [Category.assoc, hcancel]
  exact ⟨φ.obj x₁, φ.map h₁ ≫ e.hom, a, hh, ha, hfac'⟩

end

/-! ### Surjectivity of a lift of a surjection -/

section
open CategoryTheory
universe u v w uF vF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- An isomorphism of Artinian local algebras is surjective on elements. -/
public lemma surjective_hom_of_isIso
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ B) [IsIso f] :
    Function.Surjective f.hom := fun b =>
  ⟨(inv f).hom b, congrArg (fun g : B ⟶ B => g.hom b) (IsIso.inv_hom_id f)⟩

/-- A morphism of a category over `\mathcal C_\Lambda` lying over a surjection of algebras
is itself carried to a surjection: the two endpoint identifications are isomorphisms, so the
image of the lift is the given surjection up to composition with them. -/
theorem surjective_map_of_lift
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : A ⟶ B) {x y : F} (φ : x ⟶ y)
    [p.IsHomLift f φ] (hf : Function.Surjective f.hom) :
    Function.Surjective (p.map φ).hom := by
  rw [IsHomLift.fac' p f φ]
  exact (surjective_hom_of_isIso (eqToHom (IsHomLift.codomain_eq p f φ).symm)).comp
    (hf.comp (surjective_hom_of_isIso (eqToHom (IsHomLift.domain_eq p f φ))))

end

end Deformation
