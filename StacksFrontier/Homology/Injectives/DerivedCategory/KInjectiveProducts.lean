module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
import StacksCore.Tactic.StacksAttribute

/-!
# Products of K-injective complexes in the derived category

Let `A` be a Grothendieck abelian category. Tag 07D9 says that the termwise product of a
family of K-injective cochain complexes represents the product, in the unbounded derived
category, of the objects they represent.

The proof goes through the homotopy category. A termwise product of K-injective complexes is
K-injective, because a null-homotopy of a map into the product can be assembled degreewise
from null-homotopies of its components (`homotopyOfFan`). The product fan therefore survives
two steps: it stays a product after passing to the homotopy category, since homotopy classes
of maps into the product are exactly families of homotopy classes; and it stays a product
after localizing at the quasi-isomorphisms, because for a K-injective target the localization
functor `Qh` is bijective on morphism sets. Transporting along
`DerivedCategory.quotientCompQhIso` turns the resulting statement about `Qh` into the
statement about `Q`.

## Main definitions

* `Stacks.Injectives.productFanInDerivedCategory`: the fan in the derived category obtained
  from the termwise product complex and its projections.

## Main results

* `Stacks.Injectives.isLimit_productFanInDerivedCategory`: that fan is a product fan as soon
  as every member of the family is K-injective.

## Implementation notes

The object represented by `K i` is written `DerivedCategory.Q.obj (K i)`, so the legs of the
cone are the images of the canonical projections out of the termwise product complex; the
statement is therefore about whatever model of the unbounded derived category
`HasDerivedCategory` provides, with no choice of model made here.

Products are handled through `Fan` rather than `HasProduct` so that the fan can be transported
explicitly along the two functors. The reusable step is `isLimitMapFan`: a fan is sent to a
limit fan by a functor which is essentially surjective and bijective on the relevant morphism
sets.

## References

* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w' v u v₁ u₁

namespace Stacks.Injectives

variable {A : Type u} [Category.{v} A] [Abelian A]
  [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w'} A]

/-- The cone in the derived category induced by the projections from the termwise product
of a family of complexes. -/
noncomputable def productFanInDerivedCategory {I : Type w}
    (K : I → CochainComplex A ℤ) :
    Fan (fun i => DerivedCategory.Q.obj (K i)) :=
  Fan.mk (DerivedCategory.Q.obj (∏ᶜ K))
    (fun i => DerivedCategory.Q.map (Pi.π K i))

private def fanHom {C : Type u} [Category.{v} C] {I : Type w} {L : I → C} (t : Fan L)
    (X : C) (f : X ⟶ t.pt) (i : I) : X ⟶ L i := f ≫ t.proj i

private lemma bijective_fanHom {C : Type u} [Category.{v} C] {I : Type w} {L : I → C}
    {t : Fan L} (ht : IsLimit t) (X : C) : Function.Bijective (fanHom t X) :=
  ⟨fun _ _ h => Fan.IsLimit.hom_ext ht _ _ fun i => congrFun h i, fun u =>
    ⟨Fan.IsLimit.lift ht u, funext (Fan.IsLimit.fac ht u)⟩⟩

private noncomputable def isLimitOfBijectiveFanHom
    {C : Type u} [Category.{v} C] {I : Type w} {L : I → C} {t : Fan L}
    (h : ∀ X : C, Function.Bijective (fanHom t X)) : IsLimit t :=
  Fan.IsLimit.mk _ (fun s => ((h s.pt).existsUnique s.proj).choose)
    (fun s i => congrFun ((h s.pt).existsUnique s.proj).choose_spec.1 i)
    (fun s m hm => ((h s.pt).existsUnique s.proj).choose_spec.2 m (funext hm))

private lemma bijective_fanHom_of_iso {C : Type u} [Category.{v} C]
    {I : Type w} {L : I → C} {t : Fan L} {X Y : C} (e : X ≅ Y)
    (h : Function.Bijective (fanHom t X)) : Function.Bijective (fanHom t Y) := by
  have hnat : fanHom t Y ∘ e.homFromEquiv
      = Pi.map (fun i => (e.homFromEquiv (Z := L i) : (X ⟶ L i) → (Y ⟶ L i))) ∘
        fanHom t X := by
    funext f i; simp [fanHom]
  refine (Function.Bijective.of_comp_iff _ (e.homFromEquiv (Z := t.pt)).bijective).1 ?_
  rw [hnat]
  exact (Function.Bijective.piMap fun i => (e.homFromEquiv (Z := L i)).bijective).comp h

private lemma fanHom_comp_map {C : Type u} [Category.{v} C]
    {D : Type u₁} [Category.{v₁} D] {I : Type w} {L : I → C} {t : Fan L}
    (G : C ⥤ D) (Y : C) :
    fanHom (Fan.mk (G.obj t.pt) fun i => G.map (t.proj i)) (G.obj Y) ∘ G.map
      = Pi.map (fun i (f : Y ⟶ L i) => G.map f) ∘ fanHom t Y := by
  funext f i; simp [fanHom]

private noncomputable def isLimitMapFan {C : Type u} [Category.{v} C]
    {D : Type u₁} [Category.{v₁} D] {I : Type w} {L : I → C} {t : Fan L}
    (G : C ⥤ D) [G.EssSurj] (ht : IsLimit t)
    (hpt : ∀ Y : C, Function.Bijective (G.map : (Y ⟶ t.pt) → _))
    (hL : ∀ (Y : C) (i : I), Function.Bijective (G.map : (Y ⟶ L i) → _)) :
    IsLimit (Fan.mk (G.obj t.pt) fun i => G.map (t.proj i)) :=
  isLimitOfBijectiveFanHom fun X =>
    bijective_fanHom_of_iso (G.objObjPreimageIso X)
      ((Function.Bijective.of_comp_iff _ (hpt _)).1 (by
        rw [fanHom_comp_map]
        exact (Function.Bijective.piMap fun i => hL _ i).comp (bijective_fanHom ht _)))

private noncomputable def isLimitFanEval
    {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
    {I : Type w} {L : I → HomologicalComplex C c} [HasProductsOfShape I C]
    {t : Fan L} (ht : IsLimit t) (j : ι) :
    IsLimit (Fan.mk (t.pt.X j) fun i => (t.proj i).f j) :=
  Fan.isLimitMapConeEquiv (HomologicalComplex.eval C c j) L t (isLimitOfPreserves _ ht)

private lemma isLimitFanEval_lift_proj
    {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
    {I : Type w} {L : I → HomologicalComplex C c} [HasProductsOfShape I C]
    {t : Fan L} (ht : IsLimit t) (j : ι) {X : C} (f : ∀ i, X ⟶ (L i).X j) (i : I) :
    Fan.IsLimit.lift (isLimitFanEval ht j) f ≫ (t.proj i).f j = f i :=
  Fan.IsLimit.fac (isLimitFanEval ht j) f i

private noncomputable def homotopyOfFan
    {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
    {I : Type w} {L : I → HomologicalComplex C c} [HasProductsOfShape I C]
    {t : Fan L} (ht : IsLimit t) {X : HomologicalComplex C c} {f g : X ⟶ t.pt}
    (h : ∀ i, Homotopy (f ≫ t.proj i) (g ≫ t.proj i)) : Homotopy f g where
  hom i j := Fan.IsLimit.lift (isLimitFanEval ht j) fun a => (h a).hom i j
  zero i j hij := Fan.IsLimit.hom_ext (isLimitFanEval ht j) _ _ fun a => by
    simp [isLimitFanEval_lift_proj, (h a).zero i j hij]
  comm i := Fan.IsLimit.hom_ext (isLimitFanEval ht i) _ _ fun a => by
    simpa only [fan_mk_proj, Preadditive.add_comp, ← dNext_comp_right, ← prevD_comp_right,
      isLimitFanEval_lift_proj, ← HomologicalComplex.comp_f] using (h a).comm i

private noncomputable def isLimitFanQuotient {I : Type w}
    {K : I → CochainComplex A ℤ} {t : Fan K} (ht : IsLimit t) :
    IsLimit (Fan.mk ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj t.pt)
      (fun i => (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (t.proj i))) :=
  isLimitOfBijectiveFanHom fun Y => by
    obtain ⟨Y, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    refine ⟨fun f g hfg => ?_, ?_⟩
    · obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective f
      obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective g
      exact HomotopyCategory.eq_of_homotopy _ _ (homotopyOfFan ht fun i =>
        HomotopyCategory.homotopyOfEq _ _ (by simpa [fanHom] using congrFun hfg i))
    · refine Function.Surjective.of_comp
        (g := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map) ?_
      rw [fanHom_comp_map]
      exact (Function.Surjective.piMap fun i =>
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective).comp
          (bijective_fanHom ht Y).surjective

private noncomputable def isLimitFanQh {I : Type w}
    {K : I → CochainComplex A ℤ} {t : Fan K} (ht : IsLimit t)
    [∀ i, (K i).IsKInjective] :
    IsLimit (Fan.mk (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj t.pt))
      (fun i => DerivedCategory.Qh.map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (t.proj i)))) := by
  have : t.pt.IsKInjective :=
    ⟨fun f hf => ⟨homotopyOfFan ht (fun i =>
      ((inferInstance : (K i).IsKInjective).homotopyZero (f ≫ t.proj i) hf).trans
        (Homotopy.ofEq zero_comp.symm))⟩⟩
  exact isLimitMapFan DerivedCategory.Qh (isLimitFanQuotient ht)
    (fun Y => CochainComplex.IsKInjective.Qh_map_bijective Y t.pt)
    (fun Y i => CochainComplex.IsKInjective.Qh_map_bijective Y (K i))

/-- The termwise product of K-injective representatives represents their product in the
unbounded derived category. -/
@[stacks 07D9 "termwise products of K-injective complexes"]
theorem isLimit_productFanInDerivedCategory {I : Type w}
    (K : I → CochainComplex A ℤ) (hK : ∀ i, (K i).IsKInjective) :
    Nonempty (IsLimit (productFanInDerivedCategory K)) := by
  classical
  show Nonempty (IsLimit (Fan.mk (DerivedCategory.Q.obj (∏ᶜ K))
    (fun i => DerivedCategory.Q.map (Pi.π K i))))
  have (i : I) : (K i).IsKInjective := hK i
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let η := DerivedCategory.quotientCompQhIso A
  have hlim : IsLimit (Fan.mk (DerivedCategory.Qh.obj (q.obj (∏ᶜ K)))
      (fun i => DerivedCategory.Qh.map (q.map (Pi.π K i)))) :=
    isLimitFanQh (t := Fan.mk (∏ᶜ K) (fun i => Pi.π K i)) (productIsProduct K)
  refine ⟨(IsLimit.postcomposeHomEquiv
    (Discrete.natIso fun i => η.app (K i.as)) _).symm hlim |>.ofIsoLimit
      (Cone.ext (η.app (∏ᶜ K)) ?_)⟩
  rintro ⟨i⟩
  exact (DerivedCategory.quotientCompQhIso_hom_naturality (C := A) (Pi.π K i))

end Stacks.Injectives
