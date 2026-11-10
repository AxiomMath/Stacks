module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinClassBaseChangeImmersion
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.FractionBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedFractionNaturality

/-!
# Base change of the class map of Tag 0G7Q along an open immersion

Let `X` be a scheme, `f₁, …, f_c ∈ Γ(X, 𝒪_X)`, `T ⊆ X` closed and containing their common zero
locus, `ℱ` a quasi-coherent `𝒪_X`-module and `g : X' ⟶ X` an open immersion.  The class map of
[Stacks, Tag 0G7Q] factors, by `Stacks.Perfect.SupportedFraction.supportedFractionSource_eq`, as
the degree-`c` cohomology class of the fraction cochain `s / (f₁ ⋯ f_c)` followed by the
comparison of [Stacks, Tag 0G7L].  The base change of the second factor is
`Stacks.Gysin.map_cechHomologyToSupport_comp_supportCohomologyOpenImmersionIso`.  This file
supplies the base change of the first, and composes the two.

## Main results

* `Stacks.Gysin.map_shortComplexClass`: **an exact functor commutes with the passage from a
  cocycle to its cohomology class.**  Stated on a short complex, which is where
  `CategoryTheory.ShortComplex.mapHomologyIso` — the component of
  `StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso` — lives.
* `Stacks.Gysin.mapHomologicalComplex_class`: the same on a complex.
* `Stacks.Gysin.extend_class`: **the class of a cocycle is unchanged by extending the grading**,
  the cocycle being carried along `HomologicalComplex.extendXIso`.
* `Stacks.Gysin.class_comp_homologyMap`: a morphism of complexes carries the class of a cocycle
  to the class of its image.
* `Stacks.Gysin.map_cechCocycleClass_comp_cechHomologyImmersionIso`: **the degree-`p` Čech
  cohomology class of a cocycle is local.**  Its restriction along `g`, read across
  `Stacks.Gysin.cechHomologyImmersionIso`, is the class of the restricted cocycle.
* `Stacks.Gysin.map_supportedFractionSource_comp_supportCohomologyRestrictIso`: **the class map
  of [Stacks, Tag 0G7Q] is local**, which is [Stacks, Tag 0G7U] for an arbitrary open immersion
  read on the coefficient module.

## Implementation notes

The two spellings of the category of modules on `X'` are crossed exactly as in
`GysinClassBaseChange`: every chase is a lemma at a variable category, applied with `exact`.

The chain has four links, and the middle two are the ones that carry content.  Going from the
`ℕ`-graded Čech complex to its extension to the grading `ℤ` and back is `extend_class`; the
exactness of the restriction functor enters through `mapHomologicalComplex_class`; the
degreewise comparison of the two Čech complexes enters through `class_comp_homologyMap`; and
`restrictExtendIso_hom_f_succ` is the one degreewise computation needed, namely that in a
positive degree the comparison of the two extended complexes is the degreewise comparison
`Stacks.Perfect.PushforwardRestrict.restrictProdTermIso`.

## References

* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Perfect.CechDerivedSupport
open Stacks.Perfect.CechDerivedSupportImmersion
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.PushforwardRestrict (restrictFunctor_map_fractionHom restrictProdTermIso)
open Stacks.Perfect.SupportedFraction
open StacksDraft.DerivedCategoryHomology
open scoped AlgebraicGeometry

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### An exact functor and the class of a cocycle -/

section General

/-- Cancelling a pair of inverse isomorphisms after a morphism, at a variable category.  The
degree-`(p+1)` term of the extended alternating Čech complex has two spellings — as
`Stacks.Perfect.SupportedFraction.prodTerm` and as a term of `cplx` — so this cancellation has
to be made by the unifier rather than by `rw`. -/
private theorem invHomCancel {V : Type*} [Category* V] {o₁ o₂ o₃ : V} (a : o₁ ⟶ o₂)
    (i : o₂ ⟶ o₃) (j : o₃ ⟶ o₂) (h : i ≫ j = 𝟙 o₂) : (a ≫ i) ≫ j = a := by
  rw [Category.assoc, h, Category.comp_id]

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

/-- **An exact functor carries the lift of a cocycle to the cycles to the lift of its image.**
Both sides are morphisms into the cycles of the image short complex, which is a subobject of the
middle term, so the two agree as soon as they agree there, and there both are the image of the
cocycle. -/
theorem map_liftCycles (S : ShortComplex C) (P : C ⥤ D) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P] {A : C} (k : A ⟶ S.X₂)
    (hk : k ≫ S.g = 0) (hk' : P.map k ≫ (S.map P).g = 0) :
    (S.map P).liftCycles (P.map k) hk' ≫ (S.mapCyclesIso P).hom = P.map (S.liftCycles k hk) := by
  refine (Iso.eq_comp_inv (S.mapCyclesIso P)).mp ?_
  rw [← cancel_mono ((S.map P).iCycles), ShortComplex.liftCycles_i, Category.assoc,
    (Iso.inv_comp_eq (S.mapCyclesIso P)).mpr (S.mapCyclesIso_hom_iCycles P).symm,
    ← P.map_comp, ShortComplex.liftCycles_i]

/-- **An exact functor commutes with the passage from a cocycle to its cohomology class.**  The
class of the image cocycle, read across `CategoryTheory.ShortComplex.mapHomologyIso`, is the
image of the class. -/
theorem map_shortComplexClass (S : ShortComplex C) (P : C ⥤ D) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P] {A : C} (k : A ⟶ S.X₂)
    (hk : k ≫ S.g = 0) (hk' : P.map k ≫ (S.map P).g = 0) :
    (S.map P).liftCycles (P.map k) hk' ≫ (S.map P).homologyπ ≫ (S.mapHomologyIso P).hom =
      P.map (S.liftCycles k hk ≫ S.homologyπ) := by
  rw [ShortComplex.homologyπ_comp_mapHomologyIso_hom, ← Category.assoc, map_liftCycles,
    P.map_comp]

/-- **`map_shortComplexClass` on a complex**: the comparison of an exact functor with the
degree-`i` cohomology of a complex carries the class of the image of a cocycle to the image of
its class. -/
theorem mapHomologicalComplex_class (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P]
    [PreservesFiniteColimits P] {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex C c)
    (i j : ι) (hj : c.next i = j) {M : C} (u : M ⟶ K.X i) (hu : u ≫ K.d i j = 0)
    (hu' : P.map u ≫ ((P.mapHomologicalComplex c).obj K).d i j = 0) :
    (((P.mapHomologicalComplex c).obj K).liftCycles (P.map u) j hj hu' ≫
          ((P.mapHomologicalComplex c).obj K).homologyπ i) ≫
        (mapHomologicalComplexHomologyIso P c i).hom.app K =
      P.map (K.liftCycles u j hj hu ≫ K.homologyπ i) :=
  (Category.assoc _ _ _).trans
    (map_shortComplexClass ((HomologicalComplex.shortComplexFunctor C c i).obj K) P u
      (by subst hj; exact hu) (by subst hj; exact hu'))

/-- **The class of a cocycle is unchanged by extending the grading.**  Read across
`HomologicalComplex.extendHomologyIso`, the class of a cocycle on the extension of a complex
along an embedding of complex shapes is the class of the cocycle it comes from. -/
theorem extend_class {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (K : HomologicalComplex C c) (e : c.Embedding c') {q : ι} {q' : ι'} (hq : e.f q = q')
    {M : C} (u : M ⟶ K.X q) (w : M ⟶ (K.extend e).X q')
    (hw : w ≫ (K.extendXIso e hq).hom = u) (j : ι) (hj : c.next q = j)
    (hu : u ≫ K.d q j = 0) (j' : ι') (hj' : c'.next q' = j')
    (hw' : w ≫ (K.extend e).d q' j' = 0) :
    ((K.extend e).liftCycles w j' hj' hw' ≫ (K.extend e).homologyπ q') ≫
        (K.extendHomologyIso e hq).hom =
      K.liftCycles u j hj hu ≫ K.homologyπ q := by
  rw [Category.assoc, HomologicalComplex.homologyπ_extendHomologyIso_hom, ← Category.assoc]
  congr 1
  rw [← cancel_mono (K.iCycles q), Category.assoc,
    HomologicalComplex.extendCyclesIso_hom_iCycles, HomologicalComplex.liftCycles_i_assoc, hw,
    HomologicalComplex.liftCycles_i]

/-- **A cocycle stays a cocycle on the extension of the grading.** -/
theorem extend_comp_d_eq_zero {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (K : HomologicalComplex C c) (e : c.Embedding c') {q : ι} {q' : ι'} (hq : e.f q = q')
    {j : ι} {j' : ι'} (hj : e.f j = j') {M : C} (u : M ⟶ K.X q) (w : M ⟶ (K.extend e).X q')
    (hw : w ≫ (K.extendXIso e hq).hom = u) (hu : u ≫ K.d q j = 0) :
    w ≫ (K.extend e).d q' j' = 0 := by
  rw [K.extend_d_eq e hq hj, ← Category.assoc, hw, ← Category.assoc, hu, zero_comp]

/-- **A functor preserving zero morphisms carries a cocycle to a cocycle.** -/
theorem map_comp_d_eq_zero (P : C ⥤ D) [P.Additive] {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex C c) (i j : ι) {M : C} (u : M ⟶ K.X i) (hu : u ≫ K.d i j = 0) :
    P.map u ≫ ((P.mapHomologicalComplex c).obj K).d i j = 0 := by
  rw [Functor.mapHomologicalComplex_obj_d, ← P.map_comp, hu, P.map_zero]

/-- **A morphism of complexes carries a cocycle to a cocycle.** -/
theorem comp_f_comp_d_eq_zero {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c}
    (ψ : K ⟶ L) (i j : ι) {M : C} (u : M ⟶ K.X i) (hu : u ≫ K.d i j = 0) :
    (u ≫ ψ.f i) ≫ L.d i j = 0 := by
  rw [Category.assoc, ψ.comm, ← Category.assoc, hu, zero_comp]

/-- **A morphism of complexes carries the class of a cocycle to the class of its image.** -/
theorem class_comp_homologyMap {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c}
    (ψ : K ⟶ L) (i j : ι) (hj : c.next i = j) {M : C} (u : M ⟶ K.X i)
    (hu : u ≫ K.d i j = 0) (hu' : (u ≫ ψ.f i) ≫ L.d i j = 0) :
    (K.liftCycles u j hj hu ≫ K.homologyπ i) ≫ HomologicalComplex.homologyMap ψ i =
      L.liftCycles (u ≫ ψ.f i) j hj hu' ≫ L.homologyπ i := by
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc]
  congr 1
  rw [← cancel_mono (L.iCycles i), Category.assoc, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.liftCycles_i, ← Category.assoc, HomologicalComplex.liftCycles_i]

end General

/-! ### The degreewise reading of the comparison of the two extended Čech complexes -/

section Degreewise

variable {X X' : Scheme.{u}} (g : X' ⟶ X) [IsOpenImmersion g] {m : ℕ}
  (e : Fin m → Γ(X, ⊤)) (F : X.Modules)

/-- **In a positive degree the comparison of the two extended alternating Čech complexes is the
degreewise comparison `Stacks.Perfect.PushforwardRestrict.restrictProdTermIso`.**  The complex of
[Stacks, Tag 0G7I] has the identity as its identification of the degree-`(p+1)` term with the
product of the direct images, so the comparison of the two specifications reduces to the
comparison of the products. -/
theorem restrictCplxIso_hom_f_succ (p : ℕ) :
    (restrictCplxIso g e F).hom.f (p + 1) = (restrictProdTermIso e g F p).hom := by
  change ((Scheme.Modules.restrictFunctor g).map (Iso.refl (prodTerm e F p)).hom ≫
    (restrictProdTermIso e g F p).hom) ≫ (Iso.refl _).inv = _
  rw [Iso.refl_hom, (Scheme.Modules.restrictFunctor g).map_id, Category.id_comp,
    Iso.refl_inv, Category.comp_id]

/-- The chase behind `restrictExtendIso_hom_f_succ`, at a variable category. -/
private theorem chaseCancelPair {V : Type*} [Category* V] {oa ob oc od oe : V}
    (x : ob ⟶ oc) (y : oc ⟶ oa) (b : oa ⟶ ob) (bi : ob ⟶ oa) (t : ob ⟶ od)
    (ci : od ⟶ oe) (ch : oe ⟶ od)
    (h1 : b ≫ x ≫ y = 𝟙 oa) (h2 : bi ≫ b = 𝟙 ob) (h3 : ci ≫ ch = 𝟙 od) :
    x ≫ (y ≫ b ≫ t ≫ ci) ≫ ch = t := by
  have hxy : x ≫ y = bi := by
    rw [← Category.id_comp (x ≫ y), ← h2, Category.assoc, h1, Category.comp_id]
  simp only [Category.assoc]
  rw [← Category.assoc x y, hxy, ← Category.assoc bi b, h2, Category.id_comp, h3,
    Category.comp_id]

/-- **In every degree the comparison `restrictExtendIso` of [Stacks, Tag 0G7U] is the comparison
`restrictCplxIso` of the unextended complexes**, read through the canonical identifications of the
terms of the two extended complexes with the terms they come from.  The two comparisons of
extension with the degreewise functor cancel against those identifications.

The degree is arbitrary: nothing here looks at the term, only at the two cancellations, so this
holds in degree `0` as well as in a positive one.  `restrictExtendIso_hom_f_succ` below is this
composed with the positive-degree value of `restrictCplxIso`, and
`Stacks.Perfect.CechDerivedSupportImmersion.restrictCplxIso_hom_f_zero` gives the degree-`0`
value, which is where the coefficient module sits. -/
theorem restrictExtendIso_hom_f (n : ℕ) :
    (Scheme.Modules.restrictFunctor g).map
          (((cplx e F).extendXIso ComplexShape.embeddingUpNat
            (embeddingUpNat_f n)).inv) ≫
        (restrictExtendIso g e F).hom.f ((n : ℕ) : ℤ) ≫
          ((cplx (fun j => g.appTop (e j))
              ((Scheme.Modules.restrictFunctor g).obj F)).extendXIso
            ComplexShape.embeddingUpNat (embeddingUpNat_f n)).hom =
      (restrictCplxIso g e F).hom.f n := by
  have h1 := HomologicalComplex.congr_hom
    (HomologicalComplex.mapHomologicalComplexExtendIso (Scheme.Modules.restrictFunctor g)
      (cplx e F) ComplexShape.embeddingUpNat).hom_inv_id (((n : ℕ) : ℤ))
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    HomologicalComplex.mapHomologicalComplexExtendIso_hom_f _ _ _
      (embeddingUpNat_f n), Category.assoc] at h1
  refine Eq.trans (congrArg (fun z => (Scheme.Modules.restrictFunctor g).map
      (((cplx e F).extendXIso ComplexShape.embeddingUpNat
        (embeddingUpNat_f n)).inv) ≫ z ≫ _)
    (congrArg (fun ψ : _ ⟶ _ => HomologicalComplex.Hom.f ψ (((n : ℕ) : ℤ)))
      (restrictExtendIso_hom g e F))) ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.extendMap_f _ _
    (embeddingUpNat_f n)]
  exact chaseCancelPair _ _ _ _ _ _ _ h1
    ((((Scheme.Modules.restrictFunctor g).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (cplx e F)).extendXIso ComplexShape.embeddingUpNat
        (embeddingUpNat_f n)).inv_hom_id
    ((cplx (fun j => g.appTop (e j))
        ((Scheme.Modules.restrictFunctor g).obj F)).extendXIso
      ComplexShape.embeddingUpNat (embeddingUpNat_f n)).inv_hom_id

/-- **In a positive degree the comparison `restrictExtendIso` of [Stacks, Tag 0G7U] is
`restrictProdTermIso`**, read through the canonical identifications of the terms of the two
extended complexes with the terms they come from.  This is `restrictExtendIso_hom_f` followed by
the positive-degree value `restrictCplxIso_hom_f_succ` of the comparison of the unextended
complexes. -/
theorem restrictExtendIso_hom_f_succ (p : ℕ) :
    (Scheme.Modules.restrictFunctor g).map
          (((cplx e F).extendXIso ComplexShape.embeddingUpNat
            (embeddingUpNat_f (p + 1))).inv) ≫
        (restrictExtendIso g e F).hom.f ((p + 1 : ℕ) : ℤ) ≫
          ((cplx (fun j => g.appTop (e j))
              ((Scheme.Modules.restrictFunctor g).obj F)).extendXIso
            ComplexShape.embeddingUpNat (embeddingUpNat_f (p + 1))).hom =
      (restrictProdTermIso e g F p).hom :=
  (restrictExtendIso_hom_f g e F (p + 1)).trans (restrictCplxIso_hom_f_succ g e F p)

end Degreewise

/-! ### The Čech cohomology class of a cocycle is local -/

section Cocycle

variable {X X' : Scheme.{u}} (g : X' ⟶ X) [IsOpenImmersion g] {m : ℕ}
  (e : Fin m → Γ(X, ⊤)) (F : X.Modules)
  [F.IsQuasicoherent]

/-- Re-associating a composite of four morphisms, at a variable category. -/
private theorem chaseAssoc4 {V : Type*} [Category* V] {o₁ o₂ o₃ o₄ o₅ : V}
    (a : o₁ ⟶ o₂) (b : o₂ ⟶ o₃) (c : o₃ ⟶ o₄) (d : o₄ ⟶ o₅) (t : o₂ ⟶ o₅)
    (h : b ≫ c ≫ d = t) : ((a ≫ b) ≫ c) ≫ d = a ≫ t := by
  simp only [Category.assoc]
  rw [h]

omit [SheafOfModules.IsQuasicoherent F] in
/-- `Stacks.Gysin.cechHomologyImmersionIso`, factor by factor. -/
theorem cechHomologyImmersionIso_hom (p : ℕ) :
    (cechHomologyImmersionIso g e F p).hom =
      (Scheme.Modules.restrictFunctor g).map
          (HomologicalComplex.extendHomologyIso (cplx e F) ComplexShape.embeddingUpNat
            (embeddingUpNat_f p)).inv ≫
        (cechExtendHomologyImmersionIso g e F (p : ℤ)).hom ≫
          (HomologicalComplex.extendHomologyIso
              (cplx (fun j => g.appTop (e j)) ((Scheme.Modules.restrictFunctor g).obj F))
            ComplexShape.embeddingUpNat (embeddingUpNat_f p)).hom := rfl

/-- The chase behind `map_cechCocycleClass_comp_cechHomologyImmersionIso`, at a variable
category: four successive identifications of a class with a class. -/
private theorem assembleClass {V : Type*} [Category* V] {o₁ o₂ o₃ o₄ o₅ o₆ : V}
    (cls : o₁ ⟶ o₂) (ei : o₂ ⟶ o₃) (mi : o₃ ⟶ o₄) (hm : o₄ ⟶ o₅) (eh : o₅ ⟶ o₆)
    (cls₂ : o₁ ⟶ o₃) (cls₃ : o₁ ⟶ o₄) (cls₄ : o₁ ⟶ o₅) (cls₅ : o₁ ⟶ o₆)
    (h₁ : cls ≫ ei = cls₂) (h₂ : cls₂ ≫ mi = cls₃) (h₃ : cls₃ ≫ hm = cls₄)
    (h₄ : cls₄ ≫ eh = cls₅) :
    cls ≫ ei ≫ (mi ≫ hm) ≫ eh = cls₅ := by
  simp only [Category.assoc]
  rw [← Category.assoc, h₁, ← Category.assoc, h₂, ← Category.assoc, h₃, h₄]

omit [SheafOfModules.IsQuasicoherent F] in
/-- **Base change of the degree-`n` Čech cohomology class of a cocycle along an open immersion,
in every degree.**  The restriction along `g` of the class of a cocycle `u` on the extended
alternating Čech complex of [Stacks, Tag 0G7I], read across
`Stacks.Gysin.cechHomologyImmersionIso`, is the class of the restricted cocycle for the restricted
equations.

The degree is arbitrary, `0` included.  Everything the proof uses is degree-generic: the four
steps `extend_class`, `mapHomologicalComplex_class`, `class_comp_homologyMap` and `extend_class`
again are stated for an abstract complex shape and an abstract degree, and the comparison of the
extended complexes is `restrictExtendIso_hom_f`, which holds in every degree.  What the
positive-degree reading `map_cechCocycleClass_comp_cechHomologyImmersionIso` below adds is only
the identification of the degree-`(p+1)` term with `Stacks.Perfect.SupportedFraction.prodTerm`;
in degree `0` the term is the coefficient module instead, which is why that reading cannot be
used at `c = 0` and this one can. -/
theorem map_cocycleClass_comp_cechHomologyImmersionIso (n : ℕ) {M : X.Modules}
    (u : M ⟶ (cplx e F).X n) (hu : u ≫ (cplx e F).d n (n + 1) = 0)
    (hu' : ((Scheme.Modules.restrictFunctor g).map u ≫ (restrictCplxIso g e F).hom.f n) ≫
      (cplx (fun j => g.appTop (e j))
        ((Scheme.Modules.restrictFunctor g).obj F)).d n (n + 1) = 0) :
    (Scheme.Modules.restrictFunctor g).map
          (cocycleClass (K := cplx e F) (CochainComplex.next ℕ n) u hu) ≫
        (cechHomologyImmersionIso g e F n).hom =
      cocycleClass (K := cplx (fun j => g.appTop (e j))
          ((Scheme.Modules.restrictFunctor g).obj F)) (CochainComplex.next ℕ n)
        ((Scheme.Modules.restrictFunctor g).map u ≫ (restrictCplxIso g e F).hom.f n) hu' := by
  have hnext : ComplexShape.embeddingUpNat.f (n + 1) = ((n : ℕ) : ℤ) + 1 := by
    rw [embeddingUpNat_f]; push_cast; ring
  have hwz : (((Scheme.Modules.restrictFunctor g).map
          (u ≫ ((cplx e F).extendXIso ComplexShape.embeddingUpNat
            (embeddingUpNat_f n)).inv) ≫
        (restrictExtendIso g e F).hom.f ((n : ℕ) : ℤ)) ≫
      ((cplx (fun j => g.appTop (e j))
            ((Scheme.Modules.restrictFunctor g).obj F)).extendXIso
        ComplexShape.embeddingUpNat (embeddingUpNat_f n)).hom) =
      (Scheme.Modules.restrictFunctor g).map u ≫ (restrictCplxIso g e F).hom.f n := by
    refine Eq.trans (congrArg (fun z =>
        (z ≫ (restrictExtendIso g e F).hom.f ((n : ℕ) : ℤ)) ≫
          ((cplx (fun j => g.appTop (e j))
                ((Scheme.Modules.restrictFunctor g).obj F)).extendXIso
            ComplexShape.embeddingUpNat (embeddingUpNat_f n)).hom)
      ((Scheme.Modules.restrictFunctor g).map_comp u _)) ?_
    exact chaseAssoc4 _ _ _ _ _ (restrictExtendIso_hom_f g e F n)
  have hzero := extend_comp_d_eq_zero (cplx e F) ComplexShape.embeddingUpNat
    (embeddingUpNat_f n) hnext u
    (u ≫ ((cplx e F).extendXIso ComplexShape.embeddingUpNat (embeddingUpNat_f n)).inv)
    (invHomCancel u _ _ (Iso.inv_hom_id _)) hu
  have hzero' := map_comp_d_eq_zero (Scheme.Modules.restrictFunctor g) (ComplexShape.up ℤ) _ _ _ _
    hzero
  have hzero'' := comp_f_comp_d_eq_zero (restrictExtendIso g e F).hom _ _ _ hzero'
  have h₁ := Eq.trans ((Scheme.Modules.restrictFunctor g).map_comp
      (cocycleClass (K := cplx e F) (CochainComplex.next ℕ n) u hu)
      (HomologicalComplex.extendHomologyIso (cplx e F)
        ComplexShape.embeddingUpNat (embeddingUpNat_f n)).inv).symm
    (congrArg (Scheme.Modules.restrictFunctor g).map
      ((Iso.comp_inv_eq (HomologicalComplex.extendHomologyIso (cplx e F)
          ComplexShape.embeddingUpNat (embeddingUpNat_f n))).mpr
        (extend_class (cplx e F) ComplexShape.embeddingUpNat (embeddingUpNat_f n) u _
          (invHomCancel u _ _ (Iso.inv_hom_id _)) (n + 1)
          (CochainComplex.next ℕ n) hu
          (((n : ℕ) : ℤ) + 1) (CochainComplex.next ℤ ((n : ℕ) : ℤ)) hzero).symm))
  have h₂ := (Iso.comp_inv_eq ((mapHomologicalComplexHomologyIso
      (Scheme.Modules.restrictFunctor g) (ComplexShape.up ℤ)
        ((n : ℕ) : ℤ)).app ((cplx e F).extend ComplexShape.embeddingUpNat))).mpr
    (mapHomologicalComplex_class (Scheme.Modules.restrictFunctor g) (ComplexShape.up ℤ)
      ((cplx e F).extend ComplexShape.embeddingUpNat) ((n : ℕ) : ℤ)
      (((n : ℕ) : ℤ) + 1) (CochainComplex.next ℤ ((n : ℕ) : ℤ)) _ hzero hzero').symm
  have h₃ := class_comp_homologyMap (restrictExtendIso g e F).hom ((n : ℕ) : ℤ)
    (((n : ℕ) : ℤ) + 1) (CochainComplex.next ℤ ((n : ℕ) : ℤ)) _ hzero' hzero''
  have h₄ := extend_class (cplx (fun j => g.appTop (e j))
      ((Scheme.Modules.restrictFunctor g).obj F)) ComplexShape.embeddingUpNat
    (embeddingUpNat_f n) _ _ hwz (n + 1) (CochainComplex.next ℕ n) hu'
    (((n : ℕ) : ℤ) + 1) (CochainComplex.next ℤ ((n : ℕ) : ℤ)) hzero''
  rw [cechHomologyImmersionIso_hom, cechExtendHomologyImmersionIso_hom]
  exact assembleClass _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄

omit [SheafOfModules.IsQuasicoherent F] in
/-- **Base change of the degree-`(p+1)` Čech cohomology class of a cocycle along an open
immersion.**  The restriction along `g` of the class of a cocycle `u` on the extended alternating
Čech complex of [Stacks, Tag 0G7I], read across `Stacks.Gysin.cechHomologyRestrictIso`, is the
class of the restricted cocycle for the restricted equations.

This is the remaining factor of [Stacks, Tag 0G7U] for an open immersion: its companion, the
base change of the comparison of [Stacks, Tag 0G7L] in degree `p`, is
`Stacks.Gysin.map_cechHomologyToSupport_comp_supportCohomologyRestrictIso`. -/
theorem map_cechCocycleClass_comp_cechHomologyImmersionIso (p : ℕ) {M : X.Modules}
    (u : M ⟶ prodTerm e F p) (hu : u ≫ difSucc e F p = 0)
    (hu' : ((Scheme.Modules.restrictFunctor g).map u ≫ (restrictProdTermIso e g F p).hom) ≫
      difSucc (fun j => g.appTop (e j))
        ((Scheme.Modules.restrictFunctor g).obj F) p = 0) :
    (Scheme.Modules.restrictFunctor g).map (cechCocycleClass e F p u hu) ≫
        (cechHomologyImmersionIso g e F (p + 1)).hom =
      cechCocycleClass (fun j => g.appTop (e j))
        ((Scheme.Modules.restrictFunctor g).obj F) p
        ((Scheme.Modules.restrictFunctor g).map u ≫ (restrictProdTermIso e g F p).hom) hu' :=
  Eq.trans
    (map_cocycleClass_comp_cechHomologyImmersionIso g e F (p + 1) u
      (comp_cplx_d_succ e F p u hu)
      ((restrictCplxIso_hom_f_succ g e F p).symm ▸
        comp_cplx_d_succ (fun j => g.appTop (e j))
          ((Scheme.Modules.restrictFunctor g).obj F) p _ hu'))
    (cocycleClass_congr (CochainComplex.next ℕ (p + 1)) _ _
      (congrArg (fun z => (Scheme.Modules.restrictFunctor g).map u ≫ z)
        (restrictCplxIso_hom_f_succ g e F p)))

end Cocycle

/-! ### The class map of Tag 0G7Q is local -/

section ClassMap

variable {X X' : Scheme.{u}} (g : X' ⟶ X) [IsOpenImmersion g] (F : X.Modules)
  [F.IsQuasicoherent]

/-- Composing two carried factors, at a variable category. -/
private theorem chaseTwoFactors {V : Type*} [Category* V] {o₁ o₂ o₃ o₄ o₅ : V}
    (a : o₁ ⟶ o₂) (b : o₂ ⟶ o₃) (c : o₃ ⟶ o₄) (r : o₂ ⟶ o₅) (s : o₅ ⟶ o₄) (t : o₁ ⟶ o₅)
    (hA : b ≫ c = r ≫ s) (hB : a ≫ r = t) : (a ≫ b) ≫ c = t ≫ s := by
  rw [Category.assoc, hA, ← Category.assoc, hB]

/-- **Stacks Project, Tag 0G7U for an open immersion, read on the coefficient module: the class
map of [Stacks, Tag 0G7Q] is local.**  The restriction along `g` of the canonical map
`ℱ ⟶ i_*ℋ^c_T(ℱ)`, followed by the excision isomorphism of [Stacks, Tag 0G78] on degree-`c`
cohomology sheaves, is the canonical map of the restricted equations with coefficients in `g^*ℱ`.

Both factors of `Stacks.Perfect.SupportedFraction.supportedFractionSource_eq` are carried: the
cohomology class of the fraction cochain by
`map_cechCocycleClass_comp_cechHomologyImmersionIso` — whose cochain half is
`Stacks.Perfect.PushforwardRestrict.restrictFunctor_map_fractionHom` — and the comparison of
[Stacks, Tag 0G7L] in degree `c` by
`map_cechHomologyToSupport_comp_supportCohomologyOpenImmersionIso`. -/
theorem map_supportedFractionSource_comp_supportCohomologyRestrictIso {d : ℕ}
    (f : Fin (d + 1) → Γ(X, ⊤)) {T : Set X} (hT : IsClosed T)
    (hTf : equationsClosedSet f ⊆ T) (hT' : IsClosed (restrictClosedSubset g T))
    (hTf' : equationsClosedSet (fun j => g.appTop (f j)) ⊆ restrictClosedSubset g T) :
    (Scheme.Modules.restrictFunctor g).map (supportedFractionSource f F hT hTf) ≫
        (supportCohomologyOpenImmersionIso g hT hT' ((d + 1 : ℕ) : ℤ) F).hom =
      supportedFractionSource (fun j => g.appTop (f j))
        ((Scheme.Modules.restrictFunctor g).obj F) hT' hTf' := by
  rw [supportedFractionSource_eq f F hT hTf, supportedFractionSource_eq, Functor.map_comp]
  exact chaseTwoFactors _ _ _ _ _ _
    (map_cechHomologyToSupport_comp_supportCohomologyOpenImmersionIso g f F hT hTf hT' hTf'
      (d + 1))
    ((map_cechCocycleClass_comp_cechHomologyImmersionIso g f F d (fractionHom f F d)
        (comp_difSucc_top f F (fractionHom f F d))
        (comp_difSucc_top (fun j => g.appTop (f j))
          ((Scheme.Modules.restrictFunctor g).obj F) _)).trans
      (cechCocycleClass_congr (fun j => g.appTop (f j))
        ((Scheme.Modules.restrictFunctor g).obj F) d _ _
        (restrictFunctor_map_fractionHom f g F d)))

end ClassMap

end Stacks.Gysin

end
