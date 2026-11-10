module

public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.RingSystemHomotopy
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapNaturality

/-!
# Maps of chosen derived extensions of scalars, from maps of complexes over the base ring

Let `f : R ⟶ A` be a map of commutative rings and let `P`, `N` be K-flat complexes of
`R`-modules.  The chosen total derived extension of scalars
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` computes `P ⊗^𝐋_R A` and
`N ⊗^𝐋_R A` as the termwise extensions of scalars, so a morphism `P ⟶ A ⊗_R N` of the homotopy
category of `R`-modules transposes, along the adjunction of extension and restriction of scalars,
to a morphism

`P ⊗^𝐋_R A ⟶ N ⊗^𝐋_R A`

of `D(A)`.  This file constructs that map, proves it bijective when `A ⊗_R P` is K-projective,
and proves that it carries post-composition with the base-change map `A ⊗_R N ⟶ A' ⊗_R N` of a
factorisation `f ≫ β = f'` to the conjugation, by the composition law of the chosen derived
extensions of scalars, of the derived extension of scalars along `β`.

## Main definitions

* `Stacks.LimitHomDescent.Affine.totalDerivedExtensionScalarsKFlatIso`: at a K-flat complex the
  chosen derived extension of scalars is the termwise one.
* `Stacks.LimitHomDescent.Affine.totalDerivedTranspose`: the map
  `Hom_{K(R)}(P, A ⊗_R N) ⟶ Hom_{D(A)}(P ⊗^𝐋_R A, N ⊗^𝐋_R A)`.

## Main results

* `Stacks.LimitHomDescent.Affine.totalDerivedTranspose_bijective`: it is bijective when
  `A ⊗_R P` is K-projective.
* `Stacks.LimitHomDescent.Affine.totalDerivedTranspose_comp_tau`: it carries the base-change map
  of a factorisation to conjugation by the composition law of derived extensions of scalars.

## References

* [Stacks Project, Lemma 36.29.2 (Tag 09RE)](https://stacks.math.columbia.edu/tag/09RE)
* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.FilteredColimitHom (Qh)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.LimitHomDescent.Affine

variable {R A A' : CommRingCat.{u}}

/-- The comparison of the chosen derived extension of scalars with the termwise one at a complex,
with its target written as the localization of `Stacks.LimitHomDescent.Affine.ext`. -/
def totalDerivedExtensionScalarsComparison (f : R ⟶ A) (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        f.hom).functor.obj (DerivedCategory.Q.obj C) ⟶
      DerivedCategory.Q.obj ((ext f).obj C) :=
  (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    f.hom).comparison.app C

/-- The comparison `totalDerivedExtensionScalarsComparison` is natural in the complex. -/
@[reassoc]
theorem totalDerivedExtensionScalarsComparison_naturality (f : R ⟶ A)
    {C C' : CochainComplex (ModuleCat.{u} R) ℤ} (φ : C ⟶ C') :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        f.hom).functor.map (DerivedCategory.Q.map φ) ≫
      totalDerivedExtensionScalarsComparison f C' =
      totalDerivedExtensionScalarsComparison f C ≫ DerivedCategory.Q.map ((ext f).map φ) :=
  (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    f.hom).comparison.naturality φ

/-- **At a K-flat complex the chosen derived extension of scalars is the termwise one**:
`C ⊗^𝐋_R A ≅ A ⊗_R C` in `D(A)`, given by the comparison map, which is invertible at K-flat
complexes. -/
def totalDerivedExtensionScalarsKFlatIso (f : R ⟶ A) (C : CochainComplex (ModuleCat.{u} R) ℤ)
    (hC : C.KFlat) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        f.hom).functor.obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj ((ext f).obj C) :=
  @asIso _ _ _ _
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      f.hom).comparison.app C)
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      f.hom).comparison_isIso_of_kFlat C hC)

/-- The forward map of `totalDerivedExtensionScalarsKFlatIso` is the comparison map. -/
@[simp]
theorem totalDerivedExtensionScalarsKFlatIso_hom (f : R ⟶ A)
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (hC : C.KFlat) :
    (totalDerivedExtensionScalarsKFlatIso f C hC).hom =
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        f.hom).comparison.app C :=
  rfl

variable (P N : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) (hN : N.KFlat)

/-- **`Hom_{K(R)}(P, A ⊗_R N) ⟶ Hom_{D(A)}(P ⊗^𝐋_R A, N ⊗^𝐋_R A)`**: transpose along extension of
scalars, pass to the derived category of `A`, and read the result through the identification
`Stacks.LimitHomDescent.Affine.totalDerivedExtensionScalarsKFlatIso` of the chosen derived
extension of scalars with the termwise one. -/
def totalDerivedTranspose (f : R ⟶ A)
    (ψ : (Qh R).obj P ⟶
      (Qh R).obj (((resExt f).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        f.hom).functor.obj (DerivedCategory.Q.obj P) ⟶
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        f.hom).functor.obj (DerivedCategory.Q.obj N) :=
  (totalDerivedExtensionScalarsKFlatIso f P hP).hom ≫
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).inv.app ((ext f).obj P) ≫
      DerivedCategory.Qh.map (((Adjunction.mapHomotopyCategoryAdjunction
        (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom) (ComplexShape.up ℤ)).homEquiv
          ((Qh R).obj P) ((Qh A).obj ((ext f).obj N))).symm ψ) ≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.app ((ext f).obj N)) ≫
    (totalDerivedExtensionScalarsKFlatIso f N hN).inv

/-- On the class of a map of complexes, `totalDerivedTranspose` is the localization of its
transpose. -/
theorem totalDerivedTranspose_quot (f : R ⟶ A)
    (g : P ⟶ ((resExt f).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) :
    totalDerivedTranspose P N hP hN f ((Qh R).map g) =
      (totalDerivedExtensionScalarsKFlatIso f P hP).hom ≫
        DerivedCategory.Q.map (transposeCx f (Z := (ext f).obj N) g) ≫
        (totalDerivedExtensionScalarsKFlatIso f N hN).inv := by
  unfold totalDerivedTranspose
  exact congrArg (fun z => (totalDerivedExtensionScalarsKFlatIso f P hP).hom ≫ z ≫
    (totalDerivedExtensionScalarsKFlatIso f N hN).inv)
    (quotientCompQhIso_conj (transposeCx f (Z := (ext f).obj N) g))

/-- **`totalDerivedTranspose` is bijective** when `A ⊗_R P` is K-projective. -/
theorem totalDerivedTranspose_bijective (f : R ⟶ A) [((ext f).obj P).IsKProjective] :
    Function.Bijective (totalDerivedTranspose P N hP hN f) := by
  have h1 := ((Adjunction.mapHomotopyCategoryAdjunction
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom) (ComplexShape.up ℤ)).homEquiv
      ((Qh R).obj P) ((Qh A).obj ((ext f).obj N))).symm.bijective
  have h2 := CochainComplex.IsKProjective.Qh_map_bijective ((ext f).obj P)
    ((Qh A).obj ((ext f).obj N))
  have h3 := (Iso.homCongr ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app
    ((ext f).obj P)) ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app
      ((ext f).obj N))).bijective
  have h5 := (Iso.homCongr (totalDerivedExtensionScalarsKFlatIso f P hP).symm
    (totalDerivedExtensionScalarsKFlatIso f N hN).symm).bijective
  exact h5.comp (h3.comp (h2.comp h1))

/-- The degreewise composition isomorphism of extensions of scalars along a factorisation is the
cast composition isomorphism `RingTheory.TorIndependence.extendScalarsCompInvOfEq`. -/
theorem extCompIsoOf_hom_eq (f : R ⟶ A) (β : A ⟶ A') (f' : R ⟶ A') (h : f ≫ β = f')
    (hc : β.hom.comp f.hom = f'.hom) (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    (extCompIsoOf f β f' h C).hom =
      (NatTrans.mapHomologicalComplex
        (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{u, u, u, u} f.hom β.hom f'.hom hc)
        (ComplexShape.up ℤ)).app C := by
  subst h
  ext n : 1
  simp only [extCompIsoOf, extComp, RingTheory.TorIndependence.extendScalarsCompInvOfEq,
    RingTheory.TorIndependence.modelComp_extendScalarsComp_eq, Iso.trans_hom, eqToIso_refl,
    Iso.refl_hom, Category.comp_id, eqToHom_refl]
  rfl

/-- **`totalDerivedTranspose` carries the base-change map of a factorisation `f ≫ β = f'` to
conjugation by the composition law of the chosen derived extensions of scalars.**  For
`ψ : P ⟶ A ⊗_R N` in the homotopy category,

`(ψ ≫ τ)^♯ = c_P⁻¹ ≫ Lβ^*(ψ^♯) ≫ c_N`,

where `τ : A ⊗_R N ⟶ A' ⊗_R N` is the base-change map and `c` the composition isomorphism
`RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq` of the chosen models. -/
theorem totalDerivedTranspose_comp_tau (f : R ⟶ A) (f' : R ⟶ A') (β : A ⟶ A')
    (h : f ≫ β = f') (hc : β.hom.comp f.hom = f'.hom)
    (ψ : (Qh R).obj P ⟶
      (Qh R).obj (((resExt f).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) :
    totalDerivedTranspose P N hP hN f' (ψ ≫ (Qh R).map
        ((NatTrans.mapHomologicalComplex (tau f f' β h) (ComplexShape.up ℤ)).app N)) =
      (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq f.hom β.hom f'.hom
          hc).inv.app (DerivedCategory.Q.obj P) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          β.hom).functor.map (totalDerivedTranspose P N hP hN f ψ) ≫
        (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq f.hom β.hom f'.hom
          hc).hom.app (DerivedCategory.Q.obj N) := by
  obtain ⟨g, rfl⟩ := (Qh R).map_surjective ψ
  rw [← Functor.map_comp, totalDerivedTranspose_quot, totalDerivedTranspose_quot,
    transposeCx_comp_tau]
  have hnat := totalDerivedExtensionScalarsComparison_naturality β
    (transposeCx f (Z := (ext f).obj N) g)
  have hc' : ∀ X : CochainComplex (ModuleCat.{u} R) ℤ, ∀ hX : X.KFlat,
      (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq f.hom β.hom f'.hom
          hc).hom.app (DerivedCategory.Q.obj X) ≫
        (totalDerivedExtensionScalarsKFlatIso f' X hX).hom =
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          β.hom).functor.map (totalDerivedExtensionScalarsKFlatIso f X hX).hom ≫
        totalDerivedExtensionScalarsComparison β ((ext f).obj X) ≫
        DerivedCategory.Q.map (extCompIsoOf f β f' h X).hom := fun X _ => by
    rw [extCompIsoOf_hom_eq f β f' h hc]
    exact RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq_hom_app_comparison
      f.hom β.hom f'.hom hc X
  rw [← cancel_epi ((RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq f.hom β.hom
      f'.hom hc).hom.app (DerivedCategory.Q.obj P)),
    ← cancel_mono (totalDerivedExtensionScalarsKFlatIso f' N hN).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_app_assoc,
    Functor.map_comp]
  rw [reassoc_of% (hc' P hP), hc' N hN, Iso.inv_hom_id_map_assoc]
  simp only [Iso.hom_inv_id_map_assoc]
  exact congrArg (_ ≫ ·) ((reassoc_of% hnat) _).symm

end Stacks.LimitHomDescent.Affine

end
