module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksCore.Algebra.Homology.QuasiIso
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietorisAndHom.HomComplexMaps

/-!
# Derived internal Hom on a ringed site is well defined

Let `(C, O)` be a ringed site. If `l : L' ⟶ L` is a quasi-isomorphism of complexes of
`O`-modules and `i : I' ⟶ I` is a quasi-isomorphism between K-injective complexes, then the
induced map `SheafHom(L, I') ⟶ SheafHom(L', I)` of internal Hom complexes is a
quasi-isomorphism. This is what makes the derived internal Hom well defined.

The proof is local. Over an object `U` of the site, the sections of an internal Hom complex are
Mathlib's `CochainComplex.HomComplex` of the restrictions to the slice site over `U`, and the
induced map is, under that identification, the ordinary map of Hom complexes given by pre- and
postcomposition. For ordinary Hom complexes the statement is a computation with cohomology
classes: `CochainComplex.HomComplex.CohomologyClass.homAddEquiv` identifies the cohomology of
the Hom complex with morphisms in the homotopy category, and there pre- and postcomposition with
the images of `l` and `i` are bijections, because `i` becomes invertible and `L` is left
orthogonal to the shifts of a K-injective complex. Being a quasi-isomorphism on the sections
over every object is being a quasi-isomorphism of presheaves, and sheafification is exact, so
it follows for the sheaves of modules themselves.

## Main results

* `Stacks.Cohomology.InternalHom.sheafHomComplexMap_quasiIso`: the canonical map of internal
  Hom complexes induced by quasi-isomorphisms in both variables, with K-injective complexes in
  the covariant variable, is a quasi-isomorphism.

## Implementation notes

The statement is about the canonical map `sheafHomComplexMap` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/MayerVietorisAndHom/HomComplexMaps.lean`,
not about an arbitrary morphism between realizations of the internal Hom complex; its local
description `SheafHomComplexConstruction.map_isInduced` is what the proof uses to compare it
with Mathlib's map of Hom complexes.

Restriction to a slice site is additive and exact and preserves K-injectivity, so the
restrictions of `l` and `i` are again quasi-isomorphisms between complexes of the right kind;
those three facts are
`SheafOfModules.overFunctor_additive`, `Stacks.Cohomology.Localization.restriction_exact` and
`Stacks.Cohomology.Localization.isKInjective_over`.

## References

* [Stacks Project, Tag 0A95](https://stacks.math.columbia.edu/tag/0A95)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSite
open CochainComplex CochainComplex.HomComplex

universe v u

namespace Stacks.Cohomology.InternalHom

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K' K I' I : CochainComplex C ℤ} (f : K' ⟶ K) (g : I' ⟶ I)

/-- Pre- and postcomposition on cochains between complexes of an abelian category. -/
private def inducedCochainMap (n : ℤ) : Cochain K I' n →+ Cochain K' I n where
  toFun z := (Cochain.ofHom f).comp
    ((z : Cochain K I' n).comp (Cochain.ofHom g) (add_zero n)) (zero_add n)
  map_zero' := by simp
  map_add' z z' := by simp [Cochain.comp_add]

private theorem inducedCochainMap_v (n p q : ℤ) (hpq : p + n = q) (z : Cochain K I' n) :
    (inducedCochainMap f g n z).v p q hpq = f.f p ≫ z.v p q hpq ≫ g.f q := by
  simp [inducedCochainMap, Cochain.zero_cochain_comp_v,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v]

/-- Pre- and postcomposition as a map of Hom complexes. -/
private def inducedHomComplexMap : (K.HomComplex I') ⟶ (K'.HomComplex I) where
  f n := AddCommGrpCat.ofHom (inducedCochainMap f g n)
  comm' := by
    intro n m hnm
    ext z
    change δ n m ((Cochain.ofHom f).comp
        ((z : Cochain K I' n).comp (Cochain.ofHom g) (add_zero n)) (zero_add n)) =
      (Cochain.ofHom f).comp ((δ n m z).comp (Cochain.ofHom g) (add_zero m)) (zero_add m)
    rw [δ_ofHom_comp, δ_comp_ofHom (z₁ := (z : Cochain K I' n)) (f := g) (m := m)]

private theorem inducedCochainMap_comm (n m : ℤ) (z : Cochain K I' n) :
    inducedCochainMap f g m (δ n m z) = δ n m (inducedCochainMap f g n z) :=
  (ConcreteCategory.congr_hom ((inducedHomComplexMap f g).comm n m) z).symm

private def inducedCocycleMap (n : ℤ) : Cocycle K I' n →+ Cocycle K' I n where
  toFun z := (z.postcomp g).precomp f
  map_zero' := by ext; simp
  map_add' z z' := by ext; simp [Cochain.comp_add]

private def inducedClassMap (n : ℤ) : CohomologyClass K I' n →+ CohomologyClass K' I n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K' I n).comp (inducedCocycleMap f g n)) (by
      intro z hz
      change CohomologyClass.mk ((inducedCocycleMap f g n) z) = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      obtain ⟨m, hm, β, hβ⟩ := hz
      refine ⟨m, hm, inducedCochainMap f g m β, ?_⟩
      change δ m n (inducedCochainMap f g m β) = inducedCochainMap f g n (z : Cochain K I' n)
      rw [← inducedCochainMap_comm f g m n β, hβ])

private theorem precomp_bijective {D : Type*} [Category D] {A B : D}
    (f : A ⟶ B) [IsIso f] (T : D) :
    Function.Bijective (fun g : B ⟶ T => f ≫ g) :=
  ⟨fun _ _ h => (cancel_epi f).1 h, fun g => ⟨inv f ≫ g, by simp⟩⟩


private theorem postcomp_bijective {D : Type*} [Category D] {A B : D}
    (f : A ⟶ B) [IsIso f] (T : D) :
    Function.Bijective (fun g : T ⟶ A => g ≫ f) :=
  ⟨fun _ _ h => (cancel_mono f).1 h, fun g => ⟨g ≫ inv f, by simp⟩⟩

private theorem inducedClassMap_bijective
    [∀ i, K.HasHomology i] [∀ i, K'.HasHomology i] [∀ i, I.HasHomology i]
    [∀ i, I'.HasHomology i] [QuasiIso f] [QuasiIso g] [I'.IsKInjective] [I.IsKInjective]
    (n : ℤ) : Function.Bijective (inducedClassMap f g n) := by
  let Q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  have hpre : Function.Bijective (fun x : (Q.obj K ⟶ Q.obj (I'⟦n⟧)) => Q.map f ≫ x) := by
    have hI := CochainComplex.IsKInjective.rightOrthogonal (I'⟦n⟧)
    rw [← ObjectProperty.isLocal_trW] at hI
    apply hI
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
      HomotopyCategory.quotient_map_mem_quasiIso_iff]
    change QuasiIso f
    infer_instance
  have hg : IsIso (Q.map (g⟦n⟧')) := by
    have hg0 : IsIso (Q.map g) :=
      (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences g).2
        ((CochainComplex.IsKInjective.quasiIso_iff g).1 inferInstance)
    rw [← Functor.comp_map]
    exact (NatIso.isIso_map_iff (Q.commShiftIso n) g).2 (by
      change IsIso ((Q.map g)⟦n⟧')
      infer_instance)
  let F : ((Q.obj K) ⟶ (Q.obj (I'⟦n⟧))) → ((Q.obj K') ⟶ (Q.obj (I⟦n⟧))) :=
    fun x => Q.map f ≫ x ≫ Q.map (g⟦n⟧')
  have hF : Function.Bijective F := by
    have hpost := postcomp_bijective (Q.map (g⟦n⟧')) (Q.obj K')
    convert hpost.comp hpre using 1
    funext x
    simp [F, Category.assoc]
  have hcomp :
      (CohomologyClass.homAddEquiv (K := K') (L := I) (n := n)).toFun ∘
          inducedClassMap f g n =
        F ∘ (CohomologyClass.homAddEquiv (K := K) (L := I') (n := n)).toFun := by
    funext x
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    simp only [inducedClassMap]
    change CohomologyClass.toHom ((CohomologyClass.mk ((inducedCocycleMap f g n) z))) = _
    rw [CohomologyClass.toHom_mk]
    dsimp [F, CohomologyClass.homAddEquiv]
    change Q.map (Cocycle.equivHomShift.symm ((inducedCocycleMap f g n) z)) =
      Q.map f ≫ CohomologyClass.toHom (CohomologyClass.mk z) ≫ Q.map (g⟦n⟧')
    rw [CohomologyClass.toHom_mk]
    simp [inducedCocycleMap, Cocycle.equivHomShift_symm_precomp,
      Cocycle.equivHomShift_symm_postcomp, Functor.map_comp]
    rfl
  apply (Function.Bijective.of_comp_iff'
    (CohomologyClass.homAddEquiv (K := K') (L := I) (n := n)).bijective _).1
  change Function.Bijective
    ((CohomologyClass.homAddEquiv (K := K') (L := I) (n := n)).toFun ∘ inducedClassMap f g n)
  rw [hcomp]
  exact hF.comp (CohomologyClass.homAddEquiv (K := K) (L := I') (n := n)).bijective

private noncomputable def inducedHomologyMapData (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℤ) n).map
        (inducedHomComplexMap f g))
      (HomComplex.leftHomologyData K I' n) (HomComplex.leftHomologyData K' I n) where
  φK := AddCommGrpCat.ofHom (inducedCocycleMap f g n)
  φH := AddCommGrpCat.ofHom (inducedClassMap f g n)
  commi := by ext z; rfl
  commf' := by
    ext z
    apply Cocycle.ext
    exact (ConcreteCategory.congr_hom ((inducedHomComplexMap f g).comm _ _) z).symm
  commπ := by ext z; rfl

private theorem inducedHomComplexMap_quasiIso [QuasiIso f] [QuasiIso g]
    [I'.IsKInjective] [I.IsKInjective]
    [∀ i, (K.HomComplex I').HasHomology i] [∀ i, (K'.HomComplex I).HasHomology i] :
    QuasiIso (inducedHomComplexMap f g) := by
  refine (quasiIso_iff _).2 fun n => ?_
  rw [quasiIsoAt_iff, (inducedHomologyMapData f g n).quasiIso_iff]
  exact ConcreteCategory.isIso_iff_bijective _ |>.2 (inducedClassMap_bijective f g n)

end Abelian

/-- A degreewise quasi-isomorphism of complexes of sheaves of modules whose underlying map of
presheaves of modules is a quasi-isomorphism is a quasi-isomorphism. -/
private theorem moduleSheafQuasiIso_of_presheafQuasiIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {K L : CochainComplex (SheafOfModules.{u} R) ℤ} (f : K ⟶ L)
    (hf : QuasiIso (((SheafOfModules.forget R).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f)) : QuasiIso f := by
  let F := SheafOfModules.forget R
  let G := PresheafOfModules.sheafification (𝟙 R.obj)
  let c := ComplexShape.up ℤ
  let _ : G.Additive := Functor.additive_of_preserves_binary_products G
  let sf := (G.mapHomologicalComplex c).map ((F.mapHomologicalComplex c).map f)
  have hsf : QuasiIso sf :=
    HomologicalComplex.quasiIso_map_of_preservesHomology
      ((F.mapHomologicalComplex c).map f) G
  let e : F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c ≅
      𝟭 (CochainComplex (SheafOfModules.{u} R) ℤ) :=
    Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c ≪≫
      NatIso.mapHomologicalComplex
        (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit) c ≪≫
      Functor.mapHomologicalComplexIdIso _ c
  have he : Arrow.mk sf ≅ Arrow.mk f :=
    Arrow.isoMk (e.app K) (e.app L) (by simpa [sf] using (e.hom.naturality f).symm)
  exact quasiIso_of_arrow_mk_iso sf f he

/-- Over each object of the site, the induced map of internal Hom complexes is, after
forgetting the module structure, Mathlib's map of Hom complexes between the restrictions, and
so a quasi-isomorphism. -/
private theorem local_section_map_quasiIso
    (X : RingedSite.{u, u, u})
    {I' I L' L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (i : I' ⟶ I) [QuasiIso i] [I'.IsKInjective] [I.IsKInjective]
    (l : L' ⟶ L) [QuasiIso l] (U : X.C) :
    QuasiIso ((((sheafToPresheaf X.J AddCommGrpCat ⋙
      (evaluation X.Cᵒᵖ AddCommGrpCat).obj (Opposite.op U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          (((SheafOfModules.toSheaf
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (sheafHomComplexMap X l i)))) := by
  let T := SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  let lU : restrictComplex X L' U ⟶ restrictComplex X L U :=
    (T.mapHomologicalComplex (ComplexShape.up ℤ)).map l
  let iU : restrictComplex X I' U ⟶ restrictComplex X I U :=
    (T.mapHomologicalComplex (ComplexShape.up ℤ)).map i
  let g := inducedHomComplexMap lU iU
  have hg : QuasiIso g := inducedHomComplexMap_quasiIso lU iU
  let α := (sheafHomComplex X L I').sectionsIso U
  let β := (sheafHomComplex X L' I).sectionsIso U
  let Ev := (evaluation X.Cᵒᵖ AddCommGrpCat).obj (Opposite.op U)
  let Sh := sheafToPresheaf X.J AddCommGrpCat
  let R := (SheafOfModules.toSheaf
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex (ComplexShape.up ℤ)
  let h := ((Sh ⋙ Ev).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (R.map (sheafHomComplexMap X l i))
  have hconj : h ≫ β.hom = α.hom ≫ g := by
    apply HomologicalComplex.Hom.ext
    funext n
    ext s
    apply Cochain.ext
    intro p q hpq
    simp only [HomologicalComplex.comp_f, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
    let m := (((sheafHomComplexConstruction X).map l i).f n).val.app (Opposite.op U)
    have hmap : (AddCommGrpCat.Hom.hom (h.f n)) s = ConcreteCategory.hom m s := rfl
    let z := (AddCommGrpCat.Hom.hom (α.hom.f n)) s
    have gmap : (AddCommGrpCat.Hom.hom (g.f n)) z = inducedCochainMap lU iU n z := rfl
    rw [hmap, gmap]
    calc
      Cochain.v ((AddCommGrpCat.Hom.hom (β.hom.f n)) (ConcreteCategory.hom m s)) p q hpq =
          SheafOfModules.Hom.over (l.f p) U ≫
            Cochain.v ((AddCommGrpCat.Hom.hom (α.hom.f n)) s) p q hpq ≫
              SheafOfModules.Hom.over (i.f q) U :=
        (sheafHomComplexConstruction X).map_isInduced l i U n p q hpq s
      _ = Cochain.v (inducedCochainMap lU iU n z) p q hpq := by
        simpa [lU, iU, z] using (inducedCochainMap_v lU iU n p q hpq z).symm
  have heq : h = α.hom ≫ g ≫ β.inv := by
    rw [← Category.assoc, ← hconj]
    simp
  change QuasiIso h
  rw [heq]
  infer_instance

/-- Quasi-isomorphisms in both variables, with K-injective complexes in the
second variable, induce a quasi-isomorphism of internal Hom complexes. -/
@[stacks 0A95]
theorem sheafHomComplexMap_quasiIso
    (X : RingedSite.{u, u, u})
    {I' I L' L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (i : I' ⟶ I) [QuasiIso i] [I'.IsKInjective] [I.IsKInjective]
    (l : L' ⟶ L) [QuasiIso l] :
    QuasiIso (sheafHomComplexMap X l i) := by
  let φ := sheafHomComplexMap X l i
  let F := SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let : F.Additive :=
    SheafOfModules.instAdditivePresheafOfModulesObjFunctorOppositeRingCatIsSheafForget
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let G := PresheafOfModules.toPresheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
  let φP := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ
  let φG := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map φP
  have hφG : QuasiIso φG := by
    rw [HomologicalComplex.quasiIso_iff_evaluation φG]
    intro U
    change QuasiIso (((sheafToPresheaf X.J AddCommGrpCat.{u} ⋙
      (evaluation X.Cᵒᵖ AddCommGrpCat.{u}).obj U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          (((SheafOfModules.toSheaf
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ))
    exact local_section_map_quasiIso X i l U.unop
  have hφP : QuasiIso φP :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology φP G).1 hφG
  exact moduleSheafQuasiIso_of_presheafQuasiIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) φ hφP

end Stacks.Cohomology.InternalHom

end
