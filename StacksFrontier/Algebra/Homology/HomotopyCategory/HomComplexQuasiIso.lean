module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-! # The Hom complex of quasi-isomorphisms into K-injective complexes

Let `C` be an abelian category, let `f : K' ⟶ K` and `g : I' ⟶ I` be morphisms of cochain
complexes in `C`, and let `Hom(K, I)` denote Mathlib's Hom complex
`CochainComplex.HomComplex`, the complex of abelian groups whose degree-`n` term is the group
of degree-`n` cochains `K ⟶ I`. Pre- and postcomposition with `f` and `g` give a morphism of
complexes of abelian groups

`Hom(K, I') ⟶ Hom(K', I)`.

This file proves that this morphism is a quasi-isomorphism as soon as `f` and `g` are
quasi-isomorphisms and `I` and `I'` are K-injective.

## Main definitions

* `CochainComplex.HomComplex.cochainMap`: pre- and postcomposition on cochains.
* `CochainComplex.HomComplex.homComplexMap`: the induced morphism of Hom complexes.
* `CochainComplex.HomComplex.cocycleMap` and `CochainComplex.HomComplex.cohomologyClassMap`: the
  induced maps on cocycles and on cohomology classes.
* `CochainComplex.HomComplex.homComplexMapLeftHomologyMapData`: the induced map on the left
  homology data `CochainComplex.HomComplex.leftHomologyData`, whose homology is the group of
  cohomology classes.

## Main results

* `CochainComplex.HomComplex.cohomologyClassMap_bijective`: the induced map on cohomology
  classes is bijective.
* `CochainComplex.HomComplex.homComplexMap_quasiIso`: the induced morphism of Hom complexes is
  a quasi-isomorphism.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {K' K I' I : CochainComplex C ℤ}
  (f : K' ⟶ K) (g : I' ⟶ I)

/-- Pre- and postcomposition of a degree-`n` cochain `K ⟶ I'` with `f : K' ⟶ K` and
`g : I' ⟶ I`, as an additive map to degree-`n` cochains `K' ⟶ I`. -/
def cochainMap (n : ℤ) : Cochain K I' n →+ Cochain K' I n where
  toFun z := (Cochain.ofHom f).comp (z.comp (Cochain.ofHom g) (add_zero n)) (zero_add n)
  map_zero' := by simp
  map_add' z z' := by simp [Cochain.comp_add]

/-- The components of `cochainMap` are pre- and postcomposition with the components of `f` and
`g`. -/
lemma cochainMap_v (n p q : ℤ) (hpq : p + n = q) (z : Cochain K I' n) :
    (cochainMap f g n z).v p q hpq = f.f p ≫ z.v p q hpq ≫ g.f q := by
  simp [cochainMap, Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]

/-- Pre- and postcomposition with `f` and `g`, as a morphism of Hom complexes
`Hom(K, I') ⟶ Hom(K', I)`. -/
def homComplexMap : K.HomComplex I' ⟶ K'.HomComplex I where
  f n := AddCommGrpCat.ofHom (cochainMap f g n)
  comm' n m _ := by
    ext z
    change δ n m ((Cochain.ofHom f).comp
        ((z : Cochain K I' n).comp (Cochain.ofHom g) (add_zero n)) (zero_add n)) =
      (Cochain.ofHom f).comp ((δ n m z).comp (Cochain.ofHom g) (add_zero m)) (zero_add m)
    rw [δ_ofHom_comp, δ_comp_ofHom (z₁ := (z : Cochain K I' n)) (f := g) (m := m)]

/-- The components of `homComplexMap` are `cochainMap`. -/
@[simp]
lemma homComplexMap_f_apply (n : ℤ) (z : Cochain K I' n) :
    AddCommGrpCat.Hom.hom ((homComplexMap f g).f n) z = cochainMap f g n z := rfl

/-- `cochainMap` commutes with the Hom-complex differential `δ`. -/
lemma cochainMap_δ (n m : ℤ) (z : Cochain K I' n) :
    cochainMap f g m (δ n m z) = δ n m (cochainMap f g n z) :=
  (ConcreteCategory.congr_hom ((homComplexMap f g).comm n m) z).symm

/-- Pre- and postcomposition with `f` and `g`, on degree-`n` cocycles. -/
def cocycleMap (n : ℤ) : Cocycle K I' n →+ Cocycle K' I n where
  toFun z := (z.postcomp g).precomp f
  map_zero' := by ext; simp
  map_add' z z' := by ext; simp [Cochain.comp_add]

/-- Pre- and postcomposition with `f` and `g`, on degree-`n` cohomology classes. -/
def cohomologyClassMap (n : ℤ) : CohomologyClass K I' n →+ CohomologyClass K' I n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K' I n).comp (cocycleMap f g n)) (by
      intro z hz
      change CohomologyClass.mk (cocycleMap f g n z) = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      obtain ⟨m, hm, β, hβ⟩ := hz
      refine ⟨m, hm, cochainMap f g m β, ?_⟩
      change δ m n (cochainMap f g m β) = cochainMap f g n (z : Cochain K I' n)
      rw [← cochainMap_δ f g m n β, hβ])

/-- Postcomposition with an isomorphism is bijective on morphisms out of a fixed object. -/
private lemma postcomp_bijective {D : Type u} [Category.{v} D] {A B : D} (u : A ⟶ B) [IsIso u]
    (T : D) : Function.Bijective (fun h : T ⟶ A ↦ h ≫ u) :=
  ⟨fun _ _ eq ↦ (cancel_mono u).1 eq, fun h ↦ ⟨h ≫ inv u, by simp⟩⟩

/-- Pre- and postcomposition with quasi-isomorphisms `f` and `g` is bijective on cohomology
classes, provided `I'` and `I` are K-injective. -/
lemma cohomologyClassMap_bijective [QuasiIso f] [QuasiIso g] [I'.IsKInjective] [I.IsKInjective]
    (n : ℤ) : Function.Bijective (cohomologyClassMap f g n) := by
  let Q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  have hpre : Function.Bijective (fun x : Q.obj K ⟶ Q.obj (I'⟦n⟧) ↦ Q.map f ≫ x) := by
    have hI := CochainComplex.IsKInjective.rightOrthogonal (I'⟦n⟧)
    rw [← ObjectProperty.isLocal_trW] at hI
    refine hI _ ?_
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
      HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact inferInstanceAs (QuasiIso f)
  have hg : IsIso (Q.map (g⟦n⟧')) := by
    have hg₀ : IsIso (Q.map g) :=
      (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences g).2
        ((CochainComplex.IsKInjective.quasiIso_iff g).1 inferInstance)
    rw [← Functor.comp_map]
    exact (NatIso.isIso_map_iff (Q.commShiftIso n) g).2
      (by change IsIso ((Q.map g)⟦n⟧'); infer_instance)
  have hF : Function.Bijective
      (fun x : Q.obj K ⟶ Q.obj (I'⟦n⟧) ↦ Q.map f ≫ x ≫ Q.map (g⟦n⟧')) := by
    convert (postcomp_bijective (Q.map (g⟦n⟧')) (Q.obj K')).comp hpre using 1
    funext x
    simp
  have hcomp : (CohomologyClass.homAddEquiv (K := K') (L := I) (n := n)).toFun ∘
      cohomologyClassMap f g n =
      (fun x : Q.obj K ⟶ Q.obj (I'⟦n⟧) ↦ Q.map f ≫ x ≫ Q.map (g⟦n⟧')) ∘
        (CohomologyClass.homAddEquiv (K := K) (L := I') (n := n)).toFun := by
    funext x
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    simp only [cohomologyClassMap]
    show CohomologyClass.toHom (CohomologyClass.mk (cocycleMap f g n z)) = _
    rw [CohomologyClass.toHom_mk]
    dsimp [CohomologyClass.homAddEquiv]
    show Q.map (Cocycle.equivHomShift.symm (cocycleMap f g n z)) =
      Q.map f ≫ CohomologyClass.toHom (CohomologyClass.mk z) ≫ Q.map (g⟦n⟧')
    rw [CohomologyClass.toHom_mk]
    simp [cocycleMap, Cocycle.equivHomShift_symm_precomp, Cocycle.equivHomShift_symm_postcomp,
      Functor.map_comp]
    rfl
  refine (Function.Bijective.of_comp_iff'
    (CohomologyClass.homAddEquiv (K := K') (L := I) (n := n)).bijective _).1 ?_
  show Function.Bijective
    ((CohomologyClass.homAddEquiv (K := K') (L := I) (n := n)).toFun ∘ cohomologyClassMap f g n)
  rw [hcomp]
  exact hF.comp (CohomologyClass.homAddEquiv (K := K) (L := I') (n := n)).bijective

/-- The left homology map data exhibiting `cohomologyClassMap` as the map induced by
`homComplexMap` on the homology of the Hom complexes, computed through
`CochainComplex.HomComplex.leftHomologyData`. -/
noncomputable def homComplexMapLeftHomologyMapData (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℤ) n).map
        (homComplexMap f g))
      (leftHomologyData K I' n) (leftHomologyData K' I n) where
  φK := AddCommGrpCat.ofHom (cocycleMap f g n)
  φH := AddCommGrpCat.ofHom (cohomologyClassMap f g n)
  commi := by ext z; rfl
  commf' := by
    ext z
    exact Cocycle.ext (ConcreteCategory.congr_hom ((homComplexMap f g).comm _ _) z).symm
  commπ := by ext z; rfl

/-- Pre- and postcomposition with quasi-isomorphisms `f` and `g` is a quasi-isomorphism of Hom
complexes, provided `I'` and `I` are K-injective. -/
theorem homComplexMap_quasiIso [QuasiIso f] [QuasiIso g] [I'.IsKInjective] [I.IsKInjective] :
    QuasiIso (homComplexMap f g) := by
  refine (quasiIso_iff _).2 fun n => ?_
  rw [quasiIsoAt_iff, (homComplexMapLeftHomologyMapData f g n).quasiIso_iff]
  exact (ConcreteCategory.isIso_iff_bijective _).2 (cohomologyClassMap_bijective f g n)

end CochainComplex.HomComplex

end
