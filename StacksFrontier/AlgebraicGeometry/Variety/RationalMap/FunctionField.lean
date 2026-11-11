module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.FunctionField
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.CommonOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.DenseOpenIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericStalkCriterion
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic

/-!
# Birational varieties and their function fields

Two varieties over a field `k` which are birational over `k` in the sense of Mathlib's
`AlgebraicGeometry.Scheme.BirationalOver`, that is which have isomorphic dense open subschemes over
`Spec k`, are exactly those whose rings of rational functions are isomorphic as `k`-algebras,
exactly those with isomorphic nonempty open subvarieties, and exactly those for which some nonempty
open subvariety of one admits a birational morphism to the other.

## Main results

* `AlgebraicGeometry.birationalOver_tfae_functionField` gives these four equivalent conditions.

## Implementation notes

The ring of rational functions is `Stacks.Chow.rationalFunctions`, whose algebra structure over `k`
is induced by the structure morphism to `Spec k` followed by the restriction of global sections to
rational functions. Isomorphisms and morphisms of open subvarieties are required explicitly to
commute with the structure morphisms to `Spec k`.

The first entry, `AlgebraicGeometry.Scheme.BirationalOver`, is not the birationality of
Stacks 0A20 (2), isomorphism in the category of varieties and dominant rational maps. Stacks 0BXP,
with that first entry, is `AlgebraicGeometry.Variety.nonempty_iso_tfae` in
`StacksFrontier.AlgebraicGeometry.Variety.RationalMap.BirationalVariety`, which is derived from the
equivalences proved here.

## References

* [Stacks Project, Tag 0BXP](https://stacks.math.columbia.edu/tag/0BXP)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

private theorem rationalFunctions_residueField_algebraMap
    (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] (a : k) :
    letI : Algebra k (Stacks.Chow.rationalFunctions X) :=
      ((Stacks.Chow.ofSectionRingHom X ⟨⊤, dense_univ⟩).comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop).hom).toAlgebra
    (Stacks.Chow.rationalFunctionsEquivResidueField X).val
        (algebraMap k (Stacks.Chow.rationalFunctions X) a) =
      sX.residueFieldMap (genericPoint X)
        ((Spec (.of k)).Γevaluation (sX (genericPoint X))
          (((Scheme.ΓSpecIso (.of k)).inv).hom a)) := by
  let : Algebra k (Stacks.Chow.rationalFunctions X) :=
    ((Stacks.Chow.ofSectionRingHom X ⟨⊤, dense_univ⟩).comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop).hom).toAlgebra
  change (Stacks.Chow.rationalFunctionsEquivResidueField X).val
      (((Stacks.Chow.ofSectionRingHom X ⟨⊤, dense_univ⟩).comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop).hom) a) = _
  rw [RingHom.comp_apply, Stacks.Chow.ofSectionRingHom_apply,
    (Stacks.Chow.rationalFunctionsEquivResidueField X).property
      ⟨⊤, dense_univ⟩ _ (by simp)]
  change (sX.appTop ≫ X.Γevaluation (genericPoint X))
      (((Scheme.ΓSpecIso (.of k)).inv).hom a) =
    (((Spec (.of k)).Γevaluation (sX (genericPoint X))) ≫
      sX.residueFieldMap (genericPoint X))
        (((Scheme.ΓSpecIso (.of k)).inv).hom a)
  rw [Scheme.Γevaluation_naturality]

private theorem spec_Gammaevaluation_cast
    (k : Type u) [Field k] (p q : Spec (.of k)) (h : p = q) (a : k) :
    h ▸ (Spec (.of k)).Γevaluation p (((Scheme.ΓSpecIso (.of k)).inv).hom a) =
      (Spec (.of k)).Γevaluation q (((Scheme.ΓSpecIso (.of k)).inv).hom a) := by cases h; rfl

private theorem castResidueFieldHomComp_apply {S : Scheme.{u}} {p q : S} (h : p = q)
    {R T : CommRingCat.{u}} (f : S.residueField p ⟶ R) (g : R ⟶ T)
    (a : S.residueField p) :
    (h ▸ (f ≫ g)) (h ▸ a) = g (f a) := by cases h; rfl

private theorem cast_symm_apply {α : Sort u} {P : α → Sort u} {a b : α}
    (h : a = b) (x : P b) : h ▸ (h.symm ▸ x) = x := by cases h; rfl

private theorem spec_Γevaluation_surjective
    (k : Type u) [Field k] (p : Spec (.of k)) :
    Function.Surjective (fun a : k =>
      (Spec (.of k)).Γevaluation p (((Scheme.ΓSpecIso (.of k)).inv).hom a)) := by
  let q := p.asIdeal
  let e := Scheme.Spec.residueFieldIso (.of k) p
  have : q.IsPrime := p.isPrime
  have hq : Function.Surjective (algebraMap k q.ResidueField) := by
    intro b
    obtain ⟨a, ha⟩ := q.algEquivResidueFieldOfField.toRingEquiv.surjective b
    exact ⟨a, (Ideal.algEquivResidueFieldOfField_apply q a).trans ha⟩
  have heq :
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation p).hom =
        e.inv.hom.comp (algebraMap k q.ResidueField) := by
    simpa [e, q, Scheme.Γevaluation, Scheme.evaluation, RingHom.comp_assoc] using
      (congrArg CommRingCat.Hom.hom
        (Scheme.Spec.algebraMap_residueFieldIso_inv (.of k) p)).symm
  change Function.Surjective (fun a : k =>
    (((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation p).hom) a)
  rw [heq]
  exact e.commRingCatIsoToRingEquiv.symm.surjective.comp hq

private theorem functionField_algEquiv_of_birationalOver
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [IsVariety k sX] [IsVariety k sY] :
    letI : Algebra k (Stacks.Chow.rationalFunctions X) :=
      ((Stacks.Chow.ofSectionRingHom X ⟨⊤, dense_univ⟩).comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop).hom).toAlgebra
    letI : Algebra k (Stacks.Chow.rationalFunctions Y) :=
      ((Stacks.Chow.ofSectionRingHom Y ⟨⊤, dense_univ⟩).comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop).hom).toAlgebra
    Scheme.BirationalOver sX sY →
      Nonempty (Stacks.Chow.rationalFunctions X ≃ₐ[k]
        Stacks.Chow.rationalFunctions Y) := by
  let : Algebra k (Stacks.Chow.rationalFunctions X) :=
    ((Stacks.Chow.ofSectionRingHom X ⟨⊤, dense_univ⟩).comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop).hom).toAlgebra
  let : Algebra k (Stacks.Chow.rationalFunctions Y) :=
    ((Stacks.Chow.ofSectionRingHom Y ⟨⊤, dense_univ⟩).comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop).hom).toAlgebra
  intro hbir
  obtain ⟨h, e, he⟩ := residueFieldIso_of_birationalOver sX sY hbir
  let eX := (Stacks.Chow.rationalFunctionsEquivResidueField X).val
  let eY := (Stacks.Chow.rationalFunctionsEquivResidueField Y).val
  let eK := e.commRingCatIsoToRingEquiv
  let eR := eX.trans (eK.trans eY.symm)
  let cX (a : k) := (Spec (.of k)).Γevaluation (sX (genericPoint X))
    (((Scheme.ΓSpecIso (.of k)).inv).hom a)
  let cY (a : k) := (Spec (.of k)).Γevaluation (sY (genericPoint Y))
    (((Scheme.ΓSpecIso (.of k)).inv).hom a)
  refine ⟨AlgEquiv.ofRingEquiv (f := eR) ?_⟩
  intro a
  change eY.symm (eK (eX (algebraMap k (Stacks.Chow.rationalFunctions X) a))) =
    algebraMap k (Stacks.Chow.rationalFunctions Y) a
  apply eY.injective
  simp only [RingEquiv.apply_symm_apply]
  rw [rationalFunctions_residueField_algebraMap k sX a,
    rationalFunctions_residueField_algebraMap k sY a]
  have hc : h ▸ cX a = cY a := spec_Gammaevaluation_cast k _ _ h a
  have hval' : e.hom (sX.residueFieldMap (genericPoint X) (cX a)) =
      sY.residueFieldMap (genericPoint Y) (cY a) := by
    rw [← hc]
    simpa only [castResidueFieldHomComp_apply] using congrArg (fun g => g (h ▸ cX a)) he
  change eK (sX.residueFieldMap (genericPoint X) (cX a)) =
    sY.residueFieldMap (genericPoint Y) (cY a) at hval'
  simpa [eR, eK, eX, eY, cX, cY, RingEquiv.trans_apply] using hval'

private theorem birationalOver_of_functionField_algEquiv
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [IsVariety k sX] [IsVariety k sY] :
    letI : Algebra k (Stacks.Chow.rationalFunctions X) :=
      ((Stacks.Chow.ofSectionRingHom X ⟨⊤, dense_univ⟩).comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop).hom).toAlgebra
    letI : Algebra k (Stacks.Chow.rationalFunctions Y) :=
      ((Stacks.Chow.ofSectionRingHom Y ⟨⊤, dense_univ⟩).comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop).hom).toAlgebra
    Nonempty (Stacks.Chow.rationalFunctions X ≃ₐ[k]
        Stacks.Chow.rationalFunctions Y) →
      Scheme.BirationalOver sX sY := by
  let : Algebra k (Stacks.Chow.rationalFunctions X) :=
    ((Stacks.Chow.ofSectionRingHom X ⟨⊤, dense_univ⟩).comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop).hom).toAlgebra
  let : Algebra k (Stacks.Chow.rationalFunctions Y) :=
    ((Stacks.Chow.ofSectionRingHom Y ⟨⊤, dense_univ⟩).comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop).hom).toAlgebra
  rintro ⟨e⟩
  let eX := (Stacks.Chow.rationalFunctionsEquivResidueField X).val
  let eY := (Stacks.Chow.rationalFunctionsEquivResidueField Y).val
  let eR := eX.symm.trans (e.toRingEquiv.trans eY)
  let eIso := eR.toCommRingCatIso
  have h : sX (genericPoint X) = sY (genericPoint Y) := Subsingleton.elim _ _
  refine birationalOver_of_residueFieldIso sX sY h eIso ?_
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  let cX := fun a : k => (Spec (.of k)).Γevaluation (sX (genericPoint X))
    (((Scheme.ΓSpecIso (.of k)).inv).hom a)
  let cY := fun a : k => (Spec (.of k)).Γevaluation (sY (genericPoint Y))
    (((Scheme.ΓSpecIso (.of k)).inv).hom a)
  obtain ⟨a, ha⟩ := spec_Γevaluation_surjective k
    (sX (genericPoint X)) (h.symm ▸ c)
  have hc : h ▸ cX a = cY a :=
    spec_Gammaevaluation_cast k _ _ h a
  have hcast : h ▸ (h.symm ▸ c) = c :=
    cast_symm_apply (P := fun p => (Spec (.of k)).residueField p) h c
  have hforA : eR (sX.residueFieldMap (genericPoint X) (cX a)) =
      sY.residueFieldMap (genericPoint Y) (cY a) := by
    rw [← rationalFunctions_residueField_algebraMap k sX a,
      ← rationalFunctions_residueField_algebraMap k sY a]
    change eY (e (eX.symm (eX (algebraMap k (Stacks.Chow.rationalFunctions X) a)))) =
      eY (algebraMap k (Stacks.Chow.rationalFunctions Y) a)
    simpa only [RingEquiv.symm_apply_apply] using congrArg eY (e.commutes a)
  calc
    (h ▸ (sX.residueFieldMap (genericPoint X) ≫ eIso.hom)) c =
        eIso.hom (sX.residueFieldMap (genericPoint X) (h.symm ▸ c)) := by
      simpa only [hcast] using castResidueFieldHomComp_apply h
        (sX.residueFieldMap (genericPoint X)) eIso.hom (h.symm ▸ c)
    _ = eIso.hom (sX.residueFieldMap (genericPoint X) (cX a)) := by rw [← ha]
    _ = sY.residueFieldMap (genericPoint Y) (cY a) := hforA
    _ = sY.residueFieldMap (genericPoint Y) c := by
      congr 1
      rw [← hc]
      exact (congrArg (fun z => h ▸ z) ha).trans hcast

private theorem birationalOver_iff_functionField_algEquiv
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [IsVariety k sX] [IsVariety k sY] :
    letI : Algebra k (Stacks.Chow.rationalFunctions X) :=
      ((Stacks.Chow.ofSectionRingHom X ⟨⊤, dense_univ⟩).comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop).hom).toAlgebra
    letI : Algebra k (Stacks.Chow.rationalFunctions Y) :=
      ((Stacks.Chow.ofSectionRingHom Y ⟨⊤, dense_univ⟩).comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop).hom).toAlgebra
    Scheme.BirationalOver sX sY ↔
      Nonempty (Stacks.Chow.rationalFunctions X ≃ₐ[k]
        Stacks.Chow.rationalFunctions Y) :=
  ⟨functionField_algEquiv_of_birationalOver k sX sY,
    birationalOver_of_functionField_algEquiv k sX sY⟩

private theorem birational_of_open_iso {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {U : X.Opens} {V : Y.Opens} (hU : (U : Set X).Nonempty)
    (hV : (V : Set Y).Nonempty) (e : U.toScheme ≅ V.toScheme) :
    IsBirational (e.hom ≫ V.ι) := by
  have : Nonempty U.toScheme := ⟨⟨hU.choose, hU.choose_spec⟩⟩
  have : Nonempty V.toScheme := ⟨⟨hV.choose, hV.choose_spec⟩⟩
  have hη : (e.hom ≫ V.ι) (genericPoint U.toScheme) = genericPoint Y := by
    rw [Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion e.hom,
      genericPoint_eq_of_isOpenImmersion V.ι]
  apply isBirational_of_bijOn_of_isIso_stalkMap
  · rwa [genericPoints_eq_singleton, genericPoints_eq_singleton, Set.bijOn_singleton]
  · intro x hx
    obtain rfl : x = genericPoint U.toScheme := by
      simpa [genericPoints_eq_singleton] using hx
    rw [Scheme.Hom.stalkMap_comp]
    let f := V.ι.stalkMap (e.hom (genericPoint U.toScheme))
    let g := e.hom.stalkMap (genericPoint U.toScheme)
    have : IsIso f := inferInstance
    have : IsIso g := inferInstance
    exact CategoryTheory.IsIso.comp_isIso (f := f) (h := g)

/-- Four equivalent conditions on varieties `X` and `Y` over a field `k`: birationality over `k`
in the sense of Mathlib's `AlgebraicGeometry.Scheme.BirationalOver`, isomorphy of the rings of
rational functions as `k`-algebras, isomorphy of nonempty open subvarieties, and the existence of
a birational morphism from a nonempty open subvariety of `X` to `Y`.

`AlgebraicGeometry.Scheme.BirationalOver` is an isomorphism of dense open subschemes over
`Spec k`, so the first entry is a form of the third rather than the birationality of
Stacks 0A20 (2). Stacks 0BXP itself, whose first entry is isomorphism in the category of
varieties and dominant rational maps, is `AlgebraicGeometry.Variety.nonempty_iso_tfae`. -/
public theorem birationalOver_tfae_functionField
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [IsVariety k sX] [IsVariety k sY] :
    letI : Algebra k (Stacks.Chow.rationalFunctions X) :=
      ((Stacks.Chow.ofSectionRingHom X ⟨⊤, dense_univ⟩).comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop).hom).toAlgebra
    letI : Algebra k (Stacks.Chow.rationalFunctions Y) :=
      ((Stacks.Chow.ofSectionRingHom Y ⟨⊤, dense_univ⟩).comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop).hom).toAlgebra
    List.TFAE [
      Scheme.BirationalOver sX sY,
      Nonempty (Stacks.Chow.rationalFunctions X ≃ₐ[k]
        Stacks.Chow.rationalFunctions Y),
      ∃ (U : X.Opens) (V : Y.Opens),
        (U : Set X).Nonempty ∧ (V : Set Y).Nonempty ∧
          ∃ e : U.toScheme ≅ V.toScheme,
            e.hom ≫ V.ι ≫ sY = U.ι ≫ sX,
      ∃ (U : X.Opens), (U : Set X).Nonempty ∧
        ∃ f : U.toScheme ⟶ Y,
          IsBirational f ∧ f ≫ sY = U.ι ≫ sX] := by
  tfae_have 1 ↔ 3 :=
    birationalOver_iff_exists_nonempty_open_iso sX sY
  tfae_have 3 → 4 := by
    rintro ⟨U, V, hU, hV, e, he⟩
    exact ⟨U, hU, e.hom ≫ V.ι, birational_of_open_iso hU hV e, he⟩
  tfae_have 4 → 1 := by
    rintro ⟨U, hU, f, hf, hfS⟩
    have : Nonempty U.toScheme := ⟨⟨hU.choose, hU.choose_spec⟩⟩
    have : Subsingleton (irreducibleComponents U.toScheme) := by
      rw [irreducibleComponents_eq_singleton]
      infer_instance
    have : Subsingleton (irreducibleComponents Y) := by
      rw [irreducibleComponents_eq_singleton]
      infer_instance
    have : LocallyOfFiniteType (f ≫ sY) := by
      rw [hfS]
      infer_instance
    have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f sY
    exact (U.birationalOver_of_dense sX (U.2.dense hU)).symm.trans
      (birationalOver_of_isBirational (U.ι ≫ sX) sY f hf hfS
        (Or.inl ⟨inferInstance, inferInstance⟩))
  tfae_have 1 ↔ 2 :=
    birationalOver_iff_functionField_algEquiv k sX sY
  tfae_finish

end AlgebraicGeometry

end
