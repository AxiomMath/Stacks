module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Etale.Finite
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtaleConstruction.ColimitFlatness
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtaleConstruction.Coproducts
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtaleConstruction.SplittingAlgebra

/-!
# `T(A)` is the filtered colimit of its finite stages

For a finite set `s` of standard étale presentations over `A`, the finite stage `T_s(A)` is the
polynomial quotient using only the variables and relations of the presentations in `s`. These
stages form a filtered diagram indexed by `Finset (StandardEtalePresentation A)` whose colimit is
`T(A)`.

Each finite stage is the coproduct in `CommAlgCat A` of the algebras presented by the members of
`s`, so it is étale over `A` and faithfully flat over `A`; the colimit therefore makes `T(A)` a
faithfully flat ind-étale `A`-algebra.

## Main results

* `AlgebraicGeometry.ProEtale.finiteStageColimit`
* `AlgebraicGeometry.ProEtale.finiteStageCoproductIso`
* `AlgebraicGeometry.ProEtale.splittingAlgebra_faithfullyFlat`
* `AlgebraicGeometry.ProEtale.splittingAlgebra_ind_etale`

## Implementation notes

The colimit is computed by hand rather than transported from a general statement about polynomial
quotients: the descent map out of `T(A)` is the `MvPolynomial.aeval` of the function sending a
variable `⟨p, i⟩` to the image of `X i` under the leg of the cocone at the singleton `{p}`.
-/

open CategoryTheory CategoryTheory.Limits MvPolynomial

@[expose] public section

namespace AlgebraicGeometry.ProEtale

universe u

/-- A finite set of standard étale presentations over `A`, indexing a finite stage of `T(A)`. -/
abbrev finitePresentationSet (A : Type u) [CommRing A] :=
  Finset (StandardEtalePresentation A)

/-- The variables of the finite stage indexed by `s`: one copy of `Fin p.variableCount` for every
presentation `p ∈ s`. -/
abbrev finiteStageVariables {A : Type u} [CommRing A] (s : finitePresentationSet A) :=
  Σ p : {p : StandardEtalePresentation A // p ∈ s}, Fin p.1.variableCount

/-- A relation of a presentation in `s`, read as a polynomial in the variables of the finite
stage indexed by `s`. -/
noncomputable def finiteStageRelation {A : Type u} [CommRing A]
    (s : finitePresentationSet A) (i : finiteStageVariables s) :
    MvPolynomial (finiteStageVariables s) A :=
  rename (fun j ↦ ⟨i.1, j⟩) (i.1.1.relations i.2)

/-- The finite stage of `T(A)` indexed by `s`: the tensor product over `A` of the algebras
presented by the members of `s`. -/
abbrev finiteStageAlgebra {A : Type u} [CommRing A] (s : finitePresentationSet A) :=
  MvPolynomial (finiteStageVariables s) A ⧸
    Ideal.span (Set.range (finiteStageRelation s))

/-- The leg `T_s(A) → T(A)` of the finite-stage cocone. -/
noncomputable def finiteStageToSplittingAlgebra {A : Type u} [CommRing A]
    (s : finitePresentationSet A) : finiteStageAlgebra s →ₐ[A] splittingAlgebra A := by
  let I : Ideal (MvPolynomial (finiteStageVariables s) A) :=
    Ideal.span (Set.range (finiteStageRelation s))
  let J : Ideal (MvPolynomial (Σ p : StandardEtalePresentation A, Fin p.variableCount) A) :=
    Ideal.span (Set.range fun i : Σ p : StandardEtalePresentation A, Fin p.variableCount ↦
      splittingRelation i.1 i.2)
  let q : MvPolynomial (finiteStageVariables s) A →ₐ[A] splittingAlgebra A :=
    (Ideal.Quotient.mkₐ A J).comp
      (MvPolynomial.rename fun i ↦ (⟨i.1.1, i.2⟩ :
        Σ p : StandardEtalePresentation A, Fin p.variableCount))
  have hI : I ≤ RingHom.ker q.toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hrel :
        MvPolynomial.rename (fun j : finiteStageVariables s ↦ (⟨j.1.1, j.2⟩ :
            Σ p : StandardEtalePresentation A, Fin p.variableCount))
          (finiteStageRelation s i) = splittingRelation i.1.1 i.2 := by
      change MvPolynomial.rename
        (fun j : Σ p : {p : StandardEtalePresentation A // p ∈ s}, Fin p.1.variableCount ↦
          (⟨j.1.1, j.2⟩ : Σ p : StandardEtalePresentation A, Fin p.variableCount))
        (MvPolynomial.rename (fun j ↦ ⟨i.1, j⟩) (i.1.1.relations i.2)) =
        MvPolynomial.rename (fun j ↦ (⟨i.1.1, j⟩ :
          Σ p : StandardEtalePresentation A, Fin p.variableCount)) (i.1.1.relations i.2)
      rw [MvPolynomial.rename_rename]
      rfl
    change Ideal.Quotient.mk J
      (MvPolynomial.rename (fun j : finiteStageVariables s ↦ (⟨j.1.1, j.2⟩ :
        Σ p : StandardEtalePresentation A, Fin p.variableCount))
        (finiteStageRelation s i)) = 0
    rw [hrel, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨⟨i.1.1, i.2⟩, rfl⟩
  exact Ideal.Quotient.liftₐ _ q (fun _ hx ↦ RingHom.mem_ker.mp (hI hx))

/-- The transition map `T_s(A) → T_t(A)` of the finite-stage diagram, for `s ⊆ t`. -/
noncomputable def finiteStageMap {A : Type u} [CommRing A]
    {s t : finitePresentationSet A} (hst : s ⊆ t) :
    finiteStageAlgebra s →ₐ[A] finiteStageAlgebra t := by
  let I : Ideal (MvPolynomial (finiteStageVariables s) A) :=
    Ideal.span (Set.range (finiteStageRelation s))
  let J : Ideal (MvPolynomial (finiteStageVariables t) A) :=
    Ideal.span (Set.range (finiteStageRelation t))
  let q : MvPolynomial (finiteStageVariables s) A →ₐ[A] finiteStageAlgebra t :=
    (Ideal.Quotient.mkₐ A J).comp
      (MvPolynomial.rename fun i ↦ (⟨⟨i.1.1, hst i.1.2⟩, i.2⟩ : finiteStageVariables t))
  have hI : I ≤ RingHom.ker q.toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hrel :
        MvPolynomial.rename
            (fun j : finiteStageVariables s ↦
              (⟨⟨j.1.1, hst j.1.2⟩, j.2⟩ : finiteStageVariables t))
            (finiteStageRelation s i) =
          finiteStageRelation t ⟨⟨i.1.1, hst i.1.2⟩, i.2⟩ := by
      change MvPolynomial.rename
        (fun j : Σ p : {p : StandardEtalePresentation A // p ∈ s}, Fin p.1.variableCount ↦
          (⟨⟨j.1.1, hst j.1.2⟩, j.2⟩ :
            Σ p : {p : StandardEtalePresentation A // p ∈ t}, Fin p.1.variableCount))
        (MvPolynomial.rename (fun j ↦ ⟨i.1, j⟩) (i.1.1.relations i.2)) =
        MvPolynomial.rename
          (fun j ↦ (⟨⟨i.1.1, hst i.1.2⟩, j⟩ :
            Σ p : {p : StandardEtalePresentation A // p ∈ t}, Fin p.1.variableCount))
          (i.1.1.relations i.2)
      rw [MvPolynomial.rename_rename]
      rfl
    change Ideal.Quotient.mk J
      (MvPolynomial.rename
        (fun i ↦ (⟨⟨i.1.1, hst i.1.2⟩, i.2⟩ : finiteStageVariables t))
        (finiteStageRelation s i)) = 0
    rw [hrel, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨⟨⟨i.1.1, hst i.1.2⟩, i.2⟩, rfl⟩
  exact Ideal.Quotient.liftₐ _ q (fun _ hx ↦ RingHom.mem_ker.mp (hI hx))

/-- `finiteStageMap` on the class of a polynomial renames its variables. -/
lemma finiteStageMap_mk {A : Type u} [CommRing A]
    {s t : finitePresentationSet A} (hst : s ⊆ t)
    (x : MvPolynomial (finiteStageVariables s) A) :
    finiteStageMap hst (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk (Ideal.span (Set.range (finiteStageRelation t)))
        (MvPolynomial.rename
        (fun i ↦ (⟨⟨i.1.1, hst i.1.2⟩, i.2⟩ : finiteStageVariables t)) x) := by
  unfold finiteStageMap
  rfl

/-- `finiteStageToSplittingAlgebra` on the class of a polynomial renames its variables. -/
lemma finiteStageToSplittingAlgebra_mk {A : Type u} [CommRing A]
    (s : finitePresentationSet A) (x : MvPolynomial (finiteStageVariables s) A) :
    finiteStageToSplittingAlgebra s (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk
        (Ideal.span (Set.range fun i : Σ p : StandardEtalePresentation A,
          Fin p.variableCount ↦ splittingRelation i.1 i.2))
        (MvPolynomial.rename (fun i ↦ (⟨i.1.1, i.2⟩ :
          Σ p : StandardEtalePresentation A, Fin p.variableCount)) x) := by
  unfold finiteStageToSplittingAlgebra
  rfl

/-- The diagram of finite stages, indexed by the finite sets of standard étale presentations. -/
noncomputable abbrev finiteStageDiagram {A : Type u} [CommRing A] :
    finitePresentationSet A ⥤ CommAlgCat A where
  obj s := CommAlgCat.of A (finiteStageAlgebra s)
  map {s t} h := CommAlgCat.ofHom (finiteStageMap h.down.down)
  map_id s := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [CommAlgCat.hom_ofHom, CommAlgCat.hom_id]
    rw [finiteStageMap_mk]
    have hfun :
        (fun i : finiteStageVariables s ↦
          (⟨⟨i.1.1, i.1.2⟩, i.2⟩ : finiteStageVariables s)) = id := rfl
    simp only [hfun, MvPolynomial.rename_id_apply, AlgHom.id_apply]
  map_comp {s t v} f g := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [CommAlgCat.hom_ofHom, CommAlgCat.hom_comp, AlgHom.comp_apply]
    rw [finiteStageMap_mk, finiteStageMap_mk, finiteStageMap_mk]
    rw [MvPolynomial.rename_rename]
    rfl

/-- The cocone on the finite-stage diagram with vertex `T(A)`. -/
noncomputable def finiteStageCocone {A : Type u} [CommRing A] :
    Cocone (finiteStageDiagram (A := A)) where
  pt := CommAlgCat.of A (splittingAlgebra A)
  ι :=
    { app := fun s ↦ CommAlgCat.ofHom (finiteStageToSplittingAlgebra s)
      naturality := by
        intro s t f
        ext x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        change finiteStageToSplittingAlgebra t
          (finiteStageMap f.down.down (Ideal.Quotient.mk _ x)) =
          finiteStageToSplittingAlgebra s (Ideal.Quotient.mk _ x)
        rw [finiteStageMap_mk, finiteStageToSplittingAlgebra_mk,
          finiteStageToSplittingAlgebra_mk]
        rw [MvPolynomial.rename_rename]
        rfl }

/-- The variable of the one-element stage `{p}` corresponding to the `i`-th variable of `p`. -/
def singletonStageVariable {A : Type u} [CommRing A]
    (p : StandardEtalePresentation A) (i : Fin p.variableCount) :
    finiteStageVariables ({p} : finitePresentationSet A) :=
  ⟨⟨p, by simp⟩, i⟩

/-- The map out of `T(A)` induced by a cocone on the finite-stage diagram. -/
noncomputable def splittingAlgebraDesc {A : Type u} [CommRing A]
    (c : Cocone (finiteStageDiagram (A := A))) :
    splittingAlgebra A →ₐ[A] c.pt := by
  let val : (Σ p : StandardEtalePresentation A, Fin p.variableCount) → c.pt :=
    fun i ↦ c.ι.app {i.1}
      (Ideal.Quotient.mk _ (MvPolynomial.X (singletonStageVariable i.1 i.2)))
  let q : MvPolynomial (Σ p : StandardEtalePresentation A, Fin p.variableCount) A →ₐ[A] c.pt :=
    MvPolynomial.aeval val
  have hI :
      Ideal.span (Set.range fun i : Σ p : StandardEtalePresentation A, Fin p.variableCount ↦
        splittingRelation i.1 i.2) ≤ RingHom.ker q.toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨⟨p, i⟩, rfl⟩
    let s : finitePresentationSet A := {p}
    let r : MvPolynomial (Fin p.variableCount) A →ₐ[A] c.pt :=
      (c.ι.app s).hom.comp ((Ideal.Quotient.mkₐ A
        (Ideal.span (Set.range (finiteStageRelation s)))).comp
          (MvPolynomial.rename fun j ↦
            (singletonStageVariable p j : finiteStageVariables s)))
    have hcomp : q.comp (MvPolynomial.rename fun j ↦
        (⟨p, j⟩ : Σ p : StandardEtalePresentation A, Fin p.variableCount)) = r := by
      dsimp only [finiteStageDiagram]
      ext j
      simp [q, r, val, s, singletonStageVariable, AlgHom.comp_apply]
    have hz : Ideal.Quotient.mk (Ideal.span (Set.range (finiteStageRelation s)))
        (finiteStageRelation s (singletonStageVariable p i)) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨singletonStageVariable p i, rfl⟩
    change (q.comp (MvPolynomial.rename
      (fun j : Fin p.variableCount => (⟨p, j⟩ :
        Σ p : StandardEtalePresentation A, Fin p.variableCount))) (p.relations i)) = 0
    rw [AlgHom.congr_fun hcomp]
    change (c.ι.app s).hom
      (Ideal.Quotient.mk _ (MvPolynomial.rename
        (fun j ↦ (singletonStageVariable p j : finiteStageVariables s))
        (p.relations i))) = 0
    rw [show MvPolynomial.rename
      (fun j ↦ (singletonStageVariable p j : finiteStageVariables s)) (p.relations i) =
        finiteStageRelation s (singletonStageVariable p i) by rfl, hz, map_zero]
  exact Ideal.Quotient.liftₐ _ q (fun _ hx ↦ RingHom.mem_ker.mp (hI hx))

/-- `splittingAlgebraDesc` sends the generator `X ⟨p, i⟩` to the image of `X i` under the leg of
the cocone at the one-element stage `{p}`. -/
lemma splittingAlgebraDesc_generator {A : Type u} [CommRing A]
    (c : Cocone (finiteStageDiagram (A := A)))
    (p : StandardEtalePresentation A) (i : Fin p.variableCount) :
    splittingAlgebraDesc c (Ideal.Quotient.mk _
      (MvPolynomial.X (⟨p, i⟩ : Σ p : StandardEtalePresentation A, Fin p.variableCount))) =
        (c.ι.app {p}).hom
          (Ideal.Quotient.mk _ (MvPolynomial.X (singletonStageVariable p i))) := by
  unfold splittingAlgebraDesc
  rw [← Ideal.Quotient.mkₐ_eq_mk (R₁ := A), ← AlgHom.comp_apply,
    Ideal.Quotient.liftₐ_comp]
  simp [MvPolynomial.aeval_X, singletonStageVariable]

/-- `splittingAlgebraDesc` is a map of cocones: it is compatible with every leg of the
finite-stage cocone. -/
lemma splittingAlgebraDesc_stage {A : Type u} [CommRing A]
    (c : Cocone (finiteStageDiagram (A := A))) (s : finitePresentationSet A) :
    (splittingAlgebraDesc c).comp (finiteStageToSplittingAlgebra s) =
      (c.ι.app s).hom := by
  apply Ideal.Quotient.algHom_ext
  ext ⟨⟨p, hp⟩, j⟩
  let f : ({p} : finitePresentationSet A) ⟶ s :=
    homOfLE (Finset.singleton_subset_iff.mpr hp)
  have hn := congrArg (fun g : finiteStageDiagram.obj {p} ⟶ c.pt =>
    g.hom (Ideal.Quotient.mk _ (MvPolynomial.X (singletonStageVariable p j)))) (c.w f)
  simp only [finiteStageDiagram, CommAlgCat.hom_comp, CommAlgCat.hom_ofHom,
    finiteStageMap_mk, MvPolynomial.rename_X, AlgHom.comp_apply] at hn
  simp only [AlgHom.comp_apply]
  rw [show (Ideal.Quotient.mkₐ A (Ideal.span (Set.range (finiteStageRelation s))))
      (MvPolynomial.X (⟨⟨p, hp⟩, j⟩ : finiteStageVariables s)) =
      Ideal.Quotient.mk _ (MvPolynomial.X (⟨⟨p, hp⟩, j⟩ : finiteStageVariables s)) by rfl]
  rw [finiteStageToSplittingAlgebra_mk, MvPolynomial.rename_X,
    splittingAlgebraDesc_generator]
  exact hn.symm

/-- The leg of the finite-stage cocone at the one-element stage `{p}` sends the generator
`X (singletonStageVariable p i)` to the generator `X ⟨p, i⟩` of `T(A)`. -/
lemma finiteStageToSplittingAlgebra_singletonStageVariable {A : Type u} [CommRing A]
    (p : StandardEtalePresentation A) (i : Fin p.variableCount) :
    finiteStageToSplittingAlgebra ({p} : finitePresentationSet A)
        (Ideal.Quotient.mk _ (MvPolynomial.X (singletonStageVariable p i))) =
      Ideal.Quotient.mk _ (MvPolynomial.X
        (⟨p, i⟩ : Σ p : StandardEtalePresentation A, Fin p.variableCount)) := by
  rw [finiteStageToSplittingAlgebra_mk, MvPolynomial.rename_X]
  rfl

/-- `T(A)` is the colimit of the diagram of its finite stages. -/
noncomputable def finiteStageColimit {A : Type u} [CommRing A] :
    IsColimit (finiteStageCocone (A := A)) := by
  refine
    { desc := fun c ↦ CommAlgCat.ofHom (splittingAlgebraDesc c)
      fac := ?_
      uniq := ?_ }
  · exact fun c s ↦ CommAlgCat.hom_ext (splittingAlgebraDesc_stage c s)
  · intro c m hm
    apply CommAlgCat.hom_ext
    apply Ideal.Quotient.algHom_ext
    ext ⟨p, i⟩
    have h := congrArg (fun g : finiteStageDiagram.obj {p} ⟶ c.pt =>
      g.hom (Ideal.Quotient.mk _ (MvPolynomial.X (singletonStageVariable p i))))
      (hm {p})
    dsimp only [finiteStageCocone] at h
    change m.hom (finiteStageToSplittingAlgebra ({p} : finitePresentationSet A)
        (Ideal.Quotient.mk _ (MvPolynomial.X (singletonStageVariable p i)))) =
        (c.ι.app {p}).hom
          (Ideal.Quotient.mk _ (MvPolynomial.X (singletonStageVariable p i))) at h
    rw [finiteStageToSplittingAlgebra_singletonStageVariable] at h
    change m.hom (Ideal.Quotient.mk _ (MvPolynomial.X
      (⟨p, i⟩ : Σ p : StandardEtalePresentation A, Fin p.variableCount))) =
        splittingAlgebraDesc c (Ideal.Quotient.mk _ (MvPolynomial.X
          (⟨p, i⟩ : Σ p : StandardEtalePresentation A, Fin p.variableCount)))
    rw [splittingAlgebraDesc_generator]
    exact h

/-- The algebra presented by `p ∈ s`, as a summand of the finite stage indexed by `s`. -/
noncomputable def finiteStageObject {A : Type u} [CommRing A]
    (s : finitePresentationSet A) (p : {p : StandardEtalePresentation A // p ∈ s}) :
    CommAlgCat.{u} A := CommAlgCat.of A (presentedAlgebra A p.1.relations)

/-- The inclusion of the summand indexed by `p ∈ s` into the finite stage indexed by `s`. -/
noncomputable def finiteStageInclusion {A : Type u} [CommRing A]
    (s : finitePresentationSet A) (p : {p : StandardEtalePresentation A // p ∈ s}) :
    finiteStageObject s p ⟶ CommAlgCat.of A (finiteStageAlgebra s) := by
  let I : Ideal (MvPolynomial (finiteStageVariables s) A) :=
    Ideal.span (Set.range (finiteStageRelation s))
  let q : MvPolynomial (Fin p.1.variableCount) A →ₐ[A] finiteStageAlgebra s :=
    (Ideal.Quotient.mkₐ A I).comp
      (MvPolynomial.rename (fun i ↦ (⟨p, i⟩ : finiteStageVariables s)))
  have hI : Ideal.span (Set.range p.1.relations) ≤ RingHom.ker q.toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨⟨p, i⟩, rfl⟩)
  exact CommAlgCat.ofHom (Ideal.Quotient.liftₐ _ q (fun _ hx ↦
    RingHom.mem_ker.mp (hI hx)))

/-- The map from the finite stage indexed by `s` to the coproduct of its summands. -/
noncomputable def finiteStageToCoproduct {A : Type u} [CommRing A]
    (s : finitePresentationSet A) :
    finiteStageAlgebra s →ₐ[A]
      (Limits.sigmaObj (C := CommAlgCat.{u} A) (finiteStageObject s)) := by
  let val : finiteStageVariables s →
      (Limits.sigmaObj (C := CommAlgCat.{u} A) (finiteStageObject s)) := fun i ↦
    (Sigma.ι (finiteStageObject s) i.1).hom
      (Ideal.Quotient.mk _ (MvPolynomial.X i.2))
  let q : MvPolynomial (finiteStageVariables s) A →ₐ[A]
      (Limits.sigmaObj (C := CommAlgCat.{u} A) (finiteStageObject s)) :=
    MvPolynomial.aeval val
  have hI : Ideal.span (Set.range (finiteStageRelation s)) ≤ RingHom.ker q.toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change q (MvPolynomial.rename (fun j ↦ ⟨i.1, j⟩) (i.1.1.relations i.2)) = 0
    let r : MvPolynomial (Fin i.1.1.variableCount) A →ₐ[A]
        (Limits.sigmaObj (C := CommAlgCat.{u} A) (finiteStageObject s)) :=
      (Sigma.ι (finiteStageObject s) i.1).hom.comp
        (Ideal.Quotient.mkₐ A (Ideal.span (Set.range i.1.1.relations)))
    have hcomp : q.comp (MvPolynomial.rename (fun j ↦ ⟨i.1, j⟩)) = r := by
      ext j
      simp only [q, val, r, AlgHom.comp_apply, MvPolynomial.aeval_X,
        MvPolynomial.rename_X]
      rfl
    change (q.comp (MvPolynomial.rename (fun j ↦ ⟨i.1, j⟩)))
      (i.1.1.relations i.2) = 0
    rw [hcomp]
    change (Sigma.ι (finiteStageObject s) i.1).hom
      (Ideal.Quotient.mk _ (i.1.1.relations i.2)) = 0
    rw [show Ideal.Quotient.mk (Ideal.span (Set.range i.1.1.relations))
        (i.1.1.relations i.2) = 0 by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨i.2, rfl⟩]
    exact map_zero _
  exact Ideal.Quotient.liftₐ _ q (fun _ hx ↦ RingHom.mem_ker.mp (hI hx))

/-- The map from the coproduct of the summands of the stage `s` to the stage itself. -/
noncomputable def finiteStageFromCoproduct {A : Type u} [CommRing A]
    (s : finitePresentationSet A) :
    Limits.sigmaObj (C := CommAlgCat.{u} A) (finiteStageObject s) ⟶
      CommAlgCat.of A (finiteStageAlgebra s) :=
  Sigma.desc (finiteStageInclusion s)

/-- `finiteStageInclusion` on the class of a polynomial renames its variables. -/
lemma finiteStageInclusion_mk {A : Type u} [CommRing A]
    (s : finitePresentationSet A) (p : {p : StandardEtalePresentation A // p ∈ s})
    (x : MvPolynomial (Fin p.1.variableCount) A) :
    (finiteStageInclusion s p).hom (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _
        (MvPolynomial.rename (fun i ↦ (⟨p, i⟩ : finiteStageVariables s)) x) := by
  unfold finiteStageInclusion
  rfl

/-- `finiteStageInclusion` sends the generator `X j` of the summand indexed by `p` to the
generator `X ⟨p, j⟩` of the stage. -/
lemma finiteStageInclusion_generator {A : Type u} [CommRing A]
    (s : finitePresentationSet A) (p : {p : StandardEtalePresentation A // p ∈ s})
    (j : Fin p.1.variableCount) :
    (finiteStageInclusion s p).hom (Ideal.Quotient.mk _ (MvPolynomial.X j)) =
      Ideal.Quotient.mk _ (MvPolynomial.X (⟨p, j⟩ : finiteStageVariables s)) := by
  rw [finiteStageInclusion_mk, MvPolynomial.rename_X]

/-- `finiteStageToCoproduct` on the class of a polynomial is the evaluation sending each variable
to the corresponding generator of its summand. -/
lemma finiteStageToCoproduct_mk {A : Type u} [CommRing A]
    (s : finitePresentationSet A) (x : MvPolynomial (finiteStageVariables s) A) :
    finiteStageToCoproduct s (Ideal.Quotient.mk _ x) =
      MvPolynomial.aeval
      (fun i : finiteStageVariables s ↦
          (Sigma.ι (finiteStageObject s) i.1).hom
            (Ideal.Quotient.mk _ (MvPolynomial.X i.2))) x := by
  unfold finiteStageToCoproduct
  rfl

/-- `finiteStageToCoproduct` sends the generator `X ⟨p, j⟩` to the image of `X j` under the
coprojection of the summand indexed by `p`. -/
lemma finiteStageToCoproduct_generator {A : Type u} [CommRing A]
    (s : finitePresentationSet A) (p : {p : StandardEtalePresentation A // p ∈ s})
    (j : Fin p.1.variableCount) :
    finiteStageToCoproduct s
        (Ideal.Quotient.mk _ (MvPolynomial.X (⟨p, j⟩ : finiteStageVariables s))) =
      (Sigma.ι (finiteStageObject s) p).hom
        (Ideal.Quotient.mk _ (MvPolynomial.X j)) := by
  rw [finiteStageToCoproduct_mk]
  simp [MvPolynomial.aeval_X]

/-- `finiteStageFromCoproduct` restricted to a summand is the inclusion of that summand. -/
lemma finiteStageFromCoproduct_ι {A : Type u} [CommRing A]
    (s : finitePresentationSet A) (p : {p : StandardEtalePresentation A // p ∈ s})
    (x : finiteStageObject s p) :
    finiteStageFromCoproduct s ((Sigma.ι (finiteStageObject s) p).hom x) =
      (finiteStageInclusion s p).hom x := by
  change (CommAlgCat.Hom.hom (Sigma.desc (finiteStageInclusion s)))
      ((Sigma.ι (finiteStageObject s) p).hom x) = _
  have h := congrArg CommAlgCat.Hom.hom
    (Sigma.ι_comp_desc (finiteStageInclusion s) p)
  exact congrArg (fun f ↦ f x) h

/-- `finiteStageToCoproduct` undoes `finiteStageInclusion`: the composite is the coprojection of
the summand. -/
lemma finiteStageToCoproduct_inclusion {A : Type u} [CommRing A]
    (s : finitePresentationSet A) (p : {p : StandardEtalePresentation A // p ∈ s}) :
    (finiteStageToCoproduct s).comp (finiteStageInclusion s p).hom =
      (Sigma.ι (finiteStageObject s) p).hom := by
  apply Ideal.Quotient.algHom_ext
  ext j
  change finiteStageToCoproduct s
      ((finiteStageInclusion s p).hom (Ideal.Quotient.mk _ (MvPolynomial.X j))) =
    (Sigma.ι (finiteStageObject s) p).hom (Ideal.Quotient.mk _ (MvPolynomial.X j))
  rw [finiteStageInclusion_generator, finiteStageToCoproduct_generator]

/-- `finiteStageToCoproduct` followed by `finiteStageFromCoproduct` is the identity. -/
lemma finiteStageCoproduct_left_id {A : Type u} [CommRing A]
    (s : finitePresentationSet A) :
    CommAlgCat.ofHom (finiteStageToCoproduct s) ≫ finiteStageFromCoproduct s = 𝟙 _ := by
  apply CommAlgCat.hom_ext
  apply Ideal.Quotient.algHom_ext
  ext ⟨p, j⟩
  change finiteStageFromCoproduct s
      (finiteStageToCoproduct s
        (Ideal.Quotient.mk _ (MvPolynomial.X (⟨p, j⟩ : finiteStageVariables s)))) =
    Ideal.Quotient.mk _ (MvPolynomial.X (⟨p, j⟩ : finiteStageVariables s))
  rw [finiteStageToCoproduct_generator]
  exact (finiteStageFromCoproduct_ι s p _).trans (finiteStageInclusion_generator s p j)

/-- `finiteStageFromCoproduct` followed by `finiteStageToCoproduct` is the identity. -/
lemma finiteStageCoproduct_right_id {A : Type u} [CommRing A]
    (s : finitePresentationSet A) :
    finiteStageFromCoproduct s ≫ CommAlgCat.ofHom (finiteStageToCoproduct s) = 𝟙 _ := by
  refine Sigma.hom_ext _ _ fun p ↦ ?_
  change ((Sigma.ι (finiteStageObject s) p ≫
      Sigma.desc (finiteStageInclusion s)) ≫
      CommAlgCat.ofHom (finiteStageToCoproduct s)) = _
  rw [Sigma.ι_comp_desc]
  exact CommAlgCat.hom_ext (finiteStageToCoproduct_inclusion s p)

/-- The finite stage indexed by `s` is the coproduct in `CommAlgCat A` of the algebras presented
by the members of `s`. -/
noncomputable def finiteStageCoproductIso {A : Type u} [CommRing A]
    (s : finitePresentationSet A) :
    CommAlgCat.of A (finiteStageAlgebra s) ≅
      Limits.sigmaObj (C := CommAlgCat.{u} A) (finiteStageObject s) where
  hom := CommAlgCat.ofHom (finiteStageToCoproduct s)
  inv := finiteStageFromCoproduct s
  hom_inv_id := finiteStageCoproduct_left_id s
  inv_hom_id := finiteStageCoproduct_right_id s

/-- Every finite stage of `T(A)` is étale over `A`. -/
lemma finiteStageAlgebra_etale {A : Type u} [CommRing A]
    (s : finitePresentationSet A) : Algebra.Etale A (finiteStageAlgebra s) :=
  etaleObject_of_iso (finiteStageCoproductIso s).symm
    (etale_finite_coproduct A (finiteStageObject s) (fun p ↦ presentedAlgebra_etale p.1))

/-- Every finite stage of `T(A)` is faithfully flat over `A`. -/
lemma finiteStageAlgebra_faithfullyFlat {A : Type u} [CommRing A]
    (s : finitePresentationSet A) :
    (algebraMap A (finiteStageAlgebra s)).FaithfullyFlat :=
  faithfullyFlatObject_of_iso (finiteStageCoproductIso s).symm
    (faithfullyFlat_finite_coproduct A (finiteStageObject s) (fun p ↦ p.1.faithfullyFlat))

/-- The finite-stage colimit presentation of `T(A)`. -/
noncomputable def splittingAlgebraPresentation (A : Type u) [CommRing A] :
    ColimitPresentation (finitePresentationSet A) (CommAlgCat.of A (splittingAlgebra A)) where
  diag := finiteStageDiagram
  ι := (finiteStageCocone (A := A)).ι
  isColimit := finiteStageColimit

/-- `T(A)` is faithfully flat over `A`. -/
lemma splittingAlgebra_faithfullyFlat (A : Type u) [CommRing A] :
    (algebraMap A (splittingAlgebra A)).FaithfullyFlat :=
  RingHom.faithfullyFlat_algebraMap_iff.mpr <|
    faithfullyFlat_of_colimitPresentation (splittingAlgebraPresentation A) (fun s ↦
      RingHom.faithfullyFlat_algebraMap_iff.mp (finiteStageAlgebra_faithfullyFlat s))

/-- `T(A)` is an ind-étale `A`-algebra. -/
lemma splittingAlgebra_ind_etale (A : Type u) [CommRing A] :
    (CommAlgCat.etale A).ind.{u} (CommAlgCat.of A (splittingAlgebra A)) := by
  have hfin : (CommAlgCat.etale A) ≤
      ObjectProperty.isFinitelyPresentable.{u} (CommAlgCat.{u} A) :=
    fun X hX ↦ etale_isFinitelyPresentable A X hX
  have h : ((CommAlgCat.etale A).ind.{u}).ind.{u}
      (CommAlgCat.of A (splittingAlgebra A)) :=
    ObjectProperty.of_essentiallySmall_index (splittingAlgebraPresentation A) (fun s ↦
      ObjectProperty.le_ind _ _ (finiteStageAlgebra_etale s))
  rwa [ObjectProperty.ind_ind hfin] at h

end AlgebraicGeometry.ProEtale

end
