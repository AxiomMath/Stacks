module

public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRing.ChartChange

/-!
# Versal rings: independence of the affine-open presentation (Stacks 0DQV)

The predeformation category of a field-valued point is built from a chosen affine open
`Spec Λ ⊆ S` through which `Spec k ⟶ S` factors. The main theorem shows that the notion does not
depend on that choice: a ring isomorphism of the two complete local algebras over `S` which
matches their identifications of the residue field with `k` carries versality to versality.

## Main results

* `AlgebraicGeometry.Stack.isVersalRingAt_iff_of_affineOpenPresentation`: being a versal ring
  does not depend on the affine-open presentation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Stack

universe u v w

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

attribute [local implicit_reducible] rebaseArtinianAlgebra rebaseCompleteLocalAlgebra
  rebaseArtinianAlgebraCanonical rebaseArtinianFunctorCanonical
  Deformation.AdicTruncation.obj

attribute [local implicit_reducible] completeOpenRebase completeOpenRebaseFunctor

/-- Two `Λ`-algebra equivalences with the same underlying ring equivalence are equal. -/
private theorem algEquiv_eq_of_toRingEquiv_eq
    {Λ k R : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [CommRing R] [Algebra Λ R]
    (ea eb : R ≃ₐ[Λ] k) (he : ea.toRingEquiv = eb.toRingEquiv) : ea = eb :=
  AlgEquiv.ext fun r => congrArg (fun e : R ≃+* k => e r) he

/-- Two objects of `CompleteLocalAlgCat` on one carrier with equal algebra structures and equal
residue-field identifications are equal. -/
private theorem completeAlgebra_eq
    {Λ k R : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    [CommRing R] [IsLocalRing R] (hR : IsNoetherianCompleteLocalRing R)
    (a b : Algebra Λ R)
    (ea : letI := a; ResidueField R ≃ₐ[Λ] k)
    (eb : letI := b; ResidueField R ≃ₐ[Λ] k)
    (hab : a = b)
    (he : (letI := a; ea.toRingEquiv) = (letI := b; eb.toRingEquiv)) :
    (show Deformation.CompleteLocalAlgCat Λ k from
      { carrier := R, algebra := a, completeLocal := hR, residueEquiv := ea }) =
    { carrier := R, algebra := b, completeLocal := hR, residueEquiv := eb } := by
  cases hab
  let := a
  cases algEquiv_eq_of_toRingEquiv_eq ea eb he
  rfl

/-- Ring maps into a ring `T` that agree after `Spec` and composition with a monomorphism are
equal. -/
private theorem ringHom_eq_of_spec_comp_eq
    {R T : Type u} [CommRing R] [CommRing T] {S : Scheme.{u}} (i : Spec (.of R) ⟶ S) [Mono i]
    {g g' : R →+* T}
    (h : Spec.map (CommRingCat.ofHom g) ≫ i = Spec.map (CommRingCat.ofHom g') ≫ i) : g = g' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono i).mp h))

/-- `rebaseCompleteLocalAlgebra` depends only on the ring map, not on the compatibility proof. -/
private theorem rebaseCompleteLocalAlgebra_congr
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (g h : Λ' →+* A)
    (hg : ∀ a : Λ', A.residueEquiv (residue A (g a)) = algebraMap Λ' k a)
    (hh : ∀ a : Λ', A.residueEquiv (residue A (h a)) = algebraMap Λ' k a)
    (e : g = h) : rebaseCompleteLocalAlgebra A g hg = rebaseCompleteLocalAlgebra A h hh := by
  cases e
  rfl

/-- Open rebasing to `Λ'` and back to `Λ` returns the original complete local algebra. -/
private theorem completeOpenRebase_roundtrip
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ : IsOpenImmersion iΛ) (hiΛ' : IsOpenImmersion iΛ')
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k) :
    completeOpenRebase iΛ' iΛ hiΛ hclosed.symm
      (completeOpenRebase iΛ iΛ' hiΛ' hclosed A) = A := by
  let := hiΛ
  let B := completeOpenRebase iΛ iΛ' hiΛ' hclosed A
  let g := (completeLocalOpenLift_data iΛ' iΛ hiΛ hclosed.symm B).choose
  have hg : g = algebraMap Λ A :=
    ringHom_eq_of_spec_comp_eq iΛ ((completeOpenRebase_fac iΛ' iΛ hiΛ hclosed.symm B).trans
      (completeOpenRebase_fac iΛ iΛ' hiΛ' hclosed A))
  change rebaseCompleteLocalAlgebra B g _ = A
  rw [rebaseCompleteLocalAlgebra_congr B g (algebraMap Λ A) _
    (fun a => A.residueEquiv.commutes a) hg]
  simp only [B, completeOpenRebase, rebaseCompleteLocalAlgebra]
  cases A with
  | @mk R hR alg hlocal eq =>
    let := hR
    let := alg
    let := hlocal.isLocal
    apply completeAlgebra_eq (R := R)
    · exact Algebra.algebra_ext _ _ (fun _ => rfl)
    · rfl

/-- Two objects of `ArtinianLocalAlgCat` on one carrier with equal algebra structures and equal
residue-field identifications are equal. -/
private theorem artinianAlgebra_eq
    {Λ k R : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    [CommRing R] [IsArtinianRing R] [IsLocalRing R]
    (a b : Algebra Λ R)
    (ea : letI := a; ResidueField R ≃ₐ[Λ] k)
    (eb : letI := b; ResidueField R ≃ₐ[Λ] k)
    (hab : a = b)
    (he : (letI := a; ea.toRingEquiv) = (letI := b; eb.toRingEquiv)) :
    (show Deformation.ArtinianLocalAlgCat Λ k from
      { carrier := R, algebra := a, residueEquiv := ea }) =
    { carrier := R, algebra := b, residueEquiv := eb } := by
  cases hab
  let := a
  cases algEquiv_eq_of_toRingEquiv_eq ea eb he
  rfl

/-- Canonical rebasing to `Λ'` and back to `Λ` returns the original Artinian local algebra. -/
private theorem rebaseArtinian_roundtrip
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ : IsOpenImmersion iΛ) (hiΛ' : IsOpenImmersion iΛ')
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    rebaseArtinianAlgebraCanonical iΛ' iΛ hiΛ hclosed.symm
      (rebaseArtinianAlgebraCanonical iΛ iΛ' hiΛ' hclosed B) = B := by
  change rebaseArtinianAlgebra _ _ _ = B
  rw [rebaseArtinianAlgebra_congr
    (rebaseArtinianAlgebraCanonical iΛ iΛ' hiΛ' hclosed B) _ (algebraMap Λ B) _
    (fun a => B.residueEquiv.commutes a)
    (canonicalOpenLift_roundtrip iΛ iΛ' hiΛ hiΛ' hclosed B)]
  simp only [rebaseArtinianAlgebraCanonical, rebaseArtinianAlgebra]
  cases B
  apply artinianAlgebra_eq
  · exact Algebra.algebra_ext _ _ (fun _ => rfl)
  · rfl

/-- The canonical rebasing functor is full. -/
private theorem rebaseArtinian_full
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ : IsOpenImmersion iΛ) (hiΛ' : IsOpenImmersion iΛ')
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') :
    (rebaseArtinianFunctorCanonical iΛ iΛ' hiΛ' hclosed).Full := by
  let G := rebaseArtinianFunctorCanonical iΛ iΛ' hiΛ' hclosed
  let H := rebaseArtinianFunctorCanonical iΛ' iΛ hiΛ hclosed.symm
  refine ⟨?_⟩
  intro B C f
  let hB := rebaseArtinian_roundtrip iΛ iΛ' hiΛ hiΛ' hclosed B
  let hC := rebaseArtinian_roundtrip iΛ iΛ' hiΛ hiΛ' hclosed C
  refine ⟨eqToHom hB.symm ≫ H.map f ≫ eqToHom hC, ?_⟩
  apply Deformation.ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  change ∀ b : B, (eqToHom hC).hom ((H.map f).hom ((eqToHom hB.symm).hom b)) = f.hom b
  intro b
  rw [eqToHom_artinian_hom_apply, eqToHom_artinian_hom_apply]
  have hB' : congrArg Deformation.ArtinianLocalAlgCat.carrier hB.symm = rfl :=
    Subsingleton.elim _ _
  have hC' : congrArg Deformation.ArtinianLocalAlgCat.carrier hC = rfl :=
    Subsingleton.elim _ _
  rw [hB', hC']
  rfl

/-- The canonical rebasing functor is faithful. -/
private theorem rebaseArtinian_faithful
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') :
    (rebaseArtinianFunctorCanonical iΛ iΛ' hiΛ' hclosed).Faithful := by
  constructor
  intro B C f g h
  apply Deformation.ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro b
  exact congrArg (fun t => t.hom b) h

/-- Functors that are mutually inverse on the nose form an equivalence. -/
private theorem isEquivalence_of_comp_eq_id
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (H : D ⥤ C)
    (h : F ⋙ H = 𝟭 C) (h' : H ⋙ F = 𝟭 D) : F.IsEquivalence :=
  (CategoryTheory.Equivalence.mk F H (eqToIso h.symm) (eqToIso h')).isEquivalence_functor

section DeformationChart

variable {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
  [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
  (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
  (hiΛ : IsOpenImmersion iΛ) (hiΛ' : IsOpenImmersion iΛ')
  {X : Type w} [Category.{v} X] (q : X ⥤ Over S) (x₀ : X)
  (hx₀ : q.obj x₀ = Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hx₀' : q.obj x₀ = Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))

/-- Rebasing a deformation object to `Λ'` and back returns it. -/
private theorem rebaseDeformation_roundtrip
    (a : Deformation.Artin.DeformationObject iΛ q x₀ hx₀) :
    rebaseDeformationObject iΛ' iΛ hiΛ q x₀ hx₀' hx₀
      (rebaseDeformationObject iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' a) = a := by
  apply Deformation.Artin.deformationObject_ext
  · exact rebaseArtinian_roundtrip iΛ iΛ' hiΛ hiΛ'
      (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') a.algebra
  · rfl
  · rfl

/-- Morphisms of deformation objects with the same arrow are equal. -/
private theorem deformationMorphism_ext_arrow
    {a b : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    {f g : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b}
    (h : f.arrow = g.arrow) : f = g := by
  apply deformationMorphism_ext_of_ringMap
  · have hs := f.arrow_base.symm.trans ((congrArg
      (fun t => eqToHom (congrArg Over.left b.base).symm ≫
        (q.map t).left ≫ eqToHom (congrArg Over.left a.base)) h).trans g.arrow_base)
    intro a
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective hs)) a
  · exact h

/-- The two chart-change functors are mutually inverse on objects. -/
private theorem chartChange_roundtrip_obj
    (a : (Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).carrier) :
    (chartChangePredeformationFunctor iΛ' iΛ hiΛ q x₀ hx₀' hx₀).obj
      ((chartChangePredeformationFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀').obj a) = a := by
  apply (Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).objects.injective
  rw [chartChange_objects, chartChange_objects]
  exact rebaseDeformation_roundtrip iΛ iΛ' hiΛ hiΛ' q x₀ hx₀ hx₀' _

/-- The arrow of a chart-changed morphism is the original arrow. -/
theorem chartChange_arrow
    {a b : (Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).carrier} (f : a ⟶ b) :
    let C := Deformation.Artin.predeformationCategory iΛ q x₀ hx₀
    let C' := Deformation.Artin.predeformationCategory iΛ' q x₀ hx₀'
    let F := chartChangePredeformationFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀'
    (C'.morphisms (F.obj a) (F.obj b) (F.map f)).arrow =
      eqToHom (congrArg Deformation.Artin.DeformationObject.point
        (chartChange_objects iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' b)) ≫
      (C.morphisms a b f).arrow ≫
      eqToHom (congrArg Deformation.Artin.DeformationObject.point
        (chartChange_objects iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' a)).symm := by
  dsimp only
  let C := Deformation.Artin.predeformationCategory iΛ q x₀ hx₀
  let C' := Deformation.Artin.predeformationCategory iΛ' q x₀ hx₀'
  let F := chartChangePredeformationFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀'
  let m := transportDeformationMorphism
    (chartChange_objects iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' a)
    (chartChange_objects iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' b)
    (rebaseDeformationMorphism iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' (C.morphisms a b f))
  change ((C'.morphisms (F.obj a) (F.obj b))
    ((C'.morphisms (F.obj a) (F.obj b)).symm m)).arrow = _
  rw [(C'.morphisms (F.obj a) (F.obj b)).apply_symm_apply m]
  exact transportDeformationMorphism_arrow _ _ _

/-- The arrow attached to `eqToHom` in a predeformation category is the corresponding `eqToHom` of
points. -/
private theorem predeformation_eqToHom_arrow
    {a b : (Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).carrier} (h : a = b) :
    let C := Deformation.Artin.predeformationCategory iΛ q x₀ hx₀
    (C.morphisms a b (eqToHom h)).arrow =
      eqToHom (congrArg (fun z => (C.objects z).point) h).symm := by
  cases h
  exact (Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).reversed_identity a

/-- The two chart-change functors compose to the identity. -/
private theorem chartChange_roundtrip
    : chartChangePredeformationFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' ⋙
        chartChangePredeformationFunctor iΛ' iΛ hiΛ q x₀ hx₀' hx₀ =
      𝟭 (Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).carrier := by
  let C := Deformation.Artin.predeformationCategory iΛ q x₀ hx₀
  refine CategoryTheory.Functor.ext (chartChange_roundtrip_obj iΛ iΛ' hiΛ hiΛ' q x₀ hx₀ hx₀') ?_
  intro a b f
  apply (C.morphisms _ _).injective
  apply deformationMorphism_ext_arrow
  dsimp only [C, Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map]
  simp only [chartChange_arrow,
    (Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).reversed_composition,
    predeformation_eqToHom_arrow]
  apply eqToHom_squeeze

include hiΛ in
/-- The chart-change functor is full. -/
private theorem chartChange_full :
    (chartChangePredeformationFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀').Full := by
  have := isEquivalence_of_comp_eq_id _ _
    (chartChange_roundtrip iΛ iΛ' hiΛ hiΛ' q x₀ hx₀ hx₀')
    (chartChange_roundtrip iΛ' iΛ hiΛ' hiΛ q x₀ hx₀' hx₀)
  infer_instance

include hiΛ in
/-- The chart-change functor is faithful. -/
private theorem chartChange_faithful :
    (chartChangePredeformationFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀').Faithful := by
  have := isEquivalence_of_comp_eq_id _ _
    (chartChange_roundtrip iΛ iΛ' hiΛ hiΛ' q x₀ hx₀ hx₀')
    (chartChange_roundtrip iΛ' iΛ hiΛ' hiΛ q x₀ hx₀' hx₀)
  infer_instance

end DeformationChart

/-- A formal object for `p'` built from a formal object for `p` whose adic truncations are carried
over by `G`. -/
noncomputable def formalObjectOfRebasedTruncations
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    {C : Type*} {C' : Type*} [Category C] [Category C']
    {p : C ⥤ Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    {p' : C' ⥤ Deformation.ArtinianLocalAlgCat.{u, u, u} Λ' k}
    (G : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k ⥤
      Deformation.ArtinianLocalAlgCat.{u, u, u} Λ' k)
    (F : BasedFunctor (BasedCategory.ofFunctor (p ⋙ G)) (BasedCategory.ofFunctor p'))
    (ξ : Deformation.FormalObject p)
    (A' : Deformation.CompleteLocalAlgCat.{u, u, u} Λ' k)
    (hobj : ∀ n, G.obj (Deformation.AdicTruncation.obj ξ.base n) =
      Deformation.AdicTruncation.obj A' n)
    (htransition : ∀ n,
      eqToHom (hobj (n + 1)).symm ≫
        G.map (Deformation.AdicTruncation.transition ξ.base n) ≫ eqToHom (hobj n) =
      Deformation.AdicTruncation.transition A' n) : Deformation.FormalObject p' where
  base := A'
  level n := F.obj (ξ.level n)
  level_eq n := (F.w_obj (ξ.level n)).trans
    ((congrArg G.obj (ξ.level_eq n)).trans (hobj n))
  transition n := F.map (ξ.transition n)
  transition_lift n := by
    have h := Functor.isHomLift_comp_functor G _ _ (ξ.transition_lift n)
    have h' := (F.isHomLift_iff _ _).mpr h
    change p'.IsHomLift (G.map (Deformation.AdicTruncation.transition ξ.base n))
      (F.map (ξ.transition n)) at h'
    change p'.IsHomLift (Deformation.AdicTruncation.transition A' n)
      (F.map (ξ.transition n))
    rw [← htransition n]
    let := h'
    infer_instance

/-- Rebasing of formal objects along compatible functors on Artinian and on complete local
algebras. -/
noncomputable def formalObjectRebaseFunctor
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    {C : Type*} {C' : Type*} [Category C] [Category C']
    {p : C ⥤ Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    {p' : C' ⥤ Deformation.ArtinianLocalAlgCat.{u, u, u} Λ' k}
    (G : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k ⥤
      Deformation.ArtinianLocalAlgCat.{u, u, u} Λ' k)
    (H : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k ⥤
      Deformation.CompleteLocalAlgCat.{u, u, u} Λ' k)
    (F : BasedFunctor (BasedCategory.ofFunctor (p ⋙ G)) (BasedCategory.ofFunctor p'))
    (hobj : ∀ A n, G.obj (Deformation.AdicTruncation.obj A n) =
      Deformation.AdicTruncation.obj (H.obj A) n)
    (htransition : ∀ A n,
      eqToHom (hobj A (n + 1)).symm ≫
        G.map (Deformation.AdicTruncation.transition A n) ≫ eqToHom (hobj A n) =
      Deformation.AdicTruncation.transition (H.obj A) n)
    (hmap : ∀ {A B} (f : A ⟶ B) n,
      eqToHom (hobj A n).symm ≫
        G.map (Deformation.AdicTruncation.map f n) ≫ eqToHom (hobj B n) =
      Deformation.AdicTruncation.map (H.map f) n) :
    Deformation.FormalObject p ⥤ Deformation.FormalObject p' where
  obj ξ := formalObjectOfRebasedTruncations G F ξ (H.obj ξ.base)
    (hobj ξ.base) (htransition ξ.base)
  map {ξ η} f := {
    base := H.map f.base
    app n := F.map (f.app n)
    app_lift n := by
      have h := Functor.isHomLift_comp_functor G _ _ (f.app_lift n)
      have h' := (F.isHomLift_iff _ _).mpr h
      change p'.IsHomLift (G.map (Deformation.AdicTruncation.map f.base n))
        (F.map (f.app n)) at h'
      change p'.IsHomLift (Deformation.AdicTruncation.map (H.map f.base) n)
        (F.map (f.app n))
      rw [← hmap f.base n]
      let := h'
      infer_instance
    naturality n := by
      change F.map (ξ.transition n) ≫ F.map (f.app n) =
        F.map (f.app (n + 1)) ≫ F.map (η.transition n)
      simp only [← Functor.map_comp, f.naturality] }
  map_id ξ := by
    apply Deformation.FormalObject.Hom.ext
    · exact H.map_id _
    · exact fun n => F.toFunctor.map_id _
  map_comp f g := by
    apply Deformation.FormalObject.Hom.ext
    · exact H.map_comp _ _
    · exact fun n => F.toFunctor.map_comp _ _

/-- A formal object of the predeformation category of the second presentation, built from one of
the first. -/
private noncomputable def chartChangeFormalObject
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    {X : Type w} [Category.{v} X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).projection)
    (g : Λ' →+* ξ.base)
    (hg : ∀ a : Λ', ξ.base.residueEquiv (residue ξ.base (g a)) = algebraMap Λ' k a)
    (hS : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom g) ≫ iΛ') :
    Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ' q x₀ hx₀').projection :=
  formalObjectOfRebasedTruncations
    (rebaseArtinianFunctorCanonical iΛ iΛ' hiΛ'
      (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀'))
    (chartChangeBasedFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀') ξ
    (rebaseCompleteLocalAlgebra ξ.base g hg)
    (rebaseArtinianCanonical_truncation iΛ iΛ' hiΛ'
      (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') ξ.base g hg hS)
    (rebaseArtinianCanonical_transition iΛ iΛ' hiΛ'
      (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') ξ.base g hg hS)

/-- The chart-change functor on the formal objects of the two predeformation categories. -/
noncomputable def chartChangeFormalFunctor
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    {X : Type w} [Category.{v} X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')) :
    Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).projection ⥤
      Deformation.FormalObject
        (Deformation.Artin.predeformationCategory iΛ' q x₀ hx₀').projection := by
  let hc := closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀'
  refine formalObjectRebaseFunctor
    (rebaseArtinianFunctorCanonical iΛ iΛ' hiΛ' hc)
    (completeOpenRebaseFunctor iΛ iΛ' hiΛ' hc)
    (chartChangeBasedFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀')
    (completeOpenRebase_truncation iΛ iΛ' hiΛ' hc) ?_
    (fun f n => completeOpenRebase_truncation_map iΛ iΛ' hiΛ' hc f n)
  intro A n
  exact rebaseArtinianCanonical_transition iΛ iΛ' hiΛ' hc A
    (completeLocalOpenLift_data iΛ iΛ' hiΛ' hc A).choose
    (completeLocalOpenLift_data iΛ iΛ' hiΛ' hc A).choose_spec.1
    (completeLocalOpenLift_data iΛ iΛ' hiΛ' hc A).choose_spec.2.symm n

/-- The base component of `eqToHom` of an equality of formal objects. -/
private theorem formal_eqToHom_base
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {C : Type*} [Category C]
    {p : C ⥤ Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    {ξ η : Deformation.FormalObject p} (h : ξ = η) :
    (eqToHom h).base = eqToHom (congrArg Deformation.FormalObject.base h) := by
  cases h
  rfl

/-- The level-`n` component of `eqToHom` of an equality of formal objects. -/
private theorem formal_eqToHom_app
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {C : Type*} [Category C]
    {p : C ⥤ Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    {ξ η : Deformation.FormalObject p} (h : ξ = η) (n : ℕ) :
    (eqToHom h).app n = eqToHom (congrArg (fun ζ => ζ.level n) h) := by
  cases h
  rfl

/-- `eqToHom` of an equality of complete local algebras acts on elements by `cast`. -/
private theorem eqToHom_complete_hom_apply
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k} (h : A = B) (x : A) :
    (eqToHom h).hom x = cast (congrArg Deformation.CompleteLocalAlgCat.carrier h) x := by
  cases h
  rfl

attribute [local implicit_reducible] chartChangeFormalFunctor
  formalObjectRebaseFunctor formalObjectOfRebasedTruncations

section FormalChart

variable {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
  [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
  (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
  (hiΛ : IsOpenImmersion iΛ) (hiΛ' : IsOpenImmersion iΛ')
  {X : Type w} [Category.{v} X] (q : X ⥤ Over S) (x₀ : X)
  (hx₀ : q.obj x₀ = Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hx₀' : q.obj x₀ = Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))

/-- The two chart-change functors on formal objects are mutually inverse on objects. -/
private theorem chartChangeFormal_roundtrip_obj
    (ξ : Deformation.FormalObject
      (Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).projection) :
    (chartChangeFormalFunctor iΛ' iΛ hiΛ q x₀ hx₀' hx₀).obj
      ((chartChangeFormalFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀').obj ξ) = ξ := by
  refine Deformation.FormalObject.ext ?_
    (fun n => chartChange_roundtrip_obj iΛ iΛ' hiΛ hiΛ' q x₀ hx₀ hx₀' (ξ.level n)) ?_
  · exact completeOpenRebase_roundtrip iΛ iΛ' hiΛ hiΛ'
      (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') ξ.base
  · intro n
    exact Functor.congr_hom (chartChange_roundtrip iΛ iΛ' hiΛ hiΛ' q x₀ hx₀ hx₀')
      (ξ.transition n)

/-- The two chart-change functors on formal objects compose to the identity. -/
private theorem chartChangeFormal_roundtrip :
    chartChangeFormalFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' ⋙
      chartChangeFormalFunctor iΛ' iΛ hiΛ q x₀ hx₀' hx₀ =
    𝟭 (Deformation.FormalObject
      (Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).projection) := by
  refine CategoryTheory.Functor.ext
    (chartChangeFormal_roundtrip_obj iΛ iΛ' hiΛ hiΛ' q x₀ hx₀ hx₀') ?_
  intro ξ η f
  let hξ := chartChangeFormal_roundtrip_obj iΛ iΛ' hiΛ hiΛ' q x₀ hx₀ hx₀' ξ
  let hη := chartChangeFormal_roundtrip_obj iΛ iΛ' hiΛ hiΛ' q x₀ hx₀ hx₀' η
  apply Deformation.FormalObject.Hom.ext
  · change _ = (eqToHom hξ).base ≫ f.base ≫ (eqToHom hη.symm).base
    rw [formal_eqToHom_base, formal_eqToHom_base]
    apply Deformation.CompleteLocalAlgCat.Hom.ext
    apply AlgHom.ext
    intro a
    change f.base.hom a =
      (eqToHom (congrArg Deformation.FormalObject.base hη).symm).hom
        (f.base.hom ((eqToHom (congrArg Deformation.FormalObject.base hξ)).hom a))
    rw [eqToHom_complete_hom_apply, eqToHom_complete_hom_apply]
    rfl
  · intro n
    change _ = (eqToHom hξ).app n ≫ f.app n ≫ (eqToHom hη.symm).app n
    rw [formal_eqToHom_app, formal_eqToHom_app]
    exact Functor.congr_hom (chartChange_roundtrip iΛ iΛ' hiΛ hiΛ' q x₀ hx₀ hx₀')
      (f.app n)

include hiΛ in
/-- The chart-change functor on formal objects is full. -/
private theorem chartChangeFormal_full :
    (chartChangeFormalFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀').Full := by
  have := isEquivalence_of_comp_eq_id _ _
    (chartChangeFormal_roundtrip iΛ iΛ' hiΛ hiΛ' q x₀ hx₀ hx₀')
    (chartChangeFormal_roundtrip iΛ' iΛ hiΛ' hiΛ q x₀ hx₀' hx₀)
  infer_instance

include hiΛ in
/-- The chart-change functor on formal objects is surjective on objects. -/
private theorem chartChangeFormal_surjective :
    Function.Surjective (chartChangeFormalFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀').obj := by
  intro ξ
  exact ⟨(chartChangeFormalFunctor iΛ' iΛ hiΛ q x₀ hx₀' hx₀).obj ξ,
    chartChangeFormal_roundtrip_obj iΛ' iΛ hiΛ' hiΛ q x₀ hx₀' hx₀ ξ⟩

/-- Chart change followed by the projection and the reverse open rebase is the projection. -/
private theorem chartChangeFormal_projection_roundtrip :
    chartChangeFormalFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' ⋙
        Deformation.FormalObject.projection ⋙
        completeOpenRebaseFunctor iΛ' iΛ hiΛ
          (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀').symm =
      Deformation.FormalObject.projection := by
  refine CategoryTheory.Functor.ext (fun ξ => completeOpenRebase_roundtrip iΛ iΛ' hiΛ hiΛ'
    (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') ξ.base) ?_
  intro ξ η f
  let hξ := completeOpenRebase_roundtrip iΛ iΛ' hiΛ hiΛ'
    (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') ξ.base
  let hη := completeOpenRebase_roundtrip iΛ iΛ' hiΛ hiΛ'
    (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') η.base
  apply Deformation.CompleteLocalAlgCat.Hom.ext
  apply AlgHom.ext
  intro a
  change f.base.hom a = (eqToHom hη.symm).hom (f.base.hom ((eqToHom hξ).hom a))
  simp only [eqToHom_complete_hom_apply]
  rfl

end FormalChart

/-- Open rebasing agrees with canonical rebasing on the image of an Artinian local algebra. -/
private theorem completeOpenRebase_artinian_obj
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    completeOpenRebase iΛ iΛ' hiΛ' hclosed (Deformation.artinianToComplete.obj B) =
      Deformation.artinianToComplete.obj
        (rebaseArtinianAlgebraCanonical iΛ iΛ' hiΛ' hclosed B) := by
  let := hiΛ'
  have hg : (completeLocalOpenLift_data iΛ iΛ' hiΛ' hclosed
      (Deformation.artinianToComplete.obj B)).choose =
      canonicalArtinianOpenLift iΛ iΛ' hiΛ' hclosed B := by
    exact ringHom_eq_of_spec_comp_eq iΛ'
      ((completeOpenRebase_fac iΛ iΛ' hiΛ' hclosed
        (Deformation.artinianToComplete.obj B)).trans
        (canonicalArtinianOpenLift_fac iΛ iΛ' hiΛ' hclosed B).symm)
  dsimp only [completeOpenRebase]
  rw [rebaseCompleteLocalAlgebra_congr _ _ _ _
    (canonicalArtinianOpenLift_residue iΛ iΛ' hiΛ' hclosed B) hg]
  rfl

/-- The inclusion of Artinian into complete local algebras commutes with rebasing. -/
private theorem completeOpenRebase_artinian
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') :
    Deformation.artinianToComplete ⋙ completeOpenRebaseFunctor iΛ iΛ' hiΛ' hclosed =
      rebaseArtinianFunctorCanonical iΛ iΛ' hiΛ' hclosed ⋙
        Deformation.artinianToComplete := by
  refine CategoryTheory.Functor.ext (completeOpenRebase_artinian_obj iΛ iΛ' hiΛ' hclosed) ?_
  intro A B f
  let hA := completeOpenRebase_artinian_obj iΛ iΛ' hiΛ' hclosed A
  let hB := completeOpenRebase_artinian_obj iΛ iΛ' hiΛ' hclosed B
  apply Deformation.CompleteLocalAlgCat.Hom.ext
  apply AlgHom.ext
  intro a
  change f.hom a = (eqToHom hB.symm).hom (f.hom ((eqToHom hA).hom a))
  simp only [eqToHom_complete_hom_apply]
  rfl

/-- A hom-lift for `p` along `F.map g` is a hom-lift for `F ⋙ p` along `g`. -/
private theorem isHomLift_precomp
    {C C' B : Type*} [Category C] [Category C'] [Category B]
    (F : C ⥤ C') (p : C' ⥤ B)
    {R S : B} {x y : C} {f : R ⟶ S} {g : x ⟶ y}
    (h : p.IsHomLift f (F.map g)) : (F ⋙ p).IsHomLift f g := by
  have := h
  exact IsHomLift.of_fac (F ⋙ p) f g
    (IsHomLift.domain_eq p f (F.map g)) (IsHomLift.codomain_eq p f (F.map g))
    (IsHomLift.fac p f (F.map g))

/-- Versality is preserved by a full, objectwise-surjective rebasing of formal objects which is
compatible with the projections to complete local algebras. -/
private theorem isVersal_of_formalRebase
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    {C : Type*} {C' : Type*} [Category C] [Category C']
    {p : C ⥤ Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    {p' : C' ⥤ Deformation.ArtinianLocalAlgCat.{u, u, u} Λ' k}
    (hp : Deformation.IsCofiberedInGroupoids p)
    (hp' : Deformation.IsCofiberedInGroupoids p')
    (F : Deformation.FormalObject p ⥤ Deformation.FormalObject p') [F.Full]
    (G : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ' k ⥤
      Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (J : Deformation.CompleteLocalAlgCat.{u, u, u} Λ' k ⥤
      Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (hproj : F ⋙ Deformation.FormalObject.projection ⋙ J =
      Deformation.FormalObject.projection)
    (hinc : Deformation.artinianToComplete ⋙ J = G ⋙ Deformation.artinianToComplete)
    (hG : ∀ {A B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ' k}
      (f : A ⟶ B), Function.Surjective f.hom →
      Function.Surjective (G.map f).hom)
    (hF : Function.Surjective F.obj)
    (ξ : Deformation.FormalObject p) (hξ : Deformation.IsVersal hp ξ) :
    Deformation.IsVersal hp' (F.obj ξ) := by
  rw [Deformation.isVersal_iff_lifts_artinian] at hξ ⊢
  intro B A f hf y x g hg a
  obtain ⟨y, rfl⟩ := hF y
  obtain ⟨x, rfl⟩ := hF x
  let g₀ := F.preimage g
  let a₀ := F.preimage a
  have hg₀ : (Deformation.FormalObject.projection (p := p)).IsHomLift
      (Deformation.artinianToComplete.map (G.map f)) g₀ := by
    have h : (Deformation.FormalObject.projection (p := p')).IsHomLift
        (Deformation.artinianToComplete.map f) (F.map g₀) := by
      simpa only [g₀, Functor.map_preimage] using hg
    have hh := Functor.isHomLift_comp_functor (p := Deformation.FormalObject.projection) J _ _ h
    have hh' := isHomLift_precomp F (Deformation.FormalObject.projection ⋙ J) hh
    change (F ⋙ Deformation.FormalObject.projection ⋙ J).IsHomLift
      ((Deformation.artinianToComplete ⋙ J).map f) g₀ at hh'
    rw [hproj, hinc] at hh'
    exact hh'
  obtain ⟨b, hb⟩ := hξ (G.map f) (hG f hf) g₀ hg₀ a₀
  refine ⟨F.map b, ?_⟩
  calc
    F.map b ≫ g = F.map b ≫ F.map g₀ := by rw [Functor.map_preimage]
    _ = F.map (b ≫ g₀) := (F.map_comp _ _).symm
    _ = F.map a₀ := congrArg F.map hb
    _ = a := F.map_preimage a

/-- Versality is preserved by the chart-change functor on formal objects. -/
theorem isVersal_chartChange
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ : IsOpenImmersion iΛ) (hiΛ' : IsOpenImmersion iΛ')
    {X : Type w} [Category.{v} X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (hp : Deformation.IsCofiberedInGroupoids
      (Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).projection)
    (hp' : Deformation.IsCofiberedInGroupoids
      (Deformation.Artin.predeformationCategory iΛ' q x₀ hx₀').projection)
    (ξ : Deformation.FormalObject
      (Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).projection)
    (hξ : Deformation.IsVersal hp ξ) :
    Deformation.IsVersal hp'
      ((chartChangeFormalFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀').obj ξ) := by
  let := chartChangeFormal_full iΛ iΛ' hiΛ hiΛ' q x₀ hx₀ hx₀'
  let hc := closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀'
  exact isVersal_of_formalRebase hp hp'
    (chartChangeFormalFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀')
    (rebaseArtinianFunctorCanonical iΛ' iΛ hiΛ hc.symm)
    (completeOpenRebaseFunctor iΛ' iΛ hiΛ hc.symm)
    (chartChangeFormal_projection_roundtrip iΛ iΛ' hiΛ hiΛ' q x₀ hx₀ hx₀')
    (completeOpenRebase_artinian iΛ' iΛ hiΛ hc.symm)
    (fun _ hf => hf)
    (chartChangeFormal_surjective iΛ iΛ' hiΛ hiΛ' q x₀ hx₀ hx₀') ξ hξ

/-- A versal formal object can be moved along an isomorphism of its base. -/
private theorem exists_versalFormalObject_of_baseIso
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {C : Type*} [Category C]
    {p : C ⥤ Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p)
    (ξ : Deformation.FormalObject p) (hξ : Deformation.IsVersal hp ξ)
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k) (e : ξ.base ≅ A) :
    ∃ η : Deformation.FormalObject p, η.base = A ∧ Deformation.IsVersal hp η := by
  let P := Deformation.FormalObject.projection (p := p)
  have hP := Deformation.formalObjectProjection_isCofiberedInGroupoids p hp
  obtain ⟨η, f, hf⟩ := hP.exists_lift e.hom.op (Opposite.op ξ) rfl
  have hf' : P.IsHomLift e.hom f.unop := by
    have := hf
    exact CategoryTheory.isHomLift_unop P e.hom.op f
  have hcart := Deformation.isStronglyCocartesian_of_isCofiberedInGroupoids hP e.hom f.unop hf'
  have hiso := Functor.IsStronglyCocartesian.isIso_of_base_isIso P e.hom f.unop
  exact ⟨η.unop, IsHomLift.codomain_eq P e.hom f.unop,
    Deformation.isVersal_of_iso hp (asIso f.unop) hξ⟩

/-- One implication of `isVersalRingAt_iff_of_affineOpenPresentation`: versality of `A` over the
first presentation gives versality of `A'` over the second. -/
private theorem isVersalRingAt_of_affineOpenPresentation
    (D : AlgebraicGeometry.Stack.VersalSituation.{u, w})
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : IsOpenImmersion iΛ)
    (iΛ' : Spec (.of Λ') ⟶ D.S) (hiΛ' : IsOpenImmersion iΛ')
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite' : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (A' : Deformation.CompleteLocalAlgCat.{u, u, u} Λ' k)
    (e : A ≃+* A')
    (heS : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' A')) ≫ iΛ')
    (hek : ∀ a : A,
      A'.residueEquiv (residue A' (e a)) = A.residueEquiv (residue A a))
    (hA : IsVersalRingAt D iΛ hiΛ x₀ hx₀ hfinite A) :
    IsVersalRingAt D iΛ' hiΛ' x₀ hx₀' hfinite' A' := by
  obtain ⟨ξ, rfl, hξ⟩ := hA
  let q := D.𝒳.val.val.p ⋙ Over.post D.B.inclusion
  let hp := (Deformation.Artin.predeformationCategory_isPredeformationCategory
    D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered
  let hp' := (Deformation.Artin.predeformationCategory_isPredeformationCategory
    D.B D.hS iΛ' D.𝒳.val.val.p x₀ hx₀' D.𝒳.val.property).cofibered
  let η := (chartChangeFormalFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀').obj ξ
  have hη : Deformation.IsVersal hp' η :=
    isVersal_chartChange iΛ iΛ' hiΛ hiΛ' q x₀ hx₀ hx₀' hp hp' ξ hξ
  have eη : η.base ≅ A' := by
    apply completeLocalAlgIsoOfRingEquiv η.base A' e
    · have h := ringHom_comp_eq_of_spec_over iΛ'
        (algebraMap Λ' η.base) (algebraMap Λ' A') e.toRingHom ?_
      · exact fun a => DFunLike.congr_fun h a
      · change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ'
            (completeOpenRebase iΛ iΛ' hiΛ'
              (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') ξ.base))) ≫ iΛ' = _
        rwa [completeOpenRebase_fac]
    · exact hek
  exact exists_versalFormalObject_of_baseIso hp' η hη A' eη

/-- The notion of a versal ring is independent of which affine open
neighborhood presents its structure morphism to `S`. -/
@[stacks 0DQV "independence of affine-open presentation"]
public theorem isVersalRingAt_iff_of_affineOpenPresentation
    (D : AlgebraicGeometry.Stack.VersalSituation.{u, w})
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : IsOpenImmersion iΛ)
    (iΛ' : Spec (.of Λ') ⟶ D.S) (hiΛ' : IsOpenImmersion iΛ')
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite' : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (A' : Deformation.CompleteLocalAlgCat.{u, u, u} Λ' k)
    (e : A ≃+* A')
    (heS : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' A')) ≫ iΛ')
    (hek : ∀ a : A,
      A'.residueEquiv (residue A' (e a)) = A.residueEquiv (residue A a)) :
    IsVersalRingAt D iΛ hiΛ x₀ hx₀ hfinite A ↔
      IsVersalRingAt D iΛ' hiΛ' x₀ hx₀' hfinite' A' := by
  constructor
  · exact isVersalRingAt_of_affineOpenPresentation D iΛ hiΛ iΛ' hiΛ'
      x₀ hx₀ hx₀' hfinite hfinite' A A' e heS hek
  · apply isVersalRingAt_of_affineOpenPresentation D iΛ' hiΛ' iΛ hiΛ
      x₀ hx₀' hx₀ hfinite' hfinite A' A e.symm
    · calc
        Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
            Spec.map (CommRingCat.ofHom (algebraMap Λ' A')) ≫ iΛ' =
          Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
            Spec.map (CommRingCat.ofHom e.toRingHom) ≫
              Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ := by rw [heS]
        _ = Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ := by
          rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          simp
    · intro a
      simpa using (hek (e.symm a)).symm

end AlgebraicGeometry.Stack

end
