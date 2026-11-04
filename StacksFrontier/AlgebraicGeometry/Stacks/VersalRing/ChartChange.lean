module

public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRing.RebaseDeformation

/-!
# Versal rings: the chart-change functor

The comparison functor between the predeformation categories attached to two affine-open
presentations of one field-valued point of `S`, and the rebasing of complete local algebras
along the second chart; part of the proof of Stacks 0DQV.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Stack

universe u v w

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

/-- The comparison functor between the predeformation categories attached to two affine-open
presentations of the same field-valued point of `S`. -/
noncomputable def chartChangePredeformationFunctor
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    {X : Type w} [Category.{v} X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')) :
    (Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).carrier ⥤
      (Deformation.Artin.predeformationCategory iΛ' q x₀ hx₀').carrier := by
  classical
  let C := Deformation.Artin.predeformationCategory iΛ q x₀ hx₀
  let C' := Deformation.Artin.predeformationCategory iΛ' q x₀ hx₀'
  let data (a : C.carrier) : Deformation.Artin.DeformationObject iΛ' q x₀ hx₀' :=
    rebaseDeformationObject iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' (C.objects a)
  let obj (a : C.carrier) : C'.carrier := C'.objects.symm (data a)
  let objectEq (a : C.carrier) : C'.objects (obj a) = data a :=
    C'.objects.apply_symm_apply (data a)
  let morphismData {a b : C.carrier} (f : a ⟶ b) :
    Deformation.Artin.DeformationMorphism iΛ' q x₀ hx₀'
        (C'.objects (obj a)) (C'.objects (obj b)) := by
    let m := C.morphisms a b f
    simpa [data] using transportDeformationMorphism (objectEq a) (objectEq b)
      (rebaseDeformationMorphism iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' m)
  let mapHom {a b : C.carrier} (f : a ⟶ b) : obj a ⟶ obj b :=
    (C'.morphisms (obj a) (obj b)).symm (morphismData f)
  have sourceRingId (a : C.carrier) :
      (C.morphisms a a (𝟙 a)).ringHom = 𝟙 (C.objects a).algebra := by
    have h := C.morphism_projection (f := 𝟙 a)
    simpa using h.symm
  have targetRingId (a : C.carrier) :
      (C'.morphisms (obj a) (obj a) (𝟙 (obj a))).ringHom =
        𝟙 (C'.objects (obj a)).algebra := by
    have h := C'.morphism_projection (f := 𝟙 (obj a))
    simpa using h.symm
  have sourceRingComp {a b c : C.carrier} (f : a ⟶ b) (g : b ⟶ c) :
      (C.morphisms a c (f ≫ g)).ringHom =
        (C.morphisms a b f).ringHom ≫ (C.morphisms b c g).ringHom := by
    have h := C.morphism_projection (f := f ≫ g)
    have hf := C.morphism_projection (f := f)
    have hg := C.morphism_projection (f := g)
    simp only [Functor.map_comp] at h
    calc
      _ = _ := h.symm
      _ = _ := by rw [← hf, ← hg]; simp [Category.assoc]
  have targetRingComp {a b c : C.carrier} (f : obj a ⟶ obj b)
      (g : obj b ⟶ obj c) :
      (C'.morphisms (obj a) (obj c) (f ≫ g)).ringHom =
        (C'.morphisms (obj a) (obj b) f).ringHom ≫
          (C'.morphisms (obj b) (obj c) g).ringHom := by
    have h := C'.morphism_projection (f := f ≫ g)
    have hf := C'.morphism_projection (f := f)
    have hg := C'.morphism_projection (f := g)
    simp only [Functor.map_comp] at h
    calc
      _ = _ := h.symm
      _ = _ := by rw [← hf, ← hg]; simp [Category.assoc]
  exact {
    obj := obj
    map := mapHom
    map_id := by
      intro a
      have hdata : morphismData (𝟙 a) =
          C'.morphisms (obj a) (obj a) (𝟙 (obj a)) := by
        apply deformationMorphism_ext_of_ringMap
        · intro z
          let hA := congrArg
            (fun d : Deformation.Artin.DeformationObject iΛ' q x₀ hx₀' => d.algebra)
            (objectEq a)
          have hcast : eqToHom hA ≫ eqToHom hA.symm =
              𝟙 (C'.objects (obj a)).algebra := by simp
          have hval := congrArg
            (fun f : Deformation.ArtinianLocalAlgCat.Hom _ _ => f.hom z) hcast
          simp only [morphismData, transportDeformationMorphism_ringHom,
            rebaseDeformationMorphism, sourceRingId, targetRingId,
            data]
          exact hval
        · let hp := congrArg
            (fun d : Deformation.Artin.DeformationObject iΛ' q x₀ hx₀' => d.point)
            (objectEq a)
          simp only [morphismData, transportDeformationMorphism_arrow,
            rebaseDeformationMorphism_arrow_eq, C.reversed_identity]
          rw [C'.reversed_identity]
          change eqToHom hp ≫ 𝟙 (data a).point ≫ eqToHom hp.symm =
            𝟙 (C'.objects (obj a)).point
          calc
            eqToHom hp ≫ 𝟙 (data a).point ≫ eqToHom hp.symm =
                eqToHom hp ≫ eqToHom hp.symm := by simp
            _ = 𝟙 (C'.objects (obj a)).point := eqToHom_comp_symm hp
      apply (C'.morphisms (obj a) (obj a)).injective
      simpa only [mapHom, Equiv.apply_symm_apply] using hdata
    map_comp := by
      intro a b c f g
      have hmf : C'.morphisms (obj a) (obj b) (mapHom f) =
          morphismData f := Equiv.apply_symm_apply _ _
      have hmg : C'.morphisms (obj b) (obj c) (mapHom g) =
          morphismData g := Equiv.apply_symm_apply _ _
      have hdata : morphismData (f ≫ g) =
          C'.morphisms (obj a) (obj c) (mapHom f ≫ mapHom g) := by
        apply deformationMorphism_ext_of_ringMap
        · intro z
          rw [targetRingComp, hmf, hmg]
          let hA := congrArg
            (fun d : Deformation.Artin.DeformationObject iΛ' q x₀ hx₀' => d.algebra)
            (objectEq a)
          let hB := congrArg
            (fun d : Deformation.Artin.DeformationObject iΛ' q x₀ hx₀' => d.algebra)
            (objectEq b)
          let hC := congrArg
            (fun d : Deformation.Artin.DeformationObject iΛ' q x₀ hx₀' => d.algebra)
            (objectEq c)
          let mf := rebaseDeformationMorphism iΛ iΛ' hiΛ' q x₀ hx₀ hx₀'
            (C.morphisms a b f)
          let mg := rebaseDeformationMorphism iΛ iΛ' hiΛ' q x₀ hx₀ hx₀'
            (C.morphisms b c g)
          let mfg := rebaseDeformationMorphism iΛ iΛ' hiΛ' q x₀ hx₀ hx₀'
            (C.morphisms a c (f ≫ g))
          have hsource : mfg.ringHom = mf.ringHom ≫ mg.ringHom := by
            apply Deformation.ArtinianLocalAlgCat.hom_ext
            apply AlgHom.ext
            intro x
            have hs := congrArg
              (fun m : Deformation.ArtinianLocalAlgCat.Hom
                  (C.objects a).algebra (C.objects c).algebra => m.hom x)
              (sourceRingComp f g)
            change (C.morphisms a c (f ≫ g)).ringHom.hom x =
              (C.morphisms b c g).ringHom.hom
                ((C.morphisms a b f).ringHom.hom x)
            exact hs
          have hmapEq : (morphismData (f ≫ g)).ringHom =
              (morphismData f).ringHom ≫ (morphismData g).ringHom := by
            simp only [morphismData, transportDeformationMorphism_ringHom]
            rw [hsource]
            exact (eqToHom_conjugate_comp hA hB hC mf.ringHom mg.ringHom).symm
          change ((morphismData (f ≫ g)).ringHom).hom z =
            ((morphismData f).ringHom ≫ (morphismData g).ringHom).hom z
          exact congrArg (fun m : Deformation.ArtinianLocalAlgCat.Hom _ _ => m.hom z)
            hmapEq
        · let hpB := congrArg
            (fun d : Deformation.Artin.DeformationObject iΛ' q x₀ hx₀' => d.point)
            (objectEq b)
          let hpA := congrArg
            (fun d : Deformation.Artin.DeformationObject iΛ' q x₀ hx₀' => d.point)
            (objectEq a)
          let hpC := congrArg
            (fun d : Deformation.Artin.DeformationObject iΛ' q x₀ hx₀' => d.point)
            (objectEq c)
          rw [C'.reversed_composition, hmg, hmf]
          simp only [morphismData, transportDeformationMorphism_arrow,
            rebaseDeformationMorphism_arrow_eq, C.reversed_composition]
          exact (eqToHom_conjugate_comp hpC hpB hpA
            ((C.morphisms b c g).arrow) ((C.morphisms a b f).arrow)).symm
      apply (C'.morphisms (obj a) (obj c)).injective
      simpa only [mapHom, Equiv.apply_symm_apply] using hdata }

/-- `chartChangePredeformationFunctor` sends an object to the rebase of its deformation object. -/
theorem chartChange_objects
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    {X : Type w} [Category.{v} X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (a : (Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).carrier) :
    (Deformation.Artin.predeformationCategory iΛ' q x₀ hx₀').objects
        ((chartChangePredeformationFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀').obj a) =
      rebaseDeformationObject iΛ iΛ' hiΛ' q x₀ hx₀ hx₀'
        ((Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).objects a) := by
  let C := Deformation.Artin.predeformationCategory iΛ q x₀ hx₀
  let C' := Deformation.Artin.predeformationCategory iΛ' q x₀ hx₀'
  change C'.objects (C'.objects.symm
    (rebaseDeformationObject iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' (C.objects a))) = _
  exact C'.objects.apply_symm_apply _

/-- The projection of a chart-changed object is the canonical rebase of its algebra. -/
theorem chartChange_projection_obj
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    {X : Type w} [Category.{v} X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (a : (Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).carrier) :
    (Deformation.Artin.predeformationCategory iΛ' q x₀ hx₀').projection.obj
        ((chartChangePredeformationFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀').obj a) =
      rebaseArtinianAlgebraCanonical iΛ iΛ' hiΛ'
        (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀')
        ((Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).objects a).algebra := by
  let C := Deformation.Artin.predeformationCategory iΛ q x₀ hx₀
  let C' := Deformation.Artin.predeformationCategory iΛ' q x₀ hx₀'
  let F := chartChangePredeformationFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀'
  calc
    C'.projection.obj (F.obj a) = (C'.objects (F.obj a)).algebra :=
      C'.object_projection _
    _ = (rebaseDeformationObject iΛ iΛ' hiΛ' q x₀ hx₀ hx₀'
          (C.objects a)).algebra := congrArg Deformation.Artin.DeformationObject.algebra
        (chartChange_objects iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' a)
    _ = rebaseArtinianAlgebraCanonical iΛ iΛ' hiΛ'
          (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀')
          ((C.objects a).algebra) :=
        rebaseDeformationObject_algebra_eq_canonical iΛ iΛ' hiΛ' q x₀ hx₀ hx₀'
          (C.objects a)

/-- Conjugating by `eqToHom`s is transitive. -/
private theorem eqToHom_conj_trans {C : Type*} [Category C] {A A' A'' B B' B'' : C}
    (hA : A = A') (hA' : A' = A'') (hB : B = B') (hB' : B' = B'')
    {f : A ⟶ B} {g : A' ⟶ B'} {u : A'' ⟶ B''}
    (h₁ : eqToHom hA.symm ≫ f ≫ eqToHom hB = g)
    (h₂ : eqToHom hA'.symm ≫ g ≫ eqToHom hB' = u) :
    eqToHom (hA.trans hA').symm ≫ f ≫ eqToHom (hB.trans hB') = u := by
  subst hA hA' hB hB'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h₁ h₂ ⊢
  exact h₁.trans h₂

/-- The projection of a chart-changed morphism, computed through the rebased deformation
morphism. -/
private theorem chartChange_projection_map_rebased
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    {X : Type w} [Category.{v} X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    {a b : (Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).carrier}
    (f : a ⟶ b) :
    let C := Deformation.Artin.predeformationCategory iΛ q x₀ hx₀
    let C' := Deformation.Artin.predeformationCategory iΛ' q x₀ hx₀'
    let F := chartChangePredeformationFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀'
    eqToHom ((C'.object_projection (F.obj a)).trans
        (congrArg Deformation.Artin.DeformationObject.algebra
          (chartChange_objects iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' a))).symm ≫
      C'.projection.map (F.map f) ≫
      eqToHom ((C'.object_projection (F.obj b)).trans
        (congrArg Deformation.Artin.DeformationObject.algebra
          (chartChange_objects iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' b))) =
      (rebaseDeformationMorphism iΛ iΛ' hiΛ' q x₀ hx₀ hx₀'
        (C.morphisms a b f)).ringHom := by
  intro C C' F
  have hdata : C'.morphisms (F.obj a) (F.obj b) (F.map f) =
      transportDeformationMorphism (chartChange_objects iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' a)
        (chartChange_objects iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' b)
        (rebaseDeformationMorphism iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' (C.morphisms a b f)) := by
    dsimp [F, chartChangePredeformationFunctor]
    exact Equiv.apply_symm_apply _ _
  have h (c : C.carrier) := congrArg Deformation.Artin.DeformationObject.algebra
    (chartChange_objects iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' c)
  refine eqToHom_conj_trans (C'.object_projection (F.obj a)) (h a)
    (C'.object_projection (F.obj b)) (h b) (C'.morphism_projection (F.map f)) ?_
  rw [hdata, transportDeformationMorphism_ringHom]
  simp [Category.assoc, C]

/-- The ring map of a rebased deformation morphism is the canonical rebase of the original one. -/
private theorem rebaseDeformationMorphism_projection_map
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    {X : Type w} [Category X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    {a b : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    (m : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b) :
    eqToHom (rebaseDeformationObject_algebra_eq_canonical
        iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' a).symm ≫
      (rebaseDeformationMorphism iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' m).ringHom ≫
      eqToHom (rebaseDeformationObject_algebra_eq_canonical
        iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' b) =
      rebaseArtinianHomCanonical iΛ iΛ' hiΛ'
        (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') m.ringHom := by
  let hA := rebaseDeformationObject_algebra_eq_canonical
    iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' a
  let hB := rebaseDeformationObject_algebra_eq_canonical
    iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' b
  change eqToHom hA.symm ≫
      (rebaseDeformationMorphism iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' m).ringHom ≫
        eqToHom hB = _
  cases hA
  cases hB
  apply Deformation.ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro z
  rfl

/-- The projection of a chart-changed morphism is the canonical rebase of its projection. -/
theorem chartChange_projection_map
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    {X : Type w} [Category.{v} X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    {a b : (Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).carrier}
    (f : a ⟶ b) :
    let C := Deformation.Artin.predeformationCategory iΛ q x₀ hx₀
    let C' := Deformation.Artin.predeformationCategory iΛ' q x₀ hx₀'
    let F := chartChangePredeformationFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀'
    eqToHom (chartChange_projection_obj iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' a).symm ≫
      C'.projection.map (F.map f) ≫
      eqToHom (chartChange_projection_obj iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' b) =
      rebaseArtinianHomCanonical iΛ iΛ' hiΛ'
        (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') (C.morphisms a b f).ringHom := by
  intro C C' F
  have h (c : C.carrier) := (C'.object_projection (F.obj c)).trans
    (congrArg Deformation.Artin.DeformationObject.algebra
      (chartChange_objects iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' c))
  exact eqToHom_conj_trans (h a) (rebaseDeformationObject_algebra_eq_canonical
      iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' (C.objects a)) (h b)
    (rebaseDeformationObject_algebra_eq_canonical iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' (C.objects b))
    (chartChange_projection_map_rebased iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' f)
    (rebaseDeformationMorphism_projection_map iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' (C.morphisms a b f))

/-- `eqToHom` of an equality of Artinian local algebras acts on elements by `cast`. -/
theorem eqToHom_artinian_hom_apply
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k} (h : A = B) (x : A) :
    (eqToHom h).hom x = cast (congrArg Deformation.ArtinianLocalAlgCat.carrier h) x := by
  cases h
  rfl

/-- Canonical rebasing is compatible with the transition maps of the adic truncations. -/
theorem rebaseArtinianCanonical_transition
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (g : Λ' →+* A)
    (hg : ∀ a : Λ', A.residueEquiv (residue A (g a)) = algebraMap Λ' k a)
    (hS : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom g) ≫ iΛ') (n : ℕ) :
    eqToHom (rebaseArtinianCanonical_truncation
        iΛ iΛ' hiΛ' hclosed A g hg hS (n + 1)).symm ≫
      (rebaseArtinianFunctorCanonical iΛ iΛ' hiΛ' hclosed).map
        ((Deformation.AdicTruncation.transitionNat n).app A) ≫
      eqToHom (rebaseArtinianCanonical_truncation
        iΛ iΛ' hiΛ' hclosed A g hg hS n) =
      (Deformation.AdicTruncation.transitionNat n).app
        (rebaseCompleteLocalAlgebra A g hg) := by
  have hsucc := rebaseArtinianCanonical_truncation
    iΛ iΛ' hiΛ' hclosed A g hg hS (n + 1)
  have hprev := rebaseArtinianCanonical_truncation
    iΛ iΛ' hiΛ' hclosed A g hg hS n
  dsimp only [rebaseArtinianFunctorCanonical, Deformation.AdicTruncation.functor]
  apply Deformation.ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  change (eqToHom hprev).hom
      ((rebaseArtinianHomCanonical iΛ iΛ' hiΛ' hclosed
          ((Deformation.AdicTruncation.transitionNat n).app A)).hom
        ((eqToHom hsucc.symm).hom x)) =
    ((Deformation.AdicTruncation.transitionNat n).app
      (rebaseCompleteLocalAlgebra A g hg)).hom x
  simp only [eqToHom_artinian_hom_apply]
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := Deformation.AdicTruncation.ideal (rebaseCompleteLocalAlgebra A g hg) (n + 1)) x
  simp [rebaseArtinianHomCanonical, Deformation.AdicTruncation.transitionNat,
    Deformation.AdicTruncation.transition, Deformation.AdicTruncation.functor,
    Deformation.AdicTruncation.map]
  rfl

/-- The chart-change functor as a based functor over the canonical rebasing of Artinian local
algebras. -/
noncomputable def chartChangeBasedFunctor
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    {X : Type w} [Category.{v} X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')) :
    BasedFunctor
      (BasedCategory.ofFunctor
        ((Deformation.Artin.predeformationCategory iΛ q x₀ hx₀).projection ⋙
          rebaseArtinianFunctorCanonical iΛ iΛ' hiΛ'
            (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀')))
      (BasedCategory.ofFunctor
        (Deformation.Artin.predeformationCategory iΛ' q x₀ hx₀').projection) := by
  let C := Deformation.Artin.predeformationCategory iΛ q x₀ hx₀
  let C' := Deformation.Artin.predeformationCategory iΛ' q x₀ hx₀'
  let F := chartChangePredeformationFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀'
  let G := rebaseArtinianFunctorCanonical iΛ iΛ' hiΛ'
    (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀')
  refine ⟨F, ?_⟩
  change F ⋙ C'.projection = C.projection ⋙ G
  refine CategoryTheory.Functor.ext (h_obj := ?_) (h_map := ?_)
  · intro a
    change C'.projection.obj (F.obj a) =
      rebaseArtinianAlgebraCanonical iΛ iΛ' hiΛ'
        (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') (C.projection.obj a)
    rw [C.object_projection a]
    exact chartChange_projection_obj iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' a
  · intro a b f
    dsimp [C, C', F, G]
    let C := Deformation.Artin.predeformationCategory iΛ q x₀ hx₀
    let C' := Deformation.Artin.predeformationCategory iΛ' q x₀ hx₀'
    let F := chartChangePredeformationFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀'
    let G := rebaseArtinianFunctorCanonical iΛ iΛ' hiΛ'
      (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀')
    have haObj : C'.projection.obj (F.obj a) = G.obj (C.projection.obj a) := by
      change C'.projection.obj (F.obj a) =
        rebaseArtinianAlgebraCanonical iΛ iΛ' hiΛ'
          (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') (C.projection.obj a)
      rw [C.object_projection a]
      exact chartChange_projection_obj iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' a
    have hbObj : C'.projection.obj (F.obj b) = G.obj (C.projection.obj b) := by
      change C'.projection.obj (F.obj b) =
        rebaseArtinianAlgebraCanonical iΛ iΛ' hiΛ'
          (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') (C.projection.obj b)
      rw [C.object_projection b]
      exact chartChange_projection_obj iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' b
    have hmap := chartChange_projection_map iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' f
    have hA : G.obj (C.projection.obj a) =
        rebaseArtinianAlgebraCanonical iΛ iΛ' hiΛ'
          (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') (C.objects a).algebra := by
      rw [C.object_projection a]
      rfl
    have hB : G.obj (C.projection.obj b) =
        rebaseArtinianAlgebraCanonical iΛ iΛ' hiΛ'
          (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') (C.objects b).algebra := by
      rw [C.object_projection b]
      rfl
    have hbase : rebaseArtinianHomCanonical iΛ iΛ' hiΛ'
        (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') (C.morphisms a b f).ringHom =
          eqToHom hA.symm ≫ G.map (C.projection.map f) ≫ eqToHom hB := by
      have h := congrArg G.map (C.morphism_projection (f := f))
      simp only [Functor.map_comp] at h
      simpa [G, rebaseArtinianFunctorCanonical, eqToHom_map,
        eqToHom_trans, Category.assoc] using h.symm
    have hmapCanonical :
        eqToHom (chartChange_projection_obj iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' a).symm ≫
          C'.projection.map (F.map f) ≫
          eqToHom (chartChange_projection_obj iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' b) =
        rebaseArtinianHomCanonical iΛ iΛ' hiΛ'
          (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') (C.morphisms a b f).ringHom := by
      simpa [C, C', F] using hmap
    have hObjA : haObj =
        (chartChange_projection_obj iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' a).trans hA.symm :=
      Subsingleton.elim _ _
    have hObjB : hbObj =
        (chartChange_projection_obj iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' b).trans hB.symm :=
      Subsingleton.elim _ _
    have hmap' : eqToHom haObj.symm ≫ C'.projection.map (F.map f) ≫ eqToHom hbObj =
        G.map (C.projection.map f) := by
      calc
        _ = eqToHom hA ≫
            (eqToHom (chartChange_projection_obj iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' a).symm ≫
              C'.projection.map (F.map f) ≫
              eqToHom (chartChange_projection_obj iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' b)) ≫
            eqToHom hB.symm := by
              rw [hObjA, hObjB]
              simp [eqToHom_trans, Category.assoc]
        _ = eqToHom hA ≫
            rebaseArtinianHomCanonical iΛ iΛ' hiΛ'
              (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') (C.morphisms a b f).ringHom ≫
            eqToHom hB.symm := by rw [hmapCanonical]
        _ = G.map (C.projection.map f) := by
          rw [hbase]
          simp [eqToHom_trans, Category.assoc]
    change C'.projection.map (F.map f) =
      eqToHom haObj ≫ G.map (C.projection.map f) ≫ eqToHom hbObj.symm
    calc
      _ = eqToHom haObj ≫
          (eqToHom haObj.symm ≫ C'.projection.map (F.map f) ≫ eqToHom hbObj) ≫
          eqToHom hbObj.symm := by simp [Category.assoc]
      _ = _ := by
        rw [hmap']

/-- Two ring maps into `V` that agree after composing with a monomorphism `Spec R ⟶ S` are
equal. -/
theorem ringHom_comp_eq_of_spec_over
    {R T V : Type u} [CommRing R] [CommRing T] [CommRing V]
    {S : Scheme.{u}} (i : Spec (.of R) ⟶ S) [Mono i]
    (r : R →+* T) (t : R →+* V) (f : T →+* V)
    (h : Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom r) ≫ i =
      Spec.map (CommRingCat.ofHom t) ≫ i) : f.comp r = t := by
  have h' : Spec.map (CommRingCat.ofHom (f.comp r)) =
      Spec.map (CommRingCat.ofHom t) := by
    apply (cancel_mono i).mp
    simpa only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] using h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h')

/-- A complete local `Λ`-algebra over `S` whose closed point lies in the affine open `Spec Λ'` is
canonically a `Λ'`-algebra over `S`. -/
theorem completeLocalOpenLift_data
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k) :
    ∃ g : Λ' →+* A,
      (∀ a, A.residueEquiv (residue A (g a)) = algebraMap Λ' k a) ∧
      Spec.map (CommRingCat.ofHom g) ≫ iΛ' =
        Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ := by
  let := hiΛ'
  let r : A →+* k := A.residueEquiv.toRingEquiv.toRingHom.comp (residue A)
  let f : Spec (.of A) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ
  have hr : r.comp (algebraMap Λ A) = algebraMap Λ k := by
    ext a
    exact A.residueEquiv.commutes a
  have hrS : Spec.map (CommRingCat.ofHom r) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ' := by
    dsimp only [f]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hr, hclosed]
  have hpoint : f (closedPoint A) ∈ iΛ'.opensRange := by
    refine ⟨(Spec.map (CommRingCat.ofHom (algebraMap Λ' k))) (closedPoint k), ?_⟩
    have h := congrArg (fun t : Spec (.of k) ⟶ S => t (closedPoint k)) hrS
    have hrpoint : Spec.map (CommRingCat.ofHom r) (closedPoint k) = closedPoint A :=
      IsLocalRing.comap_closedPoint r
    rw [← hrpoint]
    exact h.symm
  have hrange : Set.range f ⊆ Set.range iΛ' := by
    have h := Scheme.preimage_eq_top_of_closedPoint_mem f hpoint
    rintro _ ⟨a, rfl⟩
    change a ∈ f ⁻¹ᵁ iΛ'.opensRange
    rw [h]
    trivial
  let l := IsOpenImmersion.lift iΛ' f hrange
  have hl : l ≫ iΛ' = f := IsOpenImmersion.lift_fac iΛ' f hrange
  let g := (Spec.homEquiv l).hom
  have hg : Spec.map (CommRingCat.ofHom g) = l := Spec.homEquiv.symm_apply_apply l
  refine ⟨g, ?_, by rwa [hg]⟩
  have hrg : r.comp g = algebraMap Λ' k := by
    apply ringHom_comp_eq_of_spec_over iΛ' g (algebraMap Λ' k) r
    rwa [hg, hl]
  intro a
  exact DFunLike.congr_fun hrg a

attribute [local implicit_reducible] rebaseArtinianAlgebra rebaseCompleteLocalAlgebra
  rebaseArtinianAlgebraCanonical rebaseArtinianFunctorCanonical
  Deformation.AdicTruncation.obj

section CompleteChart

variable {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
  [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
  (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
  (hiΛ' : IsOpenImmersion iΛ')
  (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
    Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')

/-- A complete local `Λ`-algebra read as a complete local `Λ'`-algebra along the lift supplied by
`completeLocalOpenLift_data`. -/
noncomputable def completeOpenRebase
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k) :
    Deformation.CompleteLocalAlgCat.{u, u, u} Λ' k :=
  rebaseCompleteLocalAlgebra A
    (completeLocalOpenLift_data iΛ iΛ' hiΛ' hclosed A).choose
    (completeLocalOpenLift_data iΛ iΛ' hiΛ' hclosed A).choose_spec.1

/-- `completeOpenRebase` factors the structure morphism through `Spec Λ' ⟶ S`. -/
theorem completeOpenRebase_fac
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k) :
    Spec.map (CommRingCat.ofHom
      (algebraMap Λ' (completeOpenRebase iΛ iΛ' hiΛ' hclosed A))) ≫ iΛ' =
    Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ :=
  (completeLocalOpenLift_data iΛ iΛ' hiΛ' hclosed A).choose_spec.2

attribute [local implicit_reducible] completeOpenRebase

/-- The morphism of open-rebased complete local algebras induced by a morphism over `Λ`. -/
noncomputable def completeOpenRebaseHom
    {A B : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k} (f : A ⟶ B) :
    completeOpenRebase iΛ iΛ' hiΛ' hclosed A ⟶
      completeOpenRebase iΛ iΛ' hiΛ' hclosed B := by
  letI := hiΛ'
  refine ⟨AlgHom.mk f.hom.toRingHom ?_, f.isLocal, f.residue_comm⟩
  have h := ringHom_comp_eq_of_spec_over iΛ'
    (algebraMap Λ' (completeOpenRebase iΛ iΛ' hiΛ' hclosed A))
    (algebraMap Λ' (completeOpenRebase iΛ iΛ' hiΛ' hclosed B)) f.hom.toRingHom ?_
  · exact fun a => DFunLike.congr_fun h a
  · rw [completeOpenRebase_fac, completeOpenRebase_fac]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hf : f.hom.toRingHom.comp (algebraMap Λ A) = algebraMap Λ B := by
      ext a
      exact f.hom.commutes a
    rw [hf]

/-- Open rebasing as a functor between categories of complete local algebras. -/
noncomputable def completeOpenRebaseFunctor :
    Deformation.CompleteLocalAlgCat.{u, u, u} Λ k ⥤
      Deformation.CompleteLocalAlgCat.{u, u, u} Λ' k where
  obj := completeOpenRebase iΛ iΛ' hiΛ' hclosed
  map := completeOpenRebaseHom iΛ iΛ' hiΛ' hclosed
  map_id A := by
    apply Deformation.CompleteLocalAlgCat.Hom.ext
    apply AlgHom.ext
    intro a
    rfl
  map_comp f g := by
    apply Deformation.CompleteLocalAlgCat.Hom.ext
    apply AlgHom.ext
    intro a
    rfl

attribute [local implicit_reducible] completeOpenRebaseFunctor

/-- Open rebasing commutes with adic truncation on objects. -/
theorem completeOpenRebase_truncation
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k) (n : ℕ) :
    (rebaseArtinianFunctorCanonical iΛ iΛ' hiΛ' hclosed).obj
      (Deformation.AdicTruncation.obj A n) =
    Deformation.AdicTruncation.obj (completeOpenRebase iΛ iΛ' hiΛ' hclosed A) n :=
  rebaseArtinianCanonical_truncation iΛ iΛ' hiΛ' hclosed A
    (completeLocalOpenLift_data iΛ iΛ' hiΛ' hclosed A).choose
    (completeLocalOpenLift_data iΛ iΛ' hiΛ' hclosed A).choose_spec.1
    (completeLocalOpenLift_data iΛ iΛ' hiΛ' hclosed A).choose_spec.2.symm n

/-- Open rebasing commutes with adic truncation on morphisms. -/
theorem completeOpenRebase_truncation_map
    {A B : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k} (f : A ⟶ B) (n : ℕ) :
    eqToHom (completeOpenRebase_truncation iΛ iΛ' hiΛ' hclosed A n).symm ≫
      (rebaseArtinianFunctorCanonical iΛ iΛ' hiΛ' hclosed).map
        (Deformation.AdicTruncation.map f n) ≫
      eqToHom (completeOpenRebase_truncation iΛ iΛ' hiΛ' hclosed B n) =
    Deformation.AdicTruncation.map
      ((completeOpenRebaseFunctor iΛ iΛ' hiΛ' hclosed).map f) n := by
  let hA := completeOpenRebase_truncation iΛ iΛ' hiΛ' hclosed A n
  let hB := completeOpenRebase_truncation iΛ iΛ' hiΛ' hclosed B n
  apply Deformation.ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  change ∀ x : A ⧸ Deformation.AdicTruncation.ideal A n,
    (eqToHom hB).hom
      ((Deformation.AdicTruncation.map f n).hom ((eqToHom hA.symm).hom x)) = _
  intro x
  simp only [eqToHom_artinian_hom_apply, cast_eq]
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end CompleteChart

end AlgebraicGeometry.Stack

end
