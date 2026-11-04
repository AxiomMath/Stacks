module

public import StacksFrontier.Deformation.Artin.FormalObject.Versal

/-!
# The formal object over the site of a formal object of a predeformation category

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category over the big fppf site of a scheme `S`, let
`x₀ : Spec k ⟶ 𝒳` be a field-valued point presented over an affine chart `Spec Λ ⟶ S`, and let
`𝓕_{𝒳,k,x₀}` be its predeformation category over `𝒞_Λ` (**Stacks 07T4**). A formal object
`ξ = (A, ξ_n, f_n)` of `𝓕_{𝒳,k,x₀}` (**Stacks 06H3**) consists of a complete local `Λ`-algebra
`A` with residue field `k` and deformations `x₀ ⟶ ξ_n` over `A / 𝔪^{n+1}` with reversed
transitions. Forgetting the arrows out of `x₀` leaves the objects `ξ_n` of `𝒳` over the
infinitesimal thickenings of `Spec A ⟶ Spec Λ ⟶ S` and the arrows `ξ_n ⟶ ξ_{n+1}` between them,
which is a formal object of `𝒳` over the site in the sense of Artin's Axioms (**Stacks 07X4**).

Morphisms go the other way: a morphism `ξ ⟶ ξ'` of formal objects of `𝓕_{𝒳,k,x₀}` lies over a
map `A ⟶ A'` of complete local algebras and consists of reversed arrows `ξ'_n ⟶ ξ_n`, so it gives
a morphism of formal objects over the site from the image of `ξ'` to the image of `ξ`, whose map of
complete local bases is `Spec A' ⟶ Spec A`.

## Main definitions

* `Deformation.Artin.completeLocalAlgFormalBase`: a complete local `Λ`-algebra with residue field
  `k`, read as a complete local base over `S` through the chart `Spec Λ ⟶ S`.
* `Deformation.Artin.FormalObject.ofPredeformation`: the formal object over the site of a formal
  object of the predeformation category.
* `Deformation.Artin.FormalObject.ofPredeformationMap`: the induced morphism of formal objects
  over the site, in the opposite direction.

## Main results

* `Deformation.Artin.FormalObject.ofPredeformation_level_over`: the `n`-th level lies over the
  `n`-th infinitesimal thickening of `Spec A ⟶ Spec Λ ⟶ S`.
* `Deformation.Artin.FormalObject.ofPredeformationMap_isBaseMap`: the induced morphism has the
  spectrum of the given map of complete local algebras as its map of bases.

## References

* [Stacks Project, Tag 06H3](https://stacks.math.columbia.edu/tag/06H3)
* [Stacks Project, Tag 07T4](https://stacks.math.columbia.edu/tag/07T4)
* [Stacks Project, Tag 07X4](https://stacks.math.columbia.edu/tag/07X4)
* [Stacks Project, Tag 0CXH](https://stacks.math.columbia.edu/tag/0CXH)
* [Stacks Project, Tag 0DQV](https://stacks.math.columbia.edu/tag/0DQV)
-/

@[expose] public noncomputable section

namespace Deformation.Artin

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u v w

/-! ### Equality of formal objects over the site -/

section Ext

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : Type v} [Category.{w} F] {p : F ⥤ BigFppfOver B S hS}

/-- Formal objects over the site agreeing on base, levels and transitions are equal, the
transitions being compared through the identifications of the levels. -/
theorem FormalObject.ext_of_level {ζ ζ' : FormalObject B S hS p} (hb : ζ.base = ζ'.base)
    (hl : ∀ n, ζ.level n = ζ'.level n)
    (ht : ∀ n, ζ.transition n = eqToHom (hl n) ≫ ζ'.transition n ≫ eqToHom (hl (n + 1)).symm) :
    ζ = ζ' := by
  rcases ζ with ⟨b, c, l, le, t, tl⟩
  rcases ζ' with ⟨b', c', l', le', t', tl'⟩
  dsimp only at hb hl ht
  subst hb
  have hl' : l = l' := funext hl
  subst hl'
  have ht' : t = t' := funext fun n => by simpa using ht n
  subst ht'
  rfl

end Ext

/-! ### Complete local algebras as complete local bases -/

section FormalBase

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {S : Scheme.{u}}
  (iΛ : Spec (.of Λ) ⟶ S)

/-- The residue point of a complete local `Λ`-algebra with residue field `k`, read on the zeroth
infinitesimal thickening, is the point `Spec k ⟶ Spec Λ ⟶ S` up to the spectrum of the chosen
identification of the residue field with `k`. -/
theorem completeLocalAlg_residuePoint_eq (A : CompleteLocalAlgCat.{u, u, u} Λ k) :
    adicThickeningι A (maximalIdeal A) 0 ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ =
      Spec.map (((Ideal.quotientEquivAlgOfEq Λ (pow_one (maximalIdeal A))).trans
          A.residueEquiv).toRingEquiv.toCommRingCatIso.inv) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ := by
  let e₀ : (A ⧸ maximalIdeal A ^ (0 + 1)) ≃ₐ[Λ] k :=
    (Ideal.quotientEquivAlgOfEq Λ (pow_one (maximalIdeal A))).trans A.residueEquiv
  rw [adicThickeningι, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  ext a
  show Ideal.Quotient.mk _ (algebraMap Λ A a) = e₀.symm (algebraMap Λ k a)
  rw [AlgEquiv.commutes]
  rfl

/-- A Noetherian complete local `Λ`-algebra `A` with residue field `k`, over a chart
`Spec Λ ⟶ S` through which the finite type point `Spec k ⟶ S` factors, as a complete local base
over `S` with structure morphism `Spec A ⟶ Spec Λ ⟶ S`. -/
def completeLocalAlgFormalBase
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (A : CompleteLocalAlgCat.{u, u, u} Λ k) : FormalBase S where
  R := A
  noetherian := inferInstance
  complete := inferInstance
  toS := Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ
  residueLocallyFiniteType := by
    have := hfinite.1
    rw [completeLocalAlg_residuePoint_eq iΛ A]
    infer_instance
  residueQuasiCompact := by
    have := hfinite.2
    rw [completeLocalAlg_residuePoint_eq iΛ A]
    infer_instance

/-- The underlying ring of `completeLocalAlgFormalBase iΛ hfinite A` is `A`. -/
@[simp]
theorem completeLocalAlgFormalBase_R
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (A : CompleteLocalAlgCat.{u, u, u} Λ k) :
    (completeLocalAlgFormalBase iΛ hfinite A).R = A := rfl

/-- The structure morphism of `completeLocalAlgFormalBase iΛ hfinite A` is the composite
`Spec A ⟶ Spec Λ ⟶ S`. -/
theorem completeLocalAlgFormalBase_toS
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (A : CompleteLocalAlgCat.{u, u, u} Λ k) :
    (completeLocalAlgFormalBase iΛ hfinite A).toS =
      Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ := rfl

end FormalBase

/-! ### The formal object over the site -/

section Bridge

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
  {F : Type v} [Category.{w} F] (p : F ⥤ BigFppfOver B S hS)
  (x₀ : F) (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
    QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- An object of the big fppf site over `S` is determined by the object of `Over S` it gives. -/
theorem bigFppfOver_eq_of_post_obj_eq {U V : BigFppfOver B S hS}
    (h : (Over.post B.inclusion).obj U = (Over.post B.inclusion).obj V) : U = V := by
  rcases U with ⟨U, ⟨⟨⟩⟩, f⟩
  rcases V with ⟨V, ⟨⟨⟩⟩, g⟩
  have hUV : U = V := ObjectProperty.FullSubcategory.ext (congrArg Over.left h)
  subst hUV
  have hfg : B.inclusion.map f = B.inclusion.map g := by
    have := congrArg (fun o : Over S => (⟨o.left, o.hom⟩ : Σ X : Scheme.{u}, X ⟶ S)) h
    simp only [Sigma.mk.injEq] at this
    exact eq_of_heq this.2
  rw [B.inclusion.map_injective hfg]

/-- The morphism of schemes underlying a morphism of the site conjugated by comparison
isomorphisms of equalities of objects is the underlying morphism conjugated by the comparison
isomorphisms of the underlying schemes. -/
theorem bigFppfOver_left_hom_eqToHom {U V T₁ T₂ : BigFppfOver B S hS} (m : U ⟶ V)
    (h₁ : T₁ = U) (h₂ : V = T₂) :
    (eqToHom h₁ ≫ m ≫ eqToHom h₂).left.hom =
      eqToHom (congrArg (fun W : BigFppfOver B S hS => W.left.obj) h₁) ≫ m.left.hom ≫
        eqToHom (congrArg (fun W : BigFppfOver B S hS => W.left.obj) h₂) := by
  subst h₁ h₂
  simp

/-- A deformation of `x₀` lying over an object `A` of `𝒞_Λ` lies over `Spec A ⟶ Spec Λ ⟶ S`. -/
theorem predeformation_point_over {a : (predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀).carrier}
    {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (ha : (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection.obj a = A) :
    (p ⋙ Over.post B.inclusion).obj
        ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a).point =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) := by
  have h := ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a).base
  have hA : ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects
      a).algebra = A :=
    ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).object_projection
      a).symm.trans ha
  rwa [hA] at h

/-- The `n`-th level of a formal object of the predeformation category lies over the `n`-th
infinitesimal thickening of `Spec A ⟶ Spec Λ ⟶ S`. -/
theorem predeformation_formalObject_level_over
    (ξ : letI := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).category
      Deformation.FormalObject
        (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) (n : ℕ) :
    (p ⋙ Over.post B.inclusion).obj
        ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects
          (ξ.level n)).point =
      Over.mk ((completeLocalAlgFormalBase iΛ hfinite ξ.base).truncationToS n) := by
  refine (predeformation_point_over B S hS iΛ p x₀ hx₀ (ξ.level_eq n)).trans ?_
  congr 1
  show _ = adicThickeningι ξ.base (maximalIdeal ξ.base) n ≫
    Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ
  rw [adicThickeningι, ← Category.assoc, ← Spec.map_comp]
  rfl

/-- Each infinitesimal thickening of the base of a formal object of the predeformation category
belongs to the chosen big fppf site. -/
theorem predeformation_formalObject_contains
    (ξ : letI := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).category
      Deformation.FormalObject
        (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) (n : ℕ) :
    B.Contains ((completeLocalAlgFormalBase iΛ hfinite ξ.base).truncation n) := by
  have h := congrArg Over.left
    (predeformation_formalObject_level_over B S hS iΛ p x₀ hx₀ hfinite ξ n)
  change (p.obj ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects
    (ξ.level n)).point).left.obj =
      (completeLocalAlgFormalBase iΛ hfinite ξ.base).truncation n at h
  rw [← h]
  exact (p.obj ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects
    (ξ.level n)).point).left.property

/-- The `n`-th level of a formal object of the predeformation category, as an object of the
site, is the `n`-th infinitesimal thickening of its base. -/
theorem predeformation_formalObject_level_eq
    (ξ : letI := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).category
      Deformation.FormalObject
        (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) (n : ℕ) :
    p.obj ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects
        (ξ.level n)).point =
      truncationOver B S hS (completeLocalAlgFormalBase iΛ hfinite ξ.base)
        (predeformation_formalObject_contains B S hS iΛ p x₀ hx₀ hfinite ξ) n :=
  bigFppfOver_eq_of_post_obj_eq B S hS
    (predeformation_formalObject_level_over B S hS iΛ p x₀ hx₀ hfinite ξ n)

/-- The reversed arrow of a morphism of a predeformation construction lying over an arrow `g`
of `𝒞_Λ` lies over `Spec g`, read through any identifications of the two points with spectra. -/
theorem predeformation_arrow_over {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type v} [Category.{w} X] {q : X ⥤ Over S} {x₀ : X}
    {hx₀ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (D : PredeformationConstruction iΛ q x₀ hx₀) :
    letI := D.category
    ∀ {a b : D.carrier} (f : a ⟶ b)
      {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k}
      (g : A ⟶ A') (_ : D.projection.IsHomLift g f)
      (ha : (q.obj (D.objects a).point).left = Spec (.of A))
      (hb : (q.obj (D.objects b).point).left = Spec (.of A')),
      eqToHom hb.symm ≫ (q.map (D.morphisms a b f).arrow).left ≫ eqToHom ha =
        Spec.map (CommRingCat.ofHom g.hom.toRingHom) := by
  let := D.category
  intro a b f A A' g hf ha hb
  let := hf
  have hA : (D.objects a).algebra = A :=
    (D.object_projection a).symm.trans (IsHomLift.domain_eq D.projection g f)
  have hB : (D.objects b).algebra = A' :=
    (D.object_projection b).symm.trans (IsHomLift.codomain_eq D.projection g f)
  subst A A'
  have hg : g = (D.morphisms a b f).ringHom :=
    (IsHomLift.fac D.projection g f).trans (D.morphism_projection f)
  subst g
  exact (D.morphisms a b f).arrow_base

/-- The formal object over the site of a formal object of the predeformation category: its
levels are the objects of `𝒳` underlying the deformations `x₀ ⟶ ξ_n`, and the transitions are
the reversed arrows of the transitions of `ξ`. -/
def FormalObject.ofPredeformation
    (ξ : letI := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).category
      Deformation.FormalObject
        (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    FormalObject B S hS p := by
  letI := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).category
  exact
  { base := completeLocalAlgFormalBase iΛ hfinite ξ.base
    contains := predeformation_formalObject_contains B S hS iΛ p x₀ hx₀ hfinite ξ
    level := fun n =>
      ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects (ξ.level n)).point
    level_eq := predeformation_formalObject_level_eq B S hS iΛ p x₀ hx₀ hfinite ξ
    transition := fun n =>
      ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).morphisms _ _
        (ξ.transition n)).arrow
    transition_lift := by
      intro n
      apply IsHomLift.of_fac p _ _ (predeformation_formalObject_level_eq B S hS iΛ p x₀ hx₀
        hfinite ξ n) (predeformation_formalObject_level_eq B S hS iΛ p x₀ hx₀ hfinite ξ (n + 1))
      apply (Over.post B.inclusion).map_injective
      apply Over.OverMorphism.ext
      simp only [Functor.map_comp]
      have ha (m : ℕ) :
          ((p ⋙ Over.post B.inclusion).obj
            ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects
              (ξ.level m)).point).left =
            Spec (.of (AdicTruncation.obj ξ.base m)) :=
        congrArg Over.left ((predeformation_point_over B S hS iΛ p x₀ hx₀ (ξ.level_eq m)))
      have ht := predeformation_arrow_over
        (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀) (ξ.transition n)
        ((AdicTruncation.transitionNat n).app ξ.base)
        (ξ.transition_lift n) (ha (n + 1)) (ha n)
      have hring :
          ((AdicTruncation.transitionNat n).app ξ.base).hom.toRingHom =
            Ideal.Quotient.factorPow (maximalIdeal ξ.base) (Nat.le_succ (n + 1)) := by
        ext z
        rfl
      rw [hring] at ht
      simp only [eqToHom_map, Over.comp_left, Over.eqToHom_left]
      convert ht.symm using 1 <;> rfl }

/-- The morphism of formal objects over the site, in the opposite direction, induced by a
morphism `ξ ⟶ ξ'` of formal objects of the predeformation category: its components are the
reversed arrows `ξ'_n ⟶ ξ_n` of `𝒳` of the morphisms of deformations `ξ_n ⟶ ξ'_n`. -/
def FormalObject.ofPredeformationMap
    {ξ ξ' : letI := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).category
      Deformation.FormalObject
        (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection}
    (f : ξ ⟶ ξ') :
    FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ' ⟶
      FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ := by
  letI := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).category
  exact
  { app := fun n =>
      ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).morphisms _ _
        (f.app n)).arrow
    naturality := fun n => by
      have h := congrArg (fun g => ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀
        hx₀).morphisms _ _ g).arrow) (f.naturality n)
      simp only [(predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀
        hx₀).reversed_composition] at h
      exact h.symm }

/-- The `n`-th component of the induced morphism is the reversed arrow of the `n`-th component of
the given one. -/
theorem FormalObject.ofPredeformationMap_app
    {ξ ξ' : letI := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).category
      Deformation.FormalObject
        (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection}
    (f : ξ ⟶ ξ') (n : ℕ) :
    (FormalObject.ofPredeformationMap B S hS iΛ p x₀ hx₀ hfinite f).app n =
      ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).morphisms _ _
        (f.app n)).arrow := rfl

/-- The map of complete local bases of the induced morphism is the spectrum of the given map of
complete local algebras. -/
theorem FormalObject.ofPredeformationMap_isBaseMap
    {ξ ξ' : letI := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).category
      Deformation.FormalObject
        (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection}
    (f : ξ ⟶ ξ') :
    (FormalObject.ofPredeformationMap B S hS iΛ p x₀ hx₀ hfinite f).IsBaseMap
      (Spec.map (CommRingCat.ofHom f.base.hom.toRingHom)) := by
  let := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).category
  refine ⟨?_, fun n => ?_⟩
  · show Spec.map (CommRingCat.ofHom f.base.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ ξ'.base)) ≫ iΛ
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact f.base.hom.comp_algebraMap
  · have ha (η : Deformation.FormalObject
        (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) (m : ℕ) :
        ((p ⋙ Over.post B.inclusion).obj
          ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects
            (η.level m)).point).left =
          Spec (.of (AdicTruncation.obj η.base m)) :=
      congrArg Over.left ((predeformation_point_over B S hS iΛ p x₀ hx₀ (η.level_eq m)))
    have ht := predeformation_arrow_over
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀) (f.app n)
      ((AdicTruncation.functor n).map f.base) (f.app_lift n) (ha ξ n) (ha ξ' n)
    have hsq : Spec.map (CommRingCat.ofHom
          ((AdicTruncation.functor n).map f.base).hom.toRingHom) ≫
        adicThickeningι ξ.base (maximalIdeal ξ.base) n =
        adicThickeningι ξ'.base (maximalIdeal ξ'.base) n ≫
          Spec.map (CommRingCat.ofHom f.base.hom.toRingHom) := by
      have e₁ := Spec.map_comp
        (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal ξ.base ^ (n + 1))) :
          CommRingCat.of ξ.base ⟶ CommRingCat.of ((AdicTruncation.functor n).obj ξ.base))
        (CommRingCat.ofHom ((AdicTruncation.functor n).map f.base).hom.toRingHom)
      have e₂ := Spec.map_comp (CommRingCat.ofHom f.base.hom.toRingHom)
        (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal ξ'.base ^ (n + 1))))
      rw [adicThickeningι, adicThickeningι]
      refine e₁.symm.trans (Eq.trans ?_ e₂)
      congr 1
    rw [bigFppfOver_left_hom_eqToHom]
    exact (congrArg (· ≫ adicThickeningι ξ.base (maximalIdeal ξ.base) n) ht).trans hsq

end Bridge

end Deformation.Artin

end
