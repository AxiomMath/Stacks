module

public import StacksFrontier.AlgebraicGeometry.Topologies.FppfPostInclusion
public import StacksFrontier.Deformation.Artin.FormalObject.Versal
public import StacksFrontier.Deformation.Artin.Predeformation

/-!
# Deformations in a thin category over the big fppf site

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category over the big fppf site of `S`, let `x₀` be a
point of `𝒳` over `Spec k` with a factorization through `Spec Λ`, and consider the
predeformation category of `x₀`: its objects are arrows `x₀ ⟶ x` of `𝒳` over the canonical
closed-point map of an Artinian local `Λ`-algebra, and its reversed arrows are the
morphisms of `𝒳` compatible with them.

Suppose that `𝒳` is *thin over the site*: a morphism of `𝒳` is determined by its image in
`(Sch/S)_{fppf}`. Then:

* a morphism of deformations is determined by its arrow of `𝒞_Λ`
  (`Deformation.Artin.DeformationMorphism.eq_of_ringHom_eq`);
* two deformations over *equal* Artinian local algebras are joined by a morphism of
  deformations lying over the identification of those algebras, as soon as their points are
  joined by a morphism of `𝒳` over the identification of the corresponding objects of the
  site (`Deformation.Artin.verticalDeformationMorphism`).

## Main definitions

* `Deformation.Artin.verticalDeformationMorphism`: the morphism of deformations over an
  identification of the underlying Artinian local algebras.

## Main results

* `Deformation.Artin.DeformationObject.arrow_left_eq`,
  `Deformation.Artin.DeformationMorphism.arrow_left_eq`: the two `arrow_base` fields solved
  for the underlying scheme morphism.
* `Deformation.Artin.DeformationObject.point_eq_of_algebra_eq`: deformations over equal
  algebras have their points over the same object of the site.
* `Deformation.Artin.DeformationMorphism.eq_of_ringHom_eq`: in a thin category over the
  site, a morphism of deformations is determined by its arrow of `𝒞_Λ`.

## References

* [Stacks Project, Tag 07T4](https://stacks.math.columbia.edu/tag/07T4)
-/

@[expose] public noncomputable section

namespace Deformation.Artin

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u v w

/-! ### Spectra of identified Artinian local algebras -/

section Identifications

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- `Spec` of an identification of Artinian local algebras is the identification of their
spectra. -/
public theorem specMap_ofHom_eqToHom
    {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (h : A = A')
    (e : (Spec (.of A') : Scheme.{u}) = Spec (.of A)) :
    Spec.map (CommRingCat.ofHom (eqToHom h).hom.toRingHom) = eqToHom e := by
  subst h
  exact Spec.map_id _

/-- The residue map of an Artinian local algebra is carried to that of an identified one. -/
public theorem residueMap_comp_eqToHom
    {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (h : A = A') :
    (residueMap A').comp (eqToHom h).hom.toRingHom = residueMap A := by
  subst h
  rfl

/-- The closed-point map of an Artinian local algebra, followed by an identification with
another, is the closed-point map of that other one. -/
public theorem specMap_residueMap_comp_eqToHom
    {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (h : A = A') :
    Spec.map (CommRingCat.ofHom (residueMap A')) ≫
        Spec.map (CommRingCat.ofHom (eqToHom h).hom.toRingHom) =
      Spec.map (CommRingCat.ofHom (residueMap A)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, residueMap_comp_eqToHom h]

end Identifications

section

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {iΛ : Spec (.of Λ) ⟶ S}
variable {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {x₀ : X}
variable {hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
  (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

/-! ### The underlying scheme morphisms -/

/-- Solving a conjugation by identifications for the middle morphism. -/
private theorem eq_eqToHom_comp_comp_eqToHom {C : Type*} [Category C] {W X Y Z : C}
    (e₁ : W = X) (e₂ : Y = Z) {f : W ⟶ Y} {g : X ⟶ Z}
    (h : eqToHom e₁.symm ≫ f ≫ eqToHom e₂ = g) : f = eqToHom e₁ ≫ g ≫ eqToHom e₂.symm := by
  subst e₁ e₂
  simpa using h

/-- The underlying scheme morphism of the arrow of a deformation out of the closed fibre is the
canonical closed-point map of its Artinian local algebra, conjugated by the identifications of
its two endpoints with spectra of rings. -/
public theorem DeformationObject.arrow_left_eq
    (d : DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀) :
    ((p ⋙ Over.post B.inclusion).map d.arrow).left =
      eqToHom (congrArg Over.left hx₀) ≫
        Spec.map (CommRingCat.ofHom (residueMap d.algebra)) ≫
        eqToHom (congrArg Over.left d.base).symm := by
  exact eq_eqToHom_comp_comp_eqToHom _ _ d.arrow_base

/-- The underlying scheme morphism of the reversed arrow of a morphism of deformations is `Spec`
of its arrow of `𝒞_Λ`, conjugated by the identifications of its two endpoints with spectra of
rings. -/
public theorem DeformationMorphism.arrow_left_eq
    {a b : DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀}
    (u : DeformationMorphism iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀ a b) :
    ((p ⋙ Over.post B.inclusion).map u.arrow).left =
      eqToHom (congrArg Over.left b.base) ≫
        Spec.map (CommRingCat.ofHom u.ringHom.hom.toRingHom) ≫
        eqToHom (congrArg Over.left a.base).symm := by
  exact eq_eqToHom_comp_comp_eqToHom _ _ u.arrow_base

/-! ### Thinness over the site -/

/-- If a morphism of the ambient category is determined by its image in schemes over `S`, then a
morphism of deformations is determined by its arrow of `𝒞_Λ`. -/
public theorem DeformationMorphism.eq_of_ringHom_eq
    (hthin : ∀ {z w : X} (s t : z ⟶ w), p.map s = p.map t → s = t)
    {a b : DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀}
    {u v : DeformationMorphism iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀ a b}
    (h : u.ringHom = v.ringHom) : u = v := by
  refine DeformationMorphism.ext_of_components iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀ h ?_
  refine hthin u.arrow v.arrow
    (BigFppfOver.map_injective_post_inclusion B S hS (Over.OverMorphism.ext ?_))
  change ((p ⋙ Over.post B.inclusion).map u.arrow).left =
    ((p ⋙ Over.post B.inclusion).map v.arrow).left
  rw [u.arrow_left_eq, v.arrow_left_eq, h]

/-- Two deformations over equal Artinian local algebras have their points over the same object of
the site. -/
public theorem DeformationObject.point_eq_of_algebra_eq
    (a b : DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (halg : a.algebra = b.algebra) : p.obj b.point = p.obj a.point :=
  BigFppfOver.obj_injective_post_inclusion B S hS
    (b.base.trans
      ((congrArg
        (fun A : ArtinianLocalAlgCat.{u, u, u} Λ k =>
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) : Over S))
        halg).symm.trans a.base.symm))

variable (a b : DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
  (halg : a.algebra = b.algebra) (u : b.point ⟶ a.point)
  (hu : p.map u = eqToHom (DeformationObject.point_eq_of_algebra_eq a b halg))

include hu

/-- A morphism of the ambient category over an identification of objects of the site lies over
the identification of the Artinian local algebras. -/
public theorem verticalArrow_base :
    eqToHom (congrArg Over.left b.base).symm ≫
        ((p ⋙ Over.post B.inclusion).map u).left ≫
        eqToHom (congrArg Over.left a.base) =
      Spec.map (CommRingCat.ofHom (eqToHom halg).hom.toRingHom) := by
  rw [Functor.comp_map, hu, eqToHom_map, Over.eqToHom_left, eqToHom_trans, eqToHom_trans]
  exact (specMap_ofHom_eqToHom halg _).symm

/-- The underlying scheme morphism of a morphism of the ambient category over an identification
of objects of the site is `Spec` of the identification of the Artinian local algebras, conjugated
by the identifications of its two endpoints with spectra of rings. -/
public theorem verticalArrow_left_eq :
    ((p ⋙ Over.post B.inclusion).map u).left =
      eqToHom (congrArg Over.left b.base) ≫
        Spec.map (CommRingCat.ofHom (eqToHom halg).hom.toRingHom) ≫
        eqToHom (congrArg Over.left a.base).symm := by
  exact eq_eqToHom_comp_comp_eqToHom _ _ (verticalArrow_base a b halg u hu)

/-- In a thin category over the site, the morphism of deformations over an identification of the
underlying Artinian local algebras, given by a morphism of the ambient category joining their
points over the resulting identification of objects of the site. -/
public def verticalDeformationMorphism
    (hthin : ∀ {z w : X} (s t : z ⟶ w), p.map s = p.map t → s = t) :
    DeformationMorphism iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀ a b where
  ringHom := eqToHom halg
  arrow := u
  triangle := by
    refine hthin (b.arrow ≫ u) a.arrow
      (BigFppfOver.map_injective_post_inclusion B S hS (Over.OverMorphism.ext ?_))
    change ((p ⋙ Over.post B.inclusion).map (b.arrow ≫ u)).left =
      ((p ⋙ Over.post B.inclusion).map a.arrow).left
    rw [Functor.map_comp, Over.comp_left, verticalArrow_left_eq a b halg u hu,
      b.arrow_left_eq, a.arrow_left_eq, ← specMap_residueMap_comp_eqToHom halg]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  arrow_base := verticalArrow_base a b halg u hu

/-- The morphism of deformations over an identification of algebras lies over that
identification. -/
@[simp]
public theorem verticalDeformationMorphism_ringHom
    (hthin : ∀ {z w : X} (s t : z ⟶ w), p.map s = p.map t → s = t) :
    (verticalDeformationMorphism a b halg u hu hthin).ringHom = eqToHom halg := rfl

end

/-! ### The predeformation category of a thin category -/

section Category

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {iΛ : Spec (.of Λ) ⟶ S}
variable {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {x₀ : X}
variable {hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
  (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

/-- Morphisms of the predeformation category of a thin category are determined by their image in
`𝒞_Λ`. -/
public theorem predeformationCategory_hom_ext
    (hthin : ∀ {z w : X} (s t : z ⟶ w), p.map s = p.map t → s = t)
    {z w : (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).carrier}
    (s t : z ⟶ w)
    (h : (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection.map s =
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection.map t) :
    s = t := by
  refine (PredeformationConstruction.morphisms _ z w).injective
    (DeformationMorphism.eq_of_ringHom_eq hthin ?_)
  rw [← PredeformationConstruction.morphism_projection _ s,
    ← PredeformationConstruction.morphism_projection _ t, h]

/-- If the ambient category is thin over the site and has morphisms over identifications of
objects of the site, then two objects of its predeformation category over the same object of
`𝒞_Λ` are joined by a morphism over the identity. -/
public theorem exists_vertical_predeformationHom
    (hthin : ∀ {z w : X} (s t : z ⟶ w), p.map s = p.map t → s = t)
    (hvert : ∀ {z w : X} (e : p.obj z = p.obj w), ∃ s : z ⟶ w, p.map s = eqToHom e)
    (z w : (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).carrier)
    (h : (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection.obj z =
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection.obj w) :
    ∃ a : z ⟶ w,
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection.map a =
        eqToHom h := by
  have halg : (PredeformationConstruction.objects _ z).algebra =
      (PredeformationConstruction.objects _ w).algebra :=
    (PredeformationConstruction.object_projection _ z).symm.trans
      (h.trans (PredeformationConstruction.object_projection _ w))
  obtain ⟨u, hu⟩ := hvert (DeformationObject.point_eq_of_algebra_eq
    (PredeformationConstruction.objects _ z) (PredeformationConstruction.objects _ w) halg)
  obtain ⟨a, hae⟩ : ∃ a : z ⟶ w,
      PredeformationConstruction.morphisms _ z w a =
        verticalDeformationMorphism (PredeformationConstruction.objects _ z)
          (PredeformationConstruction.objects _ w) halg u hu hthin :=
    ⟨_, Equiv.apply_symm_apply _ _⟩
  refine ⟨a, ?_⟩
  have hmp := PredeformationConstruction.morphism_projection _ a
  rw [hae, verticalDeformationMorphism_ringHom, eqToHom_comp_iff, comp_eqToHom_iff] at hmp
  rw [hmp]
  simp

end Category

end Deformation.Artin

end
