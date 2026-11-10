module

public import Mathlib.AlgebraicGeometry.Artinian
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.ArtinianLocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso
public import StacksFrontier.CategoryTheory.TwoFibreProduct.SquareComparisonPaste
public import StacksFrontier.CategoryTheory.TwoFibreProduct.SquareComparisonTransfer
public import StacksFrontier.Deformation.Artin.RimSchlessinger.ConditionRS
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FiberSquareComparison
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.RimSchlessinger.Basic
public import StacksFrontier.Deformation.RimSchlessingerCategory.SmallExtensionCriterion

/-!
# Deformation categories from condition (RS)

Let `𝒳` be a category fibred in groupoids over the big fppf site of a locally Noetherian scheme
`S`. Under (RS) (`Deformation.Artin.SatisfiesRS`) the predeformation category of a finite-type
field-valued point of `𝒳` is a deformation category: a fibre product in the category `𝒞_Λ` of
Artinian local algebras along a surjection is realized on the site as a pushout of affine
schemes along a closed immersion, so (RS) turns the fibre over that fibre product into the
two-fibre product of the fibres over the other three corners, and transporting a
compatible pair of deformations through that equivalence produces the required cartesian
square of deformations. Condition (RS*) gives the same conclusion: it is enough to test
condition (RS) of a cofibred category on small extensions, and the square attached to a
small extension is one of those (RS*) quantifies over.

## Main results

* `Deformation.Artin.isDeformationCategory_predeformationCategory` — the predeformation
  category of a finite-type field-valued point of a fibred category satisfying (RS) is a
  deformation category.
* `Deformation.Artin.isDeformationCategory_predeformationCategory_of_satisfiesRSStar` — the
  same conclusion under (RS*), which bounds the squares to be tested by the square-zero
  ones.
* `Deformation.Artin.isDeformationCategory_predeformationCategory_of_satisfiesRSOfResidue` — the
  same conclusion when (RS) holds at the squares inducing surjections of residue fields.

## Implementation notes

For the deformation-category statements, the functor to schemes over `S` is induced from
the chosen big fppf site, and the chosen map `Spec Λ ⟶ S` is the factorization used to form
the predeformation category; finite type of the field-valued point is expressed by local
finite type and quasi-compactness of its structure map. Each Artinian local algebra of the
problem is placed on the site through the size bound for finite-type morphisms, and the
square required of it comes from the concrete fibre product of algebras of Stacks 06GH:
under (RS) through the affine-pushout description of a surjection, and under (RS*) through
the induced fibre product of rings of global sections.

## References

* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 07WU](https://stacks.math.columbia.edu/tag/07WU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u u₁ u₂ u₃ v₁

/-! ### Deformations of a point of a category satisfying (RS) -/

namespace Deformation.Artin

open IsLocalRing

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

/-- The spectrum of an object of `𝒞_Λ` is affine, and its ring of global sections is local
and Artinian. -/
private theorem spec_of_artinianLocal_isArtinianLocal
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    IsAffine (Spec (.of A)) ∧
      IsLocalRing Γ(Spec (.of A), ⊤) ∧
      IsArtinianRing Γ(Spec (.of A), ⊤) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · exact (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm.isLocalRing
  · exact (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm.isArtinianRing

/-- The residue map of an object of `𝒞_Λ` is compatible with the structure maps from `Λ`, on
spectra. -/
private theorem spec_residueMap_comp_algebraMap
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Spec.map (CommRingCat.ofHom (residueMap A)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ A)) =
        Spec.map (CommRingCat.ofHom (algebraMap Λ k)) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  change A.residueEquiv (IsLocalRing.residue A (algebraMap Λ A a)) = algebraMap Λ k a
  rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply Λ A (ResidueField A) a]
  exact A.residueEquiv.commutes a

/-- Finite type of the chosen residue-field point transfers to the spectrum of any
Artinian local algebra with the specified residue field. -/
private theorem spec_finiteType_of_point
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (S : Scheme.{u}) (iΛ : Spec (.of Λ) ⟶ S)
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) := by
  let f : Spec (.of A) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ
  let g : Spec (.of k) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ
  let eSpec := Scheme.Spec.mapIso
    (RingEquiv.toCommRingCatIso A.residueEquiv.symm.toRingEquiv).op
  have hbase : Spec.map (CommRingCat.ofHom (residueMap A)) ≫ f = g := by
    simp only [f, g, ← spec_residueMap_comp_algebraMap A, Category.assoc]
  have hfactor :
      eSpec.hom ≫ Spec.map (CommRingCat.ofHom (residueMap A)) =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) := by
    dsimp [eSpec]
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext a
    change A.residueEquiv.symm (A.residueEquiv (IsLocalRing.residue A a)) = _
    exact A.residueEquiv.symm_apply_apply _
  have hcanonical :
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ f = eSpec.hom ≫ g := by
    rw [← hfactor, Category.assoc, hbase]
  have : LocallyOfFiniteType g := hfinite
  have : QuasiCompact g := hqc
  have hresFinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ f) := by
    rw [hcanonical]
    infer_instance
  have hresQC : QuasiCompact
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ f) := by
    rw [hcanonical]
    infer_instance
  exact AlgebraicGeometry.finiteType_iff_residueField_comp_finiteType S A f |>.2
    ⟨hresFinite, hresQC⟩

/-- The spectrum of each Artinian local algebra in the deformation problem belongs to the
chosen big fppf site, since its map to `S` is finite type. -/
private theorem spec_mem_bigFppfSite
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    B.Contains (Spec (.of A)) := by
  let f : Spec (.of A) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ
  have hf := spec_finiteType_of_point A S iΛ hfinite hqc
  have : LocallyOfFiniteType f := hf.1
  have : QuasiCompact f := hf.2
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact f hS

/-- The concrete fibre product of Artinian local algebras along a surjection is a fibre
product of the underlying commutative rings. -/
private theorem specPullback_isPullback
    {Λ : Type u} {k : Type u₃} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B C : ArtinianLocalAlgCat.{u, u₂, u₃} Λ k}
    (f : A ⟶ C) (g : B ⟶ C) (hg : Function.Surjective g.hom) :
    IsPullback
      (CommRingCat.ofHom
        (ArtinianLocalAlgCat.pullbackFst_of_surjective f g (Or.inr hg)).hom.toRingHom)
      (CommRingCat.ofHom
        (ArtinianLocalAlgCat.pullbackSnd_of_surjective f g (Or.inr hg)).hom.toRingHom)
      (CommRingCat.ofHom f.hom.toRingHom)
      (CommRingCat.ofHom g.hom.toRingHom) := by
  let f' : CommRingCat.of A ⟶ CommRingCat.of C := CommRingCat.ofHom f.hom.toRingHom
  let g' : CommRingCat.of B ⟶ CommRingCat.of C := CommRingCat.ofHom g.hom.toRingHom
  let P := ArtinianLocalAlgCat.pullbackObj_of_surjective f g (Or.inr hg)
  let q' : CommRingCat.of P ⟶ CommRingCat.of A := CommRingCat.ofHom
    (ArtinianLocalAlgCat.pullbackFst_of_surjective f g (Or.inr hg)).hom.toRingHom
  let p' : CommRingCat.of P ⟶ CommRingCat.of B := CommRingCat.ofHom
    (ArtinianLocalAlgCat.pullbackSnd_of_surjective f g (Or.inr hg)).hom.toRingHom
  have hlim : IsLimit (CommRingCat.pullbackCone f' g') :=
    CommRingCat.pullbackConeIsLimit f' g'
  have hq : q' = (CommRingCat.pullbackCone f' g').fst := by
    simp only [q', P, ArtinianLocalAlgCat.pullbackFst_of_surjective_hom]
    rfl
  have hp : p' = (CommRingCat.pullbackCone f' g').snd := by
    simp only [p', P, ArtinianLocalAlgCat.pullbackSnd_of_surjective_hom]
    rfl
  change IsPullback q' p' f' g'
  rw [hq, hp]
  exact IsPullback.of_isLimit hlim

/-- The concrete pullback of Artinian local algebras gives the affine-scheme pushout
square used by the geometric Rim--Schlessinger condition. -/
private theorem specPullback_isPushout
    {Λ : Type u} {k : Type u₃} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B C : ArtinianLocalAlgCat.{u, u₂, u₃} Λ k}
    (f : A ⟶ C) (g : B ⟶ C) (hg : Function.Surjective g.hom) :
    IsPushout
      (Spec.map (CommRingCat.ofHom g.hom.toRingHom))
      (Spec.map (CommRingCat.ofHom f.hom.toRingHom))
      (Spec.map (CommRingCat.ofHom
        (ArtinianLocalAlgCat.pullbackSnd_of_surjective
          f g (Or.inr hg)).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom
        (ArtinianLocalAlgCat.pullbackFst_of_surjective
          f g (Or.inr hg)).hom.toRingHom)) :=
  Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective _ _ _ _
    (specPullback_isPullback f g hg) hg

/-- A surjective map of the Artinian local algebras gives the closed immersion
corner of the affine pushout square. -/
private theorem specMap_isClosedImmersion_of_surjective
    {Λ : Type u} {k : Type u₃} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B : ArtinianLocalAlgCat.{u, u₂, u₃} Λ k}
    (f : A ⟶ B) (hf : Function.Surjective f.hom) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom f.hom.toRingHom)) :=
  IsClosedImmersion.spec_of_surjective _ hf

/-- The spectrum of an object of `𝒞_Λ`, read as an object of the big fppf site over `S`
through the structure map induced by the algebra map from `Λ`. -/
@[implicit_reducible] private noncomputable def specOver
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : B.Contains (Spec (.of A))) : AlgebraicGeometry.BigFppfOver B S hS := by
  let X := B.obj hA
  let Y := B.obj hS
  let f : B.inclusion.obj X ⟶ B.inclusion.obj Y :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ
  exact Over.mk (B.inclusion.preimage f)

/-- The spectrum of the residue field `k`, read as an object of the big fppf site over `S`
through the chosen field-valued point. -/
@[implicit_reducible] private noncomputable def specOverField
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (hK : B.Contains (Spec (.of k))) :
    AlgebraicGeometry.BigFppfOver B S hS := by
  let X := B.obj hK
  let Y := B.obj hS
  let f : B.inclusion.obj X ⟶ B.inclusion.obj Y :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ
  exact Over.mk (B.inclusion.preimage f)

/-- Two objects of a slice category are equal as soon as their domains are equal and their
structure maps agree after transporting along that equality. -/
private lemma overObjExt {C : Type*} [Category C] {S : C}
    (A B : Over S) (hleft : A.left = B.left)
    (hhom : A.hom = eqToHom hleft ≫ B.hom) : A = B := by
  obtain ⟨A_left, ⟨_⟩, A_hom⟩ := A
  obtain ⟨B_left, ⟨_⟩, B_hom⟩ := B
  obtain rfl : A_left = B_left := hleft
  obtain rfl : A_hom = B_hom := by simpa using hhom
  rfl

/-- An equality of objects of a slice category carries the structure map of one to the
structure map of the other. -/
private lemma overHom_eq {C : Type*} [Category C] {S : C}
    (A B : Over S) (h : A = B) :
    A.hom = eqToHom (congrArg Over.left h) ≫ B.hom := by
  cases h
  simp

/-- Forgetting the site, the slice object built from a morphism `f` of the site is the slice
object over `S` with structure map `f`. -/
private theorem over_post_mk_preimage
    (B : AlgebraicGeometry.BigFppfSite.{u}) {X Y}
    (f : B.inclusion.obj X ⟶ B.inclusion.obj Y) :
    (Over.post B.inclusion).obj (Over.mk (B.inclusion.preimage f)) = Over.mk f :=
  overObjExt _ _ (rfl : B.inclusion.obj X = B.inclusion.obj X) <| by
    change B.inclusion.map (B.inclusion.preimage f) =
      eqToHom (rfl : B.inclusion.obj X = B.inclusion.obj X) ≫ f
    rw [Functor.map_preimage, eqToHom_refl, Category.id_comp]

/-- Forgetting the site, the object attached to `A` is `Spec A` with its structure map to
`S`. -/
private theorem specOver_post
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : B.Contains (Spec (.of A))) :
    (Over.post B.inclusion).obj (specOver B S hS iΛ A hA) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) :=
  over_post_mk_preimage B _

/-- Forgetting the site, the object attached to `k` is `Spec k` with the chosen field-valued
point as its structure map. -/
private theorem specOverField_post
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (hK : B.Contains (Spec (.of k))) :
    (Over.post B.inclusion).obj (specOverField B S hS iΛ hK) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
  over_post_mk_preimage B _

/-- The distinguished point of the fibred category, read as an object of the fibre over the
site object attached to `k`. -/
private noncomputable def point_mem_specOverField
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {𝒳 : Type u₁} [Category.{v₁} 𝒳]
    (p : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (hK : B.Contains (Spec (.of k)))
    (x₀ : 𝒳)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    p.Fiber (specOverField B S hS iΛ hK) := by
  have hleftScheme := congrArg Over.left hx₀
  have hleft : (p.obj x₀).left = (specOverField B S hS iΛ hK).left := by
    apply ObjectProperty.FullSubcategory.ext
    change (p.obj x₀).left.obj = Spec (.of k)
    simpa [Over.post] using hleftScheme
  have hhom : (p.obj x₀).hom = eqToHom hleft ≫
      (specOverField B S hS iΛ hK).hom := by
    apply B.inclusion.map_injective
    have hh := overHom_eq _ _ hx₀
    let f : B.inclusion.obj (B.obj hK) ⟶ B.inclusion.obj (B.obj hS) :=
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ
    have hpre : (B.inclusion.preimage f).hom = f := by
      simpa using Functor.map_preimage B.inclusion f
    simpa [Over.post, specOverField, hleft, f, hpre] using hh
  exact ⟨x₀, overObjExt _ _ hleft hhom⟩

/-- The object deformed by a deformation, read as an object of the fibre over the site object
attached to the algebra of that deformation. -/
private noncomputable def deformationPointFiber
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {𝒳 : Type u₁} [Category.{v₁} 𝒳]
    (p : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (x₀ : 𝒳)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : B.Contains (Spec (.of A)))
    (d : DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (hd : d.algebra = A) :
    p.Fiber (specOver B S hS iΛ d.algebra (hd ▸ hA)) := by
  let hA' : B.Contains (Spec (.of d.algebra)) := hd ▸ hA
  have hleftScheme := congrArg Over.left d.base
  have hleft : (p.obj d.point).left =
      (specOver B S hS iΛ d.algebra hA').left := by
    apply ObjectProperty.FullSubcategory.ext
    change (p.obj d.point).left.obj = Spec (.of d.algebra)
    simpa [Over.post] using hleftScheme
  have hhom : (p.obj d.point).hom = eqToHom hleft ≫
      (specOver B S hS iΛ d.algebra hA').hom := by
    apply B.inclusion.map_injective
    have hh := overHom_eq _ _ d.base
    let f : B.inclusion.obj (B.obj hA') ⟶ B.inclusion.obj (B.obj hS) :=
      Spec.map (CommRingCat.ofHom (algebraMap Λ d.algebra)) ≫ iΛ
    have hpre : (B.inclusion.preimage f).hom = f := by
      simpa using Functor.map_preimage B.inclusion f
    simpa [Over.post, specOver, hleft, hA', f, hpre] using hh
  exact ⟨d.point, overObjExt _ _ hleft hhom⟩

/-- A morphism `A ⟶ A'` of `𝒞_Λ`, read as the morphism of the big fppf site given by its
spectrum, which goes from the object attached to `A'` to the object attached to `A`. -/
@[implicit_reducible] private noncomputable def specOverMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (hA : B.Contains (Spec (.of A))) (hA' : B.Contains (Spec (.of A')))
    (f : A ⟶ A') :
    specOver B S hS iΛ A' hA' ⟶ specOver B S hS iΛ A hA := by
  let Y := B.obj hA'
  let X := B.obj hA
  let g : B.inclusion.obj Y ⟶ B.inclusion.obj X :=
    Spec.map (CommRingCat.ofHom f.hom.toRingHom)
  refine Over.homMk (B.inclusion.preimage g) ?_
  apply B.inclusion.map_injective
  simp only [Functor.map_comp]
  let XA := B.obj hA
  let XB := B.obj hA'
  let XS := B.obj hS
  let fa : B.inclusion.obj XA ⟶ B.inclusion.obj XS :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ
  let fb : B.inclusion.obj XB ⟶ B.inclusion.obj XS :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ iΛ
  have hpreG : (B.inclusion.preimage g).hom = g := by
    simpa using Functor.map_preimage B.inclusion g
  have hpreA : (B.inclusion.preimage fa).hom = fa := by
    simpa using Functor.map_preimage B.inclusion fa
  have hpreB : (B.inclusion.preimage fb).hom = fb := by
    simpa using Functor.map_preimage B.inclusion fb
  change (B.inclusion.preimage g).hom ≫ (B.inclusion.preimage fa).hom =
    (B.inclusion.preimage fb).hom
  rw [hpreG, hpreA, hpreB]
  dsimp [fa, fb, g]
  have hspec : Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap Λ A')) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext x
    exact f.hom.commutes x
  rw [← Category.assoc]
  exact congrArg (fun q => q ≫ iΛ) hspec

/-- The site object attached to an object of `𝒞_Λ` is local Artinian. -/
private theorem specOver_isArtinianLocal
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : B.Contains (Spec (.of A))) :
    IsArtinianLocal B S hS (specOver B S hS iΛ A hA) := by
  change IsAffine (Spec (.of A)) ∧ IsLocalRing Γ(Spec (.of A), ⊤) ∧
    IsArtinianRing Γ(Spec (.of A), ⊤)
  exact spec_of_artinianLocal_isArtinianLocal A

/-- The site object attached to an object of `𝒞_Λ` is of finite type over `S`, because the
chosen field-valued point is. -/
private theorem specOver_isFiniteTypeOver
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : B.Contains (Spec (.of A)))
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    IsFiniteTypeOver B S hS (specOver B S hS iΛ A hA) := by
  let f : Spec (.of A) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ
  let X := B.obj hA
  let Y := B.obj hS
  let f' : B.inclusion.obj X ⟶ B.inclusion.obj Y := f
  have hpre : B.inclusion.map (B.inclusion.preimage f') = f' := by
    simpa using Functor.map_preimage B.inclusion f'
  change LocallyOfFiniteType (B.inclusion.map (B.inclusion.preimage f')) ∧
    QuasiCompact (B.inclusion.map (B.inclusion.preimage f'))
  rw [hpre]
  exact spec_finiteType_of_point A S iΛ hfinite hqc



/-- The underlying morphism of schemes of `specOverMap` is the spectrum of the given
morphism of `𝒞_Λ`. -/
private theorem specOverMap_left_map
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (hA : B.Contains (Spec (.of A))) (hA' : B.Contains (Spec (.of A')))
    (f : A ⟶ A') :
    B.inclusion.map (Over.Hom.left (specOverMap B S hS iΛ hA hA' f)) =
      Spec.map (CommRingCat.ofHom f.hom.toRingHom) := by
  let X := (specOver B S hS iΛ A hA).left
  let Y := (specOver B S hS iΛ A' hA').left
  let g : B.inclusion.obj Y ⟶ B.inclusion.obj X :=
    Spec.map (CommRingCat.ofHom f.hom.toRingHom)
  change B.inclusion.map (B.inclusion.preimage g) = g
  simpa using Functor.map_preimage B.inclusion g

/-- `specOverMap` turns a composite of morphisms of `𝒞_Λ` into the composite of the
corresponding site morphisms, in the reverse order. -/
private theorem specOverMap_comp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    {A A' A'' : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (hA : B.Contains (Spec (.of A))) (hA' : B.Contains (Spec (.of A')))
    (hA'' : B.Contains (Spec (.of A'')))
    (f : A ⟶ A') (g : A' ⟶ A'') :
    specOverMap B S hS iΛ hA' hA'' g ≫
      specOverMap B S hS iΛ hA hA' f =
      specOverMap B S hS iΛ hA hA'' (f ≫ g) := by
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  simp only [Over.comp_left, Functor.map_comp]
  rw [specOverMap_left_map B S hS iΛ hA' hA'' g,
    specOverMap_left_map B S hS iΛ hA hA' f,
    specOverMap_left_map B S hS iΛ hA hA'' (f ≫ g), ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rfl

/-- The closed point `Spec k ⟶ Spec A` of an object `A` of `𝒞_Λ`, read as a morphism of the
big fppf site over `S`. -/
private noncomputable def specOverResidueMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : B.Contains (Spec (.of A))) (hK : B.Contains (Spec (.of k))) :
    specOverField B S hS iΛ hK ⟶ specOver B S hS iΛ A hA := by
  let X := B.obj hA
  let K := B.obj hK
  let g : B.inclusion.obj K ⟶ B.inclusion.obj X :=
    Spec.map (CommRingCat.ofHom (residueMap A))
  refine Over.homMk (B.inclusion.preimage g) ?_
  apply B.inclusion.map_injective
  simp only [Functor.map_comp]
  have hpreG : (B.inclusion.preimage g).hom = g := by
    simpa using Functor.map_preimage B.inclusion g
  let fA : B.inclusion.obj X ⟶ B.inclusion.obj (B.obj hS) :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ
  let fK : B.inclusion.obj K ⟶ B.inclusion.obj (B.obj hS) :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ
  have hpreA : (B.inclusion.preimage fA).hom = fA := by
    simpa using Functor.map_preimage B.inclusion fA
  have hpreK : (B.inclusion.preimage fK).hom = fK := by
    simpa using Functor.map_preimage B.inclusion fK
  change (B.inclusion.preimage g).hom ≫
        (B.inclusion.preimage fA).hom = (B.inclusion.preimage fK).hom
  rw [hpreG, hpreA, hpreK]
  dsimp [g]
  rw [← Category.assoc, spec_residueMap_comp_algebraMap]

/-- The underlying morphism of schemes of `specOverResidueMap` is the spectrum of the
residue map of the algebra. -/
private theorem specOverResidueMap_left_map
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : B.Contains (Spec (.of A))) (hK : B.Contains (Spec (.of k))) :
    B.inclusion.map (Over.Hom.left
      (specOverResidueMap B S hS iΛ A hA hK)) =
        Spec.map (CommRingCat.ofHom (residueMap A)) := by
  let K := (specOverField B S hS iΛ hK).left
  let X := (specOver B S hS iΛ A hA).left
  let g : B.inclusion.obj K ⟶ B.inclusion.obj X :=
    Spec.map (CommRingCat.ofHom (residueMap A))
  have hg : B.inclusion.map (B.inclusion.preimage g) = g := by
    simpa using Functor.map_preimage B.inclusion g
  simpa [specOverResidueMap] using hg

/-- The closed points of the objects of `𝒞_Λ` are compatible with the site morphisms induced
by morphisms of `𝒞_Λ`. -/
private theorem specOverResidueMap_comp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (hA : B.Contains (Spec (.of A))) (hA' : B.Contains (Spec (.of A')))
    (hK : B.Contains (Spec (.of k))) (f : A ⟶ A') :
    specOverResidueMap B S hS iΛ A' hA' hK ≫
      specOverMap B S hS iΛ hA hA' f =
        specOverResidueMap B S hS iΛ A hA hK := by
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  simp only [Over.comp_left, Functor.map_comp]
  rw [specOverResidueMap_left_map, specOverMap_left_map,
    specOverResidueMap_left_map, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  change A'.residueEquiv
      (IsLocalRing.residue A' (f.hom a)) =
    A.residueEquiv (IsLocalRing.residue A a)
  exact f.residue_comm a

/-- The reversed arrow of a morphism of deformations lies over the site morphism attached to
its arrow of `𝒞_Λ`. -/
private theorem deformationMorphism_isHomLift
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {𝒳 : Type u₁} [Category.{v₁} 𝒳]
    (p : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (x₀ : 𝒳)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    {a b : DeformationObject iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀}
    (hA : B.Contains (Spec (.of a.algebra)))
    (hB : B.Contains (Spec (.of b.algebra)))
    (m : DeformationMorphism iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀ a b) :
    p.IsHomLift
      (specOverMap B S hS iΛ hA hB m.ringHom) m.arrow := by
  let af := deformationPointFiber B S hS p iΛ x₀ hx₀ a.algebra hA a rfl
  let bf := deformationPointFiber B S hS p iΛ x₀ hx₀ b.algebra hB b rfl
  change { z // p.obj z = specOver B S hS iΛ a.algebra hA } at af
  change { z // p.obj z = specOver B S hS iΛ b.algebra hB } at bf
  have haval : (af : 𝒳) = a.point := rfl
  have hbval : (bf : 𝒳) = b.point := rfl
  have hapoint : p.obj a.point = specOver B S hS iΛ a.algebra hA :=
    (congrArg p.obj haval).symm.trans af.property
  have hbpoint : p.obj b.point = specOver B S hS iΛ b.algebra hB :=
    (congrArg p.obj hbval).symm.trans bf.property
  have hapost :
      (congrArg (fun Y => (Over.post B.inclusion).obj Y) af.2).trans
          (specOver_post B S hS iΛ a.algebra hA) = a.base := by
    apply Subsingleton.elim
  have hbpost :
      (congrArg (fun Y => (Over.post B.inclusion).obj Y) bf.2).trans
          (specOver_post B S hS iΛ b.algebra hB) = b.base := by
    apply Subsingleton.elim
  have hapost_left := congrArg (congrArg Over.left) hapost
  have hbpost_left := congrArg (congrArg Over.left) hbpost
  apply IsHomLift.of_fac p (specOverMap B S hS iΛ hA hB m.ringHom)
    m.arrow hbpoint hapoint
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  rw [specOverMap_left_map B S hS iΛ hA hB m.ringHom]
  convert m.arrow_base.symm using 1
  case e'_1 => rfl
  case e'_3 =>
    rename_i htype
    cases htype
    cases hapost
    cases hbpost
    change _ = _ ≫ Over.Hom.left ((Over.post B.inclusion).map
      (p.map m.arrow)) ≫ _
    simp [Over.comp_left, Over.post]

/-- The arrow of a deformation lies over the closed point of the spectrum of its Artinian
local algebra. -/
private theorem deformationArrow_isHomLift
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {𝒳 : Type u₁} [Category.{v₁} 𝒳]
    (p : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (x₀ : 𝒳)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hK : B.Contains (Spec (.of k)))
    (d : DeformationObject iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (hA : B.Contains (Spec (.of d.algebra))) :
    p.IsHomLift (specOverResidueMap B S hS iΛ d.algebra hA hK) d.arrow := by
  let x0f := point_mem_specOverField B S hS p iΛ hK x₀ hx₀
  let df := deformationPointFiber B S hS p iΛ x₀ hx₀ d.algebra hA d rfl
  change { z // p.obj z = specOverField B S hS iΛ hK } at x0f
  change { z // p.obj z = specOver B S hS iΛ d.algebra hA } at df
  have hxval : (x0f : 𝒳) = x₀ := rfl
  have hdval : (df : 𝒳) = d.point := rfl
  have hxpoint : p.obj x₀ = specOverField B S hS iΛ hK :=
    (congrArg p.obj hxval).symm.trans x0f.property
  have hdpoint : p.obj d.point = specOver B S hS iΛ d.algebra hA :=
    (congrArg p.obj hdval).symm.trans df.property
  have hxpost :
      (congrArg (fun Y => (Over.post B.inclusion).obj Y) hxpoint).trans
          (specOverField_post B S hS iΛ hK) = hx₀ := by
    apply Subsingleton.elim
  have hdpost :
      (congrArg (fun Y => (Over.post B.inclusion).obj Y) hdpoint).trans
          (specOver_post B S hS iΛ d.algebra hA) = d.base := by
    apply Subsingleton.elim
  apply IsHomLift.of_fac p (specOverResidueMap B S hS iΛ d.algebra hA hK)
    d.arrow hxpoint hdpoint
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  rw [specOverResidueMap_left_map B S hS iΛ d.algebra hA hK]
  convert d.arrow_base.symm using 1
  case e'_1 => rfl
  case e'_3 =>
    rename_i htype
    cases htype
    cases hxpost
    cases hdpost
    simp [Over.comp_left, Over.post]

/-- A morphism of a predeformation category whose image in `𝒞_Λ` is surjective on underlying
rings has a surjective associated algebra map. -/
private theorem deformationMorphism_hom_surjective
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {𝒳 : Type u₁} [Category.{v₁} 𝒳]
    (iΛ : Spec (.of Λ) ⟶ S)
    (q : 𝒳 ⥤ Over S) (x₀ : 𝒳)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (D : PredeformationConstruction iΛ q x₀ hx₀) :
    letI : Category D.carrier := D.category
    ∀ {x y : D.carrier} (f : x ⟶ y),
      Function.Surjective (D.projection.map f).hom →
        Function.Surjective ((D.morphisms x y f).ringHom.hom) := by
  let : Category D.carrier := D.category
  intro x y f hf
  let e₁ := eqToHom (D.object_projection x).symm
  let e₂ := eqToHom (D.object_projection y)
  have hcast : e₁ ≫ D.projection.map f ≫ e₂ = (D.morphisms x y f).ringHom :=
    D.morphism_projection f
  have h₁ : Function.Surjective e₁.hom := surjective_hom_of_isIso e₁
  have h₂ : Function.Surjective e₂.hom := surjective_hom_of_isIso e₂
  rw [← congrArg (fun g => g.hom) hcast]
  simpa [e₁, e₂, RingHom.comp_apply, Function.comp_assoc] using
    h₂.comp (hf.comp h₁)

/-- The assertion that restriction to the two branches of the affine pushout square attached
to a fibre product in `𝒞_Λ` along a surjection is an equivalence onto the two-fibre product
of the fibres over the other three corners. -/
private abbrev PushoutFiberComparisonIsEquivalence
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {𝒳 : Type u₁} [Category.{v₁} 𝒳]
    (p : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hf₂ : Function.Surjective f₂.hom)
    (hA₁ : B.Contains (Spec (.of A₁)))
    (hA₂ : B.Contains (Spec (.of A₂)))
    (hA : B.Contains (Spec (.of A)))
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) : Prop :=
    let : p.IsFibered := hp.isFibered
    let P := ArtinianLocalAlgCat.pullbackObj_of_surjective
      f₁ f₂ (Or.inr hf₂)
    let hP := ArtinianLocalAlgCat.pullbackFst_of_surjective
      f₁ f₂ (Or.inr hf₂)
    let hQ := ArtinianLocalAlgCat.pullbackSnd_of_surjective
      f₁ f₂ (Or.inr hf₂)
    let hPsite := spec_mem_bigFppfSite B S hS iΛ P hfinite hqc
    (fiberSquareComparison p p.chosenPullbacks
      (specOverMap B S hS iΛ hA₁ hA f₁)
      (specOverMap B S hS iΛ hA₂ hA f₂)
      (specOverMap B S hS iΛ hPsite hA₁ hP)
      (specOverMap B S hS iΛ hPsite hA₂ hQ)
      (by
        have hpb :=
          ArtinianLocalAlgCat.isPullback_of_surjective
            f₁ f₂ (Or.inr hf₂)
        rw [specOverMap_comp B S hS iΛ hPsite hA₂ hA hQ f₂,
          specOverMap_comp B S hS iΛ hPsite hA₁ hA hP f₁]
        exact congrArg (fun q => specOverMap B S hS iΛ hPsite hA q) hpb.w)).IsEquivalence

/-- A morphism of `𝒞_Λ` induces a surjection on residue fields, read on global sections of the
spectra: every section of `Spec A` agrees with the image of a section of `Spec A₁` up to a
non-unit. -/
private theorem specMap_residue_surjective {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {A₁ A : ArtinianLocalAlgCat.{u, u, u} Λ k} (f₁ : A₁ ⟶ A)
    (a : Γ(Spec (.of A), ⊤)) :
    ∃ b : Γ(Spec (.of A₁), ⊤),
      a - (Spec.map (CommRingCat.ofHom f₁.hom.toRingHom)).appTop.hom b ∈
        nonunits Γ(Spec (.of A), ⊤) := by
  let eA := (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv
  let eA₁ := (Scheme.ΓSpecIso (.of A₁)).commRingCatIsoToRingEquiv
  obtain ⟨b₀, hb₀⟩ := (A₁.residueEquiv.surjective.comp (IsLocalRing.residue_surjective (R := A₁)))
    (A.residueEquiv (IsLocalRing.residue A (eA a)))
  refine ⟨eA₁.symm b₀, ?_⟩
  have hnat : (Spec.map (CommRingCat.ofHom f₁.hom.toRingHom)).appTop.hom (eA₁.symm b₀) =
      eA.symm (f₁.hom b₀) := by
    have h := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (.of A₁)).inv.hom b₀))
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f₁.hom.toRingHom))
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply,
      ← CommRingCat.comp_apply (Scheme.ΓSpecIso (.of A₁)).inv (Scheme.ΓSpecIso (.of A₁)).hom,
      Iso.inv_hom_id, CommRingCat.id_apply] at h
    apply eA.injective
    rw [RingEquiv.apply_symm_apply]
    exact h
  rw [hnat]
  have hmem : eA a - f₁.hom b₀ ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    apply A.residueEquiv.injective
    rw [f₁.residue_comm]
    simpa using hb₀.symm
  have : a - eA.symm (f₁.hom b₀) = eA.symm (eA a - f₁.hom b₀) := by
    rw [map_sub, RingEquiv.symm_apply_apply]
  rw [this]
  exact fun hu => hmem (by simpa using hu.map eA.toRingHom)

/-- Condition (RS) at the squares inducing surjections of residue fields applied to the square
of spectra coming from a fibre product in `𝒞_Λ` along a surjection. -/
private theorem specArtinianPushoutComparison_isEquivalence_of_residue
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {𝒳 : Type u₁} [Category.{v₁} 𝒳]
    (p : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSOfResidue B S hS p hp)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hf₂ : Function.Surjective f₂.hom)
    (hA₁ : B.Contains (Spec (.of A₁)))
    (hA₂ : B.Contains (Spec (.of A₂)))
    (hA : B.Contains (Spec (.of A)))
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    PushoutFiberComparisonIsEquivalence B S hS p hp iΛ f₁ f₂ hf₂ hA₁ hA₂ hA
      hfinite hqc := by
  dsimp only [PushoutFiberComparisonIsEquivalence]
  let P := ArtinianLocalAlgCat.pullbackObj_of_surjective
    f₁ f₂ (Or.inr hf₂)
  let hPsite := spec_mem_bigFppfSite B S hS iΛ P hfinite hqc
  let hP := ArtinianLocalAlgCat.pullbackFst_of_surjective
    f₁ f₂ (Or.inr hf₂)
  let hQ := ArtinianLocalAlgCat.pullbackSnd_of_surjective
    f₁ f₂ (Or.inr hf₂)
  have : p.IsFibered := hp.isFibered
  apply hRS
    (specOverMap B S hS iΛ hA₂ hA f₂)
    (specOverMap B S hS iΛ hA₁ hA f₁)
    (specOverMap B S hS iΛ hPsite hA₂ hQ)
    (specOverMap B S hS iΛ hPsite hA₁ hP)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [specOverMap_comp B S hS iΛ hPsite hA₂ hA hQ f₂,
      specOverMap_comp B S hS iΛ hPsite hA₁ hA hP f₁]
    have hpb :=
      ArtinianLocalAlgCat.isPullback_of_surjective
        f₁ f₂ (Or.inr hf₂)
    exact congrArg (fun q => specOverMap B S hS iΛ hPsite hA q) hpb.w.symm
  · exact specOver_isArtinianLocal B S hS iΛ A hA
  · exact specOver_isArtinianLocal B S hS iΛ A₂ hA₂
  · exact specOver_isArtinianLocal B S hS iΛ A₁ hA₁
  · exact specOver_isArtinianLocal B S hS iΛ P hPsite
  · exact specOver_isFiniteTypeOver B S hS iΛ A hA hfinite hqc
  · exact specOver_isFiniteTypeOver B S hS iΛ A₂ hA₂ hfinite hqc
  · exact specOver_isFiniteTypeOver B S hS iΛ A₁ hA₁ hfinite hqc
  · exact specOver_isFiniteTypeOver B S hS iΛ P hPsite hfinite hqc
  · change IsClosedImmersion
      (B.inclusion.map (Over.Hom.left
        (specOverMap B S hS iΛ hA₂ hA f₂)))
    rw [specOverMap_left_map B S hS iΛ hA₂ hA f₂]
    exact specMap_isClosedImmersion_of_surjective f₂ hf₂
  · change IsPushout
      (B.inclusion.map (Over.Hom.left
        (specOverMap B S hS iΛ hA₂ hA f₂)))
      (B.inclusion.map (Over.Hom.left
        (specOverMap B S hS iΛ hA₁ hA f₁)))
      (B.inclusion.map (Over.Hom.left
        (specOverMap B S hS iΛ hPsite hA₂ hQ)))
      (B.inclusion.map (Over.Hom.left
        (specOverMap B S hS iΛ hPsite hA₁ hP)))
    rw [specOverMap_left_map B S hS iΛ hA₂ hA f₂,
      specOverMap_left_map B S hS iΛ hA₁ hA f₁,
      specOverMap_left_map B S hS iΛ hPsite hA₂ hQ,
      specOverMap_left_map B S hS iΛ hPsite hA₁ hP]
    exact specPullback_isPushout f₁ f₂ hf₂
  · intro a
    have h := specMap_residue_surjective f₁ a
    rwa [← specOverMap_left_map B S hS iΛ hA₁ hA f₁] at h


/-- For the square of spectra attached to a fibre product in `𝒞_Λ` along a surjection, the
induced square of rings of global sections is again a fibre product. -/
private theorem specOverAffine_isPullback_appTop
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hf₂ : Function.Surjective f₂.hom) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (ArtinianLocalAlgCat.pullbackFst_of_surjective f₁ f₂ (Or.inr hf₂)).hom.toRingHom)).appTop
      (Spec.map (CommRingCat.ofHom
        (ArtinianLocalAlgCat.pullbackSnd_of_surjective f₁ f₂ (Or.inr hf₂)).hom.toRingHom)).appTop
      (Spec.map (CommRingCat.ofHom f₁.hom.toRingHom)).appTop
      (Spec.map (CommRingCat.ofHom f₂.hom.toRingHom)).appTop := by
  apply (specPullback_isPullback f₁ f₂ hf₂).of_iso'
    (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _)
  all_goals exact (Scheme.ΓSpecIso_naturality _).symm

/-- Condition (RS*) applied to the square of spectra coming from a fibre product in `𝒞_Λ`
along a surjection with square-zero kernel: that square lies in the big affine fppf site and
is a fibre product on rings of global sections, so the comparison of fibres is an
equivalence. -/
private theorem specSquareZeroComparison_isEquivalence
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {𝒳 : Type u₁} [Category.{v₁} 𝒳]
    (p : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hf₂ : Function.Surjective f₂.hom)
    (hker : RingHom.ker (CommRingCat.ofHom f₂.hom.toRingHom).hom ^ 2 = ⊥)
    (hA₁ : B.Contains (Spec (.of A₁)))
    (hA₂ : B.Contains (Spec (.of A₂)))
    (hA : B.Contains (Spec (.of A)))
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    PushoutFiberComparisonIsEquivalence B S hS p hp iΛ f₁ f₂ hf₂ hA₁ hA₂ hA
      hfinite hqc := by
  dsimp only [PushoutFiberComparisonIsEquivalence]
  have : p.IsFibered := hp.isFibered
  let P := ArtinianLocalAlgCat.pullbackObj_of_surjective f₁ f₂ (Or.inr hf₂)
  let hPsite := spec_mem_bigFppfSite B S hS iΛ P hfinite hqc
  let hP := ArtinianLocalAlgCat.pullbackFst_of_surjective f₁ f₂ (Or.inr hf₂)
  let hQ := ArtinianLocalAlgCat.pullbackSnd_of_surjective f₁ f₂ (Or.inr hf₂)
  let U : BigAffineFppf B S hS :=
    ⟨specOver B S hS iΛ A hA, (specOver_isArtinianLocal B S hS iΛ A hA).1⟩
  let V : BigAffineFppf B S hS :=
    ⟨specOver B S hS iΛ A₁ hA₁, (specOver_isArtinianLocal B S hS iΛ A₁ hA₁).1⟩
  let W : BigAffineFppf B S hS :=
    ⟨specOver B S hS iΛ A₂ hA₂, (specOver_isArtinianLocal B S hS iΛ A₂ hA₂).1⟩
  let Z : BigAffineFppf B S hS :=
    ⟨specOver B S hS iΛ P hPsite, (specOver_isArtinianLocal B S hS iΛ P hPsite).1⟩
  let f : U ⟶ V := ObjectProperty.homMk (specOverMap B S hS iΛ hA₁ hA f₁)
  let g : U ⟶ W := ObjectProperty.homMk (specOverMap B S hS iΛ hA₂ hA f₂)
  let i : V ⟶ Z := ObjectProperty.homMk (specOverMap B S hS iΛ hPsite hA₁ hP)
  let j : W ⟶ Z := ObjectProperty.homMk (specOverMap B S hS iΛ hPsite hA₂ hQ)
  have h : f ≫ i = g ≫ j := by
    apply ObjectProperty.hom_ext
    change specOverMap B S hS iΛ hA₁ hA f₁ ≫ specOverMap B S hS iΛ hPsite hA₁ hP =
      specOverMap B S hS iΛ hA₂ hA f₂ ≫ specOverMap B S hS iΛ hPsite hA₂ hQ
    rw [specOverMap_comp B S hS iΛ hPsite hA₁ hA hP f₁,
      specOverMap_comp B S hS iΛ hPsite hA₂ hA hQ f₂]
    exact congrArg (fun q => specOverMap B S hS iΛ hPsite hA q)
      (ArtinianLocalAlgCat.isPullback_of_surjective f₁ f₂ (Or.inr hf₂)).w
  have hmapf : (BigAffineFppf.toScheme B S hS).map f =
      Spec.map (CommRingCat.ofHom f₁.hom.toRingHom) :=
    specOverMap_left_map B S hS iΛ hA₁ hA f₁
  have hmapg : (BigAffineFppf.toScheme B S hS).map g =
      Spec.map (CommRingCat.ofHom f₂.hom.toRingHom) :=
    specOverMap_left_map B S hS iΛ hA₂ hA f₂
  have hmapi : (BigAffineFppf.toScheme B S hS).map i =
      Spec.map (CommRingCat.ofHom hP.hom.toRingHom) :=
    specOverMap_left_map B S hS iΛ hPsite hA₁ hP
  have hmapj : (BigAffineFppf.toScheme B S hS).map j =
      Spec.map (CommRingCat.ofHom hQ.hom.toRingHom) :=
    specOverMap_left_map B S hS iΛ hPsite hA₂ hQ
  have hpb : IsPullback ((BigAffineFppf.toScheme B S hS).map i).appTop
      ((BigAffineFppf.toScheme B S hS).map j).appTop
      ((BigAffineFppf.toScheme B S hS).map f).appTop
      ((BigAffineFppf.toScheme B S hS).map g).appTop := by
    rw [hmapf, hmapg, hmapi, hmapj]
    exact specOverAffine_isPullback_appTop f₁ f₂ hf₂
  have hsurj : Function.Surjective
      ((BigAffineFppf.toScheme B S hS).map g).appTop.hom := by
    rw [hmapg]
    exact specMap_appTop_surjective _ hf₂
  have hsqz : RingHom.ker
      ((BigAffineFppf.toScheme B S hS).map g).appTop.hom ^ 2 = ⊥ := by
    rw [hmapg]
    exact Stacks.Smooth.ker_specMap_appTop_pow_eq_bot _ hker
  exact hRS U V W Z f g i j h hpb hsurj hsqz

attribute [local implicit_reducible] Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
  CategoricalPullback.π₁ CategoricalPullback.π₂

attribute [local implicit_reducible] deformationPointFiber

/-- The fibre product of two deformations along a surjection, granted that the comparison of
fibres attached to the corresponding square of spectra is an equivalence. This is the common
core of the two deformation-category criteria below. -/
private theorem exists_pullbackCone_of_comparison
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type u₁} [Category.{v₁} 𝒳]
    (p : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : 𝒳)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (D : PredeformationConstruction iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (Q : ∀ {A₂ A : ArtinianLocalAlgCat.{u, u, u} Λ k}, (A₂ ⟶ A) → Prop)
    (hcomp : ∀ {A₁ A₂ A : ArtinianLocalAlgCat.{u, u, u} Λ k} (g₁ : A₁ ⟶ A) (g₂ : A₂ ⟶ A)
      (hg₂ : Function.Surjective g₂.hom), Q g₂ →
      ∀ (hA₁ : B.Contains (Spec (.of A₁))) (hA₂ : B.Contains (Spec (.of A₂)))
        (hA : B.Contains (Spec (.of A))),
        PushoutFiberComparisonIsEquivalence B S hS p hp iΛ g₁ g₂ hg₂ hA₁ hA₂ hA
          hfinite hqc) :
    letI := D.category
    ∀ {x₁ x₂ x : D.carrier} (f₁ : x₁ ⟶ x) (f₂ : x₂ ⟶ x),
      Function.Surjective (D.projection.map f₂).hom →
      Q (D.morphisms x₂ x f₂).ringHom →
      ∃ c : CategoryTheory.Limits.PullbackCone f₁ f₂,
        Nonempty (IsLimit c) ∧ Nonempty (IsLimit (c.map D.projection)) := by
  let := D.category
  intro x₁ x₂ x f₁ f₂ hf₂ hQg
  have : p.IsFibered := hp.isFibered
  let c := p.chosenPullbacks
  let d₁ := D.objects x₁
  let d₂ := D.objects x₂
  let d := D.objects x
  let m₁ := D.morphisms x₁ x f₁
  let m₂ := D.morphisms x₂ x f₂
  have hf₂' : Function.Surjective m₂.ringHom.hom :=
    deformationMorphism_hom_surjective iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀ D f₂ hf₂
  let P := ArtinianLocalAlgCat.pullbackObj_of_surjective
    m₁.ringHom m₂.ringHom (Or.inr hf₂')
  let hP := ArtinianLocalAlgCat.pullbackFst_of_surjective
    m₁.ringHom m₂.ringHom (Or.inr hf₂')
  let hQ := ArtinianLocalAlgCat.pullbackSnd_of_surjective
    m₁.ringHom m₂.ringHom (Or.inr hf₂')
  have hpb : IsPullback hP hQ m₁.ringHom m₂.ringHom :=
    ArtinianLocalAlgCat.isPullback_of_surjective _ _ _
  let hA₁ := spec_mem_bigFppfSite B S hS iΛ d₁.algebra hfinite hqc
  let hA₂ := spec_mem_bigFppfSite B S hS iΛ d₂.algebra hfinite hqc
  let hA := spec_mem_bigFppfSite B S hS iΛ d.algebra hfinite hqc
  let hPsite := spec_mem_bigFppfSite B S hS iΛ P hfinite hqc
  have hK : B.Contains (Spec (.of k)) := by
    let := hfinite
    let := hqc
    exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hS
  let a₁ := specOverMap B S hS iΛ hA₁ hA m₁.ringHom
  let a₂ := specOverMap B S hS iΛ hA₂ hA m₂.ringHom
  let p₁ := specOverMap B S hS iΛ hPsite hA₁ hP
  let p₂ := specOverMap B S hS iΛ hPsite hA₂ hQ
  have hsq : a₁ ≫ p₁ = a₂ ≫ p₂ := by
    rw [specOverMap_comp B S hS iΛ hPsite hA₁ hA hP m₁.ringHom,
      specOverMap_comp B S hS iΛ hPsite hA₂ hA hQ m₂.ringHom]
    exact congrArg (specOverMap B S hS iΛ hPsite hA) hpb.w
  let E := fiberSquareComparison p c a₁ a₂ p₁ p₂ hsq
  have : E.IsEquivalence := hcomp m₁.ringHom m₂.ringHom hf₂' hQg hA₁ hA₂ hA
  let d₁f := deformationPointFiber B S hS p iΛ x₀ hx₀ d₁.algebra hA₁ d₁ rfl
  let d₂f := deformationPointFiber B S hS p iΛ x₀ hx₀ d₂.algebra hA₂ d₂ rfl
  let df := deformationPointFiber B S hS p iΛ x₀ hx₀ d.algebra hA d rfl
  have : p.IsHomLift a₁ m₁.arrow :=
    deformationMorphism_isHomLift B S hS p iΛ x₀ hx₀ hA₁ hA m₁
  have : p.IsHomLift a₂ m₂.arrow :=
    deformationMorphism_isHomLift B S hS p iΛ x₀ hx₀ hA₂ hA m₂
  have : p.IsStronglyCartesian a₁ m₁.arrow := hp.isStronglyCartesian_homLift _ _
  have : p.IsStronglyCartesian a₂ m₂.arrow := hp.isStronglyCartesian_homLift _ _
  let e₁ : df ≅ c.obj a₁ d₁f := Functor.fiberIsoOfCartesian a₁ m₁.arrow
    (c.map a₁ d₁f)
    (Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian p a₁ m₁.arrow)
    (Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian p a₁ (c.map a₁ d₁f))
  let e₂ : df ≅ c.obj a₂ d₂f := Functor.fiberIsoOfCartesian a₂ m₂.arrow
    (c.map a₂ d₂f)
    (Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian p a₂ m₂.arrow)
    (Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian p a₂ (c.map a₂ d₂f))
  have he₁ : e₁.hom.1 ≫ c.map a₁ d₁f = m₁.arrow :=
    Functor.fiberIsoOfCartesian_hom_fac (p := p) (z := df) (z' := c.obj a₁ d₁f)
      a₁ m₁.arrow (c.map a₁ d₁f)
      (Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian p a₁ m₁.arrow)
      (Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian p a₁ (c.map a₁ d₁f))
  have he₂ : e₂.hom.1 ≫ c.map a₂ d₂f = m₂.arrow :=
    Functor.fiberIsoOfCartesian_hom_fac (p := p) (z := df) (z' := c.obj a₂ d₂f)
      a₂ m₂.arrow (c.map a₂ d₂f)
      (Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian p a₂ m₂.arrow)
      (Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian p a₂ (c.map a₂ d₂f))
  let pair : CategoricalPullback (c.pullbackFunctor a₁) (c.pullbackFunctor a₂) :=
    ⟨d₁f, d₂f, e₁.symm ≪≫ e₂⟩
  obtain ⟨src, ⟨bi⟩⟩ := Functor.EssSurj.mem_essImage E pair
  let arrow₁ := bi.inv.fst.1 ≫ c.map p₁ src
  let arrow₂ := bi.inv.snd.1 ≫ c.map p₂ src
  have : p.IsHomLift (𝟙 _) bi.inv.fst.1 := bi.inv.fst.2
  have : p.IsHomLift (𝟙 _) bi.inv.snd.1 := bi.inv.snd.2
  have : p.IsHomLift p₁ arrow₁ := IsHomLift.comp_lift_id_left' p
    (specOver B S hS iΛ d₁.algebra hA₁)
    bi.inv.fst.1 p₁ (c.map p₁ src)
  have : p.IsHomLift p₂ arrow₂ := IsHomLift.comp_lift_id_left' p
    (specOver B S hS iΛ d₂.algebra hA₂)
    bi.inv.snd.1 p₂ (c.map p₂ src)
  have hepair : e₁.hom.1 ≫ pair.iso.hom.1 = e₂.hom.1 := by
    have hh : e₁.hom ≫ pair.iso.hom = e₂.hom := by simp [pair]
    simpa only [fiber_comp] using congrArg (fun z => z.1) hh
  have pair_condition (t : 𝒳) (a : d₁.point ⟶ t) (b : d₂.point ⟶ t)
      (hab : m₁.arrow ≫ a = m₂.arrow ≫ b) :
      c.map a₁ d₁f ≫ a = pair.iso.hom.1 ≫ c.map a₂ d₂f ≫ b := by
    apply (cancel_epi (Functor.Fiber.fiberInclusion.map e₁.hom)).1
    change e₁.hom.1 ≫ _ = e₁.hom.1 ≫ _
    simpa only [← Category.assoc, he₁, hepair, he₂] using hab
  have hcomm : m₁.arrow ≫ arrow₁ = m₂.arrow ≫ arrow₂ := by
    have hh := pair_map_condition c a₁ a₂ bi.inv (c.map p₁ src) (c.map p₂ src)
      (square_fac_val p c a₁ a₂ p₁ p₂ hsq src).symm
    have hh' := congrArg (fun z => e₁.hom.1 ≫ z) hh
    change e₁.hom.1 ≫ c.map a₁ d₁f ≫ bi.inv.fst.1 ≫ c.map p₁ src =
      e₁.hom.1 ≫ pair.iso.hom.1 ≫ c.map a₂ d₂f ≫ bi.inv.snd.1 ≫ c.map p₂ src at hh'
    simp only [← Category.assoc, he₁, hepair, he₂] at hh'
    simpa only [arrow₁, arrow₂, Category.assoc] using hh'
  let rP := specOverResidueMap B S hS iΛ P hPsite hK
  let r₁ := specOverResidueMap B S hS iΛ d₁.algebra hA₁ hK
  have : p.IsHomLift r₁ d₁.arrow :=
    deformationArrow_isHomLift B S hS p iΛ x₀ hx₀ hK d₁ hA₁
  have : p.IsHomLift rP (d₁.arrow ≫ arrow₁) := by
    dsimp only [rP]
    rw [← specOverResidueMap_comp B S hS iΛ hPsite hA₁ hK hP]
    exact IsHomLift.comp p r₁ p₁ d₁.arrow arrow₁
  let srcBase : (p ⋙ Over.post B.inclusion).obj src.1 =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ P)) ≫ iΛ) :=
    (congrArg (Over.post B.inclusion).obj src.2).trans
      (specOver_post B S hS iΛ P hPsite)
  let z : DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀ := {
    algebra := P
    point := src.1
    arrow := d₁.arrow ≫ arrow₁
    base := srcBase
    arrow_base := (map_lift_fac p (Over.post B.inclusion ⋙ Over.forget S)
      rP (d₁.arrow ≫ arrow₁)
      (by
        have hh := congrArg Over.left hx₀
        exact hh)
      (by
        have hh := congrArg Over.left srcBase
        exact hh)).trans
        (specOverResidueMap_left_map B S hS iΛ P hPsite hK) }
  let g₁ : DeformationMorphism iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀ z d₁ := {
    ringHom := hP
    arrow := arrow₁
    triangle := rfl
    arrow_base := (map_lift_fac p (Over.post B.inclusion ⋙ Over.forget S)
      p₁ arrow₁
      (by
        have hh := congrArg Over.left d₁.base
        exact hh)
      (by
        have hh := congrArg Over.left srcBase
        exact hh)).trans
        (specOverMap_left_map B S hS iΛ hPsite hA₁ hP) }
  let g₂ : DeformationMorphism iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀ z d₂ := {
    ringHom := hQ
    arrow := arrow₂
    triangle := by
      change d₂.arrow ≫ arrow₂ = d₁.arrow ≫ arrow₁
      rw [← m₁.triangle, ← m₂.triangle, Category.assoc, Category.assoc, hcomm]
    arrow_base := (map_lift_fac p (Over.post B.inclusion ⋙ Over.forget S)
      p₂ arrow₂
      (by
        have hh := congrArg Over.left d₂.base
        exact hh)
      (by
        have hh := congrArg Over.left srcBase
        exact hh)).trans
        (specOverMap_left_map B S hS iΛ hPsite hA₂ hQ) }
  apply deformationCone_isPullback D f₁ f₂ z g₁ g₂ hpb hcomm
  intro t a b hrab hab
  let hT := spec_mem_bigFppfSite B S hS iΛ t.algebra hfinite hqc
  let tf := deformationPointFiber B S hS p iΛ x₀ hx₀ t.algebra hT t rfl
  let lring := hpb.lift a.ringHom b.ringHom hrab
  have hli : lring ≫ hP = a.ringHom := hpb.lift_fst _ _ _
  have hlj : lring ≫ hQ = b.ringHom := hpb.lift_snd _ _ _
  let r := specOverMap B S hS iΛ hT hPsite lring
  have hi : p₁ ≫ r = specOverMap B S hS iΛ hT hA₁ a.ringHom := by
    rw [specOverMap_comp B S hS iΛ hT hPsite hA₁ lring hP, hli]
  have hj : p₂ ≫ r = specOverMap B S hS iΛ hT hA₂ b.ringHom := by
    rw [specOverMap_comp B S hS iΛ hT hPsite hA₂ lring hQ, hlj]
  have : p.IsHomLift (p₁ ≫ r) a.arrow := by
    rw [hi]
    exact deformationMorphism_isHomLift B S hS p iΛ x₀ hx₀ hT hA₁ a
  have : p.IsHomLift (p₂ ≫ r) b.arrow := by
    rw [hj]
    exact deformationMorphism_isHomLift B S hS p iΛ x₀ hx₀ hT hA₂ b
  obtain ⟨l, hl, hu⟩ := pair_lift p c a₁ a₂ p₁ p₂ hsq src pair bi tf r
    a.arrow b.arrow (pair_condition t.point a.arrow b.arrow hab)
  let := hl.1
  let lm : DeformationMorphism iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀ t z := {
    ringHom := lring
    arrow := l
    triangle := by
      change (d₁.arrow ≫ arrow₁) ≫ l = t.arrow
      rw [Category.assoc, hl.2.1]
      exact a.triangle
    arrow_base := (map_lift_fac p (Over.post B.inclusion ⋙ Over.forget S)
      r l
      (by
        have hh := congrArg Over.left srcBase
        exact hh)
      (by
        have hh := congrArg Over.left t.base
        exact hh)).trans
        (specOverMap_left_map B S hS iΛ hT hPsite lring) }
  refine ⟨lm, ⟨⟨hli, hl.2.1⟩, ⟨hlj, hl.2.2⟩⟩, ?_⟩
  intro lm' hm
  have hring : lm'.ringHom = lring := hpb.hom_ext
    (hm.1.1.trans hli.symm) (hm.2.1.trans hlj.symm)
  apply DeformationMorphism.ext_of_components (hr := hring)
  apply hu
  refine ⟨?_, hm.1.2, hm.2.2⟩
  have hm' := deformationMorphism_isHomLift B S hS p iΛ x₀ hx₀
    (a := t) (b := z) hT hPsite lm'
  change p.IsHomLift (specOverMap B S hS iΛ hT hPsite lring) lm'.arrow
  rw [← hring]
  exact hm'

/-- **Stacks Project, Tag 07WU.** The predeformation category of a
finite-type field-valued point in a fibred category satisfying (RS) is a
deformation category. -/
@[stacks 07WU]
public theorem isDeformationCategory_predeformationCategory
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type u₁} [Category.{v₁} 𝒳]
    (p : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRS B S hS p hp)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : 𝒳)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    let D := predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀
    letI := D.category
    Deformation.IsDeformationCategory D.projection := by
  let D := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
  let := D.category
  have hpre := predeformationCategory_isPredeformationCategory
    B hS iΛ p x₀ hx₀ hp
  refine ⟨hpre, hpre.cofibered, ?_⟩
  intro x₁ x₂ x f₁ f₂ hf₂
  exact exists_pullbackCone_of_comparison B S hS p hp iΛ x₀ hx₀ hfinite hqc D
    (fun _ => True)
    (fun g₁ g₂ hg₂ _ hA₁ hA₂ hA =>
      specArtinianPushoutComparison_isEquivalence_of_residue B S hS p hp
        (satisfiesRSOfResidue_of_satisfiesRS B S hS p hp hRS) iΛ g₁ g₂ hg₂
        hA₁ hA₂ hA hfinite hqc)
    f₁ f₂ hf₂ trivial

/-- **Stacks Project, Tag 07Y8.** The predeformation category of a finite-type field-valued
point in a fibred category satisfying (RS*) is a deformation category; only the square-zero
squares that (RS*) quantifies over are needed. -/
@[stacks 07Y8 "condition (RS*) gives a deformation category"]
public theorem isDeformationCategory_predeformationCategory_of_satisfiesRSStar
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type u₁} [Category.{v₁} 𝒳]
    (p : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : 𝒳)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    let D := predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀
    letI := D.category
    Deformation.IsDeformationCategory D.projection := by
  let D := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
  let := D.category
  have hpre := predeformationCategory_isPredeformationCategory
    B hS iΛ p x₀ hx₀ hp
  refine ⟨hpre, Deformation.satisfiesRS_of_small_extensions hpre.cofibered ?_⟩
  intro x₁ x₂ x f₁ f₂ hsmall
  obtain ⟨-, -, hsurj, hker⟩ :=
    InfinitesimalLifting.IsSmallExtension.isSquareZeroSurjection _ hsmall
  refine exists_pullbackCone_of_comparison B S hS p hp iΛ x₀ hx₀ hfinite hqc D
    (fun g₂ => RingHom.ker (CommRingCat.ofHom g₂.hom.toRingHom).hom ^ 2 = ⊥)
    (fun g₁ g₂ hg₂ hg hA₁ hA₂ hA =>
      specSquareZeroComparison_isEquivalence B S hS p hp hRS iΛ g₁ g₂ hg₂ hg
        hA₁ hA₂ hA hfinite hqc)
    f₁ f₂ hsurj ?_
  exact hker

/-- **The predeformation category of a finite-type field-valued point is a deformation category
as soon as (RS) holds at the squares inducing surjections of residue fields.** This is
`Deformation.Artin.isDeformationCategory_predeformationCategory` (Tag 07WU) under the weaker
hypothesis that is all its proof uses: the squares of spectra it meets come from fibre products
in `𝒞_Λ`, all of whose residue fields are identified with `k`. -/
public theorem isDeformationCategory_predeformationCategory_of_satisfiesRSOfResidue
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type u₁} [Category.{v₁} 𝒳]
    (p : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSOfResidue B S hS p hp)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : 𝒳)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    let D := predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀
    letI := D.category
    Deformation.IsDeformationCategory D.projection := by
  let D := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
  let := D.category
  have hpre := predeformationCategory_isPredeformationCategory
    B hS iΛ p x₀ hx₀ hp
  refine ⟨hpre, hpre.cofibered, ?_⟩
  intro x₁ x₂ x f₁ f₂ hf₂
  exact exists_pullbackCone_of_comparison B S hS p hp iΛ x₀ hx₀ hfinite hqc D
    (fun _ => True)
    (fun g₁ g₂ hg₂ _ hA₁ hA₂ hA =>
      specArtinianPushoutComparison_isEquivalence_of_residue B S hS p hp hRS iΛ g₁ g₂ hg₂
        hA₁ hA₂ hA hfinite hqc)
    f₁ f₂ hf₂ trivial

end Deformation.Artin
