module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisDescentSheaf.Basic
import all StacksFrontier.AlgebraicGeometry.FundamentalGroup.SchemesEtalePoint.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Galois action on the fibres of a geometric point

Let `s` be a geometric point of a scheme `S`, with algebraically closed field `Ω` and image
`x`, and let `L` be the separable closure of the residue field `κ(x)` inside `Ω`.  Then `s`
factors through `Spec L`, and for `S` the spectrum of a field the lifts of `s` to an object of
the small étale site are exactly the lifts of that factorization: an object of the small étale
site of a field is a disjoint union of spectra of finite separable extensions, a lift of `s`
lands in one piece, and the resulting embedding of a finite separable extension has separable
image, hence takes values in `L`.  Consequently the absolute Galois group `Gal(L/κ(x))` acts on
the lifts of `s`, naturally in the object of the site, by precomposing the factorization with
the corresponding automorphism of `L`.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.sepClosureOver` — the spectrum of the separable closure at
  a geometric point, as a scheme over the base.
* `AlgebraicGeometry.sepClosureFiber` — the lifts of that point over the small étale site, with
  `AlgebraicGeometry.sepClosureFiberSmul` the Galois action on them by precomposition.
* `AlgebraicGeometry.sepClosureFiberToGeometricPointFiber` — comparison with the lifts of the
  geometric point itself, and `AlgebraicGeometry.geometricPointFiberSepClosureEquiv` the
  resulting bijection over a field.
* `AlgebraicGeometry.galoisFiberAction` — the action of the absolute Galois group on the lifts
  of a geometric point of the spectrum of a field, with
  `AlgebraicGeometry.geometricPointFiberMulAction` the corresponding `MulAction`.
* `AlgebraicGeometry.galoisGeometricPointFiberHomSheaf` — the sheaf of Galois-equivariant maps
  out of those lifts attached to a continuous Galois set.

## Main results

* `AlgebraicGeometry.GeometricPoint.specMap_algebraMap_comp_sepClosureOver` — a geometric point
  factors through the spectrum of the separable closure of the residue field at its image.
* `AlgebraicGeometry.bijective_sepClosureFiberToGeometricPointFiber` — over a field, the lifts
  of a geometric point are the lifts of its separable-closure point.
* `AlgebraicGeometry.coe_galoisFiberAction_of_extends` — the action is precomposition with any
  endomorphism of the algebraically closed field extending the Galois automorphism.
* `AlgebraicGeometry.galoisFiberAction_one`, `AlgebraicGeometry.galoisFiberAction_mul` and
  `AlgebraicGeometry.galoisFiberAction_naturality` — it is a group action, natural in the
  object of the site.
* `AlgebraicGeometry.isSheaf_galoisFiberActionEquivariantFiberHomPresheaf` — the presheaf of
  Galois-equivariant maps out of those lifts into a continuous Galois set is a sheaf.

## References

* [Stacks Project, Tag 03QT](https://stacks.math.columbia.edu/tag/03QT)
* [Stacks Project, Tag 03QX](https://stacks.math.columbia.edu/tag/03QX)
* [Stacks Project, Tag 03PC](https://stacks.math.columbia.edu/tag/03PC)
* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

attribute [local instance] GeometricPoint.residueFieldAlgebra

namespace GeometricPoint

variable {S : Scheme.{u}} (s : GeometricPoint S)

/-- A geometric point factors through the spectrum of the residue field at its image, along
the canonical embedding of that residue field into the algebraically closed field of the
point. -/
theorem specMap_residueFieldHom_comp_fromSpecResidueField :
    Spec.map (CommRingCat.ofHom (residueFieldHom s)) ≫
      S.fromSpecResidueField (s.hom default) = s.hom := by
  have hcongr : s.hom default = s.hom (IsLocalRing.closedPoint s.residueField) :=
    congrArg s.hom (Subsingleton.elim _ _)
  have h1 : CommRingCat.ofHom (residueFieldHom s) =
      (S.residueFieldCongr hcongr).hom ≫
        S.descResidueField (Scheme.stalkClosedPointTo s.hom) := rfl
  rw [h1, Spec.map_comp, Category.assoc,
    Scheme.residueFieldCongr_fromSpecResidueField hcongr,
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField]

/-- The spectrum of the separable closure of the residue field at the image of a geometric
point, as a scheme over the base. -/
@[sga "4 VIII 3.1", sga "7 XIII 0.2"]
def sepClosureOver : Spec (.of ↥(separableClosure s)) ⟶ S :=
  Spec.map (CommRingCat.ofHom
      (algebraMap (S.residueField (s.hom default)) ↥(separableClosure s))) ≫
    S.fromSpecResidueField (s.hom default)

/-- A geometric point factors through the spectrum of the separable closure of the residue
field at its image. -/
theorem specMap_algebraMap_comp_sepClosureOver :
    Spec.map (CommRingCat.ofHom (algebraMap ↥(separableClosure s) s.residueField)) ≫
      sepClosureOver s = s.hom := by
  have htower : (algebraMap ↥(separableClosure s) s.residueField).comp
      (algebraMap (S.residueField (s.hom default)) ↥(separableClosure s)) =
      residueFieldHom s := by
    rw [← IsScalarTower.algebraMap_eq]
    rfl
  rw [sepClosureOver, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, htower]
  exact specMap_residueFieldHom_comp_fromSpecResidueField s

end GeometricPoint

/-- An element of a separable extension has separable image under any embedding over the base,
hence lands in the separable closure. -/
theorem algHom_mem_separableClosure {K κ Ω E : Type u} [Field K] [Field κ] [Field Ω] [Field E]
    [Algebra K κ] [Algebra κ Ω] [Algebra K Ω] [IsScalarTower K κ Ω]
    [Algebra K E] [Algebra.IsSeparable K E] (φ : E →ₐ[K] Ω) (a : E) :
    φ a ∈ separableClosure κ Ω := by
  refine mem_separableClosure_iff.mpr (IsSeparable.tower_top (F := K) κ ?_)
  rw [IsSeparable, minpoly.algHom_eq φ φ.toRingHom.injective a]
  exact Algebra.IsSeparable.isSeparable K a

/-- Evaluating the ring map of a morphism of spectra that factors through `Spec.map h`. -/
private theorem apply_preimage_of_map_comp_eq {A B C : CommRingCat} (h : A ⟶ B)
    (f : Spec A ⟶ Spec C) (g : Spec B ⟶ Spec C) (hfg : Spec.map h ≫ f = g) (x : C) :
    (Spec.preimage g).hom x = h.hom ((Spec.preimage f).hom x) := by
  subst hfg
  rw [Spec.preimage_comp, Spec.preimage_map]
  rfl

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- The lifts of the separable-closure point of a geometric point to the objects of the small
étale site. -/
def sepClosureFiber : SmallEtale B S hS ⥤ Type u where
  obj U := {q : Spec (.of ↥(GeometricPoint.separableClosure s)) ⟶
      (SmallEtale.toScheme B S hS).obj U //
    q ≫ B.inclusion.map U.obj.hom = GeometricPoint.sepClosureOver s}
  map {U V} f := ↾ (fun q => ⟨q.1 ≫ (SmallEtale.toScheme B S hS).map f, by
    have hw : (SmallEtale.toScheme B S hS).map f ≫
        B.inclusion.map V.obj.hom = B.inclusion.map U.obj.hom := by
      change B.inclusion.map (((SmallEtale.inclusion B S hS).map f).left) ≫
        B.inclusion.map V.obj.hom = B.inclusion.map U.obj.hom
      simpa only [SmallEtale.inclusion, ObjectProperty.ι_obj, ← Functor.map_comp] using
        congrArg B.inclusion.map (Over.w ((SmallEtale.inclusion B S hS).map f))
    rw [Category.assoc, hw]
    exact q.2⟩)
  map_id := by intro U; ext q; simp
  map_comp := by intro U V W f g; ext q; simp [Category.assoc]

/-- Composing with the inclusion of the separable closure into the algebraically closed field
of a geometric point takes lifts of the separable-closure point to lifts of the geometric
point. -/
def sepClosureFiberToGeometricPointFiber :
    sepClosureFiber B S hS s ⟶ geometricPointFiber B S hS s where
  app U := ↾ (fun q => ⟨Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GeometricPoint.separableClosure s) s.residueField)) ≫ q.1, by
    rw [Category.assoc, q.2]
    exact GeometricPoint.specMap_algebraMap_comp_sepClosureOver s⟩)
  naturality U V f := by
    ext q
    exact Subtype.ext (Category.assoc _ _ _).symm

/-- The absolute Galois group of a geometric point acts on the lifts of its separable-closure
point, by precomposition with the automorphism of the separable closure. -/
@[sga "4½ Arcata 2.4.2" "partial"]
def sepClosureFiberSmul (σ : GeometricPoint.absoluteGaloisGroup s) {U : SmallEtale B S hS}
    (q : (sepClosureFiber B S hS s).obj U) : (sepClosureFiber B S hS s).obj U :=
  ⟨Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ q.1, by
    have hσ : σ.toAlgHom.toRingHom.comp
        (algebraMap (S.residueField (s.hom default))
          ↥(GeometricPoint.separableClosure s)) =
        algebraMap (S.residueField (s.hom default))
          ↥(GeometricPoint.separableClosure s) :=
      RingHom.ext fun x => σ.commutes x
    rw [Category.assoc, q.2, GeometricPoint.sepClosureOver, ← Category.assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, hσ]⟩

/-- The Galois action on the lifts of the separable-closure point, computed on the underlying
morphism of schemes. -/
@[simp]
theorem sepClosureFiberSmul_coe (σ : GeometricPoint.absoluteGaloisGroup s)
    {U : SmallEtale B S hS} (q : (sepClosureFiber B S hS s).obj U) :
    (sepClosureFiberSmul B S hS s σ q).1 =
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ q.1 :=
  rfl

/-- The identity of the absolute Galois group acts trivially on the lifts of the
separable-closure point. -/
theorem sepClosureFiberSmul_one {U : SmallEtale B S hS}
    (q : (sepClosureFiber B S hS s).obj U) :
    sepClosureFiberSmul B S hS s 1 q = q := by
  apply Subtype.ext
  change Spec.map (𝟙 (CommRingCat.of ↥(GeometricPoint.separableClosure s))) ≫ q.1 = q.1
  rw [Spec.map_id, Category.id_comp]

/-- The Galois action on the lifts of the separable-closure point is multiplicative. -/
theorem sepClosureFiberSmul_mul (σ τ : GeometricPoint.absoluteGaloisGroup s)
    {U : SmallEtale B S hS} (q : (sepClosureFiber B S hS s).obj U) :
    sepClosureFiberSmul B S hS s (σ * τ) q =
      sepClosureFiberSmul B S hS s σ (sepClosureFiberSmul B S hS s τ q) := by
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom (σ.toAlgHom.toRingHom.comp τ.toAlgHom.toRingHom)) ≫ q.1 =
    Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom τ.toAlgHom.toRingHom) ≫ q.1
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

/-- The Galois action on the lifts of the separable-closure point is natural in the object of
the small étale site. -/
theorem sepClosureFiber_map_sepClosureFiberSmul (σ : GeometricPoint.absoluteGaloisGroup s)
    {U V : SmallEtale B S hS} (f : U ⟶ V) (q : (sepClosureFiber B S hS s).obj U) :
    ConcreteCategory.hom ((sepClosureFiber B S hS s).map f)
        (sepClosureFiberSmul B S hS s σ q) =
      sepClosureFiberSmul B S hS s σ
        (ConcreteCategory.hom ((sepClosureFiber B S hS s).map f) q) :=
  Subtype.ext (Category.assoc _ _ _)

section Field

variable (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K)))

/-- Over a field, every lift of a geometric point factors through the spectrum of the
separable closure of the residue field at its image. -/
theorem surjective_sepClosureFiberToGeometricPointFiber
    (U : SmallEtale B (Spec (.of K)) hK) :
    Function.Surjective (ConcreteCategory.hom
      ((sepClosureFiberToGeometricPointFiber B (Spec (.of K)) hK sbar).app U)) := by
  classical
  intro p
  obtain ⟨I, E, _, _, _, _, e, he⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable K
      (B.inclusion.map U.obj.hom)).mp inferInstance
  obtain ⟨i, g, hg⟩ := exists_factorization_spec_sigma
    (fun i ↦ Spec (.of (E i))) sbar.residueField e p.1
  let _ : Algebra K ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) :=
    (Spec.preimage
      ((Spec (CommRingCat.of K)).fromSpecResidueField (sbar.hom default))).hom.toAlgebra
  let _ : Algebra K sbar.residueField := (Spec.preimage sbar.hom).hom.toAlgebra
  have htower : ∀ x : K, algebraMap K sbar.residueField x =
      algebraMap ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) sbar.residueField
        (algebraMap K _ x) := by
    intro x
    exact apply_preimage_of_map_comp_eq _ _ _
      (GeometricPoint.specMap_residueFieldHom_comp_fromSpecResidueField sbar) x
  let _ : IsScalarTower K
      ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) sbar.residueField :=
    IsScalarTower.of_algebraMap_eq htower
  have hsg : sbar.hom = g ≫ Spec.map (CommRingCat.ofHom (algebraMap K (E i))) := by
    rw [← p.2, hg, ← he]
    simp [Category.assoc]
  have hphi : (Spec.preimage g).hom.comp (algebraMap K (E i)) =
      (Spec.preimage sbar.hom).hom := by
    have h2 := congrArg Spec.preimage hsg
    rw [Spec.preimage_comp, Spec.preimage_map] at h2
    exact congrArg CommRingCat.Hom.hom h2.symm
  have hmem : ∀ a : E i, (Spec.preimage g).hom a ∈ GeometricPoint.separableClosure sbar := fun a =>
    algHom_mem_separableClosure
      (AlgHom.mk (Spec.preimage g).hom (fun x => RingHom.congr_fun hphi x)) a
  let phires : E i →+* ↥(GeometricPoint.separableClosure sbar) :=
    (Spec.preimage g).hom.codRestrict _ hmem
  have hval : (algebraMap ↥(GeometricPoint.separableClosure sbar) sbar.residueField).comp
      phires = (Spec.preimage g).hom := rfl
  have hinc := (algebraMap ↥(GeometricPoint.separableClosure sbar) sbar.residueField).injective
  have hpre : CommRingCat.ofHom (phires.comp (algebraMap K (E i))) =
      Spec.preimage (GeometricPoint.sepClosureOver sbar) := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => hinc ?_)
    have e1 : (algebraMap ↥(GeometricPoint.separableClosure sbar) sbar.residueField)
        (phires.comp (algebraMap K (E i)) x) = (Spec.preimage sbar.hom).hom x := by
      rw [← RingHom.comp_apply, ← RingHom.comp_assoc, hval]
      exact RingHom.congr_fun hphi x
    have e2 : (algebraMap ↥(GeometricPoint.separableClosure sbar) sbar.residueField)
        ((Spec.preimage (GeometricPoint.sepClosureOver sbar)).hom x) =
        (Spec.preimage sbar.hom).hom x :=
      (apply_preimage_of_map_comp_eq _ _ _
        (GeometricPoint.specMap_algebraMap_comp_sepClosureOver sbar) x).symm
    exact e1.trans e2.symm
  have hf : e.inv ≫ B.inclusion.map U.obj.hom =
      Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap K (E i)))) := by
    rw [← he]
    simp
  refine ⟨⟨Spec.map (CommRingCat.ofHom phires) ≫
      Sigma.ι (fun i ↦ Spec (.of (E i))) i ≫ e.inv, ?_⟩, ?_⟩
  · rw [Category.assoc, Category.assoc, hf, Sigma.ι_comp_desc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, hpre, Spec.map_preimage]
  · apply Subtype.ext
    change Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GeometricPoint.separableClosure sbar) sbar.residueField)) ≫
      (Spec.map (CommRingCat.ofHom phires) ≫
        Sigma.ι (fun i ↦ Spec (.of (E i))) i ≫ e.inv) = p.1
    rw [hg, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hval,
      CommRingCat.ofHom_hom, Spec.map_preimage]

/-- Over a field, a lift of a geometric point factors through the spectrum of the separable
closure of the residue field at its image in at most one way. -/
theorem injective_sepClosureFiberToGeometricPointFiber
    (U : SmallEtale B (Spec (.of K)) hK) :
    Function.Injective (ConcreteCategory.hom
      ((sepClosureFiberToGeometricPointFiber B (Spec (.of K)) hK sbar).app U)) := by
  classical
  intro q₁ q₂ h
  have hv : Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GeometricPoint.separableClosure sbar) sbar.residueField)) ≫ q₁.1 =
      Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GeometricPoint.separableClosure sbar) sbar.residueField)) ≫ q₂.1 :=
    congrArg Subtype.val h
  obtain ⟨I, E, _, _, _, _, e, he⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable K
      (B.inclusion.map U.obj.hom)).mp inferInstance
  obtain ⟨i₁, g₁, h₁⟩ := exists_factorization_spec_sigma
    (fun i ↦ Spec (.of (E i))) ↥(GeometricPoint.separableClosure sbar) e q₁.1
  obtain ⟨i₂, g₂, h₂⟩ := exists_factorization_spec_sigma
    (fun i ↦ Spec (.of (E i))) ↥(GeometricPoint.separableClosure sbar) e q₂.1
  set inc := Spec.map (CommRingCat.ofHom
    (algebraMap ↥(GeometricPoint.separableClosure sbar) sbar.residueField))
  have k₁ : (inc ≫ q₁.1) ≫ e.hom = (inc ≫ g₁) ≫
      Sigma.ι (fun i ↦ Spec (.of (E i))) i₁ := by
    rw [h₁]
    simp [Category.assoc]
  have k₂ : (inc ≫ q₁.1) ≫ e.hom = (inc ≫ g₂) ≫
      Sigma.ι (fun i ↦ Spec (.of (E i))) i₂ := by
    rw [hv, h₂]
    simp [Category.assoc]
  obtain ⟨hij, hcomp⟩ := factorization_spec_sigma_unique
    (fun i ↦ Spec (.of (E i))) sbar.residueField _ k₁ k₂
  subst hij
  rw [eqToHom_refl, Category.comp_id] at hcomp
  have hg : g₁ = g₂ := by
    have : Spec.preimage g₁ = Spec.preimage g₂ :=
      CommRingCat.hom_ext (RingHom.ext fun x =>
        (algebraMap ↥(GeometricPoint.separableClosure sbar) sbar.residueField).injective 
          ((apply_preimage_of_map_comp_eq _ g₁ _ rfl x).symm.trans
            ((congrArg (fun g => (Spec.preimage g).hom x) hcomp).trans
              (apply_preimage_of_map_comp_eq _ g₂ _ rfl x))))
    rw [← Spec.map_preimage g₁, ← Spec.map_preimage g₂, this]
  exact Subtype.ext (by rw [h₁, h₂, hg])

/-- **The fibre of a geometric point of the spectrum of a field sees only the separable
closure.**  Composing with the inclusion of the separable closure of the residue field into
the algebraically closed field of a geometric point is a bijection from the lifts of the
separable-closure point to the lifts of the geometric point. -/
theorem bijective_sepClosureFiberToGeometricPointFiber
    (U : SmallEtale B (Spec (.of K)) hK) :
    Function.Bijective (ConcreteCategory.hom
      ((sepClosureFiberToGeometricPointFiber B (Spec (.of K)) hK sbar).app U)) :=
  ⟨injective_sepClosureFiberToGeometricPointFiber B K hK sbar U,
    surjective_sepClosureFiberToGeometricPointFiber B K hK sbar U⟩

/-- The lifts of a geometric point of the spectrum of a field, identified with the lifts of
its separable-closure point. -/
def geometricPointFiberSepClosureEquiv (U : SmallEtale B (Spec (.of K)) hK) :
    (sepClosureFiber B (Spec (.of K)) hK sbar).obj U ≃
      (geometricPointFiber B (Spec (.of K)) hK sbar).obj U :=
  Equiv.ofBijective _ (bijective_sepClosureFiberToGeometricPointFiber B K hK sbar U)

/-- The identification of the lifts of a geometric point with the lifts of its
separable-closure point, computed on the underlying morphism of schemes. -/
@[simp]
theorem geometricPointFiberSepClosureEquiv_coe (U : SmallEtale B (Spec (.of K)) hK)
    (y : (sepClosureFiber B (Spec (.of K)) hK sbar).obj U) :
    (geometricPointFiberSepClosureEquiv B K hK sbar U y).1 =
      Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GeometricPoint.separableClosure sbar) sbar.residueField)) ≫ y.1 :=
  rfl

/-- The identification of the lifts of a geometric point with the lifts of its
separable-closure point is natural in the object of the small étale site. -/
theorem geometricPointFiberSepClosureEquiv_map {U V : SmallEtale B (Spec (.of K)) hK}
    (f : U ⟶ V) (y : (sepClosureFiber B (Spec (.of K)) hK sbar).obj U) :
    (geometricPointFiber B (Spec (.of K)) hK sbar).map f
        (geometricPointFiberSepClosureEquiv B K hK sbar U y) =
      geometricPointFiberSepClosureEquiv B K hK sbar V
        ((sepClosureFiber B (Spec (.of K)) hK sbar).map f y) :=
  Subtype.ext (Category.assoc _ _ _)

/-- **The action of the absolute Galois group on the lifts of a geometric point of the
spectrum of a field.**  A lift of the geometric point factors uniquely through the spectrum of
the separable closure of the residue field, where the Galois group acts by precomposition. -/
@[sga "4½ Arcata 2.4.2" "partial"]
def galoisFiberAction (σ : GeometricPoint.absoluteGaloisGroup sbar)
    ⦃U : SmallEtale B (Spec (.of K)) hK⦄
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    (geometricPointFiber B (Spec (.of K)) hK sbar).obj U :=
  geometricPointFiberSepClosureEquiv B K hK sbar U
    (sepClosureFiberSmul B (Spec (.of K)) hK sbar σ
      ((geometricPointFiberSepClosureEquiv B K hK sbar U).symm p))

/-- The Galois action on the lifts of a geometric point, computed on the underlying morphism of
schemes. -/
theorem coe_galoisFiberAction (σ : GeometricPoint.absoluteGaloisGroup sbar)
    ⦃U : SmallEtale B (Spec (.of K)) hK⦄
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    (galoisFiberAction B K hK sbar σ p).1 =
      Spec.map (CommRingCat.ofHom
          (algebraMap ↥(GeometricPoint.separableClosure sbar) sbar.residueField)) ≫
        Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
          ((geometricPointFiberSepClosureEquiv B K hK sbar U).symm p).1 :=
  rfl

/-- **The Galois action changes a lift of a geometric point by precomposition.**  If an
endomorphism `τ` of the algebraically closed field of the geometric point restricts to the
Galois automorphism `σ` on the separable closure, then the action of `σ` on a lift is
precomposition with `Spec τ`. -/
theorem coe_galoisFiberAction_of_extends (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (τ : sbar.residueField →+* sbar.residueField)
    (hτ : ∀ a : ↥(GeometricPoint.separableClosure sbar),
      τ (algebraMap ↥(GeometricPoint.separableClosure sbar) sbar.residueField a) =
        algebraMap ↥(GeometricPoint.separableClosure sbar) sbar.residueField (σ a))
    ⦃U : SmallEtale B (Spec (.of K)) hK⦄
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    (galoisFiberAction B K hK sbar σ p).1 = Spec.map (CommRingCat.ofHom τ) ≫ p.1 := by
  have hp : p.1 = Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GeometricPoint.separableClosure sbar) sbar.residueField)) ≫
      ((geometricPointFiberSepClosureEquiv B K hK sbar U).symm p).1 := by
    rw [← geometricPointFiberSepClosureEquiv_coe B K hK sbar U
        ((geometricPointFiberSepClosureEquiv B K hK sbar U).symm p),
      Equiv.apply_symm_apply]
  have hcomp : Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GeometricPoint.separableClosure sbar) sbar.residueField)) ≫
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) =
      Spec.map (CommRingCat.ofHom τ) ≫ Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GeometricPoint.separableClosure sbar) sbar.residueField)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map
      (CommRingCat.hom_ext (RingHom.ext fun a => (hτ a).symm))
  rw [coe_galoisFiberAction, ← Category.assoc, hcomp, Category.assoc, ← hp]

/-- The identity of the absolute Galois group acts trivially on the lifts of a geometric
point. -/
theorem galoisFiberAction_one ⦃U : SmallEtale B (Spec (.of K)) hK⦄
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    galoisFiberAction B K hK sbar 1 p = p := by
  rw [galoisFiberAction, sepClosureFiberSmul_one, Equiv.apply_symm_apply]

/-- The Galois action on the lifts of a geometric point is multiplicative. -/
theorem galoisFiberAction_mul (σ τ : GeometricPoint.absoluteGaloisGroup sbar)
    ⦃U : SmallEtale B (Spec (.of K)) hK⦄
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    galoisFiberAction B K hK sbar (σ * τ) p =
      galoisFiberAction B K hK sbar σ (galoisFiberAction B K hK sbar τ p) := by
  rw [galoisFiberAction, galoisFiberAction, galoisFiberAction, Equiv.symm_apply_apply,
    sepClosureFiberSmul_mul]

/-- The Galois action on the lifts of a geometric point is natural in the object of the small
étale site. -/
theorem galoisFiberAction_naturality (σ : GeometricPoint.absoluteGaloisGroup sbar)
    ⦃U V : SmallEtale B (Spec (.of K)) hK⦄ (f : U ⟶ V)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    (geometricPointFiber B (Spec (.of K)) hK sbar).map f
        (galoisFiberAction B K hK sbar σ p) =
      galoisFiberAction B K hK sbar σ
        ((geometricPointFiber B (Spec (.of K)) hK sbar).map f p) := by
  have key : (geometricPointFiberSepClosureEquiv B K hK sbar V).symm
      ((geometricPointFiber B (Spec (.of K)) hK sbar).map f p) =
      (sepClosureFiber B (Spec (.of K)) hK sbar).map f
        ((geometricPointFiberSepClosureEquiv B K hK sbar U).symm p) := by
    refine (geometricPointFiberSepClosureEquiv B K hK sbar V).symm_apply_eq.mpr ?_
    rw [← geometricPointFiberSepClosureEquiv_map, Equiv.apply_symm_apply]
  rw [galoisFiberAction, galoisFiberAction, key, geometricPointFiberSepClosureEquiv_map,
    sepClosureFiber_map_sepClosureFiberSmul]

/-- The absolute Galois group of a geometric point of the spectrum of a field acts on the lifts
of that point to an object of the small étale site. -/
@[instance_reducible, sga "4½ Arcata 2.4.2" "partial"]
def geometricPointFiberMulAction (U : SmallEtale B (Spec (.of K)) hK) :
    MulAction (GeometricPoint.absoluteGaloisGroup sbar)
      ((geometricPointFiber B (Spec (.of K)) hK sbar).obj U) where
  smul σ p := galoisFiberAction B K hK sbar σ p
  one_smul p := galoisFiberAction_one B K hK sbar p
  mul_smul σ τ p := galoisFiberAction_mul B K hK sbar σ τ p

/-- For a continuous set over the absolute Galois group of a geometric point of the spectrum of
a field, the presheaf of equivariant maps out of the lifts of the geometric point is a sheaf on
the small étale site. -/
theorem isSheaf_galoisFiberActionEquivariantFiberHomPresheaf
    (M : ContinuousGSet.{u, max u v} (GeometricPoint.absoluteGaloisGroup sbar)) :
    Presieve.IsSheaf (SmallEtale.topology B (Spec (.of K)) hK)
      (equivariantGeometricPointFiberHomPresheaf.{u, v} B (Spec (.of K)) hK sbar
        (galoisFiberAction B K hK sbar) (galoisFiberAction_naturality B K hK sbar)
        (continuousGSetSmul M)) :=
  isSheaf_galoisEquivariantGeometricPointFiberHomPresheaf.{u, v} B K hK sbar
    (galoisFiberAction B K hK sbar) (galoisFiberAction_naturality B K hK sbar) M

/-- The sheaf on the small étale site of `Spec K` attached to a continuous set over the
absolute Galois group of a geometric point: its sections over `U` are the Galois-equivariant
maps from the lifts of the geometric point to `U`.  This is the value of the inverse of the
stalk functor of [Stacks, Tag 03QT]. -/
def galoisGeometricPointFiberHomSheaf
    (M : ContinuousGSet.{u, max u v} (GeometricPoint.absoluteGaloisGroup sbar)) :
    smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK :=
  galoisEquivariantGeometricPointFiberHomSheaf.{u, v} B K hK sbar
    (galoisFiberAction B K hK sbar) (galoisFiberAction_naturality B K hK sbar) M

end Field

end AlgebraicGeometry

end
