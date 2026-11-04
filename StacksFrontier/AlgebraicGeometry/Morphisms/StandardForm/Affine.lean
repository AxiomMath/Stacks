module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.StandardEtale
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.Defs
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.StandardRefinement

/-!
# Morphisms of affine schemes in standard form, under isomorphism and base change

A morphism of affine schemes is in *standard form* — standard étale, standard smooth, or
standard syntomic — when its map on global sections is a standard étale, standard smooth, or
relative global complete intersection ring map. Each of these three conditions depends only on
the isomorphism class of the morphism in the arrow category, and each is preserved by base
change along an arbitrary morphism of affine schemes.

## Main results

* `AlgebraicGeometry.isStandardEtale_iff_of_arrow_iso` and
  `AlgebraicGeometry.isStandardSyntomic_iff_of_arrow_iso`: standard étaleness and standard
  syntomicity are invariants of the arrow up to isomorphism. The corresponding statement for
  standard smoothness is `AlgebraicGeometry.isStandardSmooth_iff_of_arrow_iso`.
* `AlgebraicGeometry.isStandardEtale_pullback_fst`,
  `AlgebraicGeometry.isStandardSmooth_pullback_fst` and
  `AlgebraicGeometry.isStandardSyntomic_pullback_fst`: base change of a morphism in standard
  form along a morphism of affine schemes is again in standard form.

## Implementation notes

All three predicates are stated through the algebra structure that the map on global sections
induces, so transporting one along an isomorphism of arrows amounts to transporting an algebraic
condition along a pair of compatible ring isomorphisms, one of the base and one of the total
ring. That transport is isolated in `isStandardEtale_transport_ringEquiv` and
`relativeGCI_transport_ringEquiv`; both factor the pair of isomorphisms as an isomorphism of the
total ring over the old base, where `Algebra.IsStandardEtale.of_equiv` and
`Algebra.IsRelativeGlobalCompleteIntersection.of_algEquiv` apply, followed by a change of base
ring along a ring isomorphism, which is a pushout and so a base change.

For base change the fibre product of affine schemes is identified with the spectrum of a tensor
product by `AlgebraicGeometry.pullbackSpecIso`, after normalizing the two given morphisms to
spectra of ring maps; `pullbackFstArrowIsoSpecTensor` packages that identification as an
isomorphism of arrows. The algebra structure on the tensor product that the predicates then see
is `Algebra.TensorProduct.leftAlgebra`, whereas the one coming from the scheme morphism is the
algebra of the structure ring map; `tensorProduct_leftAlgebra_eq` identifies the two.

## References

* [Stacks Project, Tag 01UC](https://stacks.math.columbia.edu/tag/01UC)
* [Stacks Project, Tag 01V5](https://stacks.math.columbia.edu/tag/01V5)
* [Stacks Project, Tag 02GI](https://stacks.math.columbia.edu/tag/02GI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Standard étaleness is transported along a pair of ring isomorphisms, one of the base and one
of the total ring, which commute with the two structure maps. -/
private lemma isStandardEtale_transport_ringEquiv {R₀ R A₀ A : Type u} [CommRing R₀]
    [CommRing R] [CommRing A₀] [CommRing A] (eR : R₀ ≃+* R) (eA : A₀ ≃+* A)
    (f₀ : R₀ →+* A₀) (f : R →+* A)
    (hcomp : eA.toRingHom.comp f₀ = f.comp eR.toRingHom)
    (hf₀ : let : Algebra R₀ A₀ := f₀.toAlgebra
      Algebra.IsStandardEtale R₀ A₀) :
    let : Algebra R A := f.toAlgebra
    Algebra.IsStandardEtale R A := by
  let f₁ : R₀ →+* A := eA.toRingHom.comp f₀
  let : Algebra R₀ A₀ := f₀.toAlgebra
  let : Algebra R₀ A := f₁.toAlgebra
  let : Algebra.IsStandardEtale R₀ A₀ := hf₀
  have h₁ : Algebra.IsStandardEtale R₀ A :=
    Algebra.IsStandardEtale.of_equiv
      { eA with commutes' := fun r => rfl : A₀ ≃ₐ[R₀] A }
  let : Algebra R₀ R := eR.toRingHom.toAlgebra
  let : Algebra R A := f.toAlgebra
  let : IsScalarTower R₀ R A := IsScalarTower.of_algebraMap_eq fun x =>
    congrFun (congrArg DFunLike.coe hcomp) x
  let : Algebra.IsPushout R₀ A R A :=
    Algebra.IsPushout.of_bijective_left (R := R₀) (A := R) (T := A) eR.bijective
  let : Algebra.IsPushout R₀ R A A := Algebra.IsPushout.symm inferInstance
  let : Algebra.IsStandardEtale R₀ A := h₁
  exact Algebra.IsStandardEtale.of_equiv (Algebra.IsPushout.equiv R₀ R A A)

/-- Being a relative global complete intersection is transported along a pair of ring
isomorphisms, one of the base and one of the total ring, which commute with the two structure
maps. -/
private lemma relativeGCI_transport_ringEquiv {R₀ R A₀ A : Type u} [CommRing R₀]
    [CommRing R] [CommRing A₀] [CommRing A] (eR : R₀ ≃+* R) (eA : A₀ ≃+* A)
    (f₀ : R₀ →+* A₀) (f : R →+* A)
    (hcomp : eA.toRingHom.comp f₀ = f.comp eR.toRingHom)
    (hf₀ : let : Algebra R₀ A₀ := f₀.toAlgebra
      Algebra.IsRelativeGlobalCompleteIntersection R₀ A₀) :
    let : Algebra R A := f.toAlgebra
    Algebra.IsRelativeGlobalCompleteIntersection R A := by
  let f₁ : R₀ →+* A := eA.toRingHom.comp f₀
  let : Algebra R₀ A₀ := f₀.toAlgebra
  let : Algebra R₀ A := f₁.toAlgebra
  let : Algebra.IsRelativeGlobalCompleteIntersection R₀ A₀ := hf₀
  have h₁ : Algebra.IsRelativeGlobalCompleteIntersection R₀ A :=
    Algebra.IsRelativeGlobalCompleteIntersection.of_algEquiv
      { eA with commutes' := fun r => rfl : A₀ ≃ₐ[R₀] A }
  exact relativeGCI_of_baseRingEquiv eR f₁ f hcomp h₁

/-- The two ring isomorphisms on global sections induced by an isomorphism of arrows of affine
schemes, together with the square they make with the maps on global sections. -/
private lemma arrowIso_appTop_comm {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : X' ⟶ S')
    (e : Arrow.mk f ≅ Arrow.mk g) :
    e.hom.left.appTop.hom.comp g.appTop.hom =
      f.appTop.hom.comp e.hom.right.appTop.hom := by
  have h := congrArg Scheme.Hom.appTop (Arrow.w e.hom)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  exact congrArg (fun k : CommRingCat.Hom _ _ => k.hom) h

/-- An isomorphism of arrows of affine schemes induces ring isomorphisms on global sections
compatible with the maps on global sections. -/
private lemma exists_ringEquiv_of_arrow_iso {X S X' S' : Scheme.{u}} [IsAffine X] [IsAffine S]
    [IsAffine X'] [IsAffine S'] (f : X ⟶ S) (g : X' ⟶ S') (e : Arrow.mk f ≅ Arrow.mk g) :
    ∃ (α : Γ(X', ⊤) ≃+* Γ(X, ⊤)) (β : Γ(S', ⊤) ≃+* Γ(S, ⊤)),
      α.toRingHom.comp g.appTop.hom = f.appTop.hom.comp β.toRingHom := by
  have : IsIso e.hom.left.appTop := by
    show IsIso (e.hom.left.app ⊤)
    infer_instance
  have : IsIso e.hom.right.appTop := by
    show IsIso (e.hom.right.app ⊤)
    infer_instance
  exact ⟨RingEquiv.ofBijective e.hom.left.appTop.hom
      ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance),
    RingEquiv.ofBijective e.hom.right.appTop.hom
      ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance),
    arrowIso_appTop_comm f g e⟩

/-- Standard étaleness of a morphism of affine schemes only depends on its isomorphism class in
the arrow category. -/
private lemma isStandardEtale_of_arrow_iso {X S X' S' : Scheme.{u}} [IsAffine X] [IsAffine S]
    [IsAffine X'] [IsAffine S'] (f : X ⟶ S) (g : X' ⟶ S')
    (e : Arrow.mk f ≅ Arrow.mk g) (hg : IsStandardEtale g) :
    IsStandardEtale f := by
  obtain ⟨α, β, hcomp⟩ := exists_ringEquiv_of_arrow_iso f g e
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(S', ⊤) Γ(X', ⊤) := g.appTop.hom.toAlgebra
  change Algebra.IsStandardEtale Γ(S', ⊤) Γ(X', ⊤) at hg
  exact isStandardEtale_transport_ringEquiv β α g.appTop.hom f.appTop.hom
    hcomp hg

/-- Standard syntomicity of a morphism of affine schemes only depends on its isomorphism class
in the arrow category. -/
private lemma isStandardSyntomic_of_arrow_iso {X S X' S' : Scheme.{u}} [IsAffine X] [IsAffine S]
    [IsAffine X'] [IsAffine S'] (f : X ⟶ S) (g : X' ⟶ S')
    (e : Arrow.mk f ≅ Arrow.mk g) (hg : IsStandardSyntomic g) :
    IsStandardSyntomic f := by
  obtain ⟨α, β, hcomp⟩ := exists_ringEquiv_of_arrow_iso f g e
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(S', ⊤) Γ(X', ⊤) := g.appTop.hom.toAlgebra
  change Algebra.IsRelativeGlobalCompleteIntersection Γ(S', ⊤) Γ(X', ⊤) at hg
  exact relativeGCI_transport_ringEquiv β α g.appTop.hom f.appTop.hom
    hcomp hg

/-- Standard étaleness of morphisms of affine schemes is invariant under isomorphism in the
arrow category. -/
lemma isStandardEtale_iff_of_arrow_iso {X S X' S' : Scheme.{u}} [IsAffine X] [IsAffine S]
    [IsAffine X'] [IsAffine S'] (f : X ⟶ S) (g : X' ⟶ S')
    (e : Arrow.mk f ≅ Arrow.mk g) :
    IsStandardEtale f ↔ IsStandardEtale g :=
  ⟨isStandardEtale_of_arrow_iso g f e.symm, isStandardEtale_of_arrow_iso f g e⟩

/-- Standard syntomicity of morphisms of affine schemes is invariant under isomorphism in the
arrow category. -/
lemma isStandardSyntomic_iff_of_arrow_iso {X S X' S' : Scheme.{u}} [IsAffine X] [IsAffine S]
    [IsAffine X'] [IsAffine S'] (f : X ⟶ S) (g : X' ⟶ S')
    (e : Arrow.mk f ≅ Arrow.mk g) :
    IsStandardSyntomic f ↔ IsStandardSyntomic g :=
  ⟨isStandardSyntomic_of_arrow_iso g f e.symm, isStandardSyntomic_of_arrow_iso f g e⟩

/-- The algebra structure on `B ⊗[R] A` over `B` given by the tensor product is the one given by
its structure ring map. -/
private lemma tensorProduct_leftAlgebra_eq (R B A : Type u)
    [CommRing R] [CommRing B] [CommRing A] [Algebra R B] [Algebra R A] :
    Algebra.TensorProduct.leftAlgebra =
      (algebraMap B (TensorProduct R B A)).toAlgebra := by
  apply Algebra.algebra_ext
  intro b
  rw [Algebra.TensorProduct.algebraMap_def]
  rfl

/-- The first projection of a fibre product of affine schemes, as an arrow, is isomorphic to the
spectrum of the structure map of the corresponding tensor product. -/
private noncomputable def pullbackFstArrowIsoSpecTensor
    {X S W : Scheme.{u}} [IsAffine X] [IsAffine S] [IsAffine W]
    (g : X ⟶ S) (w : W ⟶ S) :
    let : Algebra Γ(S, ⊤) Γ(X, ⊤) := g.appTop.hom.toAlgebra
    let : Algebra Γ(S, ⊤) Γ(W, ⊤) := w.appTop.hom.toAlgebra
    Arrow.mk (pullback.fst w g) ≅ Arrow.mk
      (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(W, ⊤) (TensorProduct Γ(S, ⊤) Γ(W, ⊤) Γ(X, ⊤))))) := by
  let R : Type u := Γ(S, ⊤)
  let A : Type u := Γ(X, ⊤)
  let B : Type u := Γ(W, ⊤)
  let : Algebra R A := g.appTop.hom.toAlgebra
  let : Algebra R B := w.appTop.hom.toAlgebra
  let g' := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let w' := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have hmapg : Spec.map g.appTop = g' := by congr 1
  have hmapw : Spec.map w.appTop = w' := by congr 1
  have hg' : g ≫ S.isoSpec.hom = X.isoSpec.hom ≫ g' := by
    rw [← Scheme.isoSpec_hom_naturality g, hmapg]
  have hw' : w ≫ S.isoSpec.hom = W.isoSpec.hom ≫ w' := by
    rw [← Scheme.isoSpec_hom_naturality w, hmapw]
  let m := pullback.map w g w' g' W.isoSpec.hom X.isoSpec.hom S.isoSpec.hom hw' hg'
  let em : pullback w g ≅ pullback w' g' := asIso m
  let e : pullback w g ≅ Spec (.of (TensorProduct R B A)) :=
    em ≪≫ pullbackSpecIso R B A
  let t := Spec.map (CommRingCat.ofHom (algebraMap B (TensorProduct R B A)))
  have he : e.hom ≫ t = pullback.fst w g ≫ W.isoSpec.hom := by
    calc
      e.hom ≫ t = em.hom ≫ pullback.fst w' g' := by
        change (em ≪≫ pullbackSpecIso R B A).hom ≫ t = _
        rw [Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_fst']
      _ = pullback.fst w g ≫ W.isoSpec.hom := by
        simp [em, m, pullback.map, pullback.lift_fst]
  exact Arrow.isoMk e W.isoSpec he

/-- The isomorphisms `ΓSpecIso` intertwine a ring map with the map on global sections of its
spectrum. -/
private lemma ΓSpecIso_symm_comp_appTop {B C : Type u} [CommRing B] [CommRing C] (φ : B →+* C) :
    (Scheme.ΓSpecIso (.of C)).commRingCatIsoToRingEquiv.symm.toRingHom.comp φ =
      (Spec.map (CommRingCat.ofHom φ)).appTop.hom.comp
        (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.symm.toRingHom :=
  congrArg (fun k : CommRingCat.Hom _ _ => k.hom)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))

/-- A base change of a standard smooth morphism of affine schemes along a morphism of affine
schemes is standard smooth. -/
theorem isStandardSmooth_pullback_fst {X S W : Scheme.{u}}
    [IsAffine X] [IsAffine S] [IsAffine W] (g : X ⟶ S) (w : W ⟶ S)
    (hg : IsStandardSmooth g) : IsStandardSmooth (pullback.fst w g) := by
  let R : Type u := Γ(S, ⊤)
  let A : Type u := Γ(X, ⊤)
  let B : Type u := Γ(W, ⊤)
  let : Algebra R A := g.appTop.hom.toAlgebra
  let : Algebra R B := w.appTop.hom.toAlgebra
  let : Algebra.IsStandardSmooth R A := hg
  have hbase : Algebra.IsStandardSmooth B (TensorProduct R B A) := inferInstance
  let t := Spec.map (CommRingCat.ofHom (algebraMap B (TensorProduct R B A)))
  have htRing : (algebraMap B (TensorProduct R B A)).IsStandardSmooth := by
    rw [RingHom.IsStandardSmooth, ← tensorProduct_leftAlgebra_eq R B A]
    exact hbase
  have ht : IsStandardSmooth t := by
    show t.appTop.hom.IsStandardSmooth
    simpa [t] using htRing
  exact (isStandardSmooth_iff_of_arrow_iso (pullback.fst w g) t
    (pullbackFstArrowIsoSpecTensor g w)).mpr ht

/-- A base change of a standard étale morphism of affine schemes along a morphism of affine
schemes is standard étale. -/
theorem isStandardEtale_pullback_fst {X S W : Scheme.{u}}
    [IsAffine X] [IsAffine S] [IsAffine W] (g : X ⟶ S) (w : W ⟶ S)
    (hg : IsStandardEtale g) : IsStandardEtale (pullback.fst w g) := by
  let R : Type u := Γ(S, ⊤)
  let A : Type u := Γ(X, ⊤)
  let B : Type u := Γ(W, ⊤)
  let : Algebra R A := g.appTop.hom.toAlgebra
  let : Algebra R B := w.appTop.hom.toAlgebra
  let : Algebra.IsStandardEtale R A := hg
  let C : Type u := TensorProduct R B A
  let : Algebra B C := Algebra.TensorProduct.leftAlgebra
  have hbase : Algebra.IsStandardEtale B C := inferInstance
  let t := Spec.map (CommRingCat.ofHom (algebraMap B C))
  have hbaseRing : (let : Algebra B C := (algebraMap B C).toAlgebra
      Algebra.IsStandardEtale B C) := by
    rw [← tensorProduct_leftAlgebra_eq R B A]
    exact hbase
  have ht : IsStandardEtale t := by
    show (let : Algebra Γ(Spec (.of B), ⊤) Γ(Spec (.of C), ⊤) := t.appTop.hom.toAlgebra
      Algebra.IsStandardEtale Γ(Spec (.of B), ⊤) Γ(Spec (.of C), ⊤))
    exact isStandardEtale_transport_ringEquiv _ _ (algebraMap B C) t.appTop.hom
      (ΓSpecIso_symm_comp_appTop (algebraMap B C)) hbaseRing
  exact (isStandardEtale_iff_of_arrow_iso (pullback.fst w g) t
    (pullbackFstArrowIsoSpecTensor g w)).mpr ht

/-- A base change of a standard syntomic morphism of affine schemes along a morphism of affine
schemes is standard syntomic. -/
theorem isStandardSyntomic_pullback_fst {X S W : Scheme.{u}}
    [IsAffine X] [IsAffine S] [IsAffine W] (g : X ⟶ S) (w : W ⟶ S)
    (hg : IsStandardSyntomic g) : IsStandardSyntomic (pullback.fst w g) := by
  let R : Type u := Γ(S, ⊤)
  let A : Type u := Γ(X, ⊤)
  let B : Type u := Γ(W, ⊤)
  let : Algebra R A := g.appTop.hom.toAlgebra
  let : Algebra R B := w.appTop.hom.toAlgebra
  let : Algebra.IsRelativeGlobalCompleteIntersection R A := hg
  let C : Type u := TensorProduct R B A
  let : Algebra B C := Algebra.TensorProduct.leftAlgebra
  let : Algebra A C := Algebra.TensorProduct.rightAlgebra
  have hbase : Algebra.IsRelativeGlobalCompleteIntersection B C := by
    let : Algebra.IsPushout R B A C := TensorProduct.isPushout
    let : Algebra.IsPushout R A B C := Algebra.IsPushout.symm inferInstance
    exact Algebra.IsRelativeGlobalCompleteIntersection.baseChange R A B C
  let t := Spec.map (CommRingCat.ofHom (algebraMap B C))
  have hbaseRing : (let : Algebra B C := (algebraMap B C).toAlgebra
      Algebra.IsRelativeGlobalCompleteIntersection B C) := by
    rw [← tensorProduct_leftAlgebra_eq R B A]
    exact hbase
  have ht : IsStandardSyntomic t := by
    show (let : Algebra Γ(Spec (.of B), ⊤) Γ(Spec (.of C), ⊤) := t.appTop.hom.toAlgebra
      Algebra.IsRelativeGlobalCompleteIntersection Γ(Spec (.of B), ⊤) Γ(Spec (.of C), ⊤))
    exact relativeGCI_transport_ringEquiv _ _ (algebraMap B C) t.appTop.hom
      (ΓSpecIso_symm_comp_appTop (algebraMap B C)) hbaseRing
  exact (isStandardSyntomic_iff_of_arrow_iso (pullback.fst w g) t
    (pullbackFstArrowIsoSpecTensor g w)).mpr ht

end AlgebraicGeometry
