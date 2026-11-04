module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffineGluedTriple
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite

/-!
# Essential surjectivity of the Beauville--Laszlo glueing functor on affines (Stacks 0F9Q)

Fix a Beauville--Laszlo glueing pair `(R → R', f)`, write `X = Spec R`, `U = Spec R_f`,
`X' = Spec R'` and `U' = Spec R'_f`, and let `G` be a glueing functor of Stacks 0F9N for the
resulting square. Stacks 0F9Q asserts that `G` restricts to an *equivalence* between the affine
algebraic spaces over `X` which are glueable for the pair and the cartesian glueing triples with
affine components. This module proves the essential surjectivity half of that assertion: every
cartesian triple with affine components is the triple of an affine glueable algebraic space over
`X`.

## Main results

* `BeauvilleLaszlo.Space.exists_glued_of_pushoutSquares`: the Beauville--Laszlo theorem for
  algebras, with its two base-change squares in the form the geometry produces them — squares of
  `CommRingCat` rather than `Algebra.IsPushout` for a scalar tower.
* `BeauvilleLaszlo.Space.exists_iso_of_affineComponents`: **from a cartesian triple with affine
  components, an affine glueable `R`-algebra whose triple is the given one.**
* `BeauvilleLaszlo.Space.essSurj_affineGlueableRestriction`: **Stacks 0F9Q**, the essential
  surjectivity clause: the restriction of the glueing functor to the affine glueable spaces is
  essentially surjective.

## Implementation notes

The two outer components of the triple are affine algebraic spaces over the affine bases
`Spec R_f` and `Spec R'`, so the presentation theorem
`AlgebraicGeometry.Space.exists_specSite_iso_of_isAffineSpace` writes them as `Spec A₁` and
`Spec A'` for an `R_f`-algebra `A₁` and an `R'`-algebra `A'` whose spectra the site contains.
Their base changes to `R'_f`, namely `C₁ = R'_f ⊗_{R_f} A₁` and `C₂ = R'_f ⊗_{R'} A'`, present
the two routes from the middle component to the two outer ones, and the glueing isomorphism of
the triple becomes the isomorphism `BeauvilleLaszlo.Space.glueingPsi` of `R'_f`-algebras between
them; `BeauvilleLaszlo.exists_glued_of_cartesianDatum` then glues an `R`-algebra `A` out of that
cartesian datum, and `BeauvilleLaszlo.Space.nonempty_glueingDataIso` identifies the triple of
`Spec A` with the given one.

Keeping that assembly inside the heartbeat budget is why the glueing step is a separate
declaration, `exists_glued_of_pushoutSquares`, stated for abstract `C₁` and `C₂`: the tensor
products, their `Algebra.TensorProduct.rightAlgebra` structures and the translation between
`Algebra.IsPushout` and squares of `CommRingCat` are then elaborated once, in its own statement,
and the assembly only instantiates it. The same reason puts the two glueability transports below
in declarations of their own.

Glueability of the algebra is transported to glueability of the algebraic space through
`BeauvilleLaszlo.Space.isGlueableAlgebraicSpace_spaceOfSite`, which asks for glueability of the
global sections of the representing object. That predicate carries its own `Algebra R R'`
instance, built from the ring map by `RingHom.toAlgebra`, which is only propositionally the
ambient one; `BeauvilleLaszlo.Space.isGlueableFor_toAlgebra` moves glueability across that
identification, which `Algebra.algebra_ext` supplies.

## References

* [Stacks Project, Tag 0BP2](https://stacks.math.columbia.edu/tag/0BP2)
* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9P](https://stacks.math.columbia.edu/tag/0F9P)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

universe u

namespace BeauvilleLaszlo.Space

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ### Glueability of the algebraic space of a glueable algebra -/

/-- **Glueability of a module does not depend on which of two `Algebra R S` structures with the
same structure map is used.** The predicate
`AlgebraicGeometry.Space.IsGlueableGlobalSections` installs the one built from the ring map by
`RingHom.toAlgebra`, which is only propositionally the ambient one. -/
theorem isGlueableFor_toAlgebra {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (f : R)
    (h : _root_.BeauvilleLaszlo.IsGlueableFor (S := S) M f) :
    @_root_.BeauvilleLaszlo.IsGlueableFor R S _ _ (algebraMap R S).toAlgebra M _ _ f := by
  have hinst : (algebraMap R S).toAlgebra = (inferInstance : Algebra R S) :=
    Algebra.algebra_ext _ _ fun _ ↦ rfl
  rwa [hinst]

/-- **A glueable algebra has glueable global sections**, read on the object `Spec A` of the site:
`AlgebraicGeometry.Scheme.ΓSpecIso` identifies the global sections of `Spec A` with `A`
compatibly with the two structure maps from `R`. -/
theorem isGlueableGlobalSections_specSite {R R' A : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] [CommRing A] [Algebra R A] (f : R) (B : BigFppfSite.{u})
    (hX : B.Contains (Spec (.of R))) (hA : B.Contains (Spec (.of A)))
    (h : _root_.BeauvilleLaszlo.IsGlueableFor (S := R') A f) :
    AlgebraicGeometry.Space.IsGlueableGlobalSections (algebraMap R R') f B hX
      (AlgebraicGeometry.Space.specSite B hX hA) := by
  let algΓ : Algebra R Γ(Spec (CommRingCat.of A), ⊤) :=
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop).hom).toAlgebra
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop) ≫
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom = CommRingCat.ofHom (algebraMap R A) := by
    rw [Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hΓ : _root_.BeauvilleLaszlo.IsGlueableFor (S := R')
      Γ(Spec (CommRingCat.of A), ⊤) f := by
    refine isGlueableFor_of_ringEquiv_comm f
      (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm (fun r ↦ ?_) h
    have h3 := congrArg (fun z : CommRingCat.of R ⟶ CommRingCat.of A ↦ z.hom r) h2
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
    exact (RingEquiv.symm_apply_eq _).mpr h3.symm
  change @_root_.BeauvilleLaszlo.IsGlueableFor R R' _ _ (algebraMap R R').toAlgebra
    Γ(Spec (CommRingCat.of A), ⊤) _ _ f
  exact isGlueableFor_toAlgebra f hΓ

/-- **The algebraic space represented by `Spec A` is glueable as soon as `A` is.** The space is
covered by `Spec A` itself, so Stacks 0F9P reduces glueability to that of the global sections of
`Spec A`. -/
theorem isGlueableAlgebraicSpace_specSpace {R R' A : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] [CommRing A] [Algebra R A] (f : R)
    (hpair : _root_.BeauvilleLaszlo.IsGlueingPair (algebraMap R R') f) (B : BigFppfSite.{u})
    (hX : B.Contains (Spec (.of R))) (hA : B.Contains (Spec (.of A)))
    (h : _root_.BeauvilleLaszlo.IsGlueableFor (S := R') A f) :
    AlgebraicGeometry.Space.IsGlueableAlgebraicSpace (algebraMap R R') f B hX
      (specSpace B hX hA) :=
  isGlueableAlgebraicSpace_spaceOfSite (algebraMap R R') f hpair B hX
    (AlgebraicGeometry.Space.specSite B hX hA) inferInstance
    (isGlueableGlobalSections_specSite f B hX hA h) (isAlgebraicSpace_yoneda _ _ _ _)

/-! ### The glued algebra -/

/-- **The Beauville--Laszlo theorem for algebras, with its base changes as squares of
`CommRingCat`.** This is `BeauvilleLaszlo.exists_glued_of_cartesianDatum` with the two squares
exhibiting `A₁` and `A'` as base changes of the glued algebra `A` put in the form
`BeauvilleLaszlo.Space.nonempty_glueingDataIso` asks for, and with the two `R`-algebra structures
on `A₁` and `A'` — which the geometry does not provide — installed here. -/
theorem exists_glued_of_pushoutSquares {R R' A₁ A' C₁ C₂ : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] (f : R)
    (hpair : _root_.BeauvilleLaszlo.IsGlueingPair (algebraMap R R') f)
    [CommRing A₁] [Algebra (Localization.Away f) A₁]
    [CommRing A'] [Algebra R' A']
    [CommRing C₁] [Algebra (Localization.Away ((algebraMap R R') f)) C₁]
      [Algebra (Localization.Away f) C₁] [Algebra A₁ C₁]
      [IsScalarTower (Localization.Away f)
        (Localization.Away ((algebraMap R R') f)) C₁]
      [IsScalarTower (Localization.Away f) A₁ C₁]
    [CommRing C₂] [Algebra (Localization.Away ((algebraMap R R') f)) C₂]
      [Algebra R' C₂] [Algebra A' C₂]
      [IsScalarTower R' (Localization.Away ((algebraMap R R') f)) C₂]
      [IsScalarTower R' A' C₂]
    (h₁ : Algebra.IsPushout (Localization.Away f)
      (Localization.Away ((algebraMap R R') f)) A₁ C₁)
    (h₂ : Algebra.IsPushout R' (Localization.Away ((algebraMap R R') f)) A' C₂)
    (ψ : C₂ ≃ₐ[Localization.Away ((algebraMap R R') f)] C₁) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra A A₁) (_ : Algebra A A'),
      _root_.BeauvilleLaszlo.IsGlueableFor (S := R') A f ∧
      Cardinal.mk A ≤ max Cardinal.aleph0 (max (Cardinal.mk A') (Cardinal.mk A₁)) ∧
      IsPushout (CommRingCat.ofHom (algebraMap R A))
          (CommRingCat.ofHom (algebraMap R (Localization.Away f)))
          (CommRingCat.ofHom (algebraMap A A₁))
          (CommRingCat.ofHom (algebraMap (Localization.Away f) A₁)) ∧
      IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R R'))
          (CommRingCat.ofHom (algebraMap A A')) (CommRingCat.ofHom (algebraMap R' A')) ∧
      ∀ x : A, ψ (algebraMap A' C₂ (algebraMap A A' x)) =
        algebraMap A₁ C₁ (algebraMap A A₁ x) := by
  let : Algebra R A₁ := ((algebraMap (Localization.Away f) A₁).comp
    (algebraMap R (Localization.Away f))).toAlgebra
  have : IsScalarTower R (Localization.Away f) A₁ :=
    IsScalarTower.of_algebraMap_eq' (RingHom.algebraMap_toAlgebra _)
  let : Algebra R A' := ((algebraMap R' A').comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' A' :=
    IsScalarTower.of_algebraMap_eq' (RingHom.algebraMap_toAlgebra _)
  obtain ⟨A, _, _, _, _, _, _, hglue, hpA', hpA₁, hcard, he⟩ :=
    _root_.BeauvilleLaszlo.exists_glued_of_cartesianDatum f hpair h₁ h₂ ψ
  have := hpA₁.symm
  have := hpA'.symm
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, hglue, hcard,
    CommRingCat.isPushout_of_isPushout R A (Localization.Away f) A₁,
    CommRingCat.isPushout_of_isPushout R A R' A', he⟩

/-! ### Essential surjectivity -/

/-- **A cartesian glueing triple with affine components is the triple of a glueable affine
algebraic space.** The two outer components are presented as `Spec A₁` and `Spec A'`, their base
changes to `R'_f` as the two tensor products `C₁` and `C₂`, and the glueing isomorphism of the
triple as the isomorphism `BeauvilleLaszlo.Space.glueingPsi : C₂ ≃ C₁` of `R'_f`-algebras;
`BeauvilleLaszlo.Space.exists_glued_of_pushoutSquares` glues the `R`-algebra `A` out of that
datum, its cardinality bound puts `Spec A` in the site, and
`BeauvilleLaszlo.Space.nonempty_glueingDataIso` identifies the triple of `Spec A` with the given
one. -/
theorem exists_iso_of_affineComponents {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] (f : R)
    (hpair : _root_.BeauvilleLaszlo.IsGlueingPair (algebraMap R R') f)
    (B : BigFppfSite.{u})
    (hX : B.Contains (Spec (.of R)))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R')))
    (hU' : B.Contains (Spec (.of (Localization.Away ((algebraMap R R') f)))))
    (hcomm : (AlgebraicGeometry.Space.specSite B hU hU').hom ≫
          (AlgebraicGeometry.Space.specSite B hX hU).hom =
        (AlgebraicGeometry.Space.specSite B hX' hU').hom ≫
          (AlgebraicGeometry.Space.specSite B hX hX').hom)
    (G : GlueingFunctorSpec B (Spec (.of (Localization.Away ((algebraMap R R') f))))
      (Spec (.of (Localization.Away f))) (Spec (.of R')) (Spec (.of R)) hU' hU hX' hX
      (AlgebraicGeometry.Space.specSite B hU hU').hom
      (AlgebraicGeometry.Space.specSite B hX' hU').hom
      (AlgebraicGeometry.Space.specSite B hX hU).hom
      (AlgebraicGeometry.Space.specSite B hX hX').hom hcomm)
    (Z : GlueingData B (Spec (.of (Localization.Away ((algebraMap R R') f))))
      (Spec (.of (Localization.Away f))) (Spec (.of R')) hU' hU hX'
      (AlgebraicGeometry.Space.specSite B hU hU').hom
      (AlgebraicGeometry.Space.specSite B hX' hU').hom)
    (hZU : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of (Localization.Away f))) hU
      ((overU B (Spec (.of (Localization.Away ((algebraMap R R') f))))
        (Spec (.of (Localization.Away f))) (Spec (.of R')) hU' hU hX'
        (AlgebraicGeometry.Space.specSite B hU hU').hom
        (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj Z).1)
    (hZX' : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R')) hX'
      ((overX' B (Spec (.of (Localization.Away ((algebraMap R R') f))))
        (Spec (.of (Localization.Away f))) (Spec (.of R')) hU' hU hX'
        (AlgebraicGeometry.Space.specSite B hU hU').hom
        (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj Z).1) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (hA : B.Contains (Spec (.of A))),
      _root_.BeauvilleLaszlo.IsGlueableFor (S := R') A f ∧
      Nonempty (G.functor.obj (specSpace B hX hA) ≅ Z) := by
  obtain ⟨A₁, _, _, hA₁, ⟨e₁⟩⟩ :=
    AlgebraicGeometry.Space.exists_specSite_iso_of_isAffineSpace B hU _ hZU
  obtain ⟨A', _, _, hA', ⟨e₂⟩⟩ :=
    AlgebraicGeometry.Space.exists_specSite_iso_of_isAffineSpace B hX' _ hZX'
  have hC₁ : B.Contains (Spec (.of
      (Localization.Away ((algebraMap R R') f) ⊗[Localization.Away f] A₁))) :=
    contains_spec_tensorProduct B hU' hA₁
  have hC₂ : B.Contains (Spec (.of (Localization.Away ((algebraMap R R') f) ⊗[R'] A'))) :=
    contains_spec_tensorProduct B hU' hA'
  have hp₂ := CommRingCat.isPushout_of_isPushout (Localization.Away f) A₁
    (Localization.Away ((algebraMap R R') f))
    (Localization.Away ((algebraMap R R') f) ⊗[Localization.Away f] A₁)
  have hp₄ := CommRingCat.isPushout_of_isPushout R' A'
    (Localization.Away ((algebraMap R R') f))
    (Localization.Away ((algebraMap R R') f) ⊗[R'] A')
  have eV : (overU B (Spec (.of (Localization.Away ((algebraMap R R') f))))
        (Spec (.of (Localization.Away f))) (Spec (.of R')) hU' hU hX'
        (AlgebraicGeometry.Space.specSite B hU hU').hom
        (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj Z ≅
      spaceOfSite B (Spec (.of (Localization.Away f))) hU
        (AlgebraicGeometry.Space.specSite B hU hA₁)
        (isAlgebraicSpace_yoneda B (Spec (.of (Localization.Away f))) hU _) :=
    ObjectProperty.isoMk _ (e₁ ≪≫ (schemeSpaceIso _).symm)
  have eW : (overX' B (Spec (.of (Localization.Away ((algebraMap R R') f))))
        (Spec (.of (Localization.Away f))) (Spec (.of R')) hU' hU hX'
        (AlgebraicGeometry.Space.specSite B hU hU').hom
        (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj Z ≅
      spaceOfSite B (Spec (.of R')) hX' (AlgebraicGeometry.Space.specSite B hX' hA')
        (isAlgebraicSpace_yoneda B (Spec (.of R')) hX' _) :=
    ObjectProperty.isoMk _ (e₂ ≪≫ (schemeSpaceIso _).symm)
  obtain ⟨A, _, _, _, _, hglue, hcard, hp₁, hp₃, he⟩ :=
    exists_glued_of_pushoutSquares (A₁ := A₁) (A' := A')
      (C₁ := Localization.Away ((algebraMap R R') f) ⊗[Localization.Away f] A₁)
      (C₂ := Localization.Away ((algebraMap R R') f) ⊗[R'] A')
      f hpair inferInstance inferInstance
      (glueingPsi (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁) (hA' := hA')
        (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄) (Z := Z) (eV := eV) (eW := eW))
  have hA : B.Contains (Spec (.of A)) :=
    BigFppfSite.contains_spec_of_mk_lt_cutoff B (hcard.trans_lt
      (max_lt B.aleph0_lt_cutoff (max_lt (BigFppfSite.mk_lt_cutoff_of_contains_spec B hA')
        (BigFppfSite.mk_lt_cutoff_of_contains_spec B hA₁))))
  exact ⟨A, inferInstance, inferInstance, hA, hglue,
    nonempty_glueingDataIso B hX hU hX' hU' hA hA₁ hA' hC₁ hC₂ hp₂ hp₄ Z eV eW hp₁ hp₃
      hcomm G he⟩

/-- **Stacks 0F9Q, the essential surjectivity clause.** The restriction of a glueing functor of
Stacks 0F9N to the affine algebraic spaces over `Spec R` which are glueable for the pair is
essentially surjective onto the cartesian glueing triples with affine components. -/
@[stacks 0F9Q "the restricted functor is essentially surjective"]
theorem essSurj_affineGlueableRestriction {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] (f : R)
    (hpair : _root_.BeauvilleLaszlo.IsGlueingPair (algebraMap R R') f)
    (B : BigFppfSite.{u})
    (hX : B.Contains (Spec (.of R)))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R')))
    (hU' : B.Contains (Spec (.of (Localization.Away ((algebraMap R R') f)))))
    (hcomm : (AlgebraicGeometry.Space.specSite B hU hU').hom ≫
          (AlgebraicGeometry.Space.specSite B hX hU).hom =
        (AlgebraicGeometry.Space.specSite B hX' hU').hom ≫
          (AlgebraicGeometry.Space.specSite B hX hX').hom)
    (G : GlueingFunctorSpec B (Spec (.of (Localization.Away ((algebraMap R R') f))))
      (Spec (.of (Localization.Away f))) (Spec (.of R')) (Spec (.of R)) hU' hU hX' hX
      (AlgebraicGeometry.Space.specSite B hU hU').hom
      (AlgebraicGeometry.Space.specSite B hX' hU').hom
      (AlgebraicGeometry.Space.specSite B hX hU).hom
      (AlgebraicGeometry.Space.specSite B hX hX').hom hcomm) :
    (affineGlueableRestriction (g := algebraMap R R') (f := f) G).EssSurj := by
  refine ⟨fun Z ↦ ?_⟩
  obtain ⟨A, _, _, hA, hglue, ⟨e⟩⟩ :=
    exists_iso_of_affineComponents f hpair B hX hU hX' hU' hcomm G Z.1 Z.2.1 Z.2.2.2
  exact ⟨⟨specSpace B hX hA,
    schemeSpace_obj (AlgebraicGeometry.Space.specSite B hX hA) ▸
      AlgebraicGeometry.Space.isAffineSpace_yoneda B (Spec (.of R)) hX _ inferInstance,
    isGlueableAlgebraicSpace_specSpace f hpair B hX hA hglue⟩,
    ⟨ObjectProperty.isoMk _ e⟩⟩

end BeauvilleLaszlo.Space

end
