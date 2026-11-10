module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.DomainBaseDescent
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricIrreducibleComponents.FunctionField
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced
public import StacksFrontier.RingTheory.GeometricallyIntegral.Defs

/-!
# The residue field at the generic point of a scheme with geometrically integral generic fibre

Let `R` be a domain with fraction field `K`, let `f : X ⟶ Spec R` be a morphism locally of finite
type with `X` integral, and suppose the generic point of `X` lies over the generic point `η` of
`Spec R`. The generic fibre `f.fiber η` is then an integral `K`-scheme whose generic point is
carried to the generic point of `X` by the inclusion of the fibre, so the residue field of `X` at
its generic point is the function field of the generic fibre. When the generic fibre is
geometrically irreducible and geometrically reduced over `K`, that function field is a
geometrically integral extension of `K`, and in particular stays a domain after base change to
an algebraic closure of `K`.

## Main results

* `AlgebraicGeometry.genericResidueFieldIsDomainTensor`: the residue field of `X` at its generic
  point stays a domain after base change to an algebraic closure of `K`.
* `AlgebraicGeometry.geometricallyIrreducibleAfterShrinkingOverDomain` and
  `AlgebraicGeometry.geometricallyIrreducibleAfterShrinking`: **Stacks Tag 0559**, over a domain
  base and in general.

## Implementation notes

Geometric irreducibility of the function field of the generic fibre is read off the fibre by
`AlgebraicGeometry.geometricallyIrreducible_tfae_functionField`, and geometric reducedness by
`AlgebraicGeometry.isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk`, which speaks
about the local ring rather than the residue field; the two agree at the generic point of an
integral scheme. Both are stated for the algebra structure obtained by evaluating global
sections, whereas the statement to be proved uses the residue field map of `f`. The two agree
because a ring homomorphism out of `K` is determined by its restriction to `R`, `K` being a
field of fractions of `R`.

## References

* [Stacks Project, Tag 054Q](https://stacks.math.columbia.edu/tag/054Q)
* [Stacks Project, Tag 035W](https://stacks.math.columbia.edu/tag/035W)
* [Stacks Project, Tag 05DY](https://stacks.math.columbia.edu/tag/05DY)
* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559), the first proof
-/

@[expose] public section

open CategoryTheory CommRingCat

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- Global evaluation at a point is unchanged by the comparison isomorphism of residue fields
along an equality of points. -/
@[reassoc]
theorem Γevaluation_residueFieldCongr_inv {Y : Scheme.{u}} {y z : Y} (h : y = z) :
    Y.Γevaluation z ≫ (Y.residueFieldCongr h).inv = Y.Γevaluation y := by
  subst h
  simp

/-- The canonical morphism from the spectrum of a residue field of an affine scheme is the
spectrum of the canonical map of the base ring into that residue field. -/
theorem fromSpecResidueField_eq_specMap (R : CommRingCat.{u}) (x : Spec R) :
    (Spec R).fromSpecResidueField x =
      Spec.map (CommRingCat.ofHom (@algebraMap ↥R ↥((Spec R).residueField x) _ _
        (specResidueFieldAlgebra R x))) := by
  have : x.asIdeal.IsPrime := x.isPrime
  have h : CommRingCat.ofHom (@algebraMap ↥R ↥((Spec R).residueField x) _ _
        (specResidueFieldAlgebra R x)) =
      CommRingCat.ofHom (algebraMap ↥R x.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso R x).inv := by
    rw [Scheme.Spec.algebraMap_residueFieldIso_inv]
    rfl
  rw [h, Spec.map_comp, Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]

/-- The canonical map of a ring into a residue field of its spectrum, read on global sections
through the canonical morphism out of the spectrum of that residue field. -/
@[reassoc]
theorem algebraMap_specResidueField_comp_ΓSpecIso_inv (R : CommRingCat.{u}) (x : Spec R) :
    CommRingCat.ofHom (@algebraMap ↥R ↥((Spec R).residueField x) _ _
        (specResidueFieldAlgebra R x)) ≫
      (Scheme.ΓSpecIso ((Spec R).residueField x)).inv =
      (Scheme.ΓSpecIso R).inv ≫ ((Spec R).fromSpecResidueField x).appTop := by
  rw [fromSpecResidueField_eq_specMap R x]
  exact Scheme.ΓSpecIso_inv_naturality _

/-- `AlgebraicGeometry.algebraMap_comp_residueFieldMapOfEq` with the algebra structure on the
residue field of the base written out, so that it can be composed on the right. -/
@[reassoc]
theorem algebraMap_comp_residueFieldMapOfEq' (R : CommRingCat.{u}) {X : Scheme.{u}}
    (f : X ⟶ Spec R) {x : X} {s : Spec R} (hs : f x = s) :
    CommRingCat.ofHom (@algebraMap ↥R ↥((Spec R).residueField s) _ _
        (specResidueFieldAlgebra R s)) ≫ f.residueFieldMapOfEq hs =
      (Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.Γevaluation x :=
  algebraMap_comp_residueFieldMapOfEq R f hs

/-- The algebra structure on a local ring of a scheme over a field coming from the stalk map of
the structure morphism is the one coming from germs of global sections. -/
theorem stalkAlgebra_eq_germ_appTop {k : Type u} [Field k] {Y : Scheme.{u}}
    (h : Y ⟶ Spec (.of k)) (y : Y) :
    ((h.stalkMap y).hom.comp (@algebraMap k ↥((Spec (.of k)).presheaf.stalk (h.base y)) _ _
        (StructureSheaf.stalkAlgebra k (h.base y)))).toAlgebra =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ h.appTop ≫
        Y.presheaf.germ ⊤ y trivial).hom.toAlgebra := by
  refine congrArg RingHom.toAlgebra ?_
  have hcat : CommRingCat.ofHom (@algebraMap k ↥((Spec (.of k)).presheaf.stalk (h.base y)) _ _
        (StructureSheaf.stalkAlgebra k (h.base y))) ≫ h.stalkMap y =
      (Scheme.ΓSpecIso (.of k)).inv ≫ h.appTop ≫ Y.presheaf.germ ⊤ y trivial := by
    change ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ (h.base y) trivial) ≫ h.stalkMap y = _
    rw [Category.assoc, Scheme.Hom.germ_stalkMap h ⊤ y trivial]
    rfl
  exact congrArg CommRingCat.Hom.hom hcat

/-- The function field of a geometrically reduced integral scheme over a field is geometrically
reduced over that field. -/
theorem geometricallyReduced_residueField_genericPoint (k : Type u) [Field k] {Y : Scheme.{u}}
    (h : Y ⟶ Spec (.of k)) [IsIntegral Y] [GeometricallyReduced h] :
    letI : Algebra k ↥(Y.residueField (genericPoint Y)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ h.appTop ≫
        Y.Γevaluation (genericPoint Y)).hom.toAlgebra
    _root_.GeometricallyReduced.{u, u, u} k ↥(Y.residueField (genericPoint Y)) := by
  let algStalk : Algebra k ↥(Y.presheaf.stalk (genericPoint Y)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ h.appTop ≫
      Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom.toAlgebra
  let algRes : Algebra k ↥(Y.residueField (genericPoint Y)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ h.appTop ≫
      Y.Γevaluation (genericPoint Y)).hom.toAlgebra
  have h035 : Algebra.IsGeometricallyReduced k ↥(Y.presheaf.stalk (genericPoint Y)) := by
    have hpt := (isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk h
      (genericPoint Y)).mp
      ((geometricallyReduced_iff_forall_isGeometricallyReducedAt h).mp ‹_› (genericPoint Y))
    rwa [stalkAlgebra_eq_germ_appTop h (genericPoint Y)] at hpt
  have hall : ∀ (L : Type u) [Field L] [Algebra k L],
      _root_.IsReduced (L ⊗[k] ↥(Y.presheaf.stalk (genericPoint Y))) :=
    ((Algebra.isGeometricallyReduced_tfae k (ringExpChar k)
      ↥(Y.presheaf.stalk (genericPoint Y)) (perfectClosure k (AlgebraicClosure k))
      (AlgebraicClosure k)).out 6 5).mp h035
  have := isIso_residue_genericPoint Y
  let e : ↥(Y.presheaf.stalk (genericPoint Y)) ≃ₐ[k] ↥(Y.residueField (genericPoint Y)) :=
    AlgEquiv.ofRingEquiv
      (f := (asIso (Y.residue (genericPoint Y))).commRingCatIsoToRingEquiv) fun _ ↦ rfl
  intro L _ _
  exact isReduced_of_ringEquiv
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := k) (A₁ := L)) e.symm).toRingEquiv
    (hall L)

/-- Two morphisms out of the residue field of `Spec R` at its generic point, for `R` a domain,
agree as soon as they agree on `R`. -/
theorem hom_ext_specResidueField_genericPoint (R : CommRingCat.{u}) [IsDomain R]
    {W : CommRingCat.{u}} (φ ψ : (Spec R).residueField (genericPoint (Spec R)) ⟶ W)
    (h : CommRingCat.ofHom (@algebraMap ↥R
          ↥((Spec R).residueField (genericPoint (Spec R))) _ _
          (specResidueFieldAlgebra R (genericPoint (Spec R)))) ≫ φ =
        CommRingCat.ofHom (@algebraMap ↥R
          ↥((Spec R).residueField (genericPoint (Spec R))) _ _
          (specResidueFieldAlgebra R (genericPoint (Spec R)))) ≫ ψ) : φ = ψ := by
  let _ := specResidueFieldAlgebra R (genericPoint (Spec R))
  have : IsFractionRing ↥R ↥((Spec R).residueField (genericPoint (Spec R))) :=
    isFractionRing_specResidueField_genericPoint R
  exact CommRingCat.hom_ext (IsLocalization.ringHom_ext (nonZeroDivisors ↥R)
    (congrArg CommRingCat.Hom.hom h))

section Fibre

variable {R : CommRingCat.{u}} [IsDomain R] {X : Scheme.{u}} [IrreducibleSpace X]
  (f : X ⟶ Spec R) (hgen : f (genericPoint X) = genericPoint (Spec R))

include hgen in
/-- The generic point of the generic fibre of a morphism from an irreducible scheme is carried to
the generic point of the source by the inclusion of the fibre. -/
theorem fiberι_genericPoint_fiber
    [IrreducibleSpace (f.fiber (genericPoint (Spec R)))] :
    f.fiberι (genericPoint (Spec R)) (genericPoint (f.fiber (genericPoint (Spec R)))) =
      genericPoint X := by
  obtain ⟨y, hy⟩ : genericPoint X ∈ Set.range (f.fiberι (genericPoint (Spec R))) := by
    rw [f.range_fiberι (genericPoint (Spec R))]
    exact hgen
  have hmem : genericPoint X ∈ closure ({f.fiberι (genericPoint (Spec R))
                                          (genericPoint (f.fiber (genericPoint (Spec R))))} :
      Set X) := by
    have hsub : f.fiberι (genericPoint (Spec R)) ''
          closure ({genericPoint (f.fiber (genericPoint (Spec R)))} : Set _) ⊆
        closure (f.fiberι (genericPoint (Spec R)) ''
          ({genericPoint (f.fiber (genericPoint (Spec R)))} : Set _)) :=
      image_closure_subset_closure_image (f.fiberι (genericPoint (Spec R))).continuous
    rw [Set.image_singleton] at hsub
    exact hsub ⟨y, by simp, hy⟩
  have hcl : IsGenericPoint (f.fiberι (genericPoint (Spec R))
      (genericPoint (f.fiber (genericPoint (Spec R))))) Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← genericPoint_closure X]
    exact closure_minimal (Set.singleton_subset_iff.mpr hmem) isClosed_closure
  exact hcl.eq (genericPoint_spec X)

/-- The identification of the residue field of `X` at its generic point with the residue field at
the generic point of the generic fibre, through the inclusion of the fibre. -/
noncomputable def genericFiberResidueFieldMap
    [IrreducibleSpace (f.fiber (genericPoint (Spec R)))] :
    X.residueField (genericPoint X) ⟶
      (f.fiber (genericPoint (Spec R))).residueField
        (genericPoint (f.fiber (genericPoint (Spec R)))) :=
  (X.residueFieldCongr (fiberι_genericPoint_fiber f hgen)).inv ≫
    (f.fiberι (genericPoint (Spec R))).residueFieldMap _

/-- The map `genericFiberResidueFieldMap` from the residue field of `X` at its generic point to the
residue field at the generic point of the generic fibre is an isomorphism. -/
instance isIso_genericFiberResidueFieldMap
    [IrreducibleSpace (f.fiber (genericPoint (Spec R)))] :
    IsIso (genericFiberResidueFieldMap f hgen) := by
  have : IsIso ((f.fiberι (genericPoint (Spec R))).residueFieldMap
      (genericPoint (f.fiber (genericPoint (Spec R))))) :=
    isIso_residueFieldMap_of_isPreimmersion _ _
  change IsIso ((X.residueFieldCongr (fiberι_genericPoint_fiber f hgen)).inv ≫
    (f.fiberι (genericPoint (Spec R))).residueFieldMap
      (genericPoint (f.fiber (genericPoint (Spec R)))))
  infer_instance

/-- The identification of the residue field of `X` at its generic point with the residue field at
the generic point of the generic fibre is one of algebras over the residue field of the base at
its generic point. -/
theorem residueFieldMapOfEq_comp_genericFiberResidueFieldMap
    [IrreducibleSpace (f.fiber (genericPoint (Spec R)))] :
    f.residueFieldMapOfEq hgen ≫ genericFiberResidueFieldMap f hgen =
      (Scheme.ΓSpecIso ((Spec R).residueField (genericPoint (Spec R)))).inv ≫
        (f.fiberToSpecResidueField (genericPoint (Spec R))).appTop ≫
        (f.fiber (genericPoint (Spec R))).Γevaluation
          (genericPoint (f.fiber (genericPoint (Spec R)))) := by
  refine hom_ext_specResidueField_genericPoint R _ _ ?_
  rw [genericFiberResidueFieldMap]
  have hfac : f.appTop ≫ (f.fiberι (genericPoint (Spec R))).appTop ≫
        (f.fiber (genericPoint (Spec R))).Γevaluation
          (genericPoint (f.fiber (genericPoint (Spec R)))) =
      ((Spec R).fromSpecResidueField (genericPoint (Spec R))).appTop ≫
        (f.fiberToSpecResidueField (genericPoint (Spec R))).appTop ≫
        (f.fiber (genericPoint (Spec R))).Γevaluation
          (genericPoint (f.fiber (genericPoint (Spec R)))) := by
    rw [← Category.assoc, ← Category.assoc, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
      Scheme.Hom.fiber_fac]
  simp only [algebraMap_comp_residueFieldMapOfEq'_assoc,
    Γevaluation_residueFieldCongr_inv_assoc (fiberι_genericPoint_fiber f hgen),
    Scheme.Γevaluation_naturality, algebraMap_specResidueField_comp_ΓSpecIso_inv_assoc]
  rw [hfac]

end Fibre

/-- **The input of Step B of Stacks Tag 0559.** For a morphism `f : X ⟶ Spec R` locally of finite
type from an integral scheme to the spectrum of a domain, whose generic point lies over the
generic point of `Spec R` and whose generic fibre is geometrically irreducible and geometrically
reduced, the residue field of `X` at its generic point stays a domain after base change to an
algebraic closure of the residue field of `Spec R` at its generic point. -/
theorem genericResidueFieldIsDomainTensor : GenericResidueFieldIsDomainTensor.{u} := by
  intro R _ X f _ _ _ hgen hgi hgr
  have := hgi
  have := hgr
  have hirr : IrreducibleSpace (f.fiber (genericPoint (Spec R))) :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton
      (f := f.fiberToSpecResidueField (genericPoint (Spec R)))
  have hred : IsReduced (f.fiber (genericPoint (Spec R))) :=
    self_of_isIntegral_of_geometrically
      (GeometricallyReduced.geometrically_isReduced
        (f := f.fiberToSpecResidueField (genericPoint (Spec R))))
  have hint : IsIntegral (f.fiber (genericPoint (Spec R))) :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  let algFib : Algebra ↥((Spec R).residueField (genericPoint (Spec R)))
      ↥((f.fiber (genericPoint (Spec R))).residueField
        (genericPoint (f.fiber (genericPoint (Spec R))))) :=
    ((Scheme.ΓSpecIso ((Spec R).residueField (genericPoint (Spec R)))).inv ≫
      (f.fiberToSpecResidueField (genericPoint (Spec R))).appTop ≫
      (f.fiber (genericPoint (Spec R))).Γevaluation
        (genericPoint (f.fiber (genericPoint (Spec R))))).hom.toAlgebra
  -- Geometric irreducibility of the function field of the generic fibre, by Tag 054Q.
  have hGI : _root_.GeometricallyIrreducible.{u, u, u}
      ↥((Spec R).residueField (genericPoint (Spec R)))
      ↥((f.fiber (genericPoint (Spec R))).residueField
        (genericPoint (f.fiber (genericPoint (Spec R))))) := by
    refine (Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct
      _ _).mp ?_
    exact ((geometricallyIrreducible_tfae_functionField
      ↥((Spec R).residueField (genericPoint (Spec R))) (f.fiber (genericPoint (Spec R)))
      (f.fiberToSpecResidueField (genericPoint (Spec R)))
      (genericPoint (f.fiber (genericPoint (Spec R))))
      (genericPoint_spec (f.fiber (genericPoint (Spec R))))).out 1 2).mp hgi
  -- Geometric reducedness of the function field of the generic fibre, by Tag 035W.
  have hGR : _root_.GeometricallyReduced.{u, u, u}
      ↥((Spec R).residueField (genericPoint (Spec R)))
      ↥((f.fiber (genericPoint (Spec R))).residueField
        (genericPoint (f.fiber (genericPoint (Spec R))))) :=
    geometricallyReduced_residueField_genericPoint
      ↥((Spec R).residueField (genericPoint (Spec R)))
      (f.fiberToSpecResidueField (genericPoint (Spec R)))
  -- Tag 05DY, applied to an algebraic closure.
  have hdom := (geometricallyIntegral_iff_irreducible_and_reduced
    ↥((Spec R).residueField (genericPoint (Spec R)))
    ↥((f.fiber (genericPoint (Spec R))).residueField
      (genericPoint (f.fiber (genericPoint (Spec R)))))).mpr ⟨hGI, hGR⟩
    (AlgebraicClosure ↥((Spec R).residueField (genericPoint (Spec R))))
  -- Transport along the identification of the residue field with the function field.
  let _ := residueFieldAlgebraOfEq f hgen
  let e : ↥(X.residueField (genericPoint X)) ≃ₐ[↥((Spec R).residueField
        (genericPoint (Spec R)))]
      ↥((f.fiber (genericPoint (Spec R))).residueField
        (genericPoint (f.fiber (genericPoint (Spec R))))) :=
    AlgEquiv.ofRingEquiv
      (f := (asIso (genericFiberResidueFieldMap f hgen)).commRingCatIsoToRingEquiv)
      fun r ↦ congrArg
        (fun φ : (Spec R).residueField (genericPoint (Spec R)) ⟶
          (f.fiber (genericPoint (Spec R))).residueField
            (genericPoint (f.fiber (genericPoint (Spec R)))) ↦ φ.hom r)
        (residueFieldMapOfEq_comp_genericFiberResidueFieldMap f hgen)
  exact Function.Injective.isDomain
    (Algebra.TensorProduct.congr e
      (AlgEquiv.refl
        (R := ↥((Spec R).residueField (genericPoint (Spec R))))
        (A₁ := AlgebraicClosure ↥((Spec R).residueField (genericPoint (Spec R)))))).toRingHom
    (Algebra.TensorProduct.congr e _).injective

/-- **Stacks Tag 0559 over a domain base.** An integral scheme, flat and of finite presentation
over the spectrum of a domain, whose fibre over the generic point of the base is geometrically
irreducible and geometrically reduced, has geometrically irreducible fibres over a nonempty open
subscheme of the base. -/
theorem geometricallyIrreducibleAfterShrinkingOverDomain :
    GeometricallyIrreducibleAfterShrinkingOverDomain.{u} :=
  geometricallyIrreducibleAfterShrinkingOverDomain_of_isDomainTensor
    genericResidueFieldIsDomainTensor

/-- **Stacks Project, Tag 0559.** A morphism of finite type onto an irreducible base whose
fibre over the generic point is geometrically irreducible has geometrically irreducible fibres
over a nonempty open subscheme of the base. -/
@[stacks 0559]
theorem geometricallyIrreducibleAfterShrinking :
    GeometricallyIrreducibleAfterShrinking.{u} :=
  geometricallyIrreducibleAfterShrinking_of_isDomainTensor genericResidueFieldIsDomainTensor

end AlgebraicGeometry

end
