module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Determinant
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.GeneralLinear
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Multiplicative

/-!
# The determinant after base change

For every scheme `S`, the determinant of the general linear group gives a morphism of group
schemes from `GLₙ` to the multiplicative group over `S`.

## Main results

* `AlgebraicGeometry.determinantGroupSchemeMorphismOverULiftIntegers` is the universal
  determinant morphism over `Spec (ULift ℤ)` in the universe of `S`.
* `AlgebraicGeometry.determinantGroupSchemeMorphism` is the group-scheme morphism over `S`.
* `AlgebraicGeometry.determinantGroupSchemeMorphism_isBaseChange` identifies the underlying
  morphism with the pullback of the universal model over every `S`.
* `AlgebraicGeometry.determinantGroupSchemeMorphism_apply` identifies its action on every
  `S`-scheme with the determinant of an invertible matrix.
* `AlgebraicGeometry.determinantGroupSchemeMorphism_baseChange` identifies, in the original
  universe, the morphism with the pullback of the integral determinant.

## Implementation notes

The source and target are the base-changed group schemes of Tags 022W and 022U. The morphism is
constructed by pulling back a universal morphism over `Spec (ULift ℤ)`, so its base-change
identity holds for an arbitrary `S` in the same universe. The functor-of-points assertion
identifies this universal morphism with the determinant. In universe zero a further equation
compares it with the integral determinant through the canonical change-of-coefficients map. All
claims include `n = 0`, where the determinant is one.

## References

* [Stacks Project, Tag 022X](https://stacks.math.columbia.edu/tag/022X)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- The multiplicative group over the universe-lifted integers, as a scheme over that base. -/
noncomputable abbrev multiplicativeGroupOverIntegers :
    Over (Spec (.of (ULift.{u} ℤ))) :=
  multiplicativeGroupULift.asOver (Spec (.of (ULift.{u} ℤ)))

/-- Pulling a global section of an affine scheme back along a morphism into it. -/
noncomputable def specPullback {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) :
    R →+* Scheme.Γ.obj (Opposite.op X) :=
  ((Scheme.ΓSpecIso R).inv ≫ Scheme.Γ.map f.op).hom

private lemma specPullback_comp {R : CommRingCat.{u}} {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Spec R) :
    specPullback (f ≫ g) = (Scheme.Γ.map f.op).hom.comp (specPullback g) := by
  unfold specPullback
  rw [op_comp, Functor.map_comp]
  rfl

private lemma specPullback_specMap {R A : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec A) (g : R ⟶ A) :
    specPullback (f ≫ Spec.map g) = (specPullback f).comp g.hom := by
  unfold specPullback
  dsimp only [Scheme.Γ_obj_op, Scheme.Γ_map_op]
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
    Category.assoc]
  rfl

private lemma pointUnit_val {X : Scheme.{u}} (f : X ⟶ multiplicativeGroupULift) :
    (multiplicativeGroupPointUnit f).val = specPullback f (LaurentPolynomial.T 1) := rfl

/-- Pulling back a point of the multiplicative group pulls back its unit. -/
lemma pointUnit_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ multiplicativeGroupULift) :
    multiplicativeGroupPointUnit (f ≫ g) =
      Units.map (Scheme.Γ.map f.op).hom (multiplicativeGroupPointUnit g) :=
  Units.ext (congrArg (fun h => h (LaurentPolynomial.T 1)) (specPullback_comp f g))

/-- Points of the integral multiplicative group are exactly units in global sections. -/
lemma pointUnit_bijective (X : Scheme.{u}) :
    Function.Bijective (multiplicativeGroupPointUnit (T := X)) := by
  let T : Over X := Over.mk (𝟙 X)
  let e := ((baseChangePointsIsoMultiplicativeGroupPoints X).app (Opposite.op T)).toEquiv
  let d := (baseChangePointsIsoGlobalUnits X).app (Opposite.op T)
  have he (f : T ⟶ Scheme.asOver (multiplicativeGroupBaseChange X) X) :
      multiplicativeGroupPointUnit (e f) = d.hom f := by
    show multiplicativeGroupPointUnit (e f) =
      (baseChangePointsIsoGlobalUnits X).hom.app (Opposite.op T) f
    rw [baseChangePointsIsoGlobalUnits_hom_app]
    congr 1
  have hcomp : multiplicativeGroupPointUnit (T := X) = (fun f => d.hom f) ∘ e.symm := by
    funext f
    have hfe := he (e.symm f)
    rw [Equiv.apply_symm_apply] at hfe
    exact hfe
  rw [hcomp]
  exact (ConcreteCategory.bijective_of_isIso d.hom).comp e.symm.bijective

/-- The unit attached to a product of points is the product of their units. -/
lemma pointUnit_mul {X : Over (Spec (.of (ULift.{u} ℤ)))}
    (f g : X ⟶ multiplicativeGroupOverIntegers) :
    multiplicativeGroupPointUnit (f * g).left =
      multiplicativeGroupPointUnit f.left * multiplicativeGroupPointUnit g.left := by
  let L := LaurentPolynomial (ULift.{u} ℤ)
  let fl : X.left ⟶ multiplicativeGroupULift := f.left
  let gl : X.left ⟶ multiplicativeGroupULift := g.left
  let fgl : X.left ⟶ multiplicativeGroupULift := (f * g).left
  let liftLeft : X.left ⟶ pullback
      (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) L)))
      (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) L))) :=
    (CartesianMonoidalCategory.lift f g).left
  let h : X.left ⟶ Spec (.of (TensorProduct (ULift.{u} ℤ) L L)) :=
    liftLeft ≫ (pullbackSpecIso (ULift.{u} ℤ) L L).hom
  have hmul : fgl = h ≫
      Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom (ULift.{u} ℤ) L)) := by
    dsimp only [fgl, h, liftLeft]
    simp only [CategoryTheory.Hom.mul_def, Over.comp_left, mul_spec_asOver_spec_left]
    exact (Category.assoc _ _ _).symm
  have hf : h ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : L →+* TensorProduct (ULift.{u} ℤ) L L)) =
      fl := by
    dsimp only [h]
    rw [Category.assoc, pullbackSpecIso_hom_fst]
    exact congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst f g)
  have hg : h ≫ Spec.map (CommRingCat.ofHom
      (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
        L →ₐ[ULift.{u} ℤ] TensorProduct (ULift.{u} ℤ) L L))) = gl := by
    dsimp only [h]
    rw [Category.assoc, pullbackSpecIso_hom_snd]
    exact congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd f g)
  apply Units.ext
  rw [Units.val_mul]
  show specPullback fgl (LaurentPolynomial.T 1) =
    specPullback fl (LaurentPolynomial.T 1) * specPullback gl (LaurentPolynomial.T 1)
  rw [hmul, specPullback_specMap, ← hf, ← hg, specPullback_specMap, specPullback_specMap]
  show specPullback h ((Bialgebra.comulAlgHom (ULift.{u} ℤ) L) (LaurentPolynomial.T 1)) =
    specPullback h (Algebra.TensorProduct.includeLeftRingHom (LaurentPolynomial.T 1)) *
      specPullback h (Algebra.TensorProduct.includeRight (LaurentPolynomial.T 1))
  rw [← map_mul]
  congr 1
  simp [L, Algebra.TensorProduct.tmul_mul_tmul]

/-- The group-valued points of the multiplicative group over the universe-lifted integers are
the units in global sections. -/
noncomputable def multiplicativeGroupPointsIso :
    yonedaGrpObj multiplicativeGroupOverIntegers.{u} ≅
      globalUnits (Spec (.of (ULift.{u} ℤ))) := by
  let e (X : (Over (Spec (.of (ULift.{u} ℤ))))ᵒᵖ) :
      (X.unop ⟶ multiplicativeGroupOverIntegers) ≃*
        (Scheme.Γ.obj (Opposite.op X.unop.left))ˣ :=
    MulEquiv.ofBijective
      (MonoidHom.mk' (fun f : X.unop ⟶ multiplicativeGroupOverIntegers =>
        multiplicativeGroupPointUnit f.left) (fun f g => pointUnit_mul f g))
      ((pointUnit_bijective X.unop.left).comp
        (show Function.Bijective
            (fun f : X.unop ⟶ multiplicativeGroupOverIntegers => f.left) from
          ⟨fun _ _ h => Over.OverMorphism.ext h,
            fun f => ⟨Over.homMk f (specULiftZIsTerminal.hom_ext _ _), rfl⟩⟩))
  refine NatIso.ofComponents (fun X => (e X).toGrpIso) fun f => ?_
  ext g
  exact pointUnit_comp f.unop.left g.left

/-- The determinant, as a natural transformation from invertible matrices over global sections
to global units. -/
noncomputable def determinantNaturalTransformation (n : ℕ) (S : Scheme.{u}) :
    generalLinearGroupOverFunctor n S ⟶ globalUnits S where
  app T := GrpCat.ofHom Matrix.GeneralLinearGroup.det
  naturality X Y f := by
    ext g
    exact Matrix.GeneralLinearGroup.map_det _ g

/-- The group-valued points of the integral general linear scheme are invertible matrices over
global sections. -/
noncomputable def generalLinearPointsIso (n : ℕ) :
    yonedaGrpObj (Over.mk (generalLinearStructureMorphism.{u} n)) ≅
      generalLinearGroupOverFunctor n (Spec (.of (ULift.{u} ℤ))) :=
  yonedaGrpObjIsoOfRepresentableBy _ _ (generalLinearOverRepresentableBy n)

private lemma schemeHomRingHomEquiv_eq_specPullback (n : ℕ) {X : Scheme.{u}}
    (f : X ⟶ generalLinearScheme n) :
    schemeHomRingHomEquiv n f = specPullback f := by
  let e := ΓSpec.adjunction.homEquiv X
    (Opposite.op (CommRingCat.of (generalLinearCoordinateRing.{u} n)))
  have h := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (e.symm f).unop
  have he : e (e.symm f).unop.op = f := e.apply_symm_apply f
  change (Scheme.ΓSpecIso _).inv ≫ (e (e.symm f).unop.op).appTop = (e.symm f).unop at h
  rw [he] at h
  exact (congrArg CommRingCat.Hom.hom h).symm

private lemma generalLinearPointsIso_entry (n : ℕ)
    (X : (Over (Spec (.of (ULift.{u} ℤ))))ᵒᵖ)
    (f : X.unop ⟶ Over.mk (generalLinearStructureMorphism n)) (i j : Fin n) :
    ((generalLinearPointsIso n).hom.app X f).val i j =
      (Scheme.Γ.map f.left.op).hom (generalLinearCoordinateSection n i j) := by
  show (localizedPolynomialHomEquiv n _ (schemeHomRingHomEquiv n f.left)).val i j = _
  rw [schemeHomRingHomEquiv_eq_specPullback]
  simp only [localizedPolynomialHomEquiv, generalLinearOfLocalizedPolynomialHom]
  rfl

/-- The determinant morphism of group schemes over the universe-lifted integers. -/
@[stacks 022X "det_after_base_change"]
noncomputable def determinantGroupSchemeMorphismOverULiftIntegers (n : ℕ) :
    Grp.mk (Over.mk (generalLinearStructureMorphism.{u} n)) ⟶
      Grp.mk (multiplicativeGroupULift.asOver (Spec (.of (ULift.{u} ℤ)))) :=
  yonedaGrpFullyFaithful.preimage
    ((generalLinearPointsIso n).hom ≫
      determinantNaturalTransformation n (Spec (.of (ULift.{u} ℤ))) ≫
      multiplicativeGroupPointsIso.inv)

/-- A natural isomorphism of group-valued functors is a section on each component. -/
private lemma hom_app_inv_app_apply {C : Type*} [Category C] {F G : Cᵒᵖ ⥤ GrpCat}
    (e : F ≅ G) (X : Cᵒᵖ) (x : G.obj X) : e.hom.app X (e.inv.app X x) = x :=
  ConcreteCategory.congr_hom (Iso.inv_hom_id (e.app X)) x

private lemma determinantOverIntegers_pointUnit (n : ℕ)
    (X : (Over (Spec (.of (ULift.{u} ℤ))))ᵒᵖ)
    (f : X.unop ⟶ Over.mk (generalLinearStructureMorphism n)) :
    multiplicativeGroupPointUnit
        (f.left ≫ (determinantGroupSchemeMorphismOverULiftIntegers n).hom.hom.left) =
      Matrix.GeneralLinearGroup.det ((generalLinearPointsIso n).hom.app X f) := by
  let G := Over.mk (generalLinearStructureMorphism.{u} n)
  let α := (generalLinearPointsIso n).hom ≫
    determinantNaturalTransformation n (Spec (.of (ULift.{u} ℤ))) ≫
    multiplicativeGroupPointsIso.inv
  have hpre : (determinantGroupSchemeMorphismOverULiftIntegers n).hom.hom =
      α.app (Opposite.op G) (𝟙 G) := rfl
  have hnat : α.app X f = f ≫ α.app (Opposite.op G) (𝟙 G) :=
    (congrArg (fun k : X.unop ⟶ G => α.app X k) (Category.comp_id f)).symm.trans
      (yonedaGrp_naturality α f (𝟙 G))
  show multiplicativeGroupPointUnit
    ((f ≫ (determinantGroupSchemeMorphismOverULiftIntegers n).hom.hom).left) = _
  rw [hpre, ← hnat]
  exact hom_app_inv_app_apply multiplicativeGroupPointsIso X
    (Matrix.GeneralLinearGroup.det (R := Scheme.Γ.obj (Opposite.op X.unop.left))
      ((generalLinearPointsIso n).hom.app X f))

/-- The determinant morphism from the base-changed general linear group scheme to the
base-changed multiplicative group scheme. -/
@[stacks 022X "det_after_base_change"]
noncomputable def determinantGroupSchemeMorphism (n : ℕ) (S : Scheme.{u}) :
    Grp.mk (generalLinearBaseChange n S) ⟶
      Grp.mk (Scheme.asOver (multiplicativeGroupBaseChange S) S) :=
  yonedaGrpFullyFaithful.preimage
    ((baseChangeGroupPointsIso n S).hom ≫ determinantNaturalTransformation n S ≫
      (baseChangePointsIsoGlobalUnits S).inv)

private theorem determinantMorphism_apply (n : ℕ) (S : Scheme.{u})
    (T : (Over S)ᵒᵖ) (f : T.unop ⟶ generalLinearBaseChange n S) :
    (baseChangePointsIsoGlobalUnits S).hom.app T
        (((yonedaGrp.map (determinantGroupSchemeMorphism n S)).app T) f) =
      Matrix.GeneralLinearGroup.det ((baseChangeGroupPointsIso n S).hom.app T f) := by
  have hm : yonedaGrp.map (determinantGroupSchemeMorphism n S) =
      (baseChangeGroupPointsIso n S).hom ≫ determinantNaturalTransformation n S ≫
        (baseChangePointsIsoGlobalUnits S).inv := by
    dsimp only [determinantGroupSchemeMorphism]
    exact yonedaGrpFullyFaithful.map_preimage _
  rw [hm]
  exact hom_app_inv_app_apply (baseChangePointsIsoGlobalUnits S) T
    (Matrix.GeneralLinearGroup.det (R := Scheme.Γ.obj (Opposite.op T.unop.left))
      ((baseChangeGroupPointsIso n S).hom.app T f))

private lemma determinantMorphism_pointUnit (n : ℕ) (S : Scheme.{u}) :
    multiplicativeGroupPointUnit
      ((determinantGroupSchemeMorphism n S).hom.hom.left ≫
        pullback.fst (multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ)))
          (specULiftZIsTerminal.from S)) =
      Matrix.GeneralLinearGroup.det
        ((baseChangeGroupPointsIso n S).hom.app (Opposite.op (generalLinearBaseChange n S))
          (𝟙 _)) := by
  have h := determinantMorphism_apply n S (Opposite.op (generalLinearBaseChange n S)) (𝟙 _)
  change (baseChangePointsIsoGlobalUnits S).hom.app _
    ((𝟙 _) ≫ (determinantGroupSchemeMorphism n S).hom.hom) = _ at h
  rwa [Category.id_comp, baseChangePointsIsoGlobalUnits_hom_app] at h

/-- The underlying scheme morphism is the pullback of the universal determinant
over the universe-lifted integers, for every base scheme in that universe. -/
@[stacks 022X "det_after_base_change"]
theorem determinantGroupSchemeMorphism_isBaseChange (n : ℕ) (S : Scheme.{u}) :
    (determinantGroupSchemeMorphism n S).hom.hom =
      (Over.pullback (specULiftZIsTerminal.from S)).map
        (determinantGroupSchemeMorphismOverULiftIntegers n).hom.hom := by
  let X := generalLinearBaseChange n S
  let f : Over.mk (specULiftZIsTerminal.from X.left) ⟶
      Over.mk (generalLinearStructureMorphism n) :=
    Over.homMk (pullback.fst (generalLinearStructureMorphism n)
      (specULiftZIsTerminal.from S)) (specULiftZIsTerminal.hom_ext _ _)
  have hmatrix : (generalLinearPointsIso n).hom.app _ f =
      (baseChangeGroupPointsIso n S).hom.app (Opposite.op X) (𝟙 _) := by
    apply Units.ext
    ext i j
    rw [generalLinearPointsIso_entry, baseChangeGroupPointsIso_hom_app]
    simp only [f, Over.homMk_left, Over.id_left, Category.id_comp]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply (pointUnit_bijective X.left).injective
    have hmap :
        ((Over.pullback (specULiftZIsTerminal.from S)).map
          (determinantGroupSchemeMorphismOverULiftIntegers n).hom.hom).left ≫
          pullback.fst (multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ)))
            (specULiftZIsTerminal.from S) =
        f.left ≫ (determinantGroupSchemeMorphismOverULiftIntegers n).hom.hom.left :=
      pullback.lift_fst _ _ _
    exact (determinantMorphism_pointUnit n S).trans
      (((determinantOverIntegers_pointUnit n _ f).trans
        (congrArg Matrix.GeneralLinearGroup.det hmatrix)).symm.trans
          (congrArg multiplicativeGroupPointUnit hmap.symm))
  · exact (Over.w (determinantGroupSchemeMorphism n S).hom.hom).trans
      (Over.w ((Over.pullback (specULiftZIsTerminal.from S)).map
        (determinantGroupSchemeMorphismOverULiftIntegers n).hom.hom)).symm

/-- The base-changed determinant sends an invertible matrix over the global sections of
an `S`-scheme to its determinant, viewed as a global unit. -/
@[stacks 022X "det_after_base_change"]
theorem determinantGroupSchemeMorphism_apply (n : ℕ) (S : Scheme.{u})
    (T : (Over S)ᵒᵖ) (f : T.unop ⟶ generalLinearBaseChange n S) :
    (baseChangePointsIsoGlobalUnits S).hom.app T
        (((yonedaGrp.map (determinantGroupSchemeMorphism n S)).app T) f) =
      Matrix.GeneralLinearGroup.det ((baseChangeGroupPointsIso n S).hom.app T f) :=
  determinantMorphism_apply n S T f

private lemma integralPoint_ext {X : Scheme.{0}} (f g : X ⟶ multiplicativeGroup)
    (h : specPullback f (LaurentPolynomial.T 1) =
      specPullback g (LaurentPolynomial.T 1)) : f = g := by
  let e : CommRingCat.of (LaurentPolynomial (ULift.{0} ℤ)) ≅
      CommRingCat.of (LaurentPolynomial ℤ) :=
    (AddMonoidAlgebra.mapRingEquiv ℤ (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ)).toCommRingCatIso
  let k : multiplicativeGroup ⟶ multiplicativeGroupULift.{0} := Spec.map e.hom
  have : IsIso k := by
    show IsIso (Scheme.Spec.map e.hom.op)
    infer_instance
  apply (cancel_mono k).mp
  apply (pointUnit_bijective X).injective
  apply Units.ext
  rw [pointUnit_val, pointUnit_val]
  dsimp only [k]
  rw [specPullback_specMap, specPullback_specMap]
  simpa only [RingHom.comp_apply, e, RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_ofHom,
    AddMonoidAlgebra.toRingHom_mapRingEquiv, LaurentPolynomial.T,
    AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.mapRingEquiv_single,
    RingEquiv.coe_toRingHom, map_one] using h

private lemma baseChangeDeterminant_val (n : ℕ) (S : Scheme.{u}) :
    (Matrix.GeneralLinearGroup.det
      ((baseChangeGroupPointsIso n S).hom.app (Opposite.op (generalLinearBaseChange n S))
        (𝟙 _))).val =
      specPullback (pullback.fst (generalLinearStructureMorphism n)
        (specULiftZIsTerminal.from S))
        (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{u} ℤ))
          (generalLinearCoordinateRing n) (generalLinearDeterminant n)) := by
  let φ := (specPullback (pullback.fst (generalLinearStructureMorphism n)
    (specULiftZIsTerminal.from S))).comp
    (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{u} ℤ))
      (generalLinearCoordinateRing n))
  have hm : ((baseChangeGroupPointsIso n S).hom.app
      (Opposite.op (generalLinearBaseChange n S)) (𝟙 _)).val =
      φ.mapMatrix (Matrix.mvPolynomialX (Fin n) (Fin n) (ULift.{u} ℤ)) := by
    ext i j
    rw [baseChangeGroupPointsIso_hom_app]
    simp only [Over.id_left, Category.id_comp]
    rfl
  show Matrix.det _ = _
  rw [hm]
  exact (φ.map_det (Matrix.mvPolynomialX (Fin n) (Fin n) (ULift.{u} ℤ))).symm

/-- After projecting the base-changed morphism to the integral models, it is the
integral determinant morphism. The coefficient map compares `ℤ` with `ULift ℤ`. -/
@[stacks 022X "det_after_base_change"]
theorem determinantGroupSchemeMorphism_baseChange (n : ℕ) (S : Scheme.{0}) :
    (determinantGroupSchemeMorphism n S).hom.hom.left ≫
        pullback.fst (multiplicativeGroupULift ↘ Spec (.of (ULift.{0} ℤ)))
          (specULiftZIsTerminal.from S) ≫
        Spec.map (CommRingCat.ofHom
          (AddMonoidAlgebra.mapRingHom ℤ
            (ULift.ringEquiv.{0, 0}.symm.toRingHom : ℤ →+* ULift.{0} ℤ))) =
      pullback.fst (generalLinearStructureMorphism.{0} n) (specULiftZIsTerminal.from S) ≫
        (determinantGroupSchemeMorphismOverIntegers n).hom.hom.left := by
  obtain ⟨g, hg, hT⟩ := determinantGroupSchemeMorphismOverIntegers_spec n
  let d : pullback (generalLinearStructureMorphism.{0} n) (specULiftZIsTerminal.from S) ⟶
      pullback (multiplicativeGroupULift ↘ Spec (.of (ULift.{0} ℤ)))
        (specULiftZIsTerminal.from S) :=
    (determinantGroupSchemeMorphism n S).hom.hom.left
  let dZ : generalLinearScheme.{0} n ⟶ multiplicativeGroup :=
    (determinantGroupSchemeMorphismOverIntegers n).hom.hom.left
  have hgz : dZ = Spec.map (CommRingCat.ofHom g) := hg
  have hpt : multiplicativeGroupPointUnit (d ≫ pullback.fst
        (multiplicativeGroupULift ↘ Spec (.of (ULift.{0} ℤ)))
          (specULiftZIsTerminal.from S)) =
      Matrix.GeneralLinearGroup.det
        ((baseChangeGroupPointsIso n S).hom.app
          (Opposite.op (generalLinearBaseChange n S)) (𝟙 _)) :=
    determinantMorphism_pointUnit n S
  show d ≫ pullback.fst (multiplicativeGroupULift ↘ Spec (.of (ULift.{0} ℤ)))
        (specULiftZIsTerminal.from S) ≫
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapRingHom ℤ
          (ULift.ringEquiv.{0, 0}.symm.toRingHom : ℤ →+* ULift.{0} ℤ))) =
    pullback.fst (generalLinearStructureMorphism.{0} n) (specULiftZIsTerminal.from S) ≫ dZ
  apply integralPoint_ext
  have hL : (AddMonoidAlgebra.mapRingHom ℤ
        (ULift.ringEquiv.{0, 0}.symm.toRingHom : ℤ →+* ULift.{0} ℤ))
      (LaurentPolynomial.T 1) = LaurentPolynomial.T 1 := by
    simp only [LaurentPolynomial.T, AddMonoidAlgebra.mapRingHom_single, map_one]
  rw [← Category.assoc, specPullback_specMap, hgz, specPullback_specMap]
  simp only [RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [hL, hT, ← pointUnit_val, hpt, baseChangeDeterminant_val]

end AlgebraicGeometry
