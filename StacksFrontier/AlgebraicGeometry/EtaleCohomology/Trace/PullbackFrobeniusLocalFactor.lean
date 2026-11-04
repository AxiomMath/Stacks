module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PullbackStalkFrobenius
public import StacksFrontier.Algebra.Module.Projective.Determinant.CharSeries
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteCoverGeometricLifts

/-!
# The geometric Frobenius on the stalk of an inverse image at a closed point

Let `g : X' ⟶ X` be a morphism of schemes and `x'` a point of `X'` whose residue field is finite
and maps isomorphically onto that of `x = g(x')` (for instance `g` an immersion). The
identification `(g⁻¹ F)_{x̄'} ≅ F_{x̄}` of the stalks at the geometric points over `x'` and `x`
intertwines the geometric Frobenii `π_{x'}` and `π_x`, so the local factors
`det(1 - π_{x'} T ^ d)` and `det(1 - π_x T ^ d)` agree.

## Main results

* `Stacks.EtaleCohomology.frobeniusStalk_inverseImage_eq_conj`.
* `Stacks.EtaleCohomology.charSeries_frobeniusStalk_inverseImage`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (x' : X')

/-- `κ(x')` as an algebra over `κ(g x')`. -/
public abbrev inverseImageResidueAlgebra :
    Algebra (X.residueField (g x')) (X'.residueField x') :=
  (g.residueFieldMap x').hom.toAlgebra

/-- If `κ(x')` is finite, `κ̄(x')` is an algebraic closure of `κ(g x')`. -/
public theorem isAlgClosure_inverseImageResidueAlgebra [Finite (X'.residueField x')] :
    letI := inverseImageResidueAlgebra g x'
    IsAlgClosure (X.residueField (g x')) (AlgebraicClosure (X'.residueField x')) := by
  let := inverseImageResidueAlgebra g x'
  have : Module.Finite (X.residueField (g x')) (X'.residueField x') := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (X.residueField (g x')) (X'.residueField x') :=
    Algebra.IsAlgebraic.of_finite _ _
  have : Algebra.IsAlgebraic (X.residueField (g x')) (AlgebraicClosure (X'.residueField x')) :=
    Algebra.IsAlgebraic.trans _ (X'.residueField x') _
  exact ⟨inferInstance, inferInstance⟩

/-- An isomorphism `κ̄(g x') ≅ κ̄(x')` extending `κ(g x') → κ(x')`. -/
public def inverseImageClosureEquiv [Finite (X'.residueField x')] :
    AlgebraicClosure (X.residueField (g x')) ≃+* AlgebraicClosure (X'.residueField x') :=
  letI := inverseImageResidueAlgebra g x'
  haveI := isAlgClosure_inverseImageResidueAlgebra g x'
  (IsAlgClosure.equiv (X.residueField (g x')) (AlgebraicClosure (X.residueField (g x')))
    (AlgebraicClosure (X'.residueField x'))).toRingEquiv

/-- `inverseImageClosureEquiv g x'` extends the residue field map `κ(g x') → κ(x')`. -/
public theorem inverseImageClosureEquiv_algebraMap [Finite (X'.residueField x')]
    (z : X.residueField (g x')) :
    inverseImageClosureEquiv g x' (algebraMap _ (AlgebraicClosure (X.residueField (g x'))) z) =
      algebraMap _ (AlgebraicClosure (X'.residueField x')) ((g.residueFieldMap x').hom z) := by
  let := inverseImageResidueAlgebra g x'
  have := isAlgClosure_inverseImageResidueAlgebra g x'
  exact ((IsAlgClosure.equiv (X.residueField (g x')) (AlgebraicClosure (X.residueField (g x')))
    (AlgebraicClosure (X'.residueField x'))).commutes z).trans
    (IsScalarTower.algebraMap_apply _ (X'.residueField x') _ z)

/-- The morphism of geometric points from the image of the geometric point at `x'` to the geometric
point at `g x'`, given by `κ̄(g x') ≅ κ̄(x')`. -/
public def inverseImagePointHom [Finite (X'.residueField x')] :
    GeometricPoint.Hom ((geometricPointAt X' x').map g) (geometricPointAt X (g x')) where
  hom := Spec.map (CommRingCat.ofHom (inverseImageClosureEquiv g x').toRingHom)
  comm := by
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (g x'))
        (AlgebraicClosure (X.residueField (g x'))))) ≫ X.fromSpecResidueField (g x') =
      (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x')
        (AlgebraicClosure (X'.residueField x')))) ≫ X'.fromSpecResidueField x') ≫ g
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    ext z
    exact inverseImageClosureEquiv_algebraMap g x' z

variable [Finite (X'.residueField x')] [Finite (X.residueField (g x'))]

include g in
/-- **`κ̄(g x') ≅ κ̄(x')` carries `σ_{g x'}` to `σ_{x'}`** when `κ(g x') → κ(x')` is bijective. -/
public theorem residueGeometricFrobenius_inverseImageClosureEquiv
    (hbij : Function.Bijective (g.residueFieldMap x').hom)
    (z : AlgebraicClosure (X.residueField (g x'))) :
    residueGeometricFrobenius X' x' (inverseImageClosureEquiv g x' z) =
      inverseImageClosureEquiv g x' (residueGeometricFrobenius X (g x') z) := by
  have hcard : Nat.card (X.residueField (g x')) = Nat.card (X'.residueField x') :=
    Nat.card_congr (Equiv.ofBijective _ hbij)
  apply (residueGeometricFrobenius X' x').symm.injective
  rw [AlgEquiv.symm_apply_apply, residueGeometricFrobenius_symm_apply]
  conv_lhs => rw [← (residueGeometricFrobenius X (g x')).symm_apply_apply z]
  rw [residueGeometricFrobenius_symm_apply, map_pow, hcard]

omit [Finite (X.residueField (g x'))] in
/-- The underlying morphism of `inverseImagePointHom` is invertible. -/
public theorem inverseImagePointHom_hom_comp :
    (inverseImagePointHom g x').hom ≫
        Spec.map (CommRingCat.ofHom (inverseImageClosureEquiv g x').symm.toRingHom) = 𝟙 _ := by
  show Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext z
  exact (inverseImageClosureEquiv g x').apply_symm_apply z

/-- **The Frobenius of the image geometric point is that at `g x'`.** -/
public theorem frobeniusPointHom_map_comp_inverseImagePointHom
    (hbij : Function.Bijective (g.residueFieldMap x').hom) :
    ((frobeniusPointHom X' x').map g).comp (inverseImagePointHom g x') =
      (inverseImagePointHom g x').comp (frobeniusPointHom X (g x')) := by
  refine GeometricPoint.Hom.ext_of_hom ?_
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext z
  exact residueGeometricFrobenius_inverseImageClosureEquiv g x' hbij z

variable (Λ : Type r) [CommRing Λ]

/-- **The stalk of an inverse image at `x'` is the stalk at `g x'`**:
`F_{g x̄'} ≅ (g⁻¹ F)_{x̄'}`. -/
public def inverseImageStalkIso (F : EtaleModules.{u, r} Λ X) :
    (Scheme.pointSmallEtale (geometricPointAt X (g x')).hom).sheafFiber.obj F ≅
      (Scheme.pointSmallEtale (geometricPointAt X' x').hom).sheafFiber.obj
        ((etaleModuleInverseImage.{u, r} Λ g).obj F) :=
  (Point.sheafFiberIsoOfIso (A := ModuleCat.{max (u + 1) r} Λ)
      (@asIso _ _ _ _ (smallEtalePointHom X (inverseImagePointHom g x'))
        (smallEtalePointHom_isIso _ _))).app F ≪≫
    ((etaleModuleStalkPullbackIso Λ g (geometricPointAt X' x').hom).app F).symm

/-- **The geometric Frobenius on the stalk of an inverse image** at a point whose residue field
maps isomorphically onto that of its image is the geometric Frobenius at the image, read through
`F_{g x̄'} ≅ (g⁻¹ F)_{x̄'}`. -/
public theorem frobeniusStalk_inverseImage_eq_conj
    (hbij : Function.Bijective (g.residueFieldMap x').hom) (F : EtaleModules.{u, r} Λ X) :
    frobeniusStalk (ModuleCat.{max (u + 1) r} Λ) X' x'
        ((etaleModuleInverseImage.{u, r} Λ g).obj F) =
      (inverseImageStalkIso g x' Λ F).inv ≫
        frobeniusStalk (ModuleCat.{max (u + 1) r} Λ) X (g x') F ≫
          (inverseImageStalkIso g x' Λ F).hom := by
  have hc := congrArg (smallEtalePointHom X)
    (frobeniusPointHom_map_comp_inverseImagePointHom g x' hbij)
  rw [smallEtalePointHom_comp ((frobeniusPointHom X' x').map g) (inverseImagePointHom g x')
      (((frobeniusPointHom X' x').map g).comp (inverseImagePointHom g x')) rfl,
    smallEtalePointHom_comp (inverseImagePointHom g x') (frobeniusPointHom X (g x'))
      ((inverseImagePointHom g x').comp (frobeniusPointHom X (g x'))) rfl] at hc
  have h3 := congrArg (fun φ => (Point.Hom.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)
    (J := X.smallEtaleTopology) φ).app F) hc
  simp only [Point.Hom.sheafFiber_comp, NatTrans.comp_app] at h3
  rw [← cancel_epi (inverseImageStalkIso g x' Λ F).hom, Iso.hom_inv_id_assoc]
  show ((Point.Hom.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)
      (smallEtalePointHom X (inverseImagePointHom g x'))).app F ≫
      (etaleModuleStalkPullbackIso Λ g (geometricPointAt X' x').hom).inv.app F) ≫
      (Point.Hom.sheafFiber (smallEtalePointHom X' (frobeniusPointHom X' x'))).app
        ((etaleModuleInverseImage Λ g).obj F) =
    (Point.Hom.sheafFiber (smallEtalePointHom X (frobeniusPointHom X (g x')))).app F ≫
      (Point.Hom.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)
        (smallEtalePointHom X (inverseImagePointHom g x'))).app F ≫
      (etaleModuleStalkPullbackIso Λ g (geometricPointAt X' x').hom).inv.app F
  rw [Category.assoc, ← smallEtalePointHom_sheafFiber_comp_etaleModuleStalkPullbackIso_inv g
    (frobeniusPointHom X' x') Λ F, ← Category.assoc, h3, Category.assoc]

/-- **The local factor of an inverse image** at a point whose residue field maps isomorphically
onto that of its image:
`det(1 - π_{x'} T ^ d | (g⁻¹ F)_{x̄'}) = det(1 - π_{g x'} T ^ d | F_{g x̄'})`. -/
public theorem charSeries_frobeniusStalk_inverseImage
    (hbij : Function.Bijective (g.residueFieldMap x').hom) (F : EtaleModules.{u, r} Λ X)
    [Module.Finite Λ (((Scheme.pointSmallEtale (geometricPointAt X (g x')).hom).sheafFiber
      (A := ModuleCat.{max (u + 1) r} Λ)).obj F)]
    [Module.Projective Λ (((Scheme.pointSmallEtale (geometricPointAt X (g x')).hom).sheafFiber
      (A := ModuleCat.{max (u + 1) r} Λ)).obj F)] (d : ℕ) :
    haveI := Module.Finite.equiv (inverseImageStalkIso g x' Λ F).toLinearEquiv
    haveI := Module.Projective.of_equiv (inverseImageStalkIso g x' Λ F).toLinearEquiv
    ProjectiveDeterminant.charSeries (frobeniusStalk (ModuleCat.{max (u + 1) r} Λ) X' x'
        ((etaleModuleInverseImage.{u, r} Λ g).obj F)).hom d =
      ProjectiveDeterminant.charSeries
        (frobeniusStalk (ModuleCat.{max (u + 1) r} Λ) X (g x') F).hom d := by
  have := Module.Finite.equiv (inverseImageStalkIso g x' Λ F).toLinearEquiv
  have := Module.Projective.of_equiv (inverseImageStalkIso g x' Λ F).toLinearEquiv
  have h : (frobeniusStalk (ModuleCat.{max (u + 1) r} Λ) X' x'
      ((etaleModuleInverseImage.{u, r} Λ g).obj F)).hom =
      (inverseImageStalkIso g x' Λ F).toLinearEquiv.conj
        (frobeniusStalk (ModuleCat.{max (u + 1) r} Λ) X (g x') F).hom :=
    LinearMap.ext fun v =>
      congrArg (fun φ => φ.hom v) (frobeniusStalk_inverseImage_eq_conj g x' Λ hbij F)
  rw [h]
  exact ProjectiveDeterminant.charSeries_conj _ _ _

end Stacks.EtaleCohomology

end
