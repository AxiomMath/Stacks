module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatObstructionBaseChangeCotangentStalk

/-!
# Tor independent base change of the cotangent complex on the models (Stacks 09DL)

Let

```
W --p--> X
|        |
q        f
v        v
Y --g--> Z
```

be a cartesian square of algebraic spaces with `X` and `Y` Tor independent over `Z`. On the
`Type u` models of the small étale ringed topoi (`AlgebraicGeometry.Space.modelTopos`), on which
the cotangent complex `L_{X/Z}` of Stacks 08SU and the obstruction groups of Stacks 0D1P are
formed, the canonical map

`Lp_m^* L_{X/Z} = L_{p_m⁻¹𝒪_X/p_m⁻¹f_m⁻¹𝒪_Z} ⊗ 𝒪_W ⟶ L_{𝒪_W/p_m⁻¹f_m⁻¹𝒪_Z}
⟶ L_{𝒪_W/q_m⁻¹𝒪_Y} = L_{W/Y}`

is an isomorphism (`AlgebraicGeometry.Space.isIso_modelCotangentBaseChangeMap`), where `p_m` is
the model morphism `AlgebraicGeometry.Space.smallEtaleModelPullbackRingedToposHom p`. This is the
first assertion of Stacks 09DL (the top row of the diagram of Stacks 09DK, whose corner vanishes)
in the form needed for the models.

The proof is the source's: the cone vanishes on derived stalks at the geometric points of `W`,
which form a conservative family of points of the model
(`AlgebraicGeometry.Space.isConservativeFamilyOfPoints_modelSitePoint`). At `w̄` the derived stalk
of the cone is a cone of `L_{B/R} ⊗^𝐋_B C ⟶ L_{C/R} ⟶ L_{C/A}` for the étale local rings
`R = 𝒪_{Z, z̄}`, `A = 𝒪_{Y, q(w̄)}`, `B = 𝒪_{X, p(w̄)}`, `C = 𝒪_{W, w̄}`
(`StacksFrontier/AlgebraicGeometry/Quot/ProperFlatObstructionBaseChangeCotangentStalk.lean`), with
`A ⊗_R B → C` weakly étale (`AlgebraicGeometry.Space.cartesian_etaleStalk_tensor_weaklyEtale`), and
it vanishes by Stacks 09DA (`CommAlgCat.isZero_cone_fundamentalMor_of_ringEquiv_of_torIndependent`).

## Main definitions

* `AlgebraicGeometry.Space.modelCotangentBaseChangeMap`: the canonical map
  `Lp_m^* L_{X/Z} ⟶ L_{W/Y}`.
* `AlgebraicGeometry.Space.modelCotangentBaseChangeIso`: the isomorphism, for a cartesian square
  of Tor independent algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isIso_modelCotangentBaseChangeMap`

## References

* [Stacks Project, Tag 09DL](https://stacks.math.columbia.edu/tag/09DL)
* [Stacks Project, Tag 09DK](https://stacks.math.columbia.edu/tag/09DK)
* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open scoped TensorProduct

universe u

namespace CommAlgCat

section CrossUniverse

open scoped TensorProduct

universe v₁ v₂

variable {R' A' B' : Type v₁} [CommRing R'] [CommRing A'] [CommRing B'] [Algebra R' A']
  [Algebra R' B'] {R A B : Type v₂} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
  [Algebra R B] (ρ : R' ≃+* R) (α : A' ≃+* A) (β : B' ≃+* B)
  (hα : ∀ r, α (algebraMap R' A' r) = algebraMap R A (ρ r))
  (hβ : ∀ r, β (algebraMap R' B' r) = algebraMap R B (ρ r))

/-- The map of tensor products of isomorphisms of algebras in two universes. -/
def crossTensorMap : A' ⊗[R'] B' →+* A ⊗[R] B :=
  letI : Algebra R' (A ⊗[R] B) := ((algebraMap R (A ⊗[R] B)).comp ρ.toRingHom).toAlgebra
  (Algebra.TensorProduct.lift
    ({ (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B)).comp α.toRingHom with
      commutes' := fun r => by
        change α (algebraMap R' A' r) ⊗ₜ[R] (1 : B) = algebraMap R (A ⊗[R] B) (ρ r)
        rw [hα, Algebra.TensorProduct.algebraMap_apply] } : A' →ₐ[R'] A ⊗[R] B)
    ({ (Algebra.TensorProduct.includeRight (R := R) (A := A)
        (B := B)).toRingHom.comp β.toRingHom with
      commutes' := fun r => by
        change (1 : A) ⊗ₜ[R] β (algebraMap R' B' r) = algebraMap R (A ⊗[R] B) (ρ r)
        rw [hβ, Algebra.TensorProduct.algebraMap_apply'] } : B' →ₐ[R'] A ⊗[R] B)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem crossTensorMap_tmul (a : A') (b : B') :
    crossTensorMap ρ α β hα hβ (a ⊗ₜ[R'] b) = α a ⊗ₜ[R] β b := by
  change (α a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] β b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The ring isomorphism `A' ⊗_{R'} B' ≃ A ⊗_R B` of isomorphisms in two universes. -/
def crossTensorRingEquiv : A' ⊗[R'] B' ≃+* A ⊗[R] B :=
  RingEquiv.ofRingHom (crossTensorMap ρ α β hα hβ)
    (crossTensorMap ρ.symm α.symm β.symm
      (fun r => by rw [RingEquiv.symm_apply_eq, hα, RingEquiv.apply_symm_apply])
      (fun r => by rw [RingEquiv.symm_apply_eq, hβ, RingEquiv.apply_symm_apply]))
    (RingHom.ext fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        rw [RingHom.comp_apply, crossTensorMap_tmul, crossTensorMap_tmul,
          RingEquiv.apply_symm_apply,
          RingEquiv.apply_symm_apply, RingHom.id_apply]
      | add x y hx hy => rw [map_add, map_add, hx, hy])
    (RingHom.ext fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        rw [RingHom.comp_apply, crossTensorMap_tmul, crossTensorMap_tmul,
          RingEquiv.symm_apply_apply,
          RingEquiv.symm_apply_apply, RingHom.id_apply]
      | add x y hx hy => rw [map_add, map_add, hx, hy])

end CrossUniverse

end CommAlgCat

namespace CategoryTheory.Sheaf

universe v' u' w' z'

attribute [local instance 10000] HasDerivedCategory.standard

variable {C : Type u'} [Category.{v'} C] (J : GrothendieckTopology C)
  [LocallySmall.{max u' v' w'} C] (Φ : J.Point.{max u' v' w'})
  {A B D A₂ : Sheaf J CommRingCat.{max u' v' w'}} (g : A ⟶ B) (h : B ⟶ D) {f₂ : A₂ ⟶ D}
  (a : A ⟶ A₂) (hsq : (g ≫ h) ≫ 𝟙 D = a ≫ f₂)

open scoped TensorProduct in
/-- **The cone of `L_{B/A} ⊗ D ⟶ L_{D/A} ⟶ L_{D/A₂}` vanishes at a point** at which the four stalk
rings are those of a Tor independent square with a weakly étale comparison (Stacks 09DA, 09DL),
for a change of base along a map of rings `a : A ⟶ A₂` over `D`. -/
theorem isZero_derivedModuleFiber_of_ringEquiv_of_torIndependent
    {R A₀ B₀ C₀ : Type (max u' v' w' z')} [CommRing R] [CommRing A₀] [CommRing B₀] [CommRing C₀]
    [Algebra R A₀] [Algebra R B₀] (φ : A₀ ⊗[R] B₀ →+* C₀)
    (hW : @Algebra.WeaklyEtale _ _ _ _ φ.toAlgebra)
    (ρR : (Φ.presheafFiber (A := CommRingCat)).obj A.obj ≃+* R)
    (ρA : (Φ.presheafFiber (A := CommRingCat)).obj A₂.obj ≃+* A₀)
    (ρB : (Φ.presheafFiber (A := CommRingCat)).obj B.obj ≃+* B₀)
    (ρC : (Φ.presheafFiber (A := CommRingCat)).obj D.obj ≃+* C₀)
    (hA : ∀ r, ρA (((Φ.presheafFiber (A := CommRingCat)).map a.hom).hom r) = algebraMap R A₀ (ρR r))
    (hB : ∀ r, ρB (((Φ.presheafFiber (A := CommRingCat)).map g.hom).hom r) = algebraMap R B₀ (ρR r))
    (hAC : ∀ x, ρC (((Φ.presheafFiber (A := CommRingCat)).map f₂.hom).hom x) = φ (ρA x ⊗ₜ[R] 1))
    (hBC : ∀ y, ρC (((Φ.presheafFiber (A := CommRingCat)).map h.hom).hom y) = φ (1 ⊗ₜ[R] ρB y))
    (hTor : RingTheory.TorIndependence.TorIndependent R A₀ B₀)
    {K M : DerivedCategory (targetModules J D)}
    (e : K ≅ DerivedCategory.Q.obj (baseChangedCotangentComplex.{u', v', w'} J g h))
    {β : DerivedCategory.Q.obj (cotangentComplex J f₂) ⟶ M} {γ : M ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (e.hom ≫ DerivedCategory.Q.map (towerCotangentBaseChange.{u', v', w'} J g h ≫
      squareCotangentComplexMap (resolutionSquareMap.{u', v', w'} J a (𝟙 D) hsq))) β γ ∈
        distTriang _) :
    IsZero ((Stacks.derivedModuleFiber Φ D).obj M) := by
  obtain ⟨b', e', hC⟩ := exists_distTriang_derivedModuleFiber_fundamental J Φ g h a hsq _
    (isPointStalkBaseMap_squareCotangentComplexMap J Φ a hsq) e hT
  let : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
      CommRingCat)).obj B.obj) := ((Φ.presheafFiber (A := CommRingCat)).map g.hom).hom.toAlgebra
  let : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj B.obj) ((Φ.presheafFiber (A :=
      CommRingCat)).obj D.obj) := ((Φ.presheafFiber (A := CommRingCat)).map h.hom).hom.toAlgebra
  let : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
      CommRingCat)).obj D.obj) :=
    ((Φ.presheafFiber (A := CommRingCat)).map (g ≫ h).hom).hom.toAlgebra
  have := isScalarTower_pointStalk J Φ g h
  let : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
      CommRingCat)).obj A₂.obj) := ((Φ.presheafFiber (A := CommRingCat)).map a.hom).hom.toAlgebra
  let : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A₂.obj) ((Φ.presheafFiber (A :=
      CommRingCat)).obj D.obj) := ((Φ.presheafFiber (A := CommRingCat)).map f₂.hom).hom.toAlgebra
  have := isScalarTower_pointStalk_base J Φ g h a hsq
  -- the ring-theoretic content of Stacks 09DL, transported along the isomorphisms `ρ` of rings in
  -- a larger universe
  have key : ∀ {R' A' B' C' : Type (max u' v' w')} [CommRing R'] [CommRing A'] [CommRing B']
      [CommRing C'] [Algebra R' A'] [Algebra R' B'] [Algebra R' C'] [Algebra A' C']
      [Algebra B' C'] [IsScalarTower R' A' C'] [IsScalarTower R' B' C']
      (ρR : R' ≃+* R) (ρA : A' ≃+* A₀) (ρB : B' ≃+* B₀) (ρC : C' ≃+* C₀)
      (hA : ∀ r, ρA (algebraMap R' A' r) = algebraMap R A₀ (ρR r))
      (hB : ∀ r, ρB (algebraMap R' B' r) = algebraMap R B₀ (ρR r))
      (hAC : ∀ a, ρC (algebraMap A' C' a) = φ (ρA a ⊗ₜ[R] 1))
      (hBC : ∀ b, ρC (algebraMap B' C' b) = φ (1 ⊗ₜ[R] ρB b))
      {EC : DerivedCategory (ModuleCat.{max u' v' w'} C')}
      {b' : CommAlgCat.cotangentComplexDerived.{max u' v' w', max u' v' w'} A'
        (CommAlgCat.of A' C') ⟶ EC}
      {e' : EC ⟶ (CommAlgCat.fundamentalVertex₁.{max u' v' w', max u' v' w', max u' v' w' + 1,
        max u' v' w' + 1} R' B' C')⟦(1 : ℤ)⟧}
      (hC : Triangle.mk (CommAlgCat.fundamentalMor₁.{max u' v' w'} R' B' C' ≫
          CommAlgCat.fundamentalMor₂.{max u' v' w'} R' A' C') b' e' ∈
        distTriang (DerivedCategory (ModuleCat.{max u' v' w'} C'))),
      IsZero EC := by
    intro R' A' B' C' _ _ _ _ _ _ _ _ _ _ _ ρR ρA ρB ρC hA hB hAC hBC EC b' e' hC
    letI : Algebra B' (A' ⊗[R'] B') := Algebra.TensorProduct.rightAlgebra
    let ψ : A' ⊗[R'] B' →ₐ[R'] C' := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R' A' C')
      (IsScalarTower.toAlgHom R' B' C') fun _ _ => Commute.all _ _
    have hψ : ∀ a b, ψ (a ⊗ₜ[R'] b) = algebraMap A' C' a * algebraMap B' C' b :=
      fun _ _ => Algebra.TensorProduct.lift_tmul ..
    let : Algebra (A' ⊗[R'] B') C' := ψ.toRingHom.toAlgebra
    have : IsScalarTower R' (A' ⊗[R'] B') C' :=
      IsScalarTower.of_algebraMap_eq fun r => (ψ.commutes r).symm
    have : IsScalarTower A' (A' ⊗[R'] B') C' := IsScalarTower.of_algebraMap_eq fun a => by
      change _ = ψ (a ⊗ₜ[R'] 1)
      simp [hψ]
    have : IsScalarTower B' (A' ⊗[R'] B') C' := IsScalarTower.of_algebraMap_eq fun b => by
      change _ = ψ (1 ⊗ₜ[R'] b)
      simp [hψ]
    have hτ : ∀ t, ρC (algebraMap (A' ⊗[R'] B') C' t) =
        φ (CommAlgCat.crossTensorRingEquiv ρR ρA ρB hA hB t) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        change ρC (ψ (a ⊗ₜ[R'] b)) = φ (CommAlgCat.crossTensorMap ρR ρA ρB hA hB (a ⊗ₜ[R'] b))
        rw [CommAlgCat.crossTensorMap_tmul, hψ, map_mul]
        rw [hAC, hBC, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    have : Algebra.WeaklyEtale (A' ⊗[R'] B') C' :=
      @Algebra.WeaklyEtale.of_ringEquiv _ _ _ _ _ _ _ _ φ.toAlgebra _ hW
        (CommAlgCat.crossTensorRingEquiv ρR ρA ρB hA hB) ρC hτ
    have hTor' : RingTheory.TorIndependence.TorIndependent R' A' B' :=
      (RingTheory.TorIndependence.torIndependent_congr_universe.{max u' v' w', max u' v' w' z'}
        ρR ρA ρB hA hB).1 hTor
    exact CommAlgCat.isZero_cone_fundamentalMor_of_torIndependent R' A' B' C' hTor' hC
  exact key ρR ρA ρB ρC hA hB hAC hBC hC

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z W : AlgebraicSpaces B S hS}

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

/-! ### Stalks on the model -/

/-- Transporting an element of a commutative ring along an equality and back returns it. -/
theorem eqToHom_hom_apply_eqToHom' {R₁ R₂ : CommRingCat.{u}} (h₁ : R₁ = R₂) (h₂ : R₂ = R₁)
    (t : R₁) : (eqToHom h₂).hom ((eqToHom h₁).hom t) = t := by
  subst h₁
  rfl

section Stalks

variable (w : GeometricPoint B S hS W.1)

/-- The stalk at the point of `w̄` of a sheaf of rings restricted from `W_et` is its stalk on
`W_et`. -/
def modelRestrictionStalkEquiv (R : Sheaf (SmallEtale.topology B S hS W.1) CommRingCat.{u}) :
    ((modelSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u})).obj
        ((modelRingRestriction (X := W)).obj R).obj ≃+*
      ((etaleSitePoint B S hS W.1 w W.2).presheafFiber (A := CommRingCat.{u})).obj R.obj :=
  ((modelRestrictionFiberRingIso B S hS W w).app R).commRingCatIsoToRingEquiv

/-- `modelRestrictionStalkEquiv` is natural. -/
theorem modelRestrictionStalkEquiv_map {R R' : Sheaf (SmallEtale.topology B S hS W.1)
      CommRingCat.{u}} (φ : R ⟶ R')
    (y : ((modelSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u})).obj
        ((modelRingRestriction (X := W)).obj R).obj) :
    modelRestrictionStalkEquiv w R'
        (((modelSitePoint B S hS W w).sheafFiber (A := CommRingCat.{u})).map
          ((modelRingRestriction (X := W)).map φ) y) =
      ((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).map φ
        (modelRestrictionStalkEquiv w R y) :=
  ConcreteCategory.congr_hom ((modelRestrictionFiberRingIso B S hS W w).hom.naturality φ) y

/-- The isomorphism of stalks at the point of `w̄` induced by an isomorphism of sheaves of rings on
the model. -/
abbrev modelStalkEquivOfIso {F G : Sheaf (modelTopos W).J CommRingCat.{u}} (e : F ≅ G) :
    ((modelSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u})).obj F.obj ≃+*
      ((modelSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u})).obj G.obj :=
  (((modelSitePoint B S hS W w).sheafFiber
      (A := CommRingCat.{u})).mapIso e).commRingCatIsoToRingEquiv

/-- `modelStalkEquivOfIso`, unfolded. -/
theorem modelStalkEquivOfIso_apply {F G : Sheaf (modelTopos W).J CommRingCat.{u}} (e : F ≅ G)
    (x : ((modelSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u})).obj F.obj) :
    modelStalkEquivOfIso w e x =
      ((modelSitePoint B S hS W w).sheafFiber (A := CommRingCat.{u})).map e.hom x :=
  rfl

/-- The stalk of `𝒪_W` at the point of `w̄` is `𝒪_{W, w̄}`. -/
def modelStructureStalkEquiv :
    ((modelSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u})).obj (modelTopos W).O.obj ≃+*
      etaleLocalRing B S hS W.1 w :=
  (modelRestrictionStalkEquiv w (smallEtaleRingedTopos B S hS W).O).trans
    (pointStalkRingEquiv B S hS W w)

/-- The stalk of `q_m⁻¹𝒪_Y` at the point of `w̄` is `𝒪_{Y, q(w̄)}`. -/
def modelInverseImageStalkEquiv (q : W ⟶ Y) :
    ((modelSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u})).obj
        ((inverseImageCommRingFunctor.{u, u, u, u, u, u + 1}
          (modelRingedToposHom q).toToposHom).obj (smallEtaleRingedTopos B S hS Y).O).obj ≃+*
      etaleLocalRing B S hS Y.1 (geometricPointMap q.hom w) :=
  (modelStalkEquivOfIso w
      ((modelInverseImageRingIso q).app (smallEtaleRingedTopos B S hS Y).O)).trans
    ((modelRestrictionStalkEquiv w _).trans (etaleInverseImageStalkEquiv B S hS q w))

/-- The stalk of `p_m⁻¹𝒪_X` at the point of `w̄` is `𝒪_{X, p(w̄)}`. -/
def modelPullbackStalkEquiv (p : W ⟶ X) :
    ((modelSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u})).obj
        ((modelPullbackHom p).toToposHom.inverseImageRing.obj (modelTopos X).O).obj ≃+*
      etaleLocalRing B S hS X.1 (geometricPointMap p.hom w) :=
  (modelStalkEquivOfIso w ((modelPullbackInverseImageRingIso p).app
      (smallEtaleRingedTopos B S hS X).O)).trans
    ((modelRestrictionStalkEquiv w _).trans (etaleInverseImageStalkEquiv B S hS p w))

/-- The stalk of `p_m⁻¹f_m⁻¹𝒪_Z` at the point of `w̄` is `𝒪_{Z, g(q(w̄))}`. -/
def modelTowerBaseStalkEquiv {f : X ⟶ Z} {g : Y ⟶ Z} {p : W ⟶ X} {q : W ⟶ Y}
    (h : p ≫ f = q ≫ g) :
    ((modelSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u})).obj
        ((modelPullbackHom p).toToposHom.inverseImageRing.obj
          ((inverseImageCommRingFunctor.{u, u, u, u, u, u + 1}
            (modelRingedToposHom f).toToposHom).obj (smallEtaleRingedTopos B S hS Z).O)).obj ≃+*
      etaleLocalRing B S hS Z.1 (geometricPointMap g.hom (geometricPointMap q.hom w)) :=
  (modelStalkEquivOfIso w (modelTowerBaseIso f p ≪≫ (modelRingRestriction (X := W)).mapIso
      (smallEtaleRingedToposHom_squareInverseImageRingIso B S hS h))).trans
    ((modelRestrictionStalkEquiv w _).trans (etaleTowerStalkEquiv B S hS q g w))

/-- **The stalk of the structure map of `q_m` is the homomorphism of étale local rings of
Stacks 04NG.** -/
theorem modelRingedToposHom_fSharpInverseImage_stalk_apply (q : W ⟶ Y)
    (a : ((modelSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u})).obj
        ((inverseImageCommRingFunctor.{u, u, u, u, u, u + 1}
          (modelRingedToposHom q).toToposHom).obj (smallEtaleRingedTopos B S hS Y).O).obj) :
    modelStructureStalkEquiv w (((modelSitePoint B S hS W w).sheafFiber
        (A := CommRingCat.{u})).map (modelRingedToposHom q).fSharpInverseImage a) =
      etaleLocalRingMap W.2 q.hom w (modelInverseImageStalkEquiv w q a) := by
  have E := (ConcreteCategory.congr_hom (congrArg ((modelSitePoint B S hS W w).sheafFiber
      (A := CommRingCat.{u})).map
        (modelRingedToposHom_fSharpInverseImage_eq_restriction q)) a).trans
    (ConcreteCategory.congr_hom (((modelSitePoint B S hS W w).sheafFiber
      (A := CommRingCat.{u})).map_comp
        ((modelInverseImageRingIso q).hom.app (smallEtaleRingedTopos B S hS Y).O)
        ((modelRingRestriction (X := W)).map
          (smallEtaleRingedToposHom B S hS q).fSharpInverseImage)) a)
  exact (congrArg (fun z => pointStalkRingEquiv B S hS W w (modelRestrictionStalkEquiv w _ z))
    E).trans
    ((congrArg (pointStalkRingEquiv B S hS W w) (modelRestrictionStalkEquiv_map w _ _)).trans
      (fSharpInverseImage_etaleStalk_apply q w _))

/-- **The stalk of the structure map of `p_m` is the homomorphism of étale local rings of
Stacks 04NG.** -/
theorem modelPullbackHom_fSharpInverseImage_stalk_apply (p : W ⟶ X)
    (b : ((modelSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u})).obj
        ((modelPullbackHom p).toToposHom.inverseImageRing.obj (modelTopos X).O).obj) :
    modelStructureStalkEquiv w (((modelSitePoint B S hS W w).sheafFiber
        (A := CommRingCat.{u})).map (modelPullbackHom p).fSharpInverseImage b) =
      etaleLocalRingMap W.2 p.hom w (modelPullbackStalkEquiv w p b) := by
  have E := (ConcreteCategory.congr_hom (congrArg ((modelSitePoint B S hS W w).sheafFiber
      (A := CommRingCat.{u})).map
        (smallEtaleModelPullbackRingedToposHom_fSharpInverseImage p)) b).trans
    (ConcreteCategory.congr_hom (((modelSitePoint B S hS W w).sheafFiber
      (A := CommRingCat.{u})).map_comp
        ((modelPullbackInverseImageRingIso p).hom.app (smallEtaleRingedTopos B S hS X).O)
        ((modelRingRestriction (X := W)).map
          (smallEtaleRingedToposHom B S hS p).fSharpInverseImage)) b)
  exact (congrArg (fun z => pointStalkRingEquiv B S hS W w (modelRestrictionStalkEquiv w _ z))
    E).trans
    ((congrArg (pointStalkRingEquiv B S hS W w) (modelRestrictionStalkEquiv_map w _ _)).trans
      (fSharpInverseImage_etaleStalk_apply p w _))

variable {f : X ⟶ Z} {g : Y ⟶ Z} {p : W ⟶ X} {q : W ⟶ Y}

/-- `modelTowerBaseStalkEquiv`, unfolded. -/
theorem modelTowerBaseStalkEquiv_apply (h : p ≫ f = q ≫ g)
    (r : ((modelSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u})).obj
        ((modelPullbackHom p).toToposHom.inverseImageRing.obj
          ((inverseImageCommRingFunctor.{u, u, u, u, u, u + 1}
            (modelRingedToposHom f).toToposHom).obj (smallEtaleRingedTopos B S hS Z).O)).obj) :
    modelTowerBaseStalkEquiv w h r = etaleTowerStalkEquiv B S hS q g w
      (((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).map
        (smallEtaleRingedToposHom_squareInverseImageRingIso B S hS h).hom
        (modelRestrictionStalkEquiv w _
          (((modelSitePoint B S hS W w).sheafFiber (A := CommRingCat.{u})).map
            (modelTowerBaseIso f p).hom r))) :=
  (congrArg (fun z => etaleTowerStalkEquiv B S hS q g w (modelRestrictionStalkEquiv w _ z))
    (ConcreteCategory.congr_hom (((modelSitePoint B S hS W w).sheafFiber
      (A := CommRingCat.{u})).map_comp (modelTowerBaseIso f p).hom
        ((modelRingRestriction (X := W)).map
          (smallEtaleRingedToposHom_squareInverseImageRingIso B S hS h).hom)) r)).trans
    (congrArg (etaleTowerStalkEquiv B S hS q g w) (modelRestrictionStalkEquiv_map w _ _))

/-- **The stalk of `a : p_m⁻¹f_m⁻¹𝒪_Z ⟶ q_m⁻¹𝒪_Y` is the homomorphism of étale local rings
`𝒪_{Z, g(q(w̄))} → 𝒪_{Y, q(w̄)}` of `g`.** -/
theorem modelSquareBaseMap_stalk_apply (h : p ≫ f = q ≫ g)
    (r : ((modelSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u})).obj
        ((modelPullbackHom p).toToposHom.inverseImageRing.obj
          ((inverseImageCommRingFunctor.{u, u, u, u, u, u + 1}
            (modelRingedToposHom f).toToposHom).obj (smallEtaleRingedTopos B S hS Z).O)).obj) :
    modelInverseImageStalkEquiv w q (((modelSitePoint B S hS W w).sheafFiber
        (A := CommRingCat.{u})).map (modelSquareBaseMap f g p q h) r) =
      etaleLocalRingMap Y.2 g.hom (geometricPointMap q.hom w) (modelTowerBaseStalkEquiv w h r) := by
  have e : modelSquareBaseMap f g p q h ≫
      (modelInverseImageRingIso q).hom.app (smallEtaleRingedTopos B S hS Y).O =
      (modelTowerBaseIso f p).hom ≫ (modelRingRestriction (X := W)).map
        ((smallEtaleRingedToposHom_squareInverseImageRingIso B S hS h).hom ≫
          (smallEtaleInverseImageRing B S hS q).map
            (smallEtaleRingedToposHom B S hS g).fSharpInverseImage) :=
    by simp only [modelSquareBaseMap, Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj,
      Category.comp_id]
  have E1 := (ConcreteCategory.congr_hom (((modelSitePoint B S hS W w).sheafFiber
      (A := CommRingCat.{u})).map_comp (modelSquareBaseMap f g p q h)
        ((modelInverseImageRingIso q).hom.app (smallEtaleRingedTopos B S hS Y).O)).symm r).trans
    ((ConcreteCategory.congr_hom (congrArg ((modelSitePoint B S hS W w).sheafFiber
      (A := CommRingCat.{u})).map e) r).trans (ConcreteCategory.congr_hom
        (((modelSitePoint B S hS W w).sheafFiber (A := CommRingCat.{u})).map_comp
          (modelTowerBaseIso f p).hom ((modelRingRestriction (X := W)).map
            ((smallEtaleRingedToposHom_squareInverseImageRingIso B S hS h).hom ≫
              (smallEtaleInverseImageRing B S hS q).map
                (smallEtaleRingedToposHom B S hS g).fSharpInverseImage))) r))
  have E2 := fun y => ConcreteCategory.congr_hom (((etaleSitePoint B S hS W.1 w W.2).sheafFiber
    (A := CommRingCat.{u})).map_comp
      (smallEtaleRingedToposHom_squareInverseImageRingIso B S hS h).hom
      ((smallEtaleInverseImageRing B S hS q).map
        (smallEtaleRingedToposHom B S hS g).fSharpInverseImage)) y
  exact (congrArg (fun z => etaleInverseImageStalkEquiv B S hS q w
      (modelRestrictionStalkEquiv w _ z)) E1).trans
    ((congrArg (etaleInverseImageStalkEquiv B S hS q w)
      ((modelRestrictionStalkEquiv_map w _ _).trans (E2 _))).trans
      ((inverseImage_fSharpInverseImage_etaleStalk_apply q g w _).trans
        (congrArg (etaleLocalRingMap Y.2 g.hom (geometricPointMap q.hom w))
          (modelTowerBaseStalkEquiv_apply w h r).symm)))

/-- **The stalk of the base map `p_m⁻¹f_m⁻¹𝒪_Z ⟶ p_m⁻¹𝒪_X` of the tower is the homomorphism of
étale local rings `𝒪_{Z, f(p(w̄))} → 𝒪_{X, p(w̄)}` of `f`**, the source read at `g(q(w̄))` through
the square. -/
theorem towerBaseMap_modelStalk_apply (h : p ≫ f = q ≫ g)
    (r : ((modelSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u})).obj
        ((modelPullbackHom p).toToposHom.inverseImageRing.obj
          ((inverseImageCommRingFunctor.{u, u, u, u, u, u + 1}
            (modelRingedToposHom f).toToposHom).obj (smallEtaleRingedTopos B S hS Z).O)).obj) :
    modelPullbackStalkEquiv w p (((modelSitePoint B S hS W w).sheafFiber
        (A := CommRingCat.{u})).map
          (RingedToposHom.towerBaseMap.{u, u, u, u, u, u, u, u + 1, u} (modelRingedToposHom f)
        (modelPullbackHom p)) r) =
      (eqToHom (congrArg (etaleLocalRing B S hS Z.1)
          (congrArg (fun k : W ⟶ Z => geometricPointMap k.hom w) h.symm)) ≫
        CommRingCat.ofHom (etaleLocalRingMap X.2 f.hom (geometricPointMap p.hom w))).hom
        (modelTowerBaseStalkEquiv w h r) := by
  have E1 := (ConcreteCategory.congr_hom (((modelSitePoint B S hS W w).sheafFiber
      (A := CommRingCat.{u})).map_comp
        (RingedToposHom.towerBaseMap.{u, u, u, u, u, u, u, u + 1, u} (modelRingedToposHom f)
          (modelPullbackHom p))
        ((modelPullbackInverseImageRingIso p).hom.app
          (smallEtaleRingedTopos B S hS X).O)).symm r).trans
    ((ConcreteCategory.congr_hom (congrArg ((modelSitePoint B S hS W w).sheafFiber
      (A := CommRingCat.{u})).map
        (towerBaseMap_comp_modelPullbackInverseImageRingIso (f := f) (p := p))) r).trans
        (ConcreteCategory.congr_hom (((modelSitePoint B S hS W w).sheafFiber
          (A := CommRingCat.{u})).map_comp (modelTowerBaseIso f p).hom
            ((modelRingRestriction (X := W)).map ((smallEtaleInverseImageRing B S hS p).map
              (smallEtaleRingedToposHom B S hS f).fSharpInverseImage))) r))
  refine (congrArg (fun z => etaleInverseImageStalkEquiv B S hS p w
      (modelRestrictionStalkEquiv w _ z)) E1).trans
    ((congrArg (etaleInverseImageStalkEquiv B S hS p w)
      (modelRestrictionStalkEquiv_map w _ _)).trans
      ((inverseImage_fSharpInverseImage_etaleStalk_apply p f w _).trans ?_))
  refine congrArg (etaleLocalRingMap X.2 f.hom (geometricPointMap p.hom w)) ?_
  exact (eqToHom_hom_apply_eqToHom'
      (congrArg (fun k : W ⟶ Z => etaleLocalRing B S hS Z.1 (geometricPointMap k.hom w)) h)
      (congrArg (etaleLocalRing B S hS Z.1)
        (congrArg (fun k : W ⟶ Z => geometricPointMap k.hom w) h.symm)) _).symm.trans
    (congrArg (eqToHom (congrArg (etaleLocalRing B S hS Z.1)
        (congrArg (fun k : W ⟶ Z => geometricPointMap k.hom w) h.symm))).hom
      ((etaleTowerStalkEquiv_square h w _).symm.trans (modelTowerBaseStalkEquiv_apply w h r).symm))

end Stalks

/-! ### The four squares, read on presheaf fibres -/

section PresheafFiber

variable (w : GeometricPoint B S hS W.1) {f : X ⟶ Z} {g : Y ⟶ Z} {p : W ⟶ X} {q : W ⟶ Y}

theorem modelSquareBaseMap_presheafFiber_apply (h : p ≫ f = q ≫ g)
    (r : ((modelSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u})).obj
        ((modelPullbackHom p).toToposHom.inverseImageRing.obj
          ((inverseImageCommRingFunctor.{u, u, u, u, u, u + 1}
            (modelRingedToposHom f).toToposHom).obj (smallEtaleRingedTopos B S hS Z).O)).obj) :
    modelInverseImageStalkEquiv w q ((((modelSitePoint B S hS W w).presheafFiber
        (A := CommRingCat.{u})).map (modelSquareBaseMap f g p q h).hom).hom r) =
      etaleLocalRingMap Y.2 g.hom (geometricPointMap q.hom w) (modelTowerBaseStalkEquiv w h r) :=
  modelSquareBaseMap_stalk_apply w h r

theorem towerBaseMap_presheafFiber_apply (h : p ≫ f = q ≫ g)
    (r : ((modelSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u})).obj
        ((modelPullbackHom p).toToposHom.inverseImageRing.obj
          ((inverseImageCommRingFunctor.{u, u, u, u, u, u + 1}
            (modelRingedToposHom f).toToposHom).obj (smallEtaleRingedTopos B S hS Z).O)).obj) :
    modelPullbackStalkEquiv w p ((((modelSitePoint B S hS W w).presheafFiber
        (A := CommRingCat.{u})).map
          (RingedToposHom.towerBaseMap.{u, u, u, u, u, u, u, u + 1, u} (modelRingedToposHom f)
            (modelPullbackHom p)).hom).hom r) =
      (eqToHom (congrArg (etaleLocalRing B S hS Z.1)
          (congrArg (fun k : W ⟶ Z => geometricPointMap k.hom w) h.symm)) ≫
        CommRingCat.ofHom (etaleLocalRingMap X.2 f.hom (geometricPointMap p.hom w))).hom
        (modelTowerBaseStalkEquiv w h r) :=
  towerBaseMap_modelStalk_apply w h r

theorem modelRingedToposHom_fSharpInverseImage_presheafFiber_apply
    (a : ((modelSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u})).obj
        ((inverseImageCommRingFunctor.{u, u, u, u, u, u + 1}
          (modelRingedToposHom q).toToposHom).obj (smallEtaleRingedTopos B S hS Y).O).obj) :
    modelStructureStalkEquiv w ((((modelSitePoint B S hS W w).presheafFiber
        (A := CommRingCat.{u})).map (modelRingedToposHom q).fSharpInverseImage.hom).hom a) =
      etaleLocalRingMap W.2 q.hom w (modelInverseImageStalkEquiv w q a) :=
  modelRingedToposHom_fSharpInverseImage_stalk_apply w q a

theorem modelPullbackHom_fSharpInverseImage_presheafFiber_apply
    (b : ((modelSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u})).obj
        ((modelPullbackHom p).toToposHom.inverseImageRing.obj (modelTopos X).O).obj) :
    modelStructureStalkEquiv w ((((modelSitePoint B S hS W w).presheafFiber
        (A := CommRingCat.{u})).map (modelPullbackHom p).fSharpInverseImage.hom).hom b) =
      etaleLocalRingMap W.2 p.hom w (modelPullbackStalkEquiv w p b) :=
  modelPullbackHom_fSharpInverseImage_stalk_apply w p b

end PresheafFiber

/-! ### The base change map and its invertibility -/

section BaseChange

variable {f : X ⟶ Z} {g : Y ⟶ Z} {p : W ⟶ X} {q : W ⟶ Y}

attribute [local instance 10000] HasDerivedCategory.standard

/-- The change of base `L_{𝒪_W/p_m⁻¹f_m⁻¹𝒪_Z} ⟶ L_{𝒪_W/q_m⁻¹𝒪_Y}` along
`AlgebraicGeometry.Space.modelSquareBaseMap`. -/
abbrev modelSquareChangeOfBase (h : p ≫ f = q ≫ g) :=
  CategoryTheory.Sheaf.squareCotangentComplexMap
    (CategoryTheory.Sheaf.resolutionSquareMap.{u, u, u} (modelTopos W).J
      (modelSquareBaseMap f g p q h) (𝟙 _) (sq_modelSquareBaseMap h))

/-- **The canonical map `Lp_m^* L_{X/Z} ⟶ L_{W/Y}`** on the models: `Lp_m^* L_{X/Z}` is
`L_{p_m⁻¹𝒪_X/p_m⁻¹f_m⁻¹𝒪_Z} ⊗ 𝒪_W` (Tags 06YY, 08SV), followed by the first arrow of the
fundamental triangle of the tower `p_m⁻¹f_m⁻¹𝒪_Z ⟶ p_m⁻¹𝒪_X ⟶ 𝒪_W` (Tag 08SZ) and the change of
base along `p_m⁻¹f_m⁻¹𝒪_Z ⟶ q_m⁻¹𝒪_Y`. -/
def modelCotangentBaseChangeMap (h : p ≫ f = q ≫ g) :=
  (RingedToposHom.derivedPullbackCotangentComplexIso.{u, u, u, u, u, u, u, u + 1, u}
      (modelRingedToposHom f)
      (modelPullbackHom p)).hom ≫
    DerivedCategory.Q.map (CategoryTheory.Sheaf.towerCotangentBaseChange.{u, u, u}
      (modelTopos W).J
        (RingedToposHom.towerBaseMap.{u, u, u, u, u, u, u, u + 1, u} (modelRingedToposHom f)
        (modelPullbackHom p))
      (modelPullbackHom p).fSharpInverseImage ≫ modelSquareChangeOfBase h)

/-- **Stacks 09DL on the models, at a geometric point**, for a cone of the base change map written
out. -/
theorem isZero_derivedModuleFiber_of_distTriang_modelBaseChange_aux (hpb : IsPullback p q f g)
    {M : DerivedCategory (modelModules W)}
    {β : (modelRingedToposHom q).cotangentComplexDerived ⟶ M}
    {γ : M ⟶ ((RingedToposHom.derivedPullback.{u, u, u, u, u, u} (modelPullbackHom p)).obj
      (modelRingedToposHom f).cotangentComplexDerived)⟦(1 : ℤ)⟧}
    (hT' : Triangle.mk ((RingedToposHom.derivedPullbackCotangentComplexIso.{u, u, u, u, u, u, u,
        u + 1, u} (modelRingedToposHom f) (modelPullbackHom p)).hom ≫ DerivedCategory.Q.map
      (CategoryTheory.Sheaf.towerCotangentBaseChange.{u, u, u} (modelTopos W).J
        (RingedToposHom.towerBaseMap.{u, u, u, u, u, u, u, u + 1, u} (modelRingedToposHom f)
          (modelPullbackHom p)) (modelPullbackHom p).fSharpInverseImage ≫
        modelSquareChangeOfBase hpb.w)) β γ ∈ distTriang _)
    (w : GeometricPoint B S hS W.1)
    [iA : Algebra (etaleLocalRing B S hS Z.1 (geometricPointMap g.hom (geometricPointMap q.hom w)))
      (etaleLocalRing B S hS Y.1 (geometricPointMap q.hom w))]
    [iB : Algebra (etaleLocalRing B S hS Z.1 (geometricPointMap g.hom (geometricPointMap q.hom w)))
      (etaleLocalRing B S hS X.1 (geometricPointMap p.hom w))]
    (hAlgA : algebraMap
      (etaleLocalRing B S hS Z.1 (geometricPointMap g.hom (geometricPointMap q.hom w)))
      (etaleLocalRing B S hS Y.1 (geometricPointMap q.hom w)) =
        etaleLocalRingMap Y.2 g.hom (geometricPointMap q.hom w))
    (hAlgB : algebraMap
      (etaleLocalRing B S hS Z.1 (geometricPointMap g.hom (geometricPointMap q.hom w)))
      (etaleLocalRing B S hS X.1 (geometricPointMap p.hom w)) =
        (eqToHom (congrArg (etaleLocalRing B S hS Z.1)
          (congrArg (fun k : W ⟶ Z => geometricPointMap k.hom w) hpb.flip.w)) ≫
        CommRingCat.ofHom (etaleLocalRingMap X.2 f.hom (geometricPointMap p.hom w))).hom)
    (φ : TensorProduct
      (etaleLocalRing B S hS Z.1 (geometricPointMap g.hom (geometricPointMap q.hom w)))
      (etaleLocalRing B S hS Y.1 (geometricPointMap q.hom w))
      (etaleLocalRing B S hS X.1 (geometricPointMap p.hom w)) →+* etaleLocalRing B S hS W.1 w)
    (hφA : φ.comp Algebra.TensorProduct.includeLeftRingHom = etaleLocalRingMap W.2 q.hom w)
    (hφB : φ.comp Algebra.TensorProduct.includeRight.toRingHom = etaleLocalRingMap W.2 p.hom w)
    (hW : @Algebra.WeaklyEtale _ _ _ _ φ.toAlgebra)
    (hT₀ : RingTheory.TorIndependence.TorIndependent
      (etaleLocalRing B S hS Z.1 (geometricPointMap g.hom (geometricPointMap q.hom w)))
      (etaleLocalRing B S hS Y.1 (geometricPointMap q.hom w))
      (etaleLocalRing B S hS X.1 (geometricPointMap p.hom w))) :
    IsZero ((Stacks.derivedModuleFiber (modelSitePoint B S hS W w) (modelTopos W).O).obj M) := by
  exact
    CategoryTheory.Sheaf.isZero_derivedModuleFiber_of_ringEquiv_of_torIndependent.{u, u, u, u + 1}
    (modelTopos W).J (modelSitePoint B S hS W w)
    (RingedToposHom.towerBaseMap.{u, u, u, u, u, u, u, u + 1, u} (modelRingedToposHom f)
        (modelPullbackHom p))
    (modelPullbackHom p).fSharpInverseImage (modelSquareBaseMap f g p q hpb.w)
    (sq_modelSquareBaseMap hpb.w) φ hW
    (modelTowerBaseStalkEquiv w hpb.w) (modelInverseImageStalkEquiv w q)
    (modelPullbackStalkEquiv w p) (modelStructureStalkEquiv w)
    (fun r => (modelSquareBaseMap_presheafFiber_apply w hpb.w r).trans
      (RingHom.congr_fun hAlgA _).symm)
    (fun r => (towerBaseMap_presheafFiber_apply w hpb.w r).trans (RingHom.congr_fun hAlgB _).symm)
    (fun a => (modelRingedToposHom_fSharpInverseImage_presheafFiber_apply w a).trans
      (RingHom.congr_fun hφA (modelInverseImageStalkEquiv w q a)).symm)
    (fun b => (modelPullbackHom_fSharpInverseImage_presheafFiber_apply w b).trans
      (RingHom.congr_fun hφB (modelPullbackStalkEquiv w p b)).symm) hT₀
    (RingedToposHom.derivedPullbackCotangentComplexIso.{u, u, u, u, u, u, u, u + 1, u}
      (modelRingedToposHom f) (modelPullbackHom p)) hT'

/-- **The rings of a Tor independent cartesian square at a geometric point** (Stacks 04NG,
Stacks 08IP): at a geometric point `w̄` of `W`, the étale local rings `𝒪_{Y, q(w̄)}` and
`𝒪_{X, p(w̄)}` are Tor independent over `𝒪_{Z, g(q(w̄))}`, and `𝒪_{W, w̄}` is weakly étale
over their
tensor product, compatibly with the homomorphisms of étale local rings. -/
theorem exists_modelBaseChange_stalkData (hpb : IsPullback p q f g)
    (hTor : TorIndependent Y.2 X.2 Z.2 g.hom f.hom) (w : GeometricPoint B S hS W.1) :
    letI : Algebra (etaleLocalRing B S hS Z.1 (geometricPointMap g.hom (geometricPointMap q.hom w)))
        (etaleLocalRing B S hS Y.1 (geometricPointMap q.hom w)) :=
      (etaleLocalRingMap Y.2 g.hom (geometricPointMap q.hom w)).toAlgebra
    letI : Algebra (etaleLocalRing B S hS Z.1 (geometricPointMap g.hom (geometricPointMap q.hom w)))
        (etaleLocalRing B S hS X.1 (geometricPointMap p.hom w)) :=
      ((eqToHom (congrArg (etaleLocalRing B S hS Z.1)
          (congrArg (fun k : W ⟶ Z => geometricPointMap k.hom w) hpb.flip.w)) ≫
        CommRingCat.ofHom (etaleLocalRingMap X.2 f.hom (geometricPointMap p.hom w))).hom).toAlgebra
    ∃ φ : TensorProduct
        (etaleLocalRing B S hS Z.1 (geometricPointMap g.hom (geometricPointMap q.hom w)))
        (etaleLocalRing B S hS Y.1 (geometricPointMap q.hom w))
        (etaleLocalRing B S hS X.1 (geometricPointMap p.hom w)) →+* etaleLocalRing B S hS W.1 w,
      φ.comp Algebra.TensorProduct.includeLeftRingHom = etaleLocalRingMap W.2 q.hom w ∧
      φ.comp Algebra.TensorProduct.includeRight.toRingHom = etaleLocalRingMap W.2 p.hom w ∧
      @Algebra.WeaklyEtale _ _ _ _ φ.toAlgebra ∧
      RingTheory.TorIndependence.TorIndependent
        (etaleLocalRing B S hS Z.1 (geometricPointMap g.hom (geometricPointMap q.hom w)))
        (etaleLocalRing B S hS Y.1 (geometricPointMap q.hom w))
        (etaleLocalRing B S hS X.1 (geometricPointMap p.hom w)) := by
  obtain ⟨φ₀, ψ₀, hφ₀, hψ₀, hT₀⟩ := hTor (geometricPointMap q.hom w) (geometricPointMap p.hom w)
    (congrArg (fun k : W ⟶ Z => geometricPointMap k.hom w) hpb.flip.w)
  obtain rfl := eq_etaleLocalRingMap Y.2 g.hom _ hφ₀
  obtain rfl := eq_etaleLocalRingMap X.2 f.hom _ hψ₀
  obtain ⟨φ, hφA, hφB, hW⟩ := cartesian_etaleStalk_tensor_weaklyEtale B S hS q p g f hpb.flip w
  exact ⟨φ, hφA, hφB, hW, hT₀⟩

/-- **Stacks 09DL on the models, at a geometric point**, for a cone of the base change map written
out. -/
theorem isZero_derivedModuleFiber_of_distTriang_modelBaseChange (hpb : IsPullback p q f g)
    (hTor : TorIndependent Y.2 X.2 Z.2 g.hom f.hom)
    {M : DerivedCategory (modelModules W)}
    {β : (modelRingedToposHom q).cotangentComplexDerived ⟶ M}
    {γ : M ⟶ ((RingedToposHom.derivedPullback.{u, u, u, u, u, u} (modelPullbackHom p)).obj
      (modelRingedToposHom f).cotangentComplexDerived)⟦(1 : ℤ)⟧}
    (hT' : Triangle.mk ((RingedToposHom.derivedPullbackCotangentComplexIso.{u, u, u, u, u, u, u,
        u + 1, u} (modelRingedToposHom f) (modelPullbackHom p)).hom ≫ DerivedCategory.Q.map
      (CategoryTheory.Sheaf.towerCotangentBaseChange.{u, u, u} (modelTopos W).J
        (RingedToposHom.towerBaseMap.{u, u, u, u, u, u, u, u + 1, u} (modelRingedToposHom f)
          (modelPullbackHom p)) (modelPullbackHom p).fSharpInverseImage ≫
        modelSquareChangeOfBase hpb.w)) β γ ∈ distTriang _)
    (w : GeometricPoint B S hS W.1) :
    IsZero ((Stacks.derivedModuleFiber (modelSitePoint B S hS W w) (modelTopos W).O).obj M) := by
  obtain ⟨φ, hφA, hφB, hW, hT₀⟩ := exists_modelBaseChange_stalkData hpb hTor w
  exact isZero_derivedModuleFiber_of_distTriang_modelBaseChange_aux hpb hT' w
    (iA := (etaleLocalRingMap Y.2 g.hom (geometricPointMap q.hom w)).toAlgebra)
    (iB := ((eqToHom (congrArg (etaleLocalRing B S hS Z.1)
        (congrArg (fun k : W ⟶ Z => geometricPointMap k.hom w) hpb.flip.w)) ≫
      CommRingCat.ofHom (etaleLocalRingMap X.2 f.hom (geometricPointMap p.hom w))).hom).toAlgebra)
    rfl rfl φ hφA hφB hW hT₀

/-- **Stacks 09DL on the models, at a geometric point.** The derived stalk at the point of every
geometric point of `W` of a cone of `modelCotangentBaseChangeMap` vanishes. -/
theorem isZero_derivedModuleFiber_modelCotangentBaseChangeCone (hpb : IsPullback p q f g)
    (hTor : TorIndependent Y.2 X.2 Z.2 g.hom f.hom)
    {M : DerivedCategory (modelModules W)}
    {β : (modelRingedToposHom q).cotangentComplexDerived ⟶ M}
    {γ : M ⟶ ((RingedToposHom.derivedPullback.{u, u, u, u, u, u} (modelPullbackHom p)).obj
      (modelRingedToposHom f).cotangentComplexDerived)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (modelCotangentBaseChangeMap hpb.w) β γ ∈ distTriang _)
    (w : GeometricPoint B S hS W.1) :
    IsZero ((Stacks.derivedModuleFiber (modelSitePoint B S hS W w) (modelTopos W).O).obj M) := by
  exact isZero_derivedModuleFiber_of_distTriang_modelBaseChange (M := M) (β := β) (γ := γ)
    hpb hTor hT w

/-- **Stacks 09DL on the models.** For a cartesian square of algebraic spaces with `X` and `Y` Tor
independent over `Z`, the canonical map `Lp_m^* L_{X/Z} ⟶ L_{W/Y}` on the `Type u` models is an
isomorphism: its cone vanishes on derived stalks at the geometric points of `W`, a conservative
family of points of the model. -/
theorem isIso_modelCotangentBaseChangeMap (hpb : IsPullback p q f g)
    (hTor : TorIndependent Y.2 X.2 Z.2 g.hom f.hom) :
    IsIso (modelCotangentBaseChangeMap hpb.w) := by
  obtain ⟨M, β, γ, hT⟩ := distinguished_cocone_triangle (modelCotangentBaseChangeMap hpb.w)
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 ?_
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro i
  exact Stacks.isZero_homology_of_forall_isZero_homology_derivedModuleFiber (modelTopos W).O M
    (modelSitePoint B S hS W) (isConservativeFamilyOfPoints_modelSitePoint B S hS W) i fun w =>
      (DerivedCategory.homologyFunctor _ i).map_isZero
        (isZero_derivedModuleFiber_modelCotangentBaseChangeCone hpb hTor hT w)

/-- The inverse of `AlgebraicGeometry.Space.modelCotangentBaseChangeMap`. -/
def modelCotangentBaseChangeInv (hpb : IsPullback p q f g)
    (hTor : TorIndependent Y.2 X.2 Z.2 g.hom f.hom) :=
  inv (modelCotangentBaseChangeMap (W := W) (X := X) (Y := Y) (Z := Z) (f := f) (g := g) (p := p)
    (q := q) hpb.w) (I := isIso_modelCotangentBaseChangeMap hpb hTor)

/-- `AlgebraicGeometry.Space.modelCotangentBaseChangeInv` is a right inverse. -/
theorem modelCotangentBaseChangeMap_hom_inv_id (hpb : IsPullback p q f g)
    (hTor : TorIndependent Y.2 X.2 Z.2 g.hom f.hom) :
    modelCotangentBaseChangeMap hpb.w ≫ modelCotangentBaseChangeInv hpb hTor = 𝟙 _ :=
  IsIso.hom_inv_id (modelCotangentBaseChangeMap hpb.w)
    (I := isIso_modelCotangentBaseChangeMap hpb hTor)

/-- `AlgebraicGeometry.Space.modelCotangentBaseChangeInv` is a left inverse. -/
theorem modelCotangentBaseChangeMap_inv_hom_id (hpb : IsPullback p q f g)
    (hTor : TorIndependent Y.2 X.2 Z.2 g.hom f.hom) :
    modelCotangentBaseChangeInv hpb hTor ≫ modelCotangentBaseChangeMap hpb.w = 𝟙 _ :=
  IsIso.inv_hom_id (modelCotangentBaseChangeMap hpb.w)
    (I := isIso_modelCotangentBaseChangeMap hpb hTor)

attribute [local instance 20000] SheafOfModules.instAbelian in
/-- `AlgebraicGeometry.Space.modelCotangentBaseChangeMap` as an isomorphism, in the spelling of
its own source and target. -/
def modelCotangentBaseChangeIsoAux (hpb : IsPullback p q f g)
    (hTor : TorIndependent Y.2 X.2 Z.2 g.hom f.hom) :=
  Iso.mk (modelCotangentBaseChangeMap (W := W) (X := X) (Y := Y) (Z := Z) (f := f) (g := g)
      (p := p) (q := q) hpb.w) (modelCotangentBaseChangeInv hpb hTor)
    (modelCotangentBaseChangeMap_hom_inv_id hpb hTor)
    (modelCotangentBaseChangeMap_inv_hom_id hpb hTor)

/-- **Stacks 09DL on the models**, as an isomorphism `Lp_m^* L_{X/Z} ≅ L_{W/Y}` in the derived
category of `𝒪_W`-modules on the model of `W`, for a cartesian square of algebraic spaces with
`X` and `Y` Tor independent over `Z`. -/
def modelCotangentBaseChangeIso (hpb : IsPullback p q f g)
    (hTor : TorIndependent Y.2 X.2 Z.2 g.hom f.hom) :
    (RingedToposHom.derivedPullback.{u, u, u, u, u, u} (modelPullbackHom p)).obj
        (modelRingedToposHom f).cotangentComplexDerived ≅
      (modelRingedToposHom q).cotangentComplexDerived :=
  (Iso.refl ((RingedToposHom.derivedPullback.{u, u, u, u, u, u} (modelPullbackHom p)).obj
      (modelRingedToposHom f).cotangentComplexDerived)
      ≪≫ modelCotangentBaseChangeIsoAux hpb hTor) ≪≫
    Iso.refl ((modelRingedToposHom q).cotangentComplexDerived)

end BaseChange

end AlgebraicGeometry.Space

end
