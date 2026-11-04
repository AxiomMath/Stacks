module

public import StacksFrontier.Cotangent.Spaces.FibreProductCornerStalk
public import StacksFrontier.Cotangent.Triangle.DisplayMorphisms
public import StacksFrontier.Cotangent.TensorProductWeaklyEtaleCone
public import StacksFrontier.Cotangent.TensorProductCohomologyCanonical

/-!
# The right column of Stacks 09DK at a point, as the fundamental triangle of the stalk rings

Let `A ⟶ B ⟶ D` be homomorphisms of sheaves of rings on a site and `Φ` a point. The first arrow
`L_{B/A} ⊗_B D ⟶ L_{D/A}` of Tag 08SZ followed by a map `L_{D/A} ⟶ L_{D/A₂}` that changes the
base along `a : A ⟶ A₂` at `Φ` (`CategoryTheory.Sheaf.IsPointStalkBaseMap`) has, as derived stalk
at `Φ`, the first displayed morphism of the fundamental triangle of `A_Φ → B_Φ → D_Φ` followed by
the second displayed morphism of `A_Φ → (A₂)_Φ → D_Φ`
(`CategoryTheory.Sheaf.derivedModuleFiber_map_towerCotangentBaseChange_comp`). Consequently the
derived stalk of a cone of such a composite is a cone of
`L_{B_Φ/A_Φ} ⊗^𝐋_{B_Φ} D_Φ ⟶ L_{D_Φ/A_Φ} ⟶ L_{D_Φ/(A₂)_Φ}`
(`CategoryTheory.Sheaf.exists_distTriang_derivedModuleFiber_fundamental`).

The right column `Lq^*L_{Y/Z} ⟶ L_{W/X} ⟶ E ⟶` of the diagram of Stacks 09DK is of that form
(`AlgebraicGeometry.Space.fibreProductColumnUnit_comp_transitivityCounit_eq`,
`AlgebraicGeometry.Space.isPointStalkBaseMap_columnChain`), and the ring-theoretic content of
Stacks 09DM is `CommAlgCat.homology_cone_fundamentalMor_of_weaklyEtale`: for `A ⊗_R B → C` weakly
étale, a cone of `L_{B/R} ⊗^𝐋_B C ⟶ L_{C/R} ⟶ L_{C/A}` has no cohomology in degrees `≥ -1` and
`H^{-2} = Tor_1^R(A, B) ⊗_{A ⊗_R B} C`, by Stacks 09DB.

## References

* [Stacks Project, Tag 09DK](https://stacks.math.columbia.edu/tag/09DK)
* [Stacks Project, Tag 09DM](https://stacks.math.columbia.edu/tag/09DM)
* [Stacks Project, Tag 09DB](https://stacks.math.columbia.edu/tag/09DB)
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 08T0](https://stacks.math.columbia.edu/tag/08T0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped TensorProduct

universe u v w

namespace CommAlgCat

section WeaklyEtale

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R] (A B : Type u) [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (C : Type u) [CommRing C] [Algebra (A ⊗[R] B) C] [Algebra R C] [Algebra A C] [Algebra B C]
  [IsScalarTower R (A ⊗[R] B) C] [IsScalarTower A (A ⊗[R] B) C] [IsScalarTower B (A ⊗[R] B) C]
  [IsScalarTower R A C] [IsScalarTower R B C] [Algebra.WeaklyEtale (A ⊗[R] B) C]

/-- **The ring-theoretic content of Stacks 09DM.** If `A ⊗_R B → C` is weakly étale, every cone
`E_C` of `L_{B/R} ⊗^𝐋_B C ⟶ L_{C/R} ⟶ L_{C/A}` has `H^i(E_C) = 0` for `i ≥ -1` and
`H^{-2}(E_C) ≅ Tor_1^R(A, B) ⊗_{A ⊗_R B} C` as `C`-modules: by
`CommAlgCat.nonempty_homology_cone_iso_extendScalars_tensorProduct` its cohomology is that of the
object `E` of the nine diagram of `R → A, R → B` tensored up to `C`, and Stacks 09DB computes
the latter. -/
theorem homology_cone_fundamentalMor_of_weaklyEtale {EC : DerivedCategory (ModuleCat.{u} C)}
    {b' : cotangentComplexDerived.{u, u} A (CommAlgCat.of A C) ⟶ EC}
    {e' : EC ⟶ (fundamentalVertex₁.{u, u, u + 1, u + 1} R B C)⟦(1 : ℤ)⟧}
    (hC : Triangle.mk (fundamentalMor₁.{u} R B C ≫ fundamentalMor₂.{u} R A C) b' e' ∈
      distTriang (DerivedCategory (ModuleCat.{u} C))) :
    (∀ i : ℤ, -1 ≤ i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} C) i).obj EC)) ∧
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} C) (-2)).obj EC ≅
        (ModuleCat.extendScalars.{u, u, u} (algebraMap (A ⊗[R] B) C)).obj
          (torOneTensorProductModule R A B)) := by
  have hE := canonicalTensorProductNineDiagram_rightColumn R A B
  refine ⟨fun i hi => ?_, ?_⟩
  · obtain ⟨φ⟩ := nonempty_homology_cone_iso_extendScalars_tensorProduct R A B C hE hC i
    exact (Functor.map_isZero _ (isZero_homology_of_tensorProduct_rightColumn hE i hi)).of_iso φ
  · obtain ⟨φ⟩ := nonempty_homology_cone_iso_extendScalars_tensorProduct R A B C hE hC (-2)
    exact ⟨φ ≪≫ (ModuleCat.extendScalars.{u, u, u} (algebraMap (A ⊗[R] B) C)).mapIso
      (homologyNegTwoIsoTorOneOfRightColumn hE)⟩

end WeaklyEtale

end CommAlgCat

namespace CategoryTheory.Sheaf

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [LocallySmall.{max u v w} C] (Φ : J.Point.{max u v w})
  {A B D A₂ : Sheaf J CommRingCat.{max u v w}} (g : A ⟶ B) (h : B ⟶ D) {f₂ : A₂ ⟶ D}

omit [LocallySmall.{max u v w} C] in
/-- The stalk maps of a tower `A ⟶ B ⟶ D` of sheaves of rings make the stalks a tower of rings. -/
theorem isScalarTower_pointStalk :
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj B.obj) := ((Φ.presheafFiber (A := CommRingCat)).map g.hom).hom.toAlgebra
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj B.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj D.obj) := ((Φ.presheafFiber (A := CommRingCat)).map h.hom).hom.toAlgebra
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj D.obj) :=
      ((Φ.presheafFiber (A := CommRingCat)).map (g ≫ h).hom).hom.toAlgebra
    IsScalarTower ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj B.obj) ((Φ.presheafFiber (A := CommRingCat)).obj D.obj) := by
  let : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
      CommRingCat)).obj B.obj) := ((Φ.presheafFiber (A := CommRingCat)).map g.hom).hom.toAlgebra
  let : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj B.obj) ((Φ.presheafFiber (A :=
      CommRingCat)).obj D.obj) := ((Φ.presheafFiber (A := CommRingCat)).map h.hom).hom.toAlgebra
  let : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
      CommRingCat)).obj D.obj) :=
    ((Φ.presheafFiber (A := CommRingCat)).map (g ≫ h).hom).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun z => ?_
  change ((Φ.presheafFiber (A := CommRingCat)).map (g.hom ≫ h.hom)).hom z =
    ((Φ.presheafFiber (A := CommRingCat)).map h.hom).hom
      (((Φ.presheafFiber (A := CommRingCat)).map g.hom).hom z)
  rw [Functor.map_comp]
  rfl

omit [LocallySmall.{max u v w} C] in
/-- The stalk maps of `a : A ⟶ A₂` and `f₂ : A₂ ⟶ D` over `g ≫ h` make the stalks a tower of
rings. -/
theorem isScalarTower_pointStalk_base (a : A ⟶ A₂) (hsq : (g ≫ h) ≫ 𝟙 D = a ≫ f₂) :
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj A₂.obj) := ((Φ.presheafFiber (A := CommRingCat)).map a.hom).hom.toAlgebra
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A₂.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj D.obj) := ((Φ.presheafFiber (A := CommRingCat)).map f₂.hom).hom.toAlgebra
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj D.obj) :=
      ((Φ.presheafFiber (A := CommRingCat)).map (g ≫ h).hom).hom.toAlgebra
    IsScalarTower ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj A₂.obj) ((Φ.presheafFiber (A := CommRingCat)).obj D.obj) := by
  let : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
      CommRingCat)).obj A₂.obj) := ((Φ.presheafFiber (A := CommRingCat)).map a.hom).hom.toAlgebra
  let : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A₂.obj) ((Φ.presheafFiber (A :=
      CommRingCat)).obj D.obj) := ((Φ.presheafFiber (A := CommRingCat)).map f₂.hom).hom.toAlgebra
  let : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
      CommRingCat)).obj D.obj) :=
    ((Φ.presheafFiber (A := CommRingCat)).map (g ≫ h).hom).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun z => ?_
  have e : (g ≫ h).hom = a.hom ≫ f₂.hom :=
    congrArg (fun k : A ⟶ D => k.hom) ((Category.comp_id _).symm.trans hsq)
  change ((Φ.presheafFiber (A := CommRingCat)).map (g ≫ h).hom).hom z =
    ((Φ.presheafFiber (A := CommRingCat)).map f₂.hom).hom
      (((Φ.presheafFiber (A := CommRingCat)).map a.hom).hom z)
  rw [e, Functor.map_comp]
  rfl

/-- **The stalk of the first arrow of Tag 08SZ followed by a change of base**, as an equation of
maps of complexes of `D_Φ`-modules: it is the first displayed morphism of the fundamental
triangle of the stalk rings `A_Φ → B_Φ → D_Φ` followed by the second displayed morphism of
`A_Φ → (A₂)_Φ → D_Φ`, at the level of complexes. -/
theorem stalk_towerCotangentBaseChange_comp (a : A ⟶ A₂)
    (hsq : (g ≫ h) ≫ 𝟙 D = a ≫ f₂) (Θ : cotangentComplex J (g ≫ h) ⟶ cotangentComplex J f₂)
    (hΘ : IsPointStalkBaseMap J Φ a hsq Θ) :
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj B.obj) := ((Φ.presheafFiber (A := CommRingCat)).map g.hom).hom.toAlgebra
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj B.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj D.obj) := ((Φ.presheafFiber (A := CommRingCat)).map h.hom).hom.toAlgebra
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj D.obj) :=
      ((Φ.presheafFiber (A := CommRingCat)).map (g ≫ h).hom).hom.toAlgebra
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj A₂.obj) := ((Φ.presheafFiber (A := CommRingCat)).map a.hom).hom.toAlgebra
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A₂.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj D.obj) := ((Φ.presheafFiber (A := CommRingCat)).map f₂.hom).hom.toAlgebra
    haveI := isScalarTower_pointStalk J Φ g h
    haveI := isScalarTower_pointStalk_base J Φ g h a hsq
    (stalkBaseChangedCotangentComplexIso Φ g h).inv ≫
        ((Stacks.sheafModuleFiberOfCommRing Φ D).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (towerCotangentBaseChange.{u, v, w} J g h ≫ Θ) ≫
        (pointStalkCotangentComplexIso J Φ f₂).hom =
      ((ModuleCat.extendScalars (Stacks.SitePointBaseChange.stalkRingHom h.hom
          Φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (pointStalkCotangentComplexIso J Φ g).hom ≫
        CommAlgCat.cotangentExtendScalarsComplexMap (A := ((Φ.presheafFiber (A := CommRingCat)).obj
            A.obj))
          (A' := ((Φ.presheafFiber (A := CommRingCat)).obj A.obj))
          (B := CommAlgCat.of ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A
              := CommRingCat)).obj B.obj)) (B' := CommAlgCat.of ((Φ.presheafFiber (A :=
                  CommRingCat)).obj A.obj) ((Φ.presheafFiber (A := CommRingCat)).obj D.obj))
          (IsScalarTower.toAlgHom ((Φ.presheafFiber (A := CommRingCat)).obj A.obj)
              ((Φ.presheafFiber (A := CommRingCat)).obj B.obj) ((Φ.presheafFiber (A :=
                  CommRingCat)).obj D.obj)) ≫
        CommAlgCat.cotangentComplexBaseRingMap ((Φ.presheafFiber (A := CommRingCat)).obj A.obj)
            ((Φ.presheafFiber (A := CommRingCat)).obj A₂.obj) ((Φ.presheafFiber (A :=
                CommRingCat)).obj D.obj) :=
  HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext (LinearMap.ext fun y =>
    stalk_towerCotangentBaseChange_comp_apply J Φ g h a hsq Θ hΘ n y)

/-- The derived stalk of `L_{B/A} ⊗_B D` is the first vertex `L_{B_Φ/A_Φ} ⊗^𝐋_{B_Φ} D_Φ` of the
fundamental triangle of the stalk rings. -/
def derivedModuleFiberBaseChangedCotangentIso :
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj B.obj) := ((Φ.presheafFiber (A := CommRingCat)).map g.hom).hom.toAlgebra
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj B.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj D.obj) := ((Φ.presheafFiber (A := CommRingCat)).map h.hom).hom.toAlgebra
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj D.obj) :=
      ((Φ.presheafFiber (A := CommRingCat)).map (g ≫ h).hom).hom.toAlgebra
    haveI := isScalarTower_pointStalk J Φ g h
    (Stacks.derivedModuleFiber Φ D).obj
        (DerivedCategory.Q.obj (baseChangedCotangentComplex.{u, v, w} J g h)) ≅
      CommAlgCat.fundamentalVertex₁.{max u v w, max u v w, max u v w + 1, max u v w + 1}
        ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A := CommRingCat)).obj
            B.obj) ((Φ.presheafFiber (A := CommRingCat)).obj D.obj) :=
  letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
      CommRingCat)).obj B.obj) := ((Φ.presheafFiber (A := CommRingCat)).map g.hom).hom.toAlgebra
  letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj B.obj) ((Φ.presheafFiber (A :=
      CommRingCat)).obj D.obj) := ((Φ.presheafFiber (A := CommRingCat)).map h.hom).hom.toAlgebra
  letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
      CommRingCat)).obj D.obj) :=
    ((Φ.presheafFiber (A := CommRingCat)).map (g ≫ h).hom).hom.toAlgebra
  haveI := isScalarTower_pointStalk J Φ g h
  (Stacks.sheafModuleFiberOfCommRing Φ D).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso (stalkBaseChangedCotangentComplexIso Φ g h) ≪≫
    DerivedCategory.Q.mapIso
      (((ModuleCat.extendScalars (Stacks.SitePointBaseChange.stalkRingHom h.hom
          Φ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso (pointStalkCotangentComplexIso J Φ g)) ≪≫
    (CommAlgCat.cotangentComplexDerivedBaseChangeTermwiseIso ((Φ.presheafFiber (A :=
        CommRingCat)).obj A.obj)
      (CommAlgCat.of ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
          CommRingCat)).obj B.obj)) ((Φ.presheafFiber (A := CommRingCat)).obj D.obj)).symm

/-- The derived stalk of `L_{D/A₂}` is `L_{D_Φ/(A₂)_Φ}`. -/
def derivedModuleFiberCotangentIso :
    (Stacks.derivedModuleFiber Φ D).obj (DerivedCategory.Q.obj (cotangentComplex J f₂)) ≅
      DerivedCategory.Q.obj (CommAlgCat.cotangentComplex.{max u v w, max u v w} _
        (pointStalkAlgebra J Φ f₂)) :=
  (Stacks.sheafModuleFiberOfCommRing Φ D).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso (pointStalkCotangentComplexIso J Φ f₂)

/-- **The derived stalk of the first arrow of Tag 08SZ followed by a change of base.** If
`Θ : L_{D/A} ⟶ L_{D/A₂}` changes the base along `a : A ⟶ A₂` at `Φ`, then the derived stalk at
`Φ` of `L_{B/A} ⊗_B D ⟶ L_{D/A} ⟶ L_{D/A₂}` is, through the identifications of the vertices,
the first displayed morphism of the fundamental triangle of `A_Φ → B_Φ → D_Φ` followed by the
second displayed morphism of `A_Φ → (A₂)_Φ → D_Φ`. -/
theorem derivedModuleFiber_map_towerCotangentBaseChange_comp (a : A ⟶ A₂)
    (hsq : (g ≫ h) ≫ 𝟙 D = a ≫ f₂) (Θ : cotangentComplex J (g ≫ h) ⟶ cotangentComplex J f₂)
    (hΘ : IsPointStalkBaseMap J Φ a hsq Θ) :
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj B.obj) := ((Φ.presheafFiber (A := CommRingCat)).map g.hom).hom.toAlgebra
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj B.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj D.obj) := ((Φ.presheafFiber (A := CommRingCat)).map h.hom).hom.toAlgebra
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj D.obj) :=
      ((Φ.presheafFiber (A := CommRingCat)).map (g ≫ h).hom).hom.toAlgebra
    haveI := isScalarTower_pointStalk J Φ g h
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj A₂.obj) := ((Φ.presheafFiber (A := CommRingCat)).map a.hom).hom.toAlgebra
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A₂.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj D.obj) := ((Φ.presheafFiber (A := CommRingCat)).map f₂.hom).hom.toAlgebra
    haveI := isScalarTower_pointStalk_base J Φ g h a hsq
    (Stacks.derivedModuleFiber Φ D).map
        (DerivedCategory.Q.map (towerCotangentBaseChange.{u, v, w} J g h ≫ Θ)) =
      (derivedModuleFiberBaseChangedCotangentIso J Φ g h).hom ≫
        CommAlgCat.fundamentalMor₁ ((Φ.presheafFiber (A := CommRingCat)).obj A.obj)
            ((Φ.presheafFiber (A := CommRingCat)).obj B.obj) ((Φ.presheafFiber (A :=
                CommRingCat)).obj D.obj) ≫
        CommAlgCat.fundamentalMor₂ ((Φ.presheafFiber (A := CommRingCat)).obj A.obj)
            ((Φ.presheafFiber (A := CommRingCat)).obj A₂.obj) ((Φ.presheafFiber (A :=
                CommRingCat)).obj D.obj) ≫
        (derivedModuleFiberCotangentIso J Φ (f₂ := f₂)).inv := by
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
  have key := stalk_towerCotangentBaseChange_comp J Φ g h a hsq Θ hΘ
  have nat := (Stacks.sheafModuleFiberOfCommRing Φ D).mapDerivedCategoryFactors_hom_naturality
    (towerCotangentBaseChange.{u, v, w} J g h ≫ Θ)
  have h1 := (Iso.eq_comp_inv ((Stacks.sheafModuleFiberOfCommRing Φ D).mapDerivedCategoryFactors.app
    (cotangentComplex J f₂))).mpr nat
  refine h1.trans ?_
  have h2 : ((Stacks.sheafModuleFiberOfCommRing Φ D).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (towerCotangentBaseChange.{u, v, w} J g h ≫ Θ) =
      (stalkBaseChangedCotangentComplexIso Φ g h).hom ≫ (((ModuleCat.extendScalars
        (Stacks.SitePointBaseChange.stalkRingHom h.hom Φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (pointStalkCotangentComplexIso J Φ g).hom ≫
        CommAlgCat.cotangentExtendScalarsComplexMap
          (A := ((Φ.presheafFiber (A := CommRingCat)).obj A.obj))
          (A' := ((Φ.presheafFiber (A := CommRingCat)).obj A.obj))
          (B := CommAlgCat.of ((Φ.presheafFiber (A := CommRingCat)).obj A.obj)
            ((Φ.presheafFiber (A := CommRingCat)).obj B.obj))
          (B' := CommAlgCat.of ((Φ.presheafFiber (A := CommRingCat)).obj A.obj)
            ((Φ.presheafFiber (A := CommRingCat)).obj D.obj))
          (IsScalarTower.toAlgHom ((Φ.presheafFiber (A := CommRingCat)).obj A.obj)
            ((Φ.presheafFiber (A := CommRingCat)).obj B.obj)
            ((Φ.presheafFiber (A := CommRingCat)).obj D.obj)) ≫
        CommAlgCat.cotangentComplexBaseRingMap ((Φ.presheafFiber (A := CommRingCat)).obj A.obj)
          ((Φ.presheafFiber (A := CommRingCat)).obj A₂.obj)
          ((Φ.presheafFiber (A := CommRingCat)).obj D.obj)) ≫
        (pointStalkCotangentComplexIso J Φ f₂).inv := by
    rw [← key]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rw [h2]
  simp only [derivedModuleFiberBaseChangedCotangentIso, derivedModuleFiberCotangentIso,
    CommAlgCat.fundamentalMor₁, CommAlgCat.fundamentalMor₂, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_assoc]
  refine congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_))
  exact (congrArg (· ≫ _) (Functor.map_comp DerivedCategory.Q _ _)).trans (Category.assoc _ _ _)

/-- **The derived stalk of a cone of the first arrow of Tag 08SZ followed by a change of base is
a cone of the composite of the two displayed morphisms of the stalk rings.** If a distinguished
triangle of `D(D)` starts with `K ≅ L_{B/A} ⊗_B D ⟶ L_{D/A} ⟶ L_{D/A₂}`, the second map changing
the base along `a : A ⟶ A₂` at `Φ`, then the derived stalk at `Φ` of its third vertex is the third
vertex of a distinguished triangle of `D(D_Φ)` on
`L_{B_Φ/A_Φ} ⊗^𝐋_{B_Φ} D_Φ ⟶ L_{D_Φ/A_Φ} ⟶ L_{D_Φ/(A₂)_Φ}`. -/
theorem exists_distTriang_derivedModuleFiber_fundamental (a : A ⟶ A₂)
    (hsq : (g ≫ h) ≫ 𝟙 D = a ≫ f₂) (Θ : cotangentComplex J (g ≫ h) ⟶ cotangentComplex J f₂)
    (hΘ : IsPointStalkBaseMap J Φ a hsq Θ)
    {K M : DerivedCategory (targetModules J D)}
    (e : K ≅ DerivedCategory.Q.obj (baseChangedCotangentComplex.{u, v, w} J g h))
    {β : DerivedCategory.Q.obj (cotangentComplex J f₂) ⟶ M} {γ : M ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (e.hom ≫ DerivedCategory.Q.map (towerCotangentBaseChange.{u, v, w} J g h ≫ Θ))
      β γ ∈ distTriang _) :
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj B.obj) := ((Φ.presheafFiber (A := CommRingCat)).map g.hom).hom.toAlgebra
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj B.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj D.obj) := ((Φ.presheafFiber (A := CommRingCat)).map h.hom).hom.toAlgebra
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj D.obj) :=
      ((Φ.presheafFiber (A := CommRingCat)).map (g ≫ h).hom).hom.toAlgebra
    letI := isScalarTower_pointStalk J Φ g h
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj A₂.obj) := ((Φ.presheafFiber (A := CommRingCat)).map a.hom).hom.toAlgebra
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A₂.obj) ((Φ.presheafFiber (A :=
        CommRingCat)).obj D.obj) := ((Φ.presheafFiber (A := CommRingCat)).map f₂.hom).hom.toAlgebra
    letI := isScalarTower_pointStalk_base J Φ g h a hsq
    ∃ (b' : CommAlgCat.fundamentalVertex₃.{max u v w, max u v w, max u v w + 1} ((Φ.presheafFiber
        (A := CommRingCat)).obj A₂.obj) ((Φ.presheafFiber (A := CommRingCat)).obj D.obj) ⟶
        (Stacks.derivedModuleFiber Φ D).obj M)
      (e' : (Stacks.derivedModuleFiber Φ D).obj M ⟶
        (CommAlgCat.fundamentalVertex₁.{max u v w, max u v w, max u v w + 1, max u v w + 1}
          ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
              CommRingCat)).obj B.obj) ((Φ.presheafFiber (A := CommRingCat)).obj D.obj))⟦(1 : ℤ)⟧),
      Triangle.mk (CommAlgCat.fundamentalMor₁ ((Φ.presheafFiber (A := CommRingCat)).obj A.obj)
          ((Φ.presheafFiber (A := CommRingCat)).obj B.obj) ((Φ.presheafFiber (A :=
              CommRingCat)).obj D.obj) ≫
        CommAlgCat.fundamentalMor₂ ((Φ.presheafFiber (A := CommRingCat)).obj A.obj)
            ((Φ.presheafFiber (A := CommRingCat)).obj A₂.obj) ((Φ.presheafFiber (A :=
                CommRingCat)).obj D.obj)) b' e' ∈ distTriang _ := by
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
  obtain ⟨e₁, e₂, key⟩ : ∃ (e₁ : (Stacks.derivedModuleFiber Φ D).obj K ≅
        CommAlgCat.fundamentalVertex₁.{max u v w, max u v w, max u v w + 1, max u v w + 1}
          ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) ((Φ.presheafFiber (A :=
              CommRingCat)).obj B.obj) ((Φ.presheafFiber (A := CommRingCat)).obj D.obj))
      (e₂ : (Stacks.derivedModuleFiber Φ D).obj (DerivedCategory.Q.obj (cotangentComplex J f₂)) ≅
        CommAlgCat.fundamentalVertex₃.{max u v w, max u v w, max u v w + 1} ((Φ.presheafFiber (A :=
            CommRingCat)).obj A₂.obj) ((Φ.presheafFiber (A := CommRingCat)).obj D.obj)),
      (Stacks.derivedModuleFiber Φ D).map
          (e.hom ≫ DerivedCategory.Q.map (towerCotangentBaseChange.{u, v, w} J g h ≫ Θ)) =
        e₁.hom ≫ CommAlgCat.fundamentalMor₁ ((Φ.presheafFiber (A := CommRingCat)).obj A.obj)
            ((Φ.presheafFiber (A := CommRingCat)).obj B.obj) ((Φ.presheafFiber (A :=
                CommRingCat)).obj D.obj) ≫
          CommAlgCat.fundamentalMor₂ ((Φ.presheafFiber (A := CommRingCat)).obj A.obj)
              ((Φ.presheafFiber (A := CommRingCat)).obj A₂.obj) ((Φ.presheafFiber (A :=
                  CommRingCat)).obj D.obj) ≫ e₂.inv :=
    ⟨(Stacks.derivedModuleFiber Φ D).mapIso e ≪≫ derivedModuleFiberBaseChangedCotangentIso J Φ g h,
      derivedModuleFiberCotangentIso J Φ (f₂ := f₂),
      ((Stacks.derivedModuleFiber Φ D).map_comp _ _).trans ((congrArg
        ((Stacks.derivedModuleFiber Φ D).map e.hom ≫ ·)
        (derivedModuleFiber_map_towerCotangentBaseChange_comp J Φ g h a hsq Θ hΘ)).trans
        (Category.assoc _ _ _).symm)⟩
  have hF := (Stacks.derivedModuleFiber Φ D).map_distinguished _ hT
  refine ⟨e₂.inv ≫ (Stacks.derivedModuleFiber Φ D).map β,
    ((Stacks.derivedModuleFiber Φ D).map γ ≫
      ((Stacks.derivedModuleFiber Φ D).commShiftIso (1 : ℤ)).hom.app K) ≫ e₁.hom⟦(1 : ℤ)⟧',
    isomorphic_distinguished _ hF _ (Triangle.isoMk _ _ e₁.symm e₂.symm (Iso.refl _) ?_ ?_ ?_)⟩
  · exact (Category.assoc _ _ _).trans
      ((Iso.inv_hom_id_assoc e₁ _).symm.trans (congrArg (e₁.inv ≫ ·) key.symm))
  · exact (Category.comp_id _).trans rfl
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      ((Functor.map_comp _ _ _).symm.trans ((congrArg _ e₁.hom_inv_id).trans
        (Functor.map_id _ _)))).trans ((Category.comp_id _).trans (Category.id_comp _).symm))

end CategoryTheory.Sheaf

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A₁ A₂ A₃ D : Sheaf J CommRingCat.{w}} {f₁ : A₁ ⟶ D} {f₂ : A₂ ⟶ D} {f₃ : A₃ ⟶ D}

/-- Squares over `D` compose. -/
theorem sq_comp {a : A₁ ⟶ A₂} {a' : A₂ ⟶ A₃} (hsq : f₁ ≫ 𝟙 D = a ≫ f₂)
    (hsq' : f₂ ≫ 𝟙 D = a' ≫ f₃) : f₁ ≫ 𝟙 D = (a ≫ a') ≫ f₃ := by
  rw [hsq, Category.assoc, ← hsq', Category.comp_id]

/-- A square over `D` along an isomorphism gives one along its inverse. -/
theorem sq_inv (e : A₁ ≅ A₂) (hsq : f₁ ≫ 𝟙 D = e.hom ≫ f₂) : f₂ ≫ 𝟙 D = e.inv ≫ f₁ :=
  (Category.comp_id _).trans ((Iso.eq_inv_comp e).mpr (hsq.symm.trans (Category.comp_id _)))

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z W : AlgebraicSpaces B S hS} {f : X ⟶ Z} {g : Y ⟶ Z} {p : W ⟶ X} {q : W ⟶ Y}

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat
  CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

attribute [local instance high] hasSheafify_smallEtaleRingedToposULift
  wEqualsLocallyBijective_smallEtaleRingedToposULift

/-- The inverse of `compBaseIso k l` is a map of rings over `𝒪_W`, from the base of the tower
structure map to the base of the structure map of the composite. -/
theorem sq_compCotangentComplexIso (k : W ⟶ Y) (l : Y ⟶ Z) :
    (RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
        (smallEtaleRingedToposHomULift l) (smallEtaleRingedToposHomULift k) ≫
      (smallEtaleRingedToposHomULift k).fSharpInverseImage) ≫ 𝟙 _ =
      (compBaseIso k l).inv ≫
        ((smallEtaleRingedToposHomULift l).comp (smallEtaleRingedToposHomULift
            k)).fSharpInverseImage :=
  Sheaf.sq_inv (compBaseIso k l)
    (RingedToposHom.comp_fSharpInverseImage_eq_tower.{u, u + 1, u, u, u + 1} _ _)

/-- The structure map of the composite of `k` and `l` agrees with `liftedStructureMap (k ≫ l)`
along `compBaseIso k l` followed by `towerBaseULiftIso k l`. -/
theorem sq_compCotangentComplexULiftIso (k : W ⟶ Y) (l : Y ⟶ Z) :
    ((smallEtaleRingedToposHomULift l).comp (smallEtaleRingedToposHomULift k)).fSharpInverseImage ≫
        𝟙 _ =
      ((compBaseIso k l).hom ≫ (towerBaseULiftIso k l).hom) ≫ liftedStructureMap (k ≫ l) :=
  Sheaf.sq_comp (RingedToposHom.comp_fSharpInverseImage_eq_tower.{u, u + 1, u, u, u + 1} _ _)
    (towerStructureMap_eq k l)

/-- For equal morphisms `k₁ = k₂`, the structure maps `liftedStructureMap k₁` and
`liftedStructureMap k₂` agree along the induced `eqToHom` of lifted base rings. -/
theorem sq_eqToHom {k₁ k₂ : W ⟶ Z} (e : k₁ = k₂) :
    liftedStructureMap k₁ ≫ 𝟙 _ =
      eqToHom (congrArg (fun k => liftedBaseRing (B := B) (S := S) (hS := hS) k) e) ≫
        liftedStructureMap k₂ := by
  subst e
  simp

/-- The structure map of `smallEtaleRingedToposHomULift k` agrees with `liftedStructureMap k`
along the inverse of `smallEtaleInverseImageRingULiftIso k` at the structure sheaf of `X`. -/
theorem sq_cotangentComplexIso (k : W ⟶ X) :
    (smallEtaleRingedToposHomULift k).fSharpInverseImage ≫ 𝟙 _ =
      (smallEtaleInverseImageRingULiftIso k).inv.app (smallEtaleRingedTopos B S hS X).O ≫
        liftedStructureMap k :=
  (Category.comp_id _).trans (smallEtaleRingedToposHomULift_fSharpInverseImage k)

/-- The composite base change of the string of `fibreProductColumnUnit_comp_transitivityCounit`:
`q⁻¹g⁻¹𝒪_Z ≅ (q ≫ g)⁻¹𝒪_Z = (p ≫ f)⁻¹𝒪_Z ≅ p⁻¹f⁻¹𝒪_Z ⟶ p⁻¹𝒪_X`, all lifted to the universe
of the site. -/
abbrev columnBaseMap (h : p ≫ f = q ≫ g) :=
  (towerBaseULiftIso q g).hom ≫
    eqToHom (congrArg (fun k => liftedBaseRing (B := B) (S := S) (hS := hS) k) h.symm) ≫
    (towerBaseULiftIso p f).inv ≫
    RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
        (smallEtaleRingedToposHomULift f) (smallEtaleRingedToposHomULift p) ≫
    (smallEtaleInverseImageRingULiftIso p).inv.app (smallEtaleRingedTopos B S hS X).O

/-- `columnBaseMap h` is unchanged by inserting the round trips through `compBaseIso q g` and
`compBaseIso p f`: this is the form in which the squares of its pieces compose. -/
theorem columnBaseMap_eq (h : p ≫ f = q ≫ g) :
    (compBaseIso q g).inv ≫ ((compBaseIso q g).hom ≫ (towerBaseULiftIso q g).hom) ≫
      eqToHom (congrArg (fun k => liftedBaseRing (B := B) (S := S) (hS := hS) k) h.symm) ≫
      ((towerBaseULiftIso p f).inv ≫ (compBaseIso p f).inv) ≫ (compBaseIso p f).hom ≫
      RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
        (smallEtaleRingedToposHomULift f) (smallEtaleRingedToposHomULift p) ≫
      (smallEtaleInverseImageRingULiftIso p).inv.app (smallEtaleRingedTopos B S hS X).O =
      columnBaseMap h := by
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans
    ((Iso.inv_hom_id_assoc (compBaseIso q g) _).trans ?_)
  refine congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_)
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Iso.inv_hom_id_assoc (compBaseIso p f) _))

/-- The square of the composite base change over `𝒪_W`. -/
theorem sq_columnBaseMap (h : p ≫ f = q ≫ g) :
    (RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
        (smallEtaleRingedToposHomULift g) (smallEtaleRingedToposHomULift q) ≫
      (smallEtaleRingedToposHomULift q).fSharpInverseImage) ≫ 𝟙 _ =
      columnBaseMap h ≫ liftedStructureMap p := by
  rw [← columnBaseMap_eq h]
  exact Sheaf.sq_comp (sq_compCotangentComplexIso q g) (Sheaf.sq_comp
    (sq_compCotangentComplexULiftIso q g) (Sheaf.sq_comp (sq_eqToHom h.symm) (Sheaf.sq_comp
      (Sheaf.sq_inv (compBaseIso p f ≪≫ towerBaseULiftIso p f)
        (sq_compCotangentComplexULiftIso p f)) (Sheaf.sq_comp
      (RingedToposHom.comp_fSharpInverseImage_eq_tower.{u, u + 1, u, u, u + 1} _ _)
      (Sheaf.sq_comp (by simp) (sq_cotangentComplexIso p))))))

/-- The string of changes of base and identifications of cotangent complexes that follows the
first arrow of Tag 08SZ in `fibreProductColumnUnit_comp_transitivityCounit`. -/
abbrev columnChain (h : p ≫ f = q ≫ g) :=
  (RingedToposHom.compCotangentComplexIso.{u, u + 1, u, u, u + 1} (smallEtaleRingedToposHomULift g)
      (smallEtaleRingedToposHomULift q)).inv ≫
    (compCotangentComplexULiftIso q g).hom ≫
    eqToHom (congrArg (cotangentComplex B S hS) h.symm) ≫
    (compCotangentComplexULiftIso p f).inv ≫
    (RingedToposHom.compCotangentComplexIso.{u, u + 1, u, u, u + 1} (smallEtaleRingedToposHomULift
        f)
      (smallEtaleRingedToposHomULift p)).hom ≫
    Sheaf.towerCotangentChangeOfBase.{u + 1, u, u} (SmallEtale.topology B S hS W.1)
      (RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
        (smallEtaleRingedToposHomULift f) (smallEtaleRingedToposHomULift p))
      (smallEtaleRingedToposHomULift p).fSharpInverseImage ≫
    (smallEtaleRingedToposHomULift_cotangentComplexIso p).hom

/-- **The string after the first arrow of 08SZ changes the base along `columnBaseMap`** at every
point of the small étale site of `W`. -/
theorem isPointStalkBaseMap_columnChain (h : p ≫ f = q ≫ g)
    (Φ : (SmallEtale.topology B S hS W.1).Point.{u + 1}) :
    Sheaf.IsPointStalkBaseMap.{u + 1, u, u} (SmallEtale.topology B S hS W.1) Φ
      (columnBaseMap h) (sq_columnBaseMap h) (columnChain h) := by
  have h7 := isPointStalkBaseMap_cotangentComplexIso Φ p (sq_cotangentComplexIso p)
  have h6 := isPointStalkBaseMap_towerCotangentChangeOfBase Φ p f
  have h5 := isPointStalkBaseMap_compCotangentComplexIso_hom Φ p f
  have h4 := isPointStalkBaseMap_compCotangentComplexULiftIso_inv Φ p f
    (Sheaf.sq_inv (compBaseIso p f ≪≫ towerBaseULiftIso p f) (sq_compCotangentComplexULiftIso p f))
  have h3 := isPointStalkBaseMap_eqToHom Φ h.symm (sq_eqToHom h.symm)
  have h2 := isPointStalkBaseMap_compCotangentComplexULiftIso_hom Φ q g
    (sq_compCotangentComplexULiftIso q g)
  have h1 := isPointStalkBaseMap_compCotangentComplexIso_inv Φ q g (sq_compCotangentComplexIso q g)
  have h67 := h6.comp'.{u + 1, u, u} _ Φ h7
  have h57 := h5.comp'.{u + 1, u, u} _ Φ h67
  have h47 := h4.comp'.{u + 1, u, u} _ Φ h57
  have h37 := h3.comp'.{u + 1, u, u} _ Φ h47
  have h27 := h2.comp'.{u + 1, u, u} _ Φ h37
  have h17 := h1.comp'.{u + 1, u, u} _ Φ h27
  exact h17.congr_base.{u + 1, u, u} _ Φ (columnBaseMap_eq h) _

/-- The first arrow of the right column of Stacks 09DK is
`Lq^*L_{Y/Z} ≅ L_{q⁻¹𝒪_Y/q⁻¹g⁻¹𝒪_Z} ⊗ 𝒪_W` followed by the image in the derived category of the
first arrow of Tag 08SZ and the string `columnChain`. -/
theorem fibreProductColumnUnit_comp_transitivityCounit_eq (h : p ≫ f = q ≫ g) :
    fibreProductColumnUnit h ≫ transitivityCounit p f =
      (derivedPullbackCotangentComplexIso q g).hom ≫
        DerivedCategory.Q.map (Sheaf.towerCotangentBaseChange.{u + 1, u, u}
            (SmallEtale.topology B S hS W.1)
            (RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
              (smallEtaleRingedToposHomULift g) (smallEtaleRingedToposHomULift q))
            (smallEtaleRingedToposHomULift q).fSharpInverseImage ≫ columnChain h) := by
  refine (fibreProductColumnUnit_comp_transitivityCounit h).trans (congrArg (_ ≫ ·) ?_)
  refine Eq.symm ((Functor.map_comp DerivedCategory.Q _ _).trans (congrArg (_ ≫ ·) ?_))
  refine (Functor.map_comp DerivedCategory.Q _ _).trans (congrArg (_ ≫ ·) ?_)
  refine (Functor.map_comp DerivedCategory.Q _ _).trans (congrArg (_ ≫ ·) ?_)
  refine (Functor.map_comp DerivedCategory.Q _ _).trans (congrArg (_ ≫ ·) ?_)
  refine (Functor.map_comp DerivedCategory.Q _ _).trans (congrArg (_ ≫ ·) ?_)
  refine (Functor.map_comp DerivedCategory.Q _ _).trans (congrArg (_ ≫ ·) ?_)
  exact Functor.map_comp DerivedCategory.Q _ _

end AlgebraicGeometry.Space

end
