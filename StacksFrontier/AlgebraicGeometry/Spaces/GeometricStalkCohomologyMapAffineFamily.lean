module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapAffinePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapIso
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapSecondSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineBaseChangeCompCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkAffineFlatness
public import StacksFrontier.Homology.KFlat.Resolution

/-!
# Conditions (1) and (2) of Stacks 0DKG on a cartesian square of affine schemes

For a cartesian square of affine objects of the big fppf site, `K ∈ D_QCoh(𝒪_U)`,
`K' ∈ D_QCoh(𝒪_{U'})` and `φ : L(g')^*K ⟶ K'`, the map of Equation 0DKF is invertible at every
geometric point of `U'` in every degree if and only if the composite
`RΓ(U, K) ⊗ᴸ_{𝒪(V)} 𝒪(V') ⟶ RΓ(U', K')` of Stacks 065Z with the map induced by `φ` is an
isomorphism. The proof reads the map of Equation 0DKF as the ring-level map of Stacks 0DJ7 of the
square of geometric stalks and applies Stacks 0DJ8 to the covering family of these squares.
-/

/- Instances that come into scope here only through the base versions of imported modules,
and that would change the elaboration below (universe joins, the small model of `D(R)`). -/
attribute [-instance] SheafOfModules.hasBinBiprod

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

namespace Stacks.Generic

/-- The input of Equation 0DKF built from an affine base change isomorphism, against an
isomorphism of the source and the counits. -/
theorem map_comp_eq_of_spec {C₀ C₁ D₁ D₂ : Type*} [Category* C₀] [Category* C₁] [Category* D₁]
    [Category* D₂] {L : D₁ ⥤ D₂} {Φ : C₀ ⥤ D₁} {Φ' : C₁ ⥤ D₂} {Dρ : C₀ ⥤ C₁}
    (β : Φ ⋙ L ⟶ Dρ ⋙ Φ') {X Y : C₀} (ι : X ⟶ Y) {K : D₁} {K' : D₂} (ε : Φ.obj Y ⟶ K)
    {Z : C₁} (φs : Dρ.obj Y ⟶ Z) (ε' : Φ'.obj Z ⟶ K') (φ : L.obj K ⟶ K')
    (spec : L.map ε ≫ φ = β.app Y ≫ Φ'.map φs ≫ ε') :
    L.map (Φ.map ι ≫ ε) ≫ φ = (β.app X ≫ Φ'.map (Dρ.map ι ≫ φs)) ≫ ε' := by
  have hn := β.naturality ι
  simp only [Functor.comp_map] at hn
  rw [L.map_comp, Category.assoc, spec, reassoc_of% hn, Φ'.map_comp]
  simp only [Category.assoc]

/-- Invertibility of a component of a natural transformation followed by the image of a morphism
is invariant under an isomorphism of the source. -/
theorem isIso_app_comp_map_comp_iff {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F : C ⥤ E} {G : C ⥤ D} {H : D ⥤ E} (τ : F ⟶ G ⋙ H) {X Y : C} (ι : X ≅ Y) {Z : D}
    (φ : G.obj Y ⟶ Z) :
    IsIso (τ.app X ≫ H.map (G.map ι.hom ≫ φ)) ↔ IsIso (τ.app Y ≫ H.map φ) := by
  have hn := τ.naturality ι.hom
  simp only [Functor.comp_map] at hn
  rw [H.map_comp, ← reassoc_of% hn]
  exact isIso_comp_left_iff _ _


end Stacks.Generic

namespace RingTheory.TorIndependence

/-- For a cocartesian square of rings, `A ⊗_R R' ⟶ A'` is bijective. -/
theorem bijective_baseChangeTensorRingMap_of_isPushout {R A R' A' : Type u} [CommRing R]
    [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R A']
    [Algebra A A'] [Algebra R' A'] [IsScalarTower R A A'] [IsScalarTower R R' A']
    [Algebra.IsPushout R A R' A'] :
    Function.Bijective (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')) := by
  have h : ∀ z, baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A') z =
      Algebra.IsPushout.equiv R A R' A' z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a r =>
      rw [baseChangeTensorRingMap_tmul, Algebra.IsPushout.equiv_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hf : (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A') : _ → _) =
      Algebra.IsPushout.equiv R A R' A' := funext h
  rw [hf]
  exact (Algebra.IsPushout.equiv R A R' A').bijective

end RingTheory.TorIndependence

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The geometric stalk ring map of an affine representable, transported along an equality of
geometric points. -/
theorem representedAffineStalkRingHom_eqToHom {U : BigFppfOver B S hS}
    {p q : GeometricPoint B S hS (yoneda.obj U)}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] (h : p = q)
    (a : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (eqToHom (congrArg (fun z => geometricStalkRing B S hS
        (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) z) h)).hom
        (representedAffineGlobalStalkRingHom B S hS U p a) =
      representedAffineGlobalStalkRingHom B S hS U q a := by
  subst h
  rfl

/-- **Stacks 08HV for affine representables, global against stalk**, at a geometric point
equal to the image of `ȳ'`. -/
theorem flat_baseChangeTensorRingMap_representedAffineStalk_of_eq {V V' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V')] (g : V' ⟶ V)
    (y : GeometricPoint B S hS (yoneda.obj V')) (p : GeometricPoint B S hS (yoneda.obj V))
    (hp : p = geometricPointMap (representedSpaceMap B S hS g).hom y) :
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        (geometricStalkRing B S hS (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩) p) :=
      (representedAffineGlobalStalkRingHom B S hS V p).toAlgebra
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj V', ⊤) :=
      (representedAffineCommRingCatHom B S hS g).hom.toAlgebra
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
        (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) :=
      (representedAffineGlobalStalkRingHom B S hS V' y).toAlgebra
    letI : Algebra
        (geometricStalkRing B S hS (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩) p)
        (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) :=
      (eqToHom (congrArg (fun z => geometricStalkRing B S hS
        (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩) z) hp) ≫
        stalkStructureMap B S hS (representedSpaceMap B S hS g) y).hom.toAlgebra
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) :=
      ((representedAffineGlobalStalkRingHom B S hS V' y).comp
        (representedAffineCommRingCatHom B S hS g).hom).toAlgebra
    letI : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
        (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        (geometricStalkRing B S hS (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩) p)
        (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => by
        change _ = (stalkStructureMap B S hS (representedSpaceMap B S hS g) y).hom
          ((eqToHom (congrArg (fun z => geometricStalkRing B S hS
            (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩) z) hp)).hom
              (representedAffineGlobalStalkRingHom B S hS V p a))
        rw [representedAffineStalkRingHom_eqToHom B S hS hp a,
          stalkStructureMap_representedAffineStalkRingHom B S hS g y a]
        rfl)
    RingHom.Flat (RingTheory.TorIndependence.baseChangeTensorRingMap
      (R := Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
      (A := geometricStalkRing B S hS (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩) p)
      (R' := Γ((BigFppfOver.toScheme B S hS).obj V', ⊤))
      (A' := geometricStalkRing B S hS
        (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y)) := by
  subst hp
  exact flat_baseChangeTensorRingMap_representedAffineStalk B S hS g y

/-- The base stalk map of the square of affine representables against the geometric stalk ring
maps. -/
theorem geometricBaseStalkMap_representedAffineStalkRingHom {U V V' U' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
    (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U) (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀)
    (x : GeometricPoint B S hS (yoneda.obj U')) (a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    (geometricBaseStalkMap B S hS (representedSpaceMap B S hS f₀) (representedSpaceMap B S hS g₀)
        (representedSpaceMap B S hS f₀') (representedSpaceMap B S hS g₀')
        (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀) x).hom
        (representedAffineGlobalStalkRingHom B S hS V
          (geometricPointMap (representedSpaceMap B S hS f₀).hom
            (geometricPointMap (representedSpaceMap B S hS g₀').hom x)) a) =
      representedAffineGlobalStalkRingHom B S hS V'
          (geometricPointMap (representedSpaceMap B S hS f₀').hom x)
        ((representedAffineCommRingCatHom B S hS g₀).hom a) := by
  show (stalkStructureMap B S hS (representedSpaceMap B S hS g₀)
    (geometricPointMap (representedSpaceMap B S hS f₀').hom x)).hom
      ((eqToHom (congrArg (fun z => geometricStalkRing B S hS
        (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩) z)
        (geometricPointMap_square B S hS (representedSpaceMap B S hS f₀)
          (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
          (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
          x))).hom (representedAffineGlobalStalkRingHom B S hS V _ a)) = _
  rw [representedAffineStalkRingHom_eqToHom B S hS (geometricPointMap_square B S hS
      (representedSpaceMap B S hS f₀) (representedSpaceMap B S hS g₀)
      (representedSpaceMap B S hS f₀') (representedSpaceMap B S hS g₀')
      (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀) x) a,
    stalkStructureMap_representedAffineStalkRingHom B S hS g₀ _ a]

open RingTheory.TorIndependence in
/-- **Conditions (1) and (2) of Stacks 0DKG on a cartesian square of affine schemes.** For
`K ∈ D_QCoh(𝒪_U)`, `K' ∈ D_QCoh(𝒪_{U'})` and any `φ : L(g')^*K ⟶ K'`, the map of Equation 0DKF
is invertible at every geometric point of `U'` in every degree if and only if the composite
`RΓ(U, K) ⊗ᴸ_{𝒪(V)} 𝒪(V') ⟶ RΓ(U', K')` of Stacks 065Z with the map induced by `φ` is an
isomorphism. -/
theorem forall_isIso_geometricStalkBaseChangeCohomologyMap_iff_isIso_representedAffineSectionsBaseChangeComp
    {U V V' U' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
    (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U) (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀)
    (hpb : IsPullback g₀' f₀' f₀ g₀)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)))
    (hK : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)))
    (hK' : QcohDerived B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ K')
    (φ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj K ⟶ K') :
    (∀ (x₁' : GeometricPoint B S hS (yoneda.obj U')) (n : ℤ),
        IsIso (canonicalGeometricStalkBaseChangeCohomologyMap B S hS (representedSpaceMap B S hS f₀)
          (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
          (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
          x₁' K K' φ n)) ↔
      IsIso (representedAffineSectionsBaseChangeComp B S hS f₀ g₀ f₀' g₀' w₀ K K' φ) := by
  refine (CochainComplex.KFlat.exists_kFlat_representative.{u, u}
    ((representedAffineDerivedSections B S hS U).obj K)).elim fun M hM => ?_
  refine hM.2.elim fun ι => ?_
  have hε := isIso_representedAffineDerivedAdjunction_counit_app B S hS U K hK
  have hε' := isIso_representedAffineDerivedAdjunction_counit_app B S hS U' K' hK'
  have step₁ := fun (x : GeometricPoint B S hS (yoneda.obj U')) (n : ℤ) =>
    (isIso_geometricStalkBaseChangeCohomologyMap_iff_of_iso B S hS (representedSpaceMap B S hS f₀)
      (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
      (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀) x
      ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app (DerivedCategory.Q.obj M) ≫
        (representedAffineToposDerivedAssociated B S hS U').map
          ((representedAffineDerivedExtension B S hS g₀').functor.map ι.hom ≫
            representedAffineSectionsBaseChangeMap B S hS g₀' K K' φ)) φ
      ((representedAffineToposDerivedAssociated B S hS U).mapIso ι ≪≫
        @asIso _ _ _ _ ((representedAffineDerivedAdjunction B S hS U).counit.app K) hε)
      (@asIso _ _ _ _ ((representedAffineDerivedAdjunction B S hS U').counit.app K') hε')
      (Stacks.Generic.map_comp_eq_of_spec
        (representedAffineToposDerivedBaseChangeIso B S hS g₀').hom
        ι.hom ((representedAffineDerivedAdjunction B S hS U).counit.app K)
        (representedAffineSectionsBaseChangeMap B S hS g₀' K K' φ)
        ((representedAffineDerivedAdjunction B S hS U').counit.app K') φ
        (representedAffineSectionsBaseChangeMap_spec B S hS g₀' K K' φ)) n).symm
  refine (forall_congr' fun x => forall_congr' fun n => (step₁ x n).trans
    (isIso_geometricStalkBaseChangeCohomologyMap_representedAffine_iff_of_kFlat B S hS f₀ g₀ f₀' g₀'
      w₀ x M hM.1 _ _ n)).trans ?_
  refine forall_swap.trans ?_
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
    (representedAffineCommRingCatHom B S hS f₀).hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj V', ⊤) :=
    (representedAffineCommRingCatHom B S hS g₀).hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) :=
    (representedAffineCommRingCatHom B S hS g₀').hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) :=
    (representedAffineCommRingCatHom B S hS f₀').hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) :=
    ((representedAffineCommRingCatHom B S hS f₀').hom.comp
      (representedAffineCommRingCatHom B S hS g₀).hom).toAlgebra
  have : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) :=
    IsScalarTower.of_algebraMap_eq'
      ((representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀).trans
        (representedAffineRingHom_comp B S hS f₀' g₀)).symm
  have : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj V', ⊤) Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ x : GeometricPoint B S hS (yoneda.obj U'), Algebra
      (geometricStalkRing B S hS
        (geometricPointMap (representedSpaceMap B S hS f₀).hom
          (geometricPointMap (representedSpaceMap B S hS g₀').hom x)))
      (geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS g₀').hom x)) :=
    fun x =>
      (stalkStructureMap B S hS (representedSpaceMap B S hS f₀)
          (geometricPointMap (representedSpaceMap B S hS g₀').hom x)).hom.toAlgebra
  let : ∀ x : GeometricPoint B S hS (yoneda.obj U'), Algebra
      (geometricStalkRing B S hS
        (geometricPointMap (representedSpaceMap B S hS f₀).hom
          (geometricPointMap (representedSpaceMap B S hS g₀').hom x)))
      (geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS f₀').hom x)) :=
    fun x =>
      (geometricBaseStalkMap B S hS (representedSpaceMap B S hS f₀)
          (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
          (representedSpaceMap B S hS g₀')
          (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀) x).hom.toAlgebra
  let : ∀ x : GeometricPoint B S hS (yoneda.obj U'), Algebra
      (geometricStalkRing B S hS
        (geometricPointMap (representedSpaceMap B S hS f₀).hom
          (geometricPointMap (representedSpaceMap B S hS g₀').hom x)))
      (geometricStalkRing B S hS (X := ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) x) :=
    fun x =>
      ((stalkStructureMap B S hS (representedSpaceMap B S hS g₀') x).hom.comp
          (stalkStructureMap B S hS (representedSpaceMap B S hS f₀)
            (geometricPointMap (representedSpaceMap B S hS g₀').hom x)).hom).toAlgebra
  let : ∀ x : GeometricPoint B S hS (yoneda.obj U'), Algebra
      (geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS g₀').hom x))
      (geometricStalkRing B S hS (X := ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) x) :=
    fun x => (stalkStructureMap B S hS (representedSpaceMap B S hS g₀') x).hom.toAlgebra
  let : ∀ x : GeometricPoint B S hS (yoneda.obj U'), Algebra
      (geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS f₀').hom x))
      (geometricStalkRing B S hS (X := ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) x) :=
    fun x => (stalkStructureMap B S hS (representedSpaceMap B S hS f₀') x).hom.toAlgebra
  have : ∀ x : GeometricPoint B S hS (yoneda.obj U'), IsScalarTower
      (geometricStalkRing B S hS
        (geometricPointMap (representedSpaceMap B S hS f₀).hom
          (geometricPointMap (representedSpaceMap B S hS g₀').hom x)))
      (geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS g₀').hom x))
      (geometricStalkRing B S hS (X := ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) x) :=
    fun x => IsScalarTower.of_algebraMap_eq' rfl
  have : ∀ x : GeometricPoint B S hS (yoneda.obj U'), IsScalarTower
      (geometricStalkRing B S hS
        (geometricPointMap (representedSpaceMap B S hS f₀).hom
          (geometricPointMap (representedSpaceMap B S hS g₀').hom x)))
      (geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS f₀').hom x))
      (geometricStalkRing B S hS (X := ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) x) :=
    fun x =>
      IsScalarTower.of_algebraMap_eq'
        (stalkStructureMap_square B S hS (representedSpaceMap B S hS f₀)
          (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
          (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
          x)
  let : ∀ x : GeometricPoint B S hS (yoneda.obj U'), Algebra
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (geometricStalkRing B S hS
        (geometricPointMap (representedSpaceMap B S hS f₀).hom
          (geometricPointMap (representedSpaceMap B S hS g₀').hom x))) := fun x =>
    (representedAffineGlobalStalkRingHom B S hS V
        (geometricPointMap (representedSpaceMap B S hS f₀).hom
          (geometricPointMap (representedSpaceMap B S hS g₀').hom x))).toAlgebra
  let : ∀ x : GeometricPoint B S hS (yoneda.obj U'), Algebra
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      (geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS g₀').hom x)) :=
    fun x =>
      (representedAffineGlobalStalkRingHom B S hS U
          (geometricPointMap (representedSpaceMap B S hS g₀').hom x)).toAlgebra
  let : ∀ x : GeometricPoint B S hS (yoneda.obj U'), Algebra
      Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
      (geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS f₀').hom x)) :=
    fun x =>
      (representedAffineGlobalStalkRingHom B S hS V'
          (geometricPointMap (representedSpaceMap B S hS f₀').hom x)).toAlgebra
  let : ∀ x : GeometricPoint B S hS (yoneda.obj U'), Algebra
      Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
      (geometricStalkRing B S hS (X := ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) x) :=
    fun x => (representedAffineGlobalStalkRingHom B S hS U' x).toAlgebra
  let : ∀ x : GeometricPoint B S hS (yoneda.obj U'), Algebra
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS g₀').hom x)) :=
    fun x =>
      ((representedAffineGlobalStalkRingHom B S hS U
            (geometricPointMap (representedSpaceMap B S hS g₀').hom x)).comp
          (representedAffineCommRingCatHom B S hS f₀).hom).toAlgebra
  have : ∀ x : GeometricPoint B S hS (yoneda.obj U'), IsScalarTower
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      (geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS g₀').hom x)) :=
    fun x => IsScalarTower.of_algebraMap_eq' rfl
  have : ∀ x : GeometricPoint B S hS (yoneda.obj U'), IsScalarTower
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (geometricStalkRing B S hS
        (geometricPointMap (representedSpaceMap B S hS f₀).hom
          (geometricPointMap (representedSpaceMap B S hS g₀').hom x)))
      (geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS g₀').hom x)) :=
    fun x =>
      IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a =>
        (stalkStructureMap_representedAffineStalkRingHom B S hS f₀
            (geometricPointMap (representedSpaceMap B S hS g₀').hom x) a).symm)
  let : ∀ x : GeometricPoint B S hS (yoneda.obj U'), Algebra
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS f₀').hom x)) :=
    fun x =>
      ((representedAffineGlobalStalkRingHom B S hS V'
            (geometricPointMap (representedSpaceMap B S hS f₀').hom x)).comp
          (representedAffineCommRingCatHom B S hS g₀).hom).toAlgebra
  have : ∀ x : GeometricPoint B S hS (yoneda.obj U'), IsScalarTower
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
      (geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS f₀').hom x)) :=
    fun x => IsScalarTower.of_algebraMap_eq' rfl
  have : ∀ x : GeometricPoint B S hS (yoneda.obj U'), IsScalarTower
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (geometricStalkRing B S hS
        (geometricPointMap (representedSpaceMap B S hS f₀).hom
          (geometricPointMap (representedSpaceMap B S hS g₀').hom x)))
      (geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS f₀').hom x)) :=
    fun x =>
      IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a =>
        (geometricBaseStalkMap_representedAffineStalkRingHom B S hS f₀ g₀ f₀' g₀' w₀ x a).symm)
  let : ∀ x : GeometricPoint B S hS (yoneda.obj U'), Algebra
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      (geometricStalkRing B S hS (X := ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) x) :=
    fun x =>
      ((representedAffineGlobalStalkRingHom B S hS U' x).comp
          (representedAffineCommRingCatHom B S hS g₀').hom).toAlgebra
  have : ∀ x : GeometricPoint B S hS (yoneda.obj U'), IsScalarTower
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
      (geometricStalkRing B S hS (X := ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) x) :=
    fun x => IsScalarTower.of_algebraMap_eq' rfl
  have : ∀ x : GeometricPoint B S hS (yoneda.obj U'), IsScalarTower
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      (geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS g₀').hom x))
      (geometricStalkRing B S hS (X := ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) x) :=
    fun x =>
      IsScalarTower.of_algebraMap_eq'
        (representedAffineStalkRingHom_square B S hS g₀' x).symm
  let : ∀ x : GeometricPoint B S hS (yoneda.obj U'), Algebra
      Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
      (geometricStalkRing B S hS (X := ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) x) :=
    fun x =>
      ((representedAffineGlobalStalkRingHom B S hS U' x).comp
          (representedAffineCommRingCatHom B S hS f₀').hom).toAlgebra
  have : ∀ x : GeometricPoint B S hS (yoneda.obj U'), IsScalarTower
      Γ((BigFppfOver.toScheme B S hS).obj V', ⊤) Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
      (geometricStalkRing B S hS (X := ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) x) :=
    fun x => IsScalarTower.of_algebraMap_eq' rfl
  have : ∀ x : GeometricPoint B S hS (yoneda.obj U'), IsScalarTower
      Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
      (geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS f₀').hom x))
      (geometricStalkRing B S hS (X := ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) x) :=
    fun x =>
      IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a =>
        (stalkStructureMap_representedAffineStalkRingHom B S hS f₀' x a).symm)
  have : ∀ x : GeometricPoint B S hS (yoneda.obj U'), Module.Flat
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (geometricStalkRing B S hS
        (geometricPointMap (representedSpaceMap B S hS f₀).hom
          (geometricPointMap (representedSpaceMap B S hS g₀').hom x))) := fun x =>
    flat_representedAffineStalkRingHom B S hS V
      (geometricPointMap (representedSpaceMap B S hS f₀).hom
        (geometricPointMap (representedSpaceMap B S hS g₀').hom x))
  have : ∀ x : GeometricPoint B S hS (yoneda.obj U'), Module.Flat
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      (geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS g₀').hom x)) :=
    fun x =>
      flat_representedAffineStalkRingHom B S hS U
        (geometricPointMap (representedSpaceMap B S hS g₀').hom x)
  have : ∀ x : GeometricPoint B S hS (yoneda.obj U'), Module.Flat
      Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
      (geometricStalkRing B S hS (X := ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) x) :=
    fun x => flat_representedAffineStalkRingHom B S hS U' x
  have : Algebra.IsPushout Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) :=
    CommRingCat.isPushout_iff_isPushout.1
    (isPushout_representedAffineRingHom B S hS f₀ g₀ f₀' g₀' hpb)
  refine (forall_congr' fun n => (isIso_ringBaseChangeCohomologyMap_iff_forall_secondSquare
    (R := Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (A := Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    (R' := Γ((BigFppfOver.toScheme B S hS).obj V', ⊤))
    (A' := Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))
    (R₁ := fun x : GeometricPoint B S hS (yoneda.obj U') =>
      (geometricStalkRing B S hS
        (geometricPointMap (representedSpaceMap B S hS f₀).hom
          (geometricPointMap (representedSpaceMap B S hS g₀').hom x)) : Type u))
    (A₁ := fun x : GeometricPoint B S hS (yoneda.obj U') =>
      (geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS g₀').hom x) :
        Type u))
    (R₁' := fun x : GeometricPoint B S hS (yoneda.obj U') =>
      (geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS f₀').hom x) :
        Type u))
    (A₁' := fun x : GeometricPoint B S hS (yoneda.obj U') =>
      (geometricStalkRing B S hS (X := ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) x :
        Type u))
    (fun x => flat_baseChangeTensorRingMap_representedAffineStalk_of_eq B S hS g₀
      (geometricPointMap (representedSpaceMap B S hS f₀').hom x)
      (geometricPointMap (representedSpaceMap B S hS f₀).hom
        (geometricPointMap (representedSpaceMap B S hS g₀').hom x))
      (geometricPointMap_square B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀) x))
    (fun q => exists_mem_range_comap_representedAffineStalkRingHom B S hS U' q)
    (DerivedCategory.Q.obj M) _ _ n).symm).trans ?_
  refine (forall_congr' fun n => isIso_ringBaseChangeCohomologyMap_iff
    (bijective_baseChangeTensorRingMap_of_isPushout
      (R := Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
      (A := Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
      (R' := Γ((BigFppfOver.toScheme B S hS).obj V', ⊤))
      (A' := Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)))
    _ _ _ n).trans ?_
  refine (isIso_ringHomSquareComparison_comp_iff_forall_cohomology
    (representedAffineCommRingCatHom B S hS f₀).hom (representedAffineCommRingCatHom B S hS g₀).hom
    (representedAffineCommRingCatHom B S hS g₀').hom
    (representedAffineCommRingCatHom B S hS f₀').hom
    ((representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀).trans
      (representedAffineRingHom_comp B S hS f₀' g₀)) (DerivedCategory.Q.obj M) _ _).symm.trans ?_
  exact Stacks.Generic.isIso_app_comp_map_comp_iff _ ι _


end AlgebraicGeometry.Space

end
