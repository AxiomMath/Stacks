module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapAffineDegreewise
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapCanonical
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffinePointwiseRingChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapIso

/-!
# Equation 0DKF on affine representables, at a geometric point

For a commutative square of affine objects of the big fppf site and a geometric point `x̄'` of the
corner `U'`, the map of Equation 0DKF attached to `Φ(M)` for a K-flat complex `M` of
`Γ(U)`-modules, `Φ(K₀')` and the morphism induced by `φ₀ : M ⊗ᴸ Γ(U') ⟶ K₀'` is identified with
the ring-level map of Stacks 0DJ7 for the square of geometric stalks, through the stalk
isomorphisms of `Φ` and the unit relating the two stalk paths.

## Main results

* `Space.representedAffineChase_heq_smul`: the two sides of the chase differ by the unit of
  `Space.exists_isUnit_representedAffineStalkPath`.
* `Space.isIso_geometricStalkBaseChangeCohomologyMap_representedAffine_iff_of_kFlat`: the map of
  Equation 0DKF at `x̄'` is invertible exactly when the ring-level map of Stacks 0DJ7 for the
  square of geometric stalks is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

namespace Stacks.Generic

/-- Assembling two chases into an equality up to a scalar. -/
theorem chase_heq_smul {k C D : Type*} [CommRing k] {_ : Category C} {_ : Preadditive C}
    {_ : Linear k C} {_ : Category D} {_ : Preadditive D} {_ : Linear k D} {Q : C ⥤ D}
    [Q.Additive] [Q.Linear k]
    {X₀ X₁ X₂ X₃ Z₁ Z₂ X₀' Z₁' : D} {V₁ V₂ W₁ W₂ : C}
    {L : X₀ ⟶ X₃} {a : X₀ ⟶ X₁} {m : X₁ ⟶ X₂} {t : X₂ ⟶ X₃} {d : X₁ ⟶ Z₁} {b : Z₁ ⟶ Z₂}
    {e : Z₂ ⟶ X₂} {y : X₀ ⟶ Z₁} {pL pR : V₁ ⟶ V₂}
    {R : X₀' ⟶ Q.obj W₂} {y' : X₀' ⟶ Z₁'} {b' : Z₁' ⟶ Q.obj W₁} {cR : W₁ ⟶ W₂} {c : k}
    (hL : L = a ≫ m ≫ t) (hD : m = d ≫ b ≫ e) (hH : a ≫ d = y) (hT : HEq (e ≫ t) (Q.map pL))
    (hR : R = y' ≫ b' ≫ Q.map cR) (hs : pL = c • pR)
    (hy : HEq y y') (hb : HEq b b') (hc : HEq cR pR)
    (hX₀ : X₀ = X₀') (hZ₁ : Z₁ = Z₁') (hZ₂ : Z₂ = Q.obj V₁) (hX₃ : X₃ = Q.obj V₂)
    (hW₁ : W₁ = V₁) (hW₂ : W₂ = V₂) :
    HEq L (c • R) := by
  subst hL hD hR hW₁ hW₂ hZ₂ hX₃ hZ₁ hX₀
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hy
  obtain rfl := eq_of_heq hb
  have hT' := eq_of_heq hT
  subst hs
  refine heq_of_eq ?_
  rw [Category.assoc, Category.assoc, hT', ← Category.assoc, hH, Q.map_smul, Linear.comp_smul,
    Linear.comp_smul]

/-- Cancelling an isomorphism from an equality of two chases up to a scalar, after moving a
morphism through a naturality square. -/
theorem cancel_heq_smul {k C₀ D : Type*} [CommRing k] {_ : Category C₀} {_ : Category D}
    {_ : Preadditive D} {_ : Linear k D} (G : C₀ ⥤ D)
    {A A' Y₁ Y₁' Z Z' W R₁ R₂ R₃ R₄ R₅ : D} {P₀ P₁ P₂ : C₀}
    {d : A ⟶ G.obj P₀} {β : P₀ ⟶ P₁} {φ : P₁ ⟶ P₂} {eY : G.obj P₂ ⟶ Z} {q : Z ⟶ W}
    {eY' : G.obj P₂ ⟶ Z'} {eX : G.obj P₁ ⟶ Y₁} {Df : Y₁ ⟶ Z'} {eX₂ : G.obj P₁ ⟶ Y₁'}
    {r₁ : A' ⟶ R₁} {r₂ : R₁ ⟶ R₂} {r₃ : R₂ ⟶ R₃} {r₄ : R₃ ⟶ R₄} {t₁ : R₄ ⟶ R₅} {t₂ : R₅ ⟶ W}
    {c : k}
    (hA : HEq (d ≫ G.map (β ≫ φ) ≫ eY ≫ q) (c • (r₁ ≫ r₂ ≫ r₃ ≫ r₄ ≫ t₁ ≫ t₂)))
    (nat : G.map φ ≫ eY' = eX ≫ Df) (h : HEq eY eY') (hX : HEq eX eX₂) (ht₁ : HEq Df t₁)
    (ht₂ : HEq q t₂) (hT : IsIso (t₁ ≫ t₂))
    (hA' : A = A') (hY₁ : Y₁ = R₄) (hY₁' : Y₁' = R₄) (hZ : Z = R₅) (hZ' : Z' = R₅) :
    HEq (d ≫ G.map β ≫ eX₂) (c • (r₁ ≫ r₂ ≫ r₃ ≫ r₄)) := by
  subst hA' hY₁ hZ' hZ hY₁'
  obtain rfl := eq_of_heq h
  obtain rfl := eq_of_heq hX
  obtain rfl := eq_of_heq ht₁
  obtain rfl := eq_of_heq ht₂
  have h₁ := eq_of_heq hA
  rw [G.map_comp, Category.assoc, reassoc_of% nat] at h₁
  refine heq_of_eq ((cancel_mono (Df ≫ q)).1 ?_)
  rw [Category.assoc, Category.assoc, h₁, Linear.smul_comp]
  simp only [Category.assoc]

/-- The compatibility of a chase up to a scalar with an isomorphism rescaled by its inverse. -/
theorem comp_trans_hom_eq_of_smul {k C₀ D : Type*} [CommRing k] {_ : Category C₀}
    {_ : Category D} {_ : Preadditive D} {_ : Linear k D} (G : C₀ ⥤ D)
    {A Y₁ Y₂ Y₃ Y₄ Z₁ : D} {P₀ P₁ P₂ : C₀}
    {d : A ⟶ G.obj P₀} {β : P₀ ⟶ P₁} {Φφ : P₁ ⟶ P₂} {eX : G.obj P₁ ⟶ Y₄}
    {eY : G.obj P₂ ⟶ Z₁} {eYI : G.obj P₂ ≅ Z₁} {Dφ : Y₄ ⟶ Z₁} {ι : Z₁ ≅ Z₁}
    {r₁ : A ⟶ Y₁} {r₂ : Y₁ ⟶ Y₂} {r₃ : Y₂ ⟶ Y₃} {r₄ : Y₃ ⟶ Y₄} {c c' : k}
    (hB : d ≫ G.map β ≫ eX = c • (r₁ ≫ r₂ ≫ r₃ ≫ r₄)) (nat : G.map Φφ ≫ eY = eX ≫ Dφ)
    (heY : eYI.hom = eY) (hι : ι.hom = c' • 𝟙 Z₁) (hcc : c' * c = 1) :
    (d ≫ G.map (β ≫ Φφ)) ≫ (eYI ≪≫ ι).hom = r₁ ≫ r₂ ≫ r₃ ≫ r₄ ≫ Dφ := by
  rw [Iso.trans_hom, heY, hι, G.map_comp, Category.assoc, Category.assoc, reassoc_of% nat,
    reassoc_of% hB]
  simp only [Linear.comp_smul, Category.comp_id, Linear.smul_comp, smul_smul, hcc, one_smul,
    Category.assoc]


end Stacks.Generic

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Chase

variable {P U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj P)]
  (g₀ : P ⟶ U) (x : GeometricPoint B S hS (yoneda.obj P))

/-- **The two sides of the chase of Equation 0DKF differ by the unit of the stalk paths.** On a
complex `M`, the derived pullback-stalk comparison at `Φ_U(M)` followed by the stalk of the affine
base change morphism, read through derived extension of scalars, is `c` times the composite
through the stalk ring maps, for `c` the unit relating the two stalk paths. -/
theorem representedAffineChase_heq_smul
    (c : geometricStalkRing B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x)
    (hc : ∀ M, (representedAffineStalkPathLeft B S hS g₀ x).hom.app M =
        c • (representedAffineStalkPathRight B S hS g₀ x).hom.app M)
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    HEq ((derivedPullbackGeometricStalkMap (representedSpaceMap B S hS g₀) x).app
        ((representedAffineDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj M)) ≫
      (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
        ((representedAffineDerivedBaseChangeIso B S hS g₀).hom.app (DerivedCategory.Q.obj M) ≫
          (representedAffineDerivedAssociated B S hS P).map
            ((representedAffineDerivedExtension B S hS g₀).comparison.app M)) ≫
      (representedAffineDerivedStalkIso B S hS P x).hom.app (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u, u, u}
              (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (representedAffineGlobalStalkRingHom B S hS P x)).comparison.app
          (((ModuleCat.extendScalars.{u, u, u}
              (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M))
    (c • ((geometricStalkDerivedExtension (representedSpaceMap B S hS g₀) x).functor.map
        ((representedAffineDerivedStalkIso B S hS U
          (geometricPointMap (representedSpaceMap B S hS g₀).hom x)).hom.app
            (DerivedCategory.Q.obj M)) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
        (representedAffineGlobalStalkRingHom B S hS U
          (geometricPointMap (representedSpaceMap B S hS g₀).hom x))
        (stalkStructureMap B S hS (representedSpaceMap B S hS g₀) x).hom).hom.app
          (DerivedCategory.Q.obj M) ≫
      eqToHom (congrArg (fun φ =>
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          φ).functor.obj (DerivedCategory.Q.obj M))
        (representedAffineStalkRingHom_square B S hS g₀ x)) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
        (representedAffineCommRingCatHom B S hS g₀).hom
        (representedAffineGlobalStalkRingHom B S hS P x)).inv.app
          (DerivedCategory.Q.obj M) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (representedAffineGlobalStalkRingHom B S hS P x)).functor.map
          ((representedAffineDerivedExtension B S hS g₀).comparison.app M) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (representedAffineGlobalStalkRingHom B S hS P x)).comparison.app
          (((ModuleCat.extendScalars.{u, u, u}
              (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M))) :=
  Stacks.Generic.chase_heq_smul (Q := DerivedCategory.Q) (chaseL₁ B S hS g₀ x M)
    (derivedPullbackGeometricStalkComplexMap_app (representedSpaceMap B S hS g₀) x
      (((representedAffineAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))
    (chaseHead B S hS g₀ x M) (chaseTail_heq_map_representedAffineStalkPathLeft B S hS g₀ x M)
    (chaseR B S hS g₀ x M)
    (representedAffineStalkPath_mapHomologicalComplex_eq_smul B S hS g₀ x c hc M)
    (by exact HEq.rfl) (by heq_congr) (representedAffineChaseRight_heq B S hS g₀ x M)
    (by exact rfl) (by exact rfl) (by exact rfl) (by exact rfl) (by exact rfl) (by exact rfl)

/-- **The derived pullback-stalk comparison of affine representables at a K-flat complex.**
After the stalk isomorphisms of `Φ_U` and `Φ_P`, the derived pullback-stalk comparison at
`Φ_U(M)` followed by the stalk of the affine base change isomorphism is `c` times the composite of
the composition isomorphisms of derived extension of scalars around the square of stalk rings. -/
theorem representedAffineDerivedStalk_heq_smul
    (c : geometricStalkRing B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x)
    (hc : ∀ M, (representedAffineStalkPathLeft B S hS g₀ x).hom.app M =
        c • (representedAffineStalkPathRight B S hS g₀ x).hom.app M)
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ)
    (hM : CochainComplex.KFlat.{u, u} M) :
    HEq ((derivedPullbackGeometricStalkMap (representedSpaceMap B S hS g₀) x).app
        ((representedAffineDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj M)) ≫
      (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
        ((representedAffineDerivedBaseChangeIso B S hS g₀).hom.app (DerivedCategory.Q.obj M)) ≫
      (representedAffineDerivedStalkIso B S hS P x).hom.app
        ((representedAffineDerivedExtension B S hS g₀).functor.obj (DerivedCategory.Q.obj M)))
    (c • ((geometricStalkDerivedExtension (representedSpaceMap B S hS g₀) x).functor.map
        ((representedAffineDerivedStalkIso B S hS U
          (geometricPointMap (representedSpaceMap B S hS g₀).hom x)).hom.app
            (DerivedCategory.Q.obj M)) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
        (representedAffineGlobalStalkRingHom B S hS U
          (geometricPointMap (representedSpaceMap B S hS g₀).hom x))
        (stalkStructureMap B S hS (representedSpaceMap B S hS g₀) x).hom).hom.app
          (DerivedCategory.Q.obj M) ≫
      eqToHom (congrArg (fun φ =>
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          φ).functor.obj (DerivedCategory.Q.obj M))
        (representedAffineStalkRingHom_square B S hS g₀ x)) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
        (representedAffineCommRingCatHom B S hS g₀).hom
        (representedAffineGlobalStalkRingHom B S hS P x)).inv.app
          (DerivedCategory.Q.obj M))) := by
  have h₁ := isIso_totalDerivedExtensionScalars_comparison_of_flat _
    (flat_representedAffineStalkRingHom B S hS P x)
  have h₂ := (representedAffineDerivedExtension B S hS g₀).comparison_isIso_of_kFlat M hM
  exact Stacks.Generic.cancel_heq_smul
    (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x)
    (representedAffineChase_heq_smul B S hS g₀ x c hc M)
    (representedAffineDerivedStalkIso_naturality B S hS x
      ((representedAffineDerivedExtension B S hS g₀).comparison.app M))
    (by heq_congr) (by heq_congr) (by exact HEq.rfl) (by exact HEq.rfl)
    (@IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _) (NatIso.isIso_app_of_isIso _ _))
    (by exact rfl) (by exact rfl) (by exact rfl) (by exact rfl) (by exact rfl)


end Chase

open RingTheory.TorIndependence in
/-- **The map of Equation 0DKF on affine representables, at a K-flat complex.** For a commutative
square of affine objects, a K-flat complex `M` of `Γ(U)`-modules, `K₀'` over `Γ(U')` and
`φ₀ : M ⊗ᴸ Γ(U') ⟶ K₀'`, the map of Equation 0DKF at `x̄'` for `Φ(M)`, `Φ(K₀')` and the induced
morphism is invertible exactly when the ring-level map of Stacks 0DJ7 of the square of geometric
stalks at `M ⊗ᴸ 𝒪_{U,x̄}`, `K₀' ⊗ᴸ 𝒪_{U',x̄'}` is. -/
theorem isIso_geometricStalkBaseChangeCohomologyMap_representedAffine_iff_of_kFlat
    {U V V' U' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
    (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U) (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀)
    (x : GeometricPoint B S hS (yoneda.obj U'))
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ)
    (hM : CochainComplex.KFlat.{u, u} M)
    (K₀' : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)))
    (φ₀ : (representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj M) ⟶
      K₀')
    (n : ℤ) :
    let R := geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS f₀).hom
      (geometricPointMap (representedSpaceMap B S hS g₀').hom x))
    let A := geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS g₀').hom x)
    let R' := geometricStalkRing B S hS (geometricPointMap (representedSpaceMap B S hS f₀').hom x)
    let A' :=
      geometricStalkRing B S hS (X := ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) x
    let a := (stalkStructureMap B S hS (representedSpaceMap B S hS f₀)
      (geometricPointMap (representedSpaceMap B S hS g₀').hom x)).hom
    let b := (geometricBaseStalkMap B S hS (representedSpaceMap B S hS f₀)
      (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
      (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀) x).hom
    let c := (stalkStructureMap B S hS (representedSpaceMap B S hS g₀') x).hom
    let e := (stalkStructureMap B S hS (representedSpaceMap B S hS f₀') x).hom
    letI : Algebra R A := a.toAlgebra
    letI : Algebra R R' := b.toAlgebra
    letI : Algebra R A' := (c.comp a).toAlgebra
    letI : Algebra A A' := c.toAlgebra
    letI : Algebra R' A' := e.toAlgebra
    letI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower R R' A' := IsScalarTower.of_algebraMap_eq'
      (stalkStructureMap_square B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀) x)
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) :=
      (representedAffineCommRingCatHom B S hS g₀').hom.toAlgebra
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) A :=
      (representedAffineGlobalStalkRingHom B S hS U
        (geometricPointMap (representedSpaceMap B S hS g₀').hom x)).toAlgebra
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) A' :=
      (representedAffineGlobalStalkRingHom B S hS U' x).toAlgebra
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) A' :=
      ((representedAffineGlobalStalkRingHom B S hS U' x).comp
        (representedAffineCommRingCatHom B S hS g₀').hom).toAlgebra
    letI : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) A A' :=
      IsScalarTower.of_algebraMap_eq' (representedAffineStalkRingHom_square B S hS g₀' x).symm
    letI : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) A' := IsScalarTower.of_algebraMap_eq' rfl
    IsIso (canonicalGeometricStalkBaseChangeCohomologyMap B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀')
        (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀) x
        ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj M))
        ((representedAffineToposDerivedAssociated B S hS U').obj K₀')
        ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
            (DerivedCategory.Q.obj M) ≫
          (representedAffineToposDerivedAssociated B S hS U').map φ₀) n) ↔
      IsIso (ringBaseChangeCohomologyMap (R := R) (A := A) (R' := R') (A' := A')
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) A)).functor.obj
            (DerivedCategory.Q.obj M))
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) A')).functor.obj K₀')
        (extendScalarsBaseChangeHom (A := Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
          (A' := Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) (A₁ := A) (A₁' := A')
          (DerivedCategory.Q.obj M) K₀' φ₀) n) := by
  intro R A R' A' a b c e
  let : Algebra R A := a.toAlgebra
  let : Algebra R R' := b.toAlgebra
  let : Algebra R A' := (c.comp a).toAlgebra
  let : Algebra A A' := c.toAlgebra
  let : Algebra R' A' := e.toAlgebra
  let : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R R' A' := IsScalarTower.of_algebraMap_eq'
    (stalkStructureMap_square B S hS (representedSpaceMap B S hS f₀)
      (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
      (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀) x)
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) :=
    (representedAffineCommRingCatHom B S hS g₀').hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) A :=
    (representedAffineGlobalStalkRingHom B S hS U
      (geometricPointMap (representedSpaceMap B S hS g₀').hom x)).toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) A' :=
    (representedAffineGlobalStalkRingHom B S hS U' x).toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) A' :=
    ((representedAffineGlobalStalkRingHom B S hS U' x).comp
      (representedAffineCommRingCatHom B S hS g₀').hom).toAlgebra
  let : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) A A' :=
    IsScalarTower.of_algebraMap_eq' (representedAffineStalkRingHom_square B S hS g₀' x).symm
  let : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) A' := IsScalarTower.of_algebraMap_eq' rfl
  refine (exists_isUnit_representedAffineStalkPath B S hS g₀' x).elim fun u hu => ?_
  have hB := eq_of_heq (representedAffineDerivedStalk_heq_smul B S hS g₀' x u hu.2 M hM)
  exact isIso_ringBaseChangeCohomologyMap_iff_of_iso (R := R) (A := A) (R' := R') (A' := A')
    ((representedAffineDerivedStalkIso B S hS U
        (geometricPointMap (representedSpaceMap B S hS g₀').hom x)).app
      (DerivedCategory.Q.obj M))
    ((representedAffineDerivedStalkIso B S hS U' x).app K₀' ≪≫
      (unitCentralIso u hu.1).symm.app _) _ _
    (Eq.symm <| eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq
      (Stacks.Generic.comp_trans_hom_eq_of_smul
        (geometricDerivedStalk B S hS (X := ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) x)
        (eYI := (representedAffineDerivedStalkIso B S hS U' x).app K₀')
        (ι := (unitCentralIso u hu.1).symm.app _) hB
        (representedAffineDerivedStalkIso_naturality B S hS x φ₀) (by exact rfl) (by exact rfl)
        hu.1.val_inv_mul)) (by heq_congr)))) n


end AlgebraicGeometry.Space

end
