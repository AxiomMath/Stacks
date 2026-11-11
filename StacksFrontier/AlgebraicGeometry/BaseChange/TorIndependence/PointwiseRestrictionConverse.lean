module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.PointwiseRestriction

/-!
# The map of Stacks 0DJ7 along open immersions: the converse

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes, `K ∈ D(𝒪_X)`, `K' ∈ D(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'`, and
let `Y → X₂ → S₂ ← S₂'` be a second cartesian square mapping to the first by open immersions.
The map of Stacks 0DJ7 of the second square at the pulled-back datum is invertible at a point `y`
exactly when the map of the first square is invertible at the image of `y`: the stalks of the
four corners at corresponding points are identified by the open immersions, and every step of the
comparison is an equivalence.

At the level of rings, the one new input is that replacing the corner `A'` of a square of rings by
an isomorphic ring `A'₂`, and `K'` by `K' ⊗ᴸ_{A'} A'₂`, does not change the invertibility of the
map of Stacks 0DJ7, in both directions.

## Main results

* `RingTheory.TorIndependence.isIso_ringBaseChangeCohomologyMap_target_iff`: the corner `A'`
  replaced by an isomorphic ring.
* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_comp_left_iff`: restricting the corner `X'`.
* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_restrict_source_iff`: restricting the corners
  `X`, `S`, `S'`.
* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_pullDatum_iff` and
  `AlgebraicGeometry.isIso_baseChangeCohomologyMap_of_pullDatum`: the composite statement.
* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_of_restrict`: the case of the restriction of
  the square to an open `U` of `X` and its preimage `g'⁻¹(U)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings
open CochainComplex.DerivedExtensionScalars StacksDraft.DerivedExtensionScalarsComp

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R A R' A' A'₂ : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [CommRing A'₂]
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra A' A'₂] [Algebra A A'₂] [Algebra R' A'₂] [Algebra R A'₂]
  [IsScalarTower A A' A'₂] [IsScalarTower R' A' A'₂] [IsScalarTower R A A'₂]
  [IsScalarTower R R' A'₂]

/-- **The map of Stacks 0DJ7 under an isomorphism of the corner `A'`.**  For `A' → A'₂` bijective
and `A'` a localization of `A ⊗_R R'`, the map of Stacks 0DJ7 at `φ : K ⊗ᴸ_A A' ⟶ K'` is
invertible in degree `n` exactly when the map of the square `R → A → A'₂ ← R'` at
`K ⊗ᴸ_A A'₂ ≅ (K ⊗ᴸ_A A') ⊗ᴸ_{A'} A'₂ ⟶ K' ⊗ᴸ_{A'} A'₂` is. -/
theorem isIso_ringBaseChangeCohomologyMap_target_iff
    (hτ : Function.Bijective (algebraMap A' A'₂))
    (hloc : letI := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
      ∃ S : Submonoid (A ⊗[R] R'), IsLocalization S A')
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj K ⟶ K') (n : ℤ) :
    IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n) ↔
      IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') (A' := A'₂) K
        ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A' A'₂)).functor.obj K')
        ((derivedTowerIso A A' A'₂).inv.app K ≫
          (totalDerivedExtensionScalars.{u, u, u} (algebraMap A' A'₂)).functor.map φ) n) := by
  obtain ⟨N, hN, e, Z, v, α, hα⟩ := exists_complexDatum K K' φ
  let T := totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')
  let Tτ := totalDerivedExtensionScalars.{u, u, u} (algebraMap A' A'₂)
  let T₂ := totalDerivedExtensionScalars.{u, u, u} (algebraMap A A'₂)
  let eτ := RingEquiv.ofBijective (algebraMap A' A'₂) hτ
  have : IsIso Tτ.comparison := isIso_comparison_of_ringEquiv eτ
  have : IsIso (alphaH A' A'₂ Z) := inferInstanceAs (IsIso (Tτ.comparison.app Z))
  let Z₂ := ((ModuleCat.extendScalars (algebraMap A' A'₂)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj Z
  let τN := towerComplexMap A A' A'₂ N
  have : IsIso τN := by
    dsimp only [τN, towerComplexMap]
    infer_instance
  let α₂ := inv τN ≫ ((ModuleCat.extendScalars (algebraMap A' A'₂)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map α
  have h1 : IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n) ↔
      IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') (DerivedCategory.Q.obj N)
        (DerivedCategory.Q.obj Z) (alphaH A A' N ≫ DerivedCategory.Q.map α) n) := by
    exact isIso_ringBaseChangeCohomologyMap_iff_of_iso e.symm v φ _
      (map_inv_comp_alphaH_comp_eq φ e v hα) n
  have h2 : IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') (A' := A'₂) K
        (Tτ.functor.obj K') ((derivedTowerIso A A' A'₂).inv.app K ≫ Tτ.functor.map φ) n) ↔
      IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') (A' := A'₂) (DerivedCategory.Q.obj N)
        (DerivedCategory.Q.obj Z₂) (alphaH A A'₂ N ≫ DerivedCategory.Q.map α₂) n) := by
    refine isIso_ringBaseChangeCohomologyMap_iff_of_iso (R := R) (R' := R') (A := A) (A' := A'₂)
      e.symm (Tτ.functor.mapIso v ≪≫ asIso (alphaH A' A'₂ Z))
      ((derivedTowerIso A A' A'₂).inv.app K ≫ Tτ.functor.map φ)
      (alphaH A A'₂ N ≫ DerivedCategory.Q.map α₂) ?_ n
    have hn := (derivedTowerIso A A' A'₂).inv.naturality e.inv
    have ht := derivedTowerIso_hom_app_alphaH A A' A'₂ N
    have hc : Tτ.functor.map (DerivedCategory.Q.map α) ≫ alphaH A' A'₂ Z =
        alphaH A' A'₂ _ ≫ DerivedCategory.Q.map
          (((ModuleCat.extendScalars (algebraMap A' A'₂)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map α) := Tτ.comparison.naturality α
    have hφ' := (map_inv_comp_alphaH_comp_eq φ e v hα).symm
    have hQ : DerivedCategory.Q.map α₂ = inv (DerivedCategory.Q.map τN) ≫
        DerivedCategory.Q.map (((ModuleCat.extendScalars (algebraMap A' A'₂)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map α) := by
      rw [DerivedCategory.Q.map_comp, CategoryTheory.Functor.map_inv]
    have ht' : (derivedTowerIso A A' A'₂).inv.app (DerivedCategory.Q.obj N) ≫
        Tτ.functor.map (alphaH A A' N) ≫ alphaH A' A'₂ _ =
        alphaH A A'₂ N ≫ inv (DerivedCategory.Q.map τN) := by
      rw [← cancel_mono (DerivedCategory.Q.map τN)]
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [← ht, Iso.inv_hom_id_app_assoc]
    have hm : Tτ.functor.map (φ ≫ v.hom) = Tτ.functor.map (T.functor.map e.inv) ≫
        Tτ.functor.map (alphaH A A' N) ≫ Tτ.functor.map (DerivedCategory.Q.map α) := by
      rw [hφ', Tτ.functor.map_comp, Tτ.functor.map_comp]
    have hn' : T₂.functor.map e.inv ≫ (derivedTowerIso A A' A'₂).inv.app (DerivedCategory.Q.obj N) =
        (derivedTowerIso A A' A'₂).inv.app K ≫ Tτ.functor.map (T.functor.map e.inv) := hn
    calc T₂.functor.map e.symm.hom ≫ alphaH A A'₂ N ≫ DerivedCategory.Q.map α₂
        = T₂.functor.map e.inv ≫ (alphaH A A'₂ N ≫ inv (DerivedCategory.Q.map τN)) ≫
            DerivedCategory.Q.map
              (((ModuleCat.extendScalars (algebraMap A' A'₂)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map α) := by
          rw [hQ]; simp only [Iso.symm_hom, Category.assoc]
      _ = (T₂.functor.map e.inv ≫ (derivedTowerIso A A' A'₂).inv.app (DerivedCategory.Q.obj N)) ≫
            Tτ.functor.map (alphaH A A' N) ≫ alphaH A' A'₂ _ ≫
            DerivedCategory.Q.map
              (((ModuleCat.extendScalars (algebraMap A' A'₂)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map α) := by
          rw [← ht']; simp only [Category.assoc]
      _ = ((derivedTowerIso A A' A'₂).inv.app K ≫ Tτ.functor.map (T.functor.map e.inv)) ≫
            Tτ.functor.map (alphaH A A' N) ≫ Tτ.functor.map (DerivedCategory.Q.map α) ≫
            alphaH A' A'₂ Z := by
          rw [hn', hc]
      _ = ((derivedTowerIso A A' A'₂).inv.app K ≫ Tτ.functor.map φ) ≫
            (Tτ.functor.mapIso v ≪≫ asIso (alphaH A' A'₂ Z)).hom := by
          have h3 := congrArg (fun t => (derivedTowerIso A A' A'₂).inv.app K ≫ t ≫
            alphaH A' A'₂ Z) hm
          simp only [CategoryTheory.Functor.map_comp, Category.assoc] at h3
          simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Category.assoc]
          exact h3.symm
  have hloc₂ := exists_isLocalization_of_bijective (R := R) (A := A) (R' := R') (A' := A') hτ hloc
  let : Algebra (MvPolynomial R' R) R' :=
    (MvPolynomial.aeval (R := R) (fun x : R' => x)).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial R' R) R' :=
    IsScalarTower.of_algebraMap_eq fun r =>
      ((MvPolynomial.aeval (R := R) (fun x : R' => x)).commutes r).symm
  have hsurj : Function.Surjective (algebraMap (MvPolynomial R' R) R') := fun x =>
    ⟨MvPolynomial.X x, MvPolynomial.aeval_X _ x⟩
  obtain ⟨F, ε, hF, -, hε, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u}
    ((CochainComplex.singleFunctor (ModuleCat.{u} (MvPolynomial R' R)) 0).obj
      (ModuleCat.of (MvPolynomial R' R) R'))
  have := hε
  let ζ : Z ⟶ ((ModuleCat.restrictScalars (algebraMap A' A'₂)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Z₂ :=
    (Adjunction.mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj (algebraMap A' A'₂)) (ComplexShape.up ℤ)).unit.app Z
  have : IsIso ζ := isIso_extendScalars_unit hτ Z
  have hinv : ∀ i (m : N.X i), ((inv τN).f i).hom ((1 : A'₂) ⊗ₜ[A, algebraMap A A'₂] m) =
      (1 : A'₂) ⊗ₜ[A', algebraMap A' A'₂] (show (ModuleCat.extendScalars (algebraMap A A')).obj
        (N.X i) from (1 : A') ⊗ₜ[A, algebraMap A A'] m) := fun i m =>
    (congrArg (fun x => ((inv τN).f i).hom x) (towerComplexMap_apply A A' A'₂ N i m).symm).trans
      (congrArg (fun g => (g.f i).hom ((1 : A'₂) ⊗ₜ[A', algebraMap A' A'₂]
        (show (ModuleCat.extendScalars (algebraMap A A')).obj (N.X i) from
          (1 : A') ⊗ₜ[A, algebraMap A A'] m))) (IsIso.hom_inv_id τN))
  have hαζ : ∀ i (m : N.X i), (α₂.f i).hom ((1 : A'₂) ⊗ₜ[A, algebraMap A A'₂] m) =
      (ζ.f i).hom ((α.f i).hom ((1 : A') ⊗ₜ[A, algebraMap A A'] m)) := fun i m =>
    (congrArg (fun x => ((((ModuleCat.extendScalars (algebraMap A' A'₂)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map α).f i).hom x) (hinv i m)).trans
      (ModuleCat.ExtendScalars.map_tmul _ (α.f i) 1 _)
  have hκ := modelKappa_algebra_eq (R := R) (A := A) (R' := R') (A' := A')
    (R₀ := MvPolynomial R' R) ε A'₂ N Z α Z₂ ζ α₂ hαζ
  have hU : IsLocalizedModule.unitsComap (modelRingMap R A R' A'₂ (MvPolynomial R' R)) =
      IsLocalizedModule.unitsComap (modelRingMap R A R' A' (MvPolynomial R' R)) := by
    ext b
    change IsUnit (modelRingMap R A R' A'₂ (MvPolynomial R' R) b) ↔
      IsUnit (modelRingMap R A R' A' (MvPolynomial R' R) b)
    rw [modelRingMap_apply_of_algebra (R := R) (A := A) (R' := R') (A' := A')
      (R₀ := MvPolynomial R' R) A'₂ b]
    exact MulEquiv.isUnit_map eτ.toMulEquiv
  let μ := modelTargetMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := MvPolynomial R' R) A'₂
    Z Z₂ ζ
  have : IsIso μ := by
    have : ∀ i, IsIso (μ.f i) := fun i => by
      have : IsIso (ζ.f i) := inferInstanceAs (IsIso ((HomologicalComplex.eval _ _ i).map ζ))
      exact (ConcreteCategory.isIso_iff_bijective _).2
        (ConcreteCategory.bijective_of_isIso (ζ.f i))
    exact HomologicalComplex.Hom.isIso_of_components μ
  have hcomp : ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] MvPolynomial R' R)) n).map
      (DerivedCategory.Q.map (modelKappa (R := R) (A := A) (R' := R') (A' := A'₂)
        (R₀ := MvPolynomial R' R) ε N Z₂ α₂))).hom =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] MvPolynomial R' R)) n).map
        (DerivedCategory.Q.map μ)).hom ∘ₗ
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] MvPolynomial R' R)) n).map
        (DerivedCategory.Q.map (modelKappa (R := R) (A := A) (R' := R') (A' := A')
          (R₀ := MvPolynomial R' R) ε N Z α))).hom := by
    rw [hκ, DerivedCategory.Q.map_comp, CategoryTheory.Functor.map_comp, ModuleCat.hom_comp]
  refine h1.trans (Iff.trans ?_ h2.symm)
  refine (isIso_ringBaseChangeCohomologyMap_iff_isLocalizedModule_units ε hF n hloc hsurj
    N Z α).trans (Iff.trans ?_ (isIso_ringBaseChangeCohomologyMap_iff_isLocalizedModule_units ε hF
      n hloc₂ hsurj N Z₂ α₂).symm)
  rw [hU, hcomp]
  exact (IsLocalizedModule.comp_iff_of_bijective_left _ _
    (ConcreteCategory.bijective_of_isIso _)).symm

end RingTheory.TorIndependence

namespace AlgebraicGeometry

open RingTheory.TorIndependence
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.DerivedPullback.Composition

attribute [local instance] HasDerivedCategory.standard

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **Condition (1) of Stacks 0DJ8 along an open immersion into `X'`.**  For an open immersion
`j : Z' ⟶ X'`, the map of Stacks 0DJ7 of the square `Z' → X → S ← S'` at
`L(j ≫ g')^*K ≅ Lj^*L(g')^*K ⟶ Lj^*K'` is invertible at `z'` exactly when that of the original
square is invertible at `j z'`. -/
theorem isIso_baseChangeCohomologyMap_comp_left_iff (hpb : IsPullback g' f' f g)
    {Z' : Scheme.{u}} (j : Z' ⟶ X') [IsOpenImmersion j] (K : DerivedCategory X.Modules)
    (K' : DerivedCategory X'.Modules) (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (z' : Z') (n : ℤ) :
    IsIso (baseChangeCohomologyMap f g f' g' hpb.w K K' φ (j z') n) ↔
      IsIso (baseChangeCohomologyMap f g (j ≫ f') (j ≫ g')
        (by rw [Category.assoc, hpb.w, Category.assoc]) K
        ((derivedPullback j.toLRSHom.toShHom).obj K')
        ((derivedPullbackCompIsoCanonical j.toLRSHom.toShHom g'.toLRSHom.toShHom).inv.app K ≫
          (derivedPullback j.toLRSHom.toShHom).map φ) z' n) := by
  have w₄ : (j ≫ g') ≫ f = (j ≫ f') ≫ g := by rw [Category.assoc, hpb.w, Category.assoc]
  let : Algebra (S.presheaf.stalk (f (g' (j z')))) (X.presheaf.stalk (g' (j z'))) :=
    ((f.stalkMap (g' (j z'))).hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' (j z')))) (S'.presheaf.stalk (f' (j z'))) :=
    (baseStalkMap f g f' g' hpb.w (j z')).toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' (j z')))) (X'.presheaf.stalk (j z')) :=
    (((g'.stalkMap (j z')).hom).comp ((f.stalkMap (g' (j z'))).hom)).toAlgebra
  let : Algebra (X.presheaf.stalk (g' (j z'))) (X'.presheaf.stalk (j z')) :=
    ((g'.stalkMap (j z')).hom).toAlgebra
  let : Algebra (S'.presheaf.stalk (f' (j z'))) (X'.presheaf.stalk (j z')) :=
    ((f'.stalkMap (j z')).hom).toAlgebra
  have : IsScalarTower (S.presheaf.stalk (f (g' (j z')))) (X.presheaf.stalk (g' (j z')))
      (X'.presheaf.stalk (j z')) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (S.presheaf.stalk (f (g' (j z')))) (S'.presheaf.stalk (f' (j z')))
      (X'.presheaf.stalk (j z')) :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' hpb.w (j z'))
  let : Algebra (X'.presheaf.stalk (j z')) (Z'.presheaf.stalk z') := ((j.stalkMap z').hom).toAlgebra
  let : Algebra (X.presheaf.stalk (g' (j z'))) (Z'.presheaf.stalk z') :=
    (((j ≫ g').stalkMap z').hom).toAlgebra
  let : Algebra (S'.presheaf.stalk (f' (j z'))) (Z'.presheaf.stalk z') :=
    (((j ≫ f').stalkMap z').hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' (j z')))) (Z'.presheaf.stalk z') :=
    ((((j ≫ g').stalkMap z').hom).comp ((f.stalkMap (g' (j z'))).hom)).toAlgebra
  have : IsScalarTower (X.presheaf.stalk (g' (j z'))) (X'.presheaf.stalk (j z'))
      (Z'.presheaf.stalk z') :=
    IsScalarTower.of_algebraMap_eq' (Stacks.ModuleSkyscraper.stalkMap_hom_comp j g' z')
  have : IsScalarTower (S'.presheaf.stalk (f' (j z'))) (X'.presheaf.stalk (j z'))
      (Z'.presheaf.stalk z') :=
    IsScalarTower.of_algebraMap_eq' (Stacks.ModuleSkyscraper.stalkMap_hom_comp j f' z')
  have : IsScalarTower (S.presheaf.stalk (f (g' (j z')))) (X.presheaf.stalk (g' (j z')))
      (Z'.presheaf.stalk z') := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (S.presheaf.stalk (f (g' (j z')))) (S'.presheaf.stalk (f' (j z')))
      (Z'.presheaf.stalk z') :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_square f g (j ≫ f') (j ≫ g') w₄ z')
  have hτ : Function.Bijective (algebraMap (X'.presheaf.stalk (j z')) (Z'.presheaf.stalk z')) :=
    ConcreteCategory.bijective_of_isIso (j.stalkMap z')
  refine (isIso_baseChangeCohomologyMap_iff_ring f g f' g' hpb.w K K' φ (j z') n).trans
    ((isIso_ringBaseChangeCohomologyMap_target_iff (R := S.presheaf.stalk (f (g' (j z'))))
      (R' := S'.presheaf.stalk (f' (j z'))) hτ (exists_isLocalization_stalk hpb (j z')) _ _ _
        n).trans (Iff.trans ?_
          (isIso_baseChangeCohomologyMap_iff_ring f g (j ≫ f') (j ≫ g') w₄ K _ _ z' n).symm))
  refine (isIso_ringBaseChangeCohomologyMap_iff_of_iso (R := S.presheaf.stalk (f (g' (j z'))))
    (R' := S'.presheaf.stalk (f' (j z'))) (A := X.presheaf.stalk (g' (j z')))
    (A' := Z'.presheaf.stalk z')
    (Iso.refl _)
    ((derivedPullbackStalkIso j z').app K') _ _ ?_ n).symm
  have hW0 := inv_eq_of_eq_trans _ _ _ (derivedPullbackStalkCompIso_eq j g' z')
  have hN := (derivedPullbackStalkIso j z').hom.naturality φ
  have hW1 := congrArg (fun t => NatTrans.app t K) hW0
  refine chase_left _ _ _ _ _ _ _ _ _ _ _ _ _ (CategoryTheory.Functor.map_id _ _)
    (CategoryTheory.Functor.map_comp _ _ _) (CategoryTheory.Functor.map_comp _ _ _)
    (Iso.inv_hom_id_app _ _) hN (Iso.inv_hom_id_app (derivedPullbackStalkIso j z') _)
    ((derivedPullbackStalkCompIso j g' z').inv.app K) ?_ hW1
  exact Category.assoc _ _ _

variable {X₂ S₂ S₂' Y : Scheme.{u}}

/-- **Condition (1) of Stacks 0DJ8 along open immersions into `X`, `S` and `S'`.**
Let `Y → X₂ → S₂ ← S₂'` be a commutative square mapping to `X → S ← S'` by open immersions
`X₂ ⟶ X`, `S₂ ⟶ S`, `S₂' ⟶ S'`.  The map of Stacks 0DJ7 of the square `Y → X → S ← S'` at `ψ`
is invertible at `y` exactly when that of the second square at the datum
`L(g₂')^*L(i_X)^*K ≅ L(g₂' ≫ i_X)^*K ⟶ E'` is. -/
theorem isIso_baseChangeCohomologyMap_restrict_source_iff (f : X ⟶ S) (g : S' ⟶ S)
    {f₂ : X₂ ⟶ S₂} {g₂ : S₂' ⟶ S₂} {f₂' : Y ⟶ S₂'} {g₂' : Y ⟶ X₂}
    (w₂ : g₂' ≫ f₂ = f₂' ≫ g₂) (iX : X₂ ⟶ X) (iS : S₂ ⟶ S) (iS' : S₂' ⟶ S')
    [IsOpenImmersion iX] [IsOpenImmersion iS] [IsOpenImmersion iS']
    (hf : f₂ ≫ iS = iX ≫ f) (hg : g₂ ≫ iS = iS' ≫ g) (w : (g₂' ≫ iX) ≫ f = (f₂' ≫ iS') ≫ g)
    (K : DerivedCategory X.Modules) (E' : DerivedCategory Y.Modules)
    (ψ : (derivedPullback (g₂' ≫ iX).toLRSHom.toShHom).obj K ⟶ E') (y : Y) (n : ℤ)
    (hloc : IsStalkLocalization f g (f₂' ≫ iS') (g₂' ≫ iX) w y)
    (hloc₂ : IsStalkLocalization f₂ g₂ f₂' g₂' w₂ y) :
    IsIso (baseChangeCohomologyMap f g (f₂' ≫ iS') (g₂' ≫ iX) w K E' ψ y n) ↔
      IsIso (baseChangeCohomologyMap f₂ g₂ f₂' g₂' w₂
        ((derivedPullback iX.toLRSHom.toShHom).obj K) E'
        ((derivedPullbackCompIsoCanonical g₂'.toLRSHom.toShHom iX.toLRSHom.toShHom).hom.app K ≫
          ψ) y n) := by
  have hpt : iS (f₂ (g₂' y)) = f (iX (g₂' y)) := congrArg (fun k : X₂ ⟶ S => k (g₂' y)) hf
  -- the base square
  let : Algebra (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (X.presheaf.stalk ((g₂' ≫ iX) y)) :=
    ((f.stalkMap ((g₂' ≫ iX) y)).hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (S'.presheaf.stalk ((f₂' ≫ iS') y)) :=
    (baseStalkMap f g (f₂' ≫ iS') (g₂' ≫ iX) w y).toAlgebra
  let : Algebra (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (Y.presheaf.stalk y) :=
    ((((g₂' ≫ iX).stalkMap y).hom).comp ((f.stalkMap ((g₂' ≫ iX) y)).hom)).toAlgebra
  let : Algebra (X.presheaf.stalk ((g₂' ≫ iX) y)) (Y.presheaf.stalk y) :=
    (((g₂' ≫ iX).stalkMap y).hom).toAlgebra
  let : Algebra (S'.presheaf.stalk ((f₂' ≫ iS') y)) (Y.presheaf.stalk y) :=
    (((f₂' ≫ iS').stalkMap y).hom).toAlgebra
  have : IsScalarTower (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (X.presheaf.stalk ((g₂' ≫ iX) y))
      (Y.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (S'.presheaf.stalk ((f₂' ≫ iS') y))
      (Y.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_square f g (f₂' ≫ iS') (g₂' ≫ iX) w y)
  -- the restricted square
  let : Algebra (S₂.presheaf.stalk (f₂ (g₂' y))) (X₂.presheaf.stalk (g₂' y)) :=
    ((f₂.stalkMap (g₂' y)).hom).toAlgebra
  let : Algebra (S₂.presheaf.stalk (f₂ (g₂' y))) (S₂'.presheaf.stalk (f₂' y)) :=
    (baseStalkMap f₂ g₂ f₂' g₂' w₂ y).toAlgebra
  let : Algebra (S₂.presheaf.stalk (f₂ (g₂' y))) (Y.presheaf.stalk y) :=
    (((g₂'.stalkMap y).hom).comp ((f₂.stalkMap (g₂' y)).hom)).toAlgebra
  let : Algebra (X₂.presheaf.stalk (g₂' y)) (Y.presheaf.stalk y) :=
    ((g₂'.stalkMap y).hom).toAlgebra
  let : Algebra (S₂'.presheaf.stalk (f₂' y)) (Y.presheaf.stalk y) :=
    ((f₂'.stalkMap y).hom).toAlgebra
  have : IsScalarTower (S₂.presheaf.stalk (f₂ (g₂' y))) (X₂.presheaf.stalk (g₂' y))
      (Y.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (S₂.presheaf.stalk (f₂ (g₂' y))) (S₂'.presheaf.stalk (f₂' y))
      (Y.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' (stalkMap_square f₂ g₂ f₂' g₂' w₂ y)
  -- the maps between them
  let : Algebra (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (S₂.presheaf.stalk (f₂ (g₂' y))) :=
    ((S.presheaf.stalkCongr (.of_eq hpt.symm)).hom ≫ iS.stalkMap (f₂ (g₂' y))).hom.toAlgebra
  let : Algebra (X.presheaf.stalk ((g₂' ≫ iX) y)) (X₂.presheaf.stalk (g₂' y)) :=
    ((iX.stalkMap (g₂' y)).hom).toAlgebra
  let : Algebra (S'.presheaf.stalk ((f₂' ≫ iS') y)) (S₂'.presheaf.stalk (f₂' y)) :=
    ((iS'.stalkMap (f₂' y)).hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (X₂.presheaf.stalk (g₂' y)) :=
    (((iX.stalkMap (g₂' y)).hom).comp ((f.stalkMap ((g₂' ≫ iX) y)).hom)).toAlgebra
  let : Algebra (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (S₂'.presheaf.stalk (f₂' y)) :=
    ((baseStalkMap f₂ g₂ f₂' g₂' w₂ y).comp
      ((S.presheaf.stalkCongr (.of_eq hpt.symm)).hom ≫ iS.stalkMap (f₂ (g₂' y))).hom).toAlgebra
  have : IsScalarTower (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (X.presheaf.stalk ((g₂' ≫ iX) y))
      (X₂.presheaf.stalk (g₂' y)) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (S₂.presheaf.stalk (f₂ (g₂' y)))
      (S₂'.presheaf.stalk (f₂' y)) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (X.presheaf.stalk ((g₂' ≫ iX) y)) (X₂.presheaf.stalk (g₂' y))
      (Y.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq' (Stacks.ModuleSkyscraper.stalkMap_hom_comp g₂' iX y)
  have : IsScalarTower (S'.presheaf.stalk ((f₂' ≫ iS') y)) (S₂'.presheaf.stalk (f₂' y))
      (Y.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq' (Stacks.ModuleSkyscraper.stalkMap_hom_comp f₂' iS' y)
  have : IsScalarTower (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (S₂.presheaf.stalk (f₂ (g₂' y)))
      (X₂.presheaf.stalk (g₂' y)) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have e := Scheme.Hom.stalkMap_congr_hom (iX ≫ f) (f₂ ≫ iS) hf.symm (g₂' y)
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at e
    exact congrArg CommRingCat.Hom.hom (e.trans (Category.assoc _ _ _).symm)
  have : IsScalarTower (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (S'.presheaf.stalk ((f₂' ≫ iS') y))
      (S₂'.presheaf.stalk (f₂' y)) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have hpt₂ : f₂ (g₂' y) = g₂ (f₂' y) := congrArg (fun k : Y ⟶ S₂ => k y) w₂
    have hpt₅ : f (iX (g₂' y)) = g (iS' (f₂' y)) := congrArg (fun k : Y ⟶ S => k y) w
    have e1 := Scheme.Hom.stalkMap_congr_point iS (f₂ (g₂' y)) (g₂ (f₂' y)) hpt₂
    have e2 := Scheme.Hom.stalkMap_congr_hom (iS' ≫ g) (g₂ ≫ iS) hg.symm (f₂' y)
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at e2
    have key : ((S.presheaf.stalkCongr (.of_eq hpt.symm)).hom ≫ iS.stalkMap (f₂ (g₂' y))) ≫
        (S₂.presheaf.stalkCongr (.of_eq hpt₂)).hom ≫ g₂.stalkMap (f₂' y) =
        ((S.presheaf.stalkCongr (.of_eq hpt₅)).hom ≫
          g.stalkMap (iS' (f₂' y))) ≫ iS'.stalkMap (f₂' y) := by
      rw [Category.assoc, reassoc_of% e1, Category.assoc, e2]
      simp only [← Category.assoc]
      exact (stalkCongr_comp_eq hpt.symm (congrArg iS hpt₂) hpt₅
        (congrArg (fun k : S₂' ⟶ S => k (f₂' y)) hg).symm =≫ _) =≫ _
    exact congrArg CommRingCat.Hom.hom key
  have : IsIso ((S.presheaf.stalkCongr (.of_eq hpt.symm)).hom ≫ iS.stalkMap (f₂ (g₂' y))) :=
    inferInstance
  have := isLocalization_bot_of_bijective (C := S.presheaf.stalk (f ((g₂' ≫ iX) y)))
    (D := S₂.presheaf.stalk (f₂ (g₂' y))) (ConcreteCategory.bijective_of_isIso
      ((S.presheaf.stalkCongr (.of_eq hpt.symm)).hom ≫ iS.stalkMap (f₂ (g₂' y))))
  have := isLocalization_bot_of_bijective (C := X.presheaf.stalk ((g₂' ≫ iX) y))
    (D := X₂.presheaf.stalk (g₂' y)) (ConcreteCategory.bijective_of_isIso (iX.stalkMap (g₂' y)))
  have := isLocalization_bot_of_bijective (C := S'.presheaf.stalk ((f₂' ≫ iS') y))
    (D := S₂'.presheaf.stalk (f₂' y)) (ConcreteCategory.bijective_of_isIso (iS'.stalkMap (f₂' y)))
  refine (isIso_baseChangeCohomologyMap_iff_ring f g (f₂' ≫ iS') (g₂' ≫ iX) w K E' ψ y n).trans
    ((isIso_ringBaseChangeCohomologyMap_iff_localization
      (R := S.presheaf.stalk (f ((g₂' ≫ iX) y))) (A := X.presheaf.stalk ((g₂' ≫ iX) y))
      (R' := S'.presheaf.stalk ((f₂' ≫ iS') y)) (B := Y.presheaf.stalk y)
      (R₁ := S₂.presheaf.stalk (f₂ (g₂' y))) (A₁ := X₂.presheaf.stalk (g₂' y))
      (R'₁ := S₂'.presheaf.stalk (f₂' y)) ⊥ ⊥ ⊥ hloc hloc₂ _ _ _ n).trans (Iff.trans ?_
        (isIso_baseChangeCohomologyMap_iff_ring f₂ g₂ f₂' g₂' w₂ _ E' _ y n).symm))
  refine (isIso_ringBaseChangeCohomologyMap_iff_of_iso (R := S₂.presheaf.stalk (f₂ (g₂' y)))
    (R' := S₂'.presheaf.stalk (f₂' y)) (A := X₂.presheaf.stalk (g₂' y))
    (A' := Y.presheaf.stalk y) ((derivedPullbackStalkIso iX (g₂' y)).app K) (Iso.refl _)
    _ _ ?_ n).symm
  have hW0 := inv_eq_of_eq_trans_right _ _ _ (derivedPullbackStalkCompIso_eq g₂' iX y)
  have hW1 := congrArg (fun t => NatTrans.app t K) hW0
  refine chase_source _ _ _ _ _ _ _ _ _
    ((totalDerivedExtensionScalars.{u, u, u} (algebraMap (X₂.presheaf.stalk (g₂' y))
      (Y.presheaf.stalk y))).functor.map ((derivedPullbackStalkIso iX (g₂' y)).inv.app K))
    ((derivedPullbackStalkCompIso g₂' iX y).inv.app K)
    rfl (CategoryTheory.Functor.map_comp _ _ _) hW1 ?_ (Iso.hom_inv_id_app _ _)
    ((CategoryTheory.Functor.map_comp _ _ _).symm.trans
      ((congrArg _ (Iso.hom_inv_id_app _ _)).trans (CategoryTheory.Functor.map_id _ _)))
  exact Category.assoc _ _ _

/-- **Condition (1) of Stacks 0DJ8 is local on opens.**  Let `Y → X₂ → S₂ ← S₂'` be a cartesian
square mapping by open immersions `Y ⟶ X'`, `X₂ ⟶ X`, `S₂ ⟶ S`, `S₂' ⟶ S'` to the cartesian
square `X' → X → S ← S'`.  The map of Stacks 0DJ7 of the first square at `φ : L(g')^*K ⟶ K'` is
invertible at the image of `y` in degree `n` exactly when that of the second square at the
datum pulled back along the morphism of squares is invertible at `y`. -/
theorem isIso_baseChangeCohomologyMap_pullDatum_iff (sq : IsPullback g' f' f g)
    {f₂ : X₂ ⟶ S₂} {g₂ : S₂' ⟶ S₂} {f₂' : Y ⟶ S₂'} {g₂' : Y ⟶ X₂}
    (sq₂ : IsPullback g₂' f₂' f₂ g₂) (iX : X₂ ⟶ X) (iY : Y ⟶ X') (iS : S₂ ⟶ S) (iS' : S₂' ⟶ S')
    [IsOpenImmersion iX] [IsOpenImmersion iY] [IsOpenImmersion iS] [IsOpenImmersion iS']
    (hg : g₂' ≫ iX = iY ≫ g') (hf : f₂ ≫ iS = iX ≫ f) (hf' : f₂' ≫ iS' = iY ≫ f')
    (hgS : g₂ ≫ iS = iS' ≫ g)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toSheafedSpace)))
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K') (y : Y) (n : ℤ) :
    IsIso (baseChangeCohomologyMap f₂ g₂ f₂' g₂' sq₂.w
      ((derivedPullback iX.toLRSHom.toShHom).obj K) ((derivedPullback iY.toLRSHom.toShHom).obj K')
      (Stacks.Cohomology.BaseChangeCover.pullDatum g₂'.toLRSHom.toShHom iY.toLRSHom.toShHom
        iX.toLRSHom.toShHom g'.toLRSHom.toShHom (comp_toShHom_of_comm hg) K K' φ) y n) ↔
      IsIso (baseChangeCohomologyMap f g f' g' sq.w K K' φ (iY y) n) := by
  refine ⟨fun h => ?_, isIso_baseChangeCohomologyMap_pullDatum sq sq₂ iX iY iS iS' hg hf hf' hgS
    K K' φ y n⟩
  have w₅ : (g₂' ≫ iX) ≫ f = (f₂' ≫ iS') ≫ g := by
    rw [Category.assoc, ← hf, ← Category.assoc, sq₂.w, Category.assoc, hgS, Category.assoc]
  have hφ :
      HEq ((derivedPullbackCompIsoCanonical iY.toLRSHom.toShHom g'.toLRSHom.toShHom).inv.app K ≫
        (derivedPullback iY.toLRSHom.toShHom).map φ)
        ((Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g₂'.toLRSHom.toShHom
          iY.toLRSHom.toShHom iX.toLRSHom.toShHom g'.toLRSHom.toShHom
          (comp_toShHom_of_comm hg)).inv.app K ≫ (derivedPullback iY.toLRSHom.toShHom).map φ) := by
    rw [Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft_inv_app_comp
      g'.toLRSHom.toShHom iX.toLRSHom.toShHom iY.toLRSHom.toShHom g₂'.toLRSHom.toShHom
      (comp_toShHom_of_comm hg) K K' φ]
    exact (eqToHom_comp_heq _ _).symm
  have hloc₅ := IsStalkLocalization.congr f g hf'.symm hg.symm _ w₅ y
    (IsStalkLocalization.comp_left sq.w iY y (isStalkLocalization_of_isPullback sq (iY y)))
  have h₅ := (isIso_baseChangeCohomologyMap_restrict_source_iff f g sq₂.w iX iS iS' hf hgS w₅ K _ _
    y n hloc₅ (isStalkLocalization_of_isPullback sq₂ y)).2 h
  have h₄ := isIso_baseChangeCohomologyMap_congr f g hf' hg w₅
    (by rw [Category.assoc, sq.w, Category.assoc]) K _ _ _ hφ.symm y n h₅
  exact (isIso_baseChangeCohomologyMap_comp_left_iff sq iY K K' φ y n).2 h₄

/-- **Condition (1) of Stacks 0DJ8 descends from opens.**  In the situation of
`AlgebraicGeometry.isIso_baseChangeCohomologyMap_pullDatum_iff`, if the map of Stacks 0DJ7 of the
second square at the pulled-back datum is invertible at `y` in degree `n`, so is the map of the
first square at `φ` at the image of `y`. -/
theorem isIso_baseChangeCohomologyMap_of_pullDatum (sq : IsPullback g' f' f g)
    {f₂ : X₂ ⟶ S₂} {g₂ : S₂' ⟶ S₂} {f₂' : Y ⟶ S₂'} {g₂' : Y ⟶ X₂}
    (sq₂ : IsPullback g₂' f₂' f₂ g₂) (iX : X₂ ⟶ X) (iY : Y ⟶ X') (iS : S₂ ⟶ S) (iS' : S₂' ⟶ S')
    [IsOpenImmersion iX] [IsOpenImmersion iY] [IsOpenImmersion iS] [IsOpenImmersion iS']
    (hg : g₂' ≫ iX = iY ≫ g') (hf : f₂ ≫ iS = iX ≫ f) (hf' : f₂' ≫ iS' = iY ≫ f')
    (hgS : g₂ ≫ iS = iS' ≫ g)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toSheafedSpace)))
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K') (y : Y) (n : ℤ)
    (h : IsIso (baseChangeCohomologyMap f₂ g₂ f₂' g₂' sq₂.w
      ((derivedPullback iX.toLRSHom.toShHom).obj K) ((derivedPullback iY.toLRSHom.toShHom).obj K')
      (Stacks.Cohomology.BaseChangeCover.pullDatum g₂'.toLRSHom.toShHom iY.toLRSHom.toShHom
        iX.toLRSHom.toShHom g'.toLRSHom.toShHom (comp_toShHom_of_comm hg) K K' φ) y n)) :
    IsIso (baseChangeCohomologyMap f g f' g' sq.w K K' φ (iY y) n) :=
  (isIso_baseChangeCohomologyMap_pullDatum_iff sq sq₂ iX iY iS iS' hg hf hf' hgS K K' φ y n).1 h

/-- **Condition (1) of Stacks 0DJ8 descends from the restriction to an open of `X`.**  For an
open `U` of `X`, if the map of Stacks 0DJ7 of the restricted square
`g'⁻¹(U) → U → S ← S'` at the pulled-back datum is invertible at `y` in degree `n`, so is the map
of the original square at `φ` at the image of `y` in `X'`. -/
theorem isIso_baseChangeCohomologyMap_of_restrict (hpb : IsPullback g' f' f g) (U : X.Opens)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toSheafedSpace)))
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K') (y : g' ⁻¹ᵁ U) (n : ℤ)
    (h : IsIso (baseChangeCohomologyMap (U.ι ≫ f) g ((g' ⁻¹ᵁ U).ι ≫ f') (g' ∣_ U)
      ((isPullback_morphismRestrict g' U).paste_vert hpb).w
      ((derivedPullback U.ι.toLRSHom.toShHom).obj K)
      ((derivedPullback (g' ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj K')
      (Stacks.Cohomology.BaseChangeCover.pullDatum (g' ∣_ U).toLRSHom.toShHom
        (g' ⁻¹ᵁ U).ι.toLRSHom.toShHom U.ι.toLRSHom.toShHom g'.toLRSHom.toShHom
        (comp_toShHom_of_comm (morphismRestrict_ι g' U)) K K' φ) y n)) :
    IsIso (baseChangeCohomologyMap f g f' g' hpb.w K K' φ ((g' ⁻¹ᵁ U).ι y) n) :=
  isIso_baseChangeCohomologyMap_of_pullDatum hpb
    ((isPullback_morphismRestrict g' U).paste_vert hpb) U.ι (g' ⁻¹ᵁ U).ι (𝟙 S) (𝟙 S')
    (morphismRestrict_ι g' U) (Category.comp_id _) (Category.comp_id _)
    (by rw [Category.comp_id, Category.id_comp]) K K' φ y n h

end AlgebraicGeometry
