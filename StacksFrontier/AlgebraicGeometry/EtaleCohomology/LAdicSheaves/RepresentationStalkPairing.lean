module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationCoefficientPairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkFlatTensorExact
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianFiniteGModulesPairingFiber
public import StacksFrontier.CategoryTheory.Sites.Modules.SheafTensorDescFiber

/-!
# The pairing of coefficients `ℱ_ρ ⊗ ℱ_{ρ^∨} → ℤ/ℓ^kℤ` on stalks, and its perfectness

Let `ρ : π₁(X, x̄) → GL_r(ℤ_ℓ)` be continuous and `s̄` a geometric point of `X`. The stalk at `s̄`
of the finite locally constant abelian sheaf attached to a finite discrete `π₁`-module `A` by
Tag 0DV5 (2) is identified with `A` once a path from `s̄` to `x̄` is chosen
(`finiteLocallyConstantAbelianStalkCounit`), and under this identification the pairing of sections
attached to an equivariant biadditive `P : M × N → L` becomes `P` on germs
(`finiteLocallyConstantAbelianStalkCounit_germ_pairing`). For the pairing of coefficients
`ℱ_{ρ,k} ⊗ ℱ_{ρ^∨,k} → ℤ/ℓ^kℤ` of `representationLevelTensorPairing` this says that on stalks it is
the dot product of `(ℤ/ℓ^kℤ)^r`, which is perfect. This is the stalkwise perfectness of the
coefficient pairing on which Poincaré duality, and so the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), rests.

## Main definitions

* `Stacks.EtaleCohomology.representationLevelStalkPairing`: the pairing of coefficients on
  stalks, `Stacks.EtaleCohomology.representationLevelStalkBilinear` as a bilinear map.
* `Stacks.EtaleCohomology.representationLevelStalkCounit`: the stalk of `ℱ_{ρ,k}` at `s̄` is
  `(ℤ/ℓ^kℤ)^r`, as sets, along a path.

## Main results

* `Stacks.EtaleCohomology.representationLevelStalkCounit_stalkPairing`: on stalks the pairing of
  coefficients is the dot product.
* `Stacks.EtaleCohomology.bijective_representationLevelStalkBilinear`,
  `Stacks.EtaleCohomology.bijective_flip_representationLevelStalkBilinear`: it is perfect.

## Implementation notes

The identification `representationLevelStalkCounit` is the counit of the equivalence of Tag 0DV5
(1) on the underlying sheaf of sets, followed by the counit of
`CategoryTheory.commGrpContinuousGSetEquivalence`; perfectness only uses that it is bijective,
together with the additive identification `representationLevelStalkIso` for counting.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  Stacks.ConstantSheaf Opposite CategoryTheory.CartesianMonoidalCategory

universe u

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology

namespace Stacks.EtaleCohomology

section Abelian

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] {x s : GeometricPoint X.1}
  (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)

/-- **The stalk at `s̄` of the finite locally constant abelian sheaf attached to a finite discrete
`π₁(X, x̄)`-module `A` by Tag 0DV5 (2) is `A`**, as sets, once a path `t` from `s̄` to `x̄` is
chosen: the stalk of the underlying sheaf of sets `e⁻¹A` is identified with `e e⁻¹ A ≅ A` by
`finiteLocallyConstantStalkForgetIso`. -/
def finiteLocallyConstantAbelianStalkCounit
    (A : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
      (EtaleFundamentalGroup X.1 x)).FullSubcategory)
    (m : (abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).obj
      ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj A).obj) :
    A.obj.obj.obj.V :=
  (finiteGSetForget.{u, u + 1} (EtaleFundamentalGroup X.1 x)).map (finiteGModuleCommGrpCounit A)
    (fiberCounit (ω := etaleStalkFunctor.{u, u + 1} B X.1 X.2 s)
      (finiteLocallyConstantStalkForgetIso B X t) _
      ((etaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map
        (eqToHom
          (sheafCompose_forget_finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_inverse_obj
            _ (canonicalFiniteLocallyConstantSetsEquivalence B X x) A))
        ((abelianEtaleStalkForgetIso.{u, u + 1} B X.1 X.2 s).inv.app _ m)))

/-- `finiteLocallyConstantAbelianStalkCounit` on germs. -/
theorem finiteLocallyConstantAbelianStalkCounit_germ
    (A : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
      (EtaleFundamentalGroup X.1 x)).FullSubcategory)
    (U : (geometricPointFiber B X.1 X.2 s).Elements)
    (a : ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj A).obj.obj.obj
      (op U.1)) :
    finiteLocallyConstantAbelianStalkCounit B X t A
        (abelianEtaleStalkGerm.{u, u + 1} B X.1 X.2 s _ U a) =
      (finiteGSetForget.{u, u + 1} (EtaleFundamentalGroup X.1 x)).map (finiteGModuleCommGrpCounit A)
        (fiberCounit (ω := etaleStalkFunctor.{u, u + 1} B X.1 X.2 s)
          (finiteLocallyConstantStalkForgetIso B X t) _
          (etaleStalkGerm.{u, u + 1} B X.1 X.2 s _ U
            ((eqToHom
      (sheafCompose_forget_finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_inverse_obj
                _ (canonicalFiniteLocallyConstantSetsEquivalence B X x) A)).hom.app
                  (op U.1) a))) := by
  have h := abelianEtaleStalkForgetIso_germ.{u, u + 1} B X.1 X.2 s
    ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj A).obj U a
  have hinv := (types_comp_apply _ _ _).symm.trans (types_congr_hom
    ((abelianEtaleStalkForgetIso.{u, u + 1} B X.1 X.2 s).hom_inv_id_app
      ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj A).obj)
    (etaleStalkGerm.{u, u + 1} B X.1 X.2 s _ U a))
  exact congrArg (fun z => (finiteGSetForget.{u, u + 1} (EtaleFundamentalGroup X.1 x)).map
      (finiteGModuleCommGrpCounit A) (fiberCounit (ω := etaleStalkFunctor.{u, u + 1} B X.1 X.2 s)
        (finiteLocallyConstantStalkForgetIso B X t) _ z))
    ((congrArg ((etaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map _)
      ((congrArg ((abelianEtaleStalkForgetIso.{u, u + 1} B X.1 X.2 s).inv.app _) h.symm).trans
        hinv)).trans (etaleStalkFunctor_map_etaleStalkGerm B X.1 X.2 s _ U a))

/-- `finiteLocallyConstantAbelianStalkCounit` is a bijection. -/
theorem finiteLocallyConstantAbelianStalkCounit_bijective
    (A : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
      (EtaleFundamentalGroup X.1 x)).FullSubcategory) :
    Function.Bijective (finiteLocallyConstantAbelianStalkCounit B X t A) :=
  (finiteGModuleCommGrpCounit_bijective A).comp ((fiberCounit_bijective _ _).comp
    ((((etaleStalkFunctor.{u, u + 1} B X.1 X.2 s).mapIso (eqToIso
      (sheafCompose_forget_finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_inverse_obj
          _ (canonicalFiniteLocallyConstantSetsEquivalence B X x) A))).toEquiv.bijective).comp
      ((abelianEtaleStalkForgetIso.{u, u + 1} B X.1 X.2 s).app _).symm.toEquiv.bijective))

attribute [local instance] cartesianMonoidalSheafType braidedSheafType
  braidedContinuousGSetIsFinite braidedι_continuousGSetIsFinite
  cartesianMonoidalContinuousGSet braidedContinuousGSet

omit [ConnectedSpace X.1] in
/-- Transport of sections along an equality of abelian sheaves and of their underlying sheaves of
sets. -/
theorem eqToHom_app_sheafCompose_forget
    {S S' : Sheaf (SmallEtale.topology B X.1 X.2) AddCommGrpCat.{u + 1}}
    (h : S = S') (hT : (sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj S =
      (sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj S')
    (V : (SmallEtale B X.1 X.2)ᵒᵖ) (a : S.obj.obj V) :
    (eqToHom hT).hom.app V a = (eqToHom h).hom.app V a := by
  subst h
  rfl

omit [ConnectedSpace X.1] in
/-- Transporting a section back and forth along an equality of abelian sheaves. -/
theorem eqToHom_app_eqToHom_symm_app
    {S S' : Sheaf (SmallEtale.topology B X.1 X.2) AddCommGrpCat.{u + 1}}
    (h : S = S') (V : (SmallEtale B X.1 X.2)ᵒᵖ) (q : S'.obj.obj V) :
    (eqToHom h).hom.app V ((eqToHom h.symm).hom.app V q) = q := by
  subst h
  rfl

/-- **On stalks, the pairing of finite locally constant abelian sheaves attached to an equivariant
biadditive `P : M × N → L` is `P`**: under `finiteLocallyConstantAbelianStalkCounit`, the germ of
the pairing of two sections is `P` of their germs. -/
theorem finiteLocallyConstantAbelianStalkCounit_germ_pairing
    (M N L : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
      (EtaleFundamentalGroup X.1 x)).FullSubcategory)
    (P : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP : ∀ (g : EtaleFundamentalGroup X.1 x) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P ((M.obj.obj.obj.ρ g).asHom.hom a) ((N.obj.obj.obj.ρ g).asHom.hom b) =
        (L.obj.obj.obj.ρ g).asHom.hom (P a b))
    (U : (geometricPointFiber B X.1 X.2 s).Elements)
    (a : ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj M).obj.obj.obj
      (op U.1))
    (b : ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj N).obj.obj.obj
      (op U.1)) :
    finiteLocallyConstantAbelianStalkCounit B X t L
        (abelianEtaleStalkGerm.{u, u + 1} B X.1 X.2 s _ U
          (finiteLocallyConstantPairing (SmallEtale.topology B X.1 X.2)
            (canonicalFiniteLocallyConstantSetsEquivalence B X x) M N L P hP (op U.1) a b)) =
      P (finiteLocallyConstantAbelianStalkCounit B X t M
          (abelianEtaleStalkGerm.{u, u + 1} B X.1 X.2 s _ U a))
        (finiteLocallyConstantAbelianStalkCounit B X t N
          (abelianEtaleStalkGerm.{u, u + 1} B X.1 X.2 s _ U b)) := by
  refine (finiteLocallyConstantAbelianStalkCounit_germ B X t L U _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (fun a b => P a b)
    (finiteLocallyConstantAbelianStalkCounit_germ B X t M U a).symm
    (finiteLocallyConstantAbelianStalkCounit_germ B X t N U b).symm)
  let J := SmallEtale.topology B X.1 X.2
  let e := canonicalFiniteLocallyConstantSetsEquivalence B X x
  have hM := finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_inverse_obj_obj J _ e M
  have hN := finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_inverse_obj_obj J _ e N
  have hL := finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_inverse_obj_obj J _ e L
  obtain ⟨w, hw1, hw2, hw3⟩ := exists_sectionsPairing_eq_app
    (isBimultiplicative_finiteLocallyConstantInternalPairing J e M N L P hP) (op U.1)
    ((eqToHom hM).hom.app (op U.1) a) ((eqToHom hN).hom.app (op U.1) b)
  have hA : (eqToHom
      (sheafCompose_forget_finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_inverse_obj
        J e L)).hom.app (op U.1) (finiteLocallyConstantPairing J e M N L P hP (op U.1) a b) =
      (finiteLocallyConstantInternalPairing J e M N L P hP).hom.app (op U.1) w :=
    (eqToHom_app_sheafCompose_forget B X hL _ _ _).trans
      ((eqToHom_app_eqToHom_symm_app B X hL _ _).trans hw3)
  have h1 := etaleStalkFunctor_map_etaleStalkGerm B X.1 X.2 s
    (finiteLocallyConstantInternalPairing J e M N L P hP) U w
  have hf := etaleStalkFunctor_map_etaleStalkGerm B X.1 X.2 s
    (fst ((isFiniteLocallyConstantSetSheaf J).ι.obj (e.inverse.obj (finiteGModuleCommGrp _ M).X))
      ((isFiniteLocallyConstantSetSheaf J).ι.obj (e.inverse.obj (finiteGModuleCommGrp _ N).X))) U w
  have hs := etaleStalkFunctor_map_etaleStalkGerm B X.1 X.2 s
    (snd ((isFiniteLocallyConstantSetSheaf J).ι.obj (e.inverse.obj (finiteGModuleCommGrp _ M).X))
      ((isFiniteLocallyConstantSetSheaf J).ι.obj (e.inverse.obj (finiteGModuleCommGrp _ N).X))) U w
  have key := fiberCounit_map_finiteLocallyConstantInternalPairing
    (ω := etaleStalkFunctor.{u, u + 1} B X.1 X.2 s)
    (finiteLocallyConstantStalkForgetIso B X t) M N L P hP
    (etaleStalkGerm.{u, u + 1} B X.1 X.2 s _ U w)
  let c : ∀ A : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
      (EtaleFundamentalGroup X.1 x)).FullSubcategory,
      (etaleStalkFunctor.{u, u + 1} B X.1 X.2 s).obj
        ((isFiniteLocallyConstantSetSheaf J).ι.obj (e.inverse.obj (finiteGModuleCommGrp _ A).X)) →
        A.obj.obj.obj.V := fun A z =>
    (finiteGSetForget.{u, u + 1} (EtaleFundamentalGroup X.1 x)).map (finiteGModuleCommGrpCounit A)
      (fiberCounit (ω := etaleStalkFunctor.{u, u + 1} B X.1 X.2 s)
        (finiteLocallyConstantStalkForgetIso B X t) _ z)
  have e1 : c L (etaleStalkGerm.{u, u + 1} B X.1 X.2 s _ U
      ((eqToHom
        (sheafCompose_forget_finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_inverse_obj
          J e L)).hom.app (op U.1) (finiteLocallyConstantPairing J e M N L P hP (op U.1) a b))) =
      c L ((etaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map
        (finiteLocallyConstantInternalPairing J e M N L P hP)
        (etaleStalkGerm.{u, u + 1} B X.1 X.2 s _ U w)) :=
    congrArg (fun q => c L (etaleStalkGerm.{u, u + 1} B X.1 X.2 s _ U q)) hA |>.trans
      (congrArg (c L) h1.symm)
  have e2 : c M ((etaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map (fst _ _)
      (etaleStalkGerm.{u, u + 1} B X.1 X.2 s _ U w)) =
      c M (etaleStalkGerm.{u, u + 1} B X.1 X.2 s _ U
        ((eqToHom
          (sheafCompose_forget_finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_inverse_obj
            J e M)).hom.app (op U.1) a)) :=
    (congrArg (c M) hf).trans (congrArg (fun q => c M (etaleStalkGerm.{u, u + 1} B X.1 X.2 s _ U q))
      (hw1.trans (eqToHom_app_sheafCompose_forget B X hM _ _ a).symm))
  have e3 : c N ((etaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map (snd _ _)
      (etaleStalkGerm.{u, u + 1} B X.1 X.2 s _ U w)) =
      c N (etaleStalkGerm.{u, u + 1} B X.1 X.2 s _ U
        ((eqToHom
          (sheafCompose_forget_finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_inverse_obj
            J e N)).hom.app (op U.1) b)) :=
    (congrArg (c N) hs).trans (congrArg (fun q => c N (etaleStalkGerm.{u, u + 1} B X.1 X.2 s _ U q))
      (hw2.trans (eqToHom_app_sheafCompose_forget B X hN _ _ b).symm))
  exact e1.trans (key.trans (congrArg₂ (fun p q => P p q) e2 e3))

end Abelian

section Levels

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)
  {s : GeometricPoint X.1} (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (k : ℕ)

/-- **The stalk at `s̄` of the `k`-th level of `ℱ_ρ` is the level module `(ℤ/ℓ^kℤ)^r`**, as sets,
through `finiteLocallyConstantAbelianStalkCounit`. -/
def representationLevelStalkCounit
    (m : (geometricPointSitePoint B X.1 X.2 s).sheafFiber
      (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k))) |>.obj (representationLevelSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k)) :
    (levelAbelian ρ hρ k).obj.obj.obj.V :=
  finiteLocallyConstantAbelianStalkCounit B X t (levelAbelian ρ hρ k)
    ((etaleStalkForget₂Iso B X.1 X.2 s (ZMod (ℓ ^ k)) _).hom m)

/-- `representationLevelStalkCounit` on germs. -/
theorem representationLevelStalkCounit_germ (U : (geometricPointFiber B X.1 X.2 s).Elements)
    (a : (representationLevelSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k).obj.obj (op U.1)) :
    representationLevelStalkCounit B X x ρ hρ t k
        ((geometricPointSitePoint B X.1 X.2 s).toPresheafFiber U.1 U.2
          (representationLevelSheaf B X x
            (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k).obj a) =
      finiteLocallyConstantAbelianStalkCounit B X t (levelAbelian ρ hρ k)
        (abelianEtaleStalkGerm.{u, u + 1} B X.1 X.2 s _ U a) :=
  congrArg (finiteLocallyConstantAbelianStalkCounit B X t (levelAbelian ρ hρ k))
    (ConcreteCategory.congr_hom (ι_preservesColimitIso_hom
      (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1})
      ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op ⋙ (representationLevelSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k).obj) (op U)) a)

/-- `representationLevelStalkCounit` is a bijection. -/
theorem representationLevelStalkCounit_bijective :
    Function.Bijective (representationLevelStalkCounit B X x ρ hρ t k) :=
  (finiteLocallyConstantAbelianStalkCounit_bijective B X t _).comp
    (etaleStalkForget₂Iso B X.1 X.2 s (ZMod (ℓ ^ k)) _).addCommGroupIsoToAddEquiv.bijective

/-- The stalk at `s̄` of the `k`-th level of `ℱ_ρ` as a `ℤ/ℓ^kℤ`-module: `(ℤ/ℓ^kℤ)^r`, by
`representationLevelStalkIso`. -/
def representationLevelStalkLinearEquiv :
    ((geometricPointSitePoint B X.1 X.2 s).sheafFiber
      (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k))) |>.obj (representationLevelSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k)) ≃ₗ[ZMod (ℓ ^ k)]
      (Fin r → ZMod (ℓ ^ k)) :=
  let e : ((geometricPointSitePoint B X.1 X.2 s).sheafFiber
      (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k))) |>.obj (representationLevelSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k)) ≃+
      (Fin r → ZMod (ℓ ^ k)) :=
    (representationLevelStalkIso B X x ρ hρ t k).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift
  LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap (ℓ ^ k)) e.bijective

omit [ConnectedSpace X.1] in
/-- Two germs at `s̄` of sections of two presheaves of modules are germs at a common pointed
étale neighbourhood: the neighbourhoods form a cofiltered category. -/
theorem exists_toPresheafFiber_eq₂ (R : Type) [Ring R]
    (P Q : (SmallEtale B X.1 X.2)ᵒᵖ ⥤ ModuleCat.{u + 1} R)
    (m : (geometricPointSitePoint B X.1 X.2 s).presheafFiber (A := ModuleCat.{u + 1} R) |>.obj P)
    (n : (geometricPointSitePoint B X.1 X.2 s).presheafFiber (A := ModuleCat.{u + 1} R) |>.obj Q) :
    ∃ (U : (geometricPointFiber B X.1 X.2 s).Elements) (a : P.obj (op U.1)) (b : Q.obj (op U.1)),
      (geometricPointSitePoint B X.1 X.2 s).toPresheafFiber U.1 U.2 P a = m ∧
        (geometricPointSitePoint B X.1 X.2 s).toPresheafFiber U.1 U.2 Q b = n := by
  let Φ := geometricPointSitePoint B X.1 X.2 s
  have : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    inferInstanceAs (PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1} ⋙ CategoryTheory.forget AddCommGrpCat))
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨X₁, x₁, a₁, rfl⟩ := Φ.toPresheafFiber_jointly_surjective m
  obtain ⟨X₂, x₂, b₂, rfl⟩ := Φ.toPresheafFiber_jointly_surjective n
  let W := IsCofiltered.min (C := Φ.fiber.Elements) (Φ.fiber.elementsMk X₁ x₁)
    (Φ.fiber.elementsMk X₂ x₂)
  let f₁ := IsCofiltered.minToLeft (C := Φ.fiber.Elements) (Φ.fiber.elementsMk X₁ x₁)
    (Φ.fiber.elementsMk X₂ x₂)
  let f₂ := IsCofiltered.minToRight (C := Φ.fiber.Elements) (Φ.fiber.elementsMk X₁ x₁)
    (Φ.fiber.elementsMk X₂ x₂)
  refine ⟨W, P.map f₁.1.op a₁, Q.map f₂.1.op b₂, ?_, ?_⟩
  · refine (Φ.toPresheafFiber_w_apply f₁.1 W.2 P a₁).trans ?_
    rw [f₁.2]
  · refine (Φ.toPresheafFiber_w_apply f₂.1 W.2 Q b₂).trans ?_
    rw [f₂.2]

attribute [local instance] Sheaf.monoidalCategory
  AlgebraicGeometry.moduleCat_preservesColimits_tensorLeft
  AlgebraicGeometry.moduleCat_preservesColimits_tensorRight

/-- Colimits of the size of the site in the large-universe module category. -/
local instance (n : ℕ) : HasColimitsOfSize.{u, u, u + 1, u + 2} (ModuleCat.{u + 1, 0} (ZMod n)) :=
  ModuleCat.hasColimitsOfSize.{u + 1, 0, u, u} (ZMod n)

/-- Limits of the size of the site in the large-universe module category. -/
local instance (n : ℕ) : HasLimitsOfSize.{u, u, u + 1, u + 2} (ModuleCat.{u + 1, 0} (ZMod n)) :=
  ModuleCat.instHasLimitsOfSize.{u + 1, u, 0}

/-- **The pairing of coefficients on stalks** at `s̄`: the bilinear map
`(ℱ_{ρ,k})_s̄ × (ℱ_{ρ^∨,k})_s̄ → (ℤ/ℓ^kℤ)_s̄` induced on fibres by
`representationLevelTensorPairing`. -/
def representationLevelStalkPairing
    (m : (geometricPointSitePoint B X.1 X.2 s).sheafFiber
      (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k))) |>.obj (representationLevelSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k))
    (n : (geometricPointSitePoint B X.1 X.2 s).sheafFiber
      (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k))) |>.obj (representationLevelSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (contragredient ρ)
      (continuous_contragredient hρ) k)) :
    (geometricPointSitePoint B X.1 X.2 s).sheafFiber
      (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k))) |>.obj (representationLevelSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
      (trivialRepresentation (ℓ := ℓ)) continuous_const k) :=
  (Functor.LaxMonoidal.μ ((geometricPointSitePoint B X.1 X.2 s).sheafFiber
      (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k)))) _ _ ≫
    ((geometricPointSitePoint B X.1 X.2 s).sheafFiber (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).map
      (representationLevelTensorPairing B X x ρ hρ k)).hom (m ⊗ₜ n)

/-- The pairing of coefficients on stalks, as a `ℤ/ℓ^kℤ`-bilinear map. -/
def representationLevelStalkBilinear :
    ((geometricPointSitePoint B X.1 X.2 s).sheafFiber
      (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k))) |>.obj (representationLevelSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k)) →ₗ[ZMod (ℓ ^ k)]
    ((geometricPointSitePoint B X.1 X.2 s).sheafFiber
      (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k))) |>.obj (representationLevelSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (contragredient ρ)
      (continuous_contragredient hρ) k)) →ₗ[ZMod (ℓ ^ k)]
    ((geometricPointSitePoint B X.1 X.2 s).sheafFiber
      (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k))) |>.obj (representationLevelSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
      (trivialRepresentation (ℓ := ℓ)) continuous_const k)) :=
  TensorProduct.curry (Functor.LaxMonoidal.μ ((geometricPointSitePoint B X.1 X.2 s).sheafFiber
      (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k)))) _ _ ≫
    ((geometricPointSitePoint B X.1 X.2 s).sheafFiber (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).map
      (representationLevelTensorPairing B X x ρ hρ k)).hom

/-- `representationLevelStalkBilinear` is `representationLevelStalkPairing`. -/
theorem representationLevelStalkBilinear_apply (m n) :
    representationLevelStalkBilinear B X x ρ hρ k (s := s) m n =
      representationLevelStalkPairing B X x ρ hρ k m n :=
  rfl

/-- **On stalks, the pairing of coefficients `ℱ_{ρ,k} ⊗ ℱ_{ρ^∨,k} → ℤ/ℓ^kℤ` is the dot product**
`⟨x, y⟩ = Σ xᵢ yᵢ` of `(ℤ/ℓ^kℤ)^r`, under the identifications
`representationLevelStalkCounit` of the stalks with the level modules. -/
theorem representationLevelStalkCounit_stalkPairing
    (m : (geometricPointSitePoint B X.1 X.2 s).sheafFiber
      (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k))) |>.obj (representationLevelSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k))
    (n : (geometricPointSitePoint B X.1 X.2 s).sheafFiber
      (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k))) |>.obj (representationLevelSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (contragredient ρ)
      (continuous_contragredient hρ) k)) :
    representationLevelStalkCounit B X x (trivialRepresentation (ℓ := ℓ)) continuous_const t k
        (representationLevelStalkPairing B X x ρ hρ k m n) =
      levelEvaluation ρ hρ k (representationLevelStalkCounit B X x ρ hρ t k m)
        (representationLevelStalkCounit B X x (contragredient ρ) (continuous_contragredient hρ)
          t k n) := by
  obtain ⟨U, a, b, rfl, rfl⟩ := exists_toPresheafFiber_eq₂ B X (ZMod (ℓ ^ k)) _ _ m n
  have h1 := Sheaf.sheafFiber_tensorDesc_tmul (geometricPointSitePoint B X.1 X.2 s)
    (representationLevelBilinear B X x ρ hρ k)
    (fun f a b => representationLevelBilinear_naturality B X x ρ hρ k f a b) U.1 U.2 a b
  refine (congrArg (representationLevelStalkCounit B X x (trivialRepresentation (ℓ := ℓ))
    continuous_const t k) h1).trans ?_
  refine (representationLevelStalkCounit_germ B X x _ continuous_const t k U _).trans ?_
  refine (finiteLocallyConstantAbelianStalkCounit_germ_pairing B X t _ _ _ (levelEvaluation ρ hρ k)
    (levelEvaluation_equivariant ρ hρ k) U a b).trans ?_
  exact congrArg₂ (fun p q => levelEvaluation ρ hρ k p q)
    (representationLevelStalkCounit_germ B X x ρ hρ t k U a).symm
    (representationLevelStalkCounit_germ B X x _ _ t k U b).symm

/-- A section of the stalk pairing vanishing against everything is zero: the dot product of
`(ℤ/ℓ^kℤ)^r` is nondegenerate. -/
theorem representationLevelStalkPairing_eq_zero_left
    (m : (geometricPointSitePoint B X.1 X.2 s).sheafFiber
      (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k))) |>.obj (representationLevelSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k))
    (hm : ∀ n, representationLevelStalkPairing B X x ρ hρ k m n = 0) : m = 0 := by
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso (X := X.1) (x := s) (x' := x)
  apply (representationLevelStalkCounit_bijective B X x ρ hρ t k).1
  have h0 : ∀ n, representationLevelStalkPairing B X x ρ hρ k (s := s) 0 n = 0 := fun n => by
    simp [representationLevelStalkPairing]
  have key : ∀ v : Fin r → ZMod (ℓ ^ k),
      (representationLevelStalkCounit B X x ρ hρ t k m).down ⬝ᵥ v =
        (representationLevelStalkCounit B X x ρ hρ t k 0).down ⬝ᵥ v := by
    intro v
    obtain ⟨n, hn⟩ := (representationLevelStalkCounit_bijective B X x (contragredient ρ)
      (continuous_contragredient hρ) t k).2 (ULift.up v)
    have h1 := representationLevelStalkCounit_stalkPairing B X x ρ hρ t k m n
    have h2 := representationLevelStalkCounit_stalkPairing B X x ρ hρ t k 0 n
    rw [hm n, ← h0 n, h2, hn] at h1
    exact (congrArg (fun z => z.down 0) h1).symm
  refine ULift.ext (funext fun i => ?_)
  simpa using key (Pi.single i 1)

/-- A section of the second stalk vanishing against everything is zero. -/
theorem representationLevelStalkPairing_eq_zero_right
    (n : (geometricPointSitePoint B X.1 X.2 s).sheafFiber
      (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k))) |>.obj (representationLevelSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (contragredient ρ)
      (continuous_contragredient hρ) k))
    (hn : ∀ m, representationLevelStalkPairing B X x ρ hρ k m n = 0) : n = 0 := by
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso (X := X.1) (x := s) (x' := x)
  apply (representationLevelStalkCounit_bijective B X x (contragredient ρ)
    (continuous_contragredient hρ) t k).1
  have h0 : ∀ m, representationLevelStalkPairing B X x ρ hρ k (s := s) m 0 = 0 := fun m => by
    simp [representationLevelStalkPairing]
  have key : ∀ v : Fin r → ZMod (ℓ ^ k),
      v ⬝ᵥ (representationLevelStalkCounit B X x (contragredient ρ)
        (continuous_contragredient hρ) t k n).down =
        v ⬝ᵥ (representationLevelStalkCounit B X x (contragredient ρ)
          (continuous_contragredient hρ) t k 0).down := by
    intro v
    obtain ⟨m, hm⟩ := (representationLevelStalkCounit_bijective B X x ρ hρ t k).2 (ULift.up v)
    have h1 := representationLevelStalkCounit_stalkPairing B X x ρ hρ t k m n
    have h2 := representationLevelStalkCounit_stalkPairing B X x ρ hρ t k m 0
    rw [hn m, ← h0 m, h2, hm] at h1
    exact (congrArg (fun z => z.down 0) h1).symm
  refine ULift.ext (funext fun i => ?_)
  simpa using key (Pi.single i 1)

/-- An injective bilinear map `M × N → T` of free `ℤ/n`-modules of ranks `r`, `r`, `1` is a perfect
pairing in its first variable. -/
private theorem bijective_of_injective_of_linearEquiv_pi {n r : ℕ} [NeZero n]
    {M N T : Type*} [AddCommGroup M] [Module (ZMod n) M] [AddCommGroup N] [Module (ZMod n) N]
    [AddCommGroup T] [Module (ZMod n) T] (f : M →ₗ[ZMod n] N →ₗ[ZMod n] T)
    (hinj : Function.Injective f) (eM : M ≃ₗ[ZMod n] (Fin r → ZMod n))
    (eN : N ≃ₗ[ZMod n] (Fin r → ZMod n)) (eT : T ≃ₗ[ZMod n] (Fin 1 → ZMod n)) :
    Function.Bijective f := by
  let eH := (eN.arrowCongr eT).trans
    (LinearEquiv.piRing (ZMod n) (Fin 1 → ZMod n) (Fin r) (ZMod n))
  have : Finite (N →ₗ[ZMod n] T) := Finite.of_equiv _ eH.toEquiv.symm
  refine hinj.bijective_of_nat_card_le ?_
  rw [Nat.card_congr eH.toEquiv, Nat.card_congr eM.toEquiv]
  exact (Nat.card_congr (Equiv.arrowCongr (Equiv.refl (Fin r))
    (Equiv.funUnique (Fin 1) (ZMod n)))).le

/-- **The pairing of coefficients is perfect on stalks**: at every geometric point `s̄`, the map
`(ℱ_{ρ,k})_s̄ → Hom((ℱ_{ρ^∨,k})_s̄, (ℤ/ℓ^kℤ)_s̄)` it induces is bijective. -/
theorem bijective_representationLevelStalkBilinear :
    Function.Bijective (representationLevelStalkBilinear B X x ρ hρ k (s := s)) := by
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso (X := X.1) (x := s) (x' := x)
  have : NeZero (ℓ ^ k) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  exact bijective_of_injective_of_linearEquiv_pi _
    ((injective_iff_map_eq_zero _).2 fun m hm =>
      representationLevelStalkPairing_eq_zero_left B X x ρ hρ k m fun n =>
        (representationLevelStalkBilinear_apply B X x ρ hρ k m n).symm.trans
          (LinearMap.congr_fun hm n))
    (representationLevelStalkLinearEquiv B X x ρ hρ t k)
    (representationLevelStalkLinearEquiv B X x (contragredient ρ)
      (continuous_contragredient hρ) t k)
    (representationLevelStalkLinearEquiv B X x (trivialRepresentation (ℓ := ℓ))
      continuous_const t k)

/-- **The pairing of coefficients is perfect on stalks**, in the second variable. -/
theorem bijective_flip_representationLevelStalkBilinear :
    Function.Bijective (representationLevelStalkBilinear B X x ρ hρ k (s := s)).flip := by
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso (X := X.1) (x := s) (x' := x)
  have : NeZero (ℓ ^ k) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  exact bijective_of_injective_of_linearEquiv_pi _
    ((injective_iff_map_eq_zero _).2 fun n hn =>
      representationLevelStalkPairing_eq_zero_right B X x ρ hρ k n fun m =>
        (representationLevelStalkBilinear_apply B X x ρ hρ k m n).symm.trans
          (LinearMap.congr_fun hn m))
    (representationLevelStalkLinearEquiv B X x (contragredient ρ)
      (continuous_contragredient hρ) t k)
    (representationLevelStalkLinearEquiv B X x ρ hρ t k)
    (representationLevelStalkLinearEquiv B X x (trivialRepresentation (ℓ := ℓ))
      continuous_const t k)

end Levels

end Stacks.EtaleCohomology
