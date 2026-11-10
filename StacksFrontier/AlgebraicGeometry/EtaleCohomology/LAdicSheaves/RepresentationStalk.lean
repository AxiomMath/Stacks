module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.FibreStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.FrobeniusStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkMatrix

/-!
# The stalks of `ℱ_ρ`

Let `X` be a connected scheme with geometric point `x̄` and let
`ρ : π₁(X, x̄) → GL_r(ℤ_ℓ)` be a continuous representation. This file identifies the stalk of the
`ℓ`-adic sheaf `ℱ_ρ` at a geometric point `s̄`, given a path `t` from `s̄` to `x̄`, with `ℤ_ℓ^r`
level by level, compatibly with reduction and with the action of endomorphisms of `s̄`.

## Main definitions

* `Stacks.EtaleCohomology.finiteLocallyConstantStalkForgetIso`: the stalk at `s̄` of a finite
  locally constant sheaf of sets is the finite `π₁(X, x̄)`-set attached to it by Tag 0DV5 (1).
* `Stacks.EtaleCohomology.finiteLocallyConstantAbelianStalkIso`: the stalk at `s̄` of a finite
  locally constant abelian sheaf is the finite `π₁(X, x̄)`-module attached to it by
  Tag 0DV5 (2).
* `Stacks.EtaleCohomology.representationLevelStalkIso`: the stalk at `s̄` of the `k`-th level of
  `ℱ_ρ` is `(ℤ/ℓ^kℤ)^r`.
* `Stacks.EtaleCohomology.representationLevelTrivialization`: the stalk of `ℱ_ρ` at `s̄` is
  `ℤ_ℓ^r`, level by level.

## Main results

* `Stacks.EtaleCohomology.representationLevelStalkIso_geometricPointStalkMap`: an endomorphism
  of `s̄` acts on the stalk of the `k`-th level through `ρ` modulo `ℓ ^ k`.
* `Stacks.EtaleCohomology.representationLevelStalkIso_transition`: the stalk transitions of
  `ℱ_ρ` are reduction.
* `Stacks.EtaleCohomology.charpoly_rationalStalkEnd_representationLAdicSheaf`: the characteristic
  polynomial of an endomorphism of `s̄` on the rational stalk of `ℱ_ρ` is that of `ρ` at the
  corresponding element of `π₁(X, x̄)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf

universe u

namespace Stacks.EtaleCohomology

section Sets

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)

/-- The finite `π₁(X, x̄)`-set attached by the canonical equivalence of Tag 0DV5 (1) to a finite
locally constant sheaf of sets has underlying set the geometric fibre at `x̄` of the finite étale
cover representing the sheaf. -/
public def canonicalFiniteLocallyConstantSetsForgetIso :
    (canonicalFiniteLocallyConstantSetsEquivalence B X x).functor ⋙ ObjectProperty.ι _ ⋙
        ContinuousGSet.forget (EtaleFundamentalGroup X.1 x) ≅
      (finiteLocallyConstantFiniteEtaleEquivalence B X).functor ⋙ finiteEtaleFiberFunctor x ⋙
        uliftFunctor.{u + 1} :=
  NatIso.ofComponents (fun G => Equiv.toIso ((FintypeCat.uSwitchEquiv _).trans Equiv.ulift.symm))
    (by
      intro G H f
      ext y
      exact congrArg ULift.up (FintypeCat.uSwitchEquiv_naturality _ y).symm)

/-- Under `canonicalFiniteLocallyConstantSetsForgetIso`, an element of `π₁(X, x̄)` acts on the
geometric fibre by evaluating the natural automorphism of the fibre functor it is. -/
public theorem canonicalFiniteLocallyConstantSetsForgetIso_hom_ρ
    (G : (isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory)
    (g : EtaleFundamentalGroup X.1 x)
    (y : ((canonicalFiniteLocallyConstantSetsEquivalence B X x).functor.obj G).obj.obj.obj.V) :
    ((canonicalFiniteLocallyConstantSetsForgetIso B X x).hom.app G
        (((canonicalFiniteLocallyConstantSetsEquivalence B X x).functor.obj G).obj.obj.obj.ρ g
          y)).down =
      (g.asIso.hom.app ((finiteLocallyConstantFiniteEtaleEquivalence B X).functor.obj G))
        ((canonicalFiniteLocallyConstantSetsForgetIso B X x).hom.app G y).down :=
  (FintypeCat.uSwitchEquiv_naturality _ y).symm.trans
    (finiteEtaleEquivalenceOfIsGaloisCategory_action X.1 x
      ((finiteLocallyConstantFiniteEtaleEquivalence B X).functor.obj G) g _)

variable {x} in
/-- **The stalk at a geometric point `s̄` of a finite locally constant sheaf of sets is the finite
`π₁(X, x̄)`-set that the canonical equivalence of Tag 0DV5 (1) attaches to it**, once a path
`t` from `s̄` to `x̄` (an isomorphism of fibre functors) is chosen, naturally in the sheaf. -/
public def finiteLocallyConstantStalkForgetIso {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) :
    ObjectProperty.ι _ ⋙ sheafToPresheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1)) ⋙
        etaleStalkPresheafFunctor B X.1 X.2 s (Type (u + 1)) ≅
      (canonicalFiniteLocallyConstantSetsEquivalence B X x).functor ⋙ ObjectProperty.ι _ ⋙
        ContinuousGSet.forget (EtaleFundamentalGroup X.1 x) :=
  finiteLocallyConstantStalkIso B X s ≪≫
    Functor.isoWhiskerLeft (finiteLocallyConstantFiniteEtaleEquivalence B X).functor
      (Functor.isoWhiskerRight t uliftFunctor.{u + 1}) ≪≫
    (canonicalFiniteLocallyConstantSetsForgetIso B X x).symm

variable {x} in
/-- **The action of an endomorphism of a geometric point on the stalks of finite locally constant
sheaves of sets is the action of an element of `π₁`.** If the natural automorphism `σ` of the
fibre functor at `s̄` is precomposition with `a : s̄ ⟶ s̄`, then the map of Tag 04FN along `a` on
the stalk at `s̄` is, under `finiteLocallyConstantStalkForgetIso`, the action of the element of
`π₁(X, x̄)` that the path `t` transports `σ` to. -/
public theorem geometricPointStalkMap_finiteLocallyConstantStalkForgetIso
    {s : GeometricPoint X.1} (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (a : GeometricPoint.Hom s s) (σ : EtaleFundamentalGroup X.1 s)
    (hσ : σ.asIso.hom = finiteEtaleFiberMap a)
    (G : (isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory) :
    (geometricPointStalkMap B X.1 X.2 a (Type (u + 1))).app G.obj.obj ≫
        (finiteLocallyConstantStalkForgetIso B X t).hom.app G =
      (finiteLocallyConstantStalkForgetIso B X t).hom.app G ≫
        (((canonicalFiniteLocallyConstantSetsEquivalence B X x).functor.obj G).obj.obj.obj.ρ
          (etaleFundamentalGroupMulEquiv t σ)).asHom := by
  change _ ≫ ((finiteLocallyConstantStalkIso B X s).hom.app G ≫
      uliftFunctor.{u + 1}.map (t.hom.app _) ≫
      (canonicalFiniteLocallyConstantSetsForgetIso B X x).inv.app G) =
    ((finiteLocallyConstantStalkIso B X s).hom.app G ≫
      uliftFunctor.{u + 1}.map (t.hom.app _) ≫
      (canonicalFiniteLocallyConstantSetsForgetIso B X x).inv.app G) ≫ _
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    (geometricPointStalkMap_finiteLocallyConstantStalkIso B X a G))).trans ?_
  refine (Category.assoc _ _ _).trans (Eq.trans (congrArg (_ ≫ ·) ?_)
    (Category.assoc _ _ _).symm)
  ext ⟨y⟩
  apply (canonicalFiniteLocallyConstantSetsForgetIso B X x).app G |>.toEquiv.injective
  apply ULift.ext
  refine Eq.trans ?_ (canonicalFiniteLocallyConstantSetsForgetIso_hom_ρ B X x G _ _).symm
  change ((canonicalFiniteLocallyConstantSetsForgetIso B X x).hom.app G
      ((canonicalFiniteLocallyConstantSetsForgetIso B X x).inv.app G
        (ULift.up (t.hom.app _ ((finiteEtaleFiberMap a).app _ y))))).down =
    (((etaleFundamentalGroupMulEquiv t) σ).asIso.hom.app _)
      ((canonicalFiniteLocallyConstantSetsForgetIso B X x).hom.app G
        ((canonicalFiniteLocallyConstantSetsForgetIso B X x).inv.app G
          (ULift.up (t.hom.app _ y)))).down
  have hinv := ((canonicalFiniteLocallyConstantSetsForgetIso B X x).app G).inv_hom_id_apply
  refine (congrArg ULift.down (hinv _)).trans (Eq.trans ?_
    (congrArg (fun z => (((etaleFundamentalGroupMulEquiv t) σ).asIso.hom.app _) (ULift.down z))
      (hinv _)).symm)
  change _ = t.hom.app _ (σ.asIso.hom.app _ (t.inv.app _ (t.hom.app _ y)))
  rw [hσ]
  have hy := (t.app ((finiteLocallyConstantFiniteEtaleEquivalence B X).functor.obj
    G)).hom_inv_id_apply
  exact congrArg (fun z => t.hom.app _ ((finiteEtaleFiberMap a).app _ z)) (hy y).symm

end Sets

section Abelian

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] {x : GeometricPoint X.1}

/-- The underlying sets of the stalk at `s̄` of a finite locally constant abelian sheaf and of the
finite `π₁(X, x̄)`-module attached to it by Tag 0DV5 (2) are isomorphic, for a path `t` from `s̄`
to `x̄`, naturally in the sheaf. -/
public def finiteLocallyConstantAbelianStalkForgetIso {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) :
    (ObjectProperty.ι _ ⋙ abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s) ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1} ≅
      ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).functor ⋙
        ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)) ⋙
          CategoryTheory.forget AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerLeft (ObjectProperty.ι _)
      (abelianEtaleStalkForgetIso.{u, u + 1} B X.1 X.2 s).symm ≪≫
    Functor.isoWhiskerLeft (forgetFiniteLocallyConstantAbelianSheaf _)
      (finiteLocallyConstantStalkForgetIso B X t)

/-- **The stalk at a geometric point `s̄` of a finite locally constant abelian sheaf is the finite
discrete `π₁(X, x̄)`-module that the canonical equivalence of Tag 0DV5 (2) attaches to it**, as
abelian groups, once a path `t` from `s̄` to `x̄` is chosen; natural in the sheaf. -/
public def finiteLocallyConstantAbelianStalkIso {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) :
    ObjectProperty.ι _ ⋙ abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s ≅
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).functor ⋙
        ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x) :=
  letI : HasBinaryBiproducts (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory := .of_hasBinaryProducts
  haveI : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
      (EtaleFundamentalGroup X.1 x)).ι.Additive :=
    inferInstance
  haveI : (ContinuousGAddCommGrp.forget.{u + 1, u + 1} (EtaleFundamentalGroup X.1 x)).Additive :=
    ⟨rfl⟩
  natIsoOfForgetAddCommGrpCat (finiteLocallyConstantAbelianStalkForgetIso B X t)

/-- **The action of an endomorphism of a geometric point on the stalks of finite locally constant
abelian sheaves is the action of an element of `π₁`**: the abelian form of
`geometricPointStalkMap_finiteLocallyConstantStalkForgetIso`. -/
public theorem geometricPointStalkMap_finiteLocallyConstantAbelianStalkIso
    {s : GeometricPoint X.1} (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (a : GeometricPoint.Hom s s) (σ : EtaleFundamentalGroup X.1 s)
    (hσ : σ.asIso.hom = finiteEtaleFiberMap a)
    (A : (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory) :
    (geometricPointStalkMap B X.1 X.2 a AddCommGrpCat.{u + 1}).app A.obj.obj ≫
        (finiteLocallyConstantAbelianStalkIso B X t).hom.app A =
      (finiteLocallyConstantAbelianStalkIso B X t).hom.app A ≫
        (((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).functor.obj
          A).obj.obj.obj.ρ (etaleFundamentalGroupMulEquiv t σ)).asHom := by
  have := forget_preservesFiberColimits.{u, u + 1} B X.1 X.2 s
  have hpre := geometricPointStalkMap_preservesColimitIso B X.1 X.2
    (CategoryTheory.forget AddCommGrpCat.{u + 1}) a A.obj.obj
  have hset := geometricPointStalkMap_finiteLocallyConstantStalkForgetIso B X t a σ hσ
    ((forgetFiniteLocallyConstantAbelianSheaf _).obj A)
  ext z
  have h1 := ConcreteCategory.congr_hom hpre z
  have h2 := ConcreteCategory.congr_hom hset
    ((preservesColimitIso (CategoryTheory.forget AddCommGrpCat.{u + 1})
      ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op ⋙ A.obj.obj)).hom z)
  change (finiteLocallyConstantStalkForgetIso B X t).hom.app
        ((forgetFiniteLocallyConstantAbelianSheaf _).obj A)
      ((preservesColimitIso (CategoryTheory.forget AddCommGrpCat.{u + 1})
        ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op ⋙ A.obj.obj)).hom
        ((geometricPointStalkMap B X.1 X.2 a AddCommGrpCat.{u + 1}).app A.obj.obj z)) =
    ConcreteCategory.hom
        ((((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).functor.obj
          A).obj.obj.obj.ρ (etaleFundamentalGroupMulEquiv t σ)).asHom)
      ((finiteLocallyConstantStalkForgetIso B X t).hom.app
          ((forgetFiniteLocallyConstantAbelianSheaf _).obj A)
        ((preservesColimitIso (CategoryTheory.forget AddCommGrpCat.{u + 1})
          ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op ⋙ A.obj.obj)).hom z))
  rw [show (preservesColimitIso (CategoryTheory.forget AddCommGrpCat.{u + 1})
        ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op ⋙ A.obj.obj)).hom
        ((geometricPointStalkMap B X.1 X.2 a AddCommGrpCat.{u + 1}).app A.obj.obj z) = _ from h1]
  exact h2

end Abelian

section ModuleStalk

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (R : Type) [Ring R]

/-- The forgetful functor from modules over a ring of the lowest universe to abelian groups
preserves filtered colimits of the size of its universe. -/
public instance forget₂_moduleCat_preservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) where
  preserves_filtered_colimits _ _ _ :=
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone
          (ModuleCat.FilteredColimits.colimitCoconeIsColimit.{u + 1, 0} F)
          (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})) }

/-- The forgetful functor from modules to abelian groups preserves the filtered colimit over the
pointed étale neighbourhoods of a geometric point. -/
public instance forget₂_moduleCat_preservesFiberColimits :
    PreservesColimitsOfShape (geometricPointFiber B S hS s).Elementsᵒᵖ
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) := by
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  exact Functor.Final.preservesColimitsOfShape_of_final
    (FinallySmall.fromFilteredFinalModel.{u} (geometricPointFiber B S hS s).Elementsᵒᵖ) _

/-- **The underlying abelian group of the stalk of a sheaf of modules is the stalk of its
underlying abelian sheaf.** -/
public def etaleStalkForget₂Iso (F : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} R)) :
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).obj (etaleStalk B S hS s F.obj) ≅
      (abelianEtaleStalkFunctor.{u, u + 1} B S hS s).obj
        ((sheafCompose (SmallEtale.topology B S hS)
          (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj F) :=
  preservesColimitIso (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})
    ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙ F.obj)

end ModuleStalk

section Levels

open AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)

/-- **The stalk at `s̄` of the `k`-th level of `ℱ_ρ` is `(ℤ/ℓ^kℤ)^r`**, for a path `t` from `s̄` to
`x̄`. -/
public def representationLevelStalkIso {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (k : ℕ) :
    (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1}).obj
        (etaleStalk B X.1 X.2 s (representationLevelSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k).obj) ≅
      AddCommGrpCat.of (ULift.{u + 1} (Fin r → ZMod (ℓ ^ k))) :=
  etaleStalkForget₂Iso B X.1 X.2 s (ZMod (ℓ ^ k)) _ ≪≫
    (finiteLocallyConstantAbelianStalkIso B X t).app
      ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj
        (levelAbelian ρ hρ k)) ≪≫
    (ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).mapIso
      ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).counitIso.app
        (levelAbelian ρ hρ k))

/-- **The action of an endomorphism `a` of the geometric point on the stalk of the `k`-th level
of `ℱ_ρ` is `ρ` modulo `ℓ ^ k` of an element of `π₁`**: if the automorphism `σ` of the fibre
functor at `s̄` is precomposition with `a`, it is the level representation of the element that
the path `t` transports `σ` to. -/
public theorem representationLevelStalkIso_geometricPointStalkMap {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (a : GeometricPoint.Hom s s)
    (σ : EtaleFundamentalGroup X.1 s) (hσ : σ.asIso.hom = finiteEtaleFiberMap a) (k : ℕ)
    (y : (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1}).obj
        (etaleStalk B X.1 X.2 s (representationLevelSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k).obj)) :
    ((representationLevelStalkIso B X x ρ hρ t k).hom
        ((forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1}).map
          ((geometricPointStalkMap B X.1 X.2 a (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).app
            (representationLevelSheaf B X x
              (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k).obj) y)).down =
      levelRepresentation ρ k (etaleFundamentalGroupMulEquiv t σ)
        ((representationLevelStalkIso B X x ρ hρ t k).hom y).down := by
  set e := canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x
  set L := levelAbelian ρ hρ k
  set g := etaleFundamentalGroupMulEquiv t σ
  let I1 := ConcreteCategory.hom (etaleStalkForget₂Iso B X.1 X.2 s (ZMod (ℓ ^ k))
    (representationLevelSheaf B X x e ρ hρ k)).hom
  let m := ConcreteCategory.hom
    ((forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1}).map
      ((geometricPointStalkMap B X.1 X.2 a (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).app
        (representationLevelSheaf B X x e ρ hρ k).obj))
  let abM := ConcreteCategory.hom ((geometricPointStalkMap B X.1 X.2 a AddCommGrpCat.{u + 1}).app
    (e.inverse.obj L).obj.obj)
  let I2 := ConcreteCategory.hom
    ((finiteLocallyConstantAbelianStalkIso B X t).hom.app (e.inverse.obj L))
  let C := ConcreteCategory.hom (e.counitIso.hom.app L).hom.hom.hom.hom
  let ρ1 := ConcreteCategory.hom ((e.functor.obj (e.inverse.obj L)).obj.obj.obj.ρ g).asHom
  let ρL := ConcreteCategory.hom (L.obj.obj.obj.ρ g).asHom
  have s1 : I1 (m y) = abM (I1 y) := ConcreteCategory.congr_hom
    (geometricPointStalkMap_preservesColimitIso B X.1 X.2
      (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1}) a
      (representationLevelSheaf B X x e ρ hρ k).obj) y
  have s2 : ∀ z, I2 (abM z) = ρ1 (I2 z) := fun z => ConcreteCategory.congr_hom
    (geometricPointStalkMap_finiteLocallyConstantAbelianStalkIso B X t a σ hσ (e.inverse.obj L)) z
  have s3 : ∀ w, C (ρ1 w) = ρL (C w) := fun w => ConcreteCategory.congr_hom
    ((e.counitIso.hom.app L).hom.hom.hom.comm g) w
  change (C (I2 (I1 (m y)))).down = levelRepresentation ρ k g (C (I2 (I1 y))).down
  rw [s1]
  exact (congrArg (fun z => (C z).down) (s2 (I1 y))).trans (congrArg ULift.down (s3 _))

/-- The underlying abelian map of the stalk transition of `ℱ_ρ` is the map of abelian stalks
induced by the transition of underlying abelian sheaves. -/
public theorem forget₂_finiteLevelStalkTransition_representation (s : GeometricPoint X.1) (k : ℕ) :
    (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (k + 1)))) AddCommGrpCat.{u + 1}).map
        (colim.map (Functor.whiskerLeft
          ((Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op)
          (representationLevelTransition B X x
            (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k).hom) ≫
        (preservesColimitIso (ModuleCat.restrictScalars (levelRingHom (ℓ := ℓ) k))
          (((Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op) ⋙
            (representationLevelSheaf B X x
              (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k).obj)).inv) ≫
        (etaleStalkForget₂Iso B X.1 X.2 s (ZMod (ℓ ^ k)) _).hom =
      (etaleStalkForget₂Iso B X.1 X.2 s (ZMod (ℓ ^ (k + 1))) _).hom ≫
        (abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map
          ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map
            (levelAbelianReduction ρ hρ k)).hom := by
  set e := canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x
  let π := (Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op
  let f₁ := forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (k + 1)))) AddCommGrpCat.{u + 1}
  let f₀ := forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1}
  let res := ModuleCat.restrictScalars.{u + 1} (levelRingHom (ℓ := ℓ) k)
  let D₁ := π ⋙ (representationLevelSheaf B X x e ρ hρ (k + 1)).obj
  let D₀ := π ⋙ (representationLevelSheaf B X x e ρ hρ k).obj
  refine (isColimitOfPreserves f₁ (colimit.isColimit D₁)).hom_ext fun j => ?_
  change f₁.map (colimit.ι D₁ j) ≫ _ = f₁.map (colimit.ι D₁ j) ≫ _
  have hT : colimit.ι D₁ j ≫ colim.map (Functor.whiskerLeft π
        (representationLevelTransition B X x e ρ hρ k).hom) ≫ (preservesColimitIso res D₀).inv =
      (representationLevelTransition B X x e ρ hρ k).hom.app (π.obj j) ≫
        res.map (colimit.ι D₀ j) := by
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (colimit.ι_map _ j))).trans ?_
    exact (Category.assoc _ _ _).trans
      (congrArg ((representationLevelTransition B X x e ρ hρ k).hom.app (π.obj j) ≫ ·)
        (ι_preservesColimitIso_inv res D₀ j))
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) ((f₁.map_comp _ _).symm.trans ((congrArg f₁.map hT).trans
    (f₁.map_comp _ _)))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans (congrArg (_ ≫ ·) (ι_preservesColimitIso_hom f₀ D₀ j)) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (· ≫ _) (ι_preservesColimitIso_hom f₁ D₁ j)).symm
  exact (colimit.ι_map (Functor.whiskerLeft π
    ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map
      (levelAbelianReduction ρ hρ k)).hom.hom) j).symm

/-- **The stalk transitions of `ℱ_ρ` are reduction** under `representationLevelStalkIso`. -/
public theorem representationLevelStalkIso_transition {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (k : ℕ)
    (y : (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (k + 1)))) AddCommGrpCat.{u + 1}).obj
        (etaleStalk B X.1 X.2 s (representationLevelSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ (k + 1)).obj)) :
    ((representationLevelStalkIso B X x ρ hρ t k).hom
        ((forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (k + 1)))) AddCommGrpCat.{u + 1}).map
          (colim.map (Functor.whiskerLeft
            ((Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op)
            (representationLevelTransition B X x
              (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k).hom) ≫
          (preservesColimitIso (ModuleCat.restrictScalars (levelRingHom (ℓ := ℓ) k))
            (((Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op) ⋙
              (representationLevelSheaf B X x
                (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k).obj)).inv)
          y)).down =
      levelReduction k ((representationLevelStalkIso B X x ρ hρ t (k + 1)).hom y).down := by
  set e := canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x
  let red := levelAbelianReduction ρ hρ k
  let I1 : ∀ k, _ := fun k => ConcreteCategory.hom (etaleStalkForget₂Iso B X.1 X.2 s (ZMod (ℓ ^ k))
    (representationLevelSheaf B X x e ρ hρ k)).hom
  let I2 : ∀ k, _ := fun k => ConcreteCategory.hom
    ((finiteLocallyConstantAbelianStalkIso B X t).hom.app (e.inverse.obj (levelAbelian ρ hρ k)))
  let C : ∀ k, _ := fun k => ConcreteCategory.hom
    (e.counitIso.hom.app (levelAbelian ρ hρ k)).hom.hom.hom.hom
  let m := ConcreteCategory.hom ((forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (k + 1))))
    AddCommGrpCat.{u + 1}).map
          (colim.map (Functor.whiskerLeft
            ((Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op)
            (representationLevelTransition B X x e ρ hρ k).hom) ≫
          (preservesColimitIso (ModuleCat.restrictScalars (levelRingHom (ℓ := ℓ) k))
            (((Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op) ⋙
              (representationLevelSheaf B X x e ρ hρ k).obj)).inv))
  let ab := ConcreteCategory.hom ((abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map
    (e.inverse.map red).hom)
  have s1 : I1 k (m y) = ab (I1 (k + 1) y) := ConcreteCategory.congr_hom
    (forget₂_finiteLevelStalkTransition_representation B X x ρ hρ s k) y
  have s2 := fun z => ConcreteCategory.congr_hom
    ((finiteLocallyConstantAbelianStalkIso B X t).hom.naturality (e.inverse.map red)) z
  have s3 := fun w => ConcreteCategory.congr_hom
    (congrArg (fun f => f.hom.hom.hom.hom) (e.counitIso.hom.naturality red)) w
  change (C k (I2 k (I1 k (m y)))).down =
    levelReduction k (C (k + 1) (I2 (k + 1) (I1 (k + 1) y))).down
  rw [s1]
  exact (congrArg (fun z => (C k z).down) (s2 _)).trans (congrArg ULift.down (s3 _))

end Levels

section LAdic

open AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]
  (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)

/-- **The stalk of `ℱ_ρ` at `s̄` is `ℤ_ℓ^r`, level by level**, for a path `t` from `s̄` to `x̄`. -/
public def representationLevelTrivialization {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) :
    LAdicSheaf.LevelTrivialization (representationLAdicSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) s r where
  equiv n := (representationLevelStalkIso B X x ρ hρ t (n + 1)).addCommGroupIsoToAddEquiv.trans
    AddEquiv.ulift
  transition n y := representationLevelStalkIso_transition B X x ρ hρ t (n + 1) y

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- **The characteristic polynomial of an endomorphism of a geometric point on the rational stalk
of `ℱ_ρ`**: if the automorphism `σ` of the fibre functor at `s̄` is precomposition with
`a : s̄ ⟶ s̄`, it is the characteristic polynomial of `ρ` at the element of `π₁(X, x̄)` that a path
`t` from `s̄` to `x̄` transports `σ` to. -/
public theorem charpoly_rationalStalkEnd_representationLAdicSheaf {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (a : GeometricPoint.Hom s s)
    (σ : EtaleFundamentalGroup X.1 s) (hσ : σ.asIso.hom = finiteEtaleFiberMap a) :
    (LAdicSheaf.rationalStalkEnd B X ℓ (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) a).charpoly =
      (ρ (etaleFundamentalGroupMulEquiv t σ)).val.charpoly.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) :=
  (representationLevelTrivialization B X x ρ hρ t).charpoly_rationalStalkEnd a _ fun n y =>
    congrArg ULift.down (ULift.ext
      (representationLevelStalkIso_geometricPointStalkMap B X x ρ hρ t a σ hσ (n + 1) y))

end LAdic

end Stacks.EtaleCohomology

end
