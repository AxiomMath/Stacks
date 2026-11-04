module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.BaseChangeRepresentable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationSheaf
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.FundamentalGroupTheorem

/-!
# The equivalences of Tag 0DV5 at two base points

Let `X` be a connected scheme with geometric points `x̄`, `x̄'` and an isomorphism
`t : F_x̄ ≅ F_x̄'` of the geometric fibre functors (Tag 0BND (2)), inducing
`π₁(X, x̄) ≃ π₁(X, x̄')`. The equivalences of Tag 0BND (1) at the two points are compatible:
restricting the action of `π₁(X, x̄)` on the fibre at `x̄` along `π₁(X, x̄') ≃ π₁(X, x̄)` gives the
action on the fibre at `x̄'`, through `t` (`AlgebraicGeometry.finiteEtaleEquivalenceBasePointIso`).
The same holds for the equivalences of Tag 0DV5 (1) for sheaves of sets, and for the equivalence of
Tag 0DV5 (2) for finite locally constant abelian sheaves
(`Stacks.EtaleCohomology.finiteLocallyConstantAbelianSheafEquivalenceBasePointIso`).

## Main definitions

* `AlgebraicGeometry.etaleFundamentalGroupBasePointHom`: `π₁(X, x̄') →ₜ* π₁(X, x̄)`.
* `AlgebraicGeometry.finiteEtaleEquivalenceBasePointIso`.
* `Stacks.EtaleCohomology.finiteLocallyConstantSetsEquivalenceBasePointIso`.
* `Stacks.EtaleCohomology.finiteLocallyConstantAbelianSheafEquivalenceBasePointIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped FintypeCatDiscrete

universe u

namespace AlgebraicGeometry

section ResIso

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  (φ : G →ₜ* H)

/-- An equivariant bijection `A ≃ B` from the restriction along `φ` of a continuous finite
`H`-set to a continuous finite `G`-set gives an isomorphism `res_φ A ≅ B`. -/
public def contActionResIsoMk {A : ContAction FintypeCat.{u} H} {B : ContAction FintypeCat.{u} G}
    (e : A.obj.V ≃ B.obj.V)
    (he : ∀ g a, e (ConcreteCategory.hom (A.obj.ρ (φ g)) a) =
      ConcreteCategory.hom (B.obj.ρ g) (e a)) :
    (ContAction.res FintypeCat.{u} φ).obj A ≅ B :=
  ObjectProperty.isoMk _ (Action.mkIso (FintypeCat.equivEquivIso e)
    (fun g => FintypeCat.hom_ext _ _ fun a => he g a))

/-- Naturality of `AlgebraicGeometry.contActionResIsoMk`. -/
public theorem contActionResIsoMk_naturality {A₁ A₂ : ContAction FintypeCat.{u} H}
    {B₁ B₂ : ContAction FintypeCat.{u} G} (e₁ : A₁.obj.V ≃ B₁.obj.V) (e₂ : A₂.obj.V ≃ B₂.obj.V)
    (he₁ : ∀ g a, e₁ (ConcreteCategory.hom (A₁.obj.ρ (φ g)) a) =
      ConcreteCategory.hom (B₁.obj.ρ g) (e₁ a))
    (he₂ : ∀ g a, e₂ (ConcreteCategory.hom (A₂.obj.ρ (φ g)) a) =
      ConcreteCategory.hom (B₂.obj.ρ g) (e₂ a))
    (f : A₁ ⟶ A₂) (f' : B₁ ⟶ B₂)
    (hf : ∀ a, e₂ (f.hom.hom a) = f'.hom.hom (e₁ a)) :
    (ContAction.res FintypeCat.{u} φ).map f ≫ (contActionResIsoMk φ e₂ he₂).hom =
      (contActionResIsoMk φ e₁ he₁).hom ≫ f' :=
  ObjectProperty.hom_ext _ (Action.Hom.ext (FintypeCat.hom_ext _ _ fun a => hf a))

end ResIso

variable {X : Scheme.{u}} [ConnectedSpace X] {x x' : GeometricPoint X}

/-- **The change of base point `π₁(X, x̄') →ₜ* π₁(X, x̄)`** of an isomorphism `t : F_x̄ ≅ F_x̄'` of
geometric fibre functors: the inverse of conjugation by `t`. -/
public def etaleFundamentalGroupBasePointHom
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :
    EtaleFundamentalGroup X x' →ₜ* EtaleFundamentalGroup X x :=
  (etaleFundamentalGroupContinuousMulEquiv t).symm

/-- Conjugation by `t` sends `etaleFundamentalGroupBasePointHom t g` back to `g`. -/
public theorem etaleFundamentalGroupMulEquiv_basePointHom
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x')
    (g : EtaleFundamentalGroup X x') :
    etaleFundamentalGroupMulEquiv t (etaleFundamentalGroupBasePointHom t g) = g :=
  (etaleFundamentalGroupContinuousMulEquiv t).apply_symm_apply g

/-- The bijection of fibres at `x̄` and `x̄'` given by `t`, on the finite sets of the equivalences
of Tag 0BND (1). -/
public def finiteEtaleEquivalenceBasePointEquiv
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') (Y : FiniteEtaleOver X) :
    ((finiteEtaleEquivalenceOfIsGaloisCategory X x).functor.obj Y).obj.V ≃
      ((finiteEtaleEquivalenceOfIsGaloisCategory X x').functor.obj Y).obj.V :=
  ((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x).app Y ≪≫ t.app Y ≪≫
    (finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x').symm.app Y).toEquiv

/-- The bijection `finiteEtaleEquivalenceBasePointEquiv t Y` carries the action of
`etaleFundamentalGroupBasePointHom t g` on the fibre at `x̄` to the action of `g` on the fibre at
`x̄'`. -/
public theorem finiteEtaleEquivalenceBasePointEquiv_action
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') (Y : FiniteEtaleOver X)
    (g : EtaleFundamentalGroup X x')
    (a : ((finiteEtaleEquivalenceOfIsGaloisCategory X x).functor.obj Y).obj.V) :
    finiteEtaleEquivalenceBasePointEquiv t Y
        (ConcreteCategory.hom (((finiteEtaleEquivalenceOfIsGaloisCategory X x).functor.obj Y).obj.ρ
          (etaleFundamentalGroupBasePointHom t g)) a) =
      ConcreteCategory.hom (((finiteEtaleEquivalenceOfIsGaloisCategory X x').functor.obj Y).obj.ρ g)
        (finiteEtaleEquivalenceBasePointEquiv t Y a) := by
  have h := etaleFundamentalGroupMulEquiv_action t Y (etaleFundamentalGroupBasePointHom t g) a
  rw [etaleFundamentalGroupMulEquiv_basePointHom] at h
  exact (congrArg ((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x').inv.app Y) h).trans
    (ConcreteCategory.congr_hom
      ((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x').hom_inv_id_app Y) _)

/-- **Tag 0BND (1) at two base points.** Restricting the action on the fibre at `x̄` along
`π₁(X, x̄') → π₁(X, x̄)` is the action on the fibre at `x̄'`, the comparison being `t`. -/
public def finiteEtaleEquivalenceBasePointIso
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :
    (finiteEtaleEquivalenceOfIsGaloisCategory X x).functor ⋙
        ContAction.res FintypeCat.{u} (etaleFundamentalGroupBasePointHom t) ≅
      (finiteEtaleEquivalenceOfIsGaloisCategory X x').functor :=
  NatIso.ofComponents
    (fun Y => contActionResIsoMk (etaleFundamentalGroupBasePointHom t)
      (finiteEtaleEquivalenceBasePointEquiv t Y) (finiteEtaleEquivalenceBasePointEquiv_action t Y))
    (fun {Y Z} h => contActionResIsoMk_naturality (etaleFundamentalGroupBasePointHom t) _ _ _ _ _ _
      (fun a => (congrArg ((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x').inv.app Z)
        ((congrArg (t.hom.app Z)
          (ConcreteCategory.congr_hom
            ((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x).hom.naturality h) a)).trans
          (ConcreteCategory.congr_hom (t.hom.naturality h)
            ((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x).hom.app Y a)))).trans
        (ConcreteCategory.congr_hom
          ((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x').inv.naturality h)
          (t.hom.app Y ((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x).hom.app Y a)))))

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] {x x' : GeometricPoint X.1}

/-- **Tag 0DV5 (1) at two base points**: the equivalence for finite locally constant sheaves of
sets at `x̄`, followed by restriction along `π₁(X, x̄') → π₁(X, x̄)`, is the one at `x̄'`. -/
public def finiteLocallyConstantSetsEquivalenceBasePointIso
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :
    (finiteLocallyConstantSetsEquivalence B X x).functor ⋙
        ContAction.res FintypeCat.{u + 1} (etaleFundamentalGroupBasePointHom t) ≅
      (finiteLocallyConstantSetsEquivalence B X x').functor :=
  Functor.isoWhiskerLeft (finiteLocallyConstantFiniteEtaleEquivalence B X).functor
    (Functor.isoWhiskerRight (finiteEtaleEquivalenceBasePointIso t)
      (contActionUniverseEquivalence.{u, u + 1} (EtaleFundamentalGroup X.1 x')).functor)

/-- **Tag 0DV5 (1) at two base points**, with the finite continuous sets presented as a full
subcategory of all continuous sets. -/
public def finiteLocallyConstantSetsEquivalence'BasePointIso
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :
    (finiteLocallyConstantSetsEquivalence' B X x).functor ⋙
        ContinuousGSet.resIsFinite (etaleFundamentalGroupBasePointHom t) ≅
      𝟭 _ ⋙ (finiteLocallyConstantSetsEquivalence' B X x').functor :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (finiteLocallyConstantSetsEquivalence B X x).functor
      (eqToIso (finiteActionToFiniteGSet_comp_resIsFinite
        (etaleFundamentalGroupBasePointHom t))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (finiteLocallyConstantSetsEquivalenceBasePointIso B X t)
      finiteActionToFiniteGSet

/-- **The identity functor is the identity on commutative group objects**, for any braided
structure on it, in a cartesian monoidal category: its structure maps `ε`, `μ` are identities. -/
public def mapCommGrpIdIsoOfBraided.{v₁, u₁} {C : Type u₁} [Category.{v₁} C]
    (iC : CartesianMonoidalCategory C) (iB : BraidedCategory C) (i : (𝟭 C).Braided) :
    (𝟭 C).mapCommGrp ≅ 𝟭 (CommGrp C) :=
  NatIso.ofComponents (fun A => CommGrp.mkIso (Iso.refl _)
    (by
      let : (𝟭 C).Monoidal := i.toMonoidal
      let : (𝟭 C).LaxMonoidal := i.toMonoidal.toLaxMonoidal
      change (Functor.LaxMonoidal.ε (𝟭 C) ≫ (𝟭 C).map (MonObj.one (X := A.X))) ≫ 𝟙 A.X =
        MonObj.one (X := A.X)
      exact (Category.comp_id _).trans ((congrArg (· ≫ (𝟭 C).map (MonObj.one (X := A.X)))
        (toUnit_unique (Functor.LaxMonoidal.ε (𝟭 C)) (𝟙 _))).trans
          ((Category.id_comp _).trans (Functor.id_map _))))
    (by
      let : (𝟭 C).Monoidal := i.toMonoidal
      let : (𝟭 C).LaxMonoidal := i.toMonoidal.toLaxMonoidal
      have h : Functor.LaxMonoidal.μ (𝟭 C) A.X A.X = 𝟙 _ :=
        CartesianMonoidalCategory.hom_ext _ _
          ((Functor.Monoidal.μ_fst (𝟭 C) A.X A.X).trans (Category.id_comp _).symm)
          ((Functor.Monoidal.μ_snd (𝟭 C) A.X A.X).trans (Category.id_comp _).symm)
      change (Functor.LaxMonoidal.μ (𝟭 C) A.X A.X ≫ (𝟭 C).map (MonObj.mul (X := A.X))) ≫ 𝟙 A.X =
        (𝟙 A.X ⊗ₘ 𝟙 A.X) ≫ MonObj.mul (X := A.X)
      have h' : MonObj.mul (X := A.X) = (𝟙 A.X ⊗ₘ 𝟙 A.X) ≫ MonObj.mul (X := A.X) := by
        rw [MonoidalCategory.id_tensorHom_id, Category.id_comp]
      exact (Category.comp_id _).trans ((congrArg (· ≫ (𝟭 C).map (MonObj.mul (X := A.X))) h).trans
        (((Category.id_comp _).trans (Functor.id_map _)).trans h'))))
    (fun f => by
      ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- **Tag 0DV5 (2) at two base points**: the equivalence for finite locally constant abelian
sheaves at `x̄`, followed by restriction along `π₁(X, x̄') → π₁(X, x̄)`, is the one at `x̄'`. -/
public def finiteLocallyConstantAbelianSheafEquivalenceBasePointIso
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :
    (finiteLocallyConstantAbelianSheafEquivalence B X x).functor ⋙
        ContinuousGAddCommGrp.resIsFinite (etaleFundamentalGroupBasePointHom t) ≅
      𝟭 _ ⋙ (finiteLocallyConstantAbelianSheafEquivalence B X x').functor :=
  @Stacks.ConstantSheaf.finiteLocallyConstantAbelianPullbackSquare.{u, u + 1, u + 1}
    _ _ _ _ (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B X.1 X.2) _ _
    _ _ _ _ _ _
    (etaleFundamentalGroupBasePointHom t) (𝟭 _) inferInstance (𝟭 _) (fun _ hA => hA)
    (finiteLocallyConstantSetsEquivalence' B X x) (finiteLocallyConstantSetsEquivalence' B X x')
    (𝟭 _) (Iso.refl _) (𝟭 _) (Iso.refl _)
    (Functor.isoWhiskerLeft _ (mapCommGrpIdIsoOfBraided _ _ _) ≪≫ Functor.rightUnitor _ ≪≫
      (Functor.leftUnitor _).symm)
    (finiteLocallyConstantSetsEquivalence'BasePointIso B X t)

end Stacks.EtaleCohomology

end
