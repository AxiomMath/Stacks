module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseEtaleSheafTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafStalkLinear
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparisonNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationStalkPairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleBalancedTensor

/-!
# Stalks of tensor pairings of lisse sheaves

Let `μ : P × Q → R` be a `π₁(X, x̄)`-equivariant `Λ`-bilinear map of finite continuous modules
over a finite commutative ring `Λ`, and `ℱ_P ⊗ ℱ_Q ⟶ ℱ_R` the morphism of sheaves on Mathlib's
small étale site it defines (`Stacks.EtaleCohomology.lisseEtaleSheafTensorHom`). Along a path `t`
from a geometric point `s̄` to `x̄`, the stalk of `ℱ_P` at `s̄` is `P`
(`Stacks.EtaleCohomology.lisseEtaleSheafStalkCounit`, a bijection), and under these
identifications the stalk of the morphism is `μ`: the germ of `a ⊗ b` goes to `μ` of the germs.
Consequently the morphism is an isomorphism as soon as every element of `R` is a value of `μ` and
`P ⊗_Λ Q` has at most as many elements as `R`, which is the case of a perfect multiplication of
free modules of rank one.

## Main definitions

* `Stacks.EtaleCohomology.lisseEtaleSheafStalkCounit`: the stalk of `ℱ_P` at `s̄` is `P`, as sets.

## Main results

* `Stacks.EtaleCohomology.lisseEtaleSheafStalkCounit_tensorHom`: on stalks the morphism
  `ℱ_P ⊗ ℱ_Q ⟶ ℱ_R` is `μ`.
* `Stacks.EtaleCohomology.isIso_lisseEtaleSheafTensorHom`: it is an isomorphism when `μ` is
  surjective on pure products and `#(P ⊗ Q) ≤ #R`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
  Stacks.ConstantSheaf Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

/-- Limits of the size of the site in the large-universe module category. -/
local instance lisseEtaleSheafTensorStalk_hasLimitsOfSize (Λ : Type) [Ring Λ] :
    HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, 0}

/-- Colimits of the size of the site in the large-universe module category. -/
local instance lisseEtaleSheafTensorStalk_hasColimitsOfSize (Λ : Type) [Ring Λ] :
    HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  ModuleCat.hasColimitsOfSize.{u + 1, 0, u, u} Λ

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type) [CommRing Λ] [Finite Λ] {s : GeometricPoint X.1}
  (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)

/-- **The stalk at `s̄` of `ℱ_P` on Mathlib's small étale site is `P`**, as sets, along a path `t`
from `s̄` to `x̄`: the comparison of the stalks of the two small étale sites followed by the
counit of Tag 0DV5 (`Stacks.EtaleCohomology.finiteLocallyConstantAbelianStalkCounit`). -/
def lisseEtaleSheafStalkCounit
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (z : (Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj
      ((lisseEtaleSheaf B X x Λ).obj P)) :
    P.obj.obj.obj.V :=
  finiteLocallyConstantAbelianStalkCounit B X t
    ((finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj P)
    (lisseSheafForget₂StalkAddEquiv B X x Λ s P
      ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ s).hom.app ((lisseSheaf B X x Λ).obj P) z))

/-- `lisseEtaleSheafStalkCounit` is a bijection. -/
theorem lisseEtaleSheafStalkCounit_bijective
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    Function.Bijective (lisseEtaleSheafStalkCounit B X x Λ t P) :=
  (finiteLocallyConstantAbelianStalkCounit_bijective B X t _).comp
    ((lisseSheafForget₂StalkAddEquiv B X x Λ s P).bijective.comp
      ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ s).app
        ((lisseSheaf B X x Λ).obj P)).toLinearEquiv.bijective)

/-- The germ of the section of the small étale sheaf corresponding to `a` is the image under the
inverse comparison of the germ of `a` at `s̄` on Mathlib's site. -/
private theorem toPresheafFiber_unit_eq_inv_app (B : BigEtaleSite.{u}) (X : B.Scheme)
    (Λ : Type) [CommRing Λ] (s : GeometricPoint X.1)
    (F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ))
    (U : (geometricPointFiber B X.1 X.2 s).Elements) (a : F.obj.obj (op U.1)) :
    (Scheme.pointSmallEtale s.hom).toPresheafFiber
        ((SmallEtale.toEtaleSite B X.1 X.2).obj U.1)
        ((toEtaleSiteFiberIso B X.1 X.2 s).inv.app U.1 U.2)
        ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).functor.obj F).obj
        ((((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).unit.app F).hom.app
          (op U.1)).hom a) =
      (sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ s).inv.app F
        ((geometricSitePoint B X s).toPresheafFiber U.1 U.2 F.obj a) :=
  (ConcreteCategory.congr_hom
    (toPresheafFiber_sheafEquivCompSheafFiberIso_inv B X Λ s F U.1 U.2) a).symm

/-- `lisseEtaleSheafStalkCounit` on the germ of a section coming from the small étale category of
Stacks 021B. -/
theorem lisseEtaleSheafStalkCounit_germ
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (U : (geometricPointFiber B X.1 X.2 s).Elements)
    (a : ((lisseSheaf B X x Λ).obj P).obj.obj (op U.1)) :
    lisseEtaleSheafStalkCounit B X x Λ t P
        ((Scheme.pointSmallEtale s.hom).toPresheafFiber
          ((SmallEtale.toEtaleSite B X.1 X.2).obj U.1)
          ((toEtaleSiteFiberIso B X.1 X.2 s).inv.app U.1 U.2)
          ((lisseEtaleSheaf B X x Λ).obj P).obj
          ((((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).unit.app
            ((lisseSheaf B X x Λ).obj P)).hom.app (op U.1)).hom a)) =
      finiteLocallyConstantAbelianStalkCounit B X t
        ((finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj P)
        (abelianEtaleStalkGerm.{u, u + 1} B X.1 X.2 s
          ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj
            ((finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj P)).obj
          U a) := by
  let F := (lisseSheaf B X x Λ).obj P
  let e := sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ s
  let c := finiteLocallyConstantAbelianStalkCounit B X t
    ((finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj P)
  have h1 := toPresheafFiber_unit_eq_inv_app B X Λ s F U a
  have h2 : e.hom.app F (e.inv.app F ((geometricSitePoint B X s).toPresheafFiber U.1 U.2 F.obj a)) =
      (geometricSitePoint B X s).toPresheafFiber U.1 U.2 F.obj a :=
    ConcreteCategory.congr_hom (e.inv_hom_id_app F) _
  have h3 : lisseSheafForget₂StalkAddEquiv B X x Λ s P
      ((geometricSitePoint B X s).toPresheafFiber U.1 U.2 F.obj a) =
      abelianEtaleStalkGerm.{u, u + 1} B X.1 X.2 s (lisseSheafAbelian B X x Λ P).obj U a :=
    ConcreteCategory.congr_hom (ι_preservesColimitIso_hom
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
      ((CategoryOfElements.π (geometricPointFiber B X.1 X.2 s)).op ⋙ F.obj) (op U)) a
  exact (congrArg (fun z => c (lisseSheafForget₂StalkAddEquiv B X x Λ s P (e.hom.app F z)))
    h1).trans
    ((congrArg (fun z => c (lisseSheafForget₂StalkAddEquiv B X x Λ s P z)) h2).trans
      (congrArg c h3))

omit [ConnectedSpace X.1] [Finite Λ] in
/-- A germ at `s̄` on Mathlib's site whose comparison is the germ of a section `a` over an object
of the small étale category of Stacks 021B is the germ of the section corresponding to `a`. -/
theorem eq_toPresheafFiber_unit_of_sheafEquivCompSheafFiberIso_hom
    (F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ))
    (z : (Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj
      ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).functor.obj F))
    (U : (geometricPointFiber B X.1 X.2 s).Elements) (a : F.obj.obj (op U.1))
    (h : (geometricSitePoint B X s).toPresheafFiber U.1 U.2 F.obj a =
      (sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ s).hom.app F z) :
    z = (Scheme.pointSmallEtale s.hom).toPresheafFiber
        ((SmallEtale.toEtaleSite B X.1 X.2).obj U.1)
        ((toEtaleSiteFiberIso B X.1 X.2 s).inv.app U.1 U.2)
        ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).functor.obj F).obj
        ((((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).unit.app F).hom.app
          (op U.1)).hom a) := by
  let e := sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ s
  have h0 : e.inv.app F (e.hom.app F z) = z := ConcreteCategory.congr_hom (e.hom_inv_id_app F) z
  exact h0.symm.trans ((congrArg (e.inv.app F) h.symm).trans
    (toPresheafFiber_unit_eq_inv_app B X Λ s F U a).symm)

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  AlgebraicGeometry.moduleCat_preservesColimits_tensorLeft
  AlgebraicGeometry.moduleCat_preservesColimits_tensorRight

variable {P Q R : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
  (μ : P.obj.obj.obj.V →ₗ[Λ] Q.obj.obj.obj.V →ₗ[Λ] R.obj.obj.obj.V)
  (hμ : ∀ (g : EtaleFundamentalGroup X.1 x) (a : P.obj.obj.obj.V) (b : Q.obj.obj.obj.V),
    μ ((P.obj.obj.obj.ρ g).asHom.hom a) ((Q.obj.obj.obj.ρ g).asHom.hom b) =
      (R.obj.obj.obj.ρ g).asHom.hom (μ a b))

/-- **On stalks, the morphism `ℱ_P ⊗ ℱ_Q ⟶ ℱ_R` attached to `μ` is `μ`**: under the
identifications `lisseEtaleSheafStalkCounit` of the stalks at `s̄` with `P`, `Q`, `R`, the image of
`z₁ ⊗ z₂` is `μ` of the images. -/
theorem lisseEtaleSheafStalkCounit_tensorHom
    (z₁ : (Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj
      ((lisseEtaleSheaf B X x Λ).obj P))
    (z₂ : (Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj
      ((lisseEtaleSheaf B X x Λ).obj Q)) :
    lisseEtaleSheafStalkCounit B X x Λ t R
        ((Functor.LaxMonoidal.μ ((Scheme.pointSmallEtale s.hom).sheafFiber
            (A := ModuleCat.{u + 1} Λ)) _ _ ≫
          ((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
            (lisseEtaleSheafTensorHom B X x Λ μ hμ)).hom (z₁ ⊗ₜ z₂)) =
      μ (lisseEtaleSheafStalkCounit B X x Λ t P z₁)
        (lisseEtaleSheafStalkCounit B X x Λ t Q z₂) := by
  let e := sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ s
  obtain ⟨U, a, b, ha, hb⟩ := exists_toPresheafFiber_eq₂ B X Λ ((lisseSheaf B X x Λ).obj P).obj
    ((lisseSheaf B X x Λ).obj Q).obj (e.hom.app _ z₁) (e.hom.app _ z₂)
  have e1 := eq_toPresheafFiber_unit_of_sheafEquivCompSheafFiberIso_hom B X Λ
    ((lisseSheaf B X x Λ).obj P) z₁ U a ha
  have e2 := eq_toPresheafFiber_unit_of_sheafEquivCompSheafFiberIso_hom B X Λ
    ((lisseSheaf B X x Λ).obj Q) z₂ U b hb
  subst e1 e2
  have hT := Sheaf.sheafFiber_tensorDesc_tmul (Scheme.pointSmallEtale s.hom)
    (lisseEtaleSheafBilinear B X x Λ μ hμ)
    (fun f a b => lisseEtaleSheafBilinear_naturality B X x Λ μ hμ f a b)
    ((SmallEtale.toEtaleSite B X.1 X.2).obj U.1) ((toEtaleSiteFiberIso B X.1 X.2 s).inv.app U.1 U.2)
    ((((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).unit.app
      ((lisseSheaf B X x Λ).obj P)).hom.app (op U.1)).hom a)
    ((((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).unit.app
      ((lisseSheaf B X x Λ).obj Q)).hom.app (op U.1)).hom b)
  refine (congrArg (lisseEtaleSheafStalkCounit B X x Λ t R) hT).trans ?_
  refine (congrArg (fun w => lisseEtaleSheafStalkCounit B X x Λ t R
    ((Scheme.pointSmallEtale s.hom).toPresheafFiber ((SmallEtale.toEtaleSite B X.1 X.2).obj U.1)
      ((toEtaleSiteFiberIso B X.1 X.2 s).inv.app U.1 U.2) ((lisseEtaleSheaf B X x Λ).obj R).obj w))
    (lisseEtaleSheafBilinear_unit B X x Λ μ hμ (op U.1) a b)).trans ?_
  refine (lisseEtaleSheafStalkCounit_germ B X x Λ t R U _).trans ?_
  refine (finiteLocallyConstantAbelianStalkCounit_germ_pairing B X t
    ((finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj P)
    ((finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj Q)
    ((finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj R)
    (finiteTypeContinuousModuleBilinearAddHom Λ μ) hμ U a b).trans ?_
  exact congrArg₂ (fun p q => μ p q) (lisseEtaleSheafStalkCounit_germ B X x Λ t P U a).symm
    (lisseEtaleSheafStalkCounit_germ B X x Λ t Q U b).symm

omit t in
/-- **The morphism `ℱ_P ⊗ ℱ_Q ⟶ ℱ_R` attached to `μ` is an isomorphism** when every element of `R`
is a value of `μ` and `P ⊗_Λ Q` has at most as many elements as `R` (for instance when `μ` is a
perfect multiplication of free modules of rank one). -/
theorem isIso_lisseEtaleSheafTensorHom (hsurj : ∀ r : R.obj.obj.obj.V, ∃ p q, μ p q = r)
    (hcard : Nat.card (TensorProduct Λ P.obj.obj.obj.V Q.obj.obj.obj.V) ≤
      Nat.card R.obj.obj.obj.V) :
    IsIso (lisseEtaleSheafTensorHom B X x Λ μ hμ) := by
  refine isIso_of_forall_isIso_etaleModuleSheafFiber_map _ fun s => ?_
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso (X := X.1) (x := s) (x' := x)
  let Φ := (Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)
  let m := Functor.LaxMonoidal.μ Φ ((lisseEtaleSheaf B X x Λ).obj P)
    ((lisseEtaleSheaf B X x Λ).obj Q) ≫ Φ.map (lisseEtaleSheafTensorHom B X x Λ μ hμ)
  have : Module.Finite Λ P.obj.obj.obj.V := P.property
  have : Module.Finite Λ Q.obj.obj.obj.V := Q.property
  have : Module.Finite Λ R.obj.obj.obj.V := R.property
  have : Finite (TensorProduct Λ P.obj.obj.obj.V Q.obj.obj.obj.V) := Module.finite_of_finite Λ
  have : Finite R.obj.obj.obj.V := Module.finite_of_finite Λ
  let eP := (lisseEtaleSheafModuleFiberIso B X x Λ t P).toLinearEquiv
  let eQ := (lisseEtaleSheafModuleFiberIso B X x Λ t Q).toLinearEquiv
  let eR := (lisseEtaleSheafModuleFiberIso B X x Λ t R).toLinearEquiv
  let eT := TensorProduct.congr eP eQ
  have : Finite ((Φ.obj ((lisseEtaleSheaf B X x Λ).obj P) ⊗
      Φ.obj ((lisseEtaleSheaf B X x Λ).obj Q) : ModuleCat.{u + 1} Λ)) :=
    Finite.of_equiv _ eT.toEquiv.symm
  have hs : Function.Surjective m.hom := fun z => by
    obtain ⟨p, q, hpq⟩ := hsurj (lisseEtaleSheafStalkCounit B X x Λ t R z)
    obtain ⟨z₁, rfl⟩ := (lisseEtaleSheafStalkCounit_bijective B X x Λ t P).2 p
    obtain ⟨z₂, rfl⟩ := (lisseEtaleSheafStalkCounit_bijective B X x Λ t Q).2 q
    exact ⟨z₁ ⊗ₜ z₂, (lisseEtaleSheafStalkCounit_bijective B X x Λ t R).1
      ((lisseEtaleSheafStalkCounit_tensorHom B X x Λ t μ hμ z₁ z₂).trans hpq)⟩
  have hb : Function.Bijective m.hom := hs.bijective_of_nat_card_le
    (((Nat.card_congr eT.toEquiv).trans_le hcard).trans_eq (Nat.card_congr eR.toEquiv).symm)
  have : IsIso m := (ConcreteCategory.isIso_iff_bijective m).2 hb
  exact IsIso.of_isIso_comp_left (Functor.LaxMonoidal.μ Φ ((lisseEtaleSheaf B X x Λ).obj P)
    ((lisseEtaleSheaf B X x Λ).obj Q)) _

end Stacks.EtaleCohomology
