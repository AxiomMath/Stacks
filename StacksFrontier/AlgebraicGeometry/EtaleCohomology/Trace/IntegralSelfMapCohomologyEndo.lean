module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSmoothModelNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GlobalSectionsEndomorphismComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionFrobeniusTrace
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusSingleCompatible

/-!
# Pullback along an integral self-map on the cohomology of a sheaf

For an integral morphism `φ : Y ⟶ Y` of schemes and a sheaf `N` of `Λ`-modules on `Y_étale`
with a map `α : N ⟶ φ_* N` (a `φ`-linearization: for `φ` an automorphism and `α` adjoint to an
isomorphism `φ^{-1} N ≅ N`, this is an equivariant structure), the composite

`H^i(Y, N) ⟶ H^i(Y, φ_* N) ≅ H^i(Y, N)`

of `H^i(Y, α)` and of `Stacks.EtaleCohomology.integralDirectImageCohomologyIso` (`φ_*` is exact,
being integral) is the pullback action of `φ` on `H^i(Y, N)`
(`Stacks.EtaleCohomology.integralSelfMapCohomologyEndo`).

The main results compare these actions along an integral morphism `g : Y ⟶ Z` intertwining two
self-maps, `φ_Y ≫ g = g ≫ φ_Z`: the identification `H^i(Z, g_* N) ≅ H^i(Y, N)` carries the action
of `φ_Z` on `g_* N`, with linearization `g_* α` followed by `g_* φ_{Y,*} ≅ φ_{Z,*} g_*`, to the
action of `φ_Y` on `N` (`Stacks.EtaleCohomology.integralSelfMapCohomologyEndo_directImage`).  The
input is the transitivity of `integralDirectImageCohomologyIso` along a composite of integral
morphisms (`Stacks.EtaleCohomology.integralDirectImageCohomologyIso_hom_comp`), which is the
coherence triangle of composition comparisons of derived functors together with the cocycle
identity `Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso_comp`.

## Main definitions

* `Stacks.EtaleCohomology.integralSelfMapCohomologyEndo`.

## Main results

* `Stacks.EtaleCohomology.integralDirectImageCohomologyIso_hom_comp`.
* `Stacks.EtaleCohomology.integralSelfMapCohomologyEndo_naturality`.
* `Stacks.EtaleCohomology.integralSelfMapCohomologyEndo_directImage`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w₁ w₂ v₁ v₂ v₃ u₁ u₂ u₃ u r

namespace Stacks.EtaleCohomology

/-! ### The two composition comparisons for an exact second factor -/

section Exact

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{w₂} C]
  [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C) [F.Additive] [G.Additive] [H.Additive]
  [F.PreservesInjectiveObjects] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (e : F ⋙ G ≅ H)

/-- **The two composition comparisons agree**: for `G` exact and `F` preserving injectives, the
comparison `RH ≅ RF ⋙ RG` of `Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso` is the
inverse of the comparison `RF ⋙ RG ≅ RH` of
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact`.  Both are characterized by the
derived-functor units. -/
theorem rightDerivedFunctorPlusCompIsoOfIso_inv_eq :
    (rightDerivedFunctorPlusCompIsoOfIso F G H e).inv =
      (Functor.rightDerivedFunctorPlusCompIsoOfExact F G H e).hom := by
  refine Iso.inv_ext ?_
  refine Functor.rightDerived_ext H.rightDerivedFunctorPlus H.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso A) _ _ _ (NatTrans.ext (funext fun K => ?_))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app]
  rw [← Category.assoc, unit_comp_rightDerivedFunctorPlusCompIsoOfIso_hom, Category.assoc,
    Category.assoc, Functor.rightDerivedFunctorPlusCompIsoOfExact_fac, ← Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

end Exact

/-- Inverting a commutative square of isomorphisms. -/
private lemma inv_comp_inv_of_hom_comp_hom {D : Type*} [Category D] {P Q R S : D}
    (e₁ : P ≅ Q) (e₂ : Q ≅ S) (e₃ : P ≅ R) (e₄ : R ≅ S) (h : e₁.hom ≫ e₂.hom = e₃.hom ≫ e₄.hom) :
    e₂.inv ≫ e₁.inv = e₄.inv ≫ e₃.inv := by
  rw [← Iso.trans_inv, ← Iso.trans_inv]
  exact congrArg Iso.inv (Iso.ext h)

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ]

/-! ### The coherence triangle for a composite of morphisms -/

section Triangle

/-- **The underived triangle for a composite `m = f ≫ g`**: the identifications
`Γ(Z, m_* -) ≅ Γ(X, -)`, `Γ(Y, f_* -) ≅ Γ(X, -)`, `Γ(Z, g_* -) ≅ Γ(Y, -)` and
`f_* ⋙ g_* ≅ m_*` are compatible. -/
theorem etaleModuleDirectImageCompGlobalSections_comp_triangle {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (m : X ⟶ Z) (hm : m = f ≫ g) (N : EtaleModules.{u, r} Λ X) :
    (etaleModuleDirectImageCompGlobalSections.{u, r} Λ m).inv.app N ≫
        (etaleModuleGlobalSections.{u, r} Λ Z).map
          ((etaleModuleDirectImageComp.{u, r} Λ f g m hm).inv.app N) =
      (etaleModuleDirectImageCompGlobalSections.{u, r} Λ f).inv.app N ≫
        (etaleModuleDirectImageCompGlobalSections.{u, r} Λ g).inv.app
          ((etaleModuleDirectImage.{u, r} Λ f).obj N) := by
  refine Sheaf.hom_ext_of_ΓRes fun U => ?_
  have h4 := etaleModuleDirectImageCompGlobalSections_inv_app_comp_ΓRes Λ g
    ((etaleModuleDirectImage.{u, r} Λ f).obj N) U
  have h5 := etaleModuleDirectImageCompGlobalSections_inv_app_comp_ΓRes Λ f N
    (op ((smallEtaleBaseChange g).obj U.unop))
  rw [Category.assoc, Category.assoc, Sheaf.ΓRes_naturality,
    etaleModuleDirectImageCompGlobalSections_inv_app_comp_ΓRes_assoc]
  refine Eq.trans ?_ (congrArg (_ ≫ ·) h4).symm
  refine Eq.trans ?_ h5.symm
  rw [etaleModuleDirectImageComp_inv_app_hom_app]
  exact Sheaf.ΓRes_map N _

/-- **The derived triangle for a composite `m = f ≫ g`**: the comparisons
`RΓ(X, -) ≅ RΓ(Z, Rm_* -)`, `RΓ(X, -) ≅ RΓ(Y, Rf_* -)`, `RΓ(Y, -) ≅ RΓ(Z, Rg_* -)` and
`Rm_* ≅ Rf_* ⋙ Rg_*` are compatible. -/
theorem etaleModuleDerivedGlobalSectionsCompIso_comp_triangle {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (m : X ⟶ Z) (hm : m = f ≫ g)
    (M : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)) :
    (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ m).hom.app M ≫
        (etaleModuleDerivedGlobalSections.{u, r} Λ Z).map
          ((etaleModuleDerivedDirectImageComp.{u, r} Λ f g m hm).hom.app M) =
      (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ f).hom.app M ≫
        (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ g).hom.app
          ((etaleModuleDerivedDirectImage.{u, r} Λ f).obj M) :=
  rightDerivedFunctorPlusCompIsoOfIso_triangle
    (etaleModuleDirectImageCompGlobalSections.{u, r} Λ f)
    (etaleModuleDirectImageCompGlobalSections.{u, r} Λ g)
    (etaleModuleDirectImageCompGlobalSections.{u, r} Λ m)
    (etaleModuleDirectImageComp.{u, r} Λ f g m hm)
    (etaleModuleDirectImageCompGlobalSections_comp_triangle Λ f g m hm) M

end Triangle

/-! ### Transitivity of `H^i(B, g_* -) ≅ H^i(A, -)` -/

section Transitivity

/-- `integralDirectImageCohomologyIso` unfolded. -/
lemma integralDirectImageCohomologyIso_hom_eq {A B : Scheme.{u}} (g : A ⟶ B) [IsIntegralHom g]
    (H : EtaleModules.{u, r} Λ A) (i : ℤ) :
    (integralDirectImageCohomologyIso Λ g H i).hom =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).map
        ((etaleModuleDerivedGlobalSections.{u, r} Λ B).map
            ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
              (etaleModuleDirectImage.{u, r} Λ g) 0).hom.app H) ≫
          (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ g).inv.app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj H)) :=
  rfl

/-- **Transitivity of `H^i(B, g_* -) ≅ H^i(A, -)`** along a composite `m = a ≫ b` of integral
morphisms: `H^i(Z, b_* a_* M) ≅ H^i(Y, a_* M) ≅ H^i(X, M)` is `H^i(Z, b_* a_* M ≅ m_* M)`
followed by `H^i(Z, m_* M) ≅ H^i(X, M)`. -/
theorem integralDirectImageCohomologyIso_hom_comp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (m : X ⟶ Z) (hm : m = a ≫ b) [IsIntegralHom a] [IsIntegralHom b] [IsIntegralHom m]
    (M : EtaleModules.{u, r} Λ X) (i : ℤ) :
    (integralDirectImageCohomologyIso Λ b ((etaleModuleDirectImage.{u, r} Λ a).obj M) i).hom ≫
        (integralDirectImageCohomologyIso Λ a M i).hom =
      ((etaleModuleGlobalSections.{u, r} Λ Z).rightDerivedPlus i).map
          ((etaleModuleDirectImageComp.{u, r} Λ a b m hm).hom.app M) ≫
        (integralDirectImageCohomologyIso Λ m M i).hom := by
  obtain ⟨_, _⟩ := etaleModuleDirectImage_exact_of_isIntegralHom Λ a
  obtain ⟨_, _⟩ := etaleModuleDirectImage_exact_of_isIntegralHom Λ b
  obtain ⟨_, _⟩ := etaleModuleDirectImage_exact_of_isIntegralHom Λ m
  let RZ := etaleModuleDerivedGlobalSections.{u, r} Λ Z
  let RY := etaleModuleDerivedGlobalSections.{u, r} Λ Y
  let sX := DerivedCategory.Plus.singleFunctor (EtaleModules.{u, r} Λ X) 0
  let eSa := Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
    (etaleModuleDirectImage.{u, r} Λ a) 0
  let eSb := Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
    (etaleModuleDirectImage.{u, r} Λ b) 0
  let eSm := Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
    (etaleModuleDirectImage.{u, r} Λ m) 0
  let cIa := etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ a
  let cIb := etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ b
  let cIm := etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ m
  have n1 := cIb.inv.naturality (eSa.hom.app M)
  dsimp only [Functor.comp_map] at n1
  have T' : cIb.inv.app ((etaleModuleDerivedDirectImage.{u, r} Λ a).obj (sX.obj M)) ≫
      cIa.inv.app (sX.obj M) =
      RZ.map ((etaleModuleDerivedDirectImageComp.{u, r} Λ a b m hm).inv.app (sX.obj M)) ≫
        cIm.inv.app (sX.obj M) := by
    have T := etaleModuleDerivedGlobalSectionsCompIso_comp_triangle Λ a b m hm (sX.obj M)
    have := inv_comp_inv_of_hom_comp_hom (cIm.app (sX.obj M))
      (RZ.mapIso ((etaleModuleDerivedDirectImageComp.{u, r} Λ a b m hm).app (sX.obj M)))
      (cIa.app (sX.obj M)) (cIb.app ((etaleModuleDerivedDirectImage.{u, r} Λ a).obj (sX.obj M)))
      T
    exact this.symm
  have hD : (etaleModuleDerivedDirectImageComp.{u, r} Λ a b m hm).inv.app (sX.obj M) =
      (Functor.rightDerivedFunctorPlusCompIsoOfExact (etaleModuleDirectImage.{u, r} Λ a)
        (etaleModuleDirectImage.{u, r} Λ b) (etaleModuleDirectImage.{u, r} Λ m)
        (etaleModuleDirectImageComp.{u, r} Λ a b m hm)).hom.app (sX.obj M) :=
    congrArg (fun t => NatTrans.app t (sX.obj M))
      (rightDerivedFunctorPlusCompIsoOfIso_inv_eq (etaleModuleDirectImage.{u, r} Λ a)
        (etaleModuleDirectImage.{u, r} Λ b) (etaleModuleDirectImage.{u, r} Λ m)
        (etaleModuleDirectImageComp.{u, r} Λ a b m hm))
  have ES := Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso_comp
    (etaleModuleDirectImage.{u, r} Λ a) (etaleModuleDirectImage.{u, r} Λ b)
    (etaleModuleDirectImage.{u, r} Λ m) (etaleModuleDirectImageComp.{u, r} Λ a b m hm) M
  have key : RZ.map (eSb.hom.app ((etaleModuleDirectImage.{u, r} Λ a).obj M)) ≫
          cIb.inv.app ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleDirectImage.{u, r} Λ a).obj M)) ≫
          RY.map (eSa.hom.app M) ≫ cIa.inv.app (sX.obj M) =
        RZ.map ((DerivedCategory.Plus.singleFunctor _ 0).map
          ((etaleModuleDirectImageComp.{u, r} Λ a b m hm).hom.app M)) ≫
          RZ.map (eSm.hom.app M) ≫ cIm.inv.app (sX.obj M) := by
    calc RZ.map (eSb.hom.app ((etaleModuleDirectImage.{u, r} Λ a).obj M)) ≫
            cIb.inv.app ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((etaleModuleDirectImage.{u, r} Λ a).obj M)) ≫
            RY.map (eSa.hom.app M) ≫ cIa.inv.app (sX.obj M)
        = RZ.map (eSb.hom.app ((etaleModuleDirectImage.{u, r} Λ a).obj M)) ≫
            RZ.map ((etaleModuleDerivedDirectImage.{u, r} Λ b).map (eSa.hom.app M)) ≫
            cIb.inv.app ((etaleModuleDerivedDirectImage.{u, r} Λ a).obj (sX.obj M)) ≫
            cIa.inv.app (sX.obj M) := by
          rw [reassoc_of% n1]
      _ = RZ.map (eSb.hom.app ((etaleModuleDirectImage.{u, r} Λ a).obj M) ≫
            (etaleModuleDerivedDirectImage.{u, r} Λ b).map (eSa.hom.app M) ≫
            (etaleModuleDerivedDirectImageComp.{u, r} Λ a b m hm).inv.app (sX.obj M)) ≫
            cIm.inv.app (sX.obj M) := by
          rw [T', Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
      _ = RZ.map ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((etaleModuleDirectImageComp.{u, r} Λ a b m hm).hom.app M) ≫ eSm.hom.app M) ≫
            cIm.inv.app (sX.obj M) := by
          rw [hD, ES]
      _ = _ := by rw [Functor.map_comp, Category.assoc]
  let Hm := DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i
  exact (Hm.map_comp _ _).symm.trans ((congrArg Hm.map
    ((Category.assoc _ _ _).trans key)).trans (Hm.map_comp _ _))

end Transitivity

/-! ### The pullback action of an integral self-map -/

section Endo

variable {Y : Scheme.{u}} (φ : Y ⟶ Y) [IsIntegralHom φ]

/-- **The pullback action of an integral self-map `φ` of `Y` on `H^i(Y, N)`** for a sheaf `N`
with a linearization `α : N ⟶ φ_* N`: `H^i(Y, α)` followed by `H^i(Y, φ_* N) ≅ H^i(Y, N)`. -/
def integralSelfMapCohomologyEndo (N : EtaleModules.{u, r} Λ Y)
    (α : N ⟶ (etaleModuleDirectImage.{u, r} Λ φ).obj N) (i : ℤ) :
    ((etaleModuleGlobalSections.{u, r} Λ Y).rightDerivedPlus i).obj N ⟶
      ((etaleModuleGlobalSections.{u, r} Λ Y).rightDerivedPlus i).obj N :=
  ((etaleModuleGlobalSections.{u, r} Λ Y).rightDerivedPlus i).map α ≫
    (integralDirectImageCohomologyIso Λ φ N i).hom

/-- **The pullback action is natural in the linearized sheaf.** -/
theorem integralSelfMapCohomologyEndo_naturality {N N' : EtaleModules.{u, r} Λ Y}
    (α : N ⟶ (etaleModuleDirectImage.{u, r} Λ φ).obj N)
    (α' : N' ⟶ (etaleModuleDirectImage.{u, r} Λ φ).obj N') (ψ : N ⟶ N')
    (h : α ≫ (etaleModuleDirectImage.{u, r} Λ φ).map ψ = ψ ≫ α') (i : ℤ) :
    integralSelfMapCohomologyEndo Λ φ N α i ≫
        ((etaleModuleGlobalSections.{u, r} Λ Y).rightDerivedPlus i).map ψ =
      ((etaleModuleGlobalSections.{u, r} Λ Y).rightDerivedPlus i).map ψ ≫
        integralSelfMapCohomologyEndo Λ φ N' α' i := by
  have hn := integralDirectImageCohomologyIso_hom_naturality.{u, r} Λ φ ψ i
  rw [integralSelfMapCohomologyEndo, integralSelfMapCohomologyEndo, Category.assoc, ← hn,
    ← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc]

/-- **The pullback action along a direct image.**  For an integral `g : Y ⟶ Z` and integral
self-maps with `φ_Y ≫ g = g ≫ φ_Z`, the identification `H^i(Z, g_* N) ≅ H^i(Y, N)` carries the
action of `φ_Z` on `g_* N`, linearized by `g_* α` followed by `g_* φ_{Y,*} ⟶ φ_{Z,*} g_*`, to
the action of `φ_Y` on `N` linearized by `α`. -/
theorem integralSelfMapCohomologyEndo_directImage {Z : Scheme.{u}} (g : Y ⟶ Z) [IsIntegralHom g]
    (φZ : Z ⟶ Z) [IsIntegralHom φZ] (e₁ : φ ≫ g = g ≫ φZ) (N : EtaleModules.{u, r} Λ Y)
    (α : N ⟶ (etaleModuleDirectImage.{u, r} Λ φ).obj N) (i : ℤ) :
    integralSelfMapCohomologyEndo Λ φZ ((etaleModuleDirectImage.{u, r} Λ g).obj N)
        ((etaleModuleDirectImage.{u, r} Λ g).map α ≫
          (directImageTwistTransfer Λ g φ φZ e₁).app N) i ≫
        (integralDirectImageCohomologyIso Λ g N i).hom =
      (integralDirectImageCohomologyIso Λ g N i).hom ≫ integralSelfMapCohomologyEndo Λ φ N α i := by
  have G1 := integralDirectImageCohomologyIso_hom_comp Λ φ g (φ ≫ g) rfl N i
  have G2 := integralDirectImageCohomologyIso_hom_comp Λ g φZ (φ ≫ g) e₁ N i
  have hn := integralDirectImageCohomologyIso_hom_naturality.{u, r} Λ g α i
  let R := (etaleModuleGlobalSections.{u, r} Λ Z).rightDerivedPlus i
  have hc : R.map ((etaleModuleDirectImageComp.{u, r} Λ g φZ (φ ≫ g) e₁).inv.app N) ≫
      R.map ((etaleModuleDirectImageComp.{u, r} Λ g φZ (φ ≫ g) e₁).hom.app N) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simp only [integralSelfMapCohomologyEndo, directImageTwistTransfer, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [G2, reassoc_of% hc, ← reassoc_of% hn, G1]

end Endo

end Stacks.EtaleCohomology

end
