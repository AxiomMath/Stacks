module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCoefficientExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparisonNaturality

/-!
# The stalks of a lisse sheaf

Let `X` be a connected scheme of a big étale site with a geometric point `x̄`, `Λ` a finite ring
and `P` a finite `Λ`-module with a continuous action of `π₁(X, x̄)`. Once a path `t` from a
geometric point `s̄` to `x̄` is chosen, the stalk at `s̄` of the lisse sheaf `ℱ_P` of Tag 0DV5 (3)
is `P`, as abelian groups, and an endomorphism `a` of `s̄` acts on it (Tag 04FN) through the
element of `π₁(X, x̄)` that `t` transports the automorphism "precompose with `a`" of the fibre
functor at `s̄` to. This is
`Stacks.EtaleCohomology.representationLevelStalkIso_geometricPointStalkMap`
for an arbitrary module in place of a level of `ℤ_ℓ^r`.

## Main definitions

* `Stacks.EtaleCohomology.lisseSheafStalkAddEquiv`: the stalk of `ℱ_P` at `s̄` is `P`, as abelian
  groups.
* `Stacks.EtaleCohomology.lisseEtaleSheafFiberIso`: over `ℤ/m`, the stalk of `ℱ_P` on Mathlib's
  small étale site is `P`, as `ℤ/m`-modules.

## Main results

* `Stacks.EtaleCohomology.lisseSheafStalkAddEquiv_geometricPointStalkMap`: the action of an
  endomorphism of `s̄` on the stalk is the action of an element of `π₁(X, x̄)`.
* `Stacks.EtaleCohomology.sheafFiber_comp_lisseEtaleSheafFiberIso_hom`: the same on Mathlib's
  small étale site.

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] ModuleCat.hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type) [CommRing Λ] [Finite Λ]

/-- The underlying additive equivalence of an isomorphism of finite continuous modules. -/
def finiteTypeContinuousModuleAddEquiv {G : Type (u + 1)} [Group G] [TopologicalSpace G]
    {P P' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G} (e : P ≅ P') :
    P.obj.obj.obj.V ≃+ P'.obj.obj.obj.V where
  toFun := e.hom.hom.hom.hom.hom.hom
  invFun := e.inv.hom.hom.hom.hom.hom
  left_inv v := congrArg (fun φ => φ.hom.hom.hom.hom.hom v) e.hom_inv_id
  right_inv v := congrArg (fun φ => φ.hom.hom.hom.hom.hom v) e.inv_hom_id
  map_add' := map_add _

omit [Finite Λ] in
/-- The underlying additive equivalence of an isomorphism of finite continuous modules is
equivariant. -/
theorem finiteTypeContinuousModuleAddEquiv_ρ {G : Type (u + 1)} [Group G] [TopologicalSpace G]
    {P P' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G} (e : P ≅ P') (g : G)
    (v : P.obj.obj.obj.V) :
    finiteTypeContinuousModuleAddEquiv Λ e ((P.obj.obj.obj.ρ g).hom v) =
      (P'.obj.obj.obj.ρ g).hom (finiteTypeContinuousModuleAddEquiv Λ e v) :=
  ConcreteCategory.congr_hom (e.hom.hom.hom.hom.comm g) v

/-- The finite locally constant abelian sheaf underlying `ℱ_P`, as an object of the source of the
canonical equivalence of Tag 0DV5 (2). -/
abbrev lisseSheafAbelian
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    (Stacks.ConstantSheaf.isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory :=
  ((Stacks.ConstantSheaf.finiteLocallyConstantModuleSheafScalarActionEquivalence
    (SmallEtale.topology B X.1 X.2) Λ).functor.obj
      ((finiteTypeLocallyConstantModuleSheafBridge B X Λ).inverse.obj
        ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse.obj P))).obj.obj
    (SingleObj.star Λ)

/-- The stalk of the abelian sheaf underlying `ℱ_P` is the underlying group of
`E(E⁻¹ P)`, `E` the equivalence of Tag 0DV5 (3). -/
def lisseSheafAbelianStalkAddEquiv {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    (abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).obj (lisseSheafAbelian B X x Λ P).obj ≃+
      (((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse ⋙
        (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor).obj
          P).obj.obj.obj.V :=
  ((finiteLocallyConstantAbelianStalkIso B X t).app
    (lisseSheafAbelian B X x Λ P)).addCommGroupIsoToAddEquiv

/-- The identification of the abelian stalk intertwines the map of Tag 04FN along `a` with the
action of the element of `π₁(X, x̄)` that `t` transports "precompose with `a`" to. -/
theorem lisseSheafAbelianStalkAddEquiv_geometricPointStalkMap {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (a : GeometricPoint.Hom s s)
    (σ : EtaleFundamentalGroup X.1 s) (hσ : σ.hom = finiteEtaleFiberMap a)
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (z : (abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).obj (lisseSheafAbelian B X x Λ P).obj) :
    lisseSheafAbelianStalkAddEquiv B X x Λ t P
        (((geometricPointStalkMap B X.1 X.2 a AddCommGrpCat.{u + 1}).app
          (lisseSheafAbelian B X x Λ P).obj.obj).hom z) =
      ((((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse ⋙
        (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor).obj
          P).obj.obj.obj.ρ (etaleFundamentalGroupMulEquiv t σ)).hom
        (lisseSheafAbelianStalkAddEquiv B X x Λ t P z) :=
  ConcreteCategory.congr_hom
    (geometricPointStalkMap_finiteLocallyConstantAbelianStalkIso B X t a σ hσ
      (lisseSheafAbelian B X x Λ P)) z

/-- The underlying abelian group of the stalk of `ℱ_P` is the stalk of its underlying abelian
sheaf. -/
def lisseSheafForget₂StalkAddEquiv (s : GeometricPoint X.1)
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    (etaleStalkPresheafFunctor B X.1 X.2 s (ModuleCat.{u + 1} Λ)).obj
      ((lisseSheaf B X x Λ).obj P).obj ≃+
      (abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).obj (lisseSheafAbelian B X x Λ P).obj :=
  (etaleStalkForget₂Iso B X.1 X.2 s Λ ((lisseSheaf B X x Λ).obj P)).addCommGroupIsoToAddEquiv

/-- The identification of the underlying abelian group of the stalk intertwines the maps of
Tag 04FN. -/
theorem lisseSheafForget₂StalkAddEquiv_geometricPointStalkMap {s : GeometricPoint X.1}
    (a : GeometricPoint.Hom s s)
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (y : (etaleStalkPresheafFunctor B X.1 X.2 s (ModuleCat.{u + 1} Λ)).obj
      ((lisseSheaf B X x Λ).obj P).obj) :
    lisseSheafForget₂StalkAddEquiv B X x Λ s P
        (((geometricPointStalkMap B X.1 X.2 a (ModuleCat.{u + 1} Λ)).app
            ((lisseSheaf B X x Λ).obj P).obj).hom y) =
      ((geometricPointStalkMap B X.1 X.2 a AddCommGrpCat.{u + 1}).app
          (lisseSheafAbelian B X x Λ P).obj.obj).hom
        (lisseSheafForget₂StalkAddEquiv B X x Λ s P y) :=
  ConcreteCategory.congr_hom
    (geometricPointStalkMap_preservesColimitIso B X.1 X.2
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) a ((lisseSheaf B X x Λ).obj P).obj) y

/-- A square with an isomorphism on both sides commutes when its inverse square does. -/
theorem moduleCat_iso_hom_comm_of_inv_comm {C : Type*} [Category C] {A A' : C} (E : A ≅ A')
    (f : A ⟶ A) (g : A' ⟶ A') (h : E.inv ≫ f = g ≫ E.inv) : f ≫ E.hom = E.hom ≫ g := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Squares with isomorphisms on both sides compose. -/
theorem iso_trans_hom_comm {C : Type*} [Category C] {A A' A'' : C} (E : A ≅ A') (E' : A' ≅ A'')
    (f : A ⟶ A) (g : A' ⟶ A') (h : A'' ⟶ A'') (h₁ : f ≫ E.hom = E.hom ≫ g)
    (h₂ : g ≫ E'.hom = E'.hom ≫ h) : f ≫ (E ≪≫ E').hom = (E ≪≫ E').hom ≫ h := by
  rw [Iso.trans_hom, ← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- Intertwining is stable under composition of additive equivalences. -/
theorem addEquiv_trans_trans_intertwine {M N P R : Type*} {_ : Add M} {_ : Add N}
    {_ : Add P} {_ : Add R}
    (e : M ≃+ R) (e₁ : M ≃+ N) (e₂ : N ≃+ P) (e₃ : P ≃+ R) (he : e = e₁.trans (e₂.trans e₃))
    (f : M → M) (g : N → N) (h : P → P) (k : R → R)
    (y : M) (h₁ : e₁ (f y) = g (e₁ y)) (h₂ : e₂ (g (e₁ y)) = h (e₂ (e₁ y)))
    (h₃ : e₃ (h (e₂ (e₁ y))) = k (e₃ (e₂ (e₁ y)))) :
    e (f y) = k (e y) := by
  subst he
  simp only [AddEquiv.trans_apply, h₁, h₂, h₃]

/-- **The stalk at `s̄` of the lisse sheaf `ℱ_P` is `P`**, as abelian groups, for a path `t` from
`s̄` to `x̄`: the stalk of the underlying abelian sheaf is the finite `π₁(X, x̄)`-module attached
to it by the canonical equivalence of Tag 0DV5 (2), which the counit of Tag 0DV5 (3) identifies
with `P`. -/
def lisseSheafStalkAddEquiv {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    (etaleStalkPresheafFunctor B X.1 X.2 s (ModuleCat.{u + 1} Λ)).obj
      ((lisseSheaf B X x Λ).obj P).obj ≃+ P.obj.obj.obj.V :=
  (lisseSheafForget₂StalkAddEquiv B X x Λ s P).trans
    ((lisseSheafAbelianStalkAddEquiv B X x Λ t P).trans
      (finiteTypeContinuousModuleAddEquiv Λ
        ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).counitIso.app P)))

/-- **The action of an endomorphism `a` of the geometric point on the stalk of `ℱ_P` is the action
of an element of `π₁`**: if the automorphism `σ` of the fibre functor at `s̄` is precomposition
with `a`, it is the action on `P` of the element that the path `t` transports `σ` to. -/
theorem lisseSheafStalkAddEquiv_geometricPointStalkMap {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (a : GeometricPoint.Hom s s)
    (σ : EtaleFundamentalGroup X.1 s) (hσ : σ.hom = finiteEtaleFiberMap a)
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (y : (etaleStalkPresheafFunctor B X.1 X.2 s (ModuleCat.{u + 1} Λ)).obj
      ((lisseSheaf B X x Λ).obj P).obj) :
    lisseSheafStalkAddEquiv B X x Λ t P
        (((geometricPointStalkMap B X.1 X.2 a (ModuleCat.{u + 1} Λ)).app
            ((lisseSheaf B X x Λ).obj P).obj).hom y) =
      (P.obj.obj.obj.ρ (etaleFundamentalGroupMulEquiv t σ)).hom
        (lisseSheafStalkAddEquiv B X x Λ t P y) := by
  have s1 := lisseSheafForget₂StalkAddEquiv_geometricPointStalkMap B X x Λ a P y
  have s2 := lisseSheafAbelianStalkAddEquiv_geometricPointStalkMap B X x Λ t a σ hσ P
    (lisseSheafForget₂StalkAddEquiv B X x Λ s P y)
  have s3 := finiteTypeContinuousModuleAddEquiv_ρ Λ
    ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).counitIso.app P)
    (etaleFundamentalGroupMulEquiv t σ)
    (lisseSheafAbelianStalkAddEquiv B X x Λ t P (lisseSheafForget₂StalkAddEquiv B X x Λ s P y))
  exact addEquiv_trans_trans_intertwine (lisseSheafStalkAddEquiv B X x Λ t P)
    (lisseSheafForget₂StalkAddEquiv B X x Λ s P)
    (lisseSheafAbelianStalkAddEquiv B X x Λ t P)
    (finiteTypeContinuousModuleAddEquiv Λ
      ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).counitIso.app P)) rfl _ _ _
      (P.obj.obj.obj.ρ (etaleFundamentalGroupMulEquiv t σ)).hom y s1 s2 s3

/-! ### Over `ℤ/m`: isomorphisms of modules -/

section ZMod

variable (m : ℕ) [NeZero m]

/-- An additive equivalence of `ℤ/m`-modules, as an isomorphism of `ℤ/m`-modules. -/
def zmodModuleCatIsoOfAddEquiv {M N : ModuleCat.{u + 1} (ZMod m)} (e : M ≃+ N) : M ≅ N :=
  LinearEquiv.toModuleIso { e with map_smul' := fun a v => ZMod.map_smul e a v }

omit [NeZero m] in
/-- An additive equivalence of `ℤ/m`-modules intertwining two endomorphisms intertwines them as
an isomorphism of modules. -/
theorem zmodModuleCatIsoOfAddEquiv_comm {M N : ModuleCat.{u + 1} (ZMod m)} (e : M ≃+ N)
    (f : M ⟶ M) (g : N ⟶ N) (h : ∀ v, e (f.hom v) = g.hom (e v)) :
    f ≫ (zmodModuleCatIsoOfAddEquiv m e).hom = (zmodModuleCatIsoOfAddEquiv m e).hom ≫ g := by
  ext v
  exact h v

/-- **The stalk of `ℱ_P` on Mathlib's small étale site is `P`**, as `ℤ/m`-modules:
`Stacks.EtaleCohomology.lisseSheafStalkAddEquiv` read through the comparison of the stalk functors
of the two small étale sites. -/
def lisseEtaleSheafFiberIso {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) (EtaleFundamentalGroup X.1 x)) :
    (Scheme.pointSmallEtale s.hom).sheafFiber.obj ((lisseEtaleSheaf B X x (ZMod m)).obj P) ≅
      P.obj.obj.obj.V :=
  (sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod m) s).app ((lisseSheaf B X x (ZMod m)).obj
      P) ≪≫
    zmodModuleCatIsoOfAddEquiv m (lisseSheafStalkAddEquiv B X x (ZMod m) t P)

/-- **The action of an endomorphism `a` of the geometric point on the stalk of `ℱ_P` on Mathlib's
small étale site is the action of an element of `π₁`**: if the automorphism `σ` of the fibre
functor at `s̄` is precomposition with `a`, it is the action on `P` of the element that the path
`t` transports `σ` to. -/
theorem sheafFiber_comp_lisseEtaleSheafFiberIso_hom {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (a : GeometricPoint.Hom s s)
    (σ : EtaleFundamentalGroup X.1 s) (hσ : σ.hom = finiteEtaleFiberMap a)
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) (EtaleFundamentalGroup X.1 x)) :
    (GrothendieckTopology.Point.Hom.sheafFiber (smallEtalePointHom X.1 a)).app
        ((lisseEtaleSheaf B X x (ZMod m)).obj P) ≫ (lisseEtaleSheafFiberIso B X x m t P).hom =
      (lisseEtaleSheafFiberIso B X x m t P).hom ≫
        P.obj.obj.obj.ρ (etaleFundamentalGroupMulEquiv t σ) := by
  have hnat := congrArg (fun α => α.app ((lisseSheaf B X x (ZMod m)).obj P))
    (sheafEquivCompSheafFiberIso_inv_naturality.{u, u + 1, 0} B X (ZMod m) a)
  have hsq := moduleCat_iso_hom_comm_of_inv_comm
    ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod m) s).app
      ((lisseSheaf B X x (ZMod m)).obj P))
    ((GrothendieckTopology.Point.Hom.sheafFiber (smallEtalePointHom X.1 a)).app
      ((lisseEtaleSheaf B X x (ZMod m)).obj P))
    ((geometricPointStalkMap B X.1 X.2 a (ModuleCat.{u + 1} (ZMod m))).app
      ((lisseSheaf B X x (ZMod m)).obj P).obj) hnat
  have h3 := zmodModuleCatIsoOfAddEquiv_comm m (lisseSheafStalkAddEquiv B X x (ZMod m) t P)
    ((geometricPointStalkMap B X.1 X.2 a (ModuleCat.{u + 1} (ZMod m))).app
      ((lisseSheaf B X x (ZMod m)).obj P).obj)
    (P.obj.obj.obj.ρ (etaleFundamentalGroupMulEquiv t σ))
    (lisseSheafStalkAddEquiv_geometricPointStalkMap B X x (ZMod m) t a σ hσ P)
  exact iso_trans_hom_comm _ _ _ _ _ hsq h3

end ZMod

end Stacks.EtaleCohomology

end
