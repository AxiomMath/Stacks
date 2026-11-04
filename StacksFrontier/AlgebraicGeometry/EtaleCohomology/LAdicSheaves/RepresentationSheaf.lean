module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.Modules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationLevels
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.IntegralModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible

/-!
# The finite levels of the sheaf `ℱ_ρ` of a continuous `ℤ_ℓ`-representation

Let `X` be a connected scheme with a geometric point `x̄` and let
`ρ : π₁(X, x̄) → GL_r(ℤ_ℓ)` be continuous.  The notation preceding
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) attaches to `ρ` the sheaf `ℱ_ρ`: by
Tag 0DV5 the finite continuous `π₁(X, x̄)`-modules `(ℤ/ℓ^kℤ)^r` of
`Stacks.EtaleCohomology.levelModule` are the finite locally constant sheaves of
`ℤ/ℓ^kℤ`-modules on `X_étale`, and reduction between consecutive levels is the transition map.

## Main definitions

* `Stacks.EtaleCohomology.levelAbelian`: the finite discrete `π₁`-module underlying the level
  module.
* `Stacks.EtaleCohomology.levelAbelianReduction`: reduction, as a morphism of finite discrete
  `π₁`-modules.
* `Stacks.EtaleCohomology.representationLevelSheaf`: the finite locally constant sheaf of
  `ℤ/ℓ^kℤ`-modules attached to the level module, its underlying abelian sheaf being the image
  under the equivalence `e` of Tag 0DV5 (2).
* `Stacks.EtaleCohomology.representationLevelTransition`: the transition map, the image of
  reduction.

## Implementation notes

The construction is carried out for an arbitrary additive equivalence `e` between the finite
locally constant abelian sheaves and the finite discrete `π₁(X, x̄)`-modules, of which
`AlgebraicGeometry.finiteLocallyConstantAbelianSheafEquivalence` is one.  The module structure is
read off the scalar operations, exactly as in the proof of Tag 0DV5 (3)
(`AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafEquivalence`): a sheaf of
`ℤ/ℓ^kℤ`-modules is an abelian sheaf with additive scalar operations
(`CategoryTheory.moduleSheafScalarActionEquivalence`), and the scalar operations of the level
module are transported along `e`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf
  Stacks.GroupCohomology

universe u

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}

section Abelian

variable {G : Type (u + 1)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : G →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)

/-- The finite discrete `G`-module `(ℤ/ℓ^kℤ)^r` underlying the level module. -/
public abbrev levelAbelian (k : ℕ) :
    (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} G).FullSubcategory :=
  (finiteTypeContinuousModuleForgetAbelian (ZMod (ℓ ^ k)) G).obj (levelModule.{u + 1, u + 1} ρ hρ k)

/-- **Reduction** `(ℤ/ℓ^{k+1}ℤ)^r → (ℤ/ℓ^kℤ)^r`, as a morphism of finite discrete `G`-modules. -/
public def levelAbelianReduction (k : ℕ) : levelAbelian ρ hρ (k + 1) ⟶ levelAbelian ρ hρ k :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom
        { toFun := fun y => ULift.up (levelReduction k y.down)
          map_zero' := ULift.ext _ _ (map_zero _)
          map_add' := fun a b => ULift.ext _ _ (map_add _ _ _) }
      comm := fun g => by
        ext y
        exact ULift.ext _ _ (levelReduction_levelRepresentation ρ k g y.down) }))

/-- Reduction intertwines multiplication by `a` on the source with multiplication by its
reduction on the target. -/
public theorem finiteContinuousScalarFunctor_map_comp_levelAbelianReduction (k : ℕ)
    (a : ZMod (ℓ ^ (k + 1))) :
    (finiteContinuousScalarFunctor (ZMod (ℓ ^ (k + 1))) G
        (levelModule.{u + 1, u + 1} ρ hρ (k + 1))).map (X := SingleObj.star _)
          (Y := SingleObj.star _) a ≫
      levelAbelianReduction ρ hρ k =
    levelAbelianReduction ρ hρ k ≫
      (finiteContinuousScalarFunctor (ZMod (ℓ ^ k)) G (levelModule.{u + 1, u + 1} ρ hρ k)).map
        (X := SingleObj.star _) (Y := SingleObj.star _) (levelRingHom k a) := by
  apply finiteContinuousAbelianHom_ext
  ext y
  exact ULift.ext _ _ (levelReduction_smul k a y.down)

/-- Multiplication by `ℓ ^ k` on the level module `(ℤ/ℓ^{k+1}ℤ)^r`, a morphism of finite
discrete `G`-modules: the scalar operation of `ℓ ^ k`. -/
public abbrev levelAbelianMulPow (k : ℕ) : levelAbelian ρ hρ (k + 1) ⟶ levelAbelian ρ hρ (k + 1) :=
  (finiteContinuousScalarFunctor (ZMod (ℓ ^ (k + 1))) G
    (levelModule.{u + 1, u + 1} ρ hρ (k + 1))).map (X := SingleObj.star _) (Y := SingleObj.star _)
      ((ℓ ^ k : ℕ) : ZMod (ℓ ^ (k + 1)))

/-- Multiplication by `ℓ ^ k` followed by reduction modulo `ℓ ^ k` is zero. -/
public theorem levelAbelianMulPow_comp_levelAbelianReduction (k : ℕ) :
    levelAbelianMulPow ρ hρ k ≫ levelAbelianReduction ρ hρ k = 0 := by
  apply finiteContinuousAbelianHom_ext
  ext y
  refine ULift.ext _ _ ?_
  show levelReduction k (((ℓ ^ k : ℕ) : ZMod (ℓ ^ (k + 1))) • y.down) = 0
  rw [levelReduction_eq_zero_iff]
  exact ⟨y.down, by rw [Nat.cast_smul_eq_nsmul]⟩

/-- A section of reduction modulo `ℓ ^ k`, as a map of sets. -/
public def levelLift (k : ℕ) (y : Fin r → ZMod (ℓ ^ k)) : Fin r → ZMod (ℓ ^ (k + 1)) :=
  fun i => ((y i).val : ZMod (ℓ ^ (k + 1)))

/-- Reducing `levelLift k y` modulo `ℓ ^ k` gives back `y`. -/
public theorem levelReduction_levelLift (k : ℕ) (y : Fin r → ZMod (ℓ ^ k)) :
    levelReduction k (levelLift k y) = y := by
  funext i
  rw [levelReduction_apply, levelLift, map_natCast, ZMod.natCast_zmod_val]

variable {ρ hρ} in
/-- A morphism out of `(ℤ/ℓ^{k+1}ℤ)^r` killing `ℓ ^ k` takes equal values on vectors with the same
reduction. -/
public theorem apply_eq_of_levelReduction_eq {k : ℕ}
    {Z : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} G).FullSubcategory}
    (g : levelAbelian ρ hρ (k + 1) ⟶ Z) (hg : levelAbelianMulPow ρ hρ k ≫ g = 0)
    {a b : Fin r → ZMod (ℓ ^ (k + 1))} (hab : levelReduction k a = levelReduction k b) :
    g.hom.hom.hom.hom.hom (ULift.up a) = g.hom.hom.hom.hom.hom (ULift.up b) := by
  have h0 : levelReduction k (a - b) = 0 := by rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := (levelReduction_eq_zero_iff k _).1 h0
  have hc' : a - b = ((ℓ ^ k : ℕ) : ZMod (ℓ ^ (k + 1))) • c := by
    rw [hc, Nat.cast_smul_eq_nsmul]
  have hz : g.hom.hom.hom.hom.hom (ULift.up (a - b)) = 0 := by
    rw [hc']
    exact congrArg (fun φ => φ.hom.hom.hom.hom.hom (ULift.up c)) hg
  have hsub : g.hom.hom.hom.hom.hom (ULift.up (a - b)) =
      g.hom.hom.hom.hom.hom (ULift.up a) - g.hom.hom.hom.hom.hom (ULift.up b) :=
    map_sub g.hom.hom.hom.hom.hom (ULift.up a) (ULift.up b)
  exact sub_eq_zero.1 (hsub.symm.trans hz)

variable {ρ hρ} in
/-- The factorisation through reduction of a morphism killing `ℓ ^ k`. -/
public def levelAbelianDesc {k : ℕ}
    {Z : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} G).FullSubcategory}
    (g : levelAbelian ρ hρ (k + 1) ⟶ Z) (hg : levelAbelianMulPow ρ hρ k ≫ g = 0) :
    levelAbelian ρ hρ k ⟶ Z :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom
        { toFun := fun y => g.hom.hom.hom.hom.hom (ULift.up (levelLift k y.down))
          map_zero' := (apply_eq_of_levelReduction_eq g hg (b := 0)
            (by rw [levelReduction_levelLift, map_zero]; rfl)).trans
              (map_zero g.hom.hom.hom.hom.hom)
          map_add' := fun a b => (apply_eq_of_levelReduction_eq g hg
              (b := levelLift k a.down + levelLift k b.down) (by
                rw [map_add, levelReduction_levelLift, levelReduction_levelLift,
                  levelReduction_levelLift]
                rfl)).trans
              (map_add g.hom.hom.hom.hom.hom (ULift.up (levelLift k a.down))
                (ULift.up (levelLift k b.down))) }
      comm := fun h => by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun y => ?_)
        have hcomm := ConcreteCategory.congr_hom (g.hom.hom.hom.comm h)
          (ULift.up (levelLift k y.down))
        refine Eq.trans ?_ hcomm
        exact apply_eq_of_levelReduction_eq g hg (by
          change _ = levelReduction k (levelRepresentation ρ (k + 1) h (levelLift k y.down))
          rw [levelReduction_levelRepresentation, levelReduction_levelLift,
            levelReduction_levelLift]
          rfl) }))

/-- **Reduction modulo `ℓ ^ k` is the cokernel of multiplication by `ℓ ^ k`** in the finite
discrete `G`-modules. -/
public def isColimitLevelAbelianReduction (k : ℕ) :
    IsColimit (CokernelCofork.ofπ (levelAbelianReduction ρ hρ k)
      (levelAbelianMulPow_comp_levelAbelianReduction ρ hρ k)) :=
  CokernelCofork.IsColimit.ofπ _ _ (fun g hg => levelAbelianDesc g hg)
    (fun g hg => by
      apply finiteContinuousAbelianHom_ext
      ext y
      exact apply_eq_of_levelReduction_eq g hg (levelReduction_levelLift k _))
    (fun g hg m hm => by
      apply finiteContinuousAbelianHom_ext
      ext y
      have h := congrArg (fun φ => φ.hom.hom.hom.hom.hom (ULift.up (levelLift k y.down))) hm
      refine Eq.trans ?_ h
      change m.hom.hom.hom.hom.hom y = m.hom.hom.hom.hom.hom (ULift.up (levelReduction k _))
      rw [levelReduction_levelLift]
      rfl)

end Abelian

/-! ### Isomorphisms out of a left adjoint -/

/-- The transpose `L A ⟶ B` of `t : A ⟶ R B` under an adjunction `L ⊣ R` is an isomorphism as
soon as `t` is universal: every `A ⟶ R G` is `t ≫ R ψ` for exactly one `ψ : B ⟶ G`. -/
public theorem Adjunction.isIso_homEquiv_symm_of_bijective {C D : Type*} [Category* C]
    [Category* D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {A : C} {B : D} (t : A ⟶ R.obj B)
    (h : ∀ G : D, Function.Bijective fun ψ : B ⟶ G => t ≫ R.map ψ) :
    IsIso ((adj.homEquiv A B).symm t) := by
  refine isIso_of_coyoneda_map_bijective _ fun G => ?_
  have : (fun ψ : B ⟶ G => (adj.homEquiv A B).symm t ≫ ψ) =
      (adj.homEquiv A G).symm ∘ fun ψ : B ⟶ G => t ≫ R.map ψ := by
    funext ψ
    exact (adj.homEquiv_naturality_right_symm t ψ).symm
  rw [this]
  exact (adj.homEquiv A G).symm.bijective.comp (h G)

/-! ### The level sheaves and their transition maps -/

section Sheaves

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (e : (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory ≌
    (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} (EtaleFundamentalGroup X.1 x)).FullSubcategory)
  [e.functor.Additive]
  (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)

/-- The scalar operations of the level module, transported along `e` to the finite locally
constant abelian sheaf attached to it. -/
public def representationLevelScalars (k : ℕ) :
    SingleObj (ZMod (ℓ ^ k)) ⥤+ Sheaf (SmallEtale.topology B X.1 X.2) AddCommGrpCat.{u + 1} :=
  AdditiveFunctor.of (finiteContinuousScalarFunctor (ZMod (ℓ ^ k)) _
    (levelModule.{u + 1, u + 1} ρ hρ k) ⋙ e.inverse ⋙ ObjectProperty.ι _)

/-- **The `k`-th level of `ℱ_ρ`**: the sheaf of `ℤ/ℓ^kℤ`-modules on `X_étale` whose underlying
abelian sheaf is the image under `e` of `(ℤ/ℓ^kℤ)^r` with the action of `π₁(X, x̄)` through `ρ`
modulo `ℓ ^ k`. -/
public def representationLevelSheaf (k : ℕ) :
    Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) :=
  (scalarActionToModuleSheaf (SmallEtale.topology B X.1 X.2) (ZMod (ℓ ^ k))).obj
    (representationLevelScalars B X x e ρ hρ k)

/-- The component at `U` of the transition map: the image under `e` of reduction, on sections
over `U`; it is semilinear along `ℤ/ℓ^{k+1}ℤ → ℤ/ℓ^kℤ` because reduction is. -/
public def representationLevelTransitionApp (k : ℕ)
    (U : (SmallEtale B X.1 X.2)ᵒᵖ) :
    (representationLevelSheaf B X x e ρ hρ (k + 1)).obj.obj U ⟶
      (ModuleCat.restrictScalars.{u + 1, 0, 0} (levelRingHom (ℓ := ℓ) k)).obj
        ((representationLevelSheaf B X x e ρ hρ k).obj.obj U) := by
  letI := scalarActionModule (ZMod (ℓ ^ (k + 1))) (AdditiveFunctor.of
    ((representationLevelScalars B X x e ρ hρ (k + 1)).obj ⋙
      abelianSheafEvaluation (SmallEtale.topology B X.1 X.2) U))
  letI := scalarActionModule (ZMod (ℓ ^ k)) (AdditiveFunctor.of
    ((representationLevelScalars B X x e ρ hρ k).obj ⋙
      abelianSheafEvaluation (SmallEtale.topology B X.1 X.2) U))
  letI : Module (ZMod (ℓ ^ (k + 1))) ((representationLevelSheaf B X x e ρ hρ k).obj.obj U) :=
    Module.compHom _ (levelRingHom (ℓ := ℓ) k)
  refine ModuleCat.ofHom
    { toFun := fun y => ((e.inverse.map (levelAbelianReduction ρ hρ k)).hom.hom.app U).hom y
      map_add' := fun a b => map_add _ a b
      map_smul' := fun a y => ?_ }
  have hfun := (e.inverse.map_comp _ _).symm.trans ((congrArg e.inverse.map
    (finiteContinuousScalarFunctor_map_comp_levelAbelianReduction ρ hρ k a)).trans
    (e.inverse.map_comp _ _))
  have h := congrArg (fun f => f.hom.hom.app U) hfun
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h
  exact ConcreteCategory.congr_hom h y

/-- **The transition map of `ℱ_ρ`** from level `k + 1` to the restriction of scalars of level
`k`: the image under `e` of reduction modulo `ℓ ^ k`. -/
public def representationLevelTransition (k : ℕ) :
    representationLevelSheaf B X x e ρ hρ (k + 1) ⟶
      (sheafCompose (SmallEtale.topology B X.1 X.2)
        (ModuleCat.restrictScalars.{u + 1, 0, 0} (levelRingHom (ℓ := ℓ) k))).obj
        (representationLevelSheaf B X x e ρ hρ k) :=
  ObjectProperty.homMk
    { app := representationLevelTransitionApp B X x e ρ hρ k
      naturality := fun U V f => by
        ext y
        exact ConcreteCategory.congr_hom
          ((e.inverse.map (levelAbelianReduction ρ hρ k)).hom.hom.naturality f) y }

/-- The underlying abelian sheaf of the `k`-th level: the image under `e` of `(ℤ/ℓ^kℤ)^r`. -/
public abbrev representationLevelAbelian (k : ℕ) :
    Sheaf (SmallEtale.topology B X.1 X.2) AddCommGrpCat.{u + 1} :=
  (e.inverse.obj (levelAbelian ρ hρ k)).obj

/-- Its underlying abelian sheaf is the image of the level module under `e`. -/
public theorem forget₂_representationLevelSheaf (k : ℕ) :
    (sheafCompose (SmallEtale.topology B X.1 X.2)
        (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1})).obj
      (representationLevelSheaf B X x e ρ hρ k) = representationLevelAbelian B X x e ρ hρ k :=
  rfl

/-- The transition map on underlying abelian sheaves is the image of reduction under `e`. -/
public theorem forget₂_representationLevelTransition (k : ℕ) :
    (sheafCompose (SmallEtale.topology B X.1 X.2)
        (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (k + 1)))) AddCommGrpCat.{u + 1})).map
      (representationLevelTransition B X x e ρ hρ k) =
      (e.inverse.map (levelAbelianReduction ρ hρ k)).hom :=
  rfl

/-- **The transition map of `ℱ_ρ` on underlying abelian sheaves is the cokernel of
multiplication by `ℓ ^ k`**, in the category of all abelian sheaves on `X_étale`: `e` carries the
cokernel of `Stacks.EtaleCohomology.isColimitLevelAbelianReduction` to a cokernel among the finite
locally constant abelian sheaves, and these form a weak Serre subcategory (Tag 093U (2)), whose
inclusion preserves cokernels. -/
public def isColimitRepresentationLevelReduction (k : ℕ) :
    IsColimit ((CokernelCofork.ofπ (levelAbelianReduction ρ hρ k)
      (levelAbelianMulPow_comp_levelAbelianReduction ρ hρ k)).map e.inverse |>.map
        (ObjectProperty.ι _)) := by
  haveI := hasSheafify_addCommGrp.{u, u + 1, u + 1} (SmallEtale.topology B X.1 X.2)
  haveI := isWeakSerreClass_isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
    (SmallEtale.topology B X.1 X.2)
  haveI := (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
    (SmallEtale.topology B X.1 X.2)).preservesCokernels_ι
      (e.inverse.map (levelAbelianMulPow ρ hρ k))
  exact CokernelCofork.mapIsColimit _
    (CokernelCofork.mapIsColimit _ (isColimitLevelAbelianReduction ρ hρ k) e.inverse) _

/-- The transition map is an epimorphism on underlying abelian sheaves. -/
public theorem epi_representationLevelAbelianReduction (k : ℕ) :
    Epi (e.inverse.map (levelAbelianReduction ρ hρ k)).hom :=
  epi_of_isColimit_cofork (isColimitRepresentationLevelReduction B X x e ρ hρ k)

/-- The scalar operation of `a` on the level sheaf is the image under `e` of multiplication by
`a` on the level module. -/
public theorem moduleSheafToScalarAction_representationLevelSheaf_map (k : ℕ)
    (a : ZMod (ℓ ^ k)) :
    ((moduleSheafToScalarAction.{u, u + 1, u + 1} (SmallEtale.topology B X.1 X.2)
      (ZMod (ℓ ^ k))).obj
        (representationLevelSheaf B X x e ρ hρ k)).obj.map
          (X := SingleObj.star _) (Y := SingleObj.star _) a =
      (e.inverse.map ((finiteContinuousScalarFunctor (ZMod (ℓ ^ k)) _
        (levelModule.{u + 1, u + 1} ρ hρ k)).map (X := SingleObj.star _) (Y := SingleObj.star _)
          a)).hom := by
  apply ObjectProperty.hom_ext
  ext U y
  rfl

/-- **The transition map is universal**: every morphism of sheaves of `ℤ/ℓ^{k+1}ℤ`-modules
from level `k + 1` to the restriction of scalars of a sheaf `T` of `ℤ/ℓ^kℤ`-modules factors
uniquely through the transition map.  On underlying abelian sheaves this is the universal
property of the cokernel of multiplication by `ℓ ^ k`, which kills every sheaf of
`ℤ/ℓ^kℤ`-modules; linearity of the factorisation is tested after the epimorphism. -/
public theorem representationLevelTransition_comp_bijective (k : ℕ)
    (T : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))) :
    Function.Bijective fun ψ : representationLevelSheaf B X x e ρ hρ k ⟶ T =>
      representationLevelTransition B X x e ρ hρ k ≫
        (sheafCompose (SmallEtale.topology B X.1 X.2)
          (ModuleCat.restrictScalars.{u + 1, 0, 0} (levelRingHom (ℓ := ℓ) k))).map ψ := by
  let F (n : ℕ) := sheafCompose (SmallEtale.topology B X.1 X.2)
    (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ n))) AddCommGrpCat.{u + 1})
  constructor
  · intro ψ ψ' hψ
    apply (F k).map_injective
    have hψ' : (e.inverse.map (levelAbelianReduction ρ hρ k)).hom ≫
        (F k).map ψ =
        (e.inverse.map (levelAbelianReduction ρ hρ k)).hom ≫
        (F k).map ψ' :=
      congrArg (F (k + 1)).map hψ
    exact (epi_representationLevelAbelianReduction B X x e ρ hρ k).left_cancellation _ _ hψ'
  · intro h
    let hab := (F (k + 1)).map h
    have hw : (e.inverse.map (levelAbelianMulPow ρ hρ k)).hom ≫ hab = 0 := by
      apply ObjectProperty.hom_ext
      ext U y
      have h1 := (h.hom.app U).hom.map_smul ((ℓ ^ k : ℕ) : ZMod (ℓ ^ (k + 1))) y
      have h2 : ((ℓ ^ k : ℕ) : ZMod (ℓ ^ (k + 1))) • (h.hom.app U).hom y = 0 := by
        show (levelRingHom k ((ℓ ^ k : ℕ) : ZMod (ℓ ^ (k + 1)))) •
          (show ToType (T.obj.obj U) from (h.hom.app U).hom y) = (0 : ToType (T.obj.obj U))
        rw [map_natCast, ZMod.natCast_self, zero_smul]
      exact h1.trans h2
    let hc := isColimitRepresentationLevelReduction B X x e ρ hρ k
    let d : representationLevelAbelian B X x e ρ hρ k ⟶
        (F k).obj T :=
      hc.desc (CokernelCofork.ofπ (f := (e.inverse.map (levelAbelianMulPow ρ hρ k)).hom) hab hw)
    have hd : (e.inverse.map (levelAbelianReduction ρ hρ k)).hom ≫ d = hab :=
      hc.fac (CokernelCofork.ofπ (f := (e.inverse.map (levelAbelianMulPow ρ hρ k)).hom) hab hw)
        WalkingParallelPair.one
    let S := moduleSheafToScalarAction.{u, u + 1, u + 1} (SmallEtale.topology B X.1 X.2)
      (ZMod (ℓ ^ k))
    let S' := moduleSheafToScalarAction.{u, u + 1, u + 1} (SmallEtale.topology B X.1 X.2)
      (ZMod (ℓ ^ (k + 1)))
    have hnat : ∀ b : ZMod (ℓ ^ k),
        (S.obj (representationLevelSheaf B X x e ρ hρ k)).obj.map
          (X := SingleObj.star _) (Y := SingleObj.star _) b ≫ d =
        d ≫ (S.obj T).obj.map (X := SingleObj.star _) (Y := SingleObj.star _) b := by
      intro b
      let a : ZMod (ℓ ^ (k + 1)) := ((b.val : ℕ) : ZMod (ℓ ^ (k + 1)))
      have ha : levelRingHom k a = b := by
        show levelRingHom k ((b.val : ℕ) : ZMod (ℓ ^ (k + 1))) = b
        rw [map_natCast, ZMod.natCast_zmod_val]
      apply (epi_representationLevelAbelianReduction B X x e ρ hρ k).left_cancellation
      have hred := (e.inverse.map_comp _ _).symm.trans ((congrArg e.inverse.map
        (finiteContinuousScalarFunctor_map_comp_levelAbelianReduction ρ hρ k a)).trans
        (e.inverse.map_comp _ _))
      have hred' := congrArg (fun f => f.hom) hred
      simp only [ObjectProperty.FullSubcategory.comp_hom] at hred'
      have E1 : (e.inverse.map (levelAbelianReduction ρ hρ k)).hom ≫
          (S.obj (representationLevelSheaf B X x e ρ hρ k)).obj.map
            (X := SingleObj.star _) (Y := SingleObj.star _) b =
          (S'.obj (representationLevelSheaf B X x e ρ hρ (k + 1))).obj.map
            (X := SingleObj.star _) (Y := SingleObj.star _) a ≫
            (e.inverse.map (levelAbelianReduction ρ hρ k)).hom := by
        rw [moduleSheafToScalarAction_representationLevelSheaf_map,
          moduleSheafToScalarAction_representationLevelSheaf_map, ← ha]
        exact hred'.symm
      have hh : (S'.obj (representationLevelSheaf B X x e ρ hρ (k + 1))).obj.map
            (X := SingleObj.star _) (Y := SingleObj.star _) a ≫ hab =
          hab ≫ (S.obj T).obj.map (X := SingleObj.star _) (Y := SingleObj.star _) b := by
        refine ((S'.map h).hom.naturality (X := SingleObj.star _) (Y := SingleObj.star _)
          a).trans ?_
        rw [← ha]
        apply ObjectProperty.hom_ext
        ext U y
        rfl
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ d) E1).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hd).trans (hh.trans
          ((congrArg (· ≫ (S.obj T).obj.map (X := SingleObj.star _) (Y := SingleObj.star _) b)
            hd.symm).trans (Category.assoc _ _ _))))))
    let θ : S.obj (representationLevelSheaf B X x e ρ hρ k) ⟶ S.obj T :=
      ObjectProperty.homMk
        { app := fun _ => d
          naturality := fun _ _ b => hnat b }
    let ψ := (moduleSheafScalarActionEquivalence.{u, u + 1, u + 1} (SmallEtale.topology B X.1 X.2)
      (ZMod (ℓ ^ k))).fullyFaithfulFunctor.preimage θ
    have hψ : (F k).map ψ = d :=
      congrArg (fun f => f.hom.app (SingleObj.star (ZMod (ℓ ^ k))))
        ((moduleSheafScalarActionEquivalence.{u, u + 1, u + 1} (SmallEtale.topology B X.1 X.2)
          (ZMod (ℓ ^ k))).fullyFaithfulFunctor.map_preimage θ)
    refine ⟨ψ, ?_⟩
    apply (F (k + 1)).map_injective
    show (e.inverse.map (levelAbelianReduction ρ hρ k)).hom ≫
      (F k).map ψ = hab
    rw [hψ, hd]

/-- The level sheaves are finite locally constant. -/
public theorem isFiniteLocallyConstant_representationLevelSheaf (k : ℕ) [NeZero (ℓ ^ k)] :
    IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.2)
      (representationLevelSheaf B X x e ρ hρ k) :=
  (isFiniteLocallyConstant_moduleSheaf_iff_forget₂ _ _ _).2
    (e.inverse.obj (levelAbelian ρ hρ k)).property

/-- The level sheaves are locally constant of finite type. -/
public theorem isFiniteTypeLocallyConstant_representationLevelSheaf (k : ℕ) [NeZero (ℓ ^ k)] :
    IsFiniteTypeLocallyConstant (ZMod (ℓ ^ k)) (SmallEtale.topology B X.1 X.2)
      (representationLevelSheaf B X x e ρ hρ k) := by
  have h := congrFun (isFiniteTypeLocallyConstant_eq_isFiniteLocallyConstant B X (ZMod (ℓ ^ k)))
    (representationLevelSheaf B X x e ρ hρ k)
  exact h ▸ isFiniteLocallyConstant_representationLevelSheaf B X x e ρ hρ k

end Sheaves

/-! ### The canonical equivalence of Tag 0DV5 (2) -/

section Canonical

open scoped ZeroObject

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)

/-- **The canonical equivalence of Tag 0DV5 (1)**, through the geometric fibre at `x̄`: a finite
locally constant sheaf of sets is a finite étale cover (Tag 03RV), which goes to its geometric
fibre at `x̄` with the action of `π₁(X, x̄)` by evaluation
(`AlgebraicGeometry.finiteEtaleEquivalenceOfIsGaloisCategory`).  Unlike
`AlgebraicGeometry.finiteLocallyConstantSetsEquivalence`, no choice is involved. -/
public def canonicalFiniteLocallyConstantSetsEquivalence :
    (isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1}
        (SmallEtale.topology B X.1 X.2)).FullSubcategory ≌
      (ContinuousGSet.isFinite.{u + 1, u + 1} (EtaleFundamentalGroup X.1 x)).FullSubcategory :=
  ((finiteLocallyConstantFiniteEtaleEquivalence B X).trans
    ((finiteEtaleEquivalenceOfIsGaloisCategory X.1 x).trans
      (contActionUniverseEquivalence.{u, u + 1} (EtaleFundamentalGroup X.1 x)))).trans
    finiteContinuousGSetEquivalence.symm

/-- **The canonical equivalence of Tag 0DV5 (2)**: the transport of commutative group objects
along `Stacks.EtaleCohomology.canonicalFiniteLocallyConstantSetsEquivalence`, so that the finite
`π₁(X, x̄)`-set underlying the module attached to an abelian sheaf is the geometric fibre at `x̄`
of the finite étale cover representing its underlying sheaf of sets. -/
public def canonicalFiniteLocallyConstantAbelianSheafEquivalence :
    (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
        (SmallEtale.topology B X.1 X.2)).FullSubcategory ≌
      (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
        (EtaleFundamentalGroup X.1 x)).FullSubcategory :=
  finiteLocallyConstantAbelianEquivalenceOfSetEquivalence
    (SmallEtale.topology B X.1 X.2) (EtaleFundamentalGroup X.1 x)
    (canonicalFiniteLocallyConstantSetsEquivalence B X x)

/-- The canonical equivalence of Tag 0DV5 (2) is additive. -/
public instance additive_canonicalFiniteLocallyConstantAbelianSheafEquivalence :
    (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).functor.Additive := by
  set e := canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x
  let : HasZeroObject
      (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
        (EtaleFundamentalGroup X.1 x)).FullSubcategory :=
    ⟨⟨e.functor.obj 0, isZero_equivalence_functor_obj e (isZero_zero _)⟩⟩
  let : e.functor.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_map_zero_object
      ((isZero_equivalence_functor_obj e (isZero_zero _)).iso (isZero_zero _))
  exact Functor.additive_of_preserves_binary_products e.functor

end Canonical

/-! ### The ℓ-adic sheaf `ℱ_ρ` -/

section LAdic

open AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (e : (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory ≌
    (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} (EtaleFundamentalGroup X.1 x)).FullSubcategory)
  [e.functor.Additive]
  (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]

/-- **The ℓ-adic sheaf of a continuous `ℤ_ℓ`-representation**: level `n` is the finite locally
constant sheaf of `ℤ/ℓ^{n+1}ℤ`-modules attached by `e` to `(ℤ/ℓ^{n+1}ℤ)^r` with the action of
`π₁(X, x̄)` through `ρ` modulo `ℓ ^ (n + 1)`, constructible because it is locally constant of
finite type, and the transition maps, the images of reduction, have isomorphic mates because
they are universal. -/
public def representationLAdicSheaf : LAdicSheaf.{u, u + 1} B X ℓ where
  level n := representationLevelSheaf B X x e ρ hρ (n + 1)
  constructible n := isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant B X _ _
    (isFiniteTypeLocallyConstant_representationLevelSheaf B X x e ρ hρ (n + 1))
  transition n := representationLevelTransition B X x e ρ hρ (n + 1)
  reduction_isIso n := Adjunction.isIso_homEquiv_symm_of_bijective _ _
    (representationLevelTransition_comp_bijective B X x e ρ hρ (n + 1))

/-- **`ℱ_ρ` is lisse**: every level is finite locally constant. -/
public theorem representationLAdicSheaf_isLisse :
    (representationLAdicSheaf B X x e ρ hρ).IsLisse := fun n => by
  have := isFiniteLocallyConstant_representationLevelSheaf B X x e ρ hρ (n + 1)
  show IsLocallyConstant _ (representationLevelSheaf B X x e ρ hρ (n + 1))
  infer_instance

/-- **The lisse ℓ-adic sheaf `ℱ_ρ` of a continuous `ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)`**, the sheaf of
the notation preceding [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH): `π₁(X, x̄)` is
compact (Tag 0BMR), so `ρ` is conjugate to a continuous `ℤ_ℓ`-representation
(`Stacks.EtaleCohomology.integralModel`), whose ℓ-adic sheaf is `ℱ_ρ`. -/
public def LAdicSheaf.ofRepresentation (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])
    (hρ : Continuous ρ) : LAdicSheaf.{u, u + 1} B X ℓ :=
  haveI := compactSpace_etaleFundamentalGroup X.1 x
  representationLAdicSheaf B X x e (integralModel ρ hρ) (continuous_integralModel ρ hρ)

/-- `ℱ_ρ` is lisse. -/
public theorem LAdicSheaf.ofRepresentation_isLisse
    (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ) :
    (LAdicSheaf.ofRepresentation B X x e ρ hρ).IsLisse :=
  have := compactSpace_etaleFundamentalGroup X.1 x
  representationLAdicSheaf_isLisse B X x e _ _

end LAdic

section CanonicalLAdic

open AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]

/-- **`ℱ_ρ`**, the lisse ℓ-adic sheaf of the notation preceding
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) attached to a continuous
`ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)`: `Stacks.EtaleCohomology.LAdicSheaf.ofRepresentation` for the
canonical equivalence of Tag 0DV5 (2), through the geometric fibre at `x̄`. -/
public def LAdicSheaf.representationSheaf (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])
    (hρ : Continuous ρ) : LAdicSheaf.{u, u + 1} B X ℓ :=
  LAdicSheaf.ofRepresentation B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
    ρ hρ

/-- `ℱ_ρ` is lisse. -/
public theorem LAdicSheaf.representationSheaf_isLisse
    (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ) :
    (LAdicSheaf.representationSheaf B X x ρ hρ).IsLisse :=
  LAdicSheaf.ofRepresentation_isLisse B X x _ ρ hρ

end CanonicalLAdic

end Stacks.EtaleCohomology

end
