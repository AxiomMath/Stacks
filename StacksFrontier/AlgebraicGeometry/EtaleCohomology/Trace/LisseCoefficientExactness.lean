module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.Modules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCompactSupportRightExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupportFunctoriality

/-!
# The lisse sheaf of a finite continuous module, and right exactness of its `H²_c` on a curve

Let `X` be a connected scheme with a geometric point `x̄` and `Λ` a finite ring. The equivalence of
[Stacks, Tag 0DV5] (3) attaches to a finite `Λ`-module `P` with a continuous action of
`π₁(X, x̄)` a finite type locally constant sheaf of `Λ`-modules `ℱ_P` on `X_étale`; for the level
modules of a continuous `ℤ_ℓ`-representation this is the level sheaf of `ℱ_ρ`
(`Stacks.EtaleCohomology.lisseSheaf_obj_levelModule`).

The functor `P ↦ ℱ_P` is right exact: an exact sequence `P₁ → P₀ → P → 0` of finite
`π₁(X, x̄)`-modules gives an exact sequence of sheaves. On underlying abelian sheaves this is the
equivalence of Tag 0DV5 (2), which preserves cokernels, followed by the inclusion of the finite
locally constant abelian sheaves, a weak Serre subcategory (Tag 093U (2)); a map of sheaves of
modules whose underlying map of abelian sheaves is a cokernel is a cokernel. Composed with the
right exactness of `H²_c` on a curve
(`Stacks.EtaleCohomology.exact_compactSupportSheafCohomology_two_map`), `P ↦ H²_c(X_k̄, ℱ_P)` is
right exact. This is how the computation of `H²_c` of a lisse sheaf on a curve in
[Stacks, Tag 03VK] reduces to a presentation of its monodromy module.

## Main definitions

* `Stacks.EtaleCohomology.lisseSheaf`: `P ↦ ℱ_P`, on the small étale site of Stacks 021B.
* `Stacks.EtaleCohomology.lisseEtaleSheaf`: the same, on Mathlib's small étale site.

## Main results

* `Stacks.EtaleCohomology.isColimitCokernelCoforkFiniteContinuousAbelian`: an exact sequence
  `A₁ → A₀ → A → 0` of finite discrete `G`-modules is a cokernel.
* `Stacks.EtaleCohomology.isColimitModuleSheafCokernelCofork`: cokernels of sheaves of modules are
  detected on the underlying abelian sheaves.
* `Stacks.EtaleCohomology.isColimitLisseSheafCokernelCofork`: `P ↦ ℱ_P` is right exact.
* `Stacks.EtaleCohomology.exact_compactSupportSheafCohomology_two_lisseEtaleSheaf_map`: right
  exactness of `P ↦ H²_c(X_k̄, ℱ_P)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf
  Stacks.GroupCohomology

universe u

attribute [local instance] discreteForget₂AddCommGrpCat
  Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize

open scoped Stacks.DiscreteModuleTopology

namespace Stacks.EtaleCohomology

/-! ### Cokernels of finite discrete `G`-modules -/

section Abelian

variable {G : Type (u + 1)} [Group G] [TopologicalSpace G]

variable {A₁ A₀ A : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} G).FullSubcategory}
  (a : A₁ ⟶ A₀) (b : A₀ ⟶ A) (w : a ≫ b = 0)
  (hb : Function.Surjective b.hom.hom.hom.hom.hom)
  (hex : ∀ y, b.hom.hom.hom.hom.hom y = 0 → ∃ z, a.hom.hom.hom.hom.hom z = y)

include hex in
/-- A morphism killing `a` takes equal values on elements with the same image under `b`. -/
theorem apply_eq_of_apply_eq_finiteContinuousAbelian
    {Z : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} G).FullSubcategory} (g : A₀ ⟶ Z)
    (hg : a ≫ g = 0) {y y' : A₀.obj.obj.obj.V}
    (h : b.hom.hom.hom.hom.hom y = b.hom.hom.hom.hom.hom y') :
    g.hom.hom.hom.hom.hom y = g.hom.hom.hom.hom.hom y' := by
  obtain ⟨z, hz⟩ := hex (y - y') (by rw [map_sub, h, sub_self])
  rw [← sub_eq_zero, ← map_sub, ← hz]
  exact congrArg (fun φ => φ.hom.hom.hom.hom.hom z) hg

/-- The factorisation through `b` of a morphism killing `a`. -/
def descFiniteContinuousAbelian
    {Z : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} G).FullSubcategory} (g : A₀ ⟶ Z)
    (hg : a ≫ g = 0) : A ⟶ Z :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom
        { toFun := fun y => g.hom.hom.hom.hom.hom (Function.surjInv hb y)
          map_zero' := (apply_eq_of_apply_eq_finiteContinuousAbelian a b hex g hg
            (y' := 0) (by rw [Function.surjInv_eq hb, map_zero])).trans (map_zero _)
          map_add' := fun y y' => (apply_eq_of_apply_eq_finiteContinuousAbelian a b hex g hg
              (y' := Function.surjInv hb y + Function.surjInv hb y') (by
                rw [map_add, Function.surjInv_eq hb, Function.surjInv_eq hb,
                  Function.surjInv_eq hb])).trans (map_add _ _ _) }
      comm := fun h => by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun y => ?_)
        have hcomm := ConcreteCategory.congr_hom (g.hom.hom.hom.comm h) (Function.surjInv hb y)
        refine Eq.trans ?_ hcomm
        refine apply_eq_of_apply_eq_finiteContinuousAbelian a b hex g hg ?_
        have hb' := ConcreteCategory.congr_hom (b.hom.hom.hom.comm h) (Function.surjInv hb y)
        refine Eq.trans ?_ hb'.symm
        change _ = (A.obj.obj.obj.ρ h).asHom.hom (b.hom.hom.hom.hom.hom (Function.surjInv hb y))
        rw [Function.surjInv_eq hb, Function.surjInv_eq hb]
        rfl }))

include hex in
/-- **An exact sequence `A₁ → A₀ → A → 0` of finite discrete `G`-modules is a cokernel.** -/
def isColimitCokernelCoforkFiniteContinuousAbelian :
    IsColimit (CokernelCofork.ofπ b w) :=
  CokernelCofork.IsColimit.ofπ _ _ (fun g hg => descFiniteContinuousAbelian a b hb hex g hg)
    (fun g hg => by
      apply finiteContinuousAbelianHom_ext
      ext y
      exact apply_eq_of_apply_eq_finiteContinuousAbelian a b hex g hg
        (Function.surjInv_eq hb _))
    (fun g hg m hm => by
      apply finiteContinuousAbelianHom_ext
      ext y
      have h := congrArg (fun φ => φ.hom.hom.hom.hom.hom (Function.surjInv hb y)) hm
      refine Eq.trans ?_ h
      change m.hom.hom.hom.hom.hom y =
        m.hom.hom.hom.hom.hom (b.hom.hom.hom.hom.hom (Function.surjInv hb y))
      rw [Function.surjInv_eq hb])

end Abelian

/-! ### Cokernels of sheaves of modules -/

section ModuleSheaf

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type) [Ring R]

/-- The underlying abelian sheaf of a sheaf of modules on the small étale site of Stacks 021B. -/
abbrev moduleSheafForget :
    Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} R) ⥤
      Sheaf (SmallEtale.topology B X.1 X.2) AddCommGrpCat.{u + 1} :=
  sheafCompose (SmallEtale.topology B X.1 X.2) (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})

variable {B X R} in
/-- **Cokernels of sheaves of modules are detected on the underlying abelian sheaves**: if the
underlying map of abelian sheaves of `g` is a cokernel of that of `f`, then `g` is a cokernel of
`f`. A morphism `h` killing `f` factors uniquely through `g` on abelian sheaves; the factorisation
commutes with the scalar operations because `g` is an epimorphism, hence is a map of sheaves of
modules (`CategoryTheory.moduleSheafScalarActionEquivalence`). -/
def isColimitModuleSheafCokernelCofork
    {A₁ A₀ A : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} R)} (f : A₁ ⟶ A₀)
    (g : A₀ ⟶ A) (w : f ≫ g = 0)
    (hc : IsColimit (CokernelCofork.ofπ (f := (moduleSheafForget B X R).map f)
      ((moduleSheafForget B X R).map g)
      (by rw [← Functor.map_comp, w, Functor.map_zero]))) :
    IsColimit (CokernelCofork.ofπ g w) := by
  let F := moduleSheafForget B X R
  haveI hepi : Epi (F.map g) := epi_of_isColimit_cofork hc
  let S := moduleSheafToScalarAction.{u, u + 1, u + 1} (SmallEtale.topology B X.1 X.2) R
  have hscal : ∀ {T : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} R)} (h : A₀ ⟶ T)
      (a : R), (S.obj A₀).obj.map (X := SingleObj.star _) (Y := SingleObj.star _) a ≫ F.map h =
        F.map h ≫ (S.obj T).obj.map (X := SingleObj.star _) (Y := SingleObj.star _) a :=
    fun h a => ((S.map h).hom.naturality (X := SingleObj.star _) (Y := SingleObj.star _) a)
  have key : ∀ {T : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} R)} (h : A₀ ⟶ T),
      f ≫ h = 0 → ∃ m : A ⟶ T, F.map g ≫ F.map m = F.map h := by
    intro T h hh
    have hw : F.map f ≫ F.map h = 0 := by rw [← Functor.map_comp, hh, Functor.map_zero]
    let d : F.obj A ⟶ F.obj T := hc.desc (CokernelCofork.ofπ (f := F.map f) (F.map h) hw)
    have hd : F.map g ≫ d = F.map h :=
      hc.fac (CokernelCofork.ofπ (f := F.map f) (F.map h) hw) WalkingParallelPair.one
    have hnat : ∀ a : R,
        (S.obj A).obj.map (X := SingleObj.star _) (Y := SingleObj.star _) a ≫ d =
          d ≫ (S.obj T).obj.map (X := SingleObj.star _) (Y := SingleObj.star _) a := by
      intro a
      apply hepi.left_cancellation
      have e1 := hscal g a
      have e2 := hscal h a
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ d) e1.symm).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hd).trans (e2.trans
          ((congrArg (· ≫ (S.obj T).obj.map (X := SingleObj.star _) (Y := SingleObj.star _) a)
            hd.symm).trans (Category.assoc _ _ _))))))
    let θ : S.obj A ⟶ S.obj T := ObjectProperty.homMk
      { app := fun _ => d
        naturality := fun _ _ a => hnat a }
    refine ⟨(moduleSheafScalarActionEquivalence.{u, u + 1, u + 1} (SmallEtale.topology B X.1 X.2)
      R).fullyFaithfulFunctor.preimage θ, ?_⟩
    have hpre := congrArg (fun φ => φ.hom.app (SingleObj.star R))
      ((moduleSheafScalarActionEquivalence.{u, u + 1, u + 1} (SmallEtale.topology B X.1 X.2)
        R).fullyFaithfulFunctor.map_preimage θ)
    exact (congrArg (F.map g ≫ ·) hpre).trans hd
  refine CokernelCofork.IsColimit.ofπ _ _ (fun h hh => (key h hh).choose)
    (fun h hh => Functor.map_injective F ?_) (fun h hh m hm => Functor.map_injective F ?_)
  · rw [Functor.map_comp]
    exact (key h hh).choose_spec
  · apply hepi.left_cancellation
    rw [(key h hh).choose_spec, ← Functor.map_comp, hm]

end ModuleSheaf

/-! ### The lisse sheaf of a finite continuous module -/

section Lisse

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type) [CommRing Λ] [Finite Λ]

/-- Sheafification of sheaves of `Λ`-modules on the small étale site of Stacks 021B. -/
local instance hasSheafify_smallEtaleObj_moduleCat :
    HasSheafify (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) :=
  Stacks.ConstantSheaf.hasSheafify_moduleCat.{u + 1, u, 0, u + 1} _ Λ

/-- **The lisse sheaf `ℱ_P`** of a finite `Λ`-module `P` with a continuous action of `π₁(X, x̄)`:
the inverse of the equivalence of Tag 0DV5 (3), on the small étale site of Stacks 021B. -/
abbrev lisseSheaf :
    FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x) ⥤
      Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) :=
  (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse ⋙ ObjectProperty.ι _

/-- `ℱ_P` read on Mathlib's small étale site. -/
abbrev lisseEtaleSheaf :
    FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x) ⥤
      EtaleModules.{u, 0} Λ X.1 :=
  lisseSheaf B X x Λ ⋙ (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).functor

/-- **The levels of `ℱ_ρ` are the lisse sheaves of the level modules.** -/
theorem lisseSheaf_obj_levelModule {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
    (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ) (k : ℕ)
    [NeZero (ℓ ^ k)] :
    (lisseSheaf B X x (ZMod (ℓ ^ k))).obj (levelModule.{u + 1, u + 1} ρ hρ k) =
      representationLevelSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        ρ hρ k :=
  rfl

variable {B X x Λ}
variable {P₁ P₀ P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
  (a : P₁ ⟶ P₀) (b : P₀ ⟶ P) (w : a ≫ b = 0)
  (hb : Function.Surjective b.hom.hom.hom.hom.hom)
  (hex : ∀ y, b.hom.hom.hom.hom.hom y = 0 → ∃ z, a.hom.hom.hom.hom.hom z = y)

include w in
/-- `ℱ_{P₁} → ℱ_{P₀} → ℱ_P` composes to zero. -/
theorem lisseSheaf_map_comp_map_eq_zero :
    (lisseSheaf B X x Λ).map a ≫ (lisseSheaf B X x Λ).map b = 0 := by
  let e := canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x
  let φ := finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)
  have w' : φ.map a ≫ φ.map b = 0 := by
    apply finiteContinuousAbelianHom_ext
    ext y
    exact congrArg (fun t => t.hom.hom.hom.hom.hom y) w
  have h0 : e.inverse.map (φ.map a) ≫ e.inverse.map (φ.map b) = 0 := by
    rw [← e.inverse.map_comp, w', Functor.map_zero]
  apply ObjectProperty.hom_ext
  ext U y
  exact congrArg (fun t => (t.hom.hom.app U).hom y) h0

include w in
/-- The same on Mathlib's small étale site. -/
theorem lisseEtaleSheaf_map_comp_map_eq_zero :
    (lisseEtaleSheaf B X x Λ).map a ≫ (lisseEtaleSheaf B X x Λ).map b = 0 := by
  have h := congrArg (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).functor.map
    (lisseSheaf_map_comp_map_eq_zero a b w)
  rw [Functor.map_comp, Functor.map_zero] at h
  exact h

include w hb hex in
/-- **`P ↦ ℱ_P` is right exact**: an exact sequence `P₁ → P₀ → P → 0` of finite continuous
`π₁(X, x̄)`-modules gives a cokernel `ℱ_{P₀} → ℱ_P` of `ℱ_{P₁} → ℱ_{P₀}`. -/
def isColimitLisseSheafCokernelCofork :
    IsColimit (CokernelCofork.ofπ (f := (lisseSheaf B X x Λ).map a) ((lisseSheaf B X x Λ).map b)
      (lisseSheaf_map_comp_map_eq_zero a b w)) := by
  let e := canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x
  let φ := finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)
  have w' : φ.map a ≫ φ.map b = 0 := by
    apply finiteContinuousAbelianHom_ext
    ext y
    exact congrArg (fun t => t.hom.hom.hom.hom.hom y) w
  haveI := hasSheafify_addCommGrp.{u, u + 1, u + 1} (SmallEtale.topology B X.1 X.2)
  haveI := isWeakSerreClass_isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
    (SmallEtale.topology B X.1 X.2)
  haveI := (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
    (SmallEtale.topology B X.1 X.2)).preservesCokernels_ι (e.inverse.map (φ.map a))
  exact isColimitModuleSheafCokernelCofork _ _ _ (CokernelCofork.mapIsColimit _
    (CokernelCofork.mapIsColimit _
      (isColimitCokernelCoforkFiniteContinuousAbelian (φ.map a) (φ.map b) w' hb hex) e.inverse)
    (ObjectProperty.ι _))

include w hb hex in
/-- The same on Mathlib's small étale site. -/
def isColimitLisseEtaleSheafCokernelCofork :
    IsColimit (CokernelCofork.ofπ (f := (lisseEtaleSheaf B X x Λ).map a)
      ((lisseEtaleSheaf B X x Λ).map b)
      (lisseEtaleSheaf_map_comp_map_eq_zero a b w)) :=
  CokernelCofork.mapIsColimit _ (isColimitLisseSheafCokernelCofork a b w hb hex)
    (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).functor

include w hb hex in
/-- The exact sequence `ℱ_{P₁} → ℱ_{P₀} → ℱ_P → 0` on Mathlib's small étale site. -/
theorem exact_lisseEtaleSheaf_map :
    (ShortComplex.mk ((lisseEtaleSheaf B X x Λ).map a) ((lisseEtaleSheaf B X x Λ).map b)
      (lisseEtaleSheaf_map_comp_map_eq_zero a b w)).Exact ∧
      Epi ((lisseEtaleSheaf B X x Λ).map b) := by
  have h := isColimitLisseEtaleSheafCokernelCofork a b w hb hex
  exact ⟨ShortComplex.exact_of_g_is_cokernel _ h, epi_of_isColimit_cofork h⟩

variable {k : Type u} [Field k] [Fintype k] (fX : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType fX] [QuasiCompact fX]
  (j : CompactificationOf (Over.mk fX)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosed kbar]

omit [Fintype k] in
/-- **Right exactness of `P ↦ H²_c(X_k̄, ℱ_P)` on a curve.** -/
theorem exact_compactSupportSheafCohomology_two_lisseEtaleSheaf_map [Finite k] (m : ℕ) [NeZero m]
    (hdim : topologicalKrullDim X.1 ≤ 1)
    {P₁ P₀ P : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) (EtaleFundamentalGroup X.1 x)}
    (a : P₁ ⟶ P₀) (b : P₀ ⟶ P) (w : a ≫ b = 0)
    (hb : Function.Surjective b.hom.hom.hom.hom.hom)
    (hex : ∀ y, b.hom.hom.hom.hom.hom y = 0 → ∃ z, a.hom.hom.hom.hom.hom z = y) :
    Function.Exact ((compactSupportSheafCohomology (ZMod m) fX j kbar 2).map
        ((lisseEtaleSheaf B X x (ZMod m)).map a)).hom
      ((compactSupportSheafCohomology (ZMod m) fX j kbar 2).map
        ((lisseEtaleSheaf B X x (ZMod m)).map b)).hom ∧
      Function.Surjective ((compactSupportSheafCohomology (ZMod m) fX j kbar 2).map
        ((lisseEtaleSheaf B X x (ZMod m)).map b)).hom := by
  have := Fintype.ofFinite k
  obtain ⟨hS, hE⟩ := exact_lisseEtaleSheaf_map a b w hb hex
  exact ⟨exact_compactSupportSheafCohomology_two_map fX j kbar m hdim _ _ _ hS,
    surjective_compactSupportSheafCohomology_two_map_of_epi fX j kbar m hdim _⟩

end Lisse

end Stacks.EtaleCohomology

end
