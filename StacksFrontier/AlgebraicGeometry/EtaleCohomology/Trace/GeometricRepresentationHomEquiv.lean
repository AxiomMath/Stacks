module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricGlobalSectionsCanonical
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricGlobalSectionsGaloisEquivPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisSectionAct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DiscreteRepresentationSheaf
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleGaloisCategory
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.FiberFunctor
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.HomTwistDual
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.ForgetCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafInternalHom
public import StacksFrontier.CategoryTheory.Sites.IsomSheafGlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportDegreeZeroDuality

/-!
# Maps `res_ψ(pr⁻¹ℱ_ρ) ⟶ pr⁻¹ℱ_W` are `π₁(X_k̄)`-equivariant maps `M → W`

Let `X` be a connected scheme, `g : Y ⟶ X` a morphism from a connected scheme with a geometric
point `y`, `x = g(y)`, `Λ` a finite ring which is a `ℤ/n`-algebra, `ρ` a finite `Λ`-module `M`
with a continuous action of `π₁(X, x)`, and `W` a finite `ℤ/n`-module with a continuous action of
`π₁(X, x)`. A morphism of sheaves of `ℤ/n`-modules `φ : res_ψ(g⁻¹ℱ_ρ) ⟶ g⁻¹ℱ_W` on `Y_étale`
(`ψ : ℤ/n → Λ`) is the same as an additive map `M → W` equivariant under `π₁(Y, y)`, acting
through `π₁(Y, y) → π₁(X, x)`.

The map is explicit. As a sheaf of sets, `g⁻¹ℱ_ρ` is represented by the pulled back representing
cover `Y ×_X V` of `ℱ_ρ` (`Stacks.EtaleCohomology.bijective_map_moduleUnitSection`), through the
pulled back tautological section `u(ε)`. So `φ` is determined by `φ(u(ε))`, a section of
`g⁻¹ℱ_W` over `Y ×_X V`, which is a `Y`-morphism `τ_φ : Y ×_X V ⟶ Y ×_X V_W`; the map `M → W` is
`τ_φ` on the geometric fibres at `y`, which are `M` and `W`
(`AlgebraicGeometry.representationFibreEquiv`). No isomorphism is chosen.

## Main definitions

* `AlgebraicGeometry.pullbackRepresentationCoverHom` — the morphism to `Y ×_X V` classifying a
  section of `g⁻¹ℱ_ρ`.
* `AlgebraicGeometry.pullbackRepresentationEval` — the value of a section of `g⁻¹ℱ_ρ` at a point
  of an étale `Y`-scheme lying over `y`, read in `M`.
* `AlgebraicGeometry.pullbackRepresentationHomFun` — the map `M → W` of `φ`.
* `AlgebraicGeometry.pullbackRepresentationHomInvariants` — `ρ ↦ Hom_{π₁(Y)}(M, W)`.
* `AlgebraicGeometry.pullbackRepresentationHomEquiv` — `Φ_ρ : Hom(res_ψ(g⁻¹ℱ_ρ), g⁻¹ℱ_W) ≃
  Hom_{π₁(Y)}(M, W)`.

## Main results

* `AlgebraicGeometry.pullbackRepresentationHomEquiv_apply` — `Φ_ρ(φ)` is the map `M → W` of `φ`.
* `AlgebraicGeometry.pullbackRepresentationHomEquiv_naturality` — naturality in `ρ`.
* `AlgebraicGeometry.pullbackRepresentationHomFun_eval` — `Φ_ρ(φ)` computes `φ` on every
  section.
* `AlgebraicGeometry.pullbackRepresentationHomFun_injective` — injectivity, by Tag 0BN0.
* `AlgebraicGeometry.nat_card_pullbackRepresentationHom` — both sides have the same cardinality.
* `AlgebraicGeometry.pullbackRepresentationHomEquiv_geometricGlobalSectionsEval` — on `X_k̄`,
  `Φ_ρ(φ)` carries the evaluation at `η̄` of a global section `z` to that of `Γ(φ)(z)`.
* `AlgebraicGeometry.pullbackRepresentationHomEquiv_apply_of_trivial` — for geometrically trivial
  `ρ` and `W`, `Φ_ρ(φ)(m) = ev_W(Γ(φ)(ev_ρ⁻¹ m))`.
* `AlgebraicGeometry.geometricCyclotomicDualHomEquiv` (+ `_naturality`) — `Φ_ρ` for `W = μ_n(k̄)`,
  with values in `AlgebraicGeometry.geometricCyclotomicDualInvariants`.

## Implementation notes

The map is canonical: it involves no choice. The existence-only isomorphism of Tag 0DV6
(`AlgebraicGeometry.representationSheafPullbackIso`) is used only inside the proof of
`AlgebraicGeometry.nat_card_pullbackRepresentationHom`, a count, from which bijectivity follows;
the values of `Φ_ρ` do not depend on it.

Statements comparing points of fibres are made on the fibres themselves
(`AlgebraicGeometry.pullbackRepresentationFibrePoint_eq_fiber`), not on their images under
`AlgebraicGeometry.representationFibreEquiv`, and the definitions are unfolded by the equations
`AlgebraicGeometry.pullbackRepresentationHomFun_def` and
`AlgebraicGeometry.pullbackRepresentationEval_def`: unifying applied fibre equivalences elaborated
in different places exhausts the recursion depth. The morphisms of finite étale covers are compared
through `AlgebraicGeometry.pullbackRepresentationCoverFiniteEtaleHom_left`: an equation between a
morphism of `FiniteEtaleOver Y` and one of `Y.Etale` makes the kernel compare the two structures
and time out.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.EtaleCohomology Stacks.GroupCohomology Stacks.Frobenius

universe u

namespace AlgebraicGeometry

section Local

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] {Y : Scheme.{u}} (g : Y ⟶ X.1)
  (y : GeometricPoint Y) (Λ : Type) [Ring Λ] [Finite Λ]

/-- **The morphism to the pulled back representing cover classifying a section of `g⁻¹ℱ_ρ`**:
the unique `t : U ⟶ Y ×_X V` along which the pulled back tautological section restricts to `a`. -/
def pullbackRepresentationCoverHom
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    {U : Y.Etale}
    (a : ((etaleModuleInverseImage.{u, 0} Λ g).obj
      ((representationSheaf B X (y.map g) Λ).obj ρ)).obj.obj (op U)) :
    U ⟶ (Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
      (representationCover B X (y.map g) Λ ρ) :=
  (Equiv.ofBijective _ (bijective_map_moduleUnitSection Λ g _ _
    (isIso_sectionEquiv_symm_representationTautologicalSection B X _ Λ ρ) U)).symm a

/-- The defining property of `AlgebraicGeometry.pullbackRepresentationCoverHom`. -/
theorem pullbackRepresentationCoverHom_eq_iff
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    {U : Y.Etale}
    (a : ((etaleModuleInverseImage.{u, 0} Λ g).obj
      ((representationSheaf B X (y.map g) Λ).obj ρ)).obj.obj (op U))
    (t : U ⟶ (Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
      (representationCover B X (y.map g) Λ ρ)) :
    pullbackRepresentationCoverHom B X g y Λ ρ a = t ↔
      ((etaleModuleInverseImage.{u, 0} Λ g).obj
        ((representationSheaf B X (y.map g) Λ).obj ρ)).obj.map t.op
          (moduleUnitSection Λ g _ (representationTautologicalSection B X _ Λ ρ)) = a := by
  rw [pullbackRepresentationCoverHom, Equiv.symm_apply_eq, Equiv.ofBijective_apply]
  exact eq_comm

/-- A section is the restriction of the pulled back tautological section along its classifying
morphism. -/
theorem map_pullbackRepresentationCoverHom
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    {U : Y.Etale}
    (a : ((etaleModuleInverseImage.{u, 0} Λ g).obj
      ((representationSheaf B X (y.map g) Λ).obj ρ)).obj.obj (op U)) :
    ((etaleModuleInverseImage.{u, 0} Λ g).obj
        ((representationSheaf B X (y.map g) Λ).obj ρ)).obj.map
        (pullbackRepresentationCoverHom B X g y Λ ρ a).op
          (moduleUnitSection Λ g _ (representationTautologicalSection B X _ Λ ρ)) = a :=
  (pullbackRepresentationCoverHom_eq_iff B X g y Λ ρ a _).1 rfl

/-- The classifying morphism of a restricted section is the composite. -/
theorem pullbackRepresentationCoverHom_map
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    {U U' : Y.Etale} (t : U' ⟶ U)
    (a : ((etaleModuleInverseImage.{u, 0} Λ g).obj
      ((representationSheaf B X (y.map g) Λ).obj ρ)).obj.obj (op U)) :
    pullbackRepresentationCoverHom B X g y Λ ρ
        (((etaleModuleInverseImage.{u, 0} Λ g).obj
          ((representationSheaf B X (y.map g) Λ).obj ρ)).obj.map t.op a) =
      t ≫ pullbackRepresentationCoverHom B X g y Λ ρ a := by
  refine (pullbackRepresentationCoverHom_eq_iff B X g y Λ ρ _ _).2 ?_
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    map_pullbackRepresentationCoverHom]

/-- The classifying morphism of the pulled back tautological section is the identity. -/
theorem pullbackRepresentationCoverHom_moduleUnitSection
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g))) :
    pullbackRepresentationCoverHom B X g y Λ ρ
        (moduleUnitSection Λ g _ (representationTautologicalSection B X _ Λ ρ)) = 𝟙 _ := by
  refine (pullbackRepresentationCoverHom_eq_iff B X g y Λ ρ _ _).2 ?_
  rw [op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The point of the geometric fibre of `V` at `x = g(y)` given by a morphism `t : U ⟶ Y ×_X V`
and a point `ū` of `U` over `y`. -/
def pullbackRepresentationFibrePoint
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    {U : Y.Etale} (t : U ⟶ (Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
      (representationCover B X (y.map g) Λ ρ))
    (ū : y.source ⟶ U.left) (hū : ū ≫ U.hom = y.hom) :
    finiteEtaleFiber (y.map g) (representationFiniteEtaleCover B X (y.map g) Λ ρ) :=
  ⟨ū ≫ t.left ≫ pullback.fst _ _, (Category.assoc _ _ _).trans ((congrArg (ū ≫ ·)
    ((Category.assoc _ _ _).trans ((congrArg (t.left ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ g) (smallEtaleBaseChange_w g t)))))).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ g) hū)))⟩

/-- **The value at `ū` of a section `a` of `g⁻¹ℱ_ρ` over `U`, read in `M`**: the point of the
geometric fibre of the representing cover at `x` given by the classifying morphism of `a` at `ū`
(`AlgebraicGeometry.representationFibreEquiv`). -/
def pullbackRepresentationEval
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    {U : Y.Etale} (ū : y.source ⟶ U.left) (hū : ū ≫ U.hom = y.hom)
    (a : ((etaleModuleInverseImage.{u, 0} Λ g).obj
      ((representationSheaf B X (y.map g) Λ).obj ρ)).obj.obj (op U)) :
    ρ.obj.obj.obj.V :=
  representationFibreEquiv B X (y.map g) Λ ρ
    (pullbackRepresentationFibrePoint B X g y Λ ρ
      (pullbackRepresentationCoverHom B X g y Λ ρ a) ū hū)

/-- The definition of `AlgebraicGeometry.pullbackRepresentationEval`, as an equation. -/
theorem pullbackRepresentationEval_def
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    {U : Y.Etale} (ū : y.source ⟶ U.left) (hū : ū ≫ U.hom = y.hom)
    (a : ((etaleModuleInverseImage.{u, 0} Λ g).obj
      ((representationSheaf B X (y.map g) Λ).obj ρ)).obj.obj (op U)) :
    pullbackRepresentationEval B X g y Λ ρ ū hū a = representationFibreEquiv B X (y.map g) Λ ρ
      (pullbackRepresentationFibrePoint B X g y Λ ρ (pullbackRepresentationCoverHom B X g y Λ ρ a)
        ū hū) :=
  rfl

/-- The value only depends on the point, not on the proof that it lies over `y`. -/
theorem pullbackRepresentationEval_congr
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    {U : Y.Etale} {ū ū' : y.source ⟶ U.left} (hū : ū ≫ U.hom = y.hom) (hū' : ū' ≫ U.hom = y.hom)
    (h : ū = ū')
    (a : ((etaleModuleInverseImage.{u, 0} Λ g).obj
      ((representationSheaf B X (y.map g) Λ).obj ρ)).obj.obj (op U)) :
    pullbackRepresentationEval B X g y Λ ρ ū hū a =
      pullbackRepresentationEval B X g y Λ ρ ū' hū' a := by
  subst h
  rfl

/-- **The value is compatible with restriction**: the value of `t^* a` at `ū'` is the value of `a`
at `t ∘ ū'`. -/
theorem pullbackRepresentationEval_map
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    {U U' : Y.Etale} (t : U' ⟶ U) (ū' : y.source ⟶ U'.left) (hū' : ū' ≫ U'.hom = y.hom)
    (hū : (ū' ≫ t.left) ≫ U.hom = y.hom)
    (a : ((etaleModuleInverseImage.{u, 0} Λ g).obj
      ((representationSheaf B X (y.map g) Λ).obj ρ)).obj.obj (op U)) :
    pullbackRepresentationEval B X g y Λ ρ ū' hū'
        (((etaleModuleInverseImage.{u, 0} Λ g).obj
          ((representationSheaf B X (y.map g) Λ).obj ρ)).obj.map t.op a) =
      pullbackRepresentationEval B X g y Λ ρ (ū' ≫ t.left) hū a := by
  unfold pullbackRepresentationEval
  congr 1
  refine Subtype.ext ?_
  change ū' ≫ (pullbackRepresentationCoverHom B X g y Λ ρ
      (((etaleModuleInverseImage.{u, 0} Λ g).obj
        ((representationSheaf B X (y.map g) Λ).obj ρ)).obj.map t.op a)).left ≫ pullback.fst _ _ =
    (ū' ≫ t.left) ≫ (pullbackRepresentationCoverHom B X g y Λ ρ a).left ≫ pullback.fst _ _
  rw [pullbackRepresentationCoverHom_map, Category.assoc]
  rfl

/-- **The value is natural in `ρ`**: the value of the image of `a` under `g⁻¹ℱ_φ` is `φ` of the
value of `a`. -/
theorem pullbackRepresentationEval_naturality
    {ρ ρ' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g))}
    (φ : ρ ⟶ ρ') {U : Y.Etale} (ū : y.source ⟶ U.left) (hū : ū ≫ U.hom = y.hom)
    (a : ((etaleModuleInverseImage.{u, 0} Λ g).obj
      ((representationSheaf B X (y.map g) Λ).obj ρ)).obj.obj (op U)) :
    pullbackRepresentationEval B X g y Λ ρ' ū hū
        (((etaleModuleInverseImage.{u, 0} Λ g).map
          ((representationSheaf B X (y.map g) Λ).map φ)).hom.app (op U) a) =
      φ.hom.hom.hom.hom.hom (pullbackRepresentationEval B X g y Λ ρ ū hū a) := by
  set t := pullbackRepresentationCoverHom B X g y Λ ρ a
  let Vφ := (SmallEtale.toEtaleSite B X.1 X.2).map ((representationCoverSmall B X _ Λ).map φ).hom
  let G := (etaleModuleInverseImage.{u, 0} Λ g).map ((representationSheaf B X (y.map g) Λ).map φ)
  have hcov : pullbackRepresentationCoverHom B X g y Λ ρ' (G.hom.app (op U) a) =
      t ≫ (Stacks.EtaleCohomology.smallEtaleBaseChange g).map Vφ := by
    refine (pullbackRepresentationCoverHom_eq_iff B X g y Λ ρ' _ _).2 ?_
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      ← Stacks.EtaleCohomology.moduleUnitSection_map g _ Vφ,
      ← representationTautologicalSection_naturality B X _ Λ φ,
      ← inverseImage_map_moduleUnitSection g ((representationSheaf B X (y.map g) Λ).map φ)]
    rw [← map_pullbackRepresentationCoverHom B X g y Λ ρ a]
    exact (ConcreteCategory.congr_hom (G.hom.naturality t.op) _).symm
  have hpt : pullbackRepresentationFibrePoint B X g y Λ ρ'
      (t ≫ (Stacks.EtaleCohomology.smallEtaleBaseChange g).map Vφ) ū hū =
      (finiteEtaleFiberFunctor (y.map g)).map ((representingCover B X).map
        ((representationSetSheaf B X (y.map g) Λ).map φ))
        (pullbackRepresentationFibrePoint B X g y Λ ρ t ū hū) := by
    refine Subtype.ext ?_
    change ū ≫ (t.left ≫ ((Stacks.EtaleCohomology.smallEtaleBaseChange g).map Vφ).left) ≫
      pullback.fst _ _ =
      (ū ≫ t.left ≫ pullback.fst _ _) ≫ Vφ.left
    exact (congrArg (ū ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (t.left ≫ ·) (smallEtaleBaseChange_map_left_fst g Vφ)))).trans
      ((Category.assoc _ _ _).trans (congrArg (ū ≫ ·) (Category.assoc _ _ _))).symm
  change representationFibreEquiv B X (y.map g) Λ ρ' (pullbackRepresentationFibrePoint B X g y Λ ρ'
      (pullbackRepresentationCoverHom B X g y Λ ρ' (G.hom.app (op U) a)) ū hū) = _
  rw [hcov, hpt, representationFibreEquiv_naturality]
  rfl

/-- **The value is additive**: sections of `g⁻¹ℱ_ρ` over `U` form an additive functor of `ρ`, and
the value is natural in `ρ` (`CategoryTheory.Functor.map_add_of_naturality`). -/
theorem pullbackRepresentationEval_add
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    {U : Y.Etale} (ū : y.source ⟶ U.left) (hū : ū ≫ U.hom = y.hom)
    (a b : ((etaleModuleInverseImage.{u, 0} Λ g).obj
      ((representationSheaf B X (y.map g) Λ).obj ρ)).obj.obj (op U)) :
    pullbackRepresentationEval B X g y Λ ρ ū hū (a + b) =
      pullbackRepresentationEval B X g y Λ ρ ū hū a +
        pullbackRepresentationEval B X g y Λ ρ ū hū b := by
  have : (finiteTypeContinuousModuleι Λ (EtaleFundamentalGroup X.1 (y.map g)) ⋙
      continuousModuleToModuleCat Λ (EtaleFundamentalGroup X.1 (y.map g))).Additive :=
    ⟨fun {_ _ _ _} => rfl⟩
  exact Functor.map_add_of_naturality
    (representationSheaf B X (y.map g) Λ ⋙ etaleModuleInverseImage.{u, 0} Λ g ⋙
      sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U))
    (finiteTypeContinuousModuleι Λ _ ⋙ continuousModuleToModuleCat Λ _)
    (fun ρ => pullbackRepresentationEval B X g y Λ ρ ū hū)
    (fun φ a => pullbackRepresentationEval_naturality B X g y Λ φ ū hū a) ρ a b

/-- **The point of `Y ×_X V` over `y` given by `m ∈ M`**: `y` together with the point of the
geometric fibre of `V` at `x` that is `m` (`AlgebraicGeometry.representationFibreEquiv`). -/
def pullbackRepresentationFibreLift
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    (m : ρ.obj.obj.obj.V) :
    y.source ⟶ ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
      (representationCover B X (y.map g) Λ ρ)).left :=
  pullback.lift ((representationFibreEquiv B X (y.map g) Λ ρ).symm m).1 y.hom
    ((representationFibreEquiv B X (y.map g) Λ ρ).symm m).2

/-- The point `pullbackRepresentationFibreLift` lies over `y`. -/
theorem pullbackRepresentationFibreLift_hom
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    (m : ρ.obj.obj.obj.V) :
    pullbackRepresentationFibreLift B X g y Λ ρ m ≫
      ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
        (representationCover B X (y.map g) Λ ρ)).hom = y.hom :=
  pullback.lift_snd _ _ _

/-- The value of the pulled back tautological section at the point given by `m` is `m`. -/
theorem pullbackRepresentationEval_moduleUnitSection
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    (m : ρ.obj.obj.obj.V) :
    pullbackRepresentationEval B X g y Λ ρ (pullbackRepresentationFibreLift B X g y Λ ρ m)
        (pullbackRepresentationFibreLift_hom B X g y Λ ρ m)
        (moduleUnitSection Λ g _ (representationTautologicalSection B X _ Λ ρ)) = m := by
  have h : pullbackRepresentationFibrePoint B X g y Λ ρ
      (pullbackRepresentationCoverHom B X g y Λ ρ
        (moduleUnitSection Λ g _ (representationTautologicalSection B X _ Λ ρ)))
      (pullbackRepresentationFibreLift B X g y Λ ρ m)
      (pullbackRepresentationFibreLift_hom B X g y Λ ρ m) =
      (representationFibreEquiv B X (y.map g) Λ ρ).symm m := by
    refine Subtype.ext ?_
    change pullbackRepresentationFibreLift B X g y Λ ρ m ≫
      (pullbackRepresentationCoverHom B X g y Λ ρ
        (moduleUnitSection Λ g _ (representationTautologicalSection B X _ Λ ρ))).left ≫
          pullback.fst _ _ = _
    rw [pullbackRepresentationCoverHom_moduleUnitSection]
    exact pullback.lift_fst _ _ _
  unfold pullbackRepresentationEval
  rw [h, Equiv.apply_symm_apply]

/-- The point given by the value of a section at `ū` is `ū` followed by its classifying
morphism. -/
theorem pullbackRepresentationFibreLift_eval
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    {U : Y.Etale} (ū : y.source ⟶ U.left) (hū : ū ≫ U.hom = y.hom)
    (a : ((etaleModuleInverseImage.{u, 0} Λ g).obj
      ((representationSheaf B X (y.map g) Λ).obj ρ)).obj.obj (op U)) :
    pullbackRepresentationFibreLift B X g y Λ ρ (pullbackRepresentationEval B X g y Λ ρ ū hū a) =
      ū ≫ (pullbackRepresentationCoverHom B X g y Λ ρ a).left := by
  apply pullback.hom_ext
  · refine (pullback.lift_fst _ _ _).trans ?_
    unfold pullbackRepresentationEval
    rw [Equiv.symm_apply_apply]
    exact (Category.assoc _ _ _).symm
  · refine (pullback.lift_snd _ _ _).trans ?_
    exact (hū.symm.trans (congrArg (ū ≫ ·)
      (smallEtaleBaseChange_w g (pullbackRepresentationCoverHom B X g y Λ ρ a)).symm)).trans
      (Category.assoc _ _ _).symm

end Local

section Hom

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] {Y : Scheme.{u}} (g : Y ⟶ X.1)
  (y : GeometricPoint Y) (Λ : Type) [Ring Λ] [Finite Λ] (n : ℕ) [NeZero n] [Algebra (ZMod n) Λ]
  (W : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 (y.map g)))

/-- **The map `M → W` of a morphism `φ : res_ψ(g⁻¹ℱ_ρ) ⟶ g⁻¹ℱ_W`**: `m` goes to the value at the
point of `Y ×_X V` given by `m` of `φ(u(ε))`, the image under `φ` of the pulled back tautological
section of `ℱ_ρ`. -/
def pullbackRepresentationHomFun
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    (φ : (etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).obj
        ((etaleModuleInverseImage.{u, 0} Λ g).obj ((representationSheaf B X (y.map g) Λ).obj ρ)) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod n) g).obj
        ((representationSheaf B X (y.map g) (ZMod n)).obj W))
    (m : ρ.obj.obj.obj.V) : W.obj.obj.obj.V :=
  pullbackRepresentationEval B X g y (ZMod n) W (pullbackRepresentationFibreLift B X g y Λ ρ m)
    (pullbackRepresentationFibreLift_hom B X g y Λ ρ m)
    (φ.hom.app (op ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
      (representationCover B X (y.map g) Λ ρ)))
      (moduleUnitSection Λ g _ (representationTautologicalSection B X _ Λ ρ)))

/-- The definition of `AlgebraicGeometry.pullbackRepresentationHomFun`, as an equation. -/
theorem pullbackRepresentationHomFun_def
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    (φ : (etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).obj
        ((etaleModuleInverseImage.{u, 0} Λ g).obj ((representationSheaf B X (y.map g) Λ).obj ρ)) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod n) g).obj
        ((representationSheaf B X (y.map g) (ZMod n)).obj W)) (m : ρ.obj.obj.obj.V) :
    pullbackRepresentationHomFun B X g y Λ n W ρ φ m =
      pullbackRepresentationEval B X g y (ZMod n) W (pullbackRepresentationFibreLift B X g y Λ ρ m)
        (pullbackRepresentationFibreLift_hom B X g y Λ ρ m)
        (φ.hom.app (op ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
          (representationCover B X (y.map g) Λ ρ)))
          (moduleUnitSection Λ g _ (representationTautologicalSection B X _ Λ ρ))) :=
  rfl

/-- **The map `M → W` computes `φ` on every section**: the value of `φ(a)` at `ū` is the image of
the value of `a` at `ū`. -/
theorem pullbackRepresentationHomFun_eval
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    (φ : (etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).obj
        ((etaleModuleInverseImage.{u, 0} Λ g).obj ((representationSheaf B X (y.map g) Λ).obj ρ)) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod n) g).obj
        ((representationSheaf B X (y.map g) (ZMod n)).obj W))
    {U : Y.Etale} (ū : y.source ⟶ U.left) (hū : ū ≫ U.hom = y.hom)
    (a : ((etaleModuleInverseImage.{u, 0} Λ g).obj
      ((representationSheaf B X (y.map g) Λ).obj ρ)).obj.obj (op U)) :
    pullbackRepresentationHomFun B X g y Λ n W ρ φ (pullbackRepresentationEval B X g y Λ ρ ū hū a) =
      pullbackRepresentationEval B X g y (ZMod n) W ū hū (φ.hom.app (op U) a) := by
  set t := pullbackRepresentationCoverHom B X g y Λ ρ a
  have ha : ((etaleModuleInverseImage.{u, 0} Λ g).obj
      ((representationSheaf B X (y.map g) Λ).obj ρ)).obj.map t.op
        (moduleUnitSection Λ g _ (representationTautologicalSection B X _ Λ ρ)) = a :=
    map_pullbackRepresentationCoverHom B X g y Λ ρ a
  have hφ : φ.hom.app (op U) a = ((etaleModuleInverseImage.{u, 0} (ZMod n) g).obj
      ((representationSheaf B X (y.map g) (ZMod n)).obj W)).obj.map t.op
        (φ.hom.app (op ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
          (representationCover B X (y.map g) Λ ρ)))
          (moduleUnitSection Λ g _ (representationTautologicalSection B X _ Λ ρ))) := by
    rw [← ha]
    exact ConcreteCategory.congr_hom (φ.hom.naturality t.op) _
  have hū' : (ū ≫ t.left) ≫ ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
      (representationCover B X (y.map g) Λ ρ)).hom = y.hom :=
    (Category.assoc _ _ _).trans ((congrArg (ū ≫ ·) (smallEtaleBaseChange_w g t)).trans hū)
  rw [hφ, pullbackRepresentationEval_map B X g y (ZMod n) W t ū hū hū']
  exact pullbackRepresentationEval_congr B X g y (ZMod n) W _ _
    (pullbackRepresentationFibreLift_eval B X g y Λ ρ ū hū a) _

/-- **The map `M → W` of `φ` is additive**: `m` and `m'` are the values of the two pulled back
tautological sections on `(Y ×_X V) ×_Y (Y ×_X V)` at the point `(m, m')`, and values are
additive. -/
theorem pullbackRepresentationHomFun_add
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    (φ : (etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).obj
        ((etaleModuleInverseImage.{u, 0} Λ g).obj ((representationSheaf B X (y.map g) Λ).obj ρ)) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod n) g).obj
        ((representationSheaf B X (y.map g) (ZMod n)).obj W))
    (m m' : ρ.obj.obj.obj.V) :
    pullbackRepresentationHomFun B X g y Λ n W ρ φ (m + m') =
      pullbackRepresentationHomFun B X g y Λ n W ρ φ m +
        pullbackRepresentationHomFun B X g y Λ n W ρ φ m' := by
  let V := (Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
      (representationCover B X (y.map g) Λ ρ)
  let U := etaleFiberObj V V
  let ε := moduleUnitSection Λ g _ (representationTautologicalSection B X _ Λ ρ)
  let A := (etaleModuleInverseImage.{u, 0} Λ g).obj ((representationSheaf B X (y.map g) Λ).obj ρ)
  let ū : y.source ⟶ U.left := pullback.lift (pullbackRepresentationFibreLift B X g y Λ ρ m)
    (pullbackRepresentationFibreLift B X g y Λ ρ m')
    ((pullbackRepresentationFibreLift_hom B X g y Λ ρ m).trans
      (pullbackRepresentationFibreLift_hom B X g y Λ ρ m').symm)
  have hū : ū ≫ U.hom = y.hom :=
    (pullback.lift_fst_assoc _ _ _ _).trans (pullbackRepresentationFibreLift_hom B X g y Λ ρ m)
  have key : ∀ (p : U ⟶ V) (m : ρ.obj.obj.obj.V),
      ū ≫ p.left = pullbackRepresentationFibreLift B X g y Λ ρ m →
      pullbackRepresentationEval B X g y Λ ρ ū hū (A.obj.map p.op ε) = m := fun p m hp => by
    rw [pullbackRepresentationEval_map B X g y Λ ρ p ū hū
      (by rw [hp]; exact pullbackRepresentationFibreLift_hom B X g y Λ ρ m)]
    exact (pullbackRepresentationEval_congr B X g y Λ ρ _
      (pullbackRepresentationFibreLift_hom B X g y Λ ρ m) hp ε).trans
      (pullbackRepresentationEval_moduleUnitSection B X g y Λ ρ m)
  have h₁ := key (etaleFiberFst V V) m (pullback.lift_fst _ _ _)
  have h₂ := key (etaleFiberSnd V V) m' (pullback.lift_snd _ _ _)
  rw [← h₁, ← h₂, ← pullbackRepresentationEval_add, pullbackRepresentationHomFun_eval,
    pullbackRepresentationHomFun_eval, pullbackRepresentationHomFun_eval,
    ← pullbackRepresentationEval_add]
  exact congrArg _ (map_add (φ.hom.app (op U)).hom _ _)

/-- **The map `M → W` is additive in `φ`.** -/
theorem pullbackRepresentationHomFun_add_left
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    (φ φ' : (etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).obj
        ((etaleModuleInverseImage.{u, 0} Λ g).obj ((representationSheaf B X (y.map g) Λ).obj ρ)) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod n) g).obj
        ((representationSheaf B X (y.map g) (ZMod n)).obj W))
    (m : ρ.obj.obj.obj.V) :
    pullbackRepresentationHomFun B X g y Λ n W ρ (φ + φ') m =
      pullbackRepresentationHomFun B X g y Λ n W ρ φ m +
        pullbackRepresentationHomFun B X g y Λ n W ρ φ' m := by
  unfold pullbackRepresentationHomFun
  have hadd : ∀ {A A' : ModuleCat.{u + 1} (ZMod n)} (f f' : A ⟶ A') (x : A),
      (f + f') x = f x + f' x := fun _ _ _ => rfl
  rw [Sheaf.Hom.add_app]
  exact (congrArg (pullbackRepresentationEval B X g y (ZMod n) W _
    (pullbackRepresentationFibreLift_hom B X g y Λ ρ m)) (hadd _ _ _)).trans
    (pullbackRepresentationEval_add B X g y (ZMod n) W _ _ _ _)

/-- A morphism between pulled back representing covers, as a morphism of finite étale covers
of `Y`. -/
def pullbackRepresentationCoverFiniteEtaleHom {R R' : Type} [Ring R] [Finite R] [Ring R']
    [Finite R']
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1 (y.map g)))
    (σ : FiniteTypeContinuousModule.{0, u + 1, u + 1} R' (EtaleFundamentalGroup X.1 (y.map g)))
    (t : (Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
      (representationCover B X (y.map g) R ρ) ⟶
      (Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
        (representationCover B X (y.map g) R' σ)) :
    (finiteEtaleBaseChange g).obj (representationFiniteEtaleCover B X (y.map g) R ρ) ⟶
      (finiteEtaleBaseChange g).obj (representationFiniteEtaleCover B X (y.map g) R' σ) :=
  MorphismProperty.Over.homMk t.left (smallEtaleBaseChange_w g t) trivial

/-- The underlying morphism of schemes of `pullbackRepresentationCoverFiniteEtaleHom t` is that
of `t`. -/
theorem pullbackRepresentationCoverFiniteEtaleHom_left {R R' : Type} [Ring R] [Finite R] [Ring R']
    [Finite R']
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1 (y.map g)))
    (σ : FiniteTypeContinuousModule.{0, u + 1, u + 1} R' (EtaleFundamentalGroup X.1 (y.map g)))
    (t : (Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
      (representationCover B X (y.map g) R ρ) ⟶
      (Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
        (representationCover B X (y.map g) R' σ)) :
    (pullbackRepresentationCoverFiniteEtaleHom B X g y ρ σ t).left = t.left :=
  CategoryTheory.Over.homMk_left _ (smallEtaleBaseChange_w g t)

/-- `pullbackRepresentationCoverFiniteEtaleHom` is injective. -/
theorem pullbackRepresentationCoverFiniteEtaleHom_injective {R R' : Type} [Ring R] [Finite R]
    [Ring R'] [Finite R']
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1 (y.map g)))
    (σ : FiniteTypeContinuousModule.{0, u + 1, u + 1} R' (EtaleFundamentalGroup X.1 (y.map g))) :
    Function.Injective (pullbackRepresentationCoverFiniteEtaleHom B X g y ρ σ) := fun t t' h =>
  MorphismProperty.Over.Hom.ext
    ((pullbackRepresentationCoverFiniteEtaleHom_left B X g y ρ σ t).symm.trans
      ((congrArg (fun k => k.left) h).trans
        (pullbackRepresentationCoverFiniteEtaleHom_left B X g y ρ σ t')))

/-- **The point of the fibre given by a morphism of pulled back representing covers at the point
given by `m` is the map on geometric fibres at `y` of the corresponding morphism of finite étale
covers**, read through the fibre projections
(`AlgebraicGeometry.finiteEtaleFiberProjectionEquiv`). -/
theorem pullbackRepresentationFibrePoint_eq_fiber {R R' : Type} [Ring R] [Finite R] [Ring R']
    [Finite R']
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1 (y.map g)))
    (σ : FiniteTypeContinuousModule.{0, u + 1, u + 1} R' (EtaleFundamentalGroup X.1 (y.map g)))
    (t : (Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
      (representationCover B X (y.map g) R ρ) ⟶
      (Stacks.EtaleCohomology.smallEtaleBaseChange g).obj (representationCover B X (y.map g) R' σ))
    (m : ρ.obj.obj.obj.V)
    (h : pullbackRepresentationFibreLift B X g y R ρ m ≫
      ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
        (representationCover B X (y.map g) R ρ)).hom = y.hom) :
    pullbackRepresentationFibrePoint B X g y R' σ t
      (pullbackRepresentationFibreLift B X g y R ρ m) h =
      finiteEtaleFiberProjection g y _
        ((finiteEtaleFiberFunctor y).map (pullbackRepresentationCoverFiniteEtaleHom B X g y ρ σ t)
          ((finiteEtaleFiberProjectionEquiv g y _).symm
            ((representationFibreEquiv B X (y.map g) R ρ).symm m))) :=
  Subtype.ext (Category.assoc _ _ _).symm

/-- **`φ` is determined by `φ(u(ε))`**: on a section `a` over `U` it is the restriction of
`φ(u(ε))` along the classifying morphism of `a`. -/
theorem pullbackRepresentationHom_app_eq
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    (φ : (etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).obj
        ((etaleModuleInverseImage.{u, 0} Λ g).obj ((representationSheaf B X (y.map g) Λ).obj ρ)) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod n) g).obj
        ((representationSheaf B X (y.map g) (ZMod n)).obj W))
    {U : Y.Etale}
    (a : ((etaleModuleInverseImage.{u, 0} Λ g).obj
      ((representationSheaf B X (y.map g) Λ).obj ρ)).obj.obj (op U)) :
    φ.hom.app (op U) a = ((etaleModuleInverseImage.{u, 0} (ZMod n) g).obj
      ((representationSheaf B X (y.map g) (ZMod n)).obj W)).obj.map
        (pullbackRepresentationCoverHom B X g y Λ ρ a).op
        (φ.hom.app (op ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
          (representationCover B X (y.map g) Λ ρ)))
          (moduleUnitSection Λ g _ (representationTautologicalSection B X _ Λ ρ))) := by
  conv_lhs => rw [← map_pullbackRepresentationCoverHom B X g y Λ ρ a]
  exact ConcreteCategory.congr_hom
    (φ.hom.naturality (pullbackRepresentationCoverHom B X g y Λ ρ a).op) _

omit [ConnectedSpace X.1] in
/-- A fibre projection followed by its inverse is the identity. -/
theorem finiteEtaleFiberProjectionEquiv_symm_projection (V : FiniteEtaleOver X.1)
    (z : finiteEtaleFiber y ((finiteEtaleBaseChange g).obj V)) :
    (finiteEtaleFiberProjectionEquiv g y V).symm (finiteEtaleFiberProjection g y V z) = z :=
  (finiteEtaleFiberProjectionEquiv g y V).symm_apply_apply z

/-- **The map `M → W` is natural in `ρ`**: for `v : ρ ⟶ ρ'`, the map of `res_ψ(g⁻¹ℱ_v) ≫ φ'` is
the map of `φ'` precomposed with `v`. -/
theorem pullbackRepresentationHomFun_naturality
    {ρ ρ' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g))}
    (v : ρ ⟶ ρ')
    (φ' : (etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).obj
        ((etaleModuleInverseImage.{u, 0} Λ g).obj ((representationSheaf B X (y.map g) Λ).obj ρ')) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod n) g).obj
        ((representationSheaf B X (y.map g) (ZMod n)).obj W))
    (m : ρ.obj.obj.obj.V) :
    pullbackRepresentationHomFun B X g y Λ n W ρ
        ((etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).map
          ((etaleModuleInverseImage.{u, 0} Λ g).map ((representationSheaf B X (y.map g) Λ).map v)) ≫
          φ') m =
      pullbackRepresentationHomFun B X g y Λ n W ρ' φ' (v.hom.hom.hom.hom.hom m) := by
  have hv : v.hom.hom.hom.hom.hom m = pullbackRepresentationEval B X g y Λ ρ'
      (pullbackRepresentationFibreLift B X g y Λ ρ m)
        (pullbackRepresentationFibreLift_hom B X g y Λ ρ m)
      (((etaleModuleInverseImage.{u, 0} Λ g).map
        ((representationSheaf B X (y.map g) Λ).map v)).hom.app
        (op ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
          (representationCover B X (y.map g) Λ ρ)))
        (moduleUnitSection Λ g _ (representationTautologicalSection B X _ Λ ρ))) := by
    rw [pullbackRepresentationEval_naturality, pullbackRepresentationEval_moduleUnitSection]
  rw [hv, pullbackRepresentationHomFun_eval, pullbackRepresentationHomFun_def]
  rfl

variable [ConnectedSpace Y]

/-- **The functor `ρ ↦ Hom_{π₁(Y)}(M, W)`**: the `π₁(Y, y)`-invariants of `Hom_ℤ(M, W)` with the
conjugation action (`Stacks.GroupCohomology.homDualFunctor`), `π₁(Y, y)` acting through
`π₁(Y, y) → π₁(X, x)`; contravariant in `ρ`, to `Λᵐᵒᵖ`-modules. -/
abbrev pullbackRepresentationHomInvariants :
    (FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))ᵒᵖ ⥤
      ModuleCat.{u + 1} Λᵐᵒᵖ :=
  homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
      (EtaleFundamentalGroup X.1 (y.map g))).obj W.obj) ⋙
    finiteTypeContinuousModuleRes Λᵐᵒᵖ (etaleFundamentalGroupMap g y) ⋙
    finiteTypeContinuousModuleInvariants Λᵐᵒᵖ (EtaleFundamentalGroup Y y)

omit [Algebra (ZMod n) Λ] in
/-- **The map on geometric fibres of a morphism of pulled back representing covers is
equivariant**: `π₁(Y, y)` acts on both fibres by monodromy, compatibly with the fibre projections
to the fibres at `x`, on which it acts through `π₁(Y, y) → π₁(X, x)` (Tag 0BND (3)). -/
theorem pullbackRepresentationFibreMap_smul
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    (t : (Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
      (representationCover B X (y.map g) Λ ρ) ⟶
      (Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
        (representationCover B X (y.map g) (ZMod n) W))
    (γ : EtaleFundamentalGroup Y y) (m : ρ.obj.obj.obj.V) :
    representationFibreEquiv B X (y.map g) (ZMod n) W (finiteEtaleFiberProjection g y _
        ((finiteEtaleFiberFunctor y).map (pullbackRepresentationCoverFiniteEtaleHom B X g y ρ W t)
          ((finiteEtaleFiberProjectionEquiv g y _).symm
            ((representationFibreEquiv B X (y.map g) Λ ρ).symm
              (finiteTypeContinuousModuleRepresentation Λ _ ρ
                (etaleFundamentalGroupMap g y γ) m))))) =
      finiteTypeContinuousModuleRepresentation (ZMod n) _ W (etaleFundamentalGroupMap g y γ)
        (representationFibreEquiv B X (y.map g) (ZMod n) W (finiteEtaleFiberProjection g y _
        ((finiteEtaleFiberFunctor y).map (pullbackRepresentationCoverFiniteEtaleHom B X g y ρ W t)
          ((finiteEtaleFiberProjectionEquiv g y _).symm
            ((representationFibreEquiv B X (y.map g) Λ ρ).symm m))))) := by
  have h1 : (representationFibreEquiv B X (y.map g) Λ ρ).symm
      (finiteTypeContinuousModuleRepresentation Λ _ ρ (etaleFundamentalGroupMap g y γ) m) =
      finiteEtaleFiberProjection g y _
        ((γ.app ((finiteEtaleBaseChange g).obj
          (representationFiniteEtaleCover B X (y.map g) Λ ρ))).hom
          ((finiteEtaleFiberProjectionEquiv g y _).symm
            ((representationFibreEquiv B X (y.map g) Λ ρ).symm m))) := by
    rw [Equiv.symm_apply_eq]
    refine Eq.trans ?_ (representationFibreEquiv_smul B X (y.map g) Λ ρ
      (etaleFundamentalGroupMap g y γ) _).symm
    rw [Equiv.apply_symm_apply]
  have hnat := ConcreteCategory.congr_hom
    (γ.hom.naturality (pullbackRepresentationCoverFiniteEtaleHom B X g y ρ W t))
    ((finiteEtaleFiberProjectionEquiv g y _).symm
      ((representationFibreEquiv B X (y.map g) Λ ρ).symm m))
  rw [h1, finiteEtaleFiberProjectionEquiv_symm_projection]
  have hnat' : (finiteEtaleFiberFunctor y).map
      (pullbackRepresentationCoverFiniteEtaleHom B X g y ρ W t)
      ((γ.app ((finiteEtaleBaseChange g).obj
        (representationFiniteEtaleCover B X (y.map g) Λ ρ))).hom
        ((finiteEtaleFiberProjectionEquiv g y _).symm
          ((representationFibreEquiv B X (y.map g) Λ ρ).symm m))) =
      (γ.app ((finiteEtaleBaseChange g).obj
          (representationFiniteEtaleCover B X (y.map g) (ZMod n) W))).hom
        ((finiteEtaleFiberFunctor y).map (pullbackRepresentationCoverFiniteEtaleHom B X g y ρ W t)
          ((finiteEtaleFiberProjectionEquiv g y _).symm
            ((representationFibreEquiv B X (y.map g) Λ ρ).symm m))) := by
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
    exact hnat.symm
  rw [hnat']
  have hs := representationFibreEquiv_smul B X (y.map g) (ZMod n) W (etaleFundamentalGroupMap g y γ)
    (finiteEtaleFiberProjection g y _ ((finiteEtaleFiberFunctor y).map
      (pullbackRepresentationCoverFiniteEtaleHom B X g y ρ W t)
        ((finiteEtaleFiberProjectionEquiv g y _).symm
          ((representationFibreEquiv B X (y.map g) Λ ρ).symm m))))
  rw [← hs]
  refine congrArg (representationFibreEquiv B X (y.map g) (ZMod n) W) ?_
  refine Eq.trans ?_ (etaleFundamentalGroupMonoidHom_app_apply g y _ γ _).symm
  rw [finiteEtaleFiberProjectionEquiv_symm_projection]

omit [Algebra (ZMod n) Λ] in
/-- **A morphism of pulled back representing covers is determined by its map on the geometric
fibres at `y`**, read in `M` and `W`: the fibre functor of the connected scheme `Y` is faithful
(Tag 0BN0). -/
theorem pullbackRepresentationCoverHom_ext_fibre
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    (t t' : (Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
      (representationCover B X (y.map g) Λ ρ) ⟶
      (Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
        (representationCover B X (y.map g) (ZMod n) W))
    (h : ∀ m, representationFibreEquiv B X (y.map g) (ZMod n) W
      (pullbackRepresentationFibrePoint B X g y (ZMod n) W t
        (pullbackRepresentationFibreLift B X g y Λ ρ m)
        (pullbackRepresentationFibreLift_hom B X g y Λ ρ m)) =
      representationFibreEquiv B X (y.map g) (ZMod n) W
      (pullbackRepresentationFibrePoint B X g y (ZMod n) W t'
        (pullbackRepresentationFibreLift B X g y Λ ρ m)
        (pullbackRepresentationFibreLift_hom B X g y Λ ρ m))) : t = t' := by
  have hF : (finiteEtaleFiberFunctor y).map
      (pullbackRepresentationCoverFiniteEtaleHom B X g y ρ W t) =
      (finiteEtaleFiberFunctor y).map
        (pullbackRepresentationCoverFiniteEtaleHom B X g y ρ W t') := by
    refine ConcreteCategory.hom_ext _ _ fun z => ?_
    have hm := h (representationFibreEquiv B X (y.map g) Λ ρ (finiteEtaleFiberProjection g y _ z))
    rw [pullbackRepresentationFibrePoint_eq_fiber, pullbackRepresentationFibrePoint_eq_fiber] at hm
    have hz : (finiteEtaleFiberProjectionEquiv g y _).symm
        ((representationFibreEquiv B X (y.map g) Λ ρ).symm
        (representationFibreEquiv B X (y.map g) Λ ρ (finiteEtaleFiberProjection g y _ z))) = z := by
      rw [Equiv.symm_apply_apply, finiteEtaleFiberProjectionEquiv_symm_projection]
    rw [hz] at hm
    exact (finiteEtaleFiberProjectionEquiv g y _).injective
      ((representationFibreEquiv B X (y.map g) (ZMod n) W).injective hm)
  exact pullbackRepresentationCoverFiniteEtaleHom_injective B X g y ρ W
    ((finiteEtaleFiberFunctor y).map_injective hF)

/-- **The map `M → W` of `φ` is equivariant under `π₁(Y, y)`**, acting through
`π₁(Y, y) → π₁(X, x)`: the morphism of finite étale covers classifying `φ(u(ε))` commutes with
the monodromy on the geometric fibres at `y`. -/
theorem pullbackRepresentationHomFun_map_smul
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    (φ : (etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).obj
        ((etaleModuleInverseImage.{u, 0} Λ g).obj ((representationSheaf B X (y.map g) Λ).obj ρ)) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod n) g).obj
        ((representationSheaf B X (y.map g) (ZMod n)).obj W))
    (γ : EtaleFundamentalGroup Y y) (m : ρ.obj.obj.obj.V) :
    pullbackRepresentationHomFun B X g y Λ n W ρ φ
        (finiteTypeContinuousModuleRepresentation Λ _ ρ (etaleFundamentalGroupMap g y γ) m) =
      finiteTypeContinuousModuleRepresentation (ZMod n) _ W (etaleFundamentalGroupMap g y γ)
        (pullbackRepresentationHomFun B X g y Λ n W ρ φ m) := by
  rw [pullbackRepresentationHomFun_def, pullbackRepresentationHomFun_def,
    pullbackRepresentationEval_def, pullbackRepresentationEval_def,
    pullbackRepresentationFibrePoint_eq_fiber, pullbackRepresentationFibrePoint_eq_fiber]
  exact pullbackRepresentationFibreMap_smul B X g y Λ n W ρ _ γ m

/-- **A morphism `res_ψ(g⁻¹ℱ_ρ) ⟶ g⁻¹ℱ_W` is determined by its map `M → W`**: that map is the
morphism of finite étale covers classifying `φ(u(ε))` on geometric fibres at `y`, the fibre functor
of the connected scheme `Y` is faithful (Tag 0BN0), and `φ` is determined by `φ(u(ε))`. -/
theorem pullbackRepresentationHomFun_injective
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g))) :
    Function.Injective (pullbackRepresentationHomFun B X g y Λ n W ρ) := by
  intro φ φ' h
  have hττ := pullbackRepresentationCoverHom_ext_fibre B X g y Λ n W ρ
    (pullbackRepresentationCoverHom B X g y (ZMod n) W
      (φ.hom.app (op ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
        (representationCover B X (y.map g) Λ ρ)))
        (moduleUnitSection Λ g _ (representationTautologicalSection B X _ Λ ρ))))
    (pullbackRepresentationCoverHom B X g y (ZMod n) W
      (φ'.hom.app (op ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
        (representationCover B X (y.map g) Λ ρ)))
        (moduleUnitSection Λ g _ (representationTautologicalSection B X _ Λ ρ)))) (fun m => by
      have hm := congrFun h m
      rw [pullbackRepresentationHomFun_def, pullbackRepresentationHomFun_def,
        pullbackRepresentationEval_def, pullbackRepresentationEval_def] at hm
      exact hm)
  have hc : φ.hom.app (op ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
        (representationCover B X (y.map g) Λ ρ)))
        (moduleUnitSection Λ g _ (representationTautologicalSection B X _ Λ ρ)) =
      φ'.hom.app (op ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
        (representationCover B X (y.map g) Λ ρ)))
        (moduleUnitSection Λ g _ (representationTautologicalSection B X _ Λ ρ)) := by
    refine (map_pullbackRepresentationCoverHom B X g y (ZMod n) W _).symm.trans ?_
    refine Eq.trans ?_ (map_pullbackRepresentationCoverHom B X g y (ZMod n) W _)
    rw [hττ]
  refine Sheaf.hom_ext (NatTrans.ext
    (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun a => ?_)))
  change φ.hom.app U a = φ'.hom.app U a
  rw [pullbackRepresentationHom_app_eq B X g y Λ n W ρ φ a,
    pullbackRepresentationHom_app_eq B X g y Λ n W ρ φ' a]
  exact congrArg _ hc

/-- **The map `M → W` of `φ` lies in `Hom_{π₁(Y)}(M, W)`**: it is additive and invariant under the
conjugation action of `π₁(Y, y)` on `Hom_ℤ(M, W)` (`Stacks.GroupCohomology.homDualFunctor`). -/
theorem pullbackRepresentationHomFun_mem
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    (φ : (etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).obj
        ((etaleModuleInverseImage.{u, 0} Λ g).obj ((representationSheaf B X (y.map g) Λ).obj ρ)) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod n) g).obj
        ((representationSheaf B X (y.map g) (ZMod n)).obj W)) :
    AddMonoidHom.mk' (pullbackRepresentationHomFun B X g y Λ n W ρ φ)
        (pullbackRepresentationHomFun_add B X g y Λ n W ρ φ) ∈
      finiteTypeContinuousModuleInvariantsSubmodule Λᵐᵒᵖ (EtaleFundamentalGroup Y y)
        ((finiteTypeContinuousModuleRes Λᵐᵒᵖ (etaleFundamentalGroupMap g y)).obj
          ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
            (EtaleFundamentalGroup X.1 (y.map g))).obj W.obj)).obj (op ρ))) := by
  intro γ
  refine AddMonoidHom.ext fun m => ?_
  have h := pullbackRepresentationHomFun_map_smul B X g y Λ n W ρ φ γ⁻¹ m
  rw [map_inv] at h
  change finiteTypeContinuousModuleRepresentation (ZMod n) _ W (etaleFundamentalGroupMap g y γ)
      (pullbackRepresentationHomFun B X g y Λ n W ρ φ
        (finiteTypeContinuousModuleRepresentation Λ _ ρ (etaleFundamentalGroupMap g y γ)⁻¹ m)) =
    pullbackRepresentationHomFun B X g y Λ n W ρ φ m
  rw [h, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-- The additive map `M → W` underlying an element of `Hom_{π₁(Y)}(M, W)`. -/
def pullbackRepresentationHomInvariantsToHom
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    (b : (pullbackRepresentationHomInvariants B X g y Λ n W).obj (op ρ)) :
    ρ.obj.obj.obj.V →+ W.obj.obj.obj.V :=
  b.1

omit [Algebra (ZMod n) Λ] in
/-- Elements of `Hom_{π₁(Y)}(M, W)` are determined by their additive maps. -/
theorem pullbackRepresentationHomInvariantsToHom_injective
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g))) :
    Function.Injective (pullbackRepresentationHomInvariantsToHom B X g y Λ n W ρ) :=
  fun _ _ h => Subtype.ext h

/-- **`φ ↦ (m ↦ φ at m)`, `Hom(res_ψ(g⁻¹ℱ_ρ), g⁻¹ℱ_W) → Hom_{π₁(Y)}(M, W)`**, as an additive
map (`AlgebraicGeometry.pullbackRepresentationHomFun`). -/
def pullbackRepresentationHomToInvariants
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g))) :
    ((etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).obj
        ((etaleModuleInverseImage.{u, 0} Λ g).obj ((representationSheaf B X (y.map g) Λ).obj ρ)) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod n) g).obj
        ((representationSheaf B X (y.map g) (ZMod n)).obj W)) →+
      (pullbackRepresentationHomInvariants B X g y Λ n W).obj (op ρ) :=
  AddMonoidHom.mk' (fun φ => ⟨AddMonoidHom.mk' (pullbackRepresentationHomFun B X g y Λ n W ρ φ)
      (pullbackRepresentationHomFun_add B X g y Λ n W ρ φ),
      pullbackRepresentationHomFun_mem B X g y Λ n W ρ φ⟩)
    fun φ φ' => Subtype.ext (AddMonoidHom.ext fun m =>
      pullbackRepresentationHomFun_add_left B X g y Λ n W ρ φ φ' m)

/-- The invariant additive map of `φ` sends `m` to `pullbackRepresentationHomFun φ m`. -/
theorem pullbackRepresentationHomToInvariants_apply
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    (φ : (etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).obj
        ((etaleModuleInverseImage.{u, 0} Λ g).obj ((representationSheaf B X (y.map g) Λ).obj ρ)) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod n) g).obj
        ((representationSheaf B X (y.map g) (ZMod n)).obj W)) (m : ρ.obj.obj.obj.V) :
    pullbackRepresentationHomInvariantsToHom B X g y Λ n W ρ
        (pullbackRepresentationHomToInvariants B X g y Λ n W ρ φ) m =
      pullbackRepresentationHomFun B X g y Λ n W ρ φ m :=
  rfl

/-- `pullbackRepresentationHomToInvariants` is injective. -/
theorem pullbackRepresentationHomToInvariants_injective
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g))) :
    Function.Injective (pullbackRepresentationHomToInvariants B X g y Λ n W ρ) := fun _ _ h =>
  pullbackRepresentationHomFun_injective B X g y Λ n W ρ (funext fun m =>
    congrArg (fun z => pullbackRepresentationHomInvariantsToHom B X g y Λ n W ρ z m) h)

/-- **The additive map to `Hom_{π₁(Y)}(M, W)` is natural in `ρ`.** -/
theorem pullbackRepresentationHomToInvariants_naturality
    {ρ ρ' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g))}
    (v : ρ ⟶ ρ') (φ' : (etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).obj
        ((etaleModuleInverseImage.{u, 0} Λ g).obj ((representationSheaf B X (y.map g) Λ).obj ρ')) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod n) g).obj
        ((representationSheaf B X (y.map g) (ZMod n)).obj W)) :
    pullbackRepresentationHomToInvariants B X g y Λ n W ρ
        ((etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).map
          ((etaleModuleInverseImage.{u, 0} Λ g).map ((representationSheaf B X (y.map g) Λ).map v)) ≫
          φ') =
      (pullbackRepresentationHomInvariants B X g y Λ n W).map v.op
        (pullbackRepresentationHomToInvariants B X g y Λ n W ρ' φ') :=
  pullbackRepresentationHomInvariantsToHom_injective B X g y Λ n W ρ (AddMonoidHom.ext fun m =>
    pullbackRepresentationHomFun_naturality B X g y Λ n W v φ' m)

end Hom

section Count

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (Y : Scheme.{u})
  (hY : B.Contains Y) [ConnectedSpace Y] (g : Y ⟶ X.1) (y : GeometricPoint Y) (Λ : Type) [Ring Λ]
  [Finite Λ]
  (n : ℕ) [NeZero n] [Algebra (ZMod n) Λ]
  (W : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 (y.map g)))

include hY in
/-- **`Hom(res_ψ(g⁻¹ℱ_ρ), g⁻¹ℱ_W)` has as many elements as `Hom_{π₁(Y)}(M, W)`.** Through the
isomorphisms `g⁻¹ℱ_ρ ≅ ℱ_{ρ|π₁(Y)}` of Tag 0DV6
(`AlgebraicGeometry.representationSheafPullbackIso`, for any choice), a morphism is a global
section of `SheafHom_{ℤ/n}(ℱ_{ρ|}, ℱ_{W|}) = ℱ_{Hom_ℤ(M, W)}`
(`AlgebraicGeometry.representationSheafModuleSheafHomIso`), and global sections of `ℱ_N` are the
invariants `N^{π₁(Y)}` (`AlgebraicGeometry.representationSheafGlobalSectionsIso`).
Only the cardinality is used, so the choice made in Tag 0DV6 does not matter. -/
theorem nat_card_pullbackRepresentationHom
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g))) :
    Nat.card ((etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).obj
        ((etaleModuleInverseImage.{u, 0} Λ g).obj
          ((representationSheaf B X (y.map g) Λ).obj ρ)) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod n) g).obj
        ((representationSheaf B X (y.map g) (ZMod n)).obj W)) =
    Nat.card (finiteTypeContinuousModuleInvariantsSubmodule Λᵐᵒᵖ (EtaleFundamentalGroup Y y)
        ((finiteTypeContinuousModuleRes Λᵐᵒᵖ (etaleFundamentalGroupMap g y)).obj
          ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
            (EtaleFundamentalGroup X.1 (y.map g))).obj W.obj)).obj (op ρ)))) := by
  let Y' : B.Scheme := ⟨Y, hY⟩
  have : ConnectedSpace Y'.1 := ‹ConnectedSpace Y›
  let g' : Y' ⟶ X := ObjectProperty.homMk g
  let σ := (finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap g y)).obj ρ
  let τ := (finiteTypeContinuousModuleRes (ZMod n) (etaleFundamentalGroupMap g y)).obj W
  have : Module.Finite (ZMod n) τ.obj.obj.obj.V := τ.property
  have : Finite τ.obj.obj.obj.V := Module.finite_of_finite (ZMod n)
  have : Finite ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
      (EtaleFundamentalGroup Y y)).obj τ.obj).obj.obj.V :=
    inferInstanceAs (Finite τ.obj.obj.obj.V)
  let N := (homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
    (EtaleFundamentalGroup Y y)).obj τ.obj)).obj (op σ)
  let e₁ := Iso.homCongr ((etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).mapIso
    ((representationSheafPullbackIso B g' Λ y).app ρ))
    ((representationSheafPullbackIso B g' (ZMod n) y).app W)
  let e₂ := (Stacks.ConstantSheaf.overPullbackFullyFaithfulOfIsTerminal Y.smallEtaleTopology
    (ModuleCat.{u + 1} (ZMod n)) terminalIsTerminal).homEquiv
    (X := (etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).obj
      ((representationSheaf B Y' y Λ).obj σ)) (Y := (representationSheaf B Y' y (ZMod n)).obj τ)
  let e₃ := (((sheafToPresheaf _ _).mapIso
    (representationSheafModuleSheafHomIso B Y' y Λ n σ τ)).app
      (op (⊤_ Y.Etale))).toLinearEquiv.toEquiv
  let e₄ := ((Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λᵐᵒᵖ)
    terminalIsTerminal).app ((representationSheaf B Y' y Λᵐᵒᵖ).obj N)).toLinearEquiv.toEquiv.symm
  let e₅ := ((representationSheafGlobalSectionsIso B Y' y Λᵐᵒᵖ).app N).toLinearEquiv.toEquiv
  let e₆ : (finiteTypeContinuousModuleInvariantsSubmodule Λᵐᵒᵖ (EtaleFundamentalGroup Y y) N) ≃
      (finiteTypeContinuousModuleInvariantsSubmodule Λᵐᵒᵖ (EtaleFundamentalGroup Y y)
        ((finiteTypeContinuousModuleRes Λᵐᵒᵖ (etaleFundamentalGroupMap g y)).obj
          ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
            (EtaleFundamentalGroup X.1 (y.map g))).obj W.obj)).obj (op ρ)))) :=
    Equiv.subtypeEquivRight fun h => by
      refine forall_congr' fun γ => ?_
      have hγ : ConcreteCategory.hom (N.obj.obj.obj.ρ γ) h =
          ConcreteCategory.hom
            (((finiteTypeContinuousModuleRes Λᵐᵒᵖ (etaleFundamentalGroupMap g y)).obj
              ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
                (EtaleFundamentalGroup X.1 (y.map g))).obj W.obj)).obj (op ρ))).obj.obj.obj.ρ
              γ) h := by
        refine AddMonoidHom.ext fun m => ?_
        let h' : ρ.obj.obj.obj.V →+ W.obj.obj.obj.V := h
        change (W.obj.obj.obj.ρ (etaleFundamentalGroupMap g y γ)).hom
            (h' ((ρ.obj.obj.obj.ρ (etaleFundamentalGroupMap g y γ⁻¹)).hom m)) =
          (W.obj.obj.obj.ρ (etaleFundamentalGroupMap g y γ)).hom
            (h' ((ρ.obj.obj.obj.ρ (etaleFundamentalGroupMap g y γ)⁻¹).hom m))
        rw [map_inv]
      rw [hγ]
      exact Iff.rfl
  exact Nat.card_congr (e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans (Equiv.ulift.trans e₆))))))

/-- `Hom_{π₁(Y)}(M, W)` is finite. -/
instance finite_pullbackRepresentationHomInvariants_obj
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g))) :
    Finite ((pullbackRepresentationHomInvariants B X g y Λ n W).obj (op ρ)) :=
  haveI : Module.Finite Λ ρ.obj.obj.obj.V := ρ.property
  haveI : Finite ρ.obj.obj.obj.V := Module.finite_of_finite Λ
  haveI : Module.Finite (ZMod n) W.obj.obj.obj.V := W.property
  haveI : Finite W.obj.obj.obj.V := Module.finite_of_finite (ZMod n)
  haveI : Finite (ρ.obj.obj.obj.V →+ W.obj.obj.obj.V) :=
    Finite.of_injective _ DFunLike.coe_injective
  Finite.of_injective _ (pullbackRepresentationHomInvariantsToHom_injective B X g y Λ n W ρ)

include hY in
/-- **The map to `Hom_{π₁(Y)}(M, W)` is bijective**: it is injective
(`AlgebraicGeometry.pullbackRepresentationHomFun_injective`, choice-free), and both sides have the
same finite number of elements (`AlgebraicGeometry.nat_card_pullbackRepresentationHom`, which uses
the existence-only isomorphisms of Tag 0DV6, inside this proof only). -/
theorem bijective_pullbackRepresentationHomToInvariants
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g))) :
    Function.Bijective (pullbackRepresentationHomToInvariants B X g y Λ n W ρ) :=
  (pullbackRepresentationHomToInvariants_injective B X g y Λ n W ρ).bijective_of_nat_card_le
    (nat_card_pullbackRepresentationHom B X Y hY g y Λ n W ρ).ge

/-- The morphisms `res_ψ(g⁻¹ℱ_ρ) ⟶ g⁻¹ℱ_W` form a finite set. -/
instance finite_pullbackRepresentationHom
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g))) :
    Finite ((etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).obj
        ((etaleModuleInverseImage.{u, 0} Λ g).obj
          ((representationSheaf B X (y.map g) Λ).obj ρ)) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod n) g).obj
        ((representationSheaf B X (y.map g) (ZMod n)).obj W)) :=
  Finite.of_injective _ (pullbackRepresentationHomToInvariants_injective B X g y Λ n W ρ)

/-- **`Φ_ρ : Hom(res_ψ(g⁻¹ℱ_ρ), g⁻¹ℱ_W) ≃ Hom_{π₁(Y, y)}(M, W)`.** A morphism `φ` of sheaves of
`ℤ/n`-modules on `Y_étale` goes to the additive map `M → W` it induces on the geometric fibres at
`y` (`AlgebraicGeometry.pullbackRepresentationHomFun`): `m` goes to the value at the point `m` of
`Y ×_X V` of `φ(u(ε))`, `u(ε)` the pulled back tautological section of `ℱ_ρ` over its
representing cover `V`. The map is canonical: no isomorphism is chosen in it. The existence-only
isomorphism of Tag 0DV6 (`AlgebraicGeometry.representationSheafPullbackIso`) enters only the proof
that it is bijective, by counting
(`AlgebraicGeometry.bijective_pullbackRepresentationHomToInvariants`). It is natural in `ρ`
(`AlgebraicGeometry.pullbackRepresentationHomEquiv_naturality`). -/
def pullbackRepresentationHomEquiv
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g))) :
    ((etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).obj
        ((etaleModuleInverseImage.{u, 0} Λ g).obj
          ((representationSheaf B X (y.map g) Λ).obj ρ)) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod n) g).obj
        ((representationSheaf B X (y.map g) (ZMod n)).obj W)) ≃+
      (pullbackRepresentationHomInvariants B X g y Λ n W).obj (op ρ) :=
  AddEquiv.ofBijective (pullbackRepresentationHomToInvariants B X g y Λ n W ρ)
    (bijective_pullbackRepresentationHomToInvariants B X Y hY g y Λ n W ρ)

/-- `Φ_ρ(φ)` is the map `M → W` that `φ` induces at `y`. -/
theorem pullbackRepresentationHomEquiv_apply
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g)))
    (φ : (etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).obj
        ((etaleModuleInverseImage.{u, 0} Λ g).obj
          ((representationSheaf B X (y.map g) Λ).obj ρ)) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod n) g).obj
        ((representationSheaf B X (y.map g) (ZMod n)).obj W)) (m : ρ.obj.obj.obj.V) :
    pullbackRepresentationHomInvariantsToHom B X g y Λ n W ρ
        (pullbackRepresentationHomEquiv B X Y hY g y Λ n W ρ φ) m =
      pullbackRepresentationHomFun B X g y Λ n W ρ φ m :=
  rfl

/-- **`Φ_ρ` is natural in `ρ`**: precomposition with `res_ψ(g⁻¹ℱ_v)` corresponds to precomposition
with `v`. -/
theorem pullbackRepresentationHomEquiv_naturality
    {ρ ρ' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map g))}
    (v : ρ ⟶ ρ') (φ' : (etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).obj
        ((etaleModuleInverseImage.{u, 0} Λ g).obj
          ((representationSheaf B X (y.map g) Λ).obj ρ')) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod n) g).obj
        ((representationSheaf B X (y.map g) (ZMod n)).obj W)) :
    pullbackRepresentationHomEquiv B X Y hY g y Λ n W ρ
        ((etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) Y).map
          ((etaleModuleInverseImage.{u, 0} Λ g).map
            ((representationSheaf B X (y.map g) Λ).map v)) ≫ φ') =
      (pullbackRepresentationHomInvariants B X g y Λ n W).map v.op
        (pullbackRepresentationHomEquiv B X Y hY g y Λ n W ρ' φ') :=
  pullbackRepresentationHomToInvariants_naturality B X g y Λ n W v φ'

end Count

section GlobalSections

variable {R Λ : Type} [Ring R] [Ring Λ] (ψ : R →+* Λ) (Y : Scheme.{u})

/-- `Γ(res_ψ G) = res_ψ Γ(G)` read at a terminal object `T` is the identity of `G(T)`. -/
theorem etaleModuleGlobalSectionsRestrictScalars_hom_ΓRes (G : EtaleModules.{u, 0} Λ Y)
    (T : Y.Etale) :
    ((etaleModuleGlobalSectionsRestrictScalars ψ Y).app G).hom ≫
      Sheaf.ΓRes ((etaleModuleRestrictScalars ψ Y).obj G) (op T) =
      (ModuleCat.restrictScalars.{u + 1} ψ).map (Sheaf.ΓRes G (op T)) := by
  have h1 : ((etaleModuleGlobalSectionsRestrictScalars ψ Y).app G).hom ≫
      Sheaf.ΓRes ((etaleModuleRestrictScalars ψ Y).obj G) (op (⊤_ Y.Etale)) =
      (ModuleCat.restrictScalars.{u + 1} ψ).map (Sheaf.ΓRes G (op (⊤_ Y.Etale))) := by
    rw [← Sheaf.ΓNatIsoSheafSections_hom_app_general terminalIsTerminal
      ((etaleModuleRestrictScalars ψ Y).obj G),
      ← Sheaf.ΓNatIsoSheafSections_hom_app_general terminalIsTerminal G]
    change ((ModuleCat.restrictScalars.{u + 1} ψ).map
        ((Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
          terminalIsTerminal).hom.app G) ≫
        (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} R)
          terminalIsTerminal).inv.app ((etaleModuleRestrictScalars ψ Y).obj G)) ≫
        (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} R)
          terminalIsTerminal).hom.app ((etaleModuleRestrictScalars ψ Y).obj G) = _
    exact (Category.assoc ((ModuleCat.restrictScalars.{u + 1} ψ).map
        ((Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
          terminalIsTerminal).hom.app G))
        ((Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} R)
          terminalIsTerminal).inv.app ((etaleModuleRestrictScalars ψ Y).obj G))
        ((Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} R)
          terminalIsTerminal).hom.app ((etaleModuleRestrictScalars ψ Y).obj G))).trans
      ((congrArg ((ModuleCat.restrictScalars.{u + 1} ψ).map
        ((Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
          terminalIsTerminal).hom.app G) ≫ ·)
        (Iso.inv_hom_id_app (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology
          (ModuleCat.{u + 1} R) terminalIsTerminal) ((etaleModuleRestrictScalars ψ Y).obj G))).trans
      (Category.comp_id _))
  rw [← Sheaf.ΓRes_map ((etaleModuleRestrictScalars ψ Y).obj G) (terminal.from T).op,
    ← Category.assoc, h1, ← Sheaf.ΓRes_map G (terminal.from T).op, Functor.map_comp]
  rfl

/-- **`Γ(φ)` read at a terminal object is `φ` there**: for `φ : res_ψ G ⟶ G'`, the restriction of
`Γ(φ)(z)` (`Stacks.EtaleCohomology.globalSectionsRestrictScalarsAddHom`) to a terminal object `T`
is `φ` applied to the restriction of `z`. -/
theorem ΓRes_globalSectionsRestrictScalarsAddHom (G : EtaleModules.{u, 0} Λ Y)
    (G' : EtaleModules.{u, 0} R Y) (φ : (etaleModuleRestrictScalars ψ Y).obj G ⟶ G') (T : Y.Etale)
    (z : (etaleModuleGlobalSections.{u, 0} Λ Y).obj G) :
    G'.ΓRes (op T) (globalSectionsRestrictScalarsAddHom ψ Y G G' φ z) =
      φ.hom.app (op T) (G.ΓRes (op T) z) := by
  have hfin : (((etaleModuleGlobalSectionsRestrictScalars ψ Y).app G).hom ≫
      (etaleModuleGlobalSections.{u, 0} R Y).map φ) ≫ G'.ΓRes (op T) =
      (ModuleCat.restrictScalars.{u + 1} ψ).map (Sheaf.ΓRes G (op T)) ≫ φ.hom.app (op T) := by
    rw [Category.assoc]
    change ((etaleModuleGlobalSectionsRestrictScalars ψ Y).app G).hom ≫
      (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} R)).map φ ≫ G'.ΓRes (op T) = _
    rw [Sheaf.ΓRes_naturality φ (op T), ← Category.assoc,
      etaleModuleGlobalSectionsRestrictScalars_hom_ΓRes]
    rfl
  have h := ConcreteCategory.congr_hom hfin z
  rw [globalSectionsRestrictScalarsAddHom_apply]
  simp only [ModuleCat.hom_comp] at h
  exact h

end GlobalSections

section Geometric

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))

omit [IsAlgClosed kbar] in
/-- **The evaluation at `η̄` of a global section of `pr⁻¹ℱ_ρ` on `X_k̄` is its value at `η̄` over
the final object** (`AlgebraicGeometry.pullbackRepresentationEval`). -/
theorem geometricGlobalSectionsEval_eq_pullbackRepresentationEval
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (z : letI := connectedSpace_of_isCurve B X f
      ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        (geometricRepresentationRestriction B X f kbar Λ y ρ))) :
    letI := connectedSpace_of_isCurve B X f
    geometricGlobalSectionsEval B X f kbar Λ y ρ z =
      pullbackRepresentationEval B X (Y := fieldBaseChange (Over.mk f) kbar)
        (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y Λ ρ
        (U := Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk f) kbar))) y.hom (Category.comp_id _)
        ((geometricRepresentationRestriction B X f kbar Λ y ρ).ΓRes
          (op (Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk f) kbar)))) z) := by
  let := connectedSpace_of_isCurve B X f
  have ht : pullbackRepresentationCoverHom B X (Y := fieldBaseChange (Over.mk f) kbar)
      (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y Λ ρ
      ((geometricRepresentationRestriction B X f kbar Λ y ρ).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk f) kbar)))) z) =
      geometricGlobalSectionsCoverEquiv B X f kbar Λ y ρ z :=
    (pullbackRepresentationCoverHom_eq_iff B X
      (Y := fieldBaseChange (Over.mk f) kbar) _ y Λ ρ _ _).2
      ((geometricGlobalSectionsCoverEquiv_eq_iff B X f kbar Λ y ρ z _).1 rfl).symm
  have hp : pullbackRepresentationFibrePoint B X (Y := fieldBaseChange (Over.mk f) kbar)
      (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y Λ ρ
      (geometricGlobalSectionsCoverEquiv B X f kbar Λ y ρ z) y.hom (Category.comp_id _) =
      geometricGlobalSectionsFibrePoint B X f kbar Λ y ρ
        (geometricGlobalSectionsCoverEquiv B X f kbar Λ y ρ z) :=
    Subtype.ext (congrArg (y.hom ≫ ·) (Category.id_comp _)).symm
  refine Eq.trans ?_ (pullbackRepresentationEval_def B X (Y := fieldBaseChange (Over.mk f) kbar)
    (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y Λ ρ
    (U := (Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk f) kbar)))) y.hom
    (Category.comp_id _) ((geometricRepresentationRestriction B X f kbar Λ y ρ).ΓRes
      (op (Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk f) kbar)))) z)).symm
  rw [ht, hp]
  unfold geometricGlobalSectionsEval
  rfl

variable (n : ℕ) [NeZero n] [Algebra (ZMod n) Λ]

omit [IsAlgClosed kbar] in
/-- **`Φ_ρ` on global sections**: for `φ : res_ψ(pr⁻¹ℱ_ρ) ⟶ pr⁻¹ℱ_W` on `X_k̄`, `Φ_ρ(φ)` carries
the evaluation at `η̄` of a global section `z` to the evaluation at `η̄` of `Γ(φ)(z)`
(`Stacks.EtaleCohomology.globalSectionsRestrictScalarsAddHom`). -/
theorem pullbackRepresentationHomEquiv_geometricGlobalSectionsEval
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (W : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (φ : letI := connectedSpace_of_isCurve B X f
      ((etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) (pullback f (specAlgebraMap k kbar))).obj
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj
            ((representationSheaf B X
              (y.map (fieldBaseChangeObjProj B X f kbar
                  (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)) ⟶
        (etaleModuleInverseImage.{u, 0} (ZMod n) (pullback.fst f (specAlgebraMap k kbar))).obj
          ((representationSheaf B X
            (y.map (fieldBaseChangeObjProj B X f kbar
                (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) (ZMod n)).obj W)))
    (z : letI := connectedSpace_of_isCurve B X f
      ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        (geometricRepresentationRestriction B X f kbar Λ y ρ))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    pullbackRepresentationHomInvariantsToHom B X (Y := fieldBaseChange (Over.mk f) kbar)
      (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y Λ n W ρ
        (pullbackRepresentationHomEquiv B X (fieldBaseChange (Over.mk f) kbar)
          (contains_fieldBaseChange_of_isCurve B X f kbar)
            (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y Λ n W ρ φ)
        (geometricGlobalSectionsEval B X f kbar Λ y ρ z) =
      geometricGlobalSectionsEval B X f kbar (ZMod n) y W
        (globalSectionsRestrictScalarsAddHom (algebraMap (ZMod n) Λ) _ _ _ φ z) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  rw [pullbackRepresentationHomEquiv_apply]
  refine (congrArg (pullbackRepresentationHomFun B X (Y := fieldBaseChange (Over.mk f) kbar)
    (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y Λ n W ρ φ)
    (geometricGlobalSectionsEval_eq_pullbackRepresentationEval B X f kbar Λ y ρ z)).trans ?_
  refine (pullbackRepresentationHomFun_eval B X (Y := fieldBaseChange (Over.mk f) kbar)
    (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y Λ n W ρ φ
    (U := (Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk f) kbar)))) y.hom
    (Category.comp_id _) ((geometricRepresentationRestriction B X f kbar Λ y ρ).ΓRes
      (op (Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk f) kbar)))) z)).trans ?_
  refine Eq.trans ?_ (geometricGlobalSectionsEval_eq_pullbackRepresentationEval B X f kbar
    (ZMod n) y W
    (globalSectionsRestrictScalarsAddHom (algebraMap (ZMod n) Λ) _ _ _ φ z)).symm
  exact congrArg (pullbackRepresentationEval B X (Y := fieldBaseChange (Over.mk f) kbar)
    (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y
    (ZMod n) W (U := (Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk f) kbar)))) y.hom
    (Category.comp_id _)) (ΓRes_globalSectionsRestrictScalarsAddHom (algebraMap (ZMod n) Λ) _ _ _ φ
      (Scheme.Etale.mk (𝟙 (fieldBaseChange (Over.mk f) kbar))) z).symm

/-- **`Φ_ρ` for geometrically trivial `ρ` and `W`**: `Φ_ρ(φ)(m) = ev_W(Γ(φ)(ev_ρ⁻¹ m))`, where
`ev : Γ(X_k̄, pr⁻¹ℱ_ρ) ≃ M` is `AlgebraicGeometry.geometricGlobalSectionsTrivialEquivPullback`. -/
theorem pullbackRepresentationHomEquiv_apply_of_trivial
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (W : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap
          (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    (hW : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation (ZMod n) _ W)
        (etaleFundamentalGroupMap
          (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    (φ : letI := connectedSpace_of_isCurve B X f
      ((etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) (pullback f (specAlgebraMap k kbar))).obj
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj
            ((representationSheaf B X
              (y.map (fieldBaseChangeObjProj B X f kbar
                  (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)) ⟶
        (etaleModuleInverseImage.{u, 0} (ZMod n) (pullback.fst f (specAlgebraMap k kbar))).obj
          ((representationSheaf B X
            (y.map (fieldBaseChangeObjProj B X f kbar
                (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) (ZMod n)).obj W)))
    (m : ρ.obj.obj.obj.V) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    pullbackRepresentationHomInvariantsToHom B X (Y := fieldBaseChange (Over.mk f) kbar)
      (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y Λ n W ρ
        (pullbackRepresentationHomEquiv B X (fieldBaseChange (Over.mk f) kbar)
          (contains_fieldBaseChange_of_isCurve B X f kbar)
            (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y Λ n W ρ φ) m =
      geometricGlobalSectionsTrivialEquivPullback B X f kbar (ZMod n) y W hW
        (globalSectionsRestrictScalarsAddHom (algebraMap (ZMod n) Λ) _ _ _ φ
          ((geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ hρ).symm m)) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have hm : m = geometricGlobalSectionsEval B X f kbar Λ y ρ
      ((geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ hρ).symm m) :=
    ((geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ hρ).apply_symm_apply
      m).symm.trans
      (geometricGlobalSectionsTrivialEquiv_apply B X f kbar Λ y ρ hρ
        ((geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ hρ).symm m))
  refine (congrArg (pullbackRepresentationHomInvariantsToHom B X
    (Y := fieldBaseChange (Over.mk f) kbar)
    (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y Λ n W ρ
      (pullbackRepresentationHomEquiv B X (fieldBaseChange (Over.mk f) kbar)
        (contains_fieldBaseChange_of_isCurve B X f kbar)
        (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom
        y Λ n W ρ φ)) hm).trans ?_
  refine (pullbackRepresentationHomEquiv_geometricGlobalSectionsEval B X f kbar Λ y n ρ W φ _).trans
    ?_
  exact (geometricGlobalSectionsTrivialEquiv_apply B X f kbar (ZMod n) y W hW _).symm

end Geometric

section Cyclotomic

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ] [Algebra (ZMod (Fintype.card Λ)) Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))

/-- **`Φ_ρ : Hom(res_ψ(pr⁻¹ℱ_ρ), pr⁻¹ℱ_{μ_n}) ≃ Hom_{π₁(X_k̄)}(M, μ_n)`** on `X_k̄`, `n = #Λ`,
`ψ : ℤ/n → Λ`, with target `AlgebraicGeometry.geometricCyclotomicDualInvariants`:
`AlgebraicGeometry.pullbackRepresentationHomEquiv` for `W = μ_n(k̄)`. -/
def geometricCyclotomicDualHomEquiv (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    ((etaleModuleRestrictScalars (algebraMap (ZMod (Fintype.card Λ)) Λ)
          (pullback f (specAlgebraMap k kbar))).obj
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj
            ((representationSheaf B X
              (y.map (fieldBaseChangeObjProj B X f kbar
                  (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)) ⟶
        (etaleModuleInverseImage.{u, 0} (ZMod (Fintype.card Λ))
          (pullback.fst f (specAlgebraMap k kbar))).obj
          ((representationSheaf B X
            (y.map (fieldBaseChangeObjProj B X f kbar
                (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) (ZMod (Fintype.card Λ))).obj
            (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ)))) ≃+
      (geometricCyclotomicDualInvariants B X f kbar Λ y).obj (op ρ) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  pullbackRepresentationHomEquiv B X (fieldBaseChange (Over.mk f) kbar)
    (contains_fieldBaseChange_of_isCurve B X f kbar)
      (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y Λ
      (Fintype.card Λ)
    (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ)) ρ

/-- `AlgebraicGeometry.geometricCyclotomicDualHomEquiv` is
`AlgebraicGeometry.pullbackRepresentationHomEquiv`. -/
theorem geometricCyclotomicDualHomEquiv_eq (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (φ : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      ((etaleModuleRestrictScalars (algebraMap (ZMod (Fintype.card Λ)) Λ)
          (pullback f (specAlgebraMap k kbar))).obj
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj
            ((representationSheaf B X
              (y.map (fieldBaseChangeObjProj B X f kbar
                  (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)) ⟶
        (etaleModuleInverseImage.{u, 0} (ZMod (Fintype.card Λ))
          (pullback.fst f (specAlgebraMap k kbar))).obj
          ((representationSheaf B X
            (y.map (fieldBaseChangeObjProj B X f kbar
                (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) (ZMod (Fintype.card Λ))).obj
            (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ))))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    geometricCyclotomicDualHomEquiv B X f kbar Λ y ρ φ =
      pullbackRepresentationHomEquiv B X (fieldBaseChange (Over.mk f) kbar)
        (contains_fieldBaseChange_of_isCurve B X f kbar)
          (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y Λ (Fintype.card Λ)
        (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ)) ρ φ :=
  rfl

/-- **`Φ_ρ` with values in `Hom_{π₁(X_k̄)}(M, μ_n)` is natural in `ρ`.** -/
theorem geometricCyclotomicDualHomEquiv_naturality
    {ρ ρ' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (v : ρ ⟶ ρ')
    (φ' : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      ((etaleModuleRestrictScalars (algebraMap (ZMod (Fintype.card Λ)) Λ)
          (pullback f (specAlgebraMap k kbar))).obj
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj
            ((representationSheaf B X
              (y.map (fieldBaseChangeObjProj B X f kbar
                  (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ')) ⟶
        (etaleModuleInverseImage.{u, 0} (ZMod (Fintype.card Λ))
          (pullback.fst f (specAlgebraMap k kbar))).obj
          ((representationSheaf B X
            (y.map (fieldBaseChangeObjProj B X f kbar
                (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) (ZMod (Fintype.card Λ))).obj
            (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ))))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    geometricCyclotomicDualHomEquiv B X f kbar Λ y ρ
        ((etaleModuleRestrictScalars (algebraMap (ZMod (Fintype.card Λ)) Λ)
          (pullback f (specAlgebraMap k kbar))).map
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).map
            ((representationSheaf B X
              (y.map (fieldBaseChangeObjProj B X f kbar
                  (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map v)) ≫ φ') =
      (geometricCyclotomicDualInvariants B X f kbar Λ y).map v.op
        (geometricCyclotomicDualHomEquiv B X f kbar Λ y ρ' φ') :=
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  pullbackRepresentationHomEquiv_naturality B X (fieldBaseChange (Over.mk f) kbar)
    (contains_fieldBaseChange_of_isCurve B X f kbar)
      (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y Λ
      (Fintype.card Λ)
    (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ)) v φ'

end Cyclotomic

end AlgebraicGeometry
