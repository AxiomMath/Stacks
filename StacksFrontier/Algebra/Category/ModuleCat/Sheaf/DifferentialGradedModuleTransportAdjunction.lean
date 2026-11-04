module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAlgebraFunctoriality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDirectImage

/-!
# The transport of a differential graded module along a monoidal left adjoint is its pullback

Let `L ⊣ G` be an adjunction between categories of sheaves of modules on two sites, with `L`
additive and strong monoidal for the tensor product of Tag 01CA, `G` additive and lax monoidal,
and the two monoidal structures compatible (`CategoryTheory.Adjunction.IsMonoidal`). For a
morphism of ringed topoi this is the pullback `f^*` and the direct image `f_*` of sheaves of
modules. Let `B` be a sheaf of differential graded algebras on the target of `L`.

The transport `L(B)` is a sheaf of differential graded algebras on the other site, and the unit
of the adjunction is a unital homomorphism `η : B ⟶ G(L(B))`. For a right differential graded
`B`-module `M`, the transport `L(M)` is a right differential graded `L(B)`-module, and it is the
pullback of `M` along the base change `η`: for every right differential graded `L(B)`-module
`Q`,

`Hom_{L(B)}(L(M), Q) ≃ Hom_B(M, res_η G(Q))`,

naturally in `Q`, by the hom-set bijection of the adjunction applied degreewise.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.transportUnit`: the unit `η : B ⟶ G(L(B))`, a
  homomorphism of sheaves of differential graded algebras, and `isUnital_transportUnit` its
  unitality.
* `SheafOfModules.DifferentialGradedModule.transportAdjHomEquiv`: the bijection above.
* `SheafOfModules.DifferentialGradedModule.transportCorepresentableBy`: **`L(M)` corepresents
  `Q ↦ Hom_B(M, res_η G(Q))`**, the universal property of a pullback.

## Main results

* `SheafOfModules.DifferentialGradedModule.smulSheaf_restrictScalarsObj`: the morphism-level
  action of a restriction of scalars is the action precomposed with the homomorphism of algebras
  on the second factor.
* `SheafOfModules.DifferentialGradedModule.transport_smulSheaf_comp_iff`: a degreewise family out
  of `L(M)` intertwines the actions exactly when its adjoint transpose does.

## Implementation notes

The argument is the module counterpart of
`SheafOfModules.DifferentialGradedAlgebra.transportHomEquiv`: compatibility with the
differentials transports because the hom-set bijection is natural, and compatibility with the
actions is `Stacks.MonoidalGraded.mapMul_comp_iff`, the transposition of a multiplicativity
square along a monoidal adjunction, with the unit of the adjunction absorbed on the algebra
factor. The only new input is that restriction of scalars along `η` precomposes the action
with `η` on the algebra factor, `smulSheaf_restrictScalarsObj`.

## References

* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 0FRG](https://stacks.math.columbia.edu/tag/0FRG)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf

open scoped TensorProduct

universe v₁ v₂ u₁ u₂ w

namespace SheafOfModules.DifferentialGradedModule

/-! ### The action of a restriction of scalars, at morphism level -/

section Restriction

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

/-- **The morphism-level action of a restriction of scalars along `φ : A ⟶ B` is the action of
the module precomposed with `φ` on the algebra factor.** -/
theorem smulSheaf_restrictScalarsObj (hO : Presheaf.IsSheaf J
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))
    {A B : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)} (φ : A ⟶ B)
    (hφ : φ.IsUnital) (Q : DifferentialGradedModule.{w, w, w} B) (n i : ℤ) :
    smulSheaf (restrictScalarsObj φ hφ Q) n i =
      (𝟙 (Q.complex.X n) ⊗ₘ φ.toHomologicalComplex.f i) ≫ smulSheaf Q n i := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := Osharp) (F := Q.complex.X n)
    (G := A.complex.X i) (Q := Q.complex.X (n + i)) fun U x y ↦ ?_
  refine (smulSheaf_unit (restrictScalarsObj φ hφ Q) n i U x y).trans ?_
  exact (smulSheaf_unit Q n i U x _).symm.trans
    (congrArg ((smulSheaf Q n i).val.app U)
      (Stacks.TensorSheafWorld.tensorHom_val_app_tensorSheafUnit Osharp hO U
        (𝟙 (Q.complex.X n)) (φ.toHomologicalComplex.f i) x y).symm)

end Restriction

/-! ### The unit of the adjunction on algebras, and the pullback along it -/

section Transport

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable {L : SheafOfModules.{w} (toRingCat K Psharp) ⥤ SheafOfModules.{w} (toRingCat J Osharp)}
  {G : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp)}
  (adj : L ⊣ G) [L.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal] [L.Additive] [G.Additive]
  (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))
  (hP : Presheaf.IsSheaf K
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Psharp.obj))

variable (B : DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp))

/-- **The unit `η : B ⟶ G(L(B))` of the adjunction, as a homomorphism of sheaves of
differential graded algebras**: the adjoint transpose of the identity of `L(B)`. -/
noncomputable def transportUnit :
    B ⟶ DifferentialGradedAlgebra.transport G hO hP
      (DifferentialGradedAlgebra.transport L hP hO B) :=
  DifferentialGradedAlgebra.transportHomForward adj hO hP (𝟙 _)

/-- In each degree the unit of the adjunction on algebras is the unit of the adjunction on
sheaves of modules. -/
theorem transportUnit_f (i : ℤ) :
    (transportUnit adj hO hP B).toHomologicalComplex.f i = adj.unit.app (B.complex.X i) := by
  show adj.homEquiv (B.complex.X i) (L.obj (B.complex.X i)) (𝟙 (L.obj (B.complex.X i))) = _
  simp [Adjunction.homEquiv_unit]

omit [L.Additive] [G.Additive] in
/-- The unit of the adjunction carries the unit of `B` to the unit of `G(L(B))`, at morphism
level. -/
theorem oneHom_comp_unit :
    (SheafOfModules.GradedAlgebra.oneHom B.toGradedAlgebra : 𝟙_ _ ⟶ B.complex.X 0) ≫
        adj.unit.app (B.complex.X 0) =
      Stacks.MonoidalGraded.mapOne G
        (Stacks.MonoidalGraded.mapOne L
          (SheafOfModules.GradedAlgebra.oneHom B.toGradedAlgebra)) := by
  refine (adj.unit_naturality (SheafOfModules.GradedAlgebra.oneHom B.toGradedAlgebra :
    𝟙_ _ ⟶ B.complex.X 0)).symm.trans ?_
  rw [Stacks.MonoidalGraded.mapOne, Stacks.MonoidalGraded.mapOne,
    ← adj.unit_app_unit_comp_map_η, Category.assoc, ← CategoryTheory.Functor.map_comp,
    Functor.Monoidal.η_ε_assoc]

/-- **The unit of the adjunction on algebras is unital.** -/
theorem isUnital_transportUnit : (transportUnit adj hO hP B).IsUnital := by
  intro U
  rw [transportUnit_f]
  let one : (𝟙_ (SheafOfModules.{w} (toRingCat K Psharp))).val.obj U :=
    (1 : (toRingCat K Psharp).obj.obj U)
  have h := SheafOfModules.hom_congr_app_apply (oneHom_comp_unit adj B) U one
  have hB : (SheafOfModules.GradedAlgebra.oneHom B.toGradedAlgebra).val.app U one =
      B.one.eval U :=
    (SheafOfModules.GradedAlgebra.oneHom_val_app B.toGradedAlgebra U 1).trans (one_smul _ _)
  have hT : (SheafOfModules.GradedAlgebra.oneHom (DifferentialGradedAlgebra.transport G hO hP
        (DifferentialGradedAlgebra.transport L hP hO B)).toGradedAlgebra).val.app U one =
      (DifferentialGradedAlgebra.transport G hO hP
        (DifferentialGradedAlgebra.transport L hP hO B)).one.eval U :=
    (SheafOfModules.GradedAlgebra.oneHom_val_app _ U 1).trans (one_smul _ _)
  have e : SheafOfModules.GradedAlgebra.oneHom (DifferentialGradedAlgebra.transport G hO hP
        (DifferentialGradedAlgebra.transport L hP hO B)).toGradedAlgebra =
      Stacks.MonoidalGraded.mapOne G
        (Stacks.MonoidalGraded.mapOne L (SheafOfModules.GradedAlgebra.oneHom B.toGradedAlgebra)) :=
    (SheafOfModules.GradedAlgebra.oneHom_transport G
      (DifferentialGradedAlgebra.transport L hP hO B).toGradedAlgebra hO hP).trans
      (congrArg (Stacks.MonoidalGraded.mapOne G)
        (SheafOfModules.GradedAlgebra.oneHom_transport L B.toGradedAlgebra hP hO))
  rw [← hB, ← hT]
  exact h.trans (SheafOfModules.hom_congr_app_apply e.symm U one)

variable {B}

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat]
  [K.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify K AddCommGrpCat] [L.Monoidal]
  [G.LaxMonoidal] [adj.IsMonoidal] [L.Additive] [G.Additive] in
/-- The adjoint transpose of the identity of `L(X)` is the unit of the adjunction at `X`. -/
theorem homEquiv_id_eq_unit (X : SheafOfModules.{w} (toRingCat K Psharp)) :
    adj.homEquiv X (L.obj X) (𝟙 (L.obj X)) = adj.unit.app X := by
  simp [Adjunction.homEquiv_unit]

/-- **A degreewise family out of `L(M)` intertwines the transported action of `L(B)` exactly when
its adjoint transpose intertwines the action of `B` on `M` with the transported action on
`G(Q)` precomposed with the unit.** This is `Stacks.MonoidalGraded.mapMul_comp_iff`. -/
theorem transportedSmul_comp_iff (M : DifferentialGradedModule.{w, w, w} B)
    (Q : DifferentialGradedModule.{w, w, w} (DifferentialGradedAlgebra.transport L hP hO B))
    (gf : ∀ q : ℤ, L.obj (M.complex.X q) ⟶ Q.complex.X q) (n i : ℤ) :
    (transportedSmul L M n i ≫ gf (n + i) =
        (gf n ⊗ₘ 𝟙 (L.obj (B.complex.X i))) ≫ smulSheaf Q n i) ↔
      (smulSheaf M n i ≫ adj.homEquiv _ _ (gf (n + i)) =
        (adj.homEquiv _ _ (gf n) ⊗ₘ (transportUnit adj hO hP B).toHomologicalComplex.f i) ≫
          transportedSmul G Q n i) :=
  Stacks.MonoidalGraded.mapMul_comp_iff adj (smulSheaf M n i) (smulSheaf Q n i) (gf n)
    (𝟙 (L.obj (B.complex.X i))) (gf (n + i))

/-- The morphism-level action of `res_η G(Q)`: the action of `G(Q)` precomposed with the unit
of the adjunction on the algebra factor. -/
theorem smulSheaf_restrictScalarsObj_transportUnit
    (Q : DifferentialGradedModule.{w, w, w} (DifferentialGradedAlgebra.transport L hP hO B))
    (n i : ℤ) {X : SheafOfModules.{w} (toRingCat K Psharp)}
    (h : X ⟶ (transport G Q hO hP).complex.X n) :
    (h ⊗ₘ 𝟙 (B.complex.X i)) ≫ smulSheaf (restrictScalarsObj (transportUnit adj hO hP B)
        (isUnital_transportUnit adj hO hP B) (transport G Q hO hP)) n i =
      (h ⊗ₘ (transportUnit adj hO hP B).toHomologicalComplex.f i) ≫
        smulSheaf (transport G Q hO hP) n i := by
  refine (congrArg (fun z => (h ⊗ₘ 𝟙 (B.complex.X i)) ≫ z)
    (smulSheaf_restrictScalarsObj hP (transportUnit adj hO hP B)
      (isUnital_transportUnit adj hO hP B) (transport G Q hO hP) n i)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine congrArg (fun z => z ≫ smulSheaf (transport G Q hO hP) n i) ?_
  refine (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).trans ?_
  rw [Category.comp_id, Category.id_comp]

/-- The adjoint transpose of a morphism `L(M) ⟶ Q` of right differential graded
`L(B)`-modules: in each degree the hom-set bijection of the adjunction. -/
noncomputable def transportAdjTranspose (M : DifferentialGradedModule.{w, w, w} B)
    (Q : DifferentialGradedModule.{w, w, w} (DifferentialGradedAlgebra.transport L hP hO B))
    (g : transport L M hP hO ⟶ Q) :
    M ⟶ restrictScalarsObj (transportUnit adj hO hP B) (isUnital_transportUnit adj hO hP B)
      (transport G Q hO hP) :=
  Hom.mk (M := M) (N := restrictScalarsObj (transportUnit adj hO hP B)
      (isUnital_transportUnit adj hO hP B) (transport G Q hO hP))
    (HomologicalComplex.Hom.mk (A := M.complex) (B := (restrictScalarsObj
        (transportUnit adj hO hP B) (isUnital_transportUnit adj hO hP B)
        (transport G Q hO hP)).complex)
      (fun q => adj.homEquiv _ _ (g.toHomologicalComplex.f q))
      (fun i j _ =>
        (Adjunction.homEquiv_naturality_left_square adj (M.complex.d i j)
          (g.toHomologicalComplex.f j) (g.toHomologicalComplex.f i) (Q.complex.d i j)
          (g.toHomologicalComplex.comm i j).symm).symm)) fun n i => by
    have h₁ := (smulSheaf_comp_eq_iff (transport L M hP hO) hO Q
      (fun q => g.toHomologicalComplex.f q) n i).mpr (g.map_mul n i)
    have h₁' : transportedSmul L M n i ≫ g.toHomologicalComplex.f (n + i) =
        (g.toHomologicalComplex.f n ⊗ₘ 𝟙 (L.obj (B.complex.X i))) ≫ smulSheaf Q n i :=
      (congrArg (fun z => z ≫ g.toHomologicalComplex.f (n + i))
        (smulSheaf_transport L M hP hO n i)).symm.trans h₁
    have h₂ := (transportedSmul_comp_iff adj hO hP M Q
      (fun q => g.toHomologicalComplex.f q) n i).mp h₁'
    refine (smulSheaf_comp_eq_iff M hP (restrictScalarsObj (transportUnit adj hO hP B)
      (isUnital_transportUnit adj hO hP B) (transport G Q hO hP))
      (fun q => adj.homEquiv _ _ (g.toHomologicalComplex.f q)) n i).mp ?_
    refine h₂.trans ?_
    refine Eq.trans ?_ (smulSheaf_restrictScalarsObj_transportUnit adj hO hP Q n i
      (adj.homEquiv _ _ (g.toHomologicalComplex.f n))).symm
    exact congrArg (fun z => (adj.homEquiv _ _ (g.toHomologicalComplex.f n) ⊗ₘ
      (transportUnit adj hO hP B).toHomologicalComplex.f i) ≫ z)
        (smulSheaf_transport G Q hO hP n i).symm

/-- The inverse transpose of a morphism `M ⟶ res_η G(Q)`. -/
noncomputable def transportAdjUntranspose (M : DifferentialGradedModule.{w, w, w} B)
    (Q : DifferentialGradedModule.{w, w, w} (DifferentialGradedAlgebra.transport L hP hO B))
    (h : M ⟶ restrictScalarsObj (transportUnit adj hO hP B) (isUnital_transportUnit adj hO hP B)
      (transport G Q hO hP)) :
    transport L M hP hO ⟶ Q :=
  Hom.mk (M := transport L M hP hO) (N := Q)
    (HomologicalComplex.Hom.mk (A := (transport L M hP hO).complex) (B := Q.complex)
      (fun q => (adj.homEquiv _ _).symm (h.toHomologicalComplex.f q))
      (fun i j _ =>
        (Adjunction.homEquiv_naturality_right_square adj (M.complex.d i j)
          (h.toHomologicalComplex.f j) (h.toHomologicalComplex.f i) (Q.complex.d i j)
          (h.toHomologicalComplex.comm i j).symm).symm)) fun n i => by
    have h₁ := (smulSheaf_comp_eq_iff M hP (restrictScalarsObj (transportUnit adj hO hP B)
      (isUnital_transportUnit adj hO hP B) (transport G Q hO hP))
      (fun q => h.toHomologicalComplex.f q) n i).mpr
      (h.map_mul n i)
    have cancel : ∀ q : ℤ, adj.homEquiv _ _
        ((adj.homEquiv _ _).symm (h.toHomologicalComplex.f q)) = h.toHomologicalComplex.f q :=
      fun q => (adj.homEquiv _ _).apply_symm_apply _
    have h₁' : smulSheaf M n i ≫ adj.homEquiv _ _
          ((adj.homEquiv _ _).symm (h.toHomologicalComplex.f (n + i))) =
        (adj.homEquiv _ _ ((adj.homEquiv _ _).symm (h.toHomologicalComplex.f n)) ⊗ₘ
          (transportUnit adj hO hP B).toHomologicalComplex.f i) ≫
            transportedSmul G Q n i := by
      rw [cancel, cancel]
      refine h₁.trans ?_
      refine (smulSheaf_restrictScalarsObj_transportUnit adj hO hP Q n i
        (h.toHomologicalComplex.f n)).trans ?_
      exact congrArg (fun z => (h.toHomologicalComplex.f n ⊗ₘ
        (transportUnit adj hO hP B).toHomologicalComplex.f i) ≫ z)
          (smulSheaf_transport G Q hO hP n i)
    have h₂ := (transportedSmul_comp_iff adj hO hP M Q
      (fun q => (adj.homEquiv _ _).symm (h.toHomologicalComplex.f q)) n i).mpr h₁'
    refine (smulSheaf_comp_eq_iff (transport L M hP hO) hO Q
      (fun q => (adj.homEquiv _ _).symm (h.toHomologicalComplex.f q)) n i).mp ?_
    exact (congrArg (fun z => z ≫ (adj.homEquiv _ _).symm (h.toHomologicalComplex.f (n + i)))
      (smulSheaf_transport L M hP hO n i)).trans h₂

/-- **The pullback of `M` along the unit `η : B ⟶ G(L(B))` is `L(M)`**: morphisms
`L(M) ⟶ Q` of right differential graded `L(B)`-modules are the morphisms `M ⟶ res_η G(Q)` of
right differential graded `B`-modules, by the hom-set bijection of the adjunction in each
degree. -/
noncomputable def transportAdjHomEquiv (M : DifferentialGradedModule.{w, w, w} B)
    (Q : DifferentialGradedModule.{w, w, w} (DifferentialGradedAlgebra.transport L hP hO B)) :
    (transport L M hP hO ⟶ Q) ≃
      (M ⟶ restrictScalarsObj (transportUnit adj hO hP B) (isUnital_transportUnit adj hO hP B)
        (transport G Q hO hP)) where
  toFun := transportAdjTranspose adj hO hP M Q
  invFun := transportAdjUntranspose adj hO hP M Q
  left_inv g := Hom.ext fun q => (adj.homEquiv _ _).symm_apply_apply (g.toHomologicalComplex.f q)
  right_inv h := Hom.ext fun q => (adj.homEquiv _ _).apply_symm_apply (h.toHomologicalComplex.f q)

/-- The bijection is the hom-set bijection of the adjunction in each degree. -/
theorem transportAdjHomEquiv_apply_f (M : DifferentialGradedModule.{w, w, w} B)
    (Q : DifferentialGradedModule.{w, w, w} (DifferentialGradedAlgebra.transport L hP hO B))
    (g : transport L M hP hO ⟶ Q) (q : ℤ) :
    (transportAdjHomEquiv adj hO hP M Q g).toHomologicalComplex.f q =
      adj.homEquiv _ _ (g.toHomologicalComplex.f q) :=
  rfl

/-- **`L(M)` corepresents `Q ↦ Hom_B(M, res_η G(Q))`**: it is the pullback of `M` along the
base change `η : B ⟶ G(L(B))`. -/
noncomputable def transportCorepresentableBy (M : DifferentialGradedModule.{w, w, w} B) :
    ((transportFunctor G hO hP ⋙ restrictScalars (transportUnit adj hO hP B)
        (isUnital_transportUnit adj hO hP B)) ⋙
      coyoneda.obj (Opposite.op M)).CorepresentableBy (transport L M hP hO) where
  homEquiv {Q} := transportAdjHomEquiv adj hO hP M Q
  homEquiv_comp {_Q _Q'} k g := Hom.ext fun q =>
    adj.homEquiv_naturality_right (g.toHomologicalComplex.f q) (k.toHomologicalComplex.f q)

end Transport

end SheafOfModules.DifferentialGradedModule

end
