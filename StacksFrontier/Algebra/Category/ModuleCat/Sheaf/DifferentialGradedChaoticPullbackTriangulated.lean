module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticDerivedPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConcreteDGFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionSystemCochain
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticSheafInstances

/-!
# The pullback along a functor of chaotic sites is a functor of differential graded categories

Let `F : C' ⥤ C` be a functor of categories with the chaotic topology and `φ : g^*A → A'` a map
of sheaves of differential graded algebras along the morphism of chaotic ringed sites it
induces. The pullback `g^*M`, `U' ↦ M(F U') ⊗_{A(F U')} A'(U')`, extends to homogeneous maps: an
action-linear cochain `c : M ⟶ N` of degree `k` is a homogeneous map `M(F U') ⟶ N(F U')` of
degree `k` on sections, its tensor product with `A'(U')` is one of the sections of the pullbacks,
these commute with restriction, and they realize to an action-linear cochain `g^*M ⟶ g^*N`. So
the pullback is a functor of differential graded categories, and by [Stacks, Tag 0FQF] it
induces an exact functor `K(A) ⥤ K(A')` of triangulated categories.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.pullbackHomogeneous`: the tensor product of the
  sections of a cochain with `A'(U')`, a homogeneous map of the sections of the pullbacks.
* `SheafOfModules.DifferentialGradedModule.pullbackConcreteDGFunctor`: the pullback, extended to
  homogeneous maps.

## Main results

* `SheafOfModules.DifferentialGradedModule.pullbackHomotopyFunctor_commShift` and
  `pullbackHomotopyFunctor_isTriangulated`: **the pullback on the homotopy categories commutes
  with the translations and is triangulated.**

## References

* [Stacks Project, Section 24.33 (Tag 0GZ8)](https://stacks.math.columbia.edu/tag/0GZ8)
* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF)
* [Stacks Project, Lemma 24.30.1 (Tag 0FTF)](https://stacks.math.columbia.edu/tag/0FTF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf CochainComplex.HomComplex

universe m u

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra
  Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [Category.{u} C] {C' : Type u} [Category.{u} C']
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  {Osharp' : Sheaf (⊥ : GrothendieckTopology C') CommRingCat.{u}}
  {F : C' ⥤ C}
  {σ : F.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf Osharp').obj}
  {A : DifferentialGradedAlgebra.{u, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
  {A' : DifferentialGradedAlgebra.{u, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp')}
  (φ : DifferentialGradedAlgebra.InverseImageHom F σ A A')

/-! ### The pullback of a homogeneous map -/

section Homogeneous

variable {M N : DifferentialGradedModule.{u, m, m} A}

/-- **The pullback of an action-linear cochain over `U'`**: the tensor product with `A'(U')` of
the homogeneous map `M(F U') ⟶ N(F U')` it induces on sections. -/
def pullbackHomogeneous {k : ℤ} (c : Cochain M.complex N.complex k)
    (hc : IsActionLinear (X := ⟨C, ⊥, Osharp⟩) A c) (U' : C'ᵒᵖ) :
    _root_.DifferentialGradedModule.HomogeneousMap (A'.sectionAlgebra U')
      (pullbackSections φ M U') (pullbackSections φ N U') k :=
  (DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).functor.map
    (sectionHomogeneous c hc (F.op.obj U'))

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The pullback of a cochain on a pure tensor: `x ⊗ b ↦ c(x) ⊗ b`. -/
theorem pullbackHomogeneous_pure {k : ℤ} (c : Cochain M.complex N.complex k)
    (hc : IsActionLinear (X := ⟨C, ⊥, Osharp⟩) A c) (U' : C'ᵒᵖ)
    (x : (M.sectionModule (F.op.obj U')).M) (y : (pullbackBimodule φ U').rightModule.M) :
    (pullbackHomogeneous φ c hc U').1 (pullbackPure φ M U' x y) =
      pullbackPure φ N U' ((sectionHomogeneous c hc (F.op.obj U')).1 x) y :=
  (DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).map_pure _ x y

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The pullbacks of a cochain commute with restriction.** -/
theorem pullbackHomogeneous_naturality {k : ℤ} (c : Cochain M.complex N.complex k)
    (hc : IsActionLinear (X := ⟨C, ⊥, Osharp⟩) A c) {U' V' : C'ᵒᵖ} (a : V' ⟶ U')
    (z : (pullbackSections φ M V').M) :
    (pullbackRestr φ N a).toFun ((pullbackHomogeneous φ c hc V').1 z) =
      (pullbackHomogeneous φ c hc U').1 ((pullbackRestr φ M a).toFun z) := by
  have key : (pullbackRestr φ N a).toFun.toAddMonoidHom.comp
      (pullbackHomogeneous φ c hc V').1.toAddMonoidHom =
      (pullbackHomogeneous φ c hc U').1.toAddMonoidHom.comp
        (pullbackRestr φ M a).toFun.toAddMonoidHom := by
    refine tensorObj_addHom_ext _ _ _ _ fun x y => ?_
    change (pullbackRestr φ N a).toFun ((pullbackHomogeneous φ c hc V').1
        (pullbackPure φ M V' x y)) =
      (pullbackHomogeneous φ c hc U').1 ((pullbackRestr φ M a).toFun (pullbackPure φ M V' x y))
    rw [pullbackHomogeneous_pure, pullbackRestr_pure, pullbackRestr_pure,
      pullbackHomogeneous_pure]
    exact congrArg (fun p => pullbackPure φ N U' p
      (regElt φ U' ((A'.sectionRestriction a).toAlgebraHom (algElt φ V' y))))
      (sectionModuleRestriction_sectionHomogeneous c hc (F.op.map a) x)
  exact DFunLike.congr_fun key z

/-- The pullbacks of a cochain, as a natural family of homogeneous maps of the presheaves of
section modules of the pullbacks. -/
def pullbackFamily {k : ℤ} (c : Cochain M.complex N.complex k)
    (hc : IsActionLinear (X := ⟨C, ⊥, Osharp⟩) A c) :
    SectionSystem.HomogeneousFamily (pullbackSystem φ M) (pullbackSystem φ N) k where
  app U' := pullbackHomogeneous φ c hc U'
  naturality a z := pullbackHomogeneous_naturality φ c hc a z

end Homogeneous

/-! ### The pullback as a functor of differential graded categories -/

/-- **The pullback, extended to homogeneous maps**: an action-linear cochain `c` goes to the
realization of the tensor products of its sections with `A'(U')`. -/
def pullbackConcreteDGFunctor :
    ConcreteDGFunctor.{u, m, m, m, m} (X := ⟨C, ⊥, Osharp⟩) (Y := ⟨C', ⊥, Osharp'⟩) A A' where
  functor := pullbackFunctor φ
  mapCochain c hc := (pullbackFamily φ c hc).realizeCochain
  isActionLinear_mapCochain c hc := (pullbackFamily φ c hc).isActionLinear_realizeCochain
  mapCochain_add c c' hc hc' hcc' := by
    refine Eq.trans ?_ (SectionSystem.HomogeneousFamily.realizeCochain_add _ _)
    congr 1
    refine SectionSystem.HomogeneousFamily.ext (funext fun U' => ?_)
    change (DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).functor.map _ =
      (DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).functor.map _ +
        (DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).functor.map _
    exact (congrArg
      (DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).functor.map
      (sectionHomogeneous_add c c' hc hc' hcc' (F.op.obj U'))).trans
      ((DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).functor.map_add _ _)
  mapCochain_delta c hc hδ := by
    refine Eq.trans ?_ (SectionSystem.HomogeneousFamily.realizeCochain_d _)
    congr 1
    refine SectionSystem.HomogeneousFamily.ext (funext fun U' => ?_)
    change (DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).functor.map _ =
      _root_.DifferentialGradedModule.homogeneousMapDifferential (A'.sectionAlgebra U')
        ((DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).functor.map _)
    exact (congrArg
      (DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).functor.map
      (sectionHomogeneous_delta c hc hδ (F.op.obj U'))).trans
      ((DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).functor.map_d _)
  mapCochain_comp {_ _ _} {k l m} c c' h hc hc' hcc' := by
    refine Eq.trans ?_ (SectionSystem.HomogeneousFamily.realizeCochain_comp h _ _)
    congr 1
    refine SectionSystem.HomogeneousFamily.ext (funext fun U' => ?_)
    change (DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).functor.map _ =
      _root_.DifferentialGradedModule.homogeneousMapComp (A'.sectionAlgebra U')
        (show l + k = m by omega)
        ((DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).functor.map _)
        ((DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).functor.map _)
    exact (congrArg
      (DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).functor.map
      (sectionHomogeneous_comp c c' h hc hc' hcc' (F.op.obj U'))).trans
      ((DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).functor.map_comp
        (show l + k = m by omega) _ _)
  mapCochain_ofHom f := by
    refine Eq.trans ?_ (SectionSystem.HomogeneousFamily.realizeCochain_ofHom
      (pullbackSystemMap φ f))
    congr 1
    refine SectionSystem.HomogeneousFamily.ext (funext fun U' => ?_)
    change (DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).functor.map _ = _
    exact (congrArg
      (DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).functor.map
      (sectionHomogeneous_ofHom f _ (F.op.obj U'))).trans rfl

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The functor of homotopy categories induced by `pullbackConcreteDGFunctor` is the pullback on
the homotopy categories. -/
theorem pullbackConcreteDGFunctor_homotopyFunctor :
    (pullbackConcreteDGFunctor φ).homotopyFunctor = pullbackHomotopyFunctor φ :=
  rfl

/-- **The pullback on the homotopy categories commutes with the translations.** -/
@[instance_reducible]
instance pullbackHomotopyFunctor_commShift : (pullbackHomotopyFunctor φ).CommShift ℤ :=
  (pullbackConcreteDGFunctor φ).commShift

/-- **The pullback on the homotopy categories is an exact functor of triangulated categories**
(Tag 0FQF). -/
instance pullbackHomotopyFunctor_isTriangulated : (pullbackHomotopyFunctor φ).IsTriangulated :=
  (pullbackConcreteDGFunctor φ).isTriangulated

end SheafOfModules.DifferentialGradedModule
