module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionSystemEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticGlobalSections
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangePlainComparison
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroAlgebra

/-!
# Extension of scalars from the constant ring to a sheaf of differential graded algebras

Let `C` be a category with the chaotic topology, `R` a commutative ring, `O` the constant sheaf of
rings with value `R` and `A` a sheaf of differential graded `O`-algebras. For a complex `K` of
`R`-modules the sections `U ↦ K ⊗_R A(U)` form a presheaf of section modules: over `U` the
differential graded `A(U)`-module obtained by extending the scalars of `K` along the structure
map `R → A(U)`, `r ↦ r · 1`, with restriction `x ⊗ b ↦ x ⊗ b|_V`. Its realization is the right
differential graded `A`-module `K ⊗_R A`. This is the pullback `f^*K` along the morphism of ringed
topoi `f : (Sh(C), A) → (Sh(pt), R)` of the proof of Proposition 0GZK, and it is left adjoint to
the global sections `M ↦ Γ(C, M) = lim_U M(U)`.

## Main definitions

* `Stacks.ChaoticSite.baseDGA R`: the ring `R` in degree zero, as a differential graded algebra
  over the lifted integers.
* `Stacks.ChaoticSite.structureHom A U`: the homomorphism `R → A(U)`, `r ↦ r · 1`, of
  differential graded algebras.
* `Stacks.ChaoticSite.extensionSystem A K`: the presheaf of section modules
  `U ↦ K ⊗_R A(U)`, and `extensionSystemFunctor A` its functoriality in `K`.
* `Stacks.ChaoticSite.extendFunctor A`: **the functor `K ↦ K ⊗_R A`** from complexes of
  `R`-modules to right differential graded `A`-modules.

## References

* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
* [Stacks Project, Section 24.33 (Tag 0GZ8)](https://stacks.math.columbia.edu/tag/0GZ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf Stacks.PresheafOfModules

universe u

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.ChaoticSite

attribute [local instance] _root_.SheafOfModules.GradedAlgebra.sectionsGOne
  _root_.SheafOfModules.GradedAlgebra.sectionsGMul _root_.SheafOfModules.GradedAlgebra.sectionsGRing
  Stacks.uliftIntAlgebra

open _root_.SheafOfModules _root_.SheafOfModules.DifferentialGradedModule
  DifferentialGraded.Bimodule

variable {C : Type u} [SmallCategory C] (R : Type u) [CommRing R]

/-- **The ring `R` in degree zero**, as a differential graded algebra over the lifted
integers. -/
abbrev baseDGA : _root_.DifferentialGradedAlgebra.{u, u} (ULift.{u} ℤ) :=
  _root_.DifferentialGradedAlgebra.degreeZero (ULift.{u} ℤ) R

variable {R}
variable (A : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (constCommRingSheaf (C := C) R)))

/-- The scalars `r · 1` of `A(U)`, as a ring homomorphism out of `R`. -/
def scalarRingHom (U : Cᵒᵖ) : R →+* (A.sectionAlgebra U).A where
  toFun r := A.sectionScalar U r
  map_one' := (A.sectionScalar U).map_one
  map_mul' r s := (A.sectionScalar U).map_mul r s
  map_zero' := (A.sectionScalar U).map_zero
  map_add' r s := (A.sectionScalar U).map_add r s

/-- The ring homomorphism `scalarRingHom A U` sends `r : R` to the scalar `r · 1` of `A(U)`. -/
@[simp] theorem scalarRingHom_apply (U : Cᵒᵖ) (r : R) :
    scalarRingHom A U r = A.sectionScalar U r := rfl

/-- **The structure homomorphism `R → A(U)`**, `r ↦ r · 1`, of differential graded algebras over
the lifted integers. -/
def structureHom (U : Cᵒᵖ) : (baseDGA R).Hom (A.sectionAlgebra U) where
  toAlgebraHom := Stacks.uliftIntAlgHom (scalarRingHom A U)
  map_grading n a ha := by
    by_cases hn : n = 0
    · subst hn
      exact A.sectionScalar_mem U a
    · have ha0 : a = 0 := by
        simpa [_root_.DifferentialGradedAlgebra.degreeZero,
          _root_.DifferentialGradedAlgebra.degreeZeroGrading, hn] using ha
      subst ha0
      show A.sectionScalar U 0 ∈ _
      rw [map_zero]
      exact Submodule.zero_mem _
  map_d a := by
    show A.sectionScalar U 0 = (A.sectionAlgebra U).d (A.sectionScalar U a)
    rw [map_zero]
    exact (A.sectionAlgebra_d_sectionScalar U a).symm

/-- The structure homomorphism `structureHom A U` sends `r : R` to the scalar `r · 1` of `A(U)`. -/
@[simp] theorem structureHom_apply (U : Cᵒᵖ) (r : R) :
    (structureHom A U).toAlgebraHom r = A.sectionScalar U r := rfl

/-- The structure homomorphisms commute with the restriction homomorphisms. -/
theorem sectionRestriction_structureHom {U V : Cᵒᵖ} (a : V ⟶ U) (r : R) :
    (A.sectionRestriction a).toAlgebraHom ((structureHom A V).toAlgebraHom r) =
      (structureHom A U).toAlgebraHom r :=
  A.sectionRestriction_sectionScalar a r


namespace DifferentialGradedModule

variable {S : Type u} [CommRing S] {A B C : _root_.DifferentialGradedAlgebra.{u, u} S}

/-- Restriction of scalars along a composite is restriction along the two factors in turn: the
identity of the underlying module. -/
def restrictScalarsCompHom (φ : A.Hom B) (ψ : B.Hom C) (χ : A.Hom C)
    (h : ∀ a, ψ.toAlgebraHom (φ.toAlgebraHom a) = χ.toAlgebraHom a)
    (N : _root_.DifferentialGradedModule.{u, u, u} C) :
    _root_.DifferentialGradedModule.restrictScalars χ N ⟶
      _root_.DifferentialGradedModule.restrictScalars φ
        (_root_.DifferentialGradedModule.restrictScalars ψ N) where
  toFun := LinearMap.id
  map_smul x a := by
    change (MulOpposite.op (χ.toAlgebraHom a)) • (show N.M from x) =
      (MulOpposite.op (ψ.toAlgebraHom (φ.toAlgebraHom a))) • (show N.M from x)
    rw [h]
  map_grading _ _ hx := hx
  map_d := rfl

/-- The morphism `restrictScalarsCompHom φ ψ χ h N` is the identity on underlying elements. -/
@[simp] theorem restrictScalarsCompHom_toFun (φ : A.Hom B) (ψ : B.Hom C) (χ : A.Hom C)
    (h : ∀ a, ψ.toAlgebraHom (φ.toAlgebraHom a) = χ.toAlgebraHom a)
    (N : _root_.DifferentialGradedModule.{u, u, u} C) (x : N.M) :
    (restrictScalarsCompHom φ ψ χ h N).toFun x = x := rfl

end DifferentialGradedModule

end Stacks.ChaoticSite

namespace Stacks.ChaoticSite

attribute [local instance] _root_.SheafOfModules.GradedAlgebra.sectionsGOne
  _root_.SheafOfModules.GradedAlgebra.sectionsGMul _root_.SheafOfModules.GradedAlgebra.sectionsGRing
  Stacks.uliftIntAlgebra

open _root_.SheafOfModules _root_.SheafOfModules.DifferentialGradedModule
  DifferentialGraded.Bimodule

/-- **Extensionality for additive maps out of a relative tensor product**, on homogeneous pure
tensors. -/
theorem tensorObj_addHom_ext_homogeneous
    {B B' : _root_.DifferentialGradedAlgebra.{u, u} (ULift.{u} ℤ)}
    (N : DifferentialGraded.Bimodule B B') (X : _root_.DifferentialGradedModule.{u, u, u} B)
    {P : Type*} [AddCommGroup P] (f g : (tensorObj N X).M →+ P)
    (h : ∀ (p q : ℤ) (x : X.grading p) (y : N.rightModule.grading q),
      f ((tensorPure N X).toLinearMap (x : X.M) (y : N.rightModule.M)) =
        g ((tensorPure N X).toLinearMap (x : X.M) (y : N.rightModule.M))) :
    f = g := by
  refine AddMonoidHom.ext fun z => ?_
  have hz : z ∈ DifferentialGraded.Bimodule.pureSpan N X := by
    rw [DifferentialGraded.Bimodule.pureSpan_eq_top]
    trivial
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨p, q, x, y, rfl⟩ := hw
    exact h p q x y
  | zero => simp only [map_zero]
  | add w w' _ _ ihw ihw' => simp only [map_add, ihw, ihw']
  | smul r w _ ih =>
    have hr := SheafOfModules.DifferentialGradedModule.uliftInt_smul_eq
      (tensorObj N X).module r w
    exact (congrArg f hr).trans ((map_zsmul f r.down w).trans
      ((congrArg (fun v => r.down • v) ih).trans ((map_zsmul g r.down w).symm.trans
        (congrArg g hr).symm)))

variable {C : Type u} [SmallCategory C] {R : Type u} [CommRing R]
variable (A : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (constCommRingSheaf (C := C) R)))
  (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- A complex of `R`-modules, as a differential graded module over `R` in degree zero. -/
abbrev baseModule : _root_.DifferentialGradedModule.{u, u, u} (baseDGA R) :=
  (_root_.DifferentialGradedModule.degreeZeroTotalFunctor (ULift.{u} ℤ) R).obj K

/-- The `(R, A(U))`-bimodule `A(U)`, through the structure homomorphism. -/
abbrev extensionBimodule (U : Cᵒᵖ) : DifferentialGraded.Bimodule (baseDGA R) (A.sectionAlgebra U) :=
  DifferentialGraded.Bimodule.regular (structureHom A U)

/-- **The sections `K ⊗_R A(U)`** of the extension of scalars of `K`. -/
abbrev extensionSections (U : Cᵒᵖ) : _root_.DifferentialGradedModule.{u, u, u} (A.sectionAlgebra U) :=
  tensorObj (extensionBimodule A U) (baseModule K)

/-- The pure tensor `x ⊗ b` of `K ⊗_R A(U)`. -/
abbrev extensionPure (U : Cᵒᵖ) :=
  (tensorPure (extensionBimodule A U) (baseModule K)).toLinearMap

/-- An element of `A(U)`, read in the bimodule `A(U)`. -/
abbrev bimElt (U : Cᵒᵖ) (b : (A.sectionAlgebra U).A) : (extensionBimodule A U).rightModule.M := b

/-- The unit `x ↦ x ⊗ 1` of extension of scalars along `R → A(U)`. -/
def extensionUnit (U : Cᵒᵖ) :
    baseModule K ⟶ _root_.DifferentialGradedModule.restrictScalars (structureHom A U)
      (extensionSections A K U) :=
  (tensorRegularAdjRestrictScalars (structureHom A U)).unit.app (baseModule K)

/-- The plain transpose of the unit is the identity. -/
theorem plainTranspose_extensionUnit (U : Cᵒᵖ) :
    plainTranspose (structureHom A U) (extensionUnit A K U) = 𝟙 _ := by
  change ((tensorRegularAdjRestrictScalars (structureHom A U)).homEquiv _ _).symm
    ((tensorRegularAdjRestrictScalars (structureHom A U)).unit.app _) = _
  rw [Adjunction.homEquiv_counit]
  exact (tensorRegularAdjRestrictScalars (structureHom A U)).left_triangle_components _

/-- **The unit of extension of scalars is `x ↦ x ⊗ 1`.** -/
theorem extensionUnit_toFun (U : Cᵒᵖ) (x : (baseModule K).M) :
    (extensionUnit A K U).toFun x = extensionPure A K U x (bimElt A U 1) := by
  induction x using DirectSum.Decomposition.inductionOn (baseModule K).grading with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | @homogeneous p x =>
    have h := plainTranspose_pure (structureHom A U) (extensionUnit A K U) p x
      (1 : (A.sectionAlgebra U).A)
    rw [plainTranspose_extensionUnit] at h
    have h1 : @HSMul.hSMul (A.sectionAlgebra U).Aᵐᵒᵖ (extensionSections A K U).M
        (extensionSections A K U).M _ (MulOpposite.op 1) ((extensionUnit A K U).toFun x) =
        (extensionUnit A K U).toFun x := one_smul _ _
    exact h1.symm.trans h.symm

/-- The pure tensors are right `A(U)`-linear in the second variable: `x ⊗ (1 · b) = (x ⊗ 1) b`. -/
theorem extensionPure_one_smul (U : Cᵒᵖ) (x : (baseModule K).M) (b : (A.sectionAlgebra U).A) :
    @HSMul.hSMul (A.sectionAlgebra U).Aᵐᵒᵖ (extensionSections A K U).M
        (extensionSections A K U).M _ (MulOpposite.op b) (extensionPure A K U x (bimElt A U 1)) =
      extensionPure A K U x (bimElt A U b) := by
  refine ((tensorPure (extensionBimodule A U) (baseModule K)).map_right x _ b).symm.trans ?_
  congr 1
  show (1 : (A.sectionAlgebra U).A) * b = b
  exact one_mul b

/-- **The restriction homomorphism** `K ⊗_R A(V) ⟶ K ⊗_R A(U)` along `a : V ⟶ U`,
`x ⊗ b ↦ x ⊗ b|_U`: the transpose of the unit of `U`, read over `A(V)`. -/
def extensionRestr {U V : Cᵒᵖ} (a : V ⟶ U) :
    extensionSections A K V ⟶
      _root_.DifferentialGradedModule.restrictScalars (A.sectionRestriction a)
        (extensionSections A K U) :=
  plainTranspose (structureHom A V)
    (extensionUnit A K U ≫ DifferentialGradedModule.restrictScalarsCompHom (structureHom A V)
      (A.sectionRestriction a) (structureHom A U) (sectionRestriction_structureHom A a)
      (extensionSections A K U))

/-- The restriction homomorphism on a homogeneous pure tensor. -/
theorem extensionRestr_pure {U V : Cᵒᵖ} (a : V ⟶ U) (p : ℤ) (x : (baseModule K).grading p)
    (b : (extensionBimodule A V).rightModule.M) :
    (extensionRestr A K a).toFun (extensionPure A K V x b) =
      extensionPure A K U x (bimElt A U ((A.sectionRestriction a).toAlgebraHom b)) := by
  refine (plainTranspose_pure (structureHom A V) _ p x b).trans ?_
  refine Eq.trans ?_ (extensionPure_one_smul A K U x ((A.sectionRestriction a).toAlgebraHom b))
  congr 1
  exact extensionUnit_toFun A K U x

/-- Additive maps out of `K ⊗_R A(U)` agree if they agree on the pure tensors `x ⊗ b`. -/
private theorem extensionSections_addHom_apply_eq {U : Cᵒᵖ} {P : Type*} [AddCommGroup P]
    (f g : (extensionSections A K U).M →+ P)
    (h : ∀ (p : ℤ) (x : (baseModule K).grading p) (b : (A.sectionAlgebra U).A),
      f (extensionPure A K U x (bimElt A U b)) = g (extensionPure A K U x (bimElt A U b)))
    (z : (extensionSections A K U).M) : f z = g z :=
  DFunLike.congr_fun (tensorObj_addHom_ext_homogeneous _ _ f g fun p _ x y => h p x y.1) z

/-- The restriction homomorphism of `K ⊗_R A(U)` along the identity of `U` is the identity. -/
theorem extensionRestr_id (U : Cᵒᵖ) (z : (extensionSections A K U).M) :
    (extensionRestr A K (𝟙 U)).toFun z = z :=
  extensionSections_addHom_apply_eq A K (extensionRestr A K (𝟙 U)).toFun.toAddMonoidHom
    (AddMonoidHom.id _) (fun p x b => by
      refine (extensionRestr_pure A K (𝟙 U) p x b).trans ?_
      exact congrArg (fun b => extensionPure A K U x (bimElt A U b))
        (DifferentialGradedAlgebra.sectionRestrictRing_id A U b)) z

/-- The restriction homomorphism along a composite `b ≫ a` is the restriction along `b` followed
by the restriction along `a`. -/
theorem extensionRestr_comp {U V W : Cᵒᵖ} (a : V ⟶ U) (b : W ⟶ V)
    (z : (extensionSections A K W).M) :
    (extensionRestr A K (b ≫ a)).toFun z =
      (extensionRestr A K a).toFun ((extensionRestr A K b).toFun z) :=
  extensionSections_addHom_apply_eq A K (extensionRestr A K (b ≫ a)).toFun.toAddMonoidHom
    ((extensionRestr A K a).toFun.toAddMonoidHom.comp
      (extensionRestr A K b).toFun.toAddMonoidHom) (fun p x c => by
    refine (extensionRestr_pure A K (b ≫ a) p x c).trans ?_
    refine Eq.trans ?_ (congrArg (extensionRestr A K a).toFun
      (extensionRestr_pure A K b p x c)).symm
    refine Eq.trans ?_ (extensionRestr_pure A K a p x _).symm
    exact congrArg (fun c => extensionPure A K U x (bimElt A U c))
      (DifferentialGradedAlgebra.sectionRestrictRing_comp A a b c)) z

/-- **The presheaf of section modules `U ↦ K ⊗_R A(U)`.** -/
def extensionSystem : SectionSystem.{u, u, u, u} A where
  obj U := extensionSections A K U
  restr a := extensionRestr A K a
  restr_id U z := extensionRestr_id A K U z
  restr_comp a b z := extensionRestr_comp A K a b z

variable {K} {L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- A cochain map, tensored with `A(U)`. -/
abbrev extensionSectionsMap (f : K ⟶ L) (U : Cᵒᵖ) :
    extensionSections A K U ⟶ extensionSections A L U :=
  (tensorCompFunctor (extensionBimodule A U)).map
    ((_root_.DifferentialGradedModule.degreeZeroTotalFunctor (ULift.{u} ℤ) R).map f)

/-- A cochain map `f`, tensored with `A(U)`, sends a pure tensor `x ⊗ y` to `f x ⊗ y`. -/
theorem extensionSectionsMap_pure (f : K ⟶ L) (U : Cᵒᵖ) (x : (baseModule K).M)
    (y : (extensionBimodule A U).rightModule.M) :
    (extensionSectionsMap A f U).toFun (extensionPure A K U x y) =
      extensionPure A L U
        (((_root_.DifferentialGradedModule.degreeZeroTotalFunctor (ULift.{u} ℤ) R).map f).toFun x)
        y :=
  tensorCompFunctor_map_pure' (extensionBimodule A U) _ x y

/-- **A cochain map, tensored with `A`**, as a morphism of presheaves of section modules. -/
def extensionSystemMap (f : K ⟶ L) : extensionSystem A K ⟶ extensionSystem A L where
  app U := extensionSectionsMap A f U
  naturality {U V} a z := by
    have key : (extensionRestr A L a).toFun.toAddMonoidHom.comp
        (extensionSectionsMap A f V).toFun.toAddMonoidHom =
        (extensionSectionsMap A f U).toFun.toAddMonoidHom.comp
          (extensionRestr A K a).toFun.toAddMonoidHom := by
      refine tensorObj_addHom_ext_homogeneous _ _ _ _ fun p q x y => ?_
      show (extensionRestr A L a).toFun ((extensionSectionsMap A f V).toFun
          (extensionPure A K V x y)) =
        (extensionSectionsMap A f U).toFun ((extensionRestr A K a).toFun
          (extensionPure A K V x y))
      rw [extensionSectionsMap_pure, extensionRestr_pure A K a p x, extensionSectionsMap_pure]
      exact extensionRestr_pure A L a p ⟨_,
        ((_root_.DifferentialGradedModule.degreeZeroTotalFunctor (ULift.{u} ℤ) R).map f).map_grading
          p x x.2⟩ y
    exact DFunLike.congr_fun key z

/-- **The presheaves of section modules `U ↦ K ⊗_R A(U)`, functorially in `K`.** -/
def extensionSystemFunctor : CochainComplex (ModuleCat.{u} R) ℤ ⥤ SectionSystem.{u, u, u, u} A where
  obj K := extensionSystem A K
  map f := extensionSystemMap A f
  map_id K := SectionSystem.hom_ext.{u, u, u, u} fun U => by
    show (tensorCompFunctor (extensionBimodule A U)).map
      ((_root_.DifferentialGradedModule.degreeZeroTotalFunctor (ULift.{u} ℤ) R).map (𝟙 K)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  map_comp f g := SectionSystem.hom_ext.{u, u, u, u} fun U => by
    show (tensorCompFunctor (extensionBimodule A U)).map
      ((_root_.DifferentialGradedModule.degreeZeroTotalFunctor (ULift.{u} ℤ) R).map (f ≫ g)) = _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rfl

/-- **Extension of scalars `K ↦ K ⊗_R A`** from complexes of `R`-modules to right differential
graded `A`-modules: the realization of the presheaf of section modules `U ↦ K ⊗_R A(U)`. -/
def extendFunctor : CochainComplex (ModuleCat.{u} R) ℤ ⥤
    _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A :=
  extensionSystemFunctor A ⋙ SectionSystem.realizeFunctor.{u, u, u, u} A

/-- **The sections of `K ⊗_R A` over `U` are `K ⊗_R A(U)`.** -/
def extendSectionsIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (U : Cᵒᵖ) :
    ((extendFunctor A).obj K).sectionModule U ≅ extensionSections A K U :=
  (extensionSystem A K).sectionsIso U

end Stacks.ChaoticSite

end
