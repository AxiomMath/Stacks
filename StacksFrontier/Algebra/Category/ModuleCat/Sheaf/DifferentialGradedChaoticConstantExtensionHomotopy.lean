module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticConstantAdjunction

/-!
# Extension of scalars from the constant ring on homotopy categories

Let `C` be a category with the chaotic topology, `R` a commutative ring and `A` a sheaf of
differential graded algebras over the constant sheaf of rings with value `R`. Extension of
scalars `K ↦ K ⊗_R A` carries homotopic maps of complexes of `R`-modules to homotopic
homomorphisms of right differential graded `A`-modules, so it descends to the homotopy
categories, and the adjunction `- ⊗_R A ⊣ Γ` descends with it.

## Main definitions

* `Stacks.ChaoticSite.baseModuleHomotopy`: a homotopy of maps of complexes of `R`-modules, read
  as a homotopy of differential graded modules over `R` in degree zero.
* `Stacks.ChaoticSite.extensionSystemHomotopy`: the extension of scalars of a homotopy, as a
  homotopy of presheaves of section modules.
* `Stacks.ChaoticSite.homotopyExtend`: **extension of scalars on the homotopy categories**,
  `K(R) ⥤ K(A, d)`.
* `Stacks.ChaoticSite.homotopyExtendAdjunction`: **the adjunction
  `K(- ⊗_R A) ⊣ K(Γ)` of homotopy categories.**

## References

* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
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

variable {C : Type u} [SmallCategory C] {R : Type u} [CommRing R]

end Stacks.ChaoticSite

namespace CategoryTheory.Quotient

variable {C D : Type*} [Category C] [Category D] (r : HomRel C) (s : HomRel D)
  [Congruence r] [Congruence s] {F : C ⥤ D} {G : D ⥤ C}

/-- **An adjunction descends to quotient categories** along congruences respected by both
functors: the unit and counit are the images of the given ones. -/
def liftAdjunction (adj : F ⊣ G)
    (hF : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), r f g → s (F.map f) (F.map g))
    (hG : ∀ ⦃X Y : D⦄ (f g : X ⟶ Y), s f g → r (G.map f) (G.map g)) :
    lift r (F ⋙ functor s) (fun _ _ f g h => CategoryTheory.Quotient.sound s (hF f g h)) ⊣
      lift s (G ⋙ functor r) (fun _ _ f g h => CategoryTheory.Quotient.sound r (hG f g h)) where
  unit := natTransLift r
    { app X := (functor r).map (adj.unit.app X)
      naturality X Y f := by
        change (functor r).map f ≫ (functor r).map (adj.unit.app Y) =
          (functor r).map (adj.unit.app X) ≫ (functor r).map (G.map (F.map f))
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (functor r).map (adj.unit.naturality f) }
  counit := natTransLift s
    { app Y := (functor s).map (adj.counit.app Y)
      naturality X Y f := by
        change (functor s).map (F.map (G.map f)) ≫ (functor s).map (adj.counit.app Y) =
          (functor s).map (adj.counit.app X) ≫ (functor s).map f
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (functor s).map (adj.counit.naturality f) }
  left_triangle_components X := by
    obtain ⟨X⟩ := X
    change (functor s).map (F.map (adj.unit.app X)) ≫ (functor s).map (adj.counit.app (F.obj X)) =
      𝟙 _
    rw [← Functor.map_comp]
    exact (congrArg (functor s).map (adj.left_triangle_components X)).trans ((functor s).map_id _)
  right_triangle_components Y := by
    obtain ⟨Y⟩ := Y
    change (functor r).map (adj.unit.app (G.obj Y)) ≫ (functor r).map (G.map (adj.counit.app Y)) =
      𝟙 _
    rw [← Functor.map_comp]
    exact (congrArg (functor r).map (adj.right_triangle_components Y)).trans ((functor r).map_id _)

end CategoryTheory.Quotient

namespace Stacks.ChaoticSite

attribute [local instance] _root_.SheafOfModules.GradedAlgebra.sectionsGOne
  _root_.SheafOfModules.GradedAlgebra.sectionsGMul _root_.SheafOfModules.GradedAlgebra.sectionsGRing
  Stacks.uliftIntAlgebra

open _root_.SheafOfModules _root_.SheafOfModules.DifferentialGradedModule
  DifferentialGraded.Bimodule

variable {C : Type u} [SmallCategory C] {R : Type u} [CommRing R]

/-! ### Homotopies of complexes as homotopies of modules in degree zero -/

section BaseHomotopy

attribute [local instance] _root_.DifferentialGradedModule.degreeZeroOppositeModule

variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} {f g : K ⟶ L} (H : Homotopy f g)

/-- A homotopy, as a linear map of the direct sums of the terms, of degree `-1`. -/
def baseHomotopyLin : (DirectSum ℤ fun n => K.X n) →ₗ[R] (DirectSum ℤ fun n => L.X n) :=
  DirectSum.toModule R ℤ _ fun p =>
    (DirectSum.lof R ℤ (fun n => L.X n) (p - 1)).comp (H.hom p (p - 1)).hom

theorem baseHomotopyLin_of (p : ℤ) (x : K.X p) :
    baseHomotopyLin H (DirectSum.of (fun n => K.X n) p x) =
      DirectSum.of (fun n => L.X n) (p - 1) (H.hom p (p - 1) x) := by
  change baseHomotopyLin H (DirectSum.lof R ℤ (fun n => K.X n) p x) = _
  rw [baseHomotopyLin, DirectSum.toModule_lof]
  rfl

theorem baseHomotopyLin_of' (q m : ℤ) (h : q - 1 = m) (x : K.X q) :
    baseHomotopyLin H (DirectSum.of (fun n => K.X n) q x) =
      DirectSum.of (fun n => L.X n) m (H.hom q m x) := by
  subst h
  exact baseHomotopyLin_of H q x

theorem complexDifferential_of' (M : CochainComplex (ModuleCat.{u} R) ℤ) (m n : ℤ) (h : m + 1 = n)
    (x : M.X m) :
    _root_.DifferentialGradedModule.complexDifferential (R := ULift.{u} ℤ) M
        (DirectSum.of (fun n => M.X n) m x) =
      DirectSum.of (fun n => M.X n) n (M.d m n x) := by
  subst h
  exact _root_.DifferentialGradedModule.complexDifferential_of M m x

theorem baseHomotopy_eq_of (p : ℤ) (x : K.X p) :
    DirectSum.of (fun n => L.X n) p (f.f p x) - DirectSum.of (fun n => L.X n) p (g.f p x) =
      DirectSum.of (fun n => L.X n) p (L.d (p - 1) p (H.hom p (p - 1) x)) +
        DirectSum.of (fun n => L.X n) p (H.hom (p + 1) p (K.d p (p + 1) x)) := by
  have hc := congrArg (fun φ => φ.hom x) (H.comm p)
  simp only [ModuleCat.hom_add, LinearMap.add_apply] at hc
  rw [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl),
    prevD_eq H.hom (show (ComplexShape.up ℤ).Rel (p - 1) p from by simp)] at hc
  rw [← map_sub, ← map_add]
  congr 1
  change f.f p x - g.f p x = _
  rw [hc]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  change (H.hom (p + 1) p) ((K.d p (p + 1)) x) + (L.d (p - 1) p) ((H.hom p (p - 1)) x) + g.f p x -
    g.f p x = _
  abel

theorem baseHomotopy_eq (x : DirectSum ℤ fun n => K.X n) :
    DirectSum.lmap (fun n => (f.f n).hom) x - DirectSum.lmap (fun n => (g.f n).hom) x =
      _root_.DifferentialGradedModule.complexDifferential (R := ULift.{u} ℤ) L
          (baseHomotopyLin H x) +
        baseHomotopyLin H (_root_.DifferentialGradedModule.complexDifferential (R := ULift.{u} ℤ) K x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, sub_zero, add_zero]
  | add x y hx hy =>
    simp only [map_add]
    rw [add_sub_add_comm, hx, hy]
    abel
  | of p x =>
    rw [DirectSum.lmap_of, DirectSum.lmap_of, baseHomotopyLin_of,
      complexDifferential_of' L (p - 1) p (by omega),
      _root_.DifferentialGradedModule.complexDifferential_of, baseHomotopyLin_of' H (p + 1) p (by omega)]
    exact baseHomotopy_eq_of H p x

/-- **A homotopy of maps of complexes of `R`-modules, read as a homotopy of differential graded
modules over `R` in degree zero.** -/
def baseModuleHomotopy :
    _root_.DifferentialGradedModule.Homotopy
      ((_root_.DifferentialGradedModule.degreeZeroTotalFunctor (ULift.{u} ℤ) R).map f)
      ((_root_.DifferentialGradedModule.degreeZeroTotalFunctor (ULift.{u} ℤ) R).map g) where
  toLinearMap :=
    { toFun := baseHomotopyLin H
      map_add' := map_add _
      map_smul' := fun a x => (baseHomotopyLin H).map_smul _ x }
  map_grading p x hx := by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨H.hom p (p - 1) y, (baseHomotopyLin_of H p y).symm⟩
  homotopy_eq x := baseHomotopy_eq H x

end BaseHomotopy

/-! ### Extension of scalars of a homotopy -/

section ExtensionHomotopy

variable (A : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (constCommRingSheaf (C := C) R)))
  {K L : CochainComplex (ModuleCat.{u} R) ℤ} {f g : K ⟶ L} (H : Homotopy f g)

theorem baseModuleHomotopy_mem (p : ℤ) (x : (baseModule K).grading p) :
    (baseModuleHomotopy H).toLinearMap (x : (baseModule K).M) ∈ (baseModule L).grading (p - 1) :=
  (baseModuleHomotopy H).map_grading p x x.2

/-- **The extension of scalars of a homotopy**, as a homotopy of presheaves of section modules:
over `U` it is the homotopy tensored with `A(U)`. -/
def extensionSystemHomotopy :
    SectionSystem.Homotopy.{u, u, u, u} (extensionSystemMap A f) (extensionSystemMap A g) where
  app U := tensorHomotopy (extensionBimodule A U) (baseModuleHomotopy H)
  naturality {U V} a z := by
    have key : (extensionRestr A L a).toFun.toAddMonoidHom.comp
        (tensorHomotopy (extensionBimodule A V) (baseModuleHomotopy H)).toLinearMap.toAddMonoidHom =
        (tensorHomotopy (extensionBimodule A U) (baseModuleHomotopy H)).toLinearMap.toAddMonoidHom.comp
          (extensionRestr A K a).toFun.toAddMonoidHom := by
      refine tensorObj_addHom_ext_homogeneous (extensionBimodule A V) (baseModule K) _ _
        fun p q x y => ?_
      show (extensionRestr A L a).toFun ((tensorHomotopy (extensionBimodule A V)
          (baseModuleHomotopy H)).toLinearMap (extensionPure A K V (x : (baseModule K).M) y)) =
        (tensorHomotopy (extensionBimodule A U) (baseModuleHomotopy H)).toLinearMap
          ((extensionRestr A K a).toFun (extensionPure A K V (x : (baseModule K).M) y))
      rw [tensorHomotopy_pure, extensionRestr_pure A K a p x, tensorHomotopy_pure]
      exact extensionRestr_pure A L a (p - 1) ⟨_, baseModuleHomotopy_mem H p x⟩ y
    exact DFunLike.congr_fun key z

/-- **Extension of scalars carries homotopic maps of complexes to homotopic homomorphisms.** -/
theorem extendFunctor_map_homotopic (H : Homotopy f g) :
    _root_.SheafOfModules.DifferentialGradedModule.Homotopic
      ((extendFunctor A).map f) ((extendFunctor A).map g) :=
  SectionSystem.realizeMap_homotopic.{u, u, u, u} (extensionSystemHomotopy A H)

end ExtensionHomotopy

/-! ### Extension of scalars on the homotopy categories -/

section HomotopyCategory

variable (A : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (constCommRingSheaf (C := C) R)))

/-- **Extension of scalars on the homotopy categories**, `K(R) ⥤ K(A, d)`. -/
def homotopyExtend :
    _root_.HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) ⥤
      _root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.{u, u, u} A :=
  CategoryTheory.Quotient.lift _ (extendFunctor A ⋙
      _root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient A)
    fun _ _ _ _ ⟨H⟩ => (_root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient_map_eq_iff
      _ _).2 (extendFunctor_map_homotopic A H)

theorem quotient_comp_homotopyExtend :
    _root_.HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ) ⋙ homotopyExtend A =
      extendFunctor A ⋙ _root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient A :=
  CategoryTheory.Quotient.lift_spec _ _ _

variable (B : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (constRingSheaf (C := C) R))

/-- `B` read over the underlying sheaf of rings of the constant sheaf of commutative rings. -/
def castAlg : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (constCommRingSheaf (C := C) R)) := B

/-- The identification of right differential graded modules over `B` and over `castAlg B`. -/
def castDGMod : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} (castAlg B) ⥤
    _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} B := 𝟭 _

/-- **Extension of scalars on the homotopy categories**, with its target read over `B`. -/
def homotopyExtend' :
    _root_.HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) ⥤
      _root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.{u, u, u} B :=
  homotopyExtend (castAlg B)

/-- **The adjunction `K(- ⊗_R B) ⊣ K(Γ)` of homotopy categories**, descended from the adjunction
`- ⊗_R B ⊣ Γ` of differential graded modules. -/
def homotopyExtendAdjunction : homotopyExtend' B ⊣ homotopyGlobalSections R B :=
  CategoryTheory.Quotient.liftAdjunction _ _ (extendAdjunction (castAlg B))
    (fun _ _ _ _ ⟨H⟩ => extendFunctor_map_homotopic (castAlg B) H)
    (fun _ _ _ _ ⟨H⟩ => ⟨(globalF R).mapHomotopy H.toComplexHomotopy⟩)

end HomotopyCategory

end Stacks.ChaoticSite

end
