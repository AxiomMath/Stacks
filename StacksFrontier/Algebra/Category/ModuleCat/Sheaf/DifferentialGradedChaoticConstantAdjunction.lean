module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticConstantExtension

/-!
# Extension of scalars from the constant ring is left adjoint to the global sections

Let `C` be a category with the chaotic topology, `R` a commutative ring and `A` a sheaf of
differential graded algebras over the constant sheaf of rings with value `R`. Extension of
scalars `K ↦ K ⊗_R A` from complexes of `R`-modules to right differential graded `A`-modules is
left adjoint to the global sections `M ↦ Γ(C, M) = lim_U M(U)`. Under the identification of a
sheaf on the site `C` with an inverse system this is the adjunction `f^* ⊣ f_*` for the morphism
of ringed topoi `f : (Sh(C), A) → (Sh(pt), R)` of the proof of Proposition 0GZK.

## Main definitions

* `Stacks.ChaoticSite.extendUnit`: the unit `K ⟶ Γ(K ⊗_R A)`, `x ↦ (x ⊗ 1)_U`.
* `Stacks.ChaoticSite.extendCounit`: the counit `Γ(M) ⊗_R A ⟶ M`, `(m_V)_V ⊗ b ↦ m_U b` over
  `U`.
* `Stacks.ChaoticSite.extendAdjunction`: **the adjunction `- ⊗_R A ⊣ Γ`.**

## References

* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf CategoryTheory.Limits Stacks.PresheafOfModules

universe u

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.ChaoticSite

attribute [local instance] _root_.SheafOfModules.GradedAlgebra.sectionsGOne
  _root_.SheafOfModules.GradedAlgebra.sectionsGMul _root_.SheafOfModules.GradedAlgebra.sectionsGRing
  Stacks.uliftIntAlgebra

open _root_.SheafOfModules _root_.SheafOfModules.DifferentialGradedModule
  DifferentialGraded.Bimodule

variable {C : Type u} [SmallCategory C] {R : Type u} [CommRing R]
variable (A : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (constCommRingSheaf (C := C) R)))

variable (R) in
/-- The sections functor of `Stacks.ChaoticSite.sectionsFunctor`, on sheaves of modules over the
underlying sheaf of rings of the constant sheaf of commutative rings, which is the constant sheaf
of rings on the nose. -/
def sectionsF :
    _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (constCommRingSheaf (C := C) R)) ⥤
      (Cᵒᵖ ⥤ ModuleCat.{u} R) :=
  sectionsFunctor R

/-- The sections of a sheaf of modules over the constant sheaf of rings are `R`-modules. -/
instance sectionsModule' (M : _root_.SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (constCommRingSheaf (C := C) R))) (U : Cᵒᵖ) :
    Module R (M.val.obj U) :=
  (M.val.obj U).isModule

/-- The value of `sectionsF R` on `M` at `U` is the `R`-module `M(U)`. -/
@[simp] theorem sectionsF_obj_obj (M : _root_.SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (constCommRingSheaf (C := C) R))) (U : Cᵒᵖ) :
    ((sectionsF R).obj M).obj U = ModuleCat.of R (M.val.obj U) := rfl

/-- The restriction maps of `(sectionsF R).obj M` are those of `M`. -/
theorem sectionsF_obj_map_apply (M : _root_.SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (constCommRingSheaf (C := C) R))) {U V : Cᵒᵖ}
    (a : U ⟶ V) (x : M.val.obj U) : (((sectionsF R).obj M).map a).hom x = M.val.map a x := rfl

/-- The component at `U` of `(sectionsF R).map f` is the component of `f` at `U`. -/
theorem sectionsF_map_app_apply {M N : _root_.SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (constCommRingSheaf (C := C) R))} (f : M ⟶ N)
    (U : Cᵒᵖ) (x : M.val.obj U) : (((sectionsF R).map f).app U).hom x = f.val.app U x := rfl

/-- The sections functor `sectionsF R` is additive. -/
instance : (sectionsF (C := C) R).Additive where
  map_add := by
    intros
    ext
    rfl

variable (R) in
/-- The global sections `M ↦ Γ(C, M) = lim_U M(U)` of sheaves of modules over the constant sheaf of
rings. -/
def globalF :
    _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (constCommRingSheaf (C := C) R)) ⥤
      ModuleCat.{u} R :=
  sectionsF R ⋙ lim

/-- The global sections functor `globalF R` is additive. -/
instance : (globalF (C := C) R).Additive where
  map_add {_ _ f g} := by
    change lim.map ((sectionsF R).map (f + g)) = _
    rw [Functor.map_add, lim_map_add]
    rfl

/-- **The global sections `M ↦ Γ(C, M)`** of right differential graded `A`-modules: the global
sections of the underlying complex of sheaves of modules. -/
def globalSectionsFunctor :
    _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A ⥤
      CochainComplex (ModuleCat.{u} R) ℤ where
  obj M := ((globalF R).mapHomologicalComplex _).obj M.complex
  map f := ((globalF R).mapHomologicalComplex _).map f.toHomologicalComplex
  map_id M := ((globalF R).mapHomologicalComplex _).map_id M.complex
  map_comp f g := ((globalF R).mapHomologicalComplex _).map_comp
    f.toHomologicalComplex g.toHomologicalComplex

/-- The degree-`p` term of `Γ(M)` is the limit of the sections of `Mᵖ`. -/
theorem globalSectionsFunctor_obj_X (M : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A)
    (p : ℤ) : ((globalSectionsFunctor A).obj M).X p = limit ((sectionsF R).obj (M.complex.X p)) :=
  rfl

/-- The differential of `Γ(M)` is the limit of the differentials of the sections of `M`. -/
theorem globalSectionsFunctor_obj_d (M : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A)
    (p q : ℤ) : ((globalSectionsFunctor A).obj M).d p q = limMap ((sectionsF R).map (M.complex.d p q)) :=
  rfl

/-- The degree-`p` component of `Γ(φ)` is the limit of the maps of sections induced by `φ`. -/
theorem globalSectionsFunctor_map_f {M N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A}
    (φ : M ⟶ N) (p : ℤ) :
    ((globalSectionsFunctor A).map φ).f p = limMap ((sectionsF R).map (φ.toHomologicalComplex.f p)) :=
  rfl

/-! ### The projections of the global sections -/

section GlobalProjections

variable {A} (M : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A)

/-- The projection of the global sections onto the sections over `U`, in degree `p`. -/
def globalπ (p : ℤ) (U : Cᵒᵖ) :
    ((globalSectionsFunctor A).obj M).X p ⟶ ((sectionsF R).obj (M.complex.X p)).obj U :=
  limit.π ((sectionsF R).obj (M.complex.X p)) U

/-- The projections of a global section are compatible with restriction along `a : V ⟶ U`. -/
theorem globalπ_naturality (p : ℤ) {U V : Cᵒᵖ} (a : V ⟶ U)
    (s : ((globalSectionsFunctor A).obj M).X p) :
    M.sectionRestrictApp a p ((globalπ M p V).hom s) = (globalπ M p U).hom s :=
  congrArg (fun φ => φ.hom s) (limit.w ((sectionsF R).obj (M.complex.X p)) a)

/-- The projection over `U` of the differential of a global section is the differential of its
projection. -/
theorem globalπ_d (p : ℤ) (U : Cᵒᵖ) (s : ((globalSectionsFunctor A).obj M).X p) :
    (globalπ M (p + 1) U).hom (((globalSectionsFunctor A).obj M).d p (p + 1) s) =
      M.sectionDApp U p ((globalπ M p U).hom s) :=
  congrArg (fun φ => φ.hom s) (limMap_π ((sectionsF R).map (M.complex.d p (p + 1))) U)

/-- The projections over `U` commute with the differentials. -/
theorem d_globalπ (p : ℤ) (U : Cᵒᵖ) :
    ((globalSectionsFunctor A).obj M).d p (p + 1) ≫ globalπ M (p + 1) U =
      globalπ M p U ≫ ((sectionsF R).map (M.complex.d p (p + 1))).app U :=
  limMap_π ((sectionsF R).map (M.complex.d p (p + 1))) U

/-- The projections over `U` are natural in the differential graded module. -/
theorem globalπ_map {N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A}
    (φ : M ⟶ N) (p : ℤ) (U : Cᵒᵖ) :
    ((globalSectionsFunctor A).map φ).f p ≫ globalπ N p U =
      globalπ M p U ≫ ((sectionsF R).map (φ.toHomologicalComplex.f p)).app U :=
  limMap_π ((sectionsF R).map (φ.toHomologicalComplex.f p)) U

/-- A map into the degree-`p` global sections is determined by its projections. -/
theorem globalπ_hom_ext {p : ℤ} {X : ModuleCat.{u} R}
    {f g : X ⟶ ((globalSectionsFunctor A).obj M).X p}
    (h : ∀ U, f ≫ globalπ M p U = g ≫ globalπ M p U) : f = g :=
  limit.hom_ext h

/-- The map into the degree-`p` global sections given by a compatible family. -/
def globalLift (p : ℤ) (c : Cone ((sectionsF R).obj (M.complex.X p))) :
    c.pt ⟶ ((globalSectionsFunctor A).obj M).X p :=
  limit.lift _ c

/-- The projection over `U` of the map given by a compatible family is its `U`-th member. -/
@[reassoc]
theorem globalLift_π (p : ℤ) (c : Cone ((sectionsF R).obj (M.complex.X p))) (U : Cᵒᵖ) :
    globalLift M p c ≫ globalπ M p U = c.π.app U :=
  limit.lift_π c U

end GlobalProjections

/-! ### The unit -/

section Unit

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- An element of the degree-`p` term of `K`, in the differential graded module `⊕ₙ Kⁿ`. -/
abbrev baseElt (p : ℤ) (k : K.X p) : (baseModule K).M :=
  DirectSum.of (fun n => K.X n) p k

/-- An element of `Kᵖ` is homogeneous of degree `p` in `⊕ₙ Kⁿ`. -/
theorem baseElt_mem (p : ℤ) (k : K.X p) : baseElt K p k ∈ (baseModule K).grading p := ⟨k, rfl⟩

/-- The right action of `s : R` on the image of `k` in `⊕ₙ Kⁿ` is the image of `s • k`. -/
theorem op_smul_baseElt (p : ℤ) (s : R) (k : K.X p) :
    @HSMul.hSMul (baseDGA R).Aᵐᵒᵖ (baseModule K).M (baseModule K).M
      (@instHSMul _ _ (baseModule K).rmodule.toSMul) (MulOpposite.op s) (baseElt K p k) =
      baseElt K p (s • k) :=
  ((DirectSum.lof R ℤ (fun n => K.X n) p).map_smul s k).symm

/-- The differential of `⊕ₙ Kⁿ` on the image of `k : Kᵖ` is the image of `d k`. -/
theorem d_baseElt (p : ℤ) (k : K.X p) :
    (baseModule K).d (baseElt K p k) = baseElt K (p + 1) (K.d p (p + 1) k) :=
  _root_.DifferentialGradedModule.complexDifferential_lof K p k

/-- The unit on an element, as an element of `K ⊗_R A(U)`. -/
def unitElt (U : Cᵒᵖ) (x : (baseModule K).M) : (extensionSections A K U).M :=
  (extensionUnit A K U).toFun x

/-- The unit sends `x` to the pure tensor `x ⊗ 1`. -/
theorem unitElt_eq (U : Cᵒᵖ) (x : (baseModule K).M) :
    unitElt A K U x = extensionPure A K U x (bimElt A U 1) := extensionUnit_toFun A K U x

/-- The unit sends an element of `Kᵖ` to a homogeneous element of degree `p` of `K ⊗_R A(U)`. -/
theorem unitElt_mem (p : ℤ) (U : Cᵒᵖ) (k : K.X p) :
    unitElt A K U (baseElt K p k) ∈ (extensionSections A K U).grading p :=
  (extensionUnit A K U).map_grading p _ (baseElt_mem K p k)

/-- The unit is additive. -/
theorem unitElt_add (U : Cᵒᵖ) (x y : (baseModule K).M) :
    unitElt A K U (x + y) = unitElt A K U x + unitElt A K U y := map_add _ x y

/-- The unit is `R`-linear on each `Kᵖ`, with `R` acting on `K ⊗_R A(U)` through `A(U)`. -/
theorem unitElt_baseElt_smul (p : ℤ) (U : Cᵒᵖ) (r : R) (k : K.X p) :
    unitElt A K U (baseElt K p (r • k)) = A.sectionScalarOp U r • unitElt A K U (baseElt K p k) := by
  rw [unitElt, ← op_smul_baseElt]
  exact (extensionUnit A K U).map_smul (baseElt K p k) r

/-- The unit commutes with the differentials. -/
theorem unitElt_baseElt_d (p : ℤ) (U : Cᵒᵖ) (k : K.X p) :
    unitElt A K U (baseElt K (p + 1) (K.d p (p + 1) k)) =
      (extensionSections A K U).d (unitElt A K U (baseElt K p k)) := by
  rw [unitElt, ← d_baseElt]
  exact DFunLike.congr_fun (extensionUnit A K U).map_d (baseElt K p k)

/-- The unit is compatible with the restriction maps of `K ⊗_R A`. -/
theorem extensionRestr_extensionUnit {U V : Cᵒᵖ} (a : V ⟶ U) (x : (baseModule K).M) :
    (extensionRestr A K a).toFun (unitElt A K V x) = unitElt A K U x := by
  have key : (extensionRestr A K a).toFun.toAddMonoidHom.comp
      (extensionUnit A K V).toFun.toAddMonoidHom = (extensionUnit A K U).toFun.toAddMonoidHom := by
    refine DirectSum.addHom_ext fun p k => ?_
    show (extensionRestr A K a).toFun (unitElt A K V (baseElt K p k)) =
      unitElt A K U (baseElt K p k)
    rw [unitElt_eq, unitElt_eq]
    refine (extensionRestr_pure A K a p ⟨_, baseElt_mem K p k⟩ _).trans ?_
    congr 2
    exact map_one _
  exact DFunLike.congr_fun key x

/-- The degree-`p` part of the unit over `U`: `k ↦ k ⊗ 1`, a homogeneous section of `K ⊗_R A`. -/
def extendUnitElt (p : ℤ) (U : Cᵒᵖ) (k : K.X p) :
    (((extendFunctor A).obj K).complex.X p).val.obj U :=
  (extensionSystem A K).eltPiece ⟨unitElt A K U (baseElt K p k), unitElt_mem A K p U k⟩

/-- The section `extendUnitElt A K p U k`, read in `K ⊗_R A(U)`, is `k ⊗ 1`. -/
theorem pieceElt_extendUnitElt (p : ℤ) (U : Cᵒᵖ) (k : K.X p) :
    ((extensionSystem A K).pieceElt (extendUnitElt A K p U k) : ((extensionSystem A K).obj U).M) =
      unitElt A K U (baseElt K p k) := rfl

/-- The differential of `K ⊗_R A` is the sheaf differential of its section system. -/
theorem extendFunctor_obj_complex_d (p : ℤ) :
    ((extendFunctor A).obj K).complex.d p (p + 1) = (extensionSystem A K).dSheaf p :=
  (extensionSystem A K).realize_complex_d p

/-- The degree-`p` part of the unit over `U`, as an `R`-linear map. -/
def extendUnitApp (p : ℤ) (U : Cᵒᵖ) :
    K.X p ⟶ ((sectionsF R).obj (((extendFunctor A).obj K).complex.X p)).obj U :=
  ModuleCat.ofHom
    { toFun := extendUnitElt A K p U
      map_add' k k' := (extensionSystem A K).pieceElt_injective (by
        rw [pieceElt_extendUnitElt,
          show baseElt K p (k + k') = baseElt K p k + baseElt K p k' from map_add _ _ _,
          unitElt_add]
        rfl)
      map_smul' r k := (extensionSystem A K).pieceElt_injective (by
        rw [pieceElt_extendUnitElt, unitElt_baseElt_smul]
        rfl) }

/-- The map `extendUnitApp A K p U` sends `k` to `extendUnitElt A K p U k`. -/
theorem extendUnitApp_apply (p : ℤ) (U : Cᵒᵖ) (k : K.X p) :
    (extendUnitApp A K p U).hom k = extendUnitElt A K p U k := rfl

/-- The degree-`p` parts of the unit are compatible with restriction along `a : V ⟶ U`. -/
theorem extendUnitApp_naturality (p : ℤ) {U V : Cᵒᵖ} (a : V ⟶ U) :
    extendUnitApp A K p V ≫
        ((sectionsF R).obj (((extendFunctor A).obj K).complex.X p)).map a =
      extendUnitApp A K p U := by
  ext k
  change (((extendFunctor A).obj K).complex.X p).val.map a (extendUnitElt A K p V k) =
    extendUnitElt A K p U k
  exact (extensionSystem A K).pieceElt_injective
    (extensionRestr_extensionUnit A K a (baseElt K p k))

/-- The cone over the sections of `K ⊗_R A` in degree `p` given by the unit. -/
abbrev extendUnitCone (p : ℤ) :
    Cone ((sectionsF R).obj (((extendFunctor A).obj K).complex.X p)) where
  pt := K.X p
  π := { app U := extendUnitApp A K p U
         naturality _ _ a := (Category.id_comp _).trans (extendUnitApp_naturality A K p a).symm }

/-- The degree-`p` parts of the unit over `U` commute with the differentials. -/
theorem extendUnitApp_d (p : ℤ) (U : Cᵒᵖ) :
    extendUnitApp A K p U ≫ ((sectionsF R).map (((extendFunctor A).obj K).complex.d p (p + 1))).app U =
      K.d p (p + 1) ≫ extendUnitApp A K (p + 1) U := by
  ext k
  change (((extendFunctor A).obj K).complex.d p (p + 1)).val.app U (extendUnitElt A K p U k) =
    extendUnitElt A K (p + 1) U (K.d p (p + 1) k)
  rw [extendFunctor_obj_complex_d]
  exact (extensionSystem A K).pieceElt_injective (unitElt_baseElt_d A K p U k).symm

/-- **The unit `K ⟶ Γ(K ⊗_R A)`**, `x ↦ (x ⊗ 1)_U`. -/
def extendUnit : K ⟶ (globalSectionsFunctor A).obj ((extendFunctor A).obj K) where
  f p := globalLift ((extendFunctor A).obj K) p (extendUnitCone A K p)
  comm' p q hpq := by
    obtain rfl : p + 1 = q := hpq
    refine globalπ_hom_ext _ fun U => ?_
    rw [Category.assoc, Category.assoc, globalLift_π, d_globalπ, globalLift_π_assoc]
    exact extendUnitApp_d A K p U

/-- The projection over `U` of the degree-`p` unit is `extendUnitApp A K p U`. -/
@[reassoc]
theorem extendUnit_f_π (p : ℤ) (U : Cᵒᵖ) :
    (extendUnit A K).f p ≫ globalπ ((extendFunctor A).obj K) p U = extendUnitApp A K p U :=
  globalLift_π _ p _ U

end Unit

/-! ### The counit -/

section Counit

attribute [local instance] _root_.DifferentialGradedModule.degreeZeroComponentModule

variable {A} (M : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A)

/-- The sections over `U`, read over `R` through the structure homomorphism. -/
abbrev sectionsOverBase (U : Cᵒᵖ) : _root_.DifferentialGradedModule.{u, u, u} (baseDGA R) :=
  _root_.DifferentialGradedModule.restrictScalars (structureHom A U) (M.sectionModule U)

/-- The projection onto the sections over `U`, in degree `p`, as an element of the degree-`p` part
of `M(U)` read over `R`. -/
def globalπElt (p : ℤ) (U : Cᵒᵖ) (s : ((globalSectionsFunctor A).obj M).X p) :
    (sectionsOverBase M U).grading p :=
  ⟨DirectSum.of (M.sectionsPiece U) p ((globalπ M p U).hom s),
    Stacks.ExternalGrading.of_mem_intSummand _ p _⟩

/-- The projection onto the sections over `U`, as a map of complexes of `R`-modules into the
homogeneous components of `M(U)`. -/
def globalProjection (U : Cᵒᵖ) :
    (globalSectionsFunctor A).obj M ⟶
      _root_.DifferentialGradedModule.degreeZeroComplex (A := R) (sectionsOverBase M U) where
  f p := ModuleCat.ofHom
    { toFun := globalπElt M p U
      map_add' s s' := Subtype.ext ((congrArg (DirectSum.of (M.sectionsPiece U) p)
        (map_add (globalπ M p U).hom s s')).trans (map_add _ _ _))
      map_smul' r s := Subtype.ext ((congrArg (DirectSum.of (M.sectionsPiece U) p)
        (map_smul (globalπ M p U).hom r s)).trans
        (act_of_sectionScalar M U p ((globalπ M p U).hom s) r).symm) }
  comm' p q hpq := by
    obtain rfl : p + 1 = q := hpq
    ext s
    simp only [_root_.DifferentialGradedModule.degreeZeroComplex, CochainComplex.of_d]
    exact Subtype.ext ((congrArg (DirectSum.of (M.sectionsPiece U) (p + 1))
      (globalπ_d M p U s)).trans
      (sectionD_of M U p _).symm).symm

/-- **The projection of `Γ(M)` onto the sections over `U`**, as a homomorphism of differential
graded modules over `R`. -/
def globalProjHom (U : Cᵒᵖ) :
    baseModule ((globalSectionsFunctor A).obj M) ⟶ sectionsOverBase M U :=
  (_root_.DifferentialGradedModule.degreeZeroTotalFunctor (ULift.{u} ℤ) R).map
      (globalProjection M U) ≫
    _root_.DifferentialGradedModule.degreeZeroTotalHom (A := R) (sectionsOverBase M U)

/-- The projection of `Γ(M)` onto `M(U)` sends `s` in degree `p` to its projection over `U`. -/
theorem globalProjHom_baseElt (U : Cᵒᵖ) (p : ℤ) (s : ((globalSectionsFunctor A).obj M).X p) :
    (globalProjHom M U).toFun (baseElt _ p s) =
      DirectSum.of (M.sectionsPiece U) p ((globalπ M p U).hom s) := by
  show _root_.DifferentialGradedModule.degreeZeroTotalLinear (A := R) (sectionsOverBase M U)
    (DirectSum.lmap (fun n => ((globalProjection M U).f n).hom)
      (DirectSum.of (fun n => ((globalSectionsFunctor A).obj M).X n) p s)) = _
  rw [DirectSum.lmap_of, _root_.DifferentialGradedModule.degreeZeroTotalLinear_of]
  rfl

/-- The counit over `U`: `Γ(M) ⊗_R A(U) ⟶ M(U)`, `s ⊗ b ↦ s_U b`, the transpose of the projection
onto the sections over `U`. -/
def counitSections (U : Cᵒᵖ) :
    (extensionSystem A ((globalSectionsFunctor A).obj M)).obj U ⟶ (sectionSystem A M).obj U :=
  plainTranspose (structureHom A U) (globalProjHom M U)

/-- The counit over `U` sends `s ⊗ b` to `s_U b`. -/
theorem counitSections_pure (U : Cᵒᵖ) (p : ℤ) (s : ((globalSectionsFunctor A).obj M).X p)
    (b : (extensionBimodule A U).rightModule.M) :
    (counitSections M U).toFun (extensionPure A _ U (baseElt _ p s) b) =
      M.act U (DirectSum.of (M.sectionsPiece U) p ((globalπ M p U).hom s)) b :=
  (plainTranspose_pure (structureHom A U) (globalProjHom M U) p ⟨_, baseElt_mem _ p s⟩ b).trans
    (congrArg (fun w => M.act U w b) (globalProjHom_baseElt M U p s))

/-- Additive maps out of `K ⊗_R A(U)` agree when they agree on the pure tensors `k ⊗ y` with `k`
in some `Kᵖ`. -/
private theorem addHom_ext_extensionPure_baseElt (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (U : Cᵒᵖ) {P : Type*} [AddCommGroup P] (f g : (extensionSections A K U).M →+ P)
    (h : ∀ (p : ℤ) (k : K.X p) (y : (extensionBimodule A U).rightModule.M),
      f (extensionPure A K U (baseElt K p k) y) = g (extensionPure A K U (baseElt K p k) y)) :
    f = g := by
  refine tensorObj_addHom_ext_homogeneous _ _ _ _ fun p q x y => ?_
  obtain ⟨k, hk⟩ := x.2
  rw [← hk]
  exact h p k y

/-- The counit is compatible with restriction along `a : V ⟶ U` on pure tensors `s ⊗ y`. -/
theorem counitSections_naturality_pure {U V : Cᵒᵖ} (a : V ⟶ U) (p : ℤ)
    (s : ((globalSectionsFunctor A).obj M).X p) (y : (extensionBimodule A V).rightModule.M) :
    M.sectionRestrictAdd a ((counitSections M V).toFun (extensionPure A _ V (baseElt _ p s) y)) =
      (counitSections M U).toFun
        ((extensionRestr A _ a).toFun (extensionPure A _ V (baseElt _ p s) y)) := by
  have h1 := counitSections_pure M V p s y
  have h2 := extensionRestr_pure A ((globalSectionsFunctor A).obj M) a p ⟨_, baseElt_mem _ p s⟩ y
  have h3 := counitSections_pure M U p s
    (bimElt A U ((A.sectionRestriction a).toAlgebraHom y))
  have h4 := M.sectionRestrictAdd_act a
    (DirectSum.of (M.sectionsPiece V) p ((globalπ M p V).hom s)) y
  have h5 := sectionRestrictAdd_of M a p ((globalπ M p V).hom s)
  have h6 := globalπ_naturality M p a s
  refine (congrArg (M.sectionRestrictAdd a) h1).trans (h4.trans ?_)
  refine Eq.trans ?_ ((congrArg (counitSections M U).toFun h2).trans h3).symm
  exact congrArg (fun w => M.act U w (A.sectionRestrictRing a y))
    (h5.trans (congrArg (DirectSum.of (M.sectionsPiece U) p) h6))

/-- The counit is compatible with restriction along `a : V ⟶ U`. -/
theorem counitSections_naturality {U V : Cᵒᵖ} (a : V ⟶ U)
    (z : ((extensionSystem A ((globalSectionsFunctor A).obj M)).obj V).M) :
    M.sectionRestrictAdd a ((counitSections M V).toFun z) =
      (counitSections M U).toFun ((extensionRestr A _ a).toFun z) := by
  have key : (M.sectionRestrictAdd a).comp
      ((counitSections M V).toFun.toAddMonoidHom : _ →+ M.totalSections V) =
      ((counitSections M U).toFun.toAddMonoidHom : _ →+ M.totalSections U).comp
        (extensionRestr A ((globalSectionsFunctor A).obj M) a).toFun.toAddMonoidHom := by
    exact addHom_ext_extensionPure_baseElt _ _ _ _ fun p s y =>
      counitSections_naturality_pure M a p s y
  exact DFunLike.congr_fun key z

/-- The counit, as a morphism of presheaves of section modules
`(U ↦ Γ(M) ⊗_R A(U)) ⟶ Σ M`. -/
def counitSystem :
    SectionSystem.Hom.{u, u, u, u} (extensionSystem A ((globalSectionsFunctor A).obj M))
      (sectionSystem A M) :=
  SectionSystem.Hom.mk.{u, u, u, u} (X := extensionSystem A ((globalSectionsFunctor A).obj M))
    (Y := sectionSystem A M) (fun U => counitSections M U)
    (fun a z => counitSections_naturality M a z)

/-- **The counit `Γ(M) ⊗_R A ⟶ M`.** -/
def extendCounit : (extendFunctor A).obj ((globalSectionsFunctor A).obj M) ⟶ M :=
  ((SectionSystem.realizeAdjunction A).homEquiv _ _).symm (counitSystem M)

/-- The sections of the counit, read through the identification of the sections of a realization,
are the counit over `U`. -/
theorem sectionMap_extendCounit (U : Cᵒᵖ) :
    SectionSystem.Hom.app.{u, u, u, u}
        (SectionSystem.realizeSectionsIso (extensionSystem A ((globalSectionsFunctor A).obj M))).inv U ≫
      sectionMap (extendCounit M) U =
      counitSections M U := by
  have h2 : ((SectionSystem.realizeAdjunction A).homEquiv _ _) (extendCounit M) =
      counitSystem M := Equiv.apply_symm_apply _ _
  have h := SectionSystem.realizeAdjunction_homEquiv_apply (extendCounit M)
  rw [h2] at h
  exact (congrArg (fun φ => SectionSystem.Hom.app.{u, u, u, u} φ U) h).symm

end Counit

/-! ### Naturality and the triangle identities -/

section Adjunction

variable {A}

/-- The map `K ⊗_R A(U) ⟶ L ⊗_R A(U)` induced by `f` sends `k ⊗ 1` to `f k ⊗ 1`. -/
theorem extensionSectionsMap_unitElt {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)
    (U : Cᵒᵖ) (p : ℤ) (k : K.X p) :
    (extensionSectionsMap A f U).toFun (unitElt A K U (baseElt K p k)) =
      unitElt A L U (baseElt L p (f.f p k)) := by
  rw [unitElt_eq, unitElt_eq, extensionSectionsMap_pure]
  exact congrArg (fun x => extensionPure A L U x (bimElt A U 1))
    (DirectSum.lmap_of (fun n => (f.f n).hom) p k)

/-- The unit `K ⟶ Γ(K ⊗_R A)` is natural in `K`. -/
theorem extendUnit_naturality {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    f ≫ extendUnit A L = extendUnit A K ≫ (globalSectionsFunctor A).map ((extendFunctor A).map f) := by
  ext p : 1
  refine globalπ_hom_ext _ fun U => ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, Category.assoc,
    extendUnit_f_π, globalπ_map, extendUnit_f_π_assoc]
  ext k
  exact (extensionSystem A L).pieceElt_injective (extensionSectionsMap_unitElt f U p k).symm

/-- The counit over `U` is natural in `M` on pure tensors `s ⊗ y`. -/
theorem extensionSectionsMap_counitSections_pure
    {M N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A} (g : M ⟶ N) (U : Cᵒᵖ)
    (p : ℤ) (s : ((globalSectionsFunctor A).obj M).X p) (y : (extensionBimodule A U).rightModule.M) :
    (counitSections N U).toFun ((extensionSectionsMap A ((globalSectionsFunctor A).map g) U).toFun
        (extensionPure A _ U (baseElt _ p s) y)) =
      sectionMapAdd g U ((counitSections M U).toFun (extensionPure A _ U (baseElt _ p s) y)) := by
  have h1 : ((_root_.DifferentialGradedModule.degreeZeroTotalFunctor (ULift.{u} ℤ) R).map
      ((globalSectionsFunctor A).map g)).toFun (baseElt _ p s) =
      baseElt _ p (((globalSectionsFunctor A).map g).f p s) :=
    DirectSum.lmap_of (fun n => (((globalSectionsFunctor A).map g).f n).hom) p s
  have h2 := extensionSectionsMap_pure A ((globalSectionsFunctor A).map g) U (baseElt _ p s) y
  have h3 := counitSections_pure N U p (((globalSectionsFunctor A).map g).f p s) y
  have h4 := counitSections_pure M U p s y
  have h5 := sectionMapAdd_act g U (DirectSum.of (M.sectionsPiece U) p ((globalπ M p U).hom s)) y
  have h6 := sectionMapAdd_of g U p ((globalπ M p U).hom s)
  have h7 : (globalπ N p U).hom (((globalSectionsFunctor A).map g).f p s) =
      sectionMapApp g U p ((globalπ M p U).hom s) :=
    congrArg (fun φ => φ.hom s) (globalπ_map M g p U)
  refine (congrArg (counitSections N U).toFun (h2.trans (congrArg (fun x =>
    extensionPure A _ U x y) h1))).trans (h3.trans ?_)
  refine Eq.trans ?_ ((congrArg (sectionMapAdd g U) h4).trans h5).symm
  exact congrArg (fun w => N.act U w y)
    ((congrArg (DirectSum.of (N.sectionsPiece U) p) h7).trans h6.symm)

/-- The counit over `U` is natural in `M`. -/
theorem extensionSectionsMap_counitSections
    {M N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A} (g : M ⟶ N) (U : Cᵒᵖ) :
    extensionSectionsMap A ((globalSectionsFunctor A).map g) U ≫ counitSections N U =
      counitSections M U ≫ sectionMap g U := by
  refine _root_.DifferentialGradedModule.Hom.ext ?_
  have key : ((counitSections N U).toFun.toAddMonoidHom : _ →+ N.totalSections U).comp
      (extensionSectionsMap A ((globalSectionsFunctor A).map g) U).toFun.toAddMonoidHom =
      (sectionMapAdd g U).comp
        ((counitSections M U).toFun.toAddMonoidHom : _ →+ M.totalSections U) := by
    exact addHom_ext_extensionPure_baseElt _ _ _ _ fun p s y =>
      extensionSectionsMap_counitSections_pure g U p s y
  exact DFunLike.ext _ _ fun z => DFunLike.congr_fun key z

/-- Taking sections over `U` preserves composition. -/
theorem sectionMap_comp' {M N P : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A}
    (f : M ⟶ N) (g : N ⟶ P) (U : Cᵒᵖ) :
    sectionMap (f ≫ g) U = sectionMap f U ≫ sectionMap g U :=
  (sectionModuleFunctor A U).map_comp f g

/-- Identifying the sections of `K ⊗_R A` over `U` with `K ⊗_R A(U)` is natural in `K`. -/
theorem sectionsIso_inv_naturality {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)
    (U : Cᵒᵖ) :
    ((extensionSystem A K).sectionsIso U).inv ≫ sectionMap ((extendFunctor A).map f) U =
      extensionSectionsMap A f U ≫ ((extensionSystem A L).sectionsIso U).inv :=
  (Iso.inv_comp_eq _).mpr (((Iso.eq_comp_inv _).mpr
    (SectionSystem.sectionsIso_naturality (extensionSystemMap A f) U)).trans (Category.assoc _ _ _))

/-- The sections over `U` of the counit, read on `Γ(M) ⊗_R A(U)`, are the counit over `U`. -/
theorem sectionsIso_inv_extendCounit (U : Cᵒᵖ)
    (M : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A) :
    ((extensionSystem A ((globalSectionsFunctor A).obj M)).sectionsIso U).inv ≫
        sectionMap (extendCounit M) U = counitSections M U :=
  sectionMap_extendCounit M U

/-- The sections over `U` of a morphism of right differential graded `A`-modules, as a morphism of
the category of differential graded `A(U)`-modules. -/
def secMap {M N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A} (f : M ⟶ N)
    (U : Cᵒᵖ) : M.sectionModule U ⟶ N.sectionModule U :=
  sectionMap f U

/-- `secMap` preserves composition. -/
theorem secMap_comp {M N P : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A}
    (f : M ⟶ N) (g : N ⟶ P) (U : Cᵒᵖ) : secMap (f ≫ g) U = secMap f U ≫ secMap g U :=
  sectionMap_comp' f g U

/-- `secMap` preserves identities. -/
theorem secMap_id (M : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A) (U : Cᵒᵖ) :
    secMap (𝟙 M) U = 𝟙 _ :=
  (sectionModuleFunctor A U).map_id M

/-- Two morphisms of right differential graded `A`-modules agreeing on the sections over every `U`
are equal. -/
theorem hom_ext_of_secMap {M N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A}
    {f g : M ⟶ N} (h : ∀ U, secMap f U = secMap g U) : f = g :=
  hom_ext_of_sectionMap.{u, u, u, u} h

/-- The underlying function of `extendSectionsIso A K U` is `sectionsAddEquiv`. -/
theorem extendSectionsIso_hom_toFun (K : CochainComplex (ModuleCat.{u} R) ℤ) (U : Cᵒᵖ)
    (z : ((extendFunctor A).obj K).totalSections U) :
    (extendSectionsIso A K U).hom.toFun z = (extensionSystem A K).sectionsAddEquiv U z := rfl

/-- The counit over `U`, `Γ(M) ⊗_R A(U) ⟶ M(U)`. -/
def cU (M : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A) (U : Cᵒᵖ) :
    extensionSections A ((globalSectionsFunctor A).obj M) U ⟶ M.sectionModule U :=
  counitSections M U

/-- The counit `cU M U` sends `s ⊗ b` to `s_U b`. -/
theorem cU_pure (M : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A) (U : Cᵒᵖ)
    (p : ℤ) (s : ((globalSectionsFunctor A).obj M).X p)
    (b : (extensionBimodule A U).rightModule.M) :
    (cU M U).toFun (extensionPure A _ U (baseElt _ p s) b) =
      M.act U (DirectSum.of (M.sectionsPiece U) p ((globalπ M p U).hom s)) b :=
  counitSections_pure M U p s b

/-- The sections over `U` of the counit are `extendSectionsIso` followed by the counit over
`U`. -/
theorem secMap_extendCounit (U : Cᵒᵖ)
    (M : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A) :
    secMap (extendCounit M) U =
      (extendSectionsIso A ((globalSectionsFunctor A).obj M) U).hom ≫ cU M U :=
  ((Iso.eq_inv_comp _).mp (sectionMap_extendCounit M U).symm).symm

/-- Under `extendSectionsIso`, the sections over `U` of `f ⊗_R A` are `f ⊗_R A(U)`. -/
theorem secMap_extendFunctor_map {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)
    (U : Cᵒᵖ) :
    secMap ((extendFunctor A).map f) U ≫ (extendSectionsIso A L U).hom =
      (extendSectionsIso A K U).hom ≫ extensionSectionsMap A f U :=
  SectionSystem.sectionsIso_naturality (extensionSystemMap A f) U

/-- The counit `cU M U` is natural in `M`. -/
theorem extensionSectionsMap_cU {M N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A}
    (g : M ⟶ N) (U : Cᵒᵖ) :
    extensionSectionsMap A ((globalSectionsFunctor A).map g) U ≫ cU N U =
      cU M U ≫ secMap g U :=
  extensionSectionsMap_counitSections g U

/-- The counit `Γ(M) ⊗_R A ⟶ M` is natural in `M`. -/
theorem extendCounit_naturality {M N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A}
    (g : M ⟶ N) :
    (extendFunctor A).map ((globalSectionsFunctor A).map g) ≫ extendCounit N =
      extendCounit M ≫ g := by
  refine hom_ext_of_secMap fun U => ?_
  rw [secMap_comp, secMap_comp, secMap_extendCounit, secMap_extendCounit, ← Category.assoc,
    secMap_extendFunctor_map, Category.assoc, extensionSectionsMap_cU, Category.assoc]

/-- The projection over `U` of the unit applied to `k : Kᵖ` is `extendUnitElt A K p U k`. -/
theorem extendUnit_π_apply (K : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℤ) (U : Cᵒᵖ)
    (k : K.X p) :
    (globalπ ((extendFunctor A).obj K) p U).hom ((extendUnit A K).f p k) =
      extendUnitElt A K p U k :=
  congrArg (fun φ => φ.hom k) (extendUnit_f_π A K p U)

/-- `extendSectionsIso A K U` sends a homogeneous section of degree `p` to its element of
`K ⊗_R A(U)`. -/
theorem extendSectionsIso_hom_of (K : CochainComplex (ModuleCat.{u} R) ℤ) (U : Cᵒᵖ) (p : ℤ)
    (e : ((extendFunctor A).obj K).sectionsPiece U p) :
    (extendSectionsIso A K U).hom.toFun
        (DirectSum.of (((extendFunctor A).obj K).sectionsPiece U) p e) =
      ((extensionSystem A K).cElt e).val :=
  (extensionSystem A K).sectionsAddEquiv_of U p e

/-- `extendSectionsIso A K U` sends the section `extendUnitElt A K p U k` to `k ⊗ 1`. -/
theorem extendSectionsIso_hom_extendUnitElt (K : CochainComplex (ModuleCat.{u} R) ℤ) (U : Cᵒᵖ)
    (p : ℤ) (k : K.X p) :
    (extendSectionsIso A K U).hom.toFun (DirectSum.of (((extendFunctor A).obj K).sectionsPiece U) p
      (extendUnitElt A K p U k)) = unitElt A K U (baseElt K p k) :=
  extendSectionsIso_hom_of K U p _

/-- `extendSectionsIso A K U` is compatible with the right action of `A(U)`. -/
theorem extendSectionsIso_hom_act (K : CochainComplex (ModuleCat.{u} R) ℤ) (U : Cᵒᵖ)
    (z : ((extendFunctor A).obj K).totalSections U) (b : A.toGradedAlgebra.totalSections U) :
    (extendSectionsIso A K U).hom.toFun (((extendFunctor A).obj K).act U z b) =
      MulOpposite.op (show (A.sectionAlgebra U).A from b) • (extendSectionsIso A K U).hom.toFun z :=
  (extensionSystem A K).sectionsAddEquiv_act U z b

/-- Over `U`, the composite of the unit `⊗_R A(U)`, the counit and `extendSectionsIso` fixes the
pure tensor `k ⊗ y`. -/
theorem triangle_left_core_pure (K : CochainComplex (ModuleCat.{u} R) ℤ) (U : Cᵒᵖ) (p : ℤ)
    (k : K.X p) (y : (extensionBimodule A U).rightModule.M) :
    (extendSectionsIso A K U).hom.toFun ((cU ((extendFunctor A).obj K) U).toFun
      ((extensionSectionsMap A (extendUnit A K) U).toFun
        (extensionPure A K U (baseElt K p k) y))) =
      extensionPure A K U (baseElt K p k) y := by
  have h1 : ((_root_.DifferentialGradedModule.degreeZeroTotalFunctor (ULift.{u} ℤ) R).map
      (extendUnit A K)).toFun (baseElt K p k) = baseElt _ p ((extendUnit A K).f p k) :=
    DirectSum.lmap_of (fun n => ((extendUnit A K).f n).hom) p k
  have h2 := extensionSectionsMap_pure A (extendUnit A K) U (baseElt K p k) y
  have h3 := cU_pure ((extendFunctor A).obj K) U p ((extendUnit A K).f p k) y
  have h4 := extendSectionsIso_hom_act (A := A) K U
    (DirectSum.of (((extendFunctor A).obj K).sectionsPiece U) p
      ((globalπ ((extendFunctor A).obj K) p U).hom ((extendUnit A K).f p k))) y
  have h5 := extendUnit_π_apply (A := A) K p U k
  have h6 := extendSectionsIso_hom_extendUnitElt (A := A) K U p k
  refine (congrArg
    (fun w => (extendSectionsIso A K U).hom.toFun ((cU ((extendFunctor A).obj K) U).toFun w))
    (h2.trans (congrArg (fun x => extensionPure A _ U x y) h1))).trans ?_
  refine (congrArg (extendSectionsIso A K U).hom.toFun h3).trans (h4.trans ?_)
  refine (congrArg (fun w => MulOpposite.op (show (A.sectionAlgebra U).A from y) •
    (extendSectionsIso A K U).hom.toFun
      (DirectSum.of (((extendFunctor A).obj K).sectionsPiece U) p w)) h5).trans ?_
  refine (congrArg (fun w => MulOpposite.op (show (A.sectionAlgebra U).A from y) • w)
    (h6.trans (unitElt_eq A K U _))).trans ?_
  exact extensionPure_one_smul A K U _ _

/-- Over `U`, the composite of the unit `⊗_R A(U)`, the counit and `extendSectionsIso` is the
identity of `K ⊗_R A(U)`. -/
theorem triangle_left_core (K : CochainComplex (ModuleCat.{u} R) ℤ) (U : Cᵒᵖ) :
    extensionSectionsMap A (extendUnit A K) U ≫ cU ((extendFunctor A).obj K) U ≫
      (extendSectionsIso A K U).hom = 𝟙 _ := by
  refine _root_.DifferentialGradedModule.Hom.ext ?_
  have key : (((extendSectionsIso A K U).hom.toFun.toAddMonoidHom :
      _ →+ (extensionSections A K U).M).comp
      (((cU ((extendFunctor A).obj K) U).toFun.toAddMonoidHom :
        _ →+ ((extendFunctor A).obj K).totalSections U).comp
        (extensionSectionsMap A (extendUnit A K) U).toFun.toAddMonoidHom)) =
      AddMonoidHom.id _ := by
    exact addHom_ext_extensionPure_baseElt _ _ _ _ fun p k y =>
      triangle_left_core_pure (A := A) K U p k y
  exact DFunLike.ext _ _ fun z => DFunLike.congr_fun key z

/-- The left triangle identity: `K ⊗_R A ⟶ Γ(K ⊗_R A) ⊗_R A ⟶ K ⊗_R A` is the identity. -/
theorem extendUnit_extendCounit_left (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (extendFunctor A).map (extendUnit A K) ≫ extendCounit ((extendFunctor A).obj K) = 𝟙 _ := by
  refine hom_ext_of_secMap fun U => ?_
  have h := triangle_left_core (A := A) K U
  rw [← Category.assoc] at h
  rw [secMap_comp, secMap_extendCounit, ← Category.assoc, secMap_extendFunctor_map,
    Category.assoc, ((Iso.comp_hom_eq_id _).mp h), Iso.hom_inv_id, secMap_id]

/-- The counit sends the section `s ⊗ 1` over `U` to the projection `s_U`. -/
theorem extendCounit_extendUnitElt
    (M : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A) (p : ℤ) (U : Cᵒᵖ)
    (s : ((globalSectionsFunctor A).obj M).X p) :
    ((extendCounit M).toHomologicalComplex.f p).val.app U (extendUnitElt A _ p U s) =
      (globalπ M p U).hom s := by
  apply DirectSum.of_injective (β := M.sectionsPiece U) p
  have h1 := congrArg (fun φ => φ.toFun (DirectSum.of
    (((extendFunctor A).obj ((globalSectionsFunctor A).obj M)).sectionsPiece U) p
      (extendUnitElt A _ p U s))) (secMap_extendCounit U M)
  have h2 := extendSectionsIso_hom_extendUnitElt (A := A) ((globalSectionsFunctor A).obj M) U p s
  have h3 := cU_pure M U p s (bimElt A U 1)
  refine (sectionMapAdd_of (extendCounit M) U p _).symm.trans (h1.trans ?_)
  refine (congrArg (cU M U).toFun (h2.trans (unitElt_eq A _ U _))).trans (h3.trans ?_)
  exact M.act_one U _

/-- The right triangle identity: `Γ(M) ⟶ Γ(Γ(M) ⊗_R A) ⟶ Γ(M)` is the identity. -/
theorem extendUnit_extendCounit_right
    (M : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A) :
    extendUnit A ((globalSectionsFunctor A).obj M) ≫ (globalSectionsFunctor A).map (extendCounit M) =
      𝟙 _ := by
  ext p : 1
  refine globalπ_hom_ext _ fun U => ?_
  rw [HomologicalComplex.comp_f, Category.assoc, globalπ_map, extendUnit_f_π_assoc,
    HomologicalComplex.id_f, Category.id_comp]
  ext s
  exact extendCounit_extendUnitElt M p U s

variable (A) in
/-- **Extension of scalars `K ↦ K ⊗_R A` is left adjoint to the global sections** `M ↦ Γ(C, M)`:
the adjunction `f^* ⊣ f_*` for the morphism of ringed topoi `(Sh(C), A) → (Sh(pt), R)`. -/
def extendAdjunction : extendFunctor A ⊣ globalSectionsFunctor A where
  unit := { app := fun K => extendUnit A K
            naturality := fun _ _ f => extendUnit_naturality f }
  counit := { app := fun M => extendCounit M
              naturality := fun _ _ g => extendCounit_naturality g }
  left_triangle_components K := extendUnit_extendCounit_left K
  right_triangle_components M := extendUnit_extendCounit_right M

/-- The unit of `extendAdjunction A` at `K` is `extendUnit A K`. -/
@[simp] theorem extendAdjunction_unit_app (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (extendAdjunction A).unit.app K = extendUnit A K := rfl

/-- The counit of `extendAdjunction A` at `M` is `extendCounit M`. -/
@[simp] theorem extendAdjunction_counit_app
    (M : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} A) :
    (extendAdjunction A).counit.app M = extendCounit M := rfl

end Adjunction

end Stacks.ChaoticSite

end
