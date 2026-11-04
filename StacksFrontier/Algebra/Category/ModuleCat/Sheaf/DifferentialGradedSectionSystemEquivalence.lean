module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticPullback

/-!
# Presheaves of section modules are differential graded modules on a chaotic site

Let `C` be a category with the chaotic topology, `O` a sheaf of commutative rings on it and
`(A, d)` a sheaf of differential graded `O`-algebras. A right differential graded `A`-module `N`
has, over every object `U`, the differential graded `A(U)`-module `N(U)` of its sections, and
restriction of sections makes these a presheaf of section modules `Σ N`. Conversely a presheaf
of section modules `X` has a realization, a right differential graded `A`-module whose sections
are `X(U)`. This file shows that the two constructions are mutually inverse equivalences: `Σ` is
fully faithful, and the realization is a quasi-inverse.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.sectionSystem`: the presheaf of section modules
  `Σ N` of a right differential graded `A`-module, and `sectionSystemFunctor` the functor
  `N ↦ Σ N`.
* `SheafOfModules.DifferentialGradedModule.homOfSectionSystem`: the morphism of right
  differential graded modules determined by a morphism of their presheaves of section modules.
* `SheafOfModules.DifferentialGradedModule.sectionSystemFullyFaithful`: `Σ` is fully faithful.
* `SheafOfModules.DifferentialGradedModule.SectionSystem.realizeSectionsIso`: the presheaf of
  section modules of a realization is the presheaf it realizes.
* `SheafOfModules.DifferentialGradedModule.sectionSystemEquivalence`: **the equivalence between
  right differential graded `A`-modules and presheaves of section modules.**
* `SheafOfModules.DifferentialGradedModule.SectionSystem.realizeAdjunction`: the realization is
  left adjoint to `Σ`, with unit the identification of the sections of a realization.

## Main results

* `SheafOfModules.DifferentialGradedModule.sectionMap_homOfSectionSystem`: the morphism
  determined by a morphism of presheaves of section modules has that morphism as its sections.
* `SheafOfModules.DifferentialGradedModule.SectionSystem.realizeAdjunction_homEquiv_apply`: the
  hom-set bijection of the adjunction is restriction to sections followed by the
  identification of the sections of the realization.

## Implementation notes

The degree-`n` component of the morphism determined by `h : Σ M ⟶ Σ N` is, over `U`, the
`n`-th coordinate of `h_U` applied to a section of `M^n(U)` placed in the summand of degree `n`.
That it is a morphism of sheaves of modules uses that the scalars `r · 1` of `A(U)` act on the
direct sum of sections by scalar multiplication, `act_sectionScalar`.

## References

* [Stacks Project, Section 24.33 (Tag 0GZ8)](https://stacks.math.columbia.edu/tag/0GZ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

variable {C : Type u} [Category.{v} C]
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{t}}

namespace DifferentialGradedModule

variable {A : DifferentialGradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}

/-! ### The scalars act by scalar multiplication on the sections -/

/-- The scalar `r · 1` of `A(U)` acting on a homogeneous section is scalar multiplication. -/
theorem act_of_sectionScalar (N : DifferentialGradedModule.{t, m, m} A) (U : Cᵒᵖ) (k : ℤ)
    (y : N.sectionsPiece U k)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U) :
    N.act U (DirectSum.of (N.sectionsPiece U) k y) (A.sectionScalar U r) =
      DirectSum.of (N.sectionsPiece U) k (r • y) := by
  rw [act_of, DifferentialGradedAlgebra.sectionScalar_apply, actOn_of,
    (N.mul k 0).map_smul_right U r y (A.one.eval U)]
  have h₁ : DirectSum.of (N.sectionsPiece U) (k + 0) (r • (N.mul k 0).app U y (A.one.eval U)) =
      r • DirectSum.of (N.sectionsPiece U) (k + 0) ((N.mul k 0).app U y (A.one.eval U)) :=
    (DirectSum.lof _ ℤ (N.sectionsPiece U) (k + 0)).map_smul r _
  rw [h₁, SheafOfModules.of_heq (add_zero k) (N.mul_one k U y)]
  exact ((DirectSum.lof _ ℤ (N.sectionsPiece U) k).map_smul r y).symm

/-- **The scalars `r · 1` of `A(U)` act on the sections over `U` by scalar multiplication.** -/
theorem act_sectionScalar (N : DifferentialGradedModule.{t, m, m} A) (U : Cᵒᵖ)
    (w : N.totalSections U)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U) :
    N.act U w (A.sectionScalar U r) = r • w := by
  induction w using DirectSum.induction_on with
  | zero => rw [map_zero, AddMonoidHom.zero_apply, smul_zero]
  | add w w' hw hw' => rw [map_add, AddMonoidHom.add_apply, hw, hw', smul_add]
  | of k y =>
      rw [act_of_sectionScalar]
      exact (DirectSum.lof _ ℤ (N.sectionsPiece U) k).map_smul r y

/-! ### The presheaf of section modules of a differential graded module -/

variable (A) in
/-- **The presheaf of section modules `Σ N`** of a right differential graded `A`-module: over `U`
the differential graded `A(U)`-module `N(U)` of sections, with restriction of sections. -/
def sectionSystem (N : DifferentialGradedModule.{t, m, m} A) : SectionSystem A where
  obj U := N.sectionModule U
  restr a := N.sectionModuleRestriction a
  restr_id U x := sectionRestrictAdd_id N U x
  restr_comp a b x := sectionRestrictAdd_comp N a b x

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The module of `Σ N` over `U` is the module `N(U)` of sections. -/
@[simp] theorem sectionSystem_obj (N : DifferentialGradedModule.{t, m, m} A) (U : Cᵒᵖ) :
    (sectionSystem A N).obj U = N.sectionModule U := rfl

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The restriction maps of `Σ N` are restriction of sections. -/
@[simp] theorem sectionSystem_restrFun (N : DifferentialGradedModule.{t, m, m} A)
    {U V : Cᵒᵖ} (a : V ⟶ U) (x : N.totalSections V) :
    (sectionSystem A N).restrFun a x = N.sectionRestrictAdd a x := rfl

variable (A) in
/-- **The functor `N ↦ Σ N`.** -/
def sectionSystemFunctor : DifferentialGradedModule.{t, m, m} A ⥤ SectionSystem A where
  obj N := sectionSystem A N
  map f := ⟨fun U => sectionMap f U, fun a x => sectionRestrictAdd_sectionMapAdd f a x⟩
  map_id N := SectionSystem.hom_ext fun U => (sectionModuleFunctor A U).map_id N
  map_comp f g := SectionSystem.hom_ext fun U => (sectionModuleFunctor A U).map_comp f g

/-- The functor `N ↦ Σ N` sends `N` to `Σ N`. -/
@[simp] theorem sectionSystemFunctor_obj (N : DifferentialGradedModule.{t, m, m} A) :
    (sectionSystemFunctor A).obj N = sectionSystem A N := rfl

/-- The component over `U` of `Σ f` is the map of sections `sectionMap f U`. -/
@[simp] theorem sectionSystemFunctor_map_app {M N : DifferentialGradedModule.{t, m, m} A}
    (f : M ⟶ N) (U : Cᵒᵖ) : ((sectionSystemFunctor A).map f).app U = sectionMap f U := rfl

/-! ### The morphism determined by a morphism of presheaves of section modules -/

section HomOfSectionSystem

variable {M N : DifferentialGradedModule.{t, m, m} A}
  (h : sectionSystem A M ⟶ sectionSystem A N)

/-- `h_U` on the total sections, as an additive map. -/
def sectionFun (U : Cᵒᵖ) : M.totalSections U →+ N.totalSections U :=
  (h.app U).toFun.toAddMonoidHom

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- `sectionFun h U` is the underlying function of `h_U`. -/
theorem sectionFun_apply (U : Cᵒᵖ) (z : M.totalSections U) :
    sectionFun h U z = (h.app U).toFun z := rfl

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- `sectionFun h` commutes with restriction of sections. -/
theorem sectionFun_naturality {U V : Cᵒᵖ} (a : V ⟶ U) (z : M.totalSections V) :
    N.sectionRestrictAdd a (sectionFun h V z) = sectionFun h U (M.sectionRestrictAdd a z) :=
  h.naturality a z

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- `sectionFun h U` commutes with the action of `A(U)` on sections. -/
theorem sectionFun_act (U : Cᵒᵖ) (z : M.totalSections U) (s : A.toGradedAlgebra.totalSections U) :
    sectionFun h U (M.act U z s) = N.act U (sectionFun h U z) s :=
  (h.app U).map_smul z s

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- `sectionFun h U` commutes with the differentials of the sections. -/
theorem sectionFun_sectionD (U : Cᵒᵖ) (z : M.totalSections U) :
    sectionFun h U (M.sectionD U z) = N.sectionD U (sectionFun h U z) :=
  congrArg (fun g => g z) (h.app U).map_d

/-- The degree-`n` coordinate of `h_U` on a section of `M^n(U)`. -/
def homOfSectionSystemApp (n : ℤ) (U : Cᵒᵖ) : M.sectionsPiece U n →+ N.sectionsPiece U n :=
  (DFinsupp.evalAddMonoidHom n).comp ((sectionFun h U).comp (DirectSum.of (M.sectionsPiece U) n))

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- `homOfSectionSystemApp h n U x` is the degree-`n` coordinate of `h_U` applied to `x` placed in
the summand of degree `n`. -/
theorem homOfSectionSystemApp_apply (n : ℤ) (U : Cᵒᵖ) (x : M.sectionsPiece U n) :
    homOfSectionSystemApp h n U x = sectionFun h U (DirectSum.of (M.sectionsPiece U) n x) n :=
  rfl

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- `h_U` carries the summand of degree `n` to the summand of degree `n`. -/
theorem of_homOfSectionSystemApp (n : ℤ) (U : Cᵒᵖ) (x : M.sectionsPiece U n) :
    DirectSum.of (N.sectionsPiece U) n (homOfSectionSystemApp h n U x) =
      sectionFun h U (DirectSum.of (M.sectionsPiece U) n x) := by
  have hmem := (h.app U).map_grading n (DirectSum.of (M.sectionsPiece U) n x)
    (Stacks.ExternalGrading.of_mem_intSummand _ n x)
  exact Stacks.ExternalGrading.of_coord_eq (N.sectionsPiece U)
    (⟨_, hmem⟩ : Stacks.ExternalGrading.intSummand (N.sectionsPiece U) n)

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- `homOfSectionSystemApp h n` commutes with restriction of sections. -/
theorem homOfSectionSystemApp_naturality (n : ℤ) {U V : Cᵒᵖ} (a : V ⟶ U)
    (x : M.sectionsPiece V n) :
    N.sectionRestrictApp a n (homOfSectionSystemApp h n V x) =
      homOfSectionSystemApp h n U (M.sectionRestrictApp a n x) := by
  apply DirectSum.of_injective (β := N.sectionsPiece U) n
  rw [← sectionRestrictAdd_of N a n, of_homOfSectionSystemApp, of_homOfSectionSystemApp,
    ← sectionRestrictAdd_of M a n]
  exact sectionFun_naturality h a _

/-- `homOfSectionSystemApp h n U` is linear over the ring of sections over `U`. -/
theorem homOfSectionSystemApp_smul (n : ℤ) (U : Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U) (x : M.sectionsPiece U n) :
    homOfSectionSystemApp h n U (r • x) = r • homOfSectionSystemApp h n U x := by
  apply DirectSum.of_injective (β := N.sectionsPiece U) n
  rw [of_homOfSectionSystemApp, ← act_of_sectionScalar, ← act_of_sectionScalar,
    of_homOfSectionSystemApp]
  exact sectionFun_act h U _ _

/-- The degree-`n` component of the morphism determined by `h`, as a morphism of sheaves. -/
def homOfSectionSystemF (n : ℤ) : M.complex.X n ⟶ N.complex.X n :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (homOfSectionSystemApp h n U)
      naturality := fun V U a => by
        ext x
        exact (homOfSectionSystemApp_naturality h n a x).symm }
    (fun U r x => homOfSectionSystemApp_smul h n U r x)⟩

/-- The component over `U` of `homOfSectionSystemF h n` is `homOfSectionSystemApp h n U`. -/
theorem homOfSectionSystemF_app (n : ℤ) (U : Cᵒᵖ) (x : M.sectionsPiece U n) :
    (homOfSectionSystemF h n).val.app U x = homOfSectionSystemApp h n U x := rfl

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- `homOfSectionSystemApp h` commutes with the differentials of `M` and `N`. -/
theorem homOfSectionSystemApp_d (n : ℤ) (U : Cᵒᵖ) (x : M.sectionsPiece U n) :
    homOfSectionSystemApp h (n + 1) U ((M.complex.d n (n + 1)).val.app U x) =
      (N.complex.d n (n + 1)).val.app U (homOfSectionSystemApp h n U x) := by
  apply DirectSum.of_injective (β := N.sectionsPiece U) (n + 1)
  have h₁ := sectionD_of N U n (homOfSectionSystemApp h n U x)
  have h₂ := sectionD_of M U n x
  rw [sectionDApp_apply] at h₁ h₂
  rw [← h₁, of_homOfSectionSystemApp, of_homOfSectionSystemApp, ← h₂]
  exact sectionFun_sectionD h U _

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- `homOfSectionSystemApp h` commutes with the right multiplication by sections of `A`. -/
theorem homOfSectionSystemApp_mul (n i : ℤ) (U : Cᵒᵖ) (x : M.sectionsPiece U n)
    (y : (A.complex.X i).val.obj U) :
    homOfSectionSystemApp h (n + i) U ((M.mul n i).app U x y) =
      (N.mul n i).app U (homOfSectionSystemApp h n U x) y := by
  apply DirectSum.of_injective (β := N.sectionsPiece U) (n + i)
  have h₁ := actOn_of N U n i (homOfSectionSystemApp h n U x) y
  have h₂ := actOn_of M U n i x y
  rw [← act_of] at h₁ h₂
  rw [← h₁, of_homOfSectionSystemApp, of_homOfSectionSystemApp, ← h₂]
  exact sectionFun_act h U _ _

/-- **The morphism of right differential graded modules determined by a morphism of their
presheaves of section modules.** -/
def homOfSectionSystem : M ⟶ N where
  toHomologicalComplex :=
    { f := homOfSectionSystemF h
      comm' := by
        rintro i j (rfl : i + 1 = j)
        ext U x
        exact (homOfSectionSystemApp_d h i U x).symm }
  map_mul n i U x y := homOfSectionSystemApp_mul h n i U x y

/-- The `n`-th component of `homOfSectionSystem h` over `U` is `homOfSectionSystemApp h n U`. -/
@[simp] theorem homOfSectionSystem_f_app (n : ℤ) (U : Cᵒᵖ) (x : M.sectionsPiece U n) :
    ((homOfSectionSystem h).toHomologicalComplex.f n).val.app U x =
      homOfSectionSystemApp h n U x := rfl

/-- **The sections of the morphism determined by `h` are `h`.** -/
theorem sectionMap_homOfSectionSystem (U : Cᵒᵖ) :
    sectionMap (homOfSectionSystem h) U = h.app U := by
  refine _root_.DifferentialGradedModule.Hom.ext (LinearMap.ext fun z => ?_)
  show sectionMapAdd (homOfSectionSystem h) U z = sectionFun h U z
  induction z using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  | of n x =>
      rw [sectionMapAdd_of]
      exact of_homOfSectionSystemApp h n U x

end HomOfSectionSystem

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- A morphism of right differential graded modules is determined by its sections. -/
theorem hom_ext_of_sectionMap {M N : DifferentialGradedModule.{t, m, m} A} {f g : M ⟶ N}
    (h : ∀ U, sectionMap f U = sectionMap g U) : f = g := by
  refine Hom.ext fun n => SheafOfModules.hom_ext ?_
  ext U x
  apply DirectSum.of_injective (β := N.sectionsPiece U) n
  have := congrArg (fun φ => φ.toFun (DirectSum.of (M.sectionsPiece U) n x)) (h U)
  simp only [sectionMap_toFun, sectionMapAdd_of, sectionMapApp_apply] at this
  exact this

variable (A) in
/-- **`Σ` is fully faithful.** -/
def sectionSystemFullyFaithful : (sectionSystemFunctor A).FullyFaithful where
  preimage h := homOfSectionSystem h
  map_preimage h := SectionSystem.hom_ext fun U => sectionMap_homOfSectionSystem h U
  preimage_map _f := hom_ext_of_sectionMap fun U => sectionMap_homOfSectionSystem _ U

/-- The functor `N ↦ Σ N` is full. -/
instance : (sectionSystemFunctor A).Full := (sectionSystemFullyFaithful A).full

/-- The functor `N ↦ Σ N` is faithful. -/
instance : (sectionSystemFunctor A).Faithful := (sectionSystemFullyFaithful A).faithful

/-! ### The sections of a realization -/

namespace SectionSystem

/-- **The presheaf of section modules of the realization of `X` is `X`.** -/
def realizeSectionsIso (X : SectionSystem A) : sectionSystem A X.realize ≅ X where
  hom := ⟨fun U => (X.sectionsIso U).hom, fun a x =>
    (congrArg (fun g => g.toFun x) (X.sectionModuleRestriction_sectionsIso a)).symm⟩
  inv := ⟨fun U => (X.sectionsIso U).inv, fun {U V} a x => by
    have hl : ∀ y, (X.sectionsIso U).inv.toFun ((X.sectionsIso U).hom.toFun y) = y :=
      fun y => congrArg (fun g => g.toFun y) (X.sectionsIso U).hom_inv_id
    have hr : ∀ y, (X.sectionsIso V).hom.toFun ((X.sectionsIso V).inv.toFun y) = y :=
      fun y => congrArg (fun g => g.toFun y) (X.sectionsIso V).inv_hom_id
    have hn := congrArg (fun g => g.toFun ((X.sectionsIso V).inv.toFun x))
      (X.sectionModuleRestriction_sectionsIso a)
    change (X.sectionsIso U).hom.toFun (X.realize.sectionRestrictAdd a _) =
      X.restrFun a ((X.sectionsIso V).hom.toFun _) at hn
    rw [hr] at hn
    change X.realize.sectionRestrictAdd a ((X.sectionsIso V).inv.toFun x) = _
    rw [← hn]
    exact (hl _).symm⟩
  hom_inv_id := SectionSystem.hom_ext fun U => (X.sectionsIso U).hom_inv_id
  inv_hom_id := SectionSystem.hom_ext fun U => (X.sectionsIso U).inv_hom_id

/-- The component over `U` of `realizeSectionsIso X` is `X.sectionsIso U`. -/
@[simp] theorem realizeSectionsIso_hom_app (X : SectionSystem A) (U : Cᵒᵖ) :
    (realizeSectionsIso X).hom.app U = (X.sectionsIso U).hom := rfl

/-- The component over `U` of the inverse of `realizeSectionsIso X` is the inverse of
`X.sectionsIso U`. -/
@[simp] theorem realizeSectionsIso_inv_app (X : SectionSystem A) (U : Cᵒᵖ) :
    (realizeSectionsIso X).inv.app U = (X.sectionsIso U).inv := rfl

variable (A) in
/-- The identification of the sections of a realization, natural in the presheaf of section
modules. -/
def realizeSectionsNatIso : realizeFunctor A ⋙ sectionSystemFunctor A ≅ 𝟭 (SectionSystem A) :=
  NatIso.ofComponents realizeSectionsIso fun f =>
    SectionSystem.hom_ext fun U => by
      rw [SectionSystem.comp_app, SectionSystem.comp_app]
      exact sectionsIso_naturality f U

end SectionSystem

/-- **Every right differential graded module is the realization of its presheaf of section
modules.** -/
def realizeSectionSystemIso (N : DifferentialGradedModule.{t, m, m} A) :
    N ≅ (sectionSystem A N).realize :=
  (sectionSystemFullyFaithful A).preimageIso
    (SectionSystem.realizeSectionsIso (sectionSystem A N)).symm

/-- The image under `N ↦ Σ N` of `realizeSectionSystemIso N` is the inverse of
`realizeSectionsIso (sectionSystem A N)`. -/
theorem sectionSystemFunctor_map_realizeSectionSystemIso_hom
    (N : DifferentialGradedModule.{t, m, m} A) :
    (sectionSystemFunctor A).map (realizeSectionSystemIso N).hom =
      (SectionSystem.realizeSectionsIso (sectionSystem A N)).inv :=
  (sectionSystemFullyFaithful A).map_preimage _

variable (A) in
/-- **The equivalence between right differential graded `A`-modules and presheaves of section
modules** on a chaotic site: `N ↦ Σ N`, with quasi-inverse the realization. -/
def sectionSystemEquivalence : DifferentialGradedModule.{t, m, m} A ≌ SectionSystem A :=
  CategoryTheory.Equivalence.mk (sectionSystemFunctor A) (SectionSystem.realizeFunctor A)
    (NatIso.ofComponents realizeSectionSystemIso
      (fun {M N} f => (sectionSystemFullyFaithful A).map_injective (by
        have h := (SectionSystem.realizeSectionsNatIso A).inv.naturality
          ((sectionSystemFunctor A).map f)
        dsimp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at h ⊢
        rw [Functor.map_comp, Functor.map_comp]
        simp only [SectionSystem.realizeFunctor_obj, sectionSystemFunctor_obj,
          sectionSystemFunctor_map_realizeSectionSystemIso_hom,
          SectionSystem.realizeSectionsNatIso] at h ⊢
        exact h)))
    (SectionSystem.realizeSectionsNatIso A)

namespace SectionSystem

variable (A) in
/-- **The realization is left adjoint to `N ↦ Σ N`.** -/
def realizeAdjunction : realizeFunctor A ⊣ sectionSystemFunctor A :=
  (sectionSystemEquivalence A).symm.toAdjunction

/-- The hom-set bijection of `realizeAdjunction`: a morphism out of a realization is sent to its
sections, read through the identification of the sections of the realization. -/
theorem realizeAdjunction_homEquiv_apply {X : SectionSystem A}
    {N : DifferentialGradedModule.{t, m, m} A} (g : X.realize ⟶ N) :
    (realizeAdjunction A).homEquiv X N g =
      (realizeSectionsIso X).inv ≫ (sectionSystemFunctor A).map g := by
  simp [realizeAdjunction, sectionSystemEquivalence, Equivalence.toAdjunction]
  rfl

end SectionSystem

end DifferentialGradedModule

end SheafOfModules

end
