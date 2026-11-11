module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Grp.Limits

/-!
# Kernels and finite powers of abelian sheaves, read on sections

For a morphism `φ : A ⟶ A'` of abelian sheaves on a site, the presheaf of sectionwise kernels
`T ↦ ker (A(T) → A'(T))` is a sheaf and is a kernel of `φ`; consequently any kernel of `φ`
(given as a limit kernel fork) maps its sections bijectively onto the sectionwise kernels.
Dually, a fan `π : P ⟶ F` indexed by `Fin n` is a limit as soon as it induces bijections
`P(T) → F(T)ⁿ` on sections.

These are the forms in which kernels and powers are handled by hand on the big fppf sites, where
elaborating the chosen `kernel` of a morphism of sheaves is slow.

## Main definitions

* `CategoryTheory.Sheaf.sectionwiseKernel`: the sheaf of sectionwise kernels of `φ`.
* `CategoryTheory.Sheaf.isLimitSectionwiseKernel`: it is a kernel of `φ`.
* `CategoryTheory.Sheaf.isLimitFanOfBijective`: a fan that is bijective on sections is a limit.

## Main results

* `CategoryTheory.Sheaf.bijective_codRestrict_of_isLimit`: a limit kernel fork of `φ` is bijective
  on sections onto the sectionwise kernels.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Kernel

variable {A A' : Sheaf J AddCommGrpCat.{v}} (φ : A ⟶ A')

/-- Restriction maps preserve the sectionwise kernels of a morphism of abelian sheaves. -/
theorem map_mem_ker_hom_app {T T' : Cᵒᵖ} (f : T ⟶ T') {x : A.obj.obj T}
    (hx : x ∈ (φ.hom.app T).hom.ker) :
    (A.obj.map f).hom x ∈ (φ.hom.app T').hom.ker := by
  have h := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (φ.hom.naturality f)) x
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h
  rw [AddMonoidHom.mem_ker, h, AddMonoidHom.mem_ker.1 hx, map_zero]

/-- The presheaf of sectionwise kernels of a morphism of abelian sheaves. -/
def sectionwiseKernelPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj T := AddCommGrpCat.of (φ.hom.app T).hom.ker
  map {T T'} f := AddCommGrpCat.ofHom
    (((A.obj.map f).hom.comp (φ.hom.app T).hom.ker.subtype).codRestrict _
      (fun x => map_mem_ker_hom_app φ f x.2))
  map_id T := by
    ext x
    exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (A.obj.map_id T)) x.1
  map_comp f g := by
    ext x
    exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (A.obj.map_comp f g)) x.1

/-- The inclusion of the sectionwise kernels. -/
def sectionwiseKernelPresheafι : sectionwiseKernelPresheaf φ ⟶ A.obj where
  app T := AddCommGrpCat.ofHom (φ.hom.app T).hom.ker.subtype
  naturality T T' f := by ext x; rfl

/-- The inclusion of the sectionwise kernels is killed by `φ`. -/
theorem sectionwiseKernelPresheafι_comp :
    sectionwiseKernelPresheafι φ ≫ φ.hom = 0 := by
  ext T x
  exact AddMonoidHom.mem_ker.1 x.2

/-- The sectionwise kernel is a kernel of presheaves. -/
def isLimitSectionwiseKernelPresheaf :
    IsLimit (KernelFork.ofι (sectionwiseKernelPresheafι φ)
      (sectionwiseKernelPresheafι_comp φ)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {W} s hs => {
      app := fun T => AddCommGrpCat.ofHom ((s.app T).hom.codRestrict _ (fun y => by
        have := DFunLike.congr_fun
          (congrArg AddCommGrpCat.Hom.hom (congrArg (fun g => g.app T) hs)) y
        simpa using this))
      naturality := fun T T' f => by
        ext y
        apply Subtype.ext
        exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (s.naturality f)) y })
    (fun s hs => by ext T y; rfl)
    (fun s hs m hm => by
      ext T y
      apply Subtype.ext
      exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (congrArg (fun g => g.app T) hm)) y)


/-- The sectionwise kernel presheaf, as a cone over the parallel pair of sheaves read in
presheaves. -/
def sectionwiseKernelCone :
    Cone (parallelPair φ 0 ⋙ sheafToPresheaf J AddCommGrpCat.{v}) :=
  (Cone.postcompose (diagramIsoParallelPair _).inv).obj
    (Fork.ofι (sectionwiseKernelPresheafι φ) (by
      change sectionwiseKernelPresheafι φ ≫ φ.hom = sectionwiseKernelPresheafι φ ≫ (0 : A ⟶ A').hom
      rw [sectionwiseKernelPresheafι_comp]
      rfl))

/-- The presheaf of sectionwise kernels of a morphism of abelian sheaves is a sheaf. -/
theorem isSheaf_sectionwiseKernelPresheaf :
    Presheaf.IsSheaf J (sectionwiseKernelPresheaf φ) :=
  Sheaf.isSheaf_of_isLimit (parallelPair φ 0) (sectionwiseKernelCone φ)
    ((IsLimit.postcomposeInvEquiv _ _).symm
      (Fork.IsLimit.mk _
        (fun s => (isLimitSectionwiseKernelPresheaf φ).lift (KernelFork.ofι s.ι (by
          have := s.condition
          change s.ι ≫ φ.hom = s.ι ≫ (0 : A ⟶ A').hom at this
          rw [this]
          rfl)))
        (fun s => (isLimitSectionwiseKernelPresheaf φ).fac _ WalkingParallelPair.zero)
        (fun s m hm => Fork.IsLimit.hom_ext (isLimitSectionwiseKernelPresheaf φ)
          (hm.trans ((isLimitSectionwiseKernelPresheaf φ).fac _ WalkingParallelPair.zero).symm))))

/-- The sheaf of sectionwise kernels of a morphism of abelian sheaves. -/
def sectionwiseKernel : Sheaf J AddCommGrpCat.{v} :=
  ⟨sectionwiseKernelPresheaf φ, isSheaf_sectionwiseKernelPresheaf φ⟩

/-- The inclusion of the sheaf of sectionwise kernels. -/
def sectionwiseKernelι : sectionwiseKernel φ ⟶ A :=
  ⟨sectionwiseKernelPresheafι φ⟩

/-- The inclusion of the sheaf of sectionwise kernels is killed by `φ`. -/
theorem sectionwiseKernelι_comp : sectionwiseKernelι φ ≫ φ = 0 := by
  ext T x
  exact AddMonoidHom.mem_ker.1 x.2

/-- The sheaf of sectionwise kernels is a kernel. -/
def isLimitSectionwiseKernel :
    IsLimit (KernelFork.ofι (sectionwiseKernelι φ) (sectionwiseKernelι_comp φ)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {W} s hs => ⟨(isLimitSectionwiseKernelPresheaf φ).lift (KernelFork.ofι s.hom (by
        exact congrArg (fun g => g.hom) hs))⟩)
    (fun s hs => by
      ext1
      exact (isLimitSectionwiseKernelPresheaf φ).fac _ WalkingParallelPair.zero)
    (fun s hs m hm => by
      ext1
      refine Fork.IsLimit.hom_ext (isLimitSectionwiseKernelPresheaf φ) ?_
      exact (congrArg (fun g => g.hom) hm).trans
        ((isLimitSectionwiseKernelPresheaf φ).fac (KernelFork.ofι s.hom (by
          exact congrArg (fun g => g.hom) hs)) WalkingParallelPair.zero).symm)

/-- For a kernel fork `ι` of `φ` which is a limit, `ι` induces bijections from sections onto the
kernels of `φ` on sections. -/
theorem bijective_codRestrict_of_isLimit {K : Sheaf J AddCommGrpCat.{v}} (ι : K ⟶ A)
    (w : ι ≫ φ = 0) (hK : IsLimit (KernelFork.ofι ι w)) (T : Cᵒᵖ) :
    Function.Bijective ((ι.hom.app T).hom.codRestrict (φ.hom.app T).hom.ker (fun x => by
      rw [AddMonoidHom.mem_ker]
      exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
        (congrArg (fun g => g.hom.app T) w)) x)) := by
  let e := hK.conePointUniqueUpToIso (isLimitSectionwiseKernel φ)
  have he : e.hom ≫ sectionwiseKernelι φ = ι :=
    hK.conePointUniqueUpToIso_hom_comp (isLimitSectionwiseKernel φ) WalkingParallelPair.zero
  have hb : Function.Bijective (e.hom.hom.app T).hom :=
    ((forget AddCommGrpCat).mapIso ((sheafToPresheaf J _ ⋙ (evaluation _ _).obj T).mapIso e)
      ).toEquiv.bijective
  have hfun : ⇑((ι.hom.app T).hom.codRestrict (φ.hom.app T).hom.ker (fun x => by
      rw [AddMonoidHom.mem_ker]
      exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
        (congrArg (fun g => g.hom.app T) w)) x)) = ⇑(e.hom.hom.app T).hom := by
    funext x
    apply Subtype.ext
    exact (DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
      (congrArg (fun g => g.hom.app T) he)) x).symm
  exact hfun ▸ hb

end Kernel


section Fan

/-- The map from sections of `P` to families of sections of `F`, given by a family of morphisms. -/
def piSectionsHom {n : ℕ} {P F : Sheaf J AddCommGrpCat.{v}} (π : Fin n → (P ⟶ F))
    (T : Cᵒᵖ) : P.obj.obj T →+ (Fin n → F.obj.obj T) :=
  AddMonoidHom.pi fun k => ((π k).hom.app T).hom

/-- `piSectionsHom` evaluated at an index. -/
theorem piSectionsHom_apply {n : ℕ} {P F : Sheaf J AddCommGrpCat.{v}} (π : Fin n → (P ⟶ F))
    (T : Cᵒᵖ) (x : P.obj.obj T) (k : Fin n) :
    piSectionsHom π T x k = ((π k).hom.app T).hom x :=
  rfl

/-- `piSectionsHom` commutes with restriction. -/
theorem piSectionsHom_naturality {n : ℕ} {P F : Sheaf J AddCommGrpCat.{v}}
    (π : Fin n → (P ⟶ F)) {T T' : Cᵒᵖ} (f : T ⟶ T') (x : P.obj.obj T) :
    piSectionsHom π T' ((P.obj.map f).hom x) =
      fun k => (F.obj.map f).hom (piSectionsHom π T x k) := by
  funext k
  exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom ((π k).hom.naturality f)) x

/-- A fan of abelian sheaves is a limit as soon as it induces bijections on sections. -/
def isLimitFanOfBijective {n : ℕ} {P F : Sheaf J AddCommGrpCat.{v}}
    (π : Fin n → (P ⟶ F)) (h : ∀ T, Function.Bijective (piSectionsHom π T)) :
    IsLimit (Fan.mk P π) :=
  let e : ∀ T, P.obj.obj T ≃+ (Fin n → F.obj.obj T) := fun T =>
    AddEquiv.ofBijective (piSectionsHom π T) (h T)
  have he : ∀ T y, piSectionsHom π T ((e T).symm y) = y := fun T y =>
    AddEquiv.ofBijective_apply_symm_apply (piSectionsHom π T) (h T)
  Fan.IsLimit.mk _
    (fun s => ⟨{
      app := fun T => AddCommGrpCat.ofHom
        ((e T).symm.toAddMonoidHom.comp (piSectionsHom (fun k => s.proj k) T))
      naturality := fun T T' f => by
        ext x
        apply (h T').1
        change piSectionsHom π T' ((e T').symm (piSectionsHom (fun k => s.proj k) T'
            ((s.pt.obj.map f).hom x))) =
          piSectionsHom π T'
            ((P.obj.map f).hom ((e T).symm (piSectionsHom (fun k => s.proj k) T x)))
        rw [he, piSectionsHom_naturality, piSectionsHom_naturality, he] }⟩)
    (fun s k => by
      ext T x
      exact congrFun (he T (piSectionsHom (fun k => s.proj k) T x)) k)
    (fun s m hm => by
      ext T x
      apply (h T).1
      change piSectionsHom π T ((m.hom.app T).hom x) =
        piSectionsHom π T ((e T).symm (piSectionsHom (fun k => s.proj k) T x))
      rw [he]
      funext k
      exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
        (congrArg (fun g => g.hom.app T) (hm k))) x)


end Fan
end CategoryTheory.Sheaf
