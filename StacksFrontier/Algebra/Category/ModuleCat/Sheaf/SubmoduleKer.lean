module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleFactorThru

/-!
# The kernel of a morphism of (pre)sheaves of modules as a submodule

Let `f : M ⟶ N` be a morphism of (pre)sheaves of modules. The sections of `M` over an object
annihilated by `f` form a submodule, and these submodules are stable under restriction, so they
assemble into a `Submodule M`. For sheaves of modules the membership condition is local, so the
same family is a `SheafOfModules.Submodule M`, and the associated sheaf of modules together with
its inclusion is a kernel of `f`.

## Main definitions

* `PresheafOfModules.Submodule.ker` and `SheafOfModules.Submodule.ker`: the kernel of `f`, as a
  submodule of the source.
* `SheafOfModules.Submodule.isLimitKernelFork`: the inclusion of `ker f` into `M` is a kernel
  of `f`.
* `SheafOfModules.Submodule.kerIsoKernel`: the isomorphism between the sheaf of modules
  associated to `ker f` and the categorical kernel of `f`.

## Main results

* `PresheafOfModules.Submodule.mem_ker` and `SheafOfModules.Submodule.mem_ker`: a section lies
  in `ker f` exactly when `f` annihilates it.
* `SheafOfModules.Submodule.ker_ι_comp`: the inclusion of `ker f` composed with `f` is zero.
* `SheafOfModules.Submodule.kerIsoKernel_hom_comp_ι` and
  `SheafOfModules.Submodule.kerIsoKernel_inv_comp_ι`: the isomorphism with the categorical
  kernel is compatible with the two inclusions into `M`.

## Implementation notes

Locality of the membership condition is separatedness of `N`: a section of `M` whose image under
`f` restricts to zero on the members of a covering sieve has image zero, because the image and
the zero section of `N` then agree locally. This is `Presheaf.IsSheaf.isSeparated` applied to the
underlying sheaf of abelian groups of `N`.

That the inclusion is a kernel uses no computation beyond
`SheafOfModules.Submodule.factorThru`: a morphism `k` with `k ≫ f = 0` has all its values in
`ker f`, hence factors through it, and the factorization is unique because the inclusion of a
submodule is a monomorphism.

## References

* [Stacks Project, Tag 01AP](https://stacks.math.columbia.edu/tag/01AP)
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory CategoryTheory.Limits Opposite

namespace PresheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- The kernel of a morphism `f : M ⟶ N` of presheaves of modules, as a submodule of `M`: over
an object it is the kernel of the component of `f` there. -/
noncomputable def ker {M N : PresheafOfModules.{v} R} (f : M ⟶ N) : M.Submodule where
  obj X := LinearMap.ker (Hom.app f X).hom
  map {X Y} g x hx := by
    refine _root_.Submodule.mem_comap.mpr (LinearMap.mem_ker.mpr ?_)
    change Hom.app f Y (M.map g x) = 0
    rw [naturality_apply f g x, LinearMap.mem_ker.mp hx]
    exact map_zero _

/-- A section of `M` lies in `ker f` exactly when `f` annihilates it. -/
lemma mem_ker {M N : PresheafOfModules.{v} R} (f : M ⟶ N) (X : Cᵒᵖ) (x : M.obj X) :
    x ∈ (ker f).obj X ↔ Hom.app f X x = 0 := Iff.rfl

end PresheafOfModules.Submodule

namespace SheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- The kernel of a morphism `f : M ⟶ N` of sheaves of modules, as a submodule of `M`.

Membership is local because `N` is separated: a section whose image is locally zero has image
zero. -/
noncomputable def ker {M N : SheafOfModules.{v} R} (f : M ⟶ N) : M.Submodule where
  toSubmodule := PresheafOfModules.Submodule.ker f.val
  isSheaf {X} s hs := by
    refine N.isSheaf.isSeparated X.unop _ hs (PresheafOfModules.Hom.app f.val X s) 0
      fun Y g hg ↦ ?_
    rw [map_zero]
    change N.val.map g.op (PresheafOfModules.Hom.app f.val X s) = 0
    rw [← PresheafOfModules.naturality_apply f.val g.op s]
    exact hg

/-- The underlying submodule of the underlying presheaf of modules of `ker f` is the kernel of
the underlying morphism of presheaves of modules. -/
@[simp]
lemma toSubmodule_ker {M N : SheafOfModules.{v} R} (f : M ⟶ N) :
    (ker f).toSubmodule = PresheafOfModules.Submodule.ker f.val := rfl

/-- A section of `M` lies in `ker f` exactly when `f` annihilates it. -/
lemma mem_ker {M N : SheafOfModules.{v} R} (f : M ⟶ N) (X : Cᵒᵖ) (x : M.val.obj X) :
    x ∈ (ker f).obj X ↔ PresheafOfModules.Hom.app f.val X x = 0 := Iff.rfl

/-- The inclusion of `ker f` into `M`, composed with `f`, is zero. -/
@[reassoc (attr := simp)]
lemma ker_ι_comp {M N : SheafOfModules.{v} R} (f : M ⟶ N) : (ker f).ι ≫ f = 0 := by
  ext X x
  exact x.2

/-- The inclusion of `ker f` into `M` is a kernel of `f`: a morphism annihilated by `f` has all
its values in `ker f`, hence factors through it, uniquely because the inclusion is a
monomorphism. -/
noncomputable def isLimitKernelFork {M N : SheafOfModules.{v} R} (f : M ⟶ N) :
    IsLimit (KernelFork.ofι (ker f).ι (ker_ι_comp f)) :=
  KernelFork.IsLimit.ofι' _ _ fun {P} k hk ↦
    ⟨(ker f).factorThru k fun X x ↦ (mem_ker f X _).2
      (by rw [show PresheafOfModules.Hom.app f.val X (PresheafOfModules.Hom.app k.val X x)
          = PresheafOfModules.Hom.app (k ≫ f).val X x from rfl, hk]; rfl),
      (ker f).factorThru_ι k _⟩

/-- The sheaf of modules associated to `ker f` is the categorical kernel of `f`. -/
noncomputable def kerIsoKernel {M N : SheafOfModules.{v} R} (f : M ⟶ N) [HasKernel f] :
    (ker f).toSheafOfModules ≅ kernel f :=
  IsLimit.conePointUniqueUpToIso (isLimitKernelFork f) (limit.isLimit (parallelPair f 0))

/-- The isomorphism of `ker f` with the categorical kernel of `f` carries the inclusion of the
kernel to the inclusion of `ker f`. -/
@[reassoc (attr := simp)]
lemma kerIsoKernel_hom_comp_ι {M N : SheafOfModules.{v} R} (f : M ⟶ N) [HasKernel f] :
    (kerIsoKernel f).hom ≫ kernel.ι f = (ker f).ι :=
  IsLimit.conePointUniqueUpToIso_hom_comp (isLimitKernelFork f)
    (limit.isLimit (parallelPair f 0)) WalkingParallelPair.zero

/-- The isomorphism of `ker f` with the categorical kernel of `f` carries the inclusion of
`ker f` to the inclusion of the kernel. -/
@[reassoc (attr := simp)]
lemma kerIsoKernel_inv_comp_ι {M N : SheafOfModules.{v} R} (f : M ⟶ N) [HasKernel f] :
    (kerIsoKernel f).inv ≫ (ker f).ι = kernel.ι f :=
  IsLimit.conePointUniqueUpToIso_inv_comp (isLimitKernelFork f)
    (limit.isLimit (parallelPair f 0)) WalkingParallelPair.zero

end SheafOfModules.Submodule

end
