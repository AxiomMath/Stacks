module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidColimits
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.OverPullback
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic

/-!
# Quasi-coherent modules on a flat groupoid scheme form an abelian category

Let `S` be a scheme and let `G` be a groupoid scheme over `S`, with object scheme `U` and
arrow scheme `R`, source `s` and target `t`.  A quasi-coherent module on `G` is a
quasi-coherent module `F` on `U` together with a descent morphism `α : t^* F ⟶ s^* F`
satisfying the cocycle and identity conditions.
These form a preadditive category for the addition of the underlying morphisms of modules, and
when `s` and `t` are flat the category is abelian.

Everything is computed on the underlying modules on `U`.  Both pullback functors are right
exact, being left adjoints, and flatness of `s` and `t` makes them left exact as well; so the
two pullbacks of a kernel are the kernels of the two pullbacks, the descent morphisms of the
source and target of a morphism induce a descent morphism on its kernel, and likewise for its
cokernel.  The resulting kernel and cokernel in the category of quasi-coherent modules on `G`
are preserved by the forgetful functor to modules on `U`, which also reflects isomorphisms;
since the coimage-image comparison is an isomorphism on `U`, it is one on `G`.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.QuasicoherentModule.compatibleHoms` is the subgroup of
  morphisms of the underlying modules which intertwine two descent morphisms, and
  `Stacks.Groupoids.GroupoidScheme.QuasicoherentModule.homEquiv` identifies it with the type of
  morphisms of quasi-coherent modules on a groupoid scheme.
* `Stacks.Groupoids.GroupoidScheme.QuasicoherentModule.kernelDescent` and
  `Stacks.Groupoids.GroupoidScheme.QuasicoherentModule.cokernelDescent` are the descent
  morphisms induced on the kernel and the cokernel of a morphism, and
  `Stacks.Groupoids.GroupoidScheme.QuasicoherentModule.kernelObj` and
  `Stacks.Groupoids.GroupoidScheme.QuasicoherentModule.cokernelObj` are the resulting
  quasi-coherent modules on the groupoid scheme.

## Main results

* `Stacks.Groupoids.GroupoidScheme.QuasicoherentModule.instPreadditive`: quasi-coherent modules
  on a groupoid scheme form a preadditive category.
* `Stacks.Groupoids.GroupoidScheme.QuasicoherentModule.isLimitKernelFork` and
  `Stacks.Groupoids.GroupoidScheme.QuasicoherentModule.isColimitCokernelCofork`: the kernel and
  the cokernel computed on the underlying modules are a kernel and a cokernel of quasi-coherent
  modules on the groupoid scheme.
* `Stacks.Groupoids.GroupoidScheme.QuasicoherentModule.abelian`: **Stacks 077S**, the category
  of quasi-coherent modules on a groupoid scheme with flat source and target is abelian.

## Implementation notes

Only the kernel needs flatness: the preadditive structure, the cokernel, the finite biproducts,
the exactness of the forgetful functor on cokernels and the fact that it reflects isomorphisms
hold for an arbitrary groupoid scheme, and are stated at that generality.

`AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat` is made a local instance, so
that left exactness of pullback along the source, the target and the composition morphism is
found by typeclass inference and the same instance term is used in every declaration below;
a descent morphism defined with one instance term and a lemma about it proved with another
would not match.  Right exactness needs no such help: pullback of modules is a left adjoint,
so it preserves all colimits by an instance already available.

## References

* [Stacks Project, Tag 077S](https://stacks.math.columbia.edu/tag/077S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.Groupoids

universe u

attribute [local instance] AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- Composing two composable arrows and taking the source is taking the source of the second
arrow, so it is flat as soon as the source of the groupoid scheme is. -/
instance flat_comp_source [Flat G.source.left] : Flat (G.comp.left ≫ G.source.left) := by
  have h : G.comp.left ≫ G.source.left =
      (pullback.snd G.source G.target).left ≫ G.source.left := by
    rw [← Over.comp_left, ← Over.comp_left, G.source_comp]
  have : Flat (pullback.snd G.source G.target).left :=
    overFibreProduct_snd _ _ inferInstance
  rw [h]
  infer_instance

/-- Composing two composable arrows and taking the target is taking the target of the first
arrow, so it is flat as soon as the target of the groupoid scheme is. -/
instance flat_comp_target [Flat G.target.left] : Flat (G.comp.left ≫ G.target.left) := by
  have h : G.comp.left ≫ G.target.left =
      (pullback.fst G.source G.target).left ≫ G.target.left := by
    rw [← Over.comp_left, ← Over.comp_left, G.target_comp]
  have : Flat (pullback.fst G.source G.target).left :=
    overFibreProduct_fst _ _ inferInstance
  rw [h]
  infer_instance

namespace QuasicoherentModule

variable {G}

/-! ### The preadditive structure -/

/-- The morphisms of the underlying modules on the object scheme which intertwine the descent
morphisms of two quasi-coherent modules on a groupoid scheme.  They are closed under addition
and negation, so they form a subgroup of all morphisms of the underlying modules. -/
def compatibleHoms (M N : QuasicoherentModule G) : AddSubgroup (M.module ⟶ N.module) where
  carrier := {f | M.alpha ≫ (Scheme.Modules.pullback G.source.left).map f =
    (Scheme.Modules.pullback G.target.left).map f ≫ N.alpha}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change M.alpha ≫ (Scheme.Modules.pullback G.source.left).map (f + g) = _
    rw [Functor.map_add, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp, hf, hg]
  neg_mem' := by
    intro f hf
    change M.alpha ≫ (Scheme.Modules.pullback G.source.left).map (-f) = _
    rw [Functor.map_neg, Functor.map_neg, Preadditive.comp_neg, Preadditive.neg_comp, hf]

/-- A morphism of quasi-coherent modules on a groupoid scheme is the same datum as a morphism
of the underlying modules which intertwines the descent morphisms. -/
def homEquiv (M N : QuasicoherentModule G) : (M ⟶ N) ≃ compatibleHoms M N where
  toFun f := ⟨f.hom, f.comm⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

/-- Quasi-coherent modules on a groupoid scheme form a preadditive category, for the addition
of the underlying morphisms of modules on the object scheme. -/
noncomputable instance instPreadditive : Preadditive (QuasicoherentModule G) where
  homGroup M N := Equiv.addCommGroup (homEquiv M N)
  add_comp _ _ _ f g h := Hom.ext (Preadditive.add_comp _ _ _ f.hom g.hom h.hom)
  comp_add _ _ _ f g h := Hom.ext (Preadditive.comp_add _ _ _ f.hom g.hom h.hom)

namespace Hom

/-- The identity of a quasi-coherent module on a groupoid scheme is the identity of the
underlying module. -/
@[simp]
theorem hom_id (M : QuasicoherentModule G) : (𝟙 M : M ⟶ M).hom = 𝟙 M.module := rfl

/-- A composite of morphisms of quasi-coherent modules on a groupoid scheme is the composite of
the underlying morphisms of modules. -/
@[simp]
theorem hom_comp {M N P : QuasicoherentModule G} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- The zero morphism of quasi-coherent modules on a groupoid scheme is zero on underlying
modules. -/
@[simp]
theorem hom_zero (M N : QuasicoherentModule G) : (0 : M ⟶ N).hom = 0 := rfl

/-- A sum of morphisms of quasi-coherent modules on a groupoid scheme is the sum of the
underlying morphisms of modules. -/
@[simp]
theorem hom_add {M N : QuasicoherentModule G} (f g : M ⟶ N) :
    (f + g).hom = f.hom + g.hom := rfl

end Hom

/-- The forgetful functor to modules on the object scheme is additive. -/
instance : (forget G).Additive where
  map_add := rfl

/-- The condition defining a fork over a morphism of quasi-coherent modules and the zero
morphism, read on the underlying modules. -/
theorem fork_condition_hom {M N : QuasicoherentModule G} {f : M ⟶ N} (s : KernelFork f) :
    s.ι.hom ≫ f.hom = 0 := by
  simpa only [Hom.hom_comp, Hom.hom_zero] using congrArg Hom.hom (KernelFork.condition s)

/-- The condition defining a cofork over a morphism of quasi-coherent modules and the zero
morphism, read on the underlying modules. -/
theorem cofork_condition_hom {M N : QuasicoherentModule G} {f : M ⟶ N}
    (s : CokernelCofork f) : f.hom ≫ s.π.hom = 0 := by
  simpa only [Hom.hom_comp, Hom.hom_zero] using congrArg Hom.hom (CokernelCofork.condition s)

/-! ### Cokernels

Pullback of modules is a left adjoint, so it is right exact for any groupoid scheme and the
cokernel needs no flatness hypothesis. -/

/-- The descent morphism on the cokernel of a morphism of quasi-coherent modules on a groupoid
scheme: pullback along source and target is right exact, so the two pullbacks of the cokernel
are the cokernels of the two pullbacks, between which the descent morphisms of the source and
target of the morphism induce a map. -/
noncomputable def cokernelDescent {M N : QuasicoherentModule G} (f : M ⟶ N) :
    (Scheme.Modules.pullback G.target.left).obj (cokernel f.hom) ⟶
      (Scheme.Modules.pullback G.source.left).obj (cokernel f.hom) :=
  (PreservesCokernel.iso (Scheme.Modules.pullback G.target.left) f.hom).hom ≫
    cokernel.map _ _ M.alpha N.alpha f.comm.symm ≫
      (PreservesCokernel.iso (Scheme.Modules.pullback G.source.left) f.hom).inv

/-- The descent morphism on a cokernel is compatible with the projection onto the cokernel. -/
theorem cokernelDescent_π {M N : QuasicoherentModule G} (f : M ⟶ N) :
    (Scheme.Modules.pullback G.target.left).map (cokernel.π f.hom) ≫ cokernelDescent f =
      N.alpha ≫ (Scheme.Modules.pullback G.source.left).map (cokernel.π f.hom) := by
  have hU : cokernel.π ((Scheme.Modules.pullback G.source.left).map f.hom) ≫
      (PreservesCokernel.iso (Scheme.Modules.pullback G.source.left) f.hom).inv =
      (Scheme.Modules.pullback G.source.left).map (cokernel.π f.hom) := by
    rw [PreservesCokernel.iso_inv, π_comp_cokernelComparison]
  simp only [cokernelDescent, ← Category.assoc, PreservesCokernel.π_iso_hom, cokernel.map,
    cokernel.π_desc]
  rw [Category.assoc, hU]

/-- The cokernel of a morphism of quasi-coherent modules on a groupoid scheme, as a
quasi-coherent module with descent data. -/
noncomputable def cokernelObj {M N : QuasicoherentModule G} (f : M ⟶ N) :
    QuasicoherentModule G where
  module := cokernel f.hom
  isQuasicoherent := inferInstance
  alpha := cokernelDescent f
  cocycle := by
    have hs := AlgebraicGeometry.GroupoidScheme.successiveDescent_naturality G N.alpha
      (cokernelDescent f) (cokernel.π f.hom) (cokernelDescent_π f).symm
    have hr := reindexHom_naturality G.comp.left N.alpha (cokernelDescent f)
      (cokernel.π f.hom) (cokernelDescent_π f).symm
    rw [← cancel_epi ((Scheme.Modules.pullback (G.comp.left ≫ G.target.left)).map
      (cokernel.π f.hom)), ← hs, ← hr, N.cocycle]
  identity := by
    have h := AlgebraicGeometry.GroupoidScheme.identityDescent_naturality G N.alpha
      (cokernelDescent f) (cokernel.π f.hom) (cokernelDescent_π f).symm
    rw [N.identity, Category.id_comp] at h
    refine (cancel_epi (cokernel.π f.hom)).1 ?_
    rw [Category.comp_id]
    exact h.symm

/-- The projection of a morphism of quasi-coherent modules on a groupoid scheme onto its
cokernel. -/
noncomputable def cokernelπ {M N : QuasicoherentModule G} (f : M ⟶ N) : N ⟶ cokernelObj f :=
  ⟨cokernel.π f.hom, (cokernelDescent_π f).symm⟩

/-- The cofork exhibiting `cokernelObj f` as a cokernel of `f`. -/
noncomputable def cokernelCofork {M N : QuasicoherentModule G} (f : M ⟶ N) :
    CokernelCofork f :=
  CokernelCofork.ofπ (cokernelπ f) (Hom.ext (cokernel.condition f.hom))

/-- A morphism out of the cokernel of the underlying morphism intertwines the descent morphism
of the cokernel with the one of its target as soon as its composite with the projection onto
the cokernel does. -/
theorem cokernelDescent_comm {M N P : QuasicoherentModule G} {f : M ⟶ N}
    (g : cokernel f.hom ⟶ P.module)
    (hg : N.alpha ≫ (Scheme.Modules.pullback G.source.left).map (cokernel.π f.hom ≫ g) =
      (Scheme.Modules.pullback G.target.left).map (cokernel.π f.hom ≫ g) ≫ P.alpha) :
    cokernelDescent f ≫ (Scheme.Modules.pullback G.source.left).map g =
      (Scheme.Modules.pullback G.target.left).map g ≫ P.alpha := by
  rw [Functor.map_comp, Functor.map_comp, Category.assoc] at hg
  rw [← cancel_epi ((Scheme.Modules.pullback G.target.left).map (cokernel.π f.hom)),
    ← Category.assoc, cokernelDescent_π, Category.assoc]
  exact hg

/-- `cokernelCofork f` is a colimit cofork: a morphism out of `N` killing `f` factors uniquely
through the cokernel of the underlying morphism, and the factorization is compatible with the
descent morphisms. -/
noncomputable def isColimitCokernelCofork {M N : QuasicoherentModule G} (f : M ⟶ N) :
    IsColimit (cokernelCofork f) :=
  Cofork.IsColimit.mk _
    (fun s ↦ ⟨cokernel.desc f.hom s.π.hom (cofork_condition_hom s),
      cokernelDescent_comm _ (by rw [cokernel.π_desc]; exact s.π.comm)⟩)
    (fun s ↦ Hom.ext (cokernel.π_desc f.hom s.π.hom (cofork_condition_hom s)))
    (fun s m hm ↦ by
      apply Hom.ext
      refine (cancel_epi (cokernel.π f.hom)).1 ?_
      rw [cokernel.π_desc]
      exact congrArg Hom.hom hm)

/-- Quasi-coherent modules on a groupoid scheme have cokernels. -/
instance : HasCokernels (QuasicoherentModule G) where
  has_colimit f := ⟨cokernelCofork f, isColimitCokernelCofork f⟩

/-- The cokernel of a morphism of quasi-coherent modules on a groupoid scheme is the cokernel
of the underlying morphism of modules, carrying the induced descent morphism. -/
noncomputable def cokernelObjIsoCokernel {M N : QuasicoherentModule G} (f : M ⟶ N) :
    cokernel f ≅ cokernelObj f :=
  (cokernelIsCokernel f).coconePointUniqueUpToIso (isColimitCokernelCofork f)

/-- The identification of the two cokernels is compatible with their projections. -/
theorem π_cokernelObjIsoCokernel_inv {M N : QuasicoherentModule G} (f : M ⟶ N) :
    cokernelπ f ≫ (cokernelObjIsoCokernel f).inv = cokernel.π f := by
  simpa [cokernelObjIsoCokernel, cokernelCofork] using
    IsColimit.comp_coconePointUniqueUpToIso_inv (cokernelIsCokernel f)
      (isColimitCokernelCofork f) WalkingParallelPair.one

/-- The projection onto `cokernelObj f` is the projection onto the cokernel of the underlying
morphism. -/
theorem forget_map_cokernelπ {M N : QuasicoherentModule G} (f : M ⟶ N) :
    (forget G).map (cokernelπ f) = cokernel.π ((forget G).map f) := rfl

/-- The forgetful functor to modules on the object scheme preserves the cokernel of every
morphism, because the cokernel is computed there. -/
instance preservesCokernel_forget {M N : QuasicoherentModule G} (f : M ⟶ N) :
    PreservesColimit (parallelPair f 0) (forget G) := by
  have h : cokernelComparison f (forget G) =
      ((forget G).mapIso (cokernelObjIsoCokernel f)).inv := by
    refine (cancel_epi (cokernel.π ((forget G).map f))).1 ?_
    calc cokernel.π ((forget G).map f) ≫ cokernelComparison f (forget G)
        = (forget G).map (cokernel.π f) := π_comp_cokernelComparison f (forget G)
      _ = (forget G).map (cokernelπ f ≫ (cokernelObjIsoCokernel f).inv) := by
          rw [π_cokernelObjIsoCokernel_inv]
      _ = cokernel.π ((forget G).map f) ≫ ((forget G).mapIso (cokernelObjIsoCokernel f)).inv :=
          (forget G).map_comp _ _
  have : IsIso (cokernelComparison f (forget G)) := h ▸ Iso.isIso_inv _
  exact PreservesCokernel.of_iso_comparison (forget G) f

/-! ### Finite biproducts and the forgetful functor -/

/-- Quasi-coherent modules on a groupoid scheme have finite biproducts: they have all colimits,
hence finite coproducts, and the category is preadditive. -/
instance : HasFiniteBiproducts (QuasicoherentModule G) :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The forgetful functor to modules on the object scheme reflects isomorphisms: the inverse of
the underlying morphism automatically intertwines the descent morphisms. -/
instance : (forget G).ReflectsIsomorphisms where
  reflects {M N} f hf := by
    have hiso : IsIso ((forget G).map f) := hf
    have : IsIso f.hom := hiso
    refine ⟨⟨⟨inv f.hom, ?_⟩, ?_, ?_⟩⟩
    · rw [Functor.map_inv, Functor.map_inv, IsIso.comp_inv_eq, Category.assoc,
        IsIso.eq_inv_comp]
      exact f.comm.symm
    · apply Hom.ext
      simp
    · apply Hom.ext
      simp

/-! ### Kernels

Left exactness of pullback along the source and the target is where flatness enters. -/

section Flat

variable [Flat G.source.left] [Flat G.target.left]

/-- The descent morphism on the kernel of a morphism of quasi-coherent modules on a groupoid
scheme with flat source and target: pullback along source and target is left exact, so the two
pullbacks of the kernel are the kernels of the two pullbacks, between which the descent
morphisms of the source and target of the morphism induce a map. -/
noncomputable def kernelDescent {M N : QuasicoherentModule G} (f : M ⟶ N) :
    (Scheme.Modules.pullback G.target.left).obj (kernel f.hom) ⟶
      (Scheme.Modules.pullback G.source.left).obj (kernel f.hom) :=
  (PreservesKernel.iso (Scheme.Modules.pullback G.target.left) f.hom).hom ≫
    kernel.map _ _ M.alpha N.alpha f.comm.symm ≫
      (PreservesKernel.iso (Scheme.Modules.pullback G.source.left) f.hom).inv

/-- The descent morphism on a kernel is compatible with the inclusion of the kernel. -/
theorem kernelDescent_ι {M N : QuasicoherentModule G} (f : M ⟶ N) :
    kernelDescent f ≫ (Scheme.Modules.pullback G.source.left).map (kernel.ι f.hom) =
      (Scheme.Modules.pullback G.target.left).map (kernel.ι f.hom) ≫ M.alpha := by
  have hT : (PreservesKernel.iso (Scheme.Modules.pullback G.target.left) f.hom).hom ≫
      kernel.ι ((Scheme.Modules.pullback G.target.left).map f.hom) =
      (Scheme.Modules.pullback G.target.left).map (kernel.ι f.hom) := by
    rw [PreservesKernel.iso_hom, kernelComparison_comp_ι]
  simp only [kernelDescent, Category.assoc, PreservesKernel.iso_inv_ι, kernel.map,
    kernel.lift_ι]
  rw [← Category.assoc, hT]

/-- The kernel of a morphism of quasi-coherent modules on a groupoid scheme with flat source
and target, as a quasi-coherent module with descent data. -/
noncomputable def kernelObj {M N : QuasicoherentModule G} (f : M ⟶ N) :
    QuasicoherentModule G where
  module := kernel f.hom
  isQuasicoherent := inferInstance
  alpha := kernelDescent f
  cocycle := by
    have hs := AlgebraicGeometry.GroupoidScheme.successiveDescent_naturality G
      (kernelDescent f) M.alpha (kernel.ι f.hom) (kernelDescent_ι f)
    have hr := reindexHom_naturality G.comp.left (kernelDescent f) M.alpha
      (kernel.ι f.hom) (kernelDescent_ι f)
    rw [← cancel_mono ((Scheme.Modules.pullback (G.comp.left ≫ G.source.left)).map
      (kernel.ι f.hom)), hs, hr, M.cocycle]
  identity := by
    have h := AlgebraicGeometry.GroupoidScheme.identityDescent_naturality G
      (kernelDescent f) M.alpha (kernel.ι f.hom) (kernelDescent_ι f)
    rw [M.identity, Category.comp_id] at h
    refine (cancel_mono (kernel.ι f.hom)).1 ?_
    rw [Category.id_comp]
    exact h

/-- The inclusion of the kernel of a morphism of quasi-coherent modules on a groupoid scheme
with flat source and target. -/
noncomputable def kernelι {M N : QuasicoherentModule G} (f : M ⟶ N) : kernelObj f ⟶ M :=
  ⟨kernel.ι f.hom, kernelDescent_ι f⟩

/-- The fork exhibiting `kernelObj f` as a kernel of `f`. -/
noncomputable def kernelFork {M N : QuasicoherentModule G} (f : M ⟶ N) : KernelFork f :=
  KernelFork.ofι (kernelι f) (Hom.ext (kernel.condition f.hom))

/-- A morphism into the kernel of the underlying morphism intertwines the descent morphism of
its source with the one of the kernel as soon as its composite with the inclusion of the
kernel does. -/
theorem kernelDescent_comm {M N P : QuasicoherentModule G} {f : M ⟶ N}
    (g : P.module ⟶ kernel f.hom)
    (hg : P.alpha ≫ (Scheme.Modules.pullback G.source.left).map (g ≫ kernel.ι f.hom) =
      (Scheme.Modules.pullback G.target.left).map (g ≫ kernel.ι f.hom) ≫ M.alpha) :
    P.alpha ≫ (Scheme.Modules.pullback G.source.left).map g =
      (Scheme.Modules.pullback G.target.left).map g ≫ kernelDescent f := by
  rw [Functor.map_comp, Functor.map_comp, Category.assoc] at hg
  rw [← cancel_mono ((Scheme.Modules.pullback G.source.left).map (kernel.ι f.hom)),
    Category.assoc, Category.assoc, kernelDescent_ι]
  exact hg

/-- `kernelFork f` is a limit fork: a morphism into `M` killed by `f` factors uniquely through
the kernel of the underlying morphism, and the factorization is compatible with the descent
morphisms. -/
noncomputable def isLimitKernelFork {M N : QuasicoherentModule G} (f : M ⟶ N) :
    IsLimit (kernelFork f) :=
  Fork.IsLimit.mk _
    (fun s ↦ ⟨kernel.lift f.hom s.ι.hom (fork_condition_hom s),
      kernelDescent_comm _ (by rw [kernel.lift_ι]; exact s.ι.comm)⟩)
    (fun s ↦ Hom.ext (kernel.lift_ι f.hom s.ι.hom (fork_condition_hom s)))
    (fun s m hm ↦ by
      apply Hom.ext
      refine (cancel_mono (kernel.ι f.hom)).1 ?_
      rw [kernel.lift_ι]
      exact congrArg Hom.hom hm)

/-- Quasi-coherent modules on a groupoid scheme with flat source and target have kernels. -/
instance : HasKernels (QuasicoherentModule G) where
  has_limit f := ⟨kernelFork f, isLimitKernelFork f⟩

/-! ### The abelian structure -/

/-- The kernel of a morphism of quasi-coherent modules on a groupoid scheme with flat source
and target is the kernel of the underlying morphism of modules, carrying the induced descent
morphism. -/
noncomputable def kernelIsoKernelObj {M N : QuasicoherentModule G} (f : M ⟶ N) :
    kernel f ≅ kernelObj f :=
  (kernelIsKernel f).conePointUniqueUpToIso (isLimitKernelFork f)

/-- The identification of the two kernels is compatible with their inclusions. -/
theorem kernelIsoKernelObj_hom_ι {M N : QuasicoherentModule G} (f : M ⟶ N) :
    (kernelIsoKernelObj f).hom ≫ kernelι f = kernel.ι f := by
  simpa [kernelIsoKernelObj, kernelFork] using
    IsLimit.conePointUniqueUpToIso_hom_comp (kernelIsKernel f) (isLimitKernelFork f)
      WalkingParallelPair.zero

/-- The inclusion of `kernelObj f` is the inclusion of the kernel of the underlying
morphism. -/
theorem forget_map_kernelι {M N : QuasicoherentModule G} (f : M ⟶ N) :
    (forget G).map (kernelι f) = kernel.ι ((forget G).map f) := rfl

/-- The forgetful functor to modules on the object scheme preserves the kernel of every
morphism, because the kernel is computed there. -/
instance preservesKernel_forget {M N : QuasicoherentModule G} (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0) (forget G) := by
  have h : kernelComparison f (forget G) =
      ((forget G).mapIso (kernelIsoKernelObj f)).hom := by
    refine (cancel_mono (kernel.ι ((forget G).map f))).1 ?_
    calc kernelComparison f (forget G) ≫ kernel.ι ((forget G).map f)
        = (forget G).map (kernel.ι f) := kernelComparison_comp_ι f (forget G)
      _ = (forget G).map ((kernelIsoKernelObj f).hom ≫ kernelι f) := by
          rw [kernelIsoKernelObj_hom_ι]
      _ = ((forget G).mapIso (kernelIsoKernelObj f)).hom ≫ kernel.ι ((forget G).map f) :=
          (forget G).map_comp _ _
  have : IsIso (kernelComparison f (forget G)) := h ▸ Iso.isIso_hom _
  exact PreservesKernel.of_iso_comparison (forget G) f

/-- The coimage-image comparison of a morphism of quasi-coherent modules on a groupoid scheme
with flat source and target is an isomorphism, because it is one on the underlying modules and
the forgetful functor reflects isomorphisms. -/
instance isIso_coimageImageComparison {M N : QuasicoherentModule G} (f : M ⟶ N) :
    IsIso (Abelian.coimageImageComparison f) := by
  have e := Abelian.PreservesCoimageImageComparison.iso (forget G) f
  have : IsIso ((forget G).map (Abelian.coimageImageComparison f)) :=
    (Arrow.isIso_iff_isIso_of_isIso e.hom).2 inferInstance
  exact isIso_of_reflects_iso (Abelian.coimageImageComparison f) (forget G)

/-- **Let `S` be a scheme and let `G` be a groupoid scheme over `S` whose source and target are
flat.  Then the category of quasi-coherent modules on `G` is abelian.** -/
@[stacks 077S, sga "3 I 4.7.2.1" "Mod.q.c. case"]
noncomputable instance abelian : Abelian (QuasicoherentModule G) :=
  Abelian.ofCoimageImageComparisonIsIso

end Flat

end QuasicoherentModule

end Stacks.Groupoids.GroupoidScheme

end
