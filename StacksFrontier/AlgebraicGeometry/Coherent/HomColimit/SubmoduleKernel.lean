module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleKer
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.Injectivity
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
/-!
# The kernel of a morphism of `𝒪_X`-modules as a subsheaf

Let `f : M ⟶ N` be a morphism of `𝒪_X`-modules on a scheme `X`.  The subsheaf of `M` cut out by
the vanishing of `f`, which `SheafOfModules.Submodule.ker` supplies, is here named as an object
of `X.Modules` together with its inclusion, shown to be a kernel of `f`, and shown to be
quasi-coherent when `M` and `N` are.

## Main definitions

* `kerMod`: the subsheaf `ker f` of `M`, as an object of `X.Modules`.
* `kerInclusion`: the inclusion `ker f ⟶ M`, with its type pinned to `X.Modules`.
* `kerIsLimit`: the inclusion of `ker f` into `M` is a kernel of `f`.
* `kerIso`: the resulting isomorphism of `ker f` with the categorical kernel of `f`.

## Main results

* `isQuasicoherent_kerMod`: **the subsheaf `ker f` is quasi-coherent** when `M` and `N` are.
  This is the quasi-coherence of a kernel, `Stacks.AlgebraicGeometry.QcohLimits`, transported
  along `kerIso`.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules _` carrying its own `Category`
instance, which copies the one of `SheafOfModules`.  The two categories therefore have the same
composition and identities but their `Mono` and `IsIso` propositions, and the kernels they
compute, are not syntactically the same.  Every statement below is phrased in `X.Modules`, which
is the spelling its consumers use; the three places where the `SheafOfModules` spelling of a fact
has to be re-elaborated are the monomorphism instance, the construction of the isomorphism, and
the transport of quasi-coherence, and each does so by applying the general result with its
category argument supplied positionally.

## References

* [Stacks Project, Tag 01AP](https://stacks.math.columbia.edu/tag/01AP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-- The subsheaf of `M` cut out by the vanishing of `f : M ⟶ N`, as an object of `X.Modules`. -/
public noncomputable abbrev kerMod {M N : X.Modules} (f : M ⟶ N) : X.Modules :=
  subMod (SheafOfModules.Submodule.ker f)

/-- The inclusion `ker f ⟶ M`, with its type pinned to `X.Modules`. -/
public noncomputable abbrev kerInclusion {M N : X.Modules} (f : M ⟶ N) : kerMod f ⟶ M :=
  (SheafOfModules.Submodule.ker f).ι

/-- The inclusion of `ker f` into `M`, composed with `f`, is zero. -/
@[reassoc (attr := simp)]
public theorem kerInclusion_comp {M N : X.Modules} (f : M ⟶ N) : kerInclusion f ≫ f = 0 :=
  SheafOfModules.Submodule.ker_ι_comp f

/-- A section of `M` lies in `ker f` exactly when `f` annihilates it. -/
public theorem mem_kerMod {M N : X.Modules} (f : M ⟶ N) (V : X.Opens) (x : Γ(M, V)) :
    x ∈ (SheafOfModules.Submodule.ker f).toSubmodule.obj (op V) ↔ f.app V x = 0 :=
  Iff.rfl

/-- The inclusion of `ker f` into `M` is a monomorphism. -/
public instance mono_kerInclusion {M N : X.Modules} (f : M ⟶ N) : Mono (kerInclusion f) :=
  have hm : @Mono (SheafOfModules.{u} X.ringCatSheaf) _ _ _
      (SheafOfModules.Submodule.ker f).ι :=
    Functor.mono_of_mono_map (SheafOfModules.forget X.ringCatSheaf)
      (inferInstanceAs (Mono (SheafOfModules.Submodule.ker f).toSubmodule.ι))
  ⟨fun g h e ↦ hm.right_cancellation g h e⟩

/-- **The inclusion of `ker f` into `M` is a kernel of `f`.**  A morphism annihilated by `f` has
all its values in `ker f`, hence factors through it, uniquely because the inclusion is a
monomorphism. -/
public noncomputable def kerIsLimit {M N : X.Modules} (f : M ⟶ N) :
    IsLimit (KernelFork.ofι (kerInclusion f) (kerInclusion_comp f)) :=
  KernelFork.IsLimit.ofι' _ _ fun {P} k hk ↦
    ⟨(SheafOfModules.Submodule.ker f).factorThru k fun W x ↦
        (SheafOfModules.Submodule.mem_ker f W _).2 (by
          rw [show PresheafOfModules.Hom.app f.val W (PresheafOfModules.Hom.app k.val W x)
            = PresheafOfModules.Hom.app (k ≫ f).val W x from rfl, hk]; rfl),
      (SheafOfModules.Submodule.ker f).factorThru_ι k _⟩

/-- The subsheaf `ker f` of `M` is the categorical kernel of `f`. -/
public noncomputable def kerIso {M N : X.Modules} (f : M ⟶ N) : kerMod f ≅ kernel f :=
  IsLimit.conePointUniqueUpToIso (kerIsLimit f) (limit.isLimit (parallelPair f 0))

/-- The isomorphism of `ker f` with the categorical kernel of `f` carries the inclusion of the
kernel to the inclusion of `ker f`. -/
@[reassoc (attr := simp)]
public theorem kerIso_hom_comp_ι {M N : X.Modules} (f : M ⟶ N) :
    (kerIso f).hom ≫ kernel.ι f = kerInclusion f :=
  IsLimit.conePointUniqueUpToIso_hom_comp (kerIsLimit f)
    (limit.isLimit (parallelPair f 0)) WalkingParallelPair.zero

/-- **The subsheaf `ker f` is quasi-coherent** when `M` and `N` are: it is isomorphic to the
categorical kernel of `f`, which is quasi-coherent. -/
public instance isQuasicoherent_kerMod {M N : X.Modules} (f : M ⟶ N) [M.IsQuasicoherent]
    [N.IsQuasicoherent] : (kerMod f).IsQuasicoherent :=
  ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (@Iso.mk (SheafOfModules.{u} X.ringCatSheaf) _ _ _ (kerIso f).inv (kerIso f).hom
      (kerIso f).inv_hom_id (kerIso f).hom_inv_id)
    (inferInstanceAs (kernel f).IsQuasicoherent)

end Stacks.AlgebraicGeometry.IdealPowerColimit

end

end
