module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Abelian
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Exactness
public import StacksFrontier.AlgebraicGeometry.Modules.StalkSupport
public import StacksCore.Tactic.StacksAttribute

/-!
# Completion only sees a morphism along the support of the ideal

Let `X` be a Noetherian scheme and `ℐ` a quasi-coherent sheaf of ideals on `X`. The completion
functor of [Stacks, Tag 0880] sends a coherent module `ℱ` to the inverse system
`n ↦ ℱ / ℐ ⁿ⁺¹ ℱ`, every term of which is annihilated by a power of `ℐ` and hence supported
inside `V(ℐ)`. So completion cannot see a coherent module away from `V(ℐ)`, and in particular it
cannot distinguish two coherent modules there: a morphism of coherent modules which is an
isomorphism on the stalks at the points of `V(ℐ)` has an isomorphism for its completion.

This is the step by which an improvement of a coherent module on the locus where its depth is to
be raised — a locus disjoint from `V(ℐ)` — leaves its completion unchanged.

## Main results

* `Stacks.Algebraization.isZero_completionFunctor_obj_of_notMem_supp_on_support` — the completion
  of a coherent module whose support misses `V(ℐ)` is zero.
* `Stacks.Algebraization.isIso_completionFunctor_map_of_isIso_stalkMap_on_support` — a morphism
  of coherent modules which is an isomorphism on the stalks along `V(ℐ)` completes to an
  isomorphism.

## Implementation notes

The proof is the exactness of completion ([Stacks, Tag 0881],
`Stacks.Algebraization.completionFunctor_exact`). The kernel and the cokernel of the morphism
have empty support along `V(ℐ)`, because taking stalks is exact and the stalk map is an
isomorphism there; so their completions vanish. Completion carries the kernel and the cokernel of
a morphism to the kernel and the cokernel of its completion, which therefore has neither, and a
morphism of an abelian category with zero kernel and zero cokernel is an isomorphism.

That a coherent module whose support misses `V(ℐ)` has vanishing completion is a two-sided bound
on the support of a term `ℱ / ℐ ⁿ⁺¹ ℱ`: it lies in `V(ℐ)` by [Stacks, Tag 01Y9], the term being
annihilated by `ℐ ⁿ⁺¹`, and it lies in the support of `ℱ` because the projection out of `ℱ` is an
epimorphism. The two bounds are disjoint, so the term has empty support and is zero.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, and the two
presentations carry separately declared `Category` instances, so an `Epi` or a `Mono` found for
one spelling is invisible to instance search in the other. The stalkwise support criteria of
`StacksFrontier/AlgebraicGeometry/Modules/StalkSupport.lean` are stated at
`AlgebraicGeometry.Scheme.Modules`, which is the spelling used throughout; the crossings into the
bare `SheafOfModules` spelling are made in term mode, by definitional equality rather than by
rewriting.

## References

* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880), the completion functor.
* [Stacks Project, Tag 0881](https://stacks.math.columbia.edu/tag/0881), its exactness.
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9), support and annihilation.
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH), exactness of stalks.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

variable {X : Scheme.{u}}

/-! ### Supports, kernels and cokernels -/

/-- **The pointwise stalkwise criterion for injectivity.** The stalk map of `f` at `x` is
injective exactly when `x` misses the support of the kernel of `f`: taking stalks is left exact,
so the stalk of `kernel f` is the kernel of the stalk map of `f`.

This is the kernel counterpart of
`AlgebraicGeometry.Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel`. -/
public theorem injective_stalkFunctor_map_iff_notMem_supp_kernel {A B : X.Modules} (f : A ⟶ B)
    (x : X) :
    Function.Injective ((Scheme.Modules.stalkFunctor X x).map f) ↔
      x ∉ SheafOfModules.supp (kernel f) := by
  refine Iff.trans
    (Iff.symm (ModuleCat.mono_iff_injective ((Scheme.Modules.stalkFunctor X x).map f)))
    (Iff.trans ?_ (Scheme.Modules.notMem_supp_iff_isZero_stalk (kernel f) x).symm)
  exact ⟨fun _ => IsZero.of_iso (isZero_kernel_of_mono ((Scheme.Modules.stalkFunctor X x).map f))
      (PreservesKernel.iso (Scheme.Modules.stalkFunctor X x) f),
    fun h => Abelian.mono_of_kernel_ι_eq_zero _
      ((IsZero.of_iso h (PreservesKernel.iso (Scheme.Modules.stalkFunctor X x) f).symm).eq_of_src
        _ _)⟩

/-- **The support of the target of an epimorphism is contained in the support of its source.**
Taking stalks preserves colimits, so an epimorphism is surjective on every stalk, and nothing
can be hit at a point where the source has no stalk. -/
public theorem supp_subset_supp_of_epi {M N : X.Modules} (p : M ⟶ N) (hp : Epi p) :
    SheafOfModules.supp N ⊆ SheafOfModules.supp M := by
  intro x hx
  by_contra hM
  have hsub := ModuleCat.isZero_iff_subsingleton.1
    ((Scheme.Modules.notMem_supp_iff_isZero_stalk M x).1 hM)
  have := hp
  have := Scheme.Modules.epi_sheafOfModules p
  have hepi : Epi ((Scheme.Modules.stalkFunctor X x).map p) :=
    preserves_epi_of_preservesColimit (Scheme.Modules.stalkFunctor X x) p
  have hsurj := (ModuleCat.epi_iff_surjective ((Scheme.Modules.stalkFunctor X x).map p)).1 hepi
  have hNzero : IsZero ((Scheme.Modules.stalkFunctor X x).obj N) := by
    refine ModuleCat.isZero_iff_subsingleton.2 ⟨fun a b => ?_⟩
    obtain ⟨a', ha'⟩ := hsurj a
    obtain ⟨b', hb'⟩ := hsurj b
    exact ha'.symm.trans ((congrArg _ (hsub.elim a' b')).trans hb')
  exact (Scheme.Modules.notMem_supp_iff_isZero_stalk N x).2 hNzero hx

/-! ### The completion of a module supported off the ideal -/

/-- **The completion of a coherent module whose support misses `V(ℐ)` is zero.** Each term of the
completion is a quotient of the module, so its support lies in the support of the module; and the
term is annihilated by a power of `ℐ`, so its support lies in `V(ℐ)` by [Stacks, Tag 01Y9]. The
two bounds being disjoint, every term has empty support and is zero. -/
public theorem isZero_completionFunctor_obj_of_notMem_supp_on_support [IsNoetherian X]
    (I : X.IdealSheafData)
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (h : ∀ x : X, x ∈ (I.support : Set X) → x ∉ SheafOfModules.supp M.obj) :
    IsZero ((completionFunctor X I).obj M) := by
  have hterm (n : ℕ) :
      IsZero (C := X.Modules) (((completionFunctor X I).obj M).obj.obj (op n)) := by
    have _ : (((completionFunctor X I).obj M).obj.obj (op n)).IsCoherent :=
      ((completionFunctor X I).obj M).property.1 n
    have hI := (exists_idealPowerMultiple_eq_bot_iff_supp_subset
      (((completionFunctor X I).obj M).obj.obj (op n)) I).1
        ⟨n + 1, ((completionFunctor X I).obj M).property.2.1 n⟩
    have hM := supp_subset_supp_of_epi (completionProjection X I M n)
      (Stacks.Coherent.epi_completionProjection I M n)
    refine Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty _
      (Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_)
    exact h x (hI hx) (hM hx)
  refine (IsZero.iff_id_eq_zero _).2 (ObjectProperty.hom_ext _ ?_)
  exact (IsZero.iff_id_eq_zero _).1 (Functor.isZero _ fun n => hterm n.unop)

/-! ### The completion of a morphism which is an isomorphism along the ideal -/

/-- **A morphism of coherent modules which is an isomorphism on the stalks along `V(ℐ)` completes
to an isomorphism.** Taking stalks is exact, so the kernel and the cokernel of the morphism have
no support where the stalk map is an isomorphism, hence none along `V(ℐ)`; their completions
therefore vanish. Completion is exact ([Stacks, Tag 0881]), so it carries them to the kernel and
the cokernel of the completed morphism, which is then both a monomorphism and an epimorphism. -/
public theorem isIso_completionFunctor_map_of_isIso_stalkMap_on_support [IsNoetherian X]
    (I : X.IdealSheafData)
    {G H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (f : G ⟶ H)
    (hf : ∀ x : X, x ∈ (I.support : Set X) →
      IsIso (AlgebraicGeometry.SheafOfModules.stalkMap X.ringCatSheaf x f.hom)) :
    IsIso ((completionFunctor X I).map f) := by
  have hexact := completionFunctor_exact X I
  rw [exactFunctor_iff] at hexact
  have _ := hexact.1
  have _ := hexact.2
  have _ : PreservesFiniteLimits
      (ObjectProperty.ι (fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent)) :=
    ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _
  have _ : PreservesFiniteColimits
      (ObjectProperty.ι (fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent)) :=
    ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _
  -- the kernel and the cokernel of `f.hom` have no support along `V(ℐ)`
  have hiso (x : X) (hx : x ∈ (I.support : Set X)) :
      IsIso ((Scheme.Modules.stalkFunctor X x).map f.hom) := hf x hx
  have hbij (x : X) (hx : x ∈ (I.support : Set X)) :
      Function.Bijective ((Scheme.Modules.stalkFunctor X x).map f.hom) := by
    have := hiso x hx
    exact ConcreteCategory.bijective_of_isIso ((Scheme.Modules.stalkFunctor X x).map f.hom)
  have hkerSupp (x : X) (hx : x ∈ (I.support : Set X)) :
      x ∉ SheafOfModules.supp (kernel (C := X.Modules) f.hom) :=
    (injective_stalkFunctor_map_iff_notMem_supp_kernel f.hom x).1 (hbij x hx).1
  have hcokSupp (x : X) (hx : x ∈ (I.support : Set X)) :
      x ∉ SheafOfModules.supp (cokernel (C := X.Modules) f.hom) :=
    (Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel f.hom x).1 (hbij x hx).2
  -- transport along the comparison of the coherent kernel with the kernel of sheaves
  have hkerIso : (kernel f).obj ≅ kernel (C := X.Modules) f.hom :=
    PreservesKernel.iso
      (ObjectProperty.ι (fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent)) f
  have hcokIso : (cokernel f).obj ≅ cokernel (C := X.Modules) f.hom :=
    PreservesCokernel.iso
      (ObjectProperty.ι (fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent)) f
  have hkerZero : IsZero ((completionFunctor X I).obj (kernel f)) :=
    isZero_completionFunctor_obj_of_notMem_supp_on_support I (kernel f) fun x hx =>
      (SheafOfModules.supp_eq_of_iso hkerIso) ▸ hkerSupp x hx
  have hcokZero : IsZero ((completionFunctor X I).obj (cokernel f)) :=
    isZero_completionFunctor_obj_of_notMem_supp_on_support I (cokernel f) fun x hx =>
      (SheafOfModules.supp_eq_of_iso hcokIso) ▸ hcokSupp x hx
  have hmono : Mono ((completionFunctor X I).map f) :=
    Abelian.mono_of_kernel_ι_eq_zero _
      ((IsZero.of_iso hkerZero (PreservesKernel.iso (completionFunctor X I) f).symm).eq_of_src
        _ _)
  have hepi : Epi ((completionFunctor X I).map f) :=
    Abelian.epi_of_cokernel_π_eq_zero _
      ((IsZero.of_iso hcokZero (PreservesCokernel.iso (completionFunctor X I) f).symm).eq_of_tgt
        _ _)
  exact isIso_of_mono_of_epi _

end Stacks.Algebraization

end
