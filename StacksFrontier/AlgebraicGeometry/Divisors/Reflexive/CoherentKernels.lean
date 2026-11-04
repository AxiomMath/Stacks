module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.CoherentCategory
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ExactSequence

/-!
# Kernels and cokernels of coherent reflexive modules

Let `X` be an integral locally Noetherian scheme and `𝒞` the category of coherent reflexive
`𝒪_X`-modules.  The kernel of a morphism of `𝒞` is computed in `Coh(𝒪_X)`: the ordinary kernel
is again reflexive, because it is the kernel of a map into a torsion-free module.  The cokernel
of `𝒞` is *not* the ordinary one — it is the reflexive hull of the ordinary cokernel, and its
universal property comes from the reflexive-hull adjunction.

## Main definitions

* `kernelObj f`, `kernelι f`: the ordinary kernel of `f` and its inclusion, as an object and a
  morphism of `𝒞`.
* `cokernelObj f`, `cokernelπ f`: the reflexive hull of the ordinary cokernel of `f`, and the
  ordinary projection followed by the canonical map to the double dual.

## Main results

* `isReflexive_kernel`: the ordinary kernel of a morphism of coherent reflexive modules is
  reflexive.
* `kernelIsKernel`: the ordinary kernel is a kernel in `𝒞`.
* `cokernelIsCokernel`: the reflexive hull of the ordinary cokernel is a cokernel in `𝒞`.

## Implementation notes

Both universal properties are stated for the explicit object and the explicit morphism, not up
to an unspecified isomorphism, so they determine the (co)kernel and not merely its existence.

Reflexivity of the kernel is [Stacks, Tag 0EBG] applied to `0 → Ker(φ) → ℱ → 𝒢`, whose right
term is torsion free by [Stacks, Tag 0AY2] because it is reflexive.

`hom_ext₂`, `comp_hom₂` and `zero_hom₂` reduce an equation between morphisms of `𝒞` to one
between the underlying morphisms of `𝒪_X`-modules, across the two nested full subcategories.
Proofs here are written in term style because `𝒞` sits over `SheafOfModules (structureSheaf
X.sheaf)` while the hull and the canonical map are stated over the definitionally equal
`X.Modules`, and `rw` does not see through that.

## References

* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive isTorsionFree_of_isReflexive
  reflexiveHull toDoubleDual)
open Stacks.AlgebraicGeometry.ReflexiveHull (CoherentModules CoherentReflexiveModules inclusion)

universe u

namespace AlgebraicGeometry.CoherentReflexive

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  {F G : CoherentReflexiveModules X}

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- Two morphisms of coherent reflexive modules agree as soon as the underlying morphisms of
`𝒪_X`-modules do. -/
theorem hom_ext₂ {A B : CoherentReflexiveModules X} {a b : A ⟶ B}
    (h : a.hom.hom = b.hom.hom) : a = b :=
  ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ h)

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- Composition of morphisms of coherent reflexive modules is composition of the underlying
morphisms of `𝒪_X`-modules. -/
theorem comp_hom₂ {A B C : CoherentReflexiveModules X} (a : A ⟶ B) (b : B ⟶ C) :
    (a ≫ b).hom.hom = a.hom.hom ≫ b.hom.hom :=
  rfl

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- The zero morphism of coherent reflexive modules has zero underlying morphism. -/
theorem zero_hom₂ {A B : CoherentReflexiveModules X} : (0 : A ⟶ B).hom.hom = 0 :=
  rfl

/-! ### Kernels -/

/-- The ordinary kernel inclusion of a morphism of coherent reflexive modules is a
monomorphism. -/
instance mono_kernel_ι (f : F ⟶ G) : Mono (kernel.ι f.hom.hom) :=
  ⟨fun {_} _ _ h => Fork.IsLimit.hom_ext (kernelIsKernel f.hom.hom) h⟩

/-- **Stacks Project, Tag 0EBH.**  The ordinary kernel of a morphism of coherent reflexive
modules is reflexive: it is the kernel of a map into the reflexive, hence torsion-free, module
`𝒢`. -/
@[stacks 0EBH "kernels"]
theorem isReflexive_kernel (f : F ⟶ G) : IsReflexive (kernel f.hom.hom) :=
  have h1 : _root_.SheafOfModules.IsCoherent F.obj.obj := F.obj.property
  have h2 : _root_.SheafOfModules.IsCoherent G.obj.obj := G.obj.property
  @isReflexive_of_exact_of_isReflexive_of_isTorsionFree X _ _ (kernel f.hom.hom) F.obj.obj
    G.obj.obj (ObjectProperty.prop_kernel (fun M : X.Modules => M.IsCoherent) f.hom.hom h1 h2)
    h1 h2 (kernel.ι f.hom.hom) f.hom.hom (mono_kernel_ι f) (kernel.condition f.hom.hom)
    (ShortComplex.exact_kernel _) F.property
    (isTorsionFree_of_isReflexive G.obj.obj G.property)

/-- The ordinary kernel of a morphism of coherent reflexive modules, as a coherent reflexive
module. -/
noncomputable abbrev kernelObj (f : F ⟶ G) : CoherentReflexiveModules X :=
  ⟨⟨kernel f.hom.hom, ObjectProperty.prop_kernel (fun M : X.Modules => M.IsCoherent) f.hom.hom
      F.obj.property G.obj.property⟩,
    isReflexive_kernel f⟩

/-- The ordinary kernel inclusion, as a morphism of coherent reflexive modules. -/
noncomputable def kernelι (f : F ⟶ G) : kernelObj f ⟶ F :=
  ObjectProperty.homMk (ObjectProperty.homMk (kernel.ι f.hom.hom))

/-- The underlying morphism of `𝒪_X`-modules of the kernel inclusion. -/
theorem kernelι_hom₂ (f : F ⟶ G) : (kernelι f).hom.hom = kernel.ι f.hom.hom :=
  rfl

/-- The kernel inclusion composed with `f` vanishes. -/
theorem kernelι_comp (f : F ⟶ G) : kernelι f ≫ f = 0 :=
  hom_ext₂ (kernel.condition f.hom.hom)

/-- **Stacks Project, Tag 0EBH.**  The ordinary kernel, with its ordinary inclusion, is a
kernel in the category of coherent reflexive modules. -/
@[stacks 0EBH "kernels"]
noncomputable def kernelIsKernel (f : F ⟶ G) :
    IsLimit (KernelFork.ofι (f := f) (kernelι f) (kernelι_comp f)) :=
  have hlift : ∀ {T : CoherentReflexiveModules X} (g : T ⟶ F), g ≫ f = 0 →
      g.hom.hom ≫ f.hom.hom = 0 := fun g hg =>
    (comp_hom₂ g f).symm.trans ((congrArg (fun k => k.hom.hom) hg).trans zero_hom₂)
  haveI : Mono (kernelι f) :=
    ⟨fun {_} a b h => hom_ext₂ ((cancel_mono (kernel.ι f.hom.hom)).1
      ((comp_hom₂ a (kernelι f)).symm.trans
        ((congrArg (fun k => k.hom.hom) h).trans (comp_hom₂ b (kernelι f)))))⟩
  KernelFork.IsLimit.ofι' (kernelι f) (kernelι_comp f) fun {_} g hg =>
    ⟨ObjectProperty.homMk (ObjectProperty.homMk (kernel.lift f.hom.hom g.hom.hom (hlift g hg))),
      hom_ext₂ (kernel.lift_ι f.hom.hom g.hom.hom (hlift g hg))⟩

/-! ### Cokernels -/

/-- The ordinary cokernel of a morphism of coherent reflexive modules, as a coherent module. -/
noncomputable abbrev ordinaryCokernel (f : F ⟶ G) : CoherentModules X :=
  ⟨cokernel f.hom.hom, ObjectProperty.prop_cokernel (fun M : X.Modules => M.IsCoherent)
    f.hom.hom F.obj.property G.obj.property⟩

/-- The ordinary cokernel projection of a morphism of coherent reflexive modules is an
epimorphism. -/
instance epi_cokernel_π (f : F ⟶ G) : Epi (cokernel.π f.hom.hom) :=
  ⟨fun {_} _ _ h => Cofork.IsColimit.hom_ext (cokernelIsCokernel f.hom.hom) h⟩

/-- The reflexive hull of the ordinary cokernel of a morphism of coherent reflexive modules, as
a coherent reflexive module. -/
noncomputable def cokernelObj (f : F ⟶ G) : CoherentReflexiveModules X :=
  (hullReflection X).obj (ordinaryCokernel f)

/-- The underlying sheaf of the cokernel in the category of coherent reflexive modules is the
double dual of the ordinary cokernel. -/
theorem cokernelObj_obj_obj (f : F ⟶ G) :
    (cokernelObj f).obj.obj = reflexiveHull (cokernel f.hom.hom) :=
  rfl

/-- The ordinary cokernel projection followed by the canonical map to the double dual, as a
morphism of coherent reflexive modules. -/
noncomputable def cokernelπ (f : F ⟶ G) : G ⟶ cokernelObj f :=
  ObjectProperty.homMk (ObjectProperty.homMk
    (cokernel.π f.hom.hom ≫ toDoubleDual (cokernel f.hom.hom)))

/-- The underlying morphism of `𝒪_X`-modules of the cokernel projection. -/
theorem cokernelπ_hom₂ (f : F ⟶ G) :
    (cokernelπ f).hom.hom = cokernel.π f.hom.hom ≫ toDoubleDual (cokernel f.hom.hom) :=
  rfl

/-- `f` followed by the cokernel projection vanishes. -/
theorem comp_cokernelπ (f : F ⟶ G) : f ≫ cokernelπ f = 0 :=
  hom_ext₂ ((Category.assoc f.hom.hom (cokernel.π f.hom.hom) _).symm.trans
    (by rw [cokernel.condition]; exact zero_comp))

/-- **Stacks Project, Tag 0EBH.**  The reflexive hull of the ordinary cokernel, with the
ordinary projection followed by the canonical map to the double dual, is a cokernel in the
category of coherent reflexive modules. -/
@[stacks 0EBH "cokernels"]
noncomputable def cokernelIsCokernel (f : F ⟶ G) :
    IsColimit (CokernelCofork.ofπ (f := f) (cokernelπ f) (comp_cokernelπ f)) := by
  have hdesc : ∀ {T : CoherentReflexiveModules X} (g : G ⟶ T), f ≫ g = 0 →
      f.hom.hom ≫ g.hom.hom = 0 := fun g hg =>
    (comp_hom₂ f g).symm.trans ((congrArg (fun k => k.hom.hom) hg).trans zero_hom₂)
  refine CokernelCofork.IsColimit.ofπ (f := f) (cokernelπ f) (comp_cokernelπ f)
    (fun {T} g hg => ((hullReflectionAdjunction X).homEquiv (ordinaryCokernel f) T).symm
      (ObjectProperty.homMk (cokernel.desc f.hom.hom g.hom.hom (hdesc g hg))))
    (fun {T} g hg => ?_) (fun {T} g hg m hm => ?_)
  · set d := ((hullReflectionAdjunction X).homEquiv (ordinaryCokernel f) T).symm
      (ObjectProperty.homMk (cokernel.desc f.hom.hom g.hom.hom (hdesc g hg))) with hd
    have h1 : ((hullReflectionAdjunction X).homEquiv (ordinaryCokernel f) T d).hom =
        cokernel.desc f.hom.hom g.hom.hom (hdesc g hg) :=
      congrArg (fun k : _ ⟶ (inclusion X).obj T => k.hom) (Equiv.apply_symm_apply _ _)
    have h3 : toDoubleDual (cokernel f.hom.hom) ≫ d.hom.hom =
        cokernel.desc f.hom.hom g.hom.hom (hdesc g hg) :=
      (hullReflectionAdjunction_homEquiv_apply X (ordinaryCokernel f) T d).symm.trans h1
    exact hom_ext₂ ((Category.assoc (cokernel.π f.hom.hom)
      (toDoubleDual (cokernel f.hom.hom)) d.hom.hom).trans
        ((congrArg (fun z => cokernel.π f.hom.hom ≫ z) h3).trans
          (cokernel.π_desc f.hom.hom g.hom.hom (hdesc g hg))))
  · refine (((hullReflectionAdjunction X).homEquiv (ordinaryCokernel f) T).eq_symm_apply).2 ?_
    refine ObjectProperty.hom_ext _ ?_
    refine (hullReflectionAdjunction_homEquiv_apply X (ordinaryCokernel f) T m).trans ?_
    refine (cancel_epi (cokernel.π f.hom.hom)).1 ?_
    refine Eq.trans ?_ (cokernel.π_desc f.hom.hom g.hom.hom (hdesc g hg)).symm
    exact (Category.assoc (cokernel.π f.hom.hom) (toDoubleDual (cokernel f.hom.hom))
      m.hom.hom).symm.trans (congrArg (fun k : G ⟶ T => k.hom.hom) hm)

end AlgebraicGeometry.CoherentReflexive

end
