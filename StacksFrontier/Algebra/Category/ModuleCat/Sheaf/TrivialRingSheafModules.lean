module

public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.Defs
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal

/-!
# Sheaves of modules over a sheaf of zero rings

A module over the zero ring is zero. Sheafwise: if every ring of sections of a sheaf of rings `O`
on a site is trivial, then every sheaf of `O`-modules is a zero object, and triviality of the
sections over an object propagates to all objects lying over it.

## Main results

* `Stacks.SheafOfModules.subsingleton_sections`: a module of sections over a trivial ring of
  sections is trivial.
* `Stacks.SheafOfModules.isZero_of_subsingleton_sections`: a sheaf of modules over a sheaf of
  rings with trivial rings of sections is a zero object.
* `Stacks.SheafOfModules.subsingleton_of_subsingleton_of_le`: triviality of the ring of sections
  over an object passes to any object mapping to it.
* `Stacks.SheafOfModules.isZero_over_restrictScalars`: on any site, if a sheaf of rings `T` has
  trivial sections over an object `W`, then the restriction to the slice site over `W` of the
  scalar restriction along any morphism into `T` of any sheaf of `T`-modules is a zero object.
* `Stacks.SheafOfModules.isZero_restrictModules_restrictScalars`: on a ringed space, if a sheaf of
  rings `T` receiving the structure sheaf has trivial sections over an open `W`, then the
  restriction to `W` of the scalar restriction along that morphism of any sheaf of `T`-modules is
  a zero object of the category of modules on the open subspace.

## Implementation notes

`IsZero` is obtained from `CategoryTheory.Limits.IsZero.iff_id_eq_zero`: a morphism of sheaves of
modules is determined by its components on the modules of sections, so the identity is the zero
morphism as soon as all modules of sections are subsingletons.

The last result is proved directly from the criterion on all sections rather than by transporting
a zero object along `restrictModules`: the sheaf of rings `T` is only assumed trivial over `W`, so
the module itself need not be zero on `X`, and only its restriction is. The sections of the
restriction over an open `V` of the open subspace `W` are the sections of the original module over
the image of `V` in `X`, an open contained in `W`, which is where triviality propagates.

## References

* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe u v w

namespace Stacks.SheafOfModules

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {T : Sheaf J RingCat.{w}}

/-- If the ring of sections of `T` over `V` is trivial, then so is the module of sections over `V`
of any sheaf of `T`-modules. -/
public theorem subsingleton_sections (M : _root_.SheafOfModules.{w} T) {V : Cᵒᵖ}
    (h : Subsingleton (T.obj.obj V)) : Subsingleton (M.val.obj V) := by
  have h1 : (1 : T.obj.obj V) = 0 := h.elim _ _
  refine subsingleton_of_forall_eq 0 fun x => ?_
  conv_lhs => rw [← one_smul (T.obj.obj V) x]
  rw [h1, zero_smul]

/-- A sheaf of modules all of whose modules of sections are trivial is a zero object. -/
public theorem isZero_of_forall_subsingleton_sections (M : _root_.SheafOfModules.{w} T)
    (h : ∀ V : Cᵒᵖ, Subsingleton (M.val.obj V)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  ext V x
  exact (h V).elim _ _

/-- A sheaf of modules over a sheaf of rings whose rings of sections are all trivial is a zero
object. -/
public theorem isZero_of_subsingleton_sections
    (h : ∀ V : C, Subsingleton (T.obj.obj (op V))) (M : _root_.SheafOfModules.{w} T) :
    IsZero M :=
  isZero_of_forall_subsingleton_sections M fun V => subsingleton_sections M (h V.unop)

/-- Triviality of the rings of sections propagates along the restriction maps of `T`: a morphism
`V ⟶ U` of the site induces a ring homomorphism from the sections over `U` to the sections over
`V`, and a ring homomorphism out of a trivial ring forces `1 = 0` in its target. -/
public theorem subsingleton_of_subsingleton_of_le {U V : C} (f : V ⟶ U)
    (h : Subsingleton (T.obj.obj (op U))) : Subsingleton (T.obj.obj (op V)) := by
  have h1 : (1 : T.obj.obj (op V)) = 0 := by
    simpa using congrArg (T.obj.map f.op).hom (h.elim (1 : T.obj.obj (op U)) 0)
  exact subsingleton_of_forall_eq 0 fun x => by rw [← mul_one x, h1, mul_zero]

/-- **The slice-site form.** If a sheaf of rings `T` on a site has trivial sections over an object
`W`, then the restriction to the slice site over `W` of the scalar restriction along any morphism
`p` into `T` of any sheaf of `T`-modules is a zero object.

The modules of sections of the restriction at an object `V ⟶ W` of the slice site are the sections
of the given module over `V`; `T` is trivial over `V` because `V` lies over `W`, hence so are
those sections. This is `isZero_restrictModules_restrictScalars` with the restriction taken to the
slice site rather than to an open subspace, and unlike that one it needs no ringed space. -/
public theorem isZero_over_restrictScalars {S : Sheaf J RingCat.{w}} (p : S ⟶ T)
    (M : _root_.SheafOfModules.{w} T) (W : C) (hW : Subsingleton (T.obj.obj (op W))) :
    IsZero (((_root_.SheafOfModules.restrictScalars p).obj M).over W) :=
  isZero_of_forall_subsingleton_sections _ fun V =>
    subsingleton_sections M (subsingleton_of_subsingleton_of_le V.unop.hom hW)

end Site

section RingedSpace

variable {X : RingedSpace.{u, u}} (W : Opens X.carrier)
  {T : Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u}}

/-- The image in `X` of an open subset of the open subspace `W` is contained in `W`. -/
public theorem isOpenEmbedding_functor_obj_le_of_restrict
    (V : Opens (X.restrict W.isOpenEmbedding).carrier) :
    W.isOpenEmbedding.functor.obj V ≤ W := by
  refine SetLike.coe_subset_coe.mp ?_
  rintro x ⟨y, -, rfl⟩
  exact y.2

/-- If a sheaf of rings `T` on a ringed space `X`, equipped with a morphism `p` from the structure
sheaf of rings, has trivial sections over an open `W`, then the restriction to `W` of the scalar
restriction along `p` of any sheaf of `T`-modules is a zero object.

The modules of sections of the restriction over an open `V` of `W` are the sections of the given
module over the image of `V` in `X`, an open contained in `W`; `T` is trivial there, hence so are
those sections. -/
public theorem isZero_restrictModules_restrictScalars
    (p : Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf ⟶ T) (M : _root_.SheafOfModules.{u} T)
    (hW : Subsingleton (T.obj.obj (op W))) :
    IsZero ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X W).obj
      ((_root_.SheafOfModules.restrictScalars p).obj M)) :=
  isZero_of_forall_subsingleton_sections _ fun V =>
    subsingleton_sections M
      (subsingleton_of_subsingleton_of_le
        (homOfLE (isOpenEmbedding_functor_obj_le_of_restrict W V.unop)) hW)

end RingedSpace

end Stacks.SheafOfModules

end
