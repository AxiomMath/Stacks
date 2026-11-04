module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection

/-!
# The kernel of the structure map of a morphism of algebraic spaces as a sheaf of ideals

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`. Stacks 03G8 attaches to `f` the structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of sheaves of
rings on the small étale site of `Y`. Its kernel, chart by chart, is a sheaf of ideals of `𝒪_Y`.

For `f` the inclusion of a closed subspace `Z ⊆ X` this is the defining ideal sheaf
`AlgebraicGeometry.Space.definingIdealSheaf` of Stacks 03MB.

## Main definitions

* `AlgebraicGeometry.Space.kernelIdealSheaf` is the kernel of the structure map of an arbitrary
  morphism of algebraic spaces, as a sheaf submodule of the structure sheaf of the target on its
  small étale ringed site.

## Main results

* `AlgebraicGeometry.Space.mem_ker_structureSharp_app_map` and
  `AlgebraicGeometry.Space.mem_ker_structureSharp_app_of_sieve` are the two conditions making the
  chartwise kernels a sheaf submodule: stability under étale restriction, and locality of
  membership.
* `AlgebraicGeometry.Space.kernelIdealSheaf_obj`: its sections over an étale chart are the kernel
  of the structure map on that chart.
* `AlgebraicGeometry.Space.kernelIdealSheaf_eq_definingIdealSheaf`: for the inclusion of a closed
  subspace it is the defining ideal sheaf.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : AlgebraicSpaces B S hS}

/-- **The kernel of the structure map is stable under étale restriction.** A regular function on
an étale chart of `Y` killed by `f♯` restricts to a function killed by `f♯` on any smaller
chart. -/
theorem mem_ker_structureSharp_app_map (f : X ⟶ Y) {U V : (SmallEtale B S hS Y.1)ᵒᵖ} (g : U ⟶ V)
    (a : ToType ((structureRingSheaf B S hS Y).obj.obj U))
    (ha : a ∈ RingHom.ker ((structureSharp B S hS f).hom.app U).hom) :
    ((structureRingSheaf B S hS Y).obj.map g).hom a ∈
      RingHom.ker ((structureSharp B S hS f).hom.app V).hom := by
  rw [RingHom.mem_ker, structureSharp_app_apply_map, RingHom.mem_ker.1 ha, map_zero]

/-- **Membership in the kernel of the structure map is local on the small étale site.** A regular
function on an étale chart of `Y` whose restriction along every arrow of a covering sieve is
killed by `f♯` is itself killed by `f♯`. -/
theorem mem_ker_structureSharp_app_of_sieve (f : X ⟶ Y) (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (s : ToType ((structureRingSheaf B S hS Y).obj.obj U))
    (T : Sieve U.unop) (hT : T ∈ SmallEtale.topology B S hS Y.1 U.unop)
    (h : ∀ (V : SmallEtale B S hS Y.1) (m : V ⟶ U.unop), T m →
      ((structureRingSheaf B S hS Y).obj.map m.op).hom s ∈
        RingHom.ker ((structureSharp B S hS f).hom.app (op V)).hom) :
    s ∈ RingHom.ker ((structureSharp B S hS f).hom.app U).hom := by
  refine RingHom.mem_ker.2 <| (structureRingSheafDirectImage B S hS f).isSeparated U.unop T hT _ 0
    fun V m hm ↦ ?_
  exact (structureSharp_app_apply_map B S hS X Y f m.op s).symm.trans
    ((RingHom.mem_ker.1 (h V m hm)).trans (map_zero _).symm)

/-- **The kernel ideal sheaf of a morphism of algebraic spaces.** The kernels of the structure
map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of Stacks 03G8, taken at every étale scheme chart of `Y`, are the
sections of a sheaf submodule of the structure sheaf `𝒪_Y` on the small étale ringed site
of `Y`. -/
noncomputable def kernelIdealSheaf (f : X ⟶ Y) :
    (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule where
  obj U := RingHom.ker ((structureSharp B S hS f).hom.app U).hom
  map g a ha := mem_ker_structureSharp_app_map B S hS f g a ha
  isSheaf {U} s hs :=
    mem_ker_structureSharp_app_of_sieve B S hS f U s _ hs fun _ _ hm => hm

/-- The sections of the kernel ideal sheaf over an étale chart are the kernel of the structure
map on that chart. -/
theorem kernelIdealSheaf_obj (f : X ⟶ Y) (U : (SmallEtale B S hS Y.1)ᵒᵖ) :
    (kernelIdealSheaf B S hS f).obj U = RingHom.ker ((structureSharp B S hS f).hom.app U).hom :=
  rfl

/-- **The defining ideal sheaf of a closed subspace is the kernel ideal sheaf of its
inclusion.** -/
theorem kernelIdealSheaf_eq_definingIdealSheaf (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    kernelIdealSheaf B S hS (ObjectProperty.homMk Z.1.ι :
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X) =
      definingIdealSheaf B S hS X Z :=
  rfl

end AlgebraicGeometry.Space

end
