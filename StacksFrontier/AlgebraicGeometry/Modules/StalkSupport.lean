module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFinite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionTransport
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Surjectivity on one stalk and the support of a cokernel

For a morphism `f : A ⟶ B` of modules on a scheme and a point `x`, the stalk map of `f` at `x`
is surjective exactly when the cokernel of `f` has vanishing stalk at `x`, that is, when `x`
misses the support of that cokernel. This is the pointwise half of the stalkwise criterion for
an epimorphism, and it is the form in which the support of a cokernel is computed: taking stalks
preserves colimits, so the stalk of the cokernel is the cokernel of the stalk map.

The file also records the finiteness and closedness facts that go with it — a quotient of a
module of finite type is of finite type, so the support of a cokernel of a map into a module of
finite type is closed — and the two elementary compatibilities of the stalk map, with
composition and with isomorphisms.

## Main results

* `AlgebraicGeometry.Scheme.Modules.notMem_supp_iff_isZero_stalk`: a point misses the support of
  a module exactly when the module has vanishing stalk there.
* `AlgebraicGeometry.Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel`: the
  stalk map of `f` at `x` is surjective exactly when `x` misses the support of `cokernel f`.
* `AlgebraicGeometry.Scheme.Modules.supp_cokernel_subset_supp`: **the support of a cokernel is
  contained in the support of the target**, with no hypothesis on either module.
* `AlgebraicGeometry.Scheme.Modules.supp_cokernel_comp_isIso` and
  `AlgebraicGeometry.Scheme.Modules.supp_cokernel_epi_comp`: that support is unchanged by
  post-composing the morphism with an isomorphism, or pre-composing it with an epimorphism.
* `AlgebraicGeometry.Scheme.Modules.stalkLinearMap_comp`,
  `AlgebraicGeometry.Scheme.Modules.stalkLinearMap_id` and
  `AlgebraicGeometry.Scheme.Modules.surjective_stalkLinearMap_of_section`: the stalk map of a
  composite is the composite of the stalk maps, the stalk map of the identity is the identity,
  and the stalk map of a split epimorphism is surjective.
* `AlgebraicGeometry.Scheme.Modules.surjective_stalkLinearMap_of_comp`: a surjective stalk map
  of a composite makes the second factor's stalk map surjective.
* `AlgebraicGeometry.Scheme.Modules.isFiniteType_cokernel` and
  `AlgebraicGeometry.Scheme.Modules.isClosed_supp_cokernel`: finiteness and closedness for the
  cokernel.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a definition over `SheafOfModules` whose categorical
instances are copies, so a hypothesis `Epi f` in one reading is invisible to instance search in
the other; `AlgebraicGeometry.Scheme.Modules.epi_sheafOfModules` transports it by hand from the
cancellation property. For the same reason the structure sheaf of a scheme is spelled both
`TopCat.Sheaf RingCat X` and `CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat`,
which are not identified at the `implicit` transparency level; statements that cross that
boundary are therefore composed in term mode rather than rewritten.

## References

* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- An epimorphism of modules on a scheme, read in the category of sheaves of modules over the
structure sheaf. The category instance on `AlgebraicGeometry.Scheme.Modules` is a copy of the
one on `SheafOfModules`, so the two readings are not interchangeable by instance search. -/
theorem epi_sheafOfModules {M N : X.Modules} (f : M ⟶ N) [Epi f] :
    @Epi (SheafOfModules.{u} X.ringCatSheaf) (inferInstance) M N f :=
  ⟨fun g h hcomp => (‹Epi f›).left_cancellation g h hcomp⟩

/-- A quotient of a module of finite type is of finite type, so the cokernel of a morphism into
a module of finite type is of finite type. -/
theorem isFiniteType_cokernel {A B : X.Modules} (f : A ⟶ B) (hB : B.IsFiniteType) :
    (cokernel f).IsFiniteType := by
  have := epi_sheafOfModules (cokernel.π f)
  exact Stacks.SheafOfModules.SliceFinite.isFiniteType_of_epi.{u, u, u} (cokernel.π f) hB

/-- The support of the cokernel of a morphism into a module of finite type is closed. -/
theorem isClosed_supp_cokernel {A B : X.Modules} (f : A ⟶ B) (hB : B.IsFiniteType) :
    IsClosed (SheafOfModules.supp (cokernel f)) :=
  @SheafOfModules.isClosed_supp _ X.ringCatSheaf (cokernel f) (isFiniteType_cokernel f hB)

/-- The stalk functor on modules over a scheme: the stalk at `x`, as a module over the local
ring. The type is deliberately not ascribed with `AlgebraicGeometry.Scheme.Modules` as its
domain: that ascription replaces the category instance by its copy, after which instance search
no longer finds the functor's exactness properties. -/
abbrev stalkFunctor (X : Scheme.{u}) (x : X) :=
  AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x

/-- A point misses the support of a module exactly when the stalk there is a zero module. -/
theorem notMem_supp_iff_isZero_stalk (F : X.Modules) (x : X) :
    x ∉ SheafOfModules.supp F ↔ IsZero ((stalkFunctor X x).obj F) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun h => ⟨fun a b => ?_⟩, fun h ⟨a, ha⟩ => ha (h.elim a 0)⟩
  exact sub_eq_zero.mp (not_not.mp (not_exists.mp h (a - b)))

/-- **The pointwise stalkwise criterion for surjectivity.** The stalk map of `f` at `x` is
surjective exactly when `x` misses the support of the cokernel of `f`: taking stalks preserves
colimits, so the stalk of `cokernel f` is the cokernel of the stalk map of `f`. -/
theorem surjective_stalkLinearMap_iff_notMem_supp_cokernel {A B : X.Modules} (f : A ⟶ B)
    (x : X) :
    Function.Surjective (stalkLinearMap A B f x) ↔ x ∉ SheafOfModules.supp (cokernel f) := by
  refine Iff.trans (Iff.symm (ModuleCat.epi_iff_surjective ((stalkFunctor X x).map f)))
    (Iff.trans ?_ (notMem_supp_iff_isZero_stalk (cokernel f) x).symm)
  exact ⟨fun _ => IsZero.of_iso (isZero_cokernel_of_epi ((stalkFunctor X x).map f))
      (PreservesCokernel.iso (stalkFunctor X x) f),
    fun h => Abelian.epi_of_cokernel_π_eq_zero _
      ((IsZero.of_iso h (PreservesCokernel.iso (stalkFunctor X x) f).symm).eq_of_tgt _ _)⟩

/-- **The support of a cokernel is contained in the support of the target.** At a point outside
the support of `B` the stalk of `B` vanishes, so the stalk map of `f` is surjective there for
want of anything to hit, and the pointwise stalkwise criterion puts the point outside the
support of the cokernel. -/
theorem supp_cokernel_subset_supp {A B : X.Modules} (f : A ⟶ B) :
    SheafOfModules.supp (cokernel f) ⊆ SheafOfModules.supp B := by
  intro x hx
  by_contra hB
  refine (surjective_stalkLinearMap_iff_notMem_supp_cokernel f x).1 (fun w => ⟨0, ?_⟩) hx
  exact (ModuleCat.isZero_iff_subsingleton.mp
    ((notMem_supp_iff_isZero_stalk B x).1 hB)).elim _ _

/-- **The support of a cokernel does not change when the morphism is post-composed with an
isomorphism.** -/
theorem supp_cokernel_comp_isIso {A B C : X.Modules} (g : A ⟶ B) (j : B ⟶ C) [IsIso j] :
    SheafOfModules.supp (cokernel (g ≫ j)) = SheafOfModules.supp (cokernel g) :=
  SheafOfModules.supp_eq_of_iso (cokernelCompIsIso g j)

/-- **The support of a cokernel does not change when the morphism is pre-composed with an
isomorphism** -- more generally with an epimorphism, which is all
`CategoryTheory.Limits.cokernelEpiComp` asks for. -/
theorem supp_cokernel_epi_comp {A B C : X.Modules} (i : A ⟶ B) [Epi i] (g : B ⟶ C) :
    SheafOfModules.supp (cokernel (i ≫ g)) = SheafOfModules.supp (cokernel g) :=
  SheafOfModules.supp_eq_of_iso (cokernelEpiComp i g)

/-- The stalk map of a composite is the composite of the stalk maps. -/
theorem stalkLinearMap_comp {A B C : X.Modules} (u : A ⟶ B) (v : B ⟶ C) (x : X)
    (z : A.presheaf.stalk x) :
    stalkLinearMap A C (u ≫ v) x z = stalkLinearMap B C v x (stalkLinearMap A B u x z) :=
  congrArg (fun g : (stalkFunctor X x).obj A ⟶ (stalkFunctor X x).obj C =>
    ConcreteCategory.hom g z) ((stalkFunctor X x).map_comp u v)

/-- The stalk map of the identity is the identity. -/
theorem stalkLinearMap_id (A : X.Modules) (x : X) (z : A.presheaf.stalk x) :
    stalkLinearMap A A (𝟙 A) x z = z :=
  congrArg (fun g : (stalkFunctor X x).obj A ⟶ (stalkFunctor X x).obj A =>
    ConcreteCategory.hom g z) ((stalkFunctor X x).map_id A)

/-- The stalk map of a split epimorphism is surjective; in particular the stalk map of an
isomorphism is, taking for the section the inverse. -/
theorem surjective_stalkLinearMap_of_section {A B : X.Modules} (f : A ⟶ B) (g : B ⟶ A)
    (h : g ≫ f = 𝟙 B) (x : X) : Function.Surjective (stalkLinearMap A B f x) := fun w =>
  ⟨stalkLinearMap B A g x w,
    (stalkLinearMap_comp g f x w).symm.trans
      ((congrArg (fun k : B ⟶ B => stalkLinearMap B B k x w) h).trans
        (stalkLinearMap_id B x w))⟩

/-- The stalk map of a morphism whose composite with a morphism out of it is surjective is
itself surjective. -/
theorem surjective_stalkLinearMap_of_comp {A B C : X.Modules} (u : A ⟶ B) (v : B ⟶ C) (x : X)
    (h : Function.Surjective (stalkLinearMap A C (u ≫ v) x)) :
    Function.Surjective (stalkLinearMap B C v x) := by
  intro w
  obtain ⟨z, hz⟩ := h w
  exact ⟨stalkLinearMap A B u x z, (stalkLinearMap_comp u v x z).symm.trans hz⟩

end AlgebraicGeometry.Scheme.Modules

end
