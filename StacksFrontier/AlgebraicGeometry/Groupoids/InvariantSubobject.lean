module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic

/-!
# Invariant subobjects of a groupoid scheme

A monomorphism into the object scheme of a groupoid scheme is *invariant* when its
pullbacks along the source and the target of the groupoid define the same subobject of
the arrow scheme. This is the subobject form of invariance, applicable to an arbitrary
immersion, where `Stacks.Groupoids.IsInvariantClosedSubscheme` applies only to a closed
subscheme presented by an ideal sheaf.

## Main results

* `Stacks.Groupoids.isInvariantClosedSubscheme_iff_isInvariantMonomorphism` identifies the
  two notions of invariance on a closed subscheme: an ideal sheaf is invariant exactly
  when the closed immersion it presents is an invariant monomorphism.
* `AlgebraicGeometry.Scheme.IdealSheafData.subobject_pullback_mk_subschemeι` computes the
  pullback of the subobject presented by an ideal sheaf as the subobject presented by the
  pulled-back ideal sheaf.
* `AlgebraicGeometry.Scheme.IdealSheafData.subobject_mk_subschemeι_inj` says that an ideal
  sheaf is determined by the subobject its closed subscheme presents.

## Implementation notes

The two invariance conditions are not literally the same statement: one is an equality in
the lattice of ideal sheaves on the arrow scheme, the other an equality in its subobject
poset. They are identified here by two general facts about `Scheme.IdealSheafData`, both of
which were missing. First, `Scheme.IdealSheafData.comapIso` exhibits the subscheme of a
pulled-back ideal sheaf as a fibre product, so the pullback functor on subobjects carries
`Subobject.mk I.subschemeι` to `Subobject.mk (I.comap f).subschemeι`; the square needed by
`Subobject.pullback_obj_mk` is supplied by `isPullback_of_isClosedImmersion`, whose
hypothesis on kernels is `Scheme.IdealSheafData.ker_subschemeι`. Second, the subobject
presented by a closed subscheme determines the ideal sheaf, because the kernel of the
arrow of `Subobject.mk f` agrees with the kernel of `f`; the two differ by the isomorphism
`Subobject.underlyingIso`, along which `Scheme.Hom.ker` is invariant.

## References

* [Stacks Project, Tag 03BC](https://stacks.math.columbia.edu/tag/03BC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The kernel of the arrow of the subobject presented by a monomorphism is the kernel of
that monomorphism. -/
theorem Scheme.Hom.ker_subobject_mk_arrow (f : X ⟶ Y) [Mono f] :
    (Subobject.mk f).arrow.ker = f.ker := by
  rw [← Subobject.underlyingIso_hom_comp_eq_mk f, Scheme.Hom.ker_comp_of_isIso]

namespace Scheme.IdealSheafData

/-- Pulling back the subobject presented by a closed subscheme gives the subobject
presented by the pulled-back ideal sheaf. -/
theorem subobject_pullback_mk_subschemeι (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (Subobject.pullback f).obj (Subobject.mk I.subschemeι) =
      Subobject.mk (I.comap f).subschemeι :=
  Subobject.pullback_obj_mk
    (AlgebraicGeometry.isPullback_of_isClosedImmersion (I.comap f).subschemeι I.subschemeι
      (subschemeMap _ _ f (I.le_map_comap f)) f (by simp) (by simp [ker_subschemeι])).flip

/-- An ideal sheaf is determined by the subobject that its closed subscheme presents. -/
theorem subobject_mk_subschemeι_inj {I J : X.IdealSheafData} :
    Subobject.mk I.subschemeι = Subobject.mk J.subschemeι ↔ I = J := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  simpa only [Scheme.Hom.ker_subobject_mk_arrow, ker_subschemeι] using
    congrArg (fun Z : Subobject X ↦ Z.arrow.ker) h

end Scheme.IdealSheafData

end AlgebraicGeometry

namespace Stacks.Groupoids

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- A closed subscheme of the objects of a groupoid scheme is invariant as an ideal sheaf
exactly when the closed immersion it presents is an invariant monomorphism. -/
theorem isInvariantClosedSubscheme_iff_isInvariantMonomorphism
    (Z : G.objects.left.IdealSheafData) :
    IsInvariantClosedSubscheme G Z ↔ IsInvariantMonomorphism G Z.subschemeι := by
  rw [IsInvariantMonomorphism, Scheme.IdealSheafData.subobject_pullback_mk_subschemeι,
    Scheme.IdealSheafData.subobject_pullback_mk_subschemeι,
    Scheme.IdealSheafData.subobject_mk_subschemeι_inj]

/-- The whole object scheme is an invariant subobject. -/
theorem isInvariantMonomorphism_id : IsInvariantMonomorphism G (𝟙 G.objects.left) := by
  rw [IsInvariantMonomorphism, Subobject.mk_eq_top_of_isIso, Subobject.pullback_top,
    Subobject.pullback_top]

end Stacks.Groupoids

end
