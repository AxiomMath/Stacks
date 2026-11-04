module

public import Mathlib.CategoryTheory.Subobject.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SubsheafRange

/-!
# A subobject of a module on a scheme is determined by its local sections

`Stacks.AlgebraicGeometry.Subsheaf.ofMono` reads a monomorphism `a : A ⟶ M` of `𝒪_X`-modules as a
subsheaf of `M`, the family of the sections of `M` in the range of `a`, and
`Stacks.AlgebraicGeometry.Subsheaf.isoOfMono_hom_comp` identifies `A` with that subsheaf over
`M`.  This file draws two consequences.

The first is that the subobject of `M` cut out by `a` is determined by those *sets of sections*:
two monomorphisms with the same sectionwise range are the same subobject.

The second is that the sets of sections need only be compared on a family of opens which refines
every neighbourhood of every point — the affine opens of a scheme, say, or a family much smaller
than a basis, since the family is asked to be closed under nothing at all.  This is because being
in the range of a *monomorphism* is a local condition
(`Stacks.AlgebraicGeometry.Subsheaf.mem_rangeObj_of_local`): the local preimages are unique, so
they glue.

Both are used by the exhaustion half of Stacks 077Z, where two subsheaves of a module on one
scheme of a system are compared over the affine opens lying inside the preimage of an affine open
of another scheme of the system — a family of opens of exactly that kind.

## Main results

* `Stacks.AlgebraicGeometry.Subsheaf.range_mk_arrow_app`: the sections of the arrow of
  `CategoryTheory.Subobject.mk a` are the sections in the range of `a`.
* `Stacks.AlgebraicGeometry.Subsheaf.mk_eq_mk_of_range_eq`: two monomorphisms into `M` whose
  ranges on sections agree over every open cut out the same subobject.
* `Stacks.AlgebraicGeometry.Subsheaf.range_subset_range_of_local`: containment of the ranges on
  sections over every open, from containment over a family of opens refining every
  neighbourhood.
* `Stacks.AlgebraicGeometry.Subsheaf.mk_eq_mk_of_local_range_eq`: **two monomorphisms into `M`
  whose ranges on sections agree over a family of opens refining every neighbourhood cut out the
  same subobject.**

## References

* [Stacks Project, Tag 077Z](https://stacks.math.columbia.edu/tag/077Z)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Subsheaf

variable {X : Scheme.{u}} {M A B : X.Modules}

/-- If `f` factors through `g` via a morphism `e`, the sections in the range of `f` are in the
range of `g`. -/
private theorem range_app_subset_range_app_of_comp_eq {U V : X.Modules} (f : U ⟶ M) (g : V ⟶ M)
    (e : U ⟶ V) (h : e ≫ g = f) (T : X.Opens) : Set.range (f.app T) ⊆ Set.range (g.app T) := by
  rintro _ ⟨z, rfl⟩
  exact ⟨e.app T z, by rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, h]⟩

/-- The sections of the arrow of the subobject cut out by a monomorphism are exactly the sections
in the range of that monomorphism: the two differ by the isomorphism
`CategoryTheory.Subobject.underlyingIso`, which is compatible with both inclusions into the
ambient module. -/
theorem range_mk_arrow_app (a : A ⟶ M) [Mono a] (T : X.Opens) :
    Set.range ((Subobject.mk a).arrow.app T) = Set.range (a.app T) :=
  Set.Subset.antisymm
    (range_app_subset_range_app_of_comp_eq _ _ _ (Subobject.underlyingIso_hom_comp_eq_mk a) T)
    (range_app_subset_range_app_of_comp_eq _ _ _ (Subobject.underlyingIso_arrow a) T)

/-- A monomorphism and the inclusion of its range cut out the same subobject of the target. -/
theorem mk_eq_mk_modι_ofMono (a : A ⟶ M) [Mono a] :
    Subobject.mk a = Subobject.mk (modι (ofMono a)) :=
  Subobject.mk_eq_mk_of_comm _ _ (isoOfMono a) (isoOfMono_hom_comp a)

/-- Two monomorphisms into `M` whose ranges on sections agree over every open have the same
range subsheaf.  The two extensionality lemmas are applied to terms rather than found by
instance search, which does not cross the `def` `AlgebraicGeometry.Scheme.Modules`. -/
theorem ofMono_eq_ofMono_of_range_eq (a : A ⟶ M) (b : B ⟶ M) [Mono a] [Mono b]
    (h : ∀ T : X.Opens, Set.range (a.app T) = Set.range (b.app T)) : ofMono a = ofMono b :=
  SheafOfModules.Submodule.ext
    (PresheafOfModules.Submodule.ext fun T => SetLike.coe_injective (h T.unop))

/-- **Two monomorphisms into `M` whose ranges on sections agree over every open cut out the same
subobject.** -/
theorem mk_eq_mk_of_range_eq (a : A ⟶ M) (b : B ⟶ M) [Mono a] [Mono b]
    (h : ∀ T : X.Opens, Set.range (a.app T) = Set.range (b.app T)) :
    Subobject.mk a = Subobject.mk b := by
  rw [mk_eq_mk_modι_ofMono a, mk_eq_mk_modι_ofMono b, ofMono_eq_ofMono_of_range_eq a b h]

/-- **Containment of the ranges on sections is local.**  Let `P` single out a family of opens of
`X` which refines every neighbourhood of every point.  If the sections of `M` in the range of `a`
over an open of that family are in the range of the monomorphism `b`, then the same holds over
*every* open: a section is in the range of `b` as soon as it is so locally. -/
theorem range_subset_range_of_local (a : A ⟶ M) (b : B ⟶ M) [Mono b] (P : X.Opens → Prop)
    (hP : ∀ (T : X.Opens) (x : X), x ∈ T → ∃ Q : X.Opens, ∃ _ : Q ≤ T, x ∈ Q ∧ P Q)
    (hsub : ∀ Q : X.Opens, P Q → Set.range (a.app Q) ⊆ Set.range (b.app Q)) (T : X.Opens) :
    Set.range (a.app T) ⊆ Set.range (b.app T) := by
  rintro s ⟨w, rfl⟩
  refine mem_rangeObj_of_local b _ fun x hx => ?_
  obtain ⟨Q, hQT, hxQ, hPQ⟩ := hP T x hx
  exact ⟨Q, hQT, hxQ, hsub Q hPQ ⟨res A hQT w, app_res a hQT w⟩⟩

/-- **Two monomorphisms into `M` whose ranges on sections agree over a family of opens refining
every neighbourhood cut out the same subobject.**  The family `P` is asked to be closed under
nothing: containment of the ranges spreads from it to every open because being in the range of a
monomorphism is a local condition. -/
theorem mk_eq_mk_of_local_range_eq (a : A ⟶ M) (b : B ⟶ M) [Mono a] [Mono b]
    (P : X.Opens → Prop)
    (hP : ∀ (T : X.Opens) (x : X), x ∈ T → ∃ Q : X.Opens, ∃ _ : Q ≤ T, x ∈ Q ∧ P Q)
    (heq : ∀ Q : X.Opens, P Q → Set.range (a.app Q) = Set.range (b.app Q)) :
    Subobject.mk a = Subobject.mk b :=
  mk_eq_mk_of_range_eq a b fun T => Set.Subset.antisymm
    (range_subset_range_of_local a b P hP (fun Q hQ => (heq Q hQ).subset) T)
    (range_subset_range_of_local b a P hP (fun Q hQ => (heq Q hQ).superset) T)

end Stacks.AlgebraicGeometry.Subsheaf

end
