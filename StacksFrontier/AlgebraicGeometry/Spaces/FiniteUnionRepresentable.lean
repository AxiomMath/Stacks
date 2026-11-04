module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocus

/-!
# A finite union of representable open subspaces is a representable open subspace

`AlgebraicGeometry.Space.isRepresentable_sheafify_iSup` glues a family of representable open
subspaces of an algebraic space over `S` indexed by a type smaller than the cofinality of the
site's cutoff. For a *finite* family the cardinal hypothesis is free, because
`AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff_cof` is a field of the site, and this file
records the resulting unconditional statements — in particular the case of two members, which
is the step the fourth paragraph of Stacks 03XW takes with Tag 03JH: there the union of the
quasi-affine scheme `V'` with the image produced by the induction hypothesis is exhibited as a
quasi-compact scheme.

The union is taken in the complete lattice of subfunctors and then sheafified, exactly as in
`AlgebraicGeometry.Space.isRepresentable_sheafify_iSup`: the object-wise union of two
subfunctors of a sheaf is not a sheaf in general, so it is its sheafification inside the
ambient sheaf which is the open subspace.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_sheafify_iSup_of_finite` and
  `AlgebraicGeometry.Space.isOpenSubspace_sheafify_iSup_of_finite`: the sheafified union of a
  finite nonempty family of representable open subspaces of an algebraic space over `S` is a
  representable open subspace, with no cardinal hypothesis.
* `AlgebraicGeometry.Space.isRepresentable_sheafify_sup` and
  `AlgebraicGeometry.Space.isOpenSubspace_sheafify_sup`: the same for two members, which is the
  shape in which the proof of Stacks 03XW uses it.

## Implementation notes

Nothing here carries a tag. Tag 03JH asserts the existence of a *largest* open subspace which
is a scheme; the statements here are the glueing step its proof rests on, specialised to a
finite family, and `AlgebraicGeometry.Space.isRepresentable_schematicLocus` remains conditional
on a small cofinal family of representable open subspaces.

The two-member family is indexed by `ULift.{u} Bool` so that it lives in `Type u`, which is
what `AlgebraicGeometry.Space.isRepresentable_sheafify_iSup` requires of its index type.

## References

* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03XW](https://stacks.math.columbia.edu/tag/03XW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A finite index type is below the cofinality of the cutoff of a big fppf site, that
cofinality being uncountable. -/
theorem mk_lt_cutoff_ord_cof_of_finite (B : BigFppfSite.{u}) (ι : Type u) [Finite ι] :
    Cardinal.mk ι < B.cutoff.ord.cof :=
  (Cardinal.lt_aleph0_of_finite ι).trans B.aleph0_lt_cutoff_cof

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The sheafified union of a finite nonempty family of representable open subspaces of a sheaf
on the big fppf site of `S` is representable.

This is `AlgebraicGeometry.Space.isRepresentable_sheafify_iSup` with its cardinal hypothesis
discharged: a finite type has cardinality below `Cardinal.aleph0`, which the site keeps below
the cofinality of its cutoff. -/
theorem isRepresentable_sheafify_iSup_of_finite
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {ι : Type u} [Nonempty ι] [Finite ι] (X : ι → Subfunctor F)
    (hXopen : ∀ i, IsOpenImmersion B S hS (X i).ι)
    (hXrep : ∀ i, (X i).toFunctor.IsRepresentable) :
    ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)).toFunctor.IsRepresentable :=
  isRepresentable_sheafify_iSup B S hS hF (mk_lt_cutoff_ord_cof_of_finite B ι) X hXopen hXrep

/-- The sheafified union of a finite nonempty family of representable open subspaces of an
algebraic space over `S` is an open subspace. -/
theorem isOpenSubspace_sheafify_iSup_of_finite
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {ι : Type u} [Nonempty ι] [Finite ι] (X : ι → Subfunctor F)
    (hXopen : ∀ i, IsOpenImmersion B S hS (X i).ι)
    (hXrep : ∀ i, (X i).toFunctor.IsRepresentable) :
    IsOpenSubspace B S hS ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)) :=
  isOpenSubspace_sheafify_iSup B S hS hF (mk_lt_cutoff_ord_cof_of_finite B ι) X hXopen hXrep

/-- The two-member family `{G, H}` of subfunctors, indexed by `ULift.{u} Bool` so as to lie in
`Type u`, has the join `G ⊔ H` for supremum. -/
private theorem iSup_uliftBool_eq_sup (G H : Subfunctor F) :
    (⨆ i : ULift.{u} Bool, bif i.down then G else H) = G ⊔ H :=
  le_antisymm (iSup_le fun i => by rcases i with ⟨b⟩; cases b <;> simp)
    (sup_le (le_iSup_of_le (ULift.up true) (by simp))
      (le_iSup_of_le (ULift.up false) (by simp)))

/-- A property holding for both `G` and `H` holds for every member of the family `{G, H}`
indexed by `ULift.{u} Bool`. -/
private theorem forall_uliftBool_cond {P : Subfunctor F → Prop} {G H : Subfunctor F}
    (hG : P G) (hH : P H) : ∀ i : ULift.{u} Bool, P (bif i.down then G else H) := by
  rintro ⟨_ | _⟩
  exacts [hH, hG]

/-- **The union of two representable open subspaces of an algebraic space over `S` is
representable**, after sheafification.

This is the step the fourth paragraph of the proof of Stacks 03XW takes with Tag 03JH. -/
theorem isRepresentable_sheafify_sup
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) {G H : Subfunctor F}
    (hG : IsOpenImmersion B S hS G.ι) (hH : IsOpenImmersion B S hS H.ι)
    (hGr : G.toFunctor.IsRepresentable) (hHr : H.toFunctor.IsRepresentable) :
    ((G ⊔ H).sheafify (BigFppfOver.topology B S hS)).toFunctor.IsRepresentable := by
  rw [← iSup_uliftBool_eq_sup G H]
  exact isRepresentable_sheafify_iSup_of_finite hF _
    (forall_uliftBool_cond (P := fun K => IsOpenImmersion B S hS K.ι) hG hH)
    (forall_uliftBool_cond (P := fun K => K.toFunctor.IsRepresentable) hGr hHr)

/-- The union of two representable open subspaces of an algebraic space over `S` is an open
subspace, after sheafification. -/
theorem isOpenSubspace_sheafify_sup
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) {G H : Subfunctor F}
    (hG : IsOpenImmersion B S hS G.ι) (hH : IsOpenImmersion B S hS H.ι)
    (hGr : G.toFunctor.IsRepresentable) (hHr : H.toFunctor.IsRepresentable) :
    IsOpenSubspace B S hS ((G ⊔ H).sheafify (BigFppfOver.topology B S hS)) := by
  rw [← iSup_uliftBool_eq_sup G H]
  exact isOpenSubspace_sheafify_iSup_of_finite hF _
    (forall_uliftBool_cond (P := fun K => IsOpenImmersion B S hS K.ι) hG hH)
    (forall_uliftBool_cond (P := fun K => K.toFunctor.IsRepresentable) hGr hHr)

end AlgebraicGeometry.Space

end
