module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The tensor, exterior and symmetric algebras of a sheaf of modules on a ringed site

Sheaves of modules on a ringed site are indexed in two equivalent ways. A ringed site
`X : AlgebraicGeometry.RingedSite` carries its structure sheaf of commutative rings `X.O`, and
`AlgebraicGeometry.RingedSite.ringSheaf` forgets commutativity; the sheaves-of-modules
development of chapters 17 and 18 instead indexes by the sheaf of rings
`CategoryTheory.Sheaf.toRingCat X.J X.O` directly, with the site and the sheaf of commutative
rings as separate arguments. `AlgebraicGeometry.RingedSite.ringSheaf_eq_toRingCat` says the two
sheaves of rings are the same, so that a statement about sheaves of modules on a ringed site is
a statement about sheaves of modules over `toRingCat`, with no transport.

That identification is what this file is for. It lets the construction of the three graded
algebras of Section 17.21 —
`SheafOfModules.algebras`, which is indexed by a site together with a
sheaf of commutative rings — be consumed where a *bundled ringed site* is expected, which is
the form Section 18.6 and its consumers use. Nothing here is a new construction: both
declarations below are existing ones at a different spelling of their index.

The second half of the file bridges the two presentations of a unital homomorphism of sheaves
of graded algebras: `SheafOfModules.GradedAlgebra.UnitalHom` carries its three laws flatly,
while a homomorphism is equally a `GradedAlgebra.Hom` together with the single equation
`sectionsMap (f.app 0) A.one = B.one` on global sections. The universal properties of the
tensor, exterior and symmetric algebras are existence-and-uniqueness statements *over* that
type, so changing its presentation changes the proposition, and
`SheafOfModules.GradedAlgebra.existsUnique_unitalHom_iff` is the transport.

## Main definitions

* `SheafOfModules.ringedSiteTensorExteriorSymmetricAlgebras`: the tensor algebra of a sheaf of
  modules on a ringed site, with its exterior and symmetric quotients — the bundle
  `SheafOfModules.TensorExteriorSymmetricAlgebras` at the ringed site's own topology and
  structure sheaf.
* `SheafOfModules.GradedAlgebra.unitalHomEquivSubtype`: a unital homomorphism of sheaves of
  graded algebras is the same thing as a homomorphism whose degree-zero component carries the
  unit to the unit.

## Main results

* `AlgebraicGeometry.RingedSite.ringSheaf_eq_toRingCat`: the sheaf of rings underlying the
  structure sheaf of a ringed site is `CategoryTheory.Sheaf.toRingCat` of that structure sheaf.
  This holds by `rfl`: both are the structure sheaf composed with
  `forget₂ CommRingCat RingCat`, and the sheaf condition is a proposition.
* `SheafOfModules.GradedAlgebra.existsUnique_unitalHom_iff`: the unique-extension statement over
  unital homomorphisms is the unique-extension statement over unit-preserving homomorphisms.

## Implementation notes

`AlgebraicGeometry.RingedSite.ringSheaf` supplies
`GrothendieckTopology.HasSheafCompose (forget₂ CommRingCat RingCat)` itself, from
`RingedSite.hasSheafCompose_forget₂_ringCat`, which holds for every site; `toRingCat` takes it
as an instance. The two declarations below therefore seat it with `letI` in their statements
rather than carrying it as a hypothesis, so that neither adds an assumption the ringed site does
not already satisfy. The two sheafification instances
`GrothendieckTopology.WEqualsLocallyBijective` and `HasWeakSheafify` for `AddCommGrpCat` are
genuine hypotheses — they are what the sheafified tensor product needs and they are not
automatic for an arbitrary site — and they are exactly the ones
`SheafOfModules.algebras` already carries.

`unitalHomEquivSubtype` is assembled from `GradedAlgebra.UnitalHom.ofHom`,
`UnitalHom.toHom` and `UnitalHom.sectionsMap_one`; both round trips are `rfl`, the second
because `toHom_ofHom` is, and the first because the subtype's proof field is a proposition. No
new content is introduced, only the equivalence those three already determine, in the form the
universal properties need in order to be read over either presentation.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe v u w t a

namespace AlgebraicGeometry.RingedSite

/-- The sheaf of rings underlying the structure sheaf of a ringed site is
`CategoryTheory.Sheaf.toRingCat` of that structure sheaf: a sheaf of modules on a ringed site is
a sheaf of modules over `toRingCat X.J X.O`, on the nose. -/
theorem ringSheaf_eq_toRingCat (X : RingedSite.{u, v, w}) :
    letI := X.hasSheafCompose_forget₂_ringCat
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) = toRingCat X.J X.O :=
  rfl

end AlgebraicGeometry.RingedSite

namespace SheafOfModules

/-- **The tensor, exterior and symmetric algebras of a sheaf of modules on a ringed site.**
This is `SheafOfModules.algebras` at the topology and the structure sheaf of `X`, which is the
same bundle by `AlgebraicGeometry.RingedSite.ringSheaf_eq_toRingCat`. -/
noncomputable def ringedSiteTensorExteriorSymmetricAlgebras
    (X : AlgebraicGeometry.RingedSite.{u, v, w})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    letI := X.hasSheafCompose_forget₂_ringCat
    TensorExteriorSymmetricAlgebras X.J F :=
  letI := X.hasSheafCompose_forget₂_ringCat
  algebras X.J F

namespace GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : GradedAlgebra.{t, a} R}

/-- A unital homomorphism of sheaves of graded algebras is the same thing as a homomorphism of
sheaves of graded algebras whose degree-zero component carries the global unit to the global
unit. -/
def unitalHomEquivSubtype :
    UnitalHom A B ≃ {f : Hom A B // SheafOfModules.sectionsMap (f.app 0) A.one = B.one} where
  toFun g := ⟨g.toHom, g.sectionsMap_one⟩
  invFun f := UnitalHom.ofHom f.1 f.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- The homomorphism underlying the image of a unital homomorphism `g` under
`unitalHomEquivSubtype` is `g.toHom`. -/
@[simp]
theorem unitalHomEquivSubtype_apply_coe (g : UnitalHom A B) :
    (unitalHomEquivSubtype g).1 = g.toHom :=
  rfl

/-- The degree-`n` component of the unital homomorphism attached by `unitalHomEquivSubtype.symm`
to a unit-preserving homomorphism `f` is the degree-`n` component of `f`. -/
@[simp]
theorem unitalHomEquivSubtype_symm_app
    (f : {f : Hom A B // SheafOfModules.sectionsMap (f.app 0) A.one = B.one}) (n : ℤ) :
    (unitalHomEquivSubtype.symm f).app n = f.1.app n :=
  rfl

/-- The universal properties of Section 17.21 read over either presentation of a unital
homomorphism: a degree-one generator extends uniquely through a unital homomorphism exactly when
it extends uniquely through a unit-preserving homomorphism. -/
theorem existsUnique_unitalHom_iff {M : SheafOfModules.{a} R} (ι : M ⟶ A.piece 1)
    (κ : M ⟶ B.piece 1) :
    (∃! g : UnitalHom A B, ι ≫ g.app 1 = κ) ↔
      ∃! f : {f : Hom A B // SheafOfModules.sectionsMap (f.app 0) A.one = B.one},
        ι ≫ f.1.app 1 = κ :=
  unitalHomEquivSubtype.existsUnique_congr fun _ => Iff.rfl

end GradedAlgebra

end SheafOfModules

end
