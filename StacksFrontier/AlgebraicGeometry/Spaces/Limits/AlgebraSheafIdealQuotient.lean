module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAlgebraColimits
public import StacksFrontier.CategoryTheory.Sites.Modules.QuotientRingSheaf

/-!
# Quotients of an algebra sheaf on an algebraic space by a sheaf of ideals

Let `S` be a scheme, `F` an algebraic space over `S` and `A` a sheaf of commutative
`𝒪_F`-algebras in the sense of `AlgebraicGeometry.Space.AlgebraSheaf`, with sections in the
universe of the schemes.  For a sheaf of ideals `I` of the underlying sheaf of rings of `A`
this file constructs `A/I` as an algebra sheaf on `F`, together with the surjection
`A ⟶ A/I`, the comparison `A/I ⟶ A/I'` attached to an inclusion `I ⊆ I'`, and the functor
`I ↦ A/I` on any preorder of sheaves of ideals.

This is the object `𝒜_{i,j} = ℬ_i/ℐ_{i,j}` of the construction of [Stacks, Tag 082A], which
that construction needs at the level of algebraic spaces: the quotient of an
algebra sheaf by an ideal is otherwise available in the library only for *schemes*, as
`Stacks.FPAlgebraSheaf.quotientAlgebra`, which lives in
`AlgebraicGeometry.Scheme.QuasicoherentAlgebra` and is built from
`AlgebraicGeometry.Scheme.IdealSheafData` and the closed subscheme it cuts out.

## Main definitions

* `AlgebraicGeometry.Space.AlgebraSheaf.idealQuotient`: **`A/I`, the quotient of an algebra
  sheaf on an algebraic space by a sheaf of ideals of its underlying sheaf of rings**, as an
  algebra sheaf on the same algebraic space.
* `AlgebraicGeometry.Space.AlgebraSheaf.toIdealQuotient`: the quotient morphism `A ⟶ A/I`.
* `AlgebraicGeometry.Space.AlgebraSheaf.idealQuotientMapOfLE`: the comparison `A/I ⟶ A/I'`
  attached to an inclusion `I ⊆ I'` of sheaves of ideals.
* `AlgebraicGeometry.Space.AlgebraSheaf.idealQuotientFunctor`: **the functor `I ↦ A/I`** on a
  preorder of sheaves of ideals, which is the shape the directed system of [Stacks, Tag 082A]
  takes once its index is in hand.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.toIdealQuotient_comp_idealQuotientMapOfLE`: the
  quotient morphisms are compatible with the comparisons, so the quotient morphisms assemble
  into a cocone under `A` over any preorder of sheaves of ideals
  (`AlgebraicGeometry.Space.AlgebraSheaf.idealQuotientCocone`).
* `AlgebraicGeometry.Space.AlgebraSheaf.idealQuotientMapOfLE_comp` and
  `idealQuotientMapOfLE_refl`: functoriality of the comparison in the inclusion.

## Implementation notes

The quotient presheaf `U ↦ A(U)/I(U)` is not a sheaf -- a section of the quotient need only
locally come from a section of `A` -- so the quotient has to be sheafified, and the
construction therefore needs sheafification of `CommRingCat`-valued presheaves on the small
étale site.  That is the hypothesis `HasWeakSheafify J CommRingCat` of
`Stacks.Sites.quotientRingSheaf`, and on the small étale site of an algebraic space it
is
*available*, not carried: `AlgebraicGeometry.Space.hasWeakSheafify_commRingCat_smallEtale`
below is `inferInstance`.  The same holds for the compatibility of the forgetful functor
`CommRingCat ⥤ RingCat` with the sheaf condition, which the library carries as the instance
`AlgebraicGeometry.Space.hasSheafCompose_smallEtale_forget₂_ringCat` and which is what makes
`Stacks.Sites.IdealSubsheaf` available for the sheaf of rings underlying an algebra sheaf.

The sections of `A` are taken in the universe `u` of the schemes rather than in the
independent universe `m` of `AlgebraicGeometry.Space.AlgebraSheaf`.  This is not a convenience:
`Stacks.Sites.IdealSubsheaf` is a submodule of the unit sheaf of modules over the sheaf of
rings, so the ideal's sections live in the same universe as the ring's, and the algebra
structure of the quotient is produced by `AlgebraicGeometry.Space.AlgebraSheaf.ofHom`, which
reads the structure-algebra maps off a morphism of sheaves of rings out of the structure sheaf
and so exists only in the single-universe case.

Nothing here asserts quasi-coherence or finite presentation of `A/I`.  Both are properties of
the sections of `A/I` over the affine étale charts, and the sections of a sheafification are
not the sections of the presheaf; see the module documentation of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotientKernel` for what is known
about those sections and for what identifying them would still take.  The *kernel* of the
quotient morphism is identified there: it is exactly `I`, over every object of the site.

## References

* [Stacks Project, Tag 082A](https://stacks.math.columbia.edu/tag/082A)
* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### The two sheafification inputs, on the small étale site -/

/-- Presheaves of commutative rings on the small étale site of an algebraic space admit
sheafification.  This is the hypothesis `HasWeakSheafify J CommRingCat` of
`Stacks.Sites.quotientRingSheaf`, and it is *available* here rather than carried. -/
theorem hasWeakSheafify_commRingCat_smallEtale :
    HasWeakSheafify (SmallEtale.topology B S hS F) CommRingCat.{u} :=
  inferInstance

namespace AlgebraSheaf

variable {B S hS F hF}

/-- Sheaves of ideals of the sheaf of commutative rings underlying an algebra sheaf on an
algebraic space. -/
abbrev IdealSheaf (A : AlgebraSheaf.{u, u} B S hS F hF) :=
  Stacks.Sites.IdealSubsheaf.{u, u + 1, u} A.right

/-! ### The quotient `A/I` -/

/-- **`A/I`, the quotient of an algebra sheaf on an algebraic space by a sheaf of ideals of its
underlying sheaf of rings**, as an algebra sheaf on the same algebraic space: the sheafified
objectwise quotient, with the structure-algebra map of `A` followed by the quotient morphism. -/
def idealQuotient (A : AlgebraSheaf.{u, u} B S hS F hF) (I : A.IdealSheaf) :
    AlgebraSheaf.{u, u} B S hS F hF :=
  ofHom (A.hom ≫ Stacks.Sites.toQuotientRingSheaf.{u, u + 1, u} I)

/-- The sheaf of rings underlying `A/I` is the quotient of the sheaf of rings underlying `A`. -/
theorem idealQuotient_right (A : AlgebraSheaf.{u, u} B S hS F hF) (I : A.IdealSheaf) :
    (A.idealQuotient I).right = Stacks.Sites.quotientRingSheaf.{u, u + 1, u} I :=
  rfl

/-- The structure-algebra map of `A/I` over an étale chart is the structure-algebra map of `A`
followed by the quotient map on sections. -/
theorem idealQuotient_algebraMap (A : AlgebraSheaf.{u, u} B S hS F hF) (I : A.IdealSheaf)
    (U : (SmallEtale B S hS F)ᵒᵖ) (r : (structureSheaf B S hS F hF).obj.obj U) :
    (A.idealQuotient I).algebraMap U r =
      ((Stacks.Sites.toQuotientRingSheaf.{u, u + 1, u} I).hom.app U).hom (A.algebraMap U r) :=
  rfl

/-- **The quotient morphism `A ⟶ A/I`.**  Its underlying morphism of sheaves of rings is
`Stacks.Sites.toQuotientRingSheaf`, and it is a morphism of *algebra* sheaves because the
structure-algebra map of the quotient is by construction the one of `A` followed by it. -/
def toIdealQuotient (A : AlgebraSheaf.{u, u} B S hS F hF) (I : A.IdealSheaf) :
    A ⟶ A.idealQuotient I where
  right := Stacks.Sites.toQuotientRingSheaf.{u, u + 1, u} I
  comm _ _ := rfl

/-- The underlying morphism of sheaves of rings of `A ⟶ A/I` is the quotient map
`Stacks.Sites.toQuotientRingSheaf I`. -/
@[simp]
theorem toIdealQuotient_right (A : AlgebraSheaf.{u, u} B S hS F hF) (I : A.IdealSheaf) :
    (A.toIdealQuotient I).right = Stacks.Sites.toQuotientRingSheaf.{u, u + 1, u} I :=
  rfl

/-! ### The comparison attached to an inclusion of sheaves of ideals -/

/-- **The comparison `A/I ⟶ A/I'` attached to an inclusion `I ⊆ I'` of sheaves of ideals**, as a
morphism of algebra sheaves. -/
def idealQuotientMapOfLE {A : AlgebraSheaf.{u, u} B S hS F hF} {I I' : A.IdealSheaf}
    (h : I ≤ I') : A.idealQuotient I ⟶ A.idealQuotient I' where
  right := Stacks.Sites.quotientRingSheafMapOfLE.{u, u + 1, u} h
  comm U r :=
    congrArg (fun ψ : A.right ⟶ Stacks.Sites.quotientRingSheaf.{u, u + 1, u} I' =>
        (ψ.hom.app U).hom (A.algebraMap U r))
      (Stacks.Sites.toQuotientRingSheaf_comp_quotientRingSheafMapOfLE.{u, u + 1, u} h)

/-- The underlying morphism of sheaves of rings of the comparison `A/I ⟶ A/I'` is
`Stacks.Sites.quotientRingSheafMapOfLE h`. -/
@[simp]
theorem idealQuotientMapOfLE_right {A : AlgebraSheaf.{u, u} B S hS F hF} {I I' : A.IdealSheaf}
    (h : I ≤ I') :
    (idealQuotientMapOfLE h).right = Stacks.Sites.quotientRingSheafMapOfLE.{u, u + 1, u} h :=
  rfl

/-- **The quotient morphisms are compatible with the comparisons.**  This is what makes the
quotient morphisms the legs of a cocone under `A`. -/
@[simp]
theorem toIdealQuotient_comp_idealQuotientMapOfLE (A : AlgebraSheaf.{u, u} B S hS F hF)
    {I I' : A.IdealSheaf} (h : I ≤ I') :
    A.toIdealQuotient I ≫ idealQuotientMapOfLE h = A.toIdealQuotient I' :=
  Hom.ext (Stacks.Sites.toQuotientRingSheaf_comp_quotientRingSheafMapOfLE.{u, u + 1, u} h)

/-- **The comparisons compose.** -/
theorem idealQuotientMapOfLE_comp {A : AlgebraSheaf.{u, u} B S hS F hF}
    {I I' I'' : A.IdealSheaf} (h : I ≤ I') (h' : I' ≤ I'') :
    idealQuotientMapOfLE h ≫ idealQuotientMapOfLE h' =
      idealQuotientMapOfLE (h.trans h') :=
  Hom.ext (Stacks.Sites.quotientRingSheafMapOfLE_comp.{u, u + 1, u} h h')

/-- **The comparison attached to the identical inclusion is the identity.** -/
theorem idealQuotientMapOfLE_refl {A : AlgebraSheaf.{u, u} B S hS F hF} (I : A.IdealSheaf)
    (h : I ≤ I) : idealQuotientMapOfLE h = 𝟙 (A.idealQuotient I) := by
  refine Hom.ext ?_
  change Stacks.Sites.quotientRingSheafMapOfLE.{u, u + 1, u} h =
    𝟙 (Stacks.Sites.quotientRingSheaf.{u, u + 1, u} I)
  have e : Stacks.Sites.quotientPresheafMapOfLE.{u, u + 1, u} h =
      𝟙 (Stacks.Sites.quotientPresheaf.{u, u + 1, u} I) := by
    ext U : 2
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext a
    rfl
  change (presheafToSheaf (SmallEtale.topology B S hS F) CommRingCat.{u}).map
      (Stacks.Sites.quotientPresheafMapOfLE.{u, u + 1, u} h) = _
  rw [e]
  exact CategoryTheory.Functor.map_id _ _

/-! ### The system of quotients over a preorder of sheaves of ideals -/

/-- **The functor `I ↦ A/I`** on a preorder of sheaves of ideals of the sheaf of rings
underlying `A`.  This is the shape the directed system of [Stacks, Tag 082A] takes once its
index is in hand: the index is a preorder of sheaves of ideals and the member at `I` is the
quotient `A/I`. -/
def idealQuotientFunctor (A : AlgebraSheaf.{u, u} B S hS F hF) {P : Type*} [Preorder P]
    (ι : P → A.IdealSheaf) (hι : ∀ p q : P, p ≤ q → ι p ≤ ι q) :
    P ⥤ AlgebraSheaf.{u, u} B S hS F hF where
  obj p := A.idealQuotient (ι p)
  map {p q} f := idealQuotientMapOfLE (hι p q (leOfHom f))
  map_id p := idealQuotientMapOfLE_refl (ι p) (hι p p (leOfHom (𝟙 p)))
  map_comp {_ _ _} _ _ := (idealQuotientMapOfLE_comp _ _).symm

/-- The functor `I ↦ A/I` sends `p` to the quotient `A/ι p`. -/
@[simp]
theorem idealQuotientFunctor_obj (A : AlgebraSheaf.{u, u} B S hS F hF) {P : Type*} [Preorder P]
    (ι : P → A.IdealSheaf) (hι : ∀ p q : P, p ≤ q → ι p ≤ ι q) (p : P) :
    (A.idealQuotientFunctor ι hι).obj p = A.idealQuotient (ι p) :=
  rfl

/-- The functor `I ↦ A/I` sends `p ≤ q` to the comparison `A/ι p ⟶ A/ι q`. -/
theorem idealQuotientFunctor_map (A : AlgebraSheaf.{u, u} B S hS F hF) {P : Type*} [Preorder P]
    (ι : P → A.IdealSheaf) (hι : ∀ p q : P, p ≤ q → ι p ≤ ι q) {p q : P} (f : p ⟶ q) :
    (A.idealQuotientFunctor ι hι).map f = idealQuotientMapOfLE (hι p q (leOfHom f)) :=
  rfl

/-- **The cocone under `A` of the system of quotients**: the leg at `I` is the quotient
morphism `A ⟶ A/I`, and compatibility is
`AlgebraicGeometry.Space.AlgebraSheaf.toIdealQuotient_comp_idealQuotientMapOfLE`.

The system of [Stacks, Tag 082A] is a system *over* `𝒜`, not under it; this cocone is the
record that every member of the system receives `A`, which is the direction in which the
quotients are canonically comparable. -/
def idealQuotientCocone (A : AlgebraSheaf.{u, u} B S hS F hF) {P : Type*} [Preorder P]
    (ι : P → A.IdealSheaf) (hι : ∀ p q : P, p ≤ q → ι p ≤ ι q) :
    (Functor.const P).obj A ⟶ A.idealQuotientFunctor ι hι where
  app p := A.toIdealQuotient (ι p)
  naturality p q f :=
    (Category.id_comp (A.toIdealQuotient (ι q))).trans
      (toIdealQuotient_comp_idealQuotientMapOfLE A (hι p q (leOfHom f))).symm

end AlgebraSheaf

end AlgebraicGeometry.Space

end
