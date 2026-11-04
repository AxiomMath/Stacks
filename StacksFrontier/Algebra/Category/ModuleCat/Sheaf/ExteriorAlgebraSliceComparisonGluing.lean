module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraDescentOpenSubspace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraIdentityGenerator

/-!
# Gluing the comparison out of an exterior algebra from a comparison morphism over each member
of a cover

`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_desc_app_of_coversTop` glues the
invertibility of the comparison `A ⟶ B` out of an exterior algebra from two local hypotheses:
the restriction of the *source* to the slice site at each member of a cover is again an exterior
algebra (`hAV`), and so is the restriction of the *target* (`hBV`). The second of these is a
universal property of `B|_{V i}`, and a universal property is the one thing that does **not**
cross a change of presentation of the site for free: it quantifies over all sheaves of graded
algebras there, and a functor of sites says nothing about those test objects unless it is an
equivalence on graded algebras (see the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedSitePushforward.lean`).

This file weakens that hypothesis to one that *is* a statement about morphisms, and therefore
does cross: it asks only for **some** homomorphism `A|_{V i} ⟶ B|_{V i}` of sheaves of graded
algebras which is an isomorphism in every degree and carries the restricted generator of `A` to
the restricted generator of `B`. Invertibility of a morphism present on both sides crosses any
presentation of the site under which the two are equivalent — that is
`Stacks.SheafOfModules.isIso_openSubspaceUnitalHom_app_iff` for an open of a ringed space — so a
local statement proved on a restricted ringed space can be fed to the gluing in this form.

The two hypotheses are in fact equivalent, and the file records both directions: a comparison
morphism is produced from `hBV` by
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isUniversal` and `pieceIso`, and conversely the
comparison morphism is identified with the local `desc` by uniqueness, which is how the weaker
hypothesis suffices.

## Main results

* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_desc_app_of_coversTop_of_hom`: **the
  gluing primitive at a comparison morphism.** Every degree of the comparison `A ⟶ B` is an
  isomorphism as soon as, over each member of a covering family, the restricted source is again
  an exterior algebra and some degreewise invertible homomorphism of the restrictions carries
  one restricted generator to the other.
* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.unitalHom_over_of_isExteriorAlgebra`: such a
  homomorphism exists as soon as the restricted target is again an exterior algebra, so the
  hypothesis above is weaker than `hBV`.
* `SheafOfModules.GradedAlgebra.isExteriorAlgebra_id_over_descend` and
  `Stacks.SheafOfModules.isExteriorAlgebra_id_sitePushforward_descend`: the two links of a
  descended algebra's presentation chain at the identity generator — restriction to a slice site
  and the interchange of descent with the passage to an open subspace — as single applications
  of `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.id_of_degreewiseIso`.
* `SheafOfModules.GradedAlgebra.smul_over_eq_zero`: the annihilation hypothesis that descent
  over a slice site consumes, read off the global one.
* `Stacks.SheafOfModules.isExteriorAlgebra_id_descend_of_openSubspace` and
  `Stacks.SheafOfModules.isExteriorAlgebra_id_over_descend_of_openSubspace`: **the whole passage
  between the open subspace, where a local computation lives, and the slice site, over which
  the gluing runs**, for a descended sheaf of graded algebras — the second for an algebra and a
  quotient formed globally on `X`, asking only for the global annihilation hypothesis.

## Implementation notes

**Why the comparison-morphism form is the useful one.** A chain of presentations of one sheaf of
graded algebras — restrict to a slice site, read the slice site as an open subspace, interchange
that reading with a descent along a quotient of the structure sheaf, replace the complex whose
composition product the algebra is by another model of it — is a chain of homomorphisms each
invertible in every degree. Transporting a *universal property* along such a chain is
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.id_ofDegreewiseIso` at each link that stays on
one site, and at a link that changes the site it is a separate statement, now available:
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.id_of_sitePushforward` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedSitePushforwardEquivalence.lean`, which asks
for fullness and faithfulness of the pushforward on unital homomorphisms and essential
surjectivity of the functor of sites, and for the slice site read as an open subspace gets all
three from the equivalence. Transporting the *invertibility* of a morphism along the same chain
needs no universal property anywhere, which is why the comparison-morphism form of the gluing
remains the cheaper hypothesis even now that the universal property does cross.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe t a v u

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {M : SheafOfModules.{a} R} {A B : GradedAlgebra.{t, a} R}

/-- **The comparison homomorphism over a member of the cover, from the universal property of the
restricted target.** If the restrictions of `A` and of `B` to the slice site at `U` are both
exterior algebras of `M|_U` on the restricted generators, the canonical comparison between them
is a homomorphism of sheaves of graded algebras, invertible in every degree, carrying one
restricted generator to the other.

This is what makes the hypothesis of
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_desc_app_of_coversTop_of_hom` weaker than
the `hBV` of `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_desc_app_of_coversTop`. -/
theorem IsExteriorAlgebra.unitalHom_over_of_isExteriorAlgebra {ι : M ⟶ A.piece 1}
    {κ : M ⟶ B.piece 1} (hκ : SquareZero κ) (U : C)
    (hAU : IsExteriorAlgebra (A.over U) (genOver ι U))
    (hBU : IsExteriorAlgebra (B.over U) (genOver κ U)) :
    ∃ w : UnitalHom (A.over U) (B.over U),
      (∀ n : ℤ, IsIso (w.app n)) ∧ genOver ι U ≫ w.app 1 = genOver κ U :=
  ⟨hAU.desc (B.over U) (genOver κ U) (hκ.over U),
    fun n => (hAU.isUniversal.pieceIso hBU.isUniversal n).isIso_hom,
    hAU.desc_extends (B.over U) (genOver κ U) (hκ.over U)⟩

/-- **The comparison out of an exterior algebra is an isomorphism in every degree as soon as it
is matched locally by a degreewise invertible homomorphism.** Let `A` with `ι` be the exterior
algebra of `M`, let `κ : M ⟶ B.piece 1` be a square-zero degree-one generator and let `{V i}` be
a family of objects covering the final object. Suppose that for each `i` the restriction of `A`
to the slice site at `V i` is again an exterior algebra of `M|_{V i}` on the restricted
generator, and that some homomorphism `w i : A|_{V i} ⟶ B|_{V i}` of sheaves of graded algebras
is an isomorphism in every degree and carries `ι|_{V i}` to `κ|_{V i}`. Then every degree of the
comparison `A ⟶ B` extending `κ` is an isomorphism.

No universal property of `B|_{V i}` is used. The restriction of the comparison to the slice at
`V i` is the comparison of the restrictions
(`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.desc_over`), which is `w i` by uniqueness in
the universal property of `A|_{V i}`; and restriction to the members of a covering family is
jointly conservative on sheaves of modules. -/
theorem IsExteriorAlgebra.isIso_desc_app_of_coversTop_of_hom {ι : M ⟶ A.piece 1}
    (hA : IsExteriorAlgebra A ι) (κ : M ⟶ B.piece 1) (hκ : SquareZero κ)
    {I : Type*} {V : I → C} (hV : J.CoversTop V)
    (hAV : ∀ i, IsExteriorAlgebra (A.over (V i)) (genOver ι (V i)))
    (w : ∀ i, UnitalHom (A.over (V i)) (B.over (V i)))
    (hw : ∀ (i : I) (n : ℤ), IsIso ((w i).app n))
    (hwgen : ∀ i, genOver ι (V i) ≫ (w i).app 1 = genOver κ (V i)) (n : ℤ) :
    IsIso ((hA.desc B κ hκ).app n) := by
  refine Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map hV _ fun i => ?_
  have h : _root_.SheafOfModules.Hom.over ((hA.desc B κ hκ).app n) (V i) = (w i).app n :=
    congrArg (fun g : UnitalHom (A.over (V i)) (B.over (V i)) => g.app n)
      ((hA.desc_over (hAV i) κ hκ).trans
        ((hAV i).desc_unique (B.over (V i)) (genOver κ (V i)) (hκ.over (V i)) (hwgen i)).symm)
  rw [show (_root_.SheafOfModules.overFunctor.{a} R (V i)).map ((hA.desc B κ hκ).app n) =
    (w i).app n from h]
  exact hw i n

end SheafOfModules.GradedAlgebra

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{t}}
  (α : R ⟶ R') [Presheaf.IsLocallySurjective J α.hom] (U : C) (A : GradedAlgebra.{t, t} R)
  (hA : ∀ (n : ℤ) (X : Cᵒᵖ) (b : R.obj.obj X), b ∈ RingHom.ker (α.hom.app X).hom →
    ∀ m : (A.piece n).val.obj X, b • m = 0)

omit [Presheaf.IsLocallySurjective J α.hom] in
include hA in
/-- **The annihilation hypothesis descent over a slice site consumes, read off the global
one.** A section of the restricted ring sheaf over an object of `Opens X / U` is a section of the
ring sheaf over its underlying object, the restricted quotient map is the quotient map there, and
the restricted algebra has the same sections, so the two statements are the same statement. -/
theorem smul_over_eq_zero (n : ℤ) (V : (Over U)ᵒᵖ) (b : (R.over U).obj.obj V)
    (hb : b ∈ RingHom.ker ((overRingHom α U).hom.app V).hom)
    (m : ((A.over U).piece n).val.obj V) : b • m = 0 :=
  hA n (op V.unop.left) b hb m

variable (hA' : ∀ (n : ℤ) (V : (Over U)ᵒᵖ) (b : (R.over U).obj.obj V),
  b ∈ RingHom.ker ((overRingHom α U).hom.app V).hom →
  ∀ m : ((A.over U).piece n).val.obj V, b • m = 0)

/-- **The restriction to a slice site of a descended sheaf of graded algebras is the exterior
algebra of its own degree-one piece as soon as the descent of the restriction is.** The direction
a local-to-global argument uses: the comparison map whose invertibility is at stake is built in
the restriction of the descent, while a statement proved over `U` produces the universal
property for the descent of the restriction.

One application of `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.id_of_degreewiseIso` to
`SheafOfModules.GradedAlgebra.descendOverHom`; no generator has to be tracked, both statements
being at the identity. -/
theorem isExteriorAlgebra_id_over_descend
    (h : IsExteriorAlgebra (descend (overRingHom α U) (A.over U) hA')
      (𝟙 ((descend (overRingHom α U) (A.over U) hA').piece 1))) :
    IsExteriorAlgebra ((descend α A hA).over U)
      (𝟙 (((descend α A hA).over U).piece 1)) :=
  h.id_of_degreewiseIso (descendOverHom α U A hA hA')

end SheafOfModules.GradedAlgebra

namespace Stacks.SheafOfModules

open TopologicalSpace AlgebraicGeometry RingedSpaceModuleAdjunction
open _root_.SheafOfModules.GradedAlgebra

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  {R' : Sheaf ((Opens.grothendieckTopology X.carrier).over U) RingCat.{u}}
  (α : (structureSheafRing X).over U ⟶ R')
  [Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X.carrier).over U) α.hom]
  (A : _root_.SheafOfModules.GradedAlgebra.{u, u} ((structureSheafRing X).over U))
  (hA : ∀ (n : ℤ) (V : (Over U)ᵒᵖ) (b : ((structureSheafRing X).over U).obj.obj V),
    b ∈ RingHom.ker (α.hom.app V).hom → ∀ m : (A.piece n).val.obj V, b • m = 0)

include hA in
/-- **The open-subspace reading of a descended sheaf of graded algebras is the exterior algebra
of its own degree-one piece as soon as the descent of the open-subspace reading is.** The
interchange of descent with the passage from the slice site to the open subspace, at the identity
generator: one application of
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.id_of_degreewiseIso` to
`Stacks.SheafOfModules.descendOpenSubspaceHom`.

Both sides live on the open subspace, so this link stays on one site and the universal property
crosses it. -/
theorem isExteriorAlgebra_id_sitePushforward_descend
    (h : IsExteriorAlgebra (_root_.SheafOfModules.GradedAlgebra.descend
        (openSubspaceRingHom U α) (openSubspaceGradedAlgebra U A)
        (smul_openSubspaceGradedAlgebra_eq_zero U α A hA))
      (𝟙 ((_root_.SheafOfModules.GradedAlgebra.descend (openSubspaceRingHom U α)
        (openSubspaceGradedAlgebra U A)
        (smul_openSubspaceGradedAlgebra_eq_zero U α A hA)).piece 1))) :
    IsExteriorAlgebra (_root_.SheafOfModules.GradedAlgebra.pushforward
        (𝟙 (openSubspaceRingSheaf U (R' := R')))
        (_root_.SheafOfModules.GradedAlgebra.descend α A hA))
      (𝟙 ((_root_.SheafOfModules.GradedAlgebra.pushforward
        (𝟙 (openSubspaceRingSheaf U (R' := R')))
        (_root_.SheafOfModules.GradedAlgebra.descend α A hA)).piece 1)) :=
  h.id_of_degreewiseIso (descendOpenSubspaceHom U α A hA)

include hA in
/-- **The descent presentation of a sheaf of graded algebras crosses from the open subspace to
the slice site.** A sheaf of graded algebras on the slice site over `U`, descended along a
quotient of the slice structure sheaf, is the exterior algebra of its own degree-one piece as
soon as the descent of its open-subspace reading, along the open-subspace reading of that
quotient, is.

The two links of the chain of presentations which the slice site and the open subspace are
separated by, in one statement: the interchange of descent with the passage to the open subspace
(`Stacks.SheafOfModules.isExteriorAlgebra_id_sitePushforward_descend`, a degreewise isomorphism
on one site), followed by the passage itself
(`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.id_of_sitePushforward`, which changes the site
and is the one link a degreewise isomorphism does not carry a universal property across). -/
theorem isExteriorAlgebra_id_descend_of_openSubspace
    (h : IsExteriorAlgebra (_root_.SheafOfModules.GradedAlgebra.descend
        (openSubspaceRingHom U α) (openSubspaceGradedAlgebra U A)
        (smul_openSubspaceGradedAlgebra_eq_zero U α A hA))
      (𝟙 ((_root_.SheafOfModules.GradedAlgebra.descend (openSubspaceRingHom U α)
        (openSubspaceGradedAlgebra U A)
        (smul_openSubspaceGradedAlgebra_eq_zero U α A hA)).piece 1))) :
    IsExteriorAlgebra (_root_.SheafOfModules.GradedAlgebra.descend α A hA)
      (𝟙 ((_root_.SheafOfModules.GradedAlgebra.descend α A hA).piece 1)) :=
  IsExteriorAlgebra.id_of_sitePushforward _
    (isExteriorAlgebra_id_sitePushforward_descend U α A hA h)

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules

open TopologicalSpace AlgebraicGeometry RingedSpaceModuleAdjunction
open _root_.SheafOfModules.GradedAlgebra

variable {X : RingedSpace.{u, u}}
  {R' : Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u}} (α : structureSheafRing X ⟶ R')
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) α.hom]
  (U : Opens X.carrier) (A : _root_.SheafOfModules.GradedAlgebra.{u, u} (structureSheafRing X))
  (hA : ∀ (n : ℤ) (W : (Opens X.carrier)ᵒᵖ) (b : (structureSheafRing X).obj.obj W),
    b ∈ RingHom.ker (α.hom.app W).hom → ∀ m : (A.piece n).val.obj W, b • m = 0)

include hA in
/-- **The whole passage between the open subspace and the slice site, for a globally descended
sheaf of graded algebras, in one statement.** A sheaf of graded algebras on `X` descended along
a quotient of the structure sheaf is, after restriction to the slice site at `U`, the exterior
algebra of its own degree-one piece as soon as the corresponding algebra on the open subspace
`U` is.

This is the composite of the three links of the chain of presentations that lie between the
algebra the comparison map of [Stacks, Tag 0BQY] is built in and the algebra a local
computation on `X|_U` produces: restriction of the descent to the slice site
(`SheafOfModules.GradedAlgebra.isExteriorAlgebra_id_over_descend`), the interchange of descent
with the passage to the open subspace, and that passage itself
(`Stacks.SheafOfModules.isExteriorAlgebra_id_descend_of_openSubspace`). The only annihilation
hypothesis asked for is the global one, the slice one being
`SheafOfModules.GradedAlgebra.smul_over_eq_zero`. -/
theorem isExteriorAlgebra_id_over_descend_of_openSubspace
    (h : IsExteriorAlgebra (_root_.SheafOfModules.GradedAlgebra.descend
        (openSubspaceRingHom U (overRingHom α U))
        (openSubspaceGradedAlgebra U (A.over U))
        (smul_openSubspaceGradedAlgebra_eq_zero U (overRingHom α U) (A.over U)
          (smul_over_eq_zero α U A hA)))
      (𝟙 ((_root_.SheafOfModules.GradedAlgebra.descend
        (openSubspaceRingHom U (overRingHom α U))
        (openSubspaceGradedAlgebra U (A.over U))
        (smul_openSubspaceGradedAlgebra_eq_zero U (overRingHom α U) (A.over U)
          (smul_over_eq_zero α U A hA))).piece 1))) :
    IsExteriorAlgebra ((_root_.SheafOfModules.GradedAlgebra.descend α A hA).over U)
      (𝟙 (((_root_.SheafOfModules.GradedAlgebra.descend α A hA).over U).piece 1)) :=
  isExteriorAlgebra_id_over_descend α U A hA (smul_over_eq_zero α U A hA)
    (isExteriorAlgebra_id_descend_of_openSubspace U (overRingHom α U) (A.over U)
      (smul_over_eq_zero α U A hA) h)

end Stacks.SheafOfModules

end
