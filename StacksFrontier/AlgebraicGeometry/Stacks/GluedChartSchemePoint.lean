module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCutoff
public import StacksFrontier.AlgebraicGeometry.Stacks.CoproductOneMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.GluedChartFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.GluedChartLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Stacks.OnObjectsSmoothPresentation

/-!
# Algebraicity from a family of charts glued into one scheme-valued point

Let `𝒴` be a category fibred in groupoids over the big fppf site of `S` which is a stack for the
fppf topology and whose diagonal is representable by algebraic spaces, and let
`f i : (Sch/Z i)_{fppf} ⟶ 𝒴`, `i ∈ I`, be a family of scheme-valued points of `𝒴` indexed by a
type of cardinality below the cofinality of the site's size cutoff. The coproduct
`W = ∐ i, Z i` is then an object of the site
(`AlgebraicGeometry.BigFppfSite.contains_sigma_of_lt_cof`),
`AlgebraicGeometry.Stack.exists_stackMap_comp_iso_of_isColimit` glues the family into a single
scheme-valued point `g : (Sch/W)_{fppf} ⟶ 𝒴` restricting to each `f i`, and
`AlgebraicGeometry.Stack.isAlgebraicStack_of_onObjects_schemePoint` turns `g` into algebraicity
of `𝒴` as soon as `g` is limit preserving, formally smooth and surjective on objects.

This is the shape of the proof of **Stacks 06DC** that does not form the stackification: the
source covers `𝒴` by the disjoint union of the loci `𝓗_{d, lci}(𝒳/𝒴)` of Tag 04YD, whose
algebraicity needs Tag 02ZN, whereas the chart assembled here is the coproduct of the *site
objects* underlying the individual charts, and the gluing happens on 1-morphisms rather than on
categories.

## Main definitions

* `AlgebraicGeometry.Stack.IsJointlySurjectiveOnObjects`: a family of 1-morphisms lifts every
  object of `𝒴` over a field object through *some* member — surjectivity on objects of
  **Stacks 06D4** with the member quantified existentially alongside the field extension.

## Main results

* `AlgebraicGeometry.Stack.isSurjectiveOnObjects_of_forall_comp_iso`: a scheme-valued point whose
  restrictions along a family of arrows of the site are 2-isomorphic to a jointly surjective
  family is itself surjective on objects.
  `AlgebraicGeometry.Stack.isSurjectiveOnObjects_of_comp_iso` is its one-member case.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_jointlySurjective_glued_schemePoints`:
  algebraicity of `𝒴` from a jointly surjective family, together with limit preservation and
  formal smoothness on objects of the glued point.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_jointlySurjective_forall_formallySmoothOnObjects`:
  the same with formal smoothness on objects read on every member of the family rather than on the
  glued point.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_jointlySurjective_forall_onObjects`:
  algebraicity of `𝒴` with all three conditions read on the family — joint surjectivity on
  objects, limit preservation and formal smoothness on objects of every member — and nothing
  asked of the glued point.
* `Stack.isAlgebraicStack_of_onObjects_glued_schemePoints`,
  `Stack.isAlgebraicStack_of_glued_schemePoints_of_forall_formallySmoothOnObjects` and
  `Stack.isAlgebraicStack_of_glued_schemePoints_of_forall_onObjects`: those three at a family one
  of whose members is surjective on objects, which is jointly surjective by
  `AlgebraicGeometry.Stack.isJointlySurjectiveOnObjects_of_member`.

## Implementation notes

Surjectivity on objects (**Stacks 06D4**) is the one of the three conditions that passes from the
family to the glued point with no further input, because it is an *existential* statement about
objects of `𝒴`: a lift of an object of `𝒴` through `f i` becomes a lift through `g` after pushing
its object of `(Sch/Z i)_{fppf}` forward along `Over.map` and composing with the component of the
2-isomorphism `𝒴` supplies, which lies over an identity by clause (3) of **Stacks 02XS** and so
does not change the arrow of the site the lift sits over.

That is also why the condition asked of the family is joint surjectivity and not surjectivity of
a single member: the index may vary with the object of `𝒴` being lifted. It has to, for Stacks
06DC — the source covers `𝒴` by the loci `𝓗_{d, lci}(𝒳/𝒴)` of all degrees at once, the degree
produced over a field object varying with the field object
(`AlgebraicGeometry.Stack.FiniteHilbert.ExistsLciQuintupleOverField`), so no single locus covers
`𝒴`.

Joint surjectivity on objects is stated, like `AlgebraicGeometry.Stack.IsSurjectiveOnObjects`
itself, for a family of bare functors to the site rather than for a family of 1-morphisms of
`CategoryTheory.CatFiberedInGroupoids` out of slices of the site: the two categories of each
member and their projections are all that the condition mentions. The members are therefore not
required to be scheme-valued points, which is what the route through **Stacks 06DC** needs —
there the family whose joint surjectivity is proved is the family of loci
`𝓗_{d, lci}(𝒳/𝒴) ⟶ 𝒴` of **Stacks 06DA**, and the scheme-valued points consumed here are
obtained from it only after each locus is covered by a chart. The three theorems of this file
read the predicate at the family of scheme slices, which is the same statement as before the
generalisation.

Limit preservation (**Stacks 06CU**) and formal smoothness on objects (**Stacks 06D0**) are
*universal* over the objects of the source, so neither of them transports to the glued point from
a single member of the family. Both descend from *all* the members.

Formal smoothness on objects descends by
`AlgebraicGeometry.Stack.isFormallySmoothOnObjects_of_isColimit_of_forall`: an affine object of
the site mapping to the coproduct decomposes into finitely many open and closed pieces each of
which lands in one summand, the members' lifting properties apply piece by piece, and the
piecewise solutions glue because `𝒴` is a stack. That reading is
`AlgebraicGeometry.Stack.isAlgebraicStack_of_glued_schemePoints_of_forall_formallySmoothOnObjects`,
which still asks limit preservation of every scheme-valued point of `𝒴` out of the coproduct that
restricts to the family — by the gluing theorem a nonempty collection containing the point the
proof uses.

Limit preservation descends by
`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_isColimit_of_forall`, which trades the
condition for local finite presentation in the sense of **Stacks 03YK** by **Stacks 06CX** and
descends that along the summand inclusions, the base changes of those inclusions covering the
source of a base change of the glued point by open subspaces. Reading all three conditions on the
members is
`AlgebraicGeometry.Stack.isAlgebraicStack_of_glued_schemePoints_of_forall_onObjects`.

## References

* [Stacks Project, Tag 02XS](https://stacks.math.columbia.edu/tag/02XS)
* [Stacks Project, Tag 04YD](https://stacks.math.columbia.edu/tag/04YD)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 06D0](https://stacks.math.columbia.edu/tag/06D0)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 06DC](https://stacks.math.columbia.edu/tag/06DC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u uI uX vX uY vY w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A family of 1-morphisms is jointly surjective on objects.** For a family
`F i : 𝒳 i ⟶ 𝒴` of 1-morphisms of categories over the big fppf site of `S`, this is the
condition that every object of `𝒴` over the spectrum of a field be lifted, after a field
extension, through *some* member of the family. It is
`AlgebraicGeometry.Stack.IsSurjectiveOnObjects` of a single 1-morphism — **Stacks 06D4** — with
the member supplying the lift quantified existentially alongside the extension.

This is the shape in which the proof of **Stacks 06DC** delivers surjectivity: the degree of the
finite locally free subscheme produced over a field object varies with the field object
(`AlgebraicGeometry.Stack.FiniteHilbert.ExistsLciQuintupleOverField`), so no single locus
`𝓗_{d, lci}(𝒳/𝒴)` covers `𝒴` and the family of them covers it only jointly. -/
@[sga "3 XI 3.6" "more general"]
def IsJointlySurjectiveOnObjects
    {I : Type uI} {X : I → Type uX} [∀ i, Category.{vX} (X i)]
    {Y : Type uY} [Category.{vY} Y]
    (pX : ∀ i, X i ⥤ BigFppfOver B S hS) (pY : Y ⥤ BigFppfOver B S hS)
    (F : ∀ i, X i ⥤ Y) : Prop :=
  ∀ U : BigFppfOver B S hS, IsFieldObject B S hS U →
    ∀ y : Y, pY.obj y = U →
      ∃ (i : I) (V : BigFppfOver B S hS), IsFieldObject B S hS V ∧
        ∃ (f : V ⟶ U) (x : X i), (pX i).obj x = V ∧
          ∃ α : (F i).obj x ⟶ y, pY.IsHomLift f α

/-- A family one of whose members is surjective on objects is jointly surjective on objects: the
member that lifts every object of `𝒴` is the same one throughout. -/
theorem isJointlySurjectiveOnObjects_of_member
    {I : Type uI} {X : I → Type uX} [∀ i, Category.{vX} (X i)]
    {Y : Type uY} [Category.{vY} Y]
    (pX : ∀ i, X i ⥤ BigFppfOver B S hS) (pY : Y ⥤ BigFppfOver B S hS)
    (F : ∀ i, X i ⥤ Y) (i₀ : I)
    (hsurj : IsSurjectiveOnObjects B S hS (pX i₀) pY (F i₀)) :
    IsJointlySurjectiveOnObjects B S hS pX pY F := fun U hU y hy =>
  let ⟨V, hV, v, x, hx, α, hα⟩ := hsurj U hU y hy
  ⟨i₀, V, hV, v, x, hx, α, hα⟩

/-- **Surjectivity on objects passes along 2-isomorphisms from a jointly surjective family of
restrictions.** Let `g : (Sch/W)_{fppf} ⟶ 𝒴` be a scheme-valued point of a category fibred in
groupoids over the big fppf site of `S`, let `j i : Z i ⟶ W` be a family of arrows of the site,
and suppose the restriction of `g` along each `j i` is 2-isomorphic to `f i`. If the family `f`
is jointly surjective on objects then `g` is surjective on objects (**Stacks 06D4**).

The lift of an object of `𝒴` that the member `f i` provides, over an object `x` of
`(Sch/Z i)_{fppf}` and an arrow of the site out of a field spectrum, becomes a lift through `g`
over `Over.map (j i)` applied to `x`: the two have the same underlying scheme, and the component
of the 2-isomorphism at `x` lies over an identity by clause (3) of **Stacks 02XS**, so it does
not change the arrow of the site the lift sits over. -/
theorem isSurjectiveOnObjects_of_forall_comp_iso
    {𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {I : Type uI} {Z : I → BigFppfOver B S hS} {W : BigFppfOver B S hS} (j : ∀ i, Z i ⟶ W)
    (g : schemeFibredCategory B S hS W ⟶ 𝒴)
    (f : ∀ i, schemeFibredCategory B S hS (Z i) ⟶ 𝒴)
    (e : ∀ i, schemeFibredCategoryMap B S hS (j i) ≫ g ≅ f i)
    (hf : IsJointlySurjectiveOnObjects B S hS
      (fun i => (schemeFibredCategory B S hS (Z i)).val.p) 𝒴.val.p
      (fun i => CatFiberedInGroupoids.homFunctor (f i))) :
    IsSurjectiveOnObjects B S hS (schemeFibredCategory B S hS W).val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor g) := by
  intro U hU y hy
  obtain ⟨i, V, hV, v, x, hx, α, hα⟩ := hf U hU y hy
  refine ⟨V, hV, v, (Over.map (j i)).obj x, hx, (e i).hom.hom.toNatTrans.app x ≫ α, ?_⟩
  have h₀ : 𝒴.val.p.IsHomLift (𝟙 ((schemeFibredCategory B S hS (Z i)).val.p.obj x))
      ((e i).hom.hom.toNatTrans.app x) :=
    CatFiberedInGroupoids.isHomLift_app (e i).hom x
  have h₁ : 𝒴.val.p.IsHomLift v α := hα
  exact @IsHomLift.comp_lift_id_left' _ _ _ _ 𝒴.val.p _ _ _
    ((schemeFibredCategory B S hS (Z i)).val.p.obj x) ((e i).hom.hom.toNatTrans.app x) h₀ _ _ v α
    h₁

/-- **Surjectivity on objects passes along a 2-isomorphism to a restriction.** Let
`g : (Sch/W)_{fppf} ⟶ 𝒴` and `f : (Sch/Z)_{fppf} ⟶ 𝒴` be scheme-valued points of a category
fibred in groupoids over the big fppf site of `S`, let `j : Z ⟶ W`, and suppose the restriction
of `g` along `j` is 2-isomorphic to `f`. If `f` is surjective on objects (**Stacks 06D4**) then
so is `g`.

This is `AlgebraicGeometry.Stack.isSurjectiveOnObjects_of_forall_comp_iso` at the one-member
family, whose joint surjectivity is
`AlgebraicGeometry.Stack.isJointlySurjectiveOnObjects_of_member`. -/
theorem isSurjectiveOnObjects_of_comp_iso
    {𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {Z W : BigFppfOver B S hS} (j : Z ⟶ W)
    (g : schemeFibredCategory B S hS W ⟶ 𝒴) (f : schemeFibredCategory B S hS Z ⟶ 𝒴)
    (e : schemeFibredCategoryMap B S hS j ≫ g ≅ f)
    (hf : IsSurjectiveOnObjects B S hS (schemeFibredCategory B S hS Z).val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor f)) :
    IsSurjectiveOnObjects B S hS (schemeFibredCategory B S hS W).val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor g) :=
  isSurjectiveOnObjects_of_forall_comp_iso B S hS (fun _ : Unit => j) g (fun _ => f)
    (fun _ => e) (isJointlySurjectiveOnObjects_of_member B S hS _ _ _ () hf)

/-- **Algebraicity of a stack in groupoids from a jointly surjective family of scheme-valued
points glued into one.** Let `𝒴` be a category fibred in groupoids over the big fppf site of `S`
which is a stack for the fppf topology and whose diagonal is representable by algebraic spaces.
Let `f i : (Sch/Z i)_{fppf} ⟶ 𝒴` be a family of scheme-valued points indexed by a type of
cardinality below the cofinality of the site's size cutoff which is *jointly* surjective on
objects, and suppose that every scheme-valued point out of the coproduct `∐ i, Z i` whose
restriction to each summand is 2-isomorphic to `f i` is limit preserving and formally smooth on
objects. Then `𝒴` is an algebraic stack.

The coproduct of the `Z i` is an object of the site by
`AlgebraicGeometry.BigFppfSite.contains_sigma_of_lt_cof`, with no uniform bound on the summands;
the family is glued into a single scheme-valued point by
`AlgebraicGeometry.Stack.exists_stackMap_comp_iso_of_isColimit`, which needs of `𝒴` only that it
is fibred in groupoids and a stack; surjectivity on objects of the glued point comes from the
family by `AlgebraicGeometry.Stack.isSurjectiveOnObjects_of_forall_comp_iso`; and
`AlgebraicGeometry.Stack.isAlgebraicStack_of_onObjects_schemePoint` concludes.

Joint surjectivity rather than surjectivity of a single member is what the proof of
**Stacks 06DC** has to work with: the degree of the finite locally free subscheme produced over a
field object varies with the field object, so the family of loci `𝓗_{d, lci}(𝒳/𝒴)` covers `𝒴`
only jointly. -/
theorem isAlgebraicStack_of_jointlySurjective_glued_schemePoints
    {𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒴 : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒴)
    {I : Type u} (hI : Cardinal.mk I < B.cutoff.ord.cof) (Z : I → BigFppfOver B S hS)
    (f : ∀ i, schemeFibredCategory B S hS (Z i) ⟶ 𝒴)
    (hsurj : IsJointlySurjectiveOnObjects B S hS
      (fun i => (schemeFibredCategory B S hS (Z i)).val.p) 𝒴.val.p
      (fun i => CatFiberedInGroupoids.homFunctor (f i)))
    (hrest : ∀ g : schemeFibredCategory B S hS
          (BigFppfOver.sigmaOver B S hS Z
            (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2)) ⟶ 𝒴,
        (∀ i, Nonempty (schemeFibredCategoryMap B S hS
          (BigFppfOver.sigmaOverInj B S hS Z
            (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2) i) ≫ g ≅ f i)) →
        BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS
            (schemeFibredCategory B S hS
              (BigFppfOver.sigmaOver B S hS Z
                (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2))) 𝒴 g ∧
          IsFormallySmoothOnObjects B S hS
            (schemeFibredCategory B S hS
              (BigFppfOver.sigmaOver B S hS Z
                (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2))) 𝒴 g) :
    IsAlgebraicStack.{u, w} B S hS 𝒴.val := by
  obtain ⟨g, hg⟩ := exists_stackMap_comp_iso_of_isColimit B S hS h𝒴 Z _ _
    (BigFppfOver.isColimit_toScheme_sigmaOver B S hS Z
      (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2)) f
  obtain ⟨hlim, hsm⟩ := hrest g hg
  exact isAlgebraicStack_of_onObjects_schemePoint.{u, w} B S hS h𝒴 hdiag _ g hlim hsm
    (isSurjectiveOnObjects_of_forall_comp_iso B S hS _ g f (fun i => (hg i).some) hsurj)

/-- **Algebraicity of a stack in groupoids from a family of scheme-valued points glued into
one.** Let `𝒴` be a category fibred in groupoids over the big fppf site of `S` which is a stack
for the fppf topology and whose diagonal is representable by algebraic spaces. Let
`f i : (Sch/Z i)_{fppf} ⟶ 𝒴` be a family of scheme-valued points indexed by a type of
cardinality below the cofinality of the site's size cutoff, let one member `f i₀` be surjective
on objects, and suppose that every scheme-valued point out of the coproduct `∐ i, Z i` whose
restriction to each summand is 2-isomorphic to `f i` is limit preserving and formally smooth on
objects. Then `𝒴` is an algebraic stack.

The coproduct of the `Z i` is an object of the site by
`AlgebraicGeometry.BigFppfSite.contains_sigma_of_lt_cof`, with no uniform bound on the summands;
the family is glued into a single scheme-valued point by
`AlgebraicGeometry.Stack.exists_stackMap_comp_iso_of_isColimit`, which needs of `𝒴` only that it
is fibred in groupoids and a stack; surjectivity on objects of the glued point comes from the one
surjective member by `AlgebraicGeometry.Stack.isSurjectiveOnObjects_of_comp_iso`; and
`AlgebraicGeometry.Stack.isAlgebraicStack_of_onObjects_schemePoint` concludes. This is the route
through **Stacks 06DC** that forms no stackification.

This is
`AlgebraicGeometry.Stack.isAlgebraicStack_of_jointlySurjective_glued_schemePoints`
at a family one of whose members is surjective on objects. -/
theorem isAlgebraicStack_of_onObjects_glued_schemePoints
    {𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒴 : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒴)
    {I : Type u} (hI : Cardinal.mk I < B.cutoff.ord.cof) (Z : I → BigFppfOver B S hS)
    (f : ∀ i, schemeFibredCategory B S hS (Z i) ⟶ 𝒴) (i₀ : I)
    (hsurj : IsSurjectiveOnObjects B S hS (schemeFibredCategory B S hS (Z i₀)).val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor (f i₀)))
    (hrest : ∀ g : schemeFibredCategory B S hS
          (BigFppfOver.sigmaOver B S hS Z
            (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2)) ⟶ 𝒴,
        (∀ i, Nonempty (schemeFibredCategoryMap B S hS
          (BigFppfOver.sigmaOverInj B S hS Z
            (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2) i) ≫ g ≅ f i)) →
        BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS
            (schemeFibredCategory B S hS
              (BigFppfOver.sigmaOver B S hS Z
                (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2))) 𝒴 g ∧
          IsFormallySmoothOnObjects B S hS
            (schemeFibredCategory B S hS
              (BigFppfOver.sigmaOver B S hS Z
                (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2))) 𝒴 g) :
    IsAlgebraicStack.{u, w} B S hS 𝒴.val :=
  isAlgebraicStack_of_jointlySurjective_glued_schemePoints.{u, w} B S hS h𝒴 hdiag
    hI Z f (isJointlySurjectiveOnObjects_of_member B S hS _ _ _ i₀ hsurj) hrest

/-- **Algebraicity of a stack in groupoids from a jointly surjective family of scheme-valued
points, with formal smoothness read on the members.** Let `𝒴` be a category fibred in groupoids
over the big fppf site of `S` which is a stack for the fppf topology and whose diagonal is
representable by algebraic spaces. Let `f i : (Sch/Z i)_{fppf} ⟶ 𝒴` be a family of scheme-valued
points indexed by a type of cardinality below the cofinality of the site's size cutoff which is
jointly surjective on objects, let every member be formally smooth on objects, and suppose that
every scheme-valued point out of the coproduct `∐ i, Z i` whose restriction to each summand is
2-isomorphic to `f i` is limit preserving on objects. Then `𝒴` is an algebraic stack.

Formal smoothness on objects of the glued point is
`AlgebraicGeometry.Stack.isFormallySmoothOnObjects_of_isColimit_of_forall`, which cuts a
first-order lifting problem over an affine thickening into the pieces of the clopen decomposition
the arrow to the coproduct induces and glues the piecewise solutions; the rest is
`AlgebraicGeometry.Stack.isAlgebraicStack_of_jointlySurjective_glued_schemePoints`. -/
theorem isAlgebraicStack_of_jointlySurjective_forall_formallySmoothOnObjects
    {𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒴 : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒴)
    {I : Type u} (hI : Cardinal.mk I < B.cutoff.ord.cof) (Z : I → BigFppfOver B S hS)
    (f : ∀ i, schemeFibredCategory B S hS (Z i) ⟶ 𝒴)
    (hsurj : IsJointlySurjectiveOnObjects B S hS
      (fun i => (schemeFibredCategory B S hS (Z i)).val.p) 𝒴.val.p
      (fun i => CatFiberedInGroupoids.homFunctor (f i)))
    (hsm : ∀ i, IsFormallySmoothOnObjects B S hS
      (schemeFibredCategory B S hS (Z i)) 𝒴 (f i))
    (hlim : ∀ g : schemeFibredCategory B S hS
          (BigFppfOver.sigmaOver B S hS Z
            (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2)) ⟶ 𝒴,
        (∀ i, Nonempty (schemeFibredCategoryMap B S hS
          (BigFppfOver.sigmaOverInj B S hS Z
            (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2) i) ≫ g ≅ f i)) →
        BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS
            (schemeFibredCategory B S hS
              (BigFppfOver.sigmaOver B S hS Z
                (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2))) 𝒴 g) :
    IsAlgebraicStack.{u, w} B S hS 𝒴.val :=
  isAlgebraicStack_of_jointlySurjective_glued_schemePoints.{u, w} B S hS h𝒴 hdiag
    hI Z f hsurj fun g hg => ⟨hlim g hg,
      isFormallySmoothOnObjects_of_isColimit_of_forall B S hS h𝒴 Z _ _
        (BigFppfOver.isColimit_toScheme_sigmaOver B S hS Z
          (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2)) g f hg hsm⟩

/-- **Algebraicity of a stack in groupoids from a family of scheme-valued points, with formal
smoothness read on the members.** Let `𝒴` be a category fibred in groupoids over the big fppf site
of `S` which is a stack for the fppf topology and whose diagonal is representable by algebraic
spaces. Let `f i : (Sch/Z i)_{fppf} ⟶ 𝒴` be a family of scheme-valued points indexed by a type of
cardinality below the cofinality of the site's size cutoff, let one member `f i₀` be surjective on
objects, let every member be formally smooth on objects, and suppose that every scheme-valued
point out of the coproduct `∐ i, Z i` whose restriction to each summand is 2-isomorphic to `f i`
is limit preserving on objects. Then `𝒴` is an algebraic stack.

Formal smoothness on objects of the glued point is
`AlgebraicGeometry.Stack.isFormallySmoothOnObjects_of_isColimit_of_forall`, which cuts a
first-order lifting problem over an affine thickening into the pieces of the clopen decomposition
the arrow to the coproduct induces and glues the piecewise solutions; the rest is
`AlgebraicGeometry.Stack.isAlgebraicStack_of_onObjects_glued_schemePoints`.

This is
`AlgebraicGeometry.Stack.isAlgebraicStack_of_jointlySurjective_forall_formallySmoothOnObjects`
at a family one of whose members is surjective on objects. -/
theorem isAlgebraicStack_of_glued_schemePoints_of_forall_formallySmoothOnObjects
    {𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒴 : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒴)
    {I : Type u} (hI : Cardinal.mk I < B.cutoff.ord.cof) (Z : I → BigFppfOver B S hS)
    (f : ∀ i, schemeFibredCategory B S hS (Z i) ⟶ 𝒴) (i₀ : I)
    (hsurj : IsSurjectiveOnObjects B S hS (schemeFibredCategory B S hS (Z i₀)).val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor (f i₀)))
    (hsm : ∀ i, IsFormallySmoothOnObjects B S hS
      (schemeFibredCategory B S hS (Z i)) 𝒴 (f i))
    (hlim : ∀ g : schemeFibredCategory B S hS
          (BigFppfOver.sigmaOver B S hS Z
            (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2)) ⟶ 𝒴,
        (∀ i, Nonempty (schemeFibredCategoryMap B S hS
          (BigFppfOver.sigmaOverInj B S hS Z
            (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2) i) ≫ g ≅ f i)) →
        BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS
            (schemeFibredCategory B S hS
              (BigFppfOver.sigmaOver B S hS Z
                (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2))) 𝒴 g) :
    IsAlgebraicStack.{u, w} B S hS 𝒴.val :=
  isAlgebraicStack_of_jointlySurjective_forall_formallySmoothOnObjects.{u, w}
    B S hS h𝒴 hdiag hI Z f (isJointlySurjectiveOnObjects_of_member B S hS _ _ _ i₀ hsurj) hsm hlim

/-- **Algebraicity of a stack in groupoids from a jointly surjective family of scheme-valued
points, with all three conditions read on the members.** Let `𝒴` be a category fibred in
groupoids over the big fppf site of `S` which is a stack for the fppf topology and whose diagonal
is representable by algebraic spaces. Let `f i : (Sch/Z i)_{fppf} ⟶ 𝒴` be a family of
scheme-valued points indexed by a type of cardinality below the cofinality of the site's size
cutoff which is jointly surjective on objects, and let every member be limit preserving on
objects and formally smooth on objects. Then `𝒴` is an algebraic stack.

Nothing is asked of the glued point: surjectivity on objects comes from the family by
`AlgebraicGeometry.Stack.isSurjectiveOnObjects_of_forall_comp_iso`, limit preservation on objects
from all the members by
`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_isColimit_of_forall` — representability of
the glued point by algebraic spaces, which that result needs, being **Stacks 045G** from the
diagonal of `𝒴` — and formal smoothness on objects from all the members by
`AlgebraicGeometry.Stack.isFormallySmoothOnObjects_of_isColimit_of_forall`. This is the route
through **Stacks 06DC** that forms no stackification, with the coproduct of the site objects
underlying the charts in place of the disjoint union of the loci of Tag 04YD, and with the
surjectivity the source actually proves: the loci cover `𝒴` jointly, not one degree at a time. -/
theorem isAlgebraicStack_of_jointlySurjective_forall_onObjects
    {𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒴 : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒴)
    {I : Type u} (hI : Cardinal.mk I < B.cutoff.ord.cof) (Z : I → BigFppfOver B S hS)
    (f : ∀ i, schemeFibredCategory B S hS (Z i) ⟶ 𝒴)
    (hsurj : IsJointlySurjectiveOnObjects B S hS
      (fun i => (schemeFibredCategory B S hS (Z i)).val.p) 𝒴.val.p
      (fun i => CatFiberedInGroupoids.homFunctor (f i)))
    (hlim : ∀ i, BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS
      (schemeFibredCategory B S hS (Z i)) 𝒴 (f i))
    (hsm : ∀ i, IsFormallySmoothOnObjects B S hS
      (schemeFibredCategory B S hS (Z i)) 𝒴 (f i)) :
    IsAlgebraicStack.{u, w} B S hS 𝒴.val :=
  isAlgebraicStack_of_jointlySurjective_forall_formallySmoothOnObjects.{u, w}
    B S hS h𝒴 hdiag hI Z f hsurj hsm fun g hg =>
      isLimitPreservingOnObjects_of_isColimit_of_forall B S hS Z
        (BigFppfOver.sigmaOver B S hS Z
          (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2))
        (fun i => BigFppfOver.sigmaOverInj B S hS Z
          (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2) i)
        (BigFppfOver.isColimit_toScheme_sigmaOver B S hS Z
          (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2)) g
        ((isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒴).mp
          ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒴).mp hdiag)
          (BigFppfOver.sigmaOver B S hS Z
            (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2)) g.hom)
        f hg hlim

/-- **Algebraicity of a stack in groupoids from a family of scheme-valued points, with all three
conditions read on the members.** Let `𝒴` be a category fibred in groupoids over the big fppf
site of `S` which is a stack for the fppf topology and whose diagonal is representable by
algebraic spaces. Let `f i : (Sch/Z i)_{fppf} ⟶ 𝒴` be a family of scheme-valued points indexed
by a type of cardinality below the cofinality of the site's size cutoff, let one member `f i₀` be
surjective on objects, and let every member be limit preserving on objects and formally smooth on
objects. Then `𝒴` is an algebraic stack.

This is
`AlgebraicGeometry.Stack.isAlgebraicStack_of_jointlySurjective_forall_onObjects`
at a family one of whose members is surjective on objects. -/
theorem isAlgebraicStack_of_glued_schemePoints_of_forall_onObjects
    {𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒴 : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒴)
    {I : Type u} (hI : Cardinal.mk I < B.cutoff.ord.cof) (Z : I → BigFppfOver B S hS)
    (f : ∀ i, schemeFibredCategory B S hS (Z i) ⟶ 𝒴) (i₀ : I)
    (hsurj : IsSurjectiveOnObjects B S hS (schemeFibredCategory B S hS (Z i₀)).val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor (f i₀)))
    (hlim : ∀ i, BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS
      (schemeFibredCategory B S hS (Z i)) 𝒴 (f i))
    (hsm : ∀ i, IsFormallySmoothOnObjects B S hS
      (schemeFibredCategory B S hS (Z i)) 𝒴 (f i)) :
    IsAlgebraicStack.{u, w} B S hS 𝒴.val :=
  isAlgebraicStack_of_jointlySurjective_forall_onObjects.{u, w} B S hS h𝒴
    hdiag hI Z f (isJointlySurjectiveOnObjects_of_member B S hS _ _ _ i₀ hsurj) hlim hsm

end AlgebraicGeometry.Stack

end
