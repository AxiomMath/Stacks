module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSheafMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibreFunctionFieldIso
public import StacksFrontier.CategoryTheory.Sites.SigmaEpiOfLocalImage
import StacksCore.Tactic.StacksAttribute

/-!
# The second map of the fundamental exact sequence of Stacks 03RI, as a morphism of sheaves

Let `X` be an integral normal scheme with generic point `η`, function field `K` and inclusion
`j : Spec K ⟶ X`. The second map of the fundamental exact sequence of Stacks 03RI,
`0 → 𝐆_{m,X} → j_* 𝐆_{m,η} → ⨁_{x ∈ X_0} (i_x)_* 𝐙 → 0`,
is built here as a morphism of abelian sheaves on the small étale site of `X`.

The commuting square the construction rests on is proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSheafMap`. What this file
adds is the assembly: the family of homomorphisms on sections, its naturality packaged as a
`CategoryTheory.NatTrans` on the *affine* étale site — where the Noetherianity hypothesis of
`Stacks.EtaleCohomology.closedPointDivisorSections` is available, by
`Stacks.EtaleCohomology.noetherianSpace_affineEtale_left` — and the transfer of that morphism of
presheaves to the whole small étale site along the cover-dense and full inclusion
`AlgebraicGeometry.Scheme.AffineEtale.Spec`.

## Main definitions

* `Stacks.EtaleCohomology.closedPointDivisorSheaf.sheafSectionOfDirectSum`: a finitely supported
  family of sections of the skyscrapers over an étale `X`-scheme, read as a section of
  `⨁_x (i_x)_* 𝐙` through the summand inclusions of the *sheaf* coproduct.
* `Stacks.EtaleCohomology.closedPointDivisorSheafSection`: the second map on sections over an
  arbitrary étale `X`-scheme with Noetherian space, valued in the sheaf `⨁_x (i_x)_* 𝐙` itself.
* `Stacks.EtaleCohomology.affineEtaleDivisorRestricted`: the same family on the affine étale site,
  as a morphism of presheaves.
* `Stacks.EtaleCohomology.divisorSequenceSecondMap`: **the second map of the fundamental exact
  sequence of Stacks 03RI, as a morphism of abelian sheaves on the small étale site of `X`.**
* `Stacks.EtaleCohomology.divisorSequenceSecondMapOfCurve`: the same for a smooth curve over a
  field, which is the setting of Stacks 03RI and Stacks 03RM.

## Main results

* `Stacks.EtaleCohomology.closedPointDivisorSheafSection_map`: the commuting square, read in the
  sheaf `⨁_x (i_x)_* 𝐙`.
* `Stacks.EtaleCohomology.closedPointDivisorSheafSection_restrict_eq_zero`: the sequence is a
  complex on sections over an arbitrary étale `X`-scheme with Noetherian space.
* `Stacks.EtaleCohomology.whiskerLeft_divisorSequenceSecondMap` and
  `Stacks.EtaleCohomology.divisorSequenceSecondMap_hom_app`: **what pins the morphism down.** The
  second map is *data*, so the mere existence of a morphism of the right type says nothing — the
  zero morphism has that type too. These two record that its restriction to the affine étale site
  is `Stacks.EtaleCohomology.affineEtaleDivisorRestricted`, whose component at an affine étale
  `X`-scheme `W` is, by
  `Stacks.EtaleCohomology.affineEtaleDivisorApp_apply`, the family of orders of vanishing
  `Stacks.EtaleCohomology.closedPointDivisorSheafSection` at `W`.
* `Stacks.EtaleCohomology.divisorSequenceSecondMap_eq_of_whiskerLeft`: **and what makes it the
  unique such morphism.** Restriction along a cover-dense, locally full inclusion is injective on
  morphisms into a sheaf, so the two equations above determine the second map completely.
* `Stacks.EtaleCohomology.epi_divisorSequenceSecondMap_of_forall_imageSieve_ι_mem` and
  `Stacks.EtaleCohomology.epi_divisorSequenceSecondMapOfCurve_of_forall_imageSieve_ι_mem`: **the
  right-hand exactness of the sequence, reduced to one summand at a time.** The second map is an
  epimorphism as soon as every section of every single summand `(i_x)_* 𝐙` is étale locally the
  divisor of a section of `j_* 𝐆_{m,η}`; see the implementation notes.
* `Stacks.EtaleCohomology.epi_divisorSequenceSecondMap_of_forall_imageSieve_ι_mem_affineEtale`,
  and its curve form under the same name with `OfCurve` in place of the first occurrence of
  `divisorSequenceSecondMap`: **the same reduced further to the affine étale site**, which is where
  the component of the second map can be computed at all.
* `Stacks.EtaleCohomology.closedPointDivisorSheaf.sheafSectionOfDirectSum_eq_ι`: **a family of
  sections of the skyscrapers supported at one closed point is the summand inclusion of its one
  member**, which is the shape in which the summand-at-a-time reduction hands the target section
  over.
* `Stacks.EtaleCohomology.exists_etaleGenericFibreOrdOfPoint_eq_and_forall_eq_zero`: **a section of
  `j_* 𝐆_{m,η}` over an integral étale `X`-scheme with a prescribed order of vanishing at a
  codimension-one point and order zero elsewhere on a neighbourhood**, stated in the order of
  vanishing the second map is built from.
* `Stacks.EtaleCohomology.coheight_eq_one_of_etale_of_isCurve` and
  `Stacks.EtaleCohomology.exists_genericFibreOrd_eq_and_forall_ord_eq_zero_of_isCurve`: the
  codimension and the prescribed divisor in the source's own setting, a smooth curve over a field.

## Implementation notes

**What the right-hand exactness needs, and what it does not.** Showing the second map epi looks as
though it needs an arbitrary section of `⨁_x (i_x)_* 𝐙` read étale locally as a finite sum of
sections of the summands — hence the separatedness of the presheaf coproduct that the sheaf
coproduct sheafifies, and the closure of the local image under addition. It does not:
`CategoryTheory.Sheaf.epi_of_forall_imageSieve_ι_mem` tests an epimorphism out of a coproduct on
the summands, so only the sections of a single `(i_x)_* 𝐙` are ever named, and
`CategoryTheory.Presheaf.imageSieve_mem_of_isCoverDense` restricts the objects to be inspected to
the affine étale ones. What that leaves is the local statement at one closed point, whose rational
function with prescribed divisor is
`Stacks.EtaleCohomology.exists_genericFibreOrd_eq_and_forall_ord_eq_zero_of_isCurve`, and the
shrinking that makes that statement applicable.

**What the shrinking has to achieve, and what is available for it.** The prescribed-divisor
statement needs the étale `X`-scheme *integral* and the chosen point of *codimension one*, and the
section of `(i_x)_* 𝐙` to be hit is a locally constant `𝐙`-valued map on the fibre
`U ×_X Spec κ(x)` rather than a single integer. The codimension is free, by
`Stacks.EtaleCohomology.coheight_eq_one_of_etale_of_isCurve`. The fibre becomes a single point —
so that the one integer the prescribed-divisor statement consumes determines the whole section —
exactly when the scheme meets the preimage of `x` once, by
`Stacks.EtaleCohomology.subsingleton_pullback_fromSpecResidueField`; the preimage is discrete,
since an étale morphism is locally quasi-finite, so a shrinking achieving this exists at every
point. Integrality is available on a neighbourhood of every point by
`Stacks.EtaleCohomology.exists_isIntegral_open_of_etale`. What is not yet written down is the
assembly of those three shrinkings into one covering family of affine étale objects, together with
the transport of the section of `(i_x)_* 𝐙` along it: the identification
`Stacks.EtaleCohomology.integerSkyscraperSectionsIsoLocallyConstantMaps` is the component of a
natural isomorphism, so the transport is its naturality, but that naturality is not stated.

**Why the affine étale site.** `Stacks.EtaleCohomology.closedPointDivisorSections` needs the
étale `X`-scheme to have a Noetherian space, and an arbitrary object of `X.Etale` does not: that
category is `MorphismProperty.Over @Etale ⊤ X`, which carries no quasi-compactness cut, and an
infinite disjoint union of copies of `X` is an object of it. The affine étale objects do have
Noetherian spaces, and they are a dense subsite, so
`CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom` transfers the morphism — uniquely. The
local Noetherianity and the Noetherianity of the space of an affine étale object are supplied as
local instances from `Stacks.EtaleCohomology.isLocallyNoetherian_etale_left` and
`Stacks.EtaleCohomology.noetherianSpace_affineEtale_left`.

**Why `Stacks.EtaleCohomology.closedPointDivisorSheafSection` is `irreducible`, and why the
summand inclusions are taken in the sheaf rather than in the presheaf coproduct.** Both are forced
by the same fact: the coproduct of abelian groups is built from
`CategoryTheory.Limits.AddCommGrpCat.getColimitCocone`, which is not exposed across module
boundaries, so a definitional unfolding that reaches it does not terminate. The body of
`closedPointDivisorSheafSection` reaches it, through
`CategoryTheory.Limits.Sigma.ι`; therefore *every* definitional equality decided underneath that
name — even one as small as `Additive.ofMul (Additive.toMul a) = a` — diverges while the name is
reducible. Marking it `irreducible` after its equational lemmas are proved makes the unifier
compare the two sides by congruence instead, which is what the assembly below needs; the three
lemmas that do look inside it are stated and proved before the attribute. For the same reason the
components are built with `CategoryTheory.ConcreteCategory.ofHom` rather than
`AddCommGrpCat.ofHom`: the latter produces a morphism between `AddCommGrpCat.of _` and so asks the
unifier to decide `AddCommGrpCat.of _ = ⨁_x (i_x)_* 𝐙` at the object, which unfolds the colimit.

**Why the presheaf coproduct is not used.** `Stacks.EtaleCohomology.closedPointDivisorSheaf`
`.homOfPresheafHom` builds a morphism into `⨁_x (i_x)_* 𝐙` out of a morphism of presheaves into
the coproduct of the underlying presheaves of the skyscrapers. That route needs the datum at
*every* object of `X.Etale`, where the Noetherianity is unavailable, and it puts a second colimit
in the way. Mapping straight into the sheaf through its own summand inclusions avoids both.

## References

* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the fundamental exact
  sequence, Theorem 59.68.1. The source states it for a smooth curve over an algebraically closed
  field; the second map is built here for an arbitrary integral, normal, locally Noetherian
  scheme.
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM): the vanishing theorem the
  sequence is needed for.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper

/-! ### Sections of the sheaf `⨁_x (i_x)_* 𝐙` from a finitely supported family -/

namespace closedPointDivisorSheaf

/-- **A finitely supported family of sections of the skyscrapers, as a section of the sheaf
`⨁_x (i_x)_* 𝐙`.** The summand inclusions of the *sheaf* coproduct, evaluated at an étale
`X`-scheme `U`, are a family of homomorphisms out of the groups of sections of the summands, so
the universal property of the direct sum turns a finitely supported family into a single section.

This is the analogue of
`Stacks.EtaleCohomology.closedPointDivisorSheaf.presheafCoproductSectionOfDirectSum` with the
coproduct of the underlying presheaves replaced by the sheaf itself. It is not an isomorphism and
is not claimed to be one: a section of a coproduct of sheaves is only locally a finite sum of
sections of the summands. Only this direction is used. -/
def sheafSectionOfDirectSum (X : Scheme.{u}) (U : X.Etale) :
    DirectSum ↥(closedPoints X)
        (fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj.obj (op U)) →+
      (closedPointDivisorSheaf.{u, v} X).obj.obj (op U) :=
  letI : DecidableEq ↥(closedPoints X) := Classical.decEq _
  DirectSum.toAddMonoid fun x ↦ ((ι.{u, v} X x).hom.app (op U)).hom

/-- **The passage from the direct sum of the groups of sections to the sections of the sheaf
`⨁_x (i_x)_* 𝐙` is natural in the étale `X`-scheme.** Restricting the resulting section along a
morphism `g : W ⟶ V` of the small étale site is the same as restricting each member of the family
of sections of the summands first.

Only the summand inclusions are involved, so this is their naturality: they are morphisms of
sheaves, hence of the underlying presheaves, and both composites are homomorphisms out of the
direct sum, so they agree as soon as they agree on each summand. -/
theorem map_comp_sheafSectionOfDirectSum (X : Scheme.{u}) {W V : X.Etale} (g : W ⟶ V) :
    (((closedPointDivisorSheaf.{u, v} X).obj.map g.op).hom).comp
        (sheafSectionOfDirectSum.{u, v} X V) =
      (sheafSectionOfDirectSum.{u, v} X W).comp
        (DirectSum.map fun x : closedPoints X ↦
          ((closedPointSkyscraper.{u, v} X x).obj.map g.op).hom) := by
  let _ : DecidableEq ↥(closedPoints X) := Classical.decEq _
  refine DirectSum.addHom_ext fun x s ↦ ?_
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, sheafSectionOfDirectSum,
    DirectSum.toAddMonoid_of, DirectSum.map_of, sheafSectionOfDirectSum,
    DirectSum.toAddMonoid_of]
  exact (NatTrans.naturality_apply (ι.{u, v} X x).hom g.op s).symm

/-- **A family of sections of the skyscrapers supported at a single closed point is the image of
its one member under the summand inclusion of the sheaf.** If every member away from `x` vanishes,
the section of `⨁_y (i_y)_* 𝐙` the family determines is
`Stacks.EtaleCohomology.closedPointDivisorSheaf.ι` applied to the member at `x`.

This is the single-summand characterisation that the implementation notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorPresheafSections` record
as unstated for the presheaf-coproduct analogue, and for the reason recorded there: naming
`DirectSum.of` in the statement would name a `DecidableEq` instance on the closed points, and that
instance would not be the classical one `DirectSum.toAddMonoid` fixes inside
`Stacks.EtaleCohomology.closedPointDivisorSheaf.sheafSectionOfDirectSum`. Phrasing the support
condition as `∀ y ≠ x, f y = 0` keeps `DirectSum.of` out of the statement, so no instance is named
at all; the proof reinstates the classical one, where the two sides are
`DirectSum.toAddMonoid_of`.

It is what the right-hand exactness of Stacks 03RI consumes: the epimorphism is tested one summand
at a time by `CategoryTheory.Sheaf.epi_of_forall_imageSieve_ι_mem`, so the section to be hit is
the image under a single summand inclusion of a single section of a single `(i_x)_* 𝐙`. -/
theorem sheafSectionOfDirectSum_eq_ι (X : Scheme.{u}) (U : X.Etale) (x : closedPoints X)
    (f : DirectSum ↥(closedPoints X)
      fun y : closedPoints X ↦ (closedPointSkyscraper.{u, v} X y).obj.obj (op U))
    (hf : ∀ y : closedPoints X, y ≠ x → f y = 0) :
    sheafSectionOfDirectSum.{u, v} X U f = ((ι.{u, v} X x).hom.app (op U)).hom (f x) := by
  let _ : DecidableEq ↥(closedPoints X) := Classical.decEq _
  have hfx : f = DirectSum.of _ x (f x) := by
    refine DFinsupp.ext fun y ↦ ?_
    by_cases hy : y = x
    · subst hy
      rw [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ hy]
      exact hf y hy
  rw [hfx, sheafSectionOfDirectSum, DirectSum.toAddMonoid_of, DirectSum.of_eq_same]

end closedPointDivisorSheaf

/-! ### The second map on sections, valued in the sheaf -/

section Section

variable {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsNormal X]

/-- **The second map of the fundamental exact sequence of Stacks 03RI over an arbitrary étale
`X`-scheme with Noetherian space, valued in the sheaf `⨁_x (i_x)_* 𝐙` itself.** This is
`Stacks.EtaleCohomology.closedPointDivisorSections` followed by
`Stacks.EtaleCohomology.closedPointDivisorSheaf.sheafSectionOfDirectSum`.

No irreducibility hypothesis is carried on `U`, which is the generality of the source. -/
@[stacks 03RI "the second map on sections over an étale X-scheme with Noetherian space, valued
in the sheaf ⨁_x i_{x,*} Z, for X integral and normal; no irreducibility is assumed"]
def closedPointDivisorSheafSection (U : X.Etale) [IsLocallyNoetherian U.left]
    [NoetherianSpace U.left] :
    Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) →+
      (closedPointDivisorSheaf.{u, v} X).obj.obj (op U) :=
  (closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, v} X U).comp
    (closedPointDivisorSections.{u, v} U)

/-- **The second map on sections is the family of orders of vanishing, read as a section of the
sheaf `⨁_x (i_x)_* 𝐙`.** This is the equational lemma of
`Stacks.EtaleCohomology.closedPointDivisorSheafSection`, stated before that definition is made
irreducible and so the only way to look inside it afterwards; the right-hand exactness of
Stacks 03RI consumes it together with
`Stacks.EtaleCohomology.closedPointDivisorSheaf.sheafSectionOfDirectSum_eq_ι`. -/
theorem closedPointDivisorSheafSection_apply (U : X.Etale) [IsLocallyNoetherian U.left]
    [NoetherianSpace U.left]
    (a : Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ)) :
    closedPointDivisorSheafSection.{u, v} U a =
      closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, v} X U
        (closedPointDivisorSections.{u, v} U a) :=
  AddMonoidHom.comp_apply _ _ a

/-- **The commuting square that makes the second map of Stacks 03RI a map of presheaves**, read in
the sheaf `⨁_x (i_x)_* 𝐙`: restricting the section attached to a unit on the generic fibre of `V`
along a morphism `φ : U ⟶ V` of the small étale site gives the section attached to the restricted
unit.

It is `Stacks.EtaleCohomology.closedPointDivisorSections_map` together with the naturality of the
passage from the direct sum of the groups of sections to the sections of the sheaf,
`Stacks.EtaleCohomology.closedPointDivisorSheaf.map_comp_sheafSectionOfDirectSum`. Neither object
is assumed irreducible, so this is the square at the generality of the source. -/
@[stacks 03RI "the second map of the sequence is compatible with restriction along a morphism of
étale X-schemes with Noetherian spaces, read in the sheaf ⨁_x i_{x,*} Z, for X integral and
normal; no irreducibility is assumed"]
theorem closedPointDivisorSheafSection_map {U V : X.Etale} [IsLocallyNoetherian U.left]
    [NoetherianSpace U.left] [IsLocallyNoetherian V.left] [NoetherianSpace V.left]
    (φ : U ⟶ V) (a : (Γ(pullback V.hom (genericPointInclusion X), ⊤))ˣ) :
    ((closedPointDivisorSheaf.{u, v} X).obj.map φ.op).hom
        (closedPointDivisorSheafSection.{u, v} V (Additive.ofMul a)) =
      closedPointDivisorSheafSection.{u, v} U (Additive.ofMul (Units.map
        ((smallEtaleBaseChange (genericPointInclusion X)).map
          φ).left.appTop.hom.toMonoidHom a)) :=
  (congrArg (fun ψ : _ →+ _ => ψ (closedPointDivisorSections.{u, v} V (Additive.ofMul a)))
      (closedPointDivisorSheaf.map_comp_sheafSectionOfDirectSum.{u, v} X φ)).trans
    (congrArg (closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, v} X U)
      (closedPointDivisorSections_map.{u, v} φ a))

/-- **An invertible global function on `U` has trivial image under the second map of Stacks 03RI
read in the sheaf `⨁_x (i_x)_* 𝐙`**: the sequence of the source is a complex over an arbitrary
étale `X`-scheme with Noetherian space, with no irreducibility hypothesis. -/
@[stacks 03RI "the sequence is a complex on sections over an étale X-scheme with Noetherian
space, read in the sheaf ⨁_x i_{x,*} Z, for X integral and normal; no irreducibility is assumed"]
theorem closedPointDivisorSheafSection_restrict_eq_zero (U : X.Etale)
    [IsLocallyNoetherian U.left] [NoetherianSpace U.left] (a : (Γ(U.left, ⊤))ˣ) :
    closedPointDivisorSheafSection.{u, v} U (Additive.ofMul (Units.map
      (pullback.fst U.hom (genericPointInclusion X)).appTop.hom.toMonoidHom a)) = 0 :=
  (AddMonoidHom.comp_apply
      (closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, v} X U)
      (closedPointDivisorSections.{u, v} U) _).trans
    ((congrArg (closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, v} X U)
      (closedPointDivisorSections_restrict_eq_zero.{u, v} U a)).trans (map_zero _))

/-- **A section of `j_* 𝐆_{m,η}` over an integral étale `X`-scheme with a prescribed order of
vanishing at a codimension-one point and order zero at every other point of a neighbourhood**, read
through the order of vanishing `Stacks.EtaleCohomology.etaleGenericFibreOrdOfPoint` out of which
the second map of Stacks 03RI is built.

This is `Stacks.EtaleCohomology.exists_genericFibreOrd_eq_and_forall_ord_eq_zero_of_isNormal` with
its conclusion transported along the identification of
`Stacks.EtaleCohomology.etaleGenericFibreOrdOfPoint` at an integral `U` with
`Stacks.EtaleCohomology.genericFibreOrd` at the structure morphism of `U`: that identification is
`Stacks.EtaleCohomology.etaleGenericFibreOrdOfPoint_eq_etaleGenericFibreOrd` followed by the
definition of `Stacks.EtaleCohomology.etaleGenericFibreOrd`, which is why it cannot be stated on
its own — the instances it needs sit at `(𝟭 Scheme).obj U.left`, the source of the structure
morphism of an object of `AlgebraicGeometry.Scheme.Etale`, and instance search does not see
through the identity functor. They are supplied here by hand.

Integrality of `U` is where this falls short of what the right-hand exactness of Stacks 03RI
needs: an arbitrary object of `X.Etale` is only *locally* integral, so the statement applies after
a shrinking that `Stacks.EtaleCohomology.exists_isIntegral_open_of_etale` supplies. -/
theorem exists_etaleGenericFibreOrdOfPoint_eq_and_forall_eq_zero (U : X.Etale)
    [AlgebraicGeometry.IsIntegral U.left] [IsLocallyNoetherian U.left] [NoetherianSpace U.left]
    {y : U.left} (hco : Order.coheight y = 1) (n : ℤ) :
    ∃ (V : U.left.Opens) (a : (Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ),
      y ∈ V ∧ etaleGenericFibreOrdOfPoint U y (Additive.ofMul a) = n ∧
        ∀ z ∈ V, z ≠ y → etaleGenericFibreOrdOfPoint U z (Additive.ofMul a) = 0 := by
  have : Etale U.hom := U.prop
  have : AlgebraicGeometry.IsIntegral ((𝟭 Scheme).obj U.left) :=
    inferInstanceAs (AlgebraicGeometry.IsIntegral U.left)
  have : IsLocallyNoetherian ((𝟭 Scheme).obj U.left) :=
    inferInstanceAs (IsLocallyNoetherian U.left)
  have : NoetherianSpace ((𝟭 Scheme).obj U.left) := inferInstanceAs (NoetherianSpace U.left)
  have hbridge : ∀ (z : U.left)
      (b : Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ)),
      etaleGenericFibreOrdOfPoint U z b = genericFibreOrd (X := X) U.hom z b := fun z b =>
    (etaleGenericFibreOrdOfPoint_eq_etaleGenericFibreOrd U z b).trans rfl
  obtain ⟨V, a, hyV, hy, hz⟩ :=
    exists_genericFibreOrd_eq_and_forall_ord_eq_zero_of_isNormal (X := X) U.hom hco n
  exact ⟨V, a, hyV, (hbridge y _).trans hy, fun z hzV hzy => (hbridge z _).trans (hz z hzV hzy)⟩

end Section

/-- **A point of a scheme étale over a curve has codimension one unless it lies over the generic
point of the curve.** An étale morphism preserves codimension by
`AlgebraicGeometry.coheight_eq_of_etale`, and every point of a curve other than its generic point
has codimension one by `AlgebraicGeometry.IsCurve.coheight_eq_one`.

This discharges the codimension hypothesis of
`Stacks.EtaleCohomology.exists_etaleGenericFibreOrdOfPoint_eq_and_forall_eq_zero` in the setting of
Stacks 03RI, at every point of every étale `X`-scheme over a closed point of the curve. No
smoothness is used: smoothness enters only through the normality that makes the stalk a discrete
valuation ring. -/
theorem coheight_eq_one_of_etale_of_isCurve {k : Type u} [Field k] {X U : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsCurve k g] (q : U ⟶ X) [Etale q] {y : U}
    (hy : q.base y ≠ genericPoint X) :
    Order.coheight y = 1 :=
  (coheight_eq_of_etale q y).symm.trans (IsCurve.coheight_eq_one g hy)

/-- **A section of `j_* 𝐆_{m,η}` over an integral scheme étale over a smooth curve, with a
prescribed divisor on a neighbourhood of a point over a closed point of the curve.** This is
`Stacks.EtaleCohomology.exists_genericFibreOrd_eq_and_forall_ord_eq_zero_of_isNormal` with both of
its hypotheses discharged in the setting of Stacks 03RI: the codimension by
`Stacks.EtaleCohomology.coheight_eq_one_of_etale_of_isCurve` and the normality of the base by
`Stacks.EtaleCohomology.isNormal_of_isCurve_of_smooth`.

This is the local input to the right-hand exactness of Stacks 03RI in the source's own setting,
with no hypothesis left but the integrality of the étale `X`-scheme. -/
theorem exists_genericFibreOrd_eq_and_forall_ord_eq_zero_of_isCurve {k : Type u} [Field k]
    {X U : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g]
    [AlgebraicGeometry.IsIntegral U] [IsLocallyNoetherian U] [NoetherianSpace U] (q : U ⟶ X)
    [Etale q] {y : U} (hy : q.base y ≠ genericPoint X) (n : ℤ) :
    ∃ (V : U.Opens) (a : (Γ(pullback q (genericPointInclusion X), ⊤))ˣ),
      y ∈ V ∧ genericFibreOrd q y (Additive.ofMul a) = n ∧
        ∀ z ∈ V, z ≠ y → genericFibreOrd q z (Additive.ofMul a) = 0 :=
  have : IsNormal X := isNormal_of_isCurve_of_smooth g
  exists_genericFibreOrd_eq_and_forall_ord_eq_zero_of_isNormal q
    (coheight_eq_one_of_etale_of_isCurve g q hy) n

attribute [irreducible] closedPointDivisorSheafSection

/-! ### The morphism of presheaves on the affine étale site -/

section Affine

variable (X : Scheme.{u}) [AlgebraicGeometry.IsIntegral X] [IsNormal X] [IsLocallyNoetherian X]

/-- An affine étale `X`-scheme over a locally Noetherian `X` is locally Noetherian; see
`Stacks.EtaleCohomology.isLocallyNoetherian_etale_left`. -/
local instance isLocallyNoetherian_affineEtale_left (W : X.AffineEtale) :
    IsLocallyNoetherian ((Scheme.AffineEtale.Spec X).obj W).left :=
  isLocallyNoetherian_etale_left X _

/-- An affine étale `X`-scheme over a locally Noetherian `X` has a Noetherian space; see
`Stacks.EtaleCohomology.noetherianSpace_affineEtale_left`. This is the hypothesis that makes the
second map available on the affine étale site and unavailable on the whole small étale site. -/
local instance noetherianSpace_affineEtale_Spec_obj_left (W : X.AffineEtale) :
    NoetherianSpace ((Scheme.AffineEtale.Spec X).obj W).left :=
  noetherianSpace_affineEtale_left X W

/-- **The component of the second map of Stacks 03RI at an affine étale `X`-scheme**: the
homomorphism from the sections of `j_* 𝐆_{m,η}` over `W`, which are the invertible global
functions on the generic fibre of `W` raised to the coefficient universe, to the sections of
`⨁_x (i_x)_* 𝐙` over `W`.

It is `Stacks.EtaleCohomology.closedPointDivisorSheafSection` preceded by the identification of
the raised group with the group itself. -/
def affineEtaleDivisorApp (W : X.AffineEtale) :
    ((genericPointDirectImage.{u, v} X).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField))).obj.obj
          (op ((Scheme.AffineEtale.Spec X).obj W)) ⟶
      (closedPointDivisorSheaf.{u, v} X).obj.obj (op ((Scheme.AffineEtale.Spec X).obj W)) :=
  ConcreteCategory.ofHom
    ((closedPointDivisorSheafSection.{u, v} ((Scheme.AffineEtale.Spec X).obj W)).comp
      (AddEquiv.ulift (α := Additive ((Γ(pullback ((Scheme.AffineEtale.Spec X).obj W).hom
          (genericPointInclusion X), ⊤))ˣ))).toAddMonoidHom)

/-- The component of the second map at an affine étale `X`-scheme, as a homomorphism of abelian
groups. -/
theorem affineEtaleDivisorApp_hom (W : X.AffineEtale) :
    (affineEtaleDivisorApp.{u, v} X W).hom =
      (closedPointDivisorSheafSection.{u, v} ((Scheme.AffineEtale.Spec X).obj W)).comp
        (AddEquiv.ulift (α := Additive ((Γ(pullback ((Scheme.AffineEtale.Spec X).obj W).hom
          (genericPointInclusion X), ⊤))ˣ))).toAddMonoidHom :=
  ConcreteCategory.hom_ofHom _

/-- **The component of the second map sends an invertible global function on the generic fibre of
`W` to its family of orders of vanishing.** This is the equation that pins the morphism of sheaves
built below down to the second map of the source rather than to some other morphism of the same
type. -/
theorem affineEtaleDivisorApp_apply (W : X.AffineEtale)
    (z : ULift.{max (u + 1) v} (Additive ((Γ(pullback ((Scheme.AffineEtale.Spec X).obj W).hom
      (genericPointInclusion X), ⊤))ˣ))) :
    (affineEtaleDivisorApp.{u, v} X W).hom z =
      closedPointDivisorSheafSection.{u, v} ((Scheme.AffineEtale.Spec X).obj W) z.down :=
  (DFunLike.congr_fun (affineEtaleDivisorApp_hom.{u, v} X W) z).trans
    (AddMonoidHom.comp_apply _ _ z)

omit [IsNormal X] [IsLocallyNoetherian X] in
/-- **The restriction maps of `j_* 𝐆_{m,η}` pull an invertible function on the generic fibre back
along the base change of the morphism of the site.** This is a definitional identity: the sheaf
`j_* 𝐆_{m,η}` is `Stacks.EtaleCohomology.globalUnitsAdditive` precomposed with base change along
the generic point, so its restriction maps are `Units.map` of the pullback on global sections. -/
theorem genericPointDirectImage_multiplicativeSheaf_map_down {U V : X.Etale} (φ : U ⟶ V)
    (z : ULift.{max (u + 1) v} (Additive ((Γ(pullback V.hom (genericPointInclusion X), ⊤))ˣ))) :
    ((((genericPointDirectImage.{u, v} X).obj
          (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField))).obj.map φ.op).hom
        z).down =
      Additive.ofMul (Units.map ((smallEtaleBaseChange (genericPointInclusion X)).map
        φ).left.appTop.hom.toMonoidHom (Additive.toMul z.down)) :=
  rfl

/-- **The commuting square of the second map of Stacks 03RI at a morphism of the affine étale
site.** This is `Stacks.EtaleCohomology.closedPointDivisorSheafSection_map` at the image of the
morphism under `AlgebraicGeometry.Scheme.AffineEtale.Spec`, with the restriction maps of
`j_* 𝐆_{m,η}` computed by
`Stacks.EtaleCohomology.genericPointDirectImage_multiplicativeSheaf_map_down`.

The chain is written out step by step, each junction matching the next syntactically, because the
sections of `⨁_x (i_x)_* 𝐙` admit no definitional unfolding; see the implementation notes. -/
theorem affineEtaleDivisorApp_naturality {V W : X.AffineEtale} (φ : V ⟶ W) :
    ((genericPointDirectImage.{u, v} X).obj
          (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField))).obj.map
        ((Scheme.AffineEtale.Spec X).map φ).op ≫ affineEtaleDivisorApp.{u, v} X V =
      affineEtaleDivisorApp.{u, v} X W ≫
        (closedPointDivisorSheaf.{u, v} X).obj.map ((Scheme.AffineEtale.Spec X).map φ).op :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext fun z =>
    (ConcreteCategory.comp_apply _ _ z).trans
      (((affineEtaleDivisorApp_apply.{u, v} X V _).trans
          ((congrArg (closedPointDivisorSheafSection.{u, v} ((Scheme.AffineEtale.Spec X).obj V))
              (genericPointDirectImage_multiplicativeSheaf_map_down.{u, v} X
                ((Scheme.AffineEtale.Spec X).map φ) z)).trans
            ((closedPointDivisorSheafSection_map.{u, v}
                ((Scheme.AffineEtale.Spec X).map φ) (Additive.toMul z.down)).symm.trans
              (congrArg (fun w => ((closedPointDivisorSheaf.{u, v} X).obj.map
                    ((Scheme.AffineEtale.Spec X).map φ).op).hom w)
                (affineEtaleDivisorApp_apply.{u, v} X W z).symm)))).trans
        (ConcreteCategory.comp_apply _ _ z).symm))

/-- **The second map of the fundamental exact sequence of Stacks 03RI on the affine étale site**,
as a morphism of presheaves of abelian groups. Its component at an affine étale `X`-scheme `W` is
`Stacks.EtaleCohomology.affineEtaleDivisorApp`, and its commuting square is
`Stacks.EtaleCohomology.affineEtaleDivisorApp_naturality`. -/
@[stacks 03RI "the second map of the sequence on the affine étale site, as a morphism of
presheaves, for X integral, normal and locally Noetherian"]
def affineEtaleDivisorRestricted :
    (Scheme.AffineEtale.Spec X).op ⋙ ((genericPointDirectImage.{u, v} X).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField))).obj ⟶
      (Scheme.AffineEtale.Spec X).op ⋙ (closedPointDivisorSheaf.{u, v} X).obj where
  app W := affineEtaleDivisorApp.{u, v} X W.unop
  naturality _ _ g := affineEtaleDivisorApp_naturality.{u, v} X g.unop

/-! ### The second map as a morphism of sheaves -/

/-- **The second map of the fundamental exact sequence of Stacks 03RI, as a morphism of abelian
sheaves on the small étale site of `X`:**
`j_* 𝐆_{m,η} ⟶ ⨁_{x ∈ X_0} (i_x)_* 𝐙`.

It is `Stacks.EtaleCohomology.affineEtaleDivisorRestricted` transferred along the inclusion of the
affine étale site, which is cover dense and full and hence locally full, so
`CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom` is a bijection. The source states the
sequence for a smooth curve over an algebraically closed field; the hypotheses carried here —
integral, normal, locally Noetherian — are all weaker, and are discharged in that setting by
`Stacks.EtaleCohomology.isLocallyNoetherian_of_isCurve` and
`Stacks.EtaleCohomology.isNormal_of_isCurve_of_smooth`.

Being data, this definition is not pinned down by its type: the zero morphism inhabits it too.
What pins it down is `Stacks.EtaleCohomology.whiskerLeft_divisorSequenceSecondMap` together with
`Stacks.EtaleCohomology.divisorSequenceSecondMap_hom_app` and
`Stacks.EtaleCohomology.affineEtaleDivisorApp_apply`, which say that on sections over an affine
étale `X`-scheme it is the family of orders of vanishing, and
`Stacks.EtaleCohomology.divisorSequenceSecondMap_eq_of_whiskerLeft`, which says that no other
morphism of sheaves does so. -/
@[stacks 03RI "the second map of the sequence, as a morphism of étale sheaves, for X integral,
normal and locally Noetherian; the exactness of the sequence is not proved at this generality"]
def divisorSequenceSecondMap :
    (genericPointDirectImage.{u, v} X).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField)) ⟶
      closedPointDivisorSheaf.{u, v} X :=
  ⟨Functor.IsCoverDense.restrictHomEquivHom (G := Scheme.AffineEtale.Spec X)
    (K := X.smallEtaleTopology) (affineEtaleDivisorRestricted.{u, v} X)⟩

/-- **The second map restricts on the affine étale site to the morphism of presheaves it was built
from.** With `Stacks.EtaleCohomology.divisorSequenceSecondMap_eq_of_whiskerLeft` this is the
characterisation of the second map. -/
theorem whiskerLeft_divisorSequenceSecondMap :
    Functor.whiskerLeft (Scheme.AffineEtale.Spec X).op
        (divisorSequenceSecondMap.{u, v} X).hom =
      affineEtaleDivisorRestricted.{u, v} X :=
  Functor.IsCoverDense.sheafHom_restrict_eq _

/-- **On sections over an affine étale `X`-scheme the second map is the family of orders of
vanishing.** Composed with `Stacks.EtaleCohomology.affineEtaleDivisorApp_apply` this says that an
invertible global function on the generic fibre of `W` is sent to
`Stacks.EtaleCohomology.closedPointDivisorSheafSection` of it. -/
theorem divisorSequenceSecondMap_hom_app (W : X.AffineEtale) :
    (divisorSequenceSecondMap.{u, v} X).hom.app
        ((Scheme.AffineEtale.Spec X).op.obj (op W)) =
      affineEtaleDivisorApp.{u, v} X W :=
  NatTrans.congr_app (whiskerLeft_divisorSequenceSecondMap.{u, v} X) (op W)

/-- **The second map is the unique morphism of sheaves restricting to
`Stacks.EtaleCohomology.affineEtaleDivisorRestricted` on the affine étale site.** Restriction along
a cover-dense and locally full inclusion is a bijection on morphisms into a sheaf, hence injective,
so the characterisation above determines the second map completely. -/
theorem divisorSequenceSecondMap_eq_of_whiskerLeft
    (f : (genericPointDirectImage.{u, v} X).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField)) ⟶
      closedPointDivisorSheaf.{u, v} X)
    (hf : Functor.whiskerLeft (Scheme.AffineEtale.Spec X).op f.hom =
      affineEtaleDivisorRestricted.{u, v} X) :
    f = divisorSequenceSecondMap.{u, v} X :=
  Sheaf.hom_ext ((Functor.IsCoverDense.restrictHomEquivHom (G := Scheme.AffineEtale.Spec X)
    (K := X.smallEtaleTopology)).symm.injective
      (hf.trans (whiskerLeft_divisorSequenceSecondMap.{u, v} X).symm))

/-! ### The sequence is a complex -/

/-- **The two maps of the divisor sequence compose to zero on sections over an affine étale
`X`-scheme.** The comparison morphism sends an invertible global function on `W` to its
restriction to the generic fibre of `W`, by
`Stacks.EtaleCohomology.multiplicativeDirectImageComparison_app_ofUnit`, and a function that is
invertible on all of `W` has neither zeros nor poles, by
`Stacks.EtaleCohomology.closedPointDivisorSheafSection_restrict_eq_zero`. -/
theorem comparison_app_comp_affineEtaleDivisorApp (W : X.AffineEtale) :
    (multiplicativeDirectImageComparison.{u, v} (genericPointInclusion X)).hom.app
          (op ((Scheme.AffineEtale.Spec X).obj W)) ≫ affineEtaleDivisorApp.{u, v} X W = 0 := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a => ?_)
  obtain ⟨x, rfl⟩ := Stacks.Kummer.ofUnit_surjective.{u, v} a
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  refine Eq.trans (congrArg (fun z => (affineEtaleDivisorApp.{u, v} X W).hom z)
    (multiplicativeDirectImageComparison_app_ofUnit.{u, v} (genericPointInclusion X)
      ((Scheme.AffineEtale.Spec X).obj W) x)) ?_
  exact (affineEtaleDivisorApp_apply.{u, v} X W _).trans
    (closedPointDivisorSheafSection_restrict_eq_zero.{u, v}
      ((Scheme.AffineEtale.Spec X).obj W) x)

/-- **The two maps of the fundamental exact sequence of Stacks 03RI compose to zero**, so that
`0 → 𝐆_{m,X} → j_* 𝐆_{m,η} → ⨁_{x ∈ X_0} (i_x)_* 𝐙 → 0`
is a complex of abelian sheaves on the small étale site of `X`.

Both composites are morphisms into the sheaf `⨁_x (i_x)_* 𝐙`, so restriction to the affine étale
site is injective on them and it suffices to compare them there, where
`Stacks.EtaleCohomology.comparison_app_comp_affineEtaleDivisorApp` applies. -/
@[stacks 03RI "the sequence is a complex: the two constructed maps compose to zero, for X
integral, normal and locally Noetherian; the exactness of the sequence is not proved at this
generality"]
theorem multiplicativeDirectImageComparison_comp_divisorSequenceSecondMap :
    multiplicativeDirectImageComparison.{u, v} (genericPointInclusion X) ≫
        divisorSequenceSecondMap.{u, v} X = 0 :=
  Sheaf.hom_ext ((Functor.IsCoverDense.restrictHomEquivHom (G := Scheme.AffineEtale.Spec X)
    (K := X.smallEtaleTopology)).symm.injective
      (NatTrans.ext (funext fun W =>
        (congrArg
            (fun ψ => (multiplicativeDirectImageComparison.{u, v}
                (genericPointInclusion X)).hom.app
              (op ((Scheme.AffineEtale.Spec X).obj W.unop)) ≫ ψ)
            (divisorSequenceSecondMap_hom_app.{u, v} X W.unop)).trans
          (comparison_app_comp_affineEtaleDivisorApp.{u, v} X W.unop))))

/-! ### The right-hand exactness of the sequence, reduced to one summand at a time -/

/-- **The second map of Stacks 03RI is an epimorphism as soon as every section of every summand
`(i_x)_* 𝐙` is étale locally the divisor of a section of `j_* 𝐆_{m,η}`.**

The hypothesis names only the sections of the *summands*: for a closed point `x` of `X`, an étale
`X`-scheme `U` and a section `t` of `(i_x)_* 𝐙` over `U`, the sieve of those `g : V ⟶ U` along
which the image of `t` under the summand inclusion restricts into the set-theoretic image of the
second map is required to cover `U`. Nothing is asked about the sections of `⨁_x (i_x)_* 𝐙`
itself.

That this suffices is `CategoryTheory.Sheaf.epi_of_forall_imageSieve_ι_mem`: an epimorphism out of
a coproduct is tested on the summands, so the local description of a section of a coproduct of
sheaves as a finite sum — and with it the separatedness of the presheaf coproduct that
`Stacks.EtaleCohomology.closedPointDivisorSheaf` sheafifies, and the closure of the local image
under addition — is never needed.

This carries the right-hand exactness of Stacks 03RI as its hypothesis and so is *not* registered
on that tag: the hypothesis is the surjectivity the source asserts. What the library still owes it
is the local statement at one closed point, for which the rational function with prescribed divisor
is `Stacks.EtaleCohomology.exists_genericFibreOrd_eq_and_forall_ord_eq_zero_of_isNormal`. -/
theorem epi_divisorSequenceSecondMap_of_forall_imageSieve_ι_mem
    (h : ∀ (x : closedPoints X) (U : X.Etale)
      (t : ToType ((closedPointSkyscraper.{u, v} X x).obj.obj (op U))),
      Presheaf.imageSieve (divisorSequenceSecondMap.{u, v} X).hom
          ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app (op U) t) ∈
        X.smallEtaleTopology U) :
    Epi (divisorSequenceSecondMap.{u, v} X) :=
  Sheaf.epi_of_forall_imageSieve_ι_mem (closedPointSkyscraper.{u, v} X)
    (divisorSequenceSecondMap.{u, v} X) h

/-- **The second map of Stacks 03RI is an epimorphism as soon as every section of every summand
`(i_x)_* 𝐙` over an *affine* étale `X`-scheme is étale locally the divisor of a section of
`j_* 𝐆_{m,η}`.** This is
`Stacks.EtaleCohomology.epi_divisorSequenceSecondMap_of_forall_imageSieve_ι_mem` with its
hypothesis restricted to the objects of the affine étale site, which are the only ones on which
`Stacks.EtaleCohomology.divisorSequenceSecondMap_hom_app` computes the component of the second map.

The reduction is `CategoryTheory.Sheaf.epi_of_forall_imageSieve_ι_mem_of_isCoverDense` at the
inclusion `AlgebraicGeometry.Scheme.AffineEtale.Spec`, which is cover dense for the small étale
topology: the sieve of arrows into an arbitrary étale `X`-scheme that factor through an affine one
covers it, so `CategoryTheory.GrothendieckTopology.transitive` reduces the sieve at an arbitrary
object to its pullbacks along those arrows, and
`CategoryTheory.Presheaf.pullback_imageSieve` identifies each pullback with the image sieve of the
restricted section.

Like the statement it specialises, this carries the right-hand exactness of Stacks 03RI as its
hypothesis and so is not registered on that tag. What the library still owes it is the covering of
an affine étale `X`-scheme by *integral* affine étale ones meeting the fibre over the chosen closed
point in a single point, on which
`Stacks.EtaleCohomology.exists_etaleGenericFibreOrdOfPoint_eq_and_forall_eq_zero_of_isCurve` and
`Stacks.EtaleCohomology.closedPointDivisorSheaf.sheafSectionOfDirectSum_eq_ι` produce the required
section. -/
theorem epi_divisorSequenceSecondMap_of_forall_imageSieve_ι_mem_affineEtale
    (h : ∀ (x : closedPoints X) (W : X.AffineEtale)
      (t : ToType ((closedPointSkyscraper.{u, v} X x).obj.obj
        (op ((Scheme.AffineEtale.Spec X).obj W)))),
      Presheaf.imageSieve (divisorSequenceSecondMap.{u, v} X).hom
          ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app
            (op ((Scheme.AffineEtale.Spec X).obj W)) t) ∈
        X.smallEtaleTopology ((Scheme.AffineEtale.Spec X).obj W)) :
    Epi (divisorSequenceSecondMap.{u, v} X) :=
  Sheaf.epi_of_forall_imageSieve_ι_mem_of_isCoverDense (closedPointSkyscraper.{u, v} X)
    (Scheme.AffineEtale.Spec X) (divisorSequenceSecondMap.{u, v} X) h

end Affine

/-! ### The second map in the setting of Stacks 03RI and Stacks 03RM -/

/-- **The second map of the fundamental exact sequence of Stacks 03RI for a smooth curve over a
field**, which is the setting of the source. The three hypotheses of
`Stacks.EtaleCohomology.divisorSequenceSecondMap` are discharged there: a curve is integral by
`AlgebraicGeometry.IsVariety` and locally Noetherian by
`Stacks.EtaleCohomology.isLocallyNoetherian_of_isCurve`, and a smooth curve is normal by
`Stacks.EtaleCohomology.isNormal_of_isCurve_of_smooth`. -/
@[stacks 03RI "the second map of the sequence for a smooth curve over a field, as a morphism of
étale sheaves; the short exactness of the sequence is proved in the MiddleExactness file of this
directory"]
def divisorSequenceSecondMapOfCurve {k : Type u} [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g] :
    (genericPointDirectImage.{u, v} X).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField)) ⟶
      closedPointDivisorSheaf.{u, v} X :=
  haveI : IsNormal X := isNormal_of_isCurve_of_smooth g
  haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
  divisorSequenceSecondMap.{u, v} X

/-- **The two maps of the fundamental exact sequence of Stacks 03RI compose to zero for a smooth
curve over a field.** This is
`Stacks.EtaleCohomology.multiplicativeDirectImageComparison_comp_divisorSequenceSecondMap` with
the hypotheses of that statement discharged as in
`Stacks.EtaleCohomology.divisorSequenceSecondMapOfCurve`. -/
@[stacks 03RI "the sequence is a complex for a smooth curve over a field: the two constructed maps
compose to zero; the short exactness of the sequence is proved in the MiddleExactness file of
this directory"]
theorem multiplicativeDirectImageComparison_comp_divisorSequenceSecondMapOfCurve {k : Type u}
    [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g] :
    multiplicativeDirectImageComparison.{u, v} (genericPointInclusion X) ≫
        divisorSequenceSecondMapOfCurve.{u, v} g = 0 :=
  have : IsNormal X := isNormal_of_isCurve_of_smooth g
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
  multiplicativeDirectImageComparison_comp_divisorSequenceSecondMap.{u, v} X

/-- **The second map of Stacks 03RI for a smooth curve over a field is an epimorphism as soon as
every section of every summand `(i_x)_* 𝐙` is étale locally the divisor of a section of
`j_* 𝐆_{m,η}`.** This is
`Stacks.EtaleCohomology.epi_divisorSequenceSecondMap_of_forall_imageSieve_ι_mem` with the
hypotheses of that statement discharged as in
`Stacks.EtaleCohomology.divisorSequenceSecondMapOfCurve`.

Together with
`Stacks.EtaleCohomology.mono_multiplicativeDirectImageComparison_genericPointInclusion` and the
exactness in the middle, this is the shape in which the `hSE` hypothesis of
`Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_smoothCurve` is discharged
through `CategoryTheory.ShortComplex.ShortExact.mk'`, in
`Stacks.EtaleCohomology.shortExact_divisorSequenceOfCurve`. Its own hypothesis is the right-hand
exactness, so it is not registered on Tag 03RI. -/
theorem epi_divisorSequenceSecondMapOfCurve_of_forall_imageSieve_ι_mem {k : Type u} [Field k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g]
    (h : ∀ (x : closedPoints X) (U : X.Etale)
      (t : ToType ((closedPointSkyscraper.{u, v} X x).obj.obj (op U))),
      Presheaf.imageSieve (divisorSequenceSecondMapOfCurve.{u, v} g).hom
          ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app (op U) t) ∈
        X.smallEtaleTopology U) :
    Epi (divisorSequenceSecondMapOfCurve.{u, v} g) :=
  have : IsNormal X := isNormal_of_isCurve_of_smooth g
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
  epi_divisorSequenceSecondMap_of_forall_imageSieve_ι_mem.{u, v} X h

/-- **The second map of Stacks 03RI for a smooth curve over a field is an epimorphism as soon as
every section of every summand over an *affine* étale `X`-scheme is étale locally the divisor of a
section of `j_* 𝐆_{m,η}`.** This is
`Stacks.EtaleCohomology.epi_divisorSequenceSecondMap_of_forall_imageSieve_ι_mem_affineEtale` with
the hypotheses of that statement discharged as in
`Stacks.EtaleCohomology.divisorSequenceSecondMapOfCurve`.

This is the shape in which the right-hand exactness of Stacks 03RI is to be proved: the only
objects left to inspect are affine étale `X`-schemes, which is where
`Stacks.EtaleCohomology.divisorSequenceSecondMap_hom_app` and
`Stacks.EtaleCohomology.affineEtaleDivisorApp_apply` compute the second map as the family of
orders of vanishing. Its own hypothesis is that exactness, so it is not registered on Tag 03RI. -/
theorem epi_divisorSequenceSecondMapOfCurve_of_forall_imageSieve_ι_mem_affineEtale {k : Type u}
    [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g]
    (h : ∀ (x : closedPoints X) (W : X.AffineEtale)
      (t : ToType ((closedPointSkyscraper.{u, v} X x).obj.obj
        (op ((Scheme.AffineEtale.Spec X).obj W)))),
      Presheaf.imageSieve (divisorSequenceSecondMapOfCurve.{u, v} g).hom
          ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app
            (op ((Scheme.AffineEtale.Spec X).obj W)) t) ∈
        X.smallEtaleTopology ((Scheme.AffineEtale.Spec X).obj W)) :
    Epi (divisorSequenceSecondMapOfCurve.{u, v} g) :=
  have : IsNormal X := isNormal_of_isCurve_of_smooth g
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
  epi_divisorSequenceSecondMap_of_forall_imageSieve_ι_mem_affineEtale.{u, v} X h

end Stacks.EtaleCohomology

end
