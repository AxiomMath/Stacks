module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.RestrictionComparison

/-!
# The quotient sheaf of a restricted groupoid in algebraic spaces

Let `G` be a groupoid in algebraic spaces over `B`, with object space `U` and arrow space `R`,
and let `g : U' ⟶ U` be a morphism of algebraic spaces. The arrow space of the restriction of
`G` to `U'` is the restriction along `g` of the pre-relation `(t, s) : R ⟶ U ×_B U` of `G`
(**Stacks 044D**), so the induced map of fppf quotient sheaves is the one of **Stacks 046P**.

That map `U'/R' ⟶ U/R` is always injective. It is bijective as soon as the *saturation map*
`U' ×_{g, U, t} R ⟶ U`, which reads off the source of an arrow of `G` whose target lifts along
`g`, is surjective as a map of fppf sheaves — in particular when that map, or `g` itself, is a
one-member fppf covering, and when `g` is surjective as a map of fppf sheaves.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionSaturationMap`: the saturation map
  `U' ×_{g, U, t} R ⟶ U`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionQuotientSheafMap`: the induced map
  `U'/R' ⟶ U/R` of quotient sheaves.

## Main results

* `AlgebraicGeometry.Space.isLocallySurjective_of_isFppfCovering_singleton`: a one-member fppf
  covering of algebraic spaces is surjective as a map of fppf sheaves.
* `AlgebraicGeometry.Space.epi_toQuotientSheaf`: the projection onto a quotient sheaf is an
  epimorphism of fppf sheaves.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.mono_restrictionQuotientSheafMap`: **Stacks
  044N**, injectivity.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isIso_restrictionQuotientSheafMap_of_saturation`:
  **Stacks 044N**, bijectivity when the saturation map is surjective. Its three special cases are
  `isIso_restrictionQuotientSheafMap_of_saturation_isFppfCovering`,
  `isIso_restrictionQuotientSheafMap_of_isLocallySurjective` and
  `isIso_restrictionQuotientSheafMap_of_isFppfCovering` in the same namespace.

## Implementation notes

Injectivity is not reproved: by **Stacks 043X** the pre-relation of a groupoid in algebraic
spaces is a pre-equivalence relation, and `AlgebraicGeometry.Space.restrictQuotientSheafMap_mono`
is **Stacks 046P** for a pre-equivalence relation. The same applies to the two criteria phrased
in terms of `g` alone.

Surjectivity under the weaker hypothesis on the saturation map is proved directly, as in the
source: the two composites of the saturation square with the quotient projection of `U` agree,
because an arrow of `G` has the same image in `U/R` at its source and at its target, and the one
through the target factors through `U'/R'`. So the surjection
`U' ×_{g, U, t} R ⟶ U ⟶ U/R` factors through `U'/R' ⟶ U/R`, which is therefore an epimorphism;
with injectivity this gives an isomorphism of sheaves.

A surjection of fppf sheaves is `CategoryTheory.Presheaf.IsLocallySurjective`, not surjectivity
on each set of sections.

## References

* [Stacks Project, Tag 043X](https://stacks.math.columbia.edu/tag/043X)
* [Stacks Project, Tag 044J](https://stacks.math.columbia.edu/tag/044J)
* [Stacks Project, Tag 044N](https://stacks.math.columbia.edu/tag/044N)
* [Stacks Project, Tag 046P](https://stacks.math.columbia.edu/tag/046P)
* [Stacks Project, Tag 0469](https://stacks.math.columbia.edu/tag/0469)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A one-member fppf covering of algebraic spaces is surjective as a map of fppf sheaves: the
coproduct of a family indexed by a one-element type is the single member, with the identity as
its inclusion, so **Stacks 0469** applies to the member itself. -/
theorem isLocallySurjective_of_isFppfCovering_singleton (site : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : site.Contains S)
    {X F : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u} (φ : X ⟶ F)
    (hφ : IsFppfCovering site S hS (fun _ : PUnit ↦ X) (fun _ ↦ φ)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology site S hS) φ := by
  let A : Sheaf (BigFppfOver.topology site S hS) (Type u) :=
    ⟨X, (hφ.source_isAlgebraicSpace PUnit.unit).isSheaf⟩
  let F' : Sheaf (BigFppfOver.topology site S hS) (Type u) :=
    ⟨F, hφ.target_isAlgebraicSpace.isSheaf⟩
  let hc := Cofan.isColimitMkOfUnique (Iso.refl A) PUnit
  have hs := isLocallySurjective_coproductDesc_of_isFppfCovering site S hS
    (fun _ : PUnit ↦ X) (fun _ ↦ φ) hφ A (fun _ ↦ 𝟙 A) hc
  have he : hc.desc (Cofan.mk F' (fun _ : PUnit ↦ (⟨φ⟩ : A ⟶ F'))) = (⟨φ⟩ : A ⟶ F') := by
    simpa using hc.fac (Cofan.mk F' (fun _ : PUnit ↦ (⟨φ⟩ : A ⟶ F'))) ⟨PUnit.unit⟩
  change Sheaf.IsLocallySurjective
    (hc.desc (Cofan.mk F' (fun _ : PUnit ↦ (⟨φ⟩ : A ⟶ F')))) at hs
  rwa [he] at hs

variable {site : BigFppfSite.{u}} {S : Scheme.{u}} {hS : site.Contains S}
  {Z : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u} {R U : Over Z}
  [HasSheafify (BigFppfOver.topology site S hS) (Type u)]

/-- **Stacks 044J.** The projection of `U` onto the quotient sheaf of a pre-relation is an
epimorphism of fppf sheaves: a map out of the quotient sheaf is determined by its restriction
to `U`. -/
@[stacks 044J "the quotient projection is an epimorphism"]
theorem epi_toQuotientSheaf (j : PreRelation R U)
    {hU : Presheaf.IsSheaf (BigFppfOver.topology site S hS) U.left}
    (p : (⟨U.left, hU⟩ : Sheaf (BigFppfOver.topology site S hS) (Type u)) ⟶ quotientSheaf j)
    (hp : p.hom = toQuotientSheaf j) : Epi p := by
  refine ⟨fun {A} f₁ f₂ h ↦ ?_⟩
  have hfg : toQuotientSheaf j ≫ f₁.hom = toQuotientSheaf j ≫ f₂.hom := by
    rw [← hp]
    exact congrArg (·.hom) h
  have hk : j.target.left ≫ toQuotientSheaf j ≫ f₁.hom =
      j.source.left ≫ toQuotientSheaf j ≫ f₁.hom := by
    simpa only [Category.assoc] using
      congrArg (· ≫ f₁.hom) (target_toQuotientSheaf_eq_source j)
  exact (quotientSheafDesc_unique j A _ hk f₁ rfl).trans
    (quotientSheafDesc_unique j A _ hk f₂ hfg.symm).symm

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} [HasSheafify (BigFppfOver.topology C S hS) (Type u)]

/-- **Stacks 044N.** The *saturation map* of a restriction: the morphism `U' ×_{g, U, t} R ⟶ U`
sending an arrow of `G` whose target lifts along `g` to its source. It is the saturation map of
**Stacks 046T** for the canonical morphism from the restriction to `G`. -/
noncomputable def restrictionSaturationMap (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    AlgebraicSpaces.fiberProduct C S hS g G.target ⟶ G.objects :=
  fiberProductSnd g G.target ≫ G.source

/-- **Stacks 044N.** The map `U'/R' ⟶ U/R` of fppf quotient sheaves induced by restricting a
groupoid in algebraic spaces along `g`, the arrow space `R'` of the restriction being the
restricted pre-relation by **Stacks 044D**. -/
@[stacks 044N "the map of quotient sheaves"]
noncomputable abbrev restrictionQuotientSheafMap (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    Space.quotientSheaf (Space.PreRelation.restrict (Space.groupoidPreRelation G)
        (restrictionObjectsHom G g)) ⟶
      Space.quotientSheaf (Space.groupoidPreRelation G) :=
  Space.restrictQuotientSheafMap (Space.groupoidPreRelation G) (restrictionObjectsHom G g)

/-- The map of quotient sheaves restricts to `g` on `U'`. -/
private theorem toQuotientSheaf_comp_restrictionQuotientSheafMap
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    Space.toQuotientSheaf (Space.PreRelation.restrict (Space.groupoidPreRelation G)
          (restrictionObjectsHom G g)) ≫
        (restrictionQuotientSheafMap G g).hom =
      g.hom ≫ Space.toQuotientSheaf (Space.groupoidPreRelation G) :=
  Space.toQuotientSheaf_quotientSheafDesc _ _ _ _

/-- **Stacks 044N.** Restricting a groupoid in algebraic spaces gives an injective map of fppf
quotient sheaves: the pre-relation of a groupoid is a pre-equivalence relation by **Stacks
043X**, and restricting a pre-equivalence relation is injective on quotient sheaves by **Stacks
046P**. -/
@[stacks 044N "injectivity"]
theorem mono_restrictionQuotientSheafMap (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    Mono (restrictionQuotientSheafMap G g) :=
  Space.restrictQuotientSheafMap_mono _ _ (Space.groupoidPreRelation_isPreEquivalenceRelation G)
    U'.property.isSheaf

/-- **Stacks 044N.** If every object of `U` is fppf-locally the source of an arrow of `G` whose
target lifts along `g`, then the map of quotient sheaves induced by the restriction is
bijective. -/
@[stacks 044N "bijectivity when the saturation map is surjective"]
theorem isIso_restrictionQuotientSheafMap_of_saturation
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (hsat : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      (restrictionSaturationMap G g).hom) :
    IsIso (restrictionQuotientSheafMap G g) := by
  let J := BigFppfOver.topology C S hS
  let jG := Space.groupoidPreRelation G
  let jR := Space.PreRelation.restrict jG (restrictionObjectsHom G g)
  let Φ := restrictionQuotientSheafMap G g
  let Us : Sheaf J (Type u) := ⟨G.objects.obj, G.objects.property.isSheaf⟩
  let U's : Sheaf J (Type u) := ⟨U'.obj, U'.property.isSheaf⟩
  let Vs : Sheaf J (Type u) :=
    ⟨(AlgebraicSpaces.fiberProduct C S hS g G.target).obj,
      (AlgebraicSpaces.fiberProduct C S hS g G.target).property.isSheaf⟩
  let p : Us ⟶ Space.quotientSheaf jG := ⟨Space.toQuotientSheaf jG⟩
  let p' : U's ⟶ Space.quotientSheaf jR := ⟨Space.toQuotientSheaf jR⟩
  let sat : Vs ⟶ Us := ⟨(restrictionSaturationMap G g).hom⟩
  let lift : Vs ⟶ U's := ⟨(fiberProductFst g G.target).hom⟩
  have htarget : (jG : _ ⟶ _).target.left = G.target.hom := by
    simp [jG, Space.groupoidPreRelation, Space.PreRelation.target]
  have hsource : (jG : _ ⟶ _).source.left = G.source.hom := by
    simp [jG, Space.groupoidPreRelation, Space.PreRelation.source]
  have hrel : G.source.hom ≫ Space.toQuotientSheaf jG =
      G.target.hom ≫ Space.toQuotientSheaf jG := by
    rw [← htarget, ← hsource]
    exact (Space.target_toQuotientSheaf_eq_source jG).symm
  have hfac : lift ≫ p' ≫ Φ = sat ≫ p := by
    refine Sheaf.hom_ext ?_
    change (fiberProductFst g G.target).hom ≫
        Space.toQuotientSheaf jR ≫ (restrictionQuotientSheafMap G g).hom =
      (restrictionSaturationMap G g).hom ≫ Space.toQuotientSheaf jG
    rw [toQuotientSheaf_comp_restrictionQuotientSheafMap G g]
    change (pullback.fst g.hom G.target.hom) ≫ g.hom ≫ Space.toQuotientSheaf jG =
      (pullback.snd g.hom G.target.hom ≫ G.source.hom) ≫ Space.toQuotientSheaf jG
    rw [Category.assoc, hrel, ← Category.assoc, ← Category.assoc, pullback.condition]
  have : Epi sat := (Sheaf.isLocallySurjective_iff_epi sat).1 hsat
  have : Epi p := Space.epi_toQuotientSheaf jG p rfl
  have : Epi (p' ≫ Φ) := epi_of_epi_fac hfac
  have : Epi Φ := epi_of_epi p' Φ
  have : Mono Φ := mono_restrictionQuotientSheafMap G g
  exact isIso_of_mono_of_epi Φ

/-- **Stacks 044N.** If the saturation map is a one-member fppf covering, then the map of
quotient sheaves induced by the restriction is bijective. -/
@[stacks 044N "the saturation map is an fppf covering"]
theorem isIso_restrictionQuotientSheafMap_of_saturation_isFppfCovering
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (hsat : Space.IsFppfCovering C S hS
      (fun _ : PUnit ↦ (AlgebraicSpaces.fiberProduct C S hS g G.target).obj)
      (fun _ ↦ (restrictionSaturationMap G g).hom)) :
    IsIso (restrictionQuotientSheafMap G g) :=
  isIso_restrictionQuotientSheafMap_of_saturation G g
    (Space.isLocallySurjective_of_isFppfCovering_singleton C S hS _ hsat)

/-- **Stacks 044N.** If `g` is surjective as a map of fppf sheaves, then the map of quotient
sheaves induced by the restriction is bijective. -/
@[stacks 044N "bijectivity when the restricting morphism is surjective"]
theorem isIso_restrictionQuotientSheafMap_of_isLocallySurjective
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (hg : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) g.hom) :
    IsIso (restrictionQuotientSheafMap G g) :=
  Space.restrictQuotientSheafMap_isIso _ _
    (Space.groupoidPreRelation_isPreEquivalenceRelation G) hg G.objects.property.isSheaf
    U'.property.isSheaf

/-- **Stacks 044N.** If `g` is a one-member fppf covering, then the map of quotient sheaves
induced by the restriction is bijective. -/
@[stacks 044N "the restricting morphism is an fppf covering"]
theorem isIso_restrictionQuotientSheafMap_of_isFppfCovering
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (hg : Space.IsFppfCovering C S hS (fun _ : PUnit ↦ U'.obj) (fun _ ↦ g.hom)) :
    IsIso (restrictionQuotientSheafMap G g) :=
  isIso_restrictionQuotientSheafMap_of_isLocallySurjective G g
    (Space.isLocallySurjective_of_isFppfCovering_singleton C S hS _ hg)

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
