module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeSlice
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheafFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryRingedTopos
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Slice

/-!
# The morphism of ringed topoi of a 1-morphism is flat (Stacks 06TX)

Let `p : 𝒳 ⥤ (Sch/S)` and `q : 𝒴 ⥤ (Sch/S)` be categories fibred in groupoids over the big fppf
category of a scheme `S`, let `F : 𝒳 ⥤ 𝒴` be a 1-morphism between them, and let `τ` be a topology
on the underlying category of schemes which is coarser than the fppf one. The morphism of ringed
topoi `f : Sh(𝒳_τ) → Sh(𝒴_τ)` of Stacks 06TW is **flat** in the sense of Stacks 04JB: its
structure map in inverse-image form is the identification `f⁻¹O_𝒴 = O_𝒳` of Stacks 06TW, hence an
isomorphism, and an isomorphism of sheaves of commutative rings is a flat morphism of sheaves of
rings.

The source's second assertion is that the same happens for a morphism of schemes: for `i : X ⟶ Y`
over `S`, the morphism of big `τ`-sites `i : (Sch/X)_τ → (Sch/Y)_τ` is flat too. In this library
`(Sch/X)` is a category fibred in groupoids over `(Sch/S)` through postcomposition with the
structure morphism of `X` (`AlgebraicGeometry.Stack.schemeSlice`), and postcomposition with `i` is
a 1-morphism between two such, so the second assertion is the first one instantiated — exactly the
reading the source gives it ("exactly the same thing happens").

## The orientation of the equality

The remark as printed says `f^{-1}\mathcal{O}_\mathcal{X} = \mathcal{O}_\mathcal{Y}`, which is the
transpose of the identification the lemma it cites actually provides, namely
`f^{-1}\mathcal{O}_\mathcal{Y} = \mathcal{O}_\mathcal{X}`; the printed form is a typo. Flatness of
a morphism of ringed topoi is flatness of `O_𝒳` as a module over `f⁻¹O_𝒴`
(`AlgebraicGeometry.RingedToposHom.IsFlat`), so it is the lemma's orientation that is used, and the
morphism asserted to be flat is `f : Sh(𝒳_τ) → Sh(𝒴_τ)`, the one the source names.

## Main results

* `AlgebraicGeometry.Stack.isFlat_associatedRingedToposHom`: **Stacks 06TX**, the morphism of
  ringed topoi of Stacks 06TW is flat.
* `AlgebraicGeometry.Stack.associatedTopology_overMap`: the site the big fppf category of a scheme
  `U` over `S` inherits, read as a category fibred in groupoids over `(Sch/S)`, is the localization
  of `τ` at `U` — so the ringed topos appearing below really is the big `τ`-site of `U`.
* `AlgebraicGeometry.Stack.isFibredOneMorphism_overMap`: postcomposition with a morphism of schemes
  over `S` is a 1-morphism of those categories fibred in groupoids.
* `AlgebraicGeometry.Stack.isFlat_associatedRingedToposHom_overMap`: **Stacks 06TX**, the second
  assertion — the morphism of big `τ`-sites of a morphism of schemes over `S` is flat.

## Implementation notes

No hypothesis on the morphism of schemes `i` is used in
`AlgebraicGeometry.Stack.isFlat_associatedRingedToposHom_overMap`: the source instantiates its
second assertion at a closed immersion, but the argument — the inverse-image structure map is an
isomorphism because both structure sheaves are restrictions of one and the same structure sheaf of
the base — is insensitive to `i`, and that insensitivity is the very point the remark is making.
So the statement here is a generalization of the source's, with the source's closed-immersion case
contained in it; it is not a weakening.

As in `AlgebraicGeometry.Stack.structureSheaf` the topology argument is an arbitrary topology
coarser than the fppf one, and the five statements of the source are its values at the five big
topologies. Essential smallness of the two total categories at the universe of the structure
sheaf's sections is carried over from
`AlgebraicGeometry.Stack.associatedRingedToposHom`, which needs it for the direct image to exist;
for the big fppf category of a scheme it follows from `EssentiallySmall.{u} B.Schemes`, which is
Stacks 000J (`AlgebraicGeometry.essentiallySmall_schemeBelow`) and is carried as an instance
hypothesis exactly as in `StacksFrontier/AlgebraicGeometry/Stacks/EssentiallySmallSite.lean`.

`CategoryTheory.Functor.isFibredOneMorphism_of_isFiberedInGroupoids` is the general fact behind
`AlgebraicGeometry.Stack.isFibredOneMorphism_overMap`: in a category fibred in groupoids every
morphism is strongly cartesian over its image (Stacks 003V,
`CategoryTheory.Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift`), so preservation of
strongly cartesian morphisms is automatic and being strictly over the base is the only condition
left. Strictness here is `Over.map i.left ⋙ Over.map Y.hom = Over.map X.hom`, which is
`CategoryTheory.Over.mapComp_eq` — an equality, not just an isomorphism — together with the
triangle `Over.w i`.

## References

* [Stacks Project, Tag 06TX](https://stacks.math.columbia.edu/tag/06TX)
* [Stacks Project, Tag 06TW](https://stacks.math.columbia.edu/tag/06TW)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS) (F : 𝒳 ⥤ 𝒴)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  (hF : p.IsFibredOneMorphism q F) [EssentiallySmall.{u} 𝒳] [EssentiallySmall.{u} 𝒴]

/-- **Stacks 06TX.** The morphism of ringed topoi `f : Sh(𝒳_τ) → Sh(𝒴_τ)` induced by a 1-morphism
of categories fibred in groupoids is flat: its structure map in inverse-image form is the
identification `f⁻¹O_𝒴 = O_𝒳` of Stacks 06TW, and an isomorphism of sheaves of commutative rings
makes its target a flat module over its source. -/
@[stacks 06TX "flatness of the morphism of ringed topoi of a 1-morphism"]
theorem isFlat_associatedRingedToposHom :
    RingedToposHom.IsFlat
      (X := associatedRingedTopos B S hS p hp τ hτ)
      (Y := associatedRingedTopos B S hS q hq τ hτ)
      (associatedRingedToposHom B S hS p q F hp hq τ hτ hF) := by
  have : IsIso (associatedRingedToposHom B S hS p q F hp hq τ hτ hF).fSharpInverseImage :=
    isIso_fSharpInverseImage_associatedRingedToposHom B S hS p q F hp hq τ hτ hF
  have : HasSheafify (associatedTopology B S hS p τ) AddCommGrpCat.{max u v w} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, w, v} _
  have : (associatedTopology B S hS p τ).WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w, v, w} _
  unfold RingedToposHom.IsFlat SheafOfModules.IsFlatMapULift
  exact SheafOfModules.isFlatMap_of_isIso
    ((SheafOfModules.sheafULift.{u, v, w} (associatedTopology B S hS p τ)).map
      (associatedRingedToposHom B S hS p q F hp hq τ hτ hF).fSharpInverseImage)

section SchemeSites

variable {B S hS} (X Y : BigFppfOver B S hS) (i : X ⟶ Y)

/-- The topology that the big fppf category of a scheme `U` over `S` inherits, read as a category
fibred in groupoids over the big fppf category of `S` through postcomposition with the structure
morphism of `U` (`AlgebraicGeometry.Stack.schemeSlice`), is the localization of `τ` at `U`: the
associated site of `(Sch/U)` *is* the big `τ`-site of `U`. -/
theorem associatedTopology_overMap (U : BigFppfOver B S hS)
    (τ : GrothendieckTopology B.Schemes) :
    associatedTopology B S hS (Over.map U.hom) τ = τ.over U.left := by
  have : (Over.map U.hom).IsFibered := (Functor.IsFiberedInGroupoids.over_map U.hom).isFibered
  have : (𝟭 B.Schemes).IsFibered := Functor.isFiberedInGroupoids_id.isFibered
  calc associatedTopology B S hS (Over.map U.hom) τ
      = (Over.map U.hom ⋙ Over.forget (B.obj hS)).inheritedTopology τ :=
        (Functor.inheritedTopology_comp_overForget' (B.obj hS) (Over.map U.hom) τ).symm
    _ = (Over.forget U.left ⋙ 𝟭 B.Schemes).inheritedTopology τ := by
        rw [Functor.comp_id, Over.mapForget_eq]
    _ = ((𝟭 B.Schemes).inheritedTopology τ).over U.left :=
        Functor.inheritedTopology_overForget_comp _ τ U.left
    _ = τ.over U.left := by rw [Functor.inheritedTopology_id]

/-- Postcomposition with a morphism `i : X ⟶ Y` of schemes over `S` is a 1-morphism of the big
fppf categories of `X` and of `Y`, read as categories fibred in groupoids over the big fppf
category of `S`. Being strictly over the base is `CategoryTheory.Over.mapComp_eq` together with
the triangle of `i`, and preservation of strongly cartesian morphisms is automatic because the
target is fibred in groupoids. -/
theorem isFibredOneMorphism_overMap :
    (Over.map X.hom).IsFibredOneMorphism (Over.map Y.hom) (Over.map i.left) :=
  Functor.isFibredOneMorphism_of_isFiberedInGroupoids (.over_map Y.hom)
    (by rw [← Over.mapComp_eq, Over.w])

variable [EssentiallySmall.{u} B.Schemes]
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- **Stacks 06TX**, the second assertion. For a morphism `i : X ⟶ Y` of schemes over `S` the
induced morphism of ringed big `τ`-sites `i : (Sch/X)_τ → (Sch/Y)_τ` is flat, for the same reason:
the two structure sheaves are restrictions of one and the same structure sheaf of the base, so the
inverse-image structure map is an isomorphism.

The source states this for a closed immersion; no hypothesis on `i` is used, which is the point
the remark makes. -/
@[stacks 06TX "flatness of the morphism of big τ-sites of a morphism of schemes"]
theorem isFlat_associatedRingedToposHom_overMap :
    RingedToposHom.IsFlat
      (X := associatedRingedTopos B S hS (Over.map X.hom) (.over_map X.hom) τ hτ)
      (Y := associatedRingedTopos B S hS (Over.map Y.hom) (.over_map Y.hom) τ hτ)
      (associatedRingedToposHom B S hS (Over.map X.hom) (Over.map Y.hom) (Over.map i.left)
        (.over_map X.hom) (.over_map Y.hom) τ hτ (isFibredOneMorphism_overMap X Y i)) :=
  isFlat_associatedRingedToposHom B S hS _ _ _ _ _ τ hτ _

end SchemeSites

end AlgebraicGeometry.Stack

end
