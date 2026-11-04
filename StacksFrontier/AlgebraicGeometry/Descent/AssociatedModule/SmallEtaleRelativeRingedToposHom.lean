module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleImageSections
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.SmallEtaleTensorProduct
public import StacksFrontier.AlgebraicGeometry.RestrictScalarsColimits.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageStructureSheaf

/-!
# The Zariski-to-étale comparison with coefficients in `f⁻¹𝒪_Y`

Let `f : X ⟶ Y` be a morphism of schemes and let
`ε = id_{small, étale, Zar} : X_étale ⟶ X_Zar` be the morphism of ringed sites of Stacks 070R,
carried by the inclusion `AlgebraicGeometry.SmallEtale.opensToSmallEtale`.  A *relative*
condition on an `𝒪_X`-module is a condition on it read as a module over `f⁻¹𝒪_Y`, so comparing
such a condition across `ε` requires `ε` itself to be read with coefficients in `f⁻¹𝒪_Y`
rather than in `𝒪_X`.  This module supplies that reading: the two ringed topoi
`(X_Zar, f⁻¹𝒪_Y)` and `(X_étale, ε⁻¹f⁻¹𝒪_Y)`, the morphism of ringed topoi between them, and
the structure map `ε⁻¹f⁻¹𝒪_Y ⟶ 𝒪_{X_étale}` with the restriction of scalars along it.

Nothing here needs a new sheafification or a new continuity argument: `ε⁻¹` on sheaves of
commutative rings is `AlgebraicGeometry.SmallEtale.inverseImageCommRing`, and the
structure map of the comparison is the unit of the adjunction that defines it.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.inverseImageRingedTopos` is the ringed topos
  `(X_Zar, f⁻¹𝒪_Y)`, the ringed-topos form of
  `AlgebraicGeometry.Scheme.Hom.inverseImageRingedSite`.
* `AlgebraicGeometry.SmallEtale.relativeStructureSheaf` is `ε⁻¹f⁻¹𝒪_Y`, a sheaf of commutative
  rings on the small étale site of `X`, and
  `AlgebraicGeometry.SmallEtale.relativeRingedTopos` is the ringed topos
  `(X_étale, ε⁻¹f⁻¹𝒪_Y)`.
* `AlgebraicGeometry.SmallEtale.toZariskiRelativeRingedToposHom` is the morphism of ringed
  topoi `(X_étale, ε⁻¹f⁻¹𝒪_Y) ⟶ (X_Zar, f⁻¹𝒪_Y)`: the continuous inclusion of the small
  Zariski site of `X` into its small étale site, with structure map the unit of the
  inverse-image/direct-image adjunction at `f⁻¹𝒪_Y`.
* `AlgebraicGeometry.SmallEtale.relativeStructureMap` is the structure map
  `ε⁻¹f⁻¹𝒪_Y ⟶ 𝒪_{X_étale}`: the inverse image of `f⁻¹𝒪_Y ⟶ 𝒪_X` followed by the structure
  map of `ε`.  `relativeRingCatSheafMap` is the same map on sheaves of rings.
* `AlgebraicGeometry.SmallEtale.relativeScalarRestriction` is restriction of scalars along it,
  `Mod(𝒪_{X_étale}) ⥤ Mod(ε⁻¹f⁻¹𝒪_Y)`, and
  `AlgebraicGeometry.SmallEtale.relativeDerivedScalarRestriction` is the induced functor on
  unbounded derived categories.

## Main results

* `AlgebraicGeometry.Scheme.Hom.inverseImageRingedTopos_ringSheaf`: the sheaf of rings of
  `(X_Zar, f⁻¹𝒪_Y)` is `AlgebraicGeometry.Scheme.Hom.inverseImageRingCatSheaf`, by `rfl`, so
  the modules of the ringed topos are the ones the Zariski-side restriction of scalars already
  lands in.
* `AlgebraicGeometry.SmallEtale.homEquiv_symm_toZariskiRelativeRingedToposHom_fSharp`: the
  structure map of the comparison is the identity in inverse-image form.  This is what says
  that the comparison changes the site and nothing else: the structure sheaf upstairs is
  *defined* to be the inverse image of the one downstairs.
* `AlgebraicGeometry.SmallEtale.relativeDerivedScalarRestriction_commShift` and
  `relativeDerivedScalarRestriction_isTriangulated`: derived restriction of scalars commutes
  with the shift and is triangulated, restated for the functor named here, which instance
  search does not unfold.

## Implementation notes

**This is `ε` with coefficients, not yet the `ε′` of Stacks 0DK7.**  The source compares
`D(f⁻¹𝒪_Y)` with `D(f_{small}^{-1}𝒪_{Y_étale})`, where `f_{small} : X_étale ⟶ Y_étale` is base
change on small étale sites.  The comparison built here is the canonical morphism of ringed
topoi over `ε` whose coefficients are `f⁻¹𝒪_Y`, and no tag is placed on it.

**The two coefficient sheaves are not isomorphic.**  Identifying `ε⁻¹f⁻¹𝒪_Y` with
`f_{small}^{-1}𝒪_{Y_étale}` cannot be done by combining
the commutation `f ∘ ε_X = ε_Y ∘ f_{small}` of morphisms of topoi together with "Stacks 070S (2),
the identification of `ε_Y^{-1}𝒪_{Y_Zar}` with `𝒪_{Y_étale}`".  There is no such identification:
070S (2) is about the *module* pullback `ε^*`, and the ring-level `ε_Y^{-1}𝒪_{Y_Zar}` is **not**
`𝒪_{Y_étale}` — Stacks 0GNA asserts only that the structure map between them is flat.  See the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleRingedToposHom.lean`.

What a consumer actually needs is weaker than an isomorphism of the two sheaves, and is a
statement about their **images in `𝒪_{X_étale}`**, since that is all a derivation sees.  Write
`c : ε⁻¹f⁻¹𝒪_Y ⟶ f_{small}^{-1}𝒪_{Y_étale}` for the map the topos commutation supplies,
together with the structure map of `ε_Y`.  Then:

* every derivation over `f_{small}^{-1}𝒪_{Y_étale}` is one over `ε⁻¹f⁻¹𝒪_Y`, by `c`; and
* the converse — the direction the invertibility clause of Stacks 04CS needs — says that a
  derivation annihilating the image of `ε⁻¹f⁻¹𝒪_Y` annihilates the image of
  `f_{small}^{-1}𝒪_{Y_étale}`.

**No local-surjectivity model for `f_{small}^{-1}` on
the small étale site, the analogue of
`AlgebraicGeometry.SmallEtale.isLocallySurjective_imageSectionsToInverseImageOf`, is
needed.**  The vanishing of a derivation on the image of
`f_{small}^{-1}𝒪_{Y_étale}` is the equality of two morphisms out of `𝒪_{X_étale}` after
`f_{small}^♯`, and the adjunction `f_{small}^{-1} ⊣ f_{small,*}` for sheaves of *sets* turns
that into an equality after the direct-image form of the structure map, whose sections are
described by a formula.  The transposition is
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv` for an arbitrary morphism
of ringed topoi, and `AlgebraicGeometry.Space.structureSharpInverseImage_of_structureSharpSetComp`
in `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsMap.lean` is exactly this reduction,
already carried out for the small étale ringed topoi of algebraic spaces and already used there
to prove the vanishing clause of a universal derivation
(`AlgebraicGeometry.Space.structureSharpInverseImageSet_comp_universalDerivationHom`).

Under that reduction the second bullet becomes `d_{T/Y}(g^♯ t) = 0` for `g : T ⟶ W` over `Y` with
`W ⟶ Y` étale and `t` a global function on `W` — the shape of the direct-image structure map, which
at an étale `W / Y` pulls a global function on `W` back along the projection `X ×_Y W ⟶ W`
(`AlgebraicGeometry.structureSharp_hom_app`).  **That vanishing is now proved**, for `d^a` and for
an arbitrary factorization rather than only for a base change, in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleEtaleBaseDerivation.lean`:
`AlgebraicGeometry.SmallEtale.associatedDerivation_etaleBase_eq_zero`, from
`Ω_{W/Y} = 0` (Stacks 02H9) and the characterizing property of the canonical morphism of
Stacks 01UV.

So what is still missing for the comparison of Stacks 04CS is not either bullet's mathematics but
the *object*: `Ω_{X_étale/Y_étale}`, the module of differentials of
`(AlgebraicGeometry.smallEtaleRingedToposHom B f).fSharpInverseImage`, is not constructed in this
development for a morphism of schemes.  The only module of differentials built on a small étale
site at the universe of `(Ω_{X/Y})^a` is `AlgebraicGeometry.Space.sheafOfDifferentials`, which is
for a morphism of algebraic *spaces*; the general site-level construction
`AlgebraicGeometry.SheafOfModules.sheafifiedObjectwiseDifferentials` lands in
`SheafOfModules.{max u u₁ v₁ v}`, and on a site whose objects are one universe above its structure
rings that is `u + 1`, not `u`.

What *is* proved is that the derivations over `ε⁻¹f⁻¹𝒪_Y` are exactly the derivations of
`𝒪_{X_étale}` annihilating `AlgebraicGeometry.SmallEtale.pullbackSection`, in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleRelativeDerivation.lean`.

The Zariski-side ringed topos repeats the three fields of
`AlgebraicGeometry.Scheme.Hom.inverseImageRingedSite` rather than being derived from it:
`AlgebraicGeometry.RingedSite` and `AlgebraicGeometry.RingedTopos` are distinct structures with
the same fields, and the comparison is a `AlgebraicGeometry.RingedToposSiteHom`, which is the
only one of the two whose two sides may have different object universes — the small Zariski
site of `X` is presented by the opens of its space, one universe below the objects of the small
étale site.  All the projections agree by `rfl`, so a result stated for either spelling is a
result about the other.

Restriction of scalars along the relative structure map is exact because it does not change the
underlying sheaf of abelian groups; the two instances are
`Stacks.AlgebraicGeometry.RestrictScalarsColimits.preservesFiniteLimits_restrictScalars` and
its colimit companion.  So the derived functor needs no resolution and no exactness argument is
repeated here.  Their hypotheses, and the abelianness of the two categories of sheaves of
modules without which the derived categories are not even formed, come from
`AlgebraicGeometry.smallEtale_hasSheafify` and
`AlgebraicGeometry.smallEtale_wEqualsLocallyBijective`, which is why
`StacksFrontier/AlgebraicGeometry/Descent/Parasitic/SmallEtaleTensorProduct.lean` is imported: the
weak sheafification of
`AlgebraicGeometry.SmallEtale.hasWeakSheafify_smallEtale` is not enough for abelianness.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u d e

namespace AlgebraicGeometry

/-! ### The inverse-image ringed topos of a morphism of schemes -/

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `f⁻¹𝒪_Y` with its type recorded as a sheaf for `Opens.grothendieckTopology ↥X` rather than
as a `TopCat.Sheaf`.  The two spellings are definitionally equal; this one is what the
inverse-image functors of the small étale site consume, as for
`AlgebraicGeometry.Scheme.zariskiCommRingSheaf`. -/
def inverseImageCommRingSheaf : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u} :=
  inverseImageStructureSheaf f

/-- The **inverse-image ringed topos** `(X_Zar, f⁻¹𝒪_Y)` of a morphism of schemes `f : X ⟶ Y`:
the small Zariski site of `X`, equipped with the inverse image of the structure sheaf of `Y`.
This is `AlgebraicGeometry.Scheme.Hom.inverseImageRingedSite` as a ringed topos. -/
abbrev inverseImageRingedTopos : RingedTopos.{u, u, u} where
  C := X.Opens
  J := Opens.grothendieckTopology ↥X
  O := inverseImageCommRingSheaf f

/-- The structure sheaf of `(X_Zar, f⁻¹𝒪_Y)` is `f⁻¹𝒪_Y`. -/
@[simp]
theorem inverseImageRingedTopos_O :
    (inverseImageRingedTopos f).O = inverseImageCommRingSheaf f :=
  rfl

/-- The two spellings of `f⁻¹𝒪_Y` agree. -/
theorem inverseImageCommRingSheaf_eq :
    inverseImageCommRingSheaf f = inverseImageStructureSheaf f :=
  rfl

/-- The sheaf of rings of `(X_Zar, f⁻¹𝒪_Y)` is
`AlgebraicGeometry.Scheme.Hom.inverseImageRingCatSheaf`, so the sheaves of modules on the
inverse-image ringed topos are the ones restriction of scalars along
`AlgebraicGeometry.Scheme.Hom.inverseImageRingCatSheafMap` lands in. -/
theorem inverseImageRingedTopos_ringSheaf :
    (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedTopos f).O) =
      inverseImageRingCatSheaf f :=
  rfl

end Scheme.Hom

/-! ### `ε⁻¹f⁻¹𝒪_Y` and the comparison of ringed topoi over it -/

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) {Y : Scheme.{u}}
  (f : X ⟶ Y)

/-- **`ε⁻¹f⁻¹𝒪_Y`**, the inverse image along `ε = id_{small, étale, Zar}` of the inverse-image
structure sheaf of `f : X ⟶ Y`: a sheaf of commutative rings on the small étale site of `X`. -/
abbrev relativeStructureSheaf : Sheaf (topology B X hX) CommRingCat.{u} :=
  (inverseImageCommRing B X hX).obj (Scheme.Hom.inverseImageCommRingSheaf f)

/-- The ringed topos `(X_étale, ε⁻¹f⁻¹𝒪_Y)`: the small étale site of `X`, equipped with the
inverse image along `ε` of the inverse-image structure sheaf of `f`. -/
abbrev relativeRingedTopos : RingedTopos.{u, u + 1, u} where
  C := SmallEtale B X hX
  J := topology B X hX
  O := relativeStructureSheaf B X hX f

/-- **The Zariski-to-étale comparison with coefficients in `f⁻¹𝒪_Y`**: the morphism of ringed
topoi `(X_étale, ε⁻¹f⁻¹𝒪_Y) ⟶ (X_Zar, f⁻¹𝒪_Y)` carried by the continuous inclusion of the
small Zariski site of `X` into its small étale site, with structure map the unit of the
inverse-image/direct-image adjunction at `f⁻¹𝒪_Y`. -/
def toZariskiRelativeRingedToposHom :
    RingedToposSiteHom (relativeRingedTopos B X hX f) (Scheme.Hom.inverseImageRingedTopos f) where
  u := opensToSmallEtale B X hX
  isContinuous := isContinuous_opensToSmallEtale B X hX
  fSharp := (inverseImageCommRingAdjunction B X hX).unit.app
    (Scheme.Hom.inverseImageCommRingSheaf f)

/-- The underlying functor of `toZariskiRelativeRingedToposHom` is the inclusion
`opensToSmallEtale` of the small Zariski site of `X` into its small étale site. -/
@[simp]
theorem toZariskiRelativeRingedToposHom_u :
    (toZariskiRelativeRingedToposHom B X hX f).u = opensToSmallEtale B X hX :=
  rfl

/-- The structure map of `toZariskiRelativeRingedToposHom` is the unit of the
inverse-image/direct-image adjunction `inverseImageCommRingAdjunction` at `f⁻¹𝒪_Y`. -/
@[simp]
theorem toZariskiRelativeRingedToposHom_fSharp :
    (toZariskiRelativeRingedToposHom B X hX f).fSharp =
      (inverseImageCommRingAdjunction B X hX).unit.app
        (Scheme.Hom.inverseImageCommRingSheaf f) :=
  rfl

/-- **The structure map of the comparison is the identity in inverse-image form.**  The
comparison changes the site and nothing else: the structure sheaf of its source is by
definition the inverse image of the structure sheaf of its target, and transposing the stored
direct-image structure map along the adjunction returns the identity of `ε⁻¹f⁻¹𝒪_Y`. -/
theorem homEquiv_symm_toZariskiRelativeRingedToposHom_fSharp :
    ((inverseImageCommRingAdjunction B X hX).homEquiv
        (Scheme.Hom.inverseImageCommRingSheaf f) (relativeStructureSheaf B X hX f)).symm
      (toZariskiRelativeRingedToposHom B X hX f).fSharp = 𝟙 _ :=
  (Equiv.symm_apply_eq _).2
    ((inverseImageCommRingAdjunction B X hX).homEquiv_id
      (Scheme.Hom.inverseImageCommRingSheaf f)).symm

/-! ### The relative structure map and restriction of scalars -/

/-- **The relative structure map `ε⁻¹f⁻¹𝒪_Y ⟶ 𝒪_{X_étale}`**: the inverse image along `ε` of
the structure map `f⁻¹𝒪_Y ⟶ 𝒪_X` of `f`, followed by the structure map
`ε⁻¹𝒪_{X_Zar} ⟶ 𝒪_{X_étale}` of `ε`.  Restriction of scalars along it reads an
`𝒪_{X_étale}`-module as an `ε⁻¹f⁻¹𝒪_Y`-module. -/
def relativeStructureMap :
    relativeStructureSheaf B X hX f ⟶ commRingStructureSheaf B X hX :=
  (inverseImageCommRing B X hX).map (AlgebraicGeometry.inverseImageStructureMap f) ≫
    inverseImageStructureMap B X hX

/-- `ε⁻¹f⁻¹𝒪_Y` with commutativity forgotten: the sheaf of rings over which sheaves of
`ε⁻¹f⁻¹𝒪_Y`-modules on the small étale site of `X` are indexed. -/
abbrev relativeRingCatSheaf : Sheaf (topology B X hX) RingCat.{u} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (relativeRingedTopos B X hX f).O)

/-- The relative structure map `ε⁻¹f⁻¹𝒪_Y ⟶ 𝒪_{X_étale}`, as a homomorphism of sheaves of not
necessarily commutative rings.  Its target is the structure sheaf of rings of Stacks 03DU, the
sheaf of rings over which the sheaves of modules of the small étale site are taken. -/
def relativeRingCatSheafMap :
    relativeRingCatSheaf B X hX f ⟶ structureSheaf B X hX :=
  (sheafCompose (topology B X hX) (forget₂ CommRingCat.{u} RingCat.{u})).map
    (relativeStructureMap B X hX f)

/-- **Restriction of scalars along `ε⁻¹f⁻¹𝒪_Y ⟶ 𝒪_{X_étale}`**,
`Mod(𝒪_{X_étale}) ⥤ Mod(ε⁻¹f⁻¹𝒪_Y)`: an `𝒪_{X_étale}`-module read as a module over the
inverse image of `f⁻¹𝒪_Y`.  The underlying sheaf of abelian groups is unchanged, so this
functor is exact. -/
abbrev relativeScalarRestriction :
    SheafOfModules.{u} (structureSheaf B X hX) ⥤
      SheafOfModules.{u} (relativeRingCatSheaf B X hX f) :=
  SheafOfModules.restrictScalars.{u} (relativeRingCatSheafMap B X hX f)

/-! ### The induced functor on derived categories -/

section Derived

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (structureSheaf B X hX))]
  [HasDerivedCategory.{e} (SheafOfModules.{u} (relativeRingCatSheaf B X hX f))]

/-- **Restriction of scalars along `ε⁻¹f⁻¹𝒪_Y ⟶ 𝒪_{X_étale}` on derived categories**,
`D(𝒪_{X_étale}) ⥤ D(ε⁻¹f⁻¹𝒪_Y)`.

Restriction of scalars is exact, so it descends to the unbounded derived categories with no
resolution at all.  This is the canonical name for that functor;
`CategoryTheory.Limits.PreservesFiniteColimits` is data rather than a proposition, so a
consumer should transport along an isomorphism rather than rebuild it. -/
def relativeDerivedScalarRestriction :
    DerivedCategory (SheafOfModules.{u} (structureSheaf B X hX)) ⥤
      DerivedCategory (SheafOfModules.{u} (relativeRingCatSheaf B X hX f)) :=
  (relativeScalarRestriction B X hX f).mapDerivedCategory

/-- Derived restriction of scalars along `ε⁻¹f⁻¹𝒪_Y ⟶ 𝒪_{X_étale}` is computed by termwise
restriction of scalars on any complex of `𝒪_{X_étale}`-modules. -/
def relativeDerivedScalarRestrictionFactors :
    DerivedCategory.Q ⋙ relativeDerivedScalarRestriction B X hX f ≅
      (relativeScalarRestriction B X hX f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (relativeScalarRestriction B X hX f).mapDerivedCategoryFactors

/-- Derived restriction of scalars along `ε⁻¹f⁻¹𝒪_Y ⟶ 𝒪_{X_étale}` commutes with the shift. -/
instance relativeDerivedScalarRestriction_commShift :
    (relativeDerivedScalarRestriction B X hX f).CommShift ℤ :=
  inferInstanceAs ((relativeScalarRestriction B X hX f).mapDerivedCategory.CommShift ℤ)

/-- Derived restriction of scalars along `ε⁻¹f⁻¹𝒪_Y ⟶ 𝒪_{X_étale}` is triangulated. -/
instance relativeDerivedScalarRestriction_isTriangulated :
    (relativeDerivedScalarRestriction B X hX f).IsTriangulated :=
  inferInstanceAs ((relativeScalarRestriction B X hX f).mapDerivedCategory.IsTriangulated)

end Derived

end SmallEtale

end AlgebraicGeometry

end
