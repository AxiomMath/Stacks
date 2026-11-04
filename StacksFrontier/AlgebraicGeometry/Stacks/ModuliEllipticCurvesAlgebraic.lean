module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurves

/-!
# When the moduli stack of elliptic curves is an algebraic stack

Following the informal chapter on algebraic stacks, a morphism from a scheme `S` to the moduli
stack `𝓜₁,₁` of elliptic curves *is* an elliptic curve over `S`, and a commutative triangle over
`𝓜₁,₁` *is* an isomorphism of elliptic curves over the given morphisms of bases. Saying that
`𝓜₁,₁` is an *algebraic stack* is then the conjunction of three conditions: descent for objects
for the étale topology on the category of all schemes, the key fact that the fibre product of two
morphisms from schemes is representable by a scheme, and the existence of a surjective and smooth
morphism from a scheme.

## Main definitions

* `AlgebraicGeometry.ModuliEllipticCurves.FamilyIso` is an isomorphism of pointed families over a
  fixed base, that is, an isomorphism of the two morphisms to `𝓜₁,₁` they classify.
* `AlgebraicGeometry.ModuliEllipticCurves.EtaleGlueingDatum` is a glueing datum of elliptic
  curves on an étale covering: a curve on each member, the witnesses identifying the two
  restrictions over a common base, and their cocycle condition.
* `AlgebraicGeometry.ModuliEllipticCurves.IsGlueingOf` says that an elliptic curve on the base
  recovers the witnesses of such a datum.
* `AlgebraicGeometry.ModuliEllipticCurves.HasEtaleDescentForObjects` is condition (1) of Tag
  072R, the "sheaf property" in the precise form the source spells out.
* `AlgebraicGeometry.ModuliEllipticCurves.KeyFactHolds` is condition (2), the key fact of Tag
  072M.
* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.IsSurjective` is surjectivity of a
  morphism `S ⟶ 𝓜₁,₁`, which is Tag 072P's definition of smoothness with smoothness replaced by
  surjectivity, as the source prescribes immediately after it.
* `AlgebraicGeometry.ModuliEllipticCurves.HasSmoothSurjectiveCover` is condition (3).
* `AlgebraicGeometry.ModuliEllipticCurves.ModuliStackIsAlgebraic` is the property defined by Tag
  072R.

## Main results

This file introduces definitions only; it has no propositional results.

## Implementation notes

The moduli stack is never introduced as an object: as in
`AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.IsSmooth`, a morphism `S ⟶ 𝓜₁,₁` is
modelled by a `PointedFamily S` together with `PointedFamily.IsElliptic`, and the fibre product
of two such morphisms by `RepresentsComparisons`. Surjectivity is therefore the extension of Tag
072P's definition of smoothness to surjective morphisms, which the source prescribes in the
sentences following that definition.

Condition (1) is the precise form the source spells out after the definition: an elliptic curve
on each member of an étale covering, witnesses identifying the two restrictions over the pairwise
fibre products, the cocycle condition over the triple fibre products, and existence of a curve on
the base, unique up to a unique isomorphism, inducing the given witnesses. The witnesses are
indexed by an arbitrary test scheme mapping into two members over the base, rather than by the
pairwise fibre products themselves, together with a compatibility under further restriction of
that test scheme; this carries the same information, because the pairwise and triple fibre
products are among the test data, while making the cocycle condition an identity between
morphisms with no intervening comparison isomorphisms. The covering is a `Scheme.Cover` for
Mathlib's étale precoverage on all schemes, so its index type lives in a universe `v`
independent of the universe `u` of the schemes; the source's `Sch` is the category of all schemes
here, so no choice of big étale site enters.

## References

* [Stacks Project, Tag 072P](https://stacks.math.columbia.edu/tag/072P)
* [Stacks Project, Tag 072R](https://stacks.math.columbia.edu/tag/072R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.ModuliEllipticCurves

namespace PointedFamily

/-- The projection `E ×_{S,a} T ⟶ E` from a family restricted along `a : T ⟶ S` to the family it
was restricted from. -/
abbrev restrictProj {S T : Scheme.{u}} (E : PointedFamily S) (a : T ⟶ S) :
    (E.pullback a).total ⟶ E.total :=
  Limits.pullback.fst E.map a

/-- The canonical morphism `E ×_{S, g ≫ a} U ⟶ E ×_{S, a} T` of restricted families induced by a
morphism `g : U ⟶ T` of test schemes. -/
abbrev restrictCompMap {S T U : Scheme.{u}} (E : PointedFamily S) (a : T ⟶ S) (g : U ⟶ T) :
    (E.pullback (g ≫ a)).total ⟶ (E.pullback a).total :=
  E.pullbackMap g rfl

end PointedFamily

/-- An isomorphism of pointed families over a fixed base `T`: an isomorphism of the total spaces
over `T` carrying the one distinguished section to the other. This is an isomorphism of the two
morphisms `T ⟶ 𝓜₁,₁` that the two families classify. -/
structure FamilyIso {T : Scheme.{u}} (E F : PointedFamily T) where
  /-- The isomorphism of total spaces. -/
  iso : E.total ≅ F.total
  /-- It is a morphism over the base. -/
  iso_map : iso.hom ≫ F.map = E.map
  /-- It matches the distinguished sections. -/
  zero_iso : E.zero ≫ iso.hom = F.zero

/-- **Stacks Project, Tag 072R.** A glueing datum for elliptic curves on an étale covering
`{Sᵢ ⟶ S}`: an elliptic curve on each member, a witness `αᵢⱼ` identifying the two restrictions
over every test scheme mapping into the `i`-th and the `j`-th member over `S`, compatibility of
the witnesses with further restriction, and the cocycle condition. -/
structure EtaleGlueingDatum {S : Scheme.{u}}
    (𝒰 : Scheme.Cover.{v, u} Scheme.etalePrecoverage S) where
  /-- The elliptic curve on each member of the covering. -/
  family (i : 𝒰.I₀) : PointedFamily (𝒰.X i)
  /-- Each member of the covering carries an elliptic curve. -/
  isElliptic (i : 𝒰.I₀) : (family i).IsElliptic
  /-- The witness `αᵢⱼ` over a test scheme mapping into the `i`-th and the `j`-th member. -/
  witness (i j : 𝒰.I₀) {T : Scheme.{u}} (a : T ⟶ 𝒰.X i) (b : T ⟶ 𝒰.X j)
    (hab : a ≫ 𝒰.f i = b ≫ 𝒰.f j) :
    FamilyIso ((family i).pullback a) ((family j).pullback b)
  /-- The witnesses are compatible with further restriction of the test scheme. -/
  witness_restrict (i j : 𝒰.I₀) {T U : Scheme.{u}} (a : T ⟶ 𝒰.X i) (b : T ⟶ 𝒰.X j)
    (hab : a ≫ 𝒰.f i = b ≫ 𝒰.f j) (g : U ⟶ T) :
    (witness i j (g ≫ a) (g ≫ b)
          (by rw [Category.assoc, Category.assoc, hab])).iso.hom ≫
        (family j).restrictCompMap b g =
      (family i).restrictCompMap a g ≫ (witness i j a b hab).iso.hom
  /-- The cocycle condition `αᵢₖ = αⱼₖ ∘ αᵢⱼ`. -/
  cocycle (i j k : 𝒰.I₀) {T : Scheme.{u}} (a : T ⟶ 𝒰.X i) (b : T ⟶ 𝒰.X j) (c : T ⟶ 𝒰.X k)
    (hab : a ≫ 𝒰.f i = b ≫ 𝒰.f j) (hbc : b ≫ 𝒰.f j = c ≫ 𝒰.f k) :
    (witness i k a c (hab.trans hbc)).iso.hom =
      (witness i j a b hab).iso.hom ≫ (witness j k b c hbc).iso.hom

/-- **Stacks Project, Tag 072R.** An elliptic curve `E` on the base, equipped with isomorphisms
`r i` of the members of a glueing datum with the restrictions of `E` to the members of the
covering, *glues* that datum when it recovers every witness of the datum. -/
def IsGlueingOf {S : Scheme.{u}} {𝒰 : Scheme.Cover.{v, u} Scheme.etalePrecoverage S}
    (D : EtaleGlueingDatum 𝒰) (E : PointedFamily S)
    (r : ∀ i, FamilyIso (D.family i) (E.pullback (𝒰.f i))) : Prop :=
  ∀ (i j : 𝒰.I₀) {T : Scheme.{u}} (a : T ⟶ 𝒰.X i) (b : T ⟶ 𝒰.X j)
    (hab : a ≫ 𝒰.f i = b ≫ 𝒰.f j),
    (D.family i).restrictProj a ≫ (r i).iso.hom ≫ E.restrictProj (𝒰.f i) =
      (D.witness i j a b hab).iso.hom ≫
        (D.family j).restrictProj b ≫ (r j).iso.hom ≫ E.restrictProj (𝒰.f j)

/-- **Stacks Project, Tag 072R.** Condition (1): descent for objects for the étale topology on
the category of all schemes. Every glueing datum of elliptic curves on an étale covering is
glued by an elliptic curve on the base, and that curve is unique up to a unique isomorphism
compatible with the glueing isomorphisms. -/
def HasEtaleDescentForObjects : Prop :=
  ∀ {S : Scheme.{u}} (𝒰 : Scheme.Cover.{v, u} Scheme.etalePrecoverage S)
    (D : EtaleGlueingDatum 𝒰),
    (∃ (E : PointedFamily S) (_ : E.IsElliptic)
        (r : ∀ i, FamilyIso (D.family i) (E.pullback (𝒰.f i))), IsGlueingOf D E r) ∧
      ∀ (E E' : PointedFamily S)
        (r : ∀ i, FamilyIso (D.family i) (E.pullback (𝒰.f i)))
        (r' : ∀ i, FamilyIso (D.family i) (E'.pullback (𝒰.f i))),
        IsGlueingOf D E r → IsGlueingOf D E' r' →
          ∃! φ : FamilyIso E E', ∀ i : 𝒰.I₀,
            (r i).iso.hom ≫ E.restrictProj (𝒰.f i) ≫ φ.iso.hom =
              (r' i).iso.hom ≫ E'.restrictProj (𝒰.f i)

/-- **Stacks Project, Tag 072R.** Condition (2): the key fact of Tag 072M, that the fibre product
over `𝓜₁,₁` of two morphisms from schemes is representable by a scheme. -/
def KeyFactHolds : Prop :=
  ∀ {S S' : Scheme.{u}} (E : PointedFamily S) (E' : PointedFamily S'),
    E.IsElliptic → E'.IsElliptic → ∃ P : Scheme.{u}, Nonempty (RepresentsComparisons E E' P)

/-- **Stacks Project, Tag 072P.** A morphism `S ⟶ 𝓜₁,₁`, that is, an elliptic curve over `S`, is
surjective when for every morphism `S' ⟶ 𝓜₁,₁` the projection `S ×_{𝓜₁,₁} S' ⟶ S'` is a
surjective morphism of schemes. This is the definition of smoothness with smoothness replaced by
surjectivity, the extension the source prescribes. -/
def PointedFamily.IsSurjective {S : Scheme.{u}} (E : PointedFamily S) (_hE : E.IsElliptic) :
    Prop :=
  ∀ {S' : Scheme.{u}} (E' : PointedFamily S'), E'.IsElliptic →
    ∀ (P : Scheme.{u}) (r : RepresentsComparisons E E' P),
      AlgebraicGeometry.Surjective (r.homEquiv P (𝟙 P)).snd

/-- **Stacks Project, Tag 072R.** Condition (3): there exists a surjective and smooth morphism
`S ⟶ 𝓜₁,₁` from a scheme. -/
def HasSmoothSurjectiveCover : Prop :=
  ∃ (S : Scheme.{u}) (E : PointedFamily S) (hE : E.IsElliptic),
    E.IsSmooth hE ∧ E.IsSurjective hE

/-- **Stacks Project, Tag 072R.** The moduli stack `𝓜₁,₁` of elliptic curves is an *algebraic
stack* if and only if descent for objects holds for the étale topology on the category of all
schemes, the key fact holds, and there exists a surjective and smooth morphism `S ⟶ 𝓜₁,₁` from a
scheme. -/
@[stacks 072R]
def ModuliStackIsAlgebraic : Prop :=
  HasEtaleDescentForObjects.{u, v} ∧ KeyFactHolds.{u} ∧ HasSmoothSurjectiveCover.{u}

end AlgebraicGeometry.ModuliEllipticCurves

end
