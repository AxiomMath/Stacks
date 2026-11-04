module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageCotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.SquareFunctoriality
public import StacksFrontier.Cotangent.Spaces.EtaleStructureSheafULift

/-!
# The cotangent complex of a morphism of algebraic spaces is étale local

Let `S` be a scheme and let

```
U --g--> V
|p       |q
X --f--> Y
```

be a commutative square of algebraic spaces over `S` with `p` and `q` étale.  Stacks 08VE
identifies the restriction of `L_{X/Y}` to the small étale site of `U` with `L_{U/V}`.

Formation of the cotangent complex of a homomorphism of sheaves of commutative rings commutes
with inverse image (Stacks 08SV), so `L_{X/Y}|_{U_étale}` is the cotangent complex of the
homomorphism `p⁻¹(f⁻¹𝒪_Y ⟶ 𝒪_X)` on the small étale site of `U`.  That homomorphism is
isomorphic to `g⁻¹𝒪_V ⟶ 𝒪_U`: on the target because `p⁻¹𝒪_X = 𝒪_U`, and on the source because
`p⁻¹f⁻¹𝒪_Y = g⁻¹q⁻¹𝒪_Y` (Stacks 03G8 for the square) and `q⁻¹𝒪_Y = 𝒪_V` (Stacks 03LV).  The two
comparisons commute with the two structure maps, so square functoriality of the cotangent
complex transports the complex and the identification follows.

## Main definitions

* `AlgebraicGeometry.Space.etaleInverseImageSheafULiftIso`: for an étale `p`, the inverse image
  along `p_small` of a sheaf of commutative rings whose sections are lifted into the universe of
  the small étale sites is the lift of its inverse image, `p⁻¹(ULift 𝒢) ≅ ULift (p⁻¹𝒢)`.
* `AlgebraicGeometry.Space.etaleRestrictionCotangentSourceIso`: the comparison
  `p⁻¹f⁻¹𝒪_Y ≅ g⁻¹𝒪_V` of the sources of the two structure maps.
* `AlgebraicGeometry.Space.etaleRestrictModules`: restriction of `𝒪_X`-modules to the small
  étale site of `U` along an étale morphism `p : U ⟶ X`, that is `p_small⁻¹` with its
  coefficients read over `𝒪_U` through `p⁻¹𝒪_X = 𝒪_U`.
* `AlgebraicGeometry.Space.etaleRestrictionCotangentComplexIso`: **Stacks 08VE**, the
  identification `L_{X/Y}|_{U_étale} = L_{U/V}`.

## Main results

* `AlgebraicGeometry.Space.etaleRestrictionCotangentSquare`: the comparison of the sources and
  the comparison of the targets form a commutative square with the two structure maps.  This is
  what makes the identification a construction: both comparisons are built from Stacks 03LV and
  Stacks 03G8, and their commuting is the compatibility those tags already carry.
* `Stacks.Sheaves.ToposPullback.inverseImageCommRingRestrictionIso_naturality`: the comparison
  of an inverse image of sheaves of commutative rings with restriction along a functor of sites
  is natural in the sheaf.

## Implementation notes

**The two universes of sections.**  The clause `p⁻¹𝒪_X = 𝒪_U` of Stacks 03LV is available at the
universe `u + 1` of the small étale sites, as
`AlgebraicGeometry.Space.etaleInverseImageStructureSheafULiftIso`, which is the universe the
cotangent complex of Stacks 08VD lives at; the composition law of Stacks 03G8 in inverse-image
form, `AlgebraicGeometry.Space.smallEtaleRingedToposHom_squareInverseImageRingIso`, is available
at the universe `u` of the structure rings, where the three small étale direct images exist.
`AlgebraicGeometry.Space.etaleInverseImageSheafULiftIso` reconciles them: for an étale `p` the
inverse image along `p_small` is restriction along small étale postcomposition at *both*
universes — `AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso` at `u + 1` and
`AlgebraicGeometry.Space.smallToposMorphismTypeU_inverseImageIso` at `u`, both read through
`Stacks.Sheaves.ToposPullback.inverseImageCommRingRestrictionIso` — and restriction along a
functor of sites commutes with `AlgebraicGeometry.SheafOfModules.sheafULift` on the nose, both
acting on the underlying presheaf by composition
(`AlgebraicGeometry.Space.sheafULift_smallEtalePostcomp_map`).  So `p⁻¹` and the universe lift
commute, naturally in the sheaf, and applying that at `f⁻¹𝒪_Y` carries the whole comparison of
the sources down to the universe `u`, where Stacks 03G8 and Stacks 03LV at `q` are available.
No universe is identified with another: `u` is the universe of the algebraic spaces and of their
structure rings and `u + 1` is the universe of their small étale sites.

**Which category the identification lives in.**  Stacks 08SV lands in the modules over
`p⁻¹𝒪_X`, while `L_{U/V}` is a complex of `𝒪_U`-modules.  The two are identified by
`CategoryTheory.Sheaf.targetModulesTransport` along the clause `p⁻¹𝒪_X = 𝒪_U` itself, which is
the same comparison that appears as the target edge of the commutative square; that transport is
the second factor of `AlgebraicGeometry.Space.etaleRestrictModules`, so the left-hand side of
Stacks 08VE is a complex of `𝒪_U`-modules and the identification is one of complexes.  Being an
isomorphism of complexes it is in particular one of their images in `D(𝒪_U)`.

**Elaboration.**  The comparison of the inverse image with restriction and the universe lift
meet at two spellings of one sheaf — restriction of a lifted sheaf, and the lift of a restricted
sheaf — which are definitionally but not syntactically equal.  Compositions across that
boundary are therefore not type-correct at the transparency level `rw` works at, and the
reassociations around them are performed in term mode instead, exactly as the implementation
notes of `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRingedToposHomInverseImage.lean`
record for the same phenomenon.

## References

* [Stacks Project, Tag 08VE](https://stacks.math.columbia.edu/tag/08VE)
* [Stacks Project, Tag 08VD](https://stacks.math.columbia.edu/tag/08VD)
* [Stacks Project, Tag 08SV](https://stacks.math.columbia.edu/tag/08SV)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.ToposPullback

universe ww vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J.HasSheafCompose (forget CommRingCat.{ww})]
  [K.HasSheafCompose (forget CommRingCat.{ww})]
  (F : C ⥤ D) [F.IsContinuous J K]
  [PreservesFiniteProducts (F.sheafPushforwardContinuous (Type ww) J K)]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww)))
  (e : f.inverseImage ≅ F.sheafPushforwardContinuous (Type ww) J K)

/-- The identification of the inverse image of a sheaf of commutative rings with its restriction
along a continuous functor of the underlying sites is natural in the sheaf.

On underlying sheaves of sets the identification is the prescribed isomorphism `f⁻¹ ≅ F^s`, so
this is the naturality of that isomorphism read through the faithful forgetful functor. -/
lemma inverseImageCommRingRestrictionIso_naturality {O O' : Sheaf K CommRingCat.{ww}}
    (m : O ⟶ O') :
    (inverseImageCommRingFunctor f).map m ≫
        (inverseImageCommRingRestrictionIso J K F f e O').hom =
      (inverseImageCommRingRestrictionIso J K F f e O).hom ≫
        (F.sheafPushforwardContinuous CommRingCat.{ww} J K).map m := by
  have h1 : (sheafCompose J (forget CommRingCat.{ww})).map
        ((inverseImageCommRingFunctor f).map m) =
      f.inverseImage.map ((sheafCompose K (forget CommRingCat.{ww})).map m) :=
    underlyingRingSheaf_map_pullbackCommRingSheafMap J _ m
  have h2 : (sheafCompose J (forget CommRingCat.{ww})).map
        ((F.sheafPushforwardContinuous CommRingCat.{ww} J K).map m) =
      (F.sheafPushforwardContinuous (Type ww) J K).map
        ((sheafCompose K (forget CommRingCat.{ww})).map m) := rfl
  refine (sheafCompose J (forget CommRingCat.{ww})).map_injective ?_
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    inverseImageCommRingRestrictionIso_hom_forget, inverseImageCommRingRestrictionIso_hom_forget,
    h1, h2]
  exact e.hom.naturality _

/-- The inverse of the identification of the inverse image of a sheaf of commutative rings with
its restriction along a continuous functor of the underlying sites is natural in the sheaf. -/
lemma inverseImageCommRingRestrictionIso_inv_naturality {O O' : Sheaf K CommRingCat.{ww}}
    (m : O ⟶ O') :
    (F.sheafPushforwardContinuous CommRingCat.{ww} J K).map m ≫
        (inverseImageCommRingRestrictionIso J K F f e O').inv =
      (inverseImageCommRingRestrictionIso J K F f e O).inv ≫
        (inverseImageCommRingFunctor f).map m := by
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  exact (inverseImageCommRingRestrictionIso_naturality J K F f e m).symm

end Stacks.Sheaves.ToposPullback

namespace CategoryTheory.Sheaf

universe w₁ v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {B B' : Sheaf J CommRingCat.{max u₁ v₁ w₁}}

/-- Transport of the coefficient modules along an isomorphism of the sheaf of commutative rings
is additive: it is a restriction of scalars, which leaves the underlying sheaves of abelian
groups and the morphisms between them untouched. -/
instance targetModulesTransport_functor_additive (e : B ≅ B') :
    (targetModulesTransport.{u₁, v₁, w₁} J e).functor.Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars ((sheafCompose J
    (forget₂ CommRingCat.{max u₁ v₁ w₁} RingCat.{max u₁ v₁ w₁})).map e.inv)).Additive

/-- The inverse transport of the coefficient modules along an isomorphism of the sheaf of
commutative rings is additive, being restriction of scalars along the isomorphism itself. -/
instance targetModulesTransport_inverse_additive (e : B ≅ B') :
    (targetModulesTransport.{u₁, v₁, w₁} J e).inverse.Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars ((sheafCompose J
    (forget₂ CommRingCat.{max u₁ v₁ w₁} RingCat.{max u₁ v₁ w₁})).map e.hom)).Additive

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U V X Y : AlgebraicSpaces B S hS}

/-- Restriction of sheaves of commutative rings along small étale postcomposition commutes with
the lift of the sections into the universe of the small étale sites, on the nose: both act on
the underlying presheaf by composition, so the two composites agree by associativity. -/
lemma sheafULift_smallEtalePostcomp_map (p : U ⟶ X) (hp : IsEtale B S hS p.hom)
    {O O' : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}} (m : O ⟶ O') :
    ((smallEtalePostcomp B S hS p hp).sheafPushforwardContinuous CommRingCat.{u + 1}
          (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS X.1)).map
        ((SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS X.1)).map m) =
      (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS U.1)).map
        (((smallEtalePostcomp B S hS p hp).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS X.1)).map m) :=
  rfl

/-- **The inverse image along an étale morphism commutes with the universe lift.**  For an étale
morphism `p : U ⟶ X` of algebraic spaces and a sheaf of commutative rings `𝒢` on the small étale
site of `X` with sections at the universe of the structure rings,

`p_small⁻¹(ULift 𝒢) ≅ ULift (p_small⁻¹𝒢)`,

the left-hand inverse image being that of the morphism of small étale topoi at the universe of
the site and the right-hand one that at the universe of the structure rings.

Both inverse images are restriction along small étale postcomposition, by Stacks 03LQ at the
respective universe, and restriction commutes with the lift on the nose. -/
noncomputable def etaleInverseImageSheafULiftIso (p : U ⟶ X) (hp : IsEtale B S hS p.hom)
    (O : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) :
    (smallToposMorphism B S hS p).inverseImageRing.obj
        ((SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS X.1)).obj O) ≅
      (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS U.1)).obj
        ((smallEtaleInverseImageRing B S hS p).obj O) :=
  inverseImageCommRingRestrictionIso (SmallEtale.topology B S hS U.1)
      (SmallEtale.topology B S hS X.1) (smallEtalePostcomp B S hS p hp)
      (smallToposMorphism B S hS p) (smallToposMorphism_inverseImageIso B S hS p hp)
      ((SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS X.1)).obj O) ≪≫
    (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS U.1)).mapIso
      (inverseImageCommRingRestrictionIso (SmallEtale.topology B S hS U.1)
        (SmallEtale.topology B S hS X.1) (smallEtalePostcomp B S hS p hp)
        (smallEtaleRingedToposHom B S hS p).toToposHom
        (smallToposMorphismTypeU_inverseImageIso B S hS p hp) O).symm

/-- The forward map of `AlgebraicGeometry.Space.etaleInverseImageSheafULiftIso` is the
identification of the inverse image with restriction at the universe of the site, followed by
the lift of the inverse of that identification at the universe of the structure rings.  Both
factors are canonical, so the comparison involves no choice. -/
lemma etaleInverseImageSheafULiftIso_hom (p : U ⟶ X) (hp : IsEtale B S hS p.hom)
    (O : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) :
    (etaleInverseImageSheafULiftIso B S hS p hp O).hom =
      (inverseImageCommRingRestrictionIso (SmallEtale.topology B S hS U.1)
          (SmallEtale.topology B S hS X.1) (smallEtalePostcomp B S hS p hp)
          (smallToposMorphism B S hS p) (smallToposMorphism_inverseImageIso B S hS p hp)
          ((SheafOfModules.sheafULift.{u, u + 1, u}
            (SmallEtale.topology B S hS X.1)).obj O)).hom ≫
        (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS U.1)).map
          (inverseImageCommRingRestrictionIso (SmallEtale.topology B S hS U.1)
            (SmallEtale.topology B S hS X.1) (smallEtalePostcomp B S hS p hp)
            (smallEtaleRingedToposHom B S hS p).toToposHom
            (smallToposMorphismTypeU_inverseImageIso B S hS p hp) O).inv :=
  rfl

/-- The comparison `p_small⁻¹(ULift 𝒢) ≅ ULift (p_small⁻¹𝒢)` is natural in `𝒢`. -/
lemma etaleInverseImageSheafULiftIso_naturality (p : U ⟶ X) (hp : IsEtale B S hS p.hom)
    {O O' : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}} (m : O ⟶ O') :
    (smallToposMorphism B S hS p).inverseImageRing.map
          ((SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS X.1)).map m) ≫
        (etaleInverseImageSheafULiftIso B S hS p hp O').hom =
      (etaleInverseImageSheafULiftIso B S hS p hp O).hom ≫
        (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS U.1)).map
          ((smallEtaleInverseImageRing B S hS p).map m) := by
  have h1 := inverseImageCommRingRestrictionIso_naturality (SmallEtale.topology B S hS U.1)
    (SmallEtale.topology B S hS X.1) (smallEtalePostcomp B S hS p hp)
    (smallToposMorphism B S hS p) (smallToposMorphism_inverseImageIso B S hS p hp)
    ((SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS X.1)).map m)
  have h2 := inverseImageCommRingRestrictionIso_inv_naturality (SmallEtale.topology B S hS U.1)
    (SmallEtale.topology B S hS X.1) (smallEtalePostcomp B S hS p hp)
    (smallEtaleRingedToposHom B S hS p).toToposHom
    (smallToposMorphismTypeU_inverseImageIso B S hS p hp) m
  have key := congrArg (fun k => (SheafOfModules.sheafULift.{u, u + 1, u}
    (SmallEtale.topology B S hS U.1)).map k) h2
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at key
  rw [etaleInverseImageSheafULiftIso_hom, etaleInverseImageSheafULiftIso_hom]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ _) h1).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => _ ≫ k)
            ((congrArg (fun k => k ≫ _)
              (sheafULift_smallEtalePostcomp_map B S hS p hp m)).trans key)).trans
          (Category.assoc _ _ _).symm)))

/-- The clause `p⁻¹𝒪_X = 𝒪_U` of Stacks 03LV at the universe of the small étale sites is the
comparison of the inverse image with the universe lift, followed by the lift of that clause at
the universe of the structure rings. -/
lemma etaleInverseImageStructureSheafULiftIso_eq (p : U ⟶ X) (hp : IsEtale B S hS p.hom) :
    (etaleInverseImageStructureSheafULiftIso B S hS p hp).hom =
      (etaleInverseImageSheafULiftIso B S hS p hp (smallEtaleRingedTopos B S hS X).O).hom ≫
        (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS U.1)).map
          (etaleInverseImageStructureSheafIso B S hS p hp).hom := by
  rw [etaleInverseImageStructureSheafULiftIso_hom, etaleInverseImageSheafULiftIso_hom]
  exact Eq.symm ((Category.assoc _ _ _).trans
    (congrArg (fun k => _ ≫ k) (CategoryTheory.Functor.map_comp _ _ _).symm))

/-- For a commutative square `p ≫ f = g ≫ q` of algebraic spaces with `q` étale, the comparison

`p⁻¹f⁻¹𝒪_Y ≅ g⁻¹𝒪_V`

of the sources of the two structure maps, at the universe of the small étale sites.  It is the
comparison of the inverse image with the universe lift, then the composition law of Stacks 03G8
for the square, then the clause `q⁻¹𝒪_Y = 𝒪_V` of Stacks 03LV read on the small étale site of
`U` along `g`. -/
noncomputable def etaleRestrictionCotangentSourceIso {p : U ⟶ X} {f : X ⟶ Y} {g : U ⟶ V}
    {q : V ⟶ Y} (hp : IsEtale B S hS p.hom) (hq : IsEtale B S hS q.hom) (h : p ≫ f = g ≫ q) :
    (smallToposMorphism B S hS p).inverseImageRing.obj
        ((SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS X.1)).obj
          ((smallEtaleInverseImageRing B S hS f).obj (smallEtaleRingedTopos B S hS Y).O)) ≅
      (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS U.1)).obj
        ((smallEtaleInverseImageRing B S hS g).obj (smallEtaleRingedTopos B S hS V).O) :=
  etaleInverseImageSheafULiftIso B S hS p hp
      ((smallEtaleInverseImageRing B S hS f).obj (smallEtaleRingedTopos B S hS Y).O) ≪≫
    (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS U.1)).mapIso
      (smallEtaleRingedToposHom_squareInverseImageRingIso B S hS h ≪≫
        (smallEtaleInverseImageRing B S hS g).mapIso
          (etaleInverseImageStructureSheafIso B S hS q hq))

/-- The forward map of `AlgebraicGeometry.Space.etaleRestrictionCotangentSourceIso` is the
comparison with the universe lift followed by the lift of the two comparisons at the universe of
the structure rings. -/
lemma etaleRestrictionCotangentSourceIso_hom {p : U ⟶ X} {f : X ⟶ Y} {g : U ⟶ V} {q : V ⟶ Y}
    (hp : IsEtale B S hS p.hom) (hq : IsEtale B S hS q.hom) (h : p ≫ f = g ≫ q) :
    (etaleRestrictionCotangentSourceIso B S hS hp hq h).hom =
      (etaleInverseImageSheafULiftIso B S hS p hp
        ((smallEtaleInverseImageRing B S hS f).obj (smallEtaleRingedTopos B S hS Y).O)).hom ≫
        (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS U.1)).map
          ((smallEtaleRingedToposHom_squareInverseImageRingIso B S hS h).hom ≫
            (smallEtaleInverseImageRing B S hS g).map
              (etaleInverseImageStructureSheafIso B S hS q hq).hom) :=
  rfl

/-- **The comparisons form an isomorphism of arrows.**  For a commutative square
`p ≫ f = g ≫ q` of algebraic spaces with `p` and `q` étale, the comparison of the sources and
the clause `p⁻¹𝒪_X = 𝒪_U` of Stacks 03LV carry the structure map `g⁻¹𝒪_V ⟶ 𝒪_U` to the inverse
image along `p` of the structure map `f⁻¹𝒪_Y ⟶ 𝒪_X`, all at the universe of the small étale
sites.

On the universe of the structure rings this is the compatibility of the square comparison of
Stacks 03G8 with the structure maps, the two clauses of Stacks 03LV being those structure maps
for `p` and for `q`. -/
theorem etaleRestrictionCotangentSquare {p : U ⟶ X} {f : X ⟶ Y} {g : U ⟶ V} {q : V ⟶ Y}
    (hp : IsEtale B S hS p.hom) (hq : IsEtale B S hS q.hom) (h : p ≫ f = g ≫ q) :
    (smallToposMorphism B S hS p).inverseImageRing.map
          ((SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS X.1)).map
            (smallEtaleRingedToposHom B S hS f).fSharpInverseImage) ≫
        (etaleInverseImageStructureSheafULiftIso B S hS p hp).hom =
      (etaleRestrictionCotangentSourceIso B S hS hp hq h).hom ≫
        (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS U.1)).map
          (smallEtaleRingedToposHom B S hS g).fSharpInverseImage := by
  have key : (smallEtaleInverseImageRing B S hS p).map
          (smallEtaleRingedToposHom B S hS f).fSharpInverseImage ≫
        (etaleInverseImageStructureSheafIso B S hS p hp).hom =
      ((smallEtaleRingedToposHom_squareInverseImageRingIso B S hS h).hom ≫
          (smallEtaleInverseImageRing B S hS g).map
            (etaleInverseImageStructureSheafIso B S hS q hq).hom) ≫
        (smallEtaleRingedToposHom B S hS g).fSharpInverseImage :=
    ((Category.assoc _ _ _).trans
      (smallEtaleRingedToposHom_squareInverseImageRingIso_fSharpInverseImage B S hS h)).symm
  rw [etaleInverseImageStructureSheafULiftIso_eq, etaleRestrictionCotangentSourceIso_hom,
    ← Category.assoc, etaleInverseImageSheafULiftIso_naturality, Category.assoc, Category.assoc,
    ← CategoryTheory.Functor.map_comp
      (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS U.1)),
    ← CategoryTheory.Functor.map_comp
      (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS U.1))]
  exact congrArg (fun k => _ ≫ (SheafOfModules.sheafULift.{u, u + 1, u}
    (SmallEtale.topology B S hS U.1)).map k) key

/-- Restriction of `𝒪_X`-modules to the small étale site of `U` along an étale morphism
`p : U ⟶ X` of algebraic spaces: the inverse image of sheaves of modules along the morphism of
small étale topoi, with its coefficients read over `𝒪_U` through the clause `p⁻¹𝒪_X = 𝒪_U` of
Stacks 03LV.  This is the functor written `𝒢 ↦ 𝒢|_{U_étale}` in Stacks 03LW. -/
noncomputable abbrev etaleRestrictModules (p : U ⟶ X) (hp : IsEtale B S hS p.hom) :
    smallEtaleModulesULift B S hS X ⥤ smallEtaleModulesULift B S hS U :=
  CategoryTheory.Sheaf.inverseImageTargetModules.{u + 1, u, u, u + 1, u, u}
      (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS X.1)
      (smallToposMorphism B S hS p) ⋙
    (CategoryTheory.Sheaf.targetModulesTransport.{u + 1, u, u}
      (SmallEtale.topology B S hS U.1)
      (etaleInverseImageStructureSheafULiftIso B S hS p hp)).functor

/-- For a commutative diagram of algebraic spaces over a scheme `S`

```
U --g--> V
|p       |q
X --f--> Y
```

with `p` and `q` étale, the restriction of the cotangent complex `L_{X/Y}` to the small étale
site of `U` is the cotangent complex `L_{U/V}`:

`L_{X/Y}|_{U_étale} = L_{U/V}`.

Formation of the cotangent complex commutes with inverse image (Stacks 08SV), and the structure
maps of `f` and of `g` are carried to one another by the comparisons of Stacks 03LV and
Stacks 03G8, which commute by `AlgebraicGeometry.Space.etaleRestrictionCotangentSquare`; square
functoriality of the cotangent complex then transports the complex. -/
@[stacks 08VE]
noncomputable def etaleRestrictionCotangentComplexIso {p : U ⟶ X} {f : X ⟶ Y} {g : U ⟶ V}
    {q : V ⟶ Y} (hp : IsEtale B S hS p.hom) (hq : IsEtale B S hS q.hom) (h : p ≫ f = g ≫ q) :
    ((etaleRestrictModules B S hS p hp).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex B S hS f) ≅
      cotangentComplex B S hS g :=
  ((CategoryTheory.Sheaf.targetModulesTransport.{u + 1, u, u} (SmallEtale.topology B S hS U.1)
          (etaleInverseImageStructureSheafULiftIso B S hS p hp)).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso
      (CategoryTheory.Sheaf.inverseImageCotangentComplexIso.{u + 1, u, u, u + 1, u, u}
          (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS X.1)
          (smallToposMorphism B S hS p)
          ((SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS X.1)).map
            (smallEtaleRingedToposHom B S hS f).fSharpInverseImage) ≪≫
        CategoryTheory.Sheaf.squareCotangentComplexIso.{u + 1, u, u}
          (etaleRestrictionCotangentSquare B S hS hp hq h)) ≪≫
    ((CategoryTheory.Sheaf.targetModulesTransport.{u + 1, u, u} (SmallEtale.topology B S hS U.1)
        (etaleInverseImageStructureSheafULiftIso B S hS p hp)).mapHomologicalComplex
      (ComplexShape.up ℤ)).counitIso.app (cotangentComplex B S hS g)

end AlgebraicGeometry.Space

end
