module

public import StacksFrontier.Deformation.Artin.Infinitesimal.SquareZeroBaseChange
public import StacksFrontier.Deformation.Artin.Obstruction.FieldCohomology

/-!
# The charted transitions of Stacks 07YA are the site-level ones

For a pair of `Deformation.Artin.ChartedObject`s, the transitions of Stacks 07YA — the morphism
`Spec C[N] ⟶ Spec A[M]` determined by a ring map `f : A ⟶ C` and an `f`-semilinear map
`M ⟶ N`, the induced relation on classes of lifts, and the induced relation on infinitesimal
automorphisms — are the site-level ones (`Deformation.Artin.IsSiteSquareZeroBaseMap`,
`Deformation.Artin.IsSiteSquareZeroLiftBaseChange` and
`Deformation.Artin.IsSiteInfinitesimalAutomorphismBaseChange`) at the two algebras of the charted
objects.

## Main results

* `Deformation.Artin.isSquareZeroBaseMap_iff_isSiteSquareZeroBaseMap`,
  `Deformation.Artin.isSquareZeroLiftBaseChange_iff_isSiteSquareZeroLiftBaseChange` and, in the
  same namespace,
  `isInfinitesimalAutomorphismBaseChange_iff_isSiteInfinitesimalAutomorphismBaseChange` — the
  charted transitions of Stacks 07YA agree with the site-level ones.
* `Deformation.Artin.isSiteSquareZeroBaseMap_squareZeroOverBaseMap` — the morphism
  `Spec A'[N] ⟶ Spec A[M]` induced by a ring map and a semilinear map of coefficients is a
  site-level square-zero base map.

## References

* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin

/-! ### The site-level base map of a ring map and a semilinear map -/

section SiteBaseMap

/-- The morphism `Spec A'[N] ⟶ Spec A[M]` induced by a ring map `A ⟶ A'` and an
`f`-semilinear map of coefficients is a square-zero base map of Stacks 07YA. -/
public theorem isSiteSquareZeroBaseMap_squareZeroOverBaseMap {A A' : Type u} [CommRing A]
    [CommRing A'] (f : A →+* A') (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (toS : Spec (.of A) ⟶ S) (toS' : Spec (.of A') ⟶ S)
    (hf : Spec.map (CommRingCat.ofHom f) ≫ toS = toS')
    {M : SiteModule A B} {N : SiteModule A' B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    IsSiteSquareZeroBaseMap B S hS toS toS' f ψ
      (squareZeroOverBaseMap f B S hS toS toS' hf M N (restrictScalarsAddHom f ψ)
        (restrictScalarsAddHom_smul f ψ)) :=
  ⟨squareZeroRingBaseMap f (restrictScalarsAddHom f ψ) (restrictScalarsAddHom_smul f ψ),
    fun _ => rfl, rfl⟩

end SiteBaseMap

/-! ### The charted transitions are the site-level ones -/

section ChartedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {c : AffineChart S}

/-- The charted square-zero base map of Stacks 07YA is the site-level one at the two algebras
of the charted objects. -/
public theorem isSquareZeroBaseMap_iff_isSiteSquareZeroBaseMap
    {P Q : ChartedObject B S hS p c} (f : P.ring →+* Q.ring)
    {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (g : Q.squareZeroBase N ⟶ P.squareZeroBase M) :
    IsSquareZeroBaseMap f ψ g ↔
      IsSiteSquareZeroBaseMap B S hS P.obj.alg.toScheme Q.obj.alg.toScheme f ψ g :=
  Iff.rfl

/-- The charted transition of Stacks 07YA on classes of lifts is the site-level one at the two
algebras and points of the charted objects. -/
public theorem isSquareZeroLiftBaseChange_iff_isSiteSquareZeroLiftBaseChange
    {P Q : ChartedObject B S hS p c} (h : AffineObject.Hom P.obj Q.obj) (f : P.ring →+* Q.ring)
    {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (a : P.liftClasses M) (b : Q.liftClasses N) :
    IsSquareZeroLiftBaseChange h f ψ a b ↔
      IsSiteSquareZeroLiftBaseChange B S hS P.obj.alg.toScheme P.obj.alg.mem
        Q.obj.alg.toScheme Q.obj.alg.mem p P.point Q.point P.obj.obj.2 Q.obj.obj.2
        h.objMap f ψ a b :=
  Iff.rfl

/-- The charted transition of Stacks 07YA on infinitesimal automorphisms is the site-level one
at the two algebras and points of the charted objects. -/
public theorem
    isInfinitesimalAutomorphismBaseChange_iff_isSiteInfinitesimalAutomorphismBaseChange
    {P Q : ChartedObject B S hS p c} (hp : p.IsFiberedInGroupoids)
    (h : AffineObject.Hom P.obj Q.obj) (f : P.ring →+* Q.ring)
    {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (θ : P.trivialLift hp M ⟶ P.trivialLift hp M)
    (θ' : Q.trivialLift hp N ⟶ Q.trivialLift hp N) :
    IsInfinitesimalAutomorphismBaseChange hp h f ψ θ θ' ↔
      IsSiteInfinitesimalAutomorphismBaseChange B S hS P.obj.alg.toScheme P.obj.alg.mem
        Q.obj.alg.toScheme Q.obj.alg.mem p P.point Q.point P.obj.obj.2 Q.obj.obj.2
        h.objMap f ψ hp θ θ' :=
  Iff.rfl

end ChartedSite

end Deformation.Artin

end
