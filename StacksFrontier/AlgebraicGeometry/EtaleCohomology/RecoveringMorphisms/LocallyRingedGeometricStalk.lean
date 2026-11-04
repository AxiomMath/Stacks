module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.MorphismsGeneral
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.StalkReflectsUnits
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.ToposHomUnitsSquare
public import StacksFrontier.CategoryTheory.Sites.Sheaf.HasSheafComposeForgetRing
public import StacksFrontier.RingTheory.Etale.StandardPresentationSolutions
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The étale stalks in the proof of Stacks 04I6

Step (3) of the proof of [Stacks Project, Tag 04I6] checks on stalks that the comparison
`g⁻¹h_V ⟶ h_{X ×_Y V}` attached to a morphism of locally ringed topoi
`(g, g^♯) : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` is an isomorphism.  Its stalk is the map of
solution sets of a standard étale presentation induced by `(g^♯)_p`, and the input the source
needs there is that `(g^♯)_p` is a *local* homomorphism of *strictly henselian* local rings, so
that [Stacks Project, Tag 04GX] applies.  This file supplies those two inputs.

Locality is the only place the *locally* ringed hypothesis is used in the whole proof: it is the
cartesian units square of Stacks 04HA, read at the stalk functor of a geometric point through
Stacks 04H9.

## Main definitions

* `AlgebraicGeometry.smallEtaleStalkRing` — the stalk of the structure sheaf of the small étale
  site of a scheme at a point of that site, as a commutative ring.

## Main results

* `AlgebraicGeometry.reflectsUnitsObj_geometricPointSitePoint_of_isLocallyRinged` and
  `AlgebraicGeometry.isLocalHom_sheafFiber_fSharpInverseImage_of_isLocallyRinged` — for a
  locally ringed `(g, g^♯)`, the stalk of `g^♯ : g⁻¹𝒪_Y ⟶ 𝒪_X` at a geometric point of `X` is a
  local ring homomorphism.
* `AlgebraicGeometry.strictlyHenselianLocalRing_smallEtaleStalkRing` — the stalk of the
  structure sheaf at *any* point of the small étale site is strictly henselian, every such
  point being a geometric point by Stacks 04HU.
* `AlgebraicGeometry.bijective_homOverMap_smallEtaleStalkRing` — Stacks 04GX at those stalks: a
  local homomorphism between them carries the points of a standard étale presentation
  bijectively.

## References

* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
* [Stacks Project, Tag 04H9](https://stacks.math.columbia.edu/tag/04H9)
* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
* [Stacks Project, Tag 04HU](https://stacks.math.columbia.edu/tag/04HU)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-! ### Locality of the stalk of the structure map -/

section LocallyRinged

variable {X Y : B.Scheme}

/-- **Condition (3) of Stacks 04H9 at a geometric point, for a morphism of small étale ringed
topoi.** The stalk functor at a geometric point of `X` is left exact, so a locally ringed
`(g, g^♯)` has units reflected by it. -/
theorem reflectsUnitsObj_geometricPointSitePoint_of_isLocallyRinged
    (g : RingedToposHom
      (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (hg : g.IsLocallyRinged) (x : GeometricPoint X.obj) :
    RingedTopos.ReflectsUnitsObj
      ((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u))
      g.fSharpInverseImage :=
  g.reflectsUnitsObj_of_isLocallyRinged hg _

/-- **The geometric stalk of the structure map of a locally ringed morphism of small étale
ringed topoi is local.** For `(g, g^♯)` a morphism of the small étale ringed topoi of `X` and
`Y` which is locally ringed in the sense of Stacks 04HA, and for a geometric point `x` of `X`,
the stalk at `x` of `g^♯ : g⁻¹𝒪_Y ⟶ 𝒪_X` is a local homomorphism.

This is the only step of the proof of Stacks 04I6 that uses the locally ringed hypothesis. -/
theorem isLocalHom_sheafFiber_fSharpInverseImage_of_isLocallyRinged
    (g : RingedToposHom
      (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (hg : g.IsLocallyRinged) (x : GeometricPoint X.obj) :
    IsLocalHom (((geometricPointSitePoint B X.obj X.property x).sheafFiber
      (A := CommRingCat.{u})).map g.fSharpInverseImage).hom :=
  RingedTopos.isLocalHom_sheafFiber_of_reflectsUnitsObj _ _
    (reflectsUnitsObj_geometricPointSitePoint_of_isLocallyRinged B g hg x)

end LocallyRinged

/-! ### The stalks are strictly henselian -/

variable (S : Scheme.{u}) (hS : B.Contains S)

/-- The stalk of the structure sheaf of the small étale site of `S` at a point of that site, as
a commutative ring. At a geometric point this is the étale local ring of Stacks 03PS. -/
abbrev smallEtaleStalkRing (p : (SmallEtale.topology B S hS).Point.{u}) : CommRingCat.{u} :=
  (p.sheafFiber (A := CommRingCat.{u})).obj (smallEtaleRingedSite B S hS).O

/-- The stalk of the structure sheaf at a geometric point is strictly henselian: it is the
étale local ring of Stacks 03PS, which is a strict henselization. -/
@[sga "4½ Arcata 2.3.1" "special case"]
theorem strictlyHenselianLocalRing_smallEtaleStalkRing_geometricPointSitePoint
    (s : GeometricPoint S) :
    StrictlyHenselianLocalRing ↥(smallEtaleStalkRing B S hS (geometricPointSitePoint B S hS s)) :=
  have := etaleLocalRing_strictHenselian B S hS s
  strictlyHenselianLocalRing_of_ringEquiv
    (commRingEtaleStalkForgetIso B S hS s).ringCatIsoToRingEquiv.symm

/-- **The stalk of the structure sheaf at any point of the small étale site is strictly
henselian.** Every point of the small étale site of `S` is isomorphic to the point attached to a
geometric point of `S`, by Stacks 04HU, and the stalk there is the étale local ring.

This is one of the two inputs that Stacks 04GX needs in step (3) of the proof of
Stacks 04I6. -/
instance strictlyHenselianLocalRing_smallEtaleStalkRing
    (p : (SmallEtale.topology B S hS).Point.{u}) :
    StrictlyHenselianLocalRing ↥(smallEtaleStalkRing B S hS p) := by
  obtain ⟨s, ⟨e⟩⟩ := exists_geometricPoint_sitePoint_iso B S hS p
  let E : (geometricPointSitePoint B S hS s).presheafFiber (A := CommRingCat.{u}) ≅
      p.presheafFiber (A := CommRingCat.{u}) :=
    { hom := e.hom.presheafFiber
      inv := e.inv.presheafFiber
      hom_inv_id := by
        rw [← GrothendieckTopology.Point.Hom.presheafFiber_comp, e.inv_hom_id,
          GrothendieckTopology.Point.Hom.presheafFiber_id]
      inv_hom_id := by
        rw [← GrothendieckTopology.Point.Hom.presheafFiber_comp, e.hom_inv_id,
          GrothendieckTopology.Point.Hom.presheafFiber_id] }
  have h : StrictlyHenselianLocalRing
      ↥(((geometricPointSitePoint B S hS s).presheafFiber (A := CommRingCat.{u})).obj
        (SmallEtale.commRingStructurePresheaf B S hS)) :=
    strictlyHenselianLocalRing_smallEtaleStalkRing_geometricPointSitePoint B S hS s
  exact strictlyHenselianLocalRing_of_ringEquiv
    (E.app (SmallEtale.commRingStructurePresheaf B S hS)).commRingCatIsoToRingEquiv

/-! ### Stacks 04GX at the étale stalks -/

/-- **Stacks 04GX at the stalks of the structure sheaves of two small étale sites.** Let `p` be a
point of the small étale site of `X`, let `q` be one of the small étale site of `Y`, let
`φ : (𝒪_Y)_q ⟶ (𝒪_X)_p` be a local homomorphism of their structure-sheaf stalks, and let
`P₁, …, P_n` present a ring étale over `(𝒪_Y)_q`. Then postcomposition with `φ` is a bijection
from the points of that presentation with values in `(𝒪_Y)_q` onto those with values
in `(𝒪_X)_p`.

Both stalks are strictly henselian local rings by
`AlgebraicGeometry.strictlyHenselianLocalRing_smallEtaleStalkRing`, so this is
`MvPolynomial.bijective_homOverMap_of_etale` with its hypotheses on the stalks discharged. In
step (3) of the proof of Stacks 04I6 the map `φ` is the stalk of `g^♯`, which is local by
`AlgebraicGeometry.isLocalHom_sheafFiber_fSharpInverseImage_of_isLocallyRinged`, and this
bijection is the stalk of the comparison `g⁻¹h_V ⟶ h_{X ×_Y V}`. -/
theorem bijective_homOverMap_smallEtaleStalkRing {X Y : Scheme.{u}} (hX : B.Contains X)
    (hY : B.Contains Y) (p : (SmallEtale.topology B X hX).Point.{u})
    (q : (SmallEtale.topology B Y hY).Point.{u})
    (φ : ↥(smallEtaleStalkRing B Y hY q) →+* ↥(smallEtaleStalkRing B X hX p))
    (hφ : IsLocalHom φ) {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n) ↥(smallEtaleStalkRing B Y hY q))
    [Algebra.Etale ↥(smallEtaleStalkRing B Y hY q)
      (MvPolynomial (Fin n) ↥(smallEtaleStalkRing B Y hY q) ⧸ Ideal.span (Set.range P))] :
    Function.Bijective
      (fun t : MvPolynomial.HomOver P (RingHom.id ↥(smallEtaleStalkRing B Y hY q)) =>
        (⟨φ.comp t.1, by rw [RingHom.comp_assoc, t.2, RingHom.comp_id]⟩ :
          MvPolynomial.HomOver P φ)) :=
  MvPolynomial.bijective_homOverMap_of_etale P φ hφ

end AlgebraicGeometry

end
