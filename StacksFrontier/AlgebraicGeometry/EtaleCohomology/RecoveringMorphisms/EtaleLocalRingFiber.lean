module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkInverseImageModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.CompositeGeometricPoint
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The étale local ring of the target as the fibre of the inverse image, as a ring

Let `(g, g^♯)` be a morphism of the small étale ringed topoi of two schemes `X` and `Y` of a big
étale site, let `x̄` be a geometric point of `X` and let `ȳ` be a geometric point of `Y` whose
geometric stalk functor is `g⁻¹` followed by the geometric stalk functor at `x̄`
(`AlgebraicGeometry.exists_geometricPoint_inverseImage_comp_sheafFiber_iso`).

This file produces from those data the **local homomorphism of étale local rings**

`𝒪^{ét}_{Y,ȳ} ⟶ 𝒪^{ét}_{X,x̄}`

which step (3) of the proof of [Stacks Project, Tag 04I6] runs [Stacks Project, Tag 04GX] along.
Two things have to be supplied: that the identification of `𝒪^{ét}_{Y,ȳ}` with the fibre at `x̄` of
`g⁻¹𝒪_Y` is an isomorphism of *rings*, not merely of sets; and that the composite with the fibre
of the structure map `g⁻¹𝒪_Y ⟶ 𝒪_X` is a local homomorphism.

## The ring half is not new

One might expect the ring half to be out of reach, because
`AlgebraicGeometry.exists_geometricPoint_inverseImage_comp_sheafFiber_iso` factors through
`PointOfTopos.sheafFiberIsoInverseImage`, whose target is Type-valued because a point of a topos
has a Type-valued inverse image by definition.  That is a correct description of *that* route, but
the conclusion does not follow: **the ring half is in the library**, for an arbitrary morphism of
topoi, as
`Stacks.Sheaves.StalkInverseImage.stalkRingEquiv` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/StalkInverseImageModules.lean`.  Its input is
precisely the Type-level isomorphism of stalk functors that
`exists_geometricPoint_inverseImage_comp_sheafFiber_iso` supplies — taken there as a datum rather
than derived, exactly so that no smallness condition on either site is needed — and its output is
a `RingEquiv` between the `RingCat`-valued fibre of a sheaf of rings at the target point and the
`RingCat`-valued fibre of its inverse image at the source point.

It is not formal: the ring
structure on the fibre of an inverse image is a *transported* structure, carried along
`CategoryTheory.Sheaf.ringObjRing` by the finite-product-preserving functor `g⁻¹ ⋙ Φ⁻¹`, and the
identification with the honest colimit-valued fibre of a sheaf of rings is checked on germs
(`Stacks.Sheaves.StalkTransport.ringStalkComparison_ringAddObj` and
`ringStalkComparison_ringMulObj`, each proved by extracting a common neighbourhood).  What this
file adds is only the passage between the spellings the two sides use: the étale local ring is the
`RingCat`-valued fibre of `AlgebraicGeometry.SmallEtale.structureSheaf`, whereas a ringed topos
carries its structure sheaf in `CommRingCat`, and the comparison of the two fibres is
`AlgebraicGeometry.commRingEtaleStalkForgetIso`.

## Main definitions

* `AlgebraicGeometry.etaleCommRingFiberEquiv` — the `CommRingCat`-valued fibre at a geometric point
  of the structure sheaf of commutative rings is the étale local ring there.
* `AlgebraicGeometry.etaleLocalRingEquivInverseImageFiber` — **the prerequisite**: the étale local
  ring `𝒪^{ét}_{Y,ȳ}` is, as a ring, the fibre at `x̄` of `g⁻¹𝒪_Y`.
* `AlgebraicGeometry.etaleLocalRingHomOfSheafFiberIso` — the induced ring homomorphism
  `𝒪^{ét}_{Y,ȳ} ⟶ 𝒪^{ét}_{X,x̄}`, namely that isomorphism followed by the fibre at `x̄` of the
  structure map `g⁻¹𝒪_Y ⟶ 𝒪_X`.

## Main results

* `AlgebraicGeometry.isLocalHom_etaleLocalRingHomOfSheafFiberIso` — for `(g, g^♯)` *locally*
  ringed, that homomorphism is **local**.  This is the hypothesis of
  [Stacks Project, Tag 04GX]; its two rings are strictly henselian by
  `AlgebraicGeometry.etaleLocalRing_strictHenselian`.
* `AlgebraicGeometry.exists_geometricPoint_isLocalHom_etaleLocalRingHom` — the two together with
  the geometric point `ȳ` produced, which is the form step (3) of [Stacks Project, Tag 04I6]
  consumes.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
* [Stacks Project, Tag 05V1](https://stacks.math.columbia.edu/tag/05V1)
* [Stacks Project, Tag 00YA](https://stacks.math.columbia.edu/tag/00YA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.StalkInverseImage
open Stacks.Sheaves.ToposPushforward

universe u

namespace Stacks.Sheaves.StalkGerm

variable {C : Type*} [Category C] {J : GrothendieckTopology C} (Φ : J.Point.{u})
  {A : Type*} [Category A] [Limits.HasColimitsOfSize.{u, u} A]

/-- **Germs are carried to germs by an equality of presheaves.**  An equality `P = Q` of
presheaves induces an equality of their fibres at a point of the site, and the resulting
`eqToHom` carries the germ at `(W, u)` of a section of `P` to the germ of the same section read
in `Q`.

It is the degenerate case of naturality of the germ maps, and it is separated out because the two
spellings of the structure presheaf of the small étale site — in `RingCat`, and in `CommRingCat`
with commutativity forgotten — are equal rather than identical. -/
theorem toPresheafFiber_eqToHom {P Q : Cᵒᵖ ⥤ A} (h : P = Q) (W : C) (u : Φ.fiber.obj W)
    (h' : P.obj (Opposite.op W) = Q.obj (Opposite.op W)) :
    Φ.toPresheafFiber W u P ≫ eqToHom (congrArg (Φ.presheafFiber (A := A)).obj h) =
      eqToHom h' ≫ Φ.toPresheafFiber W u Q := by
  subst h
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

end Stacks.Sheaves.StalkGerm

namespace AlgebraicGeometry

/-- A ring homomorphism conjugated at either end by a ring isomorphism is local as soon as it is:
ring isomorphisms reflect units. -/
private theorem isLocalHom_comp_ringEquiv {R S T U : Type*} [Semiring R] [Semiring S]
    [Semiring T] [Semiring U] (ε : R ≃+* S) (F : S →+* T) (δ : T ≃+* U) (hF : IsLocalHom F) :
    IsLocalHom ((δ.toRingHom.comp F).comp ε.toRingHom) := by
  refine ⟨fun a h => ?_⟩
  have h₁ : IsUnit (F (ε a)) := by simpa using h.map δ.symm.toRingHom
  simpa using (hF.map_nonunit _ h₁).map ε.symm.toRingHom

/-- **The étale local ring is the `CommRingCat`-valued geometric fibre of the structure sheaf.**
The structure sheaf of the small étale *ringed* site takes values in `CommRingCat`, while the
étale local ring of Stacks 03PS is the fibre of the `RingCat`-valued structure sheaf; the two
fibres are the same filtered colimit, because the forgetful functor `CommRingCat ⥤ RingCat`
preserves it.

`AlgebraicGeometry.commRingEtaleStalkForgetIso` is the same isomorphism, but built from
`CategoryTheory.Limits.preservesColimitIso`; the spelling here is the composite of the general
comparison `Stacks.commRingPresheafFiberIso` with the equality of presheaves
`AlgebraicGeometry.commRingStructurePresheaf_comp_forget₂`, and it is used because *that* one
can be computed on germs
(`AlgebraicGeometry.toPresheafFiber_comp_etaleLocalRingIsoCommFiber`), which the coefficient
compatibility of step (3) of [Stacks Project, Tag 04I6] needs. -/
def etaleLocalRingIsoCommFiber (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S) :
    etaleLocalRing B S hS s ≅
      (forget₂ CommRingCat.{u} RingCat.{u}).obj
        (Stacks.ringFiber (geometricPointSitePoint B S hS s)
          (SmallEtale.commRingStructurePresheaf B S hS)) :=
  eqToIso (congrArg ((geometricPointSitePoint B S hS s).presheafFiber (A := RingCat.{u})).obj
      (commRingStructurePresheaf_comp_forget₂ B S hS).symm) ≪≫
    Stacks.commRingPresheafFiberIso (geometricPointSitePoint B S hS s)
      (SmallEtale.commRingStructurePresheaf B S hS)

/-- A germ in the `RingCat`-valued structure sheaf, transported along the equality
`commRingStructurePresheaf_comp_forget₂`, is the germ in the `CommRingCat`-valued one. -/
private theorem toPresheafFiber_structureSheaf_comp_eqToHom (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (s : GeometricPoint S) (W : SmallEtale B S hS)
    (u : (geometricPointSitePoint B S hS s).fiber.obj W) :
    (geometricPointSitePoint B S hS s).toPresheafFiber W u
          (SmallEtale.structureSheaf B S hS).obj ≫
        eqToHom (congrArg ((geometricPointSitePoint B S hS s).presheafFiber
            (A := RingCat.{u})).obj
          (commRingStructurePresheaf_comp_forget₂ B S hS).symm) =
      (geometricPointSitePoint B S hS s).toPresheafFiber W u
        (SmallEtale.commRingStructurePresheaf B S hS ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  (Stacks.Sheaves.StalkGerm.toPresheafFiber_eqToHom (geometricPointSitePoint B S hS s)
    (A := RingCat.{u}) (commRingStructurePresheaf_comp_forget₂ B S hS).symm W u rfl).trans
    (Category.id_comp _)

/-- **The comparison of the two spellings of the étale local ring carries germs to germs.**  The
germ at a pointed étale neighbourhood `(W, u)` of a global function on `W`, taken in the
`RingCat`-valued structure sheaf, is its germ taken in the `CommRingCat`-valued one. -/
theorem toPresheafFiber_comp_etaleLocalRingIsoCommFiber (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (s : GeometricPoint S) (W : SmallEtale B S hS)
    (u : (geometricPointSitePoint B S hS s).fiber.obj W) :
    (geometricPointSitePoint B S hS s).toPresheafFiber W u
          (SmallEtale.structureSheaf B S hS).obj ≫
        (etaleLocalRingIsoCommFiber B S hS s).hom =
      (forget₂ CommRingCat.{u} RingCat.{u}).map
        ((geometricPointSitePoint B S hS s).toPresheafFiber W u
          (SmallEtale.commRingStructurePresheaf B S hS)) := by
  change (geometricPointSitePoint B S hS s).toPresheafFiber W u
        (SmallEtale.structureSheaf B S hS).obj ≫
      (eqToHom (congrArg ((geometricPointSitePoint B S hS s).presheafFiber
            (A := RingCat.{u})).obj
          (commRingStructurePresheaf_comp_forget₂ B S hS).symm) ≫
        (Stacks.commRingPresheafFiberIso (geometricPointSitePoint B S hS s)
          (SmallEtale.commRingStructurePresheaf B S hS)).hom) = _
  rw [← Category.assoc, toPresheafFiber_structureSheaf_comp_eqToHom B S hS s W u,
    Stacks.commRingPresheafFiberIso, Iso.app_hom]
  exact (geometricPointSitePoint B S hS s).toPresheafFiber_presheafFiberCompIso_hom_app
    (F := forget₂ CommRingCat.{u} RingCat.{u}) W u (SmallEtale.commRingStructurePresheaf B S hS)

/-- **The `CommRingCat`-valued geometric fibre of the structure sheaf is the étale local ring.**
This is `AlgebraicGeometry.etaleLocalRingIsoCommFiber` read as a `RingEquiv`, in the direction
step (3) of [Stacks Project, Tag 04I6] consumes. -/
def etaleCommRingFiberEquiv (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S) :
    Stacks.ringFiber (geometricPointSitePoint B S hS s)
        (SmallEtale.commRingStructurePresheaf B S hS) ≃+* ↥(etaleLocalRing B S hS s) :=
  (etaleLocalRingIsoCommFiber B S hS s).ringCatIsoToRingEquiv.symm

/-- `AlgebraicGeometry.etaleCommRingFiberEquiv` carries the germ of a global function on a
pointed étale neighbourhood to its germ in the étale local ring.  The right-hand side is
`AlgebraicGeometry.etaleLocalRingGerm`, which is defined in a file this one does not import. -/
theorem etaleCommRingFiberEquiv_toPresheafFiber (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (s : GeometricPoint S) (W : SmallEtale B S hS)
    (u : (geometricPointSitePoint B S hS s).fiber.obj W)
    (t : Γ((SmallEtale.toScheme B S hS).obj W, ⊤)) :
    etaleCommRingFiberEquiv B S hS s
        (((geometricPointSitePoint B S hS s).toPresheafFiber W u
          (SmallEtale.commRingStructurePresheaf B S hS)).hom t) =
      ((geometricPointSitePoint B S hS s).toPresheafFiber W u
        (SmallEtale.structureSheaf B S hS).obj).hom t :=
  ((etaleLocalRingIsoCommFiber B S hS s).ringCatIsoToRingEquiv.symm_apply_eq).2
    (ConcreteCategory.congr_hom
      (toPresheafFiber_comp_etaleLocalRingIsoCommFiber B S hS s W u) t).symm

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme}
  (g : RingedToposHom
    (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
    (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
  (x : GeometricPoint X.obj) (y : GeometricPoint Y.obj)
  (e : (geometricPointSitePoint B Y.obj Y.property y).sheafFiber (A := Type u) ≅
    g.toToposHom.inverseImage ⋙
      (geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u))

/-- **The étale local ring of `Y` at `ȳ` is, as a ring, the fibre at `x̄` of `g⁻¹𝒪_Y`.**

This is the prerequisite which the proof of [Stacks Project, Tag 04I6] needs in order to read the
fibre at `x̄` of the structure map of `(g, g^♯)` as a homomorphism out of `𝒪^{ét}_{Y,ȳ}`: the
set-level identification is the hypothesis `e`, and the content is that it respects the transported
ring structure on the fibre of an inverse image.

The content is `Stacks.Sheaves.StalkInverseImage.stalkRingEquiv`, Stacks 05V1 for a sheaf of rings
along an arbitrary morphism of topoi; the two comparisons at either end pass between the
`CommRingCat`-valued fibre of the structure sheaf of the ringed topos and the `RingCat`-valued
fibre of the sheaf of rings underlying it. -/
def etaleLocalRingEquivInverseImageFiber :
    ↥(etaleLocalRing B Y.obj Y.property y) ≃+*
      ↥(((geometricPointSitePoint B X.obj X.property x).sheafFiber
        (A := CommRingCat.{u})).obj ((inverseImageCommRingFunctor g.toToposHom).obj
          (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)).O)) :=
  (eqToIso (congrArg ((geometricPointSitePoint B Y.obj Y.property y).presheafFiber
        (A := RingCat.{u})).obj
      (commRingStructurePresheaf_comp_forget₂ B Y.obj
        Y.property).symm)).ringCatIsoToRingEquiv.trans
    ((stalkRingEquiv g.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)).O)
          (geometricPointSitePoint B X.obj X.property x)
          (geometricPointSitePoint B Y.obj Y.property y) e).trans
      (Stacks.commRingPresheafFiberIso (geometricPointSitePoint B X.obj X.property x)
        ((inverseImageCommRingFunctor g.toToposHom).obj
          (RingedSite.toRingedTopos
            (smallEtaleRingedSite B Y.obj Y.property)).O).obj).ringCatIsoToRingEquiv)

/-- **The identification of `𝒪^{ét}_{Y,ȳ}` with the fibre at `x̄` of `g⁻¹𝒪_Y` carries a germ to
the image of that germ under the hypothesised isomorphism `e` of stalk functors.**

This is the computation on germs which the coefficient compatibility of step (3) of
[Stacks Project, Tag 04I6] runs on: the first factor is an equality of presheaves and so carries
germs to germs (`Stacks.Sheaves.StalkGerm.toPresheafFiber_eqToHom`), and the second is
`Stacks.Sheaves.StalkInverseImage.stalkRingMap_ringStalkComparison`, which is where `e` enters
and after which the only remaining `e`-dependence is the single application `e.hom.app`. -/
theorem etaleLocalRingEquivInverseImageFiber_toPresheafFiber
    (W : SmallEtale B Y.obj Y.property)
    (u : (geometricPointSitePoint B Y.obj Y.property y).fiber.obj W)
    (t : Γ((SmallEtale.toScheme B Y.obj Y.property).obj W, ⊤)) :
    etaleLocalRingEquivInverseImageFiber B g x y e
        (((geometricPointSitePoint B Y.obj Y.property y).toPresheafFiber W u
          (SmallEtale.structureSheaf B Y.obj Y.property).obj).hom t) =
      (Stacks.commRingPresheafFiberIso (geometricPointSitePoint B X.obj X.property x)
          ((inverseImageCommRingFunctor g.toToposHom).obj
            (RingedSite.toRingedTopos
              (smallEtaleRingedSite B Y.obj Y.property)).O).obj).ringCatIsoToRingEquiv
        (Stacks.Sheaves.StalkTransport.ringStalkComparison
          (geometricPointSitePoint B X.obj X.property x)
          (inverseImageRingSheaf g.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)).O))
          (e.hom.app (CategoryTheory.Sheaf.ringSheaf
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)).O))
            ((geometricPointSitePoint B Y.obj Y.property y).toPresheafFiber W u
              (CategoryTheory.Sheaf.ringSheaf
                (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSite.toRingedTopos
                  (smallEtaleRingedSite B Y.obj Y.property)).O)).obj t))) := by
  have hgerm : (eqToIso (congrArg
          ((geometricPointSitePoint B Y.obj Y.property y).presheafFiber
            (A := RingCat.{u})).obj
          (commRingStructurePresheaf_comp_forget₂ B Y.obj
            Y.property).symm)).ringCatIsoToRingEquiv
        (((geometricPointSitePoint B Y.obj Y.property y).toPresheafFiber W u
          (SmallEtale.structureSheaf B Y.obj Y.property).obj).hom t) =
      Stacks.Sheaves.StalkTransport.ringGerm (geometricPointSitePoint B Y.obj Y.property y)
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)).O) W u t :=
    ConcreteCategory.congr_hom
      (toPresheafFiber_structureSheaf_comp_eqToHom B Y.obj Y.property y W u) t
  refine (congrArg (fun z =>
    (Stacks.commRingPresheafFiberIso (geometricPointSitePoint B X.obj X.property x)
        ((inverseImageCommRingFunctor g.toToposHom).obj
          (RingedSite.toRingedTopos
            (smallEtaleRingedSite B Y.obj Y.property)).O).obj).ringCatIsoToRingEquiv
      (stalkRingEquiv g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)).O)
        (geometricPointSitePoint B X.obj X.property x)
        (geometricPointSitePoint B Y.obj Y.property y) e z)) hgerm).trans ?_
  refine congrArg
    (Stacks.commRingPresheafFiberIso (geometricPointSitePoint B X.obj X.property x)
        ((inverseImageCommRingFunctor g.toToposHom).obj
          (RingedSite.toRingedTopos
            (smallEtaleRingedSite B Y.obj Y.property)).O).obj).ringCatIsoToRingEquiv ?_
  rw [← Stacks.Sheaves.StalkTransport.ringStalkComparison_ringGerm
    (geometricPointSitePoint B Y.obj Y.property y)
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)).O)
    W u t]
  exact stalkRingMap_ringStalkComparison g.toToposHom _
    (geometricPointSitePoint B X.obj X.property x)
    (geometricPointSitePoint B Y.obj Y.property y) e _

/-- **The homomorphism `𝒪^{ét}_{Y,ȳ} ⟶ 𝒪^{ét}_{X,x̄}` of étale local rings** attached to a
morphism of small étale ringed topoi and a matched pair of geometric points: the identification of
`AlgebraicGeometry.etaleLocalRingEquivInverseImageFiber`, followed by the fibre at `x̄` of the
inverse-image form `g⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map.

This is the ring map along which step (3) of the proof of [Stacks Project, Tag 04I6] compares the
two solution sets; it is local by
`AlgebraicGeometry.isLocalHom_etaleLocalRingHomOfSheafFiberIso`. -/
def etaleLocalRingHomOfSheafFiberIso :
    ↥(etaleLocalRing B Y.obj Y.property y) →+* ↥(etaleLocalRing B X.obj X.property x) :=
  ((etaleCommRingFiberEquiv B X.obj X.property x).toRingHom.comp
      (((geometricPointSitePoint B X.obj X.property x).sheafFiber
        (A := CommRingCat.{u})).map g.fSharpInverseImage).hom).comp
    (etaleLocalRingEquivInverseImageFiber B g x y e).toRingHom

/-- **The homomorphism of étale local rings of a locally ringed morphism of small étale ringed
topoi is local.**

This is the only place the *locally* ringed hypothesis enters the proof of
[Stacks Project, Tag 04I6], and it is the hypothesis of [Stacks Project, Tag 04GX].  The fibre of
the structure map is local by
`AlgebraicGeometry.isLocalHom_geometricSheafFiber_fSharpInverseImage`; the remaining two factors
are ring isomorphisms, which reflect units. -/
theorem isLocalHom_etaleLocalRingHomOfSheafFiberIso (hg : g.IsLocallyRinged) :
    IsLocalHom (etaleLocalRingHomOfSheafFiberIso B g x y e) :=
  isLocalHom_comp_ringEquiv _ _ _
    (isLocalHom_geometricSheafFiber_fSharpInverseImage B g hg x)

/-- **The geometric point of `Y` and the local homomorphism of étale local rings which step (3) of
[Stacks Project, Tag 04I6] produces.**  For `(g, g^♯)` a locally ringed morphism of the small étale
ringed topoi of `X` and `Y` and `x̄` a geometric point of `X`, there is a geometric point `ȳ` of
`Y`, an identification of the geometric stalk functor at `ȳ` with `g⁻¹` followed by the geometric
stalk functor at `x̄`, and a **local** homomorphism `𝒪^{ét}_{Y,ȳ} ⟶ 𝒪^{ét}_{X,x̄}` of étale local
rings.

The geometric point and the identification are
`AlgebraicGeometry.exists_geometricPoint_inverseImage_comp_sheafFiber_iso`; the homomorphism is
`AlgebraicGeometry.etaleLocalRingHomOfSheafFiberIso` and its locality is
`AlgebraicGeometry.isLocalHom_etaleLocalRingHomOfSheafFiberIso`.

Both of its rings are strictly henselian local rings by
`AlgebraicGeometry.etaleLocalRing_strictHenselian`, so this is exactly the datum
[Stacks Project, Tag 04GX] — `MvPolynomial.bijective_homOverMap_of_etale` — is stated for. -/
@[sga "4 IV 13.9" "c), special case"]
theorem exists_geometricPoint_isLocalHom_etaleLocalRingHom (hg : g.IsLocallyRinged) :
    ∃ (y : GeometricPoint Y.obj)
      (e : (geometricPointSitePoint B Y.obj Y.property y).sheafFiber (A := Type u) ≅
        g.toToposHom.inverseImage ⋙
          (geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u)),
      IsLocalHom (etaleLocalRingHomOfSheafFiberIso B g x y e) := by
  obtain ⟨y, ⟨i⟩⟩ := exists_geometricPoint_inverseImage_comp_sheafFiber_iso B
    X.property Y.property g.toToposHom x
  exact ⟨y, i.symm, isLocalHom_etaleLocalRingHomOfSheafFiberIso B g x y i.symm hg⟩

end AlgebraicGeometry

end
