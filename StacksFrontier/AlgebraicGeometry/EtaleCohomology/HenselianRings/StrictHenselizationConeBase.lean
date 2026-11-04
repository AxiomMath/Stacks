module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationLimit
public import StacksFrontier.AlgebraicGeometry.RelativeSpecRepresentability.Basic
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleLocalRing

/-!
# The structure morphism of the strict henselization is the leg of the limit cone

Let `B` be a big étale site containing a scheme `S` and let `s` be a geometric point of `S`.
There are two morphisms from the strict henselization of `S` at `s` to `S`. One,
`AlgebraicGeometry.strictHenselizationToBase`, is built from the canonical map of the local ring
at the image of `s` into the étale local ring, by taking spectra and composing with the canonical
morphism from the spectrum of a local ring of `S`. The other,
`AlgebraicGeometry.strictHenselizationConeToBase`, is the leg at the terminal neighborhood of the
cone exhibiting the strict henselization as the limit of the étale neighborhoods. This file proves
that the two agree.

## Main results

* `AlgebraicGeometry.strictHenselizationCone_π_appTop`: the leg of the limit cone at an étale
  neighborhood is, on global functions, the germ at the geometric point — that is, the structure
  map of the colimit defining the étale local ring. This is proved first over the small cofinal
  family of affine neighborhoods, where the two bridge lemmas of
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationLimit` compute
  the leg, and then transported to an arbitrary neighborhood by cofinality.
* `AlgebraicGeometry.strictHenselizationConeToBase_eq`: **the structure morphism of the limit
  cone is the canonical structure morphism of the strict henselization.**
* `AlgebraicGeometry.strictHenselizationCone_π_comp_hom_eq`: consequently every leg of the cone,
  followed by the structure morphism of its neighborhood, is that canonical morphism; so the cone
  is a cone over `S` through `AlgebraicGeometry.strictHenselizationToBase`.

## Implementation notes

The comparison is a germ computation, not an argument about abstract isomorphisms. Both morphisms
are tested against an affine open `U` of `S` containing the image of the geometric point. The
canonical morphism factors through `U` by the standard description of the morphism from the
spectrum of a local ring, and the cone leg factors through `U` because `U`, regarded as a Zariski
étale neighborhood, carries a leg of the cone. Since the inclusion of `U` is a monomorphism and
`U` is affine, the two factorizations agree as soon as they agree on global functions over `U`,
and there both sides are the germ at the geometric point: for the cone leg by
`AlgebraicGeometry.strictHenselizationCone_π_appTop`, for the canonical morphism by the germ
compatibility of the ordinary-to-étale map of Tag 04HX.

## References

* [Stacks Project, Tag 03PS](https://stacks.math.columbia.edu/tag/03PS)
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- The leg of the strict henselization cone at an étale neighborhood is the identification of
the strict henselization with the limit, followed by the limit projection. -/
theorem strictHenselizationCone_π_app (V : (geometricPointFiber B S hS s).Elements) :
    (strictHenselizationCone B S hS s).π.app V =
      (strictHenselizationIsoLimit B S hS s).hom ≫
        limit.π (etaleNeighborhoodDiagram B S hS s) V :=
  rfl

/-- Over the small affine family, the leg of the cone on global functions is the limit
projection followed by the identification of the sections of the limit with the étale local
ring. -/
private theorem strictHenselizationIsoAffineLimit_π_appTop_ΓSpecIso
    (a : etaleNeighborhoodAffineIndex B S hS s) :
    ((strictHenselizationIsoAffineLimit B S hS s).hom ≫
        limit.π (etaleNeighborhoodAffineDiagram B S hS s) a).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of ↥(etaleLocalRing B S hS s))).hom =
    (limit.π (etaleNeighborhoodAffineDiagram B S hS s) a).appTop ≫
      (RingEquiv.toCommRingCatIso (etaleNeighborhoodAffineLimitRingEquiv B S hS s)).hom := by
  rw [strictHenselizationIsoAffineLimit, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.op_hom, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
    Stacks.RelativeSpec.isoSpec_inv_appTop, Scheme.Spec_map, Category.assoc, Category.assoc,
    Scheme.ΓSpecIso_naturality]
  exact congrArg (fun z => Scheme.Hom.appTop
    (limit.π (etaleNeighborhoodAffineDiagram B S hS s) a) ≫ z) (Iso.inv_hom_id_assoc _ _)

/-- **The leg of the cone at a member of the small affine family is the germ at the geometric
point on global functions.** -/
theorem strictHenselizationCone_π_appTop_affine (a : etaleNeighborhoodAffineIndex B S hS s)
    (b : Γ((etaleNeighborhoodAffineDiagram B S hS s).obj a, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of ↥(etaleLocalRing B S hS s))).hom.hom
        (((strictHenselizationCone B S hS s).π.app
          ((etaleNeighborhoodAffineInclusion B S hS s).obj a)).appTop.hom b) =
      (colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
        (SmallEtale.structureSheaf B S hS).obj)
          (op ((etaleNeighborhoodAffineInclusion B S hS s).obj a))).hom b := by
  have h1 : (strictHenselizationCone B S hS s).π.app
      ((etaleNeighborhoodAffineInclusion B S hS s).obj a) =
      (strictHenselizationIsoAffineLimit B S hS s).hom ≫
        limit.π (etaleNeighborhoodAffineDiagram B S hS s) a :=
    strictHenselizationAffineCone_π_app B S hS s a
  have h2 := congrArg (fun f => CommRingCat.Hom.hom f b)
    (strictHenselizationIsoAffineLimit_π_appTop_ΓSpecIso B S hS s a)
  have h3 := congrArg (fun f => RingCat.Hom.hom f b)
    (etaleNeighborhoodAffineLimitSectionsRingCatIso_π_appTop B S hS s a)
  simp only at h2 h3
  rw [h1]
  exact h2.trans h3

/-- **The leg of the cone at an arbitrary étale neighborhood is the germ at the geometric point
on global functions.** Restricting a global function along the leg and reading the result in the
étale local ring is the structure map of the colimit defining that ring. -/
theorem strictHenselizationCone_π_appTop (V : (geometricPointFiber B S hS s).Elements)
    (b : Γ((etaleNeighborhoodDiagram B S hS s).obj V, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of ↥(etaleLocalRing B S hS s))).hom.hom
        (((strictHenselizationCone B S hS s).π.app V).appTop.hom b) =
      (colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
        (SmallEtale.structureSheaf B S hS).obj) (op V)).hom b := by
  obtain ⟨a, ⟨h⟩⟩ := etaleNeighborhoodAffineIndex_weaklyInitial B S hS s V
  set F := (CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
    (SmallEtale.structureSheaf B S hS).obj with hF
  have hcone : (strictHenselizationCone B S hS s).π.app
        ((etaleNeighborhoodAffineInclusion B S hS s).obj a) ≫
      (etaleNeighborhoodDiagram B S hS s).map h =
      (strictHenselizationCone B S hS s).π.app V :=
    (strictHenselizationCone B S hS s).w h
  have hb : ((strictHenselizationCone B S hS s).π.app V).appTop.hom b =
      ((strictHenselizationCone B S hS s).π.app
        ((etaleNeighborhoodAffineInclusion B S hS s).obj a)).appTop.hom
          ((F.map (op h)).hom b) := by
    rw [← hcone]
    rfl
  rw [hb]
  exact (strictHenselizationCone_π_appTop_affine B S hS s a ((F.map (op h)).hom b)).trans
    (congrArg (fun f => RingCat.Hom.hom f b) (colimit.w F (op h)))

/-- **The structure morphism of the limit cone is the canonical structure morphism of the strict
henselization.** -/
theorem strictHenselizationConeToBase_eq :
    strictHenselizationConeToBase B S hS s = strictHenselizationToBase B S hS s := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S)
      (x := s.hom (closedPoint s.residueField)) (U := ⊤) (by trivial)
  have hUaff : IsAffine ((etaleNeighborhoodDiagram B S hS s).obj
      (zariskiNeighborhood B S hS s (s.hom (closedPoint s.residueField)) rfl ⟨U, hxU⟩)) := hU
  have main : ((strictHenselizationCone B S hS s).π.app
          (zariskiNeighborhood B S hS s _ rfl ⟨U, hxU⟩)).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of ↥(etaleLocalRing B S hS s))).hom =
      U.topIso.hom ≫ (S.presheaf.germ U (s.hom (closedPoint s.residueField)) hxU ≫
        CommRingCat.ofHom (structureSheafStalkFromLocalRing B S hS s)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    have hb : (CommRingCat.Hom.hom U.topIso.inv) ((CommRingCat.Hom.hom U.topIso.hom) b) = b :=
      congrArg (fun f => CommRingCat.Hom.hom f b) U.topIso.hom_inv_id
    change (Scheme.ΓSpecIso (CommRingCat.of ↥(etaleLocalRing B S hS s))).hom.hom
        (((strictHenselizationCone B S hS s).π.app
          (zariskiNeighborhood B S hS s _ rfl ⟨U, hxU⟩)).appTop.hom b) =
      (structureSheafStalkFromLocalRing B S hS s)
        ((S.presheaf.germ U (s.hom (closedPoint s.residueField)) hxU).hom
          ((CommRingCat.Hom.hom U.topIso.hom) b))
    rw [strictHenselizationCone_π_appTop,
      structureSheafStalkFromLocalRing_open_germ B S hS s U hxU
        ((CommRingCat.Hom.hom U.topIso.hom) b), hb]
  have e2 : (Spec.map (S.presheaf.germ U (s.hom (closedPoint s.residueField)) hxU ≫
        CommRingCat.ofHom (structureSheafStalkFromLocalRing B S hS s)) ≫ hU.isoSpec.inv).appTop =
      U.topIso.hom ≫ (S.presheaf.germ U (s.hom (closedPoint s.residueField)) hxU ≫
        CommRingCat.ofHom (structureSheafStalkFromLocalRing B S hS s)) ≫
          (Scheme.ΓSpecIso (CommRingCat.of ↥(etaleLocalRing B S hS s))).inv := by
    change hU.isoSpec.inv.appTop ≫ (Spec.map (S.presheaf.germ U
        (s.hom (closedPoint s.residueField)) hxU ≫
      CommRingCat.ofHom (structureSheafStalkFromLocalRing B S hS s))).appTop = _
    rw [IsAffineOpen.isoSpec_inv_appTop, Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  have key : (strictHenselizationCone B S hS s).π.app
        (zariskiNeighborhood B S hS s _ rfl ⟨U, hxU⟩) =
      Spec.map (S.presheaf.germ U (s.hom (closedPoint s.residueField)) hxU ≫
          CommRingCat.ofHom (structureSheafStalkFromLocalRing B S hS s)) ≫ hU.isoSpec.inv :=
    ext_of_isAffine
      (((Iso.eq_comp_inv _).mpr main).trans ((Category.assoc _ _ _).trans e2.symm))
  have hfac : (strictHenselizationCone B S hS s).π.app
        (zariskiNeighborhood B S hS s _ rfl ⟨U, hxU⟩) ≫ U.ι =
      strictHenselizationConeToBase B S hS s :=
    strictHenselizationCone_π_comp_hom B S hS s _
  have hrhs : strictHenselizationToBase B S hS s =
      Spec.map (S.presheaf.germ U (s.hom (closedPoint s.residueField)) hxU ≫
          CommRingCat.ofHom (structureSheafStalkFromLocalRing B S hS s)) ≫
        hU.isoSpec.inv ≫ U.ι := by
    rw [strictHenselizationToBase, ← hU.fromSpecStalk_eq_fromSpecStalk hxU,
      IsAffineOpen.fromSpecStalk, IsAffineOpen.fromSpec]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫ (hU.isoSpec.inv ≫ U.ι)) (Spec.map_comp _ _).symm)
  exact hfac.symm.trans ((congrArg (fun f => f ≫ U.ι) key).trans
    ((Category.assoc _ _ _).trans hrhs.symm))

/-- Every leg of the strict henselization cone, followed by the structure morphism of its étale
neighborhood, is the canonical structure morphism of the strict henselization. -/
theorem strictHenselizationCone_π_comp_hom_eq (V : (geometricPointFiber B S hS s).Elements) :
    (strictHenselizationCone B S hS s).π.app V ≫ B.inclusion.map V.1.obj.hom =
      strictHenselizationToBase B S hS s :=
  (strictHenselizationCone_π_comp_hom B S hS s V).trans
    (strictHenselizationConeToBase_eq B S hS s)

/-- The canonical structure morphism of the strict henselization factors through every member of
the small cofinal family of affine étale neighborhoods, by the leg of the affine cone. This is
the form consumed by the descent results of Stacks Tag 01ZM, whose index category is the small
affine family. -/
theorem strictHenselizationAffineCone_π_comp_hom_eq
    (a : etaleNeighborhoodAffineIndex B S hS s) :
    (strictHenselizationAffineCone B S hS s).π.app a ≫
        B.inclusion.map ((etaleNeighborhoodAffineInclusion B S hS s).obj a).1.obj.hom =
      strictHenselizationToBase B S hS s :=
  strictHenselizationCone_π_comp_hom_eq B S hS s
    ((etaleNeighborhoodAffineInclusion B S hS s).obj a)

end AlgebraicGeometry

end
