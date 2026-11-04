module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedSubschemeSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.VanishingCyclesFibre
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.GeometricPointStalk

/-!
# The canonical map from an étale stalk to the cohomology of a variety of vanishing cycles

Let `f : X ⟶ S` be a morphism of schemes, let `x` be a geometric point of `X` with image `s` in
`S`, and let `t` be a geometric point of `Spec 𝒪^{sh}_{S,s}`. The variety of vanishing cycles of
`f` at `x` is the fibre product `F_{x,t} = t ×_{Spec 𝒪^{sh}_{S,s}} Spec 𝒪^{sh}_{X,x}`, and it
comes with a projection to `Spec 𝒪^{sh}_{X,x}`. Since `𝒪^{sh}_{X,x}` is strictly henselian the
stalk `K_x` of an object `K` of `D(X_étale)` is the derived sections of `K` over
`Spec 𝒪^{sh}_{X,x}`, so pulling back cohomology along that projection produces a canonical map

`α_{K,x,t} : K_x ⟶ RΓ(F_{x,t}, K)`.

This file constructs that map. Only the projection `F_{x,t} ⟶ Spec 𝒪^{sh}_{X,x}` enters the
construction, and nothing else about the vanishing-cycles square does, so the map is built for an
arbitrary scheme `T` over `Spec 𝒪^{sh}_{X,x}`; the variety of vanishing cycles is the case where
`T` is that fibre product and the morphism is its second projection.

The construction does not go through an identification of `K_x` with `RΓ(Spec 𝒪^{sh}_{X,x}, K)`.
Instead it uses what makes that identification true, namely that `Spec 𝒪^{sh}_{X,x}` is the
initial pro-étale neighbourhood of `x`: a germ at `x` is a section over some étale neighbourhood
`W` of `x`, the strict henselization maps to `W` by a unique morphism compatible with the
geometric point, and restricting the section along `T ⟶ Spec 𝒪^{sh}_{X,x} ⟶ W` gives a global
section over `T` of the inverse image. The uniqueness of that morphism is what makes the
resulting map independent of the chosen neighbourhood, and the stalk is the colimit over
neighbourhoods, so the germ-level maps assemble into a natural transformation of functors on
abelian sheaves. The passage to unbounded derived categories is then
`Stacks.DerivedFunctor.exactDerivedDesc`, which applies because the stalk functor is exact.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleBaseChangeLift` — a morphism into an étale object over `Z`,
  read as a morphism from the terminal object of the small étale site of the source into the base
  change of that object.
* `Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb` — restriction of sections over an étale
  object to global sections of the inverse image, along a morphism into that object.
* `AlgebraicGeometry.strictHenselizationNeighborhoodLift` — the unique morphism from the strict
  henselization at a geometric point to an étale neighbourhood of that point which lies over `X`
  and is compatible with the geometric point.
* `AlgebraicGeometry.etaleStalkToSectionsAb` — the map `F_x ⟶ Γ(T, g⁻¹F)` on abelian étale
  sheaves, for a scheme `T` over the strict henselization at `x` with structure morphism
  `g : T ⟶ X`.
* `AlgebraicGeometry.vanishingCyclesMap` — **[Stacks, Tag 0GJN]** the canonical map
  `α_{K,x,t} : K_x ⟶ RΓ(T, K)` on unbounded derived categories, for an arbitrary scheme `T` over
  the strict henselization.
* `AlgebraicGeometry.vanishingCyclesFibreMap` — **[Stacks, Tag 0GJN]** the displayed map
  `α_{K,x,t} : K_x ⟶ RΓ(F_{x,t}, K)` of the source, that construction at the variety of vanishing
  cycles of a morphism of schemes.

## Main results

* `AlgebraicGeometry.existsUnique_strictHenselizationNeighborhoodLift` — the morphism from the
  strict henselization into an étale neighbourhood exists and is unique, by the unique lifting
  property of weakly étale morphisms over a strictly henselian local ring.
* `AlgebraicGeometry.etaleStalkToSectionsAb_toPresheafFiber` — on the germ at `x` of a section
  over an étale neighbourhood, the map on sheaves is restriction of that section along the
  composite `T ⟶ Spec 𝒪^{sh}_{X,x} ⟶ W`. This is the description the source gives and it
  determines the map, the germs over all neighbourhoods generating the stalk.
* `AlgebraicGeometry.vanishingCyclesMap_fac_app` — **[Stacks, Tag 0GJN]** on every complex of
  abelian étale sheaves the canonical map factors the degreewise map on sheaves through the unit
  of the derivation of global sections, which determines it.
* `AlgebraicGeometry.vanishingCyclesFibreMap_eq` — the displayed map of the source is the general
  construction at the projection of the variety of vanishing cycles to the strict henselization,
  so the factorization above describes it too.

## References

* [Stacks Project, Tag 03PO](https://stacks.math.columbia.edu/tag/03PO)
* [Stacks Project, Tag 03PS](https://stacks.math.columbia.edu/tag/03PS)
* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
* [Stacks Project, Tag 0993](https://stacks.math.columbia.edu/tag/0993)
* [Stacks Project, Tag 0GJ4](https://stacks.math.columbia.edu/tag/0GJ4)
* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.Sites

/-! ### Restricting sections before comparing them -/

section

variable {C : Type*} [Category C] {D : Type*} [Category D] (G : C ⥤ D)
  (A : Type*) [Category A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] {P : Sheaf J A ⥤ Sheaf K A}

/-- Restricting a section along a morphism of the source site and then comparing it is comparing
it along the image of that morphism: the comparison map on sections is natural in the object of
the source site as well as in the sheaf. -/
theorem map_comp_sectionsPullbackComparison
    (adj : P ⊣ G.sheafPushforwardContinuous A J K) {U V : C} (m : U ⟶ V) {Y : D}
    (g : Y ⟶ G.obj U) :
    (sheafSections J A).map m.op ≫ sectionsPullbackComparison G A J K adj g =
      sectionsPullbackComparison G A J K adj (g ≫ G.map m) := by
  ext F
  have h : F.obj.map m.op ≫ (adj.unit.app F).hom.app (op U) =
      (adj.unit.app F).hom.app (op V) ≫ (P.obj F).obj.map (G.map m).op :=
    (adj.unit.app F).hom.naturality m.op
  calc ((sheafSections J A).map m.op ≫ sectionsPullbackComparison G A J K adj g).app F
      = (F.obj.map m.op ≫ (adj.unit.app F).hom.app (op U)) ≫ (P.obj F).obj.map g.op :=
        (Category.assoc _ _ _).symm
    _ = ((adj.unit.app F).hom.app (op V) ≫ (P.obj F).obj.map (G.map m).op) ≫
          (P.obj F).obj.map g.op :=
        congrArg (· ≫ (P.obj F).obj.map g.op) h
    _ = (adj.unit.app F).hom.app (op V) ≫
          ((P.obj F).obj.map (G.map m).op ≫ (P.obj F).obj.map g.op) :=
        Category.assoc _ _ _
    _ = (sectionsPullbackComparison G A J K adj (g ≫ G.map m)).app F :=
        congrArg ((adj.unit.app F).hom.app (op V) ≫ ·)
          ((P.obj F).obj.map_comp (G.map m).op g.op).symm

end

end Stacks.Sites

namespace Stacks.EtaleCohomology

/-! ### Restriction of sections to global sections of an inverse image -/

section Sections

variable {Z T : Scheme.{u}} (p : T ⟶ Z) (W : Z.Etale) (r : T ⟶ W.left)

/-- A morphism `r : T ⟶ W.left` into an étale object `W` over `Z`, lying over `p : T ⟶ Z`, read
as a morphism from the identity object of the small étale site of `T` into the base change of
`W` along `p`. -/
def smallEtaleBaseChangeLift (hr : r ≫ W.hom = p) :
    Scheme.Etale.mk (𝟙 T) ⟶ (smallEtaleBaseChange p).obj W :=
  MorphismProperty.Over.homMk
    (pullback.lift r (𝟙 T) (hr.trans (Category.id_comp p).symm))
    (pullback.lift_snd _ _ _) trivial

/-- The morphism of étale objects determined by `r` is, on underlying schemes, the morphism into
the fibre product with components `r` and the identity. -/
theorem smallEtaleBaseChangeLift_left (hr : r ≫ W.hom = p) :
    (smallEtaleBaseChangeLift p W r hr).left =
      pullback.lift r (𝟙 T) (hr.trans (Category.id_comp p).symm) :=
  rfl

/-- The identity object of a small étale site is a terminal object of that site. -/
def isTerminalEtaleMkId (T : Scheme.{u}) : IsTerminal (Scheme.Etale.mk (𝟙 T)) :=
  let _ : IsIso (Scheme.Etale.mk (𝟙 T)).hom := inferInstanceAs (IsIso (𝟙 T))
  isTerminalOfIsIsoHom _

/-- Restriction of sections of an abelian sheaf over an étale object `W` of the small étale site
of `Z` to global sections of its inverse image on `T`, along a morphism `r : T ⟶ W.left` lying
over `p : T ⟶ Z`: carry a section over `W` to a section of the inverse image over the base change
of `W`, restrict it along the morphism determined by `r`, and read the result as a global
section. -/
def smallEtaleSectionsPullbackAb (hr : r ≫ W.hom = p) :
    (sheafSections (smallEtaleTopology Z) Ab.{u + 1}).obj (op W) ⟶
      smallEtalePullbackAb p ⋙ Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1} :=
  Stacks.Sites.sectionsPullbackComparison (smallEtaleBaseChange p) Ab.{u + 1}
      (smallEtaleTopology Z) (smallEtaleTopology T) (smallEtaleAdjunctionAb p)
      (smallEtaleBaseChangeLift p W r hr) ≫
    Functor.whiskerLeft (smallEtalePullbackAb p)
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1}
        (isTerminalEtaleMkId T)).inv

/-- Restricting a section along a morphism of étale objects over `Z` and then pulling it back is
pulling it back along the composite: the chosen lifts agree, because both are determined by their
two projections out of the base change. -/
theorem map_comp_smallEtaleSectionsPullbackAb {V : Z.Etale} (m : W ⟶ V)
    (hr : r ≫ W.hom = p) (hrm : (r ≫ m.left) ≫ V.hom = p) :
    (sheafSections (smallEtaleTopology Z) Ab.{u + 1}).map m.op ≫
        smallEtaleSectionsPullbackAb p W r hr =
      smallEtaleSectionsPullbackAb p V (r ≫ m.left) hrm := by
  have ha : smallEtaleBaseChangeLift p W r hr ≫ (smallEtaleBaseChange p).map m =
      smallEtaleBaseChangeLift p V (r ≫ m.left) hrm := by
    apply MorphismProperty.Over.Hom.ext
    change (smallEtaleBaseChangeLift p W r hr).left ≫
        ((smallEtaleBaseChange p).map m).left =
      (smallEtaleBaseChangeLift p V (r ≫ m.left) hrm).left
    have hm1 : ((smallEtaleBaseChange p).map m).left ≫ pullback.fst V.hom p =
        pullback.fst W.hom p ≫ m.left := pullback.lift_fst _ _ _
    have hm2 : ((smallEtaleBaseChange p).map m).left ≫ pullback.snd V.hom p =
        pullback.snd W.hom p := pullback.lift_snd _ _ _
    apply pullback.hom_ext
    · erw [Category.assoc, hm1, ← Category.assoc, smallEtaleBaseChangeLift_left,
        pullback.lift_fst, pullback.lift_fst]
      rfl
    · erw [Category.assoc, hm2, smallEtaleBaseChangeLift_left, pullback.lift_snd,
        pullback.lift_snd]
  have key := Stacks.Sites.map_comp_sectionsPullbackComparison (smallEtaleBaseChange p)
    Ab.{u + 1} (smallEtaleTopology Z) (smallEtaleTopology T) (smallEtaleAdjunctionAb p) m
    (smallEtaleBaseChangeLift p W r hr)
  rw [ha] at key
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) key)

/-- The restriction of sections depends only on the morphism into the étale object, not on the
proof that it lies over `p`. -/
theorem smallEtaleSectionsPullbackAb_congr {r' : T ⟶ W.left} (hr : r ≫ W.hom = p)
    (hr' : r' ≫ W.hom = p) (h : r = r') :
    smallEtaleSectionsPullbackAb p W r hr = smallEtaleSectionsPullbackAb p W r' hr' := by
  subst h
  rfl

end Sections

/-! ### Maps out of the stalk at a geometric point -/

section StalkDesc

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)
  (K : Sheaf (smallEtaleTopology X) Ab.{u + 1} ⥤ Ab.{u + 1})
  (stage : ∀ (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (W : X.Etale),
    (Scheme.pointSmallEtale x).fiber.obj W → (F.obj.obj (op W) ⟶ K.obj F))

/-- A family of maps out of the sections of abelian étale sheaves over the étale neighbourhoods
of a geometric point, compatible with restriction along morphisms of neighbourhoods and natural
in the sheaf, descends to a natural transformation out of the stalk functor at that point: the
stalk is the colimit of the sections over the neighbourhoods. -/
def smallEtaleStalkDesc
    (hstage : ∀ (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) ⦃W V : X.Etale⦄ (m : W ⟶ V)
      (v : (Scheme.pointSmallEtale x).fiber.obj W),
      F.obj.map m.op ≫ stage F W v = stage F V ((Scheme.pointSmallEtale x).fiber.map m v))
    (hnat : ∀ {F G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (α : F ⟶ G) (W : X.Etale)
      (v : (Scheme.pointSmallEtale x).fiber.obj W),
      α.hom.app (op W) ≫ stage G W v = stage F W v ≫ K.map α) :
    smallEtaleStalkAb x ⟶ K where
  app F := (Scheme.pointSmallEtale x).presheafFiberDesc (stage F) (hstage F)
  naturality F G α := by
    apply (Scheme.pointSmallEtale x).presheafFiber_hom_ext
    intro W v
    change (Scheme.pointSmallEtale x).toPresheafFiber W v F.obj ≫
        ((Scheme.pointSmallEtale x).presheafFiber.map α.hom ≫
          (Scheme.pointSmallEtale x).presheafFiberDesc (stage G) (hstage G)) =
      (Scheme.pointSmallEtale x).toPresheafFiber W v F.obj ≫
        ((Scheme.pointSmallEtale x).presheafFiberDesc (stage F) (hstage F) ≫ K.map α)
    rw [(Scheme.pointSmallEtale x).toPresheafFiber_naturality_assoc α.hom W v,
      (Scheme.pointSmallEtale x).toPresheafFiber_presheafFiberDesc (stage G) (hstage G),
      (Scheme.pointSmallEtale x).toPresheafFiber_presheafFiberDesc_assoc (stage F) (hstage F)]
    exact hnat α W v

/-- The descended transformation has the prescribed value on the germ at the geometric point of a
section over an étale neighbourhood. -/
theorem toPresheafFiber_comp_smallEtaleStalkDesc
    (hstage : ∀ (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) ⦃W V : X.Etale⦄ (m : W ⟶ V)
      (v : (Scheme.pointSmallEtale x).fiber.obj W),
      F.obj.map m.op ≫ stage F W v = stage F V ((Scheme.pointSmallEtale x).fiber.map m v))
    (hnat : ∀ {F G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (α : F ⟶ G) (W : X.Etale)
      (v : (Scheme.pointSmallEtale x).fiber.obj W),
      α.hom.app (op W) ≫ stage G W v = stage F W v ≫ K.map α)
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (W : X.Etale)
    (v : (Scheme.pointSmallEtale x).fiber.obj W) :
    (Scheme.pointSmallEtale x).toPresheafFiber W v F.obj ≫
        (smallEtaleStalkDesc x K stage hstage hnat).app F =
      stage F W v :=
  (Scheme.pointSmallEtale x).toPresheafFiber_presheafFiberDesc (stage F) (hstage F) W v

end StalkDesc

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

/-! ### The initial étale neighbourhood of a geometric point -/

section Lift

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (x : GeometricPoint X)

/-- The canonical lift of a geometric point to its strict henselization hits the closed point:
evaluation of étale germs in the residue field of the geometric point is a local homomorphism. -/
theorem geometricPointToStrictHenselization_closedPoint :
    geometricPointToStrictHenselization B X hX x (closedPoint x.residueField) =
      closedPoint (CommRingCat.of ↥(etaleLocalRing B X hX x)) := by
  let : IsLocalHom
      (CommRingCat.ofHom (structureSheafStalkToGeometricField B X hX x)).hom :=
    isLocalHom_structureSheafStalkToGeometricField B X hX x
  exact Spec_closedPoint

variable (W : X.Etale) (v : (Scheme.pointSmallEtale x.hom).fiber.obj W)

/-- **The strict henselization is the initial étale neighbourhood of a geometric point.** There
is exactly one morphism from the strict henselization at `x` to an étale neighbourhood `W` of `x`
which lies over `X` and carries the canonical geometric point of the strict henselization to the
chosen lift of `x` in `W`.

An étale morphism is weakly étale and the étale local ring is strictly henselian, so this is the
unique lifting property `AlgebraicGeometry.exists_lift_of_strictlyHenselian_of_weaklyEtale`. -/
theorem existsUnique_strictHenselizationNeighborhoodLift :
    ∃! r : strictHenselization B X hX x ⟶ W.left,
      r ≫ W.hom = strictHenselizationToBase B X hX x ∧
        geometricPointToStrictHenselization B X hX x ≫ r = v.left :=
  exists_lift_of_strictlyHenselian_of_weaklyEtale W.hom
    (strictHenselizationToBase B X hX x) (geometricPointToStrictHenselization B X hX x)
    (geometricPointToStrictHenselization_closedPoint B X hX x) v.left
    ((Over.w v).trans (geometricPointToStrictHenselization_comp B X hX x).symm)

/-- The unique morphism from the strict henselization at a geometric point to an étale
neighbourhood of that point, over `X` and compatible with the geometric point. -/
def strictHenselizationNeighborhoodLift : strictHenselization B X hX x ⟶ W.left :=
  (existsUnique_strictHenselizationNeighborhoodLift B X hX x W v).exists.choose

/-- The morphism from the strict henselization into an étale neighbourhood lies over `X`. -/
theorem strictHenselizationNeighborhoodLift_comp :
    strictHenselizationNeighborhoodLift B X hX x W v ≫ W.hom =
      strictHenselizationToBase B X hX x :=
  (existsUnique_strictHenselizationNeighborhoodLift B X hX x W v).exists.choose_spec.1

/-- The morphism from the strict henselization into an étale neighbourhood carries the canonical
geometric point to the chosen lift of `x`. -/
theorem geometricPointToStrictHenselization_comp_neighborhoodLift :
    geometricPointToStrictHenselization B X hX x ≫
        strictHenselizationNeighborhoodLift B X hX x W v = v.left :=
  (existsUnique_strictHenselizationNeighborhoodLift B X hX x W v).exists.choose_spec.2

/-- Any morphism from the strict henselization into an étale neighbourhood which lies over `X`
and is compatible with the geometric point is the canonical one. -/
theorem strictHenselizationNeighborhoodLift_eq
    (r : strictHenselization B X hX x ⟶ W.left)
    (hr : r ≫ W.hom = strictHenselizationToBase B X hX x)
    (hv : geometricPointToStrictHenselization B X hX x ≫ r = v.left) :
    r = strictHenselizationNeighborhoodLift B X hX x W v :=
  (existsUnique_strictHenselizationNeighborhoodLift B X hX x W v).unique ⟨hr, hv⟩
    ⟨strictHenselizationNeighborhoodLift_comp B X hX x W v,
      geometricPointToStrictHenselization_comp_neighborhoodLift B X hX x W v⟩

/-- The morphisms from the strict henselization into étale neighbourhoods are compatible with
morphisms of neighbourhoods, by their uniqueness. -/
theorem strictHenselizationNeighborhoodLift_comp_left {V : X.Etale} (m : W ⟶ V) :
    strictHenselizationNeighborhoodLift B X hX x W v ≫ m.left =
      strictHenselizationNeighborhoodLift B X hX x V
        ((Scheme.pointSmallEtale x.hom).fiber.map m v) :=
  strictHenselizationNeighborhoodLift_eq B X hX x V _ _
    (by rw [Category.assoc, MorphismProperty.Over.w m,
      strictHenselizationNeighborhoodLift_comp])
    (by rw [← Category.assoc, geometricPointToStrictHenselization_comp_neighborhoodLift]; rfl)

end Lift

/-! ### The map on abelian sheaves -/

section Underived

open Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (x : GeometricPoint X)
  {T : Scheme.{u}} (q : T ⟶ strictHenselization B X hX x)

/-- The germ-level map: the restriction of a section of an abelian étale sheaf over an étale
neighbourhood `W` of `x` to a global section over `T` of its inverse image, along the composite
`T ⟶ Spec 𝒪^{sh}_{X,x} ⟶ W`. -/
def etaleStalkSectionsStage (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (W : X.Etale)
    (v : (Scheme.pointSmallEtale x.hom).fiber.obj W) :
    F.obj.obj (op W) ⟶
      (smallEtalePullbackAb (q ≫ strictHenselizationToBase B X hX x) ⋙
        Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).obj F :=
  (smallEtaleSectionsPullbackAb (q ≫ strictHenselizationToBase B X hX x) W
    (q ≫ strictHenselizationNeighborhoodLift B X hX x W v)
    (by rw [Category.assoc, strictHenselizationNeighborhoodLift_comp])).app F

/-- The germ-level maps are compatible with restriction along a morphism of étale
neighbourhoods. -/
theorem map_comp_etaleStalkSectionsStage
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) {W V : X.Etale} (m : W ⟶ V)
    (v : (Scheme.pointSmallEtale x.hom).fiber.obj W) :
    F.obj.map m.op ≫ etaleStalkSectionsStage B X hX x q F W v =
      etaleStalkSectionsStage B X hX x q F V
        ((Scheme.pointSmallEtale x.hom).fiber.map m v) := by
  have hlift : (q ≫ strictHenselizationNeighborhoodLift B X hX x W v) ≫ m.left =
      q ≫ strictHenselizationNeighborhoodLift B X hX x V
        ((Scheme.pointSmallEtale x.hom).fiber.map m v) := by
    rw [Category.assoc, strictHenselizationNeighborhoodLift_comp_left]
  have hr : ∀ (U : X.Etale) (u : (Scheme.pointSmallEtale x.hom).fiber.obj U),
      (q ≫ strictHenselizationNeighborhoodLift B X hX x U u) ≫ U.hom =
        q ≫ strictHenselizationToBase B X hX x := fun U u => by
    rw [Category.assoc, strictHenselizationNeighborhoodLift_comp]
  have hrm : ((q ≫ strictHenselizationNeighborhoodLift B X hX x W v) ≫ m.left) ≫ V.hom =
      q ≫ strictHenselizationToBase B X hX x := by
    rw [hlift]
    exact hr _ _
  have h := map_comp_smallEtaleSectionsPullbackAb (q ≫ strictHenselizationToBase B X hX x) W
    (q ≫ strictHenselizationNeighborhoodLift B X hX x W v) m (hr W v) hrm
  exact congrArg (fun σ => NatTrans.app σ F)
    (h.trans (smallEtaleSectionsPullbackAb_congr (q ≫ strictHenselizationToBase B X hX x) V
      ((q ≫ strictHenselizationNeighborhoodLift B X hX x W v) ≫ m.left) hrm (hr V _) hlift))

/-- The naturality in the sheaf of the germ-level maps, which is the naturality of restriction of
sections. -/
theorem etaleStalkSectionsStage_naturality
    {F G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (α : F ⟶ G) (W : X.Etale)
    (v : (Scheme.pointSmallEtale x.hom).fiber.obj W) :
    α.hom.app (op W) ≫ etaleStalkSectionsStage B X hX x q G W v =
      etaleStalkSectionsStage B X hX x q F W v ≫
        (smallEtalePullbackAb (q ≫ strictHenselizationToBase B X hX x) ⋙
          Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).map α :=
  (smallEtaleSectionsPullbackAb (q ≫ strictHenselizationToBase B X hX x) W
    (q ≫ strictHenselizationNeighborhoodLift B X hX x W v)
    (by rw [Category.assoc, strictHenselizationNeighborhoodLift_comp])).naturality α

/-- The map `F_x ⟶ Γ(T, g⁻¹F)` on abelian sheaves of the small étale site of `X`, for a scheme
`T` over the strict henselization at the geometric point `x` with structure morphism
`g : T ⟶ X`. On the germ of a section over an étale neighbourhood of `x` it is restriction of
that section along the composite `T ⟶ Spec 𝒪^{sh}_{X,x} ⟶ W`. -/
def etaleStalkToSectionsAb :
    smallEtaleStalkAb x.hom ⟶
      smallEtalePullbackAb (q ≫ strictHenselizationToBase B X hX x) ⋙
        Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1} :=
  smallEtaleStalkDesc x.hom _ (etaleStalkSectionsStage B X hX x q)
    (fun F _ _ m v => map_comp_etaleStalkSectionsStage B X hX x q F m v)
    (fun α W v => etaleStalkSectionsStage_naturality B X hX x q α W v)

/-- On the germ at `x` of a section over an étale neighbourhood `W`, the map on sheaves is
restriction of that section along the composite `T ⟶ Spec 𝒪^{sh}_{X,x} ⟶ W`. Germs over all
étale neighbourhoods of `x` generate the stalk, so this determines the map. -/
theorem etaleStalkToSectionsAb_toPresheafFiber
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (W : X.Etale)
    (v : (Scheme.pointSmallEtale x.hom).fiber.obj W) :
    (Scheme.pointSmallEtale x.hom).toPresheafFiber W v F.obj ≫
        (etaleStalkToSectionsAb B X hX x q).app F =
      etaleStalkSectionsStage B X hX x q F W v :=
  toPresheafFiber_comp_smallEtaleStalkDesc x.hom _ (etaleStalkSectionsStage B X hX x q) _ _ F W v

end Underived

/-! ### The canonical map on unbounded derived categories -/

section Derived

attribute [local instance] HasDerivedCategory.standard

open Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (x : GeometricPoint X)
  {T : Scheme.{u}} (q : T ⟶ strictHenselization B X hX x)
  [((Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology T) Ab.{u + 1}) (.up ℤ))]

/-- **Stacks 0GJN.** The canonical map `α_{K,x,t} : K_x ⟶ RΓ(T, K)` from the stalk at a geometric
point `x` of `X` of an object `K` of the unbounded derived category of abelian sheaves on the
small étale site of `X`, to the unbounded derived global sections of `K` on a scheme `T` over the
strict henselization `Spec 𝒪^{sh}_{X,x}`, natural in `K`.

For a morphism of schemes `f : X ⟶ S` and a geometric point `t` of `Spec 𝒪^{sh}_{S,f(x)}` the
variety of vanishing cycles of `f` at `x` is the fibre product
`F_{x,t} = t ×_{Spec 𝒪^{sh}_{S,f(x)}} Spec 𝒪^{sh}_{X,x}` over `Spec 𝒪^{sh}_{X,x}`, and the
displayed map of the source is this one for that `T` and the second projection; the construction
uses nothing about `T` beyond its morphism to the strict henselization.

Since the strict henselization is the initial étale neighbourhood of `x`, pulling back germs
along `T ⟶ Spec 𝒪^{sh}_{X,x}` gives the map `etaleStalkToSectionsAb` on abelian sheaves. The
stalk functor is exact, so its action on unbounded derived categories is a right derived functor
of itself, and the map on sheaves extends uniquely to one of derived categories. -/
@[stacks 0GJN "for an arbitrary scheme over the strict henselization"]
def vanishingCyclesMap :
    smallEtaleDerivedStalkAb x.hom ⟶
      smallEtaleDerivedPullbackAb
          (q ≫ strictHenselizationToBase B X hX x) ⋙
        smallEtaleDerivedGlobalSections T :=
  Stacks.DerivedFunctor.exactDerivedDesc (smallEtaleStalkAb x.hom)
    (smallEtalePullbackAb (q ≫ strictHenselizationToBase B X hX x))
    (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1})
    (smallEtaleDerivedGlobalSections T)
    (smallEtaleDerivedGlobalSectionsUnit T)
    (etaleStalkToSectionsAb B X hX x q)

/-- **Stacks 0GJN.** On every complex of abelian sheaves on the small étale site of `X`, the
canonical map to the derived global sections over `T` factors the degreewise map on sheaves
through the unit of the derivation of global sections, read through the identifications of the
degreewise actions of the stalk and of inverse image with their actions on derived categories.

Since the degreewise action of the stalk functor is a right derived functor of itself, this
property determines the map. -/
@[stacks 0GJN "the derived map factors the map on abelian sheaves"]
theorem vanishingCyclesMap_fac_app
    (J : HomotopyCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :
    (smallEtaleStalkAb x.hom).mapDerivedCategoryFactorsh.inv.app J ≫
        (vanishingCyclesMap B X hX x q).app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
          (smallEtaleStalkAb x.hom)
          (smallEtalePullbackAb
            (q ≫ strictHenselizationToBase B X hX x))
          (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1})
          (etaleStalkToSectionsAb B X hX x q)).app J) ≫
        (smallEtaleDerivedGlobalSectionsUnit T).app
            (((smallEtalePullbackAb
              (q ≫ strictHenselizationToBase B X hX x)).mapHomotopyCategory (.up ℤ)).obj J) ≫
          (smallEtaleDerivedGlobalSections T).map
            ((smallEtalePullbackAb
              (q ≫ strictHenselizationToBase B X hX x)).mapDerivedCategoryFactorsh.inv.app J) :=
  Stacks.DerivedFunctor.exactDerivedDesc_fac_app
    (smallEtaleStalkAb x.hom)
    (smallEtalePullbackAb (q ≫ strictHenselizationToBase B X hX x))
    (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1})
    (smallEtaleDerivedGlobalSections T)
    (smallEtaleDerivedGlobalSectionsUnit T)
    (etaleStalkToSectionsAb B X hX x q) J

end Derived

/-! ### The displayed map at a variety of vanishing cycles -/

section VanishingCycles

attribute [local instance] HasDerivedCategory.standard

open Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (x : GeometricPoint X)
  (t : GeometricPoint (strictHenselization B S hS (x.map f)))
  [((Sheaf.Γ (smallEtaleTopology (vanishingCyclesFibre B hX hS f x t))
        Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (smallEtaleTopology (vanishingCyclesFibre B hX hS f x t)) Ab.{u + 1}) (.up ℤ))]

/-- **Stacks 0GJN.** The canonical map

`α_{K,x,t} : K_x ⟶ RΓ(F_{x,t}, K)`

from the stalk at a geometric point `x` of `X` of an object `K` of the unbounded derived category
of abelian sheaves on the small étale site of `X`, to the unbounded derived sections of `K` on the
variety of vanishing cycles `F_{x,t}` of a morphism `f : X ⟶ S` at `x` and a geometric point `t`
of `Spec 𝒪^{sh}_{S,f(x)}`, natural in `K`.

The stalk of `K` at `x` is the derived sections of `K` over the strictly henselian
`Spec 𝒪^{sh}_{X,x}`, and the map is pullback of cohomology along the projection
`F_{x,t} ⟶ Spec 𝒪^{sh}_{X,x}`. -/
@[stacks 0GJN]
def vanishingCyclesFibreMap :
    smallEtaleDerivedStalkAb x.hom ⟶
      smallEtaleDerivedPullbackAb (vanishingCyclesFibreToSource B hX hS f x t) ⋙
        smallEtaleDerivedGlobalSections (vanishingCyclesFibre B hX hS f x t) :=
  vanishingCyclesMap B X hX x (vanishingCyclesFibreToStrictHenselization B hX hS f x t)

/-- The displayed map of the source is the general construction for the projection of the variety
of vanishing cycles to the strict henselization at `x`; in particular
`AlgebraicGeometry.vanishingCyclesMap_fac_app` describes it on every complex. -/
theorem vanishingCyclesFibreMap_eq :
    vanishingCyclesFibreMap B hX hS f x t =
      vanishingCyclesMap B X hX x
        (vanishingCyclesFibreToStrictHenselization B hX hS f x t) :=
  rfl

end VanishingCycles

end AlgebraicGeometry

end
