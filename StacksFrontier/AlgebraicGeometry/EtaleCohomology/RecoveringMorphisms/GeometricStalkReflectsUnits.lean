module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkInverseImageModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricStalkLocalHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RingedSiteHom
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.IsLocallyRingedCriterion
public import StacksFrontier.CategoryTheory.Sites.Modules.UnitsSheafStalk

/-!
# Reflection of units at a geometric stalk of the small étale structure map

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site `B` and let `x̄` be a geometric
point of `X`, with image `ȳ = a ∘ x̄`.  This file proves condition (3) of Stacks 04H9 for the
morphism of ringed sites `(a_small, a_small^♯)` at `x̄`: the stalk at `x̄` of the structure map
`a⁻¹𝒪_Y ⟶ 𝒪_X` reflects units.

Three steps are needed.  First, Stacks 03Q1 — the identification of the stalk at `x̄` of an
inverse image with the stalk at `ȳ` — is re-run for sheaves of sets valued in the universe of
the structure rings, which is the universe in which the units square of Stacks 04HA is read;
the library's `AlgebraicGeometry.smallEtalePullbackStalkIso` is stated one universe higher.
Second, the ring structure transported to the stalk of the underlying sheaf of sets of the
structure sheaf is identified with the étale local ring of Stacks 03PS.  Third, under those two
identifications the stalk of the structure map is `AlgebraicGeometry.etaleLocalRingMap`, which is
a local ring map, and a local map of local rings reflects units.

## Main definitions

* `AlgebraicGeometry.smallEtalePullbackStalkIsoTypeU`: Stacks 03Q1 at the universe of the
  structure rings.
* `AlgebraicGeometry.etaleStalkRingEquiv`: the transported stalk ring of the structure sheaf at a
  geometric point, as a *ring* isomorphism with the étale local ring.
* `AlgebraicGeometry.etaleStalkMulEquiv`: the same with the additive structure forgotten, which
  is the form the units square of Stacks 04HA consumes.

## Main results

* `AlgebraicGeometry.etaleStalkCmp_fSharpSet`: the stalk of the structure map is the map of
  étale local rings.
* `AlgebraicGeometry.reflectsUnitsObj_fSharpRingMap`: **condition (3) of Stacks 04H9** for
  `(a_small, a_small^♯)` at a geometric point.

## Implementation notes

The comparison of the transported stalk ring with the étale local ring is built as a `RingEquiv`
and the `MulEquiv` that condition (3) of Stacks 04H9 needs is read off it.  Additivity is never
needed for the units square, but it is needed for step (4) of the proof of
[Stacks 04I6](https://stacks.math.columbia.edu/tag/04I6), which reads the stalk of a sheaf of
solutions of a polynomial system over this ring and so needs both operations.  Additivity costs
nothing beyond `Stacks.Sheaves.StalkTransport.ringStalkComparison_ringAddObj`; the unit and the zero are handled by cancellation.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 03PS](https://stacks.math.columbia.edu/tag/03PS)
* [Stacks Project, Tag 04H9](https://stacks.math.columbia.edu/tag/04H9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite

universe u

namespace CategoryTheory.CategoryOfElements

universe uA vA uC vC uP

variable {C : Type uC} [Category.{vC} C] {P Q : C ⥤ Type uP}
  {A : Type uA} [Category.{vA} A]
  [Limits.HasColimitsOfShape P.Elementsᵒᵖ A] [Limits.HasColimitsOfShape Q.Elementsᵒᵖ A]

/-- The colimit over a category of elements depends on the indexing functor only through its
isomorphism class, at arbitrary coefficients. -/
def presheafColimIsoOfNatIso' (e : P ≅ Q) :
    (Functor.whiskeringLeft P.Elementsᵒᵖ Cᵒᵖ A).obj (CategoryOfElements.π P).op ⋙ Limits.colim ≅
      (Functor.whiskeringLeft Q.Elementsᵒᵖ Cᵒᵖ A).obj
        (CategoryOfElements.π Q).op ⋙ Limits.colim :=
  Functor.isoWhiskerLeft
    ((Functor.whiskeringLeft Q.Elementsᵒᵖ Cᵒᵖ A).obj (CategoryOfElements.π Q).op)
    (Functor.Final.colimIso (equivalenceOfNatIso e).op.functor)

/-- The stalk functor on sheaves given by a colimit over a category of elements depends on the
indexing functor only through its isomorphism class, at arbitrary coefficients. -/
def sheafColimIsoOfNatIso' (J : GrothendieckTopology C) (e : P ≅ Q) :
    (sheafToPresheaf J A ⋙
      (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π P).op ⋙ Limits.colim) ≅
    (sheafToPresheaf J A ⋙
      (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π Q).op ⋙ Limits.colim) :=
  Functor.isoWhiskerLeft (sheafToPresheaf J A) (presheafColimIsoOfNatIso' e)

/-- The comparison sends the germ of a section at an element to its germ at the transported
element. -/
lemma ι_sheafColimIsoOfNatIso'_hom (J : GrothendieckTopology C) (e : P ≅ Q)
    (F : Sheaf J A) (V : P.Elements) :
    Limits.colimit.ι ((CategoryOfElements.π P).op ⋙ F.obj) (op V) ≫
        (sheafColimIsoOfNatIso' J e).hom.app F =
      Limits.colimit.ι ((CategoryOfElements.π Q).op ⋙ F.obj)
        ((equivalenceOfNatIso e).op.functor.obj (op V)) :=
  Functor.Final.ι_colimitIso_hom (equivalenceOfNatIso e).op.functor
    ((CategoryOfElements.π Q).op ⋙ F.obj) (op V)

end CategoryTheory.CategoryOfElements

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y) (x : GeometricPoint X.obj)

/-! ### Stacks 03Q1 at the universe of the structure rings -/

/-- The direct image of small étale base change on sheaves of sets valued in the universe of the
structure rings is a right adjoint. -/
instance isRightAdjoint_sheafPushforwardContinuous_smallEtaleBaseChange :
    ((smallEtaleBaseChange B a).sheafPushforwardContinuous (Type u)
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)).IsRightAdjoint :=
  (smallEtaleBaseChange_isMorphismOfSites_ringUniverse B
    a).isRightAdjoint_sheafPushforwardContinuous

/-- The category of elements of the geometric point fiber at `x̄`, precomposed with small étale
base change along `a`, is initially small. -/
private theorem initiallySmall_elements_smallEtaleBaseChange_comp_geometricPointFiber :
    InitiallySmall.{u}
      (smallEtaleBaseChange B a ⋙ geometricPointFiber B X.obj X.property x).Elements := by
  let p := geometricPointSitePoint B Y.obj Y.property (x.map (B.inclusion.map a))
  let e := CategoryOfElements.equivalenceOfNatIso
    (C := SmallEtale B Y.obj Y.property)
    (P := geometricPointFiber B Y.obj Y.property (x.map (B.inclusion.map a)))
    (Q := smallEtaleBaseChange B a ⋙ geometricPointFiber B X.obj X.property x)
    (geometricPointFiberBaseChangeIso B a x)
  exact ⟨_, inferInstance, fromInitialModel.{u} p.fiber.Elements ⋙ e.functor,
    @Functor.initial_comp_equivalence _ _ _ _ _ _
      (fromInitialModel.{u} p.fiber.Elements) e.functor inferInstance e.isEquivalence_functor⟩

/-- **Stacks 03Q1 at the universe of the structure rings.** The stalk at a geometric point `x̄`
of `X` of the inverse image of a sheaf of sets on the small étale site of `Y` is the stalk of
that sheaf at the image geometric point `ȳ = a ∘ x̄`. -/
def smallEtalePullbackStalkIsoTypeU :
    (smallEtaleRingedSiteHom B a).inverseImage ⋙
      (geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u) ≅
    (geometricPointSitePoint B Y.obj Y.property
      (x.map (B.inclusion.map a))).sheafFiber (A := Type u) := by
  let J := SmallEtale.topology B Y.obj Y.property
  let K := SmallEtale.topology B X.obj X.property
  let v := smallEtaleBaseChange B a
  let p := geometricPointSitePoint B Y.obj Y.property (x.map (B.inclusion.map a))
  let q := geometricPointSitePoint B X.obj X.property x
  haveI : PreservesLimitsOfShape (Discrete PEmpty.{1}) v :=
    Functor.preservesLimitsOfShape_pempty_of_isTerminal v
      (SmallEtale.finalIsTerminal B Y.obj Y.property)
      ((SmallEtale.finalIsTerminal B Y.obj Y.property).isTerminalObj v)
  letI : HasFiniteLimits (SmallEtale B Y.obj Y.property) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  letI : PreservesFiniteLimits v := preservesFiniteLimits_of_preservesTerminal_and_pullbacks v
  letI : RepresentablyFlat v := flat_of_preservesFiniteLimits v
  let hcover : CoverPreserving J K v := CoverPreserving.of_isContinuous v J K
  let eFiber : geometricPointFiber B Y.obj Y.property (x.map (B.inclusion.map a)) ≅
      v ⋙ geometricPointFiber B X.obj X.property x :=
    geometricPointFiberBaseChangeIso B a x
  let eElements := CategoryOfElements.equivalenceOfNatIso
    (C := SmallEtale B Y.obj Y.property)
    (P := geometricPointFiber B Y.obj Y.property (x.map (B.inclusion.map a)))
    (Q := v ⋙ geometricPointFiber B X.obj X.property x) eFiber
  haveI : InitiallySmall.{u}
      (v ⋙ geometricPointFiber B X.obj X.property x).Elements :=
    ⟨_, inferInstance, fromInitialModel.{u} p.fiber.Elements ⋙ eElements.functor,
      @Functor.initial_comp_equivalence _ _ _ _ _ _ (fromInitialModel.{u} p.fiber.Elements)
        eElements.functor inferInstance eElements.isEquivalence_functor⟩
  haveI : InitiallySmall.{u} (v ⋙ q.fiber).Elements :=
    inferInstanceAs (InitiallySmall.{u} (v ⋙ geometricPointFiber B X.obj X.property x).Elements)
  letI : HasColimitsOfShape
      (v ⋙ geometricPointFiber B X.obj X.property x).Elementsᵒᵖ (Type u) :=
    hasColimitsOfShape_of_finallySmall _ _
  let eStalk := CategoryOfElements.sheafColimIsoOfNatIso' (A := Type u) J eFiber
  let eComap := q.sheafFiberComapIso v hcover (Type u)
  change (v.sheafPullback (Type u) J K ⋙ q.sheafFiber) ≅ p.sheafFiber
  exact eComap.symm ≪≫ eStalk.symm

/-- The germ formula for the stalk comparison: the germ at `ȳ` of a section over an étale
neighborhood `V / Y` corresponds to the germ at `x̄` of its image under the adjunction unit over
the base change `X ×_Y V`. -/
theorem smallEtalePullbackStalkIsoTypeU_inv_germ
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) (Type u))
    (V : (geometricPointFiber B Y.obj Y.property (x.map (B.inclusion.map a))).Elements) :
    (geometricPointSitePoint B Y.obj Y.property (x.map (B.inclusion.map a))).toPresheafFiber
        V.1 V.2 F.obj ≫ (smallEtalePullbackStalkIsoTypeU B a x).inv.app F =
      (((smallEtaleBaseChange B a).sheafAdjunctionContinuous (Type u)
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B X.obj X.property)).unit.app F).hom.app (op V.1) ≫
        (geometricPointSitePoint B X.obj X.property x).toPresheafFiber
          ((smallEtaleBaseChange B a).obj V.1)
          ((geometricPointFiberBaseChangeIso B a x).hom.app V.1 V.2)
          ((smallEtaleRingedSiteHom B a).inverseImage.obj F).obj := by
  let J := SmallEtale.topology B Y.obj Y.property
  let K := SmallEtale.topology B X.obj X.property
  let v := smallEtaleBaseChange B a
  let p := geometricPointSitePoint B Y.obj Y.property (x.map (B.inclusion.map a))
  let q := geometricPointSitePoint B X.obj X.property x
  have : HasFiniteLimits (SmallEtale B Y.obj Y.property) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  let hcover : CoverPreserving J K v := CoverPreserving.of_isContinuous v J K
  let eFiber : geometricPointFiber B Y.obj Y.property (x.map (B.inclusion.map a)) ≅
      v ⋙ geometricPointFiber B X.obj X.property x :=
    geometricPointFiberBaseChangeIso B a x
  have : InitiallySmall.{u} (v ⋙ geometricPointFiber B X.obj X.property x).Elements :=
    initiallySmall_elements_smallEtaleBaseChange_comp_geometricPointFiber B a x
  have : InitiallySmall.{u} (v ⋙ q.fiber).Elements :=
    inferInstanceAs (InitiallySmall.{u} (v ⋙ geometricPointFiber B X.obj X.property x).Elements)
  have : HasColimitsOfShape
      (v ⋙ geometricPointFiber B X.obj X.property x).Elementsᵒᵖ (Type u) :=
    hasColimitsOfShape_of_finallySmall _ _
  let eStalk := CategoryOfElements.sheafColimIsoOfNatIso' (A := Type u) J eFiber
  let eComap := q.sheafFiberComapIso v hcover (Type u)
  change p.toPresheafFiber V.1 V.2 F.obj ≫ (eComap.symm ≪≫ eStalk.symm).inv.app F = _
  calc p.toPresheafFiber V.1 V.2 F.obj ≫ (eComap.symm ≪≫ eStalk.symm).inv.app F
      = (p.toPresheafFiber V.1 V.2 F.obj ≫ eStalk.hom.app F) ≫ eComap.hom.app F :=
        (Category.assoc _ _ _).symm
    _ = _ := (congrArg (fun k ↦ k ≫ eComap.hom.app F)
      (CategoryOfElements.ι_sheafColimIsoOfNatIso'_hom (A := Type u) J eFiber F V)).trans
      (Point.toSheafFiber_sheafFiberComapIso_hom q v hcover F V.1 (eFiber.hom.app V.1 V.2))

/-- The germ formula for the stalk comparison, read on elements. -/
theorem smallEtalePullbackStalkIsoTypeU_inv_germ_apply
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) (Type u))
    (U : SmallEtale B Y.obj Y.property)
    (z : (geometricPointFiber B Y.obj Y.property (x.map (B.inclusion.map a))).obj U)
    (t : F.obj.obj (op U)) :
    (smallEtalePullbackStalkIsoTypeU B a x).inv.app F
        ((geometricPointSitePoint B Y.obj Y.property (x.map (B.inclusion.map a))).toPresheafFiber
          U z F.obj t) =
      (geometricPointSitePoint B X.obj X.property x).toPresheafFiber
        ((smallEtaleBaseChange B a).obj U)
        ((geometricPointFiberBaseChangeIso B a x).hom.app U z)
        ((smallEtaleRingedSiteHom B a).inverseImage.obj F).obj
        ((((smallEtaleBaseChange B a).sheafAdjunctionContinuous (Type u)
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B X.obj X.property)).unit.app F).hom.app (op U) t) :=
  ConcreteCategory.congr_hom (smallEtalePullbackStalkIsoTypeU_inv_germ B a x F
    ((geometricPointFiber B Y.obj Y.property (x.map (B.inclusion.map a))).elementsMk U z)) t

attribute [irreducible] smallEtalePullbackStalkIsoTypeU

/-! ### The transported stalk ring is the étale local ring -/

attribute [local instance] CategoryTheory.Sheaf.ringObjRing

open Stacks.Sheaves.StalkTransport in
/-- The comparison of the stalk of the underlying sheaf of sets of the structure sheaf of the
small étale site, with its transported ring structure, with the étale local ring at a geometric
point. -/
def etaleStalkCmp (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S) :
    ((geometricPointSitePoint B S hS s).sheafFiber (A := Type u)).obj
        (SmallEtale.structureSheaf B S hS).ringSheaf → ↥(etaleLocalRing B S hS s) :=
  ringStalkComparison (geometricPointSitePoint B S hS s) (SmallEtale.structureSheaf B S hS)

open Stacks.Sheaves.StalkTransport in
/-- The comparison with the étale local ring is bijective. -/
theorem etaleStalkCmp_bijective (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S) :
    Function.Bijective (etaleStalkCmp B S hS s) :=
  bijective_ringStalkComparison (geometricPointSitePoint B S hS s)
    (SmallEtale.structureSheaf B S hS)

open Stacks.Sheaves.StalkTransport in
/-- The comparison with the étale local ring is multiplicative. -/
theorem etaleStalkCmp_mul (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
    (p q : ((geometricPointSitePoint B S hS s).sheafFiber (A := Type u)).obj
      (SmallEtale.structureSheaf B S hS).ringSheaf) :
    etaleStalkCmp B S hS s (p * q) = etaleStalkCmp B S hS s p * etaleStalkCmp B S hS s q :=
  ringStalkComparison_ringMulObj (geometricPointSitePoint B S hS s)
    (SmallEtale.structureSheaf B S hS) p q

/-- The comparison with the étale local ring preserves the unit. -/
theorem etaleStalkCmp_one (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S) :
    etaleStalkCmp B S hS s 1 = 1 := by
  obtain ⟨z, hz⟩ := (etaleStalkCmp_bijective B S hS s).2 1
  have h1 := etaleStalkCmp_mul B S hS s 1 z
  rw [one_mul, hz, mul_one] at h1
  exact h1.symm

open Stacks.Sheaves.StalkTransport in
/-- The comparison with the étale local ring carries a germ to the corresponding germ. -/
theorem etaleStalkCmp_germ (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
    (U : SmallEtale B S hS) (z : (geometricPointFiber B S hS s).obj U)
    (t : (SmallEtale.structureSheaf B S hS).obj.obj (op U)) :
    etaleStalkCmp B S hS s
        ((geometricPointSitePoint B S hS s).toPresheafFiber U z
          (SmallEtale.structureSheaf B S hS).ringSheaf.obj t) =
      (geometricPointSitePoint B S hS s).toPresheafFiber U z
        (SmallEtale.structureSheaf B S hS).obj t :=
  ringStalkComparison_germ (geometricPointSitePoint B S hS s)
    (SmallEtale.structureSheaf B S hS) U z t

open Stacks.Sheaves.StalkTransport in
/-- The comparison with the étale local ring is additive. -/
theorem etaleStalkCmp_add (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
    (p q : ((geometricPointSitePoint B S hS s).sheafFiber (A := Type u)).obj
      (SmallEtale.structureSheaf B S hS).ringSheaf) :
    etaleStalkCmp B S hS s (p + q) = etaleStalkCmp B S hS s p + etaleStalkCmp B S hS s q :=
  ringStalkComparison_ringAddObj (geometricPointSitePoint B S hS s)
    (SmallEtale.structureSheaf B S hS) p q

/-- The comparison with the étale local ring preserves the zero. -/
theorem etaleStalkCmp_zero (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S) :
    etaleStalkCmp B S hS s 0 = 0 := by
  have h := etaleStalkCmp_add B S hS s 0 0
  rw [add_zero] at h
  exact (add_left_cancel ((add_zero (etaleStalkCmp B S hS s 0)).trans h)).symm

/-- The comparison of the transported stalk ring with the étale local ring, as a ring
homomorphism. -/
def etaleStalkRingHom (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S) :
    ((geometricPointSitePoint B S hS s).sheafFiber (A := Type u)).obj
        (SmallEtale.structureSheaf B S hS).ringSheaf →+* ↥(etaleLocalRing B S hS s) where
  toFun := etaleStalkCmp B S hS s
  map_one' := etaleStalkCmp_one B S hS s
  map_mul' := etaleStalkCmp_mul B S hS s
  map_zero' := etaleStalkCmp_zero B S hS s
  map_add' := etaleStalkCmp_add B S hS s

/-- **The transported stalk ring of the structure sheaf at a geometric point is the étale local
ring of Stacks 03PS**, as a ring isomorphism.

This is what identifies the stalk at a geometric point of the structure sheaf of the small étale
site with a strictly henselian local ring
(`AlgebraicGeometry.strictlyHenselianLocalRing_etaleLocalRing`), and so what makes the stalk of
a sheaf of solutions of a polynomial system a set of solutions over such a ring — the shape
Stacks 04GX is stated at, and the one step (4) of the proof of
[Stacks 04I6](https://stacks.math.columbia.edu/tag/04I6) reads the comparison
`g⁻¹h_V ⟶ h_{X ×_Y V}` in. -/
def etaleStalkRingEquiv (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S) :
    ((geometricPointSitePoint B S hS s).sheafFiber (A := Type u)).obj
        (SmallEtale.structureSheaf B S hS).ringSheaf ≃+* ↥(etaleLocalRing B S hS s) :=
  RingEquiv.ofBijective (etaleStalkRingHom B S hS s) (etaleStalkCmp_bijective B S hS s)

/-- The comparison of the transported stalk ring with the étale local ring, as a monoid
homomorphism. -/
def etaleStalkHom (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S) :
    ((geometricPointSitePoint B S hS s).sheafFiber (A := Type u)).obj
        (SmallEtale.structureSheaf B S hS).ringSheaf →* ↥(etaleLocalRing B S hS s) :=
  (etaleStalkRingHom B S hS s).toMonoidHom

/-- The transported stalk ring of the structure sheaf at a geometric point, as a multiplicative
equivalence with the étale local ring of Stacks 03PS.  This is
`AlgebraicGeometry.etaleStalkRingEquiv` with the additive structure forgotten; it is what the
units square of Stacks 04HA consumes, where additivity is never used. -/
def etaleStalkMulEquiv (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S) :
    ((geometricPointSitePoint B S hS s).sheafFiber (A := Type u)).obj
        (SmallEtale.structureSheaf B S hS).ringSheaf ≃* ↥(etaleLocalRing B S hS s) :=
  (etaleStalkRingEquiv B S hS s).toMulEquiv

/-- A morphism of sheaves of sets acts on germs by its component. -/
theorem map_toPresheafFiber (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
    {F G : Sheaf (SmallEtale.topology B S hS) (Type u)} (ψ : F ⟶ G)
    (U : SmallEtale B S hS) (z : (geometricPointFiber B S hS s).obj U) (t : F.obj.obj (op U)) :
    ((geometricPointSitePoint B S hS s).sheafFiber (A := Type u)).map ψ
        ((geometricPointSitePoint B S hS s).toPresheafFiber U z F.obj t) =
      (geometricPointSitePoint B S hS s).toPresheafFiber U z G.obj (ψ.hom.app (op U) t) :=
  (geometricPointSitePoint B S hS s).toPresheafFiber_naturality_apply ψ.hom U z t

/-! ### The structure map on germs -/

/-- The structure map of `(a_small, a_small^♯)`, read on the inverse image, undoes the unit of
the adjunction. -/
theorem unit_comp_pushforward_fSharpSet :
    (smallEtaleRingedSiteHom B a).toposHom.adj.unit.app
        ((sheafCompose (SmallEtale.topology B Y.obj Y.property)
          (forget CommRingCat.{u})).obj (smallEtaleRingedSite B Y.obj Y.property).O) ≫
        (smallEtaleRingedSiteHom B a).toposHom.pushforward.map
          (smallEtaleRingedSiteHom B a).fSharpSet =
      (sheafCompose (SmallEtale.topology B Y.obj Y.property) (forget CommRingCat.{u})).map
        (smallEtaleRingedSiteHom B a).fsharp :=
  (Adjunction.homEquiv_unit (adj := (smallEtaleRingedSiteHom B a).toposHom.adj)
      (f := (smallEtaleRingedSiteHom B a).fSharpSet)).symm.trans
    (((smallEtaleRingedSiteHom B a).toposHom.adj.homEquiv _ _).apply_symm_apply _)

/-- On a section carried along the adjunction unit, the structure map on underlying sheaves of
sets is pullback of global functions along the base-change projection. -/
theorem fSharpSet_app_unit_app (U : SmallEtale B Y.obj Y.property)
    (t : (SmallEtale.structureSheaf B Y.obj Y.property).obj.obj (op U)) :
    (smallEtaleRingedSiteHom B a).fSharpSet.hom.app
        (op ((smallEtaleBaseChange B a).obj U))
        ((((smallEtaleBaseChange B a).sheafAdjunctionContinuous (Type u)
            (SmallEtale.topology B Y.obj Y.property)
            (SmallEtale.topology B X.obj X.property)).unit.app
          (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf).hom.app (op U) t) =
      ((structureSharpRing B a).app (op U)).hom t :=
  congrArg (fun k : (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf ⟶
      ((smallEtaleBaseChange B a).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).obj
          ((sheafCompose (SmallEtale.topology B X.obj X.property)
            (forget CommRingCat.{u})).obj (smallEtaleRingedSite B X.obj X.property).O) ↦
    k.hom.app (op U) t) (unit_comp_pushforward_fSharpSet B a)

/-- The same, for the structure map read as the forgetful image of the inverse-image structure
map of sheaves of commutative rings. -/
theorem forgetRingMap_fSharpRingMap_app_unit_app (U : SmallEtale B Y.obj Y.property)
    (t : (SmallEtale.structureSheaf B Y.obj Y.property).obj.obj (op U)) :
    (RingedTopos.forgetRingMap (smallEtaleRingedSiteHom B a).fSharpRingMap).hom.app
        (op ((smallEtaleBaseChange B a).obj U))
        ((((smallEtaleBaseChange B a).sheafAdjunctionContinuous (Type u)
            (SmallEtale.topology B Y.obj Y.property)
            (SmallEtale.topology B X.obj X.property)).unit.app
          (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf).hom.app (op U) t) =
      ((structureSharpRing B a).app (op U)).hom t :=
  (congrArg (fun k : (smallEtaleRingedSiteHom B a).inverseImage.obj
        ((sheafCompose (SmallEtale.topology B Y.obj Y.property)
          (forget CommRingCat.{u})).obj (smallEtaleRingedSite B Y.obj Y.property).O) ⟶
      (sheafCompose (SmallEtale.topology B X.obj X.property)
        (forget CommRingCat.{u})).obj (smallEtaleRingedSite B X.obj X.property).O ↦
    k.hom.app (op ((smallEtaleBaseChange B a).obj U))
      ((((smallEtaleBaseChange B a).sheafAdjunctionContinuous (Type u)
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B X.obj X.property)).unit.app
        (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf).hom.app (op U) t))
    (RingedSite.HomGeneral.forgetRing_map_fSharpRingMap
      (smallEtaleRingedSiteHom B a))).trans (fSharpSet_app_unit_app B a U t)

/-! ### The stalk of the structure map is the map of étale local rings -/

/-- At a geometric point, the stalk of the structure map `a⁻¹𝒪_Y ⟶ 𝒪_X` is, under the
identification of the transported stalk rings with the étale local rings, the map of étale local
rings `AlgebraicGeometry.etaleLocalRingMap`. -/
theorem etaleStalkCmp_fSharpSet
    (b : ((geometricPointSitePoint B Y.obj Y.property
        (x.map (B.inclusion.map a))).sheafFiber (A := Type u)).obj
      (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf) :
    etaleStalkCmp B X.obj X.property x
        (((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u)).map
          (X := (smallEtaleRingedSiteHom B a).inverseImage.obj
            (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf)
          (Y := (SmallEtale.structureSheaf B X.obj X.property).ringSheaf)
          (RingedTopos.forgetRingMap (smallEtaleRingedSiteHom B a).fSharpRingMap)
          ((smallEtalePullbackStalkIsoTypeU B a x).inv.app
            (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf b)) =
      (etaleLocalRingMap B a x).hom
        (etaleStalkCmp B Y.obj Y.property (x.map (B.inclusion.map a)) b) := by
  obtain ⟨U, z, s, rfl⟩ :=
    (geometricPointSitePoint B Y.obj Y.property
      (x.map (B.inclusion.map a))).toPresheafFiber_jointly_surjective
      (P := (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf.obj) b
  have e2 := map_toPresheafFiber B X.obj X.property x
    (F := (smallEtaleRingedSiteHom B a).inverseImage.obj
      (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf)
    (G := (SmallEtale.structureSheaf B X.obj X.property).ringSheaf)
    (RingedTopos.forgetRingMap (smallEtaleRingedSiteHom B a).fSharpRingMap)
    ((smallEtaleBaseChange B a).obj U)
    ((geometricPointFiberBaseChangeIso B a x).hom.app U z)
    ((((smallEtaleBaseChange B a).sheafAdjunctionContinuous (Type u)
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).unit.app
      (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf).hom.app (op U) s)
  have e3 := etaleStalkCmp_germ B X.obj X.property x ((smallEtaleBaseChange B a).obj U)
    ((geometricPointFiberBaseChangeIso B a x).hom.app U z)
    (((structureSharpRing B a).app (op U)).hom s)
  have hι : (etaleLocalRingMap B a x).hom
      ((geometricPointSitePoint B Y.obj Y.property (x.map (B.inclusion.map a))).toPresheafFiber
        U z (SmallEtale.structureSheaf B Y.obj Y.property).obj s) =
      (geometricPointSitePoint B X.obj X.property x).toPresheafFiber
        ((smallEtaleBaseChange B a).obj U)
        ((geometricPointFiberBaseChangeIso B a x).hom.app U z)
        (SmallEtale.structureSheaf B X.obj X.property).obj
        (((structureSharpRing B a).app (op U)).hom s) :=
    ConcreteCategory.congr_hom (etaleLocalRingMap_ι B a x
      (op ((geometricPointFiber B Y.obj Y.property
        (x.map (B.inclusion.map a))).elementsMk U z))) s
  rw [smallEtalePullbackStalkIsoTypeU_inv_germ_apply B a x _ U z s,
    etaleStalkCmp_germ B Y.obj Y.property (x.map (B.inclusion.map a)) U z s, hι]
  exact (congrArg (etaleStalkCmp B X.obj X.property x)
    (e2.trans (congrArg
      ((geometricPointSitePoint B X.obj X.property x).toPresheafFiber
        ((smallEtaleBaseChange B a).obj U)
        ((geometricPointFiberBaseChangeIso B a x).hom.app U z)
        (SmallEtale.structureSheaf B X.obj X.property).ringSheaf.obj)
      (forgetRingMap_fSharpRingMap_app_unit_app B a U s)))).trans e3

/-! ### Reflection of units -/

/-- The germ comparison is inverted by the stalk comparison. -/
theorem smallEtalePullbackStalkIsoTypeU_inv_hom_app
    (c : ((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u)).obj
      ((smallEtaleRingedSiteHom B a).inverseImage.obj
        (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf)) :
    (smallEtalePullbackStalkIsoTypeU B a x).inv.app
        (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf
        ((smallEtalePullbackStalkIsoTypeU B a x).hom.app
          (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf c) = c :=
  Iso.hom_inv_id_apply ((smallEtalePullbackStalkIsoTypeU B a x).app
    (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf) c

/-- A germ of `a⁻¹𝒪_Y` at `x̄` whose image in the stalk of `𝒪_X` is invertible is itself
invertible: its image in the étale local ring `(𝒪_Y)_ȳ` is invertible, because the map of étale
local rings is local. -/
theorem isUnit_hom_app_of_isUnit_fSharp
    (c : ((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u)).obj
      ((smallEtaleRingedSiteHom B a).inverseImage.obj
        (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf))
    (hc : IsUnit (((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u)).map
      (X := (smallEtaleRingedSiteHom B a).inverseImage.obj
        (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf)
      (Y := (SmallEtale.structureSheaf B X.obj X.property).ringSheaf)
      (RingedTopos.forgetRingMap (smallEtaleRingedSiteHom B a).fSharpRingMap) c)) :
    IsUnit ((smallEtalePullbackStalkIsoTypeU B a x).hom.app
      (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf c) := by
  have h1 : IsUnit ((etaleLocalRingMap B a x).hom
      (etaleStalkCmp B Y.obj Y.property (x.map (B.inclusion.map a))
        ((smallEtalePullbackStalkIsoTypeU B a x).hom.app
          (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf c))) := by
    rw [← etaleStalkCmp_fSharpSet B a x, smallEtalePullbackStalkIsoTypeU_inv_hom_app]
    exact hc.map (etaleStalkHom B X.obj X.property x)
  have h4 := (IsLocalHom.map_nonunit (f := (etaleLocalRingMap B a x).hom) _ h1).map
    (etaleStalkMulEquiv B Y.obj Y.property (x.map (B.inclusion.map a))).symm
  rwa [show (etaleStalkMulEquiv B Y.obj Y.property (x.map (B.inclusion.map a))).symm
      (etaleStalkCmp B Y.obj Y.property (x.map (B.inclusion.map a)) _) = _ from
    (etaleStalkMulEquiv B Y.obj Y.property
      (x.map (B.inclusion.map a))).symm_apply_apply _] at h4

/-- The comparison of Stacks 04KR is compatible with the two inclusions of units subsheaves. -/
theorem unitsComparison_hom_comp_unitsι :
    (smallEtaleRingedSiteHom B a).unitsComparison.hom ≫
      RingedTopos.unitsι (inverseImageRingedTopos (smallEtaleRingedSite B X.obj X.property).C
        (smallEtaleRingedSite B X.obj X.property).J
        (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property))
        (smallEtaleRingedSiteHom B a).toposHom) =
      (smallEtaleRingedSiteHom B a).inverseImage.map (RingedTopos.unitsι
        (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property))) := by
  rw [← RingedSite.HomGeneral.unitsComparison_inv_comp (smallEtaleRingedSiteHom B a)]
  exact Iso.hom_inv_id_assoc _ _

/-- A germ of the units subsheaf of `𝒪_Y` at `ȳ` gives a germ of the units subsheaf of
`a⁻¹𝒪_Y` at `x̄` lying over the given germ. -/
theorem map_unitsι_map_unitsComparison
    (c : ((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u)).obj
      ((smallEtaleRingedSiteHom B a).inverseImage.obj
        (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf))
    (w : ((geometricPointSitePoint B Y.obj Y.property
        (x.map (B.inclusion.map a))).sheafFiber (A := Type u)).obj
      (RingedTopos.units
        (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property))))
    (hw : ((geometricPointSitePoint B Y.obj Y.property
        (x.map (B.inclusion.map a))).sheafFiber (A := Type u)).map
        (RingedTopos.unitsι
          (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property))) w =
      (smallEtalePullbackStalkIsoTypeU B a x).hom.app
        (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf c) :
    ((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u)).map
        (RingedTopos.unitsι (inverseImageRingedTopos
          (smallEtaleRingedSite B X.obj X.property).C
          (smallEtaleRingedSite B X.obj X.property).J
          (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property))
          (smallEtaleRingedSiteHom B a).toposHom))
        (((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u)).map
          ((smallEtaleRingedSiteHom B a).unitsComparison.hom)
          ((smallEtalePullbackStalkIsoTypeU B a x).inv.app (RingedTopos.units
            (RingedSite.toRingedTopos
              (smallEtaleRingedSite B Y.obj Y.property))) w)) = c := by
  refine Eq.trans
    (((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u)).map_comp_apply
      _ _ _).symm ?_
  refine Eq.trans (congrArg (fun k ↦
    ((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u)).map k
      ((smallEtalePullbackStalkIsoTypeU B a x).inv.app (RingedTopos.units
        (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property))) w))
    (unitsComparison_hom_comp_unitsι B a)) ?_
  refine Eq.trans ?_ (smallEtalePullbackStalkIsoTypeU_inv_hom_app B a x c)
  refine Eq.trans ?_ (congrArg ((smallEtalePullbackStalkIsoTypeU B a x).inv.app
    (SmallEtale.structureSheaf B Y.obj Y.property).ringSheaf) hw)
  exact (ConcreteCategory.congr_hom
    ((smallEtalePullbackStalkIsoTypeU B a x).inv.naturality (RingedTopos.unitsι
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))) w).symm

/-- **Condition (3) of Stacks 04H9 for the small étale ringed-site morphism of a morphism of
schemes.** At a geometric point `x̄` of `X` the stalk of the structure map `a⁻¹𝒪_Y ⟶ 𝒪_X`
reflects units: it is the map of étale local rings `(𝒪_Y)_ȳ ⟶ (𝒪_X)_x̄`, which is local. -/
theorem reflectsUnitsObj_fSharpRingMap :
    RingedTopos.ReflectsUnitsObj
      ((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u))
      (smallEtaleRingedSiteHom B a).fSharpRingMap := by
  intro c hc
  have hc₀ := (RingedTopos.isUnit_iff_exists_map_unitsIncl
    (RingedTopos.ofStructureSheaf (SmallEtale.topology B X.obj X.property)
      (SmallEtale.commRingStructureSheaf B X.obj X.property))
    ((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u)) _).2 hc
  obtain ⟨w, hw⟩ := (RingedTopos.isUnit_iff_exists_map_unitsIncl
    (RingedTopos.ofStructureSheaf (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.commRingStructureSheaf B Y.obj Y.property))
    ((geometricPointSitePoint B Y.obj Y.property
      (x.map (B.inclusion.map a))).sheafFiber (A := Type u)) _).1
      (isUnit_hom_app_of_isUnit_fSharp B a x c hc₀)
  exact ⟨_, map_unitsι_map_unitsComparison B a x c w hw⟩

end AlgebraicGeometry

end
