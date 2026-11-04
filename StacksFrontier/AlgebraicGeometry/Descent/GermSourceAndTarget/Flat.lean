module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Topology.Category.TopCat.OpenNhds
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Flat
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Local
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.Topology.Sheaves.PresheafOfModules.StalkMap
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Flatness at a point is étale local on the source and target

A morphism of germs of schemes is flat when some representing morphism on an open
neighbourhood of the distinguished point induces a flat map of local rings there. This file
proves that this property is unchanged along étale changes of both the source and the target
germ, so that it is étale local on the source and target in the sense of
`AlgebraicGeometry.MorphismOfGerms.IsEtaleLocalOnSourceAndTarget`.

The proof reduces the two directions of an étale square to the two composition statements for
flatness of a module over a base: flatness over the target is unchanged when the base is
replaced by an étale intermediate scheme, and it is unchanged under pullback along a flat
morphism. Both are applied to the structure sheaf of the source regarded as a module over
itself, which identifies them with flatness of the stalk map.

## Main definitions

No new definitions are introduced: flatness of a morphism of germs is
`AlgebraicGeometry.MorphismOfGerms.IsFlat`, which this file imports.

## Main results

* `AlgebraicGeometry.MorphismOfGerms.isEtaleLocalOnSourceAndTarget_isFlat`: flatness of the
  map on local rings of a morphism of germs is étale local on the source and target.

## Implementation notes

The map on local rings of a germ morphism is represented by the stalk map of any representative
on a neighbourhood of the distinguished point. Flatness is expressed by the *existence* of a
representative with flat stalk map, which avoids choosing a representative in the definition;
that this is independent of the representative is the content of the private lemma
transporting flatness along agreement near the distinguished point.

Flatness of the stalk map of a morphism of schemes is matched with flatness of the structure
sheaf as a module over the base through a linear equivalence between the stalk of the unit
sheaf of modules and the stalk of the structure sheaf; this is needed because the two
predicates are stated for different objects, one for a morphism of ringed spaces and one for a
module over it.

## References

* [Stacks Project, Tag 04ND](https://stacks.math.columbia.edu/tag/04ND)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace MorphismOfGerms

section Helpers

/-- A section of the structure presheaf, read as a section of the structure presheaf regarded
as a module over itself.  The two carriers are the same type; recording the identification
keeps the statements below well-typed without unfolding `PresheafOfModules.unit`. -/
private def unitSection {X : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} X)
    (U : Opens X) :
    ToType (R.obj (Opposite.op U)) ≃
      ToType ((PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).obj (Opposite.op U)) :=
  Equiv.refl _

/-- The same identification, read through the underlying presheaf of abelian groups, which is
the spelling the germ map uses. -/
private def unitSectionPresheaf {X : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} X)
    (U : Opens X) :
    ToType (R.obj (Opposite.op U)) ≃
      ToType ((PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf.obj
        (Opposite.op U)) :=
  Equiv.refl _

private lemma unitSectionPresheaf_eq_unitSection {X : TopCat.{u}}
    (R : TopCat.Presheaf CommRingCat.{u} X) (U : Opens X)
    (s : ToType (R.obj (Opposite.op U))) :
    unitSectionPresheaf R U s = unitSection R U s := rfl

private lemma unitSection_mul {X : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} X)
    (U : Opens X) (r s : ToType (R.obj (Opposite.op U))) :
    r • unitSection R U s = unitSection R U (r * s) := rfl

private lemma unitSectionPresheaf_zero {X : TopCat.{u}}
    (R : TopCat.Presheaf CommRingCat.{u} X) (U : Opens X) :
    unitSectionPresheaf R U 0 = 0 := rfl

private lemma unitSectionPresheaf_map {X : TopCat.{u}}
    (R : TopCat.Presheaf CommRingCat.{u} X) {U V : Opens X} (i : V ⟶ U)
    (s : ToType (R.obj (Opposite.op U))) :
    (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf.map i.op
        (unitSectionPresheaf R U s) =
      unitSectionPresheaf R V (R.map i.op s) := rfl

private lemma unitGerm_res {X : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} X) (x : X)
    {U V : Opens X} (i : V ⟶ U) (hxV : x ∈ V) (s : ToType (R.obj (Opposite.op U))) :
    TopCat.Presheaf.germ (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf
        V x hxV (unitSectionPresheaf R V (R.map i.op s)) =
      TopCat.Presheaf.germ (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf
        U x (i.le hxV) (unitSectionPresheaf R U s) := by
  rw [← unitSectionPresheaf_map R i s]
  exact TopCat.Presheaf.germ_res_apply _ i x hxV _

private lemma unitGerm_smul {X : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} X) (x : X)
    (U : Opens X) (hxU : x ∈ U) (r s : ToType (R.obj (Opposite.op U))) :
    R.germ U x hxU r •
        TopCat.Presheaf.germ (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf
          U x hxU (unitSectionPresheaf R U s) =
      TopCat.Presheaf.germ (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf
        U x hxU (unitSectionPresheaf R U (r * s)) := by
  rw [unitSectionPresheaf_eq_unitSection, unitSectionPresheaf_eq_unitSection,
    ← unitSection_mul]
  exact (PresheafOfModules.germ_smul
    (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})) x U hxU r (unitSection R U s)).symm

private lemma unitGerm_zero {X : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} X) (x : X)
    (U : Opens X) (hxU : x ∈ U) :
    TopCat.Presheaf.germ (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf
      U x hxU (unitSectionPresheaf R U 0) = 0 := by
  rw [unitSectionPresheaf_zero, map_zero]

/-- The stalk of the structure presheaf regarded as a module over itself is free of rank one on
the germ of the unit section. -/
private noncomputable def unitStalkLinearEquiv {X : TopCat.{u}}
    (R : TopCat.Presheaf CommRingCat.{u} X) (x : X) :
    ToType (R.stalk x) ≃ₗ[ToType (R.stalk x)]
      ToType (TopCat.Presheaf.stalk
        (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf x) :=
  LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton (ToType (R.stalk x)) _
      (TopCat.Presheaf.germ (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf
        ⊤ x trivial (unitSectionPresheaf R ⊤ 1))) <| by
    have key (U : Opens X) (hxU : x ∈ U) (r : ToType (R.obj (Opposite.op U))) :
        LinearMap.toSpanSingleton (ToType (R.stalk x)) _
            (TopCat.Presheaf.germ (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf
              ⊤ x trivial (unitSectionPresheaf R ⊤ 1)) (R.germ U x hxU r) =
          TopCat.Presheaf.germ (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf
            U x hxU (unitSectionPresheaf R U r) := by
      rw [LinearMap.toSpanSingleton_apply,
        ← unitGerm_res R x (homOfLE (le_top (a := U))) hxU
          (1 : ToType (R.obj (Opposite.op ⊤))),
        unitGerm_smul, map_one, mul_one]
    constructor
    · rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨U, hxU, r, rfl⟩ := R.exists_germ_eq a
      rw [key, ← unitGerm_zero R x U hxU] at ha
      obtain ⟨V, hxV, iV, jV, hV⟩ := TopCat.Presheaf.germ_eq
        (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf x hxU hxU _ _ ha
      rw [unitSectionPresheaf_map, unitSectionPresheaf_map] at hV
      have hres : R.map iV.op r = R.map jV.op 0 := (unitSectionPresheaf R V).injective hV
      rw [← TopCat.Presheaf.germ_res_apply R iV x hxV, hres, map_zero, map_zero]
    · intro m
      obtain ⟨U, hxU, m₀, hm₀⟩ := TopCat.Presheaf.exists_germ_eq
        (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf m
      exact ⟨R.germ U x hxU ((unitSectionPresheaf R U).symm m₀), by
        rw [key, Equiv.apply_symm_apply]; exact hm₀⟩

/-- Flatness of a morphism of ringed spaces at a point is flatness over the target of the
structure sheaf, regarded as a module over itself, at that point. -/
private lemma isFlatAt_iff_isFlatOverAt_unit {T U : RingedSpace.{u}} (f : T ⟶ U) (x : T) :
    IsFlatAt f x ↔ IsFlatOverAt f (SheafOfModules.unit (structureSheafRing T)) x := by
  let M : PresheafOfModules.{u} (T.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
    (SheafOfModules.unit (structureSheafRing T)).val
  let : Module (U.presheaf.stalk (f.hom.base x)) (T.presheaf.stalk x) :=
    Module.compHom _ (f.hom.stalkMap x).hom
  let : Module (U.presheaf.stalk (f.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) :=
    Module.compHom _ (f.hom.stalkMap x).hom
  let e : (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)
      ≃ₗ[T.presheaf.stalk x] (T.presheaf.stalk x) :=
    (unitStalkLinearEquiv T.presheaf x).symm
  let e' : (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)
      ≃ₗ[U.presheaf.stalk (f.hom.base x)] (T.presheaf.stalk x) :=
    { e.toAddEquiv with
      map_smul' := fun r m ↦ e.map_smul ((f.hom.stalkMap x).hom r) m }
  constructor
  · intro hf
    let : Module.Flat (U.presheaf.stalk (f.hom.base x)) (T.presheaf.stalk x) := hf
    exact Module.Flat.of_linearEquiv e'
  · intro hf
    let : Module.Flat (U.presheaf.stalk (f.hom.base x))
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) := hf
    exact Module.Flat.of_linearEquiv e'.symm

/-- Flatness of the stalk map of a morphism of schemes at a point is flatness over the target
of the structure sheaf, regarded as a module over itself, at that point. -/
public lemma flat_stalkMap_iff_isFlatOverAt_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    (f.stalkMap x).hom.Flat ↔
      IsFlatOverAt f.toLRSHom.toShHom (SheafOfModules.unit X.ringCatSheaf) x := by
  show IsFlatAt f.toLRSHom.toShHom x ↔ _
  exact isFlatAt_iff_isFlatOverAt_unit f.toLRSHom.toShHom x

/-- Flatness of the stalk map of a representative of a morphism of germs at the distinguished
point. -/
private abbrev RepresentativeFlat {X Y : GermOfScheme.{u}} (f : Representative X Y) : Prop :=
  (f.hom.stalkMap ⟨X.point, f.mem_source⟩).hom.Flat

/-- Flatness of a stalk map only depends on the point through its identity. -/
private lemma flat_stalkMap_congr_point {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x x' : X) (h : x = x') :
    (f.stalkMap x).hom.Flat ↔ (f.stalkMap x').hom.Flat := by
  cases h
  rfl

/-- Flatness of a stalk map only depends on the morphism through its identity. -/
private lemma flat_stalkMap_congr_hom {X Y : Scheme.{u}}
    (f g : X ⟶ Y) (h : f = g) (x : X) :
    (f.stalkMap x).hom.Flat ↔ (g.stalkMap x).hom.Flat := by
  cases h
  rfl

/-- Restricting a representative to a smaller neighbourhood does not change flatness at the
distinguished point. -/
private lemma representativeFlat_restrictRepresentative {X Y : GermOfScheme.{u}}
    (f : Representative X Y) (U : X.scheme.Opens)
    (hxU : X.point ∈ U) (hU : U ≤ f.source) :
    RepresentativeFlat (restrictRepresentative f U hxU hU) ↔ RepresentativeFlat f := by
  let i := X.scheme.homOfLE hU
  let xU : U.toScheme := ⟨X.point, hxU⟩
  have hcomp : (restrictRepresentative f U hxU hU).hom.stalkMap xU =
      f.hom.stalkMap (i xU) ≫ i.stalkMap xU :=
    Scheme.Hom.stalkMap_comp i f.hom xU
  have hbij : Function.Bijective (i.stalkMap xU).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp
      ((IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 xU)
  show ((restrictRepresentative f U hxU hU).hom.stalkMap xU).hom.Flat ↔
    (f.hom.stalkMap ⟨X.point, f.mem_source⟩).hom.Flat
  rw [hcomp]
  exact (RingHom.Flat.comp_iff_of_bijective_left (f := (f.hom.stalkMap (i xU)).hom) hbij).trans
    (flat_stalkMap_congr_point f.hom (i xU) _ (Scheme.homOfLE_apply' hU X.point hxU))

/-- Representatives agreeing near the distinguished point are simultaneously flat there. -/
private lemma representativeFlat_congr_agreeNear {X Y : GermOfScheme.{u}}
    (f g : Representative X Y) (h : f.AgreeNear g) :
    RepresentativeFlat f ↔ RepresentativeFlat g := by
  obtain ⟨U, hxU, hUf, hUg, hfg⟩ := h
  have heq : restrictRepresentative f U hxU hUf = restrictRepresentative g U hxU hUg :=
    representative_ext_of_source_hom rfl (by simpa [restrictRepresentative] using hfg)
  rw [← representativeFlat_restrictRepresentative f U hxU hUf,
    ← representativeFlat_restrictRepresentative g U hxU hUg, heq]

/-- Along a flat morphism of schemes, the pullback of the structure sheaf of the target is the
structure sheaf of the source. -/
private noncomputable def pullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (modulePullback f.toLRSHom.toShHom).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  let f' : X.toRingedSpace ⟶ Y.toRingedSpace := f.toLRSHom.toShHom
  let : (Opens.map f'.hom.base).Final := CategoryTheory.final_of_representablyFlat _
  let : (SheafOfModules.pushforward (structureSheafHom f')).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f'
  let α := _root_.SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f')
  have : IsIso α := by dsimp [α]; infer_instance
  exact (asIso α :)

/-- Flatness over the target at a point transfers along an isomorphism of modules on a ringed
space. -/
private lemma isFlatOverAt_of_iso {Y S : RingedSpace.{u, u}}
    (p : Y ⟶ S) {G G' : SheafOfModules.{u} (structureSheafRing Y)}
    (e : G ≅ G') (y : Y) (hG : IsFlatOverAt p G y) : IsFlatOverAt p G' y := by
  let M : PresheafOfModules.{u}
      (Y.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := G.val
  let N : PresheafOfModules.{u}
      (Y.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := G'.val
  let : Module (S.presheaf.stalk (p.hom.base y)) (Y.presheaf.stalk y) :=
    Module.compHom _ (p.hom.stalkMap y).hom
  let : Module (S.presheaf.stalk (p.hom.base y))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf y) :=
    Module.compHom _ (p.hom.stalkMap y).hom
  let : Module (S.presheaf.stalk (p.hom.base y))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf y) :=
    Module.compHom _ (p.hom.stalkMap y).hom
  let : Module.Flat (S.presheaf.stalk (p.hom.base y))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf y) := hG
  let eL := stalkMapLinear M N e.hom.val y
  have hbij : Function.Bijective eL := by
    let eP : M ≅ N :=
      { hom := e.hom.val
        inv := e.inv.val
        hom_inv_id := congrArg (fun φ : G ⟶ G => φ.val) e.hom_inv_id
        inv_hom_id := congrArg (fun φ : G' ⟶ G' => φ.val) e.inv_hom_id }
    let qIso := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
      ((PresheafOfModules.toPresheaf (Y.presheaf ⋙
        forget₂ CommRingCat.{u} RingCat.{u})).mapIso eP)
    show Function.Bijective (ConcreteCategory.hom qIso.hom)
    exact (ConcreteCategory.isIso_iff_bijective qIso.hom).mp (Iso.isIso_hom qIso)
  let eY : (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf y) ≃ₗ[
      S.presheaf.stalk (p.hom.base y)]
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf y) :=
    { (LinearEquiv.ofBijective eL hbij) with
      map_smul' := by
        intro r m
        show eL ((p.hom.stalkMap y).hom r • m) = (p.hom.stalkMap y).hom r • eL m
        exact eL.map_smul _ _ }
  exact Module.Flat.of_linearEquiv eY.symm

/-- Flatness over the target at a point is invariant under an isomorphism of modules on a
ringed space. -/
private lemma isFlatOverAt_iff_of_iso {Y S : RingedSpace.{u, u}}
    (p : Y ⟶ S) {G G' : SheafOfModules.{u} (structureSheafRing Y)}
    (e : G ≅ G') (y : Y) : IsFlatOverAt p G y ↔ IsFlatOverAt p G' y :=
  ⟨isFlatOverAt_of_iso p e y, isFlatOverAt_of_iso p e.symm y⟩

/-- Flatness of a stalk map is unchanged when the target is replaced by an étale intermediate
scheme. -/
private lemma flat_stalkMap_comp_right_iff {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Etale g] (x : X) :
    ((f ≫ g).stalkMap x).hom.Flat ↔ (f.stalkMap x).hom.Flat := by
  let : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  rw [flat_stalkMap_iff_isFlatOverAt_unit, flat_stalkMap_iff_isFlatOverAt_unit]
  exact isFlatOverAt_comp_iff_of_etale f g (SheafOfModules.unit X.ringCatSheaf) x

/-- Flatness of a stalk map is unchanged when the source is replaced by an étale cover of it. -/
private lemma flat_stalkMap_comp_left_iff {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (f : Y ⟶ Z) [Etale a] (x : X) :
    ((a ≫ f).stalkMap x).hom.Flat ↔ (f.stalkMap (a x)).hom.Flat := by
  let G := SheafOfModules.unit Y.ringCatSheaf
  let : G.IsQuasicoherent := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Y
  exact (flat_stalkMap_iff_isFlatOverAt_unit (a ≫ f) x).trans <|
    (isFlatOverAt_iff_of_iso _ (pullbackUnitIso a) x).symm.trans <|
      (isFlatOverAt_iff_modulePullback_isFlatOverAt a f G x (Flat.stalkMap a x)).symm.trans
        (flat_stalkMap_iff_isFlatOverAt_unit f (a x)).symm

/-- In a commutative square of schemes with étale vertical arrows, the horizontal arrows have
simultaneously flat stalk maps at corresponding points. -/
private lemma flat_stalkMap_iff_of_etale_square
    {U' U V' V : Scheme.{u}}
    (a : U' ⟶ U) (b : V' ⟶ V) (h' : U' ⟶ V') (h : U ⟶ V)
    [Etale a] [Etale b] (hsq : a ≫ h = h' ≫ b) (x : U') :
    (h.stalkMap (a x)).hom.Flat ↔ (h'.stalkMap x).hom.Flat := by
  calc
    (h.stalkMap (a x)).hom.Flat ↔ ((a ≫ h).stalkMap x).hom.Flat :=
      (flat_stalkMap_comp_left_iff a h x).symm
    _ ↔ ((h' ≫ b).stalkMap x).hom.Flat :=
      flat_stalkMap_congr_hom (a ≫ h) (h' ≫ b) hsq x
    _ ↔ (h'.stalkMap x).hom.Flat := flat_stalkMap_comp_right_iff h' b x

/-- Precomposing a representative with an étale representative does not change flatness at the
distinguished point. -/
private lemma representativeFlat_compRepresentative_left
    {X Y Z : GermOfScheme.{u}}
    (a : Representative X Y) (r : Representative Y Z) [Etale a.hom] :
    RepresentativeFlat (compRepresentative a r) ↔ RepresentativeFlat r := by
  let c := compRepresentative a r
  let k := (a.source.ι.isoImage (a.hom ⁻¹ᵁ r.source)).inv ≫ (a.hom ∣_ r.source)
  have hk : k ≫ r.hom = c.hom := by
    dsimp [k, c, compRepresentative]
    rfl
  have hp : k ⟨X.point, c.mem_source⟩ = ⟨Y.point, r.mem_source⟩ := by
    apply Subtype.ext
    show r.source.ι ((a.hom ∣_ r.source)
      ((a.source.ι.isoImage (a.hom ⁻¹ᵁ r.source)).inv ⟨X.point, _⟩)) = Y.point
    rw [← a.map_point, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
    show (((a.source.ι.isoImage _).inv ≫ (a.hom ⁻¹ᵁ r.source).ι ≫ a.hom)
      ⟨X.point, c.mem_source⟩) = a.hom ⟨X.point, a.mem_source⟩
    rw [← Category.assoc, Scheme.Opens.isoImage_ι_inv_ι]
    show a.hom (X.scheme.homOfLE _ ⟨X.point, c.mem_source⟩) = _
    exact congrArg a.hom (Subtype.ext (Scheme.homOfLE_apply _ ⟨X.point, c.mem_source⟩))
  have : Etale k := by dsimp [k]; infer_instance
  let x : c.source.toScheme := ⟨X.point, c.mem_source⟩
  show (c.hom.stalkMap x).hom.Flat ↔ (r.hom.stalkMap ⟨Y.point, r.mem_source⟩).hom.Flat
  rw [← hp]
  exact (flat_stalkMap_iff_of_etale_square k (𝟙 Z.scheme) c.hom r.hom
    (by rw [hk]; rfl) x).symm

/-- Postcomposing a representative with an étale representative does not change flatness at
the distinguished point. -/
private lemma representativeFlat_compRepresentative_right
    {X Y Z : GermOfScheme.{u}}
    (r : Representative X Y) (b : Representative Y Z) [Etale b.hom] :
    RepresentativeFlat (compRepresentative r b) ↔ RepresentativeFlat r := by
  let c := compRepresentative r b
  let W := r.hom ⁻¹ᵁ b.source
  let i := (r.source.ι.isoImage W).inv ≫ W.ι
  let j := (r.source.ι.isoImage W).inv ≫ (r.hom ∣_ b.source)
  have hsquare : i ≫ r.hom = j ≫ b.source.ι := by
    calc
      i ≫ r.hom = (r.source.ι.isoImage W).inv ≫ W.ι ≫ r.hom := by
        simp [i]
      _ = (r.source.ι.isoImage W).inv ≫ ((r.hom ∣_ b.source) ≫ b.source.ι) := by
        rw [morphismRestrict_ι]
      _ = j ≫ b.source.ι := by simp [j, Category.assoc]
  have hcomp : j ≫ b.hom = c.hom := by
    dsimp [j, c, W, compRepresentative]
    rfl
  let x : c.source.toScheme := ⟨X.point, c.mem_source⟩
  have hinc : i ≫ r.source.ι = c.source.ι := by
    dsimp [i, c, W, compRepresentative]
    rw [Scheme.Opens.isoImage_ι_inv_ι]
    simp
  have hi : i x = ⟨X.point, r.mem_source⟩ := by
    apply Subtype.ext
    show r.source.ι (i x) = X.point
    exact (Scheme.Hom.comp_apply i r.source.ι x).symm.trans
      (congrArg (fun m : c.source.toScheme ⟶ X.scheme => m x) hinc)
  have : Etale i := by dsimp [i]; infer_instance
  show (c.hom.stalkMap x).hom.Flat ↔ (r.hom.stalkMap ⟨X.point, r.mem_source⟩).hom.Flat
  rw [← hi]
  exact (flat_stalkMap_congr_hom (j ≫ b.hom) c.hom hcomp.symm x).trans
    ((flat_stalkMap_comp_right_iff j b.hom x).trans
      (flat_stalkMap_iff_of_etale_square i b.source.ι j r.hom hsquare x).symm)

end Helpers

section Helpers

/-- Flatness of a morphism of germs is flatness of any one of its representatives. -/
private lemma isFlat_iff_representativeFlat {X Y : GermOfScheme.{u}}
    (f : MorphismOfGerms X Y) (g : Representative X Y) (hg : mk g = f) :
    IsFlat f ↔ RepresentativeFlat g := by
  refine ⟨?_, fun hflat ↦ ⟨g, hg, hflat⟩⟩
  rintro ⟨g', rfl, hflat⟩
  exact (representativeFlat_congr_agreeNear g' g (mk_eq_mk_iff.mp hg.symm)).mp hflat

/-- Precomposing with an étale morphism of germs does not change flatness. -/
private lemma isFlat_comp_left_iff
    {X Y Z : GermOfScheme.{u}} (a : MorphismOfGerms X Y) (h : MorphismOfGerms Y Z)
    (ha : IsEtale a) : IsFlat (comp a h) ↔ IsFlat h := by
  obtain ⟨aR, haR, haEtale⟩ := ha
  obtain ⟨r, hr⟩ := exists_rep h
  let c := compRepresentative aR r
  have hc : mk c = comp a h := by rw [← haR, ← hr, comp_mk]
  let : Etale aR.hom := haEtale
  rw [isFlat_iff_representativeFlat (comp a h) c hc,
    isFlat_iff_representativeFlat h r hr, representativeFlat_compRepresentative_left aR r]

/-- Postcomposing with an étale morphism of germs does not change flatness. -/
private lemma isFlat_comp_right_iff
    {X Y Z : GermOfScheme.{u}} (h : MorphismOfGerms X Y) (b : MorphismOfGerms Y Z)
    (hb : IsEtale b) : IsFlat (comp h b) ↔ IsFlat h := by
  obtain ⟨bR, hbR, hbEtale⟩ := hb
  obtain ⟨r, hr⟩ := exists_rep h
  let c := compRepresentative r bR
  have hc : mk c = comp h b := by rw [← hr, ← hbR, comp_mk]
  let : Etale bR.hom := hbEtale
  rw [isFlat_iff_representativeFlat (comp h b) c hc,
    isFlat_iff_representativeFlat h r hr, representativeFlat_compRepresentative_right r bR]

end Helpers

/-- Flatness of the map on local rings of a morphism of germs is étale local on
both source and target. -/
@[stacks 04ND]
theorem isEtaleLocalOnSourceAndTarget_isFlat :
    IsEtaleLocalOnSourceAndTarget (@IsFlat.{u}) := by
  refine ⟨fun a b h' h ha hb hs ↦ ?_⟩
  rw [← isFlat_comp_left_iff a h ha, ← isFlat_comp_right_iff h' b hb, hs]

end MorphismOfGerms

end AlgebraicGeometry
