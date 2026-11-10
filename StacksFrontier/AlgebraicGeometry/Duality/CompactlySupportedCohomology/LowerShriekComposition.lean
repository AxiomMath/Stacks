module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.Composition
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.CompositionLowerShriek
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.LowerShriekAdjunction
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompactificationMap

/-!
# `Rg_! ∘ Rf_! = R(g ∘ f)_!`

In Situation [Stacks, Tag 0F42] let `f : X ⟶ Y` and `g : Y ⟶ Z` be composable morphisms of
`FTS_S`. The composition `Rg_! Rf_! K` of [Stacks, Tag 0G54] is `R(g ∘ f)_! K`
([Stacks, Tag 0G55]). Following the source, both pro-objects are compared through their functors
of points on `D^b_{Coh}(𝒪_Z)`: for `(M_n)` giving `Rf_! K`,

`Hom(Rg_! Rf_! K, L) = colim_n Hom(Rg_! M_n, L) = colim_n Hom(M_n, g^! L) = Hom(Rf_! K, g^! L)
  = Hom(K, f^! g^! L) = Hom(K, (g ∘ f)^! L) = Hom(R(g ∘ f)_! K, L)`,

naturally in `L`, by [Stacks, Tag 0G51] (twice, and once more for `g ∘ f`) and
`(g ∘ f)^! = f^! ∘ g^!` ([Stacks, Tag 0ATX]).

## Main definitions

* `CategoryTheory.ProSeq.pointsIsoHomConst`: the functor of points of a pro-object `P` is
  `L ↦ Hom(P, L)`.
* `CategoryTheory.ProSeq.pointsFunctorIsoMap`: for `ι` fully faithful, the functor of points of
  `P` is that of `ι P` restricted along `ι`.
* `Stacks.Duality.UpperShriekDuality.upperShriekStdPlusCoh`: `f^!` on `D^+_{Coh}`, at the standard
  model.
* `Stacks.Duality.UpperShriekDuality.upperShriekStdCompIso`: `f^! ∘ g^! ≅ (g ∘ f)^!` there.
* `AlgebraicGeometry.lowerShriekCompIso`: **[Stacks, Tag 0G55]**.

## References

* [Stacks Project, Tag 0G55](https://stacks.math.columbia.edu/tag/0G55)
* [Stacks Project, Tag 0G54](https://stacks.math.columbia.edu/tag/0G54)
* [Stacks Project, Tag 0G51](https://stacks.math.columbia.edu/tag/0G51)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u

namespace CategoryTheory.ProSeq

attribute [local instance] CategoryTheory.Functor.hasLeftKanExtension_of_type
  CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_type

variable {𝒞 : Type v} [Category.{v} 𝒞] {𝒟 : Type v} [Category.{v} 𝒟]
  {𝒟' : Type v} [Category.{v} 𝒟']

/-- The functor of points of a pro-object `P` is `L ↦ Hom_{Pro}(P, L)`. -/
def pointsIsoHomConst (P : ProSeq 𝒟) : P.points ≅ const ⋙ coyoneda.obj (op P) :=
  NatIso.ofComponents (fun L => (homConstEquiv P L).symm.toIso) (fun {L L'} g => by
    ext x
    obtain ⟨φ, rfl⟩ := (homConstEquiv P L).surjective x
    apply (homConstEquiv P L').injective
    change homConstEquiv P L' ((homConstEquiv P L').symm (P.points.map g (homConstEquiv P L φ))) =
      homConstEquiv P L' ((homConstEquiv P L).symm (homConstEquiv P L φ) ≫ const.map g)
    rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply, homConstEquiv_apply, homConstEquiv_apply]
    exact coyonedaEquiv_naturality φ.unop.hom g)

/-- The functors of points of the values of `G : 𝒞 ⥤ Pro-𝒟` are `L ↦ Hom_{Pro}(G K, L)`. -/
def pointsFunctorIso (G : 𝒞 ⥤ ProSeq 𝒟) :
    pointsFunctor G ≅ G.op ⋙ coyoneda ⋙ (Functor.whiskeringLeft _ _ _).obj const :=
  NatIso.ofComponents (fun K => pointsIsoHomConst (G.obj K.unop)) (fun {K K'} k => by
    ext L x
    obtain ⟨φ, rfl⟩ := (homConstEquiv (G.obj K.unop) L).surjective x
    apply (homConstEquiv (G.obj K'.unop) L).injective
    change homConstEquiv (G.obj K'.unop) L ((homConstEquiv (G.obj K'.unop) L).symm
        ((G.map k.unop).unop.hom.app L (homConstEquiv (G.obj K.unop) L φ))) =
      homConstEquiv (G.obj K'.unop) L (G.map k.unop ≫
        (homConstEquiv (G.obj K.unop) L).symm (homConstEquiv (G.obj K.unop) L φ))
    rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    rfl)

/-- For `ι` fully faithful, the functor of points of a pro-object `P` is the functor of points of
`ι P` restricted along `ι`: the left Kan extension along a fully faithful functor restricts back
to the functor extended. -/
def pointsFunctorIsoMap (ι : 𝒟 ⥤ 𝒟') [ι.Full] [ι.Faithful] (G : 𝒞 ⥤ ProSeq 𝒟) :
    pointsFunctor G ≅ pointsFunctor (G ⋙ map ι) ⋙ (Functor.whiskeringLeft _ _ _).obj ι :=
  NatIso.ofComponents (fun K =>
      have := Functor.hasPointwiseLeftKanExtension_of_type ι (G.obj K.unop).points
      @asIso _ _ _ _ (ι.lanUnit.app (G.obj K.unop).points)
        (@NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun X =>
          (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit ι (G.obj K.unop).points
            (ι.obj X)).isIso_hom_app))
    (fun k => ι.lanUnit.naturality (G.map k.unop).unop.hom)

/-- The functor of points of the pro-object of `(M_n)` is `colim_n Hom(M_n, -)`. -/
def ofPointsIso (M : ℕᵒᵖ ⥤ 𝒟) : (of M).points ≅ colimit (M.rightOp ⋙ coyoneda) :=
  Pro.seqHomColimIso M ≪≫
    (HasColimit.isoOfEquivalence (opOpEquivalence ℕ) (NatIso.ofComponents (fun _ => Iso.refl _)))

end CategoryTheory.ProSeq

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category.{v} C] (P : ObjectProperty C)

/-- Morphisms in a full subcategory are morphisms in the ambient category, as an isomorphism of
`Hom` functors. -/
def ιOpCompCoyonedaIso :
    P.ι.op ⋙ coyoneda ⋙ (Functor.whiskeringLeft _ _ _).obj P.ι ≅ coyoneda :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents
    (fun _ => P.fullyFaithfulι.homEquiv.symm.toIso) (fun _ => rfl)) (fun _ => rfl)

end CategoryTheory.ObjectProperty

namespace Stacks.Duality.UpperShriekDuality

open TwistedInverseImageDuality

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  (c : CompactificationOf (Over.mk f.left))

/-- **`f^!` maps `D^+_{Coh}(𝒪_Y)` into `D^+_{Coh}(𝒪_X)`** at the standard model: this is
[Stacks, Tag 0AU1]. -/
theorem plusCoh_upperShriekStd_obj (L : (plusCoh Y.left).FullSubcategory) :
    plusCoh X.left ((upperShriekStd f c).obj L) :=
  (plusCoh_iff _).2 (derivedCategoryBPlus_upperShriek f c _ ((plusCoh_iff L.obj).1 L.property))

/-- `f^! : D^+_{Coh}(𝒪_Y) ⥤ D^+_{Coh}(𝒪_X)` at the standard model. -/
abbrev upperShriekStdPlusCoh :
    (plusCoh Y.left).FullSubcategory ⥤ (plusCoh X.left).FullSubcategory :=
  (plusCoh X.left).lift (upperShriekStd f c) (plusCoh_upperShriekStd_obj f c)

/-- `D^+_{Coh}(𝒪_Y)` at the standard model, read in `D_{QCoh}(𝒪_Y)` at the locally small one. -/
abbrev plusCohToQCoh (Y : Scheme.{u}) [IsLocallyNoetherian Y] :=
  ObjectProperty.lift (Coherator.quasiCoherentProp Y)
    ((plusCoh Y).ι ⋙ (comparison Y).functor) (fun M => plusCoh_le_qcoh _ M.property)

/-- `D^+_{Coh}(𝒪_Y)` at the standard model, read in `D^+_{QCoh}(𝒪_Y)` at the locally small one. -/
abbrev plusCohToQCohPlus (Y : Scheme.{u}) [IsLocallyNoetherian Y] :
    (plusCoh Y).FullSubcategory ⥤ quasiCoherentDerivedCategoryPlusOfModel Y :=
  ObjectProperty.lift _ (plusCohToQCoh Y)
    (fun M => ((plusCoh_iff M.obj).1 M.property).1)

variable {Z : FTS S} (g : Y ⟶ Z) (cf : CompactificationOf (Over.mk f.left))
  (cg : CompactificationOf (Over.mk g.left)) (cfg : CompactificationOf (Over.mk (f ≫ g).left))

/-- `g^!` at the standard model, read back at the locally small model, is `g^!`. -/
def upperShriekStdPlusCohCompIso :
    upperShriekStdPlusCoh g cg ⋙ plusCohToQCoh Y.left ≅ plusCohToQCoh Z.left ⋙ upperShriek g cg :=
  NatIso.ofComponents
    (fun L => ObjectProperty.isoMk _ ((comparison Y.left).counitIso.app
      ((upperShriek g cg).obj ((plusCohToQCoh Z.left).obj L)).obj))
    (fun l => by
      apply ObjectProperty.hom_ext
      exact (comparison Y.left).counitIso.hom.naturality
        ((upperShriek g cg).map ((plusCohToQCoh Z.left).map l)).hom)

/-- `(g ∘ f)^! ≅ f^! ∘ g^!` on `D^+_{Coh}(𝒪_Z)`, read at the standard model. -/
def upperShriekCompStdIso :
    plusCohToQCoh Z.left ⋙ upperShriek g cg ⋙ upperShriek f cf ⋙
        (ObjectProperty.ι _ : quasiCoherentDerivedCategory X.left ⥤ _) ⋙
          (comparison X.left).inverse ≅ upperShriekStd (f ≫ g) cfg :=
  Functor.isoWhiskerLeft (plusCohToQCohPlus Z.left)
    (Functor.isoWhiskerRight (upperShriekCompIso f g cf cg cfg).symm
      (ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (comparison X.left).inverse))

/-- **`f^! ∘ g^! ≅ (g ∘ f)^!` on `D^+_{Coh}`** at the standard model, for arbitrary
compactifications: [Stacks, Tag 0ATX] (`Stacks.Duality.upperShriekCompIso`) read through the
comparison of models. -/
def upperShriekStdCompIso :
    upperShriekStdPlusCoh g cg ⋙ upperShriekStd f cf ≅ upperShriekStd (f ≫ g) cfg :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (upperShriekStdPlusCohCompIso g cg)
      (upperShriek f cf ⋙ (ObjectProperty.ι _ : quasiCoherentDerivedCategory X.left ⥤ _) ⋙
        (comparison X.left).inverse) ≪≫
    Functor.associator _ _ _ ≪≫ upperShriekCompStdIso f g cf cg cfg

end Stacks.Duality.UpperShriekDuality

namespace AlgebraicGeometry

open Stacks.Duality Stacks.Duality.TwistedInverseImageDuality Stacks.Duality.UpperShriekDuality

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 10000] CategoryTheory.Functor.hasLeftKanExtension_of_type
  CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_type
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens
attribute [local instance] Stacks.AssociatedSheaf.abelianModulesRingSheaf

variable {S : Scheme.{u}} [IsNoetherian S] {X Y Z : FTS S}

/-- **`Hom(Rg_! M, L) = Hom_Y(M, g^! L)`**, naturally in `M` in `D^b_{Coh}(𝒪_Y)` and `L` in
`D^b_{Coh}(𝒪_Z)`: [Stacks, Tag 0G51] for `g`, the functor of points of `Rg_! M` being read in
`Pro-D^+_{Coh}(𝒪_Z)`. -/
def lowerShriekPointsFunctorIsoStd (g : Y ⟶ Z) (cg : CompactificationOf (Over.mk g.left)) :
    ProSeq.pointsFunctor (lowerShriek g cg) ≅
      ((boundedCoherentDerived Y.left).ι.op ⋙ coyoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj (upperShriekStd g cg)) ⋙
          (Functor.whiskeringLeft _ _ _).obj (boundedCoherentToPlusCoh Z.left) :=
  ProSeq.pointsFunctorIsoMap (boundedCoherentToPlusCoh Z.left) (lowerShriek g cg) ≪≫
    Functor.isoWhiskerRight (ProSeq.pointsFunctorIso _) _ ≪≫
    Functor.isoWhiskerRight (lowerShriekHomIso g cg) _

/-- `AlgebraicGeometry.lowerShriekPointsFunctorIsoStd` with `g^! L` read in `D^+_{Coh}(𝒪_Y)`. -/
def lowerShriekPointsFunctorIso (g : Y ⟶ Z) (cg : CompactificationOf (Over.mk g.left)) :
    ProSeq.pointsFunctor (lowerShriek g cg) ≅
      (boundedCoherentToPlusCoh Y.left).op ⋙ coyoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (boundedCoherentToPlusCoh Z.left ⋙ upperShriekStdPlusCoh g cg) :=
  lowerShriekPointsFunctorIsoStd g cg ≪≫
    NatIso.ofComponents (fun M => NatIso.ofComponents (fun L =>
        ((plusCoh Y.left).fullyFaithfulι.homEquiv
          (X := (boundedCoherentToPlusCoh Y.left).obj M.unop)
          (Y := (upperShriekStdPlusCoh g cg).obj
            ((boundedCoherentToPlusCoh Z.left).obj L))).symm.toIso)
      (fun _ => rfl)) (fun _ => rfl)

/-- **`Hom(Rg_! Rf_! K, L) = Hom_X(K, f^! g^! L)`**, naturally in `L` in `D^b_{Coh}(𝒪_Z)`: the
first four identifications of the proof of [Stacks, Tag 0G55],
`Hom(Rg_! Rf_! K, L) = colim_n Hom(Rg_! M_n, L) = colim_n Hom(M_n, g^! L) = Hom(Rf_! K, g^! L)
= Hom(K, f^! g^! L)`. -/
def lowerShriekCompPointsUpperShriekIso (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : CompactificationOf (Over.mk f.left)) (cg : CompactificationOf (Over.mk g.left))
    (K : BoundedCoherentDerived X.left) :
    (lowerShriekComp f g cf cg K).points ≅
      boundedCoherentToPlusCoh Z.left ⋙ upperShriekStdPlusCoh g cg ⋙ upperShriekStd f cf ⋙
        coyoneda.obj (op ((boundedCoherentDerived X.left).ι.obj K)) :=
  lowerShriekCompPointsIso f g cf cg K (ProSeq.ofSeqOfIso _) ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft _ (lowerShriekPointsFunctorIso g cg)) ≪≫
    colimitCompWhiskeringLeftIsoCompColimit
      ((ProSeq.seqOf ((lowerShriek f cf).obj K)).rightOp ⋙
        (boundedCoherentToPlusCoh Y.left).op ⋙ coyoneda)
      (boundedCoherentToPlusCoh Z.left ⋙ upperShriekStdPlusCoh g cg) ≪≫
    Functor.isoWhiskerLeft (boundedCoherentToPlusCoh Z.left ⋙ upperShriekStdPlusCoh g cg)
      ((ProSeq.ofPointsIso (ProSeq.seqOf ((lowerShriek f cf).obj K) ⋙
          boundedCoherentToPlusCoh Y.left)).symm ≪≫
        (IsSequentialProObject _).ι.mapIso
          (ProSeq.mapOfIso (boundedCoherentToPlusCoh Y.left) _).unop ≪≫
        ((IsSequentialProObject _).ι.mapIso ((ProSeq.map (boundedCoherentToPlusCoh Y.left)).mapIso
          (ProSeq.ofSeqOfIso ((lowerShriek f cf).obj K))).unop).symm ≪≫
        ProSeq.pointsIsoHomConst _ ≪≫ (lowerShriekHomIso f cf).app (op K)) ≪≫
    (Functor.associator _ _ _)

/-- **Stacks Project, Tag 0G55.** In Situation [Stacks, Tag 0F42] let `f : X ⟶ Y` and
`g : Y ⟶ Z` be composable morphisms of `FTS_S`. With notation as in [Stacks, Tag 0G54] we have
`Rg_! ∘ Rf_! = R(g ∘ f)_!`: for `K` in `D^b_{Coh}(𝒪_X)` the composition `Rg_! Rf_! K`
(`AlgebraicGeometry.lowerShriekComp`) is isomorphic to `R(g ∘ f)_! K`, for arbitrary
compactifications `cf`, `cg` and `cfg` computing `Rf_!`, `Rg_!` and `R(g ∘ f)_!`.

The proof is the source's: both pro-objects have the functor of points
`L ↦ Hom_X(K, (g ∘ f)^! L)` on `D^b_{Coh}(𝒪_Z)`, by [Stacks, Tag 0G51] for `g`, `f` and `g ∘ f`
and `f^! ∘ g^! = (g ∘ f)^!` ([Stacks, Tag 0ATX]); a pro-object is determined by its functor of
points ([Stacks, Tag 0G2X]). -/
@[stacks 0G55]
def lowerShriekCompIso (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : CompactificationOf (Over.mk f.left)) (cg : CompactificationOf (Over.mk g.left))
    (cfg : CompactificationOf (Over.mk (f ≫ g).left)) (K : BoundedCoherentDerived X.left) :
    lowerShriekComp f g cf cg K ≅ (lowerShriek (f ≫ g) cfg).obj K :=
  (ObjectProperty.isoMk _
    (((ProSeq.pointsFunctorIsoMap (boundedCoherentToPlusCoh Z.left)
          (lowerShriek (f ≫ g) cfg)).app (op K) ≪≫
      Functor.isoWhiskerLeft (boundedCoherentToPlusCoh Z.left)
        (ProSeq.pointsIsoHomConst _ ≪≫ (lowerShriekHomIso (f ≫ g) cfg).app (op K)) ≪≫
      Functor.isoWhiskerLeft (boundedCoherentToPlusCoh Z.left)
        (Functor.isoWhiskerRight (upperShriekStdCompIso f g cf cg cfg).symm _ ≪≫
          Functor.associator _ _ _)) ≪≫
      (lowerShriekCompPointsUpperShriekIso f g cf cg K).symm)).op

end AlgebraicGeometry
