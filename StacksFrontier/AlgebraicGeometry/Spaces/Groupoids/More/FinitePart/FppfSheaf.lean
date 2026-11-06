module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Presheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import StacksFrontier.AlgebraicGeometry.Topologies.Etale
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The finite part is an fppf sheaf, and its sections over an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`. The finite part
`(X/Y)_fin` of `f`, the presheaf of Stacks 04PD whose sections over a scheme `T` are the pairs
`(a, Z)` of Stacks 04PC, satisfies the sheaf condition for the fppf topology, and for an
algebraic space `T` over `S` the morphisms of sheaves `T ⟶ (X/Y)_fin` are in canonical
bijection with the pairs `(a, Z)` over `T` itself.

## Main results

* `AlgebraicGeometry.Space.isSheaf_finiteOpenSubspacePresheaf` — Stacks 04PE, part (1).
* `AlgebraicGeometry.Space.finiteOpenSubspaceEquiv` — Stacks 04PE, part (2).

## Implementation notes

Descent of a compatible family of pairs is descent of its two components. The morphisms to `Y`
descend by Stacks 04P2 for a target satisfying the fpqc sheaf condition, which Gabber's Stacks
0APL supplies for every algebraic space; the open subspaces descend by Stacks 04P1; and the
projection of the descended open subspace is finite because finiteness is fpqc local on the
base, Stacks 0426. An fppf covering family of schemes of the site is an fpqc covering family of
algebraic spaces, which is what lets all three be applied.

Part (2) is proved for an arbitrary presheaf presenting the finite part, as the rest of this
development is, since the proof uses only the data of
`AlgebraicGeometry.Space.FinitePartPresheaf`: a pair over `T` restricts along any morphism from
a scheme, giving a transformation out of `T`, and conversely a transformation out of `T` is
determined by its restriction to a surjective étale chart `U ⟶ T`, where it is a pair whose two
pullbacks to `U ×_T U` agree, hence descends. Both directions use the same base-change relation
between pairs over algebraic spaces, which generalises
`AlgebraicGeometry.Space.FiniteOpenSubspace.IsBaseChange` from schemes of the site to arbitrary
algebraic spaces.

The bijection is returned bundled with its characterisation — the pair attached to a
transformation restricts, along every morphism from a scheme, to the pair that the
transformation names there — because that characterisation is what pins the bijection down.

## References

* [Stacks Project, Tag 04PE](https://stacks.math.columbia.edu/tag/04PE)
* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04PD](https://stacks.math.columbia.edu/tag/04PD)
* [Stacks Project, Tag 04P1](https://stacks.math.columbia.edu/tag/04P1)
* [Stacks Project, Tag 04P2](https://stacks.math.columbia.edu/tag/04P2)
* [Stacks Project, Tag 0426](https://stacks.math.columbia.edu/tag/0426)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Space

private lemma eq_preimage_of_isPullback {C : Type u} [Category.{v} C]
    {F G : C ⥤ Type w} (A : Subfunctor F) (B : Subfunctor G)
    (f : F ⟶ G) (j : A.toFunctor ⟶ B.toFunctor)
    (h : IsPullback j A.ι B.ι f) : A = B.preimage f := by
  ext U x
  have hh := Types.range_snd_of_isPullback (h.app U)
  have hA := congrArg (fun K : Subfunctor F => K.obj U) (Subfunctor.range_ι A)
  have hB := congrArg (fun K : Subfunctor G => K.obj U) (Subfunctor.range_ι B)
  change Set.range (A.ι.app U) = A.obj U at hA
  change Set.range (B.ι.app U) = B.obj U at hB
  rw [hA, hB] at hh
  exact Set.ext_iff.mp hh x

private lemma pullback_map_isPullback {C : Type u} [Category.{v} C]
    [HasPullbacks C] {T T' X Y : C} (a : T ⟶ Y) (b : T' ⟶ Y)
    (f : X ⟶ Y) (g : T' ⟶ T) (m : pullback b f ⟶ pullback a f)
    (hb : b = g ≫ a)
    (hm₁ : m ≫ pullback.fst a f = pullback.fst b f ≫ g)
    (hm₂ : m ≫ pullback.snd a f = pullback.snd b f) :
    IsPullback (pullback.fst b f) m g (pullback.fst a f) := by
  apply IsPullback.of_bot (h₂₁ := pullback.fst a f) (v₂₁ := pullback.snd a f)
      (v₂₂ := a) (h₃₁ := f)
  · simpa only [hm₂, ← hb] using IsPullback.of_hasPullback b f
  · exact hm₁.symm
  · exact IsPullback.of_hasPullback a f

private lemma subfunctor_eq_preimage_of_projection_isPullback
    {C : Type u} [Category.{v} C] {T T' F F' : C ⥤ Type w}
    (p : F ⟶ T) (q : F' ⟶ T') (g : T' ⟶ T) (m : F' ⟶ F)
    (A : Subfunctor F) (B : Subfunctor F')
    (j : B.toFunctor ⟶ A.toFunctor)
    (h : IsPullback (B.ι ≫ q) j g (A.ι ≫ p))
    (hm : IsPullback q m g p) (hj : j ≫ A.ι = B.ι ≫ m) :
    B = A.preimage m :=
  eq_preimage_of_isPullback B A m j (h.flip.of_bot hj hm.flip)

private noncomputable def pullbackBaseMap {C : Type u} [Category.{v} C]
    [HasPullbacks C] {T T' X Y : C} (a : T ⟶ Y) (b : T' ⟶ Y)
    (f : X ⟶ Y) (g : T' ⟶ T) (hb : b = g ≫ a) :
    pullback b f ⟶ pullback a f :=
  pullback.lift (pullback.fst b f ≫ g) (pullback.snd b f)
    (by rw [Category.assoc, ← hb, pullback.condition])

private lemma pullbackBaseMap_fst {C : Type u} [Category.{v} C]
    [HasPullbacks C] {T T' X Y : C} (a : T ⟶ Y) (b : T' ⟶ Y)
    (f : X ⟶ Y) (g : T' ⟶ T) (hb : b = g ≫ a) :
    pullbackBaseMap a b f g hb ≫ pullback.fst a f = pullback.fst b f ≫ g :=
  pullback.lift_fst _ _ _

private lemma pullbackBaseMap_snd {C : Type u} [Category.{v} C]
    [HasPullbacks C] {T T' X Y : C} (a : T ⟶ Y) (b : T' ⟶ Y)
    (f : X ⟶ Y) (g : T' ⟶ T) (hb : b = g ≫ a) :
    pullbackBaseMap a b f g hb ≫ pullback.snd a f = pullback.snd b f :=
  pullback.lift_snd _ _ _

private lemma pullbackBaseMap_isPullback {C : Type u} [Category.{v} C]
    [HasPullbacks C] {T T' X Y : C} (a : T ⟶ Y) (b : T' ⟶ Y)
    (f : X ⟶ Y) (g : T' ⟶ T) (hb : b = g ≫ a) :
    IsPullback (pullback.fst b f) (pullbackBaseMap a b f g hb) g
      (pullback.fst a f) :=
  pullback_map_isPullback a b f g _ hb
    (pullbackBaseMap_fst a b f g hb) (pullbackBaseMap_snd a b f g hb)

private def finitePartSchemeBelowPreservesCospan (B : BigFppfSite.{u}) :
    PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance

attribute [local instance] finitePartSchemeBelowPreservesCospan

private def finitePartBigFppfOverHasPullbacks (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks (BigFppfOver B S hS) := inferInstance

attribute [local instance] finitePartBigFppfOverHasPullbacks

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance finitePartPresheafHasPullbacks (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- Products of presheaves on the big fppf site over `S` indexed by a small type (instance
search times out without this shortcut). -/
local instance finitePartPresheafHasLimitsOfShapeDiscrete (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) finitePartPresheafHasPullback (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

private theorem isFlat_schemeSpaceMap_of_flat
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : Flat ((BigFppfOver.toScheme B S hS).map g)) :
    IsFlat B S hS (schemeSpaceMap g).hom := by
  show HoldsOnEveryEtaleChart B S hS (@Flat) (yoneda.map g)
  rw [holdsOnEveryEtaleChart_iff_representable
    B S hS (@Flat) AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget]
  let eU := yoneda.preimage (yoneda.obj U).reprW.hom
  let eV := yoneda.preimage (yoneda.obj V).reprW.inv
  have heU : IsIso eU := by
    have : IsIso (yoneda.map eU) := by simpa [eU] using (yoneda.obj U).reprW.isIso_hom
    exact Yoneda.fullyFaithful.isIso_of_isIso_map eU
  have heV : IsIso eV := by
    have : IsIso (yoneda.map eV) := by simpa [eV] using (yoneda.obj V).reprW.isIso_inv
    exact Yoneda.fullyFaithful.isIso_of_isIso_map eV
  let T := BigFppfOver.toScheme B S hS
  have : Flat (T.map g) := hg
  have hg' : Flat ((T.map eU ≫ T.map g) ≫ T.map eV) := inferInstance
  have heq : yoneda.preimage ((yoneda.obj U).reprW.hom ≫ yoneda.map g ≫
      (yoneda.obj V).reprW.inv) = eU ≫ g ≫ eV := by
    apply yoneda.map_injective
    simp [eU, eV]
  rw [heq]
  exact hg'

private noncomputable def schemeSpacePullbackIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V W : BigFppfOver B S hS} (f : U ⟶ W) (g : V ⟶ W) :
    schemeSpace (pullback f g) ≅
      AlgebraicSpaces.fiberProduct B S hS (schemeSpaceMap f)
        (schemeSpaceMap g) :=
  letI : HasPullbacks (BigFppfOver B S hS) := inferInstance
  ObjectProperty.isoMk _ (PreservesPullback.iso yoneda f g)

private theorem schemeSpacePullbackIso_hom_fst
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V W : BigFppfOver B S hS} (f : U ⟶ W) (g : V ⟶ W) :
    (schemeSpacePullbackIso B S hS f g).hom ≫
        (ObjectProperty.homMk
          (pullback.fst (schemeSpaceMap f).hom
            (schemeSpaceMap g).hom) :
          AlgebraicSpaces.fiberProduct B S hS (schemeSpaceMap f)
            (schemeSpaceMap g) ⟶ schemeSpace U) =
      schemeSpaceMap (pullback.fst f g) :=
  ObjectProperty.hom_ext _ (PreservesPullback.iso_hom_fst yoneda f g)

private theorem schemeSpacePullbackIso_hom_snd
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V W : BigFppfOver B S hS} (f : U ⟶ W) (g : V ⟶ W) :
    (schemeSpacePullbackIso B S hS f g).hom ≫
        (ObjectProperty.homMk
          (pullback.snd (schemeSpaceMap f).hom
            (schemeSpaceMap g).hom) :
          AlgebraicSpaces.fiberProduct B S hS (schemeSpaceMap f)
            (schemeSpaceMap g) ⟶ schemeSpace V) =
      schemeSpaceMap (pullback.snd f g) :=
  ObjectProperty.hom_ext _ (PreservesPullback.iso_hom_snd yoneda f g)

private theorem finite_of_fpqcLocal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {T U : AlgebraicSpaces B S hS}
    {Tᵢ : I → AlgebraicSpaces B S hS}
    (p : ∀ i, Tᵢ i ⟶ T)
    (hp : IsFpqcCovering B S hS (fun i => (p i).hom))
    (g : U ⟶ T)
    (hg : ∀ i, finiteMorphismProperty B S hS (pullback.snd g (p i))) :
    finiteMorphismProperty B S hS g := by
  let K := Topology.precoverage.{u, v} .fpqc B S hS
  let E : K.ZeroHypercover T := ⟨
    { I₀ := I, X := Tᵢ, f := p },
    ⟨I, Tᵢ, p, rfl, T.property, (fun i => (Tᵢ i).property), hp⟩⟩
  have : (finiteMorphismProperty B S hS).IsLocalAtTarget K :=
    isFinite_isLocalAtTarget_fpqc B S hS
  exact (MorphismProperty.IsLocalAtTarget.iff_of_zeroHypercover
    (P := finiteMorphismProperty B S hS) E).mpr hg

private theorem finiteSections_baseMaps_compatible
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (P : FinitePartPresheaf B S hS f)
    {V : BigFppfOver B S hS} (E : PreZeroHypercover V)
    (x : Presieve.FamilyOfElements P.toFunctor E.presieve₀)
    (hx : x.Compatible) (i j : E.I₀) :
    (ObjectProperty.homMk
      (pullback.fst (schemeSpaceMap (E.f i)).hom
        (schemeSpaceMap (E.f j)).hom) :
      AlgebraicSpaces.fiberProduct B S hS (schemeSpaceMap (E.f i))
        (schemeSpaceMap (E.f j)) ⟶ schemeSpace (E.X i)) ≫
        (P.sections (E.X i) (x (E.f i) (E.presieve₀_f i))).toBase =
    (ObjectProperty.homMk
      (pullback.snd (schemeSpaceMap (E.f i)).hom
        (schemeSpaceMap (E.f j)).hom) :
      AlgebraicSpaces.fiberProduct B S hS (schemeSpaceMap (E.f i))
        (schemeSpaceMap (E.f j)) ⟶ schemeSpace (E.X j)) ≫
        (P.sections (E.X j) (x (E.f j) (E.presieve₀_f j))).toBase := by
  let R := pullback (E.f i) (E.f j)
  let r₁ := pullback.fst (E.f i) (E.f j)
  let r₂ := pullback.snd (E.f i) (E.f j)
  let pᵢ := P.sections (E.X i) (x (E.f i) (E.presieve₀_f i))
  let pⱼ := P.sections (E.X j) (x (E.f j) (E.presieve₀_f j))
  have hxR : P.toFunctor.map r₁.op (x (E.f i) (E.presieve₀_f i)) =
      P.toFunctor.map r₂.op (x (E.f j) (E.presieve₀_f j)) :=
    hx r₁ r₂ (E.presieve₀_f i) (E.presieve₀_f j) pullback.condition
  have h₁ := (P.map_isBaseChange r₁ (x (E.f i) (E.presieve₀_f i))).1
  have h₂ := (P.map_isBaseChange r₂ (x (E.f j) (E.presieve₀_f j))).1
  have hbase : yoneda.map r₁ ≫ pᵢ.toBase.hom = yoneda.map r₂ ≫ pⱼ.toBase.hom := by
    have h := congrArg (fun z => (P.sections R z).toBase.hom) hxR
    rwa [← h₁, ← h₂]
  refine (cancel_epi (schemeSpacePullbackIso B S hS (E.f i) (E.f j)).hom).1 ?_
  rw [← Category.assoc, ← Category.assoc, schemeSpacePullbackIso_hom_fst,
    schemeSpacePullbackIso_hom_snd]
  exact ObjectProperty.hom_ext _ hbase

private noncomputable def finitePartAffineOpenOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj P).Opens)
    (hW : IsAffineOpen W) : BigAffineFppf B S hS := by
  let A : B.Schemes := ⟨W.toScheme,
    Scheme.size_lt_of_isOpenImmersion W.ι P.left.property⟩
  let j : A ⟶ P.left := ⟨W.ι⟩
  let Q : BigFppfOver B S hS := Over.mk (j ≫ P.hom)
  exact ⟨Q, hW⟩

private noncomputable def finitePartAffineOpenOverMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj P).Opens)
    (hW : IsAffineOpen W) :
    (BigAffineFppf.inclusion B S hS).obj
      (finitePartAffineOpenOver B S hS P W hW) ⟶ P := by
  let A : B.Schemes := ⟨W.toScheme,
    Scheme.size_lt_of_isOpenImmersion W.ι P.left.property⟩
  let j : A ⟶ P.left := ⟨W.ι⟩
  change (Over.mk (j ≫ P.hom)) ⟶ P
  exact Over.homMk j

private lemma exists_finite_affine_refinement {X : Scheme.{u}} [CompactSpace X]
    {ι : Type*} {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ X)
    (hf : ∀ i, Flat (f i) ∧ LocallyOfFinitePresentation (f i))
    (hsurj : ∀ x, ∃ i, ∃ y : Y i, f i y = x) :
    ∃ (i : X → ι) (W : ∀ x, (Y (i x)).Opens) (_ : ∀ x, IsAffineOpen (W x)) (s : Finset X),
      Set.univ ⊆ ⋃ x ∈ s, Set.range ((W x).ι ≫ f (i x)) := by
  choose i y hy using hsurj
  choose W hW hmem _ using fun x =>
    exists_isAffineOpen_mem_and_subset (X := Y (i x)) (x := y x) (U := ⊤) (by simp)
  have hOpen (x : X) : IsOpen (Set.range ((W x).ι ≫ f (i x))) := by
    have := (hf (i x)).1
    have := (hf (i x)).2
    simpa using Scheme.Hom.isOpenMap ((W x).ι ≫ f (i x)) Set.univ isOpen_univ
  have hcover (x : X) : x ∈ Set.range ((W x).ι ≫ f (i x)) := by
    refine ⟨⟨y x, hmem x⟩, ?_⟩
    show f (i x) ((W x).ι ⟨y x, hmem x⟩) = x
    rw [Scheme.Opens.ι_apply]
    exact hy x
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x => Set.range ((W x).ι ≫ f (i x))) hOpen
    fun x _ => Set.mem_iUnion.mpr ⟨x, hcover x⟩
  exact ⟨i, W, hW, s, hs⟩

section
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y V : BigFppfOver B S hS} (e : X ⟶ V) (g : Y ⟶ V)

private noncomputable def overPullback : BigFppfOver B S hS :=
  Over.mk ((⟨pullback.snd ((BigFppfOver.toScheme B S hS).map e)
      ((BigFppfOver.toScheme B S hS).map g)⟩ :
    (⟨pullback ((BigFppfOver.toScheme B S hS).map e) ((BigFppfOver.toScheme B S hS).map g),
      Scheme.size_pullback_lt _ _ X.left.property Y.left.property⟩ : B.Schemes) ⟶ Y.left) ≫
    Y.hom)

private noncomputable def overPullbackSnd : overPullback B S hS e g ⟶ Y :=
  Over.homMk ⟨pullback.snd _ _⟩

private noncomputable def overPullbackFst : overPullback B S hS e g ⟶ X := by
  let G := BigFppfOver.toScheme B S hS
  refine Over.homMk (f := ⟨pullback.fst (G.map e) (G.map g)⟩) ?_
  apply B.inclusion.map_injective
  change pullback.fst (G.map e) (G.map g) ≫ B.inclusion.map (Over.hom X) =
    pullback.snd (G.map e) (G.map g) ≫ B.inclusion.map (Over.hom Y)
  rw [← e.w, ← g.w]
  change pullback.fst (G.map e) (G.map g) ≫ G.map e ≫ B.inclusion.map (Over.hom V) =
    pullback.snd (G.map e) (G.map g) ≫ G.map g ≫ B.inclusion.map (Over.hom V)
  rw [← Category.assoc, pullback.condition]
  rfl

private lemma overPullback_condition :
    overPullbackFst B S hS e g ≫ e = overPullbackSnd B S hS e g ≫ g :=
  Over.OverMorphism.ext (B.inclusion.map_injective pullback.condition)

end

private lemma exists_finite_affine_cover_of_fppf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (A : BigAffineFppf B S hS) {ι : Type*} {P : ι → BigFppfOver B S hS}
    (p : ∀ k, P k ⟶ (BigAffineFppf.inclusion B S hS).obj A)
    (hp : ∀ k, Flat ((BigFppfOver.toScheme B S hS).map (p k)) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (p k)))
    (hsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj A),
      ∃ k, ∃ y : (BigFppfOver.toScheme B S hS).obj (P k),
        (BigFppfOver.toScheme B S hS).map (p k) y = x) :
    ∃ U : PreZeroHypercover.{u + 1} A, Finite U.I₀ ∧
      Presieve.map (BigAffineFppf.toScheme B S hS) U.presieve₀ ∈
        Scheme.fpqcPrecoverage ((BigAffineFppf.toScheme B S hS).obj A) ∧
      ∀ j, ∃ k, ∃ m : (BigAffineFppf.inclusion B S hS).obj (U.X j) ⟶ P k,
        (BigAffineFppf.inclusion B S hS).map (U.f j) = m ≫ p k := by
  classical
  let G := BigFppfOver.toScheme B S hS
  let : IsAffine (G.obj ((BigAffineFppf.inclusion B S hS).obj A)) := A.property
  obtain ⟨i, W, hW, s, hs⟩ := exists_finite_affine_refinement (fun k => G.map (p k)) hp hsurj
  let J₀ := {x // x ∈ s}
  let U : PreZeroHypercover.{u + 1} A := {
    I₀ := ULift.{u + 1} J₀
    X := fun x => finitePartAffineOpenOver B S hS (P (i x.down.1)) (W x.down.1) (hW x.down.1)
    f := fun x => ObjectProperty.homMk
      (finitePartAffineOpenOverMap B S hS (P (i x.down.1)) (W x.down.1) (hW x.down.1) ≫
        p (i x.down.1)) }
  let : Fintype J₀ := Fintype.ofFinset s fun _ => Iff.rfl
  refine ⟨U, Finite.of_fintype (ULift.{u + 1} J₀), ?_, fun x => ⟨i x.down.1, _, rfl⟩⟩
  apply Scheme.fppfPrecoverage_le_fpqcPrecoverage
  rw [PreZeroHypercover.presieve₀, Presieve.map_ofArrows,
    Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨fun z => ?_, fun x => ?_⟩
  · obtain ⟨x, hxS, y, hy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ z))
    exact ⟨ULift.up ⟨x, hxS⟩, y, hy⟩
  · have := (hp (i x.down.1)).1
    have := (hp (i x.down.1)).2
    show Flat ((W x.down.1).ι ≫ G.map (p (i x.down.1))) ∧
      LocallyOfFinitePresentation ((W x.down.1).ι ≫ G.map (p (i x.down.1)))
    exact ⟨inferInstance, inferInstance⟩

private theorem isFpqcCovering_of_schemeFppfPresieve
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V : BigFppfOver B S hS}
    (E : PreZeroHypercover V)
    (hf : (E.map (BigFppfOver.toScheme B S hS)).presieve₀ ∈
        Scheme.fppfPrecoverage
          ((BigFppfOver.toScheme B S hS).obj V)) :
    IsFpqcCovering B S hS
      (fun i => (schemeSpaceMap (E.f i)).hom) := by
  let G := BigFppfOver.toScheme B S hS
  refine ⟨fun i => ?_, fun A h => ?_⟩
  · obtain ⟨_, hprop⟩ := (Scheme.presieve₀_mem_precoverage_iff (E.map G)).mp hf
    exact isFlat_schemeSpaceMap_of_flat B S hS (E.f i) (hprop i |>.1)
  change yoneda.obj ((BigAffineFppf.inclusion B S hS).obj A) ⟶ yoneda.obj V at h
  obtain ⟨g, rfl⟩ : ∃ g, yoneda.map g = h :=
    ⟨yonedaEquiv h, yonedaEquiv.injective (yonedaEquiv_yoneda_map _)⟩
  let E₀ : Scheme.fppfPrecoverage.ZeroHypercover (G.obj V) := ⟨E.map G, hf⟩
  let F := E₀.pullback₂ (G.map g)
  let K := F.toPreZeroHypercover
  have hK := (Scheme.presieve₀_mem_precoverage_iff K).mp F.mem₀
  have hpoints (x : G.obj ((BigAffineFppf.inclusion B S hS).obj A)) :
      ∃ i : K.I₀, ∃ y : K.X i, K.f i y = x := by
    simpa only [Set.mem_iUnion, Set.mem_range] using hK.1 x
  obtain ⟨U, hU, hcov, hfac⟩ := exists_finite_affine_cover_of_fppf B S hS A
    (fun k : E.I₀ => overPullbackSnd B S hS (E.f k) g) hK.2 hpoints
  refine ⟨U, hU, hcov, fun j => ?_⟩
  obtain ⟨k, m, hm⟩ := hfac j
  refine ⟨k, yoneda.map (m ≫ overPullbackFst B S hS (E.f k) g), ?_⟩
  show yoneda.map (m ≫ _) ≫ yoneda.map (E.f k) = yoneda.map _ ≫ yoneda.map g
  rw [hm, ← Functor.map_comp, ← Functor.map_comp, Category.assoc, Category.assoc,
    overPullback_condition]

section
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

private abbrev PairBaseChange {T U : AlgebraicSpaces B S hS}
    (g : U ⟶ T) (p : FiniteOpenSubspace B S hS f T)
    (q : FiniteOpenSubspace B S hS f U) : Prop :=
  q.toBase.hom = g.hom ≫ p.toBase.hom ∧
    ∃ j : q.subspace.toFunctor ⟶ p.subspace.toFunctor,
      IsPullback (q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom) j g.hom
        (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom) ∧
      j ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom =
        q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom

private lemma pairBaseChange_subspace {T U : AlgebraicSpaces B S hS}
    {g : U ⟶ T} {p : FiniteOpenSubspace B S hS f T}
    {q : FiniteOpenSubspace B S hS f U}
    (h : PairBaseChange B S hS f g p q) :
    q.subspace = p.subspace.preimage
      (pullbackBaseMap p.toBase.hom q.toBase.hom f.hom g.hom h.1) := by
  obtain ⟨hb, j, hj, hX⟩ := h
  apply subfunctor_eq_preimage_of_projection_isPullback
    (pullback.fst p.toBase.hom f.hom) (pullback.fst q.toBase.hom f.hom)
    g.hom _ p.subspace q.subspace j hj
    (pullbackBaseMap_isPullback _ _ _ _ hb)
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullbackBaseMap_fst] using hj.w.symm
  · simpa only [Category.assoc, pullbackBaseMap_snd] using hX

private lemma pairBaseChange_unique {T U : AlgebraicSpaces B S hS}
    {g : U ⟶ T} {p : FiniteOpenSubspace B S hS f T}
    {q r : FiniteOpenSubspace B S hS f U}
    (hq : PairBaseChange B S hS f g p q)
    (hr : PairBaseChange B S hS f g p r) : q = r := by
  have hb : q.toBase = r.toBase := ObjectProperty.hom_ext _ (hq.1.trans hr.1.symm)
  obtain ⟨aq, Zq, oq, fq⟩ := q
  obtain ⟨ar, Zr, or, fr⟩ := r
  dsimp only at hb
  subst ar
  have hz := (pairBaseChange_subspace B S hS f hq).trans
    (pairBaseChange_subspace B S hS f hr).symm
  dsimp at hz
  subst Zr
  rfl

private lemma finite_of_isPullback
    {A A' T T' : AlgebraicSpaces B S hS}
    {i : A' ⟶ A} {q : A' ⟶ T'} {p : A ⟶ T} {g : T' ⟶ T}
    (h : IsPullback i.hom q.hom p.hom g.hom)
    (hp : IsFinite B S hS p.hom) :
    IsFinite B S hS q.hom :=
  isFinite_of_isPullback B S hS h hp

private lemma exists_pairBaseChange {T U : AlgebraicSpaces B S hS}
    (g : U ⟶ T) (p : FiniteOpenSubspace B S hS f T) :
    ∃ q, PairBaseChange B S hS f g p q := by
  let a := g ≫ p.toBase
  let m := pullbackBaseMap p.toBase.hom a.hom f.hom g.hom rfl
  let Z := p.subspace.preimage m
  have hZ : IsOpenSubspace B S hS Z :=
    isOpenSubspace_preimage B S hS m p.subspace
      (AlgebraicSpaces.fiberProduct B S hS p.toBase f).property
      (AlgebraicSpaces.fiberProduct B S hS a f).property p.isOpen
  have hm := pullbackBaseMap_isPullback p.toBase.hom a.hom f.hom g.hom rfl
  have hj := ((CategoryTheory.Subfunctor.isPullback_preimage m p.subspace).paste_vert hm.flip).flip
  have hfin : IsFinite B S hS
      (Z.ι ≫ pullback.fst a.hom f.hom) :=
    finite_of_isPullback B S hS
      (A := ⟨p.subspace.toFunctor, p.isOpen.1⟩) (A' := ⟨Z.toFunctor, hZ.1⟩)
      (T := T) (T' := U) (i := ObjectProperty.homMk (p.subspace.fromPreimage m))
      (q := ObjectProperty.homMk _) (p := ObjectProperty.homMk _)
      (g := g) hj.flip p.finite_projection
  refine ⟨⟨a, Z, hZ, hfin⟩, rfl, p.subspace.fromPreimage m, hj, ?_⟩
  simp only [Subfunctor.fromPreimage_ι_assoc, m, pullbackBaseMap_snd]
  rfl

private lemma pairBaseChange_comp {T U V : AlgebraicSpaces B S hS}
    {g : U ⟶ T} {h : V ⟶ U}
    {p : FiniteOpenSubspace B S hS f T}
    {q : FiniteOpenSubspace B S hS f U}
    {r : FiniteOpenSubspace B S hS f V}
    (hq : PairBaseChange B S hS f g p q) (hr : PairBaseChange B S hS f h q r) :
    PairBaseChange B S hS f (h ≫ g) p r := by
  obtain ⟨hbq, j, hj, hXj⟩ := hq
  obtain ⟨hbr, k, hk, hXk⟩ := hr
  refine ⟨by simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc, hbr, hbq],
    k ≫ j, hk.paste_vert hj, ?_⟩
  simpa only [Category.assoc, hXj] using hXk

private lemma pairBaseChange_overlap
    {T U V R : AlgebraicSpaces B S hS}
    (i : U ⟶ T) (j : V ⟶ T) (r : R ⟶ U) (s : R ⟶ V)
    (hrs : IsPullback r.hom s.hom i.hom j.hom)
    (a : T ⟶ Y)
    (p : FiniteOpenSubspace B S hS f U)
    (q : FiniteOpenSubspace B S hS f V)
    (z : FiniteOpenSubspace B S hS f R)
    (hp : p.toBase.hom = i.hom ≫ a.hom)
    (hq : q.toBase.hom = j.hom ≫ a.hom)
    (hzp : PairBaseChange B S hS f r p z)
    (hzq : PairBaseChange B S hS f s q z) :
    let mi := pullbackBaseMap a.hom p.toBase.hom f.hom i.hom hp
    let mj := pullbackBaseMap a.hom q.toBase.hom f.hom j.hom hq
    p.subspace.preimage (pullback.fst mi mj) =
      q.subspace.preimage (pullback.snd mi mj) := by
  dsimp only
  let mi := pullbackBaseMap a.hom p.toBase.hom f.hom i.hom hp
  let mj := pullbackBaseMap a.hom q.toBase.hom f.hom j.hom hq
  let l := pullback.fst mi mj
  let n := pullback.snd mi mj
  have hT : (l ≫ pullback.fst p.toBase.hom f.hom) ≫ i.hom =
      (n ≫ pullback.fst q.toBase.hom f.hom) ≫ j.hom := by
    have h := congrArg (fun k => k ≫ pullback.fst a.hom f.hom)
      (pullback.condition (f := mi) (g := mj))
    simpa only [Category.assoc, mi, mj, pullbackBaseMap_fst] using h
  let k := hrs.lift (l ≫ pullback.fst p.toBase.hom f.hom)
    (n ≫ pullback.fst q.toBase.hom f.hom) hT
  have hk₁ : k ≫ r.hom = l ≫ pullback.fst p.toBase.hom f.hom := hrs.lift_fst _ _ _
  have hk₂ : k ≫ s.hom = n ≫ pullback.fst q.toBase.hom f.hom := hrs.lift_snd _ _ _
  have hX : l ≫ pullback.snd p.toBase.hom f.hom =
      n ≫ pullback.snd q.toBase.hom f.hom := by
    have h := congrArg (fun k => k ≫ pullback.snd a.hom f.hom)
      (pullback.condition (f := mi) (g := mj))
    simpa only [Category.assoc, mi, mj, pullbackBaseMap_snd] using h
  let t : pullback mi mj ⟶ pullback z.toBase.hom f.hom :=
    pullback.lift k (l ≫ pullback.snd p.toBase.hom f.hom) (by
      rw [hzp.1, ← Category.assoc, hk₁, Category.assoc, pullback.condition]
      simp only [Category.assoc])
  have ht₁ : t ≫ pullbackBaseMap p.toBase.hom z.toBase.hom f.hom r.hom hzp.1 = l := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackBaseMap_fst]
      rw [← Category.assoc, show t ≫ pullback.fst _ _ = k from pullback.lift_fst _ _ _, hk₁]
    · simp only [Category.assoc, pullbackBaseMap_snd]
      exact pullback.lift_snd _ _ _
  have ht₂ : t ≫ pullbackBaseMap q.toBase.hom z.toBase.hom f.hom s.hom hzq.1 = n := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackBaseMap_fst]
      rw [← Category.assoc, show t ≫ pullback.fst _ _ = k from pullback.lift_fst _ _ _, hk₂]
    · simp only [Category.assoc, pullbackBaseMap_snd]
      exact (pullback.lift_snd _ _ _).trans hX
  have h₁ := congrArg (fun Z => Subfunctor.preimage Z t)
    (pairBaseChange_subspace B S hS f hzp)
  have h₂ := congrArg (fun Z => Subfunctor.preimage Z t)
    (pairBaseChange_subspace B S hS f hzq)
  rw [← Subfunctor.preimage_comp, ht₁] at h₁
  rw [← Subfunctor.preimage_comp, ht₂] at h₂
  exact h₁.symm.trans h₂

private lemma isPullback_algebraicSpaces
    {P U V T : AlgebraicSpaces B S hS}
    {p : P ⟶ U} {q : P ⟶ V} {f : U ⟶ T} {g : V ⟶ T}
    (h : IsPullback p.hom q.hom f.hom g.hom) : IsPullback p q f g :=
  IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ h.w) h

private lemma fpqcCover_of_isPullback
    {I : Type v} {T U : AlgebraicSpaces B S hS}
    {Ti Ui : I → AlgebraicSpaces B S hS}
    (p : ∀ i, Ti i ⟶ T) (q : ∀ i, Ui i ⟶ U)
    (r : ∀ i, Ui i ⟶ Ti i) (g : U ⟶ T)
    (hp : IsFpqcCovering B S hS (fun i => (p i).hom))
    (h : ∀ i, IsPullback (r i).hom (q i).hom (p i).hom g.hom) :
    IsFpqcCovering B S hS (fun i => (q i).hom) := by
  refine ⟨fun i => ?_, fun A a => ?_⟩
  · let P : MorphismProperty (AlgebraicSpaces B S hS) :=
      fun _ _ k => IsFlat B S hS k.hom
    have : P.IsStableUnderBaseChange := isFlat_isStableUnderBaseChange B S hS
    exact P.of_isPullback (isPullback_algebraicSpaces B S hS (h i)) (hp.1 i)
  · obtain ⟨E, hfin, hE, hfac⟩ := hp.2 A (a ≫ g.hom)
    refine ⟨E, hfin, hE, fun k => ?_⟩
    obtain ⟨i, b, hb⟩ := hfac k
    let c := yoneda.map ((BigAffineFppf.inclusion B S hS).map (E.f k)) ≫ a
    have hc : b ≫ (p i).hom = c ≫ g.hom := by simpa [c, Category.assoc] using hb
    exact ⟨i, (h i).lift b c hc, (h i).lift_snd b c hc⟩

private lemma finite_of_isPullback_cover
    {I : Type v} {T Z : AlgebraicSpaces B S hS}
    {Ti Zi : I → AlgebraicSpaces B S hS}
    (p : ∀ i, Ti i ⟶ T) (q : ∀ i, Zi i ⟶ Ti i)
    (j : ∀ i, Zi i ⟶ Z) (g : Z ⟶ T)
    (hp : IsFpqcCovering B S hS (fun i => (p i).hom))
    (hq : ∀ i, IsFinite B S hS (q i).hom)
    (h : ∀ i, IsPullback (j i).hom (q i).hom g.hom (p i).hom) :
    IsFinite B S hS g.hom := by
  refine finite_of_fpqcLocal B S hS p hp g fun i => ?_
  let H := isPullback_algebraicSpaces B S hS (h i)
  have : (finiteMorphismProperty B S hS).RespectsIso :=
    MorphismProperty.IsLocalAtTarget.toRespects
      (Topology.fpqc.precoverage.{u, v} B S hS)
  apply (MorphismProperty.cancel_left_of_respectsIso
    (P := finiteMorphismProperty B S hS) H.isoPullback.hom _).mp
  simpa only [IsPullback.isoPullback_hom_snd] using hq i

private lemma exists_isPullback_of_eq_preimage
    {C : Type*} [Category C] {F G : C ⥤ Type u}
    (m : F ⟶ G) (A : Subfunctor F) (Z : Subfunctor G)
    (h : A = Z.preimage m) :
    ∃ j : A.toFunctor ⟶ Z.toFunctor, IsPullback j A.ι Z.ι m := by
  subst A
  exact ⟨Z.fromPreimage m, CategoryTheory.Subfunctor.isPullback_preimage m Z⟩

private lemma exists_pair_of_compatible_opens
    {I : Type v} {T : AlgebraicSpaces B S hS}
    {Ti : I → AlgebraicSpaces B S hS}
    (p : ∀ i, Ti i ⟶ T)
    (hp : IsFpqcCovering B S hS (fun i => (p i).hom))
    (a : T ⟶ Y) (z : ∀ i, FiniteOpenSubspace B S hS f (Ti i))
    (ha : ∀ i, (z i).toBase.hom = (p i).hom ≫ a.hom)
    (hZ : ∀ i j,
      let mi := pullbackBaseMap a.hom (z i).toBase.hom f.hom (p i).hom (ha i)
      let mj := pullbackBaseMap a.hom (z j).toBase.hom f.hom (p j).hom (ha j)
      (z i).subspace.preimage (pullback.fst mi mj) =
        (z j).subspace.preimage (pullback.snd mi mj)) :
    ∃ q : FiniteOpenSubspace B S hS f T,
      q.toBase = a ∧ ∀ i, PairBaseChange B S hS f (p i) q (z i) := by
  classical
  let mi i := pullbackBaseMap a.hom (z i).toBase.hom f.hom (p i).hom (ha i)
  let F := AlgebraicSpaces.fiberProduct B S hS a f
  let Fi i := AlgebraicSpaces.fiberProduct B S hS (z i).toBase f
  let g : F ⟶ T := ObjectProperty.homMk (pullback.fst a.hom f.hom)
  let gi (i : I) : Fi i ⟶ Ti i :=
    ObjectProperty.homMk (pullback.fst (z i).toBase.hom f.hom)
  let m (i : I) : Fi i ⟶ F := ObjectProperty.homMk (mi i)
  have hm i : IsPullback (gi i).hom (m i).hom (p i).hom g.hom :=
    pullbackBaseMap_isPullback _ _ _ _ (ha i)
  have hmcover := fpqcCover_of_isPullback B S hS p m gi g hp hm
  obtain ⟨⟨W, hW⟩, hWi, _⟩ := existsUnique_openSubspace_of_fpqcCovering
    B S hS m hmcover (fun i => ⟨(z i).subspace, (z i).isOpen⟩) hZ
  choose ji hji using fun i => exists_isPullback_of_eq_preimage
    (mi i) (z i).subspace W (hWi i).symm
  have hsquare i := (hji i).paste_vert (hm i).flip
  let Z : AlgebraicSpaces B S hS := ⟨W.toFunctor, hW.1⟩
  let Zi i : AlgebraicSpaces B S hS :=
    ⟨(z i).subspace.toFunctor, (z i).isOpen.1⟩
  let q : Z ⟶ T := ObjectProperty.homMk (W.ι ≫ g.hom)
  let qi (i : I) : Zi i ⟶ Ti i := ObjectProperty.homMk ((z i).subspace.ι ≫ (gi i).hom)
  have hfin := finite_of_isPullback_cover B S hS p qi
    (fun i => (ObjectProperty.homMk (ji i) : Zi i ⟶ Z)) q hp
    (fun i => (z i).finite_projection) hsquare
  refine ⟨⟨a, W, hW, hfin⟩, rfl, fun i => ⟨ha i, ji i, (hsquare i).flip, ?_⟩⟩
  have h := congrArg (fun k => k ≫ pullback.snd a.hom f.hom) (hji i).w
  simpa only [Category.assoc, mi, pullbackBaseMap_snd] using h

private lemma openSubspace_ext_of_cover
    {I : Type v} {T : AlgebraicSpaces B S hS}
    {Ti : I → AlgebraicSpaces B S hS}
    (p : ∀ i, Ti i ⟶ T)
    (hp : IsFpqcCovering B S hS (fun i => (p i).hom))
    (W Z : Subfunctor T.obj)
    (hW : IsOpenSubspace B S hS W)
    (hZ : IsOpenSubspace B S hS Z)
    (h : ∀ i, W.preimage (p i).hom = Z.preimage (p i).hom) : W = Z := by
  let Wi i : {W : Subfunctor (Ti i).obj // IsOpenSubspace B S hS W} :=
    ⟨W.preimage (p i).hom,
      isOpenSubspace_preimage B S hS (p i).hom W T.property (Ti i).property hW⟩
  have hWi i j : (Wi i).1.preimage (pullback.fst (p i).hom (p j).hom) =
      (Wi j).1.preimage (pullback.snd (p i).hom (p j).hom) := by
    dsimp only [Wi]
    rw [← Subfunctor.preimage_comp, ← Subfunctor.preimage_comp, pullback.condition]
  obtain ⟨A, _, hA⟩ := existsUnique_openSubspace_of_fpqcCovering
    B S hS p hp Wi hWi
  exact congrArg Subtype.val ((hA ⟨W, hW⟩ (fun _ => rfl)).trans
    (hA ⟨Z, hZ⟩ (fun i => (h i).symm)).symm)

private lemma pairBaseChange_cover_ext
    {I : Type v} {T : AlgebraicSpaces B S hS}
    {Ti : I → AlgebraicSpaces B S hS}
    (g : ∀ i, Ti i ⟶ T)
    (hg : IsFpqcCovering B S hS (fun i => (g i).hom))
    {p q : FiniteOpenSubspace B S hS f T}
    (z : ∀ i, FiniteOpenSubspace B S hS f (Ti i))
    (hp : ∀ i, PairBaseChange B S hS f (g i) p (z i))
    (hq : ∀ i, PairBaseChange B S hS f (g i) q (z i)) : p = q := by
  have hbase i : g i ≫ p.toBase = g i ≫ q.toBase :=
    ObjectProperty.hom_ext _ ((hp i).1.symm.trans (hq i).1)
  obtain ⟨a, ha, hu⟩ := existsUnique_desc_of_fpqcCovering_of_target_isSheaf_fpqc B S hS g hg Y
    Y.property.isSheaf_fpqc (fun i => g i ≫ p.toBase) (by
      intro i j
      apply ObjectProperty.hom_ext
      show pullback.fst (g i).hom (g j).hom ≫ (g i).hom ≫ p.toBase.hom =
        pullback.snd (g i).hom (g j).hom ≫ (g j).hom ≫ p.toBase.hom
      rw [← Category.assoc, pullback.condition, Category.assoc])
  have hb : p.toBase = q.toBase :=
    (hu p.toBase (fun _ => rfl)).trans (hu q.toBase (fun i => (hbase i).symm)).symm
  obtain ⟨ap, W, hW, fW⟩ := p
  obtain ⟨aq, Z, hZ, fZ⟩ := q
  dsimp only at hb
  subst aq
  have hai i : (z i).toBase.hom = (g i).hom ≫ ap.hom := (hp i).1
  let F := AlgebraicSpaces.fiberProduct B S hS ap f
  let Fi i := AlgebraicSpaces.fiberProduct B S hS (z i).toBase f
  let m (i : I) : Fi i ⟶ F := ObjectProperty.homMk
    (pullbackBaseMap ap.hom (z i).toBase.hom f.hom (g i).hom (hai i))
  have hm := fpqcCover_of_isPullback B S hS g m
    (fun i => (ObjectProperty.homMk (pullback.fst (z i).toBase.hom f.hom) : Fi i ⟶ Ti i))
    (ObjectProperty.homMk (pullback.fst ap.hom f.hom) : F ⟶ T) hg
    (fun i => pullbackBaseMap_isPullback _ _ _ _ (hai i))
  have hWZ : W = Z := openSubspace_ext_of_cover B S hS m hm W Z hW hZ (fun i =>
    (pairBaseChange_subspace B S hS f (hp i)).symm.trans
      (pairBaseChange_subspace B S hS f (hq i)))
  subst Z
  rfl

private lemma pairBaseChange_of_map_eq (P : FinitePartPresheaf B S hS f)
    {V W : BigFppfOver B S hS} (g : W ⟶ V) {t : P.toFunctor.obj (op V)}
    {t' : P.toFunctor.obj (op W)} (h : P.toFunctor.map g.op t = t') :
    PairBaseChange B S hS f (schemeSpaceMap g) (P.sections V t) (P.sections W t') := by
  subst h
  exact P.map_isBaseChange g t

private lemma exists_amalgamation_of_fppfFamily
    (P : FinitePartPresheaf B S hS f)
    {V : BigFppfOver B S hS} (E : PreZeroHypercover V)
    (hE : IsFpqcCovering B S hS
      (fun i => (schemeSpaceMap (E.f i)).hom))
    (x : Presieve.FamilyOfElements P.toFunctor E.presieve₀)
    (hx : x.Compatible) :
    ∃ t : P.toFunctor.obj (op V),
      ∀ i, P.toFunctor.map (E.f i).op t = x (E.f i) (E.presieve₀_f i) := by
  let z i := P.sections (E.X i) (x (E.f i) (E.presieve₀_f i))
  obtain ⟨a, ha, _⟩ := existsUnique_desc_of_fpqcCovering_of_target_isSheaf_fpqc B S hS
    (fun i => schemeSpaceMap (E.f i)) hE Y
    Y.property.isSheaf_fpqc (fun i => (z i).toBase)
    (finiteSections_baseMaps_compatible B S hS f P E x hx)
  have ha' i : (z i).toBase.hom = (schemeSpaceMap (E.f i)).hom ≫ a.hom :=
    (congrArg (fun k => k.hom) (ha i)).symm
  have hZ i j := by
    let r := pullback.fst (E.f i) (E.f j)
    let s := pullback.snd (E.f i) (E.f j)
    let zR := P.sections (pullback (E.f i) (E.f j))
      (P.toFunctor.map r.op (x (E.f i) (E.presieve₀_f i)))
    have hzj : PairBaseChange B S hS f (schemeSpaceMap s) (z j) zR :=
      pairBaseChange_of_map_eq B S hS f _ s
        (hx r s (E.presieve₀_f i) (E.presieve₀_f j) pullback.condition).symm
    exact pairBaseChange_overlap B S hS f
      (schemeSpaceMap (E.f i)) (schemeSpaceMap (E.f j))
      (schemeSpaceMap r) (schemeSpaceMap s)
      ((IsPullback.of_hasPullback (E.f i) (E.f j)).map yoneda)
      a (z i) (z j) zR (ha' i) (ha' j)
      (P.map_isBaseChange r (x (E.f i) (E.presieve₀_f i))) hzj
  obtain ⟨q, _, hq⟩ := exists_pair_of_compatible_opens B S hS f
    (fun i => schemeSpaceMap (E.f i)) hE a z ha' hZ
  refine ⟨(P.sections V).symm q, fun i => ?_⟩
  apply (P.sections (E.X i)).injective
  have h := P.map_isBaseChange (E.f i) ((P.sections V).symm q)
  rw [Equiv.apply_symm_apply] at h
  exact pairBaseChange_unique B S hS f h (hq i)

private lemma isSheafFor_fppfFamily
    (P : FinitePartPresheaf B S hS f)
    {V : BigFppfOver B S hS} (E : PreZeroHypercover V)
    (hE : IsFpqcCovering B S hS
      (fun i => (schemeSpaceMap (E.f i)).hom)) :
    Presieve.IsSheafFor P.toFunctor E.presieve₀ := by
  intro x hx
  obtain ⟨t, ht⟩ := exists_amalgamation_of_fppfFamily B S hS f P E hE x hx
  refine ⟨t, fun _ _ ⟨i⟩ => ht i, fun t' ht' => ?_⟩
  apply (P.sections V).injective
  apply pairBaseChange_cover_ext B S hS f
    (fun i => schemeSpaceMap (E.f i)) hE
    (fun i => P.sections (E.X i) (x (E.f i) (E.presieve₀_f i)))
  · exact fun i => pairBaseChange_of_map_eq B S hS f P (E.f i) (ht' (E.f i) (E.presieve₀_f i))
  · exact fun i => pairBaseChange_of_map_eq B S hS f P (E.f i) (ht i)

end

/-- **Stacks 04PE, part (1).** For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the finite part `(X/Y)_fin` of `f` satisfies the sheaf condition for the fppf topology of
the big fppf site of `S`. -/
@[stacks 04PE "part (1)"]
public theorem isSheaf_finiteOpenSubspacePresheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (finiteOpenSubspacePresheaf B S hS f).toFunctor := by
  let G := BigFppfOver.toScheme B S hS
  let K := Scheme.fppfPrecoverage.comap G
  have hsheaf : Presheaf.IsSheaf K.toGrothendieck
      (finiteOpenSubspacePresheaf B S hS f).toFunctor := by
    rw [isSheaf_iff_isSheaf_of_type,
      Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small]
    intro V E
    apply isSheafFor_fppfFamily B S hS f _ E.toPreZeroHypercover
    apply isFpqcCovering_of_schemeFppfPresieve B S hS
    simpa only [K, G, Precoverage.comap, Set.mem_ofPred_eq,
      PreZeroHypercover.presieve₀_map] using E.mem₀
  apply hsheaf.of_le
  let L := Scheme.fppfPrecoverage.comap B.inclusion
  have hBL : B.precoverage ≤ L := by
    rintro V R ⟨E, rfl, hE⟩
    exact B.isFppfCovering_of_isCovering hE
  have ho : B.topology.over (B.obj hS) ≤ L.toGrothendieck.over (B.obj hS) :=
    fun _ _ hR => Precoverage.toGrothendieck_mono hBL _ hR
  rw [over_toGrothendieck_eq_toGrothendieck_comap_forget L] at ho
  simpa only [K, G, L, BigFppfOver.toScheme,
    BigFppfOver.forget, Precoverage.comap_comp] using ho

section
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

private noncomputable def finitePairToNatTrans
    (P : FinitePartPresheaf B S hS f)
    {T : AlgebraicSpaces B S hS}
    (p : FiniteOpenSubspace B S hS f T) : T.obj ⟶ P.toFunctor where
  app U := ↾fun x => (P.sections U.unop).symm
    (exists_pairBaseChange B S hS f
      (ObjectProperty.homMk (yonedaEquiv.symm x) : schemeSpace U.unop ⟶ T) p).choose
  naturality := by
    intro U V h
    ext x
    apply (P.sections V.unop).injective
    dsimp
    rw [Equiv.apply_symm_apply]
    apply pairBaseChange_unique B S hS f (p := p)
      (g := (ObjectProperty.homMk (yonedaEquiv.symm (T.obj.map h x)) :
        schemeSpace V.unop ⟶ T))
    · exact (exists_pairBaseChange B S hS f
        (ObjectProperty.homMk (yonedaEquiv.symm (T.obj.map h x)) :
          schemeSpace V.unop ⟶ T) p).choose_spec
    · have hp := (exists_pairBaseChange B S hS f
        (ObjectProperty.homMk (yonedaEquiv.symm x) :
          schemeSpace U.unop ⟶ T) p).choose_spec
      have hq := P.map_isBaseChange h.unop
        ((P.sections U.unop).symm
          (exists_pairBaseChange B S hS f
            (ObjectProperty.homMk (yonedaEquiv.symm x) :
              schemeSpace U.unop ⟶ T) p).choose)
      rw [Equiv.apply_symm_apply] at hq
      have hc := pairBaseChange_comp B S hS f hp hq
      convert hc using 1
      · apply ObjectProperty.hom_ext
        apply yonedaEquiv.injective
        change yonedaEquiv (yonedaEquiv.symm (T.obj.map h x)) =
          yonedaEquiv (yoneda.map h.unop ≫ yonedaEquiv.symm x)
        rw [← yonedaEquiv_naturality]
        simp only [Equiv.apply_symm_apply, Quiver.Hom.op_unop]
      · simp only [Quiver.Hom.op_unop]

private lemma finitePairToNatTrans_spec
    (P : FinitePartPresheaf B S hS f)
    {T : AlgebraicSpaces B S hS}
    (p : FiniteOpenSubspace B S hS f T)
    (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ T.obj) :
    PairBaseChange B S hS f (ObjectProperty.homMk g) p
      (P.sections U ((finitePairToNatTrans B S hS f P p).app (op U) (yonedaEquiv g))) := by
  show PairBaseChange B S hS f (ObjectProperty.homMk g) p
    (P.sections U ((P.sections U).symm
      (exists_pairBaseChange B S hS f
        (ObjectProperty.homMk (yonedaEquiv.symm (yonedaEquiv g)) :
          schemeSpace U ⟶ T) p).choose))
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  exact (exists_pairBaseChange B S hS f
    (ObjectProperty.homMk g : schemeSpace U ⟶ T) p).choose_spec

private lemma atlas_isFpqcCovering
    {T : AlgebraicSpaces B S hS}
    {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ T.obj)
    (hsurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    IsFpqcCovering B S hS (fun (_ : Unit) => a) := by
  apply isFpqcCovering_of_isEtaleCovering B S hS (fun _ => yoneda.obj U)
  refine ⟨T.property, fun _ => isAlgebraicSpace_yoneda B S hS U, ?_, ?_⟩
  · intro i V g hg
    let Q := MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
    have : Q.IsStableUnderComposition := by
      refine ⟨fun j k hj hk => ?_⟩
      show Etale ((BigFppfOver.toScheme B S hS).map (j ≫ k))
      rw [Functor.map_comp]
      have : Etale ((BigFppfOver.toScheme B S hS).map j) := hj
      have : Etale ((BigFppfOver.toScheme B S hS).map k) := hk
      exact Etale.etale_comp _ _
    have : Q.presheaf.IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition Q
    exact Q.presheaf.comp_mem g a hg hetale
  · have h := (presheafSurjective_iff_isSurjective B S hS
        (isAlgebraicSpace_yoneda B S hS U) T.property a hsurj.rep).mp hsurj
    simp only [Set.range_eq_univ.mpr h, Set.iUnion_const]

private lemma finitePairToNatTrans_injective
    (P : FinitePartPresheaf B S hS f)
    (T : AlgebraicSpaces B S hS) :
    Function.Injective (finitePairToNatTrans B S hS f P (T := T)) := by
  intro p q hpq
  obtain ⟨U, a, hsurj, hetale⟩ := T.property.exists_atlas
  apply pairBaseChange_cover_ext B S hS f
    (fun (_ : Unit) => (ObjectProperty.homMk a : schemeSpace U ⟶ T))
    (atlas_isFpqcCovering B S hS a hsurj hetale)
    (fun _ => P.sections U ((finitePairToNatTrans B S hS f P p).app (op U)
      (yonedaEquiv a))) (fun _ => finitePairToNatTrans_spec B S hS f P p U a)
  intro i
  rw [hpq]
  exact finitePairToNatTrans_spec B S hS f P q U a

private lemma exists_pair_of_atlas
    (P : FinitePartPresheaf B S hS f)
    {T : AlgebraicSpaces B S hS}
    (v : T.obj ⟶ P.toFunctor)
    {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ T.obj)
    (hsurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    ∃ p : FiniteOpenSubspace B S hS f T,
      PairBaseChange B S hS f (ObjectProperty.homMk a) p
        (P.sections U (yonedaEquiv (a ≫ v))) := by
  let b : T ⟶ Y := ObjectProperty.homMk (v ≫ P.baseMap)
  let z := P.sections U (yonedaEquiv (a ≫ v))
  have hz : z.toBase.hom = a ≫ b.hom := by
    rw [← P.baseMap_spec]
    apply yonedaEquiv.injective
    simp only [Equiv.apply_symm_apply, b, ObjectProperty.homMk_hom, yonedaEquiv_comp]
    rfl
  let R := hsurj.rep.pullback a
  let r := hsurj.rep.fst' a
  let s := hsurj.rep.snd a
  have hR : IsPullback (yoneda.map r) (yoneda.map s) a a := hsurj.rep.isPullback' a
  let zR := P.sections R (P.toFunctor.map r.op (yonedaEquiv (a ≫ v)))
  have hzRr : PairBaseChange B S hS f (schemeSpaceMap r) z zR :=
    P.map_isBaseChange r _
  have hzRs : PairBaseChange B S hS f (schemeSpaceMap s) z zR := by
    have heq : P.toFunctor.map r.op (yonedaEquiv (a ≫ v)) =
        P.toFunctor.map s.op (yonedaEquiv (a ≫ v)) := by
      rw [yonedaEquiv_naturality, yonedaEquiv_naturality,
        ← Category.assoc, hR.w, Category.assoc]
    exact pairBaseChange_of_map_eq B S hS f P s heq.symm
  obtain ⟨p, _, hp⟩ := exists_pair_of_compatible_opens B S hS f
    (fun (_ : Unit) => (ObjectProperty.homMk a : schemeSpace U ⟶ T))
    (atlas_isFpqcCovering B S hS a hsurj hetale) b (fun _ => z) (fun _ => hz)
    (fun _ _ => pairBaseChange_overlap B S hS f
      (ObjectProperty.homMk a : schemeSpace U ⟶ T)
      (ObjectProperty.homMk a : schemeSpace U ⟶ T)
      (schemeSpaceMap r) (schemeSpaceMap s)
      hR b z z zR hz hz hzRr hzRs)
  exact ⟨p, hp ()⟩

private lemma natTrans_ext_of_atlas
    {T : AlgebraicSpaces B S hS}
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : Presheaf.IsSheaf (BigFppfOver.topology B S hS) P)
    {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ T.obj)
    (hsurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (v w : T.obj ⟶ P) (h : a ≫ v = a ≫ w) : v = w := by
  obtain ⟨hRsh, hUsh, ⟨H⟩⟩ := isCoequalizer_of_surjectiveEtale B S hS
    a (hsurj.rep.fst' a) (hsurj.rep.snd a) (hsurj.rep.isPullback' a)
    T.property hsurj hetale
  let TF : Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    ⟨T.obj, T.property.isSheaf⟩
  let PF : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨P, hP⟩
  have heq : (⟨v⟩ : TF ⟶ PF) = ⟨w⟩ :=
    Cofork.IsColimit.hom_ext H (Sheaf.hom_ext h)
  exact congrArg (fun k : TF ⟶ PF => k.hom) heq

private lemma finitePairToNatTrans_surjective
    (P : FinitePartPresheaf B S hS f)
    (hP : Presheaf.IsSheaf (BigFppfOver.topology B S hS) P.toFunctor)
    (T : AlgebraicSpaces B S hS) :
    Function.Surjective (finitePairToNatTrans B S hS f P (T := T)) := by
  intro v
  obtain ⟨U, a, hsurj, hetale⟩ := T.property.exists_atlas
  obtain ⟨p, hp⟩ := exists_pair_of_atlas B S hS f P v a hsurj hetale
  exact ⟨p, natTrans_ext_of_atlas B S hS hP a hsurj hetale _ _
    (yonedaEquiv.injective ((P.sections U).injective
      (pairBaseChange_unique B S hS f (finitePairToNatTrans_spec B S hS f P p U a) hp)))⟩

end

/-- **Stacks 04PE, part (2).** For an algebraic space `T` over `S`, the morphisms of sheaves
from `T` to the finite part `(X/Y)_fin` of `f : X ⟶ Y` are in canonical bijection with the
pairs `(a, Z)` of Stacks 04PC over `T`: the pair attached to a morphism restricts, along every
morphism from a scheme of the site, to the pair that the morphism names there. -/
@[stacks 04PE "part (2)"]
public noncomputable def finiteOpenSubspaceEquiv
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (T : AlgebraicSpaces B S hS) :
    { e : (T.obj ⟶ (finiteOpenSubspacePresheaf B S hS f).toFunctor) ≃
        FiniteOpenSubspace B S hS f T //
      ∀ (v : T.obj ⟶ (finiteOpenSubspacePresheaf B S hS f).toFunctor)
        (U : BigFppfOver B S hS)
        (g : yoneda.obj U ⟶ T.obj),
        let p := e v
        let q := (finiteOpenSubspacePresheaf B S hS f).sections U
          (v.app (op U) (yonedaEquiv g))
        (q.toBase.hom = g ≫ p.toBase.hom) ∧
          ∃ j : q.subspace.toFunctor ⟶ p.subspace.toFunctor,
            (IsPullback
              (q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom)
              j g
              (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom)) ∧
            (j ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom =
              q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom) } := by
  classical
  let P := finiteOpenSubspacePresheaf B S hS f
  let e := (Equiv.ofBijective (finitePairToNatTrans B S hS f P (T := T))
    ⟨finitePairToNatTrans_injective B S hS f P T,
      finitePairToNatTrans_surjective B S hS f P
        (isSheaf_finiteOpenSubspacePresheaf B S hS f) T⟩).symm
  refine ⟨e, fun v U g => ?_⟩
  have h := finitePairToNatTrans_spec B S hS f P (e v) U g
  have he : finitePairToNatTrans B S hS f P (e v) = v := e.symm_apply_apply v
  rwa [he] at h

end AlgebraicGeometry.Space

end
