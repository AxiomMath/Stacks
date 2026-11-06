module

public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.SubobjectFlatDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCountable
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCover
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Equivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Sheafification
import StacksCore.Tactic.EgaSgaAttribute
import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae

/-!
# Closed immersions of algebraic spaces are fpqc local on the base

Being a closed immersion of Stacks 02YU, part (3) — a representable morphism all of whose
represented base changes are closed immersions of schemes — is local on the target for the fpqc
coverings of algebraic spaces over `S`. This is **Stacks 0420**.

The criterion of **Stacks 041J**,
`AlgebraicGeometry.Space.isLocalAtTarget_fpqc_of_affineDescent`, reduces the assertion to three
tests, and the first two are supplied by **Stacks 03M4** for closed immersions,
`AlgebraicGeometry.Space.isClosedImmersion_tfae`: the affine-test clause is that tfae's third
condition, and the clause about finite coproducts is its Zariski-covering condition applied to
the open subspaces cut out by the inclusions of the target's decomposition, which are open
immersions by **Stacks 0F15** and whose base changes are the given morphisms because a category
of sheaves of types is finitary extensive.

The third test is the descent step, over a surjective flat morphism `Z' ⟶ Z` of affine objects
of the site, and it is proved here **without Gabber's Stacks 0APL**, hence without the Stacks
041Z of the source. Two things are needed, and both are unconditional. The descended closed
subscheme is produced by `AlgebraicGeometry.Space.exists_affineCandidate_of_isPullback` — a
closed immersion is affine, and the affine case of Stacks 0245 is quasi-coherent descent and
nothing more — and it is a closed immersion rather than merely affine by **Stacks 02L6**, the
fpqc descent of closed immersions of schemes, which is
`Stacks.Descent.isClosedImmersion_descendsAlong_surjective_inf_flat_inf_quasiCompact`. The
candidate is then identified with the given algebraic space by
`AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_le_monomorphisms_of_flat` of
`StacksFrontier.AlgebraicGeometry.Descent.SubobjectFlatDescent`.

*Why the identification costs no fpqc sheaf condition.* The library's other flat-chart
comparison, `AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_invariant_of_fpqc`,
asks both ends to be fpqc sheaves, which for an algebraic space is exactly Stacks 0APL. The
comparison used here replaces that by three unconditional facts, available because a closed
immersion is a *monomorphism*: the descended projection is injective on sections, since two
sections agreeing after the flat base change agree outright by the fpqc *separatedness* of an
algebraic space (`AlgebraicGeometry.IsAlgebraicSpace.isSeparatedFor_fpqc`); a section of the
target factors through the candidate as soon as it does after the flat base change, because the
candidate is representable and representable presheaves are fpqc sheaves by subcanonicity; and
local surjectivity of the comparison is read on a surjective étale — hence **fppf** — covering
obtained by descending a surjective étale atlas of the descended fibre product along the chart.

## Main results

* `AlgebraicGeometry.Space.isClosedImmersion_isLocalAtTarget_fpqc`: **Stacks 0420**.

## Implementation notes

Coproducts and base changes of the sheaves underlying algebraic spaces are computed in the
category of sheaves of types on the big fppf category over `S`, which has finite colimits and
is finitary extensive once it is sheafifiable. Sheafifiability is not formal here, because that
category is not small: it is deduced from the essential smallness of the full subcategory of
affine objects, which is cover dense in the site, every affine object being the spectrum of a
ring whose cardinality is bounded by the site's cutoff.

The finite index type of the coproduct clause is lifted to the universe of the site, so that
the coproducts may be formed in sheaves of types, and the colimit is transported along that
lift.

In the descent step the morphism is renamed so that its target is spelled `yoneda.obj Z` rather
than the underlying presheaf of the algebraic space of `Z`: the two are definitionally equal,
but only the first makes the identity of the target and the codomain of the chart syntactically
the same, which is what the rewrites of that proof need.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02L6](https://stacks.math.columbia.edu/tag/02L6)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03M4](https://stacks.math.columbia.edu/tag/03M4)
* [Stacks Project, Tag 041J](https://stacks.math.columbia.edu/tag/041J)
* [Stacks Project, Tag 0420](https://stacks.math.columbia.edu/tag/0420)
* [Stacks Project, Tag 0F15](https://stacks.math.columbia.edu/tag/0F15)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w w'

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) AlgebraicGeometry.Space.hasPullback_presheaf_ClosedImmersionFpqcLocalAtTarget
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) : HasPullback f g :=
  HasLimitsOfShape.has_limit _

namespace AlgebraicGeometry.Space

private theorem hasSheafify_of_small_dense
    {C : Type w} [Category.{u} C] [EssentiallySmall.{u} C]
    {D : Type w'} [Category.{u} D] [HasPullbacks D]
    (K : GrothendieckTopology D) (F : C ⥤ D) [F.Full] [F.Faithful]
    [F.IsCoverDense K] : HasSheafify K (Type u) := by
  classical
  let e := equivSmallModel.{u} C
  let G := e.inverse ⋙ F
  let J := G.inducedTopology K
  let : G.IsCoverDense K := ⟨fun X => by
    apply K.superset_covering _ (F.is_cover_of_isCoverDense K X)
    rintro Y f ⟨⟨Z, a, b, hab⟩⟩
    refine ⟨⟨e.functor.obj Z, a ≫ F.map (e.unitIso.hom.app Z),
      F.map (e.unitIso.inv.app Z) ≫ b, ?_⟩⟩
    rw [Category.assoc, ← F.map_comp_assoc, e.unitIso.hom_inv_id_app]
    show a ≫ F.map (𝟙 Z) ≫ b = f
    rw [F.map_id, Category.id_comp]
    exact hab⟩
  let : G.IsDenseSubsite J K := inferInstance
  let : G.IsOneHypercoverDense.{u} J K :=
    Functor.IsOneHypercoverDense.of_hasPullbacks (fun X => by
      let I := Σ Z : SmallModel.{u} C, G.obj Z ⟶ X
      refine ⟨I, (fun i => i.1), (fun i => i.2), ?_⟩
      apply K.superset_covering _ (G.is_cover_of_isCoverDense K X)
      rintro Y f ⟨⟨Z, a, b, hab⟩⟩
      exact ⟨G.obj Z, a, b, Presieve.ofArrows.mk (⟨Z, b⟩ : I), hab⟩)
  let : (G.sheafPushforwardContinuous (Type u) J K).IsEquivalence :=
    Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _
  exact Functor.IsDenseSubsite.hasSheafify_of_isEquivalence J K G

/-- Two pullback squares over the same cospan have second legs satisfying the same
iso-invariant property. -/
private theorem snd_iff_of_isPullback {C : Type*} [Category* C] (P : MorphismProperty C)
    [P.RespectsIso] {A A' X Y Z : C} {a : A ⟶ X} {b : A ⟶ Y} {a' : A' ⟶ X} {b' : A' ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g) (h' : IsPullback a' b' f g) :
    P b ↔ P b' := by
  rw [← h.isoIsPullback_hom_snd _ _ h', P.cancel_left_of_respectsIso]

private theorem closedImmersion_pullback_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Z ⟶ Y) :
    (fun {A D : AlgebraicSpaces B S hS} (h : A ⟶ D) =>
      IsClosedImmersion B S hS h.hom) (pullback.snd f g) ↔
      IsClosedImmersion B S hS (pullback.snd f.hom g.hom) := by
  let T := BigFppfOver.toScheme B S hS
  let Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    (MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion)
      T).presheaf
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun _ _ h => Q h.hom
  have : Q.RespectsIso := MorphismProperty.relative_respectsIso _
  have : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage Q (ObjectProperty.ι _)
  show P (pullback.snd f g) ↔ P (ObjectProperty.homMk (pullback.snd f.hom g.hom) :
    AlgebraicSpaces.fiberProduct B S hS f g ⟶ Z)
  exact snd_iff_of_isPullback P (IsPullback.of_hasPullback f g)
    (AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct B S hS f g)

private theorem closedImmersion_iff_affine_tests
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (fun {A D : AlgebraicSpaces B S hS} (h : A ⟶ D) =>
      IsClosedImmersion B S hS h.hom) f ↔
      ∀ (T : BigAffineFppf B S hS)
        (g : schemeSpace
          ((BigAffineFppf.inclusion B S hS).obj T) ⟶ Y),
        (fun {A D : AlgebraicSpaces B S hS} (h : A ⟶ D) =>
          IsClosedImmersion B S hS h.hom) (pullback.snd f g) := by
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun _ _ (h : _ ⟶ _) => IsClosedImmersion B S hS h.hom
  show P f ↔ ∀ (T : BigAffineFppf B S hS)
    (g : schemeSpace
      ((BigAffineFppf.inclusion B S hS).obj T) ⟶ Y), P (pullback.snd f g)
  have htfae : IsClosedImmersion B S hS f.hom ↔
      ∀ (U : BigFppfOver B S hS)
        (g : yoneda.obj U ⟶ Y.obj),
        IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
          IsClosedImmersion B S hS (pullback.snd f.hom g) :=
    (isClosedImmersion_tfae B S hS X.property Y.property f.hom).out 1 3
  refine ⟨fun hf T g => (closedImmersion_pullback_iff B S hS f g).mpr
    (htfae.mp hf ((BigAffineFppf.inclusion B S hS).obj T) g.hom
      (BigAffineFppf.isAffine_toScheme_obj B S hS T)), fun hf => ?_⟩
  refine htfae.mpr fun U g hU => ?_
  let T : BigAffineFppf B S hS := ⟨U, hU⟩
  let g' : schemeSpace ((BigAffineFppf.inclusion B S hS).obj T) ⟶ Y :=
    ObjectProperty.homMk g
  exact (closedImmersion_pullback_iff B S hS f g').mp (hf T g')

private theorem closedImmersion_schemeMap_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T T' : BigFppfOver B S hS} (f : T' ⟶ T) :
    IsClosedImmersion B S hS
        (yoneda.map f) ↔
      AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map f) := by
  let Tscheme := BigFppfOver.toScheme B S hS
  let : PreservesLimitsOfShape WalkingCospan Tscheme := inferInstance
  let Q : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion) Tscheme
  let : MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u}) := inferInstance
  let : Q.IsStableUnderBaseChange := by
    refine ⟨?_⟩
    intro X Y Z S f g f' g' hp hg
    show AlgebraicGeometry.IsClosedImmersion (Tscheme.map g')
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (hp.map Tscheme) hg
  show Q.presheaf (yoneda.map f) ↔ Q f
  exact MorphismProperty.relative_map_iff (P := Q) (F := yoneda)

private theorem isFlat_schemeSpaceMap_inclusion_map
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T T' : BigAffineFppf B S hS} (g : T' ⟶ T)
    (hflat : Flat ((BigAffineFppf.toScheme B S hS).map g)) :
    IsFlat B S hS (schemeSpaceMap ((BigAffineFppf.inclusion B S hS).map g)).hom := by
  let incl := BigAffineFppf.inclusion B S hS
  let Tscheme := BigFppfOver.toScheme B S hS
  let F := yoneda.obj (incl.obj T')
  let G := yoneda.obj (incl.obj T)
  let : F.IsRepresentable := inferInstance
  let : G.IsRepresentable := inferInstance
  let eF : F.reprX ≅ incl.obj T' := yoneda.preimageIso F.reprW
  let eG : incl.obj T ≅ G.reprX := yoneda.preimageIso G.reprW.symm
  show HoldsOnEveryEtaleChart B S hS (@Flat) (yoneda.map (incl.map g))
  apply (holdsOnEveryEtaleChart_iff_representable
    (B := B) (S := S) (hS := hS)
    (P := @Flat) Flat.isEtaleLocalOnSourceAndTarget
    (yoneda.map (incl.map g))).2
  have hrepr : yoneda.preimage (F.reprW.hom ≫ yoneda.map (incl.map g) ≫ G.reprW.inv) =
      eF.hom ≫ incl.map g ≫ eG.hom := by
    apply Yoneda.fullyFaithful.map_injective
    simp [eF, eG]
  rw [hrepr]
  let : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsStableUnderBaseChange @Flat).respectsIso
  have h₁ : Flat (Tscheme.map eF.hom ≫ Tscheme.map (incl.map g)) :=
    (MorphismProperty.cancel_left_of_respectsIso
      (P := @Flat) (Tscheme.map eF.hom) (Tscheme.map (incl.map g))).mpr hflat
  have h₂ : Flat
      (Tscheme.map eF.hom ≫ Tscheme.map (incl.map g) ≫ Tscheme.map eG.hom) :=
    (MorphismProperty.cancel_right_of_respectsIso
      (P := @Flat) (Tscheme.map eF.hom ≫ Tscheme.map (incl.map g))
      (Tscheme.map eG.hom)).mpr h₁
  simpa only [Functor.map_comp] using h₂

private theorem isAffine_toScheme_pullback_inclusion_map
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A T T' : BigAffineFppf B S hS} (p : A ⟶ T) (g : T' ⟶ T) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (pullback
      ((BigAffineFppf.inclusion B S hS).map p) ((BigAffineFppf.inclusion B S hS).map g))) := by
  let incl := BigAffineFppf.inclusion B S hS
  let Tscheme := BigFppfOver.toScheme B S hS
  let : PreservesLimitsOfShape WalkingCospan Tscheme := inferInstance
  let D := cospan (incl.map p) (incl.map g) ⋙ Tscheme
  let c : Cone D := Tscheme.mapCone (limit.cone (cospan (incl.map p) (incl.map g)))
  have hc : IsLimit c := isLimitOfPreserves Tscheme (limit.isLimit _)
  let : ∀ i, IsAffine (D.obj i) := by
    intro i
    cases i with
    | none =>
        show IsAffine ((BigAffineFppf.toScheme B S hS).obj T)
        exact T.property
    | some j =>
        cases j with
        | left =>
            show IsAffine ((BigAffineFppf.toScheme B S hS).obj A)
            exact A.property
        | right =>
            show IsAffine ((BigAffineFppf.toScheme B S hS).obj T')
            exact T'.property
  exact Scheme.isAffine_of_isLimit c hc

private theorem singleton_toScheme_map_pullback_fst_mem_fpqcPrecoverage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A T T' : BigAffineFppf B S hS} (p : A ⟶ T) (g : T' ⟶ T)
    (hflat : Flat ((BigAffineFppf.toScheme B S hS).map g))
    (hsurj : Surjective ((BigAffineFppf.toScheme B S hS).map g)) :
    Presieve.singleton ((BigAffineFppf.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).preimage (pullback.fst
        ((BigAffineFppf.inclusion B S hS).map p) ((BigAffineFppf.inclusion B S hS).map g)) :
        (⟨_, isAffine_toScheme_pullback_inclusion_map B S hS p g⟩ : BigAffineFppf B S hS) ⟶ A)) ∈
      Scheme.fpqcPrecoverage ((BigAffineFppf.toScheme B S hS).obj A) := by
  let incl := BigAffineFppf.inclusion B S hS
  let Tscheme := BigFppfOver.toScheme B S hS
  let : PreservesLimitsOfShape WalkingCospan Tscheme := inferInstance
  let W : BigAffineFppf B S hS := ⟨_, isAffine_toScheme_pullback_inclusion_map B S hS p g⟩
  let b : W ⟶ A := incl.preimage (pullback.fst (incl.map p) (incl.map g))
  have hpb := (IsPullback.of_hasPullback (incl.map p) (incl.map g)).map Tscheme
  let : Surjective (Tscheme.map (incl.map g)) := hsurj
  let : Flat (Tscheme.map (incl.map g)) := hflat
  have hbc {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
      (h : P (Tscheme.map (incl.map g))) : P (Tscheme.map (incl.map b)) := by
    dsimp [b]
    rw [incl.map_preimage]
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip h
  let : Surjective (Tscheme.map (incl.map b)) := hbc (P := @Surjective) hsurj
  let : Flat (Tscheme.map (incl.map b)) := hbc (P := @Flat) hflat
  let : IsAffine (Tscheme.obj (incl.obj W)) := W.property
  let : IsAffine (Tscheme.obj (incl.obj A)) := A.property
  let : _root_.AlgebraicGeometry.IsAffineHom (Tscheme.map (incl.map b)) := inferInstance
  let : QuasiCompact (Tscheme.map (incl.map b)) := inferInstance
  show Presieve.singleton (Tscheme.map (incl.map b)) ∈ Scheme.fpqcPrecoverage _
  simpa only [BigAffineFppf.toScheme, Tscheme] using
    (Scheme.Hom.singleton_mem_fpqcPrecoverage (Tscheme.map (incl.map b)))

private theorem singleton_schemeMap_fpqcCover
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T T' : BigAffineFppf B S hS) (g : T' ⟶ T)
    (hflat : Flat ((BigAffineFppf.toScheme B S hS).map g))
    (hsurj : Surjective ((BigAffineFppf.toScheme B S hS).map g)) :
    Topology.IsCovering .fpqc B S hS
      (fun _ : PUnit => (schemeSpace
        ((BigAffineFppf.inclusion B S hS).obj T')).obj)
      (fun _ => (schemeSpaceMap
        ((BigAffineFppf.inclusion B S hS).map g)).hom) := by
  let incl := BigAffineFppf.inclusion B S hS
  refine ⟨(schemeSpace (incl.obj T)).property, fun _ => (schemeSpace (incl.obj T')).property,
    fun _ => isFlat_schemeSpaceMap_inclusion_map B S hS g hflat, fun A h => ?_⟩
  let hbase : (yoneda.obj (incl.obj A)) ⟶ (yoneda.obj (incl.obj T)) := h
  let hOver : incl.obj A ⟶ incl.obj T := Yoneda.fullyFaithful.preimage hbase
  let p : A ⟶ T := incl.preimage hOver
  let pOver : incl.obj A ⟶ incl.obj T := incl.map p
  let W : BigAffineFppf B S hS := ⟨_, isAffine_toScheme_pullback_inclusion_map B S hS p g⟩
  let b : W ⟶ A := incl.preimage (pullback.fst pOver (incl.map g))
  let a : W ⟶ T' := incl.preimage (pullback.snd pOver (incl.map g))
  let E : PreZeroHypercover.{u + 1} A := PreZeroHypercover.singleton b
  have hcover : E.presieve₀.map (BigAffineFppf.toScheme B S hS) ∈
      Scheme.fpqcPrecoverage ((BigAffineFppf.toScheme B S hS).obj A) := by
    rw [PreZeroHypercover.presieve₀_singleton, Presieve.map_singleton]
    exact singleton_toScheme_map_pullback_fst_mem_fpqcPrecoverage B S hS p g hflat hsurj
  refine ⟨E, inferInstance, hcover, ?_⟩
  rintro ⟨⟩
  refine ⟨PUnit.unit, (schemeSpaceMap (incl.map a)).hom, ?_⟩
  have hfst : incl.map b = pullback.fst pOver (incl.map g) := by simp [b]
  have hsnd : incl.map a = pullback.snd pOver (incl.map g) := by simp [a]
  have hab : incl.map a ≫ incl.map g = incl.map b ≫ pOver := by
    rw [hsnd, hfst]
    exact (pullback.condition (f := pOver) (g := incl.map g)).symm
  have hp : yoneda.map pOver = hbase := by
    dsimp [pOver, p, hOver]
    rw [incl.map_preimage]
    exact Yoneda.fullyFaithful.map_preimage _
  show yoneda.map (incl.map a) ≫ yoneda.map (incl.map g) =
    yoneda.map (incl.map b) ≫ hbase
  rw [← Functor.map_comp, hab, Functor.map_comp, hp]

attribute [local instance] algebraicSpacesToSheaf_full algebraicSpacesToSheaf_faithful

private noncomputable def sheaf_isColimit
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Finite I] (X : I → AlgebraicSpaces B S hS)
    (X₀ : AlgebraicSpaces B S hS) (ι : ∀ i, X i ⟶ X₀)
    (hc : IsColimit (Cofan.mk X₀ ι)) :
    IsColimit (Cofan.mk ((algebraicSpacesToSheaf B S hS).obj X₀)
      (fun i => (algebraicSpacesToSheaf B S hS).map (ι i))) := by
  letI : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    AlgebraicGeometry.hasSheafifyBigFppfOver B S hS
  letI : HasWeakSheafify (BigFppfOver.topology B S hS) (Type u) :=
    (AlgebraicGeometry.hasSheafifyBigFppfOver B S hS).isRightAdjoint
  letI : HasColimitsOfShape (Discrete I)
      (Sheaf (BigFppfOver.topology B S hS) (Type u)) :=
    Sheaf.instHasColimitsOfShape
  let F := algebraicSpacesToSheaf B S hS
  let Xs := fun i => F.obj (X i)
  letI : HasColimit (Discrete.functor Xs) :=
    HasColimitsOfShape.has_colimit _
  let Zs := ∐ Xs
  let ιs : ∀ i, Xs i ⟶ Zs := Sigma.ι Xs
  have hZs : IsColimit (Cofan.mk Zs ιs) := coproductIsCoproduct Xs
  let Z : AlgebraicSpaces B S hS :=
    ⟨Zs.obj, isAlgebraicSpace_finiteCoproduct B S hS
      (fun i => (X i).obj) (fun i => (X i).property) Zs ιs hZs⟩
  let c : Cofan X := Cofan.mk Z (fun i => ObjectProperty.homMk (ιs i).hom)
  have hm : IsColimit (F.mapCocone c) :=
    (isColimitMapCoconeCofanMkEquiv F X _).symm hZs
  have hz : IsColimit c := isColimitOfReflects F hm
  letI : PreservesColimit (Discrete.functor X) F :=
    preservesColimit_of_preserves_colimit_cocone hz hm
  exact (isColimitMapCoconeCofanMkEquiv F X ι) (isColimitOfPreserves F hc)

private noncomputable def isColimit_ulift
    {C : Type*} [Category* C] {I : Type*} {X : I → C} {Z : C}
    (ι : ∀ i, X i ⟶ Z) (hc : IsColimit (Cofan.mk Z ι)) :
    IsColimit (Cofan.mk Z (fun i : ULift.{u} I => ι i.down)) := by
  refine Cofan.IsColimit.mk _ (fun s => hc.desc (Cofan.mk s.pt
    (fun i => s.inj (ULift.up i)))) ?_ ?_
  · intro s i
    exact hc.fac _ (Discrete.mk i.down)
  · intro s m hm
    exact hc.hom_ext fun i =>
      (hm (ULift.up i.as)).trans (hc.fac (Cofan.mk s.pt (fun i => s.inj (ULift.up i))) i).symm

/-- If a sheaf of types `G` is the coproduct of sheaves `F i` with injections `ι i`, then the
induced morphism from the presheaf coproduct `∐ i, (F i).obj` to `G` is locally surjective. -/
theorem coproduct_locallySurjective
    {C : Type w} [Category.{v} C] (J : GrothendieckTopology C)
    {I : Type u} (F : I → Sheaf J (Type u)) {G : Sheaf J (Type u)}
    (ι : ∀ i, F i ⟶ G) (hG : IsColimit (Cofan.mk G ι)) :
    Presheaf.IsLocallySurjective J (Sigma.desc fun i => (ι i).hom) := by
  classical
  let P : I → Cᵒᵖ ⥤ Type u := fun i => (F i).obj
  let q : (∐ P) ⟶ G.obj := Sigma.desc fun i => (ι i).hom
  let R : Subfunctor G.obj := Subfunctor.range q
  let H : Sheaf J (Type u) :=
    ⟨(R.sheafify J).toFunctor, (isSheaf_iff_isSheaf_of_type J _).mpr
      (Subfunctor.sheafify_isSheaf R
        ((isSheaf_iff_isSheaf_of_type J G.obj).1 G.property))⟩
  let m : H ⟶ G := ⟨(R.sheafify J).ι⟩
  let η : ∀ i, F i ⟶ H := fun i =>
    ⟨Sigma.ι P i ≫ Subfunctor.toRangeSheafify J q⟩
  have hfactor : ∀ i, η i ≫ m = ι i := by
    intro i
    ext1
    ext X x
    show ((Subfunctor.toRange q).app X ((Sigma.ι P i).app X x)).val =
      (ι i).hom.app X x
    rw [Subfunctor.toRange_app_val]
    have hq : Sigma.ι P i ≫ q = (ι i).hom := by simp [q]
    exact congrArg (fun f => f.app X x) hq
  let cH : Cofan (fun i => F i) := Cofan.mk H η
  let hGtoH : G ⟶ H := hG.desc cH
  have hiden : hGtoH ≫ m = 𝟙 G := by
    apply hG.hom_ext
    intro i
    calc
      (Cofan.mk G ι).ι.app i ≫ hG.desc cH ≫ m = cH.ι.app i ≫ m := by
        rw [← Category.assoc, hG.fac cH i]
      _ = (Cofan.mk G ι).ι.app i ≫ 𝟙 G := by
        simpa [cH] using hfactor i.as
  have htop : R.sheafify J = ⊤ := by
    ext X x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have hx := congrArg (fun f : G ⟶ G => f.hom.app X x) hiden
    have hx' : (hGtoH.hom.app X x).val = x := by simpa [m] using hx
    rw [← hx']
    exact (hGtoH.hom.app X x).property
  exact (Presheaf.isLocallySurjective_iff_range_sheafify_eq_top' J q).2 htop

private theorem coproduct_binary_decomposition
    {C : Type*} [Category* C] {I : Type*} (F : I → C) {G : C}
    (ι : ∀ i, F i ⟶ G) (hG : IsColimit (Cofan.mk G ι)) (i : I)
    [HasColimit (Discrete.functor (fun j : {j : I // j ≠ i} => F j.val))] :
    Nonempty (Σ H : C, Σ m : H ⟶ G,
      IsColimit (BinaryCofan.mk (ι i) m)) := by
  classical
  let R := {j : I // j ≠ i}
  let Fr : R → C := fun j => F j.val
  let H := ∐ Fr
  let η : ∀ j : R, Fr j ⟶ H := Sigma.ι Fr
  let m : H ⟶ G := Sigma.desc fun j : R => ι j.val
  have hm (j : R) : η j ≫ m = ι j.val := by simp [η, m]
  let δ (Z : C) (f : F i ⟶ Z) (g : H ⟶ Z) (j : I) : F j ⟶ Z :=
    if h : j = i then eqToHom (congrArg F h) ≫ f else η ⟨j, h⟩ ≫ g
  have hr (Z : C) (f : F i ⟶ Z) (g : H ⟶ Z) :
      ι i ≫ hG.desc (Cofan.mk Z (δ Z f g)) = f := by
    simpa [δ] using hG.fac (Cofan.mk Z (δ Z f g)) (Discrete.mk i)
  refine ⟨⟨H, m, ?_⟩⟩
  refine BinaryCofan.IsColimit.mk (BinaryCofan.mk (ι i) m)
    (fun {Z} f g => hG.desc (Cofan.mk Z (δ Z f g))) ?_ ?_ ?_
  · intro Z f g
    exact hr Z f g
  · intro Z f g
    apply Sigma.hom_ext
    intro j
    have hj : ι j.val ≫ hG.desc (Cofan.mk Z (δ Z f g)) = η j ≫ g := by
      simpa [δ, j.property] using hG.fac (Cofan.mk Z (δ Z f g)) (Discrete.mk j.val)
    show η j ≫ m ≫ hG.desc (Cofan.mk Z (δ Z f g)) = η j ≫ g
    rwa [← Category.assoc, hm j]
  · intro Z f g l hl₁ hl₂
    change G ⟶ Z at l
    change ι i ≫ l = f at hl₁
    change m ≫ l = g at hl₂
    apply hG.hom_ext
    intro j
    by_cases hj : j.as = i
    · obtain rfl : j = Discrete.mk i := Discrete.ext hj
      exact hl₁.trans (hr Z f g).symm
    · have hfac' : ι j.as ≫ hG.desc (Cofan.mk Z (δ Z f g)) = η ⟨j.as, hj⟩ ≫ g := by
        simpa [δ, hj] using hG.fac (Cofan.mk Z (δ Z f g)) j
      calc
        ι j.as ≫ l = (η ⟨j.as, hj⟩ ≫ m) ≫ l := by rw [hm]
        _ = η ⟨j.as, hj⟩ ≫ g := by rw [Category.assoc, hl₂]
        _ = ι j.as ≫ hG.desc (Cofan.mk Z (δ Z f g)) := hfac'.symm

private alias isOpenSubspace_range_of_presheaf_isOpenImmersion :=
  AlgebraicGeometry.Space.isOpenSubspace_range_of_isAlgebraicSpace

private theorem isOpenImmersion_hom_of_isColimit_sheaf_cofan
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} (Y : I → AlgebraicSpaces B S hS) (Y₀ : AlgebraicSpaces B S hS)
    (ιY : ∀ i, Y i ⟶ Y₀)
    (hy : IsColimit (Cofan.mk ((algebraicSpacesToSheaf B S hS).obj Y₀)
      (fun i => (algebraicSpacesToSheaf B S hS).map (ιY i)))) (i : I) :
    IsOpenImmersion B S hS (ιY i).hom := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    AlgebraicGeometry.hasSheafifyBigFppfOver B S hS
  let : HasWeakSheafify (BigFppfOver.topology B S hS) (Type u) :=
    (AlgebraicGeometry.hasSheafifyBigFppfOver B S hS).isRightAdjoint
  let : HasColimit (Discrete.functor
      (fun j : {j : I // j ≠ i} => (algebraicSpacesToSheaf B S hS).obj (Y j.val))) :=
    (Sheaf.instHasColimitsOfShape).has_colimit _
  obtain ⟨⟨H, m, hm⟩⟩ := coproduct_binary_decomposition
    (fun i => (algebraicSpacesToSheaf B S hS).obj (Y i))
    (fun i => (algebraicSpacesToSheaf B S hS).map (ιY i)) hy i
  exact coproductInl_isOpenImmersion B S hS _ _ _ _ _ hm

private theorem isZariskiCover_range_of_isColimit_sheaf_cofan
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} (Y : I → AlgebraicSpaces B S hS) (Y₀ : AlgebraicSpaces B S hS)
    (ιY : ∀ i, Y i ⟶ Y₀)
    (hy : IsColimit (Cofan.mk ((algebraicSpacesToSheaf B S hS).obj Y₀)
      (fun i => (algebraicSpacesToSheaf B S hS).map (ιY i)))) :
    IsZariskiCover B S hS I (fun i => Subfunctor.range (ιY i).hom) := by
  let U : I → Subfunctor Y₀.obj := fun i => Subfunctor.range (ιY i).hom
  refine ⟨fun i => isOpenSubspace_range_of_presheaf_isOpenImmersion B S hS
    (Y i).property _ (isOpenImmersion_hom_of_isColimit_sheaf_cofan B S hS Y Y₀ ιY hy i), ?_⟩
  have hsurj : Presheaf.IsLocallySurjective
      (BigFppfOver.topology B S hS)
      (Sigma.desc fun i : I => (ιY i).hom) :=
    coproduct_locallySurjective (BigFppfOver.topology B S hS) _ _ hy
  let m : (∐ fun i : I => (Y i).obj) ⟶ ∐ fun i => (U i).toFunctor :=
    Sigma.desc (fun i => Subfunctor.toRange (ιY i).hom ≫
      Sigma.ι (fun i => (U i).toFunctor) i)
  have he : m ≫ (Sigma.desc fun i => (U i).ι) =
      Sigma.desc (fun i : I => (ιY i).hom) := by
    apply Sigma.hom_ext
    intro i
    simp [m, U]
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ he

private theorem isClosedImmersion_pullback_snd_range_of_isPullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y X₀ Y₀ : AlgebraicSpaces B S hS} (f : X ⟶ Y) (ιX : X ⟶ X₀) (ιY : Y ⟶ Y₀)
    (g : X₀ ⟶ Y₀) (hs : IsPullback ιX.hom f.hom g.hom ιY.hom)
    (hopen : IsOpenImmersion B S hS ιY.hom) (hf : IsClosedImmersion B S hS f.hom) :
    IsClosedImmersion B S hS (pullback.snd g.hom (Subfunctor.range ιY.hom).ι) := by
  let Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf
  let : Q.RespectsIso := MorphismProperty.relative_respectsIso _
  have hc : Q (pullback.snd g.hom ιY.hom) :=
    (snd_iff_of_isPullback Q (IsPullback.of_hasPullback g.hom ιY.hom) hs).mpr hf
  have : IsIso (Subfunctor.toRange ιY.hom) := by
    let := mono_of_presheaf_isOpenImmersion hopen
    infer_instance
  let e : Y.obj ≅ (Subfunctor.range ιY.hom).toFunctor := asIso (Subfunctor.toRange ιY.hom)
  let m := pullback.map g.hom ιY.hom g.hom (Subfunctor.range ιY.hom).ι
    (𝟙 _) e.hom (𝟙 _) (by simp) (by simp [e])
  have : IsIso m :=
    pullback.map_isIso g.hom ιY.hom g.hom (Subfunctor.range ιY.hom).ι
      (𝟙 _) e.hom (𝟙 _) (by simp) (by simp [e])
  apply (Q.cancel_left_of_respectsIso m _).mp
  dsimp only [m, pullback.map]
  rw [pullback.lift_snd]
  exact (Q.cancel_right_of_respectsIso _ e.hom).mpr hc

private theorem closedImmersion_preserved_by_finite_coproducts
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    ∀ (n : ℕ)
      (X Y : Fin n → AlgebraicSpaces B S hS)
      (f : ∀ i, X i ⟶ Y i)
      (X₀ Y₀ : AlgebraicSpaces B S hS)
      (ιX : ∀ i, X i ⟶ X₀) (ιY : ∀ i, Y i ⟶ Y₀)
      (g : X₀ ⟶ Y₀),
      IsColimit (Cofan.mk X₀ ιX) →
      IsColimit (Cofan.mk Y₀ ιY) →
      (∀ i, f i ≫ ιY i = ιX i ≫ g) →
    (∀ i, IsClosedImmersion B S hS (f i).hom) →
      IsClosedImmersion B S hS g.hom := by
  classical
  intro n X Y f X₀ Y₀ ιX ιY g hX hY hcomm hf
  let I := ULift.{u} (Fin n)
  let F := algebraicSpacesToSheaf B S hS
  let Xs : I → _ := fun i => F.obj (X i.down)
  let Ys : I → _ := fun i => F.obj (Y i.down)
  let ix : ∀ i : I, Xs i ⟶ F.obj X₀ := fun i => F.map (ιX i.down)
  let iy : ∀ i : I, Ys i ⟶ F.obj Y₀ := fun i => F.map (ιY i.down)
  have hx := sheaf_isColimit B S hS (fun i : I => X i.down) X₀
    (fun i => ιX i.down) (isColimit_ulift ιX hX)
  have hy := sheaf_isColimit B S hS (fun i : I => Y i.down) Y₀
    (fun i => ιY i.down) (isColimit_ulift ιY hY)
  let α : Discrete.functor Xs ⟶ Discrete.functor Ys :=
    Discrete.natTrans (fun i => F.map (f i.as.down))
  have hw : α ≫ (Cofan.mk (F.obj Y₀) iy).ι =
      (Cofan.mk (F.obj X₀) ix).ι ≫ (Functor.const (Discrete I)).map (F.map g) :=
    NatTrans.ext <| funext fun i => congrArg F.map (hcomm i.as.down)
  have hp (i : I) : IsPullback (ix i) (F.map (f i.down)) (F.map g) (iy i) :=
    ((FinitaryExtensive.isVanKampen_finiteCoproducts hy)
      (Cofan.mk (F.obj X₀) ix) α (F.map g) hw
      (NatTrans.Equifibered.of_discrete α)).mp ⟨hx⟩ (Discrete.mk i)
  apply ((isClosedImmersion_tfae B S hS X₀.property Y₀.property g.hom).out 1 5).mpr
  refine ⟨I, fun i => Subfunctor.range (ιY i.down).hom,
    isZariskiCover_range_of_isColimit_sheaf_cofan B S hS (fun i : I => Y i.down) Y₀
      (fun i : I => ιY i.down) hy,
    fun i => ?_⟩
  exact isClosedImmersion_pullback_snd_range_of_isPullback B S hS (f i.down) (ιX i.down)
    (ιY i.down) g ((hp i).map (sheafToPresheaf _ (Type u)))
    (isOpenImmersion_hom_of_isColimit_sheaf_cofan B S hS (fun i : I => Y i.down) Y₀
      (fun i : I => ιY i.down) hy i)
    (hf i.down)

private theorem isClosedImmersion_le_monomorphisms :
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) ≤
      MorphismProperty.monomorphisms Scheme.{u} :=
  fun _ _ z (_ : _root_.AlgebraicGeometry.IsClosedImmersion z) => inferInstanceAs (Mono z)

private theorem inverseImage_isClosedImmersion_le_isAffineHom
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) ≤ (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) :=
  fun _ _ z (_ : _root_.AlgebraicGeometry.IsClosedImmersion
    ((BigFppfOver.toScheme B S hS).map z)) =>
    inferInstanceAs (_root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map z))

private theorem quasiCompact_toScheme_map_inclusion_map
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T T' : BigAffineFppf B S hS} (g : T' ⟶ T) :
    QuasiCompact ((BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map g)) := by
  have haff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj T)) := T.property
  have hcaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj T')) := T'.property
  have hqaff : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map
    ((BigAffineFppf.inclusion B S hS).map g)) := inferInstance
  infer_instance

private theorem isClosedImmersion_toScheme_map_of_iso_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U V : BigFppfOver B S hS}
    (e : P ≅ yoneda.obj U) (w : U ⟶ V)
    (h : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (e.hom ≫ yoneda.map w)) :
    _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map w) := by
  let Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
  have : Q.RespectsIso := MorphismProperty.relative_respectsIso _
  exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@AlgebraicGeometry.IsClosedImmersion.{u}) w).1
    ((MorphismProperty.cancel_left_of_respectsIso (P := Q) e.hom (yoneda.map w)).1 h)

private theorem of_pullback_snd_id {C : Type*} [Category* C] (P : MorphismProperty C)
    [P.RespectsIso] {X Y : C} (f : X ⟶ Y) [HasPullback f (𝟙 Y)]
    (h : P (pullback.snd f (𝟙 Y))) : P f := by
  have : IsIso (pullback.fst f (𝟙 Y)) :=
    (IsPullback.of_hasPullback f (𝟙 _)).isIso_fst_of_isIso (IsIso.id _)
  refine (P.cancel_left_of_respectsIso (pullback.fst f (𝟙 Y)) f).1 ?_
  rwa [pullback.condition, Category.comp_id]

/-- **The descent step for closed immersions along a surjective flat morphism of affine objects
of the site.** Let `g : T' ⟶ T` be a surjective flat morphism of affine objects of the big fppf
site of `S`, let `X` be an algebraic space over `S` and let `f : X ⟶ h_T`. If the base change of
`f` along `g` is a closed immersion then so is `f`.

This is the third hypothesis of Stacks 041J at the closed immersions, and it is where Gabber's
Stacks 0APL is avoided. The datum is a closed immersion, hence affine, so the unconditional
affine descent of `AlgebraicGeometry.Space.exists_affineCandidate_of_isPullback` — quasi-coherent
descent and nothing more — produces a candidate `i : bb ⟶ T` for the descended object, which is
a closed immersion because its base change along `g` is one and closed immersions of schemes
descend along surjective flat quasi-compact morphisms (**Stacks 02L6**). The candidate is then
identified with `X` by
`AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_le_monomorphisms_of_flat`, which
needs no fpqc sheaf condition. -/
@[sga "3 IV 6.4.1" "special case"]
private theorem closedImmersion_descends_affine_fpqc
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T T' : BigAffineFppf B S hS)
    (g : T' ⟶ T)
    (hgFlat : Flat ((BigAffineFppf.toScheme B S hS).map g))
    (hgSurjective : Surjective ((BigAffineFppf.toScheme B S hS).map g))
    (X : AlgebraicSpaces B S hS)
    (f : X ⟶ schemeSpace
      ((BigAffineFppf.inclusion B S hS).obj T))
    (hf : (fun {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) =>
      IsClosedImmersion B S hS f.hom)
      (pullback.snd f (schemeSpaceMap
        ((BigAffineFppf.inclusion B S hS).map g)))) :
    IsClosedImmersion B S hS f.hom := by
  let Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
  have hQiso : Q.RespectsIso := MorphismProperty.relative_respectsIso _
  -- name the morphism with the represented presheaf as its target, so that the identity of
  -- that presheaf and the target of the chart are spelled the same way
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : X.obj ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj T),
      f₀ = f.hom := ⟨f.hom, rfl⟩
  rw [← hf₀]
  -- the chart, with both ends affine
  have haff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj T)) := T.property
  have hcaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj T')) := T'.property
  have hqs : Surjective ((BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map g)) := hgSurjective
  have hqf : Flat ((BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map g)) := hgFlat
  have hqc := quasiCompact_toScheme_map_inclusion_map B S hS g
  -- the datum is a closed immersion, hence an affine morphism
  have hrCI : Q (pullback.snd f₀
      (yoneda.map ((BigAffineFppf.inclusion B S hS).map g))) := by
    rw [hf₀]
    exact (closedImmersion_pullback_iff B S hS f
      (schemeSpaceMap ((BigAffineFppf.inclusion B S hS).map g))).mp hf
  have hrAff := MorphismProperty.relative_monotone
    (inverseImage_isClosedImmersion_le_isAffineHom B S hS) _ hrCI
  -- the datum as a Cartesian square over the identity of the base
  have sqA : IsPullback
      (pullback.fst f₀ (yoneda.map ((BigAffineFppf.inclusion B S hS).map g)))
      (pullback.snd f₀ (yoneda.map ((BigAffineFppf.inclusion B S hS).map g))) f₀
      (yoneda.map ((BigAffineFppf.inclusion B S hS).map g) ≫
        𝟙 (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj T))) := by
    rw [Category.comp_id]
    exact IsPullback.of_hasPullback _ _
  -- the descended affine candidate, by quasi-coherent descent alone
  obtain ⟨bb, v, i, k, w, -, csqSite, e, he, -⟩ :=
    exists_affineCandidate_of_isPullback sqA hrAff haff hcaff hqs hqf
  have csq := csqSite.map (BigFppfOver.toScheme B S hS)
  -- the candidate is a closed immersion, by Stacks 02L6
  have hiCI : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map i) :=
    MorphismProperty.of_isPullback_of_descendsAlong csq.flip
      (show (@Surjective.{u} ⊓ @Flat.{u} ⊓ @QuasiCompact.{u} : MorphismProperty Scheme.{u})
        ((BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map g)) from
        ⟨⟨hqs, hqf⟩, hqc⟩)
      (isClosedImmersion_toScheme_map_of_iso_comp B S hS e w (by rwa [he]))
  -- the flat-chart descent step, which needs no fpqc sheaf condition
  have hYalg := isAlgebraicSpace_yoneda B S hS ((BigAffineFppf.inclusion B S hS).obj T)
  have hPb := isAlgebraicSpace_pullback B S hS f₀ (𝟙 _) X.property hYalg hYalg
  -- read the conclusion on the morphism itself
  exact of_pullback_snd_id Q f₀ (presheaf_pullback_snd_of_isPullback_of_le_monomorphisms_of_flat
    isClosedImmersion_le_monomorphisms X.property.isSheaf hYalg.isSheaf hPb sqA hrCI hqs hqf
    hqc hiCI csq e he)

/-- **Stacks 0420.** Being a closed immersion is fpqc local on the base for morphisms of
algebraic spaces over `S`: such a morphism is a closed immersion exactly when its base change
to every member of some fpqc covering of its target is one. -/
@[stacks 0420, sga "3 IV 6.4.1" "(N')"]
theorem isClosedImmersion_isLocalAtTarget_fpqc
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsClosedImmersion B S hS f.hom)
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
  isLocalAtTarget_fpqc_of_affineDescent B S hS _
    (closedImmersion_preserved_by_finite_coproducts B S hS)
    (closedImmersion_iff_affine_tests B S hS)
    (closedImmersion_descends_affine_fpqc B S hS)

end AlgebraicGeometry.Space

end
