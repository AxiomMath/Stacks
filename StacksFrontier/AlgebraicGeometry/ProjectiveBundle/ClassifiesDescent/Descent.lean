module

public import StacksFrontier.AlgebraicGeometry.Ample.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.ChartCocycleRigidity.DegreeSection
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.PullbackExt
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.TwistPullback
public import StacksFrontier.AlgebraicGeometry.Constructions.MorphismToProjUniversal
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOneRepresents
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.PullbackCover
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.GlobalSection
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.PullbackTautologicalSection
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocalChartPinning
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Sections
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.DegreeOneProductsGlue
public import StacksFrontier.AlgebraicGeometry.SymGenDegreeOne.Basic
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.ChartHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The classifying isomorphism descends from an open cover, and the local object comparison

* `Stacks.Divisors.exists_iso_of_pullback_cover`: the descent of a comparison isomorphism.
* `Stacks.RelativeProj.TautologicalDatum.exists_classifies_of_pullback_cover`: `exists_classifies`
  reduced to the local classifying data.
* The object half of the local classifying datum, the pulled-back tautological map on sections,
  and the trivialisation of the inverse image carrying `q` to the trivialised quotient.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleHomGlue

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} {E M N : X.Modules}

/-- **A comparison isomorphism carrying one quotient map to another descends along an open
cover.** Let `p : E ⟶ M` be an epimorphism and `q : E ⟶ N` any morphism. If over every member
of an open cover of `X` there is an isomorphism of the inverse images of `M` and `N` carrying
the inverse image of `p` to that of `q`, then there is one over `X`.

No agreement on intersections is assumed: over each open the equation `p ≫ α = q` determines
`α`, because the inverse image of `p` is again an epimorphism. -/
public theorem exists_iso_of_pullback_cover {ι : Type u} (V : ι → X.Opens)
    (hV : ∀ x : X, ∃ i, x ∈ V i) (p : E ⟶ M) (q : E ⟶ N) [Epi p]
    (h : ∀ i : ι, ∃ α : (Scheme.Modules.pullback (V i).ι).obj M ≅
          (Scheme.Modules.pullback (V i).ι).obj N,
        (Scheme.Modules.pullback (V i).ι).map p ≫ α.hom =
          (Scheme.Modules.pullback (V i).ι).map q) :
    ∃ α : M ≅ N, p ≫ α.hom = q := by
  choose α hα using h
  have key : ∀ (i : ι) (W : X.Opens) (hW : W ≤ V i),
      (Scheme.Modules.pullback W.ι).map p ≫ pullbackRestrictLocal W hW (α i).hom =
        (Scheme.Modules.pullback W.ι).map q :=
    fun i W hW =>
      ((congrArg (fun z => z ≫ pullbackRestrictLocal W hW (α i).hom)
            (pullbackRestrictLocal_pullback_map p hW).symm).trans
          ((pullbackRestrictLocal_comp hW ((Scheme.Modules.pullback (V i).ι).map p)
              (α i).hom).symm.trans
            (congrArg (pullbackRestrictLocal W hW) (hα i)))).trans
        (pullbackRestrictLocal_pullback_map q hW)
  have hagree : ∀ (i j : ι) (W : X.Opens) (hi : W ≤ V i) (hj : W ≤ V j),
      pullbackRestrictLocal W hi (α i).hom = pullbackRestrictLocal W hj (α j).hom := by
    intro i j W hi hj
    have : (Scheme.Modules.pullback W.ι).PreservesEpimorphisms :=
      Functor.preservesEpimorphisms_of_adjunction
        (Scheme.Modules.pullbackPushforwardAdjunction W.ι)
    have : Epi ((Scheme.Modules.pullback W.ι).map p) := inferInstance
    exact (cancel_epi ((Scheme.Modules.pullback W.ι).map p)).mp
      ((key i W hi).trans (key j W hj).symm)
  refine ⟨glueIsoOfCover V hV (fun i => (α i).hom) hagree,
    hom_ext_of_pullbackCover V hV fun i => ?_⟩
  refine Eq.trans (Functor.map_comp _ p _) ?_
  refine Eq.trans (congrArg (fun z => (Scheme.Modules.pullback (V i).ι).map p ≫ z) ?_) (hα i)
  exact pullback_map_glueOfCover V hV (fun i => (α i).hom) hagree i

/-- **Equivalence of invertible quotients is a local question on the base.** Two invertible
quotients of `ℰ` whose inverse images along the members of an open cover are equivalent by
isomorphisms compatible with the quotient maps are equivalent.

This is the relation `Stacks.Divisors.InvertibleQuotient.IsEquivalent` that [Stacks, Tag 0B3V]'s
bijection is taken modulo, so it is the form the descent is consumed in. -/
public theorem InvertibleQuotient.isEquivalent_of_pullback_cover (P Q : InvertibleQuotient X E)
    {ι : Type u} (V : ι → X.Opens) (hV : ∀ x : X, ∃ i, x ∈ V i)
    (h : ∀ i : ι, ∃ α : (Scheme.Modules.pullback (V i).ι).obj P.L ≅
          (Scheme.Modules.pullback (V i).ι).obj Q.L,
        (Scheme.Modules.pullback (V i).ι).map P.q ≫ α.hom =
          (Scheme.Modules.pullback (V i).ι).map Q.q) :
    P.IsEquivalent Q :=
  have : Epi P.q := P.epi
  exists_iso_of_pullback_cover V hV P.q Q.q h

end Stacks.Divisors

namespace Stacks.RelativeProj

open Stacks.Divisors

variable {X : Scheme.{u}} {F : X.Modules} [F.IsQuasicoherent]

/-- **A section of `π : 𝐏(ℰ) ⟶ X` classifies an invertible quotient as soon as it does so
locally on the base.** The comparison isomorphism of
`Stacks.RelativeProj.TautologicalDatum.Classifies` descends along any open cover of `X`, the
pulled-back tautological map being an epimorphism. -/
public theorem TautologicalDatum.classifies_of_pullback_cover (D : TautologicalDatum X F)
    (σ : X ⟶ projectiveBundle X F) (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
    (Q : InvertibleQuotient X F) {ι : Type u} (V : ι → X.Opens)
    (hV : ∀ x : X, ∃ i, x ∈ V i)
    (h : ∀ i : ι, ∃ α : (Scheme.Modules.pullback (V i).ι).obj
            ((Scheme.Modules.pullback σ).obj D.twist) ≅
          (Scheme.Modules.pullback (V i).ι).obj Q.L,
        (Scheme.Modules.pullback (V i).ι).map (D.pullbackQuotientMap σ hσ) ≫ α.hom =
          (Scheme.Modules.pullback (V i).ι).map Q.q) :
    D.Classifies σ hσ Q :=
  (D.classifies_iff σ hσ Q).mpr
    (exists_iso_of_pullback_cover V hV (D.pullbackQuotientMap σ hσ) Q.q h)

variable {L : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **The glued section of `Stacks.RelativeProj.globalSection` classifies the quotient it was
built from as soon as it does so locally on the base.** The section and the fact that it is a
section are already established; what this statement asks for is only that the quotient it pulls
back agree
with the given one over the members of some open cover of `X`.

This is the exact shape in which the remaining work on [Stacks, Tag 0B3V]'s bijection is owed;
see this file's `Not done here`. -/
public theorem TautologicalDatum.classifies_globalSection_of_pullback_cover
    (D : TautologicalDatum X F) (q : F ⟶ L) [hq : Epi q]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L)
    {ι : Type u} (V : ι → X.Opens) (hV : ∀ x : X, ∃ i, x ∈ V i)
    (h : ∀ i : ι, ∃ α : (Scheme.Modules.pullback (V i).ι).obj
            ((Scheme.Modules.pullback (globalSection q)).obj D.twist) ≅
          (Scheme.Modules.pullback (V i).ι).obj L,
        (Scheme.Modules.pullback (V i).ι).map
              (D.pullbackQuotientMap (globalSection q)
                (globalSection_comp_projectiveBundleToBase q)) ≫ α.hom =
          (Scheme.Modules.pullback (V i).ι).map q) :
    D.Classifies (globalSection q) (globalSection_comp_projectiveBundleToBase q)
      ⟨L, hL, q, hq⟩ :=
  D.classifies_of_pullback_cover _ _ ⟨L, hL, q, hq⟩ V hV h

/-- **`exists_classifies` for one invertible quotient, reduced to the local classifying data.**
The field `Stacks.RelativeProj.TautologicalDatum.IsUniversal.exists_classifies` is this statement
quantified over the quotients, so with the local data in hand the field is discharged. -/
public theorem TautologicalDatum.exists_classifies_of_pullback_cover
    (D : TautologicalDatum X F) (q : F ⟶ L) [hq : Epi q]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L)
    {ι : Type u} (V : ι → X.Opens) (hV : ∀ x : X, ∃ i, x ∈ V i)
    (h : ∀ i : ι, ∃ α : (Scheme.Modules.pullback (V i).ι).obj
            ((Scheme.Modules.pullback (globalSection q)).obj D.twist) ≅
          (Scheme.Modules.pullback (V i).ι).obj L,
        (Scheme.Modules.pullback (V i).ι).map
              (D.pullbackQuotientMap (globalSection q)
                (globalSection_comp_projectiveBundleToBase q)) ≫ α.hom =
          (Scheme.Modules.pullback (V i).ι).map q) :
    ∃ σ : X ⟶ projectiveBundle X F,
      ∃ hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X,
        D.Classifies σ hσ ⟨L, hL, q, hq⟩ :=
  ⟨globalSection q, globalSection_comp_projectiveBundleToBase q,
    D.classifies_globalSection_of_pullback_cover q hL V hV h⟩

/-! ### The object half of the local classifying datum -/

section CoverTwist

open Opposite
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.ProjTwistPinnedChart
open Stacks.SymGraded

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

/-- **The object the local classifying datum of `exists_classifies_of_pullback_cover` compares,
read on the pinned frame — for an arbitrary section `σ` of `π` whose restriction to `V` has a
chart factorisation.**

Over an affine open `V` of `X` the inverse image along `V ⟶ X` of the module that `σ` pulls back
from `𝒪_{𝐏(ℰ)}(1)` is — by an explicit isomorphism — the module
`Stacks.AlgebraicGeometry.MorphismsIntoProj.pullbackTwist` on which the pulled-back degree-one
section of a frame is a basis
(`Stacks.AlgebraicGeometry.ProjTwistPinnedChart.bijective_smul_pullbackDegreeSection`) and on
which the pinning match
`Stacks.RelativeProj.resT_pullbackDegreeSection_localChartMap` holds.

It is the composite of the splitting of the pullback along `V.ι ≫ σ`, the restriction
`V.ι ≫ σ = τ`, and `Stacks.RelativeProj.chartFactorisationPullbackTwistIso` at the pair
`(τ, h)`. For the glued section `Stacks.RelativeProj.globalSection q` the restriction is
`Stacks.RelativeProj.ι_comp_globalSection_eq_localSection` and `h` is
`Stacks.RelativeProj.localChartMap`, which is `globalSectionPullbackTwistIsoOnCover` below; for an
arbitrary section `τ` is `V.ι ≫ σ` itself and `h` comes from
`Stacks.AlgebraicGeometry.RelativeProj.chartHomEquivOver`.

This is the **object** half of the datum that
`Stacks.RelativeProj.TautologicalDatum.exists_classifies_of_pullback_cover` consumes; the half
still owed is that the comparison *carries the pulled-back tautological map to `q`*. -/
public def restrictChartFactorisationTwistIso (V : X.Opens) (hV : IsAffineOpen V)
    (σ : X ⟶ projectiveBundle X F) (τ : V.toScheme ⟶ projectiveBundle X F)
    (hcs : V.ι ≫ σ = τ)
    (h : V.toScheme ⟶ AlgebraicGeometry.Proj
      ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V))
    (hgh : τ ≫ (bundlePresentationIso F).inv = h ≫ (symGradedBundle F).chart V hV) :
    (Scheme.Modules.pullback V.ι).obj
        ((Scheme.Modules.pullback σ).obj (tautologicalDatumTwist F)) ≅
      (Scheme.Modules.pullback h).obj
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
          ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
          1) :=
  (Scheme.Modules.pullbackComp V.ι σ).app _ ≪≫
    (Scheme.Modules.pullbackCongr hcs).app _ ≪≫
    chartFactorisationTwistIso V hV τ h hgh

/-- **The object comparison over an affine open, read on the open `U_1` where the twist is
invertible.** This is `restrictChartFactorisationTwistIso` followed by the transport along
`Stacks.AlgebraicGeometry.ProjTwistPinnedChart.toProj_chartFactor`, so it is the shape the
pinning match lives on; the raw version above is the one that needs no standard-open
hypothesis `hg`, and it is what produces that hypothesis. -/
public def restrictChartFactorisationPullbackTwistIso (V : X.Opens) (hV : IsAffineOpen V)
    (σ : X ⟶ projectiveBundle X F) (τ : V.toScheme ⟶ projectiveBundle X F)
    (hcs : V.ι ≫ σ = τ)
    (h : V.toScheme ⟶ AlgebraicGeometry.Proj
      ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V))
    (hgh : τ ≫ (bundlePresentationIso F).inv = h ≫ (symGradedBundle F).chart V hV)
    {m₀ : Γ(F, V)}
    (hg : h ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
        (localDegreeOne V m₀).1 = ⊤) :
    (Scheme.Modules.pullback V.ι).obj
        ((Scheme.Modules.pullback σ).obj (tautologicalDatumTwist F)) ≅
      pullbackTwist _ (chartFactor _ (localDegreeOne V m₀).2 h hg) 1 :=
  (Scheme.Modules.pullbackComp V.ι σ).app _ ≪≫
    (Scheme.Modules.pullbackCongr hcs).app _ ≪≫
    chartFactorisationPullbackTwistIso V hV τ h hgh hg

/-- **The object half of the local classifying datum of the glued section**, which is
`restrictChartFactorisationPullbackTwistIso` at `σ = Stacks.RelativeProj.globalSection q` and the
restriction `Stacks.RelativeProj.ι_comp_globalSection_eq_localSection`. -/
public def globalSectionPullbackTwistIsoOnCover (q : F ⟶ L) [Epi q] (V : TrivAffineOpens L)
    (e : L.over V.1.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over V.1.1))
    (hq : Function.Surjective (q.val.app (op V.1.1))) {m₀ : Γ(F, V.1.1)}
    (hg : localChartMap V.1.1 q e hq ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V.1.1)
        (localDegreeOne V.1.1 m₀).1 = ⊤) :
    (Scheme.Modules.pullback V.1.1.ι).obj
        ((Scheme.Modules.pullback (globalSection q)).obj (tautologicalDatumTwist F)) ≅
      pullbackTwist _
        (chartFactor _ (localDegreeOne V.1.1 m₀).2 (localChartMap V.1.1 q e hq) hg) 1 :=
  restrictChartFactorisationPullbackTwistIso V.1.1 V.1.2 (globalSection q)
    (localSection V.1.1 q e V.1.2 hq) (ι_comp_globalSection_eq_localSection q V e hq)
    (localChartMap V.1.1 q e hq)
    (localSection_comp_bundlePresentationIso_inv V.1.1 q e V.1.2 hq) hg

/-- **The object half of the local classifying datum, with the frame produced rather than
assumed.** The frame is supplied by
`Stacks.RelativeProj.exists_resT_pullbackDegreeSection_localChartMap`, whose only hypothesis is
the surjectivity of `q` on sections over the member — which
`Stacks.RelativeProj.surjective_app_of_isAffineOpen_of_epi` gives from `Epi q` and affineness
alone. So over every member of `Stacks.RelativeProj.trivCover` the object comparison exists with
no input from the consumer, together with the pinning identity on the target. -/
public theorem exists_globalSectionPullbackTwistIsoOnCover (q : F ⟶ L) [Epi q]
    (V : TrivAffineOpens L) :
    ∃ (e : L.over V.1.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over V.1.1))
      (hq : Function.Surjective (q.val.app (op V.1.1))) (m₀ : Γ(F, V.1.1))
      (hg : localChartMap V.1.1 q e hq ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
          ((schemeSheafGradedAlgebra F
            (isQuasicoherentPieces_of_isQuasicoherent F)).grading V.1.1)
          (localDegreeOne V.1.1 m₀).1 = ⊤),
      Nonempty ((Scheme.Modules.pullback V.1.1.ι).obj
          ((Scheme.Modules.pullback (globalSection q)).obj (tautologicalDatumTwist F)) ≅
        pullbackTwist _
          (chartFactor _ (localDegreeOne V.1.1 m₀).2 (localChartMap V.1.1 q e hq) hg) 1) := by
  refine ⟨V.2.some, surjective_app_of_isAffineOpen_of_epi q V.1.2, ?_⟩
  obtain ⟨m₀, hg, -⟩ := exists_resT_pullbackDegreeSection_localChartMap V.1.1 q V.2.some
    (surjective_app_of_isAffineOpen_of_epi q V.1.2)
  exact ⟨m₀, hg, ⟨globalSectionPullbackTwistIsoOnCover q V V.2.some _ hg⟩⟩

end CoverTwist

/-! ### The pulled-back tautological map, on sections -/

section OnSections

open Opposite
open Stacks.SymGraded

/-- **A section of `p` collapses the preimage of an open to that open.** `σ ⁻¹ᵁ (p ⁻¹ᵁ W)` is
`(σ ≫ p) ⁻¹ᵁ W` definitionally and `(𝟙 X) ⁻¹ᵁ W` is `W` definitionally, so the whole content is
`σ ≫ p = 𝟙 X`; the equation itself is *not* definitional, and it is what every statement below
needs in order to read a section over `σ ⁻¹ᵁ (p ⁻¹ᵁ W)` as a section over `W`. -/
public theorem preimage_preimage_of_comp_eq_id {S P : Scheme.{u}} (p : P ⟶ S) (σ : S ⟶ P)
    (hσ : σ ≫ p = 𝟙 S) (W : S.Opens) : σ ⁻¹ᵁ (p ⁻¹ᵁ W) = W :=
  congrArg (fun k : S ⟶ S => k ⁻¹ᵁ W) hσ

/-- **The inverse of the identity comparison, on a section.** It is the pullback of the section
along `𝟙 S` to the open it already lives on.

This is `CategoryTheory.unit_conjugateEquiv` at
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackId_hom`, which identifies the `hom` of
the comparison with the inverse of the adjunction unit, together with the observation that the
restriction `AlgebraicGeometry.Scheme.Modules.pullbackSection` interposes is along the identity
of `(𝟙 S) ⁻¹ᵁ W = W`. -/
public theorem pullbackSection_pullbackId_inv {S : Scheme.{u}} (M : S.Modules) (W : S.Opens)
    (m : Γ(M, W)) :
    ((Scheme.Modules.pullbackId S).inv.app M).val.app (op W) m
      = Scheme.Modules.pullbackSection (𝟙 S) M W W le_rfl m := by
  have hop : (homOfLE (le_rfl : W ≤ (𝟙 S) ⁻¹ᵁ W)).op = 𝟙 (op W) := Subsingleton.elim _ _
  have hsec : Scheme.Modules.pullbackSection (𝟙 S) M W W le_rfl m
      = ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 S)).unit.app M).val.app (op W) m := by
    refine Eq.trans (congrArg (fun k => ((Scheme.Modules.pullback (𝟙 S)).obj M).val.map k
        (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 S)).unit.app M).val.app (op W) m))
      hop) ?_
    exact PresheafOfModules.map_id_apply _ _ _
  have hunit : ((Scheme.Modules.pullbackId S).hom.app M).val.app (op W)
      (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 S)).unit.app M).val.app (op W) m)
        = m := by
    have h := CategoryTheory.unit_conjugateEquiv CategoryTheory.Adjunction.id
      (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 S))
      (Scheme.Modules.pullbackId S).hom M
    rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
    exact (congrArg (fun t => t.val.app (op W) m) h).symm
  refine Eq.trans (congrArg (fun z => ((Scheme.Modules.pullbackId S).inv.app M).val.app (op W) z)
    ((congrArg (fun z => ((Scheme.Modules.pullbackId S).hom.app M).val.app (op W) z)
      hsec).trans hunit).symm) ?_
  exact congrArg (fun k : (Scheme.Modules.pullback (𝟙 S)).obj M ⟶
        (Scheme.Modules.pullback (𝟙 S)).obj M =>
      k.val.app (op W) (Scheme.Modules.pullbackSection (𝟙 S) M W W le_rfl m))
    ((Scheme.Modules.pullbackId S).hom_inv_id_app M)

/-- Splitting a section pulled back along a composite, via the inverse comparison. -/
private theorem pullbackComp_inv_pullbackSection_aux {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W)
    (M : W.Modules) (U : W.Opens) (T : Z.Opens) (V : Y.Opens) (hg : T ≤ g ⁻¹ᵁ U)
    (hf : V ≤ f ⁻¹ᵁ T) (h : V ≤ (f ≫ g) ⁻¹ᵁ U) (a : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).val.app (op V)
        (Scheme.Modules.pullbackSection (f ≫ g) M U V h a)
      = Scheme.Modules.pullbackSection f ((Scheme.Modules.pullback g).obj M) T V hf
          (Scheme.Modules.pullbackSection g M U T hg a) :=
  (congrArg
      (fun z : Γ((Scheme.Modules.pullback (f ≫ g)).obj M, V) =>
        ((Scheme.Modules.pullbackComp f g).inv.app M).val.app (op V) z)
      (Scheme.Modules.pullbackSection_comp f g M U T V hg hf h a)).symm.trans
    (congrArg
      (fun φ : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ⟶
          (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) =>
        φ.val.app (op V)
          (Scheme.Modules.pullbackSection f ((Scheme.Modules.pullback g).obj M) T V hf
            (Scheme.Modules.pullbackSection g M U T hg a)))
      ((Scheme.Modules.pullbackComp f g).hom_inv_id_app M))

/-- **A factorisation `g ≫ p = q` carried across the two comparisons it induces and then along a
morphism out of `p^*M`, on a section.** The composite
`pullbackCongr`-`pullbackComp`-`pullback g`-of-`t` sends the pullback of `m` along `q` to the
pullback along `g` of the value of `t` at the pullback of `m` along `p`.

This is the shape `Stacks.RelativeProj.tautologicalDatumUniv` is literally in, so that statement
is an instance of this one with nothing to re-associate. The two comparisons are cancelled
forwards against `AlgebraicGeometry.Scheme.Modules.pullbackSection_congr` and
`AlgebraicGeometry.Scheme.Modules.pullbackSection_comp`, and the last leg is
`AlgebraicGeometry.Scheme.Modules.pullbackSection_naturality`. -/
public theorem pullbackSection_pullbackCongrComp_inv_map {S T P : Scheme.{u}} (g : T ⟶ P)
    (p : P ⟶ S) (q : T ⟶ S) (hgp : g ≫ p = q) {M : S.Modules} {N : P.Modules}
    (t : (Scheme.Modules.pullback p).obj M ⟶ N) (U : S.Opens) (V : T.Opens)
    (hq : V ≤ q ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ (p ⁻¹ᵁ U)) (m : Γ(M, U)) :
    ((Scheme.Modules.pullbackCongr hgp).inv.app M ≫
        (Scheme.Modules.pullbackComp g p).inv.app M ≫
          (Scheme.Modules.pullback g).map t).val.app (op V)
        (Scheme.Modules.pullbackSection q M U V hq m)
      = Scheme.Modules.pullbackSection g N (p ⁻¹ᵁ U) V hg
          (t.val.app (op (p ⁻¹ᵁ U))
            (Scheme.Modules.pullbackSection p M U (p ⁻¹ᵁ U) le_rfl m)) := by
  have hcongr : ((Scheme.Modules.pullbackCongr hgp).inv.app M).val.app (op V)
      (Scheme.Modules.pullbackSection q M U V hq m)
        = Scheme.Modules.pullbackSection (g ≫ p) M U V hg m := by
    subst hgp
    rfl
  have hcomp := pullbackComp_inv_pullbackSection_aux g p M U (p ⁻¹ᵁ U) V le_rfl hg hg m
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ (op V) _) ?_
  refine Eq.trans (congrArg (fun z => ((Scheme.Modules.pullbackComp g p).inv.app M ≫
      (Scheme.Modules.pullback g).map t).val.app (op V) z) hcongr) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ (op V) _) ?_
  refine Eq.trans (congrArg
    (fun z => ((Scheme.Modules.pullback g).map t).val.app (op V) z) hcomp) ?_
  exact Scheme.Modules.pullbackSection_naturality g t (p ⁻¹ᵁ U) V hg
    (Scheme.Modules.pullbackSection p M U (p ⁻¹ᵁ U) le_rfl m)

/-- **The three structural comparisons supplied by a section `σ ≫ p = 𝟙 S`, followed by a
morphism out of `p^*M`, on a section.** At `m : Γ(M, W)` the composite is the pullback along `σ`
of the value of `t` at the pullback of `m` along `p`.

This is the shape `Stacks.RelativeProj.TautologicalDatum.pullbackQuotientMap` is literally in.
Nothing of the projective bundle enters: `p` is an arbitrary morphism of schemes and `σ` an
arbitrary section of it. -/
public theorem pullbackSection_sectionComparisons_map {S P : Scheme.{u}} (p : P ⟶ S) (σ : S ⟶ P)
    (hσ : σ ≫ p = 𝟙 S) {M : S.Modules} {N : P.Modules}
    (t : (Scheme.Modules.pullback p).obj M ⟶ N) (W : S.Opens) (hW : W ≤ σ ⁻¹ᵁ (p ⁻¹ᵁ W))
    (m : Γ(M, W)) :
    ((Scheme.Modules.pullbackId S).inv.app M ≫
        (Scheme.Modules.pullbackCongr hσ).inv.app M ≫
          (Scheme.Modules.pullbackComp σ p).inv.app M ≫
            (Scheme.Modules.pullback σ).map t).val.app (op W) m
      = Scheme.Modules.pullbackSection σ N (p ⁻¹ᵁ W) W hW
          (t.val.app (op (p ⁻¹ᵁ W))
            (Scheme.Modules.pullbackSection p M W (p ⁻¹ᵁ W) le_rfl m)) := by
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ (op W) m) ?_
  refine Eq.trans (congrArg (fun z => ((Scheme.Modules.pullbackCongr hσ).inv.app M ≫
      (Scheme.Modules.pullbackComp σ p).inv.app M ≫
        (Scheme.Modules.pullback σ).map t).val.app (op W) z)
    (pullbackSection_pullbackId_inv M W m)) ?_
  exact pullbackSection_pullbackCongrComp_inv_map σ p (𝟙 S) hσ t W W le_rfl hW m

/-- **A factorisation `c ≫ σ = τ` carried forwards across the two comparisons it induces, on a
twice-pulled-back section.** The composite `pullbackComp`-`pullbackCongr` sends the pullback
along `c` of the pullback along `σ` of `a` to the pullback of `a` along `τ`.

This is the companion of `pullbackSection_pullbackCongrComp_inv_map` with both comparisons taken
in the `hom` direction and in the opposite order, which is the order the *object* comparison
`Stacks.RelativeProj.globalSectionPullbackTwistIsoOnCover` composes them in: the restriction of
a glued section to a member of the cover is read by `pullbackComp` followed by the
`pullbackCongr` of `Stacks.RelativeProj.ι_comp_globalSection_eq_localSection`, and the twist
comparison `Stacks.RelativeProj.localSectionTwistIso` opens with the same pair at
`bundlePresentationIso.inv`. Stated with the three morphisms of schemes as *variables*, so that
each specialisation is a bare `exact` and the chart layer of the bundle is never unfolded. -/
public theorem pullbackSection_compCongr_map {S P T : Scheme.{u}} (c : T ⟶ S) (σ : S ⟶ P)
    (τ : T ⟶ P) (hcs : c ≫ σ = τ) (M : P.Modules) (U : P.Opens) (W : S.Opens) (V : T.Opens)
    (hW : W ≤ σ ⁻¹ᵁ U) (hV : V ≤ c ⁻¹ᵁ W) (hτ : V ≤ τ ⁻¹ᵁ U) (a : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp c σ).hom.app M ≫
          (Scheme.Modules.pullbackCongr hcs).hom.app M).val.app (op V)
        (Scheme.Modules.pullbackSection c ((Scheme.Modules.pullback σ).obj M) W V hV
          (Scheme.Modules.pullbackSection σ M U W hW a))
      = Scheme.Modules.pullbackSection τ M U V hτ a := by
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ (op V) _) ?_
  refine Eq.trans (congrArg
    (fun z => ((Scheme.Modules.pullbackCongr hcs).hom.app M).val.app (op V) z)
    (Scheme.Modules.pullbackSection_comp c σ M U W V hW hV
      (hV.trans (c.preimage_mono hW)) a)) ?_
  exact Scheme.Modules.pullbackSection_congr hcs M U V (hV.trans (c.preimage_mono hW)) hτ a

/-- **The composite comparison turned around, on a section pulled back along the composite.**
`AlgebraicGeometry.Scheme.Modules.pullbackSection_comp` is stated with the `hom` of
`AlgebraicGeometry.Scheme.Modules.pullbackComp`, whereas
`Stacks.RelativeProj.localSectionTwistIso` composes its `inv`: the chart comparison
`Stacks.ProjectiveBundle.chartTwistIso` lives under *two* pullbacks and the single pullback along
the composite has to be split before it can be reached. Turning the comparison around rather than
inverting by injectivity is one use of `CategoryTheory.Iso.hom_inv_id_app`. -/
public theorem pullbackComp_inv_pullbackSection {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W)
    (M : W.Modules) (U : W.Opens) (T : Z.Opens) (V : Y.Opens) (hg : T ≤ g ⁻¹ᵁ U)
    (hf : V ≤ f ⁻¹ᵁ T) (h : V ≤ (f ≫ g) ⁻¹ᵁ U) (a : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).val.app (op V)
        (Scheme.Modules.pullbackSection (f ≫ g) M U V h a)
      = Scheme.Modules.pullbackSection f ((Scheme.Modules.pullback g).obj M) T V hf
          (Scheme.Modules.pullbackSection g M U T hg a) :=
  pullbackComp_inv_pullbackSection_aux f g M U T V hg hf h a

/-- **Pulling a global section back to an open is restricting its pullback.** The two
restrictions interposed by `AlgebraicGeometry.Scheme.Modules.pullbackSection` compose, and the
two inclusions are proofs of one proposition.

This is the dictionary entry between the shape the twist comparisons produce — a
`AlgebraicGeometry.Scheme.Modules.pullbackSection` over an open of the member — and the shape the
pinning match of `Stacks.RelativeProj.resT_pullbackDegreeSection_localChartMap` and
`Stacks.AlgebraicGeometry.ProjTwistPinnedChart.pinnedFrameIso_inv_smul_resT` are stated in, which
is `Stacks.ProjectiveFromSections.resT` of a global section. -/
public theorem pullbackSection_top_eq_resT {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : Z.Modules)
    (U : Y.Opens) (hU : U ≤ f ⁻¹ᵁ (⊤ : Z.Opens)) (ht : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ (⊤ : Z.Opens))
    (a : Γ(M, (⊤ : Z.Opens))) :
    Scheme.Modules.pullbackSection f M ⊤ U hU a =
      Stacks.ProjectiveFromSections.resT U
        (Scheme.Modules.pullbackSection f M ⊤ ⊤ ht a) :=
  (Stacks.Chow.GenuineChern.map_map_homOfLE ((Scheme.Modules.pullback f).obj M)
    (le_top : U ≤ ⊤) ht _).symm

/-- **The pulled-back degree-`d` section is the pullback of the degree-`d` section**, in the
`AlgebraicGeometry.Scheme.Modules.pullbackSection` spelling the twist comparisons produce. True
by `rfl`; it is named because
`Stacks.AlgebraicGeometry.ProjChartAlphaInstance.pullbackDegreeSection` is written with
`AlgebraicGeometry.pullbackSectionHom`, and nothing said the two agree. -/
public theorem pullbackDegreeSection_eq_pullbackSection {Y : Scheme.{u}} {ι' : Type u}
    {A : Type u} [CommRing A] [SetLike ι' A] [AddSubgroupClass ι' A] (𝒜 : ℕ → ι')
    [GradedRing 𝒜] {d : ℕ} (φ : Y ⟶ (AlgebraicGeometry.Proj.degreeOpen 𝒜 d).toScheme)
    (f : 𝒜 d) (ht : (⊤ : Y.Opens) ≤
      Stacks.AlgebraicGeometry.MorphismsIntoProj.toProj 𝒜 φ ⁻¹ᵁ
        (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens)) :
    Stacks.AlgebraicGeometry.ProjChartAlphaInstance.pullbackDegreeSection 𝒜 φ f =
      Scheme.Modules.pullbackSection
        (Stacks.AlgebraicGeometry.MorphismsIntoProj.toProj 𝒜 φ)
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf 𝒜 (d : ℤ)) ⊤ ⊤ ht
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒜 d f) :=
  rfl

/-- **The pulled-back tautological quotient map of a tautological datum, on sections.** At a
section `m` of `ℰ` over an open `W` of the base, the value of
`Stacks.RelativeProj.TautologicalDatum.pullbackQuotientMap` is the pullback along `σ` of the
value of the datum's universal surjection at the pullback of `m` along `π`.

**This is the statement the remaining work on [Stacks, Tag 0B3V]'s bijection was owed**: the
local classifying datum of `exists_classifies_of_pullback_cover` asks that the object comparison
`globalSectionPullbackTwistIsoOnCover` carry the pulled-back tautological map to `q`, and nothing
above evaluated that map past its three `AlgebraicGeometry.Scheme.Modules.pullback` comparisons.
See `Not done here` for what is still owed after it. -/
public theorem TautologicalDatum.pullbackQuotientMap_val_app (D : TautologicalDatum X F)
    (σ : X ⟶ projectiveBundle X F) (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
    (W : X.Opens) (hW : W ≤ σ ⁻¹ᵁ (projectiveBundleToBase X F ⁻¹ᵁ W)) (m : Γ(F, W)) :
    (D.pullbackQuotientMap σ hσ).val.app (op W) m =
      Scheme.Modules.pullbackSection σ D.twist (projectiveBundleToBase X F ⁻¹ᵁ W) W hW
        (D.univ.val.app (op (projectiveBundleToBase X F ⁻¹ᵁ W))
          (Scheme.Modules.pullbackSection (projectiveBundleToBase X F) F W
            (projectiveBundleToBase X F ⁻¹ᵁ W) le_rfl m)) :=
  pullbackSection_sectionComparisons_map (projectiveBundleToBase X F) σ hσ D.univ W hW m

/-- **The comparison of the two bundle substrates lies over the base, read on preimages.** The
preimage along `bundlePresentationIso.inv` of the preimage of `W` under the projection of the
`SheafGradedAlgebra` presentation is the preimage of `W` under `π`. -/
public theorem preimage_bundlePresentationIso_inv_preimage_toBase (W : X.Opens) :
    (bundlePresentationIso F).inv ⁻¹ᵁ ((symGradedBundle F).toBase ⁻¹ᵁ W)
      = projectiveBundleToBase X F ⁻¹ᵁ W :=
  congrArg (fun k : projectiveBundle X F ⟶ X => k ⁻¹ᵁ W)
    (bundlePresentationIso_inv_comp_toBase F)

/-- **The universal surjection of `Stacks.RelativeProj.tautologicalDatum`, on sections.** Its
value at the pullback of `m` along `π` is the pullback along `bundlePresentationIso.inv` of the
value of `Stacks.ProjectiveBundleSplitting.tautologicalMap` at the pullback of `m` along the
projection of the other presentation.

So the `bundlePresentationIso` transport that separated
`Stacks.ProjectiveBundleConormal.projectiveBundle_chartTwistIso_hom_pullbackSection` from the
datum of `Stacks.RelativeProj.tautologicalDatum` is discharged on sections. -/
public theorem tautologicalDatumUniv_val_app (W : X.Opens)
    (hb : projectiveBundleToBase X F ⁻¹ᵁ W ≤
      (bundlePresentationIso F).inv ⁻¹ᵁ ((symGradedBundle F).toBase ⁻¹ᵁ W)) (m : Γ(F, W)) :
    (tautologicalDatumUniv F).val.app (op (projectiveBundleToBase X F ⁻¹ᵁ W))
        (Scheme.Modules.pullbackSection (projectiveBundleToBase X F) F W
          (projectiveBundleToBase X F ⁻¹ᵁ W) le_rfl m)
      = Scheme.Modules.pullbackSection (bundlePresentationIso F).inv
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
            (isQuasicoherentPieces_of_isQuasicoherent F))
          ((symGradedBundle F).toBase ⁻¹ᵁ W) (projectiveBundleToBase X F ⁻¹ᵁ W) hb
          ((Stacks.ProjectiveBundleSplitting.tautologicalMap F
              (isQuasicoherentPieces_of_isQuasicoherent F)).val.app
            (op ((symGradedBundle F).toBase ⁻¹ᵁ W))
            (Scheme.Modules.pullbackSection (symGradedBundle F).toBase F W
              ((symGradedBundle F).toBase ⁻¹ᵁ W) le_rfl m)) :=
  pullbackSection_pullbackCongrComp_inv_map (bundlePresentationIso F).inv
    (symGradedBundle F).toBase (projectiveBundleToBase X F)
    (bundlePresentationIso_inv_comp_toBase F)
    (Stacks.ProjectiveBundleSplitting.tautologicalMap F
      (isQuasicoherentPieces_of_isQuasicoherent F))
    W (projectiveBundleToBase X F ⁻¹ᵁ W) le_rfl hb m

/-- **The tautological map of `𝐏(ℰ)` pulled back along a section, on sections, past all six
comparisons.** At `m : Γ(ℰ, W)` the value of
`Stacks.RelativeProj.TautologicalDatum.pullbackQuotientMap` at the repository's own tautological
datum is the pullback along `σ` of the pullback along `bundlePresentationIso.inv` of the value of
`Stacks.ProjectiveBundleSplitting.tautologicalMap` at the pullback of `m` along the projection of
the `SheafGradedAlgebra` presentation.

The right-hand side is the section that
`Stacks.ProjectiveBundleConormal.projectiveBundle_chartTwistIso_hom_pullbackSection` computes
through `Stacks.ProjectiveBundle.chartTwistIso`, which is the comparison
`Stacks.RelativeProj.localSectionTwistIso` is built from. -/
public theorem pullbackQuotientMap_tautologicalDatum_val_app
    (σ : X ⟶ projectiveBundle X F) (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
    (W : X.Opens) (hW : W ≤ σ ⁻¹ᵁ (projectiveBundleToBase X F ⁻¹ᵁ W))
    (hb : projectiveBundleToBase X F ⁻¹ᵁ W ≤
      (bundlePresentationIso F).inv ⁻¹ᵁ ((symGradedBundle F).toBase ⁻¹ᵁ W)) (m : Γ(F, W)) :
    ((tautologicalDatum F).pullbackQuotientMap σ hσ).val.app (op W) m =
      Scheme.Modules.pullbackSection σ (tautologicalDatumTwist F)
        (projectiveBundleToBase X F ⁻¹ᵁ W) W hW
        (Scheme.Modules.pullbackSection (bundlePresentationIso F).inv
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
            (isQuasicoherentPieces_of_isQuasicoherent F))
          ((symGradedBundle F).toBase ⁻¹ᵁ W) (projectiveBundleToBase X F ⁻¹ᵁ W) hb
          ((Stacks.ProjectiveBundleSplitting.tautologicalMap F
              (isQuasicoherentPieces_of_isQuasicoherent F)).val.app
            (op ((symGradedBundle F).toBase ⁻¹ᵁ W))
            (Scheme.Modules.pullbackSection (symGradedBundle F).toBase F W
              ((symGradedBundle F).toBase ⁻¹ᵁ W) le_rfl m))) :=
  ((tautologicalDatum F).pullbackQuotientMap_val_app σ hσ W hW m).trans
    (congrArg (fun z => Scheme.Modules.pullbackSection σ (tautologicalDatumTwist F)
        (projectiveBundleToBase X F ⁻¹ᵁ W) W hW z)
      (tautologicalDatumUniv_val_app W hb m))

end OnSections

/-! ### The trivialisation of the inverse image, carrying `q` to the trivialised quotient -/

section TrivBridge

open Opposite
open Stacks.AlgebraicGeometry.ProjF1Dehomogenization
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne (unitSection)

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

omit [F.IsQuasicoherent]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] in
/-- **The trivialisation of the inverse image of `ℒ` over `V` carries the inverse image of `q` to
`Stacks.RelativeProj.trivializedQuotientHom`.**

Over a trivialising open `V` the local classifying datum has to compare two trivialisations of
the inverse image of `ℒ`: the one the cover member carries, which lives on the *restricted site*
`Over V`, and the frame of the pulled-back twist, which lives on the open subscheme. The object
comparison is `Stacks.AlgebraicGeometry.ProjInvertibleLocus.pullbackIsoUnitOfOverIsoUnit`; this
is that comparison read on sections, and it lands exactly on the morphism
`κ : ℰ ⟶ (V.ι)_*𝒪_V` the pinning match of
`Stacks.RelativeProj.resT_pullbackDegreeSection_localChartMap` is stated in terms of.

Three steps and no new mathematics:
`AlgebraicGeometry.Scheme.Modules.unit_app_val_app_naturality` moves `q` past the adjunction
unit, `Stacks.Chow.GenuineChern.restrictFunctorIsoPullback_inv_unitSection` evaluates the
comparison of the two restriction functors on a pulled-back section, and
`Stacks.RelativeProj.ofPushforwardUnit_trivializedQuotientHom_app` — which is `rfl` — says the
result is `κ`. -/
public theorem pullbackIsoUnitOfOverIsoUnit_hom_pullback_map_unitSection (V : X.Opens)
    (q : F ⟶ L) (e : L.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V)) (x : Γ(F, V)) :
    (pullbackIsoUnitOfOverIsoUnit V L e).hom.val.app (op (V.ι ⁻¹ᵁ V))
        (((Scheme.Modules.pullback V.ι).map q).val.app (op (V.ι ⁻¹ᵁ V))
          (unitSection V.ι F V x))
      = ofPushforwardUnit V.ι ((trivializedQuotientHom V q e).val.app (op V) x) := by
  refine Eq.trans (congrArg
    (fun z => (pullbackIsoUnitOfOverIsoUnit V L e).hom.val.app (op (V.ι ⁻¹ᵁ V)) z)
    (Scheme.Modules.unit_app_val_app_naturality V.ι q V x)) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ (op (V.ι ⁻¹ᵁ V)) _) ?_
  refine Eq.trans (congrArg
    (fun z => (restrictIsoUnitOfOverIsoUnit V L e).hom.val.app (op (V.ι ⁻¹ᵁ V)) z)
    (Stacks.Chow.GenuineChern.restrictFunctorIsoPullback_inv_unitSection V.ι L V
      (q.val.app (op V) x))) ?_
  exact congrArg
    (fun z => (restrictIsoUnitOfOverIsoUnit V L e).hom.val.app (op (V.ι ⁻¹ᵁ V)) z)
    (PresheafOfModules.naturality_apply q.val (homOfLE (V.ι.image_preimage_le V)).op x).symm

omit [F.IsQuasicoherent]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] in
/-- **The `ℒ` side of the local classifying datum, on a pulled-back section.** The inverse image
of `q` followed by the trivialisation of the inverse image of `ℒ` sends the pullback of `x` to
the trivialised quotient of `x`. This is
`pullbackIsoUnitOfOverIsoUnit_hom_pullback_map_unitSection` read on the composite. -/
public theorem pullback_map_comp_pullbackIsoUnitOfOverIsoUnit_hom_unitSection (V : X.Opens)
    (q : F ⟶ L) (e : L.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V)) (x : Γ(F, V)) :
    ((Scheme.Modules.pullback V.ι).map q ≫
          (pullbackIsoUnitOfOverIsoUnit V L e).hom).val.app
        (op (V.ι ⁻¹ᵁ V)) (unitSection V.ι F V x)
      = ofPushforwardUnit V.ι ((trivializedQuotientHom V q e).val.app (op V) x) :=
  (SheafOfModules.comp_val_app_apply _ _ (op (V.ι ⁻¹ᵁ V)) _).trans
    (pullbackIsoUnitOfOverIsoUnit_hom_pullback_map_unitSection V q e x)

end TrivBridge

end Stacks.RelativeProj

end
