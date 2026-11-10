module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.LowerShriekCovariance
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceProperIso
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekComparison
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpens
public import StacksFrontier.AlgebraicGeometry.Duality.GlueingDualizingComplexesStandardModel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `f_new^!` of a proper morphism

In Situation [Stacks, Tag 0AU4], let `f : X ⟶ Y` be a proper morphism of schemes of finite type
over `S` and `ω_X^•`, `ω_Y^•` the dualizing complexes normalized relative to `ω_S^•`. Part (6)
of [Stacks, Tag 0AUE]: `f_new^!` is the restriction to `D^+_Coh(𝒪_Y)` of the right adjoint `a`
of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, and

`Rf_* R𝓗om(K, f_new^! M) ≅ R𝓗om(Rf_* K, M)`, `Rf_* R𝓗om(K, ω_X^•) ≅ R𝓗om(Rf_* K, ω_Y^•)`

for `K ∈ D^-_Coh(𝒪_X)` and `M ∈ D^+_Coh(𝒪_Y)`.

## Main definitions

* `Stacks.Duality.UpperShriekDuality.upperShriekStdIsoRightAdjointOfIsProper` — `f^! ≅ a` on
  `D^+_Coh`, at the standard model, for any compactification.
* `Stacks.Duality.NormalizedOnOpens.fNewShriekIsoRightAdjointOfIsProper` — the first assertion
  of part (6).

## References

* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
* [Stacks Project, Tag 0GEW](https://stacks.math.columbia.edu/tag/0GEW)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality

open Stacks.Duality.TwistedInverseImageDuality (Std sheafHom pull push comparison plusCoh qcoh
  rightAdjointStd plusCoh_le_qcoh)

namespace UpperShriekDuality

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y) [IsProper f.left]

/-- **`f^! = a` on `D^+_Coh` for a proper morphism**, at the standard model: for every
compactification `j`, `f^!` is the right adjoint `a` of `Rf_*` ([Stacks, Tag 0AA0] and the
definition of [Stacks, Tag 0A9Y]). -/
def upperShriekStdIsoRightAdjointOfIsProper (j : CompactificationOf (Over.mk f.left)) :
    upperShriekStd f j ≅ ObjectProperty.ιOfLE plusCoh_le_qcoh ⋙ rightAdjointStd f.left :=
  upperShriekStdCompactificationIso f j (properCompactification f) ≪≫
    upperShriekStdIso f (properCompactification f) ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ιOfLE plusCoh_le_qcoh ⋙ rightAdjointStd f.left)
      (pullIdIso X.left) ≪≫ Functor.rightUnitor _

end UpperShriekDuality

/-! ### The right adjoint of `Rf_*` at the standard model, and its sheafy trace -/

/-- For a quasi-compact quasi-separated morphism `f : X ⟶ Y` of quasi-compact quasi-separated
schemes, `rightAdjointStd f` sends a complex with quasi-coherent cohomology to one with
quasi-coherent cohomology. -/
theorem qcoh_rightAdjointStd_obj {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (M : (qcoh Y).FullSubcategory) :
    qcoh X ((rightAdjointStd f).obj M) :=
  ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
    ⟨(comparison Y).functor.obj M.obj, M.property⟩).property

section Trace

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi
open TwistedInverseImageDuality (qcoh_iff_isDQCoh adjunctionHomEquiv
  adjunctionHomEquiv_naturality_left adjunctionHomEquiv_naturality_right)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian X] [IsNoetherian Y] [IsProper f]

omit [AlgebraicGeometry.IsNoetherian X] [IsProper f] in
/-- A dualizing complex is bounded below, at the standard model. -/
theorem isBoundedBelow_of_isDualizing_std {K : Std Y}
    (hK : TwistedInverseImageDuality.IsDualizing K) : DerivedCategoryB.IsBoundedBelow K :=
  isBoundedBelow_of_isDualizingComplex _ hK

/-- An object of `D_QCoh(𝒪_Y)` at the standard model, as an object of `qcoh Y`. -/
abbrev toQCohStd (M : quasiCoherentDerivedCategory Y) : (qcoh Y).FullSubcategory :=
  ⟨M.obj, (qcoh_iff_isDQCoh M.obj).2 M.property⟩

/-- The right adjoint `a` of `Rf_*` of [Stacks, Tag 0A9E], read at the standard model
(`Stacks.Duality.TwistedInverseImageDuality.rightAdjointStd`), as a functor between the
quasi-coherent derived categories of the standard model. -/
def rightAdjointQCohStd : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X :=
  ObjectProperty.lift _ (ObjectProperty.lift (qcoh Y) (ObjectProperty.ι _)
      (fun M => (qcoh_iff_isDQCoh M.obj).2 M.property) ⋙ rightAdjointStd f)
    (fun M => (qcoh_iff_isDQCoh _).1 (qcoh_rightAdjointStd_obj f (toQCohStd M)))

/-- The adjunction bijection `(Rf_* F ⟶ M) ≃ (F ⟶ a M)` of [Stacks, Tag 0A9E] between the
quasi-coherent derived categories of the standard model. -/
@[sga "5 III 6.1" "partial"]
def rightAdjointQCohStdHomEquiv (F : quasiCoherentDerivedCategory X)
    (M : quasiCoherentDerivedCategory Y) :
    ((quasiCoherentDerivedPushforward f
        (StandardModel.isQuasicoherent_homology_derivedPushforward f)).obj F ⟶ M) ≃
      (F ⟶ (rightAdjointQCohStd f).obj M) :=
  ((ObjectProperty.fullyFaithfulι _).homEquiv.trans
    (adjunctionHomEquiv f (toQCohStd M) F.obj ((qcoh_iff_isDQCoh F.obj).2 F.property))).trans
    (ObjectProperty.fullyFaithfulι _).homEquiv.symm

/-- The underlying morphism of `rightAdjointQCohStdHomEquiv f F M k` is the image of `k` under
`adjunctionHomEquiv`. -/
theorem rightAdjointQCohStdHomEquiv_hom (F : quasiCoherentDerivedCategory X)
    (M : quasiCoherentDerivedCategory Y)
    (k : (quasiCoherentDerivedPushforward f
        (StandardModel.isQuasicoherent_homology_derivedPushforward f)).obj F ⟶ M) :
    (rightAdjointQCohStdHomEquiv f F M k).hom =
      adjunctionHomEquiv f (toQCohStd M) F.obj ((qcoh_iff_isDQCoh F.obj).2 F.property) k.hom :=
  rfl

/-- `rightAdjointQCohStdHomEquiv` is natural in the source: precomposing with `Rf_* g` corresponds
to precomposing with `g`. -/
theorem rightAdjointQCohStdHomEquiv_naturality_left {F F' : quasiCoherentDerivedCategory X}
    (M : quasiCoherentDerivedCategory Y) (g : F' ⟶ F)
    (k : (quasiCoherentDerivedPushforward f
        (StandardModel.isQuasicoherent_homology_derivedPushforward f)).obj F ⟶ M) :
    rightAdjointQCohStdHomEquiv f F' M
        ((quasiCoherentDerivedPushforward f
          (StandardModel.isQuasicoherent_homology_derivedPushforward f)).map g ≫ k) =
      g ≫ rightAdjointQCohStdHomEquiv f F M k := by
  ext
  exact adjunctionHomEquiv_naturality_left f (toQCohStd M)
    ((qcoh_iff_isDQCoh F.obj).2 F.property) ((qcoh_iff_isDQCoh F'.obj).2 F'.property) g.hom k.hom

/-- `rightAdjointQCohStdHomEquiv` is natural in the target: postcomposing with `φ` corresponds to
postcomposing with `a(φ)`. -/
theorem rightAdjointQCohStdHomEquiv_naturality_right (F : quasiCoherentDerivedCategory X)
    {M M' : quasiCoherentDerivedCategory Y} (φ : M ⟶ M')
    (k : (quasiCoherentDerivedPushforward f
        (StandardModel.isQuasicoherent_homology_derivedPushforward f)).obj F ⟶ M) :
    rightAdjointQCohStdHomEquiv f F M' (k ≫ φ) =
      rightAdjointQCohStdHomEquiv f F M k ≫ (rightAdjointQCohStd f).map φ := by
  ext
  exact adjunctionHomEquiv_naturality_right f
    (ObjectProperty.homMk φ.hom : toQCohStd M ⟶ toQCohStd M') F.obj
    ((qcoh_iff_isDQCoh F.obj).2 F.property) k.hom

/-- `Rf_* ⊣ a` at the standard model, for `a = rightAdjointQCohStd f`. -/
def rightAdjointQCohStdAdjunction :
    quasiCoherentDerivedPushforward f
        (StandardModel.isQuasicoherent_homology_derivedPushforward f) ⊣
      rightAdjointQCohStd f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := rightAdjointQCohStdHomEquiv f
      homEquiv_naturality_left_symm := fun {F F'} M g h => by
        rw [Equiv.symm_apply_eq, rightAdjointQCohStdHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun {F M M'} g h =>
        rightAdjointQCohStdHomEquiv_naturality_right f F h g }

/-- **[Stacks, Tag 0GEW] at the standard model.** For a proper morphism `f : X ⟶ Y` of Noetherian
schemes, `L ∈ D^-_Coh(𝒪_X)` and `M ∈ D_QCoh(𝒪_Y)` bounded below, the sheafy trace of
[Stacks, Tag 0B6H] is an isomorphism `Rf_*R𝓗om(L, a(M)) ≅ R𝓗om(Rf_*L, M)`. -/
def sheafyTraceIsoStd (L : Std X)
    (hL : minusCoh X L) (M : (qcoh Y).FullSubcategory)
    (hM : DerivedCategoryB.IsBoundedBelow M.obj) :
    (push f).obj (((sheafHom X).obj (op L)).obj ((rightAdjointStd f).obj M)) ≅
      ((sheafHom Y).obj (op ((push f).obj L))).obj M.obj :=
  @asIso _ _ _ _ (sheafyTrace f
    (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf))
    (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite Y.sheaf))
    (StandardModel.isQuasicoherent_homology_derivedPushforward f)
    (rightAdjointQCohStdAdjunction f)
    ⟨L, (qcoh_iff_isDQCoh L).1 (TwistedInverseImageDuality.qcoh_of_isCoherent L hL.2)⟩
    ⟨M.obj, (qcoh_iff_isDQCoh M.obj).1 M.property⟩)
    (isIso_sheafyTrace_of_isProper_of_adjunction f (rightAdjointQCohStdAdjunction f) _ _ hL hM)

end Trace

namespace NormalizedOnOpens

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S} (hpe : f ≫ q = p)
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

/-- **[Stacks, Tag 0AUE] part (6), first assertion.** For a proper morphism `f : X ⟶ Y` of
schemes of finite type over `S` and the dualizing complexes `ω_X^•`, `ω_Y^•` normalized
relative to `ω_S^•`, `f_new^!` is isomorphic to the restriction to `D^+_Coh(𝒪_Y)` of the right
adjoint `a` of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. -/
def fNewShriekIsoRightAdjointOfIsProper
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsProper f]
    (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS) :
    haveI := hq.source_noetherian
    haveI := hp.source_noetherian
    (plusCoh Y).ι ⋙ fNewShriekStd f (stdComplex c 𝒦X) (stdComplex c 𝒦Y) ≅
      ObjectProperty.ιOfLE plusCoh_le_qcoh ⋙ rightAdjointStd f :=
  haveI := hq.source_noetherian
  haveI := hp.source_noetherian
  haveI : IsProper (ftsHomSelf (isShriekable_of_isProper hq) (f := f)).left :=
    inferInstanceAs (IsProper f)
  (upperShriekStdIsoFNewShriek c hpe hωS (isShriekable_of_isProper hq) 𝒦X 𝒦Y).symm ≪≫
    UpperShriekDuality.upperShriekStdIsoRightAdjointOfIsProper _ _

/-- **[Stacks, Tag 0AUE] part (6), the duality isomorphism.** For a proper morphism `f : X ⟶ Y`
of schemes of finite type over `S`, `K ∈ D^-_Coh(𝒪_X)` and `M ∈ D^+_Coh(𝒪_Y)`, there is a
canonical isomorphism `Rf_*R𝓗om(K, f_new^! M) ≅ R𝓗om(Rf_*K, M)`: part (6) identifies `f_new^!M`
with `a(M)`, and the sheafy trace is an isomorphism by [Stacks, Tag 0GEW]. -/
def fNewShriekSheafHomIso
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsProper f]
    (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)
    (K : Std X) (hK : haveI := hp.source_noetherian; minusCoh X K)
    (M : (plusCoh Y).FullSubcategory) :
    (push f).obj (((sheafHom X).obj (op K)).obj
        ((fNewShriekStd f (stdComplex c 𝒦X) (stdComplex c 𝒦Y)).obj M.obj)) ≅
      ((sheafHom Y).obj (op ((push f).obj K))).obj M.obj :=
  haveI := hq.source_noetherian
  haveI := hp.source_noetherian
  (push f).mapIso (((sheafHom X).obj (op K)).mapIso
      ((fNewShriekIsoRightAdjointOfIsProper c hpe hωS 𝒦X 𝒦Y).app M)) ≪≫
    sheafyTraceIsoStd f K hK ((ObjectProperty.ιOfLE plusCoh_le_qcoh).obj M) M.property.1

/-- `a(ω_Y^•) ≅ ω_X^•` ([Stacks, Tag 0AUD]) at the standard model. -/
def rightAdjointStdDualizingIso
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsProper f]
    (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS) :
    haveI := hq.source_noetherian
    haveI := hp.source_noetherian
    (rightAdjointStd f).obj ⟨stdComplex c 𝒦Y, TwistedInverseImageDuality.qcoh_of_isDualizingComplex
      (isDualizing_stdComplex c hωS 𝒦Y)⟩ ≅ stdComplex c 𝒦X :=
  haveI := hq.source_noetherian
  haveI := hp.source_noetherian
  (comparison X).inverse.mapIso ((ObjectProperty.ι _).mapIso
    ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).mapIso
        (ObjectProperty.isoMk _ ((comparison Y).counitIso.app 𝒦Y.complex.obj.obj)) ≪≫
      twistedInverseImageObjIso c hpe hωS 𝒦X 𝒦Y))

/-- **[Stacks, Tag 0AUE] part (6), the duality for the dualizing complexes.** For a proper
morphism `f : X ⟶ Y` of schemes of finite type over `S` and `K ∈ D^-_Coh(𝒪_X)`,
`Rf_*R𝓗om(K, ω_X^•) ≅ R𝓗om(Rf_*K, ω_Y^•)`. -/
def sheafHomDualizingIso
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsProper f]
    (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)
    (K : Std X) (hK : haveI := hp.source_noetherian; minusCoh X K) :
    (push f).obj (((sheafHom X).obj (op K)).obj (stdComplex c 𝒦X)) ≅
      ((sheafHom Y).obj (op ((push f).obj K))).obj (stdComplex c 𝒦Y) :=
  haveI := hq.source_noetherian
  haveI := hp.source_noetherian
  (push f).mapIso (((sheafHom X).obj (op K)).mapIso
      (rightAdjointStdDualizingIso c hpe hωS 𝒦X 𝒦Y).symm) ≪≫
    sheafyTraceIsoStd f K hK _
      (isBoundedBelow_of_isDualizing_std (isDualizing_stdComplex c hωS 𝒦Y))

end NormalizedOnOpens

end Stacks.Duality

end
