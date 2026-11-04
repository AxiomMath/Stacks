module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import StacksFrontier.AlgebraicGeometry.ProjPresentationCompare.Basic
public import StacksFrontier.AlgebraicGeometry.ProjPresentationCompare.SymSectionRing
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ProjectiveBundleBaseChange
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of a projective morphism

A base change of a projective morphism of schemes is projective, and a base change of a locally
projective morphism is locally projective. These are the two assertions of Tag 02V6, read for the
two predicates of Tag 01W8 that `StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic`
defines: `AlgebraicGeometry.IsProjective` and `AlgebraicGeometry.IsLocallyProjective`.

The file also proves Tag 0C4Q — if `f ≫ g` is projective and `g` is separated then `f` is
projective — for `AlgebraicGeometry.IsProjective`, whose one geometric input is the same base
change of the projective bundle.

As in the source, both are proved from three facts: that the base change of a projective bundle
over a scheme is again a projective bundle (Tag 01O3), that the pullback of an `𝒪`-module of
finite type is of finite type (Tag 01B6, `AlgebraicGeometry.SheafOfModules.pullback_isFiniteType`),
and that the base change of a closed immersion is a closed immersion (Tag 01JY,
`AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange`), together with quasi-coherence of a
pullback, Tag 01BG. The first is `AlgebraicGeometry.projectiveBundleBaseChangeComparison`.

## Main definitions

* `AlgebraicGeometry.ProjectiveBundleBaseChangeComparison`: Tag 01O3 for the sheaf symmetric
  algebra: the projective bundle of a pullback `g^* ℰ` is the fibre product of the projective
  bundle of `ℰ` with the new base, by an isomorphism over the new base.
* `AlgebraicGeometry.ProjectiveBundlePresentationsAgree`: the comparison of the two presentations
  of the projective bundle — `Stacks.SymGraded.schemeProjectiveBundle` and
  `Stacks.RelativeProj.projectiveBundle` — as an isomorphism over the base.

## Main results

* `AlgebraicGeometry.IsProjective.pullback_fst`: **a base change of a projective morphism is
  projective**, the first assertion of Tag 02V6.
* `AlgebraicGeometry.IsLocallyProjective.pullback_fst`: **a base change of a locally projective
  morphism is locally projective**, the second assertion of Tag 02V6.
* `AlgebraicGeometry.IsProjective.of_isPullback` and
  `AlgebraicGeometry.isStableUnderBaseChange_isProjective`: the first assertion for an arbitrary
  cartesian square, and as a `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`.
* `AlgebraicGeometry.projectiveBundlePresentationsAgree`: **the two presentations of the
  projective bundle are isomorphic over the base.**
* `AlgebraicGeometry.projectiveBundleBaseChangeComparison_of_presentationsAgree` and
  `AlgebraicGeometry.projectiveBundleBaseChangeComparison`: **Tag 01O3 for the sheaf symmetric
  algebra**, deduced from the comparison of the two presentations and Tag 01O3 for
  `Stacks.RelativeProj.projectiveBundle`.
* `AlgebraicGeometry.IsProjective.comp_iso`: projectivity is preserved by precomposition with an
  isomorphism, which is what carries the first assertion from the canonical fibre product to an
  arbitrary cartesian square.
* `AlgebraicGeometry.IsProjective.of_comp`: **Tag 0C4Q for `AlgebraicGeometry.IsProjective`**, if
  `f ≫ g` is projective and `g` is separated then `f` is projective.
* `AlgebraicGeometry.IsProjective.isLocallyProjective`: a projective morphism is locally
  projective, clause (1) of Definition 01W8 implying clause (3).

## The two presentations of the projective bundle

`AlgebraicGeometry.IsProjective` asks for a closed immersion into
`Stacks.SymGraded.schemeProjectiveBundle`, the relative homogeneous spectrum of the sheaf
symmetric algebra read through
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`. Its base change is obtained from
the cartesian square `Stacks.RelativeProj.isPullback_projectiveBundleToBase_baseChange` for the
other presentation, `Stacks.RelativeProj.projectiveBundle`, the relative homogeneous spectrum of
the symmetric algebra read as a `Stacks.RelativeProj.Situation`, which assumes only
quasi-coherence and `ℰ' ≅ g^* ℰ`. It is carried along
`AlgebraicGeometry.projectiveBundlePresentationsAgree`: the two glueings have the same charts,
because the two graded rings of sections over an affine open are the same direct sum of the same
homogeneous section groups with the same homogeneous operations
(`Stacks.SymGraded.situationGradedHom`), and a scheme over the base carrying the charts of a
relative `Proj` *is* that relative `Proj`. The two `CommRing` structures on that one carrier are
not definitionally equal — one is constructed, the other selected with `Classical.choice` — which
is why the comparison is not a transport; see
`StacksFrontier.AlgebraicGeometry.ProjPresentationCompare.SymSectionRing`.

## Implementation notes

Both `Prop`s are quantified over every scheme and every module, rather than taking them as
parameters: quantifying a `Prop` costs nothing, and the locally projective assertion needs the
quantified form, since it applies the projective assertion once over each member of a covering
of the base, hence at a different pair of schemes each time.

The closed immersion into the base-changed bundle is built as a
`CategoryTheory.Limits.pullback.lift` rather than as a `pullback.map`, because the two equations
characterising it are then
`pullback.lift_fst` and `pullback.lift_snd` and the cartesian square exhibiting it as the base
change of the given closed immersion is `CategoryTheory.IsPullback.of_bot` applied to the two
fibre-product squares. Routing it through
`CategoryTheory.MorphismProperty.pullbackMap` would need
`CategoryTheory.MorphismProperty.IsStableUnderComposition` for closed immersions, which is not
an instance in Mathlib, and so a local instance, for no gain.

## References

* [Stacks Project, Tag 02V6](https://stacks.math.columbia.edu/tag/02V6)
* [Stacks Project, Tag 0C4Q](https://stacks.math.columbia.edu/tag/0C4Q)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01B6](https://stacks.math.columbia.edu/tag/01B6)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01JY](https://stacks.math.columbia.edu/tag/01JY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.SymGraded Stacks.RelativeProj

universe u

namespace AlgebraicGeometry

/-! ### Tag 01O3 for the sheaf symmetric algebra -/

/-- **The projective bundle of the sheaf symmetric algebra commutes with base change.** For
every morphism of schemes `g : S' ⟶ S`, every quasi-coherent `𝒪_S`-module `ℰ` and every
quasi-coherent `𝒪_{S'}`-module `ℰ'` identified with `g^* ℰ`, the projective bundle `𝐏(ℰ')` is
the fibre product `S' ×_S 𝐏(ℰ)`, by an isomorphism carrying the projection of `𝐏(ℰ')` to the
projection to `S'`.

This is Tag 01O3 for the sheaf symmetric algebra, named as a `Prop` because it is applied at
several bases and modules inside one proof;
`AlgebraicGeometry.projectiveBundleBaseChangeComparison` proves it. -/
def ProjectiveBundleBaseChangeComparison : Prop :=
  ∀ {S S' : Scheme.{u}} (g : S' ⟶ S) (E : S.Modules) [E.IsQuasicoherent]
      (hqc : IsQuasicoherentPieces E) (E' : S'.Modules) [E'.IsQuasicoherent]
      (hqc' : IsQuasicoherentPieces E'), (E' ≅ (Scheme.Modules.pullback g).obj E) →
    ∃ e : (schemeProjectiveBundle E' hqc').scheme ≅
        pullback g (schemeProjectiveBundle E hqc).toBase,
      e.hom ≫ pullback.fst g (schemeProjectiveBundle E hqc).toBase =
        (schemeProjectiveBundle E' hqc').toBase

/-- **The two presentations of the projective bundle agree over the base.** The projective bundle
`𝐏(ℰ) = Proj_S(Sym ℰ)` has two presentations: `Stacks.SymGraded.schemeProjectiveBundle`, by
glueing the affine `Proj` of the graded rings of sections of `Sym ℰ` read as a
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, and
`Stacks.RelativeProj.projectiveBundle`, by glueing those of a `Stacks.RelativeProj.Situation`.
This is the assertion that the two are isomorphic as schemes over `S`. -/
def ProjectiveBundlePresentationsAgree : Prop :=
  ∀ {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent] (hqc : IsQuasicoherentPieces E),
    ∃ b : (schemeProjectiveBundle E hqc).scheme ≅ Stacks.RelativeProj.projectiveBundle S E,
      b.hom ≫ Stacks.RelativeProj.projectiveBundleToBase S E =
        (schemeProjectiveBundle E hqc).toBase

/-- **The base-change comparison follows from the comparison of the two presentations.** The
cartesian square of the base change of a projective bundle holds for
`Stacks.RelativeProj.projectiveBundle`, as
`Stacks.RelativeProj.isPullback_projectiveBundleToBase_baseChange`; transporting it along an
isomorphism over the base at `ℰ` and at `ℰ'` turns it into the square for
`Stacks.SymGraded.schemeProjectiveBundle`, whose comparison with the fibre product is then
`CategoryTheory.IsPullback.isoPullback`. -/
theorem projectiveBundleBaseChangeComparison_of_presentationsAgree
    (hb : ProjectiveBundlePresentationsAgree.{u}) :
    ProjectiveBundleBaseChangeComparison.{u} := by
  intro S S' g E _ hqc E' _ hqc' hE
  obtain ⟨b, hbase⟩ := hb E hqc
  obtain ⟨b', hbase'⟩ := hb E' hqc'
  have key : IsPullback ((schemeProjectiveBundle E' hqc').toBase)
      (b'.hom ≫ Stacks.RelativeProj.projectiveBundleBaseChange g E E' hE ≫ b.inv) g
      ((schemeProjectiveBundle E hqc).toBase) := by
    refine (Stacks.RelativeProj.isPullback_projectiveBundleToBase_baseChange g E E' hE).of_iso
      b'.symm (Iso.refl _) b.symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [← hbase']
    · simp
    · simp
    · simp [← hbase]
  exact ⟨key.isoPullback, key.isoPullback_hom_fst⟩

/-- **The two presentations of the projective bundle do agree over the base.** The two glueings
are compared by `Stacks.AlgebraicGeometry.ProjPresentation.exists_iso_relativeProj_of_inverse`,
whose input is an isomorphism of the graded rings of sections over each affine open of the base
compatible with restriction and with the degree-zero identifications; that isomorphism is
`Stacks.SymGraded.situationGradedHom`, the identity on each homogeneous summand. -/
theorem projectiveBundlePresentationsAgree : ProjectiveBundlePresentationsAgree.{u} := by
  intro S E hE hqc
  refine Stacks.AlgebraicGeometry.ProjPresentation.exists_iso_relativeProj_of_inverse
    (Stacks.RelativeProj.Situation.chartData (symSituation E))
    (situationSheafGradedAlgebra E hqc).toGradedAlgebra
    (fun U => situationGradedHom E hqc U.toOpens)
    (fun U => situationSectionRingHomInv E hqc U.toOpens)
    (fun U => situationSectionRingHomInv_hom E hqc U.toOpens)
    (fun U => situationSectionRingHom_inv E hqc U.toOpens)
    (fun U => situationSectionRingHomInv_mem E hqc U.toOpens)
    (fun U V h => situationGradedHom_res E hqc U.toOpens V.toOpens h) ?_
  intro U
  refine CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext ?_)
  exact (congrArg (situationSectionRingHom E hqc U.toOpens)
      (((situationSheafGradedAlgebra E hqc).toGradedAlgebra).coe_strZero_apply U r)).trans
    ((situationSectionRingHom_strHom E hqc U.toOpens r).trans
      (Stacks.AlgebraicGeometry.RelativeProj.projZeroRingHom'_coe_of_mem _
        (Stacks.RelativeProj.Situation.sectionRingBaseMap_mem_zero
          (symSituation E) U.toOpens r)).symm)

/-- **The projective bundle of the sheaf symmetric algebra commutes with base change**: Tag 01O3
for `Stacks.SymGraded.schemeProjectiveBundle`. It is Tag 01O3 for
`Stacks.RelativeProj.projectiveBundle` carried along the comparison of the two presentations. -/
@[ega "II 4.1.3"]
theorem projectiveBundleBaseChangeComparison : ProjectiveBundleBaseChangeComparison.{u} :=
  projectiveBundleBaseChangeComparison_of_presentationsAgree projectiveBundlePresentationsAgree

/-! ### Base change of a projective morphism -/

/-- **Projectivity is preserved by precomposition with an isomorphism.** A closed immersion into
a projective bundle over the base, precomposed with an isomorphism, is again one. -/
theorem IsProjective.comp_iso {A B S : Scheme.{u}} (e : A ≅ B) {h : B ⟶ S}
    (hh : IsProjective h) : IsProjective (e.hom ≫ h) := by
  obtain ⟨E, hq, hft, hqc, i, hi, rfl⟩ := hh
  exact ⟨E, hq, hft, hqc, e.hom ≫ i, inferInstance, Category.assoc _ _ _⟩

/-- A closed immersion into the base change of a projective bundle gives a projective morphism
after composing with the first projection. -/
private theorem isProjective_comp_fst_of_isClosedImmersion {X S S' : Scheme.{u}} (g : S' ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] [E.IsFiniteType] (hqc : IsQuasicoherentPieces E)
    {j : X ⟶ pullback g (schemeProjectiveBundle E hqc).toBase} [IsClosedImmersion j] :
    IsProjective (j ≫ pullback.fst g (schemeProjectiveBundle E hqc).toBase) := by
  have : ((Scheme.Modules.pullback g).obj E).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback g E
  have : ((Scheme.Modules.pullback g).obj E).IsFiniteType :=
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType g.toLRSHom.toShHom E
  obtain ⟨e, he⟩ := projectiveBundleBaseChangeComparison g E hqc
    ((Scheme.Modules.pullback g).obj E)
    (isQuasicoherentPieces_of_isQuasicoherent _) (Iso.refl _)
  refine ⟨_, inferInstance, inferInstance, isQuasicoherentPieces_of_isQuasicoherent _,
    j ≫ e.inv, inferInstance, ?_⟩
  rw [Category.assoc, ← he, Iso.inv_hom_id_assoc]

/-- **A base change of a projective morphism is projective.** For `f : X ⟶ S` projective and
`g : S' ⟶ S` arbitrary, the first projection `S' ×_S X ⟶ S'` is projective. -/
@[stacks 02V6 "projective"]
theorem IsProjective.pullback_fst
    {X S S' : Scheme.{u}} {f : X ⟶ S} (g : S' ⟶ S) (hf : IsProjective f) :
    IsProjective (pullback.fst g f) := by
  obtain ⟨E, hq, hft, hqc, i, hi, hfac⟩ := hf
  have hcond : pullback.fst g f ≫ g =
      (pullback.snd g f ≫ i) ≫ (schemeProjectiveBundle E hqc).toBase := by
    rw [Category.assoc, hfac, pullback.condition]
  have hjfst : pullback.lift (pullback.fst g f) (pullback.snd g f ≫ i) hcond ≫
      pullback.fst g (schemeProjectiveBundle E hqc).toBase = pullback.fst g f :=
    pullback.lift_fst _ _ _
  have hjsnd : pullback.lift (pullback.fst g f) (pullback.snd g f ≫ i) hcond ≫
      pullback.snd g (schemeProjectiveBundle E hqc).toBase = pullback.snd g f ≫ i :=
    pullback.lift_snd _ _ _
  have hsq : IsPullback (pullback.snd g f)
      (pullback.lift (pullback.fst g f) (pullback.snd g f ≫ i) hcond) i
      (pullback.snd g (schemeProjectiveBundle E hqc).toBase) := by
    refine IsPullback.of_bot
      (v₂₁ := pullback.fst g (schemeProjectiveBundle E hqc).toBase) ?_ hjsnd.symm
      (IsPullback.of_hasPullback g (schemeProjectiveBundle E hqc).toBase).flip
    rw [hjfst, hfac]
    exact (IsPullback.of_hasPullback g f).flip
  have hj : IsClosedImmersion
      (pullback.lift (pullback.fst g f) (pullback.snd g f ≫ i) hcond) :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback hsq hi
  have := isProjective_comp_fst_of_isClosedImmersion g E hqc
    (j := pullback.lift (pullback.fst g f) (pullback.snd g f ≫ i) hcond)
  rwa [hjfst] at this

/-- **The first assertion of Tag 02V6 over an arbitrary cartesian square.** If `p` and `q`
exhibit their source as the fibre product of `g` and `f`, and `f` is projective, then so is `p`.
This is `AlgebraicGeometry.IsProjective.pullback_fst` carried along
`CategoryTheory.IsPullback.isoPullback` by `AlgebraicGeometry.IsProjective.comp_iso`. -/
theorem IsProjective.of_isPullback
    {T X S S' : Scheme.{u}}
    {p : T ⟶ S'} {q : T ⟶ X} {g : S' ⟶ S} {f : X ⟶ S}
    (sq : IsPullback p q g f) (hf : IsProjective f) : IsProjective p := by
  have h := IsProjective.comp_iso sq.isoPullback (IsProjective.pullback_fst g hf)
  rwa [sq.isoPullback_hom_fst] at h

/-- **Projectivity is stable under base change**, as a
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange`. -/
theorem isStableUnderBaseChange_isProjective :
    MorphismProperty.IsStableUnderBaseChange @IsProjective.{u} :=
  ⟨fun sq hg => IsProjective.of_isPullback sq.flip hg⟩

/-! ### Permanence of projectivity -/

/-- **If `f ≫ g` is projective and `g` is separated then `f` is projective.** Here projective is
`AlgebraicGeometry.IsProjective`, clause (1) of Definition 01W8: a closed immersion over the base
into the projective bundle `𝐏(ℰ)` of a quasi-coherent module of finite type. The H-projective
form, clause (2), is `AlgebraicGeometry.IsProjectiveMorphism.of_comp`. -/
@[stacks 0C4Q "projective case: closed immersion over the base into the projective bundle 𝐏(ℰ) \
of a quasi-coherent module of finite type, i.e. clause (1) of Definition 01W8; no hypothesis \
beyond the separatedness of `g` that the source states"]
theorem IsProjective.of_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsSeparated g]
    (h : IsProjective (f ≫ g)) : IsProjective f := by
  obtain ⟨E, hq, hft, hqc, i, hi, hfac⟩ := h
  have hsep : IsSeparated (pullback.snd g (schemeProjectiveBundle E hqc).toBase) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsSeparated)
      (IsPullback.of_hasPullback g (schemeProjectiveBundle E hqc).toBase) ‹IsSeparated g›
  have hk : IsClosedImmersion (pullback.lift f i hfac.symm) := by
    have : IsClosedImmersion
        (pullback.lift f i hfac.symm ≫
          pullback.snd g (schemeProjectiveBundle E hqc).toBase) := by
      rw [pullback.lift_snd]
      infer_instance
    exact IsClosedImmersion.of_comp _ (pullback.snd g (schemeProjectiveBundle E hqc).toBase)
  have := isProjective_comp_fst_of_isClosedImmersion g E hqc (j := pullback.lift f i hfac.symm)
  rwa [pullback.lift_fst] at this

/-! ### Base change of a locally projective morphism -/

/-- **A projective morphism is locally projective**, the implication from clause (1) of Definition
01W8 to clause (3). The covering of the base is its one-member covering by itself, and the
restriction `f ∣_ ⊤` is a base change of `f`, hence projective. -/
theorem IsProjective.isLocallyProjective {X S : Scheme.{u}} {f : X ⟶ S} (hf : IsProjective f) :
    IsLocallyProjective f :=
  ⟨PUnit.{u + 1}, fun _ => ⊤, by simp, fun _ =>
    IsProjective.of_isPullback (isPullback_morphismRestrict f ⊤) hf⟩

/-- **A base change of a locally projective morphism is locally projective.** For
`f : X ⟶ S` locally projective and `g : S' ⟶ S` arbitrary, the first projection
`S' ×_S X ⟶ S'` is locally projective.

The covering of `S'` is the inverse image of the covering of `S` over whose members `f` is
projective: over `g ⁻¹ᵁ U i` the restriction of the base change is a base change of the
restriction of `f` over `U i`. -/
@[stacks 02V6 "locally projective"]
theorem IsLocallyProjective.pullback_fst
    {X S S' : Scheme.{u}} {f : X ⟶ S} (g : S' ⟶ S) (hf : IsLocallyProjective f) :
    IsLocallyProjective (pullback.fst g f) := by
  obtain ⟨I, U, hU, hproj⟩ := hf
  refine ⟨I, fun k => g ⁻¹ᵁ U k, g.iSup_preimage_eq_top hU, fun k => ?_⟩
  have sq := (isPullback_morphismRestrict (pullback.fst g f) (g ⁻¹ᵁ U k)).paste_vert
    (IsPullback.of_hasPullback g f)
  rw [← morphismRestrict_ι g (U k)] at sq
  exact IsProjective.of_isPullback (sq.of_bot' (isPullback_morphismRestrict f (U k))) (hproj k)

end AlgebraicGeometry

end
