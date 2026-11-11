module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionCurveFamilyBase
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFormalSpectrum
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizerFibre
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionCurveFamilyDimension
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionCurveFamilyFlat
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionCurveFamilyOnePoint
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionCurveFamilyProper
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionCurveFamilyRelocalize
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionCurveFamilySeparated

/-!
# The contraction of a curve on a family of surfaces is a family of curves

Let `(f : X' ⟶ X, T, a)` be a solution of Artin's contraction problem (Stacks 0GH8, 0GIB) with
`|U| = |X| ∖ T` and limit preserving target, in the situation of Stacks 0D5E: `X'` is a scheme `Z`
proper over `S` whose fibres have dimension at most one, the curve `T'` is nonempty, and `W` is
separated over `S` with at most one point. This file assembles the properties of `X ⟶ S` proved in
the neighbouring files — `f` is surjective and `T` is one point
(`StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionCurveFamilyPoints`), `X` is separated
(`…Separated`), proper and of finite presentation (`…Proper`), of relative dimension at most one
(`…Dimension`) — into a family of curves over `S` in the sense of Stacks 0D4Z, whose total space
is `X` read over `Spec ℤ` by Stacks 04SG (`…Base`, `…Relocalize`), and records that if this total
space is a scheme then so is `X`.

## Main results

* `AlgebraicGeometry.FormalSpace.HasAtMostOnePoint.of_iso`: having at most one point is invariant
  under isomorphism.
* `AlgebraicGeometry.Artin.ContractionSituation.Solution.exists_curveFamily_of_isFlat`: the family
  of curves, given flatness of `X ⟶ S`.
* `AlgebraicGeometry.Artin.ContractionSituation.Solution.exists_curveFamily_of_solution`: the
  family of curves, flatness being proved from the description of `W` as the completion of a
  complete local ring (`…Flat`).
* `…Solution.exists_curveFamily_of_solution_of_affineOver`: the same with `W` the completion
  of an object `Spec A ⟶ S` of the site along its closed point.
* `AlgebraicGeometry.Artin.ContractionSituation.Solution.isProper_of_hasAtMostOnePoint`: every
  morphism from `X` to the representable presheaf of `𝟙 S` is proper.

## References

* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
* [Stacks Project, Tag 0GIB](https://stacks.math.columbia.edu/tag/0GIB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Having at most one point is invariant under isomorphism of sheaves. -/
theorem HasAtMostOnePoint.of_iso {W W' : FppfSheaf B S hS} (e : W ≅ W')
    (h : HasAtMostOnePoint W') : HasAtMostOnePoint W := by
  intro K₁ K₂ _ _ h₁ h₂ p₁ p₂ w₁ w₂
  obtain ⟨L, _, hL, pL, q₁, q₂, hq⟩ :=
    h K₁ K₂ h₁ h₂ p₁ p₂ (e.hom.hom.app _ w₁) (e.hom.hom.app _ w₂)
  refine ⟨L, inferInstance, hL, pL, q₁, q₂, ?_⟩
  let eL := ((sheafToPresheaf _ _).mapIso e).app (op (Over.mk (⟨pL⟩ : B.obj hL ⟶ B.obj hS)))
  apply eL.toEquiv.injective
  change e.hom.hom.app _ (W.obj.map q₁.op w₁) = e.hom.hom.app _ (W.obj.map q₂.op w₂)
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hq]

end FormalSpace

namespace Artin.ContractionSituation.Solution

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {c : ContractionSituation B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism of presheaves preceded by an isomorphism is surjective on points as soon as the
morphism is. -/
private theorem isSurjective_iso_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (f : G ⟶ H) (hf : Space.IsSurjective B S hS f) : Space.IsSurjective B S hS (e.hom ≫ f) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  refine ⟨(Space.pointsHomeomorphOfIso B S hS e).symm x, ?_⟩
  rw [Space.pointsMap_comp]
  exact congrArg (Space.pointsMap B S hS G f)
    ((Space.pointsHomeomorphOfIso B S hS e).apply_symm_apply x)

/-- **The contraction of a curve on a family of surfaces, as a family of curves**, given flatness.

Let `(f : X' ⟶ X, T, a)` be a solution of Artin's contraction problem with `|U| = |X| ∖ T` and
limit preserving target, where `X'` is a scheme `Z` proper over `S` whose fibres have dimension at
most one, `T'` is nonempty, `W` is separated over `S` and has at most one point. If `X` is flat over
`S`, then `X`, read over `Spec ℤ` by Stacks 04SG, is the total space of a family of curves over `S`
(Stacks 0D4Z), and if that total space is a scheme then `X` is a scheme over `S`. -/
theorem exists_curveFamily_of_isFlat (hZ : B.Contains integerBase) (s : c.Solution X)
    (hU : Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ)
    (hl : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X)
    {Zo : BigFppfOver B S hS} (eZ : c.X' ≅ yoneda.obj Zo)
    (hZp : IsProper (B.inclusion.map Zo.hom))
    (hZd : ∀ z : (BigFppfOver.toScheme B S hS).obj Zo,
      topologicalKrullDimAt ((B.inclusion.map Zo.hom).fiber (B.inclusion.map Zo.hom z))
        ((B.inclusion.map Zo.hom).asFiber z) ≤ 1)
    (hT' : c.T'.Nonempty) (hW : FormalSpace.IsSeparatedMorphism B S hS (terminal.from c.W))
    (hWpt : FormalSpace.HasAtMostOnePoint c.W)
    (hflat : Space.IsFlat B S hS (terminal.from X)) :
    ∃ (F : CurveFamily B hZ) (hb : F.base = Over.mk (integerBaseMap B hS hZ))
      (e : F.total.obj ≅ (spaceOverIntegers hS hZ ⟨X, s.isAlgebraicSpace_X⟩).1.left),
      e.hom ≫ (spaceOverIntegers hS hZ ⟨X, s.isAlgebraicSpace_X⟩).1.hom =
          F.toBase.hom ≫ eqToHom (congrArg yoneda.obj hb) ∧
        ((∃ V : BigFppfOver B integerBase hZ, Nonempty (F.total ≅ schemeSpace V)) →
          ∃ U : BigFppfOver B S hS, Nonempty (X ≅ yoneda.obj U)) := by
  let F₀ : AlgebraicSpaces B S hS := ⟨X, s.isAlgebraicSpace_X⟩
  let Y := spaceOverIntegers hS hZ F₀
  have hX'p : Space.IsProper B S hS (terminal.from c.X') := by
    rw [show terminal.from c.X' = eZ.hom ≫ terminal.from (yoneda.obj Zo) from
      terminal.hom_ext _ _, Space.isProper_isIso_comp_iff]
    exact Space.isProper_terminal_from_yoneda B S hS Zo hZp
  have hsurj : Space.IsSurjective B S hS s.f := s.surjective_pointsMap_f hWpt hT' hU
  have hft := s.isLocallyOfFiniteType_terminal_from_of_limitPreserving hl
  have hsep := s.isSeparated_terminal_from hU hX'p.1 hW hft
  have hprop := s.isProper_terminal_from hX'p hsurj hsep hft
  have hfp := s.isFinitePresentation_terminal_from hX'p.2.1.2 hsurj hsep hl
  have hdim : ∀ x : Space.points B S hS F₀.1, ∃ e : ℕ, e ≤ 1 ∧
      Space.HoldsOnEveryEtaleChartAtPoint B S hS (@HasFiberDimensionAt.{u} (e : ℕ∞))
        (terminal.from F₀.1) x :=
    Space.exists_le_one_holdsOnEveryEtaleChartAtPoint_hasFiberDimensionAt s.isAlgebraicSpace_X
      (eZ.inv ≫ s.f) ((Space.isProper_isIso_comp_iff B S hS _ _).2 s.isProper_f)
      (isSurjective_iso_comp eZ.symm s.f hsurj) hZd
  let F : CurveFamily B hZ :=
    { base := Over.mk (integerBaseMap B hS hZ)
      total := ⟨Y.1.left, Y.2⟩
      toBase := ObjectProperty.homMk Y.1.hom
      flat := (holdsOnEveryEtaleChart_spaceOverIntegers_hom_iff hS hZ _ F₀).2 hflat
      proper := (isProper_spaceOverIntegers_hom_iff hS hZ F₀).2 hprop
      finitePresentation := (isFinitePresentation_spaceOverIntegers_hom_iff hS hZ F₀).2 hfp
      relativeDimensionLE :=
        Space.relativeDimensionLE_spacesOverSmallerBaseFunctor (integerBaseMap B hS hZ) F₀ hdim }
  refine ⟨F, rfl, Iso.refl _, by
    simp only [Iso.refl_hom, Category.id_comp]; rfl, ?_⟩
  rintro ⟨V, ⟨φ⟩⟩
  exact nonempty_iso_yoneda_of_spaceOverIntegers_iso hS hZ F₀
    ((ObjectProperty.ι _).mapIso φ)

/-- **Stacks 0D5E, the family of curves.** Let `S` be an affine scheme with `Γ(S)` a Dedekind
domain, and let `(f : X' ⟶ X, T, a)` be a solution of Artin's contraction problem (Stacks 0GIB)
with `|U| = |X| ∖ T` and limit preserving target, such that

* `X'` is a scheme `Z` proper and flat over `S` whose fibres have dimension at most one at every
  point, and the curve `T' ⊆ |Z|` being contracted is nonempty;
* `W` is separated over `S` and is the completion of `Spec A` along its closed point, for an
  adically complete local `Γ(S)`-algebra `A` with algebraically closed residue field on which no
  nonzero element of `Γ(S)` is a zero divisor.

Then `X ⟶ S` is a family of curves (Stacks 0D4Z): there is a family of curves over `S` whose
total space is `X` read over `Spec ℤ` (Stacks 04SG), with structure morphism the morphism of `X`
to `S`; and if that total space is a scheme, then `X` is a scheme over `S`. -/
theorem exists_curveFamily_of_solution (hZ : B.Contains integerBase) [IsAffine S]
    [IsDomain Γ(S, ⊤)] [IsDedekindDomain Γ(S, ⊤)] (s : c.Solution X)
    (hU : Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ)
    (hl : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X)
    {Zo : BigFppfOver B S hS} (eZ : c.X' ≅ yoneda.obj Zo)
    (hZp : IsProper (B.inclusion.map Zo.hom)) (hZf : Flat (B.inclusion.map Zo.hom))
    (hZd : ∀ z : (BigFppfOver.toScheme B S hS).obj Zo,
      topologicalKrullDimAt ((B.inclusion.map Zo.hom).fiber (B.inclusion.map Zo.hom z))
        ((B.inclusion.map Zo.hom).asFiber z) ≤ 1)
    (hT' : c.T'.Nonempty) (hW : FormalSpace.IsSeparatedMorphism B S hS (terminal.from c.W))
    {A : Type u} [CommRing A] [IsLocalRing A] [Algebra Γ(S, ⊤) A]
    (hAc : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    (hAt : ∀ r : Γ(S, ⊤), r ≠ 0 → IsSMulRegular A r)
    (hA : B.Contains (Spec (.of A)))
    (eW : c.W ≅ Space.completionSheaf B S hS
      (yoneda.obj (Space.specOver B S hS S.isoSpec.inv A hA))
      {(Space.schemePointsHomeomorph B S hS (Space.specOver B S hS S.isoSpec.inv A hA)).symm
        (IsLocalRing.closedPoint A)}) :
    ∃ (F : CurveFamily B hZ) (hb : F.base = Over.mk (integerBaseMap B hS hZ))
      (e : F.total.obj ≅ (spaceOverIntegers hS hZ ⟨X, s.isAlgebraicSpace_X⟩).1.left),
      e.hom ≫ (spaceOverIntegers hS hZ ⟨X, s.isAlgebraicSpace_X⟩).1.hom =
          F.toBase.hom ≫ eqToHom (congrArg yoneda.obj hb) ∧
        ((∃ V : BigFppfOver B integerBase hZ, Nonempty (F.total ≅ schemeSpace V)) →
          ∃ U : BigFppfOver B S hS, Nonempty (X ≅ yoneda.obj U)) :=
  s.exists_curveFamily_of_isFlat hZ hU hl eZ hZp hZd hT' hW
    (FormalSpace.HasAtMostOnePoint.of_iso eW
      (FormalSpace.hasAtMostOnePoint_completionSheaf_yoneda_singleton _ _))
    (s.isFlat_terminal_from hU eZ hZf hAc hAt hA eW
      (s.isLocallyOfFiniteType_terminal_from_of_limitPreserving hl))

/-- **Properness of the target, in the form of a morphism to `S`.** Under the hypotheses of
`AlgebraicGeometry.Artin.ContractionSituation.Solution.isProper_terminal_from`, with the
surjectivity of `f` and the separatedness of `X` supplied by
`AlgebraicGeometry.Artin.ContractionSituation.Solution.surjective_pointsMap_f` and
`AlgebraicGeometry.Artin.ContractionSituation.Solution.isSeparated_terminal_from`, every morphism
from `X` to the representable presheaf of `𝟙 S` is proper. -/
theorem isProper_of_hasAtMostOnePoint (s : c.Solution X)
    (hU : Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ)
    (hX' : Space.IsProper B S hS (terminal.from c.X'))
    (hW : FormalSpace.IsSeparatedMorphism B S hS (terminal.from c.W))
    (hWpt : FormalSpace.HasAtMostOnePoint c.W) (hT' : c.T'.Nonempty)
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X))
    (g : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS)))) :
    Space.IsProper B S hS g := by
  rw [show g = terminal.from X ≫
      (((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).uniqueUpToIso
        terminalIsTerminal).inv from
      ((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).hom_ext _ _,
    Space.isProper_comp_isIso_iff]
  exact s.isProper_terminal_from hX' (s.surjective_pointsMap_f hWpt hT' hU)
    (s.isSeparated_terminal_from hU hX'.1 hW hft) hft

/-- **Stacks 0D5E, the family of curves, for `W` the completion of `Spec A` over `S` along its
closed point**, `A` being made a `Γ(S)`-algebra by its structure morphism `σ : Spec A ⟶ S`. This
is `AlgebraicGeometry.Artin.ContractionSituation.Solution.exists_curveFamily_of_solution` with `W`
presented as the completion of the object `Spec A ⟶ S` of the site
(`AlgebraicGeometry.FormalSpace.affineOver`) along the preimage of the closed point. -/
theorem exists_curveFamily_of_solution_of_affineOver (hZ : B.Contains integerBase) [IsAffine S]
    [IsDomain Γ(S, ⊤)] [IsDedekindDomain Γ(S, ⊤)] (s : c.Solution X)
    (hU : Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ)
    (hl : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X)
    {Zo : BigFppfOver B S hS} (eZ : c.X' ≅ yoneda.obj Zo)
    (hZp : IsProper (B.inclusion.map Zo.hom)) (hZf : Flat (B.inclusion.map Zo.hom))
    (hZd : ∀ z : (BigFppfOver.toScheme B S hS).obj Zo,
      topologicalKrullDimAt ((B.inclusion.map Zo.hom).fiber (B.inclusion.map Zo.hom z))
        ((B.inclusion.map Zo.hom).asFiber z) ≤ 1)
    (hT' : c.T'.Nonempty) (hW : FormalSpace.IsSeparatedMorphism B S hS (terminal.from c.W))
    {A : Type u} [CommRing A] [IsLocalRing A]
    (hAc : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    (hA : B.Contains (Spec (.of A))) (σ : Spec (.of A) ⟶ S)
    (hAt : ∀ r : Γ(S, ⊤), r ≠ 0 →
      IsSMulRegular A ((σ.appTop ≫ (Scheme.ΓSpecIso (.of A)).hom) r))
    (eW : c.W ≅ Space.completionSheaf B S hS (yoneda.obj (FormalSpace.affineOver B S hS hA σ))
      (Space.pointsToScheme B S hS (FormalSpace.affineOver B S hS hA σ) ⁻¹'
        {(IsLocalRing.closedPoint A : PrimeSpectrum A)})) :
    ∃ (F : CurveFamily B hZ) (hb : F.base = Over.mk (integerBaseMap B hS hZ))
      (e : F.total.obj ≅ (spaceOverIntegers hS hZ ⟨X, s.isAlgebraicSpace_X⟩).1.left),
      e.hom ≫ (spaceOverIntegers hS hZ ⟨X, s.isAlgebraicSpace_X⟩).1.hom =
          F.toBase.hom ≫ eqToHom (congrArg yoneda.obj hb) ∧
        ((∃ V : BigFppfOver B integerBase hZ, Nonempty (F.total ≅ schemeSpace V)) →
          ∃ U : BigFppfOver B S hS, Nonempty (X ≅ yoneda.obj U)) := by
  let : Algebra Γ(S, ⊤) A := (σ.appTop ≫ (Scheme.ΓSpecIso (.of A)).hom).hom.toAlgebra
  have hσ : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) A)) ≫ S.isoSpec.inv = σ := by
    have h := Scheme.isoSpec_inv_naturality σ
    calc Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) A)) ≫ S.isoSpec.inv
        = Spec.map (σ.appTop ≫ (Scheme.ΓSpecIso (.of A)).hom) ≫ S.isoSpec.inv := rfl
      _ = Spec.map (Scheme.ΓSpecIso (.of A)).hom ≫ Spec.map σ.appTop ≫ S.isoSpec.inv := by
          rw [Spec.map_comp, Category.assoc]
      _ = (Spec (.of A)).isoSpec.hom ≫ (Spec (.of A)).isoSpec.inv ≫ σ := by
          rw [h, Scheme.isoSpec_Spec_hom]
      _ = σ := Iso.hom_inv_id_assoc _ _
  let eO : FormalSpace.affineOver B S hS hA σ ≅ Space.specOver B S hS S.isoSpec.inv A hA :=
    Over.isoMk (Iso.refl _) (ObjectProperty.hom_ext _ (by
      change 𝟙 _ ≫ (Spec.map _ ≫ S.isoSpec.inv) = σ
      rw [Category.id_comp]; exact hσ))
  have hT : Space.pointsToScheme B S hS (FormalSpace.affineOver B S hS hA σ) ⁻¹'
      {(IsLocalRing.closedPoint A : PrimeSpectrum A)} =
      Space.pointsMap B S hS _ (yoneda.mapIso eO).hom ⁻¹'
        {(Space.schemePointsHomeomorph B S hS (Space.specOver B S hS S.isoSpec.inv A hA)).symm
          (IsLocalRing.closedPoint A)} := by
    ext x
    change Space.pointsToScheme B S hS _ x = _ ↔ Space.pointsMap B S hS _ _ x = _
    have key : Space.pointsToScheme B S hS (Space.specOver B S hS S.isoSpec.inv A hA)
        (Space.pointsMap B S hS _ (yoneda.mapIso eO).hom x) =
        Space.pointsToScheme B S hS (FormalSpace.affineOver B S hS hA σ) x :=
      (Space.pointsToScheme_pointsMap_yoneda B S hS eO.hom x).trans rfl
    constructor
    · intro hx
      apply (Space.schemePointsHomeomorph B S hS _).injective
      exact key.trans (hx.trans (Homeomorph.apply_symm_apply _ _).symm)
    · intro hx
      exact key.symm.trans ((congrArg (Space.schemePointsHomeomorph B S hS _) hx).trans
        (Homeomorph.apply_symm_apply _ _))
  refine s.exists_curveFamily_of_solution hZ hU hl eZ hZp hZf hZd hT' hW hAc
    (fun r hr => (isSMulRegular_algebraMap_iff (M := A) (A := A)).1 (hAt r hr)) hA
    (eW ≪≫ Space.completionSheafIsoOfIso B S hS (yoneda.mapIso eO) _ _ hT)

end Artin.ContractionSituation.Solution

end AlgebraicGeometry
