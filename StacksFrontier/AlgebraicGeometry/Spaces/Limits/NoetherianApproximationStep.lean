module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GluedEtaleQuotientKernelPair
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GluedEtaleQuotientLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianApproximation

/-!
# The inductive step of absolute Noetherian approximation

Let `(U ⊆ X, f : V ⟶ X)` be an elementary distinguished square with `f` surjective, `V` an object
of the site and `W = V ×_X U`. Suppose that `U`, `W` and `V` are limits of an inverse system of
glued étale data `(Uⱼ, Wⱼ ⊆ Vⱼ)` (`AlgebraicGeometry.Space.GluedEtaleQuotient.System`), compatibly,
with `W = Wⱼ ×_{Uⱼ} U` and `W = Wⱼ ×_{Vⱼ} V`. Then `X` is the limit of the algebraic spaces
`Xⱼ = Vⱼ/Rⱼ`.

This is the "proof of the claim" closing the proof of Stacks 07SU: `X ≅ X' = lim Xᵢ`, by
Spaces, Lemma 0262, both being presented by the same étale equivalence relation on `V`.

## Main results

* `AlgebraicGeometry.Space.GluedEtaleQuotient.System.exists_iso_limit_quotients`.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space.GluedEtaleQuotient.System

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
  {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
  {U : Subfunctor X} {Winf Vinf : BigFppfOver B (⊤_ Scheme.{u}) hZ} (f : yoneda.obj Vinf ⟶ X)
  (h : IsElementaryDistinguishedSquare B (⊤_ Scheme.{u}) hZ hX U f)
  (hfs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))) f)
  (winf : yoneda.obj Winf ⟶ U.toFunctor)
  (hwinf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf winf)
  (ιinf : Winf ⟶ Vinf) [AlgebraicGeometry.IsOpenImmersion
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ιinf)]
  (hWVsq : IsPullback winf (yoneda.map ιinf) U.ι f)
  {J : Type u} [Category.{u} J] [IsCofiltered J] (hJ : #J < B.cutoff.ord.cof)
  (hJhom : ∀ i j : J, #(i ⟶ j) < B.cutoff.ord.cof) (D : System B hZ J)
  (πU : (Functor.const J).obj U.toFunctor ⟶ D.base) (πW : (Functor.const J).obj Winf ⟶ D.chart)
  (πV : (Functor.const J).obj Vinf ⟶ D.ambient)
  (hwU : ∀ j, winf ≫ πU.app j = yoneda.map (πW.app j) ≫ D.toBase.app j)
  (hιV : ∀ j, ιinf ≫ πV.app j = πW.app j ≫ D.incl.app j)
  (hWU : ∀ j, IsPullback (yoneda.map (πW.app j)) winf (D.toBase.app j) (πU.app j))
  (hWV : ∀ j, IsPullback ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (πW.app j))
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ιinf)
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (D.incl.app j))
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (πV.app j)))
  (hVinf : IsLimit (yoneda.mapCone (Cone.mk Vinf πV)))

include h hfs hwinf hWVsq hJ hJhom hwU hιV hWU hWV hVinf in
/-- **The inductive step of Stacks 07SU.** `X` is the limit of the glued étale quotients
`Xⱼ = Vⱼ/Rⱼ`, compatibly with the charts `V ⟶ X` and `V ⟶ lim Xⱼ`. -/
theorem exists_iso_limit_quotients :
    ∃ e : X ≅ limit D.quotients,
      f ≫ e.hom = D.limitChart (yoneda.mapCone (Cone.mk Vinf πV)) := by
  obtain ⟨j₀⟩ := IsCofiltered.nonempty (C := J)
  have hR := isPullback_of_isElementaryDistinguishedSquare hX f h winf hwinf ιinf hWVsq
  have hR' := D.isPullback_limitChart_kernel winf hwinf ιinf πU πW πV hwU hιV hWU hWV hVinf
  have hX' : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (limit D.quotients) :=
    isAlgebraicSpace_limit B (⊤_ Scheme.{u}) hZ D.quotients hJ hJhom D.isAlgebraicSpace_quotients
      D.isAffineHom_quotients
  have hfe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))) f :=
    (isEtale_iff_presheaf_of_yoneda B (⊤_ Scheme.{u}) hZ f).mp h.isEtale
  have hsq := D.isPullback_limitChart (yoneda.mapCone (Cone.mk Vinf πV)) hVinf j₀
  have hfs' := presheaf_of_isPullback B (⊤_ Scheme.{u}) hZ hsq (qmap_surjective _ _ _)
  have hfe' := presheaf_of_isPullback B (⊤_ Scheme.{u}) hZ hsq (qmap_etale _ _ _)
  exact exists_iso_of_isomorphic_presentations B (⊤_ Scheme.{u}) hZ hR hR' (Iso.refl _)
    (Category.id_comp _) (Category.id_comp _) hX hX' hfs hfe hfs' hfe'

end AlgebraicGeometry.Space.GluedEtaleQuotient.System


/-! ### Finite type over `Spec ℤ` of a glued étale quotient -/

namespace AlgebraicGeometry.Space.GluedEtaleQuotient

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
  {U : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} {W V : BigFppfOver B (⊤_ Scheme.{u}) hZ}
  (w : yoneda.obj W ⟶ U)
  (hw : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf w)
  (ι : W ⟶ V)
  [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)]

/-- The representable presheaf of the identity object is terminal. -/
private def isTerminalYonedaObjMkId :
    IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hZ)) : BigFppfOver B (⊤_ Scheme.{u}) hZ)) :=
  (Over.mkIdTerminal (X := B.obj hZ)).isTerminalObj yoneda _

/-- The terminal presheaf on the big fppf site of `Spec ℤ` is a quasi-separated algebraic space. -/
theorem isAbsolutelyQuasiSeparated_terminal :
    IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ
      (⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) := by
  have hTaff : IsAffine (⊤_ Scheme.{u}) :=
    IsAffine.of_isIso (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).inv
  refine isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B (⊤_ Scheme.{u}) hZ _ hZ
    ⟨Over.mk (𝟙 (B.obj hZ)), ?_, ⟨Functor.representableByEquiv.symm
      (isTerminalYonedaObjMkId.uniqueUpToIso terminalIsTerminal)⟩⟩
  show QuasiSeparatedSpace (⊤_ Scheme.{u})
  infer_instance

/-- **An algebraic space over `Spec ℤ` with a surjective étale chart from a quasi-compact scheme
locally of finite type over `Spec ℤ` is of finite type over `Spec ℤ`.** -/
theorem isFiniteType_of_chart {Xs : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Xs) (a : yoneda.obj V ⟶ Xs)
    (ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))) a)
    (has : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))) a)
    [hVc : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V)]
    (hV : LocallyOfFiniteType (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V))) :
    IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ Xs)) := by
  let O : BigFppfOver B (⊤_ Scheme.{u}) hZ := Over.mk (𝟙 (B.obj hZ))
  let eT := (isTerminalYonedaObjMkId (B := B) (hZ := hZ)).uniqueUpToIso terminalIsTerminal
  have hXqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Xs :=
    isQuasiCompactSpace_of_isSurjective B (⊤_ Scheme.{u}) hZ
      (isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ V) hX _
      (isSurjective_of_presheafSurjective B (⊤_ Scheme.{u}) hZ _ has)
      (isQuasiCompactSpace_yoneda_obj B (⊤_ Scheme.{u}) hZ hVc)
  have hlft : IsLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from Xs) := by
    refine isLocallyOfFiniteType_of_holdsOnSurjectiveEtaleChart B (⊤_ Scheme.{u}) hZ
      ⟨V, O, a, eT.hom, homOfScheme (X := V) (Y := O) (terminal.from _),
        ha, ?_, has, terminal.hom_ext _ _, ?_⟩
    · exact presheaf_of_isIso B (⊤_ Scheme.{u}) hZ
        (MorphismProperty.RespectsIso.inverseImage _ _) (fun _ => by
          show Etale ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (𝟙 _))
          rw [CategoryTheory.Functor.map_id]
          infer_instance)
        eT.hom
    · rw [toScheme_map_homOfScheme]
      exact hV
  have hqc : IsQuasiCompact B (⊤_ Scheme.{u}) hZ (terminal.from Xs) :=
    isQuasiCompact_of_isQuasiCompactSpace B (⊤_ Scheme.{u}) hZ hZ
      (isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ) isAbsolutelyQuasiSeparated_terminal hXqc _
  let e := Space.selfIso_viewOverIntegers B hZ Xs
  refine ⟨(isLocallyOfFiniteType_terminal_iff_of_iso B (⊤_ Scheme.{u}) hZ e).mp hlft, ?_⟩
  have hsq : IsPullback e.inv (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ _))
      (terminal.from Xs)
      (𝟙 (⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u))) :=
    IsPullback.of_horiz_isIso ⟨terminal.hom_ext _ _⟩
  exact isQuasiCompact_of_isPullback B (⊤_ Scheme.{u}) hZ hsq hqc

/-- **A glued étale quotient of a quasi-compact scheme of finite type over `Spec ℤ` is of finite
type over `Spec ℤ`.** -/
theorem isFiniteType_quotient [CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V)]
    (hV : LocallyOfFiniteType (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V))) :
    IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ (quotient w hw ι))) :=
  isFiniteType_of_chart (isAlgebraicSpace_quotient w hw ι) (qmap w hw ι) (qmap_etale w hw ι)
    (qmap_surjective w hw ι) hV

end AlgebraicGeometry.Space.GluedEtaleQuotient


/-! ### The step, packaged as a small Noetherian approximation -/

namespace AlgebraicGeometry.Space.GluedEtaleQuotient.System

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
  {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
  {U : Subfunctor X} {Winf Vinf : BigFppfOver B (⊤_ Scheme.{u}) hZ} (f : yoneda.obj Vinf ⟶ X)
  (h : IsElementaryDistinguishedSquare B (⊤_ Scheme.{u}) hZ hX U f)
  (hfs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))) f)
  (winf : yoneda.obj Winf ⟶ U.toFunctor)
  (hwinf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf winf)
  (ιinf : Winf ⟶ Vinf)
  [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ιinf)]
  (hWVsq : IsPullback winf (yoneda.map ιinf) U.ι f)
  {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] (hI : #I < B.cutoff.ord.cof)
  (D : System B hZ Iᵒᵖ)
  (πU : (Functor.const Iᵒᵖ).obj U.toFunctor ⟶ D.base) (πW : (Functor.const Iᵒᵖ).obj Winf ⟶ D.chart)
  (πV : (Functor.const Iᵒᵖ).obj Vinf ⟶ D.ambient)
  (hwU : ∀ j, winf ≫ πU.app j = yoneda.map (πW.app j) ≫ D.toBase.app j)
  (hιV : ∀ j, ιinf ≫ πV.app j = πW.app j ≫ D.incl.app j)
  (hWU : ∀ j, IsPullback (yoneda.map (πW.app j)) winf (D.toBase.app j) (πU.app j))
  (hWV : ∀ j, IsPullback ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (πW.app j))
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ιinf)
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (D.incl.app j))
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (πV.app j)))
  (hVinf : IsLimit (yoneda.mapCone (Cone.mk Vinf πV)))
  (hbase : ∀ j, IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (D.base.obj j))
  (hbaseqs : ∀ j, IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (D.base.obj j))
  (hchart : ∀ j, CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (D.chart.obj j)))
  (hamb : ∀ j, CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (D.ambient.obj j)))
  (hambqs : ∀ j,
    QuasiSeparatedSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (D.ambient.obj j)))
  (hamblft : ∀ j, LocallyOfFiniteType
    (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (D.ambient.obj j))))

include h hfs hwinf hWVsq hI hwU hιV hWU hWV hVinf hbase hbaseqs hchart hamb hambqs hamblft in
/-- **The inductive step of Stacks 07SU**, as a small Noetherian approximation of `X`. -/
theorem hasSmallNoetherianApproximation_of_system :
    HasSmallNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X := by
  have hJ : #(Iᵒᵖ) < B.cutoff.ord.cof := by
    rwa [Cardinal.mk_congr (Opposite.equivToOpposite (α := I)).symm]
  have hJhom : ∀ i j : Iᵒᵖ, #(i ⟶ j) < B.cutoff.ord.cof := fun _ _ =>
    (Cardinal.le_one_iff_subsingleton.mpr inferInstance).trans_lt
      (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff_cof)
  obtain ⟨e, -⟩ := exists_iso_limit_quotients hX f h hfs winf hwinf ιinf hWVsq hJ hJhom D πU πW πV
    hwU hιV hWU hWV hVinf
  refine ⟨NoetherianApproximation.mk (I := I) (diagram := D.quotients)
    (isAlgebraicSpace := D.isAlgebraicSpace_quotients)
    (isAffineHom_map := D.isAffineHom_quotients)
    (isAbsolutelyQuasiSeparated := fun j => ?_)
    (isFiniteTypeOverIntegers := fun j => ?_)
    (π := (Functor.const Iᵒᵖ).map e.hom ≫ (limit.cone D.quotients).π)
    (isLimit := IsLimit.ofIsoLimit (limit.isLimit D.quotients)
      (Cone.ext e.symm fun j => by simp)),
    hI⟩
  · have := hamb j
    have := hambqs j
    have := hchart j
    have := compactSpace_kernelObj (D.toBase.app j) (D.etale j) (hbase j) (hbaseqs j)
    exact isAbsolutelyQuasiSeparated_quotient _ _ _ (hambqs j)
      (quasiCompact_tgt (D.toBase.app j) (D.etale j) (D.incl.app j))
  · have := hamb j
    exact isFiniteType_quotient _ _ _ (hamblft j)

end AlgebraicGeometry.Space.GluedEtaleQuotient.System


/-! ### The trivial approximation -/

namespace AlgebraicGeometry.Space

/-- **A quasi-separated algebraic space of finite type over `Spec ℤ` is its own small Noetherian
approximation**, over a one-point index set. This is the base case of the induction in Stacks
07SU. -/
theorem hasSmallNoetherianApproximation_self {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X)
    (hft : IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ X))) :
    HasSmallNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X :=
  ⟨NoetherianApproximation.mk (I := PUnit.{u + 1})
    (diagram := (Functor.const PUnit.{u + 1}ᵒᵖ).obj X)
    (isAlgebraicSpace := fun _ => hX)
    (isAffineHom_map := fun _ => isAffineHom_of_isIso (𝟙 X))
    (isAbsolutelyQuasiSeparated := fun _ => hqs)
    (isFiniteTypeOverIntegers := fun _ => hft)
    (π := 𝟙 _) (isLimit := isLimitConstCone PUnit.{u + 1}ᵒᵖ X),
    (Cardinal.lt_aleph0_of_finite PUnit.{u + 1}).trans B.aleph0_lt_cutoff_cof⟩

end AlgebraicGeometry.Space

end
