module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.Descend
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NoetherianApproximationInduction

/-!
# Absolute Noetherian approximation

**Stacks 07SU**: a quasi-compact and quasi-separated algebraic space over `Spec ℤ` is the limit
of a directed inverse system of quasi-separated algebraic spaces of finite type over `ℤ` with
affine transition morphisms.

## Main results

* `AlgebraicGeometry.Space.hasNoetherianApproximation_of_isQuasiCompactSpace`: a quasi-compact
  and quasi-separated algebraic space over `Spec ℤ` has a Noetherian approximation.
* `AlgebraicGeometry.Space.hasConventionalNoetherianApproximation_of_etaleAtlas`: the same, with
  an inverse system satisfying the standing convention of Section 70.2 (tag 07SD), for a space
  with a surjective étale atlas by an object of the site.
* `GluedEtaleQuotient.hasConventionalNoetherianApproximation_of_isElementaryDistinguishedSquare`
  (in the namespace `AlgebraicGeometry.Space`): along an elementary distinguished square
  `(U ⊆ X, V ⟶ X)` (Stacks 07ST), a Noetherian approximation of `U` satisfying the convention
  gives one of `X`.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07ST](https://stacks.math.columbia.edu/tag/07ST)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

/-! ### The step, as a conventional Noetherian approximation -/

namespace AlgebraicGeometry.Space.GluedEtaleQuotient.System

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
  {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
  {U : Subfunctor X} {Winf Vinf : BigFppfOver B (⊤_ Scheme.{u}) hZ} (f : yoneda.obj Vinf ⟶ X)
  (h : IsElementaryDistinguishedSquare B (⊤_ Scheme.{u}) hZ hX U f)
  (hfs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)))
      f)
  (winf : yoneda.obj Winf ⟶ U.toFunctor)
  (hwinf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf winf)
  (ιinf : Winf ⟶ Vinf)
  [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ιinf)]
  (hWVsq : IsPullback winf (yoneda.map ιinf) U.ι f)
  {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : System B hZ Iᵒᵖ)
  (πU : (Functor.const Iᵒᵖ).obj U.toFunctor ⟶ D.base)
  (πW : (Functor.const Iᵒᵖ).obj Winf ⟶ D.chart)
  (πV : (Functor.const Iᵒᵖ).obj Vinf ⟶ D.ambient)
  (hwU : ∀ j, winf ≫ πU.app j = yoneda.map (πW.app j) ≫ D.toBase.app j)
  (hιV : ∀ j, ιinf ≫ πV.app j = πW.app j ≫ D.incl.app j)
  (hWU : ∀ j, IsPullback (yoneda.map (πW.app j)) winf (D.toBase.app j) (πU.app j))
  (hWV : ∀ j, IsPullback ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (πW.app j))
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ιinf)
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (D.incl.app j))
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (πV.app j)))
  (hVsch : IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone (Cone.mk Vinf πV)))
  (hbase : ∀ j, IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (D.base.obj j))
  (hbaseqs : ∀ j, IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (D.base.obj j))
  (hchart : ∀ j, CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (D.chart.obj j)))
  (hamb : ∀ j, CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (D.ambient.obj j)))
  (hambqs : ∀ j,
    QuasiSeparatedSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (D.ambient.obj j)))
  (hamblft : ∀ j, LocallyOfFiniteType
    (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (D.ambient.obj j))))

/-- A space whose view over `Spec ℤ` is of finite type over `Spec ℤ` is quasi-compact. -/
private theorem isQuasiCompactSpace_of_isFiniteType_viewOverIntegers
    {F : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (h : IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ F))) :
    IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ F :=
  isQuasiCompactSpace_of_isFiniteType_terminal B hZ
    (isFiniteType_terminal_of_isFiniteType_viewOverIntegers B hZ h)

/-- An étale chart is étale in the relatively representable sense. -/
private theorem presheaf_etale_of_isEtale {U : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    {F : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} {g : yoneda.obj U ⟶ F}
    (hg : IsEtale B (⊤_ Scheme.{u}) hZ g) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf g :=
  (isEtale_iff_presheaf_of_yoneda B (⊤_ Scheme.{u}) hZ g).mp hg

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
include hbase hbaseqs hchart hamb hambqs in
/-- The glued étale quotients of the step are quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_quotients (j : Iᵒᵖ) :
    IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (D.quotients.obj j) := by
  have := hamb j
  have := hambqs j
  have := hchart j
  have := compactSpace_kernelObj (D.toBase.app j) (D.etale j) (hbase j) (hbaseqs j)
  exact isAbsolutelyQuasiSeparated_quotient _ _ _ (hambqs j)
    (quasiCompact_tgt (D.toBase.app j) (D.etale j) (D.incl.app j))

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
include hamb hamblft in
/-- The glued étale quotients of the step are of finite type over `Spec ℤ`. -/
theorem isFiniteType_quotients (j : Iᵒᵖ) :
    IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ (D.quotients.obj j))) := by
  have := hamb j
  exact isFiniteType_quotient _ _ _ (hamblft j)

include hVsch in
/-- The system of glued étale quotients satisfies the standing convention of Section 70.2: its
stages carry the cartesian system of surjective étale charts `V_j`, whose limit `V` is an object
of the site. -/
theorem siteContainsBaseChangeLimits_quotients :
    SiteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ D.quotients :=
  siteContainsBaseChangeLimits_of_chartSystem D.quotients D.ambient D.chartNat
    (fun _ => qmap_surjective _ _ _) (fun _ => qmap_etale _ _ _)
    (fun g => (D.isPullback_chartMap g).flip) _ hVsch Vinf.left.property

include h hfs hwinf hWVsq hwU hιV hWU hWV hVsch hbase hbaseqs hchart hamb hambqs hamblft in
/-- `X` has a Noetherian approximation whose inverse system satisfies the standing convention of
Section 70.2: `X` is the limit of the system of glued étale quotients `Xⱼ = Vⱼ/Rⱼ`. -/
theorem hasConventionalNoetherianApproximation_of_system :
    HasConventionalNoetherianApproximation B hZ X := by
  have hVinf : IsLimit (yoneda.mapCone (Cone.mk Vinf πV)) :=
    isLimitOfPreserves yoneda (isLimitOfIsLimitToScheme hVsch)
  obtain ⟨j₀⟩ := IsCofiltered.nonempty (C := Iᵒᵖ)
  have hR := isPullback_of_isElementaryDistinguishedSquare hX f h winf hwinf ιinf hWVsq
  have hR' := D.isPullback_limitChart_kernel winf hwinf ιinf πU πW πV hwU hιV hWU hWV hVinf
  have hX' : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (limit D.quotients) :=
    isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ D.quotients
      (D.siteContainsBaseChangeLimits_quotients πV hVsch) D.isAlgebraicSpace_quotients
      D.isAffineHom_quotients (fun j => isQuasiCompactSpace_of_isFiniteType_viewOverIntegers
        (D.isFiniteType_quotients hamb hamblft j))
  have hfe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))) f :=
    presheaf_etale_of_isEtale h.isEtale
  have hsq := D.isPullback_limitChart (yoneda.mapCone (Cone.mk Vinf πV)) hVinf j₀
  have hfs' := presheaf_of_isPullback B (⊤_ Scheme.{u}) hZ hsq (qmap_surjective _ _ _)
  have hfe' := presheaf_of_isPullback B (⊤_ Scheme.{u}) hZ hsq (qmap_etale _ _ _)
  obtain ⟨e, -⟩ := exists_iso_of_isomorphic_presentations B (⊤_ Scheme.{u}) hZ hR hR'
    (Iso.refl _) (Category.id_comp _) (Category.id_comp _) hX hX' hfs hfe hfs' hfe'
  exact ⟨NoetherianApproximation.mk (I := I) (diagram := D.quotients)
    (isAlgebraicSpace := D.isAlgebraicSpace_quotients)
    (isAffineHom_map := D.isAffineHom_quotients)
    (isAbsolutelyQuasiSeparated :=
      D.isAbsolutelyQuasiSeparated_quotients hbase hbaseqs hchart hamb hambqs)
    (isFiniteTypeOverIntegers := fun j => D.isFiniteType_quotients hamb hamblft j)
    (π := (Functor.const Iᵒᵖ).map e.hom ≫ (limit.cone D.quotients).π)
    (isLimit := (limit.isLimit D.quotients).ofIsoLimit (Cone.ext e.symm fun j => by simp)),
    D.siteContainsBaseChangeLimits_quotients πV hVsch⟩

end AlgebraicGeometry.Space.GluedEtaleQuotient.System

/-! ### The inductive step -/

namespace AlgebraicGeometry.Space.GluedEtaleQuotient

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}

/-- Let `(U ⊆ X, f : V ⟶ X)` be an elementary distinguished square of quasi-separated algebraic
spaces over `Spec ℤ`, with `f` surjective, `V` a quasi-compact quasi-separated scheme and `U`
quasi-compact. If `U` has a Noetherian approximation whose inverse system satisfies the standing
convention of Section 70.2, so has `X`. -/
theorem hasConventionalNoetherianApproximation_of_isElementaryDistinguishedSquare
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hXqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X)
    {U : Subfunctor X} {V : BigFppfOver B (⊤_ Scheme.{u}) hZ} (f : yoneda.obj V ⟶ X)
    (h : IsElementaryDistinguishedSquare B (⊤_ Scheme.{u}) hZ hX U f)
    (hfs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))) f)
    [CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V)]
    [QuasiSeparatedSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V)]
    (hUqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ U.toFunctor)
    (hU : HasConventionalNoetherianApproximation B hZ U.toFunctor) :
    HasConventionalNoetherianApproximation B hZ X := by
  classical
  let T := BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ
  have hO := h.isOpenSubspace.2
  let P : BigFppfOver B (⊤_ Scheme.{u}) hZ := hO.rep.pullback f
  let winf : yoneda.obj P ⟶ U.toFunctor := hO.rep.fst f
  let ιinf : P ⟶ V := hO.rep.snd f
  have hWVsq : IsPullback winf (yoneda.map ιinf) U.ι f := hO.rep.isPullback f
  have _ : AlgebraicGeometry.IsOpenImmersion (T.map ιinf) := hO.property_snd f
  have hwinf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf
      winf := presheaf_of_isPullback B (⊤_ Scheme.{u}) hZ hWVsq.flip
        (System.presheaf_etale_of_isEtale h.isEtale)
  have _ : CompactSpace (T.obj P) := by
    have hfqc : IsQuasiCompact B (⊤_ Scheme.{u}) hZ f :=
      isQuasiCompact_of_isQuasiCompactSpace B (⊤_ Scheme.{u}) hZ hZ hX hXqs
        (isQuasiCompactSpace_yoneda_obj B (⊤_ Scheme.{u}) hZ inferInstance) f
    have hpb := hfqc U.toFunctor h.isOpenSubspace.1 hUqc U.ι
    exact compactSpace_of_isQuasiCompactSpace_yoneda_obj B (⊤_ Scheme.{u}) hZ
      (IsQuasiCompactSpace.of_iso B (⊤_ Scheme.{u}) hZ hpb (hWVsq.isoPullback).symm)
  have _ : QuasiSeparatedSpace (T.obj P) := quasiSeparatedSpace_of_quasiSeparated (T.map ιinf)
  obtain ⟨A, hconvA⟩ := hU
  let _ := A.preorder
  let _ := A.nonempty
  let _ := A.isDirected
  have hAqc : ∀ i, IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (A.diagram.obj i) := fun i =>
    System.isQuasiCompactSpace_of_isFiniteType_viewOverIntegers (A.isFiniteTypeOverIntegers i)
  obtain ⟨i₀, Ws, ws, πW, hws', hwscart, hWscpt, hWslft, hWsaff, -, hπWcart, ⟨hWslim⟩⟩ :=
    exists_etaleSchemeSystem_of_isLimit A.diagram hconvA A.isAlgebraicSpace A.isAffineHom_map
      hAqc A.isAbsolutelyQuasiSeparated A.isFiniteTypeOverIntegers A.π
      A.isLimit P inferInstance inferInstance winf
      ((isEtale_iff_presheaf_of_yoneda B (⊤_ Scheme.{u}) hZ winf).mpr hwinf)
  have hws : ∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      T).presheaf (ws.app i) := fun i =>
    System.presheaf_etale_of_isEtale (hws' i)
  let I' := {i : A.I // i₀ ≤ i}
  have _ : Nonempty I' := ⟨⟨i₀, le_rfl⟩⟩
  have _ : IsDirected I' (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩⟩
  let D' : I'ᵒᵈ ⥤ Scheme.{u} := (orderDualEquivalence I').functor ⋙ Ws ⋙ T
  have _ : ∀ {i j : I'ᵒᵈ} (v : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom (D'.map v) :=
    fun v => hWsaff _
  have _ : ∀ i, CompactSpace (D'.obj i) := fun i => hWscpt _
  have _ : ∀ i, LocallyOfFiniteType (terminal.from (D'.obj i)) := fun i => hWslft _
  have _ : ∀ i, QuasiCompact (terminal.from (D'.obj i)) := fun i =>
    (compactSpace_iff_quasiCompact _).mp inferInstance
  let Uo : (T.obj V).Opens := (T.map ιinf).opensRange
  let isoUo : T.obj P ≅ Uo := (T.map ιinf).isoOpensRange
  have _ : CompactSpace (Uo : Scheme.{u}) := isoUo.hom.homeomorph.compactSpace
  let c₁ := (T.mapCone (Cone.mk P πW)).whisker (orderDualEquivalence I').functor
  have hc₁ : IsLimit c₁ := hWslim.whiskerEquivalence _
  let p : (Functor.const I'ᵒᵈ).obj (Uo : Scheme.{u}) ⟶ D' :=
    (Functor.const I'ᵒᵈ).map isoUo.inv ≫ c₁.π
  have hp : IsLimit (Cone.mk (Uo : Scheme.{u}) p) :=
    hc₁.ofIsoLimit (Cone.ext isoUo (fun j => by simp [p]))
  obtain ⟨Q, -, -⟩ := exists_finiteTypeApproximation_card_le D' (T.obj V) Uo p hp
  let J := Q.indexType
  let _ := Q.indexPreorder
  let _ := Q.indexNonempty
  let _ := Q.indexDirected
  have _ := Q.inclusion_isOpenImmersion
  have hcont : ∀ j, B.Contains (Q.ambient.obj j) := fun j => by
    have := Q.locallyOfFiniteType j
    have := Q.quasiCompact j
    exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (terminal.from _) hZ
  let e' : Jᵒᵖ ⥤ I'ᵒᵖ := Q.index.monotone.functor.op
  let dJ : Jᵒᵖ ⥤ Jᵒᵈ := (orderDualEquivalence J).inverse
  let ambient : Jᵒᵖ ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ := dJ ⋙ liftDiagram Q.ambient hcont
  let inclApp (j : Jᵒᵖ) : (e' ⋙ Ws).obj j ⟶ ambient.obj j :=
    homOfScheme (Q.comparison.inv.app (dJ.obj j) ≫ Q.inclusion.app (dJ.obj j))
  have hT_incl (j : Jᵒᵖ) : T.map (inclApp j) =
      Q.comparison.inv.app (dJ.obj j) ≫ Q.inclusion.app (dJ.obj j) := toScheme_map_homOfScheme _
  let incl : e' ⋙ Ws ⟶ ambient :=
    { app := inclApp
      naturality := fun a b g => T.map_injective (by
        rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hT_incl, hT_incl]
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ Q.inclusion.app (dJ.obj b))
            (Q.comparison.inv.naturality (dJ.map g))).trans
          ((Category.assoc _ _ _).trans
          ((congrArg (Q.comparison.inv.app (dJ.obj a) ≫ ·)
            (Q.inclusion.naturality (dJ.map g))).trans
          (Category.assoc _ _ _).symm)))) }
  let D : System B hZ Jᵒᵖ :=
    { base := e' ⋙ (Subtype.mono_coe (fun i : A.I => i₀ ≤ i)).functor.op ⋙ A.diagram
      chart := e' ⋙ Ws
      ambient := ambient
      toBase := Functor.whiskerLeft e' ws
      incl := incl
      etale := fun j => hws _
      isOpenImmersion := fun j => by
        change AlgebraicGeometry.IsOpenImmersion (T.map (inclApp j))
        have h₁ : AlgebraicGeometry.IsOpenImmersion (Q.comparison.inv.app (dJ.obj j)) :=
          AlgebraicGeometry.IsOpenImmersion.of_isIso _
        have h₂ := Q.inclusion_isOpenImmersion (dJ.obj j)
        rw [hT_incl]
        exact @AlgebraicGeometry.IsOpenImmersion.comp _ _ _ _ _ h₁ h₂
      isPullback_base := fun g => hwscart (e'.map g)
      isPullback_ambient := fun {a b} g => by
        change IsPullback (T.map ((e' ⋙ Ws).map g)) (T.map (inclApp a)) (T.map (inclApp b))
          (Q.ambient.map (dJ.map g))
        rw [hT_incl, hT_incl]
        change IsPullback (D'.map (Q.index.monotone.dual.functor.map (dJ.map g)))
          (Q.comparison.inv.app (dJ.obj a) ≫ Q.inclusion.app (dJ.obj a))
          (Q.comparison.inv.app (dJ.obj b) ≫ Q.inclusion.app (dJ.obj b))
          (Q.ambient.map (dJ.map g))
        exact (Q.transition_isPullback (dJ.map g)).of_iso (Q.comparison.app _)
          (Q.comparison.app _) (Iso.refl _) (Iso.refl _) (Q.comparison.hom.naturality _)
          ((Category.comp_id _).trans (Q.comparison.hom_inv_id_app_assoc _ _).symm)
          ((Category.comp_id _).trans (Q.comparison.hom_inv_id_app_assoc _ _).symm)
          ((Category.comp_id _).trans (Category.id_comp _).symm)
      isAffineHom_ambient := fun g => Q.transition_affine (dJ.map g) }
  let πU : (Functor.const Jᵒᵖ).obj U.toFunctor ⟶ D.base :=
    { app := fun j => A.π.app (op (Q.index j.unop).1)
      naturality := fun a b g => A.π.naturality _ }
  let πW' : (Functor.const Jᵒᵖ).obj P ⟶ D.chart :=
    { app := fun j => πW.app (e'.obj j)
      naturality := fun a b g => πW.naturality (e'.map g) }
  let πVApp (j : Jᵒᵖ) : V ⟶ ambient.obj j :=
    homOfScheme (show T.obj V ⟶ T.obj (ambient.obj j) from Q.ambientCone.app (dJ.obj j))
  have hπV (j : Jᵒᵖ) : T.map (πVApp j) = Q.ambientCone.app (dJ.obj j) :=
    toScheme_map_homOfScheme _
  let πV : (Functor.const Jᵒᵖ).obj V ⟶ ambient :=
    { app := πVApp
      naturality := fun a b g => T.map_injective (by
        rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hπV, hπV]
        exact Q.ambientCone.naturality (dJ.map g)) }
  have hopenCone (j : Jᵒᵖ) : Q.openCone.app (dJ.obj j) =
      (isoUo.inv ≫ T.map (πW.app (e'.obj j))) ≫ Q.comparison.inv.app (dJ.obj j) :=
    ((Category.comp_id _).symm.trans ((congrArg (Q.openCone.app (dJ.obj j) ≫ ·)
      (Q.comparison.hom_inv_id_app (dJ.obj j))).symm.trans (Category.assoc _ _ _).symm)).trans
      (congrArg (· ≫ Q.comparison.inv.app (dJ.obj j)) (Q.comparison_compatibility (dJ.obj j)))
  have hιV' (j : Jᵒᵖ) : T.map ιinf ≫ Q.ambientCone.app (dJ.obj j) =
      T.map (πW.app (e'.obj j)) ≫ (Q.comparison.inv.app (dJ.obj j) ≫
        Q.inclusion.app (dJ.obj j)) := by
    have e1 : T.map ιinf = isoUo.hom ≫ Uo.ι := (Scheme.Hom.isoOpensRange_hom_ι _).symm
    rw [e1, Category.assoc, Q.inclusion_compatibility (dJ.obj j), hopenCone]
    exact (congrArg (isoUo.hom ≫ ·) ((Category.assoc _ _ _).trans
      (Category.assoc _ _ _))).trans (isoUo.hom_inv_id_assoc _)
  have hιV (j : Jᵒᵖ) : ιinf ≫ πV.app j = πW'.app j ≫ incl.app j := T.map_injective (by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    change T.map ιinf ≫ T.map (πVApp j) = T.map (πW.app (e'.obj j)) ≫ T.map (inclApp j)
    rw [hπV, hT_incl]
    exact hιV' j)
  have hWV (j : Jᵒᵖ) : IsPullback (T.map (πW'.app j)) (T.map ιinf) (T.map (incl.app j))
      (T.map (πV.app j)) := by
    have hsq := isPullback_of_isLimit_of_cartesian Q.inclusion
      (fun g => Q.transition_isPullback g) Q.openCone_isLimit Q.ambientCone_isLimit Uo.ι
      (fun x => (Q.inclusion_compatibility x).symm) (dJ.obj j)
    change IsPullback (T.map (πW.app (e'.obj j))) (T.map ιinf) (T.map (inclApp j))
      (T.map (πVApp j))
    rw [hT_incl, hπV]
    have c1 : Q.openCone.app (dJ.obj j) ≫ Q.comparison.hom.app (dJ.obj j) =
        isoUo.inv ≫ T.map (πW.app (e'.obj j)) := by
      rw [hopenCone]
      exact (Category.assoc _ _ _).trans ((congrArg _ (Q.comparison.inv_hom_id_app _)).trans
        (Category.comp_id _))
    have c2 : Uo.ι ≫ 𝟙 (T.obj V) = isoUo.inv ≫ T.map ιinf :=
      (Category.comp_id _).trans (Scheme.Hom.isoOpensRange_inv_comp _).symm
    exact hsq.of_iso isoUo.symm (Q.comparison.app _) (Iso.refl _) (Iso.refl _) c1 c2
      ((Category.comp_id _).trans (Q.comparison.hom_inv_id_app_assoc _ _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hVsch : IsLimit (T.mapCone (Cone.mk V πV)) :=
    (Q.ambientCone_isLimit.whiskerEquivalence (orderDualEquivalence J).symm).ofIsoLimit
      (Cone.ext (Iso.refl _) (fun j => (Category.id_comp _).trans (hπV j).symm))
  refine System.hasConventionalNoetherianApproximation_of_system hX f h hfs winf hwinf ιinf
    hWVsq D πU πW' πV (fun j => (hπWcart (e'.obj j)).w.symm) hιV
    (fun j => hπWcart (e'.obj j)) hWV hVsch
    (fun j => A.isAlgebraicSpace _) (fun j => A.isAbsolutelyQuasiSeparated _)
    (fun j => hWscpt _) (fun j => (compactSpace_iff_quasiCompact _).mpr (Q.quasiCompact _))
    (fun j => ?_) (fun j => Q.locallyOfFiniteType _)
  have := Q.locallyOfFiniteType (dJ.obj j)
  have := (compactSpace_iff_quasiCompact _).mpr (Q.quasiCompact (dJ.obj j))
  have _ : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have _ : IsLocallyNoetherian (⊤_ Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).inv
  have _ : IsLocallyNoetherian (Q.ambient.obj (dJ.obj j)) :=
    LocallyOfFiniteType.isLocallyNoetherian (terminal.from _)
  change QuasiSeparatedSpace (Q.ambient.obj (dJ.obj j))
  infer_instance

end AlgebraicGeometry.Space.GluedEtaleQuotient

/-! ### The induction over the filtration of Stacks 07ST -/

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}

/-- A quasi-compact quasi-separated algebraic space over `Spec ℤ` with a surjective étale atlas by
an object of the site has a Noetherian approximation whose inverse system satisfies the standing
convention of Section 70.2. -/
theorem hasConventionalNoetherianApproximation_of_etaleAtlas
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X)
    (hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X)
    (A : BigFppfOver B (⊤_ Scheme.{u}) hZ) (a : yoneda.obj A ⟶ X)
    (haSurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf a)
    (haEtale : IsEtale B (⊤_ Scheme.{u}) hZ a) :
    HasConventionalNoetherianApproximation B hZ X := by
  classical
  obtain ⟨n, U, V, f, hU0, -, ⟨eUn⟩, hUopen, hUle, hstep⟩ :=
    exists_finiteFiltration_isElementaryDistinguishedSquare B (⊤_ Scheme.{u}) hZ hZ X hX hqc hqs
      A a haSurj haEtale
  have hempty : HasConventionalNoetherianApproximation B hZ
      (yoneda.obj (BigFppfOver.initialObj B (⊤_ Scheme.{u}) hZ)) := by
    obtain ⟨A₀, hA₀⟩ := hasSmallNoetherianApproximation_initialObj (B := B) (hZ := hZ)
    let _ := A₀.preorder
    let _ := A₀.nonempty
    let _ := A₀.isDirected
    exact ⟨A₀, IsSiteSmall.siteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ A₀.diagram
      (IsSiteSmall.of_lt_cof_op hA₀)⟩
  have hUnqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (U n).toFunctor := by
    have _ : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
        (BigFppfOver.initialObj B (⊤_ Scheme.{u}) hZ)) :=
      have : IsEmpty ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
          (BigFppfOver.initialObj B (⊤_ Scheme.{u}) hZ)) :=
        inferInstanceAs (IsEmpty (∅ : Scheme.{u}))
      inferInstance
    exact IsQuasiCompactSpace.of_iso B (⊤_ Scheme.{u}) hZ
      (isQuasiCompactSpace_yoneda_obj B (⊤_ Scheme.{u}) hZ inferInstance) eUn.symm
  have hrange : ∀ m (hle : U (m + 1) ≤ U m), Subfunctor.range (Subfunctor.homOfLe hle) =
      (U (m + 1)).preimage (U m).ι := fun m hle => by
    ext Y x
    refine ⟨?_, fun hx => ⟨⟨x.1, hx⟩, rfl⟩⟩
    rintro ⟨y, rfl⟩
    exact y.2
  have key : ∀ m, m ≤ n → HasConventionalNoetherianApproximation B hZ (U m).toFunctor := by
    intro m hm
    refine Nat.decreasingInduction
      (motive := fun m _ => HasConventionalNoetherianApproximation B hZ (U m).toFunctor)
      (fun m hm ih => ?_) (hempty.ofIso eUn.symm) hm
    let p : Fin n := ⟨m, hm⟩
    obtain ⟨⟨hW, hsq⟩, hfs, -, hVc, hVsep, -, hUqc⟩ := hstep p
    have hle := hUle m hm
    let eU : (U (m + 1)).toFunctor ≅ ((U (m + 1)).preimage (U m).ι).toFunctor :=
      asIso (Subfunctor.toRange (Subfunctor.homOfLe hle)) ≪≫
        eqToIso (congrArg Subfunctor.toFunctor (hrange m hle))
    have hUqc' : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ
        ((U (m + 1)).preimage (U m).ι).toFunctor := by
      refine IsQuasiCompactSpace.of_iso B (⊤_ Scheme.{u}) hZ ?_ eU
      rcases Nat.lt_or_ge (m + 1) n with h' | h'
      · exact (hstep ⟨m + 1, h'⟩).2.2.2.2.2.2
      · rw [show m + 1 = n by omega]
        exact hUnqc
    have hmqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (U m).toFunctor :=
      isAbsolutelyQuasiSeparated_of_mono _ _ _ _ hW (U m).ι inferInstance hqs
    have _ := hVc
    have _ : QuasiSeparatedSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (V p)) :=
      inferInstance
    exact
      GluedEtaleQuotient.hasConventionalNoetherianApproximation_of_isElementaryDistinguishedSquare
        hW hmqs (f p) hsq hfs hUqc' (ih.ofIso eU)
  have h0 := key 0 (Nat.zero_le n)
  rw [hU0] at h0
  exact h0.ofIso (asIso (⊤ : Subfunctor X).ι)

/-- Absolute Noetherian approximation. Let `X` be a quasi-compact and quasi-separated algebraic
space over `Spec ℤ`, the terminal scheme `⊤_ Scheme`, on the big fppf site `B`. Then there are a
directed set `I` and an inverse system `(X_i)` of algebraic spaces over `I` such that
(1) the transition morphisms are affine, (2) each `X_i` is quasi-separated and of finite type
over `ℤ`, and (3) `X = lim X_i`, the limit being taken in presheaves on the site.

The hypotheses are exactly those of the source, and nothing further is assumed: `X` is written
as a limit by the descending induction over the strata of Stacks 07ST, through
`AlgebraicGeometry.Space.hasConventionalNoetherianApproximation_of_etaleAtlas`. -/
@[stacks 07SU]
theorem hasNoetherianApproximation_of_isQuasiCompactSpace
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X)
    (hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X) :
    HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X := by
  obtain ⟨A, a, -, has, hae⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B (⊤_ Scheme.{u}) hZ X hX).mp
      hqc
  exact (hasConventionalNoetherianApproximation_of_etaleAtlas hX hqc hqs A a has
    hae).hasNoetherianApproximation

end AlgebraicGeometry.Space

end
