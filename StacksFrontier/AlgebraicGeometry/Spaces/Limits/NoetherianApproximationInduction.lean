module

public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.CardinalBound
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiltrationElementarySquares
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EtaleSchemeModelDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NoetherianApproximationStep
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms

/-!
# Absolute Noetherian approximation for algebraic spaces (Stacks 07SU)

A quasi-compact and quasi-separated algebraic space `X` over `Spec ℤ` is the limit of a directed
inverse system of quasi-separated algebraic spaces of finite type over `Spec ℤ` with affine
transition morphisms, indexed by a set small for the site.

The proof is the one of the Stacks project (after Conrad, Lieblich and Olsson): by Stacks 07ST,
`X` is built from the empty space by finitely many elementary distinguished squares
`(U ⊆ X, f : V ⟶ X)` with `V` a quasi-compact separated scheme; by induction `U = lim Uᵢ`; the
étale scheme `W = V ×_X U` over `U` descends to étale schemes `Wᵢ ⟶ Uᵢ` (Stacks 07SR); the
quasi-compact open `W ⊆ V` extends to open immersions `Wᵢ ⊆ Vᵢ` of schemes of finite type over
`Spec ℤ` with `V = lim Vᵢ` (Stacks 07RN); and `X` is the limit of the glued étale quotients
`Vᵢ ⊔_{Wᵢ} (Wᵢ ×_{Uᵢ} Wᵢ)`.

The index sets are kept below the cofinality of the size cutoff of the site, which is what
Stacks 07SF needs for the limits to exist; the price is that the étale atlas of `X` has to be
smaller than that cofinality.

## Main results

* `AlgebraicGeometry.Space.hasSmallNoetherianApproximation_of_isElementaryDistinguishedSquare`:
  the inductive step.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space.GluedEtaleQuotient

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}

/-- The terminal scheme is terminal among the schemes of the site. -/
def isTerminal_obj_terminal : IsTerminal (B.obj hZ) :=
  IsTerminal.ofUniqueHom (fun Y => B.inclusion.preimage (terminal.from (B.inclusion.obj Y)))
    (fun _ _ => B.inclusion.map_injective (terminal.hom_ext _ _))

/-- A diagram of schemes contained in the site, regarded as a diagram in the site over
`Spec ℤ`. -/
def liftDiagram {J : Type*} [Category J] (F : J ⥤ Scheme.{u}) (hF : ∀ j, B.Contains (F.obj j)) :
    J ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ :=
  ObjectProperty.lift _ F hF ⋙
    (Over.equivalenceOfIsTerminal (isTerminal_obj_terminal (hZ := hZ))).inverse

/-- The underlying morphism of schemes of `(liftDiagram F hF).map g` is `F.map g`. -/
@[simp]
theorem toScheme_map_liftDiagram {J : Type*} [Category J] (F : J ⥤ Scheme.{u})
    (hF : ∀ j, B.Contains (F.obj j)) {a b : J} (g : a ⟶ b) :
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ((liftDiagram (hZ := hZ) F hF).map g) =
      F.map g :=
  rfl

/-- **Over `Spec ℤ`, a cone of the site whose underlying cone of schemes is a limit is a limit.**
Every morphism of schemes between objects of the site over the terminal scheme is a morphism of
the site. -/
def isLimitOfIsLimitToScheme {J : Type*} [Category J] {F : J ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ}
    {c : Cone F} (hc : IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone c)) :
    IsLimit c :=
  IsLimit.ofFaithful (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ) hc
    (fun s => homOfScheme (hc.lift ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone s)))
    (fun _ => toScheme_map_homOfScheme _)

/-- An isomorphism of presheaves on the site satisfies the presheaf property attached to any
property of schemes that is multiplicative and stable under base change. -/
private theorem presheaf_inverseImage_of_isIso {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] [P.IsMultiplicative]
    {F G : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (e : F ⟶ G) [IsIso e] :
    (P.inverseImage (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf e :=
  have := MorphismProperty.IsStableUnderBaseChange.respectsIso (P := P)
  presheaf_of_isIso B (⊤_ Scheme.{u}) hZ (MorphismProperty.RespectsIso.inverseImage _ _)
    (fun _ => by simpa using P.id_mem _) e

/-- **An object of the site with an étale morphism to an algebraic space of finite type over
`Spec ℤ` is locally of finite type over `Spec ℤ`.** -/
theorem locallyOfFiniteType_of_etale {Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hY : IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ Y)))
    {W : BigFppfOver B (⊤_ Scheme.{u}) hZ} (w : yoneda.obj W ⟶ Y)
    (hw : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf w) :
    LocallyOfFiniteType (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj W)) := by
  let O : BigFppfOver B (⊤_ Scheme.{u}) hZ := Over.mk (𝟙 (B.obj hZ))
  have hterm : IsTerminal (yoneda.obj O) :=
    (Over.mkIdTerminal (X := B.obj hZ)).isTerminalObj yoneda _
  let eT := hterm.uniqueUpToIso terminalIsTerminal
  have hlft := (isFiniteType_terminal_of_isFiniteType_viewOverIntegers B hZ hY).1
  have hO : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf eT.hom :=
    presheaf_inverseImage_of_isIso eT.hom
  have := hlft W O w eT.hom (homOfScheme (X := W) (Y := O) (terminal.from _)) hw hO
    (terminal.hom_ext _ _)
  rwa [toScheme_map_homOfScheme] at this

/-- **The inductive step of Stacks 07SU.** Let `(U ⊆ X, f : V ⟶ X)` be an elementary
distinguished square of quasi-separated algebraic spaces over `Spec ℤ`, with `f` surjective, `V` a
quasi-compact quasi-separated scheme smaller than the cofinality of the size cutoff and `U`
quasi-compact. If `U` has a small Noetherian approximation, so has `X`. -/
theorem hasSmallNoetherianApproximation_of_isElementaryDistinguishedSquare
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
    (hVsize : ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V).size < B.cutoff.ord.cof)
    (hUqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ U.toFunctor)
    (hU : HasSmallNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ U.toFunctor) :
    HasSmallNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X := by
  classical
  let T := BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ
  -- the open `W = V ×_X U` of `V`
  have hO := h.isOpenSubspace.2
  let P : BigFppfOver B (⊤_ Scheme.{u}) hZ := hO.rep.pullback f
  let winf : yoneda.obj P ⟶ U.toFunctor := hO.rep.fst f
  let ιinf : P ⟶ V := hO.rep.snd f
  have hWVsq : IsPullback winf (yoneda.map ιinf) U.ι f := hO.rep.isPullback f
  have _ : AlgebraicGeometry.IsOpenImmersion (T.map ιinf) := hO.property_snd f
  have hfe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) T)) f :=
    (isEtale_iff_presheaf_of_yoneda B (⊤_ Scheme.{u}) hZ f).mp h.isEtale
  have hwinf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf
      winf := presheaf_of_isPullback B (⊤_ Scheme.{u}) hZ hWVsq.flip hfe
  have _ : CompactSpace (T.obj P) := by
    have hfqc : IsQuasiCompact B (⊤_ Scheme.{u}) hZ f :=
      isQuasiCompact_of_isQuasiCompactSpace B (⊤_ Scheme.{u}) hZ hZ hX hXqs
        (isQuasiCompactSpace_yoneda_obj B (⊤_ Scheme.{u}) hZ inferInstance) f
    have hpb := hfqc U.toFunctor h.isOpenSubspace.1 hUqc U.ι
    exact compactSpace_of_isQuasiCompactSpace_yoneda_obj B (⊤_ Scheme.{u}) hZ
      (IsQuasiCompactSpace.of_iso B (⊤_ Scheme.{u}) hZ hpb (hWVsq.isoPullback).symm)
  have _ : QuasiSeparatedSpace (T.obj P) := quasiSeparatedSpace_of_quasiSeparated (T.map ιinf)
  -- the approximation of `U`, and the scheme models `Wᵢ ⟶ Uᵢ` of `W ⟶ U`
  obtain ⟨A, hAI⟩ := hU
  let _ := A.preorder
  let _ := A.nonempty
  let _ := A.isDirected
  have hAqc : ∀ i, IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (A.diagram.obj i) := fun i =>
    isQuasiCompactSpace_of_isFiniteType_terminal B hZ
      (isFiniteType_terminal_of_isFiniteType_viewOverIntegers B hZ (A.isFiniteTypeOverIntegers i))
  obtain ⟨i₀, Ws, ws, πW, hws, hwscart, hπWcart, hWsaff, hWscqs, ⟨hWslim⟩⟩ :=
    exists_etale_scheme_models B hZ hAI A.diagram A.isAlgebraicSpace hAqc
      A.isAbsolutelyQuasiSeparated A.isAffineHom_map A.π A.isLimit winf hwinf
  -- the index set `{i ≥ i₀}` and the system `Wᵢ` as an inverse system of schemes
  let I' := {i : A.I // i₀ ≤ i}
  have _ : Nonempty I' := ⟨⟨i₀, le_rfl⟩⟩
  have _ : IsDirected I' (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩⟩
  let D' : I'ᵒᵈ ⥤ Scheme.{u} := (orderDualEquivalence I').functor ⋙ Ws ⋙ T
  have _ : ∀ {i j : I'ᵒᵈ} (v : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom (D'.map v) :=
    fun v => hWsaff _
  have _ : ∀ i, CompactSpace (D'.obj i) := fun i => (hWscqs _).1
  have _ : ∀ i, LocallyOfFiniteType (terminal.from (D'.obj i)) := fun i =>
    locallyOfFiniteType_of_etale (A.isFiniteTypeOverIntegers _) _ (hws _)
  have _ : ∀ i, QuasiCompact (terminal.from (D'.obj i)) := fun i =>
    (compactSpace_iff_quasiCompact _).mp inferInstance
  -- the open `W` of `V` as an open subscheme, and its cone over the `Wᵢ`
  let Uo : (T.obj V).Opens := (T.map ιinf).opensRange
  let isoUo : T.obj P ≅ Uo := (T.map ιinf).isoOpensRange
  have _ : CompactSpace (Uo : Scheme.{u}) :=
    isoUo.hom.homeomorph.compactSpace
  let c₁ := (T.mapCone (Cone.mk P πW)).whisker (orderDualEquivalence I').functor
  have hc₁ : IsLimit c₁ := hWslim.whiskerEquivalence _
  let p : (Functor.const I'ᵒᵈ).obj (Uo : Scheme.{u}) ⟶ D' :=
    (Functor.const I'ᵒᵈ).map isoUo.inv ≫ c₁.π
  have hp : IsLimit (Cone.mk (Uo : Scheme.{u}) p) :=
    hc₁.ofIsoLimit (Cone.ext isoUo (fun j => by simp [p]))
  -- Stacks 07RN, with a bounded index set
  obtain ⟨Q, -, hQcard⟩ := exists_finiteTypeApproximation_card_le D' (T.obj V) Uo p hp
  let J := Q.indexType
  let _ := Q.indexPreorder
  let _ := Q.indexNonempty
  let _ := Q.indexDirected
  have _ := Q.inclusion_isOpenImmersion
  have hcont : ∀ j, B.Contains (Q.ambient.obj j) := fun j => by
    have := Q.locallyOfFiniteType j
    have := Q.quasiCompact j
    exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (terminal.from _) hZ
  -- the reindexing `Jᵒᵖ ⥤ {i ≥ i₀}ᵒᵖ`
  let e' : Jᵒᵖ ⥤ I'ᵒᵖ := Q.index.monotone.functor.op
  let dJ : Jᵒᵖ ⥤ Jᵒᵈ := (orderDualEquivalence J).inverse
  let ambient : Jᵒᵖ ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ := dJ ⋙ liftDiagram Q.ambient hcont
  let inclApp (j : Jᵒᵖ) : (e' ⋙ Ws).obj j ⟶ ambient.obj j :=
    homOfScheme (Q.comparison.inv.app (dJ.obj j) ≫ Q.inclusion.app (dJ.obj j))
  have hT_incl (j : Jᵒᵖ) : T.map (inclApp j) =
      Q.comparison.inv.app (dJ.obj j) ≫ Q.inclusion.app (dJ.obj j) := toScheme_map_homOfScheme _
  have hobj (a : Jᵒᵖ) : D'.obj (Q.index.monotone.dual.functor.obj (dJ.obj a)) =
      T.obj ((e' ⋙ Ws).obj a) := rfl
  have hT_chart {a b : Jᵒᵖ} (g : a ⟶ b) :
      T.map ((e' ⋙ Ws).map g) = D'.map (Q.index.monotone.dual.functor.map (dJ.map g)) := rfl
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
        refine (Q.transition_isPullback (dJ.map g)).of_iso (Q.comparison.app _)
          (Q.comparison.app _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
        · exact Q.comparison.hom.naturality _
        · exact (Category.comp_id _).trans (Q.comparison.hom_inv_id_app_assoc _ _).symm
        · exact (Category.comp_id _).trans (Q.comparison.hom_inv_id_app_assoc _ _).symm
        · exact (Category.comp_id _).trans (Category.id_comp _).symm
      isAffineHom_ambient := fun g => Q.transition_affine (dJ.map g) }
  -- the limit cones of `U`, `W` and `V`
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
    have e2 := Q.inclusion_compatibility (dJ.obj j)
    calc T.map ιinf ≫ Q.ambientCone.app (dJ.obj j)
        = isoUo.hom ≫ (Uo.ι ≫ Q.ambientCone.app (dJ.obj j)) := by
          rw [e1, Category.assoc]
      _ = isoUo.hom ≫ (Q.openCone.app (dJ.obj j) ≫ Q.inclusion.app (dJ.obj j)) := by rw [e2]
      _ = _ := by
          rw [hopenCone]
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
  have hVinf : IsLimit (yoneda.mapCone (Cone.mk V πV)) := by
    refine isLimitOfPreserves yoneda (isLimitOfIsLimitToScheme ?_)
    exact (Q.ambientCone_isLimit.whiskerEquivalence (orderDualEquivalence J).symm).ofIsoLimit
      (Cone.ext (Iso.refl _) (fun j => (Category.id_comp _).trans (hπV j).symm))
  have hJ : #J < B.cutoff.ord.cof := hQcard.trans_lt (max_lt
    ((Cardinal.mk_subtype_le _).trans_lt hAI) hVsize)
  refine System.hasSmallNoetherianApproximation_of_system hX f h hfs winf hwinf ιinf hWVsq hJ D
    πU πW' πV
    (fun j => (hπWcart (e'.obj j)).w.symm) hιV (fun j => hπWcart (e'.obj j)) hWV hVinf
    (fun j => A.isAlgebraicSpace _) (fun j => A.isAbsolutelyQuasiSeparated _)
    (fun j => (hWscqs _).1) (fun j => ?_) (fun j => ?_) (fun j => Q.locallyOfFiniteType _)
  · exact (compactSpace_iff_quasiCompact _).mpr (Q.quasiCompact _)
  · have := Q.locallyOfFiniteType (dJ.obj j)
    have := (compactSpace_iff_quasiCompact _).mpr (Q.quasiCompact (dJ.obj j))
    have _ : IsNoetherianRing (ULift.{u} ℤ) :=
      isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
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

/-- A presheaf isomorphic to one with a small Noetherian approximation has one. -/
theorem HasSmallNoetherianApproximation.of_iso
    {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (h : HasSmallNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X) (e : X ≅ Y) :
    HasSmallNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ Y := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A.ofIso e, hA⟩

/-- The empty space has a small Noetherian approximation. -/
theorem hasSmallNoetherianApproximation_initialObj :
    HasSmallNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ
      (yoneda.obj (BigFppfOver.initialObj B (⊤_ Scheme.{u}) hZ)) := by
  let I := BigFppfOver.initialObj B (⊤_ Scheme.{u}) hZ
  have hI : IsEmpty ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj I) :=
    inferInstanceAs (IsEmpty (∅ : Scheme.{u}))
  have _ : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj I) := inferInstance
  have hIalg := isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ I
  refine hasSmallNoetherianApproximation_self hIalg ?_ ?_
  · exact isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B (⊤_ Scheme.{u}) hZ _ hZ
      ⟨I, inferInstance, ⟨Functor.representableByEquiv.symm (Iso.refl _)⟩⟩
  · refine GluedEtaleQuotient.isFiniteType_of_chart hIalg (𝟙 _) ?_ ?_
      (locallyOfFiniteType_terminal_from_of_isEmpty _)
    · exact GluedEtaleQuotient.presheaf_inverseImage_of_isIso _
    · exact GluedEtaleQuotient.presheaf_inverseImage_of_isIso _

/-- **Absolute Noetherian approximation (Stacks 07SU), for an algebraic space with a small étale
atlas.** A quasi-compact quasi-separated algebraic space over `Spec ℤ` with a surjective étale
atlas by a scheme smaller than the cofinality of the size cutoff is the limit of a directed
inverse system, indexed by a set smaller than that cofinality, of quasi-separated algebraic spaces
of finite type over `Spec ℤ` with affine transition morphisms. -/
theorem hasSmallNoetherianApproximation_of_etaleAtlas
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X)
    (hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X)
    (A : BigFppfOver B (⊤_ Scheme.{u}) hZ) (a : yoneda.obj A ⟶ X)
    (haSurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf a)
    (haEtale : IsEtale B (⊤_ Scheme.{u}) hZ a)
    (hA : ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj A).size < B.cutoff.ord.cof) :
    HasSmallNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X := by
  classical
  obtain ⟨n, U, V, f, hU0, -, ⟨eUn⟩, hUopen, hUle, hstep⟩ :=
    exists_finiteFiltration_isElementaryDistinguishedSquare B (⊤_ Scheme.{u}) hZ hZ X hX hqc hqs
      A a haSurj haEtale
  have hempty := hasSmallNoetherianApproximation_initialObj (B := B) (hZ := hZ)
  have hUnqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (U n).toFunctor := by
    have : IsEmpty ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
        (BigFppfOver.initialObj B (⊤_ Scheme.{u}) hZ)) :=
      inferInstanceAs (IsEmpty (∅ : Scheme.{u}))
    exact IsQuasiCompactSpace.of_iso B (⊤_ Scheme.{u}) hZ
      (isQuasiCompactSpace_yoneda_obj B (⊤_ Scheme.{u}) hZ inferInstance) eUn.symm
  -- the range of `U (m + 1) ⊆ U m` is the preimage subfunctor
  have hrange : ∀ m (hle : U (m + 1) ≤ U m), Subfunctor.range (Subfunctor.homOfLe hle) =
      (U (m + 1)).preimage (U m).ι := fun m hle => by
    ext Y x
    refine ⟨?_, fun hx => ⟨⟨x.1, hx⟩, rfl⟩⟩
    rintro ⟨y, rfl⟩
    exact y.2
  have key : ∀ m, m ≤ n → HasSmallNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ
      (U m).toFunctor := by
    intro m hm
    refine Nat.decreasingInduction
      (motive := fun m _ => HasSmallNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ
        (U m).toFunctor) (fun m hm ih => ?_) (hempty.of_iso eUn.symm) hm
    · let p : Fin n := ⟨m, hm⟩
      obtain ⟨⟨hW, hsq⟩, hfs, -, hVc, hVsep, hVsize, hUqc⟩ := hstep p
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
      exact GluedEtaleQuotient.hasSmallNoetherianApproximation_of_isElementaryDistinguishedSquare
        hW hmqs (f p) hsq hfs (hVsize.trans_lt (max_lt B.aleph0_lt_cutoff_cof hA)) hUqc'
        (ih.of_iso eU)
  have h0 := key 0 (Nat.zero_le n)
  rw [hU0] at h0
  exact h0.of_iso (asIso (⊤ : Subfunctor X).ι)

end AlgebraicGeometry.Space

end
