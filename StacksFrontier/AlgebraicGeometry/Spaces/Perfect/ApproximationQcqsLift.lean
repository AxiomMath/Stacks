module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.GenerationStep
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectCompactQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.CategoryTheory.Triangulated.LocallySmallRoof

/-!
# Lifting a perfect object from the open member of an elementary distinguished square

Let `(U ⊆ W, j : V ⟶ W)` be an elementary distinguished square of algebraic spaces with `W`
quasi-compact and quasi-separated, `U` quasi-compact and `V` affine. For a perfect object `P` of
`D_QCoh(𝒪_U)` and a morphism `α : P ⟶ E|_U` with `E` in `D_QCoh(𝒪_W)`, there is a perfect object
`R` of `D_QCoh(𝒪_W)` with `R|_U ≅ P ⊕ P[1]` and a morphism `R ⟶ E` restricting to `(α, 0)`. This
is the lifting step of Stacks 08HN, where the source cites Stacks 08EK and 08EH on `V`.

## The argument

The restriction `D_QCoh(𝒪_W) ⥤ D_QCoh(𝒪_U)` is a finite localization (Thomason–Trobaugh,
Neeman): its right adjoint `R(U ⟶ W)_*` is fully faithful, `D_QCoh(𝒪_W)` is compactly generated
(Stacks 09IY), and the kernel of the restriction is detected by `j_! K` for the Koszul object `K`
on functions on `V` cutting out `V ∖ U ×_W V`. So `P ⊕ P[1]` lifts to a compact `c`, a roof
`c ← c' ⟶ E` lifts the morphism, and `R = c'` is perfect by Stacks 09M8.

## Main results

* `AlgebraicGeometry.Space.exists_union_isElementaryDistinguishedSquare`: the open union of two
  open subspaces, inside which the first sits in an elementary distinguished square.
* `AlgebraicGeometry.Space.isElementaryDistinguishedSquare_of_le`: enlarging the open member.
* `AlgebraicGeometry.Space.exists_isPerfect_lift`: the lift.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated

universe u

namespace CategoryTheory.Pretriangulated

universe w v v' u₁ u₂

variable {T : Type u₁} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [IsTriangulated T]
  [LocallySmall.{w} T] [HasCoproducts.{w} T]
  {T' : Type u₂} [Category.{v'} T'] [Preadditive T'] [HasZeroObject T'] [HasShift T' ℤ]
  [∀ n : ℤ, (shiftFunctor T' n).Additive] [Pretriangulated T'] [IsTriangulated T']
  [LocallySmall.{w} T'] [HasCoproducts.{w} T']

/-- **Lifting `P ⊕ P[1]` together with a morphism** along a finite localization `L ⊣ G` of a
compactly generated category whose kernel is detected by compact objects killed by `L`: for a
compact `P` and `α : P ⟶ L E` there are a compact `R`, an isomorphism `L R ≅ P ⊕ P[1]` and
`a : R ⟶ E` with `L a` the composite of that isomorphism with `(α, 0)`. -/
theorem exists_isCompactObject_lift_biprod_desc_of_locallySmall
    {L : T ⥤ T'} {G : T' ⥤ T} (adj : L ⊣ G) [L.CommShift ℤ] [L.IsTriangulated]
    [IsIso adj.counit] [∀ J : Type w, PreservesColimitsOfShape (Discrete J) G]
    {ι : Type w} (K : ι → T)
    (hK : ∀ i, IsCompactObject.{w} (K i)) (hLK : ∀ i, IsZero (L.obj (K i)))
    (hloc : ∀ E : T, (∀ i (n : ℤ) (g : (K i)⟦n⟧ ⟶ E), g = 0) → IsIso (adj.unit.app E))
    {ι₀ : Type w} [Nonempty ι₀] (G₀ : ι₀ → T) (hG₀c : ∀ j, IsCompactObject.{w} (G₀ j))
    (hG₀ : (ObjectProperty.ofObj G₀).IsWeakTriangulatedGenerator) (P : T')
    (hP : IsCompactObject.{w} P) (E : T) (α : P ⟶ L.obj E) :
    ∃ (R : T) (e : L.obj R ≅ P ⊞ P⟦(1 : ℤ)⟧) (a : R ⟶ E), IsCompactObject.{w} R ∧
      L.map a = e.hom ≫ biprod.desc α 0 := by
  obtain ⟨c, hc, ⟨ec⟩⟩ :=
    exists_isCompactObject_iso_biprod_shift_of_locallySmall adj K hK hLK hloc G₀ hG₀c hG₀ P hP
  obtain ⟨c', s, g', hc', hLs, hg'⟩ := exists_roof_of_locallySmall adj K hK hLK hloc (c₂ := E) hc
    (ec.hom ≫ biprod.desc α 0)
  have := hLs
  refine ⟨c', asIso (L.map s) ≪≫ ec, g', hc', ?_⟩
  rw [hg', Iso.trans_hom, asIso_hom, Category.assoc]

end CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The union of two open subspaces.** For open subspaces `U` and `Y` of an algebraic space
`W` there is an open subspace `Q` with points `|U| ∪ |Y|`, containing `Y`, through which `U`
factors by `κ`, and in which `(Y ⊆ Q, κ : U ⟶ Q)` is an elementary distinguished square. -/
theorem exists_union_isElementaryDistinguishedSquare {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (U Y : Subfunctor W) (hU : IsOpenSubspace B S hS U)
    (hY : IsOpenSubspace B S hS Y) :
    ∃ (Q : Subfunctor W) (hQ : IsOpenSubspace B S hS Q) (hYQ : Y ≤ Q)
      (κ : U.toFunctor ⟶ Q.toFunctor),
      Set.range (pointsMap B S hS Q.toFunctor Q.ι) =
        Set.range (pointsMap B S hS Y.toFunctor Y.ι) ∪
          Set.range (pointsMap B S hS U.toFunctor U.ι) ∧
      κ ≫ Q.ι = U.ι ∧
      IsElementaryDistinguishedSquare B S hS hQ.1 (Subfunctor.range (Subfunctor.homOfLe hYQ))
        κ := by
  obtain ⟨Q, hQ, hYQ, κ, hrange, hκ, hsq⟩ := isElementaryDistinguishedSquare_openRestriction B S hS
    hW Y (𝟙 W) (isElementaryDistinguishedSquare_id_of_isOpenSubspace B S hS hW Y hY) U hU Y hY
    le_rfl
  exact ⟨Q, hQ, hYQ, κ, by simpa using hrange, by simpa using hκ, hsq⟩

/-- **Enlarging the open subspace of an elementary distinguished square.** If
`(U ⊆ W, f : V ⟶ W)` is an elementary distinguished square and `U ≤ U'` with `U'` open, then
`(U' ⊆ W, f)` is one: over the smaller closed complement `f` is a base change of an
isomorphism. -/
theorem isElementaryDistinguishedSquare_of_le {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hW : IsAlgebraicSpace B S hS W} {U : Subfunctor W} {f : V ⟶ W}
    (hsq : IsElementaryDistinguishedSquare B S hS hW U f) (U' : Subfunctor W)
    (hU' : IsOpenSubspace B S hS U') (hUU' : U ≤ U') :
    IsElementaryDistinguishedSquare B S hS hW U' f := by
  let := pointTopology B S hS W
  have hrange : Set.range (pointsMap B S hS U.toFunctor U.ι) ⊆
      Set.range (pointsMap B S hS U'.toFunctor U'.ι) := by
    rw [← Subfunctor.homOfLe_ι hUU', pointsMap_comp]
    exact Set.range_comp_subset_range _ _
  have hclosed : IsClosed (Set.range (pointsMap B S hS U'.toFunctor U'.ι))ᶜ :=
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS U'.ι hU'.2).isClosed_compl
  refine ⟨hsq.isAlgebraicSpace, hU', hsq.isEtale, hclosed, ?_⟩
  let Z := reducedClosedSubspace B S hS W hW _ hsq.isClosedComplement
  let Z' := reducedClosedSubspace B S hS W hW _ hclosed
  have hle : Z' ≤ Z := reducedClosedSubspace_mono B S hS hW _ _ hclosed hsq.isClosedComplement
    (Set.compl_subset_compl.2 hrange)
  have : IsIso (Z.fromPreimage f) := hsq.isIsoOverComplement
  have hpre : Z'.preimage f ≤ Z.preimage f := fun T x hx => hle _ hx
  have hcomm : Subfunctor.homOfLe hpre ≫ Z.fromPreimage f =
      Z'.fromPreimage f ≫ Subfunctor.homOfLe hle := by
    refine (cancel_mono Z.ι).1 ?_
    simp [Subfunctor.fromPreimage_ι]
  have hsmall : IsPullback (Subfunctor.homOfLe hpre) (Z'.fromPreimage f) (Z.fromPreimage f)
      (Subfunctor.homOfLe hle) := by
    refine IsPullback.of_right ?_ hcomm (Subfunctor.isPullback_preimage f Z).flip
    simpa [Subfunctor.homOfLe_ι] using (Subfunctor.isPullback_preimage f Z').flip
  exact hsmall.isIso_snd_of_isIso

section Lift

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}

/-- **Lifting a perfect object from the open member of an elementary distinguished square**
(Stacks 08EK and 08EH in the form of Thomason–Trobaugh and Neeman, on the ambient space). Let
`(U ⊆ W, j : V ⟶ W)` be an elementary distinguished square with `W` quasi-compact and
quasi-separated, `U` quasi-compact and `V` affine. For a perfect object `P` of `D_QCoh(𝒪_U)` and
a morphism `α : P ⟶ E|_U` with `E` in `D_QCoh(𝒪_W)`, there are a perfect object `R` of
`D_QCoh(𝒪_W)`, an isomorphism `R|_U ≅ P ⊕ P[1]` and a morphism `R ⟶ E` restricting to `(α, 0)`.

Restriction to `U` is a finite localization of the compactly generated `D_QCoh(𝒪_W)` (Stacks
09IY): its kernel is detected by the extension by zero of the Koszul object of functions on `V`
cutting out `V ∖ U ×_W V`. -/
theorem exists_isPerfect_lift (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    (hVa : IsAffineSpace B S hS V) (hUqc : IsQuasiCompactSpace B S hS Uo.toFunctor)
    (hWqc : IsQuasiCompactSpace B S hS W.1)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal W.1)
    (P : QuasicoherentDerivedCategory.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2)
    (hP : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2).IsPerfect
      P.obj)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2)
    (α : P ⟶ (quasicoherentDerivedEtalePullback B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).obj E) :
    ∃ (R : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2)
      (e : (quasicoherentDerivedEtalePullback B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).obj R ≅ P ⊞ P⟦(1 : ℤ)⟧) (a : R ⟶ E),
      (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect R.obj ∧
        (quasicoherentDerivedEtalePullback B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq)).map a = e.hom ≫ biprod.desc α 0 := by
  have hZ := B.contains_terminal
  have hVqc : IsQuasiCompactSpace B S hS V := hVa.isQuasiCompactSpace
  have hVqs := isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hVa
  have hUq := isQuasiCompact_edsOpenHom B S hS hZ (hsq := hsq) hWqs hUqc
  have hUs := isQuasiSeparated_edsOpenHom B S hS hsq
  have hVq := isQuasiCompact_edsEtaleHom B S hS hZ (hsq := hsq) hWqs hVqc
  have hVs := isQuasiSeparated_edsEtaleHom B S hS hZ (hsq := hsq) hVqs
  have hUqs := isAbsolutelyQuasiSeparated_edsOpen B S hS hZ (hsq := hsq) hWqs
  obtain ⟨l, ha, hb⟩ := exists_list_globalRing_unitLocus B S hS hsq hZ hVa hUqc hWqs
  obtain ⟨T₀, hT₀, ⟨i⟩⟩ := hVa
  have hT := isTerminalChartOfIso (B := B) (S := S) (hS := hS) T₀ i
  have hTa : IsAffineChart B S hS V (chartOfIso B S hS T₀ i) := hT₀
  let Kd := koszul (edsEtale B S hS hsq).2 l
  have hKP : IsZero ((edsDerivedRestrictSnd B S hS hsq).obj Kd) :=
    isZero_restrictSnd_koszul hsq l hb
  have := isGrothendieckAbelian_modules_ringUniverse B S hS W.1 W.2
  have := isGrothendieckAbelian_modules_ringUniverse B S hS
    (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2
  have := enoughInjectives_modules_ringUniverse B S hS W.1 W.2
  have := enoughInjectives_modules_ringUniverse B S hS
    (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2
  have := hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS W.1 W.2
  have := hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS
    (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2
  have := fun J : Type u => preservesCoproducts_quasicoherentDerivedPushforward B S hS
    (edsOpenHom B S hS hsq) hUq hUs J
  let aU := quasicoherentDerivedEtalePullback B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq)
  let aV := quasicoherentDerivedEtalePullback B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)
  let bU := quasicoherentDerivedEtalePullback B S hS (edsFst B S hS hsq) (isEtale_edsFst B S hS hsq)
  let bV := quasicoherentDerivedEtalePullback B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)
  let adjU := quasicoherentDerivedEtaleAdjunction B S hS _ (isEtale_edsOpenHom B S hS hsq) hUq hUs
  -- the Koszul object `j_! K`, in `D_QCoh(𝒪_W)`
  have hK'qc : QcohDerived B S hS W ((edsDerivedShriekEtale B S hS hsq).obj Kd) :=
    have := isIso_derivedShriekToPushforwardEtale B S hS hsq Kd hKP
    (QcohDerived B S hS W).prop_of_iso
      (asIso (derivedShriekToPushforwardEtale B S hS hsq Kd hKP)).symm
      (qcohDerived_derivedModulePushforward_obj B S hS _ hVq hVs Kd (qcohDerived_koszul l))
  let K' : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2 := ⟨_, hK'qc⟩
  have hK' : IsCompactObject.{u} K' :=
    isCompactObject_of_isQcohCompact B S hS W K' (isQcohCompact_lowerShriek _ _
      (isQcohCompact_of_isCompactObject B S hS (edsEtale B S hS hsq)
        (koszulQuasicoherent (edsEtale B S hS hsq).2 l)
        (isCompactObject_koszulQuasicoherent _ hT hTa l)))
  have hLK : IsZero (aU.obj K') :=
    IsZero.of_full_of_faithful_of_isZero (QcohDerived B S hS _).ι _
      (isZero_restrictOpen_derivedShriekEtale B S hS hsq Kd hKP)
  have hdet : ∀ N : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2, IsZero (aU.obj N) →
      (∀ (n : ℤ) (x : K'⟦n⟧ ⟶ N), x = 0) → IsZero N := by
    intro N hN hNK
    refine isZero_of_isZero_qcohRestrict_eds hsq N hN ?_
    refine isZero_of_hom_koszulQuasicoherent_shift_eq_zero_of_isZero_restrict
      (X := edsEtale B S hS hsq) _ hT hTa (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq) l ha
      (aV.obj N) ((Functor.map_isZero bU hN).of_iso ((qcohEdsRestrictInterIso hsq).app N).symm) ?_
    intro n y
    let ιV := (QcohDerived B S hS (edsEtale B S hS hsq)).ι
    let ιW := (QcohDerived B S hS W).ι
    let adjS := (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory
    let y₁ : (ιV.obj (koszulQuasicoherent (edsEtale B S hS hsq).2 l))⟦n⟧ ⟶
        ιV.obj (aV.obj N) :=
      (ιV.commShiftIso n).inv.app (koszulQuasicoherent (edsEtale B S hS hsq).2 l) ≫ ιV.map y
    let y₂ := (adjS.homEquiv _ _).symm y₁
    let eZ : ιW.obj (K'⟦n⟧) ≅ (edsDerivedShriekEtale B S hS hsq).obj
        ((ιV.obj (koszulQuasicoherent (edsEtale B S hS hsq).2 l))⟦n⟧) :=
      (ιW.commShiftIso n).app K' ≪≫
        (((edsDerivedShriekEtale B S hS hsq).commShiftIso n).app Kd).symm
    let y₃ : K'⟦n⟧ ⟶ N := ιW.preimage (eZ.hom ≫ y₂)
    have h3 : ιW.map y₃ = 0 := by rw [hNK n y₃, Functor.map_zero]
    have h2 : y₂ = 0 := by
      rw [Functor.map_preimage] at h3
      exact (cancel_epi eZ.hom).1 (h3.trans comp_zero.symm)
    have h1 : y₁ = 0 := by
      rw [← (adjS.homEquiv _ _).apply_symm_apply y₁]
      show adjS.homEquiv _ _ y₂ = 0
      rw [h2, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
    have h0 : ιV.map y = 0 := (cancel_epi _).1 (h1.trans comp_zero.symm)
    exact ιV.map_injective (h0.trans (Functor.map_zero _ _ _).symm)
  have hloc : ∀ E' : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2,
      (∀ (_ : PUnit.{u + 1}) (n : ℤ) (g : K'⟦n⟧ ⟶ E'), g = 0) → IsIso (adjU.unit.app E') :=
    fun E' h => isIso_unit_of_rightOrthogonal adjU K' hLK hdet E' (h PUnit.unit)
  -- a compact generator of `D_QCoh(𝒪_W)`
  obtain ⟨G, hGc, hG⟩ := exists_isCompactObject_isWeakTriangulatedGenerator_of_qcqs B S hS hZ W
    hWqc hWqs
  have hG₀ : (ObjectProperty.ofObj (fun _ : PUnit.{u + 1} => G)).IsWeakTriangulatedGenerator := by
    have : ObjectProperty.ofObj (fun _ : PUnit.{u + 1} => G) = ObjectProperty.singleton G := by
      ext Z
      rw [ObjectProperty.ofObj_iff, ObjectProperty.singleton_iff]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨PUnit.unit, h⟩⟩
    rwa [this]
  -- the lift of `P ⊕ P[1]` and the roof
  have hPc : IsCompactObject.{u} P := isCompactObject_of_isPerfect _ hUqc hUqs P hP
  have : aU.IsTriangulated := isTriangulated_quasicoherentDerivedEtalePullback B S hS _ _
  have : IsIso adjU.counit :=
    isIso_quasicoherentDerivedEtaleAdjunction_counit_of_mono B S hS _ _ _ _
  obtain ⟨R, e, a, hR, ha⟩ := exists_isCompactObject_lift_biprod_desc_of_locallySmall adjU
    (fun _ : PUnit.{u + 1} => K') (fun _ => hK') (fun _ => hLK) hloc
    (fun _ : PUnit.{u + 1} => G) (fun _ => hGc) hG₀ P hPc E α
  exact ⟨R, e, a, isPerfect_of_isCompactObject W hWqs R hR, ha⟩

end Lift

end AlgebraicGeometry.Space

end
