module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple.OpenSubobjects
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension

/-!
# Quasi-separatedness of representable presheaves

Auxiliary material for the induction principle on quasi-compact quasi-separated algebraic
spaces: quasi-separatedness and quasi-compactness of open subspaces, and the comparison
between a scheme of the site being quasi-separated and the presheaf it represents being
absolutely quasi-separated,
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- The extension of a represented presheaf along a morphism of base schemes of the site is
represented by the same object viewed over the new base. -/
noncomputable def yonedaRelocalizedRepresentableBy
    (B : BigFppfSite.{u}) (S Z : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains Z)
    (f : B.obj hS ⟶ B.obj hZ)
    (U : BigFppfOver B S hS) :
    ((OverShriek.relocalizePresheafFunctor f).obj (yoneda.obj U)).RepresentableBy
      (Over.mk (U.hom ≫ f)) := by
  refine ⟨?_, ?_⟩
  · intro W
    refine
      { toFun := fun g => ⟨⟨g.left ≫ U.hom, Over.homMk g.left rfl⟩, by
          change g.left ≫ U.hom ≫ f = W.hom
          simpa [Category.assoc] using g.w⟩
        invFun := fun x => Over.homMk x.1.2.left (by
          calc
            x.1.2.left ≫ U.hom ≫ f = x.1.1 ≫ f :=
              congrArg (fun t => t ≫ f) x.1.2.w
            _ = W.hom := x.2)
        left_inv := fun g => by ext; rfl
        right_inv := by
          rintro ⟨⟨ψ, g⟩, hψ⟩
          let gHom : Over.mk ψ ⟶ U := g
          apply Subtype.ext
          apply Sigma.ext
          · simp
          · dsimp
            let gInv : Over.mk ψ ⟶ U := Over.homMk gHom.left gHom.w
            let gL' : (Over.mk ψ).left ⟶ U.left := Over.Hom.left gInv
            let g'' : Over.mk (gL' ≫ U.hom) ⟶ U := Over.homMk gL' rfl
            have hidx : gL' ≫ U.hom = ψ := by simp [gL']
            have hObj : Over.mk (gL' ≫ U.hom) = Over.mk ψ := congrArg Over.mk hidx
            have hleft : (eqToHom hObj.symm).left = 𝟙 ((Over.mk ψ).left) := by
              rw [Over.eqToHom_left]
              rfl
            have hg : eqToHom hObj.symm ≫ g'' = gHom := by
              apply Over.OverMorphism.ext
              rw [Over.comp_left, hleft, Category.id_comp]
              change gL' = Over.Hom.left gHom
              rfl
            simpa [Over.homMk, g'', gL', gInv, gHom] using
              (eqToHom_comp_heq g'' hObj.symm).symm.trans (heq_of_eq hg) }
  · intro W W' g a
    rfl

/-- Quasi-separatedness over the base transfers along an isomorphism of presheaves. -/
theorem qs_preserved_by_iso
    (B : BigFppfSite.{u}) (Z : Scheme.{u}) (hZ : B.Contains Z)
    {F G : (BigFppfOver B Z hZ)ᵒᵖ ⥤ Type u}
    (e : F ≅ G)
    (hF : IsQuasiSeparatedOver B Z hZ F) :
    IsQuasiSeparatedOver B Z hZ G := by
  let q := BigFppfOver.toScheme B Z hZ
  let P := (MorphismProperty.inverseImage
    (@QuasiCompact.{u} : MorphismProperty Scheme.{u}) q).presheaf
  have he : Arrow.mk (diag F) ≅ Arrow.mk (diag G) :=
    Arrow.isoMk e (prod.mapIso e e) (by simp)
  exact (MorphismProperty.arrow_iso_iff P he).mp hF

/-- An open subspace of an absolutely quasi-separated algebraic space is absolutely
quasi-separated. -/
theorem openSubspace_isQuasiSeparated
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hF : IsAlgebraicSpace B S hS F)
    (hFqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (U : Subfunctor F) (hU : IsOpenSubspace B S hS U) :
    IsAbsolutelyQuasiSeparated B S hS hZ U.toFunctor := by
  have hqsmor : IsQuasiSeparated B S hS U.ι := by
    intro Z hZalg hZqc g
    have := (pullback.isIso_diagonal_iff U.ι).2 inferInstance
    exact IsQuasiCompactSpace.of_iso B S hS hZqc
      (asIso (pullback.fst g (pullback.diagonal U.ι))).symm
  exact isAbsolutelyQuasiSeparated_of_isQuasiSeparated
    B S hS hZ hU.1 hFqs hqsmor

/-- An open immersion of algebraic spaces is an immersion. -/
alias immersion_of_openImmersion := isImmersion_of_isOpenImmersion

/-- An open subspace whose set of points is quasi-compact is a quasi-compact algebraic space. -/
theorem openSubspace_isQuasiCompact_of_compact_range
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (U : Subfunctor F) (hU : IsOpenSubspace B S hS U)
    (hcompact : @IsCompact _
      (pointTopology B S hS F)
      (Set.range (pointsMap B S hS U.toFunctor U.ι))) :
    IsQuasiCompactSpace B S hS U.toFunctor := by
  let : TopologicalSpace (points B S hS U.toFunctor) :=
    pointTopology B S hS U.toFunctor
  let : TopologicalSpace (points B S hS F) :=
    pointTopology B S hS F
  have hEmb : @Topology.IsEmbedding _ _
      (pointTopology B S hS U.toFunctor)
      (pointTopology B S hS F)
      (pointsMap B S hS U.toFunctor U.ι) :=
    isEmbedding_pointsMap_of_isImmersion B S hS hF U.ι (immersion_of_openImmersion B S hS hU.2)
  have hcompact' : IsCompact
      (pointsMap B S hS U.toFunctor U.ι '' Set.univ) := by
    rwa [Set.image_univ]
  exact (isQuasiCompactSpace_iff_compactSpace_points B S hS
    U.toFunctor hU.1).2 ⟨by simpa using hEmb.isCompact_iff.mpr hcompact'⟩

/-- The image on points of a morphism out of a quasi-compact algebraic space is quasi-compact. -/
theorem pointsRange_isCompact
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G)
    (f : F ⟶ G) (hqc : IsQuasiCompactSpace B S hS F) :
    @IsCompact _ (pointTopology B S hS G)
      (Set.range (pointsMap B S hS F f)) := by
  let : TopologicalSpace (points B S hS F) := pointTopology B S hS F
  let : TopologicalSpace (points B S hS G) := pointTopology B S hS G
  have : CompactSpace (points B S hS F) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS F hF).mp hqc
  -- The family of Tag 03BX assigns `pointTopology` to an algebraic space, so its continuity
  -- clause is continuity for the topologies named in the statement.
  have hcont : @Continuous _ _ (pointTopology B S hS F) (pointTopology B S hS G)
      (pointsMap B S hS F f) := (pointTopologyFamily B S hS).continuous hF hG f
  simpa only [Set.image_univ] using isCompact_univ.image hcont

/-- The set of points of the subfunctor cut out by an open with quasi-compact underlying
scheme is quasi-compact. -/
theorem representableOpen_pointsRange_isCompact
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (hW : CompactSpace W.toScheme) :
    @IsCompact _ (pointTopology B S hS (yoneda.obj T))
      (Set.range (pointsMap B S hS
        (representableOpenSubobject B S hS T W).toFunctor
        (representableOpenSubobject B S hS T W).ι)) :=
  pointsRange_isCompact B S hS
    (representableOpenSubobject_isOpen B S hS T W).1
    (isAlgebraicSpace_yoneda B S hS T) _
    (representableOpenSubobject_isQuasiCompact B S hS T W hW)

/-- A functor preserving the binary product `X ⨯ X` carries the diagonal of `X` to an arrow
isomorphic to the diagonal of its image, so isomorphism-invariant properties agree on them. -/
private theorem map_diag_iff {C D : Type*} [Category C] [Category D] [HasBinaryProducts C]
    [HasBinaryProducts D] (F : C ⥤ D) (X : C) [PreservesLimit (pair X X) F]
    (P : MorphismProperty D) [P.RespectsIso] : P (F.map (diag X)) ↔ P (diag (F.obj X)) := by
  let e : F.obj (X ⨯ X) ≅ F.obj X ⨯ F.obj X := PreservesLimitPair.iso F X X
  have heq : F.map (diag X) ≫ e.hom = diag (F.obj X) := by
    apply prod.hom_ext <;> simp [e, ← Functor.map_comp]
  have he : Arrow.mk (F.map (diag X)) ≅ Arrow.mk (diag (F.obj X)) :=
    Arrow.isoMk (Iso.refl _) e (by simp [heq])
  exact MorphismProperty.arrow_iso_iff P he

/-- Over the terminal scheme, the presheaf represented by an object is quasi-separated exactly
when its underlying scheme is quasi-separated. -/
private theorem isQuasiSeparated_yoneda_iff
    (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))
    (T : BigFppfOver B (⊤_ Scheme.{u}) hZ) :
    IsQuasiSeparatedOver B (⊤_ Scheme.{u}) hZ (yoneda.obj T) ↔
      QuasiSeparatedSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj T) := by
  let Z := (⊤_ Scheme.{u})
  let q := BigFppfOver.toScheme B Z hZ
  let Q : MorphismProperty Scheme := @QuasiCompact.{u}
  let P := Q.inverseImage q
  let : HasPullbacks (BigFppfOver B Z hZ) := inferInstance
  let : HasTerminal (BigFppfOver B Z hZ) :=
    (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj hZ)))).hasTerminal
  let : HasBinaryProducts (BigFppfOver B Z hZ) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hqTerminal : q.obj (⊤_ (BigFppfOver B Z hZ)) ≅ ⊤_ Scheme := by
    let Tz : BigFppfOver B Z hZ := Over.mk (𝟙 (B.obj hZ))
    let hTz : IsTerminal Tz := (Over.mkIdTerminal : IsTerminal Tz)
    let e := hTz.uniqueUpToIso
      (terminalIsTerminal : IsTerminal (⊤_ (BigFppfOver B Z hZ)))
    simpa [q, BigFppfOver.toScheme, BigFppfOver.forget,
      Tz, BigFppfSite.obj] using (q.mapIso e).symm
  let : PreservesLimit (Functor.empty _) q := preservesTerminal_of_iso q hqTerminal
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) q :=
    preservesLimitsOfShape_pempty_of_preservesTerminal q
  let : PreservesLimitsOfShape WalkingCospan q := by
    apply comp_preservesLimitsOfShape
  let : P.IsStableUnderBaseChange := ⟨by
    intro A A' A'' S' f g f' g' hs hg
    let : Q.IsStableUnderBaseChange := inferInstance
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := Q) (hs.map q) hg⟩
  let : PreservesLimitsOfShape (Discrete WalkingPair) q :=
    preservesBinaryProducts_of_preservesTerminal_and_pullbacks q
  let : PreservesLimit (pair T T) yoneda := inferInstance
  rw [quasiSeparatedSpace_iff_quasiCompact_prod_lift]
  change P.presheaf (diag (yoneda.obj T)) ↔ Q (diag (q.obj T))
  rw [← map_diag_iff yoneda T P.presheaf]
  exact (MorphismProperty.relative_map_iff (F := yoneda) (P := P)).trans (map_diag_iff q T Q)


/-- Over the terminal scheme, the presheaf represented by an object with quasi-separated
underlying scheme is quasi-separated. -/
theorem isQuasiSeparated_yoneda_of_quasiSeparatedSpace
    (B : BigFppfSite.{u})
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (T : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    (hT : QuasiSeparatedSpace
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj T)) :
    IsQuasiSeparatedOver B (⊤_ Scheme.{u}) hZ
      (yoneda.obj T) :=
  (isQuasiSeparated_yoneda_iff B hZ T).2 hT

/-- Viewing the presheaf represented by `T` over the integers gives the presheaf represented by
`T` with its structure morphism composed to the terminal object. -/
private noncomputable def viewOverIntegersYonedaIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (T : BigFppfOver B S hS) :
    viewOverIntegers B S hS hZ (yoneda.obj T) ≅
      yoneda.obj (Over.mk (T.hom ≫ (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)) :
        BigFppfOver B (⊤_ Scheme.{u}) hZ) :=
  (Functor.representableByEquiv
    (yonedaRelocalizedRepresentableBy B S _ hS hZ ⟨terminal.from S⟩ T)).symm

/-- An object of the site whose represented presheaf is absolutely quasi-separated has
quasi-separated underlying scheme. -/
theorem quasiSeparatedSpace_of_isQuasiSeparated_yoneda
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (T : BigFppfOver B S hS)
    (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T)) :
    QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj T) :=
  (isQuasiSeparated_yoneda_iff B hZ _).1 (qs_preserved_by_iso B _ hZ
    (viewOverIntegersYonedaIso B S hS hZ T) hTqs)

/-- **Stacks 03JX, `(η) ∧ (θ) ⇔ (ι)`, for a represented presheaf.** The presheaf represented
by an object `T` of the big fppf site over `S` is an absolutely quasi-separated algebraic space
exactly when the underlying scheme of `T` is a quasi-separated scheme.

Both sides are read over the terminal scheme: the represented presheaf of `T`, viewed over the
integers, is the represented presheaf of `T` with its structure morphism composed to the terminal
object, whose underlying scheme is that of `T`. The forward direction is the comparison of the
diagonal of the represented presheaf with the diagonal of the scheme over the terminal object;
the reverse direction is the represented diagonal of a quasi-separated scheme, transported back
along that identification. -/
theorem isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (T : BigFppfOver B S hS) :
    IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T) ↔
      QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj T) := by
  refine ⟨quasiSeparatedSpace_of_isQuasiSeparated_yoneda B S hS hZ T, fun hT => ?_⟩
  exact qs_preserved_by_iso B _ hZ (viewOverIntegersYonedaIso B S hS hZ T).symm
    (isQuasiSeparated_yoneda_of_quasiSeparatedSpace B hZ _ hT)

/-- The subfunctor cut out by an open of an absolutely quasi-separated represented presheaf is
absolutely quasi-separated. -/
theorem representableOpenSubobject_isQuasiSeparated
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (T : BigFppfOver B S hS)
    (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T))
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    IsAbsolutelyQuasiSeparated B S hS hZ
      (representableOpenSubobject B S hS T W).toFunctor :=
  openSubspace_isQuasiSeparated B S hS hZ
    (isAlgebraicSpace_yoneda B S hS T) hTqs _
    (representableOpenSubobject_isOpen B S hS T W)

/-- An isomorphism of presheaves is étale. -/
alias etale_of_iso_presheaves := AlgebraicGeometry.Space.isEtale_of_iso

end AlgebraicGeometry.Space

end
