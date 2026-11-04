module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.GeometryBiprod
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.GeometryCover
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.GeometryLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.GeometryAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.GeometryChartCover
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.FiniteColimits.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact

/-!
# Geometric inputs for the dévissage of Stacks 07V9 along elementary distinguished squares

Let `W` be an algebraic space with an elementary distinguished square `(U ⊆ W, f : V ⟶ W)`
(Stacks 08GM).  This file collects the geometric and module-theoretic inputs which the dévissage
of Stacks 07V9 (modules of finite presentation generate the quasi-coherent ones) needs along
such a square.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_biprod`: a binary biproduct of modules of finite
  presentation is of finite presentation (the site statement
  `Stacks.SheafOfModules.isFinitePresentation_biprod`: presentations over a common refinement of
  the two covering families, and the biproduct of presentations).
* `AlgebraicGeometry.Space.isFinitePresentation_etaleModulePullback`: étale restriction preserves
  finite presentation (Stacks 03DO (7) for the pullback of Stacks 03LU, identified with étale
  restriction by Stacks 03LW).
* `AlgebraicGeometry.Space.exists_smallEtalePostcomp_iso` and
  `AlgebraicGeometry.Space.functorPushforward_smallEtalePostcomp_mem`: a chart mapping to a
  postcomposed chart is postcomposed (the slice comparison of Stacks 04M0), and postcomposition
  is cover preserving.
* `AlgebraicGeometry.Space.edsSieve_mem`: the charts factoring through `U` or through `V` cover;
  a point of `W` outside `U` lies on the reduced closed complement, over which `f` is an
  isomorphism, so it is in the image of `f`, and the pointwise covering criterion applies.
* `AlgebraicGeometry.Space.isFinitePresentation_of_eds`: finite presentation is local for the
  covering `{U, V}`: the covering families of the two restrictions are postcomposed into `W`,
  they cover by `edsSieve_mem`, and finite presentation on a slice transports along the slice
  comparison (Stacks 03DM for 03DL (7)).
* `AlgebraicGeometry.Space.isOpenImmersion_edsSnd`,
  `AlgebraicGeometry.Space.isQuasiCompactSpace_edsInter` and
  `AlgebraicGeometry.Space.nonempty_finiteAffineChartCover_edsInter`: the intersection
  `U ×_W V` is an open subspace of `V`, quasi-compact by Stacks 073B, and, when `V` is affine,
  representable by a quasi-compact open subscheme of an affine scheme, so finitely many affine
  opens with affine pairwise intersections give a finite affine chart cover.
* `AlgebraicGeometry.Space.generatedByGlobalSections_of_isAffineSpace` and
  `AlgebraicGeometry.Space.isLocallyFpGenerated_of_isAffineSpace`: on an affine algebraic space a
  section of a quasi-coherent module over an affine chart is a combination of restrictions of
  global sections (Descent 03DX (2) at the terminal chart), hence locally the image of a finite
  free module.

## References

* [Stacks Project, Tag 07V9](https://stacks.math.columbia.edu/tag/07V9)
* [Stacks Project, Tag 08GM](https://stacks.math.columbia.edu/tag/08GM)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The direct sum of two `𝒪_X`-modules of finite presentation is of finite presentation. -/
theorem isFinitePresentation_biprod {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (G G' : Modules.{u, u} B S hS X hX)
    [HasBinaryBiproduct G G'] (hG : G.IsFinitePresentation) (hG' : G'.IsFinitePresentation) :
    (G ⊞ G').IsFinitePresentation :=
  have : HasWeakSheafify (smallEtaleRingedSite B S hS X hX).J AddCommGrpCat.{u} :=
    inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS X) AddCommGrpCat.{u})
  have : (smallEtaleRingedSite B S hS X hX).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstanceAs ((SmallEtale.topology B S hS X).WEqualsLocallyBijective AddCommGrpCat.{u})
  Stacks.SheafOfModules.isFinitePresentation_biprod G G' hG hG'

/-- Étale restriction preserves finite presentation. -/
theorem isFinitePresentation_etaleModulePullback {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) (G : Modules.{u, u} B S hS X.1 X.2) (hG : G.IsFinitePresentation) :
    ((etaleModulePullback.{u, u} B S hS f hf).obj G).IsFinitePresentation := by
  let G' : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) := G
  have hG' : G'.IsFinitePresentation := hG
  have hfp : ((modulePullback B S hS f).obj G).IsFinitePresentation :=
    Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules
      (smallEtaleRingedToposModulesHom B S hS f) G'
  exact Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
    ((modulePullbackIsoEtaleModulePullback B S hS f hf).app G) hfp

/-- A chart of `X` admitting a morphism to the postcomposition of a chart of `Y` along an étale
`f : Y ⟶ X` is itself (isomorphic to) the postcomposition of a chart of `Y`. -/
theorem exists_smallEtalePostcomp_iso {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) {T' : SmallEtale B S hS X.1} {T'' : SmallEtale B S hS Y.1}
    (a : T' ⟶ (smallEtalePostcomp B S hS f hf).obj T'') :
    ∃ T''' : SmallEtale B S hS Y.1, Nonempty ((smallEtalePostcomp B S hS f hf).obj T''' ≅ T') :=
  ⟨((SmallEtale.postcompOverInverse B S hS f hf T'').obj (Over.mk a)).left,
    ⟨(Over.forget _).mapIso ((SmallEtale.postcompOverCounitIso B S hS f hf T'').app (Over.mk a))⟩⟩

/-- Postcomposition along an étale morphism carries covering sieves to covering sieves: the
sieve generated by the postcompositions of the arrows of a covering sieve is covering. -/
theorem functorPushforward_smallEtalePostcomp_mem {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) {T : SmallEtale B S hS Y.1} {R : Sieve T}
    (hR : R ∈ SmallEtale.topology B S hS Y.1 T) :
    R.functorPushforward (smallEtalePostcomp B S hS f hf) ∈
      SmallEtale.topology B S hS X.1 ((smallEtalePostcomp B S hS f hf).obj T) :=
  (SmallEtale.coverPreserving_smallEtalePostcomp B S hS f hf).cover_preserve hR

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- The sieve on a chart `T` of `W` of the charts mapping to a chart postcomposed from the open
subspace or from the étale member of the square. -/
def edsSieve (T : SmallEtale B S hS W.1) : Sieve T where
  arrows T' _ :=
    (∃ T'' : SmallEtale B S hS (edsOpen B S hS hsq).1,
      Nonempty (T' ⟶ (smallEtalePostcomp B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).obj T'')) ∨
    (∃ T'' : SmallEtale B S hS (edsEtale B S hS hsq).1,
      Nonempty (T' ⟶ (smallEtalePostcomp B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).obj T''))
  downward_closed := by
    rintro T' T'' g (⟨T₀, ⟨a⟩⟩ | ⟨T₀, ⟨a⟩⟩) h
    · exact Or.inl ⟨T₀, ⟨h ≫ a⟩⟩
    · exact Or.inr ⟨T₀, ⟨h ≫ a⟩⟩

/-- The open subspace and the étale member of an elementary distinguished square cover: the
sieve `AlgebraicGeometry.Space.edsSieve` is covering. -/
theorem edsSieve_mem (T : SmallEtale B S hS W.1) :
    edsSieve B S hS hsq T ∈ SmallEtale.topology B S hS W.1 T := by
  rw [SmallEtale.mem_topology_iff_exists_mem_range]
  intro x
  rcases mem_range_or_mem_range_of_isElementaryDistinguishedSquare B S hS W.2 Uo fV hsq
      (pointsMap B S hS _ T.1.hom ((pointsEquivScheme B S hS T.1.left).symm x)) with hx | hx
  · obtain ⟨T', k, T'', hT', hk⟩ := exists_hom_smallEtalePostcomp_of_mem_range B S hS
      (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq) T x hx
    exact ⟨T', k, Or.inl ⟨T'', hT'⟩, hk⟩
  · obtain ⟨T', k, T'', hT', hk⟩ := exists_hom_smallEtalePostcomp_of_mem_range B S hS
      (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq) T x hx
    exact ⟨T', k, Or.inr ⟨T'', hT'⟩, hk⟩

/-- Finite presentation is local for the covering by the two members of an elementary
distinguished square. -/
theorem isFinitePresentation_of_eds (G : Modules.{u, u} B S hS W.1 W.2)
    (hU : ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).obj G).IsFinitePresentation)
    (hV : ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).obj G).IsFinitePresentation) :
    G.IsFinitePresentation := by
  obtain ⟨IU, XU, hXU, hU'⟩ :=
    (Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_isFinitePresentation _).1 hU
  obtain ⟨IV, XV, hXV, hV'⟩ :=
    (Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_isFinitePresentation _).1 hV
  let PU := smallEtalePostcomp B S hS (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)
  let PV := smallEtalePostcomp B S hS (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
  refine (Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_isFinitePresentation G).2
    ⟨IU ⊕ IV, Sum.elim (fun i => PU.obj (XU i)) (fun j => PV.obj (XV j)), ?_, ?_⟩
  · intro T
    refine (SmallEtale.topology B S hS W.1).transitive (edsSieve_mem B S hS hsq T) _ ?_
    rintro T' g (⟨T'', ⟨a⟩⟩ | ⟨T'', ⟨a⟩⟩)
    · refine (SmallEtale.topology B S hS W.1).superset_covering ?_
        ((SmallEtale.topology B S hS W.1).pullback_stable a
          (functorPushforward_smallEtalePostcomp_mem B S hS _ _ (hXU T'')))
      rintro Z h ⟨Z', g', h', hg', -⟩
      obtain ⟨i, ⟨n⟩⟩ := (Sieve.mem_ofObjects_iff _ _).1 hg'
      exact (Sieve.mem_ofObjects_iff _ _).2 ⟨Sum.inl i, ⟨h' ≫ PU.map n⟩⟩
    · refine (SmallEtale.topology B S hS W.1).superset_covering ?_
        ((SmallEtale.topology B S hS W.1).pullback_stable a
          (functorPushforward_smallEtalePostcomp_mem B S hS _ _ (hXV T'')))
      rintro Z h ⟨Z', g', h', hg', -⟩
      obtain ⟨j, ⟨n⟩⟩ := (Sieve.mem_ofObjects_iff _ _).1 hg'
      exact (Sieve.mem_ofObjects_iff _ _).2 ⟨Sum.inr j, ⟨h' ≫ PV.map n⟩⟩
  · rintro (i | j)
    · exact (isFinitePresentation_over_etaleModulePullback_iff B S hS _ _ G (XU i)).2 (hU' i)
    · exact (isFinitePresentation_over_etaleModulePullback_iff B S hS _ _ G (XV j)).2 (hV' j)

/-- The second projection of the intersection of an elementary distinguished square, the base
change of the open immersion, is an open immersion. -/
theorem isOpenImmersion_edsSnd : IsOpenImmersion B S hS (edsSnd B S hS hsq).hom :=
  isOpenImmersion_of_isPullback B S hS (isPullback_edsInter B S hS hsq) hsq.isOpenSubspace.2

/-- The intersection of an elementary distinguished square with quasi-compact open subspace and
quasi-compact étale member, in a quasi-separated ambient space, is quasi-compact. -/
theorem isQuasiCompactSpace_edsInter (hUqc : IsQuasiCompactSpace B S hS Uo.toFunctor)
    (hVqc : IsQuasiCompactSpace B S hS V) (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1) :
    IsQuasiCompactSpace B S hS (edsInter B S hS hsq).1 :=
  isQuasiCompactSpace_pullback B S hS hZ Uo.ι fV hsq.isOpenSubspace.1 W.2 hUqc hVqc hWqs

/-- The intersection of an elementary distinguished square with affine étale member and
quasi-compact open subspace, in a quasi-separated ambient space, has a finite covering by affine
étale charts with affine overlaps. -/
theorem nonempty_finiteAffineChartCover_edsInter (hV : IsAffineSpace B S hS V)
    (hUqc : IsQuasiCompactSpace B S hS Uo.toFunctor)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1) :
    Nonempty (FiniteAffineChartCover B S hS (edsInter B S hS hsq)) := by
  have hqc := isQuasiCompactSpace_edsInter B S hS hZ hsq hUqc
    hV.isQuasiCompactSpace hWqs
  obtain ⟨A, hA, ⟨e⟩⟩ := hV
  let q : (edsInter B S hS hsq).1 ⟶ yoneda.obj A := (edsSnd B S hS hsq).hom ≫ e.hom
  have hq : IsOpenImmersion B S hS q := isOpenImmersion_comp B S hS _ _
    (isOpenImmersion_edsSnd B S hS hsq) (isOpenImmersion_of_isIso B S hS e.hom)
  have hpb := hq.rep.isPullback (𝟙 (yoneda.obj A))
  have : IsIso (hq.rep.fst (𝟙 (yoneda.obj A))) := hpb.isIso_fst_of_isIso
  let eP : (edsInter B S hS hsq).1 ≅ yoneda.obj (hq.rep.pullback (𝟙 (yoneda.obj A))) :=
    (asIso (hq.rep.fst (𝟙 (yoneda.obj A)))).symm
  have hOimm : AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hq.rep.snd (𝟙 (yoneda.obj A)))) :=
    hq.property_snd (𝟙 (yoneda.obj A))
  refine nonempty_finiteAffineChartCover_of_iso B S hS _ eP
    (compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS (hqc.of_iso B S hS eP)) ?_
  intro U' V' hU' hV'
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj A) := hA
  have h1 : terminal.from ((BigFppfOver.toScheme B S hS).obj
      (hq.rep.pullback (𝟙 (yoneda.obj A)))) =
      (BigFppfOver.toScheme B S hS).map (hq.rep.snd (𝟙 (yoneda.obj A))) ≫
        terminal.from _ := terminal.hom_ext _ _
  have : AlgebraicGeometry.IsSeparated (terminal.from ((BigFppfOver.toScheme B S hS).obj
      (hq.rep.pullback (𝟙 (yoneda.obj A))))) := by rw [h1]; infer_instance
  exact hU'.inf hV'

end Square

/-- **Generation by global sections on an affine space.**  On an affine algebraic space a section
of a quasi-coherent module over any chart is, locally on the chart, a finite linear combination of
restrictions of global sections (Descent 03DX(2) over affine charts). -/
theorem generatedByGlobalSections_of_isAffineSpace {V : AlgebraicSpaces B S hS}
    (hV : IsAffineSpace B S hS V.1) (F : Modules.{u, u} B S hS V.1 V.2)
    (hF : F.IsQuasicoherentOnSite) (T : SmallEtale B S hS V.1) (s : F.val.obj (op T)) :
    Sieve.mk (fun T' (g : T' ⟶ T) => ∃ (n : ℕ) (m : Fin n → F.val.sections)
        (a : Fin n → (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS V.1 V.2).O).obj.obj (op T')),
        F.val.map g.op s = ∑ i, a i • (m i).eval (op T'))
      (by
        rintro T' T'' g ⟨n, m, a, h⟩ k
        refine ⟨n, m, fun i => (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS V.1 V.2).O).obj.map k.op (a i), ?_⟩
        have e1 : F.val.map (k ≫ g).op s = F.val.map k.op (F.val.map g.op s) :=
          PresheafOfModules.map_comp_apply F.val g.op k.op s
        rw [e1, h]
        refine (map_sum (PresheafOfModules.restrictₛₗ F.val k.op) _ _).trans ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        refine (PresheafOfModules.map_smul F.val k.op (a i) ((m i).eval (op T'))).trans ?_
        exact congrArg _ (PresheafOfModules.sections_property (m i) k.op)) ∈
      SmallEtale.topology B S hS V.1 T := by
  obtain ⟨I, Ys, as, haff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS V.1 T
  refine (SmallEtale.topology B S hS V.1).superset_covering ?_ hcov
  rintro Z g ⟨Z', h, g', ⟨j⟩, rfl⟩
  refine Sieve.downward_closed _ ?_ h
  exact exists_sum_smul_sections_eval_of_isAffineSpace B S hS hV F hF (Ys j) (haff j) _

/-- **The affine case of the dévissage.**  On an affine algebraic space every quasi-coherent
module is locally generated by modules of finite presentation: over an affine chart a section is
a combination of restrictions of global sections (Descent 03DX(2)), and finitely many global
sections define a map from a finite free module. -/
theorem isLocallyFpGenerated_of_isAffineSpace {V : AlgebraicSpaces B S hS}
    (hV : IsAffineSpace B S hS V.1) (F : Modules.{u, u} B S hS V.1 V.2)
    (hF : F.IsQuasicoherentOnSite) : IsLocallyFpGenerated B S hS V.2 F := by
  intro T s
  refine (SmallEtale.topology B S hS V.1).superset_covering ?_
    (generatedByGlobalSections_of_isAffineSpace B S hS hV F hF T s)
  rintro T' g ⟨n, m, a, h⟩
  let ψ : SheafOfModules.free (ULift.{u} (Fin n)) ⟶ F :=
    F.freeHomEquiv.symm (fun i => m i.down)
  refine ⟨SheafOfModules.free (ULift.{u} (Fin n)),
    Stacks.Tag01PJFiniteColimits.isFinitePresentation_free _, ψ,
    ∑ i, a i • (SheafOfModules.freeSection (R := Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS V.1 V.2).O) (ULift.up i)).eval (op T'), ?_⟩
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  congr 1
  have := SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
    (M := F) (fun i : ULift.{u} (Fin n) => m i.down) (ULift.up i)
  exact congrArg (fun σ : F.val.sections => σ.eval (op T')) this

end AlgebraicGeometry.Space

end
