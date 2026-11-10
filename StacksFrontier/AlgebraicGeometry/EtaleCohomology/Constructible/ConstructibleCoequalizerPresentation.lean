module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.EtaleShriekConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.GlobalStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.RepresentablePresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.EtaleLocalRepresentability
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import StacksFrontier.Topology.Spectral.QuasiCompactOpenInter
public import StacksCore.Tactic.StacksAttribute

/-!
# Constructible sheaves of sets are the finite coequalizers of representables

Let `X` be a quasi-compact and quasi-separated scheme. A sheaf of sets on the small étale site
of `X` is constructible exactly when it is a coequalizer `F₁ ⇉ F₀ → F` in which `F₀` and `F₁`
are finite coproducts of sheaves `h_U` represented by quasi-compact and quasi-separated objects
`U` of `X_étale`.

## Main results

* `isConstructibleSetSheaf_iff_hasFiniteQCSRepresentableCoequalizerPresentation_unconditional`
  of `StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/ConstructibleQuasiCompact.lean`
  — both directions of the characterization, proved there from the private lemmas of this file.

## Implementation notes

The presentation itself is
`AlgebraicGeometry.HasFiniteQCSRepresentableCoequalizerPresentation`.

From a presentation, constructibility follows because `h_U` is constructible and constructible
sheaves of sets are closed under finite colimits.

Conversely a constructible sheaf is a quasi-compact object of the topos: on each stratum of a
finite constructible stratification it becomes finite étale representable, representables of
quasi-compact objects are quasi-compact, and restriction to the strata is jointly faithful.
A quasi-compact sheaf is then covered by finitely many representables of affine — hence
quasi-compact and quasi-separated — étale objects, the kernel pair of such a surjection is
again constructible so it too is covered, and the two surjections exhibit `F` as the
coequalizer because every epimorphism of sheaves of sets is a regular epimorphism.

## References

* [Stacks Project, Tag 09Y9](https://stacks.math.columbia.edu/tag/09Y9)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
attribute [local instance 2000] Sheaf.instHasFiniteColimits

private theorem isCompact_of_isConstructible
    {T : Type*} [TopologicalSpace T] [SpectralSpace T]
    {subset : Set T} (hsubset : Topology.IsConstructible subset) :
    IsCompact subset :=
  isCompact_of_le_of_isCompact (constructibleTopology_le T)
    (@IsClosed.isCompact T (constructibleTopology T) subset
      (compactSpace_constructibleTopology T)
      (SpectralSubset.isClosed_constructibleTopology_of_isConstructible subset hsubset))

private theorem compactSpace_constructibleStratification_piece
    (B : BigEtaleSite.{u}) (X : B.Scheme) [CompactSpace X.obj]
    [QuasiSeparatedSpace X.obj]
    (stratification : ConstructibleStratification B X ⊤)
    (index : Fin stratification.n) : CompactSpace (stratification.piece index).obj := by
  let inclusion := B.inclusion.map (stratification.inclusion index)
  have : IsImmersion inclusion := stratification.isImmersion index
  have : SpectralSpace X.obj := {}
  have : SpectralSpace (B.inclusion.obj X) := inferInstanceAs (SpectralSpace X.obj)
  have hconstructible : Topology.IsConstructible (Set.range inclusion.base) := by
    have hpreimage := stratification.constructible index
    have htop : Topology.IsOpenEmbedding ((⊤ : X.obj.Opens).ι.base) :=
      (⊤ : X.obj.Opens).ι.isOpenEmbedding
    have hrange : IsRetrocompact (Set.range ((⊤ : X.obj.Opens).ι.base)) := by
      simp
    have hsubset : Set.range inclusion.base ⊆ Set.range ((⊤ : X.obj.Opens).ι.base) := by
      simp
    exact (Topology.isConstructible_preimage_iff_of_isOpenEmbedding htop hrange hsubset).mp
      hpreimage
  apply isCompact_univ_iff.mp
  apply inclusion.isEmbedding.isCompact_iff.mpr
  simpa using isCompact_of_isConstructible hconstructible

private theorem exists_finiteEtaleRepresentatives_of_isConstructibleSetSheaf
    (B : BigEtaleSite.{u}) (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (hdesc : Stacks.EtaleCohomology.EtaleDescentForFiniteEtaleRepresentability B)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B X F) :
    ∃ stratification : ConstructibleStratification B X ⊤,
      ∃ representatives : ∀ index : Fin stratification.n,
        SmallEtale B (stratification.piece index).obj
          (stratification.piece index).property,
        ∀ index,
          IsFinite (B.inclusion.map (representatives index).obj.hom) ∧
          CompactSpace ((SmallEtale.toScheme B (stratification.piece index).obj
            (stratification.piece index).property).obj (representatives index)) ∧
          QuasiSeparatedSpace ((SmallEtale.toScheme B (stratification.piece index).obj
            (stratification.piece index).property).obj (representatives index)) ∧
          Nonempty
            ((((smallEtaleBaseChange B
              (stratification.inclusion index)).sheafPullback (Type (u + 1))
              (SmallEtale.topology B X.obj X.property)
              (SmallEtale.topology B (stratification.piece index).obj
                (stratification.piece index).property)).obj F) ≅
              (Sheaf.sheafifiedYoneda (SmallEtale.topology B
                (stratification.piece index).obj
                (stratification.piece index).property)).obj
                  (representatives index)) := by
  obtain ⟨stratification, hstratification⟩ :=
    (isConstructibleFiniteSheaf_iff_exists_stratification B X F).mp hF
  choose representatives hfinite hiso using fun index =>
    (Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable_of_descent B
      (stratification.piece index) _ hdesc).mp (hstratification index)
  refine ⟨stratification, representatives, fun index => ?_⟩
  let inclusion := B.inclusion.map (stratification.inclusion index)
  have : IsImmersion inclusion := stratification.isImmersion index
  have : QuasiSeparatedSpace (B.inclusion.obj X) :=
    inferInstanceAs (QuasiSeparatedSpace X.obj)
  have : QuasiSeparatedSpace (B.inclusion.obj (stratification.piece index)) :=
    quasiSeparatedSpace_of_quasiSeparated inclusion
  have : CompactSpace (B.inclusion.obj (stratification.piece index)) :=
    compactSpace_constructibleStratification_piece B X stratification index
  have := hfinite index
  exact ⟨hfinite index,
    QuasiCompact.compactSpace_of_compactSpace
      (B.inclusion.map (representatives index).obj.hom),
    quasiSeparatedSpace_of_quasiSeparated
      (B.inclusion.map (representatives index).obj.hom), hiso index⟩

private theorem smallEtale_coveringSieve_pointwise
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    {U : SmallEtale B X.obj X.property} {R : Sieve U}
    (hR : (SmallEtale.precoverage B X.obj X.property).Saturate U R) :
    ∀ point : (SmallEtale.toScheme B X.obj X.property).obj U,
      ∃ (V : SmallEtale B X.obj X.property) (arrow : V ⟶ U),
        R arrow ∧ point ∈ Set.range ((SmallEtale.toScheme B X.obj X.property).map arrow) := by
  let T := SmallEtale.toScheme B X.obj X.property
  intro point
  induction hR with
  | of U presieve hpresieve =>
      obtain ⟨cover, rfl, hcover⟩ :=
        (SmallEtale.mem_precoverage_iff B X.obj X.property).mp hpresieve
      have hcover' : (cover.map T).presieve₀ ∈ Scheme.etalePrecoverage (T.obj U) := by
        have hbig : IsEtaleCovering
            ⟨U.obj.left, cover.map (SmallEtale.inclusion B X.obj X.property ⋙
              BigEtaleOver.forget B X.obj X.property)⟩ := hcover.1
        simpa [T, SmallEtale.toScheme, BigEtaleOver.toScheme,
          IsEtaleCovering, PreZeroHypercover.map] using hbig
      obtain ⟨index, preimage, hpreimage⟩ :=
        ((Scheme.presieve₀_mem_precoverage_iff (cover.map T)).mp hcover').1 point
      exact ⟨cover.X index, cover.f index,
        Sieve.le_generate _ _ _ (Presieve.ofArrows.mk index), preimage, hpreimage⟩
  | top U =>
      exact ⟨U, 𝟙 U, by simp, point, by simp⟩
  | pullback U R hR V arrow ih =>
      obtain ⟨W, first, hfirst, preimage, hpreimage⟩ := ih (T.map arrow point)
      have hpb := (IsPullback.of_hasPullback first arrow).map T
      obtain ⟨lifted, hfirst', hsecond'⟩ :=
        Scheme.exists_preimage_of_isPullback hpb preimage point hpreimage
      refine ⟨pullback first arrow, pullback.snd first arrow, ?_, lifted, hsecond'⟩
      change R (pullback.snd first arrow ≫ arrow)
      rw [← pullback.condition]
      exact R.downward_closed hfirst _
  | transitive U R S hR hlocal ihR ihlocal =>
      obtain ⟨V, first, hfirst, preimage, hpreimage⟩ := ihR point
      obtain ⟨W, second, hsecond, preimage', hpreimage'⟩ := ihlocal hfirst preimage
      refine ⟨W, second ≫ first, hsecond, preimage', ?_⟩
      rw [Functor.map_comp, Scheme.Hom.comp_apply, hpreimage', hpreimage]

private theorem etale_map_left_of_hom_smallEtale
    (B : BigEtaleSite.{u}) (X : B.Scheme) {V U : SmallEtale B X.obj X.property} (arrow : V ⟶ U) :
    Etale (B.inclusion.map arrow.hom.left) := by
  have hcomp : Etale (B.inclusion.map arrow.hom.left ≫ B.inclusion.map U.obj.hom) := by
    rw [← Functor.map_comp, Over.w]
    infer_instance
  have := hcomp
  exact Etale.of_comp _ (B.inclusion.map U.obj.hom)

/-- An étale covering of the underlying scheme of `U` is refined by a covering family in the small
étale site, indexed compatibly with the original family. -/
private theorem exists_smallEtale_refinement
    (B : BigEtaleSite.{u}) (X : B.Scheme) (U : SmallEtale B X.obj X.property)
    (family : PreZeroHypercover.{u + 1} U.obj.left)
    (hfamily : IsEtaleCovering ⟨U.obj.left, family⟩) :
    ∃ (I : Type (u + 1)) (V : I → SmallEtale B X.obj X.property)
      (arrows : ∀ index, V index ⟶ U) (reindex : I → family.I₀),
      Sieve.ofArrows V arrows ∈ SmallEtale.topology B X.obj X.property U ∧
      ∃ hobjects : ∀ index, (V index).obj.left = family.X (reindex index),
        ∀ index, (arrows index).hom.left = eqToHom (hobjects index) ≫ family.f (reindex index) := by
  obtain ⟨⟨target, selected⟩, hselected, htarget, hcomb⟩ :=
    B.exists_covering_rep ⟨U.obj.left, family⟩ hfamily
  dsimp at htarget
  subst target
  have hetale : ∀ index, Etale (B.inclusion.map (selected.f index)) :=
    ((Scheme.presieve₀_mem_precoverage_iff (selected.map B.inclusion)).mp hselected.1).2
  let V : selected.I₀ → SmallEtale B X.obj X.property := fun index =>
    ⟨Over.mk (selected.f index ≫ U.obj.hom), by
      change Etale (B.inclusion.map (selected.f index ≫ U.obj.hom))
      rw [Functor.map_comp]
      have := hetale index
      infer_instance⟩
  let arrows : ∀ index, V index ⟶ U := fun index =>
    ObjectProperty.homMk (Over.homMk (selected.f index) rfl)
  let refinement : PreZeroHypercover.{u + 1} U :=
    { I₀ := selected.I₀
      X := V
      f := arrows }
  have hrefinement : SmallEtale.IsCovering B X.obj X.property ⟨U, refinement⟩ := hselected
  obtain ⟨reindex, hobjects, harrows⟩ := hcomb.2
  exact ⟨selected.I₀, V, arrows, reindex,
    Precoverage.generate_mem_toGrothendieck ⟨refinement, rfl, hrefinement⟩, hobjects, harrows⟩

private theorem smallEtale_sieve_mem_of_jointlySurjective
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (U : SmallEtale B X.obj X.property) {I : Type (u + 1)}
    (V : I → SmallEtale B X.obj X.property) (arrows : ∀ index, V index ⟶ U)
    (hcover : ∀ point : (SmallEtale.toScheme B X.obj X.property).obj U,
      ∃ index, point ∈ Set.range ((SmallEtale.toScheme B X.obj X.property).map
        (arrows index))) :
    Sieve.ofArrows V arrows ∈ SmallEtale.topology B X.obj X.property U := by
  let family : PreZeroHypercover.{u + 1} U.obj.left :=
    { I₀ := I
      X index := (V index).obj.left
      f index := (arrows index).hom.left }
  have hfamily : IsEtaleCovering ⟨U.obj.left, family⟩ :=
    (Scheme.presieve₀_mem_precoverage_iff (P := @Etale)
      (family.map B.inclusion)).mpr
        ⟨hcover, fun index => etale_map_left_of_hom_smallEtale B X (arrows index)⟩
  obtain ⟨J, W, selectedArrows, reindex, hmem, hobjects, harrows⟩ :=
    exists_smallEtale_refinement B X U family hfamily
  apply (SmallEtale.topology B X.obj X.property).superset_covering _ hmem
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  intro Z arrow harrow
  obtain ⟨index⟩ := harrow
  let factor : W index ⟶ V (reindex index) := ObjectProperty.homMk
    (Over.homMk (eqToHom (hobjects index)) (by
      change eqToHom (hobjects index) ≫ (V (reindex index)).obj.hom = _
      rw [← Over.w (selectedArrows index).hom, harrows index, Category.assoc]
      exact congrArg _ (Over.w (arrows (reindex index)).hom).symm))
  have hfactor : selectedArrows index = factor ≫ arrows (reindex index) := by
    apply (SmallEtale.inclusion B X.obj X.property ⋙
      BigEtaleOver.forget B X.obj X.property).map_injective
    exact harrows index
  change (Sieve.ofArrows V arrows) (selectedArrows index)
  rw [hfactor]
  exact (Sieve.ofArrows V arrows).downward_closed (Sieve.ofArrows_mk _ _ _) factor

private theorem smallEtale_isQuasiCompactObject
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (U : SmallEtale B X.obj X.property)
    [CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj U)] :
    (SmallEtale.topology B X.obj X.property).IsQuasiCompactObject U := by
  classical
  intro cover hcover
  let T := SmallEtale.toScheme B X.obj X.property
  let points := ULift.{u + 1, u} (T.obj U)
  choose V arrows harrows preimages hpreimages using
    (fun point : points => smallEtale_coveringSieve_pointwise B X
      ((Precoverage.mem_toGrothendieck_iff).mp hcover) point.down)
  choose indices factors hfactor using fun point : points =>
    (Sieve.mem_ofArrows_iff cover.X cover.f (arrows point)).mp (harrows point)
  have hetale : ∀ point, Etale (T.map (arrows point)) := fun point =>
    etale_map_left_of_hom_smallEtale B X (arrows point)
  have hopen : ∀ point, IsOpen (Set.range (T.map (arrows point))) := by
    intro point
    have := hetale point
    simpa using (T.map (arrows point)).isOpenMap _ isOpen_univ
  have hcoverage : (Set.univ : Set (T.obj U)) ⊆
      ⋃ point : points, Set.range (T.map (arrows point)) := by
    intro point hpoint
    exact Set.mem_iUnion.mpr ⟨⟨point⟩, preimages ⟨point⟩, hpreimages ⟨point⟩⟩
  obtain ⟨selected, hselected⟩ := isCompact_univ.elim_finite_subcover
    (fun point : points => Set.range (T.map (arrows point))) hopen hcoverage
  let refinement : PreZeroHypercover.{u + 1} U :=
    { I₀ := selected
      X point := V point.1
      f point := arrows point.1 }
  let comparison : refinement.Hom cover :=
    { s₀ point := indices point.1
      h₀ point := factors point.1
      w₀ point := (hfactor point.1).symm }
  refine ⟨refinement, comparison, ?_, Set.finite_range _⟩
  apply smallEtale_sieve_mem_of_jointlySurjective B X U
  intro point
  have hpoint := hselected (Set.mem_univ point)
  simp only [Set.mem_iUnion] at hpoint
  obtain ⟨chosen, hchosen, hpoint⟩ := hpoint
  exact ⟨⟨chosen, hchosen⟩, hpoint⟩

private theorem exists_affine_cover_smallEtale
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (U : SmallEtale B X.obj X.property) :
    ∃ (I : Type (u + 1)) (V : I → SmallEtale B X.obj X.property)
      (arrows : ∀ index, V index ⟶ U),
      Sieve.ofArrows V arrows ∈ SmallEtale.topology B X.obj X.property U ∧
      ∀ index, IsAffine ((SmallEtale.toScheme B X.obj X.property).obj (V index)) := by
  classical
  let T := (SmallEtale.toScheme B X.obj X.property).obj U
  let cover := T.affineCover
  let family : PreZeroHypercover.{u + 1} U.obj.left :=
    { I₀ := ULift.{u + 1, u} cover.I₀
      X index := B.obj (cover.X index.down)
        (Scheme.size_lt_of_isOpenImmersion (cover.f index.down) U.obj.left.property)
      f index := ObjectProperty.homMk (cover.f index.down) }
  have hfamily : IsEtaleCovering ⟨U.obj.left, family⟩ :=
    (Scheme.presieve₀_mem_precoverage_iff (P := @Etale)
      (family.map B.inclusion)).mpr ⟨fun point => by
        obtain ⟨index, preimage, hpreimage⟩ := cover.exists_eq point
        exact ⟨⟨index⟩, preimage, hpreimage⟩, fun index => by
        change Etale (cover.f index.down)
        infer_instance⟩
  obtain ⟨J, V, arrows, reindex, hcover, hobjects, -⟩ :=
    exists_smallEtale_refinement B X U family hfamily
  refine ⟨J, V, arrows, hcover, fun index => ?_⟩
  change IsAffine (B.inclusion.obj (V index).obj.left)
  rw [hobjects index]
  change IsAffine (cover.X (reindex index).down)
  infer_instance

private theorem exists_affineRepresentable_epi
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :
    ∃ (I : Type (u + 1)) (U : I → SmallEtale B X.obj X.property)
      (sections : ∀ index,
        (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj (U index) ⟶ F),
      (∀ index, IsAffine ((SmallEtale.toScheme B X.obj X.property).obj (U index))) ∧
      Epi (Limits.Sigma.desc sections) := by
  classical
  let J := SmallEtale.topology B X.obj X.property
  let affineObjects := {U : SmallEtale B X.obj X.property //
    IsAffine ((SmallEtale.toScheme B X.obj X.property).obj U)}
  let I := Σ U : affineObjects, F.obj.obj (Opposite.op U.1)
  let U : I → SmallEtale B X.obj X.property := fun index => index.1.1
  let sections : ∀ index, (Sheaf.sheafifiedYoneda J).obj (U index) ⟶ F :=
    fun index => (Sheaf.sectionEquiv J).symm index.2
  refine ⟨I, U, sections, fun index => index.1.2, ?_⟩
  constructor
  intro G first second hequal
  apply Sheaf.hom_ext
  ext object element
  change first.hom.app object element = second.hom.app object element
  obtain ⟨indices, V, arrows, hcover, haffine⟩ :=
    exists_affine_cover_smallEtale B X object.unop
  apply (((isSheaf_iff_isSheaf_of_type J G.obj).mp G.property).isSeparated
    (Sieve.ofArrows V arrows) hcover).ext
  intro W arrow harrow
  obtain ⟨index, factor, rfl⟩ := (Sieve.mem_ofArrows_iff V arrows arrow).mp harrow
  have hequal_section :
      first.hom.app (Opposite.op (V index)) (F.obj.map (arrows index).op element) =
      second.hom.app (Opposite.op (V index)) (F.obj.map (arrows index).op element) := by
    let chosen : I := ⟨⟨V index, haffine index⟩, F.obj.map (arrows index).op element⟩
    have hcomponent := congrArg (fun morphism => Limits.Sigma.ι
      (fun index => (Sheaf.sheafifiedYoneda J).obj (U index)) chosen ≫ morphism) hequal
    rw [← Category.assoc, ← Category.assoc, Limits.Sigma.ι_comp_desc] at hcomponent
    have hsection := congrArg (Sheaf.sectionEquiv J) hcomponent
    simpa only [sections, chosen, Sheaf.sectionEquiv_comp,
      Equiv.apply_symm_apply] using hsection
  simpa only [op_comp, Functor.map_comp, types_comp_apply,
    NatTrans.naturality_apply] using congrArg (G.obj.map factor.op) hequal_section

private theorem exists_finite_epi_of_isQuasiCompact
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hcompact : Sheaf.IsQuasiCompact F)
    {I : Type (u + 1)} (U : I → SmallEtale B X.obj X.property)
    (hU : ∀ index,
      CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj (U index)) ∧
        QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj (U index)))
    (sections : ∀ index,
      (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj (U index) ⟶ F)
    (hsections : Epi (Limits.Sigma.desc sections)) :
    ∃ (n : ℕ) (V : Fin n → SmallEtale B X.obj X.property),
      (∀ index, CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj (V index)) ∧
        QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj (V index))) ∧
      letI : HasFiniteColimits (Sheaf (SmallEtale.topology B X.obj X.property)
          (Type (u + 1))) := CategoryTheory.Sheaf.instHasFiniteColimits
      letI : HasColimitsOfShape (Discrete (Fin n))
          (Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :=
        HasFiniteColimits.out _
      ∃ p : (∐ fun index =>
        (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj (V index)) ⟶ F,
        Epi p := by
  classical
  let J := SmallEtale.topology B X.obj X.property
  let representatives := fun index => (Sheaf.sheafifiedYoneda J).obj (U index)
  obtain ⟨selection, hfinite, hsurjective⟩ := hcompact I representatives sections
    ((Sheaf.isLocallySurjective_iff_epi (Limits.Sigma.desc sections)).mpr hsections)
  have := hfinite.fintype
  let enumeration := (Fintype.equivFin selection).symm
  let selectedRepresentatives := fun index : selection => representatives index.1
  let augmentation := Limits.Sigma.desc fun index : selection => sections index.1
  have : Epi augmentation := Sheaf.epi_of_isLocallySurjective augmentation
  refine ⟨Fintype.card selection, fun index => U (enumeration index).1,
    fun index => hU (enumeration index).1,
    (Limits.Sigma.reindex enumeration selectedRepresentatives).hom ≫ augmentation, ?_⟩
  infer_instance

private theorem exists_finite_affineRepresentable_epi_of_isQuasiCompact
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hcompact : Sheaf.IsQuasiCompact F) :
    ∃ (n : ℕ) (U : Fin n → SmallEtale B X.obj X.property),
      (∀ index, CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj (U index)) ∧
        QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj (U index))) ∧
      letI : HasFiniteColimits (Sheaf (SmallEtale.topology B X.obj X.property)
          (Type (u + 1))) := CategoryTheory.Sheaf.instHasFiniteColimits
      letI : HasColimitsOfShape (Discrete (Fin n))
          (Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :=
        HasFiniteColimits.out _
      ∃ p : (∐ fun index =>
        (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj (U index)) ⟶ F,
        Epi p := by
  obtain ⟨indices, U, sections, haffine, hepi⟩ := exists_affineRepresentable_epi B X F
  apply exists_finite_epi_of_isQuasiCompact B X F hcompact U _ sections hepi
  intro index
  have := haffine index
  exact ⟨inferInstance, inferInstance⟩

private theorem exists_finite_epi_of_jointlyFaithful
    {C : Type*} [Category C]
    [∀ (I : Type (u + 1)) (G : I → C), HasCoproduct G]
    {n : ℕ} {D : Fin n → Type*} [∀ index, Category (D index)]
    (restriction : ∀ index, C ⥤ D index) (hfaithful : JointlyFaithful restriction)
    {I : Type (u + 1)} (G : I → C) (F : C) (sections : ∀ index, G index ⟶ F)
    (hselection : ∀ index, ∃ selection : Set I, selection.Finite ∧
      Epi ((restriction index).map (Limits.Sigma.desc fun selected : selection =>
        sections selected.1))) :
    ∃ selection : Set I, selection.Finite ∧
      Epi (Limits.Sigma.desc fun selected : selection => sections selected.1) := by
  classical
  choose selection hfinite hepi using hselection
  let total : Set I := ⋃ index, selection index
  have htotal : total.Finite := Set.finite_iUnion hfinite
  refine ⟨total, htotal, ?_⟩
  have hrepi : ∀ index, Epi ((restriction index).map
      (Limits.Sigma.desc fun selected : total => sections selected.1)) := by
    intro index
    let inclusion : (∐ fun selected : selection index => G selected.1) ⟶
        (∐ fun selected : total => G selected.1) :=
      Limits.Sigma.desc fun selected => Limits.Sigma.ι (fun selected : total => G selected.1)
        ⟨selected.1, Set.mem_iUnion.mpr ⟨index, selected.2⟩⟩
    have hfactor : inclusion ≫ (Limits.Sigma.desc fun selected : total =>
        sections selected.1) =
        Limits.Sigma.desc fun selected : selection index => sections selected.1 := by
      apply Limits.Sigma.hom_ext
      intro selected
      simp only [inclusion, Limits.Sigma.ι_comp_desc, Limits.Sigma.ι_comp_desc_assoc]
    have := hepi index
    have hmap := congrArg (restriction index).map hfactor
    rw [Functor.map_comp] at hmap
    exact epi_of_epi_fac hmap
  have := hrepi
  exact hfaithful.jointlyReflectEpimorphisms.epi _

private theorem isQuasiCompact_of_jointlyFaithful_restrictions
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {n : ℕ} {D : Fin n → Type (u + 1)} [∀ index, Category.{u} (D index)]
    (K : ∀ index, GrothendieckTopology (D index))
    (restriction : ∀ index, Sheaf J (Type (u + 1)) ⥤ Sheaf (K index) (Type (u + 1)))
    [∀ index, PreservesColimitsOfSize.{u + 1, u + 1} (restriction index)]
    (hfaithful : JointlyFaithful restriction)
    (F : Sheaf J (Type (u + 1)))
    (hcompact : ∀ index, Sheaf.IsQuasiCompact ((restriction index).obj F)) :
    Sheaf.IsQuasiCompact F := by
  intro I G sections hsurjective
  have hepi : Epi (Limits.Sigma.desc sections) :=
    (Sheaf.isLocallySurjective_iff_epi _).mp hsurjective
  have hselection : ∀ index, ∃ selection : Set I, selection.Finite ∧
      Epi ((restriction index).map (Limits.Sigma.desc fun selected : selection =>
        sections selected.1)) := by
    intro index
    let P := restriction index
    have := hepi
    have hepiA : Epi (Limits.Sigma.desc fun selected => P.map (sections selected)) := by
      rw [← Limits.sigmaComparison_map_desc]
      infer_instance
    obtain ⟨selection, hfinite, hsurjectiveA⟩ := hcompact index I
      (fun selected => P.obj (G selected)) (fun selected => P.map (sections selected))
      ((Sheaf.isLocallySurjective_iff_epi _).mpr hepiA)
    have hepiB : Epi (Limits.Sigma.desc fun selected : selection =>
        P.map (sections selected.1)) :=
      (Sheaf.isLocallySurjective_iff_epi _).mp hsurjectiveA
    refine ⟨selection, hfinite, ?_⟩
    have := hepiB
    exact epi_of_epi_fac (Limits.sigmaComparison_map_desc P
      (fun selected : selection => G selected.1) F
      (fun selected : selection => sections selected.1))
  obtain ⟨selection, hfinite, hepiC⟩ :=
    exists_finite_epi_of_jointlyFaithful restriction hfaithful G F sections hselection
  exact ⟨selection, hfinite, (Sheaf.isLocallySurjective_iff_epi _).mpr hepiC⟩

private theorem isQuasiCompact_of_iso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {F G : Sheaf J (Type (u + 1))} (iso : F ≅ G)
    (hcompact : Sheaf.IsQuasiCompact F) : Sheaf.IsQuasiCompact G := by
  intro I objects sections hsurjective
  have hepi : Epi (Limits.Sigma.desc sections) :=
    (Sheaf.isLocallySurjective_iff_epi _).mp hsurjective
  have := hepi
  have hdesc {A : Type (u + 1)} (H : A → Sheaf J (Type (u + 1)))
      (arrows : ∀ index, H index ⟶ G) :
      (Limits.Sigma.desc fun index => arrows index ≫ iso.inv) =
        Limits.Sigma.desc arrows ≫ iso.inv := by
    apply Limits.Sigma.hom_ext
    intro index
    simp only [Limits.Sigma.ι_comp_desc, Limits.Sigma.ι_comp_desc_assoc]
  have hepiA : Epi (Limits.Sigma.desc fun index => sections index ≫ iso.inv) := by
    rw [hdesc]
    infer_instance
  obtain ⟨selection, hfinite, hsurjectiveA⟩ := hcompact I objects
    (fun index => sections index ≫ iso.inv)
    ((Sheaf.isLocallySurjective_iff_epi _).mpr hepiA)
  refine ⟨selection, hfinite, ?_⟩
  apply (Sheaf.isLocallySurjective_iff_epi _).mpr
  have hepiB : Epi (Limits.Sigma.desc fun index : selection =>
      sections index.1 ≫ iso.inv) :=
    (Sheaf.isLocallySurjective_iff_epi _).mp hsurjectiveA
  rw [hdesc] at hepiB
  have := hepiB
  have hepiC : Epi
      (((Limits.Sigma.desc fun index : selection => sections index.1) ≫ iso.inv) ≫ iso.hom) :=
    inferInstance
  simpa using hepiC

theorem isQuasiCompact_of_isConstructibleSetSheaf
    (B : BigEtaleSite.{u}) (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (hdesc : Stacks.EtaleCohomology.EtaleDescentForFiniteEtaleRepresentability B)
    (hjf : ∀ {k : ℕ} (Y : Fin k → B.Scheme) (inclusions : ∀ i, Y i ⟶ X),
      (∀ x : X.obj, ∃ (i : Fin k) (y : (Y i).obj),
        (B.inclusion.map (inclusions i)) y = x) →
      JointlyFaithful (fun i =>
        (smallEtaleBaseChange B (inclusions i)).sheafPullback (Type (u + 1))
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (Y i).obj (Y i).property)))
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B X F) : Sheaf.IsQuasiCompact F := by
  obtain ⟨stratification, representatives, hrepresentatives⟩ :=
    exists_finiteEtaleRepresentatives_of_isConstructibleSetSheaf B X hdesc F hF
  let restriction := fun index : Fin stratification.n =>
    (smallEtaleBaseChange B (stratification.inclusion index)).sheafPullback (Type (u + 1))
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (stratification.piece index).obj
        (stratification.piece index).property)
  have hfaithful : JointlyFaithful restriction := by
    apply hjf stratification.piece stratification.inclusion
    intro point
    have hpoint : point ∈ ⋃ index,
        Set.range (B.inclusion.map (stratification.inclusion index)).base := by
      rw [← stratification.covers]
      trivial
    obtain ⟨index, y, hy⟩ := Set.mem_iUnion.mp hpoint
    exact ⟨index, y, hy⟩
  have : ∀ index, PreservesColimitsOfSize.{u + 1, u + 1} (restriction index) :=
    fun index =>
      ((smallEtaleBaseChange B
        (stratification.inclusion index)).sheafAdjunctionContinuous (Type (u + 1))
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (stratification.piece index).obj
          (stratification.piece index).property)).leftAdjoint_preservesColimits
  apply isQuasiCompact_of_jointlyFaithful_restrictions
    (SmallEtale.topology B X.obj X.property)
    (fun index => SmallEtale.topology B (stratification.piece index).obj
      (stratification.piece index).property) restriction hfaithful F
  intro index
  obtain ⟨hfinite, hcompact, hseparated, ⟨iso⟩⟩ := hrepresentatives index
  let _ := hcompact
  exact isQuasiCompact_of_iso _ iso.symm
    ((GrothendieckTopology.isQuasiCompactObject_iff_isQuasiCompact_sheafifiedYoneda _ _).mp
      (smallEtale_isQuasiCompactObject B (stratification.piece index)
        (representatives index)))

private theorem coequalizer_kernelPair_epi_comp_iso
    {C : Type*} [Category C] [HasPullbacks C] [HasCoequalizers C]
    [IsRegularEpiCategory C] {F₀ F₁ F : C} (p : F₀ ⟶ F) [Epi p]
    (q : F₁ ⟶ pullback p p) [Epi q] :
    Nonempty (coequalizer (q ≫ pullback.fst p p) (q ≫ pullback.snd p p) ≅ F) := by
  let kernelPairColimit := IsKernelPair.toCoequalizer
    (IsPullback.of_hasPullback p p) (regularEpiOfEpi p)
  exact ⟨(colimit.isColimit _).coconePointUniqueUpToIso
    (isCoequalizerEpiComp kernelPairColimit q)⟩

theorem isConstructibleSetSheaf_sigma_sheafifiedYoneda
    (B : BigEtaleSite.{u}) (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (hstrat : ∀ U : SmallEtale B X.obj X.property,
      CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj U) →
      QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj U) →
      HasFiniteEtaleStratification B X U)
    {k : ℕ} (W : Fin k → SmallEtale B X.obj X.property)
    (hW : ∀ i, CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj (W i)) ∧
      QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj (W i)))
    (i : Discrete (Fin k)) :
    IsConstructibleSetSheaf B X
      ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj (W i.as)) := by
  let _ : CompactSpace (W i.as).obj.left.obj := (hW i.as).1
  let _ : QuasiSeparatedSpace (W i.as).obj.left.obj := (hW i.as).2
  exact isConstructibleSetSheaf_sheafifiedYoneda B X (W i.as)
    (hstrat (W i.as) (hW i.as).1 (hW i.as).2)

end AlgebraicGeometry

end
