module

public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFamilyAffineSource
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoverSchematicNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedSchematicLocusCodimensionZero
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Reduction

/-!
# A neighbourhood with affine preimages under a finite family which is injective off a closed set

Let `X` be a separated, locally Noetherian algebraic space and `x ∈ |X|` a point whose local ring
has dimension at most one. Let `gₖ : X'ₖ ⟶ X` be finitely many finite morphisms whose images
cover `|X|`, each `X'ₖ` with a surjective finite locally free morphism from a scheme, and let
`Z ⊆ |X|` be a closed set containing no point of codimension zero off which the family is
injective. Then `x` lies in an open subspace of `X` which is a scheme. This is Steps 3, 4 and 5
of the proof of Stacks 0ADD in Stacks 0ADE, for an abstract finite family.

## Main results

* `AlgebraicGeometry.exists_preimage_basicOpen_eq_of_isClosedImmersion`: the lifting of a
  function along a closed immersion into an affine scheme, read on basic opens.
* `AlgebraicGeometry.mem_genericPoints_of_lt_of_ringKrullDim_stalk_le_one`: a proper
  generalization of a point of dimension at most one is a generic point.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isAffineSpace_of_isAffineOpen`: an affine open
  of a scheme mapping to an algebraic space by an open immersion is an affine open subspace.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isAffineSpace_subset`: shrinking an affine
  open subspace around a finite set into an open set.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isAffineSpace_of_isRepresentable_of_fibre`: an
  affine open subspace around a fibre, inside a schematic open subspace (Stacks 09NN).
* `AlgebraicGeometry.Space.localRingDimension_eq_zero_of_isClosedSubspace`: a closed subspace
  free of codimension-zero points has dimension zero at a point of codimension at most one.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isAffineSpace_preimage_basicOpen`: shrinking an
  affine open subspace to the preimage of a basic open over a closed subspace.
* `AlgebraicGeometry.Space.isAffineSpace_of_forall_isAffineSpace_preimage`: an open subspace
  whose preimages under a covering finite family are affine is affine.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_of_finite_family`: the
  existence of an affine open neighbourhood of `x`.

## References

* [Stacks Project, Tag 0ADE](https://stacks.math.columbia.edu/tag/0ADE)
* [Stacks Project, Tag 0ADC](https://stacks.math.columbia.edu/tag/0ADC)
* [Stacks Project, Tag 09NN](https://stacks.math.columbia.edu/tag/09NN)
* [Stacks Project, Tag 07VP](https://stacks.math.columbia.edu/tag/07VP)
* [Stacks Project, Tag 0BAQ](https://stacks.math.columbia.edu/tag/0BAQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Let `c : C ⟶ W` be a closed immersion with `W` affine, `φ : C ⟶ D` any morphism and
`f ∈ Γ(D)`. Then some `f' ∈ Γ(W)` cuts out on `C` the basic open cut out by `φ^♯ f`. -/
theorem exists_preimage_basicOpen_eq_of_isClosedImmersion {C W D : Scheme.{u}} [IsAffine W]
    (c : C ⟶ W) [IsClosedImmersion c] (φ : C ⟶ D) (f : Γ(D, ⊤)) :
    ∃ f' : Γ(W, ⊤), c ⁻¹ᵁ W.basicOpen f' = φ ⁻¹ᵁ D.basicOpen f := by
  obtain ⟨f', hf'⟩ := c.app_surjective ⊤ (isAffineOpen_top W) (φ.appTop f)
  refine ⟨f', ?_⟩
  rw [Scheme.preimage_basicOpen_top, Scheme.preimage_basicOpen_top]
  exact congrArg C.basicOpen hf'

/-- In a scheme, a proper generalization `t` of a point `u` whose local ring has dimension at most
one is a generic point. -/
theorem mem_genericPoints_of_lt_of_ringKrullDim_stalk_le_one {X : Scheme.{u}} {u t : X}
    (h : u < t) (hu : ringKrullDim (X.presheaf.stalk u) ≤ 1) : t ∈ genericPoints X := by
  rw [ringKrullDim_stalk_eq_coheight] at hu
  have hu' : Order.coheight u ≤ 1 := by exact_mod_cast hu
  have hle := (Order.coheight_add_one_le h).trans hu'
  have h0 : Order.coheight t = 0 := by
    generalize Order.coheight t = c at hle ⊢
    induction c using ENat.recTopCoe with
    | top => simp at hle
    | coe n =>
      norm_cast at hle ⊢
      omega
  rw [mem_genericPoints_iff_isMax]
  exact Order.coheight_eq_zero.mp h0

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `α : h_T ⟶ X'` be an open immersion of presheaves out of a scheme `T` of the site and let
`V ⊆ T` be an affine open. The image of `V` is an open subspace of `X'` which is an affine
algebraic space, whose points are the images of the points of `T` lying in `V`. -/
theorem exists_isOpenSubspace_isAffineSpace_of_isAffineOpen {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : BigFppfOver B S hS} (α : yoneda.obj T ⟶ X') (hα : IsOpenImmersion B S hS α)
    (V : ((BigFppfOver.toScheme B S hS).obj T).Opens) (hV : IsAffineOpen V) :
    ∃ G : Subfunctor X', IsOpenSubspace B S hS G ∧ IsAffineSpace B S hS G.toFunctor ∧
      Set.range (pointsMap B S hS G.toFunctor G.ι) =
        pointsMap B S hS _ α '' (pointsToScheme B S hS T ⁻¹' (V : Set _)) := by
  let Vo : BigFppfOver B S hS := openSubobject B S hS T V.ι inferInstance
  let jV : Vo ⟶ T := openSubobjectHom B S hS T V.ι inferInstance
  have hTjV : (BigFppfOver.toScheme B S hS).map jV = V.ι :=
    toScheme_map_openSubobjectHom B S hS T V.ι inferInstance
  have hjV : IsOpenImmersion B S hS (yoneda.map jV) :=
    isOpenImmersion_yoneda_map_openSubobjectHom B S hS T V.ι inferInstance
  have hVo : IsAlgebraicSpace B S hS (yoneda.obj Vo) := isAlgebraicSpace_yoneda B S hS Vo
  set χ := yoneda.map jV ≫ α with hχ
  have hχopen : IsOpenImmersion B S hS χ := isOpenImmersion_comp B S hS _ _ hjV hα
  have : Mono χ := mono_of_presheaf_isOpenImmersion hχopen
  refine ⟨Subfunctor.range χ, isOpenSubspace_subfunctorRange B S hS hVo hχopen,
    ⟨Vo, hV, ⟨(asIso (Subfunctor.toRange χ)).symm⟩⟩, ?_⟩
  have hrangeV : Set.range (pointsMap B S hS (yoneda.obj Vo) (yoneda.map jV)) =
      pointsToScheme B S hS T ⁻¹' (V : Set _) := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      have hmem : V.ι (pointsToScheme B S hS Vo w) ∈ Set.range V.ι := ⟨_, rfl⟩
      rw [Scheme.Opens.range_ι] at hmem
      rwa [Set.mem_preimage, pointsToScheme_pointsMap_yoneda, hTjV]
    · intro hz
      obtain ⟨q, hq⟩ : pointsToScheme B S hS T z ∈ Set.range V.ι := by
        rwa [Scheme.Opens.range_ι]
      refine ⟨(pointsEquivScheme B S hS Vo).symm q, injective_pointsToScheme B S hS T ?_⟩
      rwa [pointsToScheme_pointsMap_yoneda, hTjV,
        show pointsToScheme B S hS Vo ((pointsEquivScheme B S hS Vo).symm q) = q from
          (pointsEquivScheme B S hS Vo).apply_symm_apply q]
  rw [range_pointsMap_ι_range, hχ, pointsMap_comp, Set.range_comp, hrangeV]

/-- Precomposing the inclusion of an open subspace with an isomorphism gives an open immersion with
the same points. -/
private theorem isOpenImmersion_comp_ι_and_range_eq {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {A : Subfunctor X'} (hA : IsOpenSubspace B S hS A) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : F ⟶ A.toFunctor) [IsIso e] :
    IsOpenImmersion B S hS (e ≫ A.ι) ∧
      Set.range (pointsMap B S hS _ (e ≫ A.ι)) = Set.range (pointsMap B S hS A.toFunctor A.ι) :=
  ⟨isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS e) hA.2, by
    rw [pointsMap_comp, Set.range_comp, (pointsMap_surjective_of_isIso B S hS e).range_eq,
      Set.image_univ]⟩

/-- A subfunctor of a separated algebraic space is absolutely quasi-separated. -/
private theorem isAbsolutelyQuasiSeparated_subfunctor {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hsep : IsAbsolutelySeparated B S hS B.contains_terminal X) (A : Subfunctor X) :
    IsAbsolutelyQuasiSeparated B S hS B.contains_terminal A.toFunctor :=
  isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS B.contains_terminal _
    (isAbsolutelySeparated_of_isSeparated B S hS B.contains_terminal hsep
      (isSeparated_of_mono A.ι inferInstance))

/-- Let `A ⊆ X'` be an open subspace which is an affine algebraic space, `P ⊆ |A|` a finite set and
`U ⊇ P` open in `|X'|`. Then there is an affine open subspace `G ⊆ X'` with
`P ⊆ |G| ⊆ U ∩ |A|`. -/
theorem exists_isOpenSubspace_isAffineSpace_subset {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (A : Subfunctor X') (hA : IsOpenSubspace B S hS A) (hAaff : IsAffineSpace B S hS A.toFunctor)
    (P : Set (points B S hS X')) (hP : P.Finite)
    (hPA : P ⊆ Set.range (pointsMap B S hS A.toFunctor A.ι))
    (U : Set (points B S hS X')) (hU : IsOpen U) (hPU : P ⊆ U) :
    ∃ G : Subfunctor X', IsOpenSubspace B S hS G ∧ IsAffineSpace B S hS G.toFunctor ∧
      P ⊆ Set.range (pointsMap B S hS G.toFunctor G.ι) ∧
      Set.range (pointsMap B S hS G.toFunctor G.ι) ⊆
        U ∩ Set.range (pointsMap B S hS A.toFunctor A.ι) := by
  classical
  obtain ⟨T, hTaff, ⟨e⟩⟩ := hAaff
  set α := e.inv ≫ A.ι with hαdef
  obtain ⟨hα, hαrange⟩ := isOpenImmersion_comp_ι_and_range_eq B S hS hA e.inv
  have : Mono α := mono_of_presheaf_isOpenImmersion hα
  have hαinj := pointsMap_injective_of_mono B S hS α
  set Q := pointsMap B S hS _ α ⁻¹' P with hQ
  have hQfin : Q.Finite := hP.preimage hαinj.injOn
  set K := pointsToScheme B S hS T '' Q with hK
  have hKfin : K.Finite := hQfin.image _
  set Uo : Set ((BigFppfOver.toScheme B S hS).obj T) :=
    schemePointsHomeomorph B S hS T '' (pointsMap B S hS _ α ⁻¹' U) with hUo
  have hUoopen : IsOpen Uo :=
    (schemePointsHomeomorph B S hS T).isOpenMap _ (hU.preimage (continuous_pointsMap B S hS α))
  have hKU : K ⊆ Uo := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨q, hPU hq, rfl⟩
  obtain ⟨r, hKr, hrU⟩ := exists_basicOpen_of_finite_subset hKfin ⟨Uo, hUoopen⟩ hKU
  obtain ⟨G, hG, hGaff, hGrange⟩ := exists_isOpenSubspace_isAffineSpace_of_isAffineOpen B S hS
    α hα _ ((isAffineOpen_top _).basicOpen r)
  refine ⟨G, hG, hGaff, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, rfl⟩ : p ∈ Set.range (pointsMap B S hS _ α) := hαrange ▸ hPA hp
    rw [hGrange]
    exact ⟨q, hKr ⟨q, hp, rfl⟩, rfl⟩
  · rw [hGrange]
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨?_, hαrange ▸ ⟨q, rfl⟩⟩
    obtain ⟨q', hq', hqq'⟩ := hrU hq
    rw [schemePointsHomeomorph_apply] at hqq'
    rwa [← injective_pointsToScheme B S hS T hqq']

/-- Let `g : h_U ⟶ X` be locally quasi-finite and let `x ∈ |X|` have a local ring of dimension at
most one. Then the stalk of `U` at any point over `x` has Krull dimension at most one. -/
theorem krullDimLE_one_stalk_of_isLocallyQuasiFinite
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ X) (hg : IsLocallyQuasiFinite B S hS g)
    (x : points B S hS X) (hdim : localRingDimension B S hS x ≤ 1)
    (y : points B S hS (yoneda.obj U))
    (hy : pointsMap B S hS (yoneda.obj U) g y = x) :
    Ring.KrullDimLE 1
      (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk
        (pointsToScheme B S hS U y)) := by
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hle : localRingDimension B S hS y ≤ 1 := by
    have h := localRingDimension_le_of_isLocallyQuasiFinite B S hS hUalg hX g hg y
    rw [hy] at h
    exact h.trans hdim
  have hchart : ChartPoint B S hS U (𝟙 (yoneda.obj U)) (pointsToScheme B S hS U y) y := by
    have h := chartPoint_pointsToScheme B S hS U (𝟙 (yoneda.obj U)) y
    rwa [pointsMap_id, id_eq] at h
  have hhas : HasChartLocalRingDimension B S hS y (localRingDimension B S hS y) :=
    (localRingDimension_eq_iff_hasChartLocalRingDimension B S hS hUalg y
      (localRingDimension B S hS y)).mp rfl
  have hring := (hasChartLocalRingDimension_iff_ringKrullDim_stalk B S hS U
    (pointsToScheme B S hS U y) y hchart (localRingDimension B S hS y)).mp hhas
  rw [Ring.krullDimLE_iff, hring]
  exact_mod_cast hle

/-- Let `X` be separated and locally Noetherian, `x ∈ |X|` with a local ring of dimension at most
one, `g : X' ⟶ X` finite, and `O ⊆ X'` an open subspace which is a scheme and contains every point
over `x`. Then some affine open subspace of `X'` contains every point over `x`. -/
theorem exists_isOpenSubspace_isAffineSpace_of_isRepresentable_of_fibre
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hX' : IsAlgebraicSpace B S hS X')
    (hsep : IsAbsolutelySeparated B S hS B.contains_terminal X)
    (hnoeth : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (x : points B S hS X) (hdim : localRingDimension B S hS x ≤ 1)
    (g : X' ⟶ X) (hg : IsFinite B S hS g)
    (O : Subfunctor X') (hO : IsOpenSubspace B S hS O) (hOrep : O.toFunctor.IsRepresentable)
    (hfib : ∀ p : points B S hS X', pointsMap B S hS X' g p = x →
      p ∈ Set.range (pointsMap B S hS O.toFunctor O.ι)) :
    ∃ A : Subfunctor X', IsOpenSubspace B S hS A ∧ IsAffineSpace B S hS A.toFunctor ∧
      ∀ p : points B S hS X', pointsMap B S hS X' g p = x →
        p ∈ Set.range (pointsMap B S hS A.toFunctor A.ι) := by
  classical
  set T := O.toFunctor.reprX with hT
  set eO := O.toFunctor.reprW with heO
  have hTalg : IsAlgebraicSpace B S hS (yoneda.obj T) := isAlgebraicSpace_yoneda B S hS T
  set α := eO.hom ≫ O.ι with hαdef
  obtain ⟨hα, hαrange⟩ := isOpenImmersion_comp_ι_and_range_eq B S hS hO eO.hom
  have : Mono α := mono_of_presheaf_isOpenImmersion hα
  have hαinj := pointsMap_injective_of_mono B S hS α
  have hγlqf : IsLocallyQuasiFinite B S hS (α ≫ g) :=
    isLocallyQuasiFinite_comp B S hS hTalg hX' hX α g
      (isLocallyQuasiFinite_of_isEtale B S hS hX' (isEtale_of_isOpenImmersion B S hS hα))
      (isLocallyQuasiFinite_of_isFinite B S hS hX' hX hg)
  have hγsep : IsSeparated B S hS (α ≫ g) :=
    isSeparated_comp B S hS α g (isSeparated_of_mono α inferInstance)
      (isSeparated_of_isFinite B S hS g hX' hX hg)
  have hγlft : IsLocallyOfFiniteType B S hS (α ≫ g) :=
    isLocallyOfFiniteType_comp' B S hS α g hX' hX
      (isLocallyOfFiniteType_of_isEtale' B S hS α (isEtale_of_isOpenImmersion B S hS hα))
      (isLocallyOfFiniteType_of_isFinite B S hS hX' hX hg)
  have hTsep : ((BigFppfOver.toScheme B S hS).obj T).IsSeparated :=
    isSeparated_toScheme_obj_of_isSeparated B S hS B.contains_terminal T hsep (α ≫ g) hγsep
  have hTnoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T) :=
    (exists_atlas_iff_of_representable B S hS (yoneda.obj T)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) T (Iso.refl _)).1
      (isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hTalg hX (α ≫ g) hγlft hnoeth)
  set F := pointsMap B S hS _ (α ≫ g) ⁻¹' {x} with hFdef
  have hF : F.Finite := by
    have h := (finite_preimage_singleton_of_isFinite B S hS hX' hX g hg x).preimage hαinj.injOn
    convert h using 1
    ext q
    simp [hFdef]
  have : Finite F := hF.to_subtype
  obtain ⟨A₀, hA₀, hFA₀⟩ :=
    exists_isAffineOpen_containing_of_stalk_krullDimLE_one_of_finite_components
      ((BigFppfOver.toScheme B S hS).obj T)
      (finite_irreducibleComponents_of_isCompact ((BigFppfOver.toScheme B S hS).obj T))
      (fun y : F => pointsToScheme B S hS T y.1) (fun _ => inferInstance)
      (fun y => krullDimLE_one_stalk_of_isLocallyQuasiFinite B S hS hX T (α ≫ g) hγlqf x
        hdim y.1 y.2)
  obtain ⟨A, hA, hAaff, hArange⟩ :=
    exists_isOpenSubspace_isAffineSpace_of_isAffineOpen B S hS α hα A₀ hA₀
  refine ⟨A, hA, hAaff, fun p hp => ?_⟩
  obtain ⟨q, rfl⟩ : p ∈ Set.range (pointsMap B S hS _ α) := hαrange ▸ hfib p hp
  rw [hArange]
  refine ⟨q, hFA₀ ⟨q, ?_⟩, rfl⟩
  rw [hFdef, Set.mem_preimage, pointsMap_comp_apply, hp]
  rfl

/-- Let `Z ⊆ X` be a closed subspace of a locally Noetherian algebraic space such that no point of
`|Z|` is a point of codimension zero of `X`, and let `z ∈ |Z|` be a point whose local ring on `X`
has dimension at most one. Then the local ring of `Z` at `z` has dimension zero. -/
theorem localRingDimension_eq_zero_of_isClosedSubspace {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (Zs : Subfunctor X) (hZs : IsClosedSubspace B S hS Zs)
    (z : points B S hS Zs.toFunctor)
    (hdim : localRingDimension B S hS (pointsMap B S hS _ Zs.ι z) ≤ 1)
    (hgen : ∀ w : points B S hS Zs.toFunctor,
      localRingDimension B S hS (pointsMap B S hS _ Zs.ι w) ≠ 0) :
    localRingDimension B S hS z = 0 := by
  obtain ⟨U, a, u, ha, ⟨p, hpu, hpx⟩, hdimu⟩ :=
    (localRingDimension_eq_iff_hasChartLocalRingDimension B S hS hX
      (pointsMap B S hS _ Zs.ι z) _).mp rfl
  set Uz := hZs.2.rep.pullback a with hUz
  set c := hZs.2.rep.snd a with hc
  set a' := hZs.2.rep.fst a with ha'
  have sq : IsPullback a' (yoneda.map c) Zs.ι a := hZs.2.rep.isPullback a
  have hcci : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map c) :=
    MorphismProperty.relative.property_snd hZs.2 a
  have ha'et : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a' :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sq.flip ha
  obtain ⟨w, hw1, hw2⟩ := exists_point_of_isPullback_presheaf B S hS sq z
    (p.class B S hS (yoneda.obj U)) hpx.symm
  set u' := pointsToScheme B S hS Uz w with hu'
  have hcu : (BigFppfOver.toScheme B S hS).map c u' = u := by
    rwa [hu', ← pointsToScheme_pointsMap_yoneda, hw2]
  have hdimu' : ringKrullDim (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk u) ≤ 1 := by
    rw [hdimu]
    exact_mod_cast hdim
  have hgenu' : u' ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj Uz) := by
    rw [mem_genericPoints_iff_isMax]
    intro t ht
    by_contra hne
    have hcinj : Function.Injective ((BigFppfOver.toScheme B S hS).map c) :=
      ((BigFppfOver.toScheme B S hS).map c).isClosedEmbedding.injective
    have h2 : (BigFppfOver.toScheme B S hS).map c t ⤳ u := by
      have h1 : t ⤳ u' := ht
      have h2 := h1.map ((BigFppfOver.toScheme B S hS).map c).continuous
      rwa [hcu] at h2
    have hlt : u < (BigFppfOver.toScheme B S hS).map c t := by
      refine lt_of_le_not_ge h2 fun hle' => hne ?_
      have heq : (BigFppfOver.toScheme B S hS).map c t = u := (h2.antisymm hle').eq
      rw [hcinj (heq.trans hcu.symm)]
    have hgent := mem_genericPoints_of_lt_of_ringKrullDim_stalk_le_one hlt hdimu'
    set t₀ := (pointsEquivScheme B S hS Uz).symm t with ht₀
    have ht₀t : pointsToScheme B S hS Uz t₀ = t := (pointsEquivScheme B S hS Uz).apply_symm_apply t
    apply hgen (pointsMap B S hS _ a' t₀)
    rw [← pointsMap_comp_apply, sq.w, pointsMap_comp_apply]
    refine (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hX _).2
      ⟨U, a, (BigFppfOver.toScheme B S hS).map c t,
        (isEtale_iff_presheaf_of_yoneda B S hS a).mpr ha, ?_, hgent⟩
    have h := chartPoint_pointsToScheme B S hS U a (pointsMap B S hS _ (yoneda.map c) t₀)
    rwa [pointsToScheme_pointsMap_yoneda, ht₀t] at h
  refine (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hZs.1 z).2
    ⟨Uz, a', u', (isEtale_iff_presheaf_of_yoneda B S hS a').mpr ha'et, ?_, hgenu'⟩
  have h := chartPoint_pointsToScheme B S hS Uz a' w
  rwa [hw1] at h

/-- Let `g : X' ⟶ X` be a morphism of algebraic spaces, `Z ⊆ X` a closed subspace, `D₀ ⊆ Z` an
open subspace which is an affine scheme `T`, and `f ∈ Γ(T)`. Let `V ⊆ X'` be an affine open
subspace whose points over `|Z|` lie over `|D₀|`. Then there is an affine open subspace `V' ⊆ V`
such that a point of `V` over `|Z|` lies in `V'` exactly when its image lies in the basic open
`D(f) ⊆ T`. -/
theorem exists_isOpenSubspace_isAffineSpace_preimage_basicOpen
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_hX' : IsAlgebraicSpace B S hS X')
    (g : X' ⟶ X) (Zs : Subfunctor X) (hZs : IsClosedSubspace B S hS Zs)
    (D₀ : Subfunctor Zs.toFunctor) (hD₀ : IsOpenSubspace B S hS D₀)
    {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (eD : yoneda.obj T ≅ D₀.toFunctor)
    (V : Subfunctor X') (hV : IsOpenSubspace B S hS V) (hVaff : IsAffineSpace B S hS V.toFunctor)
    (hVZ : ∀ p ∈ Set.range (pointsMap B S hS V.toFunctor V.ι),
      pointsMap B S hS _ g p ∈ Set.range (pointsMap B S hS Zs.toFunctor Zs.ι) →
        pointsMap B S hS _ g p ∈ Set.range (pointsMap B S hS D₀.toFunctor (D₀.ι ≫ Zs.ι)))
    (f : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    ∃ V' : Subfunctor X', IsOpenSubspace B S hS V' ∧ IsAffineSpace B S hS V'.toFunctor ∧
      Set.range (pointsMap B S hS V'.toFunctor V'.ι) ⊆
        Set.range (pointsMap B S hS V.toFunctor V.ι) ∧
      ∀ p ∈ Set.range (pointsMap B S hS V.toFunctor V.ι),
        pointsMap B S hS _ g p ∈ Set.range (pointsMap B S hS Zs.toFunctor Zs.ι) →
          (p ∈ Set.range (pointsMap B S hS V'.toFunctor V'.ι) ↔
            ∃ t ∈ ((BigFppfOver.toScheme B S hS).obj T).basicOpen f,
              pointsMap B S hS _ (eD.hom ≫ D₀.ι ≫ Zs.ι) ((pointsEquivScheme B S hS T).symm t) =
                pointsMap B S hS _ g p) := by
  classical
  obtain ⟨W, hWaff, ⟨eV⟩⟩ := hVaff
  set β := eV.inv ≫ V.ι with hβdef
  obtain ⟨hβ, hβrange⟩ := isOpenImmersion_comp_ι_and_range_eq B S hS hV eV.inv
  have : Mono β := mono_of_presheaf_isOpenImmersion hβ
  have hβinj := pointsMap_injective_of_mono B S hS β
  set C := hZs.2.rep.pullback (β ≫ g) with hC
  set c := hZs.2.rep.snd (β ≫ g) with hc
  set a' := hZs.2.rep.fst (β ≫ g) with ha'
  have sq : IsPullback a' (yoneda.map c) Zs.ι (β ≫ g) := hZs.2.rep.isPullback (β ≫ g)
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map c) :=
    MorphismProperty.relative.property_snd hZs.2 (β ≫ g)
  have hCalg : IsAlgebraicSpace B S hS (yoneda.obj C) := isAlgebraicSpace_yoneda B S hS C
  have hZinj := pointsMap_injective_of_mono B S hS Zs.ι
  have hDinj := pointsMap_injective_of_mono B S hS D₀.ι
  obtain ⟨φ₀, hφ₀⟩ := (factorsThrough_openSubspace_iff_points B S hS hZs.1 hCalg D₀ hD₀ a').2 (by
    rintro _ ⟨q, rfl⟩
    have hq : pointsMap B S hS _ Zs.ι (pointsMap B S hS _ a' q) =
        pointsMap B S hS _ g (pointsMap B S hS _ β (pointsMap B S hS _ (yoneda.map c) q)) := by
      rw [← pointsMap_comp_apply, sq.w, pointsMap_comp_apply, pointsMap_comp_apply]
    have hp1 : pointsMap B S hS _ β (pointsMap B S hS _ (yoneda.map c) q) ∈
        Set.range (pointsMap B S hS V.toFunctor V.ι) := hβrange ▸ Set.mem_range_self _
    obtain ⟨d, hd⟩ := hVZ _ hp1 ⟨_, hq⟩
    refine ⟨d, hZinj ?_⟩
    rw [← pointsMap_comp_apply, hd, hq])
  set φ : C ⟶ T := yoneda.preimage (φ₀ ≫ eD.inv) with hφdef
  have hφ : yoneda.map φ = φ₀ ≫ eD.inv := yoneda.map_preimage _
  obtain ⟨f', hf'⟩ := exists_preimage_basicOpen_eq_of_isClosedImmersion
    ((BigFppfOver.toScheme B S hS).map c) ((BigFppfOver.toScheme B S hS).map φ) f
  obtain ⟨V', hV', hV'aff, hV'range⟩ := exists_isOpenSubspace_isAffineSpace_of_isAffineOpen B S hS
    β hβ _ ((isAffineOpen_top _).basicOpen f')
  set δ := fun t => pointsMap B S hS _ (eD.hom ≫ D₀.ι ≫ Zs.ι)
    ((pointsEquivScheme B S hS T).symm t) with hδdef
  have hδinj : Function.Injective δ := by
    intro t₁ t₂ h
    have hm₁ : Mono D₀.ι := inferInstance
    have hm₂ : Mono Zs.ι := inferInstance
    have hm₃ : Mono (D₀.ι ≫ Zs.ι) := @mono_comp _ _ _ _ _ _ hm₁ _ hm₂
    have hm₀ : Mono eD.hom := ⟨fun u v w => by
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
        congrArg (· ≫ eD.inv) w⟩
    have hm : Mono (eD.hom ≫ D₀.ι ≫ Zs.ι) := @mono_comp _ _ _ _ _ _ hm₀ _ hm₃
    exact (pointsEquivScheme B S hS T).symm.injective (pointsMap_injective_of_mono B S hS _ h)
  have hδφ : ∀ q, δ ((BigFppfOver.toScheme B S hS).map φ (pointsToScheme B S hS C q)) =
      pointsMap B S hS _ Zs.ι (pointsMap B S hS _ a' q) := by
    intro q
    have h1 : (pointsEquivScheme B S hS T).symm
        ((BigFppfOver.toScheme B S hS).map φ (pointsToScheme B S hS C q)) =
          pointsMap B S hS _ (yoneda.map φ) q := by
      apply (pointsEquivScheme B S hS T).injective
      rw [Equiv.apply_symm_apply]
      exact (pointsToScheme_pointsMap_yoneda B S hS φ q).symm
    rw [hδdef]
    simp only
    rw [h1, ← pointsMap_comp_apply, hφ, ← hφ₀]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, pointsMap_comp_apply]
    rfl
  refine ⟨V', hV', hV'aff, ?_, ?_⟩
  · rw [hV'range, ← hβrange]
    rintro _ ⟨w, -, rfl⟩
    exact ⟨w, rfl⟩
  · rintro p hp ⟨z, hz⟩
    obtain ⟨ŵ, rfl⟩ : p ∈ Set.range (pointsMap B S hS _ β) := hβrange ▸ hp
    obtain ⟨q, hq1, hq2⟩ := exists_point_of_isPullback_presheaf B S hS sq z ŵ
      (by rw [hz]; simp only [hβdef, pointsMap_comp_apply])
    have hgp : pointsMap B S hS _ g (pointsMap B S hS _ β ŵ) =
        pointsMap B S hS _ Zs.ι (pointsMap B S hS _ a' q) := by
      rw [hq1, hz]
    have hcq : (BigFppfOver.toScheme B S hS).map c (pointsToScheme B S hS C q) =
        pointsToScheme B S hS W ŵ := by
      rw [← pointsToScheme_pointsMap_yoneda, hq2]
    have key : pointsMap B S hS _ β ŵ ∈ Set.range (pointsMap B S hS V'.toFunctor V'.ι) ↔
        (BigFppfOver.toScheme B S hS).map φ (pointsToScheme B S hS C q) ∈
          ((BigFppfOver.toScheme B S hS).obj T).basicOpen f := by
      rw [hV'range]
      constructor
      · rintro ⟨w, hw, hwŵ⟩
        rw [hβinj hwŵ] at hw
        have : pointsToScheme B S hS C q ∈ (BigFppfOver.toScheme B S hS).map c ⁻¹ᵁ
            ((BigFppfOver.toScheme B S hS).obj W).basicOpen f' := by
          rwa [Scheme.Hom.mem_preimage, hcq]
        rwa [hf'] at this
      · intro h
        refine ⟨ŵ, ?_, rfl⟩
        have h' : pointsToScheme B S hS C q ∈ (BigFppfOver.toScheme B S hS).map c ⁻¹ᵁ
            ((BigFppfOver.toScheme B S hS).obj W).basicOpen f' := by
          rwa [hf']
        rwa [Scheme.Hom.mem_preimage, hcq] at h'
    rw [key, hgp]
    refine ⟨fun h => ⟨_, h, hδφ q⟩, ?_⟩
    rintro ⟨t, ht, htq⟩
    rw [← hδφ q] at htq
    rwa [← hδinj htq]

/-- The image of a closed set of points under a finite morphism of algebraic spaces is closed. -/
theorem isClosed_image_pointsMap_of_isFinite {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X) (g : X' ⟶ X)
    (hg : IsFinite B S hS g) {C : Set (points B S hS X')} (hC : IsClosed C) :
    IsClosed (pointsMap B S hS _ g '' C) :=
  isClosed_of_universallyClosed B S hS hX g
    ((isFinite_iff_isAffineHom_and_isProper B S hS hX' hX g).mp hg).2.universallyClosed C hC

/-- Let `X` be separated and locally Noetherian, let `gₖ : X'ₖ ⟶ X` be a finite family of finite
morphisms whose images cover `|X|`, and let `W ⊆ X` be an open subspace whose inverse images
`gₖ⁻¹(W)` are all affine. Then `W` is affine. -/
theorem isAffineSpace_of_forall_isAffineSpace_preimage {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsAbsolutelySeparated B S hS B.contains_terminal X)
    (hnoeth : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    {m : ℕ} (X' : Fin m → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX' : ∀ k, IsAlgebraicSpace B S hS (X' k)) (g : ∀ k, X' k ⟶ X)
    (hg : ∀ k, IsFinite B S hS (g k))
    (hcover : ∀ y : points B S hS X, ∃ k, ∃ a : points B S hS (X' k),
      pointsMap B S hS _ (g k) a = y)
    (W : Subfunctor X) (hW : IsOpenSubspace B S hS W)
    (hWaff : ∀ k, IsAffineSpace B S hS (W.preimage (g k)).toFunctor) :
    IsAffineSpace B S hS W.toFunctor := by
  have hpre : ∀ k, IsOpenSubspace B S hS (W.preimage (g k)) := fun k =>
    isOpenSubspace_preimage B S hS (g k) W hX (hX' k) hW
  let Xw : AlgebraicSpaces B S hS := ⟨W.toFunctor, hW.1⟩
  let Y : Fin m → AlgebraicSpaces B S hS := fun k => ⟨(W.preimage (g k)).toFunctor, (hpre k).1⟩
  let f : ∀ k, Y k ⟶ Xw := fun k => ObjectProperty.homMk (W.fromPreimage (g k))
  have hsq : ∀ k, IsPullback (W.fromPreimage (g k)) (W.preimage (g k)).ι W.ι (g k) := fun k =>
    Subfunctor.isPullback_preimage (g k) W
  have hf : ∀ k, IsFinite B S hS (f k).hom := fun k =>
    isFinite_of_isPullback B S hS (hsq k).flip (hg k)
  have hsurj : ∀ w : points B S hS Xw.1, ∃ k, ∃ y : points B S hS (Y k).1,
      pointsMap B S hS (Y k).1 (f k).hom y = w := by
    intro w
    obtain ⟨k, a, ha⟩ := hcover (pointsMap B S hS _ W.ι w)
    obtain ⟨y, hy, -⟩ := exists_point_of_isPullback_presheaf B S hS (hsq k) w a ha.symm
    exact ⟨k, y, hy⟩
  have hqc : IsQuasiCompactSpace B S hS W.toFunctor := by
    refine isQuasiCompactSpace_of_finite_jointly_surjective B S hS (fun k => (Y k).2) hW.1
      (fun k => (f k).hom) ?_ fun k => ?_
    · refine Set.eq_univ_of_forall fun w => ?_
      obtain ⟨k, y, hy⟩ := hsurj w
      exact Set.mem_iUnion.2 ⟨k, y, hy⟩
    · obtain ⟨T, hT, ⟨e⟩⟩ := hWaff k
      exact isQuasiCompactSpace_of_iso B S hS e.symm
        (isQuasiCompactSpace_yoneda B S hS T inferInstance)
  have hWsep : IsAbsolutelySeparated B S hS B.contains_terminal W.toFunctor :=
    isAbsolutelySeparated_of_isSeparated B S hS B.contains_terminal hsep
      (isSeparated_of_mono W.ι inferInstance)
  have hWnoeth : HasEtaleLocalProperty B S hS W.toFunctor
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hW.1 hX W.ι
      (isLocallyOfFiniteType_of_isEtale B S hS hX (isEtale_of_isOpenImmersion B S hS hW.2)) hnoeth
  exact isAffineSpace_of_isFinite_of_forall_exists_pointsMap_eq B S hS B.contains_terminal Xw Y f
    hf hsurj hWaff ⟨hqc, isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS
      B.contains_terminal _ hWsep, hWnoeth⟩

/-- Two open subspaces with the same points are equal. -/
theorem eq_of_isOpenSubspace_of_range_eq {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {G H : Subfunctor F} (hG : IsOpenSubspace B S hS G) (hH : IsOpenSubspace B S hS H)
    (h : Set.range (pointsMap B S hS G.toFunctor G.ι) =
      Set.range (pointsMap B S hS H.toFunctor H.ι)) : G = H :=
  le_antisymm (le_of_range_pointsMap_ι_subset B S hS hH h.subset)
    (le_of_range_pointsMap_ι_subset B S hS hG h.symm.subset)

/-- The image in `X` of an affine open subspace `W` of an open subspace `N ⊆ X` is an affine open
subspace of `X`. -/
theorem exists_isOpenSubspace_isAffineSpace_of_isOpenSubspace {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {N : Subfunctor X} (hN : IsOpenSubspace B S hS N) {W : Subfunctor N.toFunctor}
    (hW : IsOpenSubspace B S hS W) (hWaff : IsAffineSpace B S hS W.toFunctor) :
    ∃ K : Subfunctor X, IsOpenSubspace B S hS K ∧ IsAffineSpace B S hS K.toFunctor ∧
      Set.range (pointsMap B S hS K.toFunctor K.ι) =
        Set.range (pointsMap B S hS W.toFunctor (W.ι ≫ N.ι)) := by
  have hopen : IsOpenImmersion B S hS (W.ι ≫ N.ι) := isOpenImmersion_comp B S hS _ _ hW.2 hN.2
  have : Mono (W.ι ≫ N.ι) := mono_of_presheaf_isOpenImmersion hopen
  exact ⟨Subfunctor.range (W.ι ≫ N.ι), isOpenSubspace_subfunctorRange B S hS hW.1 hopen,
    hWaff.of_iso (asIso (Subfunctor.toRange (W.ι ≫ N.ι))), range_pointsMap_ι_range B S hS _⟩

/-- Let `X` be a separated, locally Noetherian algebraic space over `S` and `x ∈ |X|` a point whose
local ring has dimension at most one. Let `gₖ : X'ₖ ⟶ X`, `k < m`, be finite morphisms whose
images cover `|X|`, each `X'ₖ` receiving a surjective finite locally free morphism
`hₖ : Y'ₖ ⟶ X'ₖ` from a scheme of the site. Let `Z ⊆ |X|` be a closed set containing no point of
codimension zero, off which the family is injective: a point outside `Z` has exactly one preimage
in `⨆ₖ |X'ₖ|`. Then `x` lies in an open subspace of `X` which is an affine scheme. -/
theorem exists_isOpenSubspace_isRepresentable_of_finite_family
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsAbsolutelySeparated B S hS B.contains_terminal X)
    (hnoeth : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (x : points B S hS X) (hdim : localRingDimension B S hS x ≤ 1)
    {m : ℕ} (X' : Fin m → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX' : ∀ k, IsAlgebraicSpace B S hS (X' k)) (g : ∀ k, X' k ⟶ X)
    (hg : ∀ k, IsFinite B S hS (g k))
    (Y' : Fin m → BigFppfOver B S hS) (h : ∀ k, yoneda.obj (Y' k) ⟶ X' k)
    (hhsurj : ∀ k, (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (h k))
    (hhflf : ∀ k, (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (h k))
    (Z : Set (points B S hS X)) (hZ : IsClosed Z)
    (hZ0 : ∀ z ∈ Z, localRingDimension B S hS z ≠ 0)
    (hcover : ∀ y : points B S hS X, ∃ k, ∃ a : points B S hS (X' k),
      pointsMap B S hS _ (g k) a = y)
    (hinj : ∀ y ∉ Z, ∀ (k k' : Fin m) (a : points B S hS (X' k)) (a' : points B S hS (X' k')),
      pointsMap B S hS _ (g k) a = y → pointsMap B S hS _ (g k') a' = y →
        (⟨k, a⟩ : Σ k, points B S hS (X' k)) = ⟨k', a'⟩) :
    ∃ W : Subfunctor X, IsOpenSubspace B S hS W ∧ IsAffineSpace B S hS W.toFunctor ∧
      x ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) := by
  classical
  choose O hO hOrep hOfib using fun k =>
    exists_isOpenSubspace_isRepresentable_of_isFiniteLocallyFree_cover B S hS hX (hX' k) hsep
      hnoeth x hdim (g k) (hg k) (Y' k) (h k) (hhsurj k) (hhflf k)
  choose A hA hAaff hAfib using fun k =>
    exists_isOpenSubspace_isAffineSpace_of_isRepresentable_of_fibre B S hS hX (hX' k) hsep hnoeth
      x hdim (g k) (hg k) (O k) (hO k) (hOrep k) (hOfib k)
  have hfibfin : ∀ k, (pointsMap B S hS _ (g k) ⁻¹' {x}).Finite := fun k =>
    finite_preimage_singleton_of_isFinite B S hS (hX' k) hX (g k) (hg k) x
  have hfibA : ∀ k, pointsMap B S hS _ (g k) ⁻¹' {x} ⊆
      Set.range (pointsMap B S hS (A k).toFunctor (A k).ι) := fun k p hp => hAfib k p hp
  suffices hfinal : ∃ (Wset : Set (points B S hS X)) (V : ∀ k, Subfunctor (X' k)),
      IsOpen Wset ∧ x ∈ Wset ∧ (∀ k, IsOpenSubspace B S hS (V k)) ∧
      (∀ k, IsAffineSpace B S hS (V k).toFunctor) ∧
      ∀ k p, pointsMap B S hS _ (g k) p ∈ Wset ↔
        p ∈ Set.range (pointsMap B S hS (V k).toFunctor (V k).ι) by
    obtain ⟨Wset, V, hWopen, hxW, hV, hVaff, hpre⟩ := hfinal
    obtain ⟨W, hW, hWrange⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hX Wset hWopen
    have hWV : ∀ k, W.preimage (g k) = V k := fun k =>
      eq_of_isOpenSubspace_of_range_eq B S hS (isOpenSubspace_preimage B S hS (g k) W hX (hX' k) hW)
        (hV k) (by
          rw [pointsRange_preimage, hWrange]
          ext p
          exact hpre k p)
    have hWaff := isAffineSpace_of_forall_isAffineSpace_preimage B S hS hX hsep hnoeth X' hX' g hg
      hcover W hW fun k => hWV k ▸ hVaff k
    exact ⟨W, hW, hWaff, hWrange ▸ hxW⟩
  by_cases hxZ : x ∉ Z
  · choose V hV hVaff hfibV hVsub using fun k =>
      exists_isOpenSubspace_isAffineSpace_subset B S hS (A k) (hA k) (hAaff k) _ (hfibfin k)
        (hfibA k) (pointsMap B S hS _ (g k) ⁻¹' Zᶜ)
        (hZ.isOpen_compl.preimage (continuous_pointsMap B S hS (g k)))
        (fun p hp => by
          rw [Set.mem_preimage, Set.mem_singleton_iff.mp hp]
          exact hxZ)
    refine ⟨(Z ∪ ⋃ k, pointsMap B S hS _ (g k) ''
        (Set.range (pointsMap B S hS (V k).toFunctor (V k).ι))ᶜ)ᶜ, V, ?_, ?_, hV, hVaff, ?_⟩
    · refine (hZ.union (isClosed_iUnion_of_finite fun k => ?_)).isOpen_compl
      exact isClosed_image_pointsMap_of_isFinite B S hS (hX' k) hX (g k) (hg k)
        (isOpen_range_pointsMap_of_isOpenImmersion B S hS _ (hV k).2).isClosed_compl
    · simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_iUnion, Set.mem_image, not_or,
        not_exists, not_and]
      exact ⟨hxZ, fun k p hp hpx => hp (hfibV k hpx)⟩
    · intro k p
      simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_iUnion, Set.mem_image, not_or,
        not_exists, not_and]
      constructor
      · rintro ⟨-, h⟩
        by_contra hp
        exact h k p hp rfl
      · intro hp
        have hpZ : pointsMap B S hS _ (g k) p ∉ Z := (hVsub k hp).1
        refine ⟨hpZ, fun j q hq hqp => hq ?_⟩
        obtain ⟨rfl, hqp'⟩ := Sigma.mk.inj_iff.mp (hinj _ hpZ j k q p hqp rfl)
        rw [eq_of_heq hqp']
        exact hp
  · rw [not_not] at hxZ
    set Zs := reducedClosedSubspace B S hS X hX Z hZ with hZsdef
    have hZs : IsClosedSubspace B S hS Zs := isClosedSubspace_reducedClosedSubspace B S hS X hX Z hZ
    have hZsrange : Set.range (pointsMap B S hS Zs.toFunctor Zs.ι) = Z :=
      range_pointsMap_ι_reducedClosedSubspace B S hS X hX Z hZ
    have hZinj := pointsMap_injective_of_mono B S hS Zs.ι
    obtain ⟨xZ, hxZ'⟩ : x ∈ Set.range (pointsMap B S hS Zs.toFunctor Zs.ι) := hZsrange ▸ hxZ
    have hdimZ : localRingDimension B S hS xZ = 0 :=
      localRingDimension_eq_zero_of_isClosedSubspace B S hS hX Zs hZs xZ (hxZ' ▸ hdim)
        fun w => hZ0 _ (hZsrange ▸ ⟨w, rfl⟩)
    have hZsqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Zs.toFunctor :=
      isAbsolutelyQuasiSeparated_subfunctor B S hS hsep Zs
    obtain ⟨G₀, hG₀, hG₀rep, hxG₀⟩ :=
      exists_isRepresentable_isOpenSubspace_of_localRingDimension_eq_zero B S hS
        B.contains_terminal Zs.toFunctor hZs.1 hZsqs xZ hdimZ
    set e₀ := G₀.toFunctor.reprW with he₀
    set α₀ := e₀.hom ≫ G₀.ι with hα₀def
    have hα₀ : IsOpenImmersion B S hS α₀ :=
      isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS e₀.hom) hG₀.2
    obtain ⟨y₀, hy₀⟩ : xZ ∈ Set.range (pointsMap B S hS _ α₀) := by
      obtain ⟨z, rfl⟩ := hxG₀
      refine ⟨pointsMap B S hS _ e₀.inv z, ?_⟩
      rw [hα₀def, ← pointsMap_comp_apply, Iso.inv_hom_id_assoc]
    obtain ⟨A₀, hA₀, hyA₀, -⟩ := exists_isAffineOpen_mem_and_subset
      (x := pointsToScheme B S hS G₀.toFunctor.reprX y₀) (U := ⊤) trivial
    obtain ⟨D₀, hD₀, hD₀aff, hD₀range⟩ :=
      exists_isOpenSubspace_isAffineSpace_of_isAffineOpen B S hS α₀ hα₀ A₀ hA₀
    have hxD₀ : xZ ∈ Set.range (pointsMap B S hS D₀.toFunctor D₀.ι) := by
      rw [hD₀range]
      exact ⟨y₀, hyA₀, hy₀⟩
    obtain ⟨T, hTaff, ⟨eD'⟩⟩ := hD₀aff
    set eD := eD'.symm with heD
    set N₁ := (pointsMap B S hS _ Zs.ι '' (Set.range (pointsMap B S hS D₀.toFunctor D₀.ι))ᶜ)ᶜ
      with hN₁def
    have hN₁ : IsOpen N₁ := (isClosed_image_pointsMap_of_isFinite B S hS hZs.1 hX Zs.ι
      (isFinite_of_isClosedImmersion B S hS Zs.ι hZs.2)
      (isOpen_range_pointsMap_of_isOpenImmersion B S hS _ hD₀.2).isClosed_compl).isOpen_compl
    have hxN₁ : x ∈ N₁ := by
      rintro ⟨z, hz, hzx⟩
      apply hz
      rw [hZinj (hzx.trans hxZ'.symm)]
      exact hxD₀
    have hZN₁ : ∀ y ∈ N₁, y ∈ Z →
        y ∈ Set.range (pointsMap B S hS D₀.toFunctor (D₀.ι ≫ Zs.ι)) := by
      intro y hyN hyZ
      obtain ⟨z, rfl⟩ : y ∈ Set.range (pointsMap B S hS Zs.toFunctor Zs.ι) := hZsrange ▸ hyZ
      by_cases hzD : z ∈ Set.range (pointsMap B S hS D₀.toFunctor D₀.ι)
      · obtain ⟨d, rfl⟩ := hzD
        exact ⟨d, pointsMap_comp_apply B S hS _ _ _⟩
      · exact absurd ⟨z, hzD, rfl⟩ hyN
    choose V hV hVaff hfibV hVsub using fun k =>
      exists_isOpenSubspace_isAffineSpace_subset B S hS (A k) (hA k) (hAaff k) _ (hfibfin k)
        (hfibA k) (pointsMap B S hS _ (g k) ⁻¹' N₁)
        (hN₁.preimage (continuous_pointsMap B S hS (g k)))
        (fun p hp => by
          rw [Set.mem_preimage, Set.mem_singleton_iff.mp hp]
          exact hxN₁)
    have hVZ : ∀ k, ∀ p ∈ Set.range (pointsMap B S hS (V k).toFunctor (V k).ι),
        pointsMap B S hS _ (g k) p ∈ Set.range (pointsMap B S hS Zs.toFunctor Zs.ι) →
          pointsMap B S hS _ (g k) p ∈ Set.range (pointsMap B S hS D₀.toFunctor (D₀.ι ≫ Zs.ι)) :=
      fun k p hp hpZ => hZN₁ _ (hVsub k hp).1 (hZsrange ▸ hpZ)
    set R := fun k => pointsMap B S hS _ (g k) ''
      (pointsMap B S hS _ (g k) ⁻¹' Z ∩ (Set.range (pointsMap B S hS (V k).toFunctor (V k).ι))ᶜ)
      with hRdef
    have hR : ∀ k, IsClosed (R k) := fun k =>
      isClosed_image_pointsMap_of_isFinite B S hS (hX' k) hX (g k) (hg k)
        ((hZ.preimage (continuous_pointsMap B S hS (g k))).inter
          (isOpen_range_pointsMap_of_isOpenImmersion B S hS _ (hV k).2).isClosed_compl)
    have hxR : ∀ k, x ∉ R k := by
      rintro k ⟨p, ⟨-, hpV⟩, hpx⟩
      exact hpV (hfibV k hpx)
    set δ := fun t => pointsMap B S hS _ (eD.hom ≫ D₀.ι ≫ Zs.ι)
      ((pointsEquivScheme B S hS T).symm t) with hδdef
    have hδcont : Continuous δ :=
      (continuous_pointsMap B S hS _).comp (schemePointsHomeomorph B S hS T).symm.continuous
    obtain ⟨d₀, hd₀⟩ := hxD₀
    set tx := pointsToScheme B S hS T (pointsMap B S hS _ eD.inv d₀) with htx
    have hδtx : δ tx = x := by
      rw [hδdef]
      simp only
      rw [htx, show (pointsEquivScheme B S hS T).symm
          (pointsToScheme B S hS T (pointsMap B S hS _ eD.inv d₀)) =
            pointsMap B S hS _ eD.inv d₀ from
          (pointsEquivScheme B S hS T).symm_apply_apply _]
      rw [← pointsMap_comp_apply, Iso.inv_hom_id_assoc, pointsMap_comp_apply, hd₀, hxZ']
    set Q := δ ⁻¹' ⋃ k, R k with hQdef
    have hQ : IsClosed Q := (isClosed_iUnion_of_finite hR).preimage hδcont
    have htxQ : tx ∉ Q := by
      rw [hQdef, Set.mem_preimage, hδtx, Set.mem_iUnion]
      rintro ⟨k, hk⟩
      exact hxR k hk
    obtain ⟨f, hfQ, htxf⟩ :=
      (isAffineOpen_top ((BigFppfOver.toScheme B S hS).obj T)).exists_basicOpen_le
        (V := ⟨Qᶜ, hQ.isOpen_compl⟩) ⟨tx, htxQ⟩ trivial
    choose V' hV' hV'aff hV'sub hV'iff using fun k =>
      exists_isOpenSubspace_isAffineSpace_preimage_basicOpen B S hS (hX' k) (g k) Zs hZs D₀ hD₀
        eD (V k) (hV k) (hVaff k) (hVZ k) f
    set Dset := δ '' (((BigFppfOver.toScheme B S hS).obj T).basicOpen f : Set _) with hDsetdef
    have hDsetZ : Dset ⊆ Z := by
      rintro _ ⟨t, -, rfl⟩
      rw [← hZsrange, hδdef]
      simp only [pointsMap_comp_apply]
      exact ⟨_, rfl⟩
    have hZD : IsClosed (Z ∩ Dsetᶜ) := by
      set E := pointsMap B S hS _ (eD.hom ≫ D₀.ι) ''
        (pointsToScheme B S hS T ⁻¹' (((BigFppfOver.toScheme B S hS).obj T).basicOpen f : Set _))
        with hEdef
      have hEopen : IsOpen E := by
        refine isOpenMap_pointsMap_of_isOpenImmersion B S hS _
          (isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS eD.hom) hD₀.2) _ ?_
        exact (((BigFppfOver.toScheme B S hS).obj T).basicOpen f).isOpen.preimage
          (schemePointsHomeomorph B S hS T).continuous
      have hset : Z ∩ Dsetᶜ = pointsMap B S hS _ Zs.ι '' Eᶜ := by
        ext y
        constructor
        · rintro ⟨hyZ, hyD⟩
          obtain ⟨z, rfl⟩ : y ∈ Set.range (pointsMap B S hS Zs.toFunctor Zs.ι) := hZsrange ▸ hyZ
          refine ⟨z, fun hzE => hyD ?_, rfl⟩
          obtain ⟨u, hu, rfl⟩ := hzE
          refine ⟨pointsToScheme B S hS T u, hu, ?_⟩
          rw [hδdef]
          simp only
          rw [show (pointsEquivScheme B S hS T).symm (pointsToScheme B S hS T u) = u from
            (pointsEquivScheme B S hS T).symm_apply_apply u]
          simp only [pointsMap_comp_apply]
        · rintro ⟨z, hzE, rfl⟩
          refine ⟨hZsrange ▸ ⟨z, rfl⟩, ?_⟩
          rintro ⟨t, ht, htz⟩
          apply hzE
          refine ⟨(pointsEquivScheme B S hS T).symm t, ?_, hZinj ?_⟩
          · rw [Set.mem_preimage,
              show pointsToScheme B S hS T ((pointsEquivScheme B S hS T).symm t) = t from
                (pointsEquivScheme B S hS T).apply_symm_apply t]
            exact ht
          · rw [← htz, hδdef]
            simp only [pointsMap_comp_apply]
      rw [hset]
      exact isClosed_image_pointsMap_of_isFinite B S hS hZs.1 hX Zs.ι
        (isFinite_of_isClosedImmersion B S hS Zs.ι hZs.2) hEopen.isClosed_compl
    have hDQ : ∀ y ∈ Dset, ∀ k, y ∉ R k := by
      rintro _ ⟨t, ht, rfl⟩ k hk
      exact hfQ ht (Set.mem_iUnion.2 ⟨k, hk⟩)
    refine ⟨((Z ∩ Dsetᶜ) ∪ ⋃ k, pointsMap B S hS _ (g k) ''
        (Set.range (pointsMap B S hS (V' k).toFunctor (V' k).ι))ᶜ)ᶜ, V', ?_, ?_, hV', hV'aff, ?_⟩
    · refine (hZD.union (isClosed_iUnion_of_finite fun k => ?_)).isOpen_compl
      exact isClosed_image_pointsMap_of_isFinite B S hS (hX' k) hX (g k) (hg k)
        (isOpen_range_pointsMap_of_isOpenImmersion B S hS _ (hV' k).2).isClosed_compl
    · have hxD : x ∈ Dset := ⟨tx, htxf, hδtx⟩
      simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_inter_iff, Set.mem_iUnion,
        Set.mem_image, not_or, not_exists, not_and, not_not]
      refine ⟨fun _ => hxD, fun k p hp hpx => hp ?_⟩
      have hpV := hfibV k hpx
      refine (hV'iff k p hpV (hpx ▸ hxZ' ▸ ⟨xZ, rfl⟩)).2 ⟨tx, htxf, ?_⟩
      exact hδtx.trans hpx.symm
    · intro k p
      simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_inter_iff, Set.mem_iUnion,
        Set.mem_image, not_or, not_exists, not_and, not_not]
      constructor
      · rintro ⟨-, h⟩
        by_contra hp
        exact h k p hp rfl
      · intro hp
        have hpV := hV'sub k hp
        have hpD : pointsMap B S hS _ (g k) p ∈ Z → pointsMap B S hS _ (g k) p ∈ Dset :=
          fun hpZ => (hV'iff k p hpV (hZsrange ▸ hpZ)).1 hp
        refine ⟨hpD, fun j q hq hqp => hq ?_⟩
        by_cases hpZ : pointsMap B S hS _ (g k) p ∈ Z
        · have hD := hpD hpZ
          have hqV : q ∈ Set.range (pointsMap B S hS (V j).toFunctor (V j).ι) := by
            by_contra hqV
            exact hDQ _ hD j ⟨q, ⟨by rw [Set.mem_preimage, hqp]; exact hpZ, hqV⟩, hqp⟩
          obtain ⟨t, ht, htp⟩ := hD
          exact (hV'iff j q hqV (by rw [hZsrange, hqp]; exact hpZ)).2
            ⟨t, ht, htp.trans hqp.symm⟩
        · obtain ⟨rfl, hqp'⟩ := Sigma.mk.inj_iff.mp (hinj _ hpZ j k q p hqp rfl)
          rw [eq_of_heq hqp']
          exact hp

end AlgebraicGeometry.Space

end
