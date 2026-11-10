module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.DualizingDegree
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.AmpleNoRationalBridge
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyBaseChangeFieldFibre
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenLoci
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStableOpen
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableCurveFamilyFibres
public import StacksFrontier.AlgebraicGeometry.Quot.StableFamilyDualizingAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreChartPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationArrowContainment
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperLimitOfFinitePresentationEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspacePushforwardCech
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts

/-!
# Stable fibres form an open locus in prestable families, from the relative dualizing sheaf

Let `f : X → S` be a family of curves. This file proves condition (o) of Section 0E0E for the
property "the fibres are stable" relative to prestable families
(`AlgebraicGeometry.IsOpenCurvesLocusWithin` for `AlgebraicGeometry.CurveFamily.HasStableFibres`
within `AlgebraicGeometry.IsPrestableCurveFamily`): there is an open `W ⊆ S` such that a
prestable family `F → S'` mapping to `X → S` has stable fibres exactly when `S' → S` factors
through `W`. This is the openness of the stable locus in the proof of Stacks 0E76, obtained from
Stacks 0E74 and Stacks 0D3D.

The proof follows the source. The relative dualizing sheaf `ω_{X/S}` is an invertible module on
the total space of an at-worst-nodal family whose restriction to every fibre is the dualizing
sheaf of the fibre (Stacks 0E6Q, 0E6R and the discussion after 0E6Q); its existence is the input
`homega` of the main theorems, written out as the statement it is (for the first main theorem
only over affine bases). Let `U ⊆ S` be the open over which `X` is at-worst-nodal (Stacks 0DSH,
`AlgebraicGeometry.isOpenCurvesLocus_isAtWorstNodal`). For every affine open `A ⊆ U`, Stacks 0D3D
(`AlgebraicGeometry.Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isProper`) gives
the open `V_A ⊆ A` over which `ω_{X_A/A}` is relatively ample, and `W` is the union of the `V_A`
read in `S`. A prestable family over `S'` lies over `U`; it factors through `W` exactly when every
field-valued point of `S'` does, and at a field-valued point `Spec K → S'` this is the
ampleness of `ω` on the fibre (Stacks 01VK), that is of the dualizing sheaf of the fibre. A
fibre of a prestable family is proper, of dimension one, at-worst-nodal with `H⁰ = K`
(`AlgebraicGeometry.CurveFamily.fibre_standing_of_isPrestableCurveFamily`), and for such a curve
ampleness of `ω` is equivalent to having genus at least two and neither rational tails nor
rational bridges (Stacks 0E74 at a point: Stacks 0E63, 0E64, 0E3Q with 0C19).

## Main results

* `hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField_of_isIso`:
  a proper at-worst-nodal curve of dimension one over `k` with `H⁰ = k` has genus `≥ 2` and no
  rational tails or bridges exactly when its dualizing sheaf is invertible and ample.
* `AlgebraicGeometry.isOpenCurvesLocusWithin_hasStableFibres_of_dualizingSheaf_of_isAffine`:
  condition (o) for stable fibres within prestable families, from the existence of the relative
  dualizing sheaf of at-worst-nodal families over affine bases; `W` is the union over the affine
  opens `A` of the at-worst-nodal locus of the opens of Stacks 0D3D for `ω_{X_A/A}`.
* `AlgebraicGeometry.isOpenCurvesLocusWithin_hasStableFibres_of_dualizingSheaf`: the same from the
  relative dualizing sheaf of all at-worst-nodal families.

## References

* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0E6Q](https://stacks.math.columbia.edu/tag/0E6Q)
* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Stable curves over a field and their dualizing sheaf -/

/-- **Stacks 0E74 over a field.** Let `X` be proper over a field `k`, of dimension one, with
`H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities. Then `X` has genus at least two and neither a
rational tail nor a rational bridge exactly when its dualizing sheaf `ω_X` is invertible and
ample.

Given the conditions, `ω_X` is ample by
`AlgebraicGeometry.forall_not_isRationalTail_and_isRationalBridge_iff_isAmple` (Stacks 0E3Q).
Conversely an ample `ω_X` forces genus at least two
(`AlgebraicGeometry.two_le_genus_of_isAmple_dualizingSheafOverField_of`, with Stacks 0C19,
`AlgebraicGeometry.invertibleCurveDegree_dualizingSheafOverField`), and then excludes rational
tails and bridges by the same equivalence (Stacks 0E63, 0E64). -/
theorem hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField_of_isIso
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hH0 : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop))
    (hdim : topologicalKrullDim X = 1)
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X) :
    HasGenusTwoNoRationalTailNoRationalBridge k f ↔
      ∃ _ : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          (Stacks.Duality.dualizingSheafOverField f),
        Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField f) := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : IsProper (X ↘ Spec (.of k)) := inferInstanceAs (IsProper f)
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop) := hH0
  have h0C19 : ∀ (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] [IsGorenstein X]
      (hdim : topologicalKrullDim X = 1) [ConnectedSpace X]
      [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField f)],
      invertibleCurveDegree k f hdim.le (Stacks.Duality.dualizingSheafOverField f) =
        2 * (genus f : ℤ) - 2 :=
    fun k _ X f _ _ _ hdim _ _ => invertibleCurveDegree_dualizingSheafOverField k f hdim
  constructor
  · rintro ⟨hg, htail, _, hbridge⟩
    exact ⟨_, (forall_not_isRationalTail_and_isRationalBridge_iff_isAmple hdim hnodal hg).1
      ⟨htail, hbridge⟩⟩
  · intro hω
    have hg := two_le_genus_of_isAmple_dualizingSheafOverField_of h0C19 k X hdim hnodal hω
    obtain ⟨_, hamp⟩ := hω
    obtain ⟨htail, hbridge⟩ :=
      (forall_not_isRationalTail_and_isRationalBridge_iff_isAmple hdim hnodal hg).2 hamp
    exact ⟨hg, htail, inferInstance, hbridge⟩

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-! ### Open subspaces of a scheme read on scheme points -/

/-- A morphism of the site into `Y` factors through an open subspace `A` of `Y` exactly when it
sends every point into the corresponding open of the scheme `Y`. -/
private theorem exists_lift_iff_forall_mem_opensOfOpenSubspace {Y T : BigFppfOver B integerBase hZ}
    (A : Subfunctor (yoneda.obj Y)) (hA : Space.IsOpenSubspace B integerBase hZ A) (x : T ⟶ Y) :
    (∃ l : (schemeSpace T).1 ⟶ A.toFunctor, l ≫ A.ι = (schemeSpaceMap x).hom) ↔
      ∀ y, ((𝒯).map x) y ∈ Space.opensOfOpenSubspace B integerBase hZ Y A hA := by
  refine (Space.FinitePartUniversalOpen.exists_lift_iff_mem (X := yoneda.obj Y) A T
    (yoneda.map x)).trans ?_
  rw [yonedaEquiv_yoneda_map]
  exact Space.mem_iff_of_isOpenSubspace B integerBase hZ Y A hA x

/-- A morphism of the site into `Y` factors through the open subspace of an open `Q` of the
scheme `Y` exactly when it sends every point into `Q`. -/
private theorem exists_lift_subspaceOfOpens_iff {Y T : BigFppfOver B integerBase hZ}
    (Q : ((𝒯).obj Y).Opens) (x : T ⟶ Y) :
    (∃ l : (schemeSpace T).1 ⟶ (Space.subspaceOfOpens B integerBase hZ Y Q).toFunctor,
        l ≫ (Space.subspaceOfOpens B integerBase hZ Y Q).ι = (schemeSpaceMap x).hom) ↔
      ∀ y, ((𝒯).map x) y ∈ Q := by
  refine (Space.FinitePartUniversalOpen.exists_lift_iff_mem (X := yoneda.obj Y) _ T
    (yoneda.map x)).trans ?_
  rw [yonedaEquiv_yoneda_map]
  exact Space.mem_subspaceOfOpens_iff B integerBase hZ Y Q x

/-- The inclusion of an open subscheme of an object of the site is an open immersion. -/
private instance isOpenImmersion_toScheme_map_openSubHom (A : BigFppfOver B integerBase hZ)
    (O : ((𝒯).obj A).Opens) : IsOpenImmersion ((𝒯).map (Space.openSubHom A O)) := by
  rw [Space.toScheme_map_openSubHom]
  exact inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _))

/-! ### Relative ampleness over an affine scheme of the site -/

/-- **Ampleness on a scheme over an affine base.** Let `ω` be an invertible module on an
algebraic space `X`, let `v : V ⟶ T` be a morphism of the site with `T` affine and let
`q : V ⟶ X`. If the pullback of `ω` to `V` is identified with a module `M`, then the pullback of
`ω` is ample relative to `V ⟶ T` in the sense of algebraic spaces exactly when `M` is invertible
and ample on `V`.

This is the argument of `AlgebraicGeometry.CurveFamily.isRelativelyAmple_fibre_iff`, for any
affine target: Stacks 0D32 at `V` and Stacks 01VK. -/
private theorem isRelativelyAmple_schemeSpaceMap_iff {X : AlgebraicSpaces B integerBase hZ}
    {ω : Space.Modules.{u, u} B integerBase hZ X.1 X.2}
    (hωinv : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ X.1 X.2).O)).property ω)
    {T V : BigFppfOver B integerBase hZ} [IsAffine ((𝒯).obj T)] (v : V ⟶ T)
    (q : yoneda.obj V ⟶ X.1) (M : ((𝒯).obj V).Modules)
    (e : Space.baseChangeModule B integerBase hZ ω V q ≅ M) :
    Space.IsRelativelyAmple B integerBase hZ (schemeSpaceMap v)
        ((Space.modulePullback B integerBase hZ
          (ObjectProperty.homMk q : schemeSpace V ⟶ X)).obj ω) ↔
      ∃ _ : SheafOfModules.IsInvertible ((𝒯).obj V).toRingedSpace.presheaf
          (structureSheafRing ((𝒯).obj V).toRingedSpace).property M,
        Scheme.Modules.IsAmple ((𝒯).obj V) M := by
  let L' := (Space.modulePullback B integerBase hZ
    (ObjectProperty.homMk q : schemeSpace V ⟶ X)).obj ω
  let E : Space.baseChangeModule B integerBase hZ L' V (𝟙 _) ≅ M :=
    (Space.baseChangeModuleCompIso B integerBase hZ
      (ObjectProperty.homMk q : schemeSpace V ⟶ X) ω V (𝟙 _)).symm ≪≫
      eqToIso (congrArg (Space.baseChangeModule B integerBase hZ ω V) (Category.id_comp q)) ≪≫ e
  constructor
  · intro hamp
    obtain ⟨hL, hrel⟩ := hamp.2 T V (𝟙 _) (𝟙 _) v (IsPullback.id_horiz (yoneda.map v))
    have : Stacks.Ample.IsInvertibleModule _ M :=
      Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ E
    have hrel' := (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ E).mp hrel
    have hst := (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple
      ((𝒯).map v) _).mp hrel'
    exact ⟨this, (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mp hst⟩
  · rintro ⟨hinv, hamp⟩
    have hL'inv : Stacks.SheafOfModules.IsInvertible
        (Space.structurePresheaf B integerBase hZ (schemeSpace V).1)
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.smallEtaleRingedSite B integerBase hZ (schemeSpace V).1
            (schemeSpace V).2).O)).property L' :=
      Stacks.SheafOfModules.isInvertible_pullbackModules_obj
        (f := Space.smallEtaleRingedToposModulesHom B integerBase hZ
          (ObjectProperty.homMk q : schemeSpace V ⟶ X)) (L := ω) (hL := hωinv)
    have : Stacks.Ample.IsInvertibleModule _ M := hinv
    refine Space.isRelativelyAmple_of_exists_scheme _ L' hL'inv T (Iso.refl _)
      ⟨V, Iso.refl _, Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ E.symm, ?_⟩
    have h1 := (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple
      ((𝒯).map v) _).mpr ((Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr hamp)
    have : Stacks.Ample.IsInvertibleModule _
        (Space.baseChangeModule B integerBase hZ L' V (𝟙 _)) :=
      Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ E.symm
    have h2 := (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ E).mpr h1
    convert h2 using 2
    · apply yoneda.map_injective
      simp only [Functor.map_preimage, Iso.refl_hom, schemeSpaceMap_hom]
      exact (Category.id_comp _).trans (Category.comp_id _)
    · rfl

/-! ### The open locus of stable fibres -/

/-- A pullback square over the Yoneda image of `t` is one over `yonedaEquiv.symm t`. -/
private theorem isPullback_yonedaEquiv_symm {C : Type*} [Category C] {W V : C} (t : W ⟶ V)
    {P X : Cᵒᵖ ⥤ Type _} {p : P ⟶ X} {f : P ⟶ yoneda.obj W} {g : X ⟶ yoneda.obj V}
    (h : IsPullback p f g (yoneda.map t)) : IsPullback p f g (yonedaEquiv.symm t) :=
  (yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map _).symm : yonedaEquiv.symm t = _) ▸ h

/-- A cartesian outer rectangle whose right square is cartesian has a cartesian left square. -/
private theorem exists_isPullback_of_isPullback_right {C : Type*} [Category C]
    {P X Y Z V W : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hR : IsPullback fst snd f g) {a : V ⟶ X} {w : V ⟶ W} {k : W ⟶ Y}
    (h : IsPullback a w f (k ≫ g)) : ∃ u : V ⟶ P, IsPullback u w snd k := by
  have hw : a ≫ f = (w ≫ k) ≫ g := by simpa using h.w
  refine ⟨hR.lift a (w ≫ k) hw, IsPullback.of_right ?_ (hR.lift_snd _ _ _) hR⟩
  rwa [hR.lift_fst]

/-- **Stability of a fibre is membership in the ample locus of an affine piece.** Let `G` be a
family of curves, `j : A ⟶ S` the inclusion of an open of its base over which `G` restricts to
`G_A`, `ω` an invertible module on the total space of `G_A` restricting on every fibre to the
dualizing sheaf, and `V_A ⊆ A` the open of Stacks 0D3D for `ω`. For a prestable family `F`
mapping to `G` and a field-valued point `P` of its base whose image `c` lies in `A`, the fibre of
`F` at `P` has a presentation with genus at least two and no rational tails or bridges exactly
when `c` lies in `V_A`. -/
private theorem exists_hasGenusTwo_iff_mem_image {G F : CurveFamily B hZ} (a : F ⟶ G)
    (hF : IsPrestableCurveFamily B hZ F) (O : ((𝒯).obj G.base).Opens)
    (ω : Space.Modules.{u, u} B integerBase hZ
      (G.baseChange (Space.openSubHom G.base O)).total.obj
      (G.baseChange (Space.openSubHom G.base O)).total.property)
    (hωinv : Stacks.SheafOfModules.IsInvertible
      (Space.structurePresheaf B integerBase hZ (G.baseChange (Space.openSubHom G.base O)).total.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B integerBase hZ
        (G.baseChange (Space.openSubHom G.base O)).total.1
        (G.baseChange (Space.openSubHom G.base O)).total.2).O)).property ω)
    (hωfib : ∀ (p : Space.FieldValuedPoint B integerBase hZ
        (schemeSpace (G.baseChange (Space.openSubHom G.base O)).base).obj)
      (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
      (q : yoneda.obj V ⟶ (G.baseChange (Space.openSubHom G.base O)).total.obj)
      [IsProper ((𝒯).map v)],
      IsPullback q (yoneda.map v) (G.baseChange (Space.openSubHom G.base O)).toBase.hom
        (yonedaEquiv.symm p.value) →
      Nonempty (Space.baseChangeModule B integerBase hZ ω V q ≅
        Stacks.Duality.dualizingSheafOverField ((𝒯).map v)))
    (V₁ : Subfunctor (yoneda.obj (G.baseChange (Space.openSubHom G.base O)).base))
    (hV₁ : Space.IsOpenSubspace B integerBase hZ V₁)
    (h₁ : ∀ ⦃X' Y' : AlgebraicSpaces B integerBase hZ⦄
      (g : Y' ⟶ schemeSpace (G.baseChange (Space.openSubHom G.base O)).base)
      (p : X' ⟶ (G.baseChange (Space.openSubHom G.base O)).total) (f' : X' ⟶ Y'),
      IsPullback p f' (G.baseChange (Space.openSubHom G.base O)).toBase g →
        ((∃ l : Y'.1 ⟶ V₁.toFunctor, l ≫ V₁.ι = g.hom) ↔
          Space.IsRelativelyAmple B integerBase hZ f'
            ((Space.modulePullback B integerBase hZ p).obj ω)))
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj)
    (hPA : ∀ z, ((𝒯).map (P.value ≫ a.baseMap)) z ∈ O) :
    (∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject)
        (q : yoneda.obj V ⟶ F.total.obj),
        IsPullback q (yoneda.map v) F.toBase.hom (yonedaEquiv.symm P.value) ∧
          HasGenusTwoNoRationalTailNoRationalBridge P.carrier ((𝒯).map v)) ↔
      ∀ z, ((𝒯).map (P.value ≫ a.baseMap)) z ∈
        ((𝒯).map (Space.openSubHom G.base O)) ''ᵁ
          Space.opensOfOpenSubspace B integerBase hZ _ V₁ hV₁ := by
  let GA := G.baseChange (Space.openSubHom G.base O)
  let j := Space.openSubHom G.base O
  have : IsOpenImmersion ((𝒯).map j) := isOpenImmersion_toScheme_map_openSubHom _ _
  let c' : P.siteObject ⟶ GA.base := Space.openSubLift G.base O (P.value ≫ a.baseMap) hPA
  have hc' : c' ≫ j = P.value ≫ a.baseMap :=
    Space.openSubLift_comp_openSubHom G.base O (P.value ≫ a.baseMap) hPA
  have hRHS : (∀ z, ((𝒯).map (P.value ≫ a.baseMap)) z ∈
      ((𝒯).map j) ''ᵁ Space.opensOfOpenSubspace B integerBase hZ _ V₁ hV₁) ↔
      ∃ l : (schemeSpace P.siteObject).1 ⟶ V₁.toFunctor, l ≫ V₁.ι = (schemeSpaceMap c').hom := by
    rw [exists_lift_iff_forall_mem_opensOfOpenSubspace V₁ hV₁ c']
    refine forall_congr' fun z => ?_
    rw [← hc']
    change ((𝒯).map j) (((𝒯).map c') z) ∈ _ ↔ _
    exact ((𝒯).map j).isOpenEmbedding.injective.mem_set_image
  refine Iff.trans ?_ hRHS.symm
  have hcart := (G.baseChangeHom j).cartesian
  have hcomp : schemeSpaceMap P.value ≫ schemeSpaceMap a.baseMap =
      schemeSpaceMap c' ≫ schemeSpaceMap (G.baseChangeHom j).baseMap :=
    ObjectProperty.hom_ext _ ((yoneda.map_comp _ _).symm.trans
      ((congrArg yoneda.map hc'.symm).trans (yoneda.map_comp _ _)))
  have : IsAffine ((𝒯).obj P.siteObject) := inferInstanceAs (IsAffine (Spec _))
  -- on a presentation of the fibre at `P`: stability is membership in `V_A`
  have key : ∀ (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject)
      (q : yoneda.obj V ⟶ F.total.obj),
      IsPullback q (yoneda.map v) F.toBase.hom (yonedaEquiv.symm P.value) →
      (HasGenusTwoNoRationalTailNoRationalBridge P.carrier ((𝒯).map v) ↔
        ∃ l : (schemeSpace P.siteObject).1 ⟶ V₁.toFunctor,
          l ≫ V₁.ι = (schemeSpaceMap c').hom) := by
    intro V v q hsq
    obtain ⟨hprop, hH0, hdim, hnodal⟩ := CurveFamily.fibre_standing_of_isPrestableCurveFamily hF hsq
    have hsqG := (CurveFamily.isPullback_schemeSpace_of_isPullback_yoneda hsq).paste_horiz
      a.cartesian
    rw [hcomp] at hsqG
    obtain ⟨r, hsqA⟩ := exists_isPullback_of_isPullback_right hcart hsqG
    rw [h₁ _ _ _ hsqA]
    let P₀ : Space.FieldValuedPoint B integerBase hZ (schemeSpace GA.base).obj :=
      ⟨P.carrier, P.contained, P.toBase, c'⟩
    have hsq₀ : IsPullback r.hom (yoneda.map v) GA.toBase.hom (yonedaEquiv.symm P₀.value) := by
      exact isPullback_yonedaEquiv_symm _ (AlgebraicSpaces.isPullback_hom B integerBase hZ hsqA)
    obtain ⟨E⟩ := @hωfib P₀ V v r.hom hprop hsq₀
    rw [show r = ObjectProperty.homMk r.hom from ObjectProperty.hom_ext _ rfl]
    exact (hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField_of_isIso
      P.carrier ((𝒯).map v) hH0 hdim hnodal).trans
      (isRelativelyAmple_schemeSpaceMap_iff hωinv v r.hom _ E).symm
  refine ⟨fun ⟨V, v, q, hsq, hst⟩ => (key V v q hsq).1 hst, fun hl => ?_⟩
  -- relative ampleness makes the fibre of `G_A` at `c'` representable
  have sqX := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ GA.toBase
    (schemeSpaceMap c')
  obtain ⟨V, v, q', hsq'⟩ := ((h₁ _ _ _ sqX).1 hl).1 (𝟙 (yoneda.obj P.siteObject))
  have h₂ := hsq'.paste_horiz (AlgebraicSpaces.isPullback_hom B integerBase hZ sqX)
  have e₂ : 𝟙 (yoneda.obj P.siteObject) ≫ (schemeSpaceMap c').hom = yoneda.map c' :=
    Category.id_comp _
  have h₃ : IsPullback (ObjectProperty.homMk (q' ≫ pullback.fst GA.toBase.hom
      (schemeSpaceMap c').hom) : schemeSpace V ⟶ GA.total) (schemeSpaceMap v) GA.toBase
      (schemeSpaceMap c') :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) (e₂ ▸ h₂)
  have h₄ := h₃.paste_horiz hcart
  rw [← hcomp] at h₄
  obtain ⟨qF, h₅⟩ := exists_isPullback_of_isPullback_right a.cartesian h₄
  have hsq : IsPullback qF.hom (yoneda.map v) F.toBase.hom (yonedaEquiv.symm P.value) := by
    exact isPullback_yonedaEquiv_symm _ (AlgebraicSpaces.isPullback_hom B integerBase hZ h₅)
  exact ⟨V, v, _, hsq, (key V v _ hsq).2 hl⟩

/-- **Condition (o) for stable fibres within prestable families, from the relative dualizing
sheaf over affine bases.** The same as
`AlgebraicGeometry.isOpenCurvesLocusWithin_hasStableFibres_of_dualizingSheaf`, with the relative
dualizing sheaf required only for at-worst-nodal families over an affine base: the open `W` is the
union, over the affine opens `A` of the at-worst-nodal locus of the base, of the opens of
Stacks 0D3D for `ω_{X_A/A}`. -/
theorem isOpenCurvesLocusWithin_hasStableFibres_of_dualizingSheaf_of_isAffine
    (homega : ∀ G : CurveFamily B hZ, IsAffine ((𝒯).obj G.base) →
      Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ G.toBase.hom →
      ∃ ω : Space.Modules.{u, u} B integerBase hZ G.total.obj G.total.property,
        Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ G.total.1)
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (Space.smallEtaleRingedSite B integerBase hZ G.total.1 G.total.2).O)).property ω ∧
        ∀ (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace G.base).obj)
          (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
          (q : yoneda.obj V ⟶ G.total.obj) [IsProper ((𝒯).map v)],
          IsPullback q (yoneda.map v) G.toBase.hom (yonedaEquiv.symm p.value) →
          Nonempty (Space.baseChangeModule B integerBase hZ ω V q ≅
            Stacks.Duality.dualizingSheafOverField ((𝒯).map v))) :
    IsOpenCurvesLocusWithin B hZ (IsPrestableCurveFamily B hZ)
      (CurveFamily.HasStableFibres B hZ) := by
  intro G
  obtain ⟨W₀, hW₀, h₀⟩ := isOpenCurvesLocus_isAtWorstNodal B hZ G
  set Q₀ := Space.opensOfOpenSubspace B integerBase hZ G.base W₀ hW₀ with hQ₀
  let ι := {A : ((𝒯).obj G.base).affineOpens // (A : ((𝒯).obj G.base).Opens) ≤ Q₀}
  have hjA : ∀ (O : ((𝒯).obj G.base).Opens) y, ((𝒯).map (Space.openSubHom G.base O)) y ∈ O := by
    intro O y
    rw [Space.toScheme_map_openSubHom]
    have hy := Set.mem_range_self (f := O.ι) y
    rwa [Scheme.Opens.range_ι] at hy
  have hω : ∀ A : ι, ∃ ω : Space.Modules.{u, u} B integerBase hZ
      (G.baseChange (Space.openSubHom G.base A.1.1)).total.obj
      (G.baseChange (Space.openSubHom G.base A.1.1)).total.property, _ := fun A =>
    homega _ A.1.2 ((h₀ _ (G.baseChangeHom (Space.openSubHom G.base A.1.1))).2
      ((exists_lift_iff_forall_mem_opensOfOpenSubspace W₀ hW₀ _).2
        fun y => A.2 (hjA A.1.1 y)))
  choose ω hω using hω
  have hV : ∀ A : ι, _ := fun A =>
    Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isProper B integerBase hZ
      (G.baseChange (Space.openSubHom G.base A.1.1)).proper (hω A).1
  choose V₁ hV₁ h₁ using hV
  let QA : ι → ((𝒯).obj G.base).Opens := fun A =>
    ((𝒯).map (Space.openSubHom G.base A.1.1)) ''ᵁ
      Space.opensOfOpenSubspace B integerBase hZ _ (V₁ A) (hV₁ A)
  have hQA : ∀ A x, x ∈ QA A → x ∈ (A.1 : ((𝒯).obj G.base).Opens) := by
    rintro A x ⟨w, -, rfl⟩
    exact hjA _ w
  let Q : ((𝒯).obj G.base).Opens := ⨆ A, QA A
  refine ⟨Space.subspaceOfOpens B integerBase hZ G.base Q,
    Space.isOpenSubspace_subspaceOfOpens B integerBase hZ G.base Q, fun F a hF => ?_⟩
  refine Iff.trans ?_ (exists_lift_subspaceOfOpens_iff Q a.baseMap).symm
  have hx : ∀ y, ((𝒯).map a.baseMap) y ∈ Q₀ :=
    (exists_lift_iff_forall_mem_opensOfOpenSubspace W₀ hW₀ a.baseMap).1 ((h₀ F a).1 hF.1)
  have hpt : ∀ (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj) z z',
      ((𝒯).map (P.value ≫ a.baseMap)) z = ((𝒯).map (P.value ≫ a.baseMap)) z' := by
    intro P z z'
    have : Subsingleton ((𝒯).obj P.siteObject) := inferInstanceAs (Subsingleton (Spec _))
    exact congrArg (fun w => ((𝒯).map (P.value ≫ a.baseMap)) w)
      (Subsingleton.elim (α := (𝒯).obj P.siteObject) z z')
  have hloc : ∀ (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj) A z,
      ((𝒯).map (P.value ≫ a.baseMap)) z ∈ (A.1 : ((𝒯).obj G.base).Opens) →
      ((∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject)
        (q : yoneda.obj V ⟶ F.total.obj),
        IsPullback q (yoneda.map v) F.toBase.hom (yonedaEquiv.symm P.value) ∧
          HasGenusTwoNoRationalTailNoRationalBridge P.carrier ((𝒯).map v)) ↔
        ((𝒯).map (P.value ≫ a.baseMap)) z ∈ QA A) := by
    intro P A z hz
    have hPA : ∀ z', ((𝒯).map (P.value ≫ a.baseMap)) z' ∈ (A.1 : ((𝒯).obj G.base).Opens) :=
      fun z' => hpt P z' z ▸ hz
    rw [exists_hasGenusTwo_iff_mem_image a hF A.1.1 (ω A) (hω A).1 (hω A).2 (V₁ A) (hV₁ A)
      (h₁ A) P hPA]
    exact ⟨fun h => h z, fun h z' => hpt P z' z ▸ h⟩
  have hexA : ∀ x ∈ Q₀, ∃ A : ι, x ∈ (A.1 : ((𝒯).obj G.base).Opens) := by
    intro x hxQ
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAQ⟩ :=
      ((𝒯).obj G.base).isBasis_affineOpens.exists_subset_of_mem_open hxQ Q₀.isOpen
    exact ⟨⟨⟨A, hA⟩, hAQ⟩, hxA⟩
  constructor
  · intro hst y
    let P := Space.residueFieldMapPoint B integerBase hZ F.base y
      (B.residueField_spec_contains F.base.left.property y)
    obtain ⟨z⟩ : Nonempty ((𝒯).obj P.siteObject) := inferInstanceAs (Nonempty (Spec _))
    have hzy : ((𝒯).map (P.value ≫ a.baseMap)) z = ((𝒯).map a.baseMap) y := by
      change ((𝒯).map a.baseMap) (((𝒯).map P.value) z) = _
      rw [show ((𝒯).map P.value) z = y from Scheme.fromSpecResidueField_apply _ _]
    obtain ⟨A, hA⟩ := hexA _ (hx y)
    rw [← hzy] at hA ⊢
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨A, (hloc P A z hA).1 (hst P)⟩
  · intro hQ P
    obtain ⟨z⟩ : Nonempty ((𝒯).obj P.siteObject) := inferInstanceAs (Nonempty (Spec _))
    obtain ⟨A, hA⟩ := TopologicalSpace.Opens.mem_iSup.1
      (hQ (((𝒯).map P.value) z) : ((𝒯).map (P.value ≫ a.baseMap)) z ∈ Q)
    exact (hloc P A z (hQA A _ hA)).2 hA

/-- **Condition (o) for stable fibres within prestable families (Stacks 0E74 with 0D3D), from
the relative dualizing sheaf.** Every family of curves `G` has an open subspace `W` of its base
such that a prestable family of curves `F` mapping to `G` has stable fibres (genus at least two,
no rational tails, no rational bridges) exactly when its morphism of base schemes factors
through `W`.

The input `homega` is the existence of the relative dualizing sheaf of an at-worst-nodal family,
Stacks 0E6Q/0E6R with the base change of the discussion after 0E6Q and Section 0E6S: for every
family of curves `G` which is at-worst-nodal of relative dimension one there is an invertible
module `ω` on its total space whose pullback to every fibre — presented by a scheme `V` of the
site with a cartesian square over a field-valued point `Spec K → S` of the base — is the
dualizing sheaf of `V` over `K` (`Stacks.Duality.dualizingSheafOverField`, Stacks 0BS2). The
invertibility is in the form taken by Stacks 0D3D. -/
theorem isOpenCurvesLocusWithin_hasStableFibres_of_dualizingSheaf
    (homega : ∀ G : CurveFamily B hZ,
      Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ G.toBase.hom →
      ∃ ω : Space.Modules.{u, u} B integerBase hZ G.total.obj G.total.property,
        Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ G.total.1)
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (Space.smallEtaleRingedSite B integerBase hZ G.total.1 G.total.2).O)).property ω ∧
        ∀ (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace G.base).obj)
          (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
          (q : yoneda.obj V ⟶ G.total.obj) [IsProper ((𝒯).map v)],
          IsPullback q (yoneda.map v) G.toBase.hom (yonedaEquiv.symm p.value) →
          Nonempty (Space.baseChangeModule B integerBase hZ ω V q ≅
            Stacks.Duality.dualizingSheafOverField ((𝒯).map v))) :
    IsOpenCurvesLocusWithin B hZ (IsPrestableCurveFamily B hZ)
      (CurveFamily.HasStableFibres B hZ) :=
  isOpenCurvesLocusWithin_hasStableFibres_of_dualizingSheaf_of_isAffine fun G _ hG => homega G hG

end AlgebraicGeometry

end
