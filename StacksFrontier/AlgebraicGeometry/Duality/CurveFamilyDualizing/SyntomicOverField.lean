module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalEtaleComposition
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GorensteinDualizingInvertible
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.FiniteTypeOverFieldDualizing
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Regular
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekBounded
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplexOfCharts
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekStructureSheafCharts
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FreeNeighbourhoodRank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankBaseOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SyntomicFibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModelTargetIso
public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekPseudofunctor
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexAffineSections
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexRestrictDiagonal
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexUniqueIso
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativeDualizing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange

/-!
# The relative dualizing complex of a syntomic curve over a field

Let `k` be a field and `f : U ⟶ Spec k` syntomic of relative dimension one. This file shows
that a relative dualizing complex `K` for `f` (Stacks 0E2T) is, locally on `U`, the structure
sheaf placed in degree `-1`.

## Main results

* `Stacks.Duality.SyntomicOverField.exists_restrict_upperShriek_iso_single`: on a scheme `V`
  separated and of finite type over `k`, syntomic of relative dimension one, `f^!𝒪_{Spec k}` is
  near every point the structure sheaf in degree `-1`.
* `Stacks.Duality.SyntomicOverField.exists_derivedPullback_iso_single`: a relative dualizing
  complex `K` for `f : U ⟶ Spec k` syntomic of relative dimension one satisfies
  `K|_{U'} ≅ 𝒪_{U'}[1]` on a neighbourhood `U'` of every point.
* `Stacks.Duality.SyntomicOverField.isZero_homology_of_ne` and
  `Stacks.Duality.SyntomicOverField.isFiniteLocallyFreeOfRank_homology_neg_one`: `H^m(K) = 0`
  for `m ≠ -1`, and `H^{-1}(K)` is finite locally free of rank one.

## The argument

`V` is Gorenstein (Stacks 0BVA) and `ω = f^!𝒪_{Spec k}` is a dualizing complex on `V`
(Stacks 0AA3), so at every point `x` the stalks of its cohomology sheaves vanish outside one
degree `n`, where they are `𝒪_{V,x}` (Stacks 0BFQ). The morphism is Cohen–Macaulay of relative
dimension one, so near `x` the cohomology sheaves of `ω` vanish outside degree `-1`
(Stacks 0C0Z), hence `n = -1`. The coherent sheaf `H^{-1}(ω)` with free stalk of rank one at `x`
is free of rank one near `x` (Stacks 0B8J), and there `ω` is `H^{-1}(ω)[1] ≅ 𝒪[1]`.

For `U` itself, not necessarily separated, the restriction of a relative dualizing complex `K` to
an affine open `V` is a relative dualizing complex for `V ⟶ Spec k` (Stacks 0E2X), as is
`f_V^!𝒪_{Spec k}` at any compactification (Stacks 0E9W, Nagata), so the two are isomorphic
(Stacks 0E2W).

## Implementation notes

`f^!` is computed in the locally small model of `D(𝒪_V)`, while relative dualizing complexes live
in the standard model; `nonempty_restrict_standard_iso_single` moves the local description from
one to the other. The standard model is passed explicitly (`letI`, `@`) in the statements, since
instance search would otherwise choose the locally small model for sheaves of modules.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Duality.SyntomicOverField

/-! ### Stalks and restrictions -/

/-- The stalk at a point of an open `U` of a sheaf of modules zero on `U` is zero. -/
theorem isZero_modulesStalkFunctor_of_isZero_restrict {X : Scheme.{u}} (U : X.Opens)
    (G : X.Modules) (x : X) (hx : x ∈ U)
    (h : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj G)) :
    IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj G) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  exact AddCommGrpCat.isZero_iff_subsingleton.1
    (Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isZero_stalk_of_isZero_restrict U G x hx h)

/-- A sheaf of modules zero on an open `U` restricts to zero along every open immersion with
image in `U`. -/
theorem isZero_restrict_of_isZero_restrict {X Z : Scheme.{u}} (U : X.Opens) (G : X.Modules)
    (h : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj G)) (i : Z ⟶ X) [IsOpenImmersion i]
    (hi : Set.range i ⊆ (U : Set X)) :
    IsZero ((Scheme.Modules.restrictFunctor i).obj G) := by
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun z => ?_
  exact (Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isZero_stalk_of_isZero_restrict
    U G (i z) (hi ⟨z, rfl⟩) h).of_iso ((Scheme.Modules.restrictStalkNatIso i z).app G)

/-- `Spec k` is a Gorenstein scheme: its only affine open `⊤` has a field of sections. -/
theorem isGorenstein_spec_field (k : Type u) [Field k] :
    IsGorenstein (Spec (CommRingCat.of k)) := by
  refine isGorenstein_of_isRegular _ fun _ => ⟨⟨⊤, isAffineOpen_top _⟩, trivial, ?_⟩
  exact IsRegularRing.of_ringEquiv
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv

/-- An open immersion with image in an open `U` factors through an open immersion into `U`. -/
private theorem exists_isOpenImmersion_comp_ι_eq {X Z : Scheme.{u}} (U : X.Opens) (i : Z ⟶ X)
    [IsOpenImmersion i] (h : Set.range i ⊆ (U : Set X)) :
    ∃ i' : Z ⟶ U, IsOpenImmersion i' ∧ i' ≫ U.ι = i := by
  have h' : Set.range i ⊆ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
  exact ⟨_, IsOpenImmersion.of_comp _ U.ι, IsOpenImmersion.lift_fac U.ι i h'⟩

/-! ### `f^!𝒪` near a point -/

variable {k : Type u} [Field k]

/-- **`f^!𝒪_{Spec k}` of a syntomic morphism of relative dimension one is near every point the
structure sheaf in degree `-1`.** Let `g : V ⟶ Spec k` be separated, of finite type and
syntomic of relative dimension one, and `j` a compactification of `g`. Every `x ∈ V` has an open
neighbourhood `W` such that for every open immersion `i : Z ⟶ V` with image in `W` the
restriction of `ω = g^!𝒪_{Spec k}` along `i` is `𝒪_Z` placed in degree `-1`. -/
theorem exists_restrict_upperShriek_iso_single {V : Scheme.{u}}
    (g : V ⟶ Spec (CommRingCat.of k)) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (hg : SyntomicOfRelativeDimension 1 g)
    (j : CompactificationOf (Over.mk (ftsHomToBase g).left)) (x : V) :
    ∃ W : V.Opens, x ∈ W ∧ ∀ {Z : Scheme.{u}} (i : Z ⟶ V) [IsOpenImmersion i],
      Set.range i ⊆ (W : Set V) →
      Nonempty ((Scheme.Modules.restrictFunctor i).mapDerivedCategory.obj
          (relativeDualizingComplexObj (ftsHomToBase g) j) ≅
        (DerivedCategory.singleFunctor Z.Modules (-1)).obj
          (SheafOfModules.unit Z.ringCatSheaf)) := by
  classical
  let φ := ftsHomToBase g
  let ω := relativeDualizingComplexObj φ j
  have hsyn : Syntomic g := hg.1
  have : Flat φ.left := AlgebraicGeometry.flat hsyn
  have : LocallyOfFinitePresentation φ.left := AlgebraicGeometry.locallyOfFinitePresentation hsyn
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian g
  have hGk : IsGorenstein (Spec (CommRingCat.of k)) := isGorenstein_spec_field k
  have hG : IsGorenstein V := isGorenstein_of_isLocalCompleteIntersectionMorphism g
    (isLocalCompleteIntersectionMorphism_of_syntomic hsyn) hGk
  -- `ω` is a dualizing complex
  have h0 : IsDualizingComplex
      (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k))).obj :=
    isDualizingComplex_unit_overField (𝟙 (Spec (CommRingCat.of k)))
  have hω : IsDualizingComplex ω := isDualizingComplex_upperShriek_obj φ j _ h0
  obtain ⟨n, -, ⟨e⟩⟩ :=
    exists_stalk_homology_concentrated_free_of_isGorensteinLocalRing hω x
      (hG.isGorensteinLocalRing x)
  -- the cohomology sheaves of `ω` are coherent
  have hcoh : ∀ i : ℤ, _root_.SheafOfModules.IsCoherent
      ((DerivedCategory.homologyFunctor V.Modules i).obj ω) := fun i =>
    (derivedCategoryBBounded_upperShriek_derivedStructureSheaf φ j (fun y => by
      obtain ⟨_, ⟨B, hB, rfl⟩, hyB, -⟩ :=
        (Spec (CommRingCat.of k)).isBasis_affineOpens.exists_subset_of_mem_open
          (Set.mem_univ (φ.left y)) isOpen_univ
      obtain ⟨_, ⟨A, hA, rfl⟩, hyA, hAB⟩ :=
        V.isBasis_affineOpens.exists_subset_of_mem_open hyB (φ.left ⁻¹ᵁ B).isOpen
      have hft : (φ.left.appLE B A hAB).hom.FiniteType :=
        (locallyOfFiniteType_left φ).finiteType_appLE hB hA hAB
      let p := (Dualizing.nonempty_polynomialPresentation _ hft).some
      exact ⟨A, hA, B, hB, hAB, hyA, p, upperShriekStructureSheafCharts φ j B hB A hA hAB p⟩)).2 i
  -- `H^n(ω)` is free of rank one near `x`
  obtain ⟨W₁, hxW₁, ⟨eW₁⟩⟩ := Scheme.Modules.exists_free_restrict_of_stalk_basis _ (hcoh n) x
    ((Module.Basis.singleton (Fin 1) (V.presheaf.stalk x)).map e.toLinearEquiv.symm)
  -- near `x` the cohomology sheaves of `ω` vanish outside degree `-1`
  have hCM : φ.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left φ) :=
    isCohenMacaulay_of_syntomic hsyn _
  have : IsAffine (FTS.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
  obtain ⟨U, hU, -, hxU, hUW₁, N, -, -, hNz, -, he⟩ :=
    exists_chart_homology_of_isCohenMacaulayAt (upperShriekStructureSheafCharts φ j) x
      (hCM x) 1 (hg.2 x) W₁ hxW₁ ⊤ (isAffineOpen_top _) trivial
  have hzU : ∀ i : ℤ, i ≠ -1 → IsZero ((Scheme.Modules.restrictFunctor U.ι).obj
      ((DerivedCategory.homologyFunctor V.Modules i).obj ω)) := fun i hi =>
    IsZero.of_iso ((Scheme.Modules.pullback hU.isoSpec.hom).map_isZero
      ((tilde.functor Γ(V, U)).map_isZero (hNz i (by simpa using hi)))) (he i).some
  -- hence `n = -1`
  have hn : n = -1 := by
    by_contra hne
    have hz := (isZero_modulesStalkFunctor_of_isZero_restrict U _ x hxU (hzU n hne)).of_iso
      e.symm
    rw [ModuleCat.isZero_iff_subsingleton] at hz
    exact not_subsingleton (V.presheaf.stalk x) hz
  subst hn
  refine ⟨U, hxU, ?_⟩
  intro Z i hiI hi
  have : IsOpenImmersion i := hiI
  let R := Scheme.Modules.restrictFunctor i
  let L := R.mapDerivedCategory.obj ω
  let eH := fun m : ℤ =>
    (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso R m).app ω
  have hzL : ∀ m : ℤ, m ≠ -1 →
      IsZero ((DerivedCategory.homologyFunctor Z.Modules m).obj L) := fun m hm =>
    (isZero_restrict_of_isZero_restrict (X := V) U _ (hzU m hm) i hi).of_iso (eH m)
  have : L.IsGE (-1) := (DerivedCategory.isGE_iff L (-1)).2 fun m hm => hzL m (by omega)
  have : L.IsLE (-1) := (DerivedCategory.isLE_iff L (-1)).2 fun m hm => hzL m (by omega)
  obtain ⟨M, ⟨eL⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE L (-1)
  -- `i` factors through `W₁`
  obtain ⟨i', _, hi'⟩ := exists_isOpenImmersion_comp_ι_eq W₁ i (hi.trans hUW₁)
  let eR : R.obj ((DerivedCategory.homologyFunctor V.Modules (-1)).obj ω) ≅
      SheafOfModules.unit Z.ringCatSheaf :=
    (Scheme.Modules.restrictFunctorCongr hi'.symm).app _ ≪≫
      (Scheme.Modules.restrictFunctorComp i' W₁.ι).app _ ≪≫
      (Scheme.Modules.restrictFunctor i').mapIso
        (eW₁ ≪≫ Stacks.SheafOfModules.Invertible.freeUniqueIso _) ≪≫
      Scheme.Modules.restrictUnitIso i'
  let eM : M ≅ SheafOfModules.unit Z.ringCatSheaf :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso Z.Modules (-1)).app M).symm ≪≫
      (DerivedCategory.homologyFunctor Z.Modules (-1)).mapIso eL.symm ≪≫ eH (-1) ≪≫ eR
  exact ⟨eL ≪≫ (DerivedCategory.singleFunctor Z.Modules (-1)).mapIso eM⟩

/-! ### From the locally small model to the standard model -/

/-- **An isomorphism `ω|_Z ≅ 𝒪_Z[-n]` read at the standard model.** For an open immersion
`i : Z ⟶ V`, an isomorphism between the restriction of `ω` along `i` and `𝒪_Z` placed in degree
`n`, in the locally small model of `D(𝒪_Z)`, gives one in the standard model: the comparison
equivalence of the two models is the identity on objects and fully faithful, and it carries the
restriction and the degree-`n` functor of one model to those of the other. -/
theorem nonempty_restrict_standard_iso_single {V Z : Scheme.{u}} (i : Z ⟶ V) [IsOpenImmersion i]
    (ω : DerivedCategory V.Modules) (n : ℤ)
    (h : Nonempty ((Scheme.Modules.restrictFunctor i).mapDerivedCategory.obj ω ≅
      (DerivedCategory.singleFunctor Z.Modules n).obj (SheafOfModules.unit Z.ringCatSheaf))) :
    letI := HasDerivedCategory.standard V.Modules
    letI := HasDerivedCategory.standard Z.Modules
    Nonempty ((Scheme.Modules.restrictFunctor i).mapDerivedCategory.obj ω ≅
      (DerivedCategory.singleFunctor Z.Modules n).obj (SheafOfModules.unit Z.ringCatSheaf)) := by
  obtain ⟨e⟩ := h
  let F := Scheme.Modules.restrictFunctor i
  let E := Stacks.Injectives.grothendieckModelEquiv.{u} Z.Modules
  let O := SheafOfModules.unit Z.ringCatSheaf
  let e₁ := (Stacks.Injectives.mapDerivedCategoryTargetModelIso.{u} Z.Modules
    (hd₁ := HasDerivedCategory.standard V.Modules) F).app ω
  let e₂ := Stacks.Injectives.mapDerivedCategoryObjIso.{u} V.Modules
    (hd₂ := Scheme.Modules.hasDerivedCategory Z) F ω
  let e₄ := (@DerivedCategory.singleFunctorIsoCompQ Z.Modules _ _
      (Scheme.Modules.hasDerivedCategory Z) n).app O ≪≫
    E.functor.mapIso ((@DerivedCategory.singleFunctorIsoCompQ Z.Modules _ _
      (HasDerivedCategory.standard Z.Modules) n).app O).symm
  exact ⟨E.fullyFaithfulFunctor.preimageIso (e₁ ≪≫ e₂ ≪≫ e ≪≫ e₄)⟩

end Stacks.Duality.SyntomicOverField

/-! ### The relative dualizing complex -/

namespace Stacks.Duality.SyntomicOverField


variable {k : Type u} [Field k]

/-- A morphism syntomic of relative dimension `d` is flat. -/
theorem flat_of_syntomicOfRelativeDimension {d : ℕ} {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : SyntomicOfRelativeDimension d f) : Flat f :=
  AlgebraicGeometry.flat hf.1

/-- A morphism syntomic of relative dimension `d` is locally of finite presentation. -/
theorem locallyOfFinitePresentation_of_syntomicOfRelativeDimension {d : ℕ} {X S : Scheme.{u}}
    {f : X ⟶ S} (hf : SyntomicOfRelativeDimension d f) : LocallyOfFinitePresentation f :=
  AlgebraicGeometry.locallyOfFinitePresentation hf.1

/-- **A relative dualizing complex of a syntomic curve over a field is locally `𝒪[1]`.** Let
`f : U ⟶ Spec k` be syntomic of relative dimension one, `D` an open of `U ×_k U` through which
the diagonal factors as a closed immersion, and `(K, ξ)` a relative dualizing complex for `f`
relative to `D` (Stacks 0E2T). Every point `x` of `U` has an open neighbourhood `U'` with
`K|_{U'} ≅ 𝒪_{U'}[1]`, the structure sheaf placed in degree `-1`.

On an affine open `V ∋ x` the restriction of `(K, ξ)` is a relative dualizing complex for
`V ⟶ Spec k`, as is `f_V^!𝒪_{Spec k}` (Stacks 0E9W), so the two agree (Stacks 0E2W), and
`f_V^!𝒪_{Spec k}` is `𝒪[1]` near `x` by `exists_restrict_upperShriek_iso_single`. -/
theorem exists_derivedPullback_iso_single {U : Scheme.{u}} (f : U ⟶ Spec (CommRingCat.of k))
    (hf : SyntomicOfRelativeDimension 1 f) (D : f.DiagonalOpen)
    (K : @DerivedCategory (_root_.StrictlyPerfect.OXMod.{u, u} U.toRingedSpace) _ _
      (HasDerivedCategory.standard _))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K)
    (hK : letI := HasDerivedCategory.standard (_root_.StrictlyPerfect.OXMod.{u, u}
        ((Spec (CommRingCat.of k)).toRingedSpace.inverseImage f.base))
      letI := fun W : Opens
          ((Spec (CommRingCat.of k)).toRingedSpace.inverseImage f.base).carrier =>
        HasDerivedCategory.standard (_root_.StrictlyPerfect.OXMod.{u, u}
          (((Spec (CommRingCat.of k)).toRingedSpace.inverseImage f.base).restrict
            W.isOpenEmbedding))
      haveI := flat_of_syntomicOfRelativeDimension hf
      haveI := locallyOfFinitePresentation_of_syntomicOfRelativeDimension hf
      Scheme.Hom.IsRelativeDualizingComplex.{u + 1, u} f
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage (Spec (CommRingCat.of k)).toRingedSpace f.base)) D K ξ)
    (x : U) :
    ∃ U' : U.Opens, x ∈ U' ∧
      Nonempty ((@Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback _ _
          U'.ι.toLRSHom.toShHom (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
          _).obj K ≅
        (@DerivedCategory.singleFunctor U'.toScheme.Modules _ _ (HasDerivedCategory.standard _)
          (-1)).obj (SheafOfModules.unit U'.toScheme.ringCatSheaf)) := by
  have := flat_of_syntomicOfRelativeDimension hf
  have := locallyOfFinitePresentation_of_syntomicOfRelativeDimension hf
  obtain ⟨_, ⟨V₀, hV, rfl⟩, hxV, -⟩ :=
    U.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let V : U.Opens := V₀
  have : IsAffine V.toScheme := hV
  let g := V.ι ≫ f
  have hg : SyntomicOfRelativeDimension 1 g := syntomicOfRelativeDimension_one_comp_etale f V.ι hf
  have : IsSeparated g := inferInstance
  have : LocallyOfFiniteType g := inferInstance
  have : QuasiCompact g := inferInstance
  obtain ⟨j⟩ := Stacks.Duality.nonempty_compactificationOf (ftsHomToBase g)
  obtain ⟨W, hxW, hW⟩ := exists_restrict_upperShriek_iso_single g hg j ⟨x, hxV⟩
  -- `K|_V` and `g^!𝒪` are relative dualizing complexes for `g`, hence isomorphic
  have hKV := hK.restrict V.ι
  have : Flat (ftsHomToBase g).left := inferInstanceAs (Flat (V.ι ≫ f))
  obtain ⟨ξ', hω⟩ :=
    Stacks.Duality.exists_isRelativeDualizingComplex_upperShriek (ftsHomToBase g) j (D.restrict V.ι)
  obtain ⟨α, -, -⟩ := hKV.existsUnique_iso hω
  -- the open `U' = V.ι(W)`
  let U' : U.Opens := V.ι ''ᵁ W
  have hxU' : x ∈ U' := ⟨⟨x, hxV⟩, hxW, rfl⟩
  obtain ⟨i, _, hfac⟩ := exists_isOpenImmersion_comp_ι_eq V U'.ι (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, -, rfl⟩
    exact w.2)
  have hiW : Set.range i ⊆ (W : Set V) := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, hw, hwz⟩ := z.2
    have h₁ : V.ι (i z) = U'.ι z := by
      rw [← Scheme.Hom.comp_apply, hfac]
    obtain rfl : w = i z := V.ι.isOpenEmbedding.injective (hwz.trans h₁.symm)
    exact hw
  obtain ⟨eA⟩ := hW i hiW
  obtain ⟨eS⟩ := nonempty_restrict_standard_iso_single i _ (-1) ⟨eA⟩
  exact ⟨U', hxU', ⟨Scheme.derivedPullbackCongrObj hfac.symm K ≪≫
    (Scheme.derivedPullbackCompObj i V.ι K).symm ≪≫
    (@Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback _ _
      i.toLRSHom.toShHom (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
      _).mapIso α ≪≫
    ((Scheme.Modules.derivedRestrictIsoDerivedPullback i).app _).symm ≪≫ eS⟩⟩

/-- **The cohomology sheaves of a relative dualizing complex of a syntomic curve over a field,
locally.** In the situation of `exists_derivedPullback_iso_single`, every point `x` of `U` has an
open neighbourhood `U'` on which each cohomology sheaf `H^m(K)` (at the standard model) is the
cohomology sheaf `H^m(𝒪_{U'}[1])`. -/
theorem exists_restrict_homology_iso {U : Scheme.{u}} (f : U ⟶ Spec (CommRingCat.of k))
    (hf : SyntomicOfRelativeDimension 1 f) (D : f.DiagonalOpen)
    (K : @DerivedCategory (_root_.StrictlyPerfect.OXMod.{u, u} U.toRingedSpace) _ _
      (HasDerivedCategory.standard _))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K)
    (hK : letI := HasDerivedCategory.standard (_root_.StrictlyPerfect.OXMod.{u, u}
        ((Spec (CommRingCat.of k)).toRingedSpace.inverseImage f.base))
      letI := fun W : Opens
          ((Spec (CommRingCat.of k)).toRingedSpace.inverseImage f.base).carrier =>
        HasDerivedCategory.standard (_root_.StrictlyPerfect.OXMod.{u, u}
          (((Spec (CommRingCat.of k)).toRingedSpace.inverseImage f.base).restrict
            W.isOpenEmbedding))
      haveI := flat_of_syntomicOfRelativeDimension hf
      haveI := locallyOfFinitePresentation_of_syntomicOfRelativeDimension hf
      Scheme.Hom.IsRelativeDualizingComplex.{u + 1, u} f
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage (Spec (CommRingCat.of k)).toRingedSpace f.base)) D K ξ)
    (x : U) :
    ∃ U' : U.Opens, x ∈ U' ∧
      letI := HasDerivedCategory.standard U.Modules
      letI := HasDerivedCategory.standard U'.toScheme.Modules
      ∀ m : ℤ, Nonempty ((Scheme.Modules.restrictFunctor U'.ι).obj
          ((DerivedCategory.homologyFunctor U.Modules m).obj K) ≅
        (DerivedCategory.homologyFunctor U'.toScheme.Modules m).obj
          ((DerivedCategory.singleFunctor U'.toScheme.Modules (-1)).obj
            (SheafOfModules.unit U'.toScheme.ringCatSheaf))) := by
  obtain ⟨U', hx, ⟨e⟩⟩ := exists_derivedPullback_iso_single f hf D K ξ hK x
  refine ⟨U', hx, fun m => ?_⟩
  let := HasDerivedCategory.standard U.Modules
  let := HasDerivedCategory.standard U'.toScheme.Modules
  exact ⟨((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (Scheme.Modules.restrictFunctor U'.ι) m).app K).symm ≪≫
    (DerivedCategory.homologyFunctor U'.toScheme.Modules m).mapIso
      ((Scheme.Modules.derivedRestrictIsoDerivedPullback U'.ι).app K ≪≫ e)⟩

/-- **A relative dualizing complex of a syntomic curve over a field has cohomology only in degree
`-1`.** In the situation of `exists_derivedPullback_iso_single`, `H^m(K) = 0` for `m ≠ -1`. -/
theorem isZero_homology_of_ne {U : Scheme.{u}} (f : U ⟶ Spec (CommRingCat.of k))
    (hf : SyntomicOfRelativeDimension 1 f) (D : f.DiagonalOpen)
    (K : @DerivedCategory (_root_.StrictlyPerfect.OXMod.{u, u} U.toRingedSpace) _ _
      (HasDerivedCategory.standard _))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K)
    (hK : letI := HasDerivedCategory.standard (_root_.StrictlyPerfect.OXMod.{u, u}
        ((Spec (CommRingCat.of k)).toRingedSpace.inverseImage f.base))
      letI := fun W : Opens
          ((Spec (CommRingCat.of k)).toRingedSpace.inverseImage f.base).carrier =>
        HasDerivedCategory.standard (_root_.StrictlyPerfect.OXMod.{u, u}
          (((Spec (CommRingCat.of k)).toRingedSpace.inverseImage f.base).restrict
            W.isOpenEmbedding))
      haveI := flat_of_syntomicOfRelativeDimension hf
      haveI := locallyOfFinitePresentation_of_syntomicOfRelativeDimension hf
      Scheme.Hom.IsRelativeDualizingComplex.{u + 1, u} f
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage (Spec (CommRingCat.of k)).toRingedSpace f.base)) D K ξ)
    (m : ℤ) (hm : m ≠ -1) :
    IsZero ((@DerivedCategory.homologyFunctor U.Modules _ _ (HasDerivedCategory.standard _) m).obj
      K) := by
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun x => ?_
  obtain ⟨U', hx, h⟩ := exists_restrict_homology_iso f hf D K ξ hK x
  let := HasDerivedCategory.standard U'.toScheme.Modules
  have hz : IsZero ((DerivedCategory.homologyFunctor U'.toScheme.Modules m).obj
      ((DerivedCategory.singleFunctor U'.toScheme.Modules (-1)).obj
        (SheafOfModules.unit U'.toScheme.ringCatSheaf))) := by
    let O := SheafOfModules.unit U'.toScheme.ringCatSheaf
    exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) (-1) O m hm).of_iso
      ((DerivedCategory.homologyFunctor U'.toScheme.Modules m).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ U'.toScheme.Modules (-1)).app O) ≪≫
        (DerivedCategory.homologyFunctorFactors U'.toScheme.Modules m).app _)
  exact Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isZero_stalk_of_isZero_restrict U' _ x hx
    (hz.of_iso (h m).some)

/-- **The cohomology sheaf in degree `-1` of a relative dualizing complex of a syntomic curve over
a field is finite locally free of rank one.** In the situation of
`exists_derivedPullback_iso_single`, `H^{-1}(K)` is finite locally free of rank one. -/
theorem isFiniteLocallyFreeOfRank_homology_neg_one {U : Scheme.{u}}
    (f : U ⟶ Spec (CommRingCat.of k))
    (hf : SyntomicOfRelativeDimension 1 f) (D : f.DiagonalOpen)
    (K : @DerivedCategory (_root_.StrictlyPerfect.OXMod.{u, u} U.toRingedSpace) _ _
      (HasDerivedCategory.standard _))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K)
    (hK : letI := HasDerivedCategory.standard (_root_.StrictlyPerfect.OXMod.{u, u}
        ((Spec (CommRingCat.of k)).toRingedSpace.inverseImage f.base))
      letI := fun W : Opens
          ((Spec (CommRingCat.of k)).toRingedSpace.inverseImage f.base).carrier =>
        HasDerivedCategory.standard (_root_.StrictlyPerfect.OXMod.{u, u}
          (((Spec (CommRingCat.of k)).toRingedSpace.inverseImage f.base).restrict
            W.isOpenEmbedding))
      haveI := flat_of_syntomicOfRelativeDimension hf
      haveI := locallyOfFinitePresentation_of_syntomicOfRelativeDimension hf
      Scheme.Hom.IsRelativeDualizingComplex.{u + 1, u} f
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage (Spec (CommRingCat.of k)).toRingedSpace f.base)) D K ξ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((@DerivedCategory.homologyFunctor U.Modules _ _ (HasDerivedCategory.standard _) (-1)).obj
        K) 1 := by
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_forall_restrictIso _ 1 fun x => ?_
  obtain ⟨U', hx, h⟩ := exists_restrict_homology_iso f hf D K ξ hK x
  let := HasDerivedCategory.standard U'.toScheme.Modules
  exact ⟨U', hx, ULift.{u} (Fin 1), ⟨Equiv.ulift⟩, ⟨(h (-1)).some ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso U'.toScheme.Modules (-1)).app _ ≪≫
    (Stacks.SheafOfModules.Invertible.freeUniqueIso _).symm⟩⟩

end Stacks.Duality.SyntomicOverField

end
