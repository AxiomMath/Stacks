module

public import StacksFrontier.AlgebraicGeometry.Intersection.ProjectionFormulaFlat.AffineSupportTor
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FlatPullbackTorSheaf
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafIso
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafMultiplicity
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleRestriction
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticSupport.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaAffine.IsIso0FZE
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.RingTheory.LocalRing.TensorNontrivial
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# The comparison of Tag 0B11 at the points of top dimension

Let `f : X ⟶ Y` be a flat proper morphism of locally Noetherian schemes, `ℱ` a coherent
`𝒪_X`-module and `𝒢` a coherent `𝒪_Y`-module. At a point `y ∈ Y` over which the support of `ℱ`
has finite fibre, the stalks of

`f_* Torᵢ^{𝒪_X}(ℱ, f^*𝒢)`  and  `Torᵢ^{𝒪_Y}(f_*ℱ, 𝒢)`

have the same length. This is the comparison (43.22.1.1), Tag 0B11, in the proof of Stacks Tag
0B10, and its consequence for cycles.

## Main results

All names are in the namespace `Stacks.Intersection.ProjectionFormula`.

* `supp_inter_subset_supp_torSheaf_zero` — the support of `Tor₀^{𝒪_X}(ℱ, 𝒢)` contains
  `Supp ℱ ∩ Supp 𝒢` for coherent `ℱ` and `𝒢`.
* `sheafMultiplicity_pushforward_torSheaf_eq` — the equality of the multiplicities at a point over
  which `Supp ℱ` has finite fibre.
* `schemeDeltaDimension_reducedSupport_torSheaf_pushforward_le_of_bound` — the dimension bound for
  the supports of `Torᵢ^{𝒪_Y}(f_*ℱ, 𝒢)` that the intersection product of `f_*ℱ` and `𝒢` needs.
* `cycleAssociatedToCoherentSheaf_pushforward_torSheaf_eq` —
  `[f_* Torᵢ^{𝒪_X}(ℱ, f^*𝒢)]_n = [Torᵢ^{𝒪_Y}(f_*ℱ, 𝒢)]_n` for nonsingular varieties.

## Implementation notes

The source works at the generic point `ξ` of a component of `f(V) ∩ W`, over which `V` is
finite, and reads off lengths of stalks at `ξ`. Here the fibre of `Supp ℱ` over `y` is finite,
so by Zariski's main theorem (Stacks 02UP) the scheme-theoretic support `Z` of `ℱ` (Stacks 02OM)
is finite over an open neighbourhood `V` of `y`. Over `V` the restriction of `ℱ` is `j_*` of a
quasi-coherent module along the closed immersion `j` of `Z ∩ f⁻¹V` into `f⁻¹V`, and `j ≫ f` is
finite, so the comparison of
`Stacks.Intersection.ProjectionFormula.pushforwardTorSheafIsoOfIsAffineHom` applies there. The
`Tor` sheaves, the direct images and the pullbacks are compatible with restriction to `V`, and the
multiplicity at `y` does not see the restriction.

A point `y` of delta-dimension `n` which carries a nonzero coefficient on either side lies in the
support of `𝒢`. Then the fibre of `Supp ℱ` over `y` lies in the support of
`Tor₀^{𝒪_X}(ℱ, f^*𝒢)`, which has delta-dimension at most `n`, so it is finite. This replaces the
source's case distinction on the generic fibre dimension of `V → f(V)`.

## References

* [Stacks Project, Tag 0B10](https://stacks.math.columbia.edu/tag/0B10)
* [Stacks Project, Tag 0B11](https://stacks.math.columbia.edu/tag/0B11)
* [Stacks Project, Tag 02UP](https://stacks.math.columbia.edu/tag/02UP)
* [Stacks Project, Tag 02OM](https://stacks.math.columbia.edu/tag/02OM)
* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u

namespace Stacks.Intersection.ProjectionFormula

open Stacks.Chow AlgebraicGeometry.TorFormula

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### The support of `Tor₀` -/

/-- **The support of `Tor₀^{𝒪_X}(ℱ, 𝒢)` contains `Supp ℱ ∩ Supp 𝒢`** for coherent `ℱ` and `𝒢`:
at a point of both supports the stalk of `Tor₀` is the tensor product of the two stalks over the
local ring (Stacks 0AZT), which is nonzero by Nakayama's lemma. -/
theorem supp_inter_subset_supp_torSheaf_zero {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F G : X.Modules) [F.IsCoherent] [G.IsCoherent] :
    SheafOfModules.supp F ∩ SheafOfModules.supp G ⊆ SheafOfModules.supp (torSheaf X F G 0) := by
  rintro x ⟨hxF, hxG⟩
  have : F.IsFiniteType := isFiniteType_of_isCoherent F
  have : G.IsFiniteType := isFiniteType_of_isCoherent G
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  have hFfin : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    _root_.SheafOfModules.finite_stalk X.sheaf F x
  have hGfin : Module.Finite (X.presheaf.stalk x) (G.presheaf.stalk x) :=
    _root_.SheafOfModules.finite_stalk X.sheaf G x
  have hFnt : Nontrivial (F.presheaf.stalk x) :=
    (SheafOfModules.mem_supp_iff_nontrivial_stalk F x).mp hxF
  have hGnt : Nontrivial (G.presheaf.stalk x) :=
    (SheafOfModules.mem_supp_iff_nontrivial_stalk G x).mp hxG
  have hnt : Nontrivial (F.presheaf.stalk x ⊗[X.presheaf.stalk x] G.presheaf.stalk x) :=
    Stacks.LocalRing.nontrivial_tensorProduct _ _
  have e : ((Tor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj (stalkModuleCat X F x)).obj
      (stalkModuleCat X G x) ≅ stalkModuleCat X F x ⊗ stalkModuleCat X G x :=
    Functor.leftDerivedZeroIsoSelf _ |>.app _
  have hpos : 0 < Module.length (X.presheaf.stalk x)
      (((Tor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj (stalkModuleCat X F x)).obj
        (stalkModuleCat X G x)) := by
    rw [e.toLinearEquiv.length_eq]
    exact Module.length_pos (R := X.presheaf.stalk x)
      (M := F.presheaf.stalk x ⊗[X.presheaf.stalk x] G.presheaf.stalk x)
  rw [← length_stalk_torSheaf_eq_length_tor_stalk X F G 0 x] at hpos
  have h := Module.length_pos_iff.mp hpos
  exact (SheafOfModules.mem_supp_iff_nontrivial_stalk _ x).mpr h

/-! ### The comparison of multiplicities -/

/-- **Stacks 0B11 at a point.** Let `f : X ⟶ Y` be a flat proper morphism of locally Noetherian
schemes, `ℱ` a coherent `𝒪_X`-module and `𝒢` a coherent `𝒪_Y`-module, and let `y ∈ Y` be a point
over which the support of `ℱ` has finite fibre. Then `f_* Torᵢ^{𝒪_X}(ℱ, f^*𝒢)` and
`Torᵢ^{𝒪_Y}(f_*ℱ, 𝒢)` have the same multiplicity at `y`. -/
theorem sheafMultiplicity_pushforward_torSheaf_eq {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] [IsProper f] (F : X.Modules) [F.IsCoherent]
    (G : Y.Modules) [G.IsCoherent] (y : Y)
    (hfin : {x : X | f x = y ∧ x ∈ SheafOfModules.supp F}.Finite) (i : ℕ) :
    sheafMultiplicity ((Scheme.Modules.pushforward f).obj
        (torSheaf X F ((Scheme.Modules.pullback f).obj G) i)) y =
      sheafMultiplicity (torSheaf Y ((Scheme.Modules.pushforward f).obj F) G i) y := by
  obtain ⟨F'', hF'', ⟨e⟩⟩ := exists_isCoherent_pushforward_iso_subschemeι_annihilatorIdeal F
  set ι := (annihilatorIdeal F).subschemeι with hι
  have hrange : Set.range ι.base = SheafOfModules.supp F := by
    rw [hι, Scheme.IdealSheafData.range_subschemeι, supp_eq_support_annihilatorIdeal F]
  -- the fibre of the scheme-theoretic support over `y` is finite
  have hfin' : ((ι ≫ f) ⁻¹' {y}).Finite := by
    refine Set.Finite.of_finite_image ?_ ι.isClosedEmbedding.injective.injOn
    refine hfin.subset ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨by simpa using hz, hrange ▸ Set.mem_range_self z⟩
  obtain ⟨V, hyV, hV⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton
    (ι ≫ f) y hfin'
  -- the restricted situation over `V`
  set U : X.Opens := f ⁻¹ᵁ V with hU
  set f' : U.toScheme ⟶ V.toScheme := f ∣_ V with hf'
  set j : (ι ⁻¹ᵁ U).toScheme ⟶ U.toScheme := ι ∣_ U with hj
  have hjf : j ≫ f' = (ι ≫ f) ∣_ V := (morphismRestrict_comp ι f V).symm
  have : IsAffineHom (j ≫ f') := by rw [hjf]; exact hV.toIsAffineHom
  have : IsLocallyNoetherian (annihilatorIdeal F).subscheme :=
    isLocallyNoetherian_of_isClosedImmersion ι
  set F₃ := (Scheme.Modules.pullback (ι ⁻¹ᵁ U).ι).obj F'' with hF₃
  have : F''.IsCoherent := hF''
  have hF₃c : F₃.IsCoherent := isCoherent_pullback _ F''
  have hF₃q : F₃.IsQuasicoherent := isQuasicoherent_of_isCoherent F₃
  set G' := (Scheme.Modules.pullback V.ι).obj G with hG'
  have hG'c : G'.IsCoherent := isCoherent_pullback _ G
  have hG'q : G'.IsQuasicoherent := isQuasicoherent_of_isCoherent G'
  -- the restriction of `ℱ` is pushed forward from the scheme-theoretic support
  let e₁ : (Scheme.Modules.pullback U.ι).obj F ≅ (Scheme.Modules.pushforward j).obj F₃ :=
    (Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫
      Stacks.ProjectionFormula.pushforwardBaseChangeIso ι U F''
  let e₂ : (Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pullback f).obj G) ≅
      (Scheme.Modules.pullback f').obj G' :=
    (Scheme.Modules.pullbackComp U.ι f).app G ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι f V).symm).app G ≪≫
      ((Scheme.Modules.pullbackComp f' V.ι).app G).symm
  let e₂' : torSheaf U.toScheme ((Scheme.Modules.pushforward j).obj F₃)
        ((Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pullback f).obj G)) i ≅
      torSheaf U.toScheme ((Scheme.Modules.pushforward j).obj F₃)
        ((Scheme.Modules.pullback f').obj G') i :=
    (DerivedCategory.homologyFunctor U.toScheme.Modules (-(i : ℤ))).mapIso
      (((derivedTensor U.toScheme).obj ((DerivedCategory.singleFunctor U.toScheme.Modules 0).obj
        ((Scheme.Modules.pushforward j).obj F₃))).mapIso
        ((DerivedCategory.singleFunctor U.toScheme.Modules 0).mapIso e₂))
  -- the two restricted sheaves are isomorphic
  let eL : (Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pushforward f).obj
        (torSheaf X F ((Scheme.Modules.pullback f).obj G) i)) ≅
      torSheaf V.toScheme ((Scheme.Modules.pushforward f').obj
        ((Scheme.Modules.pushforward j).obj F₃)) G' i :=
    Stacks.ProjectionFormula.pushforwardBaseChangeIso f V _ ≪≫
      (Scheme.Modules.pushforward f').mapIso
        (pullbackTorSheafIso U.ι F ((Scheme.Modules.pullback f).obj G) i ≪≫
          torSheafMapIso e₁ _ i ≪≫ e₂') ≪≫
      pushforwardTorSheafIsoOfIsAffineHom f' j F₃ hF₃q G' hG'q i
  let eR : (Scheme.Modules.pullback V.ι).obj
        (torSheaf Y ((Scheme.Modules.pushforward f).obj F) G i) ≅
      torSheaf V.toScheme ((Scheme.Modules.pushforward f').obj
        ((Scheme.Modules.pushforward j).obj F₃)) G' i :=
    pullbackTorSheafIso V.ι ((Scheme.Modules.pushforward f).obj F) G i ≪≫
      torSheafMapIso (Stacks.ProjectionFormula.pushforwardBaseChangeIso f V F ≪≫
        (Scheme.Modules.pushforward f').mapIso e₁) G' i
  have h₁ := sheafMultiplicity_pullback_of_isOpenImmersion V.ι
    ((Scheme.Modules.pushforward f).obj (torSheaf X F ((Scheme.Modules.pullback f).obj G) i))
    ⟨y, hyV⟩
  have h₂ := sheafMultiplicity_pullback_of_isOpenImmersion V.ι
    (torSheaf Y ((Scheme.Modules.pushforward f).obj F) G i) ⟨y, hyV⟩
  have hy : V.ι ⟨y, hyV⟩ = y := rfl
  rw [hy] at h₁ h₂
  rw [← h₁, ← h₂]
  exact sheafMultiplicity_eq_of_iso (eL ≪≫ eR.symm) _

/-! ### Cycles on nonsingular varieties -/

/-- A point lies in the support of `f^*𝒢` iff its image lies in the support of `𝒢`. -/
private theorem mem_supp_pullback_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules)
    [G.IsFiniteType] (x : X) :
    x ∈ SheafOfModules.supp ((Scheme.Modules.pullback f).obj G) ↔ f x ∈ SheafOfModules.supp G := by
  rw [Stacks.Modules.supp_pullback]
  rfl

/-- The fibre of `Supp ℱ` over a point `y ∈ Supp 𝒢` of delta-dimension `n` is finite, when the
support of `Tor₀^{𝒪_X}(ℱ, f^*𝒢)` has delta-dimension at most `n`: that fibre lies in the support
of `Tor₀`, whose points over `y` are generic points of its components. -/
theorem finite_supportFibre_of_torSheaf_zero (K : Type u) [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY]
    (hX : AlgebraicGeometry.IsRegular X) (f : X ⟶ Y) [IsProper f] (hbase : f ≫ sY = sX)
    (F : X.Modules) (hF : _root_.SheafOfModules.IsCoherent F) (G : Y.Modules)
    (hG : _root_.SheafOfModules.IsCoherent G) (n : ℤ)
    (hT0 : haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
      haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
      haveI := isCoherent_torSheaf_of_isRegular X hX F ((Scheme.Modules.pullback f).obj G) hF
        (isCoherent_pullback f G) 0
      schemeDeltaDimension (fieldChowSituation K)
        ((reducedSupport (torSheaf X F ((Scheme.Modules.pullback f).obj G) 0)).subschemeι ≫ sX)
          ≤ (n : EInt))
    (y : Y) (hyG : y ∈ SheafOfModules.supp G)
    (hδ : relativeDimension (fieldChowSituation K).dimensionFunction sY y = n) :
    {x : X | f x = y ∧ x ∈ SheafOfModules.supp F}.Finite := by
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have := hF
  have := hG
  have : G.IsFiniteType := isFiniteType_of_isCoherent G
  have : ((Scheme.Modules.pullback f).obj G).IsCoherent := isCoherent_pullback f G
  have := isCoherent_torSheaf_of_isRegular X hX F ((Scheme.Modules.pullback f).obj G) hF
    (isCoherent_pullback f G) 0
  refine (finite_supportFibre (fieldChowSituation K) sX sY f hbase _ hT0 y hδ).subset ?_
  rintro x ⟨hxy, hxF⟩
  exact ⟨hxy, supp_inter_subset_supp_torSheaf_zero F _
    ⟨hxF, (mem_supp_pullback_iff f G x).2 (hxy ▸ hyG)⟩⟩

/-- **The dimension bound for `Torᵢ^{𝒪_Y}(f_*ℱ, 𝒢)`.** Let `f : X ⟶ Y` be a proper morphism of
nonsingular varieties over a field, `ℱ` and `𝒢` coherent, and suppose the supports of the sheaves
`Torᵢ^{𝒪_X}(ℱ, f^*𝒢)` have delta-dimension at most `n`. Then so do the supports of the sheaves
`Torᵢ^{𝒪_Y}(f_*ℱ, 𝒢)`: such a support lies in `Supp(f_*ℱ) ∩ Supp(𝒢)`, which is the image of
`Supp(ℱ) ∩ f⁻¹Supp(𝒢) = Supp Tor₀^{𝒪_X}(ℱ, f^*𝒢)`, and delta-dimension does not grow along `f`. -/
theorem schemeDeltaDimension_reducedSupport_torSheaf_pushforward_le_of_bound (K : Type u)
    [Field K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
    [IsVariety K sX] [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X)
    (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y) [IsProper f] (hbase : f ≫ sY = sX)
    (F : X.Modules) (hF : _root_.SheafOfModules.IsCoherent F) (G : Y.Modules)
    (hG : _root_.SheafOfModules.IsCoherent G) (n : ℤ)
    (hFn : ∀ i : ℕ,
      haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
      haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
      haveI := isCoherent_torSheaf_of_isRegular X hX F ((Scheme.Modules.pullback f).obj G) hF
        (isCoherent_pullback f G) i
      schemeDeltaDimension (fieldChowSituation K)
        ((reducedSupport (torSheaf X F ((Scheme.Modules.pullback f).obj G) i)).subschemeι ≫ sX)
          ≤ (n : EInt))
    (i : ℕ) :
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI := isCoherent_torSheaf_of_isRegular Y hY ((Scheme.Modules.pushforward f).obj F) G
      (@AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward _ _ f _ _ F hF) hG i
    schemeDeltaDimension (fieldChowSituation K)
      ((reducedSupport (torSheaf Y ((Scheme.Modules.pushforward f).obj F) G i)).subschemeι ≫ sY)
        ≤ (n : EInt) := by
  have hlft : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have := hF
  have := hG
  have : F.IsFiniteType := isFiniteType_of_isCoherent F
  have : G.IsFiniteType := isFiniteType_of_isCoherent G
  have hpF := AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
  have hcG : ((Scheme.Modules.pullback f).obj G).IsCoherent := isCoherent_pullback f G
  have := isCoherent_torSheaf_of_isRegular X hX F ((Scheme.Modules.pullback f).obj G) hF hcG 0
  have := isCoherent_torSheaf_of_isRegular Y hY ((Scheme.Modules.pushforward f).obj F) G hpF hG i
  refine schemeDeltaDimension_reducedSupport_le (fieldChowSituation K) sY _ fun y hy => ?_
  obtain ⟨hyF, hyG⟩ := supp_torSheaf_subset_inter Y _ _ i hy
  obtain ⟨x, hxF, rfl⟩ :=
    supp_pushforward_subset_image f F (SheafOfModules.isClosed_supp F) hyF
  have hx0 := supp_inter_subset_supp_torSheaf_zero F _ ⟨hxF, (mem_supp_pullback_iff f G x).2 hyG⟩
  have hxn := relativeDimension_le_of_mem_supp (fieldChowSituation K) sX _ (hFn 0) hx0
  have hstep :=
    relativeDimension_comp_eq_add_trdeg (fieldChowSituation K).dimensionFunction sY f x
  rw [hbase] at hstep
  omega

/-- **Stacks 0B11 for cycles.** Let `f : X ⟶ Y` be a flat proper morphism of nonsingular varieties
over a field, `ℱ` and `𝒢` coherent, and suppose the supports of the sheaves
`Torᵢ^{𝒪_X}(ℱ, f^*𝒢)` have delta-dimension at most `n`. Then

`[f_* Torᵢ^{𝒪_X}(ℱ, f^*𝒢)]_n = [Torᵢ^{𝒪_Y}(f_*ℱ, 𝒢)]_n`.

At a point `y` of delta-dimension `n` outside `Supp 𝒢` both stalks vanish; at one in `Supp 𝒢`
the fibre of `Supp ℱ` is finite and the multiplicities agree by
`sheafMultiplicity_pushforward_torSheaf_eq`. -/
theorem cycleAssociatedToCoherentSheaf_pushforward_torSheaf_eq (K : Type u) [Field K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX]
    [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X) (hY : AlgebraicGeometry.IsRegular Y)
    (f : X ⟶ Y) [Flat f] [IsProper f] (hbase : f ≫ sY = sX) (F : X.Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) (G : Y.Modules)
    (hG : _root_.SheafOfModules.IsCoherent G) (n : ℤ)
    (hFn : ∀ i : ℕ,
      haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
      haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
      haveI := isCoherent_torSheaf_of_isRegular X hX F ((Scheme.Modules.pullback f).obj G) hF
        (isCoherent_pullback f G) i
      schemeDeltaDimension (fieldChowSituation K)
        ((reducedSupport (torSheaf X F ((Scheme.Modules.pullback f).obj G) i)).subschemeι ≫ sX)
          ≤ (n : EInt))
    (i : ℕ) :
    haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI := isCoherent_torSheaf_of_isRegular X hX F ((Scheme.Modules.pullback f).obj G) hF
      (isCoherent_pullback f G) i
    haveI := AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f
      (torSheaf X F ((Scheme.Modules.pullback f).obj G) i)
    haveI := isCoherent_torSheaf_of_isRegular Y hY ((Scheme.Modules.pushforward f).obj F) G
      (@AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward _ _ f _ _ F hF) hG i
    cycleAssociatedToCoherentSheaf (fieldChowSituation K) sY
        ((Scheme.Modules.pushforward f).obj (torSheaf X F ((Scheme.Modules.pullback f).obj G) i))
        n (schemeDeltaDimension_reducedSupport_pushforward_le (fieldChowSituation K) sX sY f
          hbase _ (hFn i)) =
      cycleAssociatedToCoherentSheaf (fieldChowSituation K) sY
        (torSheaf Y ((Scheme.Modules.pushforward f).obj F) G i) n
        (schemeDeltaDimension_reducedSupport_torSheaf_pushforward_le_of_bound K sX sY hX hY f
          hbase F hF G hG n hFn i) := by
  have hlft : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have := hF
  have := hG
  have : G.IsFiniteType := isFiniteType_of_isCoherent G
  have hcG : ((Scheme.Modules.pullback f).obj G).IsCoherent := isCoherent_pullback f G
  have hT := isCoherent_torSheaf_of_isRegular X hX F ((Scheme.Modules.pullback f).obj G) hF hcG i
  have hT0 := isCoherent_torSheaf_of_isRegular X hX F ((Scheme.Modules.pullback f).obj G) hF hcG 0
  have hpT := AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f
    (torSheaf X F ((Scheme.Modules.pullback f).obj G) i)
  have hpF := AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
  have := isCoherent_torSheaf_of_isRegular Y hY ((Scheme.Modules.pushforward f).obj F) G hpF hG i
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y => ?_)
  by_cases hδ : relativeDimension (fieldChowSituation K).dimensionFunction sY y = n
  · simp only [cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq _ _ _ _ _ hδ]
    by_cases hyG : y ∈ SheafOfModules.supp G
    · exact sheafMultiplicity_pushforward_torSheaf_eq f F G y
        (finite_supportFibre_of_torSheaf_zero K sX sY hX f hbase F hF G hG n (hFn 0) y hyG hδ) i
    · have h₁ : y ∉ SheafOfModules.supp ((Scheme.Modules.pushforward f).obj
          (torSheaf X F ((Scheme.Modules.pullback f).obj G) i)) := by
        intro hy
        have : (torSheaf X F ((Scheme.Modules.pullback f).obj G) i).IsFiniteType :=
          isFiniteType_of_isCoherent _
        obtain ⟨x, hx, rfl⟩ := supp_pushforward_subset_image f _
          (SheafOfModules.isClosed_supp _) hy
        have hxG := (supp_torSheaf_subset_inter X _ _ i hx).2
        exact hyG ((mem_supp_pullback_iff f G x).1 hxG)
      have h₂ : y ∉ SheafOfModules.supp (torSheaf Y ((Scheme.Modules.pushforward f).obj F) G i) :=
        fun hy => hyG (supp_torSheaf_subset_inter Y _ _ i hy).2
      rw [sheafMultiplicity_eq_zero_of_notMem_supp _ h₁,
        sheafMultiplicity_eq_zero_of_notMem_supp _ h₂]
  · simp only [cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne _ _ _ _ _ hδ]

end Stacks.Intersection.ProjectionFormula

end
