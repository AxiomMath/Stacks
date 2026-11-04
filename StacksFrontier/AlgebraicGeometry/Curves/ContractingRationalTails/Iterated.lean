module

public import StacksFrontier.AlgebraicGeometry.Curves.CanonicalContraction.SmoothAtAttaching
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.Contraction
public import StacksFrontier.AlgebraicGeometry.Curves.DirectImage.RationalTailCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusNormalizationBound
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.StableModel
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteTypeStructure.GroupoidColimit

/-!
# Successive contractions of rational tails

Let `k` be a field and let `X` be a proper one-dimensional scheme over `k` with at-worst-nodal
singularities and `H⁰(X, 𝒪_X) = k`. Contracting a rational tail `C ⊆ X` produces the
scheme-theoretic closure `X'` of `X ∖ C`, which again has all of these properties and the same
genus (Tag 0E3H). This file iterates that observation along a finite chain
`X = X₀ → X₁ → ⋯ → Xₙ` of contractions of rational tails, as recorded by
`AlgebraicGeometry.IsIteratedContractionOfRationalTails`: the target of such a chain is again a
proper one-dimensional nodal curve over `k` with `H⁰ = k`, of the same genus as `X`. This is the
first step of the proof of Tag 0E3L, which then applies Tag 0E3K to the end of the chain.

## Main results

* `AlgebraicGeometry.IsIteratedContractionOfRationalTails.isProper_target`,
  `topologicalKrullDim_target`, `isIso_globalSections_target`,
  `hasAtWorstNodalSingularities_target`, `genus_target`: the target of a chain of contractions
  of rational tails is proper, one-dimensional, with constant global functions, at worst nodal,
  and of the genus of the source.
* `AlgebraicGeometry.IsIteratedContractionOfRationalTails.isIso_unitToPushforwardObjUnit`,
  `isZero_rightDerived`: its composite `c` satisfies `𝒪_Y = c_*𝒪_X` and `Rⁱ c_*𝒪_X = 0`, `i > 0`.
* `AlgebraicGeometry.IsIteratedContractionOfRationalTails.exists_forall_not_isRationalTail`:
  rational tails can be contracted until none are left.
* `AlgebraicGeometry.ncard_irreducibleComponents_complementaryCurve_lt`: contracting a rational
  tail lowers the number of irreducible components.

## Implementation notes

Each step of a chain identifies the next curve with the closure `X'` of the complement of a
rational tail only up to an isomorphism `e : X' ≅ Y`, and the structure morphism of `Y` is part
of the data of the chain. The contraction `c ≫ e.inv` restricts to the identity on `X'`, so
`e.hom = complementaryCurveι C ≫ c`, and the base-compatibility `c ≫ f_Y = f_X` then gives
`e.hom ≫ f_Y = complementaryCurveι C ≫ f_X`: the structure morphism of `Y` is the one of `X'`
transported along `e`. The properties of `X'` from Tag 0E3H therefore pass to `Y`; nodality
passes along `e` because an isomorphism is étale
(`Stacks.Curves.smoothAt_or_isNode_of_etale_of_comm`).

## References

* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
* [Stacks Project, Tag 0E3L](https://stacks.math.columbia.edu/tag/0E3L)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsIteratedContractionOfRationalTails

variable {k : Type u} [Field k]

/-- **The structure morphism of the next curve in a chain is that of the closure of the
complement, transported along the identification.** The contraction `c ≫ e.inv` restricts to the
identity on `X'`, so `complementaryCurveι C ≫ c = e.hom`. -/
theorem iso_hom_comp_structureMorphism {X Y : Scheme.{u}}
    {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)} {c : X ⟶ Y} {C : X.IdealSheafData}
    (hC : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      IsRationalTail k X C)
    (e : complementaryCurve C ≅ Y)
    (hc : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      IsContractionOfRationalTail hC (c ≫ e.inv))
    (hbase : c ≫ fY = fX) :
    e.hom ≫ fY = complementaryCurveι C ≫ fX := by
  have h2 : complementaryCurveι C ≫ c = e.hom :=
    e.comp_inv_eq_id.mp (by rw [Category.assoc]; exact hc.1)
  rw [← h2, Category.assoc, hbase]

/-- Pushing modules forward along an isomorphism of schemes is an equivalence, with inverse the
push-forward along the inverse. -/
private alias isEquivalence_pushforward_hom :=
  AlgebraicGeometry.GroupoidScheme.pushforward_isEquivalence

/-- **An isomorphism of schemes is acyclic for the structure sheaf and preserves it**:
`𝒪_Y = e_*𝒪_X` and `Rⁱ e_*𝒪_X = 0` for `i > 0`, the push-forward being an equivalence. -/
private theorem isIso_unitToPushforwardObjUnit_and_isZero_rightDerived_of_iso {X Y : Scheme.{u}}
    (e : X ≅ Y) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom) ∧
      ∀ i : ℕ, 0 < i → Limits.IsZero (((Scheme.Modules.pushforward e.hom).rightDerived i).obj
        (SheafOfModules.unit X.ringCatSheaf)) := by
  refine ⟨isIso_unitToPushforwardObjUnit_of_forall_isIso_app _ fun W => ?_, fun i hi => ?_⟩
  · exact Functor.map_isIso (forget₂ CommRingCat RingCat) (e.hom.app W.unop)
  · have := isEquivalence_pushforward_hom e
    exact Functor.isZero_rightDerived_of_exact _ _ i hi

/-- The standing hypotheses of Tag 0E3H on a curve, together with its genus, pass along an
isomorphism `e : X' ≅ Y` to `fY = e.inv ≫ g`. -/
private theorem standing_of_iso {X' Y : Scheme.{u}} {g : X' ⟶ Spec (.of k)}
    {fY : Y ⟶ Spec (.of k)} (e : X' ≅ Y) (hfY : fY = e.inv ≫ g) [IsProper g]
    (hdim : topologicalKrullDim X' = 1) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop)]
    (hnodal : @Stacks.Curves.HasAtWorstNodalSingularities k _ X' ⟨g⟩) :
    IsProper fY ∧ topologicalKrullDim Y = 1 ∧
      IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fY.appTop) ∧
      @Stacks.Curves.HasAtWorstNodalSingularities k _ Y ⟨fY⟩ ∧ genus fY = genus g := by
  have hYproper : IsProper fY := by
    rw [hfY]
    infer_instance
  have hYdim : topologicalKrullDim Y = 1 := by
    rw [← hdim]
    exact IsHomeomorph.topologicalKrullDim_eq _ e.inv.homeomorph.isHomeomorph
  have hYglob : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fY.appTop) := by
    rw [hfY, Scheme.Hom.comp_appTop, ← Category.assoc]
    have : IsIso e.inv.appTop :=
      ⟨⟨e.hom.appTop, by rw [← Scheme.Hom.comp_appTop, e.hom_inv_id, Scheme.Hom.id_appTop],
        by rw [← Scheme.Hom.comp_appTop, e.inv_hom_id, Scheme.Hom.id_appTop]⟩⟩
    infer_instance
  have hYgenus : genus fY = genus g := by
    rw [hfY]
    exact genus_comp_iso_eq k g e.symm
  refine ⟨hYproper, hYdim, hYglob, fun y hy => ?_, hYgenus⟩
  have hyc : IsClosed ({e.inv.base y} : Set X') := by
    have h := e.inv.homeomorph.isClosedMap _ hy
    rwa [Set.image_singleton] at h
  exact Stacks.Curves.smoothAt_or_isNode_of_etale_of_comm k g fY hdim hYdim e.inv (𝟙 Y)
    (by rw [Category.id_comp, hfY]) y (hnodal _ hyc)

/-- The standing hypotheses of Tag 0E3H on a curve, together with its genus, pass along a chain of
contractions of rational tails, and the composite of the chain satisfies `𝒪_Y = c_*𝒪_X` and
`Rⁱ c_*𝒪_X = 0` for `i > 0`. -/
private theorem standing {X Y : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}
    {c : X ⟶ Y} (hseq : IsIteratedContractionOfRationalTails k fX fY c)
    (hproper : IsProper fX) (hdim : topologicalKrullDim X = 1)
    (hglobal : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop))
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X) :
    IsProper fY ∧ topologicalKrullDim Y = 1 ∧
      IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fY.appTop) ∧
      @Stacks.Curves.HasAtWorstNodalSingularities k _ Y ⟨fY⟩ ∧
      genus fY = genus fX ∧
      IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom) ∧
      ∀ i : ℕ, 0 < i → Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived i).obj
        (SheafOfModules.unit X.ringCatSheaf)) := by
  induction hseq with
  | identity X fX =>
    exact ⟨hproper, hdim, hglobal, hnodal, rfl,
      isIso_unitToPushforwardObjUnit_and_isZero_rightDerived_of_iso (Iso.refl X)⟩
  | @step X Y Z fX fY fZ c d C hC e hc hbase hd ih =>
    let : X.Over (Spec (.of k)) := ⟨fX⟩
    have : IsProper (X ↘ Spec (.of k)) := hproper
    have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop) := hglobal
    let g : complementaryCurve C ⟶ Spec (.of k) := complementaryCurveι C ≫ fX
    have hfY : fY = e.inv ≫ g := by
      show fY = e.inv ≫ (complementaryCurveι C ≫ fX)
      rw [← iso_hom_comp_structureMorphism hC e hc hbase, Iso.inv_hom_id_assoc]
    -- the properties of the closure of the complement (Tag 0E3H)
    have : IsProper g := Stacks.Curves.isProper_complementaryCurve k X C
    have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) :=
      Stacks.Curves.isIso_globalSections_complementaryCurve k X hdim hnodal C hC
    obtain ⟨hYproper, hYdim, hYglob, hYnodal, hYgenus⟩ := standing_of_iso e hfY
      (Stacks.Curves.topologicalKrullDim_complementaryCurve k X hdim C hC)
      (Stacks.Curves.nodal_complementaryCurve k X hdim hnodal C hC)
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih hYproper hYdim hYglob hYnodal
    let cont : X ⟶ complementaryCurve C := c ≫ e.inv
    have hcomp : c ≫ d = cont ≫ (e.hom ≫ d) := by
      simp only [cont, Category.assoc, Iso.inv_hom_id_assoc]
    have hcontO : IsIso (SheafOfModules.unitToPushforwardObjUnit cont.toRingCatSheafHom) :=
      isIso_unitToPushforwardObjUnit_of_isIso_ringCatSheafHom cont
        (Stacks.Curves.isIso_structureSheaf_to_pushforward k X hdim hnodal C hC hc)
    have he := isIso_unitToPushforwardObjUnit_and_isZero_rightDerived_of_iso e
    have hcontg : cont ≫ g = fX := by
      rw [Category.assoc, ← hfY, hbase]
    have : IsProper cont := by
      have : IsProper (cont ≫ g) := by rwa [hcontg]
      exact IsProper.of_comp cont g
    have : CompactSpace (complementaryCurve C) := QuasiCompact.compactSpace_of_compactSpace g
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace fY
    refine ⟨h1, h2, h3, h4,
      h5.trans (hYgenus.trans (Stacks.Curves.genus_complementaryCurve k X hdim hnodal C hC)), ?_,
      fun i hi => ?_⟩
    · rw [hcomp]
      exact Stacks.Curves.StableModel.isIso_unitToPushforwardObjUnit_comp _ _ hcontO
        (Stacks.Curves.StableModel.isIso_unitToPushforwardObjUnit_comp _ _ he.1 h6)
    · rw [hcomp]
      exact (h7 i hi).of_iso
        (Stacks.Curves.StableModel.rightDerivedCompUnitIso cont (e.hom ≫ d) hcontO
            (Stacks.Curves.rightAcyclic_pushforward_ambientStructureSheaf hdim hnodal hc) i ≪≫
          Stacks.Curves.StableModel.rightDerivedCompUnitIso e.hom d he.1 he.2 i)

/-! ### Contracting rational tails until none are left -/

/-- The closure of the complement of `C` is the image of `complementaryCurveι C`. -/
theorem _root_.AlgebraicGeometry.range_complementaryCurveι_base {X : Scheme.{u}}
    [IsNoetherian X] (C : X.IdealSheafData) :
    Set.range (complementaryCurveι C).base = closure (C.support : Set X)ᶜ := by
  show Set.range (complementaryCurveIdeal C).subschemeι.base = _
  rw [Scheme.IdealSheafData.range_subschemeι]
  show ((Scheme.Opens.ι C.support.compl).ker.support : Set X) = _
  rw [Scheme.Hom.support_ker, Scheme.Opens.range_ι]
  rfl

/-- A scheme locally of finite type and quasi-compact over a Noetherian scheme is Noetherian. -/
private theorem isNoetherian_of_locallyOfFiniteType {A B : Scheme.{u}} (f : A ⟶ B)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsNoetherian B] : IsNoetherian A := by
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace f
  exact ⟨⟩

/-- **An irreducible component of the closure of the complement is one of `X` other than `C`.**
Let `C` cut out a closed subset of a Noetherian scheme `X`, and let `X'` be the closure of `X ∖ C`.
Every irreducible component `W` of `X'` meets the dense open `X ∖ C`, so its generic point lies on
an irreducible component `D ≠ C` of `X`; `D` meets `X ∖ C`, so lies in `X'`, and its preimage is
irreducible and contains `W`, hence equals it. -/
theorem _root_.AlgebraicGeometry.image_mem_irreducibleComponents_complementaryCurve
    {X : Scheme.{u}} [IsNoetherian X] (C : X.IdealSheafData) {W : Set (complementaryCurve C)}
    (hW : W ∈ irreducibleComponents (complementaryCurve C)) :
    (complementaryCurveι C).base '' W ∈ irreducibleComponents X ∧
      (complementaryCurveι C).base '' W ≠ (C.support : Set X) := by
  let ι := complementaryCurveι C
  let U : Set X := (C.support : Set X)ᶜ
  have hUo : IsOpen U := C.support.isClosed.isOpen_compl
  have hrange : Set.range ι.base = closure U := range_complementaryCurveι_base C
  have : IsNoetherian (complementaryCurve C) := isNoetherian_of_locallyOfFiniteType ι
  have hind := ι.isClosedEmbedding.isInducing
  have hdense : Dense (ι.base ⁻¹' U) := by
    rw [dense_iff_closure_eq, hind.closure_eq_preimage_closure_image,
      Set.image_preimage_eq_of_subset (hrange ▸ subset_closure), ← hrange, Set.preimage_range]
  obtain ⟨w, hw⟩ := QuasiSober.sober hW.1 (isClosed_of_mem_irreducibleComponents W hW)
  obtain ⟨V, hVo, hVne, hVW⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent W hW
  obtain ⟨v, hvV, hvU⟩ := hdense.inter_open_nonempty V hVo hVne
  have hwU : ι.base w ∈ U := by
    by_contra hwU
    have hsub : W ⊆ ι.base ⁻¹' Uᶜ := by
      rw [← hw.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr hwU)
        (hUo.isClosed_compl.preimage ι.continuous)
    exact hsub (hVW hvV) hvU
  let D := irreducibleComponent (ι.base w)
  have hD : D ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents _
  have hwD : ι.base w ∈ D := mem_irreducibleComponent
  have hDcl : IsClosed D := isClosed_of_mem_irreducibleComponents D hD
  have hDr : D ⊆ Set.range ι.base := by
    rw [hrange]
    exact (subset_closure_inter_of_isPreirreducible_of_isOpen hD.1.2 hUo ⟨_, hwD, hwU⟩).trans
      (closure_mono Set.inter_subset_right)
  have hWD : ι.base '' W ⊆ D := by
    rw [← hw.def]
    refine (image_closure_subset_closure_image ι.continuous).trans ?_
    rw [Set.image_singleton]
    exact closure_minimal (Set.singleton_subset_iff.mpr hwD) hDcl
  obtain ⟨η, hη⟩ := QuasiSober.sober hD.1 hDcl
  obtain ⟨d, hd⟩ := hDr hη.mem
  have hpre : ι.base ⁻¹' D = closure {d} := by
    rw [hind.closure_eq_preimage_closure_image, Set.image_singleton, hd, hη.def]
  have hpreirr : IsIrreducible (ι.base ⁻¹' D) := hpre ▸ isIrreducible_singleton.closure
  have hWpre : W ⊆ ι.base ⁻¹' D := Set.image_subset_iff.mp hWD
  rw [Set.Subset.antisymm hWpre (hW.2 hpreirr hWpre), Set.image_preimage_eq_of_subset hDr]
  exact ⟨hD, fun h => hwU (h ▸ hwD)⟩

/-- **The closure of the complement of an irreducible component has fewer irreducible
components.** Let `C` cut out an irreducible component of a Noetherian scheme `X`, and let `X'` be
the closure of `X ∖ C`. By `AlgebraicGeometry.image_mem_irreducibleComponents_complementaryCurve`,
`W ↦ ι(W)` embeds the irreducible components of `X'` into those of `X` other than `C`. -/
theorem _root_.AlgebraicGeometry.ncard_irreducibleComponents_complementaryCurve_lt
    {X : Scheme.{u}} [IsNoetherian X]
    (C : X.IdealSheafData) (hC : (C.support : Set X) ∈ irreducibleComponents X) :
    (irreducibleComponents (complementaryCurve C)).ncard < (irreducibleComponents X).ncard := by
  have hfin : (irreducibleComponents X).Finite := finite_irreducibleComponents_of_isNoetherian
  calc (irreducibleComponents (complementaryCurve C)).ncard
      ≤ (irreducibleComponents X \ {(C.support : Set X)}).ncard :=
        Set.ncard_le_ncard_of_injOn (fun W => (complementaryCurveι C).base '' W)
          (fun _ hW => image_mem_irreducibleComponents_complementaryCurve C hW)
          (fun W _ W' _ h => (complementaryCurveι C).isClosedEmbedding.injective.image_injective h)
          hfin.sdiff
    _ < (irreducibleComponents X).ncard := Set.ncard_sdiff_singleton_lt_of_mem hC hfin

/-- **Rational tails can be contracted until none are left** (the procedure of Tag 0E3L): a
proper one-dimensional nodal curve over `k` with `H⁰ = k` admits a chain of contractions of
rational tails whose target has no rational tail. Each contraction lowers the number of
irreducible components (`AlgebraicGeometry.ncard_irreducibleComponents_complementaryCurve_lt`),
and the hypotheses of Tag 0E3H pass to the closure of the complement. -/
theorem exists_forall_not_isRationalTail (k : Type u) [Field k] {X : Scheme.{u}}
    (fX : X ⟶ Spec (.of k)) [IsProper fX] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop)]
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X) :
    ∃ (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of k)) (c : X ⟶ Y),
      IsIteratedContractionOfRationalTails k fX fY c ∧
        ∀ C : Y.IdealSheafData, ¬ @IsRationalTail k _ Y ⟨fY⟩ C := by
  suffices h : ∀ (n : ℕ) (X : Scheme.{u}) (fX : X ⟶ Spec (.of k)),
      (irreducibleComponents X).ncard = n → IsProper fX → topologicalKrullDim X = 1 →
      IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop) →
      @Stacks.Curves.HasAtWorstNodalSingularities k _ X ⟨fX⟩ →
      ∃ (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of k)) (c : X ⟶ Y),
        IsIteratedContractionOfRationalTails k fX fY c ∧
          ∀ C : Y.IdealSheafData, ¬ @IsRationalTail k _ Y ⟨fY⟩ C from
    h _ X fX rfl inferInstance hdim inferInstance hnodal
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X fX hn hproper hdim hglobal hnodal
  let : X.Over (Spec (.of k)) := ⟨fX⟩
  by_cases htail : ∃ C : X.IdealSheafData, IsRationalTail k X C
  · obtain ⟨C, hC⟩ := htail
    have : IsProper (X ↘ Spec (.of k)) := hproper
    have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop) := hglobal
    have : IsReduced X := Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities k X hnodal
    have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType fX
    let cont := Stacks.Curves.canonicalContraction k X hdim hnodal C hC
    have hc := Stacks.Curves.isContractionOfRationalTail_canonicalContraction k X hdim hnodal C hC
    let g : complementaryCurve C ⟶ Spec (.of k) := complementaryCurveι C ≫ fX
    have hbase : cont ≫ g = fX := by
      apply ext_of_isAffine
      rw [Scheme.Hom.comp_appTop, ← cancel_epi (Scheme.ΓSpecIso (.of k)).inv]
      exact Stacks.Curves.structureMap_appTop_comp_appTop hC hc
    have hlt := ncard_irreducibleComponents_complementaryCurve_lt C
      hC.support_mem_irreducibleComponents
    obtain ⟨Y, fY, d, hd, hY⟩ := ih _ (hn ▸ hlt) (complementaryCurve C) g rfl
      (Stacks.Curves.isProper_complementaryCurve k X C)
      (Stacks.Curves.topologicalKrullDim_complementaryCurve k X hdim C hC)
      (Stacks.Curves.isIso_globalSections_complementaryCurve k X hdim hnodal C hC)
      (Stacks.Curves.nodal_complementaryCurve k X hdim hnodal C hC)
    exact ⟨Y, fY, cont ≫ d, .step C hC (Iso.refl _) (by rwa [Iso.refl_inv, Category.comp_id])
      hbase hd, hY⟩
  · push Not at htail
    exact ⟨X, fX, 𝟙 X, .identity X fX, htail⟩

variable {X Y : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)} {c : X ⟶ Y}
  (hseq : IsIteratedContractionOfRationalTails k fX fY c) [IsProper fX]
  (hdim : topologicalKrullDim X = 1) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop)]
  (hnodal : letI : X.Over (Spec (.of k)) := ⟨fX⟩
    Stacks.Curves.HasAtWorstNodalSingularities k X)

include hseq hdim hnodal

/-- **Stacks 0E3H, iterated: the target of a chain of contractions of rational tails is proper
over `k`.** -/
theorem isProper_target : IsProper fY :=
  (standing hseq inferInstance hdim inferInstance hnodal).1

/-- **Stacks 0E3H, iterated: the target of a chain of contractions of rational tails has
dimension one.** -/
theorem topologicalKrullDim_target : topologicalKrullDim Y = 1 :=
  (standing hseq inferInstance hdim inferInstance hnodal).2.1

/-- **Stacks 0E3H, iterated: the target of a chain of contractions of rational tails has only
constant global functions.** -/
theorem isIso_globalSections_target : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fY.appTop) :=
  (standing hseq inferInstance hdim inferInstance hnodal).2.2.1

/-- **Stacks 0E3H, iterated: the target of a chain of contractions of rational tails has at
worst nodal singularities.** -/
theorem hasAtWorstNodalSingularities_target :
    letI : Y.Over (Spec (.of k)) := ⟨fY⟩
    Stacks.Curves.HasAtWorstNodalSingularities k Y :=
  (standing hseq inferInstance hdim inferInstance hnodal).2.2.2.1

/-- **Stacks 0E3H, iterated: the target of a chain of contractions of rational tails has the
genus of the source.** -/
theorem genus_target : genus fY = genus fX :=
  (standing hseq inferInstance hdim inferInstance hnodal).2.2.2.2.1

/-- **The composite of a chain of contractions of rational tails satisfies `𝒪_Y = c_*𝒪_X`.**
Each contraction does (Tag 0E3H), the identifications are isomorphisms, and the condition is
stable under composition (`Stacks.Curves.StableModel.isIso_unitToPushforwardObjUnit_comp`). -/
theorem isIso_unitToPushforwardObjUnit :
    IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom) :=
  (standing hseq inferInstance hdim inferInstance hnodal).2.2.2.2.2.1

/-- **The composite of a chain of contractions of rational tails satisfies `Rⁱ c_*𝒪_X = 0` for
`i > 0`.** Each contraction is acyclic for the structure sheaf (Tag 0E3H) and so are the
identifications, so Leray (`Stacks.Curves.StableModel.rightDerivedCompUnitIso`) reduces the
composite to its last factor. -/
theorem isZero_rightDerived (i : ℕ) (hi : 0 < i) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived i).obj
      (SheafOfModules.unit X.ringCatSheaf)) :=
  (standing hseq inferInstance hdim inferInstance hnodal).2.2.2.2.2.2 i hi

end AlgebraicGeometry.IsIteratedContractionOfRationalTails

end
