module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.WeaklyContractibleCovers
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Characterization
public import StacksCore.Tactic.StacksAttribute

/-!
# One-element coverings by weakly contractible objects

Every object of a chosen big pro-étale site admits a chosen covering family with a single
member whose source is a weakly contractible object of the site, and the source may be taken
affine when the underlying scheme of the object is quasi-compact.

The source is a disjoint union of affine objects with w-contractible rings of global sections,
one for each affine open of the underlying scheme.

## Main results

* `CategoryTheory.GrothendieckTopology.isWeaklyContractible_of_disjointCover` — in an arbitrary
  site, an object covered by pairwise disjoint subobjects which are weakly contractible is
  itself weakly contractible.
* `AlgebraicGeometry.ProEtale.exists_weaklyContractible_singleton_covering` — every object of a
  chosen big pro-étale site has a one-element chosen covering by a weakly contractible object.
* `AlgebraicGeometry.ProEtale.exists_affine_weaklyContractible_singleton_covering` — for a
  quasi-compact object the source of that covering may be taken affine.
* `AlgebraicGeometry.ProEtale.exists_weaklyContractible_coproduct_singleton_covering` and
  `AlgebraicGeometry.ProEtale.exists_affine_weaklyContractible_weaklyEtale_singleton_covering` —
  the same two coverings, with the disjoint union presentation of the source and weak étaleness
  of the covering morphism.

## Implementation notes

"Pairwise disjoint" is expressed in
`CategoryTheory.GrothendieckTopology.isWeaklyContractible_of_disjointCover` by two hypotheses:
each leg is a monomorphism, and any object mapping compatibly into two distinct members is
covered by the empty sieve.

## References

* [Stacks Project, Tag 0F4P](https://stacks.math.columbia.edu/tag/0F4P)
* [Stacks Project, Tag 098A](https://stacks.math.columbia.edu/tag/098A)
* [Stacks Project, Tag 098I](https://stacks.math.columbia.edu/tag/098I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ProetaleWContractible Cardinal

universe v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] [Small.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J (Type v)]

omit [Small.{v} C] [HasSheafify J (Type v)] in
/-- **A disjoint union of weakly contractible objects is weakly contractible.** -/
theorem isWeaklyContractible_of_disjointCover {I : Type*} {X : C} (V : I → C)
    (f : ∀ i, V i ⟶ X) (hcover : Sieve.ofArrows V f ∈ J X) (hmono : ∀ i, Mono (f i))
    (hdisjoint : ∀ i j, i ≠ j → ∀ (Z : C) (a : Z ⟶ V i) (b : Z ⟶ V j),
      a ≫ f i = b ≫ f j → (⊥ : Sieve Z) ∈ J Z)
    (hV : ∀ i, J.IsWeaklyContractible (V i)) :
    J.IsWeaklyContractible X := by
  classical
  intro F G φ hφ s
  have hlift (i : I) : ∃ t : F.obj.obj (op (V i)),
      φ.hom.app (op (V i)) t = G.obj.map (f i).op s := hV i F G φ hφ _
  choose t ht using hlift
  have hcompat : Presieve.Arrows.Compatible F.obj f t := by
    intro i j Z a b hab
    by_cases hij : i = j
    · subst j
      have := hmono i
      rw [(cancel_mono (f i)).mp hab]
    · have := Limits.Types.isTerminalEquivUnique _
        (Sheaf.isTerminalOfBotCover F Z (hdisjoint i j hij Z a b hab))
      exact Subsingleton.elim _ _
  have hF : Presieve.IsSheafFor F.obj (Presieve.ofArrows V f) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact F.property.isSheafFor _ hcover
  obtain ⟨tX, htX, -⟩ := (Presieve.isSheafFor_arrows_iff F.obj f).mp hF t hcompat
  refine ⟨tX, ?_⟩
  change φ.hom.app (op X) tX = s
  apply (G.property.isSheafFor _ hcover).isSeparatedFor.ext
  intro Z a ha
  obtain ⟨Y, b, c, hc, rfl⟩ := ha
  obtain ⟨i⟩ := hc
  have heq : G.obj.map (f i).op (φ.hom.app (op X) tX) = G.obj.map (f i).op s := by
    rw [← NatTrans.naturality_apply φ.hom (f i).op tX, htX i, ht i]
  simpa only [op_comp, Functor.map_comp, types_comp_apply] using congrArg (G.obj.map b.op) heq

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry.ProEtale

/-! ### Monotonicity of the pro-étale bound -/

/-- The modified pro-étale bound is monotone. -/
private theorem proetaleBound_mono : Monotone Cardinal.proetaleBound.{u} := by
  intro a b hab
  by_cases hb : b = 0
  · subst b
    obtain rfl : a = 0 := le_antisymm hab bot_le
    rfl
  · have hExp : (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ a)) ≤
        (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ b)) :=
      Cardinal.power_le_power_left (by simp)
        (Cardinal.power_le_power_left (by simp)
          (Cardinal.power_le_power_left (by simp) hab))
    have hTop : a ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ a))) ≤
        b ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ b))) :=
      (Cardinal.power_le_power_right hab).trans (Cardinal.power_le_power_left hb hExp)
    unfold Cardinal.proetaleBound Cardinal.stacksBound
    exact sup_le_sup hTop
      (sup_le_sup (Cardinal.power_le_power_right hab) (Order.succ_le_succ hab))

/-- A cardinal is below its modified pro-étale bound. -/
private theorem self_le_proetaleBound (k : Cardinal.{u}) : k ≤ Cardinal.proetaleBound k := by
  unfold Cardinal.proetaleBound Cardinal.stacksBound
  exact (Order.le_succ k).trans ((le_max_right _ _).trans (le_max_right _ _))

/-! ### Affine w-contractible covers with a size bound -/

variable (B : BigProetaleSite.{u})

/-- **Stacks 0983** in the chosen big site, with the cardinality bound of Stacks 0984 retained:
an affine object `T` is covered by a single affine object which is weakly étale and surjective
over `T`, has w-contractible ring of global sections, and has size at most
`Cardinal.proetaleBound` of the size of `T`. -/
private theorem exists_affine_indEtale_wContractible_cover_size_le (T : B.Scheme) [IsAffine T.obj] :
    ∃ (V : B.Scheme) (g : V ⟶ T),
      B.covering ⟨T, PreZeroHypercover.singleton g⟩ ∧ IsAffine V.obj ∧
        IsWContractible.{u, u} Γ(V.obj, ⊤) ∧
        WeaklyEtale (B.inclusion.map g) ∧
        Surjective (B.inclusion.map g) ∧
        V.obj.size ≤ Cardinal.proetaleBound T.obj.size := by
  obtain ⟨V, g, hcov, haff, hwc, -, hwe, hsurj, hsize⟩ :=
    exists_affine_indEtale_wContractible_cover_surjective_size_le B T
  exact ⟨V, g, hcov, haff, hwc, hwe, hsurj, hsize⟩

/-- **An affine open of an object of the chosen big pro-étale site is covered by a single affine
weakly contractible object of the site whose image is exactly that open**, of size at most
`Bound_{pro-étale}` of the size of the ambient object. -/
private theorem exists_wContractible_cover_of_affineOpen (U : B.Scheme)
    (W : U.obj.affineOpens) :
    ∃ (V : B.Scheme) (f : V ⟶ U),
      IsAffine V.obj ∧ V.obj.size ≤ Cardinal.proetaleBound U.obj.size ∧
        B.topology.IsWeaklyContractible V ∧ WeaklyEtale (B.inclusion.map f) ∧
        Set.range (B.inclusion.map f).base = (W.1 : Set U.obj) := by
  let W₀ : B.Scheme :=
    ⟨(W.1 : Scheme.{u}), (Scheme.size_coe_opens_le U.obj W.1).trans_lt U.property⟩
  have _ : IsAffine W₀.obj := W.2
  let q : W₀ ⟶ U := B.inclusion.preimage W.1.ι
  have hq : B.inclusion.map q = W.1.ι := B.inclusion.map_preimage _
  obtain ⟨V, g, -, haff, hwc, hwe, hsurj, hsize⟩ :=
    exists_affine_indEtale_wContractible_cover_size_le B W₀
  have _ : IsAffine V.obj := haff
  have _ : WeaklyEtale (B.inclusion.map g) := hwe
  have _ : Surjective (B.inclusion.map g) := hsurj
  have hmap : B.inclusion.map (g ≫ q) = B.inclusion.map g ≫ W.1.ι := by
    rw [B.inclusion.map_comp, hq]
  refine ⟨V, g ≫ q, haff,
    hsize.trans (proetaleBound_mono (Scheme.size_coe_opens_le U.obj W.1)),
    ((isWContractible_globalSections_tfae B V).out 1 2).mp hwc, ?_, ?_⟩
  · rw [hmap]
    infer_instance
  · rw [hmap]
    have hcomp : ⇑(B.inclusion.map g ≫ W.1.ι).base =
        ⇑W.1.ι.base ∘ ⇑(B.inclusion.map g).base := by
      ext y; exact Scheme.Hom.comp_apply (B.inclusion.map g) W.1.ι y
    rw [hcomp, Set.range_comp, hsurj.surj.range_eq, Set.image_univ, Scheme.Opens.range_ι]

/-! ### One-element covers -/

/-- **A family of affine weakly contractible objects of bounded size assembles into a
one-element covering by a weakly contractible object.** -/
private theorem exists_singleton_cover_of_family (U : B.Scheme) {I : Type u}
    (V : I → B.Scheme) (f : ∀ i, V i ⟶ U)
    (hI : #I ≤ Cardinal.proetaleBound U.obj.size)
    (hsize : ∀ i, (V i).obj.size ≤ Cardinal.proetaleBound U.obj.size)
    (hwe : ∀ i, WeaklyEtale (B.inclusion.map (f i)))
    (hsurj : ∀ x : U.obj, ∃ i, x ∈ Set.range (B.inclusion.map (f i)).base)
    (hqc : QuasiCompactCover
      (⟨I, fun i ↦ (V i).obj, fun i ↦ B.inclusion.map (f i)⟩ : PreZeroHypercover.{u} U.obj))
    (hwc : ∀ i, B.topology.IsWeaklyContractible (V i)) :
    ∃ (W : B.Scheme) (p : W ⟶ U) (_ : W.obj ≅ ∐ fun i ↦ (V i).obj),
      B.covering ⟨U, PreZeroHypercover.singleton p⟩ ∧
        B.topology.IsWeaklyContractible W ∧ WeaklyEtale (B.inclusion.map p) := by
  classical
  let Y : I → Scheme.{u} := fun i ↦ (V i).obj
  let f₀ : (∐ Y) ⟶ U.obj := Sigma.desc fun i ↦ B.inclusion.map (f i)
  have hℵ : ℵ₀ ≤ Cardinal.proetaleBound U.obj.size :=
    U.obj.aleph0_le_size.trans (self_le_proetaleBound _)
  have hYsize : (∐ Y).size ≤ Cardinal.proetaleBound U.obj.size :=
    schemeSize_coproduct_le Y _ hℵ hI hsize
  let W : B.Scheme := ⟨∐ Y, B.closed_under_proetaleBound U.property hYsize⟩
  let ι : ∀ i, V i ⟶ W := fun i ↦ B.inclusion.preimage (Sigma.ι Y i)
  have hι (i : I) : B.inclusion.map (ι i) = Sigma.ι Y i := B.inclusion.map_preimage _
  let p : W ⟶ U := B.inclusion.preimage f₀
  have hp : B.inclusion.map p = f₀ := B.inclusion.map_preimage _
  have hdesc (i : I) : Sigma.ι Y i ≫ f₀ = B.inclusion.map (f i) := Sigma.ι_comp_desc _ i
  have _ : MorphismProperty.ContainsIdentities (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have hcover : Sieve.ofArrows V ι ∈ B.topology W := by
    apply Precoverage.generate_mem_toGrothendieck
    rw [B.precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    change Presieve.ofArrows Y (fun i ↦ B.inclusion.map (ι i)) ∈ _
    simp only [hι]
    refine zariskiPrecoverage_le_proetalePrecoverage _ ?_
    rw [Scheme.zariskiPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ inferInstance⟩
    obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk Y).surjective x
    exact ⟨i, y, by simpa only [sigmaMk_mk] using hy⟩
  have hdisj : ∀ i j, i ≠ j → ∀ (Z : B.Scheme) (a : Z ⟶ V i) (b : Z ⟶ V j),
      a ≫ ι i = b ≫ ι j → (⊥ : Sieve Z) ∈ B.topology Z := by
    intro i j hij Z a b hab
    have hempty : IsEmpty Z.obj := by
      refine ⟨fun z ↦ ?_⟩
      have hmapEq := congrArg B.inclusion.map hab
      rw [Functor.map_comp, hι i, Functor.map_comp, hι j] at hmapEq
      have hz := congrArg (fun q : Scheme.Hom _ _ ↦ q.base z) hmapEq
      have hz' : (Sigma.ι Y i).base ((B.inclusion.map a).base z) =
          (Sigma.ι Y j).base ((B.inclusion.map b).base z) := by
        simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using hz
      have hpair : (⟨i, (B.inclusion.map a).base z⟩ : Σ k : I, Y k) =
          ⟨j, (B.inclusion.map b).base z⟩ :=
        (sigmaMk Y).injective (by simpa only [sigmaMk_mk] using hz')
      exact hij (congrArg Sigma.fst hpair)
    have _ : IsEmpty (B.inclusion.obj Z) := hempty
    rw [← Sieve.generate_bot]
    apply Precoverage.generate_mem_toGrothendieck
    rw [B.precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_bot]
    exact Scheme.bot_mem_propQCPrecoverage (P := @WeaklyEtale) _
  have hWwc : B.topology.IsWeaklyContractible W :=
    B.topology.isWeaklyContractible_of_disjointCover V ι hcover
      (fun i ↦ by
        have : Mono (B.inclusion.map (ι i)) := by rw [hι]; infer_instance
        exact B.inclusion.mono_of_mono_map this)
      hdisj hwc
  have hf₀surj : Function.Surjective f₀.base := by
    intro x
    obtain ⟨i, y, hy⟩ := hsurj x
    refine ⟨(Sigma.ι Y i).base y, ?_⟩
    simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using
      (congrArg (fun q : Scheme.Hom _ _ ↦ q.base y) (hdesc i)).trans hy
  have hf₀we : WeaklyEtale f₀ :=
    IsZariskiLocalAtSource.sigmaDesc (P := @WeaklyEtale) fun i ↦ hwe i
  have hpro : (PreZeroHypercover.singleton.{u + 1} f₀).presieve₀ ∈
      Scheme.proetalePrecoverage U.obj := by
    refine ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr (QuasiCompactCover.of_hom
      (𝒱 := ⟨I, Y, fun i ↦ B.inclusion.map (f i)⟩)
      ⟨fun _ ↦ PUnit.unit, fun i ↦ Sigma.ι Y i, hdesc⟩), ?_⟩
    simpa only [PreZeroHypercover.presieve₀_singleton] using
      (Scheme.singleton_mem_precoverage_iff (P := @WeaklyEtale) f₀).2 ⟨hf₀surj, hf₀we⟩
  refine ⟨W, p, Iso.refl _, ⟨?_, (B.covering_isSite.1 (𝟙 U)).2⟩, hWwc, by rw [hp]; exact hf₀we⟩
  rw [B.isProetaleCovering_iff]
  change (PreZeroHypercover.singleton.{u + 1} (B.inclusion.map p)).presieve₀ ∈ _
  rwa [hp]

/-- **A family whose members surject onto the affine opens of the target is a quasi-compact
cover.** -/
private theorem quasiCompactCover_of_range_eq {X : Scheme.{u}} (E : PreZeroHypercover.{u} X)
    (a : X.affineOpens → E.I₀) (hcpt : ∀ i, CompactSpace (E.X i))
    (hrange : ∀ W : X.affineOpens, Set.range (E.f (a W)).base = (W.1 : Set X)) :
    QuasiCompactCover E := by
  refine ⟨fun {H} hH ↦ ?_⟩
  refine ⟨{a (⟨H, hH⟩ : X.affineOpens)}, Set.finite_singleton _, fun _ _ ↦ ⊤, fun i _ ↦ ?_, ?_⟩
  · have _ := hcpt i
    simpa using isCompact_univ (X := E.X i)
  · rw [Set.biUnion_singleton]
    simpa using hrange (⟨H, hH⟩ : X.affineOpens)

/-- **Each affine open of `U` is the image of an affine weakly contractible object of bounded
size, and these objects form a quasi-compact cover.** -/
private theorem exists_family_of_affineOpens (U : B.Scheme) :
    ∃ (V : U.obj.affineOpens → B.Scheme) (f : ∀ W, V W ⟶ U),
      (∀ W, IsAffine (V W).obj) ∧ (∀ W, (V W).obj.size ≤ Cardinal.proetaleBound U.obj.size) ∧
        (∀ W, B.topology.IsWeaklyContractible (V W)) ∧ (∀ W, WeaklyEtale (B.inclusion.map (f W))) ∧
        (∀ W, Set.range (B.inclusion.map (f W)).base = (W.1 : Set U.obj)) ∧
        QuasiCompactCover (⟨U.obj.affineOpens, fun W ↦ (V W).obj,
          fun W ↦ B.inclusion.map (f W)⟩ : PreZeroHypercover.{u} U.obj) := by
  choose V f haff hsize hwc hwe hrange using
    fun W : U.obj.affineOpens ↦ exists_wContractible_cover_of_affineOpen B U W
  exact ⟨V, f, haff, hsize, hwc, hwe, hrange, quasiCompactCover_of_range_eq _ id
    (fun W ↦ have _ : IsAffine (V W).obj := haff W; inferInstance) hrange⟩

/-- Every object `U` of a chosen big pro-étale site admits a one-element chosen covering
`{V → U}` whose source is a weakly contractible object of the site, presented as a disjoint union
of affine weakly contractible objects and with weakly étale covering morphism. -/
theorem exists_weaklyContractible_coproduct_singleton_covering (U : B.Scheme) :
    ∃ (I : Type u) (Y : I → B.Scheme) (V : B.Scheme) (p : V ⟶ U)
      (_ : V.obj ≅ ∐ fun i ↦ (Y i).obj),
      B.covering ⟨U, PreZeroHypercover.singleton p⟩ ∧
        B.topology.IsWeaklyContractible V ∧ WeaklyEtale (B.inclusion.map p) ∧
        ∀ i, IsAffine (Y i).obj ∧ B.topology.IsWeaklyContractible (Y i) := by
  classical
  obtain ⟨V, f, haff, hsize, hwc, hwe, hrange, hEqc⟩ := exists_family_of_affineOpens B U
  obtain ⟨W, p, e, hcov, hWwc, hpwe⟩ :=
    exists_singleton_cover_of_family B U V f
      ((U.obj.mk_affineOpens_le_size).trans (self_le_proetaleBound _)) hsize hwe
      (fun x ↦ by
        obtain ⟨-, ⟨O, hO, rfl⟩, hxO, -⟩ := U.obj.isBasis_affineOpens.exists_subset_of_mem_open
          (Set.mem_univ x) isOpen_univ
        exact ⟨⟨O, hO⟩, by rw [hrange ⟨O, hO⟩]; exact hxO⟩)
      hEqc hwc
  exact ⟨U.obj.affineOpens, V, W, p, e, hcov, hWwc, hpwe, fun W ↦ ⟨haff W, hwc W⟩⟩

/-- Every object `U` of a chosen big pro-étale site admits a one-element chosen covering
`{V → U}` whose source is a weakly contractible object of the site. -/
@[stacks 0F4P]
theorem exists_weaklyContractible_singleton_covering (U : B.Scheme) :
    ∃ (V : B.Scheme) (p : V ⟶ U),
      B.covering ⟨U, PreZeroHypercover.singleton p⟩ ∧
        B.topology.IsWeaklyContractible V := by
  obtain ⟨-, -, V, p, -, hcov, hwc, -, -⟩ :=
    exists_weaklyContractible_coproduct_singleton_covering B U
  exact ⟨V, p, hcov, hwc⟩

/-- If the underlying scheme of an object `U` of a chosen big pro-étale site is quasi-compact, the
one-element covering can be chosen with affine source and weakly étale covering morphism. -/
theorem exists_affine_weaklyContractible_weaklyEtale_singleton_covering (U : B.Scheme)
    [CompactSpace U.obj] :
    ∃ (V : B.Scheme) (p : V ⟶ U),
      B.covering ⟨U, PreZeroHypercover.singleton p⟩ ∧
        IsAffine V.obj ∧ B.topology.IsWeaklyContractible V ∧
        WeaklyEtale (B.inclusion.map p) := by
  classical
  obtain ⟨V, f, haff, hsize, hwc, hwe, hrange, hEqc⟩ := exists_family_of_affineOpens B U
  let E : PreZeroHypercover.{u} U.obj :=
    ⟨U.obj.affineOpens, fun W ↦ (V W).obj, fun W ↦ B.inclusion.map (f W)⟩
  obtain ⟨Us, hUs, hUsfin, hUseq⟩ :=
    U.obj.isBasis_affineOpens.exists_finite_of_isCompact
      (show IsCompact ((⊤ : U.obj.Opens) : Set U.obj) by
        simpa using isCompact_univ (X := U.obj))
  let A : Type u := {O : U.obj.Opens // O ∈ Us}
  have _ : Finite A := hUsfin.to_subtype
  choose n b O hO hOeq using fun W : A ↦
    QuasiCompactCover.exists_isAffineOpen_of_isCompact E (hUs W.2).isCompact
  let I : Type u := Σ W : A, Fin (n W)
  have _ : Finite I := inferInstanceAs (Finite (Σ W : A, Fin (n W)))
  let a : I → U.obj.affineOpens := fun i ↦ b i.1 i.2
  let E₀ : PreZeroHypercover.{u} U.obj :=
    ⟨I, fun i ↦ (V (a i)).obj, fun i ↦ B.inclusion.map (f (a i))⟩
  have hcover : (⋃ W : A, ((W.1 : U.obj.Opens) : Set U.obj)) = Set.univ := by
    calc (⋃ W : A, ((W.1 : U.obj.Opens) : Set U.obj)) = ⋃ O ∈ Us, (O : Set U.obj) := by
          simp [A]
      _ = ((sSup Us : U.obj.Opens) : Set U.obj) := TopologicalSpace.Opens.coe_sSup
      _ = Set.univ := by rw [← hUseq]; rfl
  have hflat : ∀ i : I, Flat (E₀.f i) := fun i ↦
    have _ : WeaklyEtale (B.inclusion.map (f (a i))) := hwe (a i)
    inferInstance
  have hfpqc : E₀.presieve₀ ∈ Scheme.fpqcPrecoverage U.obj := by
    refine (mem_fpqcPrecoverage_iff_exists_affine_open_cover (f := E₀.f)).2
      ⟨hflat, A, fun W ↦ W.1, fun W ↦ hUs W.2, hcover, fun W ↦ ?_⟩
    exact ⟨n W, fun j ↦ (⟨W, j⟩ : I), O W, fun j ↦ (hO W j).isCompact, hOeq W⟩
  have hE₀qc : QuasiCompactCover E₀ :=
    Scheme.presieve₀_mem_qcPrecoverage_iff.mp hfpqc.1
  have hsurj : ∀ x : U.obj, ∃ i : I, x ∈ Set.range (B.inclusion.map (f (a i))).base := by
    intro x
    obtain ⟨W, hW⟩ := Set.mem_iUnion.mp (hcover ▸ Set.mem_univ x)
    obtain ⟨j, y, -, hy⟩ := Set.mem_iUnion.mp ((Set.ext_iff.mp (hOeq W) x).mpr hW)
    exact ⟨⟨W, j⟩, y, hy⟩
  obtain ⟨W, p, e, hcov, hWwc, hpwe⟩ :=
    exists_singleton_cover_of_family B U (fun i : I ↦ V (a i)) (fun i ↦ f (a i))
      (Cardinal.mk_lt_aleph0.le.trans
        (U.obj.aleph0_le_size.trans (self_le_proetaleBound _)))
      (fun i ↦ hsize (a i)) (fun i ↦ hwe (a i)) hsurj
      hE₀qc (fun i ↦ hwc (a i))
  have _ : ∀ i : I, IsAffine (V (a i)).obj := fun i ↦ haff (a i)
  have _ : IsAffine (∐ fun i : I ↦ (V (a i)).obj) := inferInstance
  exact ⟨W, p, hcov, IsAffine.of_isIso e.hom, hWwc, hpwe⟩

/-- If the underlying scheme of an object `U` of a chosen big pro-étale site is quasi-compact,
the one-element covering of
`AlgebraicGeometry.ProEtale.exists_weaklyContractible_singleton_covering` can be chosen with
affine source. -/
@[stacks 0F4P "the quasi-compact case"]
theorem exists_affine_weaklyContractible_singleton_covering (U : B.Scheme)
    [CompactSpace U.obj] :
    ∃ (V : B.Scheme) (p : V ⟶ U),
      B.covering ⟨U, PreZeroHypercover.singleton p⟩ ∧
        IsAffine V.obj ∧ B.topology.IsWeaklyContractible V := by
  obtain ⟨V, p, hcov, haff, hwc, -⟩ :=
    exists_affine_weaklyContractible_weaklyEtale_singleton_covering B U
  exact ⟨V, p, hcov, haff, hwc⟩

end AlgebraicGeometry.ProEtale

end
