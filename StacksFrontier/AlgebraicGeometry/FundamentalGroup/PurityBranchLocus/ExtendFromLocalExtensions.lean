module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.ExtendFiniteEtale
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending a finite étale cover from local extensions

Let `X` be a locally Noetherian scheme, `W ⊆ X` a quasi-compact open and `U ⊆ W` an open. A
finite étale cover `E` of `U` extends to a finite étale cover of `W` as soon as the following
local condition holds: whenever `E` has been extended to a cover `F` of an open `V` with
`U ⊆ V ⊆ W`, and `x ∈ W ∖ V` is a point whose local scheme `Spec 𝒪_{X, x}` meets `V` exactly in
its punctured spectrum, the restriction of `F` to that punctured spectrum extends to a finite
étale cover of `Spec 𝒪_{X, x}`.

This is the Noetherian induction of [Stacks, Tag 0EY7] and of [Stacks, Tag 0H2W] with the local
input left open, so that it can be supplied by purity at some points and by a
codimension-one argument at others. The induction runs inside the quasi-compact open `W`, which
is a Noetherian space, so `X` itself need only be locally Noetherian.

## Main results

* `AlgebraicGeometry.isRetrocompact_of_isLocallyNoetherian`: every subset of a locally
  Noetherian scheme is retrocompact.
* `AlgebraicGeometry.nonempty_iso_restrict_iff_of_preimage_eq`: extendability of the
  restriction of a cover to the local scheme at `x` only depends on the preimage of the open.
* `AlgebraicGeometry.exists_finiteEtale_extension_of_forall_extends`: the local-to-global
  extension principle described above.

## Implementation notes

At a stage `V ≠ W` of the induction the new point `x` is chosen in `W ∖ V` with the least
coheight, that is with local ring of least dimension. Every proper generization of such a point
lies in `W`, because `W` is open, and has strictly smaller coheight, because the coheight of a
point of a locally Noetherian scheme is the finite dimension of its local ring; so it lies in
`V`. Hence the preimage of `V` in `Spec 𝒪_{X, x}` is the punctured spectrum.

## References

* [Stacks Project, Lemma 58.21.6 (0EY7)](https://stacks.math.columbia.edu/tag/0EY7)
* [Stacks Project, Lemma 58.31.2 (0H2W)](https://stacks.math.columbia.edu/tag/0H2W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

/-- Every subset of a locally Noetherian scheme is retrocompact: a quasi-compact open is a
Noetherian space, in which every subset is quasi-compact. -/
@[ega "I 6.1.2" "more general", ega "IV 1.8.1" "special case"]
theorem isRetrocompact_of_isLocallyNoetherian {X : Scheme.{u}} [IsLocallyNoetherian X]
    (s : Set X) : IsRetrocompact s := by
  intro K hK hKo
  let V : X.Opens := ⟨K, hKo⟩
  have : CompactSpace V := isCompact_iff_compactSpace.mp hK
  have : IsNoetherian V.toScheme := {}
  have : TopologicalSpace.NoetherianSpace V.toScheme := inferInstance
  have hc : IsCompact ((Subtype.val : V → X) ⁻¹' s) :=
    TopologicalSpace.NoetherianSpace.isCompact (α := V.toScheme) _
  have himage := hc.image continuous_subtype_val
  have heq : (Subtype.val : V → X) '' ((Subtype.val : V → X) ⁻¹' s) = s ∩ K :=
    Set.ext fun y ↦ ⟨fun ⟨z, hz, hzy⟩ ↦ hzy ▸ ⟨hz, z.2⟩,
      fun ⟨hs, hk⟩ ↦ ⟨⟨y, hk⟩, hs, rfl⟩⟩
  rwa [heq] at himage

/-- If base change along an isomorphism carries two finite étale covers to isomorphic covers,
the two covers are isomorphic. -/
theorem nonempty_iso_of_nonempty_iso_finiteEtaleBaseChange {T T' : Scheme.{u}} (e : T ≅ T')
    (A B : FiniteEtaleOver T')
    (h : Nonempty ((finiteEtaleBaseChange e.hom).obj A ≅ (finiteEtaleBaseChange e.hom).obj B)) :
    Nonempty (A ≅ B) := by
  obtain ⟨i⟩ := h
  let back (C : FiniteEtaleOver T') :
      (finiteEtaleBaseChange e.inv).obj ((finiteEtaleBaseChange e.hom).obj C) ≅ C :=
    ((finiteEtaleBaseChangeComp e.inv e.hom (𝟙 T') e.inv_hom_id.symm).app C).symm ≪≫
      finiteEtaleBaseChangeId.app C
  exact ⟨(back A).symm ≪≫ (finiteEtaleBaseChange e.inv).mapIso i ≪≫ back B⟩

/-- **Extendability over the local scheme only depends on the preimage of the open.** Let
`U₁ ≤ U₂` be opens of `X` whose preimages in `Spec 𝒪_{X, x}` agree, and let `E` be a finite étale
cover of `U₂`. A finite étale cover `L` of `Spec 𝒪_{X, x}` extends the restriction of `E` to the
preimage of `U₂` exactly when it extends the restriction of `E|_{U₁}` to the preimage of `U₁`. -/
theorem nonempty_iso_restrict_iff_of_preimage_eq {X : Scheme.{u}} {U₁ U₂ : X.Opens}
    (h12 : U₁ ≤ U₂) (x : X)
    (hpre : (X.fromSpecStalk x) ⁻¹ᵁ U₁ = (X.fromSpecStalk x) ⁻¹ᵁ U₂)
    (E : FiniteEtaleOver U₂.toScheme) (L : FiniteEtaleOver (Spec (X.presheaf.stalk x))) :
    Nonempty ((finiteEtaleBaseChange ((X.fromSpecStalk x) ⁻¹ᵁ U₂).ι).obj L ≅
        (finiteEtaleBaseChange ((X.fromSpecStalk x) ∣_ U₂)).obj E) ↔
      Nonempty ((finiteEtaleBaseChange ((X.fromSpecStalk x) ⁻¹ᵁ U₁).ι).obj L ≅
        (finiteEtaleBaseChange ((X.fromSpecStalk x) ∣_ U₁)).obj
          ((finiteEtaleBaseChange (X.homOfLE h12)).obj E)) := by
  let e := (Spec (X.presheaf.stalk x)).isoOfEq hpre
  have h1 : ((X.fromSpecStalk x) ⁻¹ᵁ U₁).ι = e.hom ≫ ((X.fromSpecStalk x) ⁻¹ᵁ U₂).ι :=
    (Scheme.isoOfEq_hom_ι _ hpre).symm
  have h2 : e.hom ≫ (X.fromSpecStalk x) ∣_ U₂ =
      (X.fromSpecStalk x) ∣_ U₁ ≫ X.homOfLE h12 := by
    apply (cancel_mono U₂.ι).1
    rw [Category.assoc, morphismRestrict_ι, Category.assoc, Scheme.homOfLE_ι,
      morphismRestrict_ι, ← Category.assoc, ← h1]
  let iL : (finiteEtaleBaseChange ((X.fromSpecStalk x) ⁻¹ᵁ U₁).ι).obj L ≅
      (finiteEtaleBaseChange e.hom).obj
        ((finiteEtaleBaseChange ((X.fromSpecStalk x) ⁻¹ᵁ U₂).ι).obj L) :=
    (finiteEtaleBaseChangeComp e.hom _ _ h1).app L
  let iE : (finiteEtaleBaseChange ((X.fromSpecStalk x) ∣_ U₁)).obj
        ((finiteEtaleBaseChange (X.homOfLE h12)).obj E) ≅
      (finiteEtaleBaseChange e.hom).obj
        ((finiteEtaleBaseChange ((X.fromSpecStalk x) ∣_ U₂)).obj E) :=
    ((finiteEtaleBaseChangeComp _ (X.homOfLE h12) _ h2).app E).symm ≪≫
      (finiteEtaleBaseChangeComp e.hom _ _ rfl).app E
  exact ⟨fun ⟨i⟩ ↦ ⟨iL ≪≫ (finiteEtaleBaseChange e.hom).mapIso i ≪≫ iE.symm⟩,
    fun ⟨i⟩ ↦ nonempty_iso_of_nonempty_iso_finiteEtaleBaseChange e _ _ ⟨iL.symm ≪≫ i ≪≫ iE⟩⟩

/-- In a locally Noetherian scheme, a point `x` of an open `W` lying outside an open `V` and
of least coheight among such points has the punctured spectrum of `𝒪_{X, x}` as the preimage of
`V`: its proper generizations lie in `W` and have smaller coheight. -/
theorem preimage_fromSpecStalk_eq_puncturedSpectrum_of_coheight_le
    {X : Scheme.{u}} [IsLocallyNoetherian X] (W V : X.Opens) (x : X) (hxW : x ∈ W)
    (hxV : x ∉ V)
    (hmin : ∀ y : X, y ∈ W → y ∉ V → Order.coheight x ≤ Order.coheight y) :
    (X.fromSpecStalk x) ⁻¹ᵁ V = Stacks.puncturedSpectrum (X.presheaf.stalk x) := by
  ext y
  refine ⟨fun hy hclosed ↦ ?_, fun hy ↦ ?_⟩
  · have hyV : X.fromSpecStalk x y ∈ V := hy
    rw [show y = IsLocalRing.closedPoint (X.presheaf.stalk x) from hclosed,
      Scheme.fromSpecStalk_closedPoint] at hyV
    exact hxV hyV
  · by_contra hyV
    have hyV' : X.fromSpecStalk x y ∉ V := hyV
    have hspec : X.fromSpecStalk x y ⤳ x := by
      have hmem : X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x) := ⟨y, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at hmem
    have hne : X.fromSpecStalk x y ≠ x := by
      intro heq
      apply hy
      apply (X.fromSpecStalk x).isEmbedding.injective
      rw [heq, Scheme.fromSpecStalk_closedPoint]
    have hyW : X.fromSpecStalk x y ∈ W := hspec.mem_open W.2 hxW
    have hlt : x < X.fromSpecStalk x y :=
      lt_of_le_not_ge hspec fun h ↦ hne (hspec.antisymm h).eq
    have hfin : Order.coheight (X.fromSpecStalk x y) < ⊤ := by
      have h := ringKrullDim_stalk_eq_coheight (X.fromSpecStalk x y)
      have hlt' : ringKrullDim (X.presheaf.stalk (X.fromSpecStalk x y)) < ⊤ :=
        ringKrullDim_lt_top
      rw [h] at hlt'
      exact WithBot.coe_lt_coe.mp (by simpa using hlt')
    exact absurd (hmin _ hyW hyV') (not_le.mpr (Order.coheight_strictAnti hlt hfin))

/-- **Extension of a finite étale cover from local extensions.** Let `X` be locally Noetherian,
`W ⊆ X` a quasi-compact open, `U ⊆ W` an open and `E` a finite étale cover of `U`. Suppose that
whenever `E` extends to a cover `F` of an open `V` with `U ⊆ V`, and `x ∈ W ∖ V` is a point whose
local scheme meets `V` exactly in its punctured spectrum, the restriction of `F` to that
punctured spectrum extends over `Spec 𝒪_{X, x}`. Then `E` extends to a finite étale cover of
`W`. -/
theorem exists_finiteEtale_extension_of_forall_extends
    {X : Scheme.{u}} [IsLocallyNoetherian X] (W : X.Opens) (hW : IsCompact (W : Set X))
    (U : X.Opens) (hUW : U ≤ W) (E : FiniteEtaleOver U.toScheme)
    (h : ∀ (V : X.Opens) (hUV : U ≤ V) (F : FiniteEtaleOver V.toScheme),
      Nonempty ((finiteEtaleBaseChange (X.homOfLE hUV)).obj F ≅ E) →
      ∀ x : X, x ∈ W → x ∉ V →
        (X.fromSpecStalk x) ⁻¹ᵁ V = Stacks.puncturedSpectrum (X.presheaf.stalk x) →
        ∃ L : FiniteEtaleOver (Spec (X.presheaf.stalk x)),
          Nonempty ((finiteEtaleBaseChange ((X.fromSpecStalk x) ⁻¹ᵁ V).ι).obj L ≅
            (finiteEtaleBaseChange ((X.fromSpecStalk x) ∣_ V)).obj F)) :
    ∃ F : FiniteEtaleOver W.toScheme,
      Nonempty ((finiteEtaleBaseChange (X.homOfLE hUW)).obj F ≅ E) := by
  classical
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW
  have : IsNoetherian W.toScheme := {}
  let φ : {V : X.Opens // V ≤ W} → W.toScheme.Opens := fun V ↦ W.ι ⁻¹ᵁ V.1
  have hφ : StrictMono φ := by
    intro V₁ V₂ hlt
    refine lt_of_le_of_ne (Scheme.Hom.preimage_mono _ hlt.le) fun heq ↦ hlt.ne ?_
    apply Subtype.ext
    have key (V : {V : X.Opens // V ≤ W}) : W.ι ''ᵁ φ V = V.1 := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr V.2
    rw [← key V₁, ← key V₂, heq]
  have : WellFoundedGT {V : X.Opens // V ≤ W} := hφ.wellFoundedGT
  let Ext (V : {V : X.Opens // V ≤ W}) : Prop :=
    ∃ (hUV : U ≤ V.1) (F : FiniteEtaleOver V.1.toScheme),
      Nonempty ((finiteEtaleBaseChange (X.homOfLE hUV)).obj F ≅ E)
  have hExt₀ : Ext ⟨U, hUW⟩ :=
    ⟨le_rfl, E, ⟨eqToIso (congrArg (fun f ↦ (finiteEtaleBaseChange f).obj E)
      (Scheme.homOfLE_rfl X U)) ≪≫ finiteEtaleBaseChangeId.app E⟩⟩
  obtain ⟨⟨V, hVle⟩, -, hVmax⟩ := exists_maximal_ge_of_wellFoundedGT Ext ⟨U, hUW⟩ hExt₀
  obtain ⟨hUV, F, ⟨iV⟩⟩ := hVmax.1
  have hVW : V = W := by
    by_contra hne
    let Z : Set X := (W : Set X) \ V
    have hZ : Z.Nonempty := Set.nonempty_of_not_subset fun hsub ↦ hne (le_antisymm hVle hsub)
    let x := Function.argminOn (fun y : X ↦ Order.coheight y) Z hZ
    have hxZ : x ∈ Z := Function.argminOn_mem _ _ _
    have hmin : ∀ y : X, y ∈ W → y ∉ V → Order.coheight x ≤ Order.coheight y :=
      fun y hyW hyV ↦ Function.argminOn_le _ _ (show y ∈ Z from ⟨hyW, hyV⟩)
    have hpre := preimage_fromSpecStalk_eq_puncturedSpectrum_of_coheight_le W V x hxZ.1
      hxZ.2 hmin
    obtain ⟨V', hVV', hxV', F', ⟨iF'⟩⟩ :=
      exists_finiteEtale_extension_neighborhood_of_extends V
        (isRetrocompact_of_isLocallyNoetherian _) x hxZ.2 F
        (h V hUV F ⟨iV⟩ x hxZ.1 hxZ.2 hpre)
    let V'' : X.Opens := V' ⊓ W
    have hVV'' : V ≤ V'' := le_inf hVV' hVle
    let F'' := (finiteEtaleBaseChange (X.homOfLE (inf_le_left : V'' ≤ V'))).obj F'
    have hExt : Ext ⟨V'', inf_le_right⟩ :=
      ⟨hUV.trans hVV'', F'', ⟨(finiteEtaleBaseChangeComp (X.homOfLE hUV) (X.homOfLE hVV'') _
          (Scheme.homOfLE_homOfLE X hUV hVV'').symm).app F'' ≪≫
        (finiteEtaleBaseChange (X.homOfLE hUV)).mapIso
          (((finiteEtaleBaseChangeComp (X.homOfLE hVV'') (X.homOfLE inf_le_left) _
            (Scheme.homOfLE_homOfLE X hVV'' inf_le_left).symm).app F').symm ≪≫ iF') ≪≫
        iV⟩⟩
    exact hxZ.2 ((show V'' ≤ V from hVmax.2 hExt hVV'') ⟨hxV', hxZ.1⟩)
  subst hVW
  exact ⟨F, ⟨iV⟩⟩

end AlgebraicGeometry

end
