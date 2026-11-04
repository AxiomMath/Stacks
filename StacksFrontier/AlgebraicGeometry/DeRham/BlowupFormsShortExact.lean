module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsAffine
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsDirectImageEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.Topology.Sheaves.RingedSpace.FlatModulePullback

/-!
# The blowup square of differential forms is short exact

Let `f : X ⟶ S` be smooth and let `i : Z ⟶ X` be a closed immersion with `Z` smooth over `S`;
write `b : X' ⟶ X` for the blowing up of `X` along `Z`, `E` for its exceptional divisor,
`j : E ⟶ X'` for its inclusion and `p : E ⟶ Z` for its projection onto the centre. For every
`a ≥ 0` the commutative square of sheaves of `𝒪_X`-modules

```
Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S}
    |              |
i_*Ω^a_{Z/S} ⟶ i_*p_*Ω^a_{E/S}
```

whose maps are the canonical maps of Section 07HX gives a short exact sequence
`0 ⟶ Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S} ⊕ i_*Ω^a_{Z/S} ⟶ i_*p_*Ω^a_{E/S} ⟶ 0`. This is the input of
[Stacks, Tag 0FUV] which, in the source, is supplied by clauses (1) and (2) of
[Stacks, Tag 0FUU]. Those two clauses hold only where the centre has positive codimension; the
short exactness holds for every closed immersion of smooth `S`-schemes.

The proof is local on `X`. Away from the centre `b` is an isomorphism and both terms on the
centre vanish. Near a point of the centre, [Stacks, Tag 0FUE] gives an étale coordinate chart in
which the centre is the pullback of `𝐀^m ⊆ 𝐀^{m+n}`: if `n ≥ 1`, clauses (1) and (2) of
[Stacks, Tag 0FUR] make the two horizontal maps isomorphisms; if `n = 0`, the centre fills the
chart, the blowup is empty over it, and the left vertical map is an isomorphism. In either case
the square is bicartesian, so the sequence is short exact.

## Main results

* `CategoryTheory.CommSq.shortExact_shortComplex_of_horiz_isIso`,
  `CategoryTheory.CommSq.shortExact_shortComplex_of_vert_isIso`: a commutative square with two
  parallel isomorphisms gives a short exact sequence.
* `Stacks.DeRham.shortExact_of_shortExact_pullback`: short exactness of a sequence of sheaves of
  modules is local for open immersions.
* `Stacks.DeRham.shortExact_blowupFormsSquare`: the blowup square of differential forms gives a
  short exact sequence.

## References

* [Stacks Project, Tag 0FUV](https://stacks.math.columbia.edu/tag/0FUV)
* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Tag 0FUE](https://stacks.math.columbia.edu/tag/0FUE)
* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

attribute [local instance] Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_isClosedImmersion

/-! ### Squares with two parallel isomorphisms -/

namespace CategoryTheory.CommSq

variable {C : Type*} [Category.{v} C] [Abelian C] {X₁ X₂ X₃ X₄ : C} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
  {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

/-- **A commutative square whose horizontal maps are isomorphisms gives a short exact sequence**
`0 ⟶ X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄ ⟶ 0`. -/
theorem shortExact_shortComplex_of_horiz_isIso (sq : CommSq t l r b) [IsIso t] [IsIso b] :
    sq.shortComplex.ShortExact := by
  have h : IsPushout t l r b := IsPushout.of_horiz_isIso sq
  have : Mono sq.shortComplex.f :=
    (IsSplitMono.mk' ⟨biprod.fst ≫ inv t, by simp [CommSq.shortComplex]⟩).mono
  exact { exact := h.exact_shortComplex, mono_f := this, epi_g := h.epi_shortComplex_g }

/-- **A commutative square whose vertical maps are isomorphisms gives a short exact sequence**
`0 ⟶ X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄ ⟶ 0`. -/
theorem shortExact_shortComplex_of_vert_isIso (sq : CommSq t l r b) [IsIso l] [IsIso r] :
    sq.shortComplex.ShortExact := by
  have h : IsPushout t l r b := IsPushout.of_vert_isIso sq
  have : Mono sq.shortComplex.f :=
    (IsSplitMono.mk' ⟨-(biprod.snd ≫ inv l), by simp [CommSq.shortComplex]⟩).mono
  exact { exact := h.exact_shortComplex, mono_f := this, epi_g := h.epi_shortComplex_g }

/-- An additive functor carries the short complex of a commutative square to the short complex of
the image square. -/
def mapShortComplexIso {D : Type*} [Category.{w} D] [Abelian D] (F : C ⥤ D) [F.Additive]
    (sq : CommSq t l r b) :
    F.mapShortComplex.obj sq.shortComplex ≅ (sq.map F).shortComplex :=
  haveI := Limits.preservesBinaryBiproducts_of_preservesBiproducts F
  ShortComplex.isoMk (Iso.refl _) (F.mapBiprod _ _) (Iso.refl _)
    (by
      refine (Category.id_comp _).trans ?_
      change biprod.lift (F.map t) (-F.map l) = F.map (biprod.lift t (-l)) ≫ (F.mapBiprod _ _).hom
      rw [Functor.mapBiprod_hom]
      apply biprod.hom_ext
      · rw [biprod.lift_fst, Category.assoc, biprod.lift_fst, ← F.map_comp, biprod.lift_fst]
      · rw [biprod.lift_snd, Category.assoc, biprod.lift_snd, ← F.map_comp, biprod.lift_snd,
          F.map_neg])
    (by
      refine Eq.trans ?_ (Category.comp_id _).symm
      change (F.mapBiprod _ _).hom ≫ biprod.desc (F.map r) (F.map b) = F.map (biprod.desc r b)
      rw [← Iso.eq_inv_comp, Functor.mapBiprod_inv]
      apply biprod.hom_ext'
      · rw [biprod.inl_desc, biprod.inl_desc_assoc, ← F.map_comp, biprod.inl_desc]
      · rw [biprod.inr_desc, biprod.inr_desc_assoc, ← F.map_comp, biprod.inr_desc])

/-- **An exact additive functor preserves the short exactness of the sequence of a commutative
square.** -/
theorem shortExact_shortComplex_map {D : Type*} [Category.{w} D] [Abelian D] (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (sq : CommSq t l r b)
    (h : sq.shortComplex.ShortExact) : (sq.map F).shortComplex.ShortExact :=
  ShortComplex.shortExact_of_iso (mapShortComplexIso F sq) (h.map_of_exact F)

/-- **An additive functor which inverts the two horizontal maps of a commutative square carries
its sequence to a short exact one.** -/
theorem shortExact_map_shortComplex_of_horiz_isIso {D : Type*} [Category.{w} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (sq : CommSq t l r b) [IsIso (F.map t)] [IsIso (F.map b)] :
    (F.mapShortComplex.obj sq.shortComplex).ShortExact :=
  ShortComplex.shortExact_of_iso (mapShortComplexIso F sq).symm
    (sq.map F).shortExact_shortComplex_of_horiz_isIso

/-- **An additive functor which inverts the two vertical maps of a commutative square carries
its sequence to a short exact one.** -/
theorem shortExact_map_shortComplex_of_vert_isIso {D : Type*} [Category.{w} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (sq : CommSq t l r b) [IsIso (F.map l)] [IsIso (F.map r)] :
    (F.mapShortComplex.obj sq.shortComplex).ShortExact :=
  ShortComplex.shortExact_of_iso (mapShortComplexIso F sq).symm
    (sq.map F).shortExact_shortComplex_of_vert_isIso

end CategoryTheory.CommSq

namespace Stacks.DeRham

/-! ### Short exactness is local for open immersions -/

section Local

variable {X : Scheme.{u}}

/-- The inverse image along an open immersion is exact. -/
theorem preservesFiniteLimits_pullback_of_isOpenImmersion {Y : Scheme.{u}} (ε : Y ⟶ X)
    [IsOpenImmersion ε] : PreservesFiniteLimits (Scheme.Modules.pullback ε) :=
  have h : PreservesFiniteLimits (RingedSpaceModuleAdjunction.modulePullback ε.toLRSHom.toShHom) :=
    RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat _
      fun y => Flat.stalkMap ε y
  h

/-- **A sheaf of modules which vanishes on a family of open immersions covering the scheme is
zero.** -/
theorem isZero_of_isZero_pullback {M : X.Modules}
    (h : ∀ x : X, ∃ (Y : Scheme.{u}) (ε : Y ⟶ X) (_ : IsOpenImmersion ε),
      x ∈ Set.range ε.base ∧ IsZero ((Scheme.Modules.pullback ε).obj M)) : IsZero M := by
  choose Y ε hε hx hz using h
  refine isZero_of_isZero_pullback_ι (fun x => (ε x).opensRange)
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩) fun x => ?_
  have e : (Scheme.Modules.pullback (ε x)).obj M ≅ (Scheme.Modules.pullback
      ((ε x).isoOpensRange.hom)).obj ((Scheme.Modules.pullback (ε x).opensRange.ι).obj M) :=
    (Scheme.Modules.pullbackCongr (Scheme.Hom.isoOpensRange_hom_ι (ε x))).symm.app M ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M).symm
  have := isEquivalence_pullback_of_isIso (ε x).isoOpensRange.hom
  let E := (Scheme.Modules.pullback (ε x).isoOpensRange.hom).asEquivalence
  exact (E.inverse.map_isZero ((hz x).of_iso e.symm)).of_iso (E.unitIso.app _)

/-- **Short exactness of a sequence of sheaves of modules is local for open immersions.** -/
theorem shortExact_of_shortExact_pullback {S : ShortComplex X.Modules}
    (h : ∀ x : X, ∃ (Y : Scheme.{u}) (ε : Y ⟶ X) (_ : IsOpenImmersion ε),
      x ∈ Set.range ε.base ∧ ((Scheme.Modules.pullback ε).mapShortComplex.obj S).ShortExact) :
    S.ShortExact := by
  choose Y ε hε hx hS using h
  have hz : ∀ M : X.Modules, (∀ x, IsZero ((Scheme.Modules.pullback (ε x)).obj M)) → IsZero M :=
    fun M hM => isZero_of_isZero_pullback fun x => ⟨Y x, ε x, hε x, hx x, hM x⟩
  have hl : ∀ x, PreservesFiniteLimits (Scheme.Modules.pullback (ε x)) := fun x =>
    have := hε x
    preservesFiniteLimits_pullback_of_isOpenImmersion (ε x)
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [S.exact_iff_isZero_homology]
    refine hz _ fun x => ?_
    have := hl x
    exact ((S.map (Scheme.Modules.pullback (ε x))).exact_iff_isZero_homology.1 (hS x).exact).of_iso
      (S.mapHomologyIso (Scheme.Modules.pullback (ε x))).symm
  · refine Preadditive.mono_of_isZero_kernel _ (hz _ fun x => ?_)
    have := hl x
    have : Mono ((Scheme.Modules.pullback (ε x)).map S.f) := (hS x).mono_f
    exact (isZero_kernel_of_mono ((Scheme.Modules.pullback (ε x)).map S.f)).of_iso
      (PreservesKernel.iso (Scheme.Modules.pullback (ε x)) S.f)
  · refine Preadditive.epi_of_isZero_cokernel _ (hz _ fun x => ?_)
    have : Epi ((Scheme.Modules.pullback (ε x)).map S.g) := (hS x).epi_g
    exact (isZero_cokernel_of_epi ((Scheme.Modules.pullback (ε x)).map S.g)).of_iso
      (PreservesCokernel.iso (Scheme.Modules.pullback (ε x)) S.g)

end Local

/-! ### Direct images under flat base change -/

section BaseChange

variable {X Y X₁ Y₁ : Scheme.{u}} {g : Y ⟶ X} {g₁ : Y₁ ⟶ X₁} {ε : X₁ ⟶ X} {ε' : Y₁ ⟶ Y}
  (H : IsPullback ε' g₁ g ε) [Flat ε] [QuasiCompact g] [QuasiSeparated g]

include H in
/-- **A direct image vanishes after a flat base change which empties the source**, for a
quasi-coherent module along a quasi-compact and quasi-separated morphism. -/
theorem isZero_pullback_pushforward_of_isEmpty [IsEmpty Y₁] (M : Y.Modules)
    [M.IsQuasicoherent] :
    IsZero ((Scheme.Modules.pullback ε).obj ((Scheme.Modules.pushforward g).obj M)) := by
  have := Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat H M
  exact ((Scheme.Modules.pushforward g₁).map_isZero (isZero_of_isEmpty _)).of_iso
    (asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans H.w).app M))

include H in
/-- **The direct image of a map is invertible after a flat base change as soon as the map is
invertible after the base change upstairs**, between quasi-coherent modules, along a
quasi-compact and quasi-separated morphism. -/
theorem isIso_pullback_map_pushforward_map {M N : Y.Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (φ : M ⟶ N) [IsIso ((Scheme.Modules.pullback ε').map φ)] :
    IsIso ((Scheme.Modules.pullback ε).map ((Scheme.Modules.pushforward g).map φ)) := by
  have := Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat H M
  have := Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat H N
  have hnat := (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans H.w).naturality φ
  simp only [Functor.comp_map] at hnat
  have : IsIso ((Scheme.Modules.pullback ε).map ((Scheme.Modules.pushforward g).map φ) ≫
      (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans H.w).app N) := by
    rw [hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans H.w).app N)

end BaseChange

/-! ### The blowup square of differential forms -/

section Square

open Stacks.DeRham.BlowupTriangle

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

/-- The direct image `i_*p_*M` of a module on the exceptional divisor along the centre is its
direct image `b_*j_*M` along the blowup. -/
def exceptionalPushforwardIso (M : (Stacks.Blowup.exceptionalDivisor i.ker).Modules) :
    (Scheme.Modules.pushforward i).obj
        ((Scheme.Modules.pushforward (exceptionalProjection i)).obj M) ≅
      (Scheme.Modules.pushforward (blowupMap i)).obj
        ((Scheme.Modules.pushforward (exceptionalInclusion i)).obj M) :=
  (Scheme.Modules.pushforwardComp _ _).app M ≪≫
    (Scheme.Modules.pushforwardCongr (exceptionalInclusion_comp_blowupMap i).symm).app M ≪≫
    ((Scheme.Modules.pushforwardComp _ _).app M).symm

variable [Smooth f] [Smooth (i ≫ f)]

/-- **The blowup square of differential forms gives a short exact sequence.** Let `f : X ⟶ S` be
smooth and let `i : Z ⟶ X` be a closed immersion with `Z` smooth over `S`; let `b : X' ⟶ X` be
the blowing up along `Z` and `p : E ⟶ Z` the projection of its exceptional divisor. For `a ≥ 0`,
any commutative square

```
Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S}
    |              | d
i_*Ω^a_{Z/S} ⟶ i_*p_*Ω^a_{E/S}
```

whose other three maps are the canonical ones gives a short exact sequence
`0 ⟶ Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S} ⊕ i_*Ω^a_{Z/S} ⟶ i_*p_*Ω^a_{E/S} ⟶ 0`. No hypothesis on the
codimension of the centre is made. -/
theorem shortExact_blowupFormsSquare (a : ℕ)
    {d : (Scheme.Modules.pushforward (blowupMap i)).obj
        (Scheme.Hom.relativeDifferentialForms (blowupMap i ≫ f) a) ⟶
      (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pushforward (exceptionalProjection i)).obj
        (Scheme.Hom.relativeDifferentialForms (exceptionalStructure f i) a))}
    (w : Scheme.Hom.formsDirectImageComparison (blowupMap i) f a ≫ d =
      Scheme.Hom.formsDirectImageComparison i f a ≫ (Scheme.Modules.pushforward i).map
        (Scheme.Hom.formsDirectImageComparison (exceptionalProjection i) (i ≫ f) a)) :
    (CommSq.mk w).shortComplex.ShortExact := by
  classical
  have := quasiCompact_blowUpToBase_of_smooth f i
  have := quasiCompact_exceptionalToCentre i
  have : (Scheme.Hom.relativeDifferentialForms (exceptionalStructure f i) a).IsQuasicoherent :=
    Scheme.Hom.isQuasicoherent_relativeDifferentialForms _ a
  have : (Scheme.Hom.relativeDifferentialForms (blowupMap i ≫ f) a).IsQuasicoherent :=
    Scheme.Hom.isQuasicoherent_relativeDifferentialForms _ a
  have : (Scheme.Hom.relativeDifferentialForms (i ≫ f) a).IsQuasicoherent :=
    Scheme.Hom.isQuasicoherent_relativeDifferentialForms _ a
  refine shortExact_of_shortExact_pullback fun x => ?_
  by_cases hx : x ∈ Set.range i.base
  · -- near the centre: an étale coordinate chart over an affine open of the base
    obtain ⟨z, rfl⟩ := hx
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
      (show f (i z) ∈ (⊤ : S.Opens) from trivial)
    have : IsAffine V.toScheme := hV
    have : Smooth (restrictCentre i (f ⁻¹ᵁ V) ≫ f ∣_ V) := by
      rw [restrictCentre_comp_morphismRestrict]
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (isPullback_morphismRestrict (i ≫ f) V).flip inferInstance
    let zV : (i ⁻¹ᵁ f ⁻¹ᵁ V).toScheme := ⟨z, hxV⟩
    obtain ⟨m, n, U₀, hzU₀, π, q, hπ, hbase, hpb⟩ :=
      Stacks.AlgebraicGeometry.exists_etale_coordinateSubspaceEmbedding_isPullback (f ∣_ V)
        (restrictCentre i (f ⁻¹ᵁ V)) zV
    have : Etale π := hπ
    have H : IsPullback ((restrictCentre i (f ⁻¹ᵁ V) ⁻¹ᵁ U₀).ι ≫ (i ⁻¹ᵁ f ⁻¹ᵁ V).ι)
        (restrictCentre (restrictCentre i (f ⁻¹ᵁ V)) U₀) i (U₀.ι ≫ (f ⁻¹ᵁ V).ι) :=
      (isPullback_restrictCentre _ U₀).paste_horiz (isPullback_restrictCentre i (f ⁻¹ᵁ V))
    have he : (U₀.ι ≫ (f ⁻¹ᵁ V).ι) ≫ f = (U₀.ι ≫ f ∣_ V) ≫ V.ι := by
      rw [Category.assoc, Category.assoc, morphismRestrict_ι]
    have hxε : i z ∈ Set.range (U₀.ι ≫ (f ⁻¹ᵁ V).ι).base := by
      refine ⟨⟨restrictCentre i (f ⁻¹ᵁ V) zV, hzU₀⟩, ?_⟩
      have h := congrArg (fun g => g zV)
        (Scheme.Hom.resLE_comp_ι i (le_rfl : i ⁻¹ᵁ f ⁻¹ᵁ V ≤ i ⁻¹ᵁ f ⁻¹ᵁ V))
      simp only [Scheme.Hom.comp_apply] at h
      simp only
      exact h
    refine ⟨U₀, U₀.ι ≫ (f ⁻¹ᵁ V).ι, inferInstance, hxε, ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- codimension zero: the centre fills the chart and the blowup is empty over it
      have : IsIso (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding V m 0) := by
        rw [coordinateSubspaceEmbedding_zero]
        infer_instance
      have : IsIso (restrictCentre (restrictCentre i (f ⁻¹ᵁ V)) U₀) := hpb.isIso_fst_of_isIso
      have := Scheme.Hom.isIso_formsDirectImageComparison_of_isIso
        (restrictCentre (restrictCentre i (f ⁻¹ᵁ V)) U₀) (U₀.ι ≫ f ∣_ V) (a : ℤ)
      have : IsIso ((Scheme.Modules.pullback (U₀.ι ≫ (f ⁻¹ᵁ V).ι)).map
          (Scheme.Hom.formsDirectImageComparison i f a)) :=
        Scheme.Hom.isIso_pullback_map_formsDirectImageComparison_of_isPullback H f
          (U₀.ι ≫ f ∣_ V) V.ι he a
      obtain ⟨ε', hb⟩ := Stacks.Blowup.exists_isPullback_blowUpToBase_of_isPullback H
      have : IsEmpty (Stacks.Blowup.blowUp
          (restrictCentre (restrictCentre i (f ⁻¹ᵁ V)) U₀).ker) := by
        rw [Scheme.Hom.ker_eq_bot_of_isIso]
        have := AlgebraicGeometry.isEmpty_blowUp_bot U₀.toScheme
        exact Function.isEmpty (AlgebraicGeometry.blowUpIso ⊥).inv
      have hB := isZero_pullback_pushforward_of_isEmpty hb
        (Scheme.Hom.relativeDifferentialForms (blowupMap i ≫ f) a)
      have hC := (isZero_pullback_pushforward_of_isEmpty hb
        ((Scheme.Modules.pushforward (exceptionalInclusion i)).obj
          (Scheme.Hom.relativeDifferentialForms (exceptionalStructure f i) a))).of_iso
        ((Scheme.Modules.pullback (U₀.ι ≫ (f ⁻¹ᵁ V).ι)).mapIso (exceptionalPushforwardIso i _))
      have : IsIso ((Scheme.Modules.pullback (U₀.ι ≫ (f ⁻¹ᵁ V).ι)).map d) :=
        isIso_of_source_target_iso_zero _ hB.isoZero hC.isoZero
      exact CommSq.shortExact_map_shortComplex_of_vert_isIso _ _
    · -- positive codimension: clauses (1) and (2) of Stacks 0FUR in the chart
      have := quasiCompact_blowUpToBase_coordinateSubspaceEmbedding V m n
      have : IsIso ((Scheme.Modules.pullback (U₀.ι ≫ (f ⁻¹ᵁ V).ι)).map
          (Scheme.Hom.formsDirectImageComparison (blowupMap i) f a)) := by
        have h₁ := isIso_blowupFormsDirectImage_of_isPullback _ (U₀.ι ≫ f ∣_ V) hpb.flip
          (𝟙 V.toScheme) (by rw [hbase, Category.comp_id]) a
          (isIso_blowupFormsDirectImage_coordinateSubspaceEmbedding_of_isAffine V m n hn a)
        have h := isIso_pullback_map_blowupFormsDirectImage_of_isPullback f (U₀.ι ≫ f ∣_ V) H
          V.ι he a h₁
        rwa [blowupFormsDirectImage_eq] at h
      have : IsIso ((Scheme.Modules.pullback
          ((restrictCentre i (f ⁻¹ᵁ V) ⁻¹ᵁ U₀).ι ≫ (i ⁻¹ᵁ f ⁻¹ᵁ V).ι)).map
          (Scheme.Hom.formsDirectImageComparison (exceptionalProjection i) (i ≫ f) a)) := by
        have h₂ := isIso_exceptionalFormsDirectImage_of_isPullback _ (U₀.ι ≫ f ∣_ V) hpb.flip
          (𝟙 V.toScheme) (by rw [hbase, Category.comp_id]) a
          (isIso_exceptionalFormsDirectImage_coordinateSubspaceEmbedding_of_isAffine V m n hn a)
        have h := isIso_pullback_map_exceptionalFormsDirectImage_of_isPullback f (U₀.ι ≫ f ∣_ V)
          H V.ι he a h₂
        rwa [exceptionalFormsDirectImage_eq] at h
      have := isIso_pullback_map_pushforward_map H
        (Scheme.Hom.formsDirectImageComparison (exceptionalProjection i) (i ≫ f) a)
      exact CommSq.shortExact_map_shortComplex_of_horiz_isIso _ _
  · -- away from the centre the blowing-up morphism is an isomorphism
    refine ⟨centreComplement i, (centreComplement i).ι, inferInstance, ?_, ?_⟩
    · rw [Scheme.Opens.range_ι]
      exact hx
    have := isIso_blowUpToBase_restrictCentre_centreComplement i
    have : IsIso ((Scheme.Modules.pullback (centreComplement i).ι).map
        (Scheme.Hom.formsDirectImageComparison (blowupMap i) f a)) := by
      have h := isIso_pullback_map_blowupFormsDirectImage_of_isPullback f
        ((centreComplement i).ι ≫ f) (isPullback_restrictCentre i _) (𝟙 S)
        (by rw [Category.comp_id]) a (isIso_blowupFormsDirectImage_of_isIso_blowUpToBase _ _ _)
      rwa [blowupFormsDirectImage_eq] at h
    have : IsEmpty (i ⁻¹ᵁ centreComplement i).toScheme := ⟨fun y => y.2 ⟨y.1, rfl⟩⟩
    have h₁ := isZero_pullback_pushforward_of_isEmpty
      (isPullback_restrictCentre i (centreComplement i))
      (Scheme.Hom.relativeDifferentialForms (i ≫ f) a)
    have h₂ := isZero_pullback_pushforward_of_isEmpty
      (isPullback_restrictCentre i (centreComplement i))
      ((Scheme.Modules.pushforward (exceptionalProjection i)).obj
        (Scheme.Hom.relativeDifferentialForms (exceptionalStructure f i) a))
    have : IsIso ((Scheme.Modules.pullback (centreComplement i).ι).map
        ((Scheme.Modules.pushforward i).map
          (Scheme.Hom.formsDirectImageComparison (exceptionalProjection i) (i ≫ f) a))) :=
      isIso_of_source_target_iso_zero _ h₁.isoZero h₂.isoZero
    exact CommSq.shortExact_map_shortComplex_of_horiz_isIso _ _

end Square

end Stacks.DeRham

end
