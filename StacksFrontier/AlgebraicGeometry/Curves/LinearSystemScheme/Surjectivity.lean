module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.Injectivity
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeCanonicalSection
public import StacksFrontier.AlgebraicGeometry.Divisors.IntegralDivisorMultiplicity

/-!
# Every family in the fibre of the Abel map comes from `Proj k[T₀, …, Tₙ]`

## Main results

* `Stacks.LinearSystemScheme.familyOf_coordMor`: the pullback of the universal divisor along
  `[c₀ : … : cₙ]` is the divisor of the coordinate section `Σ cᵢ wᵢ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite HomogeneousLocalization
open AlgebraicGeometry.Proj Stacks.AlgebraicGeometry.SectionsBaseChange Stacks.Hilbert

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.LinearSystemScheme

/-- The base change `X ×_k V ⟶ X ×_k T` of an open immersion is an open immersion. -/
theorem isOpenImmersion_familyBaseChangeMap {S : Scheme.{u}} (Y : Over S) {T T' : Over S}
    (g : T ⟶ T') (hg : IsOpenImmersion g.left) : IsOpenImmersion (familyBaseChangeMap Y g) :=
  MorphismProperty.of_isPullback (isPullback_familyBaseChangeMap Y g).flip hg

/-- A point of `X ×_S T` lying over the image of `g` lies in the image of its base change. -/
theorem mem_range_familyBaseChangeMap {S : Scheme.{u}} (Y : Over S) {T T' : Over S} (g : T ⟶ T')
    (hg : IsOpenImmersion g.left) (x : ((Over.pullback T'.hom).obj Y).left)
    (hx : pullback.snd Y.hom T'.hom x ∈ Set.range g.left) :
    x ∈ Set.range (familyBaseChangeMap Y g) := by
  have H := isPullback_familyBaseChangeMap Y g
  obtain ⟨y, rfl⟩ : x ∈ Set.range (pullback.fst (pullback.snd Y.hom T'.hom) g.left) := by
    rwa [IsOpenImmersion.range_pullbackFst]
  refine ⟨H.isoPullback.inv y, ?_⟩
  rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst]

private instance isOpenImmersion_familyBaseChangeMap_restrictHom {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {T : Over (Spec (.of k))}
    (U : T.left.Opens) :
    IsOpenImmersion (familyBaseChangeMap (curveOver f) (restrictHom (k := k) U.ι)) :=
  isOpenImmersion_familyBaseChangeMap _ _ (inferInstanceAs (IsOpenImmersion U.ι))

/-- A point over an open `U` of the base lies in the range of the base change along `U.ι`. -/
private theorem mem_range_familyBaseChangeMap_restrictHom {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {T : Over (Spec (.of k))}
    (U : T.left.Opens) (x : ((Over.pullback T.hom).obj (curveOver f)).left)
    (hx : pullback.snd f T.hom x ∈ U) :
    x ∈ Set.range (familyBaseChangeMap (curveOver f) (restrictHom (k := k) U.ι)) :=
  mem_range_familyBaseChangeMap _ _ (inferInstanceAs (IsOpenImmersion U.ι)) x ⟨⟨_, hx⟩, rfl⟩

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
  (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  {n : ℕ} (w : letI := baseModule f L ⊤; Module.Basis (Fin (n + 1)) Γ(Spec (.of k), ⊤) Γ(L, ⊤))

/-- `[c₀ : … : cₙ]` as a morphism of `k`-schemes. -/
abbrev coordHom {T : Over (Spec (.of k))} (c : Fin (n + 1) → Γ(T.left, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) : T ⟶ projOver k (n := n) :=
  Over.homMk (coordMor T.hom c hc) (coordMor_comp_projToSpec T.hom c hc)

omit [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f] [Smooth f] in
/-- **The pullback of the universal divisor along `[c₀ : … : cₙ]` is the divisor of `Σ cᵢ wᵢ`.** -/
theorem familyOf_coordHom {T : Over (Spec (.of k))} (c : Fin (n + 1) → Γ(T.left, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) :
    familyOf k f L w (coordHom k c hc) = coordDivisor k f L w T.hom c := by
  let U : Fin (n + 1) → T.left.Opens := fun i => T.left.basicOpen (c i)
  refine ideal_ext_of_comap (fun i => familyBaseChangeMap (curveOver f) (restrictHom (U i).ι))
    (fun x => ?_) fun i => ?_
  · have : pullback.snd f T.hom x ∈ (⊤ : T.left.Opens) := trivial
    rw [← iSup_basicOpen_of_span_eq_top (X := T.left) ⊤ (Set.range c) hc] at this
    simp only [TopologicalSpace.Opens.mem_iSup, Set.mem_range, exists_prop] at this
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := this
    exact ⟨i, mem_range_familyBaseChangeMap_restrictHom f (U i) x hi⟩
  · set ι := (U i).ι
    have hcomp : restrictHom (k := k) (T := T) ι ≫ coordHom k c hc =
        coordHom k (T := restrictOver ι) (fun m => ι.appTop (c m))
          (span_range_comp_eq_top ι c hc) :=
      Over.OverMorphism.ext (comp_coordMor T.hom ι c hc)
    have hunit : IsUnit (ι.appTop (c i)) := Scheme.isUnit_of_basicOpen_eq_top _ <| by
      rw [← Scheme.preimage_basicOpen_top]; exact (U i).ι_preimage_self
    let c' : Fin (n + 1) → Γ((U i).toScheme, ⊤) := fun m => ↑hunit.unit⁻¹ * ι.appTop (c m)
    have hc'i : c' i = 1 := hunit.val_inv_mul
    have hc' : Ideal.span (Set.range c') = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (by rw [hc'i]; exact isUnit_one)
    have hscale : coordHom k (T := restrictOver ι) (fun m => ι.appTop (c m))
        (span_range_comp_eq_top ι c hc) = coordHom k (T := restrictOver ι) c' hc' :=
      Over.OverMorphism.ext
        (coordMor_unit_mul _ _ (span_range_comp_eq_top ι c hc) hunit.unit⁻¹ hc').symm
    have hpre : (coordHom k (T := restrictOver ι) c' hc').left ⁻¹ᵁ
        basicOpen (coordGrading k n) (MvPolynomial.X i) = ⊤ := by
      change coordMor _ c' hc' ⁻¹ᵁ _ = ⊤
      rw [coordMor_preimage_basicOpen, hc'i, Scheme.basicOpen_one]
    rw [← familyOf_comp, hcomp, hscale, familyOf_of_chart k f L w _ i hpre]
    have hch : chartCoords (coordHom k (T := restrictOver ι) c' hc').left i hpre = c' :=
      chartCoords_coordMor _ c' hc' i hc'i hpre
    rw [hch, coordDivisor, coordDivisor]
    refine Eq.trans ?_ (comap_zeroScheme_coordSection L w _ _ _ _).symm
    have hs : familyBaseChangeMap (curveOver f) (restrictHom (k := k) (T := T) ι) ≫
        pullback.snd f T.hom = pullback.snd f (restrictOver (k := k) ι).hom ≫ ι :=
      familyBaseChangeMap_comp_snd _ _
    have hf : familyBaseChangeMap (curveOver f) (restrictHom (k := k) (T := T) ι) ≫
        pullback.fst f T.hom = pullback.fst f (restrictOver (k := k) ι).hom :=
      familyBaseChangeMap_comp_fst _ _
    rw [hs, coordSection_comp]
    revert hf
    generalize familyBaseChangeMap (curveOver f) (restrictHom (k := k) (T := T) ι) ≫
      pullback.fst f T.hom = P
    rintro rfl
    rw [show c' = (↑hunit.unit⁻¹ : Γ((U i).toScheme, ⊤)) • (fun m => ι.appTop (c m)) from rfl,
      coordSection_smul, zeroScheme_unit_smul _ _ ((Units.isUnit _).map _)]
    rfl

omit [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f] [Smooth f] in
/-- The zero scheme of the zero section is everything. -/
theorem zeroScheme_zero {Y : Scheme.{u}} (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M] :
    zeroScheme Y M 0 = ⊥ := by
  refine le_antisymm (fun U => ?_) bot_le
  refine le_trans (Scheme.IdealSheafData.ideal_ofIdeals_le _ U) ?_
  change Ideal.span _ ≤ (⊥ : Ideal Γ(Y, U.1))
  rw [Ideal.span_le]
  rintro a ⟨φ, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_bot, map_zero, map_zero]

omit [IsCurve k f] [Smooth f] in
/-- **Over an affine base, a relative effective Cartier divisor with `𝒪(Z) ≅ pr_X^* L` is the
divisor of a unimodular coordinate section.** -/
theorem exists_coordDivisor_eq {V : Scheme.{u}} [IsAffine V] (h : V ⟶ Spec (.of k))
    (Z : (pullback f h).IdealSheafData)
    (hZ : Stacks.Divisors.IsRelativeEffectiveCartierDivisor (pullback.snd f h) Z)
    (e : Stacks.Divisors.modulesInvertibleSheaf Z ≅
      (Scheme.Modules.pullback (pullback.fst f h)).obj L) :
    ∃ (c : Fin (n + 1) → Γ(V, ⊤)) (_ : Ideal.span (Set.range c) = ⊤),
      Z = coordDivisor k f L w h c := by
  have := isQuasicoherent_of_curve L
  have := compactSpace_of_curve k f
  have := quasiSeparatedSpace_of_curve k f
  have hgi : GeometricallyIntegral f := geometricallyIntegral k f
  have : Stacks.Divisors.IsEffectiveCartierDivisor Z := hZ.1
  have hZσ : Z = zeroScheme _ _ (e.hom.app ⊤ (Stacks.Divisors.canonicalSection Z)) :=
    (Stacks.Divisors.zeroScheme_canonicalSection' Z).symm.trans (zeroScheme_eq_of_iso e rfl)
  obtain ⟨c, hcσ⟩ := (coordSection_bijective (IsPullback.of_hasPullback f h) L w).2
    (e.hom.app ⊤ (Stacks.Divisors.canonicalSection Z))
  have hZc : Z = coordDivisor k f L w h c := hZσ.trans (by rw [coordDivisor, hcσ])
  refine ⟨c, ?_, hZc⟩
  rw [← (isAffineOpen_top V).self_le_iSup_basicOpen_iff]
  intro v _
  by_contra hv
  simp only [TopologicalSpace.Opens.mem_iSup, not_exists] at hv
  set ρ := V.fromSpecResidueField v
  have hρ : (fun j => ρ.appTop (c j)) = 0 := by
    funext j
    by_contra hne
    have hunit : IsUnit (ρ.appTop (c j)) := by
      have : IsField Γ(Spec (V.residueField v), ⊤) :=
        (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.toMulEquiv.isField
          (Field.toIsField (V.residueField v))
      let := this.toField
      exact isUnit_iff_ne_zero.mpr hne
    have hmem : IsLocalRing.closedPoint (V.residueField v) ∈
        ρ ⁻¹ᵁ V.basicOpen (c j) := by
      rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ hunit]
      trivial
    have : ρ (IsLocalRing.closedPoint (V.residueField v)) ∈ V.basicOpen (c j) := hmem
    rw [show ρ (IsLocalRing.closedPoint (V.residueField v)) = v from
      Scheme.fromSpecResidueField_apply v _] at this
    exact hv ⟨c j, ⟨j, rfl⟩⟩ this
  have hZv : Z.comap ((pullback.snd f h).fiberι v) = ⊥ := by
    rw [hZc, coordDivisor, comap_zeroScheme_coordSection, (pullback.snd f h).fiber_fac v,
      coordSection_comp, hρ]
    have h0 : coordSection ((pullback.snd f h).fiberι v ≫ pullback.fst f h)
        ((pullback.snd f h).fiberToSpecResidueField v) L w 0 = 0 := by simp [coordSection]
    rw [h0, zeroScheme_zero]
  exact ne_bot_of_isEffectiveCartierDivisor
    (isEffectiveCartierDivisor_comap_fiberι (pullback.snd f h) Z hZ v) hZv

omit [IsAlgClosed k] [IsProjectiveVariety k f] in
/-- The base change of the curve `X ⟶ Spec k` to any `S` is smooth of relative dimension one. -/
theorem smoothOfRelativeDimension_one_pullback_snd {S : Scheme.{u}} (h : S ⟶ Spec (.of k)) :
    SmoothOfRelativeDimension 1 (pullback.snd f h) :=
  have : SmoothOfRelativeDimension 1 f := Stacks.Hilbert.smoothOfRelativeDimension_one_of_isCurve f
  (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
    (IsPullback.of_hasPullback f h) ‹_›

/-- **Over an affine open `V` with `𝒪(Z)|_V ≅ pr_X^* L`, the restriction of `Z` is the divisor of
a unimodular coordinate section.** -/
theorem exists_coordDivisor_eq_comap_restrict {T : Over (Spec (.of k))}
    (Z : ((Over.pullback T.hom).obj (curveOver f)).left.IdealSheafData) {d : ℕ}
    (hZ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (Z.subschemeι ≫ pullback.snd f T.hom) d)
    (V : T.left.Opens) (hV : IsAffineOpen V)
    (e : (Scheme.Modules.pullback
          (familyBaseChangeMap (curveOver f) (restrictHom V.ι))).obj
            (Stacks.Divisors.modulesInvertibleSheaf Z) ≅
        (Scheme.Modules.pullback (pullback.fst f (V.ι ≫ T.hom))).obj L) :
    ∃ (c : Fin (n + 1) → Γ(V.toScheme, ⊤)) (_ : Ideal.span (Set.range c) = ⊤),
      Z.comap (familyBaseChangeMap (curveOver f) (restrictHom V.ι)) =
        coordDivisor k f L w (restrictOver (k := k) (T := T) V.ι).hom c := by
  have : SmoothOfRelativeDimension 1 (pullback.snd f T.hom) :=
    smoothOfRelativeDimension_one_pullback_snd k f T.hom
  have hfl : Stacks.Morphisms.IsFiniteLocallyFree (Z.subschemeι ≫ pullback.snd f T.hom) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d (h := hZ)
  have : Stacks.Divisors.IsEffectiveCartierDivisor Z :=
    (isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree (pullback.snd f T.hom) Z).1
  have : IsAffine V.toScheme := hV
  have hpd : Stacks.Divisors.IsPullbackDefined
      (familyBaseChangeMap (curveOver f) (restrictHom V.ι)) Z :=
    Stacks.Divisors.isPullbackDefined_of_flat _ _ ‹_›
  have hsq := IsPullback.paste_vert
    (Stacks.Bertini.isPullback_subschemeι_comap Z
      (familyBaseChangeMap (curveOver f) (restrictHom V.ι))).flip
    (isPullback_familyBaseChangeMap (curveOver f) (restrictHom V.ι))
  have hrk : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((Z.comap (familyBaseChangeMap (curveOver f) (restrictHom V.ι))).subschemeι ≫
        pullback.snd f (restrictOver (k := k) (T := T) V.ι).hom) d :=
    have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        (Z.subschemeι ≫ pullback.snd (curveOver f).hom T.hom) d := hZ
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback hsq
  have : SmoothOfRelativeDimension 1
      (pullback.snd f (restrictOver (k := k) (T := T) V.ι).hom) :=
    smoothOfRelativeDimension_one_pullback_snd k f _
  have : Stacks.Morphisms.IsFiniteLocallyFree
      ((Z.comap (familyBaseChangeMap (curveOver f) (restrictHom V.ι))).subschemeι ≫
        pullback.snd f (restrictOver (k := k) (T := T) V.ι).hom) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d
  have hrel := isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree
    (pullback.snd f (restrictOver (k := k) (T := T) V.ι).hom)
    (Z.comap (familyBaseChangeMap (curveOver f) (restrictHom V.ι)))
  exact exists_coordDivisor_eq k f L w _ _ hrel
    ((@Stacks.Divisors.invertibleSheafPullbackIso _ _
      (familyBaseChangeMap (curveOver f) (restrictHom V.ι)) Z _ hpd).symm ≪≫ e)

/-- **Every family with `𝒪(Z)` locally `pr_X^* L` is the pullback of the universal divisor.** -/
theorem exists_familyOf_eq {T : Over (Spec (.of k))}
    (Z : ((Over.pullback T.hom).obj (curveOver f)).left.IdealSheafData) {d : ℕ}
    (hZ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (Z.subschemeι ≫ pullback.snd f T.hom) d)
    (hloc : ∀ t : T.left, ∃ V : T.left.Opens, IsAffineOpen V ∧ t ∈ V ∧
      Nonempty ((Scheme.Modules.pullback
          (familyBaseChangeMap (curveOver f) (restrictHom V.ι))).obj
            (Stacks.Divisors.modulesInvertibleSheaf Z) ≅
        (Scheme.Modules.pullback (pullback.fst f (V.ι ≫ T.hom))).obj L)) :
    ∃ g : T ⟶ projOver k (n := n), familyOf k f L w g = Z := by
  choose V hV htV e using hloc
  choose c hc hZc using fun t =>
    exists_coordDivisor_eq_comap_restrict k f L w Z hZ (V t) (hV t) (e t).some
  let 𝒰 : T.left.OpenCover := T.left.openCoverOfIsOpenCover V (eq_top_iff.mpr fun t _ =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨t, htV t⟩)
  let gl : ∀ t, restrictOver (k := k) (T := T) (V t).ι ⟶ projOver k (n := n) :=
    fun t => coordHom k (T := restrictOver (V t).ι) (c t) (hc t)
  have hfam : ∀ t, familyOf k f L w (gl t) =
      Z.comap (familyBaseChangeMap (curveOver f) (restrictHom (V t).ι)) := fun t =>
    (familyOf_coordHom k f L w (T := restrictOver (k := k) (T := T) (V t).ι) (c t) (hc t)).trans
      (hZc t).symm
  -- compatibility on overlaps
  have hcompat' : ∀ a b : T.left, pullback.fst (V a).ι (V b).ι ≫ (gl a).left =
      pullback.snd (V a).ι (V b).ι ≫ (gl b).left := by
    intro a b
    let P : Over (Spec (.of k)) := Over.mk (pullback.fst (V a).ι (V b).ι ≫ (V a).ι ≫ T.hom)
    let pa : P ⟶ restrictOver (k := k) (T := T) (V a).ι := Over.homMk (pullback.fst _ _)
    let pb : P ⟶ restrictOver (k := k) (T := T) (V b).ι :=
      Over.homMk (pullback.snd (V a).ι (V b).ι) (by
        change pullback.snd (V a).ι (V b).ι ≫ (V b).ι ≫ T.hom =
          pullback.fst (V a).ι (V b).ι ≫ (V a).ι ≫ T.hom
        rw [← Category.assoc, ← Category.assoc, pullback.condition])
    have hab : pa ≫ restrictHom (V a).ι = pb ≫ restrictHom (V b).ι := by
      ext1; exact pullback.condition
    exact congrArg (·.left) (eq_of_familyOf_eq k f L w (pa ≫ gl a) (pb ≫ gl b) (by
      rw [familyOf_comp, familyOf_comp, hfam a, hfam b, ← Scheme.IdealSheafData.comap_comp,
        ← Scheme.IdealSheafData.comap_comp, ← familyBaseChangeMap_comp,
        ← familyBaseChangeMap_comp, hab]))
  have hcompat : ∀ a b, pullback.fst (𝒰.f a) (𝒰.f b) ≫ (gl a).left =
      pullback.snd (𝒰.f a) (𝒰.f b) ≫ (gl b).left := hcompat'
  let G : T.left ⟶ Proj (coordGrading k n) := 𝒰.glueMorphisms (fun t => (gl t).left) hcompat
  have hG : ∀ t : T.left, (V t).ι ≫ G = (gl t).left := fun t => 𝒰.ι_glueMorphisms _ hcompat t
  have hGk : G ≫ projToSpec k n = T.hom := by
    refine 𝒰.hom_ext _ _ fun t => ?_
    change (V t).ι ≫ G ≫ _ = (V t).ι ≫ T.hom
    rw [← Category.assoc, hG t]
    exact Over.w (gl t)
  refine ⟨Over.homMk G hGk, ?_⟩
  refine ideal_ext_of_comap (fun t => familyBaseChangeMap (curveOver f) (restrictHom (V t).ι))
    (fun x => ⟨pullback.snd f T.hom x,
      mem_range_familyBaseChangeMap_restrictHom f _ x (htV _)⟩) fun t => ?_
  rw [← familyOf_comp, ← hfam t]
  congr 1
  exact Over.OverMorphism.ext (hG t)

end Stacks.LinearSystemScheme

end
