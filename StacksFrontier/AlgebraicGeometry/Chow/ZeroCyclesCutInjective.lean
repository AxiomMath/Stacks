module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroCyclesBertiniChainDefs
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroCyclesBertiniStalks
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroCyclesCotangentCut

/-!
# Multiplication by the next section is injective at the points of the cut

In the proof of [Stacks, Tag 0FH5] a smooth projective `k`-scheme `X` of dimension `d` is cut by
sections `s_1, …, s_d` of an invertible module, and the cycle class of each successive cut
`H_1 ∩ ⋯ ∩ H_{j+1} ⊆ W = H_1 ∩ ⋯ ∩ H_j` is computed by Stacks 02SQ, which needs multiplication
by `s_{j+1}|_W` to be injective on the local rings of `W` at the generic points of the cut. This
file proves that injectivity in the two situations that occur.

* `Stacks.Chow.BertiniChain.injective_restrictedSection_of_notMem_support`: off the support of
  the closed subscheme `Z` the sections vanish on, `W` is smooth over `k`, so its local rings are
  regular, hence domains, and the germ of `s_{j+1}|_W` is nonzero because `s_{j+1}` vanishes at
  no generic point of `W` off `Z`.
* `Stacks.Chow.BertiniChain.injective_restrictedSection_at_point`: at a point of the last cut
  over a point `x` with `dim O_{X,x} = d + 1` at which all `d + 1` zero schemes meet in the
  reduced point, the local ring of `W = H_1 ∩ ⋯ ∩ H_d` is `O_{X,x}` modulo `d` local equations
  which together with the last one generate `𝔪_x`; by Krull's height theorem it has dimension at
  least one and principal maximal ideal, so it is a discrete valuation ring and the last local
  equation is a nonzero element of it.

## References

* [Stacks Project, Tag 0FH5](https://stacks.math.columbia.edu/tag/0FH5)
* [Stacks Project, Tag 02SQ](https://stacks.math.columbia.edu/tag/02SQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Stacks.Ample
open CategoryTheory.Limits IsLocalRing
open Stacks.SectionsVanishingOnSubscheme Stacks.Chow.CompleteIntersection

universe u

namespace Stacks.Chow.BertiniChain

attribute [local instance] Stacks.SectionsVanishingOnSubscheme.isInvertible_of_isInvertibleModule
attribute [local instance] Stacks.InvertiblePullback.isInvertibleModule_pullback

/-- Off the support of `I`, the local rings of the closed subscheme cut out by `T` are domains as
soon as the trace of `T` on the complement of the support is smooth over `k`. -/
theorem isDomain_stalk_of_smoothOffSupport {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (I T : X.IdealSheafData) (hT : SmoothOffSupport f I T)
    (w : T.subscheme) (hw : T.subschemeι w ∉ I.support) :
    IsDomain (T.subscheme.presheaf.stalk w) := by
  set U := openComplement I
  have : Smooth ((T.comap U.ι).subschemeι ≫ (U.ι ≫ f)) := hT
  let φ : (T.comap U.ι).subscheme ⟶ T.subscheme :=
    (T.comapIso U.ι).hom ≫ pullback.snd U.ι T.subschemeι
  obtain ⟨z, hz⟩ : w ∈ Set.range (pullback.snd U.ι T.subschemeι).base := by
    rw [IsOpenImmersion.range_pullbackSnd]
    show T.subschemeι w ∈ U.ι.opensRange
    rw [Scheme.Opens.opensRange_ι]
    exact hw
  let w' := (T.comapIso U.ι).inv z
  have hw' : φ w' = w := by
    have h1 : (T.comapIso U.ι).hom ((T.comapIso U.ι).inv z) = z := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
    show ((T.comapIso U.ι).hom ≫ pullback.snd U.ι T.subschemeι) ((T.comapIso U.ι).inv z) = w
    rw [Scheme.Hom.comp_apply, h1, hz]
  have := isRegularLocalRing_stalk_of_smooth
    ((T.comap U.ι).subschemeι ≫ (U.ι ≫ f)) w'
  have : IsDomain ((T.comap U.ι).subscheme.presheaf.stalk w') := IsRegularLocalRing.isDomain _
  have e := (asIso (φ.stalkMap w')).commRingCatIsoToRingEquiv
  rw [← hw']
  exact e.toMulEquiv.isDomain _

/-- If a section `s` does not vanish at the generic points of the closed subscheme `W` cut out by
`T` lying off the support of `I`, then the germ of the restriction `s|_W` is nonzero at every
point `w ∈ W` off the support of `I`. -/
theorem germ_restrictedSection_ne_zero {X : Scheme.{u}} (I T : X.IdealSheafData)
    (M : X.Modules) [IsInvertibleModule X M] (s : Γ(M, ⊤))
    (hgen : NonvanishingAtGenericOff I T M s) (w : T.subscheme)
    (hw : T.subschemeι w ∉ I.support) :
    (((Scheme.Modules.pullback T.subschemeι).obj M).presheaf.Γgerm w).hom
      ((restrictedSection T M s).eval (op ⊤)) ≠ 0 := by
  intro h0
  let η : genericPoints T.subscheme :=
    genericPoints.ofComponent
      ⟨irreducibleComponent w, irreducibleComponent_mem_irreducibleComponents w⟩
  have hηw : η.1 ⤳ w := by
    rw [specializes_iff_mem_closure, (genericPoints.isGenericPoint_ofComponent _).def]
    exact mem_irreducibleComponent
  have hηI : T.subschemeι η.1 ∉ I.support := fun h =>
    hw ((hηw.map T.subschemeι.continuous).mem_closed I.support.isClosed h)
  have hnv := hgen η.1 η.2 hηI
  rw [← Scheme.Hom.mem_preimage, ← Stacks.RatioPullback.nvOpen_pullbackGlobalSections,
    ← restrictedSection_eval_top] at hnv
  apply hnv
  have h1 := TopCat.Presheaf.germ_stalkSpecializes_apply
    ((Scheme.Modules.pullback T.subschemeι).obj M).presheaf (Opens.mem_top w) hηw
    ((restrictedSection T M s).eval (op ⊤))
  have h0' : (ConcreteCategory.hom (((Scheme.Modules.pullback T.subschemeι).obj M).presheaf.germ
      ⊤ w (Opens.mem_top w))) ((restrictedSection T M s).eval (op ⊤)) = 0 := h0
  rw [h0', map_zero] at h1
  show (ConcreteCategory.hom (((Scheme.Modules.pullback T.subschemeι).obj M).presheaf.germ
      ⊤ η.1 (Opens.mem_top _))) ((restrictedSection T M s).eval (op ⊤)) ∈ _
  rw [← h1]
  exact Submodule.zero_mem _

/-- **Injectivity off `Z`.** Let `W ⊆ X` be the closed subscheme cut out by `T`, whose trace on
the complement of the support of `I` is smooth over `k`, and let `s` be a global section of `M`
not vanishing at the generic points of `W` off the support of `I`. At every point of the zero
scheme of `s|_W` lying off the support of `I`, multiplication by `s|_W` is injective on
stalks. -/
theorem injective_restrictedSection_of_notMem_support {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (I T : X.IdealSheafData) (M : X.Modules)
    [IsInvertibleModule X M] (s : Γ(M, ⊤)) (hT : SmoothOffSupport f I T)
    (hgen : NonvanishingAtGenericOff I T M s)
    (ξ : (cutIdeal T.subschemeι M (restrictedSection T M s)).subscheme)
    (hξ : T.subschemeι ((cutIdeal T.subschemeι M (restrictedSection T M s)).subschemeι ξ) ∉
      I.support) :
    Function.Injective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        ((cutIdeal T.subschemeι M (restrictedSection T M s)).subschemeι ξ)).map
        ((Scheme.Modules.toPresheaf T.subscheme).map
          (((Scheme.Modules.pullback T.subschemeι).obj M).unitHomEquiv.symm
            (restrictedSection T M s))))) := by
  have := isDomain_stalk_of_smoothOffSupport f I T hT _ hξ
  exact Stacks.Chow.injective_stalkFunctor_map_unitHomEquiv_symm_of_isDomain _ _ _
    (germ_restrictedSection_ne_zero I T M s hgen _ hξ)

/-- **Cutting a local ring of dimension `d + 1` by `d` of `d + 1` generators of its maximal
ideal.** Let `A` be a Noetherian local ring of dimension `d + 1` whose maximal ideal is generated
by `c_0, …, c_d`, and let `φ : A → R` be a surjection onto a local ring with kernel
`(c_0, …, c_{d-1})`. Then `R` has dimension at least `1` and its maximal ideal is generated by
`φ(c_d)`, so `R` is a regular local ring of dimension one, in particular a domain, and
`φ(c_d) ≠ 0`. -/
theorem isDomain_and_ne_zero_of_ker_eq_span {A R : Type*} [CommRing A] [CommRing R]
    [IsLocalRing A] [IsLocalRing R] [IsNoetherianRing A] (φ : A →+* R)
    (hφ : Function.Surjective φ) {d : ℕ} (c : Fin (d + 1) → A)
    (hdim : ringKrullDim A = (d + 1 : ℕ)) (hmax : Ideal.span (Set.range c) = maximalIdeal A)
    (hker : RingHom.ker φ = Ideal.span (Set.range fun i : Fin d => c i.castSucc)) :
    IsDomain R ∧ φ (c (Fin.last d)) ≠ 0 := by
  have : IsNoetherianRing R := isNoetherianRing_of_surjective A R φ hφ
  have hmR : maximalIdeal R = Ideal.span {φ (c (Fin.last d))} := by
    rw [← map_maximalIdeal_of_surjective φ hφ, ← hmax, Ideal.map_span]
    refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
    · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      induction i using Fin.lastCases with
      | last => exact Ideal.subset_span rfl
      | cast i =>
        have : c i.castSucc ∈ RingHom.ker φ := hker ▸ Ideal.subset_span ⟨i, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker.1 this]
        exact Ideal.zero_mem _
    · rw [Set.singleton_subset_iff]
      exact Ideal.subset_span ⟨c (Fin.last d), ⟨Fin.last d, rfl⟩, rfl⟩
  have hJ : RingHom.ker φ ≤ Ring.jacobson A := by
    rw [← Ideal.jacobson_bot, IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top, ← hmax, hker]
    exact Ideal.span_mono (Set.range_comp_subset_range _ _)
  have h1 := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (RingHom.ker φ) hJ
  rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hφ), hdim] at h1
  have h2 : (RingHom.ker φ).spanFinrank ≤ d := by
    rw [hker]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_
    rw [← Set.image_univ]
    exact (Set.ncard_image_le Set.finite_univ).trans (by simp)
  have hdimR : (1 : WithBot ℕ∞) ≤ ringKrullDim R := by
    obtain ⟨e, he⟩ : ∃ e : ℕ∞, (e : WithBot ℕ∞) = ringKrullDim R :=
      WithBot.ne_bot_iff_exists.1 (ne_bot_of_le_ne_bot WithBot.zero_ne_bot
        ringKrullDim_nonneg_of_nontrivial)
    rw [← he] at h1 ⊢
    induction e using ENat.recTopCoe with
    | top => exact le_top
    | coe n =>
      have h4 : d + 1 ≤ n + (RingHom.ker φ).spanFinrank := by exact_mod_cast h1
      exact_mod_cast (show 1 ≤ n by omega)
  have hreg : IsRegularLocalRing R := by
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (le_trans ?_ hdimR)
    rw [hmR]
    have := Submodule.spanFinrank_span_le_ncard_of_finite (R := R)
      (Set.finite_singleton (φ (c (Fin.last d))))
    rw [Set.ncard_singleton] at this
    exact_mod_cast this
  refine ⟨IsRegularLocalRing.isDomain R, fun h0 => ?_⟩
  rw [h0, Set.singleton_zero, Ideal.span_zero] at hmR
  have h6 := ringKrullDim_le_spanFinrank_maximalIdeal R
  rw [hmR, Submodule.spanFinrank_bot] at h6
  have := hdimR.trans h6
  norm_num at this

/-- If the germ of a global section `t` of an invertible module `L` vanishes at `y`, then so does
the stalk at `y` of the ideal of the zero scheme of `t`. -/
theorem stalk_zeroScheme_eq_bot_of_germ_eq_zero {Y : Scheme.{u}} (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (t : Γ(L, ⊤)) (y : Y) (h : (L.presheaf.Γgerm y).hom t = 0) :
    AlgebraicGeometry.IdealSheafData.stalk (Stacks.Divisors.zeroScheme Y L t) y = ⊥ := by
  obtain ⟨U, hyU, e, hβ⟩ := Stacks.Chow.exists_affineOpen_linearEquiv_isStalkBasis L y
  obtain ⟨a, ha⟩ : ∃ a, e (L.presheaf.map (homOfLE le_top).op t) = a := ⟨_, rfl⟩
  rw [Stacks.Divisors.stalk_zeroScheme_eq_span_germ L t U e a ha y hyU,
    Ideal.span_singleton_eq_bot]
  have hres : L.presheaf.map (homOfLE (le_top : (U : Y.Opens) ≤ ⊤)).op t = a • e.symm 1 := by
    rw [← ha]
    conv_lhs => rw [← e.symm_apply_apply (L.presheaf.map (homOfLE le_top).op t)]
    simpa using e.symm.map_smul (e (L.presheaf.map (homOfLE le_top).op t)) (1 : Γ(Y, U.1))
  have h2 : (L.presheaf.Γgerm y).hom t =
      (Y.presheaf.germ U.1 y hyU).hom a • L.presheaf.germ U.1 y hyU (e.symm 1) := by
    rw [← TopCat.Presheaf.Γgerm_res_apply (i := homOfLE (le_top : (U : Y.Opens) ≤ ⊤))
      L.presheaf y hyU t, hres]
    exact Stacks.ModuleStalk.germ_smul L y U.1 hyU _ _
  rw [h] at h2
  exact hβ.1 (h2.symm.trans (zero_smul _ _).symm)

/-- On an affine open `U ∋ y` trivializing `L` by `e`, the stalk at `y` of the ideal of the
intersection of the zero schemes of a family of global sections `t_i` is generated by the germs
of their local equations `e(t_i|_U)`. -/
theorem stalk_familyCut_eq_span {X : Scheme.{u}} (M : X.Modules) [IsInvertibleModule X M]
    {ι : Type*} (t : ι → Γ(M, ⊤)) (y : X) (U : X.affineOpens) (hyU : y ∈ U.1)
    (e : Γ(M, U.1) ≃ₗ[Γ(X, U.1)] Γ(X, U.1)) :
    AlgebraicGeometry.IdealSheafData.stalk (familyCut M t) y = Ideal.span (Set.range fun i =>
      (X.presheaf.germ U.1 y hyU).hom (e (M.presheaf.map (homOfLE le_top).op (t i)))) := by
  rw [familyCut, AlgebraicGeometry.IdealSheafData.stalk_iSup]
  simp only [fun i => Stacks.Divisors.stalk_zeroScheme_eq_span_germ M (t i) U e _ rfl y hyU]
  rw [Submodule.iSup_span, Set.iUnion_singleton_eq_range]

/-- **The local ring of `H_1 ∩ ⋯ ∩ H_d` at a point over `x`.** If `O_{X,x}` has dimension
`d + 1` and the zero schemes of `s_0, …, s_d` meet in the reduced point `x` (the stalk of their
ideal at `x` is `𝔪_x`), then at every point `w` of the intersection `W` of the first `d` zero
schemes lying over `x`, the local ring `O_{W,w}` is a domain and the germ of `s_d|_W` at `w` is
nonzero. -/
theorem isDomain_and_germ_ne_zero_at_point {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) [IsInvertibleModule X M] {d : ℕ} (s : Fin (d + 1) → Γ(M, ⊤))
    (w : (familyCut M (prefixFamily s d (Nat.le_succ d))).subscheme)
    (hdim : ringKrullDim (X.presheaf.stalk
      ((familyCut M (prefixFamily s d (Nat.le_succ d))).subschemeι w)) = (d + 1 : ℕ))
    (hgen : AlgebraicGeometry.IdealSheafData.stalk (familyCut M s)
        ((familyCut M (prefixFamily s d (Nat.le_succ d))).subschemeι w) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk
        ((familyCut M (prefixFamily s d (Nat.le_succ d))).subschemeι w))) :
    IsDomain ((familyCut M (prefixFamily s d (Nat.le_succ d))).subscheme.presheaf.stalk w) ∧
      (((Scheme.Modules.pullback (familyCut M (prefixFamily s d (Nat.le_succ d))).subschemeι).obj
        M).presheaf.Γgerm w).hom
        ((restrictedSection (familyCut M (prefixFamily s d (Nat.le_succ d))) M
          (s (Fin.last d))).eval (op ⊤)) ≠ 0 := by
  obtain ⟨U, hxU, e, -⟩ := Stacks.Chow.exists_affineOpen_linearEquiv_isStalkBasis M
    ((familyCut M (prefixFamily s d (Nat.le_succ d))).subschemeι w)
  have hmax := (stalk_familyCut_eq_span M s _ U hxU e).symm.trans hgen
  have hker := (AlgebraicGeometry.IdealSheafData.ker_stalkMap_subschemeι_eq_stalk _ w).trans
    (stalk_familyCut_eq_span M (prefixFamily s d (Nat.le_succ d)) _ U hxU e)
  obtain ⟨hdom, hne⟩ := isDomain_and_ne_zero_of_ker_eq_span
    ((familyCut M (prefixFamily s d (Nat.le_succ d))).subschemeι.stalkMap w).hom
    ((familyCut M (prefixFamily s d (Nat.le_succ d))).subschemeι.stalkMap_surjective w) _ hdim
    hmax hker
  refine ⟨hdom, fun h0 => hne ?_⟩
  have hbot := stalk_zeroScheme_eq_bot_of_germ_eq_zero _ _ _ h0
  rwa [restrictedSection_eval_top, Stacks.Divisors.zeroScheme_pullback,
    AlgebraicGeometry.IdealSheafData.stalk_comap,
    Stacks.Divisors.stalk_zeroScheme_eq_span_germ M _ U e _ rfl _ hxU, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_eq_bot] at hbot

/-- **Injectivity at the point.** Let `O_{X,x}` be a local ring of dimension `d + 1` at which the
zero schemes of `s_0, …, s_d` meet in the reduced point `x`, let `W` be the intersection of the
zero schemes of `s_0, …, s_{d-1}`, and let `ξ` be a point of the zero scheme of `s_d|_W` lying
over `x`. Then multiplication by `s_d|_W` is injective on stalks at `ξ`. -/
theorem injective_restrictedSection_at_point {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) [IsInvertibleModule X M] (x : X) {d : ℕ} (s : Fin (d + 1) → Γ(M, ⊤))
    (hdim : ringKrullDim (X.presheaf.stalk x) = (d + 1 : ℕ))
    (hgen : AlgebraicGeometry.IdealSheafData.stalk (familyCut M s) x =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (ξ : (cutIdeal (familyCut M (prefixFamily s d (Nat.le_succ d))).subschemeι M
      (restrictedSection (familyCut M (prefixFamily s d (Nat.le_succ d))) M
        (s (Fin.last d)))).subscheme)
    (hξ : (familyCut M (prefixFamily s d (Nat.le_succ d))).subschemeι
      ((cutIdeal (familyCut M (prefixFamily s d (Nat.le_succ d))).subschemeι M
        (restrictedSection (familyCut M (prefixFamily s d (Nat.le_succ d))) M
          (s (Fin.last d)))).subschemeι ξ) = x) :
    Function.Injective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        ((cutIdeal (familyCut M (prefixFamily s d (Nat.le_succ d))).subschemeι M
          (restrictedSection (familyCut M (prefixFamily s d (Nat.le_succ d))) M
            (s (Fin.last d)))).subschemeι ξ)).map
        ((Scheme.Modules.toPresheaf
            (familyCut M (prefixFamily s d (Nat.le_succ d))).subscheme).map
          (((Scheme.Modules.pullback
              (familyCut M (prefixFamily s d (Nat.le_succ d))).subschemeι).obj M).unitHomEquiv.symm
            (restrictedSection (familyCut M (prefixFamily s d (Nat.le_succ d))) M
              (s (Fin.last d))))))) := by
  subst hξ
  obtain ⟨hdom, hne⟩ := isDomain_and_germ_ne_zero_at_point M s _ hdim hgen
  exact Stacks.Chow.injective_stalkFunctor_map_unitHomEquiv_symm_of_isDomain _ _ _ hne

end Stacks.Chow.BertiniChain

end
