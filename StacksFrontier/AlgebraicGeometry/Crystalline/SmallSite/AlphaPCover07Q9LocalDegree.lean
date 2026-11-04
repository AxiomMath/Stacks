module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AlphaPCover07Q9Main

/-!
# [Stacks, Tag 07Q9] for an iterated `α_p`-cover of locally bounded degree

[Stacks, Lemma 60.26.3, Tag 07Q9] is stated for an iterated `α_p`-cover `f : X' ⟶ X` of constant
degree `q`.  Its proof is local on `X`: over each open `W` over which `f` is a chain of `n`
successive `α_p`-extensions the cone is killed by `p ^ n`.  So the same proof gives the following
variant, in which the degree is only locally constant: if around every point of `X` the
restriction of `f` has constant degree `p ^ n` for some `n ≤ D`, then the cone of
`Ru_{X/S, *}ℱ ⟶ f_*Ru_{X'/S, *}f_cris^*ℱ` has cohomology sheaves killed by `p ^ D`.

The point is that the length of a chain over a nonempty affine open `W` is determined by the
degree: the sections over `W` are free of rank `p ^ (length)` over `Γ(X, W)`, and two free
ranks of the sections of an affine morphism over affine opens through a common point agree
(`eq_of_hasFiniteBasis_app_localDegree07Q9`).  The chain opens whose chain has length at most `D`
then form a basis of the opens of `X` (`isBasis_isChainOpen_localDegree07Q9`), and the conclusion
is local over a basis.

## Main results

* `isBasis_isChainOpen_localDegree07Q9` — the chain opens of length at most `D` form a basis.
* `annihilation07Q9_of_chainConeAnnihilation_localDegree07Q9` — the reduction to them.
* `annihilation07Q9_of_isIteratedAlphaPCover_localDegree` — the cone is killed by `p ^ D`.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe w w' u

noncomputable section

namespace AlgebraicGeometry

/-- **Two free ranks of an affine morphism through a common point agree**: if the sections of
an affine morphism `f` over two affine opens `U` and `W` of the target containing `x` are free of
ranks `q` and `m`, then `q = m`.  Both ranks are the rank of the sections over an affine open
`V ∋ x` contained in `U ∩ W`, a free module over a nonzero ring. -/
theorem eq_of_hasFiniteBasis_app_localDegree07Q9 {X' X : Scheme.{u}} {f : X' ⟶ X}
    [IsAffineHom f] {U W : X.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) {x : X}
    (hxU : x ∈ U) (hxW : x ∈ W) {q m : ℕ} (hq : HasFiniteBasis (f.app U).hom q)
    (hm : HasFiniteBasis (f.app W).hom m) : q = m := by
  obtain ⟨V, hV, hxV, hVle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ U ⊓ W from ⟨hxU, hxW⟩)
  have : IsAffine V := hV
  have key : ∀ {W : X.Opens} {m : ℕ}, IsAffineOpen W → V ≤ W → HasFiniteBasis (f.app W).hom m →
      HasFiniteBasis (f ∣_ V).appTop.hom m := fun {W m} hW hVW hm => by
    have : IsAffine W := hW
    have : IsAffine (f ⁻¹ᵁ W) := hW.preimage f
    exact .of_isPullback_appTop (isPullback_morphismRestrict_homOfLE f hVW) m
      (hasFiniteBasis_morphismRestrict_of_app f W m hm)
  have : Nonempty (↑(⊤ : (V : Scheme.{u}).Opens)) := ⟨⟨⟨x, hxV⟩, trivial⟩⟩
  let := (f ∣_ V).appTop.hom.toAlgebra
  obtain ⟨b⟩ := key hU (hVle.trans inf_le_left) hq
  obtain ⟨b'⟩ := key hW (hVle.trans inf_le_right) hm
  simpa using (rank_eq_card_basis b).symm.trans (rank_eq_card_basis b')

/-- **A free rank of a restriction is a free rank of the morphism**: if the sections of `f ∣_ U`
over an open `V` of `U` are free of rank `n`, so are the sections of `f` over the image of `V`
in the target, which are the same ring map up to the identification of the two preimages. -/
theorem hasFiniteBasis_app_image_localDegree07Q9 {X' X : Scheme.{u}} (f : X' ⟶ X) (U : X.Opens)
    (V : U.toScheme.Opens) (n : ℕ) (h : HasFiniteBasis ((f ∣_ U).app V).hom n) :
    HasFiniteBasis (f.app (U.ι ''ᵁ V)).hom n := by
  refine hasFiniteBasis_of_iso _ ((f ∣_ U).app V).hom (RingEquiv.refl _)
    (X'.presheaf.mapIso
      (eqToIso (image_morphismRestrict_preimage f U V)).op).commRingCatIsoToRingEquiv ?_ n h
  ext r
  exact (congrArg (fun k => k.hom r) (morphismRestrict_app f U V)).symm

/-- **A local degree is the power of `p` given by the length of any chain**: if `f ∣_ U` has
constant degree `p ^ n`, then around each point of `U` there is an affine open of `X` inside `U`
over which the sections of `f` are free of rank `p ^ n`. -/
theorem exists_hasFiniteBasis_app_localDegree07Q9 {X' X : Scheme.{u}} {f : X' ⟶ X}
    {U : X.Opens} {q : ℕ} (hU : HasConstantDegree (f ∣_ U) q) {x : X} (hxU : x ∈ U) :
    ∃ U' : X.Opens, IsAffineOpen U' ∧ x ∈ U' ∧ U' ≤ U ∧ HasFiniteBasis (f.app U').hom q := by
  obtain ⟨V, hV, hyV, hfree, hrank⟩ := hU ⟨x, hxU⟩
  have hb : HasFiniteBasis ((f ∣_ U).app V).hom q := by
    have : IsAffine V := hV
    have : Nonempty V := ⟨⟨⟨x, hxU⟩, hyV⟩⟩
    let := ((f ∣_ U).app V).hom.toAlgebra
    exact nonempty_basis_fin_of_rank_eq hrank
  refine ⟨U.ι ''ᵁ V, hV.image_of_isOpenImmersion U.ι, ⟨⟨x, hxU⟩, hyV, rfl⟩, ?_,
    hasFiniteBasis_app_image_localDegree07Q9 f U V q hb⟩
  rintro _ ⟨y, -, rfl⟩
  exact y.2

end AlgebraicGeometry

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {T : GlobalCrystallineSituation.{u}} {X' : Scheme.{u}} {f : X' ⟶ T.X}

/-- **The chain opens of length at most `D` around a point.**  If around every point the
restriction of `f` has constant degree `p ^ n` for some `n ≤ D`, every neighbourhood `N` of every
point `x` contains an open `W ∋ x` over which `f` is a chain of `n ≤ D` successive
`α_p`-extensions. -/
theorem exists_isChainOpen_localDegree07Q9 (hf : IsIteratedAlphaPCover T.p f) {D : ℕ}
    (hD : ∀ x : T.X, ∃ U : T.X.Opens, x ∈ U ∧ ∃ n ≤ D, HasConstantDegree (f ∣_ U) (T.p ^ n))
    {N : T.X.Opens} {x : T.X} (hx : x ∈ N) :
    ∃ W : T.X.Opens, (∃ n ≤ D, IsChainOpen07Q9 T f n W) ∧ x ∈ W ∧ W ≤ N := by
  have hp : T.p.Prime := Fact.out
  have := isAffineHom_of_isIteratedAlphaPCover hf
  obtain ⟨U, hxU, n, hnD, hU⟩ := hD x
  obtain ⟨U', hU', hxU', -, hbU'⟩ := exists_hasFiniteBasis_app_localDegree07Q9 hU hxU
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := T.S.scheme.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (sourceToBase T x)) isOpen_univ
  have hxN : x ∈ N ⊓ U' ⊓ sourceToBase T ⁻¹ᵁ V := ⟨⟨hx, hxU'⟩, hxV⟩
  obtain ⟨W, hW, hW₂, hxW, hWN, m, ch, e, he⟩ := exists_isAffineOpen_alphaPChain hf hxN
  have hnm : n = m := Nat.pow_right_injective hp.two_le
    (eq_of_hasFiniteBasis_app_localDegree07Q9 hU' hW hxU' hxW hbU'
      (AlphaPChain.hasFiniteBasis_of_iso hp.ne_zero _ ch e he))
  exact ⟨W, ⟨m, hnm ▸ hnD, V, hV, hW, hWN.trans inf_le_right, hW₂, ch, e, he⟩, hxW,
    hWN.trans (inf_le_left.trans inf_le_left)⟩

/-- **The chain opens of length at most `D` form a basis of the opens of `X`**, as soon as around
every point the restriction of `f` has constant degree `p ^ n` for some `n ≤ D`. -/
theorem isBasis_isChainOpen_localDegree07Q9 (hf : IsIteratedAlphaPCover T.p f) {D : ℕ}
    (hD : ∀ x : T.X, ∃ U : T.X.Opens, x ∈ U ∧ ∃ n ≤ D, HasConstantDegree (f ∣_ U) (T.p ^ n)) :
    Opens.IsBasis {W : T.X.Opens | ∃ n ≤ D, IsChainOpen07Q9 T f n W} :=
  Opens.isBasis_iff_nbhd.mpr fun hx =>
    let ⟨W, hW, hxW, hWN⟩ := exists_isChainOpen_localDegree07Q9 hf hD hx
    ⟨W, hW, hxW, hWN⟩

/-- **Annihilation of a mapping cone by `p ^ n` gives annihilation by `p ^ D` for `n ≤ D`.** -/
theorem ChainConeAnnihilation.pow_le_localDegree07Q9
    {K L : CochainComplex AddCommGrpCat.{u + 1} ℕ} {φ : K ⟶ L} {p n D : ℕ}
    (h : ChainConeAnnihilation (p ^ n) φ) (hnD : n ≤ D) :
    ChainConeAnnihilation (p ^ D) φ := fun j => by
  rw [← Nat.sub_add_cancel hnD, pow_add, Nat.cast_mul, mul_smul, h j, smul_zero]

variable [HasDerivedCategory.{w} (Sheaf (smallTopology (overSituation T f)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology T) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology (overSituation T f)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology T) AddCommGrpCat.{u + 1})]

/-- **[Stacks, Tag 07Q9] for a locally bounded degree, reduced to the chain opens.**  If around
every point the restriction of `f` has constant degree `p ^ n` for some `n ≤ D`, and over every
open `W` over which `f` is a chain of `n` successive `α_p`-extensions the sections over `W` of the
lift of the unit to injective resolutions have mapping cone with cohomology killed by `p ^ n`, then
the cone of the comparison map of [Stacks, Tag 07Q9] has cohomology sheaves killed by `p ^ D`. -/
theorem annihilation07Q9_of_chainConeAnnihilation_localDegree07Q9
    (hf : IsIteratedAlphaPCover T.p f) {D : ℕ}
    (hD : ∀ x : T.X, ∃ U : T.X.Opens, x ∈ U ∧ ∃ n ≤ D, HasConstantDegree (f ∣_ U) (T.p ^ n))
    (F : ModuleSheaf T)
    (hper : ∀ (n : ℕ) (W : T.X.Opens), IsChainOpen07Q9 T f n W →
      ChainConeAnnihilation (T.p ^ n) (sectionsChainMap T W
        (crisResolutionMap (overSituation T f) T (𝟙 T.S) f (overSituation_compat T f) F
          (injectiveResolution _) (injectiveResolution _)))) :
    Annihilation07Q9 T (T.p ^ D)
      (moduleComparison07Q9 (overSituation T f) T (𝟙 T.S) f (overSituation_compat T f) F) :=
  annihilation07Q9_moduleComparison07Q9_of_isBasis (overSituation T f) T (𝟙 T.S) f
    (overSituation_compat T f) F (T.p ^ D) (isBasis_isChainOpen_localDegree07Q9 hf hD)
    fun W ⟨n, hnD, hW⟩ => (hper n W hW).pow_le_localDegree07Q9 hnD

variable (T f) in
/-- **[Stacks, Tag 07Q9] for an iterated `α_p`-cover whose degree is a locally bounded power of
`p`.**  Let `p` be a prime, `(S, I, γ)` a divided power scheme over `ℤ_(p)` with `p ∈ I`, and
`f : X' ⟶ X` an iterated `α_p`-cover of schemes over `S₀ = V(I)` such that around every point of
`X` the restriction of `f` has constant degree `p ^ n` for some `n ≤ D`.  Let `ℱ` be a crystal in
quasi-coherent modules on `Cris(X/S)`.  Then in the distinguished triangle
`Ru_{X/S, *}ℱ ⟶ f_*Ru_{X'/S, *}f_cris^*ℱ ⟶ E ⟶ Ru_{X/S, *}ℱ[1]` the object `E` has cohomology
sheaves killed by `p ^ D`.

This is the proof of [Stacks, Tag 07Q9] run with a locally constant instead of a constant degree:
the conclusion is local on `X`, and over an open over which `f` is a chain of `n ≤ D` successive
`α_p`-extensions the cone is killed by `p ^ n`.  The hypothesis `p ∈ I` of the source is not used
by the argument: what the `α_p`-extension step uses is that `p` is nilpotent on `X`, which is part
of the situation. -/
theorem annihilation07Q9_of_isIteratedAlphaPCover_localDegree
    (hpI : (T.p : Γ(T.S.scheme, ⊤)) ∈ T.S.ideal.obj (op ⊤))
    (hf : IsIteratedAlphaPCover T.p f) (D : ℕ)
    (hD : ∀ x : T.X, ∃ U : T.X.Opens, x ∈ U ∧ ∃ n ≤ D, HasConstantDegree (f ∣_ U) (T.p ^ n))
    (F : SheafOfModules.{u} (structureSheaf T)) (hF : IsQuasiCoherentCrystal T F) :
    Annihilation07Q9 T (T.p ^ D)
      (moduleComparison07Q9 (overSituation T f) T (𝟙 T.S) f (overSituation_compat T f)
        ((moduleULift T).obj F)) := by
  clear hpI
  exact annihilation07Q9_of_chainConeAnnihilation_localDegree07Q9 hf hD _ fun _ _ hW =>
    chainConeAnnihilation_isChainOpen07Q9 T f F hF hW

end Crystalline.GlobalCrystallineSituation.SmallSite
