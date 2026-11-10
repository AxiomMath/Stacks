module

public import StacksFrontier.AlgebraicGeometry.ProjKoszulComplex.TwistStalk
public import StacksFrontier.AlgebraicGeometry.ProjTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpacePseudoCoherence.TelescopeSequence
public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseTensorCompatibility
public import StacksFrontier.AlgebraicGeometry.Divisors.ProjClosedSubschemeKernel

/-!
# The pushforward of the structure sheaf of a standard open of `Proj` as a colimit of twists

Let `𝒮` be a graded ring and `x` an element of degree one. On `Proj 𝒮` the sequence

`𝒪 --x--> 𝒪(1) --x--> 𝒪(2) --x--> ⋯`

has colimit `j_*𝒪_{D₊(x)}`, where `j : D₊(x) ⟶ Proj 𝒮` is the inclusion and the map from `𝒪(k)` is
division by `x ^ k` after restriction to `D₊(x)` (the trivialization of [Stacks, Tag 01MS]). The
comparison is checked on stalks: every section of `j_*𝒪_{D₊(x)}` over a standard open `D₊(h)` is
`s / x ^ N` for a section `s` of `𝒪(N)` over `D₊(h)`, and a section of `𝒪(k)` whose quotient by
`x ^ k` vanishes is killed by a power of `x` — both read off the identification of the sections of
the twisting sheaves over standard opens with degree-zero localizations ([Stacks, Tag 01M6]).
Consequently the telescope

`0 ⟶ ⨁ₖ 𝒪(k) --(1 - x)--> ⨁ₖ 𝒪(k) ⟶ j_*𝒪_{D₊(x)} ⟶ 0`

is a short exact sequence of sheaves of modules on `Proj 𝒮`.

## Main results

* `AlgebraicGeometry.ProjectiveSpacePseudoCoherence.ProjTelescope.isColimitCocone`: the colimit.
* `AlgebraicGeometry.ProjectiveSpacePseudoCoherence.ProjTelescope.shortExact_telescope`: the short
  exact telescope.

## References

* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj Stacks.AlgebraicGeometry.ProjTrivialization

universe u w

namespace AlgebraicGeometry.ProjectiveSpacePseudoCoherence.ProjTelescope

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] {x : S} (hx : x ∈ 𝒮 1)

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
/-- The ideal underlying a point of `ProjectiveSpectrum.top 𝒮` is prime. -/
local instance (y : ProjectiveSpectrum.top 𝒮) : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
/-- The ideal underlying a point of `Proj 𝒮` is prime. -/
local instance (y : AlgebraicGeometry.Proj 𝒮) : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime

/-- The standard open `D₊(x)` of `Proj 𝒮`, as an open of the scheme. -/
abbrev U₀ : (AlgebraicGeometry.Proj 𝒮).Opens := AlgebraicGeometry.Proj.basicOpen 𝒮 x

/-- The image in `Proj 𝒮` of an open of `D₊(x)` is contained in `D₊(x)`. -/
theorem image_le (W : (U₀ (x := x) 𝒮).toScheme.Opens) :
    ((U₀ (x := x) 𝒮).ι ''ᵁ W : (AlgebraicGeometry.Proj 𝒮).Opens) ≤
      ProjectiveSpectrum.basicOpen 𝒮 x :=
  (U₀ (x := x) 𝒮).ι_image_le W

/-- The twist `𝒪(k)` of `Proj 𝒮`, spelled with the degree `k * deg x` of Tag 01MS. -/
abbrev tw (k : ℤ) : SheafOfModules.{u} (AlgebraicGeometry.Proj 𝒮).ringCatSheaf :=
  twistingSheaf 𝒮 (k * ((1 : ℕ) : ℤ))

/-- The pushforward of the structure sheaf of `D₊(x)`. -/
abbrev jO : SheafOfModules.{u} (AlgebraicGeometry.Proj 𝒮).ringCatSheaf :=
  (Scheme.Modules.pushforward (U₀ (x := x) 𝒮).ι).obj
    (SheafOfModules.unit (U₀ (x := x) 𝒮).toScheme.ringCatSheaf)

/-- Restriction of a section of `𝒪(k)` over `V` to `V ∩ D₊(x)`, divided by `x ^ k`. -/
def toLocAddHom (k : ℤ) (V : (AlgebraicGeometry.Proj 𝒮).Opens) :
    (tw 𝒮 k).val.obj (op V) →+ (jO (x := x) 𝒮).val.obj (op V) where
  toFun s := ((trivializingEquiv 𝒮 hx k (image_le 𝒮 ((U₀ (x := x) 𝒮).ι ⁻¹ᵁ V))).symm
    ((tw 𝒮 k).val.map (homOfLE ((U₀ (x := x) 𝒮).ι.image_preimage_le V)).op s) :
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj
        (op ((U₀ (x := x) 𝒮).ι ''ᵁ ((U₀ (x := x) 𝒮).ι ⁻¹ᵁ V))))
  map_zero' := by simp only [map_zero]; exact LinearEquiv.map_zero _
  map_add' a b := by simp only [map_add]; exact LinearEquiv.map_add _ _ _

/-- The sheaf map `𝒪(k) ⟶ j_*𝒪_{D₊(x)}`, dividing by `x ^ k` after restriction. -/
def toLoc (k : ℤ) : tw 𝒮 k ⟶ jO (x := x) 𝒮 where
  val := PresheafOfModules.homMk
    { app := fun V => AddCommGrpCat.ofHom (toLocAddHom 𝒮 hx k V.unop)
      naturality := by
        intro V V' i
        ext s
        apply Subtype.ext
        funext y
        refine eq_of_val_mul_eq 𝒮 k (image_le 𝒮 ((U₀ (x := x) 𝒮).ι ⁻¹ᵁ V'.unop)) y ?_
        have h1 := val_trivializingEquiv_symm_mul 𝒮 hx k
          (image_le 𝒮 ((U₀ (x := x) 𝒮).ι ⁻¹ᵁ V'.unop))
          ((tw 𝒮 k).val.map (homOfLE ((U₀ (x := x) 𝒮).ι.image_preimage_le V'.unop)).op
            ((tw 𝒮 k).val.presheaf.map i s)) y
        have h2 := val_trivializingEquiv_symm_mul 𝒮 hx k
          (image_le 𝒮 ((U₀ (x := x) 𝒮).ι ⁻¹ᵁ V.unop))
          ((tw 𝒮 k).val.map (homOfLE ((U₀ (x := x) 𝒮).ι.image_preimage_le V.unop)).op s)
          ⟨y.1, (U₀ (x := x) 𝒮).ι.image_mono
            ((Opens.map (U₀ (x := x) 𝒮).ι.base).map i.unop).le y.2⟩
        exact h1.trans h2.symm }
    (fun V r s => by
      change (trivializingEquiv 𝒮 hx k _).symm ((tw 𝒮 k).val.map _ (r • s)) = _
      rw [PresheafOfModules.map_smul]
      exact ((trivializingEquiv 𝒮 hx k (image_le 𝒮 ((U₀ (x := x) 𝒮).ι ⁻¹ᵁ V.unop))).symm.map_smul
        _ _).trans rfl)

/-- On sections over `V`, `toLoc` is `toLocAddHom`. -/
theorem toLoc_app_apply (k : ℤ) (V : (AlgebraicGeometry.Proj 𝒮).Opens)
    (s : (tw 𝒮 k).val.obj (op V)) :
    (toLoc 𝒮 hx k).val.app (op V) s = toLocAddHom 𝒮 hx k V s := rfl

/-- The defining property of `toLoc`: at a point of `V ∩ D₊(x)`, its value times `x ^ k` is the
value of the section. -/
theorem val_toLoc_mul (k : ℤ) (V : (AlgebraicGeometry.Proj 𝒮).Opens)
    (s : (tw 𝒮 k).val.obj (op V)) (y : ((U₀ (x := x) 𝒮).ι ''ᵁ ((U₀ (x := x) 𝒮).ι ⁻¹ᵁ V) :
      (AlgebraicGeometry.Proj 𝒮).Opens)) :
    HomogeneousLocalization.val (((toLoc 𝒮 hx k).val.app (op V) s :
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj
          (op ((U₀ (x := x) 𝒮).ι ''ᵁ ((U₀ (x := x) 𝒮).ι ⁻¹ᵁ V)))).1 y) *
      trivializingFun 𝒮 k (image_le 𝒮 ((U₀ (x := x) 𝒮).ι ⁻¹ᵁ V)) y =
      s.1 ⟨y.1, (U₀ (x := x) 𝒮).ι.image_preimage_le V y.2⟩ :=
  val_trivializingEquiv_symm_mul 𝒮 hx k _ _ y

omit [GradedRing 𝒮] in
/-- Under `LocalizedModule P S ≃ Localization P`, the localization of multiplication by `a` is
multiplication by `a / 1`. -/
theorem localizedModule_map_mulLeft (P : Submonoid S) (a : S) (z : Localization P) :
    LocalizedModule.map P (LinearMap.mulLeft S a) z = Localization.mk a 1 * z := by
  induction z using Localization.induction_on with
  | H p =>
    obtain ⟨m, t⟩ := p
    change LocalizedModule.map P (LinearMap.mulLeft S a) (LocalizedModule.mk m t) = _
    rw [LocalizedModule.map_mk]
    change Localization.mk (a * m) t = _
    rw [Localization.mk_mul, one_mul]

/-- The trivializing function of degree `k + 1` is `x` times that of degree `k`. -/
theorem trivializingFun_succ (k : ℕ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 x) (y : W) :
    trivializingFun 𝒮 ((k : ℤ) + 1) hW y = Localization.mk x 1 * trivializingFun 𝒮 k hW y := by
  simp only [trivializingFun]
  rw [Localization.mk_mul]
  congr 1
  · rw [show ((k : ℤ) + 1).toNat = k + 1 by omega, show (k : ℤ).toNat = k by omega, pow_succ,
      mul_comm]
  · apply Subtype.ext
    simp [show (-(k : ℤ)).toNat = 0 by omega,
      show (-1 + -(k : ℤ)).toNat = 0 by omega]

/-- Multiplication by `x`, `𝒪(k) ⟶ 𝒪(k + 1)`, in the degree spelling of `tw`. -/
def mulX (k : ℤ) : tw 𝒮 k ⟶ tw 𝒮 (k + 1) :=
  twistMulLeftIntOf 𝒮 ⟨x, hx⟩ (k * ((1 : ℕ) : ℤ)) ((k + 1) * ((1 : ℕ) : ℤ)) (by push_cast; ring)

/-- Multiplication by `x` followed by division by `x ^ (k + 1)` is division by `x ^ k`. -/
theorem mulX_toLoc (k : ℕ) : mulX 𝒮 hx k ≫ toLoc 𝒮 hx ((k : ℤ) + 1) = toLoc 𝒮 hx k := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext s
  apply Subtype.ext
  funext y
  refine eq_of_val_mul_eq 𝒮 ((k : ℤ) + 1) (image_le 𝒮 ((U₀ (x := x) 𝒮).ι ⁻¹ᵁ V.unop)) y ?_
  have hL := val_toLoc_mul 𝒮 hx ((k : ℤ) + 1) V.unop ((mulX 𝒮 hx k).val.app V s) y
  have hR := val_toLoc_mul 𝒮 hx k V.unop s y
  refine hL.trans ?_
  change LocalizedModule.map _ (LinearMap.mulLeft S x) (s.1 _) = _
  rw [← hR, localizedModule_map_mulLeft, trivializingFun_succ 𝒮 k
    (image_le 𝒮 ((U₀ (x := x) 𝒮).ι ⁻¹ᵁ V.unop)) y]
  ring

/-! ### Small standard opens -/

/-- Inside any open neighbourhood of a point of `Proj 𝒮` there is a standard open neighbourhood
`D₊(f)` with `f` homogeneous of positive degree. -/
theorem exists_basicOpen_pos_le {V : Opens (ProjectiveSpectrum.top 𝒮)}
    {y : ProjectiveSpectrum.top 𝒮} (hy : y ∈ V) :
    ∃ (f : S) (d : ℕ), 0 < d ∧ f ∈ 𝒮 d ∧ y ∈ ProjectiveSpectrum.basicOpen 𝒮 f ∧
      ProjectiveSpectrum.basicOpen 𝒮 f ≤ V := by
  classical
  obtain ⟨t, ht⟩ := (ProjectiveSpectrum.isOpen_iff 𝒮 (V : Set (ProjectiveSpectrum 𝒮))).1 V.2
  have hyt : y ∉ ProjectiveSpectrum.zeroLocus 𝒮 t := by
    rw [← ht]; exact fun h => h hy
  rw [ProjectiveSpectrum.mem_zeroLocus, Set.not_subset] at hyt
  obtain ⟨a, hat, hay⟩ := hyt
  obtain ⟨i, hi⟩ : ∃ i, GradedRing.proj 𝒮 i a ∉ y.asHomogeneousIdeal := by
    by_contra h
    push Not at h
    exact hay (y.asHomogeneousIdeal.2.mem_iff.mpr fun i => h i)
  obtain ⟨n, g, hn, hg, hgy⟩ := Stacks.AlgebraicGeometry.ProjShared.exists_homogeneous_pos_notMem
    𝒮 y
  refine ⟨GradedRing.proj 𝒮 i a * g, i + n, by omega,
    SetLike.mul_mem_graded (SetLike.coe_mem _) hg, ?_, ?_⟩
  · rw [ProjectiveSpectrum.mem_basicOpen]
    exact fun h => (y.isPrime.mem_or_mem h).elim hi hgy
  · intro z hz
    have hz' : GradedRing.proj 𝒮 i a ∉ z.asHomogeneousIdeal := fun h =>
      hz (z.asHomogeneousIdeal.toIdeal.mul_mem_right _ h)
    have hza : z ∉ ProjectiveSpectrum.zeroLocus 𝒮 t := by
      rw [ProjectiveSpectrum.mem_zeroLocus]
      intro hsub
      exact hz' ((z.asHomogeneousIdeal.2.mem_iff.mp (hsub hat)) i)
    rw [← ht] at hza
    by_contra hzV
    exact hza hzV

/-- `exists_basicOpen_pos_le`, read on the scheme `Proj 𝒮`. -/
theorem exists_basicOpen_pos_le' {V : (AlgebraicGeometry.Proj 𝒮).Opens}
    {y : AlgebraicGeometry.Proj 𝒮} (hy : y ∈ V) :
    ∃ (f : S) (d : ℕ), 0 < d ∧ f ∈ 𝒮 d ∧ y ∈ AlgebraicGeometry.Proj.basicOpen 𝒮 f ∧
      AlgebraicGeometry.Proj.basicOpen 𝒮 f ≤ V :=
  exists_basicOpen_pos_le 𝒮 hy

/-! ### Sections over a standard open -/

/-- The part of `D₊(h)` lying in `D₊(x)` is `D₊(h x)`. -/
theorem preimage_basicOpen_eq (h : S) :
    (U₀ (x := x) 𝒮).ι ''ᵁ ((U₀ (x := x) 𝒮).ι ⁻¹ᵁ (AlgebraicGeometry.Proj.basicOpen 𝒮 h)) =
      AlgebraicGeometry.Proj.basicOpen 𝒮 (h * x) := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  ext y
  simp only [AlgebraicGeometry.Proj.basicOpen]
  rw [ProjectiveSpectrum.basicOpen_mul, inf_comm]
  rfl

omit [GradedRing 𝒮] in
/-- An element of degree `N (e + 1)` of `𝒮` has degree `N e` in the grading of the twist by
`N`. -/
theorem mem_twistGrading_of_mem {N e : ℕ} {a : S} (ha : a ∈ 𝒮 (N • (e + 1))) :
    a ∈ twistGrading 𝒮 ((N : ℤ) * ((1 : ℕ) : ℤ)) (N • (e : ℤ)) := by
  rw [twistGrading_apply]
  have : N • (e : ℤ) + (N : ℤ) * ((1 : ℕ) : ℤ) = ((N • (e + 1) : ℕ) : ℤ) := by
    simp; ring
  rw [this]
  exact mem_integerGrading_natCast 𝒮 ha

/-- **Every section of `j_*𝒪_{D₊(x)}` over a standard open `D₊(h)` comes from a twist**: it is
`s / x ^ N` for a section `s` of `𝒪(N)` over `D₊(h)`. -/
theorem exists_toLoc_eq {h : S} {e : ℕ} (hh : h ∈ 𝒮 e) (he : 0 < e)
    (t : (jO (x := x) 𝒮).val.obj (op (AlgebraicGeometry.Proj.basicOpen 𝒮 h))) :
    ∃ (N : ℕ) (s : (tw 𝒮 N).val.obj (op (AlgebraicGeometry.Proj.basicOpen 𝒮 h))),
      (toLoc 𝒮 hx N).val.app _ s = t := by
  have hhx : h * x ∈ 𝒮 (e + 1) := SetLike.mul_mem_graded hh hx
  have hle : AlgebraicGeometry.Proj.basicOpen 𝒮 (h * x) ≤
      (U₀ (x := x) 𝒮).ι ''ᵁ ((U₀ (x := x) 𝒮).ι ⁻¹ᵁ (AlgebraicGeometry.Proj.basicOpen 𝒮 h)) :=
    (preimage_basicOpen_eq 𝒮 h).ge
  let t'' := (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.map (homOfLE hle).op t
  obtain ⟨zz, hzz⟩ : ∃ zz, ProjectiveSpectrum.Proj.awayToSection 𝒮 (h * x) zz = t'' :=
    ⟨(AlgebraicGeometry.Proj.basicOpenIsoAway 𝒮 (h * x) hhx (by omega)).inv t'',
      congrArg (fun φ => φ t'')
        (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒮 (h * x) hhx (by omega)).inv_hom_id⟩
  obtain ⟨N, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒮 hhx zz
  refine ⟨N, ProjectiveSpectrum.Proj.degreeZeroToSection 𝒮 _ h
    (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 _ hh N a (mem_twistGrading_of_mem 𝒮 ha)), ?_⟩
  apply Subtype.ext
  funext y
  refine eq_of_val_mul_eq 𝒮 N (image_le 𝒮 _) y ?_
  refine (val_toLoc_mul 𝒮 hx N _ _ y).trans ?_
  have hy : y.1 ∈ AlgebraicGeometry.Proj.basicOpen 𝒮 (h * x) := by
    rw [← preimage_basicOpen_eq 𝒮 h]; exact y.2
  have ht : t.1 y = t''.1 ⟨y.1, hy⟩ := rfl
  rw [ht, ← hzz]
  refine (ProjectiveSpectrum.Proj.degreeZeroToSection_fraction 𝒮 _ hh N a
    (mem_twistGrading_of_mem 𝒮 ha) ⟨y.1, (ProjectiveSpectrum.basicOpen_mul_le_left 𝒮 h x) hy⟩).trans
    ?_
  have hval := ProjectiveSpectrum.Proj.awayToSection_apply 𝒮 (h * x)
    (HomogeneousLocalization.Away.mk 𝒮 hhx N a ha) ⟨y.1, hy⟩
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    ← Localization.mk_eq_mk'] at hval
  refine Eq.trans ?_ (congrArg (fun z => z * trivializingFun 𝒮 (N : ℤ) (image_le 𝒮 _) y)
    hval.symm)
  change Localization.mk a _ = _ * Localization.mk _ _
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, RingHom.id_apply,
    show (-(N : ℤ)).toNat = 0 by omega, show (N : ℤ).toNat = N by omega, pow_zero, mul_one]
  ring

/-- **A section of `𝒪(k)` over `D₊(h)` whose quotient by `x ^ k` vanishes is killed by a power of
`x`.** -/
theorem exists_pow_eq_zero_of_toLoc_eq_zero (k : ℕ) {h : S} {e : ℕ} (hh : h ∈ 𝒮 e) (he : 0 < e)
    (s : (tw 𝒮 k).val.obj (op (AlgebraicGeometry.Proj.basicOpen 𝒮 h)))
    (hs : (toLoc 𝒮 hx k).val.app _ s = 0) :
    ∃ N : ℕ, ∀ z : ProjectiveSpectrum.basicOpen 𝒮 h,
      LocalizedModule.map z.1.asHomogeneousIdeal.toIdeal.primeCompl
        (LinearMap.mulLeft S (x ^ N)) (s.1 z) = 0 := by
  have hhx : h * x ∈ 𝒮 (e + 1) := SetLike.mul_mem_graded hh hx
  obtain ⟨a, rfl⟩ := ProjectiveSpectrum.Proj.degreeZeroToSection_surjective 𝒮 _ hh he s
  obtain ⟨M, b, hb, rfl⟩ := Stacks.Veronese.exists_degreeZeroFraction 𝒮 _ h hh a
  -- the section vanishes on `D₊(h x)`
  have hzero : ∀ z : ProjectiveSpectrum.basicOpen 𝒮 (h * x),
      (LocalizedModule.mk b ⟨h ^ M, z.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem
        ((ProjectiveSpectrum.basicOpen_mul_le_left 𝒮 h x) z.2) M⟩ :
          LocalizedModule z.1.asHomogeneousIdeal.toIdeal.primeCompl S) = 0 := by
    intro z
    have hz : z.1 ∈ (U₀ (x := x) 𝒮).ι ''ᵁ ((U₀ (x := x) 𝒮).ι ⁻¹ᵁ
        (AlgebraicGeometry.Proj.basicOpen 𝒮 h)) := by
      rw [preimage_basicOpen_eq 𝒮 h]; exact z.2
    have h1 := val_toLoc_mul 𝒮 hx k (AlgebraicGeometry.Proj.basicOpen 𝒮 h)
      (ProjectiveSpectrum.Proj.degreeZeroToSection 𝒮 _ h
        (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 _ hh M b hb)) ⟨z.1, hz⟩
    rw [hs] at h1
    have h2 := ProjectiveSpectrum.Proj.degreeZeroToSection_fraction 𝒮 _ hh M b hb
      ⟨z.1, (ProjectiveSpectrum.basicOpen_mul_le_left 𝒮 h x) z.2⟩
    refine h2.symm.trans (h1.symm.trans ?_)
    change HomogeneousLocalization.val 0 * _ = 0
    rw [HomogeneousLocalization.val_zero, zero_mul]
  -- the fraction `b x ^ M / (h x) ^ M` is zero in the localization at `h x`
  have hb' : b * x ^ M ∈ twistGrading 𝒮 ((k : ℤ) * ((1 : ℕ) : ℤ)) (M • ((e + 1 : ℕ) : ℤ)) := by
    rw [twistGrading_apply] at hb ⊢
    have := ProjectiveSpectrum.Proj.mul_mem_integerGrading 𝒮 (SetLike.pow_mem_graded M hx) hb
    have heq : (((M • 1 : ℕ) : ℤ) + (M • (e : ℤ) + (k : ℤ) * ((1 : ℕ) : ℤ))) =
        M • (((e + 1 : ℕ) : ℤ)) + (k : ℤ) * ((1 : ℕ) : ℤ) := by
      simp only [nsmul_eq_mul, smul_eq_mul]; push_cast; ring
    rw [heq] at this
    have key : ∀ j j' : ℤ, j = j' → b * x ^ M ∈ integerGrading 𝒮 j' →
        b * x ^ M ∈ integerGrading 𝒮 j := fun j j' hj hm => hj ▸ hm
    refine key _ _ ?_ (by rw [mul_comm]; exact this)
    ring
  have hfr := ProjectiveSpectrum.Proj.degreeZeroToSection_injective 𝒮
    (twistGrading 𝒮 ((k : ℤ) * ((1 : ℕ) : ℤ))) hhx (by omega)
    (a₁ := ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 _ hhx M (b * x ^ M) hb') (a₂ := 0) (by
      apply Subtype.ext
      funext z
      rw [ProjectiveSpectrum.Proj.degreeZeroToSection_fraction, map_zero]
      refine Eq.trans ?_ (hzero z)
      rw [LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      simp only [one_smul, Submonoid.smul_def, smul_eq_mul]
      ring)
  have hv := congrArg Subtype.val hfr
  have hv' : (LocalizedModule.mk (b * x ^ M) ⟨(h * x) ^ M, ⟨M, rfl⟩⟩ :
      LocalizedModule.Away (R := S) (h * x) S) = LocalizedModule.mk 0 1 :=
    hv.trans (LocalizedModule.zero_mk 1).symm
  rw [LocalizedModule.mk_eq] at hv'
  have hv := hv'
  obtain ⟨⟨c, L, rfl⟩, hc⟩ := hv
  simp only [one_smul, smul_zero, Submonoid.smul_def, smul_eq_mul] at hc
  refine ⟨M + L, fun z => ?_⟩
  rw [ProjectiveSpectrum.Proj.degreeZeroToSection_fraction, LocalizedModule.map_mk,
    LinearMap.mulLeft_apply,
    ← LocalizedModule.zero_mk (1 : z.1.asHomogeneousIdeal.toIdeal.primeCompl),
    LocalizedModule.mk_eq]
  refine ⟨⟨h ^ L, z.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem z.2 L⟩, ?_⟩
  simp only [one_smul, smul_zero, Submonoid.smul_def, smul_eq_mul]
  calc h ^ L * (x ^ (M + L) * b) = (h * x) ^ L * (b * x ^ M) := by ring
    _ = 0 := hc

/-! ### The colimit -/

/-- The sequence `𝒪 ⟶ 𝒪(1) ⟶ 𝒪(2) ⟶ ⋯` of multiplications by `x`. -/
def seq : ℕ ⥤ SheafOfModules.{u} (AlgebraicGeometry.Proj 𝒮).ringCatSheaf :=
  Functor.ofSequence (X := fun k : ℕ => (tw 𝒮 (k : ℤ) : SheafOfModules.{u} _))
    fun k => mulX 𝒮 hx k

/-- The cocone of the sequence on `j_*𝒪_{D₊(x)}`. -/
def cocone : Cocone (seq 𝒮 hx) where
  pt := jO (x := x) 𝒮
  ι := NatTrans.ofSequence (fun k => toLoc 𝒮 hx (k : ℤ)) fun k => by
    have h1 : (seq 𝒮 hx).map (homOfLE (k.le_add_right 1)) = mulX 𝒮 hx k :=
      Functor.ofSequence_map_homOfLE_succ _ _
    rw [h1]
    refine (mulX_toLoc 𝒮 hx k).trans ?_
    exact (Category.comp_id _).symm

/-- The component of `cocone` at `k` is `toLoc` in degree `k`. -/
@[simp]
theorem cocone_ι_app (k : ℕ) : (cocone 𝒮 hx).ι.app k = toLoc 𝒮 hx (k : ℤ) := rfl

include hx in
/-- The transition maps of the sequence multiply by a power of `x`, at every point. -/
theorem seq_map_apply (n : ℕ) : ∀ (N : ℕ) (V : (AlgebraicGeometry.Proj 𝒮).Opens)
    (s : (tw 𝒮 (n : ℤ)).val.obj (op V)) (z : (V : Opens (ProjectiveSpectrum.top 𝒮))),
    (((seq 𝒮 hx).map (homOfLE (Nat.le_add_right n N))).val.app (op V) s).1 z =
      LocalizedModule.map z.1.asHomogeneousIdeal.toIdeal.primeCompl
        (LinearMap.mulLeft S (x ^ N)) (s.1 z)
  | 0, V, s, z => by
    rw [show (seq 𝒮 hx).map (homOfLE (Nat.le_add_right n 0)) = 𝟙 _ from (seq 𝒮 hx).map_id n,
      pow_zero]
    change s.1 z = _
    induction s.1 z using LocalizedModule.induction_on with
    | h m t => rw [LocalizedModule.map_mk, LinearMap.mulLeft_apply, one_mul]
  | N + 1, V, s, z => by
    have hc : homOfLE (Nat.le_add_right n (N + 1)) =
        homOfLE (Nat.le_add_right n N) ≫ homOfLE (Nat.le_add_right (n + N) 1) := rfl
    have h1 : (seq 𝒮 hx).map (homOfLE (Nat.le_add_right (n + N) 1)) = mulX 𝒮 hx (n + N : ℕ) :=
      Functor.ofSequence_map_homOfLE_succ _ _
    rw [hc, CategoryTheory.Functor.map_comp, h1]
    change LocalizedModule.map _ (LinearMap.mulLeft S x)
      ((((seq 𝒮 hx).map (homOfLE (Nat.le_add_right n N))).val.app (op V) s).1 z) = _
    rw [seq_map_apply n N V s z]
    induction s.1 z using LocalizedModule.induction_on with
    | h m t =>
      rw [LocalizedModule.map_mk, LocalizedModule.map_mk, LocalizedModule.map_mk,
        LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, pow_succ,
        mul_comm (x ^ N) x, mul_assoc]

open AlgebraicGeometry.SheafOfModules in
/-- The stalk map of a composite, applied to an element, is the composite of the stalk maps. -/
theorem stalkMap_comp_apply {M N P : SheafOfModules.{u} (AlgebraicGeometry.Proj 𝒮).ringCatSheaf}
    (f : M ⟶ N) (g : N ⟶ P) (y : AlgebraicGeometry.Proj 𝒮) (a) :
    (stalkMap (AlgebraicGeometry.Proj 𝒮).ringCatSheaf y (f ≫ g)).hom a =
      (stalkMap _ y g).hom ((stalkMap _ y f).hom a) := by
  rw [show stalkMap _ y (f ≫ g) = stalkMap _ y f ≫ stalkMap _ y g from
    (stalkFunctor (AlgebraicGeometry.Proj 𝒮).ringCatSheaf y).map_comp f g]
  rfl

open AlgebraicGeometry.SheafOfModules in
/-- **`j_*𝒪_{D₊(x)}` is the colimit of `𝒪 ⟶ 𝒪(1) ⟶ 𝒪(2) ⟶ ⋯`**, the transition maps being
multiplication by `x` and the maps to `j_*𝒪_{D₊(x)}` division by the powers of `x`. -/
noncomputable def isColimitCocone : IsColimit (cocone 𝒮 hx) := by
  let m := colimit.desc (seq 𝒮 hx) (cocone 𝒮 hx)
  suffices h : IsIso m from @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit _) h
  rw [isIso_iff_bijective_stalkMap]
  intro y
  have hm : ∀ k : ℕ, colimit.ι (seq 𝒮 hx) k ≫ m = toLoc 𝒮 hx (k : ℤ) := fun k =>
    colimit.ι_desc _ _
  constructor
  · rw [injective_iff_map_eq_zero]
    intro ζ hζ
    obtain ⟨k, w, rfl⟩ := exists_stalkMap_eq _ y (colimit.isColimit (seq 𝒮 hx)) ζ
    obtain ⟨W, hyW, s, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq ((seq 𝒮 hx).obj k).val.presheaf w
    obtain ⟨f, d, hd, hf, hyf, hfW⟩ := exists_basicOpen_pos_le' 𝒮 hyW
    rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hfW) y hyf s] at hζ ⊢
    set s' := ((seq 𝒮 hx).obj k).val.presheaf.map (homOfLE hfW).op s with hs'
    have h0 : (TopCat.Presheaf.germ (jO (x := x) 𝒮).val.presheaf _ y hyf).hom
        ((toLoc 𝒮 hx (k : ℤ)).val.app _ s') =
        (TopCat.Presheaf.germ (jO (x := x) 𝒮).val.presheaf _ y hyf).hom 0 := by
      rw [map_zero, ← stalkMap_germ _ y (toLoc 𝒮 hx (k : ℤ)) _ hyf s']
      refine (congrArg (fun φ => (stalkMap _ y φ).hom
        ((TopCat.Presheaf.germ ((seq 𝒮 hx).obj k).val.presheaf _ y hyf).hom s')) (hm k)).symm.trans
        ?_
      refine (stalkMap_comp_apply 𝒮 _ _ y _).trans ?_
      exact hζ
    obtain ⟨W'', hyW'', i1, i2, heq⟩ := TopCat.Presheaf.germ_eq _ y hyf hyf _ _ h0
    obtain ⟨f', d', hd', hf', hyf', hf'W⟩ := exists_basicOpen_pos_le' 𝒮 hyW''
    let j1 : AlgebraicGeometry.Proj.basicOpen 𝒮 f' ⟶ AlgebraicGeometry.Proj.basicOpen 𝒮 f :=
      homOfLE hf'W ≫ i1
    set s'' := ((seq 𝒮 hx).obj k).val.presheaf.map j1.op s' with hs''
    have hz : (toLoc 𝒮 hx (k : ℤ)).val.app _ s'' = 0 := by
      have hnat := PresheafOfModules.naturality_apply (toLoc 𝒮 hx (k : ℤ)).val j1.op s'
      refine hnat.trans ?_
      change (jO (x := x) 𝒮).val.presheaf.map (homOfLE hf'W ≫ i1).op
        ((toLoc 𝒮 hx (k : ℤ)).val.app _ s') = 0
      have hcomp : (jO (x := x) 𝒮).val.presheaf.map (homOfLE hf'W ≫ i1).op =
          (jO (x := x) 𝒮).val.presheaf.map i1.op ≫
            (jO (x := x) 𝒮).val.presheaf.map (homOfLE hf'W).op := by
        rw [op_comp, CategoryTheory.Functor.map_comp]
      refine (congrArg (fun φ => φ.hom ((toLoc 𝒮 hx (k : ℤ)).val.app _ s')) hcomp).trans ?_
      change (jO (x := x) 𝒮).val.presheaf.map (homOfLE hf'W).op
        ((jO (x := x) 𝒮).val.presheaf.map i1.op ((toLoc 𝒮 hx (k : ℤ)).val.app _ s')) = 0
      rw [heq, map_zero, map_zero]
    obtain ⟨N, hN⟩ := exists_pow_eq_zero_of_toLoc_eq_zero 𝒮 hx k hf' hd' s'' hz
    have hs''0 : ((seq 𝒮 hx).map (homOfLE (Nat.le_add_right k N))).val.app _ s'' = 0 :=
      Subtype.ext (funext fun z => (seq_map_apply 𝒮 hx k N _ s'' z).trans (hN z))
    have hg : (TopCat.Presheaf.germ ((seq 𝒮 hx).obj k).val.presheaf _ y hyf).hom s' =
        (TopCat.Presheaf.germ ((seq 𝒮 hx).obj k).val.presheaf _ y hyf').hom s'' :=
      (TopCat.Presheaf.germ_res_apply _ j1 y hyf' s').symm
    rw [hg]
    have hw := colimit.w (seq 𝒮 hx) (homOfLE (Nat.le_add_right k N))
    refine (congrArg (fun φ => (stalkMap _ y φ).hom
      ((TopCat.Presheaf.germ ((seq 𝒮 hx).obj k).val.presheaf _ y hyf').hom s'')) hw).symm.trans ?_
    refine (stalkMap_comp_apply 𝒮 _ _ y _).trans ?_
    refine (congrArg (fun a => (stalkMap _ y (colimit.ι (seq 𝒮 hx) (k + N))).hom a)
      (stalkMap_germ _ y ((seq 𝒮 hx).map (homOfLE (Nat.le_add_right k N))) _ hyf' s'')).trans ?_
    rw [hs''0]
    exact (congrArg (fun a => (stalkMap _ y (colimit.ι (seq 𝒮 hx) (k + N))).hom a)
      (map_zero (TopCat.Presheaf.germ ((seq 𝒮 hx).obj (k + N)).val.presheaf _ y hyf').hom)).trans
      (map_zero _)
  · intro ζ
    obtain ⟨W, hyW, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq (jO (x := x) 𝒮).val.presheaf ζ
    obtain ⟨f, d, hd, hf, hyf, hfW⟩ := exists_basicOpen_pos_le' 𝒮 hyW
    obtain ⟨N, s, hs⟩ := exists_toLoc_eq 𝒮 hx hf hd
      ((jO (x := x) 𝒮).val.map (homOfLE hfW).op t)
    refine ⟨(stalkMap _ y (colimit.ι (seq 𝒮 hx) N)).hom
      ((TopCat.Presheaf.germ (tw 𝒮 (N : ℤ)).val.presheaf
        (AlgebraicGeometry.Proj.basicOpen 𝒮 f) y hyf).hom s), ?_⟩
    refine ((stalkMap_comp_apply 𝒮 _ _ y _).symm).trans ?_
    refine (congrArg (fun φ => (stalkMap _ y φ).hom
      ((TopCat.Presheaf.germ (tw 𝒮 (N : ℤ)).val.presheaf
        (AlgebraicGeometry.Proj.basicOpen 𝒮 f) y hyf).hom s)) (hm N)).trans ?_
    refine (stalkMap_germ _ y (toLoc 𝒮 hx (N : ℤ)) _ hyf s).trans ?_
    change (TopCat.Presheaf.germ (jO (x := x) 𝒮).val.presheaf _ y hyf).hom
      ((toLoc 𝒮 hx (N : ℤ)).val.app _ s) = _
    rw [hs]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- **The telescope `0 ⟶ ⨁ₖ 𝒪(k) ⟶ ⨁ₖ 𝒪(k) ⟶ j_*𝒪_{D₊(x)} ⟶ 0` on `Proj 𝒮` is short exact**, for a
degree-one element `x`. -/
theorem shortExact_telescope :
    (ShortComplex.mk (telescopeDiff (seq 𝒮 hx)) (telescopeπ (cocone 𝒮 hx))
      (telescopeDiff_desc (cocone 𝒮 hx))).ShortExact :=
  AlgebraicGeometry.SheafOfModules.shortExact_telescope (seq 𝒮 hx) (isColimitCocone 𝒮 hx)

end AlgebraicGeometry.ProjectiveSpacePseudoCoherence.ProjTelescope

end
