module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.Basic
public import StacksFrontier.Topology.Sheaves.Modules.Exactness

/-!
# The quotient sequence of a flat pushforward at a stalk

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes, let `F` be an
`𝒪_X`-module which is flat over `S`, and let `r` be a section of `𝒪_S` over an open `V₀ ∋ s`
whose germ `a` at `s` is a nonzerodivisor. Let `m : F ⟶ F` be multiplication by the pullback
of `r`, so that `cokernel m` is the quotient `F / r F`. This file proves that the sequence

`(f_* F)_s --a--> (f_* F)_s ⟶ (f_* (F / r F))_s`

is exact at the middle term: an element of `(f_* F)_s` dies in `(f_* (F / r F))_s` exactly when
it is divisible by `a`. Together with `isSMulRegular_stalk_pushforward`, which is the injectivity
of the first map, this is the exactness statement used inside the proof of [Stacks, Tag 0EY0].

The two halves are very different. Divisibility always implies vanishing, because `m` composed
with the quotient map is zero; that direction needs no hypothesis on `f` at all. The converse is
the geometric content. Vanishing of the germ means that, after shrinking `V₀`, the section is
killed by the quotient map on `f⁻¹V₀`; exactness of a complex of sheaves of modules is detected
on stalks ([Stacks, Tag 01AG]), so the section becomes divisible by `r` on a neighbourhood of
every point of `f⁻¹V₀`. Those local quotients differ by sections annihilated by `r`, which
`exists_nbhd_germ_eq_zero` kills after a further shrinking of the neighbourhood of `s`, and the
corrected local quotients then glue. Quasi-compactness bounds the number of local quotients that
must be corrected simultaneously, and quasi-separatedness makes their pairwise overlaps
quasi-compact; both are used exactly as in `exists_resF_div`.

## Main definitions

There are no new definitions; `m` is supplied by the caller through its multiplication rule.

## Main results

* `exists_resF_div_of_local`: local divisibility by `r` on `f⁻¹V` assembles into divisibility
  over `f⁻¹V₃` for a smaller neighbourhood `V₃` of `s`.
* `exists_local_div_of_cokernel_app_eq_zero`: a section killed by the quotient map is locally
  divisible by `r`.
* `stalkMap_cokernel_eq_zero_of_smul`: the easy half, with no finiteness hypothesis on `f`.
* `exists_smul_eq_of_stalkMap_cokernel_eq_zero`: the converse.
* `stalkMap_cokernel_eq_zero_iff`: the two halves combined.

## Implementation notes

Flatness over the base is `AlgebraicGeometry.IsFlatOver`, and all the germ and restriction
notation is that of `StacksFrontier/AlgebraicGeometry/PushforwardRegularity/Basic.lean`.

The caller describes `m` by its action on sections rather than by a construction, as
`m.app W z = f.appLE V₀ W hW r • z`. This keeps the results usable both for a multiplication map
built on `X` and for one transported from the base, and it is what makes the identification of
the stalk map of `m` with scalar multiplication by the pullback of `r` a one-line computation.

Quasi-coherence of `F` is not assumed. The source states Tag 0EY0 for a quasi-coherent module,
but the argument here never uses it, exactly as in `isWeaklyRegular_stalk_pushforward'`.

The intermediate open `V₂` on which the quotient map annihilates the section must be affine,
because `exists_resF_div_of_local` passes it to `exists_nbhd_germ_eq_zero`, which needs the
stalks of `𝒪_S` over it to be localizations of its sections.

## References

* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.PushforwardRegularity

variable {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)

/-- Applying a morphism of `𝒪_X`-modules commutes with restriction of sections. -/
public lemma resF_app {G : X.Modules} (φ : F ⟶ G) {U U' : X.Opens} (h : U' ≤ U) (ξ : Γ(F, U)) :
    resF G h (φ.app U ξ) = φ.app U' (resF F h ξ) :=
  (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) ξ).symm

/-- Pulling back a section of `𝒪_S` to `W` can be computed after restricting it to a smaller
open of the base. -/
public lemma appLE_res {V V' : S.Opens} (hVV' : V' ≤ V) {W : X.Opens} (hW : W ≤ f ⁻¹ᵁ V')
    (r : Γ(S, V)) :
    f.appLE V' W hW (S.presheaf.map (homOfLE hVV').op r) =
      f.appLE V W (hW.trans fun _ hz => hVV' hz) r := by
  have h := ConcreteCategory.congr_hom (f.map_appLE hW (homOfLE hVV').op) r
  rwa [CommRingCat.comp_apply] at h

/-- The stalk map of a morphism of `𝒪_X`-modules sends a germ to the germ of the image. -/
public lemma stalkMap_germ {G : X.Modules} (φ : F ⟶ G) (y : X) {W : X.Opens} (hy : y ∈ W)
    (ξ : Γ(F, W)) :
    (TopCat.Presheaf.stalkFunctor Ab.{u} y).map φ.mapPresheaf
        (TopCat.Presheaf.germ F.val.presheaf W y hy ξ) =
      TopCat.Presheaf.germ G.val.presheaf W y hy (φ.app W ξ) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply W y hy φ.mapPresheaf ξ

/-- A morphism of `𝒪_X`-modules which acts on sections as multiplication by the pullback of
`r : Γ(S, V)` induces multiplication by the pullback of `r` on every stalk over `V`. -/
public lemma stalkMap_eq_smul (m : F ⟶ F) {V : S.Opens} (r : Γ(S, V))
    (hm : ∀ (W : X.Opens) (hW : W ≤ f ⁻¹ᵁ V) (z : Γ(F, W)),
      m.app W z = (f.appLE V W hW r) • z)
    {W : X.Opens} (hW : W ≤ f ⁻¹ᵁ V) {y : X} (hy : y ∈ W)
    (n : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :
    (TopCat.Presheaf.stalkFunctor Ab.{u} y).map m.mapPresheaf n =
      stalkPullback f V y (hW hy) r • n := by
  obtain ⟨U, hUW, hyU, η, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq F.val.presheaf n hy
  rw [stalkMap_germ F m y hyU η, hm U (hUW.trans hW) η,
    germ_smul_appLE f F (hUW.trans hW) r η y hyU]

/-- The quotient map kills the image of the multiplication map, on sections. -/
public lemma cokernelπ_app_app_eq_zero (m : F ⟶ F) (W : X.Opens) (ζ : Γ(F, W)) :
    (cokernel.π m).app W (m.app W ζ) = 0 := by
  calc (cokernel.π m).app W (m.app W ζ)
      = (m ≫ cokernel.π m).app W ζ := rfl
    _ = (0 : F ⟶ cokernel m).app W ζ := by rw [cokernel.condition m]
    _ = 0 := by simp

/-- Two local quotients of a section `ξ` of `F` over `f⁻¹V` by the pullback of `r`, defined on
affine opens, agree near every point of their overlap lying over a smaller neighbourhood of `s`. -/
public lemma exists_nbhd_germ_resF_sub_eq_zero [QuasiSeparated f]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) {s : S}
    {V : S.Opens} (hV : IsAffineOpen V) (hs : s ∈ V) (r : Γ(S, V))
    (ha : IsSMulRegular (S.presheaf.stalk s) (S.presheaf.germ V s hs r))
    (ξ : Γ(F, f ⁻¹ᵁ V)) {U₁ U₂ : X.Opens} (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    (hU₁V : U₁ ≤ f ⁻¹ᵁ V) (hU₂V : U₂ ≤ f ⁻¹ᵁ V) {ζ₁ : Γ(F, U₁)} {ζ₂ : Γ(F, U₂)}
    (h₁ : resF F hU₁V ξ = (f.appLE V U₁ hU₁V r) • ζ₁)
    (h₂ : resF F hU₂V ξ = (f.appLE V U₂ hU₂V r) • ζ₂) :
    ∃ (V'' : S.Opens) (_ : s ∈ V'') (_ : V'' ≤ V),
      ∀ (y : X) (hy : y ∈ U₁ ⊓ U₂), f.base y ∈ V'' →
        TopCat.Presheaf.germ F.val.presheaf (U₁ ⊓ U₂) y hy
          (resF F (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ζ₁ -
            resF F (inf_le_right : U₁ ⊓ U₂ ≤ U₂) ζ₂) = 0 := by
  have hW : (U₁ ⊓ U₂ : X.Opens) ≤ f ⁻¹ᵁ V := inf_le_left.trans hU₁V
  have hWc : IsCompact ((U₁ ⊓ U₂ : X.Opens) : Set X) := by
    rw [Opens.coe_inf]
    exact f.isQuasiSeparated_preimage hV.isQuasiSeparated _ _ hU₁V U₁.isOpen hU₁.isCompact hU₂V
      U₂.isOpen hU₂.isCompact
  refine exists_nbhd_germ_eq_zero f F hflat hV hs r ha hW hWc _ ?_
  have key : ∀ {U : X.Opens} (hUV : U ≤ f ⁻¹ᵁ V) (hle : U₁ ⊓ U₂ ≤ U) {ζ : Γ(F, U)},
      resF F hUV ξ = (f.appLE V U hUV r) • ζ →
        resF F hW ξ = (f.appLE V (U₁ ⊓ U₂) hW r) • resF F hle ζ := fun hUV hle _ h => by
    rw [← resF_resF F hUV hle ξ, h, resF_smul_appLE f F hUV hle r]
  rw [smul_sub, ← key hU₁V inf_le_left h₁, ← key hU₂V inf_le_right h₂, sub_self]

/-- **The assembly step, from local divisibility.** If `r : Γ(S, V)` has germ a nonzerodivisor
at `s` and a section `ξ` of `F` over `f⁻¹V` is divisible by the pullback of `r` near every point
of `f⁻¹V`, then it is divisible by the pullback of `r` over the preimage of a smaller
neighbourhood of `s`.

This is the second half of the proof of `exists_resF_div`, taking the local divisions as given
rather than producing them from a relation `t • ξ = r • η`. -/
public lemma exists_resF_div_of_local [QuasiCompact f] [QuasiSeparated f]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) {s : S}
    {V : S.Opens} (hV : IsAffineOpen V) (hs : s ∈ V) (r : Γ(S, V))
    (ha : IsSMulRegular (S.presheaf.stalk s) (S.presheaf.germ V s hs r))
    (ξ : Γ(F, f ⁻¹ᵁ V))
    (hloc : ∀ y : (f ⁻¹ᵁ V : X.Opens), ∃ (U : X.Opens) (_ : IsAffineOpen U)
      (_ : (y : X) ∈ U) (hUV : U ≤ f ⁻¹ᵁ V) (ζ : Γ(F, U)),
      resF F hUV ξ = (f.appLE V U hUV r) • ζ) :
    ∃ (V₃ : S.Opens) (_ : s ∈ V₃) (_ : V₃ ≤ V) (hpre : f ⁻¹ᵁ V₃ ≤ f ⁻¹ᵁ V)
      (ζ : Γ(F, f ⁻¹ᵁ V₃)),
      resF F hpre ξ = (f.appLE V (f ⁻¹ᵁ V₃) hpre r) • ζ := by
  have hVc : IsCompact ((f ⁻¹ᵁ V : X.Opens) : Set X) := f.isCompact_preimage hV.isCompact
  choose U hUaff hyU hUV ζ hζ using hloc
  obtain ⟨T, hT⟩ := hVc.elim_finite_subcover (fun y : (f ⁻¹ᵁ V : X.Opens) => (U y : Set X))
    (fun y => (U y).isOpen) fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hyU ⟨z, hz⟩⟩
  -- The pairwise discrepancies are annihilated by `r`, so they die over a smaller `V''`.
  choose V'' hsV'' hV''le hV''germ using fun i j : {x : (f ⁻¹ᵁ V : X.Opens) // x ∈ T} =>
    exists_nbhd_germ_resF_sub_eq_zero f F hflat hV hs r ha ξ (hUaff i.1) (hUaff j.1) (hUV i.1)
      (hUV j.1) (hζ i.1) (hζ j.1)
  set V₃ : S.Opens := V ⊓ ⨅ i : {x : (f ⁻¹ᵁ V : X.Opens) // x ∈ T},
    ⨅ j : {x : (f ⁻¹ᵁ V : X.Opens) // x ∈ T}, V'' i j
  have hsV₃ : s ∈ V₃ :=
    ⟨hs, by simpa only [SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter] using hsV''⟩
  have hV₃V : V₃ ≤ V := inf_le_left
  have hV₃V'' : ∀ i j, V₃ ≤ V'' i j := fun i j =>
    inf_le_right.trans ((iInf_le _ i).trans (iInf_le _ j))
  have hpre₃ : (f ⁻¹ᵁ V₃ : X.Opens) ≤ f ⁻¹ᵁ V := fun _ hz => hV₃V hz
  set C : {x : (f ⁻¹ᵁ V : X.Opens) // x ∈ T} → X.Opens := fun i => U i.1 ⊓ f ⁻¹ᵁ V₃
  have hCU : ∀ i, C i ≤ U i.1 := fun i => inf_le_left
  have hCpre : ∀ i, C i ≤ f ⁻¹ᵁ V₃ := fun i => inf_le_right
  have hcompat : ∀ i j, resF F (inf_le_left.trans (hCU i) : C i ⊓ C j ≤ U i.1) (ζ i.1) =
      resF F (inf_le_right.trans (hCU j) : C i ⊓ C j ≤ U j.1) (ζ j.1) :=
    fun i j => section_ext_F F _ _ fun y hy => by
    have hyij : y ∈ U i.1 ⊓ U j.1 := ⟨hCU i hy.1, hCU j hy.2⟩
    have h0 := hV''germ i j y hyij (hV₃V'' i j hy.1.2)
    rw [germF_sub F y hyij,
      germ_resF F (inf_le_left : U i.1 ⊓ U j.1 ≤ U i.1) (ζ i.1) y hyij,
      germ_resF F (inf_le_right : U i.1 ⊓ U j.1 ≤ U j.1) (ζ j.1) y hyij, sub_eq_zero] at h0
    rwa [germ_resF F (inf_le_left.trans (hCU i) : C i ⊓ C j ≤ U i.1) (ζ i.1) y hy,
      germ_resF F (inf_le_right.trans (hCU j) : C i ⊓ C j ≤ U j.1) (ζ j.1) y hy]
  obtain ⟨ζ₀, hζ₀⟩ := exists_glue F (f ⁻¹ᵁ V₃) C
    (fun z hz => by
      obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (hT (hV₃V hz))
      exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hzi, hz⟩)
    hCpre (fun i => resF F (hCU i) (ζ i.1)) fun i j =>
      (resF_resF F (hCU i) (inf_le_left : C i ⊓ C j ≤ C i) (ζ i.1)).trans ((hcompat i j).trans
        (resF_resF F (hCU j) (inf_le_right : C i ⊓ C j ≤ C j) (ζ j.1)).symm)
  refine ⟨V₃, hsV₃, hV₃V, hpre₃, ζ₀, ?_⟩
  refine section_ext_F F _ _ fun y hy => ?_
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (hT (hV₃V hy))
  set I : {x : (f ⁻¹ᵁ V : X.Opens) // x ∈ T} := ⟨i, hi⟩
  have hyC : y ∈ C I := ⟨hyi, hy⟩
  have e2 : resF F (hCU I) (resF F (hUV I.1) ξ) =
      (f.appLE V (C I) ((hCU I).trans (hUV I.1)) r) • resF F (hCU I) (ζ I.1) := by
    rw [hζ I.1, resF_smul_appLE f F (hUV I.1) (hCU I) r (ζ I.1)]
  have e3 : resF F (hCpre I) ((f.appLE V (f ⁻¹ᵁ V₃) hpre₃ r) • ζ₀) =
      (f.appLE V (C I) ((hCU I).trans (hUV I.1)) r) • resF F (hCU I) (ζ I.1) := by
    rw [resF_smul_appLE f F hpre₃ (hCpre I) r ζ₀, hζ₀ I]
  rw [← germ_resF F (hCpre I) (resF F hpre₃ ξ) y hyC,
    ← germ_resF F (hCpre I) ((f.appLE V (f ⁻¹ᵁ V₃) hpre₃ r) • ζ₀) y hyC,
    e3, resF_resF F hpre₃ (hCpre I) ξ, ← e2, resF_resF F (hUV I.1) (hCU I) ξ]

/-- **Local divisibility.** A section of `F` annihilated by the quotient map
`F ⟶ cokernel m` is, near every point, the pullback of `r` times a section.

Exactness of `F --m--> F ⟶ cokernel m` holds in the abelian category of sheaves of modules, and
is therefore visible on stalks; lifting the resulting stalk relation to a neighbourhood is
`exists_affine_resF_eq_sum` with a single coefficient. -/
public lemma exists_local_div_of_cokernel_app_eq_zero
    (m : F ⟶ F) {V : S.Opens} (r : Γ(S, V))
    (hm : ∀ (W : X.Opens) (hW : W ≤ f ⁻¹ᵁ V) (z : Γ(F, W)),
      m.app W z = (f.appLE V W hW r) • z)
    {W : X.Opens} (hW : W ≤ f ⁻¹ᵁ V) (ξ : Γ(F, W))
    (hξ : (cokernel.π m).app W ξ = 0) {y : X} (hy : y ∈ W) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : y ∈ U) (hUW : U ≤ W) (ζ : Γ(F, U)),
      resF F hUW ξ = (f.appLE V U (hUW.trans hW) r) • ζ := by
  have hex := (_root_.AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact
      X.ringCatSheaf (ShortComplex.cokernelSequence m)).mp
      (ShortComplex.cokernelSequence_exact m) y
  rw [ShortComplex.ab_exact_iff] at hex
  have hg : (TopCat.Presheaf.stalkFunctor Ab.{u} y).map (cokernel.π m).mapPresheaf
      (TopCat.Presheaf.germ F.val.presheaf W y hy ξ) = 0 := by
    rw [stalkMap_germ F (cokernel.π m) y hy ξ, hξ]
    exact germF_zero (cokernel m) y hy
  obtain ⟨n, hn⟩ := hex (TopCat.Presheaf.germ F.val.presheaf W y hy ξ) hg
  set n₀ : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y :=
    show TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y from n
  have hn' : stalkPullback f V y (hW hy) r • n₀ =
      TopCat.Presheaf.germ F.val.presheaf W y hy ξ :=
    (stalkMap_eq_smul f F m r hm hW hy n₀).symm.trans hn
  obtain ⟨U, hUaff, hyU, hUW, m', hm'⟩ := exists_affine_resF_eq_sum f F hW ξ y hy
    (fun _ : Fin 1 => r) (fun _ => n₀) (by simpa only [Fin.sum_univ_one] using hn'.symm)
  refine ⟨U, hUaff, hyU, hUW, m' 0, ?_⟩
  rw [hm', Fin.sum_univ_one]

/-- The stalk map of the pushforward of a morphism sends a pushforward germ to the pushforward
germ of the image. -/
public lemma stalkMap_pushforwardGerm {G : X.Modules} (φ : F ⟶ G) (s : S) (V : S.Opens)
    (hs : s ∈ V) (ξ : Γ(F, f ⁻¹ᵁ V)) :
    (TopCat.Presheaf.stalkFunctor Ab.{u} s).map ((Scheme.Modules.pushforward f).map φ).mapPresheaf
        (pushforwardGerm f F s V hs ξ) =
      pushforwardGerm f G s V hs (φ.app (f ⁻¹ᵁ V) ξ) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply V s hs
    ((Scheme.Modules.pushforward f).map φ).mapPresheaf ξ

/-- The pushforward germ of a section in the image of the multiplication map is killed by the
pushforward of the quotient map. -/
public lemma stalkMap_cokernel_pushforwardGerm_eq_zero (m : F ⟶ F) (s : S) (V : S.Opens)
    (hs : s ∈ V) (ζ : Γ(F, f ⁻¹ᵁ V)) :
    (TopCat.Presheaf.stalkFunctor Ab.{u} s).map
        ((Scheme.Modules.pushforward f).map (cokernel.π m)).mapPresheaf
        (pushforwardGerm f F s V hs (m.app (f ⁻¹ᵁ V) ζ)) = 0 := by
  rw [stalkMap_pushforwardGerm f F (cokernel.π m) s V hs,
    cokernelπ_app_app_eq_zero F m (f ⁻¹ᵁ V) ζ]
  exact pushforwardGerm_zero f (cokernel m) s V hs

/-- The germ of the pushforward of a restricted section is the germ of the original section. -/
private theorem pushforwardGerm_resF_eq (s : S) {V V' : S.Opens} (hVV' : V' ≤ V) (hs : s ∈ V')
    (hpre : f ⁻¹ᵁ V' ≤ f ⁻¹ᵁ V) {ξ : Γ(F, f ⁻¹ᵁ V)}
    {x : TopCat.Presheaf.stalk (C := Ab.{u}) ((Scheme.Modules.pushforward f).obj F).val.presheaf s}
    (h : pushforwardGerm f F s V (hVV' hs) ξ = x) :
    pushforwardGerm f F s V' hs (resF F hpre ξ) = x :=
  (pushforwardGerm_res f F s hVV' hs hpre ξ).trans h

/-- Pulling back the restriction of `r` to a smaller open `V'` is the restricted pullback of
`r`. -/
private theorem app_map_eq_appLE {V V' : S.Opens} (h : V' ≤ V) (r : Γ(S, V))
    (hpre : f ⁻¹ᵁ V' ≤ f ⁻¹ᵁ V) :
    f.app V' (S.presheaf.map (homOfLE h).op r) = f.appLE V (f ⁻¹ᵁ V') hpre r := by
  rw [← f.appLE_eq_app (U := V'), appLE_res f h le_rfl r]

/-- **The easy half.** An element of `(f_* F)_s` divisible by the germ of `r` is killed by the
stalk map of `f_*(F ⟶ F / r F)`. No finiteness hypothesis on `f` and no flatness is needed. -/
public lemma stalkMap_cokernel_eq_zero_of_smul (m : F ⟶ F) {V₀ : S.Opens} (r : Γ(S, V₀))
    (hm : ∀ (W : X.Opens) (hW : W ≤ f ⁻¹ᵁ V₀) (z : Γ(F, W)),
      m.app W z = (f.appLE V₀ W hW r) • z)
    (s : S) (hs₀ : s ∈ V₀)
    (z : TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pushforward f).obj F).val.presheaf s) :
    (TopCat.Presheaf.stalkFunctor Ab.{u} s).map
        ((Scheme.Modules.pushforward f).map (cokernel.π m)).mapPresheaf
        (S.presheaf.germ V₀ s hs₀ r • z) = 0 := by
  obtain ⟨V, -, hsV, ξ, hξ⟩ := exists_pushforwardGerm_eq f F s z
  set V₁ : S.Opens := V ⊓ V₀ with hV₁
  have hsV₁ : s ∈ V₁ := ⟨hsV, hs₀⟩
  have hV₁V : V₁ ≤ V := inf_le_left
  have hV₁V₀ : V₁ ≤ V₀ := inf_le_right
  have hpre : (f ⁻¹ᵁ V₁ : X.Opens) ≤ f ⁻¹ᵁ V := fun _ hz => hV₁V hz
  have hpre₀ : (f ⁻¹ᵁ V₁ : X.Opens) ≤ f ⁻¹ᵁ V₀ := fun _ hz => hV₁V₀ hz
  set ξ₁ : Γ(F, f ⁻¹ᵁ V₁) := resF F hpre ξ with hξ₁
  set r₁ : Γ(S, V₁) := S.presheaf.map (homOfLE hV₁V₀).op r with hr₁
  have hgz : pushforwardGerm f F s V₁ hsV₁ ξ₁ = z :=
    pushforwardGerm_resF_eq f F s hV₁V hsV₁ hpre hξ
  have hgr : S.presheaf.germ V₁ s hsV₁ r₁ = S.presheaf.germ V₀ s hs₀ r := by
    rw [hr₁, S.presheaf.germ_res_apply (homOfLE hV₁V₀) s hsV₁ r]
  have hcoef : (f.app V₁ r₁) • ξ₁ = m.app (f ⁻¹ᵁ V₁) ξ₁ := by
    rw [hm (f ⁻¹ᵁ V₁) hpre₀ ξ₁, hr₁, app_map_eq_appLE f hV₁V₀ r hpre₀]
  rw [← hgz, ← hgr, ← pushforwardGerm_smul f F s V₁ hsV₁ r₁ ξ₁, hcoef]
  exact stalkMap_cokernel_pushforwardGerm_eq_zero f F m s V₁ hsV₁ ξ₁

/-- **The geometric half.** For `f` quasi-compact and quasi-separated and `F` flat over `S`, an
element of `(f_* F)_s` killed by the stalk map of `f_*(F ⟶ F / r F)` is divisible by the germ of
`r` at `s`, provided that germ is a nonzerodivisor on `𝒪_{S,s}`. -/
public theorem exists_smul_eq_of_stalkMap_cokernel_eq_zero [QuasiCompact f] [QuasiSeparated f]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (m : F ⟶ F) {V₀ : S.Opens} (r : Γ(S, V₀))
    (hm : ∀ (W : X.Opens) (hW : W ≤ f ⁻¹ᵁ V₀) (z : Γ(F, W)),
      m.app W z = (f.appLE V₀ W hW r) • z)
    (s : S) (hs₀ : s ∈ V₀)
    (ha : IsSMulRegular (S.presheaf.stalk s) (S.presheaf.germ V₀ s hs₀ r))
    (x : TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pushforward f).obj F).val.presheaf s)
    (hx : (TopCat.Presheaf.stalkFunctor Ab.{u} s).map
      ((Scheme.Modules.pushforward f).map (cokernel.π m)).mapPresheaf x = 0) :
    ∃ z, x = S.presheaf.germ V₀ s hs₀ r • z := by
  -- Represent `x` on the preimage of an affine open inside `V₀`.
  obtain ⟨V, -, hsV, ξ, hξ⟩ := exists_pushforwardGerm_eq f F s x
  obtain ⟨_, ⟨V₁, hV₁aff, rfl⟩, hsV₁, hsub⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (show s ∈ (V ⊓ V₀ : S.Opens) from ⟨hsV, hs₀⟩) (V ⊓ V₀).isOpen
  have hV₁le : V₁ ≤ V ⊓ V₀ := hsub
  have hV₁V : V₁ ≤ V := hV₁le.trans inf_le_left
  have hV₁V₀ : V₁ ≤ V₀ := hV₁le.trans inf_le_right
  have hpre₁ : (f ⁻¹ᵁ V₁ : X.Opens) ≤ f ⁻¹ᵁ V := fun _ hz => hV₁V hz
  set ξ₁ : Γ(F, f ⁻¹ᵁ V₁) := resF F hpre₁ ξ with hξ₁
  set r₁ : Γ(S, V₁) := S.presheaf.map (homOfLE hV₁V₀).op r with hr₁
  have hg₁ : pushforwardGerm f F s V₁ hsV₁ ξ₁ = x :=
    pushforwardGerm_resF_eq f F s hV₁V hsV₁ hpre₁ hξ
  have hgr₁ : S.presheaf.germ V₁ s hsV₁ r₁ = S.presheaf.germ V₀ s hs₀ r := by
    rw [hr₁, S.presheaf.germ_res_apply (homOfLE hV₁V₀) s hsV₁ r]
  -- The quotient germ vanishes, so it vanishes on sections over a smaller affine open.
  have hzero : pushforwardGerm f (cokernel m) s V₁ hsV₁
      ((cokernel.π m).app (f ⁻¹ᵁ V₁) ξ₁) = 0 := by
    rwa [← stalkMap_pushforwardGerm f F (cokernel.π m) s V₁ hsV₁ ξ₁, hg₁]
  obtain ⟨V₂, hsV₂, hV₂aff, hV₂V₁, hV₂V₁', he⟩ := TopCat.Presheaf.germ_eq_of_isBasis
    S.isBasis_affineOpens ((Scheme.Modules.pushforward f).obj (cokernel m)).val.presheaf s
    hsV₁ hsV₁ (hzero.trans (pushforwardGerm_zero f (cokernel m) s V₁ hsV₁).symm)
  have hpre₂ : (f ⁻¹ᵁ V₂ : X.Opens) ≤ f ⁻¹ᵁ V₁ := fun _ hz => hV₂V₁ hz
  set ξ₂ : Γ(F, f ⁻¹ᵁ V₂) := resF F hpre₂ ξ₁ with hξ₂
  set r₂ : Γ(S, V₂) := S.presheaf.map (homOfLE hV₂V₁).op r₁ with hr₂
  have hV₂V₀ : V₂ ≤ V₀ := hV₂V₁.trans hV₁V₀
  have hpre₂₀ : (f ⁻¹ᵁ V₂ : X.Opens) ≤ f ⁻¹ᵁ V₀ := fun _ hz => hV₂V₀ hz
  have hgr₂ : S.presheaf.germ V₂ s hsV₂ r₂ = S.presheaf.germ V₀ s hs₀ r := by
    rw [hr₂, S.presheaf.germ_res_apply (homOfLE hV₂V₁) s hsV₂ r₁, hgr₁]
  have h0 : (cokernel.π m).app (f ⁻¹ᵁ V₂) ξ₂ = 0 := by
    rw [hξ₂, ← resF_app F (cokernel.π m) hpre₂ ξ₁]
    exact he.trans (resF_zero (cokernel m)
      (show (f ⁻¹ᵁ V₂ : X.Opens) ≤ f ⁻¹ᵁ V₁ from fun _ hz => hV₂V₁' hz))
  -- The multiplication rule, transported to `V₂`.
  have hm₂ : ∀ (W : X.Opens) (hW : W ≤ f ⁻¹ᵁ V₂) (z : Γ(F, W)),
      m.app W z = (f.appLE V₂ W hW r₂) • z := by
    intro W hW z
    rw [hm W (hW.trans hpre₂₀) z, hr₂, hr₁, appLE_res f hV₂V₁ hW r₁, hr₁,
      appLE_res f hV₁V₀ (hW.trans hpre₂) r]
  -- Local divisibility at every point, then assembly.
  obtain ⟨V₃, hsV₃, hV₃V₂, hpre₃, ζ, hζ⟩ := exists_resF_div_of_local f F hflat hV₂aff hsV₂ r₂
    (by rwa [hgr₂]) ξ₂ fun y =>
      exists_local_div_of_cokernel_app_eq_zero f F m r₂ hm₂ le_rfl ξ₂ h0 y.2
  refine ⟨pushforwardGerm f F s V₃ hsV₃ ζ, ?_⟩
  have happ₃ : f.app V₃ (S.presheaf.map (homOfLE hV₃V₂).op r₂) =
      f.appLE V₂ (f ⁻¹ᵁ V₃) hpre₃ r₂ :=
    app_map_eq_appLE f hV₃V₂ r₂ hpre₃
  have c2 : pushforwardGerm f F s V₃ hsV₃ (resF F hpre₃ ξ₂) = x :=
    pushforwardGerm_resF_eq f F s hV₃V₂ hsV₃ hpre₃
      (pushforwardGerm_resF_eq f F s hV₂V₁ hsV₂ hpre₂ hg₁)
  rw [← c2, hζ, ← happ₃, pushforwardGerm_smul f F s V₃ hsV₃ _ ζ,
    S.presheaf.germ_res_apply (homOfLE hV₃V₂) s hsV₃ r₂, hgr₂]

/-- **Exactness of the pushforward quotient sequence at a stalk.** Let `f : X ⟶ S` be
quasi-compact and quasi-separated, let `F` be flat over `S`, let `r` be a section of `𝒪_S` over
an open `V₀ ∋ s` whose germ at `s` is a nonzerodivisor, and let `m : F ⟶ F` be multiplication by
the pullback of `r`. An element of `(f_* F)_s` is killed by the stalk map of
`f_*(F ⟶ F / r F)` if and only if it is divisible by the germ of `r`. -/
public theorem stalkMap_cokernel_eq_zero_iff [QuasiCompact f] [QuasiSeparated f]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (m : F ⟶ F) {V₀ : S.Opens} (r : Γ(S, V₀))
    (hm : ∀ (W : X.Opens) (hW : W ≤ f ⁻¹ᵁ V₀) (z : Γ(F, W)),
      m.app W z = (f.appLE V₀ W hW r) • z)
    (s : S) (hs₀ : s ∈ V₀)
    (ha : IsSMulRegular (S.presheaf.stalk s) (S.presheaf.germ V₀ s hs₀ r))
    (x : TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pushforward f).obj F).val.presheaf s) :
    (TopCat.Presheaf.stalkFunctor Ab.{u} s).map
        ((Scheme.Modules.pushforward f).map (cokernel.π m)).mapPresheaf x = 0 ↔
      ∃ z, x = S.presheaf.germ V₀ s hs₀ r • z := by
  refine ⟨exists_smul_eq_of_stalkMap_cokernel_eq_zero f F hflat m r hm s hs₀ ha x, ?_⟩
  rintro ⟨z, rfl⟩
  exact stalkMap_cokernel_eq_zero_of_smul f F m r hm s hs₀ z

end Stacks.AlgebraicGeometry.PushforwardRegularity

end
