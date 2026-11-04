module

public import StacksFrontier.AlgebraicGeometry.Divisors.CartierRegular.FrameTrivialization
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.InvertibleSheaves
public import StacksFrontier.Topology.Sheaves.Modules.Exactness
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleCompleteLattice
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Converse

/-!
# Sections of a locally trivial module over the affine opens of a trivialization

Let `X` be a scheme and `L` a sheaf of `𝒪_X`-modules which is locally isomorphic to `𝒪_X`
([Stacks, Tag 02AD]). Over an open `W` inside an open `T` on which `L|_T ≅ 𝒪_T`, the trivialization
identifies `Γ(L, W)` with `Γ(X, W)` linearly; the affine opens inside such opens form a basis of
`X`. This file records the consequences used to compare subsheaves of `L` by computing their
sections over that basis, and a criterion for exactness of a short complex of sheaves of modules
over a basis of affine opens.

## Main definitions

* `Stacks.LocallyTrivial.trivSections`: the `Γ(X, W)`-linear identification
  `Γ(L, W) ≃ Γ(X, W)` induced by a trivialization `L|_T ≅ 𝒪_T` over an open `W ≤ T`.

## Main results

* `Stacks.LocallyTrivial.onSpace_isInvertible_of_isInvertible`: an invertible `𝒪_X`-module
  ([Stacks, Tag 01CS]) is locally isomorphic to `𝒪_X` ([Stacks, Tag 02AD]), the local rings of a
  scheme being local.
* `Stacks.LocallyTrivial.trivSections_map_smul_top`: the identification carries `K • Γ(L, W)` to
  the ideal `K`.
* `Stacks.LocallyTrivial.submodule_le_of_locallyTrivial`: an inclusion of subsheaves of a locally
  trivial `L` may be checked over the affine opens on which `L` is trivial.
* `AlgebraicGeometry.Scheme.Modules.eq_zero_of_locally` and
  `AlgebraicGeometry.Scheme.Modules.eq_zero_of_locally_affine`: a section restricting to zero over
  a basis of affine opens inside its domain is zero.
* `AlgebraicGeometry.Scheme.Modules.exact_of_affinewise`: a short complex of `𝒪_X`-modules is
  exact as soon as, over every affine open of a basis, every section killed by the second map
  lifts along the first.

## References

* [Stacks Project, Tag 02AD](https://stacks.math.columbia.edu/tag/02AD)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Every point of an open `U` has an affine open neighbourhood inside `U`. -/
private theorem exists_affineOpens_le {x : X} {U : X.Opens} (hx : x ∈ U) :
    ∃ W : X.affineOpens, x ∈ W.1 ∧ W.1 ≤ U := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  exact ⟨⟨V, hV⟩, hxV, hVU⟩

/-- **A section which vanishes over a basis of affine opens is zero.** Let `P` be a property of
affine opens such that every point of every open has an affine neighbourhood with `P` inside it.
A section restricting to zero over every affine open with `P` inside its domain is zero. -/
theorem eq_zero_of_locally (L : X.Modules) (P : X.affineOpens → Prop)
    (hP : ∀ (x : X) (U : X.Opens), x ∈ U → ∃ W : X.affineOpens, P W ∧ x ∈ W.1 ∧ W.1 ≤ U)
    {U : X.Opens} (m : Γ(L, U))
    (h : ∀ (V : X.affineOpens), P V → ∀ (hVU : V.1 ≤ U), L.presheaf.map (homOfLE hVU).op m = 0) :
    m = 0 := by
  refine TopCat.Presheaf.section_ext ⟨L.presheaf, L.isSheaf⟩ U _ _ fun x hx => ?_
  obtain ⟨V, hPV, hxV, hVU⟩ := hP x U hx
  rw [← TopCat.Presheaf.germ_res_apply L.presheaf (homOfLE hVU) x hxV m, h V hPV hVU, map_zero,
    map_zero]

/-- **A section which vanishes over every affine open inside its domain is zero.** -/
theorem eq_zero_of_locally_affine (L : X.Modules) {U : X.Opens} (m : Γ(L, U))
    (h : ∀ (V : X.affineOpens) (hVU : V.1 ≤ U), L.presheaf.map (homOfLE hVU).op m = 0) :
    m = 0 :=
  eq_zero_of_locally L (fun _ => True) (fun _ _ hx => by
    obtain ⟨V, hxV, hVU⟩ := exists_affineOpens_le hx
    exact ⟨V, trivial, hxV, hVU⟩) m fun V _ hVU => h V hVU

/-- **Exactness of a short complex of `𝒪_X`-modules over a basis of affine opens.** Let `P` be a
property of affine opens such that every point of every open has an affine neighbourhood with
`P` inside it. If over every affine open with `P` each section of the middle term killed by the
second map lifts along the first, the short complex is exact: exactness is detected on stalks,
and every germ is represented over such an affine open. -/
theorem exact_of_affinewise (S : ShortComplex X.Modules) (P : X.affineOpens → Prop)
    (hP : ∀ (x : X) (U : X.Opens), x ∈ U → ∃ W : X.affineOpens, P W ∧ x ∈ W.1 ∧ W.1 ≤ U)
    (hS : ∀ (W : X.affineOpens), P W → ∀ β : Γ(S.X₂, W.1), S.g.app W.1 β = 0 →
      ∃ α : Γ(S.X₁, W.1), S.f.app W.1 α = β) :
    S.Exact := by
  classical
  refine (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact X.ringCatSheaf
    S).mpr fun z => ?_
  refine (ShortComplex.ab_exact_iff_function_exact _).2 fun m => ?_
  constructor
  · intro hm
    obtain ⟨O₁, hzO₁, s, hs⟩ := TopCat.Presheaf.exists_germ_eq S.X₂.val.presheaf (x := z) m
    have hgm : TopCat.Presheaf.germ S.X₃.val.presheaf O₁ z hzO₁ (S.g.app O₁ s) = 0 := by
      refine (TopCat.Presheaf.stalkFunctor_map_germ_apply (F := S.X₂.val.presheaf)
        (G := S.X₃.val.presheaf) O₁ z hzO₁
        ((PresheafOfModules.toPresheaf _).map S.g.val) s).symm.trans ?_
      rw [hs]
      exact hm
    obtain ⟨W₀, hzW₀, iU, iV, hWeq⟩ := TopCat.Presheaf.germ_eq S.X₃.val.presheaf z hzO₁ hzO₁
      (S.g.app O₁ s) 0 (by rw [hgm, map_zero])
    obtain ⟨W, hPW, hzW, hWW₀⟩ := hP z W₀ hzW₀
    have hWO : W.1 ≤ O₁ := hWW₀.trans iU.le
    have h2 : S.X₃.val.map iU.op (S.g.app O₁ s) = 0 :=
      (hWeq : S.X₃.val.map iU.op (S.g.app O₁ s) =
        S.X₃.val.map iV.op (0 : S.X₃.val.obj (op O₁))).trans (map_zero _)
    have hgβ : S.g.app W.1 (S.X₂.val.map (homOfLE hWO).op s) = 0 := by
      refine (PresheafOfModules.naturality_apply S.g.val (homOfLE hWO).op s).trans ?_
      refine (PresheafOfModules.map_comp_apply S.X₃.val iU.op (homOfLE hWW₀).op
        (S.g.app O₁ s)).trans ?_
      rw [h2]
      exact map_zero _
    obtain ⟨α, hα⟩ := hS W hPW (S.X₂.val.map (homOfLE hWO).op s) hgβ
    refine ⟨TopCat.Presheaf.germ S.X₁.val.presheaf W.1 z hzW α, ?_⟩
    refine (TopCat.Presheaf.stalkFunctor_map_germ_apply (F := S.X₁.val.presheaf)
      (G := S.X₂.val.presheaf) W.1 z hzW
      ((PresheafOfModules.toPresheaf _).map S.f.val) α).trans ?_
    refine Eq.trans (congrArg
      (fun w => TopCat.Presheaf.germ S.X₂.val.presheaf W.1 z hzW w) hα) ?_
    exact (TopCat.Presheaf.germ_res_apply' S.X₂.val.presheaf (homOfLE hWO).op z hzW s).trans hs
  · rintro ⟨n, rfl⟩
    simp

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.LocallyTrivial

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

variable {X : Scheme.{u}} {L : X.Modules}

/-- **A trivialization identifies the sections over a smaller open with functions.** For
`L|_T ≅ 𝒪_T` and an open `W ≤ T`, the trivialization gives a `Γ(X, W)`-linear isomorphism
`Γ(L, W) ≃ Γ(X, W)`. -/
noncomputable def trivSections {T : X.Opens}
    (eT : L.over T ≅ SheafOfModules.unit (X.ringCatSheaf.over T))
    {W : X.Opens} (hW : W ≤ T) : Γ(L, W) ≃ₗ[Γ(X, W)] Γ(X, W) :=
  (Stacks.Divisors.frameTrivialization eT).θ W (homOfLE hW)

/-- Under the identification of a trivialization, the multiples `K • Γ(L, W)` of an ideal `K` of
`Γ(X, W)` correspond to `K` itself. -/
theorem trivSections_map_smul_top {T : X.Opens}
    (eT : L.over T ≅ SheafOfModules.unit (X.ringCatSheaf.over T))
    {W : X.Opens} (hW : W ≤ T) (K : Ideal Γ(X, W)) :
    (K • (⊤ : Submodule Γ(X, W) Γ(L, W))).map (trivSections eT hW).toLinearMap = K := by
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  exact Ideal.mul_top K

/-- A section lies in `K • Γ(L, W)` exactly when its image under a trivialization lies in `K`. -/
theorem mem_smul_top_iff {T : X.Opens}
    (eT : L.over T ≅ SheafOfModules.unit (X.ringCatSheaf.over T))
    {W : X.Opens} (hW : W ≤ T) (K : Ideal Γ(X, W)) (s : Γ(L, W)) :
    s ∈ K • (⊤ : Submodule Γ(X, W) Γ(L, W)) ↔ trivSections eT hW s ∈ K := by
  conv_rhs => rw [← trivSections_map_smul_top eT hW K]
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

/-- **Inclusions of subsheaves of a locally trivial module are checked on trivializing affine
opens.** If `L` is locally isomorphic to `𝒪_X` and two subsheaves have included sections over
every affine open on which `L` is trivial, then they are included. -/
theorem submodule_le_of_locallyTrivial
    [AlgebraicGeometry.SheafOfModules.OnSpace.IsInvertible L] (N₁ N₂ : L.Submodule)
    (h : ∀ (T : X.Opens) (_ : L.over T ≅ SheafOfModules.unit (X.ringCatSheaf.over T))
      (W : X.affineOpens), W.1 ≤ T → N₁.obj (op W.1) ≤ N₂.obj (op W.1)) : N₁ ≤ N₂ := by
  refine SheafOfModules.Submodule.le_iff.mpr (PresheafOfModules.Submodule.le_iff.mpr ?_)
  intro U s hs
  refine N₂.isSheaf s ?_
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨T, hxT, ⟨eT⟩⟩ :=
    AlgebraicGeometry.SheafOfModules.OnSpace.IsInvertible.locally_iso (L := L) x
  obtain ⟨W, hxW, hWle⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_affineOpens_le (show x ∈ U.unop ⊓ T from ⟨hx, hxT⟩)
  refine ⟨W.1, homOfLE (hWle.trans inf_le_left), ?_, hxW⟩
  exact h T eT W (hWle.trans inf_le_right)
    (N₁.toSubmodule.map (homOfLE (hWle.trans inf_le_left)).op hs)

/-- The affine opens contained in some trivializing open of a locally trivial module form a
basis of the topology. -/
theorem exists_trivializing_affine [AlgebraicGeometry.SheafOfModules.OnSpace.IsInvertible L]
    (x : X) (U : X.Opens) (hx : x ∈ U) :
    ∃ W : X.affineOpens, (∃ (T : X.Opens) (_ : L.over T ≅ SheafOfModules.unit
      (X.ringCatSheaf.over T)), W.1 ≤ T) ∧ x ∈ W.1 ∧ W.1 ≤ U := by
  obtain ⟨T, hxT, ⟨eT⟩⟩ :=
    AlgebraicGeometry.SheafOfModules.OnSpace.IsInvertible.locally_iso (L := L) x
  obtain ⟨W, hxW, hWle⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_affineOpens_le (show x ∈ U ⊓ T from ⟨hx, hxT⟩)
  exact ⟨W, ⟨T, eT, hWle.trans inf_le_right⟩, hxW, hWle.trans inf_le_left⟩

/-- **An invertible module on a scheme is locally isomorphic to the structure sheaf.** An
`𝒪_X`-module invertible for the tensor product ([Stacks, Tag 01CS]) is locally trivial
([Stacks, Tag 02AD]): the local rings of a scheme are local, so by [Stacks, Tag 0B8M] every point
has a neighbourhood on which the module is trivial. -/
theorem onSpace_isInvertible_of_isInvertible (L : X.Modules)
    [h : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    AlgebraicGeometry.SheafOfModules.OnSpace.IsInvertible L := by
  have : ∀ z : X.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace z) :=
    fun z => X.isLocalRing z
  obtain ⟨I, U, hU, hiso⟩ :=
    (@Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_isInvertible X.toRingedSpace L _ h).1
  refine ⟨fun x => ?_⟩
  rw [Opens.coversTop_iff] at hU
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU ▸ (show x ∈ (⊤ : Opens X) from trivial))
  exact ⟨U i, hi, hiso i⟩

end Stacks.LocallyTrivial

end
