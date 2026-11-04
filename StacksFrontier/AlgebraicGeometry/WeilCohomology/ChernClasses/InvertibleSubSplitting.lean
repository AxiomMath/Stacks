module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DualSectionsInfinitesimal
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.FiniteLocallyFreeReflexive
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.DualShortExact
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelLocallyFree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.StandingSituation
public import StacksFrontier.CategoryTheory.Abelian.KernelComp
public import StacksFrontier.CategoryTheory.Abelian.KernelLadder
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Splitting an invertible submodule off by passing to the projective bundle of the dual

In the standing situation of Stacks Section 45.12, Tag 0FI5's proof of the Whitney formula in
arbitrary rank begins: *"it suffices to check this after pulling back by the morphism
`𝐏(ℰ^∨) → X`. Thus we may assume we have an invertible submodule `ℒ ⊂ ℰ` such that both `ℰ/ℒ`
and `ℱ/ℒ` are finite locally free."* This file **proves that sentence**.

## Main results

* `Stacks.WeilCohomology.isFiniteLocallyFreeOfRank_X₂_of_shortExact`: the middle term of a short
  exact sequence whose outer terms have constant ranks has constant rank, as soon as it is finite
  locally free.
* `Stacks.WeilCohomology.pullbackDualDualIso`: `(p^*(ℳ^∨))^∨ ≅ p^*ℳ` for `ℳ` finite locally
  free.
* `Stacks.WeilCohomology.exists_shortExact_dualSheaf_mid` and
  `Stacks.WeilCohomology.exists_shortExact_dualSheaf_outer`: the dual of a short exact sequence
  of finite locally free modules, with its middle term, respectively its two outer terms,
  transported along isomorphisms.
* `Stacks.WeilCohomology.exists_splitInvertibleSub_of_bundleDatum`: the three sequences, from a
  bundle datum of the dual; no `A` and no standing situation enter.
* `Stacks.WeilCohomology.ChernSituation.exists_splitInvertibleSub`: **the sentence above.**

## The argument

Let `0 ⟶ ℰ ⟶ ℱ ⟶ 𝒢 ⟶ 0` be short exact with `ℰ` of rank `r + 2`, `ℱ` of rank `b` and `𝒢` of
rank `c`.

`𝐏(ℰ^∨)` is the projective bundle of the dual, which exists as an object of `𝒞` by clause (3)(a)
— the field `ChernSetup.bundleDatum` — because `ℰ^∨` is again finite locally free of rank `r + 2`
(`Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf`). Injectivity of
`p^*` on `A` is **not** assumed: it is `ChernSetup.injective_pull_proj`, a consequence of the
projective bundle formula, which is condition (4).

On `P = 𝐏(ℰ^∨)` the tautological sequence is `0 ⟶ 𝓖 ⟶ p^*(ℰ^∨) ⟶ 𝒪_P(1) ⟶ 0` with `𝓖` of rank
`r + 1`. Dualizing it gives `0 ⟶ 𝒪_P(1)^∨ ⟶ (p^*(ℰ^∨))^∨ ⟶ 𝓖^∨ ⟶ 0`, and
`(p^*(ℰ^∨))^∨ ≅ p^*ℰ`: pullback commutes with the dual of a finite locally free module
(`Stacks.FundamentalGroup.pullbackDualSheafIso`) and a finite locally free module is reflexive
(`Stacks.FundamentalGroup.ExtendedEtale.isReflexive_of_isFiniteLocallyFree'`). So `ℒ := 𝒪_P(1)^∨`
is an invertible submodule of `p^*ℰ` with `ℰ' := 𝓖^∨` as quotient, of rank `r + 1`.

For `ℱ` the same module is used. Dualizing the given sequence on `X` and pulling back along the
flat `p` gives `0 ⟶ p^*(𝒢^∨) ⟶ p^*(ℱ^∨) ⟶ p^*(ℰ^∨) ⟶ 0`, so the composite
`φ : p^*(ℱ^∨) ⟶ p^*(ℰ^∨) ⟶ 𝒪_P(1)` is an epimorphism onto an invertible module, and
`𝒦 := ker φ` is finite locally free
(`Stacks.ProjectiveBundleSplitting.isFiniteLocallyFree_kernel_of_epi_isInvertible`). Dualizing
`0 ⟶ 𝒦 ⟶ p^*(ℱ^∨) ⟶ 𝒪_P(1) ⟶ 0` exhibits the *same* `ℒ` inside `p^*ℱ` with quotient
`ℱ' := 𝒦^∨`; so `ℱ/ℒ` is obtained as the dual of a **kernel** and never as a cokernel, which is
what makes its local freeness available.

Finally `𝒦` is the kernel of a composite, so `CategoryTheory.shortExact_kernelComp` gives
`0 ⟶ p^*(𝒢^∨) ⟶ 𝒦 ⟶ 𝓖 ⟶ 0`; dualizing that is `0 ⟶ ℰ' ⟶ ℱ' ⟶ p^*𝒢 ⟶ 0`, the third sequence.

## Why the ranks are constant

The source states this step for modules of constant rank, and so does this file. The field of
`ChernSituation` that it replaces asked only that `ℱ` and `𝒢` be finite locally free while still
demanding a *constant* rank of `ℱ/ℒ`, and that is not satisfiable: over an `X` with two open and
closed pieces on which `ℱ` has ranks `5` and `17` the quotient has ranks `4` and `16`, and one
cannot escape by choosing `p` to meet one piece only, because condition (2) makes
`A(X) = A(U) × A(V)` and so destroys injectivity of `p^*`. A field that cannot be inhabited makes
every theorem over it vacuous, which is worse than an unproved hypothesis because no check of the
axioms used detects it. The sole consumer,
`Stacks.WeilCohomology.ChernSituation.chernSeries_mul_of_shortExact`, has all three ranks
constant in hand, so nothing downstream is lost.

## References

* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FV8](https://stacks.math.columbia.edu/tag/0FV8)
* [Stacks Project, Tag 02N4](https://stacks.math.columbia.edu/tag/02N4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u v v₁ w

namespace Stacks.WeilCohomology

/-! ### The constant rank of the middle term of a short exact sequence -/

/-- **The middle term of a short exact sequence whose outer terms have constant ranks has
constant rank**, as soon as it is finite locally free.

A finite locally free module has some constant rank near every point; restricting the sequence to
such an open is a flat pullback and so keeps it short exact, and rank additivity at the point the
open was chosen around pins that rank to `r₁ + r₃`. The conclusion then glues over the cover, so
no point of the scheme is assumed. -/
@[sga "6 I 6.0" "(ii), special case"]
theorem isFiniteLocallyFreeOfRank_X₂_of_shortExact {P : Scheme.{u}} (Z : ShortComplex P.Modules)
    (hZ : Z.ShortExact) (r₁ r₃ : ℕ)
    (h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Z.X₁ r₁)
    (h3 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Z.X₃ r₃)
    (h2 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} Z.X₂) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Z.X₂ (r₁ + r₃) := by
  have := h1
  have := h3
  choose U hxU m hm using fun x : P =>
    Stacks.ProjectiveBundleSplitting.exists_isFiniteLocallyFreeOfRank_restrict Z.X₂ h2 x
  refine (Scheme.Modules.isFiniteLocallyFreeOfRank_iff Z.X₂ (r₁ + r₃)).mp ?_
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top U ?_ fun x => ?_
  · exact eq_top_iff.mpr fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hxU y⟩
  · have hmx : m x = r₁ + r₃ := by
      have hZU : (Z.map (Scheme.Modules.pullback (U x).ι)).ShortExact :=
        shortExact_map_pullback (U x).ι Z hZ
      have i1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          (Z.map (Scheme.Modules.pullback (U x).ι)).X₁ r₁ :=
        AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (U x).ι Z.X₁ r₁
      have i3 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          (Z.map (Scheme.Modules.pullback (U x).ι)).X₃ r₃ :=
        AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (U x).ι Z.X₃ r₃
      have i2 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          (Z.map (Scheme.Modules.pullback (U x).ι)).X₂ (m x) :=
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
          ((Scheme.Modules.restrictFunctorIsoPullback (U x).ι).app Z.X₂) (hm x)
      exact AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact
        (Z.map (Scheme.Modules.pullback (U x).ι)) hZU r₁ (m x) r₃ ⟨x, hxU x⟩
    exact (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mpr (hmx ▸ hm x)

/-! ### Duality on a pullback, and the dual of a short exact sequence -/

/-- **`(p^*(ℳ^∨))^∨ ≅ p^*ℳ` for `ℳ` finite locally free**, read in the direction the dual of a
tautological sequence needs it. Pullback commutes with the dual of a finite locally free module
by `Stacks.FundamentalGroup.pullbackDualSheafIso`, and `p^*ℳ` is reflexive because it is finite
locally free. -/
def pullbackDualDualIso {Y P : Scheme.{u}} (q : P ⟶ Y) (M : Y.Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M)
    (hMP : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback q).obj M)) :
    (Scheme.Modules.pullback q).obj M ≅
      dualSheaf ((Scheme.Modules.pullback q).obj (dualSheaf M)) :=
  haveI : IsIso (toDoubleDual ((Scheme.Modules.pullback q).obj M)) :=
    Stacks.FundamentalGroup.ExtendedEtale.isReflexive_of_isFiniteLocallyFree' _
      ((Scheme.Modules.isFiniteLocallyFree_iff _).mpr hMP)
  asIso (toDoubleDual _) ≪≫
    dualSheafIsoOfIso (Stacks.FundamentalGroup.pullbackDualSheafIso q M hM)

/-- `Stacks.WeilCohomology.pullbackDualDualIso` for a module of constant rank. -/
def pullbackDualDualIsoOfRank {Y P : Scheme.{u}} (q : P ⟶ Y) (M : Y.Modules) (n : ℕ)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M n) :
    (Scheme.Modules.pullback q).obj M ≅
      dualSheaf ((Scheme.Modules.pullback q).obj (dualSheaf M)) :=
  pullbackDualDualIso q M hM.isFiniteLocallyFree
    (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback q M n).isFiniteLocallyFree

/-- The dual of a short exact sequence of finite locally free modules, with all three terms
transported along isomorphisms. -/
private theorem exists_shortExact_dualSheaf_iso {Y : Scheme.{u}} {A B L E' M G' : Y.Modules}
    (f : A ⟶ B) (g : B ⟶ L) (w : f ≫ g = 0) (hmono : Mono f) (hepi : Epi g)
    (hex : (ShortComplex.mk f g w).Exact)
    (hA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A)
    (hB : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} B)
    (hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L)
    (α : dualSheaf L ≅ E') (κ : M ≅ dualSheaf B) (γ : dualSheaf A ≅ G') :
    ∃ w' : (α.inv ≫ dualMap g ≫ κ.inv) ≫ (κ.hom ≫ dualMap f ≫ γ.hom) = 0,
      (ShortComplex.mk (α.inv ≫ dualMap g ≫ κ.inv) (κ.hom ≫ dualMap f ≫ γ.hom) w').ShortExact := by
  obtain ⟨w₀, h₀⟩ := exists_dualSheaf_shortExact f g w hmono hepi hex hA hB hL
  exact ⟨by simp [reassoc_of% w₀],
    ShortComplex.shortExact_of_iso (S₁ := ShortComplex.mk (dualMap g) (dualMap f) w₀)
      (ShortComplex.isoMk α κ.symm γ (by simp) (by simp)) h₀⟩

/-- **The dual of a short exact sequence of finite locally free modules, with its middle term
transported along an isomorphism.** The dual sequence is
`Stacks.AlgebraicGeometry.ReflexiveModules.exists_dualSheaf_shortExact`; `κ` replaces `ℬ^∨` by
whatever is isomorphic to it, which is how `(p^*(ℳ^∨))^∨` is read as `p^*ℳ`. -/
theorem exists_shortExact_dualSheaf_mid {Y : Scheme.{u}} {A B L M : Y.Modules} (f : A ⟶ B)
    (g : B ⟶ L) (w : f ≫ g = 0) (hmono : Mono f) (hepi : Epi g)
    (hex : (ShortComplex.mk f g w).Exact)
    (hA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A)
    (hB : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} B)
    (hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L)
    (κ : M ≅ dualSheaf B) :
    ∃ w' : (dualMap g ≫ κ.inv) ≫ (κ.hom ≫ dualMap f) = 0,
      (ShortComplex.mk (dualMap g ≫ κ.inv) (κ.hom ≫ dualMap f) w').ShortExact := by
  obtain ⟨w₀, h₀⟩ := exists_shortExact_dualSheaf_iso f g w hmono hepi hex hA hB hL
    (Iso.refl _) κ (Iso.refl _)
  exact ⟨by simpa using w₀, by simpa using h₀⟩

/-- **The dual of a short exact sequence of finite locally free modules, with its two outer terms
transported along isomorphisms.** The companion of
`Stacks.WeilCohomology.exists_shortExact_dualSheaf_mid` for the sequence whose middle term is
already in the wanted form. -/
theorem exists_shortExact_dualSheaf_outer {Y : Scheme.{u}} {A B L E' G' : Y.Modules} (f : A ⟶ B)
    (g : B ⟶ L) (w : f ≫ g = 0) (hmono : Mono f) (hepi : Epi g)
    (hex : (ShortComplex.mk f g w).Exact)
    (hA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A)
    (hB : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} B)
    (hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L)
    (α : dualSheaf L ≅ E') (γ : dualSheaf A ≅ G') :
    ∃ w' : (α.inv ≫ dualMap g) ≫ (dualMap f ≫ γ.hom) = 0,
      (ShortComplex.mk (α.inv ≫ dualMap g) (dualMap f ≫ γ.hom) w').ShortExact := by
  obtain ⟨w₀, h₀⟩ := exists_shortExact_dualSheaf_iso f g w hmono hepi hex hA hB hL
    α (Iso.refl _) γ
  exact ⟨by simpa using w₀, by simpa using h₀⟩

/-- **The dual of a short exact sequence of finite locally free modules, pulled back along a flat
morphism, is short exact.** -/
theorem exists_shortExact_pullback_dualSheaf {Y P : Scheme.{u}} (q : P ⟶ Y) [Flat q]
    (T : ShortComplex Y.Modules) (hT : T.ShortExact)
    (hA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} T.X₁)
    (hB : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} T.X₂)
    (hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} T.X₃) :
    ∃ w : (Scheme.Modules.pullback q).map (dualMap T.g) ≫
        (Scheme.Modules.pullback q).map (dualMap T.f) = 0,
      (ShortComplex.mk _ _ w).ShortExact := by
  obtain ⟨wd, hTd⟩ := exists_dualSheaf_shortExact T.f T.g T.zero hT.mono_f hT.epi_g hT.exact
    hA
    hB
    hL
  exact ⟨((ShortComplex.mk (dualMap T.g) (dualMap T.f) wd).map (Scheme.Modules.pullback q)).zero,
    shortExact_map_pullback q (ShortComplex.mk (dualMap T.g) (dualMap T.f) wd) hTd⟩

/-! ### Splitting an invertible submodule off, from a bundle datum of the dual -/

/-- **The three short exact sequences of Tag 0FI5's reduction, from a projective bundle of the
dual.** Given `0 ⟶ ℰ ⟶ ℱ ⟶ 𝒢 ⟶ 0` of constant ranks `r + 2`, `b`, `c` on an object `X` of `𝒞`
and a bundle datum `D` of `ℰ^∨` with projection `p`, there are an invertible `ℒ`, a module `ℰ'`
of rank `r + 1` and a module `ℱ'` of constant rank `c + (r + 1)` with
`0 ⟶ ℒ ⟶ p^*ℰ ⟶ ℰ' ⟶ 0`, `0 ⟶ ℒ ⟶ p^*ℱ ⟶ ℱ' ⟶ 0` and `0 ⟶ ℰ' ⟶ ℱ' ⟶ p^*𝒢 ⟶ 0`.

Nothing about `A` enters, so this is a statement about modules on schemes and not about the
standing situation; `Stacks.WeilCohomology.ChernSituation.exists_splitInvertibleSub` adds the
bundle datum of clause (3)(a) and the injectivity of `p^*` that condition (4) gives. -/
theorem exists_splitInvertibleSub_of_bundleDatum {C : Type w} [Category.{v₁} C]
    {S : C ⥤ Scheme.{u}} (X : C) (T : ShortComplex (S.obj X).Modules) (hT : T.ShortExact)
    (r b c : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₁ (r + 1 + 1))
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₂ b)
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₃ c)
    (D : BundleDatum S X (dualSheaf T.X₁) (r + 1)) :
    ∃ (L E' F' : (S.obj D.bundle).Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj D.bundle).presheaf
        (S.obj D.bundle).ringCatSheaf.2 L)
      (_ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' (r + 1))
      (s : ℕ)
      (_ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' s)
      (iE : L ⟶ (Scheme.Modules.pullback (S.map D.proj)).obj T.X₁)
      (qE : (Scheme.Modules.pullback (S.map D.proj)).obj T.X₁ ⟶ E') (wE : iE ≫ qE = 0)
      (iF : L ⟶ (Scheme.Modules.pullback (S.map D.proj)).obj T.X₂)
      (qF : (Scheme.Modules.pullback (S.map D.proj)).obj T.X₂ ⟶ F') (wF : iF ≫ qF = 0)
      (fQ : E' ⟶ F') (gQ : F' ⟶ (Scheme.Modules.pullback (S.map D.proj)).obj T.X₃)
      (wQ : fQ ≫ gQ = 0),
      (ShortComplex.mk iE qE wE).ShortExact ∧ (ShortComplex.mk iF qF wF).ShortExact ∧
        (ShortComplex.mk fQ gQ wQ).ShortExact := by
  have hEd := isFiniteLocallyFreeOfRank_dualSheaf T.X₁ (r + 1 + 1) hE
  have hFd := isFiniteLocallyFreeOfRank_dualSheaf T.X₂ b hF
  have hGd := isFiniteLocallyFreeOfRank_dualSheaf T.X₃ c hG
  have hA3 := isFiniteLocallyFreeOfRank_pullback (S.map D.proj) (dualSheaf T.X₃) c
  have hA1fl := (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (S.map D.proj)
    (dualSheaf T.X₁) (r + 1 + 1)).isFiniteLocallyFree
  have hA2fl := (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (S.map D.proj)
    (dualSheaf T.X₂) b).isFiniteLocallyFree
  have htw1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.twist 1 :=
    Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_one_of_isInvertible D.twist
      D.twist_isInvertible
  have htwfl := htw1.isFiniteLocallyFree
  have : Mono D.incl := D.shortExact.mono_f
  have : Epi D.quot := D.shortExact.epi_g
  have κ₁ := pullbackDualDualIsoOfRank (S.map D.proj) T.X₁ _ hE
  have κ₂ := pullbackDualDualIsoOfRank (S.map D.proj) T.X₂ _ hF
  have κ₃ := pullbackDualDualIsoOfRank (S.map D.proj) T.X₃ _ hG
  obtain ⟨hzz, hTdp⟩ := exists_shortExact_pullback_dualSheaf (S.map D.proj) T hT
    hE.isFiniteLocallyFree hF.isFiniteLocallyFree hG.isFiniteLocallyFree
  have : Epi ((Scheme.Modules.pullback (S.map D.proj)).map (dualMap T.f)) := hTdp.epi_g
  have hker := shortExact_kernelComp hzz hTdp D.quot
  have hKfl := Stacks.ProjectiveBundleSplitting.isFiniteLocallyFree_kernel_of_epi_isInvertible
    ((Scheme.Modules.pullback (S.map D.proj)).map (dualMap T.f) ≫ D.quot) inferInstance hA2fl
    D.twist_isInvertible
  have eSub : D.sub ≅ kernel D.quot :=
    IsLimit.conePointUniqueUpToIso D.shortExact.exact.fIsKernel
      (limit.isLimit (parallelPair D.quot 0))
  have hKQ :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} eSub D.sub_rank
  have hKrank := isFiniteLocallyFreeOfRank_X₂_of_shortExact _ hker c (r + 1) hA3 hKQ hKfl
  obtain ⟨wE, hseqE⟩ := exists_shortExact_dualSheaf_mid D.incl D.quot D.incl_comp_quot
    D.shortExact.mono_f D.shortExact.epi_g D.shortExact.exact D.sub_rank.isFiniteLocallyFree
    hA1fl htwfl κ₁
  obtain ⟨wF, hseqF⟩ := exists_shortExact_dualSheaf_mid
    (kernel.ι ((Scheme.Modules.pullback (S.map D.proj)).map (dualMap T.f) ≫ D.quot))
    ((Scheme.Modules.pullback (S.map D.proj)).map (dualMap T.f) ≫ D.quot)
    (kernel.condition _) inferInstance inferInstance (ShortComplex.exact_kernel _) hKfl hA2fl
    htwfl κ₂
  obtain ⟨wQ, hseqQ⟩ := exists_shortExact_dualSheaf_outer (kernelCompSub hzz D.quot)
    (kernelCompQuot ((Scheme.Modules.pullback (S.map D.proj)).map (dualMap T.f)) D.quot)
    (kernelCompSub_comp_kernelCompQuot hzz D.quot) hker.mono_f hker.epi_g hker.exact
    hA3.isFiniteLocallyFree hKfl hKQ.isFiniteLocallyFree (dualSheafIsoOfIso eSub) κ₃.symm
  exact ⟨dualSheaf D.twist, dualSheaf D.sub,
    dualSheaf (kernel ((Scheme.Modules.pullback (S.map D.proj)).map (dualMap T.f) ≫ D.quot)),
    @Stacks.InvertibleRankOneIff.isInvertible_of_isFiniteLocallyFreeOfRank_one
      (S.obj D.bundle).toRingedSpace (dualSheaf D.twist)
      (isFiniteLocallyFreeOfRank_dualSheaf D.twist 1 htw1),
    isFiniteLocallyFreeOfRank_dualSheaf D.sub (r + 1) D.sub_rank, c + (r + 1),
    isFiniteLocallyFreeOfRank_dualSheaf _ (c + (r + 1)) hKrank,
    _, _, wE, _, _, wF, _, _, wQ, hseqE, hseqF, hseqQ⟩

namespace ChernSituation

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}
  (𝔖 : ChernSituation.{u, v, v₁, w} C S)

/-- **"It suffices to check this after pulling back by the morphism `𝐏(ℰ^∨) → X`; thus we may
assume we have an invertible submodule `ℒ ⊂ ℰ` such that both `ℰ/ℒ` and `ℱ/ℒ` are finite locally
free"** — the sentence of Tag 0FI5's proof of the Whitney formula in arbitrary rank, proved.

The object `P` is the projective bundle of `ℰ^∨`, an object of `𝒞` by clause (3)(a), and
injectivity of `p^*` on `A` is `Stacks.WeilCohomology.ChernSetup.injective_pull_proj`, a
consequence of the projective bundle formula and not a further assumption. The three sequences
are `Stacks.WeilCohomology.exists_splitInvertibleSub_of_bundleDatum`, which is pure sheaf
theory. -/
theorem exists_splitInvertibleSub (X : C) (T : ShortComplex (S.obj X).Modules) (hT : T.ShortExact)
    (r b c : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₁ (r + 1 + 1))
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₂ b)
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₃ c) :
    ∃ (P : C) (p : P ⟶ X), Function.Injective (𝔖.pull p) ∧
      ∃ (L E' F' : (S.obj P).Modules)
        (_ : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
          (S.obj P).ringCatSheaf.2 L)
        (_ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' (r + 1))
        (s : ℕ)
        (_ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' s)
        (iE : L ⟶ (Scheme.Modules.pullback (S.map p)).obj T.X₁)
        (qE : (Scheme.Modules.pullback (S.map p)).obj T.X₁ ⟶ E') (wE : iE ≫ qE = 0)
        (iF : L ⟶ (Scheme.Modules.pullback (S.map p)).obj T.X₂)
        (qF : (Scheme.Modules.pullback (S.map p)).obj T.X₂ ⟶ F') (wF : iF ≫ qF = 0)
        (fQ : E' ⟶ F') (gQ : F' ⟶ (Scheme.Modules.pullback (S.map p)).obj T.X₃)
        (wQ : fQ ≫ gQ = 0),
        (ShortComplex.mk iE qE wE).ShortExact ∧ (ShortComplex.mk iF qF wF).ShortExact ∧
          (ShortComplex.mk fQ gQ wQ).ShortExact :=
  have hEd := isFiniteLocallyFreeOfRank_dualSheaf T.X₁ (r + 1 + 1) hE
  ⟨(𝔖.bundleDatum X (dualSheaf T.X₁) (r + 1) hEd).bundle,
    (𝔖.bundleDatum X (dualSheaf T.X₁) (r + 1) hEd).proj,
    𝔖.injective_pull_proj X (dualSheaf T.X₁) (r + 1) hEd,
    exists_splitInvertibleSub_of_bundleDatum X T hT r b c hE hF hG
      (𝔖.bundleDatum X (dualSheaf T.X₁) (r + 1) hEd)⟩

end ChernSituation

end Stacks.WeilCohomology

end
