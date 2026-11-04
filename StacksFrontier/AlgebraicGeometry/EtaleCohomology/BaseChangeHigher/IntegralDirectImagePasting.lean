module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralSurjectiveCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedDirectImagePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleBaseChangeAbIntegral
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangeCriteria

/-!
# Higher base change maps across an integral morphism

Consider two commutative squares of schemes sharing the vertical edge `e`,

```
X'  ←-h-  Y  ←-π'-  Y'
|f'       |e        |e'
S'  ←-g-  T  ←-π-   T'
```

the right-hand one cartesian with `π` integral. For an abelian sheaf `𝒢` on the small étale site
of `T'` this file proves that the base change map `(f')⁻¹ R^q g_* (π_* 𝒢) ⟶ R^q h_* e⁻¹ (π_* 𝒢)`
of the left-hand square at `π_* 𝒢` is an isomorphism exactly when the base change map
`(f')⁻¹ R^q (π ≫ g)_* 𝒢 ⟶ R^q (π' ≫ h)_* (e')⁻¹ 𝒢` of the outer rectangle at `𝒢` is, in every
degree `q`.

This is the identification the proof of [Stacks, Tag 0F04] makes in one sentence: direct image
along an integral morphism is exact ([Stacks, Tag 04C2]), so `Rπ_* = π_*` and `Rπ'_* = π'_*`,
and it commutes with base change ([Stacks, Tag 0EYP]), so that the derived base change
comparison of the right-hand square is invertible; by the pasting law for derived base change
comparisons along the direct image legs the comparison of the rectangle is then that of the
left-hand square at `Rπ_* 𝒢 = π_* 𝒢`, up to isomorphisms.

## Main results

* `Stacks.EtaleCohomology.isIso_smallEtaleDerivedBaseChangeAb_of_exact` — the derived base change
  comparison of a commutative square whose two direct images are exact is invertible as soon as
  the underived comparison is.
* `Stacks.EtaleCohomology.isIso_smallEtaleDerivedBaseChangeAb_of_isIntegralHom` — the derived
  base change comparison of a cartesian square along an integral morphism is invertible.
* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_pushforward_iff` — the comparison of
  the base change map of the left-hand square at `π_* 𝒢` with that of the outer rectangle at `𝒢`.
* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_isIso_integralSurjective` —
  **[Stacks, Tag 0F04]**: under `BC(f, n, q)`, for `π` integral surjective and `F` annihilated by
  `n`, the base change map of the middle square at `F` in degree `q + 1` is an isomorphism if the
  base change map of the pasted diagram at `π⁻¹F` is. The conditional form of the same statement,
  `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_isIso_integralSurjectiveCover`, takes
  the identifications this file proves as hypotheses.

## Implementation notes

The degree convention of the tag is that of [Stacks, Tag 0F03] in this library: the source's
`q ≥ 1` with `BC(f, n, q - 1)` is read as degree `q + 1` with `BC(f, n, q)`.

Only invertibility is transported, never a specific identification: the base change map of the
rectangle is the degree-`q` cohomology of the derived comparison of the rectangle, which the
pasting law `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_eq_derivedVPaste_app` writes as
a composite in which only the derived comparison of the left-hand square at `Rπ_* (𝒢[0])` is not
already known to be invertible; and `Rπ_* (𝒢[0])` is isomorphic to `(π_* 𝒢)[0]` because `π_*` is
exact. No compatibility of the relative Leray identifications with the base change maps is
needed for this.

## References

* [Stacks Project, Tag 0F04](https://stacks.math.columbia.edu/tag/0F04)
* [Stacks Project, Tag 0F03](https://stacks.math.columbia.edu/tag/0F03)
* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
* [Stacks Project, Tag 0E46](https://stacks.math.columbia.edu/tag/0E46)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

open Stacks.Cohomology.BaseChange

section Exact

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)

/-- **The derived base change comparison of a square with exact direct images is invertible when
the underived one is.** For a commutative square `h ≫ f' = e ≫ g` of schemes such that direct
image of abelian sheaves along `g` and along `h` is exact, if the underived comparison
`(f')⁻¹ g_* ⟶ h_* e⁻¹` is an isomorphism then so is the derived comparison
`R(f')⁻¹ Rg_* ⟶ Rh_* Re⁻¹` on bounded below derived categories.

All four functors of the square are then exact, so their right derived functors are computed
degreewise and the derived comparison is the degreewise image of the underived one
(`Stacks.Cohomology.BaseChange.isIso_derived_app_Qh_of_acyclic`). -/
public theorem isIso_smallEtaleDerivedBaseChangeAb_of_exact (w : h ≫ f' = e ≫ g)
    [PreservesFiniteLimits (smallEtalePushforwardAb g)]
    [PreservesFiniteColimits (smallEtalePushforwardAb g)]
    [PreservesFiniteLimits (smallEtalePushforwardAb h)]
    [PreservesFiniteColimits (smallEtalePushforwardAb h)]
    [IsIso (smallEtaleBaseChangeAb f' g h e w)] :
    IsIso (smallEtaleDerivedBaseChangeAb f' g h e w) := by
  have ug := exactUnit_isIso (smallEtalePushforwardAb g)
  have uh := exactUnit_isIso (smallEtalePushforwardAb h)
  have ue := exactUnit_isIso (smallEtalePullbackAb e)
  have hQh : ∀ K : HomotopyCategory.Plus (Sheaf (smallEtaleTopology T) Ab.{u + 1}),
      IsIso ((smallEtaleDerivedBaseChangeAb f' g h e w).app (DerivedCategory.Plus.Qh.obj K)) :=
    fun K ↦ isIso_derived_app_Qh_of_acyclic _ _ _ _ _ _ K
      (NatIso.isIso_app_of_isIso _ _) (NatIso.isIso_app_of_isIso _ _)
      (NatIso.isIso_app_of_isIso _ _) fun _ ↦ NatIso.isIso_app_of_isIso _ _
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M ↦ ?_
  exact (NatTrans.isIso_app_iff_of_iso _ (DerivedCategory.Plus.Qh.objObjPreimageIso M)).1
    (hQh _)

end Exact

section Integral

/-- Direct image of abelian sheaves along an integral morphism preserves finite limits and
colimits. -/
private theorem preserves_finite_pushforwardAb_of_isIntegralHom {T T' : Scheme.{u}} (π : T' ⟶ T)
    [IsIntegralHom π] :
    PreservesFiniteLimits (smallEtalePushforwardAb π) ∧
      PreservesFiniteColimits (smallEtalePushforwardAb π) :=
  (exactFunctor_iff _).mp (smallEtalePushforwardAb_exact_of_isIntegralHom π)

variable {Y Y' T T' : Scheme.{u}} (e : Y ⟶ T) (π : T' ⟶ T) (π' : Y' ⟶ Y) (e' : Y' ⟶ T')

/-- **The derived base change comparison along an integral morphism is invertible.** For a
cartesian square
```
Y' --π'--> Y
|e'        |e
v          v
T' --π---> T
```
of schemes with `π` integral, the comparison `Re⁻¹ Rπ_* ⟶ Rπ'_* R(e')⁻¹` on bounded below derived
categories of abelian sheaves on the small étale sites is an isomorphism.

Direct image along `π` and along its base change `π'` is exact ([Stacks, Tag 04C2],
`Stacks.EtaleCohomology.smallEtalePushforwardAb_exact_of_isIntegralHom`), and the underived
comparison is invertible by [Stacks, Tag 0EYP]
(`Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isIntegralHom`). -/
public theorem isIso_smallEtaleDerivedBaseChangeAb_of_isIntegralHom (sq : IsPullback π' e' e π)
    [IsIntegralHom π] :
    IsIso (smallEtaleDerivedBaseChangeAb e π π' e' sq.w) := by
  have : IsIntegralHom π' := MorphismProperty.of_isPullback sq.flip inferInstance
  obtain ⟨_, _⟩ := preserves_finite_pushforwardAb_of_isIntegralHom π
  obtain ⟨_, _⟩ := preserves_finite_pushforwardAb_of_isIntegralHom π'
  have := isIso_smallEtaleBaseChangeAb_of_isIntegralHom e π π' e' sq
  exact isIso_smallEtaleDerivedBaseChangeAb_of_exact e π π' e' sq.w

end Integral

section Paste

variable {S T X' Y T' Y' : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (π : T' ⟶ T) (π' : Y' ⟶ Y) (e' : Y' ⟶ T')

/-- **The base change map at a direct image along an integral morphism is that of the pasted
rectangle.** Consider commutative squares
```
X'  ←-h-  Y  ←-π'-  Y'
|f'       |e        |e'
S   ←-g-  T  ←-π-   T'
```
with the right-hand one cartesian and `π` integral, and an abelian sheaf `𝒢` on the small étale
site of `T'`. In every degree `q`, the base change map
`(f')⁻¹ R^q g_* (π_* 𝒢) ⟶ R^q h_* e⁻¹ (π_* 𝒢)` of the left-hand square is an isomorphism exactly
when the base change map `(f')⁻¹ R^q (π ≫ g)_* 𝒢 ⟶ R^q (π' ≫ h)_* (e')⁻¹ 𝒢` of the outer
rectangle is.

Both are the degree-`q` cohomology of derived base change comparisons
(`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_iff`). By the pasting law along the
direct image legs (`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_eq_derivedVPaste_app`)
the comparison of the rectangle at `𝒢[0]` is the comparison of the left-hand square at
`Rπ_* (𝒢[0])` composed with isomorphisms, the derived comparison of the right-hand square being
invertible (`Stacks.EtaleCohomology.isIso_smallEtaleDerivedBaseChangeAb_of_isIntegralHom`); and
`Rπ_* (𝒢[0]) ≅ (π_* 𝒢)[0]` because `π_*` is exact. -/
public theorem isIso_higherBaseChangeMapAb_app_pushforward_iff (w : h ≫ f' = e ≫ g)
    (sq : IsPullback π' e' e π) [IsIntegralHom π]
    (wo : (π' ≫ h) ≫ f' = e' ≫ (π ≫ g)) (q : ℕ) (G : Sheaf (smallEtaleTopology T') Ab.{u + 1}) :
    IsIso ((higherBaseChangeMapAb f' g h e w q).app ((smallEtalePushforwardAb π).obj G)) ↔
      IsIso ((higherBaseChangeMapAb f' (π ≫ g) (π' ≫ h) e' wo q).app G) := by
  obtain ⟨_, _⟩ := preserves_finite_pushforwardAb_of_isIntegralHom π
  have := isIso_smallEtaleDerivedBaseChangeAb_of_isIntegralHom e π π' e' sq
  let H := DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X') Ab.{u + 1}) (q : ℤ)
  let M := (DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology T') Ab.{u + 1}) 0).obj G
  rw [isIso_higherBaseChangeMapAb_app_iff, isIso_higherBaseChangeMapAb_app_iff,
    smallEtaleDerivedBaseChangeAb_eq_derivedVPaste_app f' g h e π π' e' w sq.w (π ≫ g) rfl
      (π' ≫ h) rfl wo M, Functor.map_comp, Functor.map_comp, Functor.map_comp,
    isIso_comp₄_iff, isIso_comp_right_iff]
  exact NatTrans.isIso_app_iff_of_iso
    (Functor.whiskerRight (smallEtaleDerivedBaseChangeAb f' g h e w) H)
    ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
      (smallEtalePushforwardAb π) 0).app G)

end Paste

/-! ### Stacks 0F04 -/

section IntegralSurjectiveCover

open Opposite

/-- **Stacks Project, Tag 0F04.** With `f : X ⟶ S` and `n` as in [Stacks, Tag 0F02], assume
`BC(f, n, q)`. Consider the commutative diagrams

```
X  ←--  X'  ←-h-  Y  ←-π'-  Y'            X'  ←----h' = π' ≫ h----  Y'
|f      |f'       |e        |e'    and    |f'                       |e'
S  ←--  S'  ←-g-  T  ←-π-   T'            S'  ←----g' = π ≫ g-----  T'
```

with all squares cartesian, `g` quasi-compact and quasi-separated and `π` integral surjective,
and let `F` be an abelian sheaf on the small étale site of `T` annihilated by `n`, with
`F' = π⁻¹F`. If the base change map
`(f')⁻¹ R^{q+1} g'_* F' ⟶ R^{q+1} h'_* (e')⁻¹ F'` of the pasted diagram is an isomorphism, then
so is the base change map `(f')⁻¹ R^{q+1} g_* F ⟶ R^{q+1} h_* e⁻¹ F` of the middle square.

The index convention is that of [Stacks, Tag 0F03] in this library: the source's `q ≥ 1` with
`BC(f, n, q - 1)` is read as degree `q + 1` with `BC(f, n, q)`.

The unit `F ⟶ π_*π⁻¹F` is a monomorphism because `π` is surjective
(`Stacks.EtaleCohomology.mono_smallEtaleUnitAb_of_surjective`) and `π_*π⁻¹F` is annihilated by
`n` (`Stacks.EtaleCohomology.zsmul_eq_zero_of_additive`), so by parts (1) and (2) of
[Stacks, Tag 0F03] it suffices that the base change map of the middle square at `π_*π⁻¹F` is an
isomorphism. That is the hypothesis, read through
`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_pushforward_iff`, which is where
[Stacks, Tag 0EYP], [Stacks, Tag 04C2] and the relative Leray identification `Rπ_* = π_*` enter. -/
@[stacks 0F04]
public theorem isIso_higherBaseChangeMapAb_app_of_isIso_integralSurjective
    {X S S' X' T Y T' Y' : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (q : ℕ)
    (hbc : BaseChangeHolds f n (q : ℤ))
    (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S') (sq₁ : IsPullback p f' f s)
    (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (sq₂ : IsPullback h e f' g)
    [QuasiCompact g] [QuasiSeparated g]
    (π : T' ⟶ T) (π' : Y' ⟶ Y) (e' : Y' ⟶ T') (sq₃ : IsPullback π' e' e π)
    [IsIntegralHom π] [Surjective π]
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (hF : ∀ (U : T.Etale) (y : F.obj.obj (op U)), n • y = 0)
    (hpaste : IsIso ((higherBaseChangeMapAb f' (π ≫ g) (π' ≫ h) e'
      (sq₃.paste_horiz sq₂).w (q + 1)).app ((smallEtalePullbackAb π).obj F))) :
    IsIso ((higherBaseChangeMapAb f' g h e sq₂.w (q + 1)).app F) := by
  -- The unit `F ⟶ π_*π⁻¹F`, and the two facts parts (1) and (2) of 0F03 need about it.
  have hi : Mono ((smallEtaleAdjunctionAb π).unit.app F) :=
    mono_smallEtaleUnitAb_of_surjective π F
  have hGn : ∀ (U : T.Etale)
      (z : ToType (((smallEtalePushforwardAb π).obj
        ((smallEtalePullbackAb π).obj F)).obj.obj (op U))), n • z = 0 :=
    fun U z ↦ zsmul_eq_zero_of_additive
      (smallEtalePullbackAb π ⋙ smallEtalePushforwardAb π) F n
      (fun V y ↦ hF V.unop y) (op U) z
  -- The base change map at `π_*π⁻¹F` is that of the pasted diagram at `π⁻¹F`.
  have hGiso : IsIso ((higherBaseChangeMapAb f' g h e sq₂.w (q + 1)).app
      ((smallEtalePushforwardAb π).obj ((smallEtalePullbackAb π).obj F))) :=
    (isIso_higherBaseChangeMapAb_app_pushforward_iff f' g h e π π' e' sq₂.w sq₃
      (sq₃.paste_horiz sq₂).w (q + 1) ((smallEtalePullbackAb π).obj F)).2 hpaste
  -- Part (1) of 0F03 at `F`, and part (2) of 0F03 for `F ⊂ π_*π⁻¹F`.
  have hmono : Mono ((higherBaseChangeMapAb f' g h e sq₂.w (q + 1)).app F) :=
    mono_higherBaseChangeMapAb_app_of_annihilated f n q s p f' g h e hbc sq₁ sq₂ hF
  have hcoker := mono_cokernelMap_higherBaseChangeMapAb_app_of_annihilated
    f n q s p f' g h e hbc sq₁ sq₂
    (F := F) (G := (smallEtalePushforwardAb π).obj ((smallEtalePullbackAb π).obj F))
    ((smallEtaleAdjunctionAb π).unit.app F) hi hF hGn
  exact Stacks.Cohomology.BaseChange.isIso_of_mono_of_isIso_of_mono_cokernelMap
    ((higherBaseChangeMapAb f' g h e sq₂.w (q + 1)).app F)
    ((higherBaseChangeMapAb f' g h e sq₂.w (q + 1)).app
      ((smallEtalePushforwardAb π).obj ((smallEtalePullbackAb π).obj F)))
    hmono hGiso hcoker

end IntegralSurjectiveCover

end Stacks.EtaleCohomology

end
