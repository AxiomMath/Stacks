module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralSurjectiveCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralHigherDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.TorsionSheafEmbeddingInvertibility

/-!
# Base change along an integral surjective cover of the base of the sheaf: Tag 0F04

Let `f : X ⟶ S` be a morphism of schemes and let `n` be an integer, as in the condition
`BC(f, n, q₀)` of [Stacks, Tag 0F02]. [Stacks, Tag 0F04] fixes `q ≥ 1`, assumes
`BC(f, n, q - 1)`, and considers the two commutative diagrams

```
X  ←--  X'  ←-h-  Y  ←-π'-  Y'            X'  ←----h' = π' ≫ h----  Y'
|f      |f'       |e        |e'    and    |f'                       |e'
S  ←--  S'  ←-g-  T  ←-π-   T'            S'  ←----g' = π ≫ g-----  T'
```

in which every square of the first is cartesian, `g` is quasi-compact and quasi-separated, `π`
is integral surjective, and the second diagram is the first one with its two right-hand squares
pasted. For an abelian sheaf `F` on the small étale site of `T` annihilated by `n`, put
`F' = π⁻¹F`. The source asserts that if the base change map
`(f')⁻¹ R^q g'_* F' ⟶ R^q h'_* (e')⁻¹ F'` of the pasted diagram is an isomorphism, then so is
the base change map `(f')⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` of the middle square.

The source's proof embeds `F` into `π_*π⁻¹F` — the unit is injective because `π` is
surjective (`Stacks.EtaleCohomology.mono_smallEtaleUnitAb_of_surjective`) — and identifies the
base change map of `π_*F'` with that of `F'` for the pasted diagram, through
`R^q g_*π_* = R^q g'_*`, `e⁻¹π_* = π'_*(e')⁻¹` and `R^q h_*π'_* = R^q h'_*`. Here the base change
maps themselves are never compared. Both are decided by the criterion
`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_iff_map_eq_zero` of
[Stacks, Tag 0F03], which looks only at the target side `R^{q+1}h_* e⁻¹`; and on that side only
two identifications are needed, each used through its naturality alone:
`R^{q+1}(π' ≫ h)_* ≅ R^{q+1}h_* ∘ π'_*`, which holds because `π'` is integral
(`Stacks.EtaleCohomology.integralCompRightDerivedIso`), and the comparison
`e⁻¹π_* ⟶ π'_*(e')⁻¹`, invertible on sheaves annihilated by `n`. The latter is not an appeal to
[Stacks, Tag 0EYP]: the square `Y' = Y ×_T T'` over `T ⟶ S' ⟶ S` is itself one of the diagrams
of [Stacks, Tag 0F02], with `π` quasi-compact and quasi-separated, so its degree-zero base change
map is invertible on `n`-torsion sheaves by the hypothesis `BC(f, n, q)` (Stacks writes
`BC(f, n, q - 1)` with `q ≥ 1`, so degree zero is always included).

Degrees are indexed as in [Stacks, Tag 0F03] as formalized in this library: the running index is
`q : ℕ`, the hypothesis is `BC(f, n, q)`, and the conclusion is about degree `q + 1`. That is
the source's `q ≥ 1` together with its `BC(f, n, q - 1)`.

## Main results

* `Stacks.EtaleCohomology.exists_baseChange_isIso_of_baseChangeHolds` — under `BC(f, n, q)`,
  the degree-zero base change map of `Y' = Y ×_T T'`, read as `e⁻¹π_* ⟶ π'_*(e')⁻¹`, is
  invertible on sheaves annihilated by `n`.
* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_integralSurjective` —
  **[Stacks, Tag 0F04]**, the conclusion of the source.

## Implementation notes

The three cartesian squares of the first diagram are transcribed as `IsPullback` hypotheses; the
pasted diagram is not a separate hypothesis, being `sq₃.paste_horiz sq₂`. Quasi-compactness and
quasi-separatedness of `g` and integrality and surjectivity of `π` are instance hypotheses,
matching the spelling of `Stacks.EtaleCohomology.BaseChangeHolds`. Annihilation of `F` by `n` is
imposed on every section, again as in `BaseChangeHolds`.

The embeddings into injective sheaves of `ℤ/nℤ`-modules that the criterion of
[Stacks, Tag 0F03] needs are `Stacks.EtaleCohomology.torsionEtaleInjectiveEmbedding`, at `F'`
and at `π_*` of the injective sheaf receiving `F'`.

Integrality of `π` is consumed through `π'`, its base change: it makes `π'_*` exact and
`R^{q+1}(π' ≫ h)_* = R^{q+1}h_* ∘ π'_*`. Surjectivity of `π` is what makes the unit
`F ⟶ π_*π⁻¹F` a monomorphism.

## References

* [Stacks Project, Tag 0F04](https://stacks.math.columbia.edu/tag/0F04)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 0F03](https://stacks.math.columbia.edu/tag/0F03)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **Direct image along `π` commutes with base change on `n`-torsion sheaves, under
`BC(f, n, q)`.** In the situation of [Stacks, Tag 0F04], the square `Y' = Y ×_T T'` lies over
`T ⟶ S' ⟶ S` with `Y = X ×_S T` and `π` quasi-compact and quasi-separated, so it is one of the
diagrams the condition `BC(f, n, q)` speaks about. Its degree-zero clause, read through
`R^0π_* = π_*` and `R^0π'_* = π'_*`, is a natural transformation `e⁻¹π_* ⟶ π'_*(e')⁻¹` which is
invertible at every sheaf annihilated by `n`. This is the instance of [Stacks, Tag 0EYP] the
source's proof uses, which is therefore already contained in the hypothesis. -/
public theorem exists_baseChange_isIso_of_baseChangeHolds
    {X S S' X' T Y T' Y' : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (q : ℕ)
    (hbc : BaseChangeHolds f n (q : ℤ))
    (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S') (sq₁ : IsPullback p f' f s)
    (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (sq₂ : IsPullback h e f' g)
    (π : T' ⟶ T) (π' : Y' ⟶ Y) (e' : Y' ⟶ T') (sq₃ : IsPullback π' e' e π)
    [QuasiCompact π] [QuasiSeparated π] :
    ∃ β : smallEtalePushforwardAb π ⋙ smallEtalePullbackAb e ⟶
        smallEtalePullbackAb e' ⋙ smallEtalePushforwardAb π',
      ∀ G : Sheaf (smallEtaleTopology T') Ab.{u + 1},
        (∀ (U : T'.Etale) (y : G.obj.obj (op U)), n • y = 0) → IsIso (β.app G) := by
  have : (smallEtalePushforwardAb π).IsRightAdjoint := ⟨_, ⟨smallEtaleAdjunctionAb π⟩⟩
  have : (smallEtalePushforwardAb π').IsRightAdjoint := ⟨_, ⟨smallEtaleAdjunctionAb π'⟩⟩
  refine ⟨Functor.whiskerRight (smallEtalePushforwardAb π).rightDerivedZeroIsoSelf.inv
      (smallEtalePullbackAb e) ≫ higherBaseChangeMapAb e π π' e' sq₃.w 0 ≫
      Functor.whiskerLeft (smallEtalePullbackAb e')
        (smallEtalePushforwardAb π').rightDerivedZeroIsoSelf.hom, fun G hG ↦ ?_⟩
  have : IsIso ((higherBaseChangeMapAb e π π' e' sq₃.w 0).app G) :=
    hbc (g ≫ s) (h ≫ p) e (sq₂.paste_horiz sq₁) π π' e' sq₃ G hG 0 (by positivity)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

/-- **Stacks Project, Tag 0F04.** With `f : X ⟶ S` and `n` as in [Stacks, Tag 0F02], assume
`BC(f, n, q)`. Consider the commutative diagrams

```
X  ←--  X'  ←-h-  Y  ←-π'-  Y'            X'  ←----h' = π' ≫ h----  Y'
|f      |f'       |e        |e'    and    |f'                       |e'
S  ←--  S'  ←-g-  T  ←-π-   T'            S'  ←----g' = π ≫ g-----  T'
```

with all squares cartesian, `g` quasi-compact and quasi-separated and `π` integral surjective,
and let `F` be an abelian sheaf on the small étale site of `T` annihilated by `n`, with
`F' = π⁻¹F`. If the base change map `(f')⁻¹ R^{q+1} g'_* F' ⟶ R^{q+1} h'_* (e')⁻¹ F'` of the
pasted diagram is an isomorphism, then so is the base change map
`(f')⁻¹ R^{q+1} g_* F ⟶ R^{q+1} h_* e⁻¹ F` of the middle square.

The index convention is that of [Stacks, Tag 0F03] in this library: the source's `q ≥ 1` with
`BC(f, n, q - 1)` is read as degree `q + 1` with `BC(f, n, q)`.

Both base change maps are decided by the criterion
`isIso_higherBaseChangeMapAb_app_iff_map_eq_zero` of [Stacks, Tag 0F03]. Embed `F'` into an
injective sheaf `J'` of `ℤ/nℤ`-modules by `k'`; the hypothesis says `R^{q+1}h'_*(e')⁻¹k' = 0`.
The sheaf `π_*J'` is annihilated by `n` and receives `F` by the monomorphism
`F ⟶ π_*π⁻¹F ⟶ π_*J'`, the unit being injective because `π` is surjective; embedding `π_*J'`
into an injective sheaf of `ℤ/nℤ`-modules gives an embedding of `F` factoring through it. And
`R^{q+1}h_* e⁻¹(π_*k')` vanishes: through the base change transformation
`e⁻¹π_* ⟶ π'_*(e')⁻¹` of `exists_baseChange_isIso_of_baseChangeHolds`, invertible at `J'`, it is
carried to `R^{q+1}h_*(π'_*(e')⁻¹k')`, which is `R^{q+1}h'_*(e')⁻¹k'` read through
`integralCompRightDerivedIso π' h`, `π'` being integral. -/
@[stacks 0F04]
public theorem isIso_higherBaseChangeMapAb_app_of_integralSurjective
    {X S S' X' T Y T' Y' : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (q : ℕ)
    (hbc : BaseChangeHolds f n (q : ℤ))
    (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S') (sq₁ : IsPullback p f' f s)
    (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (sq₂ : IsPullback h e f' g)
    [QuasiCompact g] [QuasiSeparated g]
    (π : T' ⟶ T) (π' : Y' ⟶ Y) (e' : Y' ⟶ T') (sq₃ : IsPullback π' e' e π)
    [IsIntegralHom π] [Surjective π]
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (hF : ∀ (U : T.Etale) (y : F.obj.obj (op U)), n • y = 0)
    (hcollapse : IsIso ((higherBaseChangeMapAb f' (π ≫ g) (π' ≫ h) e'
      (sq₃.paste_horiz sq₂).w (q + 1)).app ((smallEtalePullbackAb π).obj F))) :
    IsIso ((higherBaseChangeMapAb f' g h e sq₂.w (q + 1)).app F) := by
  have : IsIntegralHom π' :=
    MorphismProperty.of_isPullback (P := @IsIntegralHom) sq₃.flip inferInstance
  have : IsSeparated π := IsSeparated.of_isAffineHom π
  have : QuasiCompact (π ≫ g) := inferInstance
  have : QuasiSeparated (π ≫ g) := inferInstance
  obtain ⟨β, hβ⟩ := exists_baseChange_isIso_of_baseChangeHolds f n q hbc s p f' sq₁ g h e sq₂
    π π' e' sq₃
  -- The sheaf `F' = π⁻¹F` and its embedding `k'` into an injective sheaf of `ℤ/nℤ`-modules.
  set F' := (smallEtalePullbackAb π).obj F
  have hF' : ∀ (U : T'.Etale) (y : F'.obj.obj (op U)), n • y = 0 :=
    fun U y ↦ zsmul_eq_zero_of_additive (smallEtalePullbackAb π) F n
      (fun V ↦ hF V.unop) (op U) y
  set J := (SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf T' n)).obj
        (Injective.under (torsionEtaleModule F' hF'))
  have hJ := zsmul_toSheaf_etaleZModRingSheaf_eq_zero T' n
    (Injective.under (torsionEtaleModule F' hF'))
  set k' := torsionEtaleInjectiveEmbedding F' hF'
  have h1 : (higherBaseChangeTarget (π' ≫ h) e' (q + 1)).map k' = 0 :=
    (isIso_higherBaseChangeMapAb_app_iff_map_eq_zero f n q s p f' (π ≫ g) (π' ≫ h) e' hbc sq₁
      (sq₃.paste_horiz sq₂) hF' (Injective.under (torsionEtaleModule F' hF')) k'
      inferInstance).1 hcollapse
  -- `R^{q+1}h_*(π'_*(e')⁻¹k') = 0`.
  have h2 : ((smallEtalePushforwardAb h).rightDerived (q + 1)).map
      ((smallEtalePushforwardAb π').map ((smallEtalePullbackAb e').map k')) = 0 := by
    have hnat := (integralCompRightDerivedIso π' h (q + 1)).hom.naturality
      ((smallEtalePullbackAb e').map k')
    have h1' : ((smallEtalePushforwardAb (π' ≫ h)).rightDerived (q + 1)).map
        ((smallEtalePullbackAb e').map k') = 0 := h1
    rw [h1', comp_zero] at hnat
    exact (Preadditive.IsIso.comp_right_eq_zero _ _).1 hnat
  -- `R^{q+1}h_* e⁻¹(π_*k') = 0`, through the base change transformation `β`.
  have h3 : ((smallEtalePushforwardAb h).rightDerived (q + 1)).map
      ((smallEtalePullbackAb e).map ((smallEtalePushforwardAb π).map k')) = 0 := by
    have : IsIso (β.app J) := hβ _ hJ
    have hnat := congrArg ((smallEtalePushforwardAb h).rightDerived (q + 1)).map
      (β.naturality k')
    simp only [Functor.comp_map, Functor.map_comp, h2, comp_zero] at hnat
    exact (Preadditive.IsIso.comp_right_eq_zero _ _).1 hnat
  -- The target `G = π_*J'` and the embedding of `F` through it.
  set G := (smallEtalePushforwardAb π).obj J
  have hG : ∀ (U : T.Etale) (y : G.obj.obj (op U)), n • y = 0 :=
    fun U y ↦ zsmul_eq_zero_of_additive (smallEtalePushforwardAb π) _ n
      (fun V ↦ hJ V.unop) (op U) y
  have : (smallEtalePushforwardAb π).IsRightAdjoint := ⟨_, ⟨smallEtaleAdjunctionAb π⟩⟩
  have := mono_smallEtaleUnitAb_of_surjective π F
  set j : F ⟶ G := (smallEtaleAdjunctionAb π).unit.app F ≫ (smallEtalePushforwardAb π).map k'
  rw [isIso_higherBaseChangeMapAb_app_iff_map_eq_zero f n q s p f' g h e hbc sq₁ sq₂ hF
    (Injective.under (torsionEtaleModule G hG)) (j ≫ torsionEtaleInjectiveEmbedding G hG)
    (mono_comp _ _)]
  change ((smallEtalePushforwardAb h).rightDerived (q + 1)).map
    ((smallEtalePullbackAb e).map (((smallEtaleAdjunctionAb π).unit.app F ≫
      (smallEtalePushforwardAb π).map k') ≫ torsionEtaleInjectiveEmbedding G hG)) = 0
  simp only [Functor.map_comp, h3, zero_comp, comp_zero]

end Stacks.EtaleCohomology

end
