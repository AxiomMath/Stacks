module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.DerivedBaseChangeHomologyCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralBase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedDirectImagePasting
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images and an integral morphism of the base, at the source's hypotheses

`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralBase` reduces
[Stacks, Tag 0F05] to three identifications that the source's proof uses: [Stacks, Tag 0EYP] for
the middle square, the two relative Leray identifications along the integral morphisms `π` and
`π'`, and the compatibility of the base change maps of [Stacks, Tag 0F02] with them. This file
supplies all three, and states the tag with no hypothesis beyond the source's.

* `Stacks.EtaleCohomology.isIntegralHom_of_isPullback` — integrality passes to the base change
  `π'` of `π` along the cartesian square `X'' = X' ×_{S'} S''`.
* `Stacks.EtaleCohomology.integralLerayIso` — the relative Leray identification
  `R^q (f ≫ g)_* ≅ g_* R^q f_*` for `g` integral, from exactness of `g_*`
  ([Stacks, Tag 04C2]); no spectral sequence is needed.
* `Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_app_of_annihilated` — [Stacks, Tag 0EYP]
  in the abelian small-étale setting at an abelian sheaf annihilated by `n`, from the condition
  `BC(f, n, q₀)` of [Stacks, Tag 0F02], `q₀ ≥ 0`.
* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_isIso_collapsed_of_bc` —
  **[Stacks, Tag 0F05]**: the base change map of the right-hand square is an isomorphism as soon
  as the one of the collapsed diagram is. The pasting compatibility is
  `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_eq_derivedVPaste_app`, and
  [Stacks, Tag 0EYP] is the source's own `BC(f, n, q - 1)` read in degree zero.

## References

* [Stacks Project, Tag 0F05](https://stacks.math.columbia.edu/tag/0F05)
* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- Integrality passes to a base change: if `π` is integral and the square
`X'' = X' ×_{S'} S''` is cartesian, then `π'` is integral. -/
public theorem isIntegralHom_of_isPullback {X' X'' S' S'' : Scheme.{u}} {π : S'' ⟶ S'}
    {π' : X'' ⟶ X'} {f' : X' ⟶ S'} {f'' : X'' ⟶ S''} (sq : IsPullback π' f'' f' π)
    [IsIntegralHom π] : IsIntegralHom π' :=
  MorphismProperty.of_isPullback (P := @IsIntegralHom) sq.flip inferInstance

/-- **The relative Leray identification along an integral morphism**,
`R^q (f ≫ g)_* ≅ g_* R^q f_*`, for abelian sheaves on the small étale sites and `g` integral.

No spectral sequence is needed: direct image along an integral morphism is exact by
[Stacks, Tag 04C2], so `Rg_* = g_*`, and an exact functor commutes with right derived functors.
The identification is therefore
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`, which is that general statement,
applied to the composition isomorphism
`Stacks.EtaleCohomology.smallEtalePushforwardAbCompIso`. This is the collapse of the relative
Leray spectral sequence of [Stacks, Tag 0734] that the proof of [Stacks, Tag 0F05] uses.

Integrality of `g` is an explicit argument rather than an instance hypothesis, because the
consumer applies this to the base change `π'` of an integral `π`, whose integrality is produced
by `Stacks.EtaleCohomology.isIntegralHom_of_isPullback` and is not found by instance search. -/
@[sga "4½ Arcata 2.3.4" "special case"]
public noncomputable def integralLerayIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : IsIntegralHom g) (q : ℕ) :
    (smallEtalePushforwardAb (f ≫ g)).rightDerived q ≅
      (smallEtalePushforwardAb f).rightDerived q ⋙ smallEtalePushforwardAb g :=
  haveI := hg
  haveI : (smallEtalePushforwardAb g).IsRightAdjoint := ⟨_, ⟨smallEtaleAdjunctionAb g⟩⟩
  haveI : PreservesFiniteLimits (smallEtalePushforwardAb g) := inferInstance
  haveI : (smallEtalePushforwardAb g).PreservesEpimorphisms :=
    smallEtalePushforwardAb_preservesEpimorphisms_of_isIntegralHom g
  haveI := Functor.preservesHomology_of_preservesEpis_and_kernels (smallEtalePushforwardAb g)
  (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (smallEtalePushforwardAb f)
    (smallEtalePushforwardAb g) (smallEtalePushforwardAb (f ≫ g))
    (smallEtalePushforwardAbCompIso f g) q).symm

/-- Direct image along an integral morphism preserves finite limits and finite colimits. -/
private theorem preservesFinite_smallEtalePushforwardAb_of_isIntegralHom {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIntegralHom g] :
    PreservesFiniteLimits (smallEtalePushforwardAb g) ∧
      PreservesFiniteColimits (smallEtalePushforwardAb g) :=
  (exactFunctor_iff _).mp (smallEtalePushforwardAb_exact_of_isIntegralHom g)

/-- **[Stacks, Tag 0EYP] in the abelian small-étale setting, at an abelian sheaf annihilated by
`n`.** With `f : X ⟶ S` and `n` as in [Stacks, Tag 0F02], assume `BC(f, n, q₀)` for some
`q₀ ≥ 0`, let `X' = X ×_S S'` and let

```
X'' --π'--> X'
|f''        |f'
v           v
S'' --π---> S'
```

be cartesian with `π` integral. Then the underived base change map `(f')⁻¹ π_* ⟶ π'_* (f'')⁻¹`
of that square is an isomorphism at every abelian sheaf `G` on the small étale site of `S''`
annihilated by `n`.

This is the condition `BC(f, n, q₀)` read in degree zero. The condition applies: `π` is
integral, hence affine, hence quasi-compact and separated, so quasi-compact and quasi-separated,
and `0 ≤ q₀`. What it delivers is the degree-zero base change map of [Stacks, Tag 0F02], which
is the degree-zero cohomology of the *derived* comparison at `G[0]`; since both legs of the
square's direct image are exact — `π` is integral and so is its base change `π'`, by
`Stacks.EtaleCohomology.isIntegralHom_of_isPullback` — that cohomology already determines the
underived comparison, which is
`Stacks.Cohomology.BaseChange.isIso_app_of_isIso_homology_zero_derived`. -/
public theorem isIso_smallEtaleBaseChangeAb_app_of_annihilated
    {X S X' S' X'' S'' : Scheme.{u}} (f : X ⟶ S) (n q₀ : ℤ) (hq₀ : 0 ≤ q₀)
    (hbc : BaseChangeHolds f n q₀) (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
    (sq₁ : IsPullback p f' f s) (π : S'' ⟶ S') (π' : X'' ⟶ X') (f'' : X'' ⟶ S'')
    (sq₂ : IsPullback π' f'' f' π) [IsIntegralHom π]
    (G : Sheaf (smallEtaleTopology S'') Ab.{u + 1})
    (hG : ∀ (U : S''.Etale) (x : G.obj.obj (Opposite.op U)), n • x = 0) :
    IsIso ((smallEtaleBaseChangeAb f' π π' f'' sq₂.w).app G) := by
  have : IsSeparated π := IsSeparated.of_isAffineHom π
  have hπ' : IsIntegralHom π' := isIntegralHom_of_isPullback sq₂
  obtain ⟨_, _⟩ := preservesFinite_smallEtalePushforwardAb_of_isIntegralHom π
  obtain ⟨_, _⟩ := preservesFinite_smallEtalePushforwardAb_of_isIntegralHom π'
  have h0 := hbc s p f' sq₁ π π' f'' sq₂ G hG 0 (by simpa using hq₀)
  rw [isIso_higherBaseChangeMapAb_app_iff, smallEtaleDerivedBaseChangeAb_eq] at h0
  exact Stacks.Cohomology.BaseChange.isIso_app_of_isIso_homology_zero_derived
    (smallEtalePushforwardAb π) (smallEtalePushforwardAb π') (smallEtalePullbackAb f')
    (smallEtalePullbackAb f'') (smallEtaleBaseChangeAb f' π π' f'' sq₂.w) _ G h0

/-- The third of four composable morphisms is invertible when the composite and the other three
are. Stated on variables because the morphisms it is applied to are components of comparisons of
derived functors at sheaves on small étale sites, where writing them out is unreadable; the
pasting law for the derived base change comparison presents the collapsed diagram's comparison
as exactly such a fourfold composite. -/
private theorem isIso_mid_of_comp₄ {E : Type*} [Category* E] {O₁ O₂ O₃ O₄ O₅ : E}
    (a : O₁ ⟶ O₂) (b : O₂ ⟶ O₃) (c : O₃ ⟶ O₄) (d : O₄ ⟶ O₅)
    (ha : IsIso a) (hb : IsIso b) (hd : IsIso d) (h : IsIso (a ≫ b ≫ c ≫ d)) : IsIso c := by
  have := ha
  have := hb
  have := hd
  have := h
  have : IsIso (b ≫ c ≫ d) := IsIso.of_isIso_comp_left a _
  have : IsIso (c ≫ d) := IsIso.of_isIso_comp_left b _
  have hc : c = (c ≫ d) ≫ inv d := by simp
  rw [hc]
  infer_instance

/-- **Stacks Project, Tag 0F05.** With `f : X ⟶ S` and `n` as in [Stacks, Tag 0F02], let
`q ≥ 1` and assume `BC(f, n, q - 1)`. Consider the commutative diagrams

```
X  ←--  X'  ←-π'-  X''  ←-h'-  Y                X'  ←------h------  Y
|f      |f'        |f''        |e       and     |f'                 |e
S  ←--  S'  ←-π-   S''  ←-g'-  T                S'  ←------g------  T
```

with all squares cartesian, `g'` quasi-compact and quasi-separated, `π` integral,
`h = h' ≫ π'` and `g = g' ≫ π`, and let `F` be an abelian sheaf on the small étale site of `T`
annihilated by `n`. If the base change map `(f')⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` of the collapsed
diagram is an isomorphism, then so is the base change map
`(f'')⁻¹ R^q g'_* F ⟶ R^q h'_* e⁻¹ F` of the right-hand square.

The two relative Leray identifications the source's proof uses are supplied, not assumed: they
are `Stacks.EtaleCohomology.integralLerayIso` for `g = g' ≫ π` and for `h = h' ≫ π'`, the
second along the base change `π'` of `π`, whose integrality is
`Stacks.EtaleCohomology.isIntegralHom_of_isPullback`.

The remaining identification, [Stacks, Tag 0EYP] for the middle square, is not assumed either:
it is needed only at the cohomology sheaves of `Rg'_* F`, which are annihilated by `n` because
`F` is, and there it is the source's own `BC(f, n, q - 1)` read in degree zero, which is
`Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_app_of_annihilated`. That only the
cohomology sheaves matter is
`Stacks.Cohomology.BaseChange.isIso_derived_app_iff_homology`, both legs of the middle square's
direct image being exact.

The pasting compatibility the source elides is *not* assumed: it is
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_eq_derivedVPaste_app`, the pasting law for
the derived base change comparison along the direct image legs, whose two leg comparisons
`Rg'_* ⋙ Rπ_* ≅ R(g' ≫ π)_*` and `Rh'_* ⋙ Rπ'_* ≅ R(h' ≫ π')_*` are the derived form of the
relative Leray identification for an integral morphism. Of the four factors of that pasting,
two are isomorphisms outright, the third is one by the preceding paragraph, and the fourth is
the direct image
along `π'` of the base change map of the right-hand square; the conclusion is then
`isIso_pushforward_higherBaseChangeMapAb_app_iff` in the form carried by
`Stacks.EtaleCohomology.isIso_smallEtalePushforwardAb_map_iff_of_isIntegralHom`. -/
@[stacks 0F05]
public theorem isIso_higherBaseChangeMapAb_app_of_isIso_collapsed_of_bc
    {X S X' S' X'' S'' Y T : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (q : ℕ) (hq : 1 ≤ q)
    (hbc : BaseChangeHolds f n ((q : ℤ) - 1)) (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
    (sq₁ : IsPullback p f' f s) (π : S'' ⟶ S') (π' : X'' ⟶ X') (f'' : X'' ⟶ S'')
    (sq₂ : IsPullback π' f'' f' π) (g' : T ⟶ S'') (h' : Y ⟶ X'') (e : Y ⟶ T)
    (sq₃ : IsPullback h' e f'' g') [QuasiCompact g'] [QuasiSeparated g'] [IsIntegralHom π]
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (hF : ∀ (U : T.Etale) (x : F.obj.obj (Opposite.op U)), n • x = 0)
    (hcollapse : IsIso
      ((higherBaseChangeMapAb f' (g' ≫ π) (h' ≫ π') e (sq₃.paste_horiz sq₂).w q).app F)) :
    IsIso ((higherBaseChangeMapAb f'' g' h' e sq₃.w q).app F) := by
  have hπ' : IsIntegralHom π' := isIntegralHom_of_isPullback sq₂
  obtain ⟨_, _⟩ := preservesFinite_smallEtalePushforwardAb_of_isIntegralHom π
  obtain ⟨_, _⟩ := preservesFinite_smallEtalePushforwardAb_of_isIntegralHom π'
  let : (smallEtalePushforwardAb g').rightDerivedFunctorPlus.CommShift ℤ :=
    CategoryTheory.Functor.commShiftRightDerivedFunctorPlus (smallEtalePushforwardAb g')
  have : (smallEtalePushforwardAb g').rightDerivedFunctorPlus.IsTriangulated :=
    CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus (smallEtalePushforwardAb g')
  have : (smallEtalePushforwardAb g').rightDerivedFunctorPlus.Additive := inferInstance
  have hid : n • (𝟙 F) = 0 :=
    (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff F n).2 fun U x => hF U.unop x
  have hmid : IsIso ((smallEtaleDerivedBaseChangeAb f' π π' f'' sq₂.w).app
      ((smallEtalePushforwardAb g').rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj F))) := by
    rw [smallEtaleDerivedBaseChangeAb_eq,
      Stacks.Cohomology.BaseChange.isIso_derived_app_iff_homology]
    intro j
    have hz : n • 𝟙 ((DerivedCategory.Plus.singleFunctor
            (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0 ⋙
          (smallEtalePushforwardAb g').rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor
            (Sheaf (smallEtaleTopology S'') Ab.{u + 1}) j).obj F) = 0 := by
      rw [← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_zsmul, hid,
        CategoryTheory.Functor.map_zero]
    exact isIso_smallEtaleBaseChangeAb_app_of_annihilated f n ((q : ℤ) - 1) (by omega) hbc
      s p f' sq₁ π π' f'' sq₂ _
      fun U x => (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff _ n).1 hz (Opposite.op U) x
  rw [isIso_higherBaseChangeMapAb_app_iff] at hcollapse ⊢
  rw [smallEtaleDerivedBaseChangeAb_eq_derivedVPaste_app
    f' π π' f'' g' h' e sq₂.w sq₃.w (g' ≫ π) rfl (h' ≫ π') rfl] at hcollapse
  simp only [Functor.map_comp] at hcollapse
  have hC : IsIso ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (smallEtaleTopology X') Ab.{u + 1}) (q : ℤ)).map
      ((smallEtalePushforwardAb π').rightDerivedFunctorPlus.map
        ((smallEtaleDerivedBaseChangeAb f'' g' h' e sq₃.w).app
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj F)))) := by
    refine isIso_mid_of_comp₄ _ _ _ _ ?_ ?_ ?_ hcollapse <;> infer_instance
  have hnat := (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
      (smallEtalePushforwardAb π') (q : ℤ)).hom.naturality
    ((smallEtaleDerivedBaseChangeAb f'' g' h' e sq₃.w).app
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj F))
  simp only [Functor.comp_map] at hnat
  have := hC
  have hpush : IsIso ((DerivedCategory.Plus.homologyFunctor
        (Sheaf (smallEtaleTopology X') Ab.{u + 1}) (q : ℤ)).map
        ((smallEtalePushforwardAb π').rightDerivedFunctorPlus.map
          ((smallEtaleDerivedBaseChangeAb f'' g' h' e sq₃.w).app
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj F))) ≫
      (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
        (smallEtalePushforwardAb π') (q : ℤ)).hom.app _) := inferInstance
  rw [hnat] at hpush
  have := hpush
  exact (isIso_smallEtalePushforwardAb_map_iff_of_isIntegralHom π' _).mp
    (IsIso.of_isIso_comp_left ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
      (smallEtalePushforwardAb π') (q : ℤ)).hom.app _) _)

end Stacks.EtaleCohomology

end
