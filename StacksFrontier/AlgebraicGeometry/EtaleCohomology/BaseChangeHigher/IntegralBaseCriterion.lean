module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralBase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.TorsionSheafEmbedding
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralHigherDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.TorsionSheafEmbeddingInvertibility

/-!
# Base change along an integral morphism of the base: the criterion of Tag 0F05

Let `f : X ⟶ S` be a morphism of schemes and let `n` be an integer, as in the condition
`BC(f, n, q₀)` of [Stacks, Tag 0F02]. [Stacks, Tag 0F05] fixes `q ≥ 1`, assumes
`BC(f, n, q - 1)`, and considers the two commutative diagrams

```
X  ←--  X'  ←-π'-  X''  ←-h'-  Y                X'  ←------h------  Y
|f      |f'        |f''        |e       and     |f'                 |e
S  ←--  S'  ←-π-   S''  ←-g'-  T                S'  ←------g------  T
```

in which every square of the first is cartesian, `g'` is quasi-compact and quasi-separated,
`π` is integral, and the second diagram is the first one collapsed, so that `h = h' ≫ π'` and
`g = g' ≫ π`. For an abelian sheaf `F` on the small étale site of `T` annihilated by `n`, the
source asserts that if the base change map `(f')⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` of the collapsed
diagram is an isomorphism, then so is the base change map
`(f'')⁻¹ R^q g'_* F ⟶ R^q h'_* e⁻¹ F` of the right-hand square of the first diagram. This file
proves that the two are isomorphisms together.

Both diagrams are of the kind `BC(f, n, q - 1)` speaks about: the collapsed one is the
horizontal pasting of the two right-hand squares, with `g' ≫ π` quasi-compact and
quasi-separated because an integral morphism is affine, and the right-hand one sits over
`S'' ⟶ S' ⟶ S` with `X'' = X ×_S S''` by pasting the two left-hand squares. So the criterion
`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_iff_map_eq_zero` of
[Stacks, Tag 0F03] applies to both: choosing an embedding `F ⊂ I` into an injective sheaf of
`ℤ/nℤ`-modules, the base change map of the collapsed diagram is an isomorphism exactly when
`R^q h_* e⁻¹(F ⟶ I)` vanishes, and that of the right-hand square exactly when
`R^q h'_* e⁻¹(F ⟶ I)` does. The two maps correspond under the identification
`R^q h_* = π'_* R^q h'_*` (`Stacks.EtaleCohomology.rightDerivedCompIntegralIso`), `π'` being
integral as a base change of `π`; and `π'_*` is faithful ([Stacks, Tag 04C9]), so one vanishes
exactly when the other does. This is the source's argument — `R^q h_* = π'_* R^q h'_*` and
direct image along an integral morphism detects the conclusion — read on the target of the base
change maps only.

## Main results

* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_iff_of_isIntegralHom` —
  **[Stacks, Tag 0F05]**, in the stronger form that the base change map of the collapsed diagram
  is an isomorphism if and only if that of the right-hand square is.

## Implementation notes

The source identifies the base change map of the collapsed diagram with the direct image along
`π'` of the base change map of the right-hand square, which needs the identification
`(f')⁻¹ π_* = π'_* (f'')⁻¹` of [Stacks, Tag 0EYP] and the compatibility of base change maps
with the two Leray identifications. The criterion of [Stacks, Tag 0F03] makes both unnecessary:
it decides invertibility of a base change map from a single morphism between higher direct
images on the target side, and the Leray identification for `h = h' ≫ π'` is natural, which is
all that the comparison of the two such morphisms requires.

## References

* [Stacks Project, Tag 0F05](https://stacks.math.columbia.edu/tag/0F05)
* [Stacks Project, Tag 0F03](https://stacks.math.columbia.edu/tag/0F03)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 04C9](https://stacks.math.columbia.edu/tag/04C9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **Stacks Project, Tag 0F05.** With `f : X ⟶ S` and `n` as in [Stacks, Tag 0F02], let
`q ≥ 1` and assume `BC(f, n, q - 1)`. Consider the commutative diagrams

```
X  ←--  X'  ←-π'-  X''  ←-h'-  Y                X'  ←------h------  Y
|f      |f'        |f''        |e       and     |f'                 |e
S  ←--  S'  ←-π-   S''  ←-g'-  T                S'  ←------g------  T
```

with all squares cartesian, `g'` quasi-compact and quasi-separated, `π` integral,
`h = h' ≫ π'` and `g = g' ≫ π`, and let `F` be an abelian sheaf on the small étale site of `T`
annihilated by `n`. Then the base change map `(f')⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` of the
collapsed diagram is an isomorphism if and only if the base change map
`(f'')⁻¹ R^q g'_* F ⟶ R^q h'_* e⁻¹ F` of the right-hand square is. The source's statement is the
forward implication.

Both are decided by the criterion `isIso_higherBaseChangeMapAb_app_iff_map_eq_zero` at one
embedding `F ⊂ I` into an injective sheaf of `ℤ/nℤ`-modules, and the two morphisms it asks to
vanish correspond under `rightDerivedCompIntegralIso h' π'`, the faithful functor `π'_*`
carrying one to the other. -/
@[stacks 0F05 "as an equivalence; the source's statement is the forward implication"]
public theorem isIso_higherBaseChangeMapAb_app_iff_of_isIntegralHom
    {X S X' S' X'' S'' Y T : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (q : ℕ) (hq : 1 ≤ q)
    (hbc : BaseChangeHolds f n ((q : ℤ) - 1)) (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
    (sq₁ : IsPullback p f' f s) (π : S'' ⟶ S') (π' : X'' ⟶ X') (f'' : X'' ⟶ S'')
    (sq₂ : IsPullback π' f'' f' π) (g' : T ⟶ S'') (h' : Y ⟶ X'') (e : Y ⟶ T)
    (sq₃ : IsPullback h' e f'' g') [QuasiCompact g'] [QuasiSeparated g'] [IsIntegralHom π]
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (hF : ∀ (U : T.Etale) (x : F.obj.obj (Opposite.op U)), n • x = 0) :
    IsIso ((higherBaseChangeMapAb f' (g' ≫ π) (h' ≫ π') e (sq₃.paste_horiz sq₂).w q).app F) ↔
      IsIso ((higherBaseChangeMapAb f'' g' h' e sq₃.w q).app F) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hbc' : BaseChangeHolds f n (r : ℤ) :=
    fun s p f' hp g h e sq _ _ F hF k hk ↦ hbc s p f' hp g h e sq F hF k (by push_cast; omega)
  have : IsIntegralHom π' :=
    MorphismProperty.of_isPullback (P := @IsIntegralHom) sq₂.flip inferInstance
  have hfaith : (smallEtalePushforwardAb π').Faithful :=
    (smallEtalePushforwardAb_properties_of_isIntegralHom π').2.2.2.1
  have : QuasiCompact (g' ≫ π) := inferInstance
  have : QuasiSeparated (g' ≫ π) := quasiSeparated_comp_of_isIntegralHom g' π
  rw [isIso_higherBaseChangeMapAb_app_iff_map_eq_zero f n r s p f' (g' ≫ π) (h' ≫ π') e hbc'
      sq₁ (sq₃.paste_horiz sq₂) hF (Injective.under (torsionEtaleModule F hF))
      (torsionEtaleInjectiveEmbedding F hF) inferInstance,
    isIso_higherBaseChangeMapAb_app_iff_map_eq_zero f n r (π ≫ s) (π' ≫ p) f'' g' h' e hbc'
      (sq₂.paste_horiz sq₁) sq₃ hF (Injective.under (torsionEtaleModule F hF))
      (torsionEtaleInjectiveEmbedding F hF) inferInstance]
  have hnat := (rightDerivedCompIntegralIso h' π' (r + 1)).hom.naturality
    ((smallEtalePullbackAb e).map (torsionEtaleInjectiveEmbedding F hF))
  have key : (higherBaseChangeTarget (h' ≫ π') e (r + 1)).map
        (torsionEtaleInjectiveEmbedding F hF) =
      (rightDerivedCompIntegralIso h' π' (r + 1)).inv.app _ ≫
        (smallEtalePushforwardAb π').map
          ((higherBaseChangeTarget h' e (r + 1)).map (torsionEtaleInjectiveEmbedding F hF)) ≫
        (rightDerivedCompIntegralIso h' π' (r + 1)).hom.app _ := by
    rw [← cancel_epi ((rightDerivedCompIntegralIso h' π' (r + 1)).hom.app _),
      Iso.hom_inv_id_app_assoc]
    exact hnat.symm
  rw [key, Preadditive.IsIso.comp_left_eq_zero, Preadditive.IsIso.comp_right_eq_zero,
    Functor.map_eq_zero_iff]

end Stacks.EtaleCohomology
