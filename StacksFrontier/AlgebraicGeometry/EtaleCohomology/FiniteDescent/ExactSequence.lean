module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteDescent.CechSheafIterate
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteDescent.CobarExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteDescent.PullbackConservative

/-!
# The Čech resolution of an abelian étale sheaf along a finite surjection

Let `f : X ⟶ Y` be a finite surjective morphism of schemes, let `f_n : X_n ⟶ Y` be the structure
map of the `(n + 1)`-fold fibre product of `X` over `Y`, and for an abelian sheaf `F` on the small
étale site of `Y` put `F_n = f_{n,*}f_n^{-1}F`. The sequence

```
0 ⟶ F ⟶ F_0 ⟶ F_1 ⟶ F_2 ⟶ ⋯
```

is exact, its augmentation being the canonical map `F ⟶ f_*f^{-1}F`.

This is the first assertion of [Stacks, Tag 09Z2].

## Main definitions

* `Stacks.EtaleCohomology.cechSheaf` — the sheaf `F_n = f_{n,*}f_n^{-1}F`.
* `Stacks.EtaleCohomology.cechAug` — the augmentation `F ⟶ F_0`.

## Main results

* `Stacks.EtaleCohomology.exists_exact_cechSheafSequence` — **the exact sequence.**

## Implementation notes

The source checks exactness on stalks at geometric points, using that the stalk of `F_n` at a
geometric point `ȳ` is the direct sum of copies of `F_ȳ` indexed by `E^{n+1}`, for `E` the finite
nonempty set of geometric points of `X` over `ȳ`. That route is not taken here, because this
repository has the stalk of a finite direct image as such a direct sum only for the size-bounded
small étale site of [Stacks, Tag 021B]
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/FinitePushforwardStalk.lean`), whereas the
cohomological half of 09Z2 lives on Mathlib's small étale site; the two sites would have to be
compared before the stalk computation could be used.

The route taken instead stays on one site and replaces the stalk computation by two facts about
the adjunction `f^{-1} ⊣ f_*` alone. First, the sequence above is the augmented cobar complex of
the monad `T = f_*f^{-1}`, because `f_{n,*}f_n^{-1} ≅ T^{n+1}` by one application of finite base
change per Čech level (`Stacks.EtaleCohomology.cechSheafIterateIso`), compatibly with the
augmentations (`Stacks.EtaleCohomology.cechSheafIterateObjIso_zero_unit`). Second, that cobar
complex becomes contractible after applying `f^{-1}`: the triangle identity splits its
coaugmentation and the counit at the outermost slot contracts it, which is
`Stacks.Cobar.exists_exact_cobar`. No base-change comparison is needed for that step, since
`f^{-1}(f_*f^{-1})^{n+1}` and `(f^{-1}f_*)^{n+1}f^{-1}` are the same functor in Lean. Exactness
then descends because `f^{-1}` is faithful and exact for `f` surjective
(`Stacks.EtaleCohomology.exact_of_exact_map_smallEtalePullbackAb`), which is where surjectivity
enters, exactly as the nonemptiness of `E` does in the source.

## References

* [Stacks Project, Tag 09Z2](https://stacks.math.columbia.edu/tag/09Z2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The sheaf `F_n = f_{n,*} f_n^{-1} F` of [Stacks, Tag 09Z2] on the small étale site of `Y`,
the direct image along the structure map of the `(n + 1)`-fold fibre product of `X` over `Y` of
the inverse image of `F`. -/
public abbrev cechSheaf (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (n : ℕ) :
    Sheaf (smallEtaleTopology Y) Ab.{u + 1} :=
  (smallEtalePushforwardAb (cechProjection f n)).obj
    ((smallEtalePullbackAb (cechProjection f n)).obj F)

/-- The canonical augmentation `F ⟶ F_0` of [Stacks, Tag 09Z2]: the unit of the
inverse-image/direct-image adjunction for the zeroth level of the Čech nerve, which is the
canonical map `F ⟶ f_*f^{-1}F`. -/
public abbrev cechAug (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) : F ⟶ cechSheaf f F 0 :=
  (smallEtaleAdjunctionAb (cechProjection f 0)).unit.app F

/-- **[Stacks, Tag 09Z2], the exact sequence.** For a finite surjective morphism `f : X ⟶ Y` of
schemes and an abelian sheaf `F` on the small étale site of `Y`, the sequence

```
0 ⟶ F ⟶ F_0 ⟶ F_1 ⟶ F_2 ⟶ ⋯
```

is exact, where `F_n = f_{n,*}f_n^{-1}F` for `f_n : X_n ⟶ Y` the `(n + 1)`-fold fibre product of
`X` over `Y`, and the augmentation is the canonical map `F ⟶ f_*f^{-1}F`.

Exactness is asserted in the three places the displayed sequence has: the augmentation is a
monomorphism, the sequence is exact at `F_0`, and it is exact at every `F_{n+1}`. -/
public theorem exists_exact_cechSheafSequence [IsFinite f] [Surjective f]
    (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    ∃ (d : ∀ n : ℕ, cechSheaf f F n ⟶ cechSheaf f F (n + 1))
      (haug : cechAug f F ≫ d 0 = 0) (hdd : ∀ n : ℕ, d n ≫ d (n + 1) = 0),
      Mono (cechAug f F) ∧ (ShortComplex.mk _ _ haug).Exact ∧
        ∀ n : ℕ, (ShortComplex.mk _ _ (hdd n)).Exact := by
  have hrefl : ∀ S : ShortComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}),
      (S.map (smallEtalePullbackAb f)).Exact → S.Exact :=
    fun S hS => exact_of_exact_map_smallEtalePullbackAb f S hS
  have hmono : ∀ {P Q : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} (φ : P ⟶ Q),
      Mono ((smallEtalePullbackAb f).map φ) → Mono φ :=
    fun {_ _} φ hφ => mono_of_mono_smallEtalePullbackAb_map f φ hφ
  obtain ⟨d', haug', hdd', hmono', hex0', hex'⟩ :=
    Stacks.Cobar.exists_exact_cobar (smallEtaleAdjunctionAb f) hrefl hmono F
  set e : ∀ n : ℕ, cechSheaf f F n ≅
      ((Stacks.Cobar.mnd (smallEtalePullbackAb f)
        (smallEtalePushforwardAb f)).iterate (n + 1)).obj F :=
    fun n => cechSheafIterateObjIso f n F with he
  have hunit : cechAug f F ≫ (e 0).hom = (smallEtaleAdjunctionAb f).unit.app F :=
    cechSheafIterateObjIso_zero_unit f F
  refine ⟨fun n => (e n).hom ≫ d' n ≫ (e (n + 1)).inv, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, ← Category.assoc, hunit, haug', zero_comp]
  · intro n
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc _ (d' (n + 1)),
      hdd' n, zero_comp, comp_zero]
  · have hm : Mono ((smallEtaleAdjunctionAb f).unit.app F) := hmono'
    exact mono_of_mono_fac hunit
  · refine Stacks.Cobar.exact_of_iso_conj (Iso.refl F) (e 0).symm (e 1).symm ?_ ?_ hex0'
    · rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom, ← hunit, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    · rw [Iso.symm_hom, Iso.symm_hom, Iso.inv_hom_id_assoc]
  · intro n
    refine Stacks.Cobar.exact_of_iso_conj (e n).symm (e (n + 1)).symm (e (n + 2)).symm ?_ ?_
      (hex' n) <;> rw [Iso.symm_hom, Iso.symm_hom, Iso.inv_hom_id_assoc]

end Stacks.EtaleCohomology

end
