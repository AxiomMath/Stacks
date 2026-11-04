module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreAbelian
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 03RZ in one statement

Let `X` be a scheme of a big étale site. Tag 03RZ asserts three closure properties of the
constructible sheaves on the small étale site of `X`:

1. the constructible sheaves of sets are closed under finite limits and under finite colimits;
2. the constructible abelian sheaves form a weak Serre subcategory of all abelian sheaves; and
3. for `Λ` a Noetherian ring, the constructible sheaves of `Λ`-modules form a weak Serre
   subcategory of all sheaves of `Λ`-modules.

Each part is already a theorem of this library, stating that part alone. This file conjoins the
three into the single statement of the tag, forwarding each conjunct to the theorem that proves
it; those three registrations are retained.

## Main results

* `AlgebraicGeometry.isConstructibleSetSheaf_limit_colimit_and_isWeakSerreClass_abelian_and_module`
  — the whole of Stacks 03RZ.

## Implementation notes

The weak Serre condition is `CategoryTheory.ObjectProperty.IsWeakSerreClass`, the form of Tag
0754: a strictly full subcategory containing `0` and closed under kernels, cokernels **and
extensions**. Closure under extensions is a field of that class and not an extra hypothesis, so
parts (2) and (3) here are the full assertions of the source and not their kernel/cokernel
halves.

Part (3)'s ring `Λ` is a `Ring` and not a `CommRing`, which is more general than the source, and
it lives in its own universe `r`. The three hypotheses `Λ`, `Ring Λ` and `IsNoetherianRing Λ`
belong to part (3) alone: parts (1) and (2) do not mention `Λ` and are proved without it. No
hypothesis beyond those is assumed — in particular there is no hypothesis on the scheme `X`, and
no instance that the source does not name.

## References

* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe v u w r

/-- **Stacks 03RZ.** Let `X` be a scheme of a big étale site and `Λ` a Noetherian ring. Then

1. a finite limit and a finite colimit of constructible sheaves of sets on the small étale site
   of `X` are constructible;
2. the constructible abelian sheaves on that site form a weak Serre subcategory of all abelian
   sheaves on it; and
3. the constructible sheaves of `Λ`-modules on that site form a weak Serre subcategory of all
   sheaves of `Λ`-modules on it.

This is the whole tag in one statement, under no hypothesis on `X` and none on `Λ` beyond the
source's own Noetherianness, which part (3) alone uses. Each part is proved by the theorem that
states it alone: `AlgebraicGeometry.isConstructibleSetSheaf_limit` and
`AlgebraicGeometry.isConstructibleSetSheaf_colimit` for part (1),
`AlgebraicGeometry.constructibleAbelianSheaf_isWeakSerreClass` for part (2), and
`AlgebraicGeometry.SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf` for part (3). Those
four registrations are retained, each stating its own part.

The three parts are independent facts and not a chain: part (1) is about sheaves of sets and is
not used for parts (2) and (3), which reduce to Tag 093U (2) and Tag 093U (3) respectively, so
the conjunction asserts strictly more than any one of them. -/
@[stacks 03RZ "the whole tag: part (1) finite limits and finite colimits of constructible sheaves
of sets are constructible, part (2) the constructible abelian sheaves are a weak Serre
subcategory, part (3) the constructible sheaves of modules over a Noetherian ring are a weak
Serre subcategory. Unconditional: no hypothesis on the scheme and no instance the source does not
name; part (3)'s ring is a Ring rather than a CommRing, which is more general than the source,
and its Noetherian hypothesis is used by part (3) alone. The four component registrations are
retained.", sga "4 IX 2.6"]
public theorem isConstructibleSetSheaf_limit_colimit_and_isWeakSerreClass_abelian_and_module
    (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ] [IsNoetherianRing Λ] :
    (∀ (I : Type v) [SmallCategory I] [FinCategory I]
        (F : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))),
        (∀ i, IsConstructibleSetSheaf B X (F.obj i)) →
          IsConstructibleSetSheaf B X (limit F) ∧
            IsConstructibleSetSheaf B X (colimit F)) ∧
      ObjectProperty.IsWeakSerreClass
        (fun F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} =>
          IsConstructibleAbelianSheaf B X F) ∧
      ObjectProperty.IsWeakSerreClass
        (fun F : Sheaf (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) w} Λ) => IsConstructibleModuleSheaf B X Λ F) :=
  ⟨fun _ _ _ F hF =>
      ⟨isConstructibleSetSheaf_limit B X F hF, isConstructibleSetSheaf_colimit B X F hF⟩,
    constructibleAbelianSheaf_isWeakSerreClass B X,
    SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, w, r} B X Λ⟩

end AlgebraicGeometry

end
