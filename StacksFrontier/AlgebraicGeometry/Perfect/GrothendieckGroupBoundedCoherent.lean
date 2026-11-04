module

public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroup
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The middle group of Tag 0FDF: `K₀(D^b(Coh(𝒪_X)))`

Tag 0FDF reads `K₀(Coh(𝒪_X)) = K₀(D^b(Coh(𝒪_X))) = K₀(D^b_Coh(𝒪_X))` for a Noetherian scheme `X`.
The right-hand equality is `AlgebraicGeometry.exists_addEquiv_coherentKZero_K0`. This file supplies
the middle group — the zeroth `K`-group of the bounded derived category *of the abelian category*
`Coh(𝒪_X)`, as opposed to the bounded objects of `D(𝒪_X)` with coherent cohomology — and identifies
it both with `K'₀(X)` and with `K₀(D^b_Coh(𝒪_X))`.

## Main results

* `AlgebraicGeometry.exists_addEquiv_coherentKZero_K0_bounded`: the left-hand equality,
  `K'₀(X) ≃+ K₀(D^b(Coh(𝒪_X)))`, by the class of a coherent sheaf going to the class of that sheaf
  in degree `0`.
* `AlgebraicGeometry.exists_addEquiv_K0_bounded_K0_boundedCoherent`: the two outer groups of the
  chain meet, `K₀(D^b(Coh(𝒪_X))) ≃+ K₀(D^b_Coh(𝒪_X))`, compatibly with the classes of coherent
  sheaves placed in degree `0` on either side.

## Implementation notes

`Coh(𝒪_X)` is an abelian category (`AlgebraicGeometry.coherentModulesAbelian`), so the left-hand
equality is `CategoryTheory.DerivedCategory.Bounded.exists_addEquiv_K0` ([Stacks, Tag 0FCP]) read
at it; it needs a derived category of `Coh(𝒪_X)` itself, which is a separate datum from a derived
category of all `𝒪_X`-modules and is therefore a separate hypothesis. For the second result both
data are present, and the isomorphism is the composite through `K'₀(X)`: the source's own proof
identifies the two outer groups through `K₀(Coh(𝒪_X))` in exactly this way, rather than through the
equivalence `D^b(Coh(𝒪_X)) = D^b_Coh(𝒪_X)` of [Stacks, Tag 0FDA], which it records only as an
alternative.

As with `exists_addEquiv_coherentKZero_K0`, the source assumes `X` Noetherian and no step here uses
it, so it is not assumed. The source's proof of the first equality is Tag 0FCP, which asks only
that the category be abelian; the proof of the second is Tag 0FCS, which asks only that the
subcategory be weak Serre. Both hold over an arbitrary scheme
(`AlgebraicGeometry.coherentModulesAbelian` is Tag 01Y0, stated over an arbitrary ringed space), so
both equalities of Tag 0FDF hold unconditionally and the statements here are correspondingly
stronger than the source's.

## References

* [Stacks Project, Tag 0FDF](https://stacks.math.columbia.edu/tag/0FDF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u d d'

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0FDF.** The Grothendieck group `K'₀(X)` of coherent sheaves on a scheme
`X` is the zeroth `K`-group of `D^b(Coh(𝒪_X))`, the bounded derived category of the abelian
category of coherent `𝒪_X`-modules, by an isomorphism sending the class of a coherent sheaf to the
class of that sheaf placed in degree `0`. -/
@[stacks 0FDF "the identification K₀(Coh(𝒪_X)) = K₀(D^b(Coh(𝒪_X))), the source's first equality",
  sga "6 IV 1.5" "(1.5.3), special case"]
theorem exists_addEquiv_coherentKZero_K0_bounded (X : Scheme.{u})
    [HasDerivedCategory.{d} (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)] :
    ∃ e : CoherentKZero X ≃+ Pretriangulated.K0
        (DerivedCategory.Bounded (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)),
      ∀ F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf,
        e (KZero.mk _ F) = QuotientAddGroup.mk (FreeAbelianGroup.of
          (⟨(DerivedCategory.singleFunctor
                (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) 0).obj F,
            ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩⟩ :
            DerivedCategory.Bounded (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf))) :=
  DerivedCategory.Bounded.exists_addEquiv_K0

/-- **Stacks Project, Tag 0FDF.** For a scheme `X` the two outer groups of the chain of Tag 0FDF
agree: the zeroth `K`-group of `D^b(Coh(𝒪_X))`, the bounded derived category of the abelian
category of coherent `𝒪_X`-modules, is isomorphic to the zeroth `K`-group of `D^b_Coh(𝒪_X)`, the
bounded objects of `D(𝒪_X)` whose cohomology sheaves are coherent. The isomorphism matches the
classes of a coherent sheaf placed in degree `0` on the two sides: it carries the class of `F` in
`D^b(Coh(𝒪_X))` to the class of any object of `D^b_Coh(𝒪_X)` isomorphic to `F` in degree `0`. -/
@[stacks 0FDF "the identification K₀(D^b(Coh(𝒪_X))) = K₀(D^b_Coh(𝒪_X)) of the source's two \
outer groups"]
theorem exists_addEquiv_K0_bounded_K0_boundedCoherent (X : Scheme.{u})
    [HasDerivedCategory.{d} (SheafOfModules.{u} X.ringCatSheaf)]
    [HasDerivedCategory.{d'} (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)] :
    ∃ e : Pretriangulated.K0
        (DerivedCategory.Bounded (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)) ≃+
      Pretriangulated.K0 (DerivedCategoryB.derivedCategoryBBounded
        (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)).FullSubcategory,
      ∀ (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)
        (K : (DerivedCategoryB.derivedCategoryBBounded
            (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)).FullSubcategory),
        (K.obj ≅ (DerivedCategory.singleFunctor
            (SheafOfModules.{u} X.ringCatSheaf) 0).obj F.obj) →
          e (QuotientAddGroup.mk (FreeAbelianGroup.of
              (⟨(DerivedCategory.singleFunctor
                    (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) 0).obj F,
                ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩⟩ :
                DerivedCategory.Bounded
                  (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)))) =
            QuotientAddGroup.mk (FreeAbelianGroup.of K) := by
  obtain ⟨e₁, h₁⟩ := exists_addEquiv_coherentKZero_K0_bounded X
  obtain ⟨e₂, -, h₂⟩ := exists_addEquiv_coherentKZero_K0 X
  refine ⟨e₁.symm.trans e₂, fun F K hK => ?_⟩
  rw [AddEquiv.trans_apply, ← h₁ F, AddEquiv.symm_apply_apply]
  exact h₂ F K hK

end AlgebraicGeometry
