module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyOverFieldSurjective
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward

/-!
# Stacks 0FBW through any classes characterized by the rule of Stacks 0B78

The surjectivity half of Stacks 0FBW in
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyOverFieldSurjective` uses the class
of Stacks 0B78 for the structure morphism of each flat scheme `W` over the base, through its cap
operation alone. This file states it for any Gysin system over which those classes exist, in the
sense of `Stacks.Chow.IsBivariantFlatPullback`, in place of the inputs Stacks 02RG and 0B71 of the
construction `Stacks.Chow.flatPullbackBivariantClass`. Over the Gysin system of an invertible
module they exist with nothing assumed: `Stacks.Chow.flatPullbackBivariantClassOfInvertible` and
`Stacks.Chow.isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible`.

## Main results

* `Stacks.Chow.bivariantToBaseEval_of_isBivariantFlatPullback` — a class characterized by the rule
  of Stacks 0B78 for the structure morphism of `W` evaluates to
  `Stacks.Chow.flatPullbackBaseClass`.
* `Stacks.Chow.bivariantToBaseEval_properPushforward_of_isBivariantFlatPullback` — the step of the
  proof of Stacks 0FBW that produces the bivariant classes.
* `Stacks.Chow.bivariantToBaseEval_surjective_of_isBivariantFlatPullback`,
  `Stacks.Chow.bivariantToBaseEval_bijective_of_isBivariantFlatPullback`,
  `Stacks.Chow.bivariantToBaseEquivOfIsBivariantFlatPullback` — **Stacks 0FBW**.
* `Stacks.Chow.exists_isBivariantFlatPullback_ofInvertible` — over the Gysin system of an
  invertible module the classes these statements ask for exist, with nothing assumed.

## References

* [Stacks Project, Tag 0FBW](https://stacks.math.columbia.edu/tag/0FBW)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- A class characterized by the rule of Stacks 0B78 for the structure morphism of `W` evaluates,
under the canonical map of Stacks 0FBW for `W`, to `Stacks.Chow.flatPullbackBaseClass`: both are
the flat pullback of `[Spec k]` along the base change of the structure morphism, read through the
same collapse. -/
theorem bivariantToBaseEval_of_isBivariantFlatPullback (C : ChowSituation.{u})
    (G : GysinSystem C) {W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW] [Flat sW]
    (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension sW r) (hS1 : FlatPullbackDescends C)
    {c : BivariantClass C G sW (𝟙 C.S) sW (Category.comp_id sW) (-(r : ℤ))}
    (hc : IsBivariantFlatPullback C G sW (𝟙 C.S) sW (Category.comp_id sW) r hr hS1 c) :
    bivariantToBaseEval C G sW (-(r : ℤ)) c = flatPullbackBaseClass C sW r hr hS1 := by
  rw [bivariantToBaseEval_apply, hc]
  rfl

/-- Over the Gysin system of an invertible module, every scheme `W` flat of relative dimension `r`
over the base carries a class characterized by the rule of Stacks 0B78 for its structure morphism,
with nothing assumed: `Stacks.Chow.flatPullbackBivariantClassOfInvertible`. -/
theorem exists_isBivariantFlatPullback_ofInvertible (C : ChowSituation.{u}) {W : Scheme.{u}}
    (sW : W ⟶ C.S) [LocallyOfFiniteType sW] [Flat sW] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension sW r) :
    ∃ c : BivariantClass C (gysinSystemOfInvertible C) sW (𝟙 C.S) sW (Category.comp_id sW)
        (-(r : ℤ)),
      IsBivariantFlatPullback C (gysinSystemOfInvertible C) sW (𝟙 C.S) sW (Category.comp_id sW) r
        hr (flatPullbackDescends C) c :=
  ⟨flatPullbackBivariantClassOfInvertible C sW (𝟙 C.S) sW (Category.comp_id sW) r hr,
    isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C sW (𝟙 C.S) sW
      (Category.comp_id sW) r hr⟩

section Surjective

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (p : ℤ)

/-- **The step of the proof of Stacks 0FBW that produces the bivariant classes.** Let
`g : W ⟶ X` be proper, with `W` flat of relative dimension `r` over the base, and let `c` be a
class characterized by the rule of Stacks 0B78 for the structure morphism of `W`. A proper
pushforward `d` of `c` along `g` is a bivariant class of degree `-r` for the structure morphism of
`X` whose image under the canonical map of Stacks 0FBW is the proper pushforward along `g` of
`Stacks.Chow.flatPullbackBaseClass`. -/
theorem bivariantToBaseEval_properPushforward_of_isBivariantFlatPullback
    (hS1 : FlatPullbackDescends C) (hpp : ProperPushforwardDescends C) {W : Scheme.{u}}
    (g : W ⟶ X) [IsProper g] [LocallyOfFiniteType (g ≫ sX)] [Flat (g ≫ sX)] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension (g ≫ sX) r)
    {c : BivariantClass C G (g ≫ sX) (𝟙 C.S) (g ≫ sX)
      (comp_comp_structureMorphism_eq (rfl : g ≫ sX = g ≫ sX) (Category.comp_id sX))
      (-(r : ℤ))}
    (hc : IsBivariantFlatPullback C G (g ≫ sX) (𝟙 C.S) (g ≫ sX)
      (comp_comp_structureMorphism_eq (rfl : g ≫ sX = g ≫ sX) (Category.comp_id sX)) r hr hS1 c)
    {d : bivariantToBase C G sX (-(r : ℤ))}
    (hd : IsBivariantProperPushforward C G (g ≫ sX) sX (𝟙 C.S) g sX rfl (Category.comp_id sX) hpp
      (-(r : ℤ)) c d) :
    bivariantToBaseEval C G sX (-(r : ℤ)) d =
      properChowPushforward C (g ≫ sX) sX g rfl (-(-(r : ℤ))) (hpp _ _ g rfl _)
        (flatPullbackBaseClass C (g ≫ sX) r hr hS1) := by
  rw [bivariantToBaseEval_apply, hd (𝟙 C.S) 0 (baseFundamentalClass C),
    bivariantProperPushforwardCap_apply, hc]
  exact chowGroupBaseUnitCollapse_properChowPushforward C sX g hpp (-(r : ℤ)) _

/-- **Stacks 0FBW, surjectivity.** Over a Gysin system for which every flat scheme `W` over the
base carries a class characterized by the rule of Stacks 0B78 for its structure morphism (`hFP`),
the canonical map `A^p(X ⟶ Spec k) ⟶ CH_{-p}(X)` of Stacks 0FBW is surjective, given Stacks 0EPK
(`hEPK`) and the generation of Chow homology by proper pushforwards of flat pullbacks of the class
of the point (`hgen`).

The proof is that of `Stacks.Chow.bivariantToBaseEval_surjective`: each generator is hit by the
proper pushforward along `g` of the class of `hFP` for the scheme it comes from. -/
theorem bivariantToBaseEval_surjective_of_isBivariantFlatPullback (hS1 : FlatPullbackDescends C)
    (hpp : ProperPushforwardDescends C)
    (hFP : ∀ {W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW] [Flat sW] (r : ℕ)
      (hr : AlgebraicGeometry.RelativeDimension sW r),
      ∃ c : BivariantClass C G sW (𝟙 C.S) sW (Category.comp_id sW) (-(r : ℤ)),
        IsBivariantFlatPullback C G sW (𝟙 C.S) sW (Category.comp_id sW) r hr hS1 c)
    (hEPK : BivariantProperPushforwardExists C G)
    (hgen : ChowClassesGeneratedByBaseFlatPullbacks C hS1 hpp) :
    Function.Surjective (bivariantToBaseEval C G sX p) := by
  intro α
  have hle : AddSubgroup.closure
      {β : chowGroup C sX (-p) |
        ∃ (W : Scheme.{u}) (g : W ⟶ X) (hgp : IsProper g)
          (hgt : LocallyOfFiniteType (g ≫ sX)) (hgf : Flat (g ≫ sX)) (r : ℕ)
          (hr : AlgebraicGeometry.RelativeDimension (g ≫ sX) r), -(r : ℤ) = p ∧
          let := hgp
          let := hgt
          let := hgf
          β ≍ properChowPushforward C (g ≫ sX) sX g rfl (-(-(r : ℤ))) (hpp _ _ g rfl _)
            (flatPullbackBaseClass C (g ≫ sX) r hr hS1)} ≤
      (bivariantToBaseEval C G sX p).range := by
    rw [AddSubgroup.closure_le]
    rintro β ⟨W, g, hgp, hgt, hgf, r, hr, hrp, hβ⟩
    let _ := hgp
    let _ := hgt
    let _ := hgf
    subst hrp
    obtain ⟨c, hc⟩ := hFP (g ≫ sX) r hr
    obtain ⟨d, hd⟩ := hEPK (g ≫ sX) sX (𝟙 C.S) g sX rfl (Category.comp_id sX) hpp (-(r : ℤ)) c
    refine ⟨d, ?_⟩
    rw [bivariantToBaseEval_properPushforward_of_isBivariantFlatPullback C G sX hS1 hpp g r hr hc
      hd]
    exact (eq_of_heq hβ).symm
  exact hle (hgen sX p α)

/-- **Stacks 0FBW.** Over a Gysin system for which every flat scheme over the base carries a class
characterized by the rule of Stacks 0B78 for its structure morphism, the canonical map
`A^p(X ⟶ Spec k) ⟶ CH_{-p}(X)` of Stacks 0FBW is bijective. Injectivity is
`Stacks.Chow.bivariantToBaseEval_injective` and surjectivity is
`Stacks.Chow.bivariantToBaseEval_surjective_of_isBivariantFlatPullback`. -/
theorem bivariantToBaseEval_bijective_of_isBivariantFlatPullback
    [Subsingleton C.S] [IsIntegral C.S] (hS1 : FlatPullbackDescends C)
    (hfund : IntegralFundamentalClassIsFlatPullback C hS1) (hpp : ProperPushforwardDescends C)
    (hFP : ∀ {W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW] [Flat sW] (r : ℕ)
      (hr : AlgebraicGeometry.RelativeDimension sW r),
      ∃ c : BivariantClass C G sW (𝟙 C.S) sW (Category.comp_id sW) (-(r : ℤ)),
        IsBivariantFlatPullback C G sW (𝟙 C.S) sW (Category.comp_id sW) r hr hS1 c)
    (hEPK : BivariantProperPushforwardExists C G)
    (hgen : ChowClassesGeneratedByBaseFlatPullbacks C hS1 hpp) :
    Function.Bijective (bivariantToBaseEval C G sX p) :=
  ⟨bivariantToBaseEval_injective C G sX p hS1 hfund,
    bivariantToBaseEval_surjective_of_isBivariantFlatPullback C G sX p hS1 hpp hFP hEPK hgen⟩

/-- **Stacks 0FBW.** The identification `A^p(X ⟶ Spec k) = CH_{-p}(X)` as an isomorphism of
abelian groups, cap product with the fundamental class of the point, under the hypotheses of
`Stacks.Chow.bivariantToBaseEval_bijective_of_isBivariantFlatPullback`. -/
def bivariantToBaseEquivOfIsBivariantFlatPullback
    [Subsingleton C.S] [IsIntegral C.S] (hS1 : FlatPullbackDescends C)
    (hfund : IntegralFundamentalClassIsFlatPullback C hS1) (hpp : ProperPushforwardDescends C)
    (hFP : ∀ {W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW] [Flat sW] (r : ℕ)
      (hr : AlgebraicGeometry.RelativeDimension sW r),
      ∃ c : BivariantClass C G sW (𝟙 C.S) sW (Category.comp_id sW) (-(r : ℤ)),
        IsBivariantFlatPullback C G sW (𝟙 C.S) sW (Category.comp_id sW) r hr hS1 c)
    (hEPK : BivariantProperPushforwardExists C G)
    (hgen : ChowClassesGeneratedByBaseFlatPullbacks C hS1 hpp) :
    bivariantToBase C G sX p ≃+ chowGroup C sX (-p) :=
  AddEquiv.ofBijective (bivariantToBaseEval C G sX p)
    (bivariantToBaseEval_bijective_of_isBivariantFlatPullback C G sX p hS1 hfund hpp hFP hEPK
      hgen)

end Surjective

end Stacks.Chow

end
