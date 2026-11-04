module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPoint
public import StacksFrontier.AlgebraicGeometry.NagataExtensionClosed.Basic
public import StacksFrontier.AlgebraicGeometry.NagataValuativeCriterion.SeparatedAndProper

/-!
# Separatedness over a Nagata base, tested on punctured curves

Condition (2) of Stacks tag `0GWW`, stated with the canonical morphism
`Spec K ⟶ C \ {c}`, `K = Frac 𝒪_{C,c}`, built rather than quantified over.

## Main definitions

* `fractionRingToPuncture`: the canonical morphism
  `Spec (Frac 𝒪_{C,c}) ⟶ C \ {c}` for a closed point `c` of an integral scheme `C` whose
  local ring has dimension one.
* `HasAtMostOneLiftOverPuncturedCurves`: condition (2) of tag `0GWW`.

## Main results

* `isSeparated_iff_hasAtMostOneLiftOverPuncturedCurves`: tag `0GWW`.

## Implementation notes

`HasAtMostOneLiftOverPuncturedCurves hX hY f` follows the source clause by clause.  The data
are a commutative square of schemes over `S`, with `a : C \ {c} ⟶ X` along the top and
`q : C ⟶ Y` along the bottom.  The hypotheses are that `C` is a normal integral scheme of
finite type over `S` (`LocallyOfFiniteType p` together with `QuasiCompact p`), that `c` is a
closed point, and that `A = 𝒪_{C,c}` has dimension one.  The conclusion is that at most one
`l : Spec A ⟶ X` makes the second square commute, the one with `Spec K ⟶ C \ {c} ⟶ X` along
the top and `Spec A ⟶ C ⟶ Y` along the bottom.  Nothing else is quantified over: the domain
instance on `A` comes from `IsIntegral C`, and the generic morphism is `fractionRingToPuncture`.

The earlier statement `isSeparated_iff_hasEssentiallyFiniteTypeValuativeUniqueness`, whose
condition quantifies over the generic morphism and over a domain instance, is kept.  The theorem
here is proved from it.

## References

* [Stacks Project, Tag 0GWW](https://stacks.math.columbia.edu/tag/0GWW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.AlgebraicGeometry.NagataValuativeCriterion

/-! ### The generic morphism into the puncture -/

/-- On an integral scheme `C`, the morphism `Spec (Frac 𝒪_{C,c}) ⟶ Spec 𝒪_{C,c} ⟶ C` lands in
`C \ {c}` when `𝒪_{C,c}` has dimension one.  Its image is the generic point of `C`, whose local
ring has dimension zero, so it is not `c`. -/
theorem range_fractionRing_fromSpecStalk_subset_compl {C : Scheme.{u}} [IsIntegral C] {c : C}
    (hc : IsClosed ({c} : Set C)) (hdim : ringKrullDim (C.presheaf.stalk c) = 1) :
    Set.range (Spec.map (CommRingCat.ofHom
        (algebraMap (C.presheaf.stalk c) (FractionRing (C.presheaf.stalk c)))) ≫
          C.fromSpecStalk c) ⊆
      Set.range (Scheme.Opens.ι (X := C) ⟨({c} : Set C)ᶜ, hc.isOpen_compl⟩) := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨z, rfl⟩
  show _ ∉ ({c} : Set C)
  rw [NagataExtensionClosed.fractionRing_fromSpecStalk_apply c z, Set.mem_singleton_iff]
  intro h
  have h0 := ringKrullDim_stalk_genericPoint_eq_zero C
  rw [h, hdim] at h0
  exact one_ne_zero h0

/-- The canonical morphism `Spec K ⟶ C \ {c}`, `K = Frac 𝒪_{C,c}`, for a closed point `c` of an
integral scheme `C` with `dim 𝒪_{C,c} = 1`: the factorization of
`Spec K ⟶ Spec 𝒪_{C,c} ⟶ C` through the open immersion `C \ {c} ⟶ C`. -/
noncomputable def fractionRingToPuncture {C : Scheme.{u}} [IsIntegral C] {c : C}
    (hc : IsClosed ({c} : Set C)) (hdim : ringKrullDim (C.presheaf.stalk c) = 1) :
    Spec (.of (FractionRing (C.presheaf.stalk c))) ⟶
      Scheme.Opens.toScheme (X := C) ⟨({c} : Set C)ᶜ, hc.isOpen_compl⟩ :=
  IsOpenImmersion.lift _ _ (range_fractionRing_fromSpecStalk_subset_compl hc hdim)

/-- Composing `fractionRingToPuncture hc hdim` with the open immersion `C \ {c} ⟶ C` gives the
morphism `Spec (Frac 𝒪_{C,c}) ⟶ Spec 𝒪_{C,c} ⟶ C`. -/
@[reassoc (attr := simp)]
theorem fractionRingToPuncture_ι {C : Scheme.{u}} [IsIntegral C] {c : C}
    (hc : IsClosed ({c} : Set C)) (hdim : ringKrullDim (C.presheaf.stalk c) = 1) :
    fractionRingToPuncture hc hdim ≫ Scheme.Opens.ι (X := C) ⟨({c} : Set C)ᶜ, hc.isOpen_compl⟩ =
      Spec.map (CommRingCat.ofHom
        (algebraMap (C.presheaf.stalk c) (FractionRing (C.presheaf.stalk c)))) ≫
          C.fromSpecStalk c :=
  IsOpenImmersion.lift_fac _ _ _

/-! ### Condition (2) of tag `0GWW` -/

/-- **Condition (2) of tag `0GWW`.**  Consider a commutative square of schemes over `S`, with
`a : U ⟶ X` along the top, `q : C ⟶ Y` along the bottom and `f` on the right.  Suppose `C` is a
normal integral scheme of finite type over `S`, that `U = C \ {c}` for a closed point `c ∈ C`, and
that `A = 𝒪_{C,c}` has dimension `1`.  Then the square with `Spec K ⟶ U ⟶ X` along the top and
`Spec A ⟶ C ⟶ Y` along the bottom, where `K = Frac A`, has at most one dotted arrow
`Spec A ⟶ X` making it commute. -/
def HasAtMostOneLiftOverPuncturedCurves {S X Y : Scheme.{u}} (hX : X ⟶ S) (hY : Y ⟶ S)
    (f : X ⟶ Y) : Prop :=
  ∀ (C : Scheme.{u}) (p : C ⟶ S) [IsNormal C] [IsIntegral C]
    [LocallyOfFiniteType p] [QuasiCompact p]
    (c : C) (hc : IsClosed ({c} : Set C)) (hdim : ringKrullDim (C.presheaf.stalk c) = 1)
    (a : Scheme.Opens.toScheme (X := C) ⟨({c} : Set C)ᶜ, hc.isOpen_compl⟩ ⟶ X) (q : C ⟶ Y),
    a ≫ f = Scheme.Opens.ι _ ≫ q → a ≫ hX = Scheme.Opens.ι _ ≫ p → q ≫ hY = p →
    ∀ l₁ l₂ : Spec (.of (C.presheaf.stalk c)) ⟶ X,
      Spec.map (CommRingCat.ofHom
          (algebraMap (C.presheaf.stalk c) (FractionRing (C.presheaf.stalk c)))) ≫ l₁ =
        fractionRingToPuncture hc hdim ≫ a →
      l₁ ≫ f = C.fromSpecStalk c ≫ q →
      Spec.map (CommRingCat.ofHom
          (algebraMap (C.presheaf.stalk c) (FractionRing (C.presheaf.stalk c)))) ≫ l₂ =
        fractionRingToPuncture hc hdim ≫ a →
      l₂ ≫ f = C.fromSpecStalk c ≫ q →
      l₁ = l₂

/-- Over `S`, with `f` a morphism over `S`, condition (2) of tag `0GWW` is equivalent to the
earlier formulation `HasEssentiallyFiniteTypeValuativeUniqueness`.  That formulation quantifies
over the generic morphism `g`, and the only such `g` is `fractionRingToPuncture`. -/
theorem hasAtMostOneLiftOverPuncturedCurves_iff {S X Y : Scheme.{u}} (hX : X ⟶ S) (hY : Y ⟶ S)
    (f : X ⟶ Y) (hf : f ≫ hY = hX) :
    HasAtMostOneLiftOverPuncturedCurves hX hY f ↔
      HasEssentiallyFiniteTypeValuativeUniqueness f hY := by
  constructor
  · refine fun h C p hp hqc hn hint c hc hdim q a hq ha hdom g hg l₁ l₂ hl₁ hg₁ hl₂ hg₂ => ?_
    obtain rfl : g = fractionRingToPuncture hc hdim :=
      (cancel_mono (Scheme.Opens.ι _)).mp (hg.trans (fractionRingToPuncture_ι hc hdim).symm)
    exact h C p c hc hdim a q ha
      (by rw [← hf, ← Category.assoc, ha, Category.assoc, hq]) hq l₁ l₂ hg₁ hl₁ hg₂ hl₂
  · exact fun h C p _ _ _ _ c hc hdim a q ha _ hq l₁ l₂ hg₁ hl₁ hg₂ hl₂ =>
      h C p inferInstance inferInstance inferInstance inferInstance c hc hdim q a hq ha
        inferInstance (fractionRingToPuncture hc hdim) (fractionRingToPuncture_ι hc hdim)
        l₁ l₂ hl₁ hg₁ hl₂ hg₂

/-! ### Tag `0GWW` -/

/-- **Stacks Project, Tag 0GWW.**  Let `S` be a Nagata scheme and let `f : X ⟶ Y` be a morphism
of schemes locally of finite type over `S`.  Then `f` is separated if and only if, for every
normal integral scheme `C` of finite type over `S`, every closed point `c ∈ C` with
`dim 𝒪_{C,c} = 1`, and every commutative square over `S` with `C \ {c} ⟶ X` along the top and
`C ⟶ Y` along the bottom, at most one `Spec 𝒪_{C,c} ⟶ X` makes the induced square from
`Spec (Frac 𝒪_{C,c}) ⟶ Spec 𝒪_{C,c}` to `f` commute.

This is `isSeparated_iff_hasEssentiallyFiniteTypeValuativeUniqueness`, whose condition is
equivalent to this one by `hasAtMostOneLiftOverPuncturedCurves_iff`. -/
@[stacks 0GWW]
theorem isSeparated_iff_hasAtMostOneLiftOverPuncturedCurves
    {S X Y : Scheme.{u}} (hX : X ⟶ S) (hY : Y ⟶ S) (f : X ⟶ Y)
    (hf : f ≫ hY = hX) (hS : IsNagataScheme S)
    [LocallyOfFiniteType hX] [LocallyOfFiniteType hY] :
    IsSeparated f ↔ HasAtMostOneLiftOverPuncturedCurves hX hY f :=
  (isSeparated_iff_hasEssentiallyFiniteTypeValuativeUniqueness hX hY f hf hS).trans
    (hasAtMostOneLiftOverPuncturedCurves_iff hX hY f hf).symm

end Stacks.AlgebraicGeometry.NagataValuativeCriterion
