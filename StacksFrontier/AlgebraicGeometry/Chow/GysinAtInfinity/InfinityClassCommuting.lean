module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Commuting

/-!
# The class of a divisor with flat complement commutes with every bivariant class

Let `(S, δ)` be as in Situation 02QL, let `π : W ⟶ X` be locally of finite type over `S`, let
`j : U ⟶ W` be an open immersion with `U ⟶ X` flat of relative dimension one, and let
`i : Z(s) ⟶ W` be the zero scheme of a section `s` of an invertible module, with trivial normal
bundle and complement `U`. The construction of Stacks 0F9J, carried out for this divisor, gives the
class `C ∈ A⁰(Z(s) ⟶ X)` of `Stacks.Chow.GysinAtInfinity.infinityClass`: `C ∩ α = i^* β` for any
`β` on `W ×_X T` restricting over `U ×_X T` to the flat pullback of `α ∈ CH_k(T)`.

This file proves the argument of Stacks 0FAS for this class: `C` commutes, in the sense of
Remark 0FA2, with every bivariant class `c ∈ A^p(Y ⟶ X)`. Choose a lift `β` of `α`. Then `c ∩ β`
is a lift of `c ∩ α` (`Stacks.Chow.GysinAtInfinity.isLift_capLift`), so
`C ∩ (c ∩ α) = i^*(c ∩ β)`, while `c ∩ (C ∩ α) = c ∩ i^* β = i^*(c ∩ β)` by condition (3) of
Stacks 0B76 for `c`; the two Gysin maps, on `W ×_X (Y ×_X T)` and on `Y ×_X (W ×_X T)`, are
compared by Stacks 02TA along the canonical isomorphism.

The modification `b : W ⟶ 𝐏¹_X` of Stacks 0F9J itself is the case treated in
`Stacks.Chow.GysinAtInfinity.gysinAtInfinityClass_bivariantCommute`. The deformation space of a
closed immersion, on which the class `j^* ∘ C` of the construction preceding Stacks 0FBK is
computed (`Stacks.Deformation.normalConeClass`), is another instance.

## Main definitions

* `Stacks.Chow.GysinAtInfinity.DivisorCommuting.divisorIso` — the identification of the zero
  scheme of the pulled-back section on `W ×_X T` with `Z(s) ×_X T`.

## Main results

* `Stacks.Chow.GysinAtInfinity.DivisorCommuting.infinityCap_eq_of_isLift'` — `C ∩ α = i^* β`,
  read on `Z(s) ×_X T` through `divisorIso`.
* `Stacks.Chow.GysinAtInfinity.DivisorCommuting.cap_divisorGysin` — `c ∩ i^* β` is the Gysin map
  of the pulled-back divisor applied to `c ∩ β`.
* `Stacks.Chow.GysinAtInfinity.DivisorCommuting.gysin_comparison` — the comparison of the two
  Gysin maps.
* `Stacks.Chow.GysinAtInfinity.infinityClass_bivariantCommute` — `C` and `c` commute.

## References

* [Stacks Project, Tag 0FAS](https://stacks.math.columbia.edu/tag/0FAS)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

namespace GysinAtInfinity

namespace DivisorCommuting

/-! ### The zero scheme of the pulled-back section, read on `Z(s) ×_X T` -/

section Iso

variable {X W : Scheme.{u}} (π : W ⟶ X) (L : W.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) {T : Scheme.{u}} (t : T ⟶ X)

/-- The divisor `Z(s)` pulled back to `W ×_X T`: the zero scheme of the pulled-back section. -/
abbrev testDivisor : (pullback π t).IdealSheafData :=
  gysinTripleDivisor L s (pullback.fst π t)

/-- The identification of the zero scheme of the section pulled back to `W ×_X T` with
`Z(s) ×_X T` (Stacks 0B6Y followed by the associativity of fibre products). -/
def divisorIso : (testDivisor π L s t).subscheme ⟶ pullback (gysinTripleInclusion L s ≫ π) t :=
  (gysinDivisorBaseChangeIso L s (pullback.fst π t)).hom ≫
    (pullbackRightPullbackFstIso π t (gysinTripleInclusion L s)).hom

/-- `divisorIso` is an isomorphism. -/
instance isIso_divisorIso : IsIso (divisorIso π L s t) := by
  unfold divisorIso
  infer_instance

/-- Read in `W`, the identification is the inclusion of the zero scheme. -/
@[reassoc]
theorem divisorIso_fst_incl :
    divisorIso π L s t ≫ pullback.fst (gysinTripleInclusion L s ≫ π) t ≫
        gysinTripleInclusion L s =
      (testDivisor π L s t).subschemeι ≫ pullback.fst π t := by
  rw [divisorIso, Category.assoc, pullbackRightPullbackFstIso_hom_fst_assoc]
  exact gysinDivisorBaseChangeIso_hom_comp_test L s (pullback.fst π t)

/-- The identification lies over `T`. -/
@[reassoc]
theorem divisorIso_snd :
    divisorIso π L s t ≫ pullback.snd (gysinTripleInclusion L s ≫ π) t =
      (testDivisor π L s t).subschemeι ≫ pullback.snd π t := by
  rw [divisorIso, Category.assoc, pullbackRightPullbackFstIso_hom_snd,
    gysinDivisorBaseChangeIso_hom_snd_assoc]

/-- The identification lies over `X`. -/
theorem divisorIso_comp_test :
    divisorIso π L s t ≫ (pullback.fst (gysinTripleInclusion L s ≫ π) t ≫
        (gysinTripleInclusion L s ≫ π)) =
      (testDivisor π L s t).subschemeι ≫ (pullback.fst π t ≫ π) :=
  divisorIso_fst_incl_assoc π L s t π

variable (C : ChowSituation.{u}) (f : X ⟶ C.S)

/-- The identification lies over the base. -/
theorem divisorIso_comp_structure :
    divisorIso π L s t ≫ (pullback.fst (gysinTripleInclusion L s ≫ π) t ≫
        (gysinTripleInclusion L s ≫ (π ≫ f))) =
      (testDivisor π L s t).subschemeι ≫ testStr C f π t := by
  have h := congrArg (· ≫ f) (divisorIso_comp_test π L s t)
  simpa only [testStr, Category.assoc] using h

end Iso

/-! ### The cap operation of the class, computed by a lift -/

section Formula

variable (C : ChowSituation.{u}) {X W U : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (π : W ⟶ X) [LocallyOfFiniteType π] (j : U ⟶ W) [IsOpenImmersion j] [Flat (j ≫ π)]
  (hU : AlgebraicGeometry.RelativeDimension (j ≫ π) 1) (L : W.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property L]
  (s : Γ(L, ⊤))
  (hcompl : Set.range (Stacks.Divisors.zeroScheme W L s).subschemeι.base = (Set.range j.base)ᶜ)
  (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
    (Stacks.Divisors.zeroScheme W L s).subscheme.sheaf.obj
    (Stacks.Divisors.zeroScheme W L s).subscheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme W L s).subschemeι).obj L))
  {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t]

include hcompl htriv in
/-- **The construction of Stacks 0F9J, read on `Z(s) ×_X T`.** For every lift
`β ∈ A_{k+1}(W ×_X T)` of `α ∈ A_k(T)` the class caps `α` to the Gysin image `i^* β` of `β`,
the Gysin map of the section pulled back to `W ×_X T`, read on `Z(s) ×_X T` through
`Stacks.Chow.GysinAtInfinity.DivisorCommuting.divisorIso`. -/
theorem infinityCap_eq_of_isLift' {k : ℤ} {α : chowGroup C (t ≫ f) k}
    {β : chowGroup C (testStr C f π t) (k + 1)} (hβ : IsLift C f π j hU t k α β) :
    infinityCap C f π j hU L s hcompl htriv t k α =
      chowGroupDegreeEquiv C _ (sub_zero k).symm
        (chowPushforwardOfIso C ((testDivisor π L s t).subschemeι ≫ testStr C f π t)
          (pullback.fst (gysinTripleInclusion L s ≫ π) t ≫ (gysinTripleInclusion L s ≫ (π ≫ f)))
          (divisorIso π L s t) (divisorIso_comp_structure π L s t C f) k
          ((gysinSystemOfInvertible C).onChow (testStr C f π t)
            (gysinTripleModule L (pullback.fst π t))
            (gysinTripleSection L s (pullback.fst π t)) k β)) := by
  rw [infinityCap_eq_of_isLift C f π j hU L s hcompl htriv hβ, divisorMiddleCap, middleCap_apply,
    (gysinBivariantClass C (π ≫ f) L s).2, gysinBivariantCap_apply]
  apply eq_of_heq
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
  refine HEq.trans ?_ (chowGroupDegreeEquiv_heq C _ _ _).symm
  refine HEq.trans (heq_of_eq (properChowPushforward_comp_apply C _ _ _
    (gysinDivisorBaseChangeIso L s (pullback.fst π t)).hom _ (divisorIso π L s t) rfl _ _
    (divisorIso_comp_structure π L s t C f) (k + 1 - 1)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) _).symm) ?_
  exact heq_map_index (α := fun n ↦ chowGroup C (testStr C f π t) (n + 1))
    (β := fun n ↦ chowGroup C (pullback.fst (gysinTripleInclusion L s ≫ π) t ≫
      (gysinTripleInclusion L s ≫ (π ≫ f))) n) (by ring : k + 1 - 1 = k)
    (chowGroupDegreeEquiv_heq C _ _ _)
    (fun n x ↦ properChowPushforward C _ _ (divisorIso π L s t)
      (divisorIso_comp_structure π L s t C f) n (properPushforwardDescends C _ _ _ _ _)
      ((gysinSystemOfInvertible C).onChow (testStr C f π t)
        (gysinTripleModule L (pullback.fst π t))
        (gysinTripleSection L s (pullback.fst π t)) n x))

end Formula

/-! ### The cap of `c` on the Gysin image of a lift -/

section Commuting

variable (C : ChowSituation.{u}) {X W Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (π : W ⟶ X) [LocallyOfFiniteType π] (L : W.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (fY : Y ⟶ X) [LocallyOfFiniteType fY] {p : ℤ}
  (c : BivariantClass C (gysinSystemOfInvertible C) (fY ≫ f) f fY rfl p)
  {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t]

/-- The test morphism `W ×_X T ⟶ X`. -/
abbrev wTest : pullback π t ⟶ X :=
  pullback.fst π t ≫ π

/-- The test morphism `Z(s) ×_X T ⟶ X`. -/
abbrev zTest : pullback (gysinTripleInclusion L s ≫ π) t ⟶ X :=
  pullback.fst (gysinTripleInclusion L s ≫ π) t ≫ (gysinTripleInclusion L s ≫ π)

/-- The invertible module of the divisor, pulled back to `Y ×_X (W ×_X T)`. -/
abbrev capModule : (pullback fY (wTest π t)).Modules :=
  (Scheme.Modules.pullback (pullback.snd fY (wTest π t))).obj
    (gysinTripleModule L (pullback.fst π t))

/-- The section of the divisor, pulled back to `Y ×_X (W ×_X T)`. -/
abbrev capSection : Γ(capModule π L fY t, ⊤) :=
  AlgebraicGeometry.pullbackGlobalSections (pullback.snd fY (wTest π t))
    (gysinTripleModule L (pullback.fst π t)) (gysinTripleSection L s (pullback.fst π t))

/-- The divisor `Z(s)` pulled back to `Y ×_X (W ×_X T)`. -/
abbrev capDivisor : (pullback fY (wTest π t)).IdealSheafData :=
  Stacks.Divisors.zeroScheme (pullback fY (wTest π t)) (capModule π L fY t)
    (capSection π L s fY t)

/-- The identification of the divisor of `Y ×_X (W ×_X T)` with `Y ×_X (Z(s) ×_X T)`. -/
def capIso : (capDivisor π L s fY t).subscheme ⟶ pullback fY (zTest π L s t) :=
  (bivariantDivisorBaseChangeIso fY (wTest π t) (gysinTripleModule L (pullback.fst π t))
      (gysinTripleSection L s (pullback.fst π t))).inv ≫
    (testBaseChangeIso fY (zTest π L s t) (divisorIso π L s t)
      ((testDivisor π L s t).subschemeι ≫ wTest π t) (divisorIso_comp_test π L s t)).hom

/-- `capIso` is an isomorphism. -/
instance : IsIso (capIso π L s fY t) := by
  unfold capIso
  infer_instance

omit [LocallyOfFiniteType f] [LocallyOfFiniteType π] [LocallyOfFiniteType fY]
  [LocallyOfFiniteType t] in
/-- `capIso` is a morphism over the base. -/
theorem capIso_comp_structure :
    capIso π L s fY t ≫ (pullback.fst fY (zTest π L s t) ≫ (fY ≫ f)) =
      (capDivisor π L s fY t).subschemeι ≫ pullback.fst fY (wTest π t) ≫ (fY ≫ f) := by
  rw [capIso, Category.assoc, ← Category.assoc (testBaseChangeIso _ _ _ _ _).hom,
    testBaseChangeIso_hom_fst, Iso.inv_comp_eq]
  exact (bivariantDivisorBaseChangeIso_hom_comp_structureMorphism (fY ≫ f) fY _ _ _).symm

/-- **The cap of `c` on `i^* β`.** For `β ∈ A_{k+1}(W ×_X T)`, capping the Gysin image
`i^* β ∈ A_k(Z(s) ×_X T)` with `c` is the Gysin map of the divisor of `Y ×_X (W ×_X T)` applied
to `c ∩ β`: condition (3) of Stacks 0B76 for `c`. -/
theorem cap_divisorGysin (k : ℤ) (β : chowGroup C (testStr C f π t) (k + 1)) :
    c.cap (zTest π L s t) k
      (chowGroupCongr C (by simp only [Category.assoc]) k
        (chowPushforwardOfIso C ((testDivisor π L s t).subschemeι ≫ testStr C f π t)
          (pullback.fst (gysinTripleInclusion L s ≫ π) t ≫
            (gysinTripleInclusion L s ≫ (π ≫ f))) (divisorIso π L s t)
          (divisorIso_comp_structure π L s t C f) k
          ((gysinSystemOfInvertible C).onChow (testStr C f π t)
            (gysinTripleModule L (pullback.fst π t))
            (gysinTripleSection L s (pullback.fst π t)) k β))) =
      chowPushforwardOfIso C ((capDivisor π L s fY t).subschemeι ≫
          pullback.fst fY (wTest π t) ≫ (fY ≫ f))
        (pullback.fst fY (zTest π L s t) ≫ (fY ≫ f))
        (capIso π L s fY t) (capIso_comp_structure C f π L s fY t) (k - p)
        ((gysinSystemOfInvertible C).onChow (pullback.fst fY (wTest π t) ≫ (fY ≫ f))
          (capModule π L fY t) (capSection π L s fY t) (k - p)
          (Eq.mp (congrArg (chowGroup C (pullback.fst fY (wTest π t) ≫ (fY ≫ f))) (by omega :
              (k + 1) - p = (k - p) + 1))
            (c.cap (wTest π t) (k + 1)
              (chowGroupCongr C (Category.assoc _ _ _).symm (k + 1) β)))) := by
  have hmb : divisorIso π L s t ≫ (zTest π L s t ≫ f) =
      (testDivisor π L s t).subschemeι ≫ testStr C f π t := by
    rw [← divisorIso_comp_structure π L s t C f]
    simp only [Category.assoc]
  have hqm : (testDivisor π L s t).subschemeι ≫ testStr C f π t
      = ((testDivisor π L s t).subschemeι ≫ wTest π t) ≫ f := by
    simp only [testStr, Category.assoc]
  set y := (gysinSystemOfInvertible C).onChow (testStr C f π t)
    (gysinTripleModule L (pullback.fst π t)) (gysinTripleSection L s (pullback.fst π t)) k β
  have hcap := BivariantClass.cap_chowPushforwardOfIso c (zTest π L s t)
    (divisorIso π L s t) ((testDivisor π L s t).subschemeι ≫ wTest π t)
    (divisorIso_comp_test π L s t) _ hqm k hmb y (chowGroupCongr C hqm k y) rfl
  rw [chowGroupCongr_chowPushforwardOfIso_target C _ (by simp only [Category.assoc]) _ _ hmb k,
    hcap]
  have hz : chowGroupCongr C hqm k y = (gysinSystemOfInvertible C).onChow (wTest π t ≫ f)
      (gysinTripleModule L (pullback.fst π t)) (gysinTripleSection L s (pullback.fst π t)) k
      (chowGroupCongr C (Category.assoc _ _ _).symm (k + 1) β) :=
    eq_of_heq ((chowGroupCongr_heq C hqm k y).trans
      (onChow_heq_congr C _ (Category.assoc _ _ _).symm
      _ _ k (chowGroupCongr_heq C _ _ β).symm))
  have hgn := c.gysin_naturality (wTest π t)
    (gysinTripleModule L (pullback.fst π t)) (gysinTripleSection L s (pullback.fst π t)) k
    (bivariantDivisorBaseChangeIso fY _ _ _) (bivariantDivisorBaseChangeIso_hom_subschemeι fY _ _ _)
    (bivariantDivisorBaseChangeIso_hom_comp_structureMorphism (fY ≫ f) fY _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (chowGroupCongr C (Category.assoc _ _ _).symm (k + 1) β)
  rw [properChowPushforward_eq_chowPushforwardOfIso] at hgn
  rw [hz]
  refine Eq.trans ?_ (congrArg (chowPushforwardOfIso C _ _ (capIso π L s fY t)
    (capIso_comp_structure C f π L s fY t) (k - p)) hgn)
  rw [chowPushforwardOfIso_comp_apply]
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _
  rw [capIso, Iso.hom_inv_id_assoc]

/-! ### The comparison of the two divisors -/

omit [LocallyOfFiniteType f] [LocallyOfFiniteType π] [LocallyOfFiniteType fY]
  [LocallyOfFiniteType t] in
/-- Two morphisms into `Y ×_X (Z(s) ×_X T)` agree when their points of `Y`, `W` and `T` do. -/
theorem capTarget_hom_ext {V : Scheme.{u}} {a a' : V ⟶ pullback fY (zTest π L s t)}
    (hY : a ≫ pullback.fst fY (zTest π L s t) = a' ≫ pullback.fst fY (zTest π L s t))
    (hW : a ≫ pullback.snd fY (zTest π L s t) ≫
        pullback.fst (gysinTripleInclusion L s ≫ π) t ≫ gysinTripleInclusion L s =
      a' ≫ pullback.snd fY (zTest π L s t) ≫
        pullback.fst (gysinTripleInclusion L s ≫ π) t ≫ gysinTripleInclusion L s)
    (hT : a ≫ pullback.snd fY (zTest π L s t) ≫ pullback.snd (gysinTripleInclusion L s ≫ π) t =
      a' ≫ pullback.snd fY (zTest π L s t) ≫ pullback.snd (gysinTripleInclusion L s ≫ π) t) :
    a = a' := by
  refine pullback.hom_ext hY (pullback.hom_ext ?_ ?_)
  · rw [← cancel_mono (gysinTripleInclusion L s)]
    simpa only [Category.assoc] using hW
  · simpa only [Category.assoc] using hT

omit [LocallyOfFiniteType f] [LocallyOfFiniteType π] [LocallyOfFiniteType fY]
  [LocallyOfFiniteType t] in
/-- The point of `Y` of the identification `capIso`. -/
theorem capIso_fst :
    capIso π L s fY t ≫ pullback.fst fY (zTest π L s t) =
      (capDivisor π L s fY t).subschemeι ≫ pullback.fst fY (wTest π t) := by
  rw [capIso, Category.assoc, testBaseChangeIso_hom_fst,
    ← bivariantDivisorBaseChangeIso_inv_comp (wTest π t) _ _ fY, Category.assoc]
  simp [bivariantBaseChangeMap]

omit [LocallyOfFiniteType f] [LocallyOfFiniteType π] [LocallyOfFiniteType fY]
  [LocallyOfFiniteType t] in
/-- The point of `W` of the identification `capIso`. -/
theorem capIso_snd_fst :
    capIso π L s fY t ≫ pullback.snd fY (zTest π L s t) ≫
        pullback.fst (gysinTripleInclusion L s ≫ π) t ≫ gysinTripleInclusion L s =
      (capDivisor π L s fY t).subschemeι ≫ pullback.snd fY (wTest π t) ≫ pullback.fst π t := by
  rw [capIso, Category.assoc, testBaseChangeIso_hom_snd_assoc, divisorIso_fst_incl,
    ← bivariantDivisorBaseChangeIso_inv_comp (wTest π t) _ _ fY, Category.assoc]
  simp [bivariantBaseChangeMap]

omit [LocallyOfFiniteType f] [LocallyOfFiniteType π] [LocallyOfFiniteType fY]
  [LocallyOfFiniteType t] in
/-- The point of `T` of the identification `capIso`. -/
theorem capIso_snd_snd :
    capIso π L s fY t ≫ pullback.snd fY (zTest π L s t) ≫
        pullback.snd (gysinTripleInclusion L s ≫ π) t =
      (capDivisor π L s fY t).subschemeι ≫ pullback.snd fY (wTest π t) ≫ pullback.snd π t := by
  rw [capIso, Category.assoc, testBaseChangeIso_hom_snd_assoc, divisorIso_snd,
    ← bivariantDivisorBaseChangeIso_inv_comp (wTest π t) _ _ fY, Category.assoc]
  simp [bivariantBaseChangeMap]

omit [LocallyOfFiniteType f] [LocallyOfFiniteType π] [LocallyOfFiniteType fY]
  [LocallyOfFiniteType t] in
/-- The divisor of `Y ×_X (W ×_X T)` is the pullback of the divisor of `W ×_X (Y ×_X T)` along
the comparison isomorphism. -/
theorem capDivisor_eq :
    capDivisor π L s fY t =
      pullbackZeroScheme (commuteComparisonHom fY π t)
        (gysinTripleModule L (pullback.fst π (yTest fY t)))
        (gysinTripleSection L s (pullback.fst π (yTest fY t))) := by
  rw [capDivisor, Stacks.Divisors.zeroScheme_pullback_comp
      (pullback.snd fY (wTest π t)) (pullback.fst π t) L s, pullbackZeroScheme,
    Stacks.Divisors.zeroScheme_pullback_comp
      (commuteComparisonHom fY π t) (pullback.fst π (yTest fY t)) L s, commuteComparisonHom_fst]

/-- The morphism from the divisor of `Y ×_X (W ×_X T)` to that of `W ×_X (Y ×_X T)` over the
comparison isomorphism. -/
def capDivisorHom : (capDivisor π L s fY t).subscheme ⟶
    (testDivisor π L s (yTest fY t)).subscheme :=
  eqToHom (congrArg Scheme.IdealSheafData.subscheme (capDivisor_eq π L s fY t)) ≫
    zeroSchemePullbackHom (commuteComparisonHom fY π t) _ _

/-- `capDivisorHom` is proper. -/
instance : IsProper (capDivisorHom π L s fY t) := by
  unfold capDivisorHom
  infer_instance

omit [LocallyOfFiniteType f] [LocallyOfFiniteType π] [LocallyOfFiniteType fY]
  [LocallyOfFiniteType t] in
/-- `capDivisorHom` lies over the comparison isomorphism. -/
@[reassoc]
theorem capDivisorHom_subschemeι :
    capDivisorHom π L s fY t ≫ (testDivisor π L s (yTest fY t)).subschemeι =
      (capDivisor π L s fY t).subschemeι ≫ commuteComparisonHom fY π t := by
  rw [capDivisorHom, Category.assoc, zeroSchemePullbackHom_subschemeι, ← Category.assoc,
    subschemeι_eqToHom (capDivisor_eq π L s fY t)]

omit [LocallyOfFiniteType f] [LocallyOfFiniteType π] [LocallyOfFiniteType fY]
  [LocallyOfFiniteType t] in
/-- `capDivisorHom` lies over the base. -/
private theorem capDivisorHom_comp_structure :
    capDivisorHom π L s fY t ≫ ((testDivisor π L s (yTest fY t)).subschemeι ≫
        testStr C f π (yTest fY t)) =
      (capDivisor π L s fY t).subschemeι ≫ pullback.fst fY (wTest π t) ≫ (fY ≫ f) := by
  rw [← Category.assoc, capDivisorHom_subschemeι, Category.assoc,
    commuteComparisonHom_comp_structureMorphism]

omit [LocallyOfFiniteType f] [LocallyOfFiniteType π] [LocallyOfFiniteType fY]
  [LocallyOfFiniteType t] in
/-- The two identifications of the divisor of `Y ×_X (W ×_X T)` with `Y ×_X (Z(s) ×_X T)`
agree. -/
theorem capDivisorHom_comp_eq :
    capDivisorHom π L s fY t ≫ divisorIso π L s (yTest fY t) ≫
        commuteComparisonHom (gysinTripleInclusion L s ≫ π) fY t =
      capIso π L s fY t := by
  refine capTarget_hom_ext π L s fY t ?_ ?_ ?_
  · rw [capIso_fst]
    simp only [Category.assoc, commuteComparisonHom_fst, divisorIso_snd_assoc,
      capDivisorHom_subschemeι_assoc, commuteComparisonHom_snd_fst]
  · rw [capIso_snd_fst]
    simp only [Category.assoc, commuteComparisonHom_snd_fst_assoc, divisorIso_fst_incl,
      capDivisorHom_subschemeι_assoc, commuteComparisonHom_fst]
  · rw [capIso_snd_snd]
    simp only [Category.assoc, divisorIso_snd_assoc, capDivisorHom_subschemeι_assoc,
      commuteComparisonHom_snd_snd]

/-- **The Gysin map on `W ×_X (Y ×_X T)`, read on `Y ×_X (W ×_X T)`.** The Gysin map of the
divisor commutes with pushforward along the comparison isomorphism
`Y ×_X (W ×_X T) ≅ W ×_X (Y ×_X T)` (Stacks 02TA), the divisor pulling back to the divisor. -/
theorem gysin_comparison (k : ℤ)
    (z : chowGroup C (pullback.fst fY (wTest π t) ≫ (fY ≫ f)) (k - p + 1)) :
    chowPushforwardOfIso C (pullback.fst (gysinTripleInclusion L s ≫ π) (yTest fY t) ≫
          (gysinTripleInclusion L s ≫ (π ≫ f)))
        (pullback.fst fY (zTest π L s t) ≫ (fY ≫ f))
        (commuteComparisonHom (gysinTripleInclusion L s ≫ π) fY t)
        (by rw [commuteComparisonHom_comp_structureMorphism C f _ fY t]; simp only [Category.assoc])
        (k - p)
      (chowPushforwardOfIso C ((testDivisor π L s (yTest fY t)).subschemeι ≫
          testStr C f π (yTest fY t))
        (pullback.fst (gysinTripleInclusion L s ≫ π) (yTest fY t) ≫
          (gysinTripleInclusion L s ≫ (π ≫ f)))
        (divisorIso π L s (yTest fY t)) (divisorIso_comp_structure π L s _ C f) (k - p)
        ((gysinSystemOfInvertible C).onChow (testStr C f π (yTest fY t))
          (gysinTripleModule L (pullback.fst π (yTest fY t)))
          (gysinTripleSection L s (pullback.fst π (yTest fY t))) (k - p)
          (chowPushforwardOfIso C (pullback.fst fY (wTest π t) ≫ (fY ≫ f))
            (testStr C f π (yTest fY t))
            (commuteComparisonHom fY π t)
            (commuteComparisonHom_comp_structureMorphism C f fY _ t) (k - p + 1) z))) =
      chowPushforwardOfIso C ((capDivisor π L s fY t).subschemeι ≫
          pullback.fst fY (wTest π t) ≫ (fY ≫ f))
        (pullback.fst fY (zTest π L s t) ≫ (fY ≫ f)) (capIso π L s fY t)
        (capIso_comp_structure C f π L s fY t) (k - p)
        ((gysinSystemOfInvertible C).onChow (pullback.fst fY (wTest π t) ≫ (fY ≫ f))
          (capModule π L fY t) (capSection π L s fY t) (k - p) z) := by
  set y := (gysinSystemOfInvertible C).onChow (pullback.fst fY (wTest π t) ≫ (fY ≫ f))
    (capModule π L fY t) (capSection π L s fY t) (k - p) z
  have hnat := gysinSystemOfInvertible_isNaturalUnderProperPushforward C
    (pullback.fst fY (wTest π t) ≫ (fY ≫ f))
    (testStr C f π (yTest fY t))
    (commuteComparisonHom fY π t)
    (commuteComparisonHom_comp_structureMorphism C f fY _ t)
    (gysinTripleModule L (pullback.fst π (yTest fY t)))
    (gysinTripleSection L s (pullback.fst π (yTest fY t))) (k - p) _
    (zeroSchemePullbackHom_subschemeι _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) z
  have hx := (onChow_pullbackComp_heq C (pullback.fst fY (wTest π t) ≫ (fY ≫ f))
      L s (k - p) z (pullback.snd fY (wTest π t)) (pullback.fst π t)).trans
    ((onChow_pullback_heq C (pullback.fst fY (wTest π t) ≫ (fY ≫ f))
      L s (k - p) z (commuteComparisonHom_fst fY π t).symm).trans
    (onChow_pullbackComp_heq C (pullback.fst fY (wTest π t) ≫ (fY ≫ f))
      L s (k - p) z (commuteComparisonHom fY π t) (pullback.fst π (yTest fY t))).symm)
  have h2 := properChowPushforward_comp_apply C _ _ _
    (eqToHom (congrArg Scheme.IdealSheafData.subscheme (capDivisor_eq π L s fY t)))
    (zeroSchemePullbackHom (commuteComparisonHom fY π t) _ _)
    (capDivisorHom π L s fY t) rfl
    (by rw [← Category.assoc, subschemeι_eqToHom (capDivisor_eq π L s fY t)])
    (zeroSchemeSquare_comp_structureMorphism C _ _ _
      (commuteComparisonHom_comp_structureMorphism C f fY _ t) _ _ _
      (zeroSchemePullbackHom_subschemeι _ _ _))
    (capDivisorHom_comp_structure C f π L s fY t) (k - p)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _)
    y
  have h3 := properChowPushforward_comp₃_eq C (capDivisorHom π L s fY t)
    (divisorIso π L s (yTest fY t))
    (commuteComparisonHom (gysinTripleInclusion L s ≫ π) fY t)
    (capIso π L s fY t) (capDivisorHom_comp_eq π L s fY t)
    (capDivisorHom_comp_structure C f π L s fY t)
    (divisorIso_comp_structure π L s _ C f)
    (by rw [commuteComparisonHom_comp_structureMorphism C f _ fY t]; simp only [Category.assoc])
    (capIso_comp_structure C f π L s fY t) (k - p)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    y
  have hconv' : properChowPushforward C _ _
      (eqToHom (congrArg Scheme.IdealSheafData.subscheme (capDivisor_eq π L s fY t))) _ (k - p)
      (properPushforwardDescends C _ _ _ _ _)
      y = _ :=
    chowPushforwardOfIso_eqToHom_eq_of_heq C
      (pullback.fst fY (wTest π t) ≫ (fY ≫ f)) (k - p) (capDivisor_eq π L s fY t)
      (by rw [← Category.assoc, subschemeι_eqToHom (capDivisor_eq π L s fY t)]) hx
  refine Eq.trans ?_ h3
  rw [h2, hconv', ← hnat]
  rfl

end Commuting

end DivisorCommuting

/-! ### The commutation -/

section Statement

variable (C : ChowSituation.{u}) {X W U Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (π : W ⟶ X) [LocallyOfFiniteType π] (j : U ⟶ W) [IsOpenImmersion j] [Flat (j ≫ π)]
  (hU : AlgebraicGeometry.RelativeDimension (j ≫ π) 1) (L : W.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property L]
  (s : Γ(L, ⊤))
  (hcompl : Set.range (Stacks.Divisors.zeroScheme W L s).subschemeι.base = (Set.range j.base)ᶜ)
  (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
    (Stacks.Divisors.zeroScheme W L s).subscheme.sheaf.obj
    (Stacks.Divisors.zeroScheme W L s).subscheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme W L s).subschemeι).obj L))
  (fY : Y ⟶ X) [LocallyOfFiniteType fY] (p : ℤ)

/-- The class `C ∈ A⁰(Z(s) ⟶ X)` of Stacks 0F9J for the divisor `Z(s)` of `W`, with its source
read over the base through `(Z(s) ⟶ W ⟶ X) ≫ (X ⟶ S)`, the form in which Remark 0FA2 compares
classes. -/
abbrev infinityClassOverBase :
    BivariantClass C (gysinSystemOfInvertible C) ((gysinTripleInclusion L s ≫ π) ≫ f) f
      (gysinTripleInclusion L s ≫ π) rfl 0 :=
  bivariantClassCongrBase C (gysinSystemOfInvertible C) (gysinTripleInclusion L s ≫ π)
    (Category.assoc _ _ _).symm rfl (hv := Category.assoc _ _ _) (hv' := rfl) 0
    (infinityClass C f π j hU L s hcompl htriv)

/-- The cap operation of `infinityClassOverBase` is that of the class. -/
theorem infinityClassOverBase_cap {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ f) k) :
    (infinityClassOverBase C f π j hU L s hcompl htriv).cap t k α =
      chowGroupCongr C (by simp only [Category.assoc]) (k - 0)
        (infinityCap C f π j hU L s hcompl htriv t k α) :=
  eq_of_heq ((bivariantClassCongrBase_cap C (gysinSystemOfInvertible C) _ _ _ 0
    (infinityClass C f π j hU L s hcompl htriv) t k α α HEq.rfl).trans
    (chowGroupCongr_heq C _ _ _).symm)

/-- **Stacks 0FAS for the class of a divisor with flat complement, in the form of
Remark 0FA2.** Let `π : W ⟶ X`, `j : U ⟶ W` and `Z(s) ⊆ W` be as in
`Stacks.Chow.GysinAtInfinity.infinityClass`, so that `C ∈ A⁰(Z(s) ⟶ X)` caps `α` to `i^* β` for
any lift `β` of `α`. Let `fY : Y ⟶ X` be locally of finite type and `c ∈ A^p(Y ⟶ X)`. Then `C`
and `c` commute: `C ∩ (c ∩ α) = c ∩ (C ∩ α)` for every `α ∈ CH_k(T)` and every `T ⟶ X` locally of
finite type, the two sides compared by the canonical isomorphism
`Z(s) ×_X (Y ×_X T) ≅ Y ×_X (Z(s) ×_X T)`.

Choose a lift `β ∈ A_{k+1}(W ×_X T)` of `α`. Then `c ∩ β` is a lift of `c ∩ α`
(`Stacks.Chow.GysinAtInfinity.isLift_capLift`), so `C ∩ (c ∩ α) = i^*(c ∩ β)`, while
`c ∩ (C ∩ α) = c ∩ i^* β = i^*(c ∩ β)` by condition (3) of Stacks 0B76 for `c`. -/
theorem infinityClass_bivariantCommute
    (c : BivariantClass C (gysinSystemOfInvertible C) (fY ≫ f) f fY rfl p) :
    BivariantCommute C (gysinSystemOfInvertible C) f (gysinTripleInclusion L s ≫ π) fY 0 p
      (infinityClassOverBase C f π j hU L s hcompl htriv) c := by
  intro T t _ k α
  obtain ⟨β, hβ⟩ := exists_isLift C f π j hU t k α
  rw [bivariantIteratedCap_apply, bivariantIteratedCap_apply, infinityClassOverBase_cap,
    infinityClassOverBase_cap,
    DivisorCommuting.infinityCap_eq_of_isLift' C f π j hU L s hcompl htriv (yTest fY t)
      (isLift_capLift C f π j hU fY c t k hβ),
    DivisorCommuting.infinityCap_eq_of_isLift' C f π j hU L s hcompl htriv t hβ, capLift,
    chowGroupDegreeEquiv_chowPushforwardOfIso C _ _ (commuteComparisonHom fY π t)]
  set x := c.cap (DivisorCommuting.wTest π t) (k + 1)
    (chowGroupCongr C (Category.assoc _ _ _).symm (k + 1) β)
  have hL := DivisorCommuting.gysin_comparison C f π L s fY t k
    (chowGroupDegreeEquiv C _ (by ring : k + 1 - p = k - p + 1) x)
  have hR := DivisorCommuting.cap_divisorGysin C f π L s fY c t k β
  rw [eqMp_chowGroup C _ (by ring : k + 1 - p = k - p + 1)] at hR
  refine eq_of_heq (HEq.trans ?_ ((heq_of_eq (hL.trans hR.symm)).trans ?_))
  · refine chowPushforwardOfIso_heq_congr_base C _ _ rfl _ _ (by simp only [Category.assoc]) rfl
      (sub_zero _) _ _ ?_
    exact (chowGroupCongr_heq C _ _ _).trans (chowGroupDegreeEquiv_heq C _ _ _)
  · refine HEq.trans ?_ (chowGroupDegreeEquiv_heq C _ _ _).symm
    refine heq_cap_of_heq C (gysinSystemOfInvertible C) (fY ≫ f) f fY rfl p c
      (DivisorCommuting.zTest π L s t) (sub_zero k).symm ?_
    exact (chowGroupCongr_heq C _ _ _).trans ((chowGroupDegreeEquiv_heq C _ _ _).symm.trans
      ((chowGroupCongr_heq C _ _ _).symm.trans (chowGroupCongr_heq C _ _ _).symm))

end Statement

end GysinAtInfinity

end Stacks.Chow

end
