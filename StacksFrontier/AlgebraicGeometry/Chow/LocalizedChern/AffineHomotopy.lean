module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.VirtualNormalCommutingEveryClass
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.GysinAtInfinityRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Unconditional

/-!
# Homotopy invariance of bivariant classes over the affine line

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `π : 𝐀¹_X ⟶ X` be the affine line over `X`, let `z : Z ⟶ X` be locally of
finite type and let `c ∈ A^p(Z ×_X 𝐀¹_X ⟶ 𝐀¹_X)` be a bivariant class. For two sections
`σ, σ' : X ⟶ 𝐀¹_X` of `π` whose images are effective Cartier divisors, presented as zero schemes of
sections of invertible modules, the two restrictions of `c` along `σ` and `σ'` agree: on every test
scheme `g : T ⟶ X`,

  `c ∩_{g ≫ σ} α = c ∩_{g ≫ σ'} α`   in   `A_{k-p}(Z ×_X T)`,

after the canonical identifications of `Z ×_X 𝐀¹_X ×_{𝐀¹_X} T` with `Z ×_X T` along `g ≫ σ` and
`g ≫ σ'`. This is the fact "`i_0^* = i_1^*` by definition of rational equivalence (more precisely
this follows from the formulae in Lemma 0F96)" that the proof of Stacks 0FBD uses.

## Implementation notes

Write `A = 𝐀¹_X ×_X T`, an affine line over `T`, and `h : A ⟶ 𝐀¹_X`, `pr : A ⟶ T` for the two
projections. The divisor `D ⊆ 𝐀¹_X` of `σ` pulls back to a divisor `D_A ⊆ A` mapping isomorphically
to `T`, so the Gysin map of `D_A` is a left inverse of flat pullback along `pr` (Stacks 02TR).
Condition (3) of Stacks 0B76 for `c` at the test scheme `h` then gives
`c ∩_{g ≫ σ} α = i_{D}^*(c ∩_h pr^*α)`, read through `D_A ≅ T`. The class `c ∩_h pr^*α` lives on
`Z ×_X A`, an affine line over `Z ×_X T`, so it is a flat pullback (Stacks 02TT), on which the
Gysin map of the pulled-back divisor is again the inverse of flat pullback (Stacks 02TR). Hence
`c ∩_{g ≫ σ} α` is the class on `Z ×_X T` whose flat pullback is `c ∩_h pr^*α`, independently of
`σ`.

## Main definitions

* `Stacks.Chow.SectionDivisor`: a section of `π : V ⟶ X` presented as the zero scheme of a
  section of an invertible module which is an effective Cartier divisor.
* `Stacks.Chow.SectionDivisor.section`: the section `X ⟶ V` it presents.
* `Stacks.Chow.testIso`, `Stacks.Chow.testMap`: the identifications of the base changes of
  `Z ×_X V ⟶ V` with `Z ×_X T`.

## Main results

* `Stacks.Chow.SectionDivisor.gysin_flatPullbackChow`: Stacks 02TR on every base change of `π`,
  for the pulled-back divisor.
* `Stacks.Chow.isPullback_testMap`: `Z ×_X V ×_V A` is the base change of `π` along
  `Z ×_X T ⟶ X`.
* `Stacks.Chow.SectionDivisor.test_comp_eq_id`: the identifications of the pulled-back divisor
  with `Z ×_X T` compose to the identity.
* `Stacks.Chow.SectionDivisor.cap_section_eq`: the restrictions of a bivariant class along the
  sections of two divisors agree.

## References

* [Stacks Project, Tag 0FBD](https://stacks.math.columbia.edu/tag/0FBD)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Divisors of a line over `X` mapping isomorphically to `X` -/

/-- **A section of a morphism `π : V ⟶ X` presented as a divisor**: an invertible module on `V`
with a global section whose zero scheme is an effective Cartier divisor mapping isomorphically to
`X`. For `π` the affine line `𝐀¹_X ⟶ X` these are the sections `X ⟶ 𝐀¹_X` at the points `0`
and `1`. -/
structure SectionDivisor {V X : Scheme.{u}} (π : V ⟶ X) where
  /-- The invertible module. -/
  L : V.Modules
  [isInvertible : AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj
    V.ringCatSheaf.property L]
  /-- The global section. -/
  s : Γ(L, ⊤)
  /-- Its zero scheme is an effective Cartier divisor. -/
  isEffectiveCartierDivisor :
    Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme _ L s)
  /-- Its zero scheme maps isomorphically to `X`. -/
  isIso : IsIso ((Stacks.Divisors.zeroScheme _ L s).subschemeι ≫ π)

attribute [instance] SectionDivisor.isInvertible SectionDivisor.isIso

namespace SectionDivisor

variable {V X : Scheme.{u}} {π : V ⟶ X} (D : SectionDivisor π)

/-- The zero scheme of the presentation. -/
abbrev divisor : V.IdealSheafData := Stacks.Divisors.zeroScheme _ D.L D.s

/-- **The section `X ⟶ V` presented by the divisor**: the inverse of `D ⟶ X` followed by the
inclusion of `D`. -/
def «section» : X ⟶ V :=
  inv (D.divisor.subschemeι ≫ π) ≫ D.divisor.subschemeι

/-- The section presented by the divisor is a section of `π`. -/
@[reassoc (attr := simp)]
theorem section_comp : D.section ≫ π = 𝟙 X := by
  rw [«section», Category.assoc, IsIso.inv_hom_id]

/-- The inclusion of the divisor factors through the section. -/
theorem subschemeι_eq : D.divisor.subschemeι = (D.divisor.subschemeι ≫ π) ≫ D.section := by
  rw [«section», IsIso.hom_inv_id_assoc]

/-! ### Pulling the divisor back along a base change of `π` -/

section BaseChange

variable {U B : Scheme.{u}} {p' : U ⟶ V} {q : U ⟶ B} {k : B ⟶ X} (sq : IsPullback p' q π k)

/-- The pulled-back module. -/
abbrev pullbackL (p' : U ⟶ V) : U.Modules := (Scheme.Modules.pullback p').obj D.L

/-- The pulled-back section. -/
abbrev pullbackS (p' : U ⟶ V) : Γ(D.pullbackL p', ⊤) :=
  AlgebraicGeometry.pullbackGlobalSections p' D.L D.s

/-- The zero scheme of the pulled-back section. -/
abbrev pullbackDivisor (p' : U ⟶ V) : U.IdealSheafData :=
  Stacks.Divisors.zeroScheme U (D.pullbackL p') (D.pullbackS p')

/-- The pulled-back module is invertible. -/
instance (p' : U ⟶ V) :
    AlgebraicGeometry.SheafOfModules.IsInvertible U.sheaf.obj U.ringCatSheaf.property
      (D.pullbackL p') :=
  Stacks.ChernCap42.isInvertible_sheafObj_modulePullback _ _

/-- The zero scheme of the pulled-back section is the inverse image of the divisor. -/
theorem pullbackDivisor_eq (p' : U ⟶ V) : D.pullbackDivisor p' = D.divisor.comap p' :=
  Stacks.Divisors.zeroScheme_pullback p' D.L D.s

include sq in
/-- **The pulled-back divisor maps isomorphically to the base of the base change.** -/
theorem isIso_pullbackDivisor : IsIso ((D.pullbackDivisor p').subschemeι ≫ q) := by
  rw [D.pullbackDivisor_eq]
  exact isIso_comap_subschemeι_comp_of_isPullback sq D.divisor

include sq in
/-- **The pulled-back divisor lies over the section**: on it, `p'` is `q` followed by `k` and the
section. -/
theorem pullbackDivisor_subschemeι_comp_section :
    ((D.pullbackDivisor p').subschemeι ≫ q) ≫ (k ≫ D.section) =
      (D.pullbackDivisor p').subschemeι ≫ p' := by
  have key : ∀ J' : U.IdealSheafData, J' = D.divisor.comap p' →
      J'.subschemeι ≫ q ≫ k ≫ D.section = J'.subschemeι ≫ p' := by
    intro J' hJ'
    subst hJ'
    have hm := Scheme.IdealSheafData.subschemeMap_subschemeι (D.divisor.comap p') D.divisor p'
      (D.divisor.le_map_comap p')
    have e1 : (D.divisor.comap p').subschemeι ≫ p' =
        (D.divisor.comap p').subschemeι ≫ p' ≫ π ≫ D.section := by
      rw [← hm, D.subschemeι_eq]
      simp only [Category.assoc]
      rw [← Category.assoc _ D.divisor.subschemeι, hm, Category.assoc]
    rw [e1, ← Category.assoc p', sq.w, Category.assoc]
  exact (Category.assoc _ _ _).trans (key _ (D.pullbackDivisor_eq _))

variable (C : ChowSituation.{u}) (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sB : B ⟶ C.S)
  [LocallyOfFiniteType sB] (hbase : q ≫ sB = sU) [LocallyOfFiniteType q] [Flat q]
  (hq : AlgebraicGeometry.RelativeDimension q 1)

include sq in
/-- **Stacks 02TR on a base change of `π`.** Let `L'` be an invertible module on a base change `U`
of `π` with a section whose zero scheme is the inverse image of the divisor. The Gysin map of that
section is a left inverse of flat pullback along the base change `q : U ⟶ B` of `π`, read on the
zero scheme through its isomorphism with `B`. -/
theorem gysin_flatPullbackChow (L' : U.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible U.sheaf.obj U.ringCatSheaf.property L']
    (s' : Γ(L', ⊤)) (hs' : Stacks.Divisors.zeroScheme U L' s' = D.divisor.comap p') (n : ℤ)
    (α : chowGroup C sB n) :
    haveI : IsIso ((Stacks.Divisors.zeroScheme U L' s').subschemeι ≫ q) := by
      rw [hs']; exact isIso_comap_subschemeι_comp_of_isPullback sq D.divisor
    (gysinSystemOfInvertible C).onChow sU L' s' n
        (flatPullbackChow C sU sB q hbase 1 hq n (flatPullbackDescends C _ _ _ _ _ _ _) α) =
      chowPushforwardOfIso C sB ((Stacks.Divisors.zeroScheme U L' s').subschemeι ≫ sU)
        (inv ((Stacks.Divisors.zeroScheme U L' s').subschemeι ≫ q))
        (by rw [IsIso.inv_comp_eq, Category.assoc, hbase]) n α := by
  have : IsIso ((Stacks.Divisors.zeroScheme U L' s').subschemeι ≫ q) := by
    rw [hs']; exact isIso_comap_subschemeι_comp_of_isPullback sq D.divisor
  have hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor q
      (Stacks.Divisors.zeroScheme U L' s') := by
    refine ⟨?_, inferInstance⟩
    rw [hs']
    have : Flat (D.divisor.subschemeι ≫ π) := inferInstance
    exact AlgebraicGeometry.isEffectiveCartierDivisor_comap_of_isPullback _ _ sq.flip _
      D.isEffectiveCartierDivisor
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by ring⟩
  exact gysinSystemOfInvertible_onChow_flatPullbackChow_of_isIso C sU sB q hbase hq _ _ hD m α

end BaseChange

end SectionDivisor

/-- Pushing forward along an isomorphism after its inverse is a transport of the structure
morphism. -/
theorem chowPushforwardOfIso_inv_comp_self (C : ChowSituation.{u}) {A B : Scheme.{u}}
    {sA : A ⟶ C.S} [LocallyOfFiniteType sA] {sB sB' : B ⟶ C.S} [LocallyOfFiniteType sB]
    [LocallyOfFiniteType sB'] (w : A ⟶ B) [IsIso w] (h₁ : inv w ≫ sA = sB) (h₂ : w ≫ sB' = sA)
    (k : ℤ) (x : chowGroup C sB k) :
    chowPushforwardOfIso C sA sB' w h₂ k (chowPushforwardOfIso C sB sA (inv w) h₁ k x) =
      chowGroupCongr C (by rw [← h₁, ← h₂, IsIso.inv_hom_id_assoc]) k x := by
  rw [chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_congr_apply C sB sB' (inv w ≫ w) (𝟙 B)
    (IsIso.inv_hom_id w) _ (by rw [Category.id_comp, ← h₁, ← h₂, IsIso.inv_hom_id_assoc]),
    chowPushforwardOfIso_id_eq_chowGroupCongr]

/-! ### The homotopy -/

section Homotopy

variable {X Z Z' V T A ZT : Scheme.{u}} {π : V ⟶ X} {z : Z ⟶ X} {z' : Z' ⟶ V} {zf : Z' ⟶ Z}
  (sqZ : IsPullback zf z' z π) {g : T ⟶ X} {h : A ⟶ V} {pr : A ⟶ T}
  (sqA : IsPullback h pr π g) {zfT : ZT ⟶ Z} {zsT : ZT ⟶ T} (sqT : IsPullback zfT zsT z g)

include sqZ in
/-- The base change of `Z' ⟶ V` along a test morphism `v : T ⟶ V` is a base change of `z`
along `v ≫ π`. -/
theorem isPullback_testBaseChange (v : T ⟶ V) :
    IsPullback (pullback.fst z' v ≫ zf) (pullback.snd z' v) z (v ≫ π) :=
  (IsPullback.of_hasPullback z' v).paste_horiz sqZ

/-- **The identification along a test morphism through `V`**: for `v : T ⟶ V` over `g`, the base
change of `Z' ⟶ V` along `v` is `Z ×_X T`. -/
noncomputable def testIso (v : T ⟶ V) (hv : v ≫ π = g) : pullback z' v ≅ ZT :=
  (hv ▸ isPullback_testBaseChange sqZ v).isoIsPullback _ _ sqT

/-- `testIso` commutes with the projections to `Z`. -/
@[reassoc (attr := simp)]
theorem testIso_hom_fst (v : T ⟶ V) (hv : v ≫ π = g) :
    (testIso sqZ sqT v hv).hom ≫ zfT = pullback.fst z' v ≫ zf := by
  subst hv
  exact IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- `testIso` commutes with the projections to `T`. -/
@[reassoc (attr := simp)]
theorem testIso_hom_snd (v : T ⟶ V) (hv : v ≫ π = g) :
    (testIso sqZ sqT v hv).hom ≫ zsT = pullback.snd z' v := by
  subst hv
  exact IsPullback.isoIsPullback_hom_snd _ _ _ _

include sqZ sqA in
/-- The projections of `Z' ×_V A` to `Z` and to `T` agree over `X`. -/
theorem testMap_w : (pullback.fst z' h ≫ zf) ≫ z = (pullback.snd z' h ≫ pr) ≫ g := by
  rw [Category.assoc, sqZ.w, ← Category.assoc, pullback.condition, Category.assoc,
    Category.assoc, sqA.w]

/-- The comparison morphism from the base change of `Z' ⟶ V` along `h : A ⟶ V` to `Z ×_X T`. -/
noncomputable def testMap : pullback z' h ⟶ ZT :=
  sqT.lift (pullback.fst z' h ≫ zf) (pullback.snd z' h ≫ pr) (testMap_w sqZ sqA)

/-- `testMap` commutes with the projections to `Z`. -/
@[reassoc (attr := simp)]
theorem testMap_fst : testMap sqZ sqA sqT ≫ zfT = pullback.fst z' h ≫ zf :=
  sqT.lift_fst _ _ _

/-- `testMap` commutes with the projections to `T`. -/
@[reassoc (attr := simp)]
theorem testMap_snd : testMap sqZ sqA sqT ≫ zsT = pullback.snd z' h ≫ pr :=
  sqT.lift_snd _ _ _

/-- **`Z' ×_V A` is the base change of `π` along `Z ×_X T ⟶ X`.** -/
theorem isPullback_testMap :
    IsPullback (pullback.snd z' h ≫ h) (testMap sqZ sqA sqT) π (zsT ≫ g) := by
  have outer : IsPullback (testMap sqZ sqA sqT ≫ zfT) (pullback.snd z' h) z (pr ≫ g) := by
    rw [testMap_fst, ← sqA.w]
    exact (IsPullback.of_hasPullback _ _).paste_horiz sqZ
  have left : IsPullback (testMap sqZ sqA sqT) (pullback.snd z' h) zsT pr :=
    IsPullback.of_right outer (testMap_snd sqZ sqA sqT) sqT
  exact left.flip.paste_horiz sqA

/-- The inverse image of a divisor mapping isomorphically to `X` maps isomorphically to
`Z ×_X T`. -/
private theorem isIso_subschemeι_comp_testMap (J : V.IdealSheafData) [IsIso (J.subschemeι ≫ π)]
    (J' : (pullback z' h).IdealSheafData) (hJ : J' = J.comap (pullback.snd z' h ≫ h)) :
    IsIso (J'.subschemeι ≫ testMap sqZ sqA sqT) := by
  subst hJ
  exact isIso_comap_subschemeι_comp_of_isPullback (isPullback_testMap sqZ sqA sqT) _

variable (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
  [LocallyOfFiniteType π] [Flat π] (hπ : AlgebraicGeometry.RelativeDimension π 1)
  (hb : IsAffineSpaceBundle π 1) [LocallyOfFiniteType z] [LocallyOfFiniteType z']
  [LocallyOfFiniteType g] {p : ℤ}

omit [LocallyOfFiniteType π] [Flat π] [LocallyOfFiniteType g] in
include sqA in
/-- The two structure morphisms `A ⟶ C.S`, through `T` and through `V`, agree. -/
theorem testStructure_eq (C : ChowSituation.{u}) (f : X ⟶ C.S) : pr ≫ g ≫ f = h ≫ π ≫ f := by
  rw [← Category.assoc, ← sqA.w, Category.assoc]

/-- The invertible module of the divisor pulled back to `Z' ×_V A`. -/
abbrev SectionDivisor.testL (D : SectionDivisor π) (z' : Z' ⟶ V) (h : A ⟶ V) :
    (pullback z' h).Modules :=
  (Scheme.Modules.pullback (pullback.snd z' h)).obj (D.pullbackL h)

/-- The section of the divisor pulled back to `Z' ×_V A`. -/
abbrev SectionDivisor.testS (D : SectionDivisor π) (z' : Z' ⟶ V) (h : A ⟶ V) :
    Γ(D.testL z' h, ⊤) :=
  AlgebraicGeometry.pullbackGlobalSections (pullback.snd z' h) (D.pullbackL h) (D.pullbackS h)

/-- The invertible module of the divisor pulled back to `Z' ×_V A` is invertible. -/
instance (D : SectionDivisor π) (z' : Z' ⟶ V) (h : A ⟶ V) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (pullback z' h).sheaf.obj
      (pullback z' h).ringCatSheaf.property (D.testL z' h) :=
  Stacks.ChernCap42.isInvertible_sheafObj_modulePullback _ _

omit [LocallyOfFiniteType π] [Flat π] [LocallyOfFiniteType z'] in
/-- The divisor pulled back to `Z' ×_V A` is the inverse image of `D`. -/
theorem SectionDivisor.zeroScheme_testL (D : SectionDivisor π) :
    Stacks.Divisors.zeroScheme (pullback z' h) (D.testL z' h) (D.testS z' h) =
      D.divisor.comap (pullback.snd z' h ≫ h) := by
  rw [Stacks.Divisors.zeroScheme_pullback]
  exact (congrArg (fun J => Scheme.IdealSheafData.comap J _) (D.pullbackDivisor_eq _)).trans
    (Scheme.IdealSheafData.comap_comp _ _ _).symm

/-- The section presented by a divisor is locally of finite type. -/
instance (D : SectionDivisor π) : LocallyOfFiniteType D.section := by
  have : LocallyOfFiniteType (D.section ≫ π) := by rw [SectionDivisor.section_comp]; infer_instance
  exact LocallyOfFiniteType.of_comp (f := D.section) (g := π) this

omit [Flat π] in
include sqA in
/-- **Condition (3) of Stacks 0B76 at the divisor of a section.** For `α ∈ A_k(T)` the cap of `c`
along `g ≫ σ` is the Gysin map of the pulled-back divisor applied to `c ∩_h pr^*α`, read through
the identifications of the base changes. -/
theorem SectionDivisor.cap_section_eq_gysin (c : BivariantClass C (gysinSystemOfInvertible C)
    (z' ≫ π ≫ f) (π ≫ f) z' rfl p) (D : SectionDivisor π) [LocallyOfFiniteType pr]
    [Flat pr] (hpr : AlgebraicGeometry.RelativeDimension pr 1) [LocallyOfFiniteType h] (k : ℤ)
    (α : chowGroup C (g ≫ f) k) :
    haveI := D.isIso_pullbackDivisor sqA
    c.cap (g ≫ D.section) k (chowGroupCongr C (by simp) k α) =
      chowPushforwardOfIso C
        ((Stacks.Divisors.zeroScheme (pullback z' h) (D.testL z' h) (D.testS z' h)).subschemeι ≫
          (pullback.fst z' h ≫ (z' ≫ (π ≫ f))))
        (pullback.fst z' (g ≫ D.section) ≫ (z' ≫ (π ≫ f)))
        ((bivariantDivisorBaseChangeIso z' h (D.pullbackL h) (D.pullbackS h)).inv ≫
          (testBaseChangeIso z' (g ≫ D.section) ((D.pullbackDivisor h).subschemeι ≫ pr)
            ((D.pullbackDivisor h).subschemeι ≫ h)
            (D.pullbackDivisor_subschemeι_comp_section sqA)).hom)
        (by
          rw [Category.assoc, testBaseChangeIso_hom_fst_assoc, Iso.inv_comp_eq,
            reassoc_of% (bivariantDivisorBaseChangeIso_hom_comp_fst z' h (D.pullbackL h)
              (D.pullbackS h))]) (k - p)
        ((gysinSystemOfInvertible C).onChow (pullback.fst z' h ≫ (z' ≫ (π ≫ f)))
          (D.testL z' h) (D.testS z' h) (k - p)
          (chowGroupDegreeEquiv C _ (by ring : k + 1 - p = k - p + 1)
            (c.cap h (k + 1) (chowGroupCongr C (testStructure_eq sqA C f) (k + 1)
              (flatPullbackChow C (pr ≫ g ≫ f) (g ≫ f) pr rfl 1 hpr k
                (flatPullbackDescends C _ _ _ _ _ _ _) α))))) := by
  have := D.isIso_pullbackDivisor sqA
  have huq : ((D.pullbackDivisor h).subschemeι ≫ pr) ≫ ((g ≫ D.section) ≫ π ≫ f) =
      (D.pullbackDivisor h).subschemeι ≫ (pr ≫ g ≫ f) := by
    simp
  have h1 := BivariantClass.cap_chowPushforwardOfIso_gysin c h (D.pullbackL h) (D.pullbackS h)
    (g ≫ D.section) _ (D.pullbackDivisor_subschemeι_comp_section sqA) (testStructure_eq sqA C f)
    rfl huq k (flatPullbackChow C (pr ≫ g ≫ f) (g ≫ f) pr rfl 1 hpr k
      (flatPullbackDescends C _ _ _ _ _ _ _) α)
  have h2 := D.gysin_flatPullbackChow sqA C (pr ≫ g ≫ f) (g ≫ f) rfl hpr (D.pullbackL h)
    (D.pullbackS h) (D.pullbackDivisor_eq h) k α
  rw [h2, chowPushforwardOfIso_inv_comp_self] at h1
  exact h1

omit [LocallyOfFiniteType f] [LocallyOfFiniteType π] [Flat π] [LocallyOfFiniteType z]
  [LocallyOfFiniteType z'] [LocallyOfFiniteType g] in
include sqZ in
/-- `testIso` along `g ≫ D.section` commutes with the structure morphisms to `C.S`. -/
theorem testIso_base (D : SectionDivisor π) :
    (testIso sqZ sqT (g ≫ D.section) (by simp)).hom ≫ (zfT ≫ z ≫ f) =
      pullback.fst z' (g ≫ D.section) ≫ (z' ≫ (π ≫ f)) := by
  rw [testIso_hom_fst_assoc, ← Category.assoc zf, sqZ.w, Category.assoc]

omit [LocallyOfFiniteType f] [LocallyOfFiniteType π] [Flat π] [LocallyOfFiniteType z]
  [LocallyOfFiniteType z'] [LocallyOfFiniteType g] in
include sqZ sqA in
/-- `testMap` commutes with the structure morphisms to `C.S`. -/
theorem testMap_base :
    testMap sqZ sqA sqT ≫ (zfT ≫ z ≫ f) = pullback.fst z' h ≫ (z' ≫ (π ≫ f)) := by
  rw [testMap_fst_assoc, ← Category.assoc zf, sqZ.w, Category.assoc]

omit [LocallyOfFiniteType z] [LocallyOfFiniteType g] in
omit [LocallyOfFiniteType π] [Flat π] [LocallyOfFiniteType z'] in
include sqZ sqA sqT in
/-- **The identifications compose to the identity of `Z ×_X T`.** -/
theorem SectionDivisor.test_comp_eq_id (D : SectionDivisor π) :
    haveI : IsIso ((Stacks.Divisors.zeroScheme (pullback z' h) (D.testL z' h)
        (D.testS z' h)).subschemeι ≫ testMap sqZ sqA sqT) := by
      rw [D.zeroScheme_testL]
      exact isIso_comap_subschemeι_comp_of_isPullback (isPullback_testMap sqZ sqA sqT) _
    haveI := D.isIso_pullbackDivisor sqA
    inv ((Stacks.Divisors.zeroScheme (pullback z' h) (D.testL z' h)
        (D.testS z' h)).subschemeι ≫ testMap sqZ sqA sqT) ≫
        (((bivariantDivisorBaseChangeIso z' h (D.pullbackL h) (D.pullbackS h)).inv ≫
          (testBaseChangeIso z' (g ≫ D.section) ((D.pullbackDivisor h).subschemeι ≫ pr)
            ((D.pullbackDivisor h).subschemeι ≫ h)
            (D.pullbackDivisor_subschemeι_comp_section sqA)).hom) ≫
      (testIso sqZ sqT (g ≫ D.section) (by simp)).hom) = 𝟙 _ := by
  have := isIso_subschemeι_comp_testMap sqZ sqA sqT D.divisor _ D.zeroScheme_testL
  have := D.isIso_pullbackDivisor sqA
  have hw' : (testBaseChangeIso z' (g ≫ D.section) ((D.pullbackDivisor h).subschemeι ≫ pr)
        ((D.pullbackDivisor h).subschemeι ≫ h)
        (D.pullbackDivisor_subschemeι_comp_section sqA)).hom ≫
      (testIso sqZ sqT (g ≫ D.section) (by simp)).hom =
      (bivariantDivisorBaseChangeIso z' h (D.pullbackL h) (D.pullbackS h)).hom ≫
        ((Stacks.Divisors.zeroScheme (pullback z' h) (D.testL z' h)
          (D.testS z' h)).subschemeι ≫ testMap sqZ sqA sqT) := by
    refine sqT.hom_ext ?_ ?_
    · rw [Category.assoc, testIso_hom_fst, testBaseChangeIso_hom_fst_assoc,
        Category.assoc, Category.assoc, testMap_fst,
        reassoc_of% (bivariantDivisorBaseChangeIso_hom_comp_fst z' h (D.pullbackL h)
          (D.pullbackS h))]
    · rw [Category.assoc, testIso_hom_snd, testBaseChangeIso_hom_snd,
        Category.assoc, Category.assoc, testMap_snd,
        bivariantDivisorBaseChangeIso_hom_comp_snd_assoc]
  rw [Category.assoc (bivariantDivisorBaseChangeIso z' h (D.pullbackL h) (D.pullbackS h)).inv,
    hw', Iso.inv_hom_id_assoc, IsIso.inv_hom_id]

omit [Flat π] in
include sqZ sqA sqT in
/-- **The restriction of `c` along the section of a divisor, through flat pullback.** Let `δ` be a
class on `Z ×_X T` whose flat pullback to `Z' ×_V A` is `c ∩_h pr^*α`. Then the cap of `c` along
`g ≫ σ`, read on `Z ×_X T`, is `δ`, for the section `σ` of every divisor `D`: the Gysin map of `D`
inverts flat pullback twice (Stacks 02TR) and commutes with `c` (condition (3) of Stacks 0B76). -/
theorem SectionDivisor.cap_section_eq_of_flatPullback
    (c : BivariantClass C (gysinSystemOfInvertible C) (z' ≫ π ≫ f) (π ≫ f) z' rfl p)
    (D : SectionDivisor π) [LocallyOfFiniteType pr] [Flat pr]
    (hpr : AlgebraicGeometry.RelativeDimension pr 1) [LocallyOfFiniteType h]
    [LocallyOfFiniteType (testMap sqZ sqA sqT)] [Flat (testMap sqZ sqA sqT)]
    (hT : AlgebraicGeometry.RelativeDimension (testMap sqZ sqA sqT) 1)
    [LocallyOfFiniteType zfT] (k : ℤ) (α : chowGroup C (g ≫ f) k)
    (δ : chowGroup C (zfT ≫ z ≫ f) (k - p))
    (hδ : flatPullbackChow C (pullback.fst z' h ≫ (z' ≫ (π ≫ f))) (zfT ≫ z ≫ f)
        (testMap sqZ sqA sqT) (testMap_base sqZ sqA sqT C f) 1 hT (k - p)
        (flatPullbackDescends C _ _ _ _ _ _ _) δ =
      chowGroupDegreeEquiv C _ (by ring : k + 1 - p = k - p + 1)
        (c.cap h (k + 1) (chowGroupCongr C (testStructure_eq sqA C f) (k + 1)
          (flatPullbackChow C (pr ≫ g ≫ f) (g ≫ f) pr rfl 1 hpr k
            (flatPullbackDescends C _ _ _ _ _ _ _) α)))) :
    chowPushforwardOfIso C (pullback.fst z' (g ≫ D.section) ≫ (z' ≫ (π ≫ f))) (zfT ≫ z ≫ f)
        (testIso sqZ sqT (g ≫ D.section) (by simp)).hom (testIso_base sqZ sqT C f D) (k - p)
        (c.cap (g ≫ D.section) k (chowGroupCongr C (by simp) k α)) = δ := by
  have := isIso_subschemeι_comp_testMap sqZ sqA sqT D.divisor _ D.zeroScheme_testL
  rw [D.cap_section_eq_gysin sqA C f c hpr k α, ← hδ,
    D.gysin_flatPullbackChow (isPullback_testMap sqZ sqA sqT) C _ _ (testMap_base sqZ sqA sqT C f)
      hT _ _ D.zeroScheme_testL (k - p) δ,
    chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _) (D.test_comp_eq_id sqZ sqA sqT) _
      (Category.id_comp _), chowPushforwardOfIso_id]

omit [Flat π] in
include sqZ sqA sqT in
/-- **Homotopy invariance of bivariant classes over an affine line.** Let `π : V ⟶ X` be an
affine-space bundle of rank one (for instance `𝐀¹_X ⟶ X`), let `c` be a bivariant class of degree
`p` for the base change `Z' = Z ×_X V ⟶ V` of `z : Z ⟶ X`, and let `σ, σ'` be the sections of two
divisors of `V` mapping isomorphically to `X`. On every test scheme `g : T ⟶ X` the cap
operations of `c` along `g ≫ σ` and `g ≫ σ'` agree, read on `Z ×_X T`: both are the class whose
flat pullback to `Z' ×_V (V ×_X T)` is `c ∩ pr^*α` (Stacks 02TT, 02TR and condition (3) of
Stacks 0B76). This is "`i_0^* = i_1^*`" in the proof of Stacks 0FBD. -/
theorem SectionDivisor.cap_section_eq
    (c : BivariantClass C (gysinSystemOfInvertible C) (z' ≫ π ≫ f) (π ≫ f) z' rfl p)
    (D D' : SectionDivisor π) [LocallyOfFiniteType pr] [Flat pr]
    (hpr : AlgebraicGeometry.RelativeDimension pr 1) [LocallyOfFiniteType h]
    [LocallyOfFiniteType (testMap sqZ sqA sqT)] [Flat (testMap sqZ sqA sqT)]
    (hT : AlgebraicGeometry.RelativeDimension (testMap sqZ sqA sqT) 1)
    (hbT : IsAffineSpaceBundle (testMap sqZ sqA sqT) 1)
    [LocallyOfFiniteType zfT] (k : ℤ) (α : chowGroup C (g ≫ f) k) :
    chowPushforwardOfIso C (pullback.fst z' (g ≫ D.section) ≫ (z' ≫ (π ≫ f))) (zfT ≫ z ≫ f)
        (testIso sqZ sqT (g ≫ D.section) (by simp)).hom (testIso_base sqZ sqT C f D) (k - p)
        (c.cap (g ≫ D.section) k (chowGroupCongr C (by simp) k α)) =
      chowPushforwardOfIso C (pullback.fst z' (g ≫ D'.section) ≫ (z' ≫ (π ≫ f)))
        (zfT ≫ z ≫ f) (testIso sqZ sqT (g ≫ D'.section) (by simp)).hom
        (testIso_base sqZ sqT C f D') (k - p)
        (c.cap (g ≫ D'.section) k (chowGroupCongr C (by simp) k α)) := by
  obtain ⟨δ, hδ⟩ := flatPullbackChow_surjective_of_isAffineSpaceBundle_general C
    (pullback.fst z' h ≫ (z' ≫ (π ≫ f))) (zfT ≫ z ≫ f) (testMap sqZ sqA sqT)
    (testMap_base sqZ sqA sqT C f) 1 hT hbT (k - p)
    (chowGroupDegreeEquiv C _ (by ring : k + 1 - p = k - p + 1)
      (c.cap h (k + 1) (chowGroupCongr C (testStructure_eq sqA C f) (k + 1)
        (flatPullbackChow C (pr ≫ g ≫ f) (g ≫ f) pr rfl 1 hpr k
          (flatPullbackDescends C _ _ _ _ _ _ _) α))))
  have h1 := D.cap_section_eq_of_flatPullback sqZ sqA sqT C f c hpr hT k α δ
  have h2 := D'.cap_section_eq_of_flatPullback sqZ sqA sqT C f c hpr hT k α δ
  exact (h1 hδ).trans (h2 hδ).symm

end Homotopy

end Stacks.Chow

end
