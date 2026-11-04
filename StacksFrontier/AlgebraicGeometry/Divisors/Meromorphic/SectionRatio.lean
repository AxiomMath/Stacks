module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.Trivialization
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.PoleLocus
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.PrincipalDivisor

/-!
# The ratio of two regular meromorphic sections

Let `X` be a locally Noetherian integral scheme and let `L` be an invertible sheaf of
`𝒪_X`-modules. Two regular meromorphic sections `s`, `s'` of `L` differ by a unique invertible
rational function `f`, and their Weil divisors differ by the principal divisor of `f`:

`div_L(s) = div_L(s') + div(f)`.

## Main definitions

* `AlgebraicGeometry.IsMeromorphicSectionRatio`: `f` is the ratio of `s` and `s'`.
* `AlgebraicGeometry.meromorphicSectionRatio`: the ratio itself.

## Main results

* `AlgebraicGeometry.existsUnique_meromorphicSectionRatio`: the ratio exists and is unique.
* `AlgebraicGeometry.meromorphicWeilDivisor_eq_add_principalDivisor`: the divisor identity.

## References

* [Stacks Project, Tag 02SH](https://stacks.math.columbia.edu/tag/02SH)
* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 0BE3](https://stacks.math.columbia.edu/tag/0BE3)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### A regular meromorphic section has nonzero generic value -/

/-- The sections of an isomorphism of sheaves of commutative rings over a fixed open set are
injective. -/
theorem injective_sheafIso_hom_app {Y : TopCat.{u}} {F G : TopCat.Sheaf CommRingCat.{u} Y}
    (e : F ≅ G) (U : (Opens Y)ᵒᵖ) : Function.Injective (e.hom.hom.app U) := by
  have h1 : IsIso ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map e.hom) :=
    Functor.map_isIso _ e.hom
  have h2 : IsIso (e.hom.hom.app U) :=
    NatIso.isIso_app_of_isIso
      ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map e.hom) U
  exact (ConcreteCategory.bijective_of_isIso (e.hom.hom.app U)).1

/-- On an integral scheme the unit of the ring of meromorphic functions on the whole space is
nonzero. -/
theorem one_ne_zero_totalQuotientSheaf_top (X : Scheme.{u}) [IsIntegral X] :
    (1 : (totalQuotientSheaf X.sheaf).obj.obj (op (⊤ : X.Opens))) ≠ 0 := by
  intro h
  have hiso := injective_sheafIso_hom_app (totalQuotientSheafIsoConstant X).1
    (op (⊤ : X.Opens))
  have h0 : (1 : (constantSheafOnSpace X CommRingCat.{u} X.functionField).obj.obj
      (op (⊤ : X.Opens))) = 0 := by
    rw [← map_one ((totalQuotientSheafIsoConstant X).1.hom.hom.app (op (⊤ : X.Opens))).hom, h,
      map_zero]
  exact one_ne_zero (α := X.functionField)
    ((constantSheafOnSpaceSectionRingEquiv X X.functionField ⊤
      ⟨⟨genericPoint X, trivial⟩⟩).injective (by rw [map_one, map_zero, h0]))

/-- A regular meromorphic section on an integral scheme is nonzero on the whole space. -/
theorem val_top_ne_zero_of_isRegularMeromorphicSection [IsIntegral X] (L : X.Modules)
    (s : MeromorphicSection X.sheaf L) (hs : IsRegularMeromorphicSection X.sheaf L s) :
    s.val (op (⊤ : X.Opens)) ≠ 0 := by
  intro h
  refine one_ne_zero_totalQuotientSheaf_top X
    (SheafOfModules.app_injective_of_mono hs (op (⊤ : X.Opens)) ?_)
  have h1 := SheafOfModules.unitHomEquiv_apply_coe (meromorphicSectionSheaf X.sheaf L)
    ((meromorphicSectionSheaf X.sheaf L).unitHomEquiv.symm s) (op (⊤ : X.Opens))
  rw [Equiv.apply_symm_apply] at h1
  exact (h1.symm.trans h).trans (map_zero _).symm

/-- The element of the generic stalk representing a regular meromorphic section is nonzero. -/
theorem ne_zero_of_isRegularMeromorphicSection [IsIntegral X] (L : X.Modules)
    [L.IsQuasicoherent] (s : MeromorphicSection X.sheaf L)
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    {v : L.presheaf.stalk (genericPoint X)}
    (hv : (meromorphicSectionSheafIsoConstant X L).val.hom.val.app (op (⊤ : X.Opens))
      (s.val (op ⊤)) = constantGenericStalkModuleSection X L ⊤ v) : v ≠ 0 := by
  intro h0
  refine val_top_ne_zero_of_isRegularMeromorphicSection L s hs ?_
  have hco := (meromorphicSectionSheafIsoConstant X L).2 ⊤ 0 trivial
  have h1 : (L.presheaf.germ ⊤ (genericPoint X) trivial)
      (0 : L.val.obj (op (⊤ : X.Opens))) = 0 := map_zero _
  have hcv : (meromorphicSectionSheafIsoConstant X L).val.hom.val.app (op (⊤ : X.Opens))
      (s.val (op ⊤)) =
      (meromorphicSectionSheafIsoConstant X L).val.hom.val.app (op (⊤ : X.Opens))
        ((toMeromorphicSectionSheafAsModule X L).val.app (op (⊤ : X.Opens))
          (0 : L.val.obj (op (⊤ : X.Opens)))) := by
    rw [hv, h0]
    exact (hco.trans (congrArg (constantGenericStalkModuleSection X L ⊤) h1)).symm
  exact (injective_iso_hom_val_app (meromorphicSectionSheafIsoConstant X L).val
    (op (⊤ : X.Opens)) hcv).trans (map_zero _)

/-! ### The ratio of two regular meromorphic sections -/

variable (X)

/-- A regular meromorphic section is the constant section of a unique element of the generic
stalk, and that element is nonzero. -/
private theorem exists_ne_zero_unique_eq_constantGenericStalkModuleSection [IsIntegral X]
    (L : X.Modules) [L.IsQuasicoherent] (s : MeromorphicSection X.sheaf L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) :
    ∃ m : L.presheaf.stalk (genericPoint X),
      (meromorphicSectionSheafIsoConstant X L).val.hom.val.app (op (⊤ : X.Opens))
          (s.val (op ⊤)) = constantGenericStalkModuleSection X L ⊤ m ∧ m ≠ 0 ∧
        ∀ n : L.presheaf.stalk (genericPoint X),
          (meromorphicSectionSheafIsoConstant X L).val.hom.val.app (op (⊤ : X.Opens))
            (s.val (op ⊤)) = constantGenericStalkModuleSection X L ⊤ n → m = n := by
  obtain ⟨m, hm, hmuniq⟩ := exists_unique_eq_constantGenericStalkModuleSection X L
    ((meromorphicSectionSheafIsoConstant X L).val.hom.val.app (op (⊤ : X.Opens)) (s.val (op ⊤)))
  exact ⟨m, hm, ne_zero_of_isRegularMeromorphicSection L s hs hm, hmuniq⟩

/-- An invertible rational function `f` is the *ratio* of two meromorphic sections `s`, `s'` of
a quasi-coherent module `L` when `s = f · s'` read in the generic stalk: elements `m` and `m'` of
`L_η` representing `s` and `s'` under the comparison isomorphism of Tag 01X5 part (2) exist, and
any two such satisfy `m = f · m'`. -/
def IsMeromorphicSectionRatio [IsIntegral X] (L : X.Modules)
    (s s' : MeromorphicSection X.sheaf L) (f : (Stacks.Chow.rationalFunctions X)ˣ) : Prop :=
  ∃ _ : L.IsQuasicoherent,
    (∃ m m' : L.presheaf.stalk (genericPoint X),
        (meromorphicSectionSheafIsoConstant X L).val.hom.val.app (op (⊤ : X.Opens))
            (s.val (op ⊤)) = constantGenericStalkModuleSection X L ⊤ m ∧
          (meromorphicSectionSheafIsoConstant X L).val.hom.val.app (op (⊤ : X.Opens))
            (s'.val (op ⊤)) = constantGenericStalkModuleSection X L ⊤ m') ∧
      ∀ m m' : L.presheaf.stalk (genericPoint X),
        (meromorphicSectionSheafIsoConstant X L).val.hom.val.app (op (⊤ : X.Opens))
            (s.val (op ⊤)) = constantGenericStalkModuleSection X L ⊤ m →
          (meromorphicSectionSheafIsoConstant X L).val.hom.val.app (op (⊤ : X.Opens))
            (s'.val (op ⊤)) = constantGenericStalkModuleSection X L ⊤ m' →
            m = (Stacks.Chow.rationalFunctionsEquivFunctionField X).val
              (f : Stacks.Chow.rationalFunctions X) • m'

variable [IsIntegral X] (L : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s s' : MeromorphicSection X.sheaf L)

/-- Two regular meromorphic sections of an invertible module on an integral scheme have a unique
ratio in the units of the ring of rational functions. -/
@[stacks 02SH "ratio", ega "IV 20.1.8" "partial"]
theorem existsUnique_meromorphicSectionRatio
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    (hs' : IsRegularMeromorphicSection X.sheaf L s') :
    ∃! f : (Stacks.Chow.rationalFunctions X)ˣ, IsMeromorphicSectionRatio X L s s' f := by
  classical
  have hqc : L.IsQuasicoherent := isQuasicoherent_of_isInvertible L
  have hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := ‹_›
  obtain ⟨m, hm, hm0, hmuniq⟩ :=
    exists_ne_zero_unique_eq_constantGenericStalkModuleSection X L s hs
  obtain ⟨m', hm', hm'0, hm'uniq⟩ :=
    exists_ne_zero_unique_eq_constantGenericStalkModuleSection X L s' hs'
  obtain ⟨a, ha, hauniq⟩ := Stacks.Divisors.existsUnique_smul_eq
    (Stacks.Divisors.isTrivializedNear_of_isInvertible L (genericPoint X)) hm'0 (s := m)
  have ha0 : a ≠ 0 := fun h => hm0 (by rw [ha, h, zero_smul])
  have hinv0 : (Stacks.Chow.rationalFunctionsEquivFunctionField X).val.symm a ≠ 0 := by
    simpa using ha0
  refine ⟨Units.mk0 _ hinv0, ⟨hqc, ⟨m, m', hm, hm'⟩, fun n n' hn hn' => ?_⟩, fun g hg => ?_⟩
  · rw [← hmuniq n hn, ← hm'uniq n' hn']
    simpa using ha
  · obtain ⟨_, -, hrel⟩ := hg
    refine Units.ext ((Stacks.Chow.rationalFunctionsEquivFunctionField X).val.injective ?_)
    rw [hauniq _ (hrel m m' hm hm')]
    simp

/-- The ratio of two regular meromorphic sections of an invertible module, as an invertible
rational function. -/
def meromorphicSectionRatio (hs : IsRegularMeromorphicSection X.sheaf L s)
    (hs' : IsRegularMeromorphicSection X.sheaf L s') : (Stacks.Chow.rationalFunctions X)ˣ :=
  (existsUnique_meromorphicSectionRatio X L s s' hs hs').exists.choose

/-- `AlgebraicGeometry.meromorphicSectionRatio` satisfies the characterization of
`AlgebraicGeometry.IsMeromorphicSectionRatio`. -/
theorem isMeromorphicSectionRatio_meromorphicSectionRatio
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    (hs' : IsRegularMeromorphicSection X.sheaf L s') :
    IsMeromorphicSectionRatio X L s s' (meromorphicSectionRatio X L s s' hs hs') :=
  (existsUnique_meromorphicSectionRatio X L s s' hs hs').exists.choose_spec

/-- The order of vanishing of a regular meromorphic section `s` along a prime divisor is that of
`s'` plus the order of vanishing of the ratio of `s` and `s'`. -/
theorem orderOfVanishingMeromorphic_eq_add_ord [IsLocallyNoetherian X]
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    (hs' : IsRegularMeromorphicSection X.sheaf L s')
    {f : (Stacks.Chow.rationalFunctions X)ˣ} (hf : IsMeromorphicSectionRatio X L s s' f)
    (Z : PrimeDivisor X) :
    orderOfVanishingMeromorphic X L s hs Z =
      orderOfVanishingMeromorphic X L s' hs' Z +
        X.ord ((Stacks.Chow.rationalFunctionsEquivFunctionField X).val
          (f : Stacks.Chow.rationalFunctions X)) Z.genericPoint := by
  classical
  have hqc : L.IsQuasicoherent := isQuasicoherent_of_isInvertible L
  have hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := ‹_›
  obtain ⟨_, _, hrel⟩ := hf
  have hc_ne : (Stacks.Chow.rationalFunctionsEquivFunctionField X).val
      (f : Stacks.Chow.rationalFunctions X) ≠ 0 :=
    (f.isUnit.map (Stacks.Chow.rationalFunctionsEquivFunctionField X).val).ne_zero
  obtain ⟨m, hm, hm0, -⟩ :=
    exists_ne_zero_unique_eq_constantGenericStalkModuleSection X L s hs
  obtain ⟨m', hm', hm'0, -⟩ :=
    exists_ne_zero_unique_eq_constantGenericStalkModuleSection X L s' hs'
  have hmc := hrel m m' hm hm'
  obtain ⟨n, hn, a, hcoord⟩ := (orderOfVanishingMeromorphicData X L s hs Z).2.1
  have hmn : m = a • (L.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes trivial)) n :=
    (constantGenericStalkModuleSection_bijective X L ⊤ trivial).1 (hm.symm.trans hcoord)
  have hnη0 : (L.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)) n ≠ 0 :=
    fun h => hm0 (by rw [hmn, h, smul_zero])
  obtain ⟨b, hb, -⟩ := Stacks.Divisors.existsUnique_smul_eq
    (Stacks.Divisors.isTrivializedNear_of_isInvertible L (genericPoint X)) hnη0 (s := m')
  have hb_ne : b ≠ 0 := fun h => hm'0 (by rw [hb, h, zero_smul])
  have horder : orderOfVanishingMeromorphic X L s hs Z = X.ord a Z.genericPoint :=
    (orderOfVanishingMeromorphicData X L s hs Z).2.2 n hn a hcoord
  have horder' : orderOfVanishingMeromorphic X L s' hs' Z = X.ord b Z.genericPoint :=
    (orderOfVanishingMeromorphicData X L s' hs' Z).2.2 n hn b
      (hm'.trans (congrArg _ hb))
  have hab : a = (Stacks.Chow.rationalFunctionsEquivFunctionField X).val
      (f : Stacks.Chow.rationalFunctions X) * b :=
    (Stacks.Divisors.existsUnique_smul_eq
      (Stacks.Divisors.isTrivializedNear_of_isInvertible L (genericPoint X)) hnη0
      (s := a • (L.presheaf.stalkSpecializes
        ((genericPoint_spec X).specializes trivial)) n)).unique rfl
      (by rw [mul_smul, ← hb, ← hmc, ← hmn])
  rw [horder, horder', hab, Scheme.ord_mul hc_ne hb_ne]
  ring

/-- The Weil divisors of two regular meromorphic sections of an invertible
module on a locally Noetherian integral scheme differ by the principal divisor of their ratio. -/
@[stacks 02SH "divisor identity"]
theorem meromorphicWeilDivisor_eq_add_principalDivisor [IsLocallyNoetherian X]
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    (hs' : IsRegularMeromorphicSection X.sheaf L s') :
    weilDivisorOfMeromorphicSection X L s hs =
      weilDivisorOfMeromorphicSection X L s' hs' +
        principalDivisor X (meromorphicSectionRatio X L s s' hs hs') := by
  refine Subtype.ext (funext fun Z => ?_)
  simp only [weilDivisorOfMeromorphicSection_apply, AddSubgroup.coe_add, Pi.add_apply,
    principalDivisor_apply]
  exact orderOfVanishingMeromorphic_eq_add_ord X L s s' hs hs'
    (isMeromorphicSectionRatio_meromorphicSectionRatio X L s s' hs hs') Z

end AlgebraicGeometry

end
