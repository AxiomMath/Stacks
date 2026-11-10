module

public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassInjective
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.RestrictMeromorphic

/-!
# The divisor class of an invertible module on an open with codimension two complement

Let `X` be an integral locally Noetherian scheme and `U ⊆ X` an open subscheme whose complement
has codimension at least two at every point.  Restriction is an isomorphism `Cl(X) ≅ Cl(U)`, so
the Weil divisor class of an invertible `𝒪_U`-module is a class in `Cl(X)`.  Shrinking `U` does
not change that class: a regular meromorphic section restricts to one with the same orders of
vanishing.

## Main definitions

* `AlgebraicGeometry.weilClassOfCodimTwoInvertible` — the class in `Cl(X)`.

## Main results

* `AlgebraicGeometry.weilClassOfCodimTwoInvertible_congr` — it only depends on the isomorphism
  class of the module.
* `AlgebraicGeometry.weilClassOfCodimTwoInvertible_eq_iff` — on a normal scheme it determines the
  isomorphism class.
* `AlgebraicGeometry.weilClassOfCodimTwoInvertible_restrict` — it is unchanged by shrinking the
  open subscheme.

## References

* [Stacks Project, Tag 0EBM](https://stacks.math.columbia.edu/tag/0EBM)
* [Stacks Project, Tag 0BE8](https://stacks.math.columbia.edu/tag/0BE8)
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] schemePicardGroupAddCommGroup

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
  (hU : ∀ x : X, x ∉ U → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))

include hU

/-- **The class in `Cl(X)` of an invertible module on an open subscheme whose complement has
codimension at least two**: its Weil divisor class in `Cl(U)`, read through the isomorphism
`Cl(X) ≅ Cl(U)`. -/
def weilClassOfCodimTwoInvertible (L : U.toScheme.Modules)
    (hL : SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property L) :
    weilDivisorClassGroup X :=
  haveI : IsIntegral U.toScheme := isIntegral_of_two_le_codimension_compl U hU
  haveI : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  haveI : IsDominant U.ι := isDominant_opensι (U := U)
  haveI := hL
  (weilDivisorClassRestrictEquiv U hU).symm (weilDivisorClassOfInvertibleSheaf U.toScheme L)

/-- The class of an invertible module depends only on its isomorphism class. -/
theorem weilClassOfCodimTwoInvertible_congr {L M : U.toScheme.Modules} (hL) (hM) (e : L ≅ M) :
    weilClassOfCodimTwoInvertible U hU L hL = weilClassOfCodimTwoInvertible U hU M hM := by
  have : IsIntegral U.toScheme := isIntegral_of_two_le_codimension_compl U hU
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have : IsDominant U.ι := isDominant_opensι (U := U)
  have := hL
  have := hM
  exact congrArg _ (weilDivisorClassOfInvertibleSheaf_congr L M e)

/-- **On a normal scheme the class determines the invertible module up to isomorphism**: the
first Chern class of `U` is injective by [Stacks, Tag 0BE8]. -/
theorem weilClassOfCodimTwoInvertible_eq_iff [IsNormal X] (L M : U.toScheme.Modules) (hL) (hM) :
    weilClassOfCodimTwoInvertible U hU L hL = weilClassOfCodimTwoInvertible U hU M hM ↔
      Nonempty (L ≅ M) := by
  have : IsIntegral U.toScheme := isIntegral_of_two_le_codimension_compl U hU
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have : IsDominant U.ι := isDominant_opensι (U := U)
  have : IsNormal U.toScheme := isNormal_of_isOpenImmersion U.ι
  have := hL
  have := hM
  refine ⟨fun h => ?_, fun ⟨e⟩ => weilClassOfCodimTwoInvertible_congr U hU hL hM e⟩
  have hc : weilDivisorClassOfInvertibleSheaf U.toScheme L =
      weilDivisorClassOfInvertibleSheaf U.toScheme M :=
    (weilDivisorClassRestrictEquiv U hU).symm.injective h
  have hL' : Stacks.SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hL
  have hM' : Stacks.SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hM
  refine (Stacks.SheafOfModules.picardClass_eq_iff U.toScheme.sheaf.obj
    U.toScheme.ringCatSheaf.property _ _ hL' hM').mp
    (picardToWeilDivisorClassGroup_injective U.toScheme ?_)
  change weilDivisorClassOfPicardClass U.toScheme _ = weilDivisorClassOfPicardClass U.toScheme _
  rw [weilDivisorClassOfPicardClass_picardClass U.toScheme L,
    weilDivisorClassOfPicardClass_picardClass U.toScheme M]
  exact hc

omit hU in
/-- An open immersion between integral schemes is dominant: its image is a nonempty open subset
of an irreducible space, hence dense. -/
theorem isDominant_of_isOpenImmersion_of_isIntegral {Y Z : Scheme.{u}} (j : Y ⟶ Z)
    [IsOpenImmersion j] [IsIntegral Y] [IsIntegral Z] : IsDominant j :=
  ⟨(j.isOpenEmbedding.isOpen_range).dense (Set.range_nonempty _)⟩

omit [IsIntegral X] in
/-- The value of the inverse of the restriction isomorphism `Div(X) ≅ Div(U)`. -/
theorem weilDivisorRestrictEquiv_symm_apply_val (E : WeilDivisor U.toScheme) (Z : PrimeDivisor X) :
    ((weilDivisorRestrictEquiv U hU).symm E).val Z = E.val (primeDivisorRestrictEquiv U hU Z) := by
  have h := weilDivisorRestrictEquiv_apply_val U hU ((weilDivisorRestrictEquiv U hU).symm E)
    (primeDivisorRestrictEquiv U hU Z)
  rw [AddEquiv.apply_symm_apply, Equiv.symm_apply_apply] at h
  exact h.symm

/-- The inverse restriction isomorphism sends the class of an invertible module to the class of
the Weil divisor of any regular meromorphic section. -/
private theorem symm_weilDivisorClassOfInvertibleSheaf [IsIntegral U.toScheme]
    [IsLocallyNoetherian U.toScheme] [IsDominant U.ι] (L : U.toScheme.Modules)
    [SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property L]
    (s : MeromorphicSection U.toScheme.sheaf L)
    (hs : IsRegularMeromorphicSection U.toScheme.sheaf L s) :
    (weilDivisorClassRestrictEquiv U hU).symm (weilDivisorClassOfInvertibleSheaf U.toScheme L) =
      (((weilDivisorRestrictEquiv U hU).symm (weilDivisorOfMeromorphicSection U.toScheme L s hs) :
        WeilDivisor X) : weilDivisorClassGroup X) := by
  rw [weilDivisorClassOfInvertibleSheaf_eq U.toScheme L s hs, AddEquiv.symm_apply_eq,
    weilDivisorClassRestrictEquiv_mk, AddEquiv.apply_symm_apply]

/-- **Shrinking the open subscheme does not change the class.**  A regular meromorphic section
restricts to a regular meromorphic section of the restriction with the same orders of vanishing,
and the two restriction isomorphisms of `Div` agree on the prime divisors of `X`. -/
theorem weilClassOfCodimTwoInvertible_restrict {V : X.Opens}
    (hV : ∀ x : X, x ∉ V → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (hUV : U ≤ V) (L : V.toScheme.Modules) (hL) (hLU) :
    weilClassOfCodimTwoInvertible U hU (L.restrict (X.homOfLE hUV)) hLU =
      weilClassOfCodimTwoInvertible V hV L hL := by
  have : IsIntegral U.toScheme := isIntegral_of_two_le_codimension_compl U hU
  have : IsIntegral V.toScheme := isIntegral_of_two_le_codimension_compl V hV
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
  have : IsDominant U.ι := isDominant_opensι (U := U)
  have : IsDominant V.ι := isDominant_opensι (U := V)
  have := hL
  set ρ : U.toScheme ⟶ V.toScheme := X.homOfLE hUV with hρ
  have : IsDominant ρ := isDominant_of_isOpenImmersion_of_isIntegral ρ
  have hLU : SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property
      (L.restrict ρ) := Stacks.UFDExtensionGlobal.isInvertible_restrict ρ L hL
  have hρι : ρ ≫ V.ι = U.ι := by simp [hρ]
  obtain ⟨s, hs⟩ := exists_isRegularMeromorphicSection_of_isIntegral V.toScheme L
  have key : weilDivisorRestrictEquiv U hU ((weilDivisorRestrictEquiv V hV).symm
        (weilDivisorOfMeromorphicSection V.toScheme L s hs)) =
      weilDivisorOfMeromorphicSection U.toScheme (L.restrict ρ)
        (restrictMeromorphicSection ρ L s)
        (isRegularMeromorphicSection_restrictMeromorphicSection ρ L s hs) := by
    apply Subtype.ext
    funext W
    rw [weilDivisorRestrictEquiv_apply_val, weilDivisorRestrictEquiv_symm_apply_val,
      weilDivisorOfMeromorphicSection_apply, weilDivisorOfMeromorphicSection_apply]
    refine (orderOfVanishingMeromorphic_restrict ρ L s hs _ W ?_).symm
    apply V.ι.isOpenEmbedding.injective
    rw [base_genericPoint_primeDivisorRestrictEquiv V hV,
      genericPoint_primeDivisorRestrictEquiv_symm U hU]
    change U.ι.base W.genericPoint = (ρ ≫ V.ι).base W.genericPoint
    rw [hρι]
  change (weilDivisorClassRestrictEquiv U hU).symm
      (weilDivisorClassOfInvertibleSheaf U.toScheme (L.restrict ρ)) =
    (weilDivisorClassRestrictEquiv V hV).symm (weilDivisorClassOfInvertibleSheaf V.toScheme L)
  rw [symm_weilDivisorClassOfInvertibleSheaf U hU (L.restrict ρ) (restrictMeromorphicSection ρ L s)
    (isRegularMeromorphicSection_restrictMeromorphicSection ρ L s hs),
    symm_weilDivisorClassOfInvertibleSheaf V hV L s hs, ← key, AddEquiv.symm_apply_apply]

end AlgebraicGeometry

end
