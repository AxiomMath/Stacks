module

public import StacksFrontier.AlgebraicGeometry.Blowup.DenominatorExceptional
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomRegularSection
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower

/-!
# The divisor `D` of Tag 0ESL and the isomorphism `b^* L = 𝒪_{X'}(D - E)`

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `s` a regular meromorphic section of
`L`, let `b : X' ⟶ X` be the blowup of `X` in the ideal of denominators of `s` and let `E ⊆ X'`
be the exceptional divisor.  `StacksFrontier/AlgebraicGeometry/Blowup/DenominatorExceptional.lean`
constructs the morphism `ℐ_E ⟶ b^* L` — multiplication by `b^* s` — proves it monic, identifies
`Hom(ℐ_E, b^* L)` with `b^* L ⊗ 𝒪_{X'}(E)` and so reads it as a global section `t` of
`b^* L ⊗ 𝒪_{X'}(E)`.

This file turns that into the **second assertion of [Stacks, Tag 0ESL]**: `t` is a *regular*
section, so its zero scheme `D` is an effective Cartier divisor ([Stacks, Tag 02OR] (4)), there
is a unique isomorphism `𝒪_{X'}(D) ≅ b^* L ⊗ 𝒪_{X'}(E)` carrying `1_D` to `t`
([Stacks, Tag 01X0]), and untwisting it by `E` gives `b^* L ≅ 𝒪_{X'}(D - E)` with `b^* s`
corresponding to `1_D ⊗ (1_E)^{-1}`.

## Main definitions

* `Stacks.DenominatorBlowup.exceptionalTensorSections`: the global section `t` of
  `b^* L ⊗ 𝒪_{X'}(E)`, as a compatible family of local sections — the shape in which the
  regular-section API of [Stacks, Tag 01WY] takes a global section.
* `Stacks.DenominatorBlowup.denominatorDivisor`: **the divisor `D`**, the zero scheme of `t`.
* `Stacks.DenominatorBlowup.untwistExceptional`: untwisting by `E`, which turns an isomorphism
  `𝒪_{X'}(D) ≅ b^* L ⊗ 𝒪_{X'}(E)` into one `b^* L ≅ 𝒪_{X'}(D - E)`.

## Main results

* `Stacks.DenominatorBlowup.isRegularSection_exceptionalTensorSections`: **`t` is a regular
  section** of `b^* L ⊗ 𝒪_{X'}(E)`.
* `Stacks.DenominatorBlowup.isEffectiveCartierDivisor_denominatorDivisor`: **`D` is an effective
  Cartier divisor.**
* `Stacks.DenominatorBlowup.exists_isEffectiveCartierDivisor_pullL_iso_differenceTwist`: **the
  second assertion of [Stacks, Tag 0ESL]**, with the section-matching clause.
* `Stacks.DenominatorBlowup.isSectionOver_and_isAdmissibleBlowup_and_exists_differenceTwist`:
  **the whole of [Stacks, Tag 0ESL]** — maximality of `U`, `U`-admissibility of the blowup and
  the divisor `D` with its isomorphism and section-matching clause, under the source's own
  hypotheses, assembled from the three clause theorems.

## Implementation notes

**Regularity of `t` is the crossing that the file exists for.**  What `DenominatorExceptional`
proves is that the morphism `ℐ_E ⟶ b^* L` is a monomorphism; what the zero-scheme criterion
needs is that multiplication by `t` is a monomorphism `𝒪_{X'} ⟶ b^* L ⊗ 𝒪_{X'}(E)`.  Those are
cancellation properties of two different morphisms, and the tensor–hom adjunction of
[Stacks, Tag 03EO] identifies the hom-sets they live in without transporting monicity.  The
transport is `Stacks.SheafOfModules.mono_unitHomEquiv_symm_homSections`, proved on an arbitrary
ringed site in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafHomRegularSection.lean`: a
monomorphism out of a locally rank-one module is a regular global section of the sheaf-hom.  It
applies here because `ℐ_E` is invertible, `E` being an effective Cartier divisor, and because
the rank-one dual bases it asks for are the very ones that
`Stacks.DenominatorBlowup.exists_coversTop_dualBasisOne_exceptionalSheaf` already produces for
the identification `Hom(ℐ_E, b^* L) ≅ b^* L ⊗ 𝒪_{X'}(E)`.  Carrying it across that
identification is then `SheafOfModules.unitHomEquiv_symm_comp` and `mono_of_mono_fac`.

**Two shapes of a global section.**  `DenominatorExceptional` produces `t` as an element of
`Γ(b^* L ⊗ 𝒪_{X'}(E), ⊤)`, whereas `AlgebraicGeometry.IsRegularSection` and Tags 02OR and 01X0
are stated for a `PresheafOfModules.sections`, i.e. a compatible family over every open.
`Stacks.DenominatorBlowup.exceptionalTensorSections` is that family, and it is built not by
restricting the section over `⊤` but by transporting the family
`Stacks.SheafOfModules.homSections` of restrictions of the morphism `ℐ_E ⟶ b^* L` along the
identification — so its value over `⊤` is `exceptionalTensorSection` by `rfl`, and no
compatibility has to be re-checked.

**The section-matching clause.**  The literal clause `b^* s = 1_D ⊗ (1_E)^{-1}` cannot be formed
in this development; see the implementation notes of `DenominatorExceptional` for why.  What the
registered theorem carries is the multiplied-out form, as a conjunction of the three identities
that pin down `D`, the isomorphism and `b^* s` together: `e` carries `1_D` to `t`, `t` *is* the
morphism `ℐ_E ⟶ b^* L`, and that morphism *is* multiplication by `b^* s`
(`Stacks.DenominatorBlowup.exceptionalToPullL_comp_toK`).  This is the source's own
reinterpretation of its final assertion — that `b^* s` is a global regular section of
`b^* L(E)` whose zero scheme is `D`.

**Untwisting is a four-step chain** of the structural isomorphisms of the tensor product sheaf:
the right unitor, the evaluation pairing `𝒪_{X'}(E) ⊗ ℐ_E ≅ 𝒪_{X'}` of [Stacks, Tag 01WX], the
associativity constraint, and `e` itself.  `𝒪_{X'}(E)` and `ℐ_E` are, on the nose, the
`Stacks.Divisors.invertibleSheaf'` and `negativeTwist'` of the exceptional divisor, so no
re-spelling intervenes.

## References

* [Stacks Project, Tag 0ESL](https://stacks.math.columbia.edu/tag/0ESL)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.DenominatorBlowup

section Blowup

variable {X : Scheme.{u}} (L : SheafOfModules.{u} (Stacks.DenominatorIdeal.O X))
  (s : MeromorphicSection.{u, u} X.sheaf L)
  (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
    (Stacks.DenominatorIdeal.O X).property L)

/-- `b^* L ⊗ 𝒪_{X'}(E)`, the invertible sheaf of which `b^* s` is a regular global section. -/
abbrev pullLTensorExceptionalTwist : SheafOfModules.{u} (Stacks.DenominatorIdeal.O (blow L s)) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(blow L s).presheaf, Presheaf.isSheaf_of_isSheaf_comp _ ((blow L s).presheaf)
        (forget₂ CommRingCat RingCat)
        ((structureSheafRing (blow L s).toRingedSpace).property)⟩).obj
      ((pullL L s))).obj ((exceptionalTwist L s)))

/-- The morphism `ℐ_E ⟶ b^* L`, read as a global section of `Hom(ℐ_E, b^* L)` in the
`PresheafOfModules.sections` sense: the compatible family of its restrictions. -/
noncomputable def exceptionalHomSections :
    (Stacks.SheafOfModules.sheafHom (blow L s).presheaf
      (structureSheafRing (blow L s).toRingedSpace).property
      (exceptionalSheaf L s) (pullL L s)).sections :=
  Stacks.SheafOfModules.homSections (blow L s).presheaf
    (structureSheafRing (blow L s).toRingedSpace).property (exceptionalToPullL L s hL)

/-- **The global section `t` of `b^* L ⊗ 𝒪_{X'}(E)`, as a compatible family of sections.**  Its
value over `⊤` is `Stacks.DenominatorBlowup.exceptionalTensorSection`. -/
noncomputable def exceptionalTensorSections : (pullLTensorExceptionalTwist L s).sections :=
  SheafOfModules.sectionsMap (pullLTensorExceptionalTwistIso L s).inv
    (exceptionalHomSections L s hL)

/-- The compatible family `exceptionalTensorSections` really is the section `t`: its value over
`⊤` is `Stacks.DenominatorBlowup.exceptionalTensorSection`. -/
theorem exceptionalTensorSections_eval_top :
    (exceptionalTensorSections L s hL).eval (op ⊤) = exceptionalTensorSection L s hL := rfl

include hL in
/-- **The section `t` is a regular section of `b^* L ⊗ 𝒪_{X'}(E)`.** -/
theorem isRegularSection_exceptionalTensorSections
    (hs : IsRegularMeromorphicSection X.sheaf L s) :
    AlgebraicGeometry.IsRegularSection (blow L s).presheaf
      (structureSheafRing (blow L s).toRingedSpace).property
      (exceptionalTensorSections L s hL) := by
  obtain ⟨ι, V, hV, ⟨b⟩⟩ := exists_coversTop_dualBasisOne_exceptionalSheaf L s
  have hmono : Mono ((Stacks.SheafOfModules.sheafHom (blow L s).presheaf
      (structureSheafRing (blow L s).toRingedSpace).property
      (exceptionalSheaf L s) (pullL L s)).unitHomEquiv.symm
        (exceptionalHomSections L s hL)) :=
    Stacks.SheafOfModules.mono_unitHomEquiv_symm_homSections (blow L s).presheaf
      (structureSheafRing (blow L s).toRingedSpace).property hV b (exceptionalToPullL L s hL)
      (mono_exceptionalToPullL L s hL hs)
  have hsec : SheafOfModules.sectionsMap (pullLTensorExceptionalTwistIso L s).hom
        (exceptionalTensorSections L s hL) = exceptionalHomSections L s hL :=
    (SheafOfModules.sectionsMap_comp (pullLTensorExceptionalTwistIso L s).inv
        (pullLTensorExceptionalTwistIso L s).hom (exceptionalHomSections L s hL)).symm.trans
      ((congrArg (fun ψ => SheafOfModules.sectionsMap ψ (exceptionalHomSections L s hL))
          (pullLTensorExceptionalTwistIso L s).inv_hom_id).trans
        (SheafOfModules.sectionsMap_id (exceptionalHomSections L s hL)))
  have hcomp : (pullLTensorExceptionalTwist L s).unitHomEquiv.symm
        (exceptionalTensorSections L s hL) ≫ (pullLTensorExceptionalTwistIso L s).hom =
      (Stacks.SheafOfModules.sheafHom (blow L s).presheaf
        (structureSheafRing (blow L s).toRingedSpace).property
        (exceptionalSheaf L s) (pullL L s)).unitHomEquiv.symm
          (exceptionalHomSections L s hL) :=
    (SheafOfModules.unitHomEquiv_symm_comp (exceptionalTensorSections L s hL)
        (pullLTensorExceptionalTwistIso L s).hom).trans
      (congrArg (fun m => (Stacks.SheafOfModules.sheafHom (blow L s).presheaf
        (structureSheafRing (blow L s).toRingedSpace).property
        (exceptionalSheaf L s) (pullL L s)).unitHomEquiv.symm m) hsec)
  exact mono_of_mono_fac hcomp

/-! ### The divisor `D` and the isomorphism `b^* L ≅ 𝒪_{X'}(D - E)` -/

include hL in
/-- `b^* L ⊗ 𝒪_{X'}(E)` is invertible in the spelling the zero-scheme construction of
[Stacks, Tag 02OQ] takes its hypothesis in. -/
theorem isInvertible_pullLTensorExceptionalTwist :
    AlgebraicGeometry.SheafOfModules.IsInvertible (blow L s).presheaf
      (structureSheafRing (blow L s).toRingedSpace).property
      (pullLTensorExceptionalTwist L s) :=
  have _ : Stacks.SheafOfModules.IsInvertible (blow L s).presheaf
      (structureSheafRing (blow L s).toRingedSpace).property
      (pullLTensorExceptionalTwist L s) :=
    stacksIsInvertible_pullLTensorExceptionalTwist L s hL
  Stacks.InvertibleBridge.algebraicGeometryIsInvertible_of_stacksIsInvertible

/-- **The divisor `D` of the second assertion of [Stacks, Tag 0ESL]**: the zero scheme of the
global section `t` of `b^* L ⊗ 𝒪_{X'}(E)` attached to `b^* s`. -/
noncomputable def denominatorDivisor : (blow L s).IdealSheafData :=
  @AlgebraicGeometry.zeroScheme (blow L s) (pullLTensorExceptionalTwist L s)
    (isInvertible_pullLTensorExceptionalTwist L s hL) (exceptionalTensorSection L s hL)

include hL in
/-- **`D` is an effective Cartier divisor**, by [Stacks, Tag 02OR] (4): `t` is a regular
section. -/
theorem isEffectiveCartierDivisor_denominatorDivisor
    (hs : IsRegularMeromorphicSection X.sheaf L s) :
    Stacks.Divisors.IsEffectiveCartierDivisor (denominatorDivisor L s hL) :=
  (@AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection (blow L s)
      (pullLTensorExceptionalTwist L s) (isInvertible_pullLTensorExceptionalTwist L s hL)
      (exceptionalTensorSections L s hL)).mpr
    (isRegularSection_exceptionalTensorSections L s hL hs)

/-- **Untwisting by the exceptional divisor.**  An isomorphism `𝒪_{X'}(D) ≅ b^* L ⊗ 𝒪_{X'}(E)`
becomes an isomorphism `b^* L ≅ 𝒪_{X'}(D - E)`: tensor it with `ℐ_E` and cancel the factor
`𝒪_{X'}(E) ⊗ ℐ_E ≅ 𝒪_{X'}`, which is the evaluation pairing of [Stacks, Tag 01WX] for the
effective Cartier divisor `E`. -/
noncomputable def untwistExceptional {D : (blow L s).IdealSheafData}
    (e : Stacks.Divisors.invertibleSheaf' D ≅ pullLTensorExceptionalTwist L s) :
    pullL L s ≅ Stacks.Divisors.differenceTwist D (exceptional L s) :=
  have _ : Stacks.Divisors.IsEffectiveCartierDivisor (exceptional L s) :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (centre L s)
  (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor (blow L s).presheaf
      (structureSheafRing (blow L s).toRingedSpace).property (pullL L s)).symm ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductIso (blow L s).presheaf
        (structureSheafRing (blow L s).toRingedSpace).property (Iso.refl (pullL L s))
        (Stacks.Divisors.invertibleSheafPairing (exceptional L s)).symm ≪≫
      (Stacks.SheafOfModules.tensorSheafAssociator (blow L s).presheaf
          (structureSheafRing (blow L s).toRingedSpace).property (pullL L s)
          (exceptionalTwist L s) (exceptionalSheaf L s)).symm ≪≫
        Stacks.SheafOfModules.Invertible.tensorProductIso (blow L s).presheaf
          (structureSheafRing (blow L s).toRingedSpace).property e.symm
          (Iso.refl (exceptionalSheaf L s))

include hL in
/-- **Stacks Project, Tag 0ESL, second assertion.**  Let `X` be a scheme, `L` an invertible
`𝒪_X`-module and `s` a regular meromorphic section of `L`, let `b : X' ⟶ X` be the blowup of `X`
in the ideal of denominators of `s` and let `E ⊆ X'` be the exceptional divisor.  Then there is
an effective Cartier divisor `D ⊆ X'` and an isomorphism

`b^* L ≅ 𝒪_{X'}(D - E)`

through which the meromorphic section `b^* s` corresponds to `1_D ⊗ (1_E)^{-1}`.

The last clause is stated in the multiplied-out form of the implementation notes of
`StacksFrontier/AlgebraicGeometry/Blowup/DenominatorExceptional.lean`, as the conjunction of its
three constituents: the isomorphism `b^* L ≅ 𝒪_{X'}(D - E)` is the untwisting of an isomorphism
`e : 𝒪_{X'}(D) ≅ b^* L ⊗ 𝒪_{X'}(E)`; `e` carries the canonical section `1_D` to the global
section `t` of `b^* L ⊗ 𝒪_{X'}(E)`; `t` is the morphism `ℐ_E ⟶ b^* L` under the identification
`b^* L ⊗ 𝒪_{X'}(E) ≅ Hom(ℐ_E, b^* L)`; and that morphism, composed into the sheaf of
meromorphic sections, is the ideal inclusion `ℐ_E ⟶ 𝒪_{X'}` followed by multiplication by
`b^* s`.  Together these say `1_E · (1_D ⊗ (1_E)^{-1}) = 1_E · b^* s` with the invertible factor
`1_E` cleared, which is the identity the source's own proof establishes — namely that `b^* s` is
a global regular section of `b^* L(E)` whose zero scheme is `D`. -/
theorem exists_isEffectiveCartierDivisor_pullL_iso_differenceTwist
    (hs : IsRegularMeromorphicSection X.sheaf L s) :
    ∃ D : (blow L s).IdealSheafData, Stacks.Divisors.IsEffectiveCartierDivisor D ∧
      ∃ (i : pullL L s ≅ Stacks.Divisors.differenceTwist D (exceptional L s))
        (e : Stacks.Divisors.invertibleSheaf' D ≅ pullLTensorExceptionalTwist L s),
        i = untwistExceptional L s e ∧
        Scheme.Modules.Hom.app e.hom ⊤
            ((Stacks.Divisors.canonicalSection' D).eval (op ⊤)) =
          exceptionalTensorSection L s hL ∧
        ((pullLTensorExceptionalTwistIso L s).hom.val.app (op ⊤))
            (exceptionalTensorSection L s hL) = exceptionalHomSection L s hL ∧
        exceptionalToPullL L s hL ≫ DenominatorIdeal.toK (blow L s) (pullL L s) =
          exceptionalι L s ≫
            DenominatorIdeal.sectionMap (blow L s) (pullL L s) (pullS L s) := by
  refine ⟨denominatorDivisor L s hL, isEffectiveCartierDivisor_denominatorDivisor L s hL hs, ?_⟩
  obtain ⟨e, he, -⟩ := @AlgebraicGeometry.existsUnique_invertibleSheafIso_zeroScheme (blow L s)
    (pullLTensorExceptionalTwist L s) (isInvertible_pullLTensorExceptionalTwist L s hL)
    (exceptionalTensorSections L s hL) (isRegularSection_exceptionalTensorSections L s hL hs)
  exact ⟨untwistExceptional L s e, e, rfl, he,
    pullLTensorExceptionalTwistIso_hom_exceptionalTensorSection L s hL,
    exceptionalToPullL_comp_toK L s hL⟩

/-! ### The whole of Tag 0ESL -/

include hL in
/-- **Stacks Project, Tag 0ESL.**  Let `X` be a locally Noetherian scheme, `L` an invertible
`𝒪_X`-module and `s` a regular meromorphic section of `L`.  Let `U ⊆ X` be the maximal open
subscheme such that `s` corresponds to a section of `L` over `U`.  Then:

* `U` really is maximal — `s` corresponds to a section of `L` over `U`, and every open subscheme
  over which `s` corresponds to a section of `L` is contained in `U`;
* the blowup `b : X' ⟶ X` of `X` in the ideal of denominators of `s` is `U`-admissible;
* there is an effective Cartier divisor `D ⊆ X'` and an isomorphism `b^* L ≅ 𝒪_{X'}(D - E)`,
  where `E ⊆ X'` is the exceptional divisor, through which the meromorphic section `b^* s`
  corresponds to the meromorphic section `1_D ⊗ (1_E)^{-1}`.

The three clauses are
`Stacks.DenominatorBlowup.isSectionOver_sectionOpens` together with
`Stacks.DenominatorBlowup.le_sectionOpens`,
`Stacks.DenominatorBlowup.isAdmissibleBlowup_denominatorIdealData` carried from
`Stacks.Blowup.blowUp` to `AlgebraicGeometry.blowUp` along
`AlgebraicGeometry.blowUpIso` — the two constructions of the blowup are isomorphic over `X`, so
the morphism `b` of the admissibility clause is the morphism `b` of the divisor clause — and
`Stacks.DenominatorBlowup.exists_isEffectiveCartierDivisor_pullL_iso_differenceTwist`.

The last clause is stated as in that theorem, as the conjunction of the identities that pin down
`D`, the isomorphism and `b^* s` together; see its docstring and the implementation notes of
`StacksFrontier/AlgebraicGeometry/Blowup/DenominatorExceptional.lean`. -/
@[stacks 0ESL "the whole statement: U is maximal, the blowup in the ideal of denominators is \
U-admissible, and there is an effective Cartier divisor D with b^* L = O(D - E) carrying the \
last clause in the form the source's own proof gives it, that b^* s is the regular global \
section of b^* L(E) whose zero scheme is D"]
theorem isSectionOver_and_isAdmissibleBlowup_and_exists_differenceTwist
    [IsLocallyNoetherian X] (hs : IsRegularMeromorphicSection X.sheaf L s) :
    (IsSectionOver L s (sectionOpens L s) ∧
        ∀ V : Opens X, IsSectionOver L s V → V ≤ sectionOpens L s) ∧
      Stacks.Blowup.IsAdmissibleBlowup (sectionOpens L s) (blowHom L s) ∧
      ∃ D : (blow L s).IdealSheafData, Stacks.Divisors.IsEffectiveCartierDivisor D ∧
        ∃ (i : pullL L s ≅ Stacks.Divisors.differenceTwist D (exceptional L s))
          (e : Stacks.Divisors.invertibleSheaf' D ≅ pullLTensorExceptionalTwist L s),
          i = untwistExceptional L s e ∧
          Scheme.Modules.Hom.app e.hom ⊤
              ((Stacks.Divisors.canonicalSection' D).eval (op ⊤)) =
            exceptionalTensorSection L s hL ∧
          ((pullLTensorExceptionalTwistIso L s).hom.val.app (op ⊤))
              (exceptionalTensorSection L s hL) = exceptionalHomSection L s hL ∧
          exceptionalToPullL L s hL ≫ DenominatorIdeal.toK (blow L s) (pullL L s) =
            exceptionalι L s ≫
              DenominatorIdeal.sectionMap (blow L s) (pullL L s) (pullS L s) := by
  refine ⟨⟨isSectionOver_sectionOpens X L s hL, fun _V hV => le_sectionOpens L s hV⟩, ?_,
    exists_isEffectiveCartierDivisor_pullL_iso_differenceTwist L s hL hs⟩
  obtain ⟨I, hfp, hdisj, e, he⟩ := isAdmissibleBlowup_denominatorIdealData L s hL hs
  exact ⟨I, hfp, hdisj, AlgebraicGeometry.blowUpIso (centre L s) ≪≫ e, by
    rw [Iso.trans_hom, Category.assoc, he, AlgebraicGeometry.blowUpIso_hom_blowUpToBase]⟩

end Blowup

end Stacks.DenominatorBlowup

end
