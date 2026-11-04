module

public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkGenerators
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tensor product of two meromorphic sections

Let `X` be an integral scheme. By Tag 01X5 part (2) a meromorphic section of a quasi-coherent
`𝒪_X`-module `F` is one element of the stalk `F_η` at the generic point, so two meromorphic
sections `s` of `L` and `t` of `N` have a product: the meromorphic section of `L ⊗_{𝒪_X} N`
whose generic value is the pure tensor of the generic values of `s` and `t`. This file
constructs that product and proves the four assertions Tag 02SL makes about it.

When `L` and `N` are invertible and `X` is in addition locally Noetherian, the product of two
regular meromorphic sections is regular, and its Weil divisor is the sum of the two Weil
divisors: along a prime divisor `Z` with generic point `ξ`, if `m` generates `L_ξ` and `n`
generates `N_ξ` then `m ⊗ n` generates `(L ⊗ N)_ξ`, the coordinate of `s ⊗ t` against it is the
product of the coordinates of `s` and `t`, and the order of vanishing is multiplicative. Since a
regular meromorphic section exists, the Weil divisor class of Tag 0BE6 part (2) is additive in
the tensor product, which is the input Tag 0BE7 needs.

## Main definitions

* `AlgebraicGeometry.meromorphicGenericValue`: the element of the generic stalk representing a
  meromorphic section.
* `AlgebraicGeometry.tensorMeromorphicSection`: the product of two meromorphic sections.

## Main results

* `AlgebraicGeometry.meromorphicSectionSheafIsoConstant_tensorMeromorphicSection`: at the
  generic point the product is the pure tensor, which characterizes it.
* `AlgebraicGeometry.isRegularMeromorphicSection_tensorMeromorphicSection`: a product of
  regular meromorphic sections of invertible modules is regular.
* `AlgebraicGeometry.orderOfVanishingMeromorphic_tensorMeromorphicSection` and
  `AlgebraicGeometry.weilDivisorOfMeromorphicSection_tensorMeromorphicSection`: the order of
  vanishing of Tag 02SF, and the Weil divisor of Tag 0BE6 part (1), are additive.
* `AlgebraicGeometry.weilDivisorClassOfInvertibleSheaf_tensorObj`: the Weil divisor class of Tag
  0BE6 part (2) is additive. This is the hypothesis of Tag 0BE7.

## Implementation notes

**No junk branch.** The product is not defined by a case distinction on whether the ambient
scheme is integral, with an arbitrary value otherwise; integrality is a hypothesis of the
definition, so no consumer has to discharge a `dif_pos` before it can compute with the product.
Quasi-coherence of the two factors and of their tensor product is likewise a hypothesis of the
definition rather than of a surrounding case split;
`AlgebraicGeometry.isQuasicoherent_of_isInvertible` and
`Stacks.SheafOfModules.isInvertible_tensorSheaf` are registered as file-local instances, so the
four results about invertible modules need only assume invertibility.

**Which generic value.** The development has a second construction of the element of `F_η`
representing a meromorphic section, `Stacks.Divisors.genericValue`, characterized through
`Stacks.Divisors.toMeromorphicSectionStalk`. It is not used here and no bridge to it is
introduced. The one built here is characterized against
`AlgebraicGeometry.meromorphicSectionSheafIsoConstant` and
`AlgebraicGeometry.constantGenericStalkModuleSection`, which is what the order of vanishing of
Tag 02SF — `AlgebraicGeometry.orderOfVanishingMeromorphicData`, the declaration carrying that
tag — is read at, so the coordinate computation needs no translation.

**Which invertibility, and which tensor product.** `AlgebraicGeometry.SheafOfModules.IsInvertible`
throughout, since that is the spelling the Weil divisor class of Tag 0BE6 is stated for; the
tensor product is `AlgebraicGeometry.Scheme.Modules.tensorObj`, the one the Picard group of Tag
01CX is stated for. Crossing to `Stacks.SheafOfModules.IsInvertible`, needed once in order to
quote the invertibility of a tensor product, goes through the existing bridge
`Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry`; no new bridge is written.

## References

* [Stacks Project, Tag 02SL](https://stacks.math.columbia.edu/tag/02SL)
* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
* [Stacks Project, Tag 02OX](https://stacks.math.columbia.edu/tag/02OX)
* [Stacks Project, Tag 02OZ](https://stacks.math.columbia.edu/tag/02OZ)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 0BE6](https://stacks.math.columbia.edu/tag/0BE6)
* [Stacks Project, Tag 0BE7](https://stacks.math.columbia.edu/tag/0BE7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) [IsIntegral X]

/-- **The generic value of a meromorphic section.** On an integral scheme the comparison
isomorphism of Tag 01X5 part (2) identifies the sheaf of meromorphic sections of a
quasi-coherent module `F` with the constant sheaf on the stalk `F_η` at the generic point, so a
meromorphic section of `F` is the constant section of a unique element of `F_η`; this is that
element. Its characterization is
`AlgebraicGeometry.constantGenericStalkModuleSection_meromorphicGenericValue`. -/
def meromorphicGenericValue (F : X.Modules) [F.IsQuasicoherent]
    (s : MeromorphicSection X.sheaf F) : F.presheaf.stalk (genericPoint X) :=
  (exists_unique_eq_constantGenericStalkModuleSection X F
    ((meromorphicSectionSheafIsoConstant X F).val.hom.val.app (op (⊤ : X.Opens))
      (s.val (op ⊤)))).choose

/-- **The characterization of the generic value.** Under the comparison isomorphism of Tag 01X5
part (2), a meromorphic section is the constant section of its generic value. -/
theorem constantGenericStalkModuleSection_meromorphicGenericValue (F : X.Modules)
    [F.IsQuasicoherent] (s : MeromorphicSection X.sheaf F) :
    (meromorphicSectionSheafIsoConstant X F).val.hom.val.app (op (⊤ : X.Opens))
        (s.val (op ⊤)) =
      constantGenericStalkModuleSection X F ⊤ (meromorphicGenericValue X F s) :=
  (exists_unique_eq_constantGenericStalkModuleSection X F _).choose_spec.1

/-- The generic value is the only element of the generic stalk whose constant section is the
image of `s` under the comparison isomorphism of Tag 01X5 part (2). -/
theorem meromorphicGenericValue_eq (F : X.Modules) [F.IsQuasicoherent]
    (s : MeromorphicSection X.sheaf F) (v : F.presheaf.stalk (genericPoint X))
    (hv : (meromorphicSectionSheafIsoConstant X F).val.hom.val.app (op (⊤ : X.Opens))
      (s.val (op ⊤)) = constantGenericStalkModuleSection X F ⊤ v) :
    meromorphicGenericValue X F s = v :=
  (exists_unique_eq_constantGenericStalkModuleSection X F _).choose_spec.2 v hv

/-- The comparison isomorphism of Tag 01X5 part (2) carries the meromorphic section determined
by an element `v` of the generic stalk back to the constant section of `v`: the two are
exchanged by the isomorphism and its inverse. -/
theorem meromorphicSectionSheafIsoConstant_meromorphicSectionOfConstantGenericStalk (F : X.Modules)
    [F.IsQuasicoherent] (v : F.presheaf.stalk (genericPoint X)) :
    (meromorphicSectionSheafIsoConstant X F).val.hom.val.app (op (⊤ : X.Opens))
        ((meromorphicSectionOfConstantGenericStalk X F v).val (op ⊤)) =
      constantGenericStalkModuleSection X F ⊤ v := by
  have h : (meromorphicSectionOfConstantGenericStalk X F v).val (op (⊤ : X.Opens)) =
      (meromorphicSectionSheafIsoConstant X F).val.inv.val.app (op (⊤ : X.Opens))
        (constantGenericStalkModuleSection X F ⊤ v) := rfl
  have hid := (meromorphicSectionSheafIsoConstant X F).val.inv_hom_id
  rw [h]
  exact congrArg (fun g => g.val.app (op (⊤ : X.Opens))
    (constantGenericStalkModuleSection X F ⊤ v)) hid

/-- The generic value of the meromorphic section determined by an element `v` of the generic
stalk is `v`: the two constructions of Tag 01X5 part (2) are mutually inverse. -/
theorem meromorphicGenericValue_meromorphicSectionOfConstantGenericStalk (F : X.Modules)
    [F.IsQuasicoherent] (v : F.presheaf.stalk (genericPoint X)) :
    meromorphicGenericValue X F (meromorphicSectionOfConstantGenericStalk X F v) = v :=
  meromorphicGenericValue_eq X F _ v
    (meromorphicSectionSheafIsoConstant_meromorphicSectionOfConstantGenericStalk X F v)

/-! ### The tensor product of two meromorphic sections -/

/-- An invertible `𝒪_X`-module is quasi-coherent. A file-local instance, so that the
quasi-coherence the comparison isomorphism of Tag 01X5 part (2) needs is available from
invertibility alone. -/
local instance isQuasicoherentOfIsInvertible (F : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property F] : F.IsQuasicoherent :=
  isQuasicoherent_of_isInvertible F

/-- **Stacks 01CT (1).** The tensor product of two invertible `𝒪_X`-modules is invertible. A
file-local instance; the mathematics is
`Stacks.SheafOfModules.isInvertible_tensorSheaf`, read through the comparison of the two
spellings of invertibility. -/
local instance isInvertibleTensorObj (L N : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.Modules.tensorObj L N) := by
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  exact (Stacks.SheafOfModules.isInvertible_tensorSheaf X.sheaf.obj X.ringCatSheaf.property
    L N).toAlgebraicGeometry

variable (L N : X.Modules)

/-- **Stacks 02SL: the tensor product of two meromorphic sections.** The meromorphic section of
`L ⊗_{𝒪_X} N` whose generic value is the pure tensor of the generic values of `s` and `t`. On an
integral scheme this determines it, by Tag 01X5 part (2);
`AlgebraicGeometry.meromorphicSectionSheafIsoConstant_tensorMeromorphicSection` is the resulting
description on pure tensors of honest sections. -/
@[stacks 02SL "tensor product of meromorphic sections"]
def tensorMeromorphicSection [L.IsQuasicoherent] [N.IsQuasicoherent]
    [(Scheme.Modules.tensorObj L N).IsQuasicoherent]
    (s : MeromorphicSection X.sheaf L) (t : MeromorphicSection X.sheaf N) :
    MeromorphicSection X.sheaf (Scheme.Modules.tensorObj L N) :=
  meromorphicSectionOfConstantGenericStalk X (Scheme.Modules.tensorObj L N)
    (tensorStalkTmul L N (genericPoint X) (meromorphicGenericValue X L s)
      (meromorphicGenericValue X N t))

/-- The generic value of a product of meromorphic sections is the product of the generic
values. -/
theorem meromorphicGenericValue_tensorMeromorphicSection [L.IsQuasicoherent]
    [N.IsQuasicoherent] [(Scheme.Modules.tensorObj L N).IsQuasicoherent]
    (s : MeromorphicSection X.sheaf L) (t : MeromorphicSection X.sheaf N) :
    meromorphicGenericValue X (Scheme.Modules.tensorObj L N)
        (tensorMeromorphicSection X L N s t) =
      tensorStalkTmul L N (genericPoint X) (meromorphicGenericValue X L s)
        (meromorphicGenericValue X N t) :=
  meromorphicGenericValue_meromorphicSectionOfConstantGenericStalk X _ _

/-- The comparison isomorphism sends a product of meromorphic sections with generic values `v`
and `w` to the constant section of `v ⊗ w`. -/
private theorem iso_tensorMeromorphicSection_eq [L.IsQuasicoherent] [N.IsQuasicoherent]
    [(Scheme.Modules.tensorObj L N).IsQuasicoherent]
    (s : MeromorphicSection X.sheaf L) (t : MeromorphicSection X.sheaf N)
    {v : L.presheaf.stalk (genericPoint X)} {w : N.presheaf.stalk (genericPoint X)}
    (hv : meromorphicGenericValue X L s = v) (hw : meromorphicGenericValue X N t = w) :
    (meromorphicSectionSheafIsoConstant X (Scheme.Modules.tensorObj L N)).val.hom.val.app
        (op (⊤ : X.Opens)) ((tensorMeromorphicSection X L N s t).val (op ⊤)) =
      constantGenericStalkModuleSection X (Scheme.Modules.tensorObj L N) ⊤
        (tensorStalkTmul L N (genericPoint X) v w) :=
  (constantGenericStalkModuleSection_meromorphicGenericValue X
    (Scheme.Modules.tensorObj L N) (tensorMeromorphicSection X L N s t)).trans
      (congrArg _ ((meromorphicGenericValue_tensorMeromorphicSection X L N s t).trans
        (congrArg₂ _ hv hw)))

/-- **Stacks 02SL: at the generic point the product is the pure tensor.** If the meromorphic
sections `s` and `t` are, at the generic point, the germs of honest sections `m` of `L` and `n`
of `N` over a neighbourhood `U` of it, then their product is the germ of the pure tensor
`m ⊗ n`. This fixes the product and not merely its divisor: a meromorphic section on an integral
scheme is determined by its generic germ. -/
@[stacks 02SL "pure-tensor characterization"]
theorem meromorphicSectionSheafIsoConstant_tensorMeromorphicSection
    [L.IsQuasicoherent] [N.IsQuasicoherent] [(Scheme.Modules.tensorObj L N).IsQuasicoherent]
    (s : MeromorphicSection X.sheaf L) (t : MeromorphicSection X.sheaf N)
    (U : X.Opens) (hU : genericPoint X ∈ U)
    (m : L.val.obj (op U)) (n : N.val.obj (op U))
    (hs : (meromorphicSectionSheafIsoConstant X L).val.hom.val.app (op (⊤ : X.Opens))
      (s.val (op ⊤)) =
        constantGenericStalkModuleSection X L ⊤ (L.presheaf.germ U (genericPoint X) hU m))
    (ht : (meromorphicSectionSheafIsoConstant X N).val.hom.val.app (op (⊤ : X.Opens))
      (t.val (op ⊤)) =
        constantGenericStalkModuleSection X N ⊤ (N.presheaf.germ U (genericPoint X) hU n)) :
    (meromorphicSectionSheafIsoConstant X (Scheme.Modules.tensorObj L N)).val.hom.val.app
        (op (⊤ : X.Opens)) ((tensorMeromorphicSection X L N s t).val (op ⊤)) =
      constantGenericStalkModuleSection X (Scheme.Modules.tensorObj L N) ⊤
        (PresheafOfModules.tensorSheafGerm X.sheaf L N (genericPoint X) U hU m n) := by
  refine (iso_tensorMeromorphicSection_eq X L N s t (meromorphicGenericValue_eq X L s _ hs)
    (meromorphicGenericValue_eq X N t _ ht)).trans (congrArg _ ?_)
  exact tensorStalkTmul_germ L N (genericPoint X) U hU m n

/-- The generic value of a regular meromorphic section, in the sense of Tag 02OX, is
nonzero. -/
theorem meromorphicGenericValue_ne_zero [L.IsQuasicoherent] (s : MeromorphicSection X.sheaf L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) : meromorphicGenericValue X L s ≠ 0 :=
  ne_zero_of_isRegularMeromorphicSection L s hs
    (constantGenericStalkModuleSection_meromorphicGenericValue X L s)

/-- If the generic value of a regular meromorphic section is `a • e`, then `a ≠ 0`. -/
private theorem ne_zero_of_meromorphicGenericValue_eq_smul [L.IsQuasicoherent]
    (s : MeromorphicSection X.sheaf L) (hs : IsRegularMeromorphicSection X.sheaf L s)
    {a : X.presheaf.stalk (genericPoint X)} {e : L.presheaf.stalk (genericPoint X)}
    (h : meromorphicGenericValue X L s = a • e) : a ≠ 0 := fun h0 =>
  meromorphicGenericValue_ne_zero X L s hs (by rw [h, h0, zero_smul])

/-- An invertible `𝒪_X`-module on an integral scheme has a stalk basis at the generic point: it
is trivialized near every point, and the germ of a trivializing section is such a basis. -/
theorem exists_isStalkBasis_genericPoint
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    ∃ e : L.presheaf.stalk (genericPoint X),
      Stacks.Divisors.IsStalkBasis L (genericPoint X) e := by
  have hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := ‹_›
  obtain ⟨W, hW, e, hb⟩ := Stacks.Divisors.isTrivializedNear_of_isInvertible L (genericPoint X)
  exact ⟨L.presheaf.germ W (genericPoint X) hW e, hb _ hW⟩

/-- **Stacks 02SL: a product of nonzero meromorphic sections is nonzero.** Regularity in the
sense of Tag 02OX is injectivity of multiplication by the generic value. Writing the generic
values of `s` and `t` as `a` and `b` times stalk bases of `L_η` and `N_η`, the generic value of
the product is `a * b` times the product of those bases, which is a stalk basis of
`(L ⊗_{𝒪_X} N)_η`; and `a * b` is nonzero in the function field. -/
@[stacks 02SL "nonzero product", ega "IV 20.1.10" "integral; tensor clause"]
theorem isRegularMeromorphicSection_tensorMeromorphicSection
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (s : MeromorphicSection X.sheaf L) (t : MeromorphicSection X.sheaf N)
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    (ht : IsRegularMeromorphicSection X.sheaf N t) :
    IsRegularMeromorphicSection X.sheaf (Scheme.Modules.tensorObj L N)
      (tensorMeromorphicSection X L N s t) := by
  obtain ⟨e, hbe⟩ := exists_isStalkBasis_genericPoint X L
  obtain ⟨f, hbf⟩ := exists_isStalkBasis_genericPoint X N
  obtain ⟨a, ha⟩ := hbe.surjective (meromorphicGenericValue X L s)
  obtain ⟨b, hb⟩ := hbf.surjective (meromorphicGenericValue X N t)
  replace ha : a • e = meromorphicGenericValue X L s := ha
  replace hb : b • f = meromorphicGenericValue X N t := hb
  have ha0 := ne_zero_of_meromorphicGenericValue_eq_smul X L s hs ha.symm
  have hb0 := ne_zero_of_meromorphicGenericValue_eq_smul X N t ht hb.symm
  have hv : tensorStalkTmul L N (genericPoint X) (meromorphicGenericValue X L s)
        (meromorphicGenericValue X N t) =
      (a * b) • tensorStalkTmul L N (genericPoint X) e f :=
    (congrArg₂ (tensorStalkTmul L N (genericPoint X)) ha.symm hb.symm).trans
      (tensorStalkTmul_smul_smul L N (genericPoint X) a b e f)
  refine isRegularMeromorphicSection_meromorphicSectionOfConstantGenericStalk X _ ?_
  intro r r' hrr'
  rw [hv] at hrr'
  have hz : (r * (a * b)) • tensorStalkTmul L N (genericPoint X) e f =
      (r' * (a * b)) • tensorStalkTmul L N (genericPoint X) e f :=
    (smul_smul r (a * b) _).symm.trans (hrr'.trans (smul_smul r' (a * b) _))
  exact mul_right_cancel₀ (mul_ne_zero ha0 hb0)
    ((isStalkBasis_tensorStalkTmul L N (genericPoint X) hbe hbf).injective hz)

/-! ### Additivity of the divisor -/

variable [IsLocallyNoetherian X]

/-- **Stacks 02SL, coefficientwise.** The order of vanishing of Tag 02SF of a product of
regular meromorphic sections along a prime divisor `Z` is the sum of the two orders: if `m`
generates `L_ξ` and `n` generates `N_ξ` at the generic point `ξ` of `Z`, then `m ⊗ n` generates
`(L ⊗_{𝒪_X} N)_ξ`, and the coordinate of `s ⊗ t` against it is the product of the coordinates of
`s` against `m` and of `t` against `n`, because the product of stalk elements is bilinear and
commutes with specialization from the generic point of `X`. The order of vanishing is
multiplicative. -/
theorem orderOfVanishingMeromorphic_tensorMeromorphicSection
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (s : MeromorphicSection X.sheaf L) (t : MeromorphicSection X.sheaf N)
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    (ht : IsRegularMeromorphicSection X.sheaf N t) (Z : PrimeDivisor X) :
    orderOfVanishingMeromorphic X (Scheme.Modules.tensorObj L N)
        (tensorMeromorphicSection X L N s t)
        (isRegularMeromorphicSection_tensorMeromorphicSection X L N s t hs ht) Z =
      orderOfVanishingMeromorphic X L s hs Z + orderOfVanishingMeromorphic X N t ht Z := by
  obtain ⟨m, hm, a, ha⟩ := (orderOfVanishingMeromorphicData X L s hs Z).2.1
  obtain ⟨n, hn, b, hb⟩ := (orderOfVanishingMeromorphicData X N t ht Z).2.1
  have hsa : meromorphicGenericValue X L s =
      a • L.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) m :=
    meromorphicGenericValue_eq X L s _ ha
  have htb : meromorphicGenericValue X N t =
      b • N.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) n :=
    meromorphicGenericValue_eq X N t _ hb
  have ha0 := ne_zero_of_meromorphicGenericValue_eq_smul X L s hs hsa
  have hb0 := ne_zero_of_meromorphicGenericValue_eq_smul X N t ht htb
  have hmn : Submodule.span (X.presheaf.stalk Z.genericPoint)
      {tensorStalkTmul L N Z.genericPoint m n} = ⊤ :=
    span_singleton_tensorStalkTmul_eq_top L N Z.genericPoint hm hn
  have hcoord :
      (meromorphicSectionSheafIsoConstant X (Scheme.Modules.tensorObj L N)).val.hom.val.app
          (op (⊤ : X.Opens)) ((tensorMeromorphicSection X L N s t).val (op ⊤)) =
        constantGenericStalkModuleSection X (Scheme.Modules.tensorObj L N) ⊤
          ((a * b) • (Scheme.Modules.tensorObj L N).presheaf.stalkSpecializes
            ((genericPoint_spec X).specializes trivial)
              (tensorStalkTmul L N Z.genericPoint m n)) := by
    refine (iso_tensorMeromorphicSection_eq X L N s t hsa htb).trans (congrArg _ ?_)
    refine (tensorStalkTmul_smul_smul L N (genericPoint X) a b _ _).trans ?_
    exact congrArg (fun z => (a * b) • z)
      (tensorStalkTmul_stalkSpecializes L N ((genericPoint_spec X).specializes trivial) m n)
  have hordP := (orderOfVanishingMeromorphicData X (Scheme.Modules.tensorObj L N)
    (tensorMeromorphicSection X L N s t)
    (isRegularMeromorphicSection_tensorMeromorphicSection X L N s t hs ht) Z).2.2
      (tensorStalkTmul L N Z.genericPoint m n) hmn (a * b) hcoord
  have hordL := (orderOfVanishingMeromorphicData X L s hs Z).2.2 m hm a ha
  have hordN := (orderOfVanishingMeromorphicData X N t ht Z).2.2 n hn b hb
  exact hordP.trans ((Scheme.ord_mul ha0 hb0).trans
    (congrArg₂ (· + ·) hordL.symm hordN.symm))

/-- **Stacks 02SL: the divisor of a product is the sum of the divisors.** The Weil divisor of
Tag 0BE6 part (1) is additive in the product of regular meromorphic sections of invertible
modules, coefficient by coefficient. -/
@[stacks 02SL "divisor additivity"]
theorem weilDivisorOfMeromorphicSection_tensorMeromorphicSection
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (s : MeromorphicSection X.sheaf L) (t : MeromorphicSection X.sheaf N)
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    (ht : IsRegularMeromorphicSection X.sheaf N t) :
    weilDivisorOfMeromorphicSection X (Scheme.Modules.tensorObj L N)
        (tensorMeromorphicSection X L N s t)
        (isRegularMeromorphicSection_tensorMeromorphicSection X L N s t hs ht) =
      weilDivisorOfMeromorphicSection X L s hs + weilDivisorOfMeromorphicSection X N t ht := by
  refine Subtype.ext (funext fun Z => ?_)
  simp only [weilDivisorOfMeromorphicSection_apply, AddSubgroup.coe_add, Pi.add_apply]
  exact orderOfVanishingMeromorphic_tensorMeromorphicSection X L N s t hs ht Z

/-- **Stacks 02SL: the divisor class of a tensor product is the sum of the divisor classes.**
The Weil divisor class of Tag 0BE6 part (2) is additive in the tensor product of invertible
modules: a regular meromorphic section of each factor exists by Tag 02OZ part (1), their
product is a regular meromorphic section of the tensor product, and its divisor is the sum of
their divisors. This is the input Tag 0BE7 needs, and it is supplied to it in
`AlgebraicGeometry.picardToWeilDivisorClassGroup`. -/
@[stacks 02SL "divisor-class additivity"]
theorem weilDivisorClassOfInvertibleSheaf_tensorObj
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] :
    weilDivisorClassOfInvertibleSheaf X (Scheme.Modules.tensorObj L N) =
      weilDivisorClassOfInvertibleSheaf X L + weilDivisorClassOfInvertibleSheaf X N := by
  obtain ⟨s, hs⟩ := exists_isRegularMeromorphicSection_of_isIntegral X L
  obtain ⟨t, ht⟩ := exists_isRegularMeromorphicSection_of_isIntegral X N
  rw [weilDivisorClassOfInvertibleSheaf_eq X L s hs,
    weilDivisorClassOfInvertibleSheaf_eq X N t ht,
    weilDivisorClassOfInvertibleSheaf_eq X (Scheme.Modules.tensorObj L N)
      (tensorMeromorphicSection X L N s t)
      (isRegularMeromorphicSection_tensorMeromorphicSection X L N s t hs ht),
    weilDivisorOfMeromorphicSection_tensorMeromorphicSection X L N s t hs ht]
  rfl

end AlgebraicGeometry

end
