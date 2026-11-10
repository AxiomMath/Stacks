module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndEtale
public import StacksFrontier.RingTheory.Flat.BaseChangeAlongFlatAlgebra
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Quotient
public import StacksFrontier.RingTheory.WeaklyEtale.Flat

/-!
# Flatness over a henselization

Let `(R, 𝔪, κ)` be a local ring, let `κ ⊆ L` be an extension of its residue field and let `Rh`
be a henselization of `R` with residue field `L`. A module which is flat over `R` and carries a
compatible `Rh`-action is automatically flat over `Rh`: a henselization is a filtered colimit of
étale algebras, hence weakly étale, and flatness ascends along a weakly étale ring map.

Applying this to the tower `R → R^h → R^{sh}` consisting of the henselization and a
henselization with a larger residue field — the strict henselization when the larger field is a
separable closure — gives the three equivalent flatness conditions on an `R^{sh}`-module. When
the module is obtained from an `R^h`-module by extension of scalars, two further conditions on
that module are equivalent, and when that module is in turn obtained from an `R`-module by
extension of scalars, so is flatness of the original module.

## Main results

* `Module.Flat.of_isHenselization`: flatness over a local ring ascends to any of its
  henselizations.
* `flat_tfae_henselization`: the three equivalent flatness conditions on a module over a
  henselization with extended residue field.
* `flat_tfae_baseChange_henselization`: the five equivalent conditions when the module is a base
  change.
* `flat_tfae_iteratedBaseChange_henselization`: the six equivalent conditions when the module is
  an iterated base change.
* `IsLocalRing.IsHenselization.quotient`: a strict henselization of `R` stays one after dividing
  `R` and it by an ideal `I ⊆ 𝔪`.
* `Module.Flat.quotient_iff_of_isHenselization`: over `R/I` and over `R^{sh}/I R^{sh}` flatness
  of a module is the same condition.
* `Module.Flat.quotSMul_baseChange_iff_of_faithfullyFlat`: dividing a faithfully flat base
  change by an ideal of the base does not change flatness over a third ring.
* `Module.Flat.quotSMul_baseChange_iff_of_isHenselization`: the two preceding results composed.

## Implementation notes

The henselization and the henselization with extended residue field are represented by rings
satisfying `IsLocalRing.IsHenselization R (ResidueField R) Rh` and
`IsLocalRing.IsHenselization R K Rsh`, with a compatible `Rh`-algebra structure on `Rsh`
standing for the canonical map between them; taking `K` to be a separable closure of the residue
field makes `Rsh` a strict henselization.

The displayed equalities `M^{sh} = M^h ⊗ R^{sh}` and `M^h = M ⊗ R^h` of the source are
represented by the tensor products themselves, with the scalars written as the left tensor factor
following Mathlib's convention for the module structure on a tensor product. The restriction of a
module along a tower of structure maps is `Module.compHom`, supplied in the statement so that the
listed conditions are about one fixed additive group.

## References

* [Stacks Project, Tag 05VL](https://stacks.math.columbia.edu/tag/05VL)
* [Stacks Project, Tag 05WS](https://stacks.math.columbia.edu/tag/05WS), strict henselization
  and quotients
* [Stacks Project, Tag 0584](https://stacks.math.columbia.edu/tag/0584), flatness over the base
  along a faithfully flat change of algebra
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u v w x y

/-- **Flatness ascends to a henselization.** A module over a henselization `Rh` of a local ring
`R` whose restriction to `R` is flat is flat over `Rh`. A henselization is ind-étale, hence
weakly étale (Stacks 097N), and flatness over the base ascends along a weakly étale ring map
(Stacks 092C). -/
theorem Module.Flat.of_isHenselization {R : Type u} [CommRing R] [IsLocalRing R]
    {Rh : Type v} [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    (L : Type w) [Field L] [Algebra (ResidueField R) L] [IsHenselization R L Rh]
    (M : Type x) [AddCommGroup M] [Module R M] [Module Rh M] [IsScalarTower R Rh M]
    [Module.Flat R M] : Module.Flat Rh M :=
  have : Algebra.WeaklyEtale R Rh :=
    Algebra.weaklyEtale_of_ind_etale (IsHenselization.ind_etale (R := R) (L := L) (Rh := Rh))
  flat_of_flat_of_mul_flat R Rh (Algebra.WeaklyEtale.flat_lmul' R Rh) M inferInstance

/-- A module over a henselization is flat over the local ring if and only if it is flat over the
henselization. -/
private theorem flat_iff_of_isHenselization {R : Type u} [CommRing R] [IsLocalRing R]
    {Rh : Type v} [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    (L : Type w) [Field L] [Algebra (ResidueField R) L] [IsHenselization R L Rh]
    (M : Type x) [AddCommGroup M] [Module R M] [Module Rh M] [IsScalarTower R Rh M] :
    Module.Flat R M ↔ Module.Flat Rh M :=
  have : Module.Flat R Rh := IsHenselization.flat (L := L)
  ⟨fun _ => Module.Flat.of_isHenselization (R := R) (Rh := Rh) L M,
    fun _ => Module.Flat.trans R Rh M⟩

/-- For a tower `A → B → C` of commutative rings and a `C`-module `N`, the `A`- and `B`-module
structures obtained by restricting along the structure maps to `C` make `N` a scalar tower. -/
private theorem isScalarTower_compHom_algebraMap {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (N : Type*) [AddCommGroup N] [Module C N] :
    letI : Module B N := Module.compHom N (algebraMap B C)
    letI : Module A N := Module.compHom N (algebraMap A C)
    IsScalarTower A B N := by
  let : Module B N := Module.compHom N (algebraMap B C)
  let : Module A N := Module.compHom N (algebraMap A C)
  refine ⟨fun r s n => ?_⟩
  change algebraMap B C (r • s) • n = algebraMap A C r • (algebraMap B C s • n)
  simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply A B C, mul_smul]

variable {R : Type u} {Rh : Type v} {Rsh : Type w} [CommRing R] [IsLocalRing R]
  [CommRing Rh] [IsLocalRing Rh] [CommRing Rsh] [IsLocalRing Rsh]
  [Algebra R Rh] [Algebra Rh Rsh] [Algebra R Rsh] [IsScalarTower R Rh Rsh]
  [IsHenselization R (ResidueField R) Rh]
  {K : Type x} [Field K] [Algebra (ResidueField R) K]
  [IsHenselization R K Rsh]

include K

/-- **Stacks Project, Tag 05VL, conditions (1)--(3).** A module over a henselization with
extended residue field is flat over the original local ring if and only if it is flat over the
henselization with unchanged residue field, if and only if it is flat over the
extended-residue-field henselization. A strict henselization is the case where `K` is a separable
closure of the residue field. -/
@[stacks 05VL "conditions (1)--(3)",
  sga "4 VIII 4.1" "more general",
  sga "4 VIII 4.4" "more general",
  sga "4 XVII 5.5.29" "Flatness clause"]
theorem flat_tfae_henselization {Msh : Type y} [AddCommGroup Msh] [Module Rsh Msh] :
    letI : Module Rh Msh := Module.compHom Msh (algebraMap Rh Rsh)
    letI : Module R Msh := Module.compHom Msh (algebraMap R Rsh)
    List.TFAE [Module.Flat R Msh, Module.Flat Rh Msh, Module.Flat Rsh Msh] := by
  let : Module Rh Msh := Module.compHom Msh (algebraMap Rh Rsh)
  let : Module R Msh := Module.compHom Msh (algebraMap R Rsh)
  let : IsScalarTower R Rh Msh := isScalarTower_compHom_algebraMap Msh
  let : IsScalarTower R Rsh Msh := IsScalarTower.of_compHom R Rsh Msh
  let : Module.Flat R Rh := IsHenselization.flat (L := ResidueField R)
  let : Module.Flat R Rsh := IsHenselization.flat (L := K)
  tfae_have 1 ↔ 2 := flat_iff_of_isHenselization (Rh := Rh) (ResidueField R) Msh
  tfae_have 1 ↔ 3 := flat_iff_of_isHenselization (Rh := Rsh) K Msh
  tfae_finish

/-- **Stacks Project, Tag 05VL, conditions (1)--(5).** If the module over the
extended-residue-field henselization is obtained from an `Rh`-module by extension of scalars, its
three flatness conditions are also equivalent to flatness of the original module over `R` and
over `Rh`. -/
@[stacks 05VL "conditions (1)--(5)"]
theorem flat_tfae_baseChange_henselization {Mh : Type y} [AddCommGroup Mh] [Module Rh Mh] :
    letI : Module R Mh := Module.compHom Mh (algebraMap R Rh)
    letI : Module Rsh (Rsh ⊗[Rh] Mh) := TensorProduct.leftModule
    letI : Module Rh (Rsh ⊗[Rh] Mh) := Module.compHom (Rsh ⊗[Rh] Mh) (algebraMap Rh Rsh)
    letI : Module R (Rsh ⊗[Rh] Mh) := Module.compHom (Rsh ⊗[Rh] Mh) (algebraMap R Rsh)
    List.TFAE [Module.Flat R (Rsh ⊗[Rh] Mh), Module.Flat Rh (Rsh ⊗[Rh] Mh),
      Module.Flat Rsh (Rsh ⊗[Rh] Mh), Module.Flat R Mh, Module.Flat Rh Mh] := by
  let : Module R Mh := Module.compHom Mh (algebraMap R Rh)
  let : Module Rsh (Rsh ⊗[Rh] Mh) := TensorProduct.leftModule
  let : Module Rh (Rsh ⊗[Rh] Mh) := Module.compHom (Rsh ⊗[Rh] Mh) (algebraMap Rh Rsh)
  let : Module R (Rsh ⊗[Rh] Mh) := Module.compHom (Rsh ⊗[Rh] Mh) (algebraMap R Rsh)
  let : IsScalarTower R Rh Mh := IsScalarTower.of_compHom R Rh Mh
  let : Module.Flat R Rh := IsHenselization.flat (L := ResidueField R)
  let : Module.Flat R Rsh := IsHenselization.flat (L := K)
  let : IsLocalHom (algebraMap R Rsh) := IsHenselization.isLocalHom (L := K)
  let : IsLocalHom (algebraMap Rh Rsh) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap Rh Rsh)).out 3 1).mp
    rw [← IsHenselization.map_maximalIdeal (R := R) (Rh := Rh) (L := ResidueField R),
      Ideal.map_map, ← IsScalarTower.algebraMap_eq R Rh Rsh,
      IsHenselization.map_maximalIdeal (R := R) (Rh := Rsh) (L := K)]
  let : Module.Flat Rh Rsh := Module.Flat.of_isHenselization (R := R) (Rh := Rh)
    (ResidueField R) Rsh
  let : Module.FaithfullyFlat Rh Rsh := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have ht := flat_tfae_henselization (R := R) (Rh := Rh) (Rsh := Rsh) (K := K)
    (Msh := Rsh ⊗[Rh] Mh)
  tfae_have 1 ↔ 2 := ht.out 1 2
  tfae_have 2 ↔ 3 := ht.out 2 3
  tfae_have 3 ↔ 5 := Module.Flat.iff_flat_tensorProduct Rh Mh Rsh
  tfae_have 4 ↔ 5 := flat_iff_of_isHenselization (Rh := Rh) (ResidueField R) Mh
  tfae_finish

/-- **Stacks Project, Tag 05VL, conditions (1)--(6).** If the `Rh`-module is in turn obtained from
an `R`-module by extension of scalars, all five flatness conditions after base change are
equivalent to flatness of the original module over `R`. -/
@[stacks 05VL "conditions (1)--(6)"]
theorem flat_tfae_iteratedBaseChange_henselization {M : Type y} [AddCommGroup M] [Module R M] :
    letI : Module Rh (Rh ⊗[R] M) := TensorProduct.leftModule
    letI : Module R (Rh ⊗[R] M) := Module.compHom (Rh ⊗[R] M) (algebraMap R Rh)
    letI : Module Rsh (Rsh ⊗[Rh] (Rh ⊗[R] M)) := TensorProduct.leftModule
    letI : Module Rh (Rsh ⊗[Rh] (Rh ⊗[R] M)) :=
      Module.compHom (Rsh ⊗[Rh] (Rh ⊗[R] M)) (algebraMap Rh Rsh)
    letI : Module R (Rsh ⊗[Rh] (Rh ⊗[R] M)) :=
      Module.compHom (Rsh ⊗[Rh] (Rh ⊗[R] M)) (algebraMap R Rsh)
    List.TFAE [Module.Flat R (Rsh ⊗[Rh] (Rh ⊗[R] M)), Module.Flat Rh (Rsh ⊗[Rh] (Rh ⊗[R] M)),
      Module.Flat Rsh (Rsh ⊗[Rh] (Rh ⊗[R] M)), Module.Flat R (Rh ⊗[R] M),
      Module.Flat Rh (Rh ⊗[R] M), Module.Flat R M] := by
  let : Module Rh (Rh ⊗[R] M) := TensorProduct.leftModule
  let : Module R (Rh ⊗[R] M) := Module.compHom (Rh ⊗[R] M) (algebraMap R Rh)
  let : Module Rsh (Rsh ⊗[Rh] (Rh ⊗[R] M)) := TensorProduct.leftModule
  let : Module Rh (Rsh ⊗[Rh] (Rh ⊗[R] M)) :=
    Module.compHom (Rsh ⊗[Rh] (Rh ⊗[R] M)) (algebraMap Rh Rsh)
  let : Module R (Rsh ⊗[Rh] (Rh ⊗[R] M)) :=
    Module.compHom (Rsh ⊗[Rh] (Rh ⊗[R] M)) (algebraMap R Rsh)
  let : Module.FaithfullyFlat R Rh := IsHenselization.faithfullyFlat (L := ResidueField R)
  have h5 := flat_tfae_baseChange_henselization (R := R) (Rh := Rh) (Rsh := Rsh) (K := K)
    (Mh := Rh ⊗[R] M)
  tfae_have 1 ↔ 2 := h5.out 1 2
  tfae_have 2 ↔ 3 := h5.out 2 3
  tfae_have 3 ↔ 4 := h5.out 3 4
  tfae_have 4 ↔ 5 := h5.out 4 5
  tfae_have 5 ↔ 6 := Module.Flat.iff_flat_tensorProduct R M Rh
  tfae_finish

end

/-!
# Flatness over a henselization after dividing by an ideal of the base

Let `(A, 𝔪, κ)` be a local ring, let `A → A^{sh}` be a strict henselization of `A` and let
`I ⊆ 𝔪` be an ideal. Then `A^{sh}/I A^{sh}` is a strict henselization of `A/I` (Stacks 05WS), so
an `A^{sh}/I A^{sh}`-module is flat over `A/I` exactly when it is flat over `A^{sh}/I A^{sh}`
(Stacks 05VL). Independently, for a faithfully flat ring map `C → C^{sh}`, an ideal `J` of `C` and
a `C`-module `M`, the module `(C^{sh} ⊗_C M)/J(C^{sh} ⊗_C M)` is flat over a ring acting through
`C^{sh}/J C^{sh}` exactly when `M/JM` is flat over it through `C/J` (Stacks 0584 (2)), because
`C/J → C^{sh}/J C^{sh}` is faithfully flat. The two statements compose into one criterion for
flatness of the fibre of a base-changed module over the fibre of a henselization.

## Main definitions

* `TensorProduct.quotSMulBaseChangeEquivOfLE`: the identification
  `(C^{sh}/J') ⊗_{C/J} (M/JM) = (C^{sh} ⊗_C M)/J'(C^{sh} ⊗_C M)`, for `J'` an ideal of
  `C^{sh}` containing `J C^{sh}`.
* `TensorProduct.quotSMulBaseChangeEquiv`: the same at `J' = J C^{sh}`, which is the
  identification `(C^{sh}/J C^{sh}) ⊗_{C/J} (M/JM) = (C^{sh} ⊗_C M)/J(C^{sh} ⊗_C M)`.

## Main results

* `IsLocalRing.IsHenselization.quotient`: Stacks 05WS read as a henselization structure on the
  quotient tower.
* `Module.Flat.quotSMul_baseChange_iff_of_faithfullyFlat`: the fibre of a faithfully flat base
  change is flat over a ring if and only if the fibre of the original module is.
* `Module.Flat.quotient_iff_of_isHenselization`: flatness over `A/I` and over
  `A^{sh}/I A^{sh}` agree.
* `Module.Flat.quotSMul_baseChange_iff_of_isHenselization`: the composite of the two.
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u v w x y

namespace IsLocalRing

/-- The quotient of a local ring by an ideal contained in its maximal ideal is a local ring,
the ideal being proper and the quotient map surjective. -/
public theorem isLocalRing_quotient_of_le_maximalIdeal_of_isHenselization {A : Type u} [CommRing A]
    [IsLocalRing A] {I : Ideal A} (hI : I ≤ maximalIdeal A) : IsLocalRing (A ⧸ I) :=
  have : Nontrivial (A ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top hI)
  IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- A ring map whose precomposition with a surjection is local is itself local, since every
element of the source of the map is the image of one on which the composite reflects units. -/
public theorem isLocalHom_of_isLocalHom_comp {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] (g : B →+* C) (π : A →+* B) (hπ : Function.Surjective π)
    [IsLocalHom (g.comp π)] : IsLocalHom g where
  map_nonunit b hb := by
    obtain ⟨a, rfl⟩ := hπ b
    exact (IsLocalHom.map_nonunit (f := g.comp π) a hb).map π

namespace IsHenselization

variable {A Ash : Type u} [CommRing A] [IsLocalRing A] [CommRing Ash] [IsLocalRing Ash]
  [Algebra A Ash] (L : Type v) [Field L] [Algebra (ResidueField A) L] [IsHenselization A L Ash]

include L

/-- The ideal of a henselization generated by the image of an ideal contained in the maximal
ideal of the base is contained in the maximal ideal, since `𝔪 A^h` is the maximal ideal. -/
public theorem map_le_maximalIdeal {I : Ideal A} (hI : I ≤ maximalIdeal A) :
    I.map (algebraMap A Ash) ≤ maximalIdeal Ash := by
  rw [← map_maximalIdeal (R := A) (L := L) (Rh := Ash)]
  exact Ideal.map_mono hI

/-- The quotient of a henselization by the ideal generated by the image of an ideal contained in
the maximal ideal of the base is a local ring. -/
public theorem isLocalRing_quotient {I : Ideal A} (hI : I ≤ maximalIdeal A) :
    IsLocalRing (Ash ⧸ I.map (algebraMap A Ash)) :=
  isLocalRing_quotient_of_le_maximalIdeal_of_isHenselization (map_le_maximalIdeal L hI)

/-- The map `A/I → A^h/I A^h` induced by the structure map of a henselization is local, for `I`
an ideal contained in the maximal ideal of `A`. -/
public theorem isLocalHom_quotient {I : Ideal A} (hI : I ≤ maximalIdeal A) :
    letI : IsLocalRing (A ⧸ I) := isLocalRing_quotient_of_le_maximalIdeal_of_isHenselization hI
    letI : IsLocalRing (Ash ⧸ I.map (algebraMap A Ash)) := isLocalRing_quotient L hI
    IsLocalHom (algebraMap (A ⧸ I) (Ash ⧸ I.map (algebraMap A Ash))) := by
  let : IsLocalRing (A ⧸ I) := isLocalRing_quotient_of_le_maximalIdeal_of_isHenselization hI
  let : IsLocalRing (Ash ⧸ I.map (algebraMap A Ash)) := isLocalRing_quotient L hI
  let : IsLocalHom (algebraMap A Ash) := isLocalHom (L := L)
  let : IsLocalHom (Ideal.Quotient.mk (I.map (algebraMap A Ash))) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hcomp : (algebraMap (A ⧸ I) (Ash ⧸ I.map (algebraMap A Ash))).comp
      (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk (I.map (algebraMap A Ash))).comp (algebraMap A Ash) :=
    RingHom.ext fun _ => rfl
  let : IsLocalHom ((algebraMap (A ⧸ I) (Ash ⧸ I.map (algebraMap A Ash))).comp
      (Ideal.Quotient.mk I)) := by
    rw [hcomp]; exact RingHom.isLocalHom_comp _ _
  exact isLocalHom_of_isLocalHom_comp _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- **The residue field of a henselization is the prescribed one.** If the prescribed residue
field `L` of a henselization `A^h` of `A` is a separable algebraic closure of `κ`, then so is the
residue field of `A^h` itself, for the extension induced by `A → A^h`. -/
public theorem isSepClosure [IsSepClosure (ResidueField A) L] :
    letI : IsLocalHom (algebraMap A Ash) := isLocalHom (L := L)
    IsSepClosure (ResidueField A) (ResidueField Ash) := by
  let : IsLocalHom (algebraMap A Ash) := isLocalHom (L := L)
  let : IsSepClosed L := IsSepClosure.sep_closed (ResidueField A)
  let : Algebra.IsSeparable (ResidueField A) L := IsSepClosure.separable
  obtain ⟨e, he⟩ := exists_residueFieldEquiv (R := A) (L := L) (Rh := Ash)
  have hsq : (algebraMap (ResidueField A) (ResidueField Ash)).comp
      (RingEquiv.refl (ResidueField A) : ResidueField A →+* ResidueField A) =
      (e : L →+* ResidueField Ash).comp (algebraMap (ResidueField A) L) := by
    refine RingHom.ext fun y => ?_
    obtain ⟨x, rfl⟩ := residue_surjective y
    exact (ResidueField.algebraMap_residue x).trans (he x).symm
  exact isSepClosure_iff.mpr ⟨IsSepClosed.of_ringEquiv e.symm,
    Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl (ResidueField A)) e hsq⟩

/-- **A strict henselization stays one after dividing by an ideal of the base.** Let `A^{sh}` be a
henselization of a local ring `(A, 𝔪, κ)` whose prescribed residue field `L` is a separable
algebraic closure of `κ`, and let `I ⊆ 𝔪` be an ideal. Then `A^{sh}/I A^{sh}` is a henselization
of `A/I` with residue field its own residue field.

The hypothesis `IsSepClosure (ResidueField A) L` is carried: it is what Stacks 05WS assumes, so
the statement is about strict henselizations and not about an arbitrary prescribed `L`. For the
same reason `A` and `A^{sh}` are taken in a common universe. -/
public theorem quotient [IsSepClosure (ResidueField A) L]
    {I : Ideal A} (hI : I ≤ maximalIdeal A) :
    letI : IsLocalRing (A ⧸ I) := isLocalRing_quotient_of_le_maximalIdeal_of_isHenselization hI
    letI : IsLocalRing (Ash ⧸ I.map (algebraMap A Ash)) := isLocalRing_quotient L hI
    letI : IsLocalHom (algebraMap (A ⧸ I) (Ash ⧸ I.map (algebraMap A Ash))) :=
      isLocalHom_quotient L hI
    IsHenselization (A ⧸ I) (ResidueField (Ash ⧸ I.map (algebraMap A Ash)))
      (Ash ⧸ I.map (algebraMap A Ash)) := by
  let : IsLocalRing (A ⧸ I) := isLocalRing_quotient_of_le_maximalIdeal_of_isHenselization hI
  let : IsLocalRing (Ash ⧸ I.map (algebraMap A Ash)) := isLocalRing_quotient L hI
  let : IsLocalHom (algebraMap (A ⧸ I) (Ash ⧸ I.map (algebraMap A Ash))) :=
    isLocalHom_quotient L hI
  let : HenselianLocalRing Ash := henselian (R := A) (L := L) (Rh := Ash)
  let : IsLocalHom (algebraMap A Ash) := isLocalHom (L := L)
  let : IsSepClosure (ResidueField A) (ResidueField Ash) := isSepClosure L
  obtain ⟨-, -, -, hhens, hind, -, -⟩ :=
    IsLocalRing.strictHenselization_quotient (R := A) (Rsh := Ash)
      (ind_etale_of_universe_le.{u, v, u} (R := A) L) (map_maximalIdeal (L := L)) I hI
  exact of_ind_etale hhens hind ⟨RingEquiv.refl _, fun x => ResidueField.algebraMap_residue x⟩

end IsHenselization

end IsLocalRing

/-- Left tensoring a module with a quotient of the ring is quotienting that module by the
corresponding submodule, as modules over the quotient ring. -/
@[ega "0 7.2.9" "partial", ega "0 7.3.1" "partial", ega "0 7.7.2" "special case"]
public noncomputable def TensorProduct.quotTensorEquivQuotSMulOverQuotient {R : Type u}
    [CommRing R] (J : Ideal R) (M : Type w) [AddCommGroup M] [Module R M] :
    (R ⧸ J) ⊗[R] M ≃ₗ[R ⧸ J] M ⧸ J • (⊤ : Submodule R M) :=
  { TensorProduct.quotTensorEquivQuotSMul M J with
    map_smul' := by
      intro s x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
      exact (TensorProduct.quotTensorEquivQuotSMul M J).map_smul r x }

/-- **A faithfully flat algebra stays faithfully flat after dividing by an ideal of the base.**
For `C → C'` faithfully flat and `J` an ideal of `C`, the ring `C'/J C'` is faithfully flat over
`C/J`, being the base change `(C/J) ⊗_C C'`. -/
@[ega "IV 2.5.8.8" "partial"]
public theorem Module.FaithfullyFlat.quotient_map_of_idealSMul {C Csh : Type*} [CommRing C]
    [CommRing Csh] [Algebra C Csh] [Module.FaithfullyFlat C Csh] (J : Ideal C) :
    Module.FaithfullyFlat (C ⧸ J) (Csh ⧸ J.map (algebraMap C Csh)) :=
  Module.FaithfullyFlat.of_linearEquiv (C ⧸ J) ((C ⧸ J) ⊗[C] Csh)
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Csh J).toLinearEquiv

/-- **Dividing a base change by an ideal of the base.** For a `C`-algebra `C'`, an ideal `J` of
`C` and a `C`-module `M`, the quotient of `C' ⊗_C M` by the submodule generated by `J` is the base
change of `M/JM` along `C/J → C'/J C'`, as modules over `C'/J C'`. -/
public noncomputable def TensorProduct.quotSMulBaseChangeEquivOfLE {C : Type*} (Csh : Type*)
    [CommRing C] [CommRing Csh] [Algebra C Csh] (J : Ideal C) (J' : Ideal Csh)
    (hJ : J.map (algebraMap C Csh) ≤ J') (M : Type*) [AddCommGroup M] [Module C M] :
    letI : Algebra (C ⧸ J) (Csh ⧸ J') :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.1 hJ)
    (Csh ⧸ J') ⊗[C ⧸ J] (M ⧸ J • (⊤ : Submodule C M)) ≃ₗ[Csh ⧸ J']
      (Csh ⊗[C] M) ⧸ J' • (⊤ : Submodule Csh (Csh ⊗[C] M)) :=
  letI : Algebra (C ⧸ J) (Csh ⧸ J') :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.1 hJ)
  letI : IsScalarTower C (C ⧸ J) (Csh ⧸ J') :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [← Ideal.Quotient.mk_algebraMap]; exact Ideal.quotientMap_mk.symm
  (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (Csh ⧸ J') (Csh ⧸ J'))
      (TensorProduct.quotTensorEquivQuotSMulOverQuotient J M)).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange C (C ⧸ J) (Csh ⧸ J') (Csh ⧸ J') M ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange C Csh (Csh ⧸ J') (Csh ⧸ J') M).symm ≪≫ₗ
    TensorProduct.quotTensorEquivQuotSMulOverQuotient J' (Csh ⊗[C] M)

/-- **Dividing a base change by an ideal of the base.** For a `C`-algebra `C'`, an ideal `J` of
`C` and a `C`-module `M`, the quotient of `C' ⊗_C M` by the submodule generated by `J` is the base
change of `M/JM` along `C/J → C'/J C'`, as modules over `C'/J C'`.

This is `TensorProduct.quotSMulBaseChangeEquivOfLE` at the ideal of the target generated by the
ideal of the base. -/
@[ega "0 7.7.2" "special case"]
public noncomputable def TensorProduct.quotSMulBaseChangeEquiv {C : Type*} (Csh : Type*)
    [CommRing C] [CommRing Csh] [Algebra C Csh] (J : Ideal C) (M : Type*) [AddCommGroup M]
    [Module C M] :
    (Csh ⧸ J.map (algebraMap C Csh)) ⊗[C ⧸ J] (M ⧸ J • (⊤ : Submodule C M)) ≃ₗ[
      Csh ⧸ J.map (algebraMap C Csh)]
      (Csh ⊗[C] M) ⧸ (J.map (algebraMap C Csh)) • (⊤ : Submodule Csh (Csh ⊗[C] M)) :=
  TensorProduct.quotSMulBaseChangeEquivOfLE Csh J (J.map (algebraMap C Csh)) le_rfl M

/-- **Stacks 0584 (2) after dividing by an ideal.** Let `C → C'` be faithfully flat, let `J` be an
ideal of `C`, let `M` be a `C`-module and let `R₀` be a ring acting on `C/J` and on `C'/J C'`
compatibly. Then `(C' ⊗_C M)/J(C' ⊗_C M)` is flat over `R₀` if and only if `M/JM` is. -/
public theorem Module.Flat.quotSMul_baseChange_iff_of_faithfullyFlat {R₀ C : Type*}
    (Csh : Type*) [CommRing R₀] [CommRing C] [CommRing Csh] [Algebra C Csh]
    [Module.FaithfullyFlat C Csh] (J : Ideal C) [Algebra R₀ (C ⧸ J)]
    [Algebra R₀ (Csh ⧸ J.map (algebraMap C Csh))]
    [IsScalarTower R₀ (C ⧸ J) (Csh ⧸ J.map (algebraMap C Csh))]
    (M : Type*) [AddCommGroup M] [Module C M] [Module R₀ (M ⧸ J • (⊤ : Submodule C M))]
    [IsScalarTower R₀ (C ⧸ J) (M ⧸ J • (⊤ : Submodule C M))]
    [Module R₀ ((Csh ⊗[C] M) ⧸ (J.map (algebraMap C Csh)) • (⊤ : Submodule Csh (Csh ⊗[C] M)))]
    [IsScalarTower R₀ (Csh ⧸ J.map (algebraMap C Csh))
      ((Csh ⊗[C] M) ⧸ (J.map (algebraMap C Csh)) • (⊤ : Submodule Csh (Csh ⊗[C] M)))] :
    Module.Flat R₀ ((Csh ⊗[C] M) ⧸
        (J.map (algebraMap C Csh)) • (⊤ : Submodule Csh (Csh ⊗[C] M))) ↔
      Module.Flat R₀ (M ⧸ J • (⊤ : Submodule C M)) := by
  let : Module.FaithfullyFlat (C ⧸ J) (Csh ⧸ J.map (algebraMap C Csh)) :=
    Module.FaithfullyFlat.quotient_map_of_idealSMul J
  have e := (TensorProduct.quotSMulBaseChangeEquiv Csh J M).restrictScalars R₀
  refine Iff.trans ⟨fun h => ?_, fun h => ?_⟩
    (Module.Flat.tensorProduct_iff_of_faithfullyFlat (R := R₀) (S := C ⧸ J)
      (S' := Csh ⧸ J.map (algebraMap C Csh)) (M := M ⧸ J • (⊤ : Submodule C M)))
  · let : Module.Flat R₀ ((Csh ⊗[C] M) ⧸
        (J.map (algebraMap C Csh)) • (⊤ : Submodule Csh (Csh ⊗[C] M))) := h
    exact Module.Flat.of_linearEquiv e
  · let : Module.Flat R₀ ((Csh ⧸ J.map (algebraMap C Csh)) ⊗[C ⧸ J]
        (M ⧸ J • (⊤ : Submodule C M))) := h
    exact Module.Flat.of_linearEquiv e.symm

/-- **Flatness over a quotient of a local ring and over the same quotient of a strict
henselization agree.** Let `A^{sh}` be a henselization of `(A, 𝔪, κ)` whose prescribed residue
field is a separable algebraic closure of `κ`, let `I ⊆ 𝔪` and let `N` carry compatible actions of
`A/I` and `A^{sh}/I A^{sh}`. Then `N` is flat over `A/I` if and only if it is flat over
`A^{sh}/I A^{sh}`.

The hypothesis `IsSepClosure (ResidueField A) L` is carried from
`IsLocalRing.IsHenselization.quotient`, and with it the common universe of `A` and `A^{sh}`. -/
@[sga "4 VIII 4.4" "more general", sga "4 XVII 5.5.29" "partial"]
public theorem Module.Flat.quotient_iff_of_isHenselization
    {A Ash : Type u} [CommRing A] [IsLocalRing A] [CommRing Ash] [IsLocalRing Ash]
    [Algebra A Ash] (L : Type v) [Field L] [Algebra (ResidueField A) L]
    [IsHenselization A L Ash] [IsSepClosure (ResidueField A) L]
    {I : Ideal A} (hI : I ≤ maximalIdeal A)
    (N : Type w) [AddCommGroup N] [Module (A ⧸ I) N]
    [Module (Ash ⧸ I.map (algebraMap A Ash)) N]
    [IsScalarTower (A ⧸ I) (Ash ⧸ I.map (algebraMap A Ash)) N] :
    Module.Flat (A ⧸ I) N ↔ Module.Flat (Ash ⧸ I.map (algebraMap A Ash)) N := by
  let : IsLocalRing (A ⧸ I) :=
    IsLocalRing.isLocalRing_quotient_of_le_maximalIdeal_of_isHenselization hI
  let : IsLocalRing (Ash ⧸ I.map (algebraMap A Ash)) :=
    IsHenselization.isLocalRing_quotient L hI
  let : IsLocalHom (algebraMap (A ⧸ I) (Ash ⧸ I.map (algebraMap A Ash))) :=
    IsHenselization.isLocalHom_quotient L hI
  let : IsHenselization (A ⧸ I) (ResidueField (Ash ⧸ I.map (algebraMap A Ash)))
      (Ash ⧸ I.map (algebraMap A Ash)) := IsHenselization.quotient L hI
  exact flat_iff_of_isHenselization (Rh := Ash ⧸ I.map (algebraMap A Ash))
    (ResidueField (Ash ⧸ I.map (algebraMap A Ash))) N

/-- **Flatness of a fibre of a base change over a fibre of a strict henselization.** Let `A^{sh}`
be a strict henselization of `(A, 𝔪, κ)`, let `I ⊆ 𝔪`, let `C → C'` be faithfully flat with `C'`
also an `A^{sh}/I A^{sh}`-algebra through the quotients, let `J` be an ideal of `C` and let `M` be
a `C`-module. Then `M/JM` is flat over `A/I` if and only if `(C' ⊗_C M)/J(C' ⊗_C M)` is flat over
`A^{sh}/I A^{sh}`.

The algebra structures on the quotients and their compatibilities are hypotheses; in an
application they come from the inclusions of the ideals involved, through
`Ideal.Quotient.algebraQuotientOfLEComap`. The hypothesis `IsSepClosure (ResidueField A) L` is
carried from `IsLocalRing.IsHenselization.quotient`. -/
public theorem Module.Flat.quotSMul_baseChange_iff_of_isHenselization
    {A Ash : Type u} [CommRing A] [IsLocalRing A] [CommRing Ash] [IsLocalRing Ash]
    [Algebra A Ash] (L : Type v) [Field L] [Algebra (ResidueField A) L]
    [IsHenselization A L Ash] [IsSepClosure (ResidueField A) L]
    {I : Ideal A} (hI : I ≤ maximalIdeal A)
    {C : Type w} (Csh : Type x) [CommRing C] [CommRing Csh] [Algebra C Csh]
    [Module.FaithfullyFlat C Csh] (J : Ideal C) [Algebra (A ⧸ I) (C ⧸ J)]
    [Algebra (A ⧸ I) (Csh ⧸ J.map (algebraMap C Csh))]
    [Algebra (Ash ⧸ I.map (algebraMap A Ash)) (Csh ⧸ J.map (algebraMap C Csh))]
    [IsScalarTower (A ⧸ I) (C ⧸ J) (Csh ⧸ J.map (algebraMap C Csh))]
    [IsScalarTower (A ⧸ I) (Ash ⧸ I.map (algebraMap A Ash)) (Csh ⧸ J.map (algebraMap C Csh))]
    (M : Type y) [AddCommGroup M] [Module C M] :
    letI : Module (A ⧸ I) (M ⧸ J • (⊤ : Submodule C M)) :=
      Module.compHom _ (algebraMap (A ⧸ I) (C ⧸ J))
    letI : Module (Ash ⧸ I.map (algebraMap A Ash)) ((Csh ⊗[C] M) ⧸
        (J.map (algebraMap C Csh)) • (⊤ : Submodule Csh (Csh ⊗[C] M))) :=
      Module.compHom _ (algebraMap (Ash ⧸ I.map (algebraMap A Ash))
        (Csh ⧸ J.map (algebraMap C Csh)))
    (Module.Flat (A ⧸ I) (M ⧸ J • (⊤ : Submodule C M)) ↔
      Module.Flat (Ash ⧸ I.map (algebraMap A Ash)) ((Csh ⊗[C] M) ⧸
        (J.map (algebraMap C Csh)) • (⊤ : Submodule Csh (Csh ⊗[C] M)))) := by
  let : Module (A ⧸ I) (M ⧸ J • (⊤ : Submodule C M)) :=
    Module.compHom _ (algebraMap (A ⧸ I) (C ⧸ J))
  let : Module (Ash ⧸ I.map (algebraMap A Ash)) ((Csh ⊗[C] M) ⧸
      (J.map (algebraMap C Csh)) • (⊤ : Submodule Csh (Csh ⊗[C] M))) :=
    Module.compHom _ (algebraMap (Ash ⧸ I.map (algebraMap A Ash))
      (Csh ⧸ J.map (algebraMap C Csh)))
  let : Module (A ⧸ I) ((Csh ⊗[C] M) ⧸
      (J.map (algebraMap C Csh)) • (⊤ : Submodule Csh (Csh ⊗[C] M))) :=
    Module.compHom _ (algebraMap (A ⧸ I) (Csh ⧸ J.map (algebraMap C Csh)))
  let : IsScalarTower (A ⧸ I) (C ⧸ J) (M ⧸ J • (⊤ : Submodule C M)) :=
    IsScalarTower.of_compHom _ _ _
  let : IsScalarTower (A ⧸ I) (Csh ⧸ J.map (algebraMap C Csh)) ((Csh ⊗[C] M) ⧸
      (J.map (algebraMap C Csh)) • (⊤ : Submodule Csh (Csh ⊗[C] M))) :=
    IsScalarTower.of_compHom _ _ _
  let : IsScalarTower (A ⧸ I) (Ash ⧸ I.map (algebraMap A Ash)) ((Csh ⊗[C] M) ⧸
      (J.map (algebraMap C Csh)) • (⊤ : Submodule Csh (Csh ⊗[C] M))) := by
    refine ⟨fun a b x => ?_⟩
    change algebraMap (Ash ⧸ I.map (algebraMap A Ash)) (Csh ⧸ J.map (algebraMap C Csh))
        (a • b) • x = _
    rw [Algebra.smul_def, map_mul, mul_smul,
      ← IsScalarTower.algebraMap_apply (A ⧸ I) (Ash ⧸ I.map (algebraMap A Ash))
        (Csh ⧸ J.map (algebraMap C Csh)) a]
    rfl
  exact (Module.Flat.quotSMul_baseChange_iff_of_faithfullyFlat Csh J M).symm.trans
    (Module.Flat.quotient_iff_of_isHenselization L hI _)

/-- **Flatness is invariant under transport of the base along a ring isomorphism.** The
isomorphism exhibits the target as the localization of the source at the trivial submonoid, over
which flatness is insensitive to the base. The two rings may lie in different universes. -/
public theorem Module.Flat.compHom_ringEquiv_iff_of_tower {R T : Type*} [CommRing R] [CommRing T]
    (e : R ≃+* T) (M : Type*) [AddCommGroup M] [Module T M] :
    letI : Module R M := Module.compHom M e.toRingHom
    (Module.Flat R M ↔ Module.Flat T M) := by
  let : Algebra R T := e.toRingHom.toAlgebra
  let : Module R M := Module.compHom M e.toRingHom
  let : IsScalarTower R T M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsLocalization (⊥ : Submonoid R) T :=
    IsLocalization.of_le_isUnit_of_bijective (by
      rintro x ⟨r, hr, rfl⟩
      have hr' : r = 1 := hr
      simp [hr']) e.bijective
  exact (Module.flat_iff_of_isLocalization T (⊥ : Submonoid R) M).symm

/-- **Flatness over a quotient is invariant under transport of the base along a ring
isomorphism.** For `e : A ≃+* A'` carrying an ideal `I` to `J`, flatness of a module over
`A' ⧸ J` and over `A ⧸ I`, along the induced isomorphism of quotients, are the same condition.
The ideal of the target is taken as a separate argument with the equation identifying it, so that
the statement applies at whichever presentation of `J` the caller has; `A` and `A'` may lie in
different universes. -/
public theorem Module.Flat.quotient_ringEquiv_iff {A A' : Type*} [CommRing A] [CommRing A']
    (e : A ≃+* A') (I : Ideal A) (J : Ideal A') (hJ : J = I.map (e : A →+* A'))
    (N : Type*) [AddCommGroup N] [Module (A' ⧸ J) N] :
    letI : Module (A ⧸ I) N :=
      Module.compHom N (Ideal.quotientEquiv I J e hJ).toRingHom
    (Module.Flat (A ⧸ I) N ↔ Module.Flat (A' ⧸ J) N) :=
  Module.Flat.compHom_ringEquiv_iff_of_tower (Ideal.quotientEquiv I J e hJ) N

end
