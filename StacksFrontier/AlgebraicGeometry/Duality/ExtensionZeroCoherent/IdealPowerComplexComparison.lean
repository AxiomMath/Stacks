module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.IdealPowerComplex

/-!
# Comparing the ideal-power subcomplexes of two nested ideal sheaves

Let `X` be a scheme, let `𝓘' ⊆ 𝓘` be quasi-coherent sheaves of ideals on `X` and let `𝓕^•` be a
cochain complex of sheaves of modules on `X`. Then `(𝓘')^n 𝓕^• ⊆ 𝓘^n 𝓕^•` for every `n`, and the
resulting inclusions

`K'_n = (𝓘')^n 𝓕^• ⟶ 𝓘^n 𝓕^• = K_n`

are compatible with the inclusions into `𝓕^•` and with the transitions of the two ideal-power
filtrations.

This is the explicit construction in [Stacks, Tag 0G4Y]. There `X ⊃ U ⊃ U'` are open subschemes
of a Noetherian scheme, `𝓕^•` is a bounded complex of coherent modules whose restriction to `U`
represents `K`, and `𝓘`, `𝓘'` cut out `X ∖ U`, `X ∖ U'`; the source first replaces `𝓘` by
`𝓘 + 𝓘'`, which is legitimate because that does not change the vanishing locus
(`Stacks.AlgebraicGeometry.IdealPower.support_sup_eq_left`), and then takes the maps
`K'_n ⟶ K_n` induced by `(𝓘')^n ⊆ 𝓘^n`.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultipleMapOfIdealLE`: the inclusion
  `𝓘'^n • M ⟶ 𝓘^n • M` for `𝓘' ≤ 𝓘`.
* `AlgebraicGeometry.IdealPowerComplexSystem.compareFun`: its component on the term in one
  degree of a presentation of the ideal-power subcomplexes.
* `AlgebraicGeometry.IdealPowerComplexSystem.compareHom`: the map of complexes
  `(𝓘')^n 𝓕^• ⟶ 𝓘^n 𝓕^•`.

## Main results

* `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_mono`: `𝓘'^n • M ≤ 𝓘^n • M` for
  `𝓘' ≤ 𝓘`.
* `Stacks.AlgebraicGeometry.IdealPower.support_sup_eq_left`: adding a sheaf of ideals with a
  larger vanishing locus does not change the vanishing locus, which is what lets the source
  assume `𝓘' ⊆ 𝓘`.
* `AlgebraicGeometry.IdealPowerComplexSystem.compareHom_comp_inclusion`: the comparison map
  `K'_n ⟶ K_n`, followed by the inclusion of `K_n` into `𝓕^•`, is the inclusion of `K'_n`; this
  characterises it, because the inclusions are termwise monomorphisms.
* `AlgebraicGeometry.IdealPowerComplexSystem.compareHom_comp_transition`: the comparison maps
  commute with the transitions of the two filtrations, so they form a map of inverse systems.

## Implementation notes

A term of `AlgebraicGeometry.IdealPowerComplexSystem` identifies its terms with the ideal-power
multiples `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple` and its inclusions with the
inclusions of those submodules, so the comparison map is built from
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultipleMapOfIdealLE` through those
identifications. Every compatibility is then proved by cancelling the inclusion into `𝓕^•`,
which is legitimate degreewise by
`AlgebraicGeometry.IdealPowerComplexSystem.cancel_inclusion_f`.

## References

* [Stacks Project, Tag 0G4Y](https://stacks.math.columbia.edu/tag/0G4Y)
* [Stacks Project, Tag 0G4R](https://stacks.math.columbia.edu/tag/0G4R)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.IdealPower

variable {X : Scheme.{u}}

/-- Replacing a quasi-coherent sheaf of ideals by its sum with one whose vanishing locus is
larger does not change the vanishing locus. In [Stacks, Tag 0G4Y] this is the step that lets one
assume `𝓘' ⊆ 𝓘`: there `V(𝓘) = X ∖ U` and `V(𝓘') = X ∖ U'` with `U' ⊆ U`, so
`V(𝓘 + 𝓘') = V(𝓘)`, while `𝓘' ≤ 𝓘 + 𝓘'`. -/
@[stacks 0G4Y "the reduction to 𝓘' ⊆ 𝓘 of the explicit construction: replacing 𝓘 by 𝓘 + 𝓘' \
leaves the vanishing locus unchanged"]
public lemma support_sup_eq_left {I I' : X.IdealSheafData} (h : I.support ≤ I'.support) :
    (I ⊔ I').support = I.support := by
  rw [Scheme.IdealSheafData.support_sup]
  exact inf_eq_left.mpr h

/-- The ideal-power multiple is monotone in the ideal: `𝓘'^n • M ≤ 𝓘^n • M` for `𝓘' ≤ 𝓘`. -/
public lemma idealPowerMultiple_mono {I J : X.IdealSheafData} (h : I ≤ J) (n : ℕ)
    (M : X.Modules) : idealPowerMultiple I n M ≤ idealPowerMultiple J n M := by
  rw [idealPowerMultiple_le_iff]
  intro U
  refine (Submodule.smul_mono_left (pow_le_pow_left' ?_ n)).trans
    (le_idealPowerMultiple_obj J n M U)
  exact Scheme.IdealSheafData.le_def.mp h U

/-- The inclusion `𝓘'^n • M ⟶ 𝓘^n • M` of sheaves of modules, for `𝓘' ≤ 𝓘`. -/
public def idealPowerMultipleMapOfIdealLE {I J : X.IdealSheafData} (h : I ≤ J) (n : ℕ)
    (M : X.Modules) :
    (idealPowerMultiple I n M).toSheafOfModules ⟶
      (idealPowerMultiple J n M).toSheafOfModules :=
  SheafOfModules.Submodule.homOfLE (idealPowerMultiple_mono h n M)

/-- The inclusion `𝓘'^n • M ⟶ 𝓘^n • M`, followed by the inclusion of `𝓘^n • M` into `M`, is the
inclusion of `𝓘'^n • M` into `M`. -/
@[simp]
public lemma idealPowerMultipleMapOfIdealLE_comp_ι {I J : X.IdealSheafData} (h : I ≤ J) (n : ℕ)
    (M : X.Modules) :
    idealPowerMultipleMapOfIdealLE h n M ≫ (idealPowerMultiple J n M).ι =
      (idealPowerMultiple I n M).ι :=
  SheafOfModules.Submodule.homOfLE_ι _

end Stacks.AlgebraicGeometry.IdealPower

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.IdealPower

variable {X : Scheme.{u}} {I J : X.IdealSheafData} {F : CochainComplex X.Modules ℤ}

namespace IdealPowerComplexSystem

/-- A morphism into the term of `𝓘^n 𝓕^•` in one degree is determined by its composite with the
inclusion into `𝓕^•`: that inclusion is the inclusion of a subsheaf, read through an
isomorphism. -/
public lemma cancel_inclusion_f (S : IdealPowerComplexSystem J F) (n : ℕ) (i : ℤ)
    {A : X.Modules} (f g : A ⟶ (S.complex n).X i)
    (hfg : f ≫ (S.inclusion n).f i = g ≫ (S.inclusion n).f i) : f = g :=
  have key : (f ≫ (S.termIso n i).hom) ≫ (idealPowerMultiple J n (F.X i)).ι =
      (g ≫ (S.termIso n i).hom) ≫ (idealPowerMultiple J n (F.X i)).ι :=
    calc (f ≫ (S.termIso n i).hom) ≫ (idealPowerMultiple J n (F.X i)).ι
        = f ≫ (S.termIso n i).hom ≫ (idealPowerMultiple J n (F.X i)).ι :=
          Category.assoc _ _ _
      _ = f ≫ (S.inclusion n).f i := congrArg (fun t => f ≫ t) (S.include_f n i)
      _ = g ≫ (S.inclusion n).f i := hfg
      _ = g ≫ (S.termIso n i).hom ≫ (idealPowerMultiple J n (F.X i)).ι :=
          congrArg (fun t => g ≫ t) (S.include_f n i).symm
      _ = (g ≫ (S.termIso n i).hom) ≫ (idealPowerMultiple J n (F.X i)).ι :=
          (Category.assoc _ _ _).symm
  (Iso.cancel_iso_hom_right _ _ (S.termIso n i)).mp
    (cancel_sheafSubmodule_ι (idealPowerMultiple J n (F.X i)) _ _ key)

/-- The term in degree `i` of the comparison map `(𝓘')^n 𝓕^• ⟶ 𝓘^n 𝓕^•`: the inclusion
`(𝓘')^n • 𝓕^i ⟶ 𝓘^n • 𝓕^i`, read through the identifications of the two presentations. -/
public def compareFun (S' : IdealPowerComplexSystem I F) (S : IdealPowerComplexSystem J F)
    (h : I ≤ J) (n : ℕ) (i : ℤ) : (S'.complex n).X i ⟶ (S.complex n).X i :=
  (S'.termIso n i).hom ≫ idealPowerMultipleMapOfIdealLE h n (F.X i) ≫ (S.termIso n i).inv

/-- The comparison map in degree `i`, followed by the inclusion of `𝓘^n 𝓕^•` into `𝓕^•`, is the
inclusion of `(𝓘')^n 𝓕^•`. -/
public lemma compareFun_comp_inclusion (S' : IdealPowerComplexSystem I F)
    (S : IdealPowerComplexSystem J F) (h : I ≤ J) (n : ℕ) (i : ℤ) :
    S'.compareFun S h n i ≫ (S.inclusion n).f i = (S'.inclusion n).f i :=
  have hJ : (S.termIso n i).inv ≫ (S.inclusion n).f i =
      (idealPowerMultiple J n (F.X i)).ι :=
    (congrArg (fun t => (S.termIso n i).inv ≫ t) (S.include_f n i).symm).trans
      (Iso.inv_hom_id_assoc (S.termIso n i) _)
  calc S'.compareFun S h n i ≫ (S.inclusion n).f i
      = ((S'.termIso n i).hom ≫ idealPowerMultipleMapOfIdealLE h n (F.X i) ≫
          (S.termIso n i).inv) ≫ (S.inclusion n).f i := rfl
    _ = (S'.termIso n i).hom ≫ (idealPowerMultipleMapOfIdealLE h n (F.X i) ≫
          (S.termIso n i).inv) ≫ (S.inclusion n).f i := Category.assoc _ _ _
    _ = (S'.termIso n i).hom ≫ idealPowerMultipleMapOfIdealLE h n (F.X i) ≫
          (S.termIso n i).inv ≫ (S.inclusion n).f i :=
        congrArg (fun t => (S'.termIso n i).hom ≫ t) (Category.assoc _ _ _)
    _ = (S'.termIso n i).hom ≫ (idealPowerMultiple I n (F.X i)).ι :=
        congrArg (fun t => (S'.termIso n i).hom ≫ t)
          ((congrArg (fun u => idealPowerMultipleMapOfIdealLE h n (F.X i) ≫ u) hJ).trans
            (idealPowerMultipleMapOfIdealLE_comp_ι h n (F.X i)))
    _ = (S'.inclusion n).f i := S'.include_f n i

/-- **The maps `K'_n ⟶ K_n` of the explicit construction in [Stacks, Tag 0G4Y].** For
`𝓘' ≤ 𝓘` the inclusions `(𝓘')^n • 𝓕^i ⊆ 𝓘^n • 𝓕^i` assemble into a map of complexes

`(𝓘')^n 𝓕^• ⟶ 𝓘^n 𝓕^•`.

The source writes `K'_n = (𝓘')^n 𝓕^•` and `K_n = 𝓘^n 𝓕^•` and describes its canonical map
`Rj'_!(K|_{U'}) ⟶ Rj_! K` as being given by these maps. -/
@[stacks 0G4Y "the maps K'_n = (𝓘')^n 𝓕^• ⟶ 𝓘^n 𝓕^• = K_n of the explicit construction, induced \
by the inclusions (𝓘')^n ⊆ 𝓘^n"]
public def compareHom (S' : IdealPowerComplexSystem I F) (S : IdealPowerComplexSystem J F)
    (h : I ≤ J) (n : ℕ) : S'.complex n ⟶ S.complex n where
  f i := S'.compareFun S h n i
  comm' i j _ := by
    apply S.cancel_inclusion_f n j
    calc (S'.compareFun S h n i ≫ (S.complex n).d i j) ≫ (S.inclusion n).f j
        = S'.compareFun S h n i ≫ (S.complex n).d i j ≫ (S.inclusion n).f j :=
          Category.assoc _ _ _
      _ = S'.compareFun S h n i ≫ (S.inclusion n).f i ≫ F.d i j :=
          congrArg (fun t => S'.compareFun S h n i ≫ t) ((S.inclusion n).comm i j).symm
      _ = (S'.compareFun S h n i ≫ (S.inclusion n).f i) ≫ F.d i j :=
          (Category.assoc _ _ _).symm
      _ = (S'.inclusion n).f i ≫ F.d i j :=
          congrArg (fun t => t ≫ F.d i j) (S'.compareFun_comp_inclusion S h n i)
      _ = (S'.complex n).d i j ≫ (S'.inclusion n).f j := (S'.inclusion n).comm i j
      _ = (S'.complex n).d i j ≫ S'.compareFun S h n j ≫ (S.inclusion n).f j :=
          congrArg (fun t => (S'.complex n).d i j ≫ t)
            (S'.compareFun_comp_inclusion S h n j).symm
      _ = ((S'.complex n).d i j ≫ S'.compareFun S h n j) ≫ (S.inclusion n).f j :=
          (Category.assoc _ _ _).symm

/-- **The comparison map of [Stacks, Tag 0G4Y] is the inclusion, read inside `𝓕^•`.** Composing
`K'_n ⟶ K_n` with the inclusion of `K_n` into `𝓕^•` gives the inclusion of `K'_n`. Since the
inclusions are termwise monomorphisms, this characterises the comparison map. -/
@[stacks 0G4Y "the maps K'_n ⟶ K_n of the explicit construction are the inclusions read inside \
𝓕^•, which is what pins them down"]
public lemma compareHom_comp_inclusion (S' : IdealPowerComplexSystem I F)
    (S : IdealPowerComplexSystem J F) (h : I ≤ J) (n : ℕ) :
    S'.compareHom S h n ≫ S.inclusion n = S'.inclusion n :=
  HomologicalComplex.Hom.ext (funext (S'.compareFun_comp_inclusion S h n))

/-- **The comparison maps of [Stacks, Tag 0G4Y] form a map of inverse systems.** They commute
with the transitions `K'_{n+1} ⟶ K'_n` and `K_{n+1} ⟶ K_n` of the two ideal-power
filtrations. -/
@[stacks 0G4Y "the maps K'_n ⟶ K_n of the explicit construction commute with the transitions, so \
they are a map of the inverse systems (K'_n) ⟶ (K_n)"]
public lemma compareHom_comp_transition (S' : IdealPowerComplexSystem I F)
    (S : IdealPowerComplexSystem J F) (h : I ≤ J) (n : ℕ) :
    S'.transition n ≫ S'.compareHom S h n = S'.compareHom S h (n + 1) ≫ S.transition n := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply S.cancel_inclusion_f n i
  calc (S'.transition n ≫ S'.compareHom S h n).f i ≫ (S.inclusion n).f i
      = (S'.transition n).f i ≫ S'.compareFun S h n i ≫ (S.inclusion n).f i :=
        Category.assoc _ _ _
    _ = (S'.transition n).f i ≫ (S'.inclusion n).f i :=
        congrArg (fun t => (S'.transition n).f i ≫ t) (S'.compareFun_comp_inclusion S h n i)
    _ = (S'.inclusion (n + 1)).f i :=
        congrArg (fun t : S'.complex (n + 1) ⟶ F => t.f i) (S'.transition_include n)
    _ = S'.compareFun S h (n + 1) i ≫ (S.inclusion (n + 1)).f i :=
        (S'.compareFun_comp_inclusion S h (n + 1) i).symm
    _ = S'.compareFun S h (n + 1) i ≫ (S.transition n).f i ≫ (S.inclusion n).f i :=
        congrArg (fun t => S'.compareFun S h (n + 1) i ≫ t)
          (congrArg (fun t : S.complex (n + 1) ⟶ F => t.f i) (S.transition_include n)).symm
    _ = (S'.compareHom S h (n + 1) ≫ S.transition n).f i ≫ (S.inclusion n).f i :=
        (Category.assoc _ _ _).symm

end IdealPowerComplexSystem

end AlgebraicGeometry

end
