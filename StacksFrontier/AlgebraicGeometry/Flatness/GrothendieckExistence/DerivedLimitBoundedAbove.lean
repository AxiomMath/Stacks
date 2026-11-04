module

public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.DerivedLimitObject
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeDevissage
public import StacksFrontier.AlgebraicGeometry.ThickeningVanishingAscent.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The object of Stacks 0DIC is bounded above

In Situation [Stacks, Tag 0DIB] let `K = DQ_X(R lim_{D(𝒪_X)} Kₙ)` be the object
`AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.limitObject` of
`StacksFrontier/AlgebraicGeometry/Flatness/GrothendieckExistence/DerivedLimitObject.lean`. This file
proves [Stacks, Tag 0DIC]: `K` lies in `D^-_QCoh(𝒪_X)`.

## Main results

* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.isLE_K_succ_of_isLE` — an
  upper bound on `Kₙ` is one on `Kₙ₊₁`.
* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.exists_forall_isLE` — the
  `Kₙ` are bounded above independently of `n`.
* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.exists_isLE_limitObject` —
  `K` is bounded above.
* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.limitObject_spec` —
  **[Stacks, Tag 0DIC]**: the displayed equality, and `K` in `D^-_QCoh(𝒪_X)`.

## The shape of the proof

This is the last paragraph of the source's proof. Each `Kₙ` is pseudo-coherent on the
quasi-compact scheme `Xₙ`, hence bounded above. Suppose `a` bounds `Kₙ` and `m > a` bounds
`Kₙ₊₁`. The top cohomology sheaf `H^m(Kₙ₊₁)` is of finite type ([Stacks, Tag 08DN]), and its
pullback along `tₙ : Xₙ → Xₙ₊₁` is `H^m(Ltₙ^* Kₙ₊₁) = H^m(Kₙ) = 0`, the derived pullback of an
object of `D^{≤ m}` having `tₙ^* H^m` as its degree-`m` cohomology. Since `tₙ` is a surjective
closed immersion, Nakayama's lemma ([Stacks, Tag 00DV]) on the stalks forces `H^m(Kₙ₊₁) = 0`, so
`m - 1` bounds `Kₙ₊₁`; descending, `a` bounds `Kₙ₊₁`. By induction `a` bounds every `Kₙ`, and
`DerivedExistenceSituation.exists_isLE_coheratorLimit_of_forall_isLE` concludes.

## Implementation notes

The source writes "suppose `aₙ` is maximal with `H^{aₙ}(Kₙ) ≠ 0`" and shows `aₙ = aₙ₋₁`; the
argument here shows instead that a bound for `Kₙ` is a bound for `Kₙ₊₁`, which is the same
Nakayama step and needs no case distinction for the objects `Kₙ` that vanish.

The objects `Kₙ` live at `CategoryTheory.HasDerivedCategory.standard`, which is named explicitly
at each spelling of the category of `𝒪_{Xₙ}`-modules it is needed at.

## References

* [Stacks Project, Tag 0DIC](https://stacks.math.columbia.edu/tag/0DIC)
* [Stacks Project, Tag 0DIB](https://stacks.math.columbia.edu/tag/0DIB)
* [Stacks Project, Tag 08DN](https://stacks.math.columbia.edu/tag/08DN)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open RingedSpaceModuleAdjunction Stacks.Duality.Coherator

universe u

namespace AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation

variable (S : DerivedExistenceSituation.{u})

/-- `Kₙ` is bounded above, being pseudo-coherent on the quasi-compact scheme `Xₙ`. -/
private theorem exists_isLE_K (n : ℕ) : ∃ B : ℤ,
    letI := HasDerivedCategory.standard
      (StrictlyPerfect.OXMod.{u, u, u} (schemeAt S.system S.X n).toRingedSpace)
    (S.K n).IsLE B := by
  let := HasDerivedCategory.standard
    (StrictlyPerfect.OXMod.{u, u, u} (schemeAt S.system S.X n).toRingedSpace)
  obtain ⟨E, hE, e⟩ := S.pseudoCoherent n
  exact exists_isLE_of_isPseudoCoherentFrom (Y := schemeAt S.system S.X n)
    (S.K n) 0 ⟨E, hE 0, e⟩

/-- **An upper bound on `Kₙ` is one on `Kₙ₊₁`.** If `Kₙ₊₁` is bounded by `m > a` while `a` bounds
`Kₙ`, then `H^m(Kₙ₊₁)` is of finite type ([Stacks, Tag 08DN] part (1)) and its pullback along the
surjective closed immersion `tₙ` is `H^m(Ltₙ^* Kₙ₊₁) ≅ H^m(Kₙ) = 0`, so it vanishes by Nakayama's
lemma on the stalks; descending from a bound of the pseudo-coherent `Kₙ₊₁` gives the claim. -/
theorem isLE_K_succ_of_isLE (n : ℕ) (a : ℤ)
    (h :
      letI := HasDerivedCategory.standard
        (StrictlyPerfect.OXMod.{u, u, u} (schemeAt S.system S.X n).toRingedSpace)
      (S.K n).IsLE a) :
    letI := HasDerivedCategory.standard
      (StrictlyPerfect.OXMod.{u, u, u} (schemeAt S.system S.X (n + 1)).toRingedSpace)
    (S.K (n + 1)).IsLE a := by
  let := HasDerivedCategory.standard
    (StrictlyPerfect.OXMod.{u, u, u} (schemeAt S.system S.X n).toRingedSpace)
  let := HasDerivedCategory.standard
    (StrictlyPerfect.OXMod.{u, u, u} (schemeAt S.system S.X (n + 1)).toRingedSpace)
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (structureSheafRing (schemeAt S.system S.X n).toRingedSpace))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (structureSheafRing (schemeAt S.system S.X (n + 1)).toRingedSpace))
  obtain ⟨E, hE, e⟩ := S.pseudoCoherent (n + 1)
  obtain ⟨B, hB⟩ := S.exists_isLE_K (n + 1)
  have step : ∀ m : ℤ, a < m → (S.K (n + 1)).IsLE m → (S.K (n + 1)).IsLE (m - 1) := by
    intro m hm hKm
    have habove : ∀ i : ℤ, m < i →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj (S.K (n + 1))) := fun i hi =>
      @DerivedCategory.isZero_of_isLE _ _ _ _ (S.K (n + 1)) m i hi hKm
    have hft := RingedSpace.isFiniteType_homology_of_isPseudoCoherentFrom (S.K (n + 1)) m
      ⟨E, hE m, e⟩ habove
    have htop : IsZero ((Scheme.Modules.pullback (S.transitionScheme n)).obj
        ((DerivedCategory.homologyFunctor
          (StrictlyPerfect.OXMod.{u, u, u} (schemeAt S.system S.X (n + 1)).toRingedSpace) m).obj
            (S.K (n + 1)))) :=
      (@DerivedCategory.isZero_of_isLE _ _ _ _ (S.K n) a m hm h).of_iso
        ((Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback
          (S.transitionScheme n).toLRSHom.toShHom (S.K (n + 1)) m hKm).symm ≪≫
          (DerivedCategory.homologyFunctor
            (StrictlyPerfect.OXMod.{u, u, u} (schemeAt S.system S.X n).toRingedSpace) m).mapIso
              (@asIso _ _ _ _ (S.φ n) (S.φ_isIso n)))
    have hzero :=
      Stacks.AlgebraicGeometry.ThickeningVanishingAscent.isZero_of_isZero_pullback_of_surjective
        (S.transitionScheme n) (S.surjective_transitionScheme n) _ hft htop
    refine (DerivedCategory.isLE_iff _ (m - 1)).2 fun i hi => ?_
    rcases eq_or_lt_of_le (show m ≤ i by omega) with h' | h'
    · exact h' ▸ hzero
    · exact habove i h'
  have hdown : ∀ k : ℕ, (S.K (n + 1)).IsLE (a + k) → (S.K (n + 1)).IsLE a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => exact fun h => ih (by convert step _ (by omega) h using 2; omega)
  exact hdown (B - a).toNat
    (@Triangulated.TStructure.isLE_of_le _ _ _ _ _ _ _ DerivedCategory.TStructure.t
      _ B _ (by omega) hB)

/-- **The `Kₙ` are bounded above independently of `n`.** `K₀` is bounded above, being
pseudo-coherent on the quasi-compact scheme `X₀`, and a bound on `Kₙ` is one on `Kₙ₊₁`
(`AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.isLE_K_succ_of_isLE`). -/
theorem exists_forall_isLE : ∃ a : ℤ, ∀ n : ℕ,
    letI := HasDerivedCategory.standard
      (StrictlyPerfect.OXMod.{u, u, u} (schemeAt S.system S.X n).toRingedSpace)
    (S.K n).IsLE a := by
  obtain ⟨a, ha⟩ := S.exists_isLE_K 0
  refine ⟨a, fun n => ?_⟩
  induction n with
  | zero => exact ha
  | succ n ih => exact S.isLE_K_succ_of_isLE n a ih

/-- **`DQ_X(R lim Kₙ)` is bounded above**, at the locally small model. -/
theorem exists_isLE_coheratorLimit :
    ∃ c : ℤ, ((quasiCoherentι S.X.left).obj S.coheratorLimit).IsLE c :=
  let ⟨a, ha⟩ := S.exists_forall_isLE
  S.exists_isLE_coheratorLimit_of_forall_isLE a ha

/-- **The object `K` of [Stacks, Tag 0DIC] is bounded above**, at the model of the situation. -/
theorem exists_isLE_limitObject :
    ∃ c : ℤ,
      letI := HasDerivedCategory.standard
        (StrictlyPerfect.OXMod.{u, u, u} S.X.left.toRingedSpace)
      S.limitObject.IsLE c :=
  let ⟨c, hc⟩ := S.exists_isLE_coheratorLimit
  ⟨c, S.isLE_limitObject_of_isLE c hc⟩

/-- **Stacks Project, Tag 0DIC.** In Situation [Stacks, Tag 0DIB] consider
`K = R lim_{D_QCoh(𝒪_X)}(Kₙ) = DQ_X(R lim_{D(𝒪_X)} Kₙ)`. Then `K` is in `D^-_QCoh(𝒪_X)`.

Here `R lim_{D(𝒪_X)} Kₙ` is a chosen derived limit
(`AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.derivedLimit`) of the system
`(R(iₙ)_* Kₙ)` whose transition maps are the adjoints of the `φₙ`, and `DQ_X` is the coherator of
[Stacks, Tag 0CR0]. The three conjuncts are:

* the displayed equality: `DQ_X(R lim_{D(𝒪_X)} Kₙ)` is a derived limit `R lim_{D_QCoh(𝒪_X)}(Kₙ)`
  of the system in `D_QCoh(𝒪_X)`;
* `K`, read at the model of the situation
  (`AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.limitObject`), has
  quasi-coherent cohomology sheaves;
* `K` is bounded above.

The proof is the source's, see the module documentation and that of
`StacksFrontier/AlgebraicGeometry/Flatness/GrothendieckExistence/DerivedLimitObject.lean`. -/
@[stacks 0DIC]
theorem limitObject_spec :
    (∃ _ : HasProduct fun n : ℕ => S.qcohTower.obj (op n),
      IsDerivedLimit S.qcohTower S.coheratorLimit) ∧
    letI := HasDerivedCategory.standard
      (StrictlyPerfect.OXMod.{u, u, u} S.X.left.toRingedSpace)
    (∀ j : ℤ, ((DerivedCategory.homologyFunctor _ j).obj S.limitObject).IsQuasicoherent) ∧
      ∃ c : ℤ, S.limitObject.IsLE c :=
  ⟨S.isDerivedLimit_coheratorLimit, S.isQuasicoherent_homology_limitObject,
    S.exists_isLE_limitObject⟩

end AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation

end
