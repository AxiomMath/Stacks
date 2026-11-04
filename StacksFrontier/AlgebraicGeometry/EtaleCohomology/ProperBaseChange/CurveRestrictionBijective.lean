module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CurveRestrictionInduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.PrimaryDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ProperScalarExtension
public import StacksFrontier.AlgebraicGeometry.ClosedSupportFiniteness.Basic

/-!
# Restriction to a scalar extension of a proper curve is bijective on torsion coefficients

Let `k ⊆ k'` be separably closed fields. Granted

* injectivity of restriction to the scalar extension, in every degree, for every abelian sheaf on
  every proper `k`-scheme of dimension at most one, and
* the base case: surjectivity in every degree for `ℤ/ℓ`, `ℓ` prime, on every proper normal
  irreducible `k`-scheme of dimension at most one,

restriction is bijective in every degree for every torsion abelian sheaf on every proper `k`-scheme
of dimension at most one. For sheaves killed by a prime this is the induction of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CurveRestrictionInduction`; a sheaf
killed by a positive integer is reached by the primary dévissage
(`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_of_nsmul_id_eq_zero`), and a
torsion sheaf is the filtered colimit of its torsion filtration `F[n!]`, along which cohomology on
a quasi-compact quasi-separated scheme commutes.

Over algebraically closed fields the base case is split by the characteristic: for `ℓ` the
characteristic it is Stacks 0A3P (2), unconditional for every proper scheme; for a
zero-dimensional piece it is the finite case; what remains is `ℤ/ℓ` with `ℓ` invertible on a proper
normal curve.

## Main results

In the namespace `Stacks.EtaleCohomology`:

* `bijective_etaleCohomologyRestrictionMap_of_torsion_of_curve`
* `bijective_etaleCohomologyRestrictionMap_of_torsion_of_curve_of_isAlgClosed`
  — the same over algebraically closed fields, with the base case asked only for `ℓ` invertible
  in `k` and curves of dimension exactly one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k']

/-- **Bijectivity on sheaves killed by a prime from injectivity and the base case.** -/
theorem bijective_etaleCohomologyRestrictionMap_of_nsmul_prime_of_curve
    [IsSepClosed k] [IsSepClosed k']
    (hinj : ∀ (Y : Scheme.{u}) (πY : Y ⟶ Spec (.of k)), IsProper πY →
      topologicalKrullDim Y ≤ 1 → ∀ (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
        (p : ℕ), Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
          (scalarExtensionFst k k' πY) G p))
    (hbase : ∀ ℓ : ℕ, ℓ.Prime → ∀ (q : ℕ) (C : Scheme.{u}) (πC : C ⟶ Spec (.of k)),
      IsProper πC → IsNormal C → IrreducibleSpace C → topologicalKrullDim C ≤ 1 →
      Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (scalarExtensionFst k k' πC) ((constantSheaf C.smallEtaleTopology
          AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))) q))
    {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsProper π] (hdim : topologicalKrullDim X ≤ 1)
    (p : ℕ) (hp : p.Prime) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : p • 𝟙 G = 0) (r : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
      (scalarExtensionFst k k' π) G r) := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨hinj X π inferInstance hdim G r, ?_⟩
  exact surjective_etaleCohomologyRestrictionMap_of_zsmul_id_eq_zero_of_curve k k' p
    (hbase p hp) hinj r X π hdim G (by rw [natCast_zsmul]; exact hG)

/-- **Surjectivity on a torsion sheaf from surjectivity on the sheaves killed by a positive
integer**, for a proper scheme over `k`: a torsion sheaf is the filtered colimit of its torsion
filtration `F[n!]`. -/
theorem surjective_etaleCohomologyRestrictionMap_of_torsion_of_nsmul
    {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsProper π]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (q : ℕ)
    (h : ∀ n : ℕ, 0 < n → ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      n • 𝟙 G = 0 → Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (scalarExtensionFst k k' π) G q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' π)
      F q) := by
  let K := Stacks.Torsion.torsionFiltration.{u + 1, u, u + 1} X.smallEtaleTopology F
  let c : Cocone K :=
    Cocone.mk F (Stacks.Torsion.torsionFiltrationι.{u + 1, u, u + 1} X.smallEtaleTopology F)
  have : IsIso ((colimit.isColimit K).desc c) := by
    have := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
    exact Stacks.Torsion.isIso_torsionFiltrationDesc X.smallEtaleTopology F hF
  have hc : IsColimit c := IsColimit.ofPointIso (colimit.isColimit K)
  have hsnd : IsProper (pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback π _) ‹_›
  have : CompactSpace (scalarExtension k k' π) :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
  have : QuasiSeparatedSpace (scalarExtension k k' π) :=
    quasiSeparatedSpace_of_quasiSeparated
      (pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
  exact surjective_etaleCohomologyRestrictionMap_of_isColimit_of_qcqs X (scalarExtensionFst k k' π)
    hc q fun i => h _ (Nat.factorial_pos i.down) _ (nsmul_id_kernel_eq_zero F _)

/-- **Bijectivity on torsion sheaves from injectivity and the base case.** Let `k ⊆ k'` be
separably closed. If restriction to the scalar extension is injective in every degree for every
abelian sheaf on every proper `k`-scheme of dimension at most one, and surjective in every degree
for `ℤ/ℓ` (`ℓ` prime) on every proper normal irreducible `k`-scheme of dimension at most one, then
it is bijective in every degree for every torsion abelian sheaf on every proper `k`-scheme of
dimension at most one. -/
theorem bijective_etaleCohomologyRestrictionMap_of_torsion_of_curve
    [IsSepClosed k] [IsSepClosed k']
    (hinj : ∀ (Y : Scheme.{u}) (πY : Y ⟶ Spec (.of k)), IsProper πY →
      topologicalKrullDim Y ≤ 1 → ∀ (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
        (p : ℕ), Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
          (scalarExtensionFst k k' πY) G p))
    (hbase : ∀ ℓ : ℕ, ℓ.Prime → ∀ (q : ℕ) (C : Scheme.{u}) (πC : C ⟶ Spec (.of k)),
      IsProper πC → IsNormal C → IrreducibleSpace C → topologicalKrullDim C ≤ 1 →
      Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (scalarExtensionFst k k' πC) ((constantSheaf C.smallEtaleTopology
          AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))) q))
    {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsProper π] (hdim : topologicalKrullDim X ≤ 1)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' π)
      F q) := by
  refine ⟨hinj X π inferInstance hdim F q, ?_⟩
  refine surjective_etaleCohomologyRestrictionMap_of_torsion_of_nsmul k k' π F hF q
    fun n hn G hG => ?_
  have hpr := bijective_etaleCohomologyRestrictionMap_of_nsmul_prime_of_curve k k' hinj hbase π
    hdim
  exact (etaleCohomologyRestrictionMap_bijective_of_nsmul_id_eq_zero
    (scalarExtensionFst k k' π) hpr n hn.ne' G hG q).2

/-- **Bijectivity on torsion sheaves over algebraically closed fields, from injectivity and the
base case for `ℓ` invertible on curves.** Let `k ⊆ k'` be algebraically closed. Granted
injectivity of restriction in every degree for every abelian sheaf on every proper `k`-scheme of
dimension at most one, and surjectivity in every degree for `ℤ/ℓ` on every proper normal
irreducible `k`-scheme of dimension one, for every prime `ℓ` invertible in `k`, restriction is
bijective in every degree for every torsion abelian sheaf on every proper `k`-scheme of dimension
at most one. The base case for `ℓ` the characteristic is Stacks 0A3P (2), and for a
zero-dimensional piece it is the finite case. -/
theorem bijective_etaleCohomologyRestrictionMap_of_torsion_of_curve_of_isAlgClosed
    [IsAlgClosed k] [IsAlgClosed k']
    (hinj : ∀ (Y : Scheme.{u}) (πY : Y ⟶ Spec (.of k)), IsProper πY →
      topologicalKrullDim Y ≤ 1 → ∀ (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
        (p : ℕ), Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
          (scalarExtensionFst k k' πY) G p))
    (hbase : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : k) ≠ 0 → ∀ (q : ℕ) (C : Scheme.{u})
      (πC : C ⟶ Spec (.of k)), IsProper πC → IsNormal C → IrreducibleSpace C →
      topologicalKrullDim C = 1 →
      Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (scalarExtensionFst k k' πC) ((constantSheaf C.smallEtaleTopology
          AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))) q))
    {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsProper π] (hdim : topologicalKrullDim X ≤ 1)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' π)
      F q) := by
  refine bijective_etaleCohomologyRestrictionMap_of_torsion_of_curve k k' hinj
    (fun ℓ hℓ r C πC hC hn hirr hCdim => ?_) π hdim F hF q
  have : IsProper πC := hC
  by_cases hchar : (ℓ : k) = 0
  · have : CharP k ℓ := (CharP.charP_iff_prime_eq_zero hℓ).2 hchar
    exact (Stacks.ArtinSchreier.bijective_etaleCohomologyRestrictionMap_constantZMod.{u + 1, u} k k'
      πC hℓ.pos r).2
  by_cases h0 : topologicalKrullDim C ≤ 0
  · have : IsFinite πC := isFinite_of_isProper_of_topologicalKrullDim_le_zero πC h0
    exact (etaleCohomologyRestrictionMap_bijective_of_isFinite_of_isSepClosed k k' πC _ r).2
  · refine hbase ℓ hℓ hchar r C πC hC hn hirr ?_
    clear hbase hinj
    revert hCdim h0
    generalize topologicalKrullDim C = x
    intro hCdim h0
    induction x using WithBot.recBotCoe with
    | bot => exact absurd bot_le h0
    | coe m =>
      have h1 : m ≤ 1 := by exact_mod_cast hCdim
      have h0' : ¬ m ≤ 0 := fun h => h0 (by exact_mod_cast h)
      have : m = 1 := le_antisymm h1 (ENat.one_le_iff_ne_zero.2 fun h => h0' h.le)
      rw [this]; rfl

end Stacks.EtaleCohomology

end
