module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.StrongAssertions
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ExtensionByZeroFiniteDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.GenericInduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.TraceDegree

/-!
# The reduction steps of Stacks Tag 03SD

Let `j : U ⟶ X` be an open immersion and `G` an abelian sheaf on `U` killed by a prime `ℓ`. The
proof of Tag 03SD chooses a finite étale `g : V ⟶ U` of degree prime to `ℓ` such that `g⁻¹ G` is a
successive extension of copies of `Z/ℓ` (Tag 0A3R), and a finite `π : Y ⟶ X` containing `V` as an
open `j' : V ⟶ Y` with `V = U ×_X Y` (Zariski's main theorem, Tag 05K0). Then:

* the trace (Tag 03SE) makes `G` a retract of `g_* g⁻¹ G` (up to an automorphism);
* `j_! g_* g⁻¹ G ≅ π_* j'_! g⁻¹ G` (Tag 0GJ1);
* the eight assertions pass to `π_*` (Tag 0A5D) and along extensions (Tag 0A5C), so they reduce to
  `j'_! Z/ℓ` on `Y`, which is Tag 0A3Q.

This file proves the formal part, for `Stacks.EtaleCohomology.StrongTorsionCurveAssertions`: given
the retraction, the filtration (as an induction principle) and the assertions for `j'_! L` on `Y`,
the assertions hold for `j_! G` on `X`.

## Main results

* `Stacks.EtaleCohomology.StrongTorsionCurveAssertions.extensionByZero_of_finiteCover`.
* `Stacks.EtaleCohomology.StrongTorsionCurveAssertions.extensionByZero_of_finiteEtaleCover`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

namespace StrongTorsionCurveAssertions

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k))
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] [IsNoetherian X]

/-- **The formal part of Stacks Tag 03SD.** Let `j : U ⟶ X` be an open immersion, `g : V ⟶ U`
finite, `π : Y ⟶ X` finite and `j' : V ⟶ Y` an open immersion with `V = U ×_X Y`. Let `G` be a
sheaf on `U` killed by a prime `ℓ` such that the unit `G ⟶ g_* g⁻¹ G` is split up to an
automorphism, and such that `g⁻¹ G` lies in every class of sheaves on `V` containing the zero
sheaves and `L`, closed under isomorphism and extensions. If the strong assertions hold for
`j'_! L` on `Y`, they hold for `j_! G` on `X`. -/
theorem extensionByZero_of_finiteCover {U V Y : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (g : V ⟶ U) [IsFinite g] (π : Y ⟶ X) [IsFinite π] (j' : V ⟶ Y) [IsOpenImmersion j']
    (sq : IsPullback j' g π j)
    [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})] [IsNoetherian Y]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (G : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hℓG : ℓ • 𝟙 G = 0)
    (hret : ∃ p : (etaleAbelianDirectImage.{u, u + 1} g).obj
        ((etaleAbelianInverseImage.{u, u + 1} g).obj G) ⟶ G,
      IsIso ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} g).unit.app G ≫ p))
    (L : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) (_hℓL : ℓ • 𝟙 L = 0)
    (hfilt : ∀ P : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop,
      (∀ H, IsZero H → P H) → (∀ H H', (H ≅ H') → P H → P H') →
      (∀ S : ShortComplex (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}),
        S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂) →
      P L → P ((etaleAbelianInverseImage.{u, u + 1} g).obj G))
    (hbase : StrongTorsionCurveAssertions (π ≫ fX) ((extensionByZero.{u, u + 1} j').obj L)) :
    StrongTorsionCurveAssertions fX ((extensionByZero.{u, u + 1} j).obj G) := by
  have hup : StrongTorsionCurveAssertions (π ≫ fX) ((extensionByZero.{u, u + 1} j').obj
      ((etaleAbelianInverseImage.{u, u + 1} g).obj G)) := by
    refine hfilt (fun H => StrongTorsionCurveAssertions (π ≫ fX)
        ((extensionByZero.{u, u + 1} j').obj H)) ?_ ?_ ?_ hbase
    · intro H hH
      exact of_isZero _ ((extensionByZero.{u, u + 1} j').map_isZero hH)
    · intro H H' e h
      exact of_iso _ ((extensionByZero.{u, u + 1} j').mapIso e) h
    · intro S hS h₁ h₃
      exact of_shortExact _ (hS.map_of_exact (extensionByZero.{u, u + 1} j')) h₁ h₃
  have hℓ' : ℓ • 𝟙 ((extensionByZero.{u, u + 1} j').obj
      ((etaleAbelianInverseImage.{u, u + 1} g).obj G)) = 0 :=
    TorsionCurveAssertions.nsmul_id_map_eq_zero _
      (TorsionCurveAssertions.nsmul_id_map_eq_zero _ hℓG)
  have hπ := of_directImage fX π hℓ hℓ' hup
  obtain ⟨e⟩ := nonempty_extensionByZero_directImage_iso π j j' g sq
    ((etaleAbelianInverseImage.{u, u + 1} g).obj G)
  have hjg := of_iso fX e.symm hπ
  obtain ⟨p, hp⟩ := hret
  set η := (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} g).unit.app G
  refine of_retract fX hℓ ((extensionByZero.{u, u + 1} j).map η)
    ((extensionByZero.{u, u + 1} j).map (p ≫ inv (η ≫ p))) ?_
    (TorsionCurveAssertions.nsmul_id_map_eq_zero _ hℓG)
    (TorsionCurveAssertions.nsmul_id_map_eq_zero (extensionByZero.{u, u + 1} j)
      (TorsionCurveAssertions.nsmul_id_map_eq_zero (etaleAbelianDirectImage.{u, u + 1} g)
        (TorsionCurveAssertions.nsmul_id_map_eq_zero (etaleAbelianInverseImage.{u, u + 1} g)
          hℓG))) hjg
  rw [← Functor.map_comp, ← Category.assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]

/-- Multiplication by an integer prime to `ℓ` is an isomorphism on an object killed by `ℓ`. -/
theorem isIso_nsmul_id_of_not_dvd {C : Type*} [Category* C] [Preadditive C] {ℓ d : ℕ}
    (hℓ : ℓ.Prime) (hd : ¬ ℓ ∣ d) {A : C} (hA : ℓ • 𝟙 A = 0) : IsIso (d • 𝟙 A) := by
  have hcop : Nat.Coprime d ℓ := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hd))
  obtain ⟨e, -, he⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hℓ.one_lt
  have hde : d * e = ℓ * (d * e / ℓ) + 1 := by
    have := Nat.div_add_mod (d * e) ℓ
    omega
  have key : ∀ a b : ℕ, a * b = ℓ * (d * e / ℓ) + 1 → (a • 𝟙 A) ≫ (b • 𝟙 A) = 𝟙 A := by
    intro a b h
    rw [Preadditive.nsmul_comp, Category.id_comp, smul_smul, h, add_smul, one_smul,
      mul_comm, mul_smul, hA, smul_zero, zero_add]
  exact ⟨⟨e • 𝟙 A, key d e hde, key e d (by rw [mul_comm]; exact hde)⟩⟩

/-- **The formal part of Stacks Tag 03SD, with the trace.** The variant of
`extensionByZero_of_finiteCover` in which `g` is finite étale of degree `d` prime to `ℓ`. -/
theorem extensionByZero_of_finiteEtaleCover {U V Y : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (g : V ⟶ U) [IsFinite g] [Etale g] (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank g d] (π : Y ⟶ X) [IsFinite π] (j' : V ⟶ Y)
    [IsOpenImmersion j'] (sq : IsPullback j' g π j)
    [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})] [IsNoetherian Y]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hd : ¬ ℓ ∣ d) (G : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hℓG : ℓ • 𝟙 G = 0)
    (L : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) (hℓL : ℓ • 𝟙 L = 0)
    (hfilt : ∀ P : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop,
      (∀ H, IsZero H → P H) → (∀ H H', (H ≅ H') → P H → P H') →
      (∀ S : ShortComplex (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}),
        S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂) →
      P L → P ((etaleAbelianInverseImage.{u, u + 1} g).obj G))
    (hbase : StrongTorsionCurveAssertions (π ≫ fX) ((extensionByZero.{u, u + 1} j').obj L)) :
    StrongTorsionCurveAssertions fX ((extensionByZero.{u, u + 1} j).obj G) := by
  obtain ⟨p, hp⟩ := exists_unit_comp_eq_nsmul g d G
  refine extensionByZero_of_finiteCover fX j g π j' sq hℓ G hℓG ⟨p, ?_⟩ L hℓL hfilt hbase
  rw [hp]
  exact isIso_nsmul_id_of_not_dvd hℓ hd hℓG

end StrongTorsionCurveAssertions

end Stacks.EtaleCohomology

end
