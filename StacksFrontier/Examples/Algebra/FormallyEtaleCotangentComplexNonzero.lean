module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.SurjectionSiteEdgeMapsUnconditional
public import StacksFrontier.Cotangent.SurjectionSiteExteriorConormal
public import StacksFrontier.Cotangent.SurjectionSiteProNilpotent
public import StacksFrontier.Examples.Algebra.FormallyEtaleNontrivialCotangent

/-!
# A formally étale ring map with nonzero cotangent complex

Stacks Tag 06E6: there is a formally étale surjective ring map `A → B` with `L_{B/A} ≠ 0`.

## Main results

* `Stacks.Examples.exists_formallyEtale_surjective_cotangentComplex_ne_zero`: **Stacks 06E6**, a
  formally étale surjection with `L_{B/A} ≠ 0` in `D(B)`, indeed with `H^{-2}(L_{B/A}) ≠ 0`.
* `Stacks.Examples.not_isZero_cotangentComplex_homology_two_of_formallyEtale`: for a formally
  étale surjection, `Tor₂^A(B, B) ≠ 0` implies `H^{-2}(L_{B/A}) ≠ 0`.

## Implementation notes

The example is that of `StacksFrontier.Examples.Algebra.FormallyEtaleNontrivialCotangent`, where
`Tor₂^A(B, B) ≠ 0` is proved.

The cotangent complex. The source deduces `H_2(L_{B/A}) ≠ 0` from the nonvanishing of
`Tor₂^A(B, B) = Ker(J ⊗_A J → J)` by the five-term exact sequence of Quillen's fundamental
spectral sequence (Tags 08RF and 08RG). That sequence is in this library for every surjective
ring map (`CommAlgCat.exact_fiveTerm_torTwo_of_surjective`), with `L_{B/A}` the cotangent
complex `CommAlgCat.cotangentComplex` of Tag 08PN and `Tor₂^A(B, B)` read as the second left
derived functor of extension of scalars along `A → B`. Its term `∧²_B(J/J²)` vanishes because
`J = J²` (through the second clause of 08RG,
`CommAlgCat.exteriorPower_conormal_leftDerivedColim_symmetricPower_of_surjective`), so the edge
map `Tor₂^A(B, B) → H^{-2}(L_{B/A})` is injective. The two readings of `Tor₂^A(B, B)` are compared
by restricting scalars back to `A`, where extension of scalars becomes `B ⊗_A -`.

## References

* [Stacks Project, Tag 06E6](https://stacks.math.columbia.edu/tag/06E6)
* [Stacks Project, Tag 08RG](https://stacks.math.columbia.edu/tag/08RG)
-/

@[expose] public section

open CategoryTheory Limits

universe w u

namespace Stacks.Examples

/-! ### From `Tor₂^A(B, B) ≠ 0` to `L_{B/A} ≠ 0` -/

section CotangentComplex

open CategoryTheory.MonoidalCategory

/-- Vanishing of a left derived map is carried along a post-composition which preserves
homology: the converse direction of `Stacks.NoncommChangeOfRings.leftDerived_map_eq_zero_of_comp`,
which needs no faithfulness. -/
private theorem leftDerived_comp_map_eq_zero {C D E : Type*} [Category* C] [Category* D]
    [Category* E] [Abelian C] [Abelian D] [Abelian E] [EnoughProjectives C]
    (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive] [G.PreservesHomology] (j : ℕ) {X Y : C}
    (φ : X ⟶ Y) (h : (F.leftDerived j).map φ = 0) : ((F ⋙ G).leftDerived j).map φ = 0 := by
  have hcomm := ProjectiveResolution.lift_commutes φ (ProjectiveResolution.of X)
    (ProjectiveResolution.of Y)
  generalize ProjectiveResolution.lift φ (ProjectiveResolution.of X)
    (ProjectiveResolution.of Y) = l at hcomm
  have h1 := F.leftDerived_map_eq j φ l hcomm
  rw [h] at h1
  have h2 : HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map l) j = 0 :=
    StacksDraft.PolynomialLocalComplex.eq_zero_of_iso_comp_comp_iso _ _ h1.symm
  have h3 := StacksDraft.PolynomialLocalComplex.homologyMap_map_eq_zero G
    (ComplexShape.down ℕ) j _ h2
  rw [(F ⋙ G).leftDerived_map_eq j φ l hcomm,
    show ((F ⋙ G).mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) j).map l = 0 from h3,
    zero_comp, comp_zero]

/-- If `L_j(B ⊗_A -)` vanishes at an `A`-module `X`, then so does `Tor'_j^A(X, B)`. -/
private theorem isZero_tor'_of_isZero_leftDerived_extendScalars {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] (j : ℕ) (X : ModuleCat.{u} A)
    (h : IsZero (((ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).leftDerived j).obj X)) :
    IsZero (((Tor' (ModuleCat.{u} A) j).obj X).obj (ModuleCat.of A B)) := by
  let f := algebraMap A B
  let M := (ModuleCat.restrictScalars f).obj (ModuleCat.of B B)
  have e : ModuleCat.extendScalars.{u, u, u} f ⋙ ModuleCat.restrictScalars f ≅ tensorLeft M :=
    Functor.isoWhiskerRight (Adjunction.leftAdjointUniq (ModuleCat.extendRestrictScalarsAdj f)
        (Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj.{u} f))
      (ModuleCat.restrictScalars f) ≪≫
      Stacks.NoncommChangeOfRings.extendScalarsCompRestrictScalarsIsoTensorLeft f
  have h0 : ((ModuleCat.extendScalars.{u, u, u} f).leftDerived j).map (𝟙 X) = 0 :=
    h.eq_of_src _ _
  have h1 := leftDerived_comp_map_eq_zero _ (ModuleCat.restrictScalars f) j (𝟙 X) h0
  have h2 := Stacks.NoncommChangeOfRings.leftDerived_map_eq_zero_of_natIso e.symm j (𝟙 X) h1
  have h3 := Stacks.NoncommChangeOfRings.leftDerived_map_eq_zero_of_natIso
    (BraidedCategory.tensorLeftIsoTensorRight M).symm j (𝟙 X) h2
  rw [CategoryTheory.Functor.map_id] at h3
  have hM : IsZero (((Tor' (ModuleCat.{u} A) j).obj X).obj M) :=
    (IsZero.iff_id_eq_zero _).mpr h3
  let le : (ModuleCat.of A B : Type u) ≃ₗ[A] (M : Type u) :=
    { toFun := fun b => (b : B), invFun := fun b => (b : B), left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_add' := fun _ _ => rfl,
      map_smul' := fun a b => Algebra.smul_def a b }
  let eM : ModuleCat.of A B ≅ M := le.toModuleIso
  exact hM.of_iso (((Tor' (ModuleCat.{u} A) j).obj X).mapIso eM)

/-- **`Tor₂^A(B, B) ≠ 0` forces `H^{-2}(L_{B/A}) ≠ 0` for a formally étale surjection.** For a
surjective formally étale `A → B` with kernel `I`, `I = I²`, so `∧²_B(I/I²) = 0`, and the five term
exact sequence of Remark 08RG makes the first edge map `Tor₂^A(B, B) → H^{-2}(L_{B/A})`
injective. -/
theorem not_isZero_cotangentComplex_homology_two_of_formallyEtale (A : Type u) [CommRing A]
    (B : CommAlgCat.{u} A) [Algebra.FormallyEtale A B]
    (hsurj : Function.Surjective (algebraMap A B))
    (htor : ¬ IsZero (((Tor' (ModuleCat.{u} A) 2).obj (ModuleCat.of A B)).obj
      (ModuleCat.of A B))) :
    ¬ IsZero ((CommAlgCat.cotangentComplex.{u, u} A B).homology (-2)) := by
  intro hL
  have hidem : IsIdempotentElem (RingHom.ker (algebraMap A B)) :=
    (Algebra.FormallyEtale.iff_of_surjective hsurj).1 inferInstance
  have : Subsingleton (RingHom.ker (algebraMap A B)).Cotangent :=
    (Ideal.cotangent_subsingleton_iff _).mpr hidem
  have : Subsingleton (CommAlgCat.surjectionExtension.{u, u} A B hsurj).Cotangent :=
    (CommAlgCat.surjectionKerCotangentEquiv A B hsurj).toEquiv.subsingleton
  have : Subsingleton
      (⋀[(B : Type u)]^2 (CommAlgCat.surjectionExtension.{u, u} A B hsurj).Cotangent) :=
    exteriorPower.subsingleton_of_span_eq_top_of_card_lt (Empty.elim : Empty → _)
      (Submodule.eq_top_iff'.mpr fun x => (Subsingleton.elim x 0).symm ▸ zero_mem _) 2
      (by simp)
  obtain ⟨eΛ⟩ :=
    CommAlgCat.exteriorPower_conormal_leftDerivedColim_symmetricPower_of_surjective A B hsurj 2
  have := eΛ.toEquiv.subsingleton
  have hΛ := ModuleCat.isZero_of_subsingleton
    ((CommAlgCat.siteHomologyFunctor A B (CommAlgCat.standardResolutionVarCardinal A B) 2).obj
      (Stacks.ChaoticSite.symmetricPowerDiagram
        (CommAlgCat.smallBoundedPolynomialSite A B (CommAlgCat.standardResolutionVarCardinal A B))
        (B : Type u)
        (CommAlgCat.smallPolynomialCotangentModulePresheaf A B
          (CommAlgCat.standardResolutionVarCardinal A B)) 2))
  have hex := CommAlgCat.exact_fiveTerm_torTwo_of_surjective A B hsurj
  have := hex.mono_g (hΛ.eq_of_src _ _)
  have hL' : IsZero ((CommAlgCat.cotangentComplex.{u, u} A B).homology (-((2 : ℕ) : ℤ))) := by
    simpa using hL
  have hT := IsZero.of_mono (CommAlgCat.torToCotangentEdge A B 2 two_pos) hL'
  exact htor (isZero_tor'_of_isZero_leftDerived_extendScalars 2 _ hT)

/-- **Stacks 06E6.** There exists a formally étale surjective ring map `A → B` with
`L_{B/A} ≠ 0`: the cotangent complex `CommAlgCat.cotangentComplex A B` of Tag 08PN is not zero in
the derived category `D(B)`, in every model of it, and indeed
`H^{-2}(L_{B/A}) = H_2(L_{B/A}) ≠ 0`, as the source concludes. The example is that of
`exists_formallyEtale_surjective_not_isZero_torTwo`, and the deduction is the source's:
`Tor₂^A(B, B) ≠ 0`, `∧²_B(J/J²) = 0` because `J = J²`, and the five term exact sequence of
Quillen's fundamental spectral sequence (Remark 08RG). -/
@[stacks 06E6]
theorem exists_formallyEtale_surjective_cotangentComplex_ne_zero :
    ∃ (A : Type u) (_ : CommRing A) (B : CommAlgCat.{u} A),
      Algebra.FormallyEtale A B ∧ Function.Surjective (algebraMap A B) ∧
        (∀ [HasDerivedCategory.{w} (ModuleCat.{u} B)],
          ¬ IsZero (DerivedCategory.Q.obj (CommAlgCat.cotangentComplex.{u, u} A B))) ∧
        ¬ IsZero ((CommAlgCat.cotangentComplex.{u, u} A B).homology (-2)) := by
  obtain ⟨A, hA, B, hB, hAlg, hFE, hsurj, htor⟩ :=
    exists_formallyEtale_surjective_not_isZero_torTwo.{u}
  let B' : CommAlgCat.{u} A := CommAlgCat.of A B
  have : Algebra.FormallyEtale A B' := hFE
  have hH := not_isZero_cotangentComplex_homology_two_of_formallyEtale A B' hsurj htor
  refine ⟨A, hA, B', hFE, hsurj, fun hQ => hH ?_, hH⟩
  exact ((DerivedCategory.homologyFunctor _ (-2)).map_isZero hQ).of_iso
    ((DerivedCategory.homologyFunctorFactors _ (-2)).app _).symm

end CotangentComplex

end Stacks.Examples

end
