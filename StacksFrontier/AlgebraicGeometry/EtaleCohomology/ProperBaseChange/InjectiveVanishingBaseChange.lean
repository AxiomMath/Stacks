module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AcyclicResolutionBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeTorsionColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.InjectiveVanishingCondition
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianWeakSerre
public import StacksFrontier.CategoryTheory.Triangulated.DimensionShifting

/-!
# From the vanishing condition of Stacks 0A4B (2) to cohomology commuting with base change

Let `f : X ⟶ Y` be proper. The implication (2) ⟹ (1) of
[Stacks, Tag 0A4B](https://stacks.math.columbia.edu/tag/0A4B) runs as follows.

* At an injective sheaf `I` of `ℤ/ℓℤ`-modules both direct images in the base change map
  `g⁻¹ Rf_* I ⟶ Rf'_* (g')⁻¹ I` are computed by underived direct images: `I` is acyclic for `f_*`
  ([Stacks, Tag 03FD]) and `(g')⁻¹ I` is acyclic for `f'_*` by (2). So the base change map at `I`
  is the underived comparison `g⁻¹ f_* I ⟶ f'_* (g')⁻¹ I`, which is invertible by
  [Stacks, Tag 0A3U].
* A sheaf killed by `ℓ` embeds in such an `I` with a cokernel again killed by `ℓ`; dimension
  shifting along these embeddings, which replaces the injective resolution and Leray's lemma of
  the source and is the same induction on the degree, gives invertibility at every sheaf killed by
  `ℓ`.
* The dévissage `0 → F[ℓ] → F → F/F[ℓ] → 0` and filtered colimits of the subsheaves `F[n]` give
  it at every torsion sheaf.

Tag 0A3U is carried here as the explicit hypothesis that the underived comparison is invertible
for every cartesian square of `f`.

## Main results

* `isIso_etaleAbelianSheafDerivedBaseChange_of_nsmul_id_eq_zero_of_embedding` and
  `cohomologyCommutesWithBaseChange_of_embedding` — dimension shifting along embeddings into
  sheaves at which the base change map is invertible.
* `isIso_etaleAbelianSheafDerivedBaseChange_of_nsmul_id_eq_zero_of_injective` — invertibility at
  injective sheaves of `ℤ/nℤ`-modules gives it at every sheaf killed by `n`.
* `cohomologyCommutesWithBaseChange_of_isIso_injective` — invertibility at injective sheaves of
  `ℤ/ℓℤ`-modules, `ℓ` prime, gives that cohomology commutes with base change.
* `cohomologyCommutesWithBaseChange_of_higherDirectImagesVanishOnInjectives` — the implication
  (2) ⟹ (1), granted Tag 0A3U for `f`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.ZModSheaf

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

section Square

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- **Dimension shifting for sheaves killed by `n`.** If every abelian sheaf killed by `n > 0`
embeds in a sheaf killed by `n` at which the base change map of a commutative square is
invertible, then the base change map is invertible at every abelian sheaf killed by `n`: the
cokernel of such an embedding is again killed by `n`, so dimension shifting applies; in negative
degrees both sides vanish. -/
public theorem isIso_etaleAbelianSheafDerivedBaseChange_of_nsmul_id_eq_zero_of_embedding
    (n : ℕ)
    (hemb : ∀ A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}, n • 𝟙 A = 0 →
      ∃ (B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : A ⟶ B), Mono i ∧
        n • 𝟙 B = 0 ∧ IsIso (etaleAbelianSheafDerivedBaseChange.{u, 0} f g g' f' h B))
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hA : n • 𝟙 A = 0) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, 0} f g g' f' h A) := by
  refine Stacks.Triangulated.isIso_app_of_dimensionShifting
    (etaleAbelianDerivedBaseChange.{u, 0} f g g' f' h)
    (fun K ↦ ∃ A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      n • 𝟙 A = 0 ∧ K = (DerivedCategory.singleFunctor _ 0).obj A) ?_ ?_ _ ⟨A, hA, rfl⟩
  · rintro _ ⟨A, hA, rfl⟩
    obtain ⟨B, i, hi, hB, hBiso⟩ := hemb A hA
    have hS := ShortComplex.ShortExact.mk' (S := ShortComplex.mk i (cokernel.π i)
      (cokernel.condition i)) (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i))
      hi inferInstance
    refine ⟨_, _, _, _, _, hS.singleTriangle_distinguished, hBiso, cokernel i, ?_, rfl⟩
    exact Stacks.ConstantSheaf.nsmul_id_zero_of_epi (cokernel.π i) n hB
  · rintro _ ⟨A, -, rfl⟩ q hq
    exact isIso_homology_etaleAbelianDerivedBaseChange_single_of_neg.{u, 0} f g g' f' h A q hq

/-- **From injective sheaves of `ℤ/nℤ`-modules to all sheaves killed by `n`.** If the base change
map of a commutative square is invertible at the underlying abelian sheaf of every injective sheaf
of `ℤ/nℤ`-modules, `n > 0`, then it is invertible at every abelian sheaf killed by `n`: each such
sheaf embeds in the underlying sheaf of an injective sheaf of `ℤ/nℤ`-modules. -/
public theorem isIso_etaleAbelianSheafDerivedBaseChange_of_nsmul_id_eq_zero_of_injective
    (n : ℕ)
    (hinj : ∀ (J : SheafOfModules.{u + 1}
        (zmodRingSheaf.{u + 1} X.smallEtaleTopology n)), Injective J →
      IsIso (etaleAbelianSheafDerivedBaseChange.{u, 0} f g g' f' h
        ((SheafOfModules.toSheaf _).obj J)))
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hA : n • 𝟙 A = 0) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, 0} f g g' f' h A) := by
  refine isIso_etaleAbelianSheafDerivedBaseChange_of_nsmul_id_eq_zero_of_embedding f g g' f' h n
    (fun A hA ↦ ?_) A hA
  obtain ⟨J, hJ, i, hi⟩ := exists_mono_toSheaf_injective n A hA
  exact ⟨_, i, hi, nsmul_id_toSheaf_eq_zero.{u, 0} n J, hinj J hJ⟩

end Square

/-- **Dimension shifting gives that cohomology commutes with base change**, for `f`
quasi-compact and quasi-separated: if for every prime `ℓ` and every cartesian square every sheaf
killed by `ℓ` embeds in a sheaf killed by `ℓ` at which the base change map is invertible, then
the base change map is invertible at every sheaf killed by a prime, and the reductions by
dévissage and filtered colimits of [Stacks, Tag 0A4B] give it at every torsion sheaf. -/
public theorem cohomologyCommutesWithBaseChange_of_embedding {X Y : Scheme.{u}}
    {f : X ⟶ Y} [QuasiCompact f] [QuasiSeparated f]
    (hf : ∀ (ℓ : ℕ), ℓ.Prime → ∀ ⦃X' Y' : Scheme.{u}⦄ (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g) (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      ℓ • 𝟙 A = 0 →
      ∃ (B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : A ⟶ B), Mono i ∧
        ℓ • 𝟙 B = 0 ∧ IsIso (etaleAbelianSheafDerivedBaseChange.{u, 0} f g g' f' sq.w B)) :
    CohomologyCommutesWithBaseChange.{u, 0} f := by
  intro X' Y' g g' f' sq F hF
  exact isIso_etaleAbelianSheafDerivedBaseChange_of_torsionSheafProperty_of_prime f g g' f' sq
    (fun ℓ hℓ G hG ↦ isIso_etaleAbelianSheafDerivedBaseChange_of_nsmul_id_eq_zero_of_embedding
      f g g' f' sq.w ℓ (hf ℓ hℓ g g' f' sq) G hG) F hF

/-- **Base change at injective sheaves of `ℤ/ℓℤ`-modules implies that cohomology commutes with
base change**, for `f` quasi-compact and quasi-separated. Invertibility at the injective sheaves
of `ℤ/ℓℤ`-modules gives it at every sheaf killed by a prime, and the reductions by dévissage and
filtered colimits of [Stacks, Tag 0A4B] give it at every torsion sheaf. -/
public theorem cohomologyCommutesWithBaseChange_of_isIso_injective {X Y : Scheme.{u}}
    {f : X ⟶ Y} [QuasiCompact f] [QuasiSeparated f]
    (hf : ∀ (ℓ : ℕ), ℓ.Prime →
      ∀ (I : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ)),
        Injective I →
      ∀ ⦃X' Y' : Scheme.{u}⦄ (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
        (sq : IsPullback g' f' f g),
        IsIso (etaleAbelianSheafDerivedBaseChange.{u, 0} f g g' f' sq.w
          ((SheafOfModules.toSheaf _).obj I))) :
    CohomologyCommutesWithBaseChange.{u, 0} f := by
  intro X' Y' g g' f' sq F hF
  exact isIso_etaleAbelianSheafDerivedBaseChange_of_torsionSheafProperty_of_prime f g g' f' sq
    (fun ℓ hℓ G hG ↦ isIso_etaleAbelianSheafDerivedBaseChange_of_nsmul_id_eq_zero_of_injective
      f g g' f' sq.w ℓ (fun J hJ ↦ hf ℓ hℓ J hJ g g' f' sq) G hG) F hF

/-- **The implication (2) ⟹ (1) of [Stacks, Tag 0A4B]**, for a proper morphism `f`, granted
[Stacks, Tag 0A3U] for `f` as the hypothesis `hbc`: if the higher direct images
`R^q f'_* (g')⁻¹ I` vanish for every injective sheaf `I` of `ℤ/ℓℤ`-modules and every base change,
then cohomology commutes with base change for `f`. -/
public theorem cohomologyCommutesWithBaseChange_of_higherDirectImagesVanishOnInjectives
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (hbc : ∀ ⦃X' Y' : Scheme.{u}⦄ (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), IsIso (etaleAbelianBaseChange.{u, 0} f g g' f' sq.w))
    (h : HigherDirectImagesVanishOnInjectives.{u, 0} f) :
    CohomologyCommutesWithBaseChange.{u, 0} f :=
  cohomologyCommutesWithBaseChange_of_isIso_injective fun ℓ hℓ I hI _ _ g g' f' sq ↦ by
    have := hbc g g' f' sq
    have : Injective I := hI
    exact (isIso_etaleAbelianSheafDerivedBaseChange_iff_of_rightAcyclic.{u, 0} f g g' f' sq.w _
      (isZero_homology_etaleAbelianDerivedDirectImage_single_toSheaf_of_injective.{u, 0} f ℓ I)
      (h ℓ hℓ I hI g g' f' sq)).2 inferInstance

end Stacks.EtaleCohomology

end
