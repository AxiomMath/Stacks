module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.InjectiveVanishingCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageFilteredColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.PrimaryDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeShortExact

/-!
# The base change map at torsion sheaves, from the base change map at `ℓ`-torsion sheaves

Let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a commutative square of schemes and consider the base change map
`g⁻¹ Rf_* F ⟶ Rf'_* (g')⁻¹ F` of `Stacks.EtaleCohomology.etaleAbelianSheafDerivedBaseChange` at an
abelian sheaf `F` on `X_étale`. The proof of [Stacks, Tag 0A4B] makes two reductions before it
uses any hypothesis on the square.

* **Filtered colimits.** A torsion sheaf `F` is the colimit of its subsheaves `F[n!]`
  (`Stacks.Torsion.isIso_torsionFiltrationDesc`); `g⁻¹` and `(g')⁻¹` are left adjoints, and
  higher direct images along a quasi-compact and quasi-separated morphism commute with filtered
  colimits ([Stacks, Tag 09Z1] for a fixed base,
  `Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_etaleAbelianDirectImage`). Comparing the
  two sides degree by degree, it suffices to treat sheaves killed by a positive integer.
* **Dévissage.** If `n = ℓ m` with `ℓ` prime, `0 → F[ℓ] → F → F/F[ℓ] → 0` is short exact with
  `F/F[ℓ]` killed by `m`, and the sheaves at which the base change map is invertible are closed
  under extensions (`isIso_etaleAbelianSheafDerivedBaseChange_of_shortExact`). So it suffices to
  treat sheaves killed by a prime.

## Main results

* `Stacks.EtaleCohomology.isIso_app_of_isColimit` — a natural transformation is invertible at the
  point of a colimit preserved by its source and target if it is invertible at every term.
* `Stacks.EtaleCohomology.etaleAbelianHigherBaseChange` — the base change map in degree `q`, as a
  natural transformation of functors on abelian sheaves, with its source and target identified
  with `g⁻¹ R^q f_*` and `R^q f'_* (g')⁻¹` by `etaleAbelianHigherBaseChangeSourceIso` and
  `etaleAbelianHigherBaseChangeTargetIso`.
* `Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_torsionSheafProperty` and
  `..._of_torsionSheafProperty_of_isPullback` — the colimit reduction.
* `Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_nsmul_id_eq_zero` — the
  dévissage.
* `EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_torsionSheafProperty_of_prime` —
  both together, for a cartesian square with `f` quasi-compact and quasi-separated.

## References

* [Stacks Project, Tag 0A4B](https://stacks.math.columbia.edu/tag/0A4B)
* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

/-- **Dévissage of an object annihilated by an integer into prime-annihilated pieces.** Let `P`
be a property of objects of an abelian category which holds for objects with vanishing identity,
is closed under extensions (the middle term of a short exact sequence whose outer terms have it),
and holds for every object killed by a prime. Then `P` holds for every object killed by a positive
integer: for `m = ℓ b` with `ℓ` the least prime factor, `0 → A[ℓ] → A → A/A[ℓ] → 0` has its sub
killed by `ℓ` and its quotient killed by `b < m`. -/
theorem prop_of_nsmul_id_eq_zero {C : Type*} [Category* C] [Abelian C] (P : C → Prop)
    (hzero : ∀ A : C, 𝟙 A = 0 → P A)
    (hext : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    (hprime : ∀ p : ℕ, p.Prime → ∀ A : C, p • 𝟙 A = 0 → P A) :
    ∀ m : ℕ, m ≠ 0 → ∀ A : C, m • 𝟙 A = 0 → P A := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm A hA
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hm) with hm1 | hm1
    · exact hzero A (by simpa [← hm1] using hA)
    · have hp : m.minFac.Prime := Nat.minFac_prime (by omega)
      obtain ⟨b, hb⟩ := Nat.minFac_dvd m
      have hbne : b ≠ 0 := by
        rintro rfl
        rw [Nat.mul_zero] at hb
        exact hm hb
      have hblt : b < m := by
        rw [hb]
        exact lt_mul_left (Nat.pos_of_ne_zero hbne) hp.one_lt
      exact hext _ (kernelQuotientShortComplex_shortExact (m.minFac • 𝟙 A))
        (hprime _ hp _ (nsmul_id_kernel_eq_zero A _))
        (ih b hblt hbne _ (nsmul_id_cokernel_eq_zero A _ b (by rw [← hb]; exact hA)))

/-- **A natural transformation is invertible at the point of a colimit cocone preserved by its
source and target as soon as it is invertible at every term of the diagram.** -/
public theorem isIso_app_of_isColimit {C D I : Type*} [Category* C] [Category* D] [Category* I]
    {Φ Ψ : C ⥤ D} (β : Φ ⟶ Ψ) {K : I ⥤ C} {c : Cocone K} (hc : IsColimit c)
    [PreservesColimit K Φ] [PreservesColimit K Ψ] (h : ∀ i, IsIso (β.app (K.obj i))) :
    IsIso (β.app c.pt) := by
  have h₁ := isColimitOfPreserves Φ hc
  have h₂ := isColimitOfPreserves Ψ hc
  have : ∀ i, IsIso ((Functor.whiskerLeft K β).app i) := h
  have : IsIso (Functor.whiskerLeft K β) := NatIso.isIso_of_isIso_app _
  suffices hβ : (h₁.coconePointsIsoOfNatIso h₂ (asIso (Functor.whiskerLeft K β))).hom =
      β.app c.pt by
    rw [← hβ]; infer_instance
  refine h₁.hom_ext fun j ↦ ?_
  rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
  exact (β.naturality (c.ι.app j)).symm

section Square

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- The base change map in degree `q`, as a natural transformation of functors on abelian
sheaves: `H^q(g⁻¹ Rf_*(-[0])) ⟶ H^q(Rf'_* (g')⁻¹(-[0]))`. -/
public abbrev etaleAbelianHigherBaseChange (q : ℤ) :
    (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0 ⋙
        (etaleAbelianDerivedDirectImage.{u, v} f ⋙ etaleAbelianDerivedInverseImage.{u, v} g)) ⋙
      DerivedCategory.homologyFunctor
        (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) q ⟶
    (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0 ⋙
        (etaleAbelianDerivedInverseImage.{u, v} g' ⋙ etaleAbelianDerivedDirectImage.{u, v} f')) ⋙
      DerivedCategory.homologyFunctor
        (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) q :=
  Functor.whiskerRight
    (Functor.whiskerLeft
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0)
      (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h))
    (DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) q)

/-- The source of the degree-`q` base change map is `g⁻¹ R^q f_*`. -/
public def etaleAbelianHigherBaseChangeSourceIso (p : ℕ) :
    (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0 ⋙
        (etaleAbelianDerivedDirectImage.{u, v} f ⋙ etaleAbelianDerivedInverseImage.{u, v} g)) ⋙
      DerivedCategory.homologyFunctor
        (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (p : ℤ) ≅
    (etaleAbelianDirectImage.{u, v} f).rightDerived p ⋙ etaleAbelianInverseImage.{u, v} g :=
  Functor.isoWhiskerLeft
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0 ⋙
        etaleAbelianDerivedDirectImage.{u, v} f)
      (Stacks.DerivedFunctor.derivedHomologyIso (etaleAbelianInverseImage.{u, v} g) (p : ℤ)) ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
        (etaleAbelianDirectImage.{u, v} f) (etaleAbelianDerivedDirectImage.{u, v} f)
        (etaleAbelianDerivedDirectImageUnit.{u, v} f)
        Stacks.DerivedFunctor.exists_quasiIso_isKInjective p)
      (etaleAbelianInverseImage.{u, v} g)

/-- The target of the degree-`q` base change map is `R^q f'_* (g')⁻¹`. -/
public def etaleAbelianHigherBaseChangeTargetIso (p : ℕ) :
    (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0 ⋙
        (etaleAbelianDerivedInverseImage.{u, v} g' ⋙ etaleAbelianDerivedDirectImage.{u, v} f')) ⋙
      DerivedCategory.homologyFunctor
        (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (p : ℤ) ≅
    etaleAbelianInverseImage.{u, v} g' ⋙ (etaleAbelianDirectImage.{u, v} f').rightDerived p :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
        ((etaleAbelianInverseImage.{u, v} g').mapDerivedCategorySingleFunctor 0)
        (etaleAbelianDerivedDirectImage.{u, v} f'))
      (DerivedCategory.homologyFunctor
        (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (p : ℤ)) ≪≫
    Functor.isoWhiskerLeft (etaleAbelianInverseImage.{u, v} g')
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
        (etaleAbelianDirectImage.{u, v} f') (etaleAbelianDerivedDirectImage.{u, v} f')
        (etaleAbelianDerivedDirectImageUnit.{u, v} f')
        Stacks.DerivedFunctor.exists_quasiIso_isKInjective p)

/-- **From sheaves annihilated by a prime to sheaves annihilated by a positive integer.** The
abelian sheaves at which the base change map is invertible contain the zero sheaves and are closed
under extensions (`isIso_etaleAbelianSheafDerivedBaseChange_of_shortExact`), so
`prop_of_nsmul_id_eq_zero` applies. -/
public theorem isIso_etaleAbelianSheafDerivedBaseChange_of_nsmul_id_eq_zero
    (hprime : ∀ ℓ : ℕ, ℓ.Prime →
      ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}, ℓ • 𝟙 G = 0 →
        IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' h G))
    (n : ℕ) (hn : n ≠ 0) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hG : n • 𝟙 G = 0) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' h G) := by
  refine prop_of_nsmul_id_eq_zero
    (fun G ↦ IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' h G)) (fun A hA ↦ ?_)
    (fun S hS h₁ h₃ ↦ isIso_etaleAbelianSheafDerivedBaseChange_of_shortExact f g g' f' h hS h₁ h₃)
    hprime n hn G hG
  have hA' : IsZero ((DerivedCategory.singleFunctor _ 0).obj A) :=
    Functor.map_isZero _ ((IsZero.iff_id_eq_zero A).2 hA)
  have hs := Functor.map_isZero
    (etaleAbelianDerivedDirectImage.{u, v} f ⋙ etaleAbelianDerivedInverseImage.{u, v} g) hA'
  have ht := Functor.map_isZero
    (etaleAbelianDerivedInverseImage.{u, v} g' ⋙ etaleAbelianDerivedDirectImage.{u, v} f') hA'
  exact ⟨⟨0, hs.eq_of_src _ _, ht.eq_of_src _ _⟩⟩

/-- **From sheaves annihilated by an integer to torsion sheaves.** If the higher direct images
along `f` and `f'` commute with the colimit of every `ℕ`-indexed diagram, and the base change map
is invertible at every abelian sheaf annihilated by a positive integer, then it is invertible at
every torsion abelian sheaf: such a sheaf is the colimit of its torsion filtration
`F[n!]` (`Stacks.Torsion.isIso_torsionFiltrationDesc`), and both sides of the base change map
in degree `q` commute with that colimit, `g⁻¹` and `(g')⁻¹` being left adjoints. -/
public theorem isIso_etaleAbelianSheafDerivedBaseChange_of_torsionSheafProperty
    (hcolf : ∀ (p : ℕ) (K : ULift.{max (u + 1) v} ℕ ⥤
        Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}),
      PreservesColimit K ((etaleAbelianDirectImage.{u, v} f).rightDerived p))
    (hcolf' : ∀ (p : ℕ) (K : ULift.{max (u + 1) v} ℕ ⥤
        Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}),
      PreservesColimit K ((etaleAbelianDirectImage.{u, v} f').rightDerived p))
    (hbdd : ∀ (n : ℕ), 0 < n →
      ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}, n • 𝟙 G = 0 →
        IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' h G))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' h F) := by
  rw [DerivedCategory.isIso_iff]
  intro q
  rcases lt_or_ge q 0 with hq | hq
  · exact isIso_homology_etaleAbelianDerivedBaseChange_single_of_neg f g g' f' h F q hq
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    let K := Stacks.Torsion.torsionFiltration.{max (u + 1) v, u, u + 1} X.smallEtaleTopology F
    let c : Cocone K :=
      Cocone.mk F
        (Stacks.Torsion.torsionFiltrationι.{max (u + 1) v, u, u + 1} X.smallEtaleTopology F)
    have : IsIso ((colimit.isColimit K).desc c) :=
      Stacks.Torsion.isIso_torsionFiltrationDesc X.smallEtaleTopology F hF
    have hc : IsColimit c := IsColimit.ofPointIso (colimit.isColimit K)
    have := hcolf p K
    have : PreservesColimit (K ⋙ (etaleAbelianDirectImage.{u, v} f).rightDerived p)
        (etaleAbelianInverseImage.{u, v} g) := inferInstance
    have : PreservesColimit (K ⋙ etaleAbelianInverseImage.{u, v} g')
        ((etaleAbelianDirectImage.{u, v} f').rightDerived p) :=
      hcolf' p (K ⋙ etaleAbelianInverseImage.{u, v} g')
    have : PreservesColimit K (etaleAbelianInverseImage.{u, v} g') := inferInstance
    have : PreservesColimit K
        ((DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0 ⋙
          (etaleAbelianDerivedDirectImage.{u, v} f ⋙ etaleAbelianDerivedInverseImage.{u, v} g)) ⋙
        DerivedCategory.homologyFunctor
          (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (p : ℤ)) :=
      preservesColimit_of_natIso K (etaleAbelianHigherBaseChangeSourceIso f g p).symm
    have : PreservesColimit K
        ((DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0 ⋙
          (etaleAbelianDerivedInverseImage.{u, v} g' ⋙ etaleAbelianDerivedDirectImage.{u, v} f')) ⋙
        DerivedCategory.homologyFunctor
          (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (p : ℤ)) :=
      preservesColimit_of_natIso K (etaleAbelianHigherBaseChangeTargetIso g' f' p).symm
    refine isIso_app_of_isColimit (etaleAbelianHigherBaseChange f g g' f' h (p : ℤ)) hc
      (fun i ↦ ?_)
    have := hbdd (Nat.factorial i.down) (Nat.factorial_pos _) (K.obj i)
      (nsmul_id_kernel_eq_zero F _)
    exact Functor.map_isIso (DerivedCategory.homologyFunctor _ (p : ℤ))
      (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' h (K.obj i))

/-- **From sheaves annihilated by an integer to torsion sheaves, for a cartesian square with `f`
quasi-compact and quasi-separated.** The higher direct images along `f`, and along its base change
`f'`, commute with filtered colimits ([Stacks, Tag 09Z1] for a fixed base), so
`isIso_etaleAbelianSheafDerivedBaseChange_of_torsionSheafProperty` applies. -/
public theorem isIso_etaleAbelianSheafDerivedBaseChange_of_torsionSheafProperty_of_isPullback
    (sq : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f]
    (hbdd : ∀ (n : ℕ), 0 < n →
      ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}, n • 𝟙 G = 0 →
        IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' sq.w G))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' sq.w F) := by
  have : QuasiCompact f' := MorphismProperty.IsStableUnderBaseChange.of_isPullback sq ‹_›
  have : QuasiSeparated f' := MorphismProperty.IsStableUnderBaseChange.of_isPullback sq ‹_›
  refine isIso_etaleAbelianSheafDerivedBaseChange_of_torsionSheafProperty f g g' f' sq.w
    (fun p K ↦ ?_) (fun p K ↦ ?_) hbdd F hF
  · have := preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage_of_qcqs.{v, u} f p
      (ULift.{max (u + 1) v} ℕ)
    exact PreservesColimitsOfShape.preservesColimit
  · have := preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage_of_qcqs.{v, u} f' p
      (ULift.{max (u + 1) v} ℕ)
    exact PreservesColimitsOfShape.preservesColimit

/-- **From sheaves annihilated by a prime to torsion sheaves**, for a cartesian square with `f`
quasi-compact and quasi-separated: the two reductions of [Stacks, Tag 0A4B], by filtered
colimits and by the dévissage `0 → F[ℓ] → F → F/F[ℓ] → 0`. -/
public theorem isIso_etaleAbelianSheafDerivedBaseChange_of_torsionSheafProperty_of_prime
    (sq : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f]
    (hprime : ∀ ℓ : ℕ, ℓ.Prime →
      ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}, ℓ • 𝟙 G = 0 →
        IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' sq.w G))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' sq.w F) :=
  isIso_etaleAbelianSheafDerivedBaseChange_of_torsionSheafProperty_of_isPullback f g g' f' sq
    (fun n hn G hG ↦ isIso_etaleAbelianSheafDerivedBaseChange_of_nsmul_id_eq_zero f g g' f' sq.w
      hprime n hn.ne' G hG) F hF

end Square

end Stacks.EtaleCohomology

end
