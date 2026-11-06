module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology

/-!
# When the descent of a base change comparison between exact functors is invertible

`Stacks.Cohomology.BaseChange.derived` descends a comparison `τ : F ⋙ G ⟶ G' ⋙ F'` of underived
composites to the bounded below right derived functors. `Stacks.Cohomology.BaseChange`
already records that the descent is invertible *everywhere* when `τ` is
(`Stacks.Cohomology.BaseChange.isIso_derived_app`). This file proves the pointwise refinement,
in the case where **all four functors of the square are exact**: the descent is invertible at an
object `M` of the bounded below derived category exactly when `τ` is invertible at each
cohomology object `H^n(M)`.

The two directions are used in opposite ways. Read forwards, it reduces invertibility of the
descent at a single object to invertibility of the underived comparison on a *prescribed* family
of objects — which is what lets a base change statement available only for, say, torsion sheaves
be fed into a derived argument. Read backwards at `M = Y[0]`, it recovers the underived
comparison at `Y` from the degree-zero cohomology of the descent, which is the form in which the
condition `BC(f, n, q₀)` of [Stacks, Tag 0F02] delivers it.

## The route

With `F`, `F'`, `G`, `G'` exact, all four derived-functor units are invertible, so the
characterizing factorization `Stacks.Cohomology.BaseChange.derived_fac_app` exhibits the
descent at `Qh.obj K` as the image under `DerivedCategory.Plus.Qh` of the *degreewise*
transformation `Stacks.Cohomology.BaseChange.mapPlus τ`, conjugated by three isomorphisms
(`isIso_derived_app_Qh_iff_of_exact`). A morphism of the bounded below derived category is
invertible exactly when it is on cohomology (`DerivedCategory.Plus.isIso_iff`), and the cohomology
of the image of a morphism of the homotopy category is the cohomology of that morphism
(`DerivedCategory.homologyFunctorFactorsh`), so invertibility of the descent becomes a degreewise
condition on complexes (`isIso_Qh_map_iff_homology`). There
`Stacks.Homology.homotopyHomologyIso_hom_naturality` — the naturality of the comparison of an
exact functor with homology **in the functor** — turns the condition into invertibility of `τ`
at the homology of the complex (`isIso_homology_map_mapPlus_app_iff`). The passage from a
complex representing `M` back to `M` is `CategoryTheory.Functor.objObjPreimageIso` for the
essentially surjective `Qh`.

For the backwards reading at `M = Y[0]` the extra ingredient is that both sides of the square
are then concentrated in degree zero: with `F` and `G` exact,
`Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso` identifies `RG(RF(Y[0]))` with
`(G F Y)[0]`, whose cohomology vanishes outside degree zero, so degree-zero cohomology already
reflects invertibility (`isIso_of_isIso_homology_zero`).

## Main definitions

* `Stacks.Cohomology.BaseChange.plusHomologyIsoAux` — the cohomology of the image of a bounded
  below complex under `DerivedCategory.Plus.Qh`, identified with the cohomology of the complex.
* `Stacks.Cohomology.BaseChange.plusSingleHomologyIso` — degree-zero cohomology of the
  degree-zero embedding is the object itself.

## Main results

* `Stacks.Cohomology.BaseChange.isIso_Qh_map_iff_homology` — a morphism of the bounded below
  homotopy category becomes invertible in the derived category exactly when it is invertible on
  cohomology.
* `Stacks.Cohomology.BaseChange.isIso_homology_map_mapPlus_app_iff` — the degreewise image of a
  transformation of **exact** functors is invertible on cohomology in degree `n` exactly when
  the transformation is invertible at the degree-`n` cohomology of the complex.
* `Stacks.Cohomology.BaseChange.isIso_derived_app_Qh_iff_of_exact` — the descent at the image of a
  complex is invertible exactly when the degreewise transformation is.
* `Stacks.Cohomology.BaseChange.isIso_derived_app_iff_homology` — **the criterion**: the descent
  is invertible at `M` exactly when `τ` is invertible at every `H^n(M)`.
* `Stacks.Cohomology.BaseChange.isIso_app_of_isIso_homology_zero_derived` — the backwards
  reading at a single object: invertibility of the degree-zero cohomology of the descent at
  `Y[0]` forces invertibility of `τ` at `Y`.

## Implementation notes

Everything is generic: no statement mentions sheaves or schemes.

The comparison isomorphism `ε` that `Stacks.Cohomology.BaseChange.derived` descends along is
carried as a parameter rather than specialized to
`Stacks.Cohomology.BaseChange.exactUnitIso`. Nothing in the proofs uses its shape — only that
it is an isomorphism — and leaving it free is what lets the statements be applied to
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`, whose own spelling of it is
`exactUnitIso`, without a comparison of two spellings.

The three invertible factors of the factorization are cancelled by `isIso_mid_iff₄`, whose
docstring records why its invertibility hypotheses cannot be instances here.

The transfer of invertibility of a component along an isomorphism of the object is Mathlib's
`CategoryTheory.NatTrans.isIso_app_iff_of_iso`, and the passage between annihilation of a sheaf
by `n` on sections and annihilation of its identity is
`Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff`; neither is restated here.

## References

* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.BaseChange

attribute [local instance] HasDerivedCategory.standard

/-! ### Cancelling three invertible factors -/

section Algebra

/-- **The second of four composable morphisms is invertible exactly when the composite is**,
given that the other three are.

The three invertibility hypotheses are explicit arguments rather than instances, and that is
load-bearing: the morphisms this is applied to are components of comparisons of derived
functors, whose sources and targets agree with the ones the composite carries only up to
`Functor.mapHomotopyCategoryPlus` of a composite versus the composite of the two, and instance
search does not close that gap — it reports the composite of the two invertible outer factors as
unsynthesizable even with both factors in context. Passing them in and re-registering them
inside is what makes the cancellation go through.

This is not `Stacks.Cohomology.DerivedPushforward.isIso_middle_of_comp`, which is the
three-fold composite in implication form, nor the implication for the *third* of four factors
used in `StacksFrontier/AlgebraicGeometry/EtaleCohomology/BaseChangeHigher/IntegralBase.lean`. -/
private theorem isIso_mid_iff₄ {X : Type*} [Category* X] {o₁ o₂ o₃ o₄ o₅ : X}
    (a : o₁ ⟶ o₂) (q : o₂ ⟶ o₃) (b : o₃ ⟶ o₄) (c : o₄ ⟶ o₅)
    (ha : IsIso a) (hb : IsIso b) (hc : IsIso c) : IsIso (a ≫ q ≫ b ≫ c) ↔ IsIso q := by
  have := ha
  have := hb
  have := hc
  rw [isIso_comp_left_iff, isIso_comp_right_iff]

end Algebra

/-! ### Cohomology of the image of a complex in the derived category -/

section Bridge

variable {A D : Type*} [Category* A] [Category* D] [Abelian A] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory D]

/-- **The cohomology of the image of a bounded below complex under
`DerivedCategory.Plus.Qh`** is the cohomology of the complex. -/
public def plusHomologyIsoAux (n : ℤ) (K : HomotopyCategory.Plus A) :
    (DerivedCategory.Plus.homologyFunctor A n).obj (DerivedCategory.Plus.Qh.obj K) ≅
      (HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n).obj K.obj :=
  (DerivedCategory.homologyFunctorFactorsh A n).app K.obj

/-- Cohomology in a fixed degree of the image of a morphism of bounded below complexes is
invertible exactly when the cohomology of that morphism is. -/
public theorem isIso_plus_homology_map_Qh_map_iff (n : ℤ) {K L : HomotopyCategory.Plus D}
    (ψ : K ⟶ L) :
    IsIso ((DerivedCategory.Plus.homologyFunctor D n).map (DerivedCategory.Plus.Qh.map ψ)) ↔
      IsIso ((HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) n).map ψ.hom) := by
  have h : (DerivedCategory.Plus.homologyFunctor D n).map (DerivedCategory.Plus.Qh.map ψ) =
      (DerivedCategory.homologyFunctor D n).map (DerivedCategory.Qh.map ψ.hom) := rfl
  rw [h]
  exact NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactorsh D n) ψ.hom

/-- **A morphism of bounded below complexes becomes invertible in the derived category exactly
when it is invertible on cohomology in every degree.** -/
public theorem isIso_Qh_map_iff_homology {K L : HomotopyCategory.Plus D} (ψ : K ⟶ L) :
    IsIso (DerivedCategory.Plus.Qh.map ψ) ↔
      ∀ n : ℤ, IsIso ((HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) n).map ψ.hom) := by
  rw [DerivedCategory.Plus.isIso_iff]
  exact forall_congr' fun n => isIso_plus_homology_map_Qh_map_iff n ψ

end Bridge

/-! ### The degreewise image of a transformation of exact functors -/

section Degreewise

variable {A D : Type*} [Category* A] [Category* D] [Abelian A] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory D]
  {E₁ E₂ : A ⥤ D} [E₁.Additive] [E₂.Additive]
  [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]
  [PreservesFiniteLimits E₂] [PreservesFiniteColimits E₂]

omit [HasDerivedCategory A] [HasDerivedCategory D] in
/-- **Invertibility of a transformation of exact functors is detected on homology, degreewise.**
Applying the transformation to a complex and taking cohomology in degree `n` is, up to the
comparison of an exact functor with cohomology, the transformation at the degree-`n` cohomology
of the complex; and that comparison is natural in the functor, which is
`Stacks.Homology.homotopyHomologyIso_hom_naturality`. -/
public theorem isIso_homology_map_mapPlus_app_iff (τ : E₁ ⟶ E₂) (K : HomotopyCategory.Plus A)
    (n : ℤ) :
    IsIso ((HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) n).map
        ((mapPlus τ).app K).hom) ↔
      IsIso (τ.app ((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n).obj K.obj)) := by
  have hnat := congr_app (Stacks.Homology.homotopyHomologyIso_hom_naturality τ n) K.obj
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hnat
  have hψ : ((mapPlus τ).app K).hom =
      (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K.obj := rfl
  rw [hψ]
  have h1 : IsIso ((Stacks.Homology.homotopyHomologyIso E₁ n).hom.app K.obj) := inferInstance
  have h2 : IsIso ((Stacks.Homology.homotopyHomologyIso E₂ n).hom.app K.obj) := inferInstance
  rw [← isIso_comp_right_iff (τ.app ((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n).obj
    K.obj)) ((Stacks.Homology.homotopyHomologyIso E₂ n).hom.app K.obj), hnat,
    isIso_comp_left_iff]

end Degreewise

/-! ### Objects concentrated in degree zero -/

section SingleObjects

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- **Degree-zero cohomology of the degree-zero embedding is the object itself.** -/
public def plusSingleHomologyIso (Y : A) :
    (DerivedCategory.Plus.homologyFunctor A 0).obj
        ((DerivedCategory.Plus.singleFunctor A 0).obj Y) ≅ Y :=
  (DerivedCategory.homologyFunctor A 0).mapIso
      ((DerivedCategory.Plus.singleFunctorιIso A 0).app Y) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app Y

/-- The degree-zero embedding has no cohomology outside degree zero. -/
public theorem isZero_plusSingle_homology (Y : A) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor A n).obj
      ((DerivedCategory.Plus.singleFunctor A 0).obj Y)) := by
  rcases lt_or_gt_of_ne hn with h | h
  · exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 n h
  · exact DerivedCategory.Plus.isZero_homology_of_isLE _ 0 n h

/-- **A morphism between objects concentrated in degree zero is invertible as soon as its
degree-zero cohomology is**: outside degree zero both cohomologies vanish, so there the induced
map is invertible for free. -/
public theorem isIso_of_isIso_homology_zero {X Y : DerivedCategory.Plus A} {X₀ Y₀ : A}
    (φ : X ⟶ Y) (eX : X ≅ (DerivedCategory.Plus.singleFunctor A 0).obj X₀)
    (eY : Y ≅ (DerivedCategory.Plus.singleFunctor A 0).obj Y₀)
    (h : IsIso ((DerivedCategory.Plus.homologyFunctor A 0).map φ)) : IsIso φ := by
  rw [DerivedCategory.Plus.isIso_iff]
  intro n
  by_cases hn : n = 0
  · subst hn
    exact h
  · have hZ : ∀ {Z : DerivedCategory.Plus A} {Z₀ : A},
        (Z ≅ (DerivedCategory.Plus.singleFunctor A 0).obj Z₀) →
          IsZero ((DerivedCategory.Plus.homologyFunctor A n).obj Z) := fun e =>
      IsZero.of_iso (isZero_plusSingle_homology _ n hn)
        ((DerivedCategory.Plus.homologyFunctor A n).mapIso e)
    exact ⟨⟨0, (hZ eX).eq_of_src _ _, (hZ eY).eq_of_src _ _⟩⟩

end SingleObjects

/-! ### The criterion -/

section DerivedLocal

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  (τ : F ⋙ G ⟶ G' ⋙ F')
  (ε : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
    DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus)

omit [PreservesFiniteLimits G] [PreservesFiniteColimits G] in
/-- **With all four functors of the square exact, the descent of `τ` is invertible at the image
of a bounded below complex exactly when the degreewise transformation is.** All four
derived-functor units are invertible, so the three remaining factors of the characterizing
factorization `Stacks.Cohomology.BaseChange.derived_fac_app` cancel. -/
public theorem isIso_derived_app_Qh_iff_of_exact (K : HomotopyCategory.Plus A) :
    IsIso ((derived F F' G G' τ ε).app (DerivedCategory.Plus.Qh.obj K)) ↔
      IsIso (DerivedCategory.Plus.Qh.map ((mapPlus τ).app K)) := by
  have hFu : IsIso F.rightDerivedFunctorPlusUnith := exactUnit_isIso F
  have hF'u : IsIso F'.rightDerivedFunctorPlusUnith := exactUnit_isIso F'
  have hG'u : IsIso G'.rightDerivedFunctorPlusUnith := exactUnit_isIso G'
  have iU : IsIso (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K)) :=
    (G.rightDerivedFunctorPlus.mapIso
      (Iso.app (asIso F.rightDerivedFunctorPlusUnith) K)).isIso_hom
  have i1 : IsIso (ε.inv.app (F.mapHomotopyCategoryPlus.obj K)) := (Iso.app ε _).isIso_inv
  have i3 : IsIso (F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K)) :=
    (Iso.app (asIso F'.rightDerivedFunctorPlusUnith) _).isIso_hom
  have i4 : IsIso (F'.rightDerivedFunctorPlus.map (G'.rightDerivedFunctorPlusUnith.app K)) :=
    (F'.rightDerivedFunctorPlus.mapIso
      (Iso.app (asIso G'.rightDerivedFunctorPlusUnith) K)).isIso_hom
  have hfac := derived_fac_app F F' G G' τ ε K
  rw [onHomotopy_app] at hfac
  have := iU
  rw [← isIso_comp_left_iff (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K)),
    hfac]
  exact isIso_mid_iff₄ _ _ _ _ i1 i3 i4

/-- **The descent of a comparison between exact functors is invertible at an object of the
bounded below derived category exactly when the comparison itself is invertible at each of that
object's cohomology objects.** -/
public theorem isIso_derived_app_iff_homology (M : DerivedCategory.Plus A) :
    IsIso ((derived F F' G G' τ ε).app M) ↔
      ∀ n : ℤ, IsIso (τ.app ((DerivedCategory.Plus.homologyFunctor A n).obj M)) := by
  obtain ⟨K, ⟨η⟩⟩ : ∃ K, Nonempty (DerivedCategory.Plus.Qh.obj K ≅ M) :=
    ⟨DerivedCategory.Plus.Qh.objPreimage M, ⟨DerivedCategory.Plus.Qh.objObjPreimageIso M⟩⟩
  rw [← NatTrans.isIso_app_iff_of_iso (derived F F' G G' τ ε) η,
    isIso_derived_app_Qh_iff_of_exact, isIso_Qh_map_iff_homology]
  refine forall_congr' fun n => ?_
  rw [isIso_homology_map_mapPlus_app_iff τ K n]
  exact NatTrans.isIso_app_iff_of_iso τ ((plusHomologyIsoAux n K).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor A n).mapIso η)

/-- **From the degree-zero cohomology of the descent at an object in degree zero back to the
underived comparison.** With all four functors of the square exact, the descent of `τ` at the
degree-zero embedding of `Y` has both ends concentrated in degree zero, so invertibility of its
degree-zero cohomology forces invertibility of `τ` at `Y`. -/
public theorem isIso_app_of_isIso_homology_zero_derived (Y : A)
    (h : IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      ((derived F F' G G' τ ε).app
        ((DerivedCategory.Plus.singleFunctor A 0).obj Y)))) :
    IsIso (τ.app Y) := by
  have eX : (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).obj
        ((DerivedCategory.Plus.singleFunctor A 0).obj Y) ≅
      (DerivedCategory.Plus.singleFunctor D 0).obj (G.obj (F.obj Y)) :=
    G.rightDerivedFunctorPlus.mapIso
        ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso F 0).app Y).symm ≪≫
      ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso G 0).app (F.obj Y)).symm
  have eY : (G'.rightDerivedFunctorPlus ⋙ F'.rightDerivedFunctorPlus).obj
        ((DerivedCategory.Plus.singleFunctor A 0).obj Y) ≅
      (DerivedCategory.Plus.singleFunctor D 0).obj (F'.obj (G'.obj Y)) :=
    F'.rightDerivedFunctorPlus.mapIso
        ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso G' 0).app Y).symm ≪≫
      ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso F' 0).app (G'.obj Y)).symm
  have hiso : IsIso ((derived F F' G G' τ ε).app
      ((DerivedCategory.Plus.singleFunctor A 0).obj Y)) :=
    isIso_of_isIso_homology_zero _ eX eY h
  have key := (isIso_derived_app_iff_homology F F' G G' τ ε
    ((DerivedCategory.Plus.singleFunctor A 0).obj Y)).mp hiso 0
  exact (NatTrans.isIso_app_iff_of_iso τ (plusSingleHomologyIso Y)).mp key

end DerivedLocal

end Stacks.Cohomology.BaseChange

end
