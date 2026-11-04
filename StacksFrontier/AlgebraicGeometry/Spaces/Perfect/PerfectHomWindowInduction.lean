module

public import StacksFrontier.Algebra.Homology.DerivedCategory.HomWindow
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisExtTag
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal

/-!
# A window of Hom-vanishing against a perfect object, by induction on an algebraic space

Let `X` be a quasi-compact and quasi-separated algebraic space and let `K` be a perfect object of
`D(𝒪_X)`.  [Stacks, Tag 09MB] part (1) asserts that there is a window of degrees `[a, b]` such
that every `L ∈ D_QCoh(𝒪_X)` whose cohomology sheaves vanish in that window admits no nonzero
morphism `K ⟶ L`.  This file reduces that statement to the case of an *affine* algebraic space,
by the induction principle of Stacks 08GP and the Mayer–Vietoris sequence of Stacks 08H9.

The window property is `Stacks.HomWindow.HasHomWindow` of
`StacksFrontier.Algebra.Homology.DerivedCategory.HomWindow`.

## Main definitions

* `AlgebraicGeometry.Space.qcohModules`: quasi-coherence of `𝒪_Y`-modules, as an object property.

## Main results

* `AlgebraicGeometry.Space.hasHomWindow_of_eds`: the window property is inherited across an
  elementary distinguished square — from the open subspace, the étale member and their
  intersection to the ambient space.
* `AlgebraicGeometry.Space.hasHomWindow_of_isPerfect_of_affine`: the window property of perfect
  objects on every quasi-compact quasi-separated algebraic space follows from the window
  property of perfect objects on every affine algebraic space.

## Implementation notes

**The argument.**  The source proves Tag 09MB through the dual `K^∨` and the cohomological
dimension of `X`.  On an algebraic space the dual is not available in this library at the
universes of the small étale site (the internal Hom of Stacks 0A8Z raises the module universe of a
site whose objects lie in `Type (u + 1)`), so the window is built instead by induction on `X`:
the window property is local in the sense that an elementary distinguished square
`(U ⊆ W, V ⟶ W)` with intersection `P` transmits it.  If `[a_U, b_U]`, `[a_V, b_V]` and
`[a_P, b_P]` are windows for the restrictions of `K`, then `[a, b]` with
`a = min(a_U, a_V, a_P - 1)` and `b = max(b_U, b_V, b_P - 1)` is one for `K`: by the exactness of

`Hom(K|_P, L|_P[-1]) ⟶ Hom(K, L) ⟶ Hom(K|_U, L|_U) ⊕ Hom(K|_V, L|_V)`

(Stacks 08H9), `Hom(K, L)` vanishes as soon as the two outer groups do, and restriction along an
étale morphism is exact, so it preserves the vanishing of cohomology sheaves and quasi-coherence
(Stacks 03M0).  The restrictions of `K` are perfect by
`AlgebraicGeometry.Space.isPerfect_etaleModulePullback_standard`.

**The derived categories** are the standard models, as in the Mayer–Vietoris file this consumes.

## References

* [Stacks Project, Tag 09MB](https://stacks.math.columbia.edu/tag/09MB)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08H9](https://stacks.math.columbia.edu/tag/08H9)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated


namespace AlgebraicGeometry.Space

open Stacks.HomWindow

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Quasi-coherence of `𝒪_Y`-modules on an algebraic space `Y`, as an object property, at the
module universe of the structure rings. -/
abbrev qcohModules (Y : AlgebraicSpaces B S hS) : ObjectProperty (Modules.{u, u} B S hS Y.1 Y.2) :=
  SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)

section MayerVietoris

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-- Restriction along an étale morphism of algebraic spaces preserves the hypotheses of a window:
the cohomology sheaves of the restriction of `L` are the restrictions of those of `L`, which are
quasi-coherent if those of `L` are, and vanish where those of `L` do. -/
theorem etaleModulePullback_window_hyps {Y Z : AlgebraicSpaces B S hS} (g : Z ⟶ Y)
    (hg : IsEtale B S hS g.hom) (L : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hL : ∀ i : ℤ, qcohModules B S hS Y
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj L)) :
    (∀ i : ℤ, qcohModules B S hS Z ((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS Z.1 Z.2) i).obj
        ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj L))) ∧
      ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj L) →
        IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Z.1 Z.2) i).obj
          ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj L)) := by
  refine ⟨fun i => ?_, fun i hz => ?_⟩
  · exact (qcohModules B S hS Z).prop_of_iso
      ((Functor.mapDerivedCategoryHomologyIso (etaleModulePullback.{u, u} B S hS g hg) i).app
        L).symm (isQuasicoherentOnSite_etaleModulePullback B S hS g hg _ (hL i))
  · exact ((etaleModulePullback.{u, u} B S hS g hg).map_isZero hz).of_iso
      ((Functor.mapDerivedCategoryHomologyIso (etaleModulePullback.{u, u} B S hS g hg) i).app L)

/-- **A window gives the vanishing of morphisms into a shift.**  If `[a, b]` is a window for `K`
and `L` has quasi-coherent cohomology vanishing in the degrees `n + a, …, n + b`, then every
morphism `K ⟶ L⟦n⟧` vanishes. -/
theorem subsingleton_hom_shift_of_window {Y : AlgebraicSpaces B S hS}
    {K L : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)} {a b : ℤ}
    (h : ∀ L : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2),
      (∀ i : ℤ, qcohModules B S hS Y
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj L)) →
      (∀ i : ℤ, a ≤ i → i ≤ b →
        IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj L)) →
      Subsingleton (K ⟶ L))
    (n : ℤ)
    (hL : ∀ i : ℤ, qcohModules B S hS Y
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj L))
    (hz : ∀ i : ℤ, n + a ≤ i → i ≤ n + b →
      IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj L)) :
    Subsingleton (K ⟶ L⟦n⟧) :=
  h (L⟦n⟧)
    (fun i => (qcohModules B S hS Y).prop_of_iso
      (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).shiftIso n i (n + i)
        rfl).app L).symm (hL (n + i)))
    (fun i hai hib => (hz (n + i) (by omega) (by omega)).of_iso
      (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).shiftIso n i (n + i)
        rfl).app L))

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **The window property crosses an elementary distinguished square.**  Let `(U ⊆ W, V ⟶ W)`
be an elementary distinguished square of algebraic spaces with intersection `P = U ×_W V`, and
let `K` be an object of `D(𝒪_W)`.  If the restrictions of `K` to `U`, to `V` and to `P` have
windows of Hom-vanishing against the objects with quasi-coherent cohomology, so does `K`.

With windows `[a_U, b_U]`, `[a_V, b_V]` and `[a_P, b_P]`, the window
`[min(a_U, a_V, a_P - 1), max(b_U, b_V, b_P - 1)]` works: by the exactness of the Mayer–Vietoris
sequence of Stacks 08H9 at `Hom(K, L)`, a morphism `K ⟶ L` vanishing on `U` and on `V` comes from
`Hom(K|_P, L|_P⟦-1⟧)`, and all three of those groups vanish. -/
theorem hasHomWindow_of_eds (K : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hU : HasHomWindow (qcohModules B S hS (edsOpen B S hS hsq))
      ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj K))
    (hV : HasHomWindow (qcohModules B S hS (edsEtale B S hS hsq))
      ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj K))
    (hP : HasHomWindow (qcohModules B S hS (edsInter B S hS hsq))
      ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj K)) :
    HasHomWindow (qcohModules B S hS W) K := by
  obtain ⟨aU, bU, habU, hU⟩ := hU
  obtain ⟨aV, bV, -, hV⟩ := hV
  obtain ⟨aP, bP, -, hP⟩ := hP
  refine ⟨min aU (min aV (aP - 1)), max bU (max bV (bP - 1)), by omega, fun L hL hz => ?_⟩
  obtain ⟨hLU, hzU⟩ := etaleModulePullback_window_hyps B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq) L hL
  obtain ⟨hLV, hzV⟩ := etaleModulePullback_window_hyps B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq) L hL
  obtain ⟨hLP, hzP⟩ := etaleModulePullback_window_hyps B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq) L hL
  have sU := subsingleton_hom_shift_of_window B S hS hU ((-1 : ℤ) + 1) hLU
    (fun i h₁ h₂ => hzU i (hz i (by omega) (by omega)))
  have sV := subsingleton_hom_shift_of_window B S hS hV ((-1 : ℤ) + 1) hLV
    (fun i h₁ h₂ => hzV i (hz i (by omega) (by omega)))
  have sP := subsingleton_hom_shift_of_window B S hS hP (-1 : ℤ) hLP
    (fun i h₁ h₂ => hzP i (hz i (by omega) (by omega)))
  obtain ⟨δ, -, -, -, -, hex⟩ :=
    mayerVietoris_derivedHom_longExactSequence_of_eds_lowerShriek B S hS hsq K L
  have hexact := (hex (-1)).2.2
  have hsub : Subsingleton (K ⟶ L⟦(-1 : ℤ) + 1⟧) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨zx, hzx⟩ := (hexact x).1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))
    obtain ⟨zy, hzy⟩ := (hexact y).1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))
    rw [← hzx, ← hzy, Subsingleton.elim zx zy]
  exact ((shiftFunctorZero' (DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    ((-1 : ℤ) + 1) (by norm_num)).app L).homToEquiv.subsingleton_congr.1 hsub

end MayerVietoris

section Induction

attribute [local instance] HasDerivedCategory.standard

/-- **The window property of perfect objects, from the affine case.**  Let `X` be a quasi-compact
and quasi-separated algebraic space.  If every perfect object of the derived category of every
affine algebraic space has a window of Hom-vanishing against the objects with quasi-coherent
cohomology, then so does every perfect object of `D(𝒪_X)`.

This is the induction principle of Stacks 08GP run on the property "every perfect object of
`D(𝒪_Y)` has a window", whose inductive step is `hasHomWindow_of_eds`, the restrictions of a
perfect object being perfect (`isPerfect_etaleModulePullback_standard`). -/
theorem hasHomWindow_of_isPerfect_of_affine (hZ : B.Contains (⊤_ Scheme.{u}))
    (haff : ∀ Y : AlgebraicSpaces B S hS, IsAffineSpace B S hS Y.1 →
      ∀ K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2),
        (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect K →
          HasHomWindow (qcohModules B S hS Y) K)
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect K) :
    HasHomWindow (qcohModules B S hS X) K := by
  have key := qcqs_induction_on_self B S hS hZ X hqc hqs
    (fun Y _ => ∀ (hY : IsAlgebraicSpace B S hS Y)
      (K : DerivedCategory (Modules.{u, u} B S hS Y hY)),
        (smallEtaleRingedSite B S hS Y hY).IsPerfect K →
          HasHomWindow (qcohModules B S hS ⟨Y, hY⟩) K)
    (fun V hV hY K hK => haff ⟨V.1.left.1, hY⟩ hV K hK)
    (fun W V U f _ hsq _ _ _ _ hPU hPV hPP hY K hK => by
      have hsq' : IsElementaryDistinguishedSquare B S hS (W.1.left.2) U f := hsq
      have hp := fun {Z} g hg => isPerfect_etaleModulePullback_standard B S hS (Y := Z) g hg K hK
      exact hasHomWindow_of_eds B S hS (W := ⟨W.1.left.1, hY⟩) hsq' K
        (hPU _ _ (hp _ (isEtale_edsOpenHom B S hS hsq')))
        (hPV _ _ (hp _ (isEtale_edsEtaleHom B S hS hsq')))
        (hPP _ _ (hp _ (isEtale_edsInterHom B S hS hsq'))))
  exact key X.2 K hK

end Induction

end AlgebraicGeometry.Space

end
