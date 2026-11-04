module

public import StacksFrontier.AlgebraicGeometry.Duality.CurveFamilyDualizingSheaf
public import StacksFrontier.AlgebraicGeometry.FiberRank.FlatFibreFiniteFree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.InvertibleOfStalkRankOne
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOneLocal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence

/-!
# The relative dualizing sheaf of a family of Gorenstein curves is invertible

Let `S` be Noetherian and `f : X ⟶ S` proper, flat and Cohen–Macaulay with one-dimensional
fibres, so that `f^!𝒪_S = ω_{X/S}[1]` for a coherent `𝒪_X`-module `ω_{X/S}`, flat over `S`
([Stacks, Tag 0BV8]). If the dualizing sheaf of every fibre `X_s` is invertible — as it is for
connected one-dimensional nodal fibres — then `ω_{X/S}` is invertible.

The restriction of `ω_{X/S}` to `X_s` is `ω_{X_s}`
(`Stacks.Duality.nonempty_pullback_relativeDualizingSheaf_iso`), whose stalks are free of rank one;
as `ω_{X/S}` is flat over `S`, the fibrewise criterion for flatness ([Stacks, Tag 039C]) makes its
stalks flat, hence free, over the local rings of `X`, and the rank is read on the fibre.

## Main results

* `Stacks.Duality.nonempty_linearEquiv_of_tensor_linearEquiv`: a finite flat module over a local
  ring whose base change to a nonzero algebra is free of rank one is free of rank one.
* `Stacks.Duality.isInvertibleModule_relativeDualizingSheaf`: `ω_{X/S}` is invertible.

## References

* [Stacks Project, Tag 0BV8](https://stacks.math.columbia.edu/tag/0BV8)
* [Stacks Project, Tag 039C](https://stacks.math.columbia.edu/tag/039C)
* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace Stacks.Duality

/-- **A finite flat module over a local ring whose base change to a nonzero algebra is free of
rank one is free of rank one.** -/
theorem nonempty_linearEquiv_of_tensor_linearEquiv {A B M : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [Nontrivial B] [Algebra A B] [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Flat A M] (e : B ⊗[A] M ≃ₗ[B] B) : Nonempty (M ≃ₗ[A] A) := by
  have : Module.Free A M := Module.free_of_flat_of_isLocalRing
  have h1 : Module.finrank B (B ⊗[A] M) = 1 := by
    rw [e.finrank_eq, Module.finrank_self]
  rw [Module.finrank_baseChange] at h1
  exact ⟨(Module.finBasisOfFinrankEq A M h1).equivFun ≪≫ₗ LinearEquiv.funUnique (Fin 1) A A⟩

open DerivedPushforward

variable {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f] [Flat f]

/-- The underlying morphism `f` of `ftsHomToBase f` is flat. -/
instance flat_ftsHomToBase_left : Flat (ftsHomToBase f).left := inferInstanceAs (Flat f)

/-- A linear equivalence for one `R`-module structure on `M` is also one for any equal
structure. -/
private theorem nonempty_linearEquiv_of_moduleEq {R M N : Type*} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R N] {i₁ i₂ : Module R M} (h : i₁ = i₂)
    (e : @LinearEquiv R R _ _ (RingHom.id R) (RingHom.id R) _ _ M N _ _ i₁ _) :
    Nonempty (@LinearEquiv R R _ _ (RingHom.id R) (RingHom.id R) _ _ M N _ _ i₂ _) := by
  subst h
  exact ⟨e⟩

/-- The relative dualizing sheaf `ω_{X/S}` of a proper morphism to a Noetherian scheme is
coherent. -/
private theorem isCoherent_relativeDualizingSheaf :
    (relativeDualizingSheaf (ftsHomToBase f) (properCompactification (ftsHomToBase f)) 1 :
      X.Modules).IsCoherent := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := locallyOfFinitePresentation_left (ftsHomToBase f)
  exact (derivedCategoryBBounded_upperShriek_derivedStructureSheaf_of_charts (ftsHomToBase f)
    (properCompactification (ftsHomToBase f)) (fun x => by
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
        S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hxV (f ⁻¹ᵁ V).isOpen
      have hft : (f.appLE V U hUV).hom.FiniteType :=
        (locallyOfFiniteType_left (ftsHomToBase f)).finiteType_appLE hV hU hUV
      let p := (Dualizing.nonempty_polynomialPresentation _ hft).some
      exact ⟨U, hU, V, hV, hUV, hxU, p, upperShriekStructureSheafCharts (ftsHomToBase f)
        (properCompactification (ftsHomToBase f)) V hV U hU hUV p⟩)).2 _

/-- Under the hypotheses of `isInvertibleModule_relativeDualizingSheaf`, the restriction of
`ω_{X/S}` to the fibre `X_s` is invertible. -/
private theorem isInvertible_pullback_relativeDualizingSheaf
    (hCM : f.IsCohenMacaulay (isLocallyNoetherian_fiber_left (ftsHomToBase f)))
    (hd : ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = ((1 : ℕ) : WithBot ℕ∞))
    (hfib : ∀ (K : Type u) [Field K] (X' : Scheme.{u}) (y : Spec (CommRingCat.of K) ⟶ S)
      (g' : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)) [IsProper f'], IsPullback g' f' f y →
        SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 (dualizingSheafOverField f'))
    (s : S) :
    SheafOfModules.IsInvertible (f.fiber s).presheaf (f.fiber s).ringCatSheaf.2
      ((Scheme.Modules.pullback (f.fiberι s)).obj (relativeDualizingSheaf (ftsHomToBase f)
        (properCompactification (ftsHomToBase f)) 1)) := by
  have sq : IsPullback (f.fiberι s) (f.fiberToSpecResidueField s :
      f.fiber s ⟶ Spec (CommRingCat.of (S.residueField s))) f (S.fromSpecResidueField s) :=
    IsPullback.of_hasPullback f (S.fromSpecResidueField s)
  have hP : IsProper (f.fiberToSpecResidueField s :
      f.fiber s ⟶ Spec (CommRingCat.of (S.residueField s))) :=
    MorphismProperty.of_isPullback (P := @IsProper) sq inferInstance
  obtain ⟨e⟩ := nonempty_pullback_relativeDualizingSheaf_iso f hCM hd sq (hf' := hP)
  exact @Stacks.SheafOfModules.isInvertible_of_iso _ _ _ _ _ _ _ _ _ e.symm
    (@hfib (S.residueField s) _ _ _ _ _ hP sq)

/-- Under the hypotheses of `isInvertibleModule_relativeDualizingSheaf`, every stalk of
`ω_{X/S}` is free of rank one. -/
private theorem nonempty_stalk_linearEquiv_relativeDualizingSheaf
    (hCM : f.IsCohenMacaulay (isLocallyNoetherian_fiber_left (ftsHomToBase f)))
    (hd : ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = ((1 : ℕ) : WithBot ℕ∞))
    (hfib : ∀ (K : Type u) [Field K] (X' : Scheme.{u}) (y : Spec (CommRingCat.of K) ⟶ S)
      (g' : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)) [IsProper f'], IsPullback g' f' f y →
        SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 (dualizingSheafOverField f'))
    (x : X) :
    letI : Module (X.presheaf.stalk x) (ToType ((relativeDualizingSheaf (ftsHomToBase f)
        (properCompactification (ftsHomToBase f)) 1).presheaf.stalk x)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) (relativeDualizingSheaf (ftsHomToBase f)
          (properCompactification (ftsHomToBase f)) 1).val x
    Nonempty (ToType ((relativeDualizingSheaf (ftsHomToBase f)
      (properCompactification (ftsHomToBase f)) 1).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
        X.presheaf.stalk x) := by
  set ω : X.Modules :=
    relativeDualizingSheaf (ftsHomToBase f) (properCompactification (ftsHomToBase f)) 1
  have : ω.IsCoherent := isCoherent_relativeDualizingSheaf f
  have hflat : IsFlatOver f.toLRSHom.toShHom ω :=
    isFlatOver_homology_of_isCohenMacaulay (upperShriekStructureSheafCharts (ftsHomToBase f)
      (properCompactification (ftsHomToBase f))) hCM (-1)
  have : ω.IsFinitePresentation := isFinitePresentation_of_isCoherent ω
  let s := f x
  have := isInvertible_pullback_relativeDualizingSheaf f hCM hd hfib s
  obtain ⟨eℓ⟩ := Stacks.SheafOfModules.nonempty_grpStalk_linearEquiv (f.fiber s).toRingedSpace
    ((Scheme.Modules.pullback (f.fiberι s)).obj ω) (f.asFiber x)
  obtain ⟨et⟩ := Stacks.Divisors.exists_modulePullbackStalkLinearEquiv_of_eq (f.fiberι s) ω
    (f.asFiber x) x (f.fiberι_asFiber x)
  obtain ⟨eℓ'⟩ := nonempty_linearEquiv_of_moduleEq (Stacks.SheafOfModules.stalkModule_eq
    (f.fiber s).toRingedSpace ((Scheme.Modules.pullback (f.fiberι s)).obj ω).val (f.asFiber x)) eℓ
  let e₂ := et.symm ≪≫ₗ eℓ'
  have hfibflat :
      let := Stacks.Flatness.stalkModule
        ((Scheme.Modules.pullback (f.fiberι (f x))).obj ω) (f.asFiber x)
      Module.Flat (ToType ((f.fiber (f x)).presheaf.stalk (f.asFiber x)))
        (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          ((Scheme.Modules.pullback (f.fiberι (f x))).obj ω).val.presheaf (f.asFiber x))) :=
    Module.Flat.of_linearEquiv eℓ'
  have : IsLocalRing (ToType (X.presheaf.stalk x)) := X.isLocalRing x
  have hx : ∃ a : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ω.val.presheaf x, a ≠ 0 := by
    by_contra! hn
    have : Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ω.val.presheaf x) :=
      ⟨fun a b => by rw [hn a, hn b]⟩
    exact not_subsingleton (ToType ((f.fiber s).presheaf.stalk (f.asFiber x)))
      e₂.symm.toEquiv.subsingleton
  have := Scheme.Modules.flat_stalk_of_isFlatOverAt_of_flat_fiber_stalk f ω x hx (hflat x)
    hfibflat
  have : _root_.SheafOfModules.IsFinitePresentation.{u, u, u} ω := ‹_›
  have : _root_.SheafOfModules.IsFiniteType.{u, u, u} ω :=
    _root_.SheafOfModules.instIsFiniteTypeOfIsFinitePresentation ω
  have : Module.Finite (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ω.val.presheaf x)) :=
    _root_.SheafOfModules.finite_stalk X.sheaf ω x
  let : Algebra (X.presheaf.stalk x) ((f.fiber s).presheaf.stalk (f.asFiber x)) :=
    (((f.fiberι s).stalkMap (f.asFiber x)).hom.comp
      (X.presheaf.stalkCongr (.of_eq (f.fiberι_asFiber x).symm)).hom.hom).toAlgebra
  exact (nonempty_linearEquiv_of_tensor_linearEquiv e₂ :)

/-- **The relative dualizing sheaf of a family of curves with invertible fibre dualizing sheaves
is invertible.** Let `f : X ⟶ S` be proper, flat and Cohen–Macaulay with one-dimensional fibres
over a Noetherian scheme, and suppose the dualizing sheaf of every fibre `X_s` is invertible. Then
`ω_{X/S} = H^{-1}(f^!𝒪_S)` is an invertible `𝒪_X`-module. -/
theorem isInvertibleModule_relativeDualizingSheaf
    (hCM : f.IsCohenMacaulay (isLocallyNoetherian_fiber_left (ftsHomToBase f)))
    (hd : ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = ((1 : ℕ) : WithBot ℕ∞))
    (hfib : ∀ (K : Type u) [Field K] (X' : Scheme.{u}) (y : Spec (CommRingCat.of K) ⟶ S)
      (g' : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)) [IsProper f'], IsPullback g' f' f y →
        SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 (dualizingSheafOverField f')) :
    Stacks.Ample.IsInvertibleModule X
      (relativeDualizingSheaf (ftsHomToBase f) (properCompactification (ftsHomToBase f)) 1) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact Scheme.Modules.isInvertibleModule_of_forall_stalk_linearEquiv _
    (isCoherent_relativeDualizingSheaf f)
    (nonempty_stalk_linearEquiv_relativeDualizingSheaf f hCM hd hfib)

end Stacks.Duality

end
