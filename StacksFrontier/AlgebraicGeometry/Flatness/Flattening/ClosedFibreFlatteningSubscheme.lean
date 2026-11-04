module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeFactorization
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LocalFlatteningSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.RingTheory.Henselian.EtaleLifting
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange

/-!
# Flattening a module along a subset of the closed fibre

Let `A` be a henselian local ring, let `f : X ⟶ Spec A` be locally of finite type, let `F` be a
finite type quasi-coherent `O_X`-module and let `E` be an arbitrary subset of the fibre of `f`
over the closed point of `Spec A`. There is a closed subscheme of `Spec A` which detects, after
every pointed base change `(T, t) ⟶ (Spec A, closed point)`, flatness of the pulled back module
at every point of `X ×_{Spec A} T` lying over a point of `E`: the condition holds exactly when
`Spec O_{T, t} ⟶ Spec A` factors through that closed subscheme.

## Main results

* `AlgebraicGeometry.exists_closedSubscheme_flatOverAt_iff_factors`: **Stacks Tag 05PI**, the
  closed flattening subscheme.

## Implementation notes

The closed subscheme is the supremum of the ideal sheaves produced, one for each point of `E`,
by the pointwise statement
`AlgebraicGeometry.exists_closedSubscheme_flatOverAt_iff_factorStalk`, **Stacks Tag 05PH**;
the supremum of ideal sheaves corresponds to the intersection of closed subschemes, which is
how the source forms `Z` from the `Z_x`. Both directions are read off from
`AlgebraicGeometry.factorsThrough_ideal_iff_ideal_le_ker`: a morphism factors through the closed
subscheme of an ideal sheaf exactly when that ideal sheaf is contained in the morphism's
kernel, so factoring through the supremum is factoring through every member.

A henselian local base is presented intrinsically for the pointwise statement: the local ring of
`Spec A` at the closed point is henselian because it is isomorphic to `A`
(`HenselianLocalRing.of_ringEquiv` applied to
`AlgebraicGeometry.stalkClosedPointIso`), and `(Spec A).fromSpecStalk` at the closed point is an
isomorphism by `AlgebraicGeometry.Spec_stalkClosedPointIso`.

## References

* [Stacks Project, Tag 05PI](https://stacks.math.columbia.edu/tag/05PI)
* [Stacks Project, Tag 05PH](https://stacks.math.columbia.edu/tag/05PH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The local ring of the spectrum of a henselian local ring at its closed point is
henselian. -/
lemma henselianLocalRing_stalk_closedPoint (A : Type u) [CommRing A]
    [HenselianLocalRing A] :
    HenselianLocalRing ((Spec (.of A)).presheaf.stalk (IsLocalRing.closedPoint A)) :=
  HenselianLocalRing.of_ringEquiv
    (stalkClosedPointIso (.of A)).commRingCatIsoToRingEquiv.symm

/-- **Stacks Project, Tag 05PI.** Flatness of a finite type quasi-coherent module along an
arbitrary subset `E` of the closed fibre, after an arbitrary pointed base change of a henselian
local base, is detected by a closed subscheme of that base: the flatness condition for a pointed
scheme `(T, t)` over `(Spec A, closed point)` holds exactly when `Spec O_{T,t} ⟶ Spec A` factors
through the closed subscheme. -/
@[stacks 05PI "closed flattening subscheme"]
theorem exists_closedSubscheme_flatOverAt_iff_factors
    (A : Type u) [CommRing A] [HenselianLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (E : Set (f.fiber (IsLocalRing.closedPoint A))) :
    ∃ I : (Spec (.of A)).IdealSheafData,
      ∀ (T : Scheme.{u}) (g : T ⟶ Spec (.of A)) (t : T)
        (_ : g t = IsLocalRing.closedPoint A),
        (∀ y : (pullback f g : Scheme.{u}),
          (pullback.snd f g) y = t →
          (pullback.fst f g) y ∈
            (f.fiberι (IsLocalRing.closedPoint A)) '' E →
          AlgebraicGeometry.IsFlatOverAt (pullback.snd f g).toLRSHom.toShHom
            ((Scheme.Modules.pullback (pullback.fst f g)).obj F) y) ↔
        ∃ h : Spec (T.presheaf.stalk t) ⟶ I.subscheme,
          h ≫ I.subschemeι = T.fromSpecStalk t ≫ g := by
  classical
  let s : Spec (.of A) := IsLocalRing.closedPoint A
  have : IsIso ((Spec (.of A)).fromSpecStalk s) := by
    rw [← AlgebraicGeometry.Spec_stalkClosedPointIso (.of A)]
    infer_instance
  have := henselianLocalRing_stalk_closedPoint A
  let P (z : E) :=
    exists_closedSubscheme_flatOverAt_iff_factorStalk
      f F (f.fiberι s z) s (f.apply_fiberι s z)
  let J : E → (Spec (.of A)).IdealSheafData := fun z => Classical.choose (P z)
  have hJ (z : E) : ∀ {T : Scheme.{u}} (g : T ⟶ Spec (.of A)) (t : T) (_ : g t = s),
      (∀ y : pullback (C := Scheme.{u}) f g,
        (pullback.snd f g) y = t →
        (pullback.fst f g) y = f.fiberι s z →
        AlgebraicGeometry.IsFlatOverAt (pullback.snd f g).toLRSHom.toShHom
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F) y) ↔
      ∃ h : Spec (T.presheaf.stalk t) ⟶ (J z).subscheme,
        h ≫ (J z).subschemeι = T.fromSpecStalk t ≫ g :=
    Classical.choose_spec (P z)
  let I : (Spec (.of A)).IdealSheafData := ⨆ z : E, J z
  refine ⟨I, fun T g t ht => ?_⟩
  rw [factorsThrough_ideal_iff_ideal_le_ker]
  refine ⟨fun hflat => iSup_le fun z => (factorsThrough_ideal_iff_ideal_le_ker (J z) _).mp
    ((hJ z g t ht).mp fun y hy hzy => hflat y hy ⟨z.1, z.2, hzy.symm⟩), ?_⟩
  rintro h y hy ⟨w, hw, hwy⟩
  exact (hJ ⟨w, hw⟩ g t ht).mpr ((factorsThrough_ideal_iff_ideal_le_ker (J ⟨w, hw⟩) _).mpr
    ((le_iSup J ⟨w, hw⟩).trans h)) y hy hwy.symm

end AlgebraicGeometry

end
