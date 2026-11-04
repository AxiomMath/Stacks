module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.RestrictToDenseOpen
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.AlgebraicClosureBaseChange
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.AssertionsExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition

/-!
# Vanishing of the cohomology of a sheaf supported on finitely many points

Let `i : Z ⟶ X` be a closed immersion with open complement `j : U ⟶ X`, and let `F` be an abelian
sheaf on `X_étale` whose restriction to `U` vanishes. By the localization sequence of Stacks Tag
095L, `F` is then `i_* i⁻¹ F`. If `Z` is affine, all of its points are closed and all of its
residue fields are separably closed — for instance if `Z` is a finite set of rational points over a
separably closed field — then the higher direct images of `i` vanish (Tag 03QP) and so does the
higher cohomology of `Z` (Tag 09AY), so `H^q(X, F) = 0` for `q > 0`.

This is the input of Stacks Tag 0GJA about the closed part of the localization sequence, in the
form which applies after any base change of the situation.

## Main results

* `Stacks.EtaleCohomology.isIso_openClosedShortComplex_g_of_isZero`: `F ≅ i_* i⁻¹ F` when
  `j⁻¹ F = 0`.
* `Stacks.EtaleCohomology.subsingleton_sheafH_of_isZero_etaleRestriction_of_affine_closedPoints`:
  `H^q(X, F) = 0` for `q > 0` when `j⁻¹ F = 0` and `Z` is as above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section Support

variable {X Z U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ)

/-- A sheaf whose restriction to the open complement vanishes is the direct image of its inverse
image to the closed part. -/
theorem isIso_openClosedShortComplex_g_of_isZero
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsZero ((etaleRestriction.{u, u + 1} j).obj F)) :
    IsIso (openClosedShortComplex.{u, u + 1} i j hij F).g := by
  have hS := openClosedShortComplex_shortExact.{u, u + 1} i j hij F
  have h₁ : IsZero (openClosedShortComplex.{u, u + 1} i j hij F).X₁ :=
    (extensionByZero.{u, u + 1} j).map_isZero hF
  have : Mono (openClosedShortComplex.{u, u + 1} i j hij F).g :=
    hS.exact.mono_g (h₁.eq_of_src _ _)
  have := hS.epi_g
  exact isIso_of_mono_of_epi _

include hij in
/-- **Vanishing of higher cohomology of a sheaf supported on a nice closed subscheme.** -/
theorem subsingleton_sheafH_of_isZero_etaleRestriction_of_affine_closedPoints [IsAffine Z]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hclosed : ∀ z : Z, IsClosed ({z} : Set Z))
    (hsep : ∀ z : Z, IsSepClosed (Z.residueField z))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsZero ((etaleRestriction.{u, u + 1} j).obj F)) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} F q) := by
  have := isIso_openClosedShortComplex_g_of_isZero i j hij F hF
  have h := subsingleton_etaleCohomology_directImage_of_closed_points i hclosed hsep
    ((etaleAbelianInverseImage.{u, u + 1} i).obj F) q hq
  let e := (Sheaf.functorH.{u + 1, u + 1, u, u + 1} X.smallEtaleTopology q).mapIso
    (asIso (openClosedShortComplex.{u, u + 1} i j hij F).g)
  have h' : Subsingleton ((Sheaf.functorH.{u + 1, u + 1, u, u + 1} X.smallEtaleTopology q).obj
      (openClosedShortComplex.{u, u + 1} i j hij F).X₃) := h
  exact e.addCommGroupIsoToAddEquiv.injective.subsingleton

end Support

section FiniteOverField

/-- **A scheme finite over an algebraically closed field is a finite set of rational points**: it
is affine, all of its points are closed, and all of its residue fields are separably closed. -/
theorem isAffine_isClosed_isSepClosed_of_isFinite {K : Type u} [Field K] [IsAlgClosed K]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of K)) [IsFinite g] :
    IsAffine Z ∧ (∀ z : Z, IsClosed ({z} : Set Z)) ∧
      ∀ z : Z, IsSepClosed (Z.residueField z) := by
  have : DiscreteTopology Z := discreteTopology_of_isFinite_over_field K g
  have hcl : ∀ z : Z, IsClosed ({z} : Set Z) := fun z => isClosed_discrete _
  refine ⟨isAffine_of_isAffineHom g, hcl, fun z => ?_⟩
  have : IsAlgClosed (Z.residueField z) :=
    IsAlgClosed.of_ringEquiv K _ (residueFieldIsoBase g z (hcl z)).commRingCatIsoToRingEquiv.symm
  infer_instance

end FiniteOverField

section BaseChange

variable {X Z U Y : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ)

include hij in
/-- The base change of a closed immersion and of the open immersion of its complement are again
complementary. -/
theorem range_pullback_snd_compl (a : Y ⟶ X) :
    Set.range (pullback.snd j a).base = (Set.range (pullback.snd i a).base)ᶜ := by
  rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, hij, Set.preimage_compl]

/-- The vanishing of the restriction to the open complement survives inverse image. -/
theorem isZero_etaleRestriction_inverseImage (a : Y ⟶ X)
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hQ : IsZero ((etaleRestriction.{u, u + 1} j).obj Q)) :
    IsZero ((etaleRestriction.{u, u + 1} (pullback.snd j a)).obj
      ((etaleAbelianInverseImage.{u, u + 1} a).obj Q)) := by
  have h1 : IsZero ((etaleAbelianInverseImage.{u, u + 1} j).obj Q) :=
    hQ.of_iso ((etaleAbelianInverseImageRestrictionIso.{u, u + 1} j).app Q)
  have h2 : IsZero ((etaleAbelianInverseImage.{u, u + 1} (pullback.fst j a)).obj
      ((etaleAbelianInverseImage.{u, u + 1} j).obj Q)) :=
    (etaleAbelianInverseImage.{u, u + 1} (pullback.fst j a)).map_isZero h1
  have h3 : IsZero ((etaleAbelianInverseImage.{u, u + 1} (pullback.snd j a ≫ a)).obj Q) :=
    h2.of_iso ((etaleAbelianInverseImageCompIso'.{u, u + 1} (pullback.fst j a) j
      (pullback.snd j a ≫ a) pullback.condition.symm).app Q)
  have h4 : IsZero ((etaleAbelianInverseImage.{u, u + 1} (pullback.snd j a)).obj
      ((etaleAbelianInverseImage.{u, u + 1} a).obj Q)) :=
    h3.of_iso ((etaleAbelianInverseImageCompIso'.{u, u + 1} (pullback.snd j a) a
      (pullback.snd j a ≫ a) rfl).app Q).symm
  exact h4.of_iso ((etaleAbelianInverseImageRestrictionIso.{u, u + 1} (pullback.snd j a)).app
    _).symm

include hij in
/-- **Vanishing of higher cohomology after inverse image**, when the base change of the closed
part is finite over an algebraically closed field. -/
theorem subsingleton_sheafH_inverseImage_of_isZero_etaleRestriction (a : Y ⟶ X)
    {K : Type u} [Field K] [IsAlgClosed K] (g : pullback i a ⟶ Spec (.of K)) [IsFinite g]
    [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hQ : IsZero ((etaleRestriction.{u, u + 1} j).obj Q)) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} ((etaleAbelianInverseImage.{u, u + 1} a).obj Q) q) := by
  obtain ⟨hA, hcl, hsep⟩ := isAffine_isClosed_isSepClosed_of_isFinite g
  let : HasExt.{u + 1} (Sheaf (pullback i a).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    hasExt_of_enoughInjectives.{u + 1} _
  exact subsingleton_sheafH_of_isZero_etaleRestriction_of_affine_closedPoints (pullback.snd i a)
    (pullback.snd j a)
    (range_pullback_snd_compl i j hij a) hcl hsep _
    (isZero_etaleRestriction_inverseImage j a Q hQ) q hq

end BaseChange

section Assertions

variable {k : Type u} [Field k] [IsAlgClosed k] {X Z U : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ) [IsFinite (i ≫ f)]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The base change of the closed part to a scalar extension is finite over the extended field. -/
theorem isFinite_pullback_scalarExtension (k' : Type u) [Field k'] [Algebra k k'] :
    IsFinite (pullback.snd i (scalarExtensionFst k k' f) ≫
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback i (scalarExtensionFst k k' f)).paste_vert
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))))
    (inferInstance : IsFinite (i ≫ f))

/-- The base change of the closed part to an open subscheme is finite over the field. -/
theorem isFinite_pullback_opens (V : X.Opens) : IsFinite (pullback.fst i V.ι ≫ i ≫ f) := by
  have : DiscreteTopology Z := discreteTopology_of_isFinite_over_field k (i ≫ f)
  have : IsClosedImmersion (pullback.fst i V.ι) :=
    IsClosedImmersion.of_isPreimmersion _ (isClosed_discrete _)
  infer_instance

include hij in
/-- **The eight assertions of Tag 03SC for a sheaf supported on the closed part.** Let `i : Z ⟶ X`
be a closed immersion over `k` with `Z` finite over `k`, and `Q` a sheaf on `X_étale` whose
restriction to the complement of `Z` vanishes. If `H⁰(X, Q)` is finite and restriction to every
scalar extension by an algebraically closed field is bijective in degree zero, the eight
assertions hold for `Q`. -/
theorem TorsionCurveAssertions.of_isZero_etaleRestriction
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hQ : IsZero ((etaleRestriction.{u, u + 1} j).obj Q))
    (hfin : Finite (Sheaf.H.{u + 1} Q 0))
    (h0 : ∀ (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
      [HasExt.{u + 1} (Sheaf (scalarExtension k k' f).smallEtaleTopology AddCommGrpCat.{u + 1})],
      Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
        (scalarExtensionFst k k' f) Q 0)) :
    TorsionCurveAssertions f Q := by
  obtain ⟨hA, hcl, hsep⟩ := isAffine_isClosed_isSepClosed_of_isFinite (i ≫ f)
  let : HasExt.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    hasExt_of_enoughInjectives.{u + 1} _
  have hv : ∀ q, 0 < q → Subsingleton (Sheaf.H.{u + 1} Q q) := fun q hq =>
    subsingleton_sheafH_of_isZero_etaleRestriction_of_affine_closedPoints i j hij hcl hsep Q hQ q hq
  refine TorsionCurveAssertions.of_cohomology_concentrated f hv hfin (fun k' _ _ _ _ q => ?_)
    (fun V _ => ?_)
  · rcases Nat.eq_zero_or_pos q with rfl | hq
    · exact h0 k'
    · have := hv q hq
      have := isFinite_pullback_scalarExtension f i k'
      have := subsingleton_sheafH_inverseImage_of_isZero_etaleRestriction i j hij
        (scalarExtensionFst k k' f) (K := k') (pullback.snd i (scalarExtensionFst k k' f) ≫
          pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) Q hQ q hq
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  · have := isFinite_pullback_opens f i V
    exact subsingleton_sheafH_inverseImage_of_isZero_etaleRestriction i j hij V.ι (K := k)
      (pullback.fst i V.ι ≫ i ≫ f) Q hQ 2 two_pos

end Assertions

end Stacks.EtaleCohomology

end
