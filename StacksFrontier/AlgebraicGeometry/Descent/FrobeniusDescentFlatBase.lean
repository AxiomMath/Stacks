module

public import StacksFrontier.AlgebraicGeometry.BirationalDenseOpenIso.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.TowerBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusDescentNormalBase
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GraphConstruction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.FlatNormalBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Components
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.FiniteNearGenericPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Normalization

/-!
# The essential-image half of Stacks Tag 0EXH for a flat family over a reduced base

Let `f : X ⟶ Y` be flat, proper and surjective, with `Y` reduced and of finite type over a field,
and suppose `f_*𝒪_X = 𝒪_Y` over a dense open `V ⊆ Y`. The proof of Stacks Tag 0EXH replaces `Y`
by its normalization `ν : Y^ν ⟶ Y` (Stacks Tags 035E, 035S, 035B), which is finite, surjective and
an isomorphism over a dense open; the base change `X ×_Y Y^ν ⟶ Y^ν` is again flat, proper and
surjective, and `f_*𝒪 = 𝒪` holds for it over a dense open, hence everywhere because `Y^ν` is
normal ("the Stein factorization has to be an isomorphism in this case"). Then the normal case
applies. This file carries out that replacement; the descent back along `ν` is the h-descent of
Stacks Tag 0EXE.

## Main results

* `AlgebraicGeometry.isIso_c_morphismRestrict_iff`: `f_*𝒪 = 𝒪` over an open, read on sections.
* `AlgebraicGeometry.isIso_c_morphismRestrict_of_isPullback`: it passes to a base change along a
  morphism that is an isomorphism over the open.
* `AlgebraicGeometry.dense_preimage_of_isBirational`.
* `AlgebraicGeometry.Scheme.Vect.descendsAfterFrobenius_normalization_pullback`.

## References

* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **`f_*𝒪_X = 𝒪_Y` over an open `U`, read on sections**: it holds if and only if
`Γ(Y, W) ⟶ Γ(X, f⁻¹W)` is an isomorphism for every open `W ⊆ U`. -/
theorem isIso_c_morphismRestrict_iff (f : X ⟶ Y) (U : Y.Opens) :
    IsIso (f ∣_ U).c ↔ ∀ W : Y.Opens, W ≤ U → IsIso (f.app W) := by
  have hrestr : ∀ W' : U.toScheme.Opens,
      IsIso ((f ∣_ U).app W') ↔ IsIso (f.app (U.ι ''ᵁ W')) := by
    intro W'
    rw [ConcreteCategory.isIso_iff_bijective, ConcreteCategory.isIso_iff_bijective]
    let ρ := X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U W')).op
    have hρ : Function.Bijective ρ := (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
    have h' : ⇑((f ∣_ U).app W') = ρ ∘ f.app (U.ι ''ᵁ W') := funext fun x ↦
      congrArg (fun φ : Γ(Y, U.ι ''ᵁ W') ⟶ Γ(X, (f ⁻¹ᵁ U).ι ''ᵁ (f ∣_ U) ⁻¹ᵁ W') ↦ φ x)
        (morphismRestrict_app f U W')
    rw [h']
    exact Function.Bijective.of_comp_iff' hρ _
  constructor
  · intro hc W hW
    have hW' : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr hW]
    have := (hrestr (U.ι ⁻¹ᵁ W)).mp (NatIso.isIso_app_of_isIso _ (op (U.ι ⁻¹ᵁ W)))
    rwa [hW'] at this
  · intro h
    have : ∀ W' : (U.toScheme.Opens)ᵒᵖ, IsIso ((f ∣_ U).c.app W') := fun W' ↦
      (hrestr W'.unop).mpr (h _ (Scheme.Opens.ι_image_le _ _))
    exact NatIso.isIso_of_isIso_app _

/-- **`f_*𝒪 = 𝒪` over an open passes to a base change along a morphism which is an isomorphism
over that open.** -/
theorem isIso_c_morphismRestrict_of_isPullback {X' Y' : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) [QuasiCompact f]
    [QuasiSeparated f] (U : Y.Opens) [IsIso (g ∣_ U)] (h : IsIso (f ∣_ U).c) :
    IsIso (f' ∣_ (g ⁻¹ᵁ U)).c := by
  have : IsIso (g.resLE U (g ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  exact Stacks.AlgebraicGeometry.isIso_c_of_isPullback_of_flat
    (Stacks.Chow.isPullback_morphismRestrict_of_isPullback sq U) h

/-- **The preimage of a dense open under a birational morphism is dense**, for schemes with
finitely many irreducible components. -/
theorem dense_preimage_of_isBirational (f : X ⟶ Y) [Finite (irreducibleComponents X)]
    [Finite (irreducibleComponents Y)] (hf : IsBirational f) (U : Y.Opens)
    (hU : Dense (U : Set Y)) : Dense ((f ⁻¹ᵁ U : X.Opens) : Set X) := by
  have hgen : genericPoints X ⊆ (f ⁻¹ᵁ U : X.Opens) := by
    rw [← preimage_genericPoints_eq_genericPoints_of_isBirational f hf]
    exact Set.preimage_mono (genericPoints_subset_of_dense_isOpen (Set.toFinite _) U.isOpen hU)
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro x
  exact closure_mono hgen (by rw [genericPoints.closure]; trivial)

variable {p : ℕ} [Fact p.Prime]

open Scheme.Vect in
/-- **The essential-image half of Stacks Tag 0EXH for the base change of a flat family to the
normalization.** Let `Y` be reduced, quasi-compact and locally of finite type over a field, and
let `f : X ⟶ Y` be flat, proper and surjective with `f_*𝒪_X = 𝒪_Y` over a dense open. Then the
conclusion of Stacks Tag 0EXH holds for the base change of `f` to the normalization
`ν : Y^ν ⟶ Y` and the pullback of any `ℰ` satisfying the fibre condition. -/
theorem descendsAfterFrobenius_normalization_pullback (k : Type u) [Field k]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] [CompactSpace Y] [IsReduced Y] (f : X ⟶ Y)
    [Flat f] [IsProper f] [Surjective f] (V : Y.Opens) (hV : Dense (V : Set Y))
    (hfV : IsIso (f ∣_ V).c) (hX : IsInCharacteristic X p) (E : X.Vect)
    (hE : IsFreeOnReducedFibresAfterFrobenius f p hX E) :
    DescendsAfterFrobenius (pullback.snd f (normalizationOverField k s)) p
      (isInCharacteristic_of_hom (pullback.fst f (normalizationOverField k s)) p hX)
      ((Scheme.Vect.pullback (pullback.fst f (normalizationOverField k s))).obj E) := by
  have hfin := finite_irreducibleComponents_of_locallyOfFiniteType k s
  let ν := normalizationOverField k s
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsNoetherian Y := {}
  have : IsFinite ν := isFinite_normalizationOverField k s
  have : IsIntegralHom ν := Scheme.isIntegralHom_normalization Y hfin
  have : IsLocallyNoetherian (Y.normalizationScheme hfin) :=
    LocallyOfFiniteType.isLocallyNoetherian ν
  have : CompactSpace ↑(Y.normalizationScheme hfin) :=
    QuasiCompact.compactSpace_of_compactSpace ν
  have : IsNoetherian (Y.normalizationScheme hfin) := {}
  have : IsNormal (Y.normalizationScheme hfin) := Scheme.isNormal_normalizationScheme Y hfin
  have : Finite (irreducibleComponents Y) :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).to_subtype
  have : Finite (irreducibleComponents (Y.normalizationScheme hfin)) :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).to_subtype
  have hbir : IsBirational ν := Scheme.isBirational_normalization Y hfin
  obtain ⟨W, hW, hνW⟩ := exists_dense_open_isIso_morphismRestrict_of_isIntegralHom ν hbir
    (Or.inl ⟨inferInstance, inferInstance⟩)
  let U := V ⊓ W
  have hUd : Dense (U : Set Y) := hV.inter_of_isOpen_left hW V.isOpen
  have : IsIso (ν ∣_ U) := isIso_morphismRestrict_of_le ν inf_le_right hνW
  have hfU : IsIso (f ∣_ U).c :=
    (isIso_c_morphismRestrict_iff f U).mpr fun W' hW' ↦
      (isIso_c_morphismRestrict_iff f V).mp hfV W' (hW'.trans inf_le_left)
  have hfνU := isIso_c_morphismRestrict_of_isPullback (IsPullback.of_hasPullback f ν) U hfU
  have hO : IsIso (pullback.snd f ν).c :=
    Stacks.SteinFactorization.isIso_c_of_flat_of_isNormal _ (ν ⁻¹ᵁ U)
      (dense_preimage_of_isBirational ν hbir U hUd)
      ((isIso_c_morphismRestrict_iff _ _).mp hfνU)
  have hXν := isInCharacteristic_of_hom (pullback.fst f ν) p hX
  exact descendsAfterFrobenius_of_isNormal _ hO hXν _
    (hE.pullback (f' := pullback.snd f ν) pullback.condition hX hXν)

end AlgebraicGeometry

end
