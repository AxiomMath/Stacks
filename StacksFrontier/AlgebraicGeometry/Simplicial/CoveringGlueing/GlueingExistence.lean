module

public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.TotalRestrictionDescent
public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenSummandIdentificationIso

/-!
# A global object restricting to given local objects on the total site

Let `(C, O_C)` be a ringed site with fibre products, given by a pretopology, `{U_i ⟶ X}` a
covering, `E_i` objects of `D(O_{U_i})` and `ρ_{ij}` isomorphisms on the overlaps satisfying the
cocycle condition. If the negative self-exts of the restrictions of the `E_i` vanish and the
cohomology of the `E_i` vanishes uniformly to the left, then Stacks 0DCA, applied to the data of
Situation 0DC9 attached to the covering and to the Čech object of the covering, produces a
cartesian object of `D(O)` on the total site, which by Stacks 0D7S is the restriction of an
object `M` of `D(O_X)`. This file records that `M`, with its summandwise identification.

## Main definitions

* `AlgebraicGeometry.RingedSite.CoveringGlueing.coveringLocallyGiven`: the data of Situation 0DC9
  attached to the covering.

## Main results

* `AlgebraicGeometry.RingedSite.CoveringGlueing.exists_summandIdentification`: the object `M`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace CategoryTheory

/-- **Shifted self-maps vanish when the corresponding negative self-ext does.** -/
theorem shift_hom_eq_zero_of_subsingleton {𝒟 : Type*} [Category 𝒟] [Preadditive 𝒟]
    [HasShift 𝒟 ℤ] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] (A : 𝒟) (t : ℤ)
    (h : Subsingleton (A ⟶ (shiftFunctor 𝒟 (-t)).obj A)) (g : (shiftFunctor 𝒟 t).obj A ⟶ A) :
    g = 0 := by
  apply (shiftFunctor 𝒟 (-t)).map_injective
  rw [Functor.map_zero]
  have e := @Subsingleton.elim _ h ((shiftFunctorCompIsoId 𝒟 t (-t) (add_neg_cancel t)).inv.app A ≫
    (shiftFunctor 𝒟 (-t)).map g) 0
  rw [← cancel_epi ((shiftFunctorCompIsoId 𝒟 t (-t) (add_neg_cancel t)).inv.app A), e,
    comp_zero]

/-- **Shifted self-maps vanish after a fully faithful functor commuting with shifts.** -/
theorem shift_hom_eq_zero_of_fullyFaithful {𝒟 𝒟' : Type*} [Category 𝒟] [Category 𝒟']
    [Preadditive 𝒟] [Preadditive 𝒟'] [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] (T : 𝒟 ⥤ 𝒟')
    [T.CommShift ℤ] [T.Full] [T.Faithful] [T.PreservesZeroMorphisms] (A : 𝒟) (t : ℤ)
    (hA : ∀ g : (shiftFunctor 𝒟 t).obj A ⟶ A, g = 0)
    (g : (shiftFunctor 𝒟' t).obj (T.obj A) ⟶ T.obj A) : g = 0 := by
  have h := congrArg T.map (hA (T.preimage ((T.commShiftIso t).hom.app A ≫ g)))
  rw [Functor.map_preimage, Functor.map_zero] at h
  rw [← cancel_epi ((T.commShiftIso t).hom.app A), h, comp_zero]

end CategoryTheory

namespace AlgebraicGeometry.RingedSite.CoveringGlueing

open CategoryTheory.SimplicialSemiRepresentable

attribute [local instance] HasDerivedCategory.standard pretopologyRingedSite_over_hasPullbacks

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (OC : Sheaf P.toGrothendieck CommRingCat.{u}) {ι : Type u} {U : ι → C} (f : ∀ i, U i ⟶ X)
  (E : ∀ i, LocalDerivedCategory.{0} (pretopologyRingedSite P OC) (U i))
  (ρ : ∀ i j, (derivedOverMap.{0} (pretopologyRingedSite P OC) (pullback.fst (f i) (f j))).obj
      (E i) ≅ (derivedOverMap.{0} (pretopologyRingedSite P OC) (pullback.snd (f i) (f j))).obj
        (E j))

/-- The data of Situation 0DC9 attached to the covering, on the universe-explicit localized
site. -/
def coveringLocallyGiven (hρ : IsCocycle (X := pretopologyRingedSite P OC) f ρ) :
    LocallyGiven.{0, u, u, u, u, u} (overRingedSite P OC (X := X)) :=
  locallyGiven (X := pretopologyRingedSite P OC) f E ρ hρ

variable {P OC f E ρ}

/-- **The negative self-exts of the locally given objects of the covering vanish** when those of
the restrictions of the `E_i` to all objects over the `U_i` do. -/
theorem indexObj_shift_hom_eq_zero
    (hExt : ∀ (i : ι) {V : C} (a : V ⟶ U i) (n : ℤ), n < 0 →
      Subsingleton (DerivedCategory.Ext ((derivedOverMap.{0} (pretopologyRingedSite P OC) a).obj
        (E i)) ((derivedOverMap.{0} (pretopologyRingedSite P OC) a).obj (E i)) n))
    (b : IndexCategory (X := pretopologyRingedSite P OC) f) (t : ℤ) (ht : 0 < t)
    (g : (shiftFunctor (LocalDerivedCategory.{0} ((pretopologyRingedSite P OC).over X) b.V) t).obj
        (indexObj f E b) ⟶ indexObj f E b) :
    g = 0 :=
  have := RingedSite.iteratedSliceTransport_additive (pretopologyRingedSite P OC) X b.V
  have := RingedSite.derivedIteratedSliceTransport_isEquivalence (pretopologyRingedSite P OC) X b.V
  shift_hom_eq_zero_of_fullyFaithful
    ((pretopologyRingedSite P OC).derivedIteratedSliceTransport X b.V)
    ((derivedOverMap.{0} (pretopologyRingedSite P OC) b.a).obj (E b.i)) t
    (fun g' => shift_hom_eq_zero_of_subsingleton _ t (hExt b.i b.a (-t) (by omega)) g') g

/-- **The cohomology of the locally given objects of the covering vanishes** where that of the
`E_i` does. -/
theorem coveringLocallyGiven_isZero_homology (hρ : IsCocycle (X := pretopologyRingedSite P OC) f ρ)
    (b : (coveringLocallyGiven P OC f E ρ hρ).B) (q : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor _ q).obj (E b.i))) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((coveringLocallyGiven P OC f E ρ hρ).obj b)) :=
  have := RingedSite.iteratedSliceTransport_additive (pretopologyRingedSite P OC) X b.V
  have := RingedSite.iteratedSliceTransport_preservesFiniteLimits (pretopologyRingedSite P OC) X
    b.V
  have := RingedSite.iteratedSliceTransport_preservesFiniteColimits (pretopologyRingedSite P OC) X
    b.V
  have := RingedSite.overMapModules_preservesFiniteLimits (pretopologyRingedSite P OC) b.a
  Functor.isZero_homologyFunctor_mapDerivedCategory_obj
    ((pretopologyRingedSite P OC).iteratedSliceTransport X b.V) _ q
    (Functor.isZero_homologyFunctor_mapDerivedCategory_obj
      ((pretopologyRingedSite P OC).overMapModules b.a) (E b.i) q h)

/-- **A global object restricting to the locally given objects of the covering on the total
site of its Čech object**: under the hypotheses of Stacks 0GMG, Stacks 0DCA and Stacks 0D7S
produce an object `M` of `D(O_X)` together with a summandwise identification of its restriction
to the total site with the locally given objects. -/
theorem exists_summandIdentification (hf : Presieve.ofArrows U f ∈ P X)
    (hρ : IsCocycle (X := pretopologyRingedSite P OC) f ρ)
    (hExt : ∀ (i : ι) {V : C} (a : V ⟶ U i) (n : ℤ), n < 0 →
      Subsingleton (DerivedCategory.Ext ((derivedOverMap.{0} (pretopologyRingedSite P OC) a).obj
        (E i)) ((derivedOverMap.{0} (pretopologyRingedSite P OC) a).obj (E i)) n))
    (hBound : ∃ t : ℤ, ∀ (i : ι) (n : ℤ), n < t →
      IsZero ((DerivedCategory.homologyFunctor _ n).obj (E i))) :
    ∃ M : LocalDerivedCategory.{0} (pretopologyRingedSite P OC) X,
      Nonempty ((coveringLocallyGiven P OC f E ρ hρ).SummandIdentification
        (cechLift (X := pretopologyRingedSite P OC) f)
        ((cechTotalRestriction P OC f).mapDerivedCategory.obj M)) := by
  obtain ⟨t, ht⟩ := hBound
  obtain ⟨⟨Etot, hE, ⟨σ⟩⟩, -⟩ :=
    (coveringLocallyGiven P OC f E ρ hρ).exists_unique_cartesian_summandIdentification
      (cechLift (X := pretopologyRingedSite P OC) f)
      (fun b t' ht' g => indexObj_shift_hom_eq_zero hExt b t' ht' g)
  have hb := σ.isBoundedBelow_of_summands t
    (fun n i q hq => coveringLocallyGiven_isZero_homology hρ _ q (ht _ q hq))
  obtain ⟨M, ⟨e⟩⟩ := exists_cechTotalRestriction_iso hf Etot hE hb
  exact ⟨M, ⟨σ.ofIso e⟩⟩

end AlgebraicGeometry.RingedSite.CoveringGlueing

end
