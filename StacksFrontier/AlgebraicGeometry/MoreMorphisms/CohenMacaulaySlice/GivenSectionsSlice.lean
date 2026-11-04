module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.Comap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.RegularSliceThroughPoint

/-!
# Slicing by prescribed global functions (Stacks 06LI for the functions one is given)

Stacks 06LI produces the slice from a family of elements of the local ring `𝒪_{X, x}`: it
returns an affine open `U ∋ x` together with sections `a₁, …, a_r ∈ Γ(U, 𝒪_U)` *of its own
choosing* whose germs at `x` are the prescribed ones, and asserts flatness and local finite
presentation over the base of the zero scheme `V(a₁, …, a_r)`.

Every consumer of it starts instead from global functions `b₁, …, b_r ∈ Γ(X, 𝒪_X)` and needs the
conclusion for `V(b₁, …, b_r)`, not for the manufactured `a_i`.  This file performs that
exchange: the two families have the same germ at `x`, so they agree on a basic open neighbourhood
of `x`, and over that neighbourhood the two zero schemes are the same closed subscheme.

## Main results

* `Stacks.AlgebraicGeometry.exists_affineOpenImmersion_flat_zeroScheme_of_isRegular_fiber`:
  **Stacks 06LI stated for the given global functions.**  If `f : X ⟶ S` is locally of finite
  presentation and flat at `x`, and the germs at `x` of `b₁, …, b_r ∈ Γ(X, 𝒪_X)` become a regular
  sequence in the local ring of the fibre through `x`, then `x` has an affine open neighbourhood
  `j : W ⟶ X` over which the zero scheme of the restrictions `b_i|_W` is flat and locally of
  finite presentation over `S`.
* `Stacks.AlgebraicGeometry.exists_basicOpen_appTop_eq_of_germ_eq`: on an affine scheme, two
  finite families of global functions with the same germs at a point agree on a basic open
  neighbourhood of that point.
* `Stacks.AlgebraicGeometry.isUnit_appTop_ι_basicOpen`,
  `Stacks.AlgebraicGeometry.germ_appTop_eq_stalkMap_germ`: the two elementary facts about
  `AlgebraicGeometry.Scheme.Hom.appTop` the exchange uses.

## Implementation notes

The germ comparison is done in the ring rather than through a refinement of opens.  On an affine
scheme the stalk at a point is the localization of the global sections at the corresponding prime
(`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`), so equality of the germs of `a_i` and
`b_i|_U` gives, for each `i`, an element `m_i` outside that prime with `m_i * (a_i - b_i|_U) = 0`.
Their product `s` is again outside the prime, so `x` lies in the basic open `D(s)`, and the
restriction of `s` to `D(s)` is a unit — `isUnit_appTop_ι_basicOpen`, which reads the unit off
`AlgebraicGeometry.Scheme.preimage_basicOpen_top` and
`AlgebraicGeometry.Scheme.Opens.ι_preimage_self` rather than off a refinement — so the
restrictions of `a_i` and of `b_i|_U` to `D(s)` agree.  Nothing is transported along an equality
of opens: everything is phrased through `AlgebraicGeometry.Scheme.Hom.appTop`, which is where the
pullback of the ideal sheaf of a zero scheme, `Stacks.AlgebraicGeometry.comap_ofIdealTop`, states
its conclusion too.

Flatness over `S` then transfers because the zero scheme of the restricted functions is the
pullback of the zero scheme of the `a_i` along the open immersion `D(s) ⟶ U`: the comparison
`AlgebraicGeometry.Scheme.IdealSheafData.comapIso` identifies it with that fibre product, whose
projection to `V(a₁, …, a_r)` is a base change of an open immersion and hence flat and locally of
finite presentation, and the two properties compose.

This is one of the inputs of the flatness half of Stacks 06LW, which is proved as
`AlgebraicGeometry.Space.exists_isOpenSubspace_isFlat_vanishingSubfunctor_of_isRegular_fiber`.
No
`@[stacks]` attribute is claimed here: the statement is Stacks 06LI's conclusion re-expressed,
and Stacks 06LI itself is registered on
`Stacks.AlgebraicGeometry.exists_affineOpen_regularImmersion_flat_of_isRegular_fiber`.

## References

* [Stacks Project, Lemma 37.24.1 (Tag 06LI)](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Lemma 76.28.1 (Tag 06LW)](https://stacks.math.columbia.edu/tag/06LW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Stacks.AlgebraicGeometry

universe u

/-- The germ at `x` of the pullback of a global function along `g : X ⟶ Y` is the image of its
germ at `g x` under the homomorphism of local rings of `g`. -/
theorem germ_appTop_eq_stalkMap_germ {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X) (t : Γ(Y, ⊤)) :
    X.presheaf.germ ⊤ x trivial (g.appTop t)
      = (g.stalkMap x) (Y.presheaf.germ ⊤ (g x) trivial t) :=
  (g.germ_stalkMap_apply ⊤ x trivial t).symm

/-- **The restriction of a global function to its own basic open is a unit.**  The basic open of
the restricted function is the preimage of the basic open, which is everything, so the germ of
the restriction is a unit at every point. -/
theorem isUnit_appTop_ι_basicOpen {Z : Scheme.{u}} (s : Γ(Z, ⊤)) :
    IsUnit ((Z.basicOpen s).ι.appTop s) := by
  have htop : (Z.basicOpen s).toScheme.basicOpen ((Z.basicOpen s).ι.appTop s) = ⊤ := by
    rw [← Scheme.preimage_basicOpen_top]
    exact Scheme.Opens.ι_preimage_self _
  refine (Z.basicOpen s).toScheme.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun w _ => ?_
  exact ((Z.basicOpen s).toScheme.mem_basicOpen_top ((Z.basicOpen s).ι.appTop s) w).1
    (by rw [htop]; trivial)

/-- **Two finite families of global functions on an affine scheme with the same germs at a point
agree on a basic open neighbourhood of that point.**

The stalk is the localization of the global sections at the prime of the point, so each
difference `a_i - c_i` is killed by an element `m_i` outside that prime; the product of the `m_i`
is the function cutting out the neighbourhood, and its restriction there is a unit. -/
theorem exists_basicOpen_appTop_eq_of_germ_eq {Z : Scheme.{u}} [IsAffine Z] {r : ℕ}
    (a c : Fin r → Γ(Z, ⊤)) (y : Z)
    (h : ∀ i, Z.presheaf.germ ⊤ y trivial (a i) = Z.presheaf.germ ⊤ y trivial (c i)) :
    ∃ s : Γ(Z, ⊤), y ∈ Z.basicOpen s ∧
      ∀ i, (Z.basicOpen s).ι.appTop (a i) = (Z.basicOpen s).ι.appTop (c i) := by
  classical
  have hU : IsAffineOpen (⊤ : Z.Opens) := isAffineOpen_top Z
  set p := (hU.primeIdealOf ⟨y, trivial⟩).asIdeal with hp
  have hpp : p.IsPrime := (hU.primeIdealOf ⟨y, trivial⟩).isPrime
  let : Algebra Γ(Z, ⊤) (Z.presheaf.stalk y) := (Z.presheaf.germ ⊤ y trivial).hom.toAlgebra
  have : IsLocalization.AtPrime (Z.presheaf.stalk y) p := hU.isLocalization_stalk ⟨y, trivial⟩
  have halg : ∀ t : Γ(Z, ⊤), algebraMap Γ(Z, ⊤) (Z.presheaf.stalk y) t
      = (Z.presheaf.germ ⊤ y trivial) t := fun _ => rfl
  have key : ∀ i, ∃ m : p.primeCompl, (m : Γ(Z, ⊤)) * a i = (m : Γ(Z, ⊤)) * c i := fun i =>
    (IsLocalization.eq_iff_exists p.primeCompl (Z.presheaf.stalk y)).mp
      (by rw [halg, halg]; exact h i)
  choose m hm using key
  refine ⟨∏ i, (m i : Γ(Z, ⊤)), ?_, fun i => ?_⟩
  · rw [Scheme.mem_basicOpen_top, ← halg]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Z.presheaf.stalk y) p _).2
      (Submonoid.prod_mem _ fun i _ => (m i).2)
  · have hmul : (∏ j, (m j : Γ(Z, ⊤))) * a i = (∏ j, (m j : Γ(Z, ⊤))) * c i := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_right_comm, hm i, mul_right_comm]
    refine (isUnit_appTop_ι_basicOpen (∏ j, (m j : Γ(Z, ⊤)))).mul_left_cancel ?_
    rw [← map_mul, ← map_mul, hmul]

/-- **Stacks 06LI for the global functions one is given.**  Let `f : X ⟶ S` be locally of finite
presentation and flat at `x : X`, and let `b₁, …, b_r ∈ Γ(X, 𝒪_X)` be global functions whose
germs at `x` map to a regular sequence in the local ring of the fibre `X_{f x}` at `x`.  Then
there is an affine open neighbourhood `j : W ⟶ X` of `x` such that the zero scheme of the
restrictions `b₁|_W, …, b_r|_W` is flat and locally of finite presentation over `S`.

Stacks 06LI gives this for sections it chooses itself with the prescribed germs; the two families
agree on a basic open neighbourhood of `x` by
`Stacks.AlgebraicGeometry.exists_basicOpen_appTop_eq_of_germ_eq`, over which the zero schemes
coincide, and restricting to it is a base change along an open immersion, which preserves both
properties. -/
theorem exists_affineOpenImmersion_flat_zeroScheme_of_isRegular_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) {r : ℕ} (b : Fin r → Γ(X, ⊤))
    [LocallyOfFinitePresentation f]
    (hflat : IsFlatAt f.toLRSHom.toShHom x)
    (hregular : RingTheory.Sequence.IsRegular
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
      (List.ofFn fun i : Fin r =>
        ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
          ((f.fiberι_asFiber x).symm ▸ (X.presheaf.germ ⊤ x trivial (b i))))) :
    ∃ (W : Scheme.{u}) (j : W ⟶ X) (_ : IsOpenImmersion j) (w : W),
      IsAffine W ∧ j w = x ∧
      Flat ((Scheme.IdealSheafData.ofIdealTop
          (Ideal.ofList (List.ofFn fun i => j.appTop (b i)))).subschemeι ≫ j ≫ f) ∧
      LocallyOfFinitePresentation ((Scheme.IdealSheafData.ofIdealTop
          (Ideal.ofList (List.ofFn fun i => j.appTop (b i)))).subschemeι ≫ j ≫ f) := by
  obtain ⟨U, hx, a, hgerm, hsupp, hreg, hflatZ, hlfpZ, hbc⟩ :=
    exists_affineOpen_regularImmersion_flat_of_isRegular_fiber f x
      (fun i => X.presheaf.germ ⊤ x trivial (b i)) hflat hregular
  have hZ : IsAffine U.1.toScheme := U.2
  have hgerm2 : ∀ i, U.1.toScheme.presheaf.germ ⊤ (⟨x, hx⟩ : U.1.toScheme) trivial (a i)
      = U.1.toScheme.presheaf.germ ⊤ (⟨x, hx⟩ : U.1.toScheme) trivial
          (U.1.ι.appTop (b i)) := fun i =>
    (hgerm i).symm.trans
      (germ_appTop_eq_stalkMap_germ U.1.ι (⟨x, hx⟩ : U.1.toScheme) (b i)).symm
  obtain ⟨s, hys, hagree⟩ := exists_basicOpen_appTop_eq_of_germ_eq a
    (fun i => U.1.ι.appTop (b i)) (⟨x, hx⟩ : U.1.toScheme) hgerm2
  have hideal : Scheme.IdealSheafData.ofIdealTop
        (Ideal.ofList (List.ofFn fun i =>
          ((U.1.toScheme.basicOpen s).ι ≫ U.1.ι).appTop (b i)))
      = (Scheme.IdealSheafData.ofIdealTop
          (Ideal.ofList (List.ofFn a))).comap (U.1.toScheme.basicOpen s).ι := by
    rw [comap_ofIdealTop (U.1.toScheme.basicOpen s).ι (Ideal.ofList (List.ofFn a)),
      Ideal.ofList_ofFn, Ideal.ofList_ofFn, Ideal.map_span, ← Set.range_comp]
    exact congrArg (Scheme.IdealSheafData.ofIdealTop ∘ Ideal.span)
      (congrArg Set.range (funext fun i => by
        simp only [Function.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        exact (hagree i).symm))
  have hW : IsAffine (U.1.toScheme.basicOpen s).toScheme :=
    (isAffineOpen_top U.1.toScheme).basicOpen s
  have hcomm : ((Scheme.IdealSheafData.ofIdealTop
        (Ideal.ofList (List.ofFn a))).comap (U.1.toScheme.basicOpen s).ι).subschemeι ≫
          ((U.1.toScheme.basicOpen s).ι ≫ U.1.ι) ≫ f
      = (((Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn a))).comapIso
            (U.1.toScheme.basicOpen s).ι).hom ≫
          pullback.snd (U.1.toScheme.basicOpen s).ι
            (Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn a))).subschemeι) ≫
        ((Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn a))).subschemeι ≫
          U.1.ι ≫ f) := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst
      (Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn a)))
      (U.1.toScheme.basicOpen s).ι]
    simp only [Category.assoc]
    rw [← Category.assoc (pullback.fst (U.1.toScheme.basicOpen s).ι _)
      (U.1.toScheme.basicOpen s).ι, pullback.condition]
    simp only [Category.assoc]
  refine ⟨(U.1.toScheme.basicOpen s).toScheme, (U.1.toScheme.basicOpen s).ι ≫ U.1.ι,
    inferInstance, ⟨⟨x, hx⟩, hys⟩, hW, rfl, ?_, ?_⟩ <;> rw [hideal, hcomm] <;> infer_instance

end Stacks.AlgebraicGeometry

end
