module

public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.ProperSmoothNoetherianModel
public import StacksFrontier.AlgebraicGeometry.AffineStageDescent.ProperSmoothModelSpec

/-!
# Global functions of a proper smooth family over an affine open, near a point

Let `f : X ⟶ S` be a proper smooth morphism of schemes and `s ∈ S`. Writing `f` over an affine
neighbourhood of `s` as the base change of a proper smooth morphism to the spectrum of a
Noetherian ring ([Stacks, Tag 01ZM]), the Noetherian statement
`exists_away_globalFunctions_finiteEtale_and_split` gives an open neighbourhood `G` of `s` over
every affine open `V ⊆ G` of which

* the global functions of `f⁻¹(V)` form a finite étale `Γ(S, V)`-algebra, and
* `RΓ(f⁻¹(V), 𝒪) ≅ Γ(S, V)^r[0] ⊕ K` with `K` a bounded complex of finite free modules
  concentrated in degrees `≥ 1`.

Both are stated for the base change `X'` of `X` along `Spec Γ(S, V) ⟶ S`, which is the form the
Čech computation is made in; `X'` is `f⁻¹(V)`.

## Main results

* `exists_nhds_globalFunctions_finiteEtale_and_split`: the two conclusions above, for `X'` over
  every affine open `V ⊆ G`.

## References

* [Stacks Project, Tag 0G7Y](https://stacks.math.columbia.edu/tag/0G7Y)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

@[expose] public noncomputable section

open scoped Stacks.StandardDerivedModel

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

/-- **A proper smooth family near a point.** For `f : X ⟶ S` proper and smooth and `s ∈ S` there
are an open neighbourhood `G` of `s`, `r ∈ ℕ` and `b ∈ ℤ` such that for every affine open `V ⊆ G`
the base change `X'` of `X` along `Spec Γ(S, V) ⟶ S` has finite étale global functions over
`Γ(S, V)` and `RΓ(X', 𝒪_{X'}) ≅ Γ(S, V)^r[0] ⊕ K` in `D(Γ(S, V))`, for a complex `K` of finite
free modules concentrated in degrees `[1, b]`. -/
theorem exists_nhds_globalFunctions_finiteEtale_and_split {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Smooth f] (s : S) :
    ∃ (G : S.Opens) (_ : s ∈ G) (r : ℕ) (b : ℤ),
      ∀ (V : S.Opens) (hV : IsAffineOpen V), V ≤ G →
        ∃ (X' : Scheme.{u}) (f' : X' ⟶ Spec (.of Γ(S, V))) (j : X' ⟶ X),
          IsPullback j f' f hV.fromSpec ∧
          (letI : Algebra Γ(S, V) Γ(X', ⊤) :=
              ((Stacks.Cech.globalRingHom f').hom : Γ(S, V) →+* Γ(X', ⊤)).toAlgebra;
            Algebra.Etale Γ(S, V) Γ(X', ⊤) ∧ Module.Finite Γ(S, V) Γ(X', ⊤)) ∧
          ∃ K : CochainComplex (ModuleCat.{u} Γ(S, V)) ℤ, K.IsStrictlyGE 1 ∧ K.IsStrictlyLE b ∧
            (∀ i, Module.Free Γ(S, V) (K.X i) ∧ Module.Finite Γ(S, V) (K.X i)) ∧
            Nonempty ((derivedGlobalSectionsOver f').obj
                ((DerivedCategory.singleFunctor X'.Modules 0).obj (Scheme.unitModule X')) ≅
              (DerivedCategory.singleFunctor (ModuleCat.{u} Γ(S, V)) 0).obj
                  (ModuleCat.of Γ(S, V) (Fin r → Γ(S, V))) ⊞
                DerivedCategory.Q.obj K) := by
  classical
  obtain ⟨W, hW, hsW, -⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) trivial
  have : IsAffine W := hW
  have hW' := (isPullback_morphismRestrict f W).flip
  have : IsProper (f ∣_ W) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hW' inferInstance
  have : Smooth (f ∣_ W) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hW' inferInstance
  obtain ⟨A, _, _, Y, h, q, q', _, _, hpb⟩ :=
    exists_isPullback_spec_isNoetherianRing_properSmooth (f ∣_ W)
  let sW : W.toScheme := ⟨s, hsW⟩
  have := (q sW).isPrime
  obtain ⟨a, ha, r, b, H⟩ := exists_away_globalFunctions_finiteEtale_and_split h (q sW).asIdeal
  let G : S.Opens := W.ι ''ᵁ (q ⁻¹ᵁ PrimeSpectrum.basicOpen a)
  refine ⟨G, ⟨sW, ha, rfl⟩, r, b, fun V hV hVG => ?_⟩
  have hVW : V ≤ W :=
    hVG.trans ((Scheme.Hom.image_le_opensRange _ _).trans (Scheme.Opens.opensRange_ι W).le)
  let ι := S.homOfLE hVW
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (hV.isoSpec.inv ≫ ι ≫ q)
  let φ : A →+* Γ(S, V) := φ'.hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = hV.isoSpec.inv ≫ ι ≫ q := hφ'
  have hunit : IsUnit (φ a) := by
    by_contra hna
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {φ a})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    let x : Spec (.of Γ(S, V)) := ⟨m, hm.isPrime⟩
    have hz : ι (hV.isoSpec.inv x) ∈ q ⁻¹ᵁ PrimeSpectrum.basicOpen a := by
      have h1 : W.ι (ι (hV.isoSpec.inv x)) ∈ G := by
        rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
        exact hVG (hV.isoSpec.inv x).2
      exact (Scheme.Hom.preimage_image_eq W.ι (q ⁻¹ᵁ PrimeSpectrum.basicOpen a)).le h1
    have hx : Spec.map (CommRingCat.ofHom φ) x ∈ PrimeSpectrum.basicOpen a := by
      rwa [hφ]
    exact hx (hle (Ideal.subset_span rfl))
  let X' := pullback h (Spec.map (CommRingCat.ofHom φ))
  let f' : X' ⟶ Spec (.of Γ(S, V)) := pullback.snd _ _
  let g' : X' ⟶ Y := pullback.fst _ _
  have hsq0 : IsPullback g' f' h (Spec.map (CommRingCat.ofHom φ)) := IsPullback.of_hasPullback _ _
  have hcond : g' ≫ h = (f' ≫ hV.isoSpec.inv ≫ ι) ≫ q := by simp [hsq0.w, hφ]
  let j₁ : X' ⟶ (f ⁻¹ᵁ W : Scheme.{u}) := hpb.lift g' (f' ≫ hV.isoSpec.inv ≫ ι) hcond
  have hpb₁ : IsPullback j₁ f' (f ∣_ W) (hV.isoSpec.inv ≫ ι) := by
    refine IsPullback.of_right ?_ (hpb.lift_snd _ _ _) hpb
    rwa [hpb.lift_fst, Category.assoc, ← hφ]
  have hpbS : IsPullback (j₁ ≫ (f ⁻¹ᵁ W).ι) f' f hV.fromSpec := by
    have hpaste := hpb₁.paste_horiz hW'
    rwa [Category.assoc, Scheme.homOfLE_ι] at hpaste
  exact ⟨X', f', j₁ ≫ (f ⁻¹ᵁ W).ι, hpbS, H φ hunit hsq0⟩

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end
