module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.SpectralSequence.GrothendieckEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentUniverseDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyOverBaseUniverseLift
public import StacksFrontier.AlgebraicGeometry.Spaces.EulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Spaces.InjectivePushforwardAcyclicity
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperHigherDirectImageCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperModuleCohomologyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCohomologyUniformVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp

/-!
# The Euler characteristic along a morphism of proper algebraic spaces over a field

Let `k` be a field, `f : Y ⟶ X` a morphism of algebraic spaces proper over `k` and `𝓖` a coherent
`𝒪_Y`-module. [Stacks, Tag 0EDD] asserts that only finitely many of the higher direct images
`Rⁱf_*𝓖` are nonzero, each is coherent, and

`χ(Y, 𝓖) = ∑ᵢ (-1)ⁱ χ(X, Rⁱf_*𝓖)`.

## Main results

* `AlgebraicGeometry.Space.isProper_of_isProper_toBase`: a morphism of algebraic spaces proper
  over `k` is proper.
* `AlgebraicGeometry.Space.globalSectionsOverBaseCompIso`: `Γ(X, f_* −) ≅ Γ(Y, −)` as functors
  to `k`-vector spaces.
* `AlgebraicGeometry.Space.eulerCharacteristic_eq_finsum_eulerCharacteristic_higherDirectImage`:
  **[Stacks, Tag 0EDD]**, for a coherent module with sections in the universe of the structure
  sheaf.
* `exists_eulerCharacteristic_eq_finsum_eulerCharacteristic_higherDirectImage`:
  **[Stacks, Tag 0EDD]**, for a coherent module with sections in the universe of the Euler
  characteristic.

## Implementation notes

**Universes.** The Euler characteristic `AlgebraicGeometry.Space.eulerCharacteristic` of
[Stacks, Tag 0DN1] is taken of modules whose sections lie in a universe `max (u + 1) w`
containing the small étale site, while the direct image
`AlgebraicGeometry.Space.modulePushforward` and hence `Rⁱf_*` exist for modules with sections in
the universe `u` of the structure sheaf. The statement is therefore made for a coherent `𝓖` with
sections in `Type u`, with both Euler characteristics taken of universe lifts
(`SheafOfModules.uliftForPresentation`). This loses nothing: every coherent module with sections
in `Type (max (u + 1) w)` is such a lift
(`AlgebraicGeometry.Space.exists_iso_uliftForPresentation_of_isCoherent`), and the Euler
characteristic depends on its module only up to isomorphism
(`AlgebraicGeometry.Space.eulerCharacteristic_congr`).

## References

* [Stacks Project, Tag 0EDD](https://stacks.math.columbia.edu/tag/0EDD)
* [Stacks Project, Tag 0DN1](https://stacks.math.columbia.edu/tag/0DN1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

universe u w

namespace AlgebraicGeometry.Space

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    {X Y : AlgebraicSpaces B (Spec (.of k)) hk}

/-- **A morphism of algebraic spaces proper over `k` is proper.** -/
theorem isProper_of_isProper_toBase (f : Y ⟶ X)
    (πX : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hπX : IsProper B (Spec (.of k)) hk πX)
    (πY : Y.1 ⟶ yoneda.obj (baseObject k B hk)) (hπY : IsProper B (Spec (.of k)) hk πY) :
    IsProper B (Spec (.of k)) hk f.hom := by
  have h : f.hom ≫ πX = πY := (isTerminal_yoneda_obj_base B (Spec (.of k)) hk).hom_ext _ _
  exact isProper_of_comp_of_isSeparated B (Spec (.of k)) hk Y.2 X.2
    (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)) f.hom πX (h ▸ hπY) hπX.1

/-- **The higher direct images of a coherent module along a morphism of algebraic spaces proper
over `k` are coherent.** -/
theorem isCoherent_higherDirectImage_of_isProper_toBase (f : Y ⟶ X)
    (πX : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hπX : IsProper B (Spec (.of k)) hk πX)
    (πY : Y.1 ⟶ yoneda.obj (baseObject k B hk)) (hπY : IsProper B (Spec (.of k)) hk πY)
    (G : Modules.{u, u} B (Spec (.of k)) hk Y.1 Y.2) [hG : IsCoherent B (Spec (.of k)) hk Y.1 Y.2 G]
    (i : ℕ) :
    have := hasInjectiveResolutions_modules B (Spec (.of k)) hk Y.1 Y.2
    IsCoherent B (Spec (.of k)) hk X.1 X.2
      (((modulePushforward B (Spec (.of k)) hk f).rightDerived i).obj G) :=
  isCoherent_higherDirectImage_of_isProper B (Spec (.of k)) hk f
    (isProper_of_isProper_toBase k B hk f πX hπX πY hπY)
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 πX hπX) G hG i

/-- **`Γ(X, f_* −) ≅ Γ(Y, −)` over the base ring**, for a morphism `f : Y ⟶ X` of algebraic spaces
over `Spec A`: both are the sections over `Spec A` of the direct image to the base. -/
def globalSectionsOverBaseCompIso (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A)))
    {X Y : AlgebraicSpaces B (Spec (.of A)) hA} (f : Y ⟶ X) :
    modulePushforward B (Spec (.of A)) hA f ⋙ globalSectionsOverBase X ≅ globalSectionsOverBase Y :=
  let V := baseObject A B hA
  let Z : AlgebraicSpaces B (Spec (.of A)) hA :=
    schemeSpace V
  let gX : X ⟶ Z := ObjectProperty.homMk ((isTerminal_yoneda_obj_base B (Spec (.of A)) hA).from X.1)
  let gY : Y ⟶ Z := ObjectProperty.homMk ((isTerminal_yoneda_obj_base B (Spec (.of A)) hA).from Y.1)
  have h : f ≫ gX = gY :=
    ObjectProperty.hom_ext _ ((isTerminal_yoneda_obj_base B (Spec (.of A)) hA).hom_ext _ _)
  let O := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA
    (yoneda.obj V) (isAlgebraicSpace_yoneda B (Spec (.of A)) hA V)).O
  let ev := SheafOfModules.evaluation.{u} O (op (idEtaleChart B (Spec (.of A)) hA V))
  let E := ModuleCat.restrictScalars.{u} (idEtaleChartBaseRingHom V) ⋙
    ModuleCat.uliftFunctor.{u + 1} A
  Functor.isoWhiskerLeft _ (globalSectionsOverBaseIso V gX) ≪≫
    (Functor.associator _ _ E).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ ev).symm E ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (modulePushforwardCompIso B (Spec (.of A)) hA f gX) ev) E ≪≫
    eqToIso (congrArg (fun φ ↦ (modulePushforward B (Spec (.of A)) hA φ ⋙ ev) ⋙ E) h) ≪≫
    (globalSectionsOverBaseIso V gY).symm

/-- A left exact additive functor out of an abelian category with injective resolutions has
zero right derived functors at a zero object. -/
private theorem isZero_rightDerived_obj_of_isZero {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    [Abelian 𝒞] [Abelian 𝒟] [HasInjectiveResolutions 𝒞] (Φ : 𝒞 ⥤ 𝒟) [Φ.Additive]
    [PreservesFiniteLimits Φ] {Z : 𝒞} (hZ : IsZero Z) (n : ℕ) :
    IsZero ((Φ.rightDerived n).obj Z) := by
  cases n with
  | zero => exact (Φ.map_isZero hZ).of_iso (Φ.rightDerivedZeroIsoSelf.app Z)
  | succ n =>
    have := hZ.injective
    exact Φ.isZero_rightDerived_obj_injective_succ n Z

/-- Let `k` be a field, `f : Y ⟶ X` a morphism of algebraic spaces proper over
`k` and `𝓖` a coherent `𝒪_Y`-module. Then only finitely many of the higher direct images
`Rⁱf_*𝓖` are nonzero, each is coherent, and
`χ(Y, 𝓖) = ∑ᵢ (-1)ⁱ χ(X, Rⁱf_*𝓖)`.

Here `𝓖` has sections in the universe of the structure sheaf, where `Rⁱf_*` exists, and both
Euler characteristics are taken of universe lifts. -/
@[stacks 0EDD]
theorem eulerCharacteristic_eq_finsum_eulerCharacteristic_higherDirectImage (f : Y ⟶ X)
    (πX : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hπX : IsProper B (Spec (.of k)) hk πX)
    (πY : Y.1 ⟶ yoneda.obj (baseObject k B hk)) (hπY : IsProper B (Spec (.of k)) hk πY)
    (G : Modules.{u, u} B (Spec (.of k)) hk Y.1 Y.2)
    [hG : IsCoherent B (Spec (.of k)) hk Y.1 Y.2 G] :
    have := hasInjectiveResolutions_modules B (Spec (.of k)) hk Y.1 Y.2
    have := isCoherent_higherDirectImage_of_isProper_toBase k B hk f πX hπX πY hπY G
    {i : ℕ | ¬ IsZero (((modulePushforward B (Spec (.of k)) hk f).rightDerived i).obj G)}.Finite ∧
      eulerCharacteristic.{u, w} k B hk Y.1 Y.2 πY hπY
          (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w} G) =
        ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * eulerCharacteristic.{u, w} k B hk X.1 X.2 πX hπX
          (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w}
            (((modulePushforward B (Spec (.of k)) hk f).rightDerived i).obj G)) := by
  intro hres hcoh
  classical
  have := enoughInjectives_modules B (Spec (.of k)) hk X.1 X.2
  have := enoughInjectives_modules B (Spec (.of k)) hk Y.1 Y.2
  have := modulePushforward_additive B (Spec (.of k)) hk f
  have hf := isProper_of_isProper_toBase k B hk f πX hπX πY hπY
  let F := modulePushforward B (Spec (.of k)) hk f
  let ΓX := globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)
  let ΓY := globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of k)) hk Y.1 Y.2).O)
  let resX := ModuleCat.restrictScalars.{u + 1} (baseRingHom k B hk X.1 X.2)
  let resY := ModuleCat.restrictScalars.{u + 1} (baseRingHom k B hk Y.1 Y.2)
  have : PreservesFiniteLimits resX := ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have : PreservesFiniteColimits resX := ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have : resX.PreservesHomology := Functor.preservesHomologyOfExact _
  have : PreservesFiniteLimits resY := ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have : PreservesFiniteColimits resY := ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have : resY.PreservesHomology := Functor.preservesHomologyOfExact _
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B (Spec (.of k)) hk X.1 X.2
  have : PreservesFiniteLimits (ΓX ⋙ resX) := comp_preservesFiniteLimits _ _
  let eX (p : ℕ) (M) : ((ΓX ⋙ resX).rightDerived p).obj M ≅ resX.obj ((ΓX.rightDerived p).obj M) :=
    (Functor.rightDerivedCompIso ΓX resX p).app M
  have hZ := B.contains_terminal
  have hXqs : IsAbsolutelyQuasiSeparated B (Spec (.of k)) hk hZ X.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B (Spec (.of k)) hk hZ X.2
      (isAbsolutelyQuasiSeparated_yoneda_obj B (Spec (.of k)) hk hZ (baseObject k B hk)
        (inferInstanceAs (QuasiSeparatedSpace (Spec (.of k)))))
      (isQuasiSeparated_of_isSeparated B (Spec (.of k)) hk hπX.1)
  have hXqc : IsQuasiCompactSpace B (Spec (.of k)) hk X.1 :=
    isQuasiCompactSpace_of_isQuasiCompact_toBase B (Spec (.of k)) hk πX hπX.2.1.2
  obtain ⟨N₁, hN₁⟩ := exists_forall_isZero_rightDerived_globalSections_of_qcqs k B hk hZ X.1 X.2
    hXqc hXqs
  obtain ⟨N₂, hN₂⟩ := exists_forall_isZero_rightDerived_modulePushforward_of_qcqs B
    (Spec (.of k)) hk f hf.2.1.2 (isQuasiSeparated_of_isSeparated B (Spec (.of k)) hk hf.1) hXqc
  have hRf (q : ℕ) (hq : N₂ ≤ q) : IsZero ((F.rightDerived q).obj G) :=
    hN₂ X Y (𝟙 X) (𝟙 Y) f IsPullback.of_id_fst G hG.toIsQuasicoherentOnSite q hq
  have hFG (I : Modules.{u, u} B (Spec (.of k)) hk Y.1 Y.2) (hI : Injective I) (n : ℕ)
      (hn : 0 < n) : IsZero (((ΓX ⋙ resX).rightDerived n).obj (F.obj I)) := by
    have := hI
    exact IsZero.of_iso (resX.map_isZero
      (acyclic_globalSectionsFunctor_modulePushforward_of_injective B (Spec (.of k)) hk f I n hn))
      (eX n _)
  have hfin (p q : ℕ) :
      Module.Finite k (((ΓX ⋙ resX).rightDerived p).obj ((F.rightDerived q).obj G)) := by
    have := hcoh q
    have := moduleFinite_cohomology_of_isProper (A := k) X.1 X.2 πX hπX ((F.rightDerived q).obj G) p
    exact Module.Finite.equiv (eX p _).symm.toLinearEquiv
  have hsupp : {pq : ℕ × ℕ | ¬ IsZero (((ΓX ⋙ resX).rightDerived pq.1).obj
      ((F.rightDerived pq.2).obj G))}.Finite := by
    refine ((Set.finite_Iio N₁).prod (Set.finite_Iio N₂)).subset fun pq hpq => ?_
    refine Set.mem_prod.2 ⟨Set.mem_Iio.2 (not_le.1 fun h => hpq ?_),
      Set.mem_Iio.2 (not_le.1 fun h => hpq ?_)⟩
    · exact IsZero.of_iso (resX.map_isZero (hN₁ _ (hcoh pq.2).toIsQuasicoherentOnSite pq.1 h))
        (eX pq.1 _)
    · exact isZero_rightDerived_obj_of_isZero _ (hRf pq.2 h) pq.1
  obtain ⟨-, -, hsum⟩ := Functor.finsum_finrank_rightDerived_comp_eq F (ΓX ⋙ resX) hFG G hfin hsupp
  refine ⟨(Set.finite_Iio N₂).subset fun q hq => Set.mem_Iio.2 (not_le.1 fun h => hq (hRf q h)), ?_⟩
  have eY (n : ℕ) : ((F ⋙ ΓX ⋙ resX).rightDerived n).obj G ≅ resY.obj ((ΓY.rightDerived n).obj G) :=
    (Functor.rightDerivedIsoOfNatIso (globalSectionsOverBaseCompIso B k hk f) n).app G ≪≫
      (Functor.rightDerivedCompIso ΓY resY n).app G
  rw [eulerCharacteristic_eq_finsum]
  simp_rw [eulerCharacteristic_eq_finsum, finrank_cohomologyOverBase_uliftForPresentation.{u, w}]
  have hdsupp : (Function.support fun pq : ℕ × ℕ => (-1 : ℤ) ^ (pq.1 + pq.2) *
      (Module.finrank k
        (((ΓX ⋙ resX).rightDerived pq.1).obj ((F.rightDerived pq.2).obj G)) : ℤ)).Finite :=
    hsupp.subset fun pq hpq h => hpq (by
      simp only [HomologicalComplex.finrank_eq_zero_of_isZero h, Nat.cast_zero, mul_zero])
  calc ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (resY.obj ((ΓY.rightDerived n).obj G)) : ℤ)
      = ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          (Module.finrank k (((F ⋙ ΓX ⋙ resX).rightDerived n).obj G) : ℤ) :=
        finsum_congr fun n => by rw [(eY n).toLinearEquiv.finrank_eq]
    _ = ∑ᶠ pq : ℕ × ℕ, (-1 : ℤ) ^ (pq.1 + pq.2) *
          (Module.finrank k
            (((ΓX ⋙ resX).rightDerived pq.1).obj ((F.rightDerived pq.2).obj G)) : ℤ) :=
        hsum
    _ = ∑ᶠ qp : ℕ × ℕ, (-1 : ℤ) ^ (qp.2 + qp.1) *
          (Module.finrank k
            (((ΓX ⋙ resX).rightDerived qp.2).obj ((F.rightDerived qp.1).obj G)) : ℤ) :=
        (finsum_comp_equiv (Equiv.prodComm ℕ ℕ)).symm
    _ = ∑ᶠ (q : ℕ) (p : ℕ), (-1 : ℤ) ^ (p + q) *
          (Module.finrank k (((ΓX ⋙ resX).rightDerived p).obj ((F.rightDerived q).obj G)) : ℤ) :=
        finsum_curry _ (hdsupp.preimage (Equiv.prodComm ℕ ℕ).injective.injOn)
    _ = ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * ∑ᶠ p : ℕ, (-1 : ℤ) ^ p *
          (Module.finrank k
            (resX.obj ((ΓX.rightDerived p).obj ((F.rightDerived q).obj G))) : ℤ) := by
        refine finsum_congr fun q => ?_
        rw [mul_finsum]
        refine finsum_congr fun p => ?_
        rw [(eX p _).toLinearEquiv.finrank_eq, pow_add]
        ring

/-- For a coherent module `𝓖'` with sections in the universe of the Euler characteristic: `𝓖'` is
the universe lift of a coherent module `𝓖` with sections in the universe of the structure sheaf,
only finitely many `Rⁱf_*𝓖` are nonzero, and `χ(Y, 𝓖') = ∑ᵢ (-1)ⁱ χ(X, Rⁱf_*𝓖)`. -/
@[stacks 0EDD "for a coherent module in the universe of the Euler characteristic, the higher \
direct images being taken of its descent to the universe of the structure sheaf"]
theorem exists_eulerCharacteristic_eq_finsum_eulerCharacteristic_higherDirectImage (f : Y ⟶ X)
    (πX : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hπX : IsProper B (Spec (.of k)) hk πX)
    (πY : Y.1 ⟶ yoneda.obj (baseObject k B hk)) (hπY : IsProper B (Spec (.of k)) hk πY)
    (G' : Modules.{u, max (u + 1) w} B (Spec (.of k)) hk Y.1 Y.2)
    [IsCoherent B (Spec (.of k)) hk Y.1 Y.2 G'] :
    ∃ (G : Modules.{u, u} B (Spec (.of k)) hk Y.1 Y.2)
      (_ : IsCoherent B (Spec (.of k)) hk Y.1 Y.2 G)
      (_ : SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w} G ≅ G'),
      have := hasInjectiveResolutions_modules B (Spec (.of k)) hk Y.1 Y.2
      have := isCoherent_higherDirectImage_of_isProper_toBase k B hk f πX hπX πY hπY G
      {i : ℕ | ¬ IsZero (((modulePushforward B (Spec (.of k)) hk f).rightDerived i).obj G)}.Finite ∧
        eulerCharacteristic.{u, w} k B hk Y.1 Y.2 πY hπY G' =
          ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * eulerCharacteristic.{u, w} k B hk X.1 X.2 πX hπX
            (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w}
              (((modulePushforward B (Spec (.of k)) hk f).rightDerived i).obj G)) := by
  obtain ⟨G, hG, ⟨e⟩⟩ := exists_iso_uliftForPresentation_of_isCoherent.{u, w} B (Spec (.of k)) hk
    Y.1 Y.2 G'
  refine ⟨G, hG, e, ?_⟩
  obtain ⟨h₁, h₂⟩ := eulerCharacteristic_eq_finsum_eulerCharacteristic_higherDirectImage.{u, w}
    k B hk f πX hπX πY hπY G
  exact ⟨h₁, (eulerCharacteristic_congr k B hk Y.1 Y.2 πY hπY e).symm.trans h₂⟩

end AlgebraicGeometry.Space

end
