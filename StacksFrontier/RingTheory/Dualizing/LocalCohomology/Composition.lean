module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.PowerTorsionComparison.LocalCohomologyFunctor
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.SmallLocalization

/-!
# Composing local cohomology functors

Let `I` and `J` be finitely generated ideals of a commutative ring `A`, and let `Z = V(I)` and
`Y = V(J)` be the corresponding closed subsets of `Spec(A)`. Since `Z ∩ Y = V(I + J)`, local
cohomology supported on `Z` followed by local cohomology supported on `Y` ought to be local
cohomology supported on `V(I + J)`, and it is: both are right adjoint to the inclusion of the
objects with `(I + J)`-power-torsion cohomology into those with `I`-power-torsion cohomology.

The one point needing an argument is that `RΓ_Y` carries an object with `I`-power-torsion
cohomology to one with `(I + J)`-power-torsion cohomology. Its value is `J`-power torsion for
free, and `I`-power torsion because `RΓ_Y` is built as an iterated fibre of localizations at
generators of `J`, each of which preserves vanishing of the localization at a generator of `I`;
a module is `(I + J)`-power torsion exactly when it is both `I`- and `J`-power torsion, since
`V(I + J) = V(I) ∩ V(J)`.

## Main definitions

* `Dualizing.localCohomologyOnPowerTorsion` — `RΓ_Y` as a functor from the objects with
  `I`-power-torsion cohomology to those with `(I + J)`-power-torsion cohomology.

## Main results

* `Dualizing.localCohomology_comp_torsion` — `RΓ_Y` preserves `I`-power torsion, so its values on
  `D_{I^∞-torsion}(A)` have `(I + J)`-power-torsion cohomology.
* `Dualizing.localCohomologyCompIso` — **[Stacks, Tag 0BJC]**, `RΓ_Y ∘ RΓ_Z ≅ RΓ_{Y ∩ Z}`.

## Implementation notes

The source states an equality of functors; this is a natural isomorphism, obtained from
uniqueness of right adjoints (`CategoryTheory.Adjunction.rightAdjointUniq`). The first clause of
the source, `Z ∩ Y = V(I + J)`, is `PrimeSpectrum.zeroLocus_sup`; it is what turns the two
separate torsion conditions into the single one for `I + J`.

The spectral sequence `E₂^{p,q} = H^p_Y(H^q_Z(K)) ⇒ H^{p+q}_{Y ∩ Z}(K)` for `K` in `D⁺(A)` of
the same statement is `Dualizing.localCohomology_comp_spectralSequence`, whose abutment is
identified through `Dualizing.localCohomologyCompIso`.

No Noetherian hypothesis and no comparison of the two models of local cohomology is involved:
everything happens in the coreflection model `RΓ_Z` of [Stacks, Tag 0A6Q], where
`Dualizing.localCohomologyAdjunction` is available for every ideal.

## References

* [Stacks Project, Tag 0BJC](https://stacks.math.columbia.edu/tag/0BJC)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace Dualizing

attribute [local instance] HasDerivedCategory.standard

/-! ### A coreflection that keeps a further localization vanishing -/

/-- `Dualizing.Coreflection.exists_finite_localization_coreflection` with one extra conclusion:
an exact endofunctor `H` which preserves the vanishing of each `F i` and which kills `X` also
kills the universal object over `X`. -/
private lemma exists_finite_localization_coreflection_of_isZero
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {ι : Type*} (F : ι → C ⥤ C) [∀ i, (F i).Additive]
    [∀ i, (F i).CommShift ℤ] [∀ i, (F i).IsTriangulated]
    (H : C ⥤ C) [H.Additive] [H.CommShift ℤ] [H.IsTriangulated]
    (η : ∀ i, 𝟭 C ⟶ F i)
    (hη : ∀ i X, IsIso ((η i).app ((F i).obj X)))
    (hFη : ∀ i X, IsIso ((F i).map ((η i).app X)))
    (hpres : ∀ i j X, IsZero ((F j).obj X) → IsZero ((F j).obj ((F i).obj X)))
    (hHpres : ∀ i X, IsZero (H.obj X) → IsZero (H.obj ((F i).obj X)))
    (s : Finset ι) (X : C) (hX : IsZero (H.obj X)) :
    ∃ (Y : C) (a : Y ⟶ X), (∀ i ∈ s, IsZero ((F i).obj Y)) ∧ IsZero (H.obj Y) ∧
      ∀ W, (∀ i ∈ s, IsZero ((F i).obj W)) →
        Function.Bijective (fun g : W ⟶ Y => g ≫ a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨X, 𝟙 X, by simp, hX, ?_⟩
      intro W _
      exact ⟨fun _ _ h => by simpa only [Category.comp_id] using h,
        fun g => ⟨g, Category.comp_id g⟩⟩
  | @insert i s _ ih =>
      obtain ⟨U, b, hU, hHU, hb⟩ := ih
      obtain ⟨T, hT, h₂, h₃, hFT, ha⟩ :=
        Coreflection.exists_fiber_localization (F i) (η i) (hη i) (hFη i) U
      let e : T.obj₂ ≅ U := eqToIso h₂
      refine ⟨T.obj₁, T.mor₁ ≫ e.hom ≫ b, ?_, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hFT
        · exact Triangle.isZero₁_of_isZero₂₃ _ ((F j).map_distinguished _ hT)
            ((hU j hj).of_iso ((F j).mapIso e))
            ((hpres i j U (hU j hj)).of_iso ((F j).mapIso (eqToIso h₃)))
      · exact Triangle.isZero₁_of_isZero₂₃ _ (H.map_distinguished _ hT)
          (hHU.of_iso (H.mapIso e)) ((hHpres i U hHU).of_iso (H.mapIso (eqToIso h₃)))
      · intro W hW
        have k₁ := ha W (hW i (Finset.mem_insert_self _ _))
        have k₂ : Function.Bijective (fun g : W ⟶ T.obj₂ => g ≫ e.hom) :=
          ⟨fun _ _ h => (cancel_mono e.hom).1 h, fun g => ⟨g ≫ e.inv, by simp⟩⟩
        have k₃ := hb W (fun j hj => hW j (Finset.mem_insert_of_mem hj))
        simpa only [Function.comp_def, Category.assoc] using k₃.comp (k₂.comp k₁)

/-! ### Local cohomology preserves power torsion -/

/-- If a localization of `K` vanishes, so does the same localization of `RΓ_{V(J)}(K)`. -/
private lemma localization_isZero_localCohomologyFunctor
    (A : Type u) [CommRing A] (J : Ideal A) (hJ : J.FG)
    (K : DerivedCategory (ModuleCat.{v} A)) (f : A)
    (hf : IsZero ((smallLocalizationFunctor (Submonoid.powers f)).mapDerivedCategory.obj K)) :
    IsZero ((smallLocalizationFunctor (Submonoid.powers f)).mapDerivedCategory.obj
      ((derivedPowerTorsionProperty A J hJ).ι.obj
        ((localCohomologyFunctor A J hJ).obj K))) := by
  classical
  obtain ⟨s, hs⟩ := id hJ
  let F : A → DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A) :=
    fun g => (smallLocalizationFunctor (Submonoid.powers g)).mapDerivedCategory
  let η : ∀ g, 𝟭 (DerivedCategory (ModuleCat.{v} A)) ⟶ F g := fun g =>
    Coreflection.derivedUnit (smallLocalizationFunctor (Submonoid.powers g))
      (smallLocalizationUnit (Submonoid.powers g))
  have hη (g : A) (X : DerivedCategory (ModuleCat.{v} A)) :
      IsIso ((η g).app ((F g).obj X)) :=
    Coreflection.derivedUnit_obj_isIso _ _
      (isIso_smallLocalizationUnit_app_obj (Submonoid.powers g)) X
  have hFη (g : A) (X : DerivedCategory (ModuleCat.{v} A)) :
      IsIso ((F g).map ((η g).app X)) :=
    Coreflection.derivedUnit_map_isIso _ _
      (isIso_smallLocalizationFunctor_map_smallLocalizationUnit_app (Submonoid.powers g)) X
  have hpres (g g' : A) (X : DerivedCategory (ModuleCat.{v} A))
      (h : IsZero ((F g').obj X)) : IsZero ((F g').obj ((F g).obj X)) :=
    isZero_mapDerivedCategory_smallLocalization_comp (Submonoid.powers g') (Submonoid.powers g) X h
  obtain ⟨Y, a, hY, hHY, ha⟩ :=
    exists_finite_localization_coreflection_of_isZero F (F f) η hη hFη hpres
      (fun g => hpres g f) s K hf
  -- `Y` and `RΓ_{V(J)}(K)` are both universal over `K`, hence isomorphic.
  let P := derivedPowerTorsionProperty A J hJ
  -- `W₀` is spelled through `localCohomologyRightAdjoint` rather than `localCohomologyFunctor`
  -- so that it matches the right adjoint of `adj` at reducible transparency, which is what the
  -- `Adjunction.homEquiv_symm_apply` rewrite below needs.
  let W₀ : P.FullSubcategory := (localCohomologyRightAdjoint A J hJ).1.obj K
  let W₁ : P.FullSubcategory :=
    ⟨Y, (derivedPowerTorsionProperty_iff_isZero_mapDerivedCategory J hJ s hs Y).2 hY⟩
  let adj := localCohomologyAdjunction A J hJ
  let e₀ (W : P.FullSubcategory) : (W ⟶ W₀) ≃ (P.ι.obj W ⟶ K) := (adj.homEquiv W K).symm
  let e₁ (W : P.FullSubcategory) : (W ⟶ W₁) ≃ (P.ι.obj W ⟶ K) :=
    Equiv.ofBijective (fun g => g.hom ≫ a) ((ha W.obj
      ((derivedPowerTorsionProperty_iff_isZero_mapDerivedCategory J hJ s hs W.obj).mp
        W.property)).comp P.fullyFaithfulι.homEquiv.bijective)
  have he₀ (W : P.FullSubcategory) (g : W ⟶ W₀) : (e₀ W) g = g.hom ≫ adj.counit.app K := by
    show (adj.homEquiv W K).symm g = _
    rw [Adjunction.homEquiv_symm_apply]
    simp only [ObjectProperty.ι_map]
  have he₁ (W : P.FullSubcategory) (g : W ⟶ W₁) : (e₁ W) g = g.hom ≫ a := rfl
  let φ : W₀ ⟶ W₁ := (e₁ W₀).symm ((e₀ W₀) (𝟙 W₀))
  let ψ : W₁ ⟶ W₀ := (e₀ W₁).symm (P.ι.map (𝟙 W₁) ≫ a)
  have h₀ : (e₀ W₀) (𝟙 W₀) = adj.counit.app K := by
    simp only [he₀, ObjectProperty.FullSubcategory.id_hom, Category.id_comp]
  have hφ : φ.hom ≫ a = adj.counit.app K :=
    (he₁ W₀ φ).symm.trans (((e₁ W₀).apply_symm_apply _).trans h₀)
  have hψ : ψ.hom ≫ adj.counit.app K = a := by
    calc
      ψ.hom ≫ adj.counit.app K = (e₀ W₁) ψ := (he₀ W₁ ψ).symm
      _ = P.ι.map (𝟙 W₁) ≫ a := (e₀ W₁).apply_symm_apply _
      _ = a := by
        show 𝟙 W₁.obj ≫ a = a
        exact Category.id_comp a
  have hφψ : φ ≫ ψ = 𝟙 W₀ := by
    apply (e₀ W₀).injective
    calc
      (e₀ W₀) (φ ≫ ψ) = (φ ≫ ψ).hom ≫ adj.counit.app K := he₀ W₀ _
      _ = φ.hom ≫ a := by rw [ObjectProperty.FullSubcategory.comp_hom, Category.assoc, hψ]
      _ = adj.counit.app K := hφ
      _ = (e₀ W₀) (𝟙 W₀) := h₀.symm
  have hψφ : ψ ≫ φ = 𝟙 W₁ := by
    apply (e₁ W₁).injective
    calc
      (e₁ W₁) (ψ ≫ φ) = (ψ ≫ φ).hom ≫ a := he₁ W₁ _
      _ = ψ.hom ≫ adj.counit.app K := by
        rw [ObjectProperty.FullSubcategory.comp_hom, Category.assoc, hφ]
      _ = a := hψ
      _ = (e₁ W₁) (𝟙 W₁) := by
        simp only [he₁, ObjectProperty.FullSubcategory.id_hom, Category.id_comp]
  exact hHY.of_iso ((F f).mapIso (P.ι.mapIso (⟨φ, ψ, hφψ, hψφ⟩ : W₀ ≅ W₁)))

/-- Local cohomology supported on `V(J)` preserves `I`-power torsion. -/
private lemma derivedPowerTorsion_localCohomologyFunctor
    (A : Type u) [CommRing A] (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : derivedPowerTorsionProperty A I hI K) :
    derivedPowerTorsionProperty A I hI
      ((derivedPowerTorsionProperty A J hJ).ι.obj ((localCohomologyFunctor A J hJ).obj K)) := by
  classical
  obtain ⟨s, hs⟩ := id hI
  refine (derivedPowerTorsionProperty_iff_isZero_mapDerivedCategory _ hI s hs _).2 fun f hf => ?_
  exact localization_isZero_localCohomologyFunctor A J hJ K f
    ((derivedPowerTorsionProperty_iff_isZero_mapDerivedCategory _ hI s hs K).mp hK f hf)

/-- **[Stacks, Tag 0BJC].** Local cohomology supported on `V(J)` of an object with
`I`-power-torsion cohomology has `(I + J)`-power-torsion cohomology, because
`V(I + J) = V(I) ∩ V(J)`. -/
@[stacks 0BJC "the target of the composition of the local cohomology functors"]
theorem localCohomology_comp_torsion (A : Type u) [CommRing A] (I J : Ideal A)
    (hI : I.FG) (hJ : J.FG) (K : PowerTorsionDerivedCategory A I hI) :
    derivedPowerTorsionProperty A (I + J) (Submodule.FG.sup hI hJ)
      (((derivedPowerTorsionProperty A I hI).ι ⋙ localCohomologyFunctor A J hJ ⋙
        (derivedPowerTorsionProperty A J hJ).ι).obj K) := by
  set L := ((derivedPowerTorsionProperty A I hI).ι ⋙ localCohomologyFunctor A J hJ ⋙
    (derivedPowerTorsionProperty A J hJ).ι).obj K with hL
  have hItor : derivedPowerTorsionProperty A I hI L :=
    derivedPowerTorsion_localCohomologyFunctor A I J hI hJ _
      ((derivedPowerTorsionProperty A I hI).prop_ι_obj K)
  have hJtor : derivedPowerTorsionProperty A J hJ L :=
    (derivedPowerTorsionProperty A J hJ).prop_ι_obj _
  exact fun i => isIPowerTorsion_of_support_subset (Submodule.FG.sup hI hJ) fun p hp =>
    (PrimeSpectrum.zeroLocus_sup I J).ge ⟨support_subset_zeroLocus_of_isIPowerTorsion (hItor i) hp,
      support_subset_zeroLocus_of_isIPowerTorsion (hJtor i) hp⟩

/-- Local cohomology supported on `V(J)`, as a functor from the objects with `I`-power-torsion
cohomology to the objects with `(I + J)`-power-torsion cohomology. -/
noncomputable def localCohomologyOnPowerTorsion (A : Type u) [CommRing A] (I J : Ideal A)
    (hI : I.FG) (hJ : J.FG) :
    PowerTorsionDerivedCategory.{u, v} A I hI ⥤
      PowerTorsionDerivedCategory.{u, v} A (I + J) (Submodule.FG.sup hI hJ) :=
  (derivedPowerTorsionProperty A (I + J) (Submodule.FG.sup hI hJ)).lift
    ((derivedPowerTorsionProperty A I hI).ι ⋙ localCohomologyFunctor A J hJ ⋙
      (derivedPowerTorsionProperty A J hJ).ι)
    (localCohomology_comp_torsion A I J hI hJ)

/-- **[Stacks, Tag 0BJC].** `RΓ_Y ∘ RΓ_Z = RΓ_{Y ∩ Z}` for `Z = V(I)` and `Y = V(J)`: iterated
local cohomology is local cohomology supported on `V(I) ∩ V(J) = V(I + J)`. Both functors are
right adjoint to the inclusion of the objects with `(I + J)`-power-torsion cohomology into those
with `I`-power-torsion cohomology, so they agree. -/
@[stacks 0BJC "the composition of the local cohomology functors"]
noncomputable def localCohomologyCompIso (A : Type u) [CommRing A] (I J : Ideal A)
    (hI : I.FG) (hJ : J.FG) :
    localCohomologyFunctor.{u, v} A I hI ⋙ localCohomologyOnPowerTorsion A I J hI hJ ≅
      localCohomologyFunctor A (I + J) (Submodule.FG.sup hI hJ) := by
  let P := derivedPowerTorsionProperty.{u, v} A (I + J) (Submodule.FG.sup hI hJ)
  let PI := derivedPowerTorsionProperty.{u, v} A I hI
  let PJ := derivedPowerTorsionProperty.{u, v} A J hJ
  have hsplit (W : P.FullSubcategory) (n : ℤ) :
      Module.support A ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj W.obj) ⊆
        PrimeSpectrum.zeroLocus (I : Set A) ∩ PrimeSpectrum.zeroLocus (J : Set A) := by
    have hs := support_subset_zeroLocus_of_isIPowerTorsion (W.property n)
    rwa [Ideal.add_eq_sup, PrimeSpectrum.zeroLocus_sup] at hs
  have hPI (W : P.FullSubcategory) : PI W.obj := fun n =>
    isIPowerTorsion_of_support_subset hI fun _ hp => (hsplit W n hp).1
  have hPJ (W : P.FullSubcategory) : PJ W.obj := fun n =>
    isIPowerTorsion_of_support_subset hJ fun _ hp => (hsplit W n hp).2
  let toI : P.FullSubcategory ⥤ PI.FullSubcategory :=
    { obj W := ⟨W.obj, hPI W⟩
      map f := ObjectProperty.homMk f.hom
      map_id := by intro; apply ObjectProperty.hom_ext; rfl
      map_comp := by intros; apply ObjectProperty.hom_ext; rfl }
  let toJ : P.FullSubcategory ⥤ PJ.FullSubcategory :=
    { obj W := ⟨W.obj, hPJ W⟩
      map f := ObjectProperty.homMk f.hom
      map_id := by intro; apply ObjectProperty.hom_ext; rfl
      map_comp := by intros; apply ObjectProperty.hom_ext; rfl }
  let hiJ : toJ.FullyFaithful :=
    { preimage f := ObjectProperty.homMk f.hom
      map_preimage := by intro X Y f; apply ObjectProperty.hom_ext PJ; rfl
      preimage_map := by intro X Y f; apply ObjectProperty.hom_ext P; rfl }
  let comm₁ : toJ ⋙ PJ.ι ≅ toI ⋙ PI.ι :=
    NatIso.ofComponents (fun W => Iso.refl W.obj) (by intros; simp [toI, toJ])
  let comm₂ : PI.ι ⋙ localCohomologyFunctor A J hJ ≅
      localCohomologyOnPowerTorsion A I J hI hJ ⋙ toJ :=
    NatIso.ofComponents (fun X => PJ.isoMk (Iso.refl _)) (by
      intro X Y f
      apply ObjectProperty.hom_ext
      change ((localCohomologyFunctor A J hJ).map f.hom).hom ≫ 𝟙 _ =
        𝟙 _ ≫ ((localCohomologyFunctor A J hJ).map f.hom).hom
      simp)
  let commIn : toI ⋙ PI.ι ≅ P.ι :=
    NatIso.ofComponents (fun W => Iso.refl W.obj) (by intros; simp [toI])
  exact ((((localCohomologyAdjunction A J hJ).restrictFullyFaithful hiJ PI.fullyFaithfulι
    comm₁ comm₂).comp (localCohomologyAdjunction A I hI)).ofNatIsoLeft
      commIn).rightAdjointUniq
        (localCohomologyAdjunction A (I + J) (Submodule.FG.sup hI hJ))

end Dualizing

end
