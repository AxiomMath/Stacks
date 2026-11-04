module

public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.Coreflection
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.SmallLocalization
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.Algebra.Module.Shrink

/-!
# The right adjoint defining local cohomology

Let `I` be a finitely generated ideal of a commutative ring `A`. The inclusion into `D(A)` of
the full subcategory of objects whose cohomology modules are `I`-power torsion admits a right
adjoint; that right adjoint is local cohomology with support in `V(I)`.

## Main definitions

* `Dualizing.localCohomologyRightAdjoint` — the right adjoint together with its adjunction.
* `Dualizing.localCohomologyAdjunction` — the adjunction of that construction, on its own.

## Main results

* `Dualizing.localCohomologyRightAdjoint_nonempty` — existence of the right adjoint.

## Implementation notes

The construction uses the fibres of localization at a finite set of generators of `I`. Their
common kernel consists exactly of the objects with power-torsion cohomology, and the universal
morphisms produced by `Dualizing.Coreflection.exists_finite_localization_coreflection` assemble
into the right adjoint. Localization modules are replaced by the equivalent small models of
`StacksFrontier/RingTheory/Dualizing/TorsionComplete/SmallLocalization.lean`, which keeps the
universes of the ring and of the modules independent.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- The inclusion of the objects of `D(A)` with `I`-power-torsion cohomology has a right
adjoint. The witness is produced from the coreflection onto the common kernel of the derived
localizations at a finite set of generators of `I`. -/
lemma localCohomologyRightAdjoint_nonempty
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    Nonempty (Σ F : DerivedCategory (ModuleCat.{v} A) ⥤
        PowerTorsionDerivedCategory A I hI,
      (derivedPowerTorsionProperty A I hI).ι ⊣ F) := by
  classical
  let s := Classical.choose hI
  have hs := Classical.choose_spec hI
  let F : A → DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A) :=
    fun f => (smallLocalizationFunctor (Submonoid.powers f)).mapDerivedCategory
  let η : ∀ f, 𝟭 (DerivedCategory (ModuleCat.{v} A)) ⟶ F f := fun f =>
    Coreflection.derivedUnit (smallLocalizationFunctor (Submonoid.powers f))
      (smallLocalizationUnit (Submonoid.powers f))
  have hη (f : A) (X : DerivedCategory (ModuleCat.{v} A)) : IsIso ((η f).app ((F f).obj X)) :=
    Coreflection.derivedUnit_obj_isIso _ _
      (isIso_smallLocalizationUnit_app_obj (Submonoid.powers f)) X
  have hFη (f : A) (X : DerivedCategory (ModuleCat.{v} A)) : IsIso ((F f).map ((η f).app X)) :=
    Coreflection.derivedUnit_map_isIso _ _
      (isIso_smallLocalizationFunctor_map_smallLocalizationUnit_app (Submonoid.powers f)) X
  have hpres (f g : A) (X : DerivedCategory (ModuleCat.{v} A))
      (h : IsZero ((F g).obj X)) : IsZero ((F g).obj ((F f).obj X)) :=
    isZero_mapDerivedCategory_smallLocalization_comp
      (Submonoid.powers g) (Submonoid.powers f) X h
  have hex := fun X =>
    Coreflection.exists_finite_localization_coreflection F η hη hFη hpres s X
  choose Y a hY ha using hex
  let P := derivedPowerTorsionProperty A I hI
  let G : DerivedCategory (ModuleCat.{v} A) → P.FullSubcategory := fun X =>
    ⟨Y X, (derivedPowerTorsionProperty_iff_isZero_mapDerivedCategory I hI s hs (Y X)).mpr (hY X)⟩
  have hb (X : DerivedCategory (ModuleCat.{v} A)) (W : P.FullSubcategory) :
      Function.Bijective (fun k : W ⟶ G X => P.ι.map k ≫ a X) :=
    (ha X W.obj
      ((derivedPowerTorsionProperty_iff_isZero_mapDerivedCategory I hI s hs W.obj).mp
        W.property)).comp
      P.fullyFaithfulι.homEquiv.bijective
  let e : ∀ (W : P.FullSubcategory) X, (P.ι.obj W ⟶ X) ≃ (W ⟶ G X) :=
    fun W X => (Equiv.ofBijective _ (hb X W)).symm
  have he : ∀ (W : P.FullSubcategory) X (k : P.ι.obj W ⟶ X),
      P.ι.map (e W X k) ≫ a X = k :=
    fun W X k => (Equiv.ofBijective _ (hb X W)).apply_symm_apply k
  have hn : ∀ (W' W : P.FullSubcategory) X (f : W' ⟶ W) (k : P.ι.obj W ⟶ X),
      e W' X (P.ι.map f ≫ k) = f ≫ e W X k := by
    intro W' W X f k
    apply (hb X W').injective
    dsimp only
    rw [he, P.ι.map_comp, Category.assoc, he]
  exact ⟨⟨Adjunction.rightAdjointOfEquiv e hn, Adjunction.adjunctionOfEquivRight e hn⟩⟩

/-- **Stacks 0A6R, local cohomology right adjoint.** The inclusion of the derived category of
objects with `I`-power-torsion cohomology has a right adjoint. This construction supplies the
functor denoted `RΓ_Z` for `Z = V(I)`. -/
@[stacks 0A6R "local_cohomology_right_adjoint"]
noncomputable def localCohomologyRightAdjoint
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    Σ F : DerivedCategory (ModuleCat.{v} A) ⥤
        PowerTorsionDerivedCategory A I hI,
      (derivedPowerTorsionProperty A I hI).ι ⊣ F :=
  Classical.choice (by exact localCohomologyRightAdjoint_nonempty A I hI)

/-- The adjunction supplied by `Dualizing.localCohomologyRightAdjoint`. Its right adjoint is
the functor `Dualizing.localCohomologyFunctor`. -/
noncomputable def localCohomologyAdjunction
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    (derivedPowerTorsionProperty A I hI).ι ⊣
      (localCohomologyRightAdjoint A I hI).1 :=
  (localCohomologyRightAdjoint A I hI).2

end Dualizing
