module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.ProEtale.AdicConstructibleComplexes
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.ChangeOfRings
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.InverseImageEssSurj
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.InverseImageLimits
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.DerivedTensor
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.DerivedChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.InverseImage
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.InverseImage

/-!
# Restriction of objects of `D(X_proét, Λ)` and their reductions

Let `g : Z ⟶ X` be a morphism of schemes, `Λ` a ring and `I ⊆ Λ` an ideal. The restriction
`K ↦ K|_Z = g⁻¹K` of an object of `D(X_proét, Λ)` is the inverse image of pro-étale sheaves of
`Λ`-modules applied termwise (`AlgebraicGeometry.ProEtale.derivedInverseImage`). This file
compares the reduction `K|_Z ⊗_Λ^L \underline{Λ/I}` of a restriction with the restriction of the
reduction `K ⊗_Λ^L \underline{Λ/I}`, on cohomology sheaves:
`Hⁱ(K|_Z ⊗_Λ^L \underline{Λ/I}) ≅ g⁻¹Hⁱ(K ⊗_Λ^L \underline{Λ/I})`.

So the cohomology sheaves of the reduction of a restriction are the restrictions of the
cohomology sheaves of the reduction; this is how a property of `K` read on its reduction, such as
having constructible or locally constant cohomology sheaves (Stacks 09C1, 09C4), is transported to
a stratum.

## Main definitions

* `AlgebraicGeometry.ProEtale.constantSheafCompProetaleModuleInverseImageIso`: the inverse image
  of a constant pro-étale sheaf of modules is the constant sheaf with the same value.
* `AlgebraicGeometry.ProEtale.derivedInverseImageCompIso`: restriction along a composite is the
  composite of the restrictions.

## Main results

* `AlgebraicGeometry.ProEtale.nonempty_homology_tensor_single_proetaleModuleInverseImage_iso`:
  `g⁻¹Hⁱ(K ⊗_Λ^L N) ≅ Hⁱ(g⁻¹K ⊗_Λ^L g⁻¹N)` for a sheaf of `Λ`-modules `N`.
* `ProEtale.nonempty_homology_tensor_constantSheaf_proetaleModuleInverseImage_iso`:
  `g⁻¹Hⁱ(K ⊗_Λ^L \underline{N}) ≅ Hⁱ(g⁻¹K ⊗_Λ^L \underline{N})` for a `Λ`-module `N`.
* `AlgebraicGeometry.ProEtale.nonempty_homology_derivedReduction_derivedInverseImage_iso`:
  `Hⁱ(K|_Z ⊗_Λ^L \underline{Λ/I}) ≅ g⁻¹Hⁱ(K ⊗_Λ^L \underline{Λ/I})`.
* `AlgebraicGeometry.ProEtale.hasTorAmplitude_derivedReduction_iff`: the Tor amplitude of the
  reduction, read over `Λ`.
* `AlgebraicGeometry.ProEtale.hasTorAmplitude_derivedReduction_derivedInverseImage`: when every
  sheaf of `Λ/I`-modules on `Z_proét` is an inverse image, `K|_Z ⊗_Λ^L \underline{Λ/I}` has the
  Tor amplitude of `K ⊗_Λ^L \underline{Λ/I}`.
* `AlgebraicGeometry.ProEtale.hasTorAmplitude_derivedReduction_derivedInverseImage_of_isImmersion`:
  the same along any immersion `g`, the statement being local on `Z`.

## Implementation notes

The reduction is the derived extension of scalars along `Λ → Λ/I`; read over `Λ` it is the
derived tensor product with the constant sheaf `\underline{Λ/I}`
(`Stacks.ModuleSheaf.nonempty_restrictScalars_derivedExtendScalars_iso`). Inverse image commutes
with the cohomology of a derived tensor product with a bounded above object
(`Stacks.ModuleSheaf.nonempty_homology_sheafPullback_tensor_iso`) and with restriction of scalars,
and restriction of scalars along the surjection `Λ → Λ/I` is fully faithful, so the comparison
over `Λ` descends to `Λ/I`.

## References

* [Stacks Project, Tag 09C1](https://stacks.math.columbia.edu/tag/09C1)
* [Stacks Project, Tag 09C4](https://stacks.math.columbia.edu/tag/09C4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Sheaf.symmetricCategory Stacks.ModuleSheaf.derivedMonoidal Stacks.ModuleSheaf.derivedSymmetric

variable {Z X : Scheme.{u}} (g : Z ⟶ X)

/-- **Inverse image of a constant pro-étale sheaf of modules is constant**, with the same
value. -/
def constantSheafCompProetaleModuleInverseImageIso (Λ : Type (max (u + 1) w)) [CommRing Λ] :
    constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ) ⋙
        proetaleModuleInverseImage.{u, max (u + 1) w, w} g Λ ≅
      constantSheaf (Scheme.ProEt.topology Z) (ModuleCat.{max (u + 1) w} Λ) :=
  Functor.isoWhiskerLeft _ (proetaleModuleInverseImageIsoSheafPullback.{u, max (u + 1) w, w} Λ g) ≪≫
    Stacks.ConstantSheaf.constantSheafCompSheafPullbackIso (Scheme.proetaleBaseChange g) _ _ _
      terminalIsTerminal terminalIsTerminal
      ((IsTerminal.isTerminalObj (Scheme.proetaleBaseChange g) _ terminalIsTerminal).uniqueUpToIso
        terminalIsTerminal)

variable {Λ : Type (max (u + 1) w)} [CommRing Λ]

/-- **Inverse image commutes with the cohomology of the derived tensor product with a sheaf**:
`g⁻¹Hⁱ(K ⊗_Λ^L N) ≅ Hⁱ(g⁻¹K ⊗_Λ^L g⁻¹N)` for an object `K` of the derived category of
pro-étale sheaves of `Λ`-modules on `X` and a sheaf of `Λ`-modules `N`. -/
theorem nonempty_homology_tensor_single_proetaleModuleInverseImage_iso
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)))
    (N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) (i : ℤ) :
    Nonempty ((proetaleModuleInverseImage.{u, max (u + 1) w, w} g Λ).obj
        ((DerivedCategory.homologyFunctor _ i).obj
          (K ⊗ (DerivedCategory.singleFunctor _ 0).obj N)) ≅
      (DerivedCategory.homologyFunctor _ i).obj
        ((proetaleModuleInverseImage.{u, max (u + 1) w, w} g Λ).mapDerivedCategory.obj K ⊗
          (DerivedCategory.singleFunctor _ 0).obj
            ((proetaleModuleInverseImage.{u, max (u + 1) w, w} g Λ).obj N))) := by
  have := isFiltered_costructuredArrow_proetaleBaseChange g
  let Φ := (Scheme.proetaleBaseChange g).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)
  let e := proetaleModuleInverseImageIsoSheafPullback.{u, max (u + 1) w, w} Λ g
  have : PreservesFiniteLimits Φ := preservesFiniteLimits_of_natIso e
  have : PreservesFiniteColimits Φ := preservesFiniteColimits_of_natIso e
  obtain ⟨e₁⟩ := Stacks.ModuleSheaf.nonempty_homology_sheafPullback_tensor_iso
    (Scheme.proetaleBaseChange g) Λ (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z) K
    ((DerivedCategory.singleFunctor _ 0).obj N) 0 i
  exact ⟨(e.app _) ≪≫ e₁ ≪≫ (DerivedCategory.homologyFunctor _ i).mapIso
    ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso Φ _ e.symm).app K ⊗ᵢ
      ((Φ.mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (e.app N).symm))⟩

/-- **Inverse image commutes with the cohomology of the derived tensor product with a constant
sheaf**: `g⁻¹Hⁱ(K ⊗_Λ^L \underline{N}) ≅ Hⁱ(g⁻¹K ⊗_Λ^L \underline{N})` for an object `K` of
the derived category of pro-étale sheaves of `Λ`-modules on `X` and a `Λ`-module `N`. -/
theorem nonempty_homology_tensor_constantSheaf_proetaleModuleInverseImage_iso
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)))
    (N : ModuleCat.{max (u + 1) w} Λ) (i : ℤ) :
    Nonempty ((proetaleModuleInverseImage.{u, max (u + 1) w, w} g Λ).obj
        ((DerivedCategory.homologyFunctor _ i).obj
          (K ⊗ (DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj N))) ≅
      (DerivedCategory.homologyFunctor _ i).obj
        ((proetaleModuleInverseImage.{u, max (u + 1) w, w} g Λ).mapDerivedCategory.obj K ⊗
          (DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf (Scheme.ProEt.topology Z) (ModuleCat.{max (u + 1) w} Λ)).obj N))) := by
  obtain ⟨e⟩ := nonempty_homology_tensor_single_proetaleModuleInverseImage_iso g K
    ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj N) i
  exact ⟨e ≪≫ (DerivedCategory.homologyFunctor _ i).mapIso (Iso.refl _ ⊗ᵢ
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((constantSheafCompProetaleModuleInverseImageIso g Λ).app N))⟩

variable (Λ) in
/-- **The cohomology sheaves of the reduction of a restriction are the restrictions of the
cohomology sheaves of the reduction.** For a morphism of schemes `g : Z ⟶ X`, an object `K` of
`D(X_proét, Λ)` and an ideal `I ⊆ Λ`,
`Hⁱ(K|_Z ⊗_Λ^L \underline{Λ/I}) ≅ g⁻¹Hⁱ(K ⊗_Λ^L \underline{Λ/I})` as sheaves of
`Λ/I`-modules on `Z_proét`.

Read over `Λ`, both sides are cohomology sheaves of derived tensor products with the constant
sheaf `\underline{Λ/I}`, which inverse image preserves; restriction of scalars along `Λ → Λ/I`
is fully faithful. -/
theorem nonempty_homology_derivedReduction_derivedInverseImage_iso (I : Ideal Λ)
    (K : DerivedSheaves.{u, max (u + 1) w, w} X Λ) (i : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor _ i).obj
        ((derivedReduction.{u, w} Z Λ I).obj
          ((derivedInverseImage.{u, max (u + 1) w, w} g Λ).obj K)) ≅
      (proetaleModuleInverseImage.{u, max (u + 1) w, w} g (Λ ⧸ I)).obj
        ((DerivedCategory.homologyFunctor _ i).obj ((derivedReduction.{u, w} X Λ I).obj K))) := by
  let f := Ideal.Quotient.mk I
  let JX := Scheme.ProEt.topology X
  let JZ := Scheme.ProEt.topology Z
  let RX := Stacks.ModuleSheaf.restrictScalars JX f
  let RZ := Stacks.ModuleSheaf.restrictScalars JZ f
  let gΛ := proetaleModuleInverseImage.{u, max (u + 1) w, w} g Λ
  let K' := (derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K
  let N := (ModuleCat.restrictScalars.{max (u + 1) w} f).obj (ModuleCat.of (Λ ⧸ I) (Λ ⧸ I))
  let L := gΛ.mapDerivedCategory.obj K'
  let eL : (derivedModuleEquiv.{u, max (u + 1) w, w} Z Λ).inverse.obj
      ((derivedInverseImage.{u, max (u + 1) w, w} g Λ).obj K) ≅ L :=
    ((derivedModuleEquiv.{u, max (u + 1) w, w} Z Λ).unitIso.app L).symm
  obtain ⟨a⟩ := Stacks.ModuleSheaf.nonempty_restrictScalars_derivedExtendScalars_iso (J := JZ) f L
  obtain ⟨b⟩ := Stacks.ModuleSheaf.nonempty_restrictScalars_derivedExtendScalars_iso (J := JX) f K'
  obtain ⟨c⟩ := nonempty_homology_tensor_constantSheaf_proetaleModuleInverseImage_iso g K' N i
  have e : RZ.obj ((DerivedCategory.homologyFunctor _ i).obj
        ((Stacks.ModuleSheaf.derivedExtendScalars JZ f).obj L)) ≅
      RZ.obj ((proetaleModuleInverseImage.{u, max (u + 1) w, w} g (Λ ⧸ I)).obj
        ((DerivedCategory.homologyFunctor _ i).obj
          ((Stacks.ModuleSheaf.derivedExtendScalars JX f).obj K'))) :=
    ((RZ.mapDerivedCategoryHomologyIso i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso (a ≪≫ β_ _ _) ≪≫ c.symm ≪≫
      gΛ.mapIso ((DerivedCategory.homologyFunctor _ i).mapIso (β_ _ _ ≪≫ b.symm) ≪≫
        (RX.mapDerivedCategoryHomologyIso i).app _) ≪≫
      ((proetaleModuleInverseImageRestrictScalarsIso g f).app _).symm
  exact ⟨(DerivedCategory.homologyFunctor _ i).mapIso
      ((Stacks.ModuleSheaf.derivedExtendScalars JZ f).mapIso eL) ≪≫
    (Stacks.ModuleSheaf.fullyFaithfulRestrictScalars JZ Ideal.Quotient.mk_surjective).preimageIso e⟩

variable (Λ) in
/-- **Inverse image is compatible with composition on `D(X_proét, Λ)`**: restricting to `Z` and
then to `Y` is restricting along the composite. -/
def derivedInverseImageCompIso {Y : Scheme.{u}} (a : Y ⟶ Z) :
    derivedInverseImage.{u, max (u + 1) w, w} (a ≫ g) Λ ≅
      derivedInverseImage.{u, max (u + 1) w, w} g Λ ⋙
        derivedInverseImage.{u, max (u + 1) w, w} a Λ :=
  let eX := derivedModuleEquiv.{u, max (u + 1) w, w} X Λ
  let eY := derivedModuleEquiv.{u, max (u + 1) w, w} Y Λ
  let eZ := derivedModuleEquiv.{u, max (u + 1) w, w} Z Λ
  let gD := (proetaleModuleInverseImage.{u, max (u + 1) w, w} g Λ).mapDerivedCategory
  let aD := (proetaleModuleInverseImage.{u, max (u + 1) w, w} a Λ).mapDerivedCategory
  Functor.isoWhiskerLeft eX.inverse
      (Functor.isoWhiskerRight
          (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
              (proetaleModuleInverseImageCompIso.{u, max (u + 1) w, w} Λ a g).symm ≪≫
            Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _) eY.functor ≪≫
        Functor.associator gD aD eY.functor ≪≫
        Functor.isoWhiskerLeft gD (Functor.leftUnitor (aD ⋙ eY.functor)).symm ≪≫
        Functor.isoWhiskerLeft gD (Functor.isoWhiskerRight eZ.unitIso (aD ⋙ eY.functor)) ≪≫
        Functor.isoWhiskerLeft gD (Functor.associator eZ.functor eZ.inverse (aD ⋙ eY.functor)) ≪≫
        (Functor.associator gD eZ.functor (eZ.inverse ⋙ aD ⋙ eY.functor)).symm) ≪≫
    (Functor.associator eX.inverse (gD ⋙ eZ.functor) (eZ.inverse ⋙ aD ⋙ eY.functor)).symm

variable (Λ) in
/-- **The Tor amplitude of the reduction, read over `Λ`.** For an object `K` of `D(Y_proét, Λ)`
and an ideal `I ⊆ Λ`, the reduction `K ⊗_Λ^L \underline{Λ/I}` has Tor amplitude in `S` exactly
when `Hⁱ(K ⊗_Λ^L F) = 0` for every `i ∉ S` and every sheaf of `Λ/I`-modules `F`, read over `Λ`:
this is the projection formula
`Stacks.ModuleSheaf.nonempty_restrictScalars_homology_tensor_derivedExtendScalars_iso`, and
restriction of scalars along `Λ → Λ/I` reflects vanishing. -/
theorem hasTorAmplitude_derivedReduction_iff {Y : Scheme.{u}} (I : Ideal Λ)
    (K : DerivedSheaves.{u, max (u + 1) w, w} Y Λ) (S : Set ℤ) :
    Stacks.ModuleSheaf.HasTorAmplitude (J := Scheme.ProEt.topology Y)
        ((derivedReduction.{u, w} Y Λ I).obj K) S ↔
      ∀ (F : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{max (u + 1) w} (Λ ⧸ I))) (i : ℤ),
        i ∉ S → IsZero ((DerivedCategory.homologyFunctor _ i).obj
          ((derivedModuleEquiv.{u, max (u + 1) w, w} Y Λ).inverse.obj K ⊗
            (DerivedCategory.singleFunctor _ 0).obj
              ((Stacks.ModuleSheaf.restrictScalars (Scheme.ProEt.topology Y)
                (Ideal.Quotient.mk I)).obj F))) := by
  refine forall_congr' fun F => forall_congr' fun i => imp_congr_right fun _ => ?_
  let f := Ideal.Quotient.mk I
  let R := Stacks.ModuleSheaf.restrictScalars (Scheme.ProEt.topology Y) f
  let K' := (derivedModuleEquiv.{u, max (u + 1) w, w} Y Λ).inverse.obj K
  obtain ⟨p⟩ := Stacks.ModuleSheaf.nonempty_restrictScalars_homology_tensor_derivedExtendScalars_iso
    (J := Scheme.ProEt.topology Y) f F K' i
  exact ⟨fun h => ((R.map_isZero (h.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
      (β_ _ _)))).of_iso p.symm).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso (β_ _ _)),
    fun h => (Stacks.ModuleSheaf.isZero_of_isZero_restrictScalars_obj f
      ((h.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso (β_ _ _))).of_iso p)).of_iso
        ((DerivedCategory.homologyFunctor _ i).mapIso (β_ _ _))⟩

/-- Inverse image commutes with the cohomology of the derived tensor product with a sheaf of
`Λ/I`-modules, read over `Λ`. -/
private theorem nonempty_homology_tensor_single_restrictScalars_proetaleModuleInverseImage_iso
    (I : Ideal Λ)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)))
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} (Λ ⧸ I))) (i : ℤ) :
    Nonempty ((proetaleModuleInverseImage.{u, max (u + 1) w, w} g Λ).obj
        ((DerivedCategory.homologyFunctor _ i).obj
          (K ⊗ (DerivedCategory.singleFunctor _ 0).obj
            ((Stacks.ModuleSheaf.restrictScalars (Scheme.ProEt.topology X)
              (Ideal.Quotient.mk I)).obj F))) ≅
      (DerivedCategory.homologyFunctor _ i).obj
        ((proetaleModuleInverseImage.{u, max (u + 1) w, w} g Λ).mapDerivedCategory.obj K ⊗
          (DerivedCategory.singleFunctor _ 0).obj
            ((Stacks.ModuleSheaf.restrictScalars (Scheme.ProEt.topology Z)
              (Ideal.Quotient.mk I)).obj
              ((proetaleModuleInverseImage.{u, max (u + 1) w, w} g (Λ ⧸ I)).obj F)))) := by
  obtain ⟨c⟩ := nonempty_homology_tensor_single_proetaleModuleInverseImage_iso g K
    ((Stacks.ModuleSheaf.restrictScalars (Scheme.ProEt.topology X) (Ideal.Quotient.mk I)).obj F) i
  exact ⟨c ≪≫ (DerivedCategory.homologyFunctor _ i).mapIso (Iso.refl _ ⊗ᵢ
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((proetaleModuleInverseImageRestrictScalarsIso g (Ideal.Quotient.mk I)).app F).symm)⟩

variable (Λ) in
/-- **Vanishing against an inverse image survives restriction.** If `Hⁱ(K ⊗_Λ^L F₀) = 0` for a
sheaf of `Λ/I`-modules `F₀` on `X`, read over `Λ`, then `Hⁱ(K|_Z ⊗_Λ^L g⁻¹F₀) = 0`: inverse image
commutes with the cohomology of the derived tensor product with a sheaf and with restriction of
scalars. -/
theorem isZero_homology_tensor_single_restrictScalars_derivedInverseImage (I : Ideal Λ)
    (K : DerivedSheaves.{u, max (u + 1) w, w} X Λ)
    (F₀ : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} (Λ ⧸ I))) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K ⊗
        (DerivedCategory.singleFunctor _ 0).obj
          ((Stacks.ModuleSheaf.restrictScalars (Scheme.ProEt.topology X)
            (Ideal.Quotient.mk I)).obj F₀)))) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((derivedModuleEquiv.{u, max (u + 1) w, w} Z Λ).inverse.obj
          ((derivedInverseImage.{u, max (u + 1) w, w} g Λ).obj K) ⊗
        (DerivedCategory.singleFunctor _ 0).obj
          ((Stacks.ModuleSheaf.restrictScalars (Scheme.ProEt.topology Z) (Ideal.Quotient.mk I)).obj
            ((proetaleModuleInverseImage.{u, max (u + 1) w, w} g (Λ ⧸ I)).obj F₀)))) := by
  let K' := (derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K
  obtain ⟨c⟩ := nonempty_homology_tensor_single_restrictScalars_proetaleModuleInverseImage_iso g I
    K' F₀ i
  exact ((Functor.map_isZero _ h).of_iso c.symm).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso
      (((derivedModuleEquiv.{u, max (u + 1) w, w} Z Λ).unitIso.app _).symm ⊗ᵢ Iso.refl _))

variable (Λ) in
/-- **Restriction along a morphism with essentially surjective inverse image preserves the Tor
amplitude of the reduction.** Let `g : Z ⟶ X` be a morphism of schemes such that every sheaf of
`Λ/I`-modules on `Z_proét` is the inverse image of one on `X_proét` (for instance an open
immersion, or a closed immersion of affine schemes). If `K ⊗_Λ^L \underline{Λ/I}` has Tor
amplitude in `S`, then so has `K|_Z ⊗_Λ^L \underline{Λ/I}`.

Read over `Λ` (`AlgebraicGeometry.ProEtale.hasTorAmplitude_derivedReduction_iff`), the
cohomology of `K|_Z ⊗_Λ^L g⁻¹F₀` is the inverse image of that of `K ⊗_Λ^L F₀`. -/
theorem hasTorAmplitude_derivedReduction_derivedInverseImage (I : Ideal Λ)
    [(proetaleModuleInverseImage.{u, max (u + 1) w, w} g (Λ ⧸ I)).EssSurj]
    {K : DerivedSheaves.{u, max (u + 1) w, w} X Λ} {S : Set ℤ}
    (h : Stacks.ModuleSheaf.HasTorAmplitude (J := Scheme.ProEt.topology X)
      ((derivedReduction.{u, w} X Λ I).obj K) S) :
    Stacks.ModuleSheaf.HasTorAmplitude (J := Scheme.ProEt.topology Z)
      ((derivedReduction.{u, w} Z Λ I).obj ((derivedInverseImage.{u, max (u + 1) w, w} g Λ).obj K))
      S := by
  rw [hasTorAmplitude_derivedReduction_iff] at h ⊢
  intro F i hi
  let gI := proetaleModuleInverseImage.{u, max (u + 1) w, w} g (Λ ⧸ I)
  exact (isZero_homology_tensor_single_restrictScalars_derivedInverseImage g Λ I K
    (gI.objPreimage F) i (h _ i hi)).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
      (Iso.refl _ ⊗ᵢ (DerivedCategory.singleFunctor _ 0).mapIso
        ((Stacks.ModuleSheaf.restrictScalars _ _).mapIso (gI.objObjPreimageIso F).symm)))

variable (Λ) in
/-- **Restriction to a locally closed subscheme preserves the Tor amplitude of the reduction.**
Let `g : Z ⟶ X` be an immersion. If `K ⊗_Λ^L \underline{Λ/I}` has Tor amplitude in `S`, then
so has `K|_Z ⊗_Λ^L \underline{Λ/I}`.

Locally on `Z`, `g` is a closed immersion of affine schemes followed by an open immersion, along
which every sheaf is an inverse image
(`AlgebraicGeometry.ProEtale.exists_isOpenImmersion_cover_essSurj_proetaleModuleInverseImage`);
the cohomology sheaves to be shown zero restrict on such an open `W` to those of `K|_W`, and
vanishing of sheaves is local on `Z`. -/
theorem hasTorAmplitude_derivedReduction_derivedInverseImage_of_isImmersion (I : Ideal Λ)
    [IsImmersion g] {K : DerivedSheaves.{u, max (u + 1) w, w} X Λ} {S : Set ℤ}
    (h : Stacks.ModuleSheaf.HasTorAmplitude (J := Scheme.ProEt.topology X)
      ((derivedReduction.{u, w} X Λ I).obj K) S) :
    Stacks.ModuleSheaf.HasTorAmplitude (J := Scheme.ProEt.topology Z)
      ((derivedReduction.{u, w} Z Λ I).obj ((derivedInverseImage.{u, max (u + 1) w, w} g Λ).obj K))
      S := by
  rw [hasTorAmplitude_derivedReduction_iff] at h ⊢
  intro F i hi
  obtain ⟨ι, W, j, hjo, hj, hess⟩ :=
    exists_isOpenImmersion_cover_essSurj_proetaleModuleInverseImage.{u, max (u + 1) w, w}
      (Λ ⧸ I) g
  refine isZero_of_isZero_proetaleModuleInverseImage Λ j hj _ fun a => ?_
  let L' := (derivedModuleEquiv.{u, max (u + 1) w, w} Z Λ).inverse.obj
    ((derivedInverseImage.{u, max (u + 1) w, w} g Λ).obj K)
  let jI := proetaleModuleInverseImage.{u, max (u + 1) w, w} (j a) (Λ ⧸ I)
  let gI := proetaleModuleInverseImage.{u, max (u + 1) w, w} (j a ≫ g) (Λ ⧸ I)
  let F₀ := gI.objPreimage (jI.obj F)
  obtain ⟨c⟩ := nonempty_homology_tensor_single_restrictScalars_proetaleModuleInverseImage_iso
    (j a) I L' F i
  exact (isZero_homology_tensor_single_restrictScalars_derivedInverseImage (j a ≫ g) Λ I K F₀ i
    (h _ i hi)).of_iso (c ≪≫ (DerivedCategory.homologyFunctor _ i).mapIso
      (((derivedModuleEquiv.{u, max (u + 1) w, w} (W a) Λ).unitIso.app _ ≪≫
        (derivedModuleEquiv.{u, max (u + 1) w, w} (W a) Λ).inverse.mapIso
          ((derivedInverseImageCompIso g Λ (j a)).app K).symm) ⊗ᵢ
      (DerivedCategory.singleFunctor _ 0).mapIso
        ((Stacks.ModuleSheaf.restrictScalars _ _).mapIso (gI.objObjPreimageIso _).symm)))

end AlgebraicGeometry.ProEtale
