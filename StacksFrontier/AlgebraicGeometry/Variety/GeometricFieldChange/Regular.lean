module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.RegularNoetherian
public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.GeometricallyRegular.FieldExtension

/-!
# Characterizations of geometrically regular schemes

For a locally Noetherian scheme over a field, geometric regularity can be tested after all
finitely generated field extensions, or only after the finite purely inseparable ones. It is
equally detected by geometric regularity of the ring of sections on every affine open, or on
the members of a single affine open covering.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.geometricallyRegular_tfae`: the five equivalent characterizations of a
  geometrically regular scheme over a field.

## Implementation notes

The five entries of the `List.TFAE` are the five numbered conditions of the source. A finitely
generated field extension is `Algebra.EssFiniteType`, and an affine open covering is an indexed
family of affine opens whose supremum is the top open. The `k`-algebra structure on the
sections over an affine open is the one induced by the structure morphism.

Passing between regularity of a scheme and regularity of the rings of sections on affine opens
uses the characterization of regularity by the local rings, together with the fact that the
local ring at a point of an affine open is a localization of the ring of sections there.

## References

* [Stacks Project, Tag 038V](https://stacks.math.columbia.edu/tag/038V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The ring of sections of a regular scheme on an affine open is a regular ring. Each of its
localizations at a prime is the local ring of the corresponding point. -/
private lemma isRegularRing_sections_of_isRegular {X : Scheme.{u}} (hX : IsRegular X)
    (U : X.affineOpens) : IsRegularRing Γ(X, U) := by
  obtain ⟨hN, hstalk⟩ := ((isRegular_tfae X).out 1 2).mp hX
  have : IsLocallyNoetherian X := hN
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  rw [isRegularRing_iff]
  intro p hp
  let z : PrimeSpectrum Γ(X, U) := ⟨p, hp⟩
  let x : X := U.2.fromSpec z
  have hx : x ∈ U.val := by
    have hz : z ∈ U.2.fromSpec ⁻¹ᵁ (U : X.Opens) := by
      rw [U.2.fromSpec_preimage_self]; trivial
    exact hz
  let _ := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) p := U.2.isLocalization_stalk' z hx
  have : IsRegularLocalRing (X.presheaf.stalk x) := hstalk x
  exact IsRegularLocalRing.of_ringEquiv
    ((IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (X.presheaf.stalk x)).toRingEquiv).symm

/-- A scheme covered by affine opens whose rings of sections are regular is regular. -/
private lemma isRegular_of_affineOpens_cover {X : Scheme.{u}} {I : Type*}
    (U : I → X.affineOpens) (hU : (⨆ i, (U i).1) = ⊤)
    (hreg : ∀ i, IsRegularRing Γ(X, (U i).1)) : IsRegular X := by
  intro x
  have hx : x ∈ (⨆ i, (U i).1 : X.Opens) := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨U i, hi, hreg i⟩




private theorem regularRing_tensorProduct_of_regularBaseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (U : X.affineOpens)
    [Algebra k Γ(X, U.1)]
    (hfi : Spec.map (ofHom (algebraMap k Γ(X, U.1))) = U.2.fromSpec ≫ f)
    (hY : IsRegular
      (pullback f (Spec.map (ofHom (algebraMap k K))))) :
    IsRegularRing (K ⊗[k] Γ(X, U.1)) := by
  let A := Γ(X, U.1)
  let g := Spec.map (ofHom (algebraMap k K))
  let fi : Spec (.of A) ⟶ Spec (.of k) :=
    Spec.map (ofHom (algebraMap k A))
  have hφ : fi = U.2.fromSpec ≫ f := hfi
  let Z := pullback fi g
  let e₁ : fi ≫ 𝟙 (Spec (.of k)) = U.2.fromSpec ≫ f := by
    rw [hφ]
    simp
  let j := pullback.map fi g f g U.2.fromSpec (𝟙 _) (𝟙 _) e₁ (by simp)
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let : Mono (𝟙 (Spec (.of k))) := inferInstance
  let : IsOpenImmersion j := by
    dsimp [j]
    infer_instance
  have hRange : IsAffineOpen j.opensRange := isAffineOpen_opensRange j
  let V : (pullback f g).affineOpens := ⟨j.opensRange, hRange⟩
  have hΓ : IsRegularRing Γ(pullback f g, V.1) :=
    isRegularRing_sections_of_isRegular hY V
  let : IsRegularRing Γ(pullback f g, V.1) := hΓ
  have hZ : IsRegularRing Γ(Z, ⊤) :=
    IsRegularRing.of_ringEquiv
      (IsOpenImmersion.ΓIsoTop j).commRingCatIsoToRingEquiv.symm
  let : IsRegularRing Γ(Z, ⊤) := hZ
  let eSpec : Γ(Z, ⊤) ≃+* (A ⊗[k] K) :=
    (Scheme.Γ.mapIso (pullbackSpecIso k A K).symm.op).commRingCatIsoToRingEquiv.trans
      ((Scheme.ΓSpecIso (CommRingCat.of (A ⊗[k] K))).commRingCatIsoToRingEquiv)
  have hTensor : IsRegularRing (A ⊗[k] K) :=
    IsRegularRing.of_ringEquiv eSpec
  let : IsRegularRing (A ⊗[k] K) := hTensor
  exact IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm k K A).toRingEquiv.symm

private theorem regularRing_sections_openRange_of_regularTensor
    (k K A : Type u) [Field k] [Field K] [CommRing A] [Algebra k K] [Algebra k A]
    (Y Z : Scheme.{u}) (j : Z ⟶ Y) [IsOpenImmersion j]
    (e : Z ≅ Spec (.of (A ⊗[k] K)))
    (hK : IsRegularRing (K ⊗[k] A)) :
    IsRegularRing Γ(Y, j.opensRange) := by
  let eΓ : Γ(Z, ⊤) ≃+* (K ⊗[k] A) :=
    (Scheme.Γ.mapIso e.symm.op).commRingCatIsoToRingEquiv.trans
      ((Scheme.ΓSpecIso (CommRingCat.of (A ⊗[k] K))).commRingCatIsoToRingEquiv.trans
        (Algebra.TensorProduct.comm k K A).toRingEquiv.symm)
  let : IsRegularRing (K ⊗[k] A) := hK
  have hZ : IsRegularRing Γ(Z, ⊤) := IsRegularRing.of_ringEquiv eΓ.symm
  let : IsRegularRing Γ(Z, ⊤) := hZ
  exact IsRegularRing.of_ringEquiv
    (IsOpenImmersion.ΓIsoTop j).commRingCatIsoToRingEquiv

/-- The structure morphism of the sections of `X` over an affine open `U` is the restriction of
`f` along `U.fromSpec`. -/
private theorem specMap_algebraMap_sections_eq_fromSpec_comp {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (U : X.affineOpens) :
    letI : Algebra k Γ(X, U.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    Spec.map (ofHom (algebraMap k Γ(X, U.1))) = U.2.fromSpec ≫ f := by
  have hs := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) U.2 (by simp)
  calc
    _ = Spec.map (f.appLE ⊤ U.1 (by simp)) ≫
        (isAffineOpen_top (Spec (.of k))).fromSpec := by
      rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
      congr 1
    _ = _ := hs

/-- **Stacks Project, Tag 038V.** The five standard characterizations of geometric regularity
for a locally Noetherian scheme over a field are equivalent. -/
@[stacks 038V]
theorem geometricallyRegular_tfae
    (k : Type u) [Field k] (X : Scheme.{u}) [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of k)) :
    let geometricallyRegularSections := fun U : X.Opens ↦
      letI : Algebra k Γ(X, U) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra
      Algebra.IsGeometricallyRegular k Γ(X, U)
    List.TFAE
      [ IsGeometricallyRegular f,
        ∀ (k' : Type u) [Field k'] [Algebra k k'] [Algebra.EssFiniteType k k'],
          IsRegular
            (pullback f (Spec.map (ofHom (algebraMap k k')))),
        ∀ (k' : Type u) [Field k'] [Algebra k k'] [Module.Finite k k']
          [IsPurelyInseparable k k'],
          IsRegular
            (pullback f (Spec.map (ofHom (algebraMap k k')))),
        ∀ U : X.affineOpens, geometricallyRegularSections U.1,
        ∃ (I : Type u) (U : I → X.affineOpens),
          (⨆ i, (U i).1) = ⊤ ∧ ∀ i, geometricallyRegularSections (U i).1 ] := by
  classical
  tfae_have 1 → 2 := by
    intro h K _ _ _
    let g := Spec.map (ofHom (algebraMap k K))
    let Y := pullback f g
    let : IsLocallyNoetherian Y :=
      (isLocallyNoetherian_baseChange_iff k K X f).mp inferInstance
    show IsRegular Y
    apply ((isRegular_tfae Y).out 2 1).mp
    refine ⟨inferInstance, fun z => ?_⟩
    exact h (pullback.fst f g z) K z rfl
  tfae_have 2 → 3 := by
    intro h K _ _ hfin hpi
    exact h K
  tfae_have 3 → 4 := by
    intro h U
    let : Algebra k Γ(X, U.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    show Algebra.IsGeometricallyRegular k Γ(X, U.1)
    refine ⟨?_⟩
    intro K _ _ hess
    apply (Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
      k Γ(X, U.1)).2 ?_ K
    intro K' _ _ hfin hpi
    have hfi := specMap_algebraMap_sections_eq_fromSpec_comp f U
    exact regularRing_tensorProduct_of_regularBaseChange k K' X f U hfi (h K')
  tfae_have 4 → 5 := by
    intro h
    exact ⟨X.affineOpens, id, iSup_affineOpens_eq_top X, h⟩
  tfae_have 5 → 1 := by
    intro h x K _ _ hess _ y hy
    rcases h with ⟨I, U, hcover, hgeo⟩
    let g := Spec.map (ofHom (algebraMap k K))
    let Y := pullback f g
    let 𝒜 : X.AffineOpenCover :=
      Scheme.AffineOpenCover.ofIsOpenCover (X := X) (fun i => (U i).1) hcover
        (fun i => (U i).2)
    let 𝒰 : X.OpenCover := 𝒜.openCover
    let 𝒱 : Y.OpenCover := Scheme.Pullback.openCoverOfLeft 𝒰 f g
    have hAff : ∀ i, IsAffine (𝒱.X i) := by
      intro i
      let : IsAffine (𝒰.X i) := Scheme.isAffine_affineOpenCover X 𝒜 i
      let : IsAffineHom (𝒰.f i ≫ f) := isAffineHom_of_isAffine _
      let : IsAffineHom g := inferInstance
      show IsAffine (pullback (𝒰.f i ≫ f) g)
      exact Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine _ _
    let V : 𝒱.I₀ → Y.affineOpens := fun i =>
      ⟨(𝒱.f i).opensRange, by
        let : IsAffine (𝒱.X i) := hAff i
        exact isAffineOpen_opensRange (𝒱.f i)⟩
    have hVcover : (⨆ i, (V i).1) = ⊤ := by
      simpa [V] using 𝒱.iSup_opensRange
    have hVreg : ∀ i, IsRegularRing Γ(Y, V i) := by
      intro i
      let Ui : X.affineOpens := U i
      let A := Γ(X, Ui.1)
      let : Algebra k A :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ Ui.1 (by simp)).hom.toAlgebra
      let j : 𝒱.X i ⟶ Y := 𝒱.f i
      let : IsOpenImmersion j := 𝒱.map_prop i
      have hfi := specMap_algebraMap_sections_eq_fromSpec_comp f Ui
      have hfi' : Spec.map (ofHom (algebraMap k A)) = 𝒰.f i ≫ f := by
        show Spec.map (ofHom (algebraMap k A)) = Ui.2.fromSpec ≫ f
        exact hfi
      have e : 𝒱.X i ≅ Spec (.of (A ⊗[k] K)) := by
        show pullback (𝒰.f i ≫ f) g ≅ _
        exact (pullback.congrHom hfi' rfl).symm ≪≫ pullbackSpecIso k A K
      let : Algebra.IsGeometricallyRegular k A := hgeo i
      have hK : IsRegularRing (K ⊗[k] A) := inferInstance
      have hΓ := regularRing_sections_openRange_of_regularTensor k K A Y
        (𝒱.X i) j e hK
      simpa [V, j, Y] using hΓ
    have hYreg : IsRegular Y := isRegular_of_affineOpens_cover V hVcover hVreg
    have hstalks : IsLocallyNoetherian Y ∧
        ∀ y' : Y, IsRegularLocalRing (Y.presheaf.stalk y') :=
      ((isRegular_tfae Y).out 1 2).mp hYreg
    exact hstalks.2 y
  tfae_finish

end AlgebraicGeometry

end
