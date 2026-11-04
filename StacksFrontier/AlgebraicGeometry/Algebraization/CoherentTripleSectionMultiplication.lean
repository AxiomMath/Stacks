module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPullbackMultiplication
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerSectionMultiplication
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistHom

/-!
# Multiplying the twists of a coherent triple by a global section

This file defines multiplication by a global section on the integral tensor powers of an
invertible module on a scheme, and proves that the inverse-image comparison of tensor powers, the
comparison of the tensor powers of two isomorphic invertible modules, and hence the
identification `Stacks.Algebraization.IsInvertibleTriple.alphaPow` of an invertible coherent
triple, carry it to multiplication by the corresponding section. This gives multiplication by a
global section of an invertible coherent triple as a morphism from the `n`-th twist of a coherent
triple to its `(n + 1)`-st, for every integer `n`.

## Main definitions

* `Stacks.Algebraization.mulSectionPowScheme`: multiplication by a global section of an
  invertible `𝒪_X`-module, from its `n`-th tensor power to its `(n + 1)`-st.
* `Stacks.Algebraization.CoherentTriple.mulSectionTwistZ`: multiplication by a global section
  of an invertible coherent triple, as a morphism from the `n`-th twist of a coherent triple to
  its `(n + 1)`-st.

## Main results

* `Stacks.Algebraization.pullbackTensorPowSchemeIso_eq_pullbackIntPowIso`: the comparison of
  tensor powers used by the coherent triples is the ringed-space one.
* `Stacks.Algebraization.pullbackTensorPowSchemeIso_mulSectionPowScheme`: the inverse-image
  comparison of the tensor powers carries multiplication by a section to multiplication by the
  inverse image of that section.
* `Stacks.Algebraization.tensorPowSchemeCongr_mulSectionPowScheme` and
  `Stacks.Algebraization.tensorPowSchemeCongr_mulSectionPowScheme_of_eq`: the same for the
  comparison of the tensor powers of two isomorphic invertible modules, the second with the
  section of the second module given independently.
* `Stacks.Algebraization.alphaPow_mulSectionPowScheme`: the identification of an invertible
  coherent triple in degree `n` carries multiplication by a section of the punctured-spectrum
  member to multiplication by the corresponding section of the closed-fibre member.
* `Stacks.Algebraization.compatible_tensorModuleRight`: the compatibility square of a morphism
  tensored into the second slot.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing MonoidalCategory
open Stacks.RelativeVeryAmple

universe u

namespace Stacks.Algebraization

/-! ### Multiplication by a global section on a scheme -/

/-- An invertible `𝒪_X`-module in the sense of `Stacks.Ample.IsInvertibleModule` is invertible in
the sense of `Stacks.SheafOfModules.IsInvertible`. -/
public theorem isInvertible_of_isInvertibleModule (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] :
    Stacks.SheafOfModules.IsInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).2 ‹_›

/-- Multiplication by a global section `σ : 𝒪_X ⟶ L` of an invertible `𝒪_X`-module `L`, from
the `n`-th integral tensor power of `L` to the `(n + 1)`-st. -/
public def mulSectionPowScheme (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (σ : Stacks.Ample.unitModule X ⟶ L) (n : ℤ) :
    tensorPowScheme X L n ⟶ tensorPowScheme X L (n + 1) :=
  letI := isInvertible_of_isInvertibleModule X L
  Stacks.SheafOfModules.TensorPower.mulSectionPow X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L σ n

/-! ### The inverse-image comparison -/

/-- The comparison of the integral tensor powers used by the coherent triples is the
ringed-space comparison of [Stacks, Tag 01CD] in every degree. -/
public theorem pullbackTensorPowSchemeIso_eq_pullbackIntPowIso {X S : Scheme.{u}} (g : X ⟶ S)
    (L : S.Modules) [Stacks.Ample.IsInvertibleModule S L]
    [Stacks.Ample.IsInvertibleModule X ((Scheme.Modules.pullback g).obj L)] (n : ℤ) :
    pullbackTensorPowSchemeIso g L n =
      Stacks.TensorPowerPullback.pullbackIntPowIso g.toLRSHom.toShHom L n := by
  unfold pullbackTensorPowSchemeIso Stacks.TensorPowerPullback.pullbackIntPowIso
  congr 1
  exact funext fun _ => Iso.ext rfl

/-- The inverse-image comparison of the integral tensor powers carries multiplication by a
global section to multiplication by the inverse image of that section. -/
@[reassoc]
public theorem pullbackTensorPowSchemeIso_mulSectionPowScheme {X S : Scheme.{u}} (g : X ⟶ S)
    (L : S.Modules) [Stacks.Ample.IsInvertibleModule S L]
    [Stacks.Ample.IsInvertibleModule X ((Scheme.Modules.pullback g).obj L)]
    (σ : Stacks.Ample.unitModule S ⟶ L) (n : ℤ) :
    (Scheme.Modules.pullback g).map (mulSectionPowScheme S L σ n) ≫
        (pullbackTensorPowSchemeIso g L (n + 1)).hom =
      (pullbackTensorPowSchemeIso g L n).hom ≫
        mulSectionPowScheme X ((Scheme.Modules.pullback g).obj L)
          ((Scheme.Modules.pullbackUnitIso g).inv ≫ (Scheme.Modules.pullback g).map σ) n := by
  let := isInvertible_of_isInvertibleModule S L
  let := isInvertible_of_isInvertibleModule X ((Scheme.Modules.pullback g).obj L)
  rw [pullbackTensorPowSchemeIso_eq_pullbackIntPowIso,
    pullbackTensorPowSchemeIso_eq_pullbackIntPowIso]
  exact Stacks.SheafOfModules.TensorPower.map_mulSectionPow_tensorPowerComparison
    S.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf S)
    X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)
    (Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom) L
    (Stacks.TensorPowerPullback.pullbackTensorator g.toLRSHom.toShHom)
    (Stacks.TensorPowerPullback.pullbackUnitSheafIso g.toLRSHom.toShHom)
    (Stacks.TensorPowerPullback.isRightUnital_pullback g.toLRSHom.toShHom)
    (Stacks.TensorPowerPullback.isNaturalRight_pullback g.toLRSHom.toShHom) σ n

/-! ### The comparison of the powers of two isomorphic modules -/

/-- The comparison of the integral tensor powers of two isomorphic invertible modules carries
multiplication by a global section to multiplication by the corresponding section. -/
@[reassoc]
public theorem tensorPowSchemeCongr_mulSectionPowScheme (X : Scheme.{u}) {L L' : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X L'] (e : L ≅ L')
    (σ : Stacks.Ample.unitModule X ⟶ L) (n : ℤ) :
    mulSectionPowScheme X L σ n ≫ (tensorPowSchemeCongr X e (n + 1)).hom =
      (tensorPowSchemeCongr X e n).hom ≫ mulSectionPowScheme X L' (σ ≫ e.hom) n := by
  let := isInvertible_of_isInvertibleModule X L
  let := isInvertible_of_isInvertibleModule X L'
  exact Stacks.SheafOfModules.TensorPower.mulSectionPow_tensorPowerCongr X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L L' e σ n

/-- `Stacks.Algebraization.tensorPowSchemeCongr_mulSectionPowScheme` with the section `σ'` of the
second module given independently, together with an identification `σ ≫ e.hom = σ'`. -/
@[reassoc]
public theorem tensorPowSchemeCongr_mulSectionPowScheme_of_eq (X : Scheme.{u})
    {L L' : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
    [Stacks.Ample.IsInvertibleModule X L'] (e : L ≅ L')
    (σ : Stacks.Ample.unitModule X ⟶ L) (σ' : Stacks.Ample.unitModule X ⟶ L')
    (h : σ ≫ e.hom = σ') (n : ℤ) :
    mulSectionPowScheme X L σ n ≫ (tensorPowSchemeCongr X e (n + 1)).hom =
      (tensorPowSchemeCongr X e n).hom ≫ mulSectionPowScheme X L' σ' n := by
  subst h
  exact tensorPowSchemeCongr_mulSectionPowScheme X e σ n

/-! ### The identification of an invertible coherent triple -/

/-- The identification of an invertible coherent triple in degree `n` carries multiplication by
a global section of the punctured-spectrum member to multiplication by the corresponding global
section of the closed-fibre member, for every integer `n`.

The hypothesis is that the two sections correspond: their inverse images along the two routes
around the square of the triple agree, through the identification of the triple and the two
identifications of the inverse image of a structure sheaf with the structure sheaf, that is,
`(σ, σ₀)` is a morphism of coherent triples from the unit triple to the invertible triple. -/
@[reassoc]
public theorem alphaPow_mulSectionPowScheme {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    {L : CoherentTriple A f} (hL : IsInvertibleTriple L)
    (σ : Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme ⟶ L.F)
    (σ₀ : Stacks.Ample.unitModule (closedFibre A f) ⟶ L.F₀)
    (hcompat :
      ((Scheme.Modules.pullbackUnitIso (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).inv ≫
          (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map σ) ≫ L.alpha.hom =
        (Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map σ₀)
    (n : ℤ) :
    letI := hL.invertible_F
    letI := hL.invertible_F₀
    (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).map
        (mulSectionPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F σ n) ≫
        (hL.alphaPow (n + 1)).hom =
      (hL.alphaPow n).hom ≫
        (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
          (mulSectionPowScheme (closedFibre A f) L.F₀ σ₀ n) := by
  let := hL.invertible_F
  let := hL.invertible_F₀
  have hA := pullbackTensorPowSchemeIso_mulSectionPowScheme
    (morphismRestrict (closedImmersion A f) (Stacks.Divisors.puncturedSpectrum A)) L.F σ n
  have hC := tensorPowSchemeCongr_mulSectionPowScheme_of_eq (puncturedClosedFibre A f).toScheme
    L.alpha ((Scheme.Modules.pullbackUnitIso (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A))).inv ≫
      (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A))).map σ)
    ((Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι).inv ≫
      (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map σ₀)
    hcompat n
  have hB := pullbackTensorPowSchemeIso_mulSectionPowScheme
    (puncturedClosedFibre A f).ι L.F₀ σ₀ n
  have hB' : mulSectionPowScheme (puncturedClosedFibre A f).toScheme
        ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj L.F₀)
        ((Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map σ₀) n ≫
        (pullbackTensorPowSchemeIso (puncturedClosedFibre A f).ι L.F₀ (n + 1)).inv =
      (pullbackTensorPowSchemeIso (puncturedClosedFibre A f).ι L.F₀ n).inv ≫
        (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
          (mulSectionPowScheme (closedFibre A f) L.F₀ σ₀ n) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact hB.symm
  unfold IsInvertibleTriple.alphaPow
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% hA, reassoc_of% hC, hB']

/-! ### Multiplication by a section as a morphism of coherent triples -/

/-- The compatibility square of a morphism tensored into the second slot: the first slot carries
the identity of the members of the triple `T`, and the second a morphism `(m, m₀)` of two pairs of
modules identified over the punctured closed fibre. -/
public theorem compatible_tensorModuleRight {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    (T : CoherentTriple A f)
    {M N : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules}
    {M₀ N₀ : (closedFibre A f).Modules}
    (μ : (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).obj M ≅
      (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj M₀)
    (ν : (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).obj N ≅
      (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj N₀)
    (m : M ⟶ N) (m₀ : M₀ ⟶ N₀)
    (hm : (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).map m ≫ ν.hom =
      μ.hom ≫ (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map m₀) :
    (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map
          (tensorModulesMap (Stacks.Divisors.puncturedSpectrum A).toScheme (𝟙 T.F) m) ≫
        (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A)) T.F N).hom ≫
          tensorModulesMap (puncturedClosedFibre A f).toScheme T.alpha.hom ν.hom ≫
          (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀ N₀).inv =
      (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A)) T.F M).hom ≫
        tensorModulesMap (puncturedClosedFibre A f).toScheme T.alpha.hom μ.hom ≫
        (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀ M₀).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
            (tensorModulesMap (closedFibre A f) (𝟙 T.F₀) m₀) := by
  have hnatk := pullbackTensorModulesIso_naturality (morphismRestrict (closedImmersion A f)
    (Stacks.Divisors.puncturedSpectrum A)) (𝟙 T.F) m
  have hnatj := pullbackTensorModulesIso_naturality (puncturedClosedFibre A f).ι (𝟙 T.F₀) m₀
  rw [CategoryTheory.Functor.map_id] at hnatk hnatj
  have key : tensorModulesMap (puncturedClosedFibre A f).toScheme (𝟙 _)
        ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).map m) ≫
      tensorModulesMap (puncturedClosedFibre A f).toScheme T.alpha.hom ν.hom =
      tensorModulesMap (puncturedClosedFibre A f).toScheme T.alpha.hom μ.hom ≫
        tensorModulesMap (puncturedClosedFibre A f).toScheme (𝟙 _)
          ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map m₀) := by
    rw [tensorModulesMap_comp, tensorModulesMap_comp, Category.id_comp, Category.comp_id, hm]
  have hnatj' : tensorModulesMap (puncturedClosedFibre A f).toScheme (𝟙 _)
        ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map m₀) ≫
      (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀ N₀).inv =
      (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀ M₀).inv ≫
        (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
          (tensorModulesMap (closedFibre A f) (𝟙 T.F₀) m₀) :=
    (Iso.comp_inv_eq _).2
      ((((Category.assoc _ _ _).trans
        (congrArg (fun t => (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀ M₀).inv ≫ t)
          hnatj)).trans (Iso.inv_hom_id_assoc _ _)).symm)
  exact comp_eq_of_three_squares _ _ _ _ _ _ _ _ _ _ hnatk key hnatj'

/-- Multiplication by a global section of an invertible coherent triple, as a morphism from the
`n`-th twist of a coherent triple to its `(n + 1)`-st, for every integer `n`.

The datum is a global section of each member of the invertible triple, the two corresponding
over the punctured closed fibre, that is, a morphism of coherent triples from the unit triple to
the invertible triple. -/
public def CoherentTriple.mulSectionTwistZ {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    (T L : CoherentTriple A f) (hL : IsInvertibleTriple L)
    (σ : Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme ⟶ L.F)
    (σ₀ : Stacks.Ample.unitModule (closedFibre A f) ⟶ L.F₀)
    (hcompat :
      ((Scheme.Modules.pullbackUnitIso (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).inv ≫
          (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map σ) ≫ L.alpha.hom =
        (Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map σ₀)
    (n : ℤ) : (T.twistZ L hL n).Hom (T.twistZ L hL (n + 1)) :=
  letI := hL.invertible_F
  letI := hL.invertible_F₀
  { onPunctured := tensorModulesMap (Stacks.Divisors.puncturedSpectrum A).toScheme (𝟙 T.F)
      (mulSectionPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F σ n)
    onClosedFibre := tensorModulesMap (closedFibre A f) (𝟙 T.F₀)
      (mulSectionPowScheme (closedFibre A f) L.F₀ σ₀ n)
    compatible := compatible_tensorModuleRight T (hL.alphaPow n) (hL.alphaPow (n + 1)) _ _
      (alphaPow_mulSectionPowScheme hL σ σ₀ hcompat n) }

end Stacks.Algebraization

end
