module

public import Mathlib.Algebra.Homology.SpectralObject.FirstPage
import all Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# The spectral sequence of a spectral object is functorial

For a spectral object `X` in an abelian category `C` indexed by a preorder `ι` and
`data : CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore ι c r₀`, Mathlib
constructs the spectral sequence `X.spectralSequence data`. This file shows that it is
functorial in `X`: it constructs the functor
```
CategoryTheory.Abelian.SpectralObject C ι ⥤ CategoryTheory.SpectralSequence C c r₀
```
and its `E₂`-cohomological specialisation for spectral objects indexed by `EInt`. On the
objects `X.E f₁ f₂ f₃ n₀ n₁ n₂` from which the pages are built, a morphism of spectral objects
induces the map `CategoryTheory.Abelian.SpectralObject.EMap`, which commutes with the
functoriality of `E` in `ComposableArrows ι 3` and with the differentials.

## Main definitions

* `CategoryTheory.Abelian.SpectralObject.EMap`: functoriality of `E` in the spectral object.
* `CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageMap`: the induced morphism of
  `r`-th pages.
* `CategoryTheory.Abelian.SpectralObject.spectralSequenceMap`: the induced morphism of spectral
  sequences.
* `CategoryTheory.Abelian.SpectralObject.spectralSequenceFunctor`: the functor
  `SpectralObject C ι ⥤ SpectralSequence C c r₀`.
* `CategoryTheory.Abelian.SpectralObject.E₂SpectralSequenceFunctor`: its specialisation to
  spectral objects indexed by `EInt` and `coreE₂Cohomological`, a functor
  `SpectralObject C EInt ⥤ E₂CohomologicalSpectralSequence C`.

## Main results

* `CategoryTheory.Abelian.SpectralObject.map_EMap` and
  `CategoryTheory.Abelian.SpectralObject.d_EMap`: `EMap` commutes with the functoriality of `E`
  in `ComposableArrows ι 3` and with the differentials.
* `CategoryTheory.Abelian.SpectralObject.spectralSequenceFirstPageXIso_hom_naturality` and
  `CategoryTheory.Abelian.SpectralObject.spectralSequenceFirstPageXNatIso`: the identification
  of the objects of the starting page with objects `X.H n` is natural in the spectral object,
  as a natural isomorphism of functors on `SpectralObject C ι`.

## Implementation notes

* `import all` of `Mathlib.Algebra.Homology.SpectralObject.SpectralSequence` is needed because
  `CategoryTheory.Abelian.SpectralObject.SpectralSequence.homologyData` has private auxiliary
  proofs in its arguments, so a declaration of this module that mentions it does not typecheck
  against the public interface alone.
* `unseal spectralSequence` is used where the `@[irreducible]` definition
  `CategoryTheory.Abelian.SpectralObject.spectralSequence` must be unfolded to see its pages as
  `SpectralSequence.page`; Mathlib's own file does the same for `spectralSequencePageXIso` and
  `spectralSequence_page_d_eq`.
* Nothing here is specific to this development: this is material for
  `Mathlib/Algebra/Homology/SpectralObject/`.

## References

* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4]
-/

@[expose] public section

namespace HomologicalComplex

open CategoryTheory Limits

variable {C : Type*} [Category* C] [Abelian C]
  {ιc : Type*} {cc : ComplexShape ιc} {K L : HomologicalComplex C cc}

/-- **`HomologicalComplex.homologyIsoSc'` is natural in the complex.**  The isomorphism
`K.homology j ≅ (K.sc' i j k).homology` commutes with the maps induced by a morphism
`ψ : K ⟶ L` of complexes. -/
@[reassoc]
lemma homologyMap_homologyIsoSc'_hom (ψ : K ⟶ L) (i j k : ιc)
    (hi : cc.prev j = i) (hk : cc.next j = k) :
    homologyMap ψ j ≫ (L.homologyIsoSc' i j k hi hk).hom =
      (K.homologyIsoSc' i j k hi hk).hom ≫
        ShortComplex.homologyMap ((shortComplexFunctor' C cc i j k).map ψ) :=
  Eq.trans (ShortComplex.homologyMap_comp _ _).symm
    (Eq.trans (congrArg (fun α ↦ ShortComplex.homologyMap α)
      ((natIsoSc' C cc i j k hi hk).hom.naturality ψ)) (ShortComplex.homologyMap_comp _ _))

end HomologicalComplex

namespace CategoryTheory

open Category Limits ComposableArrows

namespace Abelian

namespace SpectralObject

variable {C : Type*} [Category* C] [Abelian C]

section EFunctoriality

variable {ι : Type*} [Category* ι] {X Y Z : SpectralObject C ι}

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l) (n₀ n₁ n₂ : ℤ)

/-- **Functoriality of `E` in the spectral object.**  A morphism `φ : X ⟶ Y` of spectral
objects induces `X.E f₁ f₂ f₃ n₀ n₁ n₂ ⟶ Y.E f₁ f₂ f₃ n₀ n₁ n₂`.

It is the map induced, through the universal property of `X.E` as a cokernel
(`CategoryTheory.Abelian.SpectralObject.descE`), by `(φ.hom n₁).app (mk₁ (f₁ ≫ f₂))` followed
by the projection of `Y`. -/
noncomputable def EMap (φ : X ⟶ Y)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶ Y.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  X.descE f₁ f₂ f₃ (f₁ ≫ f₂) rfl n₀ n₁ n₂
    ((φ.hom n₁).app (mk₁ (f₁ ≫ f₂)) ≫
      Y.toCycles f₁ f₂ (f₁ ≫ f₂) rfl n₁ ≫ Y.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)
    (by
      rw [← Category.assoc, (φ.hom n₁).naturality]
      simp)
    hn₁
    (by
      rw [← Category.assoc, φ.comm n₀ n₁ hn₁ (f₁ ≫ f₂) f₃]
      simp)
    hn₂

/-- **The equation characterising `EMap`.**  Precomposed with the epimorphism
`toCycles ≫ πE : H^{n₁}(f₁₂) ⟶ E^{n₁}(f₁, f₂, f₃)`, the map `EMap φ` is `(φ.hom n₁)`. -/
@[reassoc]
lemma toCycles_πE_EMap (φ : X ⟶ Y) (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
      EMap f₁ f₂ f₃ n₀ n₁ n₂ φ hn₁ hn₂ =
      (φ.hom n₁).app (mk₁ f₁₂) ≫ Y.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫
        Y.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  subst h₁₂
  exact X.toCycles_πE_descE f₁ f₂ f₃ (f₁ ≫ f₂) rfl n₀ n₁ n₂ _ _ hn₁ _ hn₂

/-- Two maps out of `X.E f₁ f₂ f₃` agree if they agree after `toCycles ≫ πE`. -/
private lemma E_hom_ext_of_toCycles_πE {T : C} (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
    {X : SpectralObject C ι} {u v : X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶ T}
    (h : X.toCycles f₁ f₂ _ rfl n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ u =
      X.toCycles f₁ f₂ _ rfl n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ v) : u = v :=
  (cancel_epi (X.toCycles f₁ f₂ _ rfl n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)).1 (by simpa using h)

/-- `EMap` sends the identity to the identity. -/
@[simp]
lemma EMap_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    EMap f₁ f₂ f₃ n₀ n₁ n₂ (𝟙 X) hn₁ hn₂ = 𝟙 _ := by
  refine E_hom_ext_of_toCycles_πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ?_
  rw [toCycles_πE_EMap f₁ f₂ f₃ n₀ n₁ n₂ (𝟙 X) _ rfl hn₁ hn₂]
  simp

/-- `EMap` is compatible with composition. -/
@[reassoc (attr := simp)]
lemma EMap_comp (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    EMap f₁ f₂ f₃ n₀ n₁ n₂ (φ ≫ ψ) hn₁ hn₂ =
      EMap f₁ f₂ f₃ n₀ n₁ n₂ φ hn₁ hn₂ ≫ EMap f₁ f₂ f₃ n₀ n₁ n₂ ψ hn₁ hn₂ := by
  refine E_hom_ext_of_toCycles_πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ?_
  rw [toCycles_πE_EMap f₁ f₂ f₃ n₀ n₁ n₂ (φ ≫ ψ) _ rfl hn₁ hn₂,
    toCycles_πE_EMap_assoc f₁ f₂ f₃ n₀ n₁ n₂ φ _ rfl hn₁ hn₂,
    toCycles_πE_EMap f₁ f₂ f₃ n₀ n₁ n₂ ψ _ rfl hn₁ hn₂]
  simp

end

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  {i' j' k' l' : ι} (f₁' : i' ⟶ j') (f₂' : j' ⟶ k') (f₃' : k' ⟶ l')
  (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃') (n₀ n₁ n₂ : ℤ)

/-- **`EMap` commutes with the functoriality of `E` in `ComposableArrows ι 3`.** -/
@[reassoc]
lemma map_EMap (φ : X ⟶ Y)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ ≫ EMap f₁' f₂' f₃' n₀ n₁ n₂ φ hn₁ hn₂ =
      EMap f₁ f₂ f₃ n₀ n₁ n₂ φ hn₁ hn₂ ≫ Y.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ := by
  have hfg : (f₁ ≫ f₂) ≫ α.app 2 = α.app 0 ≫ (f₁' ≫ f₂') :=
    naturality' α 0 2 (by lia) (by lia)
  set β : mk₂ f₁ f₂ ⟶ mk₂ f₁' f₂' :=
    homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1 (by lia) (by lia))
      (naturality' α 1 2 (by lia) (by lia)) with hβ
  set γ : mk₁ (f₁ ≫ f₂) ⟶ mk₁ (f₁' ≫ f₂') := homMk₁ (α.app 0) (α.app 2) hfg with hγ
  refine E_hom_ext_of_toCycles_πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ?_
  rw [X.πE_map_assoc f₁ f₂ f₃ f₁' f₂' f₃' α β n₀ n₁ n₂ hβ hn₁ hn₂,
    X.toCycles_cyclesMap_assoc (fg := f₁ ≫ f₂) (h := rfl) (fg' := f₁' ≫ f₂') (h' := rfl)
      f₁ f₂ f₁' f₂' β γ n₁ (by simp [hβ, hγ]) (by simp [hβ, hγ]),
    toCycles_πE_EMap f₁' f₂' f₃' n₀ n₁ n₂ φ _ rfl hn₁ hn₂,
    toCycles_πE_EMap_assoc f₁ f₂ f₃ n₀ n₁ n₂ φ _ rfl hn₁ hn₂,
    Y.πE_map f₁ f₂ f₃ f₁' f₂' f₃' α β n₀ n₁ n₂ hβ hn₁ hn₂,
    Y.toCycles_cyclesMap_assoc (fg := f₁ ≫ f₂) (h := rfl) (fg' := f₁' ≫ f₂') (h' := rfl)
      f₁ f₂ f₁' f₂' β γ n₁ (by simp [hβ, hγ]) (by simp [hβ, hγ]),
    (φ.hom n₁).naturality_assoc γ]

end

section

variable {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (n₀ n₁ n₂ n₃ : ℤ)

/-- **`EMap` commutes with the differentials of a spectral object.** -/
@[reassoc]
lemma d_EMap (φ : X ⟶ Y)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫ EMap f₁ f₂ f₃ n₁ n₂ n₃ φ hn₂ hn₃ =
      EMap f₃ f₄ f₅ n₀ n₁ n₂ φ hn₁ hn₂ ≫ Y.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ := by
  refine E_hom_ext_of_toCycles_πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂ ?_
  rw [X.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ _ rfl _ rfl n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃,
    toCycles_πE_EMap f₁ f₂ f₃ n₁ n₂ n₃ φ _ rfl hn₂ hn₃,
    φ.comm_assoc n₁ n₂ hn₂ (f₁ ≫ f₂) (f₃ ≫ f₄),
    toCycles_πE_EMap_assoc f₃ f₄ f₅ n₀ n₁ n₂ φ _ rfl hn₁ hn₂,
    Y.toCycles_πE_d f₁ f₂ f₃ f₄ f₅ _ rfl _ rfl n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃]

end

section

variable {i j : ι} (f : i ⟶ j) (n₀ n₁ n₂ : ℤ)

/-- **`EMap` is compatible with the identification `E^{n₁}(𝟙, f, 𝟙) ≅ H^{n₁}(f)`.** -/
@[reassoc]
lemma EMap_EIsoH_hom (φ : X ⟶ Y)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    EMap (𝟙 i) f (𝟙 j) n₀ n₁ n₂ φ hn₁ hn₂ ≫ (Y.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom =
      (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom ≫ (φ.hom n₁).app (mk₁ f) := by
  rw [← cancel_epi (X.toCycles (𝟙 i) f f (by simp) n₁ ≫ X.πE (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂),
    Category.assoc, Category.assoc,
    toCycles_πE_EMap_assoc (𝟙 i) f (𝟙 j) n₀ n₁ n₂ φ f (by simp) hn₁ hn₂,
    Y.πE_EIsoH_hom f n₀ n₁ n₂ hn₁ hn₂, Y.cyclesIsoH_inv_hom_id f n₁ n₂ hn₂,
    X.πE_EIsoH_hom_assoc f n₀ n₁ n₂ hn₁ hn₂, X.cyclesIsoH_inv_hom_id_assoc f n₁ n₂ hn₂]
  simp

end

section HObj

variable {ι : Type*} [Category* ι]

/-- **Evaluating `H^n` at a fixed arrow is a functor in the spectral object.** -/
@[simps]
noncomputable def HObjFunctor (n : ℤ) (D : ComposableArrows ι 1) :
    SpectralObject C ι ⥤ C where
  obj X := (X.H n).obj D
  map φ := (φ.hom n).app D

end HObj

end EFunctoriality

namespace SpectralSequence

variable {ι κ : Type*} [Preorder ι] {X Y Z : SpectralObject C ι}
  {c : ℤ → ComplexShape κ} {r₀ : ℤ} (data : SpectralSequenceDataCore ι c r₀)

/-- **The map induced on the object of the `r`-th page in position `pq`.**  It is `EMap` at the
four indices `data` assigns to `(r, pq)`. -/
noncomputable def pageXMap (φ : X ⟶ Y) (r : ℤ) (pq : κ) (hr : r₀ ≤ r) :
    pageX X data r pq hr ⟶ pageX Y data r pq hr :=
  EMap (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq))
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) φ (by lia) (by lia)

/-- **`pageXMap` is `EMap` across the reindexing isomorphism `pageXIso`.** -/
@[reassoc]
lemma pageXIso_hom_EMap (φ : X ⟶ Y) (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    {i₀ i₁ i₂ i₃ : ι} (le₀₁ : i₀ ≤ i₁) (le₁₂ : i₁ ≤ i₂) (le₂₃ : i₂ ≤ i₃)
    (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq)
    (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (pageXIso X data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).hom ≫
      EMap (homOfLE le₀₁) (homOfLE le₁₂) (homOfLE le₂₃) n₀ n₁ n₂ φ hn₁ hn₂ =
      pageXMap data φ r pq hr ≫
        (pageXIso Y data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).hom := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  subst h hn₂ h₀ h₁ h₂ h₃
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The inverse form of `pageXIso_hom_EMap`. -/
@[reassoc]
lemma EMap_pageXIso_inv (φ : X ⟶ Y) (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    {i₀ i₁ i₂ i₃ : ι} (le₀₁ : i₀ ≤ i₁) (le₁₂ : i₁ ≤ i₂) (le₂₃ : i₂ ≤ i₃)
    (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq)
    (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    EMap (homOfLE le₀₁) (homOfLE le₁₂) (homOfLE le₂₃) n₀ n₁ n₂ φ hn₁ hn₂ ≫
      (pageXIso Y data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).inv =
      (pageXIso X data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).inv ≫
        pageXMap data φ r pq hr := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  subst h hn₂ h₀ h₁ h₂ h₃
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **The morphism of `r`-th pages induced by a morphism of spectral objects.** -/
noncomputable def pageMap (φ : X ⟶ Y) (r : ℤ) (hr : r₀ ≤ r) :
    page X data r hr ⟶ page Y data r hr where
  f pq := pageXMap data φ r pq hr
  comm' pq pq' hpq := by
    change pageXMap data φ r pq hr ≫ pageD Y data r pq pq' hr =
      pageD X data r pq pq' hr ≫ pageXMap data φ r pq' hr
    rw [pageD_eq X data r hr pq pq' hpq
        (homOfLE (data.le₀₁ r pq')) (homOfLE (data.le₁₂' pq' rfl (data.hc₀₂ r pq pq' hpq)))
        (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq))
        rfl rfl rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)
        (data.deg pq + 2) rfl,
      pageD_eq Y data r hr pq pq' hpq
        (homOfLE (data.le₀₁ r pq')) (homOfLE (data.le₁₂' pq' rfl (data.hc₀₂ r pq pq' hpq)))
        (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq))
        rfl rfl rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)
        (data.deg pq + 2) rfl,
      Category.assoc, Category.assoc,
      ← EMap_pageXIso_inv data φ r hr pq' (data.le₀₁ r pq')
        (data.le₁₂' pq' rfl (data.hc₀₂ r pq pq' hpq)) (data.le₀₁ r pq)
        _ _ _ _ _ _ _ _ _ _,
      d_EMap_assoc _ _ _ _ _ (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)
        (data.deg pq + 2) φ,
      pageXIso_hom_EMap_assoc data φ r hr pq _ _ _ _ _ _ _
        (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) _ (by lia) (by lia)]

/-- `pageMap` sends the identity to the identity. -/
@[simp]
lemma pageMap_id (r : ℤ) (hr : r₀ ≤ r) : pageMap data (𝟙 X) r hr = 𝟙 _ := by
  ext pq
  exact EMap_id ..

/-- `pageMap` is compatible with composition. -/
@[reassoc (attr := simp)]
lemma pageMap_comp (φ : X ⟶ Y) (ψ : Y ⟶ Z) (r : ℤ) (hr : r₀ ≤ r) :
    pageMap data (φ ≫ ψ) r hr = pageMap data φ r hr ≫ pageMap data ψ r hr := by
  ext pq
  exact EMap_comp ..

variable [X.HasSpectralSequence data] [Y.HasSpectralSequence data]

section

variable (W : SpectralObject C ι) [W.HasSpectralSequence data]
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq pq' pq'' : κ) (hpq : (c r).prev pq' = pq) (hpq' : (c r).next pq' = pq'')
    (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
    (hi₀' : i₀' = data.i₀ r' pq') (hi₀ : i₀ = data.i₀ r pq')
    (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq')
    (hi₃ : i₃ = data.i₃ r pq') (hi₃' : i₃' = data.i₃ r' pq')
    (n₀ n₁ n₂ : ℤ) (hn₁' : n₁ = data.deg pq')

/-- The monomorphism of the left homology datum of a page of the spectral sequence of a
spectral object, written out: it is `mapFourδ₁Toδ₀'` followed by a reindexing. -/
lemma homologyData_left_i_eq (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (homologyData W data r r' hrr' hr pq pq' pq'' hpq hpq'
        i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).left.i =
      W.mapFourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃ (data.i₀_le' hrr' hr pq' hi₀' hi₀)
        (data.le₀₁' r hr pq' hi₀ hi₁) (data.le₁₂' pq' hi₁ hi₂)
        (data.le₂₃' r hr pq' hi₂ hi₃) n₀ n₁ n₂ hn₁ hn₂ ≫
      (pageXIso W data r hr pq' i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁' hn₁ hn₂).inv :=
  rfl

/-- The epimorphism of the left homology datum of a page of the spectral sequence of a spectral
object, written out: it is `mapFourδ₄Toδ₃'`. -/
lemma homologyData_left_π_eq (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (homologyData W data r r' hrr' hr pq pq' pq'' hpq hpq'
        i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).left.π =
      W.mapFourδ₄Toδ₃' i₀' i₁ i₂ i₃ i₃'
        ((data.i₀_le' hrr' hr pq' hi₀' hi₀).trans (data.le₀₁' r hr pq' hi₀ hi₁))
        (data.le₁₂' pq' hi₁ hi₂) (data.le₂₃' r hr pq' hi₂ hi₃)
        (data.le₃₃' hrr' hr pq' hi₃ hi₃') n₀ n₁ n₂ hn₁ hn₂ :=
  rfl

end

section

variable (φ : X ⟶ Y)
  (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
  (pq pq' pq'' : κ) (hpq : (c r).prev pq' = pq) (hpq' : (c r).next pq' = pq'')
  (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
  (hi₀' : i₀' = data.i₀ r' pq') (hi₀ : i₀ = data.i₀ r pq')
  (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq')
  (hi₃ : i₃ = data.i₃ r pq') (hi₃' : i₃' = data.i₃ r' pq')
  (n₀ n₁ n₂ : ℤ) (hn₁' : n₁ = data.deg pq')

/-- **`EMap` commutes with the monomorphism of the left homology datum of a page.** -/
lemma EMap_homologyData_left_i (le₀₁ : i₀' ≤ i₁) (le₁₂ : i₁ ≤ i₂) (le₂₃ : i₂ ≤ i₃)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    EMap (homOfLE le₀₁) (homOfLE le₁₂) (homOfLE le₂₃) n₀ n₁ n₂ φ hn₁ hn₂ ≫
      (homologyData Y data r r' hrr' hr pq pq' pq'' hpq hpq'
        i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).left.i =
      (homologyData X data r r' hrr' hr pq pq' pq'' hpq hpq'
        i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).left.i ≫
      pageXMap data φ r pq' hr := by
  rw [homologyData_left_i_eq (data := data) (n₀ := n₀) (n₁ := n₁) (n₂ := n₂)
      (hn₁ := hn₁) (hn₂ := hn₂) (W := Y),
    homologyData_left_i_eq (data := data) (n₀ := n₀) (n₁ := n₁) (n₂ := n₂)
      (hn₁ := hn₁) (hn₂ := hn₂) (W := X)]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact (map_EMap_assoc ..).symm.trans (_ ≫= EMap_pageXIso_inv data φ r hr pq'
    (data.le₀₁' r hr pq' hi₀ hi₁) (data.le₁₂' pq' hi₁ hi₂)
    (data.le₂₃' r hr pq' hi₂ hi₃) hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁' hn₁ hn₂)

/-- **`EMap` commutes with the epimorphism of the left homology datum of a page.** -/
lemma homologyData_left_π_EMap (le₀₁ : i₀' ≤ i₁) (le₁₂ : i₁ ≤ i₂) (le₂₃ : i₂ ≤ i₃)
    (le₂₃' : i₂ ≤ i₃') (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
      (homologyData X data r r' hrr' hr pq pq' pq'' hpq hpq'
        i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).left.π ≫
      EMap (homOfLE le₀₁) (homOfLE le₁₂) (homOfLE le₂₃') n₀ n₁ n₂ φ hn₁ hn₂ =
      EMap (homOfLE le₀₁) (homOfLE le₁₂) (homOfLE le₂₃) n₀ n₁ n₂ φ hn₁ hn₂ ≫
      (homologyData Y data r r' hrr' hr pq pq' pq'' hpq hpq'
        i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).left.π := by
  rw [homologyData_left_π_eq (data := data) (n₀ := n₀) (n₁ := n₁) (n₂ := n₂)
      (hn₁ := hn₁) (hn₂ := hn₂) (W := X),
    homologyData_left_π_eq (data := data) (n₀ := n₀) (n₁ := n₁) (n₂ := n₂)
      (hn₁ := hn₁) (hn₂ := hn₂) (W := Y)]
  exact map_EMap ..

/-- **The map on cycles of the left homology data is `EMap`.**  The map induced by `pageMap` on
the cycles of the left homology data of a page is `EMap`. -/
lemma cyclesMap'_eq_EMap (le₀₁ : i₀' ≤ i₁) (le₁₂ : i₁ ≤ i₂) (le₂₃ : i₂ ≤ i₃)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex.cyclesMap'
      ((HomologicalComplex.shortComplexFunctor' C (c r) pq pq' pq'').map (pageMap data φ r hr))
      (homologyData X data r r' hrr' hr pq pq' pq'' hpq hpq'
        i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).left
      (homologyData Y data r r' hrr' hr pq pq' pq'' hpq hpq'
        i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).left =
      EMap (homOfLE le₀₁) (homOfLE le₁₂) (homOfLE le₂₃) n₀ n₁ n₂ φ hn₁ hn₂ := by
  refine (cancel_mono (homologyData Y data r r' hrr' hr pq pq' pq'' hpq hpq'
        i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).left.i).1 ?_
  rw [ShortComplex.cyclesMap'_i]
  exact (EMap_homologyData_left_i data φ r r' hrr' hr pq pq' pq'' hpq hpq'
    i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' le₀₁ le₁₂ le₂₃ hn₁ hn₂).symm

/-- **The map on left homology of the left homology data is `EMap`.**  The map induced by
`pageMap` on the left homology of the left homology data of a page is `EMap`. -/
lemma leftHomologyMap'_eq_EMap (le₀₁ : i₀' ≤ i₁) (le₁₂ : i₁ ≤ i₂) (le₂₃ : i₂ ≤ i₃)
    (le₂₃' : i₂ ≤ i₃') (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex.leftHomologyMap'
      ((HomologicalComplex.shortComplexFunctor' C (c r) pq pq' pq'').map (pageMap data φ r hr))
      (homologyData X data r r' hrr' hr pq pq' pq'' hpq hpq'
        i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).left
      (homologyData Y data r r' hrr' hr pq pq' pq'' hpq hpq'
        i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).left =
      EMap (homOfLE le₀₁) (homOfLE le₁₂) (homOfLE le₂₃') n₀ n₁ n₂ φ hn₁ hn₂ := by
  refine (cancel_epi (homologyData X data r r' hrr' hr pq pq' pq'' hpq hpq'
        i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).left.π).1 ?_
  rw [ShortComplex.leftHomologyπ_naturality',
    cyclesMap'_eq_EMap data φ r r' hrr' hr pq pq' pq'' hpq hpq'
    i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' le₀₁ le₁₂ le₂₃ hn₁ hn₂]
  exact (homologyData_left_π_EMap data φ r r' hrr' hr pq pq' pq'' hpq hpq'
    i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' le₀₁ le₁₂ le₂₃ le₂₃' hn₁ hn₂).symm

end

end SpectralSequence

section Functor

variable {ι κ : Type*} [Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (data : SpectralSequenceDataCore ι c r₀)
  {X Y : SpectralObject C ι} [X.HasSpectralSequence data] [Y.HasSpectralSequence data]

variable (W : SpectralObject C ι) [W.HasSpectralSequence data]

unseal spectralSequence in
/-- **Mathlib's `spectralSequence_iso`, with the composite written out.**  The page-to-page
isomorphism of the spectral sequence of a spectral object is the composite of
`HomologicalComplex.homologyIsoSc'`, the `homologyIso` of the left homology datum, and the
reindexing isomorphism `SpectralSequence.pageXIso` of the next page. -/
lemma spectralSequence_iso_hom (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq pq' pq'' : κ) (hpq : (c r).prev pq' = pq) (hpq' : (c r).next pq' = pq'')
    (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
    (hi₀' : i₀' = data.i₀ r' pq') (hi₀ : i₀ = data.i₀ r pq')
    (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq')
    (hi₃ : i₃ = data.i₃ r pq') (hi₃' : i₃' = data.i₃ r' pq')
    (n₀ n₁ n₂ : ℤ) (hn₁' : n₁ = data.deg pq')
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ((W.spectralSequence data).iso r r' pq').hom =
      ((SpectralSequence.page W data r hr).homologyIsoSc' pq pq' pq'' hpq hpq').hom ≫
        (SpectralSequence.homologyData W data r r' hrr' hr pq pq' pq'' hpq hpq'
          i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃'
          n₀ n₁ n₂ hn₁' hn₁ hn₂).left.homologyIso.hom ≫
          (SpectralSequence.pageXIso W data r' (by lia) pq' i₀' i₁ i₂ i₃'
            hi₀' hi₁ hi₂ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).inv := by
  rw [W.spectralSequence_iso data r r' hrr' hr pq pq' pq'' hpq hpq'
    i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂]
  rfl

unseal spectralSequence in
/-- **The morphism of spectral sequences induced by a morphism of spectral objects.**  Its
morphisms of pages are `SpectralSequence.pageMap`. -/
noncomputable def spectralSequenceMap (φ : X ⟶ Y) :
    X.spectralSequence data ⟶ Y.spectralSequence data where
  hom r hr := SpectralSequence.pageMap data φ r hr
  comm r r' pq hrr' hr := by
    have hr' : r₀ ≤ r' := hr.trans (by lia)
    rw [spectralSequence_iso_hom data X r r' hrr' hr _ pq _ rfl rfl _ _ _ _ _ _
        rfl rfl rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl,
      spectralSequence_iso_hom data Y r r' hrr' hr _ pq _ rfl rfl _ _ _ _ _ _
        rfl rfl rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl]
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (_ ≫= (Category.assoc _ _ _).symm)
    refine Eq.trans (HomologicalComplex.homologyMap_homologyIsoSc'_hom_assoc
      (SpectralSequence.pageMap data φ r hr) ((c r).prev pq) pq ((c r).next pq) rfl rfl _) ?_
    refine whisker_eq _ ?_
    refine Eq.trans (ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality_assoc
      _ (SpectralSequence.homologyData X data r r' hrr' hr _ pq _ rfl rfl
        _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
        (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl (by lia) (by lia)).left _ _).symm ?_
    refine whisker_eq ((SpectralSequence.homologyData X data r r' hrr' hr _ pq _ rfl rfl
        _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq)
        (data.deg pq + 1) rfl (by lia) (by lia)).left).homologyIso.hom ?_
    rw [SpectralSequence.leftHomologyMap'_eq_EMap data φ r r' hrr' hr _ pq _ rfl rfl
      _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl
      (data.le₀₁' r' hr' pq rfl rfl) (data.le₁₂' pq rfl rfl)
      (data.le₂₃' r hr pq rfl rfl) (data.le₂₃' r' hr' pq rfl rfl)]
    exact SpectralSequence.EMap_pageXIso_inv data φ r' hr' pq
      (data.le₀₁' r' hr' pq rfl rfl) (data.le₁₂' pq rfl rfl)
      (data.le₂₃' r' hr' pq rfl rfl) rfl rfl rfl rfl
      (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl

unseal spectralSequence in
/-- **The spectral sequence of a spectral object, as a functor.**  The hypothesis is that every
spectral object of `C` indexed by `ι` has the spectral sequence of `data`. -/
noncomputable def spectralSequenceFunctor
    [∀ (W : SpectralObject C ι), W.HasSpectralSequence data] :
    SpectralObject C ι ⥤ SpectralSequence C c r₀ where
  obj W := W.spectralSequence data
  map φ := spectralSequenceMap data φ
  map_id _W :=
    _root_.CategoryTheory.SpectralSequence.hom_ext
      (fun r hr ↦ SpectralSequence.pageMap_id data r hr)
  map_comp φ ψ :=
    _root_.CategoryTheory.SpectralSequence.hom_ext
      (fun r hr ↦ SpectralSequence.pageMap_comp data φ ψ r hr)

/-- **The `E₂`-cohomological spectral sequence of a spectral object indexed by `EInt`, as a
functor.** -/
noncomputable abbrev E₂SpectralSequenceFunctor (D : Type*) [Category* D] [Abelian D] :
    SpectralObject D EInt ⥤ E₂CohomologicalSpectralSequence D :=
  spectralSequenceFunctor coreE₂Cohomological

unseal spectralSequence in
/-- **The first-page identification is natural in the spectral object.**  When `data` has a
first-page computation, the isomorphism
`((X.spectralSequence data).page r₀).X pq ≅ (X.H n).obj (mk₁ _)` of
`spectralSequenceFirstPageXIso` is natural in `X`. -/
lemma spectralSequenceFirstPageXIso_hom_naturality [data.HasFirstPageComputation] (φ : X ⟶ Y)
    (pq : κ) (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
    (n : ℤ) (hn : n = data.deg pq) :
    ((spectralSequenceMap data φ).hom r₀).f pq ≫
        (Y.spectralSequenceFirstPageXIso data pq i₁ i₂ hi₁ hi₂ n hn).hom =
      (X.spectralSequenceFirstPageXIso data pq i₁ i₂ hi₁ hi₂ n hn).hom ≫
        (φ.hom n).app (mk₁ (homOfLE (data.le₁₂' pq hi₁ hi₂))) := by
  rw [X.spectralSequenceFirstPageXIso_hom data pq i₁ i₂ hi₁ hi₂ (n - 1) n (n + 1) hn,
    Y.spectralSequenceFirstPageXIso_hom data pq i₁ i₂ hi₁ hi₂ (n - 1) n (n + 1) hn]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact (SpectralSequence.pageXIso_hom_EMap_assoc data φ r₀ (by rfl) pq
    le_rfl (data.le₁₂' pq hi₁ hi₂) le_rfl (by rw [hi₁, ← data.hi₀₁]) hi₁ hi₂
    (by rw [hi₂, data.hi₂₃]) (n - 1) n (n + 1) hn (by lia) (by lia) _).symm.trans
      (_ ≫= EMap_EIsoH_hom (homOfLE (data.le₁₂' pq hi₁ hi₂)) (n - 1) n (n + 1) φ
        (by lia) (by lia))

/-- **The objects of the starting page, as a natural isomorphism of functors.**  Composing the
functor `spectralSequenceFunctor` with "take the `r₀`-th page at `pq`" is naturally isomorphic
to "take `H^n` at the arrow `data.i₁ pq ≤ data.i₂ pq`", with components
`spectralSequenceFirstPageXIso`. -/
noncomputable def spectralSequenceFirstPageXNatIso [data.HasFirstPageComputation]
    [∀ (W : SpectralObject C ι), W.HasSpectralSequence data]
    (pq : κ) (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
    (n : ℤ) (hn : n = data.deg pq) :
    spectralSequenceFunctor data ⋙
        _root_.CategoryTheory.SpectralSequence.pageFunctor C c r₀ r₀ (le_refl r₀) ⋙
          HomologicalComplex.eval C (c r₀) pq ≅
      HObjFunctor n (mk₁ (homOfLE (data.le₁₂' pq hi₁ hi₂))) :=
  NatIso.ofComponents
    (fun W ↦ W.spectralSequenceFirstPageXIso data pq i₁ i₂ hi₁ hi₂ n hn)
    (fun φ ↦ spectralSequenceFirstPageXIso_hom_naturality data φ pq i₁ i₂ hi₁ hi₂ n hn)

end Functor

end SpectralObject

end Abelian

end CategoryTheory

end
