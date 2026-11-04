module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyPi

/-!
# Additive endomorphisms of a short complex of modules

Let `A` be a commutative ring and let `S` be a short complex of `A`-modules. An endomorphism of
`S` that is merely *additive* — a differential operator, say — is not a morphism of short
complexes of `A`-modules, so it induces nothing on `S.cycles` or `S.homology` by functoriality
in `ModuleCat A`. It is however a morphism of the underlying short complex of abelian groups,
and the forgetful functor `forget₂ (ModuleCat A) AddCommGrpCat` preserves the homology of `S`.
Transporting the cycles and homology maps of that morphism across Mathlib's comparison
isomorphisms `ShortComplex.mapCyclesIso` and `ShortComplex.mapHomologyIso` therefore produces
additive endomorphisms of `S.cycles` and `S.homology`.

The twisted Leibniz rule is inherited: if the middle component of the operator satisfies
`d (a • x) = θ a • x + a • d x` for a function `θ : A → A`, then so do the induced operators on
cycles and on homology. No hypothesis on `θ` is needed, and in particular it need not be a
derivation.

## Main definitions

* `CategoryTheory.ShortComplex.additiveCyclesMap` — the additive endomorphism of `S.cycles`
  induced by an additive endomorphism of `S`.
* `CategoryTheory.ShortComplex.additiveHomologyMap` — the additive endomorphism of `S.homology`
  induced by an additive endomorphism of `S`.

## Main results

* `CategoryTheory.ShortComplex.additiveCyclesMap_i` and
  `CategoryTheory.ShortComplex.additiveHomologyMap_π` — the induced operators are computed by
  the inclusion of cycles and by the projection to homology.
* `CategoryTheory.ShortComplex.additiveCyclesMap_leibniz` and
  `CategoryTheory.ShortComplex.additiveHomologyMap_leibniz` — the twisted Leibniz rule is
  inherited by cycles and by homology.
* `CategoryTheory.ShortComplex.additiveHomologyMap_naturality` — a morphism of short complexes
  of `A`-modules commuting with two additive endomorphisms commutes with the induced operators
  on homology.
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Category Limits

namespace ShortComplex

universe u

variable {A : Type u} [CommRing A]

/-- The forgetful functor from `A`-modules to abelian groups, under which an additive
endomorphism of a short complex of `A`-modules becomes a morphism of short complexes. -/
abbrev forgetToAddCommGrp (A : Type u) [CommRing A] :
    ModuleCat.{u} A ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat.{u} A) AddCommGrpCat

variable (S : ShortComplex (ModuleCat.{u} A))

/-- **The additive endomorphism of cycles induced by an additive endomorphism of `S`.** The
operator `φ` is a morphism of the underlying short complexes of abelian groups, and the
forgetful functor preserves cycles, so `φ` acts on `S.cycles`. -/
def additiveCyclesMap (φ : S.map (forgetToAddCommGrp A) ⟶ S.map (forgetToAddCommGrp A)) :
    S.cycles →+ S.cycles :=
  ((S.mapCyclesIso (forgetToAddCommGrp A)).inv ≫ cyclesMap φ ≫
    (S.mapCyclesIso (forgetToAddCommGrp A)).hom).hom

/-- The induced operator on cycles is computed by the middle component of `φ`, through the
inclusion of cycles. -/
lemma additiveCyclesMap_i
    (φ : S.map (forgetToAddCommGrp A) ⟶ S.map (forgetToAddCommGrp A)) (z : S.cycles) :
    S.iCycles (additiveCyclesMap S φ z) = φ.τ₂ (S.iCycles z) := by
  have h : (S.mapCyclesIso (forgetToAddCommGrp A)).inv ≫ cyclesMap φ ≫
      (S.mapCyclesIso (forgetToAddCommGrp A)).hom ≫
        (forgetToAddCommGrp A).map S.iCycles =
      (forgetToAddCommGrp A).map S.iCycles ≫ φ.τ₂ := by
    rw [mapCyclesIso_hom_iCycles, cyclesMap_i,
      ← mapCyclesIso_hom_iCycles S (forgetToAddCommGrp A)]
    simp only [assoc, Iso.inv_hom_id_assoc]
  exact congr($h z)

/-- **The additive endomorphism of homology induced by an additive endomorphism of `S`.** -/
def additiveHomologyMap (φ : S.map (forgetToAddCommGrp A) ⟶ S.map (forgetToAddCommGrp A)) :
    S.homology →+ S.homology :=
  ((S.mapHomologyIso (forgetToAddCommGrp A)).inv ≫ homologyMap φ ≫
    (S.mapHomologyIso (forgetToAddCommGrp A)).hom).hom

/-- The induced operator on homology sends the class of a cycle to the class of its image under
the induced operator on cycles. -/
lemma additiveHomologyMap_π
    (φ : S.map (forgetToAddCommGrp A) ⟶ S.map (forgetToAddCommGrp A)) (z : S.cycles) :
    additiveHomologyMap S φ (S.homologyπ z) =
      S.homologyπ (additiveCyclesMap S φ z) := by
  have h : (forgetToAddCommGrp A).map S.homologyπ ≫
        (S.mapHomologyIso (forgetToAddCommGrp A)).inv ≫ homologyMap φ ≫
          (S.mapHomologyIso (forgetToAddCommGrp A)).hom =
      (S.mapCyclesIso (forgetToAddCommGrp A)).inv ≫ cyclesMap φ ≫
        (S.mapCyclesIso (forgetToAddCommGrp A)).hom ≫
          (forgetToAddCommGrp A).map S.homologyπ := by
    rw [π_comp_mapHomologyIso_inv_assoc, homologyπ_naturality_assoc,
      homologyπ_comp_mapHomologyIso_hom]
  exact congr($h z)

/-- **The twisted Leibniz rule passes to cycles.** -/
lemma additiveCyclesMap_leibniz
    (φ : S.map (forgetToAddCommGrp A) ⟶ S.map (forgetToAddCommGrp A))
    (θ : A → A) (d : S.X₂ →+ S.X₂) (hd : ∀ x : S.X₂, φ.τ₂ x = d x)
    (hφ : ∀ (a : A) (x : S.X₂), d (a • x) = θ a • x + a • d x)
    (a : A) (z : S.cycles) :
    additiveCyclesMap S φ (a • z) = θ a • z + a • additiveCyclesMap S φ z := by
  apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
  simp only [additiveCyclesMap_i, map_add, map_smul, hd, hφ]

/-- **The twisted Leibniz rule passes to homology.** -/
lemma additiveHomologyMap_leibniz
    (φ : S.map (forgetToAddCommGrp A) ⟶ S.map (forgetToAddCommGrp A))
    (θ : A → A) (d : S.X₂ →+ S.X₂) (hd : ∀ x : S.X₂, φ.τ₂ x = d x)
    (hφ : ∀ (a : A) (x : S.X₂), d (a • x) = θ a • x + a • d x)
    (a : A) (x : S.homology) :
    additiveHomologyMap S φ (a • x) = θ a • x + a • additiveHomologyMap S φ x := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance x
  rw [← map_smul, additiveHomologyMap_π, additiveCyclesMap_leibniz S φ θ d hd hφ]
  simp only [map_add, map_smul, additiveHomologyMap_π]

/-- **Naturality of the induced operator on homology.** A morphism `k : S ⟶ T` of short complexes
of `A`-modules intertwining two additive endomorphisms intertwines the operators they induce on
homology. -/
lemma additiveHomologyMap_naturality (T : ShortComplex (ModuleCat.{u} A))
    (φ : S.map (forgetToAddCommGrp A) ⟶ S.map (forgetToAddCommGrp A))
    (ψ : T.map (forgetToAddCommGrp A) ⟶ T.map (forgetToAddCommGrp A)) (k : S ⟶ T)
    (hk : φ ≫ (forgetToAddCommGrp A).mapShortComplex.map k =
      (forgetToAddCommGrp A).mapShortComplex.map k ≫ ψ)
    (x : S.homology) :
    additiveHomologyMap T ψ (homologyMap k x) = homologyMap k (additiveHomologyMap S φ x) := by
  have h : (forgetToAddCommGrp A).map (homologyMap k) ≫
        (T.mapHomologyIso (forgetToAddCommGrp A)).inv ≫ homologyMap ψ ≫
          (T.mapHomologyIso (forgetToAddCommGrp A)).hom =
      (S.mapHomologyIso (forgetToAddCommGrp A)).inv ≫ homologyMap φ ≫
        (S.mapHomologyIso (forgetToAddCommGrp A)).hom ≫
          (forgetToAddCommGrp A).map (homologyMap k) := by
    rw [mapHomologyIso_inv_naturality_assoc, ← assoc (homologyMap _), ← homologyMap_comp,
      ← hk, homologyMap_comp]
    simp only [assoc]
    rw [mapHomologyIso_hom_naturality]
  exact congr($h x)

end ShortComplex

end CategoryTheory

end
