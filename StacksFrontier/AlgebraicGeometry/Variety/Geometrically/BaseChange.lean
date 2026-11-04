module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Machinery for iterated base change of a scheme over a field

Base changing a scheme over a field twice, first along `k → k'` and then along `k' → K`, gives
the same scheme as base changing once along the composite `k → K`. This file records that
comparison isomorphism for an arbitrary tower of morphisms of schemes, together with the fact
that the morphism of spectra induced by a purely inseparable field extension is universally
injective.

## Main definitions

* `AlgebraicGeometry.iteratedBaseChangeIso` compares a twice-iterated fibre product with the
  fibre product along the composite.
* `AlgebraicGeometry.iteratedBaseChangeComparison` is the resulting morphism from the base
  change along one leg of a composite to the base change along another.

## Main results

* `AlgebraicGeometry.iteratedBaseChangeIso_fst` identifies the composite of that isomorphism
  with the projection to the original scheme.
* `AlgebraicGeometry.iteratedBaseChangeIso_snd` identifies the composite of that isomorphism
  with the projection to the base.
* `AlgebraicGeometry.iteratedBaseChangeComparison_fst` identifies the composite of that
  comparison morphism with the projection to the original scheme.
* `AlgebraicGeometry.specMap_algebraMap_comp`: the morphisms of spectra induced by the two
  steps of a tower of field extensions compose to the one induced by the whole tower.
* `AlgebraicGeometry.universallyInjective_specMap_of_isPurelyInseparable`: the morphism of
  spectra induced by a purely inseparable field extension is universally injective.

## Implementation notes

The tower is given by `φ : Z ⟶ Y` and `χ : W ⟶ Z` together with a morphism `μ : W ⟶ Y` and a
proof that `χ ≫ φ = μ`; supplying `μ` separately rather than using `χ ≫ φ` keeps the composite
in the form in which the base-change statements present it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- The comparison isomorphism between base changing `f` first along `φ` and then along `χ`,
and base changing it once along a composite `μ` of `χ` and `φ`. -/
public noncomputable def iteratedBaseChangeIso {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (φ : Z ⟶ Y) (χ : W ⟶ Z) (μ : W ⟶ Y)
    (h : χ ≫ φ = μ) :
    pullback (pullback.snd f φ) χ ≅ pullback f μ :=
  asIso ((pullbackSymmetry _ _).hom ≫
    pullback.map _ _ _ _ (𝟙 _) (pullbackSymmetry _ _).hom (𝟙 _)
      (by simp) (by simp)) ≪≫
    pullbackRightPullbackFstIso φ f χ ≪≫
      pullback.congrHom h rfl ≪≫ pullbackSymmetry μ f

/-- The comparison isomorphism for iterated base change is compatible with the projections
down to the original scheme. -/
public lemma iteratedBaseChangeIso_fst {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (φ : Z ⟶ Y) (χ : W ⟶ Z) (μ : W ⟶ Y)
    (h : χ ≫ φ = μ) :
    (iteratedBaseChangeIso f φ χ μ h).hom ≫ pullback.fst f μ =
      pullback.fst (pullback.snd f φ) χ ≫ pullback.fst f φ := by
  dsimp [iteratedBaseChangeIso, pullback.congrHom, pullback.map]
  simp only [Category.comp_id]
  simp only [Category.assoc, pullbackSymmetry_hom_comp_fst]
  rw [pullback.lift_snd, pullbackRightPullbackFstIso_hom_snd,
    pullback.lift_snd_assoc]
  simp only [Category.assoc, pullbackSymmetry_hom_comp_snd]
  rw [pullbackSymmetry_hom_comp_snd_assoc]

/-- The comparison isomorphism for iterated base change is compatible with the projections
down to the base. -/
public lemma iteratedBaseChangeIso_snd {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (φ : Z ⟶ Y) (χ : W ⟶ Z) (μ : W ⟶ Y)
    (h : χ ≫ φ = μ) :
    (iteratedBaseChangeIso f φ χ μ h).hom ≫ pullback.snd f μ =
      pullback.snd (pullback.snd f φ) χ := by
  dsimp [iteratedBaseChangeIso, pullback.congrHom, pullback.map]
  simp only [Category.comp_id]
  simp only [Category.assoc, pullbackSymmetry_hom_comp_snd]
  rw [pullback.lift_fst, pullbackRightPullbackFstIso_hom_fst, pullback.lift_fst,
    pullbackSymmetry_hom_comp_fst]

/-- The comparison morphism from the base change of `f` along a tower `χU`, `φ` to the base change
of `f` along a second leg `ψ` of the same composite `μ`, obtained by passing through the base
change along `μ` and projecting. -/
public noncomputable def iteratedBaseChangeComparison {S T U V W : Scheme.{u}}
    (f : S ⟶ T) (φ : U ⟶ T) (ψ : V ⟶ T)
    (χU : W ⟶ U) (χV : W ⟶ V) (μ : W ⟶ T)
    (hU : χU ≫ φ = μ) (hV : χV ≫ ψ = μ) :
    pullback (pullback.snd f φ) χU ⟶ pullback f ψ :=
  (iteratedBaseChangeIso f φ χU μ hU).hom ≫
    (iteratedBaseChangeIso f ψ χV μ hV).inv ≫
      pullback.fst (pullback.snd f ψ) χV

/-- The comparison morphism between two base changes along legs of one composite is compatible
with the projections down to the original scheme. -/
public lemma iteratedBaseChangeComparison_fst {S T U V W : Scheme.{u}}
    (f : S ⟶ T) (φ : U ⟶ T) (ψ : V ⟶ T)
    (χU : W ⟶ U) (χV : W ⟶ V) (μ : W ⟶ T)
    (hU : χU ≫ φ = μ) (hV : χV ≫ ψ = μ) :
    iteratedBaseChangeComparison f φ ψ χU χV μ hU hV ≫ pullback.fst f ψ =
      pullback.fst (pullback.snd f φ) χU ≫ pullback.fst f φ := by
  dsimp [iteratedBaseChangeComparison]
  rw [Category.assoc, Category.assoc,
    ← iteratedBaseChangeIso_fst f ψ χV μ hV,
    Iso.inv_hom_id_assoc,
    iteratedBaseChangeIso_fst f φ χU μ hU]

/-
The comparison isomorphism is sealed once its projection lemma is available: the iterated
base changes it relates are large terms, and leaving it transparent makes the kernel unfold
them at every use site. Downstream only ever needs that it is an isomorphism and how it
composes with the projections, both of which survive sealing.
-/
attribute [irreducible] iteratedBaseChangeIso

/-- The morphisms of spectra induced by the two steps `k → K` and `K → L` of a tower of field
extensions compose to the morphism induced by `k → L`. -/
public lemma specMap_algebraMap_comp (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] :
    Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (Spec.map ∘ CommRingCat.ofHom) (IsScalarTower.algebraMap_eq k K L).symm

/-- The morphism of spectra induced by a purely inseparable field extension is universally
injective. -/
public lemma universallyInjective_specMap_of_isPurelyInseparable
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsPurelyInseparable k K] :
    UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  apply ((tfae_universallyInjective
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).out 2 1).mp
  intro L _ a b hab
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply IsPurelyInseparable.injective_comp_algebraMap k K L
  have hcat : CommRingCat.ofHom (algebraMap k K) ≫ a =
      CommRingCat.ofHom (algebraMap k K) ≫ b := by
    apply Spec.map_injective
    simpa only [← Spec.map_comp] using hab
  exact congrArg CommRingCat.Hom.hom hcat

end AlgebraicGeometry
