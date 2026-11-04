module

public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
public import StacksFrontier.AlgebraicGeometry.Topologies.EtaleDescentIntegral
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale schemes and universal homeomorphisms

Let `g : S' ⟶ S` be a universal homeomorphism. This file collects what the topological
invariance of the small étale site (Stacks Project, Tag 0BTY) needs about `g`, and proves the
uniqueness half of that statement.

## Main definitions

* `Stacks.Etale.pullbackSectionObjIso`: base change along `r` followed by base change along a
  section `s` of `r` returns the original object of the over category.
* `Stacks.Etale.diagonalDescentComparison`: the morphism along the diagonal `S' ⟶ S' ×_S S'`
  that a descent datum relative to `S'/S` is required to restrict to.

## Main results

* `Stacks.Etale.isSeparated_of_universalHomeomorphism`: a universal homeomorphism is separated.
* `Stacks.Etale.isClosedImmersion_diagonal_of_universalHomeomorphism` and
  `Stacks.Etale.surjective_diagonal_of_universalHomeomorphism`: the diagonal
  `S' ⟶ S' ×_S S'` of a universal homeomorphism is a thickening.
* `Stacks.Etale.bijective_diagonalPullback_hom`: consequently, base change along that diagonal
  is a bijection on morphisms into a scheme étale over `S' ×_S S'`.
* `Stacks.Etale.injective_baseChange_hom_of_surjective` and
  `Stacks.Etale.injective_baseChange_hom_of_universalHomeomorphism`: base change along a
  surjective morphism is injective on morphisms into an étale scheme. This is the injectivity
  half of Tag 0BTY.
* `Stacks.Etale.existsUnique_diagonalDescentHom` and
  `Stacks.Etale.isIso_of_map_diagonal_eq_comparison`: a scheme étale over `S'` carries a unique
  descent datum relative to `S'/S`, and it is an isomorphism. This is the claim proved in the
  course of Tag 0BTY.

## Implementation notes

Schemes over a base are represented by objects of the over category, and base change by
`CategoryTheory.Over.pullback`.

The hypothesis `AlgebraicGeometry.UniversalHomeomorphism` is the library form of the property
in Stacks Project, Tag 04DD; `universalHomeomorphism_iff_integral_universallyInjective_surjective`
is the characterisation of Tag 04DF.

Surjectivity of the diagonal is Mathlib's `UniversallyInjective.iff_diagonal`, the implication
(1) ⇒ (4) of Tag 01S4.

## References

* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
* [Stacks Project, Tag 01S4](https://stacks.math.columbia.edu/tag/01S4)
-/

@[expose] public section

namespace Stacks.Etale

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {S S' : Scheme.{u}}

/-- A universal homeomorphism of schemes is integral. -/
theorem isIntegralHom_of_universalHomeomorphism (g : S' ⟶ S) [UniversalHomeomorphism g] :
    IsIntegralHom g :=
  ((universalHomeomorphism_iff_integral_universallyInjective_surjective g).mp inferInstance).1

/-- A universal homeomorphism of schemes is universally injective. -/
theorem universallyInjective_of_universalHomeomorphism (g : S' ⟶ S)
    [UniversalHomeomorphism g] : UniversallyInjective g :=
  ((universalHomeomorphism_iff_integral_universallyInjective_surjective g).mp inferInstance).2.1

/-- A universal homeomorphism of schemes is surjective. -/
@[ega "IV 2.4.5" "(ii)"]
theorem surjective_of_universalHomeomorphism (g : S' ⟶ S) [UniversalHomeomorphism g] :
    Surjective g :=
  ((universalHomeomorphism_iff_integral_universallyInjective_surjective g).mp inferInstance).2.2

/-- A universal homeomorphism of schemes is separated. -/
theorem isSeparated_of_universalHomeomorphism (g : S' ⟶ S) [UniversalHomeomorphism g] :
    IsSeparated g :=
  have := isIntegralHom_of_universalHomeomorphism g
  IsSeparated.of_isAffineHom g

/-- The diagonal of a universal homeomorphism is a closed immersion. -/
theorem isClosedImmersion_diagonal_of_universalHomeomorphism (g : S' ⟶ S)
    [UniversalHomeomorphism g] : IsClosedImmersion (pullback.diagonal g) :=
  have := isSeparated_of_universalHomeomorphism g
  IsSeparated.isClosedImmersion_diagonal

/-- The diagonal of a universal homeomorphism is surjective on points; together with
`isClosedImmersion_diagonal_of_universalHomeomorphism` this says that `S' ⟶ S' ×_S S'` is a
thickening. -/
theorem surjective_diagonal_of_universalHomeomorphism (g : S' ⟶ S)
    [UniversalHomeomorphism g] : Function.Surjective (pullback.diagonal g).base :=
  have := universallyInjective_of_universalHomeomorphism g
  ((UniversallyInjective.iff_diagonal g).mp inferInstance).surj

/-- Base change along the diagonal `S' ⟶ S' ×_S S'` of a universal homeomorphism is a bijection
on morphisms into a scheme étale over `S' ×_S S'`. -/
theorem bijective_diagonalPullback_hom (g : S' ⟶ S) [UniversalHomeomorphism g]
    (X Y : Over (pullback g g)) [Etale X.hom] :
    Function.Bijective
      (fun f : Y ⟶ X => (Over.pullback (pullback.diagonal g)).map f) :=
  have := isClosedImmersion_diagonal_of_universalHomeomorphism g
  bijective_pullbackHom_of_etale (pullback.diagonal g)
    (surjective_diagonal_of_universalHomeomorphism g) X Y

/-- Base change along a surjective morphism of schemes is injective on morphisms into an étale
scheme.

This is the injectivity half of Stacks Project, Tag 0BTY: an `S`-morphism into a scheme étale
over `S` is determined by its base change along any surjection onto `S`. -/
@[ega "IV 2.2.16" "Target S-scheme étale"]
theorem injective_baseChange_hom_of_surjective (g : S' ⟶ S) [Surjective g]
    (X Y : Over S) [Etale X.hom] :
    Function.Injective (fun f : Y ⟶ X => (Over.pullback g).map f) := by
  let : MorphismProperty.IsStableUnderBaseChangeAlong (P := @Surjective) Y.hom :=
    ⟨fun pb H => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb H⟩
  let : Surjective (pullback.fst Y.hom g) := MorphismProperty.pullback_fst Y.hom g inferInstance
  intro f h hfh
  apply Over.OverMorphism.ext
  have hbase : f.left ≫ X.hom = h.left ≫ X.hom := (Over.w f).trans (Over.w h).symm
  have hrestrict : pullback.fst Y.hom g ≫ f.left = pullback.fst Y.hom g ≫ h.left := by
    calc
      pullback.fst Y.hom g ≫ f.left =
          ((Over.pullback g).map f).left ≫ pullback.fst X.hom g := by
        simp [Over.pullback_map_left, pullback.lift_fst]
      _ = ((Over.pullback g).map h).left ≫ pullback.fst X.hom g := by
        rw [congrArg Over.Hom.left hfh]
      _ = pullback.fst Y.hom g ≫ h.left := by
        simp [Over.pullback_map_left, pullback.lift_fst]
  exact hom_ext_of_surjective (pullback.fst Y.hom g) this.surj X.hom f.left h.left hbase hrestrict

/-- Base change along a universal homeomorphism is injective on morphisms into an étale scheme:
the injectivity half of Stacks Project, Tag 0BTY. -/
@[ega "IV 2.2.16" "special case"]
theorem injective_baseChange_hom_of_universalHomeomorphism (g : S' ⟶ S)
    [UniversalHomeomorphism g] (X Y : Over S) [Etale X.hom] :
    Function.Injective (fun f : Y ⟶ X => (Over.pullback g).map f) :=
  have := surjective_of_universalHomeomorphism g
  injective_baseChange_hom_of_surjective g X Y

section Section

variable {A B : Scheme.{u}}

/-- Reading an object of `Over B` first as a scheme over `A` via `r` and then back over `B` via
a section `s` of `r` returns its structure morphism. -/
theorem pullbackSection_fst_fst_comp_hom (r : A ⟶ B) (s : B ⟶ A) (h : s ≫ r = 𝟙 B)
    (V : Over B) :
    (pullback.fst (pullback.snd V.hom r) s ≫ pullback.fst V.hom r) ≫ V.hom =
      pullback.snd (pullback.snd V.hom r) s := by
  calc
    (pullback.fst (pullback.snd V.hom r) s ≫ pullback.fst V.hom r) ≫ V.hom =
        pullback.fst (pullback.snd V.hom r) s ≫ pullback.snd V.hom r ≫ r := by
      rw [Category.assoc, pullback.condition]
    _ = pullback.snd (pullback.snd V.hom r) s ≫ s ≫ r := by
      rw [← Category.assoc, pullback.condition, Category.assoc]
    _ = pullback.snd (pullback.snd V.hom r) s := by rw [h, Category.comp_id]

/-- If `s` is a section of `r`, then base changing an object of `Over B` along `r` and then
along `s` returns its underlying scheme. -/
noncomputable def pullbackSectionLeftIso (r : A ⟶ B) (s : B ⟶ A) (h : s ≫ r = 𝟙 B)
    (V : Over B) : pullback (pullback.snd V.hom r) s ≅ V.left where
  hom := pullback.fst (pullback.snd V.hom r) s ≫ pullback.fst V.hom r
  inv := pullback.lift (pullback.lift (𝟙 V.left) (V.hom ≫ s) (by simp [h])) V.hom
    (pullback.lift_snd _ _ _)
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, pullback.lift_fst]
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.comp_id]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc,
          pullbackSection_fst_fst_comp_hom r s h V]
        exact pullback.condition.symm
    · rw [Category.id_comp, Category.assoc, pullback.lift_snd]
      exact pullbackSection_fst_fst_comp_hom r s h V
  inv_hom_id := by rw [← Category.assoc, pullback.lift_fst, pullback.lift_fst]

/-- The forward map of `pullbackSectionLeftIso`. -/
@[simp]
theorem pullbackSectionLeftIso_hom (r : A ⟶ B) (s : B ⟶ A) (h : s ≫ r = 𝟙 B) (V : Over B) :
    (pullbackSectionLeftIso r s h V).hom =
      pullback.fst (pullback.snd V.hom r) s ≫ pullback.fst V.hom r :=
  rfl

/-- If `s` is a section of `r`, then base change along `r` followed by base change along `s`
returns the original object of `Over B`. -/
noncomputable def pullbackSectionObjIso (r : A ⟶ B) (s : B ⟶ A) (h : s ≫ r = 𝟙 B)
    (V : Over B) : (Over.pullback s).obj ((Over.pullback r).obj V) ≅ V :=
  Over.isoMk (pullbackSectionLeftIso r s h V) (pullbackSection_fst_fst_comp_hom r s h V)

end Section

section Diagonal

variable (g : S' ⟶ S) (V : Over S')

/-- The canonical identification of `V` with the pullback along the diagonal of the base change
of `V` to `S' ×_S S'` along the first projection. -/
noncomputable abbrev diagonalPullbackFstObjIso :
    (Over.pullback (pullback.diagonal g)).obj ((Over.pullback (pullback.fst g g)).obj V) ≅ V :=
  pullbackSectionObjIso _ _ (pullback.diagonal_fst g) V

/-- The canonical identification of `V` with the pullback along the diagonal of the base change
of `V` to `S' ×_S S'` along the second projection. -/
noncomputable abbrev diagonalPullbackSndObjIso :
    (Over.pullback (pullback.diagonal g)).obj ((Over.pullback (pullback.snd g g)).obj V) ≅ V :=
  pullbackSectionObjIso _ _ (pullback.diagonal_snd g) V

/-- The morphism along the diagonal that a descent datum on `V` relative to `S'/S` is required
to restrict to: the identity of `V`, read through the two canonical identifications. -/
noncomputable abbrev diagonalDescentComparison :
    (Over.pullback (pullback.diagonal g)).obj ((Over.pullback (pullback.fst g g)).obj V) ⟶
      (Over.pullback (pullback.diagonal g)).obj ((Over.pullback (pullback.snd g g)).obj V) :=
  (diagonalPullbackFstObjIso g V).hom ≫ (diagonalPullbackSndObjIso g V).inv

/-- The base change of a scheme étale over `S'` along the first projection of `S' ×_S S'` is
étale. -/
theorem etale_pullbackFst_hom [Etale V.hom] :
    Etale ((Over.pullback (pullback.fst g g)).obj V).hom := by
  show Etale (pullback.snd V.hom (pullback.fst g g))
  infer_instance

/-- The base change of a scheme étale over `S'` along the second projection of `S' ×_S S'` is
étale. -/
theorem etale_pullbackSnd_hom [Etale V.hom] :
    Etale ((Over.pullback (pullback.snd g g)).obj V).hom := by
  show Etale (pullback.snd V.hom (pullback.snd g g))
  infer_instance

variable [UniversalHomeomorphism g] [Etale V.hom]

/-- **The canonical descent datum of an étale scheme along a universal homeomorphism.**

Let `g : S' ⟶ S` be a universal homeomorphism and let `V` be étale over `S'`. Then there is a
unique morphism between the two base changes of `V` to `S' ×_S S'` which restricts along the
diagonal to the identity of `V`.

This is the claim proved in the course of Stacks Project, Tag 0BTY. -/
theorem existsUnique_diagonalDescentHom :
    ∃! φ : (Over.pullback (pullback.fst g g)).obj V ⟶
        (Over.pullback (pullback.snd g g)).obj V,
      (Over.pullback (pullback.diagonal g)).map φ = diagonalDescentComparison g V :=
  have := etale_pullbackSnd_hom g V
  (bijective_diagonalPullback_hom g ((Over.pullback (pullback.snd g g)).obj V)
    ((Over.pullback (pullback.fst g g)).obj V)).existsUnique _

/-- A morphism between the two base changes of `V` to `S' ×_S S'` which restricts along the
diagonal to `diagonalDescentComparison g V` is an isomorphism. -/
theorem isIso_of_map_diagonal_eq_comparison
    (φ : (Over.pullback (pullback.fst g g)).obj V ⟶ (Over.pullback (pullback.snd g g)).obj V)
    (hφ : (Over.pullback (pullback.diagonal g)).map φ = diagonalDescentComparison g V) :
    IsIso φ := by
  have hX := etale_pullbackFst_hom g V
  have hY := etale_pullbackSnd_hom g V
  obtain ⟨ψ, hψ⟩ :=
    (bijective_diagonalPullback_hom g ((Over.pullback (pullback.fst g g)).obj V)
      ((Over.pullback (pullback.snd g g)).obj V)).2
      ((diagonalPullbackSndObjIso g V).hom ≫ (diagonalPullbackFstObjIso g V).inv)
  have hψ' : (Over.pullback (pullback.diagonal g)).map ψ =
      (diagonalPullbackSndObjIso g V).hom ≫ (diagonalPullbackFstObjIso g V).inv := hψ
  have key : ∀ (X : Over (pullback g g)) [Etale X.hom] (u : X ⟶ X),
      (Over.pullback (pullback.diagonal g)).map u = 𝟙 _ → u = 𝟙 _ := fun X _ u hu =>
    (bijective_diagonalPullback_hom g X X).1 (hu.trans (CategoryTheory.Functor.map_id _ _).symm)
  refine ⟨ψ, key _ _ ?_, key _ _ ?_⟩
  · rw [Functor.map_comp, hφ, hψ']
    simp
  · rw [Functor.map_comp, hφ, hψ']
    simp

end Diagonal

end Stacks.Etale

end
