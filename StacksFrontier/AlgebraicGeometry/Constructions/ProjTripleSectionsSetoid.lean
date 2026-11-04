module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleClassifyingMorphism

/-!
# Strict equivalence of weight-`d` graded maps is an equivalence relation

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `Y` a scheme and `d ≥ 1`.  A weight-`d` graded map on
`Y` is an `𝒪_Y`-module `L` together with a `ψ : A^{(d)} ⟶ Γ_*(Y, L)`, i.e. a
`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections`, and
`Stacks.AlgebraicGeometry.ProjTripleClassifying.SectionsEquiv` is strict equivalence of two such:
an isomorphism `β : L ≅ L'` whose tensor powers carry `ψ` to `ψ'` degreewise.  It is the relation
the set `F_d(Y)` of [Stacks, Tag 01N4] quotients by, and
`Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom_eq_of_sectionsEquiv` is the
statement that the morphism to `Proj(A)` is constant on its classes.

This file proves that the tensor powers `Stacks.AmplePullbackPart1.natTensorPowCongr` of an
isomorphism are functorial in it, deduces that strict equivalence is reflexive, symmetric and
transitive, and bundles it as a `Setoid` on the type of weight-`d` graded maps on `Y`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTripleClassifying.DegreeSections`: a weight-`d` graded map on `Y`
  together with the module it maps into, as one type.
* `Stacks.AlgebraicGeometry.ProjTripleClassifying.sectionsSetoid`: strict equivalence as a
  `Setoid` on that type.  Its quotient is the set `F_d(Y)` of [Stacks, Tag 01N4] once the
  invertibility and generation conditions are imposed.

## Main results

* `Stacks.AmplePullbackPart1.natTensorPowCongr_zero` and `natTensorPowCongr_succ`: the two arms
  of the recursion defining the tensor powers of an isomorphism, as equations.
* `Stacks.AmplePullbackPart1.natTensorPowCongr_refl`, `natTensorPowCongr_symm` and
  `natTensorPowCongr_trans`: the tensor powers of an isomorphism are functorial in it.
* `Stacks.AlgebraicGeometry.ProjTripleClassifying.sectionsEquiv_refl`, `sectionsEquiv_symm` and
  `sectionsEquiv_trans`: strict equivalence is reflexive, symmetric and transitive.

## Implementation notes

The monoidal structure on `Y.Modules` is available only through the local instances of
`Stacks.SheafInternalHom`, so the `attribute [local instance]` block of
`StacksFrontier/AlgebraicGeometry/Constructions/ProjTripleClassifyingMorphism.lean` is repeated here.

`SectionsEquiv` relates graded maps into *different* modules, so the module is packaged with the
graded map as a `Sigma` type.  The invertibility and generation conditions of a triple play no
part in strict equivalence and are not assumed.

## References

* [Stacks Project, Tag 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Tag 01NB](https://stacks.math.columbia.edu/tag/01NB)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.TensorPowers (natTensorPow)

universe v u w

namespace Stacks.AmplePullbackPart1

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The zeroth tensor power of an isomorphism is the identity of the monoidal unit. -/
theorem natTensorPowCongr_zero {A B : C} (e : A ≅ B) :
    natTensorPowCongr e 0 = Iso.refl (𝟙_ C) := rfl

/-- The `(n+1)`-st tensor power of an isomorphism is the `n`-th tensored with it. -/
theorem natTensorPowCongr_succ {A B : C} (e : A ≅ B) (n : ℕ) :
    natTensorPowCongr e (n + 1) = natTensorPowCongr e n ⊗ᵢ e := rfl

/-- The tensor powers of an identity are identities. -/
theorem natTensorPowCongr_refl {A : C} : ∀ n : ℕ,
    natTensorPowCongr (Iso.refl A) n = Iso.refl (natTensorPow A n)
  | 0 => rfl
  | n + 1 => by
      show natTensorPowCongr (Iso.refl A) n ⊗ᵢ Iso.refl A = Iso.refl (natTensorPow A n ⊗ A)
      rw [natTensorPowCongr_refl n]
      exact Iso.ext (MonoidalCategory.id_tensorHom_id _ _)

/-- The tensor powers of an inverse are the inverses of the tensor powers. -/
theorem natTensorPowCongr_symm {A B : C} (e : A ≅ B) : ∀ n : ℕ,
    natTensorPowCongr e.symm n = (natTensorPowCongr e n).symm
  | 0 => rfl
  | n + 1 => by
      show natTensorPowCongr e.symm n ⊗ᵢ e.symm = (natTensorPowCongr e n ⊗ᵢ e).symm
      rw [natTensorPowCongr_symm e n]
      rfl

/-- The tensor powers of a composite are the composites of the tensor powers. -/
theorem natTensorPowCongr_trans {A B D : C} (e : A ≅ B) (g : B ≅ D) : ∀ n : ℕ,
    natTensorPowCongr (e ≪≫ g) n = natTensorPowCongr e n ≪≫ natTensorPowCongr g n
  | 0 => Iso.ext (Category.comp_id (𝟙 (𝟙_ C))).symm
  | n + 1 => by
      show natTensorPowCongr (e ≪≫ g) n ⊗ᵢ (e ≪≫ g) =
        (natTensorPowCongr e n ⊗ᵢ e) ≪≫ (natTensorPowCongr g n ⊗ᵢ g)
      rw [natTensorPowCongr_trans e g n]
      exact Iso.ext (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).symm

end Stacks.AmplePullbackPart1

namespace Stacks.AlgebraicGeometry.ProjTripleClassifying

open Stacks.AmplePullbackPart1 (natTensorPowCongr natTensorPowCongr_refl natTensorPowCongr_symm
  natTensorPowCongr_trans)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

section Evaluation

variable {Y : Scheme.{u}} {M M' M'' : Y.Modules}

/-- The identity morphism of an `𝒪_Y`-module acts as the identity on global sections. -/
private theorem id_app_top (z : Γ(M, ⊤)) : (𝟙 M : M ⟶ M).app ⊤ z = z := by
  simp [Scheme.Modules.Hom.id_app]

/-- A composite of morphisms of `𝒪_Y`-modules acts on global sections by acting twice. -/
private theorem comp_app_top (f : M ⟶ M') (g : M' ⟶ M'') (z : Γ(M, ⊤)) :
    (f ≫ g).app ⊤ z = g.app ⊤ (f.app ⊤ z) := by
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]

/-- The inverse of an isomorphism of `𝒪_Y`-modules undoes it on global sections. -/
private theorem inv_app_hom_app (e : M ≅ M') (z : Γ(M, ⊤)) :
    e.inv.app ⊤ (e.hom.app ⊤ z) = z := by
  rw [← comp_app_top, e.hom_inv_id, id_app_top]

end Evaluation

/-! ### The three clauses -/

variable {Y : Scheme.{u}} {d : ℕ} {L L' L'' : Y.Modules}

/-- Strict equivalence of weight-`d` graded maps is reflexive. -/
theorem sectionsEquiv_refl (ψ : VeroneseSections 𝒜 d L) : SectionsEquiv 𝒜 ψ ψ :=
  ⟨Iso.refl L, fun n x => by
    rw [natTensorPowCongr_refl n]
    exact id_app_top (ψ.toFun n x)⟩

/-- Strict equivalence of weight-`d` graded maps is symmetric. -/
theorem sectionsEquiv_symm {ψ : VeroneseSections 𝒜 d L} {ψ' : VeroneseSections 𝒜 d L'}
    (h : SectionsEquiv 𝒜 ψ ψ') : SectionsEquiv 𝒜 ψ' ψ := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨β.symm, fun n x => ?_⟩
  rw [natTensorPowCongr_symm, Iso.symm_hom, ← hβ n x]
  exact inv_app_hom_app _ _

/-- Strict equivalence of weight-`d` graded maps is transitive. -/
theorem sectionsEquiv_trans {ψ : VeroneseSections 𝒜 d L} {ψ' : VeroneseSections 𝒜 d L'}
    {ψ'' : VeroneseSections 𝒜 d L''} (h : SectionsEquiv 𝒜 ψ ψ')
    (h' : SectionsEquiv 𝒜 ψ' ψ'') : SectionsEquiv 𝒜 ψ ψ'' := by
  obtain ⟨β, hβ⟩ := h
  obtain ⟨γ, hγ⟩ := h'
  refine ⟨β ≪≫ γ, fun n x => ?_⟩
  rw [natTensorPowCongr_trans, Iso.trans_hom, comp_app_top, hβ n x]
  exact hγ n x

/-! ### The quotient -/

/-- A weight-`d` graded map on `Y`, together with the `𝒪_Y`-module it maps into. -/
def DegreeSections (d : ℕ) (Y : Scheme.{u}) : Type (u + 1) :=
  Σ L : Y.Modules, VeroneseSections 𝒜 d L

/-- Strict equivalence of weight-`d` graded maps, as an equivalence relation on
`DegreeSections 𝒜 d Y`.  The set `F_d(Y)` of [Stacks, Tag 01N4] is a quotient by it. -/
def sectionsSetoid (d : ℕ) (Y : Scheme.{u}) : Setoid (DegreeSections 𝒜 d Y) where
  r p q := SectionsEquiv 𝒜 p.2 q.2
  iseqv :=
    ⟨fun p => sectionsEquiv_refl 𝒜 p.2, fun h => sectionsEquiv_symm 𝒜 h,
      fun h h' => sectionsEquiv_trans 𝒜 h h'⟩

/-- The relation of `sectionsSetoid` is strict equivalence of the two graded maps. -/
theorem sectionsSetoid_r (p q : DegreeSections 𝒜 d Y) :
    (sectionsSetoid 𝒜 d Y).r p q ↔ SectionsEquiv 𝒜 p.2 q.2 :=
  Iff.rfl

/-- The weight-`d` graded map underlying a triple of weight `d`. -/
def Triple.degreeSections (t : Triple 𝒜 Y) : DegreeSections 𝒜 t.deg Y :=
  ⟨t.module, t.psi⟩

end Stacks.AlgebraicGeometry.ProjTripleClassifying

end
