module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.AltProjectorFreeSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.MatrixUnitCombination
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.PullbackExactDescent

/-!
# The matrix dictionary of a finite free sheaf of modules under pullback

Let `ρ : V ⟶ T` be a morphism of schemes, write `F = ρ^*` for the pullback of sheaves of
modules (`Stacks.EtaleCohomology.BrauerScheme.modulePullback`), and let
`Φ I : F (𝒪_T^{(I)}) ≅ 𝒪_V^{(I)}` be the identification of the pullback of a free sheaf of
modules with the free sheaf of modules
(`Stacks.EtaleCohomology.BrauerScheme.modulePullbackFreeIso`). The endomorphisms of a finite
free sheaf of `𝒪_T`-modules are square matrices over the commutative ring
`R₀ T = End (𝟙_ (ModuleSheaf T))` of endomorphisms of the structure sheaf, by the dual basis
dictionary `Stacks.EtaleCohomology.BrauerScheme.freeDualMatrix`. This file says what the pullback
does to that dictionary: **it is entrywise base change along a ring homomorphism
`R₀ T →+* R₀ V`**, and nothing else.

The ring homomorphism is `unitEndPullbackHom ρ`. On an endomorphism `a` of `𝒪_T` it is the
conjugate `ε ≫ ρ^* a ≫ ε⁻¹` of `ρ^* a` by the structure-sheaf comparison `ε : 𝒪_V ≅ ρ^* 𝒪_T` of
[Stacks, Tag 01CD], which is the unit of the monoidal structure of `ρ^*`
(`Stacks.EtaleCohomology.BrauerScheme.monoidalModulePullback`). It is multiplicative because the
multiplication of `End (𝟙_ C)` is composition
(`CategoryTheory.MonoidalCategory.unitEnd_mul_eq_comp`) and the two copies of the comparison in a
product cancel, and additive because `ρ^*` is a left adjoint between preadditive categories,
hence additive.

That `Φ` matches the dictionaries is the content of two statements about the tautological dual
basis. The tautological point `freeInj i : 𝒪_T ⟶ 𝒪_T^{(I)}` is carried by `ρ^*`, up to the
comparison at the unit, to the tautological point of `𝒪_V^{(I)}`; this is Mathlib's
`CategoryTheory.SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom`, whose right-hand
side `pullbackObjUnitToUnit` is exactly the inverse of the comparison, so composing with `ε`
leaves `freeInj i` alone. The tautological coordinate `freeProj j` has no description beyond its
pairing with the points, so the dual statement is proved by the extensionality principle
`Stacks.EtaleCohomology.BrauerScheme.freeModule_hom_ext_inj`: pairing the conjugate of
`ρ^* (freeProj j)` with `freeInj i` turns it into `unitEndPullbackHom ρ` applied to
`freeInj i ≫ freeProj j`, which is `1` or `0`, and a ring homomorphism preserves both.

Conjugating an endomorphism `g` by `Φ I` therefore replaces the `(a, b)` entry
`freeInj a ≫ g ≫ freeProj b` by its image under `unitEndPullbackHom ρ`. Two consequences follow
by injectivity of the dictionary, and they are the reason the file exists: the alternating
projector `altProjFree` of [Stacks, Tag 0A2L] and the matrix units `matIncl` of the matrix
algebra sheaf are both given by formulas with integer coefficients, so each is carried to its
counterpart on `V`. In other words the trivialisation of a matrix algebra sheaf that `Φ`
provides is compatible with the projector and with the matrix units, which is what lets the
rank computation of Tag 0A2L be made on a refinement of the étale covering.

## Main definitions

* `Stacks.EtaleCohomology.BrauerScheme.unitEndPullbackHom`: **the ring homomorphism
  `R₀ T →+* R₀ V` induced on the endomorphisms of the structure sheaf** by a morphism of
  schemes `ρ : V ⟶ T`.

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.epsilon_comp_map_freeInj` and
  `Stacks.EtaleCohomology.BrauerScheme.modulePullbackFreeIso_inv_comp_map_freeProj`: **the
  tautological points and coordinates of a finite free sheaf of modules are preserved** by the
  pullback, read through `modulePullbackFreeIso` and the comparison at the unit.
* `Stacks.EtaleCohomology.BrauerScheme.freeDualMatrix_conj_modulePullbackFreeIso`: **the matrix
  of a conjugated endomorphism is the matrix mapped along `unitEndPullbackHom`.**
* `Stacks.EtaleCohomology.BrauerScheme.conj_modulePullbackFreeIso_altProjFree`: **the pullback
  of the alternating projector of [Stacks, Tag 0A2L] is the alternating projector.**
* `Stacks.EtaleCohomology.BrauerScheme.conj_modulePullbackFreeIso_uncurry'_matIncl`: **the
  pullback of a matrix unit is that matrix unit.**

## Implementation notes

**The comparison at the unit is spelled three ways** and the three are equal by `rfl`:
`CategoryTheory.Functor.LaxMonoidal.ε (modulePullback ρ)` is the inverse of
`Stacks.PullbackTensorCoherence.pullbackUnitComparison` by
`Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal_epsilon`, and that comparison is
`CategoryTheory.SheafOfModules.pullbackObjUnitToUnit` at the structure-sheaf morphism of `ρ`,
which is the morphism Mathlib's statement about free sheaves is phrased with. The proof of
`epsilon_comp_map_freeInj` therefore quotes Mathlib's lemma at the spelling
`CategoryTheory.Functor.OplaxMonoidal.η (modulePullback ρ)` — the `.inv` of
`CategoryTheory.Functor.Monoidal.εIso` — and finishes with `CategoryTheory.Functor.Monoidal.ε_η`.
The finality instance needed to state Mathlib's lemma is the one
`Stacks.EtaleCohomology.BrauerScheme.modulePullbackFreeIso` supplies for itself; `Final` is a
`Prop`, so there is no question of two different instances disagreeing.

**Why two of the ring homomorphism laws are applications of abstract lemmas.** A goal mentioning
`freeModule S I` or `𝟙_ (ModuleSheaf S)` carries `Stacks.SheafOfModules.Tensor.ringSheaf S.sheaf`,
whose argument fits only after `TopCat.Sheaf` is unfolded, and that unfolding is unavailable at
the `implicit` transparency `rw` and `simp` check their motives at. Rewriting with
`CategoryTheory.Functor.map_id` and `CategoryTheory.Functor.map_add` is refused there, so
`CategoryTheory.MonoidalCategory.epsilon_comp_map_id_comp_epsilonIso_inv` and
`CategoryTheory.MonoidalCategory.epsilon_comp_map_add_comp_epsilonIso_inv` state those two
computations for an abstract monoidal functor, where everything rewrites, and the corresponding
fields of `unitEndPullbackHom` are applications of them. For the same reason the matrix identity
`freeDualMatrix_conj_modulePullbackFreeIso` opens with a `show` that puts the goal in the form of
a morphism identity — the dual basis matrix, the entrywise map and the ring homomorphism all
unfold by `rfl` — rather than unfolding the dictionary with `simp`. This is the convention of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.AltProjectorFreeSheaf` and of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.EndAlgebraFreePoints`.

**`HasFiniteBiproducts (ModuleSheaf S)` and `MonoidalPreadditive (ModuleSheaf S)`** are
re-enabled from `MatrixFreeSheaf` with `attribute [local instance]` rather than restated: the two
declarations there are `local instance`s, hence ordinary declarations downstream, and restating
them collides. This is the convention of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.AltProjectorFreeSheaf`.

## References

* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules

universe u

noncomputable section

namespace CategoryTheory.MonoidalCategory

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]

/-- **Conjugating the identity of the monoidal unit by the unit comparison of a monoidal functor
gives the identity.** This is the `map_one` of
`Stacks.EtaleCohomology.BrauerScheme.unitEndPullbackHom`, stated for an abstract monoidal functor
because the scheme-level statement cannot be rewritten in — see the implementation notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.FreeSheafPullbackMatrix`. -/
lemma epsilon_comp_map_id_comp_epsilonIso_inv (F : C ⥤ D) [F.Monoidal] :
    Functor.LaxMonoidal.ε F ≫ F.map (𝟙 (𝟙_ C)) ≫ (Functor.Monoidal.εIso F).inv = 𝟙 (𝟙_ D) := by
  simp only [Functor.map_id, Category.id_comp, Functor.Monoidal.εIso_inv, Functor.Monoidal.ε_η]

/-- **Conjugating an endomorphism of the monoidal unit by the unit comparison of an additive
monoidal functor is additive.** This is the `map_add` of
`Stacks.EtaleCohomology.BrauerScheme.unitEndPullbackHom`, stated for an abstract monoidal functor
for the same reason as `epsilon_comp_map_id_comp_epsilonIso_inv`. -/
lemma epsilon_comp_map_add_comp_epsilonIso_inv [Preadditive C] [Preadditive D] (F : C ⥤ D)
    [F.Monoidal] [F.Additive] (a b : 𝟙_ C ⟶ 𝟙_ C) :
    Functor.LaxMonoidal.ε F ≫ F.map (a + b) ≫ (Functor.Monoidal.εIso F).inv
      = Functor.LaxMonoidal.ε F ≫ F.map a ≫ (Functor.Monoidal.εIso F).inv +
        Functor.LaxMonoidal.ε F ≫ F.map b ≫ (Functor.Monoidal.εIso F).inv := by
  simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

end CategoryTheory.MonoidalCategory

namespace Stacks.EtaleCohomology.BrauerScheme

attribute [local instance] hasFiniteBiproductsModuleSheaf monoidalPreadditiveModuleSheaf

variable {V T : Scheme.{u}}

/-! ### The ring homomorphism on the endomorphisms of the structure sheaf -/

/-- **The pullback of sheaves of modules along a morphism of schemes is additive.** It is a left
adjoint — the right adjoint is the pushforward — and a left adjoint of an additive functor
between preadditive categories is additive. This is
`Stacks.RingedSpaceModuleAdjunction.modulePullback_additive` at the spelling of this
namespace. -/
theorem additive_modulePullback (ρ : V ⟶ T) : (modulePullback ρ).Additive :=
  RingedSpaceModuleAdjunction.modulePullback_additive ρ.toLRSHom.toShHom

/-- **The ring homomorphism `R₀ T →+* R₀ V` induced by a morphism of schemes `ρ : V ⟶ T`** on the
endomorphisms of the structure sheaf: an endomorphism `a` of `𝒪_T` is sent to the conjugate of
`ρ^* a` by the structure-sheaf comparison `𝒪_V ≅ ρ^* 𝒪_T` of [Stacks, Tag 01CD], which is the
unit of the monoidal structure of `ρ^*`.

It is multiplicative because the multiplication of `End (𝟙_ C)` is composition
(`CategoryTheory.MonoidalCategory.unitEnd_mul_eq_comp`), so the two inner copies of the
comparison cancel, and additive by `additive_modulePullback`. This is the ring homomorphism the
matrix dictionary of a finite free sheaf of modules base changes along. -/
def unitEndPullbackHom (ρ : V ⟶ T) : R₀ T →+* R₀ V where
  toFun a := Functor.LaxMonoidal.ε (modulePullback ρ) ≫ (modulePullback ρ).map a ≫
    (Functor.Monoidal.εIso (modulePullback ρ)).inv
  map_one' :=
    CategoryTheory.MonoidalCategory.epsilon_comp_map_id_comp_epsilonIso_inv (modulePullback ρ)
  map_mul' a b := by
    simp only [CategoryTheory.MonoidalCategory.unitEnd_mul_eq_comp, Functor.map_comp,
      Functor.Monoidal.εIso_inv, Category.assoc, Functor.Monoidal.η_ε_assoc]
  map_zero' := by
    let := additive_modulePullback ρ
    simp only [Functor.map_zero, Limits.zero_comp, Limits.comp_zero]
  map_add' a b :=
    letI := additive_modulePullback ρ
    CategoryTheory.MonoidalCategory.epsilon_comp_map_add_comp_epsilonIso_inv
      (modulePullback ρ) a b

/-- `unitEndPullbackHom` is conjugation of the pullback by the comparison at the unit, by
definition. -/
theorem unitEndPullbackHom_apply (ρ : V ⟶ T) (a : R₀ T) :
    unitEndPullbackHom ρ a = Functor.LaxMonoidal.ε (modulePullback ρ) ≫
      (modulePullback ρ).map a ≫ (Functor.Monoidal.εIso (modulePullback ρ)).inv :=
  rfl

/-! ### The tautological dual basis under pullback -/

/-- **The tautological points of a finite free sheaf of modules are preserved by the pullback**:
`ρ^*` carries `freeInj i` to `freeInj i`, read through `modulePullbackFreeIso` and the
structure-sheaf comparison at the unit.

This is Mathlib's
`CategoryTheory.SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom`, whose right-hand
side is `CategoryTheory.SheafOfModules.pullbackObjUnitToUnit` followed by the tautological point;
that morphism is the inverse of the comparison, so composing with the comparison leaves the
tautological point alone. -/
theorem epsilon_comp_map_freeInj (ρ : V ⟶ T) (I : Type u) (i : I) :
    Functor.LaxMonoidal.ε (modulePullback ρ) ≫ (modulePullback ρ).map (freeInj (S := T) i) ≫
        (modulePullbackFreeIso ρ I).hom
      = freeInj (S := V) i := by
  have : (RingedSpaceModuleAdjunction.opensMap ρ.toLRSHom.toShHom).Final :=
    CategoryTheory.final_of_representablyFlat _
  have h : (modulePullback ρ).map (freeInj (S := T) i) ≫ (modulePullbackFreeIso ρ I).hom
      = Functor.OplaxMonoidal.η (modulePullback ρ) ≫ freeInj (S := V) i :=
    SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom
      (RingedSpaceModuleAdjunction.structureSheafHom ρ.toLRSHom.toShHom) i
  rw [h, ← Category.assoc, Functor.Monoidal.ε_η, Category.id_comp]

/-- `epsilon_comp_map_freeInj` with the identification of the pullback of the free sheaf moved to
the other side: the tautological point of `𝒪_V^{(I)}`, followed by the inverse of that
identification, is the pullback of the tautological point of `𝒪_T^{(I)}`. -/
@[reassoc]
theorem freeInj_comp_modulePullbackFreeIso_inv (ρ : V ⟶ T) (I : Type u) (i : I) :
    freeInj (S := V) i ≫ (modulePullbackFreeIso ρ I).inv
      = Functor.LaxMonoidal.ε (modulePullback ρ) ≫
        (modulePullback ρ).map (freeInj (S := T) i) := by
  rw [← epsilon_comp_map_freeInj ρ I i]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The tautological coordinates of a finite free sheaf of modules are preserved by the
pullback**: `ρ^*` carries `freeProj j` to `freeProj j`, read through `modulePullbackFreeIso` and
the structure-sheaf comparison at the unit.

A tautological coordinate is characterised only by its pairings with the tautological points, so
this is proved by the extensionality principle `freeModule_hom_ext_inj`: pairing the left-hand
side with `freeInj i` and using `freeInj_comp_modulePullbackFreeIso_inv` turns it into
`unitEndPullbackHom ρ` applied to `freeInj i ≫ freeProj j`, which is `1` or `0` by
`freeInj_comp_freeProj`, and a ring homomorphism preserves both. -/
theorem modulePullbackFreeIso_inv_comp_map_freeProj (ρ : V ⟶ T) (I : Type u) [DecidableEq I]
    (j : I) :
    (modulePullbackFreeIso ρ I).inv ≫ (modulePullback ρ).map (freeProj (S := T) j) ≫
        (Functor.Monoidal.εIso (modulePullback ρ)).inv
      = freeProj (S := V) j := by
  refine freeModule_hom_ext_inj fun i => ?_
  rw [freeInj_comp_modulePullbackFreeIso_inv_assoc, ← Functor.map_comp_assoc,
    freeInj_comp_freeProj, freeInj_comp_freeProj, ← unitEndPullbackHom_apply]
  split_ifs with h
  · exact map_one (unitEndPullbackHom ρ)
  · exact map_zero (unitEndPullbackHom ρ)

/-- `modulePullbackFreeIso_inv_comp_map_freeProj` with the identification of the pullback of the
free sheaf moved to the other side: the identification followed by the tautological coordinate of
`𝒪_V^{(I)}` is the pullback of the tautological coordinate of `𝒪_T^{(I)}`, followed by the
comparison at the unit. -/
@[reassoc]
theorem modulePullbackFreeIso_hom_comp_freeProj (ρ : V ⟶ T) (I : Type u) [DecidableEq I] (j : I) :
    (modulePullbackFreeIso ρ I).hom ≫ freeProj (S := V) j
      = (modulePullback ρ).map (freeProj (S := T) j) ≫
        (Functor.Monoidal.εIso (modulePullback ρ)).inv := by
  rw [← modulePullbackFreeIso_inv_comp_map_freeProj ρ I j, ← Category.assoc, Iso.hom_inv_id,
    Category.id_comp]

/-! ### The matrix of a conjugated endomorphism -/

/-- **The matrix of a conjugated endomorphism is the matrix mapped along the ring homomorphism
on the endomorphisms of the structure sheaf.** Conjugating `ρ^* g` by `modulePullbackFreeIso`
gives an endomorphism of the free sheaf of `𝒪_V`-modules on `I` whose dual basis matrix is the
entrywise image of the dual basis matrix of `g` under `unitEndPullbackHom ρ`.

This is the whole dictionary: the `(a, b)` entry of the left-hand side is
`freeInj a ≫ (Φ⁻¹ ≫ ρ^* g ≫ Φ) ≫ freeProj b`, and the two statements about the tautological dual
basis turn it into `ε ≫ ρ^* (freeInj a ≫ g ≫ freeProj b) ≫ ε⁻¹`, which is `unitEndPullbackHom ρ`
applied to the `(a, b)` entry of the matrix of `g`. -/
theorem freeDualMatrix_conj_modulePullbackFreeIso (ρ : V ⟶ T) {I : Type u} [Fintype I]
    [DecidableEq I] (g : freeModule T I ⟶ freeModule T I) :
    freeDualMatrix ((modulePullbackFreeIso ρ I).inv ≫ (modulePullback ρ).map g ≫
        (modulePullbackFreeIso ρ I).hom)
      = (freeDualMatrix g).map (unitEndPullbackHom ρ) := by
  ext a b
  show freeInj (S := V) a ≫ ((modulePullbackFreeIso ρ I).inv ≫ (modulePullback ρ).map g ≫
        (modulePullbackFreeIso ρ I).hom) ≫ freeProj (S := V) b
      = Functor.LaxMonoidal.ε (modulePullback ρ) ≫
        (modulePullback ρ).map (freeInj (S := T) a ≫ g ≫ freeProj (S := T) b) ≫
        (Functor.Monoidal.εIso (modulePullback ρ)).inv
  simp only [Category.assoc, Functor.map_comp, freeInj_comp_modulePullbackFreeIso_inv_assoc,
    modulePullbackFreeIso_hom_comp_freeProj]

/-! ### The alternating projector and the matrix units under pullback -/

/-- **The pullback of the alternating projector of [Stacks, Tag 0A2L] is the alternating
projector.** The matrix of `altProjFree T d` is `Matrix.altProj (R₀ T)`, a formula with integer
coefficients, so `Matrix.map_altProj` identifies its image under `unitEndPullbackHom ρ` with
`Matrix.altProj (R₀ V)`; the conclusion follows because the dual basis dictionary is
injective. -/
theorem conj_modulePullbackFreeIso_altProjFree (ρ : V ⟶ T) (d : ℕ) :
    (modulePullbackFreeIso ρ (ULift.{u, 0} (Fin d → Fin d))).inv ≫
        (modulePullback ρ).map (altProjFree T d) ≫
        (modulePullbackFreeIso ρ (ULift.{u, 0} (Fin d → Fin d))).hom
      = altProjFree V d := by
  refine freeDualMatrix_injective ?_
  rw [freeDualMatrix_conj_modulePullbackFreeIso]
  ext k l
  rw [Matrix.map_apply, freeDualMatrix_altProjFree, freeDualMatrix_altProjFree]
  exact congrFun (congrFun (Matrix.map_altProj (n := Fin d) (unitEndPullbackHom ρ)) k.down) l.down

/-- **The pullback of a matrix unit of the matrix algebra sheaf is that matrix unit.** The matrix
of the `(a, b)` matrix unit is `Matrix.single a b 1`, and a ring homomorphism carries
`Matrix.single a b 1` to `Matrix.single a b 1`; the conclusion follows because the dual basis
dictionary is injective. -/
theorem conj_modulePullbackFreeIso_uncurry'_matIncl (ρ : V ⟶ T) {I : Type u} [Fintype I]
    [DecidableEq I] (k : I × I) :
    (modulePullbackFreeIso ρ I).inv ≫
        (modulePullback ρ).map (MonoidalClosed.uncurry' (matIncl (S := T) k)) ≫
        (modulePullbackFreeIso ρ I).hom
      = MonoidalClosed.uncurry' (matIncl (S := V) k) := by
  obtain ⟨a, b⟩ := k
  refine freeDualMatrix_injective ?_
  rw [freeDualMatrix_conj_modulePullbackFreeIso, freeDualMatrix_uncurry'_matIncl,
    freeDualMatrix_uncurry'_matIncl, Matrix.map_single, map_one]

end Stacks.EtaleCohomology.BrauerScheme

end

end
