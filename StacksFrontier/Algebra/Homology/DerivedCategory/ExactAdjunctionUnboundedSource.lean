module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived adjunction of an exact left adjoint, with an unbounded source

Let `L ⊣ R` be an adjunction between abelian categories `A` and `B` with enough injectives,
whose left adjoint `L` is exact. Then `L` acts on the unbounded derived categories, degreewise,
and the right adjoint has a total right derived functor `R⁺ : D⁺(B) ⥤ D⁺(A)` on the bounded
below derived categories. This file proves

`Hom_{D(B)}(L E, H) ≃ Hom_{D(A)}(E, R⁺ H)`

for *every* object `E` of the unbounded derived category `D(A)` and every bounded below object
`H` of `D⁺(B)`, the bijection being `a ↦ L(a) ≫ ε_H` with `ε` the counit of the adjunction
`L⁺ ⊣ R⁺` on `D⁺`. This is a form of Stacks 07A6.

## Main definitions

* `CategoryTheory.Adjunction.mapDerivedCategoryPlusAdjunction`: the adjunction `L⁺ ⊣ R⁺` on the
  bounded below derived categories, with `L⁺ = L.mapDerivedCategoryPlus`.
* `CategoryTheory.Adjunction.unboundedHomEquiv`: the bijection above.

## Main results

* `CategoryTheory.Adjunction.unboundedHomEquiv_symm_apply`: the bijection is `a ↦ L(a) ≫ ε_H`.
* `CategoryTheory.Adjunction.unboundedHomEquiv_naturality_left` and
  `CategoryTheory.Adjunction.unboundedHomEquiv_naturality_right`: its naturality in both
  variables.

## Implementation notes

The proof is a truncation argument. Choose `n` with both `H` and `R⁺ H` in `D^{≥ n}`, and let
`π : E ⟶ τ_{≥ n} E` be the truncation. Precomposition with `π` is a bijection onto morphisms
from `E` to any object of `D^{≥ n}` (`CategoryTheory.Triangulated.TStructure.descTruncGE`); and
precomposition with `L(π)` is a bijection onto morphisms from `L E` into `H`, because the cone
of `L(π)` is `L(τ_{< n} E)⟦1⟧` and `L`, being exact, keeps `τ_{< n} E` in `D^{≤ n - 1}`. Since
`τ_{≥ n} E` is bounded below, the adjunction on `D⁺` concludes.

## References

* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 07BE](https://stacks.math.columbia.edu/tag/07BE)
-/

@[expose] public noncomputable section

universe vA uA vB uB wA wB

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

variable {C : Type uA} [Category.{vA} C] [Abelian C] [HasDerivedCategory.{wA} C]
  {D : Type uB} [Category.{vB} D] [Abelian D] [HasDerivedCategory.{wB} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **An exact functor preserves boundedness above.** Its action on the derived category
commutes with cohomology, so the degrees in which the cohomology vanishes are unchanged. -/
theorem isLE_obj_mapDerivedCategory (X : DerivedCategory C) (n : ℤ) (hX : X.IsLE n) :
    (F.mapDerivedCategory.obj X).IsLE n := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact (F.map_isZero ((DerivedCategory.isLE_iff X n).1 hX i hi)).of_iso
    ((F.mapDerivedCategoryHomologyIso i).app X)

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  [EnoughInjectives A] [EnoughInjectives B]
  {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive] [PreservesFiniteLimits L]
  [PreservesFiniteColimits L] (adj : L ⊣ R)

/-- **The derived adjunction on bounded below derived categories, for an exact left adjoint.**
The induced functor `L⁺ = L.mapDerivedCategoryPlus` is left adjoint to the total right derived
functor `R⁺` of the right adjoint. This is `CategoryTheory.Adjunction.rightDerivedFunctorPlus`
transported along the identification of the right derived functor of the exact functor `L` with
`L⁺`. -/
@[sga "4 V 2.2" "more general"]
def mapDerivedCategoryPlusAdjunction :
    L.mapDerivedCategoryPlus ⊣ R.rightDerivedFunctorPlus :=
  adj.rightDerivedFunctorPlus.ofNatIsoLeft L.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus

/-- The counit `L(R⁺ H) ⟶ H` of the adjunction `L⁺ ⊣ R⁺`, read in the unbounded derived
category `D(B)`. -/
def plusCounit (H : DerivedCategory.Plus B) :
    L.mapDerivedCategory.obj (R.rightDerivedFunctorPlus.obj H).obj ⟶ H.obj :=
  ((mapDerivedCategoryPlusAdjunction adj).counit.app H).hom

/-- Naturality of `CategoryTheory.Adjunction.plusCounit`: for `h : H ⟶ H'` in `D⁺(B)`,
`L(R⁺ h) ≫ ε_{H'} = ε_H ≫ h`. -/
@[reassoc]
theorem plusCounit_naturality {H H' : DerivedCategory.Plus B} (h : H ⟶ H') :
    L.mapDerivedCategory.map (R.rightDerivedFunctorPlus.map h).hom ≫ plusCounit adj H' =
      plusCounit adj H ≫ h.hom :=
  congrArg InducedCategory.Hom.hom ((mapDerivedCategoryPlusAdjunction adj).counit.naturality h)

/-- The inverse of the hom-equivalence of the adjunction `L⁺ ⊣ R⁺` sends `g : X ⟶ R⁺ H` to
`L(g)` followed by the counit `CategoryTheory.Adjunction.plusCounit`. -/
theorem homEquiv_symm_hom (X : DerivedCategory.Plus A) (H : DerivedCategory.Plus B)
    (g : X ⟶ R.rightDerivedFunctorPlus.obj H) :
    (((mapDerivedCategoryPlusAdjunction adj).homEquiv X H).symm g).hom =
      L.mapDerivedCategory.map g.hom ≫ plusCounit adj H :=
  congrArg InducedCategory.Hom.hom ((mapDerivedCategoryPlusAdjunction adj).homEquiv_counit X H g)

/-- The map underlying `CategoryTheory.Adjunction.unboundedHomEquiv`: a morphism
`a : E ⟶ R⁺ H` goes to `L(a)` followed by the counit of the adjunction on `D⁺`. -/
def unboundedHomMap (E : DerivedCategory A) (H : DerivedCategory.Plus B)
    (a : E ⟶ (R.rightDerivedFunctorPlus.obj H).obj) :
    L.mapDerivedCategory.obj E ⟶ H.obj :=
  L.mapDerivedCategory.map a ≫ plusCounit adj H

omit [EnoughInjectives A] [EnoughInjectives B] in
/-- Precomposition with `L` of a truncation map `π : E ⟶ τ_{≥ n} E` is a bijection onto the
morphisms from `L E` into an object of `D^{≥ n}`. -/
theorem bijective_precomp_map_truncGEπ (E : DerivedCategory A) (Y : DerivedCategory B) (n : ℤ)
    [Y.IsGE n] :
    Function.Bijective fun c : L.mapDerivedCategory.obj
        ((DerivedCategory.TStructure.t.truncGE n).obj E) ⟶ Y =>
      L.mapDerivedCategory.map ((DerivedCategory.TStructure.t.truncGEπ n).app E) ≫ c := by
  let t := (DerivedCategory.TStructure.t : Triangulated.TStructure (DerivedCategory A))
  let T := L.mapDerivedCategory.mapTriangle.obj ((t.triangleLTGE n).obj E)
  have hT : T ∈ distTriang _ :=
    L.mapDerivedCategory.map_distinguished _ (t.triangleLTGE_distinguished n E)
  have h₁ : (T.obj₁).IsLE (n - 1) :=
    L.isLE_obj_mapDerivedCategory _ (n - 1) (inferInstanceAs (t.IsLE _ (n - 1)))
  have h₁' : DerivedCategory.TStructure.t.IsLE ((T.obj₁)⟦(1 : ℤ)⟧) (n - 2) :=
    DerivedCategory.TStructure.t.isLE_shift _ (n - 1) 1 (n - 2) (by lia)
  constructor
  · intro c₁ c₂ hc
    suffices ∀ c : L.mapDerivedCategory.obj ((t.truncGE n).obj E) ⟶ Y,
        L.mapDerivedCategory.map ((t.truncGEπ n).app E) ≫ c = 0 → c = 0 by
      rw [← sub_eq_zero]
      exact this _ ((Preadditive.comp_sub _ _ _).trans (sub_eq_zero.2 hc))
    intro c hc
    obtain ⟨g, rfl⟩ := Triangle.yoneda_exact₃ T hT c hc
    exact (congrArg (T.mor₃ ≫ ·) (DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g (n - 2) n
      (by lia) h₁' inferInstance)).trans comp_zero
  · intro g
    obtain ⟨c, hc⟩ := Triangle.yoneda_exact₂ T hT g
      (DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ (n - 1) n (by lia) h₁ inferInstance)
    exact ⟨c, hc.symm⟩

/-- Precomposition with a truncation map `π : E ⟶ τ_{≥ n} E` is a bijection onto the morphisms
from `E` into an object of `D^{≥ n}`. -/
theorem bijective_precomp_truncGEπ {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (t : Triangulated.TStructure C) (E Y : C) (n : ℤ) [t.IsGE Y n] :
    Function.Bijective fun c : (t.truncGE n).obj E ⟶ Y => (t.truncGEπ n).app E ≫ c :=
  ⟨fun _ _ h => t.from_truncGE_obj_ext h, fun f => ⟨t.descTruncGE f n, t.π_descTruncGE f n⟩⟩

/-- The map `a ↦ L(a) ≫ ε_H` from `E ⟶ R⁺ H` to `L E ⟶ H` is a bijection. -/
theorem bijective_unboundedHomMap (E : DerivedCategory A) (H : DerivedCategory.Plus B) :
    Function.Bijective (unboundedHomMap adj E H) := by
  obtain ⟨n₁, h₁⟩ := H.property
  obtain ⟨n₂, h₂⟩ := (R.rightDerivedFunctorPlus.obj H).property
  let n := min n₁ n₂
  have hH : H.obj.IsGE n :=
    DerivedCategory.TStructure.t.isGE_of_ge _ n n₁ (min_le_left _ _)
  have hRH : (R.rightDerivedFunctorPlus.obj H).obj.IsGE n :=
    DerivedCategory.TStructure.t.isGE_of_ge _ n n₂ (min_le_right _ _)
  let t := (DerivedCategory.TStructure.t : Triangulated.TStructure (DerivedCategory A))
  let X : DerivedCategory.Plus A := ⟨(t.truncGE n).obj E, ⟨n, inferInstance⟩⟩
  let adj' := mapDerivedCategoryPlusAdjunction adj
  have hΦ₁ := bijective_precomp_truncGEπ t E (R.rightDerivedFunctorPlus.obj H).obj n
  let Φ₂ : ((t.truncGE n).obj E ⟶ (R.rightDerivedFunctorPlus.obj H).obj) →
      (L.mapDerivedCategory.obj ((t.truncGE n).obj E) ⟶ H.obj) := fun b =>
    ((adj'.homEquiv X H).symm (ObjectProperty.homMk b)).hom
  have hΦ₂ : Function.Bijective Φ₂ :=
    ⟨fun _ _ h => congrArg InducedCategory.Hom.hom
        ((adj'.homEquiv X H).symm.injective (ObjectProperty.hom_ext _ h)),
      fun c => ⟨(adj'.homEquiv X H (ObjectProperty.homMk c)).hom,
        congrArg InducedCategory.Hom.hom ((adj'.homEquiv X H).symm_apply_apply _)⟩⟩
  have key : unboundedHomMap adj E H ∘ (fun c => (t.truncGEπ n).app E ≫ c) =
      (fun c => L.mapDerivedCategory.map ((t.truncGEπ n).app E) ≫ c) ∘ Φ₂ := by
    funext b
    change L.mapDerivedCategory.map ((t.truncGEπ n).app E ≫ b) ≫ plusCounit adj H =
      L.mapDerivedCategory.map ((t.truncGEπ n).app E) ≫
        ((adj'.homEquiv X H).symm (ObjectProperty.homMk b)).hom
    rw [homEquiv_symm_hom, Functor.map_comp, Category.assoc]
    rfl
  have := (bijective_precomp_map_truncGEπ (L := L) E H.obj n).comp hΦ₂
  rw [← key] at this
  exact (Function.Bijective.of_comp_iff _ hΦ₁).1 this

/-- **Stacks 07A6 for an exact left adjoint, with an unbounded source.** For an adjunction
`L ⊣ R` of abelian categories with enough injectives whose left adjoint is exact,

`Hom_{D(B)}(L E, H) ≃ Hom_{D(A)}(E, R⁺ H)`

for every object `E` of the unbounded derived category `D(A)` and every object `H` of the
bounded below derived category `D⁺(B)`. -/
def unboundedHomEquiv (E : DerivedCategory A) (H : DerivedCategory.Plus B) :
    (L.mapDerivedCategory.obj E ⟶ H.obj) ≃ (E ⟶ (R.rightDerivedFunctorPlus.obj H).obj) :=
  (Equiv.ofBijective _ (bijective_unboundedHomMap adj E H)).symm

/-- The inverse of `CategoryTheory.Adjunction.unboundedHomEquiv` sends `a : E ⟶ R⁺ H` to
`L(a) ≫ ε_H`. -/
theorem unboundedHomEquiv_symm_apply (E : DerivedCategory A) (H : DerivedCategory.Plus B)
    (a : E ⟶ (R.rightDerivedFunctorPlus.obj H).obj) :
    (unboundedHomEquiv adj E H).symm a =
      L.mapDerivedCategory.map a ≫ plusCounit adj H :=
  rfl

/-- Naturality of `CategoryTheory.Adjunction.unboundedHomEquiv` in the unbounded variable. -/
theorem unboundedHomEquiv_naturality_left {E E' : DerivedCategory A} (e : E' ⟶ E)
    (H : DerivedCategory.Plus B) (g : L.mapDerivedCategory.obj E ⟶ H.obj) :
    unboundedHomEquiv adj E' H (L.mapDerivedCategory.map e ≫ g) =
      e ≫ unboundedHomEquiv adj E H g := by
  apply (unboundedHomEquiv adj E' H).symm.injective
  rw [Equiv.symm_apply_apply, unboundedHomEquiv_symm_apply, Functor.map_comp, Category.assoc,
    ← unboundedHomEquiv_symm_apply, Equiv.symm_apply_apply]

/-- Naturality of `CategoryTheory.Adjunction.unboundedHomEquiv` in the bounded below
variable. -/
theorem unboundedHomEquiv_naturality_right (E : DerivedCategory A) {H H' : DerivedCategory.Plus B}
    (h : H ⟶ H') (g : L.mapDerivedCategory.obj E ⟶ H.obj) :
    unboundedHomEquiv adj E H' (g ≫ h.hom) =
      unboundedHomEquiv adj E H g ≫ (R.rightDerivedFunctorPlus.map h).hom := by
  apply (unboundedHomEquiv adj E H').symm.injective
  rw [Equiv.symm_apply_apply, unboundedHomEquiv_symm_apply, Functor.map_comp, Category.assoc,
    plusCounit_naturality, ← Category.assoc, ← unboundedHomEquiv_symm_apply,
    Equiv.symm_apply_apply]

end CategoryTheory.Adjunction
