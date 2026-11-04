module

public import StacksFrontier.AlgebraicGeometry.Perfect.QcqsPerfectGenerator
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPseudoCoherentHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualLeftDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomothetyCriteria

/-!
# Invertibility of the homothety from morphisms out of perfect objects

Let `X` be a quasi-compact and quasi-separated scheme and `W` a pseudo-coherent, bounded below
object of `D(𝒪_X)`. The homothety `𝒪_X ⟶ R𝓗om_{𝒪_X}(W, W)` is an isomorphism as soon as, for
every perfect object `E`, the map `Hom(E, 𝒪_X) ⟶ Hom(E ⊗^L W, W)`, `g ↦ g ⊗ 1_W` followed by the
unit constraint, is bijective. This is the Yoneda step of the proof of [Stacks, Tag 0E4L] (3):
`R𝓗om(W, W)` lies in `D_QCoh(𝒪_X)` by [Stacks, Tag 0A6H] (1), so the cone of the homothety does,
it receives no nonzero map from a perfect object, and the perfect objects generate `D_QCoh(𝒪_X)`
([Stacks, Tag 09IS]).

The hypothesis is reached from any family of bijections `Hom(E, 𝒪_X) ≃ Hom(E ⊗^L W, W)` natural
along the maps `E ⟶ 𝒪_X`: such a family differs from the one above by an automorphism of `W`.
That is a statement about an arbitrary monoidal category.

## Main results

* `CategoryTheory.MonoidalCategory.bijective_whiskerRight_comp_leftUnitor_of_equiv` — a family of
  bijections `(E ⟶ 𝟙) ≃ (E ⊗ W ⟶ W)` natural along the maps `E ⟶ 𝟙`, on a class of objects
  containing `𝟙`, makes `g ↦ g ▷ W ≫ λ_W` bijective on that class.
* `Stacks.Duality.StandardModel.isIso_derivedSheafHomothety_of_bijective` — the criterion above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

universe v u

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- **A family of bijections `(E ⟶ 𝟙) ≃ (E ⊗ W ⟶ W)` natural along the maps into the unit is
the canonical one up to an automorphism of `W`.** Let `S` be a class of objects containing `𝟙_ C`
and suppose given, for `E` in `S`, bijections `Φ E : (E ⟶ 𝟙_ C) ≃ (E ⊗ W ⟶ W)` with
`Φ E g = g ▷ W ≫ Φ (𝟙_ C) (𝟙 _)`. Then `g ↦ g ▷ W ≫ λ_W` is bijective on every `E` in `S`.

Writing `Φ (𝟙_ C) (𝟙 _) = λ_W ≫ φ`, surjectivity at `𝟙_ C` gives a scalar `g₀` with
`μ(g₀) ≫ φ = 𝟙`, where `μ(g₀) = λ_W⁻¹ ≫ g₀ ▷ W ≫ λ_W`; scalars commute with endomorphisms of `W`,
so `φ` is invertible, and `g ▷ W ≫ λ_W = Φ E g ≫ μ(g₀)`. -/
theorem bijective_whiskerRight_comp_leftUnitor_of_equiv (S : C → Prop) (hS : S (𝟙_ C)) (W : C)
    (Φ : ∀ E : C, S E → ((E ⟶ 𝟙_ C) ≃ (E ⊗ W ⟶ W)))
    (hΦ : ∀ (E : C) (hE : S E) (g : E ⟶ 𝟙_ C), Φ E hE g = g ▷ W ≫ Φ (𝟙_ C) hS (𝟙 _))
    (E : C) (hE : S E) :
    Function.Bijective fun g : E ⟶ 𝟙_ C => g ▷ W ≫ (λ_ W).hom := by
  set φ : W ⟶ W := (λ_ W).inv ≫ Φ (𝟙_ C) hS (𝟙 _) with hφ
  have hc : Φ (𝟙_ C) hS (𝟙 _) = (λ_ W).hom ≫ φ := by simp [hφ]
  obtain ⟨g₀, hg₀⟩ := (Φ (𝟙_ C) hS).surjective (λ_ W).hom
  set μ : W ⟶ W := (λ_ W).inv ≫ g₀ ▷ W ≫ (λ_ W).hom with hμ
  have h₁ : μ ≫ φ = 𝟙 W := by
    rw [hΦ, hc] at hg₀
    simp only [hμ, Category.assoc]
    rw [hg₀, Iso.inv_hom_id]
  have h₂ : φ ≫ μ = μ ≫ φ := by
    simp only [hμ, Category.assoc]
    rw [← leftUnitor_naturality φ, ← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]
  have h₃ : φ ≫ μ = 𝟙 W := h₂.trans h₁
  have hθ : (fun g : E ⟶ 𝟙_ C => g ▷ W ≫ (λ_ W).hom) = fun g => Φ E hE g ≫ μ := by
    funext g
    rw [hΦ, hc, Category.assoc, Category.assoc, h₃, Category.comp_id]
  have hμ' : Function.Bijective fun y : E ⊗ W ⟶ W => y ≫ μ :=
    ⟨fun a b h => by simpa only [Category.assoc, h₁, Category.comp_id] using congrArg (· ≫ φ) h,
      fun y => ⟨y ≫ φ, by simp only [Category.assoc, h₃, Category.comp_id]⟩⟩
  rw [hθ]
  exact hμ'.comp (Φ E hE).bijective

end CategoryTheory.MonoidalCategory

namespace Stacks.Duality.StandardModel

open _root_.AlgebraicGeometry CategoryTheory.Pretriangulated

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Postcomposition with a morphism `f : A ⟶ B` of `D_QCoh(𝒪_X)` which is bijective on maps
out of perfect objects makes `f` an isomorphism**, for `X` quasi-compact and quasi-separated: the
cone of `f` has quasi-coherent cohomology and receives no nonzero map from a perfect object, since
perfect objects are stable under shifts; the perfect generator of [Stacks, Tag 09IS] kills it. -/
theorem isIso_of_bijective_comp_of_isPerfect {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] {A B : DerivedCategory X.Modules}
    (hA : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf) A)
    (hB : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf) B)
    (f : A ⟶ B)
    (hf : ∀ E : DerivedCategory X.Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) E →
        Function.Bijective fun x : E ⟶ A => x ≫ f) :
    IsIso f := by
  let P : ObjectProperty (DerivedCategory X.Modules) := fun K =>
    Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) K
  have : P.IsTriangulated :=
    Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect X.toRingedSpace
  obtain ⟨Z, g, k, hT⟩ := distinguished_cocone_triangle f
  let Q : ObjectProperty (DerivedCategory X.Modules) :=
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)
  have : Q.IsTriangulated := DerivedCategoryB.derivedCategoryB_isTriangulated _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)
  have : Q.IsClosedUnderIsomorphisms :=
    DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)
  have hZ : Q Z :=
    Q.ext_of_isTriangulatedClosed₂ _ (rot_of_distTriang _ hT) hB (Q.le_shift (1 : ℤ) A hA)
  have h31 : k ≫ f⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
  have h12 : f ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
  -- maps from a perfect object to the cone vanish
  have hvan : ∀ (E : DerivedCategory X.Modules), P E → ∀ x : E ⟶ Z, x = 0 := by
    intro E hE x
    have hx : x ≫ k = 0 := by
      let e := shiftFunctorCompIsoId (DerivedCategory X.Modules) (1 : ℤ) (-1) (by norm_num)
      have h0 : ((x ≫ k)⟦(-1 : ℤ)⟧' ≫ e.hom.app A) ≫ f = 0 := by
        have hn := e.hom.naturality f
        dsimp at hn
        rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp, Category.assoc, h31,
          comp_zero, Functor.map_zero, zero_comp]
      have hv : (x ≫ k)⟦(-1 : ℤ)⟧' ≫ e.hom.app A = 0 :=
        (hf _ (P.le_shift (-1 : ℤ) E hE)).1 (by dsimp only; rw [h0, zero_comp])
      exact (Functor.map_eq_zero_iff (shiftFunctor (DerivedCategory X.Modules) (-1 : ℤ))).1
        ((cancel_mono (e.hom.app A)).1 (by rw [hv, zero_comp]))
    obtain ⟨y, rfl⟩ := Triangle.coyoneda_exact₃ _ hT x hx
    obtain ⟨y', rfl⟩ := (hf E hE).2 y
    simp [h12]
  obtain ⟨G, hG, hgen⟩ := Stacks.SheafOfModules.exists_isPerfect_generator_modules X
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 (hgen Z hZ fun n x => hvan _ (P.le_shift n G hG) x)

/-- **The homothety `𝒪_X ⟶ R𝓗om_{𝒪_X}(W, W)` is invertible as soon as `Hom(E, 𝒪_X) ⟶
Hom(E ⊗^L W, W)`, `g ↦ g ⊗ 1_W` followed by the unit constraint, is bijective for every perfect
`E`**, for `X` quasi-compact and quasi-separated and `W` pseudo-coherent and bounded below.

By [Stacks, Tag 08DJ] the hypothesis says that postcomposition with the homothety is bijective on
maps out of perfect objects, `R𝓗om(W, W)` has quasi-coherent cohomology by [Stacks, Tag 0A6H]
(1), and `isIso_of_bijective_comp_of_isPerfect` applies. -/
theorem isIso_derivedSheafHomothety_of_bijective {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X]
    (W : DerivedCategory (SheafOfModules.StructureSheafModules X.sheaf))
    (hW : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) W)
    (hWb : DerivedCategoryB.IsBoundedBelow W)
    (h : letI := Stacks.SheafOfModules.derivedMonoidalStructure X.sheaf
      ∀ E : DerivedCategory (SheafOfModules.StructureSheafModules X.sheaf),
        Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) E →
          Function.Bijective fun g :
            E ⟶ 𝟙_ (DerivedCategory (SheafOfModules.StructureSheafModules X.sheaf)) =>
              g ▷ W ≫ (λ_ W).hom) :
    IsIso (Stacks.SheafOfModules.derivedSheafHomothety X.sheaf W) := by
  let := Stacks.SheafOfModules.derivedMonoidalStructure X.sheaf
  have hWq : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) W :=
    isQuasicoherentDerived_of_isPseudoCoherent X W hW
  have hA := derivedCategoryB_derivedSheafHom_of_isPseudoCoherent X W W hW ⟨hWb, hWq⟩
  have h1 : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      (𝟙_ (DerivedCategory (SheafOfModules.StructureSheafModules X.sheaf))) := by
    have hpc : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace)
        (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite X.sheaf)) :=
      Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect.{u, u + 1}
        (X := X.toRingedSpace) _
        (Stacks.SheafOfModules.isPerfect_derivedStructureSheaf_space.{u} X.toRingedSpace)
    rw [Stacks.SheafOfModules.tensorUnit_derivedMonoidalStructure]
    exact isQuasicoherentDerived_of_isPseudoCoherent X _ hpc
  refine isIso_of_bijective_comp_of_isPerfect h1 hA _
    fun (E : DerivedCategory (SheafOfModules.StructureSheafModules X.sheaf)) hE => ?_
  have heq : (fun a : E ⟶ ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op W)).obj W =>
        a ▷ W ≫ Stacks.SheafOfModules.derivedSheafHomCounit X.sheaf W W) ∘
      (fun x : E ⟶ 𝟙_ (DerivedCategory (SheafOfModules.StructureSheafModules X.sheaf)) =>
        x ≫ Stacks.SheafOfModules.derivedSheafHomothety X.sheaf W) =
      fun g => g ▷ W ≫ (λ_ W).hom := by
    funext g
    simp only [Function.comp_apply, comp_whiskerRight, Category.assoc,
      Stacks.SheafOfModules.whiskerRight_derivedSheafHomothety_comp]
  exact (Function.Bijective.of_comp_iff'
    (Stacks.SheafOfModules.tensorHomBijective_derivedSheafHomCounit X.sheaf W W E) _).1
    (heq ▸ h E hE)

end Stacks.Duality.StandardModel

end
