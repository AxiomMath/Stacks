module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Closure of quasi-coherence under finite products

Stacks 03M1 asserts that quasi-coherent modules on an algebraic space are closed, inside all
modules, under kernels, cokernels, extensions, direct sums and arbitrary colimits; the four
clauses that `AlgebraicGeometry.Space.quasicoherentSheaves_abelian_of_closure` and
`AlgebraicGeometry.Space.quasicoherentSheaves_isGrothendieckAbelian_of_closure` consume are
closure under kernels, cokernels, finite products and filtered colimits.  This file proves the
third of them, for an arbitrary ringed site, from the single geometric input that *having a
global presentation is stable under restriction along a morphism of the site*.

## Main definitions

* the universe-lift functor `SheafOfModules.uliftForPresentationFunctor` is
  `SheafOfModules.uliftForPresentation` of the sections of a sheaf of modules, as a functor; its
  action on morphisms is the existing `SheafOfModules.uliftForPresentationMap`.

## Main results

* `CategoryTheory.Limits.isColimitCokernelCoforkBiprodMap`: in a preadditive category, a binary
  biproduct of two cokernel coforks is a cokernel cofork.
* `SheafOfModules.HasGlobalPresentation.biprod`: a binary biproduct of modules with global
  presentations has a global presentation.  This is unconditional.
* `SheafOfModules.IsQuasicoherentOnSite.biprod`: a binary biproduct of quasi-coherent modules is
  quasi-coherent, given restriction-stability of global presentations.
* `SheafOfModules.isClosedUnderBinaryProducts_isQuasicoherentOnSite`,
  `SheafOfModules.isClosedUnderBinaryCoproducts_isQuasicoherentOnSite` and
  `SheafOfModules.isClosedUnderFiniteProducts_isQuasicoherentOnSite`: the same statement as the
  three `CategoryTheory.ObjectProperty` closure classes, and
  `SheafOfModules.IsQuasicoherentOnSite.coprod` for the direct sum of two modules.
* `AlgebraicGeometry.Space.isClosedUnderFiniteProducts_quasicoherentSheaves`: the finite-product
  clause on the small étale ringed site of an algebraic space, in the universes in which
  `AlgebraicGeometry.Space.quasicoherentSheaves_abelian_of_closure` asks for it.

## Implementation notes

Quasi-coherence is `SheafOfModules.IsQuasicoherentOnSite`, Stacks 03DL(6), and a global
presentation is `SheafOfModules.HasGlobalPresentation`, Stacks 03DE(6); nothing is restated.

A binary product of sheaves of modules is a binary biproduct — the category is preadditive and
has all finite limits — so the whole argument is carried out for
`CategoryTheory.Limits.biprod`, which is simultaneously the product the `ObjectProperty` class
asks about and the coproduct that a presentation is assembled from.  Concretely: the two
presenting families of copies of the structure sheaf add up to one family indexed by the sum of
the two index types, by the existing
`SheafOfModules.isColimitCofanSumOfBinaryCofan`; the biproduct of the two presenting cokernel
coforks is a cokernel cofork, which is `isColimitCokernelCoforkBiprodMap` and needs only
preadditivity; and the universe lift of a biproduct is the biproduct of the universe lifts,
because that lift preserves finite limits — it is the sectionwise `ULift` of abelian groups, so
this is `CategoryTheory.Limits.preservesFiniteLimits_of_reflects_of_preserves` applied to the
faithful inclusion of sheaves of modules into presheaves of abelian groups.

Restriction-stability of global presentations is a hypothesis and not a theorem here.  It is the
one thing the refinement step needs and the one thing that is not formal: `M` and `N` are
presented on two possibly different coverings of an object `U`, the intersection of the two
covering sieves is covering because a Grothendieck topology is closed under binary
intersections, but the members of the intersection are arrows factoring through members of the
two given families, so both presentations have to be transported along those factorizations.
The statement of the hypothesis is literally that of
`Stacks.SheafOfModules.hasGlobalPresentation_overMap` in
`StacksDraft.Ch18.Sec23.QuasicoherenceLocalOnCover`, and it is discharged by a one-line
application in `StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFiniteProducts`, which turns
the three closure theorems below into unconditional instances.

No `@[stacks 03M1]` tag is carried: every statement about quasi-coherence here is conditional on
that hypothesis, and 03M1 has no finite-product clause of its own — the clause it does have is
about arbitrary direct sums, which no refinement of coverings can reach, since a Grothendieck
topology is not closed under infinite intersections.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v r m t

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}


variable {R : Sheaf J RingCat.{r}}

instance uliftForPresentationFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (uliftForPresentationFunctor.{u, v, r, m, t} (R := R)) := by
  let G := SheafOfModules.forget.{max t m} R ⋙ PresheafOfModules.toPresheaf R.obj
  have hG : PreservesFiniteLimits
      (uliftForPresentationFunctor.{u, v, r, m, t} (R := R) ⋙ G) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget.{m} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{m} AddCommGrpCat.{max t m}).obj
          AddCommGrpCat.uliftFunctor.{t, m})
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves
    (uliftForPresentationFunctor.{u, v, r, m, t} (R := R)) G

end SheafOfModules

namespace CategoryTheory.Limits

variable {D : Type u} [Category.{v} D] [Preadditive D]

/-- The biproduct of two composable pairs of morphisms with zero composite has zero composite. -/
theorem biprod_map_comp_biprod_map_eq_zero {Q₁ P₁ N₁ Q₂ P₂ N₂ : D}
    [HasBinaryBiproduct Q₁ Q₂] [HasBinaryBiproduct P₁ P₂] [HasBinaryBiproduct N₁ N₂]
    {a₁ : Q₁ ⟶ P₁} {b₁ : P₁ ⟶ N₁} {a₂ : Q₂ ⟶ P₂} {b₂ : P₂ ⟶ N₂}
    (h₁ : a₁ ≫ b₁ = 0) (h₂ : a₂ ≫ b₂ = 0) :
    biprod.map a₁ a₂ ≫ biprod.map b₁ b₂ = 0 := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [comp_zero, biprod.inl_map_assoc, biprod.inl_map, ← Category.assoc, h₁, zero_comp]
  · rw [comp_zero, biprod.inr_map_assoc, biprod.inr_map, ← Category.assoc, h₂, zero_comp]

/-- A binary biproduct of two cokernel coforks is a cokernel cofork. -/
noncomputable def isColimitCokernelCoforkBiprodMap {Q₁ P₁ N₁ Q₂ P₂ N₂ : D}
    [HasBinaryBiproduct Q₁ Q₂] [HasBinaryBiproduct P₁ P₂] [HasBinaryBiproduct N₁ N₂]
    {a₁ : Q₁ ⟶ P₁} {b₁ : P₁ ⟶ N₁} {a₂ : Q₂ ⟶ P₂} {b₂ : P₂ ⟶ N₂}
    (h₁ : a₁ ≫ b₁ = 0) (hb₁ : IsColimit (CokernelCofork.ofπ b₁ h₁))
    (h₂ : a₂ ≫ b₂ = 0) (hb₂ : IsColimit (CokernelCofork.ofπ b₂ h₂)) :
    IsColimit (CokernelCofork.ofπ (biprod.map b₁ b₂)
      (biprod_map_comp_biprod_map_eq_zero h₁ h₂)) := by
  have he₁ : Epi b₁ := Cofork.IsColimit.epi hb₁
  have he₂ : Epi b₂ := Cofork.IsColimit.epi hb₂
  refine CokernelCofork.IsColimit.ofπ' _ _ fun {A} k hk ↦ ?_
  have hk₁ : a₁ ≫ biprod.inl ≫ k = 0 := by
    have h := biprod.inl ≫= hk
    rwa [comp_zero, biprod.inl_map_assoc] at h
  have hk₂ : a₂ ≫ biprod.inr ≫ k = 0 := by
    have h := biprod.inr ≫= hk
    rwa [comp_zero, biprod.inr_map_assoc] at h
  obtain ⟨l₁, hl₁⟩ := CokernelCofork.IsColimit.desc' hb₁ _ hk₁
  obtain ⟨l₂, hl₂⟩ := CokernelCofork.IsColimit.desc' hb₂ _ hk₂
  refine ⟨biprod.desc l₁ l₂, biprod.hom_ext' _ _ ?_ ?_⟩
  · rw [biprod.inl_map_assoc, biprod.inl_desc]
    exact hl₁
  · rw [biprod.inr_map_assoc, biprod.inr_desc]
    exact hl₂

end CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

private instance : HasBinaryBiproducts (SheafOfModules.{m} R) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- A functor preserving finite limits between preadditive categories sends a binary biproduct to
the binary biproduct of the images. -/
private noncomputable def mapBiprodOfPreservesFiniteLimits {D E : Type*} [Category D] [Category E]
    [Preadditive D] [Preadditive E] [HasBinaryBiproducts E] (F : D ⥤ E) [PreservesFiniteLimits F]
    [F.PreservesZeroMorphisms] (M N : D) [HasBinaryBiproduct M N] :
    F.obj (M ⊞ N) ≅ F.obj M ⊞ F.obj N :=
  have := preservesBinaryBiproducts_of_preservesBinaryProducts F
  F.mapBiprod M N

/-- A binary biproduct of two sheaves of modules with global presentations has a global
presentation: the two presenting families of copies of the structure sheaf become one family
indexed by the sum of the two index types, and the biproduct of the two presenting cokernel
coforks is again one. -/
theorem HasGlobalPresentation.biprod {M N : SheafOfModules.{m} R} [HasBinaryBiproduct M N]
    (hM : M.HasGlobalPresentation) (hN : N.HasGlobalPresentation) :
    (M ⊞ N).HasGlobalPresentation := by
  obtain ⟨I₁, K₁, P₁, Q₁, ι₁, κ₁, ⟨hP₁⟩, ⟨hQ₁⟩, a₁, b₁, hab₁, ⟨hb₁⟩⟩ := hM
  obtain ⟨I₂, K₂, P₂, Q₂, ι₂, κ₂, ⟨hP₂⟩, ⟨hQ₂⟩, a₂, b₂, hab₂, ⟨hb₂⟩⟩ := hN
  let e : uliftForPresentation.{u, v, r, m, max u v r} (M ⊞ N) ≅
      uliftForPresentation.{u, v, r, m, max u v r} M ⊞
        uliftForPresentation.{u, v, r, m, max u v r} N :=
    mapBiprodOfPreservesFiniteLimits (uliftForPresentationFunctor.{u, v, r, m, max u v r} (R := R))
      M N
  refine ⟨I₁ ⊕ I₂, K₁ ⊕ K₂, P₁ ⊞ P₂, Q₁ ⊞ Q₂,
    Sum.elim (fun i ↦ ι₁ i ≫ biprod.inl) (fun i ↦ ι₂ i ≫ biprod.inr),
    Sum.elim (fun i ↦ κ₁ i ≫ biprod.inl) (fun i ↦ κ₂ i ≫ biprod.inr),
    ⟨?_⟩, ⟨?_⟩, biprod.map a₁ a₂, biprod.map b₁ b₂ ≫ e.inv, ?_, ⟨?_⟩⟩
  · exact isColimitCofanSumOfBinaryCofan hP₁ hP₂ (BinaryBiproduct.isColimit P₁ P₂)
  · exact isColimitCofanSumOfBinaryCofan hQ₁ hQ₂ (BinaryBiproduct.isColimit Q₁ Q₂)
  · rw [← Category.assoc, biprod_map_comp_biprod_map_eq_zero hab₁ hab₂, zero_comp]
  · exact (isColimitCokernelCoforkBiprodMap hab₁ hb₁ hab₂ hb₂).ofIsoColimit
      (Cofork.ext e.symm rfl)

/-- Restriction to a slice of the site preserves finite limits, hence binary biproducts: it is
the direct image along `CategoryTheory.Over.forget`. -/
theorem preservesFiniteLimits_overFunctor (R : Sheaf J RingCat.{r}) (X : C) :
    PreservesFiniteLimits (overFunctor.{m} R X) :=
  preservesFiniteLimits_pushforward _

/-- If the restrictions of `M` and of `N` to a slice of the site have global presentations, so
does the restriction of their biproduct: restriction preserves finite limits, hence biproducts,
and a biproduct of globally presented modules is globally presented. -/
theorem HasGlobalPresentation.over_biprod {M N : SheafOfModules.{m} R}
    [HasBinaryBiproduct M N] (X : C)
    (hM : (M.over X).HasGlobalPresentation) (hN : (N.over X).HasGlobalPresentation) :
    ((M ⊞ N).over X).HasGlobalPresentation := by
  have : PreservesFiniteLimits (overFunctor.{m} R X) := preservesFiniteLimits_overFunctor R X
  have : (overFunctor.{m} R X).PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  exact HasGlobalPresentation.of_iso
    (mapBiprodOfPreservesFiniteLimits (overFunctor.{m} R X) M N).symm
    (HasGlobalPresentation.biprod.{max u v, v, r, m} hM hN)

/-- Quasi-coherence is stable under binary biproducts, as soon as having a global presentation
is stable under restriction along an arbitrary morphism of the site.

The hypothesis is the only non-formal input: `M` and `N` are presented on possibly different
coverings of an object `U`, and the intersection of the two covering sieves is covering, but
its members are arrows factoring through members of the two given families, so the two
presentations have to be moved along those factorizations. -/
theorem IsQuasicoherentOnSite.biprod
    (hres : ∀ (M : SheafOfModules.{m} R) {X Y : C}, (X ⟶ Y) →
      (M.over Y).HasGlobalPresentation → (M.over X).HasGlobalPresentation)
    {M N : SheafOfModules.{m} R} [HasBinaryBiproduct M N]
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    (M ⊞ N).IsQuasicoherentOnSite where
  locally_hasGlobalPresentation U := by
    classical
    obtain ⟨I, V, f, hV, hPV⟩ := hM.locally_hasGlobalPresentation U
    obtain ⟨I', V', f', hV', hPV'⟩ := hN.locally_hasGlobalPresentation U
    set S : Sieve U := Sieve.ofArrows V f ⊓ Sieve.ofArrows V' f' with hSdef
    have hS : S ∈ J U := J.intersection_covering hV hV'
    refine ⟨{g : Over U // S g.hom}, fun a ↦ a.1.left, fun a ↦ a.1.hom, ?_, ?_⟩
    · have hEq : Sieve.ofArrows (fun a : {g : Over U // S g.hom} ↦ a.1.left)
          (fun a ↦ a.1.hom) = S := by
        refine le_antisymm (fun Z g hg ↦ ?_) (fun Z g hg ↦ ?_)
        · obtain ⟨a, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
          exact S.downward_closed a.2 b
        · rw [Sieve.mem_ofArrows_iff]
          exact ⟨⟨Over.mk g, hg⟩, 𝟙 Z, by simp⟩
      rw [hEq]
      exact hS
    · intro a
      obtain ⟨i, c, hc⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp a.2.1
      obtain ⟨i', c', hc'⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp a.2.2
      exact HasGlobalPresentation.over_biprod _ (hres M c (hPV i)) (hres N c' (hPV' i'))

section Closure

variable (R) in
/-- Quasi-coherence of sheaves of modules on a site is closed under binary products, as soon as
having a global presentation is stable under restriction along a morphism of the site. -/
theorem isClosedUnderBinaryProducts_isQuasicoherentOnSite
    (hres : ∀ (M : SheafOfModules.{m} R) {X Y : C}, (X ⟶ Y) →
      (M.over Y).HasGlobalPresentation → (M.over X).HasGlobalPresentation) :
    (isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderBinaryProducts :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨G, hG⟩
    have : HasBinaryBiproduct (G.obj ⟨WalkingPair.left⟩) (G.obj ⟨WalkingPair.right⟩) :=
      HasBinaryBiproduct.of_hasBinaryProduct _ _
    refine ObjectProperty.prop_of_iso _
      ((HasLimit.isoOfNatIso (diagramIsoPair G)).trans (IsLimit.conePointUniqueUpToIso
        (limit.isLimit (pair _ _)) (BinaryBiproduct.isLimit _ _))).symm ?_
    exact IsQuasicoherentOnSite.biprod hres (hG ⟨WalkingPair.left⟩) (hG ⟨WalkingPair.right⟩))

variable (R) in
/-- Quasi-coherence of sheaves of modules on a site is closed under binary coproducts, as soon
as having a global presentation is stable under restriction along a morphism of the site.

A binary coproduct of sheaves of modules is a binary biproduct, so this is the same statement
as closure under binary products; it is the binary case of the direct-sum clause of
Stacks 03M1. -/
@[ega "0 5.1.3" "special case"]
theorem isClosedUnderBinaryCoproducts_isQuasicoherentOnSite
    (hres : ∀ (M : SheafOfModules.{m} R) {X Y : C}, (X ⟶ Y) →
      (M.over Y).HasGlobalPresentation → (M.over X).HasGlobalPresentation) :
    (isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderBinaryCoproducts :=
  ObjectProperty.IsClosedUnderColimitsOfShape.mk' (by
    rintro _ ⟨G, hG⟩
    have : HasBinaryBiproduct (G.obj ⟨WalkingPair.left⟩) (G.obj ⟨WalkingPair.right⟩) :=
      HasBinaryBiproduct.of_hasBinaryProduct _ _
    refine ObjectProperty.prop_of_iso _
      ((HasColimit.isoOfNatIso (diagramIsoPair G)).trans
        (IsColimit.coconePointUniqueUpToIso (colimit.isColimit (pair _ _))
          (BinaryBiproduct.isColimit _ _))).symm ?_
    exact IsQuasicoherentOnSite.biprod hres (hG ⟨WalkingPair.left⟩) (hG ⟨WalkingPair.right⟩))

/-- The direct sum of two quasi-coherent modules is quasi-coherent, as soon as having a global
presentation is stable under restriction along a morphism of the site.  This is the binary case
of the direct-sum clause of Stacks 03M1. -/
@[ega "0 5.1.3" "special case"]
theorem IsQuasicoherentOnSite.coprod
    (hres : ∀ (M : SheafOfModules.{m} R) {X Y : C}, (X ⟶ Y) →
      (M.over Y).HasGlobalPresentation → (M.over X).HasGlobalPresentation)
    (M N : SheafOfModules.{m} R) [HasBinaryCoproduct M N]
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    (M ⨿ N).IsQuasicoherentOnSite :=
  have := isClosedUnderBinaryCoproducts_isQuasicoherentOnSite R hres
  ObjectProperty.prop_coprod _ M N hM hN

variable (R) in
/-- **Stacks 03M1, finite products, reduced to restriction-stability of global presentations.**
Quasi-coherence of sheaves of modules on a site is closed under finite products.

This is the third of the four closure properties that
`SheafOfModules.abelian_fullSubcategory_isQuasicoherentOnSite` consumes.  Closure under the
empty product is `SheafOfModules.isQuasicoherentOnSite_containsZero` and is unconditional. -/
theorem isClosedUnderFiniteProducts_isQuasicoherentOnSite
    (hres : ∀ (M : SheafOfModules.{m} R) {X Y : C}, (X ⟶ Y) →
      (M.over Y).HasGlobalPresentation → (M.over X).HasGlobalPresentation) :
    (isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderFiniteProducts := by
  have : HasZeroObject (SheafOfModules.{m} R) := hasZeroObject_of_hasTerminal_object
  have := isClosedUnderBinaryProducts_isQuasicoherentOnSite R hres
  exact ObjectProperty.IsClosedUnderFiniteProducts.mk'

end Closure

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Stacks 03M1, finite products, on an algebraic space, reduced to restriction-stability of
global presentations.**  Quasi-coherence of `𝒪_F`-modules is closed under finite products, as
soon as having a global presentation is stable under restriction along a morphism of the small
étale site.

This is the `AlgebraicGeometry.Space.quasicoherentSheaves_abelian_of_closure` hypothesis
`(SheafOfModules.isQuasicoherentOnSite (RingedSite.ringSheaf (smallEtaleRingedSite ..)))`
`.IsClosedUnderFiniteProducts`, in its universes: the small étale site of an algebraic space
over `Scheme.{u}` has objects in `Type (u + 1)`, morphisms in `Type u` and a
`CommRingCat.{u}`-valued structure sheaf, and the module universe stays free. -/
theorem isClosedUnderFiniteProducts_quasicoherentSheaves
    (hres : ∀ (M : Modules.{u, m} B S hS F hF)
      {X Y : (smallEtaleRingedSite B S hS F hF).C}, (X ⟶ Y) →
      (M.over Y).HasGlobalPresentation → (M.over X).HasGlobalPresentation) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderFiniteProducts :=
  SheafOfModules.isClosedUnderFiniteProducts_isQuasicoherentOnSite _ hres

end AlgebraicGeometry.Space

end
