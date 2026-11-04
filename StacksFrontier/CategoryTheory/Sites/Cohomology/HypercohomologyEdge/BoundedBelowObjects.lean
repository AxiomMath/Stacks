module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.SingleSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.TruncationTowerConstancy
import StacksCore.Tactic.StacksAttribute

/-! # The hypercohomology edge morphism on a bounded below object

Let `(C, O)` be a ringed site, `U` an object of `C` and `K` an object of the unbounded derived
category of `O`-modules whose cohomology sheaves have no higher cohomology over `U`. This file
proves that the edge morphism

`H^q(U, τ_{≥ a}K) ⟶ Γ(U, H^q(τ_{≥ a}K))`

of `Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge` is an isomorphism, for every
truncation level `a` and every degree `q`. This is the bounded below case of Stacks 0BKZ, and it
is one of the two halves of that tag: the other is the passage from a bounded below object to an
arbitrary one through the derived limit of the truncation tower.

The proof is an induction on `q - a` which peels one cohomology sheaf off the bottom at a time.
For `q < a` there is nothing to prove, both sides being zero by left t-exactness of derived
sections and by the truncation. For `q ≥ a` the comparison triangle of two truncation levels,
`Stacks.TruncationLevel.exists_distTriang_truncGE`, presents `τ_{≥ a}K` between the one-step
interval truncation `τ_{< a + 1}(τ_{≥ a}K)`, which is the cohomology sheaf `H^a(K)` placed in
degree `a`, and `τ_{≥ a + 1}K`:

* in the lowest degree `q = a` the third vertex `τ_{≥ a + 1}K` has no cohomology in degrees `a`
  and `a - 1`, and neither have its derived sections, by left t-exactness; so the first map of the
  triangle is inverted by degree-`a` cohomology on both sides of the edge morphism and the claim
  is the degenerate case
  `Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_single` at the single sheaf
  `H^a(K)`;
* in a higher degree `q > a` the first vertex has no cohomology in degrees `q` and `q + 1`,
  because it is concentrated in degree `a`, and neither have its derived sections, which is where
  the acyclicity hypothesis enters through
  `Stacks.Cohomology.HypercohomologyEdge.isZero_homology_derivedSections_truncLTGE`; so the second
  map of the triangle is inverted by degree-`q` cohomology on both sides and the claim follows
  from the same claim one level up, at `τ_{≥ a + 1}K`.

Both steps are the same move: in a naturality square of the edge morphism whose two vertical maps
are invertible, one horizontal map is invertible exactly when the other is. That is recorded
separately as `Stacks.NatTransSquare.isIso_app_of_isIso_app_cod` and its companion.

## Main results

* `Stacks.NatTransSquare.isIso_app_of_isIso_app_cod`,
  `Stacks.NatTransSquare.isIso_app_of_isIso_app_dom`: transport of invertibility of a natural
  transformation along a morphism inverted by both functors.
* `Stacks.NatTransSquare.isIso_map_of_isIso_app`: the remaining face of the same square, reading
  invertibility of the image of a morphism off invertibility of the transformation at both ends.
* `Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_truncLTGE`: the edge
  morphism is invertible at a one-step interval truncation, in its own degree.
* `Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_truncGE_self` and
  `Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_isGE_self`: **the
  bottom-degree case, with no acyclicity hypothesis at all** -- `H^a(U, K) ≅ Γ(U, H^a(K))` for `K`
  with no cohomology below degree `a`.  This is the `q = a` case of the two statements below,
  separated out because its proof is the base case of their induction and consumes nothing from
  the acyclicity hypothesis `hK`.
* `Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_truncGE`: **the bounded
  below case of Tag 0BKZ**, stated at a truncation `τ_{≥ a}K`.
* `Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_isGE`: the same, stated
  at an object which is bounded below.

## Implementation notes

The acyclicity hypothesis is needed over the single object `U` only, and is phrased with
`CategoryTheory.Functor.rightDerived` of evaluation at `U`, which is the form the statement of
Tag 0BKZ uses. The hypothesis of the tag over a whole covering collection is what the other half
of its proof consumes.

The statement is given at `τ_{≥ a}K` rather than under the hypothesis `K.IsGE a`, because that is
the form in which the terms of the truncation tower `Stacks.DerivedLimit.truncGETower` arrive at
the assembly; the hypothesis form is derived from it at the end of the file. Note also that the
acyclicity hypothesis is about the cohomology sheaves of `K` itself, which is what makes the
induction step available: the cohomology sheaves of `τ_{≥ a}K` in the degrees the truncation keeps
are those of `K`, so the hypothesis is never weakened as the induction climbs.

Exactness of derived sections is `Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor`,
whose conclusion is typeable only under the shift-commutation datum attached to the unit; that
datum is therefore bound before the instance is introduced.

## References

* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace Stacks.NatTransSquare

variable {D : Type*} [Category* D] {E : Type*} [Category* E] {F G : D ⥤ E}

/-- If both functors invert a morphism `f : X ⟶ Y`, then a natural transformation between them
which is invertible at `Y` is invertible at `X`: the naturality square exhibits the component at
`X` as a factor of an invertible composite whose other factor is invertible. -/
lemma isIso_app_of_isIso_app_cod (α : F ⟶ G) {X Y : D} (f : X ⟶ Y)
    (hF : IsIso (F.map f)) (hG : IsIso (G.map f)) (h : IsIso (α.app Y)) :
    IsIso (α.app X) := by
  have : IsIso (F.map f ≫ α.app Y) := IsIso.comp_isIso' hF h
  rw [α.naturality f] at this
  exact IsIso.of_isIso_comp_right (α.app X) (G.map f)

/-- If both functors invert a morphism `f : X ⟶ Y`, then a natural transformation between them
which is invertible at `X` is invertible at `Y`. -/
lemma isIso_app_of_isIso_app_dom (α : F ⟶ G) {X Y : D} (f : X ⟶ Y)
    (hF : IsIso (F.map f)) (hG : IsIso (G.map f)) (h : IsIso (α.app X)) :
    IsIso (α.app Y) := by
  have : IsIso (α.app X ≫ G.map f) := IsIso.comp_isIso' h hG
  rw [← α.naturality f] at this
  exact IsIso.of_isIso_comp_left (F.map f) (α.app Y)

/-- If a natural transformation is invertible at both ends of a morphism `f : X ⟶ Y` and the
target functor inverts `f`, then so does the source functor. -/
lemma isIso_map_of_isIso_app (α : F ⟶ G) {X Y : D} (f : X ⟶ Y)
    (hX : IsIso (α.app X)) (hY : IsIso (α.app Y)) (hG : IsIso (G.map f)) :
    IsIso (F.map f) := by
  have : IsIso (F.map f ≫ α.app Y) := by
    rw [α.naturality f]
    exact IsIso.comp_isIso' hX hG
  exact IsIso.of_isIso_comp_right (F.map f) (α.app Y)

end Stacks.NatTransSquare

namespace Stacks.Cohomology.HypercohomologyEdge

universe u v wRing wModule g

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{wRing})
  [HasSheafify J AddCommGrpCat.{wModule}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)]
  [EnoughInjectives (SheafOfModules.{wModule} O)]

attribute [local instance] evaluation_additive

omit [EnoughInjectives (SheafOfModules.{wModule} O)] in
/-- **Transport of the edge morphism along a comparison.** If a morphism `f` of the derived
category is inverted by degree-`q` hypercohomology over `U` and by the degree-`q` cohomology
sheaf, then the edge morphism is invertible at the source of `f` exactly when it is invertible at
its target. -/
lemma isIso_hypercohomologyEdge_app_iff_of_isIso_map (U : C) (q : ℤ)
    {X Y : DerivedCategory (SheafOfModules.{wModule} O)} (f : X ⟶ Y)
    (hsec : IsIso ((DerivedCategory.homologyFunctor
      (ModuleCat.{wModule} (O.obj.obj (.op U))) q).map ((derivedSections O U).map f)))
    (hsheaf : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q).map f)) :
    IsIso ((hypercohomologyEdge O U q).app X) ↔
      IsIso ((hypercohomologyEdge O U q).app Y) := by
  have hF : IsIso ((derivedSections O U ⋙ DerivedCategory.homologyFunctor
    (ModuleCat.{wModule} (O.obj.obj (.op U))) q).map f) := hsec
  have hG : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q ⋙
      SheafOfModules.evaluation O (.op U)).map f) :=
    Functor.map_isIso (SheafOfModules.evaluation O (.op U)) _
  exact ⟨Stacks.NatTransSquare.isIso_app_of_isIso_app_dom _ f hF hG,
    Stacks.NatTransSquare.isIso_app_of_isIso_app_cod _ f hF hG⟩

omit [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)]
  [EnoughInjectives (SheafOfModules.{wModule} O)] in
/-- A one-step interval truncation has no cohomology above its own degree. This is Mathlib's
instance for `τ_{< b}(τ_{≥ a}K)` read at `b = a + 1`, where the bound `b - 1` is not syntactically
`a`. -/
lemma isLE_truncLTGE (K : DerivedCategory (SheafOfModules.{wModule} O)) (a : ℤ) :
    DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.truncLTGE a (a + 1)).obj K) a := by
  have h : DerivedCategory.TStructure.t.IsLE
    ((DerivedCategory.TStructure.t.truncLTGE a (a + 1)).obj K) (a + 1 - 1) := inferInstance
  simpa using h

/-- **The edge morphism at a one-step interval truncation.** In its own degree `a` the edge
morphism is invertible at `τ_{< a + 1}(τ_{≥ a}K)`, with no hypothesis on `K`: that object is the
cohomology sheaf `H^a(K)` placed in degree `a`, where the degenerate case
`Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_single` applies. -/
lemma isIso_hypercohomologyEdge_app_truncLTGE (U : C)
    (K : DerivedCategory (SheafOfModules.{wModule} O)) (a : ℤ) :
    IsIso ((hypercohomologyEdge O U a).app
      ((DerivedCategory.TStructure.t.truncLTGE a (a + 1)).obj K)) := by
  obtain ⟨e⟩ := Stacks.TruncationLevel.nonempty_iso_singleFunctor_truncLTGE a K
  exact Stacks.NatTransSquare.isIso_app_of_isIso_app_cod (hypercohomologyEdge O U a) e.hom
    (Functor.map_isIso _ _) (Functor.map_isIso _ _)
    (isIso_hypercohomologyEdge_app_single O U _ a)

/-- Below the truncation level the edge morphism is a map between zero objects: its source
vanishes by left t-exactness of derived sections and its target because the truncation has no
cohomology there. -/
lemma isIso_hypercohomologyEdge_app_truncGE_of_lt (U : C)
    (K : DerivedCategory (SheafOfModules.{wModule} O)) (a q : ℤ) (hq : q < a) :
    IsIso ((hypercohomologyEdge O U q).app
      ((DerivedCategory.TStructure.t.truncGE a).obj K)) := by
  have hsrc : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{wModule} (O.obj.obj (.op U))) q).obj
      ((derivedSections O U).obj ((DerivedCategory.TStructure.t.truncGE a).obj K))) :=
    Stacks.DerivedFunctor.isZero_homology_totalRightDerived_obj
      (SheafOfModules.evaluation O (.op U)) _ a q hq
  have htgt : IsZero ((SheafOfModules.evaluation O (.op U)).obj
      ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q).obj
        ((DerivedCategory.TStructure.t.truncGE a).obj K))) :=
    Functor.map_isZero _ (DerivedCategory.isZero_of_isGE _ a q hq)
  exact ⟨0, hsrc.eq_of_src _ _, htgt.eq_of_src _ _⟩

/-- **The edge morphism at the truncation level itself, with no acyclicity hypothesis.**  In the
degree `a` of the truncation the edge morphism is invertible at `τ_{≥ a}K` for every `K`: the
comparison triangle of the levels `a` and `a + 1` has third vertex `τ_{≥ a + 1}K`, which has no
cohomology in degrees `a` and `a - 1`, and whose derived sections likewise have none there by left
t-exactness alone.  So its first map is inverted by degree-`a` cohomology on both sides of the edge
morphism, and the claim is the degenerate case
`Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_truncLTGE` at the one-step
interval truncation.

This is the lowest degree of
`Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_truncGE`, and the only one
whose proof consumes nothing from the acyclicity of the cohomology sheaves of `K` over `U`; it is
stated separately because the identification `H^a(U, K) ≅ Γ(U, H^a(K))` at the bottom degree of a
bounded below object is wanted unconditionally. -/
theorem isIso_hypercohomologyEdge_app_truncGE_self (U : C)
    (K : DerivedCategory (SheafOfModules.{wModule} O)) (a : ℤ) :
    IsIso ((hypercohomologyEdge O U a).app
      ((DerivedCategory.TStructure.t.truncGE a).obj K)) := by
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedSections O U) (derivedSectionsUnit O U)
    (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)) ℤ
  have htri : (derivedSections O U).IsTriangulated :=
    Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
      Stacks.Cohomology.Localization.enoughKInjectives (homotopySections O U)
      (derivedSections O U) (derivedSectionsUnit O U)
  obtain ⟨δ, hδ⟩ := Stacks.TruncationLevel.exists_distTriang_truncGE
    DerivedCategory.TStructure.t a (a + 1) (by omega) K
  have hsheaf := Stacks.TruncationLevel.isIso_homologyMap_mor₁ _ hδ a
    (DerivedCategory.isZero_of_isGE
      ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj K) (a + 1) a (by omega))
    (DerivedCategory.isZero_of_isGE
      ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj K) (a + 1) (a - 1) (by omega))
  have hsec := Stacks.TruncationLevel.isIso_homologyMap_mor₁ _
    ((derivedSections O U).map_distinguished _ hδ) a
    (Stacks.DerivedFunctor.isZero_homology_totalRightDerived_obj
      (SheafOfModules.evaluation O (.op U))
      ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj K) (a + 1) a (by omega))
    (Stacks.DerivedFunctor.isZero_homology_totalRightDerived_obj
      (SheafOfModules.evaluation O (.op U))
      ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj K) (a + 1) (a - 1) (by omega))
  exact (isIso_hypercohomologyEdge_app_iff_of_isIso_map O U a
    ((DerivedCategory.TStructure.t.truncLTι (a + 1)).app
      ((DerivedCategory.TStructure.t.truncGE a).obj K)) hsec hsheaf).1
    (isIso_hypercohomologyEdge_app_truncLTGE O U K a)

/-- **The bottom-degree case of Tag 0BKZ, with no acyclicity hypothesis.**  If `K` has no
cohomology below degree `a`, then the hypercohomology edge morphism is invertible at `K` in degree
`a` itself: `H^a(U, K) ≅ Γ(U, H^a(K))`.

This is `Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_truncGE_self` read
through the invertibility of the truncation map `K ⟶ τ_{≥ a}K`, which is what `K.IsGE a` says. -/
theorem isIso_hypercohomologyEdge_app_of_isGE_self (U : C)
    (K : DerivedCategory (SheafOfModules.{wModule} O)) (a : ℤ)
    [DerivedCategory.TStructure.t.IsGE K a] :
    IsIso ((hypercohomologyEdge O U a).app K) := by
  have : IsIso ((DerivedCategory.TStructure.t.truncGEπ a).app K) :=
    (DerivedCategory.TStructure.t.isGE_iff_isIso_truncGEπ_app a K).1 inferInstance
  exact Stacks.NatTransSquare.isIso_app_of_isIso_app_cod (hypercohomologyEdge O U a)
    ((DerivedCategory.TStructure.t.truncGEπ a).app K)
    (Functor.map_isIso _ _) (Functor.map_isIso _ _)
    (isIso_hypercohomologyEdge_app_truncGE_self O U K a)

/-- The induction behind `isIso_hypercohomologyEdge_app_truncGE`, on the number of cohomology
sheaves between the truncation level and the degree. -/
private lemma isIso_hypercohomologyEdge_app_truncGE_aux (U : C)
    (K : DerivedCategory (SheafOfModules.{wModule} O))
    (hK : ∀ (q : ℤ) (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.evaluation O (.op U)).rightDerived p).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q).obj K))) :
    ∀ (n : ℕ) (a q : ℤ), q = a + n →
      IsIso ((hypercohomologyEdge O U q).app
        ((DerivedCategory.TStructure.t.truncGE a).obj K)) := by
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedSections O U) (derivedSectionsUnit O U)
    (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)) ℤ
  have htri : (derivedSections O U).IsTriangulated :=
    Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
      Stacks.Cohomology.Localization.enoughKInjectives (homotopySections O U)
      (derivedSections O U) (derivedSectionsUnit O U)
  intro n
  induction n with
  | zero =>
    intro a q hq
    obtain rfl : q = a := by simpa using hq
    exact isIso_hypercohomologyEdge_app_truncGE_self O U K q
  | succ n ih =>
    intro a q hq
    obtain ⟨δ, hδ⟩ := Stacks.TruncationLevel.exists_distTriang_truncGE
      DerivedCategory.TStructure.t a (a + 1) (by omega) K
    have hLE := isLE_truncLTGE O K a
    have hsheaf := Stacks.TruncationLevel.isIso_homologyMap_mor₂ _ hδ q
      (DerivedCategory.isZero_of_isLE
        ((DerivedCategory.TStructure.t.truncLTGE a (a + 1)).obj K) a q (by omega))
      (DerivedCategory.isZero_of_isLE
        ((DerivedCategory.TStructure.t.truncLTGE a (a + 1)).obj K) a (q + 1) (by omega))
    have hsec := Stacks.TruncationLevel.isIso_homologyMap_mor₂ _
      ((derivedSections O U).map_distinguished _ hδ) q
      (isZero_homology_derivedSections_truncLTGE O U K a (a + 1) rfl (hK a) q (by omega))
      (isZero_homology_derivedSections_truncLTGE O U K a (a + 1) rfl (hK a) (q + 1) (by omega))
    exact (isIso_hypercohomologyEdge_app_iff_of_isIso_map O U q
      ((DerivedCategory.TStructure.t.natTransTruncGEOfLE a (a + 1) (by omega)).app K)
      hsec hsheaf).2 (ih (a + 1) q (by omega))

/-- **The bounded below case of Tag 0BKZ.** If the cohomology sheaves of `K` have no higher
cohomology over `U`, then the hypercohomology edge morphism is invertible at every truncation
`τ_{≥ a}K` from below, in every degree. -/
theorem isIso_hypercohomologyEdge_app_truncGE (U : C)
    (K : DerivedCategory (SheafOfModules.{wModule} O))
    (hK : ∀ (q : ℤ) (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.evaluation O (.op U)).rightDerived p).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q).obj K)))
    (a q : ℤ) :
    IsIso ((hypercohomologyEdge O U q).app
      ((DerivedCategory.TStructure.t.truncGE a).obj K)) := by
  rcases lt_or_ge q a with hq | hq
  · exact isIso_hypercohomologyEdge_app_truncGE_of_lt O U K a q hq
  · exact isIso_hypercohomologyEdge_app_truncGE_aux O U K hK (q - a).toNat a q (by omega)

/-- **The bounded below case of Tag 0BKZ, at a bounded below object.** If `K` has no cohomology
below degree `a` and its cohomology sheaves have no higher cohomology over `U`, then the
hypercohomology edge morphism is invertible at `K` in every degree. -/
theorem isIso_hypercohomologyEdge_app_of_isGE (U : C)
    (K : DerivedCategory (SheafOfModules.{wModule} O)) (a : ℤ)
    [DerivedCategory.TStructure.t.IsGE K a]
    (hK : ∀ (q : ℤ) (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.evaluation O (.op U)).rightDerived p).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q).obj K)))
    (q : ℤ) :
    IsIso ((hypercohomologyEdge O U q).app K) := by
  have : IsIso ((DerivedCategory.TStructure.t.truncGEπ a).app K) :=
    (DerivedCategory.TStructure.t.isGE_iff_isIso_truncGEπ_app a K).1 inferInstance
  exact Stacks.NatTransSquare.isIso_app_of_isIso_app_cod (hypercohomologyEdge O U q)
    ((DerivedCategory.TStructure.t.truncGEπ a).app K)
    (Functor.map_isIso _ _) (Functor.map_isIso _ _)
    (isIso_hypercohomologyEdge_app_truncGE O U K hK a q)

end Stacks.Cohomology.HypercohomologyEdge

end
