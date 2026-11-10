module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GaloisFixedComponentDescent
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.LocalMinimalPrime
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.PointsOverField
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RestrictionOverField
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Translation
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
public import StacksFrontier.RingTheory.Spectrum.Prime.IrreducibleComponents
public import StacksFrontier.RingTheory.Spectrum.Prime.Surjective

/-!
# Irreducible components of a groupoid scheme over a field

For a groupoid scheme whose object scheme is the spectrum of a field, each local ring of the
arrow scheme has a unique minimal prime. There is a unique irreducible component through the
identity, and this component is geometrically irreducible over the field with respect to both
the source and target morphisms.

The argument first treats a separably closed ground field: composition of arrows glues the
component through the identity to any other component through the identity, so that component is
unique, and translation by a point whose source and target induce isomorphisms on residue fields
moves it to a component through that point. Uniqueness of the component through a point is
equivalent to uniqueness of the minimal prime of the local ring there, which descends along the
flat restriction of the groupoid along an algebraically closed extension. Geometric
irreducibility is then descent of the Galois-fixed component over a separable closure.

## Main results

* `AlgebraicGeometry.GroupoidScheme.existsUnique_minimalPrime_stalk` gives the unique minimal
  prime in each local ring of the arrow scheme.
* `AlgebraicGeometry.GroupoidScheme.existsUnique_irreducibleComponent_containing_identity` gives
  the unique component through the identity section.
* `AlgebraicGeometry.GroupoidScheme`'s
  `geometricallyIrreducible_irreducibleComponent_of_identity_source` and
  `geometricallyIrreducible_irreducibleComponent_of_identity_target` give geometric
  irreducibility of that component via the two structure morphisms.

## Implementation notes

The identity point is represented by the range of the identity section; since the object scheme
is a field spectrum, this range is a singleton. Each irreducible component is given its canonical
reduced closed subscheme structure by the vanishing ideal. The geometric irreducibility
assertions are stated for any component through the identity, so the unique component from the
preceding result can be used directly.

## References

* [Stacks Project, Tag 04LT](https://stacks.math.columbia.edu/tag/04LT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-! ### Transport along an identification of the object scheme -/

private theorem over_eq_of_left_eq {S : Scheme.{u}} (U : Over S) {Y : Scheme.{u}}
    (h : U.left = Y) : U = Over.mk (eqToHom h.symm ≫ U.hom) := by
  cases U
  cases h
  rfl

/-! ### The reduced subscheme on an irreducible component -/

/-- The identity section factors through the reduced closed subscheme on any irreducible
component of the arrow scheme which contains its image. -/
private noncomputable def identitySectionToComponent
    {S : Scheme.{u}} (G : GroupoidScheme S) (k : Type u) [Field k]
    (hU : G.objects.left = Spec (.of k)) (Z : irreducibleComponents G.arrows.left)
    (he : Set.range G.identity.left ⊆ Z.1) :
    G.objects.left ⟶
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ :
          Closeds G.arrows.left)).subscheme := by
  let Zc : Closeds G.arrows.left :=
    ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Zc
  have : Subsingleton G.objects.left := hU ▸ (inferInstance : Subsingleton (Spec (.of k)))
  have : IsReduced G.objects.left := by
    rw [hU]
    infer_instance
  have : IsClosedImmersion G.identity.left :=
    isClosedImmersion_of_comp_eq_id G.source.left G.identity.left (by
      simpa using congrArg Over.Hom.left G.source_identity)
  have hpSupport : G.identity.left.ker.support ≤ Zc := by
    change (G.identity.left.ker.support : Set G.arrows.left) ⊆ Z.1
    rw [Scheme.Hom.support_ker G.identity.left]
    exact closure_minimal he (isClosed_of_mem_irreducibleComponents Z.1 Z.2)
  have : IsReduced G.identity.left.ker.subscheme := by
    have : IsIso G.identity.left.toImage := inferInstance
    exact ObjectProperty.IsClosedUnderIsomorphisms.of_iso
      (asIso G.identity.left.toImage) (inferInstance : IsReduced G.objects.left)
  have hpker : G.identity.left.ker = Scheme.IdealSheafData.vanishingIdeal
      G.identity.left.ker.support :=
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme
      G.identity.left.ker G.identity.left.ker.support rfl
  have hker : I.subschemeι.ker ≤ G.identity.left.ker := by
    rw [I.ker_subschemeι, hpker]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono hpSupport
  exact IsClosedImmersion.lift I.subschemeι G.identity.left hker

private theorem identitySectionToComponent_fac
    {S : Scheme.{u}} (G : GroupoidScheme S) (k : Type u) [Field k]
    (hU : G.objects.left = Spec (.of k)) (Z : irreducibleComponents G.arrows.left)
    (he : Set.range G.identity.left ⊆ Z.1) :
    identitySectionToComponent G k hU Z he ≫
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ :
          Closeds G.arrows.left)).subschemeι =
      G.identity.left :=
  IsClosedImmersion.lift_fac _ _ _

/-- The reduced closed subscheme on an irreducible component is irreducible. -/
private theorem irreducibleSpace_vanishingIdeal_subscheme
    {X : Scheme.{u}} (Z : irreducibleComponents X) :
    IrreducibleSpace
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ : Closeds X)).subscheme := by
  let T : Closeds X := ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩
  let I := Scheme.IdealSheafData.vanishingIdeal T
  have hrange : Set.range I.subschemeι.base = Z.1 := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I, T]
  have homeo := I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph
  apply homeo.irreducibleSpace_iff.mpr
  rw [hrange]
  exact Subtype.irreducibleSpace Z.2.1

@[ega "IV 4.5.21"]
private theorem geometricallyIrreducible_component_of_isSepClosed
    (k : Type u) [Field k] [IsSepClosed k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) (Z : irreducibleComponents X) :
    GeometricallyIrreducible
      ((Scheme.IdealSheafData.vanishingIdeal
        (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ : Closeds X)).subschemeι ≫ f) := by
  let T : Closeds X := ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩
  let I := Scheme.IdealSheafData.vanishingIdeal T
  have : IrreducibleSpace I.subscheme := irreducibleSpace_vanishingIdeal_subscheme Z
  exact geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed
    k I.subscheme (I.subschemeι ≫ f)

private theorem irreducibleSpace_pullback_of_isSepClosed
    (k : Type u) [Field k] [IsSepClosed k] (X Y : Scheme.{u})
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    IrreducibleSpace ↥(pullback f g) := by
  have : GeometricallyIrreducible f :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k X f
  have : GeometricallyIrreducible g :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k Y g
  have : UniversallyOpen f := by infer_instance
  have : UniversallyOpen g := by infer_instance
  exact inferInstance

private theorem irreducibleSpace_componentProduct
    {S : Scheme.{u}} (G : GroupoidScheme S) (k : Type u) [Field k] [IsSepClosed k]
    (hU : G.objects.left = Spec (.of k)) (Z W : irreducibleComponents G.arrows.left) :
    IrreducibleSpace ↥(pullback
      ((Scheme.IdealSheafData.vanishingIdeal
        (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ :
          Closeds G.arrows.left)).subschemeι ≫ G.source.left ≫ eqToHom hU)
      ((Scheme.IdealSheafData.vanishingIdeal
        (⟨W.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ :
          Closeds G.arrows.left)).subschemeι ≫ G.target.left ≫ eqToHom hU)) := by
  let IZ := Scheme.IdealSheafData.vanishingIdeal
    (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ : Closeds G.arrows.left)
  let IW := Scheme.IdealSheafData.vanishingIdeal
    (⟨W.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ : Closeds G.arrows.left)
  have : IrreducibleSpace IZ.subscheme := irreducibleSpace_vanishingIdeal_subscheme Z
  have : IrreducibleSpace IW.subscheme := irreducibleSpace_vanishingIdeal_subscheme W
  exact irreducibleSpace_pullback_of_isSepClosed k IZ.subscheme IW.subscheme
    (IZ.subschemeι ≫ G.source.left ≫ eqToHom hU)
    (IW.subschemeι ≫ G.target.left ≫ eqToHom hU)

/-! ### Composing two components -/

section Composition

variable {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k]
  (hU : G.objects.left = Spec (.of k)) {A B : Scheme.{u}} (a : A ⟶ G.arrows.left)
  (b : B ⟶ G.arrows.left)

private noncomputable abbrev pairOver : Over S :=
  Over.mk (pullback.fst (a ≫ G.source.left ≫ eqToHom hU) (b ≫ G.target.left ≫ eqToHom hU) ≫
    (a ≫ G.source.left ≫ eqToHom hU) ≫ eqToHom hU.symm ≫ G.objects.hom)

private noncomputable def pairFst : pairOver G hU a b ⟶ G.arrows :=
  Over.homMk (pullback.fst _ _ ≫ a) (by simp [pairOver])

private noncomputable def pairSnd : pairOver G hU a b ⟶ G.arrows :=
  Over.homMk (pullback.snd _ _ ≫ b) (by
    change _ = pullback.fst _ _ ≫ _ ≫ _
    rw [pullback.condition_assoc]
    simp)

private theorem pairFst_source : pairFst G hU a b ≫ G.source = pairSnd G hU a b ≫ G.target := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (eqToHom hU)).1
  change pullback.fst _ _ ≫ (a ≫ G.source.left ≫ eqToHom hU) =
    pullback.snd _ _ ≫ (b ≫ G.target.left ≫ eqToHom hU)
  exact pullback.condition

end Composition

private theorem subset_image_of_comp_eq_subschemeι {X P : Scheme.{u}}
    (Z : irreducibleComponents X) (φ : P ⟶ X)
    {h : (Scheme.IdealSheafData.vanishingIdeal
      (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ : Closeds X)).subscheme ⟶ P}
    (hcomp : h ≫ φ = (Scheme.IdealSheafData.vanishingIdeal
      (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ : Closeds X)).subschemeι) :
    (Z : Set X) ⊆ φ.base '' Set.univ := by
  intro x hx
  obtain ⟨x', rfl⟩ : x ∈ Set.range (Scheme.IdealSheafData.vanishingIdeal
      (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ : Closeds X)).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hx
  exact ⟨h.base x', Set.mem_univ _, by
    simpa only [Scheme.Hom.comp_base, CategoryTheory.comp_apply] using
      congrArg (fun r => r.base x') hcomp⟩

/-- Composition of arrows, restricted to the product of the reduced subschemes on two
irreducible components. -/
private noncomputable def componentProductCompositionMap
    {S : Scheme.{u}} (G : GroupoidScheme S) (k : Type u) [Field k]
    (hU : G.objects.left = Spec (.of k)) (Z W : irreducibleComponents G.arrows.left) :
    pullback
      ((Scheme.IdealSheafData.vanishingIdeal
        (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ :
          Closeds G.arrows.left)).subschemeι ≫ G.source.left ≫ eqToHom hU)
      ((Scheme.IdealSheafData.vanishingIdeal
        (⟨W.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ :
          Closeds G.arrows.left)).subschemeι ≫ G.target.left ≫ eqToHom hU) ⟶
      G.arrows.left :=
  (Over.forget S).map (G.compose _ _ (pairFst_source G hU
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ : Closeds G.arrows.left)).subschemeι
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨W.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ : Closeds G.arrows.left)).subschemeι))

private theorem isIrreducible_image_componentProductCompositionMap
    {S : Scheme.{u}} (G : GroupoidScheme S) (k : Type u) [Field k] [IsSepClosed k]
    (hU : G.objects.left = Spec (.of k)) (Z W : irreducibleComponents G.arrows.left) :
    IsIrreducible ((componentProductCompositionMap G k hU Z W).base ''
      (Set.univ : Set ↥(pullback
        ((Scheme.IdealSheafData.vanishingIdeal
          (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ :
            Closeds G.arrows.left)).subschemeι ≫ G.source.left ≫ eqToHom hU)
        ((Scheme.IdealSheafData.vanishingIdeal
          (⟨W.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ :
            Closeds G.arrows.left)).subschemeι ≫ G.target.left ≫ eqToHom hU)))) := by
  have := irreducibleSpace_componentProduct G k hU Z W
  exact (IrreducibleSpace.isIrreducible_univ _).image _
    (componentProductCompositionMap G k hU Z W).continuous.continuousOn

private theorem groupoidCompose_precomp {S : Scheme.{u}} (G : GroupoidScheme S)
    {T T' : Over S} (f g : T ⟶ G.arrows) (w : f ≫ G.source = g ≫ G.target)
    (h : T' ⟶ T) (w' : (h ≫ f) ≫ G.source = (h ≫ g) ≫ G.target) :
    h ≫ G.compose f g w = G.compose (h ≫ f) (h ≫ g) w' := by
  dsimp [GroupoidScheme.compose]
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]

private theorem groupoidCompose_of_precomp_eq {S : Scheme.{u}} (G : GroupoidScheme S)
    {T T' : Over S} (f g : T ⟶ G.arrows) (w : f ≫ G.source = g ≫ G.target) (h : T' ⟶ T)
    {f' g' : T' ⟶ G.arrows} (hf : h ≫ f = f') (hg : h ≫ g = g')
    (w' : f' ≫ G.source = g' ≫ G.target) :
    h ≫ G.compose f g w = G.compose f' g' w' := by
  subst hf hg
  exact groupoidCompose_precomp G f g w h w'

private theorem groupoidCompose_identity_left {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over S} (f : T ⟶ G.arrows) (w : (f ≫ G.target ≫ G.identity) ≫ G.source = f ≫ G.target) :
    G.compose (f ≫ G.target ≫ G.identity) f w = f := by
  dsimp [GroupoidScheme.compose]
  exact G.left_identity _ _ w

private theorem groupoidCompose_identity_right {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over S} (f : T ⟶ G.arrows) (w : f ≫ G.source = (f ≫ G.source ≫ G.identity) ≫ G.target) :
    G.compose f (f ≫ G.source ≫ G.identity) w = f := by
  dsimp [GroupoidScheme.compose]
  exact G.right_identity _ _ w

section Composition

variable {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k]
  (hU : G.objects.left = Spec (.of k)) {A B : Scheme.{u}} (a : A ⟶ G.arrows.left)
  (b : B ⟶ G.arrows.left)

/-- If the identity section factors through `b`, every arrow of `a` is the composite of itself
with an identity arrow of `b`. -/
private theorem exists_comp_pairCompose_eq_left {aW : G.objects.left ⟶ B}
    (hfac : aW ≫ b = G.identity.left) :
    ∃ h : A ⟶ (pairOver G hU a b).left,
      h ≫ (Over.forget S).map (G.compose _ _ (pairFst_source G hU a b)) = a := by
  have htarget : G.identity.left ≫ G.target.left = 𝟙 G.objects.left :=
    congrArg Over.Hom.left G.target_identity
  let hT : Over.mk (a ≫ G.arrows.hom) ⟶ pairOver G hU a b :=
    Over.homMk (pullback.lift (𝟙 A) (a ≫ G.source.left ≫ aW)
      (by simp [reassoc_of% hfac, reassoc_of% htarget])) (by
        simp only [pairOver, Over.mk_hom]
        rw [pullback.lift_fst_assoc]
        simp)
  let pT : Over.mk (a ≫ G.arrows.hom) ⟶ G.arrows := Over.homMk a rfl
  have hpO : hT ≫ pairFst G hU a b = pT := by
    apply Over.OverMorphism.ext
    simp only [hT, pT, pairFst, Over.comp_left, Over.homMk_left]
    rw [pullback.lift_fst_assoc]
    simp
  have hqO : hT ≫ pairSnd G hU a b = pT ≫ G.source ≫ G.identity := by
    apply Over.OverMorphism.ext
    simp only [hT, pT, pairSnd, Over.comp_left, Over.homMk_left]
    rw [pullback.lift_snd_assoc]
    simp [hfac]
  refine ⟨hT.left, ?_⟩
  change (Over.forget S).map hT ≫ (Over.forget S).map (G.compose _ _ _) = a
  rw [← Functor.map_comp, groupoidCompose_of_precomp_eq G _ _ _ hT hpO hqO
    (by simp [G.target_identity]), groupoidCompose_identity_right]
  rfl

/-- If the identity section factors through `a`, every arrow of `b` is the composite of an
identity arrow of `a` with itself. -/
private theorem exists_comp_pairCompose_eq_right {aZ : G.objects.left ⟶ A}
    (hfac : aZ ≫ a = G.identity.left) :
    ∃ h : B ⟶ (pairOver G hU a b).left,
      h ≫ (Over.forget S).map (G.compose _ _ (pairFst_source G hU a b)) = b := by
  have hsource : G.identity.left ≫ G.source.left = 𝟙 G.objects.left :=
    congrArg Over.Hom.left G.source_identity
  let hT : Over.mk (b ≫ G.arrows.hom) ⟶ pairOver G hU a b :=
    Over.homMk (pullback.lift (b ≫ G.target.left ≫ aZ) (𝟙 B)
      (by simp [reassoc_of% hfac, reassoc_of% hsource]))
      (by
        simp only [pairOver, Over.mk_hom]
        rw [pullback.lift_fst_assoc]
        simp [reassoc_of% hfac])
  let qT : Over.mk (b ≫ G.arrows.hom) ⟶ G.arrows := Over.homMk b rfl
  have hpO : hT ≫ pairFst G hU a b = qT ≫ G.target ≫ G.identity := by
    apply Over.OverMorphism.ext
    simp only [hT, qT, pairFst, Over.comp_left, Over.homMk_left]
    rw [pullback.lift_fst_assoc]
    simp [hfac]
  have hqO : hT ≫ pairSnd G hU a b = qT := by
    apply Over.OverMorphism.ext
    simp only [hT, qT, pairSnd, Over.comp_left, Over.homMk_left]
    rw [pullback.lift_snd_assoc]
    simp
  refine ⟨hT.left, ?_⟩
  change (Over.forget S).map hT ≫ (Over.forget S).map (G.compose _ _ _) = b
  rw [← Functor.map_comp, groupoidCompose_of_precomp_eq G _ _ _ hT hpO hqO
    (by simp [G.source_identity]), groupoidCompose_identity_left]
  rfl

end Composition

private theorem componentProductCompositionMap_contains_left
    {S : Scheme.{u}} (G : GroupoidScheme S) (k : Type u) [Field k]
    (hU : G.objects.left = Spec (.of k)) (Z W : irreducibleComponents G.arrows.left)
    (hW : Set.range G.identity.left ⊆ (W : Set G.arrows.left)) :
    (Z : Set G.arrows.left) ⊆
      (componentProductCompositionMap G k hU Z W).base '' Set.univ := by
  obtain ⟨h, hcomp⟩ := exists_comp_pairCompose_eq_left G hU
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ : Closeds G.arrows.left)).subschemeι _
    (identitySectionToComponent_fac G k hU W hW)
  exact subset_image_of_comp_eq_subschemeι Z _ hcomp

private theorem componentProductCompositionMap_contains_right
    {S : Scheme.{u}} (G : GroupoidScheme S) (k : Type u) [Field k]
    (hU : G.objects.left = Spec (.of k)) (Z W : irreducibleComponents G.arrows.left)
    (hZ : Set.range G.identity.left ⊆ (Z : Set G.arrows.left)) :
    (W : Set G.arrows.left) ⊆
      (componentProductCompositionMap G k hU Z W).base '' Set.univ := by
  obtain ⟨h, hcomp⟩ := exists_comp_pairCompose_eq_right G hU _
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨W.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ : Closeds G.arrows.left)).subschemeι
    (identitySectionToComponent_fac G k hU Z hZ)
  exact subset_image_of_comp_eq_subschemeι W _ hcomp

/-- Since the object scheme is a point, the identity section lies in a set iff one point of it
does. -/
private theorem range_identity_subset_iff {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u}
    [Field k] (hU : G.objects.left = Spec (.of k)) (T : Set G.arrows.left) (x : G.objects.left) :
    Set.range G.identity.left ⊆ T ↔ G.identity.left x ∈ T := by
  have : Subsingleton G.objects.left := hU ▸ (inferInstance : Subsingleton (Spec (.of k)))
  refine ⟨fun h => h ⟨x, rfl⟩, ?_⟩
  rintro h _ ⟨u, rfl⟩
  rwa [Subsingleton.elim u x]

private theorem existsUnique_irreducibleComponent_containing_identity_of_isSepClosed
    {S : Scheme.{u}} (G : GroupoidScheme S) (k : Type u) [Field k] [IsSepClosed k]
    (hU : G.objects.left = Spec (.of k)) :
    ∃! Z : irreducibleComponents G.arrows.left,
      Set.range G.identity.left ⊆ (Z : Set G.arrows.left) := by
  let x₀ : G.objects.left := hU.symm ▸ IsLocalRing.closedPoint k
  let e := G.identity.left x₀
  obtain ⟨Z, hZ, hZsub⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible ({e} : Set G.arrows.left)
      isIrreducible_singleton
  let Z₀ : irreducibleComponents G.arrows.left := ⟨Z, hZ⟩
  have heZ : e ∈ (Z₀ : Set G.arrows.left) := hZsub (by simp)
  have hZid : Set.range G.identity.left ⊆ (Z₀ : Set G.arrows.left) :=
    (range_identity_subset_iff G hU _ x₀).2 heZ
  refine ⟨Z₀, hZid, fun W hWid => ?_⟩
  obtain ⟨Cset, hC, hCsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_image_componentProductCompositionMap G k hU Z₀ W)
  let C : irreducibleComponents G.arrows.left := ⟨Cset, hC⟩
  have hZC : (Z₀ : Set G.arrows.left) ⊆ (C : Set G.arrows.left) :=
    (componentProductCompositionMap_contains_left G k hU Z₀ W hWid).trans hCsub
  have hWC : (W : Set G.arrows.left) ⊆ (C : Set G.arrows.left) :=
    (componentProductCompositionMap_contains_right G k hU Z₀ W hZid).trans hCsub
  have hCZ : (C : Set G.arrows.left) ⊆ (Z₀ : Set G.arrows.left) :=
    Z₀.property.2 C.property.1 hZC
  have hCW : (C : Set G.arrows.left) ⊆ (W : Set G.arrows.left) :=
    W.property.2 C.property.1 hWC
  exact Subtype.ext ((hWC.trans hCZ).antisymm (hZC.trans hCW))

/-! ### Unique components and unique minimal primes -/

private theorem closure_image_preimage_eq_of_mem_irreducibleComponents
    {X Y : Type*} [TopologicalSpace X] {f : Y → X} (hf : IsOpen (Set.range f))
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) (hne : (Z ∩ Set.range f).Nonempty) :
    closure (f '' (f ⁻¹' Z)) = Z := by
  refine subset_antisymm (closure_minimal (Set.image_preimage_subset f Z)
    (isClosed_of_mem_irreducibleComponents Z hZ)) ?_
  rw [Set.image_preimage_eq_inter_range]
  exact subset_closure_inter_of_isPreirreducible_of_isOpen hZ.1.2 hf hne

private theorem existsUnique_irreducibleComponent_of_uniqueOpenRestriction
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Y → X} (hf : Topology.IsOpenEmbedding f) (y : Y)
    (h : ∃! W : irreducibleComponents Y, y ∈ (W : Set Y)) :
    ∃! Z : irreducibleComponents X, f y ∈ (Z : Set X) := by
  obtain ⟨W, -, hWuniq⟩ := h
  obtain ⟨Zset, hZset, hZsub⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible ({f y} : Set X)
      isIrreducible_singleton
  have hyZ : f y ∈ Zset := hZsub (by simp)
  have hcl (C : irreducibleComponents X) (hC : f y ∈ (C : Set X)) :
      closure (f '' (W : Set Y)) = C := by
    rw [← congrArg Subtype.val
      (hWuniq ⟨_, preimage_mem_irreducibleComponents C.2 hf ⟨f y, hC, y, rfl⟩⟩ hC)]
    exact closure_image_preimage_eq_of_mem_irreducibleComponents hf.isOpen_range C.2
      ⟨f y, hC, y, rfl⟩
  exact ⟨⟨Zset, hZset⟩, hyZ, fun Z' hyZ' =>
    Subtype.ext ((hcl Z' hyZ').symm.trans (hcl ⟨Zset, hZset⟩ hyZ))⟩

/-- A homeomorphism carries irreducible components to irreducible components. -/
private theorem image_mem_irreducibleComponents_of_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) {Z : Set X} (hZ : Z ∈ irreducibleComponents X) :
    e '' Z ∈ irreducibleComponents Y :=
  image_mem_irreducibleComponents_of_isPreirreducible_fiber e e.continuous e.isOpenMap
    (fun _ => (Set.subsingleton_singleton.preimage e.injective).isPreirreducible)
    e.surjective hZ

private theorem existsUnique_irreducibleComponent_of_homeomorph
    {X : Type u} [TopologicalSpace X] (e : X ≃ₜ X) (x y : X) (hxy : e x = y)
    (h : ∃! Z : irreducibleComponents X, x ∈ (Z : Set X)) :
    ∃! Z : irreducibleComponents X, y ∈ (Z : Set X) := by
  obtain ⟨Z, hxZ, hZ⟩ := h
  let W : irreducibleComponents X :=
    ⟨e '' (Z : Set X), image_mem_irreducibleComponents_of_homeomorph e Z.2⟩
  refine ⟨W, ?_, fun V hyV => ?_⟩
  · change y ∈ e '' (Z : Set X)
    rw [← hxy]
    exact ⟨x, hxZ, rfl⟩
  let W' : irreducibleComponents X :=
    ⟨e ⁻¹' (V : Set X),
      preimage_mem_irreducibleComponents V.2 e.isOpenEmbedding
        ⟨e x, by rwa [hxy], x, rfl⟩⟩
  have hxW' : x ∈ (W' : Set X) := by
    change e x ∈ (V : Set X)
    rwa [hxy]
  have hW' : W' = Z := hZ W' hxW'
  apply Subtype.ext
  change (V : Set X) = e '' (Z : Set X)
  rw [← hW']
  exact (Set.image_preimage_eq _ e.surjective).symm

private theorem existsUnique_irreducibleComponent_at_point_of_identityComponent
    {S : Scheme.{u}} (G : GroupoidScheme S) (k : Type u) [Field k]
    (hU : G.objects.left = Spec (.of k))
    (hId : ∃! Z : irreducibleComponents G.arrows.left,
      Set.range G.identity.left ⊆ (Z : Set G.arrows.left))
    (r : G.arrows.left) [IsIso (G.source.left.residueFieldMap r)]
    [IsIso (G.target.left.residueFieldMap r)] :
    ∃! Z : irreducibleComponents G.arrows.left, r ∈ (Z : Set G.arrows.left) := by
  let p := G.identity.left (G.source.left r)
  have hp : ∃! Z : irreducibleComponents G.arrows.left, p ∈ (Z : Set G.arrows.left) := by
    obtain ⟨Z, hZ, hZu⟩ := hId
    exact ⟨Z, hZ ⟨_, rfl⟩, fun Z' hp' =>
      hZu Z' ((range_identity_subset_iff G hU _ _).2 hp')⟩
  let f := translationByPoint G k hU r
  have : IsIso f := translationByPoint_isIso G k hU r
  let f₀ : G.arrows.left ⟶ G.arrows.left := f.left
  have : IsIso f₀ := inferInstanceAs (IsIso ((Over.forget S).map f))
  let e : G.arrows.left ≃ₜ G.arrows.left :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso f₀))
  have hfp : e p = r := by
    have h := identity_image_translationByPoint G k hU r
    change f₀.base p = r
    simpa [p, f₀] using h
  exact existsUnique_irreducibleComponent_of_homeomorph e p r hfp hp

private theorem existsUnique_irreducibleComponent_of_unique_minimalPrime_stalk
    {X : Scheme.{u}} (x : X)
    (h : ∃! p : Ideal (X.presheaf.stalk x), p ∈ minimalPrimes _) :
    ∃! Z : irreducibleComponents X, x ∈ (Z : Set X) := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let p := hU.primeIdealOf ⟨x, hxU⟩
  let _ : p.asIdeal.IsPrime := p.isPrime
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hxU).hom.toAlgebra
  let _ : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  let eRing : Localization.AtPrime p.asIdeal ≃+* X.presheaf.stalk x :=
    (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) (X.presheaf.stalk x)).toRingEquiv
  obtain ⟨q, hq, hqunique⟩ := existsUnique_minimalPrime_of_ringEquiv eRing h
  let eComp := PrimeSpectrum.irreducibleComponentsThroughEquiv Γ(X, U) p.asIdeal
    (Localization.AtPrime p.asIdeal)
  let z : PrimeSpectrum.irreducibleComponentsThrough Γ(X, U) p.asIdeal := eComp.symm ⟨q, hq⟩
  let W : irreducibleComponents (PrimeSpectrum Γ(X, U)) := ⟨z.1, z.2.1⟩
  have hW : ∃! C : irreducibleComponents (PrimeSpectrum Γ(X, U)),
      p ∈ (C : Set (PrimeSpectrum Γ(X, U))) := by
    refine ⟨W, z.2.2, fun C' hC' => ?_⟩
    let z' : PrimeSpectrum.irreducibleComponentsThrough Γ(X, U) p.asIdeal :=
      ⟨C', C'.property, hC'⟩
    have heq0 : eComp z' = ⟨q, hq⟩ := Subtype.ext (hqunique _ (eComp z').property)
    have heq : eComp z' = eComp z := by simpa [z] using heq0
    have hz : z' = z := eComp.injective heq
    have hsets : z'.1 = z.1 := congrArg
      (fun t : PrimeSpectrum.irreducibleComponentsThrough Γ(X, U) p.asIdeal => t.1) hz
    apply Subtype.ext
    simpa [W] using hsets
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  simpa [p, hU.fromSpec_primeIdealOf] using
    existsUnique_irreducibleComponent_of_uniqueOpenRestriction hU.fromSpec.isOpenEmbedding p hW

private theorem existsUnique_minimalPrime_stalk_of_flatMap
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Flat f] (y : Y)
    (hY : ∃! p : Ideal (Y.presheaf.stalk y), p ∈ minimalPrimes _) :
    ∃! p : Ideal (X.presheaf.stalk (f y)), p ∈ minimalPrimes _ :=
  existsUnique_minimalPrime_of_flat_localHom (f.stalkMap y).hom (Flat.stalkMap f y) hY

private theorem isIso_residueFieldMap_comp_of_isOpenImmersion {X Y Y' Z : Scheme.{u}}
    (a : X ⟶ Y) (m : Y ⟶ Z) (b : Z ⟶ Y') [IsOpenImmersion a] [IsOpenImmersion b] (x : X)
    [hm : IsIso (m.residueFieldMap (a x))] : IsIso ((a ≫ m ≫ b).residueFieldMap x) := by
  rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' (IsIso.comp_isIso'
    (Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion b _) hm)
    (Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion a x)

/-! ### The three parts of the theorem -/

/-- **Stacks Project, Tag 04LT.** Every local ring of the arrows of a groupoid scheme over a
field has a unique minimal prime ideal. -/
@[stacks 04LT "part (1)"]
public theorem existsUnique_minimalPrime_stalk {S : Scheme.{u}} (G : GroupoidScheme S)
    (k : Type u) [Field k] (hU : G.objects.left = Spec (.of k))
    (r : G.arrows.left) :
    ∃! p : Ideal (G.arrows.left.presheaf.stalk r),
      p ∈ minimalPrimes (G.arrows.left.presheaf.stalk r) := by
  classical
  let structureMap : Spec (.of k) ⟶ S := eqToHom hU.symm ≫ G.objects.hom
  have hObjects : G.objects = Over.mk structureMap := over_eq_of_left_eq G.objects hU
  obtain ⟨k', hField, hAlg, i, r', hr, hs, ht⟩ :=
    exists_isIso_source_target_over_isAlgClosed structureMap G hObjects r
  let _ : Field k' := hField
  let _ : IsAlgClosed k' := hAlg
  let U' : Over S := Over.mk (Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap)
  let g : U' ⟶ G.objects := extensionMap structureMap i ≫ eqToHom hObjects.symm
  let R := GroupoidScheme.restrict G g
  let G' := R.groupoid
  have hU' : G'.objects.left = Spec (.of k') := congrArg Over.left R.objects_eq
  let rPoint : G'.arrows.left :=
    (eqToHom R.arrows_eq.symm).left (r' (IsLocalRing.closedPoint k'))
  have hpoint : (eqToHom R.arrows_eq).left rPoint = r' (IsLocalRing.closedPoint k') := by
    change (((eqToHom R.arrows_eq.symm).left ≫ (eqToHom R.arrows_eq).left)
      (r' (IsLocalRing.closedPoint k'))) = _
    simp
  have : IsIso ((eqToHom R.arrows_eq).left) :=
    inferInstanceAs (IsIso ((Over.forget S).map (eqToHom R.arrows_eq)))
  have : IsIso ((eqToHom R.objects_eq.symm).left) :=
    inferInstanceAs (IsIso ((Over.forget S).map (eqToHom R.objects_eq.symm)))
  have : IsIso (G'.source.left.residueFieldMap rPoint) := by
    rw [R.source_eq]
    exact isIso_residueFieldMap_comp_of_isOpenImmersion (eqToHom R.arrows_eq).left
      (restrictionSource G g).left (eqToHom R.objects_eq.symm).left rPoint (hm := by
        rw [hpoint]
        simpa [g] using hs)
  have : IsIso (G'.target.left.residueFieldMap rPoint) := by
    rw [R.target_eq]
    exact isIso_residueFieldMap_comp_of_isOpenImmersion (eqToHom R.arrows_eq).left
      (restrictionTarget G g).left (eqToHom R.objects_eq.symm).left rPoint (hm := by
        rw [hpoint]
        simpa [g] using ht)
  have hLift := existsUnique_minimalPrime_stalk_of_irreducibleComponent rPoint
    (existsUnique_irreducibleComponent_at_point_of_identityComponent G' k' hU'
      (existsUnique_irreducibleComponent_containing_identity_of_isSepClosed G' k' hU') rPoint)
  have : Flat (restrictionArrowsToArrows G g).left := by
    have hflat := flat_restrictionDiagramMorphisms G g k k'
      (eqToIso hU) (Iso.refl _) ⟨11, by decide⟩
    convert hflat using 1 <;> rfl
  let f := (eqToHom R.arrows_eq).left ≫ (restrictionArrowsToArrows G g).left
  have : Flat f := by infer_instance
  have hfr : f rPoint = r := by
    change (restrictionArrowsToArrows G g).left
      ((eqToHom R.arrows_eq).left rPoint) = r
    rwa [hpoint]
  have hDown := existsUnique_minimalPrime_stalk_of_flatMap f rPoint hLift
  rwa [hfr] at hDown

/-- **Stacks Project, Tag 04LT.** There is exactly one irreducible component of the arrow scheme
containing the identity section. -/
@[stacks 04LT "part (2)"]
public theorem existsUnique_irreducibleComponent_containing_identity
    {S : Scheme.{u}} (G : GroupoidScheme S) (k : Type u) [Field k]
    (hU : G.objects.left = Spec (.of k)) :
    ∃! Z : irreducibleComponents G.arrows.left,
      Set.range G.identity.left ⊆ (Z : Set G.arrows.left) := by
  classical
  let x : G.arrows.left := G.identity.left (hU.symm ▸ IsLocalRing.closedPoint k)
  obtain ⟨Z, hxZ, hZ⟩ := existsUnique_irreducibleComponent_of_unique_minimalPrime_stalk
    x (existsUnique_minimalPrime_stalk G k hU x)
  exact ⟨Z, (range_identity_subset_iff G hU _ _).2 hxZ, fun W hW => hZ W (hW ⟨_, rfl⟩)⟩

private theorem existsUnique_minimalPrime_stalk_of_flat_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
    (hX : ∀ x : X, ∃! p : Ideal (X.presheaf.stalk x), p ∈ minimalPrimes _) :
    ∀ y : Y, ∃! p : Ideal (Y.presheaf.stalk y), p ∈ minimalPrimes _ := by
  intro y
  obtain ⟨x, rfl⟩ := f.surjective y
  exact existsUnique_minimalPrime_stalk_of_flatMap f x (hX x)

private theorem existsUnique_minimalPrime_stalk_restrictionArrows
    {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects)
    (K : Type u) [Field K] (hU' : U'.left = Spec (.of K)) :
    ∀ r : (restrictionArrows G g).left,
      ∃! p : Ideal ((restrictionArrows G g).left.presheaf.stalk r),
        p ∈ minimalPrimes _ := by
  let R := GroupoidScheme.restrict G g
  let f : R.groupoid.arrows.left ⟶ (restrictionArrows G g).left :=
    (Over.forget S).map (eqToHom R.arrows_eq)
  have : IsIso f := inferInstance
  exact existsUnique_minimalPrime_stalk_of_flat_surjective f
    (existsUnique_minimalPrime_stalk R.groupoid K
      ((congrArg Over.left R.objects_eq).trans hU'))

private theorem existsUnique_minimalPrime_stalk_pullback_source_target
    {S : Scheme.{u}} (G : GroupoidScheme S) (k K : Type u) [Field k] [Field K]
    (hU : G.objects.left = Spec (.of k)) {U' : Over S} (g : U' ⟶ G.objects)
    (hU' : U'.left = Spec (.of K)) (m : G.arrows ⟶ G.objects)
    (hm : m = G.source ∨ m = G.target) :
    ∀ r : pullback (C := Scheme) m.left g.left,
      ∃! p : Ideal ((pullback (C := Scheme) m.left g.left).presheaf.stalk r),
        p ∈ minimalPrimes _ := by
  have hR := existsUnique_minimalPrime_stalk_restrictionArrows G g K hU'
  rcases hm with rfl | rfl
  · let q := (pullback.snd (pullback.snd g G.target) (pullback.fst G.source g)).left
    have : Flat q :=
      flat_restrictionDiagramMorphisms G g k K (eqToIso hU) (eqToIso hU') 8
    have : Surjective q :=
      surjective_restrictionDiagramMorphisms G g k K (eqToIso hU) (eqToIso hU') 8
    let e := PreservesPullback.iso (Over.forget S) G.source g
    exact existsUnique_minimalPrime_stalk_of_flat_surjective e.hom
      (existsUnique_minimalPrime_stalk_of_flat_surjective q hR)
  · let q := (pullback.fst (pullback.snd g G.target) (pullback.fst G.source g)).left
    have : Flat q :=
      flat_restrictionDiagramMorphisms G g k K (eqToIso hU) (eqToIso hU') 7
    have : Surjective q :=
      surjective_restrictionDiagramMorphisms G g k K (eqToIso hU) (eqToIso hU') 7
    let e := PreservesPullback.iso (Over.forget S) g G.target ≪≫
      pullbackSymmetry g.left G.target.left
    exact existsUnique_minimalPrime_stalk_of_flat_surjective e.hom
      (existsUnique_minimalPrime_stalk_of_flat_surjective q hR)

private theorem existsUnique_irreducibleComponent_baseChange_source_target
    {S : Scheme.{u}} (G : GroupoidScheme S) (k K : Type u) [Field k] [Field K]
    (hU : G.objects.left = Spec (.of k)) (i : Spec (.of K) ⟶ Spec (.of k))
    (m : G.arrows ⟶ G.objects) (hm : m = G.source ∨ m = G.target) :
    ∀ r : pullback (C := Scheme) (m.left ≫ eqToHom hU) i,
      ∃! Z : irreducibleComponents (pullback (C := Scheme) (m.left ≫ eqToHom hU) i),
        r ∈ Z.1 := by
  let U' : Over S := Over.mk (i ≫ eqToHom hU.symm ≫ G.objects.hom)
  let g : U' ⟶ G.objects := Over.homMk (i ≫ eqToHom hU.symm) (by simp [U'])
  let f : pullback (C := Scheme) m.left g.left ⟶
      pullback (C := Scheme) (m.left ≫ eqToHom hU) i :=
    pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (eqToHom hU) (by simp) (by simp [g])
  have : IsIso f := by dsimp [f]; infer_instance
  have h := existsUnique_minimalPrime_stalk_of_flat_surjective f
    (existsUnique_minimalPrime_stalk_pullback_source_target G k K hU g rfl m hm)
  exact fun r => existsUnique_irreducibleComponent_of_unique_minimalPrime_stalk r (h r)

/-- The Galois action fixes the unique geometric component through a point of the base change
lying over a rational point. -/
private theorem galoisAction_fixes_component_through_point
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (e : Spec (.of k) ⟶ X)
    (e' : Spec (.of K) ⟶
      pullback (C := Scheme) f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (he'fst : e' ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ e)
    (he'snd : e' ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))) = 𝟙 _)
    (W : irreducibleComponents
      (pullback (C := Scheme) f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    (hrW : e' (IsLocalRing.closedPoint K) ∈ W.1)
    (hW : ∀ W' : irreducibleComponents
      (pullback (C := Scheme) f (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
        e' (IsLocalRing.closedPoint K) ∈ W'.1 → W' = W)
    (σ : MulOpposite (K ≃ₐ[k] K)) :
    ConcreteCategory.hom
      ((galoisActionOnGeometricIrreducibleComponents k K (Over.mk f)).ρ σ).asHom
      (⟨W.1, W.2⟩ : (galoisActionOnGeometricIrreducibleComponents k K (Over.mk f)).V) =
      ⟨W.1, W.2⟩ := by
  have hσbase : Spec.map (CommRingCat.ofHom σ.unop.toRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext x
    exact σ.unop.commutes x
  have hcomm : e' ≫ galoisBaseChangeMap k K X f σ.unop =
      Spec.map (CommRingCat.ofHom σ.unop.toRingEquiv.toRingHom) ≫ e' := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, galoisBaseChangeMap_fst, he'fst, Category.assoc, he'fst,
        ← Category.assoc, hσbase]
    · rw [Category.assoc, galoisBaseChangeMap_snd, ← Category.assoc, he'snd,
        Category.assoc, he'snd]
      simp
  have hfixr : (galoisBaseChangeMap k K X f σ.unop).base (e' (IsLocalRing.closedPoint K)) =
      e' (IsLocalRing.closedPoint K) :=
    (congrArg (fun q : Spec (.of K) ⟶
      pullback (C := Scheme) f (Spec.map (CommRingCat.ofHom (algebraMap k K))) =>
        q (IsLocalRing.closedPoint K)) hcomm).trans (congrArg e' (Subsingleton.elim _ _))
  let eh := Scheme.homeoOfIso ((galoisActionOnBaseChange k K (Over.mk f)).ρAut σ).asIso
  have hcomp : (galoisBaseChangeMap k K X f σ.unop).base '' (W.1 : Set _) ∈
      irreducibleComponents (pullback (C := Scheme) f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    image_mem_irreducibleComponents_of_homeomorph eh W.2
  let W' : (galoisActionOnGeometricIrreducibleComponents k K (Over.mk f)).V := ⟨W.1, W.2⟩
  change ConcreteCategory.hom
    ((galoisActionOnGeometricIrreducibleComponents k K (Over.mk f)).ρ σ).asHom W' = W'
  apply Subtype.ext
  rw [galoisActionOnGeometricIrreducibleComponents_ρ_apply_coe]
  exact congrArg Subtype.val (hW ⟨_, hcomp⟩ ⟨_, hrW, hfixr⟩)

private theorem geometricallyIrreducible_component_of_rationalPoint
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (e : Spec (.of k) ⟶ X)
    (hef : e ≫ f = 𝟙 _) (Z : irreducibleComponents X) (heZ : Set.range e ⊆ Z.1)
    (hunique : ∀ r : pullback (C := Scheme) f (Spec.map (CommRingCat.ofHom (algebraMap k K))),
      ∃! W : irreducibleComponents (pullback (C := Scheme) f (Spec.map (CommRingCat.ofHom
        (algebraMap k K)))), r ∈ W.1) :
    GeometricallyIrreducible ((Scheme.IdealSheafData.vanishingIdeal
      (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ : Closeds X)).subschemeι ≫ f) := by
  classical
  let e' : Spec (.of K) ⟶
      pullback (C := Scheme) f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ e) (𝟙 _)
      (by simp [Category.assoc, hef])
  have he'fst : e' ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ e := pullback.lift_fst _ _ _
  have he'snd : e' ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))) = 𝟙 _ :=
    pullback.lift_snd _ _ _
  let r := e' (IsLocalRing.closedPoint K)
  obtain ⟨W, hrW, hW⟩ := hunique r
  obtain ⟨T, hT, hpre⟩ :=
    (fixed_geometricComponent_iff_exists_geometricallyIrreducible_component
        k K X f ⟨W.1, W.2⟩).mp (galoisAction_fixes_component_through_point k K f e e'
          he'fst he'snd W hrW hW)
  have hrT : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) r ∈ T.1 := by
    change r ∈ (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base ⁻¹' (T : Set X)
    rw [hpre]
    exact hrW
  have hrZ : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) r ∈ Z.1 := by
    have hpoint : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) r =
        e (Spec.map (CommRingCat.ofHom (algebraMap k K)) (IsLocalRing.closedPoint K)) := by
      change (e' ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (IsLocalRing.closedPoint K) = _
      rw [he'fst]
      rfl
    rw [hpoint]
    exact heZ ⟨_, rfl⟩
  have hbase := existsUnique_irreducibleComponent_of_unique_minimalPrime_stalk
    ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) r)
    (existsUnique_minimalPrime_stalk_of_flatMap
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) r
      (existsUnique_minimalPrime_stalk_of_irreducibleComponent r ⟨W, hrW, hW⟩))
  have hTZ : T = Z := hbase.unique hrT hrZ
  cases hTZ
  exact hT

/-- A component through the identity is geometrically irreducible via the source or target. -/
private theorem geometricallyIrreducible_component_of_identity
    {S : Scheme.{u}} (G : GroupoidScheme S) (k : Type u) [Field k]
    (hU : G.objects.left = Spec (.of k)) (Z : irreducibleComponents G.arrows.left)
    (he : Set.range G.identity.left ⊆ (Z : Set G.arrows.left)) (m : G.arrows ⟶ G.objects)
    (hm : m = G.source ∨ m = G.target) (hid : G.identity ≫ m = 𝟙 _) :
    GeometricallyIrreducible
      ((Scheme.IdealSheafData.vanishingIdeal
        (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ :
          Closeds G.arrows.left)).subschemeι ≫ m.left ≫ eqToHom hU) := by
  apply geometricallyIrreducible_component_of_rationalPoint k (SeparableClosure k)
    (m.left ≫ eqToHom hU) (eqToHom hU.symm ≫ G.identity.left)
  · have h : G.identity.left ≫ m.left = 𝟙 _ := congrArg Over.Hom.left hid
    rw [Category.assoc, ← Category.assoc G.identity.left, h]
    simp
  · rintro x ⟨y, rfl⟩
    exact he ⟨(eqToHom hU.symm) y, rfl⟩
  · exact existsUnique_irreducibleComponent_baseChange_source_target G k
      (SeparableClosure k) hU _ m hm

/-- **Stacks Project, Tag 04LT.** The component containing the identity is geometrically
irreducible over the field via the source morphism. -/
@[stacks 04LT "part (3), source",
  ega "IV 15.6.10" "partial",
  sga "3 VIA 2.6.2" "more general",
  sga "3 VIA 2.6.5" "more general"]
public theorem geometricallyIrreducible_irreducibleComponent_of_identity_source
    {S : Scheme.{u}} (G : GroupoidScheme S) (k : Type u) [Field k]
    (hU : G.objects.left = Spec (.of k)) (Z : irreducibleComponents G.arrows.left)
    (he : Set.range G.identity.left ⊆ (Z : Set G.arrows.left)) :
    GeometricallyIrreducible
      ((Scheme.IdealSheafData.vanishingIdeal
        (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ :
          Closeds G.arrows.left)).subschemeι ≫ G.source.left ≫ eqToHom hU) :=
  geometricallyIrreducible_component_of_identity G k hU Z he G.source (Or.inl rfl)
    G.source_identity

/-- **Stacks Project, Tag 04LT.** The component containing the identity is geometrically
irreducible over the field via the target morphism. -/
@[stacks 04LT "part (3), target",
  ega "IV 15.6.10" "partial",
  sga "3 VIA 2.6.2" "more general",
  sga "3 VIA 2.6.5" "more general"]
public theorem geometricallyIrreducible_irreducibleComponent_of_identity_target
    {S : Scheme.{u}} (G : GroupoidScheme S) (k : Type u) [Field k]
    (hU : G.objects.left = Spec (.of k)) (Z : irreducibleComponents G.arrows.left)
    (he : Set.range G.identity.left ⊆ (Z : Set G.arrows.left)) :
    GeometricallyIrreducible
      ((Scheme.IdealSheafData.vanishingIdeal
        (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ :
          Closeds G.arrows.left)).subschemeι ≫ G.target.left ≫ eqToHom hU) :=
  geometricallyIrreducible_component_of_identity G k hU Z he G.target (Or.inr rfl)
    G.target_identity

end AlgebraicGeometry.GroupoidScheme
