module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.TensorHomTorAmplitudeComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BraidingIsoEqCanonicalBraiding
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightUnitTransCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorCommShiftTwoField
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparisonBraiding
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparisonCommShift
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionCommShift
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.UnboundedLocalization
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.BraidingIsoSymmetry
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map of Tag 0B4C is natural and compatible with distinguished triangles

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces, so that `i_*` is exact and
`R ℰom(𝒪_Z, -) : D(𝒪_X) ⥤ D(𝒪_Z)` is its right adjoint ([Stacks, Tag 0A76]). [Stacks, Tag 0B4C]
says that for every `K` in `D(𝒪_X)` there is a canonical map

`Li^*K ⊗^L_{𝒪_Z} R ℰom(𝒪_Z, 𝒪_X) ⟶ R ℰom(𝒪_Z, K)`

in `D(𝒪_Z)`, functorial in `K` and compatible with distinguished triangles. The map itself is
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.derivedPullbackTensorSheafHomMap`
and its naturality is `derivedPullbackTensorSheafHomMap_natural`. This file assembles it into a
morphism of functors and proves that this morphism commutes with the shift, for the commutations
of source and target with the shift that the source has in mind: `Li^*` carries its commutation as
a total left derived functor ([Stacks, Tag 06YJ]), `- ⊗^L R ℰom(𝒪_Z, 𝒪_X)` the one of the derived
tensor product ([Stacks, Tag 06YU]), and `R ℰom(𝒪_Z, -)` the one it has as the right adjoint of the
exact functor `i_*`. Both functors are exact for these commutations, so a distinguished triangle
`K ⟶ L ⟶ M ⟶ K[1]` is carried to a morphism between the two image triangles: this is what
"compatible with distinguished triangles" says.

## Main definitions

* `derivedPullbackTensorSheafHomNatTrans`: the canonical map of [Stacks, Tag 0B4C] as a morphism
  of functors `D(𝒪_X) ⥤ D(𝒪_Z)`.
* `derivedPullbackTensorSheafHomCommShift`: the commutation of the source with the shift.
* `derivedSheafHomExactSupportCommShift`: the commutation of `R ℰom(𝒪_Z, -)` with the shift.

## Main results

* `commShift_derivedPullbackTensorSheafHomNatTrans`: **[Stacks, Tag 0B4C]**, the canonical map
  commutes with the shift.
* `isTriangulated_derivedPullbackTensorSheafHom` and `isTriangulated_derivedSheafHomExactSupport`:
  its source and target are exact functors.

## The proof

The canonical map is the transpose under `i_* ⊣ R ℰom(𝒪_Z, -)` of the composite `σ_K` of
`derivedPullbackTensorSheafHomMateMap`, and the transpose of a morphism of functors commuting with
the shift commutes with the shift. The composite `σ_K` runs through the commutativity constraint of
[Stacks, Tag 0FPT] twice, which is not known to commute with the shift. It is rewritten without
it: `σ_K` is equal to

`i_*(Li^*K ⊗^L E) ≅ Ri_*(Li^*K ⊗^L E) ≅ K ⊗^L Ri_*E ⟶ K ⊗^L 𝒪_X ≅ K`,

with `E = R ℰom(𝒪_Z, 𝒪_X)`, where the second arrow is the inverse of the projection formula with
the varying factor `K` on the left. That projection formula is the transpose under `Li^* ⊣ Ri_*`
of the comparison of [Stacks, Tag 079U] in its first variable followed by the counit, and each
piece commutes with the shift: the comparison of the two models of `i_*`
(`commShift_derivedPushforwardComparison_hom`), the adjunction `Li^* ⊣ Ri_*`
(`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_commShift`), the comparison
of [Stacks, Tag 079U] in its first variable (`Stacks.Cohomology.DerivedPullbackTensor`
`.derivedPullbackTensorIso_bifunctorComparisonFlip_commShift`),
the action of the derived tensor product on morphisms, and the right unit constraint
(`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.commShift_rightUnitTrans`). The rewriting
uses that the comparison of [Stacks, Tag 079U] is braided
(`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_braiding`) and that the
commutativity constraint is natural and involutive.

## References

* [Stacks Project, Tag 0B4C](https://stacks.math.columbia.edu/tag/0B4C)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod
open RingedSpaceModuleAdjunction
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula

attribute [local instance] HasDerivedCategory.standard

universe u

/-! ### Rearrangements in bare categories -/

namespace Stacks.Duality.ExactSupportDerivedTensorHomMapTriangles

section Bare

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (TA : C ⥤ C ⥤ C) (TB : D ⥤ D ⥤ D)
  (α : Functor.uncurry.obj TA ⋙ L ⟶ L.prod L ⋙ Functor.uncurry.obj TB)

/-- **The projection formula with the varying factor on the left, through the braidings.** If the
comparison `α` carries a braiding `βA` of `TA` to a braiding `βB` of `TB`, and `βB` is natural and
involutive, then the projection-formula map `TA(R G, H) ⟶ R TB(G, L H)` conjugated by the two
braidings is the transpose of `α` at `(H, R G)` followed by `TB(L H, -)` of the counit at `G`. -/
theorem braiding_comp_adjunctionTensorMap_comp_braiding
    (βA : ∀ M N : C, (TA.obj M).obj N ⟶ (TA.obj N).obj M)
    (βB : ∀ M N : D, (TB.obj M).obj N ⟶ (TB.obj N).obj M)
    (hcompat : ∀ M N : C, L.map (βA M N) ≫ α.app (N, M) = α.app (M, N) ≫ βB (L.obj M) (L.obj N))
    (hnat : ∀ {M M' N N' : D} (f : M ⟶ M') (g : N ⟶ N'),
      (Functor.uncurry.obj TB).map (f ×ₘ g) ≫ βB M' N' =
        βB M N ≫ (Functor.uncurry.obj TB).map (g ×ₘ f))
    (hsymm : ∀ M N : D, βB M N ≫ βB N M = 𝟙 _) (G : D) (H : C) :
    βA H (R.obj G) ≫
        adjunctionTensorMap adj (Functor.uncurry.obj TA) (Functor.uncurry.obj TB) α G H ≫
          R.map (βB G (L.obj H)) =
      adj.unit.app ((TA.obj H).obj (R.obj G)) ≫
        R.map (α.app (H, R.obj G) ≫ (TB.obj (L.obj H)).map (adj.counit.app G)) := by
  have hu : βA H (R.obj G) ≫ adj.unit.app ((Functor.uncurry.obj TA).obj (R.obj G, H)) =
      adj.unit.app ((TA.obj H).obj (R.obj G)) ≫ R.map (L.map (βA H (R.obj G))) :=
    adj.unit.naturality (βA H (R.obj G))
  rw [adjunctionTensorMap_eq_unit_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hu]
  simp only [Category.assoc, ← R.map_comp]
  congr 2
  have h2 := hnat (𝟙 (L.obj H)) (adj.counit.app G)
  rw [Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left] at h2
  rw [reassoc_of% hcompat H (R.obj G), ← reassoc_of% h2, hsymm]
  exact congrArg (fun x => _ ≫ x) (Category.comp_id _)

/-- A square read through two equations of its vertical edges. -/
theorem square_of_eq {X Y : Type*} [Category X] [Category Y] (F : X ⥤ Y) {x x' : X}
    {y₀ y₁ : Y} {p p' : x ⟶ x'} {a : F.obj x' ⟶ y₁} {b : F.obj x ⟶ y₀} {q q' : y₀ ⟶ y₁}
    (h : F.map p ≫ a = b ≫ q) (hp : p = p') (hq : q = q') : F.map p' ≫ a = b ≫ q' := by
  subst hp hq
  exact h

/-- A square in one category read through two equations of its horizontal edges. -/
theorem square_of_eq' {X : Type*} [Category X] {x₀ x₁ y₀ y₁ : X} {a : x₀ ⟶ x₁}
    {b : y₀ ⟶ y₁} {p p' : x₁ ⟶ y₁} {q q' : x₀ ⟶ y₀}
    (h : a ≫ p = q ≫ b) (hp : p = p') (hq : q = q') : a ≫ p' = q' ≫ b := by
  subst hp hq
  exact h

/-- A composite equal to the identity, read through two equations. -/
theorem comp_eq_id_of_eq₂ {X : Type*} [Category X] {x y : X} {p p' : x ⟶ y} {q q' : y ⟶ x}
    (h : p ≫ q = 𝟙 _) (hp : p = p') (hq : q = q') : p' ≫ q' = 𝟙 _ := by
  subst hp hq
  exact h

/-- An identity morphism composed with a unit and a morphism under a functor, with identities. -/
theorem id_comp_comp_id_comp_comp_id {X : Type*} [Category X] {x₀ x₁ x₂ : X} (a : x₀ ⟶ x₁)
    (b : x₁ ⟶ x₂) : 𝟙 _ ≫ a ≫ 𝟙 _ ≫ b ≫ 𝟙 _ = a ≫ b := by
  simp

/-- The rearrangement identifying the two descriptions of the composite of [Stacks, Tag 0B4C]. -/
theorem chain_eq {X : Type*} [Category X]
    {a₀ a₁ a₀' a₂ a₃ a₃' a₄ a₄' a₅ k : X}
    {Pb : a₀ ⟶ a₁} {c₁ : a₁ ⟶ a₂} {c₀ : a₀ ⟶ a₀'} {Rb : a₀' ⟶ a₂} {ipf : a₂ ⟶ a₃}
    {bX' : a₃ ⟶ a₃'} {ipf' : a₀' ⟶ a₃'} {t₁ : a₃ ⟶ a₅} {t₂ : a₅ ⟶ a₄} {s : a₃' ⟶ a₄'}
    {bO : a₄ ⟶ a₄'} {r : a₄' ⟶ k} {lam : a₄ ⟶ k}
    (hc : Pb ≫ c₁ = c₀ ≫ Rb) (hi : ipf' = Rb ≫ ipf ≫ bX') (hn : bX' ≫ s = (t₁ ≫ t₂) ≫ bO)
    (hl : lam = bO ≫ r) :
    c₀ ≫ 𝟙 _ ≫ ipf' ≫ s ≫ r = Pb ≫ c₁ ≫ ipf ≫ t₁ ≫ t₂ ≫ lam := by
  rw [Category.id_comp, reassoc_of% hc, hi, hl]
  simp only [Category.assoc, reassoc_of% hn]

/-- The inverse of a composite of three morphisms, each with a given right inverse. -/
theorem inv_eq_of_comp {X : Type*} [Category X] {x₀ x₁ x₂ x₃ : X} (e : x₀ ⟶ x₃) (hI : IsIso e)
    {a : x₀ ⟶ x₁} {b : x₁ ⟶ x₂} {c : x₂ ⟶ x₃} {c' : x₃ ⟶ x₂} {b' : x₂ ⟶ x₁} {a' : x₁ ⟶ x₀}
    (he : a ≫ b ≫ c = e) (hc : c ≫ c' = 𝟙 _) (hb : b ≫ b' = 𝟙 _) (ha : a ≫ a' = 𝟙 _) :
    CategoryTheory.inv (I := hI) e = c' ≫ b' ≫ a' := by
  refine IsIso.inv_eq_of_hom_inv_id ?_
  rw [← he]
  simp only [Category.assoc, reassoc_of% hc, reassoc_of% hb, ha]

/-- A composite of three isomorphisms is an isomorphism, given inverses of the outer two. -/
theorem isIso_comp_of_inverses {X : Type*} [Category X] {x₀ x₁ x₂ x₃ : X} (e : x₀ ⟶ x₃)
    {a : x₀ ⟶ x₁} {b : x₁ ⟶ x₂} {c : x₂ ⟶ x₃} {c' : x₃ ⟶ x₂} {a' : x₁ ⟶ x₀} (hb : IsIso b)
    (he : a ≫ b ≫ c = e) (hc : c ≫ c' = 𝟙 _) (hc' : c' ≫ c = 𝟙 _) (ha : a ≫ a' = 𝟙 _)
    (ha' : a' ≫ a = 𝟙 _) : IsIso e := by
  subst he
  have : IsIso a := ⟨a', ha, ha'⟩
  have : IsIso c := ⟨c', hc, hc'⟩
  infer_instance

/-- A composite equal to the identity under a functor, read through an equation. -/
theorem map_comp_eq_id_of_eq {X Y : Type*} [Category X] [Category Y] (F : X ⥤ Y) {x y : X}
    {p : x ⟶ y} {q q' : y ⟶ x} (h : p ≫ q = 𝟙 _) (hq : q = q') : F.map p ≫ F.map q' = 𝟙 _ := by
  rw [← hq, ← F.map_comp, h, F.map_id]

/-- A composite equal to the identity, read through an equation. -/
theorem comp_eq_id_of_eq' {X : Type*} [Category X] {x y : X} {p : x ⟶ y} {q q' : y ⟶ x}
    (h : p ≫ q = 𝟙 _) (hq : q = q') : p ≫ q' = 𝟙 _ := hq ▸ h

/-- A square with two identities inserted, read without them and with the first edge split. -/
theorem square_of_ids {X Y Z : Type*} [Category X] [Category Y] [Category Z] (T : X ⥤ Y ⥤ Z)
    {x₀ x₁ x₂ : X} (a : x₀ ⟶ x₁) (b : x₁ ⟶ x₂) (y : Y) {z₁ z₂ : Z}
    {v : (T.obj x₂).obj y ⟶ z₂} {u : (T.obj x₀).obj y ⟶ z₁} {g : z₁ ⟶ z₂}
    {i : (T.obj x₂).obj y ⟶ (T.obj x₂).obj y} {j : z₁ ⟶ z₁}
    (h : (T.map (a ≫ b)).app y ≫ i ≫ v = u ≫ j ≫ g) (hi : i = 𝟙 _) (hj : j = 𝟙 _) :
    u ≫ g = ((T.map a).app y ≫ (T.map b).app y) ≫ v := by
  rw [hi, hj, Category.id_comp, Category.id_comp, Functor.map_comp, NatTrans.comp_app] at h
  exact h.symm

/-- A transpose through a unit, with identities inserted, read through an equation of the
transposed morphisms. -/
theorem eq_unit_comp_of_eq {X Y : Type*} [Category X] [Category Y] (G : X ⥤ Y) {y₀ : Y}
    {x₀ x₁ : X} {τ : y₀ ⟶ G.obj x₁} {η : y₀ ⟶ G.obj x₀} {m m' : x₀ ⟶ x₁}
    {e : G.obj x₀ ⟶ G.obj x₀} (hτ : τ = η ≫ G.map m') (hm : m = m') (he : e = 𝟙 _) :
    τ = 𝟙 _ ≫ η ≫ e ≫ G.map m ≫ 𝟙 _ := by
  rw [hτ, hm, he, Category.id_comp, Category.id_comp, Category.comp_id]

/-- The third square of the image of a triangle under a morphism of functors commuting with the
shift. -/
theorem shift_square {X Y : Type*} [Category X] [Category Y] [HasShift X ℤ] [HasShift Y ℤ]
    {F G : X ⥤ Y} [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
    {x₁ x₃ : X} (f : x₃ ⟶ x₁⟦(1 : ℤ)⟧) :
    (F.map f ≫ (F.commShiftIso (1 : ℤ)).hom.app x₁) ≫ (τ.app x₁)⟦(1 : ℤ)⟧' =
      τ.app x₃ ≫ G.map f ≫ (G.commShiftIso (1 : ℤ)).hom.app x₁ := by
  rw [Category.assoc, NatTrans.shift_app_comm, ← Category.assoc, τ.naturality, Category.assoc]

end Bare

end Stacks.Duality.ExactSupportDerivedTensorHomMapTriangles

open Stacks.Duality.ExactSupportDerivedTensorHomMapTriangles

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

/-! ### The derived tensor product in its first variable, at the spelling of `D(𝒪)` -/

/-- `- ⊗^L M` on the derived category of a ringed space, as a functor of
`DerivedCategory (SheafOfModules (structureSheafRing W))`, the spelling at which the derived
pullback and pushforward are stated. -/
abbrev tensorRightFunctor (W : RingedSpace.{u, u})
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing W))) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing W)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing W)) :=
  (derivedTensorProductFunctor W.sheaf).flip.obj M

/-- `K ↦ K ⊗^L g` for a morphism `g` of the derived category of a ringed space, as a morphism of
the functors `tensorRightFunctor`. -/
abbrev tensorRightMap (W : RingedSpace.{u, u})
    {M M' : DerivedCategory (SheafOfModules.{u} (structureSheafRing W))} (g : M ⟶ M') :
    tensorRightFunctor W M ⟶ tensorRightFunctor W M' :=
  (derivedTensorProductFunctor W.sheaf).flip.map g

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-! ### The canonical map as a morphism of functors -/

/-- **[Stacks, Tag 0B4C], the canonical map as a morphism of functors**
`Li^*(-) ⊗^L R ℰom(𝒪_Z, 𝒪_X) ⟶ R ℰom(𝒪_Z, -)` of `D(𝒪_X) ⥤ D(𝒪_Z)`. Its component at `K` is
`derivedPullbackTensorSheafHomMap K` and its naturality is
`derivedPullbackTensorSheafHomMap_natural`. -/
@[stacks 0B4C "the canonical map, functorial in the complex, as a morphism of functors"]
def derivedPullbackTensorSheafHomNatTrans :
    S.derivedPullbackTensorSheafHom ⟶ S.derivedSheafHomExactSupport where
  app K := S.derivedPullbackTensorSheafHomMap K
  naturality _ _ k := S.derivedPullbackTensorSheafHomMap_natural k

/-- The components of `derivedPullbackTensorSheafHomNatTrans`. -/
@[simp]
theorem derivedPullbackTensorSheafHomNatTrans_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    S.derivedPullbackTensorSheafHomNatTrans.app K = S.derivedPullbackTensorSheafHomMap K :=
  rfl

/-! ### The projection formula with the varying factor on the left -/

/-- The comparison of [Stacks, Tag 079U] at a fixed second argument `M`, as a morphism of
functors `Li^*(- ⊗^L M) ⟶ Li^*(-) ⊗^L Li^*M` of the first. -/
abbrev pullbackTensorComparisonFlip
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    tensorRightFunctor S.X M ⋙ derivedPullback S.i ⟶
      derivedPullback S.i ⋙ tensorRightFunctor S.Z ((derivedPullback S.i).obj M) :=
  Functor.bifunctorComparisonFlip
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso S.i).hom M

/-- The projection formula `K ⊗^L Ri_*E ⟶ Ri_*(Li^*K ⊗^L E)` with the varying factor `K` on the
left, at a fixed `E` in `D(𝒪_Z)`, as a morphism of functors of `K`: the transpose under
`Li^* ⊣ Ri_*` of the comparison `Li^*(K ⊗^L Ri_*E) ⟶ Li^*K ⊗^L Li^*Ri_*E` of
[Stacks, Tag 079U] followed by the counit of `Li^* ⊣ Ri_*` at `E` in the second factor. -/
def projectionFormulaLeftTrans
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z))) :
    tensorRightFunctor S.X ((derivedPushforward S.i).obj E) ⟶
      derivedPullback S.i ⋙ tensorRightFunctor S.Z E ⋙ derivedPushforward S.i :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft (tensorRightFunctor S.X ((derivedPushforward S.i).obj E))
      (derivedAdjunction S.i).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (S.pullbackTensorComparisonFlip ((derivedPushforward S.i).obj E) ≫
        Functor.whiskerLeft (derivedPullback S.i)
          (tensorRightMap S.Z ((derivedAdjunction S.i).counit.app E)))
      (derivedPushforward S.i) ≫
    (Functor.associator _ _ _).hom

/-- The components of `projectionFormulaLeftTrans`. -/
theorem projectionFormulaLeftTrans_app
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    (S.projectionFormulaLeftTrans E).app K =
      (derivedAdjunction S.i).unit.app
          (((derivedTensorProductFunctor S.X.sheaf).obj K).obj ((derivedPushforward S.i).obj E)) ≫
        (derivedPushforward S.i).map
          ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso S.i).hom.app
              (K, (derivedPushforward S.i).obj E) ≫
            ((derivedTensorProductFunctor S.Z.sheaf).obj ((derivedPullback S.i).obj K)).map
              ((derivedAdjunction S.i).counit.app E)) :=
  id_comp_comp_id_comp_comp_id _ _

/-- **The two projection formulas agree through the commutativity constraints.** The projection
formula of [Stacks, Tag 0B53], `Ri_*E ⊗^L K ⟶ Ri_*(E ⊗^L Li^*K)`, conjugated by the
commutativity constraints of [Stacks, Tag 0FPT] on `D(𝒪_X)` and `D(𝒪_Z)`, is the projection
formula with the varying factor on the left. The comparison of [Stacks, Tag 079U] is braided
(`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_braiding`), and the
commutativity constraint is natural and involutive. -/
theorem braidingIso_comp_projectionFormulaMap_comp_map
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    ((canonicalDerivedTensorProduct S.X.sheaf).braidingIso S.ambientSite K
          ((derivedPushforward S.i).obj E)).hom ≫
        projectionFormulaMap S.i E K ≫
          (derivedPushforward S.i).map
            ((canonicalDerivedTensorProduct S.Z.sheaf).braidingIso S.closedSite E
              ((derivedPullback S.i).obj K)).hom =
      (S.projectionFormulaLeftTrans E).app K := by
  have hX := canonicalBraidingHom_eq_braidingIso S.ambientSite
  have hZ := canonicalBraidingHom_eq_braidingIso S.closedSite
  have h := braiding_comp_adjunctionTensorMap_comp_braiding (derivedAdjunction S.i)
    (derivedTensorProductFunctor S.X.sheaf) (derivedTensorProductFunctor S.Z.sheaf)
    (pullbackTensorComparison S.i)
    (fun M N => ((canonicalDerivedTensorProduct S.X.sheaf).braidingIso S.ambientSite M N).hom)
    (fun M N => ((canonicalDerivedTensorProduct S.Z.sheaf).braidingIso S.closedSite M N).hom)
    (fun M N => square_of_eq _
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_braiding S.i M N)
      (hX M N) (hZ _ _))
    (fun f g => square_of_eq'
      (Stacks.Cohomology.DerivedPullbackTensor.canonicalBraidingHom_naturality S.Z f g)
      (hZ _ _) (hZ _ _))
    (fun M N => comp_eq_id_of_eq₂
      (Stacks.Cohomology.SupportedComplexes.canonicalBraidingHom_symmetry S.Z M N)
      (hZ M N) (hZ N M)) E K
  exact h.trans (S.projectionFormulaLeftTrans_app E K).symm

/-- At `E = R ℰom(𝒪_Z, 𝒪_X)` the projection formula with the varying factor on the left is
invertible: it is the projection formula of [Stacks, Tag 0B53] between two commutativity
constraints, and the former is invertible by [Stacks, Tag 0B55]. -/
theorem isIso_projectionFormulaLeftTrans_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    IsIso ((S.projectionFormulaLeftTrans S.derivedSheafHomStructureSheaf).app K) :=
  isIso_comp_of_inverses _ (S.isIso_projectionFormulaMap_derivedSheafHomStructureSheaf K)
    (S.braidingIso_comp_projectionFormulaMap_comp_map S.derivedSheafHomStructureSheaf K)
    (map_comp_eq_id_of_eq (derivedPushforward S.i) (Iso.hom_inv_id _) rfl)
    (map_comp_eq_id_of_eq (derivedPushforward S.i) (Iso.inv_hom_id _) rfl)
    (Iso.hom_inv_id _) (Iso.inv_hom_id _)

/-- The projection formula with the varying factor on the left at `R ℰom(𝒪_Z, 𝒪_X)`, as an
isomorphism of functors of `K`. -/
def projectionFormulaLeftIso :
    tensorRightFunctor S.X ((derivedPushforward S.i).obj S.derivedSheafHomStructureSheaf) ≅
      derivedPullback S.i ⋙ tensorRightFunctor S.Z S.derivedSheafHomStructureSheaf ⋙
        derivedPushforward S.i :=
  NatIso.ofComponents
    (fun K => @asIso _ _ _ _ ((S.projectionFormulaLeftTrans S.derivedSheafHomStructureSheaf).app K)
      (S.isIso_projectionFormulaLeftTrans_app K))
    (fun f => (S.projectionFormulaLeftTrans S.derivedSheafHomStructureSheaf).naturality f)

/-! ### The adjoint composite, without the commutativity constraints -/

/-- The structure sheaf `𝒪_X` in degree zero, at the spelling
`DerivedCategory (SheafOfModules (structureSheafRing X))` of `D(𝒪_X)`. -/
abbrev ambientUnit : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)) :=
  S.ambientStructureSheafObject

/-- The trace `Ri_* R ℰom(𝒪_Z, 𝒪_X) ⟶ 𝒪_X`: back to the exact model of `i_*`, then the counit of
[Stacks, Tag 0A76] at `𝒪_X`. -/
abbrev pushforwardTrace :
    (derivedPushforward S.i).obj S.derivedSheafHomStructureSheaf ⟶ S.ambientUnit :=
  S.derivedPushforwardComparison.inv.app S.derivedSheafHomStructureSheaf ≫
    S.derivedSheafHomAdjunction.counit.app S.ambientStructureSheafObject

/-- The right unit constraint `K ⊗^L 𝒪_X ≅ K` of [Stacks, Tag 0FPT] on `D(𝒪_X)`, as a morphism of
functors out of `tensorRightFunctor`. -/
abbrev ambientRightUnitTrans :
    tensorRightFunctor S.X S.ambientUnit ⟶
      𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :=
  DerivedTensorProduct.rightUnitTrans S.ambientSite (canonicalDerivedTensorProduct S.X.sheaf)

/-- The composite that the canonical map of [Stacks, Tag 0B4C] is adjoint to, rewritten without
the commutativity constraint, as a morphism of functors of `K`:

`i_*(Li^*K ⊗^L E) ≅ Ri_*(Li^*K ⊗^L E) ≅ K ⊗^L Ri_*E ⟶ K ⊗^L 𝒪_X ≅ K`,

with `E = R ℰom(𝒪_Z, 𝒪_X)`: the comparison of the two models of `i_*`, the inverse of the
projection formula with the varying factor on the left, `K` tensored with `pushforwardTrace`, and
the right unit constraint of [Stacks, Tag 0FPT]. -/
def mateTrans :
    S.derivedPullbackTensorSheafHom ⋙ (modulePushforward S.i).mapDerivedCategory ⟶
      𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :=
  Functor.whiskerLeft S.derivedPullbackTensorSheafHom S.derivedPushforwardComparison.hom ≫
    (Functor.associator (derivedPullback S.i)
      (tensorRightFunctor S.Z S.derivedSheafHomStructureSheaf) (derivedPushforward S.i)).hom ≫
    S.projectionFormulaLeftIso.inv ≫
    tensorRightMap S.X S.pushforwardTrace ≫
    S.ambientRightUnitTrans

/-- **The two descriptions of the adjoint composite agree**: `mateTrans` has the components
`derivedPullbackTensorSheafHomMateMap`, the composite through the commutativity constraint. -/
theorem mateTrans_app_eq (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    S.mateTrans.app K = S.derivedPullbackTensorSheafHomMateMap K := by
  have hiso := S.isIso_projectionFormulaMap_derivedSheafHomStructureSheaf K
  have hX := canonicalBraidingHom_eq_braidingIso S.ambientSite
  have hZ := canonicalBraidingHom_eq_braidingIso S.closedSite
  have hsZ : ((canonicalDerivedTensorProduct S.Z.sheaf).braidingIso S.closedSite
        S.derivedSheafHomStructureSheaf ((derivedPullback S.i).obj K)).hom ≫
      ((canonicalDerivedTensorProduct S.Z.sheaf).braidingIso S.closedSite
        ((derivedPullback S.i).obj K) S.derivedSheafHomStructureSheaf).hom = 𝟙 _ :=
    comp_eq_id_of_eq₂ (Stacks.Cohomology.SupportedComplexes.canonicalBraidingHom_symmetry
      S.Z S.derivedSheafHomStructureSheaf ((derivedPullback S.i).obj K)) (hZ _ _) (hZ _ _)
  have hsX : ((canonicalDerivedTensorProduct S.X.sheaf).braidingIso S.ambientSite
        K ((derivedPushforward S.i).obj S.derivedSheafHomStructureSheaf)).hom ≫
      ((canonicalDerivedTensorProduct S.X.sheaf).braidingIso S.ambientSite
        ((derivedPushforward S.i).obj S.derivedSheafHomStructureSheaf) K).hom = 𝟙 _ :=
    comp_eq_id_of_eq₂ (Stacks.Cohomology.SupportedComplexes.canonicalBraidingHom_symmetry
      S.X K ((derivedPushforward S.i).obj S.derivedSheafHomStructureSheaf)) (hX _ _) (hX _ _)
  have hinv := inv_eq_of_comp
    ((S.projectionFormulaLeftTrans S.derivedSheafHomStructureSheaf).app K)
    (S.isIso_projectionFormulaLeftTrans_app K)
    (S.braidingIso_comp_projectionFormulaMap_comp_map S.derivedSheafHomStructureSheaf K)
    (map_comp_eq_id_of_eq (derivedPushforward S.i) hsZ rfl)
    (@IsIso.hom_inv_id _ _ _ _ _ hiso) hsX
  have hnat := (canonicalDerivedTensorProduct S.X.sheaf).braidingIso_hom_naturality S.ambientSite
    S.pushforwardTrace (𝟙 K)
  have hn := square_of_ids (derivedTensorProductFunctor S.X.sheaf)
    (S.derivedPushforwardComparison.inv.app S.derivedSheafHomStructureSheaf)
    (S.derivedSheafHomAdjunction.counit.app S.ambientStructureSheafObject) K hnat
    (CategoryTheory.Functor.map_id _ _)
    ((NatTrans.congr_app (CategoryTheory.Functor.map_id _ _) _).trans (NatTrans.id_app _ _))
  have hl := congrArg (fun x => ((canonicalDerivedTensorProduct S.X.sheaf).braidingIso
      S.ambientSite S.ambientStructureSheafObject K).hom ≫ x)
    (DerivedTensorProduct.rightUnitIso_hom_eq S.ambientSite
      (canonicalDerivedTensorProduct S.X.sheaf) K)
  exact chain_eq (S.derivedPushforwardComparison.hom.naturality _) hinv hn hl

/-! ### The canonical map is the transpose of `mateTrans` -/

/-- **The canonical map of [Stacks, Tag 0B4C] is the transpose of `mateTrans`** under
`i_* ⊣ R ℰom(𝒪_Z, -)`, as morphisms of functors. -/
theorem derivedPullbackTensorSheafHomNatTrans_eq :
    S.derivedPullbackTensorSheafHomNatTrans =
      (Functor.rightUnitor _).inv ≫
        Functor.whiskerLeft S.derivedPullbackTensorSheafHom S.derivedSheafHomAdjunction.unit ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight S.mateTrans S.derivedSheafHomExactSupport ≫
        (Functor.leftUnitor _).hom :=
  NatTrans.ext (funext fun K =>
    eq_unit_comp_of_eq S.derivedSheafHomExactSupport
      (Adjunction.homEquiv_unit S.derivedSheafHomAdjunction _ _
        (S.derivedPullbackTensorSheafHomMateMap K))
      (S.mateTrans_app_eq K) rfl)

/-! ### The commutation of the derived tensor product with the shift -/

/-- The commutation of `- ⊗^L M` with the shift on the derived category of a ringed space: the
structure field of the derived tensor product of [Stacks, Tag 06YU]. -/
@[instance_reducible]
def tensorRightFunctorCommShift (W : RingedSpace.{u, u})
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing W))) :
    (tensorRightFunctor W M).CommShift ℤ :=
  (canonicalDerivedTensorProduct W.sheaf).commShift_left M

attribute [local instance] tensorRightFunctorCommShift

/-- `K ↦ K ⊗^L g` commutes with the shift, for a morphism `g` of the derived category of a ringed
space: a field of the commutation of the derived tensor product with the shifts in both
variables. -/
theorem commShift_tensorRightMap (W : RingedSpace.{u, u})
    {M M' : DerivedCategory (SheafOfModules.{u} (structureSheafRing W))} (g : M ⟶ M') :
    NatTrans.CommShift (tensorRightMap W g) ℤ :=
  (canonicalDerivedTensorProduct W.sheaf).commShift₂.commShift_flip_map g

attribute [local instance] commShift_tensorRightMap

/-- The shift datum of the derived tensor product of a ringed space transported from the
bifunctor on K-flat models is its structure field. -/
theorem derivedTensorCommShift₂Int_eq (W : RingedSpace.{u, u}) :
    Stacks.Cohomology.DerivedPullbackTensor.derivedTensorCommShift₂Int W =
      (canonicalDerivedTensorProduct W.sheaf).commShift₂ :=
  (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedTensorProduct_commShift₂_eq W.sheaf).symm

/-! ### The comparison of the two models of `i_*` commutes with the shift -/

/-- **The comparison `i_* ≅ Ri_*` of [Stacks, Tag 0E2K] commutes with the shift**, for Mathlib's
commutation of the functor induced by the exact functor `i_*` and the commutation of the total
right derived functor `Ri_*`. Both are right derived functors of `i_*` on the homotopy category,
with units compatible with the shift, and the comparison is the induced morphism of right derived
functors. -/
theorem commShift_derivedPushforwardComparison_hom :
    NatTrans.CommShift S.derivedPushforwardComparison.hom ℤ :=
  Functor.rightDerivedNatTrans_commShift _ _ _ _
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.Z)) (ComplexShape.up ℤ)) ℤ
    (𝟙 _)

/-! ### The commutations of the source and of the target with the shift -/

/-- The commutation of `R ℰom(𝒪_Z, -)` with the shift: the one it has as the right adjoint of the
functor induced on derived categories by the exact functor `i_*` ([Stacks, Tag 0A76]). -/
@[instance_reducible]
def derivedSheafHomExactSupportCommShift : S.derivedSheafHomExactSupport.CommShift ℤ :=
  S.derivedSheafHomAdjunction.rightAdjointCommShift ℤ

/-- The commutation of `K ↦ Li^*K ⊗^L R ℰom(𝒪_Z, 𝒪_X)` with the shift: that of `Li^*` as a total
left derived functor ([Stacks, Tag 06YJ]) followed by that of the derived tensor product in its
first variable ([Stacks, Tag 06YU]). -/
@[instance_reducible]
def derivedPullbackTensorSheafHomCommShift : S.derivedPullbackTensorSheafHom.CommShift ℤ :=
  Functor.CommShift.comp (derivedPullback S.i)
    (tensorRightFunctor S.Z S.derivedSheafHomStructureSheaf)

attribute [local instance] derivedSheafHomExactSupportCommShift
  derivedPullbackTensorSheafHomCommShift

/-- The adjunction `i_* ⊣ R ℰom(𝒪_Z, -)` of [Stacks, Tag 0A76] commutes with the shift. -/
instance commShift_derivedSheafHomAdjunction : S.derivedSheafHomAdjunction.CommShift ℤ :=
  S.derivedSheafHomAdjunction.commShift_of_leftAdjoint ℤ

/-! ### Each piece commutes with the shift -/

open Stacks.Cohomology.DerivedPullbackTensor in
/-- **The comparison of [Stacks, Tag 079U] commutes with the shift in its first variable**, for
the commutations of the derived tensor products with the shift that are their structure fields.
This is
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_bifunctorComparisonFlip_commShift`
read through `derivedTensorCommShift₂Int_eq`. -/
theorem commShift_pullbackTensorComparisonFlip
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    NatTrans.CommShift (S.pullbackTensorComparisonFlip M) ℤ :=
  NatTrans.commShift_of_eq_data (by rw [derivedTensorCommShift₂Int_eq]; rfl)
    (by rw [derivedTensorCommShift₂Int_eq]; rfl) _
    (derivedPullbackTensorIso_bifunctorComparisonFlip_commShift S.i M)

/-- The projection formula with the varying factor on the left commutes with the shift. -/
theorem commShift_projectionFormulaLeftTrans
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z))) :
    NatTrans.CommShift (S.projectionFormulaLeftTrans E) ℤ := by
  have : (derivedAdjunction S.i).CommShift ℤ := derivedAdjunction_commShift S.i
  have := S.commShift_pullbackTensorComparisonFlip ((derivedPushforward S.i).obj E)
  unfold projectionFormulaLeftTrans
  infer_instance

/-- `mateTrans` commutes with the shift. -/
theorem commShift_mateTrans : NatTrans.CommShift S.mateTrans ℤ := by
  have := S.commShift_derivedPushforwardComparison_hom
  have : NatTrans.CommShift S.projectionFormulaLeftIso.hom ℤ :=
    S.commShift_projectionFormulaLeftTrans S.derivedSheafHomStructureSheaf
  have : NatTrans.CommShift S.ambientRightUnitTrans ℤ :=
    DerivedTensorProduct.commShift_rightUnitTrans S.ambientSite
  have h₁ : NatTrans.CommShift (Functor.whiskerLeft S.derivedPullbackTensorSheafHom
      S.derivedPushforwardComparison.hom) ℤ := inferInstance
  have h₂ : NatTrans.CommShift (Functor.associator (derivedPullback S.i)
      (tensorRightFunctor S.Z S.derivedSheafHomStructureSheaf) (derivedPushforward S.i)).hom ℤ :=
    inferInstance
  have h₃ : NatTrans.CommShift S.projectionFormulaLeftIso.inv ℤ := inferInstance
  have h₄ : NatTrans.CommShift (tensorRightMap S.X S.pushforwardTrace) ℤ :=
    commShift_tensorRightMap S.X S.pushforwardTrace
  unfold mateTrans
  infer_instance

/-! ### Tag 0B4C -/

/-- **[Stacks, Tag 0B4C], compatibility with distinguished triangles.** The canonical map
`Li^*K ⊗^L R ℰom(𝒪_Z, 𝒪_X) ⟶ R ℰom(𝒪_Z, K)`, as a morphism of functors of `K`, commutes with the
shift: `Li^*` carries its commutation as a total left derived functor
(`Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift`) and the derived tensor
product the one of its structure (`tensorRightFunctorCommShift`), so that the source carries
`derivedPullbackTensorSheafHomCommShift`, and `R ℰom(𝒪_Z, -)` carries the commutation
`derivedSheafHomExactSupportCommShift` it has as the right adjoint of the exact functor `i_*`.
Both functors are exact for these commutations (`isTriangulated_derivedPullbackTensorSheafHom`,
`isTriangulated_derivedSheafHomExactSupport`), and the map carries every triangle to a morphism of
the image triangles (`derivedPullbackTensorSheafHomTriangleHom`). -/
@[stacks 0B4C "compatible with distinguished triangles: the canonical map, functorial in the \
  complex, commutes with the shift"]
theorem commShift_derivedPullbackTensorSheafHomNatTrans :
    NatTrans.CommShift S.derivedPullbackTensorSheafHomNatTrans ℤ := by
  have := S.commShift_mateTrans
  rw [derivedPullbackTensorSheafHomNatTrans_eq]
  infer_instance

/-- The target `R ℰom(𝒪_Z, -)` of the canonical map of [Stacks, Tag 0B4C] is an exact functor,
for its commutation with the shift as the right adjoint of the exact functor `i_*`. -/
theorem isTriangulated_derivedSheafHomExactSupport :
    S.derivedSheafHomExactSupport.IsTriangulated :=
  S.derivedSheafHomAdjunction.isTriangulated_rightAdjoint

/-- The source `K ↦ Li^*K ⊗^L R ℰom(𝒪_Z, 𝒪_X)` of the canonical map of [Stacks, Tag 0B4C] is an
exact functor: `Li^*` is exact ([Stacks, Tag 06YJ]) and so is the derived tensor product in its
first variable ([Stacks, Tag 06YU]). -/
theorem isTriangulated_derivedPullbackTensorSheafHom :
    S.derivedPullbackTensorSheafHom.IsTriangulated :=
  have : (tensorRightFunctor S.Z S.derivedSheafHomStructureSheaf).IsTriangulated :=
    (canonicalDerivedTensorProduct S.Z.sheaf).exact_left S.derivedSheafHomStructureSheaf
  Functor.IsTriangulated.instComp (F := derivedPullback S.i)
    (G := tensorRightFunctor S.Z S.derivedSheafHomStructureSheaf)

/-- **[Stacks, Tag 0B4C], the map of triangles.** For every triangle `T` of `D(𝒪_X)`, the
components of the canonical map at its three vertices form a morphism from the image of `T`
under `K ↦ Li^*K ⊗^L R ℰom(𝒪_Z, 𝒪_X)` to its image under `R ℰom(𝒪_Z, -)`; for a distinguished
`T` both images are distinguished (`isTriangulated_derivedPullbackTensorSheafHom`,
`isTriangulated_derivedSheafHomExactSupport`). -/
@[stacks 0B4C "compatible with distinguished triangles: the canonical map is a morphism of the \
  image triangles"]
def derivedPullbackTensorSheafHomTriangleHom
    (T : Pretriangulated.Triangle
      (DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)))) :
    S.derivedPullbackTensorSheafHom.mapTriangle.obj T ⟶
      S.derivedSheafHomExactSupport.mapTriangle.obj T :=
  have := S.commShift_derivedPullbackTensorSheafHomNatTrans
  Pretriangulated.Triangle.homMk _ _
    (S.derivedPullbackTensorSheafHomNatTrans.app T.obj₁)
    (S.derivedPullbackTensorSheafHomNatTrans.app T.obj₂)
    (S.derivedPullbackTensorSheafHomNatTrans.app T.obj₃)
    (S.derivedPullbackTensorSheafHomNatTrans.naturality T.mor₁)
    (S.derivedPullbackTensorSheafHomNatTrans.naturality T.mor₂)
    (shift_square S.derivedPullbackTensorSheafHomNatTrans T.mor₃)

/-- The first component of `derivedPullbackTensorSheafHomTriangleHom` is the canonical map of
[Stacks, Tag 0B4C] at the first vertex. -/
theorem derivedPullbackTensorSheafHomTriangleHom_hom₁
    (T : Pretriangulated.Triangle
      (DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)))) :
    (S.derivedPullbackTensorSheafHomTriangleHom T).hom₁ =
      S.derivedPullbackTensorSheafHomMap T.obj₁ :=
  rfl

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
