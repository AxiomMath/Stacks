module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeComparisonSections

/-!
# The base change comparison of [Stacks, Tag 0EX3] (c) on sections over an open

For a commutative square of ringed spaces
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
an open `V ⊆ S`, objects `A` of `D(𝒪_X)` and `M` of `D(𝒪_{X'})` and a morphism
`c : A ⟶ Rg'_* M`, let `β : Rf_*(A) ⟶ Rg_*(Rf'_* M)` be `Rf_*(c)` followed by
`Stacks.Cohomology.DerivedBaseChange.Mate.derivedPushforwardComparisonSquare` at `M`. This file
expresses the degree-`q` cohomology of `RΓ(V, β)` through derived sections over the opens `f⁻¹V`
and `g⁻¹V`.

## Main results

* `homology_map_derivedPushforwardComparisonSquare_eq_lerayComposite`: the degree-`q` cohomology
  of `RΓ(V, β)`, prefixed by the Leray comparison of [Stacks, Tag 0D5W] for `f` at `V` and
  followed by a left inverse of the Leray comparison for `g` at `V`, is the degree-`q` cohomology
  of `RΓ(f⁻¹V, c)`, the inverse of the relative Leray comparison for `g'` over `f⁻¹V`, the
  transport along `(g' ≫ f)⁻¹V = (f' ≫ g)⁻¹V`, and the relative Leray comparison for `f'` over
  `g⁻¹V`. Nothing is assumed of the square beyond its commutativity.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.DerivedPullback.Composition

namespace Stacks.Cohomology.DerivedBaseChange

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-! ### Reassociation lemmas -/

/-- **A leading factor of a known factorisation cancelled against its inverse.** From
`(p ≫ x) ≫ y = e ≫ s ≫ t` together with `pinv ≫ p = 𝟙` one gets `x ≫ y = (pinv ≫ e ≫ s) ≫ t`. -/
private theorem cancel_head_inv {C : Type*} [Category* C] {A B D E F₁ F₂ : C}
    {p : A ⟶ B} {pinv : B ⟶ A} (hp : pinv ≫ p = 𝟙 B)
    {x : B ⟶ D} {y : D ⟶ E} {e : A ⟶ F₁} {s : F₁ ⟶ F₂} {t : F₂ ⟶ E}
    (h : (p ≫ x) ≫ y = e ≫ s ≫ t) : x ≫ y = (pinv ≫ e ≫ s) ≫ t := by
  simp only [Category.assoc] at h ⊢
  rw [← h, reassoc_of% hp]

/-- **A naturality square spliced onto a factorisation under a functor.** From
`l ≫ G.map m = p ≫ l'` and `l' ≫ G.map n = u ≫ t` one gets `l ≫ G.map (m ≫ n) = (p ≫ u) ≫ t`. -/
private theorem comp_map_splice {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {A₁ A₂ A₃ : C} {B₁ B₂ B₃ : D} {l : B₁ ⟶ G.obj A₁} {m : A₁ ⟶ A₂} {n : A₂ ⟶ A₃}
    {p : B₁ ⟶ B₂} {l' : B₂ ⟶ G.obj A₂} (hnat : l ≫ G.map m = p ≫ l')
    {u : B₂ ⟶ B₃} {t : B₃ ⟶ G.obj A₃} (hmid : l' ≫ G.map n = u ≫ t) :
    l ≫ G.map (m ≫ n) = (p ≫ u) ≫ t := by
  rw [G.map_comp, reassoc_of% hnat, hmid, Category.assoc]

/-- **A factorisation carried through a functor, with a trailing cancelling pair.** From
`l ≫ s = u ≫ t` and `G.map t ≫ lInv = 𝟙` one gets `G.map l ≫ G.map s ≫ lInv = G.map u`. -/
private theorem map_comp_comp_cancel {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {A B E F : C} {l : A ⟶ B} {s : B ⟶ E} {u : A ⟶ F} {t : F ⟶ E} (h : l ≫ s = u ≫ t)
    {lInv : G.obj E ⟶ G.obj F} (hl : G.map t ≫ lInv = 𝟙 _) :
    G.map l ≫ G.map s ≫ lInv = G.map u := by
  rw [← G.map_comp_assoc, h, G.map_comp_assoc, hl, Category.comp_id]

/-! ### The comparison on derived sections -/

variable {X' X S' S : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)
  (V : Opens S.carrier)

/-- **The base change comparison of [Stacks, Tag 0EX3] (c) on derived sections over `V`.** For
a commutative square of ringed spaces
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
an open `V ⊆ S`, objects `A` of `D(𝒪_X)` and `M` of `D(𝒪_{X'})`, a morphism
`c : A ⟶ Rg'_* M` and a degree `q`, write

> `β = Rf_*(c) ≫ (comparison of the two iterated derived pushforwards at M)`

for the morphism `Rf_*(A) ⟶ Rg_*(Rf'_* M)`. Then the degree-`q` cohomology of
`RΓ(V, β)`, prefixed by the Leray comparison of [Stacks, Tag 0D5W] for `f` at `V` and followed by
a left inverse `lInv` of the degree-`q` cohomology of the Leray comparison for `g` at `V`, is the
degree-`q` cohomology of

> `RΓ(f⁻¹V, c)`, the inverse of the relative Leray comparison for `g'` over `f⁻¹V`, the transport
> along `(g' ≫ f)⁻¹V = (f' ≫ g)⁻¹V`, and the relative Leray comparison for `f'` over `g⁻¹V`.

There is no hypothesis on the square beyond `sq`; in particular nothing is assumed of `g`. -/
theorem homology_map_derivedPushforwardComparisonSquare_eq_lerayComposite
    (A : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')))
    (c : A ⟶ (derivedPushforward g').obj M) (q : ℤ)
    {lInv : (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing S).obj.obj (op V))) q).obj
        ((derivedSectionsOverOpen S V).obj
          ((derivedPushforward g).obj ((derivedPushforward f').obj M))) ⟶
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing S).obj.obj (op V))) q).obj
        ((derivedPreimageSections g V).obj ((derivedPushforward f').obj M))}
    (hl : lInv ≫ (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing S).obj.obj (op V))) q).map
          ((lerayComparison g V).app ((derivedPushforward f').obj M)) = 𝟙 _) :
    (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing S).obj.obj (op V))) q).map
          ((lerayComparison f V).app A) ≫
        (DerivedCategory.homologyFunctor
              (ModuleCat.{u} ((structureSheafRing S).obj.obj (op V))) q).map
            ((derivedSectionsOverOpen S V).map ((derivedPushforward f).map c ≫
              (Mate.derivedPushforwardComparisonSquare (derivedAdjunction f)
                  (derivedAdjunction f') (derivedAdjunction g) (derivedAdjunction g')
                  (derivedPullbackCompIsoLeft g' f' f g sq)
                  (derivedPullbackCompIsoCanonical g' f)).app M)) ≫ lInv =
      (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing S).obj.obj (op V))) q).map
          ((derivedPreimageSections f V).map c ≫
            (derivedPreimageSectionsCompIso g' f V).hom.app M ≫
              eqToHom (congrArg (fun k : X' ⟶ S => (derivedPreimageSections k V).obj M) sq) ≫
                (lerayCompositeComparison f' g V).app M) := by
  have hnat : (lerayComparison f V).app A ≫
      (derivedSectionsOverOpen S V).map ((derivedPushforward f).map c) =
        (derivedPreimageSections f V).map c ≫
          (lerayComparison f V).app ((derivedPushforward g').obj M) :=
    ((lerayComparison f V).naturality c).symm
  have hinv : (derivedPreimageSectionsCompIso g' f V).hom.app M ≫
      (lerayCompositeComparison g' f V).app M = 𝟙 _ :=
    congr_app (derivedPreimageSectionsCompIso g' f V).hom_inv_id M
  have hfull := comp_map_splice (derivedSectionsOverOpen S V) hnat
    (cancel_head_inv hinv
      (derivedPushforwardComparisonSquare_app_comp_lerayComposite g' f' f g sq V M))
  have := isIso_lerayComparison g V
  have : IsIso ((lerayComparison g V).app ((derivedPushforward f').obj M)) :=
    NatIso.isIso_app_of_isIso _ _
  have hl' : (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing S).obj.obj (op V))) q).map
        ((lerayComparison g V).app ((derivedPushforward f').obj M)) ≫ lInv = 𝟙 _ := by
    rw [← IsIso.inv_eq_of_inv_hom_id hl, IsIso.hom_inv_id]
  exact map_comp_comp_cancel _ hfull hl'

end

end Stacks.Cohomology.DerivedBaseChange

end
