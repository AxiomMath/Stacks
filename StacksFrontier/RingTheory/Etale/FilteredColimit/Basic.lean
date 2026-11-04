module

import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.CategoryTheory.WithTerminal.Lemmas
public import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.CategoryTheory.Filtered.Grothendieck
import Mathlib.Tactic.ENatToNat
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.CategoryTheory.Limits.Shapes.Countable

public import StacksFrontier.RingTheory.Etale.Basic
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Defs
public import StacksFrontier.RingTheory.Henselian.EtaleLifting
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Filtered colimits of étale ring maps

An `R`-algebra is *ind-étale*, or *a filtered colimit of étale `R`-algebras*, when it is the
colimit of a filtered diagram of étale `R`-algebras. This file collects the permanence properties
of that class: it is stable under iterated filtered colimits, under base change and under
composition, it cancels on the left, and an ind-étale henselian local algebra is determined up to
a unique isomorphism by its residue field — which is what makes the henselization `R ↦ R^h` well
defined.

Ind-étaleness is not a predicate here, and no construction of any of the colimits is chosen.
`CategoryTheory.ObjectProperty.ind P Λ` says that `Λ` is presented as the colimit of a filtered
diagram of small index all of whose values satisfy `P`: a cocone with tip `Λ` together with the
assertion that it is colimiting, so the comparison map `colim Λᵢ → Λ` is the one induced by the
structure maps and not an unnamed isomorphism. Each result is stated with the spelling of `P` that
its dependents use — see the implementation notes.

Two of those spellings live in the category `Under (CommRingCat.of R)` of `R`-algebras, whose
objects are commutative rings `B` with a structure map `R ⟶ B` and whose morphisms are
`R`-algebra maps; for `X : Under (CommRingCat.of R)` the underlying ring map is
`X.hom.hom : R →+* X.right`.

## Main definitions

* `CommRingCat.etale`: being an étale ring map, as a morphism property on `CommRingCat`. Ind-étale
  is `CategoryTheory.MorphismProperty.ind` of it.

## Main results

* `isFilteredColimitOfEtaleUnder_of_isColimit`: a filtered colimit of ind-étale `R`-algebras is
  ind-étale.
* `filteredColimitEtale_baseChange`, `CommAlgCat.ind_etale_of_isPushout`: if `A` is ind-étale over
  `R`, then `R' ⊗[R] A` is ind-étale over `R'`.
* `CommRingCat.ind_etale_of_comp`, `CommAlgCat.ind_etale_of_comp`: for ring maps `R → A → B` with
  `A` and `B` ind-étale over `R`, `B` is ind-étale over `A`.
* `CommAlgCat.ind_etale_comp`: for `A → B → C` with `B` ind-étale over `A` and `C` ind-étale over
  `B`, `C` is ind-étale over `A`.
* `CommAlgCat.ind_etale_iff_ind_algebraMap`: an algebra is ind-étale exactly when its structure
  map is an ind-étale ring map.
* `HenselianLocalRing.existsUnique_algEquiv_of_ind_etale`: two ind-étale henselian local
  `R`-algebras surjecting onto the same field `K` are uniquely `R`-isomorphic over `K`.

## Implementation notes

The spelling of "`Λ` is a filtered colimit of étale `R`-algebras" varies with the dependents of
each result: `IsFilteredColimitOfEtaleUnder` and `IsFilteredColimitOfEtale` for the two colimit
statements, `ObjectProperty.ind (fun C : Under R ↦ C.hom.hom.Etale)` for
`CommRingCat.ind_etale_of_comp`, and `(CommAlgCat.etale R).ind` — the form Definition 04GQ and
every statement about henselizations use — for the statements about `Algebra` towers of types. The
equivalence `CategoryTheory.commAlgCatEquivUnder` transports between the last two, carrying
`CommAlgCat.etale A` to `fun D : Under _ ↦ D.hom.hom.Etale`;
`CommAlgCat.ind_etale_iff_ind_algebraMap` below is that transport, read against the morphism
property `CommRingCat.etale`, and `CommRingCat.ind_under_iff_exists_factorization` (Lemma 07C3) is
the factorization criterion all three arguments run through.

Lemmas 0BSH and 08HS are each stated twice and tagged jointly, because no dependent can use both
spellings. For 08HS the two are one rewrite apart. For 0BSH they are not: nothing here relates
`IsFilteredColimitOfEtale R A`, which presents `A` as a direct limit over a directed preorder with
a chosen `Algebra` structure on `Ring.DirectLimit`, to `(CommAlgCat.etale R).ind`, which presents
it as a filtered colimit in `CommAlgCat`. So `CommAlgCat.ind_etale_of_isPushout` is not derived
from `filteredColimitEtale_baseChange`, and does not use `directLimitTensorProductAlgEquiv`: it is
the stability of `CategoryTheory.MorphismProperty.ind` under cobase change, applied to
`CommRingCat.etale`, whose own stability under cobase change is Lemma 00U2.

Neither Mathlib nor this repository has a predicate `RingHom.IsIndEtale` or `Algebra.IsIndEtale`;
if one is introduced, `CommRingCat.ind_etale_of_comp` and `CommAlgCat.ind_etale_of_comp` become
`RingHom.IsIndEtale.of_comp` (the ind-analogue of `RingHom.Etale.of_comp`) and its `Algebra`
form, `CommAlgCat.ind_etale_of_isPushout` becomes `Algebra.IsIndEtale.of_isPushout` and
`CommAlgCat.ind_etale_comp` becomes `Algebra.IsIndEtale.comp`, with their hypotheses as instances.

`HenselianLocalRing.existsUnique_algEquiv_of_ind_etale` departs from the source's form: the source
concludes that there is a unique `R`-algebra *isomorphism* `S → S'` over `K`, whereas the
isomorphism `e` is characterised here by `p'.comp f = p ↔ f = e` among *all* `f : S →ₐ[R] S'`.
That is stronger in two ways — no other `R`-algebra map `S → S'` over `K` exists, and every such
map is an isomorphism — it is what Lemma 08HR gives, and the dependents (functoriality of the
henselization, 04GT, 05WP) need the map-level uniqueness.

The arguments use of the class of étale ring maps only that its members are of finite
presentation and that it is stable under base change and under composition, together with the
cancellation of Lemma 00U7 for `ind_etale_of_comp`, so they generalize to any class of ring maps
with those properties. Étale is the class the source names and the one this repository has the
API for, and an abstract version would have to carry the three properties as hypotheses, so no
class of ring maps is abstracted out.

No hypothesis of the composition statements is dead. For `ind_etale_of_comp`, in either
spelling: with
`R = A = ℤ` and `B = ℤ[X]` the hypothesis on `A` holds while that on `B` and the conclusion fail,
since `Ω` commutes with filtered colimits and `Ω_{ℤ[X]/ℤ} ≠ 0`; with `R = B = ℤ`, `A = ℤ[X]` and
`g : X ↦ 0` the hypothesis on `B` holds while that on `A` and the conclusion fail, an ind-étale
algebra being flat and `ℤ[X] → ℤ` not. The same two witnesses serve `ind_etale_comp`. For
`existsUnique_algEquiv_of_ind_etale`: dropping `HenselianLocalRing S` fails for `S = R` and
`S' = R^h` with `R` local and not henselian; dropping ind-étaleness of `S` fails for `R = ℚ`,
`S = ℚ⟦t⟧`, `S' = K = ℚ`; dropping surjectivity of `p` fails for `R = S = ℚ` and `S' = K = ℚ̄`.

## References

* [StacksProject 0BSJ](https://stacks.math.columbia.edu/tag/0BSJ)
* [StacksProject 0BSH](https://stacks.math.columbia.edu/tag/0BSH)
* [StacksProject 08HS](https://stacks.math.columbia.edu/tag/08HS)
* [StacksProject 08HT](https://stacks.math.columbia.edu/tag/08HT)
* [StacksProject 0BSI](https://stacks.math.columbia.edu/tag/0BSI)
-/

@[expose] public section

open CategoryTheory

/-! ### Rectification: a strict fibration from the per-stage presentations

Write `A = colim_{j : J} A_j` with `J` filtered, and present each `A_j = colim_{x : Idx j} F^j_x`
with `Idx j` small filtered and every `F^j_x` étale over `R`. The classical argument forms the
total index category of pairs `(j, x)`, with the all-étale diagram `(j, x) ↦ F^j_x`, and
identifies its colimit with `A`. Both the filteredness of that category and the identification
rest on an étale algebra being of finite presentation, hence a finitely presentable object of
`Under R`: a map out of one into a filtered colimit factors through a stage, and two maps that
agree in the colimit agree at a later stage.

The transition data `Idx j ⥤ Idx j'` that the factorization supplies is determined only up to a
later stage, so it is lax, whereas a `Grothendieck` construction needs a strict functor
`J ⥤ Cat`. Strictness is bought by carrying a *global* type of stages `Stage J Idx = Σ j', Idx j'`:
the fibre `SliceFibObj G Fib j` has objects a stage `s` together with a map
`p : F_s ⟶ G.obj j`, and the transition along `f : j ⟶ j'` is post-composition
`⟨s, p⟩ ↦ ⟨s, p ≫ G.map f⟩`, strictly functorial by `G.map_id` and `G.map_comp`. It leaves the
stage fixed, so the cocycle of the total diagram `sliceD` is trivial, and the fibre stays in
`Type 0` because a stage is a small index rather than a large étale algebra. Each fibre is
filtered because `sliceEmb`, the embedding `x ↦ ⟨⟨j, x⟩, p^j_x⟩` of the given filtered `Idx j`,
is final.

The comparison `fiberwiseColimit (sliceD G Fib) ≅ G` has to be produced together with its
naturality rather than assembled from objectwise isomorphisms, since objectwise-isomorphic
functors need not be naturally isomorphic: for `R = ℤ`, `J = Fin 2`, `Φ = const (Discrete PUnit)`,
`D = const` and `G.map (0 ⟶ 1) = aeval 0` there is an objectwise family admitting no natural
isomorphism. Here naturality is immediate, the transition being post-composition by `G.map f`.
-/

section

-- Needed section-wide: the ten declarations from `sliceFibMap_id` to `slicePsi_nat` rewrite
-- and `apply` against `Under`/`Grothendieck` comma objects, whose projections are
-- semireducible, so the patterns match only when `isDefEq` ignores transparency.
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] {J : Type} [SmallCategory J] {Idx : J → Type}
  [∀ j, SmallCategory (Idx j)]

/-- An étale `R`-algebra is of finite presentation (Stacks 00QO), hence a finitely presentable
object of `Under R`; this is the compactness that drives the whole construction. -/
private lemma isFinitelyPresentable_stageObj {Fib : ∀ j, Idx j ⥤ Under (CommRingCat.of R)}
    (hEt : ∀ j x, RingHom.Etale ((Fib j).obj x).hom.hom) (s : Stage J Idx) :
    IsFinitelyPresentable.{0} (stageObj Fib s) :=
  CommRingCat.isFinitelyPresentable_under _ _ (hEt s.fst s.snd).finitePresentation

variable {G : J ⥤ Under (CommRingCat.of R)} {Fib : ∀ j, Idx j ⥤ Under (CommRingCat.of R)}

@[simp] private lemma sliceFib_id_g {j : J} (a : SliceFibObj G Fib j) :
    (𝟙 a : SliceFibHom a a).g = 𝟙 _ := rfl

@[simp] private lemma sliceFib_comp_g {j : J} {a b c : SliceFibObj G Fib j} (f : a ⟶ b)
    (g : b ⟶ c) : (f ≫ g).g = f.g ≫ g.g := rfl

@[simp] private lemma sliceFib_eqToHom_g {j : J} {a b : SliceFibObj G Fib j} (h : a = b) :
    (eqToHom h).g = eqToHom (by rw [h]) := by
  subst h; rfl

/-- Reindexing `f : j ⟶ j'` on strict fibres: post-compose the structure map by `G.map f`. -/
private def sliceFibMap {j j' : J} (f : j ⟶ j') : SliceFibObj G Fib j ⥤ SliceFibObj G Fib j' where
  obj a := ⟨a.s, a.p ≫ G.map f⟩
  map {a b} φ := ⟨φ.g, by rw [reassoc_of% φ.w]⟩
  map_id := by intro a; apply SliceFibHom.ext; simp
  map_comp := by intro a b c φ ψ; apply SliceFibHom.ext; simp

/-- Reindexing along an identity of `J` is the identity functor. -/
private lemma sliceFibMap_id (j : J) : (sliceFibMap (𝟙 j) : SliceFibObj G Fib j ⥤ _) = 𝟭 _ := by
  apply CategoryTheory.Functor.ext
  · intro a b φ; apply SliceFibHom.ext; simp [sliceFibMap]
  · intro a; cases a with | mk s p => simp [sliceFibMap]

/-- Reindexing along a composite of maps of `J` is the composite of the reindexings. -/
private lemma sliceFibMap_comp {j j' j'' : J} (f : j ⟶ j') (h : j' ⟶ j'') :
    (sliceFibMap (f ≫ h) : SliceFibObj G Fib j ⥤ _) = sliceFibMap f ⋙ sliceFibMap h := by
  apply CategoryTheory.Functor.ext
  · intro a b φ; apply SliceFibHom.ext; simp [sliceFibMap]
  · intro a; cases a with | mk s p => simp [sliceFibMap, Category.assoc]

/-- The strict functor `J ⥤ Cat.{0,0}` of fibres of stages over `G`. -/
private def sliceΦ (G : J ⥤ Under (CommRingCat.of R))
    (Fib : ∀ j, Idx j ⥤ Under (CommRingCat.of R)) : J ⥤ Cat.{0,0} where
  obj j := Cat.of (SliceFibObj G Fib j)
  map f := (sliceFibMap f).toCatHom
  map_id j := by change (sliceFibMap (𝟙 j)).toCatHom = _; rw [sliceFibMap_id]; rfl
  map_comp f h := by change (sliceFibMap (f ≫ h)).toCatHom = _; rw [sliceFibMap_comp]; rfl

private lemma sliceD_id_fiber_g (X : Grothendieck (sliceΦ G Fib)) :
    ((𝟙 X : X ⟶ X).fiber).g = 𝟙 (stageObj Fib X.fiber.s) := by
  rw [Grothendieck.id_fiber, sliceFib_eqToHom_g]; rfl

private lemma sliceD_comp_fiber_g {X Y Z : Grothendieck (sliceΦ G Fib)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((f ≫ g : X ⟶ Z).fiber).g = f.fiber.g ≫ g.fiber.g := by
  rw [Grothendieck.comp_fiber, sliceFib_comp_g, sliceFib_comp_g, sliceFib_eqToHom_g]
  show (eqToHom _ : stageObj Fib X.fiber.s ⟶ stageObj Fib X.fiber.s) ≫ _ ≫ g.fiber.g
    = f.fiber.g ≫ g.fiber.g
  rw [show (eqToHom rfl : stageObj Fib X.fiber.s ⟶ stageObj Fib X.fiber.s) = 𝟙 _ from rfl,
      Category.id_comp]
  rfl

/-- The total diagram of stage algebras over `Grothendieck (sliceΦ G Fib)`; every value is
étale over `R`, and reindexing acts on it by the identity. -/
private def sliceD (G : J ⥤ Under (CommRingCat.of R))
    (Fib : ∀ j, Idx j ⥤ Under (CommRingCat.of R)) :
    Grothendieck (sliceΦ G Fib) ⥤ Under (CommRingCat.of R) where
  obj X := stageObj Fib X.fiber.s
  map {_ _} f := f.fiber.g
  map_id X := sliceD_id_fiber_g X
  map_comp f g := sliceD_comp_fiber_g f g

@[simp] private lemma sliceD_obj (G : J ⥤ Under (CommRingCat.of R))
    (Fib : ∀ j, Idx j ⥤ Under (CommRingCat.of R)) (X : Grothendieck (sliceΦ G Fib)) :
    (sliceD G Fib).obj X = stageObj Fib X.fiber.s := rfl

@[simp] private lemma sliceD_map (G : J ⥤ Under (CommRingCat.of R))
    (Fib : ∀ j, Idx j ⥤ Under (CommRingCat.of R)) {X Y : Grothendieck (sliceΦ G Fib)} (f : X ⟶ Y) :
    (sliceD G Fib).map f = f.fiber.g := rfl

/-- The embedding `Idx j ⥤ SliceFibObj G Fib j`, `x ↦ ⟨⟨j, x⟩, p^j_x⟩`. -/
private def sliceEmb (cFib : ∀ j, Limits.Cocone (Fib j)) (e : ∀ j, (cFib j).pt ≅ G.obj j) (j : J) :
    Idx j ⥤ SliceFibObj G Fib j where
  obj x := ⟨⟨j, x⟩, (cFib j).ι.app x ≫ (e j).hom⟩
  map {x y} φ := ⟨(Fib j).map φ, by
    have : (Fib j).map φ ≫ (cFib j).ι.app y = (cFib j).ι.app x := (cFib j).w φ
    rw [← Category.assoc, this]⟩
  map_id := by intro x; apply SliceFibHom.ext; simp [stageObj]
  map_comp := by intro x y z φ ψ; apply SliceFibHom.ext; simp [stageObj]

/-- `sliceEmb` is final: a stage mapping to `G.obj j` factors through a stage of `Idx j`, and two
such factorizations agree after pushing to a later stage. -/
private lemma sliceEmb_final [∀ j, IsFiltered (Idx j)] (cFib : ∀ j, Limits.Cocone (Fib j))
    (e : ∀ j, (cFib j).pt ≅ G.obj j) (j : J)
    (hEt : ∀ j x, RingHom.Etale ((Fib j).obj x).hom.hom)
    (hcFib : Limits.IsColimit (cFib j)) : (sliceEmb cFib e j).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro d
    have := isFinitelyPresentable_stageObj hEt d.s
    obtain ⟨c, h, hc⟩ :=
      IsFinitelyPresentable.exists_hom_of_isColimit hcFib (d.p ≫ (e j).inv)
    refine ⟨c, ⟨⟨h, ?_⟩⟩⟩
    show d.p = h ≫ ((cFib j).ι.app c ≫ (e j).hom)
    rw [← Category.assoc, hc, Category.assoc]
    simp
  · intro d c s s'
    have key : s.g ≫ (cFib j).ι.app c = s'.g ≫ (cFib j).ι.app c :=
      (cancel_mono (e j).hom).mp <| by
        rw [Category.assoc, Category.assoc]; exact s.w.symm.trans s'.w
    have h := isFinitelyPresentable_stageObj hEt d.s
    rw [isFinitelyPresentable_iff_preservesFilteredColimits] at h
    obtain ⟨c', t, ht⟩ :=
      Limits.exists_eq_of_preservesColimit_coyoneda_self hcFib s.g s'.g key
    exact ⟨c', t, SliceFibHom.ext ht⟩

/-- Each strict fibre is filtered, `sliceEmb` being a final functor out of the filtered
`Idx j`. -/
private lemma sliceFib_isFiltered [∀ j, IsFiltered (Idx j)]
    (G : J ⥤ Under (CommRingCat.of R)) (Fib : ∀ j, Idx j ⥤ Under (CommRingCat.of R))
    (cFib : ∀ j, Limits.Cocone (Fib j)) (e : ∀ j, (cFib j).pt ≅ G.obj j) (j : J)
    (hEt : ∀ j x, RingHom.Etale ((Fib j).obj x).hom.hom)
    (hcFib : Limits.IsColimit (cFib j)) : IsFiltered (SliceFibObj G Fib j) := by
  have := sliceEmb_final cFib e j hEt hcFib
  exact IsFiltered.of_final (sliceEmb cFib e j)

open CategoryTheory.Limits in
/-- The cocone over the fibre of `sliceD` at `j` whose leg at `⟨s, p⟩` is `p`. -/
private def fwdCocone (G : J ⥤ Under (CommRingCat.of R))
    (Fib : ∀ j, Idx j ⥤ Under (CommRingCat.of R)) (j : J) :
    Cocone (Grothendieck.ι (sliceΦ G Fib) j ⋙ sliceD G Fib) where
  pt := G.obj j
  ι := { app := fun a => a.p
         naturality := by
           intro a b φ
           change (Grothendieck.ι (sliceΦ G Fib) j ⋙ sliceD G Fib).map φ ≫ b.p = a.p ≫ 𝟙 _
           have hmap : (Grothendieck.ι (sliceΦ G Fib) j ⋙ sliceD G Fib).map φ = φ.g := by
             change ((Grothendieck.ι (sliceΦ G Fib) j).map φ).fiber.g = φ.g
             rw [Grothendieck.ι_map, sliceFib_comp_g, sliceFib_eqToHom_g]
             change (eqToHom rfl : stageObj Fib a.s ⟶ stageObj Fib a.s) ≫ φ.g = φ.g
             rw [show (eqToHom rfl : stageObj Fib a.s ⟶ stageObj Fib a.s) = 𝟙 _ from rfl,
                 Category.id_comp]
           rw [hmap, Category.comp_id, ← φ.w] }

/-- Embedding `Idx j` into the strict fibre over `j` and reading off the stage algebra recovers
`Fib j`. -/
private lemma sliceEmb_compFib (cFib : ∀ j, Limits.Cocone (Fib j))
    (e : ∀ j, (cFib j).pt ≅ G.obj j) (j : J) :
    sliceEmb cFib e j ⋙ (Grothendieck.ι (sliceΦ G Fib) j ⋙ sliceD G Fib) = Fib j := by
  apply CategoryTheory.Functor.ext
  · intro x y φ
    show ((((Grothendieck.ι (sliceΦ G Fib) j).map ((sliceEmb cFib e j).map φ)).fiber).g) = _
    rw [Grothendieck.ι_map, sliceFib_comp_g, sliceFib_eqToHom_g]
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · intro x; rfl

open CategoryTheory.Limits in
/-- `fwdCocone` is a colimit cocone: `sliceEmb` is final and `cFib j` extended along
`e j` is a colimit cocone of `Fib j` with apex `G.obj j`. -/
private noncomputable def isColimitFwdCocone [∀ j, IsFiltered (Idx j)]
    (cFib : ∀ j, Limits.Cocone (Fib j)) (e : ∀ j, (cFib j).pt ≅ G.obj j) (j : J)
    (hEt : ∀ j x, RingHom.Etale ((Fib j).obj x).hom.hom)
    (hcFib : Limits.IsColimit (cFib j)) : IsColimit (fwdCocone G Fib j) := by
  haveI : (sliceEmb cFib e j).Final := sliceEmb_final cFib e j hEt hcFib
  refine (Functor.Final.isColimitWhiskerEquiv (sliceEmb cFib e j) _) ?_
  refine (IsColimit.equivOfNatIsoOfIso (eqToIso (sliceEmb_compFib cFib e j))
    (Cocone.whisker (sliceEmb cFib e j) (fwdCocone G Fib j))
    ((cFib j).extend (e j).hom) ?_).symm (IsColimit.extendIso _ hcFib)
  refine Cocone.ext (Iso.refl _) ?_
  intro x
  simp [fwdCocone, Cocone.extend, sliceEmb, Cocone.whisker]

open CategoryTheory.Limits in
/-- The comparison maps `colim (fwdCocone j) ⟶ G.obj j` are natural in `j`: reindexing
post-composes the structure map by `G.map f`, so on cocone legs the comparison is `G.map f`. -/
private lemma slicePsi_nat (G : J ⥤ Under (CommRingCat.of R))
    (Fib : ∀ j, Idx j ⥤ Under (CommRingCat.of R))
    {j j' : J} (f : j ⟶ j') (a : SliceFibObj G Fib j) :
    colimit.ι (Grothendieck.ι (sliceΦ G Fib) j ⋙ sliceD G Fib) a ≫
        ((Limits.fiberwiseColimit (sliceD G Fib)).map f ≫ colimit.desc _ (fwdCocone G Fib j'))
      = colimit.ι (Grothendieck.ι (sliceΦ G Fib) j ⋙ sliceD G Fib) a ≫
        (colimit.desc _ (fwdCocone G Fib j) ≫ G.map f) := by
  rw [fiberwiseColimit_map, Category.assoc, ι_colimMap_assoc, colimit.ι_pre_assoc, colimit.ι_desc,
    ← Category.assoc, colimit.ι_desc]
  show _ ≫ (fwdCocone G Fib j').ι.app ((sliceFibMap f).obj a) = (fwdCocone G Fib j).ι.app a ≫
      G.map f
  simp only [fwdCocone]
  simp [Grothendieck.ιNatTrans, sliceD_map, sliceΦ, sliceFibMap]

/-- The fibrewise colimit of the total diagram is `G`, naturally in `j`. -/
private lemma sliceFiberwiseColimit_natIso [∀ j, IsFiltered (Idx j)]
    (G : J ⥤ Under (CommRingCat.of R)) (Fib : ∀ j, Idx j ⥤ Under (CommRingCat.of R))
    (cFib : ∀ j, Limits.Cocone (Fib j)) (e : ∀ j, (cFib j).pt ≅ G.obj j)
    (hEt : ∀ j x, RingHom.Etale ((Fib j).obj x).hom.hom)
    (hcFib : ∀ j, Limits.IsColimit (cFib j)) :
    Nonempty (Limits.fiberwiseColimit (sliceD G Fib) ≅ G) := by
  let Ψ : Limits.fiberwiseColimit (sliceD G Fib) ⟶ G :=
    { app := fun j => Limits.colimit.desc _ (fwdCocone G Fib j)
      naturality := fun j j' f => Limits.colimit.hom_ext fun a => slicePsi_nat G Fib f a }
  have : ∀ j, IsIso (Ψ.app j) := by
    intro j
    have hΨ : Ψ.app j = ((Limits.colimit.isColimit _).coconePointUniqueUpToIso
        (isColimitFwdCocone cFib e j hEt (hcFib j))).hom :=
      (Limits.colimit.isColimit _).hom_ext fun a => by simp [Ψ]
    rw [hΨ]
    infer_instance
  have : IsIso Ψ := NatIso.isIso_of_isIso_app Ψ
  exact ⟨asIso Ψ⟩

end

/-- **Transitivity of "filtered colimit of étale algebras".** Let `J` be a small filtered
category, let `G : J ⥤ Under (CommRingCat.of R)` be a diagram whose values are all filtered
colimits of étale `R`-algebras, and let `cG` be a colimit cocone of `G`. Then `cG.pt` is a
filtered colimit of étale `R`-algebras.

The index category is `Grothendieck (sliceΦ G Fib)`, filtered because `J` and each of its fibres
are, and its colimit is `cG.pt` because the fibrewise colimit of the total diagram is `G`. -/
lemma IsFilteredColimitOfEtaleUnder.trans_colimit (R : Type) [CommRing R]
    (J : Type) [SmallCategory J] [IsFiltered J]
    (G : J ⥤ Under (CommRingCat.of R))
    (cG : Limits.Cocone G) (hcG : Limits.IsColimit cG)
    (hEach : ∀ j, IsFilteredColimitOfEtaleUnder R (G.obj j)) :
    IsFilteredColimitOfEtaleUnder R cG.pt := by
  classical
  choose Idx instSC instF Fib cFib hEt hCol hIso using hEach
  obtain ⟨ε⟩ := sliceFiberwiseColimit_natIso G Fib cFib (fun j => (hIso j).some) hEt
    (fun j => (hCol j).some)
  have : ∀ j, IsFiltered ((sliceΦ G Fib).obj j) := fun j =>
    sliceFib_isFiltered G Fib cFib (fun j => (hIso j).some) j hEt (hCol j).some
  refine ⟨Grothendieck (sliceΦ G Fib), inferInstance, inferInstance, sliceD G Fib,
    Limits.colimit.cocone _, ?_, ⟨Limits.colimit.isColimit _⟩, ⟨?_⟩⟩
  · rintro ⟨j, a⟩
    show RingHom.Etale (stageObj Fib a.s).hom.hom
    exact hEt a.s.fst a.s.snd
  · exact (Limits.colimitFiberwiseColimitIso (sliceD G Fib)).symm ≪≫
      Limits.HasColimit.isoOfNatIso ε ≪≫
      (Limits.colimit.isColimit G).coconePointUniqueUpToIso hcG

/-- **Stacks 0BSJ.** Let `R` be a commutative ring, let `J` be a small filtered category and let
`G : J ⥤ Under (CommRingCat.of R)` be a diagram of `R`-algebras with colimit cocone `cA` and
apex isomorphic to `A`. If every `G.obj j` is a filtered colimit of étale `R`-algebras, then so
is `A`. -/
@[stacks 0BSJ]
theorem isFilteredColimitOfEtaleUnder_of_isColimit (R : Type) [CommRing R]
    (A : Under (CommRingCat.of R))
    (J : Type) [SmallCategory J] [IsFiltered J]
    (G : J ⥤ Under (CommRingCat.of R))
    (cA : Limits.Cocone G) (hcA : Limits.IsColimit cA) (hA : cA.pt ≅ A)
    (hEach : ∀ j, IsFilteredColimitOfEtaleUnder R (G.obj j)) :
    IsFilteredColimitOfEtaleUnder R A := by
  obtain ⟨K, instK, instFK, F, c, hEtF, hcolim, ⟨hiso⟩⟩ :=
    IsFilteredColimitOfEtaleUnder.trans_colimit R J G cA hcA hEach
  exact ⟨K, instK, instFK, F, c, hEtF, hcolim, ⟨hiso ≪≫ hA⟩⟩

/-! ### Base change

If `A = colim_i G i` is a filtered colimit of étale `R`-algebras and `R → R'` is a ring map, then
`R' ⊗[R] A` is a filtered colimit of étale `R'`-algebras: the base changed system `R' ⊗[R] G i` is
again directed, its members are étale over `R'` because étale ring maps are stable under base
change (Stacks 00U2), and its colimit is `R' ⊗[R] A`.

That last identification is `directLimitTensorProductAlgEquiv` below, where the two maps are
exhibited and compared on generators, `Ring.DirectLimit` being a quotient of a free commutative
ring rather than a categorical colimit; see its docstring.
-/

universe u

/-- Base changing along `R'` turns a composite of `R`-algebra maps into a composite. -/
private lemma tensor_map_comp_apply {R R' A B C : Type*} [CommRing R] [CommRing R']
    [Algebra R R'] [CommRing A] [CommRing B] [CommRing C] [Algebra R A] [Algebra R B] [Algebra R C]
    (g : B →ₐ[R] C) (h : A →ₐ[R] B) (k : A →ₐ[R] C) (hgh : g.comp h = k)
    (x : TensorProduct R R' A) :
    Algebra.TensorProduct.map (AlgHom.id R' R') g
        (Algebra.TensorProduct.map (AlgHom.id R' R') h x)
      = Algebra.TensorProduct.map (AlgHom.id R' R') k x := by
  rw [← hgh, Algebra.TensorProduct.map_id_comp]
  rfl

-- Needed: `rw [Algebra.TensorProduct.lift_tmul]` in `hΦ_tmul` matches only once the
-- `Algebra R' (R' ⊗[R] G i)` instances unfold at `default` transparency.
set_option backward.isDefEq.respectTransparency false in
/-- **Base change commutes with the direct limit of a directed system of algebras.** Let `G` be a
directed system of `R`-algebras with transition maps `f`, and let `R'` be an `R`-algebra. Then
`R' ⊗[R] -` carries the direct limit of `G` to the direct limit of the base changed system
`i ↦ R' ⊗[R] G i`.

The `Algebra R'` structure on a `Ring.DirectLimit` is not canonical — it is read off a chosen
index — so each limit carries its own as an instance, together with the condition (`hof`, `hof'`)
that the structure maps `Ring.DirectLimit.of i` are algebra maps. That condition pins the
structure down as the natural one, and it is what `IsFilteredColimitOfEtale` supplies.

`Ring.DirectLimit G f` is a quotient of a free commutative ring, not a categorical colimit, so
`R' ⊗[R] -` being a left adjoint is unavailable at this spelling and there is no
colimit-preservation lemma to invoke. The two maps are therefore built by hand, with
`Algebra.TensorProduct.lift` and `Ring.DirectLimit.lift`, and shown mutually inverse on
generators by `TensorProduct.induction_on` and `Ring.DirectLimit.induction_on`. Mathlib's
`TensorProduct.directLimitRight` is the same statement for `Module.DirectLimit`, and does not
apply. -/
@[ega "III 6.3.12" "special case", sga "3 V 4.1.2" "partial"]
private noncomputable def directLimitTensorProductAlgEquiv
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    (G : ι → Type u) [∀ i, CommRing (G i)] [∀ i, Algebra R (G i)]
    (f : (i j : ι) → i ≤ j → G i →ₐ[R] G j)
    [Algebra R (Ring.DirectLimit G fun i j h ↦ (f i j h : G i → G j))]
    [Algebra R' (Ring.DirectLimit (fun i ↦ TensorProduct R R' (G i))
      fun i j h ↦ (Algebra.TensorProduct.map (AlgHom.id R' R') (f i j h) : _ → _))]
    [Algebra R (Ring.DirectLimit (fun i ↦ TensorProduct R R' (G i))
      fun i j h ↦ (Algebra.TensorProduct.map (AlgHom.id R' R') (f i j h) : _ → _))]
    [IsScalarTower R R' (Ring.DirectLimit (fun i ↦ TensorProduct R R' (G i))
      fun i j h ↦ (Algebra.TensorProduct.map (AlgHom.id R' R') (f i j h) : _ → _))]
    (hof : ∀ (i : ι) (r : R),
      Ring.DirectLimit.of G (fun i j h ↦ (f i j h : G i → G j)) i (algebraMap R (G i) r)
        = algebraMap R (Ring.DirectLimit G fun i j h ↦ (f i j h : G i → G j)) r)
    (hof' : ∀ (i : ι) (r : R'),
      Ring.DirectLimit.of (fun i ↦ TensorProduct R R' (G i))
          (fun i j h ↦ (Algebra.TensorProduct.map (AlgHom.id R' R') (f i j h) : _ → _)) i
          (algebraMap R' (TensorProduct R R' (G i)) r)
        = algebraMap R' (Ring.DirectLimit (fun i ↦ TensorProduct R R' (G i))
          fun i j h ↦ (Algebra.TensorProduct.map (AlgHom.id R' R') (f i j h) : _ → _)) r)
    (i₀ : ι) :
    TensorProduct R R' (Ring.DirectLimit G fun i j h ↦ (f i j h : G i → G j))
      ≃ₐ[R'] Ring.DirectLimit (fun i ↦ TensorProduct R R' (G i))
        fun i j h ↦ (Algebra.TensorProduct.map (AlgHom.id R' R') (f i j h) : _ → _) := by
  haveI : Nonempty ι := ⟨i₀⟩
  let f₀ : (i j : ι) → i ≤ j → G i → G j := fun i j h ↦ (f i j h : G i → G j)
  let G' : ι → Type u := fun i ↦ TensorProduct R R' (G i)
  let f'₀ : (i j : ι) → i ≤ j → G' i → G' j :=
    fun i j h ↦ (Algebra.TensorProduct.map (AlgHom.id R' R') (f i j h) : _ → _)
  let L : Type u := Ring.DirectLimit G f₀
  let L' : Type u := Ring.DirectLimit G' f'₀
  change TensorProduct R R' L ≃ₐ[R'] L'
  let ofAlg : (i : ι) → G i →ₐ[R] L := fun i =>
    { Ring.DirectLimit.of G f₀ i with
      commutes' := fun r => hof i r }
  let ofAlg' : (i : ι) → G' i →ₐ[R'] L' := fun i =>
    { Ring.DirectLimit.of G' f'₀ i with
      commutes' := fun r => hof' i r }
  let gComp : (i : ι) → G i →+* L' := fun i =>
    ((ofAlg' i).restrictScalars R).comp Algebra.TensorProduct.includeRight |>.toRingHom
  have hgComp : ∀ (i j : ι) (hij : i ≤ j) (x : G i),
      gComp j (f₀ i j hij x) = gComp i x := by
    intro i j hij x
    simp only [gComp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply]
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply]
    have hmap : f'₀ i j hij (1 ⊗ₜ[R] x) = (1 : R') ⊗ₜ[R] (f i j hij x) := by
      change Algebra.TensorProduct.map (AlgHom.id R' R') (f i j hij) (1 ⊗ₜ[R] x)
          = (1 : R') ⊗ₜ[R] (f i j hij x)
      rw [Algebra.TensorProduct.map_tmul]
      simp
    change Ring.DirectLimit.of G' f'₀ j ((1 : R') ⊗ₜ[R] (f i j hij x))
        = Ring.DirectLimit.of G' f'₀ i ((1 : R') ⊗ₜ[R] x)
    rw [← hmap]
    exact Ring.DirectLimit.of_f hij _
  let gRing : L →+* L' := Ring.DirectLimit.lift G f₀ L' gComp hgComp
  have htmul_alg : ∀ (i : ι) (r : R),
      (1 : R') ⊗ₜ[R] (algebraMap R (G i) r) = algebraMap R' (G' i) (algebraMap R R' r) := by
    intro i r
    have hL : (1 : R') ⊗ₜ[R] (algebraMap R (G i) r) = algebraMap R (G' i) r := by
      rw [← Algebra.TensorProduct.includeRight_apply]
      exact (Algebra.TensorProduct.includeRight).commutes r
    rw [hL, ← IsScalarTower.algebraMap_apply R R' (G' i)]
  have hgRing_comm : ∀ r : R, gRing (algebraMap R L r) = algebraMap R L' r := by
    intro r
    have h1 : algebraMap R L r = Ring.DirectLimit.of G f₀ i₀ (algebraMap R (G i₀) r) :=
      (hof i₀ r).symm
    rw [h1]
    change Ring.DirectLimit.lift G f₀ L' gComp hgComp
        (Ring.DirectLimit.of G f₀ i₀ (algebraMap R (G i₀) r)) = algebraMap R L' r
    rw [Ring.DirectLimit.lift_of]
    change ofAlg' i₀ (Algebra.TensorProduct.includeRight (algebraMap R (G i₀) r))
        = algebraMap R L' r
    rw [Algebra.TensorProduct.includeRight_apply, htmul_alg i₀ r]
    change Ring.DirectLimit.of G' f'₀ i₀ (algebraMap R' (G' i₀) (algebraMap R R' r))
        = algebraMap R L' r
    rw [hof' i₀ (algebraMap R R' r)]
    exact (IsScalarTower.algebraMap_apply R R' L' r).symm
  let gAlg : L →ₐ[R] L' :=
    { gRing with commutes' := hgRing_comm }
  let Φ : TensorProduct R R' L →ₐ[R'] L' :=
    Algebra.TensorProduct.lift (Algebra.ofId R' L') gAlg
      (fun x y => mul_comm _ _)
  let ψComp : (i : ι) → G' i →+* TensorProduct R R' L := fun i =>
    (Algebra.TensorProduct.map (AlgHom.id R' R') (ofAlg i)).toRingHom
  have hψComp : ∀ (i j : ι) (hij : i ≤ j) (x : G' i),
      ψComp j (f'₀ i j hij x) = ψComp i x := by
    intro i j hij x
    exact tensor_map_comp_apply (ofAlg j) (f i j hij) (ofAlg i)
      (AlgHom.ext fun b => Ring.DirectLimit.of_f hij b) x
  let ψRing : L' →+* TensorProduct R R' L :=
    Ring.DirectLimit.lift G' f'₀ (TensorProduct R R' L) ψComp hψComp
  have hψRing_comm : ∀ r : R',
      ψRing (algebraMap R' L' r) = algebraMap R' (TensorProduct R R' L) r := by
    intro r
    have h1 : algebraMap R' L' r
        = Ring.DirectLimit.of G' f'₀ i₀ (algebraMap R' (G' i₀) r) := (hof' i₀ r).symm
    rw [h1]
    change Ring.DirectLimit.lift G' f'₀ (TensorProduct R R' L) ψComp hψComp
        (Ring.DirectLimit.of G' f'₀ i₀ (algebraMap R' (G' i₀) r))
        = algebraMap R' (TensorProduct R R' L) r
    rw [Ring.DirectLimit.lift_of]
    change (Algebra.TensorProduct.map (AlgHom.id R' R') (ofAlg i₀)) (algebraMap R' (G' i₀) r)
        = algebraMap R' (TensorProduct R R' L) r
    rw [AlgHom.commutes]
  let Ψ : L' →ₐ[R'] TensorProduct R R' L :=
    { ψRing with commutes' := hψRing_comm }
  have hΨ_of : ∀ (i : ι) (w : G' i),
      Ψ (Ring.DirectLimit.of G' f'₀ i w) = ψComp i w := by
    intro i w
    change ψRing (Ring.DirectLimit.of G' f'₀ i w) = ψComp i w
    exact Ring.DirectLimit.lift_of _ _ _ _ _
  have hΦ_tmul : ∀ (r' : R') (x : L),
      Φ (r' ⊗ₜ[R] x) = algebraMap R' L' r' * gAlg x := by
    intro r' x
    change Algebra.TensorProduct.lift (Algebra.ofId R' L') gAlg _ (r' ⊗ₜ[R] x)
        = algebraMap R' L' r' * gAlg x
    rw [Algebra.TensorProduct.lift_tmul]
    rfl
  have hgAlg_of : ∀ (i : ι) (y : G i),
      gAlg (ofAlg i y) = Ring.DirectLimit.of G' f'₀ i ((1 : R') ⊗ₜ[R] y) := by
    intro i y
    change Ring.DirectLimit.lift G f₀ L' gComp hgComp (Ring.DirectLimit.of G f₀ i y)
        = Ring.DirectLimit.of G' f'₀ i ((1 : R') ⊗ₜ[R] y)
    rw [Ring.DirectLimit.lift_of]
    change ofAlg' i (Algebra.TensorProduct.includeRight y)
        = Ring.DirectLimit.of G' f'₀ i ((1 : R') ⊗ₜ[R] y)
    rw [Algebra.TensorProduct.includeRight_apply]
    rfl
  have hmul : ∀ (i : ι) (r' : R') (y : G i),
      algebraMap R' (G' i) r' * ((1 : R') ⊗ₜ[R] y) = r' ⊗ₜ[R] y := by
    intro i r' y
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    simp
  refine AlgEquiv.ofAlgHom Φ Ψ (AlgHom.ext fun z => ?_) (AlgHom.ext fun z => ?_)
  · change Φ (Ψ z) = z
    induction z using Ring.DirectLimit.induction_on with
    | ih i w =>
      rw [hΨ_of i w]
      change Φ (Algebra.TensorProduct.map (AlgHom.id R' R') (ofAlg i) w)
          = Ring.DirectLimit.of G' f'₀ i w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul r' y =>
        rw [Algebra.TensorProduct.map_tmul]
        simp only [AlgHom.id_apply]
        rw [hΦ_tmul, hgAlg_of, ← hof' i r', ← map_mul]
        congr 1
        exact hmul i r' y
      | add w₁ w₂ hw₁ hw₂ => rw [map_add, map_add, map_add, hw₁, hw₂]
  · change Ψ (Φ z) = z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r' x =>
      rw [hΦ_tmul]
      induction x using Ring.DirectLimit.induction_on with
      | ih i y =>
        change Ψ (algebraMap R' L' r' * gAlg (ofAlg i y)) = r' ⊗ₜ[R] (ofAlg i y)
        rw [hgAlg_of, ← hof' i r', ← map_mul, hmul, hΨ_of i (r' ⊗ₜ[R] y)]
        change Algebra.TensorProduct.map (AlgHom.id R' R') (ofAlg i) (r' ⊗ₜ[R] y)
            = r' ⊗ₜ[R] (ofAlg i y)
        rw [Algebra.TensorProduct.map_tmul]
        rfl
    | add z₁ z₂ hz₁ hz₂ => rw [map_add, map_add, hz₁, hz₂]

/-- **Stacks 0BSH.** Let `A` and `R'` be commutative `R`-algebras, equivalently ring
maps `R → A` and `R → R'`. If `A` is a filtered colimit of étale `R`-algebras, then
`R' ⊗[R] A`, regarded as an `R'`-algebra via the canonical map `R' → R' ⊗[R] A`, is a
filtered colimit of étale `R'`-algebras. Here `TensorProduct R R' A` is `R' ⊗[R] A`
with its canonical `R'`-algebra structure. -/
@[stacks 0BSH]
theorem filteredColimitEtale_baseChange
    {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    {R' : Type u} [CommRing R'] [Algebra R R']
    (hA : IsFilteredColimitOfEtale R A) :
    IsFilteredColimitOfEtale R' (TensorProduct R R' A) := by
  classical
  obtain ⟨ι, instPre, hdir, hne, G, instCR, instAlgRG, f, hsys, instAlgL, hetale, hof, ⟨e⟩⟩ := hA
  let f₀ : (i j : ι) → i ≤ j → G i → G j := fun i j h => (f i j h : G i → G j)
  let L : Type u := Ring.DirectLimit G f₀
  let G' : ι → Type u := fun i => TensorProduct R R' (G i)
  let f' : (i j : ι) → i ≤ j → G' i →ₐ[R'] G' j :=
    fun i j h => Algebra.TensorProduct.map (AlgHom.id R' R') (f i j h)
  let f'₀ : (i j : ι) → i ≤ j → G' i → G' j := fun i j h => (f' i j h : G' i → G' j)
  have hsys' : DirectedSystem G' f'₀ := by
    constructor
    · intro i x
      show Algebra.TensorProduct.map (AlgHom.id R' R') (f i i (le_refl i)) x = x
      rw [show f i i (le_refl i) = AlgHom.id R (G i) from AlgHom.ext fun b => hsys.map_self b,
        Algebra.TensorProduct.map_id]
      rfl
    · intro i j k hij hjk x
      exact tensor_map_comp_apply (f j i hjk) (f k j hij) (f k i (le_trans hij hjk))
        (AlgHom.ext fun b => hsys.map_map hij hjk b) x
  let L' : Type u := Ring.DirectLimit G' f'₀
  have hf'_alg : ∀ (i j : ι) (h : i ≤ j) (r : R'),
      f'₀ i j h (algebraMap R' (G' i) r) = algebraMap R' (G' j) r :=
    fun i j h r => (f' i j h).commutes r
  have hof_eq : ∀ (i j : ι) (r : R'),
      Ring.DirectLimit.of G' f'₀ i (algebraMap R' (G' i) r)
        = Ring.DirectLimit.of G' f'₀ j (algebraMap R' (G' j) r) := by
    intro i j r
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    have h1 : Ring.DirectLimit.of G' f'₀ i (algebraMap R' (G' i) r)
        = Ring.DirectLimit.of G' f'₀ k (algebraMap R' (G' k) r) := by
      rw [← hf'_alg i k hik r]
      exact (Ring.DirectLimit.of_f hik _).symm
    have h2 : Ring.DirectLimit.of G' f'₀ j (algebraMap R' (G' j) r)
        = Ring.DirectLimit.of G' f'₀ k (algebraMap R' (G' k) r) := by
      rw [← hf'_alg j k hjk r]
      exact (Ring.DirectLimit.of_f hjk _).symm
    rw [h1, h2]
  obtain ⟨i₀⟩ := hne
  let algR'L' : R' →+* L' :=
    (Ring.DirectLimit.of G' f'₀ i₀).comp (algebraMap R' (G' i₀))
  let instAlgL' : Algebra R' L' := algR'L'.toAlgebra
  have hof' : ∀ (i : ι) (r : R'),
      Ring.DirectLimit.of G' f'₀ i (algebraMap R' (G' i) r) = algebraMap R' L' r := by
    intro i r
    show Ring.DirectLimit.of G' f'₀ i (algebraMap R' (G' i) r) = algR'L' r
    exact hof_eq i i₀ r
  have hetale' : ∀ i, Algebra.Etale R' (G' i) := by
    intro i
    have := hetale i
    exact Algebra.Etale.baseChange R (G i) R'
  let instAlgRL' : Algebra R L' := ((algebraMap R' L').comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨ι, instPre, hdir, ⟨i₀⟩, G', (fun i => inferInstance), (fun i => inferInstance),
    f', hsys', instAlgL', hetale', hof',
    ⟨(Algebra.TensorProduct.congr AlgEquiv.refl e).trans
      (directLimitTensorProductAlgEquiv G f hof hof' i₀)⟩⟩

/-! ### Left cancellation for ind-étale ring maps

Write `A = colim Aᵢ` and `B = colim Bⱼ` with `Aᵢ`, `Bⱼ` étale over `R`. Each `Aᵢ → B` factors
through some `Bⱼ` because `R → Aᵢ` is of finite presentation, and such a factorization
`Aᵢ → Bⱼ` is itself étale because `R → Aᵢ` is étale and `R → Bⱼ` is (Lemma 00U7). Base changing
along `Aᵢ → A` makes `A → A ⊗_{Aᵢ} Bⱼ` étale, and `colim A ⊗_{Aᵢ} Bⱼ = A ⊗_A B = B` over the
directed system of pairs `(i, j)` together with a factorization `Aᵢ → Bⱼ → B`, because tensor
products commute with colimits.
-/

section

open Limits TensorProduct

/-- Étale algebras are of finite presentation. -/
private lemma etale_le_finitePresentation (R : CommRingCat.{u}) :
    (fun C : Under R ↦ C.hom.hom.Etale) ≤ fun C : Under R ↦ C.hom.hom.FinitePresentation :=
  fun _ h ↦ (RingHom.Etale.iff_flat_and_formallyUnramified.mp h).2.2

/-- The sum of the monomials built from lifts `c d` along `φ : S →+* T` of the coefficients of
`p : MvPolynomial σ T` maps to `p`; so a polynomial whose coefficients all lift along `φ` is
itself the image of a polynomial over `S`. -/
private lemma map_sum_monomial_eq {S T σ : Type*} [CommRing S] [CommRing T] (φ : S →+* T)
    (p : MvPolynomial σ T) (c : {d // d ∈ p.support} → S)
    (hc : ∀ d, φ (c d) = MvPolynomial.coeff d.1 p) :
    MvPolynomial.map φ (∑ d ∈ p.support.attach, MvPolynomial.monomial d.1 (c d)) = p := by
  refine Eq.trans ?_ (MvPolynomial.as_sum p).symm
  rw [map_sum, ← Finset.sum_attach p.support
    fun d ↦ MvPolynomial.monomial d (MvPolynomial.coeff d p)]
  exact Finset.sum_congr rfl fun d _ ↦ by rw [MvPolynomial.map_monomial, hc d]

/-- A finite family of elements of an `R`-algebra `Λ` with the factorization property of Lemma
07C3 is, all at once, the image of a family of elements of a single member of the family: apply
the factorization to the polynomial algebra on the family. -/
private lemma exists_lift {R : CommRingCat.{u}} {Λ : Under R} {E : ObjectProperty (Under R)}
    (hΛ : ∀ P : Under R, P.hom.hom.FinitePresentation → ∀ φ : P ⟶ Λ,
      ∃ (X : Under R) (a : P ⟶ X) (b : X ⟶ Λ), a ≫ b = φ ∧ E X)
    {ι : Type u} [Finite ι] (a : ι → Λ.right) :
    ∃ (X : Under R) (b : X ⟶ Λ) (c : ι → X.right), E X ∧ ∀ t, b.right.hom (c t) = a t := by
  classical
  have hP : (MvPolynomial.C (σ := ι) (R := R)).FinitePresentation := by
    rw [← MvPolynomial.algebraMap_eq, RingHom.finitePresentation_algebraMap]
    exact Algebra.FinitePresentation.mvPolynomial R R ι
  obtain ⟨X, p, b, hp, hX⟩ := hΛ
    (Under.mk (CommRingCat.ofHom (MvPolynomial.C (σ := ι) (R := R)))) hP
    (Under.homMk (CommRingCat.ofHom (MvPolynomial.eval₂Hom Λ.hom.hom a)) (by ext x; simp))
  refine ⟨X, b, fun t ↦ p.right.hom (MvPolynomial.X t), hX, fun t ↦ ?_⟩
  simpa using congrArg (fun (φ : _ ⟶ Λ) ↦ φ.right.hom (MvPolynomial.X t)) hp

namespace CommRingCat

/-- **A filtered colimit of étale algebras over a filtered colimit of étale algebras.** Let
`R → A → B` be ring maps. If `A` and `B` are filtered colimits of étale `R`-algebras, then `B` is
a filtered colimit of étale `A`-algebras. -/
@[stacks 08HS "\"`Λ` is a filtered colimit of étale `R`-algebras\" is
`ObjectProperty.ind.{u} (fun C : Under R ↦ C.hom.hom.Etale) Λ`, as in Lemma `07C3`; the source's
`R`-algebra map `A → B` is a map `g` together with the composite `f ≫ g` as the `R`-algebra
structure of `B`, so the triangle commutes by construction. See the module docstring."]
theorem ind_etale_of_comp {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : A ⟶ B)
    (hf : ObjectProperty.ind.{u} (fun C : Under R ↦ C.hom.hom.Etale) (Under.mk f))
    (hfg : ObjectProperty.ind.{u} (fun C : Under R ↦ C.hom.hom.Etale) (Under.mk (f ≫ g))) :
    ObjectProperty.ind.{u} (fun C : Under A ↦ C.hom.hom.Etale) (Under.mk g) := by
  classical
  rw [CommRingCat.ind_under_iff_exists_factorization (Under.mk f)
    (etale_le_finitePresentation R)] at hf
  rw [CommRingCat.ind_under_iff_exists_factorization (Under.mk (f ≫ g))
    (etale_le_finitePresentation R)] at hfg
  rw [CommRingCat.ind_under_iff_exists_factorization (Under.mk g)
    (etale_le_finitePresentation A)]
  intro C hC ψ
  let : Algebra A C.right := C.hom.hom.toAlgebra
  obtain ⟨n, hn⟩ := hC
  obtain ⟨π, hπC, hπs, s, hs⟩ :
      ∃ π : MvPolynomial (Fin n) A →+* C.right,
        π.comp MvPolynomial.C = C.hom.hom ∧ Function.Surjective π ∧
          ∃ s : Finset (MvPolynomial (Fin n) A), Ideal.span ↑s = RingHom.ker π := by
    obtain ⟨p, h₁, h₂⟩ := hn
    exact ⟨p.toRingHom, by
      simpa [MvPolynomial.algebraMap_eq, RingHom.algebraMap_toAlgebra] using p.comp_algebraMap,
      h₁, h₂⟩
  obtain ⟨X, b, c, hX, hc⟩ := exists_lift hf
    (ι := Σ p : {p // p ∈ s}, {d // d ∈ (p : MvPolynomial (Fin n) A).support})
    (fun z ↦ MvPolynomial.coeff z.2.1 z.1.1)
  have hbX : ∀ x : R, b.right.hom (X.hom.hom x) = f.hom x := fun x ↦
    congr($(Under.w b).hom x)
  have hXfp : X.hom.hom.FinitePresentation := etale_le_finitePresentation R X hX
  set P : {p // p ∈ s} → MvPolynomial (Fin n) X.right := fun p ↦
    ∑ d ∈ (p : MvPolynomial (Fin n) A).support.attach,
      MvPolynomial.monomial d.1 (c ⟨p, d⟩)
  have hP : ∀ p, MvPolynomial.map b.right.hom (P p) = (p : MvPolynomial (Fin n) A) :=
    fun p ↦ map_sum_monomial_eq _ _ _ fun d ↦ hc ⟨p, d⟩
  set I : Ideal (MvPolynomial (Fin n) X.right) := Ideal.span (Set.range P) with hIdef
  have hI : I.FG := ⟨Finset.univ.image P, by
    rw [hIdef, Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩
  set q : X.right →+* MvPolynomial (Fin n) X.right ⧸ I :=
    (Ideal.Quotient.mk I).comp MvPolynomial.C with hqdef
  have hqalg : q = algebraMap X.right (MvPolynomial (Fin n) X.right ⧸ I) := rfl
  have hqfp : q.FinitePresentation := by
    have : Algebra.FinitePresentation X.right (MvPolynomial (Fin n) X.right ⧸ I) :=
      Algebra.FinitePresentation.quotient hI
    rw [hqalg, RingHom.finitePresentation_algebraMap]
    assumption
  set bvals : Fin n → B := fun t ↦ ψ.right.hom (π (MvPolynomial.X t)) with hbvals
  have hρ : (MvPolynomial.eval₂Hom g.hom bvals : MvPolynomial (Fin n) A →+* B) =
      ψ.right.hom.comp π := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun t ↦ by simp [hbvals])
    have : π (MvPolynomial.C r) = C.hom.hom r := congr($hπC r)
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.coe_comp,
      Function.comp_apply, this]
    exact (congr($(Under.w ψ).hom r)).symm
  set φB : MvPolynomial (Fin n) X.right →+* B :=
    MvPolynomial.eval₂Hom (g.hom.comp b.right.hom) bvals with hφBdef
  have hφB : ∀ z ∈ I, φB z = 0 := by
    have hsub : I ≤ RingHom.ker φB := by
      rw [hIdef, Ideal.span_le]
      rintro - ⟨p, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker, hφBdef, MvPolynomial.coe_eval₂Hom]
      rw [← MvPolynomial.eval₂_map, hP p, ← MvPolynomial.coe_eval₂Hom, hρ]
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [show π (p : MvPolynomial (Fin n) A) = 0 from
        RingHom.mem_ker.1 (hs.le (Ideal.subset_span p.2)), map_zero]
    exact fun z hz ↦ RingHom.mem_ker.1 (hsub hz)
  have hlift : ∀ x : R, Ideal.Quotient.lift I φB hφB (q (X.hom.hom x)) = g.hom (f.hom x) := by
    intro x
    rw [hqdef]
    show φB (MvPolynomial.C (X.hom.hom x)) = g.hom (f.hom x)
    rw [hφBdef]
    simp [hbX x]
  obtain ⟨Y, u, v, huv, hY⟩ := hfg (Under.mk (X.hom ≫ CommRingCat.ofHom q))
    (by simpa using hqfp.comp hXfp)
    (Under.homMk (CommRingCat.ofHom (Ideal.Quotient.lift I φB hφB)) (by ext x; exact hlift x))
  set j : X.right →+* Y.right := u.right.hom.comp q with hjdef
  have huv' : ∀ z, v.right.hom (u.right.hom z) = Ideal.Quotient.lift I φB hφB z := fun z ↦ by
    simpa using congr($(huv).right.hom z)
  have hjY : ∀ x, j (X.hom.hom x) = Y.hom.hom x := fun x ↦ by
    simpa [hjdef] using congr($(Under.w u).hom x)
  have hjE : j.Etale := by
    refine RingHom.Etale.of_comp (RingHom.Etale.formallyUnramified _ hX)
      (RingHom.FiniteType.of_finitePresentation hXfp) ?_
    rw [show j.comp X.hom.hom = Y.hom.hom from RingHom.ext hjY]
    exact hY
  let : Algebra X.right A := b.right.hom.toAlgebra
  let : Algebra X.right Y.right := j.toAlgebra
  let : Algebra A B := g.hom.toAlgebra
  let : Algebra X.right B := (g.hom.comp b.right.hom).toAlgebra
  have : IsScalarTower X.right A B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.Etale X.right Y.right := hjE
  have hfY : ∀ r : X.right, v.right.hom (algebraMap X.right Y.right r) =
      algebraMap X.right B r := by
    intro r
    rw [show algebraMap X.right Y.right r = u.right.hom (q r) from rfl, huv']
    simp [hqdef, hφBdef, RingHom.algebraMap_toAlgebra]
  set fY : Y.right →ₐ[X.right] B := { v.right.hom with commutes' := hfY } with hfYdef
  set vAlg : A ⊗[X.right] Y.right →ₐ[A] B :=
    Algebra.TensorProduct.lift (Algebra.ofId A B) fY (fun _ _ ↦ Commute.all _ _) with hvAlg
  set θ : MvPolynomial (Fin n) A →+* A ⊗[X.right] Y.right :=
    MvPolynomial.eval₂Hom (algebraMap A (A ⊗[X.right] Y.right))
      (fun t ↦ Algebra.TensorProduct.includeRight
        (u.right.hom (Ideal.Quotient.mk I (MvPolynomial.X t)))) with hθdef
  have hθker : RingHom.ker π ≤ RingHom.ker θ := by
    rw [← hs, Ideal.span_le]
    intro z hz
    simp only [SetLike.mem_coe, RingHom.mem_ker]
    have h1 : (algebraMap A (A ⊗[X.right] Y.right)).comp b.right.hom =
        (Algebra.TensorProduct.includeRight :
          Y.right →ₐ[X.right] A ⊗[X.right] Y.right).toRingHom.comp j := by
      refine RingHom.ext fun x ↦ ?_
      show algebraMap A (A ⊗[X.right] Y.right) (algebraMap X.right A x) =
        Algebra.TensorProduct.includeRight (algebraMap X.right Y.right x)
      rw [← IsScalarTower.algebraMap_apply X.right A (A ⊗[X.right] Y.right)]
      exact ((Algebra.TensorProduct.includeRight
        (R := X.right) (A := A) (B := Y.right)).commutes x).symm
    have h3 : ∀ p : {p // p ∈ s}, θ (p : MvPolynomial (Fin n) A) = 0 := by
      intro p
      rw [hθdef, MvPolynomial.coe_eval₂Hom, ← hP p, MvPolynomial.eval₂_map, h1]
      rw [show (fun t ↦ Algebra.TensorProduct.includeRight
            (u.right.hom (Ideal.Quotient.mk I (MvPolynomial.X t)))) =
          fun t ↦ (Algebra.TensorProduct.includeRight :
            Y.right →ₐ[X.right] A ⊗[X.right] Y.right).toRingHom
            (u.right.hom (Ideal.Quotient.mk I (MvPolynomial.X t))) from rfl,
        ← MvPolynomial.hom_eval₂]
      have h4 : MvPolynomial.eval₂ j
          (fun t ↦ u.right.hom (Ideal.Quotient.mk I (MvPolynomial.X t))) (P p) = 0 := by
        rw [show (fun t ↦ u.right.hom (Ideal.Quotient.mk I (MvPolynomial.X t))) =
            fun t ↦ u.right.hom (Ideal.Quotient.mk I (MvPolynomial.X t)) from rfl,
          ← MvPolynomial.hom_eval₂]
        have h5 : MvPolynomial.eval₂ q (fun t ↦ Ideal.Quotient.mk I (MvPolynomial.X t)) (P p) =
            Ideal.Quotient.mk I (P p) := by
          have : (MvPolynomial.eval₂Hom q fun t ↦ Ideal.Quotient.mk I (MvPolynomial.X t)) =
              (Ideal.Quotient.mk I : MvPolynomial (Fin n) X.right →+* _) :=
            MvPolynomial.ringHom_ext (fun r ↦ by simp [hqdef]) (fun t ↦ by simp)
          exact congr($this (P p))
        have hPI : P p ∈ I := by
          rw [hIdef]; exact Ideal.subset_span (Set.mem_range_self p)
        rw [h5, Ideal.Quotient.eq_zero_iff_mem.2 hPI, map_zero]
      rw [h4]
      simp
    exact h3 ⟨z, hz⟩
  set uD : C.right →+* A ⊗[X.right] Y.right := RingHom.liftOfSurjective π hπs ⟨θ, hθker⟩
  have huDπ : ∀ y, uD (π y) = θ y := fun y ↦
    RingHom.liftOfSurjective_comp_apply π hπs ⟨θ, hθker⟩ y
  refine ⟨Under.mk (CommRingCat.ofHom (algebraMap A (A ⊗[X.right] Y.right))),
    Under.homMk (CommRingCat.ofHom uD) ?_,
    Under.homMk (CommRingCat.ofHom vAlg.toRingHom) ?_, ?_, ?_⟩
  · ext a
    have : C.hom.hom a = π (MvPolynomial.C a) := (congr($hπC a)).symm
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom, Under.mk_hom, this, huDπ, hθdef,
      MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
  · ext x
    simp [RingHom.algebraMap_toAlgebra]
  · refine Under.UnderMorphism.ext ?_
    ext x
    obtain ⟨y, rfl⟩ := hπs x
    have key : vAlg.toRingHom.comp θ = ψ.right.hom.comp π := by
      refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun t ↦ ?_)
      · have h6 := congr($hρ (MvPolynomial.C r))
        simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.coe_comp,
          Function.comp_apply] at h6
        simp only [RingHom.coe_comp, Function.comp_apply, hθdef, MvPolynomial.coe_eval₂Hom,
          MvPolynomial.eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        rw [vAlg.commutes r, RingHom.algebraMap_toAlgebra]
        exact h6
      · simp only [RingHom.coe_comp, Function.comp_apply, hθdef, MvPolynomial.coe_eval₂Hom,
          MvPolynomial.eval₂_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hvAlg]
        rw [show (Algebra.TensorProduct.lift (Algebra.ofId A B) fY
            (fun _ _ ↦ Commute.all _ _)) (Algebra.TensorProduct.includeRight
              (u.right.hom (Ideal.Quotient.mk I (MvPolynomial.X t)))) =
            fY (u.right.hom (Ideal.Quotient.mk I (MvPolynomial.X t))) from
          congr($(Algebra.TensorProduct.lift_comp_includeRight (Algebra.ofId A B) fY
            (fun _ _ ↦ Commute.all _ _)) _), hfYdef]
        simp only [AlgHom.coe_mk]
        rw [huv']
        simp [hφBdef, hbvals]
    have h7 := congr($key y)
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] at h7
    simpa [huDπ y] using h7
  · show (algebraMap A (A ⊗[X.right] Y.right)).Etale
    exact RingHom.etale_algebraMap.2 (Algebra.Etale.baseChange X.right Y.right A)

end CommRingCat

end

/-! ### Uniqueness of the henselization

Lemma 08HR produces, for an ind-étale `R`-algebra `A`, a prime `q` of `A` over `𝔪_S ∩ R` and a
`κ(𝔪_S ∩ R)`-algebra map `τ : κ(q) → κ(𝔪_S)`, a unique `R`-algebra map `A → S` cutting out `q`
and inducing `τ`. Taking `q = ker p` and for `τ` the composite `κ(ker p) ≅ K ≅ κ(𝔪_{S'})`
translates that datum into the single condition `p' ∘ f = p`, so 08HR already says that `f`
exists and is unique. Reading the same statement in the other direction gives `g : S' → S` over
`K`, and `g ∘ f`, `id_S` are two `R`-algebra maps `S → S` over `K`, hence equal; likewise
`f ∘ g = id_{S'}`.
-/

section

universe v w

open IsLocalRing Stacks.Henselian.EtaleLifting

/-- A surjection `f : S → K` from a local ring onto a field inverts to a ring map
`β : K →+* κ(S)` with `β ∘ f = residue S`; that is, `f` identifies `K` with the residue field of
`S`. It is the inverse of the isomorphism `IsLocalRing.ResidueField.lift f`. -/
private theorem exists_ringHom_comp_eq_residue {S K : Type*} [CommRing S] [IsLocalRing S] [Field K]
    (f : S →+* K) (hf : Function.Surjective f) :
    ∃ β : K →+* ResidueField S, β.comp f = residue S := by
  have _ : IsLocalHom f := hf.isLocalHom f
  have hbij : Function.Bijective (ResidueField.lift f) :=
    ⟨(ResidueField.lift f).injective,
      .of_comp (g := residue S) (by simpa [Function.comp_def] using hf)⟩
  refine ⟨((RingEquiv.ofBijective _ hbij).symm : K →+* ResidueField S), RingHom.ext fun x => ?_⟩
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
  exact (RingEquiv.ofBijective (ResidueField.lift f) hbij).symm_apply_eq.mpr
    (ResidueField.lift_residue_apply f x).symm

/-- A ring map `p : A → K` to a field factors through the residue field at its kernel: there is
`α : κ(ker p) →+* K` with `α ∘ (A → κ(ker p)) = p`. -/
private theorem exists_ringHom_comp_algebraMap_eq {A K : Type*} [CommRing A] [Field K]
    (p : A →+* K) [(RingHom.ker p).IsPrime] :
    ∃ α : (RingHom.ker p).ResidueField →+* K,
      α.comp (algebraMap A (RingHom.ker p).ResidueField) = p := by
  have h : (RingHom.ker p).primeCompl ≤ Submonoid.comap p (IsUnit.submonoid K) := fun x hx => by
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    simpa [RingHom.mem_ker] using (hx : x ∉ RingHom.ker p)
  exact ⟨Ideal.ResidueField.lift _ p le_rfl h,
    RingHom.ext (Ideal.ResidueField.lift_algebraMap _ p le_rfl h)⟩

/-- The comap condition of 08HR's residue datum is implied by the residue-map condition: if
`f : A → S` induces `τ` on residue fields at a prime `q`, then `q = f⁻¹(𝔪_S)`, because `τ` is a
map of fields, hence injective. -/
private theorem comap_maximalIdeal_eq_of_inducesResidueMap {A S : Type*} [CommRing A] [CommRing S]
    [IsLocalRing S] {q : Ideal A} [q.IsPrime] {f : A →+* S} {τ : q.ResidueField →+* ResidueField S}
    (h : InducesResidueMap q f τ) : q = (maximalIdeal S).comap f :=
  calc q = RingHom.ker (algebraMap A q.ResidueField) := (Ideal.ker_algebraMap_residueField q).symm
    _ = RingHom.ker (τ.comp (algebraMap A q.ResidueField)) :=
        (RingHom.ker_comp_of_injective _ τ.injective).symm
    _ = RingHom.ker ((residue S).comp f) := by rw [h]
    _ = (maximalIdeal S).comap f := by rw [← RingHom.comap_ker, ker_residue]

/-- **08HR's residue datum in terms of a surjection onto a field.** Let `p : A →ₐ[R] K` be an
`R`-algebra map to a field, let `S` be a local `R`-algebra and let `p' : S →ₐ[R] K` be a
surjection, so that `K` is the residue field of `S`; assume the prime `ker p` of `A` lies over
`𝔪_S ∩ R`. Then the composite `κ(ker p) ≅ K ≅ κ(𝔪_S)` is a residue datum `τ` for 08HR at
`ker p`, and an `R`-algebra map `f : A → S` cuts out `ker p` and induces `τ` if and only if
`p' ∘ f = p`. -/
private theorem exists_residueDatum {R A : Type u} {S : Type v} {K : Type w} [CommRing R]
    [CommRing A] [CommRing S] [Field K] [Algebra R A] [Algebra R S] [Algebra R K] [IsLocalRing S]
    (p : A →ₐ[R] K) (p' : S →ₐ[R] K) (hp' : Function.Surjective p')
    [(RingHom.ker (p : A →+* K)).IsPrime]
    (hpq : (maximalIdeal S).comap (algebraMap R S)
      = (RingHom.ker (p : A →+* K)).comap (algebraMap R A)) :
    ∃ τ : (RingHom.ker (p : A →+* K)).ResidueField →+* ResidueField S,
      τ.comp (residueFieldMapFib ((maximalIdeal S).comap (algebraMap R S))
          (RingHom.ker (p : A →+* K)) hpq)
          = residueFieldMapBase ((maximalIdeal S).comap (algebraMap R S)) rfl ∧
        ∀ f : A →ₐ[R] S, (RingHom.ker (p : A →+* K) = (maximalIdeal S).comap (f : A →+* S) ∧
          InducesResidueMap (RingHom.ker (p : A →+* K)) (f : A →+* S) τ) ↔ p'.comp f = p := by
  obtain ⟨β, hβ⟩ := exists_ringHom_comp_eq_residue (p' : S →+* K) hp'
  obtain ⟨α, hα⟩ := exists_ringHom_comp_algebraMap_eq (p : A →+* K)
  have hβapp : ∀ x : S, β (p' x) = residue S x := fun x => RingHom.congr_fun hβ x
  have hαapp : ∀ a : A, α (algebraMap A (RingHom.ker (p : A →+* K)).ResidueField a) = p a :=
    fun a => RingHom.congr_fun hα a
  refine ⟨β.comp α, Ideal.ResidueField.ringHom_ext (RingHom.ext fun r => ?_), fun f => ?_⟩
  · simp only [RingHom.comp_apply, residueFieldMapFib_algebraMap,
      residueFieldMapBase_algebraMap]
    rw [hαapp, p.commutes, ← p'.commutes, hβapp]
  · rw [and_iff_right_of_imp comap_maximalIdeal_eq_of_inducesResidueMap]
    refine (RingHom.ext_iff.trans <| forall_congr' fun a => ?_).trans AlgHom.ext_iff.symm
    simp only [RingHom.comp_apply, AlgHom.comp_apply, AlgHom.coe_toRingHom, hαapp, ← hβapp]
    exact β.injective.eq_iff.trans eq_comm

/-- **Lemma 08HR in terms of a surjection onto the residue field.** Let `A` be a filtered colimit
of étale `R`-algebras, let `S` be a henselian local `R`-algebra and let `p' : S → K` be a
surjection of `R`-algebras onto a field `K`, so that `K` is the residue field of `S`. Then for
every `R`-algebra map `p : A → K` there is exactly one `R`-algebra map `f : A → S` with
`p' ∘ f = p`.

Neither `A` local nor `p` surjective is assumed; specialising to `A` henselian local and `p`
surjective and reading the conclusion in all four directions is what proves Stacks 08HT. -/
@[ega "IV 18.6.2" "more general"]
theorem HenselianLocalRing.existsUnique_algHom_comp_of_ind_etale {R : Type u} [CommRing R]
    {A : Type u} [CommRing A] [Algebra R A] {S : Type v} [CommRing S] [Algebra R S]
    [HenselianLocalRing S]
    (hA : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R A))
    {K : Type w} [Field K] [Algebra R K] (p : A →ₐ[R] K) (p' : S →ₐ[R] K)
    (hp' : Function.Surjective p') :
    ∃! f : A →ₐ[R] S, p'.comp f = p := by
  have : (RingHom.ker (p : A →+* K)).IsPrime := RingHom.ker_isPrime _
  have hpq : (maximalIdeal S).comap (algebraMap R S)
      = (RingHom.ker (p : A →+* K)).comap (algebraMap R A) := by
    rw [← ker_eq_maximalIdeal (p' : S →+* K) hp', RingHom.comap_ker, RingHom.comap_ker,
      AlgHom.comp_algebraMap, AlgHom.comp_algebraMap]
  obtain ⟨τ, hτ, hiff⟩ := exists_residueDatum p p' hp' hpq
  have hAU : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R (ULift.{u} A)) :=
    ((CommAlgCat.etale.{u} R).ind.{u}).prop_of_iso
      (CommAlgCat.isoMk (ULift.algEquiv (R := R) (A := A)).symm) hA
  exact ⟨Stacks.Henselian.EtaleLifting.algHom hAU _ rfl _ hpq τ hτ,
    (hiff _).mp (Stacks.Henselian.EtaleLifting.algHom_spec hAU _ rfl _ hpq τ hτ),
    fun g hg => Stacks.Henselian.EtaleLifting.algHom_unique hAU _ rfl _ hpq τ hτ g ((hiff g).mpr
      hg)⟩

/-- **Two terminal objects are uniquely isomorphic**, for `R`-algebras over `K`. If there is
exactly one `R`-algebra map over `K` in each of the four directions `S → S'`, `S' → S`, `S → S`
and `S' → S'`, then the map `S → S'` is an isomorphism, and it is the unique `R`-algebra map
`S → S'` over `K`. -/
private theorem existsUnique_algEquiv_of_existsUnique {R S S' K : Type*} [CommRing R] [CommRing S]
    [CommRing S'] [CommRing K] [Algebra R S] [Algebra R S'] [Algebra R K] {p : S →ₐ[R] K}
    {p' : S' →ₐ[R] K} (h : ∃! f : S →ₐ[R] S', p'.comp f = p)
    (h' : ∃! g : S' →ₐ[R] S, p.comp g = p') (hS : ∃! i : S →ₐ[R] S, p.comp i = p)
    (hS' : ∃! i : S' →ₐ[R] S', p'.comp i = p') :
    ∃ e : S ≃ₐ[R] S', ∀ f : S →ₐ[R] S', p'.comp f = p ↔ f = (e : S →ₐ[R] S') := by
  obtain ⟨f, hf, hfu⟩ := h
  obtain ⟨g, hg, -⟩ := h'
  refine ⟨AlgEquiv.ofAlgHom f g (hS'.unique (by rw [← AlgHom.comp_assoc, hf]; exact hg)
    (AlgHom.comp_id p')) (hS.unique (by rw [← AlgHom.comp_assoc, hg]; exact hf)
    (AlgHom.comp_id p)), fun f₀ => ?_⟩
  rw [AlgEquiv.toAlgHom_ofAlgHom]
  exact ⟨hfu f₀, fun h => h ▸ hf⟩

/-- **Uniqueness of the henselization** (Stacks 08HT). Let `R` be a ring, let `S` and `S'` be
henselian local `R`-algebras that are filtered colimits of étale `R`-algebras, and let
`p : S →ₐ[R] K` and `p' : S' →ₐ[R] K` be surjections onto a field `K`, so that `K` is the residue
field of both. Then there is an `R`-algebra isomorphism `e : S ≃ₐ[R] S'` such that an `R`-algebra
map `f : S → S'` satisfies `p' ∘ f = p` if and only if `f = e`; in particular `e` is the unique
`R`-algebra isomorphism `S → S'` compatible with the maps to `K`. -/
@[stacks 08HT "\"`S` is a filtered colimit of étale `R`-algebras\" is
`(CommAlgCat.etale R).ind (CommAlgCat.of R S)`, as in Lemma 04GN; the source's commutative square
is the two `R`-algebra maps to `K`; and \"the arrows identify `K` with the residue field\" is their
surjectivity, `K` being a field. Uniqueness is stated among all `R`-algebra maps `S → S'`, which is
stronger than the source's uniqueness among isomorphisms. See the module docstring."]
theorem HenselianLocalRing.existsUnique_algEquiv_of_ind_etale
    {R : Type u} [CommRing R] {S S' : Type u} [CommRing S] [CommRing S'] [Algebra R S]
    [Algebra R S'] [HenselianLocalRing S] [HenselianLocalRing S']
    (hS : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R S))
    (hS' : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R S'))
    {K : Type v} [Field K] [Algebra R K] (p : S →ₐ[R] K) (p' : S' →ₐ[R] K)
    (hp : Function.Surjective p) (hp' : Function.Surjective p') :
    ∃ e : S ≃ₐ[R] S', ∀ f : S →ₐ[R] S', p'.comp f = p ↔ f = (e : S →ₐ[R] S') :=
  existsUnique_algEquiv_of_existsUnique (existsUnique_algHom_comp_of_ind_etale hS p p' hp')
    (existsUnique_algHom_comp_of_ind_etale hS' p' p hp)
    (existsUnique_algHom_comp_of_ind_etale hS p p hp)
    (existsUnique_algHom_comp_of_ind_etale hS' p' p' hp')

end

/-! ### Ind-étale ring maps as a morphism property

Étale ring maps form a morphism property `CommRingCat.etale` on `CommRingCat`, stable under
composition and under cobase change, and being a filtered colimit of étale `R`-algebras is being
an ind-étale ring map for that property: `CommAlgCat.ind_etale_iff_ind_algebraMap` below, the
transport along the equivalence `CategoryTheory.commAlgCatEquivUnder`. That makes Mathlib's API
for `CategoryTheory.MorphismProperty.ind` available for the spelling of ind-étaleness the
henselization results take as a hypothesis, and reduces cobase change (Lemma 0BSH) to the
stability of `MorphismProperty.ind` under cobase change and cancellation (Lemma 08HS) to
`CommRingCat.ind_etale_of_comp`.

Composition (Lemma 0BSI) is the one that needs an argument. By the criterion of Lemma 07C3 it is
enough to factor every `A`-algebra map `P → C` with `P` of finite presentation over `A` through an
étale `A`-algebra. Write `B = colim_{i ∈ I} Bᵢ` with `Bᵢ` étale over `A` and `C = colim_{j ∈ J} Cⱼ`
with `Cⱼ` étale over `B`. As `P` is of finite presentation over `A`, the map `P → C` factors
through some `Cⱼ`. As `Cⱼ` is étale over `B = colim Bᵢ`, it is the base change `B ⊗_{Bᵢ} C'ⱼ` of an
étale `Bᵢ`-algebra `C'ⱼ` for some `i ∈ I` (item (9) of Lemma 00U2, `exists_isPushout_etale`
below); hence `Cⱼ = colim_{i' ≥ i} B_{i'} ⊗_{Bᵢ} C'ⱼ` and `P → Cⱼ` factors through
`C' = B_{i'} ⊗_{Bᵢ} C'ⱼ` for some `i' ≥ i`. Finally `C'` is étale over `A`, because étale ring
maps are stable under base change and under composition, so 07C3 applies.
-/

section

open Limits TensorProduct

namespace CommRingCat

/-- The morphism property of étale ring maps. -/
def etale : MorphismProperty CommRingCat.{u} :=
  RingHom.toMorphismProperty fun f ↦ f.Etale

/-- A morphism of commutative rings lies in `etale` if and only if its underlying ring map is
étale. -/
@[simp] lemma etale_iff {R S : CommRingCat.{u}} (f : R ⟶ S) : etale f ↔ f.hom.Etale := .rfl

/-- The morphism `ofHom f` lies in `etale` if and only if the ring map `f` is étale. -/
lemma etale_ofHom_iff {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    etale (ofHom f) ↔ f.Etale := .rfl

/-- The class of étale ring maps respects isomorphisms. -/
instance : (etale.{u}).RespectsIso :=
  RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso

/-- A composite of étale ring maps is étale. -/
instance : (etale.{u}).IsStableUnderComposition where
  comp_mem _ _ hf hg := RingHom.Etale.stableUnderComposition _ _ hf hg

/-- Étale ring maps are stable under cobase change. -/
instance : (etale.{u}).IsStableUnderCobaseChange := by
  rw [etale, RingHom.isStableUnderCobaseChange_toMorphismProperty_iff]
  exact RingHom.Etale.isStableUnderBaseChange

end CommRingCat

/-- `etale_le_finitePresentation` in the `MorphismProperty.underObj` spelling, which is the one
`CommRingCat.ind_under_iff_exists_factorization` rewrites with in `ind_comp`. -/
private lemma etale_underObj_le_finitePresentation {X : CommRingCat.{u}} :
    (CommRingCat.etale.{u}).underObj (X := X) ≤
      fun D : Under X ↦ D.hom.hom.FinitePresentation :=
  etale_le_finitePresentation X

/-- A ring of finite presentation over `ℤ` is a finitely presentable object of `CommRingCat`.

This is Mathlib's `CommRingCat.isFinitelyPresentable_under` read at the initial object: `ULift ℤ`
is initial in `CommRingCat`, so `Under (CommRingCat.of (ULift ℤ))` is `CommRingCat` itself, and a
ring of finite presentation over `ℤ` is a finitely presented algebra over `ULift ℤ`. -/
lemma isFinitelyPresentable_of_finitePresentation (R : CommRingCat.{u})
    (h : Algebra.FinitePresentation ℤ R) : IsFinitelyPresentable.{u} R := by
  have := Cardinal.fact_isRegular_aleph0.{u}
  have hfp : (CommRingCat.isInitial.to R).hom.FinitePresentation := by
    rw [CommRingCat.isInitial.hom_ext (CommRingCat.isInitial.to R)
      (CommRingCat.ofHom ((algebraMap ℤ R).comp ULift.ringEquiv.toRingHom)),
      CommRingCat.hom_ofHom]
    exact (RingHom.finitePresentation_algebraMap.mpr h).comp
      (.of_bijective ULift.ringEquiv.bijective)
  have : IsFinitelyPresentable.{u} (Under.mk (CommRingCat.isInitial.to R)) :=
    CommRingCat.isFinitelyPresentable_under _ _ hfp
  have : (Under.forget (CommRingCat.of (ULift.{u} ℤ))).IsEquivalence := by
    rw [← Under.equivalenceOfIsInitial_functor CommRingCat.isInitial]
    infer_instance
  exact isCardinalPresentable_of_isEquivalence (Under.mk (CommRingCat.isInitial.to R)) _
    (Under.forget _)

/-- A ring presented as a base change is the vertex of a pushout square: if `T` is isomorphic to
`S ⊗[R] E` as an `S`-algebra, then
```
  R ---> E
  |      |
  v      v
  S ---> T
```
is a pushout square in `CommRingCat`, the map `E → T` being `e.symm` on `1 ⊗ ·`. -/
@[ega "IV 8.2.7" "special case"]
lemma isPushout_of_algEquiv_tensorProduct (R S E T : Type u) [CommRing R] [CommRing S]
    [CommRing E] [CommRing T] [Algebra R S] [Algebra R E] [Algebra S T]
    (e : T ≃ₐ[S] S ⊗[R] E) :
    IsPushout (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R E))
      (CommRingCat.ofHom (algebraMap S T))
      (CommRingCat.ofHom (e.symm.toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := E)).toRingHom)) :=
  (CommRingCat.isPushout_tensorProduct R S E).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    e.symm.toRingEquiv.toCommRingCatIso (by simp) (by simp)
    (by ext x; exact e.symm.commutes x) (by simp)

/-- **Item (9) of Lemma 00U2.** Let `B = colim_i B_i` be a filtered colimit of rings and let
`B → E` be étale. Then `E` is the base change of an étale ring map `B_i → E'` for some `i`, that
is, the square
```
  B_i ---> E'
   |        |
   v        v
   B -----> E
```
is a pushout square with `B_i → E'` étale.

This is `CategoryTheory.MorphismProperty.PreIndSpreads` for the property of being étale. It is
deduced from item (8) of the same lemma, `Algebra.Etale.exists_subalgebra_fg`: an étale algebra
`B → E` is already the base change of an étale algebra `E₀` over a `ℤ`-subalgebra `A₀ ⊆ B` of
finite type. As `ℤ` is Noetherian, `A₀` is of finite presentation over `ℤ`, hence a finitely
presentable object of `CommRingCat`, so `A₀ → B` factors through some `B_i` and a pushout square
over a factored map factors into two pushout squares. -/
lemma exists_isPushout_etale {J : Type u} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ CommRingCat.{u}} {c : Cocone D} (hc : IsColimit c) {T : CommRingCat.{u}}
    (f : c.pt ⟶ T) (hf : CommRingCat.etale.{u} f) :
    ∃ (j : J) (T' : CommRingCat.{u}) (f' : D.obj j ⟶ T') (g : T' ⟶ T),
      IsPushout (c.ι.app j) f' f g ∧ CommRingCat.etale.{u} f' := by
  have hf' : f.hom.Etale := hf
  algebraize [f.hom]
  obtain ⟨A₀, E₀, _, _, hfg, hE, ⟨e⟩⟩ :=
    Algebra.Etale.exists_subalgebra_fg ℤ (c.pt : Type u) (T : Type u)
  have : IsFinitelyPresentable.{u} (CommRingCat.of ↥A₀) :=
    isFinitelyPresentable_of_finitePresentation _
      (Algebra.FinitePresentation.of_finiteType.mp ⟨A₀.fg_top.mpr hfg⟩)
  obtain ⟨j, ψ, hψ⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc
    (CommRingCat.ofHom (algebraMap ↥A₀ (c.pt : Type u)))
  have s := isPushout_of_algEquiv_tensorProduct ↥A₀ (c.pt : Type u) E₀ (T : Type u) e
  rw [← hψ] at s
  exact ⟨j, _, _, _, IsPushout.of_left' s (IsPushout.of_hasPushout ψ _),
    CommRingCat.etale.pushout_inl ψ _ (RingHom.etale_algebraMap.mpr hE)⟩

-- Needed: `CommRingCat.etale.pushout_inl` needs `IsStableUnderCobaseChangeAlong` on an
-- `Under.post` structure map, which synthesizes only at `default` transparency.
set_option backward.isDefEq.respectTransparency false in
/-- The composition of two ind-étale ring maps is ind-étale: the argument of the source,
which is Mathlib's `MorphismProperty.IsStableUnderComposition.ind_of_preIndSpreads` with the
criterion of Lemma 07C3 in place of `MorphismProperty.ind_iff_exists`. -/
private lemma ind_comp {X Y Z : CommRingCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : MorphismProperty.ind.{u} CommRingCat.etale.{u} f)
    (hg : MorphismProperty.ind.{u} CommRingCat.etale.{u} g) :
    MorphismProperty.ind.{u} CommRingCat.etale.{u} (f ≫ g) := by
  rw [MorphismProperty.ind_iff_ind_underMk,
    CommRingCat.ind_under_iff_exists_factorization _ etale_underObj_le_finitePresentation]
  intro A hA φ
  obtain ⟨J₁, _, _, D₁, s₁, t₁, ht₁, h₁⟩ := hf
  obtain ⟨J₂, _, _, D₂, s₂, t₂, ht₂, h₂⟩ := hg
  have hpu : A.hom ≫ φ.right = f ≫ g := Under.w φ
  have hp : IsFinitelyPresentable.{u} (Under.mk A.hom) :=
    CommRingCat.isFinitelyPresentable_hom A.hom hA
  obtain ⟨j₂, q, hcomp, hu⟩ := IsFinitelyPresentable.exists_hom_of_isColimit_under
      ht₂ A.hom ((Functor.const _).map f ≫ s₂) φ.right <| by simp [h₂, hpu]
  obtain ⟨j₁, W, f', g', h, hf'⟩ := exists_isPushout_etale ht₁ (s₂.app j₂) (h₂ j₂).left
  let D' : Under j₁ ⥤ CommRingCat.{u} :=
    (Under.post D₁ ⋙ Under.pushout f') ⋙ Under.forget _
  let c' : Cocone D' :=
    (Under.pushout f' ⋙ Under.forget _).mapCocone ((Cocone.mk _ t₁).underPost j₁)
      |>.extend h.isoPushout.inv
  let hc' : IsColimit c' :=
    IsColimit.extendIso _ <| isColimitOfPreserves _ (ht₁.underPost j₁)
  let s' : (Functor.const (Under j₁)).obj X ⟶ D' :=
    { app k := s₁.app k.right ≫ pushout.inl _ _
      naturality k l a := by
        have h2 := s₁.naturality a.right
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at h2
        simp [h2, D'] }
  obtain ⟨j₃, v, hcomp', hq⟩ := IsFinitelyPresentable.exists_hom_of_isColimit_under
      hc' A.hom s' q <| fun k ↦ by
    simp [c', s', hcomp, reassoc_of% (h₁ k.right).right]
  refine ⟨Under.mk (A.hom ≫ v), Under.homMk v rfl,
    Under.homMk (c'.ι.app j₃ ≫ t₂.app j₂) ?_, ?_, ?_⟩
  · show (A.hom ≫ v) ≫ c'.ι.app j₃ ≫ t₂.app j₂ = f ≫ g
    rw [← hpu, ← hu, ← hq]
    simp
  · refine Under.UnderMorphism.ext ?_
    show v ≫ c'.ι.app j₃ ≫ t₂.app j₂ = φ.right
    rw [← hu, ← hq]
    simp
  · show CommRingCat.etale.{u} (A.hom ≫ v)
    rw [hcomp']
    exact CommRingCat.etale.comp_mem _ _ (h₁ _).left
      (CommRingCat.etale.pushout_inl _ _ hf')

namespace CommAlgCat

/-- **Ind-étaleness of an algebra is ind-étaleness of its structure map.** Being a filtered colimit
of étale `R`-algebras, in the spelling `(CommAlgCat.etale R).ind` of Definition 04GQ, is being an
ind-étale ring map for the morphism property `CommRingCat.etale`. -/
theorem ind_etale_iff_ind_algebraMap {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ] :
    (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R Λ) ↔
      MorphismProperty.ind.{u} CommRingCat.etale.{u}
        (CommRingCat.ofHom (algebraMap R Λ)) := by
  have hinv : (CommAlgCat.etale.{u} R) = (CommRingCat.etale.{u}).underObj.inverseImage
      (commAlgCatEquivUnder (CommRingCat.of R)).functor := by
    ext S
    show Algebra.Etale R S ↔ RingHom.Etale (algebraMap R S)
    rw [RingHom.etale_algebraMap]
  rw [MorphismProperty.ind_iff_ind_underMk,
    ← ObjectProperty.ind_iff_of_equivalence (CommRingCat.etale.{u}).underObj
      (commAlgCatEquivUnder (CommRingCat.of R)) (Under.mk (CommRingCat.ofHom (algebraMap R Λ))),
    ← hinv]
  exact (ObjectProperty.ind.{u} (CommAlgCat.etale.{u} R)).prop_iff_of_iso
    ((commAlgCatEquivUnder (CommRingCat.of R)).unitIso.app (CommAlgCat.of R Λ))

/-- **An ind-étale algebra stays ind-étale after cobase change.** Let `R → S` and `R → R'` be ring
maps and let `S'` be a pushout of `S` and `R'` over `R`, that is, `S' = S ⊗[R] R'`. If `R'` is a
filtered colimit of étale `R`-algebras, then `S'` is a filtered colimit of étale `S`-algebras. -/
@[stacks 0BSH "\"`Λ` is a filtered colimit of étale `R`-algebras\" is
`(CommAlgCat.etale R).ind.{u} (CommAlgCat.of R Λ)`, as in Lemma `04GN`, and the source's `S ⊗_R R'`
is an abstract `Algebra.IsPushout R S R' S'` rather than a model of the tensor product. Tagged
jointly with `filteredColimitEtale_baseChange`, which is this lemma for the predicate
`IsFilteredColimitOfEtale` and the model `TensorProduct R R' A`. See the module docstring."]
theorem ind_etale_of_isPushout (R S R' S' : Type u) [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S']
    [Algebra R' S'] [IsScalarTower R S S'] [IsScalarTower R R' S']
    [Algebra.IsPushout R S R' S']
    (h : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R R')) :
    (CommAlgCat.etale.{u} S).ind.{u} (CommAlgCat.of S S') := by
  rw [ind_etale_iff_ind_algebraMap] at h ⊢
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
    (CommRingCat.isPushout_of_isPushout R S R' S') h

/-- The structure map of a tower `A → B → C` is the composite of the structure maps. -/
private lemma ofHom_algebraMap_comp (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    CommRingCat.ofHom (algebraMap A C) =
      CommRingCat.ofHom (algebraMap A B) ≫ CommRingCat.ofHom (algebraMap B C) := by
  ext x; exact IsScalarTower.algebraMap_apply A B C x

/-- **A filtered colimit of étale algebras over a filtered colimit of étale algebras.** Let
`A → B → C` be ring maps. If `B` and `C` are filtered colimits of étale `A`-algebras, then `C` is
a filtered colimit of étale `B`-algebras. -/
@[stacks 08HS "\"`Λ` is a filtered colimit of étale `R`-algebras\" is
`(CommAlgCat.etale R).ind.{u} (CommAlgCat.of R Λ)`, as in Lemma `04GN`, and the source's
`A → B → C` is an `IsScalarTower A B C`. Tagged jointly with `CommRingCat.ind_etale_of_comp`,
which is this lemma for ring maps and the `ObjectProperty.ind` spelling on `Under R`. See the
module docstring."]
theorem ind_etale_of_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hB : (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A B))
    (hC : (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A C)) :
    (CommAlgCat.etale.{u} B).ind.{u} (CommAlgCat.of B C) := by
  rw [ind_etale_iff_ind_algebraMap, MorphismProperty.ind_iff_ind_underMk] at hB hC ⊢
  rw [ofHom_algebraMap_comp A B C] at hC
  exact CommRingCat.ind_etale_of_comp _ _ hB hC

/-- **A filtered colimit of étale algebras over a filtered colimit of étale algebras.** Let
`A → B → C` be ring maps. If `B` is a filtered colimit of étale `A`-algebras and `C` is a
filtered colimit of étale `B`-algebras, then `C` is a filtered colimit of étale `A`-algebras. -/
theorem ind_etale_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hB : (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A B))
    (hC : (CommAlgCat.etale.{u} B).ind.{u} (CommAlgCat.of B C)) :
    (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A C) := by
  rw [ind_etale_iff_ind_algebraMap] at hB hC ⊢
  rw [ofHom_algebraMap_comp A B C]
  exact ind_comp _ _ hB hC

end CommAlgCat

end
