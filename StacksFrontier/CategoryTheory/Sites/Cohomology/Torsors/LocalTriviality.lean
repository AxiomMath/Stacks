module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FirstCocycles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# First Čech cohomology and torsors trivial on a covering

Let `(C, J)` be a site, let `G` be an abelian sheaf on it, let `U` be an object of `C` and let
`𝒰 = {U_i → U}_{i ∈ I}` be a family of morphisms with target `U`. A torsor under the
restriction `G|_U` of `G` to the localized site `(C/U, J.over U)` which has a section over every
member of the family carries a Čech `1`-cocycle of differences: over the fibre product
`U_{i₀} ×_U U_{i₁}` the unique section of `G` carrying the restriction of `s_{i₀}` to the
restriction of `s_{i₁}`. Its class in `Ȟ¹(𝒰, G)` depends neither on the chosen sections nor on
the torsor inside its isomorphism class, and it vanishes exactly when the torsor is trivial.

## Main definitions

* `SheafOfGroups.over` and `PseudoTorsor.over`: the restrictions of a sheaf of groups and of a
  pseudo-torsor under it to a localized site.
* `Stacks.Cohomology.Torsors.transitionCocycle`: the Čech `1`-cocycle of differences of a family
  of local sections of a torsor.
* `Stacks.Cohomology.Torsors.IsLocallyTrivialOn`: an isomorphism class of torsors under `G|_U`
  is *locally trivial on* `𝒰` when it has a representative with a section over every member.
* `Stacks.Cohomology.Torsors.cechClass`: the Čech cohomology class of a locally trivial
  isomorphism class of torsors.

## Main results

* `PseudoTorsor.isTrivial_over_iff`: a pseudo-torsor restricts to a trivial pseudo-torsor on the
  localized site at `V` exactly when it has a section over `V`. Together with
  `Stacks.Cohomology.Torsors.isTrivialOnMembers_iff` this says that the torsors under `G|_U`
  which restrict to trivial torsors over each `U_i` are exactly the ones with a section over
  each `U_i`.
* `Stacks.Cohomology.Torsors.cls_transitionCocycle_congr` and
  `Stacks.Cohomology.Torsors.cls_transitionCocycle_eq_of_isIsomorphic`: the Čech class of the
  transition cocycle depends neither on the chosen family of local sections nor on the torsor
  inside its isomorphism class.
* `Stacks.Cohomology.Torsors.cechClass_eq_zero_of_isTrivial`: a trivial torsor has vanishing
  Čech class.
* `Stacks.Cohomology.Torsors.isTrivial_iff_exists_transitionCochain_eq_zero`: for a covering
  family, a torsor is trivial exactly when some family of local sections has vanishing
  transition cochain; the substantial direction,
  `Stacks.Cohomology.Torsors.isTrivial_of_transitionCochain_eq_zero`, glues such a family to a
  section over the terminal object of `C/U`.

## Implementation notes

A covering family `{U_i → U}` is a `CategoryTheory.PreZeroHypercover U`, as in Stacks 03AM, and
its members are the objects `Over.mk (E.f i)` of `C/U`; the iterated fibre products
`U_{i₀} ×_U ⋯ ×_U U_{i_p}` are the products of those objects taken in `C/U`, whose existence is
carried as an instance hypothesis rather than deduced from finite limits in `C`. Consequently a
section of `G|_U` over such a fibre product is literally a degree-`p` Čech cochain factor
`Stacks.CechSite.cochainFactor`, and the transition cochain of a family of local sections is a
Čech cochain with no transport along a comparison isomorphism.

The differences of sections are `Stacks.Cohomology.Torsors.torsorDifference` for the site
`(C/U, J.over U)`: the convention there is that `torsorDifference H F V s s'` is the section of
`H` carrying `s'` to `s`, so the transition cochain at a pair `(i₀, i₁)` is the difference of
the restriction of `s_{i₁}` by the restriction of `s_{i₀}`, which is the normalization of the
source. The cocycle identity is then exactly transitivity of differences, and a change of the
local sections changes the cochain by the Čech coboundary of their differences.

The restriction of a torsor to a localized site is taken at an object of `C/U`, so "trivial over
`U_i`" is read as triviality on the localization of `(C/U, J.over U)` at `Over.mk (E.f i)`,
rather than on `(C/U_i, J.over U_i)`; the two sites are identified by the canonical equivalence
`(C/U)/(U_i → U) ≌ C/U_i`, which is not used here.

What is *not* proved here is the comparison with sheaf cohomology: that the Čech class of the
transition cocycle corresponds, under the bijection of Stacks 03AJ, to the image of the Čech
class under the comparison map of Stacks 03AX. Injectivity of that comparison map is
`Stacks.CechSite.injective_cechH1ToCohomology`, proved by a different route, and the image in
`H¹(U, G)` of the Čech class of the transition cocycle is
`Stacks.CechSite.torsorCohomologyClass`, which is injective on the locally trivial classes and
vanishes exactly on the trivial torsor.
Nor is the bijection between `Ȟ¹(𝒰, G)` and the locally trivial isomorphism classes
established: `Stacks.Cohomology.Torsors.isTrivial_of_transitionCochain_eq_zero` is its
injectivity at the trivial class, for a transition cochain that vanishes on the nose rather than
only up to a Čech coboundary. Its injectivity, at the trivial class and in general, is
`Stacks.Cohomology.Torsors.cechClass_injective`; surjectivity would need a torsor built from a
prescribed cocycle.

## References

* [Stacks Project, Tag 0A6G](https://stacks.math.columbia.edu/tag/0A6G)
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 03AI](https://stacks.math.columbia.edu/tag/03AI)
* [Stacks Project, Tag 03AX](https://stacks.math.columbia.edu/tag/03AX)
* [Stacks Project, Tag 0B8R](https://stacks.math.columbia.edu/tag/0B8R), the same statement for
  an open covering of a topological space.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe h t w v u

/-! ### Restriction of a torsor to a localized site -/

section Slice

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The restriction of a sheaf of groups on `(C, J)` to the localized site `(C/V, J.over V)`:
its sections over an object `W → V` are the sections over `W`. -/
def SheafOfGroups.over (𝒢 : SheafOfGroups.{t} (C := C) J) (V : C) :
    SheafOfGroups.{t} (C := Over V) (J.over V) where
  presheaf := (Over.forget V).op ⋙ 𝒢.presheaf
  isSheaf := ((J.overPullback (Type t) V).obj ⟨𝒢.presheaf, 𝒢.isSheaf⟩).property
  group _ := 𝒢.group _
  map_mul f a b := 𝒢.map_mul ((Over.forget V).op.map f) a b

variable {𝒢 : SheafOfGroups.{t} (C := C) J}

/-- The restriction of a pseudo-torsor to the localized site `(C/V, J.over V)`, a pseudo-torsor
under the restriction of the sheaf of groups. -/
def PseudoTorsor.over (F : PseudoTorsor.{t} 𝒢) (V : C) :
    PseudoTorsor.{t} (𝒢.over V) where
  presheaf := (Over.forget V).op ⋙ F.presheaf
  isSheaf := ((J.overPullback (Type t) V).obj ⟨F.presheaf, F.isSheaf⟩).property
  act _ g s := F.act _ g s
  one_act _ s := F.one_act _ s
  mul_act _ g g' s := F.mul_act _ g g' s
  naturality f g s := F.naturality ((Over.forget V).op.map f) g s
  simplyTransitive _ hne s t := F.simplyTransitive _ hne s t

/-- The restriction of a torsor to a localized site is a torsor: a covering of the image of an
object of `C/V` is a covering of that object. -/
lemma PseudoTorsor.over_isTorsor (F : PseudoTorsor.{t} 𝒢) (hF : F.IsTorsor) (V : C) :
    (F.over V).IsTorsor := by
  intro W
  obtain ⟨S, hS, hne⟩ := hF W.left
  exact ⟨(Sieve.overEquiv W).symm S, J.overEquiv_symm_mem_over W S hS,
    fun _ _ hf ↦ hne hf⟩

/-- Global sections of a presheaf restricted to a localized site are its sections over the
object at which the site is localized: a compatible family on `C/V` is determined by its value
at the identity, and every section over `V` extends to one by restriction. -/
lemma nonempty_globalSections_comp_forget_iff (P : Cᵒᵖ ⥤ Type t) (V : C) :
    Nonempty (GlobalSections ((Over.forget V).op ⋙ P)) ↔ Nonempty (P.obj (op V)) := by
  rw [Stacks.Cohomology.Torsors.nonempty_globalSections_iff_sectionFamily]
  constructor
  · rintro ⟨s, -⟩
    exact ⟨s (op (Over.mk (𝟙 V)))⟩
  · rintro ⟨x⟩
    refine ⟨fun W ↦ P.map (W.unop.hom).op x, ?_⟩
    intro W W' f
    change P.map (f.unop.left).op (P.map (W.unop.hom).op x) = P.map (W'.unop.hom).op x
    rw [← Functor.map_comp_apply, ← op_comp, Over.w f.unop]

/-- **The torsors trivial over an object.** A pseudo-torsor restricts to a trivial pseudo-torsor
on the localized site at `V` exactly when it has a section over `V`. This is Stacks 03AI on the
localized site, where global sections are the sections over `V`. -/
theorem PseudoTorsor.isTrivial_over_iff (F : PseudoTorsor.{t} 𝒢) (V : C) :
    (F.over V).IsTrivial ↔ Nonempty (F.presheaf.obj (op V)) := by
  rw [← nonempty_globalSections_comp_forget_iff F.presheaf V]
  exact ⟨nonempty_globalSections_of_isTrivial (F.over V),
    isTrivial_of_nonempty_globalSections (F.over V)⟩

/-- A pseudo-torsor with a section over every object of the site is trivial. -/
lemma PseudoTorsor.isTrivial_of_terminal_section {V : C} (hV : Limits.IsTerminal V)
    (F : PseudoTorsor.{t} 𝒢) (x : F.presheaf.obj (op V)) : F.IsTrivial := by
  refine isTrivial_of_nonempty_globalSections F
    ((Stacks.Cohomology.Torsors.nonempty_globalSections_iff_sectionFamily F.presheaf).2
      ⟨fun W ↦ F.presheaf.map (hV.from W.unop).op x, ?_⟩)
  intro W W' f
  change F.presheaf.map f.unop.op (F.presheaf.map (hV.from W.unop).op x) =
    F.presheaf.map (hV.from W'.unop).op x
  rw [← Functor.map_comp_apply, ← op_comp,
    hV.hom_ext (f.unop ≫ hV.from W.unop) (hV.from W'.unop)]

end Slice

namespace Stacks.Cohomology.Torsors

open Stacks.CechSite

/-! ### Differences of sections of a torsor -/

section Difference

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{t}] [HasExt.{h} (Sheaf J AddCommGrpCat.{t})]
  (H : Sheaf J AddCommGrpCat.{t})

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{h} (Sheaf J AddCommGrpCat.{t})] in
/-- An equivariant morphism of torsors preserves differences of sections. -/
lemma torsorDifference_hom {F F' : AbelianTorsor H} (e : F.1.Hom F'.1) (V : Cᵒᵖ)
    (x y : F.1.presheaf.obj V) :
    torsorDifference H F' V (e.hom.app V x) (e.hom.app V y) = torsorDifference H F V x y := by
  apply torsorDifference_eq_of_act
  exact (e.map_act V (Multiplicative.ofAdd (torsorDifference H F V x y)) y).symm.trans
    (congrArg _ (torsorDifference_act H F V x y))

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{h} (Sheaf J AddCommGrpCat.{t})] in
/-- Differences of sections of a torsor satisfy the parallelogram identity: the two ways of
comparing the pairs `(x, x')` and `(y, y')` agree, both being a decomposition of the difference
of `x` and `y'`. -/
lemma torsorDifference_sub_comm (F : AbelianTorsor H)
    (V : Cᵒᵖ) (x x' y y' : F.1.presheaf.obj V) :
    torsorDifference H F V x x' - torsorDifference H F V y y' =
      torsorDifference H F V x y - torsorDifference H F V x' y' := by
  rw [sub_eq_sub_iff_add_eq_add, ← torsorDifference_trans H F V x x' y',
    ← torsorDifference_trans H F V x y y']

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{h} (Sheaf J AddCommGrpCat.{t})] in
/-- The zero section of the coefficient sheaf acts trivially, the unit of the multiplicative
group underlying it being the image of zero. -/
lemma act_zero (F : AbelianTorsor H) (V : Cᵒᵖ) (y : F.1.presheaf.obj V) :
    F.1.act V (Multiplicative.ofAdd (0 : H.obj.obj V)) y = y :=
  F.1.one_act V y

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{h} (Sheaf J AddCommGrpCat.{t})] in
/-- Two sections of a torsor with vanishing difference are equal. -/
lemma eq_of_torsorDifference_eq_zero (F : AbelianTorsor H) (V : Cᵒᵖ)
    (x y : F.1.presheaf.obj V) (hxy : torsorDifference H F V x y = 0) : x = y :=
  (torsorDifference_act H F V x y).symm.trans
    ((congrArg (fun a ↦ F.1.act V (Multiplicative.ofAdd a) y) hxy).trans (act_zero H F V y))

end Difference

/-! ### The transition cocycle of a family of local sections -/

section Transition

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
  (E : PreZeroHypercover.{w} U) (G : Sheaf J AddCommGrpCat.{t})
  [HasProducts.{w} AddCommGrpCat.{t}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})]

/-- The restriction of the local section indexed by `k m` to the iterated fibre product indexed
by the tuple `k`. -/
def sectionRestriction (F : AbelianTorsor (G.over U))
    (s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i)))) {n : ℕ} (k : Fin (n + 1) → E.I₀)
    (m : Fin (n + 1)) : F.1.presheaf.obj (op (∏ᶜ fun j ↦ Over.mk (E.f (k j)))) :=
  F.1.presheaf.map (Pi.π (fun j ↦ Over.mk (E.f (k j))) m).op (s (k m))

omit [HasProducts.{w} AddCommGrpCat.{t}] [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- Restricting a local section along a face projection of an iterated fibre product is
restricting it along the corresponding projection of the bigger product. -/
lemma map_sectionRestriction (F : AbelianTorsor (G.over U))
    (s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i)))) {n : ℕ} (k : Fin (n + 2) → E.I₀)
    (j : Fin (n + 2)) (m : Fin (n + 1)) :
    F.1.presheaf.map (faceProjection E k j).op
        (sectionRestriction E G F s (fun b ↦ k (j.succAbove b)) m) =
      sectionRestriction E G F s k (j.succAbove m) := by
  have hc : faceProjection E k j ≫ Pi.π (fun b ↦ Over.mk (E.f (k (j.succAbove b)))) m =
      Pi.π (fun c ↦ Over.mk (E.f (k c))) (j.succAbove m) := Pi.lift_comp_π _ _
  change F.1.presheaf.map (faceProjection E k j).op
      (F.1.presheaf.map (Pi.π (fun b ↦ Over.mk (E.f (k (j.succAbove b)))) m).op
        (s (k (j.succAbove m)))) =
    F.1.presheaf.map (Pi.π (fun c ↦ Over.mk (E.f (k c))) (j.succAbove m)).op
      (s (k (j.succAbove m)))
  rw [← Functor.map_comp_apply, ← op_comp, hc]

omit [HasProducts.{w} AddCommGrpCat.{t}] [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- Restricting a restricted local section further along a morphism into the iterated fibre
product is restricting the local section along the composite. -/
lemma map_sectionRestriction_comp (F : AbelianTorsor (G.over U))
    (s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i)))) {n : ℕ} (k : Fin (n + 1) → E.I₀)
    (m : Fin (n + 1)) {W : Over U} (g : W ⟶ (∏ᶜ fun j ↦ Over.mk (E.f (k j)))) :
    F.1.presheaf.map g.op (sectionRestriction E G F s k m) =
      F.1.presheaf.map (g ≫ Pi.π (fun j ↦ Over.mk (E.f (k j))) m).op (s (k m)) := by
  change F.1.presheaf.map g.op
      (F.1.presheaf.map (Pi.π (fun j ↦ Over.mk (E.f (k j))) m).op (s (k m))) = _
  rw [← Functor.map_comp_apply, ← op_comp]

omit [HasProducts.{w} AddCommGrpCat.{t}] [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- An equivariant morphism of torsors carries restricted local sections to restricted local
sections. -/
lemma sectionRestriction_hom {F F' : AbelianTorsor (G.over U)} (e : F.1.Hom F'.1)
    (s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i)))) {n : ℕ} (k : Fin (n + 1) → E.I₀)
    (m : Fin (n + 1)) :
    sectionRestriction E G F' (fun i ↦ e.hom.app _ (s i)) k m =
      e.hom.app _ (sectionRestriction E G F s k m) :=
  (NatTrans.naturality_apply e.hom _ _).symm

/-- The Čech `1`-cochain of differences of a family of local sections of a torsor: over the
fibre product indexed by `(i₀, i₁)` it is the section of `G` carrying the restriction of
`s_{i₀}` to the restriction of `s_{i₁}`. -/
def transitionCochain (F : AbelianTorsor (G.over U))
    (s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i)))) : cechCochain E G.obj 1 :=
  fun k ↦ torsorDifference (G.over U) F (op (∏ᶜ fun j ↦ Over.mk (E.f (k j))))
    (sectionRestriction E G F s k 1) (sectionRestriction E G F s k 0)

omit [HasProducts.{w} AddCommGrpCat.{t}] in
  omit [HasSheafify (J.over U) AddCommGrpCat.{t}] in
  omit [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
  /-- Restricting a difference of restricted local sections along a face projection is the
  difference of the corresponding restrictions along the bigger product. -/
  private lemma map_face_torsorDifference_sectionRestriction (F : AbelianTorsor (G.over U))
      (s s' : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i)))) {n : ℕ} (k : Fin (n + 2) → E.I₀)
      (j : Fin (n + 2)) (m m' : Fin (n + 1)) :
      G.obj.map (faceProjection E k j).left.op
          (torsorDifference (G.over U) F (op (∏ᶜ fun b ↦ Over.mk (E.f (k (j.succAbove b)))))
            (sectionRestriction E G F s (fun b ↦ k (j.succAbove b)) m)
            (sectionRestriction E G F s' (fun b ↦ k (j.succAbove b)) m')) =
        torsorDifference (G.over U) F (op (∏ᶜ fun c ↦ Over.mk (E.f (k c))))
          (sectionRestriction E G F s k (j.succAbove m))
          (sectionRestriction E G F s' k (j.succAbove m')) := by
    rw [← map_sectionRestriction E G F s k j m, ← map_sectionRestriction E G F s' k j m']
    exact torsorDifference_naturality (G.over U) F (faceProjection E k j).op _ _

omit [HasProducts.{w} AddCommGrpCat.{t}] [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- The restriction of the transition cochain along a face projection is the difference of the
two corresponding restricted local sections. -/
lemma map_face_transitionCochain (F : AbelianTorsor (G.over U))
    (s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i)))) (k : Fin 3 → E.I₀) (j : Fin 3) :
    G.obj.map (faceProjection E k j).left.op
        (transitionCochain E G F s (fun b ↦ k (j.succAbove b))) =
      torsorDifference (G.over U) F (op (∏ᶜ fun c ↦ Over.mk (E.f (k c))))
        (sectionRestriction E G F s k (j.succAbove 1))
        (sectionRestriction E G F s k (j.succAbove 0)) :=
  map_face_torsorDifference_sectionRestriction E G F s s k j 1 0

omit [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- **The transition cochain is a Čech `1`-cocycle.** Over a triple fibre product the three
restricted differences compose, which is exactly the Čech cocycle identity. -/
lemma transitionCochain_mem_cocycles1 (F : AbelianTorsor (G.over U))
    (s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i)))) :
    transitionCochain E G F s ∈ cocycles1 E G.obj := by
  rw [mem_cocycles1_iff']
  intro k
  rw [map_face_transitionCochain, map_face_transitionCochain, map_face_transitionCochain]
  exact (torsorDifference_trans (G.over U) F _ _ _ _).symm

/-- The Čech `1`-cocycle of differences of a family of local sections of a torsor. -/
@[ega "IV 16.5.15" "special case", sga "4½ Cycle 1.1.2" "more general"]
def transitionCocycle (F : AbelianTorsor (G.over U))
    (s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i)))) : cocycles1 E G.obj :=
  ⟨transitionCochain E G F s, transitionCochain_mem_cocycles1 E G F s⟩

/-- The Čech `0`-cochain of differences of two families of local sections of a torsor. -/
def sectionDifferenceCochain (F : AbelianTorsor (G.over U))
    (s s' : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i)))) : cechCochain E G.obj 0 :=
  fun l ↦ torsorDifference (G.over U) F (op (∏ᶜ fun j ↦ Over.mk (E.f (l j))))
    (sectionRestriction E G F s l 0) (sectionRestriction E G F s' l 0)

omit [HasProducts.{w} AddCommGrpCat.{t}] [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- The restriction of the cochain of section differences along a face projection. -/
lemma map_face_sectionDifferenceCochain (F : AbelianTorsor (G.over U))
    (s s' : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i)))) (k : Fin 2 → E.I₀) (j : Fin 2) :
    G.obj.map (faceProjection E k j).left.op
        (sectionDifferenceCochain E G F s s' (fun b ↦ k (j.succAbove b))) =
      torsorDifference (G.over U) F (op (∏ᶜ fun c ↦ Over.mk (E.f (k c))))
        (sectionRestriction E G F s k (j.succAbove 0))
        (sectionRestriction E G F s' k (j.succAbove 0)) :=
  map_face_torsorDifference_sectionRestriction E G F s s' k j 0 0

omit [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- **Two families of local sections have cohomologous transition cocycles.** Their transition
cochains differ by the Čech coboundary of their cochain of differences. -/
@[ega "IV 16.5.15" "special case"]
lemma cechDifferential_sectionDifferenceCochain (F : AbelianTorsor (G.over U))
    (s s' : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i)))) :
    cechDifferential E G.obj 0 (sectionDifferenceCochain E G F s s') =
      transitionCochain E G F s - transitionCochain E G F s' := by
  funext k
  rw [cechDifferential_zero_apply, map_face_sectionDifferenceCochain,
    map_face_sectionDifferenceCochain]
  exact torsorDifference_sub_comm (G.over U) F (op (∏ᶜ fun c ↦ Over.mk (E.f (k c))))
    (sectionRestriction E G F s k 1) (sectionRestriction E G F s' k 1)
    (sectionRestriction E G F s k 0) (sectionRestriction E G F s' k 0)

omit [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- **The Čech class of the transition cocycle does not depend on the chosen local sections.** -/
@[stacks 0A6G "variant: independence of the chosen local sections; \
the tag is Stacks.CechSite.cechH1ToSliceH_injective_and_range_eq", ega "IV 16.5.15" "special case"]
lemma cls_transitionCocycle_congr (F : AbelianTorsor (G.over U))
    (s s' : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i)))) :
    cls E G.obj (transitionCocycle E G F s) = cls E G.obj (transitionCocycle E G F s') :=
  QuotientAddGroup.eq_iff_sub_mem.mpr ((mem_coboundaries1_iff E G.obj _).mpr
    ⟨sectionDifferenceCochain E G F s s', cechDifferential_sectionDifferenceCochain E G F s s'⟩)

omit [HasProducts.{w} AddCommGrpCat.{t}] [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- The transition cochain is carried along an equivariant morphism of torsors. -/
lemma transitionCochain_hom {F F' : AbelianTorsor (G.over U)} (e : F.1.Hom F'.1)
    (s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i)))) :
    transitionCochain E G F' (fun i ↦ e.hom.app _ (s i)) = transitionCochain E G F s := by
  funext k
  change torsorDifference (G.over U) F' _
      (sectionRestriction E G F' (fun i ↦ e.hom.app _ (s i)) k 1)
      (sectionRestriction E G F' (fun i ↦ e.hom.app _ (s i)) k 0) = _
  rw [sectionRestriction_hom, sectionRestriction_hom]
  exact torsorDifference_hom (G.over U) e _ _ _

omit [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- **The Čech class of the transition cocycle depends only on the isomorphism class of the
torsor.** -/
@[stacks 0A6G "variant: independence of the torsor inside its isomorphism class; \
the tag is Stacks.CechSite.cechH1ToSliceH_injective_and_range_eq", ega "IV 16.5.15" "partial"]
lemma cls_transitionCocycle_eq_of_isIsomorphic {F F' : AbelianTorsor (G.over U)}
    (hFF' : AbelianTorsor.IsIsomorphic F F')
    (s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i))))
    (s' : ∀ i, F'.1.presheaf.obj (op (Over.mk (E.f i)))) :
    cls E G.obj (transitionCocycle E G F s) = cls E G.obj (transitionCocycle E G F' s') := by
  obtain ⟨e, -⟩ := hFF'
  exact (congrArg (cls E G.obj) (Subtype.ext (transitionCochain_hom E G e s).symm)).trans
    (cls_transitionCocycle_congr E G F' _ s')

end Transition

/-! ### Local triviality and the Čech class of a torsor -/

section LocalTriviality

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
  (E : PreZeroHypercover.{w} U) (G : Sheaf J AddCommGrpCat.{t})
  [HasProducts.{w} AddCommGrpCat.{t}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})]

/-- A torsor under `G|_U` is *trivial on the members of* `𝒰` when its restriction to the
localization of `(C/U, J.over U)` at each member `U_i → U` of the family is a trivial torsor. -/
def IsTrivialOnMembers (F : AbelianTorsor (G.over U)) : Prop :=
  ∀ i, (F.1.over (Over.mk (E.f i))).IsTrivial

omit [HasProducts.{w} AddCommGrpCat.{t}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- **The torsors which restrict to trivial torsors over each member of the covering.** A torsor
under `G|_U` restricts to a trivial torsor over every member of the family exactly when it has a
section over every member. -/
@[stacks 0A6G "variant: torsors trivial over each member have sections there; \
the tag is Stacks.CechSite.cechH1ToSliceH_injective_and_range_eq", sga "3 IV 5.1.5" "(ii)"]
theorem isTrivialOnMembers_iff (F : AbelianTorsor (G.over U)) :
    IsTrivialOnMembers E G F ↔
      ∀ i, Nonempty (F.1.presheaf.obj (op (Over.mk (E.f i)))) :=
  forall_congr' fun i ↦ PseudoTorsor.isTrivial_over_iff F.1 (Over.mk (E.f i))

/-- An isomorphism class of torsors under `G|_U` is *locally trivial on* `𝒰` when it has a
representative with a section over every member of the family, equivalently (by
`Stacks.Cohomology.Torsors.isTrivialOnMembers_iff`) a representative restricting to a trivial
torsor over every member. -/
def IsLocallyTrivialOn (c : torsorIsoClasses (G.over U)) : Prop :=
  ∃ F : AbelianTorsor (G.over U), Quotient.mk (torsorSetoid (G.over U)) F = c ∧
    ∀ i, Nonempty (F.1.presheaf.obj (op (Over.mk (E.f i))))

/-- The isomorphism classes of torsors under `G|_U` which are locally trivial on `𝒰`. -/
def LocallyTrivialClass : Type _ :=
  {c : torsorIsoClasses (G.over U) // IsLocallyTrivialOn E G c}

/-- **The Čech class of a locally trivial isomorphism class of torsors**: the class of the
transition cocycle of any family of local sections of any representative with sections over all
members of the family. -/
@[sga "4½ Cycle 1.1.2" "more general"]
def cechClass (c : LocallyTrivialClass E G) : cechH1 E G.obj :=
  cls E G.obj (transitionCocycle E G (Classical.choose c.2)
    (fun i ↦ Classical.choice ((Classical.choose_spec c.2).2 i)))

omit [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- The Čech class of a locally trivial class is computed by any representative and any family
of local sections of it. -/
@[sga "4½ Cycle 1.1.2" "partial"]
lemma cechClass_mk (F : AbelianTorsor (G.over U))
    (hF : ∀ i, Nonempty (F.1.presheaf.obj (op (Over.mk (E.f i)))))
    (s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i)))) :
    cechClass E G ⟨Quotient.mk (torsorSetoid (G.over U)) F, ⟨F, rfl, hF⟩⟩ =
      cls E G.obj (transitionCocycle E G F s) := by
  refine cls_transitionCocycle_eq_of_isIsomorphic E G ?_ _ s
  exact Quotient.exact (Classical.choose_spec
    (⟨F, rfl, hF⟩ : IsLocallyTrivialOn E G (Quotient.mk (torsorSetoid (G.over U)) F))).1

omit [HasProducts.{w} AddCommGrpCat.{t}] [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- A compatible family of sections over all objects of `C/U` has vanishing transition
cochain: its restrictions to a fibre product along the two projections agree. -/
lemma transitionCochain_eq_zero_of_sectionFamily (F : AbelianTorsor (G.over U))
    (σ : ∀ W : (Over U)ᵒᵖ, F.1.presheaf.obj W)
    (hσ : ∀ {W W' : (Over U)ᵒᵖ} (f : W ⟶ W'), F.1.presheaf.map f (σ W) = σ W') :
    transitionCochain E G F (fun i ↦ σ (op (Over.mk (E.f i)))) = 0 := by
  funext k
  have heq : sectionRestriction E G F (fun i ↦ σ (op (Over.mk (E.f i)))) k 1 =
      sectionRestriction E G F (fun i ↦ σ (op (Over.mk (E.f i)))) k 0 := by
    change F.1.presheaf.map _ (σ (op (Over.mk (E.f (k 1))))) =
      F.1.presheaf.map _ (σ (op (Over.mk (E.f (k 0)))))
    rw [hσ, hσ]
  change torsorDifference (G.over U) F _ _ _ = 0
  rw [heq]
  exact torsorDifference_self (G.over U) F _ _

omit [HasProducts.{w} AddCommGrpCat.{t}] [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
  /-- A trivial torsor has a family of local sections with vanishing transition cochain. -/
  private lemma exists_transitionCochain_eq_zero_of_isTrivial (F : AbelianTorsor (G.over U))
      (hF : F.1.IsTrivial) :
      ∃ s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i))), transitionCochain E G F s = 0 := by
    obtain ⟨σ, hσ⟩ := (Stacks.Cohomology.Torsors.nonempty_globalSections_iff_sectionFamily
      F.1.presheaf).1 (nonempty_globalSections_of_isTrivial F.1 hF)
    exact ⟨fun i ↦ σ (op (Over.mk (E.f i))),
      transitionCochain_eq_zero_of_sectionFamily E G F σ hσ⟩

omit [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- **A trivial torsor has vanishing Čech class.** A global section restricts to a family of
local sections all of whose differences vanish. -/
@[stacks 0A6G "variant: the trivial torsor has vanishing Čech class; \
the tag is Stacks.CechSite.cechH1ToSliceH_injective_and_range_eq", ega "IV 16.5.15" "partial"]
theorem cechClass_eq_zero_of_isTrivial (F : AbelianTorsor (G.over U))
    (hF : F.1.IsTrivial)
    (hs : ∀ i, Nonempty (F.1.presheaf.obj (op (Over.mk (E.f i))))) :
    cechClass E G ⟨Quotient.mk (torsorSetoid (G.over U)) F, ⟨F, rfl, hs⟩⟩ = 0 := by
  obtain ⟨s, hs0⟩ := exists_transitionCochain_eq_zero_of_isTrivial E G F hF
  rw [cechClass_mk E G F hs s, cls_eq_zero_iff]
  exact ⟨0, by rw [map_zero]; exact hs0.symm⟩

end LocalTriviality

/-! ### Gluing the local sections of a torsor with vanishing transition cochain -/

section Gluing

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
  (E : PreZeroHypercover.{w} U) (G : Sheaf J AddCommGrpCat.{t})
  [HasProducts.{w} AddCommGrpCat.{t}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})]

omit [HasProducts.{w} AddCommGrpCat.{t}] [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- **The local sections agree on every common refinement.** If the transition cochain of a
family of local sections vanishes then, for any object `W` of `C/U` and any two morphisms from
`W` to members of the family, the two restrictions of the corresponding local sections agree:
the pair of morphisms factors through the fibre product of the two members, where the vanishing
of the transition cochain says exactly that. -/
lemma map_eq_of_transitionCochain_eq_zero (F : AbelianTorsor (G.over U))
    (s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i))))
    (hs : transitionCochain E G F s = 0) {W : Over U} (k : Fin 2 → E.I₀)
    (a : W ⟶ Over.mk (E.f (k 0))) (b : W ⟶ Over.mk (E.f (k 1))) :
    F.1.presheaf.map a.op (s (k 0)) = F.1.presheaf.map b.op (s (k 1)) := by
  let u : W ⟶ (∏ᶜ fun m ↦ Over.mk (E.f (k m))) :=
    Pi.lift (fun m ↦ match m with | 0 => a | 1 => b)
  have h0 : u ≫ Pi.π (fun m ↦ Over.mk (E.f (k m))) 0 = a := Pi.lift_comp_π _ _
  have h1 : u ≫ Pi.π (fun m ↦ Over.mk (E.f (k m))) 1 = b := Pi.lift_comp_π _ _
  have heq : sectionRestriction E G F s k 1 = sectionRestriction E G F s k 0 :=
    eq_of_torsorDifference_eq_zero (G.over U) F _ _ _ (congrFun hs k)
  have e0 := map_sectionRestriction_comp E G F s k 0 u
  have e1 := map_sectionRestriction_comp E G F s k 1 u
  rw [h0] at e0
  rw [h1] at e1
  rw [← e0, ← heq, e1]

omit [HasProducts.{w} AddCommGrpCat.{t}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- **A refinement of a member of the covering.** Every arrow of the sieve generated by the
family, viewed in `C/U` over the terminal object, factors through some member of the family. -/
lemma exists_hom_over_member {W : Over U} (f : W ⟶ Over.mk (𝟙 U))
    (hf : E.sieve₀.arrows f.left) : ∃ i : E.I₀, Nonempty (W ⟶ Over.mk (E.f i)) := by
  obtain ⟨Y, hh, g, hg, hcomp⟩ := hf
  obtain ⟨i⟩ := hg
  refine ⟨i, ⟨Over.homMk hh ?_⟩⟩
  change hh ≫ E.f i = W.hom
  rw [hcomp]
  simpa using Over.w f

omit [HasProducts.{w} AddCommGrpCat.{t}] [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- **The glued value over a refinement.** For a family of local sections with vanishing
transition cochain, an arrow of the covering sieve carries a section of the torsor which is the
restriction of the local section along *any* morphism to *any* member of the family. -/
lemma exists_glueValue (F : AbelianTorsor (G.over U))
    (s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i))))
    (hs : transitionCochain E G F s = 0) {W : Over U} (f : W ⟶ Over.mk (𝟙 U))
    (hf : E.sieve₀.arrows f.left) :
    ∃ x : F.1.presheaf.obj (op W),
      ∀ (i : E.I₀) (g : W ⟶ Over.mk (E.f i)), F.1.presheaf.map g.op (s i) = x := by
  obtain ⟨i, ⟨a⟩⟩ := exists_hom_over_member E f hf
  exact ⟨F.1.presheaf.map a.op (s i),
    fun j b ↦ map_eq_of_transitionCochain_eq_zero E G F s hs ![j, i] b a⟩

omit [HasProducts.{w} AddCommGrpCat.{t}] [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- **A vanishing transition cochain makes the torsor trivial.** The local sections then agree
on every common refinement of two members of the covering, so the sheaf condition for the
covering sieve glues them to a section over the terminal object of `C/U`, and a torsor with such
a section is trivial by Stacks 03AI. -/
@[stacks 0A6G "variant: a torsor whose transition cocycle vanishes is trivial; \
the tag is Stacks.CechSite.cechH1ToSliceH_injective_and_range_eq"]
theorem isTrivial_of_transitionCochain_eq_zero (hE : E.sieve₀ ∈ J U)
    (F : AbelianTorsor (G.over U))
    (s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i))))
    (hs : transitionCochain E G F s = 0) : F.1.IsTrivial := by
  classical
  let S : Sieve (Over.mk (𝟙 U)) := (Sieve.overEquiv (Over.mk (𝟙 U))).symm E.sieve₀
  have hmem : ∀ {W : Over U} {f : W ⟶ Over.mk (𝟙 U)}, S.arrows f → E.sieve₀.arrows f.left :=
    fun hf ↦ hf
  let fam : Presieve.FamilyOfElements F.1.presheaf S.arrows :=
    fun _ f hf ↦ Classical.choose (exists_glueValue E G F s hs f (hmem hf))
  have hfam : ∀ {W : Over U} (f : W ⟶ Over.mk (𝟙 U)) (hf : S.arrows f) (i : E.I₀)
      (g : W ⟶ Over.mk (E.f i)), F.1.presheaf.map g.op (s i) = fam f hf :=
    fun f hf ↦ Classical.choose_spec (exists_glueValue E G F s hs f (hmem hf))
  have hcompat : fam.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ _
    obtain ⟨i₁, ⟨a₁⟩⟩ := exists_hom_over_member E f₁ (hmem h₁)
    obtain ⟨i₂, ⟨a₂⟩⟩ := exists_hom_over_member E f₂ (hmem h₂)
    rw [← hfam f₁ h₁ i₁ a₁, ← hfam f₂ h₂ i₂ a₂, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, ← op_comp, ← op_comp]
    exact map_eq_of_transitionCochain_eq_zero E G F s hs ![i₁, i₂] (g₁ ≫ a₁) (g₂ ≫ a₂)
  obtain ⟨x, -, -⟩ := (isSheaf_iff_isSheaf_of_type (J.over U) F.1.presheaf).1 F.1.isSheaf S
    (J.overEquiv_symm_mem_over (Over.mk (𝟙 U)) E.sieve₀ hE) fam hcompat
  exact PseudoTorsor.isTrivial_of_terminal_section Over.mkIdTerminal F.1 x

omit [HasProducts.{w} AddCommGrpCat.{t}] [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- **Triviality in terms of the transition cocycle.** For a covering family, a torsor under
`G|_U` with a section over every member of the family is trivial exactly when some family of
local sections has vanishing transition cochain, that is, exactly when the local sections can be
chosen to agree on all the fibre products. -/
@[stacks 0A6G "variant: triviality in terms of the transition cocycle; \
the tag is Stacks.CechSite.cechH1ToSliceH_injective_and_range_eq"]
theorem isTrivial_iff_exists_transitionCochain_eq_zero (hE : E.sieve₀ ∈ J U)
    (F : AbelianTorsor (G.over U)) :
    F.1.IsTrivial ↔
      ∃ s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i))), transitionCochain E G F s = 0 := by
  exact ⟨exists_transitionCochain_eq_zero_of_isTrivial E G F,
    fun ⟨s, hs⟩ ↦ isTrivial_of_transitionCochain_eq_zero E G hE F s hs⟩

end Gluing

end Stacks.Cohomology.Torsors

end
