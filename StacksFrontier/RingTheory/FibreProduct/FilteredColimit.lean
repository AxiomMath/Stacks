module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.RingTheory.LocalRing.Pullback

/-!
# Filtered colimits commute with fibre products of rings

Let `s : B ⟶ R` be a map of commutative rings and let `R` be the colimit of a filtered diagram
`F` of rings.  Forming the fibre product with `B` over `R` at each stage gives a new filtered
diagram, and its colimit is `B` itself.

This is the step in Noetherian approximation (Stacks Tag 07RN) which produces the inverse
system of affine models: there `B = Γ(U, 𝒪_U)` for an affine open `U`, `R = Γ(W, 𝒪_W)` for
`W = U ∩ V` with `V` the quasi-compact open being approximated, and `R = colim Γ(W_i, 𝒪_{W_i})`
along the approximating system.  The rings `B_i = B ×_R Γ(W_i, 𝒪_{W_i})` then have colimit `B`,
which is what makes the glued finite stages have the ambient scheme as their inverse limit.

## Main definitions

* `RingFibreProduct.pullbackObj` is the fibre product `B ×_R R_j`, as a subring of `B × R_j`.
  It is `RingHom.pullback` of `s` and the `j`-th leg of the colimit cocone.
* `RingFibreProduct.pullbackDiagram` assembles those fibre products into a diagram of the same
  shape as the given one, the transition map `B_j → B_{j'}` being `(b, r) ↦ (b, R_j → R_{j'} r)`.
* `RingFibreProduct.pullbackCocone` is the cocone on that diagram with point `B` whose legs are
  the first projections `B_j → B`.

## Main results

* `RingFibreProduct.isColimitPullbackCocone`: for a filtered index category,
  `RingFibreProduct.pullbackCocone` is a colimit cocone, i.e. `B = colim_j (B ×_R R_j)`.
* `RingFibreProduct.nonempty_isColimit_of_jointly_injective`: the element-level form for a
  fibre product supplied by the consumer.  A cocone whose legs are the first projections of a
  compatible family of fibre products is colimiting as soon as each stage is jointly injective
  over `B` and `F.obj i`, and hits every compatible pair.
* `RingFibreProduct.nonempty_isColimit_of_isPullback`: the same statement with the stagewise
  fibre product recorded by `CategoryTheory.IsPullback` instead.

Three lemmas pin down the explicit construction, so that the colimit statement says what it is
meant to: `RingFibreProduct.pullbackVal_map` identifies the transition maps of the diagram,
`RingFibreProduct.pullbackCocone_pt` its point, and
`RingFibreProduct.pullbackCocone_ι_app_apply` its legs.

## Implementation notes

The explicit colimit is established by showing that the canonical comparison map out of
`CategoryTheory.Limits.colimit` is bijective.  Surjectivity is joint surjectivity of the legs of
the given colimit cocone, applied to `s b`; injectivity uses that two elements of a filtered
colimit of rings agree only if they already agree at some later stage.  Both directions need the
colimit to be filtered, and indeed the statement fails for a general colimit.

Elements of the objects of the diagram are handled through `RingFibreProduct.pullbackVal`, which
exposes the underlying pair: the carrier of `(pullbackDiagram s).obj j` is only definitionally,
not syntactically, the subring `pullbackObj s j`, and a bare `Subtype.val` on it does not
elaborate.

The two `nonempty_isColimit_*` forms do not construct the fibre product: they take the stagewise
fibre products as given, either by their universal property (`CategoryTheory.IsPullback`) or by
the two element-level properties that characterise a subring of a product.  A consumer holding
Mathlib's concrete `RingHom.pullback` discharges the element-level hypotheses directly, and a
consumer holding a cartesian square in `CommRingCat` uses the second form.

Both are proved by recognising the colimit on underlying types, where the forgetful functor
reflects filtered colimits.  The element-level description of a cartesian square of types is
extracted by testing against `PUnit`, which is terminal there.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace RingFibreProduct

section TypePullback

variable {P X Y Z : Type u} {f : P ⟶ X} {g : P ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

/-- The legs of a cartesian square of types are jointly injective. -/
private lemma eq_of_isPullback (H : IsPullback f g h i) {x y : P}
    (hx : f x = f y) (hy : g x = g y) : x = y := by
  have key : (↾fun _ : PUnit.{u + 1} ↦ x) = (↾fun _ : PUnit.{u + 1} ↦ y) := by
    refine H.hom_ext ?_ ?_
    · ext _
      simpa using hx
    · ext _
      simpa using hy
  simpa using ConcreteCategory.congr_hom key PUnit.unit

/-- Every compatible pair of elements comes from the corner of a cartesian square of types. -/
private lemma exists_of_isPullback (H : IsPullback f g h i) (x : X) (y : Y)
    (hxy : h x = i y) : ∃ p : P, f p = x ∧ g p = y := by
  refine ⟨H.lift (↾fun _ : PUnit.{u + 1} ↦ x) (↾fun _ : PUnit.{u + 1} ↦ y) ?_ PUnit.unit, ?_, ?_⟩
  · ext _
    simpa using hxy
  · exact ConcreteCategory.congr_hom (H.lift_fst _ _ _) PUnit.unit
  · exact ConcreteCategory.congr_hom (H.lift_snd _ _ _) PUnit.unit

end TypePullback

section ExplicitFibreProduct

variable {J : Type u} [SmallCategory J] {F : J ⥤ CommRingCat.{u}} {c : Cocone F}
  {B : CommRingCat.{u}} (s : B ⟶ c.pt)

/-- The fibre product `B ×_R R_j`, where `R = c.pt` is the point of the cocone `c` and
`R_j = F.obj j`, as a subring of `B × R_j`. -/
abbrev pullbackObj (j : J) : Subring (B × F.obj j) := RingHom.pullback s.hom (c.ι.app j).hom

/-- Membership in `RingFibreProduct.pullbackObj` is the expected compatibility condition. -/
theorem mem_pullbackObj {j : J} {x : B × F.obj j} :
    x ∈ pullbackObj s j ↔ s x.1 = c.ι.app j x.2 := Iff.rfl

/-- The legs of a cocone are compatible with the transition maps, elementwise. -/
private lemma app_map_apply {j j' : J} (f : j ⟶ j') (r : F.obj j) :
    c.ι.app j' (F.map f r) = c.ι.app j r := by
  rw [← ConcreteCategory.comp_apply, c.w f]

/-- Pushing the second coordinate forward along a transition map of the given diagram stays in
the fibre product. -/
theorem map_mem_pullbackObj {j j' : J} (f : j ⟶ j') (x : pullbackObj s j) :
    ((x : B × F.obj j).1, F.map f (x : B × F.obj j).2) ∈ pullbackObj s j' := by
  rw [mem_pullbackObj]
  exact x.2.trans (app_map_apply f _).symm

/-- The transition map `B ×_R R_j → B ×_R R_{j'}` induced by a transition map `R_j → R_{j'}` of
the given diagram. -/
def pullbackObjMap {j j' : J} (f : j ⟶ j') :
    CommRingCat.of (pullbackObj s j) ⟶ CommRingCat.of (pullbackObj s j') :=
  CommRingCat.ofHom
    ((((RingHom.id B).prodMap (F.map f).hom).comp (pullbackObj s j).subtype).codRestrict
      (pullbackObj s j') (map_mem_pullbackObj s f))

/-- The diagram `j ↦ B ×_R R_j` of fibre products, of the same shape as the given diagram. -/
def pullbackDiagram : J ⥤ CommRingCat.{u} where
  obj j := CommRingCat.of (pullbackObj s j)
  map f := pullbackObjMap s f
  map_id j := by
    ext x
    · rfl
    · exact ConcreteCategory.congr_hom (F.map_id j) _
  map_comp f g := by
    ext x
    · rfl
    · exact ConcreteCategory.congr_hom (F.map_comp f g) _

/-- The pair in `B × R_j` underlying an element of `(pullbackDiagram s).obj j`. -/
def pullbackVal {j : J} (x : ToType ((pullbackDiagram s).obj j)) : B × F.obj j :=
  Subtype.val (α := B × F.obj j) x

/-- An element of `(pullbackDiagram s).obj j` is determined by its underlying pair. -/
theorem pullbackVal_injective {j : J} : Function.Injective (pullbackVal s (j := j)) :=
  fun _ _ h => Subtype.ext (p := (· ∈ pullbackObj s j)) h

/-- The two coordinates of an element of `(pullbackDiagram s).obj j` agree in `R`. -/
theorem apply_pullbackVal_fst {j : J} (x : ToType ((pullbackDiagram s).obj j)) :
    s (pullbackVal s x).1 = c.ι.app j (pullbackVal s x).2 :=
  Subtype.property (p := (· ∈ pullbackObj s j)) x

/-- The transition maps of `RingFibreProduct.pullbackDiagram` are the identity on the first
coordinate and the given transition map on the second. -/
@[simp] theorem pullbackVal_map {j j' : J} (f : j ⟶ j') (x : ToType ((pullbackDiagram s).obj j)) :
    pullbackVal s ((pullbackDiagram s).map f x) =
      ((pullbackVal s x).1, F.map f (pullbackVal s x).2) := rfl

/-- The cocone on `RingFibreProduct.pullbackDiagram` with point `B` whose legs are the first
projections `B ×_R R_j → B`. -/
def pullbackCocone : Cocone (pullbackDiagram s) where
  pt := B
  ι :=
  { app := fun j => CommRingCat.ofHom (s.hom.pullbackFst (c.ι.app j).hom)
    naturality := fun j j' f => by ext x; rfl }

/-- The point of `RingFibreProduct.pullbackCocone` is `B`. -/
@[simp] theorem pullbackCocone_pt : (pullbackCocone s).pt = B := rfl

/-- The legs of `RingFibreProduct.pullbackCocone` are the first projections. -/
@[simp] theorem pullbackCocone_ι_app_apply (j : J) (x : ToType ((pullbackDiagram s).obj j)) :
    (pullbackCocone s).ι.app j x = (pullbackVal s x).1 := rfl

variable [IsFiltered J]

/-- **Fibre products commute with filtered colimits of rings.** If `R = colim_j R_j` is a
filtered colimit of commutative rings and `s : B → R` is a ring map, then the first projections
`B ×_R R_j → B` exhibit `B` as `colim_j (B ×_R R_j)`.

This is the ring-theoretic ingredient of Stacks Tag 07RN. -/
noncomputable def isColimitPullbackCocone (hc : IsColimit c) : IsColimit (pullbackCocone s) := by
  have key : ∀ (m : J) (y : ToType ((pullbackDiagram s).obj m)),
      (colimit.isColimit (pullbackDiagram s)).desc (pullbackCocone s)
        (colimit.ι (pullbackDiagram s) m y) = (pullbackVal s y).1 := fun m y => by
    rw [← ConcreteCategory.comp_apply]
    exact ConcreteCategory.congr_hom
      ((colimit.isColimit (pullbackDiagram s)).fac (pullbackCocone s) m) y
  have hiso : IsIso ((colimit.isColimit (pullbackDiagram s)).desc (pullbackCocone s)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun z z' hzz' ↦ ?_, fun b ↦ ?_⟩
    · obtain ⟨j, x, rfl⟩ := Concrete.colimit_exists_rep (pullbackDiagram s) z
      obtain ⟨j', x', rfl⟩ := Concrete.colimit_exists_rep (pullbackDiagram s) z'
      rw [key j x, key j' x'] at hzz'
      set k := IsFiltered.max j j'
      set f : j ⟶ k := IsFiltered.leftToMax j j'
      set g : j' ⟶ k := IsFiltered.rightToMax j j'
      have hu : c.ι.app k (F.map f (pullbackVal s x).2) = s (pullbackVal s x).1 := by
        rw [← ConcreteCategory.comp_apply, c.w f]
        exact (apply_pullbackVal_fst s x).symm
      have hv : c.ι.app k (F.map g (pullbackVal s x').2) = s (pullbackVal s x).1 := by
        rw [← ConcreteCategory.comp_apply, c.w g, hzz']
        exact (apply_pullbackVal_fst s x').symm
      obtain ⟨k', h, hh⟩ := (IsColimit.eq_iff' hc _ _).mp (hu.trans hv.symm)
      refine Concrete.colimit_rep_eq_of_exists (pullbackDiagram s) x x' ⟨k', f ≫ h, g ≫ h, ?_⟩
      refine pullbackVal_injective s (Prod.ext hzz' ?_)
      simpa using hh
    · obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep F hc (s b)
      exact ⟨colimit.ι (pullbackDiagram s) j ⟨(b, y), hy.symm⟩, key j ⟨(b, y), hy.symm⟩⟩
  exact IsColimit.ofPointIso (colimit.isColimit (pullbackDiagram s))

end ExplicitFibreProduct

variable {K : Type u} [Category.{u} K] [IsFiltered K] {F G : K ⥤ CommRingCat.{u}}
  {c : Cocone F} {B : CommRingCat.{u}} (s : B ⟶ c.pt)
  (π₁ : G ⟶ (Functor.const K).obj B) (π₂ : G ⟶ F)

/-- **Filtered colimits commute with fibre products of rings**, element-level form.

Let `R` be the colimit of a filtered diagram `F` of rings and let `s : B ⟶ R`.  Suppose given a
diagram `G` with natural transformations `π₁ : G ⟶ B` and `π₂ : G ⟶ F` exhibiting each `G.obj i`
as the fibre product `B ×_R F.obj i`: the square commutes, `π₁` and `π₂` are jointly injective,
and together they hit every compatible pair.  Then `π₁` exhibits `B` as the colimit of `G`. -/
theorem nonempty_isColimit_of_jointly_injective (hc : IsColimit c)
    (hcomm : ∀ i : K, π₁.app i ≫ s = π₂.app i ≫ c.ι.app i)
    (hinj : ∀ (i : K) (x y : G.obj i), π₁.app i x = π₁.app i y → π₂.app i x = π₂.app i y → x = y)
    (hsurj : ∀ (i : K) (b : B) (r : F.obj i), s b = c.ι.app i r →
      ∃ x : G.obj i, π₁.app i x = b ∧ π₂.app i x = r) :
    Nonempty (IsColimit (Cocone.mk B π₁)) := by
  have hcT : IsColimit ((forget CommRingCat.{u}).mapCocone c) := isColimitOfPreserves _ hc
  have : ReflectsFilteredColimits (forget CommRingCat.{u}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  have hcomm' : ∀ (i : K) (z : G.obj i), s (π₁.app i z) = c.ι.app i (π₂.app i z) := fun i z ↦ by
    simpa using ConcreteCategory.congr_hom (hcomm i) z
  refine ReflectsColimit.reflects (F := forget CommRingCat.{u})
    (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · intro b
    obtain ⟨i, r, hr⟩ := Types.jointly_surjective_of_isColimit hcT (s b)
    obtain ⟨x, hx, -⟩ := hsurj i b r hr.symm
    exact ⟨i, x, hx.symm⟩
  · intro i x y hxy
    have hπ₁ : π₁.app i x = π₁.app i y := hxy
    have h₂ : c.ι.app i (π₂.app i x) = c.ι.app i (π₂.app i y) := by
      rw [← hcomm', ← hcomm', hπ₁]
    obtain ⟨j, φ, hφ⟩ := (Types.FilteredColimit.isColimit_eq_iff' hcT _ _).mp h₂
    have n₁ : ∀ z : G.obj i, π₁.app j (G.map φ z) = π₁.app i z := fun z ↦ by simp
    have n₂ : ∀ z : G.obj i, π₂.app j (G.map φ z) = F.map φ (π₂.app i z) := fun z ↦ by simp
    refine ⟨j, φ, hinj j _ _ ?_ ?_⟩
    · change π₁.app j (G.map φ x) = π₁.app j (G.map φ y)
      rw [n₁, n₁, hπ₁]
    · change π₂.app j (G.map φ x) = π₂.app j (G.map φ y)
      rw [n₂, n₂]
      exact hφ

/-- **Filtered colimits commute with fibre products of rings**, cartesian-square form.

Let `R` be the colimit of a filtered diagram `F` of rings, let `s : B ⟶ R`, and suppose given a
diagram `G` whose stages sit in cartesian squares exhibiting them as `B ×_R F.obj i`.  Then the
first projections exhibit `B` as the colimit of `G`. -/
theorem nonempty_isColimit_of_isPullback (hc : IsColimit c)
    (hsq : ∀ i : K, IsPullback (π₁.app i) (π₂.app i) s (c.ι.app i)) :
    Nonempty (IsColimit (Cocone.mk B π₁)) :=
  nonempty_isColimit_of_jointly_injective s π₁ π₂ hc (fun i ↦ (hsq i).w)
    (fun i _ _ hx hy ↦ eq_of_isPullback ((hsq i).map (forget CommRingCat.{u})) hx hy)
    (fun i b r hbr ↦ exists_of_isPullback ((hsq i).map (forget CommRingCat.{u})) b r hbr)

end RingFibreProduct

end
