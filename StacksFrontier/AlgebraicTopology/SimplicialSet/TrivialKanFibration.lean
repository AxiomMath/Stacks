module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Quotient

/-!
# Trivial Kan fibrations

Trivial Kan fibrations of simplicial sets: the definition, lifting properties, products, filtered
colimits, inverse limits of towers, and the fact that trivial Kan fibrations are homotopy
equivalences.
-/

/-!
## Trivial Kan fibrations

A morphism `f : X ⟶ Y` of simplicial sets is a *trivial Kan fibration* if `X₀ → Y₀` is surjective
and, for every `n ≥ 1`, every commutative square

```
∂Δ[n] ⟶ X
  |      |
  v      v
Δ[n]  ⟶ Y
```

admits a diagonal filler `Δ[n] ⟶ X`. The two clauses together say that `f` has the right lifting
property with respect to every boundary inclusion `∂Δ[n].ι : ∂Δ[n] ⟶ Δ[n]`, and that is how the
class is defined here.

### Main definitions

* `SSet.trivialKanFibrations`: the class of trivial Kan fibrations, namely the right lifting class
  `SSet.modelCategoryQuillen.I.rlp` of the family of boundary inclusions.

### Implementation notes

The source's first clause is the case `n = 0` of its second one, read through the lifting property:
`∂Δ[0] = ⊥` (`SSet.boundary_zero`) is initial (`SSet.Subcomplex.isInitialBot`), so a square over
`∂Δ[0].ι` is a `0`-simplex of `Y` and a filler is a `0`-simplex of `X` above it
(`SSet.yonedaEquiv` identifying `Δ[0] ⟶ X` with `X₀`); for `n ≥ 1` the lifting property is the
filler condition verbatim.

The boundary inclusions are Mathlib's generating cofibrations
`SSet.modelCategoryQuillen.I = .ofHoms (fun n ↦ ∂Δ[n].ι)` for the Quillen model structure, with
`∂Δ[n]` the subcomplex `SSet.boundary n` of `Δ[n]`. Taking the class to be an `rlp` rather than an
unfolded conjunction makes stability under composition [Stacks, Tag 08NP] and under base change
[Stacks, Tag 08NN] instances of the general theory of lifting classes, derived here, and makes
the lifting property against all monomorphisms [Stacks, Tag 08NM] a comparison of two lifting
classes, `I.rlp = (monomorphisms SSet).rlp`.

### References

* [Stacks, Tag 08NL](https://stacks.math.columbia.edu/tag/08NL)
-/

section

open CategoryTheory MorphismProperty Simplicial

universe u

namespace SSet

/-- **Stacks 08NL**.
The class of *trivial Kan fibrations*: the morphisms `f : X ⟶ Y` of simplicial sets having the
right lifting property with respect to every boundary inclusion `∂Δ[n].ι : ∂Δ[n] ⟶ Δ[n]`, that
is, such that `X₀ → Y₀` is surjective and, for `n ≥ 1`, every commutative square with
`∂Δ[n] ⟶ X` on top and `Δ[n] ⟶ Y` at the bottom has a diagonal filler `Δ[n] ⟶ X`. -/
@[stacks 08NL "the two clauses `X₀ → Y₀` surjective and lifting for `n ≥ 1` are the \
  single right lifting property against all boundary inclusions, the case `n = 0` \
  being the surjectivity since `∂Δ[0] = ⊥`", expose]
public def trivialKanFibrations : MorphismProperty SSet.{u} :=
  modelCategoryQuillen.I.rlp
deriving IsMultiplicative, RespectsIso, IsStableUnderRetracts

/-- **Stacks 08NN**.
Trivial Kan fibrations are stable under arbitrary base change. This is the general base-change
closure of a right lifting class, applied to the boundary-inclusion definition above. -/
@[stacks 08NN]
public instance trivialKanFibrations_isStableUnderBaseChange :
    trivialKanFibrations.{u}.IsStableUnderBaseChange :=
  MorphismProperty.rlp_isStableUnderBaseChange _

/-- The trivial Kan fibrations are the right lifting class of the boundary inclusions. -/
public lemma trivialKanFibrations_eq_rlp_I :
    trivialKanFibrations.{u} = modelCategoryQuillen.I.rlp :=
  rfl

/-- A morphism of simplicial sets is a trivial Kan fibration if and only if it has the right
lifting property with respect to every boundary inclusion `∂Δ[n].ι`, one `n` at a time. -/
public lemma trivialKanFibrations_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    trivialKanFibrations f ↔ ∀ n : ℕ, HasLiftingProperty ∂Δ[n].ι f := by
  rw [trivialKanFibrations_eq_rlp_I]
  refine ⟨fun hf n ↦ hf _ (modelCategoryQuillen.boundary_ι_mem_I n), ?_⟩
  rintro hf _ _ _ ⟨n⟩
  exact hf n

/-- A morphism `f : X ⟶ Y` of simplicial sets has the right lifting property with respect to
`∂Δ[0].ι` if and only if `X₀ → Y₀` is surjective: `∂Δ[0]` is initial, so a square over `∂Δ[0].ι`
is a `0`-simplex of `Y` and a filler is a `0`-simplex of `X` above it. -/
public lemma hasLiftingProperty_boundary_zero_ι_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    HasLiftingProperty ∂Δ[0].ι f ↔ Function.Surjective (f.app (Opposite.op ⦋0⦌)) := by
  have init : Limits.IsInitial (∂Δ[0] : SSet.{u}) := boundary_zero ▸ Subcomplex.isInitialBot
  refine ⟨fun _ y ↦ ?_, fun hf ↦ ⟨fun {_ b} _ ↦ ?_⟩⟩
  · have sq : CommSq (init.to X) ∂Δ[0].ι f (yonedaEquiv.symm y) := ⟨init.hom_ext _ _⟩
    refine ⟨yonedaEquiv sq.lift, ?_⟩
    rw [← yonedaEquiv_comp, sq.fac_right, Equiv.apply_symm_apply]
  · obtain ⟨x, hx⟩ := hf (yonedaEquiv b)
    refine ⟨⟨⟨yonedaEquiv.symm x, init.hom_ext _ _, yonedaEquiv.injective ?_⟩⟩⟩
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply, hx]

/-- The two clauses of [Stacks, Tag 08NL]: a morphism of simplicial sets is a trivial Kan
fibration if and only if `X₀ → Y₀` is surjective and, for every `n ≥ 1`, it has the right lifting
property with respect to `∂Δ[n].ι`. -/
public lemma trivialKanFibrations_iff_surjective_and_hasLiftingProperty {X Y : SSet.{u}}
    (f : X ⟶ Y) :
    trivialKanFibrations f ↔ Function.Surjective (f.app (Opposite.op ⦋0⦌)) ∧
      ∀ n : ℕ, 1 ≤ n → HasLiftingProperty ∂Δ[n].ι f := by
  rw [trivialKanFibrations_iff, ← hasLiftingProperty_boundary_zero_ι_iff]
  refine ⟨fun h ↦ ⟨h 0, fun n _ ↦ h n⟩, fun ⟨h₀, h⟩ n ↦ ?_⟩
  obtain _ | n := n
  exacts [h₀, h _ n.succ_pos]

/-- A trivial Kan fibration `f : X ⟶ Y` of simplicial sets is surjective on `0`-simplices. -/
public lemma surjective_app_zero_of_trivialKanFibrations {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : trivialKanFibrations f) : Function.Surjective (f.app (Opposite.op ⦋0⦌)) :=
  ((trivialKanFibrations_iff_surjective_and_hasLiftingProperty f).1 hf).1

end SSet

end

/-!
## Trivial Kan fibrations: lifting, products and filtered colimits

A morphism of simplicial sets is a *trivial Kan fibration* when it has the right lifting
property with respect to every boundary inclusion `∂Δ[n].ι : ∂Δ[n] ⟶ Δ[n]`
([Stacks, Tag 08NL], `SSet.trivialKanFibrations`). Such a morphism lifts against much more than
the boundary inclusions: it lifts against every monomorphism of simplicial sets, that is,
against every morphism which is injective in each degree, and as the boundary inclusions are
themselves monomorphisms, the trivial Kan fibrations are *precisely* the right lifting class of
the monomorphisms. The class is moreover stable under products and under filtered colimits.

### Main results

* `SSet.trivialKanFibrations_eq_rlp_monomorphisms`: the trivial Kan fibrations are the right
  lifting class of the monomorphisms of simplicial sets.
* `SSet.isStableUnderProductsOfShape_trivialKanFibrations`: the class of trivial Kan fibrations
  is stable under products indexed by any type.
* `SSet.isStableUnderFilteredColimits_trivialKanFibrations`: the class of trivial Kan
  fibrations is stable under filtered colimits.

### Implementation notes

The source's "`Z → W` termwise injective" is `CategoryTheory.MorphismProperty.monomorphisms
SSet`: a morphism of `Type`-valued presheaves is a monomorphism if and only if each of its
components is injective (`CategoryTheory.NatTrans.mono_iff_mono_app` with
`CategoryTheory.mono_iff_injective`). Of the two containments only
`trivialKanFibrations ≤ (monomorphisms SSet).rlp` has content, the reverse being
`MorphismProperty.antitone_rlp` applied to `SSet.modelCategoryQuillen.I_le_monomorphisms`; the
equality is stated because it is what serves as a rewrite in both directions, in particular to
*recognise* trivial Kan fibrations. Its content is Mathlib's `SSet.rlp_monomorphisms`, which
takes the other of the two standard roads: a monomorphism is exhibited as a relative cell
complex on the boundary inclusions (`SSet.relativeCellComplexOfMono`, attaching the
nondegenerate simplices of the complement as pushouts of coproducts of `∂Δ[n].ι`), and a right
lifting class is closed under those pushouts and under the transfinite composition. The source
instead extends a morphism one nondegenerate simplex at a time and appeals to Zorn's lemma,
which is that same transfinite induction.

The two stability statements quantify over arbitrary limit and colimit cocones rather than
fixing a construction of the products and the colimits, as Mathlib does for the trivial
fibrations of a model category
(`HomotopicalAlgebra.isStableUnderProductsOfShape_trivialFibrations`, an instance which does not
apply here, the Quillen model structure on `SSet` not being available). The source's own
morphisms `∏ X i ⟶ ∏ Y i` and `colim X₁ ⟶ colim X₂` are the cases of a chosen cone, whence
`trivialKanFibrations (Limits.Pi.map f)` and `trivialKanFibrations (colimMap f)` by
`CategoryTheory.MorphismProperty.limMap` and `CategoryTheory.MorphismProperty.colimMap`. Both
are `instance`s, joining the `IsMultiplicative` [Stacks, Tag 08NP], `RespectsIso` and
`IsStableUnderBaseChange` [Stacks, Tag 08NN] derived at Tag 08NL; stability under transfinite
composition then follows by inference.

Where the source says "a set", the index type of the products and both universes of the index
category of the colimits are arbitrary and independent of the universe of the simplicial sets.
For filtered colimits the added generality is in the morphism universe rather than the object
universe: `MorphismProperty.IsStableUnderColimitsOfShape` transfers along an equivalence of
shapes (`CategoryTheory.MorphismProperty.colimitsOfShape_eq_of_equivalence`), so the diagonal
form `IsStableUnderFilteredColimits.{u, u}` — the form of Mathlib's sibling statement for
monomorphisms of simplicial sets — already reaches every shape whose type of objects is
`u`-small, `ℕ` included via `AsSmall.{u} ℕ`, whereas a filtered `J : Type u` whose hom types
live in `Type (u + 5)` is equivalent to no shape of diagonal size. The generality costs the
hypothesis `HasColimitsOfSize.{w, w'} (Type u)`, which holds for arbitrary `w` under
`UnivLE.{w', u}` and is what makes colimits of shape `J` in
`SSet.{u} = SimplexCategoryᵒᵖ ⥤ Type u` degreewise, hence describable as in the source's hint
(Categories, Section 04AX).

The filtered-colimit argument is the source's: `∂Δ[n]` and `Δ[n]` are finite, hence finitely
presentable, so a lifting problem for `colim X₁ ⟶ colim X₂` against `∂Δ[n].ι` comes from one at
a single stage, where it is solved by hypothesis. Presentability is available for diagrams
indexed by an essentially small category, whereas `HasColimitsOfSize.{w, w'} (Type u)` leaves
the morphism universe `w` unconstrained, so the hom-sets are made small by hand, one diagram at
a time: `CategoryTheory.Quotient D.homRel` identifies two morphisms of `J` having the same image
under `D : J ⥤ C`, so that its hom-sets inject into those of `C` while its objects are those of
`J` and `D` factors through it. The quotient functor is full and surjective on objects, hence
final, which is what makes the passage to the quotient harmless: the target of a final functor
from a filtered category is filtered, and a functor preserving the colimit of the induced
diagram preserves the colimit of `D`.

### References

* [Stacks, Tag 08NL](https://stacks.math.columbia.edu/tag/08NL)
* [Stacks, Tag 08NM](https://stacks.math.columbia.edu/tag/08NM)
* [Stacks, Tag 08NR](https://stacks.math.columbia.edu/tag/08NR)
* [Stacks, Tag 08Q5](https://stacks.math.columbia.edu/tag/08Q5)
-/

section

open CategoryTheory Limits MorphismProperty

universe w w' v v' u u'

namespace SSet

/-- **A trivial Kan fibration lifts against any degreewise injective map.** For a trivial Kan
fibration `f : X ⟶ Y` of simplicial sets, every solid commutative square

```
Z --b--> X
|        |
v        v
W --a--> Y
```

with `Z ⟶ W` a monomorphism, i.e. injective in every degree, admits a diagonal `W ⟶ X`
making both triangles commute; conversely such a morphism `f` is a trivial Kan fibration,
the boundary inclusions being monomorphisms. Equivalently, the trivial Kan fibrations are
precisely the right lifting class of the monomorphisms of simplicial sets. -/
@[stacks 08NM "stated as the equality of morphism properties; the source's containment `≤` \
  is the content, the reverse being `antitone_rlp` on `I_le_monomorphisms`, and \"`Z → W` \
  termwise injective\" is `monomorphisms SSet`"]
public theorem trivialKanFibrations_eq_rlp_monomorphisms :
    trivialKanFibrations.{u} = (monomorphisms SSet.{u}).rlp :=
  rlp_monomorphisms.symm

/-- **A product of trivial Kan fibrations is a trivial Kan fibration.** If `f i : X i ⟶ Y i` is
a family of trivial Kan fibrations of simplicial sets, that is, of morphisms having the right
lifting property with respect to every boundary inclusion `∂Δ[n].ι`, then so is the induced
morphism `∏ X i ⟶ ∏ Y i` between any products of the `X i` and of the `Y i`. -/
@[stacks 08NR "stability under products is stated for arbitrary product cones, as \
  `IsStableUnderProductsOfShape` for the class of Tag 08NL; the source's `∏ X_i → ∏ Y_i` is \
  the case of `Limits.Pi.map`, and the index type is in an arbitrary universe where the \
  source says \"a set\""]
public instance isStableUnderProductsOfShape_trivialKanFibrations (J : Type w) :
    trivialKanFibrations.{u}.IsStableUnderProductsOfShape J :=
  modelCategoryQuillen.I.rlp_isStableUnderProductsOfShape J

section FilteredColimits

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- A full and essentially surjective functor is final: over any object `d` of the target, the
category of arrows `d ⟶ F.obj c` is connected, every one of them being connected to a chosen
isomorphism `d ≅ F.obj c₀` by a lift of its composite with that isomorphism. -/
private lemma final_of_full_of_essSurj {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] (F : C ⥤ D) [F.Full] [F.EssSurj] : F.Final where
  out d := by
    have h (X : StructuredArrow d F) :
        Zigzag (StructuredArrow.mk (F.objObjPreimageIso d).inv) X := by
      obtain ⟨g, hg⟩ := F.map_surjective ((F.objObjPreimageIso d).hom ≫ X.hom)
      exact Zigzag.of_hom (StructuredArrow.homMk g (by simp [hg]))
    have : Nonempty (StructuredArrow d F) := ⟨StructuredArrow.mk (F.objObjPreimageIso d).inv⟩
    exact zigzag_isConnected fun X Y ↦ (h X).symm.trans (h Y)

section

variable {C : Type u'} [Category.{v} C] {J : Type w'} [Category.{w} J]

/-- The quotient functor `J ⥤ CategoryTheory.Quotient D.homRel` is final, being full and
surjective on objects. -/
private instance final_quotientFunctor (D : J ⥤ C) :
    (CategoryTheory.Quotient.functor D.homRel).Final :=
  final_of_full_of_essSurj _

/-- The quotient of `J` by the relation identifying two morphisms with the same image under
`D : J ⥤ C` is essentially `v`-small as soon as the type of objects of `J` is `v`-small: its
hom-sets inject into those of `C`. -/
private instance essentiallySmall_quotient_homRel [Small.{v} J] {D : J ⥤ C} :
    EssentiallySmall.{v} (CategoryTheory.Quotient D.homRel) := by
  have : Small.{v} (CategoryTheory.Quotient D.homRel) :=
    (small_congr (CategoryTheory.Quotient.equiv D.homRel)).2 inferInstance
  have : LocallySmall.{v} (CategoryTheory.Quotient D.homRel) :=
    locallySmall_of_faithful (CategoryTheory.Quotient.lift D.homRel D fun _ _ _ _ h ↦ h)
  infer_instance

/-- The quotient of a filtered category `J` by the relation identifying two morphisms with the
same image under `D : J ⥤ C` is `ℵ₀`-filtered, being the target of a final functor from `J`. -/
private instance isCardinalFiltered_quotient_homRel [IsFiltered J] {D : J ⥤ C} :
    IsCardinalFiltered (CategoryTheory.Quotient D.homRel) Cardinal.aleph0.{v} :=
  (isCardinalFiltered_aleph0_iff _).2
    (IsFiltered.of_final (CategoryTheory.Quotient.functor D.homRel))

/-- The functor `hom(A, -)` corepresented by a finitely presentable object preserves the colimit
of any filtered diagram whose type of objects is small: the diagram factors through the quotient
of its index category by the relation identifying two morphisms with the same image, which is
essentially small and again filtered, and the quotient functor is final. No smallness assumption
is made on the hom-sets of the index category. -/
private lemma preservesColimit_of_isFinitelyPresentable_of_small [IsFiltered J] [Small.{v} J]
    (D : J ⥤ C) (A : C) [IsFinitelyPresentable.{v} A] :
    PreservesColimit D (coyoneda.obj (.op A)) := by
  have := preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall
    (X := A) (κ := Cardinal.aleph0.{v}) (CategoryTheory.Quotient D.homRel)
  rw [← CategoryTheory.Quotient.lift_spec D.homRel D fun _ _ _ _ h ↦ h]
  infer_instance

/-- If `i : A ⟶ B` is a morphism of finitely presentable objects and `f : X₁ ⟶ X₂` is a morphism
of filtered diagrams whose components have the right lifting property with respect to `i`, then
so has the morphism `φ` induced between the apices of colimit cocones: since `hom(A, -)` and
`hom(B, -)` preserve the colimits, a lifting problem for `φ` comes from one at a single stage,
where a filler exists and pushes forward to a filler for `φ`. -/
private lemma hasLiftingProperty_of_isColimit [IsFiltered J] [Small.{v} J] {A B : C}
    [IsFinitelyPresentable.{v} A] [IsFinitelyPresentable.{v} B] (i : A ⟶ B) {X₁ X₂ : J ⥤ C}
    {c₁ : Cocone X₁} {c₂ : Cocone X₂} (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (f : X₁ ⟶ X₂)
    (hf : ∀ j, HasLiftingProperty i (f.app j)) (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) :
    HasLiftingProperty i φ where
  sq_hasLift {t b} sq := by
    have := preservesColimit_of_isFinitelyPresentable_of_small X₁ A
    have := preservesColimit_of_isFinitelyPresentable_of_small X₂ A
    have := preservesColimit_of_isFinitelyPresentable_of_small X₂ B
    obtain ⟨j₁, t₁, ht⟩ := exists_hom_of_preservesColimit_coyoneda h₁ t
    obtain ⟨j₂, b₁, hb⟩ := exists_hom_of_preservesColimit_coyoneda h₂ b
    obtain ⟨k, u, v, huv⟩ := exists_eq_of_preservesColimit_coyoneda h₂ (t₁ ≫ f.app j₁) (i ≫ b₁)
      (by rw [Category.assoc, ← hφ j₁, ← Category.assoc, ht, sq.w, Category.assoc, hb])
    have hsq : CommSq (t₁ ≫ X₁.map u) i (f.app k) (b₁ ≫ X₂.map v) :=
      ⟨by simpa only [Category.assoc, f.naturality u] using huv⟩
    have := hf k
    refine ⟨⟨⟨hsq.lift ≫ c₁.ι.app k, ?_, ?_⟩⟩⟩
    · rw [← Category.assoc, hsq.fac_left, Category.assoc, c₁.w u, ht]
    · rw [Category.assoc, hφ k, ← Category.assoc, hsq.fac_right, Category.assoc, c₂.w v, hb]

end

/-- A type in `Type w'` is `u`-small as soon as `Type u` has colimits indexed by categories with
object type in `Type w'`: the colimit of the constant diagram `PUnit` over the type, made
discrete, contains the type. The discrete category is spelled out rather than taken to be
`CategoryTheory.Discrete`, whose hom types lie in `Type w'`, so that the hypothesis applies to
it: the shape has to have its morphisms in `Type w`. -/
private lemma small_of_hasColimitsOfSize [HasColimitsOfSize.{w, w'} (Type u)] (α : Type w') :
    Small.{u} α := by
  let _ : Category.{w} α :=
    { Hom := fun x y ↦ ULift.{w} (PLift (x = y))
      id := fun _ ↦ ⟨⟨rfl⟩⟩
      comp := fun f g ↦ ⟨⟨f.down.down.trans g.down.down⟩⟩ }
  let F : α ⥤ Type u := (Functor.const α).obj PUnit.{u + 1}
  refine small_of_injective (f := fun x ↦ colimit.ι F x PUnit.unit) fun x y hxy ↦ ?_
  let s : Cocone F :=
    { pt := ULift.{u} Prop
      ι :=
        { app := fun z ↦ ↾(fun _ : PUnit.{u + 1} ↦ ULift.up.{u} (z = x))
          naturality := fun z z' g ↦ by obtain ⟨⟨rfl⟩⟩ := g; rfl } }
  have h (z : α) : colimit.desc F s (colimit.ι F z PUnit.unit) = ULift.up.{u} (z = x) :=
    colimit.ι_desc_apply s z PUnit.unit
  have key : ULift.up.{u} (x = x) = ULift.up.{u} (y = x) := by
    rw [← h x, ← h y, show colimit.ι F x PUnit.unit = colimit.ι F y PUnit.unit from hxy]
  exact ((congrArg ULift.down key).mp rfl).symm

/-- **A filtered colimit of trivial Kan fibrations is a trivial Kan fibration.** If `J` is a
filtered category and `f : X₁ ⟶ X₂` is a morphism of diagrams `J ⥤ SSet` whose components
`f.app j` are all trivial Kan fibrations, that is, all have the right lifting property with
respect to every boundary inclusion `∂Δ[n].ι`, then so is the induced morphism
`colim X₁ ⟶ colim X₂` between any colimits of `X₁` and of `X₂`. -/
@[stacks 08Q5 "stability under filtered colimits is stated for arbitrary colimit cocones \
  over an arbitrary filtered index category, as `IsStableUnderFilteredColimits` for the class \
  of Tag 08NL; the source's `colim X₁ → colim X₂` is the case of `colimMap`, and the index \
  category is in arbitrary universes, the hypothesis `HasColimitsOfSize` being what makes the \
  colimits degreewise as in the source's hint"]
public instance isStableUnderFilteredColimits_trivialKanFibrations
    [HasColimitsOfSize.{w, w'} (Type u)] :
    MorphismProperty.IsStableUnderFilteredColimits.{w, w'} trivialKanFibrations.{u} where
  isStableUnderColimitsOfShape J _ _ :=
    { condition := fun X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ ↦ by
        rintro A B i ⟨n⟩
        have : Small.{u} J := small_of_hasColimitsOfSize.{w, w', u} J
        exact hasLiftingProperty_of_isColimit _ h₁ h₂ f
          (fun j ↦ hf j _ (MorphismProperty.ofHoms.mk n)) φ hφ }

end FilteredColimits

end SSet

end

/-!
## Composition and inverse limits of towers of trivial Kan fibrations

The composition of two trivial Kan fibrations is a trivial Kan fibration. A tower
`⋯ → U² → U¹ → U⁰` of simplicial sets is a functor `F : ℕᵒᵖ ⥤ SSet`, its inverse limit
`U = limₜ Uᵗ` is `limit F`, computed levelwise, and if every transition map `Uᵗ⁺¹ ⟶ Uᵗ` is a
trivial Kan fibration then so is the projection `U ⟶ U⁰`.

### Main results

* `SSet.trivialKanFibrations_comp`: the composition of two trivial Kan fibrations is a trivial Kan
  fibration.
* `CategoryTheory.MorphismProperty.rlp_limit_π_zero`: for any class of morphisms `W`, if every
  transition map of a tower `F : ℕᵒᵖ ⥤ C` has the right lifting property with respect to `W`, then
  so has the projection `limit F ⟶ F.obj (op 0)`.
* `SSet.trivialKanFibrations_limit_π_zero`: if every transition map of a tower
  `F : ℕᵒᵖ ⥤ SSet` is a trivial Kan fibration, then the projection `limₜ Uᵗ ⟶ U⁰` from the inverse
  limit is a trivial Kan fibration.

### Implementation notes

The tower statement is the case `W = SSet.modelCategoryQuillen.I` of a statement about right
lifting classes in an arbitrary category, which also gives the version for Kan fibrations
[Stacks, Tag 08NX], `W` being then the family of horn inclusions. The lift for the projection is
built by recursion on `t`: a lift `Δ[n] ⟶ Uᵗ` is lifted along the transition map `Uᵗ⁺¹ ⟶ Uᵗ`, and
the resulting compatible family is a cone over `F`.

### References

* [Stacks, Tag 08NP](https://stacks.math.columbia.edu/tag/08NP)
* [Stacks, Tag 08NQ](https://stacks.math.columbia.edu/tag/08NQ)
-/

section

open CategoryTheory Limits

universe v u

/-- If every transition map `F.obj (op (t + 1)) ⟶ F.obj (op t)` of a tower `F : ℕᵒᵖ ⥤ C` has the
right lifting property with respect to a class of morphisms `W`, then so has the projection
`limit F ⟶ F.obj (op 0)` from its limit: a lifting problem for the projection is solved by lifting
successively along the transition maps and assembling the lifts into a cone over `F`. -/
public theorem CategoryTheory.MorphismProperty.rlp_limit_π_zero {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) (F : ℕᵒᵖ ⥤ C) [HasLimit F]
    (hF : ∀ t : ℕ, W.rlp (F.map (homOfLE (Nat.le_succ t)).op)) :
    W.rlp (limit.π F (Opposite.op 0)) := by
  intro A B g hg
  constructor
  intro u v sq
  set q : ∀ t : ℕ, F.obj (Opposite.op (t + 1)) ⟶ F.obj (Opposite.op t) :=
    fun t ↦ F.map (homOfLE (Nat.le_succ t)).op
  set pi : ∀ t : ℕ, limit F ⟶ F.obj (Opposite.op t) := fun t ↦ limit.π F (Opposite.op t)
  have hw : ∀ t : ℕ, pi (t + 1) ≫ q t = pi t :=
    fun t ↦ limit.w F (homOfLE (Nat.le_succ t)).op
  have hfib : ∀ t : ℕ, HasLiftingProperty g (q t) := fun t ↦ hF t g hg
  have stepSq : ∀ (t : ℕ) (prev : B ⟶ F.obj (Opposite.op t)), g ≫ prev = u ≫ pi t →
      CommSq (u ≫ pi (t + 1)) g (q t) prev :=
    fun t prev hprev ↦ ⟨by rw [Category.assoc, hw t, ← hprev]⟩
  let l : (t : ℕ) → {x : B ⟶ F.obj (Opposite.op t) // g ≫ x = u ≫ pi t} :=
    fun t ↦ Nat.rec
      (⟨v, by rw [← sq.w]⟩ : {x : B ⟶ F.obj (Opposite.op 0) // g ≫ x = u ≫ pi 0})
      (fun t prev ↦
        have := hfib t
        ⟨(stepSq t prev.1 prev.2).lift, (stepSq t prev.1 prev.2).fac_left⟩)
      t
  have hcompat : ∀ t, (l (t + 1)).val ≫ q t = (l t).val := fun t ↦
    have := hfib t
    (stepSq t (l t).val (l t).property).fac_right
  let c : Cone F := ⟨B, NatTrans.ofOpSequence (fun t ↦ (l t).val) (by
    intro t
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
    rw [← hcompat t])⟩
  have hL : ∀ t, limit.lift F c ≫ limit.π F (Opposite.op t) = (l t).val :=
    fun t ↦ limit.lift_π c (Opposite.op t)
  exact ⟨⟨⟨limit.lift F c,
    limit.hom_ext fun ⟨t⟩ ↦ by rw [Category.assoc, hL t, (l t).property], hL 0⟩⟩⟩

namespace SSet

/-- **Stacks 08NP**.
The composition of two trivial Kan fibrations is a trivial Kan fibration. -/
@[stacks 08NP]
public theorem trivialKanFibrations_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : trivialKanFibrations f) (hg : trivialKanFibrations g) :
    trivialKanFibrations (f ≫ g) :=
  trivialKanFibrations.comp_mem f g hf hg

/-- **Stacks 08NQ**.
Let `⋯ → U² → U¹ → U⁰` be a tower of simplicial sets, encoded as a functor `F : ℕᵒᵖ ⥤ SSet`, and
let `U = limₜ Uᵗ` be its levelwise inverse limit. If every transition map `Uᵗ⁺¹ ⟶ Uᵗ` is a trivial
Kan fibration, then the projection `π⁰ : U ⟶ U⁰` is a trivial Kan fibration. -/
@[stacks 08NQ]
public theorem trivialKanFibrations_limit_π_zero (F : ℕᵒᵖ ⥤ SSet.{u})
    (h : ∀ t : ℕ, trivialKanFibrations (F.map (homOfLE (Nat.le_succ t)).op)) :
    trivialKanFibrations (limit.π F (Opposite.op 0)) := by
  rw [trivialKanFibrations_eq_rlp_I] at h ⊢
  exact modelCategoryQuillen.I.rlp_limit_π_zero F h

end SSet

end

/-!
## Trivial Kan fibrations are homotopy equivalences

A trivial Kan fibration of simplicial sets is a morphism `f : X ⟶ Y` with the right lifting
property against every boundary inclusion `∂Δ[n] ↪ Δ[n]`, that is, one in
`SSet.trivialKanFibrations`. Such an `f` has the right lifting property against every
monomorphism, hence admits a section `g`, and lifts against the cylinder boundary
`X ⊗ ∂Δ[1] ↪ X ⊗ Δ[1]` exhibit `g` as a two-sided homotopy inverse of `f`.

### Main definitions

* `SSet.Homotopy.ofEnds`: the homotopy from `f` to `g` carried by a morphism `k : X ⊗ Δ[1] ⟶ Y`
  whose restrictions to the two ends of the interval are `f` and `g`.

### Main results

* `SSet.exists_section_of_trivialKanFibrations`: a trivial Kan fibration `f : X ⟶ Y` admits a
  section `g : Y ⟶ X`, so `g ≫ f = 𝟙 Y`.
* `SSet.exists_cylinder_lift`: for `f` with the right lifting property against every
  monomorphism and `a b : X ⟶ X` with `a ≫ f = b ≫ f = f`, some `H : X ⊗ Δ[1] ⟶ X` has
  endpoints `a`, `b`.
* `SSet.exists_homotopy_comp_id`: for a section `g` of a trivial Kan fibration `f`, the
  composite `f ≫ g` is homotopic to `𝟙 X`.
* `SSet.trivialKanFibrations_isHomotopyEquiv`: a trivial Kan fibration is a homotopy
  equivalence.

### References

* [Stacks, Tag 08NS](https://stacks.math.columbia.edu/tag/08NS)
-/

section

@[expose] public section

universe u

open CategoryTheory Simplicial MonoidalCategory

namespace SSet

/-- A morphism `k : X ⊗ Δ[1] ⟶ Y` whose restrictions to the two ends of the interval are `f` and
`g`, as a homotopy from `f` to `g`. This is the missing constructor of `SSet.Homotopy`, which is
`SSet.RelativeMorphism.Homotopy` for the subcomplexes `⊥`: its relativity condition is vacuous, `⊥`
having no simplices in any degree, but the structure's default tactic does not discharge it. -/
@[simps]
def Homotopy.ofEnds {X Y : SSet.{u}} {f g : X ⟶ Y} (k : X ⊗ Δ[1] ⟶ Y) (hk₀ : ι₀ ≫ k = f)
    (hk₁ : ι₁ ≫ k = g) : Homotopy f g :=
  { h := k, h₀ := hk₀, h₁ := hk₁,
    rel := by
      ext m ⟨x, a⟩
      exact x.2.elim }

/-- A trivial Kan fibration of simplicial sets admits a section. -/
theorem exists_section_of_trivialKanFibrations {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : trivialKanFibrations f) :
    ∃ g : Y ⟶ X, g ≫ f = 𝟙 Y := by
  rw [trivialKanFibrations_eq_rlp_monomorphisms] at hf
  have hlift : HasLiftingProperty (⊥ : Y.Subcomplex).ι f := by
    refine hf _ ?_
    rw [MorphismProperty.monomorphisms.iff]
    infer_instance
  have hsq : CommSq (Subcomplex.isInitialBot.to X) (⊥ : Y.Subcomplex).ι f (𝟙 Y) :=
    ⟨Subcomplex.isInitialBot.hom_ext _ _⟩
  exact ⟨hsq.lift, hsq.fac_right⟩

/-- Let `f : X ⟶ Y` have the right lifting property against every monomorphism of simplicial
sets, and let `a b : X ⟶ X` satisfy `a ≫ f = f` and `b ≫ f = f`. Then there is a cylinder map
`H : X ⊗ Δ[1] ⟶ X` with `ι₀ ≫ H = a` and `ι₁ ≫ H = b`. -/
theorem exists_cylinder_lift {X Y : SSet.{u}} (f : X ⟶ Y) (a b : X ⟶ X)
    (hf : (MorphismProperty.monomorphisms SSet).rlp f)
    (ha : a ≫ f = f) (hb : b ≫ f = f) :
    ∃ H : X ⊗ Δ[1] ⟶ X, ι₀ ≫ H = a ∧ ι₁ ≫ H = b := by
  have hconst : ∀ {d : ℕ} (q : (∂Δ[1] : SSet) _⦋d⦌) (j : Fin (d + 1)),
      (stdSimplex.objEquiv ((∂Δ[1]).ι.app _ q)).toOrderHom j =
        (stdSimplex.objEquiv ((∂Δ[1]).ι.app _ q)).toOrderHom 0 := by
    intro d q j
    have hq : (∂Δ[1]).ι.app _ q ∈ (∂Δ[1] : (Δ[1]).Subcomplex).obj _ := by
      rw [Subfunctor.ι_app, TypeCat.ofHom_apply]
      exact q.property
    obtain ⟨c, hc⟩ := (mem_boundary_iff_notMem_range _).mp hq
    rw [stdSimplex.objEquiv_toOrderHom_apply, stdSimplex.objEquiv_toOrderHom_apply]
    have hj : ((∂Δ[1]).ι.app _ q j).val ≠ c.val := fun e => hc ⟨j, Fin.ext e⟩
    have h0 : ((∂Δ[1]).ι.app _ q 0).val ≠ c.val := fun e => hc ⟨0, Fin.ext e⟩
    have hj' := ((∂Δ[1]).ι.app _ q j).isLt
    have h0' := ((∂Δ[1]).ι.app _ q 0).isLt
    have hc' := c.isLt
    exact Fin.ext (by omega)
  have hlift : HasLiftingProperty (X ◁ (∂Δ[1]).ι) f := by
    refine hf _ ?_
    rw [MorphismProperty.monomorphisms.iff]
    refine ⟨fun g₁ g₂ h => CartesianMonoidalCategory.hom_ext _ _ ?_ ?_⟩
    · simpa using h =≫ SemiCartesianMonoidalCategory.fst _ _
    · rw [← cancel_mono (∂Δ[1]).ι]
      simpa using h =≫ SemiCartesianMonoidalCategory.snd _ _
  let v : ∀ k, (X ⊗ (∂Δ[1] : SSet)).obj k → Fin 2 := fun k p =>
    (stdSimplex.objEquiv ((∂Δ[1]).ι.app k
      ((SemiCartesianMonoidalCategory.snd X (∂Δ[1] : SSet)).app k p))).toOrderHom 0
  have hv : ∀ {k k' : SimplexCategoryᵒᵖ} (g : k ⟶ k') (p : (X ⊗ (∂Δ[1] : SSet)).obj k),
      v k' ((X ⊗ (∂Δ[1] : SSet)).map g p) = v k p := by
    rintro ⟨⟨d⟩⟩ ⟨⟨d'⟩⟩ g p
    dsimp only [v]
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, stdSimplex.map_apply,
      Equiv.apply_symm_apply, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
      Function.comp_apply]
    exact hconst _ _
  let sel : Fin 2 → (X ⟶ X) := fun i => if i = 0 then a else b
  have hsel : ∀ i, sel i ≫ f = f := by
    intro i
    fin_cases i
    exacts [ha, hb]
  let topMap : X ⊗ (∂Δ[1] : SSet) ⟶ X :=
    { app k := ↾fun p =>
        (sel (v k p)).app k ((SemiCartesianMonoidalCategory.fst X (∂Δ[1] : SSet)).app k p)
      naturality k k' g := by
        refine ConcreteCategory.hom_ext _ _ fun p => ?_
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, TypeCat.ofHom_apply,
          TypeCat.ofHom_apply, hv, NatTrans.naturality_apply, NatTrans.naturality_apply] }
  have hmem : ∀ i : Fin 2, (stdSimplex.obj₀Equiv.symm i)
      ∈ (∂Δ[1] : (Δ[1]).Subcomplex).obj (Opposite.op ⦋0⦌) := by
    rw [boundary_obj_eq_univ 0 1]
    exact fun _ => Set.mem_univ _
  have hrange : ∀ i : Fin 2,
      Subcomplex.range (SSet.const (X := X) (stdSimplex.obj₀Equiv.symm i)) ≤ ∂Δ[1] := by
    rintro i k _ ⟨x, rfl⟩
    rw [SSet.const_app, TypeCat.ofHom_apply]
    exact (∂Δ[1] : (Δ[1]).Subcomplex).map _ (hmem i)
  let endpt : Fin 2 → (X ⟶ X ⊗ (∂Δ[1] : SSet)) := fun i =>
    CartesianMonoidalCategory.lift (𝟙 X) (Subcomplex.lift _ (hrange i))
  have endpt_snd : ∀ i : Fin 2,
      endpt i ≫ SemiCartesianMonoidalCategory.snd X (∂Δ[1] : SSet) ≫ (∂Δ[1]).ι =
        SSet.const (stdSimplex.obj₀Equiv.symm i) := by
    intro i
    dsimp only [endpt]
    rw [CartesianMonoidalCategory.lift_snd_assoc, Subcomplex.lift_ι]
  have endpt_factor : ∀ i : Fin 2, endpt i ≫ (X ◁ (∂Δ[1]).ι) =
      CartesianMonoidalCategory.lift (𝟙 X) (SSet.const (stdSimplex.obj₀Equiv.symm i)) := by
    intro i
    dsimp only [endpt]
    rw [CartesianMonoidalCategory.lift_whiskerLeft, Subcomplex.lift_ι]
  have endpt_value : ∀ (i : Fin 2) (k : SimplexCategoryᵒᵖ) (x : X.obj k),
      v k ((endpt i).app k x) = i := by
    intro i k x
    dsimp only [v]
    rw [← NatTrans.comp_app_apply, ← NatTrans.comp_app_apply, endpt_snd,
      SSet.const_app, TypeCat.ofHom_apply, stdSimplex.map_apply, Equiv.apply_symm_apply,
      SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      Quiver.Hom.unop_op, SimplexCategory.const_apply, stdSimplex.objEquiv_toOrderHom_apply]
    exact stdSimplex.obj₀Equiv.{0}.apply_symm_apply i
  have endpt_top : ∀ i : Fin 2, endpt i ≫ topMap = sel i := by
    intro i
    ext k x
    rw [TypeCat.Fun.toFun_apply, TypeCat.Fun.toFun_apply, NatTrans.comp_app,
      ConcreteCategory.comp_apply]
    dsimp only [topMap]
    rw [TypeCat.ofHom_apply, endpt_value,
      ← NatTrans.comp_app_apply (endpt i) (SemiCartesianMonoidalCategory.fst X _)]
    dsimp only [endpt]
    rw [CartesianMonoidalCategory.lift_fst]
    simp
  have htop : topMap ≫ f = SemiCartesianMonoidalCategory.fst X (∂Δ[1] : SSet) ≫ f := by
    ext k p
    rw [TypeCat.Fun.toFun_apply, TypeCat.Fun.toFun_apply, NatTrans.comp_app, NatTrans.comp_app,
      ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    dsimp only [topMap]
    rw [TypeCat.ofHom_apply]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (hsel _) k) _
  have hsq : CommSq topMap (X ◁ (∂Δ[1]).ι) f
      (SemiCartesianMonoidalCategory.fst X Δ[1] ≫ f) :=
    ⟨by rw [htop, ← Category.assoc, CartesianMonoidalCategory.whiskerLeft_fst]⟩
  have hend : ∀ (i : Fin 2) (e : X ⟶ X ⊗ Δ[1]), endpt i ≫ (X ◁ (∂Δ[1]).ι) = e →
      e ≫ hsq.lift = sel i := fun i e h => by
    rw [← h, Category.assoc, hsq.fac_left, endpt_top]
  exact ⟨hsq.lift, hend 0 _ (endpt_factor 0), hend 1 _ (endpt_factor 1)⟩

/-- If `f : X ⟶ Y` is a trivial Kan fibration and `g : Y ⟶ X` is a section of `f`, then `f ≫ g`
is homotopic to `𝟙 X`. -/
theorem exists_homotopy_comp_id {X Y : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hf : trivialKanFibrations f) (hg : g ≫ f = 𝟙 Y) :
    Nonempty (Homotopy (f ≫ g) (𝟙 X)) := by
  rw [trivialKanFibrations_eq_rlp_monomorphisms] at hf
  obtain ⟨H, h₀, h₁⟩ := exists_cylinder_lift f (f ≫ g) (𝟙 X) hf
    (by rw [Category.assoc, hg, Category.comp_id]) (Category.id_comp f)
  exact ⟨Homotopy.ofEnds H h₀ h₁⟩

/-- **Stacks 08NS**.
A trivial Kan fibration `f : X ⟶ Y` of simplicial sets — one with the right lifting property
against every boundary inclusion `∂Δ[n] ↪ Δ[n]` — is a homotopy equivalence: there is a
`g : Y ⟶ X` with `f ≫ g` homotopic to `𝟙 X` and `g ≫ f` homotopic to `𝟙 Y`. -/
@[stacks 08NS]
theorem trivialKanFibrations_isHomotopyEquiv
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : trivialKanFibrations f) :
    ∃ g : Y ⟶ X,
      Nonempty (Homotopy (f ≫ g) (𝟙 X)) ∧
      Nonempty (Homotopy (g ≫ f) (𝟙 Y)) := by
  obtain ⟨g, hg⟩ := exists_section_of_trivialKanFibrations f hf
  refine ⟨g, exists_homotopy_comp_id f g hf hg, ?_⟩
  rw [hg, Homotopy]
  exact ⟨RelativeMorphism.Homotopy.refl _⟩

end SSet

end

end
