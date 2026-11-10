module

public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWatts

/-!
# Arbitrary coproducts are preserved as soon as finite ones and filtered colimits are

A coproduct `∐ᵢ Xᵢ` is the colimit, over the filtered poset of finite subsets of the index
type, of the finite sub-coproducts: that is Mathlib's
`CategoryTheory.Limits.CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone`, which is
used there to *construct* coproducts. This file records the corresponding *preservation*
statement, which Mathlib does not have: a functor which preserves finite coproducts and the
colimits indexed by `Finset (Discrete α)` preserves coproducts of shape `α`.

The step is the one the proof of [Stacks, Tag 0EX3] (b) elides. The source says that the functor
`M ↦ H^d(X', F' ⊗ (f')^* M~)` "commutes with direct sums" and cites [Stacks, Tag 01FF], which is
a statement about *directed systems*, not about direct sums. Additivity supplies the finite
coproducts and Tag 01FF supplies the filtered colimits; this file is what turns the pair into the
direct sums that `Stacks.EilenbergWatts.iso` consumes.

## Main results

* `Stacks.CoproductsFromFiltered.preservesColimit_discreteFunctor`: a functor preserving finite
  coproducts and `Finset (Discrete α)`-indexed colimits preserves the coproduct of a family
  indexed by `α`.
* `Stacks.CoproductsFromFiltered.preservesColimitsOfShape_discrete`: the same as preservation of
  all colimits of shape `Discrete α`.
* `Stacks.EilenbergWatts.isoOfFilteredColimits`: Eilenberg-Watts with "commutes with direct
  sums" replaced by "commutes with directed colimits", which is the hypothesis [Stacks, Tag
  01FF] actually provides.

## Implementation notes

Every statement below is phrased with the target of an injection written as the value of
Mathlib's diagram `liftToFinsetObj (Discrete.functor f)`, and the leg of the colimit cocone
written with `∐ f` as its codomain, by giving the two abbreviations `subι` and `totalι` an
explicit return type. Without that the two spellings `(liftToFinsetObj (Discrete.functor f)).obj s`
and `∐ fun x : ↥s => (Discrete.functor f).obj x` of one object are interchangeable for the
elaborator but not while a rewrite motive is being formed, and every `rw` in the file fails with
a type-correctness complaint about the `implicit` transparency level.

## References

* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public section

universe w v v' u u'

open CategoryTheory CategoryTheory.Limits CoproductsFromFiniteFiltered

namespace Stacks.CoproductsFromFiltered

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) {α : Type w} (f : α → C)

section Diagram

variable [HasFiniteCoproducts C]

/-- The injection of one summand into the coproduct over a finite subset `s` of the index type,
with its target written as the value at `s` of Mathlib's finite-sub-coproduct diagram. -/
noncomputable abbrev subι (s : Finset (Discrete α)) (x : ↥s) :
    f (x : Discrete α).as ⟶ (liftToFinsetObj (Discrete.functor f)).obj s :=
  Sigma.ι (fun y : ↥s => (Discrete.functor f).obj y) x

/-- The leg at `s` of the cocone exhibiting `∐ f` as the colimit of its finite
sub-coproducts. -/
noncomputable abbrev totalι [HasCoproduct f] (s : Finset (Discrete α)) :
    (liftToFinsetObj (Discrete.functor f)).obj s ⟶ ∐ f :=
  (finiteSubcoproductsCocone f).ι.app s

/-- Enlarging the finite subset carries the injection of a summand to the injection of the same
summand. -/
theorem subι_comp_liftToFinsetObj_map {s s' : Finset (Discrete α)} (h : s ⟶ s') (x : ↥s) :
    subι f s x ≫ (liftToFinsetObj (Discrete.functor f)).map h =
      subι f s' ⟨x.1, h.down.down x.2⟩ := by
  simp [liftToFinsetObj, subι]

/-- The injection of a summand into a finite sub-coproduct, followed by the leg of the cocone,
is the injection of that summand into the whole coproduct. -/
theorem subι_comp_totalι [HasCoproduct f] (s : Finset (Discrete α)) (x : ↥s) :
    subι f s x ≫ totalι f s = Sigma.ι f (x : Discrete α).as := by
  simp only [finiteSubcoproductsCocone_ι_app, subι, totalι]
  exact Sigma.ι_comp_desc _ _

/-- `subι_comp_totalι` at a singleton subset, where the summand is `f i` itself. -/
theorem subι_singleton_comp_totalι [HasCoproduct f] (i : α) :
    subι f {Discrete.mk i} ⟨Discrete.mk i, Finset.mem_singleton_self _⟩ ≫
        totalι f {Discrete.mk i} = Sigma.ι f i :=
  subι_comp_totalι f {Discrete.mk i} ⟨Discrete.mk i, Finset.mem_singleton_self _⟩

end Diagram

section Finite

variable [HasFiniteCoproducts C] [PreservesFiniteCoproducts F]

/-- `F` of the coproduct over a finite subset of the index type is the coproduct of the images
of the summands. -/
noncomputable def isColimitMapFiniteSubcofan (s : Finset (Discrete α)) :
    IsColimit (F.mapCocone (Cofan.mk (∐ fun x : ↥s => (Discrete.functor f).obj x)
      (Sigma.ι fun x : ↥s => (Discrete.functor f).obj x))) :=
  isColimitOfPreserves F (coproductIsCoproduct _)

/-- Two morphisms out of `F` of a finite sub-coproduct agree as soon as they agree on each
summand. -/
theorem hom_ext_map_finite {s : Finset (Discrete α)} {W : D}
    {a b : F.obj ((liftToFinsetObj (Discrete.functor f)).obj s) ⟶ W}
    (h : ∀ x : ↥s, F.map (subι f s x) ≫ a = F.map (subι f s x) ≫ b) : a = b :=
  (isColimitMapFiniteSubcofan F f s).hom_ext fun x => h x.as

/-- The component at a finite subset of the cocone `descCocone`: the morphism out of `F` of the
finite sub-coproduct whose restriction to each summand is the given leg. -/
noncomputable def descApp (t : Cocone (Discrete.functor f ⋙ F)) (s : Finset (Discrete α)) :
    F.obj ((liftToFinsetObj (Discrete.functor f)).obj s) ⟶ t.pt :=
  (isColimitMapFiniteSubcofan F f s).desc
    (Cocone.mk t.pt (Discrete.natTrans fun x => t.ι.app (x.as : Discrete α)))

/-- `descApp` restricted to a summand is the corresponding leg of the given cocone. -/
theorem map_subι_descApp (t : Cocone (Discrete.functor f ⋙ F))
    {s : Finset (Discrete α)} (x : ↥s) :
    F.map (subι f s x) ≫ descApp F f t s = t.ι.app (x : Discrete α) :=
  (isColimitMapFiniteSubcofan F f s).fac _ ⟨x⟩

/-- The components of `descApp` are compatible with enlarging the finite subset. -/
theorem map_liftToFinsetObj_map_descApp (t : Cocone (Discrete.functor f ⋙ F))
    {s s' : Finset (Discrete α)} (h : s ⟶ s') :
    F.map ((liftToFinsetObj (Discrete.functor f)).map h) ≫ descApp F f t s' =
      descApp F f t s := by
  refine hom_ext_map_finite F f fun x => ?_
  rw [← Category.assoc, ← F.map_comp, subι_comp_liftToFinsetObj_map, map_subι_descApp,
    map_subι_descApp]

/-- A cocone on the family `fun i => F (f i)` induces a cocone on the image under `F` of the
finite-sub-coproduct diagram. -/
noncomputable def descCocone (t : Cocone (Discrete.functor f ⋙ F)) :
    Cocone (liftToFinsetObj (Discrete.functor f) ⋙ F) where
  pt := t.pt
  ι :=
    { app := descApp F f t
      naturality := fun _ _ h =>
        (map_liftToFinsetObj_map_descApp F f t h).trans (Category.comp_id _).symm }

/-- The component of `descCocone` at a finite subset is `descApp`. -/
@[simp]
theorem descCocone_ι_app (t : Cocone (Discrete.functor f ⋙ F)) (s : Finset (Discrete α)) :
    (descCocone F f t).ι.app s = descApp F f t s :=
  rfl

end Finite

section Filtered

variable [HasFiniteCoproducts C] [PreservesFiniteCoproducts F] [HasCoproduct f]
  [HasColimitsOfShape (Finset (Discrete α)) C]
  [PreservesColimitsOfShape (Finset (Discrete α)) F]

/-- `F` preserves the colimit expressing `∐ f` as the colimit of its finite sub-coproducts. -/
noncomputable def isColimitMapFinsetCocone :
    IsColimit (F.mapCocone (finiteSubcoproductsCocone f)) :=
  isColimitOfPreserves F (isColimitFiniteSubproductsCocone f)

/-- The morphism out of `F (∐ f)` induced by a cocone on the images of the summands. -/
noncomputable def descTotal (t : Cocone (Discrete.functor f ⋙ F)) : F.obj (∐ f) ⟶ t.pt :=
  (isColimitMapFinsetCocone F f).desc (descCocone F f t)

/-- `descTotal` restricted to a finite sub-coproduct is `descApp`. -/
theorem map_totalι_descTotal (t : Cocone (Discrete.functor f ⋙ F)) (s : Finset (Discrete α)) :
    F.map (totalι f s) ≫ descTotal F f t = descApp F f t s :=
  (isColimitMapFinsetCocone F f).fac _ s

/-- `descTotal` restricted to a summand is the corresponding leg of the given cocone. -/
theorem map_sigmaι_descTotal (t : Cocone (Discrete.functor f ⋙ F)) (i : α) :
    F.map (Sigma.ι f i) ≫ descTotal F f t = t.ι.app ⟨i⟩ := by
  rw [← subι_singleton_comp_totalι f i, F.map_comp, Category.assoc, map_totalι_descTotal,
    map_subι_descApp]

/-- **`F` preserves the coproduct `∐ f`.** The coproduct is the colimit of its finite
sub-coproducts over the filtered poset of finite subsets of the index type, `F` preserves that
colimit, and `F` preserves each finite sub-coproduct; the descent is assembled from the two. -/
noncomputable def isColimitMapCofan : IsColimit (F.mapCocone (Cofan.mk (∐ f) (Sigma.ι f))) where
  desc t := descTotal F f t
  fac t j := map_sigmaι_descTotal F f t j.as
  uniq t m hm := by
    refine (isColimitMapFinsetCocone F f).uniq (descCocone F f t) m fun s => ?_
    change F.map (totalι f s) ≫ m = descApp F f t s
    refine hom_ext_map_finite F f fun x => ?_
    rw [← Category.assoc, ← F.map_comp, subι_comp_totalι, map_subι_descApp]
    exact hm _

/-- **Finite coproducts and filtered colimits give the coproduct of one family.** -/
theorem preservesColimit_discreteFunctor : PreservesColimit (Discrete.functor f) F :=
  preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct f) (isColimitMapCofan F f)

end Filtered

/-- **Finite coproducts and filtered colimits give arbitrary coproducts.** A functor which
preserves finite coproducts and the colimits indexed by the finite subsets of `α` preserves all
colimits of shape `Discrete α`. Mathlib has the corresponding *construction* of coproducts
(`CategoryTheory.Limits.hasCoproducts_of_finite_and_filtered`) but not this preservation
statement. -/
theorem preservesColimitsOfShape_discrete [HasFiniteCoproducts C] [HasCoproducts.{w} C]
    [HasColimitsOfShape (Finset (Discrete α)) C] [PreservesFiniteCoproducts F]
    [PreservesColimitsOfShape (Finset (Discrete α)) F] :
    PreservesColimitsOfShape (Discrete α) F := by
  refine ⟨fun {K} => ?_⟩
  have : PreservesColimit (Discrete.functor (K.obj ∘ Discrete.mk)) F :=
    preservesColimit_discreteFunctor F _
  exact preservesColimit_of_iso_diagram F (Discrete.natIsoFunctor (F := K)).symm

end Stacks.CoproductsFromFiltered

namespace Stacks.EilenbergWatts

/-- **Eilenberg-Watts with "commutes with direct sums" replaced by "commutes with directed
colimits".** A right exact `R`-linear endofunctor of `R`-modules which preserves the colimits
indexed by the finite subsets of every index type is tensoring with `F(R)`. This is the form in
which the proof of [Stacks, Tag 0EX3] (b) has its hypothesis: [Stacks, Tag 01FF] is a statement
about directed systems, and the direct sums of `Stacks.EilenbergWatts.iso` come from it only
through `Stacks.CoproductsFromFiltered.preservesColimitsOfShape_discrete`. -/
noncomputable def isoOfFilteredColimits {R : Type u} [CommRing R]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive] [Functor.Linear R F]
    [PreservesFiniteColimits F]
    [∀ ι : Type u, PreservesColimitsOfShape (Finset (Discrete ι)) F] :
    MonoidalCategory.tensorLeft (F.obj (ModuleCat.of R R)) ≅ F :=
  have : ∀ ι : Type u, PreservesColimitsOfShape (Discrete ι) F := fun _ =>
    Stacks.CoproductsFromFiltered.preservesColimitsOfShape_discrete F
  iso F

end Stacks.EilenbergWatts

end
