module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentSiteSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafifyMixed
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.IteratedSliceSheafification
public import StacksCore.Tactic.StacksAttribute

/-!
# Coherence of a tensor product over an arbitrary site

Stacks 03L6 (7): on a ringed site, the tensor product of a sheaf of modules of finite
presentation with a coherent sheaf of modules is coherent. This is the same assertion as
Stacks 01CE, which `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoherence` proves on a
ringed space, and the two things that file leaves open are supplied here.

The first is the gluing step. `Stacks.TensorCoherence.isCoherent_tensor_of_presentation` is
already stated over an arbitrary site — it is the case of a *global* finite presentation — but
`Stacks.TensorCoherence.isCoherent_tensorSheaf`, which glues it along a covering on which the
presentation exists, is stated only for the site of opens of a topological space. Nothing in
that argument is about opens: the gluing principle
`Stacks.SheafOfModules.Site.isCoherent_of_coversTop` and the restriction principle
`Stacks.SheafOfModules.Site.isCoherent_over` are both site-level already, and
`SheafOfModules.QuasicoherentData` indexes its covering in the universe of objects of the site,
which is exactly the universe `isCoherent_of_coversTop` asks for. What the space-level statement
*did* get for free is the whole instance pile of the closure theory of coherence, which the site
of opens of a space discharges by synthesis; over an arbitrary site part of it has to be
assumed, and that is the only difference between the two statements.

The second is the sectionwise form of the coherence predicate, which is Stacks 03DL (10). That
comparison is no longer here: it is
`Stacks.SheafOfModules.Site.isCoherent_iff_isFiniteTypeSections` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentSiteSections`, stated as an equivalence
and independent of anything about tensor products.

## Main results

* `Stacks.TensorCoherence.sheafTensorRight_obj_eq_tensorSheafBifunctor_obj`: the tensor product
  of sheaves of modules of `StacksFrontier.CategoryTheory.Sites.Modules.Flat`, over which right
  exactness is available, **is** the tensor-product bifunctor of Tag 0GMW, by `rfl`.
* `Stacks.TensorCoherence.isCoherent_tensorSheafSite` and
  `Stacks.TensorCoherence.isCoherent_tensorSheafBifunctor`: **Stacks Project, Tag 03L6 (7),
  over an arbitrary site**, in the two spellings of the tensor product.

## Implementation notes

**The instance hypotheses, and which ones are *not* needed.** The closure theory of coherence on
a site assumes sheafification and local bijectivity for `AddCommGrpCat.{w}` separately at the
base site and at each level of the tower of slice sites, and
`isCoherent_tensor_of_presentation` is applied here on a slice site and itself reaches three
levels down, so the proof below touches the tower up to depth four. Those deep hypotheses are
nevertheless **not** assumed, because they are theorems:
`CategoryTheory.hasSheafify_over_over` and `CategoryTheory.wEqualsLocallyBijective_over_over`
(in `StacksFrontier.CategoryTheory.Sites.SliceTopos.IteratedSliceSheafification`) derive each level
of the tower from the level below it, via the iterated slice equivalence
`(C/Y)/Z ≌ C/Z.left`. They are attached as `local instance`s for this file, which is what lets
the *statements* below elaborate: `Stacks.SheafOfModules.Site.IsCoherent` needs the depth-two
hypotheses in order to be stated at all, so they cannot be introduced inside a proof. What
remains assumed is the base site and slice depth one, and nothing deeper.

Two further remarks on the shape:

* `HasBinaryProducts C` is **not** assumed, although the closure theory's own section assumes
  it. It is not needed: every application of the closure theory here is on a slice site, and a
  slice category of a category with pullbacks has a terminal object and finite wide pullbacks,
  hence binary products, by synthesis; the unused-section-variable linter confirms this.
* `HasPullbacks C` is **not** assumed either, being synthesized from
  `HasFiniteWidePullbacks C`.

**The module universe equals the ring universe**, as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoherence`: Mathlib declares
`SheafOfModules.IsFiniteType` — and hence coherence — only for `SheafOfModules.{u} R` with
`R : Sheaf J RingCat.{u}`, and the monoidal unit of the tensor product only for a module
universe equal to the ring universe. Decoupling either is a change to Mathlib. The two site
universes `u` and `v` stay independent throughout.

## References

* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

/-! ### Stacks 03L6 (7) over an arbitrary site -/

namespace Stacks.TensorCoherence

open Stacks.SheafOfModules.Site

section Bifunctor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {O : Sheaf J CommRingCat.{w}}

/-- The tensor product of sheaves of modules of
`StacksFrontier.CategoryTheory.Sites.Modules.Flat` is the tensor-product bifunctor of Tag 0GMW. -/
lemma sheafTensorRight_obj_eq_tensorSheafBifunctor_obj
    (F G : SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G)).obj F
      = ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj F).obj G :=
  rfl

end Bifunctor

-- Each level of the tower of slice sites inherits sheafification and local bijectivity from the
-- level below it, so only the base site and slice depth one are assumed below. These are local
-- instances rather than global ones because their conclusion `P ((J.over Y).over Z)` matches
-- every level of the tower above the first, so globally they would be tried on the way to
-- resolving themselves.
attribute [local instance] hasSheafify_over_over wEqualsLocallyBijective_over_over

variable {C : Type u} [Category.{v} C] [HasFiniteWidePullbacks C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O : Sheaf J CommRingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{w}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{w}]
  (F G : SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O))

/-- **Stacks Project, Tag 03L6 (7), over an arbitrary site.** The tensor product of a sheaf of
modules of finite presentation with a coherent sheaf of modules is coherent. -/
theorem isCoherent_tensorSheafSite [F.IsFinitePresentation] (hG : IsCoherent G) :
    IsCoherent ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        O).flip.obj G)).obj F) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  refine isCoherent_of_coversTop _ q.X q.coversTop fun i => ?_
  have hGi : IsCoherent (G.over (q.X i)) := have := hG; isCoherent_over (q.X i)
  have key : IsCoherent ((((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w}
      (O.over (q.X i))).flip.obj (G.over (q.X i)))).obj (F.over (q.X i))) :=
    isCoherent_tensor_of_presentation (O := O.over (q.X i)) (G.over (q.X i)) (F.over (q.X i))
      hGi (q.presentation i) (hq.isFinite_presentation i)
  exact isCoherent_of_iso' (O := O.over (q.X i)) (tensorSheafOverIso F G (q.X i)) key

/-- **Stacks Project, Tag 03L6 (7), over an arbitrary site, in the tensor-bifunctor
spelling.** -/
theorem isCoherent_tensorSheafBifunctor [F.IsFinitePresentation] (hG : IsCoherent G) :
    IsCoherent (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj F).obj G) :=
  isCoherent_tensorSheafSite F G hG

end Stacks.TensorCoherence

end
