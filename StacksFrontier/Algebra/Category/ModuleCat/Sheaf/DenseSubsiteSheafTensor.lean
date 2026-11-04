module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteSheafification

/-!
# Restriction to a dense subsite commutes with the tensor product of sheaves of modules

Let `v : C ⥤ C'` exhibit `(C, J)` as a dense subsite of `(C', K)` and let `O` be a sheaf of
commutative rings on `(C', K)`. The tensor product of sheaves of `O`-modules used in this
development, `(Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj N` (Stacks 03ER), is
the composite of three functors: forget to presheaves of modules, take the objectwise tensor
product (`PresheafOfModules.tensorBifunctor`, which is `Stacks.tensorRight` by `rfl`), and
sheafify. Restriction of sections along `v` commutes with each of
the three — with the first two on the nose
(`Stacks.DenseSubsiteModules.moduleRestriction_comp_forget` and
`presheafRestrict_comp_tensorRight`, both `rfl`) and with the third up to the isomorphism
`Stacks.DenseSubsiteModules.commRingRestriction_sheafification` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteSheafification`. This file assembles
those three facts into

`Stacks.DenseSubsiteModules.moduleRestriction_sheafTensorRight`:
`(sheafTensor O).flip.obj N ⋙ moduleRestriction ≅
  moduleRestriction ⋙ (sheafTensor O|_C).flip.obj N|_C`.

Together with `Stacks.DenseSubsiteModules.moduleRestrictionEquivalence` — restriction of
sheaves of modules to a dense subsite is an equivalence — this says that the tensor product of
sheaves of modules is carried to the tensor product by that equivalence, i.e. that the tensor
product depends only on the ringed topos `(Sh(C'), O)` and not on the site presenting it.
That is Stacks 03DG method (2) for the tensor product, and the input Stacks 05VD consumes
through 03DG.

## Main definitions

* `Stacks.DenseSubsiteModules.moduleRestriction_sheafTensorRight`: the comparison isomorphism.
  This is the main result.
## Main results

* `Stacks.DenseSubsiteModules.forget_comp_presheafCommRingRestrict`,
  `tensorRight_comp_presheafCommRingRestrict`, `presheafCommRingRestrict_obj_val`: the three
  individually cheap `rfl` steps out of which the comparison is built.
* `Stacks.DenseSubsiteModules.forget_tensorRight_comp_presheafCommRingRestrict`: the
  presheaf-level half of the comparison — forgetting, tensoring and then restricting is
  restricting, forgetting and then tensoring. **True by `rfl` and not provable by `rfl`**; see
  the implementation notes.
* `Stacks.DenseSubsiteModules.sheafTensorRight_comp_moduleRestriction_eq` and
  `moduleRestriction_comp_sheafTensorRight_eq`: the two unfoldings of the tensor product into
  its three factors, one on each side of the comparison.

## Implementation notes

**There is no mathematics in this file.** Every step is an equality of functors that holds by
`rfl`, and the isomorphism `commRingRestriction_sheafification` supplies the only
non-identity comparison. What the file is about is *elaboration cost*: the one-shot

```
(Functor.isoWhiskerLeft (SheafOfModules.forget _ ⋙ Stacks.tensorRight N.val)
  (commRingRestriction_sheafification J K v O).symm :
    (Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj N ⋙ moduleRestriction J K v _ ≅
      moduleRestriction J K v _ ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor _).flip.obj _)
```

is the whole of `moduleRestriction_sheafTensorRight`, and it does not elaborate: it dies with a
deterministic `whnf` timeout at the default heartbeat budget, after about 29 seconds, while
every individual step in it is a verified `rfl`. The remedy — and the reusable recipe — has
three parts.

**1. A type ascription does not pin a spelling; a declared result type does.** `inferType`
ignores an ascription, so `(e : T)` leaves the elaborator unifying the inferred type of `e`
against `T`, which is exactly the large defeq problem one is trying to avoid. Only a `def`'s
declared result type, or a `let`'s declared binder type, fixes a spelling. Hence
`presheafCommRingRestrict`, and hence the named equations below: each is a `theorem` whose
statement writes both sides out, so `rfl` is asked one small question at a time.

**2. The cheap body and the pinned type are independent choices, and the functor needs both.**
Mathlib's `PresheafOfModules.pushforward (𝟙 _)` is `pushforward₀` followed by
`restrictScalars (𝟙 _)`, while `presheafRestrict` is `pushforward₀` with no restriction of
scalars. The two are definitionally equal (`presheafRestrict_eq`), but the commutation with
`Stacks.tensorRight` is cheap by `rfl` through `pushforward₀` and exhausts the budget through
`pushforward (𝟙 _)`. So `presheafCommRingRestrict` is declared with the
result type the tensor product uses on the subsite and the body the elaborator can see
through, and `commRingRestriction_sheafification` is stated across it once and for all. For
the same reason the two unfolding equations name the source `R₀` of each sheafification
functor: left implicit, it is solved from the codomain of `Stacks.tensorRight`, spelled
`Stacks.ringPresheaf`, and `𝟙` between two differently spelled presheaves of rings is not seen
by instance search to be locally bijective.

**3. Composing cheap `rfl`s does not give a cheap `rfl`.** This is the step that is easy to get
wrong. `forget_comp_presheafCommRingRestrict`, `tensorRight_comp_presheafCommRingRestrict` and
`presheafCommRingRestrict_obj_val` are each `rfl` in well under a second, and their composite
`forget_tensorRight_comp_presheafCommRingRestrict` *also* holds by `rfl` — but asking `rfl` for it
times out. It has to be assembled, by rewriting along two of the three and whiskering the third
with `congrArg`. The same is true one level up: the equality obtained from
`forget_tensorRight_comp_presheafCommRingRestrict` by composing with the sheafification functor is
not provable by `rfl` either, and is `congrArg (· ⋙ sheafification) · |>.trans` of it. So the
chain is

```
(sheafTensor O).flip.obj N ⋙ moduleRestriction
  = (forget ⋙ tensorRight N.val) ⋙ (sheafification ⋙ moduleRestriction)   -- rfl, cheap
  ≅ (forget ⋙ tensorRight N.val) ⋙ (presheafCommRingRestrict ⋙ sheafification)
                                                      -- isoWhiskerLeft, no defeq asked
  = moduleRestriction ⋙ (sheafTensor O|_C).flip.obj N|_C              -- assembled, not rfl
```

and no single step asks the elaborator to `whnf` the whole composite. There is no `set_option`,
no raised heartbeat budget and no `erw` in this file; the whole module elaborates in a few
seconds.

**Why `rw` and not `simp` or `Category.assoc`.** The crossings here are equalities of
*functors*, so rewriting along one cannot strand a type, and `rw` is the right tool; `exact`
with the equation as a term is the right tool when the two sides are only definitionally equal.
What does not work is `rw` across a spelling boundary, since `rw` demands a syntactic match, nor
`simp [Category.assoc]` on a composite whose middle object has two `rfl`-equal spellings, where
`simp` reports "made no progress" and `rw` reports that it did not find the pattern it is
printing.

**Hypotheses and universes.** Beyond `v.IsDenseSubsite J K`, these are exactly what the two
sheafification functors and the two underlying-ring-sheaf functors need: `HasWeakSheafify` and
`WEqualsLocallyBijective` for `AddCommGrpCat.{w}` on `J` and on `K`, and `HasSheafCompose` for
`forget₂ CommRingCat RingCat` on `J` and on `K`. Nothing is assumed about the sites: no finite
limits, no products, no smallness. Cocontinuity of `v` is automatic for a dense subsite. The
single module universe `w` is inherited from `Stacks.DenseSubsiteModules.moduleRestriction`
and from the tensor product `Stacks.SheafOfModules.Tensor.sheafTensor`, which is used over
`O : Sheaf K CommRingCat.{w}` with modules in `SheafOfModules.{w}`; the four universes
of the two sites are free and independent.

**What is still owed.** The dense-subsite hypothesis is used only through
`commRingRestriction_sheafification`; the sheafification factor itself,
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyNatIso`, holds for any
continuous and cocontinuous `G`, so the comparison here generalizes to that setting once the
ring-sheaf spelling is pinned there. That generalization would subsume
`Stacks.TensorCoherence.tensorSheafOverIso` (the same comparison for the slice site
`Over U`, objectwise rather than as an isomorphism of functors) and
`Stacks.SheafOfModules.SliceRestriction.tensorSheafOver` (the same for the Tag 01CA spelling of
the tensor product); a dedup against those two is owed if it is carried out.

## References

* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD), whose proof consumes
  this through Tag 03DG
* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG), method (2)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU), the Comparison Lemma
-/

@[expose] public section

open CategoryTheory

universe w v₁ u₁ v₂ u₂

namespace Stacks.DenseSubsiteModules

section DenseSubsite

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  (J : GrothendieckTopology C) (K : GrothendieckTopology C')
  (v : C ⥤ C') [v.IsDenseSubsite J K]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- Forgetting a sheaf of modules to a presheaf and then restricting is restricting and then
forgetting. This is `Stacks.DenseSubsiteModules.moduleRestriction_comp_forget` at the pinned
spelling. -/
theorem forget_comp_presheafCommRingRestrict (O : Sheaf K CommRingCat.{w}) :
    SheafOfModules.forget.{w} (Stacks.commRingSheafToRingSheaf O) ⋙
        presheafCommRingRestrict J K v O =
      moduleRestriction.{w} J K v (Stacks.commRingSheafToRingSheaf O) ⋙
        SheafOfModules.forget.{w}
          (Stacks.commRingSheafToRingSheaf (commRingRestriction J K v O)) := rfl

/-- The objectwise tensor product commutes with restriction. This is
`Stacks.DenseSubsiteModules.presheafRestrict_comp_tensorRight` at the pinned spelling. -/
theorem tensorRight_comp_presheafCommRingRestrict (O : Sheaf K CommRingCat.{w})
    (N : SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)) :
    Stacks.tensorRight (O := O.obj) N.val ⋙ presheafCommRingRestrict J K v O =
      presheafCommRingRestrict J K v O ⋙
        Stacks.tensorRight (O := (commRingRestriction J K v O).obj)
          ((presheafCommRingRestrict J K v O).obj N.val) := rfl

/-- The presheaf of modules underlying the restriction of a sheaf of modules is the restriction
of the underlying presheaf of modules. -/
theorem presheafCommRingRestrict_obj_val (O : Sheaf K CommRingCat.{w})
    (N : SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)) :
    (presheafCommRingRestrict J K v O).obj N.val =
      ((moduleRestriction.{w} J K v (Stacks.commRingSheafToRingSheaf O)).obj N).val := rfl

/-- **The presheaf-level half of the comparison**: forget, tensor on the right with `N`, then
restrict along `v` is restrict, forget, then tensor on the right with the restriction of `N`.

Both sides are the same functor, and `rfl` nevertheless does not prove this: the three steps it
is assembled from are each a cheap `rfl` and their composite is not. See the module
implementation notes. -/
theorem forget_tensorRight_comp_presheafCommRingRestrict (O : Sheaf K CommRingCat.{w})
    (N : SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)) :
    (SheafOfModules.forget.{w} (Stacks.commRingSheafToRingSheaf O) ⋙
        Stacks.tensorRight (O := O.obj) N.val) ⋙ presheafCommRingRestrict J K v O =
      (moduleRestriction.{w} J K v (Stacks.commRingSheafToRingSheaf O) ⋙
          SheafOfModules.forget.{w}
            (Stacks.commRingSheafToRingSheaf (commRingRestriction J K v O))) ⋙
        Stacks.tensorRight (O := (commRingRestriction J K v O).obj)
          ((moduleRestriction.{w} J K v (Stacks.commRingSheafToRingSheaf O)).obj N).val := by
  rw [← presheafCommRingRestrict_obj_val, ← forget_comp_presheafCommRingRestrict]
  exact congrArg (fun F ↦ SheafOfModules.forget.{w} (Stacks.commRingSheafToRingSheaf O) ⋙ F)
    (tensorRight_comp_presheafCommRingRestrict J K v O N)

variable [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The tensor product `(Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj N` on the big
site, unfolded into its three factors and reassociated
so that the sheafification factor stands next to `moduleRestriction`. -/
theorem sheafTensorRight_comp_moduleRestriction_eq (O : Sheaf K CommRingCat.{w})
    (N : SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u₂, v₂, w, w, w} O).flip.obj N ⋙
        moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O) =
      (SheafOfModules.forget.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
        (show PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj ⥤
            PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj from
          (PresheafOfModules.tensorBifunctor.{v₂, u₂, w, w, w} O.obj).flip.obj N.val)) ⋙
        (PresheafOfModules.sheafification.{w}
            (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
            (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) ⋙
          moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O)) := rfl

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The tensor product `Stacks.SheafOfModules.Tensor.sheafTensor` on the subsite, precomposed
with `moduleRestriction` and unfolded
into its three factors. -/
theorem moduleRestriction_comp_sheafTensorRight_eq
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (O : Sheaf K CommRingCat.{w})
    (N : SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)) :
    ((moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
        SheafOfModules.forget.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf (commRingRestriction J K v O))) ⋙
      (show PresheafOfModules.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf (commRingRestriction J K v O)).obj ⥤
          PresheafOfModules.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf (commRingRestriction J K v O)).obj from
        (PresheafOfModules.tensorBifunctor.{v₁, u₁, w, w, w}
          (commRingRestriction J K v O).obj).flip.obj
            ((moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj N).val)) ⋙
      PresheafOfModules.sheafification.{w}
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf (commRingRestriction J K v O)).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (commRingRestriction J K v O))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (commRingRestriction J K v O)).obj) =
      moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u₁, v₁, w, w, w}
          (commRingRestriction J K v O)).flip.obj
            ((moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj N) := rfl

omit [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The right-hand crossing of the comparison, assembled from
`forget_tensorRight_comp_presheafCommRingRestrict` and
`moduleRestriction_comp_sheafTensorRight_eq`. -/
theorem forget_tensorRight_comp_presheafCommRingRestrict_sheafification
    (O : Sheaf K CommRingCat.{w})
    (N : SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)) :
    (SheafOfModules.forget.{w} (Stacks.commRingSheafToRingSheaf O) ⋙
        Stacks.tensorRight (O := O.obj) N.val) ⋙
        (presheafCommRingRestrict J K v O ⋙
          PresheafOfModules.sheafification.{w}
            (R := Stacks.commRingSheafToRingSheaf (commRingRestriction J K v O))
            (𝟙 (Stacks.commRingSheafToRingSheaf (commRingRestriction J K v O)).obj)) =
      moduleRestriction.{w} J K v (Stacks.commRingSheafToRingSheaf O) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u₁, v₁, w, w, w}
            (commRingRestriction J K v O)).flip.obj
          ((moduleRestriction.{w} J K v (Stacks.commRingSheafToRingSheaf O)).obj N)) :=
  (congrArg (fun F ↦ F ⋙ PresheafOfModules.sheafification.{w}
      (R := Stacks.commRingSheafToRingSheaf (commRingRestriction J K v O))
      (𝟙 (Stacks.commRingSheafToRingSheaf (commRingRestriction J K v O)).obj))
    (forget_tensorRight_comp_presheafCommRingRestrict J K v O N)).trans
    (moduleRestriction_comp_sheafTensorRight_eq J K v O N)

/-- **Restriction to a dense subsite commutes with the tensor product of sheaves of modules.**

Tensoring with `N` and then restricting to the subsite is restricting to the subsite and then
tensoring with the restriction of `N`, naturally in the other variable. Together with
`Stacks.DenseSubsiteModules.moduleRestrictionEquivalence` this is Stacks 03DG method (2) for
the tensor product: the tensor product of sheaves of modules depends only on the ringed topos
`(Sh(C'), O)` and not on the site presenting it. -/
noncomputable def moduleRestriction_sheafTensorRight (O : Sheaf K CommRingCat.{w})
    (N : SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u₂, v₂, w, w, w} O).flip.obj N) ⋙
        moduleRestriction.{w} J K v (Stacks.commRingSheafToRingSheaf O) ≅
      moduleRestriction.{w} J K v (Stacks.commRingSheafToRingSheaf O) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u₁, v₁, w, w, w}
            (commRingRestriction J K v O)).flip.obj
          ((moduleRestriction.{w} J K v (Stacks.commRingSheafToRingSheaf O)).obj N)) :=
  eqToIso (sheafTensorRight_comp_moduleRestriction_eq J K v O N) ≪≫
    Functor.isoWhiskerLeft
      (SheafOfModules.forget.{w} (Stacks.commRingSheafToRingSheaf O) ⋙
        Stacks.tensorRight (O := O.obj) N.val)
      (commRingRestriction_sheafification J K v O).symm ≪≫
    eqToIso (forget_tensorRight_comp_presheafCommRingRestrict_sheafification J K v O N)

end DenseSubsite

end Stacks.DenseSubsiteModules

end
