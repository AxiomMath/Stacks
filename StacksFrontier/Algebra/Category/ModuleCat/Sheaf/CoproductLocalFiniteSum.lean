module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoproductSheafification

/-!
# A section of a coproduct of sheaves of modules is locally a finite sum

Let `R : Sheaf J RingCat` be a sheaf of rings on a site and `M : I → SheafOfModules R` a family
of sheaves of modules. A coproduct of sheaves of modules is **not** computed objectwise, so a
section of `∐ M` over an object `V` need not be a finite sum of sections of the summands. On a
covering sieve of `V` it is:

`s|_W = ∑ i ∈ S, ι_i (y i)` with `S` a finite set of indices and `y i` a section of `M i`
over `W`.

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoproductSheafification` proves the weaker
statement that all but finitely many *components* of `s` vanish on a covering sieve
(`Stacks.SheafOfModules.CoproductSheafification.exists_finset_eq_zero_of_ι`). That is enough for
a vanishing argument — it is what the local boundedness of Stacks 0FPA uses — but not enough to
*produce* sections of the summands, which is what a factorization argument needs. The two
statements have the same proof up to the last step: the objectwise coproduct of the underlying
presheaves of modules receives a section locally
(`Stacks.SheafOfModules.CoproductSheafification.imageSieve_toCoprod_mem`), and a point of the
vertex of a colimiting cofan of modules is a finite sum of images of the inclusions, not merely
one killed by all but finitely many components.

This is the step of the proof of Stacks 0FPD, conclusion (a), at which the source's sections
`fᵢ` and `gᵢ` of `η(1) = ∑ fᵢ ⊗ gᵢ` are produced: the coevaluation lands in degree zero of a
total tensor complex, which is a coproduct `⊕_{p + q = 0} M^p ⊗ N^q` over `{p : ℤ × ℤ // p.1 +
p.2 = 0}`, and the summands are then opened up into elementary tensors by
`Stacks.SheafOfModules.TensorUnit.exists_nhd_sum_monoidalTensorSection`. Nothing below is a
clause of a tag; no `@[stacks …]` attribute is attached.

## Main results

* `Stacks.SheafOfModules.CoproductSheafification.exists_finset_sum_inj_of_isColimit`: **a point
  of the vertex of a colimiting cofan of modules is a finite sum of images of the inclusions.**
* `Stacks.SheafOfModules.CoproductSheafification.exists_sieve_sum_ι`: **a section of `∐ M` over
  `V` is, on a covering sieve of `V`, a finite sum of sections of the summands.**
* `Stacks.SheafOfModules.CoproductSheafification.exists_sieve_sum_inj_of_isColimit`: the same
  for a coproduct presented by an arbitrary colimiting cofan, which is how the fibres of a graded
  tensor product are presented (`CategoryTheory.GradedObject.isColimitCofanMapObj`).

## Implementation notes

The index type is fixed at `Type 0`, as it is in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoproductSheafification`, and for the same reason:
the finiteness runs through `⨁ i, Z i`, whose carrier lives in `Type (max v u')` for an index
type in `Type v`, and the inversion of `max` that a polymorphic shape would require is not
something Lean will do. The graded consumers have index types in `Type 0` — the fibres of a
`ℤ`-graded tensor product are indexed by `{p : ℤ × ℤ // p.1 + p.2 = n}` — so nothing is lost.

The family `y` is total rather than defined on `S` only: a function `I → M i` restricted to the
finite set is what `Finset.sum` consumes, and a total family is cheaper to supply and to use
than a dependent one. Its values off `S` are unconstrained and the statement says nothing about
them, which is correct — a section of the coproduct determines its components, but the finite
set `S` of a *presentation* is not unique.

## References

* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
* [Stacks Project, Tag 0FPA](https://stacks.math.columbia.edu/tag/0FPA)
-/

@[expose] public section

open CategoryTheory Limits Opposite DirectSum

namespace Stacks.SheafOfModules.CoproductSheafification

universe v u u'

/-! ### Modules -/

section ModuleCat

variable {A : Type u} [Ring A] {I : Type v} {Z : I → ModuleCat.{max v u'} A}

/-- **A point of the vertex of a colimiting cofan of modules is a finite sum of images of the
inclusions.** There is a finite set `S` of indices and a family `y` of points of the summands
with `t = ∑ i ∈ S, c.inj i (y i)`.

The cofan is compared with the direct sum, as in
`Stacks.SheafOfModules.CoproductSheafification.exists_finset_eq_zero_of_inj`; `S` is the support
of the corresponding element of `⨁ i, Z i` and `y i` its `i`-th coordinate, and the sum is
recovered by `DirectSum.sum_support_of` pushed through the comparison isomorphism. The values of
`y` off `S` are unconstrained. -/
public theorem exists_finset_sum_inj_of_isColimit {c : Cofan Z} (hc : IsColimit c) (t : c.pt) :
    ∃ (S : Finset I) (y : ∀ i : I, Z i), t = ∑ i ∈ S, (c.inj i).hom (y i) := by
  classical
  let e : c.pt ≅ ModuleCat.of A (⨁ i, Z i) :=
    hc.coconePointUniqueUpToIso (ModuleCat.coproductCoconeIsColimit Z)
  have hinj : ∀ j : I, (c.inj j) =
      ModuleCat.ofHom (DirectSum.lof A I (fun i => Z i) j) ≫ e.inv := fun j =>
    (Iso.eq_comp_inv e).2
      (hc.comp_coconePointUniqueUpToIso_hom (ModuleCat.coproductCoconeIsColimit Z) ⟨j⟩)
  have ht : t = e.inv.hom (e.hom.hom t) := by
    simp
  set w := e.hom.hom t
  have hstep : ∀ i : I, (c.inj i).hom (w i) =
      e.inv.hom ((DirectSum.of (fun k => (Z k : Type _)) i) (w i)) := by
    intro i
    rw [hinj i]
    rfl
  refine ⟨w.support, fun i => w i, ?_⟩
  calc t = e.inv.hom w := ht
    _ = e.inv.hom (∑ i ∈ w.support, (DirectSum.of (fun k => (Z k : Type _)) i) (w i)) := by
          rw [DirectSum.sum_support_of]
    _ = ∑ i ∈ w.support, e.inv.hom ((DirectSum.of (fun k => (Z k : Type _)) i) (w i)) := by
          rw [map_sum]
    _ = ∑ i ∈ w.support, (c.inj i).hom (w i) :=
          Finset.sum_congr rfl fun i _ => (hstep i).symm

end ModuleCat

/-! ### Sheaves of modules -/

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {I : Type} (M : I → SheafOfModules.{u} R) [HasCoproduct M]

/-- **A section of a coproduct of sheaves of modules is a finite sum of sections of the summands
on a covering sieve.** Given a section `s` of `∐ M` over `V`, there is a covering sieve of `V`
on each member `g : W ⟶ V` of which the restriction of `s` is `∑ i ∈ S, ι_i (y i)` for a finite
set `S` of indices and sections `y i` of `M i` over `W`.

The covering sieve is the one along which `s` comes from the coproduct of the underlying
presheaves of modules, which is objectwise —
`Stacks.SheafOfModules.CoproductSheafification.imageSieve_toCoprod_mem` — and the finite sum is
then read off the objectwise coproduct by
`Stacks.SheafOfModules.CoproductSheafification.exists_finset_sum_inj_of_isColimit`, the
evaluation of presheaves of modules at `W` preserving coproducts. The identification of the
inclusion of the objectwise coproduct followed by the comparison with the inclusion into `∐ M`
is `Stacks.SheafOfModules.CoproductSheafification.ι_toCoprod`.

Both the finite set and the sections depend on the member of the covering, not on `s` alone;
this is the sense in which a coproduct of sheaves of modules is objectwise *after
localization*. -/
public theorem exists_sieve_sum_ι {V : C}
    (s : ToType (((PresheafOfModules.toPresheaf R.obj).obj (∐ M).val).obj (op V))) :
    ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (g : W ⟶ V), T g →
      ∃ (S : Finset I)
        (y : ∀ i : I,
          ToType (((PresheafOfModules.toPresheaf R.obj).obj (M i).val).obj (op W))),
        (((PresheafOfModules.toPresheaf R.obj).obj (∐ M).val).map g.op) s =
          ∑ i ∈ S,
            ((PresheafOfModules.toPresheaf R.obj).map (Sigma.ι M i).val).app (op W) (y i) := by
  classical
  refine ⟨_, imageSieve_toCoprod_mem R M s, fun {W} g hg => ?_⟩
  obtain ⟨t, ht⟩ := hg
  obtain ⟨S, y, hy⟩ := exists_finset_sum_inj_of_isColimit
    (isColimitOfHasCoproductOfPreservesColimit
      (PresheafOfModules.evaluation R.obj (op W)) (fun i => (M i).val))
    (t : ((presCoprod R M).obj (op W) : ModuleCat _))
  refine ⟨S, y, ?_⟩
  rw [← ht]
  have hsum : (t : ((presCoprod R M).obj (op W) : ModuleCat _)) =
      ∑ i ∈ S, ((Sigma.ι (fun k => (M k).val) i).app (op W)).hom (y i) := hy
  rw [show ((PresheafOfModules.toPresheaf R.obj).map (toCoprod R M)).app (op W) t =
      ((toCoprod R M).app (op W)).hom (t : ((presCoprod R M).obj (op W) : ModuleCat _)) from rfl,
    hsum, map_sum]
  exact Finset.sum_congr rfl fun i _ =>
    congrArg (fun f : (M i).val.obj (op W) ⟶ (∐ M).val.obj (op W) => f.hom (y i))
      (congrArg (fun f : (M i).val ⟶ (∐ M).val => f.app (op W)) (ι_toCoprod R M i))

/-! ### An arbitrary colimiting cofan -/

/-- **A section of the vertex of a colimiting cofan of sheaves of modules is a finite sum of
sections of the summands on a covering sieve.** This is
`Stacks.SheafOfModules.CoproductSheafification.exists_sieve_sum_ι` transported along the
comparison of the cofan with `∐ M`, so that a consumer presenting a coproduct by a colimiting
cofan — as the fibres of a graded tensor product are presented by
`CategoryTheory.GradedObject.isColimitCofanMapObj` — can use it without first identifying its
vertex with `∐ M`. -/
public theorem exists_sieve_sum_inj_of_isColimit {c : Cofan M} (hc : IsColimit c) {V : C}
    (s : ToType (((PresheafOfModules.toPresheaf R.obj).obj c.pt.val).obj (op V))) :
    ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (g : W ⟶ V), T g →
      ∃ (S : Finset I)
        (y : ∀ i : I,
          ToType (((PresheafOfModules.toPresheaf R.obj).obj (M i).val).obj (op W))),
        (((PresheafOfModules.toPresheaf R.obj).obj c.pt.val).map g.op) s =
          ∑ i ∈ S,
            ((PresheafOfModules.toPresheaf R.obj).map (c.inj i).val).app (op W) (y i) := by
  classical
  let e : (∐ M) ≅ c.pt := (coproductIsCoproduct M).coconePointUniqueUpToIso hc
  have hι : ∀ i : I, Sigma.ι M i ≫ e.hom = c.inj i := fun i =>
    (coproductIsCoproduct M).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩
  obtain ⟨T, hT, hsum⟩ := exists_sieve_sum_ι R M
    (((PresheafOfModules.toPresheaf R.obj).map e.inv.val).app (op V) s)
  refine ⟨T, hT, fun {W} g hg => ?_⟩
  obtain ⟨S, y, hy⟩ := hsum g hg
  refine ⟨S, y, ?_⟩
  have hnat := congrArg (fun z => ((PresheafOfModules.toPresheaf R.obj).map e.hom.val).app
    (op W) z) hy
  simp only [map_sum] at hnat
  have hcancel : ((PresheafOfModules.toPresheaf R.obj).map e.hom.val).app (op V)
      (((PresheafOfModules.toPresheaf R.obj).map e.inv.val).app (op V) s) = s := by
    have hid : e.inv.val ≫ e.hom.val = 𝟙 _ := congrArg SheafOfModules.Hom.val e.inv_hom_id
    rw [← CategoryTheory.comp_apply, ← NatTrans.comp_app, ← Functor.map_comp, hid,
      CategoryTheory.Functor.map_id, NatTrans.id_app, CategoryTheory.id_apply]
  have hnatur : ((PresheafOfModules.toPresheaf R.obj).map e.hom.val).app (op W)
        ((((PresheafOfModules.toPresheaf R.obj).obj (∐ M).val).map g.op)
          (((PresheafOfModules.toPresheaf R.obj).map e.inv.val).app (op V) s)) =
      (((PresheafOfModules.toPresheaf R.obj).obj c.pt.val).map g.op) s := by
    have h := ConcreteCategory.congr_hom
      (((PresheafOfModules.toPresheaf R.obj).map e.hom.val).naturality g.op)
      (((PresheafOfModules.toPresheaf R.obj).map e.inv.val).app (op V) s)
    simp only [CategoryTheory.comp_apply] at h
    rw [h, hcancel]
  exact hnatur.symm.trans (hnat.trans (Finset.sum_congr rfl fun i _ =>
    congrArg (fun f : (M i).val ⟶ c.pt.val =>
        ((PresheafOfModules.toPresheaf R.obj).map f).app (op W) (y i))
      (congrArg SheafOfModules.Hom.val (hι i))))

end Stacks.SheafOfModules.CoproductSheafification

end
