module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceScalarRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackPresentationData
public import StacksFrontier.CategoryTheory.Sites.Topos.JointlyLocallyInhabited

/-!
# A finite presentation gives presentation data on sections, jointly locally everywhere

Mathlib states that a sheaf of modules `F` on a ringed site is *of finite presentation*
(`SheafOfModules.IsFinitePresentation`) by a `SheafOfModules.QuasicoherentData`: a family of
objects `X i` covering the terminal object together with, for each `i`, a
`SheafOfModules.Presentation` of `F.over (X i)` whose generators and relations are finite.  A
presentation in that sense is a pair of *generating families of global sections* of two sheaves
of modules on the slice site — of `F.over (X i)` and of the kernel of the induced map out of a
finite free sheaf — and neither family is a tuple of sections of the structure sheaf.

Stacks 03DL(7) states the same condition directly on sections: locally there are `n` sections
`s` of `F` and `m` tuples `t` of `n` sections of `O` such that each `t j` is a relation among
the `s`, the `s` generate `F` locally, and every relation among the `s` is locally an
`O`-combination of the `t j`.  That is the predicate
`Stacks.Sheaves.LocalGeneration.IsPresentationData`, and the sheaf of such data is
`Stacks.Sheaves.LocalGeneration.presDataSheaf`.

This file crosses from the first description to the second.  Its main result,
`Stacks.Sheaves.LocalGeneration.jointlyLocallyInhabited_presDataSheaf`, says that the family
`presDataSheaf F n m` indexed by `(n, m) : ℕ × ℕ` is jointly locally inhabited
(`Stacks.Topos.JointlyLocallyInhabited`): every object of the site is covered by objects
carrying a section of *some* member of the family.  The index type has to be `ℕ × ℕ` and the
statement has to be the joint one, because `QuasicoherentData.I` is arbitrary and the sizes of
the presentations vary over the covering family; this is why the conclusion is phrased through
`JointlyLocallyInhabited`, which needs no coproduct over `ℕ × ℕ`.

## Main results

* `Stacks.SheafOfModules.coordsOver_sum`: taking coordinates in the base commutes with finite
  sums, the companion of `Stacks.SheafOfModules.coordsOver_add` and
  `Stacks.SheafOfModules.coordsOver_smul`.
* `Stacks.Sheaves.LocalGeneration.exists_isPresentationData_of_presentation`: **a finite
  `SheafOfModules.Presentation` of `F.over W` yields presentation data for `F` over `W` on
  sections**, with `n` the number of generators and `m` the number of relations.
* `Stacks.Sheaves.LocalGeneration.jointlyLocallyInhabited_presDataSheaf`: **if `F` is of finite
  presentation then the family of data sheaves is jointly locally inhabited.**

## Implementation notes

**No sections description of a free sheaf of modules is needed, and none is used in the shape
one might expect.** The generating sections of the presentation are carried to the section
condition by `Stacks.Sheaves.LocalGeneration.locallySpans_of_generatingSections_over`.
For the relations the main step is reading an abstract section of
`SheafOfModules.free I` as a tuple of coefficients; that is exactly what the coordinate layer
`Stacks.SheafOfModules.coordsOver` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover` provides for a *finite* index
type, with its scalars already spelled in the base, which is the spelling
`IsPresentationData` needs.  The relation matrix `t` is therefore an honest tuple over `W`
itself, with no covering sieve required to produce it, and condition (A) is then one application
of `kernel.condition`.

**Where the covering sieve of condition (C) comes from.** A relation among the restricted
generators over an object `V → W` is turned into a section of `free I` by
`Stacks.SheafOfModules.ofCoordsOver`, is killed by the presentation's epimorphism, and so lifts
to a section of its kernel by `Stacks.SheafOfModules.exists_kernel_section`.  The relations of
the presentation generate that kernel, so
`Stacks.Sheaves.LocalGeneration.generatingSections_locally_span` produces a covering sieve of
`V` *in the slice topology* on which the lift is a combination of them; `Sieve.overEquiv` and
`GrothendieckTopology.mem_over_iff` carry that sieve to the base, and `coordsOver`, being
additive, linear and compatible with restriction, turns the combination of kernel sections into
the required combination of coefficient tuples.

**`HasSheafify` is not a hypothesis.**  `SheafOfModules.exists_kernel_section` is stated with
`HasSheafify (J.over W) AddCommGrpCat`, which
`AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective` derives from the
`HasWeakSheafify` and `WEqualsLocallyBijective` that `SheafOfModules.Presentation` already
assumes.  That is a theorem and not an instance, so it is supplied by a local `let`; the
`kernel` of the presentation's epimorphism is unaffected, since the abelian structure of
`SheafOfModules` comes from the weak hypotheses either way.

**The slice hypotheses are per-object where possible.**
`exists_isPresentationData_of_presentation` asks for `HasWeakSheafify (J.over W)` and
`(J.over W).WEqualsLocallyBijective` at the single object `W` it is about, following
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover`; the `∀ X` form is needed only by
the main theorem, where `SheafOfModules.QuasicoherentData` demands it.

## References

* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01BD](https://stacks.math.columbia.edu/tag/01BD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open Stacks.SheafOfModules

universe v u w

namespace Stacks.SheafOfModules

/-- **Taking coordinates in the base commutes with finite sums.** The companion of
`Stacks.SheafOfModules.coordsOver_add` and `Stacks.SheafOfModules.coordsOver_smul`. -/
lemma coordsOver_sum {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {U : C} [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}] {ι : Type w} [DecidableEq ι]
    {κ : Type*} (V : Over U) (T : Finset κ)
    (e : κ → ToType ((free (R := R.over U) ι).val.obj (op V))) (i : ι) :
    coordsOver V (∑ j ∈ T, e j) i = ∑ j ∈ T, coordsOver V (e j) i :=
  map_sum ((freeProj (S := R.over U) i).val.app (op V)).hom e T

end Stacks.SheafOfModules

namespace Stacks.Sheaves.LocalGeneration

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **A finite presentation of `F.over W` is presentation data for `F` over `W` on sections.**
The generators are the generating sections of the presentation read over `W`, and the `j`-th
relation tuple is the coordinate tuple of the `j`-th relation, a section of the kernel of the
presentation's epimorphism pushed into the finite free sheaf of modules on the generators. -/
theorem exists_isPresentationData_of_presentation (M : SheafOfModules.{w} R) (W : C)
    [HasWeakSheafify (J.over W) AddCommGrpCat.{w}]
    [(J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (p : (M.over W).Presentation) [p.IsFinite] :
    ∃ (n m : ℕ) (s : Fin n → M.val.obj (op W)) (t : Fin m → Fin n → R.obj.obj (op W)),
      IsPresentationData M s t := by
  classical
  let _ : HasSheafify (J.over W) AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let _ : Fintype p.generators.I := Fintype.ofFinite _
  let _ : Fintype p.relations.I := Fintype.ofFinite _
  set π := p.generators.π with hπdef
  let gens : p.generators.I → ToType (M.val.obj (op W)) :=
    fun k => (p.generators.s k).eval (op (Over.mk (𝟙 W)))
  have hπ : π = freeToOver M gens := freeHomEquiv_symm_eq_freeToOver M p.generators.s
  have hcoord : ∀ (V : Over W) (e : ToType ((free (R := R.over W) p.generators.I).val.obj (op V))),
      π.val.app (op V) e = ∑ k : p.generators.I, coordsOver V e k • res M V.hom (gens k) := by
    intro V e
    rw [hπ]
    exact app_freeToOver_eq_sum_smul_coordsOver M gens V e
  let relsec : p.relations.I → ToType ((kernel π).val.obj (op (Over.mk (𝟙 W)))) :=
    fun l => (p.relations.s l).val (op (Over.mk (𝟙 W)))
  let tmat : p.relations.I → p.generators.I → ToType (R.obj.obj (op W)) :=
    fun l k => coordsOver (Over.mk (𝟙 W))
      ((kernel.ι π).val.app (op (Over.mk (𝟙 W))) (relsec l)) k
  have hA : ∀ l : p.relations.I, (∑ k : p.generators.I, tmat l k • gens k) = 0 := by
    intro l
    have h0 : π.val.app (op (Over.mk (𝟙 W)))
        ((kernel.ι π).val.app (op (Over.mk (𝟙 W))) (relsec l)) = 0 :=
      (congrArg (fun φ : kernel π ⟶ M.over W => φ.val.app (op (Over.mk (𝟙 W))) (relsec l))
        (kernel.condition π)).trans (zero_app_apply _ _)
    rw [hcoord (Over.mk (𝟙 W)) ((kernel.ι π).val.app (op (Over.mk (𝟙 W))) (relsec l))] at h0
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h0
    exact congrArg (fun y => tmat l k • y) (res_id M (gens k)).symm
  set n := Fintype.card p.generators.I with hn
  set m := Fintype.card p.relations.I with hm
  let eg : p.generators.I ≃ Fin n := Fintype.equivFin _
  let er : p.relations.I ≃ Fin m := Fintype.equivFin _
  refine ⟨n, m, fun i => gens (eg.symm i), fun j i => tmat (er.symm j) (eg.symm i),
    fun j => ?_, locallySpans_of_generatingSections_over M p.generators n eg, ?_⟩
  · rw [combinationValue]
    exact (Fintype.sum_equiv eg.symm _ _ fun i => rfl).trans (hA (er.symm j))
  · intro V f a ha
    have ha' : (∑ i : Fin n, a i • restr M f.op (gens (eg.symm i))) = 0 := ha
    have hz : (∑ k : p.generators.I, a (eg k) • res M f (gens k)) = 0 :=
      (Fintype.sum_equiv eg _ _ fun k => by
        simp only [Equiv.symm_apply_apply]; rfl).trans ha'
    have h0 : π.val.app (op (Over.mk f))
        (ofCoordsOver (Over.mk f) (fun k => a (eg k))) = 0 := by
      rw [hcoord (Over.mk f) (ofCoordsOver (Over.mk f) (fun k => a (eg k)))]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hz
      exact congrArg (fun c => c • res M (Over.mk f).hom (gens k))
        (congrFun (coordsOver_ofCoordsOver (Over.mk f) (fun k => a (eg k))) k)
    obtain ⟨wk, hwk⟩ := Stacks.SheafOfModules.exists_kernel_section π (op (Over.mk f)) _ h0
    have hspan := generatingSections_locally_span (kernel π) p.relations m er (Over.mk f) wk
    rw [GrothendieckTopology.mem_over_iff] at hspan
    refine J.superset_covering ?_ hspan
    intro V' g hg
    rw [Sieve.overEquiv_iff] at hg
    obtain ⟨b, hb⟩ := hg
    let bb : Fin m → ToType (R.obj.obj (op V')) := fun j => b j
    refine ⟨bb, fun i => ?_⟩
    have hker : ∀ (X Y : Over W) (h : X ⟶ Y) (w : ToType ((kernel π).val.obj (op Y)))
        (k : p.generators.I),
        coordsOver X ((kernel.ι π).val.app (op X) (restr (kernel π) h.op w)) k
          = resR R h.left (coordsOver Y ((kernel.ι π).val.app (op Y) w) k) := fun X Y h w k =>
      (congrArg (fun z => coordsOver X z k)
        (PresheafOfModules.naturality_apply (kernel.ι π).val h.op w)).trans (coordsOver_map h _ k)
    have hmat : ∀ (l : p.relations.I) (X : Over W) (h : X ⟶ Over.mk f) (k : p.generators.I),
        coordsOver X ((kernel.ι π).val.app (op X)
          (restr (kernel π) h.op ((p.relations.s l).val (op (Over.mk f))))) k
          = resR R h.left (resR R f (tmat l k)) := by
      intro l X h k
      refine (hker _ _ h _ k).trans (congrArg (resR R h.left) ?_)
      rw [← (p.relations.s l).property
        (Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 W)).op]
      exact hker (Over.mk f) (Over.mk (𝟙 W)) (Over.homMk f (by simp)) _ k
    have hR : coordsOver (Over.mk (g ≫ f)) ((kernel.ι π).val.app (op (Over.mk (g ≫ f)))
          (restr (kernel π) (Over.homMk g : Over.mk (g ≫ f) ⟶ Over.mk f).op wk)) (eg.symm i)
        = R.obj.map g.op (a i) := by
      refine (hker (Over.mk (g ≫ f)) (Over.mk f) (Over.homMk g) wk _).trans (congrArg (resR R g) ?_)
      refine Eq.trans (congrArg (fun z => coordsOver (Over.mk f) z (eg.symm i)) hwk) ?_
      exact Eq.trans (congrFun (coordsOver_ofCoordsOver (Over.mk f) (fun k => a (eg k)))
        (eg.symm i)) (congrArg a (eg.apply_symm_apply i))
    have hL : coordsOver (Over.mk (g ≫ f)) ((kernel.ι π).val.app (op (Over.mk (g ≫ f)))
          (combinationValue (kernel π) b (fun j => restr (kernel π)
            (Over.homMk g : Over.mk (g ≫ f) ⟶ Over.mk f).op
            ((p.relations.s (er.symm j)).val (op (Over.mk f)))))) (eg.symm i)
        = ∑ j, bb j * R.obj.map g.op (R.obj.map f.op (tmat (er.symm j) (eg.symm i))) := by
      rw [combinationValue, map_sum, coordsOver_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Eq.trans (congrArg (fun z => coordsOver (Over.mk (g ≫ f)) z (eg.symm i))
        (map_smul ((kernel.ι π).val.app (op (Over.mk (g ≫ f)))).hom (b j) _)) ?_
      refine Eq.trans (coordsOver_smul (Over.mk (g ≫ f)) (bb j) _ (eg.symm i)) ?_
      exact congrArg (fun z => bb j * z)
        (hmat (er.symm j) (Over.mk (g ≫ f)) (Over.homMk g) (eg.symm i))
    exact (hL.symm.trans (congrArg (fun y => coordsOver (Over.mk (g ≫ f))
      ((kernel.ι π).val.app (op (Over.mk (g ≫ f))) y) (eg.symm i)) hb)).trans hR

variable [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **If `F` is of finite presentation then the family of presentation data sheaves is jointly
locally inhabited**: every object of the site is covered by objects over which `F` has, for some
`n` and `m`, a presentation by `n` sections and `m` relation tuples.

The sizes `n` and `m` vary over the covering family supplied by
`SheafOfModules.QuasicoherentData`, which is why the conclusion is the joint statement for the
family indexed by `ℕ × ℕ` rather than local surjectivity of one data sheaf onto the terminal
sheaf; no coproduct over `ℕ × ℕ` is formed. -/
theorem jointlyLocallyInhabited_presDataSheaf (M : SheafOfModules.{w} R)
    [M.IsFinitePresentation] :
    Stacks.Topos.JointlyLocallyInhabited J (fun q : ℕ × ℕ => presDataSheaf M q.1 q.2) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  intro U
  refine J.superset_covering ?_ (q.coversTop U)
  rintro V g ⟨i, ⟨h⟩⟩
  let _ := hq.isFinite_presentation i
  obtain ⟨n, m, s, t, hd⟩ :=
    exists_isPresentationData_of_presentation M (q.X i) (q.presentation i)
  exact ⟨(n, m), ⟨(presDataSheaf M n m).obj.map h.op (presDataMk M hd)⟩⟩

end Stacks.Sheaves.LocalGeneration

end
