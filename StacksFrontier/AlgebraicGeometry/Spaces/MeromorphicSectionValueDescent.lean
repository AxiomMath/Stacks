module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctionsLocalFraction
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionCanonicalValue
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheafLocal

/-!
# A meromorphic section which is locally an honest section is an honest section

Let `F` be an algebraic space over a scheme `S` of a big fppf site `B` and let `ℒ` be an
*invertible* `𝒪_F`-module.  The canonical map `ℒ ⟶ 𝒦_F(ℒ)` of
`AlgebraicGeometry.Space.toMeromorphicSectionValue` is, over every étale chart, **injective**: a
section of `ℒ` is not killed by being read as a meromorphic section.  Its image is therefore a
*subsheaf* of `𝒦_F(ℒ)` and not merely a subpresheaf, which is to say that lying in `ℒ` is a
local condition on a section of `𝒦_F(ℒ)`:

`s|_{W_i} ∈ ℒ(W_i)` for a covering `{W_i ⟶ V}`  ⟹  `s|_V ∈ ℒ(V)`.

This is the descent statement the first collection of Stacks 0EPS needs — the step that carries
a presentation of a meromorphic section as an honest section, obtained on *some* étale
refinement, back to the chart one wants to read it on.

## Main results

* `Stacks.Sites.exists_eq_of_locally_exists`: the general form.  A family of maps of sections
  natural in the object of a site, injective and out of a sheaf into a sheaf, has an image which
  is a *sheaf* of subsets: a section of the target lying in the image over the members of a
  covering sieve lies in the image.
* `AlgebraicGeometry.Space.injective_toMeromorphicSectionValue`: the canonical map
  `ℒ ⟶ 𝒦_F(ℒ)` is injective on the sections over every étale chart, for `ℒ` invertible.
* `AlgebraicGeometry.Space.exists_toMeromorphicSectionValue_eq_of_sieve`: **lying in `ℒ` is
  local on the small étale site**, for `ℒ` invertible.
* `AlgebraicGeometry.Space.exists_eval_eq_toMeromorphicSectionValue_of_sieve`: the same for the
  value of a global meromorphic section at a chart, which is the shape the proof of Stacks 0EPS
  uses it in.

## Implementation notes

The general statement is not an instance of
`Stacks.SheafOfModules.ImageSubsheaf.exists_app_eq_of_mem_imageSubmodule`, which is the same
argument for a monomorphism of sheaves of modules over one sheaf of rings.  The canonical map
`ℒ ⟶ 𝒦_F(ℒ)` is not such a morphism: its source is a module over `𝒪_F` and its target a module
over `𝒦_F`, and the sections of the two live in different universes — which is exactly why
`AlgebraicGeometry.Space.toMeromorphicSectionValue` is given chart by chart, with naturality as
the explicit lemma `AlgebraicGeometry.Space.toMeromorphicSectionValue_map`.  So the argument is
made once more, at a family of maps of *types* with a naturality hypothesis, where neither the
coefficient rings nor the universes are asked to agree.

Injectivity is local-to-global twice over.  The map factors as `m ↦ 1 ⊗ m` into the presheaf
`ℒ ⊗_{𝒪_F} 𝒦_F` followed by the sheafification map of Stacks 0EN5, and neither factor is
injective on the nose: the second is only *locally* injective
(`AlgebraicGeometry.Space.equalizerSieve_toMeromorphicSectionSheaf_mem`), and the first needs a
free generator of `ℒ`, which exists only on a covering family of the chart
(`AlgebraicGeometry.Space.exists_generator_cover_smul_of_isInvertible`).  Over a chart carrying a
free generator `e` the two sections are `r • e` and `r' • e`, the pure meromorphic sections are
then `r` and `r'` read in `𝒦_F` tensored against `e`, and `𝒪_F(W) ⟶ 𝒦_F(W)` is injective by
`AlgebraicGeometry.Space.injective_toMeromorphicFunctionSheaf` — unconditionally, the regular
functions being a sheaf.  Separatedness of `ℒ` then upgrades the equality on the covering sieve
to an equality over the chart.

Invertibility of `ℒ` is used only for the free generator; the statement is false for a general
`𝒪_F`-module, whose torsion is killed by passing to meromorphic sections.

## References

* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe w₁ w₂ v₁ u₁ u

namespace Stacks.Sites

/-- **A section lying locally in the range of an injective natural family of maps lies in its
range.**  Let `P` and `Q` be presheaves of types on a site, both sheaves, and let `φ` be a
family of maps `P(Y) ⟶ Q(Y)`, natural in `Y` and injective.  A section of `Q` over an object
which lies in the range of `φ` over every member of a covering sieve lies in the range of `φ`.

The local preimages are unique because `φ` is injective, hence form a compatible family, hence
glue by the sheaf condition for `P`; and the glued section has the right image because `Q` is
separated.

Neither the coefficients nor the universes of `P` and `Q` are asked to agree, which is what
makes this applicable to the canonical map from a sheaf of modules to its sheaf of meromorphic
sections. -/
theorem exists_eq_of_locally_exists {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {P : Cᵒᵖ ⥤ Type w₁} {Q : Cᵒᵖ ⥤ Type w₂}
    (hP : Presieve.IsSheaf J P) (hQ : Presieve.IsSheaf J Q)
    (φ : ∀ Y : Cᵒᵖ, P.obj Y → Q.obj Y)
    (hnat : ∀ {V W : C} (g : W ⟶ V) (m : P.obj (op V)),
      φ (op W) (P.map g.op m) = Q.map g.op (φ (op V) m))
    (hinj : ∀ Y : Cᵒᵖ, Function.Injective (φ Y))
    {X : C} (T : Sieve X) (hT : T ∈ J X) (x : Q.obj (op X))
    (hloc : ∀ ⦃Y : C⦄ (g : Y ⟶ X), T g → ∃ m : P.obj (op Y), φ (op Y) m = Q.map g.op x) :
    ∃ m : P.obj (op X), φ (op X) m = x := by
  classical
  let fam : Presieve.FamilyOfElements P (T : Presieve X) := fun _ g hg => (hloc g hg).choose
  have hfam : ∀ ⦃Y : C⦄ (g : Y ⟶ X) (hg : T.arrows g),
      φ (op Y) (fam g hg) = Q.map g.op x := fun _ g hg => (hloc g hg).choose_spec
  have hcomp : fam.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Y Z g h hg
    refine hinj (op Z) ?_
    rw [hfam (h ≫ g) (T.downward_closed hg h), hnat h (fam g hg), hfam g hg]
    exact Functor.map_comp_apply Q g.op h.op x
  obtain ⟨m, hm, -⟩ := hP T hT fam hcomp
  refine ⟨m, (hQ T hT).isSeparatedFor.ext fun {Y} g hg => ?_⟩
  rw [← hnat g m, show P.map g.op m = fam g hg from hm g hg, hfam g hg]

end Stacks.Sites

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-- The presheaf of types underlying an `𝒪_F`-module is a sheaf for the small étale topology.
This is `Stacks.SheafOfModules.isSheaf_forget` at the topology of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, which is the small étale topology but is a
projection of a structure instance and so is not seen through by unification. -/
theorem isSheaf_forget_modules (M : Modules.{u, u} B S hS X.1 X.2) :
    Presieve.IsSheaf (SmallEtale.topology B S hS X.1)
      (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}) :=
  Stacks.SheafOfModules.isSheaf_forget M

/-- **Two sections of an `𝒪_F`-module which agree on a covering sieve of a chart are equal.**
Separatedness of the presheaf of types underlying the module. -/
theorem eq_of_modules_map_eq_of_sieve (M : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1) (T : Sieve V)
    (hT : T ∈ SmallEtale.topology B S hS X.1 V) (m m' : M.val.obj (op V))
    (h : ∀ ⦃W : SmallEtale B S hS X.1⦄ (k : W ⟶ V), T k →
      (M.val.map k.op).hom m = (M.val.map k.op).hom m') :
    m = m' :=
  (isSheaf_forget_modules B S hS X M T hT).isSeparatedFor.ext fun {_} k hk => h k hk

/-- **The canonical map `ℒ ⟶ 𝒦_F(ℒ)` of an invertible module is injective over every chart.**
A section of an invertible `𝒪_F`-module over an étale chart is not killed by being read as a
meromorphic section of it.

Both halves of the map — the unit `m ↦ 1 ⊗ m` of the extension of scalars and the sheafification
map of Stacks 0EN5 — are injective only locally, so the comparison is made on a covering sieve
of the chart over whose members a free generator `e` of `ℒ` is available: there the two sections
are `r • e` and `r' • e`, their pure meromorphic sections are the images of `r` and `r'` in
`𝒦_F` tensored against `e`, and `𝒪_F(W) ⟶ 𝒦_F(W)` is injective.  Separatedness of `ℒ` carries
the resulting equality on the sieve back to the chart. -/
theorem injective_toMeromorphicSectionValue (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (V : SmallEtale B S hS X.1) :
    Function.Injective (toMeromorphicSectionValue B S hS X.1 X.2 L V) := by
  intro m m' hmm
  obtain ⟨I, Vi, a, hcov, hfree⟩ := exists_generator_cover_smul_of_isInvertible B S hS X L hL V
  have hE := equalizerSieve_toMeromorphicSectionSheaf_mem B S hS X.1 X.2 L V
    (pureMeromorphicSection B S hS X.1 X.2 L V m)
    (pureMeromorphicSection B S hS X.1 X.2 L V m') hmm
  refine eq_of_modules_map_eq_of_sieve B S hS X L V
    (Presheaf.equalizerSieve (F := meromorphicSectionModuleUp B S hS X.1 X.2 L)
        (ULift.up (pureMeromorphicSection B S hS X.1 X.2 L V m))
        (ULift.up (pureMeromorphicSection B S hS X.1 X.2 L V m')) ⊓ Sieve.ofArrows Vi a)
    ((SmallEtale.topology B S hS X.1).intersection_covering hE hcov) m m' ?_
  intro W k hk
  obtain ⟨i, b, rfl⟩ := (Sieve.mem_ofArrows_iff Vi a k).1 hk.2
  obtain ⟨e, -, hbij⟩ := hfree i
  have key : ∀ n : L.val.obj (op V), ∃ r : chartRing B S hS X.1 X.2 W,
      (L.val.map (b ≫ a i).op).hom n = r • e W b ∧
      ((meromorphicSectionModule B S hS X.1 X.2 L).map (b ≫ a i).op).hom
        (pureMeromorphicSection B S hS X.1 X.2 L V n) =
      pureMeromorphicSection B S hS X.1 X.2 L W (r • e W b) := fun n ↦ by
    obtain ⟨r, hr⟩ := (hbij W b).2 ((L.val.map (b ≫ a i).op).hom n)
    exact ⟨r, hr.symm, by
      rw [pureMeromorphicSection_map B S hS X.1 X.2 L V W (b ≫ a i) n, ← hr]⟩
  obtain ⟨r, hr, hr1⟩ := key m
  obtain ⟨r', hr', hr1'⟩ := key m'
  have h1 := (hr1.symm.trans (congrArg ULift.down hk.1)).trans hr1'
  rw [pureMeromorphicSection_smul_eq_algebraMap_tmul B S hS X.1 X.2 L W r (e W b),
    pureMeromorphicSection_smul_eq_algebraMap_tmul B S hS X.1 X.2 L W r' (e W b)] at h1
  rw [hr, hr', injective_toMeromorphicFunctionSheaf B S hS X.1 X.2 W
    ((bijective_meromorphicSectionModule_tmul B S hS X.1 X.2 L W (e W b) (hbij W b)).1 h1)]

/-- The presheaf of types underlying the sheaf `𝒦_F(M)` of meromorphic sections of Stacks 0EN5
is a sheaf for the small étale topology.  As for
`AlgebraicGeometry.Space.isSheaf_forget_modules`, the topology of
`AlgebraicGeometry.Space.meromorphicRingedSite` is the small étale topology but is a projection
of a structure instance. -/
theorem isSheaf_forget_meromorphicSectionSheaf (M : Modules.{u, u} B S hS X.1 X.2) :
    Presieve.IsSheaf (SmallEtale.topology B S hS X.1)
      ((meromorphicSectionSheaf.{u, u} B S hS X.1 X.2 M).val.presheaf ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  Stacks.SheafOfModules.isSheaf_forget _

/-- **Lying in an invertible module is a local condition on a meromorphic section of it.**  A
section of the sheaf `𝒦_F(ℒ)` of meromorphic sections of Stacks 0EN5 over an étale chart which,
over each member of a covering sieve of that chart, is the image under
`AlgebraicGeometry.Space.toMeromorphicSectionValue` of a section of `ℒ` is itself the image of a
section of `ℒ` over the chart.

This is `Stacks.Sites.exists_eq_of_locally_exists` at the canonical map `ℒ ⟶ 𝒦_F(ℒ)`, whose
three hypotheses are: the sheaf condition for `ℒ` and for `𝒦_F(ℒ)`, naturality in the chart
(`AlgebraicGeometry.Space.toMeromorphicSectionValue_map`), and injectivity over every chart
(`AlgebraicGeometry.Space.injective_toMeromorphicSectionValue`), which is where invertibility of
`ℒ` is used. -/
theorem exists_toMeromorphicSectionValue_eq_of_sieve (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (V : SmallEtale B S hS X.1)
    (x : (meromorphicSectionSheaf.{u, u} B S hS X.1 X.2 L).val.obj (op V))
    (T : Sieve V) (hT : T ∈ SmallEtale.topology B S hS X.1 V)
    (hloc : ∀ ⦃W : SmallEtale B S hS X.1⦄ (k : W ⟶ V), T k →
      ∃ e : L.val.obj (op W), toMeromorphicSectionValue B S hS X.1 X.2 L W e =
        ((meromorphicSectionSheaf.{u, u} B S hS X.1 X.2 L).val.map k.op).hom x) :
    ∃ e : L.val.obj (op V), toMeromorphicSectionValue B S hS X.1 X.2 L V e = x :=
  Stacks.Sites.exists_eq_of_locally_exists (isSheaf_forget_modules B S hS X L)
    (isSheaf_forget_meromorphicSectionSheaf B S hS X L)
    (fun Y m ↦ toMeromorphicSectionValue B S hS X.1 X.2 L Y.unop m)
    (fun {V' W'} g m ↦ (toMeromorphicSectionValue_map B S hS X.1 X.2 L V' W' g m).symm)
    (fun Y ↦ injective_toMeromorphicSectionValue B S hS X L hL Y.unop) T hT x hloc

/-- **A meromorphic section of an invertible module which is an honest section on a covering
sieve of a chart is an honest section over that chart.**  This is
`AlgebraicGeometry.Space.exists_toMeromorphicSectionValue_eq_of_sieve` at the value of a global
meromorphic section, whose values over the charts of a sieve are the restrictions of its value
over the base of the sieve.

It is the step the proof of Stacks 0EPS needs: the presentation of a regular meromorphic section
as an honest section of `ℒ` is obtained on an étale refinement, and what the germ at a
codimension-one point reads is the value over a chart the refinement need not factor
through. -/
theorem exists_eval_eq_toMeromorphicSectionValue_of_sieve (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (s : MeromorphicSection.{u, u} B S hS X.1 X.2 L)
    (V : SmallEtale B S hS X.1) (T : Sieve V)
    (hT : T ∈ SmallEtale.topology B S hS X.1 V)
    (hloc : ∀ ⦃W : SmallEtale B S hS X.1⦄ (k : W ⟶ V), T k →
      ∃ e : L.val.obj (op W),
        s.eval (op W) = toMeromorphicSectionValue B S hS X.1 X.2 L W e) :
    ∃ e : L.val.obj (op V),
      s.eval (op V) = toMeromorphicSectionValue B S hS X.1 X.2 L V e := by
  have hstep : ∀ ⦃W : SmallEtale B S hS X.1⦄ (k : W ⟶ V), T k →
      ∃ e : L.val.obj (op W), toMeromorphicSectionValue B S hS X.1 X.2 L W e =
        ((meromorphicSectionSheaf.{u, u} B S hS X.1 X.2 L).val.map k.op).hom
          (s.eval (op V)) := by
    intro W k hk
    obtain ⟨e', he'⟩ := hloc k hk
    exact ⟨e', he'.symm.trans (PresheafOfModules.sections_property
      (M := (meromorphicSectionSheaf.{u, u} B S hS X.1 X.2 L).val) s k.op).symm⟩
  exact (exists_toMeromorphicSectionValue_eq_of_sieve B S hS X L hL V
    (s.eval (op V)) T hT hstep).imp fun _ ↦ Eq.symm

end AlgebraicGeometry.Space

end
