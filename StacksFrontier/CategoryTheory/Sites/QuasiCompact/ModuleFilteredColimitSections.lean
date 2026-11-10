module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafSections
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleSections

/-!
# Sections of a filtered colimit of sheaves of modules over a quasi-compact object

Let `R` be a sheaf of rings on a site and let `D : I ⥤ SheafOfModules R` be a filtered diagram
with colimit cocone `c`.  A section of `c.pt` over an arbitrary object need not come from any
stage of the diagram, but it does so locally: the canonical morphism from the coproduct of the
stages to `c.pt` is an epimorphism, hence locally surjective, and over a *quasi-compact* object
of the site a section of that coproduct is a finite sum of sections of single summands, so
filteredness puts it in a single stage.

The file also records two combinatorial facts: a family refining a family
which covers the final object again covers it, and a finite family of sections of a presheaf of
modules which generates it locally still does so after restriction along an arrow of the site.

## Main results

* `Stacks.Sites.exists_covering_stage_of_section`: for every section `x` of `c.pt` over an
  object `Z` there is a covering sieve of `Z` such that over each of its quasi-compact members
  the restriction of `x` is the image of a section of a single stage of the diagram.
* `Stacks.Sites.exists_covering_stage_of_finite_family`: the same for a finite family of
  sections, with a single stage serving all of them.
* `Stacks.Sites.coversTop_of_exists_hom` and `Stacks.Sites.coversTop_bind`: a family which
  every member of a covering family of the final object maps into is again such a family, and
  covering families of the members of such a family compose to one.
* `Stacks.SheafOfModules.generatesLocally_restrict`: local generation by a finite family of
  sections is inherited by the restricted family.

## Implementation notes

The universes of the site, of the index category and of the module sections are independent.
Quasi-compactness enters only through
`Stacks.Sites.sheafOfModules_sections_preserves_coproducts` (Stacks 0935), which is where the
sections of the coproduct of the stages are identified with the direct sum of the sections; the
identification is used in the weak form "the sections of the coproduct are generated, as an
abelian group, by the images of the coproduct injections", which is read off the universal
property of the colimit cofan rather than from a model of the coproduct.

Nothing here assumes that the transition maps of the diagram are monomorphisms.

## References

* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
* [Stacks Project, Tag 0738](https://stacks.math.columbia.edu/tag/0738)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w t vI uI v u

namespace Stacks.Filtered

/-- A finite family of objects of a filtered category admits a common upper bound. -/
lemma exists_hom_of_finite {I : Type uI} [Category.{vI} I] [IsFiltered I] {T : Type w}
    [Finite T] (k : T → I) : ∃ j : I, ∀ t, Nonempty (k t ⟶ j) := by
  classical
  cases nonempty_fintype T
  obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (Finset.univ.image k)
  exact ⟨j, fun t => hj (Finset.mem_image_of_mem k (Finset.mem_univ t))⟩

end Stacks.Filtered

namespace Stacks.Sites

/-- Equal morphisms of sheaves of modules act equally on sections. -/
private lemma app_apply_congr {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{t}} {M N : SheafOfModules.{t} R} {f g : M ⟶ N} (h : f = g) {W : C}
    (x : ToType (M.val.obj (op W))) : f.val.app (op W) x = g.val.app (op W) x := by
  rw [h]

section CoversTop

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A family of objects which every member of a family covering the final object maps into
again covers the final object. -/
lemma coversTop_of_exists_hom {ι ι' : Type*} {X : ι → C} {Y : ι' → C} (hX : J.CoversTop X)
    (h : ∀ i, ∃ i', Nonempty (X i ⟶ Y i')) : J.CoversTop Y := by
  intro Z
  refine J.superset_covering ?_ (hX Z)
  intro Z' g hg
  obtain ⟨i, ⟨a⟩⟩ := (Sieve.mem_ofObjects_iff X g).1 hg
  obtain ⟨i', ⟨e⟩⟩ := h i
  exact (Sieve.mem_ofObjects_iff Y g).2 ⟨i', ⟨a ≫ e⟩⟩

/-- Covering families of the members of a family covering the final object assemble into a
family covering the final object. -/
lemma coversTop_bind {ι : Type*} {X : ι → C} (hX : J.CoversTop X) {κ : ι → Type*}
    {Y : ∀ i, κ i → C} (g : ∀ i (m : κ i), Y i m ⟶ X i)
    (hg : ∀ i, Sieve.ofArrows (Y i) (g i) ∈ J (X i)) :
    J.CoversTop (fun p : Σ i, κ i => Y p.1 p.2) := by
  intro Z
  refine J.transitive (hX Z) _ fun W h hh => ?_
  obtain ⟨i, ⟨a⟩⟩ := (Sieve.mem_ofObjects_iff X h).1 hh
  refine J.superset_covering ?_ (J.pullback_stable a (hg i))
  rintro W' b ⟨T, p, q, ⟨m⟩, hpq⟩
  exact (Sieve.mem_ofObjects_iff _ _).2 ⟨⟨i, m⟩, ⟨p⟩⟩

end CoversTop

section FilteredColimit

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  {I : Type uI} [Category.{vI} I] [IsFiltered I]
  (D : I ⥤ SheafOfModules.{t} R) [HasColimitsOfShape (Discrete I) (SheafOfModules.{t} R)]
  (c : Cocone D)

/-- The canonical morphism from the coproduct of the stages of `D` to the vertex of a cocone
on `D`. -/
private noncomputable abbrev stagesDesc : (∐ fun i => D.obj i) ⟶ c.pt :=
  Sigma.desc (fun i => c.ι.app i)

omit [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  [IsFiltered I] in
/-- The coproduct of the stages of a diagram surjects onto the colimit. -/
private lemma epi_stagesDesc (hc : IsColimit c) : Epi (stagesDesc D c) where
  left_cancellation {Z} f g h := hc.hom_ext fun i => by
    rw [show c.ι.app i = Sigma.ι (fun i => D.obj i) i ≫ stagesDesc D c by simp,
      Category.assoc, Category.assoc, h]

omit [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  [IsFiltered I] in
/-- Over a quasi-compact object of the site the sections of the coproduct of the stages are
generated, as an abelian group, by the images of the coproduct injections. -/
private lemma mem_closure_range_ι (W : C) (hW : J.IsQuasiCompactObject W)
    (y : ToType ((∐ fun i => D.obj i).val.obj (op W))) :
    y ∈ AddSubgroup.closure
      (⋃ i : I, Set.range (fun x : ToType ((D.obj i).val.obj (op W)) =>
        (Sigma.ι (fun i => D.obj i) i).val.app (op W) x)) := by
  set G := SheafOfModules.toSheaf.{t} R ⋙ (sheafSections J AddCommGrpCat.{t}).obj (op W)
  have hpres : PreservesColimitsOfShape (Discrete I) G :=
    sheafOfModules_sections_preserves_coproducts J R W hW I
  have hcol : IsColimit (G.mapCocone (Cofan.mk (∐ fun i => D.obj i)
      (Sigma.ι (fun i => D.obj i)))) :=
    isColimitOfPreserves G (coproductIsCoproduct (fun i => D.obj i))
  set H := AddSubgroup.closure
      (⋃ i : I, Set.range (fun x : ToType ((D.obj i).val.obj (op W)) =>
        (Sigma.ι (fun i => D.obj i) i).val.app (op W) x))
  have hmem (i : I) (x : ToType ((D.obj i).val.obj (op W))) :
      (Sigma.ι (fun i => D.obj i) i).val.app (op W) x ∈ H :=
    AddSubgroup.subset_closure (Set.mem_iUnion.2 ⟨i, Set.mem_range_self x⟩)
  let Q : AddCommGrpCat.{t} :=
    AddCommGrpCat.of (ToType ((∐ fun i => D.obj i).val.obj (op W)) ⧸ H)
  let q : G.obj (∐ fun i => D.obj i) ⟶ Q := AddCommGrpCat.ofHom (QuotientAddGroup.mk' H)
  have hq : q = 0 := by
    refine hcol.hom_ext fun i => ?_
    ext x
    exact (QuotientAddGroup.eq_zero_iff _).2 (hmem i.as x)
  exact (QuotientAddGroup.eq_zero_iff _).1 (ConcreteCategory.congr_hom hq y)

omit [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}] in
/-- Over a quasi-compact object of the site, the image of a section of the coproduct of the
stages under the canonical map to the vertex is the image of a section of a single stage. -/
private lemma exists_stage (W : C) (hW : J.IsQuasiCompactObject W)
    (y : ToType ((∐ fun i => D.obj i).val.obj (op W))) :
    ∃ (k : I) (z : ToType ((D.obj k).val.obj (op W))),
      (c.ι.app k).val.app (op W) z = (stagesDesc D c).val.app (op W) y := by
  have hι (i : I) (x : ToType ((D.obj i).val.obj (op W))) :
      (stagesDesc D c).val.app (op W) ((Sigma.ι (fun i => D.obj i) i).val.app (op W) x) =
        (c.ι.app i).val.app (op W) x := by
    have h : (Sigma.ι (fun i => D.obj i) i ≫ stagesDesc D c) = c.ι.app i := by simp
    exact app_apply_congr h x
  have hw {i j : I} (f : i ⟶ j) (x : ToType ((D.obj i).val.obj (op W))) :
      (c.ι.app j).val.app (op W) ((D.map f).val.app (op W) x) =
        (c.ι.app i).val.app (op W) x :=
    app_apply_congr (c.w f) x
  induction (mem_closure_range_ι D W hW y) using AddSubgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, z, rfl⟩ := Set.mem_iUnion.1 hx
      exact ⟨i, z, (hι i z).symm⟩
  | zero =>
      have : Nonempty I := IsFiltered.nonempty
      exact ⟨Classical.arbitrary I, 0, by simp⟩
  | add a b _ _ ha hb =>
      obtain ⟨k₁, z₁, h₁⟩ := ha
      obtain ⟨k₂, z₂, h₂⟩ := hb
      refine ⟨IsFiltered.max k₁ k₂,
        (D.map (IsFiltered.leftToMax k₁ k₂)).val.app (op W) z₁ +
          (D.map (IsFiltered.rightToMax k₁ k₂)).val.app (op W) z₂, ?_⟩
      rw [map_add, map_add, hw, hw, h₁, h₂]
  | neg a _ ha =>
      obtain ⟨k, z, h⟩ := ha
      exact ⟨k, -z, by rw [map_neg, map_neg, h]⟩

/-- **A section of a filtered colimit of sheaves of modules comes locally from a stage.** For a
section `x` of the colimit over an object `Z` there is a covering sieve of `Z` over each of
whose quasi-compact members the restriction of `x` is the image of a section of a single stage
of the diagram. -/
theorem exists_covering_stage_of_section (hc : IsColimit c) {Z : C}
    (x : ToType (c.pt.val.obj (op Z))) :
    ∃ S : Sieve Z, S ∈ J Z ∧ ∀ (V : C) (g : V ⟶ Z), S g → J.IsQuasiCompactObject V →
      ∃ (k : I) (z : ToType ((D.obj k).val.obj (op V))),
        (c.ι.app k).val.app (op V) z = c.pt.val.map g.op x := by
  have := epi_stagesDesc D c hc
  have hls : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (stagesDesc D c).val) :=
    Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi _
  refine ⟨Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map (stagesDesc D c).val) x,
    hls.imageSieve_mem x, fun V g hg hV => ?_⟩
  obtain ⟨y, hy⟩ := hg
  obtain ⟨k, z, hz⟩ := exists_stage D c V hV y
  exact ⟨k, z, hz.trans hy⟩

/-- **A finite family of sections of a filtered colimit of sheaves of modules comes locally
from one stage.** The sieve and the stage are common to all members of the family. -/
theorem exists_covering_stage_of_finite_family (hc : IsColimit c) {Z : C} {T : Type w}
    [Finite T] (x : T → ToType (c.pt.val.obj (op Z))) :
    ∃ S : Sieve Z, S ∈ J Z ∧ ∀ (V : C) (g : V ⟶ Z), S g → J.IsQuasiCompactObject V →
      ∃ (k : I) (z : T → ToType ((D.obj k).val.obj (op V))),
        ∀ t, (c.ι.app k).val.app (op V) (z t) = c.pt.val.map g.op (x t) := by
  classical
  choose S hS hlift using fun t => exists_covering_stage_of_section D c hc (x t)
  refine ⟨⨅ t, S t, Stacks.SheafOfModules.FiniteTypeKernel.iInf_mem J _ hS,
    fun V g hg hV => ?_⟩
  choose kk zz hzz using fun t =>
    hlift t V g ((Stacks.SheafOfModules.FiniteTypeKernel.iInf_apply _ _).1 hg t) hV
  obtain ⟨k, hk⟩ := Stacks.Filtered.exists_hom_of_finite (I := I) kk
  refine ⟨k, fun t => (D.map (hk t).some).val.app (op V) (zz t), fun t => ?_⟩
  exact (app_apply_congr (c.w (hk t).some) (zz t)).trans (hzz t)

end FilteredColimit

end Stacks.Sites

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Cᵒᵖ ⥤ RingCat.{t}}

/-- Restricting a finite family of sections which generates a presheaf of modules locally over
`U` along an arrow `U' ⟶ U` gives a family which generates it locally over `U'`. -/
lemma generatesLocally_restrict {M : PresheafOfModules.{t} R} {U U' : C} (h : U' ⟶ U)
    {T : Type*} [Fintype T] {s : T → ToType (M.obj (op U))} (hs : GeneratesLocally J M s) :
    GeneratesLocally J M (fun i => M.restrictₛₗ h.op (s i)) := by
  intro V f x
  obtain ⟨S, hS, hcov⟩ := hs V (f ≫ h) x
  refine ⟨S, hS, fun W g hg => ?_⟩
  obtain ⟨a, ha⟩ := hcov W g hg
  refine ⟨a, ?_⟩
  rw [← ha]
  refine Finset.sum_congr rfl fun i _ => congrArg (a i • ·) ?_
  change M.map (g ≫ f).op (M.map h.op (s i)) = M.map (g ≫ f ≫ h).op (s i)
  rw [← M.map_comp_apply, ← op_comp]
  exact M.congr_map_apply (by rw [Category.assoc]) _

end Stacks.SheafOfModules

end
