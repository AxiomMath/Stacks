module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.DirectSum.Module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
import StacksCore.Tactic.StacksAttribute

/-!
# Sections over a quasi-compact object

Sections of sheaves of sets over a quasi-compact object of a site commute with filtered colimits
whose transition maps are injective. For a sheaf of rings `R`, sections of sheaves of
`R`-modules over such an object commute with arbitrary direct sums.

The proof of the second statement is the one of the source. A section of the coproduct over a
quasi-compact object is locally a finite subsum: the subfunctor of sections lying in some finite
subsum contains every coproduct injection, hence, by the universal property of the coproduct,
its local closure is everything; quasi-compactness then bounds the finitely many local subsums
by a single finite one, and separatedness upgrades the local equality to a global one. The
resulting finitely supported family of components exhibits the sections of the coproduct as the
coproduct of the sections.

## Main results

* `Stacks.Sites.sheafOfModules_sections_preserves_coproducts`: evaluation of sheaves of modules
  at a quasi-compact object preserves direct sums.

## Implementation notes

Part (1) of the source is a statement about coproducts of sheaves of *sets*, not about filtered
colimits, so it is not Stacks 0738 part (3): the latter assumes the filtered diagram and the
injectivity of its transition maps, which for a coproduct have first to be produced. That
reduction, and the failure of part (1) as the source states it, are in
`StacksFrontier.CategoryTheory.Sites.QuasiCompact.SetCoproductSections`, which is where part (1)
is now registered. For part (2),
direct sums are categorical coproducts, that is colimits indexed by a discrete category, and
evaluation of a sheaf of modules is the composite of the passage to its underlying abelian
sheaf with the sections functor at the chosen object.

The finite-support argument is carried out with the *presheaf* submodule of sections lying in
some finite subsum together with its sheafification as a subobject, rather than with an
explicit kernel or image, because the finite-support condition is not local: only after
quasi-compactness is used does the local statement become global.

## References

* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
* [Stacks Project, Tag 0738](https://stacks.math.columbia.edu/tag/0738)
-/

@[expose] public section

universe w s r v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites

attribute [local instance] Classical.propDecidable

private noncomputable def liftToLocalClosure
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} {M L : SheafOfModules.{s} R}
    (N : M.val.Submodule) (f : L ⟶ M)
    (hf : ∀ X x, f.val.app X x ∈ N.obj X) :
    L ⟶ (Stacks.SheafOfModules.localClosure _ N).toSheafOfModules where
  val :=
    { app X := ModuleCat.ofHom
        ((f.val.app X).hom.codRestrict _ fun x => N.toSubfunctor.le_sheafify J X (hf X x))
      naturality g := by
        ext x
        exact Subtype.ext (PresheafOfModules.naturality_apply f.val g x) }

private lemma liftToLocalClosure_comp
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} {M L : SheafOfModules.{s} R}
    (N : M.val.Submodule) (f : L ⟶ M)
    (hf : ∀ X x, f.val.app X x ∈ N.obj X) :
    liftToLocalClosure N f hf ≫ (Stacks.SheafOfModules.localClosure _ N).ι = f := by
  ext X x
  rfl

section Coproduct

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{r}} {ι : Type w}
  (F : ι → SheafOfModules.{s} R) (c : Cofan F) (hc : IsColimit c)

/-- Pointwise form of an equality of morphisms of sheaves of modules `f ≫ g = h`. -/
private lemma app_apply_of_comp_eq {M N P : SheafOfModules.{s} R} {f : M ⟶ N} {g : N ⟶ P}
    {h : M ⟶ P} (e : f ≫ g = h) (X : Cᵒᵖ) (x : M.val.obj X) :
    g.val.app X (f.val.app X x) = h.val.app X x :=
  congrArg (fun k => k.val.app X x) e

/-- The canonical retraction onto one summand of a colimiting cofan. -/
private noncomputable def projection (i : ι) : c.pt ⟶ F i :=
  hc.desc (Cofan.mk (F i) (fun j => if h : j = i then eqToHom (congrArg F h) else 0))

private lemma injection_projection (i j : ι) :
    c.inj j ≫ projection F c hc i =
      if h : j = i then eqToHom (congrArg F h) else 0 :=
  hc.fac _ (Discrete.mk j)

/-- The endomorphism retaining just the summands indexed by a finite set. -/
private noncomputable def projector (t : Finset ι) : c.pt ⟶ c.pt :=
  ∑ i ∈ t, projection F c hc i ≫ c.inj i

private lemma injection_projector (t : Finset ι) (i : ι) :
    c.inj i ≫ projector F c hc t = if i ∈ t then c.inj i else 0 := by
  classical
  simp only [projector, Preadditive.comp_sum, ← Category.assoc, injection_projection]
  trans ∑ j ∈ t, if i = j then c.inj i else 0
  · refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  · simp

private lemma projector_comp_of_subset {t t' : Finset ι} (h : t ⊆ t') :
    projector F c hc t ≫ projector F c hc t' = projector F c hc t := by
  classical
  simp only [projector, Preadditive.sum_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← projector, injection_projector, ite_eq_left (h hi)]

private lemma fixed_of_subset {t t' : Finset ι} (h : t ⊆ t')
    (X : Cᵒᵖ) (x : c.pt.val.obj X) (hx : (projector F c hc t).val.app X x = x) :
    (projector F c hc t').val.app X x = x := by
  have hh := app_apply_of_comp_eq (projector_comp_of_subset F c hc h) X x
  rwa [hx] at hh

/-- Sections lying in some finite subsum, before imposing the sheaf condition. -/
private noncomputable def finiteSupportSubmodule : c.pt.val.Submodule where
  obj X :=
    { carrier := {x | ∃ t : Finset ι, (projector F c hc t).val.app X x = x}
      zero_mem' := ⟨∅, map_zero _⟩
      add_mem' := by
        rintro x y ⟨t, ht⟩ ⟨t', ht'⟩
        classical
        exact ⟨t ∪ t', by rw [map_add,
          fixed_of_subset F c hc Finset.subset_union_left X x ht,
          fixed_of_subset F c hc Finset.subset_union_right X y ht']⟩
      smul_mem' := by
        rintro a x ⟨t, ht⟩
        refine ⟨t, ?_⟩
        change ((projector F c hc t).val.app X).hom (a • x) = a • x
        rw [map_smul, ht] }
  map {X Y} g := by
    rintro x ⟨t, ht⟩
    refine ⟨t, ?_⟩
    change (projector F c hc t).val.app Y (c.pt.val.map g x) = c.pt.val.map g x
    rw [PresheafOfModules.naturality_apply, ht]

/-- The local closure of the finite subsums contains every coproduct injection, so the
coproduct universal property forces it to contain every section. -/
private lemma locally_finiteSupport (X : Cᵒᵖ) (x : c.pt.val.obj X) :
    ((finiteSupportSubmodule F c hc).toSubfunctor.sieveOfSection x) ∈ J X.unop := by
  let N := finiteSupportSubmodule F c hc
  have hi (i : ι) (X : Cᵒᵖ) (x : (F i).val.obj X) : (c.inj i).val.app X x ∈ N.obj X :=
    ⟨{i}, by
      simpa using app_apply_of_comp_eq (injection_projector F c hc {i} i) X x⟩
  let d : Cofan F := Cofan.mk (Stacks.SheafOfModules.localClosure _ N).toSheafOfModules
    (fun i => liftToLocalClosure N (c.inj i) (hi i))
  have hd : hc.desc d ≫ (Stacks.SheafOfModules.localClosure _ N).ι = 𝟙 c.pt := by
    refine hc.hom_ext fun i => ?_
    rw [← Category.assoc, hc.fac]
    exact liftToLocalClosure_comp N (c.inj i.as) (hi i.as)
  have hx := ((hc.desc d).val.app X x).property
  change ((hc.desc d ≫ (Stacks.SheafOfModules.localClosure _ N).ι).val.app X x) ∈
    (Stacks.SheafOfModules.localClosure _ N).obj X at hx
  have hx' : x ∈ (Stacks.SheafOfModules.localClosure _ N).obj X := by
    simpa only [hd, SheafOfModules.id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply] using hx
  exact hx'

/-- Quasi-compactness bounds the finitely many local subsums by one finite subsum. The
resulting equality of sections follows from separatedness. -/
private lemma finiteSupport_of_quasiCompact (W : C) (hW : J.IsQuasiCompactObject W)
    (x : c.pt.val.obj (op W)) :
    ∃ t : Finset ι, (projector F c hc t).val.app (op W) x = x := by
  classical
  let S := (finiteSupportSubmodule F c hc).toSubfunctor.sieveOfSection x
  obtain ⟨V, φ, hV, hfin⟩ := hW S.arrows.preZeroHypercover (by
    rw [PreZeroHypercover.sieve₀, Sieve.ofArrows,
      ← PreZeroHypercover.presieve₀, Presieve.presieve₀_preZeroHypercover,
      Sieve.generate_sieve]
    exact locally_finiteSupport F c hc (op W) x)
  have hi (i : S.arrows.preZeroHypercover.I₀) : ∃ t : Finset ι,
      (projector F c hc t).val.app (op i.1.1) (c.pt.val.map i.1.2.op x) =
        c.pt.val.map i.1.2.op x := i.2
  choose t ht using hi
  let e : Finset ι := hfin.toFinset.biUnion t
  refine ⟨e, ?_⟩
  apply V.ext_of_isSeparatedFor
    (Presieve.isSeparatedFor_iff_generate.2
      ((Stacks.SheafOfModules.isSheaf_forgetPresheaf c.pt).isSeparated _ hV))
  intro j
  change c.pt.val.map (V.f j).op ((projector F c hc e).val.app (op W) x) =
    c.pt.val.map (V.f j).op x
  rw [← φ.w₀ j]
  change c.pt.val.map ((φ.h₀ j) ≫ (φ.s₀ j).1.2).op
    ((projector F c hc e).val.app (op W) x) = _
  have hx := fixed_of_subset F c hc
    (show t (φ.s₀ j) ⊆ e from Finset.subset_biUnion_of_mem t
      (hfin.mem_toFinset.mpr ⟨j, rfl⟩)) _ _ (ht (φ.s₀ j))
  change c.pt.val.map ((φ.s₀ j).1.2.op ≫ (φ.h₀ j).op)
    ((projector F c hc e).val.app (op W) x) =
    c.pt.val.map ((φ.s₀ j).1.2.op ≫ (φ.h₀ j).op) x
  have hmc (y : c.pt.val.obj (op W)) :
      c.pt.val.map ((φ.s₀ j).1.2.op ≫ (φ.h₀ j).op) y =
        c.pt.val.map (φ.h₀ j).op (c.pt.val.map (φ.s₀ j).1.2.op y) :=
    PresheafOfModules.map_comp_apply c.pt.val _ _ y
  rw [hmc, hmc, ← PresheafOfModules.naturality_apply, hx]

private lemma projection_eq_zero_of_fixed {t : Finset ι} (X : Cᵒᵖ)
    (x : c.pt.val.obj X) (hx : (projector F c hc t).val.app X x = x)
    {i : ι} (hi : i ∉ t) : (projection F c hc i).val.app X x = 0 := by
  have he : projector F c hc t ≫ projection F c hc i = 0 := by
    simp only [projector, Preadditive.sum_comp, Category.assoc, injection_projection]
    refine Finset.sum_eq_zero fun j hj => ?_
    simp [show j ≠ i from fun h => hi (h ▸ hj)]
  have hh : (projection F c hc i).val.app X ((projector F c hc t).val.app X x) = 0 :=
    app_apply_of_comp_eq he X x
  rwa [hx] at hh

/-- The canonical projections of a section form a finitely supported family. -/
private noncomputable def sectionComponents (W : C) (hW : J.IsQuasiCompactObject W) :
    c.pt.val.obj (op W) →+ Π₀ i, (F i).val.obj (op W) where
  toFun x :=
    { toFun i := (projection F c hc i).val.app (op W) x
      support' := Trunc.mk ⟨(finiteSupport_of_quasiCompact F c hc W hW x).choose.val,
        fun i => by
          by_cases hi : i ∈ (finiteSupport_of_quasiCompact F c hc W hW x).choose
          · exact Or.inl hi
          · exact Or.inr (projection_eq_zero_of_fixed F c hc _ x
              (finiteSupport_of_quasiCompact F c hc W hW x).choose_spec hi)⟩ }
  map_zero' := by
    ext i
    exact ((projection F c hc i).val.app (op W)).hom.map_zero
  map_add' x y := by
    ext i
    exact ((projection F c hc i).val.app (op W)).hom.map_add x y

private lemma sectionComponents_injection (W : C) (hW : J.IsQuasiCompactObject W)
    (i : ι) (x : (F i).val.obj (op W)) :
    sectionComponents F c hc W hW ((c.inj i).val.app (op W) x) = DFinsupp.single i x := by
  classical
  ext j
  change (projection F c hc j).val.app (op W) ((c.inj i).val.app (op W) x) = _
  have h := app_apply_of_comp_eq (injection_projection F c hc j i) (op W) x
  by_cases hij : i = j
  · subst hij
    simpa using h
  · rw [DFinsupp.single_eq_of_ne (Ne.symm hij)]
    rw [dite_eq_right hij] at h
    exact h

private lemma projector_apply (t : Finset ι) (X : Cᵒᵖ) (x : c.pt.val.obj X) :
    (projector F c hc t).val.app X x =
      ∑ i ∈ t, (c.inj i).val.app X ((projection F c hc i).val.app X x) := by
  classical
  induction t using Finset.induction_on with
  | empty => rfl
  | @insert i t hi ih =>
    simp only [projector, Finset.sum_insert hi] at *
    change ((projection F c hc i ≫ c.inj i).val.app X x +
      (∑ j ∈ t, projection F c hc j ≫ c.inj j).val.app X x) = _
    rw [ih]
    rfl

private noncomputable def sectionsCofanIsColimit (W : C) (hW : J.IsQuasiCompactObject W) :
    IsColimit (Cofan.mk (AddCommGrpCat.of (c.pt.val.obj (op W)))
      (fun i => AddCommGrpCat.ofHom ((c.inj i).val.app (op W)).hom.toAddMonoidHom)) := by
  classical
  let components := sectionComponents F c hc W hW
  refine Cofan.IsColimit.mk _
    (fun d => AddCommGrpCat.ofHom
      ((DFinsupp.sumAddHom (fun i => (d.inj i).hom)).comp components)) ?_ ?_
  · intro d i
    ext x
    change DFinsupp.sumAddHom (fun j => (d.inj j).hom)
      (components ((c.inj i).val.app (op W) x)) = _
    rw [sectionComponents_injection, DFinsupp.sumAddHom_single]
  · intro d m hm
    ext x
    obtain ⟨t, ht⟩ := finiteSupport_of_quasiCompact F c hc W hW x
    have hs : (components x).support ⊆ t := by
      intro i hi
      by_contra hn
      exact (DFinsupp.mem_support_iff.mp hi)
        (projection_eq_zero_of_fixed F c hc _ x ht hn)
    change m x = DFinsupp.sumAddHom (fun j => (d.inj j).hom) (components x)
    rw [DFinsupp.sumAddHom_apply, DFinsupp.sum_of_support_subset hs (fun i _ => map_zero _)]
    conv_lhs => rw [← ht, projector_apply]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ =>
      CategoryTheory.congr_fun (hm i) ((projection F c hc i).val.app (op W) x)

end Coproduct

/-- **Stacks 0935, part (2).** For a sheaf of rings, sections of sheaves of modules over a
quasi-compact object preserve arbitrary direct sums. -/
@[stacks 0935 "part (2)", ega "IV 16.8.11" "(i), special case"]
theorem sheafOfModules_sections_preserves_coproducts
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{r}) (W : C) (hW : J.IsQuasiCompactObject W) (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι)
      (SheafOfModules.toSheaf.{s} R ⋙
        (sheafSections J AddCommGrpCat.{s}).obj (op W)) := by
  let S := SheafOfModules.toSheaf.{s} R ⋙ (sheafSections J AddCommGrpCat.{s}).obj (op W)
  constructor
  intro F
  let f : ι → SheafOfModules.{s} R := fun i => F.obj (Discrete.mk i)
  let e : F ≅ Discrete.functor f := Discrete.natIso (fun i => Iso.refl (F.obj i))
  have : PreservesColimit (Discrete.functor f) S :=
    ⟨fun {c} hc => ⟨(Cofan.isColimitMapCoconeEquiv S f c).symm
      (sectionsCofanIsColimit f c hc W hW)⟩⟩
  exact preservesColimit_of_iso_diagram S e.symm

end Stacks.Sites

end
