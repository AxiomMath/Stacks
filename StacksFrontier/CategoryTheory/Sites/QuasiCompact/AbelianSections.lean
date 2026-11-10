module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Sites.Hypercover.One
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.CategoryTheory.Sites.Whiskering
public import StacksFrontier.CategoryTheory.Sites.DirectSumRecognition
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact

/-!
# Sections of sheaves of abelian groups over a quasi-compact object

For a quasi-compact object `W` of a site (Stacks 090H), taking sections over `W` of sheaves of
abelian groups commutes with arbitrary direct sums.

A section of a direct sum over a quasi-compact object is locally a finite subsum: the subobject
of sections lying in some finite subsum contains every coproduct injection, hence, by the
universal property of the coproduct, its local closure is everything; quasi-compactness then
bounds the finitely many local subsums by a single finite one, and separatedness upgrades the
local equality to a global one. The resulting finitely supported family of components exhibits
the sections of the direct sum as the direct sum of the sections.

## Main results

* `Stacks.Sites.preservesColimitsOfShape_discrete_sheafSections_of_isQuasiCompactObject`:
  for a quasi-compact object `W` of a site, the sections functor
  `(sheafSections J AddCommGrpCat).obj (op W)` on sheaves of abelian groups preserves colimits
  indexed by a discrete category, that is, arbitrary direct sums.

## Implementation notes

This is the sheaf-of-abelian-groups analogue of Stacks 0935 part (2), which the source states
for sheaves of modules over a sheaf of rings; that faithful version is
`Stacks.Sites.sheafOfModules_sections_preserves_coproducts`. The source does not separately
state the abelian-group case, so no declaration here carries a Stacks tag: the file is
Lean-side substrate, stated in the shape the rest of the library consumes.

The proof is the source's argument for the module case, transcribed to sheaves of abelian
groups. It cannot be obtained from the module statement by a change of rings: sheaves of modules
over a sheaf of rings `R` are sheaves of abelian groups only after a choice of `R`, and the
constant presheaf `ℤ` is not a sheaf on a general site, so there is no sheaf of rings whose
modules are exactly the sheaves of abelian groups. The private helpers below therefore rebuild,
for `Sheaf J AddCommGrpCat`, what `SheafOfModules.Submodule` provides for sheaves of modules:
`Stacks.Sites.SubgroupPresheaf` is a family of subgroups of the sections stable under
restriction, and its `localClosure` is the sheaf of abelian groups cut out by the sheafification
of the corresponding subfunctor of sets.

The finite-support argument is carried out with the *presheaf* subgroups of sections lying in
some finite subsum together with their local closure, rather than with an explicit kernel or
image, because the finite-support condition is not local: only after quasi-compactness is used
does the local statement become global.

Which of these helpers are genuinely sheaf-theoretic, and which only look parallel to
`StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleSections`, is worth stating, because the two
files share seventeen private names and the answer differs between them. Twelve --
`underlying_isSheaf`, the `SubgroupPresheaf`/`localClosure`/`liftToLocalClosure` chain,
`locally_finiteSupport`, `finiteSupport_of_quasiCompact`, `projection_eq_zero_of_fixed`,
`sectionComponents`, `sectionComponents_injection`, `projector_apply`, `sectionsCofanIsColimit`
-- mention sections, sieves or the sheaf condition, and are the rebuild the paragraph above
describes. The remaining five -- `projection`, `injection_projection`, `projector`,
`injection_projector`, `projector_comp_of_subset` -- mention no section and no sieve: their
statements and proofs use only `Cofan`, `IsColimit`, composition, `eqToHom`, `0`, `∑` and
`Preadditive.comp_sum`/`sum_comp`. They are parallel not because the mathematics differs but
because the ambient category does, and both `Sheaf J AddCommGrpCat` and `SheafOfModules R` are
preadditive. `projection` is already shared: it delegates to
`Stacks.Sites.DirectSumRecognition.projection`, read through `Cofan F = Cocone
(Discrete.functor F)`. Unifying the other four would mean stating them over an abstract
preadditive category and instantiating twice -- a generalisation, not the deletion of a copy --
and Mathlib has `Cofan.IsColimit.desc` but no named retraction of a colimiting cofan to build on.

No universe constraint relates the index type of the direct sum to the universe of the sheaves:
the colimiting cofan is an input, never formed here, so no coproduct in `AddCommGrpCat` of a
family indexed by a larger universe is required.

## References

* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
-/

@[expose] public section

universe w s v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites

attribute [local instance] Classical.propDecidable

section LocalClosure

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A family of subgroups of the sections of a sheaf of abelian groups, stable under
restriction: a subobject of the underlying presheaf of abelian groups. -/
private structure SubgroupPresheaf (M : Sheaf J AddCommGrpCat.{s}) where
  /-- The subgroup of sections over `X`. -/
  obj (X : Cᵒᵖ) : AddSubgroup (M.obj.obj X)
  /-- Membership is stable under restriction along any morphism. -/
  map (X Y : Cᵒᵖ) (f : X ⟶ Y) (x : M.obj.obj X) : x ∈ obj X → M.obj.map f x ∈ obj Y

namespace SubgroupPresheaf

variable {M : Sheaf J AddCommGrpCat.{s}}

/-- The subfunctor of the underlying presheaf of sets determined by `N`. -/
private def toSubfunctor (N : SubgroupPresheaf M) :
    Subfunctor (M.obj ⋙ forget AddCommGrpCat.{s}) where
  obj X := (N.obj X : Set (M.obj.obj X))
  map {X Y} f := fun x hx => N.map X Y f x hx

/-- The subgroups of sections *locally* lying in `N`. -/
private def localClosureSubgroup (N : SubgroupPresheaf M) (X : Cᵒᵖ) :
    AddSubgroup (M.obj.obj X) where
  carrier := (N.toSubfunctor.sheafify J).obj X
  zero_mem' := N.toSubfunctor.le_sheafify J X (N.obj X).zero_mem
  add_mem' := by
    intro x y hx hy
    apply J.superset_covering _ (J.intersection_covering hx hy)
    intro Y f hf
    change M.obj.map f.op (x + y) ∈ N.obj (op Y)
    rw [map_add]
    exact (N.obj _).add_mem hf.1 hf.2
  neg_mem' := by
    intro x hx
    apply J.superset_covering _ hx
    intro Y f hf
    change M.obj.map f.op (-x) ∈ N.obj (op Y)
    rw [map_neg]
    exact (N.obj _).neg_mem hf

/-- The presheaf of abelian groups of sections locally lying in `N`. -/
private def localClosurePresheaf (N : SubgroupPresheaf M) : Cᵒᵖ ⥤ AddCommGrpCat.{s} where
  obj X := AddCommGrpCat.of (N.localClosureSubgroup X)
  map {X Y} f := AddCommGrpCat.ofHom
    { toFun x := ⟨M.obj.map f x.1, (N.toSubfunctor.sheafify J).map f x.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' x y := Subtype.ext (map_add _ _ _) }
  map_id X := by ext x; simp
  map_comp f g := by ext x; simp

/-- The sheaf of abelian groups of sections locally lying in `N`: it is a sheaf because the
sheafification of a subfunctor of a sheaf of sets is one. -/
private def localClosure (N : SubgroupPresheaf M) : Sheaf J AddCommGrpCat.{s} where
  obj := N.localClosurePresheaf
  property := by
    suffices h : Presieve.IsSheaf J (N.toSubfunctor.sheafify J).toFunctor by
      apply Presheaf.isSheaf_of_isSheaf_comp J _ (CategoryTheory.forget AddCommGrpCat.{s})
      rwa [isSheaf_iff_isSheaf_of_type]
    exact N.toSubfunctor.sheafify_isSheaf (Stacks.Sites.DirectSumRecognition.underlying_isSheaf M)

/-- The inclusion of the local closure of `N` into `M`. -/
private def localClosureι (N : SubgroupPresheaf M) : N.localClosure ⟶ M :=
  ObjectProperty.homMk
    { app X := AddCommGrpCat.ofHom (AddSubgroup.subtype (N.localClosureSubgroup X))
      naturality := fun _ _ _ => by ext x; rfl }

/-- A morphism whose sections all lie in `N` factors through the local closure of `N`. -/
private def liftToLocalClosure (N : SubgroupPresheaf M) {L : Sheaf J AddCommGrpCat.{s}}
    (f : L ⟶ M)
    (hf : ∀ (X : Cᵒᵖ) (x : L.obj.obj X), f.hom.app X x ∈ N.obj X) :
    L ⟶ N.localClosure :=
  ObjectProperty.homMk
    { app X := AddCommGrpCat.ofHom
        { toFun x := ⟨f.hom.app X x, N.toSubfunctor.le_sheafify J X (hf X x)⟩
          map_zero' := Subtype.ext (map_zero _)
          map_add' x y := Subtype.ext (map_add _ _ _) }
      naturality := fun X Y g => by
        ext x
        exact Subtype.ext (NatTrans.naturality_apply f.hom g x) }

private lemma liftToLocalClosure_comp (N : SubgroupPresheaf M)
    {L : Sheaf J AddCommGrpCat.{s}} (f : L ⟶ M)
    (hf : ∀ (X : Cᵒᵖ) (x : L.obj.obj X), f.hom.app X x ∈ N.obj X) :
    N.liftToLocalClosure f hf ≫ N.localClosureι = f := by
  apply Sheaf.hom_ext
  ext X x
  rfl

end SubgroupPresheaf

end LocalClosure

section Coproduct

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {ι : Type w}
  (F : ι → Sheaf J AddCommGrpCat.{s}) (c : Cofan F) (hc : IsColimit c)

/-- The canonical retraction onto one summand of a colimiting cofan: the construction of
`Stacks.Sites.DirectSumRecognition.projection`, read through `Cofan F = Cocone
(Discrete.functor F)`. -/
private noncomputable def projection (i : ι) : c.pt ⟶ F i :=
  Stacks.Sites.DirectSumRecognition.projection (Discrete.functor F) c hc i

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
  · apply Finset.sum_congr rfl
    intro j hj
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

/-- If `q ≫ p = r` and `q` fixes a section `x`, then `p` and `r` agree on `x`. -/
private lemma app_eq_of_comp_eq_of_fixed {A B : Sheaf J AddCommGrpCat.{s}} {q : A ⟶ A}
    {p r : A ⟶ B} (h : q ≫ p = r) (X : Cᵒᵖ) (x : A.obj.obj X) (hx : q.hom.app X x = x) :
    p.hom.app X x = r.hom.app X x := by
  have hh := congrArg (fun f : A ⟶ B => f.hom.app X x) h
  change p.hom.app X (q.hom.app X x) = r.hom.app X x at hh
  rwa [hx] at hh

private lemma fixed_of_subset {t t' : Finset ι} (h : t ⊆ t')
    (X : Cᵒᵖ) (x : c.pt.obj.obj X) (hx : (projector F c hc t).hom.app X x = x) :
    (projector F c hc t').hom.app X x = x :=
  (app_eq_of_comp_eq_of_fixed (projector_comp_of_subset F c hc h) X x hx).trans hx

/-- Sections lying in some finite subsum, before imposing the sheaf condition. -/
private noncomputable def finiteSupportSubgroups : SubgroupPresheaf c.pt where
  obj X :=
    { carrier := {x | ∃ t : Finset ι, (projector F c hc t).hom.app X x = x}
      zero_mem' := ⟨∅, map_zero _⟩
      add_mem' := by
        rintro x y ⟨t, ht⟩ ⟨t', ht'⟩
        classical
        exact ⟨t ∪ t', by rw [map_add,
          fixed_of_subset F c hc Finset.subset_union_left X x ht,
          fixed_of_subset F c hc Finset.subset_union_right X y ht']⟩
      neg_mem' := by
        rintro x ⟨t, ht⟩
        exact ⟨t, by rw [map_neg, ht]⟩ }
  map X Y f x := by
    rintro ⟨t, ht⟩
    exact ⟨t, by rw [NatTrans.naturality_apply, ht]⟩

/-- The local closure of the finite subsums contains every coproduct injection, so the
coproduct universal property forces it to contain every section. -/
private lemma locally_finiteSupport (X : Cᵒᵖ) (x : c.pt.obj.obj X) :
    ((finiteSupportSubgroups F c hc).toSubfunctor.sieveOfSection x) ∈ J X.unop := by
  let N := finiteSupportSubgroups F c hc
  have hi (i : ι) (Y : Cᵒᵖ) (y : (F i).obj.obj Y) : (c.inj i).hom.app Y y ∈ N.obj Y :=
    ⟨{i}, by simpa using (congrArg (fun g : F i ⟶ c.pt => g.hom.app Y y)
      (injection_projector F c hc {i} i))⟩
  let d : Cofan F := Cofan.mk N.localClosure (fun i => N.liftToLocalClosure (c.inj i) (hi i))
  have hd : hc.desc d ≫ N.localClosureι = 𝟙 c.pt := hc.hom_ext fun i => by
    rw [← Category.assoc, hc.fac]
    exact N.liftToLocalClosure_comp (c.inj i.as) (hi i.as)
  have hid : ∀ y : c.pt.obj.obj X, (hc.desc d ≫ N.localClosureι).hom.app X y = y := by
    intro y
    rw [hd]
    simp
  have hx := ((hc.desc d).hom.app X x).2
  change ((hc.desc d ≫ N.localClosureι).hom.app X x) ∈ N.localClosureSubgroup X at hx
  rwa [hid x] at hx

/-- Quasi-compactness bounds the finitely many local subsums by one finite subsum. The
resulting equality of sections follows from separatedness. -/
private lemma finiteSupport_of_quasiCompact (W : C) (hW : J.IsQuasiCompactObject W)
    (x : c.pt.obj.obj (op W)) :
    ∃ t : Finset ι, (projector F c hc t).hom.app (op W) x = x := by
  classical
  let S := (finiteSupportSubgroups F c hc).toSubfunctor.sieveOfSection x
  obtain ⟨V, φ, hV, hfin⟩ := hW S.arrows.preZeroHypercover (by
    rw [PreZeroHypercover.sieve₀, Sieve.ofArrows,
      ← PreZeroHypercover.presieve₀, Presieve.presieve₀_preZeroHypercover,
      Sieve.generate_sieve]
    exact locally_finiteSupport F c hc (op W) x)
  have hi (i : S.arrows.preZeroHypercover.I₀) : ∃ t : Finset ι,
      (projector F c hc t).hom.app (op i.1.1) (c.pt.obj.map i.1.2.op x) =
        c.pt.obj.map i.1.2.op x := i.2
  choose t ht using hi
  let e : Finset ι := hfin.toFinset.biUnion t
  refine ⟨e, ?_⟩
  apply V.ext_of_isSeparatedFor (Presieve.isSeparatedFor_iff_generate.2
    ((DirectSumRecognition.underlying_isSheaf c.pt).isSeparated _ hV))
  intro j
  change c.pt.obj.map (V.f j).op ((projector F c hc e).hom.app (op W) x) =
    c.pt.obj.map (V.f j).op x
  rw [← φ.w₀ j]
  change c.pt.obj.map ((φ.h₀ j) ≫ (φ.s₀ j).1.2).op
    ((projector F c hc e).hom.app (op W) x) = _
  have hx := fixed_of_subset F c hc
    (show t (φ.s₀ j) ⊆ e from Finset.subset_biUnion_of_mem t
      (hfin.mem_toFinset.mpr ⟨j, rfl⟩)) _ _ (ht (φ.s₀ j))
  change c.pt.obj.map ((φ.s₀ j).1.2.op ≫ (φ.h₀ j).op)
    ((projector F c hc e).hom.app (op W) x) =
    c.pt.obj.map ((φ.s₀ j).1.2.op ≫ (φ.h₀ j).op) x
  have hmc (y : c.pt.obj.obj (op W)) :
      c.pt.obj.map ((φ.s₀ j).1.2.op ≫ (φ.h₀ j).op) y =
        c.pt.obj.map (φ.h₀ j).op (c.pt.obj.map (φ.s₀ j).1.2.op y) :=
    (ConcreteCategory.congr_hom (c.pt.obj.map_comp _ _) y).trans
      (CategoryTheory.comp_apply _ _ y)
  rw [hmc, hmc, ← NatTrans.naturality_apply, hx]

private lemma projection_eq_zero_of_fixed {t : Finset ι} (X : Cᵒᵖ)
    (x : c.pt.obj.obj X) (hx : (projector F c hc t).hom.app X x = x)
    {i : ι} (hi : i ∉ t) : (projection F c hc i).hom.app X x = 0 := by
  have he : projector F c hc t ≫ projection F c hc i = 0 := by
    simp only [projector, Preadditive.sum_comp, Category.assoc, injection_projection]
    apply Finset.sum_eq_zero
    intro j hj
    simp [show j ≠ i from fun h => hi (h ▸ hj)]
  exact app_eq_of_comp_eq_of_fixed he X x hx

/-- The canonical projections of a section form a finitely supported family. -/
private noncomputable def sectionComponents (W : C) (hW : J.IsQuasiCompactObject W) :
    c.pt.obj.obj (op W) →+ Π₀ i, (F i).obj.obj (op W) where
  toFun x :=
    { toFun i := (projection F c hc i).hom.app (op W) x
      support' := Trunc.mk ⟨(finiteSupport_of_quasiCompact F c hc W hW x).choose.val,
        fun i => by
          by_cases hi : i ∈ (finiteSupport_of_quasiCompact F c hc W hW x).choose
          · exact Or.inl hi
          · exact Or.inr (projection_eq_zero_of_fixed F c hc _ x
              (finiteSupport_of_quasiCompact F c hc W hW x).choose_spec hi)⟩ }
  map_zero' := by
    ext i
    exact ((projection F c hc i).hom.app (op W)).hom.map_zero
  map_add' x y := by
    ext i
    exact ((projection F c hc i).hom.app (op W)).hom.map_add x y

private lemma sectionComponents_injection (W : C) (hW : J.IsQuasiCompactObject W)
    (i : ι) (x : (F i).obj.obj (op W)) :
    sectionComponents F c hc W hW ((c.inj i).hom.app (op W) x) = DFinsupp.single i x := by
  classical
  ext j
  change (projection F c hc j).hom.app (op W) ((c.inj i).hom.app (op W) x) = _
  have h := congrArg (fun f : F i ⟶ F j => f.hom.app (op W) x)
    (injection_projection F c hc j i)
  by_cases hij : i = j
  · subst hij
    simpa using h
  · rw [DFinsupp.single_eq_of_ne (Ne.symm hij)]
    rw [dite_eq_right hij] at h
    change (projection F c hc j).hom.app (op W) ((c.inj i).hom.app (op W) x) =
      ((0 : (F i).obj ⟶ (F j).obj).app (op W)) x at h
    exact h

private lemma projector_apply (t : Finset ι) (X : Cᵒᵖ) (x : c.pt.obj.obj X) :
    (projector F c hc t).hom.app X x =
      ∑ i ∈ t, (c.inj i).hom.app X ((projection F c hc i).hom.app X x) := by
  classical
  induction t using Finset.induction_on with
  | empty => rfl
  | @insert i t hi ih =>
    simp only [projector, Finset.sum_insert hi] at *
    change ((projection F c hc i ≫ c.inj i).hom.app X x +
      (∑ j ∈ t, projection F c hc j ≫ c.inj j).hom.app X x) = _
    rw [ih]
    rfl

/-- Over a quasi-compact object the sections of a direct sum of sheaves of abelian groups are
the direct sum of the sections. -/
private noncomputable def sectionsCofanIsColimit (W : C) (hW : J.IsQuasiCompactObject W) :
    IsColimit (Cofan.mk (c.pt.obj.obj (op W)) (fun i => (c.inj i).hom.app (op W))) := by
  classical
  let components := sectionComponents F c hc W hW
  refine Cofan.IsColimit.mk _
    (fun d => AddCommGrpCat.ofHom
      ((DFinsupp.sumAddHom (fun i => (d.inj i).hom)).comp components)) ?_ ?_
  · intro d i
    ext x
    change DFinsupp.sumAddHom (fun j => (d.inj j).hom)
      (components ((c.inj i).hom.app (op W) x)) = _
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
      ConcreteCategory.congr_hom (hm i) ((projection F c hc i).hom.app (op W) x)

end Coproduct

/-- Sections of sheaves of abelian groups over a quasi-compact object of a site commute with
arbitrary direct sums.

This is the abelian-sheaf analogue of the statement of Stacks 0935 part (2), which the source
states for sheaves of modules; see
`Stacks.Sites.sheafOfModules_sections_preserves_coproducts`. -/
theorem preservesColimitsOfShape_discrete_sheafSections_of_isQuasiCompactObject
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (W : C) (hW : J.IsQuasiCompactObject W) (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι)
      ((sheafSections J AddCommGrpCat.{s}).obj (op W)) := by
  let S := (sheafSections J AddCommGrpCat.{s}).obj (op W)
  refine ⟨fun {G} => ?_⟩
  let f : ι → Sheaf J AddCommGrpCat.{s} := fun i => G.obj (Discrete.mk i)
  let e : G ≅ Discrete.functor f := Discrete.natIso (fun i => Iso.refl (G.obj i))
  let : PreservesColimit (Discrete.functor f) S :=
    ⟨fun {d} hd => ⟨(Cofan.isColimitMapCoconeEquiv S f d).symm
      (sectionsCofanIsColimit f d hd W hW)⟩⟩
  exact preservesColimit_of_iso_diagram S e.symm

end Stacks.Sites

end
