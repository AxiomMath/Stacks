module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFinite
public import StacksCore.Tactic.StacksAttribute

/-!
# The kernel of a surjection onto a finitely presented sheaf of modules, with no products

Let `(C, J)` be a site and `R` a sheaf of rings on it. Stacks Tag 082T, the ringed-site form of
Tag 01BP, says that if `F` is a sheaf of `R`-modules of finite presentation and `θ : G ⟶ F` is a
surjection with `G` of finite type, then `Ker θ` is of finite type. A site in the sense of the
Stacks project (Tag 00VH) is assumed to have neither products nor pullbacks, so a proof that
takes `HasBinaryProducts C` or `HasPullbacks C` proves something weaker than the source.

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify` proves the statement with
both of those hypotheses:
`Stacks.SheafOfModules.LocalKernel.kernel_isFiniteType_of_epi_from_finiteType` intersects the
covering family on which `F` has a finite presentation with the one on which `G` has finitely
many generators, and then restricts both pieces of data *along a morphism of the site*, which is
where the hypotheses enter — restriction along a morphism of `C` is a left adjoint only when `C`
has pullbacks, and restriction to a slice site only when `C` has binary products.

This file removes both hypotheses. The observation is that an object of the intersected covering
sieve already carries a morphism to a member of each family, so the two pieces of data can be
transported by *restriction to a slice of a slice site* instead of along a morphism of `C`, and
for finite data that transport is products-free: it is
`Stacks.SheafOfModules.SliceFinite.slicePresentation` and
`Stacks.SheafOfModules.SliceFinite.sliceGenerators`, followed by the identification of the twice
restricted sheaf with a once restricted one along `CategoryTheory.Over.iteratedSliceEquiv`.

## Main definitions

* `Stacks.SheafOfModules.SliceFinite.presentationIteratedSlice`: a presentation of the twice
  restricted sheaf of modules `(M.over W).over Z`, read as a presentation of `M.over Z.left`
  along `CategoryTheory.Over.iteratedSliceEquiv`. This is the presentation analogue of
  `Stacks.SheafOfModules.LocalKernel.generatingSectionsIteratedSlice`.
* `Stacks.SheafOfModules.SliceFinite.presentationOfHomToQuasicoherentData` and
  `Stacks.SheafOfModules.SliceFinite.generatorsOfHomToLocalGeneratorsData`: over an object
  carrying a morphism to a member of a covering family, a finite global presentation,
  respectively a finite family of global generating sections, of the restricted sheaf.

## Main results

* `Stacks.SheafOfModules.SliceFinite.isFiniteType_kernel_over`: over an object carrying a finite
  global presentation of the target and finitely many global generators of the source, the
  kernel of a surjection restricts to a sheaf of modules of finite type.
* `Stacks.SheafOfModules.SliceFinite.isFiniteType_kernel_of_epi`: **Stacks Tag 082T**, and hence
  Tag 01BP part (2), with no products and no pullbacks on the site.
* `Stacks.SheafOfModules.SliceFinite.isFiniteType_kernel_of_epi_from_finite_free`: **Stacks Tag
  01BP part (1)**, with no products and no pullbacks on the site.

## Implementation notes

**Why the transport is products-free.** `SheafOfModules.Presentation.map` asks the functor it
maps along for `PreservesColimitsOfSize`. Restriction to a slice site has that only through
`SheafOfModules.overPushforwardOverAdj`, which needs `HasBinaryProducts C`; but the functor used
here is half of `SheafOfModules.pushforwardPushforwardEquivalence` applied to the *equivalence*
`CategoryTheory.Over.iteratedSliceEquiv`, and an equivalence preserves every colimit
unconditionally. The construction is the one Mathlib performs inline inside
`SheafOfModules.QuasicoherentData.bind`; it is factored out here because the finiteness of the
transported presentation is needed, and `bind` never records it.

**Why the index sets of a mapped presentation are handled by defeq.** The simp lemmas
`Presentation.map_generators_I` and `Presentation.map_relations_I` do not fire on these goals: the
`PreservesColimitsOfSize` argument is a `Prop`, so the instance appearing in the goal is only
proof-irrelevantly equal to the one simp's pattern carries, and simp reports no progress. Both
equalities hold by `rfl`, so the finiteness instances are supplied by `inferInstanceAs` on the
index type of the original presentation and never by rewriting.

**Which hypotheses are kept.** The sheafification hypotheses `HasSheafify` and
`WEqualsLocallyBijective` on `J` and on each slice topology `J.over X` are kept:
`Abelian (SheafOfModules.{u} R)` is transferred along the sheafification adjunction, and the
argument forms kernels and finite biproducts on both. The twice iterated slice versions are
*not* hypotheses here: they are derived from the once sliced ones by
`Stacks.SheafOfModules.SliceFinite.hasSheafify_iteratedSlice` and
`wEqualsLocallyBijective_iteratedSlice`, which is why they appear as `have`s in the proofs rather
than in the variable block. So the only hypotheses beyond Mathlib's own for stating
`IsFiniteType` and `IsFinitePresentation` are the slice sheafification ones, and they hold on the
site of opens of a topological space.

**Universes.** The site `C : Type u₁` has `Category.{v₁} C` and the sheaf of rings is
`R : Sheaf J RingCat.{u}` with `u`, `u₁`, `v₁` unrelated, which is the generality in which
Mathlib states `SheafOfModules.IsFiniteType` and `SheafOfModules.IsFinitePresentation`. Nothing
is specialised. The slice categories `Over X` live in `Type (max u₁ v₁)` with `Category.{v₁}`,
so every lemma reused on a slice site is instantiated at `u₁ := max u₁ v₁`; that happens by
unification and needs no annotation.

**Relation to the tagged declarations already in the library.** Stacks 01BP is stated for a
ringed *space*, and `Opens X` has both binary products and pullbacks (intersections of opens), so
`Stacks.SheafOfModules.LocalKernel.kernel_isFiniteType_of_epi_from_finiteType` instantiates to
the full content of part (2) and carries that registration. Part (1) is registered here, on the
statement proved with four instance hypotheses instead of ten; `LocalKernel` derives the same
statement from its part (2) and keeps it as the untagged `instance` that downstream instance
search reaches. What neither of those proves is the ringed-site statement 082T, which is why
that tag is carried here rather than there.

## References

* [Stacks Project, Tag 082T](https://stacks.math.columbia.edu/tag/082T)
* [Stacks Project, Tag 01BP](https://stacks.math.columbia.edu/tag/01BP)
* [Stacks Project, Tag 00VH](https://stacks.math.columbia.edu/tag/00VH)
-/

@[expose] public section

open CategoryTheory Limits SheafOfModules Opposite

universe u v₁ u₁

namespace Stacks.SheafOfModules.SliceFinite

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### Transport of a presentation along `Over.iteratedSliceEquiv` -/

/-- A presentation of the twice restricted sheaf of modules `(M.over W).over Z`, read as a
presentation of `M.over Z.left` along `CategoryTheory.Over.iteratedSliceEquiv`.

This is the presentation analogue of
`Stacks.SheafOfModules.LocalKernel.generatingSectionsIteratedSlice`, and the construction Mathlib
performs inline in `SheafOfModules.QuasicoherentData.bind`. It needs no products on the site
because the functor mapped along is half of an equivalence. -/
noncomputable def presentationIteratedSlice {M : SheafOfModules.{u} R} {W : C} (Z : Over W)
    [HasSheafify ((J.over W).over Z) AddCommGrpCat.{u}]
    [((J.over W).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (P : ((M.over W).over Z).Presentation) :
    (M.over Z.left).Presentation :=
  letI e := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv Z)
    (S := (R.over W).over Z) (R := R.over Z.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
  (P.map e.inverse (.refl _)).ofIsIso
    (e.fullyFaithfulFunctor.preimageIso
      (by exact e.counitIso.app ((M.over W).over Z))).hom

/-- The presentation `presentationIteratedSlice Z P` is finite when `P` is. -/
instance presentationIteratedSlice_isFinite {M : SheafOfModules.{u} R} {W : C} (Z : Over W)
    [HasSheafify ((J.over W).over Z) AddCommGrpCat.{u}]
    [((J.over W).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (P : ((M.over W).over Z).Presentation) [P.IsFinite] :
    (presentationIteratedSlice Z P).IsFinite := by
  let e := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv Z)
    (S := (R.over W).over Z) (R := R.over Z.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
  have : (P.map e.inverse (.refl _)).IsFinite :=
    ⟨⟨inferInstanceAs (Finite P.generators.I)⟩, ⟨inferInstanceAs (Finite P.relations.I)⟩⟩
  exact inferInstanceAs (Presentation.IsFinite (Presentation.ofIsIso _ _))

/-! ### Finite data over an object of an intersected covering sieve -/

/-- Over an object `V` carrying a morphism to a member of a covering family on which `M` has
finite presentations, a finite presentation of `M.over V` by global sections: restrict the given
presentation to the slice over `V` inside the slice site, then read the twice restricted sheaf as
a once restricted one. -/
noncomputable def presentationOfHomToQuasicoherentData {M : SheafOfModules.{u} R}
    (q : M.QuasicoherentData) [q.IsFinitePresentation] (i : q.I) {V : C} (a : V ⟶ q.X i) :
    (M.over V).Presentation :=
  have _ : ∀ (X : C) (Z : Over X), HasSheafify ((J.over X).over Z) AddCommGrpCat.{u} :=
    fun X Z ↦ hasSheafify_iteratedSlice J X Z
  have _ : ∀ (X : C) (Z : Over X),
      ((J.over X).over Z).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    fun X Z ↦ wEqualsLocallyBijective_iteratedSlice J X Z
  presentationIteratedSlice (Over.mk a) (slicePresentation (q.presentation i) (Over.mk a))

/-- The presentation `presentationOfHomToQuasicoherentData q i a` is finite. -/
instance presentationOfHomToQuasicoherentData_isFinite {M : SheafOfModules.{u} R}
    (q : M.QuasicoherentData) [q.IsFinitePresentation] (i : q.I) {V : C} (a : V ⟶ q.X i) :
    (presentationOfHomToQuasicoherentData q i a).IsFinite := by
  have _ : ∀ (X : C) (Z : Over X), HasSheafify ((J.over X).over Z) AddCommGrpCat.{u} :=
    hasSheafify_iteratedSlice J
  have _ : ∀ (X : C) (Z : Over X),
      ((J.over X).over Z).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    wEqualsLocallyBijective_iteratedSlice J
  exact inferInstanceAs (Presentation.IsFinite
    (presentationIteratedSlice (Over.mk a) (slicePresentation (q.presentation i) (Over.mk a))))

/-- Over an object `V` carrying a morphism to a member of a covering family on which `M` has
finitely many generating sections, a finite family of global generating sections of `M.over V`. -/
noncomputable def generatorsOfHomToLocalGeneratorsData {M : SheafOfModules.{u} R}
    (σ : M.LocalGeneratorsData) (j : σ.I) [(σ.generators j).IsFiniteType] {V : C}
    (b : V ⟶ σ.X j) :
    (M.over V).GeneratingSections :=
  have _ : ∀ (X : C) (Z : Over X), HasSheafify ((J.over X).over Z) AddCommGrpCat.{u} :=
    fun X Z ↦ hasSheafify_iteratedSlice J X Z
  have _ : ∀ (X : C) (Z : Over X),
      ((J.over X).over Z).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    fun X Z ↦ wEqualsLocallyBijective_iteratedSlice J X Z
  LocalKernel.generatingSectionsIteratedSlice (Over.mk b)
    (sliceGenerators (σ.generators j) (Over.mk b))

/-- The family of generating sections `generatorsOfHomToLocalGeneratorsData σ j b` is finite. -/
instance generatorsOfHomToLocalGeneratorsData_isFiniteType {M : SheafOfModules.{u} R}
    (σ : M.LocalGeneratorsData) (j : σ.I) [(σ.generators j).IsFiniteType] {V : C}
    (b : V ⟶ σ.X j) :
    (generatorsOfHomToLocalGeneratorsData σ j b).IsFiniteType := by
  have _ : ∀ (X : C) (Z : Over X), HasSheafify ((J.over X).over Z) AddCommGrpCat.{u} :=
    hasSheafify_iteratedSlice J
  have _ : ∀ (X : C) (Z : Over X),
      ((J.over X).over Z).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    wEqualsLocallyBijective_iteratedSlice J
  exact inferInstanceAs (GeneratingSections.IsFiniteType
    (LocalKernel.generatingSectionsIteratedSlice (Over.mk b)
      (sliceGenerators (σ.generators j) (Over.mk b))))

/-! ### Stacks Tag 082T without products on the site -/

/-- Over an object carrying a finite global presentation of the target and finitely many global
generating sections of the source, the kernel of a surjection restricts to a sheaf of modules of
finite type. -/
theorem isFiniteType_kernel_over [∀ (X : C) (Z : Over X),
      HasSheafify ((J.over X).over Z) AddCommGrpCat.{u}]
    [∀ (X : C) (Z : Over X), ((J.over X).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {F G : SheafOfModules.{u} R} (θ : G ⟶ F) [Epi θ] (V : C)
    (P : (F.over V).Presentation) [P.IsFinite]
    (gs : (G.over V).GeneratingSections) [gs.IsFiniteType] :
    ((kernel θ).over V).IsFiniteType :=
  isFiniteType_of_epi (PreservesKernel.iso (overFunctor R V) θ).inv
    (isFiniteType_kernel_of_presentation P gs (θ.over V))

/-- On a site with no products and no pullbacks assumed, the kernel of a surjection from a sheaf
of modules of finite type onto a sheaf of modules of finite presentation is of finite type. This
also gives Stacks Project, Tag 01BP part (2). -/
@[stacks 082T]
theorem isFiniteType_kernel_of_epi {F G : SheafOfModules.{u} R}
    [F.IsFinitePresentation] [G.IsFiniteType] (theta : G ⟶ F) [Epi theta] :
    (kernel theta).IsFiniteType := by
  have _ : ∀ (X : C) (Z : Over X), HasSheafify ((J.over X).over Z) AddCommGrpCat.{u} :=
    hasSheafify_iteratedSlice J
  have _ : ∀ (X : C) (Z : Over X),
      ((J.over X).over Z).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    wEqualsLocallyBijective_iteratedSlice J
  obtain ⟨q, hq⟩ := IsFinitePresentation.exists_quasicoherentData F
  obtain ⟨σ, hσ⟩ := IsFiniteType.exists_localGeneratorsData G
  refine LocalKernel.isFiniteType_of_coversTop _
    (Subtype.val : { V : C // ((kernel theta).over V).IsFiniteType } → C) ?_ fun i ↦ i.2
  intro Y
  refine J.superset_covering ?_
    (J.intersection_covering (q.coversTop Y) (σ.coversTop Y))
  rintro V g ⟨hg₁, hg₂⟩
  obtain ⟨i, ⟨a⟩⟩ := (Sieve.mem_ofObjects_iff _ g).1 hg₁
  obtain ⟨j, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff _ g).1 hg₂
  have := hσ.isFiniteType j
  exact (Sieve.mem_ofObjects_iff _ g).2
    ⟨⟨V, isFiniteType_kernel_over theta V (presentationOfHomToQuasicoherentData q i a)
      (generatorsOfHomToLocalGeneratorsData σ j b)⟩, ⟨𝟙 V⟩⟩

/-- On a site with no products and no pullbacks assumed, the kernel of a surjection from a
finite-rank free sheaf of modules onto a sheaf of modules of finite presentation is of finite
type. -/
@[stacks 01BP "part (1)"]
theorem isFiniteType_kernel_of_epi_from_finite_free {I : Type u} [Finite I]
    {F : SheafOfModules.{u} R} [F.IsFinitePresentation] (psi : free I ⟶ F) [Epi psi] :
    (kernel psi).IsFiniteType :=
  have _ : (free.generatingSections (R := R) I).IsFiniteType := ⟨inferInstanceAs (Finite I)⟩
  isFiniteType_kernel_of_generatingSections (free.generatingSections I) psi

end Stacks.SheafOfModules.SliceFinite

end
