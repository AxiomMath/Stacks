module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineMemberBaseChange
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineSpannedRelations

/-!
# The span condition on the small étale site from the base change of the sections

On the slice of the small étale site of an algebraic space at a chart whose underlying scheme is
affine, a quasi-coherent module and the relations between any family of generators of it are each
locally spanned by their sections over that chart.  This file reduces both halves of that
statement to a single condition on the module alone, namely that over the objects of a prescribed
class its sections are the base change, along the ring map of global functions induced by the
structural morphism, of its sections over the chart.  That condition is
`AlgebraicGeometry.Space.SmallEtale.HasSectionBaseChangeOn`.

The relations half asks strictly more of that comparison than the generators half.  For the
generators only surjectivity of the comparison is used, a span condition being exactly the
assertion that a section is a combination of restricted sections.  For the relations the
comparison must be injective as well, because the module-theoretic step is right exactness of the
tensor product at the kernel (`Module.BaseChange.mem_span_image_ker_of_liftBaseChange`): a
relation over an object of the class is a combination of restrictions of relations over the chart
only once the base change of the sections over the chart injects into the sections there.  A span
condition therefore does not supply what the relations half consumes, and that is why the
hypothesis carried here is bijectivity of the comparison and not an equality of spans.

The second input of the relations half is that the covering of the module whose kernel is being
spanned be surjective on the sections over the chart itself.  It is proved by faithfully flat
descent: an epimorphism of sheaves of modules is locally surjective, so a section over the chart
becomes a value of the covering on a covering sieve; that sieve is intersected with the sieve of
the prescribed covering family before a finite family of objects with affine underlying scheme
whose image in schemes is an fppf covering family is extracted from it
(`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_ofArrows_le_over`).  The intersection is
what keeps the extracted family inside the class: its members have affine underlying scheme and
factor through a member of the covering family, so the hypothesis applies to them, while the
product of their rings of global functions is faithfully flat over the ring of the chart.

Nothing here assumes the comparison; it is carried as a hypothesis throughout, so that the
statements below are already in the shape the span condition needs and discharging it is a
substitution.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtale.HasSectionBaseChangeOn`: the sections of a sheaf of modules
  over the objects of a prescribed class of a slice of the small étale site are the base change of
  its sections over the chart the slice is taken at.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.exists_affine_ofArrows_over_ringedSite`: **every object of a
  slice of the small étale site carries a covering family by objects with affine underlying
  scheme**, at the spelling the sheaves of modules on the slice are indexed by.
* `AlgebraicGeometry.Space.SmallEtale.globalSectionSpan_eq_top_of_hasSectionBaseChangeOn`: **the
  sections over an object of the class are combinations of the restrictions of the sections over
  the chart**, which uses only surjectivity of the comparison.
* `AlgebraicGeometry.Space.SmallEtale.globalSectionSpan_eq_top_ker_of_hasSectionBaseChangeOn`:
  **the relations among the sections of a covering of the module over an object of the class with
  affine underlying scheme are combinations of the relations over the chart.**
* `AlgebraicGeometry.Space.SmallEtale`'s
  `surjective_val_app_mkId_of_epi_of_hasSectionBaseChangeOn`: **an epimorphism onto the module
  from a coproduct of copies of the universe lift of the structure sheaf is surjective on the
  sections over the chart.**
* `AlgebraicGeometry.Space.SmallEtale.isLocallySpannedBySections_over_of_forall_affine_of_cover`
  and `AlgebraicGeometry.Space.SmallEtale.hasLocallySpannedRelations_over_of_cover`: **both span
  conditions are conditions at the objects with affine underlying scheme lying over the members of
  one covering family of the chart.**
* `AlgebraicGeometry.Space.SmallEtale.hasSpannedRelationsOn_of_hasSectionBaseChangeOn` and
  `AlgebraicGeometry.Space.SmallEtale.hasSpannedRelationsOn_over_of_hasSectionBaseChangeOn`: **the
  relations half of a global presentation in its unlocalised form.**
* `AlgebraicGeometry.Space.SmallEtale.hasLocallySpannedRelations_of_hasSectionBaseChangeOn` and
  `AlgebraicGeometry.Space.SmallEtale.isLocallySpannedBySections_of_hasSectionBaseChangeOn`: the
  two halves of the span condition at one chart, and
  `AlgebraicGeometry.Space.SmallEtale`'s
  `isLocallySpannedBySections_and_hasLocallySpannedRelations_of_hasSectionBaseChangeOn` their
  conjunction.

## Implementation notes

The ring and module structures the comparison is stated over are written into
`AlgebraicGeometry.Space.SmallEtale.HasSectionBaseChangeOn` rather than assumed.  The ring of
global functions on the underlying scheme and the ring of sections of the coefficient sheaf of
rings are the same ring definitionally
(`AlgebraicGeometry.Space.SmallEtale.ringSheaf_over_obj_obj`) but not syntactically, so a module
structure over the former is not found by instance search; assuming one as an instance argument
instead would not do, because the maps the proofs build out of the morphisms of the site are
linear for the module structure the sheaf of modules carries and for no other.  With the
structures written into the definition, the comparison it speaks of is the one those proofs
construct, and each structure is `inferInstanceAs`, `Module.compHom` along the induced map, or
`IsScalarTower.of_algebraMap_smul`; no instance is created.

The class of testing objects is a parameter rather than the objects with affine underlying scheme.
Both halves are needed at the objects with affine underlying scheme lying over a member of a
covering family of the chart, which is what quasi-coherence presents the module over and
therefore all a descent argument reaches, while the surjectivity on the sections over the chart
has to be proved at an arbitrary covering sieve of it; intersecting that sieve with the sieve of
the family reconciles the two, and it is the only place the family is used.

The comparison is asked for of the universe lift of the module, because
`SheafOfModules.HasSpannedRelationsOn` quantifies over the coverings of that lift: the kernels
whose sections are to be spanned live at the universe in which global presentations are taken.
The spans of the module itself are read off from those of its lift by
`SheafOfModules.down_mem_globalSectionSpan_of_mem_uliftForPresentation`.

The objects of the site are spelled through the projection of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, which is the spelling the sheaves of modules are
indexed by.  Instance search does not unfold that projection, so each statement stays inside one
of the two spellings and the crossings are confined to one-line restatements, of which
`AlgebraicGeometry.Space.SmallEtale.exists_affine_ofArrows_over_ringedSite` is one.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe y z r m t u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

namespace SmallEtale

/-! ### Covering families by objects with affine underlying scheme, for the sheaves of modules -/

/-- **Every object of a slice of the small étale site carries a covering family by objects whose
underlying schemes are affine**, with the objects of the site spelled through the projection of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, which is the spelling the sheaves of modules on
the slice are indexed by.

This is `AlgebraicGeometry.Space.SmallEtale.exists_affine_ofArrows_over` restated; the two
spellings are definitionally equal, and restating is what keeps the locality argument below
inside one of them, so that instance search, which does not unfold the projection, succeeds
throughout. -/
theorem exists_affine_ofArrows_over_ringedSite (hF : IsAlgebraicSpace B S hS F)
    {V : (smallEtaleRingedSite B S hS F hF).C} (W : Over V) :
    ∃ (I : Type (u + 1)) (Y : I → Over V) (a : ∀ j, Y j ⟶ W),
      (∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Y j).left))) ∧
        Sieve.ofArrows Y a ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) W :=
  exists_affine_ofArrows_over B S hS F V W

/-! ### The sections over the objects of a class as a base change -/

/-- **The sections over the objects of a class are the base change of the sections over the
chart.**  For every object `W` of the slice at a chart `V` satisfying `Q`, the comparison carrying
`c ⊗ₜ n` to `c` times the restriction of `n` is a bijection from the base change, along the ring
map induced on global functions by the structural morphism of `W`, of the sections over `V` onto
the sections over `W`.

This is the content of the essential surjectivity of Stacks 03DX at the objects satisfying `Q`, in
the form the span condition consumes: its surjectivity is the span of the sections over `V` at
`W`, and its injectivity is what makes the relations between a family of generators spanned there
as well.

The module structures are introduced here rather than assumed, so that the comparison is the one a
consumer of this definition builds out of the restriction maps of the module: the ring of sections
of the coefficient sheaf of rings at an object of the slice is the ring of global functions on the
underlying scheme definitionally, the action of the ring of `V` on the sections over `W` is
restriction of scalars along the induced map, and the scalar tower is the identity. -/
def HasSectionBaseChangeOn (hF : IsAlgebraicSpace B S hS F)
    {V : (smallEtaleRingedSite B S hS F hF).C}
    (N : SheafOfModules.{m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V))
    (Q : Over V → Prop) : Prop :=
  ∀ W : Over V, Q W →
    let _ : Module Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj V), ⊤)
        (N.val.obj (op (Over.mk (𝟙 V)))) := inferInstanceAs (Module
      ((((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj
        (op (Over.mk (𝟙 V)))) (N.val.obj (op (Over.mk (𝟙 V)))))
    let _ : Module Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
        (N.val.obj (op W)) := inferInstanceAs (Module
      ((((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj (op W))
      (N.val.obj (op W)))
    let _ : Algebra Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj V), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left), ⊤) := RingHom.toAlgebra
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map
        (Over.mkIdTerminal.from W : W ⟶ Over.mk (𝟙 V)).left)).appTop.hom
    let _ : Module Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj V), ⊤) (N.val.obj (op W)) :=
      Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj V), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left), ⊤))
    have _ : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj V), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left), ⊤) (N.val.obj (op W)) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    Function.Bijective
      ((({ toFun := fun n => N.val.map (Over.mkIdTerminal.from W).op n
           map_add' := map_add (N.val.map (Over.mkIdTerminal.from W).op).hom
           map_smul' := fun c n =>
             (N.val.map_smul (Over.mkIdTerminal.from W).op c n).symm ▸ rfl } :
            N.val.obj (op (Over.mk (𝟙 V))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS F).obj V), ⊤)]
              N.val.obj (op W))).liftBaseChange
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left), ⊤))

/-- The module structure over the ring of global functions of `W` on the sections over `W`. -/
private abbrev moduleAt (hF : IsAlgebraicSpace B S hS F)
    {V : (smallEtaleRingedSite B S hS F hF).C}
    (N : SheafOfModules.{m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V))
    (W : Over V) :
    Module Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
      (N.val.obj (op W)) :=
  inferInstanceAs (Module
    ((((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj (op W)) (N.val.obj (op W)))

/-- The module structure over the ring of global functions of `V` on the sections over the chart. -/
private abbrev moduleChart (hF : IsAlgebraicSpace B S hS F)
    {V : (smallEtaleRingedSite B S hS F hF).C}
    (N : SheafOfModules.{m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)) :
    Module Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V), ⊤)
      (N.val.obj (op (Over.mk (𝟙 V)))) :=
  moduleAt B S hS F hF N (Over.mk (𝟙 V))

/-- The algebra structure on the global functions of `W` over those of the chart. -/
private noncomputable abbrev algebraAt (hF : IsAlgebraicSpace B S hS F)
    {V : (smallEtaleRingedSite B S hS F hF).C} (W : Over V) :
    Algebra Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤) :=
  RingHom.toAlgebra ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map
    (Over.mkIdTerminal.from W : W ⟶ Over.mk (𝟙 V)).left)).appTop.hom

/-- The sections over `W` as a module over the global functions of the chart. -/
private noncomputable abbrev moduleVia (hF : IsAlgebraicSpace B S hS F)
    {V : (smallEtaleRingedSite B S hS F hF).C}
    (N : SheafOfModules.{m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V))
    (W : Over V) :
    Module Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V), ⊤)
      (N.val.obj (op W)) :=
  letI := moduleAt B S hS F hF N W
  letI := algebraAt B S hS F hF W
  Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤))

private theorem isScalarTower_moduleVia (hF : IsAlgebraicSpace B S hS F)
    {V : (smallEtaleRingedSite B S hS F hF).C}
    (N : SheafOfModules.{m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V))
    (W : Over V) :
    letI := moduleAt B S hS F hF N W
    letI := algebraAt B S hS F hF W
    letI := moduleVia B S hS F hF N W
    IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
      (N.val.obj (op W)) := by
  let := moduleAt B S hS F hF N W
  let := algebraAt B S hS F hF W
  let := moduleVia B S hS F hF N W
  exact IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- Restriction of sections from the chart to `W`, linear over the global functions of the chart. -/
private noncomputable def restrictLinear (hF : IsAlgebraicSpace B S hS F)
    {V : (smallEtaleRingedSite B S hS F hF).C}
    (N : SheafOfModules.{m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V))
    (W : Over V) :
    letI := moduleChart B S hS F hF N
    letI := moduleVia B S hS F hF N W
    N.val.obj (op (Over.mk (𝟙 V))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)] N.val.obj (op W) :=
  letI := moduleChart B S hS F hF N
  letI := moduleVia B S hS F hF N W
  { toFun := fun n => N.val.map (Over.mkIdTerminal.from W).op n
    map_add' := map_add (N.val.map (Over.mkIdTerminal.from W).op).hom
    map_smul' := fun c n => (N.val.map_smul (Over.mkIdTerminal.from W).op c n).symm ▸ rfl }

/-- A morphism of sheaves of modules on the sections over the chart, linear over the global
functions of the chart. -/
private noncomputable def appLinearChart (hF : IsAlgebraicSpace B S hS F)
    {V : (smallEtaleRingedSite B S hS F hF).C}
    {M N : SheafOfModules.{m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)}
    (f : M ⟶ N) :
    letI := moduleChart B S hS F hF M
    letI := moduleChart B S hS F hF N
    M.val.obj (op (Over.mk (𝟙 V))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)] N.val.obj (op (Over.mk (𝟙 V))) :=
  letI := moduleChart B S hS F hF M
  letI := moduleChart B S hS F hF N
  { toFun := fun q => f.val.app (op (Over.mk (𝟙 V))) q
    map_add' := map_add (f.val.app (op (Over.mk (𝟙 V)))).hom
    map_smul' := fun c q => (f.val.app (op (Over.mk (𝟙 V)))).hom.map_smul c q }

/-- A morphism of sheaves of modules on the sections over `W`, linear over the global functions of
`W`. -/
private noncomputable def appLinear (hF : IsAlgebraicSpace B S hS F)
    {V : (smallEtaleRingedSite B S hS F hF).C}
    {M N : SheafOfModules.{m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)}
    (f : M ⟶ N) (W : Over V) :
    letI := moduleAt B S hS F hF M W
    letI := moduleAt B S hS F hF N W
    M.val.obj (op W) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left), ⊤)] N.val.obj (op W) :=
  letI := moduleAt B S hS F hF M W
  letI := moduleAt B S hS F hF N W
  { toFun := fun q => f.val.app (op W) q
    map_add' := map_add (f.val.app (op W)).hom
    map_smul' := fun c q => (f.val.app (op W)).hom.map_smul c q }

/-- The comparison for a coproduct of copies of the lifted structure sheaf, between two objects with
affine underlying scheme, is bijective. -/
private theorem bijective_liftBaseChange_restrictLinear (hF : IsAlgebraicSpace B S hS F)
    {V : (smallEtaleRingedSite B S hS F hF).C} {I₂ : Type y}
    {P₂ : SheafOfModules.{max t u}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)}
    (ι₂ : ∀ _ : I₂, SheafOfModules.uliftForPresentation.{u + 1, u, u, u, t}
      (SheafOfModules.unit
        (((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)).over V)) ⟶ P₂)
    (hP₂ : IsColimit (Cofan.mk P₂ ι₂))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V)))
    (W : Over V) (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left))) :
    letI := moduleChart B S hS F hF P₂
    letI := moduleAt B S hS F hF P₂ W
    letI := algebraAt B S hS F hF W
    letI := moduleVia B S hS F hF P₂ W
    haveI := isScalarTower_moduleVia B S hS F hF P₂ W
    Function.Bijective ((restrictLinear B S hS F hF P₂ W).liftBaseChange
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)) := by
  let := moduleChart B S hS F hF P₂
  let := moduleAt B S hS F hF P₂ W
  let := algebraAt B S hS F hF W
  let := moduleVia B S hS F hF P₂ W
  have := isScalarTower_moduleVia B S hS F hF P₂ W
  exact SheafOfModules.bijective_liftBaseChange_of_tautBasis ι₂
    (Over.mkIdTerminal.from W : W ⟶ Over.mk (𝟙 V))
    Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V), ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
    (tautBasisOfIsAffineCoeffs B S hS F hF ι₂ hP₂ (Over.mk (𝟙 V)) hV
      (sectionRingEquivGamma B S hS F hF (Over.mk (𝟙 V))) (fun _ _ => rfl))
    (tautBasisOfIsAffineCoeffs B S hS F hF ι₂ hP₂ W hW
      (sectionRingEquivGamma B S hS F hF W) (fun _ _ => rfl))
    (fun i => tautBasisOfIsAffineCoeffs_apply B S hS F hF ι₂ hP₂ (Over.mk (𝟙 V)) hV _ _ i)
    (fun i => tautBasisOfIsAffineCoeffs_apply B S hS F hF ι₂ hP₂ W hW _ _ i)
    (restrictLinear B S hS F hF P₂ W) fun _ => rfl

section Span

variable (hF : IsAlgebraicSpace B S hS F) {V : (smallEtaleRingedSite B S hS F hF).C}
  {N : SheafOfModules.{m}
    (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)}
  {Q : Over V → Prop}

/-- **The sections over an object where the comparison is surjective are combinations of the
restrictions of the sections over the chart.**  Every section over such an object is a
combination, over the ring of sections of the structure sheaf there, of restrictions of sections
over the chart the slice is taken at.

This is `SheafOfModules.globalSectionSpan_eq_top_of_baseChangeEquiv` applied to the comparison the
hypothesis provides; only its surjectivity is used, and nothing is assumed of the object beyond
membership in the class.  It is the generators half of the span condition at one object. -/
theorem globalSectionSpan_eq_top_of_hasSectionBaseChangeOn
    (hN : HasSectionBaseChangeOn B S hS F hF N Q) (W : Over V) (hW : Q W) :
    N.globalSectionSpan (Over.mkIdTerminal (X := V)) W = ⊤ := by
  let := moduleChart B S hS F hF N
  let := moduleAt B S hS F hF N W
  let := algebraAt B S hS F hF W
  let := moduleVia B S hS F hF N W
  have := isScalarTower_moduleVia B S hS F hF N W
  exact SheafOfModules.globalSectionSpan_eq_top_of_baseChangeEquiv (Over.mkIdTerminal (X := V)) N
    Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V), ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
    (sectionRingEquivGamma B S hS F hF W).symm.toRingHom (fun _ _ => rfl)
    ((restrictLinear B S hS F hF N W).liftBaseChange Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left), ⊤))
    (hN W hW).2 fun n => by rw [LinearMap.liftBaseChange_tmul, one_smul]; rfl

end Span


section Kernel

variable (hF : IsAlgebraicSpace B S hS F) {V : (smallEtaleRingedSite B S hS F hF).C}
  {N : SheafOfModules.{max t u}
    (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)}
  {Q : Over V → Prop}

/-- **The relations among the sections of a covering of the module over an object of the class with
affine underlying scheme are combinations of the relations over the chart.**

Let `b₂ : P₂ ⟶ N` be a morphism onto `N` from a coproduct of copies of the universe lift of the
structure sheaf which is surjective on the sections over the chart `V` the slice is taken at,
whose underlying scheme is affine, and let `k : Z ⟶ P₂` be a kernel of it.  Then the sections of
`Z` over an object `W` of the class with affine underlying scheme are combinations, over the ring
of sections of the structure sheaf there, of restrictions of its sections over `V`.

The module-theoretic content is `Module.BaseChange.mem_span_image_ker_of_liftBaseChange`, whose
injectivity hypothesis for the comparison of `N` is the hypothesis of this theorem and whose
surjectivity hypothesis for the comparison of `P₂` is
`SheafOfModules.bijective_liftBaseChange_of_tautBasis` at the two objects with affine underlying
scheme.  The sections of `Z` are read off from the limit fork by
`SheafOfModules.injective_val_app_of_isLimit_kernelFork` and
`SheafOfModules.mem_range_val_app_of_isLimit_kernelFork`, so that a relation over `W` is a
combination of restrictions of relations over `V` precisely because `b₂` is surjective on the
sections over `V`: without that surjectivity the tensor product is not right exact at the kernel
and the conclusion fails already for modules. -/
theorem globalSectionSpan_eq_top_ker_of_hasSectionBaseChangeOn
    (hN : HasSectionBaseChangeOn B S hS F hF N Q) {I₂ : Type y}
    {P₂ Z : SheafOfModules.{max t u}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)}
    (ι₂ : ∀ _ : I₂, SheafOfModules.uliftForPresentation.{u + 1, u, u, u, t}
      (SheafOfModules.unit
        (((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)).over V)) ⟶ P₂)
    (hP₂ : IsColimit (Cofan.mk P₂ ι₂)) (b₂ : P₂ ⟶ N)
    (hsurj₂ : Function.Surjective (b₂.val.app (op (Over.mk (𝟙 V)))))
    (k : Z ⟶ P₂) (hk : k ≫ b₂ = 0) (hZ : IsLimit (KernelFork.ofι k hk))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V)))
    (W : Over V) (hQW : Q W)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left))) :
    Z.globalSectionSpan (Over.mkIdTerminal (X := V)) W = ⊤ := by
  let := moduleChart B S hS F hF P₂
  let := moduleChart B S hS F hF N
  let := moduleAt B S hS F hF P₂ W
  let := moduleAt B S hS F hF N W
  let := moduleAt B S hS F hF Z W
  let := algebraAt B S hS F hF W
  let := moduleVia B S hS F hF P₂ W
  let := moduleVia B S hS F hF N W
  have := isScalarTower_moduleVia B S hS F hF P₂ W
  have := isScalarTower_moduleVia B S hS F hF N W
  have hP₂bij := bijective_liftBaseChange_restrictLinear B S hS F hF ι₂ hP₂ hV W hW
  refine Submodule.eq_top_iff'.2 fun zz => ?_
  have hzk : b₂.val.app (op W) (k.val.app (op W) zz) = 0 := by
    have h := congr($(hk).val.app (op W) zz)
    rwa [SheafOfModules.comp_val] at h
  have hkey := Module.BaseChange.mem_span_image_ker_of_liftBaseChange
    (A := Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V), ⊤))
    (Bc := Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left), ⊤))
    (PT := P₂.val.obj (op (Over.mk (𝟙 V)))) (NT := N.val.obj (op (Over.mk (𝟙 V))))
    (PW := P₂.val.obj (op W)) (NW := N.val.obj (op W)) (appLinearChart B S hS F hF b₂)
    (appLinear B S hS F hF b₂ W)
    (restrictLinear B S hS F hF P₂ W) (restrictLinear B S hS F hF N W)
    (fun q => (PresheafOfModules.naturality_apply b₂.val
      (Over.mkIdTerminal.from W).op q).symm)
    hP₂bij.2 (hN W hQW).1 hsurj₂ hzk
  have hspan : ∀ q ∈ Submodule.span Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
      (restrictLinear B S hS F hF P₂ W ''
        (LinearMap.ker (appLinearChart B S hS F hF b₂) : Set (P₂.val.obj (op (Over.mk (𝟙 V)))))),
      ∃ ζ ∈ Z.globalSectionSpan (Over.mkIdTerminal (X := V)) W, k.val.app (op W) ζ = q := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨q₀, hq₀, rfl⟩ := hq
      obtain ⟨ζ₀, hζ₀⟩ := SheafOfModules.mem_range_val_app_of_isLimit_kernelFork hZ
        (op (Over.mk (𝟙 V))) (show b₂.val.app (op (Over.mk (𝟙 V))) q₀ = 0 from hq₀)
      refine ⟨Z.val.map (Over.mkIdTerminal.from W).op ζ₀,
        Submodule.subset_span ⟨ζ₀, rfl⟩, ?_⟩
      exact (PresheafOfModules.naturality_apply k.val (Over.mkIdTerminal.from W).op ζ₀).trans
        (congrArg (fun yy => P₂.val.map (Over.mkIdTerminal.from W).op yy) hζ₀)
    | zero => exact ⟨0, zero_mem _, map_zero (k.val.app (op W)).hom⟩
    | add q q' _ _ hζ hζ' =>
      obtain ⟨ζ, hζm, hζe⟩ := hζ
      obtain ⟨ζ', hζm', hζe'⟩ := hζ'
      exact ⟨ζ + ζ', add_mem hζm hζm', by
        rw [map_add (k.val.app (op W)).hom, hζe, hζe']⟩
    | smul c q _ hζ =>
      obtain ⟨ζ, hζm, hζe⟩ := hζ
      exact ⟨c • ζ, Submodule.smul_mem _ c hζm, by rw [map_smul, hζe]⟩
  obtain ⟨ζ, hζm, hζe⟩ := hspan _ hkey
  exact SheafOfModules.injective_val_app_of_isLimit_kernelFork hZ (op W) hζe ▸ hζm

end Kernel

section Surjectivity

variable (hF : IsAlgebraicSpace B S hS F) {V : (smallEtaleRingedSite B S hS F hF).C}
  [HasSheafify ((smallEtaleRingedSite B S hS F hF).J.over V) AddCommGrpCat.{max t u}]
  [((smallEtaleRingedSite B S hS F hF).J.over V).WEqualsLocallyBijective AddCommGrpCat.{max t u}]
  {N : SheafOfModules.{max t u}
    (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)}
  {Q : Over V → Prop}

/-- **An epimorphism onto the module from a coproduct of copies of the universe lift of the
structure sheaf is surjective on the sections over the chart the slice is taken at.**

This is the hypothesis `hsurj₂` of
`AlgebraicGeometry.Space.SmallEtale.globalSectionSpan_eq_top_ker_of_hasSectionBaseChangeOn`, and
it is neither formal nor an instance of the surjectivity of a presenting morphism: `b₂` is an
arbitrary epimorphism from a coproduct, not one whose kernel is known to be such a coproduct.

It is proved by faithfully flat descent.  An epimorphism of sheaves of modules is locally
surjective, so a section over the chart becomes a value of `b₂` on a covering sieve; that sieve is
intersected with the sieve of the given covering family of the chart, which is covering as well,
before `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_ofArrows_le_over` extracts from it
a finite family of objects with affine underlying scheme whose image in schemes is an fppf
covering family.  The members of that family therefore have affine underlying scheme and factor
through a member of the given family, so the hypothesis applies to them, and the product of their
rings of global functions is faithfully flat over the ring of the chart
(`AlgebraicGeometry.Space.SmallEtale.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage`).
The sections of the coproduct over a member are the base change of its sections over the chart by
`SheafOfModules.bijective_liftBaseChange_of_tautBasis`, so
`Module.BaseChange.mem_range_of_forall_mem_range_of_liftBaseChange` descends membership in the
image from the members to the chart, which is `SheafOfModules.JointlyDetectsRange`, and
`SheafOfModules.surjective_val_app_of_epi_of_jointlyDetectsRange` concludes. -/
theorem surjective_val_app_mkId_of_epi_of_hasSectionBaseChangeOn
    (hN : HasSectionBaseChangeOn B S hS F hF N Q)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V)))
    {ιv : Type z} {Y₀ : ιv → Over V} (g₀ : ∀ j, Y₀ j ⟶ Over.mk (𝟙 V))
    (hcov₀ : Sieve.ofArrows Y₀ g₀ ∈ ((smallEtaleRingedSite B S hS F hF).J.over V)
      (Over.mk (𝟙 V)))
    (hQfac : ∀ (W : Over V) (j : ιv), (W ⟶ Y₀ j) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left)) → Q W)
    {I₂ : Type y}
    {P₂ : SheafOfModules.{max t u}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)}
    (ι₂ : ∀ _ : I₂, SheafOfModules.uliftForPresentation.{u + 1, u, u, u, t}
      (SheafOfModules.unit
        (((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)).over V)) ⟶ P₂)
    (hP₂ : IsColimit (Cofan.mk P₂ ι₂)) (b₂ : P₂ ⟶ N) [Epi b₂] :
    Function.Surjective (b₂.val.app (op (Over.mk (𝟙 V)))) := by
  refine SheafOfModules.surjective_val_app_of_epi_of_jointlyDetectsRange.{0} b₂ fun Sv hSv => ?_
  obtain ⟨mm, Y, g, hYaff, hmem, hcov, hfppf⟩ :=
    exists_finite_affine_ofArrows_le_over B S hS F hF (Over.mk (𝟙 V)) hV
      (Sv ⊓ Sieve.ofArrows Y₀ g₀)
      (((smallEtaleRingedSite B S hS F hF).J.over V).intersection_covering hSv hcov₀)
  have hg : ∀ i, g i = Over.mkIdTerminal.from (Y i) :=
    fun i => (Over.mkIdTerminal (X := V)).hom_ext (g i) _
  have hQY : ∀ i, Q (Y i) := fun i => by
    obtain ⟨j, c, -⟩ := (Sieve.mem_ofArrows_iff Y₀ g₀ (g i)).1 (hmem i).2
    exact hQfac (Y i) j c (hYaff i)
  have hfppf' : Presieve.ofArrows
      (fun i => (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y i).left))
      (fun i => (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map
        (Over.mkIdTerminal.from (Y i) : Y i ⟶ Over.mk (𝟙 V)).left)) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Over.mk (𝟙 V) : Over V).left)) := by
    simpa only [hg] using hfppf
  refine ⟨Fin mm, Y, fun i => Over.mkIdTerminal.from (Y i),
    fun i => by simpa only [hg i] using (hmem i).1, fun nn hnn => ?_⟩
  let := moduleChart B S hS F hF P₂
  let := moduleChart B S hS F hF N
  let := fun i => moduleAt B S hS F hF P₂ (Y i)
  let := fun i => moduleAt B S hS F hF N (Y i)
  let := fun i => algebraAt B S hS F hF (Y i)
  let : ∀ i, Algebra Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Over.mk (𝟙 V) : Over V).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤) := fun i => algebraAt B S hS F hF (Y i)
  let := fun i => moduleVia B S hS F hF P₂ (Y i)
  let := fun i => moduleVia B S hS F hF N (Y i)
  have := fun i => isScalarTower_moduleVia B S hS F hF P₂ (Y i)
  have := fun i => isScalarTower_moduleVia B S hS F hF N (Y i)
  have hff : Module.FaithfullyFlat Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)
      (∀ i, Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤)) :=
    faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage B S hS F Y
      (fun i => Over.mkIdTerminal.from (Y i)) hV hYaff hfppf' fun _ => rfl
  exact Module.BaseChange.mem_range_of_forall_mem_range_of_liftBaseChange
    Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V), ⊤)
    (fun i => Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤))
    (PT := P₂.val.obj (op (Over.mk (𝟙 V)))) (NT := N.val.obj (op (Over.mk (𝟙 V))))
    (PW := fun i => P₂.val.obj (op (Y i))) (NW := fun i => N.val.obj (op (Y i)))
    (appLinearChart B S hS F hF b₂) (fun i => appLinear B S hS F hF b₂ (Y i))
    (fun i => restrictLinear B S hS F hF P₂ (Y i)) (fun i => restrictLinear B S hS F hF N (Y i))
    (fun i q => (PresheafOfModules.naturality_apply b₂.val
      (Over.mkIdTerminal.from (Y i)).op q).symm)
    (fun i => (bijective_liftBaseChange_restrictLinear B S hS F hF ι₂ hP₂ hV (Y i) (hYaff i)).2)
    (fun i => (hN (Y i) (hQY i)).1) fun i => by obtain ⟨q, hq⟩ := hnn i; exact ⟨q, hq⟩

end Surjectivity

/-! ### Locality of the two span conditions -/

section Locality

variable (hF : IsAlgebraicSpace B S hS F) (V : (smallEtaleRingedSite B S hS F hF).C)
  {R : Sheaf ((smallEtaleRingedSite B S hS F hF).J.over V) RingCat.{r}}
  {T : Over V} (hT : IsTerminal T)

/-- **Being locally spanned by global sections is a condition at the objects with affine
underlying scheme lying over the members of one covering family of the terminal object.**

A covering family `Y i ⟶ T` of the terminal object of a slice of the small étale site is given.
For an arbitrary object `U` of the slice, pulling that family's sieve back along the structural
morphism of `U` produces a covering sieve of `U` each of whose sources admits a morphism to some
`Y i`; such a source carries a covering family by objects with affine underlying scheme
(`AlgebraicGeometry.Space.SmallEtale.exists_affine_ofArrows_over_ringedSite`), whose members again
admit a morphism to that `Y i`, so the hypothesis makes the span everything there, and the span
condition holds at the source.  It then holds at `U` by the locality of the condition
(`SheafOfModules.isLocallySpannedBySectionsAt_of_sieve`). -/
theorem isLocallySpannedBySections_over_of_forall_affine_of_cover (N : SheafOfModules.{m} R)
    {ιv : Type z} (Y : ιv → Over V) (g : ∀ i, Y i ⟶ T)
    (hcov : Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) T)
    (h : ∀ (i : ιv) (W : Over V), IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left)) → (W ⟶ Y i) →
      N.globalSectionSpan hT W = ⊤) :
    N.IsLocallySpannedBySections hT := by
  refine SheafOfModules.isLocallySpannedBySections_of_forall_sieve hT N fun U => ?_
  refine ⟨(Sieve.ofArrows Y g).pullback (hT.from U),
    ((smallEtaleRingedSite B S hS F hF).J.over V).pullback_stable _ hcov,
    fun {Z} f hf => ?_⟩
  have hf' : Sieve.ofArrows Y g (f ≫ hT.from U) := hf
  rw [Sieve.mem_ofArrows_iff] at hf'
  obtain ⟨i, c, -⟩ := hf'
  obtain ⟨Iv, W, a, hWaff, hWcov⟩ := exists_affine_ofArrows_over_ringedSite B S hS F hF Z
  exact SheafOfModules.isLocallySpannedBySectionsAt_of_exists_cover hT N W a hWcov
    fun j => h i (W j) (hWaff j) (a j ≫ c)

/-- **The relations half of a global presentation with the objects restricted to those with
affine underlying scheme lying over the members of one covering family.**  This is
`SheafOfModules.hasLocallySpannedRelations_of_hasSpannedRelationsOn` whose locality criterion is
discharged by
`AlgebraicGeometry.Space.SmallEtale.isLocallySpannedBySections_over_of_forall_affine_of_cover`;
the class of testing objects is the objects with affine underlying scheme admitting a morphism to
a member of the family, which includes the members themselves. -/
theorem hasLocallySpannedRelations_over_of_cover (M : SheafOfModules.{m} R)
    {ιv : Type z} (Y : ιv → Over V) (g : ∀ i, Y i ⟶ T)
    (hcov : Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) T)
    (h : M.HasSpannedRelationsOn hT fun W => IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left)) ∧ ∃ i, Nonempty (W ⟶ Y i)) :
    M.HasLocallySpannedRelations hT :=
  SheafOfModules.hasLocallySpannedRelations_of_hasSpannedRelationsOn hT M _
    (fun Z hZ => isLocallySpannedBySections_over_of_forall_affine_of_cover B S hS F hF V hT Z Y g
      hcov fun i W hW a => hZ W ⟨hW, i, ⟨a⟩⟩) h

end Locality

/-! ### The two halves of the span condition at one chart -/

section Assembly

variable (hF : IsAlgebraicSpace B S hS F) {V : (smallEtaleRingedSite B S hS F hF).C}
  (M : SheafOfModules.{m}
    (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V))

/-- **The relations half of a global presentation in its unlocalised form, at the objects of the
class.**  The kernel of every covering of the universe lift of the module by a coproduct of copies
of the universe lift of the structure sheaf has its sections over an object of the class spanned
by the restrictions of its sections over the chart.

The two inputs are
`AlgebraicGeometry.Space.SmallEtale.globalSectionSpan_eq_top_ker_of_hasSectionBaseChangeOn` and
`AlgebraicGeometry.Space.SmallEtale.surjective_val_app_mkId_of_epi_of_hasSectionBaseChangeOn`,
which discharges its hypothesis that the covering be surjective on the sections over the chart.
The quantification is over every coproduct covering of the lift, not only the one a presentation
would provide, which is what `SheafOfModules.HasSpannedRelationsOn` asks for.

The covering family enters only through the surjectivity, and the class only has to contain the
objects with affine underlying scheme factoring through one of its members. -/
theorem hasSpannedRelationsOn_of_hasSectionBaseChangeOn
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V)))
    {Q : Over V → Prop}
    (hQaff : ∀ W : Over V, Q W → IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left)))
    {ιv : Type z} {Y : ιv → Over V} (g : ∀ j, Y j ⟶ Over.mk (𝟙 V))
    (hcov : Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) (Over.mk (𝟙 V)))
    (hQfac : ∀ (W : Over V) (j : ιv), (W ⟶ Y j) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left)) → Q W)
    (hM : HasSectionBaseChangeOn B S hS F hF
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, m, u + 1} M) Q) :
    M.HasSpannedRelationsOn (Over.mkIdTerminal (X := V)) Q := by
  have _ : HasSheafify ((smallEtaleRingedSite B S hS F hF).J.over V)
      AddCommGrpCat.{max (u + 1) m} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat ((smallEtaleRingedSite B S hS F hF).J.over V)
  have _ : ((smallEtaleRingedSite B S hS F hF).J.over V).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) m} :=
    GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat
      ((smallEtaleRingedSite B S hS F hF).J.over V)
  intro I₂ P₂ ι₂ hP₂ b₂ hb₂ Z k hk hZ W hW
  exact globalSectionSpan_eq_top_ker_of_hasSectionBaseChangeOn B S hS F hF hM ι₂ hP₂ b₂
    (surjective_val_app_mkId_of_epi_of_hasSectionBaseChangeOn B S hS F hF hM hV g hcov hQfac
      ι₂ hP₂ b₂) k hk hZ hV W hW (hQaff W hW)

/-- **The relations half of a global presentation at the objects with affine underlying scheme
lying over a member of a covering family.**  This is
`AlgebraicGeometry.Space.SmallEtale.hasSpannedRelationsOn_of_hasSectionBaseChangeOn` for the class
of objects of the slice with affine underlying scheme admitting a morphism to a member of the
family, which contains the members themselves and is the class the locality criterion of
`AlgebraicGeometry.Space.SmallEtale.hasLocallySpannedRelations_over_of_cover` tests. -/
theorem hasSpannedRelationsOn_over_of_hasSectionBaseChangeOn
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V)))
    {ιv : Type z} {Y : ιv → Over V} (g : ∀ j, Y j ⟶ Over.mk (𝟙 V))
    (hcov : Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) (Over.mk (𝟙 V)))
    (hM : HasSectionBaseChangeOn B S hS F hF
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, m, u + 1} M)
      fun W => IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left)) ∧ ∃ j, Nonempty (W ⟶ Y j)) :
    M.HasSpannedRelationsOn (Over.mkIdTerminal (X := V))
      fun W => IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left)) ∧ ∃ j, Nonempty (W ⟶ Y j) :=
  hasSpannedRelationsOn_of_hasSectionBaseChangeOn B S hS F hF M hV (fun _ h => h.1) g hcov
    (fun _ j c hW => ⟨hW, j, ⟨c⟩⟩) hM

/-- **The relations between any family of generators of the module are locally spanned by their
sections over the chart the slice is taken at.**  This is
`AlgebraicGeometry.Space.SmallEtale.hasSpannedRelationsOn_over_of_hasSectionBaseChangeOn` with the
passage from the objects with affine underlying scheme over the covering family to all objects
supplied by
`AlgebraicGeometry.Space.SmallEtale.hasLocallySpannedRelations_over_of_cover`. -/
theorem hasLocallySpannedRelations_of_hasSectionBaseChangeOn
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V)))
    {ιv : Type z} {Y : ιv → Over V} (g : ∀ j, Y j ⟶ Over.mk (𝟙 V))
    (hcov : Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) (Over.mk (𝟙 V)))
    (hM : HasSectionBaseChangeOn B S hS F hF
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, m, u + 1} M)
      fun W => IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left)) ∧ ∃ j, Nonempty (W ⟶ Y j)) :
    M.HasLocallySpannedRelations (Over.mkIdTerminal (X := V)) :=
  hasLocallySpannedRelations_over_of_cover B S hS F hF V (Over.mkIdTerminal (X := V)) M Y g hcov
    (hasSpannedRelationsOn_over_of_hasSectionBaseChangeOn B S hS F hF M hV g hcov hM)

/-- **The module is locally spanned by its sections over the chart the slice is taken at.**  The
span at an object with affine underlying scheme lying over a member of the family is
`AlgebraicGeometry.Space.SmallEtale.globalSectionSpan_eq_top_of_hasSectionBaseChangeOn` for the
universe lift, read for the module itself by
`SheafOfModules.down_mem_globalSectionSpan_of_mem_uliftForPresentation`; the passage to all
objects is
`AlgebraicGeometry.Space.SmallEtale.isLocallySpannedBySections_over_of_forall_affine_of_cover`.

Only surjectivity of the comparison is used, so this half of the span condition needs strictly
less than the relations half. -/
theorem isLocallySpannedBySections_of_hasSectionBaseChangeOn
    {ιv : Type z} {Y : ιv → Over V} (g : ∀ j, Y j ⟶ Over.mk (𝟙 V))
    (hcov : Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) (Over.mk (𝟙 V)))
    (hM : HasSectionBaseChangeOn B S hS F hF
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, m, u + 1} M)
      fun W => IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left)) ∧ ∃ j, Nonempty (W ⟶ Y j)) :
    M.IsLocallySpannedBySections (Over.mkIdTerminal (X := V)) :=
  isLocallySpannedBySections_over_of_forall_affine_of_cover B S hS F hF V
    (Over.mkIdTerminal (X := V)) M Y g hcov fun j W hW a => by
      refine Submodule.eq_top_iff'.2 fun n => ?_
      refine SheafOfModules.down_mem_globalSectionSpan_of_mem_uliftForPresentation
        (Over.mkIdTerminal (X := V)) M W (x := ULift.up n) ?_
      rw [globalSectionSpan_eq_top_of_hasSectionBaseChangeOn B S hS F hF hM W ⟨hW, j, ⟨a⟩⟩]
      exact Submodule.mem_top

/-- **Both halves of the span condition at a chart with affine underlying scheme, from the base
change of the sections.**  This is what a global presentation of a module on the slice is
assembled from, with quasi-coherence of the module replaced by the base-change comparisons at the
objects with affine underlying scheme lying over the members of one covering family of the
chart. -/
theorem isLocallySpannedBySections_and_hasLocallySpannedRelations_of_hasSectionBaseChangeOn
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V)))
    {ιv : Type z} {Y : ιv → Over V} (g : ∀ j, Y j ⟶ Over.mk (𝟙 V))
    (hcov : Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) (Over.mk (𝟙 V)))
    (hM : HasSectionBaseChangeOn B S hS F hF
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, m, u + 1} M)
      fun W => IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left)) ∧ ∃ j, Nonempty (W ⟶ Y j)) :
    M.IsLocallySpannedBySections (Over.mkIdTerminal (X := V)) ∧
      M.HasLocallySpannedRelations (Over.mkIdTerminal (X := V)) :=
  ⟨isLocallySpannedBySections_of_hasSectionBaseChangeOn B S hS F hF M g hcov hM,
    hasLocallySpannedRelations_of_hasSectionBaseChangeOn B S hS F hF M hV g hcov hM⟩

/-- **A global presentation of a module on the slice at a chart with affine underlying scheme,
from the base change of the sections.**  The two span conditions make the module generated by its
sections over the chart and the relations between any family of generators generated likewise
(`SheafOfModules.isGeneratedByUnit_of_isLocallySpannedBySections` and
`SheafOfModules.hasGeneratedRelations_of_isLocallySpannedBySections`), and a module with both
properties has a global presentation
(`SheafOfModules.HasGlobalPresentation.of_isGeneratedByUnit`). -/
theorem hasGlobalPresentation_of_hasSectionBaseChangeOn
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V)))
    {ιv : Type z} {Y : ιv → Over V} (g : ∀ j, Y j ⟶ Over.mk (𝟙 V))
    (hcov : Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) (Over.mk (𝟙 V)))
    (hM : HasSectionBaseChangeOn B S hS F hF
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, m, u + 1} M)
      fun W => IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left)) ∧ ∃ j, Nonempty (W ⟶ Y j)) :
    M.HasGlobalPresentation :=
  SheafOfModules.HasGlobalPresentation.of_isGeneratedByUnit
    (SheafOfModules.isGeneratedByUnit_of_isLocallySpannedBySections _
      (isLocallySpannedBySections_of_hasSectionBaseChangeOn B S hS F hF M g hcov hM))
    (SheafOfModules.hasGeneratedRelations_of_isLocallySpannedBySections _ _
      (hasLocallySpannedRelations_of_hasSectionBaseChangeOn B S hS F hF M hV g hcov hM))

end Assembly

end SmallEtale

end AlgebraicGeometry.Space

end
