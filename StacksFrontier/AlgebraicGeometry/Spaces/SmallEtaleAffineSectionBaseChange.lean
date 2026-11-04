module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentAffineChartPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineSpannedSections
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineSectionBaseChangeExit

/-!
# Global presentations on the affine charts of the small étale site

This file discharges, for the small étale ringed site of an algebraic space, the one condition on
which the span conditions of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineSpannedSections` rest: a quasi-coherent
`𝒪_F`-module has, over every chart `V` whose underlying scheme is affine, a covering family of
that chart over whose members with affine underlying scheme its sections are the base change of
its sections over `V`.  With that condition discharged a quasi-coherent module restricted to such
a chart has a global presentation, which is
`AlgebraicGeometry.Space.hasAffineChartPresentations`.

The comparison asked for is between the sections over the chart and the sections over an object
with affine underlying scheme lying over a member of the covering family, and it is **not**
obtainable from a global presentation at the chart: quasi-coherence never provides one there.  It
is obtained in two steps instead — flat descent along the family from the chart to a member, then
a presentation at a member of the family which quasi-coherence does provide — composed by
`Module.BaseChange.bijective_liftBaseChange_trans`.

The family is extracted from the one quasi-coherence provides: that one is neither finite nor
affine, so `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_ofArrows_le_over` replaces it
by a finite family of objects with affine underlying scheme whose image in schemes is an fppf
covering family, each member of which factors through a member of the original one by
`CategoryTheory.Sieve.mem_ofArrows_iff`.  No presentation is claimed on the slice at a member of
the extracted family; what the factorisation supplies is the hypothesis of
`AlgebraicGeometry.Space.SmallEtale`'s
`bijective_liftBaseChange_of_hasGlobalPresentation_overChart`, whose base is the chart underlying
the member of the original family and whose two objects are the ones compared.

The descent along the extracted family is
`SheafOfModules.bijective_liftBaseChange_of_family_cancelBaseChange`, whose two inputs over the
double and the triple overlaps are that same statement.  The rings are the rings of global
functions on the underlying schemes, the ring of an overlap is exhibited as a tensor product by
`AlgebraicGeometry.Space.SmallEtale.exists_ringEquivTensorGamma_of_isPullback`, the identities
between the induced maps are
`AlgebraicGeometry.Space.SmallEtale.appTopGamma_comp_apply_of_eq`, and the faithful flatness of
the product of the rings of the members is
`AlgebraicGeometry.Space.SmallEtale.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage`.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.exists_affine_family_overlaps_ringedSite`: **a family of
  objects of a slice of the small étale site with affine underlying scheme has affine double and
  triple overlaps**, at the spelling the sheaves of modules on the slice are indexed by.
* `AlgebraicGeometry.Space.SmallEtale`'s
  `exists_hasSectionBaseChangeOn_of_isQuasicoherentOnSite`: **a quasi-coherent `𝒪_F`-module has a
  covering family of a chart with affine underlying scheme over whose affine objects its sections
  are the base change of its sections over the chart.**
* `AlgebraicGeometry.Space.hasAffineChartPresentations`: **a quasi-coherent `𝒪_F`-module has a
  global presentation after restriction to a chart whose underlying scheme is affine**, with no
  hypothesis.
* `AlgebraicGeometry.Space.hasAffineChartSurjectivePresentations`: **on the slice at such a chart
  the presenting morphism of a global presentation is surjective on the sections over the chart**,
  with no hypothesis.
* `AlgebraicGeometry.Space.isClosedUnderDirectSumsQuasicoherent`,
  `AlgebraicGeometry.Space.isClosedUnderCokernels` and
  `AlgebraicGeometry.Space.isClosedUnderColimitsOfShape`: **the direct-sum, the cokernel and the
  colimit clauses of Stacks 03M1 for the small étale ringed site of an algebraic space, with no
  hypothesis.**
* `AlgebraicGeometry.Space.existsUnique_quasicoherentSubobject_of_isClosedUnderKernels` and
  `AlgebraicGeometry.Space.exists_greatest_quasicoherentSubobject_of_isClosedUnderKernels`:
  **Stacks 04CK with two of the three closure clauses of Stacks 03M1 discharged**, the kernel
  clause being the one hypothesis left.

## Implementation notes

No `@[stacks 03M1]` tag is carried: Stacks 03M1 has six clauses — direct sums, arbitrary colimits,
kernels and cokernels, two-out-of-three in a short exact sequence, tensor products and internal
homs — and the kernel clause is not among the ones proved here.  No `@[stacks 04CK]` tag is
carried either: the two statements of Stacks 04CK below still assume the kernel clause, which the
source does not, and a statement carrying a hypothesis the source does not have is weaker than the
source.  The kernel clause needs flat base change of a kernel along an étale morphism of affine
charts, whose two inputs are in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineKernelBaseChange`.

The module is given on the whole small étale site rather than only on the slice at the chart, and
that is what keeps `CategoryTheory.Over.iteratedSliceEquiv` out of the argument: the sections of a
restriction at an object of a slice are the sections of the module at the underlying chart, so a
presentation on the slice at a member of the covering family is read at the canonical objects
directly.  The one place the two readings have to be identified is
`AlgebraicGeometry.Space.SmallEtale`'s
`bijective_liftBaseChange_of_hasGlobalPresentation_overChart`, which does it once.

The semilinearity of restriction along a morphism of the slice is the sheaf of modules' own
`PresheafOfModules.map_smul`, because the ring of sections of the coefficient sheaf of rings at an
object is the ring of global functions on the underlying scheme and its restriction map is the
induced map of global functions.  The counterpart for a fixed module universe is
`AlgebraicGeometry.Space.SmallEtale.restrictₛₗ_smul_appTopGamma`; it is not used here, the module
universe being left free.  For the same reason the two scalar towers over an overlap whose legs
are a projection onto a member and the structural morphism of another member are written out from
`AlgebraicGeometry.Space.SmallEtale.appTopGamma_comp_apply_of_eq` rather than taken from
`AlgebraicGeometry.Space.SmallEtale.isScalarTower_appTopGamma`.

The rings of global functions on the scheme underlying the chart are written both as the chart
itself and as the underlying object of the terminal object of the slice.  The two are the same
ring definitionally but instance search does not identify them, so each algebra and module
structure over that ring whose consumer is stated at the second spelling is bound a second time
with the same value.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 04CK](https://stacks.math.columbia.edu/tag/04CK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe z m u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

namespace SmallEtale

/-- Module structures pulled back along `R → A → C` and `A → C` form a scalar tower when the ring
maps compose. -/
private theorem isScalarTower_compHom_of_algebraMap_comp {R A C M : Type*} [CommRing R]
    [CommRing A] [CommRing C] [AddCommGroup M] [Module C M] [Algebra R A] [Algebra R C]
    [Algebra A C] (h : ∀ r, algebraMap A C (algebraMap R A r) = algebraMap R C r) :
    letI := Module.compHom M (algebraMap R C)
    letI := Module.compHom M (algebraMap A C)
    IsScalarTower R A M :=
  letI := Module.compHom M (algebraMap R C)
  letI := Module.compHom M (algebraMap A C)
  IsScalarTower.of_algebraMap_smul fun r n => congrArg (· • n) (h r)

/-- **A family of objects of a slice of the small étale site with affine underlying scheme over an
object with affine underlying scheme has affine double and triple overlaps**, with the objects of
the site spelled through the projection of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, which is the spelling the sheaves of modules on
the slice are indexed by.

This is `AlgebraicGeometry.Space.SmallEtale.exists_affine_family_overlaps` restated; the two
spellings are definitionally equal, and restating is what keeps the descent below inside one of
them, so that instance search, which does not unfold the projection, succeeds throughout. -/
theorem exists_affine_family_overlaps_ringedSite (hF : IsAlgebraicSpace B S hS F)
    {V : (smallEtaleRingedSite B S hS F hF).C} {T : Over V}
    {ι : Type*} (Y : ι → Over V) (g : ∀ i, Y i ⟶ T)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj T.left)))
    (hY : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Y i).left))) :
    ∃ (Pb : ι → ι → Over V) (Pb₃ : ι → ι → ι → Over V)
      (pr₁ : ∀ i j, Pb i j ⟶ Y i) (pr₂ : ∀ i j, Pb i j ⟶ Y j) (δ : ∀ i, Y i ⟶ Pb i i)
      (q : ∀ i j k, Pb₃ i j k ⟶ Y i) (t₁₂ : ∀ i j k, Pb₃ i j k ⟶ Pb i j)
      (t₁₃ : ∀ i j k, Pb₃ i j k ⟶ Pb i k) (t₂₃ : ∀ i j k, Pb₃ i j k ⟶ Pb j k),
      (∀ i j, IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Pb i j).left))) ∧
      (∀ i j k, IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Pb₃ i j k).left))) ∧
      (∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (g i) (g j)) ∧
      (∀ i j k, IsPullback (q i j k) (t₂₃ i j k) (g i) (pr₁ j k ≫ g j)) ∧
      (∀ i, δ i ≫ pr₁ i i = 𝟙 (Y i)) ∧ (∀ i, δ i ≫ pr₂ i i = 𝟙 (Y i)) ∧
      (∀ i j k, t₁₂ i j k ≫ pr₁ i j = q i j k) ∧
      (∀ i j k, t₁₃ i j k ≫ pr₁ i k = q i j k) ∧
      (∀ i j k, t₁₂ i j k ≫ pr₂ i j = t₂₃ i j k ≫ pr₁ j k) ∧
      (∀ i j k, t₁₃ i j k ≫ pr₂ i k = t₂₃ i j k ≫ pr₂ j k) :=
  exists_affine_family_overlaps B S hS F Y g hT hY

/-- **The sections over an object of a slice lying over an object on which the module is presented
are the base change of the sections over that object**, with the two coefficient rings written as
the rings of global functions on the underlying schemes and the module structures over them
written out.

This is `AlgebraicGeometry.Space.SmallEtale`'s
`bijective_liftBaseChange_of_hasGlobalPresentation_overChart` with the two commutative rings it
takes as data specialised to those rings, the ring identifications specialised to
`AlgebraicGeometry.Space.SmallEtale.sectionRingEquivGamma` and the module structures over them
bound as the consumers below hold them: the action of the ring of global functions on an object is
the action of the ring of sections of the coefficient sheaf of rings there, and the action of the
ring of the target of a morphism is restriction of scalars along the induced map.

Specialising once is what keeps each of the three places the comparison is needed — the double and
the triple overlaps of a covering family, and an object lying over a member of it — a single
line. -/
theorem bijective_liftBaseChange_gamma_of_hasGlobalPresentation_overChart
    (hF : IsAlgebraicSpace B S hS F)
    (M : SheafOfModules.{m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
    {V V' : (smallEtaleRingedSite B S hS F hF).C} (hM : (M.over V').HasGlobalPresentation)
    (N : SheafOfModules.{m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V))
    (hN : N = M.over V)
    {T W : Over V} (cT : T.left ⟶ V') (cW : W.left ⟶ V') (h : W ⟶ T)
    (hcl : h.left ≫ cT = cW)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj T.left)))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left))) :
    let _mT : Module Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj T.left), ⊤) (N.val.obj (op T)) :=
      inferInstanceAs (Module
        ((((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj (op T))
        (N.val.obj (op T)))
    let _mW : Module Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤) (N.val.obj (op W)) :=
      inferInstanceAs (Module
        ((((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj (op W))
        (N.val.obj (op W)))
    let _algTW : Algebra Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj T.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left), ⊤) :=
      RingHom.toAlgebra ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map h.left)).appTop.hom
    let _mWT : Module Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj T.left), ⊤) (N.val.obj (op W)) :=
      Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj T.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left), ⊤))
    have _ : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj T.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left), ⊤) (N.val.obj (op W)) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    ∀ r : N.val.obj (op T) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj T.left), ⊤)] N.val.obj (op W),
      (∀ n, r n = N.val.restrictₛₗ h.op n) →
      Function.Bijective (r.liftBaseChange Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤)) := by
  intro mT mW algTW mWT twTW r hr
  exact bijective_liftBaseChange_of_hasGlobalPresentation_overChart B S hS F hF M hM N hN
    cT cW h hcl hT hW
    Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj T.left), ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
    (sectionRingEquivGamma B S hS F hF T) (fun _ _ => rfl)
    (sectionRingEquivGamma B S hS F hF W) (fun _ _ => rfl) (fun _ => rfl) r hr

/-- **The sections over a member of a finite flat covering family of a chart with affine
underlying scheme, by objects with affine underlying scheme each factoring through a chart on
which the module is presented, are the base change of the sections over the chart.**

This is `SheafOfModules.bijective_liftBaseChange_of_family_cancelBaseChange` for the small étale
site, with every hypothesis discharged.  The double and triple overlaps of the family and their
affineness are
`AlgebraicGeometry.Space.SmallEtale.exists_affine_family_overlaps_ringedSite`, the ring of an
overlap is exhibited as a tensor product of the rings of its two factors by
`AlgebraicGeometry.Space.SmallEtale.exists_ringEquivTensorGamma_of_isPullback`, the identities
between the induced maps of global functions are
`AlgebraicGeometry.Space.SmallEtale.appTopGamma_comp_apply_of_eq`, the product of the rings of the
members is faithfully flat over the ring of the chart by
`AlgebraicGeometry.Space.SmallEtale.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage`, and
the two base-change comparisons over the overlaps are
`AlgebraicGeometry.Space.SmallEtale`'s
`bijective_liftBaseChange_of_hasGlobalPresentation_overChart` — which is where the factorisation
of a member through a chart carrying a presentation is used, and the only place a presentation
enters.

The module structures the comparison is stated over are written into the statement, as in
`AlgebraicGeometry.Space.SmallEtale.HasSectionBaseChangeOn`, so that the comparison it speaks of
is the one a consumer builds out of the restriction maps of the module; they are bound uniformly
in the object where the object alone determines them. -/
theorem bijective_liftBaseChange_mem_of_hasGlobalPresentation_family
    (hF : IsAlgebraicSpace B S hS F)
    (M : SheafOfModules.{m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
    {V : (smallEtaleRingedSite B S hS F hF).C}
    (N : SheafOfModules.{m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V))
    (hN : N = M.over V)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V)))
    {ι : Type z} [Finite ι] (Y : ι → Over V) (g : ∀ i, Y i ⟶ Over.mk (𝟙 V))
    (hYaff : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Y i).left)))
    (hcov : Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) (Over.mk (𝟙 V)))
    (hfppf : Presieve.ofArrows
        (fun i => (BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Y i).left))
        (fun i => (BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS F).map (g i).left)) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Over.mk (𝟙 V) : Over V).left)))
    (V' : ι → (smallEtaleRingedSite B S hS F hF).C) (c : ∀ i, (Y i).left ⟶ V' i)
    (hpres : ∀ i, (M.over (V' i)).HasGlobalPresentation) :
    let _mSheaf : ∀ Z : Over V, Module Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj Z.left), ⊤) (N.val.obj (op Z)) := fun Z =>
      inferInstanceAs (Module
        ((((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj (op Z))
        (N.val.obj (op Z)))
    let _mT : Module Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj V), ⊤)
        (N.val.obj (op (Over.mk (𝟙 V)))) := inferInstanceAs (Module
      ((((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj
        (op (Over.mk (𝟙 V)))) (N.val.obj (op (Over.mk (𝟙 V)))))
    let _algY : ∀ i, Algebra Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj V), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤) := fun i =>
      RingHom.toAlgebra ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map (g i).left)).appTop.hom
    let _mYA : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj V), ⊤) (N.val.obj (op (Y i))) := fun i =>
      Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj V), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤))
    have _twY : ∀ i, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj V), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤)
        (N.val.obj (op (Y i))) := fun _ =>
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    ∀ i, Function.Bijective
      ((({ toFun := fun n => N.val.map (g i).op n
           map_add' := map_add (N.val.map (g i).op).hom
           map_smul' := fun cc nn => N.val.map_smul (g i).op cc nn } :
          N.val.obj (op (Over.mk (𝟙 V))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS F).obj V), ⊤)]
            N.val.obj (op (Y i)))).liftBaseChange
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤)) := by
  intro mSheaf mT algY mYA twY
  obtain ⟨Pb, Pb₃, pr₁, pr₂, δ, q, t₁₂, t₁₃, t₂₃, hPbaff, hPb₃aff, hpb, hpb₃,
    hδ₁, hδ₂, hq₁₂, hq₁₃, hov₂, hov₃⟩ :=
    exists_affine_family_overlaps_ringedSite B S hS F hF Y g hV hYaff
  -- the four layers of rings, and the algebra structures between them
  let algY' : ∀ i, Algebra Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Over.mk (𝟙 V) : Over V).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤) := algY
  let algD : ∀ i j, Algebra Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Pb i j).left), ⊤) := fun i j =>
    RingHom.toAlgebra ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS F).map (pr₁ i j ≫ g i).left)).appTop.hom
  let algD' : ∀ i j, Algebra Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Over.mk (𝟙 V) : Over V).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Pb i j).left), ⊤) := algD
  let algBD : ∀ i j, Algebra Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Y j).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Pb i j).left), ⊤) := fun i j =>
    RingHom.toAlgebra ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS F).map (pr₂ i j).left)).appTop.hom
  let algD₃ : ∀ i j k, Algebra Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Pb₃ i j k).left), ⊤) := fun i j k =>
    RingHom.toAlgebra ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS F).map (q i j k ≫ g i).left)).appTop.hom
  let algD₃' : ∀ i j k, Algebra Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Over.mk (𝟙 V) : Over V).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Pb₃ i j k).left), ⊤) := algD₃
  let algDD₃ : ∀ i j k, Algebra Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Pb j k).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Pb₃ i j k).left), ⊤) := fun i j k =>
    RingHom.toAlgebra ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS F).map (t₂₃ i j k).left)).appTop.hom
  -- the module structures on the sections
  let mPA : ∀ i j, Module Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)
      (N.val.obj (op (Pb i j))) := fun i j => Module.compHom _
    (algebraMap Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Pb i j).left), ⊤))
  let mPA' : ∀ i j, Module Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Over.mk (𝟙 V) : Over V).left), ⊤)
      (N.val.obj (op (Pb i j))) := mPA
  let mPB : ∀ i j, Module Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Y j).left), ⊤)
      (N.val.obj (op (Pb i j))) := fun i j => Module.compHom _
    (algebraMap Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y j).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Pb i j).left), ⊤))
  have twPBD : ∀ i j, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Y j).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Pb i j).left), ⊤)
      (N.val.obj (op (Pb i j))) := fun _ _ =>
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twPAD : ∀ i j, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Pb i j).left), ⊤)
      (N.val.obj (op (Pb i j))) := fun _ _ =>
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twPAB : ∀ i j, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y j).left), ⊤)
      (N.val.obj (op (Pb i j))) := fun i j =>
    isScalarTower_compHom_of_algebraMap_comp fun a =>
      appTopGamma_comp_apply_of_eq B S hS F (pr₂ i j).left (g j).left (pr₁ i j ≫ g i).left
        (congrArg Over.Hom.left (hpb i j).w.symm) a
  let mP₃A : ∀ i j k, Module Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)
      (N.val.obj (op (Pb₃ i j k))) := fun i j k => Module.compHom _
    (algebraMap Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Pb₃ i j k).left), ⊤))
  let mP₃A' : ∀ i j k, Module Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Over.mk (𝟙 V) : Over V).left), ⊤)
      (N.val.obj (op (Pb₃ i j k))) := mP₃A
  let mP₃D : ∀ i j k, Module Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Pb j k).left), ⊤)
      (N.val.obj (op (Pb₃ i j k))) := fun i j k => Module.compHom _
    (algebraMap Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Pb j k).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Pb₃ i j k).left), ⊤))
  have twP₃DD₃ : ∀ i j k, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Pb j k).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Pb₃ i j k).left), ⊤)
      (N.val.obj (op (Pb₃ i j k))) := fun _ _ _ =>
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twP₃AD : ∀ i j k, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Pb j k).left), ⊤)
      (N.val.obj (op (Pb₃ i j k))) := fun i j k =>
    isScalarTower_compHom_of_algebraMap_comp fun a =>
      appTopGamma_comp_apply_of_eq B S hS F (t₂₃ i j k).left (pr₁ j k ≫ g j).left
        (q i j k ≫ g i).left (congrArg Over.Hom.left (hpb₃ i j k).w.symm) a
  -- the rings of the overlaps as tensor products
  have hψex : ∀ i j, ∃ ψ : Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤)
        ⊗[Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V), ⊤)]
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Y j).left), ⊤) ≃+*
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Pb i j).left), ⊤),
      (∀ b : Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤),
        ψ (b ⊗ₜ[Γ((BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS F).obj V), ⊤)]
            (1 : Γ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS F).obj (Y j).left), ⊤))) =
          ((BigFppfOver.toScheme B S hS).map
            ((SmallEtale.toOver B S hS F).map (pr₁ i j).left)).appTop.hom b) ∧
        ∀ c : Γ((BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS F).obj (Y j).left), ⊤),
          ψ ((1 : Γ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤))
            ⊗ₜ[Γ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS F).obj V), ⊤)] c) =
            algebraMap Γ((BigFppfOver.toScheme B S hS).obj
                ((SmallEtale.toOver B S hS F).obj (Y j).left), ⊤)
              Γ((BigFppfOver.toScheme B S hS).obj
                ((SmallEtale.toOver B S hS F).obj (Pb i j).left), ⊤) c := fun i j =>
    exists_ringEquivTensorGamma_of_isPullback B S hS F (hpb i j) hV (hYaff i) (hYaff j)
      rfl rfl rfl rfl
  choose ψ hψv hψw using hψex
  have hψ₃ex : ∀ i j k, ∃ ψ : Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤)
        ⊗[Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V), ⊤)]
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Pb j k).left), ⊤) ≃+*
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Pb₃ i j k).left), ⊤),
      (∀ b : Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤),
        ψ (b ⊗ₜ[Γ((BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS F).obj V), ⊤)]
            (1 : Γ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS F).obj (Pb j k).left), ⊤))) =
          ((BigFppfOver.toScheme B S hS).map
            ((SmallEtale.toOver B S hS F).map (q i j k).left)).appTop.hom b) ∧
        ∀ c : Γ((BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS F).obj (Pb j k).left), ⊤),
          ψ ((1 : Γ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤))
            ⊗ₜ[Γ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS F).obj V), ⊤)] c) =
            algebraMap Γ((BigFppfOver.toScheme B S hS).obj
                ((SmallEtale.toOver B S hS F).obj (Pb j k).left), ⊤)
              Γ((BigFppfOver.toScheme B S hS).obj
                ((SmallEtale.toOver B S hS F).obj (Pb₃ i j k).left), ⊤) c :=
    fun i j k => exists_ringEquivTensorGamma_of_isPullback B S hS F (hpb₃ i j k) hV
      (hYaff i) (hPbaff j k) rfl rfl rfl rfl
  choose ψ₃ hψ₃u hψ₃w using hψ₃ex
  -- faithful flatness of the product of the rings of the members
  have hff : Module.FaithfullyFlat Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)
      (∀ i, Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤)) :=
    faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage B S hS F Y g hV hYaff hfppf
      fun _ => rfl
  have hflat : Module.Flat Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)
      (∀ i, Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤)) := inferInstance
  -- the restrictions to the members, and the two comparisons over the overlaps
  let ρ : N.val.obj (op (Over.mk (𝟙 V))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)] ∀ i, N.val.obj (op (Y i)) :=
    { toFun := fun n i => N.val.map (g i).op n
      map_add' := fun n n' => funext fun i => map_add (N.val.map (g i).op).hom n n'
      map_smul' := fun c n => funext fun i => N.val.map_smul (g i).op c n }
  let ρmem : ∀ i, N.val.obj (op (Over.mk (𝟙 V))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)] N.val.obj (op (Y i)) := fun i =>
    { toFun := fun n => N.val.map (g i).op n
      map_add' := map_add (N.val.map (g i).op).hom
      map_smul' := fun c n => N.val.map_smul (g i).op c n }
  let ρ₂ : ∀ i j, N.val.obj (op (Y j)) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Y j).left), ⊤)]
      N.val.obj (op (Pb i j)) := fun i j =>
    { toFun := fun n => N.val.map (pr₂ i j).op n
      map_add' := map_add (N.val.map (pr₂ i j).op).hom
      map_smul' := fun c n => N.val.map_smul (pr₂ i j).op c n }
  let ρ₃ : ∀ i j k, N.val.obj (op (Pb j k)) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Pb j k).left), ⊤)]
      N.val.obj (op (Pb₃ i j k)) := fun i j k =>
    { toFun := fun ww => N.val.map (t₂₃ i j k).op ww
      map_add' := map_add (N.val.map (t₂₃ i j k).op).hom
      map_smul' := fun c ww => N.val.map_smul (t₂₃ i j k).op c ww }
  have hbij₂ : ∀ i j, Function.Bijective ((ρ₂ i j).liftBaseChange
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Pb i j).left), ⊤)) := fun i j =>
    bijective_liftBaseChange_gamma_of_hasGlobalPresentation_overChart B S hS F hF M
      (hpres j) N hN (c j) ((pr₂ i j).left ≫ c j) (pr₂ i j) rfl
      (hYaff j) (hPbaff i j) (ρ₂ i j) fun _ => rfl
  have hbij₃ : ∀ i j k, Function.Bijective ((ρ₃ i j k).liftBaseChange
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Pb₃ i j k).left), ⊤)) := fun i j k =>
    bijective_liftBaseChange_gamma_of_hasGlobalPresentation_overChart B S hS F hF M
      (hpres k) N hN ((pr₂ j k).left ≫ c k)
      ((t₂₃ i j k).left ≫ (pr₂ j k).left ≫ c k) (t₂₃ i j k) rfl
      (hPbaff j k) (hPb₃aff i j k) (ρ₃ i j k) fun _ => rfl
  -- the descent along the extracted family
  have hmemY : ∀ i, Function.Bijective ((ρmem i).liftBaseChange
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤)) := fun i =>
    SheafOfModules.bijective_liftBaseChange_of_family_cancelBaseChange N g
      pr₁ pr₂ δ t₁₂ t₁₃ t₂₃ hδ₁ hδ₂
      (fun a b c => (hq₁₂ a b c).trans (hq₁₃ a b c).symm) hov₂ hov₃ hpb hcov
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V), ⊤)
      (fun a => Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y a).left), ⊤))
      (fun a b => Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Pb a b).left), ⊤))
      (fun a b c => Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Pb₃ a b c).left), ⊤))
      (fun a b => ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map (pr₁ a b).left)).appTop.hom)
      ψ hψv hψw
      (fun a b c => ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map (q a b c).left)).appTop.hom)
      ψ₃ hψ₃u hψ₃w
      (fun a b c => ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map (t₁₂ a b c).left)).appTop.hom)
      (fun a b c => ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map (t₁₃ a b c).left)).appTop.hom)
      (fun a => ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map (δ a).left)).appTop.hom)
      (fun a b => (appTopGamma_comp_apply_of_eq B S hS F (δ a).left (pr₁ a a).left
        (𝟙 (Y a).left) (congrArg (fun mo : Y a ⟶ Y a => mo.left) (hδ₁ a)) b).trans
          (appTopGamma_id_apply B S hS F b))
      (fun a b c => appTopGamma_comp_apply_of_eq B S hS F (t₁₂ a b c).left (pr₁ a b).left
        (q a b c).left (congrArg (fun mo : Pb₃ a b c ⟶ Y a => mo.left) (hq₁₂ a b c)))
      (fun a b c => appTopGamma_comp_apply_of_eq B S hS F (t₁₃ a b c).left (pr₁ a c).left
        (q a b c).left (congrArg (fun mo : Pb₃ a b c ⟶ Y a => mo.left) (hq₁₃ a b c)))
      (fun a b bb nn => N.val.map_smul (pr₁ a b).op bb nn)
      (fun a d ww => N.val.map_smul (δ a).op d ww)
      (fun a b c d ww => N.val.map_smul (t₁₂ a b c).op d ww)
      (fun a b c d ww => N.val.map_smul (t₁₃ a b c).op d ww)
      ρ₂ (fun _ _ _ => rfl) hbij₂ ρ₃ (fun _ _ _ _ => rfl) hbij₃ ρ (fun _ _ => rfl)
      ρmem (fun _ _ => rfl) i
  exact hmemY

/-- **A quasi-coherent `𝒪_F`-module has a covering family of a chart with affine underlying scheme
over whose objects with affine underlying scheme its sections are the base change of its sections
over the chart.**  This is the hypothesis `hM` of
`AlgebraicGeometry.Space.SmallEtale.hasGlobalPresentation_of_hasSectionBaseChangeOn`.

The family is the finite affine flat refinement of the family quasi-coherence provides, and the
comparison is obtained in two steps: from the chart to a member it is flat descent along that
refinement, `SheafOfModules.bijective_liftBaseChange_of_family_cancelBaseChange`, whose two inputs
over the overlaps are
`AlgebraicGeometry.Space.SmallEtale`'s
`bijective_liftBaseChange_of_hasGlobalPresentation_overChart`; from a member to an object with
affine underlying scheme over it, it is that same statement once more.  The two compose by
`Module.BaseChange.bijective_liftBaseChange_trans`.

The conclusion is asked of the universe lift of the restricted module, because
`SheafOfModules.HasSpannedRelationsOn` quantifies over the coverings of that lift; the sections of
the lift are the sections of the module lifted, so the comparison for the lift is the comparison
for the module transported along `ULift.up` by
`Module.BaseChange.bijective_liftBaseChange_of_comm`. -/
theorem exists_hasSectionBaseChangeOn_of_isQuasicoherentOnSite
    (hF : IsAlgebraicSpace B S hS F)
    (M : SheafOfModules.{m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
    (hM : M.IsQuasicoherentOnSite)
    (V : (smallEtaleRingedSite B S hS F hF).C)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V))) :
    ∃ (k : ℕ) (Y : Fin k → Over V) (g : ∀ j, Y j ⟶ Over.mk (𝟙 V)),
      Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) (Over.mk (𝟙 V)) ∧
        HasSectionBaseChangeOn B S hS F hF
          (SheafOfModules.uliftForPresentation.{u + 1, u, u, m, u + 1} (M.over V))
          fun W => IsAffine ((BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS F).obj W.left)) ∧ ∃ j, Nonempty (W ⟶ Y j) := by
  classical
  obtain ⟨N, hNeq⟩ : ∃ N : SheafOfModules.{m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V),
        M.over V = N :=
    ⟨_, rfl⟩
  rw [hNeq]
  obtain ⟨I₀, V₀, f₀, hcov₀, hpres⟩ := hM.locally_hasGlobalPresentation V
  obtain ⟨mm, Y, g, hYaff, hle, hcov, hfppf⟩ :=
    exists_finite_affine_ofArrows_le_over B S hS F hF (Over.mk (𝟙 V)) hV
      ((Sieve.overEquiv (Over.mk (𝟙 V) : Over V)).symm (Sieve.ofArrows V₀ f₀))
      (((smallEtaleRingedSite B S hS F hF).J).overEquiv_symm_mem_over
        (Over.mk (𝟙 V)) (Sieve.ofArrows V₀ f₀) hcov₀)
  choose kk cc hcc using fun i =>
    (Sieve.mem_ofArrows_iff V₀ f₀ (g i).left).1
      ((Sieve.overEquiv_symm_iff (Y := (Over.mk (𝟙 V) : Over V)) _ (g i)).1 (hle i))
  have hmemY :=
    bijective_liftBaseChange_mem_of_hasGlobalPresentation_family B S hS F hF M N hNeq.symm hV
      Y g hYaff hcov hfppf (fun i => V₀ (kk i)) cc fun i => hpres (kk i)
  refine ⟨mm, Y, g, hcov, fun W hQW => ?_⟩
  obtain ⟨hWaff, jj, ⟨bb⟩⟩ := hQW
  intro mNUT mNUW algW mNUW' twNU
  have hfacW : bb ≫ g jj = Over.mkIdTerminal.from W :=
    (Over.mkIdTerminal (X := V)).hom_ext _ _
  let mSheaf : ∀ Z : Over V, Module Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Z.left), ⊤) (N.val.obj (op Z)) := fun Z =>
    inferInstanceAs (Module
      ((((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj (op Z))
      (N.val.obj (op Z)))
  let mT : Module Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)
      (N.val.obj (op (Over.mk (𝟙 V)))) := inferInstanceAs (Module
    ((((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj
      (op (Over.mk (𝟙 V)))) (N.val.obj (op (Over.mk (𝟙 V)))))
  let algY : Algebra Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y jj).left), ⊤) :=
    RingHom.toAlgebra ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS F).map (g jj).left)).appTop.hom
  let mYA : Module Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤) (N.val.obj (op (Y jj))) :=
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y jj).left), ⊤))
  have twY : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y jj).left), ⊤)
      (N.val.obj (op (Y jj))) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let ρmem : N.val.obj (op (Over.mk (𝟙 V))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)] N.val.obj (op (Y jj)) :=
    { toFun := fun n => N.val.map (g jj).op n
      map_add' := map_add (N.val.map (g jj).op).hom
      map_smul' := fun cc nn => N.val.map_smul (g jj).op cc nn }
  let algBW : Algebra Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Y jj).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤) :=
    RingHom.toAlgebra ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS F).map bb.left)).appTop.hom
  have hABW : ∀ c, ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS F).map bb.left)).appTop.hom
      (((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map (g jj).left)).appTop.hom
        c) = ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS F).map (Over.mkIdTerminal.from W).left)).appTop.hom c :=
    appTopGamma_comp_apply_of_eq B S hS F bb.left (g jj).left
      (Over.mkIdTerminal.from W : W ⟶ Over.mk (𝟙 V)).left (congrArg Over.Hom.left hfacW)
  have twABW : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y jj).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤) :=
    IsScalarTower.of_algebraMap_eq fun c => (hABW c).symm
  let mWB : Module Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Y jj).left), ⊤)
      (N.val.obj (op W)) := Module.compHom _
    (algebraMap Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y jj).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤))
  let mWA : Module Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤) (N.val.obj (op W)) :=
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤))
  have twWBC : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Y jj).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
      (N.val.obj (op W)) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twWAC : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
      (N.val.obj (op W)) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twWAB : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y jj).left), ⊤)
      (N.val.obj (op W)) := isScalarTower_compHom_of_algebraMap_comp hABW
  let ρ₂W : N.val.obj (op (Y jj)) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Y jj).left), ⊤)] N.val.obj (op W) :=
    { toFun := fun n => N.val.map bb.op n
      map_add' := map_add (N.val.map bb.op).hom
      map_smul' := fun c n => N.val.map_smul bb.op c n }
  have hbijW : Function.Bijective (ρ₂W.liftBaseChange
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤)) :=
    bijective_liftBaseChange_gamma_of_hasGlobalPresentation_overChart B S hS F hF M
      (hpres (kk jj)) N hNeq.symm (cc jj) (bb.left ≫ cc jj) bb rfl (hYaff jj) hWaff
      ρ₂W fun _ => rfl
  let ρW : N.val.obj (op (Over.mk (𝟙 V))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)] N.val.obj (op W) :=
    { toFun := fun n => N.val.map (Over.mkIdTerminal.from W).op n
      map_add' := map_add (N.val.map (Over.mkIdTerminal.from W).op).hom
      map_smul' := fun c n => N.val.map_smul (Over.mkIdTerminal.from W).op c n }
  have hcomp : ∀ n, ρW n = ρ₂W (ρmem n) := fun n =>
    show N.val.restrictₛₗ (Over.mkIdTerminal.from W).op n =
        N.val.restrictₛₗ bb.op (N.val.restrictₛₗ (g jj).op n) by
      rw [N.val.restrictₛₗ_restrictₛₗ_op, hfacW]
  have htrans : Function.Bijective (ρW.liftBaseChange
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤)) :=
    Module.BaseChange.bijective_liftBaseChange_trans
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y jj).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
      ρmem ρ₂W ρW hcomp (hmemY jj) hbijW
  exact Module.BaseChange.bijective_liftBaseChange_of_comm _ ρW
    { toFun := ULift.down
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := ULift.up
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    { toFun := ULift.down
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := ULift.up
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    (fun _ => rfl) htrans

end SmallEtale

/-! ### Global presentations on the affine charts, with no hypothesis -/

variable (hF : IsAlgebraicSpace B S hS F)

/-- **A quasi-coherent `𝒪_F`-module has a global presentation after restriction to a chart whose
underlying scheme is affine**, with no hypothesis: this is
`AlgebraicGeometry.Space.HasAffineChartPresentations` discharged.

The two span conditions at the chart come from
`AlgebraicGeometry.Space.SmallEtale.hasGlobalPresentation_of_hasSectionBaseChangeOn`, whose
hypothesis is discharged by
`AlgebraicGeometry.Space.SmallEtale`'s
`exists_hasSectionBaseChangeOn_of_isQuasicoherentOnSite`. -/
theorem hasAffineChartPresentations : HasAffineChartPresentations.{u, m} B S hS F hF :=
  fun M hM V hV => by
  obtain ⟨k, Y, g, hcov, hbc⟩ :=
    SmallEtale.exists_hasSectionBaseChangeOn_of_isQuasicoherentOnSite B S hS F hF M hM V hV
  exact SmallEtale.hasGlobalPresentation_of_hasSectionBaseChangeOn B S hS F hF
    (M.over V) hV g hcov hbc

/-- **On the slice of the small étale site at a chart whose underlying scheme is affine the
presenting morphism of a global presentation is surjective on the sections over the chart**, with
no hypothesis: this is
`AlgebraicGeometry.Space.HasAffineChartSurjectivePresentations` discharged.

This is
`AlgebraicGeometry.Space.SmallEtale.surjective_val_app_of_isColimit_of_isAffineOver` at the
terminal object of the slice, whose underlying chart is the chart itself.  The epimorphism it asks
for is the presenting morphism, which is an epimorphism because it is a cokernel
(`CategoryTheory.Limits.Cofork.IsColimit.epi`), and the two sheafification conditions on the slice
hold in the universe of the presentation by
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and
`CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat`. -/
theorem hasAffineChartSurjectivePresentations :
    HasAffineChartSurjectivePresentations.{u, m} B S hS F hF := by
  intro V hV N I K P Q ι κ hP hQ a b hab hb
  have _ : HasSheafify ((smallEtaleRingedSite B S hS F hF).J.over V)
      AddCommGrpCat.{max (u + 1) m} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat ((smallEtaleRingedSite B S hS F hF).J.over V)
  have _ : ((smallEtaleRingedSite B S hS F hF).J.over V).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) m} :=
    GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat
      ((smallEtaleRingedSite B S hS F hF).J.over V)
  have _ : Epi b := Cofork.IsColimit.epi hb
  exact SmallEtale.surjective_val_app_of_isColimit_of_isAffineOver B S hS F hF κ ι hQ hP a b
    (by rw [← SheafOfModules.comp_val, hab]; rfl) hab hb (Over.mk (𝟙 V)) hV

/-! ### The closure clauses of Stacks 03M1 reached by the affine inputs -/

/-- **The direct-sum clause of Stacks 03M1 for the small étale ringed site of an algebraic
space**, with no hypothesis: a direct sum of quasi-coherent `𝒪_F`-modules is quasi-coherent.

This is `AlgebraicGeometry.Space`'s
`isClosedUnderDirectSumsQuasicoherent_of_hasAffineChartPresentations` with its affine input
discharged by `AlgebraicGeometry.Space.hasAffineChartPresentations`.  It is
the hypothesis `hsum` of
`AlgebraicGeometry.Space.existsUnique_quasicoherentSubobject_of_closure`. -/
theorem isClosedUnderDirectSumsQuasicoherent :
    IsClosedUnderDirectSumsQuasicoherent.{u, m} B S hS F hF :=
  isClosedUnderDirectSumsQuasicoherent_of_hasAffineChartPresentations B S hS F hF
    (hasAffineChartPresentations B S hS F hF)

/-- **The cokernel clause of Stacks 03M1 for the small étale ringed site of an algebraic space**,
with no hypothesis: a cokernel of a morphism of quasi-coherent `𝒪_F`-modules is quasi-coherent.

This is `AlgebraicGeometry.Space.isClosedUnderCokernels_of_hasAffineChartPresentations` with both
of its affine inputs discharged, by
`AlgebraicGeometry.Space.hasAffineChartPresentations` and
`AlgebraicGeometry.Space.hasAffineChartSurjectivePresentations`.  It is the instance hypothesis
`CategoryTheory.ObjectProperty.IsClosedUnderCokernels` of
`AlgebraicGeometry.Space.existsUnique_quasicoherentSubobject_of_closure`. -/
theorem isClosedUnderCokernels :
    ObjectProperty.IsClosedUnderCokernels
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) :=
  isClosedUnderCokernels_of_hasAffineChartPresentations B S hS F hF
    (hasAffineChartPresentations B S hS F hF)
    (hasAffineChartSurjectivePresentations B S hS F hF)

/-- **The colimit clause of Stacks 03M1 for the small étale ringed site of an algebraic space**,
with no hypothesis: a colimit of quasi-coherent `𝒪_F`-modules over any shape inside the module
universe is quasi-coherent.

This is `AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_of_hasAffineChartPresentations` with
both of its affine inputs discharged.  It subsumes the cokernel clause; the direct-sum clause is
stated separately because it needs only the first input. -/
theorem isClosedUnderColimitsOfShape (K : Type (max (u + 1) m))
    [Category.{max (u + 1) m} K] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) K :=
  isClosedUnderColimitsOfShape_of_hasAffineChartPresentations B S hS F hF
    (hasAffineChartPresentations B S hS F hF)
    (hasAffineChartSurjectivePresentations B S hS F hF) K

/-! ### The construction of Stacks 04CK, reduced to the kernel clause -/

/-- **Stacks 04CK with two of the three closure clauses of Stacks 03M1 discharged.**  Let `M` be a
quasi-coherent `𝒪_F`-module on an algebraic space `F` and let `G ⊆ M` be an `𝒪_F`-submodule.
There is a unique quasi-coherent submodule `G' ⊆ G` for which composition with the inclusion
`G' ⊆ G` is a bijection `Hom(H, G') ⟶ Hom(H, G)` for every quasi-coherent `𝒪_F`-module `H`.

This is `AlgebraicGeometry.Space.existsUnique_quasicoherentSubobject_of_closure` with its
direct-sum hypothesis discharged by
`AlgebraicGeometry.Space.isClosedUnderDirectSumsQuasicoherent` and its cokernel hypothesis by
`AlgebraicGeometry.Space.isClosedUnderCokernels`.  The kernel clause of Stacks 03M1 is the one
hypothesis left, and it is not a consequence of global presentations on the affine charts: it
needs flat base change of a kernel along an étale morphism of affine charts.  No
`@[stacks 04CK]` tag is carried while it is assumed, since the source assumes nothing. -/
theorem existsUnique_quasicoherentSubobject_of_isClosedUnderKernels
    [ObjectProperty.IsClosedUnderKernels
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))]
    (M : Modules.{u, m} B S hS F hF) [M.IsQuasicoherentOnSite] (G : Subobject M) :
    ∃! G' : { G' : Subobject (G : Modules.{u, m} B S hS F hF) //
        (G' : Modules.{u, m} B S hS F hF).IsQuasicoherentOnSite },
      ∀ (H : Modules.{u, m} B S hS F hF) [H.IsQuasicoherentOnSite],
        Function.Bijective
          (fun f : H ⟶ (G'.1 : Modules.{u, m} B S hS F hF) ↦ f ≫ G'.1.arrow) :=
  have _ := isClosedUnderCokernels B S hS F hF
  existsUnique_quasicoherentSubobject_of_closure B S hS F hF
    (isClosedUnderDirectSumsQuasicoherent B S hS F hF) M G

/-- **The maximality clause of Stacks 04CK with two of the three closure clauses of Stacks 03M1
discharged.**  The quasi-coherent submodule of
`AlgebraicGeometry.Space.existsUnique_quasicoherentSubobject_of_isClosedUnderKernels` is the
largest quasi-coherent submodule contained in `G`.

As there, the kernel clause of Stacks 03M1 is the one hypothesis left. -/
theorem exists_greatest_quasicoherentSubobject_of_isClosedUnderKernels
    [ObjectProperty.IsClosedUnderKernels
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))]
    (M : Modules.{u, m} B S hS F hF) [M.IsQuasicoherentOnSite] (G : Subobject M) :
    ∃ G' : Subobject (G : Modules.{u, m} B S hS F hF),
      (G' : Modules.{u, m} B S hS F hF).IsQuasicoherentOnSite ∧
        ∀ K : Subobject (G : Modules.{u, m} B S hS F hF),
          (K : Modules.{u, m} B S hS F hF).IsQuasicoherentOnSite → K ≤ G' :=
  have _ := isClosedUnderCokernels B S hS F hF
  exists_greatest_quasicoherentSubobject_of_closure B S hS F hF
    (isClosedUnderDirectSumsQuasicoherent B S hS F hF) M G

end AlgebraicGeometry.Space

end
