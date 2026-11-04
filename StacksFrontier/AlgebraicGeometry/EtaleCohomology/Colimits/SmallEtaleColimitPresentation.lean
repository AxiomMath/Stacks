module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition

/-!
# The presentation predicate of Stacks 09YQ, instantiated

[Stacks, Tag 09YQ] (Étale Cohomology, Lemma 59.51.3) is a statement about a system `(F_i, φ_a)`
of abelian sheaves on the small étale sites of an inverse system of schemes `D : Iᵒᵖ ⥤ Scheme`
together with an abelian sheaf `𝒢` on the small étale site of the limit `X = c.pt` **presenting
`colim_i f_i^{-1}F_i`**, where `f_i : X ⟶ X_i` are the projections of the cone.

`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem` carries that presentation
hypothesis as a *parameter* `P`, because the diagram `i ↦ f_i^{-1}F_i` is not a functor on `I`
and so `CategoryTheory.Limits.IsColimit` is unavailable (see the implementation notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleCohomologyColimit.lean`).
This file supplies the parameter: it *defines* the presentation condition, in the universal
property form, in exactly the vocabulary `PresentedSystem` asks for — the inverse image
`Stacks.EtaleCohomology.etaleAbelianInverseImage` along
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.conePi` on Mathlib's small étale sites, at the
coefficients `AddCommGrpCat.{u + 1}`.

## Main definitions

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.coneInverseImageComp` — the comparison
  `f_j^{-1} ≅ f_{ji}^{-1} ⋙ f_i^{-1}` of inverse images along the factorisation
  `f_j = f_i ≫ f_{ji}` of a projection of the cone through a transition, with the projection
  carried as a *named* composite.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsCompatibleFamily` — a family of maps
  `τ_i : f_i^{-1}F_i ⟶ H` compatible with the transition maps of the system.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation` — **the presentation
  predicate**: the legs `ι_i` form a compatible family, and every compatible family factors
  uniquely through them. This is `𝒢 = colim_i f_i^{-1}F_i`, and it is the intended value of the
  parameter `P` of `PresentedSystem`.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation.desc` — the induced
  map out of `𝒢`.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation.isoOfPresentations` —
  the canonical isomorphism between two presentations of one and the same system.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.trivialSystem` and
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.trivialPresentedSystem` — the system whose
  sheaf at every level is zero, and the presented system it carries.

## Main results

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation.hom_ext` — a map out
  of `𝒢` is determined by its composites with the legs.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimitPresentation_trivialSystem` — the
  zero sheaf on the limit, with the zero legs, presents the colimit of the zero system. With
  `trivialPresentedSystem` this exhibits a concrete inhabitant of
  `PresentedSystem IsColimitPresentation`, so both that structure and
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.Devissage` are statable at a concrete
  system; in particular the predicate is not unsatisfiable, which an abstract `P` leaves open.

## Implementation notes

**Why the universal property and not `IsColimit`.** For `a : i ⟶ j` in `Iᵒᵖ` the cone gives
`f_i ≫ f_{ji} = f_j`, so `f_j^{-1}` and `f_i^{-1} ∘ f_{ji}^{-1}` are compared by
`coneInverseImageComp`, and the transition of the system gives `f_{ji}^{-1}F_j ⟶ F_i`; together
these produce the diagram map `f_j^{-1}F_j ⟶ f_i^{-1}F_i` whose compatibility `IsCompatibleFamily`
records. The assignment `i ↦ f_i^{-1}F_i` is *not* a functor on `I`: Tag 0EZL, and with it
`Stacks.EtaleCohomology.EtaleSheafSystem`, imposes only the cocycle condition and not the
identity law, so there is no `CategoryTheory.Limits.Cocone` and hence no
`CategoryTheory.Limits.IsColimit` to ask for. Nothing is weakened by the universal-property
form: the factorisation is required to be *through the given legs* and to be *unique*, which is
precisely what a colimit cocone asserts. This is the same device as
`Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation`, which states the
same condition for the other of the two inverse images this library carries (see below), and as
`Stacks.WeakSites.ColimitSiteCohomology.IsColimitPresentation`, which states it for a system of
abelian sheaves on an abstract inverse system of sites.

**Named composites.** `coneInverseImageComp` is
`Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso'` at the factorisation
`f_j = f_i ≫ f_{ji}`, with `f_j` as the *name* of the composite rather than `f_i ≫ f_{ji}`
written out. Without that the comparison would have to be transported along `Cone.w` at every
use, and the transport would have to be reconciled with the ones the associativity pentagon
`etaleAbelianInverseImageCompIso'_assoc` already carries.

**`conePi`.** The projection is written `conePi c i` and never `c.π.app i`: the two are
definitionally equal, but the second has source `((Functor.const Iᵒᵖ).obj c.pt).obj i`, which
typeclass inference does not unfold, so the `HasSheafify` instance for the small étale site of
the limit is not found. This is the rule of the file this one extends.

**The other inverse image.** `etaleAbelianInverseImage` is the inverse image built as a left Kan
extension followed by sheafification, which is the one `Sheaf.H` and therefore `PresentedSystem`
are built from. `Stacks.EtaleCohomology.smallEtalePullbackAb` — equivalently
`Stacks.EtaleCohomology.systemPullback`, which `EtaleSheafSystem` carries its transitions along
— is the abstract left adjoint of the same direct image. The two are isomorphic but not equal,
and `Stacks.EtaleCohomology.systemTransitionMap` is what reads a transition of a system through
the comparison; the predicate here is stated entirely in the first vocabulary, so that it can be
used as the `P` of `PresentedSystem` with no transport in the statement.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology.SmallEtaleLimitCohomology

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  {c : Cone D}
  [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]

/-! ### The comparison of inverse images along a projection factored through a transition -/

omit [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}] in
/-- The projection of the cone at a level factors through any later level:
`f_i ≫ f_{ji} = f_j` for `a : i ⟶ j` in `Iᵒᵖ`, written with
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.conePi`. -/
theorem conePi_comp (c : Cone D) {i j : Iᵒᵖ} (a : i ⟶ j) :
    conePi c i ≫ D.map a = conePi c j :=
  c.w a

/-- **The comparison `f_j^{-1} ≅ f_{ji}^{-1} ⋙ f_i^{-1}`** of inverse images of abelian étale
sheaves along the factorisation `f_j = f_i ≫ f_{ji}` of a projection of the cone through a
transition of the index. It is
`Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso'` at that factorisation, with the
projection `f_j` carried as the *name* of the composite. -/
def coneInverseImageComp {i j : Iᵒᵖ} (a : i ⟶ j) :
    etaleAbelianInverseImage.{u, u + 1} (conePi c j) ≅
      etaleAbelianInverseImage.{u, u + 1} (D.map a) ⋙
        etaleAbelianInverseImage.{u, u + 1} (conePi c i) :=
  etaleAbelianInverseImageCompIso'.{u, u + 1} (conePi c i) (D.map a) (conePi c j)
    (conePi_comp c a).symm

/-! ### The presentation predicate -/

/-- **A family of maps out of the inverse images of a system, compatible with its transitions.**
For `a : i ⟶ j` in `Iᵒᵖ` the diagram map `f_j^{-1}F_j ⟶ f_i^{-1}F_i` is the comparison
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.coneInverseImageComp` followed by the inverse
image along `f_i` of the transition `Stacks.EtaleCohomology.systemTransitionMap`; a family `τ` is
compatible when it turns every such triangle into a commuting one.

This is the shape of both clauses of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation`: the legs of a
presentation are a compatible family, and a compatible family is what a presentation lets one
factor. -/
def IsCompatibleFamily (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (H : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
    (τ : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ H) :
    Prop :=
  ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
    (coneInverseImageComp a).hom.app (F.obj j) ≫
        (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (systemTransitionMap F a) ≫ τ i =
      τ j

/-- A compatible family stays compatible after composing with a map of the target sheaf. -/
theorem IsCompatibleFamily.comp {F : EtaleSheafSystem D AddCommGrpCat.{u + 1}}
    {H H' : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
    {τ : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ H}
    (hτ : IsCompatibleFamily F H τ) (χ : H ⟶ H') :
    IsCompatibleFamily F H' fun i => τ i ≫ χ := fun a => by
  simpa using congrArg (fun m => m ≫ χ) (hτ a)

/-- **The presentation predicate of [Stacks, Tag 09YQ]: `𝒢 = colim_i f_i^{-1}F_i`.** The legs
`ι_i : f_i^{-1}F_i ⟶ 𝒢` form a family compatible with the transitions of the system, and every
compatible family of maps to an abelian sheaf `H` on the small étale site of the limit factors
uniquely through them.

This is the intended value of the parameter `P` of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem`: it is stated in exactly the
vocabulary that structure asks for, so `PresentedSystem IsColimitPresentation` and the dévissage
datum over it are statements with no parameter left. See the module docstring on why the colimit
is expressed by its universal property rather than as a
`CategoryTheory.Limits.IsColimit`. -/
structure IsColimitPresentation (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢) :
    Prop where
  /-- The legs are compatible with the transition maps of the system. -/
  compatible : IsCompatibleFamily F 𝒢 ι
  /-- Every compatible family factors uniquely through the legs. -/
  existsUnique_desc : ∀ (H : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
      (τ : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ H),
      IsCompatibleFamily F H τ → ∃! χ : 𝒢 ⟶ H, ∀ i : Iᵒᵖ, ι i ≫ χ = τ i

namespace IsColimitPresentation

variable {F : EtaleSheafSystem D AddCommGrpCat.{u + 1}}
  {𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
  {ι : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢}

/-- **The map induced by a compatible family** on the sheaf presenting the colimit. -/
def desc (h : IsColimitPresentation F 𝒢 ι)
    {H : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
    {τ : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ H}
    (hτ : IsCompatibleFamily F H τ) : 𝒢 ⟶ H :=
  (h.existsUnique_desc H τ hτ).choose

/-- The induced map factors the family it was built from. -/
theorem desc_fac (h : IsColimitPresentation F 𝒢 ι)
    {H : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
    {τ : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ H}
    (hτ : IsCompatibleFamily F H τ) (i : Iᵒᵖ) : ι i ≫ h.desc hτ = τ i :=
  (h.existsUnique_desc H τ hτ).choose_spec.1 i

/-- **A map out of the presenting sheaf is determined by its composites with the legs.** -/
theorem hom_ext (h : IsColimitPresentation F 𝒢 ι)
    {H : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}} {χ₁ χ₂ : 𝒢 ⟶ H}
    (hχ : ∀ i : Iᵒᵖ, ι i ≫ χ₁ = ι i ≫ χ₂) : χ₁ = χ₂ :=
  (h.existsUnique_desc H (fun i => ι i ≫ χ₁)
      (IsCompatibleFamily.comp h.compatible χ₁)).unique (fun _ => rfl) fun i => (hχ i).symm

/-- **Two presentations of one system are canonically isomorphic**, by the maps each induces on
the other's legs. -/
def isoOfPresentations {𝒢' : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
    {ι' : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢'}
    (h : IsColimitPresentation F 𝒢 ι) (h' : IsColimitPresentation F 𝒢' ι') : 𝒢 ≅ 𝒢' where
  hom := h.desc h'.compatible
  inv := h'.desc h.compatible
  hom_inv_id := h.hom_ext fun i => by
    rw [← Category.assoc, h.desc_fac h'.compatible i, h'.desc_fac h.compatible i,
      Category.comp_id]
  inv_hom_id := h'.hom_ext fun i => by
    rw [← Category.assoc, h'.desc_fac h.compatible i, h.desc_fac h'.compatible i,
      Category.comp_id]

/-- The isomorphism of two presentations carries the legs of one to the legs of the other. -/
theorem isoOfPresentations_leg {𝒢' : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
    {ι' : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢'}
    (h : IsColimitPresentation F 𝒢 ι) (h' : IsColimitPresentation F 𝒢' ι') (i : Iᵒᵖ) :
    ι i ≫ (h.isoOfPresentations h').hom = ι' i :=
  h.desc_fac h'.compatible i

end IsColimitPresentation

/-! ### A concrete presented system -/

/-- **The zero system**: the system of abelian étale sheaves whose sheaf at every level is the
zero sheaf and whose transition maps are zero. The cocycle condition is automatic. -/
def trivialSystem (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}] :
    EtaleSheafSystem D AddCommGrpCat.{u + 1} where
  obj _ := 0
  map _ := 0
  map_comp _ _ := by simp

/-- The sheaf of the zero system at a level is the zero sheaf. -/
@[simp]
theorem trivialSystem_obj (i : Iᵒᵖ) : (trivialSystem D).obj i = 0 := rfl

/-- The inverse image of the zero sheaf is a zero object: the inverse image is additive. -/
theorem isZero_inverseImage_zero {X Y : Scheme.{u}} (f : Y ⟶ X)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}] :
    IsZero ((etaleAbelianInverseImage.{u, u + 1} f).obj 0) :=
  IsZero.of_iso (isZero_zero _) (Functor.mapZeroObject _)

/-- **The zero sheaf on the limit presents the colimit of the zero system.** Every map out of
the inverse image of a zero sheaf vanishes, so there is exactly one compatible family to any
target and exactly one map out of the zero sheaf factoring it. -/
theorem isColimitPresentation_trivialSystem (c : Cone D)
    [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}] :
    IsColimitPresentation (c := c) (trivialSystem D) 0 (fun _ => 0) where
  compatible := fun _ => by rw [comp_zero, comp_zero]
  existsUnique_desc H τ _ := by
    have hτ : ∀ i : Iᵒᵖ, τ i = 0 := fun i =>
      (isZero_inverseImage_zero (conePi c i)).eq_of_src _ _
    exact ⟨0, fun i => by rw [hτ i, zero_comp], fun y _ => (isZero_zero _).eq_of_src _ _⟩

variable [∀ i : Iᵒᵖ, HasExt.{u + 1} (Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})]

/-- **A concrete presented system.** The zero system, the zero sheaf on the limit and the zero
legs form a
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem` for the presentation predicate
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation`: the two cocone laws on
cohomology hold because the cohomology of a zero sheaf vanishes in every degree.

Its point is that it is concrete: `PresentedSystem IsColimitPresentation` is an inhabited type
with no parameter left, so `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.Devissage` is
statable at a concrete presented system, and
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_of_degreeZero_of_vanishing`
is a statement about a nonempty class of systems. -/
def trivialPresentedSystem (c : Cone D)
    [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})] :
    PresentedSystem (c := c) IsColimitPresentation where
  sys := trivialSystem D
  sheaf := 0
  ι _ := 0
  pres := isColimitPresentation_trivialSystem c
  transition_comp := by
    intro i _ _ _ _ p _
    have hs : Subsingleton (Sheaf.H.{u + 1, u + 1} ((trivialSystem D).obj i) p) := by
      rw [trivialSystem_obj]
      exact Sheaf.subsingleton_H_of_isZero
        (isZero_zero (Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1})) p
    exact hs.elim _ _
  leg_transition := by
    intro _ _ _ p _
    have hs : Subsingleton
        (Sheaf.H.{u + 1, u + 1} (0 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}) p) :=
      Sheaf.subsingleton_H_of_isZero
        (isZero_zero (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})) p
    exact hs.elim _ _

end Stacks.EtaleCohomology.SmallEtaleLimitCohomology

end
