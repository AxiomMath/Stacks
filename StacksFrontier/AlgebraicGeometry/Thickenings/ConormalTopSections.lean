module

public import StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorization
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineIdentification
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobal
public import StacksFrontier.AlgebraicGeometry.Smooth.ThickeningRestriction
public import StacksFrontier.AlgebraicGeometry.Thickenings.FirstOrderConormalInclusion

/-!
# The global sections of the conormal sheaf of a first-order thickening of an affine scheme

Let `i : X ⟶ X'` be a first-order thickening of schemes, [Stacks Project, Tag 04EX] (2), with
`X'` affine.  Its conormal sheaf has a Zariski description and an algebraic one, and the
deformation-theoretic development uses both:

* `Stacks.Conormal.conormalSheaf i = i^*ℐ` is the sheaf of modules, which is what
  [Stacks Project, Tag 01R2] attaches to the thickening and what the comparison of
  [Stacks Project, Tag 04G2] (1) identifies with the conormal module of a closed subspace of an
  algebraic space;
* `RingHom.ker i^♯`, the kernel of the surjection `Γ(X', ⊤) ⟶ Γ(X, ⊤)`, with the
  `Γ(X, ⊤)`-module structure of `Stacks.Smooth.thickeningKerModule`, which is what the lifting
  and derivation calculus of `StacksFrontier.AlgebraicGeometry.Smooth.LiftTorsor` is written in.

This file identifies them, as a `Γ(X, ⊤)`-linear equivalence.

## Main definitions

* `Stacks.Thickenings.conormalTopSectionsEquivKer`: the underlying bijection — the global
  sections of the conormal sheaf are the kernel ideal.
* `Stacks.Thickenings.conormalTopSectionsLinearEquivKer`: **the same as a `Γ(X, ⊤)`-linear
  equivalence**, which is what identifies a module of linear maps out of a Zariski sheaf's global
  sections with one landing in `RingHom.ker i^♯`.

## Main results

* `Stacks.Thickenings.conormalModules_eq`: the conormal sheaf typed as an
  `AlgebraicGeometry.Scheme.Modules` is `Stacks.Conormal.conormalSheaf`.
* `Stacks.Thickenings.conormalTopSectionsEquivKer_smul`: the bijection is `Γ(X, ⊤)`-linear.
* `Stacks.Thickenings.coe_conormalTopSectionsLinearEquivKer`: **the identification is the
  inclusion `𝒞_{X/X'} ⊆ 𝒪_{X'}` on global sections** — the regular function underlying the kernel
  element attached to a conormal section is that section's image under
  `Stacks.Thickenings.firstOrderImmersionConormalSheafι`.  This is what reduces a statement about
  the identification to one about the inclusion, which, unlike the identification, is pinned and
  is a monomorphism.

## Implementation notes

**Why a separate name for the sheaf.** `Stacks.Conormal.conormalSheaf` is typed over
`Stacks.Sheaves.RingedSpaceModules.structureSheafRing` of the underlying ringed space, whereas the
`Γ(M, U)` notation and the instance `Module Γ(X, U) Γ(M, U)` are stated for
`AlgebraicGeometry.Scheme.Modules`, that is over `AlgebraicGeometry.Scheme.ringCatSheaf`.  The two
sheaves of rings are definitionally equal but not syntactically, so instance resolution — which is
syntactic — does not find the module structure on the sections of the conormal sheaf as it is
typed.  `Stacks.Thickenings.conormalModules` of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/MapDerivationActionGlobal.lean` is the same sheaf
declared at the type the instance is stated for, and
`Stacks.Thickenings.conormalModules_eq` below records that the two agree; this is the same
obstruction that
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalChartSections` records when it declines
to state its identifications as linear equivalences.

**The two steps, and why the second needs a descent.** Over the *ambient* scheme the computation
is two isomorphisms of the library: `Stacks.Thickenings.firstOrderConormalIso` says `ℐ ≅ i_*𝒞_{X/X'}` —
the unit of `i^* ⊣ i_*` at the defining ideal sheaf, invertible because `ℐ² = 0` — and
`Stacks.Conormal.idealSheafSectionsIso` says the sections of `ℐ` over any open are the kernel of
the map on functions there.  Between them sits
`Stacks.Immersion.conormalSheafSelfIso`, which reconciles the two constructions of the conormal
sheaf of a closed immersion — as `i^*ℐ_i` and, for the immersion of
[Stacks Project, Tag 01R2], as the pullback of the ideal sheaf of the closed immersion into the
coborder neighbourhood.  All three are isomorphisms of `Γ(X', ⊤)`-modules, and the sections of
`i_*𝒞_{X/X'}` over `⊤` *are* the sections of `𝒞_{X/X'}` over `⊤`, because `i ⁻¹ᵁ ⊤ = ⊤` holds by
`Eq.refl`.

What is wanted, however, is `Γ(X, ⊤)`-linearity, and that is a descent along the surjection
`i^♯ : Γ(X', ⊤) ⟶ Γ(X, ⊤)`: on the sections of the direct image the `Γ(X', ⊤)`-action *is* the
`Γ(X, ⊤)`-action read through `i^♯` (restriction of scalars, by `Eq.refl`), and on
`RingHom.ker i^♯` the same holds by `Stacks.Smooth.thickeningKerModule_smul`.  So a scalar is
lifted along `Stacks.Smooth.surjective_appTop_of_isFirstOrderThickening` — which is where `X'`
affine is used, and the only place — and the ambient linearity applies verbatim.

No `@[stacks]` attribute is claimed: Tag 01R2's construction and Tag 01R3's quotient map are
registered where they are built, and nothing here asserts a clause of either.

## References

* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Thickenings

variable {X X' : Scheme.{u}} (i : X ⟶ X')

/-- `Stacks.Thickenings.conormalModules` is `Stacks.Conormal.conormalSheaf`: the two differ only
in which of the two definitionally equal spellings of the structure sheaf of rings their type
names. -/
theorem conormalModules_eq [AlgebraicGeometry.IsClosedImmersion i] :
    conormalModules i = Stacks.Conormal.conormalSheaf i :=
  rfl

/-- The identification of the global sections of the conormal sheaf with the kernel ideal, as an
isomorphism of `Γ(X', ⊤)`-modules read over the *ambient* scheme.

It is `Stacks.Thickenings.firstOrderConormalIso` inverted — the sections of `i_*𝒞_{X/X'}` over
`⊤` being the sections of `𝒞_{X/X'}` over `⊤` by `Eq.refl` — followed by
`Stacks.Conormal.idealSheafSectionsIso`. -/
def conormalTopSectionsAmbientLinearEquiv [AlgebraicGeometry.IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) :=
  ((SheafOfModules.evaluation _ (op (⊤ : X'.Opens))).mapIso
        (firstOrderConormalIso i hsq ≪≫
          (RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom).mapIso
            (Stacks.Immersion.conormalSheafSelfIso i)).symm ≪≫
    Stacks.Conormal.idealSheafSectionsIso i (⊤ : X'.Opens)).toLinearEquiv

/-- **The global sections of the conormal sheaf of a first-order thickening are the kernel
ideal.**  For a closed immersion `i : X ⟶ X'` with square-zero kernel,

`Γ(𝒞_{X/X'}, ⊤) ≃ RingHom.ker i^♯`.

No affineness is needed for the bijection; it is needed only to make this `Γ(X, ⊤)`-linear, in
`Stacks.Thickenings.conormalTopSectionsLinearEquivKer`. -/
def conormalTopSectionsEquivKer [AlgebraicGeometry.IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥) :
    (Γ(conormalModules i, (⊤ : X.Opens)) : Type u) ≃ RingHom.ker i.appTop.hom :=
  (conormalTopSectionsAmbientLinearEquiv i hsq).toEquiv

/-- **The identification of the conormal sections with the kernel ideal is `Γ(X, ⊤)`-linear.**
The scalar is lifted along the surjection `i^♯ : Γ(X', ⊤) ⟶ Γ(X, ⊤)`, where both actions are the
`Γ(X, ⊤)`-actions read through `i^♯` — on the sections of the direct image by `Eq.refl` and on
the kernel ideal by `Stacks.Smooth.thickeningKerModule_smul` — so the ambient linearity applies
unchanged. -/
theorem conormalTopSectionsEquivKer_smul [IsAffine X']
    [AlgebraicGeometry.IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥)
    (c : Γ(X, (⊤ : X.Opens))) (m : Γ(conormalModules i, (⊤ : X.Opens))) :
    letI := Stacks.Smooth.thickeningKerModule (i := i) ⟨inferInstance, hsq⟩
    conormalTopSectionsEquivKer i hsq (c • m) = c • conormalTopSectionsEquivKer i hsq m := by
  let := Stacks.Smooth.thickeningKerModule (i := i) ⟨inferInstance, hsq⟩
  obtain ⟨x, hx⟩ := Stacks.Smooth.surjective_appTop_of_isFirstOrderThickening
    (i := i) ⟨inferInstance, hsq⟩ c
  subst hx
  exact ((conormalTopSectionsAmbientLinearEquiv i hsq).map_smul x m).trans
    (Stacks.Smooth.thickeningKerModule_smul (i := i) ⟨inferInstance, hsq⟩ x _).symm

/-- **The global sections of the conormal sheaf of a first-order thickening of an affine scheme
are the kernel ideal, `Γ(X, ⊤)`-linearly.**

`Γ(𝒞_{X/X'}, ⊤) ≃ₗ[Γ(X, ⊤)] RingHom.ker i^♯`,

the right-hand side carrying the module structure of `Stacks.Smooth.thickeningKerModule`.  This
is the identification which lets a module of `Γ(X, ⊤)`-linear maps into the global sections of the
Zariski conormal sheaf be read as a module of linear maps into the conormal data `RingHom.ker i^♯`
of the thickening. -/
def conormalTopSectionsLinearEquivKer [IsAffine X']
    [AlgebraicGeometry.IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥) :
    letI := Stacks.Smooth.thickeningKerModule (i := i) ⟨inferInstance, hsq⟩
    (Γ(conormalModules i, (⊤ : X.Opens)) : Type u) ≃ₗ[Γ(X, (⊤ : X.Opens))]
      RingHom.ker i.appTop.hom :=
  letI := Stacks.Smooth.thickeningKerModule (i := i) ⟨inferInstance, hsq⟩
  { toFun := conormalTopSectionsEquivKer i hsq
    map_add' := (conormalTopSectionsAmbientLinearEquiv i hsq).map_add
    map_smul' := conormalTopSectionsEquivKer_smul i hsq
    invFun := (conormalTopSectionsEquivKer i hsq).symm
    left_inv := (conormalTopSectionsEquivKer i hsq).left_inv
    right_inv := (conormalTopSectionsEquivKer i hsq).right_inv }

/-- **The identification of the conormal sections with the kernel ideal is the inclusion
`𝒞_{X/X'} ⊆ 𝒪_{X'}` read on global sections.**  The regular function on the ambient scheme
underlying the kernel element attached to a global section of the conormal sheaf is the image of
that section under `Stacks.Thickenings.firstOrderImmersionConormalSheafι`.

This says what the identification *is*, and it is how a statement about the identification is
reduced to one about the inclusion: `Stacks.Thickenings.firstOrderImmersionConormalSheafι` is a
monomorphism pinned by
`Stacks.Thickenings.canonicalConormalQuotientMap_comp_firstOrderImmersionConormalSheafι`, so it
is determined at the level of the defining ideal sheaf, whereas the identification is a composite
of three isomorphisms and a descent of scalars and is determined by nothing.  In particular the
naturality of `Stacks.Thickenings.conormalTopSectionsLinearEquivKer` in the thickening — which a
comparison of the conormal data of two chart thickenings needs — becomes a statement about the
inclusion alone.

Both sides are `Eq.refl`: the identification's two remaining factors are the evaluation at `⊤` of
the inverse of the composite of `Stacks.Thickenings.firstOrderConormalIso` with the direct image
of `Stacks.Immersion.conormalSheafSelfIso`, which is exactly what the inclusion is built from,
and `Stacks.Conormal.idealSheafSectionsIso` lands in the kernel by the inclusion of the defining
ideal sheaf, by `Stacks.Conormal.idealSheafSectionsIso_hom_coe`. -/
theorem coe_conormalTopSectionsLinearEquivKer [IsAffine X']
    [AlgebraicGeometry.IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥)
    (m : Γ(conormalModules i, (⊤ : X.Opens))) :
    letI := Stacks.Smooth.thickeningKerModule (i := i) ⟨inferInstance, hsq⟩
    ((conormalTopSectionsLinearEquivKer i hsq m : RingHom.ker i.appTop.hom) :
        Γ(X', (⊤ : X'.Opens))) =
      (firstOrderImmersionConormalSheafι i hsq).val.app (op (⊤ : X'.Opens)) m :=
  rfl

end Stacks.Thickenings

end
