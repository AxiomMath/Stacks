module

public import StacksFrontier.AlgebraicGeometry.Thickenings.Conormal
public import StacksFrontier.AlgebraicGeometry.Thickenings.FirstOrderConormalInclusion
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalTopSections
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalGenerators

/-!
# Naturality of the conormal-sections identification in the thickening

Let `i : X ⟶ X'` and `j : Y ⟶ Y'` be first-order thickenings of schemes with `X'` and `Y'`
affine, and let `(f, f')` be a morphism of thickenings from `i` to `j`, that is a commutative
square

```
X --f--> Y
|        |
i        j
v        v
X' -f'-> Y'
```

`Stacks.Thickenings.conormalTopSectionsLinearEquivKer` identifies the global sections of the
Zariski conormal sheaf of a first-order thickening with its kernel ideal. This file proves that
the identification is **natural in the thickening**: the square

```
Γ(𝒞_{Y/Y'}, ⊤) ---≃---> RingHom.ker j^♯
      |                       |
   𝒞-map                  conormalMap
      v                       v
Γ(𝒞_{X/X'}, ⊤) ---≃---> RingHom.ker i^♯
```

commutes, where the left vertical is the transpose along `f^* ⊣ f_*` of
`Stacks.Immersion.immersionConormalSheafMap` read on global sections and the right vertical is
`Stacks.Thickenings.conormalMap`, which is `f'^♯` restricted to the kernel ideals.

Both verticals already existed; what was missing is the commutativity, and it is the fifth
structural input to the naturality step of [Stacks Project, Tag 04AM], alongside the four
compatibilities of
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.IsActionSectionRestrictionNatural`.

## The reduction that makes this tractable

`Stacks.Thickenings.conormalTopSectionsLinearEquivKer` is a composite of three isomorphisms and
a descent of scalars, and nothing pins it. The route taken here is the one the module
documentation of `StacksFrontier/AlgebraicGeometry/Thickenings/ConormalTopSections.lean` predicts:
`Stacks.Thickenings.coe_conormalTopSectionsLinearEquivKer` says — by `rfl` — that the
identification **is** the inclusion `𝒞_{X/X'} ⊆ 𝒪_{X'}` on global sections, so the naturality
of the identification becomes the naturality of
`Stacks.Thickenings.firstOrderImmersionConormalSheafι` alone, and that inclusion is pinned:
its composite with the conormal quotient map is the inclusion of the defining ideal sheaf
(`Stacks.Thickenings.canonicalConormalQuotientMap_comp_firstOrderImmersionConormalSheafι`).

The reduction is real, and it is what the proof below does. The naturality of the inclusion is
proved at the level of **sheaves** in three rewrites, by cancelling the conormal quotient map —
which for a first-order thickening is an isomorphism,
`Stacks.Thickenings.isIso_canonicalConormalQuotientMap` of
`StacksFrontier/AlgebraicGeometry/Thickenings/FirstOrderConormalInclusion.lean` —
and then composing two identities:
`Stacks.Immersion.canonicalConormalQuotientMap_comp_pushforward_homEquiv` exchanges the quotient
maps with the conormal map of the square, and
`Stacks.ClosedImmersion.unit_comp_pushforward_idealSheafMap_comp_ι` says the ideal-sheaf map of
the square is the ambient structure-sheaf map. No affineness and no square-zero hypothesis on
the *other* thickening is needed for that step; see the hypothesis discussion below.

## Main results

* `Stacks.Thickenings.firstOrderImmersionConormalSheafι_natural`: **naturality of the inclusion
  `𝒞_{X/X'} ⊆ 𝒪_{X'}` in the thickening**, at the level of sheaves on the ambient scheme.
* `Stacks.Thickenings.firstOrderImmersionConormalSheafι_natural_val_app_top`: the same on global
  sections, with the comparison of the two pushforward composites discharged.
* `Stacks.Thickenings.coe_conormalTopSectionsLinearEquivKer_natural`: the naturality square,
  read in `Γ(X', ⊤)`.
* `Stacks.Thickenings.conormalTopSectionsLinearEquivKer_natural`: **the naturality square**, as
  an equality in `RingHom.ker i^♯`.

Two bookkeeping lemmas are proved on the way:
`AlgebraicGeometry.RingedSpace.val_map_eqToHom_preimage_top` and
`RingedSpaceModuleAdjunction.modulePushforwardSquareIso_inv_val_app_top`, which say that the
comparison of the two ways around the square is the identity on global sections.

## Hypotheses, and why each is there

* `[AlgebraicGeometry.IsClosedImmersion i]`, `[AlgebraicGeometry.IsClosedImmersion j]` and
  `hi : i.ker ^ 2 = ⊥`, `hj : j.ker ^ 2 = ⊥` make both legs first-order thickenings. `hj` is
  what makes the quotient map of `j` invertible, which is how the inclusion-level statement is
  reduced to the ideal sheaf; `hi` is what gives the inclusion of `i` at all.
* `[IsAffine X']` and `[IsAffine Y']` are carried only by the two statements that mention
  `Stacks.Thickenings.conormalTopSectionsLinearEquivKer` or
  `Stacks.Thickenings.conormalMap`, because those two objects are only defined for an affine
  ambient scheme: the descent of scalars along `i^♯` needs
  `Stacks.Smooth.surjective_appTop_of_isFirstOrderThickening`. This is not a weakening — it is
  the setting the identification lives in. The two statements about the **inclusion** carry no
  affineness at all.
* No representability hypothesis, and no hypothesis on the square beyond its commutativity.

## Implementation notes

**The statement elaborates without ascription here**, unlike the comparisons elsewhere in this
area: the left vertical is written as the transpose of
`Stacks.Immersion.immersionConormalSheafMap` applied at `op ⊤`, and both ambient spaces are
scheme variables rather than projections of constructors, so neither of the two known
`whnf` timeouts of this subsystem is reachable from here.

**What did have to be controlled is the opposite: a `CategoryTheory.congrArg` motive.** Chaining
the sheaf-level naturality to the goal through
`AlgebraicGeometry.RingedSpace.comp_val_app_apply` by a bare `congrArg _` reports
`maximum recursion depth has been reached`, and still does with the motive's binder ascribed. The
form that works, and the reason
`Stacks.Thickenings.firstOrderImmersionConormalSheafι_natural_val_app_top` is a separate
declaration, is to peel the composite with `rw` inside a statement whose section argument is
**typed at the spelling the peeling lemma expects** — that is
`((modulePushforward j).obj (conormalSheaf j.liftCoborder)).val.obj (op ⊤)` rather than the
definitionally equal `Γ(conormalModules j, ⊤)`. Against the latter spelling neither `rw` nor
`simp only` finds `AlgebraicGeometry.RingedSpace.comp_val_app_apply` at all, because the
lemma's section argument is indexed by the sheaf. This is the same obstruction that
`Stacks.Thickenings.conormalModules` exists to manage, met from the other side.

**`RingedSpaceModuleAdjunction.modulePushforwardSquareIso_inv_val_app_top` is not `rfl`**: the
components of `RingedSpaceModuleAdjunction.modulePushforwardComp` are identities, but the
transport along the square's commutativity is not, and `rfl` fails on it. It is instead
`RingedSpaceModuleAdjunction.modulePushforwardSquareIso_inv_val_app`, which exhibits the
comparison as a restriction map, followed by the observation that over `⊤` that restriction is
the identity. That observation is
`AlgebraicGeometry.RingedSpace.val_map_eqToHom_preimage_top`, and it is stated with the two
composites as **variables** so that `subst` applies — written at `j₁ ≫ b` and `a ≫ j₂` directly
it cannot be substituted, and replacing the transport by `𝟙` instead produces a term that is
only type-correct at default transparency, which the elaborator then rejects.

## References

* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.ClosedImmersion

universe u

namespace AlgebraicGeometry.RingedSpace

/-- **Restricting a global section along the transport of an equality of morphisms does
nothing.** For `p q : Z ⟶ X` with `p = q`, the two preimages of `⊤` agree, and the restriction
map of a sheaf of modules on `Z` between them is the identity on sections.

The two morphisms are variables and the equality is a hypothesis, which is what lets the proof
substitute it; stated at `j₁ ≫ b` and `a ≫ j₂` — the shape its consumer
`RingedSpaceModuleAdjunction.modulePushforwardSquareIso_inv_val_app_top` meets it at — neither
side is a variable and `subst` does not apply. -/
theorem val_map_eqToHom_preimage_top {Z X : RingedSpace.{u, u}} {p q : Z ⟶ X} (h : p = q)
    (N : SheafOfModules.{u} (structureSheafRing Z))
    (x : N.val.obj (op ((Opens.map q.hom.base).obj (⊤ : Opens X.carrier)))) :
    N.val.map (eqToHom (congrArg
      (fun r : Z ⟶ X => (Opens.map r.hom.base).obj (⊤ : Opens X.carrier)) h)).op x = x := by
  subst h
  exact CategoryTheory.SheafOfModules.val_map_id_apply N x

end AlgebraicGeometry.RingedSpace

namespace RingedSpaceModuleAdjunction

variable {Z₁ Z₂ X₁ X₂ : RingedSpace.{u, u}} (a : Z₁ ⟶ Z₂) (b : X₁ ⟶ X₂) (j₁ : Z₁ ⟶ X₁)
  (j₂ : Z₂ ⟶ X₂)

/-- **The pushforward comparison of a commuting square is the identity on global sections.**
Over `⊤` the two ways around the square have the same preimage, so the restriction map that
`RingedSpaceModuleAdjunction.modulePushforwardSquareIso_inv_val_app` exhibits the comparison as
is the identity.

This is what lets a sheaf-level identity that crosses the square be read on global sections with
no transport left over. It is not `rfl`: the transport along the square's commutativity does not
reduce. -/
theorem modulePushforwardSquareIso_inv_val_app_top (comm : j₁ ≫ b = a ≫ j₂)
    (N : SheafOfModules.{u} (structureSheafRing Z₁))
    (x : ((modulePushforward j₂).obj ((modulePushforward a).obj N)).val.obj
      (op (⊤ : Opens X₂.carrier))) :
    ((modulePushforwardSquareIso a b j₁ j₂ comm).inv.app N).val.app
      (op (⊤ : Opens X₂.carrier)) x = x :=
  (modulePushforwardSquareIso_inv_val_app a b j₁ j₂ comm N (⊤ : Opens X₂.carrier) x).trans
    (AlgebraicGeometry.RingedSpace.val_map_eqToHom_preimage_top comm N x)

end RingedSpaceModuleAdjunction

namespace Stacks.Thickenings

open Stacks.Immersion

variable {X X' Y Y' : Scheme.{u}} (i : X ⟶ X') (j : Y ⟶ Y')

/-! ### The conormal quotient map of a first-order thickening is invertible -/

/-! ### Naturality of the inclusion -/

/-- **Naturality of the inclusion `𝒞_{X/X'} ⊆ 𝒪_{X'}` in the thickening**, at the level of
sheaves on the ambient scheme. For a morphism `(f, f')` of first-order thickenings from
`i : X ⟶ X'` to `j : Y ⟶ Y'`, the transpose along `f^* ⊣ f_*` of
`Stacks.Immersion.immersionConormalSheafMap`, pushed forward along `j` and read across the
square, followed by the inclusion of `i`, is the inclusion of `j` followed by the ambient
structure-sheaf map `f'^♯`.

Equivalently: the regular function on `X'` underlying the conormal section that the square
produces from a conormal section of `j` is the image under `f'^♯` of the regular function on `Y'`
underlying the given one.

The proof is the reduction the module documentation describes. Both sides are composed with the
conormal quotient map of `j`, which is invertible by
`Stacks.Thickenings.isIso_canonicalConormalQuotientMap`, and two identities then apply:
`Stacks.Immersion.canonicalConormalQuotientMap_comp_pushforward_homEquiv` on the left and
`Stacks.Thickenings.canonicalConormalQuotientMap_comp_firstOrderImmersionConormalSheafι` on the
right, after which `Stacks.ClosedImmersion.unit_comp_pushforward_idealSheafMap_comp_ι` closes
it. No affineness is used. -/
theorem firstOrderImmersionConormalSheafι_natural
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion j]
    (hi : i.ker ^ 2 = ⊥) (hj : j.ker ^ 2 = ⊥)
    (f : X ⟶ Y) (f' : X' ⟶ Y') (comm : i ≫ f' = f ≫ j) :
    (modulePushforward j.toLRSHom.toShHom).map
          ((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _
            (immersionConormalSheafMap i j f f' (toShHom_square comm))) ≫
        (modulePushforwardSquareIso f.toLRSHom.toShHom f'.toLRSHom.toShHom
            i.toLRSHom.toShHom j.toLRSHom.toShHom (toShHom_square comm)).inv.app
          (Stacks.ClosedImmersion.conormalSheaf i.liftCoborder.toLRSHom.toShHom) ≫
        (modulePushforward f'.toLRSHom.toShHom).map
          (firstOrderImmersionConormalSheafι i hi) =
      firstOrderImmersionConormalSheafι j hj ≫
        structureSheafModuleHom f'.toLRSHom.toShHom := by
  have := isIso_canonicalConormalQuotientMap j hj
  rw [← cancel_epi (canonicalConormalQuotientMap j), ← Category.assoc,
    canonicalConormalQuotientMap_comp_pushforward_homEquiv, Category.assoc, Category.assoc,
    Iso.hom_inv_id_app_assoc, ← Category.assoc (canonicalConormalQuotientMap j),
    canonicalConormalQuotientMap_comp_firstOrderImmersionConormalSheafι]
  slice_lhs 3 4 => rw [← Functor.map_comp,
    canonicalConormalQuotientMap_comp_firstOrderImmersionConormalSheafι]
  slice_lhs 2 3 => rw [← Functor.map_comp]
  rw [unit_comp_pushforward_idealSheafMap_comp_ι (toShHom_square comm)]

/-- **Naturality of the inclusion `𝒞_{X/X'} ⊆ 𝒪_{X'}` on global sections.**
`Stacks.Thickenings.firstOrderImmersionConormalSheafι_natural` read at `⊤`, with the comparison
of the two pushforward composites discharged by
`RingedSpaceModuleAdjunction.modulePushforwardSquareIso_inv_val_app_top`.

The conormal section is typed as a section of `j_*𝒞_{Y/Y'}` over `⊤` rather than as an element
of `Γ(conormalModules j, ⊤)` on purpose: the two are definitionally equal, but
`AlgebraicGeometry.RingedSpace.comp_val_app_apply` is indexed by the sheaf and is found by
neither `rw` nor `simp` at the second spelling. -/
theorem firstOrderImmersionConormalSheafι_natural_val_app_top
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion j]
    (hi : i.ker ^ 2 = ⊥) (hj : j.ker ^ 2 = ⊥)
    (f : X ⟶ Y) (f' : X' ⟶ Y') (comm : i ≫ f' = f ≫ j)
    (m : ((modulePushforward j.toLRSHom.toShHom).obj
      (Stacks.ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom)).val.obj
      (op (⊤ : Y'.Opens))) :
    (firstOrderImmersionConormalSheafι i hi).val.app (op (⊤ : X'.Opens))
        ((((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _
            (immersionConormalSheafMap i j f f' (toShHom_square comm))).val.app
          (op (⊤ : Y.Opens))) m)
      = f'.appTop.hom
          ((firstOrderImmersionConormalSheafι j hj).val.app (op (⊤ : Y'.Opens)) m) := by
  have hnat :=
    congr($(firstOrderImmersionConormalSheafι_natural i j hi hj f f' comm).val.app
      (op (⊤ : Y'.Opens)) m)
  simp only [AlgebraicGeometry.RingedSpace.comp_val_app_apply] at hnat
  rwa [modulePushforwardSquareIso_inv_val_app_top] at hnat

/-! ### Naturality of the identification -/

/-- **Naturality of the conormal-sections identification in the thickening, read in
`Γ(X', ⊤)`.** The regular function on `X'` underlying the kernel element attached to the conormal
section that the square produces is the image under `f'^♯` of the regular function on `Y'`
underlying the kernel element attached to the given conormal section.

This is `Stacks.Thickenings.coe_conormalTopSectionsLinearEquivKer` on both sides — which is where
the identification is replaced by the inclusion — followed by
`Stacks.Thickenings.firstOrderImmersionConormalSheafι_natural_val_app_top`. -/
theorem coe_conormalTopSectionsLinearEquivKer_natural [IsAffine X'] [IsAffine Y']
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion j]
    (hi : i.ker ^ 2 = ⊥) (hj : j.ker ^ 2 = ⊥)
    (f : X ⟶ Y) (f' : X' ⟶ Y') (comm : i ≫ f' = f ≫ j)
    (m : Γ(conormalModules j, (⊤ : Y.Opens))) :
    letI := Stacks.Smooth.thickeningKerModule (i := i) ⟨inferInstance, hi⟩
    letI := Stacks.Smooth.thickeningKerModule (i := j) ⟨inferInstance, hj⟩
    ((conormalTopSectionsLinearEquivKer i hi
          ((((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _
              (immersionConormalSheafMap i j f f'
                (toShHom_square comm))).val.app
            (op (⊤ : Y.Opens))) m) : RingHom.ker i.appTop.hom) : Γ(X', (⊤ : X'.Opens)))
      = f'.appTop.hom
          ((conormalTopSectionsLinearEquivKer j hj m :
            RingHom.ker j.appTop.hom) : Γ(Y', (⊤ : Y'.Opens))) := by
  exact (coe_conormalTopSectionsLinearEquivKer i hi _).trans
    ((firstOrderImmersionConormalSheafι_natural_val_app_top i j hi hj f f' comm m).trans
      (congrArg f'.appTop.hom (coe_conormalTopSectionsLinearEquivKer j hj m)).symm)

/-- **The identification of the conormal sections with the kernel ideal is natural in the
thickening.** For a morphism `(f, f')` of first-order thickenings from `i : X ⟶ X'` to
`j : Y ⟶ Y'` with both ambient schemes affine,

`conormalTopSectionsLinearEquivKer i ∘ (conormal map of the square on global sections)`
`= conormalMap ∘ conormalTopSectionsLinearEquivKer j`,

the left vertical being the transpose along `f^* ⊣ f_*` of
`Stacks.Immersion.immersionConormalSheafMap` read at `⊤` and the right vertical being
`Stacks.Thickenings.conormalMap`, which by `Stacks.Thickenings.conormalMap_apply` is `f'^♯`
restricted to the kernel ideals.

This is the comparison of the conormal data of two chart thickenings that the naturality step of
[Stacks Project, Tag 04AM] needs. Since the coercion out of `RingHom.ker i^♯` is injective it is
`Stacks.Thickenings.coe_conormalTopSectionsLinearEquivKer_natural` read through
`Subtype.ext`. -/
theorem conormalTopSectionsLinearEquivKer_natural [IsAffine X'] [IsAffine Y']
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion j]
    (hi : i.ker ^ 2 = ⊥) (hj : j.ker ^ 2 = ⊥)
    (f : X ⟶ Y) (f' : X' ⟶ Y') (comm : i ≫ f' = f ≫ j)
    (m : Γ(conormalModules j, (⊤ : Y.Opens))) :
    letI := Stacks.Smooth.thickeningKerModule (i := i) ⟨inferInstance, hi⟩
    letI := Stacks.Smooth.thickeningKerModule (i := j) ⟨inferInstance, hj⟩
    conormalTopSectionsLinearEquivKer i hi
        ((((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _
            (immersionConormalSheafMap i j f f'
              (toShHom_square comm))).val.app
          (op (⊤ : Y.Opens))) m)
      = conormalMap ⟨inferInstance, hi⟩ ⟨inferInstance, hj⟩ comm
          (conormalTopSectionsLinearEquivKer j hj m) :=
  Subtype.ext ((coe_conormalTopSectionsLinearEquivKer_natural i j hi hj f f' comm m).trans
    (conormalMap_apply (i := i) (j := j) ⟨inferInstance, hi⟩ ⟨inferInstance, hj⟩ comm _).symm)

end Stacks.Thickenings

end
