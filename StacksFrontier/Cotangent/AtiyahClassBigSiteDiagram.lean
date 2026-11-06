module

public import StacksFrontier.Cotangent.AtiyahClassBigSiteFirstVertexDerived
public import StacksFrontier.Cotangent.AtiyahClassBigSiteMoore
public import StacksFrontier.Cotangent.UliftBaseChangedDifferentials

/-!
# The sections of `B̲ ⊗_𝒪 Ω_{𝒪/A}` at the site `C_{B/A}` itself

At the site `C_{B/A}` of [Stacks, Tag 08PR] itself, read on its `CategoryTheory.AsSmall` model
`CommAlgCat.atiyahSite`, the first vertex of the Atiyah triangle of [Stacks, Tag 09DD] is the
extended Moore complex of the `B̲`-module `M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A})`
(`CommAlgCat.atiyahFirstVertexMooreIso`), while the Moore complex of the cotangent complex is
computed from the diagram `i^*Ω_{𝒪/A} ⋙ moduleLift ⋙ M ⊗ -`
(`CommAlgCat.atiyahMooreTensorIso`). Identifying those two diagrams is what remains of the
first displayed endpoint of Tag 09DD at this site, and it is what this file provides. The
content is the objectwise comparison

`ULift B ⊗_{ULift P} Ω[ULift P⁄ULift A] = ULift (B ⊗_P Ω[P⁄A])`

over each object `(P, α)` of the site, together with its naturality in `(P, α)`, out of which
the comparison of the two diagrams is assembled.

## Main definitions

* `CommAlgCat.atiyahOverObj` and `CommAlgCat.atiyahSiteRing`: the augmented `A`-algebra
  underlying an object of `CommAlgCat.atiyahSite`, and its carrier in `Type u`;
  `CommAlgCat.atiyahSiteRingMap` and `CommAlgCat.atiyahOverMap` are the map of carriers and the
  map of augmented algebras underlying a morphism of the site.

## Main results

* `CommAlgCat.atiyahDifferentialsSectionsIso`: **the sections of `Ω_{𝒪/A}` over `(P, α)` are
  `Ω[ULift P⁄ULift A]`** for the `ULift A`-algebra structure instance resolution puts on
  `ULift P`, with `CommAlgCat.atiyahDifferentialsSectionsIso_hom_d` and
  `CommAlgCat.atiyahDifferentialsSectionsIso_inv_D` matching the two universal derivations.
* `CommAlgCat.atiyahDifferentialsBaseChangeObjIso`: **the sections of `B̲ ⊗_𝒪 Ω_{𝒪/A}` over
  `(P, α)` are the universe lift of `CommAlgCat.overDifferentials (P, α) = B ⊗_P Ω[P⁄A]`**, with
  `CommAlgCat.atiyahDifferentialsBaseChangeObjIso_naturality` for its naturality in `(P, α)`.
* `CommAlgCat.atiyahFirstVertexDiagramIso`: **the `B̲`-module `M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A})`, read
  as a diagram of `ULift B`-modules, is `M ⊗_B i^*Ω_{𝒪/A}`** -- the first displayed endpoint of
  Tag 09DD at this site, before `Lπ_!`.

## Implementation notes

**Why the comparison is not a formality.** The sections of `Ω_{𝒪/A}` on this site are a module
of Kähler differentials of the universe lift `ULift A → ULift P`, because the morphism of topoi
`π` of [Stacks, Tag 08PF] is formed at a coefficient universe containing the objects of the
site, whereas `CommAlgCat.overDifferentials` is the `Type u` module `B ⊗_P Ω[P⁄A]`. So the base
change on the left is taken over `ULift P` and the one on the right over `P`, and the comparison
has to be written out in both directions; that is what
`StacksFrontier/Cotangent/UliftBaseChangedDifferentials.lean` does, and the gap it closes is the
one `StacksFrontier/Cotangent/PolynomialAlgebraSiteCotangentComplex.lean` records as "a
universe-lift comparison of tensor products, not carried out here". Both sides of
`KaehlerDifferential.uliftBaseChangeEquiv` are the two objects compared here on the nose, by
`KaehlerDifferential.uliftBaseChange_source_eq` and
`KaehlerDifferential.uliftBaseChange_target_eq`; what the comparison needs in addition is that
the augmentation on sections is the universe lift of the `Type u` augmentation, which holds by
`rfl`, and that the sections of `Ω_{𝒪/A}` are the differentials of the lifted algebra, which is
`CommAlgCat.atiyahDifferentialsSectionsIso`.

**Which algebra structure, and why a comparison is needed at all.** The sections of `Ω_{𝒪/A}`
over `(P, α)` are `CommRingCat.KaehlerDifferential` of the map `A̲ ⟶ 𝒪` evaluated there, hence
are formed at the algebra structure `((atiyahBaseHom A B).hom.app V).hom.toAlgebra` that a ring
map induces, while `KaehlerDifferential.uliftBaseChangeEquiv` is stated at the structure
`ULift.algebra'` that instance resolution produces. The two have the same `algebraMap`, so they
are equal by `Algebra.algebra_ext` (`CommAlgCat.atiyahBaseHom_app_toAlgebra_eq`), but they are
**not** definitionally equal, so the passage between them is the genuine comparison
`KaehlerDifferential.congrAlgebraIso` and not a `rfl`. That is why every statement about
elements below comes in two spellings of the universal derivation —
`CommRingCat.KaehlerDifferential.d` at the induced structure and `KaehlerDifferential.D` at the
resolved one — bridged by `CommAlgCat.atiyahDifferentialsSectionsIso_hom_d`.

**How the naturality square is proved.** The square is
`KaehlerDifferential.uliftBaseChange_naturality` applied to the restriction map of
`B̲ ⊗_𝒪 Ω_{𝒪/A}` conjugated by `CommAlgCat.atiyahDifferentialsSectionsIso`: the two pushforwards
that naturality asks for are that conjugated restriction map upstairs and
`CommAlgCat.overDifferentialsPush` downstairs, and the hypothesis to discharge is that each sends
the pure differential `1 ⊗ d p` to `1 ⊗ d (g p)` — downstairs by
`CommAlgCat.overDifferentialsPush_mk`, upstairs by `ModuleCat.ExtendScalars.map_tmul`,
`CommAlgCat.atiyahDifferentialsSectionsIso_inv_D`,
`Stacks.PresheafOfModules.ChangeOfRings.cofMap_tmul`,
`PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d` and
`CommAlgCat.atiyahDifferentialsSectionsIso_hom_d` in turn. Since naturality is stated for every
element, the extensionality step is `CategoryTheory.ConcreteCategory.hom_ext`, and no
extensionality principle for a scalar extension is needed.

Four mechanical obstacles are worth recording, each met and diagnosed rather than guessed. A
morphism of `ModuleCat` whose source is written as
`(atiyahRelativeDifferentialsPresheaf A B).obj V` cannot be applied to an element through the
usual coercion — `ModuleCat.Hom.hom` has to be written out, as in
`CommAlgCat.atiyahDifferentialsSectionsIso_hom_d`. `rw` and `simp only` cannot split
`ConcreteCategory.hom (f ≫ g) x` here, because the change-of-rings application is not
type-correct at `implicit` transparency (`PresheafOfModules (atiyahRingSheaf A B).obj` against
`Stacks.PresheafOfModules.ChangeOfRings.PMod (atiyahStructureSheaf A B).obj`), so
`ConcreteCategory.comp_apply` is used as a term, through `Eq.trans`, which does work; the
remaining rewrites then go through, the goal being left in the coercion form the lemmas are
stated in. `CategoryTheory.Iso.inv_comp_eq` does not see through
`CommAlgCat.atiyahDifferentialsBaseChangeObjIso` to its two factors at reducible transparency, so
the goal is first restated by `show` in the factored form, which is a `rfl`-level conversion.
Finally, rewriting inside a pure tensor needs the map `x ↦ 1 ⊗ x` as a *morphism*, so that
`CategoryTheory.ConcreteCategory.congr_arg` can be applied to it: writing the tensor out instead
sends instance resolution looking for `Module` structures at the sheaf-section spelling of the
rings, where they are not instances. That morphism is
`ModuleCat.ExtendRestrictScalarsAdj.Unit.map`, with its universes pinned.

## References

* [Stacks Project, Tag 09DD](https://stacks.math.columbia.edu/tag/09DD)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ChangeOfRings TensorProduct

universe u

namespace CommAlgCat

section Sections

attribute [local instance] ULift.algebra'

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- **The augmented `A`-algebra underlying an object of `CommAlgCat.atiyahSite`.** The site is
the `CategoryTheory.AsSmall` model of the opposite of the category of polynomial `A`-algebras
augmented to `B`, so an object of it is such an augmented algebra, read in `Over B`. -/
abbrev atiyahOverObj (V : (atiyahSite A B)ᵒᵖ) : Over B :=
  ((atiyahSiteFunctor A B).obj V).unop.unop.obj

/-- The `A`-algebra `P` underlying an object `(P, α)` of `CommAlgCat.atiyahSite`, in `Type u`. -/
abbrev atiyahSiteRing (V : (atiyahSite A B)ᵒᵖ) : Type u := (atiyahOverObj A B V).left

/-- The `ULift A`-algebra structure that the map of sheaves of rings `A̲ ⟶ 𝒪` induces on the
sections of `𝒪` over an object of the site is the one instance resolution produces from
`ULift.algebra'`: both send `a` to `up (algebraMap a.down)`. -/
lemma atiyahBaseHom_app_toAlgebra_eq (V : (atiyahSite A B)ᵒᵖ) :
    ((atiyahBaseHom A B).hom.app V).hom.toAlgebra =
      ULift.algebra' A (ULift.{u + 1} (atiyahSiteRing A B V)) :=
  Algebra.algebra_ext _ _ fun _ => rfl

/-- **The sections of `Ω_{𝒪/A}` over an object `(P, α)` of `C_{B/A}` are
`Ω[ULift P⁄ULift A]`**, for the `ULift A`-algebra structure on `ULift P` that instance
resolution produces. The two algebra structures involved have the same `algebraMap`, so this is
`KaehlerDifferential.congrAlgebraIso`. -/
def atiyahDifferentialsSectionsIso (V : (atiyahSite A B)ᵒᵖ) :
    (atiyahRelativeDifferentialsPresheaf A B).obj V ≅
      ModuleCat.of (ULift.{u + 1} (atiyahSiteRing A B V))
        Ω[ULift.{u + 1} (atiyahSiteRing A B V)⁄ULift.{u + 1} A] :=
  KaehlerDifferential.congrAlgebraIso _ _ (atiyahBaseHom_app_toAlgebra_eq A B V)

/-- The identification of the sections of `Ω_{𝒪/A}` matches the universal derivations. -/
lemma atiyahDifferentialsSectionsIso_hom_d (V : (atiyahSite A B)ᵒᵖ)
    (x : ULift.{u + 1} (atiyahSiteRing A B V)) :
    (atiyahDifferentialsSectionsIso A B V).hom.hom
        (CommRingCat.KaehlerDifferential.d (f := (atiyahBaseHom A B).hom.app V) x) =
      KaehlerDifferential.D (ULift.{u + 1} A) (ULift.{u + 1} (atiyahSiteRing A B V)) x :=
  KaehlerDifferential.congrAlgebraIso_hom_D _ _ (atiyahBaseHom_app_toAlgebra_eq A B V) x

/-- The identification of the sections of `Ω_{𝒪/A}`, read in the other direction. -/
lemma atiyahDifferentialsSectionsIso_inv_D (V : (atiyahSite A B)ᵒᵖ)
    (x : ULift.{u + 1} (atiyahSiteRing A B V)) :
    (atiyahDifferentialsSectionsIso A B V).inv.hom
        (KaehlerDifferential.D (ULift.{u + 1} A)
          (ULift.{u + 1} (atiyahSiteRing A B V)) x) =
      CommRingCat.KaehlerDifferential.d (f := (atiyahBaseHom A B).hom.app V) x := by
  conv_lhs => rw [← atiyahDifferentialsSectionsIso_hom_d A B V x]
  exact ConcreteCategory.congr_hom (atiyahDifferentialsSectionsIso A B V).hom_inv_id _

/-- **The sections of `B̲ ⊗_𝒪 Ω_{𝒪/A}` over an object `(P, α)` of `C_{B/A}` are the universe
lift of `CommAlgCat.overDifferentials (P, α) = B ⊗_P Ω[P⁄A]`.** On the site the base change is
taken over the sections `ULift P` of `𝒪`, in `Type (u + 1)`; the comparison with the `Type u`
module is `KaehlerDifferential.uliftBaseChangeEquiv`, reached after the sections of `Ω_{𝒪/A}`
have been read as `Ω[ULift P⁄ULift A]` by
`CommAlgCat.atiyahDifferentialsSectionsIso`. Both sides of
`KaehlerDifferential.uliftBaseChangeEquiv` are the two objects on the nose, by
`KaehlerDifferential.uliftBaseChange_source_eq` and
`KaehlerDifferential.uliftBaseChange_target_eq`. -/
def atiyahDifferentialsBaseChangeObjIso (V : (atiyahSite A B)ᵒᵖ) :
    ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
          (atiyahAugmentationComm A B).hom).obj
        (atiyahRelativeDifferentialsPresheaf A B)).obj V ≅
      (StacksDraft.TorAmplitude.moduleLift.{u, u, u + 1} (B : Type u)).obj
        ((atiyahCotangentModulePresheaf A B).obj V) :=
  letI : Algebra (atiyahSiteRing A B V) (B : Type u) :=
    (augmentationRingHom (atiyahOverObj A B V)).toAlgebra
  (ModuleCat.extendScalars ((atiyahAugmentationComm A B).hom.app V).hom).mapIso
      (atiyahDifferentialsSectionsIso A B V) ≪≫
    (KaehlerDifferential.uliftBaseChangeEquiv.{u, u + 1} A (atiyahSiteRing A B V)
      (B : Type u)).toModuleIso

/-! ### Naturality in the object of the site -/

/-- The map of `A`-algebras in `Type u` underlying a morphism of `CommAlgCat.atiyahSite`. -/
abbrev atiyahSiteRingMap {V W : (atiyahSite A B)ᵒᵖ} (g : V ⟶ W) :
    atiyahSiteRing A B V →+* atiyahSiteRing A B W :=
  ((atiyahSiteFunctor A B).map g).unop.unop.hom.left.hom.toRingHom

/-- The morphism of `Over B` in `Type u` underlying a morphism of `CommAlgCat.atiyahSite`. -/
abbrev atiyahOverMap {V W : (atiyahSite A B)ᵒᵖ} (g : V ⟶ W) :
    atiyahOverObj A B V ⟶ atiyahOverObj A B W :=
  ((atiyahSiteFunctor A B).map g).unop.unop.hom

/-- The restriction maps of `i^*Ω_{𝒪/A}` at `Type u` coefficients are
`CommAlgCat.overDifferentialsPush`: the presheaf is `CommAlgCat.overDifferentialsFunctor`
restricted along the site, so this is an identity. -/
lemma atiyahCotangentModulePresheaf_map {V W : (atiyahSite A B)ᵒᵖ} (g : V ⟶ W) :
    (atiyahCotangentModulePresheaf A B).map g =
      overDifferentialsPush (atiyahOverMap A B g).left
        (augmentationRingHom_comp (atiyahOverMap A B g)) :=
  rfl

/-- Extension of scalars sends `1 ⊗ x` to the unit applied to `g x`, when `g x = y`. -/
private lemma extendScalars_map_one_tmul {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (f : R →+* S) {M N : ModuleCat.{u + 1} R} (g : M ⟶ N) {x : M} {y : N}
    (h : g.hom x = y) :
    (ModuleCat.extendScalars f).map g ((1 : S) ⊗ₜ[R, f] x) =
      ModuleCat.ExtendRestrictScalarsAdj.Unit.map.{u + 1, u + 1, u + 1} f y :=
  (ModuleCat.ExtendScalars.map_tmul f g 1 x).trans
    (ConcreteCategory.congr_arg (ModuleCat.ExtendRestrictScalarsAdj.Unit.map f) h)

/-- **Naturality of `CommAlgCat.atiyahDifferentialsBaseChangeObjIso` in the object of the
site.** -/
lemma atiyahDifferentialsBaseChangeObjIso_naturality {V W : (atiyahSite A B)ᵒᵖ} (g : V ⟶ W) :
    ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
            (atiyahAugmentationComm A B).hom).obj
          (atiyahRelativeDifferentialsPresheaf A B)).map g ≫
        (atiyahDifferentialsBaseChangeObjIso A B W).hom =
      (atiyahDifferentialsBaseChangeObjIso A B V).hom ≫
        (StacksDraft.TorAmplitude.moduleLift.{u, u, u + 1} (B : Type u)).map
          ((atiyahCotangentModulePresheaf A B).map g) := by
  let : Algebra (atiyahSiteRing A B V) (B : Type u) :=
    (augmentationRingHom (atiyahOverObj A B V)).toAlgebra
  let : Algebra (atiyahSiteRing A B W) (B : Type u) :=
    (augmentationRingHom (atiyahOverObj A B W)).toAlgebra
  show ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
            (atiyahAugmentationComm A B).hom).obj
          (atiyahRelativeDifferentialsPresheaf A B)).map g ≫
        (((ModuleCat.extendScalars ((atiyahAugmentationComm A B).hom.app W).hom).mapIso
              (atiyahDifferentialsSectionsIso A B W)).hom ≫
          (KaehlerDifferential.uliftBaseChangeEquiv.{u, u + 1} A
            (atiyahSiteRing A B W) (B : Type u)).toModuleIso.hom) =
      ((ModuleCat.extendScalars ((atiyahAugmentationComm A B).hom.app V).hom).mapIso
            (atiyahDifferentialsSectionsIso A B V)).hom ≫
        ((KaehlerDifferential.uliftBaseChangeEquiv.{u, u + 1} A
              (atiyahSiteRing A B V) (B : Type u)).toModuleIso.hom ≫
          (StacksDraft.TorAmplitude.moduleLift.{u, u, u + 1} (B : Type u)).map
            ((atiyahCotangentModulePresheaf A B).map g))
  refine (Iso.inv_comp_eq _).1 ?_
  refine ConcreteCategory.hom_ext _ _ fun z => ?_
  refine KaehlerDifferential.uliftBaseChange_naturality.{u, u + 1} A
    (atiyahSiteRing A B V) (B : Type u) (atiyahSiteRing A B W) (atiyahSiteRingMap A B g)
    (ModuleCat.Hom.hom
      (((ModuleCat.extendScalars ((atiyahAugmentationComm A B).hom.app V).hom).mapIso
            (atiyahDifferentialsSectionsIso A B V)).inv ≫
        ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
              (atiyahAugmentationComm A B).hom).obj
            (atiyahRelativeDifferentialsPresheaf A B)).map g ≫
          ((ModuleCat.extendScalars ((atiyahAugmentationComm A B).hom.app W).hom).mapIso
            (atiyahDifferentialsSectionsIso A B W)).hom))
    ?_
    (ModuleCat.Hom.hom (overDifferentialsPush (atiyahOverMap A B g).left
      (augmentationRingHom_comp (atiyahOverMap A B g))))
    (fun q => overDifferentialsPush_mk (atiyahOverMap A B g).left
      (augmentationRingHom_comp (atiyahOverMap A B g)) q) z
  intro p
  have step1 := extendScalars_map_one_tmul ((atiyahAugmentationComm A B).hom.app V).hom
    (atiyahDifferentialsSectionsIso A B V).inv
    (atiyahDifferentialsSectionsIso_inv_D A B V (.up p))
  have step2 :=
    (Stacks.PresheafOfModules.ChangeOfRings.cofMap_tmul (atiyahAugmentationComm A B).hom
        (atiyahRelativeDifferentialsPresheaf A B) g (1 : ULift.{u + 1} (B : Type u))
        (CommRingCat.KaehlerDifferential.d
          (f := (atiyahBaseHom A B).hom.app V) (ULift.up p))).trans
      (ConcreteCategory.congr_arg
        (ModuleCat.ExtendRestrictScalarsAdj.Unit.map.{u + 1, u + 1, u + 1}
          ((atiyahAugmentationComm A B).hom.app W).hom)
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
          (atiyahBaseHom A B).hom g (ULift.up p)))
  have step3 := extendScalars_map_one_tmul ((atiyahAugmentationComm A B).hom.app W).hom
    (atiyahDifferentialsSectionsIso A B W).hom
    (atiyahDifferentialsSectionsIso_hom_d A B W (.up (atiyahSiteRingMap A B g p)))
  exact Eq.trans (ConcreteCategory.comp_apply _ _ _)
    (Eq.trans (ConcreteCategory.comp_apply _ _ _)
      (Eq.trans
        (ConcreteCategory.congr_arg
          ((ModuleCat.extendScalars ((atiyahAugmentationComm A B).hom.app W).hom).mapIso
            (atiyahDifferentialsSectionsIso A B W)).hom
          (Eq.trans
            (ConcreteCategory.congr_arg
              (((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
                      (atiyahAugmentationComm A B).hom).obj
                  (atiyahRelativeDifferentialsPresheaf A B)).map g)
              step1)
            step2))
        step3))

/-! ### The first vertex of the Atiyah triangle as a diagram of `ULift B`-modules -/

variable (M : ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))

/-- **The `B̲`-module attached to `M` by
`Stacks.ChaoticSite.constantModulePresheafEquivalence` has constant sections `M`.** It is
`Stacks.ChaoticSite.constantSectionsModulePresheafIso` at `CommAlgCat.atiyahSite`; the
equivalence being reducible only where it is given, that identification is obtained from its
unit rather than from a reduction. -/
def atiyahModuleOverConstantIso :
    Stacks.ChaoticSite.constantSectionsModulePresheaf
        (C := atiyahSite A B) (ULift.{u + 1} (B : Type u)) M ≅
      atiyahModuleOverConstant A B M :=
  Stacks.ChaoticSite.constantSectionsModulePresheafIso
    (C := atiyahSite A B) (ULift.{u + 1} (B : Type u)) M

/-- **The `B̲`-module `M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A})` at the site `C_{B/A}` itself, read as a
diagram of `ULift B`-modules, is `M ⊗_B i^*Ω_{𝒪/A}`** -- that is, the universe lift of
`CommAlgCat.atiyahCotangentModulePresheaf` tensored with `M`. This is the comparison that
identifies the first vertex of the Atiyah triangle with the first displayed term of
[Stacks, Tag 09DD]; the extended Moore complex of the right-hand side is computed by
`CommAlgCat.atiyahMooreTensorIso`.

Both sides have sections `M ⊗_{ULift B} ULift (B ⊗_P Ω[P⁄A])` over `(P, α)`. The `M` factor of
the left-hand side is reached through `CommAlgCat.atiyahModuleOverConstantIso`, which replaces
the `B̲`-module attached to `M` by the equivalence with the one whose sections are written out,
and `Stacks.ChaoticSite.constantModulePresheafEquivalenceFunctorObjIso` then reads off the
sections of the tensor product. The other factor is
`CommAlgCat.atiyahDifferentialsBaseChangeObjIso` with
`CommAlgCat.atiyahDifferentialsBaseChangeObjIso_naturality`. -/
def atiyahFirstVertexDiagramIso :
    (Stacks.ChaoticSite.constantModulePresheafEquivalence
          (ULift.{u + 1} (B : Type u))).functor.obj
        (atiyahFirstVertexConstantModule A B M) ≅
      atiyahCotangentModulePresheaf A B ⋙
        StacksDraft.TorAmplitude.moduleLift.{u, u, u + 1} (B : Type u) ⋙ tensorLeft M :=
  (Stacks.ChaoticSite.constantModulePresheafEquivalence
      (ULift.{u + 1} (B : Type u))).functor.mapIso
      ((Stacks.tensorRight (O := (atiyahConstantSheaf A B).obj)
        ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
          (atiyahAugmentationComm A B).hom).obj
            (atiyahRelativeDifferentialsPresheaf A B))).mapIso
        (atiyahModuleOverConstantIso A B M).symm) ≪≫
    Stacks.ChaoticSite.constantModulePresheafEquivalenceFunctorObjIso
      (ULift.{u + 1} (B : Type u)) _ _
      (fun V => (tensorLeft M).mapIso (atiyahDifferentialsBaseChangeObjIso A B V))
      (by
        intro V W g
        have key :
            ((Stacks.tensorRight (O := (atiyahConstantSheaf A B).obj)
                  ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
                    (atiyahAugmentationComm A B).hom).obj
                      (atiyahRelativeDifferentialsPresheaf A B))).obj
                (Stacks.ChaoticSite.constantSectionsModulePresheaf
                  (C := atiyahSite A B) (ULift.{u + 1} (B : Type u)) M)).map g ≫
              ((tensorLeft M).mapIso (atiyahDifferentialsBaseChangeObjIso A B W)).hom =
            ((tensorLeft M).mapIso (atiyahDifferentialsBaseChangeObjIso A B V)).hom ≫
              (atiyahCotangentModulePresheaf A B ⋙
                StacksDraft.TorAmplitude.moduleLift.{u, u, u + 1} (B : Type u) ⋙
                  tensorLeft M).map g := by
          apply ModuleCat.hom_ext
          apply TensorProduct.ext
          ext a b
          exact congrArg (fun y => a ⊗ₜ[ULift.{u + 1} (B : Type u)] y)
            (ConcreteCategory.congr_hom
              (atiyahDifferentialsBaseChangeObjIso_naturality A B g) b)
        exact ConcreteCategory.congr_hom key)

end Sections

end CommAlgCat

end
