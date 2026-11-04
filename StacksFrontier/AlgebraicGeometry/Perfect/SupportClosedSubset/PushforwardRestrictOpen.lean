module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Preadditive.LeftExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restricting a direct image to an open of the target

For a morphism of schemes `i : X ⟶ Y` and an open `V ⊆ Y`, the square

```
i ⁻¹ᵁ V --j--> V
|              |
ι              ι
v              v
X ------i-----> Y
```

commutes, and the direct image along `i` followed by restriction to `V` agrees with restriction
to `i ⁻¹ᵁ V` followed by the direct image along `j = i.resLE V (i ⁻¹ᵁ V)`.  This is the
termwise locality of the direct images, the statement the two extended alternating Čech
complexes of [Stacks, Tag 0G7U] are compared with.

## Main definitions

* `Stacks.Perfect.PushforwardRestrict.pushforwardRestrictIso`: the natural isomorphism
  `i_* ⋙ (-)|_V ≅ (-)|_{i ⁻¹ᵁ V} ⋙ j_*`, for an arbitrary morphism of schemes `i`.
* `Stacks.Perfect.PushforwardRestrict.restrictPushforwardRestrictIso`: its form for an open `U`
  of a scheme `Z` and an arbitrary open immersion `g : X' ⟶ Z`, in which the right-hand side is
  written with the open `g ⁻¹ᵁ U` of `X'` rather than with `Scheme.Hom.resLE`.
* `Stacks.Perfect.PushforwardRestrict.restrictUnitFactor` and
  `Stacks.Perfect.PushforwardRestrict.restrictCounitFactor`: the two factors of
  `restrictPushforwardRestrictIso` carrying content, the invertible unit of the restriction
  adjunction along `X' ∩ U ⟶ X'` and the counit cancelling the restriction of a direct image
  along `U ⟶ Z`.
* `Stacks.Perfect.PushforwardRestrict.comparisonFactor₁` to `…comparisonFactor₈`: the eight
  single whiskered factors `restrictPushforwardRestrictIso` is the composite of, and
  `…comparisonChain₂` to `…comparisonChain₇` their partial composites.

## Main results

* `comparisonOpen_eq`: the two opens of `Z` over which the two sides of
  `restrictPushforwardRestrictIso` take their sections agree, so the comparison is on every open
  a restriction map of the coefficient module along an equality of opens.

## Implementation notes

The leg of the comparison is an **arbitrary open immersion** `g : X' ⟶ Z`, not only the
inclusion `W.ι` of an open subscheme.  Nothing in the construction uses more of `g` than that it
is an open immersion: the underlying presheaf of `Scheme.Modules.restrictFunctor g` is
`g.opensFunctor.op ⋙ Z.presheaf` whatever `g` is, so every identification of sections below is
the same `rfl` it was for `W.ι`, and the two opens of `Z` compared by `comparisonOpen_eq` are
computed from `g.opensRange` alone.  (The one place where an open immersion differs from the
inclusion of an open is the comparison `g.appIso` of the two structure sheaves, which is the
identity only for `W.ι`; it enters where a *scalar* acts, that is in `FractionBaseChange`, not
here.)

## Implementation notes

The isomorphism is assembled from the adjunction `restrictFunctor ⊣ pushforward` of Mathlib
rather than constructed on sections.  The one step with content is that the unit of
`Scheme.Modules.restrictAdjunction (i ⁻¹ᵁ V).ι` is invertible on modules of the shape
`(i_* M)|_V`: on an open `W` of `i ⁻¹ᵁ V` its component is the restriction of `M` along the
inclusion `(i ⁻¹ᵁ V).ι ''ᵁ ((i ⁻¹ᵁ V).ι ⁻¹ᵁ (i ⁻¹ᵁ (V.ι ''ᵁ W))) ≤ i ⁻¹ᵁ (V.ι ''ᵁ W)`, and that
inclusion is an equality because `V.ι ''ᵁ W ≤ V`, so `i ⁻¹ᵁ (V.ι ''ᵁ W) ≤ i ⁻¹ᵁ V`.  Being a
restriction along an equality of opens it is invertible; `Subsingleton.elim` replaces the
`homOfLE` by the corresponding `eqToHom`, after which the instance is found.

The remaining steps are formal: the two direct images are composed with
`Scheme.Modules.pushforwardComp`, transported along the commuting square with `eqToIso`, and the
restriction of a direct image along the same open immersion is cancelled by
`Scheme.Modules.restrictFunctorAdjCounitIso`.

For an open `U` of `Z` and an open immersion `g : X' ⟶ Z` the source of `j` is the open
`U.ι ⁻¹ᵁ g.opensRange` of `U`, whereas the extended alternating Čech complex of the restricted
equations is indexed by the open `g ⁻¹ᵁ U` of `X'`.  `restrictPushforwardRestrictIso` performs
that change of index: the comparison `g.resLE U (g ⁻¹ᵁ U) le_rfl` of the two opens is used to
restrict along the two factorisations of one open immersion `(g ⁻¹ᵁ U).toScheme ⟶ Z`, which is
why the statement needs no isomorphism of schemes.

### Why `restrictPushforwardRestrictIso` is spelled as a chain of whiskered single factors

Reading off the effect of the comparison on sections means rewriting with the `app` lemmas of
the Mathlib transformations it is built from, and every one of those lemmas is a `rfl` lemma.
That is only usable if no factor of the chain is a *composite* sitting inside the functor
`Scheme.Modules.pushforward _`: `CategoryTheory.Functor.map_comp` is not a `rfl` lemma, so
distributing such a factor needs `simp only`, which leaves the goal type-incorrect at
`implicit` transparency (the `ConcreteCategory.hom` applications keep the type arguments they
had before the rewrite) and therefore blocks every later `rw` and `simp`.  The chain is
accordingly written with `Functor.isoWhiskerRight` applied to each factor separately, and the
counit factor is given the type with no identity functor in it, so that no
`Functor.leftUnitor` and no `𝟙` survive the reduction either.  The `obj_map` lemmas below
supply the remaining `rfl` identifications of the sections of the functors involved.

The factors are then composed through the partial composites `comparisonChain₂` to
`comparisonChain₇`, that is grouped from the left, and `comparisonFactor₈` is given its type
explicitly so that its target is associated the way `restrictPushforwardRestrictIso` associates
it.  Both are forced by the heartbeat cost of identifying `Γ(Gᵢ.obj M, V)` with `Γ(M, Oᵢ)`; see
the module docstring of `PushforwardRestrictSections`, which reads the section formula off this
chain one partial composite at a time.

## References

* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.PushforwardRestrict

variable {X Y : Scheme.{u}}

/-- Restriction of modules along an open immersion of schemes is left exact, being computed on
sections.  This is what makes the restriction of a finite product of modules the product of the
restrictions, hence what makes the degreewise comparison of the extended alternating Čech
complexes possible. -/
public instance preservesFiniteLimits_restrictFunctor (g : X ⟶ Y) [IsOpenImmersion g] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor g) := by
  have : PreservesLimitsOfSize.{0, 0} (Scheme.Modules.toPresheaf Y) :=
    preservesLimitsOfSize_shrink _
  have : PreservesFiniteLimits (Scheme.Modules.toPresheaf Y) := inferInstance
  have : PreservesFiniteLimits
      ((Functor.whiskeringLeft _ _ Ab.{u}).obj g.opensFunctor.op) := inferInstance
  have e : Scheme.Modules.restrictFunctor g ⋙ Scheme.Modules.toPresheaf X ≅
      Scheme.Modules.toPresheaf Y ⋙
        (Functor.whiskeringLeft _ _ _).obj g.opensFunctor.op := Iso.refl _
  have : PreservesFiniteLimits
      (Scheme.Modules.restrictFunctor g ⋙ Scheme.Modules.toPresheaf X) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (Scheme.Modules.toPresheaf X)

/-- On an open `W` of `i ⁻¹ᵁ V`, the two opens of `X` whose sections the unit of the restriction
adjunction compares agree. -/
public theorem image_preimage_image_eq (i : X ⟶ Y) (V : Y.Opens) (W : V.toScheme.Opens) :
    (i ⁻¹ᵁ V).ι ''ᵁ ((i ⁻¹ᵁ V).ι ⁻¹ᵁ (i ⁻¹ᵁ (V.ι ''ᵁ W))) = i ⁻¹ᵁ (V.ι ''ᵁ W) := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  refine inf_eq_right.mpr fun x hx => ?_
  change i x ∈ V.ι ''ᵁ W at hx
  obtain ⟨y, -, hxy⟩ := hx
  show i x ∈ V
  rw [← hxy]
  exact y.property

/-- **The direct image along `i` restricted to an open `V` of the target.**  It is the
restriction to `i ⁻¹ᵁ V` followed by the direct image along the induced morphism
`i ⁻¹ᵁ V ⟶ V`. -/
@[ega "0 3.4.3" "(F), special case"]
public def pushforwardRestrictIso (i : X ⟶ Y) (V : Y.Opens) :
    Scheme.Modules.pushforward i ⋙ Scheme.Modules.restrictFunctor V.ι ≅
      Scheme.Modules.restrictFunctor (i ⁻¹ᵁ V).ι ⋙
        Scheme.Modules.pushforward (i.resLE V (i ⁻¹ᵁ V) le_rfl) := by
  let U := i ⁻¹ᵁ V
  let j := i.resLE V U le_rfl
  let G := Scheme.Modules.pushforward i ⋙ Scheme.Modules.restrictFunctor V.ι
  let η := Functor.whiskerRight (Scheme.Modules.restrictAdjunction U.ι).unit G
  have hη : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.2
    intro W
    change IsIso (M.presheaf.map (homOfLE
      (U.ι.image_preimage_le (i ⁻¹ᵁ (V.ι ''ᵁ W)))).op)
    have heh : (homOfLE (U.ι.image_preimage_le (i ⁻¹ᵁ (V.ι ''ᵁ W))) :
          U.ι ''ᵁ (U.ι ⁻¹ᵁ (i ⁻¹ᵁ (V.ι ''ᵁ W))) ⟶ i ⁻¹ᵁ (V.ι ''ᵁ W)) =
        eqToHom (image_preimage_image_eq i V W) := Subsingleton.elim _ _
    rw [heh]
    infer_instance
  let c : U.ι ≫ i = j ≫ V.ι := (i.resLE_comp_ι le_rfl).symm
  let e := Scheme.Modules.pushforwardComp U.ι i ≪≫
    eqToIso (congrArg Scheme.Modules.pushforward c) ≪≫
      (Scheme.Modules.pushforwardComp j V.ι).symm
  exact (Functor.leftUnitor G).symm ≪≫ asIso η ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor U.ι)
      (Functor.isoWhiskerRight e (Scheme.Modules.restrictFunctor V.ι)) ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward j)
      (Scheme.Modules.restrictFunctorAdjCounitIso V.ι) ≪≫
    Functor.rightUnitor _

section TwoOpens

variable {Z X' : Scheme.{u}} (U : Z.Opens) (g : X' ⟶ Z) [IsOpenImmersion g]

/-- The open immersion `X' ∩ U ⟶ U` induced by `g`, where `X' ∩ U` is read as the open
`g ⁻¹ᵁ U` of `X'`. -/
public def interToFst : (g ⁻¹ᵁ U).toScheme ⟶ U.toScheme := g.resLE U (g ⁻¹ᵁ U) le_rfl

public instance : IsOpenImmersion (interToFst U g) := by
  delta interToFst Scheme.Hom.resLE; infer_instance

omit [IsOpenImmersion g] in
/-- The two factorisations of the open immersion `X' ∩ U ⟶ Z` agree. -/
public theorem interToFst_comp : interToFst U g ≫ U.ι = (g ⁻¹ᵁ U).ι ≫ g :=
  g.resLE_comp_ι le_rfl

/-- The image of the part of an open lying in `U` is the intersection with `U`. -/
public theorem fst_image_preimage (T : Z.Opens) : U.ι ''ᵁ (U.ι ⁻¹ᵁ T) = U ⊓ T := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

/-- Intersecting with `U` absorbs the intersection with `X' ∩ U`: the two opens of `Z` whose
sections the unit of the restriction adjunction compares agree. -/
public theorem image_inter_eq (V : X'.Opens) :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ ((g ⁻¹ᵁ U).ι ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V)))) =
      U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)) := by
  simp only [fst_image_preimage]
  refine le_antisymm (inf_le_inf_left _ (Scheme.Hom.image_mono _ inf_le_right)) ?_
  rintro x ⟨hxU, y, hyV, hxy⟩
  subst hxy
  exact ⟨hxU, y, ⟨hxU, hyV⟩, rfl⟩

/-- **The two opens the comparison of the direct images is a restriction along.**  Over an open
`V` of `X'`, the sections of `(U → Z)_*(M|_U)` restricted along `g` are the sections of `M` on
`U ∩ g(V)` written as `U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V))`, and those of
`(X' ∩ U → X')_*((g^*M)|_{X' ∩ U})` are the same open written as the image under `g` of the part
of `V` lying in `U`. -/
public theorem comparisonOpen_eq (V : X'.Opens) :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)) =
      g ''ᵁ ((g ⁻¹ᵁ U).ι ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V)) := by
  rw [← image_inter_eq U g V, fst_image_preimage]
  refine inf_eq_right.mpr (le_trans (Scheme.Hom.image_mono g ?_) (g.image_preimage_le U))
  rw [fst_image_preimage (g ⁻¹ᵁ U) V]
  exact inf_le_left

/-! ### Sections of the functors the comparison is built from

The comparison is assembled from natural transformations of Mathlib whose effect on sections is
a restriction map of the coefficient module.  Reading off that effect means rewriting with the
`app` lemmas of those transformations and with the following identifications of the sections of
the functors involved, all of which hold by definition. -/

/-- Applying an identity morphism of modules to a section. -/
public theorem id_app_apply {Y₁ : Scheme.{u}} {M : Y₁.Modules} (V : Y₁.Opens) (x : Γ(M, V)) :
    (𝟙 M : M ⟶ M).app V x = x := rfl

/-- The restriction along an open immersion of a morphism of modules, on sections. -/
public theorem restrictFunctor_map_app {X₁ Y₁ : Scheme.{u}} (h : X₁ ⟶ Y₁) [IsOpenImmersion h]
    {M N : Y₁.Modules} (φ : M ⟶ N) (V : X₁.Opens) :
    ((Scheme.Modules.restrictFunctor h).map φ).app V = φ.app (h ''ᵁ V) := rfl

/-- The sections of a restriction of a module. -/
public theorem restrictFunctor_obj_map {X₁ Y₁ : Scheme.{u}} (h : X₁ ⟶ Y₁) [IsOpenImmersion h]
    (M : Y₁.Modules) {V₁ V₂ : X₁.Opens} (i : V₂ ⟶ V₁) :
    ((Scheme.Modules.restrictFunctor h).obj M).presheaf.map i.op =
      M.presheaf.map ((Scheme.Hom.opensFunctor h).map i).op := rfl

/-- The sections of the direct image of a restriction. -/
public theorem pushRestrict_obj_map (M : Z.Modules) {V₁ V₂ : Z.Opens} (i : V₂ ⟶ V₁) :
    ((Scheme.Modules.restrictFunctor U.ι ⋙
        Scheme.Modules.pushforward U.ι).obj M).presheaf.map i.op =
      M.presheaf.map (homOfLE (Scheme.Hom.image_mono U.ι
        (show U.ι ⁻¹ᵁ V₂ ≤ U.ι ⁻¹ᵁ V₁ from fun _ hx => leOfHom i hx))).op := rfl

/-- The sections of the direct image of a restriction, restricted to a second open. -/
public theorem restrictPushRestrict_obj_map (M : Z.Modules) {V₁ V₂ : X'.Opens}
    (i : V₂ ⟶ V₁) :
    ((Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward U.ι ⋙
        Scheme.Modules.restrictFunctor g).obj M).presheaf.map i.op =
      M.presheaf.map (homOfLE (Scheme.Hom.image_mono U.ι
        (show U.ι ⁻¹ᵁ (g ''ᵁ V₂) ≤ U.ι ⁻¹ᵁ (g ''ᵁ V₁) from
          fun _ hx => Scheme.Hom.image_mono g (leOfHom i) hx))).op := rfl

/-! ### The factors of the comparison -/

/-- **The unit factor of the comparison.**  The unit of the restriction adjunction along
`X' ∩ U ⟶ X'` is invertible on a module of the shape `g^*((U → Z)_*(M|_U))`: on an open `V` of
`X'` its component is the restriction of `M` along an equality of opens (`image_inter_eq`). -/
public def restrictUnitFactor :
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward U.ι ⋙
        Scheme.Modules.restrictFunctor g ≅
      (Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward U.ι ⋙
          Scheme.Modules.restrictFunctor g) ⋙
        Scheme.Modules.restrictFunctor (g ⁻¹ᵁ U).ι ⋙
          Scheme.Modules.pushforward (g ⁻¹ᵁ U).ι := by
  have hη : IsIso (Functor.whiskerLeft
      (Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward U.ι ⋙
        Scheme.Modules.restrictFunctor g)
      (Scheme.Modules.restrictAdjunction (g ⁻¹ᵁ U).ι).unit :
      (Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward U.ι ⋙
          Scheme.Modules.restrictFunctor g) ⟶
        (Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward U.ι ⋙
            Scheme.Modules.restrictFunctor g) ⋙
          Scheme.Modules.restrictFunctor (g ⁻¹ᵁ U).ι ⋙
            Scheme.Modules.pushforward (g ⁻¹ᵁ U).ι) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.2
    intro V
    change IsIso (M.presheaf.map (eqToHom (image_inter_eq U g V)).op)
    infer_instance
  exact asIso (Functor.whiskerLeft
      (Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward U.ι ⋙
        Scheme.Modules.restrictFunctor g)
      (Scheme.Modules.restrictAdjunction (g ⁻¹ᵁ U).ι).unit :
    (Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward U.ι ⋙
        Scheme.Modules.restrictFunctor g) ⟶
      (Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward U.ι ⋙
          Scheme.Modules.restrictFunctor g) ⋙
        Scheme.Modules.restrictFunctor (g ⁻¹ᵁ U).ι ⋙
          Scheme.Modules.pushforward (g ⁻¹ᵁ U).ι)

public theorem restrictUnitFactor_hom_app (M : Z.Modules) :
    (restrictUnitFactor U g).hom.app M =
      (Scheme.Modules.restrictAdjunction (g ⁻¹ᵁ U).ι).unit.app
        ((Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward U.ι ⋙
          Scheme.Modules.restrictFunctor g).obj M) := rfl

/-- **The counit factor of the comparison.**  The counit of the restriction adjunction along
`U ⟶ Z` cancels the restriction of a direct image along the same open immersion.  It is written
without an identity functor in its target, so that its component is a single restriction map. -/
public def restrictCounitFactor :
    Scheme.Modules.restrictFunctor U.ι ⋙ (Scheme.Modules.pushforward U.ι ⋙
        Scheme.Modules.restrictFunctor U.ι) ⋙ Scheme.Modules.restrictFunctor (interToFst U g) ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.restrictFunctor (interToFst U g) :=
  asIso (Functor.whiskerLeft (Scheme.Modules.restrictFunctor U.ι)
      (Functor.whiskerRight (Scheme.Modules.restrictAdjunction U.ι).counit
        (Scheme.Modules.restrictFunctor (interToFst U g)))
    : Scheme.Modules.restrictFunctor U.ι ⋙ (Scheme.Modules.pushforward U.ι ⋙
          Scheme.Modules.restrictFunctor U.ι) ⋙
          Scheme.Modules.restrictFunctor (interToFst U g) ⟶
        Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.restrictFunctor (interToFst U g))

public theorem restrictCounitFactor_hom_app (M : Z.Modules) :
    (restrictCounitFactor U g).hom.app M =
      (Scheme.Modules.restrictFunctor (interToFst U g)).map
        ((Scheme.Modules.restrictAdjunction U.ι).counit.app
          ((Scheme.Modules.restrictFunctor U.ι).obj M)) := rfl

/-! ### The eight factors of the comparison

The comparison is the composite of the eight isomorphisms below.  Each of them is a single
Mathlib transformation, whiskered on the left and on the right but never a composite sitting
inside a functor, so its effect on sections is a *single* restriction map of the coefficient
module; see `PushforwardRestrictSections`.  Their types are left to be inferred: writing them
out would repeat the eight parenthesisations of the same five functors, and the composite below
pins the two ends down. -/

/-- **Factor 1 of the comparison:** the invertible unit of the restriction adjunction along
`X' ∩ U ⟶ X'`. -/
public def comparisonFactor₁ := restrictUnitFactor U g

/-- **Factor 2 of the comparison:** the restriction along `X' ∩ U ⟶ X' ⟶ Z`, written as the
composite of the restrictions along `X' ∩ U ⟶ X'` and `g`. -/
public def comparisonFactor₂ :=
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft
      (Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward U.ι)
      (Scheme.Modules.restrictFunctorComp (g ⁻¹ᵁ U).ι g).symm)
    (Scheme.Modules.pushforward (g ⁻¹ᵁ U).ι)

/-- **Factor 3 of the comparison:** the two factorisations of the open immersion
`X' ∩ U ⟶ Z`, inside the restriction. -/
public def comparisonFactor₃ :=
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft
      (Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward U.ι)
      (Scheme.Modules.restrictFunctorCongr (interToFst_comp U g)).symm)
    (Scheme.Modules.pushforward (g ⁻¹ᵁ U).ι)

/-- **Factor 4 of the comparison:** the restriction along `X' ∩ U ⟶ U ⟶ Z`, written as the
composite of the restrictions along `X' ∩ U ⟶ U` and `U ⟶ Z`. -/
public def comparisonFactor₄ :=
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft
      (Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward U.ι)
      (Scheme.Modules.restrictFunctorComp (interToFst U g) U.ι))
    (Scheme.Modules.pushforward (g ⁻¹ᵁ U).ι)

/-- **Factor 5 of the comparison:** the counit cancelling the restriction to `U` of a direct
image along `U ⟶ Z`. -/
public def comparisonFactor₅ :=
  Functor.isoWhiskerRight (restrictCounitFactor U g)
    (Scheme.Modules.pushforward (g ⁻¹ᵁ U).ι)

/-- **Factor 6 of the comparison:** the inverse of factor 4, now with no direct image in
between. -/
public def comparisonFactor₆ :=
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorComp (interToFst U g) U.ι).symm
    (Scheme.Modules.pushforward (g ⁻¹ᵁ U).ι)

/-- **Factor 7 of the comparison:** the inverse of factor 3, now with no direct image in
between. -/
public def comparisonFactor₇ :=
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorCongr (interToFst_comp U g))
    (Scheme.Modules.pushforward (g ⁻¹ᵁ U).ι)

/-- **Factor 8 of the comparison:** the inverse of factor 2, now with no direct image in
between.  This one is given its type explicitly, with the three functors of the target of
`restrictPushforwardRestrictIso` associated the way that declaration associates them: the last
step of the section formula would otherwise have to reassociate them, and it cannot afford
the extra identification. -/
public def comparisonFactor₈ :
    Scheme.Modules.restrictFunctor ((g ⁻¹ᵁ U).ι ≫ g) ⋙
        Scheme.Modules.pushforward (g ⁻¹ᵁ U).ι ≅
      Scheme.Modules.restrictFunctor g ⋙ Scheme.Modules.restrictFunctor (g ⁻¹ᵁ U).ι ⋙
        Scheme.Modules.pushforward (g ⁻¹ᵁ U).ι :=
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorComp (g ⁻¹ᵁ U).ι g)
    (Scheme.Modules.pushforward (g ⁻¹ᵁ U).ι)

/-- The first 2 factors of the comparison. -/
public def comparisonChain₂ := comparisonFactor₁ U g ≪≫ comparisonFactor₂ U g

/-- The first 3 factors of the comparison. -/
public def comparisonChain₃ := comparisonChain₂ U g ≪≫ comparisonFactor₃ U g

/-- The first 4 factors of the comparison. -/
public def comparisonChain₄ := comparisonChain₃ U g ≪≫ comparisonFactor₄ U g

/-- The first 5 factors of the comparison. -/
public def comparisonChain₅ := comparisonChain₄ U g ≪≫ comparisonFactor₅ U g

/-- The first 6 factors of the comparison. -/
public def comparisonChain₆ := comparisonChain₅ U g ≪≫ comparisonFactor₆ U g

/-- The first 7 factors of the comparison. -/
public def comparisonChain₇ := comparisonChain₆ U g ≪≫ comparisonFactor₇ U g

/-- **The direct image of a restriction to an open, restricted along an open immersion.**  For
an open `U` of a scheme `Z` and an open immersion `g : X' ⟶ Z`, restricting `(U → Z)_*(F|_U)`
along `g` gives `(X' ∩ U → X')_*((g^*F)|_{X' ∩ U})`, where `X' ∩ U` is read as the open
`g ⁻¹ᵁ U` of `X'`.  This is the termwise locality of the direct images indexing the extended
alternating Čech complex.

It is written as the chain `comparisonChain₂`, …, `comparisonChain₇` of partial composites,
grouped from the left, rather than as the eight factors in a row.  The reason is the section
formula of `PushforwardRestrictSections`, which is read off one partial composite at a time: an
identification of `Γ(Gᵢ.obj M, V)` with `Γ(M, Oᵢ)` is expensive, two of the eight of them are
expensive enough that no declaration can afford both, and grouping from the left means every
declaration mentions only the section group the chain starts at and one other. -/
public def restrictPushforwardRestrictIso :
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward U.ι ⋙
        Scheme.Modules.restrictFunctor g ≅
      Scheme.Modules.restrictFunctor g ⋙ Scheme.Modules.restrictFunctor (g ⁻¹ᵁ U).ι ⋙
        Scheme.Modules.pushforward (g ⁻¹ᵁ U).ι :=
  comparisonChain₇ U g ≪≫ comparisonFactor₈ U g

end TwoOpens

end Stacks.Perfect.PushforwardRestrict

end
