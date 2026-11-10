module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffineOverBaseCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantPerfectComplex
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.InfiniteProducts
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks

/-!
# The Čech *terms* of a covering of `X_étale` are affine over `Y`

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site.  The Čech route to the étale clause
of [Stacks, Tag 071N] above degree zero, which ends at
`AlgebraicGeometry.SmallEtale.isCartesianOnAffines_rightDerived_pushforward_sheafLevelCech`, asks
for a covering family of the final object of `X_étale` whose Čech **terms** are affine over `Y`.
The terms sit at the iterated fibre products *over `X`* of the members, so affineness over `Y` of
the members is strictly weaker than what is asked:  for an affine open cover of a non-separated
`X` the iterated fibre products are the intersections of the affine opens, which need not be
affine, and `AlgebraicGeometry.SmallEtale.isAffine_toScheme_piObj` supplies affineness only over
an affine object of `X_étale`, which the final object is not.

This file closes that gap, at a hypothesis on `a` which is named and is not removable by this
argument:  **`a` separated**.

## The argument

Three steps, each a composition or cancellation of affine morphisms.

* If `a` is separated and `U ⟶ Y` is affine then the structure morphism `U ⟶ X` is affine.  This
  is [Stacks, Tag 01SG] part (2), `AlgebraicGeometry.isAffineHom_of_isAffineHom_of_isSeparated`,
  applied to the factorisation `U ⟶ X ⟶ Y` of the structure morphism to `Y`:  the composite is
  affine and the second factor separated, so the first factor is affine.  This is
  `AlgebraicGeometry.SmallEtale.isAffineHom_structureHom_of_isAffineHom_toBaseHom`.
* An iterated fibre product over `X` of objects *affine over `X`* is affine over `X`.  The
  functor to schemes preserves the fibre products of the site, and a finite product in
  `CategoryTheory.Over X` of schemes affine over `X` is affine over `X` by
  `AlgebraicGeometry.isAffineHom_over_finiteProduct`;  no affineness of `X` itself is used, which
  is what distinguishes this from `AlgebraicGeometry.SmallEtale.isAffine_toScheme_piObj`.  This
  is `AlgebraicGeometry.SmallEtale.isAffineHom_structureHom_piObj`.
* A projection of the iterated fibre product onto one of its factors is affine — again
  [Stacks, Tag 01SG] part (2), now over `X`:  the structure morphism of the product to `X` is
  affine and that of the factor is separated, an affine morphism being separated.  Composing
  that projection with the factor's affine morphism to `Y` gives the term's morphism to `Y`.

## Why separatedness of `a` is needed and where it bites

Only the first step uses it, and it is where the mathematics genuinely needs it:  for a
non-separated `a` the intersection of two affine opens of `X` is a quasi-compact immersion into
an affine scheme, hence quasi-affine and not affine, and quasi-affine schemes carry nonvanishing
higher quasi-coherent cohomology.  So a *one-step* Čech resolution cannot be made acyclic for
`(ε_a)_*` without separatedness;  removing the hypothesis asks for an affine hypercovering, not
for a better argument about covers.  **The hypothesis is named in the declarations and is not
hidden in a docstring.**

It is not a weakening of [Stacks, Tag 071N] *for separated `a`*, and it is not a proof of the tag
for general `a`:  the tag's own hypothesis is that `a` be quasi-compact and quasi-separated, and
quasi-separated does not give separated.

## Main results

* `AlgebraicGeometry.SmallEtale.isAffineHom_structureHom_of_isAffineHom_toBaseHom`: for a
  **separated** `a`, an object of `X_étale` affine over `Y` is affine over `X`.
* `AlgebraicGeometry.SmallEtale.isAffineHom_structureHom_piObj`: an iterated fibre product of a
  covering family of the final object of `S_étale` whose members are affine over `S` is affine
  over `S`.  No hypothesis on `S`.
* `AlgebraicGeometry.SmallEtale.isAffineHom_toBaseHom_piObj_of_isSeparatedHom`: **for a separated
  `a`, the iterated fibre products of a covering family whose members are affine over `Y` are
  affine over `Y`** — the Čech terms, not just the members.
* `SmallEtale.exists_coversTop_isAffineHom_piObj_of_isSeparated_of_isSeparatedHom`:
  **a covering family of the final object of `X_étale` whose members *and all their iterated
  fibre products over `X`* are affine over `Y`**, for a separated `Y` and a separated `a`.  This
  is the geometric input of the Čech route, with the gap of
  `AlgebraicGeometry.SmallEtale.exists_coversTop_isAffineHom_of_isSeparated` closed.

**No `@[stacks]` attribute is placed.**  None of these statements is a statement of
[Stacks, Tag 071N] or of [Stacks, Tag 01SG];  they are the geometry of a cover, assembled.

## References

* [Stacks Project, Tag 01SG](https://stacks.math.columbia.edu/tag/01SG)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

section Site

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An iterated fibre product of a covering family of the final object of `S_étale` whose
members are affine over `S` is affine over `S`.**

The functor to schemes preserves the fibre products of the family
(`Stacks.Sites.preservesLimit_fibreProducts_overPost`), and a finite product in
`CategoryTheory.Over S` of schemes affine over `S` is affine over `S`
(`AlgebraicGeometry.isAffineHom_over_finiteProduct`), so the product's structure morphism is
affine.  Nothing is assumed of `S`:  this is the statement
`AlgebraicGeometry.SmallEtale.isAffine_toScheme_piObj` becomes when "affine object" is replaced
throughout by "affine structure morphism", and in that form the hypothesis that the *target* of
the family be affine disappears — which is what makes it usable at the final object. -/
public theorem isAffineHom_structureHom_piObj
    (E : PreZeroHypercover.{u} (final B S hS))
    (hX : ∀ j, IsAffineHom (B.inclusion.map (E.X j).obj.hom))
    (p : ℕ) (i : Fin (p + 1) → E.I₀) :
    letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.I₀),
        HasProduct (fun b ↦ Over.mk (E.f (j b))) := fun q j ↦
      Stacks.Sites.hasProduct_fibreProducts E (fun _ _ _ ↦ inferInstance) q j
    IsAffineHom
      (B.inclusion.map (∏ᶜ (fun b ↦ Over.mk (E.f (i b)))).left.obj.hom) := by
  let : ∀ (q : ℕ) (j : Fin (q + 1) → E.I₀),
      HasProduct (fun b ↦ Over.mk (E.f (j b))) := fun q j ↦
    Stacks.Sites.hasProduct_fibreProducts E (fun _ _ _ ↦ inferInstance) q j
  let w : SmallEtale B S hS ⥤ Scheme.{u} := toScheme B S hS
  let U := final B S hS
  let A : Fin (p + 1) → Over U := fun b ↦ Over.mk (E.f (i b))
  let _ : PreservesLimit (Discrete.functor A) (Over.post (X := U) w) :=
    Stacks.Sites.preservesLimit_fibreProducts_overPost w E
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) p i
  have hF : ∀ b, IsAffineHom ((Over.post (X := U) w).obj (A b)).hom := fun b ↦ by
    change IsAffineHom (w.map (E.f (i b)))
    rw [toScheme_map_to_final B S hS (E.f (i b))]
    exact hX (i b)
  have hprod : IsAffineHom (∏ᶜ (fun b ↦ (Over.post (X := U) w).obj (A b))).hom :=
    isAffineHom_over_finiteProduct _ hF
  have e := PreservesProduct.iso (Over.post (X := U) w) A
  have hw : ((Over.forget (w.obj U)).mapIso e).hom ≫
      (∏ᶜ (fun b ↦ (Over.post (X := U) w).obj (A b))).hom =
      ((Over.post (X := U) w).obj (∏ᶜ A)).hom := Over.w e.hom
  have hfac : B.inclusion.map (∏ᶜ A).left.obj.hom =
      ((Over.forget (w.obj U)).mapIso e).hom ≫
        (∏ᶜ (fun b ↦ (Over.post (X := U) w).obj (A b))).hom :=
    (toScheme_map_to_final B S hS (∏ᶜ A).hom).symm.trans hw.symm
  have hiso : IsAffineHom ((Over.forget (w.obj U)).mapIso e).hom := inferInstance
  have hmul : MorphismProperty.IsMultiplicative (C := Scheme.{u})
      (fun _ _ f ↦ IsAffineHom f) := inferInstance
  have := hmul.toIsStableUnderComposition
  exact hfac ▸ MorphismProperty.comp_mem (C := Scheme.{u})
    (fun _ _ f ↦ IsAffineHom f) _ _ hiso hprod

end Site

section Base

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- **For a separated `a`, an object of `X_étale` affine over `Y` is affine over `X`.**

[Stacks, Tag 01SG] part (2) at the factorisation `U ⟶ X ⟶ Y` of the structure morphism of `U` to
`Y`:  that composite is affine by hypothesis and its second factor `a` is separated, so the first
factor — the structure morphism of `U` to `X` — is affine.

Separatedness of `a` is used and is not removable:  an affine open of a non-separated `X` need
not be affine over `X`. -/
public theorem isAffineHom_structureHom_of_isAffineHom_toBaseHom
    [IsSeparated (schemeHom B a)] (U : SmallEtale B X.obj X.property)
    (hU : IsAffineHom (toBaseHom B a U)) :
    IsAffineHom (B.inclusion.map U.obj.hom) :=
  have := hU
  isAffineHom_of_isAffineHom_of_isSeparated (B.inclusion.map U.obj.hom) (schemeHom B a) rfl

/-- **For a separated `a`, the iterated fibre products over `X` of a covering family of the final
object of `X_étale` whose members are affine over `Y` are themselves affine over `Y`.**  These
are the *terms* of the sheaf-level Čech complex of the family, as opposed to its members.

The members are affine over `X` by
`AlgebraicGeometry.SmallEtale.isAffineHom_structureHom_of_isAffineHom_toBaseHom`, hence so is the
iterated fibre product by `AlgebraicGeometry.SmallEtale.isAffineHom_structureHom_piObj`;  the
projection onto the factor of index `0` is then affine by [Stacks, Tag 01SG] part (2) over `X`,
an affine morphism being separated, and composing it with that factor's affine morphism to `Y`
is the term's morphism to `Y`.

Separatedness of `a` is carried and is named;  nothing is assumed of `X`, of `Y` or of the
degree. -/
public theorem isAffineHom_toBaseHom_piObj_of_isSeparatedHom
    [IsSeparated (schemeHom B a)]
    (E : PreZeroHypercover.{u} (final B X.obj X.property))
    (hE : ∀ j, IsAffineHom (toBaseHom B a (E.X j)))
    (p : ℕ) (i : Fin (p + 1) → E.I₀) :
    letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.I₀),
        HasProduct (fun b ↦ Over.mk (E.f (j b))) := fun q j ↦
      Stacks.Sites.hasProduct_fibreProducts E (fun _ _ _ ↦ inferInstance) q j
    IsAffineHom (toBaseHom B a (∏ᶜ (fun b ↦ Over.mk (E.f (i b)))).left) := by
  let : ∀ (q : ℕ) (j : Fin (q + 1) → E.I₀),
      HasProduct (fun b ↦ Over.mk (E.f (j b))) := fun q j ↦
    Stacks.Sites.hasProduct_fibreProducts E (fun _ _ _ ↦ inferInstance) q j
  let w : SmallEtale B X.obj X.property ⥤ Scheme.{u} := toScheme B X.obj X.property
  let A : Fin (p + 1) → Over (final B X.obj X.property) := fun b ↦ Over.mk (E.f (i b))
  have hstruct : ∀ j, IsAffineHom (B.inclusion.map (E.X j).obj.hom) := fun j ↦
    isAffineHom_structureHom_of_isAffineHom_toBaseHom B a _ (hE j)
  have hP : IsAffineHom (B.inclusion.map (∏ᶜ A).left.obj.hom) :=
    isAffineHom_structureHom_piObj B X.obj X.property E hstruct p i
  have hproj : IsAffineHom (w.map (Pi.π A (0 : Fin (p + 1))).left) := by
    have := hP
    have := hstruct (i 0)
    have : IsSeparated (B.inclusion.map (E.X (i 0)).obj.hom) := IsSeparated.of_isAffineHom _
    exact isAffineHom_of_isAffineHom_of_isSeparated
      (w.map (Pi.π A (0 : Fin (p + 1))).left) (B.inclusion.map (E.X (i 0)).obj.hom)
      (toScheme_map_comp B X.obj X.property (Pi.π A (0 : Fin (p + 1))).left)
  have hfac : toBaseHom B a (∏ᶜ A).left =
      w.map (Pi.π A (0 : Fin (p + 1))).left ≫ toBaseHom B a (E.X (i 0)) :=
    (congrArg (fun k ↦ k ≫ schemeHom B a)
        (toScheme_map_comp B X.obj X.property
          (Pi.π A (0 : Fin (p + 1))).left).symm).trans (Category.assoc _ _ _)
  have := hE (i 0)
  rw [hfac]
  infer_instance

/-- **A covering family of the final object of `X_étale` whose members *and all their iterated
fibre products over `X`* are affine over `Y`**, for a separated `Y` and a separated `a`.

The family is the one of
`AlgebraicGeometry.SmallEtale.exists_coversTop_isAffineHom_of_isSeparated` — the affine opens of
`X` — and what is added here is the last conjunct, affineness over `Y` of the *terms* of the Čech
complex, by
`AlgebraicGeometry.SmallEtale.isAffineHom_toBaseHom_piObj_of_isSeparatedHom`.

**Two hypotheses are carried, both separatedness and both named.**  Separatedness of `Y` is what
makes the members affine over `Y` ([Stacks, Tag 01SG] part (4)) and costs nothing, the conclusion
of the étale clause of [Stacks, Tag 071N] being Zariski-local on `Y` (
`AlgebraicGeometry.SmallEtale.isCartesianOnAffines_rightDerived_pushforward_of_forall_affineOpens`)
and an affine open of `Y` being separated.  Separatedness of **`a`** is what makes the terms
affine over `Y`, and it does *not* come for free:  the hypothesis of [Stacks, Tag 071N] is that
`a` be quasi-compact and quasi-separated. -/
public theorem exists_coversTop_isAffineHom_piObj_of_isSeparated_of_isSeparatedHom
    [Y.obj.IsSeparated] [IsSeparated (schemeHom B a)] :
    ∃ E : PreZeroHypercover.{u} (final B X.obj X.property),
      (topology B X.obj X.property).CoversTop E.X ∧
        (∀ j, AlgebraicGeometry.IsAffine ((toScheme B X.obj X.property).obj (E.X j))) ∧
        (∀ j, IsAffineHom (toBaseHom B a (E.X j))) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.I₀),
              HasProduct (fun b ↦ Over.mk (E.f (j b))) := fun q j ↦
            Stacks.Sites.hasProduct_fibreProducts E (fun _ _ _ ↦ inferInstance) q j
          IsAffineHom (toBaseHom B a (∏ᶜ (fun b ↦ Over.mk (E.f (i b)))).left) :=
  have hE := fun j ↦ isAffineHom_toBaseHom B a _
    (isAffine_toScheme_affineOpensHypercoverFinal B X.obj X.property j)
  ⟨affineOpensHypercoverFinal B X.obj X.property,
    coversTop_affineOpensHypercoverFinal B X.obj X.property,
    fun j ↦ isAffine_toScheme_affineOpensHypercoverFinal B X.obj X.property j, hE,
    fun p i ↦ isAffineHom_toBaseHom_piObj_of_isSeparatedHom B a _ hE p i⟩

end Base

end AlgebraicGeometry.SmallEtale

end
