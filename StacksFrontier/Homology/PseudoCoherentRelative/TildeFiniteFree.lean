module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeRetract
public import StacksCore.Tactic.StacksAttribute

/-!
# The finite free `𝒪_{Spec R}`-module is `(R^n)^~`

`Stacks.StrictlyPerfect.finiteFree X n` is the `n`-fold biproduct of the structure module of a
ringed space `X`; it is the ambient module in the definition of
`Stacks.StrictlyPerfect.IsDirectSummandOfFiniteFree`, hence in the definition of a strictly
perfect complex. On `X = Spec R` it is the sheaf associated to the finite free module
`Fin n → R`, and this file proves that.

Together with `StacksFrontier/Homology/PseudoCoherentRelative/TildeRetract.lean` this puts the
affine case of Stacks 0BCI into the exact shape Stacks 08E7 consumes it: a term of a strictly
perfect complex on `Spec R` is `N^~` for an `R`-module `N` that is finite free on each member of
a finite covering of `Spec R` by standard opens.

## Main results

* `Stacks.AffineTilde.hasFiniteBiproducts_modules`: `X.Modules` has finite biproducts. Mathlib
  has the finite products and the preadditive structure but not this consequence.
* `Stacks.AffineTilde.tildeFinPi`: `(R^n)^~` is the `n`-fold biproduct of `R^~`.
* `Stacks.AffineTilde.finiteFreeIsoTilde`: `Stacks.StrictlyPerfect.finiteFree` on `Spec R` is
  `(R^n)^~`.
* `Stacks.AffineTilde.exists_finiteProjective_tilde_of_retract_finiteFree`: a direct summand of
  `Stacks.StrictlyPerfect.finiteFree` on `Spec R` is `N^~` for `N` finite projective.
* `Stacks.AffineTilde.exists_finite_span_free_away_of_isDirectSummandOfFiniteFree`: the same,
  with the conclusion that `N` becomes finite free over `R_g` for the members `g` of a finite
  family generating the unit ideal.

## Implementation notes

Two spelling obstructions, both resolved at term level with no transparency flag.

First, `Stacks.StrictlyPerfect.finiteFree` is a biproduct taken in
`Stacks.StrictlyPerfect.OXMod (Spec R).toRingedSpace` using the `HasFiniteBiproducts` instance
on `Stacks.StrictlyPerfect.OXMod`, while the chain below builds a biproduct in
`AlgebraicGeometry.Scheme.Modules`. No transport lemma is needed for that:
`CategoryTheory.Limits.HasBiproduct` is a `Prop`, so the two instances are definitionally equal
by proof irrelevance, and the two categories are definitionally equal as well
(`Stacks.DerivedQCoh.oxMod_eq_sheafOfModules` is `rfl`). The two biproducts are therefore the
same term up to default-transparency defeq, which is what a type ascription checks — so
`finiteFreeIsoTilde` is literally `tildeFinPi` composed with nothing. `biproduct.uniqueUpToIso`
is *not* needed.

Second, the family being summed must be spelled `(tilde.functor R).obj (ModuleCat.of R R)` and
not `AlgebraicGeometry.SheafOfModules.unit (Spec R).ringCatSheaf`, even though
`AlgebraicGeometry.tildeSelf` identifies the two by `Iso.refl`. The reason is a failure of
*instance synthesis*, not of defeq: the type of the second spelling is
`SheafOfModules (Spec R).ringCatSheaf`, and `AlgebraicGeometry.Scheme.Modules` is a
semireducible `def` for that type, so when
`CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct` tries to unify its family argument
`f : J → (Spec R).Modules` with the given family it is comparing types at reducible
transparency and fails. With the first spelling the family's type is literally `(Spec R).Modules`
and synthesis succeeds.

## References

* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
* [Stacks Project, Tag 0BCI](https://stacks.math.columbia.edu/tag/0BCI)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AffineTilde

/-- The category of `𝒪_X`-modules on a scheme has finite biproducts: it is preadditive and has
finite products. Mathlib records both of those for `AlgebraicGeometry.Scheme.Modules` but not
this consequence, and without it a biproduct of `𝒪_X`-modules does not even elaborate. -/
instance hasFiniteBiproducts_modules (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable (R : CommRingCat.{u}) (n : ℕ)

/-- The sheaf associated to the finite free module `Fin n → R` is the `n`-fold biproduct of the
sheaf associated to `R`, because `M ↦ M^~` is additive and `Fin n → R` is the `n`-fold biproduct
of `R` in `ModuleCat R`. -/
def tildeFinPi : (tilde.functor R).obj (ModuleCat.of R (Fin n → R)) ≅
    ⨁ fun _ : Fin n => (tilde.functor R).obj (ModuleCat.of R R) :=
  (tilde.functor R).mapIso (ModuleCat.biproductIsoPi fun _ : Fin n => ModuleCat.of R R).symm ≪≫
    (tilde.functor R).mapBiproduct _

/-- **The finite free module of a strictly perfect complex, on an affine scheme.**
`Stacks.StrictlyPerfect.finiteFree` of `Spec R` is the sheaf associated to `Fin n → R`.

The left-hand side is a biproduct of copies of
`Stacks.StrictlyPerfect.structureModule (Spec R).toRingedSpace`, which is
`AlgebraicGeometry.SheafOfModules.unit (Spec R).ringCatSheaf`, which is `(R)^~` on the nose
(`AlgebraicGeometry.tildeSelf` is `Iso.refl`); the two `CategoryTheory.Limits.HasBiproduct`
instances involved are proofs of a proposition, hence definitionally equal. So this is
`Stacks.AffineTilde.tildeFinPi` read in the other spelling. -/
def finiteFreeIsoTilde : StrictlyPerfect.finiteFree.{u} (Spec R).toRingedSpace n ≅
    (tilde.functor R).obj (ModuleCat.of R (Fin n → R)) :=
  (tildeFinPi R n).symm

variable {R n}

/-- **The affine case of Stacks 0BCI, for `Stacks.StrictlyPerfect.finiteFree`.** A direct summand
of the finite free module `𝒪_{Spec R}^{⊕ n}` is the sheaf `N^~` associated to a finite projective
`R`-module `N`. -/
theorem exists_finiteProjective_tilde_of_retract_finiteFree
    {F : StrictlyPerfect.OXMod.{u, u} (Spec R).toRingedSpace}
    (h : Retract F (StrictlyPerfect.finiteFree.{u} (Spec R).toRingedSpace n)) :
    ∃ N : ModuleCat.{u} R, Module.Finite R N ∧ Module.Projective R N ∧
      Nonempty ((tilde.functor R).obj N ≅ (F : (Spec R).Modules)) :=
  exists_finiteProjective_tilde_of_retract_oxMod
    (M := ModuleCat.of R (Fin n → R)) (finiteFreeIsoTilde R n).symm h

/-- **The affine case of Stacks 0BCI, in the form Stacks 08E7 uses it.** A direct summand of a
finite free `𝒪_{Spec R}`-module — i.e. a term of a strictly perfect complex on `Spec R`, by
`Stacks.StrictlyPerfect.IsDirectSummandOfFiniteFree` — is the sheaf `N^~` associated to an
`R`-module `N` which becomes finite free over `R_g` for each member `g` of a finite family
generating the unit ideal.

This is the statement that, after refining a covering of `Spec R` by standard opens, the terms
of a strictly perfect complex become finite free. -/
theorem exists_finite_span_free_away_of_isDirectSummandOfFiniteFree
    {F : StrictlyPerfect.OXMod.{u, u} (Spec R).toRingedSpace}
    (h : StrictlyPerfect.IsDirectSummandOfFiniteFree F) :
    ∃ N : ModuleCat.{u} R, Nonempty ((tilde.functor R).obj N ≅ (F : (Spec R).Modules)) ∧
      ∃ s : Finset R, Ideal.span (s : Set R) = ⊤ ∧
        ∀ g ∈ s, Module.Free (Localization.Away g) (LocalizedModule.Away g N) ∧
          Module.Finite (Localization.Away g) (LocalizedModule.Away g N) := by
  obtain ⟨m, ⟨ρ⟩⟩ := (StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract F).mp h
  obtain ⟨N, hfin, hproj, he⟩ := exists_finiteProjective_tilde_of_retract_finiteFree ρ
  have hFP : Module.Finite R N ∧ Module.Projective R N := ⟨hfin, hproj⟩
  obtain ⟨t, ht, hfree⟩ := ((Module.finite_projective_tfae R N).out 2 7).mp hFP
  obtain ⟨s, hs, hspan⟩ := (Ideal.span_eq_top_iff_finite t).mp ht
  exact ⟨N, he, s, hspan, fun g hg => hfree g (hs hg)⟩

/-! ### Strictly perfect complexes on `Spec R`

The reason `Stacks.AffineTilde.finiteFreeIsoTilde` is wanted: it identifies the terms of the
complex `\widetilde{E^•}` associated to a bounded complex `E^•` of finite free `R`-modules as
finite free `𝒪_{Spec R}`-modules, which is what makes that complex strictly perfect in the sense
of Stacks 08C4. -/

/-- A retract of `𝒪_{Spec R}`-modules in the `AlgebraicGeometry.Scheme.Modules` spelling, where
Mathlib's `tilde` API lives, is a retract in the `Stacks.StrictlyPerfect.OXMod` spelling, where
strict perfection is stated. This is the converse of `Stacks.AffineTilde.retractModules` and
type-checks for the same reason: the two `Hom` types and the two compositions are definitionally
equal, and a structure instance is elaborated at default transparency. -/
def retractOxMod {F H : (Spec R).Modules} (h : Retract F H) :
    Retract (F : StrictlyPerfect.OXMod.{u, u} (Spec R).toRingedSpace)
      (H : StrictlyPerfect.OXMod.{u, u} (Spec R).toRingedSpace) :=
  ⟨h.i, h.r, h.retract⟩

/-- A finite free `R`-module has a basis indexed by a finite type, hence is isomorphic to
`Fin n → R` for `n` the cardinality of that index type; this is the induced isomorphism of
associated sheaves. -/
def tildeIsoFinPi (N : ModuleCat.{u} R) [Module.Finite R N] [Module.Free R N] :
    (tilde.functor R).obj N ≅ (tilde.functor R).obj
      (ModuleCat.of R (Fin (Fintype.card (Module.Free.ChooseBasisIndex R N)) → R)) :=
  (tilde.functor R).mapIso ((Module.Free.chooseBasis R N).equivFun.trans
    (LinearEquiv.funCongrLeft R R
      (Fintype.equivFin (Module.Free.ChooseBasisIndex R N)).symm)).toModuleIso

/-- The sheaf associated to a finite free `R`-module is a direct summand of a finite free
`𝒪_{Spec R}`-module — in fact it is finite free, so the retract is an isomorphism. -/
theorem isDirectSummandOfFiniteFree_tilde (N : ModuleCat.{u} R) [Module.Finite R N]
    [Module.Free R N] :
    StrictlyPerfect.IsDirectSummandOfFiniteFree
      (X := (Spec R).toRingedSpace) ((tilde.functor R).obj N) :=
  (StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract _).mpr
    ⟨Fintype.card (Module.Free.ChooseBasisIndex R N),
      ⟨retractOxMod (Retract.ofIso (tildeIsoFinPi N ≪≫
        (finiteFreeIsoTilde R (Fintype.card (Module.Free.ChooseBasisIndex R N))).symm))⟩⟩

/-- **Stacks 08C4 on an affine scheme.** The complex of `𝒪_{Spec R}`-modules associated to a
bounded complex of finite free `R`-modules is strictly perfect.

This is the ingredient of Stacks 08E7 which says that a bounded complex of finite free modules —
the witness of `m`-pseudo-coherence at the level of modules, Stacks 064Q (1) — produces a
strictly perfect approximation at the level of sheaves. -/
theorem isStrictlyPerfect_tildeComplex (E : CochainComplex (ModuleCat.{u} R) ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hff : ∀ i : ℤ, Module.Finite R (E.X i) ∧ Module.Free R (E.X i)) :
    StrictlyPerfect.IsStrictlyPerfect (X := (Spec R).toRingedSpace)
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) where
  bounded := hbdd.subset fun i hi => by
    simp only [Set.mem_ofPred_eq] at hi ⊢
    exact fun hz => hi ((tilde.functor R).map_isZero hz)
  directSummand i :=
    have := (hff i).1
    have := (hff i).2
    isDirectSummandOfFiniteFree_tilde (E.X i)

end Stacks.AffineTilde

end
