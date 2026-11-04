module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDifferentialsInvertible
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDifferentialsIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
import StacksCore.Tactic.StacksAttribute

/-!
# A `Y_étale`-derivation is its restriction to the small Zariski site

Let `f : X ⟶ Y` be a morphism of schemes of a big étale site and let `𝓕` be a sheaf of
`𝒪_{X_étale}`-modules.  Restricting a `Y_étale`-derivation of `𝒪_{X_étale}` with values in `𝓕` to
the small Zariski site of `X` gives an ordinary `Y`-derivation of `𝒪_X` with values in the
restriction `ε_*𝓕` (`AlgebraicGeometry.SmallEtale.zariskiRestriction`).  **That restriction is a
bijection**, and this file proves it.

Both halves are the invertibility clause of Stacks 04CS, already in the tree, read as one
statement:

* injectivity is `AlgebraicGeometry.SmallEtale.eq_of_zariskiRestrictionData_eq` — a derivation
  annihilating the functions pulled back from `Y` is determined by its Zariski restriction;
* surjectivity is the universal property of `d^a`,
  `AlgebraicGeometry.SmallEtale.existsUnique_postcomp_etaleAssociatedDerivation`, together with
  the adjunction of Stacks 03DU (4) and the universal property of `Ω_{X/Y}`.

What makes the two fit together is
`AlgebraicGeometry.SmallEtale.differentialsComparison_adjunct`: the adjunct of the comparison map
`c'' : (Ω_{X/Y})^a ⟶ 𝓕` of a derivation carries `d_{X/Y}` to that derivation's Zariski
restriction.  So the Zariski restriction *is* the composite of three bijections — the comparison
map, the adjunction, and the universal property of `Ω_{X/Y}` — and no new mathematics is needed.

## Main definitions

* `AlgebraicGeometry.SmallEtale.etaleZariskiRestriction`: the Zariski restriction of a
  `Y_étale`-derivation, with the vanishing hypothesis of
  `AlgebraicGeometry.SmallEtale.zariskiRestriction` discharged from the derivation's own
  vanishing condition.

## Main results

* `AlgebraicGeometry.SmallEtale.bijective_etaleZariskiRestriction`: **a `Y_étale`-derivation of
  `𝒪_{X_étale}` is the same thing as a `Y`-derivation of `𝒪_X` with values in `ε_*𝓕`.**
* `AlgebraicGeometry.SmallEtale.etaleZariskiRestrictionEquiv`: the same as an `Equiv`.
* `AlgebraicGeometry.SmallEtale.bijective_differentialsComparison_ofEtaleDerivation`: the
  intermediate bijection, from `Y_étale`-derivations onto the morphisms `(Ω_{X/Y})^a ⟶ 𝓕`.

## Implementation notes

`AlgebraicGeometry.SmallEtale.differentialsComparison` and
`AlgebraicGeometry.SmallEtale.zariskiRestriction` take the derivation *and* the proof that it
annihilates `AlgebraicGeometry.SmallEtale.pullbackSection`, and the type of that proof mentions
the derivation.  So an equality of derivations cannot be rewritten under them.
`AlgebraicGeometry.SmallEtale.differentialsComparison_congr` and
`AlgebraicGeometry.SmallEtale.zariskiRestriction_congr` substitute the equality instead, after
which the two proofs are proofs of one proposition and definitional proof irrelevance closes the
goal.

The two spellings of "the derivation `d^a` postcomposed with `g`" —
`AlgebraicGeometry.SmallEtale.ofEtaleDerivation` of
`(etaleAssociatedDerivation).postcomp g.val`, and `(associatedDerivation).postcomp g.val` — have
the same underlying additive map, because `etaleAssociatedDerivation` is `associatedDerivation`
with a vanishing condition added and `ofEtaleDerivation` forgets one.  They are therefore equal
by `PresheafOfModules.Derivation.ext` and `rfl` on values, which is
`AlgebraicGeometry.SmallEtale.ofEtaleDerivation_postcomp_etaleAssociatedDerivation`.

**A sections description of `(Ω_{X/Y})^a` is available**, and is the thing to reach for before
rebuilding one: `AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheaf`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleAssociatedSections.lean`) is
Stacks 070S (2) for an arbitrary big étale site and a quasi-coherent `𝓕` — it identifies `𝓕^a`
with the sections sheaf `(g : T → X) ↦ Γ(T, g^*𝓕)` of Stacks 03DS — and over an étale
`h : T ⟶ X` the derivation `d^a` is the universal derivation `d_{T/Y}` read through the
isomorphism of Stacks 04BX, which is
`AlgebraicGeometry.SmallEtale.associatedSectionsDerivation_d` together with
`AlgebraicGeometry.etaleAssociatedDerivation` and
`AlgebraicGeometry.differentialSectionsComparison_etaleAssociatedDerivation` in
`StacksFrontier/AlgebraicGeometry/Morphisms/Differentials/EtaleSectionsComparison.lean`.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), the associated module
  and its adjunction.
* [Stacks Project, Tag 04BN](https://stacks.math.columbia.edu/tag/04BN), derivations on a ringed
  topos.
* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM), the universal property
  of `Ω_{X/Y}`.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallEtale

/-! ### Substituting an equality of derivations -/

section Congr

variable (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (f : X ⟶ Y)
  {F : SheafOfModules.{u} (structureSheaf B X hX)}
  {R : (SmallEtale B X hX)ᵒᵖ ⥤ CommRingCat.{u}}
  {ψ : R ⟶ (commRingStructureSheaf B X hX).obj}

/-- The Zariski restriction of Stacks 04CS depends on the derivation only through the derivation.
-/
public theorem zariskiRestriction_congr
    {D₁ D₂ : PresheafOfModules.Derivation'
      (R := (commRingStructureSheaf B X hX).obj) F.val ψ} (h : D₁ = D₂)
    (hD₁ : ∀ (W : Y.Opens) (b : Γ(Y, W)), D₁.d (pullbackSection B hX f W b) = 0)
    (hD₂ : ∀ (W : Y.Opens) (b : Γ(Y, W)), D₂.d (pullbackSection B hX f W b) = 0) :
    zariskiRestriction B hX f D₁ hD₁ = zariskiRestriction B hX f D₂ hD₂ := by
  subst h
  rfl

end Congr

/-! ### The Zariski restriction of a `Y_étale`-derivation -/

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  (F : SheafOfModules.{u} (structureSheaf B X.obj X.property))

/-- A `Y_étale`-derivation annihilates every function pulled back from an open of `Y`: it
annihilates the image of `f_small^♯`, and
`AlgebraicGeometry.SmallEtale.d_pullbackSection_eq_zero` puts those functions there. -/
public theorem ofEtaleDerivation_pullbackSection_eq_zero (D : EtaleDerivation B f F)
    (W : Y.obj.Opens) (b : Γ(Y.obj, W)) :
    (ofEtaleDerivation B f D).d (pullbackSection B X.property (schemeHom B f) W b) = 0 :=
  d_pullbackSection_eq_zero B f D (fun _ s ↦ PresheafOfModules.Derivation'.d_app D s) W b

/-- **The restriction of a `Y_étale`-derivation of `𝒪_{X_étale}` to the small Zariski site of
`X`**: an ordinary `Y`-derivation of `𝒪_X` with values in the restriction `ε_*𝓕`.  Over an open
`W` of `X` it is the value of the derivation at `W` read as an object of the small étale site. -/
public noncomputable def etaleZariskiRestriction (D : EtaleDerivation B f F) :
    SheafOfModules.SheafDerivation (inverseImageStructureMap (schemeHom B f))
      ((restrictModule B X.obj X.property).obj F) :=
  zariskiRestriction B X.property (schemeHom B f) (ofEtaleDerivation B f D)
    (ofEtaleDerivation_pullbackSection_eq_zero B f F D)

/-- The two spellings of `d^a` postcomposed with a morphism agree: `d^a` as a
`Y_étale`-derivation and `d^a` as a derivation over the constant presheaf `ℤ` have the same
values, and so do their postcompositions. -/
public theorem ofEtaleDerivation_postcomp_etaleAssociatedDerivation
    (g : associatedRelativeDifferentials B X.property (schemeHom B f) ⟶ F) :
    ofEtaleDerivation B f ((etaleAssociatedDerivation B f).postcomp g.val) =
      (associatedDerivation B X.property (schemeHom B f)).postcomp g.val :=
  PresheafOfModules.Derivation.ext (funext fun _ ↦ AddMonoidHom.ext fun _ ↦ rfl)

/-- **The comparison map of Stacks 04CS, read as a map on `Y_étale`-derivations, is a
bijection.**  A `Y_étale`-derivation of `𝒪_{X_étale}` with values in `𝓕` is the same thing as a
morphism `(Ω_{X/Y})^a ⟶ 𝓕`.

`AlgebraicGeometry.SmallEtale.existsUnique_postcomp_etaleAssociatedDerivation` already makes
`g ↦ d^a ∘ g` a bijection in the other direction, so all that is needed is that the comparison
map is a left inverse of it, which is
`AlgebraicGeometry.SmallEtale.differentialsComparison_postcomp_associatedDerivation`: the
comparison map of `d^a` postcomposed with `g` is `g` itself.  A left inverse of a bijection is
its inverse, hence a bijection. -/
public theorem bijective_differentialsComparison_ofEtaleDerivation :
    Function.Bijective (fun D : EtaleDerivation B f F ↦
      differentialsComparison B X.property (schemeHom B f) (ofEtaleDerivation B f D)
        (ofEtaleDerivation_pullbackSection_eq_zero B f F D)) := by
  have hback : Function.Bijective
      (fun g : associatedRelativeDifferentials B X.property (schemeHom B f) ⟶ F ↦
        (etaleAssociatedDerivation B f).postcomp g.val) :=
    (Function.bijective_iff_existsUnique _).2
      (existsUnique_postcomp_etaleAssociatedDerivation B f F)
  have key : ∀ g : associatedRelativeDifferentials B X.property (schemeHom B f) ⟶ F,
      differentialsComparison B X.property (schemeHom B f)
          (ofEtaleDerivation B f ((etaleAssociatedDerivation B f).postcomp g.val))
          (ofEtaleDerivation_pullbackSection_eq_zero B f F _) = g := by
    intro g
    refine Eq.trans (differentialsComparison_congr B X.obj X.property (schemeHom B f)
      (ofEtaleDerivation_postcomp_etaleAssociatedDerivation B f F g) _
      (postcomp_pullbackSection_eq_zero B X.property (schemeHom B f)
        (associatedDerivation B X.property (schemeHom B f))
        (associatedDerivation_pullbackSection_eq_zero B X.property (schemeHom B f)) g)) ?_
    exact differentialsComparison_postcomp_associatedDerivation B X.property (schemeHom B f) g
  refine ⟨fun D₁ D₂ h ↦ ?_, fun g ↦ ⟨(etaleAssociatedDerivation B f).postcomp g.val, key g⟩⟩
  obtain ⟨g₁, rfl⟩ := hback.surjective D₁
  obtain ⟨g₂, rfl⟩ := hback.surjective D₂
  exact congrArg (fun g ↦ (etaleAssociatedDerivation B f).postcomp
    (SheafOfModules.Hom.val g)) ((key g₁).symm.trans (h.trans (key g₂)))

/-- Postcomposition with the universal relative derivation is a bijection from the morphisms out
of `Ω_{X/Y}` onto the `Y`-derivations of `𝒪_X`: the universal property of Stacks 08RM read as a
bijection. -/
public theorem bijective_universalRelativeDerivation_postcomp
    (G : X.obj.Modules) :
    Function.Bijective (fun α : Scheme.Hom.relativeDifferentials (schemeHom B f) ⟶ G ↦
      (Scheme.Hom.universalRelativeDerivation (schemeHom B f)).postcomp α.val) :=
  (Function.bijective_iff_existsUnique _).2
    (Scheme.Hom.existsUnique_hom_relativeDifferentials (schemeHom B f) G)

/-- **A `Y_étale`-derivation of `𝒪_{X_étale}` is its restriction to the small Zariski site of
`X`.**  Restriction is a bijection onto the `Y`-derivations of `𝒪_X` with values in `ε_*𝓕`.

By `AlgebraicGeometry.SmallEtale.differentialsComparison_adjunct` the restriction is the
composite of three bijections: the comparison map of Stacks 04CS
(`AlgebraicGeometry.SmallEtale.bijective_differentialsComparison_ofEtaleDerivation`), the
adjunction of Stacks 03DU (4), and the universal property of `Ω_{X/Y}`. -/
public theorem bijective_etaleZariskiRestriction :
    Function.Bijective (etaleZariskiRestriction B f F) := by
  have hcomp : etaleZariskiRestriction B f F =
      (fun α : Scheme.Hom.relativeDifferentials (schemeHom B f) ⟶
            (restrictModule B X.obj X.property).obj F ↦
          (Scheme.Hom.universalRelativeDerivation (schemeHom B f)).postcomp α.val) ∘
        ((associatedModuleAdjunction B X.obj X.property).homEquiv
          (Scheme.Hom.relativeDifferentials (schemeHom B f)) F) ∘
        fun D : EtaleDerivation B f F ↦
          differentialsComparison B X.property (schemeHom B f) (ofEtaleDerivation B f D)
            (ofEtaleDerivation_pullbackSection_eq_zero B f F D) :=
    funext fun D ↦ (differentialsComparison_adjunct B X.property (schemeHom B f)
      (ofEtaleDerivation B f D) (ofEtaleDerivation_pullbackSection_eq_zero B f F D)).symm
  rw [hcomp]
  exact (bijective_universalRelativeDerivation_postcomp B f _).comp
    (((associatedModuleAdjunction B X.obj X.property).homEquiv
        (Scheme.Hom.relativeDifferentials (schemeHom B f)) F).bijective.comp
      (bijective_differentialsComparison_ofEtaleDerivation B f F))

/-- **A `Y_étale`-derivation of `𝒪_{X_étale}` is its restriction to the small Zariski site of
`X`**, as an `Equiv`. -/
public noncomputable def etaleZariskiRestrictionEquiv :
    EtaleDerivation B f F ≃
      SheafOfModules.SheafDerivation (inverseImageStructureMap (schemeHom B f))
        ((restrictModule B X.obj X.property).obj F) :=
  Equiv.ofBijective _ (bijective_etaleZariskiRestriction B f F)

end AlgebraicGeometry.SmallEtale

end
