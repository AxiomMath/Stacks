module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomRingModelBuildStageEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnconditionalPullbackData
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedBaseChangeTriangle

/-!
# The bijection of a derived pullback between represented affines intertwines a factorisation

`AlgebraicGeometry.Space.representedAffineDerivedPullbackHomEquiv` moves a homomorphism group
between derived pullbacks of associated modules over an affine representable to a homomorphism
group of complexes of modules,

`Hom_{D(𝒪_{h_{U'}})}(Lg^*(Φ_R M), Lg^*(Φ_R N)) ≃ Hom_{D(R')}(M ⊗^𝐋_R R', N ⊗^𝐋_R R')`,

for arbitrary `M`, `N` in `D(R)`, `R = Γ(U, 𝒪)`.  This file proves that it intertwines the maps
of homomorphism groups attached to a factorisation: the map
`CategoryTheory.PullbackData.factorHom` of `AlgebraicGeometry.Space.canonicalPullbackData` along
`g₂ : U'' ⟶ U'` becomes, on the module side, conjugation by the composition law of derived
extensions of scalars.

Those maps are the transition maps and the maps to the vertex of the system of Stacks 09RI, so
this is what carries that system, at an arbitrary quasi-coherent object rather than at a
structure sheaf, to a system of homomorphism groups of complexes of modules.

The proof is *exact*: the affine base change isomorphisms compose along a triangle with no unit
(`AlgebraicGeometry.Space.representedAffineToposDerivedBaseChange_comp`), and the comparison of
a factorisation of `AlgebraicGeometry.Space.canonicalPullbackData` is built from exactly the two
ingredients that triangle law is stated with — the composition isomorphism of Stacks 0D6D and
the `eqToIso` of `AlgebraicGeometry.Space.representedSpaceMap_comp`.

## Main results

* `CategoryTheory.Functor.conjHom_crossing_eq`: the abstract computation — for two families of
  functors crossed by a compatible triple of comparison isomorphisms, conjugation by the
  composition law on one side is conjugation by the comparison of the factorisation on the
  other.  This is `CategoryTheory.PullbackData.Crossing.homEquiv_factorHom` with no pullback
  pseudofunctor datum on the module side, which is what the affine leaf needs: the derived
  extensions of scalars are indexed by morphisms of *affine* representables, which are not a
  fibration over the base.
* `AlgebraicGeometry.Space.canonicalPullbackData_triangle_inv_app`: the comparison of a
  factorisation of `AlgebraicGeometry.Space.canonicalPullbackData`, inverted, on components.
* `AlgebraicGeometry.Space.representedAffineDerivedBaseChange_canonicalTriangle`: the triangle
  law of the affine base change isomorphisms, read against that comparison.
* `AlgebraicGeometry.Space.representedAffineDerivedPullbackHomEquiv_factorHom`: **the bijection
  intertwines the maps attached to a factorisation.**

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 08H1](https://stacks.math.columbia.edu/tag/08H1)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v₀ v₁ v₂ w₀ w₁ w₂ s₀ s₁ s₂ t₀ t₁ t₂ u

namespace CategoryTheory.Functor

section Crossing

variable {Dm₀ : Type s₀} {Dm₁ : Type s₁} {Dm₂ : Type s₂} [Category.{v₀} Dm₀]
  [Category.{v₁} Dm₁] [Category.{v₂} Dm₂]
  {D₀ : Type t₀} {D₁ : Type t₁} {D₂ : Type t₂} [Category.{w₀} D₀] [Category.{w₁} D₁]
  [Category.{w₂} D₂] {E₀ : Dm₀ ⥤ D₀} {E₁ : Dm₁ ⥤ D₁} {E₂ : Dm₂ ⥤ D₂}
  {q₁ : Dm₀ ⥤ Dm₁} {q₂ : Dm₁ ⥤ Dm₂} {q : Dm₀ ⥤ Dm₂}
  {p₁ : D₀ ⥤ D₁} {p₂ : D₁ ⥤ D₂} {p : D₀ ⥤ D₂}
  (β₁ : E₀ ⋙ p₁ ≅ q₁ ⋙ E₁) (β₂ : E₁ ⋙ p₂ ≅ q₂ ⋙ E₂) (β : E₀ ⋙ p ≅ q ⋙ E₂)
  (T : q₁ ⋙ q₂ ≅ q) (tri : p ≅ p₁ ⋙ p₂)

/-- **Conjugation by the comparison of a factorisation is conjugation by the composition law,
across a crossing.**  Let `E₀`, `E₁`, `E₂` cross one chain of functors `q₁`, `q₂`, `q` into
another `p₁`, `p₂`, `p` through comparison isomorphisms `β₁`, `β₂`, `β`, compatibly with a
composition law `T : q₁ ⋙ q₂ ≅ q` and a comparison `tri : p ≅ p₁ ⋙ p₂` (the hypothesis `htri`).
If `α` corresponds to `φ` under `β₁` at `M` and at `N`, then the conjugate of `α` by `T`
corresponds to the conjugate of `φ` by `tri` under `β`.

This is `CategoryTheory.PullbackData.Crossing.homEquiv_factorHom` with the pullback
pseudofunctor datum on neither side: only the three comparison isomorphisms and the two
composition laws at hand are used. -/
theorem conjHom_crossing_eq
    (htri : ∀ X : Dm₀, p₂.map (β₁.hom.app X) ≫ β₂.hom.app (q₁.obj X) ≫
      E₂.map (T.hom.app X) = tri.inv.app (E₀.obj X) ≫ β.hom.app X)
    {M N : Dm₀} (φ : p₁.obj (E₀.obj M) ⟶ p₁.obj (E₀.obj N)) (α : q₁.obj M ⟶ q₁.obj N)
    (hα : φ ≫ β₁.hom.app N = β₁.hom.app M ≫ E₁.map α) :
    β.hom.app M ≫ E₂.map (conjHom T.symm α) = conjHom tri φ ≫ β.hom.app N := by
  have hβ : tri.hom.app (E₀.obj M) ≫ p₂.map (β₁.hom.app M) ≫ β₂.hom.app (q₁.obj M) ≫
      E₂.map (T.hom.app M) = β.hom.app M := by
    rw [htri M, Iso.hom_inv_id_app_assoc]
  have hM : β.hom.app M ≫ E₂.map (T.inv.app M) =
      tri.hom.app (E₀.obj M) ≫ p₂.map (β₁.hom.app M) ≫ β₂.hom.app (q₁.obj M) := by
    rw [← hβ]
    simp only [Category.assoc]
    rw [← E₂.map_comp, Iso.hom_inv_id_app]
    simp
  have hnat := β₂.hom.naturality α
  simp only [Functor.comp_map] at hnat
  simp only [conjHom, Iso.symm_hom, Iso.symm_inv, Functor.map_comp, Category.assoc]
  rw [← htri N, ← Category.assoc (p₂.map φ), ← p₂.map_comp, hα, p₂.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hnat, reassoc_of% hM]

end Crossing

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

/- The filtered colimits used to form the étale sheafification, through Mathlib's instance, so that
the categories of `𝒪`-modules below are spelled as in the files of the derived pullback. -/
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance] additive_extendScalars_representedAffineRingHom
  additive_pullbackModules_representedSpaceMap

attribute [local instance 6000] preadditive_smallEtaleModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparison of a factorisation, on components -/

section Triangle

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **The comparison of a presented factorisation of
`AlgebraicGeometry.Space.canonicalPullbackData`, inverted, on components**: it is the
composition isomorphism of Stacks 0D6D followed by the identification of the inverse images
along the two equal morphisms.  This is the shape in which the triangle law of the affine base
change isomorphisms is stated.

Checked at the composite itself, where the identification is the identity: there the
composition comparison of the datum is the inverse of
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso`
(`AlgebraicGeometry.Space.canonicalPullbackData_compIso_eq_smallEtale` and
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData_compIso_eq`). -/
theorem canonicalPullbackData_triangle_inv_app {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z}
    (h : f ≫ g = k) (A : derivedModules B S hS Z) :
    ((canonicalPullbackData B S hS).triangle h).inv.app A =
      (smallEtaleDerivedModulePullbackCompIso B S hS f g).hom.app A ≫
        (eqToIso (congrArg (fun m : X ⟶ Z ↦ smallEtaleDerivedModulePullback B S hS m)
          h.symm)).inv.app A := by
  subst h
  rw [PullbackData.triangle_rfl, canonicalPullbackData_compIso_eq_smallEtale,
    smallEtaleDerivedPullbackData_compIso_eq]
  exact (Category.comp_id _).symm

end Triangle

/-! ### The triangle law against that comparison -/

section TriangleLaw

variable {U U' U'' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')] (g : U' ⟶ U) (g₂ : U'' ⟶ U')

/-- **The affine base change isomorphisms compose along a triangle, read against the comparison
of the factorisation of `AlgebraicGeometry.Space.canonicalPullbackData`.**  This is
`AlgebraicGeometry.Space.representedAffineToposDerivedBaseChange_comp` with its two trailing
factors folded into `CategoryTheory.PullbackData.triangle`; no unit intervenes. -/
theorem representedAffineDerivedBaseChange_canonicalTriangle
    (N : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) :
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₂)).map
          ((representedAffineDerivedBaseChangeIso B S hS g).hom.app N) ≫
        (representedAffineDerivedBaseChangeIso B S hS g₂).hom.app
          ((representedAffineDerivedExtension B S hS g).functor.obj N) ≫
        (representedAffineDerivedAssociated B S hS U'').map
          ((RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
              (representedAffineCommRingCatHom B S hS g).hom
              (representedAffineCommRingCatHom B S hS g₂).hom
              (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
              (representedAffineRingHom_comp B S hS g₂ g).symm).hom.app N) =
      ((canonicalPullbackData B S hS).triangle
            (representedSpaceMap_comp B S hS g₂ g)).inv.app
          ((representedAffineDerivedAssociated B S hS U).obj N) ≫
        (representedAffineDerivedBaseChangeIso B S hS (g₂ ≫ g)).hom.app N := by
  rw [canonicalPullbackData_triangle_inv_app]
  exact (representedAffineToposDerivedBaseChange_comp B S hS g g₂ N).trans
    (Category.assoc _ _ _).symm

end TriangleLaw

/-! ### The bijection intertwines a factorisation -/

section HomEquiv

variable {U U' U'' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')]

/-- **`AlgebraicGeometry.Space.representedAffineDerivedPullbackHomEquiv` is characterised by the
affine base change isomorphism**: the image of `φ` under the bijection is the unique morphism of
`D(R')` whose associated module makes the square of `Lg^*(Φ_R M) ≅ Φ_{R'}(M ⊗^𝐋_R R')` with `φ`
commute. -/
theorem representedAffineDerivedBaseChangeIso_hom_app_comp_map_pullbackHomEquiv (g : U' ⟶ U)
    (M N : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
    (φ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
          ((representedAffineDerivedAssociated B S hS U).obj M) ⟶
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
          ((representedAffineDerivedAssociated B S hS U).obj N)) :
    (representedAffineDerivedBaseChangeIso B S hS g).hom.app M ≫
        (representedAffineDerivedAssociated B S hS U').map
          (representedAffineDerivedPullbackHomEquiv B S hS g M N φ) =
      φ ≫ (representedAffineDerivedBaseChangeIso B S hS g).hom.app N := by
  have key : (representedAffineDerivedAssociated B S hS U').map
        (representedAffineDerivedPullbackHomEquiv B S hS g M N φ) =
      (representedAffineDerivedBaseChangeIso B S hS g).inv.app M ≫ φ ≫
        (representedAffineDerivedBaseChangeIso B S hS g).hom.app N :=
    (representedAffineDerivedAssociatedFullyFaithful B S hS U').map_preimage _
  rw [key]
  exact Iso.hom_inv_id_app_assoc _ _ _

/-- **The bijection of Stacks 08H1 over an affine representable intertwines the maps attached to
a factorisation.**  For `g : U' ⟶ U` and `g₂ : U'' ⟶ U'` of affine representables and arbitrary
`M`, `N` in `D(R)`, `R = Γ(U, 𝒪)`, the map of homomorphism groups attached to the factorisation
`g₂ ≫ g`, followed by
`AlgebraicGeometry.Space.representedAffineDerivedPullbackHomEquiv` at `g₂ ≫ g`, is the bijection
at `g` followed by conjugation by the composition law of derived extensions of scalars.

These are the transition maps and the maps to the vertex of the system of Stacks 09RI, so this
is what reads that system — at an arbitrary object of `D(R)`, with no flatness, boundedness or
perfectness hypothesis — as a system of homomorphism groups of complexes of modules. -/
theorem representedAffineDerivedPullbackHomEquiv_factorHom (g : U' ⟶ U) (g₂ : U'' ⟶ U')
    (M N : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
    (φ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
          ((representedAffineDerivedAssociated B S hS U).obj M) ⟶
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
          ((representedAffineDerivedAssociated B S hS U).obj N)) :
    representedAffineDerivedPullbackHomEquiv B S hS (g₂ ≫ g) M N
        ((canonicalPullbackData B S hS).factorHom
          (representedSpaceMap_comp B S hS g₂ g) φ) =
      Functor.conjHom (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
            (representedAffineCommRingCatHom B S hS g).hom
            (representedAffineCommRingCatHom B S hS g₂).hom
            (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
            (representedAffineRingHom_comp B S hS g₂ g).symm).symm
        (representedAffineDerivedPullbackHomEquiv B S hS g M N φ) := by
  apply (representedAffineDerivedAssociatedFullyFaithful B S hS U'').map_injective
  have h₁ := representedAffineDerivedBaseChangeIso_hom_app_comp_map_pullbackHomEquiv B S hS
    (g₂ ≫ g) M N ((canonicalPullbackData B S hS).factorHom
      (representedSpaceMap_comp B S hS g₂ g) φ)
  have h₂ := Functor.conjHom_crossing_eq _ _ _ _ _
    (representedAffineDerivedBaseChange_canonicalTriangle B S hS g g₂) φ _
    (representedAffineDerivedBaseChangeIso_hom_app_comp_map_pullbackHomEquiv B S hS g M N
      φ).symm
  exact (Iso.cancel_iso_hom_left
    ((representedAffineDerivedBaseChangeIso B S hS (g₂ ≫ g)).app M) _ _).1
    (h₁.trans h₂.symm)

end HomEquiv

end AlgebraicGeometry.Space

end
