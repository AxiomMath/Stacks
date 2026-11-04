module

public import StacksFrontier.AlgebraicGeometry.Perfect.BaseAlternatingCechModuleTransport
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsUniversalModelData
public import StacksFrontier.Homology.ExtendScalars.Flat

/-!
# The cocycle identity for the `ℤ`-indexed Čech base-change isomorphism

Let `φ : A →+* A'` and `ψ : A' →+* A''` be ring maps, let `f : X ⟶ Spec A` be separated, and let
`IsPullback g f' f (Spec φ)` and `IsPullback g' f'' f' (Spec ψ)` exhibit `X'` as the base change
of `X` and `X''` as the base change of `X'`. For a quasi-coherent `𝒪_X`-module `F` and a finite
family `U` of affine opens covering `X`,
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatGlobalSectionsBaseChange.lean` gives a
base-change isomorphism of the `ℤ`-indexed `A`-linear alternating Čech models for each of `φ`,
`ψ` and `ψ ∘ φ`. This file proves that **the isomorphism for the composite is the composite of
the two isomorphisms**.

This is the `ℤ`-indexed counterpart of
`Stacks.Cech.alternatingCechModuleComplexBaseChangeIso_comp_of_isPullback`, and it is the square
a naturality statement in `A'` for [Stacks, Tag 07VL] is built from: it says that the models of
`RΓ` of the two base changes in a tower are identified compatibly.

## Main results

* `Stacks.DerivedIndexing.comp_f_comp_eq_of_pinned_squares`: a purely diagrammatic lemma — if a
  three-fold composite of morphisms of complexes, read in one degree and against a morphism `d`,
  and a two-fold composite of the same kind are each pinned by a commuting square, and the
  pinned data satisfy the corresponding identity, then the two composites agree in that degree
  against `d`. The leading factor is the termwise image of a chain map under an additive functor,
  which is how the extension of scalars along `ψ` of the comparison for `φ` enters.
* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.preimage_comp_family`: the inverse-image
  family of an inverse-image family is the inverse-image family of the composite.
* `…ProperFlatGlobalSections.baseAlternatingCechComplexBaseChangeIso_comp`: **the cocycle
  identity.** Extending the scalars along `ψ` of the base-change isomorphism for `φ`, following
  it by the base-change isomorphism for `ψ` and then identifying the model of `g'^* (g^* F)` with
  that of `(g' ≫ g)^* F` gives the base-change isomorphism for `ψ ∘ φ`, read through the
  composition isomorphism `(- ⊗_A A') ⊗_{A'} A'' ≅ - ⊗_A A''` of `extendScalarsComplexCompIso`.

## Implementation notes

**The reduction to the `ℕ` level.** `hom_ext_baseAlternatingCechComplex` reduces the identity to
the degrees `(m : ℤ)` for `m : ℕ`, since the target model vanishes in negative degrees. In such a
degree every factor is pinned: the two base-change factors by
`baseAlternatingCechComplexBaseChangeIso_hom_f_comp_XIso`, the module-transport factor by
`baseAlternatingCechComplexMapIso_hom_f_comp_XIso`, each against the degree isomorphisms
`baseAlternatingCechComplexXIso` of the models. What is left after the pinnings is exactly
`Stacks.Cech.alternatingCechModuleObjBaseChangeIso_comp`, the `ℕ`-level degreewise cocycle, plus
the naturality of `ModuleCat.extendScalarsComp` in the module. No new mathematics enters.

**Why the diagrammatic step is abstract.** The identity is reached by postcomposing with the
degree isomorphism of the target, which is invertible, and then shuffling associativities. Doing
that shuffling on the goal itself is not possible: the goal mixes
`(((ModuleCat.extendScalars ψ).mapHomologicalComplex _).obj K).X p` with
`(ModuleCat.extendScalars ψ).obj (K.X p)`, which are definitionally but not reducibly equal, and
`rw`/`simp` — which revalidate at reducible transparency — refuse such a goal. The shuffling is
therefore `Stacks.DerivedIndexing.comp_f_comp_eq_of_pinned_squares`, stated for an arbitrary
additive functor between arbitrary preadditive categories where the obstruction is absent, and
applied in term position, where default transparency is in force. This is the discipline of
`BaseAlternatingCechBaseChangeDegreewise.lean`.

**Every proof argument appearing in a statement is a named theorem, never the term `rfl`.** The
hypothesis `∀ i, (g' ≫ g) ⁻¹ᵁ U i = g' ⁻¹ᵁ (g ⁻¹ᵁ U i)` of the `ℕ`-level cocycle holds by `rfl`,
but the *term* `rfl` elaborates against it to `@rfl _ ((g' ≫ g) ⁻¹ᵁ U i)`, whose type is not
syntactically the expected one; `preimage_comp_family`, being a theorem, has the declared type.
The same applies to `preimage_eq_preimage_equivRefl`.

**The index reindexing is the identity** throughout, as in the `ℕ`-level cocycle: all families
are indexed by the same `I` and the equivalence is `Equiv.refl I`.

The file runs under `HasDerivedCategory.standard` at priority `10000`, as the files it builds on
do, and imports `StacksFrontier.Homology.ExtendScalars.Flat` explicitly for the root-namespace
instance `extendScalars_additive`.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
* [Stacks Project, Tag 07VL](https://stacks.math.columbia.edu/tag/07VL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.DerivedIndexing

/-- **A three-fold composite of morphisms of complexes equals a two-fold one in a degree, given
the pinnings of the factors and the corresponding identity of the pinned data.**

The leading factor of the three-fold composite is the termwise image under an additive functor
`G` of a chain map `u`; the hypotheses `h₁`, `h₂`, `h₃` pin the three factors in the degree `i`
against morphisms `e₁`, `e₂`, `d`, and `h₄` pins the second factor of the two-fold composite.
`h₅` is the identity satisfied by the pinned data and `h₆` the naturality square relating the
leading morphisms of the two composites. The conclusion is the equality of the two composites in
degree `i`, read against `d`.

Nothing here is specific to extension of scalars or to Čech complexes; the statement is at this
generality because the goal of its application in
`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.baseAlternatingCechComplexBaseChangeIso_comp`
mixes the two spellings of a termwise functor image and so admits no rewriting. -/
lemma comp_f_comp_eq_of_pinned_squares {ι : Type*} {c : ComplexShape ι} {C D : Type*}
    [Category C] [Category D] [Preadditive C] [Preadditive D] (G : C ⥤ D) [G.Additive]
    {N₀ N₁ : HomologicalComplex C c} (u : N₀ ⟶ N₁)
    {L₂ L₃ M₀ : HomologicalComplex D c}
    (β : (G.mapHomologicalComplex c).obj N₁ ⟶ L₂) (γ : L₂ ⟶ L₃)
    (ρ : (G.mapHomologicalComplex c).obj N₀ ⟶ M₀) (σ : M₀ ⟶ L₃) (i : ι)
    {Z Y₂ Q : D} {Y₁ P : C} (d : L₃.X i ⟶ Z) (e₁ : N₁.X i ⟶ Y₁) (e₂ : L₂.X i ⟶ Y₂)
    (p : N₀.X i ⟶ P) (q₁ : P ⟶ Y₁) (q₂ : G.obj Y₁ ⟶ Y₂) (q₃ : Y₂ ⟶ Z) (c₀ : G.obj P ⟶ Q)
    (q₄ : Q ⟶ Z) (r : M₀.X i ⟶ Q)
    (h₁ : u.f i ≫ e₁ = p ≫ q₁)
    (h₂ : β.f i ≫ e₂ = G.map e₁ ≫ q₂)
    (h₃ : γ.f i ≫ d = e₂ ≫ q₃)
    (h₄ : σ.f i ≫ d = r ≫ q₄)
    (h₅ : G.map q₁ ≫ q₂ ≫ q₃ = c₀ ≫ q₄)
    (h₆ : G.map p ≫ c₀ = ρ.f i ≫ r) :
    ((G.mapHomologicalComplex c).map u ≫ β ≫ γ).f i ≫ d = (ρ ≫ σ).f i ≫ d := by
  simp only [HomologicalComplex.comp_f, Category.assoc, Functor.mapHomologicalComplex_map_f, h₃, h₄]
  rw [reassoc_of% h₂, ← G.map_comp_assoc, h₁, G.map_comp_assoc, h₅, reassoc_of% h₆]

end Stacks.DerivedIndexing

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The inverse-image family of an inverse-image family is the inverse-image family of the
composite.** This is the hypothesis `U'' i = g' ⁻¹ᵁ U' i` of
`Stacks.Cech.alternatingCechModuleObjBaseChangeIso_comp` for `U' = g ⁻¹ᵁ U` and
`U'' = (g' ≫ g) ⁻¹ᵁ U`. It holds by `rfl`, and is stated as a theorem because the term `rfl`
does not have this type syntactically; see the implementation notes. -/
theorem preimage_comp_family {X X' X'' : Scheme.{u}} (g : X' ⟶ X) (g' : X'' ⟶ X') {I : Type u}
    (U : I → X.Opens) (i : I) : (g' ≫ g) ⁻¹ᵁ U i = g' ⁻¹ᵁ (g ⁻¹ᵁ U i) :=
  rfl

variable {A A' A'' : Type u} [CommRing A] [CommRing A'] [CommRing A'']
  (φ : A →+* A') (ψ : A' →+* A'')
  {X X' X'' : Scheme.{u}} {f : X ⟶ Spec (.of A)} [IsSeparated f]
  {f' : X' ⟶ Spec (.of A')} {f'' : X'' ⟶ Spec (.of A'')}
  {g : X' ⟶ X} {g' : X'' ⟶ X'}
  (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
  (hsq' : IsPullback g' f'' f' (Spec.map (CommRingCat.ofHom ψ)))
  (F : X.Modules) [F.IsQuasicoherent] {I : Type u} [Finite I]
  (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))

/-- **The cocycle identity for the `ℤ`-indexed Čech base-change isomorphism.** For a tower of two
cartesian squares over `Spec φ` and `Spec ψ`, extending the scalars along `ψ` of the base-change
isomorphism for `φ`, following it by the base-change isomorphism for `ψ` and then identifying the
`A''`-linear model of `g'^* (g^* F)` with that of `(g' ≫ g)^* F` — by
`baseAlternatingCechComplexMapIso` applied to
`AlgebraicGeometry.Scheme.Modules.pullbackComp` — gives the base-change isomorphism for
`ψ ∘ φ` and `g' ≫ g`, read through the composition isomorphism
`(- ⊗_A A') ⊗_{A'} A'' ≅ - ⊗_A A''` of `extendScalarsComplexCompIso`.

Everything the identity needs beyond the two squares is produced from them: `f'` is separated
because separatedness is stable under base change, the inverse-image family is affine by
`isAffineOpen_preimage`, and the two squares paste by
`Stacks.Cech.isPullback_comp_specMap`.

The proof reduces to a single nonnegative degree by `hom_ext_baseAlternatingCechComplex` and
there to the `ℕ`-level `Stacks.Cech.alternatingCechModuleObjBaseChangeIso_comp` by the degreewise
pinnings of the three factors. -/
theorem baseAlternatingCechComplexBaseChangeIso_comp :
    haveI : IsSeparated f' := isSeparated_of_isPullback φ hsq
    ((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (baseAlternatingCechComplexBaseChangeIso φ hsq F U hU hUaff).hom ≫
        (baseAlternatingCechComplexBaseChangeIso ψ hsq' ((Scheme.Modules.pullback g).obj F)
            (fun i => g ⁻¹ᵁ U i) (top_eq_iSup_preimage g U hU)
            (isAffineOpen_preimage φ hsq U hUaff)).hom ≫
        (baseAlternatingCechComplexMapIso f'' (fun i => (g' ≫ g) ⁻¹ᵁ U i)
          (top_eq_iSup_preimage (g' ≫ g) U hU)
          ((Scheme.Modules.pullbackComp g' g).app F)).hom =
      (extendScalarsComplexCompIso φ ψ).hom.app (baseAlternatingCechComplex f U hU F) ≫
        (baseAlternatingCechComplexBaseChangeIso (ψ.comp φ)
          (Stacks.Cech.isPullback_comp_specMap φ ψ f f' f'' g g' hsq hsq') F U hU hUaff).hom := by
  have : IsSeparated f' := isSeparated_of_isPullback φ hsq
  have hU'aff : ∀ i, IsAffineOpen (g ⁻¹ᵁ U i) := isAffineOpen_preimage φ hsq U hUaff
  have hsq'' : IsPullback (g' ≫ g) f'' f (Spec.map (CommRingCat.ofHom (ψ.comp φ))) :=
    Stacks.Cech.isPullback_comp_specMap φ ψ f f' f'' g g' hsq hsq'
  refine hom_ext_baseAlternatingCechComplex f'' (fun i => (g' ≫ g) ⁻¹ᵁ U i)
    (top_eq_iSup_preimage (g' ≫ g) U hU) ((Scheme.Modules.pullback (g' ≫ g)).obj F) _ _
    fun m => ?_
  refine (Iso.cancel_iso_hom_right _ _ (baseAlternatingCechComplexXIso f''
    (fun i => (g' ≫ g) ⁻¹ᵁ U i) (top_eq_iSup_preimage (g' ≫ g) U hU)
    ((Scheme.Modules.pullback (g' ≫ g)).obj F) m)).1 ?_
  exact Stacks.DerivedIndexing.comp_f_comp_eq_of_pinned_squares
    (ModuleCat.extendScalars.{u, u, u} ψ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (baseAlternatingCechComplexBaseChangeIso_hom_f_comp_XIso φ hsq F U hU hUaff m)
    (baseAlternatingCechComplexBaseChangeIso_hom_f_comp_XIso ψ hsq'
      ((Scheme.Modules.pullback g).obj F) (fun i => g ⁻¹ᵁ U i) (top_eq_iSup_preimage g U hU)
      hU'aff m)
    (baseAlternatingCechComplexMapIso_hom_f_comp_XIso f'' (fun i => (g' ≫ g) ⁻¹ᵁ U i)
      (top_eq_iSup_preimage (g' ≫ g) U hU) ((Scheme.Modules.pullbackComp g' g).app F) m)
    (baseAlternatingCechComplexBaseChangeIso_hom_f_comp_XIso (ψ.comp φ) hsq'' F U hU hUaff m)
    (Stacks.Cech.alternatingCechModuleObjBaseChangeIso_comp φ ψ f f' f'' g g' F U
      (fun i => g ⁻¹ᵁ U i) (fun i => (g' ≫ g) ⁻¹ᵁ U i) (preimage_eq_preimage_equivRefl g U)
      (preimage_comp_family g g' U)
      (fun W => Stacks.Cech.baseRingHom_comp_app φ f f' g hsq W)
      (fun W => Stacks.Cech.baseRingHom_comp_app ψ f' f'' g' hsq' W)
      (fun W => Stacks.Cech.baseRingHom_comp_app (ψ.comp φ) f f'' (g' ≫ g) hsq'' W)
      hsq hsq' hsq'' hUaff hU'aff m)
    ((ModuleCat.extendScalarsComp φ ψ).inv.naturality
      (baseAlternatingCechComplexXIso f U hU F m).hom)

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end
