module

public import StacksFrontier.Cotangent.SheavesOfRings.AffineCotangentRestriction

/-!
# Compatibility of the affine comparison map with restriction, as sheaves

Let `f : X ⟶ Y` be a morphism of schemes, let `U' ≤ U` be affine opens of `X` and `V' ≤ V` opens
of `Y` with `f(U) ⊂ V` and `f(U') ⊂ V'`. Write `A = 𝒪_Y(V)`, `B = 𝒪_X(U)`, `A' = 𝒪_Y(V')` and
`B' = 𝒪_X(U')`. Tag 08T3 attaches to these data the canonical map

```
  ~(L_{B/A}) ⟶ L_{X/Y}|_U
```

of complexes of `𝒪_U`-modules, `AlgebraicGeometry.Scheme.Hom.affineCotangentComparison`. Its
third assertion is that these maps are compatible with restriction to smaller affine opens. This
file proves that assertion **as sheaves**: writing `ρ : Spec B' ⟶ Spec B` for the morphism
induced by the restriction map `B ⟶ B'`, the square

```
  ~(L_{B/A})          ⟶   L_{X/Y}|_U
       |                        |
       ↓                        ↓
  ρ_*(~(L_{B'/A'}))   ⟶   ρ_*(L_{X/Y}|_{U'})
```

of complexes of `𝒪_{Spec B}`-modules commutes, the bottom row being the pushforward along `ρ` of
the comparison map for `U'`, `V'`. The two vertical maps are the restriction maps: on the right
it is literally the restriction map of the sheaf `L_{X/Y}` read through the identifications of
`U` with `Spec B` and of `U'` with `Spec B'`
(`Stacks.AffineCotangentSheaf.restrictionUnit_app_app`), on the left it is the adjunct, under the
universal property of the associated-sheaf functor, of the functoriality of the cotangent complex
of a ring map in the square `AlgebraicGeometry.Scheme.Hom.affineRestrictionSquare` of restriction
maps.

The proof is the universal property of `~` (Tag 01I7, available as the tilde–`Γ` adjunction)
applied twice: both composites in the square are maps out of `~(L_{B/A})`, so they agree as soon
as their adjuncts do, and the adjunct statement is the compatibility of
`AlgebraicGeometry.Scheme.Hom.gammaCotangentComparison` with restriction, which is the sectionwise
statement `AlgebraicGeometry.Scheme.Hom.cotangentSectionsComparison_restriction` together with the
identification `fromSpec ''ᵁ ⊤ = U`.

## Main definitions

* `Stacks.AffineCotangentSheaf.gammaPushforwardIso`: global sections over `Spec R` of a
  pushforward along `Spec φ` are the restriction of scalars along `φ : R ⟶ S` of global sections
  over `Spec S`. This is Mathlib's
  `AlgebraicGeometry.pushforwardCompModulesSpecToSheafIso` evaluated at the whole of `Spec R`.
* `Stacks.AffineCotangentSheaf.specRestriction` is `ρ : Spec 𝒪_X(U') ⟶ Spec 𝒪_X(U)`, and
  `Stacks.AffineCotangentSheaf.restrictionUnit` is the restriction map
  `M|_U ⟶ ρ_*(M|_{U'})` of a sheaf of modules on `X`.
* `Stacks.AffineCotangentSheaf.gammaRestrictionComparison` is the map
  `L_{B/A} ⟶ Γ(ρ_*(~(L_{B'/A'})))` of complexes of `B`-modules, and
  `Stacks.AffineCotangentSheaf.tildeCotangentRestriction` is its adjunct
  `~(L_{B/A}) ⟶ ρ_*(~(L_{B'/A'}))`, the left vertical map of the square.
* `Stacks.AffineCotangentSheaf.restrictedCotangentRestriction` is the right vertical map
  `L_{X/Y}|_U ⟶ ρ_*(L_{X/Y}|_{U'})` of the square.

## Main results

* `Stacks.AffineCotangentSheaf.restrictionUnit_app_app`: the sections of
  `Stacks.AffineCotangentSheaf.restrictionUnit` are the restriction maps of `M`.
* `Stacks.AffineCotangentSheaf.gammaCotangentComparison_restriction` and
  `Stacks.AffineCotangentSheaf.gammaCotangentComparison_restriction_degree`: the canonical map
  `L_{B/A} ⟶ Γ(L_{X/Y}|_U)` commutes with restriction. This is the adjunct form of the main
  result.
* `Stacks.AffineCotangentSheaf.affineCotangentComparison_restriction` and
  `Stacks.AffineCotangentSheaf.affineCotangentComparison_restriction_degree`: **the third
  assertion of Tag 08T3**, the commuting square above, as an equality of maps of complexes of
  `𝒪_{Spec 𝒪_X(U)}`-modules and degreewise as an equality of maps of sheaves of modules.

## Implementation notes

Hypotheses: a morphism of schemes `f : X ⟶ Y`; opens `U' ≤ U` of `X` with
`hU : IsAffineOpen U` and `hU' : IsAffineOpen U'`; opens `V' ≤ V` of `Y`; and the containments
`U ≤ f⁻¹V`, `U' ≤ f⁻¹V'`. Both affineness hypotheses are genuinely needed and neither is
dischargeable: `AlgebraicGeometry.Scheme.Hom.affineCotangentComparison` is only defined for an
affine open, so `IsAffineOpen U` is needed to state the square at all and `IsAffineOpen U'` is
needed for its bottom row; `IsAffineOpen U'` is used a second time to know that
`ρ = Spec (𝒪_X(U) ⟶ 𝒪_X(U'))` is an open immersion
(`Stacks.AffineCotangentSheaf.isOpenImmersion_specRestriction`), which is what identifies the
restriction of `L_{X/Y}|_U` along `ρ` with `L_{X/Y}|_{U'}`. Affineness of `V` and of `V'` is
*not* assumed: nothing in the construction uses it. This generalizes the hypotheses of the
source statement rather than weakening its conclusion.

The square is stated with the pushforward `ρ_*` rather than with the restriction `ρ^*`. The two
forms are equivalent: `Scheme.Modules.restrictFunctor ρ` is left adjoint to
`Scheme.Modules.pushforward ρ`, so transposing the square along that adjunction turns the
pushforward form into the statement that restricting the comparison map for `U`, `V` along `ρ`
agrees with the comparison map for `U'`, `V'`. The pushforward form is the one written out here
because the right-hand vertical map is then literally a restriction map of the sheaf `L_{X/Y}`,
with no comparison isomorphism intervening.

`Stacks.AffineCotangentSheaf.gammaPushforwardIso` is obtained by whiskering Mathlib's
`AlgebraicGeometry.pushforwardCompModulesSpecToSheafIso` with evaluation at `⊤` rather than
written out by hand. Written out by hand its `map_smul` is exactly
`AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality`, but the two `R`-module structures on the
sections are not definitionally equal, so a hand-written identity map does not typecheck without
that naturality; Mathlib's iso packages it.

The two adjunct lemmas `Stacks.AffineCotangentSheaf.affineCotangentComparison_f` and
`Stacks.AffineCotangentSheaf.tildeCotangentRestriction_f` spell the type arguments of
`homEquiv` out in full. Both maps are built as `tilde.map _ ≫ fromTildeΓNatTrans.app _`, which
is the adjunct up to unfolding, but the target of the degreewise map is spelled
`(F.mapHomologicalComplex _ |>.obj C).X j` on one side and `F.obj (C.X j)` on the other; those
are definitionally equal but not syntactically, and `rw [Equiv.apply_symm_apply]` needs the two
occurrences of `homEquiv` to be syntactically the same term.

## References

* [Stacks Project, Tag 08T3](https://stacks.math.columbia.edu/tag/08T3)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

universe u

namespace Stacks.AffineCotangentSheaf

/-! ### Global sections of a pushforward along a morphism of affine schemes -/

section Gamma

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- **Global sections of a pushforward along `Spec φ`.** For `φ : R ⟶ S` and a sheaf of modules
`Q` on `Spec S`, the global sections of `(Spec φ)_* Q` as an `R`-module are the global sections
of `Q` with scalars restricted along `φ`. This is Mathlib's
`AlgebraicGeometry.pushforwardCompModulesSpecToSheafIso` evaluated at the whole of `Spec R`. -/
def gammaPushforwardIso :
    moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom ≅
      Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) :=
  (Functor.isoWhiskerRight (AlgebraicGeometry.pushforwardCompModulesSpecToSheafIso φ)
    (TopCat.Sheaf.forget (ModuleCat.{u} R) _ ⋙ (evaluation _ _).obj (op ⊤))).symm

/-- Taking global sections of `𝒪_{Spec R}`-modules is additive: it is the right adjoint of the
associated-sheaf functor of Tag 01I7, which is additive. -/
instance additive_moduleSpecΓFunctor : (moduleSpecΓFunctor (R := R)).Additive :=
  (tilde.adjunction (R := R)).right_adjoint_additive

/-- On sections, `Stacks.AffineCotangentSheaf.gammaPushforwardIso` is the identity: restriction
of scalars does not change the underlying type, and `(Spec φ)⁻¹⊤ = ⊤`. -/
theorem gammaPushforwardIso_hom_app_apply (Q : (Spec S).Modules)
    (x : (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom).obj Q) :
    (gammaPushforwardIso φ).hom.app Q x = x := rfl

end Gamma

/-! ### The restriction morphism of affine spectra, and restriction of sheaves of modules -/

section SpecRestriction

variable {X : Scheme.{u}} {U U' : X.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
  (hUle : U' ≤ U)

/-- The morphism `ρ : Spec 𝒪_X(U') ⟶ Spec 𝒪_X(U)` induced by the restriction map
`𝒪_X(U) ⟶ 𝒪_X(U')`. -/
def specRestriction : Spec Γ(X, U') ⟶ Spec Γ(X, U) :=
  Spec.map (X.presheaf.map (homOfLE hUle).op)

/-- `ρ` is compatible with the identifications of `U` with `Spec 𝒪_X(U)` and of `U'` with
`Spec 𝒪_X(U')`. -/
theorem specRestriction_fromSpec :
    specRestriction hUle ≫ hU.fromSpec = hU'.fromSpec :=
  hU.map_fromSpec hU' (homOfLE hUle).op

include hU hU' in
/-- **`ρ` is an open immersion.** It becomes the open immersion `hU'.fromSpec` after composing
with the open immersion `hU.fromSpec`. -/
theorem isOpenImmersion_specRestriction : IsOpenImmersion (specRestriction (X := X) hUle) :=
  have : IsOpenImmersion (specRestriction (X := X) hUle ≫ hU.fromSpec) := by
    rw [specRestriction_fromSpec hU hU' hUle]; infer_instance
  AlgebraicGeometry.IsOpenImmersion.of_comp _ hU.fromSpec

/-- **The restriction map `M|_U ⟶ ρ_*(M|_{U'})`** of a sheaf of modules on `X`, read through the
identifications of `U` with `Spec 𝒪_X(U)` and of `U'` with `Spec 𝒪_X(U')`: the unit of the
restriction/pushforward adjunction along `ρ`, followed by the identification of the restriction
along `ρ` of the restriction along `hU.fromSpec` with the restriction along `hU'.fromSpec`. -/
def restrictionUnit :
    Scheme.Modules.restrictFunctor hU.fromSpec ⟶
      Scheme.Modules.restrictFunctor hU'.fromSpec ⋙
        Scheme.Modules.pushforward (specRestriction hUle) :=
  have : IsOpenImmersion (specRestriction (X := X) hUle) :=
    isOpenImmersion_specRestriction hU hU' hUle
  Functor.whiskerLeft (Scheme.Modules.restrictFunctor hU.fromSpec)
      (Scheme.Modules.restrictAdjunction (specRestriction hUle)).unit ≫
    Functor.whiskerRight
      ((Scheme.Modules.restrictFunctorComp (specRestriction hUle) hU.fromSpec).symm ≪≫
        Scheme.Modules.restrictFunctorCongr (specRestriction_fromSpec hU hU' hUle)).hom
      (Scheme.Modules.pushforward (specRestriction hUle))

/-- **The sections of `Stacks.AffineCotangentSheaf.restrictionUnit` are the restriction maps of
`M`.** Over an open `W` of `Spec 𝒪_X(U)` the map is `M.presheaf.map` of the inclusion
`hU'.fromSpec ''ᵁ ρ⁻¹W ≤ hU.fromSpec ''ᵁ W`. -/
theorem restrictionUnit_app_app (M : X.Modules) (W : (Spec Γ(X, U)).Opens)
    (h : hU'.fromSpec ''ᵁ (specRestriction hUle ⁻¹ᵁ W) ≤ hU.fromSpec ''ᵁ W) :
    ((restrictionUnit hU hU' hUle).app M).app W = M.presheaf.map (homOfLE h).op := by
  have : IsOpenImmersion (specRestriction (X := X) hUle) :=
    isOpenImmersion_specRestriction hU hU' hUle
  simp only [restrictionUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.trans_hom, Iso.symm_hom,
    Scheme.Modules.restrictAdjunction_unit_app_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrict_map]
  show M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _ = M.presheaf.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg M.presheaf.map (Subsingleton.elim _ _)

end SpecRestriction

/-! ### Assertion 3 of Tag 08T3 -/

section Main

open AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {U U' : X.Opens} {V V' : Y.Opens}
  (hU : IsAffineOpen U) (hU' : IsAffineOpen U')

/-- **Compatibility of the canonical map `L_{B/A} ⟶ Γ(L_{X/Y}|_U)` with restriction.** The
canonical map of `AlgebraicGeometry.Scheme.Hom.gammaCotangentComparison` commutes with
restricting to a smaller affine open `U' ≤ U` of `X` and a smaller open `V' ≤ V` of `Y`: the
source's restriction map is the functoriality of the cotangent complex of a ring map in the
square `AlgebraicGeometry.Scheme.Hom.affineRestrictionSquare`, and the target's is the
restriction map of the sheaf `L_{X/Y}`. This is the adjunct form of
`Stacks.AffineCotangentSheaf.affineCotangentComparison_restriction`. -/
theorem gammaCotangentComparison_restriction (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V')
    (hUle : U' ≤ U) (hVle : V' ≤ V) (j : ℤ)
    (x : (CommAlgCat.cotangentComplex.{u, u} Γ(Y, V) (affineAlgebra f e)).X j) :
    (moduleSpecΓFunctor (R := Γ(X, U))).map
        ((restrictionUnit hU hU' hUle).app (f.cotangentComplex.X j))
        ((gammaCotangentComparison f hU e).f j x) =
      (gammaPushforwardIso (X.presheaf.map (homOfLE hUle).op)).hom.app
          ((Scheme.Modules.restrictFunctor hU'.fromSpec).obj (f.cotangentComplex.X j))
        ((ModuleCat.restrictScalars (affineRestrictionSquare f e e' hUle hVle).map).map
            ((gammaCotangentComparison f hU' e').f j)
          ((CommAlgCat.squareCotangentComplexMap.{u, u, u}
            (affineRestrictionSquare f e e' hUle hVle)).f j x)) := by
  have himg : hU'.fromSpec ''ᵁ (specRestriction hUle ⁻¹ᵁ (⊤ : (Spec Γ(X, U)).Opens)) = U' := by
    show hU'.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U')).Opens) = U'
    exact hU'.fromSpec_image_top
  have h₁ : hU'.fromSpec ''ᵁ (specRestriction hUle ⁻¹ᵁ (⊤ : (Spec Γ(X, U)).Opens)) ≤
      hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) := by
    rwa [himg, hU.fromSpec_image_top]
  have hunit := ConcreteCategory.congr_hom
    (restrictionUnit_app_app hU hU' hUle (f.cotangentComplex.X j) ⊤ h₁)
    ((gammaCotangentComparison f hU e).f j x)
  refine hunit.trans ?_
  have key := cotangentSectionsComparison_restriction f e e' hUle hVle j x
  have e1 := ConcreteCategory.congr_hom
    ((Scheme.Modules.presheaf (f.cotangentComplex.X j)).map_comp
      (eqToHom (hU.fromSpec_image_top)).op (homOfLE h₁).op)
    ((cotangentSectionsComparison f e).f j x)
  have e2 := ConcreteCategory.congr_hom
    ((Scheme.Modules.presheaf (f.cotangentComplex.X j)).map_comp
      (homOfLE hUle).op (eqToHom (hU'.fromSpec_image_top)).op)
    ((cotangentSectionsComparison f e).f j x)
  have e3 : ((eqToHom (hU.fromSpec_image_top)).op ≫ (homOfLE h₁).op) =
      ((homOfLE hUle).op ≫ (eqToHom (hU'.fromSpec_image_top)).op) := Subsingleton.elim _ _
  refine (e1.symm.trans ((congrArg
    (fun k => (Scheme.Modules.presheaf (f.cotangentComplex.X j)).map k
      ((cotangentSectionsComparison f e).f j x)) e3).trans e2)).trans ?_
  exact congrArg
    (fun z => (Scheme.Modules.presheaf (f.cotangentComplex.X j)).map
      (eqToHom (hU'.fromSpec_image_top)).op z) key

/-- **Compatibility of the canonical map `L_{B/A} ⟶ Γ(L_{X/Y}|_U)` with restriction**, as an
equality of maps of `𝒪_X(U)`-modules in a single cohomological degree. -/
theorem gammaCotangentComparison_restriction_degree (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V')
    (hUle : U' ≤ U) (hVle : V' ≤ V) (j : ℤ) :
    (gammaCotangentComparison f hU e).f j ≫
        (moduleSpecΓFunctor (R := Γ(X, U))).map
          ((restrictionUnit hU hU' hUle).app (f.cotangentComplex.X j)) =
      (CommAlgCat.squareCotangentComplexMap.{u, u, u}
          (affineRestrictionSquare f e e' hUle hVle)).f j ≫
        (ModuleCat.restrictScalars (affineRestrictionSquare f e e' hUle hVle).map).map
            ((gammaCotangentComparison f hU' e').f j) ≫
          (gammaPushforwardIso (X.presheaf.map (homOfLE hUle).op)).hom.app
            ((Scheme.Modules.restrictFunctor hU'.fromSpec).obj (f.cotangentComplex.X j)) :=
  ConcreteCategory.hom_ext _ _
    (gammaCotangentComparison_restriction f hU hU' e e' hUle hVle j)

/-- `~(L_{B/A})` for `B = 𝒪_X(U)` and `A = 𝒪_Y(V)`: the source of the canonical map of
Tag 08T3. -/
abbrev tildeAffineCotangentComplex (e : U ≤ f ⁻¹ᵁ V) :
    CochainComplex (Spec Γ(X, U)).Modules ℤ :=
  ((tilde.functor Γ(X, U)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (CommAlgCat.cotangentComplex.{u, u} Γ(Y, V) (affineAlgebra f e))

/-- The map `L_{B/A} ⟶ Γ(ρ_*(~(L_{B'/A'})))` of complexes of `B`-modules: the functoriality of
the cotangent complex of a ring map in the square
`AlgebraicGeometry.Scheme.Hom.affineRestrictionSquare` of restriction maps, followed by the unit
of the tilde–`Γ` adjunction on `Spec B'` and by
`Stacks.AffineCotangentSheaf.gammaPushforwardIso`. -/
def gammaRestrictionComparison (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V')
    (hUle : U' ≤ U) (hVle : V' ≤ V) :
    CommAlgCat.cotangentComplex.{u, u} Γ(Y, V) (affineAlgebra f e) ⟶
      ((Scheme.Modules.pushforward (specRestriction hUle) ⋙
            moduleSpecΓFunctor (R := Γ(X, U))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (tildeAffineCotangentComplex f e') :=
  CommAlgCat.squareCotangentComplexMap.{u, u, u} (affineRestrictionSquare f e e' hUle hVle) ≫
    ((ModuleCat.restrictScalars
        (affineRestrictionSquare f e e' hUle hVle).map).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (tilde.adjunction (R := Γ(X, U'))).unit
          (ComplexShape.up ℤ)).app
            (CommAlgCat.cotangentComplex.{u, u} Γ(Y, V') (affineAlgebra f e'))) ≫
      (NatTrans.mapHomologicalComplex
        (gammaPushforwardIso (X.presheaf.map (homOfLE hUle).op)).hom
        (ComplexShape.up ℤ)).app (tildeAffineCotangentComplex f e')

/-- **The restriction map on the sheafified affine cotangent complexes.** The canonical map
`~(L_{B/A}) ⟶ ρ_*(~(L_{B'/A'}))` of complexes of `𝒪_{Spec B}`-modules, where
`ρ : Spec B' ⟶ Spec B` is induced by restriction: the adjunct, under the universal property of
the associated-sheaf functor (Tag 01I7), of
`Stacks.AffineCotangentSheaf.gammaRestrictionComparison`. -/
def tildeCotangentRestriction (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V')
    (hUle : U' ≤ U) (hVle : V' ≤ V) :
    tildeAffineCotangentComplex f e ⟶
      ((Scheme.Modules.pushforward (specRestriction hUle)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (tildeAffineCotangentComplex f e') :=
  ((tilde.functor Γ(X, U)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (gammaRestrictionComparison f e e' hUle hVle) ≫
    (NatTrans.mapHomologicalComplex (Scheme.Modules.fromTildeΓNatTrans (R := Γ(X, U)))
      (ComplexShape.up ℤ)).app
        (((Scheme.Modules.pushforward (specRestriction hUle)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (tildeAffineCotangentComplex f e'))

/-- **The restriction map on the restricted cotangent complexes.** The canonical map
`L_{X/Y}|_U ⟶ ρ_*(L_{X/Y}|_{U'})` of complexes of `𝒪_{Spec B}`-modules: the restriction map of
the sheaf `L_{X/Y}`, read through the identifications of `U` with `Spec 𝒪_X(U)` and of `U'` with
`Spec 𝒪_X(U')`; see `Stacks.AffineCotangentSheaf.restrictionUnit_app_app`. -/
def restrictedCotangentRestriction (hUle : U' ≤ U) :
    restrictedCotangentComplex f hU ⟶
      ((Scheme.Modules.pushforward (specRestriction hUle)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (restrictedCotangentComplex f hU') :=
  (NatTrans.mapHomologicalComplex (restrictionUnit hU hU' hUle)
    (ComplexShape.up ℤ)).app f.cotangentComplex

/-- In each cohomological degree, the canonical map of Tag 08T3 is the adjunct of
`AlgebraicGeometry.Scheme.Hom.gammaCotangentComparison` under the tilde–`Γ` adjunction. -/
theorem affineCotangentComparison_f (e : U ≤ f ⁻¹ᵁ V) (j : ℤ) :
    (affineCotangentComparison f hU e).f j =
      ((tilde.adjunction (R := Γ(X, U))).homEquiv _ _).symm
        ((gammaCotangentComparison f hU e).f j) := by
  rw [Adjunction.homEquiv_counit]
  rfl

/-- The unit of the tilde–`Γ` adjunction followed by the global sections of the canonical map of
Tag 08T3 is `AlgebraicGeometry.Scheme.Hom.gammaCotangentComparison`. -/
theorem gammaCotangentComparison_eq (e : U ≤ f ⁻¹ᵁ V) (j : ℤ) :
    (tilde.adjunction (R := Γ(X, U))).unit.app
          ((CommAlgCat.cotangentComplex.{u, u} Γ(Y, V) (affineAlgebra f e)).X j) ≫
        (moduleSpecΓFunctor (R := Γ(X, U))).map ((affineCotangentComparison f hU e).f j) =
      (gammaCotangentComparison f hU e).f j := by
  have h1 : (tilde.adjunction (R := Γ(X, U))).homEquiv _ _
      ((affineCotangentComparison f hU e).f j) = (gammaCotangentComparison f hU e).f j := by
    rw [affineCotangentComparison_f, Equiv.apply_symm_apply]
  exact (Adjunction.homEquiv_unit _ _ _ _).symm.trans h1

/-- In each cohomological degree, the left vertical map of the square is the adjunct of
`Stacks.AffineCotangentSheaf.gammaRestrictionComparison` under the tilde–`Γ` adjunction. -/
theorem tildeCotangentRestriction_f (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V')
    (hUle : U' ≤ U) (hVle : V' ≤ V) (j : ℤ) :
    (tildeCotangentRestriction f e e' hUle hVle).f j =
      ((tilde.adjunction (R := Γ(X, U))).homEquiv
          ((CommAlgCat.cotangentComplex.{u, u} Γ(Y, V) (affineAlgebra f e)).X j)
          ((((Scheme.Modules.pushforward (specRestriction hUle)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (tildeAffineCotangentComplex f e')).X j)).symm
        ((gammaRestrictionComparison f e e' hUle hVle).f j) := by
  rw [Adjunction.homEquiv_counit]
  rfl

/-- **Stacks 08T3, assertion 3, as sheaves.** For a morphism of schemes `f : X ⟶ Y`, affine opens
`U' ≤ U` of `X` and opens `V' ≤ V` of `Y` with `f(U) ⊂ V` and `f(U') ⊂ V'`, the canonical map
`~(L_{𝒪_X(U)/𝒪_Y(V)}) ⟶ L_{X/Y}|_U` of Tag 08T3 is compatible with restriction: writing
`ρ : Spec 𝒪_X(U') ⟶ Spec 𝒪_X(U)` for the morphism induced by restriction, the square formed by
the two comparison maps and the two restriction maps commutes as an equality of maps of complexes
of `𝒪_{Spec 𝒪_X(U)}`-modules. -/
@[stacks 08T3 "ASSERTION 3 ONLY, and AS SHEAVES: the canonical map of this tag, \
~(L_{O_X(U)/O_Y(V)}) -> L_{X/Y}|_U, is compatible with restriction along affine opens U' <= U \
and opens V' <= V, as an EQUALITY of maps of complexes of sheaves of O_{Spec O_X(U)}-modules -- \
not a Nonempty and not the sectionwise statement. The two vertical maps of the square are \
tildeCotangentRestriction and restrictedCotangentRestriction; the latter is the genuine sheaf \
restriction map, which restrictionUnit_app_app proves acts on sections as presheaf.map \
(homOfLE _).op. CARRIED: IsAffineOpen U and IsAffineOpen U', which are the source's own \
hypotheses -- the comparison map is only defined for an affine open -- and nothing else; \
IsAffineOpen V and IsAffineOpen V' are NOT carried, so this is more general than the source in \
the base variables. ASSERTIONS 1 AND 2 ARE NOT CLAIMED HERE"]
theorem affineCotangentComparison_restriction (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V')
    (hUle : U' ≤ U) (hVle : V' ≤ V) :
    affineCotangentComparison f hU e ≫ restrictedCotangentRestriction f hU hU' hUle =
      tildeCotangentRestriction f e e' hUle hVle ≫
        ((Scheme.Modules.pushforward (specRestriction hUle)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (affineCotangentComparison f hU' e') := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    affineCotangentComparison_f, tildeCotangentRestriction_f]
  refine ((tilde.adjunction (R := Γ(X, U))).homEquiv _ _).injective ?_
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  refine ConcreteCategory.hom_ext _ _ fun x => ?_
  refine (gammaCotangentComparison_restriction f hU hU' e e' hUle hVle j x).trans ?_
  exact (ConcreteCategory.congr_hom (gammaCotangentComparison_eq f hU' e' j)
    ((CommAlgCat.squareCotangentComplexMap.{u, u, u}
      (affineRestrictionSquare f e e' hUle hVle)).f j x)).symm

/-- **Stacks 08T3, assertion 3, as sheaves**, in a single cohomological degree: the square
commutes as an equality of maps of sheaves of `𝒪_{Spec 𝒪_X(U)}`-modules. -/
theorem affineCotangentComparison_restriction_degree (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V')
    (hUle : U' ≤ U) (hVle : V' ≤ V) (j : ℤ) :
    (affineCotangentComparison f hU e).f j ≫
        (restrictedCotangentRestriction f hU hU' hUle).f j =
      (tildeCotangentRestriction f e e' hUle hVle).f j ≫
        (Scheme.Modules.pushforward (specRestriction hUle)).map
          ((affineCotangentComparison f hU' e').f j) :=
  congrArg (fun k => HomologicalComplex.Hom.f k j)
    (affineCotangentComparison_restriction f hU hU' e e' hUle hVle)

end Main

end Stacks.AffineCotangentSheaf

end
