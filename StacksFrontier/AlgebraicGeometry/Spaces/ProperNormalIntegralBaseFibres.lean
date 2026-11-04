module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.ClopenGlobalFunction
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnected
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperConnectedFibresGeneralBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperNormalIntegralBase
public import StacksFrontier.AlgebraicGeometry.Spaces.UnibranchCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Stacks 0AYI: proper morphisms onto a normal integral space with `H⁰(X_ξ, 𝒪) = κ(ξ)`

Let `S` be a scheme and `f : X ⟶ Y` a morphism of algebraic spaces over `S` such that

1. `f` is proper,
2. `Y` is integral (Stacks 0AD4) with generic point `ξ`,
3. `Y` is normal,
4. `X` is reduced,
5. every generic point of an irreducible component of `|X|` maps to `ξ`,
6. `H⁰(X_ξ, 𝒪) = κ(ξ)`.

Then `f_* 𝒪_X = 𝒪_Y` and `f` has geometrically connected fibres: this is **Stacks 0AYI**.

The first conclusion is `AlgebraicGeometry.Space.isIso_fSharp_of_isNormal_of_isIntegralSpace`.
For the second, `f` is surjective — its image is closed and contains `ξ`, the fibre `X_ξ` being
nonempty because `H⁰(X_ξ, 𝒪) = κ(ξ) ≠ 0` — so the geometric fibres of `f` are connected by
`AlgebraicGeometry.Space.connectedPullback_of_isProper_of_isSurjective_of_isIso_fSharp`.  The fibre
of `f` over an arbitrary field-valued point `Spec k ⟶ Y` is then connected as well: it receives a
surjection from the fibre over the composite `Spec k̄ ⟶ Spec k ⟶ Y` with `k̄` an algebraic closure.

## Conventions

* `X_ξ` is the fibre `X ×_Y Spec κ(ξ)` over the monomorphism `Spec κ(ξ) ⟶ Y` from the spectrum of
  the residue field (Stacks 0EMW), and `H⁰(X_ξ, 𝒪) = κ(ξ)` is the statement that pullback of global
  functions along `X_ξ ⟶ Spec κ(ξ)` is bijective, the global functions of `Spec κ(ξ)` being
  `κ(ξ)`.
* "`f` has geometrically connected fibres" is stated as: for every field `k` and every morphism
  `Spec k ⟶ Y`, the fibre `X ×_Y Spec k` has connected point space.  The fibre `X_y` over a point
  `y` is geometrically connected over `κ(y)` exactly when `(X_y)_K = X ×_Y Spec K` is connected for
  every field extension `K/κ(y)`, and every such `Spec K ⟶ Spec κ(y) ⟶ Y` is a field-valued point
  of `Y`; conversely every field-valued point of `Y` factors through the residue field of its image
  point.  So the two formulations agree.

## Main results

* `AlgebraicGeometry.Space.isSurjective_of_bijective_globalFunctionsMap_genericFibre`: `f` is
  surjective.
* `AlgebraicGeometry.Space.connectedPullback_fieldMorphism_of_isProper_of_isIso_fSharp`: the fibres
  over all field-valued points of a proper surjective morphism with `f_* 𝒪_X = 𝒪_Y` are connected.
* `AlgebraicGeometry.Space.isIso_fSharp_and_connectedPullback_of_isNormal_of_isIntegralSpace`:
  **Stacks 0AYI**.

## References

* [Stacks Project, Tag 0AYI](https://stacks.math.columbia.edu/tag/0AYI)
* [Stacks Project, Tag 0A1C](https://stacks.math.columbia.edu/tag/0A1C)
* [Stacks Project, Tag 0A1A](https://stacks.math.columbia.edu/tag/0A1A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A proper morphism onto an irreducible space whose generic fibre has nonzero global functions
is surjective.**  The fibre `X ×_Y Spec κ` over a field-valued point `p` of `Y` with class `ξ` is
nonempty, its global functions being those of `Spec κ`; so `ξ` is in the image of `f`, which is
closed, and `ξ` is the generic point. -/
theorem isSurjective_of_bijective_globalFunctionsMap_genericFibre {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsProper B S hS f.hom) {ξ : points B S hS Y.1}
    (hξ : IsGenericPoint ξ Set.univ) (p : FieldValuedPoint B S hS Y.1)
    (hp : p.class B S hS Y.1 = ξ)
    (h6 : Function.Bijective (globalFunctionsMap B S hS (pullback.snd f
      (ObjectProperty.homMk (fieldMorphism B S hS Y.1 p) :
        schemeSpace (p.siteObject B S hS Y.1) ⟶ Y)))) :
    IsSurjective B S hS f.hom := by
  let ρ : schemeSpace (p.siteObject B S hS Y.1) ⟶ Y :=
    ObjectProperty.homMk (fieldMorphism B S hS Y.1 p)
  have : Nontrivial Γ((BigFppfOver.toScheme B S hS).obj (p.siteObject B S hS Y.1), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of p.carrier)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have : Nontrivial (globalFunctions B S hS (schemeSpace (p.siteObject B S hS Y.1)).obj) :=
    (globalFunctionsYonedaRingEquiv B S hS (p.siteObject B S hS Y.1)).toEquiv.nontrivial
  have : Nontrivial (globalFunctions B S hS (pullback f ρ).obj) :=
    (RingEquiv.ofBijective _ h6).symm.toEquiv.nontrivial
  obtain ⟨x'⟩ := nonempty_points_of_nontrivial_globalFunctions (B := B) (S := S) (hS := hS)
    (F := (pullback f ρ).obj)
  have hfx : pointsMap B S hS X.1 f.hom
      (pointsMap B S hS _ (pullback.fst f ρ).hom x') = ξ := by
    rw [← pointsMap_comp_apply, ← ObjectProperty.FullSubcategory.comp_hom, pullback.condition,
      ObjectProperty.FullSubcategory.comp_hom, pointsMap_comp_apply]
    exact (pointsMap_fieldMorphism_eq_class B S hS p _).trans hp
  have hsub : closure {ξ} ⊆ Set.range (pointsMap B S hS X.1 f.hom) :=
    closure_minimal (Set.singleton_subset_iff.mpr ⟨_, hfx⟩)
      (isClosedMap_pointsMap_of_pullback_fst_id B S hS f.hom (hf.2.2 Y.1 Y.2 (𝟙 _))).isClosed_range
  exact fun y => hsub (hξ.def ▸ Set.mem_univ y)

/-- **The fibres over field-valued points of a proper surjective morphism with `f_* 𝒪_X = 𝒪_Y`
are connected.**  For a field-valued point `p : Spec k ⟶ Y` let `k̄` be an algebraic closure of
`k`; the fibre over the geometric point `Spec k̄ ⟶ Spec k ⟶ Y` is connected
(`AlgebraicGeometry.Space.connectedPullback_of_isProper_of_isSurjective_of_isIso_fSharp`) and is
the base change of the fibre over `p` along the surjection `Spec k̄ ⟶ Spec k`, so it surjects onto
the fibre over `p`. -/
theorem connectedPullback_fieldMorphism_of_isProper_of_isIso_fSharp {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsProper B S hS f.hom) (hfs : IsSurjective B S hS f.hom)
    [IsIso (smallEtaleRingedToposHom B S hS f).fSharp] (p : FieldValuedPoint B S hS Y.1) :
    ConnectedPullback B S hS f.hom (fieldMorphism B S hS Y.1 p) := by
  let k := p.carrier
  let Ω := AlgebraicClosure k
  have hΩ : B.Contains (Spec (.of Ω)) := contains_specAlgebraicClosure B k p.contained
  let c : (Over.mk (fieldExtensionMap B k Ω p.contained hΩ ≫ (⟨p.toBase⟩ : B.obj p.contained ⟶
      B.obj hS)) : BigFppfOver B S hS) ⟶ p.siteObject B S hS Y.1 :=
    Over.homMk (fieldExtensionMap B k Ω p.contained hΩ) rfl
  let gp : FieldValuedPoint B S hS Y.1 :=
    { carrier := Ω
      contained := hΩ
      toBase := B.inclusion.map (fieldExtensionMap B k Ω p.contained hΩ) ≫ p.toBase
      value := Y.1.map c.op p.value }
  have hfac : yoneda.map c ≫ fieldMorphism B S hS Y.1 p = fieldMorphism B S hS Y.1 gp :=
    yonedaEquiv_symm_naturality_left c Y.1 p.value
  have hconn : ConnectedPullback B S hS f.hom (fieldMorphism B S hS Y.1 gp) :=
    connectedPullback_of_isProper_of_isSurjective_of_isIso_fSharp f hf hfs
      ⟨gp, (inferInstance : IsAlgClosed Ω)⟩
  have : ConnectedSpace (points B S hS
      (pullback (pullback.snd f.hom (fieldMorphism B S hS Y.1 p)) (yoneda.map c))) :=
    connectedSpace_of_presheafIso B S hS
      (pullback_point_compIso f.hom (fieldMorphism B S hS Y.1 p) (yoneda.map c)
        (fieldMorphism B S hS Y.1 gp) hfac) hconn
  have hsurj : Function.Surjective
      (pointsMap B S hS (yoneda.obj (gp.siteObject B S hS Y.1)) (yoneda.map c)) := fun _ =>
    ⟨(FieldValuedPoint.tautological B S hS gp).class B S hS _,
      (subsingleton_points_yoneda_siteObject B S hS p).elim _ _⟩
  exact (surjective_pointsMap_of_isPullback B S hS
    (IsPullback.of_hasPullback (pullback.snd f.hom (fieldMorphism B S hS Y.1 p))
      (yoneda.map c)).flip hsurj).connectedSpace (continuous_pointsMap B S hS _)

/-- **Stacks 0AYI.**  Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` such that

1. `f` is proper,
2. `Y` is integral (Stacks 0AD4, `AlgebraicGeometry.Space.IsIntegralSpace`) with generic point `ξ`,
3. `Y` is normal,
4. `X` is reduced,
5. every generic point of an irreducible component of `|X|` maps to `ξ`,
6. `H⁰(X_ξ, 𝒪) = κ(ξ)`: for the monomorphism `Spec κ(ξ) ⟶ Y` from the spectrum of the residue
   field at `ξ` (Stacks 0EMW) and the fibre `X_ξ = X ×_Y Spec κ(ξ)`, pullback of global functions
   `κ(ξ) = Γ(Spec κ(ξ), 𝒪) ⟶ Γ(X_ξ, 𝒪)` along the projection is bijective.

Then

* `f_* 𝒪_X = 𝒪_Y`: the canonical map `𝒪_Y ⟶ f_* 𝒪_X` (Stacks 03G8) is an isomorphism;
* `f` has geometrically connected fibres: for every field `k` and every morphism `Spec k ⟶ Y`, the
  fibre `X ×_Y Spec k` has connected point space.  Taking `Spec k ⟶ Spec κ(y) ⟶ Y` for the field
  extensions `k` of the residue field at a point `y`, this says that the fibre `X_y` is
  geometrically connected over `κ(y)`.

Normality and reducedness are the étale-local properties of schemes of Stacks 03E6, as elsewhere
in the library. -/
@[stacks 0AYI]
theorem isIso_fSharp_and_connectedPullback_of_isNormal_of_isIntegralSpace
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsProper B S hS f.hom) (hYint : IsIntegralSpace B S hS Y.1)
    {ξ : points B S hS Y.1} (hξ : IsGenericPoint ξ Set.univ)
    (hYnormal : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsNormal T))
    (hXred : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsReduced T))
    (hgen : ∀ x ∈ genericPoints (points B S hS X.1), pointsMap B S hS X.1 f.hom x = ξ)
    (h6 : Function.Bijective (globalFunctionsMap B S hS (pullback.snd f
      (ObjectProperty.homMk (residueFieldMorphism B S hS Y.1 hYint.2.1 ξ) :
        schemeSpace ((residueFieldRepresentative B S hS Y.1 hYint.2.1 ξ).1.siteObject B S hS Y.1) ⟶
          Y)))) :
    IsIso (smallEtaleRingedToposHom B S hS f).fSharp ∧
      ∀ p : FieldValuedPoint B S hS Y.1,
        ConnectedPullback B S hS f.hom (fieldMorphism B S hS Y.1 p) := by
  have := isIso_fSharp_of_isNormal_of_isIntegralSpace f hf hYint hYnormal hXred hξ hgen h6
  have hfs : IsSurjective B S hS f.hom :=
    isSurjective_of_bijective_globalFunctionsMap_genericFibre f hf hξ _
      (residueFieldRepresentative B S hS Y.1 hYint.2.1 ξ).2.1 h6
  exact ⟨inferInstance, connectedPullback_fieldMorphism_of_isProper_of_isIso_fSharp f hf hfs⟩

end AlgebraicGeometry.Space

end
