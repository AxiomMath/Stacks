module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.StalksTestMaps
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Coefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A stalkwise criterion for base change on higher direct images

Consider a cartesian diagram of schemes
```
X  ←-h-  Y
|f       |e
S  ←-g-  T
```
with `g : T ⟶ S` quasi-compact and quasi-separated, let `F` be an abelian sheaf on `T_étale` and
let `q ≥ 0`. The base change map on higher direct images `f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is a
morphism of abelian sheaves on `X_étale`, so it is an isomorphism exactly when it is an
isomorphism on the stalk at every geometric point `x̄` of `X`. Moreover the stalk of
`f⁻¹ R^q g_* F` at `x̄` is the stalk of `R^q g_* F` at the image geometric point `s̄ = f(x̄)`, so
the condition at `x̄` reads as invertibility of a canonical map
`(R^q g_* F)_{s̄} ⟶ (R^q h_* e⁻¹ F)_{x̄}`.

Three ingredients go into this. Conservativity is the statement that the stalk functors at the
geometric points of a scheme jointly reflect isomorphisms of abelian sheaves on its small étale
site. It cannot be read off from the fact that the geometric points form a conservative family of
points of the site, because that notion is formulated for coefficients in the universe of the
points, whereas abelian sheaves on the small étale site of `X : Scheme.{u}` have coefficients in
`Ab.{u + 1}`, a category which is not concrete over `Type u`. Local injectivity and local
surjectivity are conditions on germs, however, so they are visible to the `Type u`-valued fibres;
the route taken here is to compose with the forgetful functor to sets, where the conservativity
statement at the mismatched universes is available, and to use that the forgetful functor
commutes with taking fibres at a point of a site. The comparison of stalks under inverse image is
the identification of the fibre of an inverse-image point, together with the invariance of the
elements-colimit which computes a stalk under an isomorphism of fibre functors. The base change
map itself is the degree-`q` cohomology of the canonical derived base change comparison.

## Main definitions

* `Stacks.EtaleCohomology.smallEtalePullbackStalkAbIso` — the stalk at a geometric point `x̄` of
  the inverse image `f⁻¹ G` of an abelian sheaf is the stalk of `G` at the image geometric point
  `f(x̄)`.
* `Stacks.EtaleCohomology.higherBaseChangeMapAbStalk` — the canonical map
  `(R^q g_* F)_{s̄} ⟶ (R^q h_* e⁻¹ F)_{x̄}` attached to a geometric point `x̄` of `X` with image
  `s̄ = f(x̄)`.

## Main results

* `Stacks.EtaleCohomology.isIso_iff_forall_isIso_smallEtaleStalkAb` — a morphism of abelian
  sheaves on the small étale site of a scheme is an isomorphism if and only if it is an
  isomorphism on the stalk at every geometric point.
* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_iff_forall_isIso_stalk` — the base
  change map on degree-`q` higher direct images attached to a cartesian square with
  quasi-compact and quasi-separated base morphism is an isomorphism if and only if it is an
  isomorphism on the stalk at every geometric point of `X`.
* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_iff_forall_isIso_stalkMap` — the same
  criterion with the condition at `x̄` phrased as invertibility of the canonical map
  `(R^q g_* F)_{s̄} ⟶ (R^q h_* e⁻¹ F)_{x̄}`.

## Implementation notes

A geometric point of `X` is a morphism out of the spectrum of an algebraically closed field,
packaged as `AlgebraicGeometry.GeometricPoint`. The stalk at such a point is
`Stacks.EtaleCohomology.smallEtaleStalkAb`, the fibre at the point of the small étale site which
the geometric point determines; it takes a morphism out of the spectrum of a *separably* closed
field, and an algebraically closed field is separably closed. The conservative family used to
prove sufficiency of the stalkwise condition is therefore the one indexed by the points of `X`,
taking at each the algebraic closure of the residue field, which is jointly surjective on the
underlying space. The image geometric point `s̄ = f(x̄)` is written `x.hom ≫ f`, which is the
morphism underlying `AlgebraicGeometry.GeometricPoint.map`.

Only the commutativity of the square enters the proofs; that the square is cartesian and that `g`
is quasi-compact and quasi-separated are carried because they are the hypotheses under which the
criterion is stated at its source.

The equality of cohomology groups
`H^q(Spec(𝒪^{sh}_{X,x̄}) ×_S T, F) = H^q(Spec(𝒪^{sh}_{S,s̄}) ×_S T, F)`
which the source uses to phrase the stalkwise condition is not available: it identifies each of
the two stalks above with the cohomology of `F` over a fibre product with a strict henselization,
which is the statement that the canonical map
`AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSections` is an isomorphism for a
quasi-compact and quasi-separated morphism, and that is not proved in the library. The condition
is therefore stated with the two stalks in place of the two cohomology groups, which is what the
source's proof identifies them with.

## References

* [Stacks Project, Tag 0EZU](https://stacks.math.columbia.edu/tag/0EZU)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- Forgetting the group structure of an abelian group commutes with `u`-filtered colimits, the
abelian groups living one universe up. -/
private instance : PreservesFilteredColimitsOfSize.{u, u} (forget Ab.{u + 1}) :=
  preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} (forget Ab.{u + 1})

/-- **Stalks at geometric points detect isomorphisms of abelian étale sheaves.** A morphism of
abelian sheaves on the small étale site of a scheme `X` is an isomorphism if and only if the
induced map on the stalk at every geometric point of `X` is an isomorphism.

Necessity is functoriality of the stalk. For sufficiency the morphism is composed with the
forgetful functor to sheaves of sets, where the geometric points indexed by the points of `X`
with the algebraic closures of their residue fields are jointly surjective and hence detect
isomorphisms; the forgetful functor commutes with taking fibres at a point of a site, so the
hypothesis transports, and it reflects isomorphisms, so the conclusion comes back. -/
@[sga "4½ Arcata 2.3.2" "special case"]
public theorem isIso_iff_forall_isIso_smallEtaleStalkAb {X : Scheme.{u}}
    {F G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (φ : F ⟶ G) :
    IsIso φ ↔ ∀ x : GeometricPoint X, IsIso ((smallEtaleStalkAb x.hom).map φ) := by
  refine ⟨fun _ _ ↦ inferInstance, fun hstalk ↦ ?_⟩
  rw [← isIso_iff_of_reflects_iso _ (sheafCompose (smallEtaleTopology X) (forget Ab.{u + 1}))]
  refine isIso_of_geometricStalk_family.{0, u} (fun x : X ↦ X.algClosedPointHom x) ?_ _ ?_
  · ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨x, default, X.algClosedPointHom_apply x _⟩
  · intro x
    have hiso : IsIso ((smallEtaleStalkAb (X.algClosedPointHom x)).map φ) :=
      hstalk (X.algClosedPoint x)
    refine (NatIso.isIso_map_iff
      ((pointSmallEtale (X.algClosedPointHom x)).sheafFiberCompIso (forget Ab.{u + 1}))
      φ).2 ?_
    exact inferInstanceAs (IsIso ((forget Ab.{u + 1}).map
      ((smallEtaleStalkAb (X.algClosedPointHom x)).map φ)))

/-- **Stacks 03Q1 for abelian coefficients on the small étale site.** For a morphism of schemes
`f : X ⟶ S` and a geometric point `x` of `X`, the stalk at `x` of the inverse image `f⁻¹ G` of an
abelian sheaf on the small étale site of `S` is the stalk of `G` at the image geometric point
`x ≫ f`, naturally in `G`.

Base change along `f` carries an étale `S`-scheme `U` to `U ×_S X`, and a lift of `x` to `U ×_S X`
is the same thing as a lift of `x ≫ f` to `U`, which is the fibre identification
`Stacks.EtaleCohomology.pointSmallEtaleBaseChangeFiberIso`. Under that identification the point
`x` pulled back along base change is the point `x ≫ f`, so the comparison is the fibre of an
inverse-image point followed by the invariance of the elements-colimit computing a stalk under an
isomorphism of fibre functors. -/
@[sga "4 VIII 3.4" "abelian sheaves", sga "4½ Arcata 2.3.3"]
public def smallEtalePullbackStalkAbIso {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u}
    [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    smallEtalePullbackAb f ⋙ smallEtaleStalkAb x ≅ smallEtaleStalkAb (x ≫ f) := by
  let u := smallEtaleBaseChange f
  let p := pointSmallEtale (x ≫ f)
  let q := pointSmallEtale x
  let eFiber : p.fiber ≅ u ⋙ q.fiber := pointSmallEtaleBaseChangeFiberIso f x
  let eElements := CategoryOfElements.equivalenceOfNatIso eFiber
  haveI : InitiallySmall.{u} (u ⋙ q.fiber).Elements := by
    have hModel : Functor.Initial (fromInitialModel.{u} p.fiber.Elements) := inferInstance
    have hEquiv : eElements.functor.IsEquivalence := eElements.isEquivalence_functor
    exact ⟨_, inferInstance, fromInitialModel.{u} p.fiber.Elements ⋙ eElements.functor,
      @Functor.initial_comp_equivalence _ _ _ _ _ _
        (fromInitialModel.{u} p.fiber.Elements) eElements.functor hModel hEquiv⟩
  letI : HasColimitsOfShape (u ⋙ q.fiber).Elementsᵒᵖ Ab.{u + 1} :=
    hasColimitsOfShape_of_finallySmall _ _
  exact (q.sheafFiberComapIso u (CoverPreserving.of_isContinuous u _ _) Ab.{u + 1}).symm ≪≫
    (CategoryOfElements.sheafColimIsoOfNatIsoOfCoefficients
      (A := Ab.{u + 1}) (smallEtaleTopology S) eFiber).symm

section BaseChangeSquare

variable {X Y S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T)
  (w : h ≫ f = e ≫ g) (q : ℕ) (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})

/-- The map on stalks which the base change map on higher direct images induces at a geometric
point `x` of `X`, read as a map out of the stalk at the image geometric point: the canonical map
`(R^q g_* F)_{f(x)} ⟶ (R^q h_* e⁻¹ F)_x`, the stalk of
`Stacks.EtaleCohomology.higherBaseChangeMapAb` at `x` precomposed with the identification
`Stacks.EtaleCohomology.smallEtalePullbackStalkAbIso` of the stalk of `f⁻¹ R^q g_* F` at `x` with
the stalk of `R^q g_* F` at `f(x)`. -/
public def higherBaseChangeMapAbStalk (x : GeometricPoint X) :
    (smallEtaleStalkAb (x.hom ≫ f)).obj
        (((smallEtalePushforwardAb g).rightDerived q).obj F) ⟶
      (smallEtaleStalkAb x.hom).obj
        ((smallEtalePullbackAb e ⋙ (smallEtalePushforwardAb h).rightDerived q).obj F) :=
  ((smallEtalePullbackStalkAbIso f x.hom).app
      (((smallEtalePushforwardAb g).rightDerived q).obj F)).inv ≫
    (smallEtaleStalkAb x.hom).map ((higherBaseChangeMapAb f g h e w q).app F)

/-- The map `higherBaseChangeMapAbStalk` is invertible exactly when the stalk at `x` of the base
change map on higher direct images is: the two differ by the identification of the stalk of
`f⁻¹ R^q g_* F` at `x` with the stalk of `R^q g_* F` at `f(x)`, which is an isomorphism. -/
public theorem isIso_higherBaseChangeMapAbStalk_iff (x : GeometricPoint X) :
    IsIso (higherBaseChangeMapAbStalk f g h e w q F x) ↔
      IsIso ((smallEtaleStalkAb x.hom).map ((higherBaseChangeMapAb f g h e w q).app F)) :=
  isIso_comp_left_iff _ _

end BaseChangeSquare

/-- **Stacks 0EZU.** Consider a cartesian diagram of schemes
```
X  ←-h-  Y
|f       |e
S  ←-g-  T
```
with `g : T ⟶ S` quasi-compact and quasi-separated, let `F` be an abelian sheaf on the small
étale site of `T`, and let `q ≥ 0`. Then the base change map on higher direct images
`f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism if and only if its map on the stalk at every
geometric point of `X` is an isomorphism. -/
@[stacks 0EZU "base change on higher direct images is an isomorphism iff it is on every stalk"]
public theorem isIso_higherBaseChangeMapAb_app_iff_forall_isIso_stalk
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (sq : IsPullback h e f g) [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (q : ℕ) :
    (∀ x : GeometricPoint X,
        IsIso ((smallEtaleStalkAb x.hom).map ((higherBaseChangeMapAb f g h e sq.w q).app F))) ↔
      IsIso ((higherBaseChangeMapAb f g h e sq.w q).app F) :=
  (isIso_iff_forall_isIso_smallEtaleStalkAb _).symm

/-- **Stacks 0EZU**, with the condition at a geometric point `x̄` of `X` phrased as invertibility
of the canonical map `(R^q g_* F)_{s̄} ⟶ (R^q h_* e⁻¹ F)_{x̄}` out of the stalk at the image
geometric point `s̄ = f(x̄)`. In the situation of
`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_iff_forall_isIso_stalk`, the base change
map `f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism if and only if that map is an isomorphism
for every geometric point `x̄` of `X`.

This is the source's equivalence with each of its two cohomology groups replaced by the stalk
which it computes; the identification of the stalks with cohomology over the fibre products
`Spec(𝒪^{sh}_{S,s̄}) ×_S T` and `Spec(𝒪^{sh}_{X,x̄}) ×_S T` is not available in the library. -/
@[stacks 0EZU "the condition at a geometric point, as a map out of the stalk at its image"]
public theorem isIso_higherBaseChangeMapAb_app_iff_forall_isIso_stalkMap
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (sq : IsPullback h e f g) [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (q : ℕ) :
    (∀ x : GeometricPoint X,
        IsIso (higherBaseChangeMapAbStalk f g h e sq.w q F x)) ↔
      IsIso ((higherBaseChangeMapAb f g h e sq.w q).app F) :=
  (forall_congr' fun x ↦ isIso_higherBaseChangeMapAbStalk_iff f g h e sq.w q F x).trans
    (isIso_higherBaseChangeMapAb_app_iff_forall_isIso_stalk f h e g sq F q)

end Stacks.EtaleCohomology

end
