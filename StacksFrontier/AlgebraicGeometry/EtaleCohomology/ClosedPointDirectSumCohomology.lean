module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DirectSumsOfEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianSmallEtaleVanishing
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.GeometricPointStalk
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteSheafCohomology

/-!
# Étale cohomology of a direct sum of constant sheaves at the closed points

Let `X` be a quasi-compact, quasi-separated scheme locally of finite type over an algebraically
closed field `k`, and for a closed point `x` of `X` let `i_x : Spec κ(x) ⟶ X` be its inclusion.
Then `H^q_étale(X, ⨁_{x ∈ X₀} (i_x)_* ℤ) = 0` for every `q ≥ 1`, the sum being over the closed
points of `X`.

Three steps. Étale cohomology commutes with the direct sum, so only one summand has to be
treated. The inclusion of a closed point is a closed immersion, hence integral, so direct image
along it changes neither the global cohomology nor its vanishing. And the residue field at a
closed point of a scheme locally of finite type over an algebraically closed field is again
algebraically closed, hence a strictly henselian local ring, so the cohomology of any abelian
sheaf on `Spec κ(x)` vanishes in positive degree.

## Main results

* `StrictlyHenselianLocalRing.of_isSepClosed` — **a separably closed field is a strictly
  henselian local ring.**
* `Stacks.EtaleCohomology.smallEtalePushforwardAb_preservesInjectiveObjects` — direct image of
  abelian sheaves on small étale sites preserves injective objects.
* `Stacks.EtaleCohomology.sheafHSmallEtalePushforwardAddEquiv` — **for an integral morphism
  `f : X ⟶ Y`, the global étale cohomology of `F` and of `f_* F` agree.**
* `Stacks.EtaleCohomology.subsingleton_sheafH_closedPointPushforward` — the positive-degree
  cohomology of `(i_x)_* F` vanishes for every abelian sheaf `F` on `Spec κ(x)`.
* `Stacks.EtaleCohomology.subsingleton_sheafH_sigma_closedPointPushforward_smallEtale` —
  **Stacks 03RL.**

## Implementation notes

The cohomological input for the direct image step is
`Stacks.Cohomology.BiggerSite.sheafHAddEquiv`, which needs the restriction functor along the
site morphism to be right exact and to preserve injective objects. Right exactness is Tag 04C2
(`Stacks.EtaleCohomology.smallEtalePushforwardAb_exact_of_isIntegralHom`) and holds because the
morphism is integral; preservation of injectives holds for every morphism, being the adjoint
form of exactness of inverse image. Both are supplied in the unfolded
`Functor.sheafPushforwardContinuous` spelling, because `smallEtalePushforwardAb` is not
reducible and the instances are consumed through the abstract statement. The two terminal
objects are matched on the nose rather than up to isomorphism by taking the one on the source
site to *be* the base change of the one on the target site, which is terminal by
`Stacks.EtaleCohomology.isTerminalSmallEtaleBaseChangeObj`.

Coefficients are `AddCommGrpCat.{u + 1}` for `X : Scheme.{u}`, the convention of the whole
`Stacks.EtaleCohomology` namespace, and the `Ext` universe is `u + 1` as well. The latter is not
an assumption: abelian sheaves on the small étale site of `X` form a Grothendieck abelian
category relative to `u + 1`, which is recorded as a local instance here so that
`CategoryTheory.Sheaf.H` elaborates with no `HasExt` hypothesis. It is deliberately local, since
Mathlib keeps `HasExt` instances scarce.

Existence of the coproduct is not reachable by instance search on this site, the coefficient
universe of `AlgebraicGeometry.Scheme.hasColimitsOfShape_sheaf_smallEtaleTopology` being
undetermined by its arguments. Here it is pinned to `u + 1` and registered as a local instance,
at both the shape level and the single-diagram level, which is what the scoped namespace
`AlgebraicGeometry.Scheme.SmallEtaleColimits` does for a free coefficient universe.

## References

* [Stacks Project, Tag 03RL](https://stacks.math.columbia.edu/tag/03RL)
* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/-- **A separably closed field is a strictly henselian local ring.** A field is a henselian
local ring, and its residue field is the field itself: the residue map of a field is a ring
homomorphism out of a field onto a nontrivial ring, hence bijective. -/
public theorem StrictlyHenselianLocalRing.of_isSepClosed (K : Type*) [Field K] [IsSepClosed K] :
    StrictlyHenselianLocalRing K :=
  let e : IsLocalRing.ResidueField K ≃+* K :=
    (RingEquiv.ofBijective (IsLocalRing.residue K)
      ⟨(IsLocalRing.residue K).injective, Ideal.Quotient.mk_surjective⟩).symm
  let : IsSepClosed (IsLocalRing.ResidueField K) := IsSepClosed.of_ringEquiv e
  ⟨⟩

namespace Stacks.EtaleCohomology

/-- Abelian sheaves on the small étale site of `X : Scheme.{u}` with coefficients in
`AddCommGrpCat.{u + 1}` form a Grothendieck abelian category relative to `u + 1`: the site has
an essentially small underlying category in that universe. This is what makes `HasExt.{u + 1}`
available, and so `CategoryTheory.Sheaf.H` elaborate, without any hypothesis. -/
local instance isGrothendieckAbelian_sheaf_smallEtaleTopology (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (smallEtaleTopology X) Ab.{u + 1}) :=
  letI : EssentiallySmall.{u + 1} X.Etale := inferInstance
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} (smallEtaleTopology X) Ab.{u + 1}

/-- Abelian sheaves on the small étale site of `X : Scheme.{u}` with coefficients in
`AddCommGrpCat.{u + 1}` have coproducts indexed by a `Type u`. This is
`AlgebraicGeometry.Scheme.hasColimitsOfShape_sheaf_smallEtaleTopology` with the coefficient
universe pinned, which is what instance search cannot guess. -/
local instance (priority := 10000) hasColimitsOfShape_discrete_sheaf_smallEtaleTopology
    (X : Scheme.{u}) (α : Type u) :
    HasColimitsOfShape (Discrete α) (Sheaf (smallEtaleTopology X) Ab.{u + 1}) :=
  hasColimitsOfShape_sheaf_smallEtaleTopology.{u, u + 1} X (Discrete α)

/-- A single `Type u`-indexed family of abelian sheaves on the small étale site has a
coproduct. Stated separately from the shape-level instance because instance search reaches
`CategoryTheory.Limits.HasColimit` first. -/
local instance (priority := 10000) hasColimit_discrete_sheaf_smallEtaleTopology
    {X : Scheme.{u}} {α : Type u}
    (F : Discrete α ⥤ Sheaf (smallEtaleTopology X) Ab.{u + 1}) : HasColimit F :=
  hasColimit_sheaf_smallEtaleTopology.{u, u + 1} X F

/-- **Direct image of abelian sheaves on the small étale sites preserves injective objects.**
It is the right adjoint of inverse image, which is exact and in particular preserves
monomorphisms. -/
public instance smallEtalePushforwardAb_preservesInjectiveObjects {X Y : Scheme.{u}}
    (f : X ⟶ Y) : (smallEtalePushforwardAb f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (smallEtaleAdjunctionAb f)

/-- **Direct image along an integral morphism does not change global étale cohomology.** For
`f : X ⟶ Y` integral and `F` an abelian sheaf on the small étale site of `X`, the degree-`q`
cohomology of `F` over `X` and of `f_* F` over `Y` are the same group. -/
public def sheafHSmallEtalePushforwardAddEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (q : ℕ) :
    Sheaf.H.{u + 1, u + 1} F q ≃+
      Sheaf.H.{u + 1, u + 1} ((smallEtalePushforwardAb f).obj F) q :=
  letI : PreservesFiniteColimits ((smallEtaleBaseChange f).sheafPushforwardContinuous
      Ab.{u + 1} (smallEtaleTopology Y) (smallEtaleTopology X)) :=
    ((exactFunctor_iff _).mp (smallEtalePushforwardAb_exact_of_isIntegralHom f)).2
  letI : ((smallEtaleBaseChange f).sheafPushforwardContinuous Ab.{u + 1}
      (smallEtaleTopology Y) (smallEtaleTopology X)).PreservesInjectiveObjects :=
    smallEtalePushforwardAb_preservesInjectiveObjects f
  Stacks.Cohomology.BiggerSite.sheafHAddEquiv (smallEtaleTopology Y) (smallEtaleTopology X)
    (smallEtaleBaseChange f) terminalIsTerminal
    (isTerminalSmallEtaleBaseChangeObj f terminalIsTerminal) rfl F q

/-- **The positive-degree étale cohomology of a sheaf pushed forward from a closed point
vanishes**, for a scheme locally of finite type over an algebraically closed field. The
inclusion of a closed point is a closed immersion, hence integral, so the cohomology is that of
the sheaf itself over `Spec κ(x)`; and `κ(x)` is algebraically closed, hence a strictly
henselian local ring, so that cohomology vanishes by Tag 03QO. -/
public theorem subsingleton_sheafH_closedPointPushforward {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g] (x : X)
    (hx : IsClosed {x}) (F : Sheaf (smallEtaleTopology (Spec (X.residueField x))) Ab.{u + 1})
    (q : ℕ) (hq : 1 ≤ q) :
    Subsingleton
      (Sheaf.H.{u + 1, u + 1} ((smallEtalePushforwardAb (X.fromSpecResidueField x)).obj F) q) := by
  let : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  let : IsIntegralHom (X.fromSpecResidueField x) := inferInstance
  let : IsAlgClosed (ToType (X.residueField x)) :=
    IsAlgClosed.of_ringEquiv k _ (residueFieldIsoBase g x hx).commRingCatIsoToRingEquiv.symm
  let hsh : StrictlyHenselianLocalRing (ToType (X.residueField x)) :=
    StrictlyHenselianLocalRing.of_isSepClosed _
  have : Subsingleton (Sheaf.H.{u + 1, u + 1} F q) :=
    -- `hsh` is passed by hand: its `CommRing` instance and the one instance search finds
    -- for `ToType (X.residueField x)` agree only after unfolding
    -- `AlgebraicGeometry.Scheme.residueField`, which instance resolution will not do.
    @Stacks.StrictlyHenselian.subsingleton_etaleCohomology_smallEtaleTopology
      (ToType (X.residueField x)) _ hsh _ F q hq
  exact Equiv.subsingleton
    (sheafHSmallEtalePushforwardAddEquiv (X.fromSpecResidueField x) F q).symm.toEquiv

/-- **Stacks Project, Tag 03RL.** Let `X` be a quasi-compact, quasi-separated scheme locally of
finite type over an algebraically closed field — a smooth curve over an algebraically closed
field, for instance. For every `q ≥ 1` the degree-`q` étale cohomology of
`⨁_{x ∈ X₀} (i_x)_* ℤ` vanishes, the sum being over the closed points `X₀` of `X` and `i_x` the
inclusion of a closed point. -/
@[stacks 03RL "vanishing of the positive-degree étale cohomology of the direct sum over the
closed points of the pushforwards of the constant integer sheaf"]
public theorem subsingleton_sheafH_sigma_closedPointPushforward_smallEtale {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g]
    [CompactSpace X] [QuasiSeparatedSpace X] (q : ℕ) (hq : 1 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      (∐ fun x : closedPoints X ↦
        (smallEtalePushforwardAb (X.fromSpecResidueField x.1)).obj
          ((constantSheaf (smallEtaleTopology (Spec (X.residueField x.1))) Ab.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) q) :=
  subsingleton_sheafH_sigma_smallEtale_small.{u + 1} X q _ fun x ↦
    subsingleton_sheafH_closedPointPushforward g x.1 x.2 _ q hq

end Stacks.EtaleCohomology

end
