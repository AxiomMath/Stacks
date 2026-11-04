module

public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToAlgebraicSpace
public import StacksFrontier.RingTheory.CompleteLocalRing.Noetherian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The quotient system of a spectrum in the site, and the `𝔪`-adic system of a complete local ring

Let `R` be a topological commutative ring whose ordinary spectrum `Spec R` is an object of a big
fppf site `B` over a scheme `S`, and let `p : Spec R ⟶ S`. The quotient maps `R ⟶ R ⧸ J`, over the
weak ideals of definition `J` of `R`, then assemble into an
`AlgebraicGeometry.FormalSpace.QuotientSystem`: each `Spec (R ⧸ J)` is a closed subscheme of
`Spec R`, hence again an object of `B`, and it is given the structure morphism `p` composed with
the quotient map. So the formal spectrum `Spf R = colim_J Spec (R ⧸ J)` of **Stacks 0AIF** exists
over `S` for every such ring.

When the topology of `R` is the `I`-adic topology of an ideal `I`, the positive powers of `I` are
weak ideals of definition and every weak ideal of definition contains one of them, so the powers
of `I` and the weak ideals of definition are mutually cofinal. Taking `I` to be the maximal ideal
`𝔪` of a Noetherian complete local ring puts us in the situation of **Stacks 0AQH**, whose
theorems take a quotient system together with exactly those two cofinality conditions; the
injectivity half of that tag is restated here with all of its hypotheses on the system
discharged.

## Main definitions

* `AlgebraicGeometry.FormalSpace.quotientSystemOfSpec`: the quotient system of a topological ring
  whose spectrum lies in the site, over a base through a morphism `Spec R ⟶ S`.
* `AlgebraicGeometry.FormalSpace.maximalAdicTopology`: the `𝔪`-adic topology of a Noetherian
  complete local ring.

## Main results

* `AlgebraicGeometry.FormalSpace.isWeakIdealOfDefinition_pow_of_isAdic`: a positive power of an
  ideal defining the topology is a weak ideal of definition.
* `AlgebraicGeometry.FormalSpace.exists_pow_le_of_isWeakIdealOfDefinition` and
  `AlgebraicGeometry.FormalSpace.exists_weakIdealOfDefinition_le_pow`: the powers of `I` and the
  weak ideals of definition are mutually cofinal.
* `AlgebraicGeometry.FormalSpace.injective_map_into_algebraicSpace_of_isAdic` and
  `AlgebraicGeometry.FormalSpace.injective_map_into_algebraicSpace_maximalAdic`: the injectivity
  half of **Stacks 0AQH** for a Noetherian complete local ring with its `𝔪`-adic topology, with
  no quotient system and no cofinality condition left as a hypothesis.
* `AlgebraicGeometry.FormalSpace.surjective_map_into_algebraicSpace_of_isAdic`: the surjectivity
  half of **Stacks 0AQH** for the same ring, with the same hypotheses discharged.
* `AlgebraicGeometry.FormalSpace.nonempty_obj_of_forall_nonempty_obj_quotient`: the surjectivity
  half in the shape its consumers want — a subterminal algebraic space with a point over every
  `Spec (R ⧸ J)` has a point over `Spec R`.

## Implementation notes

Building the quotient system itself uses no property of the topology, and neither the Noetherian
hypothesis nor completeness nor locality: a structure morphism `Spec R ⟶ S` and the closed
immersions `Spec (R ⧸ J) ↪ Spec R` are all it takes. What the `𝔪`-adic topology supplies, and
what the theorems built on it genuinely need, are the two cofinality conditions; those are the
content here.

The topology is pinned by the propositional hypothesis `IsAdic I` rather than by substituting
`Ideal.adicTopology` for the `TopologicalSpace` instance, so that the statements apply to a ring
already carrying an adic topology. `AlgebraicGeometry.FormalSpace.maximalAdicTopology` supplies
the instance when none is given, and there `IsAdic` holds by definition.

Weak admissibility of the adic topology is *not* established here: it additionally requires that
the uniform space of `R` be complete and Hausdorff, which for a Noetherian complete local ring is
the passage from `IsAdicComplete 𝔪 R` to completeness of the uniformity of the `𝔪`-adic topology.
That passage, and with it the affine-formal-algebraic-space property of **Stacks 0AIF** and the
bijection of **Stacks 0AQG** for a Noetherian complete local ring, is in
`StacksFrontier.AlgebraicGeometry.FormalSpace.WeaklyAdmissibleCompleteLocal`.
`AlgebraicGeometry.FormalSpace.QuotientSystem.HasLargeSite` remains uninstantiated, being a
condition on the site rather than on the ring.

The nonemptiness form of surjectivity needs the points over the quotient stages to be
*compatible*, which is what makes them a point of the formal spectrum; the hypothesis that every
value of the algebraic space is a subsingleton supplies that for free, and is exactly what holds
for the subterminal functors the statement is used on. Its stage hypothesis is stated for every
ideal containing a power of the maximal ideal rather than for the powers themselves, because the
weak ideals of definition of the `𝔪`-adic topology are precisely such ideals and a consumer that
can produce a point over one quotient can produce it over all of them.

## References

* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
* [Stacks Project, Tag 0AQH](https://stacks.math.columbia.edu/tag/0AQH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Cofinality

variable {R : Type u} [CommRing R]

/-- The powers of an ideal are open for its own adic topology. -/
@[ega "0 7.1.9" "partial"]
private theorem isOpen_pow_adicTopology (I : Ideal R) (n : ℕ) :
    @IsOpen R I.adicTopology ((I ^ n : Ideal R) : Set R) := by
  let := I.adicTopology
  exact (I.openAddSubgroup n).isOpen'

variable [TopologicalSpace R] {I : Ideal R}

/-- Every power of an ideal defining the topology is open. -/
@[ega "0 7.1.9" "partial"]
public theorem isOpen_pow_of_isAdic (h : IsAdic I) (n : ℕ) :
    IsOpen ((I ^ n : Ideal R) : Set R) :=
  h ▸ isOpen_pow_adicTopology I n

/-- Every element of an ideal defining the topology is topologically nilpotent: its `m`-th
power lies in `Iᵐ`, and the powers of `I` are a neighbourhood basis of zero. -/
@[ega "0 7.1.4" "(ii)"]
public theorem isTopologicallyNilpotent_of_isAdic (h : IsAdic I) {x : R} (hx : x ∈ I) :
    IsTopologicallyNilpotent x := by
  subst h
  refine I.hasBasis_nhds_zero_adic.tendsto_right_iff.mpr fun n _ => ?_
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  exact Ideal.pow_le_pow_right hm (Ideal.pow_mem_pow hx m)

/-- A positive power of an ideal defining the topology is a weak ideal of definition. -/
public theorem isWeakIdealOfDefinition_pow_of_isAdic (h : IsAdic I) {n : ℕ} (hn : n ≠ 0) :
    TopologicalRing.IsWeakIdealOfDefinition (I ^ n) :=
  ⟨isOpen_pow_of_isAdic h n, fun _ hx =>
    isTopologicallyNilpotent_of_isAdic h (Ideal.pow_le_self hn hx)⟩

/-- An open ideal of a ring with the `I`-adic topology contains a power of `I`. -/
public theorem exists_pow_le_of_isOpen (h : IsAdic I) {J : Ideal R}
    (hJ : IsOpen (J : Set R)) : ∃ n : ℕ, I ^ n ≤ J := by
  have hmem : (J : Set R) ∈ nhds (0 : R) := hJ.mem_nhds J.zero_mem
  subst h
  obtain ⟨n, -, hn⟩ := I.hasBasis_nhds_zero_adic.mem_iff.mp hmem
  exact ⟨n, fun _ hx => hn hx⟩

/-- Every weak ideal of definition of a ring with the `I`-adic topology contains a power of
`I`: this is the first cofinality condition. -/
@[ega "I 10.12.1" "Affine comparison"]
public theorem exists_pow_le_of_isWeakIdealOfDefinition (h : IsAdic I)
    (J : { K : Ideal R // TopologicalRing.IsWeakIdealOfDefinition K }) :
    ∃ n : ℕ, I ^ n ≤ J.1 :=
  exists_pow_le_of_isOpen h J.2.1

/-- Every power of an ideal defining the topology contains a weak ideal of definition: this is
the second cofinality condition. -/
public theorem exists_weakIdealOfDefinition_le_pow (h : IsAdic I) (n : ℕ) :
    ∃ J : { K : Ideal R // TopologicalRing.IsWeakIdealOfDefinition K }, J.1 ≤ I ^ n :=
  ⟨⟨I ^ max n 1, isWeakIdealOfDefinition_pow_of_isAdic h
      (Nat.one_le_iff_ne_zero.mp (le_max_right n 1))⟩,
    Ideal.pow_le_pow_right (le_max_left n 1)⟩

end Cofinality

section System

variable {R : Type u} [CommRing R] [TopologicalSpace R]

/-- The quotient system carried by a topological ring whose ordinary spectrum is an object of
the site, equipped with a structure morphism to the base: the quotient of `R` by a weak ideal
of definition is a closed subscheme of `Spec R`, hence again an object of the site, and its
structure morphism is the given one composed with the quotient map. -/
public def quotientSystemOfSpec (hRS : B.Contains (Spec (.of R)))
    (p : Spec (.of R) ⟶ S) : QuotientSystem B S hS R where
  inSite J := by
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    exact Scheme.size_lt_of_isClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1))) hRS
  overS J := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ p
  compatible _ _ hJL := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Ideal.Quotient.factor_comp_mk]

/-- The structure morphisms of `AlgebraicGeometry.FormalSpace.quotientSystemOfSpec` are the
quotient maps followed by the given morphism `Spec R ⟶ S`. -/
public theorem quotientSystemOfSpec_overS (hRS : B.Contains (Spec (.of R)))
    (p : Spec (.of R) ⟶ S)
    (J : { K : Ideal R // TopologicalRing.IsWeakIdealOfDefinition K }) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ p =
      (quotientSystemOfSpec (hS := hS) hRS p).overS J :=
  rfl

/-- **The injectivity half of Stacks 0AQH** for a Noetherian complete local ring carrying its
`𝔪`-adic topology: restriction along the canonical map `Spf R ⟶ Spec R` is injective on
morphisms to an algebraic space over `S`. -/
public theorem injective_map_into_algebraicSpace_of_isAdic
    (hR : IsNoetherianCompleteLocalRing R)
    (hadic : IsAdic (@IsLocalRing.maximalIdeal R _ hR.isLocal))
    (hRS : B.Contains (Spec (.of R))) (p : Spec (.of R) ⟶ S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X) :
    Function.Injective (fun f :
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (specOver hRS p)) ⟶ upliftedSheaf X hX =>
      formalSpectrumToSpec (quotientSystemOfSpec hRS p) hRS p
        (quotientSystemOfSpec_overS hRS p) ≫ f) :=
  injective_map_into_algebraicSpace hR (quotientSystemOfSpec hRS p)
    (exists_weakIdealOfDefinition_le_pow hadic) hRS p
    (quotientSystemOfSpec_overS hRS p) X hX

/-- **The surjectivity half of Stacks 0AQH** for a Noetherian complete local ring carrying its
`𝔪`-adic topology: every morphism from the formal spectrum to an algebraic space over `S` is the
restriction of a morphism from the ordinary spectrum. -/
public theorem surjective_map_into_algebraicSpace_of_isAdic
    (hR : IsNoetherianCompleteLocalRing R)
    (hadic : IsAdic (@IsLocalRing.maximalIdeal R _ hR.isLocal))
    (hRS : B.Contains (Spec (.of R))) (p : Spec (.of R) ⟶ S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X) :
    Function.Surjective (fun f :
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (specOver hRS p)) ⟶ upliftedSheaf X hX =>
      formalSpectrumToSpec (quotientSystemOfSpec hRS p) hRS p
        (quotientSystemOfSpec_overS hRS p) ≫ f) :=
  surjective_map_into_algebraicSpace hR (quotientSystemOfSpec hRS p)
    (exists_pow_le_of_isWeakIdealOfDefinition hadic)
    (exists_weakIdealOfDefinition_le_pow hadic) hRS p
    (quotientSystemOfSpec_overS hRS p) X hX

end System

section Maximal

attribute [local instance] sheaf_hasColimits

variable {R : Type u} [CommRing R]

/-- The `𝔪`-adic topology of a Noetherian complete local ring. -/
@[instance_reducible]
public def maximalAdicTopology (hR : IsNoetherianCompleteLocalRing R) : TopologicalSpace R :=
  (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology

/-- The topology of `AlgebraicGeometry.FormalSpace.maximalAdicTopology` is the `𝔪`-adic one. -/
public theorem isAdic_maximalAdicTopology (hR : IsNoetherianCompleteLocalRing R) :
    @IsAdic R _ (maximalAdicTopology hR) (@IsLocalRing.maximalIdeal R _ hR.isLocal) :=
  rfl

/-- **The injectivity half of Stacks 0AQH** for a Noetherian complete local ring, with no
topology, quotient system or cofinality condition assumed: the `𝔪`-adic topology and its
quotient system are supplied by the construction. -/
public theorem injective_map_into_algebraicSpace_maximalAdic
    (hR : IsNoetherianCompleteLocalRing R) (hRS : B.Contains (Spec (.of R)))
    (p : Spec (.of R) ⟶ S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X) :
    Function.Injective (fun f :
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (specOver hRS p)) ⟶ upliftedSheaf X hX =>
      @formalSpectrumToSpec B S hS R _ (maximalAdicTopology hR)
        (@quotientSystemOfSpec B S hS R _ (maximalAdicTopology hR) hRS p) hRS p
        (@quotientSystemOfSpec_overS B S hS R _ (maximalAdicTopology hR) hRS p) ≫ f) :=
  @injective_map_into_algebraicSpace_of_isAdic B S hS R _ (maximalAdicTopology hR) hR
    (isAdic_maximalAdicTopology hR) hRS p X hX

/-- **An algebraic space with a point over every infinitesimal quotient of a Noetherian complete
local ring has a point over the ring itself**, provided each of its values is a subsingleton, so
that those points are automatically compatible.  This is the surjectivity half of
**Stacks 0AQH** read on points: `lim_n X(R ⧸ 𝔪ⁿ) ≠ ∅` forces `X(R) ≠ ∅`.

Nothing in the statement mentions a topology or a quotient system: the `𝔪`-adic topology and its
quotient system are supplied by the proof, and the stage hypothesis asks for a point over
`Spec (R ⧸ J)` for every ideal `J` containing a power of the maximal ideal. -/
public theorem nonempty_obj_of_forall_nonempty_obj_quotient
    (hR : IsNoetherianCompleteLocalRing R) (hRS : B.Contains (Spec (.of R)))
    (p : Spec (.of R) ⟶ S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hsub : ∀ T, Subsingleton (X.obj T))
    (hstage : ∀ (n : ℕ) (J : Ideal R),
      (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J →
      ∀ hJ : B.Contains (Spec (.of (R ⧸ J))),
        Nonempty (X.obj (Opposite.op (siteObject B S hS hJ
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ p))))) :
    Nonempty (X.obj (Opposite.op (siteObject B S hS hRS p))) := by
  let top := maximalAdicTopology hR
  let D : QuotientSystem B S hS R := quotientSystemOfSpec hRS p
  let F := upliftedSheaf X hX
  -- every value of the uplifted sheaf is a subsingleton, so morphisms into it are unique
  have hhom : ∀ {G : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (a b : G ⟶ F),
      a = b := fun a b => Sheaf.hom_ext <| by
    ext T s
    let := hsub T
    exact Subsingleton.elim (α := ULift _) _ _
  -- a point over every quotient stage, the weak ideals of definition being the ideals above a
  -- power of `𝔪`
  have hpt : ∀ J : { K : Ideal R // TopologicalRing.IsWeakIdealOfDefinition K },
      Nonempty (F.obj.obj (Opposite.op ((BigAffineFppf.inclusion B S hS).obj (D.stage J)))) := by
    intro J
    obtain ⟨n, hn⟩ := exists_pow_le_of_isWeakIdealOfDefinition
      (isAdic_maximalAdicTopology hR) J
    exact (hstage n J.1 hn (D.inSite J)).map ULift.up
  -- they assemble into a morphism out of the formal spectrum, which is a restriction
  let c : Limits.Cocone (formalSpectrumDiagram D) :=
    { pt := F
      ι :=
        { app := fun J => (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
            (hpt (OrderDual.ofDual J)).some
          naturality := fun _ _ _ => hhom _ _ } }
  obtain ⟨g, -⟩ := surjective_map_into_algebraicSpace_of_isAdic hR
    (isAdic_maximalAdicTopology hR) hRS p X hX (Limits.colimit.desc _ c)
  exact ⟨(Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down⟩

end Maximal

end AlgebraicGeometry.FormalSpace

end
