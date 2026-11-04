module

public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.LocalPrincipality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibreOrdLocallyIntegral
public import StacksFrontier.AlgebraicGeometry.Properties.NormalStalkDvr
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkClosedPoint

/-!
# Every rational function on an étale `X`-scheme comes from the generic fibre

Let `X` be an integral scheme with generic point `η` and function field `K`, let
`j : Spec K ⟶ X` be the inclusion of the generic point, and let `g : U ⟶ X` be étale with `U`
integral. `Stacks.EtaleCohomology.genericFibreToFunctionField g` reads a global function on the
generic fibre `U ×_X Spec K` as a rational function on `U`, and that is how the second map of the
fundamental exact sequence of Stacks 03RI takes orders of vanishing on `U` of a section of
`j_* 𝐆_{m,K}` over `U`.

That comparison is an **isomorphism**. The generic fibre of an étale morphism from an integral
scheme is a one-point scheme
(`Stacks.EtaleCohomology.subsingleton_pullback_genericPointInclusion`), so the whole space is the
only open neighbourhood of its point and the colimit computing the stalk there is attained at
`⊤`: the germ of the global sections is an isomorphism. The remaining two factors of the
comparison are isomorphisms already — the stalk map of the projection by
`Stacks.EtaleCohomology.isIso_stalkMap_pullback_fst_genericPointInclusion`, and the transport
along the equality of points by `TopCat.Presheaf.stalkCongr`.

Consequently *every* rational function on `U`, invertible or not, is a global function on the
generic fibre, and every invertible one is an invertible global function on the generic fibre.
Combined with the local principality of divisors
(`AlgebraicGeometry.Scheme.exists_ord_eq_and_forall_ord_eq_zero_of_isDiscreteValuationRing`) this
produces, from a prescribed order of vanishing at a codimension-one point of `U`, a *section of
`j_* 𝐆_{m,K}` over `U`* with that order there and order zero at every other point of a
neighbourhood — the local input to the right-hand exactness of the sequence of Stacks 03RI, stated
on the sheaf whose sections the sequence actually uses.

## Main results

* `TopCat.Presheaf.isIso_Γgerm_of_subsingleton`: **the germ of the global sections of a presheaf
  on a one-point space is an isomorphism.**
* `Stacks.EtaleCohomology.isIso_genericFibreToFunctionField`: **the comparison with the function
  field is an isomorphism** for an étale morphism of integral schemes.
* `Stacks.EtaleCohomology.surjective_genericFibreToFunctionField`,
  `Stacks.EtaleCohomology.surjective_units_map_genericFibreToFunctionField`: every rational
  function on `U`, and every invertible one, comes from the generic fibre.
* `Stacks.EtaleCohomology.exists_genericFibreOrd_eq_and_forall_ord_eq_zero`: **a section of
  `j_* 𝐆_{m,K}` over `U` with a prescribed order of vanishing at a codimension-one point and order
  zero elsewhere on a neighbourhood**, from a discrete valuation stalk there.
* `Stacks.EtaleCohomology.exists_genericFibreOrd_eq_and_forall_ord_eq_zero_of_isNormal`: the same
  with the discrete valuation hypothesis discharged from normality of `X`, normality being étale
  local on the source by Stacks 0BQL.

## Implementation notes

`TopCat.Presheaf.isIso_Γgerm_of_subsingleton` is the one-point instantiation of
`TopCat.Presheaf.isIso_Γgerm_of_forall_eq_top`, whose hypothesis is supplied here by
`TopCat.Presheaf.forall_eq_top_of_specializes`: on a one-point space every point specializes to
every other. The same hypothesis is proved directly for a one-point scheme by
`AlgebraicGeometry.MultiplePointLength.eq_top_of_mem_of_subsingleton`; routing through
`TopCat.Presheaf.forall_eq_top_of_specializes` keeps this file out of the dependency cone of the
Euler-characteristic file that lemma lives in.

The hypotheses are integrality of `X` and of `U` and étaleness of `g`, where
`Stacks.EtaleCohomology.genericFibreToFunctionField` itself only needs flatness and
irreducibility. Both strengthenings are used by
`Stacks.EtaleCohomology.subsingleton_pullback_genericPointInclusion`, and they are what makes the
generic fibre a *single* point rather than one point per irreducible component of `U`: for a merely
flat `g` the generic fibre meets every irreducible component of `U`, and for a non-integral `U` the
fibre of an étale morphism over `η` need not be a single point.

What the right-hand exactness of Stacks 03RI still owes beyond this file: the sections-level
statement here has to be assembled into a covering sieve for
`Stacks.EtaleCohomology.divisorSequenceSecondMap`. It needs neither the separatedness of the
presheaf coproduct that `closedPointDivisorSheaf` sheafifies nor the passage from a single
prescribed point to an arbitrary finitely-supported section: an epimorphism out of a coproduct is
tested on the summands, by `CategoryTheory.Sheaf.epi_of_forall_imageSieve_ι_mem`, so only the
sections of a single summand are ever named. What it does need is the covering of an arbitrary
étale `X`-scheme by *integral affine* étale objects meeting the fibre over the chosen closed
point in a single point — the hypotheses `[IsIntegral U]` here and `coheight y = 1` being
available only after such a shrinking.

## References

* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the fundamental exact
  sequence, whose second map reads orders of vanishing of a function on the generic fibre.
* [Stacks Project, Tag 0BQL](https://stacks.math.columbia.edu/tag/0BQL): normality is étale local
  on the source.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Order TopologicalSpace TopCat
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace TopCat.Presheaf

/-- **The germ of the global sections of a presheaf on a one-point space is an isomorphism.** The
whole space is the only open neighbourhood of the point, so the colimit computing the stalk is
attained at `⊤`. -/
theorem isIso_Γgerm_of_subsingleton {C : Type u} [Category.{v} C] [HasColimits.{v} C]
    {X : TopCat.{v}} [Subsingleton X] (F : X.Presheaf C) (x : X) : IsIso (F.Γgerm x) :=
  isIso_Γgerm_of_forall_eq_top F x (forall_eq_top_of_specializes x fun z => by
    have hz : z = x := Subsingleton.elim z x
    subst hz
    exact specializes_rfl)

end TopCat.Presheaf

namespace Stacks.EtaleCohomology

section Iso

variable {X U : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral U]
  (g : U ⟶ X) [Etale g]

/-- **The germ of the global functions on the generic fibre at the generic fibre point is an
isomorphism.** The generic fibre of an étale morphism of integral schemes is a one-point scheme,
so its global functions are its local ring at that point. -/
theorem isIso_germ_top_genericFibrePoint :
    IsIso ((pullback g (genericPointInclusion X)).presheaf.germ ⊤
      (genericFibrePoint g) trivial) :=
  have : Subsingleton ↥(pullback g (genericPointInclusion X)) :=
    subsingleton_pullback_genericPointInclusion g
  TopCat.Presheaf.isIso_Γgerm_of_subsingleton _ _

/-- **The comparison with the function field is an isomorphism** for an étale morphism of integral
schemes: a rational function on `U` is the same thing as a global function on the generic fibre
`U ×_X Spec K`.

All three factors of
`Stacks.EtaleCohomology.genericFibreToFunctionField_eq_germ_comp` are isomorphisms: the germ by
`Stacks.EtaleCohomology.isIso_germ_top_genericFibrePoint`, the stalk map of the projection by
`Stacks.EtaleCohomology.isIso_stalkMap_pullback_fst_genericPointInclusion`, and the transport
along the equality of points by `TopCat.Presheaf.stalkCongr`. -/
theorem isIso_genericFibreToFunctionField : IsIso (genericFibreToFunctionField g) := by
  have h := isIso_stalkMap_pullback_fst_genericPointInclusion X g (genericFibrePoint g)
  have hgerm := isIso_germ_top_genericFibrePoint g
  rw [genericFibreToFunctionField_eq_germ_comp g (fst_base_genericFibrePoint g)]
  infer_instance

/-- **Every rational function on an étale `X`-scheme is a global function on its generic
fibre.** -/
theorem surjective_genericFibreToFunctionField :
    Function.Surjective (genericFibreToFunctionField g) :=
  have := isIso_genericFibreToFunctionField g
  (ConcreteCategory.bijective_of_isIso (genericFibreToFunctionField g)).2

/-- **Every invertible rational function on an étale `X`-scheme is an invertible global function
on its generic fibre**, that is, a section of `j_* 𝐆_{m,K}` over that scheme.

This is the surjectivity the right-hand exactness of the fundamental exact sequence of
Stacks 03RI needs: prescribing an order of vanishing on `U` means producing a *unit on the generic
fibre* mapping to the chosen rational function, the order of vanishing of a section of
`j_* 𝐆_{m,K}` being read through
`Stacks.EtaleCohomology.genericFibreToFunctionField` by
`Stacks.EtaleCohomology.genericFibreOrd_apply`. -/
theorem surjective_units_map_genericFibreToFunctionField :
    Function.Surjective (Units.map (genericFibreToFunctionField g).hom.toMonoidHom) := by
  have := isIso_genericFibreToFunctionField g
  intro b
  refine ⟨Units.map (inv (genericFibreToFunctionField g)).hom.toMonoidHom b, Units.ext ?_⟩
  simp

end Iso

section Ord

variable {X U : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral U]
  [IsLocallyNoetherian U] [NoetherianSpace U] (g : U ⟶ X) [Etale g]

/-- **A section of `j_* 𝐆_{m,K}` over an étale `X`-scheme with a prescribed divisor on a
neighbourhood of a codimension-one point.** Given a point `y` of `U` of codimension one whose
local ring is a discrete valuation ring and an integer `n`, there is an open neighbourhood `V` of
`y` in `U` and an invertible global function on the generic fibre `U ×_X Spec K` whose order of
vanishing is `n` at `y` and zero at every other point of `V`.

This is `AlgebraicGeometry.Scheme.exists_ord_eq_and_forall_ord_eq_zero_of_isDiscreteValuationRing`
transported along the surjectivity
`Stacks.EtaleCohomology.surjective_units_map_genericFibreToFunctionField`: the rational function
it produces is the image of a section of `j_* 𝐆_{m,K}` over `U`, which is the datum the second map
of the fundamental exact sequence of Stacks 03RI consumes. -/
theorem exists_genericFibreOrd_eq_and_forall_ord_eq_zero {y : U} (hco : coheight y = 1)
    (hdvr : IsDiscreteValuationRing (U.presheaf.stalk y)) (n : ℤ) :
    ∃ (V : U.Opens) (a : (Γ(pullback g (genericPointInclusion X), ⊤))ˣ),
      y ∈ V ∧ genericFibreOrd g y (Additive.ofMul a) = n ∧
        ∀ z ∈ V, z ≠ y → genericFibreOrd g z (Additive.ofMul a) = 0 := by
  obtain ⟨V, f, hyV, hf0, hfy, hfz⟩ :=
    Scheme.exists_ord_eq_and_forall_ord_eq_zero_of_isDiscreteValuationRing hco hdvr n
  obtain ⟨a, ha⟩ := surjective_units_map_genericFibreToFunctionField g (Units.mk0 f hf0)
  have hav : genericFibreToFunctionField g (a : Γ(pullback g (genericPointInclusion X), ⊤))
      = f := congrArg Units.val ha
  exact ⟨V, a, hyV, by simpa [hav] using hfy, fun z hz hzy => by simpa [hav] using hfz z hz hzy⟩

/-- **The same with the discrete valuation hypothesis discharged from normality of the base.** An
étale `X`-scheme over a normal `X` is normal by Stacks 0BQL, and the local ring of a locally
Noetherian normal scheme at a codimension-one point is a discrete valuation ring. -/
theorem exists_genericFibreOrd_eq_and_forall_ord_eq_zero_of_isNormal [IsNormal X] {y : U}
    (hco : coheight y = 1) (n : ℤ) :
    ∃ (V : U.Opens) (a : (Γ(pullback g (genericPointInclusion X), ⊤))ˣ),
      y ∈ V ∧ genericFibreOrd g y (Additive.ofMul a) = n ∧
        ∀ z ∈ V, z ≠ y → genericFibreOrd g z (Additive.ofMul a) = 0 :=
  have : IsNormal U := isNormal_of_etale g
  exists_genericFibreOrd_eq_and_forall_ord_eq_zero g hco
    (isDiscreteValuationRing_stalk_of_coheight_eq_one hco) n

end Ord

end Stacks.EtaleCohomology

end
