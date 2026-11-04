module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinFractionDeRham

/-!
# The abelian naturality of the class map of Stacks 0G7Q, above the Čech cokernel

Let `X` be a scheme and let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be global equations with `c = n + 1`.  The
class map of [Stacks, Tag 0G7Q] carries a top-degree cochain of the extended alternating Čech
complex of a quasi-coherent `𝒪_X`-module `ℱ` to its class in `i_*ℋ ᶜ_Z(ℱ)`; in the spelling the
Gysin map of [Stacks, Tag 0G83] is built in this is
`Stacks.Perfect.GysinFractionDeRham.topCechClass`, the canonical epimorphism
`cokernel.π (lastDif f ℱ)` followed by the identification
`Stacks.Perfect.GysinFractionDeRham.cokernelLastDifToPushforward` of the Čech cokernel with
`i_*ℋ ᶜ_Z(ℱ)`.

The proof of [Stacks, Tag 0G85] needs that class map to be natural along a morphism of the
**underlying abelian sheaves** of the coefficient modules, not merely along an `𝒪_X`-linear one,
because the relative de Rham differential `d : Ω^p_{X/S} ⟶ Ω^{p+1}_{X/S}` is `f⁻¹𝒪_S`-linear and
is not a morphism of `X.Modules` at all.  That statement is
`Stacks.Perfect.GysinFractionDeRham.TopCechClassAbelianNatural`.

This file **moves that statement off the epimorphism**: it shows that
`TopCechClassAbelianNatural` is *equivalent* to the commutativity of the square one step above it,
between the Čech cokernel and `i_*ℋ ᶜ_Z`, with left vertical arrow
`Stacks.Perfect.AbelianFraction.cokernelLastDifAb` — the abelian functoriality of the Čech
cokernel — and right vertical arrow
`Stacks.Perfect.GysinAbelianSquare.gysinTargetAbelianMap`.  The passage is in both directions and
therefore loses nothing: the square below is neither weaker nor stronger than
`TopCechClassAbelianNatural`, so no new and possibly unsatisfiable hypothesis is introduced.  What
it buys is that the surviving statement is a square between the two objects the comparison of
[Stacks, Tag 0G7L] relates, with no cochain and no `cokernel.π` in it, which is the form in which
the derived-category input can be applied to it.

## Main definitions

* `CokernelLastDifToPushforwardAbelianNatural`: the square

  `Coker(lastDif f ℱ) ⟶ i_*ℋ ᶜ_Z(ℱ)` over `Coker(lastDif f 𝒢) ⟶ i_*ℋ ᶜ_Z(𝒢)`,

  with horizontal arrows the underlying abelian-sheaf morphisms of `cokernelLastDifToPushforward`,
  left vertical arrow `Stacks.Perfect.AbelianFraction.cokernelLastDifAb` and right vertical arrow
  `Stacks.Perfect.GysinAbelianSquare.gysinTargetAbelianMap`, for a morphism `ψ` of the underlying
  abelian sheaves of the coefficient modules.  A proposition; it is proved here only in the
  `𝒪_X`-linear-identity case.

## Main results

* `topCechClassAbelianNatural_of_abelianSquare` and
  `abelianSquare_of_topCechClassAbelianNatural`: the two implications, so that
  `CokernelLastDifToPushforwardAbelianNatural` and
  `Stacks.Perfect.GysinFractionDeRham.TopCechClassAbelianNatural` are equivalent; the equivalence
  itself is `topCechClassAbelianNatural_iff_abelianSquare`.  The forward direction is the
  defining property `Stacks.Perfect.AbelianFraction.map_cokernelπ_comp_cokernelLastDifAb` of the
  abelian functoriality of the cokernel; the converse uses in addition that the canonical
  epimorphism onto the cokernel stays an epimorphism after forgetting the module structure,
  `Stacks.Perfect.AbelianFraction.epi_map_cokernelπ_lastDif`.
* `topCechClassAbelianNatural_id`: both propositions hold for the identity morphism.  This is a
  nonvacuity check and nothing more: the identity satisfies any square of this shape.  The
  substantive check is that the equivalence above is an equivalence, which is what makes the
  square exactly as satisfiable as the statement it replaces.

## Implementation notes

**Carried hypotheses.**  Exactly those of
`Stacks.Perfect.GysinFractionDeRham.TopCechClassAbelianNatural` itself: a nonempty family of
global equations `f : Fin (n + 1) → Γ(X, 𝒪_X)` and quasi-coherence of both coefficient modules,
`[F.IsQuasicoherent]` and `[G.IsQuasicoherent]`, which is what
`cokernelLastDifToPushforward` needs — it is where [Stacks, Tag 0G7M] enters.  The closed subset
is specialised throughout to the common zero locus of the equations, as it is in the Gysin map;
that is a specialisation and not a hypothesis.  No hypothesis is placed on `ψ` beyond its being a
morphism of the underlying abelian presheaves, and in particular no `𝒪_X`-linearity: the whole
point of the statement is that it is false to assume any.  `IsClosed` is not carried because the
zero locus is closed by `Stacks.Perfect.CechDerivedSupport.isClosed_equationsClosedSet`, which
`Stacks.Perfect.GysinAbelianSquare.gysinTargetAbelianMap` already applies.

## References

* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Perfect.AbelianFraction (abelianSheaf abHom)
open Stacks.Perfect.GysinFractionDeRham (TopCechClassAbelianNatural cokernelLastDifToPushforward
  topCechClass)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.AbelianClassMap

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}} {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤))

/-- **The square of step (ii) of [Stacks, Tag 0G85], above the Čech cokernel.**  For a morphism
`ψ` of the underlying abelian sheaves of two quasi-coherent coefficient modules — not required to
be `𝒪_X`-linear — the identification `Coker(lastDif f ℱ) ⟶ i_*ℋ ᶜ_Z(ℱ)` of
`Stacks.Perfect.GysinFractionDeRham.cokernelLastDifToPushforward` carries the abelian
functoriality `Stacks.Perfect.AbelianFraction.cokernelLastDifAb` of the Čech cokernel to the
abelian action `Stacks.Perfect.GysinAbelianSquare.gysinTargetAbelianMap` on the target of the
Gysin map.

This is equivalent to `Stacks.Perfect.GysinFractionDeRham.TopCechClassAbelianNatural` by
`topCechClassAbelianNatural_iff_abelianSquare`, and is not proved here. -/
public def CokernelLastDifToPushforwardAbelianNatural {F G : X.Modules} [F.IsQuasicoherent]
    [G.IsQuasicoherent] (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) : Prop :=
  (abelianSheaf X).map (cokernelLastDifToPushforward f F) ≫
      GysinAbelianSquare.gysinTargetAbelianMap f (abHom ψ) =
    AbelianFraction.cokernelLastDifAb f ψ ≫
      (abelianSheaf X).map (cokernelLastDifToPushforward f G)

/-- The class map of [Stacks, Tag 0G7Q] in the Gysin map's spelling, read after forgetting the
module structure, is the forgotten canonical epimorphism onto the Čech cokernel followed by the
forgotten identification of that cokernel with `i_*ℋ ᶜ_Z(ℱ)`. -/
private theorem map_topCechClass (F : X.Modules) [F.IsQuasicoherent] :
    (abelianSheaf X).map (topCechClass f F) =
      (abelianSheaf X).map (cokernel.π (SupportedFraction.lastDif f F)) ≫
        (abelianSheaf X).map (cokernelLastDifToPushforward f F) := by
  simp only [topCechClass, CategoryTheory.Functor.map_comp]

/-- The naturality of the class map is equivalent to the square above the Čech cokernel, by
cancelling the forgotten canonical epimorphism onto the cokernel. -/
private theorem topCechClassAbelianNatural_iff {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    TopCechClassAbelianNatural f ψ ↔ CokernelLastDifToPushforwardAbelianNatural f ψ := by
  simp only [TopCechClassAbelianNatural, CokernelLastDifToPushforwardAbelianNatural,
    map_topCechClass]
  rw [← cancel_epi ((abelianSheaf X).map (cokernel.π (SupportedFraction.lastDif f F))),
    ← Category.assoc, ← Category.assoc, ← Category.assoc,
    ← AbelianFraction.map_cokernelπ_comp_cokernelLastDifAb, Category.assoc, Category.assoc]

/-- **The square above the Čech cokernel implies the naturality of the class map.**  Composing
the square with the forgotten canonical epimorphism onto the cokernel and using its defining
property `Stacks.Perfect.AbelianFraction.map_cokernelπ_comp_cokernelLastDifAb` gives
`Stacks.Perfect.GysinFractionDeRham.TopCechClassAbelianNatural`. -/
public theorem topCechClassAbelianNatural_of_abelianSquare {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (h : CokernelLastDifToPushforwardAbelianNatural f ψ) :
    TopCechClassAbelianNatural f ψ :=
  (topCechClassAbelianNatural_iff f ψ).2 h

/-- **The naturality of the class map implies the square above the Čech cokernel.**  The
canonical epimorphism onto the cokernel stays an epimorphism after forgetting the module
structure (`Stacks.Perfect.AbelianFraction.epi_map_cokernelπ_lastDif`), so the square may be
cancelled off it.  Together with `topCechClassAbelianNatural_of_abelianSquare` this shows the two
statements are equivalent, so that replacing one by the other introduces no hypothesis that was
not already at issue. -/
public theorem abelianSquare_of_topCechClassAbelianNatural {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (h : TopCechClassAbelianNatural f ψ) :
    CokernelLastDifToPushforwardAbelianNatural f ψ :=
  (topCechClassAbelianNatural_iff f ψ).1 h

/-- **The naturality of the class map of [Stacks, Tag 0G7Q] in an arbitrary morphism of abelian
sheaves is equivalent to the square above the Čech cokernel.** -/
public theorem topCechClassAbelianNatural_iff_abelianSquare {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    TopCechClassAbelianNatural f ψ ↔ CokernelLastDifToPushforwardAbelianNatural f ψ :=
  topCechClassAbelianNatural_iff f ψ

/-- **A nonvacuity check**: the square holds for the identity morphism.  The abelian
functoriality of the Čech cokernel sends the identity to the identity
(`Stacks.Perfect.AbelianFraction.cokernelLastDifAb_id`) and so does the abelian action on the
target of the Gysin map
(`Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyAbelianMap_id`), so both composites
are the identification itself.  This says nothing about a morphism that is not `𝒪_X`-linear. -/
public theorem abelianSquare_id (F : X.Modules) [F.IsQuasicoherent] :
    CokernelLastDifToPushforwardAbelianNatural f (Scheme.Modules.Hom.mapPresheaf (𝟙 F)) := by
  have hab : abHom (Scheme.Modules.Hom.mapPresheaf (𝟙 F)) = 𝟙 ((abelianSheaf X).obj F) := by
    rw [← AbelianFraction.abelianSheaf_map, CategoryTheory.Functor.map_id]
  have hgt : GysinAbelianSquare.gysinTargetAbelianMap f
      (abHom (Scheme.Modules.Hom.mapPresheaf (𝟙 F))) = 𝟙 _ := by
    rw [hab]
    exact GysinAbelianSquare.pushforwardLocalCohomologyAbelianMap_id
      (CechDerivedSupport.isClosed_equationsClosedSet f) (n + 1) F
  simp only [CokernelLastDifToPushforwardAbelianNatural, hgt,
    AbelianFraction.cokernelLastDifAb_id, Category.comp_id, Category.id_comp]

/-- **A nonvacuity check**: the naturality statement holds for the identity morphism. -/
public theorem topCechClassAbelianNatural_id (F : X.Modules) [F.IsQuasicoherent] :
    TopCechClassAbelianNatural f (Scheme.Modules.Hom.mapPresheaf (𝟙 F)) :=
  topCechClassAbelianNatural_of_abelianSquare f _ (abelianSquare_id f F)

/-! ### The square of Stacks 0G85 for the Gysin formula, from the square above the cokernel -/

section Assembly

attribute [local instance]
  AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms

/-- **The comparison square of [Stacks, Tag 0G85] for the Gysin formula follows from the square
above the Čech cokernel.**  This chains `topCechClassAbelianNatural_of_abelianSquare` with
`Stacks.Perfect.GysinFractionDeRham.gysinFormulaCommutesWithDeRham_of_topCechClassNatural`, which
discharges everything else in the source's proof: step (iii), the commutation of the wedge factor
with `d`, and step (ii-b), the localized Leibniz rule.

This is a reduction and **not** a proof of [Stacks, Tag 0G85]: the hypothesis carries all of the
content, and by `topCechClassAbelianNatural_iff_abelianSquare` it is neither weaker nor stronger
than the hypothesis of the statement it is chained with. -/
public theorem gysinFormulaCommutesWithDeRham_of_abelianSquare {S : Scheme.{u}} (π : X ⟶ S)
    (p : ℕ)
    (h : CokernelLastDifToPushforwardAbelianNatural f
      (AlgebraicGeometry.Scheme.Hom.deRhamDifferentialPresheafHom π (p + (n + 1)))) :
    AlgebraicGeometry.Scheme.Hom.GysinFormulaCommutesWithDeRham π f p :=
  GysinFractionDeRham.gysinFormulaCommutesWithDeRham_of_topCechClassNatural f π p
    (topCechClassAbelianNatural_of_abelianSquare f _ h)

end Assembly

end Stacks.Perfect.AbelianClassMap

end
