module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalConnectionTensor

/-!
# The pair `(M, ∇)` attached to a crystal, and the three clauses of the comparison datum

[Stacks, Tag 07JG] asserts a functor from crystals in quasi-coherent `𝒪_{X/S}`-modules to pairs
`(M, ∇)` satisfying its four items (07JB)–(07JE).  In the library the target of that functor is
`Crystalline.firstOrderCrystalsToPairs`, whose source objects `Crystalline.FirstOrderCrystal`
bundle a `Crystalline.FirstOrderComparison` — a map `ε : M → (D ⊕ Ω) ⊗_D M` which is additive,
reduces to the identity modulo `Ω` and is semilinear for `p₁` — together with the four carried
properties.

`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalFirstOrderComparison.lean` builds the
*geometric* datum `ε : p₀^* F_T ≅ p₁^* F_T` of a crystal and records that the passage to the
algebraic datum was blocked on the sections of a pullback being a base change.  The connection
itself is available on sections regardless, as
`Crystalline.GlobalCrystallineSituation.crystalConnection` with its values in the ideal of the
diagonal, and this module supplies the two things that gives:

* **the three clauses of `Crystalline.FirstOrderComparison`**, read on the sections of `F` over an
  object of `CRIS(X/S)`.  The comparison map is the restriction `s ↦ p₁^* s` along the second
  projection; in the decomposition `𝒪_{T'}(T') = 𝒪_T(T) ⊕ Ω` its reduction is `s` itself and its
  differential component is `∇(s)`.  So the clause `reduction` is that both projections retract
  the diagonal, the clause `semilinear` is semilinearity of a restriction map, and the equation
  identifying the differential component with the connection is
  `moduleSiteRestrict_siteP₁_eq_add_crystalConnection`;
* **the functoriality in the crystal of the assignment `F ↦ (Γ(T, F_T), ∇)`**, which is the
  "functor" half of [Stacks, Tag 07JG] at the level of the pairs rather than, as in the earlier
  module, at the level of the comparison data.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.moduleSiteMap` — a morphism of sheaves of
  `𝒪_{X/S}`-modules on the sections over an object, as a linear map.

## Main results

* `Crystalline.GlobalCrystallineSituation.moduleSiteMap_naturality` — a morphism of sheaves of
  modules commutes with the restriction maps along a morphism of the site.
* `Crystalline.GlobalCrystallineSituation.diffAction_naturality` — the canonical map
  `F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ ker` is natural in the module.
* `Crystalline.GlobalCrystallineSituation.moduleSiteMap_crystalConnection` — **the connection of
  [Stacks, Tag 07J6] is natural in the module**: a morphism of sheaves of modules carries the
  pair of one to the pair of the other.  This is the functoriality clause of
  [Stacks, Tag 07JG], and it takes no hypothesis.
* `Crystalline.GlobalCrystallineSituation.crystalConnectionTensor_naturality` — the same
  statement for the connection valued in `Ω ⊗_D M`, which needs a
  `Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange` datum for each of the two
  modules.
* `Crystalline.GlobalCrystallineSituation.moduleSiteRestrict_siteι_siteP₁`,
  `Crystalline.GlobalCrystallineSituation.moduleSiteRestrict_siteP₁_smul` and
  `Crystalline.GlobalCrystallineSituation.moduleSiteRestrict_siteP₁_eq_add_crystalConnection` —
  **the three clauses of `Crystalline.FirstOrderComparison`** for the comparison map
  `s ↦ p₁^* s`: it reduces to the identity modulo the ideal of the diagonal, it is semilinear for
  `p₁`, and its differential component is the connection.  None of the three takes a hypothesis.
* `Crystalline.GlobalCrystallineSituation.moduleSiteRestrict_siteP₁_eq_add_diffAction` — the
  third of those clauses with the differential component read inside `Ω ⊗_D M`, which again needs
  the datum.

## What is and is not proved

The three clauses and the functoriality are proved, and the two of them that mention the
connection are proved twice.  Once with the connection valued in the ideal of the diagonal of
[Stacks, Tag 07J2] — where the statement takes no hypothesis, and where the attributes for
[Stacks, Tag 07JG] sit — and once with it valued in
`Ω ⊗_D M = Γ(T, Ω_{T/S,δ}) ⊗ Γ(T, F_T)`, where the statement takes a
`Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange` datum.  The second spelling
carries no attribute: that datum puts the algebraic tensor product of global sections where
[Stacks, Tag 07J6] names the sheaf tensor product `F_T ⊗_{𝒪_T} Ω_{T/S,δ}`, and the two differ on
a general object, by the ℙ¹ counterexample in the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealSheaf.lean`.

Together the unconditional forms give the decomposition on which item (07JC) of
[Stacks, Tag 07JG] rests — its Leibniz rule being
`Crystalline.GlobalCrystallineSituation.crystalConnection_smul`, registered for
[Stacks, Tag 07J6] — and the half of the tag that makes the assignment a functor.  What is
**not** proved, and is not claimed by any attribute here:

1. **The remaining three items.**  (07JB) `p`-adic completeness of `M`, (07JD) integrability of
   `∇` and (07JE) topological quasi-nilpotence are properties that
   `Crystalline.FirstOrderCrystal` carries as hypotheses, and nothing here derives any of them.
   Integrability needs the second-order thickening `(U, T'', δ'')` of [Stacks, Tag 07J3] as an
   object of the site and the degree-two analogue of
   `Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange`; completeness needs the
   finite levels `Spec(D/p^e D)` as objects of the site, which is [Stacks, Tag 07JN];
   quasi-nilpotence needs the explicit structure of `D(1)`.  So
   `Crystalline.firstOrderCrystalsToPairs` still **cannot** be fed by a crystal: four of its
   source's fields are exactly these, and this module closes none of them.

   The second-order thickening itself is available:
   `Crystalline.GlobalCrystallineSituation.secondOrderThickeningSiteData` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/CrystalConnectionSecondOrder.lean` constructs the
   datum outright.  And the finite levels are available too: they are
   `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineCosimplicialSystem.lean`.  What
   remains open in each case is the base-change datum, not the object.
2. **The specific ring `D` of Situation 07MD.**  Everything below is over an arbitrary object
   `(U, T, δ)` of `CRIS(X/S)`, with `D = Γ(T, 𝒪_T)`, and that is not the `D` of the tag.  The
   ring `D` of Situation 07MD is nevertheless related to the site, in the following form.
   The completed envelope is the section ring of no object of `Cris(X/S)`, its divided power
   ideal not being locally nilpotent, so the identification is with a *system* of objects: the
   finite levels are `...SmallSite.wholeSpaceSystem`, their section rings are `D(n)/(p)^{N+e}`
   by `...SmallSite.wholeSpaceSystemLevelRingEquiv`, and `D(n)` is their inverse limit by
   `...SmallSite.envelopeLevelRingLimitEquiv` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/WholeSpaceSystemLevelRings.lean`.  What
   this module does not do is rerun its statements over that system instead of over one
   object.
3. **The bundled `Crystalline.FirstOrderComparison` record.**  Its three clauses are proved here
   in the geometric spelling, over `Γ(T', 𝒪_{T'})` and `Γ(T, Ω_{T/S,δ})`.  Assembling the record
   additionally needs `Γ(T, 𝒪_T)` presented as a bundled `Crystalline.DividedPowerRing` with
   `Γ(T, Ω_{T/S,δ})` as a module carrying the opposite action and central scalars, the derivation
   presented as a `Crystalline.DividedPowerDerivation` — which is available, as
   `Crystalline.dpDerivationAt` — and the ring `Γ(T', 𝒪_{T'})` presented as
   `Crystalline.firstOrderExtension` of those, compatibly with `Crystalline.firstOrderP₀` and
   `Crystalline.firstOrderP₁`.  Each identification is definitional and none is carried out here.
4. **The quasi-coherence clause** of the source of the tag, and the base-change datum itself: see
   the "What is and is not proved" section of
   `StacksFrontier/AlgebraicGeometry/Crystalline/CrystalConnectionTensor.lean`, which records that
   `Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange` follows from invertibility
   of the *presheaf-level* comparison map of [Stacks, Tag 07IQ] and not from the sheaf-level
   crystal condition.

Everything is stated on the **big** crystalline site `CRIS(X/S)`, whose objects are
`Crystalline.GlobalCrystallineSituation.Thickening`, because that is where the connection of the
previous module lives.  [Stacks, Tag 07JG] quantifies over crystals on the small site
`Cris(X/S)`; the proofs below use nothing about the site beyond the three morphisms of the
first-order thickening, so they transcribe to `Crystalline.GlobalCrystallineSituation.
CrystallineThickening` verbatim, and that transcription is not performed here.

## Implementation notes

A morphism of sheaves of `𝒪_{X/S}`-modules is read on sections through
`Crystalline.GlobalCrystallineSituation.moduleSiteMap`, which forces the result to be a
`LinearMap` rather than a morphism of `ModuleCat`, so that `map_smul` and `map_add` apply to it
without unfolding the concrete-category coercion.

The crystal hypothesis `Crystalline.GlobalCrystallineSituation.IsSheafCrystal` appears nowhere
below.  The quantifier runs over all sheaves of `𝒪_{X/S}`-modules, as it does for the connection
of the previous module: what the crystal condition contributes is that the difference
`p₁^* s - p₀^* s` *is* the map `∇` of [Stacks, Tag 07J6], which is
`Crystalline.GlobalCrystallineSituation.moduleComparisonSheaf_app_apply_unit_app` together with
`Crystalline.GlobalCrystallineSituation.exists_comp_moduleComparisonSheaf_eq`, and that is
already proved in
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalConnectionGeneral.lean`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}
  {M N : SheafOfModules.{u} (crystallineStructureSheaf S)}

/-! ### A morphism of sheaves of modules on the sections over an object -/

/-- **A morphism of sheaves of `𝒪_{X/S}`-modules, read on the sections over an object of
`CRIS(X/S)`**, as a linear map over the sections of `𝒪_{X/S}` there. -/
abbrev moduleSiteMap (ψ : M ⟶ N) (A : Thickening S) :
    M.val.obj (op A) →ₗ[crysSheafRing S A] N.val.obj (op A) :=
  (Hom.app ψ.val (op A)).hom

/-- **A morphism of sheaves of modules commutes with the restriction maps of the site.**  This is
the naturality of the underlying morphism of presheaves of modules, read at the opposite of a
morphism of `CRIS(X/S)`. -/
theorem moduleSiteMap_naturality (ψ : M ⟶ N) {A B : Thickening S} (g : A ⟶ B)
    (x : M.val.obj (op B)) :
    moduleSiteMap ψ A (moduleSiteRestrict M g x) =
      moduleSiteRestrict N g (moduleSiteMap ψ B x) :=
  PresheafOfModules.naturality_apply ψ.val g.op x

/-! ### Naturality of the canonical map and of the connection -/

/-- **The canonical map `F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ ker` is natural in the module.**  Both sides
send `ω ⊗ s` to `ω · p₀^* ψ(s)`: on the left the morphism is applied before the canonical map and
on the right after it, and the two agree because `ψ` commutes with the restriction along `p₀` and
is linear over the sections of `𝒪_{T'}`. -/
theorem diffAction_naturality (ψ : M ⟶ N) (A : Thickening S)
    (z : crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    diffAction N A (LinearMap.lTensor (crysDiffSections A) (moduleSiteMap ψ A) z) =
      moduleSiteMap ψ (firstOrderThickeningObject S A) (diffAction M A z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul ω s =>
      rw [LinearMap.lTensor_tmul, diffAction_tmul, diffAction_tmul,
        map_smul (moduleSiteMap ψ (firstOrderThickeningObject S A)), moduleSiteMap_naturality]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

/-- **The canonical connection of [Stacks, Tag 07J6] is natural in the module.**  A morphism
`ψ : F ⟶ G` of sheaves of `𝒪_{X/S}`-modules carries the pair `(Γ(T, F_T), ∇_F)` to the pair
`(Γ(T, G_T), ∇_G)`: the square formed by the two connections and the two readings of `ψ` on
sections commutes.  Both terms of `∇` are restriction maps of the module along a morphism of the
site and `ψ` commutes with those, so the statement holds for every pair of sheaves of
`𝒪_{X/S}`-modules over every object, with no hypothesis.

This is the functoriality clause of [Stacks, Tag 07JG] — the half of the statement that makes the
assignment of a pair to a crystal a functor — at the level of the pairs `(M, ∇)` rather than, as
in `Crystalline.GlobalCrystallineSituation.SmallSite.firstOrderComparison_naturality`, at the
level of the comparison data.  The connection is the one [Stacks, Tag 07J6] is registered on,
`Crystalline.GlobalCrystallineSituation.crystalConnection`, whose values are sections of the
ideal of the diagonal `i : T ⟶ T'`; reading them inside `F_T ⊗_{𝒪_T} Ω_{T/S,δ}` is the open half
of [Stacks, Tag 07J6], discussed in the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealSheaf.lean`. -/
theorem moduleSiteMap_crystalConnection (ψ : M ⟶ N) (A : Thickening S)
    (s : M.val.obj (op A)) :
    moduleSiteMap ψ (firstOrderThickeningObject S A) (crystalConnection M A s) =
      crystalConnection N A (moduleSiteMap ψ A s) := by
  rw [crystalConnection_apply, crystalConnection_apply, map_sub, moduleSiteMap_naturality,
    moduleSiteMap_naturality]

/-- **The connection with the target of [Stacks, Tag 07J6] is natural in the module.**  A morphism
`ψ : F ⟶ G` of sheaves of `𝒪_{X/S}`-modules carries the pair `(Γ(T, F_T), ∇_F)` to the pair
`(Γ(T, G_T), ∇_G)`, for the connection valued in `Ω ⊗_D M`.  The proof is the naturality of the
difference `p₁^* s - p₀^* s`, transported across the injectivity of the canonical map.

This declaration carries no `@[stacks]` attribute.  Its hypothesis is a
`Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange` datum for each of the two
modules, and in that spelling — with `Ω ⊗_D M` the algebraic tensor product of *global sections*,
while the target `F_T ⊗_{𝒪_T} Ω_{T/S,δ}` of [Stacks, Tag 07J6] is the sheaf tensor product — the
datum is false on a general object, by the ℙ¹ counterexample in the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealSheaf.lean`.  The functoriality clause
of [Stacks, Tag 07JG] is registered instead on
`Crystalline.GlobalCrystallineSituation.moduleSiteMap_crystalConnection` above, which is that
clause for the connection valued in the ideal of the diagonal and takes no datum. -/
theorem crystalConnectionTensor_naturality (ψ : M ⟶ N) (A : Thickening S)
    (hM : FirstOrderIdealBaseChange M A) (hN : FirstOrderIdealBaseChange N A)
    (s : M.val.obj (op A)) :
    LinearMap.lTensor (crysDiffSections A) (moduleSiteMap ψ A)
        (crystalConnectionTensor M A hM s) =
      crystalConnectionTensor N A hN (moduleSiteMap ψ A s) := by
  refine hN.injective_diffAction ?_
  rw [diffAction_naturality, diffAction_crystalConnectionTensor,
    diffAction_crystalConnectionTensor, moduleSiteMap_crystalConnection]

/-! ### The three clauses of the algebraic comparison datum -/

/-- **The comparison map reduces to the identity modulo the ideal of the diagonal.**  Restricting
`p₁^* s` along the diagonal `i` returns `s`, because `p₁ ∘ i = id` in `CRIS(X/S)`.  This is the
clause `reduction` of `Crystalline.FirstOrderComparison` for the comparison map `s ↦ p₁^* s`, the
ideal of `i` being `Ω_{T/S,δ}` by [Stacks, Tag 07J2]. -/
theorem moduleSiteRestrict_siteι_siteP₁ (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    (A : Thickening S) (s : M.val.obj (op A)) :
    moduleSiteRestrict M (firstOrderThickeningSiteι S A)
        (moduleSiteRestrict M (firstOrderThickeningSiteP₁ S A) s) = s := by
  rw [moduleSiteRestrict_comp, firstOrderThickeningSiteι_comp_P₁, moduleSiteRestrict_id]

/-- **The comparison map is semilinear for `p₁`.**  It is a restriction map of `F` along the
morphism `p₁` of the site, hence semilinear over the map `p₁` on sections of `𝒪_{X/S}`.  This is
the clause `semilinear` of `Crystalline.FirstOrderComparison`, and it needs nothing beyond the
definition of a presheaf of modules: it is the content of that clause that the comparison
identifies the two pullbacks of `F_T`, and on sections that identification *is* the restriction
along `p₁`. -/
theorem moduleSiteRestrict_siteP₁_smul
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (A : Thickening S)
    (b : crysSheafRing S A) (s : M.val.obj (op A)) :
    moduleSiteRestrict M (firstOrderThickeningSiteP₁ S A) (b • s) =
      crysSheafRingMap (firstOrderThickeningSiteP₁ S A) b •
        moduleSiteRestrict M (firstOrderThickeningSiteP₁ S A) s :=
  map_smulₛₗ _ b s

/-- **The differential component of the comparison map is the connection.**  The comparison map
`s ↦ p₁^* s` of [Stacks, Tag 07JG] decomposes as

`p₁^* s = p₀^* s + ∇(s)`,

the second term being the connection of [Stacks, Tag 07J6] with its values in the ideal of the
diagonal.  This is the defining equation that the proof of [Stacks, Tag 07JG] quotes from
[Stacks, Tag 07J6], and it holds for every sheaf of `𝒪_{X/S}`-modules over every object with no
hypothesis: `Crystalline.GlobalCrystallineSituation.crystalConnection` is that difference by
definition.

So the differential component of the comparison map, which is what
`Crystalline.FirstOrderComparison.connection` extracts, is the connection of [Stacks, Tag 07J6] —
the identity on which item (07JC) of [Stacks, Tag 07JG] rests, its Leibniz rule being
`Crystalline.GlobalCrystallineSituation.crystalConnection_smul`.  Reading that component inside
`F_T ⊗_{𝒪_T} Ω_{T/S,δ}` rather than inside the ideal is the open half of [Stacks, Tag 07J6]; the
restatement that does so is
`Crystalline.GlobalCrystallineSituation.moduleSiteRestrict_siteP₁_eq_add_diffAction` below. -/
theorem moduleSiteRestrict_siteP₁_eq_add_crystalConnection
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (A : Thickening S)
    (s : M.val.obj (op A)) :
    moduleSiteRestrict M (firstOrderThickeningSiteP₁ S A) s =
      moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s + crystalConnection M A s := by
  rw [crystalConnection_apply]
  abel

/-- **The differential component of the comparison map, read inside `Ω ⊗_D M`.**  The same
decomposition

`p₁^* s = p₀^* s + ∇(s)`,

with the second term now the image of `∇(s) ∈ Ω ⊗_D M` under the canonical map
`Crystalline.GlobalCrystallineSituation.diffAction`.

This declaration carries no `@[stacks]` attribute.  Its hypothesis is a
`Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange` datum, and in that spelling —
with `Ω ⊗_D M` the algebraic tensor product of *global sections*, while the target
`F_T ⊗_{𝒪_T} Ω_{T/S,δ}` of [Stacks, Tag 07J6] is the sheaf tensor product — the datum is false on
a general object, by the ℙ¹ counterexample in the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealSheaf.lean`.  The decomposition clause
of [Stacks, Tag 07JG] is registered instead on
`Crystalline.GlobalCrystallineSituation.moduleSiteRestrict_siteP₁_eq_add_crystalConnection`
above, which takes no datum. -/
theorem moduleSiteRestrict_siteP₁_eq_add_diffAction
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (A : Thickening S)
    (h : FirstOrderIdealBaseChange M A) (s : M.val.obj (op A)) :
    moduleSiteRestrict M (firstOrderThickeningSiteP₁ S A) s =
      moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s +
        diffAction M A (crystalConnectionTensor M A h s) := by
  rw [diffAction_crystalConnectionTensor, ← moduleSiteRestrict_siteP₁_eq_add_crystalConnection]

end Crystalline.GlobalCrystallineSituation

end

end
