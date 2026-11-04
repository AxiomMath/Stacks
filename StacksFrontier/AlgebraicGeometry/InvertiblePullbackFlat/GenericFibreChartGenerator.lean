module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GenericFibreChart
public import StacksFrontier.AlgebraicGeometry.NormInvertible.PullbackGenerator

/-!
# A trivialization of `ℒ` on an affine chart, read on the generic fibre

`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/GenericFibreChart.lean` exhibits
`Spec (Ideal.Fiber ⊥ Γ(X, U))` as an affine open of the generic fibre `X_ξ`, for affine opens
`x ∈ U ≤ f ⁻¹ᵁ V` of a morphism `f : X ⟶ Y` to an integral `Y`
(`AlgebraicGeometry.genericFiberChartι`), and reduces the penultimate paragraph of
[Stacks, Tag 0BD7] at `x` to a *unit* of that ring. This file identifies the open and carries a
trivialization of `ℒ` on `U` across to it.

The open is the range of the chart morphism (`AlgebraicGeometry.genericFiberChartOpens`), it *is*
`(f.fiberι ξ) ⁻¹ᵁ U` (`AlgebraicGeometry.genericFiberChartOpens_eq`), and so a generator of `ℒ` on
`U` becomes, by `Stacks.SheafOfModules.pullbackGenerator` and one restriction, a generator of
`ℒ_ξ` there.

The equality, rather than the containment alone, is what lets a *given* point of the generic
fibre be placed in the chart — the point over the generic point of `X`, at which the germ of the
chart ratio is taken.

## Main definitions

* `AlgebraicGeometry.genericFiberChartOpens`: the affine open of `X_ξ` the chart cuts out.
* `AlgebraicGeometry.genericFiberChartGenerator`: the pullback to it of a generator of `ℒ` on `U`.

## Main results

* `AlgebraicGeometry.fiberCompι_comp_fiberι`: the fibre of `j ≫ f` maps to the fibre of `f` over
  `j`.
* `AlgebraicGeometry.fiberCompIsoFiber_hom_fiberι`,
  `AlgebraicGeometry.fiber_transport_hom_fiberι` and
  `AlgebraicGeometry.fiberAppLEIsoFiberComp_hom_fiberι`: the two isomorphisms standing in front
  of `AlgebraicGeometry.fiberCompι` inside `AlgebraicGeometry.fiberAppLEι` leave the inclusion of
  the fibre alone.
* `AlgebraicGeometry.specMapFiberIsoSpecFiberRing_inv_fiberι`: the last of those legs — the fibre
  of a morphism of spectra, read as the spectrum of the fibre ring, includes into `Spec S` as the
  spectrum of `S → Ideal.Fiber 𝔭 S`.
* `AlgebraicGeometry.fiberAppLEι_comp_fiberι`, `AlgebraicGeometry.fiberChartι_comp_fiberι` and
  `AlgebraicGeometry.genericFiberChartι_comp_fiberι`: hence **the chart square commutes**, at a
  variable prime, at a named point of `Y`, and over the generic point.
* `AlgebraicGeometry.fiberι_fiberChartι_mem` and
  `AlgebraicGeometry.genericFiberChartOpens_le`: the chart of the fibre lies over `U`.
* `AlgebraicGeometry.range_fiberCompι`, `AlgebraicGeometry.range_fiberAppLEι` and
  `AlgebraicGeometry.range_fiberChartι`: the chart of the fibre is the *whole* of the part of
  the fibre lying over `U`.
* `AlgebraicGeometry.genericFiberChartOpens_eq` and
  `AlgebraicGeometry.mem_genericFiberChartOpens`: hence the containment above is an equality,
  and a point of the generic fibre over `U` lies in the chart.
* `AlgebraicGeometry.nonempty_generatorSections_genericFiberChart`: existence of the generator.
* `AlgebraicGeometry.exists_affine_chart_generator_mem`: every point of `X` has an affine chart
  carrying a generator of `ℒ`, so the hypotheses above are available at every point.

## Implementation notes

That the chart lies over `U` is proved twice, and the two proofs are not variants of one
another. `AlgebraicGeometry.fiberι_fiberChartι_mem` argues on morphisms rather than on points:
`AlgebraicGeometry.fiberAppLEι` is a composite ending in
`AlgebraicGeometry.fiberCompι hU.fromSpec f`, and `AlgebraicGeometry.fiberCompι_comp_fiberι`
turns that into a composite ending in `hU.fromSpec`, whose range is `U` by
`AlgebraicGeometry.IsAffineOpen.range_fromSpec`. That gives the containment only.
`AlgebraicGeometry.range_fiberCompι` computes the range instead, as the base change of an open
immersion (`AlgebraicGeometry.IsOpenImmersion.range_pullbackSnd`), and so gives the equality;
the containment is then `le_of_eq`. The equality is what a consumer holding a *given* point of
the generic fibre needs, and the containment cannot supply it.

The statement is made at the variable point of `AlgebraicGeometry.fiberChartι` and only then
instantiated at the generic point, for the reason recorded in `GenericFibreChart.lean`: with the
point a variable the transport in the definition is removed by `subst`, while at a named point it
cannot be.

`AlgebraicGeometry.fiberAppLEι` is `AlgebraicGeometry.fiberCompι` preceded by
`AlgebraicGeometry.specMapFiberIsoSpecFiberRing` and
`AlgebraicGeometry.fiberAppLEIsoFiberComp`; the three leg computations above, with
`AlgebraicGeometry.fiberCompι_comp_fiberι`, compute
`fiberAppLEι f hV hU e q ≫ f.fiberι (hV.fromSpec q)` — that is
`AlgebraicGeometry.fiberAppLEι_comp_fiberι`, the chart square. That composite is what identifies
`AlgebraicGeometry.genericFiberChartSections` on the image of `Γ(X, U)` — the one equation that,
by `AlgebraicGeometry.eq_stalkFiberBotToGenericStalk_comp_chartFiberBotToStalkFiberBot`, pins the
chart coordinate down inside the function field.

The last of the legs cannot be proved by rewriting. Its statement contains
`(Spec.map φ).fiber q` with `q` a `PrimeSpectrum`, which is a point of `Spec` only up to
unfolding, so once the composite isomorphism is unfolded `simp` and `rw` refuse the goal as not
type-correct at `implicit` transparency; Mathlib's own results in this area carry
`set_option backward.isDefEq.respectTransparency false` for exactly this reason, and that option
is not available here. `AlgebraicGeometry.pullback_fst_eq_trans_hom_comp` is the way round: the
whole rewriting is done once in an abstract category, where the point does not occur, and the
instantiation is a single `exact` whose unification never checks a motive.

`AlgebraicGeometry.genericFiberChartOpens` exists because `AlgebraicGeometry.Scheme.Hom.opensRange`
takes the open immersion as an instance argument and
`AlgebraicGeometry.isOpenImmersion_genericFiberChartι` is not one; the definition binds it once.

No tag attribute: each statement below carries an affine chart, which [Stacks, Tag 0BD7] does not.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open Stacks.RingedSpace Stacks.SheafOfModules

namespace AlgebraicGeometry

/-- **The fibre of `j ≫ f` maps to the fibre of `f` over `j`.** Both sides of
`AlgebraicGeometry.fiberCompι` are projections of the pasted pullback squares, so this is
`CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_fst`. -/
theorem fiberCompι_comp_fiberι {X' X Y : Scheme.{u}} (j : X' ⟶ X) (f : X ⟶ Y) (y : Y) :
    fiberCompι j f y ≫ f.fiberι y = (j ≫ f).fiberι y ≫ j :=
  (Category.assoc _ _ _).trans
    (pullbackRightPullbackFstIso_inv_snd_fst f (Y.fromSpecResidueField y) j)

/-- **`AlgebraicGeometry.fiberCompIsoFiber` commutes with the inclusion of the fibre.** Both
isomorphisms it is built from are `CategoryTheory.Limits.pullback.map`s whose first component is
the identity, and the inclusion of a fibre is the first projection. -/
theorem fiberCompIsoFiber_hom_fiberι {X' V' Y : Scheme.{u}} (g : X' ⟶ V') (m : V' ⟶ Y)
    [IsOpenImmersion m] (v : V') :
    (fiberCompIsoFiber g m v).hom ≫ (g ≫ m).fiberι (m v) = g.fiberι v := by
  simp only [fiberCompIsoFiber, Scheme.Hom.fiberι, Scheme.Hom.fiber, pullback.map, asIso,
    Iso.trans_hom, Category.comp_id, Category.assoc]
  rw [pullback.lift_fst, pullback.lift_fst]

/-- **Transporting a presentation of a fibre along an equality of morphisms does not change the
inclusion of the fibre.** The equality is between morphisms and cannot be `subst`ed where it
occurs inside a definition, so it is made a hypothesis here, where it can be. -/
theorem fiber_transport_hom_fiberι {X Y : Scheme.{u}} {a b : X ⟶ Y} (h : a = b) (y : Y)
    {Z : Scheme.{u}} (i : Z ≅ a.fiber y) :
    (h ▸ i : Z ≅ b.fiber y).hom ≫ b.fiberι y = i.hom ≫ a.fiberι y := by
  subst h
  rfl

/-- **`AlgebraicGeometry.fiberAppLEIsoFiberComp` commutes with the inclusion of the fibre.** The
transport in its definition is removed by `AlgebraicGeometry.fiber_transport_hom_fiberι` and
what is left is `AlgebraicGeometry.fiberCompIsoFiber_hom_fiberι`. -/
theorem fiberAppLEIsoFiberComp_hom_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (q : PrimeSpectrum ↑Γ(Y, V)) :
    (fiberAppLEIsoFiberComp f hV hU e q).hom ≫ (hU.fromSpec ≫ f).fiberι (hV.fromSpec q) =
      (Spec.map (f.appLE V U e)).fiberι q :=
  (fiber_transport_hom_fiberι (IsAffineOpen.SpecMap_appLE_fromSpec f hV hU e) _ _).trans
    (fiberCompIsoFiber_hom_fiberι (Spec.map (f.appLE V U e)) hV.fromSpec q)

/-- **The first projection of a pullback, read through the composite isomorphism
`AlgebraicGeometry.Spec.fiberToSpecResidueFieldIso` is built from.** Stated in an abstract
category: at the instantiation below the goal admits no rewriting at all. -/
private theorem pullback_fst_eq_trans_hom_comp {C : Type*} [Category C] {X Y Y' Z T : C}
    {f : X ⟶ Z} {g : Y ⟶ Z} {g' : Y' ⟶ Z} {j : Y ⟶ Y'} [IsIso j] (hg : g = j ≫ g')
    [HasPullback f g] [HasPullback g f] [HasPullback (j ≫ g') f] [HasPullback g' f]
    {D : pullback g' f ≅ T} {k : T ⟶ X} (hD : D.hom ≫ k = pullback.snd g' f)
    (e₁ : (j ≫ g') ≫ 𝟙 Z = j ≫ g') (e₂ : f ≫ 𝟙 Z = 𝟙 X ≫ f) :
    pullback.fst f g =
      (pullbackSymmetry f g ≪≫
          (pullback.congrHom hg rfl ≪≫
            asIso (pullback.map (j ≫ g') f g' f j (𝟙 X) (𝟙 Z) e₁ e₂)) ≪≫ D).hom ≫ k := by
  subst hg
  simp only [Iso.trans_hom, Category.assoc, hD, asIso_hom, pullback.lift_snd, Category.comp_id,
    pullback.congrHom_hom, pullbackSymmetry_hom_comp_snd]

/-- **`Spec (Ideal.Fiber 𝔭 S)` sits inside `Spec S` as the spectrum of `S → Ideal.Fiber 𝔭 S`.**
Composing the inverse of `AlgebraicGeometry.specMapFiberIsoSpecFiberRing` with the inclusion of
the fibre is the spectrum of the algebra map into the fibre ring. -/
theorem specMapFiberIsoSpecFiberRing_inv_fiberι {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (p : PrimeSpectrum R) :
    letI : Algebra S (p.asIdeal.Fiber S) := Algebra.TensorProduct.rightAlgebra
    (specMapFiberIsoSpecFiberRing (R := R) (S := S) p).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι p =
      Spec.map (CommRingCat.ofHom (algebraMap S (p.asIdeal.Fiber S))) := by
  refine (Iso.inv_comp_eq _).mpr ?_
  show Scheme.Hom.fiberι (Spec.map (CommRingCat.ofHom (algebraMap R S))) p =
      _ ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := p.asIdeal.ResidueField)
          (B := S)).toRingHom)
  simp only [specMapFiberIsoSpecFiberRing, asIso_hom, Spec.fiberToSpecResidueFieldIso,
    Arrow.isoMk', Arrow.isoMk, Comma.isoMk, Arrow.Hom.left, Scheme.Hom.fiberι]
  exact pullback_fst_eq_trans_hom_comp _
    (pullbackSpecIso_hom_snd R p.asIdeal.ResidueField S) _ _

/-- **The chart square commutes.** The chart of the fibre, followed into `X` by the inclusion of
the fibre, is the spectrum of `Γ(X, U) → Ideal.Fiber 𝔮 Γ(X, U)` followed by `hU.fromSpec`. -/
theorem fiberAppLEι_comp_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (q : PrimeSpectrum ↑Γ(Y, V)) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Algebra ↑Γ(X, U) (q.asIdeal.Fiber ↑Γ(X, U)) := Algebra.TensorProduct.rightAlgebra
    fiberAppLEι f hV hU e q ≫ f.fiberι (hV.fromSpec q) =
      Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, U) (q.asIdeal.Fiber ↑Γ(X, U)))) ≫
        hU.fromSpec := by
  let : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let : Algebra ↑Γ(X, U) (q.asIdeal.Fiber ↑Γ(X, U)) := Algebra.TensorProduct.rightAlgebra
  have hmor : fiberAppLEι f hV hU e q ≫ f.fiberι (hV.fromSpec q) =
      ((specMapFiberIsoSpecFiberRing (R := ↑Γ(Y, V)) (S := ↑Γ(X, U)) q).inv ≫
        (fiberAppLEIsoFiberComp f hV hU e q).hom ≫
          (hU.fromSpec ≫ f).fiberι (hV.fromSpec q)) ≫ hU.fromSpec := by
    rw [fiberAppLEι, Category.assoc, Category.assoc, Category.assoc, Category.assoc,
      fiberCompι_comp_fiberι]
  refine hmor.trans (congrArg (· ≫ hU.fromSpec) ?_)
  exact (congrArg
    (fun m => (specMapFiberIsoSpecFiberRing (R := ↑Γ(Y, V)) (S := ↑Γ(X, U)) q).inv ≫ m)
      (fiberAppLEIsoFiberComp_hom_fiberι f hV hU e q)).trans
    (specMapFiberIsoSpecFiberRing_inv_fiberι q)

/-- Precomposing with an isomorphism does not change the range on underlying spaces. -/
private theorem range_base_iso_comp {A B C : Scheme.{u}} (i : A ⟶ B) [IsIso i] (m : B ⟶ C) :
    Set.range (i ≫ m).base = Set.range m.base :=
  (Scheme.homeoOfIso (asIso i)).surjective.range_comp _

/-- **The range of `AlgebraicGeometry.fiberCompι` for an open immersion `j`**: the fibre of
`j ≫ f` is exactly the part of the fibre of `f` lying over the range of `j`, being the base
change of `j` along `f.fiberι y` up to an isomorphism of the source. -/
theorem range_fiberCompι {X' X Y : Scheme.{u}} (j : X' ⟶ X) [IsOpenImmersion j] (f : X ⟶ Y)
    (y : Y) :
    Set.range (fiberCompι j f y).base = ↑(f.fiberι y ⁻¹ᵁ j.opensRange) :=
  (range_base_iso_comp (pullbackRightPullbackFstIso f (Y.fromSpecResidueField y) j).inv _).trans
    (IsOpenImmersion.range_pullbackSnd j (pullback.fst f (Y.fromSpecResidueField y)))

/-- **The range of `AlgebraicGeometry.fiberAppLEι`**: the chart of the fibre is the whole of the
part of the fibre lying over `U`, the two isomorphisms in front of
`AlgebraicGeometry.fiberCompι` being surjective. -/
theorem range_fiberAppLEι {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (q : PrimeSpectrum ↑Γ(Y, V)) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    Set.range (fiberAppLEι f hV hU e q).base = ↑(f.fiberι (hV.fromSpec q) ⁻¹ᵁ U) := by
  let : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  rw [fiberAppLEι, range_base_iso_comp, range_base_iso_comp,
    range_fiberCompι, hU.opensRange_fromSpec]

/-- **The affine open of the generic fibre an affine chart cuts out**, namely the range of
`AlgebraicGeometry.genericFiberChartι`. Its ring of sections is `Ideal.Fiber ⊥ Γ(X, U)`. -/
noncomputable def genericFiberChartOpens {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y] {x : X}
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (hx : x ∈ U) : (f.fiber (genericPoint Y)).Opens :=
  letI := isOpenImmersion_genericFiberChartι f hV hU e hx
  Scheme.Hom.opensRange (genericFiberChartι f hV hU e hx)

/-- **The range of `AlgebraicGeometry.fiberChartι`.** With the point of the target a variable
the equation substitutes away and this is `AlgebraicGeometry.range_fiberAppLEι`. -/
theorem range_fiberChartι {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (q : PrimeSpectrum ↑Γ(Y, V)) (y : Y) (hy : hV.fromSpec q = y) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    Set.range (fiberChartι f hV hU e q y hy).base = ↑(f.fiberι y ⁻¹ᵁ U) := by
  let : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  subst hy
  exact range_fiberAppLEι f hV hU e q

/-- **The chart square at a named point of the target.** With the point a variable the equation
substitutes away and this is `AlgebraicGeometry.fiberAppLEι_comp_fiberι`. -/
theorem fiberChartι_comp_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (q : PrimeSpectrum ↑Γ(Y, V)) (y : Y) (hy : hV.fromSpec q = y) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Algebra ↑Γ(X, U) (q.asIdeal.Fiber ↑Γ(X, U)) := Algebra.TensorProduct.rightAlgebra
    fiberChartι f hV hU e q y hy ≫ f.fiberι y =
      Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, U) (q.asIdeal.Fiber ↑Γ(X, U)))) ≫
        hU.fromSpec := by
  let : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let : Algebra ↑Γ(X, U) (q.asIdeal.Fiber ↑Γ(X, U)) := Algebra.TensorProduct.rightAlgebra
  subst hy
  exact fiberAppLEι_comp_fiberι f hV hU e q

/-- **The chart of the fibre lies over `U`.** Every point of `Spec (Ideal.Fiber 𝔮 Γ(X, U))` is
carried by `AlgebraicGeometry.fiberChartι` to a point of the fibre lying over a point of `U`,
because the chart morphism factors through `hU.fromSpec`. -/
theorem fiberι_fiberChartι_mem {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (q : PrimeSpectrum ↑Γ(Y, V)) (y : Y) (hy : hV.fromSpec q = y) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    ∀ p : Spec (CommRingCat.of (q.asIdeal.Fiber ↑Γ(X, U))),
      (f.fiberι y).base ((fiberChartι f hV hU e q y hy).base p) ∈ U :=
  let : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let : Algebra ↑Γ(X, U) (q.asIdeal.Fiber ↑Γ(X, U)) := Algebra.TensorProduct.rightAlgebra
  fun p => hU.range_fromSpec.subset
    ⟨_, congrArg (fun m : Spec (CommRingCat.of (q.asIdeal.Fiber ↑Γ(X, U))) ⟶ X => m.base p)
      (fiberChartι_comp_fiberι f hV hU e q y hy).symm⟩

/-- The zero prime of `Γ(Y, V)` is sent to the generic point, `V` containing the image of `x`. -/
private theorem fromSpec_bot_eq_genericPoint {X Y : Scheme.{u}} {f : X ⟶ Y} [IsIntegral Y]
    {x : X} {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) (hx : x ∈ U)
    [Nonempty ↥(V.toScheme)] [IsDomain ↑Γ(Y, V)] :
    hV.fromSpec (⊥ : PrimeSpectrum ↑Γ(Y, V)) = genericPoint Y :=
  fromSpec_eq_genericPoint_of_asIdeal_eq_bot hV (e hx) _ rfl

/-- **The chart square of the generic fibre.** The chart of the generic fibre, followed into `X`,
is the spectrum of `Γ(X, U) → Ideal.Fiber ⊥ Γ(X, U)` followed by `hU.fromSpec`. -/
theorem genericFiberChartι_comp_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y] {x : X}
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (hx : x ∈ U) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
    letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
    letI : Algebra ↑Γ(X, U) ((⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U)) :=
      Algebra.TensorProduct.rightAlgebra
    genericFiberChartι f hV hU e hx ≫ f.fiberι (genericPoint Y) =
      Spec.map (CommRingCat.ofHom
          (algebraMap ↑Γ(X, U) ((⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U)))) ≫ hU.fromSpec :=
  let : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  have : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
  have : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
  fiberChartι_comp_fiberι f hV hU e (⊥ : PrimeSpectrum ↑Γ(Y, V)) (genericPoint Y)
    (fromSpec_bot_eq_genericPoint hV e hx)

/-- **The chart of the generic fibre is exactly the part of the generic fibre lying over `U`.**
The fibre of `U ⟶ V` over the zero prime is the fibre of `f` over `ξ` restricted to `U`, so the
containment of `AlgebraicGeometry.genericFiberChartOpens_le` is an equality. This is what lets a
*given* point of the generic fibre — the one over the generic point of `X`, say — be placed in
the chart, which the containment alone cannot do. -/
theorem genericFiberChartOpens_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y] {x : X}
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (hx : x ∈ U) :
    genericFiberChartOpens f hV hU e hx = (f.fiberι (genericPoint Y)) ⁻¹ᵁ U := by
  let : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
  let : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
  exact Opens.ext <| range_fiberChartι f hV hU e (⊥ : PrimeSpectrum ↑Γ(Y, V)) (genericPoint Y)
    (fromSpec_bot_eq_genericPoint hV e hx)

/-- **The chart of the generic fibre lies over `U`.** -/
theorem genericFiberChartOpens_le {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y] {x : X}
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (hx : x ∈ U) :
    genericFiberChartOpens f hV hU e hx ≤ (f.fiberι (genericPoint Y)) ⁻¹ᵁ U :=
  le_of_eq (genericFiberChartOpens_eq f hV hU e hx)

/-- **A point of the generic fibre lying over `U` lies in the chart.** The converse of
`AlgebraicGeometry.genericFiberChartOpens_le`, from the equality above. -/
theorem mem_genericFiberChartOpens {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y] {x : X}
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (hx : x ∈ U) (x₀ : f.fiber (genericPoint Y))
    (hx₀ : (f.fiberι (genericPoint Y)).base x₀ ∈ U) :
    x₀ ∈ genericFiberChartOpens f hV hU e hx :=
  (genericFiberChartOpens_eq f hV hU e hx).ge hx₀

/-- **A trivialization of `ℒ` on an affine chart, read on the generic fibre.** The pullback of a
generator of `ℒ` on `U` along `f.fiberι ξ` generates `ℒ_ξ` on `(f.fiberι ξ) ⁻¹ᵁ U`, hence on the
affine open `AlgebraicGeometry.genericFiberChartOpens` inside it. -/
noncomputable def genericFiberChartGenerator {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral Y] {x : X} {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (e : U ≤ f ⁻¹ᵁ V) (hx : x ∈ U)
    (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))
    (hL : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L)
    (genU : GeneratorSections X.toRingedSpace L U) :
    GeneratorSections (f.fiber (genericPoint Y)).toRingedSpace
      ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L)
      (genericFiberChartOpens f hV hU e hx) :=
  generatorRestrict _ (genericFiberChartOpens_le f hV hU e hx)
    (pullbackGenerator (f.fiberι (genericPoint Y)) L hL U genU)

/-- **The identification the penultimate paragraph of [Stacks, Tag 0BD7] needs**: a generator of
`ℒ` on an affine chart `U` of `X` gives a generator of `ℒ_ξ` on the affine open of the generic
fibre whose ring is `Ideal.Fiber ⊥ Γ(X, U)`. -/
theorem nonempty_generatorSections_genericFiberChart {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral Y] {x : X} {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (e : U ≤ f ⁻¹ᵁ V) (hx : x ∈ U)
    (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))
    (hL : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L)
    (genU : GeneratorSections X.toRingedSpace L U) :
    Nonempty (GeneratorSections (f.fiber (genericPoint Y)).toRingedSpace
      ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L)
      (genericFiberChartOpens f hV hU e hx)) :=
  ⟨genericFiberChartGenerator f hV hU e hx L hL genU⟩

/-- **An affine chart at `x` carrying a generator of `ℒ`.** Every point of `X` lies in an affine
open `U` on which `ℒ` is trivial and which maps into an affine open `V` of `Y`: choose `V` around
`f x`, a trivializing open `W` around `x`, and an affine open inside `W ⊓ f ⁻¹ᵁ V`.

This is what makes the hypotheses of `AlgebraicGeometry.genericFiberChartGenerator` available at
every point of `X` from invertibility of `ℒ` alone. -/
theorem exists_affine_chart_generator_mem {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))
    (hL : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L) (x : X) :
    ∃ (V : Y.Opens) (U : X.Opens) (_ : IsAffineOpen V) (_ : IsAffineOpen U) (_ : U ≤ f ⁻¹ᵁ V),
      x ∈ U ∧ Nonempty (GeneratorSections X.toRingedSpace L U) := by
  have := hL
  obtain ⟨V, hV, hyV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := f x) (U := ⊤) trivial
  obtain ⟨W, hxW, a, ha⟩ := exists_bijective_smul_of_isInvertible L x
  obtain ⟨U, hU, hxU, hsub⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x)
    (U := W ⊓ f ⁻¹ᵁ V) ⟨hxW, hyV⟩
  exact ⟨V, U, hV, hU, hsub.trans inf_le_right, hxU,
    ⟨generatorRestrict L (hsub.trans inf_le_left) ⟨a, ha⟩⟩⟩

end AlgebraicGeometry

end
