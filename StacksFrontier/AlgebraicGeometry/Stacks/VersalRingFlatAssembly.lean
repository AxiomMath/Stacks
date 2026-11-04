module

public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingFlatChartPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingFieldExtensionRealization
public import StacksFrontier.Deformation.Artin.FormalObject.BaseContains

/-!
# Steps II and III of the proof of Stacks 0DR2

Step II of the source's proof: for a finite extension `l/k` and the induced point `x_{l,0}`, the
lemma holds at `x₀` if and only if it holds at `x_{l,0}`, because by **Stacks 0DQY** and part (2)
of **Stacks 0DR1** a versal ring `A` at `x₀` maps to a versal ring `A'` at `x_{l,0}` by a formally
smooth, hence faithfully flat, homomorphism compatible with the morphisms `Spec A' ⟶ Spec A ⟶ 𝒳`.
Step III: a point of a smooth chart is reached by two such steps, and there the morphism is
`Spec(𝒪^∧_{U, u₀}) ⟶ U ⟶ 𝒳`, which is flat.

The comparison of part (2) of Stacks 0DR1 is used through its consequence for flatness,
`AlgebraicGeometry.Stack.ExtensionRealizationComparison`: a realization of a versal formal object
at `x₀` receives a morphism, lying over a flat surjective morphism of schemes, from a realization
of a versal formal object at `x_{l,0}`. That consequence is proved in
`AlgebraicGeometry.Stack.extensionRealizationComparison` from part (2) of Stacks 0DR1 and
Stacks 07PM.

## Main definitions

* `AlgebraicGeometry.Stack.ExtensionRealizationComparison`: the consequence of part (2) of
  Stacks 0DR1 used in Step II.

## Main results

* `AlgebraicGeometry.Stack.realizationsFlatAt_of_extension` and
  `AlgebraicGeometry.Stack.realizationsFlatAt_extension_of_flat`: the two directions of Step II.
* `AlgebraicGeometry.Stack.flatObject_of_realization_of_extensionRealizationComparison`: Stacks
  0DR2 from that comparison.
* `AlgebraicGeometry.Stack.extensionRealizationComparison`: the comparison holds.
* `AlgebraicGeometry.Stack.flatObject_of_realization_of_isVersal`: **Stacks 0DR2**.

## References

* [Stacks Project, Tag 0DR2](https://stacks.math.columbia.edu/tag/0DR2)
* [Stacks Project, Tag 0DR1](https://stacks.math.columbia.edu/tag/0DR1)
* [Stacks Project, Tag 0DQY](https://stacks.math.columbia.edu/tag/0DQY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Stack

universe u w

variable (D : VersalSituation.{u, w})

/-- **The consequence of part (2) of Stacks 0DR1 used in Step II of the proof of Stacks 0DR2.**
For every realization `y` of a versal formal object at a point `x₀` over `Spec k`, every finite
extension `l/k` and every point `xₗ` over `Spec l` with a morphism `η : xₗ ⟶ x₀` over
`Spec l ⟶ Spec k`, there are a versal formal object at `xₗ`, a realization `y'` of it and a
morphism `y' ⟶ y` of `𝒳` lying over a flat surjective morphism of schemes. -/
def ExtensionRealizationComparison : Prop :=
  ∀ (Λ k l : Type u) [CommRing Λ] [Field k] [Field l] [Algebra Λ k] [Algebra k l] [Algebra Λ l]
    [IsScalarTower Λ k l] [Module.Finite k l]
    (iΛ : Spec (.of Λ) ⟶ D.S) (_hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection),
    Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ →
    ∀ (hA : D.B.Contains (Spec (.of ξ.base))) (y : D.𝒳.val.val.obj)
      (hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
        (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA),
      (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
        hfinite ξ).Realization hA y hy →
    ∀ (xₗ : D.𝒳.val.val.obj)
      (hxₗ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xₗ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
      (η : xₗ ⟶ x₀),
      eqToHom (congrArg Over.left hxₗ).symm ≫
          ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η).left ≫
        eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k l)) →
      ∃ (ξ' : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
          (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) xₗ hxₗ).projection)
        (_ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
          D.B D.hS iΛ D.𝒳.val.val.p xₗ hxₗ D.𝒳.val.property).cofibered ξ')
        (hA' : D.B.Contains (Spec (.of ξ'.base))) (y' : D.𝒳.val.val.obj)
        (hy' : D.𝒳.val.val.p.obj y' = Deformation.Artin.baseOver D.B D.S D.hS
          (Deformation.Artin.completeLocalAlgFormalBase iΛ
            (locallyOfFiniteType_and_quasiCompact_fieldExtension iΛ hfinite) ξ'.base) hA')
        (_ : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p xₗ
          hxₗ (locallyOfFiniteType_and_quasiCompact_fieldExtension iΛ hfinite) ξ').Realization
            hA' y' hy')
        (m : y' ⟶ y),
        Flat (D.B.inclusion.map (D.𝒳.val.val.p.map m).left) ∧
          Surjective (D.B.inclusion.map (D.𝒳.val.val.p.map m).left)

variable {D}

/-- **Step II of the proof of Stacks 0DR2, from the extension to the point.** If the conclusion
holds at the point `xₗ` over a finite extension `l/k`, it holds at `x₀`: every realization at
`x₀` receives a morphism lying over a flat surjective morphism from a realization at `xₗ`, which
is flat, and flatness descends (Stacks 06Q0). -/
theorem realizationsFlatAt_of_extension (H : ExtensionRealizationComparison D)
    {Λ k l : Type u} [CommRing Λ] [Field k] [Field l] [Algebra Λ k] [Algebra k l] [Algebra Λ l]
    [IsScalarTower Λ k l] [Module.Finite k l]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (xₗ : D.𝒳.val.val.obj)
    (hxₗ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (η : xₗ ⟶ x₀)
    (hη : eqToHom (congrArg Over.left hxₗ).symm ≫
        ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k l)))
    (hl : RealizationsFlatAt D xₗ l) :
    ∀ (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection),
    Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ →
    ∀ (hA : D.B.Contains (Spec (.of ξ.base))) (y : D.𝒳.val.val.obj)
      (hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
        (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA),
      (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
        hfinite ξ).Realization hA y hy →
      flatObject D.B D.S D.hS D.𝒳.val y := by
  intro ξ hξ hA y hy Ry
  obtain ⟨ξ', hξ', hA', y', hy', Ry', m, hmflat, hmsurj⟩ :=
    H Λ k l iΛ hiΛ x₀ hx₀ hfinite ξ hξ hA y hy Ry xₗ hxₗ η hη
  exact flatObject_of_flat_of_surjective D.B D.S D.hS D.𝒳 m hmflat hmsurj
    (hl Λ iΛ hiΛ hxₗ _ ξ' hξ' hA' y' hy' Ry')

/-- **Step II of the proof of Stacks 0DR2, from the point to the extension.** If one realization
of one versal formal object at `x₀` is flat, the conclusion holds at the point `xₗ` over a finite
extension `l/k`: the realization at `xₗ` provided by the comparison maps to it over a flat
morphism, so it is flat (Stacks 06PX), and Step I spreads flatness. -/
theorem realizationsFlatAt_extension_of_flat (H : ExtensionRealizationComparison D)
    {Λ k l : Type u} [CommRing Λ] [Field k] [Field l] [Algebra Λ k] [Algebra k l] [Algebra Λ l]
    [IsScalarTower Λ k l] [Module.Finite k l]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ)
    {hA : D.B.Contains (Spec (.of ξ.base))} {y : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy)
    (hyflat : flatObject D.B D.S D.hS D.𝒳.val y)
    (xₗ : D.𝒳.val.val.obj)
    (hxₗ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (η : xₗ ⟶ x₀)
    (hη : eqToHom (congrArg Over.left hxₗ).symm ≫
        ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k l))) :
    RealizationsFlatAt D xₗ l := by
  obtain ⟨ξ', hξ', hA', y', hy', Ry', m, hmflat, -⟩ :=
    H Λ k l iΛ hiΛ x₀ hx₀ hfinite ξ hξ hA y hy Ry xₗ hxₗ η hη
  exact realizationsFlatAt_of_flatObject D xₗ iΛ hiΛ hxₗ _ ξ' hξ' Ry'
    (flatObject_of_flat D.B D.S D.hS D.𝒳 m hmflat hyflat)

/-- **Stacks 0DR2, from the comparison of part (2) of Stacks 0DR1.** In the versal situation, let
`x₀` be a point of `𝒳` over `Spec k ⟶ Spec Λ ⟶ S` with `k` of finite type over `S`, and let `ξ`
be a versal formal object at `x₀` with a realization `y`, the morphism `Spec A ⟶ 𝒳` of Stacks
0DR1. Then `y` is a flat object.

Step III: there are a finite extension `l/k`, a point `xₗ ⟶ x₀` over it, and the versal flat
completion of a smooth chart whose closed fibre receives `xₗ` over a finite extension
(`AlgebraicGeometry.Stack.exists_chartPoint_closedFibre`). The conclusion holds at that closed
fibre (`AlgebraicGeometry.Stack.exists_flat_realization_closedFibre`), passes to `xₗ` and from
there to `x₀` by the two directions of Step II. -/
theorem flatObject_of_realization_of_extensionRealizationComparison
    (H : ExtensionRealizationComparison D)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ)
    {hA : D.B.Contains (Spec (.of ξ.base))} {y : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy) :
    flatObject D.B D.S D.hS D.𝒳.val y := by
  obtain ⟨l, _, _, _, _, hkl, xₗ, hxₗ, η, hη, xR, ζ, hζ, alg, hΛ, hxRflat, hζversal,
    _, _, hfin, η', hη'⟩ := exists_chartPoint_closedFibre D iΛ hiΛ x₀ hx₀ hfinite
  obtain ⟨hAc, yc, hyc, ⟨Ryc⟩, hycflat⟩ :=
    exists_flat_realization_closedFibre D xR hxRflat ζ hζ Λ iΛ hΛ hζversal
  have hl : RealizationsFlatAt D xₗ l :=
    realizationsFlatAt_extension_of_flat H iΛ hiΛ (ζ.level 0) (ζ.basePoint Λ iΛ hΛ)
      (locallyOfFiniteType_and_quasiCompact_residueField_formalBase D ζ Λ iΛ hΛ) _ hζversal
      Ryc hycflat xₗ hxₗ η' hη'
  exact realizationsFlatAt_of_extension H iΛ hiΛ x₀ hx₀ hfinite xₗ hxₗ η hη hl ξ hξ hA y hy Ry

variable (D) in
/-- **The comparison of Step II holds**, by part (2) of **Stacks 0DR1**
(`AlgebraicGeometry.Stack.exists_isVersalRingAt_fieldExtension_realization`): the versal formal
object `ξₗ` at `xₗ` it produces over `A'` has a realization, its complete local base being in the
site (`Deformation.Artin.FormalObject.contains_spec_base`); that realization maps to `y` over
`Spec A' ⟶ Spec A` for the formally smooth local homomorphism `A → A'`, and this morphism of
spectra is flat and surjective by **Stacks 07PM**. -/
theorem extensionRealizationComparison : ExtensionRealizationComparison D := by
  intro Λ k l _ _ _ _ _ _ _ _ iΛ hiΛ x₀ hx₀ hfinite ξ hξ hA y hy Ry xₗ hxₗ η hη
  obtain ⟨ξₗ, f, hv, hloc, -, hsm, hex, hhom⟩ :=
    exists_isVersalRingAt_fieldExtension_realization D iΛ hiΛ x₀ hx₀ hfinite xₗ hxₗ η hη ξ hξ Ry
  let hfinite' := locallyOfFiniteType_and_quasiCompact_fieldExtension (k := k) (l := l) iΛ hfinite
  have hA' : D.B.Contains (Spec (.of ξₗ.base)) :=
    (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p xₗ hxₗ
      hfinite' ξₗ).contains_spec_base
  obtain ⟨y', hy', ⟨Ry'⟩⟩ := hex hA'
  obtain ⟨m, hm⟩ := hhom Ry'
  have : IsLocalHom f.toRingHom := hloc
  obtain ⟨hfl, hsu⟩ := flat_and_surjective_specMap_of_formallySmoothNAdic f.toRingHom hsm
  have key : ∀ {X Y U V : BigFppfOver D.B D.S D.hS} (hX : X = U) (hY : Y = V) (g : X ⟶ Y)
      {ψ : (BigFppfOver.toScheme D.B D.S D.hS).obj U ⟶ (BigFppfOver.toScheme D.B D.S D.hS).obj V},
      (BigFppfOver.toScheme D.B D.S D.hS).map (eqToHom hX.symm ≫ g ≫ eqToHom hY) = ψ →
      Flat ψ ∧ Surjective ψ →
      Flat (D.B.inclusion.map g.left) ∧ Surjective (D.B.inclusion.map g.left) := by
    intro X Y U V hX hY g ψ h hψ
    subst hX hY
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
    show Flat ((BigFppfOver.toScheme D.B D.S D.hS).map g) ∧
      Surjective ((BigFppfOver.toScheme D.B D.S D.hS).map g)
    rw [h]
    exact hψ
  exact ⟨ξₗ, hv, hA', y', hy', Ry', m, key hy' hy _ hm ⟨hfl, hsu⟩⟩

/-- **Stacks 0DR2.** In Situation 0DQU — `𝒳` an algebraic stack locally of finite type over a
locally Noetherian scheme `S` — let `x₀ : Spec k ⟶ 𝒳` be a point with `k` a field of finite type
over `S`, presented over an affine open `Spec Λ ⊆ S`, and let `A` be a versal ring to `𝒳` at
`x₀`, with versal formal object `ξ` over `A`. Then the morphism `Spec A ⟶ 𝒳` of Stacks 0DR1 —
any object `y` of `𝒳` over `Spec A` realizing `ξ`, i.e. whose restrictions to the infinitesimal
thickenings of the closed point are the levels of `ξ` — is flat.

The proof is the source's: Step III reaches a point of a smooth chart, where the morphism is
`Spec(𝒪^∧_{U, u₀}) ⟶ U ⟶ 𝒳`, through two field extensions, and Steps I and II carry flatness
back along the faithfully flat comparisons of parts (1) and (2) of Stacks 0DR1. -/
@[stacks 0DR2]
theorem flatObject_of_realization_of_isVersal
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ)
    {hA : D.B.Contains (Spec (.of ξ.base))} {y : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy) :
    flatObject D.B D.S D.hS D.𝒳.val y :=
  flatObject_of_realization_of_extensionRealizationComparison (extensionRealizationComparison D)
    iΛ hiΛ x₀ hx₀ hfinite ξ hξ Ry

end AlgebraicGeometry.Stack

end
