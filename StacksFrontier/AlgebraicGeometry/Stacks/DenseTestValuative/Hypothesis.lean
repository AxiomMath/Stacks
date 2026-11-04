module

public import StacksFrontier.AlgebraicGeometry.Stacks.DenseTestValuative.SchemeTwoCells
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterion

/-!
# The valuative hypothesis of Stacks 0CQM and its transfer along a lift

Let `f : 𝒳 ⟶ 𝒴` and `h : 𝒰 ⟶ 𝒳` be 1-morphisms of algebraic stacks over `S`. **Stacks 0CQM**
asks, of every 2-commutative diagram
```
Spec K --u--> 𝒰 --h--> 𝒳
  |j                    |f
  v                     v
Spec A -------y-------> 𝒴
```
with `A` a discrete valuation ring with fraction field `K` and `γ : y ∘ j → f ∘ h ∘ u`, that
after an extension `K'/K` of fields and a valuation ring `A' ⊂ K'` dominating `A` the category
of dotted arrows of the induced square for `f` be nonempty.

## Main definitions

* `AlgebraicGeometry.Stack.ValuativeCriterion.DenseTestExistence`: that hypothesis.

## Main results

* `AlgebraicGeometry.Stack.ValuativeCriterion.denseTestExistence_of_lift`: the hypothesis is
  inherited by a pair `h' : 𝒰' ⟶ 𝒳'`, `f' : 𝒳' ⟶ 𝒴` with target represented by a scheme, given
  1-morphisms `u : 𝒰' ⟶ 𝒰` and `π : 𝒳' ⟶ 𝒳` with `h' ≫ π ≅ u ≫ h` and `f' ≅ π ≫ f`, as soon as
  `π` satisfies the existence part of the valuative criterion (**Stacks 0CLK**).

## Implementation notes

A diagram as above is a valuative square (`AlgebraicGeometry.Stack.ValuativeSquare`) for the
composite `h ≫ f`, whose generic point is `u`; the square for `f` it induces is
`AlgebraicGeometry.Stack.ValuativeSquare.compRight`, with generic point `u ≫ h`. The hypothesis
is the existence part of the valuative criterion (Stacks 0CLK) for those squares only, with the
extra clause that the valuation ring be discrete; the dominating valuation ring is not asked to
be discrete.

The transfer is the proof of **Stacks 0CLM**: a square for `h' ≫ f'` is read as one for `h ≫ f`
through `u`, the hypothesis gives a dotted arrow to `𝒳`, the square it leaves behind for `π` is
filled by the existence part of the valuative criterion for `π`, and the two extensions are
composed by `AlgebraicGeometry.Stack.ValuativeSquare.exists_of_rebase`. When the target is
represented by an object of the site the compatibility triangle of the resulting dotted arrow
holds automatically, by `AlgebraicGeometry.Stack.subsingleton_hom₂_schemeFibredCategory`; this is
the only case the proof of Stacks 0CQM needs.

## References

* [Stacks Project, Tag 0CQM](https://stacks.math.columbia.edu/tag/0CQM)
* [Stacks Project, Tag 0CLK](https://stacks.math.columbia.edu/tag/0CLK)
* [Stacks Project, Tag 0CLM](https://stacks.math.columbia.edu/tag/0CLM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace ValuativeCriterion

/-- **The hypothesis of Stacks 0CQM.** For 1-morphisms `h : 𝒰 ⟶ 𝒳` and `f : 𝒳 ⟶ 𝒴` of algebraic
stacks over `S`: every valuative square for `h ≫ f` whose valuation ring is a discrete valuation
ring — that is, a 2-commutative diagram `Spec K ⟶ 𝒰 ⟶ 𝒳 ⟶ 𝒴`, `Spec A ⟶ 𝒴` — admits, after an
extension of the fraction field and passage to a dominating valuation ring, a dotted arrow for
the induced square for `f` (`AlgebraicGeometry.Stack.ValuativeSquare.compRight`). -/
abbrev DenseTestExistence {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (h : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴) :
    Prop :=
  ∀ q : ValuativeSquare B S hS (h ≫ f), IsDiscreteValuationRing q.R →
    ∃ e : (ValuativeSquare.compRight B S hS q).DominatingExtension,
      Nonempty (DottedArrow (e.k ≫ (ValuativeSquare.compRight B S hS q).x) e.j f.hom
        (e.a ≫ (ValuativeSquare.compRight B S hS q).y) e.inducedGamma)

end ValuativeCriterion

namespace ValuativeSquare

variable {𝒰 𝒳 𝒴 𝒰' 𝒳' : AlgebraicStacks.{u, w} B S hS}
  {h : 𝒰 ⟶ 𝒳} {f : 𝒳 ⟶ 𝒴} {h' : 𝒰' ⟶ 𝒳'} {f' : 𝒳' ⟶ 𝒴} {u : 𝒰' ⟶ 𝒰} {π : 𝒳' ⟶ 𝒳}

/-- A valuative square for `h' ≫ f'`, read as a valuative square for `h ≫ f` through `u`. -/
@[implicit_reducible]
noncomputable def throughLift (σ : h' ≫ π ≅ u ≫ h) (τ : f' ≅ π ≫ f)
    (q : ValuativeSquare B S hS (h' ≫ f')) : ValuativeSquare B S hS (h ≫ f) :=
  { q with
    x := q.x ≫ u.hom
    γ := q.γ ≫ (q.x ◁ (h'.hom ◁ τ.hom.hom)) ≫ (q.x ◁ (α_ h'.hom π.hom f.hom).inv) ≫
      (q.x ◁ (σ.hom.hom ▷ f.hom)) ≫ (q.x ◁ (α_ u.hom h.hom f.hom).hom) ≫
      (α_ q.x u.hom (h.hom ≫ f.hom)).inv }

/-- The valuative square for `π` left behind by a dotted arrow for the square for `f` induced by
`throughLift`. -/
@[implicit_reducible]
noncomputable def throughLiftUpper (σ : h' ≫ π ≅ u ≫ h) (τ : f' ≅ π ≫ f)
    (q : ValuativeSquare B S hS (h' ≫ f'))
    (e₁ : (compRight B S hS (throughLift B S hS σ τ q)).DominatingExtension)
    (d₁ : DottedArrow (e₁.k ≫ (compRight B S hS (throughLift B S hS σ τ q)).x) e₁.j f.hom
      (e₁.a ≫ (compRight B S hS (throughLift B S hS σ τ q)).y) e₁.inducedGamma) :
    ValuativeSquare B S hS π where
  R := e₁.R'
  K := e₁.K'
  ring_mem := e₁.ring_mem
  field_mem := e₁.field_mem
  base := Spec.map (CommRingCat.ofHom e₁.ringMap) ≫ q.base
  genericMap := e₁.genericMap
  genericMap_left := e₁.genericMap_left
  j := e₁.j
  j_canonical := e₁.j_canonical
  x := e₁.k ≫ q.x ≫ h'.hom
  y := d₁.a
  γ := d₁.α ≫ (e₁.k ◁ (α_ q.x u.hom h.hom).hom) ≫ (e₁.k ◁ (q.x ◁ σ.inv.hom)) ≫
    (e₁.k ◁ (α_ q.x h'.hom π.hom).inv) ≫ (α_ e₁.k (q.x ≫ h'.hom) π.hom).inv

end ValuativeSquare

namespace ValuativeCriterion

open ValuativeSquare

variable {𝒰 𝒳 𝒴 𝒰' 𝒳' : AlgebraicStacks.{u, w} B S hS}

/-- **The hypothesis of Stacks 0CQM transfers along a lift.** Let `h : 𝒰 ⟶ 𝒳`, `f : 𝒳 ⟶ 𝒴`
satisfy the hypothesis of Stacks 0CQM, and let `h' : 𝒰' ⟶ 𝒳'`, `f' : 𝒳' ⟶ 𝒴` be such that
`h' ≫ π ≅ u ≫ h` and `f' ≅ π ≫ f` for 1-morphisms `u : 𝒰' ⟶ 𝒰` and `π : 𝒳' ⟶ 𝒳`. If `π`
satisfies the existence part of the valuative criterion and the 2-morphisms into `𝒴` from
represented categories fibred in groupoids form subsingletons — as they do when `𝒴` is
represented by an object of the site — then `h'`, `f'` satisfy the hypothesis of Stacks 0CQM. -/
theorem denseTestExistence_of_lift {h : 𝒰 ⟶ 𝒳} {f : 𝒳 ⟶ 𝒴} {h' : 𝒰' ⟶ 𝒳'} {f' : 𝒳' ⟶ 𝒴}
    (u : 𝒰' ⟶ 𝒰) (π : 𝒳' ⟶ 𝒳) (σ : h' ≫ π ≅ u ≫ h) (τ : f' ≅ π ≫ f)
    (hthin : ∀ (T : BigFppfOver B S hS) (F G : schemeFibredCategory B S hS T ⟶ 𝒴.val),
      Subsingleton (F ⟶ G))
    (hπ : ValuativeCriterion.Existence B S hS π)
    (hlift : DenseTestExistence B S hS h f) :
    DenseTestExistence B S hS h' f' := by
  intro q hq
  obtain ⟨e₁, ⟨d₁⟩⟩ := hlift (throughLift B S hS σ τ q) hq
  obtain ⟨e₂, ⟨d₂⟩⟩ := hπ (throughLiftUpper B S hS σ τ q e₁ d₁)
  refine exists_of_rebase B S hS (compRight B S hS q) e₂.R' e₂.K'
    (e₂.ringMap.comp e₁.ringMap) (e₂.fieldMap.comp e₁.fieldMap)
    ⟨fun a ha => e₁.isLocalHom.map_nonunit a
      (e₂.isLocalHom.map_nonunit _ ha)⟩ ?_ e₂.ring_mem e₂.field_mem
    (Spec.map (CommRingCat.ofHom e₂.ringMap) ≫
      Spec.map (CommRingCat.ofHom e₁.ringMap) ≫ q.base) ?_
    (Spec.map (CommRingCat.ofHom (algebraMap e₂.R' e₂.K')) ≫
      Spec.map (CommRingCat.ofHom e₂.ringMap) ≫
        Spec.map (CommRingCat.ofHom e₁.ringMap) ≫ q.base) rfl
    (e₂.specialOver ≫ e₁.specialOver) ?_
    (e₂.genericOver ≫ e₁.genericOver) ?_
    e₂.genericMap e₂.genericMap_left
    e₂.j e₂.j_canonical
    (e₂.a ≫ e₁.a) ?_
    (e₂.k ≫ e₁.k) ?_
    ((α_ e₂.j e₂.a e₁.a).inv ≫ (e₂.commute ▷ e₁.a) ≫ (α_ e₂.k e₁.j e₁.a).hom ≫
      (e₂.k ◁ e₁.commute) ≫ (α_ e₂.k e₁.k q.j).inv) ?_
  · ext x
    have h1 := RingHom.congr_fun e₁.fraction_comm x
    have h2 := RingHom.congr_fun e₂.fraction_comm (e₁.ringMap x)
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    exact h2.trans (congrArg e₂.fieldMap h1)
  · exact (congrArg (· ≫ q.base) (specMap_ofHom_comp e₁.ringMap e₂.ringMap)).trans
      (Category.assoc _ _ _)
  · refine Eq.trans (B.inclusion.map_comp _ _) ?_
    exact (congrArg₂ (fun u v => u ≫ v) e₂.specialOver_left e₁.specialOver_left).trans
      (specMap_ofHom_comp e₁.ringMap e₂.ringMap).symm
  · refine Eq.trans (B.inclusion.map_comp _ _) ?_
    exact (congrArg₂ (fun u v => u ≫ v) e₂.genericOver_left e₁.genericOver_left).trans
      (specMap_ofHom_comp e₁.fieldMap e₂.fieldMap).symm
  · refine Eq.trans ?_ (Over.mapComp_eq _ _).symm
    exact congrArg₂ Functor.comp e₂.a_canonical e₁.a_canonical
  · refine Eq.trans ?_ (Over.mapComp_eq _ _).symm
    exact congrArg₂ Functor.comp e₂.k_canonical e₁.k_canonical
  · exact ⟨{
      a := d₂.a
      α := d₂.α ≫ (α_ e₂.k e₁.k (q.x ≫ h'.hom)).inv
      β := (α_ e₂.a e₁.a q.y).hom ≫ (e₂.a ◁ d₁.β) ≫ (α_ e₂.a d₁.a f.hom).inv ≫
        (d₂.β ▷ f.hom) ≫ (α_ d₂.a π.hom f.hom).hom ≫ (d₂.a ◁ τ.inv.hom)
      compat := Subsingleton.elim (h := hthin _ _ _) _ _ }⟩

end ValuativeCriterion

end AlgebraicGeometry.Stack

end
