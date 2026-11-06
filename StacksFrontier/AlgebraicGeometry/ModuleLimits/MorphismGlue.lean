module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackCanonical
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.DescendResidue

/-!
# Descent of a morphism of finitely presented modules through a cofiltered limit of
quasi-compact quasi-separated schemes

[Stacks Project, Tag 01ZR] (2) is proved for a cofiltered diagram of *affine* schemes in
`StacksFrontier/AlgebraicGeometry/ModuleLimits/CanonicalDescent.lean`.  The source passes from
there to a diagram of quasi-compact quasi-separated schemes by Zariski glueing.  This file
collects the local-to-global apparatus that passage needs.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.sqIso`: the canonical identification of the two routes
  through a commuting square of schemes, read on pullbacks of modules.
* `Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_pullback_cover`: two morphisms of sheaves of
  modules whose pullbacks along the inclusions of the members of an open covering agree are
  equal.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_restrict_map_eq_of_isLimit`:
  [Stacks Project, Tag 01ZR] (3) for the restrictions of two morphisms to a quasi-compact open
  of a stage, in the form in which the glueing argument needs it.

The conditional statements of [Stacks Project, Tag 01ZR] (1) live in
`StacksFrontier/AlgebraicGeometry/ModuleLimits/DescendResidue.lean` and
`StacksFrontier/AlgebraicGeometry/ModuleLimits/AffineFaithful.lean`.

## Implementation notes

Everything is phrased with `AlgebraicGeometry.Scheme.Modules.pullback` along the inclusion of an
open rather than with `AlgebraicGeometry.Scheme.Modules.restrictFunctor`.  That is what makes the
comparisons uniform: every identification in play is then built from
`AlgebraicGeometry.Scheme.Modules.pullbackComp` and `pullbackCongr`, so the only coherence ever
needed is `Stacks.AlgebraicGeometry.ModuleLimits.canHom_comp`.  The one place where the
restriction functor is unavoidable is the locality of an equality of morphisms, and there it is
removed in a single step by the natural isomorphism
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.

The diagram of preimages of an open `W` of a stage `E.obj k` is
`AlgebraicGeometry.EventualLimit.preimageDiagram E k W`, indexed by `CategoryTheory.Over k`,
whose terminal object `CategoryTheory.Over.mk (𝟙 k)` carries the open `E.map (𝟙 k) ⁻¹ᵁ W` rather
than `W` itself.  No isomorphism is transported to repair this: the arguments are run with
`E.map (𝟙 k) ⁻¹ᵁ W` throughout, as in
`Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_isLimit`.  Working over
`Over k` rather than over the ambient index category is also what makes the finitely many stages
produced below refinable to a single one *compatibly*: a morphism of `Over k` to the terminal
object is unique, so the composites through different intermediate stages agree automatically,
which they need not do in the ambient index category.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-! ### The canonical identification across a commuting square -/

/-- The canonical identification of the two routes through a commuting square
`u ≫ v = w ≫ t` of morphisms of schemes, as an isomorphism of the two iterated pullback
functors.  It is `AlgebraicGeometry.Scheme.Modules.pullbackComp` twice and one
`pullbackCongr`. -/
noncomputable def sqNatIso {A B C E : Scheme.{u}} (u : A ⟶ B) (v : B ⟶ E) (w : A ⟶ C)
    (t : C ⟶ E) (h : u ≫ v = w ≫ t) :
    Scheme.Modules.pullback v ⋙ Scheme.Modules.pullback u ≅
      Scheme.Modules.pullback t ⋙ Scheme.Modules.pullback w :=
  Scheme.Modules.pullbackComp u v ≪≫ Scheme.Modules.pullbackCongr h ≪≫
    (Scheme.Modules.pullbackComp w t).symm

/-- `sqNatIso` at a single module. -/
noncomputable def sqIso {A B C E : Scheme.{u}} (u : A ⟶ B) (v : B ⟶ E) (w : A ⟶ C)
    (t : C ⟶ E) (h : u ≫ v = w ≫ t) (K : E.Modules) :
    (Scheme.Modules.pullback u).obj ((Scheme.Modules.pullback v).obj K) ≅
      (Scheme.Modules.pullback w).obj ((Scheme.Modules.pullback t).obj K) :=
  (sqNatIso u v w t h).app K

/-- `sqIso` is `canHom` across the square, with the second canonical identification inverted. -/
theorem sqIso_hom {A B C E : Scheme.{u}} (u : A ⟶ B) (v : B ⟶ E) (w : A ⟶ C)
    (t : C ⟶ E) (h : u ≫ v = w ≫ t) (K : E.Modules) :
    (sqIso u v w t h K).hom = canHom u v (u ≫ v) rfl K ≫
      (Scheme.Modules.pullbackCongr h).hom.app K ≫ (canIso w t (w ≫ t) rfl K).inv := by
  simp [sqIso, sqNatIso, canHom, canIso, Scheme.Modules.pullbackCongr]

/-- `sqIso` is natural in the module. -/
theorem sqIso_naturality {A B C E : Scheme.{u}} (u : A ⟶ B) (v : B ⟶ E) (w : A ⟶ C)
    (t : C ⟶ E) (h : u ≫ v = w ≫ t) {K L : E.Modules} (ψ : K ⟶ L) :
    (Scheme.Modules.pullback u).map ((Scheme.Modules.pullback v).map ψ) ≫ (sqIso u v w t h L).hom
      = (sqIso u v w t h K).hom ≫
        (Scheme.Modules.pullback w).map ((Scheme.Modules.pullback t).map ψ) :=
  (sqNatIso u v w t h).hom.naturality ψ

/-! ### Locality of an equality of morphisms, in the pullback spelling -/

/-- Two morphisms of sheaves of modules on a scheme are equal as soon as their pullbacks along
the inclusions of the members of an open covering agree.  This is
`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover` read through
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. -/
theorem hom_ext_of_pullback_cover {X : Scheme.{u}} {M N : X.Modules} {ι : Type*}
    (W : ι → X.Opens) (hW : ∀ x : X, ∃ a, x ∈ W a) {φ ψ : M ⟶ N}
    (h : ∀ a, (Scheme.Modules.pullback (W a).ι).map φ =
      (Scheme.Modules.pullback (W a).ι).map ψ) : φ = ψ := by
  refine hom_ext_of_restrict_cover W hW (fun a => ?_)
  have e := Scheme.Modules.restrictFunctorIsoPullback (W a).ι
  rw [← Iso.cancel_iso_hom_right _ _ (e.app N), Iso.app_hom, e.hom.naturality φ,
    e.hom.naturality ψ, h a]

/-! ### Tag 01ZR (3) over a quasi-compact open of a stage -/

/-- **[Stacks Project, Tag 01ZR] (3) over a quasi-compact open of a stage.**  Let `d` be a limit
cone on a cofiltered diagram `E` of schemes with affine transition morphisms, let `W` be a
quasi-compact open of a stage `E.obj k`, and let `ξ₁`, `ξ₂` be two morphisms of sheaves of
modules of finite presentation on the preimage of `W` at that stage.  If their pullbacks to the
preimage of `W` in the limit agree, then their pullbacks to the preimage of `W` at some stage
over `k` agree.

The open is spelled `E.map (𝟙 k) ⁻¹ᵁ W`, which is the value at the terminal object of
`CategoryTheory.Over k` of the diagram of preimages; see the implementation notes. -/
theorem exists_pullback_restrict_map_eq_of_isLimit {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ Scheme.{u}) [∀ {x y : J} (g : x ⟶ y), IsAffineHom (E.map g)]
    (d : Cone E) (hd : IsLimit d) (k : J) (W : (E.obj k).Opens)
    (hW : IsCompact (W : Set (E.obj k)))
    (M N : ((EventualLimit.preimageDiagram E k W).obj (Over.mk (𝟙 k))).Modules)
    [M.IsFinitePresentation] [N.IsFinitePresentation] (ξ₁ ξ₂ : M ⟶ N)
    (h : (Scheme.Modules.pullback
          ((EventualLimit.preimageCone E d k W).π.app (Over.mk (𝟙 k)))).map ξ₁ =
      (Scheme.Modules.pullback
          ((EventualLimit.preimageCone E d k W).π.app (Over.mk (𝟙 k)))).map ξ₂) :
    ∃ (x : Over k) (e : x ⟶ Over.mk (𝟙 k)),
      (Scheme.Modules.pullback ((EventualLimit.preimageDiagram E k W).map e)).map ξ₁ =
        (Scheme.Modules.pullback ((EventualLimit.preimageDiagram E k W).map e)).map ξ₂ := by
  have : ∀ {x y : Over k} (g : x ⟶ y),
      IsAffineHom ((EventualLimit.preimageDiagram E k W).map g) := fun g =>
    EventualLimit.preimageDiagram_isAffineHom E k W g
  have : CompactSpace ((EventualLimit.preimageDiagram E k W).obj (Over.mk (𝟙 k))) :=
    isCompact_iff_compactSpace.mp
      (show IsCompact ((E.map (𝟙 k) ⁻¹ᵁ W : (E.obj k).Opens) : Set (E.obj k)) by simpa using hW)
  exact exists_pullback_map_eq_of_isLimit (EventualLimit.preimageDiagram E k W)
    (EventualLimit.preimageCone E d k W) (EventualLimit.isLimitPreimageCone E d hd k W)
    (Over.mk (𝟙 k)) M N ξ₁ ξ₂ h

end Stacks.AlgebraicGeometry.ModuleLimits

end
