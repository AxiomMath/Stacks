module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MapDescentChart
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MapDescentTransport
/-!
# Carrying a canonical descent of a morphism forward to every later stage

The conclusion of [Stacks Project, Tag 01ZR] (2) pins the descended morphism by the *canonical*
identification `Stacks.AlgebraicGeometry.ModuleLimits.canHom` of the iterated pullback with the
pullback of the composite, and that is also the shape in which
`StacksFrontier/AlgebraicGeometry/ModuleLimits/MapDescentChart.lean` produces the descent of a
morphism over one affine chart of a stage.  A Zariski glueing of such local descents has to
compare the data obtained over the different charts, which can only be done after refining the
finitely many stages they live over to a single one.  This file supplies that refinement.

The only mathematical input is the pseudofunctoriality of the pullback functor:
the pentagon `AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity` says exactly that
`canHom` for a composite transition morphism factors as the two `canHom`s of its factors, which is
`canHom_comp` below, and everything else is naturality.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.canNatIso`: `canHom` as a natural isomorphism of functors.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.Pentagon.canHom_comp`: **the pentagon, read on
  `canHom`.** For `q`, `g₁`, `g₂` composable, the canonical identification for the transition
  morphism `g₁ ≫ g₂` composed with the one for `q` is the one for `q ≫ g₁` composed with the one
  for `g₂`. It is exported as `Stacks.AlgebraicGeometry.ModuleLimits.canHom_comp`.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_canonical_of_precomp`: **a canonical descent stays
  one after precomposing the transition morphism.**  If `φj` descends `φ` through `g₂`, then some
  morphism descends `φ` through `g₁ ≫ g₂`.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_canonical_of_terminal_base`: the same for a diagram
  indexed by `CategoryTheory.Over i`, where it says that a canonical descent at one stage is a
  canonical descent at *every* stage over it, the transition morphism to the base being unique.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_over_map_of_isAffineOpen_stage`: **the chart step
  of Tag 01ZR (2) at every later stage.**  This is
  `Stacks.AlgebraicGeometry.ModuleLimits.exists_over_map_of_isAffineOpen` with the stage it
  produces replaced by all stages over it, which is what a common refinement of the charts of a
  covering can be fed to.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_restrictFunctor_map`: the restriction to a
  smaller open of the restriction of a *global* morphism is that global morphism restricted.

## Implementation notes

`canHom` is an isomorphism — both of its factors are — and `canNatIso` records that, which is what
lets the canonical descent equation be solved for the descended morphism.  It is not folded into
`canHom` itself: the conclusion of the tag is stated with the morphism, and
`StacksFrontier/AlgebraicGeometry/ModuleLimits/CanonicalDescent.lean` proves it in that form.

`exists_canonical_of_terminal_base` is stated with the morphism `k ⟶ Over.mk (𝟙 i)` as an argument
rather than as `CategoryTheory.Over.homMk k.hom (by simp)`.  The two agree — `Over.mk (𝟙 i)` is
terminal in `Over i`, which is `over_hom_terminal_ext` — and taking it as an argument is what keeps
the statement usable: a caller that has built the morphism in its own way does not have to
transport along an equality of morphisms of `Over i` to apply the result.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

open Scheme.Modules

/-! ### The canonical identification as an isomorphism -/

/-- `Stacks.AlgebraicGeometry.ModuleLimits.canHom` as a natural isomorphism: the iterated pullback
along `q` and `g` is the pullback along the composite. -/
noncomputable def canNatIso {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X)
    (hpi : q ≫ g = pi) :
    Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback q ≅ Scheme.Modules.pullback pi :=
  Scheme.Modules.pullbackComp q g ≪≫ Scheme.Modules.pullbackCongr hpi

/-- The component of `Stacks.AlgebraicGeometry.ModuleLimits.canNatIso` at `F` is
`Stacks.AlgebraicGeometry.ModuleLimits.canHom` at `F`. -/
theorem canNatIso_hom_app {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X)
    (hpi : q ≫ g = pi) (F : X.Modules) :
    (canNatIso q g pi hpi).hom.app F = canHom q g pi hpi F := rfl

/-- **The pentagon of the pullback pseudofunctor, read on the canonical identification.**  The
canonical identification for the transition morphism `g₁ ≫ g₂` and the projection `q`, precomposed
with the comparison of the iterated pullback, is the canonical identification for `q ≫ g₁` and `g₂`
composed with the one for `q` and `g₁`.

This is `AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity` with the
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` bookkeeping carried out; it is the only coherence
of the pullback functor that the refinement step needs.

`Stacks.AlgebraicGeometry.ModuleLimits.canHom_comp` of
`StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackCanonical` is the same pentagon stated
without `canNatIso` and with the composites taken in a different order; the two are not
interchangeable at a call site, so this one lives in `Pentagon` and is exported. -/
theorem Pentagon.canHom_comp {W Z Y X : Scheme.{u}} (q : W ⟶ Z) (g₁ : Z ⟶ Y) (g₂ : Y ⟶ X)
    (qz : W ⟶ Y) (h₁ : q ≫ g₁ = qz) (g : Z ⟶ X) (hg : g₁ ≫ g₂ = g)
    (pi : W ⟶ X) (h₂ : qz ≫ g₂ = pi) (hq : q ≫ g = pi) (M : X.Modules) :
    (Scheme.Modules.pullback q).map ((canNatIso g₁ g₂ g hg).hom.app M) ≫ canHom q g pi hq M =
      canHom q g₁ qz h₁ ((Scheme.Modules.pullback g₂).obj M) ≫ canHom qz g₂ pi h₂ M := by
  subst h₁
  subst hg
  subst h₂
  have papp := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity q g₁ g₂) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, eqToHom_app, Category.id_comp] at papp
  simp only [canHom, canNatIso, Iso.trans_hom, Scheme.Modules.pullbackCongr,
    eqToIso.hom, eqToHom_app, eqToHom_refl, Category.comp_id, Category.assoc]
  rw [← papp]
  simp

export Pentagon (canHom_comp)

/-! ### Precomposing the transition morphism of a canonical descent -/

/-- **A canonical descent through `g₂` is a canonical descent through `g₁ ≫ g₂`.**  Let `φ` be a
morphism between the pullbacks along `pi` of two modules and let `φj` be a morphism between their
pullbacks along `g₂` whose pullback along `qz` is `φ` through the canonical identifications.  Then
the pullback of `φj` along `g₁` is, through the canonical identifications, a morphism whose
pullback along `q` is again `φ`.

The proof is `canHom_comp` at the source and at the target, with the naturality of `canNatIso` in
between. -/
theorem exists_canonical_of_precomp {W Z Y X : Scheme.{u}} (q : W ⟶ Z) (g₁ : Z ⟶ Y) (g₂ : Y ⟶ X)
    (qz : W ⟶ Y) (h₁ : q ≫ g₁ = qz) (g : Z ⟶ X) (hg : g₁ ≫ g₂ = g)
    (pi : W ⟶ X) (h₂ : qz ≫ g₂ = pi) (hq : q ≫ g = pi) {F G : X.Modules}
    (φ : (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G)
    (φj : (Scheme.Modules.pullback g₂).obj F ⟶ (Scheme.Modules.pullback g₂).obj G)
    (hφj : (Scheme.Modules.pullback qz).map φj ≫ canHom qz g₂ pi h₂ G =
      canHom qz g₂ pi h₂ F ≫ φ) :
    ∃ φk : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G,
      (Scheme.Modules.pullback q).map φk ≫ canHom q g pi hq G = canHom q g pi hq F ≫ φ := by
  refine ⟨(canNatIso g₁ g₂ g hg).inv.app F ≫ (Scheme.Modules.pullback g₁).map φj ≫
    (canNatIso g₁ g₂ g hg).hom.app G, ?_⟩
  have hnat := (canNatIso q g₁ qz h₁).hom.naturality φj
  dsimp only [Functor.comp_map] at hnat
  rw [canNatIso_hom_app, canNatIso_hom_app] at hnat
  simp only [Functor.map_comp, Category.assoc, canHom_comp q g₁ g₂ qz h₁ g hg pi h₂ hq G]
  rw [reassoc_of% hnat, hφj,
    ← reassoc_of% (canHom_comp q g₁ g₂ qz h₁ g hg pi h₂ hq F), ← Category.assoc,
    ← Functor.map_comp]
  simp

/-! ### Diagrams indexed by the objects over a stage -/

/-- `CategoryTheory.Over.mk (𝟙 i)` is terminal in `CategoryTheory.Over i`: any two morphisms into
it from the same object agree. -/
theorem over_hom_terminal_ext {I : Type u} [Category.{u} I] {i : I} {k : Over i}
    (f g : k ⟶ Over.mk (𝟙 i)) : f = g := by
  apply Over.OverMorphism.ext
  simpa using (Over.w f).trans (Over.w g).symm

section OverBase

variable {I : Type u} [Category.{u} I] {i : I} (D' : Over i ⥤ Scheme.{u}) (c' : Cone D')

/-- **A canonical descent at one stage of a diagram indexed by `CategoryTheory.Over i` is a
canonical descent at every stage over it.**  The transition morphism from a stage `k` to the base
`CategoryTheory.Over.mk (𝟙 i)` is unique, so the descent carried forward from `j` to `k` descends
`ψ` through that same morphism, whichever factorisation through `j` is used.

This is `exists_canonical_of_precomp` with `over_hom_terminal_ext` supplying the factorisation. -/
theorem exists_canonical_of_terminal_base {F G : (D'.obj (Over.mk (𝟙 i))).Modules}
    (ψ : (Scheme.Modules.pullback (c'.π.app (Over.mk (𝟙 i)))).obj F ⟶
      (Scheme.Modules.pullback (c'.π.app (Over.mk (𝟙 i)))).obj G)
    {j : Over i} (e : j ⟶ Over.mk (𝟙 i))
    (φj : (Scheme.Modules.pullback (D'.map e)).obj F ⟶ (Scheme.Modules.pullback (D'.map e)).obj G)
    (hφj : (Scheme.Modules.pullback (c'.π.app j)).map φj ≫
        canHom (c'.π.app j) (D'.map e) (c'.π.app (Over.mk (𝟙 i))) (c'.w e) G =
      canHom (c'.π.app j) (D'.map e) (c'.π.app (Over.mk (𝟙 i))) (c'.w e) F ≫ ψ)
    (k : Over i) (hk : k ⟶ Over.mk (𝟙 i)) (m : k ⟶ j) :
    ∃ φk : (Scheme.Modules.pullback (D'.map hk)).obj F ⟶
        (Scheme.Modules.pullback (D'.map hk)).obj G,
      (Scheme.Modules.pullback (c'.π.app k)).map φk ≫
          canHom (c'.π.app k) (D'.map hk) (c'.π.app (Over.mk (𝟙 i))) (c'.w hk) G =
        canHom (c'.π.app k) (D'.map hk) (c'.π.app (Over.mk (𝟙 i))) (c'.w hk) F ≫ ψ :=
  exists_canonical_of_precomp (c'.π.app k) (D'.map m) (D'.map e) (c'.π.app j) (c'.w m)
    (D'.map hk) ((D'.map_comp m e).symm.trans
      (congrArg D'.map (over_hom_terminal_ext (m ≫ e) hk)))
    (c'.π.app (Over.mk (𝟙 i))) (c'.w e) (c'.w hk) ψ φj hφj

end OverBase

/-! ### The chart step at every later stage -/

section Stage

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

/-- **Stacks Project, Tag 01ZR (2) over one affine chart of the stage, at every later stage.**  Let
`V` be an affine open of the stage `D.obj i` and let `φ` be a morphism between the pullbacks to the
limit of two finitely presented modules on `D.obj i`.  Then there is a stage `j` over `i` such that
for *every* stage `k` over `i` admitting a morphism to `j`, the restriction of `φ` to the preimage
of `V` — transported to the base of the diagram of preimages of `V` by
`Stacks.Modules.restrictPullbackIso` — is, through the canonical identifications, the pullback of a
morphism over the preimage of `V` at `k`.

This is `Stacks.AlgebraicGeometry.ModuleLimits.exists_over_map_of_isAffineOpen` followed by
`exists_canonical_of_terminal_base`.  The point of the reformulation is that the morphism descends
at every stage over `j` and not only at `j` itself, so that the charts of a finite affine covering
of `D.obj i` can be made to descend simultaneously at one common refinement. -/
theorem exists_over_map_of_isAffineOpen_stage (hc : IsLimit c) (i : I)
    {V : (D.obj i).Opens} (hV : IsAffineOpen V)
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    ∃ (j : Over i) (ψ : (Scheme.Modules.pullback
          ((EventualLimit.preimageCone D c i V).π.app (Over.mk (𝟙 i)))).obj
            ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj F) ⟶
        (Scheme.Modules.pullback
          ((EventualLimit.preimageCone D c i V).π.app (Over.mk (𝟙 i)))).obj
            ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj G)),
      (ψ = ((Stacks.Modules.restrictPullbackIso (c.π.app i)
            (Scheme.Hom.preimage_mono (c.π.app i)
              (show V ≤ D.map (𝟙 i) ⁻¹ᵁ V by simp))).app F).inv ≫
          (Scheme.Modules.restrictFunctor (c.π.app i ⁻¹ᵁ V).ι).map φ ≫
          ((Stacks.Modules.restrictPullbackIso (c.π.app i)
            (Scheme.Hom.preimage_mono (c.π.app i)
              (show V ≤ D.map (𝟙 i) ⁻¹ᵁ V by simp))).app G).hom) ∧
      ∀ (k : Over i) (hk : k ⟶ Over.mk (𝟙 i)), (k ⟶ j) →
        ∃ φk : (Scheme.Modules.pullback ((EventualLimit.preimageDiagram D i V).map hk)).obj
            ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj F) ⟶
          (Scheme.Modules.pullback ((EventualLimit.preimageDiagram D i V).map hk)).obj
            ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj G),
          (Scheme.Modules.pullback ((EventualLimit.preimageCone D c i V).π.app k)).map φk ≫
              canHom ((EventualLimit.preimageCone D c i V).π.app k)
                ((EventualLimit.preimageDiagram D i V).map hk)
                ((EventualLimit.preimageCone D c i V).π.app (Over.mk (𝟙 i)))
                ((EventualLimit.preimageCone D c i V).w hk)
                ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj G) =
            canHom ((EventualLimit.preimageCone D c i V).π.app k)
                ((EventualLimit.preimageDiagram D i V).map hk)
                ((EventualLimit.preimageCone D c i V).π.app (Over.mk (𝟙 i)))
                ((EventualLimit.preimageCone D c i V).w hk)
                ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj F) ≫ ψ := by
  obtain ⟨j, e, φj, hφj⟩ := exists_over_map_of_isAffineOpen D c hc i hV F G φ
  exact ⟨j, _, rfl, fun k hk m =>
    exists_canonical_of_terminal_base (EventualLimit.preimageDiagram D i V)
      (EventualLimit.preimageCone D c i V) _ e φj hφj k hk m⟩

end Stage

/-! ### Restricting the restriction of a global morphism -/

/-- **Restricting to a smaller open the restriction of a global morphism gives that global morphism
restricted.**  For `V ≤ W` and `ψ : M ⟶ N`, the sectionwise-defined restriction of
`ψ|_W : M|_W ⟶ N|_W` to `V` is `ψ|_V`.

This is the compatibility that makes the two restrictions of a morphism of sheaves to the members
of a covering agree on the pairwise intersections, and it is the naturality of
`Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso` read through
`Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_eq`. -/
theorem restrictHomOfLE_restrictFunctor_map {X : Scheme.{u}} {M N : X.Modules} {V W : X.Opens}
    (e : V ≤ W) (ψ : M ⟶ N) :
    restrictHomOfLE e ((Scheme.Modules.restrictFunctor W.ι).map ψ) =
      (Scheme.Modules.restrictFunctor V.ι).map ψ := by
  rw [restrictHomOfLE_eq]
  exact NatIso.naturality_1 (restrictLEIso e) ψ

end Stacks.AlgebraicGeometry.ModuleLimits

end
