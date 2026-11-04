module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethCompositeCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity
public import StacksFrontier.Topology.Sheaves.Cohomology.KunnethOnSections.RelativeNaive

/-!
# The relative Künneth map along a morphism of diagrams

Let `S` be a ringed space and consider two commuting squares over `S`,
`p ≫ a = f = q ≫ b` on `W ⟶ X, Y ⟶ S` and `p' ≫ a' = f' = q' ≫ b'` on `W' ⟶ X', Y' ⟶ S`,
together with morphisms `τ_X : X ⟶ X'`, `τ_Y : Y ⟶ Y'`, `τ_W : W ⟶ W'` with `a = τ_X ≫ a'`,
`b = τ_Y ≫ b'`, `f = τ_W ≫ f'`, `τ_W ≫ p' = p ≫ τ_X` and `τ_W ≫ q' = q ≫ τ_Y`.  For
`E ∈ D(𝒪_X)` and `M ∈ D(𝒪_Y)` the relative Künneth map of [Stacks, Tag 0FLP] of the first
square at `(E, M)` is, under the identifications `Ra_* ≅ Ra'_*Rτ_{X,*}` and
`Rf_* ≅ Rf'_*Rτ_{W,*}`, the relative Künneth map of the second square at
`(Rτ_{X,*}E, Rτ_{Y,*}M)` followed by `Rf'_*` of the abstract Künneth map of `Lτ_W^* ⊣ Rτ_{W,*}`
with legs `Lτ_W^*Lp'^*Rτ_{X,*} ≅ Lp^*Lτ_X^*Rτ_{X,*} ⟶ Lp^*`.

This is used for the inverse-image ringed spaces `(X, a^{-1}𝒪_S)` of the proof of
[Stacks, Tag 0FLT], where `τ_X` is the identity on spaces: the relative Künneth map of the
inverse-image square, through which the cup product of [Stacks, Tag 0FLR] is defined, is compared
with the one of the fibre product of schemes, which is the one [Stacks, Tag 0FU4] is about.

## Main results

* `Stacks.Cohomology.DerivedKunneth.adjunctionBitensorMap_comp_legs`: the abstract statement for
  an adjunction identified with a composite, legs factored through the composite.
* `Stacks.Cohomology.DerivedKunneth.pullbackCounitLeg_crossing`: the counit leg of the first
  square, read through the identifications, is the counit leg of the second followed by the
  crossing leg.
* `Stacks.Cohomology.DerivedKunneth.adjunctionBitensorMap_crossing`: the statement above.

## References

* [Stacks Project, Tag 0FLP](https://stacks.math.columbia.edu/tag/0FLP)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedPullback.Composition
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedKunneth

section Abstract

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ u₁ u₂ u₃ u₄ u₅ u₆ u₇

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) {L₂ : D ⥤ E} {R₂ : E ⥤ D} (adj₂ : L₂ ⊣ R₂)
  {L : C ⥤ E} {R : E ⥤ C} (adj : L ⊣ R) (cl : L₁ ⋙ L₂ ≅ L) (cr : R₂ ⋙ R₁ ≅ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (B' : E × E ⥤ E)
  (α₁ : A ⋙ L₁ ⟶ L₁.prod L₁ ⋙ B) (α₂ : B ⋙ L₂ ⟶ L₂.prod L₂ ⋙ B') (α : A ⋙ L ⟶ L.prod L ⋙ B')
  {X₁ : Type u₄} [Category.{v₄} X₁] {X₁' : Type u₅} [Category.{v₅} X₁']
  {Y₁ : Type u₆} [Category.{v₆} Y₁] {Y₁' : Type u₇} [Category.{v₇} Y₁']
  {Ra : X₁ ⥤ C} {Pp : X₁ ⥤ E} (β : Ra ⋙ L ⟶ Pp)
  {Ra' : X₁' ⥤ C} {Pp' : X₁' ⥤ D} (β₁ : Ra' ⋙ L₁ ⟶ Pp')
  {Rb : Y₁ ⥤ C} {Pq : Y₁ ⥤ E} (γ : Rb ⋙ L ⟶ Pq)
  {Rb' : Y₁' ⥤ C} {Pq' : Y₁' ⥤ D} (γ₁ : Rb' ⋙ L₁ ⟶ Pq')

/-- **The abstract Künneth map along a composite adjunction, with legs factored through the
composite, at one pair of objects.**  Let `adj : L ⊣ R` be identified with the composite of
`adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` by `cl`, `cr` and the transposition coherence
`hcompat`, and let the comparison `α` for `L` be the composite of `α₁` and `α₂` (`hα`).  Let
`e`, `m` be objects with legs `β`, `γ` for the first Künneth map, `e'`, `m'` objects with legs
`β₁`, `γ₁` for the second, `cX : Ra'e' ⟶ Rae` and `cY : Rb'm' ⟶ Rbm`, and `bX`, `bY` such that
`β` read through `cX` is `L₂β₁` followed by `bX` (`hβ`, `hγ`).  Then the first Künneth map,
after `cX` and `cY`, is the second followed by `R₁` of the transpose under `adj₂` of
`α₂ ≫ (bX ⊗ bY)` and by `cr`. -/
theorem adjunctionBitensorMap_comp_legs
    (hcompat : ∀ (Z : C) (T : E) (φ : L.obj Z ⟶ T),
      adj₁.homEquiv _ _ (adj₂.homEquiv _ _ (cl.hom.app Z ≫ φ)) ≫ cr.hom.app T =
        adj.homEquiv Z T φ)
    (hα : ∀ (x y : C), cl.hom.app (A.obj (x, y)) ≫ α.app (x, y) =
      L₂.map (α₁.app (x, y)) ≫ α₂.app (L₁.obj x, L₁.obj y) ≫
        B'.map (cl.hom.app x ×ₘ cl.hom.app y))
    (e : X₁) (e' : X₁') (m : Y₁) (m' : Y₁') (cX : Ra'.obj e' ⟶ Ra.obj e)
    (cY : Rb'.obj m' ⟶ Rb.obj m) (bX : L₂.obj (Pp'.obj e') ⟶ Pp.obj e)
    (bY : L₂.obj (Pq'.obj m') ⟶ Pq.obj m)
    (hβ : cl.hom.app (Ra'.obj e') ≫ L.map cX ≫ β.app e = L₂.map (β₁.app e') ≫ bX)
    (hγ : cl.hom.app (Rb'.obj m') ≫ L.map cY ≫ γ.app m = L₂.map (γ₁.app m') ≫ bY) :
    A.map (cX ×ₘ cY) ≫ adjunctionBitensorMap adj A B' α β γ e m =
      adjunctionBitensorMap adj₁ A B α₁ β₁ γ₁ e' m' ≫
        R₁.map (adj₂.homEquiv _ _ (α₂.app (Pp'.obj e', Pq'.obj m') ≫ B'.map (bX ×ₘ bY))) ≫
          cr.hom.app (B'.obj (Pp.obj e, Pq.obj m)) := by
  have hR : adjunctionBitensorMap adj₁ A B α₁ β₁ γ₁ e' m' ≫
        R₁.map (adj₂.homEquiv _ _ (α₂.app (Pp'.obj e', Pq'.obj m') ≫ B'.map (bX ×ₘ bY))) =
      adj₁.homEquiv _ _ (adj₂.homEquiv _ _
        (L₂.map (α₁.app (Ra'.obj e', Rb'.obj m') ≫ B.map (β₁.app e' ×ₘ γ₁.app m')) ≫
          α₂.app (Pp'.obj e', Pq'.obj m') ≫ B'.map (bX ×ₘ bY))) := by
    rw [adjunctionBitensorMap, ← Adjunction.homEquiv_naturality_right]
    congr 1
    rw [Adjunction.homEquiv_naturality_left]
  have hL : A.map (cX ×ₘ cY) ≫ adjunctionBitensorMap adj A B' α β γ e m =
      adj₁.homEquiv _ _ (adj₂.homEquiv _ _
        (cl.hom.app (A.obj (Ra'.obj e', Rb'.obj m')) ≫ L.map (A.map (cX ×ₘ cY)) ≫
          α.app (Ra.obj e, Rb.obj m) ≫ B'.map (β.app e ×ₘ γ.app m))) ≫ cr.hom.app _ := by
    rw [hcompat, adjunctionBitensorMap]
    exact (Adjunction.homEquiv_naturality_left _ _ _).symm
  rw [hL, reassoc_of% hR]
  refine congrArg (fun t => adj₁.homEquiv _ _ (adj₂.homEquiv _ _ t) ≫ cr.hom.app _) ?_
  have e3 : L₁.map (A.map (cX ×ₘ cY)) ≫ α₁.app (Ra.obj e, Rb.obj m) =
      α₁.app (Ra'.obj e', Rb'.obj m') ≫ B.map (L₁.map cX ×ₘ L₁.map cY) :=
    α₁.naturality (cX ×ₘ cY)
  have e4 : L₂.map (B.map (L₁.map cX ×ₘ L₁.map cY)) ≫
      α₂.app (L₁.obj (Ra.obj e), L₁.obj (Rb.obj m)) =
      α₂.app (L₁.obj (Ra'.obj e'), L₁.obj (Rb'.obj m')) ≫
        B'.map (L₂.map (L₁.map cX) ×ₘ L₂.map (L₁.map cY)) :=
    α₂.naturality (L₁.map cX ×ₘ L₁.map cY)
  have e5 : L₂.map (B.map (β₁.app e' ×ₘ γ₁.app m')) ≫ α₂.app (Pp'.obj e', Pq'.obj m') =
      α₂.app (L₁.obj (Ra'.obj e'), L₁.obj (Rb'.obj m')) ≫
        B'.map (L₂.map (β₁.app e') ×ₘ L₂.map (γ₁.app m')) :=
    α₂.naturality (β₁.app e' ×ₘ γ₁.app m')
  have key : ∀ {u u' : C} {t' : D} {t : E} (c : u' ⟶ u) (g₁ : L₁.obj u' ⟶ t')
      (g : L.obj u ⟶ t) (b : L₂.obj t' ⟶ t), cl.hom.app u' ≫ L.map c ≫ g = L₂.map g₁ ≫ b →
        L₂.map (L₁.map c) ≫ cl.hom.app u ≫ g = L₂.map g₁ ≫ b := fun c g₁ g b h => by
    rw [← h, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ g) (cl.hom.naturality c)
  have hprod : B'.map (L₂.map (L₁.map cX) ×ₘ L₂.map (L₁.map cY)) ≫
      B'.map (cl.hom.app (Ra.obj e) ×ₘ cl.hom.app (Rb.obj m)) ≫ B'.map (β.app e ×ₘ γ.app m) =
      B'.map (L₂.map (β₁.app e') ×ₘ L₂.map (γ₁.app m')) ≫ B'.map (bX ×ₘ bY) := by
    rw [← B'.map_comp, ← B'.map_comp, ← B'.map_comp]
    exact congrArg B'.map (CategoryTheory.Prod.hom_ext (key cX _ _ _ hβ) (key cY _ _ _ hγ))
  calc cl.hom.app (A.obj (Ra'.obj e', Rb'.obj m')) ≫ L.map (A.map (cX ×ₘ cY)) ≫
        α.app (Ra.obj e, Rb.obj m) ≫ B'.map (β.app e ×ₘ γ.app m)
      = L₂.map (L₁.map (A.map (cX ×ₘ cY))) ≫
          (cl.hom.app (A.obj (Ra.obj e, Rb.obj m)) ≫ α.app (Ra.obj e, Rb.obj m)) ≫
            B'.map (β.app e ×ₘ γ.app m) := by
        rw [← cl.hom.naturality_assoc]
        simp only [Functor.comp_map, Category.assoc]
    _ = L₂.map (L₁.map (A.map (cX ×ₘ cY)) ≫ α₁.app (Ra.obj e, Rb.obj m)) ≫
          α₂.app (L₁.obj (Ra.obj e), L₁.obj (Rb.obj m)) ≫
            B'.map (cl.hom.app (Ra.obj e) ×ₘ cl.hom.app (Rb.obj m)) ≫
              B'.map (β.app e ×ₘ γ.app m) := by
        rw [hα, Functor.map_comp]
        simp only [Category.assoc]
    _ = L₂.map (α₁.app (Ra'.obj e', Rb'.obj m')) ≫
          (L₂.map (B.map (L₁.map cX ×ₘ L₁.map cY)) ≫
            α₂.app (L₁.obj (Ra.obj e), L₁.obj (Rb.obj m))) ≫
            B'.map (cl.hom.app (Ra.obj e) ×ₘ cl.hom.app (Rb.obj m)) ≫
              B'.map (β.app e ×ₘ γ.app m) := by
        rw [e3, Functor.map_comp]
        simp only [Category.assoc]
    _ = L₂.map (α₁.app (Ra'.obj e', Rb'.obj m')) ≫
          α₂.app (L₁.obj (Ra'.obj e'), L₁.obj (Rb'.obj m')) ≫
            B'.map (L₂.map (β₁.app e') ×ₘ L₂.map (γ₁.app m')) ≫ B'.map (bX ×ₘ bY) := by
        rw [e4, Category.assoc, hprod]
    _ = L₂.map (α₁.app (Ra'.obj e', Rb'.obj m') ≫ B.map (β₁.app e' ×ₘ γ₁.app m')) ≫
          α₂.app (Pp'.obj e', Pq'.obj m') ≫ B'.map (bX ×ₘ bY) := by
        rw [Functor.map_comp, Category.assoc, reassoc_of% e5]

end Abstract

section Geometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- The counit leg at a factorization `p ≫ a = f`, read at an object: the transport along the
factorization, the inverse composition isomorphism of Stacks 0D5S, and `Lp^*` of the counit. -/
theorem pullbackCounitLeg_app_eq {S X W : RingedSpace.{u, u}} (a : X ⟶ S) (p : W ⟶ X)
    (f : W ⟶ S) (hp : p ≫ a = f)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (pullbackCounitLeg a p f hp).app E =
      eqToHom (congrArg (fun z : W ⟶ S => (derivedPullback z).obj ((derivedPushforward a).obj E))
          hp.symm) ≫
        (derivedPullbackCompIsoCanonical p a).inv.app ((derivedPushforward a).obj E) ≫
          (derivedPullback p).map ((derivedAdjunction a).counit.app E) := by
  subst hp
  simp only [pullbackCounitLeg, pullbackCounitLegComp, eqToHom_refl, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Category.id_comp]
  exact congrArg (_ ≫ ·) (Category.comp_id _)

/-- Transport of a derived pullback along an equality of morphisms commutes with the derived
pullback of a morphism. -/
theorem eqToHom_derivedPullback_naturality {S W : RingedSpace.{u, u}} {g₁ g₂ : W ⟶ S}
    (h : g₁ = g₂) {M N : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
    (φ : M ⟶ N) :
    (derivedPullback g₁).map φ ≫
        eqToHom (congrArg (fun z : W ⟶ S => (derivedPullback z).obj N) h) =
      eqToHom (congrArg (fun z : W ⟶ S => (derivedPullback z).obj M) h) ≫
        (derivedPullback g₂).map φ := by
  subst h
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- Transport of the composition isomorphism of Stacks 0D5S along an equality of the first
morphisms. -/
theorem derivedPullbackCompIsoCanonical_hom_app_eqToHom {S X W : RingedSpace.{u, u}}
    {g₁ g₂ : W ⟶ X} (h : g₁ = g₂) (a : X ⟶ S)
    (Z : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    (derivedPullbackCompIsoCanonical g₁ a).hom.app Z ≫
        eqToHom (congrArg (fun z : W ⟶ X => (derivedPullback (z ≫ a)).obj Z) h) =
      eqToHom (congrArg (fun z : W ⟶ X => (derivedPullback z).obj ((derivedPullback a).obj Z))
          h) ≫
        (derivedPullbackCompIsoCanonical g₂ a).hom.app Z := by
  subst h
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]


/-- The coherence chase behind `pullbackCounitLeg_crossing`, with every object and morphism a
variable: two associativity squares and a transport. -/
private theorem iso_chase {C : Type*} [Category C] {P Q Q' R T U V V' : C}
    (c1 : P ≅ Q) (c2 : U ≅ P) (c3 : U ≅ V) (c4 : V ≅ Q) (c5 : R ≅ V') (c6 : V' ≅ Q')
    (c7 : R ≅ T) (c8 : T ≅ Q') (e1 : Q ⟶ Q') (e2 : V ⟶ V')
    (hA1 : c3.hom ≫ c4.hom = c2.hom ≫ c1.hom) (hA2 : c5.hom ≫ c6.hom = c7.hom ≫ c8.hom)
    (hT : c4.hom ≫ e1 = e2 ≫ c6.hom) :
    c1.hom ≫ e1 ≫ c8.inv ≫ c7.inv = c2.inv ≫ c3.hom ≫ e2 ≫ c5.inv := by
  have h1 : c1.hom = c2.inv ≫ c3.hom ≫ c4.hom := by
    rw [hA1, Iso.inv_hom_id_assoc]
  have h6 : c6.hom = c5.inv ≫ c7.hom ≫ c8.hom := by
    rw [← hA2, Iso.inv_hom_id_assoc]
  rw [h1, Category.assoc, Category.assoc, reassoc_of% hT, h6]
  simp

/-- The chase behind `pullbackCounitLeg_crossing`, every object and morphism a variable. -/
private theorem spade_chase {C : Type*} [Category C]
    {P Q Q₁ Q₂ Q₃ O Q' T R N U U₁ V₁ V₂ V V' : C}
    {cl : P ⟶ Q} {Lc : Q ⟶ Q₁} {e₁ : Q₁ ⟶ Q₂} {ci : Q₂ ⟶ Q₃} {Lε : Q₃ ⟶ O}
    {e₁' : Q ⟶ Q'} {Lc' : Q' ⟶ Q₂} {ci' : Q' ⟶ T} {Lpc : T ⟶ Q₃} {m : T ⟶ R} {n : R ⟶ N}
    {o : N ⟶ O} {Ld : P ⟶ U₁} {d1 : P ⟶ U} {d2 : U ⟶ U₁} {c3' : U₁ ⟶ V₁} {e₂ : V₁ ⟶ V₂}
    {ci₂ : V₂ ⟶ N} {c3 : U ⟶ V} {k1 : V ⟶ V₁} {e₂' : V ⟶ V'} {k2 : V' ⟶ V₂} {c5i : V' ⟶ R}
    (h1 : Lc ≫ e₁ = e₁' ≫ Lc') (h2 : Lc' ≫ ci = ci' ≫ Lpc) (h3 : Lpc ≫ Lε = m ≫ n ≫ o)
    (h4 : Ld = d1 ≫ d2) (h5 : d2 ≫ c3' = c3 ≫ k1) (h6 : k1 ≫ e₂ = e₂' ≫ k2)
    (h7 : k2 ≫ ci₂ = c5i ≫ n) (hI : cl ≫ e₁' ≫ ci' ≫ m = d1 ≫ c3 ≫ e₂' ≫ c5i) :
    cl ≫ Lc ≫ e₁ ≫ ci ≫ Lε = Ld ≫ c3' ≫ e₂ ≫ ci₂ ≫ o := by
  rw [reassoc_of% h1, reassoc_of% h2, h3, h4]
  simp only [Category.assoc]
  rw [reassoc_of% h5, reassoc_of% h6, reassoc_of% h7]
  simp only [← Category.assoc] at hI ⊢
  rw [hI]

/-- **The counit leg of the first square, read through the crossing**: the counit leg of
`(τ_X ≫ a', p)` at the factorization through `τ_W ≫ f'`, after `L(τ_W ≫ f')^*` of
`Ra'_*Rτ_{X,*} ≅ R(τ_X ≫ a')_*` and the composition isomorphism for `(τ_W, f')`, is `Lτ_W^*` of
the counit leg of `(a', p')` followed by the crossing leg. -/
theorem pullbackCounitLeg_crossing {S X X' W W' : RingedSpace.{u, u}} (τX : X ⟶ X')
    (a' : X' ⟶ S) (τW : W ⟶ W') (p : W ⟶ X) (p' : W' ⟶ X') (f' : W' ⟶ S)
    (hp' : p' ≫ a' = f') (hsq : τW ≫ p' = p ≫ τX) (hp : p ≫ τX ≫ a' = τW ≫ f')
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedPullbackCompIsoCanonical τW f').hom.app
          ((derivedPushforward a').obj ((derivedPushforward τX).obj E)) ≫
        (derivedPullback (τW ≫ f')).map ((derivedPushforwardCompIso τX a').hom.app E) ≫
          (pullbackCounitLeg (τX ≫ a') p (τW ≫ f') hp).app E =
      (derivedPullback τW).map
          ((pullbackCounitLeg a' p' f' hp').app ((derivedPushforward τX).obj E)) ≫
        (derivedPullbackCompIsoCanonical τW p').hom.app ((derivedPushforward τX).obj E) ≫
          (pullbackCounitLeg τX p (τW ≫ p') hsq.symm).app E := by
  subst hp'
  have hL := pullbackCounitLeg_app_eq (τX ≫ a') p (τW ≫ p' ≫ a') hp E
  have hR := pullbackCounitLeg_app_eq τX p (τW ≫ p') hsq.symm E
  have hLd : (derivedPullback τW).map ((pullbackCounitLeg a' p' (p' ≫ a') rfl).app
        ((derivedPushforward τX).obj E)) =
      (derivedPullback τW).map ((derivedPullbackCompIsoCanonical p' a').inv.app
          ((derivedPushforward a').obj ((derivedPushforward τX).obj E))) ≫
        (derivedPullback τW).map ((derivedPullback p').map
          ((derivedAdjunction a').counit.app ((derivedPushforward τX).obj E))) :=
    (congrArg (derivedPullback τW).map
      (Stacks.Cohomology.KunnethNaive.pullbackCounitLeg_comp_app a' p'
        ((derivedPushforward τX).obj E))).trans (Functor.map_comp _ _ _)
  have h1 : (derivedPullback (τW ≫ p' ≫ a')).map ((derivedPushforwardCompIso τX a').hom.app E) ≫
      eqToHom (congrArg (fun z : W ⟶ S =>
        (derivedPullback z).obj ((derivedPushforward (τX ≫ a')).obj E)) hp.symm) =
      eqToHom (congrArg (fun z : W ⟶ S => (derivedPullback z).obj
          ((derivedPushforward a').obj ((derivedPushforward τX).obj E))) hp.symm) ≫
        (derivedPullback (p ≫ τX ≫ a')).map ((derivedPushforwardCompIso τX a').hom.app E) :=
    eqToHom_derivedPullback_naturality hp.symm _
  have h2 : (derivedPullback (p ≫ τX ≫ a')).map ((derivedPushforwardCompIso τX a').hom.app E) ≫
      (derivedPullbackCompIsoCanonical p (τX ≫ a')).inv.app
        ((derivedPushforward (τX ≫ a')).obj E) =
      (derivedPullbackCompIsoCanonical p (τX ≫ a')).inv.app
          ((derivedPushforward a').obj ((derivedPushforward τX).obj E)) ≫
        (derivedPullback p).map ((derivedPullback (τX ≫ a')).map
          ((derivedPushforwardCompIso τX a').hom.app E)) :=
    (derivedPullbackCompIsoCanonical p (τX ≫ a')).inv.naturality _
  have h3 : (derivedPullback p).map ((derivedPullback (τX ≫ a')).map
        ((derivedPushforwardCompIso τX a').hom.app E)) ≫
      (derivedPullback p).map ((derivedAdjunction (τX ≫ a')).counit.app E) =
      (derivedPullback p).map ((derivedPullbackCompIsoCanonical τX a').inv.app
          ((derivedPushforward a').obj ((derivedPushforward τX).obj E))) ≫
        (derivedPullback p).map ((derivedPullback τX).map
          ((derivedAdjunction a').counit.app ((derivedPushforward τX).obj E))) ≫
        (derivedPullback p).map ((derivedAdjunction τX).counit.app E) :=
    (Functor.map_comp _ _ _).symm.trans ((congrArg (derivedPullback p).map
      (derivedAdjunction_comp_counit τX a' E)).trans ((Functor.map_comp _ _ _).trans
        (congrArg (_ ≫ ·) (Functor.map_comp _ _ _))))
  have h5 : (derivedPullback τW).map ((derivedPullback p').map
        ((derivedAdjunction a').counit.app ((derivedPushforward τX).obj E))) ≫
      (derivedPullbackCompIsoCanonical τW p').hom.app ((derivedPushforward τX).obj E) =
      (derivedPullbackCompIsoCanonical τW p').hom.app
          ((derivedPullback a').obj ((derivedPushforward a').obj ((derivedPushforward τX).obj E))) ≫
        (derivedPullback (τW ≫ p')).map
          ((derivedAdjunction a').counit.app ((derivedPushforward τX).obj E)) :=
    (derivedPullbackCompIsoCanonical τW p').hom.naturality _
  have h6 : (derivedPullback (τW ≫ p')).map
        ((derivedAdjunction a').counit.app ((derivedPushforward τX).obj E)) ≫
      eqToHom (congrArg (fun z : W ⟶ X' =>
        (derivedPullback z).obj ((derivedPushforward τX).obj E)) hsq.symm.symm) =
      eqToHom (congrArg (fun z : W ⟶ X' =>
        (derivedPullback z).obj ((derivedPullback a').obj
            ((derivedPushforward a').obj ((derivedPushforward τX).obj E)))) hsq.symm.symm) ≫
        (derivedPullback (p ≫ τX)).map
          ((derivedAdjunction a').counit.app ((derivedPushforward τX).obj E)) :=
    eqToHom_derivedPullback_naturality hsq.symm.symm _
  have h7 : (derivedPullback (p ≫ τX)).map
        ((derivedAdjunction a').counit.app ((derivedPushforward τX).obj E)) ≫
      (derivedPullbackCompIsoCanonical p τX).inv.app ((derivedPushforward τX).obj E) =
      (derivedPullbackCompIsoCanonical p τX).inv.app
          ((derivedPullback a').obj ((derivedPushforward a').obj ((derivedPushforward τX).obj E))) ≫
        (derivedPullback p).map ((derivedPullback τX).map
          ((derivedAdjunction a').counit.app ((derivedPushforward τX).obj E))) :=
    (derivedPullbackCompIsoCanonical p τX).inv.naturality _
  have hI : (derivedPullbackCompIsoCanonical τW (p' ≫ a')).hom.app
      ((derivedPushforward a').obj ((derivedPushforward τX).obj E)) ≫
      eqToHom (congrArg (fun z : W ⟶ S => (derivedPullback z).obj
          ((derivedPushforward a').obj ((derivedPushforward τX).obj E))) hp.symm) ≫
        (derivedPullbackCompIsoCanonical p (τX ≫ a')).inv.app
            ((derivedPushforward a').obj ((derivedPushforward τX).obj E)) ≫
          (derivedPullback p).map ((derivedPullbackCompIsoCanonical τX a').inv.app
              ((derivedPushforward a').obj ((derivedPushforward τX).obj E))) =
      (derivedPullback τW).map ((derivedPullbackCompIsoCanonical p' a').inv.app
          ((derivedPushforward a').obj ((derivedPushforward τX).obj E))) ≫
        (derivedPullbackCompIsoCanonical τW p').hom.app
            ((derivedPullback a').obj ((derivedPushforward a').obj ((derivedPushforward τX).obj E)))
            ≫
          eqToHom (congrArg (fun z : W ⟶ X' =>
            (derivedPullback z).obj ((derivedPullback a').obj
                ((derivedPushforward a').obj ((derivedPushforward τX).obj E)))) hsq.symm.symm) ≫
            (derivedPullbackCompIsoCanonical p τX).inv.app
                ((derivedPullback a').obj ((derivedPushforward a').obj
                ((derivedPushforward τX).obj E))) :=
    iso_chase
      ((derivedPullbackCompIsoCanonical τW (p' ≫ a')).app
          ((derivedPushforward a').obj ((derivedPushforward τX).obj E)))
      ((derivedPullback τW).mapIso ((derivedPullbackCompIsoCanonical p' a').app
          ((derivedPushforward a').obj ((derivedPushforward τX).obj E))))
      ((derivedPullbackCompIsoCanonical τW p').app ((derivedPullback a').obj
          ((derivedPushforward a').obj ((derivedPushforward τX).obj E))))
      ((derivedPullbackCompIsoCanonical (τW ≫ p') a').app
          ((derivedPushforward a').obj ((derivedPushforward τX).obj E)))
      ((derivedPullbackCompIsoCanonical p τX).app ((derivedPullback a').obj
          ((derivedPushforward a').obj ((derivedPushforward τX).obj E))))
      ((derivedPullbackCompIsoCanonical (p ≫ τX) a').app
          ((derivedPushforward a').obj ((derivedPushforward τX).obj E)))
      ((derivedPullback p).mapIso ((derivedPullbackCompIsoCanonical τX a').app
          ((derivedPushforward a').obj ((derivedPushforward τX).obj E))))
      ((derivedPullbackCompIsoCanonical p (τX ≫ a')).app
          ((derivedPushforward a').obj ((derivedPushforward τX).obj E)))
      _ _
      (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_assoc_app
          τW p' a' _)
      (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_assoc_app p
          τX a' _)
      (derivedPullbackCompIsoCanonical_hom_app_eqToHom hsq a' _)
  exact (congrArg (fun t => _ ≫ _ ≫ t) hL).trans
    ((spade_chase h1 h2 h3 hLd h5 h6 h7 hI).trans (congrArg (fun t => _ ≫ _ ≫ t) hR.symm))

variable {S X X' Y Y' W W' : RingedSpace.{u, u}}
  (τX : X ⟶ X') (a' : X' ⟶ S) (τY : Y ⟶ Y') (b' : Y' ⟶ S) (τW : W ⟶ W')
  (p : W ⟶ X) (q : W ⟶ Y) (p' : W' ⟶ X') (q' : W' ⟶ Y')

end Geometry

section Kunneth

attribute [local instance 10000] HasDerivedCategory.standard

variable {S X X' Y Y' W W' : RingedSpace.{u, u}}
  (τX : X ⟶ X') (a' : X' ⟶ S) (τY : Y ⟶ Y') (b' : Y' ⟶ S) (τW : W ⟶ W') (f' : W' ⟶ S)
  (p : W ⟶ X) (q : W ⟶ Y) (p' : W' ⟶ X') (q' : W' ⟶ Y')
  (hp' : p' ≫ a' = f') (hq' : q' ≫ b' = f') (hpsq : τW ≫ p' = p ≫ τX) (hqsq : τW ≫ q' = q ≫ τY)
  (hp : p ≫ τX ≫ a' = τW ≫ f') (hq : q ≫ τY ≫ b' = τW ≫ f')
  [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology S.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The monoidality isomorphism of Stacks 079U for a composite, at a pair of objects: the
composition law `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp` read at
`(x, y)`, in the form consumed by `adjunctionBitensorMap_comp_legs`. -/
theorem pullbackTensorComparison_comp_app {Z₁ Z₂ Z₃ : RingedSpace.{u, u}} (g : Z₁ ⟶ Z₂)
    (h : Z₂ ⟶ Z₃)
    [HasSheafify (Opens.grothendieckTopology Z₁.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z₁.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify (Opens.grothendieckTopology Z₂.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z₂.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify (Opens.grothendieckTopology Z₃.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z₃.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (x y : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z₃))) :
    (derivedPullbackCompIsoCanonical g h).hom.app
          ((Functor.uncurry.obj (derivedTensorProductFunctor Z₃.sheaf)).obj (x, y)) ≫
        (pullbackTensorComparison (g ≫ h)).app (x, y) =
      (derivedPullback g).map ((pullbackTensorComparison h).app (x, y)) ≫
        (pullbackTensorComparison g).app ((derivedPullback h).obj x, (derivedPullback h).obj y) ≫
          (Functor.uncurry.obj (derivedTensorProductFunctor Z₁.sheaf)).map
            ((derivedPullbackCompIsoCanonical g h).hom.app x ×ₘ
              (derivedPullbackCompIsoCanonical g h).hom.app y) :=
  NatTrans.congr_app (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp g h)
    (x, y)

/-- **The relative Künneth map along a morphism of diagrams.**  After the identifications
`Ra'_*Rτ_{X,*} ≅ R(τ_X ≫ a')_*` and `Rb'_*Rτ_{Y,*} ≅ R(τ_Y ≫ b')_*`, the relative Künneth map of
the square `p ≫ (τ_X ≫ a') = τ_W ≫ f'` at `(E, M)` is the relative Künneth map of the square
`p' ≫ a' = f'` at `(Rτ_{X,*}E, Rτ_{Y,*}M)` followed by `Rf'_*` of the abstract Künneth map of
`Lτ_W^* ⊣ Rτ_{W,*}` with the crossing legs `Lτ_W^*Lp'^*Rτ_{X,*} ≅ L(p ≫ τ_X)^*Rτ_{X,*} ⟶ Lp^*`
and by `Rf'_*Rτ_{W,*} ≅ R(τ_W ≫ f')_*`.  Both Künneth maps are written as abstract Künneth maps,
which they are by definition (`Stacks.Cohomology.DerivedKunneth.kunnethMap_eq`). -/
theorem adjunctionBitensorMap_crossing (E : DerivedCategory
    (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)).map
        ((derivedPushforwardCompIso τX a').hom.app E ×ₘ
          (derivedPushforwardCompIso τY b').hom.app M) ≫
      adjunctionBitensorMap (derivedAdjunction (τW ≫ f'))
        (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
        (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf))
        (pullbackTensorComparison (τW ≫ f'))
        (pullbackCounitLeg (τX ≫ a') p (τW ≫ f') hp)
        (pullbackCounitLeg (τY ≫ b') q (τW ≫ f') hq) E M =
    adjunctionBitensorMap (derivedAdjunction f')
        (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
        (Functor.uncurry.obj (derivedTensorProductFunctor W'.sheaf))
        (pullbackTensorComparison f') (pullbackCounitLeg a' p' f' hp')
        (pullbackCounitLeg b' q' f' hq') ((derivedPushforward τX).obj E)
        ((derivedPushforward τY).obj M) ≫
      (derivedPushforward f').map ((derivedAdjunction τW).homEquiv _ _
        ((pullbackTensorComparison τW).app
            ((derivedPullback p').obj ((derivedPushforward τX).obj E),
              (derivedPullback q').obj ((derivedPushforward τY).obj M)) ≫
          (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
            (((derivedPullbackCompIsoCanonical τW p').hom.app ((derivedPushforward τX).obj E) ≫
                (pullbackCounitLeg τX p (τW ≫ p') hpsq.symm).app E) ×ₘ
              ((derivedPullbackCompIsoCanonical τW q').hom.app ((derivedPushforward τY).obj M) ≫
                (pullbackCounitLeg τY q (τW ≫ q') hqsq.symm).app M)))) ≫
        (derivedPushforwardCompIso τW f').hom.app
          ((Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).obj
            ((derivedPullback p).obj E, (derivedPullback q).obj M)) :=
  adjunctionBitensorMap_comp_legs (derivedAdjunction f') (derivedAdjunction τW)
    (derivedAdjunction (τW ≫ f')) (derivedPullbackCompIsoCanonical τW f')
    (derivedPushforwardCompIso τW f') (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor W'.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf))
    (pullbackTensorComparison f') (pullbackTensorComparison τW)
    (pullbackTensorComparison (τW ≫ f'))
    (pullbackCounitLeg (τX ≫ a') p (τW ≫ f') hp) (pullbackCounitLeg a' p' f' hp')
    (pullbackCounitLeg (τY ≫ b') q (τW ≫ f') hq) (pullbackCounitLeg b' q' f' hq')
    (derivedAdjunction_comp_homEquiv τW f')
    (pullbackTensorComparison_comp_app τW f')
    E ((derivedPushforward τX).obj E) M ((derivedPushforward τY).obj M)
    ((derivedPushforwardCompIso τX a').hom.app E) ((derivedPushforwardCompIso τY b').hom.app M)
    _ _
    (pullbackCounitLeg_crossing τX a' τW p p' f' hp' hpsq hp E)
    (pullbackCounitLeg_crossing τY b' τW q q' f' hq' hqsq hq M)

end Kunneth

end Stacks.Cohomology.DerivedKunneth

end
