module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ShriekAdjunction
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtensionByZeroCovariance

/-!
# The adjointness of `Rf_!` and `f^!` and the covariance of extension by zero, abstractly

Let `j^* : 𝒟 ⥤ 𝒞` and `j'^* : 𝒟 ⥤ 𝒞'` carry Deligne-system assignments, let `i^* : 𝒞 ⥤ 𝒞'` with
`j^* ⋙ i^* ≅ j'^*`, and let `Rf̄_* : 𝒟 ⥤ ℰ` be as in `CategoryTheory.shriekHomEquiv`, so that
`Rf_! = Rf̄_* ∘ Rj_!` and `Rg_! = Rf̄_* ∘ Rj'_!`. Applying `Rf̄_*` to the canonical map
`Rj'_!(i^* K) ⟶ Rj_! K` of [Stacks, Tag 0G4Y] gives `Rg_!(i^* K) ⟶ Rf_! K`. Under the adjointness
bijections `Hom(Rf_! K, L) = Hom(K, j^* f̄^! L)` of [Stacks, Tag 0G51], composing with this map is
restriction: `Hom(K, j^* f̄^! L) ⟶ Hom(i^* K, i^* j^* f̄^! L) = Hom(i^* K, j'^* f̄^! L)`, provided
the restrictions on the large categories are compatible with those on the small ones.

## Main results

* `CategoryTheory.lan_map_restrictionHomNatTrans_comp_baseChangePointsHom`: the base change map
  of functors of points is compatible with restriction.
* `CategoryTheory.shriekHomEquiv_covariance`: composing with `Rf̄_*` of the map of
  [Stacks, Tag 0G4Y] is restriction, under the bijections of [Stacks, Tag 0G51].

## References

* [Stacks Project, Tag 0G56](https://stacks.math.columbia.edu/tag/0G56)
* [Stacks Project, Tag 0G4Y](https://stacks.math.columbia.edu/tag/0G4Y)
* [Stacks Project, Tag 0G51](https://stacks.math.columbia.edu/tag/0G51)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

namespace CategoryTheory

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒞' : Type u₂} [Category.{v} 𝒞']
  {𝒟 : Type u₃} [Category.{v} 𝒟] {𝒟p : Type u₄} [Category.{v} 𝒟p]
  {𝒞u : Type u₅} [Category.{v} 𝒞u] {𝒞u' : Type u₆} [Category.{v} 𝒞u']
  (jX : 𝒟 ⥤ 𝒞) (jX' : 𝒟 ⥤ 𝒞') (istar : 𝒞 ⥤ 𝒞') (e : jX ⋙ istar ≅ jX')
  (ιX : 𝒟 ⥤ 𝒟p) (ιU : 𝒞 ⥤ 𝒞u) (ιU' : 𝒞' ⥤ 𝒞u') (jY : 𝒟p ⥤ 𝒞u) (jY' : 𝒟p ⥤ 𝒞u')
  (β : ιX ⋙ jY ≅ jX ⋙ ιU) (β' : ιX ⋙ jY' ≅ jX' ⋙ ιU') (istarU : 𝒞u ⥤ 𝒞u')
  (δ : ιU ⋙ istarU ≅ istar ⋙ ιU') (ε : jY ⋙ istarU ≅ jY')

/-- **The base change map of functors of points is compatible with restriction.** If the
identifications `β`, `β'` of the restrictions on the large categories with those on the small ones
are compatible with `e : j^* ⋙ i^* ≅ j'^*`, `δ` and `ε`, then the left Kan extension of the
restriction map `Hom(K, j^* -) ⟶ Hom(i^* K, j'^* -)` followed by the base change map for `j'` is
the base change map for `j` followed by restriction `Hom(K, j^* -) ⟶ Hom(i^* K, j'^* -)` on the
large categories. -/
public lemma lan_map_restrictionHomNatTrans_comp_baseChangePointsHom
    [∀ P : 𝒟 ⥤ Type v, ιX.HasLeftKanExtension P]
    (hc : ∀ N : 𝒟, ιU'.map (e.hom.app N) ≫ β'.inv.app N =
      δ.inv.app (jX.obj N) ≫ istarU.map (β.inv.app N) ≫ ε.hom.app (ιX.obj N)) (K : 𝒞) :
    ιX.lan.map (restrictionHomNatTrans jX jX' istar e K) ≫
        baseChangePointsHom ιX ιU' β' (istar.obj K) =
      baseChangePointsHom ιX ιU β K ≫ restrictionHomNatTrans jY jY' istarU ε (ιU.obj K) ≫
        Functor.whiskerLeft jY' (coyoneda.map (δ.inv.app K).op) := by
  rw [baseChangePointsHom, baseChangePointsHom,
    ← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  ext N α
  show ιU'.map (istar.map α ≫ e.hom.app N) ≫ β'.inv.app N =
    δ.inv.app K ≫ istarU.map (ιU.map α ≫ β.inv.app N) ≫ ε.hom.app (ιX.obj N)
  have hδ : δ.inv.app K ≫ istarU.map (ιU.map α) = ιU'.map (istar.map α) ≫ δ.inv.app (jX.obj N) :=
    (δ.inv.naturality α).symm
  rw [ιU'.map_comp, Category.assoc, hc, istarU.map_comp, Category.assoc, reassoc_of% hδ]

variable {ℰ : Type u₇} [Category.{v} ℰ] {ℰp : Type u₈} [Category.{v} ℰp]
  (direct : 𝒟 ⥤ ℰ) (ιY : ℰ ⥤ ℰp) (directPlus : 𝒟p ⥤ ℰp)
  (γ : direct ⋙ ιY ≅ ιX ⋙ directPlus) {shriek : ℰp ⥤ 𝒟p} (adj : directPlus ⊣ shriek)
  [∀ A : 𝒟 ⥤ Type v, direct.HasLeftKanExtension A] [∀ A : ℰ ⥤ Type v, ιY.HasLeftKanExtension A]
  [∀ A : 𝒟 ⥤ Type v, ιX.HasLeftKanExtension A]
  [∀ A : 𝒟p ⥤ Type v, directPlus.HasLeftKanExtension A]
  [∀ A : 𝒟 ⥤ Type v, (direct ⋙ ιY).HasLeftKanExtension A]
  [∀ A : 𝒟 ⥤ Type v, (ιX ⋙ directPlus).HasLeftKanExtension A]
  (A : DeligneSystemValues jX) (A' : DeligneSystemValues jX')
  (hlift : ∀ (K : 𝒞) (N : 𝒟p), RestrictionLifting (A.system K ⋙ ιX) jY N)
  (hlift' : ∀ (K : 𝒞') (N : 𝒟p), RestrictionLifting (A'.system K ⋙ ιX) jY' N)

/-- `Rf̄_*` of the map `Rj'_!(i^* K) ⟶ Rj_! K` of [Stacks, Tag 0G4Y], viewed in `Pro-ℰ⁺`, acts on
functors of points as the left Kan extension of the restriction map. -/
public lemma shriekPro_covariance_unop_hom (K : 𝒞) :
    ((ProSeq.map ιY).map ((ProSeq.map direct).map
        ((extensionByZeroCovariance jX jX' istar e A.toAssignment
          A'.toAssignment).app K))).unop.hom =
      ιY.lan.map (direct.lan.map (restrictionHomNatTrans jX jX' istar e K)) :=
  rfl

/-- **Covariance of `CategoryTheory.shriekPointsIso`**: under the identifications of the functors
of points of `Rf_! K` and `Rg_!(i^* K)` with `Hom(K, j^* f̄^! -)` and `Hom(i^* K, j'^* f̄^! -)`,
`Rf̄_*` of the map of [Stacks, Tag 0G4Y] is restriction. -/
public lemma shriekPro_covariance_unop_hom_comp_shriekPointsIso_hom
    (hc : ∀ N : 𝒟, ιU'.map (e.hom.app N) ≫ β'.inv.app N =
      δ.inv.app (jX.obj N) ≫ istarU.map (β.inv.app N) ≫ ε.hom.app (ιX.obj N)) (K : 𝒞) :
    ((ProSeq.map ιY).map ((ProSeq.map direct).map
        ((extensionByZeroCovariance jX jX' istar e A.toAssignment
          A'.toAssignment).app K))).unop.hom ≫
        (shriekPointsIso ιX direct ιY directPlus γ adj A' ιU' jY' β' hlift' (istar.obj K)).hom =
      (shriekPointsIso ιX direct ιY directPlus γ adj A ιU jY β hlift K).hom ≫
        Functor.whiskerLeft shriek (restrictionHomNatTrans jY jY' istarU ε (ιU.obj K) ≫
          Functor.whiskerLeft jY' (coyoneda.map (δ.inv.app K).op)) := by
  rw [shriekPro_covariance_unop_hom]
  have h₁ := (shriekLanIso ιX direct ιY directPlus γ adj).hom.naturality
    (restrictionHomNatTrans jX jX' istar e K)
  have h₂ := lan_map_restrictionHomNatTrans_comp_baseChangePointsHom jX jX' istar e ιX ιU ιU' jY jY'
    β β' istarU δ ε hc K
  dsimp only [Functor.comp_map] at h₁
  show ιY.lan.map (direct.lan.map (restrictionHomNatTrans jX jX' istar e K)) ≫
      (shriekLanIso ιX direct ιY directPlus γ adj).hom.app (jX' ⋙ coyoneda.obj (op (istar.obj K))) ≫
        (proPointsWhisker shriek).map (baseChangePointsHom ιX ιU' β' (istar.obj K)) =
      ((shriekLanIso ιX direct ιY directPlus γ adj).hom.app (jX ⋙ coyoneda.obj (op K)) ≫
        (proPointsWhisker shriek).map (baseChangePointsHom ιX ιU β K)) ≫
        (proPointsWhisker shriek).map (restrictionHomNatTrans jY jY' istarU ε (ιU.obj K) ≫
          Functor.whiskerLeft jY' (coyoneda.map (δ.inv.app K).op))
  rw [← Category.assoc, h₁, Category.assoc, Category.assoc, ← Functor.map_comp, h₂,
    Functor.map_comp]

/-- **Composing with `Rf̄_*` of the map of [Stacks, Tag 0G4Y] is restriction**, under the
adjointness bijections of [Stacks, Tag 0G51]: for `φ : Rf_! K ⟶ L`, the morphism
`Rg_!(i^* K) ⟶ Rf_! K ⟶ L` corresponds to the restriction to `i^* K` of the morphism
`K ⟶ j^* f̄^! L` corresponding to `φ`. -/
public lemma shriekHomEquiv_covariance
    (hc : ∀ N : 𝒟, ιU'.map (e.hom.app N) ≫ β'.inv.app N =
      δ.inv.app (jX.obj N) ≫ istarU.map (β.inv.app N) ≫ ε.hom.app (ιX.obj N)) (K : 𝒞) (L : ℰp)
    (φ : shriekPro direct ιY A K ⟶ ProSeq.const.obj L) :
    shriekHomEquiv ιX direct ιY directPlus γ adj A' ιU' jY' β' hlift' (istar.obj K) L
        ((ProSeq.map ιY).map ((ProSeq.map direct).map
          ((extensionByZeroCovariance jX jX' istar e A.toAssignment A'.toAssignment).app K)) ≫ φ) =
      δ.inv.app K ≫
        istarU.map (shriekHomEquiv ιX direct ιY directPlus γ adj A ιU jY β hlift K L φ) ≫
        ε.hom.app (shriek.obj L) := by
  have h : ProSeq.homConstEquiv _ L ((ProSeq.map ιY).map ((ProSeq.map direct).map
        ((extensionByZeroCovariance jX jX' istar e A.toAssignment A'.toAssignment).app K)) ≫ φ) =
      ((ProSeq.map ιY).map ((ProSeq.map direct).map
        ((extensionByZeroCovariance jX jX' istar e A.toAssignment
          A'.toAssignment).app K))).unop.hom.app
          L (ProSeq.homConstEquiv _ L φ) := by
    rfl
  simp only [shriekHomEquiv, Equiv.trans_apply, Iso.toEquiv_fun, h]
  exact ConcreteCategory.congr_hom (congr_app
    (shriekPro_covariance_unop_hom_comp_shriekPointsIso_hom jX jX' istar e ιX ιU ιU' jY jY' β β'
      istarU δ ε direct ιY directPlus γ adj A A' hlift hlift' hc K) L) _

end CategoryTheory

end
