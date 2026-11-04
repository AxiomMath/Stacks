module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FamilyPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RefinementFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ReprFpqcFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedSchemeDescentDatum

/-!
# Morphisms of descent data of a represented family, checked on the underlying schemes

Let `(f i : T i ⟶ U)` be a family of the big fppf category over a scheme `S` and let `D`, `E` be
two descent data of Stacks 04W3 relative to the family of representable algebraic spaces it
represents. A family of morphisms `app i : D.F i ⟶ E.F i` of the component modules is a
morphism of descent data exactly when it commutes with the pairwise isomorphisms, an equation on
the pairwise fibre products `yoneda.obj (T i) ×_{yoneda.obj U} yoneda.obj (T j)`. It is enough to
check the corresponding equation on the underlying schemes, at every object `Y` of the big fppf
category over `S` mapping to two members with equal composites to `U`, between the readings
`AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiTransitionOn` of the two data.

The equation on a pairwise fibre product may be checked after pullback along a scheme atlas of
it, whose two legs to the members are represented morphisms. On a representable test space the
pairwise isomorphisms are the readings conjugated by the comparison
`AlgebraicGeometry.Space.representedZariskiModulePullbackIso`, and reading is injective on
morphisms out of a quasi-coherent module.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_representedAtlas_pair`: a pairwise fibre
  product of a represented family carries a one-member étale covering by a representable
  algebraic space whose two legs to the members are represented morphisms with equal composites
  to `U`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.IsZariskiNatural`: the pairwise condition on the
  readings of a family of morphisms of the component modules on the underlying schemes.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_naturality_of_zariskiTransitionOn`:
  at a representable test space, a family of morphisms of the component modules which commutes
  with the readings of the pairwise isomorphisms on the underlying schemes commutes with those
  isomorphisms read there.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.naturality_of_zariskiTransitionOn`: the pairwise
  condition of Stacks 04W3 (2) itself, on the pairwise fibre products, from the condition on the
  readings.

## References

* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 041E](https://stacks.math.columbia.edu/tag/041E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Two morphisms of the big fppf category over `S` representing the same morphism of
representable algebraic spaces are equal. -/
theorem representedSpaceMap_injective {V W : BigFppfOver B S hS} {x y : V ⟶ W}
    (h : representedSpaceMap B S hS x = representedSpaceMap B S hS y) : x = y :=
  Yoneda.fullyFaithful.map_injective (congrArg (fun z => z.hom) h)

namespace QuasiCoherentDescent

variable {I : Type v} {U : BigFppfOver B S hS} (T : I → BigFppfOver B S hS)
  (f : ∀ i, T i ⟶ U)

/-- A pairwise fibre product of a represented family carries a one-member étale covering by a
representable algebraic space, whose two legs to the two members are represented morphisms with
equal composites to `U`. -/
theorem exists_representedAtlas_pair (i j : I) :
    ∃ (V : BigFppfOver B S hS) (a : V ⟶ T i) (b : V ⟶ T j) (_ : a ≫ f i = b ≫ f j)
      (c : representedAlgebraicSpace B S hS V ⟶
        pair B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f) i j),
      c ≫ pairFst B S hS (representedFamily B S hS T)
            (representedFamilyMap B S hS T f) i j = representedSpaceMap B S hS a ∧
        c ≫ pairSnd B S hS (representedFamily B S hS T)
            (representedFamilyMap B S hS T f) i j = representedSpaceMap B S hS b ∧
          IsEtaleCovering B S hS (fun _ : Unit => (representedAlgebraicSpace B S hS V).1)
            (fun _ => c.hom) := by
  obtain ⟨V, c₀, hsurj, hetale⟩ := (pair B S hS (representedFamily B S hS T)
    (representedFamilyMap B S hS T f) i j).property.exists_atlas
  set c : representedAlgebraicSpace B S hS V ⟶
    pair B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f) i j :=
    ObjectProperty.homMk c₀ with hc
  have key : ∀ {W : BigFppfOver B S hS} (g : representedAlgebraicSpace B S hS V ⟶
      representedAlgebraicSpace B S hS W),
      representedSpaceMap B S hS (Yoneda.fullyFaithful.preimage g.hom) = g := fun g =>
    ObjectProperty.hom_ext _ (Yoneda.fullyFaithful.map_preimage _)
  have ha := key (c ≫ pairFst B S hS (representedFamily B S hS T)
    (representedFamilyMap B S hS T f) i j)
  have hb := key (c ≫ pairSnd B S hS (representedFamily B S hS T)
    (representedFamilyMap B S hS T f) i j)
  have hab : Yoneda.fullyFaithful.preimage
        (c ≫ pairFst B S hS (representedFamily B S hS T)
          (representedFamilyMap B S hS T f) i j).hom ≫ f i =
      Yoneda.fullyFaithful.preimage
        (c ≫ pairSnd B S hS (representedFamily B S hS T)
          (representedFamilyMap B S hS T f) i j).hom ≫ f j := by
    refine representedSpaceMap_injective B S hS ?_
    rw [← representedSpaceMap_comp, ← representedSpaceMap_comp, ha, hb, Category.assoc,
      Category.assoc, pair_condition B S hS (representedFamily B S hS T)
        (representedFamilyMap B S hS T f) i j]
  refine ⟨V, _, _, hab, c, ha.symm, hb.symm, ?_⟩
  refine ⟨(pair B S hS (representedFamily B S hS T)
    (representedFamilyMap B S hS T f) i j).property,
    fun _ => isAlgebraicSpace_yoneda B S hS V,
    fun _ => (isEtale_iff_presheaf_of_yoneda B S hS c₀).2 hetale, ?_⟩
  rw [Set.iUnion_const, Set.range_eq_univ]
  exact (surjective_iff_surjective_pointsMap B S hS _
    (pair B S hS (representedFamily B S hS T)
      (representedFamilyMap B S hS T f) i j).property V c₀).1 hsurj

section Crossing

variable {T f}

/-- Cancelling the isomorphisms `ia` and `ie` from an equation between composites of
conjugates. -/
theorem conj_step {C₀ : Type*} [Category C₀] {pD qD pE qE rD sD rE sE : C₀}
    (ia : pD ≅ qD) (ib : pE ≅ qE) (ic : rD ≅ sD) (ie : rE ≅ sE)
    (X : pD ⟶ pE) (Y : rD ⟶ rE) (TD : qD ⟶ sD) (TE : qE ⟶ sE)
    (h : X ≫ ib.hom ≫ TE ≫ ie.inv = ia.hom ≫ TD ≫ ic.inv ≫ Y) :
    ia.inv ≫ X ≫ ib.hom ≫ TE = TD ≫ ic.inv ≫ Y ≫ ie.hom :=
  calc ia.inv ≫ X ≫ ib.hom ≫ TE
      = ia.inv ≫ (X ≫ ib.hom ≫ TE ≫ ie.inv) ≫ ie.hom := by simp
    _ = ia.inv ≫ (ia.hom ≫ TD ≫ ic.inv ≫ Y) ≫ ie.hom := by rw [h]
    _ = TD ≫ ic.inv ≫ Y ≫ ie.hom := by simp

/-- A square of morphisms whose image under a functor is a square of conjugates commutes after
that functor: if `G` carries `L₁`, `R₂` to the conjugates of `X`, `Y` by `ia`, `ib`, `ic`, `ie`,
and `L₂`, `R₁` to the middles `TE`, `TD` of conjugates `zE`, `zD`, and `X ≫ zE = zD ≫ Y`, then
`G` identifies `L₁ ≫ L₂` with `R₁ ≫ R₂`. -/
theorem reading_step {C₀ D₀ : Type*} [Category C₀] [Category D₀] (G : C₀ ⥤ D₀)
    {A A' Bb Bb' : C₀} (L₁ : A ⟶ A') (L₂ : A' ⟶ Bb') (R₁ : A ⟶ Bb) (R₂ : Bb ⟶ Bb')
    {pD pE rD rE : D₀} (ia : pD ≅ G.obj A) (ib : pE ≅ G.obj A') (ic : rD ≅ G.obj Bb)
    (ie : rE ≅ G.obj Bb') (X : pD ⟶ pE) (Y : rD ⟶ rE) (TD : G.obj A ⟶ G.obj Bb)
    (TE : G.obj A' ⟶ G.obj Bb') (zD : pD ⟶ rD) (zE : pE ⟶ rE)
    (hTD : TD = G.map R₁) (hTE : TE = G.map L₂)
    (hL : G.map L₁ = ia.inv ≫ X ≫ ib.hom) (hR : G.map R₂ = ic.inv ≫ Y ≫ ie.hom)
    (hzD : zD = ia.hom ≫ TD ≫ ic.inv) (hzE : zE = ib.hom ≫ TE ≫ ie.inv)
    (h : X ≫ zE = zD ≫ Y) : G.map (L₁ ≫ L₂) = G.map (R₁ ≫ R₂) := by
  subst hTD hTE hzD hzE
  rw [G.map_comp, G.map_comp, hL, hR]
  simp only [Category.assoc] at h ⊢
  exact conj_step ia ib ic ie X Y (G.map R₁) (G.map L₂) h

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- Reading a morphism of quasi-coherent `𝒪`-modules on a representable algebraic space on the
underlying scheme is injective. -/
theorem representedZariski_map_injective {V : BigFppfOver B S hS}
    {F F' : SheafOfModules.{u} (representedStructureRingSheaf B S hS V)}
    (hF : F.IsQuasicoherentOnSite) {x y : F ⟶ F'}
    (h : (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
      ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map x) =
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
      ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map y)) : x = y :=
  (bijective_representedZariski_map B S hS F F' hF).1 h

/-- The reading of the inverse image of a morphism of quasi-coherent `𝒪`-modules along a
represented morphism is the pullback of its reading, conjugated by the comparison
`AlgebraicGeometry.Space.representedZariskiModulePullbackIso`. -/
theorem representedZariski_map_modulePullback {V W : BigFppfOver B S hS} (g : V ⟶ W)
    {F F' : SheafOfModules.{u} (representedStructureRingSheaf B S hS W)}
    (hF : F.IsQuasicoherentOnSite) (hF' : F'.IsQuasicoherentOnSite) (ψ : F ⟶ F') :
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
      ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map
        ((modulePullback B S hS (representedSpaceMap B S hS g)).map ψ)) =
      (representedZariskiModulePullbackIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g) F hF).inv ≫
        (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
            (associatedBigEtaleSite B) g.left)).map
          ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj W) W.left.property).map
              ((representedSmallEtaleModuleEquivalence B S hS W).inverse.map ψ)) ≫
        (representedZariskiModulePullbackIso B S hS g
          (relativelyRepresentable_yoneda_map B S hS g) F' hF').hom := by
  rw [representedZariskiModulePullbackIso_naturality B S hS g
    (relativelyRepresentable_yoneda_map B S hS g) hF hF' ψ, Iso.inv_hom_id_assoc]

/-- At a representable test space, a family of morphisms of the component modules which
commutes with the readings of the pairwise isomorphisms on the underlying schemes commutes with
those isomorphisms read there. -/
theorem transitionOn_naturality_of_zariskiTransitionOn
    {D E : DescentDatum B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f)}
    (app : ∀ t, D.F t ⟶ E.F t) {Y : BigFppfOver B S hS} {q : Y ⟶ U} {i j : I}
    (a : Y ⟶ T i) (b : Y ⟶ T j) (ha : a ≫ f i = q) (hb : b ≫ f j = q)
    (hzar : (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
                (associatedBigEtaleSite B) a.left)).map
              ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                    ((BigFppfOver.toScheme B S hS).obj (T i)) (T i).left.property).map
                  ((representedSmallEtaleModuleEquivalence B S hS (T i)).inverse.map (app i))) ≫
          (zariskiTransitionOn B S hS T f E a b ha hb).hom =
        (zariskiTransitionOn B S hS T f D a b ha hb).hom ≫
          (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
                (associatedBigEtaleSite B) b.left)).map
              ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                    ((BigFppfOver.toScheme B S hS).obj (T j)) (T j).left.property).map
                  ((representedSmallEtaleModuleEquivalence B S hS (T j)).inverse.map (app j)))) :
    (modulePullback B S hS (representedSpaceMap B S hS a)).map (app i) ≫
        (transitionOn B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f)
          E.F E.transition i j (representedPairLift B S hS T f a b ha hb)
          (representedSpaceMap B S hS a) (representedSpaceMap B S hS b)
          (representedPairLift_fst B S hS T f a b ha hb)
          (representedPairLift_snd B S hS T f a b ha hb)).hom =
      (transitionOn B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f)
        D.F D.transition i j (representedPairLift B S hS T f a b ha hb)
        (representedSpaceMap B S hS a) (representedSpaceMap B S hS b)
        (representedPairLift_fst B S hS T f a b ha hb)
        (representedPairLift_snd B S hS T f a b ha hb)).hom ≫
        (modulePullback B S hS (representedSpaceMap B S hS b)).map (app j) := by
  refine representedZariski_map_injective B S hS
    (isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS a
      (relativelyRepresentable_yoneda_map B S hS a) (D.F i) (D.quasicoherent i)) ?_
  exact reading_step ((representedSmallEtaleModuleEquivalence B S hS Y).inverse ⋙
      _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj Y) Y.left.property) _ _ _ _
    (representedZariskiModulePullbackIso B S hS a
        (relativelyRepresentable_yoneda_map B S hS a) (D.F i) (D.quasicoherent i))
    (representedZariskiModulePullbackIso B S hS a
        (relativelyRepresentable_yoneda_map B S hS a) (E.F i) (E.quasicoherent i))
    (representedZariskiModulePullbackIso B S hS b
        (relativelyRepresentable_yoneda_map B S hS b) (D.F j) (D.quasicoherent j))
    (representedZariskiModulePullbackIso B S hS b
        (relativelyRepresentable_yoneda_map B S hS b) (E.F j) (E.quasicoherent j))
    _ _ _ _ _ _ rfl rfl
    (representedZariski_map_modulePullback B S hS a (D.quasicoherent i) (E.quasicoherent i)
      (app i))
    (representedZariski_map_modulePullback B S hS b (D.quasicoherent j) (E.quasicoherent j)
      (app j))
    (zariskiTransitionOn_hom B S hS T f D a b ha hb)
    (zariskiTransitionOn_hom B S hS T f E a b ha hb) hzar

/-- The pairwise condition on the readings of a family of morphisms of the component modules on
the underlying schemes: at every object `Y` of the big fppf category over `S` mapping to two
members of the family with equal composites to `U`, the reading of the component at the first
member, pulled back to the scheme underlying `Y`, commutes with the readings
`AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiTransitionOn` of the pairwise isomorphisms
of the two data. -/
def IsZariskiNatural
    {D E : DescentDatum B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f)}
    (app : ∀ t, D.F t ⟶ E.F t) : Prop :=
  ∀ (Y : BigFppfOver B S hS) (q : Y ⟶ U) (i j : I) (a : Y ⟶ T i) (b : Y ⟶ T j)
      (ha : a ≫ f i = q) (hb : b ≫ f j = q),
      (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
                (associatedBigEtaleSite B) a.left)).map
              ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                    ((BigFppfOver.toScheme B S hS).obj (T i)) (T i).left.property).map
                  ((representedSmallEtaleModuleEquivalence B S hS (T i)).inverse.map (app i))) ≫
          (zariskiTransitionOn B S hS T f E a b ha hb).hom =
        (zariskiTransitionOn B S hS T f D a b ha hb).hom ≫
          (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
                (associatedBigEtaleSite B) b.left)).map
              ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                    ((BigFppfOver.toScheme B S hS).obj (T j)) (T j).left.property).map
                  ((representedSmallEtaleModuleEquivalence B S hS (T j)).inverse.map (app j)))

/-- A family of morphisms of the component modules of two descent data of a represented family
which commutes with the readings of the pairwise isomorphisms on the underlying schemes commutes
with the pairwise isomorphisms themselves. This is the pairwise condition of a morphism of
descent data, Stacks 04W3 (2), for a represented family, checked on the underlying schemes. -/
theorem naturality_of_zariskiTransitionOn
    {D E : DescentDatum B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f)}
    (app : ∀ t, D.F t ⟶ E.F t) (hzar : IsZariskiNatural B S hS app) (i j : I) :
    (modulePullback B S hS (pairFst B S hS (representedFamily B S hS T)
            (representedFamilyMap B S hS T f) i j)).map (app i) ≫ (E.transition i j).hom =
      (D.transition i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS (representedFamily B S hS T)
          (representedFamilyMap B S hS T f) i j)).map (app j) := by
  obtain ⟨V, a, b, hab, c, hca, hcb, hcov⟩ := exists_representedAtlas_pair B S hS T f i j
  have hcL : c = representedPairLift B S hS T f a b hab rfl := by
    refine (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (representedFamilyMap B S hS T f i) (representedFamilyMap B S hS T f j)).hom_ext ?_ ?_
    · rw [hca, representedPairLift_fst]
    · rw [hcb, representedPairLift_snd]
  have hcov' : IsEtaleCovering B S hS (fun _ : Unit => (representedAlgebraicSpace B S hS V).1)
      (fun _ => (representedPairLift B S hS T f a b hab rfl).hom) := by
    rwa [← hcL]
  have hnat := transitionOn_naturality_of_zariskiTransitionOn B S hS app a b hab rfl
    (hzar V (b ≫ f j) i j a b hab rfl)
  refine naturality_of_transitionOn_of_isEtaleCovering B S hS (representedFamily B S hS T)
    (representedFamilyMap B S hS T f) app i j (representedPairLift B S hS T f a b hab rfl)
    (representedSpaceMap B S hS a) (representedSpaceMap B S hS b)
    (representedPairLift_fst B S hS T f a b hab rfl)
    (representedPairLift_snd B S hS T f a b hab rfl) hcov' ?_
  convert hnat using 1

end Crossing

end QuasiCoherentDescent

end AlgebraicGeometry.Space

end
