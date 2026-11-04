module

public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.LocallyGivenOfCovering

/-!
# Morphisms of glueing data and the locally given objects of a covering

Let `(C, O_C)` be a ringed site with fibre products and `f_i : U_i ⟶ X` a family of arrows.
For an arrow `a : V ⟶ U` and a morphism `θ : a^*A ⟶ a^*B` of restrictions to `V`, and an arrow
`c : W ⟶ V`, the restriction of `θ` along `c`, read through `x = c ≫ a`, is a morphism
`x^*A ⟶ x^*B`; restricting the restriction of a morphism `β : A ⟶ B` gives the restriction of
`β`, and restricting twice is restricting along the composite.

For two families `(E_i, ρ_{ij})`, `(E'_i, ρ'_{ij})` of derived objects on the `U_i` with
isomorphisms on the overlaps, a family `β_i : E'_i ⟶ E_i` carrying `ρ'_{ij}` to `ρ_{ij}` induces
on the locally given objects of Situation 0DC9 attached to the two families morphisms
compatible with all the isomorphisms `ρ_g`. Conversely, compatibility with an isomorphism `ρ_g`
can be tested on the slices of `C`, before transport to the iterated slices.

## Main definitions

* `AlgebraicGeometry.RingedSite.restrictAlong`: the restriction of `θ : a^*A ⟶ a^*B` along
  `c : W ⟶ V`, read through `c ≫ a = x`.

## Main results

* `AlgebraicGeometry.RingedSite.restrictAlong_map`, `.restrictAlong_comp_left`: restriction of
  a restriction, and restriction in two steps.
* `AlgebraicGeometry.RingedSite.CoveringGlueing.indexRhoBase_naturality`,
  `AlgebraicGeometry.RingedSite.CoveringGlueing.indexRho_naturality`: compatibility of the
  morphisms induced by a morphism of glueing data with the isomorphisms `ρ_g`.
* `AlgebraicGeometry.RingedSite.CoveringGlueing.indexRho_comm_iff`: compatibility with `ρ_g`
  is tested on the slices of `C`.
* `AlgebraicGeometry.RingedSite.CoveringGlueing.restrictAlong_overlapIso`: compatibility of a
  restriction with the isomorphisms attached to the overlaps is inherited by its restrictions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSite.{u, u, u}}

/-- **The restriction along `c : W ⟶ V` of a morphism `θ : a^*A ⟶ a^*B` of restrictions to
`V`**, read through `c ≫ a = x` as a morphism `x^*A ⟶ x^*B`. -/
def restrictAlong {U V W : X.C} (a : V ⟶ U) (c : W ⟶ V) {x : W ⟶ U} (hx : c ≫ a = x)
    {A B : LocalDerivedCategory.{0} X U}
    (θ : (derivedOverMap.{0} X a).obj A ⟶ (derivedOverMap.{0} X a).obj B) :
    (derivedOverMap.{0} X x).obj A ⟶ (derivedOverMap.{0} X x).obj B :=
  (derivedOverMapComp.{0} X hx).hom.app A ≫ (derivedOverMap.{0} X c).map θ ≫
    (derivedOverMapComp.{0} X hx).inv.app B

/-- The restriction of an isomorphism, as an isomorphism. -/
def restrictAlongIso {U V W : X.C} (a : V ⟶ U) (c : W ⟶ V) {x : W ⟶ U} (hx : c ≫ a = x)
    {A B : LocalDerivedCategory.{0} X U}
    (θ : (derivedOverMap.{0} X a).obj A ≅ (derivedOverMap.{0} X a).obj B) :
    (derivedOverMap.{0} X x).obj A ≅ (derivedOverMap.{0} X x).obj B :=
  (derivedOverMapComp.{0} X hx).app A ≪≫ (derivedOverMap.{0} X c).mapIso θ ≪≫
    ((derivedOverMapComp.{0} X hx).app B).symm

/-- The forward morphism of the restriction of an isomorphism is the restriction of its forward
morphism. -/
@[simp]
theorem restrictAlongIso_hom {U V W : X.C} (a : V ⟶ U) (c : W ⟶ V) {x : W ⟶ U} (hx : c ≫ a = x)
    {A B : LocalDerivedCategory.{0} X U}
    (θ : (derivedOverMap.{0} X a).obj A ≅ (derivedOverMap.{0} X a).obj B) :
    (restrictAlongIso a c hx θ).hom = restrictAlong a c hx θ.hom :=
  rfl

/-- **Restricting the restriction of a morphism is restricting the morphism.** -/
theorem restrictAlong_map {U V W : X.C} (a : V ⟶ U) (c : W ⟶ V) {x : W ⟶ U} (hx : c ≫ a = x)
    {A B : LocalDerivedCategory.{0} X U} (β : A ⟶ B) :
    restrictAlong a c hx ((derivedOverMap.{0} X a).map β) = (derivedOverMap.{0} X x).map β := by
  have n := (derivedOverMapComp.{0} X hx).hom.naturality β
  simp only [Functor.comp_map] at n
  rw [restrictAlong, ← reassoc_of% n, Iso.hom_inv_id_app, Category.comp_id]

/-- The restriction depends on the arrow `c` only through its value. -/
theorem restrictAlong_congr {U V W : X.C} (a : V ⟶ U) {c c' : W ⟶ V} (hc : c = c')
    {x : W ⟶ U} (hx : c ≫ a = x) (hx' : c' ≫ a = x) {A B : LocalDerivedCategory.{0} X U}
    (θ : (derivedOverMap.{0} X a).obj A ⟶ (derivedOverMap.{0} X a).obj B) :
    restrictAlong a c hx θ = restrictAlong a c' hx' θ := by
  subst hc
  rfl

/-- Restriction along `c` takes a composite of morphisms to the composite of restrictions. -/
theorem restrictAlong_comp {U V W : X.C} (a : V ⟶ U) (c : W ⟶ V) {x : W ⟶ U} (hx : c ≫ a = x)
    {A B D : LocalDerivedCategory.{0} X U}
    (θ : (derivedOverMap.{0} X a).obj A ⟶ (derivedOverMap.{0} X a).obj B)
    (θ' : (derivedOverMap.{0} X a).obj B ⟶ (derivedOverMap.{0} X a).obj D) :
    restrictAlong a c hx (θ ≫ θ') = restrictAlong a c hx θ ≫ restrictAlong a c hx θ' := by
  simp [restrictAlong]

/-- **Restriction in two steps is restriction along the composite.** -/
theorem restrictAlong_comp_left {U V W W' : X.C} (a : V ⟶ U) (c : W ⟶ V) {x : W ⟶ U}
    (hx : c ≫ a = x) (h : W' ⟶ W) {x' : W' ⟶ U} (hh : h ≫ x = x') (hx' : (h ≫ c) ≫ a = x')
    {A B : LocalDerivedCategory.{0} X U}
    (θ : (derivedOverMap.{0} X a).obj A ⟶ (derivedOverMap.{0} X a).obj B) :
    restrictAlong a (h ≫ c) hx' θ =
      (derivedOverMapComp.{0} X hh).hom.app A ≫ (derivedOverMap.{0} X h).map
        (restrictAlong a c hx θ) ≫ (derivedOverMapComp.{0} X hh).inv.app B := by
  have assA := X.derivedOverMapComp_assoc a c h hx (rfl : h ≫ c = h ≫ c) hh hx' A
  have assB := X.derivedOverMapComp_assoc a c h hx (rfl : h ≫ c = h ≫ c) hh hx' B
  have assB' : (derivedOverMap.{0} X h).map ((derivedOverMapComp.{0} X hx).inv.app B) ≫
        (derivedOverMapComp.{0} X hh).inv.app B =
      (derivedOverMapComp.{0} X (rfl : h ≫ c = h ≫ c)).inv.app
          ((derivedOverMap.{0} X a).obj B) ≫ (derivedOverMapComp.{0} X hx').inv.app B := by
    rw [← cancel_epi ((derivedOverMapComp.{0} X hh).hom.app B ≫
      (derivedOverMap.{0} X h).map ((derivedOverMapComp.{0} X hx).hom.app B))]
    conv_rhs => rw [assB]
    simp [← Functor.map_comp_assoc]
  have nat := (derivedOverMapComp.{0} X (rfl : h ≫ c = h ≫ c)).hom.naturality θ
  simp only [Functor.comp_map] at nat
  simp only [restrictAlong, Functor.map_comp, Category.assoc]
  rw [assB', reassoc_of% assA, ← reassoc_of% nat, Iso.hom_inv_id_app_assoc]

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.RingedSite.CoveringGlueing

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSite.{u, u, u}} [HasPullbacks X.C] {X₀ : X.C} {ι : Type u} {U : ι → X.C}
  (f : ∀ i, U i ⟶ X₀) {E E' : ∀ i, LocalDerivedCategory.{0} X (U i)}
  (ρ : ∀ i j, (derivedOverMap.{0} X (pullback.fst (f i) (f j))).obj (E i) ≅
    (derivedOverMap.{0} X (pullback.snd (f i) (f j))).obj (E j))
  (ρ' : ∀ i j, (derivedOverMap.{0} X (pullback.fst (f i) (f j))).obj (E' i) ≅
    (derivedOverMap.{0} X (pullback.snd (f i) (f j))).obj (E' j))

/-- **A morphism of glueing data is compatible with the isomorphisms `indexRhoBase`.** -/
theorem indexRhoBase_naturality (β : ∀ i, E' i ⟶ E i)
    (hβ : ∀ i j, (derivedOverMap.{0} X (pullback.fst (f i) (f j))).map (β i) ≫ (ρ i j).hom =
      (ρ' i j).hom ≫ (derivedOverMap.{0} X (pullback.snd (f i) (f j))).map (β j))
    {b b' : IndexCategory f} (g : b' ⟶ b) :
    (derivedOverMap.{0} X g.hom.left).map ((derivedOverMap.{0} X b.a).map (β b.i)) ≫
        (indexRhoBase f E ρ g).hom =
      (indexRhoBase f E' ρ' g).hom ≫ (derivedOverMap.{0} X b'.a).map (β b'.i) := by
  have n := (derivedOverMapComp.{0} X (rfl : g.hom.left ≫ b.a = g.hom.left ≫ b.a)).inv.naturality
    (β b.i)
  simp only [Functor.comp_map] at n
  simp only [indexRhoBase, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Category.assoc]
  rw [reassoc_of% n, overlapIso_naturality f ρ ρ' β hβ]

/-- **Compatibility with an isomorphism `ρ_g` of the transported locally given objects is
tested on the slices of `C`.** -/
theorem indexRho_comm_iff {b b' : IndexCategory f} (g : b' ⟶ b)
    (θ : (derivedOverMap.{0} X b.a).obj (E' b.i) ⟶ (derivedOverMap.{0} X b.a).obj (E b.i))
    (θ' : (derivedOverMap.{0} X b'.a).obj (E' b'.i) ⟶ (derivedOverMap.{0} X b'.a).obj (E b'.i)) :
    (derivedOverMap.{0} (X.over X₀) g.hom).map ((X.derivedIteratedSliceTransport X₀ b.V).map θ) ≫
        (indexRho f E ρ g).hom =
      (indexRho f E' ρ' g).hom ≫ (X.derivedIteratedSliceTransport X₀ b'.V).map θ' ↔
    (derivedOverMap.{0} X g.hom.left).map θ ≫ (indexRhoBase f E ρ g).hom =
      (indexRhoBase f E' ρ' g).hom ≫ θ' := by
  have n := (X.derivedIteratedSliceTransportOverMapIso X₀ g.hom).hom.naturality θ
  simp only [Functor.comp_map] at n
  simp only [indexRho, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [reassoc_of% n, Category.assoc, cancel_epi, ← Functor.map_comp, ← Functor.map_comp]
  exact (X.derivedIteratedSliceTransport X₀ b'.V).map_injective.eq_iff

/-- **A morphism of glueing data is compatible with the isomorphisms `ρ_g` of Situation 0DC9.** -/
theorem indexRho_naturality (β : ∀ i, E' i ⟶ E i)
    (hβ : ∀ i j, (derivedOverMap.{0} X (pullback.fst (f i) (f j))).map (β i) ≫ (ρ i j).hom =
      (ρ' i j).hom ≫ (derivedOverMap.{0} X (pullback.snd (f i) (f j))).map (β j))
    {b b' : IndexCategory f} (g : b' ⟶ b) :
    (derivedOverMap.{0} (X.over X₀) g.hom).map ((X.derivedIteratedSliceTransport X₀ b.V).map
        ((derivedOverMap.{0} X b.a).map (β b.i))) ≫ (indexRho f E ρ g).hom =
      (indexRho f E' ρ' g).hom ≫ (X.derivedIteratedSliceTransport X₀ b'.V).map
        ((derivedOverMap.{0} X b'.a).map (β b'.i)) :=
  (indexRho_comm_iff f ρ ρ' g _ _).2 (indexRhoBase_naturality f ρ ρ' β hβ g)

/-- **Compatibility of a restriction with the isomorphisms attached to the overlaps is
inherited by its restrictions.** -/
theorem restrictAlong_overlapIso {i j : ι} {V V' W : X.C} (a : V ⟶ U i) (a' : V' ⟶ U j)
    (g : V' ⟶ V) (hga : (g ≫ a) ≫ f i = a' ≫ f j)
    (θ : (derivedOverMap.{0} X a).obj (E' i) ⟶ (derivedOverMap.{0} X a).obj (E i))
    (θ' : (derivedOverMap.{0} X a').obj (E' j) ⟶ (derivedOverMap.{0} X a').obj (E j))
    (h : restrictAlong a g rfl θ ≫ (overlapIso f ρ (g ≫ a) a' hga).hom =
      (overlapIso f ρ' (g ≫ a) a' hga).hom ≫ θ')
    (w : W ⟶ V') {y : W ⟶ U i} (hy : (w ≫ g) ≫ a = y) {x : W ⟶ U j} (hx : w ≫ a' = x)
    (hyx : y ≫ f i = x ≫ f j) :
    restrictAlong a (w ≫ g) hy θ ≫ (overlapIso f ρ y x hyx).hom =
      (overlapIso f ρ' y x hyx).hom ≫ restrictAlong a' w hx θ' := by
  have hy' : w ≫ g ≫ a = y := by rw [← Category.assoc, hy]
  rw [restrictAlong_comp_left a g rfl w hy' hy, overlapIso_restrict f ρ (g ≫ a) a' hga w hy' hx,
    overlapIso_restrict f ρ' (g ≫ a) a' hga w hy' hx]
  simp only [restrictAlong, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  · simp only [restrictAlong] at h
    rw [← Category.assoc ((derivedOverMapComp.{0} X (rfl : g ≫ a = g ≫ a)).hom.app (E' i)), ← h]
    simp only [Functor.map_comp, Category.assoc]

/-- `AlgebraicGeometry.RingedSite.CoveringGlueing.indexRho_comm_iff` for morphisms of the
transported objects, through their preimages under the transport. -/
theorem indexRho_comm_iff_preimage {b b' : IndexCategory f} (g : b' ⟶ b)
    (θ : (X.derivedIteratedSliceTransport X₀ b.V).obj ((derivedOverMap.{0} X b.a).obj (E' b.i)) ⟶
      (X.derivedIteratedSliceTransport X₀ b.V).obj ((derivedOverMap.{0} X b.a).obj (E b.i)))
    (θ' : (X.derivedIteratedSliceTransport X₀ b'.V).obj
        ((derivedOverMap.{0} X b'.a).obj (E' b'.i)) ⟶
      (X.derivedIteratedSliceTransport X₀ b'.V).obj ((derivedOverMap.{0} X b'.a).obj (E b'.i))) :
    (derivedOverMap.{0} (X.over X₀) g.hom).map θ ≫ (indexRho f E ρ g).hom =
      (indexRho f E' ρ' g).hom ≫ θ' ↔
    (derivedOverMap.{0} X g.hom.left).map ((X.derivedIteratedSliceTransport X₀ b.V).preimage θ) ≫
        (indexRhoBase f E ρ g).hom =
      (indexRhoBase f E' ρ' g).hom ≫ (X.derivedIteratedSliceTransport X₀ b'.V).preimage θ' := by
  rw [← indexRho_comm_iff f ρ ρ' g, Functor.map_preimage, Functor.map_preimage]

end AlgebraicGeometry.RingedSite.CoveringGlueing

end
