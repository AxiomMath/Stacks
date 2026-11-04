module

public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.Overlap
public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.SliceTransport

/-!
# The locally given objects attached to a covering

Let `(C, O_C)` be a ringed site with fibre products, `f_i : U_i ⟶ X` a family of arrows of `C`,
`E_i` objects of `D(O_{U_i})` and `ρ_{ij} : E_i|_{U_{ij}} ⟶ E_j|_{U_{ij}}` isomorphisms satisfying
the cocycle condition. Following the first proof of Stacks 0GMG, this file produces the data of
Situation 0DC9 on the localized ringed site `C/X`: the category `B` of objects `V` of `C/X`
equipped with an index `i` and an arrow `a : V ⟶ U_i` over `X`, the functor `B ⥤ C/X` forgetting
`i` and `a`, the objects `E_{(V, i, a)} = a^*E_i`, and for an arrow `g : V' ⟶ V` of `B` the
isomorphism `ρ_g : g^*a^*E_i ⟶ a'^*E_{i'}` obtained by restricting `ρ_{i i'}` along
`(a ∘ g, a') : V' ⟶ U_i ×_X U_{i'}`. The cocycle condition of Situation 0DC9 for the `ρ_g` holds
because the cocycle condition for the `ρ_{ij}` holds at every object over `X`
(`AlgebraicGeometry.RingedSite.CoveringGlueing.overlapIso_trans`).

## Main definitions

* `AlgebraicGeometry.RingedSite.CoveringGlueing.Index`: the objects of `B`.
* `AlgebraicGeometry.RingedSite.CoveringGlueing.locallyGiven`: the data of Situation 0DC9.

## Implementation notes

The objects `E_{(V, i, a)}` live on the slice of `C/X` over `V ⟶ X`; they are the transports
(`AlgebraicGeometry.RingedSite.derivedIteratedSliceTransport`) of the restrictions `a^*E_i`, which
live on the slice `C/V` of `C`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSite.CoveringGlueing

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSite.{u, u, u}} [HasPullbacks X.C] {X₀ : X.C} {ι : Type u} {U : ι → X.C}
  (f : ∀ i, U i ⟶ X₀)

/-- An object of the indexing category: an object `V` of `C/X` together with an index `i` and an
arrow `a : V ⟶ U_i` over `X`. -/
structure Index where
  /-- The object of `C/X`. -/
  V : Over X₀
  /-- The index of the member of the family. -/
  i : ι
  /-- The arrow to the member of the family. -/
  a : V.left ⟶ U i
  /-- The arrow lies over `X`. -/
  w : a ≫ f i = V.hom

/-- The indexing category: objects are `AlgebraicGeometry.RingedSite.CoveringGlueing.Index`,
arrows are the arrows of `C/X` between the underlying objects. -/
abbrev IndexCategory : Type u := InducedCategory (Over X₀) (Index.V (f := f))

variable {f}

/-- For an arrow `g : V' ⟶ V` of the indexing category, the arrows `a ∘ g : V' ⟶ U_i` and
`a' : V' ⟶ U_{i'}` have equal composites to `X`. -/
theorem Index.comp_w {b b' : IndexCategory f} (g : b' ⟶ b) :
    (g.hom.left ≫ b.a) ≫ f b.i = b'.a ≫ f b'.i := by
  rw [Category.assoc, b.w, Over.w g.hom, b'.w]

/-- For composable arrows `k : V'' ⟶ V'` and `g : V' ⟶ V` of the indexing category, the arrows
`a ∘ g ∘ k : V'' ⟶ U_i` and `a' ∘ k : V'' ⟶ U_{i'}` have equal composites to `X`. -/
theorem Index.comp_comp_w {b b' b'' : IndexCategory f} (g : b' ⟶ b) (k : b'' ⟶ b') :
    ((k ≫ g).hom.left ≫ b.a) ≫ f b.i = (k.hom.left ≫ b'.a) ≫ f b'.i := by
  rw [Category.assoc, b.w, Over.w (k ≫ g).hom, Category.assoc, b'.w, Over.w k.hom]

variable (f) (E : ∀ i, LocalDerivedCategory.{0} X (U i))
  (ρ : ∀ i j, (derivedOverMap.{0} X (pullback.fst (f i) (f j))).obj (E i) ≅
    (derivedOverMap.{0} X (pullback.snd (f i) (f j))).obj (E j))

/-- The locally given object at `(V, i, a)`: the restriction `a^*E_i`, transported to the slice
of `C/X` over `V`. -/
abbrev indexObj (b : IndexCategory f) : LocalDerivedCategory.{0} (X.over X₀) b.V :=
  (X.derivedIteratedSliceTransport X₀ b.V).obj ((derivedOverMap.{0} X b.a).obj (E b.i))

/-- The isomorphism `g^*a^*E_i ⟶ a'^*E_{i'}` on the slice `C/V'`, for an arrow `g : V' ⟶ V` of the
indexing category. -/
def indexRhoBase {b b' : IndexCategory f} (g : b' ⟶ b) :
    (derivedOverMap.{0} X g.hom.left).obj ((derivedOverMap.{0} X b.a).obj (E b.i)) ≅
      (derivedOverMap.{0} X b'.a).obj (E b'.i) :=
  ((derivedOverMapComp.{0} X (rfl : g.hom.left ≫ b.a = g.hom.left ≫ b.a)).app (E b.i)).symm ≪≫
    overlapIso f ρ (g.hom.left ≫ b.a) b'.a (Index.comp_w g)

/-- The isomorphism `ρ_g` of Situation 0DC9 for an arrow `g : V' ⟶ V` of the indexing category. -/
def indexRho {b b' : IndexCategory f} (g : b' ⟶ b) :
    (derivedOverMap.{0} (X.over X₀) g.hom).obj (indexObj f E b) ≅ indexObj f E b' :=
  (X.derivedIteratedSliceTransportOverMapIso X₀ g.hom).app
      ((derivedOverMap.{0} X b.a).obj (E b.i)) ≪≫
    (X.derivedIteratedSliceTransport X₀ b'.V).mapIso (indexRhoBase f E ρ g)

/-- The cocycle condition for the isomorphisms `indexRhoBase`, on slices of `C`. -/
theorem indexRhoBase_comp (hρ : IsCocycle f ρ) {b b' b'' : IndexCategory f} (g : b' ⟶ b)
    (k : b'' ⟶ b') :
    (indexRhoBase f E ρ (k ≫ g)).hom =
      (derivedOverMapComp.{0} X (Over.comp_left _ _ _ k.hom g.hom).symm).hom.app
          ((derivedOverMap.{0} X b.a).obj (E b.i)) ≫
        (derivedOverMap.{0} X k.hom.left).map (indexRhoBase f E ρ g).hom ≫
          (indexRhoBase f E ρ k).hom := by
  have ha : k.hom.left ≫ g.hom.left ≫ b.a = (k ≫ g).hom.left ≫ b.a := by
    simp only [InducedCategory.comp_hom, Over.comp_left, Category.assoc]
  have res := overlapIso_restrict f ρ (g.hom.left ≫ b.a) b'.a (Index.comp_w g) k.hom.left ha
    (rfl : k.hom.left ≫ b'.a = k.hom.left ≫ b'.a)
    (Index.comp_comp_w g k)
  have tr := overlapIso_trans f ρ hρ ((k ≫ g).hom.left ≫ b.a) (k.hom.left ≫ b'.a) b''.a
    (Index.comp_comp_w g k) (Index.comp_w k) (Index.comp_w (k ≫ g))
  have ass := X.derivedOverMapComp_assoc b.a g.hom.left k.hom.left
    (rfl : g.hom.left ≫ b.a = g.hom.left ≫ b.a) (Over.comp_left _ _ _ k.hom g.hom).symm ha
    (rfl : (k ≫ g).hom.left ≫ b.a = (k ≫ g).hom.left ≫ b.a) (E b.i)
  have res' : (derivedOverMap.{0} X k.hom.left).map
        (overlapIso f ρ (g.hom.left ≫ b.a) b'.a (Index.comp_w g)).hom ≫
        (derivedOverMapComp.{0} X (rfl : k.hom.left ≫ b'.a = k.hom.left ≫ b'.a)).inv.app
          (E b'.i) =
      (derivedOverMapComp.{0} X ha).inv.app (E b.i) ≫
        (overlapIso f ρ ((k ≫ g).hom.left ≫ b.a) (k.hom.left ≫ b'.a)
          (Index.comp_comp_w g k)).hom := by
    rw [res]
    simp only [Iso.inv_hom_id_app_assoc]
  have ass' : (derivedOverMapComp.{0} X (Over.comp_left _ _ _ k.hom g.hom).symm).hom.app
          ((derivedOverMap.{0} X b.a).obj (E b.i)) ≫
        (derivedOverMap.{0} X k.hom.left).map
          ((derivedOverMapComp.{0} X (rfl : g.hom.left ≫ b.a = g.hom.left ≫ b.a)).inv.app
            (E b.i)) ≫
        (derivedOverMapComp.{0} X ha).inv.app (E b.i) =
      (derivedOverMapComp.{0} X
        (rfl : (k ≫ g).hom.left ≫ b.a = (k ≫ g).hom.left ≫ b.a)).inv.app (E b.i) := by
    rw [← cancel_epi ((derivedOverMapComp.{0} X
      (rfl : (k ≫ g).hom.left ≫ b.a = (k ≫ g).hom.left ≫ b.a)).hom.app (E b.i)),
      Iso.hom_inv_id_app, ← reassoc_of% ass]
    simp [← Functor.map_comp_assoc]
  simp only [indexRhoBase, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.map_comp,
    Category.assoc]
  rw [reassoc_of% res', tr, reassoc_of% ass']

/-- **The data of Situation 0DC9 attached to a covering**, on the localized ringed site `C/X`:
the indexing category of objects of `C/X` with an arrow to a member of the family, the objects
`a^*E_i` and the isomorphisms obtained by restricting the `ρ_{ij}`. -/
def locallyGiven (hρ : IsCocycle f ρ) : LocallyGiven.{0, u, u, u, u, u} (X.over X₀) where
  B := IndexCategory f
  u := inducedFunctor _
  obj b := indexObj f E b
  rho g := indexRho f E ρ g
  cocycle {b'' b' b} k g := by
    have coh := X.derivedIteratedSliceTransportOverMapIso_comp X₀ g.hom k.hom
      ((derivedOverMap.{0} X b.a).obj (E b.i))
    have nat := (X.derivedIteratedSliceTransportOverMapIso X₀ k.hom).hom.naturality
      (indexRhoBase f E ρ g).hom
    simp only [Functor.comp_map] at nat
    change (indexRho f E ρ (k ≫ g)).hom =
      (derivedOverMapComp.{0} (X.over X₀) (rfl : k.hom ≫ g.hom = k.hom ≫ g.hom)).hom.app
          (indexObj f E b) ≫
        (derivedOverMap.{0} (X.over X₀) k.hom).map (indexRho f E ρ g).hom ≫
          (indexRho f E ρ k).hom
    simp only [indexRho, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
      Category.assoc]
    rw [reassoc_of% nat, reassoc_of% coh, indexRhoBase_comp f E ρ hρ g k]
    simp only [Functor.map_comp, Category.assoc]
    rfl

end AlgebraicGeometry.RingedSite.CoveringGlueing

end
