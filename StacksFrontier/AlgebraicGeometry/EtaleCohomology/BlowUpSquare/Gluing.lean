module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BlowUpSquare.Triangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedBelowDerivedDirectImage

/-!
# Gluing objects of the derived category along a square that is an isomorphism off a closed set

Consider a cartesian square of schemes

```
E --j--> X'
|π       |b
v        v
Z --i--> X
```

with `i` and `j` closed immersions, `c = π ≫ i = j ≫ b`, `b` an isomorphism over the open
complement `U` of `Z` (with inverse image `U'`, the complement of `E`), and such that cohomology
commutes with base change for `b`. Given bounded below objects `K'` of `D(X'_étale)` with torsion
cohomology sheaves and `L` of `D(Z_étale)`, together with an isomorphism `γ : K'|_E ≅ L|_E`,
there is a bounded below `K` in `D(X_étale)` with isomorphisms `f : K|_{X'} ≅ K'` and
`g : K|_Z ≅ L` such that `γ = g|_E ∘ f⁻¹|_E`; and morphisms out of `K` are glued from compatible
morphisms out of `K'` and `L`. For the blowup square of a quasi-coherent ideal of finite type
this is Stacks Tag 0EW6.

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianDerivedCompDirectImageMap`: for `c = π ≫ i` and
  `w : π⁻¹ L ⟶ N`, the induced `Ri_* L ⟶ Rc_* N`.

## Main results

* `Stacks.EtaleCohomology.homEquiv_comp_etaleAbelianDerivedCompDirectImageMap`: maps into
  `Ri_* L` followed by this map are adjoint, along `c`, to the evident maps out of `c⁻¹`.
* `Stacks.EtaleCohomology.isIso_map_etaleAbelianDerivedAdjunction_counit_of_isPullback_of_isIso`:
  over an open on which `b` is an isomorphism, the counit of `b` is invertible.
* `Stacks.EtaleCohomology.exists_gluing_of_isPullback_of_cohomologyCommutesWithBaseChange`: the
  gluing statement above.

## Implementation notes

Following the source, `K` is the fibre of the map `Ri_* L ⊕ Rb_* K' ⟶ Rc_*(L|_E)` whose
components are `Ri_*` of the unit of `π` and the composite of `Rb_*` of the unit of `j` with
`Rc_* γ`, and `g`, `f` are the adjoints of the two components of `K ⟶ Ri_* L ⊕ Rb_* K'`.

* `g` is invertible: after `i⁻¹` the second component becomes the base change map
  `i⁻¹ Rb_* K' ⟶ Rπ_* j⁻¹ K'` (Stacks 0DDE) followed by `Rπ_* γ`, hence invertible, so the fibre
  is `i⁻¹ Ri_* L ≅ L`.
* `f` is invertible: the restrictions to `E` and to `U'` jointly reflect isomorphisms. On `E`
  the identity `γ ∘ f|_E = g|_E` holds by construction, both `γ` and `g` being invertible. On
  `U'` both direct images from `Z` and from `E` vanish, and the counit of `b` is invertible
  there.

The "moreover" clause of the source asks for a morphism `M ⟶ K`; the morphism produced by its
proof, and the only one whose restrictions can be `α ∘ f` and `β ∘ g` (which have source
`K|_{X'}` and `K|_Z`), goes `K ⟶ M`. It is formalized in that corrected direction: the morphism
of triangles from the triangle defining `K` to the Mayer–Vietoris triangle of `M`
(`Stacks.EtaleCohomology.exists_distTriang_of_isPullback_of_cohomologyCommutesWithBaseChange`,
Stacks 0EW5).

## References

* [Stacks Project, Tag 0EW6](https://stacks.math.columbia.edu/tag/0EW6)
* [Stacks Project, Tag 0EW5](https://stacks.math.columbia.edu/tag/0EW5)
* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

/-! ### The map `Ri_* L ⟶ Rc_* N` induced by `π⁻¹ L ⟶ N` -/

section CompDirectImageMap

variable {E Z X : Scheme.{u}} (π : E ⟶ Z) (i : Z ⟶ X) (c : E ⟶ X) (hc : c = π ≫ i)

/-- For a factorization `c = π ≫ i`, a morphism `w : π⁻¹ L ⟶ N` induces `Ri_* L ⟶ Rc_* N`: `Ri_*`
of the adjoint `L ⟶ Rπ_* N` of `w`, read through `Ri_* Rπ_* ≅ Rc_*`. -/
public def etaleAbelianDerivedCompDirectImageMap
    {L : DerivedCategory (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    {N : DerivedCategory (Sheaf E.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (w : (etaleAbelianDerivedInverseImage.{u, v} π).obj L ⟶ N) :
    (etaleAbelianDerivedDirectImage.{u, v} i).obj L ⟶
      (etaleAbelianDerivedDirectImage.{u, v} c).obj N :=
  (etaleAbelianDerivedDirectImage.{u, v} i).map
      ((etaleAbelianDerivedAdjunction.{u, v} π).homEquiv L N w) ≫
    (etaleAbelianDerivedDirectImageCompIso'.{u, v} π i c hc).inv.app N

variable {L L' : DerivedCategory (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
  {N N' : DerivedCategory (Sheaf E.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}

/-- The induced map is natural in its target. -/
public theorem etaleAbelianDerivedCompDirectImageMap_comp
    (w : (etaleAbelianDerivedInverseImage.{u, v} π).obj L ⟶ N) (w' : N ⟶ N') :
    etaleAbelianDerivedCompDirectImageMap.{u, v} π i c hc (w ≫ w') =
      etaleAbelianDerivedCompDirectImageMap.{u, v} π i c hc w ≫
        (etaleAbelianDerivedDirectImage.{u, v} c).map w' := by
  simp only [etaleAbelianDerivedCompDirectImageMap, Adjunction.homEquiv_naturality_right,
    Functor.map_comp, Category.assoc]
  rw [← (etaleAbelianDerivedDirectImageCompIso'.{u, v} π i c hc).inv.naturality w']
  rfl

/-- The induced map is natural in its source. -/
public theorem map_comp_etaleAbelianDerivedCompDirectImageMap (β : L' ⟶ L)
    (w : (etaleAbelianDerivedInverseImage.{u, v} π).obj L ⟶ N) :
    (etaleAbelianDerivedDirectImage.{u, v} i).map β ≫
        etaleAbelianDerivedCompDirectImageMap.{u, v} π i c hc w =
      etaleAbelianDerivedCompDirectImageMap.{u, v} π i c hc
        ((etaleAbelianDerivedInverseImage.{u, v} π).map β ≫ w) := by
  simp only [etaleAbelianDerivedCompDirectImageMap, Adjunction.homEquiv_naturality_left,
    Functor.map_comp, Category.assoc]

/-- The comparison `Ri_* i⁻¹ K ⟶ Rc_* c⁻¹ K` of
`Stacks.EtaleCohomology.etaleAbelianDerivedUnitCompMap` is the map induced by the identification
`π⁻¹ i⁻¹ K ≅ c⁻¹ K`. -/
public theorem etaleAbelianDerivedUnitCompMap_app_eq_compDirectImageMap
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    (etaleAbelianDerivedUnitCompMap.{u, v} π i c hc).app K =
      etaleAbelianDerivedCompDirectImageMap.{u, v} π i c hc
        ((etaleAbelianDerivedInverseImageCompIso'.{u, v} π i c hc).inv.app K) := by
  simp only [etaleAbelianDerivedUnitCompMap_app, etaleAbelianDerivedCompDirectImageMap,
    Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]

/-- **Maps into `Ri_* L` followed by the induced map are adjoint along `c`.** For
`t : i⁻¹ K ⟶ L`, the adjoint `K ⟶ Ri_* L` of `t` followed by the map induced by
`w : π⁻¹ L ⟶ N` is the adjoint, along `c⁻¹ ⊣ Rc_*`, of `c⁻¹ K ≅ π⁻¹ i⁻¹ K ⟶ π⁻¹ L ⟶ N`. -/
public theorem homEquiv_comp_etaleAbelianDerivedCompDirectImageMap
    {K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (t : (etaleAbelianDerivedInverseImage.{u, v} i).obj K ⟶ L)
    (w : (etaleAbelianDerivedInverseImage.{u, v} π).obj L ⟶ N) :
    (etaleAbelianDerivedAdjunction.{u, v} i).homEquiv K L t ≫
        etaleAbelianDerivedCompDirectImageMap.{u, v} π i c hc w =
      (etaleAbelianDerivedAdjunction.{u, v} c).homEquiv K N
        ((etaleAbelianDerivedInverseImageCompIso'.{u, v} π i c hc).hom.app K ≫
          (etaleAbelianDerivedInverseImage.{u, v} π).map t ≫ w) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    ← etaleAbelianDerivedAdjunction_unit_app_comp_unitCompMap.{u, v} π i c hc K,
    etaleAbelianDerivedUnitCompMap_app_eq_compDirectImageMap]
  simp only [Category.assoc]
  rw [← etaleAbelianDerivedCompDirectImageMap_comp, Iso.inv_hom_id_app_assoc,
    ← map_comp_etaleAbelianDerivedCompDirectImageMap]

end CompDirectImageMap

/-! ### The open part: the counit -/

section OpenPart

/-- If `bU` is an isomorphism, the comparison `etaleAbelianDerivedSquare` of the square
`o' ≫ b = bU ≫ o` is invertible. -/
private theorem isIso_natTrans_etaleAbelianDerivedSquare {X X' U U' : Scheme.{u}} (b : X' ⟶ X)
    (o : U ⟶ X) (o' : U' ⟶ X') (bU : U' ⟶ U) (sq : IsPullback o' bU b o) [IsIso bU] :
    IsIso (etaleAbelianDerivedSquare.{u, v} b o o' bU (o' ≫ b) rfl sq.w).natTrans := by
  dsimp only [etaleAbelianDerivedSquare]
  infer_instance

/-- **Over an open subscheme on which `b` is an isomorphism, the counit of `b` is invertible.**
For a cartesian square `o' ≫ b = bU ≫ o` with `o` an open immersion and `bU` an isomorphism,
`o'⁻¹` of the counit `b⁻¹ Rb_* K' ⟶ K'` is invertible: by open base change it is identified with
the counit of `bU⁻¹ ⊣ RbU_*`, and inverse image along an isomorphism is an equivalence. -/
public theorem isIso_map_etaleAbelianDerivedAdjunction_counit_of_isPullback_of_isIso
    {X X' U U' : Scheme.{u}} (b : X' ⟶ X) (o : U ⟶ X) [IsOpenImmersion o] (o' : U' ⟶ X')
    (bU : U' ⟶ U) (sq : IsPullback o' bU b o) [IsIso bU]
    (K' : DerivedCategory (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    IsIso ((etaleAbelianDerivedInverseImage.{u, v} o').map
      ((etaleAbelianDerivedAdjunction.{u, v} b).counit.app K')) := by
  let α := etaleAbelianDerivedSquare.{u, v} b o o' bU (o' ≫ b) rfl sq.w
  have hα : IsIso α.natTrans := isIso_natTrans_etaleAbelianDerivedSquare.{u, v} b o o' bU sq
  have hβ : IsIso (etaleAbelianDerivedBaseChange.{u, v} b o o' bU sq.w) :=
    isIso_etaleAbelianDerivedBaseChange_of_isOpenImmersion.{u, v} b o o' bU sq
  rw [etaleAbelianDerivedBaseChange_eq_mateEquiv.{u, v} b o o' bU (o' ≫ b) rfl sq.w] at hβ
  have hdense := isDenseSubsite_smallEtaleBaseChange_of_isIso bU
  have : (etaleAbelianDirectImage.{u, v} bU).IsEquivalence :=
    inferInstanceAs ((smallEtaleBaseChange bU).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (smallEtaleTopology U) (smallEtaleTopology U')).IsEquivalence
  have : (etaleAbelianInverseImage.{u, v} bU).IsEquivalence :=
    Functor.isEquivalence_of_iso (Adjunction.leftAdjointUniq
      (etaleAbelianInverseImageDirectImageAdj.{u, v} bU)
      (etaleAbelianDirectImage.{u, v} bU).asEquivalence.symm.toAdjunction).symm
  have : (etaleAbelianDerivedInverseImage.{u, v} bU).IsEquivalence :=
    Stacks.DerivedFunctor.isEquivalence_mapDerivedCategory _
  have h := mateEquiv_counit (etaleAbelianDerivedAdjunction.{u, v} b)
    (etaleAbelianDerivedAdjunction.{u, v} bU) α K'
  have : IsIso ((etaleAbelianDerivedAdjunction.{u, v} bU).counit.app
      ((etaleAbelianDerivedInverseImage.{u, v} o').obj K')) := inferInstance
  have : IsIso ((mateEquiv (etaleAbelianDerivedAdjunction.{u, v} b)
      (etaleAbelianDerivedAdjunction.{u, v} bU) α).natTrans.app K') := inferInstance
  have : IsIso (α.natTrans.app ((etaleAbelianDerivedDirectImage.{u, v} b).obj K')) :=
    inferInstance
  dsimp only [Functor.id_obj, Functor.comp_obj] at h
  have : IsIso (α.natTrans.app ((etaleAbelianDerivedDirectImage.{u, v} b).obj K') ≫
      (etaleAbelianDerivedInverseImage.{u, v} o').map
        ((etaleAbelianDerivedAdjunction.{u, v} b).counit.app K')) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_left (α.natTrans.app _) _

end OpenPart

/-! ### The gluing -/

section Gluing

variable {X Z X' E : Scheme.{u}} (i : Z ⟶ X) (b : X' ⟶ X) (j : E ⟶ X') (π : E ⟶ Z)
  (c : E ⟶ X) (hcπ : c = π ≫ i) (hcj : c = j ≫ b)

/-- If `κ ≫ G.map a = φ ≫ unit`, then `F.map φ` is the adjoint of `κ` followed by `a`. -/
private theorem map_eq_homEquiv_symm_comp_of_comp_unit {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {K M : C} {A : D} (φ : K ⟶ M) (κ : K ⟶ G.obj A)
    (a : A ⟶ F.obj M) (h : κ ≫ G.map a = φ ≫ adj.unit.app M) :
    F.map φ = (adj.homEquiv K A).symm κ ≫ a := by
  rw [Adjunction.homEquiv_counit, Category.assoc, ← adj.counit_naturality, ← Category.assoc,
    ← F.map_comp, h, F.map_comp, Category.assoc, adj.left_triangle_components, Category.comp_id]

include hcπ in
/-- **Over the closed subscheme, the comparison `Rb_* K' ⟶ Rc_* N` along `c = j ≫ b` induced by an
isomorphism becomes invertible.** For a cartesian square for which cohomology commutes with base
change for `b`, a bounded below `K'` with torsion cohomology sheaves, and an isomorphism
`w : j⁻¹ K' ⟶ N`, the map `i⁻¹ Rb_* K' ⟶ i⁻¹ Rc_* N` is the base change map
`i⁻¹ Rb_* K' ⟶ Rπ_* j⁻¹ K'` (Stacks 0DDE) followed by isomorphisms. -/
public theorem isIso_map_etaleAbelianDerivedCompDirectImageMap_of_cohomologyCommutesWithBaseChange
    [IsClosedImmersion i] (sq : IsPullback j π b i)
    (hb : CohomologyCommutesWithBaseChange.{u, v} b)
    (K' : DerivedCategory (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) (n : ℤ)
    (hK' : K'.IsGE n)
    (hT : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) v} X'.smallEtaleTopology K')
    {N : DerivedCategory (Sheaf E.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (w : (etaleAbelianDerivedInverseImage.{u, v} j).obj K' ⟶ N) [IsIso w] :
    IsIso ((etaleAbelianDerivedInverseImage.{u, v} i).map
      (etaleAbelianDerivedCompDirectImageMap.{u, v} j b c hcj w)) := by
  have hβ : IsIso ((etaleAbelianDerivedBaseChange.{u, v} b i j π sq.w).app K') :=
    isIso_etaleAbelianDerivedBaseChange_of_cohomologyCommutesWithBaseChange.{u, v} hb sq K' n hK'
      hT
  have key := etaleAbelianDerivedAdjunction_unit_app_comp_map_etaleAbelianDerivedBaseChange.{u, v}
    b i j π sq.w c hcj hcπ K'
  have hw : etaleAbelianDerivedCompDirectImageMap.{u, v} j b c hcj w =
      (etaleAbelianDerivedAdjunction.{u, v} i).unit.app
          ((etaleAbelianDerivedDirectImage.{u, v} b).obj K') ≫
        (etaleAbelianDerivedDirectImage.{u, v} i).map
          ((etaleAbelianDerivedBaseChange.{u, v} b i j π sq.w).app K') ≫
        (etaleAbelianDerivedDirectImageCompIso'.{u, v} π i c hcπ).inv.app
          ((etaleAbelianDerivedInverseImage.{u, v} j).obj K') ≫
        (etaleAbelianDerivedDirectImage.{u, v} c).map w := by
    rw [← Category.id_comp w, etaleAbelianDerivedCompDirectImageMap_comp, Category.id_comp,
      reassoc_of% key]
    simp [etaleAbelianDerivedCompDirectImageMap, Adjunction.homEquiv_unit]
  rw [hw]
  simp only [Functor.map_comp]
  infer_instance

/-- **Stacks 0EW6 for a square that is an isomorphism off a closed subscheme, granted that
cohomology commutes with base change for `b`.** Let
```
E --j--> X'
|π       |b
v        v
Z --i--> X
```
be a cartesian square with `i`, `j` closed immersions and common composite `c`, let `o : U ⟶ X`
and `o' : U' ⟶ X'` be open immersions onto the complements of `Z` and of `E`, with `b` an
isomorphism over `U` (the base change `bU` is invertible), and suppose cohomology commutes with
base change for `b`. Let `K'` in `D(X'_étale)` be bounded below with torsion cohomology sheaves,
`L` in `D(Z_étale)` bounded below, and `γ : K'|_E ≅ L|_E`. Then there is a bounded below `K` in
`D(X_étale)` with isomorphisms `f : K|_{X'} ≅ K'` and `g : K|_Z ≅ L` such that
`γ = g|_E ∘ f⁻¹|_E` (read through `K|_{X'}|_E ≅ K|_E ≅ K|_Z|_E`). Moreover, for every bounded
below `M` with torsion cohomology sheaves and `α : K' ⟶ M|_{X'}`, `β : L ⟶ M|_Z` with
`α|_E = β|_E ∘ γ`, there is a morphism `K ⟶ M` whose restrictions to `X'` and `Z` are `α ∘ f`
and `β ∘ g`.

The source states the last morphism as `M ⟶ K`; its restrictions are required to be `α ∘ f` and
`β ∘ g`, which are morphisms out of `K|_{X'}` and `K|_Z`, and the morphism of triangles of the
source's proof goes from the triangle of `K` to that of `M`. The direction is corrected here to
`K ⟶ M`. The source's hypothesis that `L` has torsion cohomology sheaves is not needed. -/
public theorem exists_gluing_of_isPullback_of_cohomologyCommutesWithBaseChange
    [IsClosedImmersion i] [IsClosedImmersion j] {U U' : Scheme.{u}} (o : U ⟶ X)
    [IsOpenImmersion o] (hio : Set.range o.base = (Set.range i.base)ᶜ) (sq : IsPullback j π b i)
    (o' : U' ⟶ X') [IsOpenImmersion o'] (hjo : Set.range o'.base = (Set.range j.base)ᶜ)
    (bU : U' ⟶ U) (sqU : IsPullback o' bU b o) [IsIso bU]
    (hb : CohomologyCommutesWithBaseChange.{u, v} b)
    (K' : DerivedCategory (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}))
    (L : DerivedCategory (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) (n : ℤ)
    (hK' : K'.IsGE n) (hL : L.IsGE n)
    (hK'T : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) v} X'.smallEtaleTopology K')
    (γ : (etaleAbelianDerivedInverseImage.{u, v} j).obj K' ≅
      (etaleAbelianDerivedInverseImage.{u, v} π).obj L) :
    ∃ (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}))
      (_ : K.IsGE n) (f : (etaleAbelianDerivedInverseImage.{u, v} b).obj K ≅ K')
      (g : (etaleAbelianDerivedInverseImage.{u, v} i).obj K ≅ L),
      γ.hom = (etaleAbelianDerivedInverseImage.{u, v} j).map f.inv ≫
          (etaleAbelianDerivedInverseImageCompIso'.{u, v} j b c hcj).inv.app K ≫
          (etaleAbelianDerivedInverseImageCompIso'.{u, v} π i c hcπ).hom.app K ≫
          (etaleAbelianDerivedInverseImage.{u, v} π).map g.hom ∧
      ∀ (M : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) (m : ℤ),
        M.IsGE m →
        Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) v} X.smallEtaleTopology M →
        ∀ (α : K' ⟶ (etaleAbelianDerivedInverseImage.{u, v} b).obj M)
          (β : L ⟶ (etaleAbelianDerivedInverseImage.{u, v} i).obj M),
          (etaleAbelianDerivedInverseImage.{u, v} j).map α ≫
              (etaleAbelianDerivedInverseImageCompIso'.{u, v} j b c hcj).inv.app M ≫
              (etaleAbelianDerivedInverseImageCompIso'.{u, v} π i c hcπ).hom.app M =
            γ.hom ≫ (etaleAbelianDerivedInverseImage.{u, v} π).map β →
          ∃ φ : K ⟶ M, (etaleAbelianDerivedInverseImage.{u, v} b).map φ = f.hom ≫ α ∧
            (etaleAbelianDerivedInverseImage.{u, v} i).map φ = g.hom ≫ β := by
  set ψ := biprod.desc
    (etaleAbelianDerivedCompDirectImageMap.{u, v} π i c hcπ
      (𝟙 ((etaleAbelianDerivedInverseImage.{u, v} π).obj L)))
    (-etaleAbelianDerivedCompDirectImageMap.{u, v} j b c hcj γ.hom) with hψ
  obtain ⟨K, κ, δ, hT⟩ := distinguished_cocone_triangle₁ ψ
  set g' := ((etaleAbelianDerivedAdjunction.{u, v} i).homEquiv K L).symm (κ ≫ biprod.fst)
    with hg'
  set f' := ((etaleAbelianDerivedAdjunction.{u, v} b).homEquiv K K').symm (κ ≫ biprod.snd)
    with hf'
  -- the two components of `κ` agree in `Rc_*(L|_E)`
  have h₁ : κ ≫ biprod.fst ≫
        etaleAbelianDerivedCompDirectImageMap.{u, v} π i c hcπ
          (𝟙 ((etaleAbelianDerivedInverseImage.{u, v} π).obj L)) =
      κ ≫ biprod.snd ≫ etaleAbelianDerivedCompDirectImageMap.{u, v} j b c hcj γ.hom := by
    have h := comp_distTriang_mor_zero₁₂ _ hT
    simp only [Triangle.mk_mor₁, Triangle.mk_mor₂, hψ, biprod.desc_eq, Preadditive.comp_add,
      Preadditive.comp_neg] at h
    exact add_neg_eq_zero.mp h
  -- `γ ∘ f|_E = g|_E`
  have hcompat : (etaleAbelianDerivedInverseImageCompIso'.{u, v} j b c hcj).hom.app K ≫
        (etaleAbelianDerivedInverseImage.{u, v} j).map f' ≫ γ.hom =
      (etaleAbelianDerivedInverseImageCompIso'.{u, v} π i c hcπ).hom.app K ≫
        (etaleAbelianDerivedInverseImage.{u, v} π).map g' := by
    apply ((etaleAbelianDerivedAdjunction.{u, v} c).homEquiv K _).injective
    have e₁ := homEquiv_comp_etaleAbelianDerivedCompDirectImageMap.{u, v} j b c hcj f' γ.hom
    have e₂ := homEquiv_comp_etaleAbelianDerivedCompDirectImageMap.{u, v} π i c hcπ g'
      (𝟙 ((etaleAbelianDerivedInverseImage.{u, v} π).obj L))
    rw [Category.comp_id] at e₂
    rw [← e₁, ← e₂, hf', hg', Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    simpa only [Category.assoc] using h₁.symm
  -- `g` is invertible
  have hg : IsIso g' := by
    have : IsIso ((etaleAbelianDerivedInverseImage.{u, v} i).map
        (-etaleAbelianDerivedCompDirectImageMap.{u, v} j b c hcj γ.hom)) := by
      rw [Functor.map_neg]
      have :=
        isIso_map_etaleAbelianDerivedCompDirectImageMap_of_cohomologyCommutesWithBaseChange.{u, v}
          i b j π c hcπ hcj sq hb K' n hK' hK'T γ.hom
      infer_instance
    have := isIso_map_mor₁_comp_biprod_fst_of_isIso (etaleAbelianDerivedInverseImage.{u, v} i)
      κ _ _ δ hT
    rw [hg', Adjunction.homEquiv_counit]
    infer_instance
  -- `f` is invertible
  have hf : IsIso f' := by
    refine isIso_of_isIso_etaleAbelianDerivedInverseImage_of_range_eq_compl j o' hjo f' ?_ ?_
    · have h₂ : IsIso ((etaleAbelianDerivedInverseImageCompIso'.{u, v} j b c hcj).hom.app K ≫
          (etaleAbelianDerivedInverseImage.{u, v} j).map f' ≫ γ.hom) := by
        rw [hcompat]
        infer_instance
      have h₃ : IsIso ((etaleAbelianDerivedInverseImage.{u, v} j).map f' ≫ γ.hom) :=
        IsIso.of_isIso_comp_left
          ((etaleAbelianDerivedInverseImageCompIso'.{u, v} j b c hcj).hom.app K) _
      exact IsIso.of_isIso_comp_right _ γ.hom
    · have hA : IsZero ((etaleAbelianDerivedInverseImage.{u, v} o).obj
          ((etaleAbelianDerivedDirectImage.{u, v} i).obj L)) :=
        isZero_etaleAbelianDerivedInverseImage_derivedDirectImage.{u, v} i o hio _
      have hC : IsZero ((etaleAbelianDerivedInverseImage.{u, v} o).obj
          ((etaleAbelianDerivedDirectImage.{u, v} c).obj
            ((etaleAbelianDerivedInverseImage.{u, v} π).obj L))) :=
        IsZero.of_iso (isZero_etaleAbelianDerivedInverseImage_derivedDirectImage.{u, v} i o hio _)
          ((etaleAbelianDerivedInverseImage.{u, v} o).mapIso
            ((etaleAbelianDerivedDirectImageCompIso'.{u, v} π i c hcπ).app _))
      have hsnd := isIso_map_mor₁_comp_biprod_snd_of_isZero
        (etaleAbelianDerivedInverseImage.{u, v} o) κ ψ δ hT hA hC
      let α := etaleAbelianDerivedSquare.{u, v} b o o' bU (o' ≫ b) rfl sqU.w
      have hα : IsIso α.natTrans := isIso_natTrans_etaleAbelianDerivedSquare.{u, v} b o o' bU sqU
      have hb' : IsIso ((etaleAbelianDerivedInverseImage.{u, v} o').map
          ((etaleAbelianDerivedInverseImage.{u, v} b).map (κ ≫ biprod.snd))) :=
        (NatIso.isIso_map_iff (asIso α.natTrans) (κ ≫ biprod.snd)).mp
          (by dsimp; infer_instance)
      have hε := isIso_map_etaleAbelianDerivedAdjunction_counit_of_isPullback_of_isIso.{u, v}
        b o o' bU sqU K'
      rw [hf', Adjunction.homEquiv_counit, Functor.map_comp]
      infer_instance
  -- `K` is bounded below
  have hK : K.IsGE n := by
    have hA := isGE_etaleAbelianDerivedDirectImage_obj.{u, v} i L n hL
    have hB := isGE_etaleAbelianDerivedDirectImage_obj.{u, v} b K' n hK'
    have hC := isGE_etaleAbelianDerivedDirectImage_obj.{u, v} c _ n
      (Functor.isGE_obj_mapDerivedCategory (etaleAbelianInverseImage.{u, v} π) L n hL)
    have hAB := DerivedCategory.TStructure.t.isGE₂ _
      (binaryBiproductTriangle_distinguished _ _) n hA hB
    have hC' : DerivedCategory.TStructure.t.IsGE
        (((etaleAbelianDerivedDirectImage.{u, v} c).obj
          ((etaleAbelianDerivedInverseImage.{u, v} π).obj L))⟦(-1 : ℤ)⟧) n :=
      have := DerivedCategory.TStructure.t.isGE_shift ((etaleAbelianDerivedDirectImage.{u, v} c).obj
        ((etaleAbelianDerivedInverseImage.{u, v} π).obj L)) n (-1) (n + 1)
      DerivedCategory.TStructure.t.isGE_of_ge _ n (n + 1)
    exact DerivedCategory.TStructure.t.isGE₂ _ (inv_rot_of_distTriang _ hT) n hC' hAB
  refine ⟨K, hK, asIso f', asIso g', ?_, ?_⟩
  · rw [asIso_hom, ← hcompat]
    simp
  · intro M m hM hMT α β hαβ
    obtain ⟨δM, hTM⟩ := exists_distTriang_of_isPullback_of_cohomologyCommutesWithBaseChange.{u, v}
      i b j π c hcπ hcj o hio sq o' bU sqU hb M m hM hMT
    have hαβ' : γ.hom ≫ (etaleAbelianDerivedInverseImage.{u, v} π).map β ≫
          (etaleAbelianDerivedInverseImageCompIso'.{u, v} π i c hcπ).inv.app M =
        (etaleAbelianDerivedInverseImage.{u, v} j).map α ≫
          (etaleAbelianDerivedInverseImageCompIso'.{u, v} j b c hcj).inv.app M := by
      rw [← reassoc_of% hαβ]
      simp
    obtain ⟨φ, hφ, -⟩ := complete_distinguished_triangle_morphism₁ _ _ hT hTM
      (biprod.map ((etaleAbelianDerivedDirectImage.{u, v} i).map β)
        ((etaleAbelianDerivedDirectImage.{u, v} b).map α))
      ((etaleAbelianDerivedDirectImage.{u, v} c).map
        ((etaleAbelianDerivedInverseImage.{u, v} π).map β ≫
          (etaleAbelianDerivedInverseImageCompIso'.{u, v} π i c hcπ).inv.app M)) (by
        apply biprod.hom_ext'
        · simp only [Triangle.mk_mor₂, hψ, biprod.inl_desc_assoc, biprod.inl_map_assoc,
            etaleAbelianDerivedSquareDifference, biprod.inl_desc]
          rw [← etaleAbelianDerivedCompDirectImageMap_comp, Category.id_comp,
            etaleAbelianDerivedUnitCompMap_app_eq_compDirectImageMap,
            map_comp_etaleAbelianDerivedCompDirectImageMap]
        · simp only [Triangle.mk_mor₂, hψ, biprod.inr_desc_assoc, biprod.inr_map_assoc,
            etaleAbelianDerivedSquareDifference, biprod.inr_desc, Preadditive.neg_comp,
            Preadditive.comp_neg, neg_inj]
          rw [← etaleAbelianDerivedCompDirectImageMap_comp,
            etaleAbelianDerivedUnitCompMap_app_eq_compDirectImageMap j b c hcj M,
            map_comp_etaleAbelianDerivedCompDirectImageMap, hαβ'])
    simp only [Triangle.mk_mor₁, etaleAbelianDerivedSquareUnits] at hφ
    refine ⟨φ, ?_, ?_⟩
    · refine map_eq_homEquiv_symm_comp_of_comp_unit _ φ _ α ?_
      simpa using congrArg (· ≫ biprod.snd) hφ
    · refine map_eq_homEquiv_symm_comp_of_comp_unit _ φ _ β ?_
      simpa using congrArg (· ≫ biprod.fst) hφ

end Gluing

end Stacks.EtaleCohomology

end
