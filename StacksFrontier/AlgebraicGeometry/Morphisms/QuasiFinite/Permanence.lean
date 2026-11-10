module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField

/-!
# Permanence and descent of quasi-finiteness

Quasi-finiteness of a morphism to a base passes to its factor through any intermediate scheme:
if `f ≫ g` is quasi-finite at a point, so is `f`. In the other direction, local
quasi-finiteness descends along a surjection of sources, provided the morphism it descends to
is already locally of finite type — the residue field extension at a point of the middle scheme
is then sandwiched inside an algebraic one, so it is algebraic, which closes the point in its
fibre. Quasi-finiteness at a point is also stable under composition: the relevant stalk map is
a composite of two quasi-finite ring maps, and the finite type condition is witnessed on an
affine neighbourhood small enough to map into an affine neighbourhood of the image point.

## Main results

* `AlgebraicGeometry.quasiFiniteAt_of_comp` proves permanence of quasi-finiteness at a point.
* `AlgebraicGeometry.locallyOfFiniteType_of_comp` and
  `AlgebraicGeometry.LocallyQuasiFinite.of_comp` jointly prove permanence of local
  quasi-finiteness.
* `AlgebraicGeometry.locallyQuasiFinite_of_comp_surjective` descends local quasi-finiteness
  along a surjective first morphism.
* `AlgebraicGeometry.finiteTypeAt_comp` and `AlgebraicGeometry.quasiFiniteAt_comp` compose
  finite type, respectively quasi-finiteness, at a point with the same property at the image
  of that point.

## Implementation notes

The map from `X` to the base is represented by the composite `f ≫ g`. As in
`AlgebraicGeometry.quasiFiniteAt`, quasi-finiteness at a point uses that predicate, while local
quasi-finiteness is represented by the two typeclasses `AlgebraicGeometry.LocallyOfFiniteType`
and `AlgebraicGeometry.LocallyQuasiFinite`. The two existing Mathlib permanence theorems jointly
give the local assertion, so they carry the tag directly.

## References

* [Stacks Project, Tag 03WR](https://stacks.math.columbia.edu/tag/03WR)
* [Stacks Project, Tag 0GWS](https://stacks.math.columbia.edu/tag/0GWS)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Finite type at a point, recast as local finite type of the restriction to an affine
neighbourhood of that point. -/
private lemma finiteTypeAt_iff_exists_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    AlgebraicGeometry.finiteTypeAt f x ↔
      ∃ (V : X.affineOpens) (_ : x ∈ V.1), LocallyOfFiniteType (V.1.ι ≫ f) := by
  constructor
  · rintro ⟨U, V, hxV, hVU, hft⟩
    refine ⟨V, hxV, ?_⟩
    rw [← Scheme.Hom.resLE_comp_ι f hVU]
    have hiso {A B : CommRingCat} (φ : A ⟶ B) [IsIso φ] : φ.hom.FiniteType :=
      .of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    have : LocallyOfFiniteType (f.resLE U.1 V.1 hVU) :=
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).2 (by
        simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
          CommRingCat.hom_comp, RingHom.comp_assoc]
        exact (hiso _).comp (hft.comp (hiso _)))
    infer_instance
  · rintro ⟨V, hxV, hft⟩
    have := hft
    obtain ⟨_, ⟨U, hU, rfl⟩, hfxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    let xV : V.1.toScheme := ⟨x, hxV⟩
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
      V.1.toScheme.isBasis_affineOpens.exists_subset_of_mem_open
        (a := xV) (show f x ∈ U from hfxU) ((V.1.ι ≫ f) ⁻¹ᵁ U).isOpen
    change IsAffineOpen W at hW
    let W' : X.affineOpens := ⟨V.1.ι ''ᵁ W, hW.image_of_isOpenImmersion V.1.ι⟩
    have hW'U : W'.1 ≤ f ⁻¹ᵁ U := by
      rintro _ ⟨z, hz, rfl⟩
      exact hWU hz
    refine ⟨⟨U, hU⟩, W', ⟨xV, hxW, rfl⟩, hW'U, ?_⟩
    have ht := (V.1.ι ≫ f).finiteType_appLE hU hW hWU
    have eW : W ≤ V.1.ι ⁻¹ᵁ W'.1 := by simp [W']
    have : IsIso (V.1.ι.appLE W'.1 W eW) :=
      inferInstanceAs (IsIso (V.1.ι.app W'.1 ≫ V.1.toScheme.presheaf.map
        (eqToHom (V.1.ι.preimage_image_eq W).symm).op))
    rwa [← Scheme.Hom.appLE_comp_appLE V.1.ι f U W'.1 W hW'U eW, CommRingCat.hom_comp,
      RingHom.finiteType_respectsIso.cancel_right_isIso] at ht

add_to_stacks 03WR "local finite-type part of locally quasi-finite"
  AlgebraicGeometry.locallyOfFiniteType_of_comp
add_to_sga "3 V 6.1" "partial" AlgebraicGeometry.locallyOfFiniteType_of_comp
add_to_ega "I 6.3.4" "clause (v)" AlgebraicGeometry.locallyOfFiniteType_of_comp
add_to_ega "I 6.3.6" "local finite type of f" AlgebraicGeometry.locallyOfFiniteType_of_comp
add_to_ega "I 6.6.6" AlgebraicGeometry.locallyOfFiniteType_of_comp
add_to_ega "IV 1.3.4" AlgebraicGeometry.locallyOfFiniteType_of_comp
add_to_ega "IV 1.5.6" "partial" AlgebraicGeometry.locallyOfFiniteType_of_comp
add_to_ega "IV 6.11.9" "The induced morphism v" AlgebraicGeometry.locallyOfFiniteType_of_comp

add_to_stacks 03WR "fiberwise part of locally quasi-finite"
  AlgebraicGeometry.LocallyQuasiFinite.of_comp
add_to_ega "II 6.2.4" "(v)" AlgebraicGeometry.LocallyQuasiFinite.of_comp

/-- The stalk map of a composite is the composite of the stalk maps. -/
private lemma stalkMap_comp_hom {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X) :
    ((f ≫ g).stalkMap x).hom = (f.stalkMap x).hom.comp (g.stalkMap (f x)).hom := by
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- **Stacks Project, Tag 03WR.** If a composite is quasi-finite at a point of its
source, then its first factor is quasi-finite there. -/
@[stacks 03WR "quasi-finite at a point"]
public theorem quasiFiniteAt_of_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (x : X) (h : quasiFiniteAt (f ≫ g) x) :
    quasiFiniteAt f x := by
  refine ⟨(finiteTypeAt_iff_exists_restrict f x).2 ?_, ?_⟩
  · obtain ⟨V, hxV, hV⟩ := (finiteTypeAt_iff_exists_restrict (f ≫ g) x).1 h.1
    refine ⟨V, hxV, ?_⟩
    rw [← Category.assoc] at hV
    have := hV
    exact locallyOfFiniteType_of_comp (V.1.ι ≫ f) g
  · have hq : ((f ≫ g).stalkMap x).hom.QuasiFinite := h.2
    rw [stalkMap_comp_hom] at hq
    exact RingHom.QuasiFinite.of_comp hq

/-- A composite is of finite type at a point of its source as soon as the first morphism is
of finite type there and the second is of finite type at the image of that point. -/
public theorem finiteTypeAt_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
    (hf : AlgebraicGeometry.finiteTypeAt f x)
    (hg : AlgebraicGeometry.finiteTypeAt g (f.base x)) :
    AlgebraicGeometry.finiteTypeAt (f ≫ g) x := by
  obtain ⟨V, hxV, hV⟩ := (finiteTypeAt_iff_exists_restrict f x).1 hf
  obtain ⟨W, hfxW, hW⟩ := (finiteTypeAt_iff_exists_restrict g (f.base x)).1 hg
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV₀, hV₀le⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (a := x) (show x ∈ (V.1 ⊓ f ⁻¹ᵁ W.1 : X.Opens) from ⟨hxV, hfxW⟩)
      (V.1 ⊓ f ⁻¹ᵁ W.1).isOpen
  change IsAffineOpen V₀ at hV₀
  have hle₁ : V₀ ≤ V.1 := fun _ hz ↦ (hV₀le hz).1
  have hle₂ : V₀ ≤ f ⁻¹ᵁ W.1 := fun _ hz ↦ (hV₀le hz).2
  refine (finiteTypeAt_iff_exists_restrict (f ≫ g) x).2 ⟨⟨V₀, hV₀⟩, hxV₀, ?_⟩
  change LocallyOfFiniteType (Scheme.Opens.ι V₀ ≫ f ≫ g)
  have : LocallyOfFiniteType (Scheme.Opens.ι V₀ ≫ f) := by
    have := hV
    rw [← X.homOfLE_ι hle₁, Category.assoc]
    infer_instance
  have : LocallyOfFiniteType (f.resLE W.1 V₀ hle₂ ≫ W.1.ι) := by
    rwa [Scheme.Hom.resLE_comp_ι]
  have := locallyOfFiniteType_of_comp (f.resLE W.1 V₀ hle₂) W.1.ι
  have := hW
  rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι f hle₂, Category.assoc]
  infer_instance

/-- A composite is quasi-finite at a point of its source as soon as the first morphism is
quasi-finite there and the second is quasi-finite at the image of that point. -/
public theorem quasiFiniteAt_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
    (hf : quasiFiniteAt f x) (hg : quasiFiniteAt g (f.base x)) :
    quasiFiniteAt (f ≫ g) x := by
  refine ⟨finiteTypeAt_comp f g x hf.1 hg.1, ?_⟩
  change ((f ≫ g).stalkMap x).hom.QuasiFinite
  rw [stalkMap_comp_hom]
  exact RingHom.QuasiFinite.comp hf.2 hg.2

/-- **Stacks Project, Tag 0GWS.** If `f` is surjective, `f ≫ g` is locally
quasi-finite, and `g` is locally of finite type, then `g` is locally quasi-finite. -/
@[stacks 0GWS]
public theorem locallyQuasiFinite_of_comp_surjective
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Surjective f]
    [LocallyOfFiniteType (f ≫ g)]
    [LocallyQuasiFinite (f ≫ g)]
    [LocallyOfFiniteType g] :
    LocallyQuasiFinite g := by
  have hclosed : ∀ y : Y, IsClosed ({g.asFiber y} : Set (g.fiber (g y))) := by
    intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    let _ : Algebra (S.residueField (g (f x))) (X.residueField x) :=
      ((f ≫ g).residueFieldMap x).hom.toAlgebra
    have : Module.Finite (S.residueField (g (f x))) (X.residueField x) :=
      (isClosed_asFiber_iff_finite_residueField (f ≫ g) x).mp
        ((f ≫ g).quasiFiniteAt x).isClopen_singleton_asFiber.isClosed
    let _ := (g.residueFieldMap (f x)).hom.toAlgebra
    let _ := (f.residueFieldMap x).hom.toAlgebra
    have : IsScalarTower (S.residueField (g (f x)))
        (Y.residueField (f x)) (X.residueField x) :=
      IsScalarTower.of_algebraMap_eq fun z ↦ by
        change ((f ≫ g).residueFieldMap x).hom z =
          (f.residueFieldMap x).hom ((g.residueFieldMap (f x)).hom z)
        rw [Scheme.residueFieldMap_comp]
        rfl
    have : Algebra.IsAlgebraic (S.residueField (g (f x))) (X.residueField x) :=
      Algebra.IsAlgebraic.of_finite _ _
    have : Algebra.IsAlgebraic (S.residueField (g (f x))) (Y.residueField (f x)) :=
      Algebra.IsAlgebraic.of_injective
        (IsScalarTower.toAlgHom (S.residueField (g (f x)))
          (Y.residueField (f x)) (X.residueField x))
        (f.residueFieldMap x).hom.injective
    exact isClosed_asFiber_of_isAlgebraic_residueField g (f x) inferInstance
  have hfiberClosed : ∀ (s : S) (y' : g.fiber s), IsClosed ({y'} : Set (g.fiber s)) := by
    intro s y'
    rw [← (g.fiberHomeo s).symm_apply_apply y']
    generalize g.fiberHomeo s y' = z'
    obtain ⟨z, hz⟩ := z'
    change g z = s at hz
    subst s
    simpa [Scheme.Hom.asFiber] using hclosed z
  refine ((forall_quasiFiniteAt_iff g).mp fun y ↦ ?_).2
  apply (quasiFiniteAt_tfae g y).out 3 1 |>.mp
  refine ⟨hclosed y, ?_⟩
  rintro ⟨y', hy', hspec⟩
  rw [specializes_iff_mem_closure, (hfiberClosed (g y) y').closure_eq] at hspec
  exact hy' hspec.symm

end AlgebraicGeometry
