module

public import StacksFrontier.AlgebraicGeometry.Spaces.StructureContraction
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageUniformBound
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase

/-!
# Étale locality of `c_*𝒪_X = 𝒪_Y` and `R¹c_*𝒪_X = 0`

Let

```
X' --i--> X
|c'       |c
Y' --g--> Y
```

be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `g` étale. This file shows that the condition
`AlgebraicGeometry.Space.IsStructureContraction` — the structure map `c♯ : 𝒪_Y ⟶ c_*𝒪_X` is an
isomorphism and `R¹c_*𝒪_X = 0` — passes from `c` to `c'`, and back from `c'` to `c` when `g` is
moreover surjective. This is the sense in which the conclusion of Stacks 0E88 is "local in the
étale topology", the reduction its proof starts with.

## Main results

* `CategoryTheory.Sheaf.isIso_of_forall_exists_mem_isIso_app`: a morphism of sheaves of rings
  that is invertible on the sections over the members of a covering sieve of every object is
  invertible.
* `AlgebraicGeometry.Space.exists_mem_forall_smallEtalePostcomp_iso`: for an étale surjective
  `g : Y' ⟶ Y`, every étale chart of `Y` has a covering sieve whose members come from charts of
  `Y'`.
* `AlgebraicGeometry.Space.isIso_of_isIso_smallEtaleRingRestriction_map`: restriction along an
  étale surjective morphism reflects isomorphisms of sheaves of rings.
* `AlgebraicGeometry.Space.isIso_structureSharp_iff_of_isPullback`: `c'♯` is invertible exactly
  when the restriction of `c♯` along `g` is.
* `AlgebraicGeometry.Space.firstHigherDirectImageStructureSheafEtaleBaseChangeIso`:
  `R¹c'_*𝒪_{X'} ≅ (R¹c_*𝒪_X)|_{Y'}`, the higher-direct-image clause of Stacks 03LX at the
  structure sheaf.
* `AlgebraicGeometry.Space.isStructureContraction_of_isPullback`: the condition passes to `c'`.
* `AlgebraicGeometry.Space.isStructureContraction_of_isPullback_of_isSurjective`: it descends to
  `c` when `g` is surjective.
* `AlgebraicGeometry.Space.isStructureContraction_iff_of_isPullback_of_isIso`: in particular it
  is invariant under isomorphisms of arrows.

## Implementation notes

The structure maps are compared through
`AlgebraicGeometry.Space.baseChangeStructureSharp_comp_baseChangeRingMap`, whose two ring
comparisons and whose `AlgebraicGeometry.Space.baseChangeRingMap` are isomorphisms; the last one
because its underlying morphism of sheaves of sets is the base-change isomorphism of Stacks 03LR,
part (1), and forgetting the ring structure reflects isomorphisms. The objects involved are
sheaves of rings typed both in `CategoryTheory.Sheaf` and in the full subcategory of sheaves,
so the isomorphisms are bundled by hand rather than found by instance search.

The étale restriction of the structure sheaf of `X` is the structure sheaf of `X'` on the nose
(`AlgebraicGeometry.Space.etaleModulePullbackUnitIso` is `Iso.refl`), so Stacks 03LX for the
higher direct images, `AlgebraicGeometry.Space.moduleHigherPushforwardEtaleBaseChangeIso`, applies
directly to `𝒪_X`.

## References

* [Stacks Project, Tag 0E88](https://stacks.math.columbia.edu/tag/0E88)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe v w

variable {C : Type*} [Category.{v} C] {J : GrothendieckTopology C}

/-- **A morphism of sheaves which is invertible on the sections over the objects of a covering
sieve of every object is invertible.** -/
theorem isIso_of_forall_exists_mem_isIso_app [J.HasSheafCompose (forget RingCat.{w})]
    {F G : Sheaf J RingCat.{w}} (φ : F ⟶ G)
    (h : ∀ V : C, ∃ R : Sieve V, R ∈ J V ∧
      ∀ ⦃W : C⦄ (a : W ⟶ V), R a → IsIso (φ.hom.app (op W))) :
    IsIso φ := by
  choose R hR hRa using h
  refine (Sheaf.isLocallyBijective_iff_isIso φ).1 ⟨⟨fun {X} x y hxy => ?_⟩, ⟨fun {U} s => ?_⟩⟩
  · refine J.superset_covering (fun W a ha => ?_) (hR X.unop)
    have := hRa _ a ha
    apply (ConcreteCategory.bijective_of_isIso (φ.hom.app (op W))).1
    change φ.hom.app (op W) (F.obj.map a.op x) = φ.hom.app (op W) (F.obj.map a.op y)
    rw [NatTrans.naturality_apply φ.hom a.op x, NatTrans.naturality_apply φ.hom a.op y, hxy]
  · refine J.superset_covering (fun W a ha => ?_) (hR U)
    have := hRa _ a ha
    exact (ConcreteCategory.bijective_of_isIso (φ.hom.app (op W))).2 (G.obj.map a.op s)

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The charts in the image of a surjective étale morphism cover.** For an étale surjective
`c : Z ⟶ Y` of algebraic spaces, every étale scheme chart `W` of `Y` has a covering sieve whose
members are all isomorphic to charts of `Y` obtained by postcomposing a chart of `Z` with `c`. -/
theorem exists_mem_forall_smallEtalePostcomp_iso {Z Y : AlgebraicSpaces B S hS} (c : Z ⟶ Y)
    (hc : IsEtale B S hS c.hom) (hsurj : IsSurjective B S hS c.hom) (W : SmallEtale B S hS Y.1) :
    ∃ R : Sieve W, R ∈ SmallEtale.topology B S hS Y.1 W ∧
      ∀ ⦃W' : SmallEtale B S hS Y.1⦄ (a : W' ⟶ W), R a →
        ∃ W'' : SmallEtale B S hS Z.1,
          Nonempty ((smallEtalePostcomp B S hS c hc).obj W'' ≅ W') := by
  obtain ⟨T, t, htsurj, htet⟩ := Z.2.exists_atlas
  have ht : IsEtale B S hS t := (isEtale_iff_presheaf_of_yoneda B S hS t).2 htet
  have htc : IsEtale B S hS (t ≫ c.hom) := isEtale_comp B S hS ht hc
  let U : SmallEtale B S hS Y.1 :=
    ⟨CostructuredArrow.mk (t ≫ c.hom), (isEtale_iff_presheaf_of_yoneda B S hS _).1 htc⟩
  have hUsurj : IsSurjective B S hS U.1.hom :=
    isSurjective_comp B S hS ((presheafSurjective_iff_isSurjective_yoneda B S hS Z.1 Z.2 T t).1
      htsurj) hsurj
  have hcov := SmallEtale.coversTop_of_isSurjective B S hS Y.1 Y.2 U hUsurj
  refine ⟨_, hcov W, ?_⟩
  rintro W' g ⟨_, ⟨φ⟩⟩
  have hφ : Etale ((BigFppfOver.toScheme B S hS).map φ.hom.left) :=
    etale_toScheme_toOver_map B S hS Y.1 φ
  have hW'' : IsEtale B S hS (yoneda.map φ.hom.left ≫ t) :=
    isEtale_of_presheaf_etale B S hS (etale_comp_of_scheme B S hS φ.hom.left t hφ
      (presheaf_etale_of_isEtale B S hS ht))
  let W'' : SmallEtale B S hS Z.1 :=
    ⟨CostructuredArrow.mk (yoneda.map φ.hom.left ≫ t),
      (isEtale_iff_presheaf_of_yoneda B S hS _).1 hW''⟩
  exact ⟨W'', ⟨ObjectProperty.isoMk _ (CostructuredArrow.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ W'.1.hom = (yoneda.map φ.hom.left ≫ t) ≫ c.hom
      rw [Category.id_comp, Category.assoc, ← CostructuredArrow.w φ.hom]
      rfl))⟩⟩

/-- **Restriction along a surjective étale morphism reflects isomorphisms of sheaves of
rings.** -/
theorem isIso_of_isIso_smallEtaleRingRestriction_map {Z Y : AlgebraicSpaces B S hS} (c : Z ⟶ Y)
    (hc : IsEtale B S hS c.hom) (hsurj : IsSurjective B S hS c.hom)
    {F G : Sheaf (SmallEtale.topology B S hS Y.1) RingCat.{u}} (φ : F ⟶ G)
    (hφ : IsIso ((smallEtaleRingRestriction B S hS c hc).map φ)) : IsIso φ := by
  refine Sheaf.isIso_of_forall_exists_mem_isIso_app φ fun W => ?_
  obtain ⟨R, hR, hRW⟩ := exists_mem_forall_smallEtalePostcomp_iso B S hS c hc hsurj W
  refine ⟨R, hR, fun W' a ha => ?_⟩
  obtain ⟨W'', ⟨e⟩⟩ := hRW a ha
  have h1 : IsIso (φ.hom.app (op ((smallEtalePostcomp B S hS c hc).obj W''))) :=
    inferInstanceAs (IsIso (((smallEtaleRingRestriction B S hS c hc).map φ).hom.app (op W'')))
  have : IsIso (φ.hom.app (op W') ≫ G.obj.map e.op.hom) := by
    rw [← φ.hom.naturality e.op.hom]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (G.obj.map e.op.hom)

attribute [local instance] etaleModulePullback_additive

section BaseChange

variable {B S hS} {X X' Y Y' : AlgebraicSpaces B S hS} {i : X' ⟶ X} {c' : X' ⟶ Y'} {c : X ⟶ Y}
  {g : Y' ⟶ Y}

/-- **The structure map of an étale base change is the restriction of the structure map.** For
a cartesian square with `g` étale, `c'♯ : 𝒪_{Y'} ⟶ c'_*𝒪_{X'}` is an isomorphism exactly when the
étale restriction along `g` of `c♯ : 𝒪_Y ⟶ c_*𝒪_X` is. -/
theorem isIso_structureSharp_iff_of_isPullback (sq : IsPullback i c' c g)
    (hg : IsEtale B S hS g.hom) :
    IsIso (structureSharp B S hS c') ↔
      IsIso ((smallEtaleRingRestriction B S hS g hg).map (structureSharp B S hS c)) := by
  have hM : IsIso (baseChangeRingMap B S hS i c' c g sq hg) := by
    have : IsIso ((sheafCompose (SmallEtale.topology B S hS Y'.1) (forget RingCat.{u})).map
        (baseChangeRingMap B S hS i c' c g sq hg)) := by
      rw [baseChangeRingMap,
        Stacks.Sheaves.ToposPullback.ringSheafMap_pullbackRingSheafMapOfNatTrans]
      exact Iso.isIso_hom ((smallEtaleSetPushforwardBaseChangeIso B S hS i c' c g sq hg).app _)
    exact isIso_of_reflects_iso _
      (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget RingCat.{u}))
  have hi := isEtale_of_isPullback B S hS c' i g c sq.flip hg
  let T : structureRingSheafDirectImage B S hS c' ≅
      (smallEtaleRingRestriction B S hS g hg).obj (structureRingSheafDirectImage B S hS c) :=
    (etaleBaseChangeRingComparison B S hS i c' hi).symm ≪≫
      etaleBaseChangeRingCompIso B S hS i c' hi ≪≫
        @asIso _ _ _ _ (baseChangeRingMap B S hS i c' c g sq hg) hM
  have key : structureSharp B S hS c' ≫ T.hom =
      (smallEtaleRingRestriction B S hS g hg).map (structureSharp B S hS c) := by
    rw [← baseChangeStructureSharp_comp_baseChangeRingMap B S hS i c' c g sq hg]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
      Stacks.Sheaves.ToposPullback.pullbackRingSheafFunctor_map, baseChangeStructureSharp,
      Category.assoc, T]
    rfl
  rw [← key]
  exact (isIso_comp_right_iff _ _).symm

/-- **The first higher direct image of an étale base change is the restriction of the first
higher direct image** (Stacks 03LX), at the structure sheaf: `R¹c'_*𝒪_{X'} ≅ (R¹c_*𝒪_X)|_{Y'}`. -/
noncomputable def firstHigherDirectImageStructureSheafEtaleBaseChangeIso (sq : IsPullback i c' c g)
    (hg : IsEtale B S hS g.hom) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
    ((modulePushforward B S hS c').rightDerived 1).obj (structureSheafModule B S hS X') ≅
      (etaleModulePullback B S hS g hg).obj
        (((modulePushforward B S hS c).rightDerived 1).obj (structureSheafModule B S hS X)) :=
  (moduleHigherPushforwardEtaleBaseChangeIso B S hS i c' c g sq hg 1).app
    (structureSheafModule B S hS X)

/-- **`c_*𝒪_X = 𝒪_Y` and `R¹c_*𝒪_X = 0` are preserved by étale base change.** For a cartesian
square

```
X' --i--> X
|c'       |c
Y' --g--> Y
```

of algebraic spaces with `g` étale, if `c♯ : 𝒪_Y ⟶ c_*𝒪_X` is an isomorphism and `R¹c_*𝒪_X = 0`,
then the same holds for `c'`. -/
theorem isStructureContraction_of_isPullback (sq : IsPullback i c' c g)
    (hg : IsEtale B S hS g.hom) (h : IsStructureContraction B S hS c) :
    IsStructureContraction B S hS c' := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨(isIso_structureSharp_iff_of_isPullback sq hg).2 inferInstance, ?_⟩
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
  exact IsZero.of_iso ((etaleModulePullback B S hS g hg).map_isZero h₂)
    (firstHigherDirectImageStructureSheafEtaleBaseChangeIso sq hg)

/-- **`c_*𝒪_X = 𝒪_Y` and `R¹c_*𝒪_X = 0` descend along a surjective étale base change.** For a
cartesian square

```
X' --i--> X
|c'       |c
Y' --g--> Y
```

of algebraic spaces with `g` étale and surjective, if `c'♯ : 𝒪_{Y'} ⟶ c'_*𝒪_{X'}` is an
isomorphism and `R¹c'_*𝒪_{X'} = 0`, then the same holds for `c`. -/
theorem isStructureContraction_of_isPullback_of_isSurjective (sq : IsPullback i c' c g)
    (hg : IsEtale B S hS g.hom) (hsurj : IsSurjective B S hS g.hom)
    (h : IsStructureContraction B S hS c') : IsStructureContraction B S hS c := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨isIso_of_isIso_smallEtaleRingRestriction_map B S hS g hg hsurj _
    ((isIso_structureSharp_iff_of_isPullback sq hg).1 h₁), ?_⟩
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
  exact isZero_of_isZero_etaleModulePullback_of_isSurjective B S hS g hg hsurj _
    (IsZero.of_iso h₂ (firstHigherDirectImageStructureSheafEtaleBaseChangeIso sq hg).symm)

/-- **For an étale surjective base change, `c` satisfies `c_*𝒪_X = 𝒪_Y` and `R¹c_*𝒪_X = 0`
exactly when `c'` does.** -/
theorem isStructureContraction_iff_of_isPullback_of_isSurjective (sq : IsPullback i c' c g)
    (hg : IsEtale B S hS g.hom) (hsurj : IsSurjective B S hS g.hom) :
    IsStructureContraction B S hS c ↔ IsStructureContraction B S hS c' :=
  ⟨isStructureContraction_of_isPullback sq hg,
    isStructureContraction_of_isPullback_of_isSurjective sq hg hsurj⟩

/-- **`c_*𝒪_X = 𝒪_Y` and `R¹c_*𝒪_X = 0` are invariant under isomorphism.** For a cartesian square
whose bottom edge `g` is an isomorphism, `c` satisfies the two conditions exactly when `c'`
does: an isomorphism is étale and surjective. -/
theorem isStructureContraction_iff_of_isPullback_of_isIso (sq : IsPullback i c' c g) [IsIso g] :
    IsStructureContraction B S hS c ↔ IsStructureContraction B S hS c' := by
  have : IsIso g.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).map g))
  exact isStructureContraction_iff_of_isPullback_of_isSurjective sq (isEtale_of_isIso B S hS g.hom)
    (isSurjective_of_isIso B S hS g.hom)

end BaseChange

end AlgebraicGeometry.Space

end
