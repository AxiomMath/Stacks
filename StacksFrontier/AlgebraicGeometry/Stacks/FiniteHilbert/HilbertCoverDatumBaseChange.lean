module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.HilbertCoverDatumGluing

/-!
# The gluing isomorphism of a descent datum of `ℋ_d` base-changes

`AlgebraicGeometry.Stack.datumGluing` reads the gluing isomorphism of a descent datum of the
category `ℋ_d` of degree-`d` finite locally free covers at a pair of morphisms `ε`, `ε'` out of
one object `Z` of the site. The third axiom of
`CategoryTheory.Functor.SieveDescentDatum`, its compatibility with base change, says that the
gluing isomorphism at `(γ ≫ ε, γ ≫ ε')` is the one at `(ε, ε')` pulled back along `γ`. This file
states that axiom in fibre-product coordinates: the comparison isomorphisms of the chosen
pullbacks are replaced by the canonical morphisms of fibre products, and the conclusion becomes an
equation between morphisms into the covering object of the second arrow.

## Main definitions

* `AlgebraicGeometry.Stack.fiberPointCompMap`: the canonical morphism of `ℋ_d` from the base
  change of an object of a fibre along `γ ≫ ε` to its base change along `ε`. It is the value of
  `AlgebraicGeometry.Stack.finiteCoverPointMap` at `γ` read as a morphism of the slice at the
  base, so its base component is `γ` and its cover component is the gap-filler of the
  fibre-product square.

## Main results

* `AlgebraicGeometry.Stack.fiberPointCompMap_comp_fiberPointHom`:
  `AlgebraicGeometry.Stack.fiberPointCompMap` is the comparison of the two base changes over the
  object of the fibre — it is the unique morphism over `γ` which carries the projection of the
  base change along `ε` to the projection of the base change along `γ ≫ ε`.
* `AlgebraicGeometry.Stack.datumCoverIso_comp`: **the base-change axiom in fibre-product
  coordinates.** The gluing isomorphism at `(γ ≫ ε, γ ≫ ε')`, followed by the projection of the
  second base change, is `AlgebraicGeometry.Stack.fiberPointCompMap` followed by the gluing
  isomorphism at `(ε, ε')` and that projection.
* `AlgebraicGeometry.Stack.datumGluing_comp_fst`: the same equation on the covering objects of the
  site.
* `AlgebraicGeometry.Stack.datumGluing_comp_fst_of_fac`: the same with the morphism of fibre
  products given as any morphism with the same two components.

## References

* [Stacks Project, Tag 026B](https://stacks.math.columbia.edu/tag/026B)
* [Stacks Project, Tag 026C](https://stacks.math.columbia.edu/tag/026C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] finiteCoverPointObj finiteCoverProjection
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}

/-- Two morphisms of `ℋ_d` over the same morphism that agree after a cartesian morphism are
equal. -/
private theorem eq_of_comp_eq_of_isCartesian {V U Z : BigFppfOver B S hS} {ε : V ⟶ U}
    {γ : Z ⟶ V} {a b c : FiniteCover B S hS d} (φ : b ⟶ c)
    [(finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsCartesian ε φ]
    (ν ν' : a ⟶ b) [(finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift γ ν]
    [(finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift γ ν']
    (h : ν ≫ φ = ν' ≫ φ) : ν = ν' := by
  have := (isFiberedInGroupoids_finiteCoverProjection
    (B := B) (S := S) (hS := hS) (d := d)).isStronglyCartesian_homLift ε φ
  exact Functor.IsStronglyCartesian.ext
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) ε φ γ h

/-! ### Iterated base change of an object of a fibre -/

section Comp

variable {V U Z : BigFppfOver B S hS}
  (x : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber U)
  (ε : V ⟶ U) (γ : Z ⟶ V)

/-- **The comparison of the two base changes of an object of a fibre of `ℋ_d` over a composite.**
Base changing the cover of `x` along `γ ≫ ε` and along `ε` gives two objects of `ℋ_d`, over `Z`
and over `V`; this is the morphism between them obtained by base changing the cover along the
morphism `γ` of the slice of the site at `U`. Its base component is `γ` and its cover component
is the gap-filler of the fibre-product square. -/
def fiberPointCompMap : (fiberPointObj x (γ ≫ ε)).1 ⟶ (fiberPointObj x ε).1 :=
  finiteCoverPointMap (fiberCoverHom x) (isFiniteLocallyFreeOfRank_fiberCoverHom x)
    (Over.homMk γ rfl : (Over.mk (γ ≫ ε) : Over U) ⟶ Over.mk ε)

/-- The base component of `AlgebraicGeometry.Stack.fiberPointCompMap` is `γ`. -/
@[simp]
theorem fiberPointCompMap_f : (fiberPointCompMap x ε γ).f = γ := rfl

/-- The cover component of `AlgebraicGeometry.Stack.fiberPointCompMap` followed by the first
projection of the fibre product along `ε` is the first projection of the fibre product along
`γ ≫ ε`. -/
@[reassoc (attr := simp)]
theorem fiberPointCompMap_g_comp_fst :
    (fiberPointCompMap x ε γ).g ≫ pullback.fst (fiberCoverHom x) ε =
      pullback.fst (fiberCoverHom x) (γ ≫ ε) :=
  finiteCoverPointMap_g_comp_fst _ _ _

/-- The cover component of `AlgebraicGeometry.Stack.fiberPointCompMap` followed by the second
projection of the fibre product along `ε` is the second projection of the fibre product along
`γ ≫ ε` followed by `γ`. -/
@[reassoc (attr := simp)]
theorem fiberPointCompMap_g_comp_snd :
    (fiberPointCompMap x ε γ).g ≫ pullback.snd (fiberCoverHom x) ε =
      pullback.snd (fiberCoverHom x) (γ ≫ ε) ≫ γ :=
  finiteCoverPointMap_g_comp_snd _ _ _

/-- **The comparison lies over `γ`.** -/
theorem isHomLift_fiberPointCompMap :
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift γ
      (fiberPointCompMap x ε γ) :=
  CategoryTheory.IsHomLift.of_fac'
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) γ _ rfl rfl (by
      show γ = eqToHom rfl ≫ γ ≫ eqToHom rfl
      simp)

/-- **The comparison carries the projection of the base change along `ε` to the projection of the
base change along `γ ≫ ε`.** -/
@[reassoc]
theorem fiberPointCompMap_comp_fiberPointHom :
    fiberPointCompMap x ε γ ≫ fiberPointHom x (Over.mk ε) =
      fiberPointHom x (Over.mk (γ ≫ ε)) := by
  refine FiniteCover.Hom.ext ?_ ?_
  · show γ ≫ ε ≫ eqToHom x.2.symm = (γ ≫ ε) ≫ eqToHom x.2.symm
    exact (Category.assoc _ _ _).symm
  · exact fiberPointCompMap_g_comp_fst x ε γ

/-- **A morphism of `ℋ_d` over `γ` which carries the projection of the base change along `ε` to
the projection of the base change along `γ ≫ ε` is the comparison.** -/
theorem eq_fiberPointCompMap (ν : (fiberPointObj x (γ ≫ ε)).1 ⟶ (fiberPointObj x ε).1)
    (hν : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift γ ν)
    (hfac : ν ≫ fiberPointHom x (Over.mk ε) = fiberPointHom x (Over.mk (γ ≫ ε))) :
    ν = fiberPointCompMap x ε γ := by
  have := isHomLift_fiberPointCompMap x ε γ
  have : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsCartesian ε
      (fiberPointHom x (Over.mk ε)) := isCartesian_fiberPointHom x ε
  exact eq_of_comp_eq_of_isCartesian (ε := ε) (γ := γ) (fiberPointHom x (Over.mk ε)) ν _
    (hfac.trans (fiberPointCompMap_comp_fiberPointHom x ε γ).symm)

/-- **The comparison of the two base changes, read against the chosen pullbacks.** Contracting the
iterated chosen pullback and comparing each chosen pullback with the fibre product is the same as
comparing the fibre products first and the chosen pullback of the composite afterwards. -/
@[reassoc]
theorem fiberPointCompMap_comp_pullbackFiberIsoPointObj_inv :
    Functor.Fiber.fiberInclusion.map (pullbackFiberIsoPointObj x (γ ≫ ε)).inv ≫
        Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberCompIso x ε γ).inv ≫
        Functor.IsPreFibered.pullbackMap
          (Functor.pullbackFiber
            (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) x ε).2 γ =
      fiberPointCompMap x ε γ ≫
        Functor.Fiber.fiberInclusion.map (pullbackFiberIsoPointObj x ε).inv := by
  have : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift (𝟙 Z)
      (Functor.Fiber.fiberInclusion.map (pullbackFiberIsoPointObj x (γ ≫ ε)).inv) :=
    (pullbackFiberIsoPointObj x (γ ≫ ε)).inv.2
  have : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift (𝟙 Z)
      (Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberCompIso x ε γ).inv) :=
    (Functor.pullbackFiberCompIso x ε γ).inv.2
  have : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift (𝟙 V)
      (Functor.Fiber.fiberInclusion.map (pullbackFiberIsoPointObj x ε).inv) :=
    (pullbackFiberIsoPointObj x ε).inv.2
  have : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsCartesian γ
      (Functor.IsPreFibered.pullbackMap
        (Functor.pullbackFiber
          (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) x ε).2 γ) :=
    Functor.IsPreFibered.pullbackMap.IsCartesian _ _
  have := isHomLift_fiberPointCompMap x ε γ
  have : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsCartesian ε
      (Functor.IsPreFibered.pullbackMap x.2 ε) :=
    Functor.IsPreFibered.pullbackMap.IsCartesian x.2 ε
  have hiL : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift γ
      (Functor.Fiber.fiberInclusion.map (pullbackFiberIsoPointObj x (γ ≫ ε)).inv ≫
        Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberCompIso x ε γ).inv ≫
        Functor.IsPreFibered.pullbackMap
          (Functor.pullbackFiber
            (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) x ε).2 γ) := by
    have h : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift
        (𝟙 Z ≫ 𝟙 Z ≫ γ)
        (Functor.Fiber.fiberInclusion.map (pullbackFiberIsoPointObj x (γ ≫ ε)).inv ≫
          Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberCompIso x ε γ).inv ≫
          Functor.IsPreFibered.pullbackMap
            (Functor.pullbackFiber
              (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) x ε).2 γ) :=
      inferInstance
    simpa using h
  have hiR : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift γ
      (fiberPointCompMap x ε γ ≫
        Functor.Fiber.fiberInclusion.map (pullbackFiberIsoPointObj x ε).inv) := by
    have h : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift (γ ≫ 𝟙 V)
        (fiberPointCompMap x ε γ ≫
          Functor.Fiber.fiberInclusion.map (pullbackFiberIsoPointObj x ε).inv) := inferInstance
    simpa using h
  have hL : (Functor.Fiber.fiberInclusion.map (pullbackFiberIsoPointObj x (γ ≫ ε)).inv ≫
        Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberCompIso x ε γ).inv ≫
        Functor.IsPreFibered.pullbackMap
          (Functor.pullbackFiber
            (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) x ε).2 γ) ≫
      Functor.IsPreFibered.pullbackMap x.2 ε = fiberPointHom x (Over.mk (γ ≫ ε)) := by
    simp only [Category.assoc, Functor.pullbackFiberCompIso_inv_fac,
      fiberInclusion_pullbackFiberIsoPointObj_inv_comp]
  have hR : (fiberPointCompMap x ε γ ≫
        Functor.Fiber.fiberInclusion.map (pullbackFiberIsoPointObj x ε).inv) ≫
      Functor.IsPreFibered.pullbackMap x.2 ε = fiberPointHom x (Over.mk (γ ≫ ε)) := by
    rw [Category.assoc, fiberInclusion_pullbackFiberIsoPointObj_inv_comp,
      fiberPointCompMap_comp_fiberPointHom]
  exact eq_of_comp_eq_of_isCartesian (ε := ε) (γ := γ) (Functor.IsPreFibered.pullbackMap x.2 ε) _ _
    (hL.trans hR.symm)

end Comp

/-! ### The base-change axiom in fibre-product coordinates -/

section BaseChange

variable {U : BigFppfOver B S hS} {R : Sieve U}
  (D : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).SieveDescentDatum R)

/-- **The gluing isomorphism of `AlgebraicGeometry.Stack.datumCoverIso`, followed by the
projection of the second fibre product, read through the chosen pullbacks.** -/
@[reassoc]
theorem datumCoverIso_hom_comp_fiberPointHom ⦃V W Z : BigFppfOver B S hS⦄ ⦃f : V ⟶ U⦄
    (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    Functor.Fiber.fiberInclusion.map (datumCoverIso D hf hg ε ε' heq).hom ≫
        fiberPointHom (D.obj g hg) (Over.mk ε') =
      Functor.Fiber.fiberInclusion.map (pullbackFiberIsoPointObj (D.obj f hf) ε).inv ≫
        Functor.Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom ≫
        Functor.IsPreFibered.pullbackMap (D.obj g hg).2 ε' := by
  rw [datumCoverIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc,
    fiberInclusion_pullbackFiberIsoPointObj_hom_comp]

/-- **The base-change axiom of a descent datum of `ℋ_d`, in fibre-product coordinates.** The
gluing isomorphism at `(γ ≫ ε, γ ≫ ε')`, followed by the projection of the fibre product of the
second cover along `γ ≫ ε'`, is the comparison
`AlgebraicGeometry.Stack.fiberPointCompMap` followed by the gluing isomorphism at `(ε, ε')` and
the projection of the fibre product along `ε'`. -/
theorem datumCoverIso_comp ⦃V W Z Z' : BigFppfOver B S hS⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄
    (hg : R g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) (γ : Z' ⟶ Z)
    (hγ : (γ ≫ ε) ≫ f = (γ ≫ ε') ≫ g) :
    Functor.Fiber.fiberInclusion.map (datumCoverIso D hf hg (γ ≫ ε) (γ ≫ ε') hγ).hom ≫
        fiberPointHom (D.obj g hg) (Over.mk (γ ≫ ε')) =
      fiberPointCompMap (D.obj f hf) ε γ ≫
        Functor.Fiber.fiberInclusion.map (datumCoverIso D hf hg ε ε' heq).hom ≫
        fiberPointHom (D.obj g hg) (Over.mk ε') := by
  rw [datumCoverIso_hom_comp_fiberPointHom, datumCoverIso_hom_comp_fiberPointHom,
    ← D.iso_pullback hf hg ε ε' heq γ]
  simp only [Functor.map_comp, Category.assoc, Functor.pullbackFiberCompIso_hom_fac,
    Functor.pullbackFiberIso_hom, Functor.pullbackFiberHom_fac_assoc]
  rw [fiberPointCompMap_comp_pullbackFiberIsoPointObj_inv_assoc]

/-- **The base-change axiom on the covering objects of the site.** The gluing isomorphism of
`AlgebraicGeometry.Stack.datumGluing` is an *action*: precomposing the pair of morphisms out of
`Z` with `γ` changes the resulting point of the second covering object only through the
precomposition. This is the cover component of `AlgebraicGeometry.Stack.datumCoverIso_comp`. -/
theorem datumGluing_comp_fst ⦃V W Z Z' : BigFppfOver B S hS⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄
    (hg : R g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) (γ : Z' ⟶ Z)
    (hγ : (γ ≫ ε) ≫ f = (γ ≫ ε') ≫ g) :
    (datumGluing D hf hg (γ ≫ ε) (γ ≫ ε') hγ).hom ≫
        pullback.fst (fiberCoverHom (D.obj g hg)) (γ ≫ ε') =
      (fiberPointCompMap (D.obj f hf) ε γ).g ≫ (datumGluing D hf hg ε ε' heq).hom ≫
        pullback.fst (fiberCoverHom (D.obj g hg)) ε' :=
  congrArg (fun m => FiniteCover.Hom.g m) (datumCoverIso_comp D hf hg ε ε' heq γ hγ)

/-- **The base-change axiom on the covering objects, at a pair of morphisms that merely factors
through a given one.** This is `AlgebraicGeometry.Stack.datumGluing_comp_fst` with the factoring
morphism of fibre products replaced by any morphism `μ` having the same two components as
`AlgebraicGeometry.Stack.fiberPointCompMap`. -/
theorem datumGluing_comp_fst_of_fac ⦃V W Z Z' : BigFppfOver B S hS⦄ ⦃f : V ⟶ U⦄ (hf : R f)
    ⦃g : W ⟶ U⦄ (hg : R g) (ε₀ : Z ⟶ V) (ε₀' : Z ⟶ W) (heq₀ : ε₀ ≫ f = ε₀' ≫ g)
    (γ : Z' ⟶ Z) (ε : Z' ⟶ V) (ε' : Z' ⟶ W) (heq : ε ≫ f = ε' ≫ g)
    (hε : γ ≫ ε₀ = ε) (hε' : γ ≫ ε₀' = ε')
    (μ : pullback (fiberCoverHom (D.obj f hf)) ε ⟶ pullback (fiberCoverHom (D.obj f hf)) ε₀)
    (hμ₁ : μ ≫ pullback.fst (fiberCoverHom (D.obj f hf)) ε₀ =
      pullback.fst (fiberCoverHom (D.obj f hf)) ε)
    (hμ₂ : μ ≫ pullback.snd (fiberCoverHom (D.obj f hf)) ε₀ =
      pullback.snd (fiberCoverHom (D.obj f hf)) ε ≫ γ) :
    (datumGluing D hf hg ε ε' heq).hom ≫ pullback.fst (fiberCoverHom (D.obj g hg)) ε' =
      μ ≫ (datumGluing D hf hg ε₀ ε₀' heq₀).hom ≫
        pullback.fst (fiberCoverHom (D.obj g hg)) ε₀' := by
  subst hε hε'
  obtain rfl : μ = (fiberPointCompMap (D.obj f hf) ε₀ γ).g :=
    pullback.hom_ext (by rw [hμ₁, fiberPointCompMap_g_comp_fst])
      (by rw [hμ₂, fiberPointCompMap_g_comp_snd])
  exact datumGluing_comp_fst D hf hg ε₀ ε₀' heq₀ γ heq

end BaseChange

end AlgebraicGeometry.Stack

end
