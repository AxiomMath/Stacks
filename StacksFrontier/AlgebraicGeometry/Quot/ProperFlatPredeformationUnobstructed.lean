module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationObstructionGroups
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatVersalPowerSeries
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.Deformation.Artin.Infinitesimal.SiteContainment
public import StacksFrontier.Deformation.Artin.Obstruction.DualSituation
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.Examples.BaseCategoryOverItself
public import StacksFrontier.Deformation.SchlessingerConditions.SmoothMorphisms

/-!
# A point of `Spaces'_{fp, flat, proper}` with vanishing obstruction groups is unobstructed

Let `x₀ = (X₀ ⟶ Spec k)` be an object of `𝒳 = Spaces'_{fp, flat, proper}` over a field,
presented over an affine chart `Spec Λ ⟶ S`, and let `𝓕 = 𝓕_{𝒳,k,x₀}` be its predeformation
category. If the obstruction groups `T²(I) = Ext²_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A I)` of
[Stacks, Remark 0D1P] vanish for every deformation `x = (X ⟶ Spec A)` of `x₀` and every
`A`-module `I` killed by `𝔪_A`, then `𝓕` is unobstructed: its structure functor to `𝒞_Λ` is
smooth.

By [Stacks, Tag 06HH] it suffices to lift a deformation `x` over `A` along a small extension
`A' → A`. Such an extension is a square-zero thickening `Spec A ⊂ Spec A'` of Situation 07YX
whose ideal `I` is killed by `𝔪_A`, so the obstruction class of [Stacks, Tag 08V5] of `x` along it
(`AlgebraicGeometry.Space.ProperFlatLift.chartObstruction`) lies in the zero group `T²(I)`; it
vanishes, so `x` lifts to an object over `Spec A'`, which is a deformation over `A'` mapping to
`x` over `A' → A`.

## Main results

* `AlgebraicGeometry.ProperFlatSpaceDeformation.exists_deformationMorphism_of_isSmallExtension`:
  a deformation lifts along every small extension.
* `isSmooth_baseProjection_predeformationCat_of_obstructionGroupsVanish` (in
  `AlgebraicGeometry.ProperFlatSpaceDeformation`): `𝓕_{𝒳,k,x₀}` is unobstructed when the
  obstruction groups of all deformations vanish.

## References

* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
* [Stacks Project, Tag 06HH](https://stacks.math.columbia.edu/tag/06HH)
* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
-/

@[expose] public noncomputable section

open CategoryTheory Deformation Deformation.Artin InfinitesimalLifting

universe t u

/-! ### The kernel of a small extension -/

namespace AlgebraicGeometry.ProperFlatSpaceDeformation

section SmallExtension

variable {A' A : Type u} [CommRing A'] [CommRing A] [IsLocalRing A'] [IsArtinianRing A']
  [Nontrivial A] (φ : A' →+* A) (hsurj : Function.Surjective φ)
  (hlen : Module.length A' (RingHom.ker φ) = 1)

omit [IsArtinianRing A'] in
include hsurj in
/-- The kernel of a surjection onto a nonzero ring out of a local ring lies in the maximal
ideal. -/
theorem ker_le_maximalIdeal_of_surjective :
    RingHom.ker φ ≤ IsLocalRing.maximalIdeal A' := by
  refine IsLocalRing.le_maximalIdeal fun h => one_ne_zero (α := A) ?_
  obtain ⟨b, hb⟩ := hsurj 1
  have hbI : b ∈ RingHom.ker φ := by rw [h]; trivial
  rw [← hb, RingHom.mem_ker.mp hbI]

omit [IsLocalRing A'] [IsArtinianRing A'] [Nontrivial A] in
include hlen in
/-- The kernel of a small extension is nonzero. -/
theorem ker_ne_bot_of_length_eq_one : RingHom.ker φ ≠ ⊥ := by
  intro h
  have : Module.length A' (RingHom.ker φ) = 0 := by rw [h]; simp
  rw [hlen] at this
  exact one_ne_zero this

omit [Nontrivial A] in
include hlen in
/-- **The kernel of a small extension is killed by the maximal ideal**: it is a simple module,
and `𝔪 · I` is a proper submodule of it by Nakayama's lemma. -/
theorem maximalIdeal_mul_ker_eq_bot :
    IsLocalRing.maximalIdeal A' * RingHom.ker φ = ⊥ := by
  set I : Ideal A' := RingHom.ker φ with hI
  have hsimple : IsSimpleModule A' I := Module.length_eq_one_iff.mp hlen
  have hInz : I ≠ ⊥ := ker_ne_bot_of_length_eq_one φ hlen
  have hfg : (⊤ : Submodule A' I).FG := by
    have : Module.Finite A' I := Module.Finite.of_injective I.subtype I.subtype_injective
    exact Module.Finite.fg_top
  set N : Submodule A' I := IsLocalRing.maximalIdeal A' • (⊤ : Submodule A' I) with hN
  have hNtop : N ≠ ⊤ := by
    intro h
    have hle : (⊤ : Submodule A' I) ≤ Ring.jacobson A' • (⊤ : Submodule A' I) := by
      rw [IsLocalRing.ringJacobson_eq_maximalIdeal A', ← hN, h]
    have : (⊤ : Submodule A' I) = ⊥ := hfg.eq_bot_of_le_jacobson_smul hle
    rw [Submodule.eq_bot_iff] at this
    obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hInz
    exact hy0 (congrArg Subtype.val (this ⟨y, hyI⟩ trivial))
  have hNbot : N = ⊥ := (eq_bot_or_eq_top N).resolve_right hNtop
  have hpush : Submodule.map I.subtype N = IsLocalRing.maximalIdeal A' * I := by
    rw [hN, Submodule.map_smul'']
    congr 1
    simp [Submodule.map_top, Submodule.range_subtype]
  rw [hNbot, Submodule.map_bot] at hpush
  exact hpush.symm

omit [Nontrivial A] in
include hlen in
/-- An element of the maximal ideal times an element of the kernel of a small extension is
zero. -/
theorem mul_eq_zero_of_mem_maximalIdeal_of_mem_ker {r x : A'}
    (hr : r ∈ IsLocalRing.maximalIdeal A') (hx : x ∈ RingHom.ker φ) : r * x = 0 := by
  have h := Ideal.mul_mem_mul hr hx
  rw [maximalIdeal_mul_ker_eq_bot φ hlen] at h
  exact h

include hsurj hlen in
/-- The kernel of a small extension `A' → A` has at most the cardinality of `A`: it is spanned
by any nonzero element `t`, and `φ b ↦ b t` is well defined because the kernel is killed by the
maximal ideal. -/
theorem mk_ker_le_of_length_eq_one : Cardinal.mk (RingHom.ker φ) ≤ Cardinal.mk A := by
  set I : Ideal A' := RingHom.ker φ with hI
  have hsimple : IsSimpleModule A' I := Module.length_eq_one_iff.mp hlen
  obtain ⟨t, htI, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (ker_ne_bot_of_length_eq_one φ hlen)
  let T : I := ⟨t, htI⟩
  have hspan : Submodule.span A' {T} = ⊤ := by
    refine (eq_bot_or_eq_top (Submodule.span A' {T})).resolve_left ?_
    rw [Submodule.span_singleton_eq_bot]
    exact fun h => ht0 (congrArg Subtype.val h)
  let g : A → I := fun a => ⟨Function.surjInv hsurj a * t, I.mul_mem_left _ htI⟩
  refine Cardinal.mk_le_of_surjective (f := g) fun i => ?_
  have hi : i ∈ Submodule.span A' {T} := hspan ▸ Submodule.mem_top
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hi
  refine ⟨φ b, Subtype.ext ?_⟩
  have hd : Function.surjInv hsurj (φ b) - b ∈ I := by
    rw [hI, RingHom.mem_ker, map_sub, Function.surjInv_eq hsurj, sub_self]
  have hz := mul_eq_zero_of_mem_maximalIdeal_of_mem_ker φ hlen
    (ker_le_maximalIdeal_of_surjective φ hsurj hd) htI
  rw [sub_mul, sub_eq_zero] at hz
  change Function.surjInv hsurj (φ b) * t = (i : A')
  rw [hz, ← hb]
  rfl

end SmallExtension

/-! ### Lifting a deformation along a small extension -/

/-- A functor carries a morphism conjugated by two identifications to its image conjugated by the
image identifications. -/
theorem map_eqToHom_comp_comp_eqToHom {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {P Q P' Q' : C} (X : P ⟶ Q) (e : Q = Q') (e' : P' = P) :
    G.map (eqToHom e' ≫ X ≫ eqToHom e) =
      eqToHom (congrArg G.obj e') ≫ G.map X ≫ eqToHom (congrArg G.obj e) := by
  subst e e'
  simp

/-- A square `X ≫ eqToHom e = eqToHom e' ≫ Z` exhibits `Z` as `X` conjugated by the two
identifications. -/
theorem eqToHom_comp_comp_eqToHom_eq_of_comp_eqToHom {C : Type*} [Category C] {P Q P' Q' : C}
    (X : P ⟶ Q) (Z : P' ⟶ Q') (e : Q = Q') (e' : P = P')
    (h : X ≫ eqToHom e = eqToHom e' ≫ Z) : eqToHom e'.symm ≫ X ≫ eqToHom e = Z := by
  subst e e'
  simpa using h

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {x₀ : CartesianProperFlatSpaces B S hS}
  {hx₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

/-- **The square-zero thickening of Situation 07YX attached to a surjection `A' → A` of `𝒞_Λ`**
with square-zero kernel, whose spectrum lies in the site, over the base of a deformation over `A`;
the structure morphism of `Spec A'` is the one through the chart `Spec Λ ⟶ S`. -/
def deformationThickening
    (a : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀
      hx₀) {A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A' ⟶ a.algebra)
    (hsurj : Function.Surjective f.hom) (hsq : RingHom.ker f.hom.toRingHom ^ 2 = ⊥)
    (hA' : B.Contains (Spec (.of A'))) :
    SquareZeroThickening a.algebra B S hS a.toS a.contains A' :=
  letI : Algebra A' a.algebra := f.hom.toRingHom.toAlgebra
  haveI : IsScalarTower Λ A' a.algebra :=
    IsScalarTower.of_algebraMap_eq fun c => (f.hom.commutes c).symm
  squareZeroThickeningOfTower Λ a.algebra B S hS a.toS a.contains iΛ rfl A' hA' hsurj hsq

section Lift

variable (a : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
    x₀ hx₀) {A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A' ⟶ a.algebra)
  (hsurj : Function.Surjective f.hom) (hsq : RingHom.ker f.hom.toRingHom ^ 2 = ⊥)
  (hA' : B.Contains (Spec (.of A')))
  (y : (Under.post (cartesianProperFlatProjection B S hS)).Fiber
    (Under.mk (eqToHom a.obj_eq ≫ (deformationThickening a f hsurj hsq hA').arrow)))

/-- The object a lift of `a` along the thickening of `A' → A` lives on lies over `Spec A'`. -/
theorem lift_base :
    (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj y.1.right =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ iΛ) :=
  congrArg (Over.post B.inclusion).obj (congrArg Under.right y.2)

/-- The arrow of a lift of `a` along the thickening of `A' → A` lies over `Spec A ⟶ Spec A'`. -/
theorem lift_hom_base :
    eqToHom (congrArg Over.left a.base).symm ≫
      ((cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).map y.1.hom).left ≫
        eqToHom (congrArg Over.left (lift_base a f hsurj hsq hA' y)) =
      Spec.map (CommRingCat.ofHom f.hom.toRingHom) := by
  have hw : (cartesianProperFlatProjection B S hS).map y.1.hom ≫
      eqToHom (congrArg Under.right y.2) =
        eqToHom a.obj_eq ≫ (deformationThickening a f hsurj hsq hA').arrow := by
    have h := Under.w (eqToHom y.2)
    simp only [Under.eqToHom_right] at h
    exact h
  have hc := eqToHom_comp_comp_eqToHom_eq_of_comp_eqToHom _ _ _ _ hw
  have hG := (map_eqToHom_comp_comp_eqToHom (Over.forget _ ⋙ B.inclusion) _ _ _).symm.trans
    (congrArg (Over.forget _ ⋙ B.inclusion).map hc)
  exact hG.trans (deformationThickening a f hsurj hsq hA').arrow_spec

/-- **A lift of `a` along the thickening of `A' → A`, read as a deformation over `A'`.** Its
arrow is the arrow of `a` followed by the lift. -/
def liftDeformation :
    DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀ hx₀ where
  algebra := A'
  point := y.1.right
  arrow := a.arrow ≫ y.1.hom
  base := lift_base a f hsurj hsq hA' y
  arrow_base := by
    have h1 := a.arrow_base
    have h2 := lift_hom_base a f hsurj hsq hA' y
    have hres : Spec.map (CommRingCat.ofHom (residueMap A')) =
        Spec.map (CommRingCat.ofHom (residueMap a.algebra)) ≫
          Spec.map (CommRingCat.ofHom f.hom.toRingHom) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← residueMap_comp f]
    rw [hres, ← h1, ← h2, Functor.map_comp, Over.comp_left]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The morphism of deformations from the lift to `a`, over `A' → A`. -/
def liftDeformationMorphism :
    DeformationMorphism iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀ hx₀
      (liftDeformation a f hsurj hsq hA' y) a where
  ringHom := f
  arrow := y.1.hom
  triangle := rfl
  arrow_base := lift_hom_base a f hsurj hsq hA' y

end Lift

/-- **A lift exists when `T²(I) = 0`**: the obstruction class of `x` along `D` lies in
`T²(I) = Ext²_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A I)`, `I = D.kernel` (Stacks 08V5). The structure of derived
category is an implicit argument, so that it is read off the hypothesis. -/
theorem nonempty_lift_of_subsingleton_cotangentExtTwo {A : Type u} [CommRing A]
    {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
    (x : CartesianProperFlatSpaces B S hS)
    (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)
    {A₁ : Type u} [CommRing A₁] (D : SquareZeroThickening A B S hS toS hA A₁)
    {_ : HasDerivedCategory.{t} (Space.modelModules x.obj.obj.left)}
    (hsub : Subsingleton ((Space.cotangentExtTwo (Space.ProperFlatLift.chartStructureMap x hx)
      (Space.ProperFlatLift.chartBaseRingHom x hx)).obj D.kernel)) :
    Nonempty ((Under.post (cartesianProperFlatProjection B S hS)).Fiber
      (Under.mk (eqToHom hx ≫ D.arrow))) :=
  (Space.ProperFlatLift.nonempty_lift_iff_chartObstruction_eq_zero x hx D).mpr
    (Subsingleton.elim _ _)

/-- **A deformation lifts along a small extension when the obstruction groups vanish.** For a
deformation `a` over `A` and a small extension `f : A' → A` of `𝒞_Λ`, `f` is a square-zero
thickening of Situation 07YX whose kernel `I` is killed by `𝔪_A`, so the obstruction class
(Stacks 08V5) of `a` along it lies in `T²(I) = 0`; hence `a` lifts, and the lift is a
deformation over `A'` with a morphism to `a` over `f`. -/
theorem exists_deformationMorphism_of_isSmallExtension
    (h : DeformationObstructionGroupsVanish (B := B) (S := S) (hS := hS) (iΛ := iΛ) (x₀ := x₀)
      (hx₀ := hx₀))
    (a : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀
      hx₀) {A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A' ⟶ a.algebra)
    (hf : IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom)) :
    ∃ (a' : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
        x₀ hx₀) (hA : a'.algebra = A')
      (m : DeformationMorphism iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
        x₀ hx₀ a' a), m.ringHom = eqToHom hA ≫ f := by
  obtain ⟨-, -, -, -, hsurj, hlen⟩ := hf
  have hsurj' : Function.Surjective f.hom.toRingHom := hsurj
  have hsq : RingHom.ker f.hom.toRingHom ^ 2 = ⊥ :=
    (IsSmallExtension.isSquareZeroSurjection _
      ⟨inferInstance, inferInstance, inferInstance, inferInstance, hsurj, hlen⟩).2.2.2
  have hA' : B.Contains (Spec (.of A')) :=
    contains_spec_of_surjective_of_mk_ker_le B a.contains A' f.hom.toRingHom hsurj'
      ((mk_ker_le_of_length_eq_one f.hom.toRingHom hsurj' hlen).trans (le_max_right _ _))
  let D := deformationThickening a f hsurj hsq hA'
  have hlen' : Module.length A' (RingHom.ker f.hom.toRingHom) = 1 := hlen
  have hsub := h a D.kernel fun r hr i => by
    obtain ⟨r', rfl⟩ := hsurj' r
    have hr' : r' ∈ IsLocalRing.maximalIdeal A' := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
      exact fun hu => hr (hu.map f.hom.toRingHom)
    refine (Stacks.Smooth.kerModule_smul D.squareZeroSurjection.1 D.squareZeroSurjection.2 r'
      i).trans (Subtype.ext ?_)
    exact mul_eq_zero_of_mem_maximalIdeal_of_mem_ker f.hom.toRingHom hlen' hr' i.2
  obtain ⟨y⟩ := nonempty_lift_of_subsingleton_cotangentExtTwo a.point a.obj_eq D hsub
  exact ⟨liftDeformation a f hsurj hsq hA' y, rfl, liftDeformationMorphism a f hsurj hsq hA' y,
    (Category.id_comp f).symm⟩

/-- A morphism `g` lifting `f` along the identity functor is `f`, up to the identifications of
their endpoints. -/
theorem exists_eq_of_isHomLift_id {C : Type*} [Category C] {R T a b : C} {f : R ⟶ T}
    {g : a ⟶ b} (h : (𝟭 C).IsHomLift f g) :
    ∃ (hR : a = R) (hT : b = T), f = eqToHom hR.symm ≫ g ≫ eqToHom hT :=
  ⟨IsHomLift.domain_eq (𝟭 C) f g, IsHomLift.codomain_eq (𝟭 C) f g, IsHomLift.fac (𝟭 C) f g⟩

/-- A morphism lifting `f` along the identity functor, with the same endpoints, is `f`. -/
theorem eq_of_isHomLift_id {C : Type*} [Category C] {a b : C} {f g : a ⟶ b}
    (h : (𝟭 C).IsHomLift f g) : f = g := by
  obtain ⟨_, _, hfg⟩ := exists_eq_of_isHomLift_id h
  simpa using hfg

attribute [local instance] PredeformationConstruction.category

variable (B S hS iΛ x₀ hx₀) in
/-- **`𝓕_{𝒳,k,x₀}` is unobstructed when the obstruction groups of all deformations vanish.**
If `T²(I) = Ext²_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A I)` (Stacks 0D1P) is zero for every deformation
`x = (X ⟶ Spec A)` of `x₀` and every `A`-module `I` killed by `𝔪_A`, then the structure functor
of `𝓕_{𝒳,k,x₀}` to `𝒞_Λ` is smooth: by Stacks 06HH it suffices to lift along small extensions,
which `exists_deformationMorphism_of_isSmallExtension` does. -/
theorem isSmooth_baseProjection_predeformationCat_of_obstructionGroupsVanish
    (h : DeformationObstructionGroupsVanish (B := B) (S := S) (hS := hS) (iΛ := iΛ) (x₀ := x₀)
      (hx₀ := hx₀)) :
    IsSmooth (baseProjection (predeformationCat B S hS iΛ x₀ hx₀).projection) := by
  have hpre := predeformationCategory_isPredeformationCategory B hS iΛ
    (cartesianProperFlatProjection B S hS) x₀ hx₀
    (cartesianProperFlatProjection_isFiberedInGroupoids B S hS)
  refine isSmooth_of_lifts_smallExtensions hpre.cofibered isCofiberedInGroupoids_id _ ?_
  intro A' A f hf y a g hg
  obtain ⟨hy, hA, -⟩ := exists_eq_of_isHomLift_id hg
  subst hy hA
  have hfg : f = g := eq_of_isHomLift_id hg
  subst hfg
  obtain ⟨a', hA', m, hm⟩ := exists_deformationMorphism_of_isSmallExtension h a f hf
  subst hA'
  have hpm : (predeformationCat B S hS iΛ x₀ hx₀).projection.map m = f :=
    hm.trans (Category.id_comp f)
  have hlift : (BasedCategory.ofFunctor (predeformationCat B S hS iΛ x₀ hx₀).projection).p.IsHomLift
      f m := by
    have hmap := IsHomLift.map
      (BasedCategory.ofFunctor (predeformationCat B S hS iΛ x₀ hx₀).projection).p m
    rwa [show (BasedCategory.ofFunctor (predeformationCat B S hS iΛ x₀ hx₀).projection).p.map m =
      f from hpm] at hmap
  exact ⟨a', m, 𝟙 a'.algebra, hlift, IsHomLift.id rfl, hpm.trans (Category.id_comp f).symm⟩

end AlgebraicGeometry.ProperFlatSpaceDeformation

end
