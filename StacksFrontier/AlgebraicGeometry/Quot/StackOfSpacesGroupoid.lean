module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.VaryingBase.FiniteTypeEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FinitePresentationFpqcLocality
public import StacksFrontier.CategoryTheory.Sites.Stack.CartesianFullSubcategory

/-!
# The stacks of finite-type and of proper flat families of algebraic spaces (Stacks 0D1G)

Stacks 0D1G asserts that the category `Spaces'_{ft}` of finite-type families of algebraic spaces
over varying base schemes, with cartesian squares as morphisms, is a stack in groupoids over the
big fppf site, and that the same holds for its full subcategory `Spaces'_{fp, flat, proper}`. The
two categories are `AlgebraicGeometry.CartesianFiniteTypeSpaces` and
`AlgebraicGeometry.CartesianProperFlatSpaces` of Stacks 0D1D and 0D1E.

## Main results

* `AlgebraicGeometry.cartesianFiniteTypeProjection_isStackInGroupoids`: **Stacks 0D1G**, the
  finite-type families (unregistered).
* `AlgebraicGeometry.cartesianProperFlatProjection_isStackInGroupoids`: **Stacks 0D1G**, the
  finitely presented, flat and proper families (unregistered, likewise).
* `AlgebraicGeometry.SpacesDescent.of_forall_isPullback_of_mem_topology`: a property of morphisms
  of algebraic spaces which is stable under base change and fppf local on the target holds for a
  morphism to a scheme as soon as it holds for its base changes along the members of a family
  generating a covering sieve of the big fppf site.
* `AlgebraicGeometry.SpacesDescent.hasRelativeDimensionLE_of_forall_isPullback_of_mem_topology`:
  the same for the bound on the relative dimension of Stacks 06LR, which is Stacks 04NS part (1)
  read on points.

## Implementation notes

The source deduces both assertions from the slogan that fppf descent data of algebraic spaces are
effective: for `Spaces'_{ft}` this is Stacks 04UD, and for `Spaces'_{fp, flat, proper}` it is
that and the fppf locality on the base of the three conditions, Stacks 041V, 041W and 0422. Both
are instances of `CategoryTheory.Functor.isStackInGroupoids_wideSubcategory_of_isStack_restrict`,
applied to the comma category of all algebraic spaces over varying base schemes with the full
subcategory of finite-type families, which is a stack by Stacks 04UD
(`AlgebraicGeometry.finiteTypeSpacesProjection_isStack_of_bootstrap`). What is proved here is the
input that lemma asks for: base change stability of the three conditions, and their locality
along a covering sieve, both read through the cartesian squares that strongly cartesian morphisms
of the comma category are (Stacks 04U9).

The source works over `Spec(ℤ)`; as elsewhere in this chapter the base here is the big fppf site
of an arbitrary scheme `S`, and `S = Spec(ℤ)` recovers the source's statement.

## References

* [Stacks Project, Tag 0D1G](https://stacks.math.columbia.edu/tag/0D1G)
* [Stacks Project, Tag 04UD](https://stacks.math.columbia.edu/tag/04UD)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.SpacesDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A pullback square of algebraic space presheaves is a pullback square in `AlgebraicSpaces`. -/
private theorem isPullback_homMk {A F Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : IsAlgebraicSpace B S hS A) (hF : IsAlgebraicSpace B S hS F)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    {a : A ⟶ F} {b : A ⟶ Y} {c : F ⟶ Z} {d : Y ⟶ Z} (hsq : IsPullback a b c d) :
    IsPullback (ObjectProperty.homMk a : (⟨A, hA⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩)
      (ObjectProperty.homMk b : (⟨A, hA⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk c : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)
      (ObjectProperty.homMk d) :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι _) hsq

/-- Pasting the base change of `q` along `h : W ⟶ V` with a pullback square over `f : V ⟶ U`
gives a pullback square over `g = h ≫ f`. -/
private theorem isPullback_pullback_fst_comp {U V W : BigFppfOver B S hS}
    {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : F ⟶ yoneda.obj U} {ζ : X ⟶ F}
    {q : X ⟶ yoneda.obj V} {f : V ⟶ U} (hsq : IsPullback ζ q π (yoneda.map f))
    (h : W ⟶ V) (g : W ⟶ U) (hh : h ≫ f = g) :
    IsPullback (pullback.fst q (yoneda.map h) ≫ ζ) (pullback.snd q (yoneda.map h)) π
      (yoneda.map g) := by
  rw [← hh, Functor.map_comp]
  exact (IsPullback.of_hasPullback _ _).paste_horiz hsq

/-- **A property of morphisms of algebraic spaces which is fppf local on the target, read along a
covering family of schemes.** A morphism `π : F ⟶ h_U` of algebraic spaces whose base changes along
the members of a flat, locally finitely presented, jointly surjective family `{g k : W k ⟶ U}` have
a property `R` local on the target for the fppf topology has `R`. This is the shape of
`AlgebraicGeometry.SpacesDescent.isFiniteType_of_forall_isPullback` for an arbitrary such `R`. -/
theorem of_forall_isPullback_of_isLocalAtTarget
    (R : MorphismProperty (AlgebraicSpaces B S hS))
    [R.IsLocalAtTarget (Space.Topology.precoverage.{u, v} .fppf B S hS)]
    {U : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (π : F ⟶ yoneda.obj U) {K : Type v}
    (W : K → BigFppfOver B S hS) (g : ∀ k, W k ⟶ U)
    (hflat : ∀ k, Flat ((BigFppfOver.toScheme B S hS).map (g k)))
    (hlfp : ∀ k, LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (g k)))
    (hsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj U, ∃ k,
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g k)))
    (X : K → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : ∀ k, IsAlgebraicSpace B S hS (X k))
    (ζ : ∀ k, X k ⟶ F) (q : ∀ k, X k ⟶ yoneda.obj (W k))
    (hsq : ∀ k, IsPullback (ζ k) (q k) π (yoneda.map (g k)))
    (hR : ∀ k, R (ObjectProperty.homMk (q k) :
      (⟨X k, hX k⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨yoneda.obj (W k), isAlgebraicSpace_yoneda B S hS (W k)⟩)) :
    R (ObjectProperty.homMk π :
      (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) := by
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  let Ya : AlgebraicSpaces B S hS := ⟨yoneda.obj U, hU⟩
  let Fa : AlgebraicSpaces B S hS := ⟨F, hF⟩
  let Wa : K → AlgebraicSpaces B S hS := fun k =>
    ⟨yoneda.obj (W k), isAlgebraicSpace_yoneda B S hS (W k)⟩
  let ga : ∀ k, Wa k ⟶ Ya := fun k => ObjectProperty.homMk (yoneda.map (g k))
  have hcov : Presieve.ofArrows Wa ga ∈
      (Space.Topology.precoverage.{u, v} .fppf B S hS).coverings Ya :=
    ⟨K, Wa, ga, rfl, hU, fun k => isAlgebraicSpace_yoneda B S hS (W k),
      Space.isFppfCovering_yoneda_map B S hS W g hflat hlfp hsurj⟩
  refine (MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd
    (P := R) hcov (f := (ObjectProperty.homMk π : Fa ⟶ Ya))).2 ?_
  rintro Uo h _ ⟨k⟩
  have h₂ := isPullback_homMk (hX k) hF (isAlgebraicSpace_yoneda B S hS (W k)) hU (hsq k)
  let e := h₂.isoIsPullback _ _
    (IsPullback.of_hasPullback (ObjectProperty.homMk π : Fa ⟶ Ya) (ga k))
  refine (MorphismProperty.cancel_left_of_respectsIso R e.hom _).1 ?_
  rw [IsPullback.isoIsPullback_hom_snd]
  exact hR k

/-- A family generating a covering sieve of the big fppf site of `S` is refined by a flat, locally
finitely presented and jointly surjective family, each member of which factors through a member of
the given family. -/
theorem exists_refinement_of_mem_topology {U : BigFppfOver B S hS} {ι : Type*}
    {V : ι → BigFppfOver B S hS} {f : ∀ i, V i ⟶ U}
    (hcov : Sieve.generate (Presieve.ofArrows V f) ∈ BigFppfOver.topology B S hS U) :
    ∃ (K : Type (u + 1)) (W : K → BigFppfOver B S hS) (g : ∀ k, W k ⟶ U) (κ : K → ι)
      (h : ∀ k, W k ⟶ V (κ k)), (∀ k, h k ≫ f (κ k) = g k) ∧
      (∀ k, Flat ((BigFppfOver.toScheme B S hS).map (g k))) ∧
      (∀ k, LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (g k))) ∧
      (∀ x : (BigFppfOver.toScheme B S hS).obj U, ∃ k,
        x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g k))) := by
  obtain ⟨K, Wb, m, hmR, hflat, hlfp, hsurj⟩ := exists_family_of_mem_topology B S hS hcov
  have hfac : ∀ k, ∃ (i : ι) (h : (Over.mk (m k ≫ U.hom) : BigFppfOver B S hS) ⟶ V i),
      h ≫ f i = Over.homMk (m k) := by
    intro k
    obtain ⟨Y, h, gk, ⟨i⟩, hcomp⟩ := hmR k
    exact ⟨i, h, hcomp⟩
  choose κ h hh using hfac
  exact ⟨K, fun k => Over.mk (m k ≫ U.hom), fun k => Over.homMk (m k), κ, h, hh, hflat, hlfp,
    hsurj⟩

/-- **A property of morphisms of algebraic spaces which is stable under base change and fppf local
on the target, read along a covering sieve.** A morphism `π : F ⟶ h_U` of algebraic spaces has
`R` as soon as, for each member `f i : V i ⟶ U` of a family generating a covering sieve of the big
fppf site of `S`, some base change of `π` along `f i` has `R`. -/
theorem of_forall_isPullback_of_mem_topology
    (R : MorphismProperty (AlgebraicSpaces B S hS))
    [R.IsLocalAtTarget (Space.Topology.precoverage.{u, u + 1} .fppf B S hS)]
    [R.IsStableUnderBaseChange]
    {U : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (π : F ⟶ yoneda.obj U) {ι : Type*}
    (V : ι → BigFppfOver B S hS) (f : ∀ i, V i ⟶ U)
    (hcov : Sieve.generate (Presieve.ofArrows V f) ∈ BigFppfOver.topology B S hS U)
    (X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : ∀ i, IsAlgebraicSpace B S hS (X i))
    (ζ : ∀ i, X i ⟶ F) (q : ∀ i, X i ⟶ yoneda.obj (V i))
    (hsq : ∀ i, IsPullback (ζ i) (q i) π (yoneda.map (f i)))
    (hR : ∀ i, R (ObjectProperty.homMk (q i) :
      (⟨X i, hX i⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨yoneda.obj (V i), isAlgebraicSpace_yoneda B S hS (V i)⟩)) :
    R (ObjectProperty.homMk π :
      (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) := by
  obtain ⟨K, W, g, κ, h, hh, hflat, hlfp, hsurj⟩ := exists_refinement_of_mem_topology hcov
  have hXk : ∀ k, IsAlgebraicSpace B S hS (pullback (q (κ k)) (yoneda.map (h k))) := fun k =>
    isAlgebraicSpace_pullback B S hS _ _ (hX (κ k)) (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS _)
  refine of_forall_isPullback_of_isLocalAtTarget R hF π W g hflat hlfp hsurj
    (fun k => pullback (q (κ k)) (yoneda.map (h k))) hXk
    (fun k => pullback.fst _ _ ≫ ζ (κ k)) (fun k => pullback.snd _ _) (fun k => ?_) (fun k => ?_)
  · exact isPullback_pullback_fst_comp (hsq (κ k)) (h k) (g k) (hh k)
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_homMk (hXk k) (hX (κ k)) (isAlgebraicSpace_yoneda B S hS _)
        (isAlgebraicSpace_yoneda B S hS _) (IsPullback.of_hasPullback _ _)) (hR (κ k))

/-- **A bound on the relative dimension is fppf local on the base, read along a covering family of
schemes.** Let `π : F ⟶ h_U` be a morphism of algebraic spaces which is locally of finite type, and
let `{g k : W k ⟶ U}` be a jointly surjective family whose base changes of `π` have relative
dimension at most `n`. Then `π` has relative dimension at most `n`.

Every point of `F` lifts to a point of one of the base changes, by Stacks 03H4 applied to a point
of `W k` over its image in `U`, and the relative dimension at the lift is the relative dimension at
the point by Stacks 04NS part (1). -/
theorem hasRelativeDimensionLE_of_forall_isPullback (n : ℕ) {U : BigFppfOver B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (π : F ⟶ yoneda.obj U) (hπ : Space.IsLocallyOfFiniteType B S hS π) {K : Type v}
    (W : K → BigFppfOver B S hS) (g : ∀ k, W k ⟶ U)
    (hsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj U, ∃ k,
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g k)))
    (X : K → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : ∀ k, IsAlgebraicSpace B S hS (X k))
    (ζ : ∀ k, X k ⟶ F) (q : ∀ k, X k ⟶ yoneda.obj (W k))
    (hsq : ∀ k, IsPullback (ζ k) (q k) π (yoneda.map (g k)))
    (hrel : ∀ k, Space.HasRelativeDimensionLE n B S hS (q k)) :
    Space.HasRelativeDimensionLE n B S hS π := by
  intro x
  have hcover := Space.jointlySurjective_yoneda_of_scheme B S hS W g hsurj
  have hy : Space.pointsMap B S hS F π x ∈
      ⋃ k, Set.range (Space.pointsMap B S hS (yoneda.obj (W k)) (yoneda.map (g k))) := by
    rw [hcover]
    exact Set.mem_univ _
  obtain ⟨k, z, hz⟩ := Set.mem_iUnion.1 hy
  obtain ⟨x', hx', -⟩ := Space.exists_point_of_isPullback B S hS
    (isPullback_homMk (hX k) hF (isAlgebraicSpace_yoneda B S hS (W k))
      (isAlgebraicSpace_yoneda B S hS U) (hsq k)) x z hz.symm
  obtain ⟨e, he, hAt⟩ := hrel k x'
  refine ⟨e, he, ?_⟩
  rw [← hx']
  exact (Space.hasRelativeDimensionAt_iff_of_isPullback' B S hS e (hsq k).flip hF
    (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS (W k)) hπ x').1 hAt

/-- **A bound on the relative dimension is fppf local on the base, read along a covering
sieve.** A morphism `π : F ⟶ h_U` of algebraic spaces which is locally of finite type has relative
dimension at most `n` as soon as, for each member `f i : V i ⟶ U` of a family generating a
covering sieve of the big fppf site of `S`, some base change of `π` along `f i` has relative
dimension at most `n`. -/
theorem hasRelativeDimensionLE_of_forall_isPullback_of_mem_topology (n : ℕ)
    {U : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (π : F ⟶ yoneda.obj U)
    (hπ : Space.IsLocallyOfFiniteType B S hS π) {ι : Type*}
    (V : ι → BigFppfOver B S hS) (f : ∀ i, V i ⟶ U)
    (hcov : Sieve.generate (Presieve.ofArrows V f) ∈ BigFppfOver.topology B S hS U)
    (X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : ∀ i, IsAlgebraicSpace B S hS (X i))
    (ζ : ∀ i, X i ⟶ F) (q : ∀ i, X i ⟶ yoneda.obj (V i))
    (hsq : ∀ i, IsPullback (ζ i) (q i) π (yoneda.map (f i)))
    (hq : ∀ i, Space.IsLocallyOfFiniteType B S hS (q i))
    (hrel : ∀ i, Space.HasRelativeDimensionLE n B S hS (q i)) :
    Space.HasRelativeDimensionLE n B S hS π := by
  obtain ⟨K, W, g, κ, h, hh, -, -, hsurj⟩ := exists_refinement_of_mem_topology hcov
  have hXk : ∀ k, IsAlgebraicSpace B S hS (pullback (q (κ k)) (yoneda.map (h k))) := fun k =>
    isAlgebraicSpace_pullback B S hS _ _ (hX (κ k)) (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS _)
  refine hasRelativeDimensionLE_of_forall_isPullback n hF π hπ W g hsurj
    (fun k => pullback (q (κ k)) (yoneda.map (h k))) hXk
    (fun k => pullback.fst _ _ ≫ ζ (κ k)) (fun k => pullback.snd _ _) (fun k => ?_) (fun k => ?_)
  · exact isPullback_pullback_fst_comp (hsq (κ k)) (h k) (g k) (hh k)
  · intro x
    obtain ⟨e, he, hAt⟩ := hrel (κ k) (Space.pointsMap B S hS _ (pullback.fst _ _) x)
    exact ⟨e, he, (Space.hasRelativeDimensionAt_iff_of_isPullback' B S hS e
      (IsPullback.of_hasPullback (q (κ k)) (yoneda.map (h k))).flip (hX (κ k))
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) (hq (κ k)) x).2 hAt⟩

end AlgebraicGeometry.SpacesDescent

namespace AlgebraicGeometry

open SpacesDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of the comma category of Stacks 04U8 which is strongly cartesian over some
morphism of the base exhibits the structure morphism of its source as a base change of the
structure morphism of its target, along its own morphism of base schemes. -/
theorem isPullback_hom_of_isStronglyCartesian_over {V U : BigFppfOver B S hS}
    {y x : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (f : V ⟶ U) (φ : y ⟶ x) (h : (spacesProjection B S hS).IsStronglyCartesian f φ) :
    IsPullback y.hom φ.left.hom (yoneda.map φ.right) x.hom :=
  isPullback_hom_of_isStronglyCartesian B S hS φ
    (Functor.StronglyCartesianWide.mem_of_isStronglyCartesian φ f h)

/-- The data of the locality condition of
`CategoryTheory.Functor.isStackInGroupoids_wideSubcategory_of_isStack_restrict` for the comma
category of Stacks 04U8, read as cartesian squares: if an algebraic space `x` over `U` receives,
along each member of a family generating a covering sieve of `U`, a strongly cartesian morphism
from an object satisfying `T`, then the bases of those morphisms generate a covering sieve of the
base of `x`, and over each of them the structure morphism of `x` has a base change satisfying
`T`. -/
theorem exists_isPullback_of_isStronglyCartesian {U : BigFppfOver B S hS} {ι : Type*}
    (Uᵢ : ι → BigFppfOver B S hS) (fᵢ : ∀ i, Uᵢ i ⟶ U)
    (hgen : Sieve.generate (Presieve.ofArrows Uᵢ fᵢ) ∈ BigFppfOver.topology B S hS U)
    (T : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop)
    (x : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hx : x.right = U)
    (h : ∀ i, ∃ (y : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) (φ : y ⟶ x),
        (spacesProjection B S hS).IsStronglyCartesian (fᵢ i) φ ∧ T y) :
    ∃ (y : ι → Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) (φ : ∀ i, y i ⟶ x),
      Sieve.generate (Presieve.ofArrows (fun i => (y i).right) (fun i => (φ i).right)) ∈
        BigFppfOver.topology B S hS x.right ∧
      (∀ i, IsPullback (φ i).left.hom (y i).hom x.hom (yoneda.map (φ i).right)) ∧
      ∀ i, T (y i) := by
  subst hx
  choose y φ hsc hT using h
  refine ⟨y, φ, ?_, fun i => (isPullback_hom_of_isStronglyCartesian_over B S hS _ _
    (hsc i)).flip, hT⟩
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hgen
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨i⟩
  have hV : (y i).right = Uᵢ i := IsHomLift.domain_eq (spacesProjection B S hS) (fᵢ i) (φ i)
  refine ⟨_, eqToHom hV.symm, (φ i).right, ⟨i⟩, ?_⟩
  have hfac := IsHomLift.fac (spacesProjection B S hS) (fᵢ i) (φ i)
  simp only [eqToHom_refl, Category.comp_id] at hfac
  rw [hfac]
  rfl

/-- **Condition (1) of Stacks 04TU for the three conditions of Stacks 0D1D, read plainly.** The
source of a strongly cartesian morphism whose target is of finite presentation, flat and proper
over its base is of finite presentation, flat and proper over its base. -/
theorem isProperFlatSpace_of_isStronglyCartesian {V U : BigFppfOver B S hS}
    {y x : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (f : V ⟶ U) (φ : y ⟶ x) (h : (spacesProjection B S hS).IsStronglyCartesian f φ)
    (hx : isProperFlatSpace B S hS x) : isProperFlatSpace B S hS y := by
  have hsq := isPullback_commaHomAsSpaceMap_of_isStronglyCartesian B S hS φ
    (Functor.StronglyCartesianWide.mem_of_isStronglyCartesian φ f h)
  exact ⟨(Space.isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hsq hx.1,
    (Space.isFlat_isStableUnderBaseChange B S hS).of_isPullback hsq hx.2.1,
    (Space.isProper_isStableUnderBaseChange B S hS).of_isPullback hsq hx.2.2⟩

/-- **Condition (3) of Stacks 04TU for the three conditions of Stacks 0D1D.** Being of finite
presentation, flat and proper over the base is fppf local on the base: Stacks 041V, 041W and
0422, read along a covering sieve through cartesian squares. -/
theorem isProperFlatSpace_of_forall_isPullback {ι : Type*}
    (x : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (y : ι → Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) (φ : ∀ i, y i ⟶ x)
    (hcov : Sieve.generate (Presieve.ofArrows (fun i => (y i).right) (fun i => (φ i).right)) ∈
      BigFppfOver.topology B S hS x.right)
    (hsq : ∀ i, IsPullback (φ i).left.hom (y i).hom x.hom (yoneda.map (φ i).right))
    (hy : ∀ i, isProperFlatSpace B S hS (y i)) : isProperFlatSpace B S hS x := by
  have : MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => Space.IsFinitePresentation B S hS f.hom)
      (Space.Topology.precoverage.{u, u + 1} .fppf B S hS) :=
    (Space.finitePresentation_isLocalAtTarget_fpqc.{u, u + 1} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u + 1} B S hS)
  have : MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => Space.IsFlat B S hS f.hom)
      (Space.Topology.precoverage.{u, u + 1} .fppf B S hS) :=
    (Space.isFlat_isLocalAtTarget_fpqc.{u, u + 1} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u + 1} B S hS)
  have : MorphismProperty.IsLocalAtTarget (Space.properProperty B S hS)
      (Space.Topology.precoverage.{u, u + 1} .fppf B S hS) :=
    Space.proper_isLocalAtTarget_fppf.{u, u + 1} B S hS
  have := Space.isFinitePresentation_isStableUnderBaseChange B S hS
  have := Space.isFlat_isStableUnderBaseChange B S hS
  have := Space.isProper_isStableUnderBaseChange B S hS
  exact ⟨of_forall_isPullback_of_mem_topology
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => Space.IsFinitePresentation B S hS f.hom)
      x.left.property x.hom _ _ hcov _ (fun i => (y i).left.property) _ _ hsq
      (fun i => (hy i).1),
    of_forall_isPullback_of_mem_topology
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => Space.IsFlat B S hS f.hom)
      x.left.property x.hom _ _ hcov _ (fun i => (y i).left.property) _ _ hsq
      (fun i => (hy i).2.1),
    of_forall_isPullback_of_mem_topology (Space.properProperty B S hS)
      x.left.property x.hom _ _ hcov _ (fun i => (y i).left.property) _ _ hsq
      (fun i => (hy i).2.2)⟩

/-- **Stacks 0D1G**, the finite-type families. The category `Spaces'_{ft}` of finite-type
algebraic spaces over varying base schemes, with cartesian squares as morphisms, is a stack in
groupoids over the big fppf site of `S`.

This is Stacks 04UD (`AlgebraicGeometry.finiteTypeSpacesProjection_isStack_of_bootstrap`) passed
to its category of cartesian morphisms, through
`CategoryTheory.Functor.isStackInGroupoids_wideSubcategory_of_isStack_restrict` with both
properties equal to finite typeness.

This proves Stacks 0D1G (its first sentence); the theorem is not registered here. -/
theorem cartesianFiniteTypeProjection_isStackInGroupoids :
    (cartesianFiniteTypeProjection B S hS).IsStackInGroupoids.{w}
      (BigFppfOver.topology B S hS) :=
  have := spacesProjection_isFibered B S hS
  Functor.isStackInGroupoids_wideSubcategory_of_isStack_restrict (spacesProjection B S hS)
    (isFiniteTypeSpace B S hS) (closedUnderStronglyCartesian_isFiniteTypeSpace B S hS)
    (isFiniteTypeSpace B S hS) le_rfl (BigFppfOver.topology B S hS)
    (finiteTypeSpacesProjection_isStack_of_bootstrap B S hS)
    (fun _ _ _ hy _ => hy) (fun _ _ _ _ _ hx _ => hx)

/-- **Stacks 0D1G**, the finitely presented, flat and proper families. The category
`Spaces'_{fp, flat, proper}` of algebraic spaces whose structure morphism is of finite
presentation, flat and proper over a varying base scheme, with cartesian squares as morphisms, is
a stack in groupoids over the big fppf site of `S`.

The three conditions are stable under base change
(`AlgebraicGeometry.isProperFlatSpace_of_isStronglyCartesian`) and fppf local on the base
(`AlgebraicGeometry.isProperFlatSpace_of_forall_isPullback`), so this is
`CategoryTheory.Functor.isStackInGroupoids_wideSubcategory_of_isStack_restrict` inside the stack of
finite-type families of Stacks 04UD.

This proves Stacks 0D1G (its second sentence); the theorem is not registered here. -/
theorem cartesianProperFlatProjection_isStackInGroupoids :
    (cartesianProperFlatProjection B S hS).IsStackInGroupoids.{w}
      (BigFppfOver.topology B S hS) :=
  have := spacesProjection_isFibered B S hS
  Functor.isStackInGroupoids_wideSubcategory_of_isStack_restrict (spacesProjection B S hS)
    (isFiniteTypeSpace B S hS) (closedUnderStronglyCartesian_isFiniteTypeSpace B S hS)
    (isProperFlatSpace B S hS) (isProperFlatSpace_le_isFiniteTypeSpace B S hS)
    (BigFppfOver.topology B S hS) (finiteTypeSpacesProjection_isStack_of_bootstrap B S hS)
    (fun f φ h _ hx => isProperFlatSpace_of_isStronglyCartesian B S hS f φ h hx)
    (fun Uᵢ fᵢ hgen x hx _ h => by
      obtain ⟨y, φ, hcov, hsq, hy⟩ := exists_isPullback_of_isStronglyCartesian B S hS Uᵢ fᵢ hgen
        (isProperFlatSpace B S hS) x hx fun i => by
          obtain ⟨y, φ, hφ, -, hy⟩ := h i
          exact ⟨y, φ, hφ, hy⟩
      exact isProperFlatSpace_of_forall_isPullback B S hS x y φ hcov hsq hy)

end AlgebraicGeometry
