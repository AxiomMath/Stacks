module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.RingTheory.HopkinsLevitzki
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationUnthickenedTarget
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.Deformation.Examples.Geometric.OpenSubschemes
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftTorsor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fibre automorphisms of a deformation of a scheme as self-maps of its total space

## Main definitions

* `Deformation.Examples.deformationFiberObj`: a deformation read as an object of the fibre of
  the projection to `𝒞_Λ` over its own base.
* `Deformation.Examples.fiberAutEquivSelfMaps`: the automorphism group of that fibre object is
  the set of invertible self-maps of the total space over the base fixing the special fibre.
* `Deformation.Examples.topSelfMapEquiv`: the self-maps of the top open of a scheme are the
  self-maps of the scheme.
* `Deformation.Examples.liftsOverBaseTopEquivSelfMaps`: the same set of self-maps, without the
  invertibility clause, is the set of global lifts of the identity of
  `Stacks.Thickenings.liftsOverBase`.
* `Deformation.Examples.liftDeformationDiagram`: a self-map of the total space over the base
  fixing the special fibre, read as a cartesian finite-order deformation of the identity.
* `Deformation.Examples.fiberAutEquivLiftsOverBaseTop`: the payoff, that the fibre automorphism
  group is the set of global lifts of the identity.

## Main results

* `Deformation.Examples.isIso_of_fixes_specialMap_over_base` and
  `Deformation.Examples.isIso_of_lift_id`: every lift of the identity is an isomorphism.
* `Deformation.Examples.residueSpecMap_isFiniteOrderThickening`: the closed point of the
  spectrum of an object of `𝒞_Λ` is a finite-order thickening.
* `Deformation.Examples.deformationSpecialMap_isThickening`: the special-fibre immersion of a
  deformation is a thickening.

* `Deformation.Examples.deformationFiberHom_base`: a morphism of the fibre acts as the identity
  on the base object of `𝒞_Λ`.
* `Deformation.Examples.preimage_top_ι_comp_specialMap_comp`: the restriction of the
  special-fibre immersion to the two top opens, read through `Scheme.topIso`, is the immersion.
* `Deformation.Examples.apply_eq_self_of_fixes_specialMap` and
  `Deformation.Examples.isHomeomorph_of_fixes_specialMap`: a self-map of the total space fixing
  the special-fibre immersion is the identity on points, hence a homeomorphism.
* `Deformation.Examples.fiberAutEquivSelfMaps_mul`: the identification of fibre automorphisms
  with self-maps takes the group law to composition.

## Implementation notes

The fibre of `Deformation.Examples.schemeDeformationCategoryProjection` over `P.base` is a
subtype of the deformation category, so `P` itself is an object of it with a `rfl` proof; this is
`Deformation.Examples.deformationFiberObj`, kept reducible so that the projection to the
underlying deformation is transparent to instance search and to `rw`. A morphism of that fibre
is a morphism of deformations lying over `𝟙 P.base`, and
`CategoryTheory.IsHomLift.eq_of_isHomLift` turns that lifting condition into the plain equation
`f.base = 𝟙 P.base`, which is what makes the `cartesian` field of such a morphism an honest
statement about `P.toBase`: it becomes `IsPullback e P.toBase P.toBase (𝟙 _)`, equivalent by
`CategoryTheory.IsPullback.of_horiz_isIso` to `e` being invertible over the base.

For `Deformation.Examples.liftsOverBaseTopEquivSelfMaps` the only work is the canonical
identification `AlgebraicGeometry.Scheme.topIso` of `(⊤ : P.scheme.Opens).toScheme` with
`P.scheme`, and the fact that the restriction of the special-fibre immersion to the two top
opens is that immersion read through the two copies of `Scheme.topIso`, which is
`AlgebraicGeometry.morphismRestrict_ι`. Both top-open inclusions are written as
`Scheme.topIso.hom` rather than as `Scheme.Opens.ι` — the two are definitionally equal, but
only the former lets the iso-cancellation lemmas fire by syntactic matching.

The invertibility of a lift of the identity is a genuine theorem rather than formal bookkeeping,
and it is where the cartesian square enters. For a general closed immersion `i : X ⟶ X'` with
square-zero kernel and a morphism `g' : X' ⟶ S`, a self-map `e` of `X'` over `S` with
`i ≫ e = i` need not be invertible: over `S = Spec k` with `X' = Spec k[x]/(x²)` and
`X = Spec k`, the map dual to `x ↦ 0` satisfies both equations and is not invertible. What rules
this out for a deformation is
`Deformation.Examples.SchemeDeformationCategory.specialCartesian`, which exhibits the special
fibre as a base change. The proof therefore does not argue on the structure sheaf at all: it
packages `e` and the identity of the special fibre as the two horizontal morphisms of a
cartesian finite-order deformation diagram and quotes [Stacks Project, Tag 06AG], that being an
isomorphism is invariant under such a deformation. The two cartesian squares of the diagram are
both `specialCartesian`, the flatness of the enlarged source is
`Deformation.Examples.SchemeDeformationCategory.flat`, and the base thickening is of finite
order because the maximal ideal of an Artinian local ring is nilpotent. In particular the
square-zero hypothesis on `P.specialMap.ker` is not used, and
`Deformation.Examples.isIso_of_fixes_specialMap_over_base` omits it;
`Deformation.Examples.isIso_of_lift_id` keeps it only to match the shape in which
[Stacks Project, Tag 0E3V] states the step.

`Deformation.Examples.isHomeomorph_of_fixes_specialMap` records separately that such a self-map
is the identity on points, which is immediate from surjectivity of the special-fibre immersion
and is what a stalkwise proof would have started from.

## References

* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 04FK](https://stacks.math.columbia.edu/tag/04FK)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

-- The general statement lives in `SchemeMorphismLiftTorsor`; it is used here only as an
-- instance, so it is enabled locally rather than duplicated.
attribute [local instance] isIso_preimage_top_ι

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X : Over (Spec (CommRingCat.of k))}

/-! ### The fibre of the projection to `𝒞_Λ` -/

/-- A deformation read as an object of the fibre of the projection to `𝒞_Λ` over its own
base object. -/
abbrev deformationFiberObj (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber P.base :=
  ⟨P, rfl⟩

/-- A morphism of the fibre over `P.base` acts as the identity on the base object: this is the
lifting condition read through `CategoryTheory.IsHomLift.eq_of_isHomLift`. -/
theorem deformationFiberHom_base {P : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (f : deformationFiberObj P ⟶ deformationFiberObj P) : f.val.base = 𝟙 P.base := by
  have : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).IsHomLift (𝟙 P.base)
      f.val := f.2
  exact (IsHomLift.eq_of_isHomLift (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X)
    (𝟙 P.base) f.val).symm

/-- A self-morphism of a deformation acting as the identity on the base object is a morphism of
the fibre over that object. -/
theorem deformationFiberHom_isHomLift {P : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (f : P ⟶ P) (hf : f.base = 𝟙 P.base) :
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).IsHomLift (𝟙 P.base) f := by
  refine IsHomLift.of_fac' _ (𝟙 P.base) f rfl rfl ?_
  simp only [eqToHom_refl, Category.comp_id]
  exact hf

/-! ### Fibre automorphisms as self-maps of the total space -/

/-- **An automorphism of a deformation in its fibre is exactly an invertible self-map of its
total space over the base fixing the special fibre.** The `cartesian` field of a morphism of
deformations lying over `𝟙 P.base` says that the square with `P.toBase` on both sides and the
identity underneath is cartesian, which for a morphism of schemes is invertibility together with
compatibility with `P.toBase`; the `special_compat` field is the compatibility with the
special-fibre immersion. -/
def fiberAutEquivSelfMaps (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    Aut (deformationFiberObj P) ≃
      { e : P.scheme ⟶ P.scheme //
        e ≫ P.toBase = P.toBase ∧ P.specialMap ≫ e = P.specialMap ∧ IsIso e } where
  toFun a := by
    refine ⟨a.asIso.hom.val.map, ?_, a.asIso.hom.val.special_compat, ?_⟩
    · have hb : a.asIso.hom.val.base = 𝟙 P.base := deformationFiberHom_base a.asIso.hom
      have hw : a.asIso.hom.val.map ≫ P.toBase = P.toBase ≫ baseSpecMap a.asIso.hom.val.base :=
        a.asIso.hom.val.cartesian.w
      rw [hb, baseSpecMap_id, Category.comp_id] at hw
      exact hw
    · refine ⟨a.asIso.inv.val.map, ?_, ?_⟩
      · exact congrArg (fun g : deformationFiberObj P ⟶ deformationFiberObj P ↦ g.val.map)
          a.asIso.inv_hom_id
      · exact congrArg (fun g : deformationFiberObj P ⟶ deformationFiberObj P ↦ g.val.map)
          a.asIso.hom_inv_id
  invFun := fun ⟨e, hbase, hspecial, hiso⟩ => by
    letI := hiso
    have hinvbase : CategoryTheory.inv e ≫ P.toBase = P.toBase := by
      calc CategoryTheory.inv e ≫ P.toBase = CategoryTheory.inv e ≫ e ≫ P.toBase := by
            rw [hbase]
        _ = P.toBase := by rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    have hinvspecial : P.specialMap ≫ CategoryTheory.inv e = P.specialMap := by
      calc P.specialMap ≫ CategoryTheory.inv e =
            (P.specialMap ≫ e) ≫ CategoryTheory.inv e := by rw [hspecial]
        _ = P.specialMap := by rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    let hom : P ⟶ P :=
      { base := 𝟙 P.base
        map := e
        cartesian := by
          rw [baseSpecMap_id]
          exact IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact hbase⟩
        special_compat := hspecial }
    let inv : P ⟶ P :=
      { base := 𝟙 P.base
        map := CategoryTheory.inv e
        cartesian := by
          rw [baseSpecMap_id]
          exact IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact hinvbase⟩
        special_compat := hinvspecial }
    refine .of
      { hom := ⟨hom, deformationFiberHom_isHomLift hom rfl⟩
        inv := ⟨inv, deformationFiberHom_isHomLift inv rfl⟩
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · refine Functor.Fiber.hom_ext (show hom ≫ inv = 𝟙 P from ?_)
      refine SchemeDeformationCategory.Hom.ext ?_ ?_
      · exact Category.comp_id _
      · exact IsIso.inv_hom_id e
    · refine Functor.Fiber.hom_ext (show inv ≫ hom = 𝟙 P from ?_)
      refine SchemeDeformationCategory.Hom.ext ?_ ?_
      · exact Category.comp_id _
      · exact IsIso.hom_inv_id e
  left_inv a := by
    refine Aut.ext (Iso.ext (Subtype.ext (SchemeDeformationCategory.Hom.ext ?_ rfl)))
    exact (deformationFiberHom_base a.asIso.hom).symm
  right_inv := by
    rintro ⟨e, hbase, hspecial, hiso⟩
    exact Subtype.ext rfl

/-! ### Self-maps of the total space as global lifts of the identity -/

/-- The self-maps of the top open of a scheme are the self-maps of the scheme, by conjugation
with `AlgebraicGeometry.Scheme.topIso`. -/
def topSelfMapEquiv (Y : Scheme.{u}) : ((⊤ : Y.Opens).toScheme ⟶ Y) ≃ (Y ⟶ Y) where
  toFun b := Y.topIso.inv ≫ b
  invFun e := (⊤ : Y.Opens).ι ≫ e
  left_inv b := by
    change (⊤ : Y.Opens).ι ≫ Y.topIso.inv ≫ b = b
    rw [← Category.assoc, Scheme.ι_toIso_inv, Category.id_comp]
  right_inv e := by
    change Y.topIso.inv ≫ (⊤ : Y.Opens).ι ≫ e = e
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]

/-- `Deformation.Examples.topSelfMapEquiv` is precomposition with the inverse of
`AlgebraicGeometry.Scheme.topIso`. -/
theorem topSelfMapEquiv_apply (Y : Scheme.{u}) (b : (⊤ : Y.Opens).toScheme ⟶ Y) :
    topSelfMapEquiv Y b = Y.topIso.inv ≫ b := rfl

/-- **The restriction of the special-fibre immersion of a deformation to the two top opens,
followed by a self-map of the top open of the total space, is the immersion followed by the
corresponding self-map of the total space.** This is `AlgebraicGeometry.morphismRestrict_ι`
transported through `AlgebraicGeometry.Scheme.topIso`, and it is the only computation behind
`Deformation.Examples.liftsOverBaseTopEquivSelfMaps`. -/
theorem preimage_top_ι_comp_specialMap_comp
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (b : (⊤ : P.scheme.Opens).toScheme ⟶ P.scheme) :
    (P.specialMap ⁻¹ᵁ (⊤ : P.scheme.Opens)).ι ≫ P.specialMap ≫ P.scheme.topIso.inv ≫ b =
      P.specialMap ∣_ (⊤ : P.scheme.Opens) ≫ b :=
  calc (P.specialMap ⁻¹ᵁ (⊤ : P.scheme.Opens)).ι ≫ P.specialMap ≫ P.scheme.topIso.inv ≫ b
      = ((P.specialMap ⁻¹ᵁ (⊤ : P.scheme.Opens)).ι ≫ P.specialMap) ≫
          (P.scheme.topIso.inv ≫ b) := by simp only [Category.assoc]
    _ = (P.specialMap ∣_ (⊤ : P.scheme.Opens) ≫ (⊤ : P.scheme.Opens).ι) ≫
          (P.scheme.topIso.inv ≫ b) := by rw [morphismRestrict_ι]
    _ = P.specialMap ∣_ (⊤ : P.scheme.Opens) ≫
          ((⊤ : P.scheme.Opens).ι ≫ P.scheme.topIso.inv) ≫ b := by simp only [Category.assoc]
    _ = P.specialMap ∣_ (⊤ : P.scheme.Opens) ≫ b := by
        rw [Scheme.ι_toIso_inv, Category.id_comp]

/-- **A self-map of the total space of a deformation over the base restricting to the identity
on the special fibre is exactly a global lift of the identity** in the sense of
`Stacks.Thickenings.liftsOverBase` at the top open. The two conditions match after the canonical
identification `Deformation.Examples.topSelfMapEquiv` of the self-maps of the top open of the
total space with the self-maps of the total space. -/
def liftsOverBaseTopEquivSelfMaps (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    Stacks.Thickenings.liftsOverBase P.specialMap P.specialMap P.toBase P.toBase
        (𝟙 X.left) ⊤ ≃
      { e : P.scheme ⟶ P.scheme //
        e ≫ P.toBase = P.toBase ∧ P.specialMap ≫ e = P.specialMap } := by
  refine (topSelfMapEquiv P.scheme).subtypeEquiv fun b => ?_
  rw [topSelfMapEquiv_apply]
  refine and_congr ?_ ?_
  · constructor
    · intro h
      rw [Category.assoc, h, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]
    · intro h
      have h2 : (⊤ : P.scheme.Opens).ι ≫ (P.scheme.topIso.inv ≫ b) ≫ P.toBase =
          (⊤ : P.scheme.Opens).ι ≫ P.toBase := by rw [h]
      rw [← Category.assoc, ← Category.assoc, Scheme.ι_toIso_inv, Category.id_comp] at h2
      exact h2
  · have hrhs : ((P.specialMap ⁻¹ᵁ (⊤ : P.scheme.Opens)).ι ≫ 𝟙 X.left) ≫ P.specialMap =
        (P.specialMap ⁻¹ᵁ (⊤ : P.scheme.Opens)).ι ≫ P.specialMap := by
      rw [Category.comp_id]
    rw [hrhs, ← preimage_top_ι_comp_specialMap_comp P b]
    exact cancel_epi ((P.specialMap ⁻¹ᵁ (⊤ : P.scheme.Opens)).ι)

/-! ### Self-maps fixing the special fibre are the identity on points -/

/-- **A self-map of the total space of a deformation fixing the special-fibre immersion is the
identity on points.** The immersion is surjective by
`Deformation.Examples.deformationSpecialMap_surjective`, so every point of the total space is
the image of a point of the special fibre, where the self-map is the identity by hypothesis. -/
theorem apply_eq_self_of_fixes_specialMap
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) (e : P.scheme ⟶ P.scheme)
    (he : P.specialMap ≫ e = P.specialMap) (x : P.scheme) : e.base x = x := by
  obtain ⟨y, hy⟩ := deformationSpecialMap_surjective P x
  have h := congrArg (fun m : X.left ⟶ P.scheme => m.base y) he
  rw [← hy]
  exact h

/-- **A self-map of the total space of a deformation fixing the special-fibre immersion is a
homeomorphism on points**, being the identity by
`Deformation.Examples.apply_eq_self_of_fixes_specialMap`. -/
theorem isHomeomorph_of_fixes_specialMap
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) (e : P.scheme ⟶ P.scheme)
    (he : P.specialMap ≫ e = P.specialMap) : IsHomeomorph e.base := by
  have h : (e.base : P.scheme → P.scheme) = id :=
    funext fun x => apply_eq_self_of_fixes_specialMap P e he x
  rw [h]
  exact ⟨continuous_id, IsOpenMap.id, Function.bijective_id⟩

/-! ### Every lift of the identity is an isomorphism -/

/-- **The closed point of the spectrum of an object of `𝒞_Λ` is a finite-order thickening.** The
maximal ideal of an Artinian local ring is nilpotent by Hopkins–Levitzki, and
`Stacks.Smooth.ker_pow_eq_bot_iff_of_isAffine` reads that off on the spectrum, the kernel ideal
sheaf of a morphism of affine schemes being the kernel on global sections. -/
theorem residueSpecMap_isFiniteOrderThickening (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Stacks.Thickenings.IsFiniteOrderThickening (residueSpecMap A) := by
  obtain ⟨N, hN⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance
  have := residueSpecMap_isClosedImmersion A
  refine ⟨inferInstance, N, ?_⟩
  refine (Stacks.Smooth.ker_pow_eq_bot_iff_of_isAffine (residueSpecMap A) (N + 1)).mpr ?_
  refine Stacks.Smooth.ker_specMap_appTop_pow_eq_bot
    (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ?_
  have hker : RingHom.ker (Deformation.Artin.residueMap A) = IsLocalRing.maximalIdeal A :=
    IsLocalRing.ker_eq_maximalIdeal _ (residueMap_surjective A)
  show RingHom.ker (Deformation.Artin.residueMap A) ^ (N + 1) = ⊥
  rw [hker]
  exact le_bot_iff.mp ((Ideal.pow_le_pow_right (Nat.le_succ N)).trans (le_of_eq hN))

/-- The special-fibre immersion of a deformation is a thickening: it is a closed immersion and
surjective on points. -/
@[sga "7 VI 4.1(d)" "partial"]
theorem deformationSpecialMap_isThickening
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    Stacks.Thickenings.IsThickening P.specialMap :=
  ⟨deformationSpecialMap_isClosedImmersion P, deformationSpecialMap_surjective P⟩

/-- The deformation of the identity of the special fibre presented by a self-map of the total
space over the base: the cartesian finite-order deformation diagram whose base thickening is the
closed point of the spectrum of `P.base`, whose two cartesian squares are both
`Deformation.Examples.SchemeDeformationCategory.specialCartesian`, and whose two horizontal
morphisms are the identity of the special fibre and the given self-map. -/
def liftDeformationDiagram (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (e : P.scheme ⟶ P.scheme) (he₁ : e ≫ P.toBase = P.toBase)
    (he₂ : P.specialMap ≫ e = P.specialMap) :
    Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.{u} where
  S := Spec (CommRingCat.of k)
  S' := baseSpec P.base
  iS := residueSpecMap P.base
  iS_finiteOrder := residueSpecMap_isFiniteOrderThickening P.base
  X := X.left
  X' := P.scheme
  iX := P.specialMap
  iX_thickening := deformationSpecialMap_isThickening P
  Y := X.left
  Y' := P.scheme
  iY := P.specialMap
  iY_thickening := deformationSpecialMap_isThickening P
  pX := X.hom
  pX' := P.toBase
  pY := X.hom
  pY' := P.toBase
  f := 𝟙 X.left
  f' := e
  f_over_S := Category.id_comp _
  f'_over_S' := he₁
  f_thickening_comm := (Category.id_comp _).trans he₂.symm
  X_cartesian := P.specialCartesian
  Y_cartesian := P.specialCartesian
  X'_flat := P.flat

/-- **A self-map of the total space of a deformation, over the base and fixing the special-fibre
immersion, is an isomorphism.** The self-map and the identity of the special fibre form the
cartesian finite-order deformation diagram
`Deformation.Examples.liftDeformationDiagram`, whose base thickening is the closed point of the
spectrum of `P.base` — of finite order because the maximal ideal of an Artinian local ring is
nilpotent — and whose enlarged source is flat over the enlarged base by
`Deformation.Examples.SchemeDeformationCategory.flat`. Being an isomorphism is invariant under
such a deformation, [Stacks Project, Tag 06AG], and the identity is one.

No square-zero hypothesis on `P.specialMap.ker` is needed: the base thickening is of finite
order for every object of `𝒞_Λ`. -/
@[sga "7 VI 4.1(a)" "special case"]
theorem isIso_of_fixes_specialMap_over_base
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) (e : P.scheme ⟶ P.scheme)
    (he₁ : e ≫ P.toBase = P.toBase) (he₂ : P.specialMap ≫ e = P.specialMap) : IsIso e :=
  (liftDeformationDiagram P e he₁ he₂).isIso_iff.mp
    (inferInstance : IsIso (𝟙 X.left))

/-- **Every lift of the identity over the special-fibre thickening of a deformation is an
isomorphism**, in the shape in which [Stacks Project, Tag 0E3V] consumes it. This is
`Deformation.Examples.isIso_of_fixes_specialMap_over_base`, whose proof does not use the
square-zero hypothesis. -/
theorem isIso_of_lift_id (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (_hsq : P.specialMap.ker ^ 2 = ⊥)
    (e : P.scheme ⟶ P.scheme) (he₁ : e ≫ P.toBase = P.toBase)
    (he₂ : P.specialMap ≫ e = P.specialMap) : IsIso e :=
  isIso_of_fixes_specialMap_over_base P e he₁ he₂

/-! ### The fibre automorphism group as the set of global lifts -/

/-- `Deformation.Examples.fiberAutEquivSelfMaps` carries the group structure of the fibre
automorphisms to composition of self-maps, contravariantly: the composition of
`Deformation.Examples.SchemeDeformationCategory.Hom` is contravariant on total spaces, and the
multiplication of `CategoryTheory.Aut` composes in the other order, so the two reversals cancel
into this equation. -/
theorem fiberAutEquivSelfMaps_mul (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (a b : Aut (deformationFiberObj P)) :
    (fiberAutEquivSelfMaps P (a * b)).val =
      (fiberAutEquivSelfMaps P a).val ≫ (fiberAutEquivSelfMaps P b).val := rfl

/-- **The fibre automorphism group of a deformation is the set of global lifts of the identity
over the base.** The invertibility clause of
`Deformation.Examples.fiberAutEquivSelfMaps` is automatic by
`Deformation.Examples.isIso_of_fixes_specialMap_over_base`, so the two descriptions of a
self-map agree, and `Deformation.Examples.liftsOverBaseTopEquivSelfMaps` identifies the second
with the lift set. `Deformation.Examples.fiberAutEquivSelfMaps_mul` says the bijection takes the
group law to composition of self-maps. -/
def fiberAutEquivLiftsOverBaseTop (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    Aut (deformationFiberObj P) ≃
      Stacks.Thickenings.liftsOverBase P.specialMap P.specialMap P.toBase P.toBase
        (𝟙 X.left) ⊤ :=
  (fiberAutEquivSelfMaps P).trans
    ((Equiv.subtypeEquivRight fun e =>
        ⟨fun h => ⟨h.1, h.2.1⟩,
          fun h => ⟨h.1, h.2, isIso_of_fixes_specialMap_over_base P e h.1 h.2⟩⟩).trans
      (liftsOverBaseTopEquivSelfMaps P).symm)

end Deformation.Examples

end
