module

public import StacksFrontier.Deformation.Artin.Infinitesimal.InfIsomTransport
public import StacksFrontier.Deformation.Artin.Infinitesimal.DeformationSituationMorphism

/-!
# Infinitesimal automorphisms as sections of the automorphism presheaf

Let `p : 𝒳 ⥤ (Sch/S)_fppf` be a category fibred in groupoids and `x` an object over `Spec A`.
The presheaf `Mor(x, x)` of Stacks 02ZB lives on the slice over `Spec A`, which is the big fppf
site of `Spec A` (`Over.iteratedSliceBackward`); for a category fibred in groupoids it is the
automorphism presheaf `Isom(x, x)` of the source.

Let `x' ⟶ x` be an arrow over `Spec D ⟶ Spec A`. For a `D`-module `M` the trivial deformation of
`x'` over `Spec D[M]` is a pullback of `x` along `Spec D[M] ⟶ Spec D ⟶ Spec A`, so its vertical
endomorphisms are transported, by `Deformation.Artin.cartesianCmpEnd`, to sections of `Mor(x, x)`
over `Spec D[M]`, read as an object of the big fppf site of `Spec A`. The infinitesimal
automorphisms of the trivial deformation, the source's `Inf_{x'}(M)`, are exactly the sections
whose restriction to `Spec D` is the identity (`Deformation.Artin.infIsomEquiv`), and the
transport commutes with restriction along every arrow of trivial deformations compatible with the
arrows to `x` (`Deformation.Artin.morRestrict_infIsomSec`).

With `x' = x` this says `Inf_x(M) = ker(G(A[M]) → G(A))` for the automorphism group space
`G = Isom(x, x)` of `x` over `Spec A`, which is the identification the proof of Stacks 0DNR
starts from.

## Main definitions

* `Deformation.Artin.sqzSliceIso`, `Deformation.Artin.algSliceIso`: `Spec D[M]` and `Spec D` as
  objects over `S` are identified with the same objects read over `Spec A` and pushed back to `S`.
* `Deformation.Artin.infIsomSec`: the section of `Mor(x, x)` attached to an endomorphism of the
  trivial deformation of `x'`.
* `Deformation.Artin.infIsomEquiv`: the bijection with the sections restricting to the identity.

## Main results

* `Deformation.Artin.morRestrict_infIsomSec`: naturality.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor Opposite AlgebraicGeometry

namespace Deformation.Artin

universe u v w

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

section InfIsom

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  [p.IsFibered]
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {x : X} (hx : p.obj x = algebraOver A B S hS toS hA)

/-- `x`, as an object of the fibre over `Spec A`. -/
abbrev fiberPt : p.Fiber (algebraOver A B S hS toS hA) := ⟨x, hx⟩

/-- An object of the big fppf site of `Spec A`, read in the slice over `Spec A`. -/
abbrev sliceOver (T : BigFppfOver B (Spec (.of A)) hA) : Over (algebraOver A B S hS toS hA) :=
  (Over.iteratedSliceBackward (algebraOver A B S hS toS hA)).obj T

section Point

variable {D : Type u} [CommRing D] {toSD : Spec (.of D) ⟶ S} {hD : B.Contains (Spec (.of D))}
  (toSD₀ : Spec (.of D) ⟶ Spec (.of A))
  (s : algebraOver D B S hS toSD hD ⟶ algebraOver A B S hS toS hA)
  (hs : s.left = ObjectProperty.homMk toSD₀)

include hs in
/-- If the arrow `s : Spec D ⟶ Spec A` over `S` has underlying morphism `toSD₀`, then `toSD₀`
followed by the structure morphism of `Spec A` is the structure morphism of `Spec D`. -/
theorem comp_toS_of_left_eq : toSD₀ ≫ toS = toSD := by
  have h := congrArg B.inclusion.map (Over.w s)
  rw [B.inclusion.map_comp, hs] at h
  exact h

include hs in
/-- `Spec D[M]` over `S` is `Spec D[M]` over `Spec A` pushed back to `S`. -/
def sqzSliceIso (M : SiteModule D B) :
    squareZeroOver D B S hS toSD M ≅
      (sliceOver (toS := toS) (squareZeroOver D B (Spec (.of A)) hA toSD₀ M)).left :=
  Over.isoMk (Iso.refl _) (by
    apply ObjectProperty.hom_ext
    change 𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom D M.obj)) ≫ toSD₀) ≫ toS =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom D M.obj)) ≫ toSD
    rw [Category.id_comp, Category.assoc, comp_toS_of_left_eq toSD₀ s hs])

include hs in
/-- `Spec D` over `S` is `Spec D` over `Spec A` pushed back to `S`. -/
def algSliceIso :
    algebraOver D B S hS toSD hD ≅
      (sliceOver (toS := toS) (algebraOver D B (Spec (.of A)) hA toSD₀ hD)).left :=
  Over.isoMk (Iso.refl _) (by
    apply ObjectProperty.hom_ext
    change 𝟙 _ ≫ toSD₀ ≫ toS = toSD
    rw [Category.id_comp, comp_toS_of_left_eq toSD₀ s hs])

/-- The identification `sqzSliceIso`, followed by the structure arrow to `Spec A`, is the
retraction `Spec D[M] ⟶ Spec D` followed by `s`. -/
theorem sqzSliceIso_hom_comp (M : SiteModule D B) :
    (sqzSliceIso toSD₀ s hs M).hom ≫ (sliceOver (toS := toS)
        (squareZeroOver D B (Spec (.of A)) hA toSD₀ M)).hom =
      squareZeroRetraction D B S hS toSD hD M ≫ s := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom D M.obj)) ≫ toSD₀ =
    (squareZeroRetraction D B S hS toSD hD M).left.hom ≫ s.left.hom
  rw [hs, Category.id_comp]
  rfl

/-- The identification `algSliceIso`, followed by the structure arrow to `Spec A`, is `s`. -/
theorem algSliceIso_hom_comp :
    (algSliceIso toSD₀ s hs).hom ≫ (sliceOver (toS := toS)
        (algebraOver D B (Spec (.of A)) hA toSD₀ hD)).hom = s := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change 𝟙 _ ≫ toSD₀ = s.left.hom
  rw [hs, Category.id_comp]
  rfl

variable {x' : X} (hx' : p.obj x' = algebraOver D B S hS toSD hD) (φ' : x' ⟶ x)
  [p.IsHomLift s φ']

/-- The trivial deformation of `x'` over `Spec D[M]`, with its arrow to `x`. -/
abbrev infRetract (M : SiteModule D B) :
    (trivialDeformation D B S hS toSD hD p x' hx' hp M).1.right ⟶ x :=
  trivialRetract D B S hS toSD hD p x' hx' hp M ≫ φ'

/-- The arrow from the trivial deformation of `x'` to `x` lies over
`Spec D[M] ⟶ Spec D ⟶ Spec A`. -/
instance infRetract_isHomLift (M : SiteModule D B) :
    p.IsHomLift (squareZeroRetraction D B S hS toSD hD M ≫ s) (infRetract p hp hx' φ' M) := by
  have := trivialRetract_isHomLift D B S hS toSD hD p x' hx' hp M
  unfold infRetract
  infer_instance

omit [p.IsFibered] in
/-- An endomorphism of a lift lies over the identity. -/
theorem infEnd_isHomLift (M : SiteModule D B)
    (θ : trivialDeformation D B S hS toSD hD p x' hx' hp M ⟶
      trivialDeformation D B S hS toSD hD p x' hx' hp M) :
    p.IsHomLift (𝟙 (squareZeroOver D B S hS toSD M)) θ.1.right :=
  underPost_isHomLift_right p (𝟙 _) θ.1 θ.2

/-- **The section of `Mor(x, x)` attached to an endomorphism of the trivial deformation of
`x'`.** -/
noncomputable def infIsomSec (M : SiteModule D B)
    (θ : trivialDeformation D B S hS toSD hD p x' hx' hp M ⟶
      trivialDeformation D B S hS toSD hD p x' hx' hp M) :
    pullbackFiber p (fiberPt p hx) (sliceOver (toS := toS)
        (squareZeroOver D B (Spec (.of A)) hA toSD₀ M)).hom ⟶
      pullbackFiber p (fiberPt p hx) (sliceOver (toS := toS)
        (squareZeroOver D B (Spec (.of A)) hA toSD₀ M)).hom :=
  have := infEnd_isHomLift p hp hx' M θ
  cartesianCmpEnd p hp (fiberPt p hx) (infRetract p hp hx' φ' M) _ (sqzSliceIso toSD₀ s hs M).hom
    (sqzSliceIso_hom_comp toSD₀ s hs M) θ.1.right

/-- A section `g` of `Mor(x, x)` over `Spec D[M]` is the section attached to `θ` if and only if
the comparison with the chosen pullback intertwines `θ` and `g`. -/
theorem infIsomSec_spec (M : SiteModule D B)
    (θ : trivialDeformation D B S hS toSD hD p x' hx' hp M ⟶
      trivialDeformation D B S hS toSD hD p x' hx' hp M)
    (g : pullbackFiber p (fiberPt p hx) (sliceOver (toS := toS)
        (squareZeroOver D B (Spec (.of A)) hA toSD₀ M)).hom ⟶
      pullbackFiber p (fiberPt p hx) (sliceOver (toS := toS)
        (squareZeroOver D B (Spec (.of A)) hA toSD₀ M)).hom) :
    haveI := infEnd_isHomLift p hp hx' M θ
    g = infIsomSec p hp hx toSD₀ s hs hx' φ' M θ ↔
      θ.1.right ≫ cartesianCmp p (fiberPt p hx) (infRetract p hp hx' φ' M) _
          (sqzSliceIso toSD₀ s hs M).hom (sqzSliceIso_hom_comp toSD₀ s hs M) =
        cartesianCmp p (fiberPt p hx) (infRetract p hp hx' φ' M) _
          (sqzSliceIso toSD₀ s hs M).hom (sqzSliceIso_hom_comp toSD₀ s hs M) ≫
            Fiber.fiberInclusion.map g := by
  have := infEnd_isHomLift p hp hx' M θ
  exact eq_cartesianCmpEnd_iff p hp (fiberPt p hx) _ _ _ _ θ.1.right g

/-- The section of `Mor(x, x)` over `Spec D` attached to `x'`: the identity. -/
theorem cartesianCmpEnd_point_id :
    haveI : p.IsHomLift (𝟙 (algebraOver D B S hS toSD hD)) (𝟙 x') := IsHomLift.id hx'
    cartesianCmpEnd p hp (fiberPt p hx) φ' _ (algSliceIso toSD₀ s hs).hom
      (algSliceIso_hom_comp toSD₀ s hs) (𝟙 x') = 𝟙 _ :=
  cartesianCmpEnd_id p hp (fiberPt p hx) φ' _ _ _

/-- The identifications `algSliceIso` and `sqzSliceIso` are compatible with the closed immersion
`Spec D ⟶ Spec D[M]`. -/
theorem algSliceIso_hom_comp_squareZeroArrow (M : SiteModule D B) :
    (algSliceIso toSD₀ s hs).hom ≫ ((Over.iteratedSliceBackward
        (algebraOver A B S hS toS hA)).map
          (squareZeroArrow D B (Spec (.of A)) hA toSD₀ hD M)).left =
      squareZeroArrow D B S hS toSD hD M ≫ (sqzSliceIso toSD₀ s hs M).hom := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom D D M.obj).toRingHom) =
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom D D M.obj).toRingHom) ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]

/-- The transport of an endomorphism `θ'` of the trivial deformation restricts, along
`Spec D ⟶ Spec D[M]`, to the transport of any `θ₁ : x' ⟶ x'` with `θ₁ ≫ ι = ι ≫ θ'`. -/
private theorem morRestrict_cartesianCmpEnd_trivialDeformation (M : SiteModule D B)
    (θ₁ : x' ⟶ x')
    (θ' : (trivialDeformation D B S hS toSD hD p x' hx' hp M).1.right ⟶
      (trivialDeformation D B S hS toSD hD p x' hx' hp M).1.right)
    [p.IsHomLift (𝟙 (algebraOver D B S hS toSD hD)) θ₁]
    [p.IsHomLift (𝟙 (squareZeroOver D B S hS toSD M)) θ']
    (hθ : θ₁ ≫ (trivialDeformation D B S hS toSD hD p x' hx' hp M).1.hom =
      (trivialDeformation D B S hS toSD hD p x' hx' hp M).1.hom ≫ θ') :
    morRestrict p (fiberPt p hx) (fiberPt p hx)
        ((Over.iteratedSliceBackward (algebraOver A B S hS toS hA)).map
          (squareZeroArrow D B (Spec (.of A)) hA toSD₀ hD M))
        (cartesianCmpEnd p hp (fiberPt p hx) (infRetract p hp hx' φ' M) _
          (sqzSliceIso toSD₀ s hs M).hom (sqzSliceIso_hom_comp toSD₀ s hs M) θ') =
      cartesianCmpEnd p hp (fiberPt p hx) φ' _ (algSliceIso toSD₀ s hs).hom
        (algSliceIso_hom_comp toSD₀ s hs) θ₁ := by
  have := underFiber_isHomLift p hx' (squareZeroArrow D B S hS toSD hD M)
    (trivialDeformation D B S hS toSD hD p x' hx' hp M)
  exact morRestrict_cartesianCmpEnd p hp (fiberPt p hx) φ' (infRetract p hp hx' φ' M)
    (algSliceIso toSD₀ s hs).hom (sqzSliceIso toSD₀ s hs M).hom (algSliceIso_hom_comp toSD₀ s hs)
    (sqzSliceIso_hom_comp toSD₀ s hs M) (trivialDeformation D B S hS toSD hD p x' hx' hp M).1.hom
    (by rw [← Category.assoc, trivialRetract_fac, Category.id_comp]) _
    (algSliceIso_hom_comp_squareZeroArrow toSD₀ s hs M) θ₁ θ' hθ

/-- **An endomorphism of the trivial deformation is infinitesimal**: its section restricts to the
identity over `Spec D`. -/
theorem infIsomSec_restrict (M : SiteModule D B)
    (θ : trivialDeformation D B S hS toSD hD p x' hx' hp M ⟶
      trivialDeformation D B S hS toSD hD p x' hx' hp M) :
    morRestrict p (fiberPt p hx) (fiberPt p hx)
        ((Over.iteratedSliceBackward (algebraOver A B S hS toS hA)).map
          (squareZeroArrow D B (Spec (.of A)) hA toSD₀ hD M))
        (infIsomSec p hp hx toSD₀ s hs hx' φ' M θ) = 𝟙 _ := by
  have := infEnd_isHomLift p hp hx' M θ
  have : p.IsHomLift (𝟙 (algebraOver D B S hS toSD hD)) (𝟙 x') := IsHomLift.id hx'
  rw [infIsomSec, morRestrict_cartesianCmpEnd_trivialDeformation p hp hx toSD₀ s hs hx' φ' M
    (𝟙 x') θ.1.right (by rw [Category.id_comp]; exact (Under.w θ.1).symm)]
  exact cartesianCmpEnd_point_id p hp hx toSD₀ s hs hx' φ'

/-- The section attached to an endomorphism of the trivial deformation determines it. -/
theorem infIsomSec_injective (M : SiteModule D B) :
    Function.Injective (infIsomSec p hp hx toSD₀ s hs hx' φ' M) := by
  intro θ θ' h
  have := infEnd_isHomLift p hp hx' M θ
  have := infEnd_isHomLift p hp hx' M θ'
  have h' := cartesianCmpEnd_injective p hp (fiberPt p hx) _ _ _ _ θ.1.right θ'.1.right h
  exact Functor.Fiber.hom_ext (Under.UnderMorphism.ext h')

/-- Every section of `Mor(x, x)` over `Spec D[M]` restricting to the identity over `Spec D` is
the section attached to an endomorphism of the trivial deformation of `x'`. -/
theorem exists_infIsomSec_eq (M : SiteModule D B)
    (g : pullbackFiber p (fiberPt p hx) (sliceOver (toS := toS)
        (squareZeroOver D B (Spec (.of A)) hA toSD₀ M)).hom ⟶
      pullbackFiber p (fiberPt p hx) (sliceOver (toS := toS)
        (squareZeroOver D B (Spec (.of A)) hA toSD₀ M)).hom)
    (hg : morRestrict p (fiberPt p hx) (fiberPt p hx)
        ((Over.iteratedSliceBackward (algebraOver A B S hS toS hA)).map
          (squareZeroArrow D B (Spec (.of A)) hA toSD₀ hD M)) g = 𝟙 _) :
    ∃ θ, infIsomSec p hp hx toSD₀ s hs hx' φ' M θ = g := by
  let td := trivialDeformation D B S hS toSD hD p x' hx' hp M
  let c := infRetract p hp hx' φ' M
  let θ' := cartesianCmpEndInv p hp (fiberPt p hx) c _ (sqzSliceIso toSD₀ s hs M).hom
    (sqzSliceIso_hom_comp toSD₀ s hs M) g
  have hθ' : p.IsHomLift (𝟙 (squareZeroOver D B S hS toSD M)) θ' :=
    cartesianCmpEndInv_isHomLift p hp (fiberPt p hx) c _ _ _ g
  have := underFiber_isHomLift p hx' (squareZeroArrow D B S hS toSD hD M) td
  have := hp.isStronglyCartesian_homLift (squareZeroArrow D B S hS toSD hD M) td.1.hom
  have : p.IsHomLift (𝟙 (algebraOver D B S hS toSD hD)) (𝟙 x') := IsHomLift.id hx'
  -- the restriction of `θ'` to `x'`
  let θ₁ : x' ⟶ x' := IsStronglyCartesian.map p (squareZeroArrow D B S hS toSD hD M) td.1.hom
    (Category.id_comp _).symm (td.1.hom ≫ θ')
  have : p.IsHomLift (𝟙 (algebraOver D B S hS toSD hD)) θ₁ :=
    IsStronglyCartesian.map_isHomLift p _ _ _ _
  have hθ₁ : θ₁ ≫ td.1.hom = td.1.hom ≫ θ' := IsStronglyCartesian.fac p _ _ _ _
  have hres := morRestrict_cartesianCmpEnd_trivialDeformation p hp hx toSD₀ s hs hx' φ' M θ₁ θ' hθ₁
  rw [cartesianCmpEnd_cartesianCmpEndInv, hg,
    ← cartesianCmpEnd_point_id p hp hx toSD₀ s hs hx' φ'] at hres
  have h1 : θ₁ = 𝟙 x' := (cartesianCmpEnd_injective p hp (fiberPt p hx) φ' _ _ _ _ _ hres).symm
  have hw : td.1.hom ≫ θ' = td.1.hom := by rw [← hθ₁, h1, Category.id_comp]
  refine ⟨underFiberHomMk p hx' (squareZeroArrow D B S hS toSD hD M) θ' hθ' hw, ?_⟩
  change cartesianCmpEnd p hp (fiberPt p hx) c _ _ _ θ' = g
  exact cartesianCmpEnd_cartesianCmpEndInv p hp (fiberPt p hx) c _ _ _ g

/-- **`Inf_{x'}(M)` is the set of sections of `Mor(x, x)` over `Spec D[M]` restricting to the
identity over `Spec D`.** -/
noncomputable def infIsomEquiv (M : SiteModule D B) :
    (trivialDeformation D B S hS toSD hD p x' hx' hp M ⟶
        trivialDeformation D B S hS toSD hD p x' hx' hp M) ≃
      {g : pullbackFiber p (fiberPt p hx) (sliceOver (toS := toS)
          (squareZeroOver D B (Spec (.of A)) hA toSD₀ M)).hom ⟶
        pullbackFiber p (fiberPt p hx) (sliceOver (toS := toS)
          (squareZeroOver D B (Spec (.of A)) hA toSD₀ M)).hom //
        morRestrict p (fiberPt p hx) (fiberPt p hx)
          ((Over.iteratedSliceBackward (algebraOver A B S hS toS hA)).map
            (squareZeroArrow D B (Spec (.of A)) hA toSD₀ hD M)) g = 𝟙 _} :=
  Equiv.ofBijective (fun θ ↦ ⟨infIsomSec p hp hx toSD₀ s hs hx' φ' M θ,
      infIsomSec_restrict p hp hx toSD₀ s hs hx' φ' M θ⟩)
    ⟨fun _ _ h ↦ infIsomSec_injective p hp hx toSD₀ s hs hx' φ' M (congrArg Subtype.val h),
      fun g ↦ (exists_infIsomSec_eq p hp hx toSD₀ s hs hx' φ' M g.1 g.2).imp
        fun _ h ↦ Subtype.ext h⟩

/-- The section underlying the image of `θ` under `infIsomEquiv` is the section attached to
`θ`. -/
@[simp]
theorem infIsomEquiv_apply (M : SiteModule D B)
    (θ : trivialDeformation D B S hS toSD hD p x' hx' hp M ⟶
      trivialDeformation D B S hS toSD hD p x' hx' hp M) :
    (infIsomEquiv p hp hx toSD₀ s hs hx' φ' M θ).1 = infIsomSec p hp hx toSD₀ s hs hx' φ' M θ :=
  rfl

end Point

/-- **Naturality of the sections of infinitesimal automorphisms.** Let `x₁ ⟶ x` and `x₂ ⟶ x`
be two points, `k` an arrow from the trivial deformation of `x₁` over `Spec D₁[M₁]` to that of
`x₂` over `Spec D₂[M₂]` lying over a morphism `h` that is also a morphism `H₀` of the site of
`Spec A`, and compatible with the arrows to `x`. If `θ₁` is the restriction of `θ₂` along `k`,
the section of `θ₁` is the restriction of the section of `θ₂` along `H₀`. -/
theorem morRestrict_infIsomSec
    {D₁ : Type u} [CommRing D₁] {toS₁ : Spec (.of D₁) ⟶ S} {h₁ : B.Contains (Spec (.of D₁))}
    (toS₁₀ : Spec (.of D₁) ⟶ Spec (.of A))
    (s₁ : algebraOver D₁ B S hS toS₁ h₁ ⟶ algebraOver A B S hS toS hA)
    (hs₁ : s₁.left = ObjectProperty.homMk toS₁₀)
    {x₁ : X} (hx₁ : p.obj x₁ = algebraOver D₁ B S hS toS₁ h₁) (φ₁ : x₁ ⟶ x) [p.IsHomLift s₁ φ₁]
    {D₂ : Type u} [CommRing D₂] {toS₂ : Spec (.of D₂) ⟶ S} {h₂ : B.Contains (Spec (.of D₂))}
    (toS₂₀ : Spec (.of D₂) ⟶ Spec (.of A))
    (s₂ : algebraOver D₂ B S hS toS₂ h₂ ⟶ algebraOver A B S hS toS hA)
    (hs₂ : s₂.left = ObjectProperty.homMk toS₂₀)
    {x₂ : X} (hx₂ : p.obj x₂ = algebraOver D₂ B S hS toS₂ h₂) (φ₂ : x₂ ⟶ x) [p.IsHomLift s₂ φ₂]
    (M₁ : SiteModule D₁ B) (M₂ : SiteModule D₂ B)
    (H₀ : squareZeroOver D₁ B (Spec (.of A)) hA toS₁₀ M₁ ⟶
      squareZeroOver D₂ B (Spec (.of A)) hA toS₂₀ M₂)
    (h : squareZeroOver D₁ B S hS toS₁ M₁ ⟶ squareZeroOver D₂ B S hS toS₂ M₂)
    (hh : h.left = H₀.left)
    (k : (trivialDeformation D₁ B S hS toS₁ h₁ p x₁ hx₁ hp M₁).1.right ⟶
      (trivialDeformation D₂ B S hS toS₂ h₂ p x₂ hx₂ hp M₂).1.right) [p.IsHomLift h k]
    (hk : k ≫ infRetract p hp hx₂ φ₂ M₂ = infRetract p hp hx₁ φ₁ M₁)
    (θ₁ : trivialDeformation D₁ B S hS toS₁ h₁ p x₁ hx₁ hp M₁ ⟶
      trivialDeformation D₁ B S hS toS₁ h₁ p x₁ hx₁ hp M₁)
    (θ₂ : trivialDeformation D₂ B S hS toS₂ h₂ p x₂ hx₂ hp M₂ ⟶
      trivialDeformation D₂ B S hS toS₂ h₂ p x₂ hx₂ hp M₂)
    (hθ : θ₁.1.right ≫ k = k ≫ θ₂.1.right) :
    morRestrict p (fiberPt p hx) (fiberPt p hx)
        ((Over.iteratedSliceBackward (algebraOver A B S hS toS hA)).map H₀)
        (infIsomSec p hp hx toS₂₀ s₂ hs₂ hx₂ φ₂ M₂ θ₂) =
      infIsomSec p hp hx toS₁₀ s₁ hs₁ hx₁ φ₁ M₁ θ₁ := by
  have := infEnd_isHomLift p hp hx₁ M₁ θ₁
  have := infEnd_isHomLift p hp hx₂ M₂ θ₂
  refine morRestrict_cartesianCmpEnd p hp (fiberPt p hx) _ _ _ _ _ _ (h := h) k hk _ ?_ θ₁.1.right
    θ₂.1.right hθ
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change 𝟙 _ ≫ H₀.left.hom = h.left.hom ≫ 𝟙 _
  rw [hh, Category.id_comp, Category.comp_id]

end InfIsom

end Deformation.Artin
