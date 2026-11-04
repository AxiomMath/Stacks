module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.MinimalDegreeFibreBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSpacesFieldRepresentability
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoidStabilizerDimension

/-!
# The self-intersection groupoid of a field-valued point is a groupoid scheme

Let `𝒳` be an algebraic stack over `S` which is quasi-DM over `S` and let
`ξ : Spec(k) ⟶ 𝒳` be a 1-morphism out of the algebraic stack represented by a field-valued point
of the base which is locally of finite type. The groupoid in algebraic spaces of
**Stacks 04T4** part (4) that `ξ` carries is
`AlgebraicGeometry.Stack.SelfIntersection.pointGroupoid`. Both of its structure spaces, the
presheaf of `Spec(k)` and the self-intersection `Spec(k) ×_{ξ, 𝒳, ξ} Spec(k)`, are representable,
so it is a groupoid scheme over `S` by `AlgebraicGeometry.GroupoidInAlgebraicSpaces.derealization`.

## Main results

* `AlgebraicGeometry.Stack.SelfIntersection.isRepresentable_objects_selfIntersectionGroupoid`:
  the object space of a self-intersection groupoid is representable as soon as the representing
  space of the source stack is identified with the presheaf of an object of the site.
* `AlgebraicGeometry.Stack.SelfIntersection.isRepresentable_arrows_selfIntersectionGroupoid`:
  the arrow space is representable when the object space is a field spectrum of the site, the
  source map is locally of finite type and the arrow space has dimension at most zero.
* `AlgebraicGeometry.Stack.SelfIntersection.isRepresentable_objects_pointGroupoid` and
  `AlgebraicGeometry.Stack.SelfIntersection.isRepresentable_arrows_pointGroupoid`: both
  representabilities at the self-intersection groupoid of a field-valued point of a quasi-DM
  algebraic stack.
* `AlgebraicGeometry.Stack.SelfIntersection.pointGroupoidScheme`: that groupoid as a groupoid
  scheme over `S`.
* `AlgebraicGeometry.Stack.SelfIntersection.pointGroupoidScheme_fieldSpectrum`: the same at a
  field spectrum `AlgebraicGeometry.Stack.FieldSpectrum` of the site.

## References

* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 06FF](https://stacks.math.columbia.edu/tag/06FF)
* [Stacks Project, Tag 06LZ](https://stacks.math.columbia.edu/tag/06LZ)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 06N0](https://stacks.math.columbia.edu/tag/06N0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.SelfIntersection

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
variable {f : 𝒰.val ⥤ᵇ 𝒳.val}
variable {U R : AlgebraicSpaces B S hS}
variable
  (eU : StacksRepresentableCFG.EquivalenceOver
    𝒰.val.p (presheafOfCategories (U.obj ⋙ typeToCat)).p)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (relation B S hS 𝒰 𝒳 f).val.p
    (presheafOfCategories (R.obj ⋙ typeToCat)).p)

/-- **The object space of a self-intersection groupoid is representable** as soon as the
representing space of the source stack is identified with the presheaf of an object of the
site. -/
theorem isRepresentable_objects_selfIntersectionGroupoid
    (hsetU : 𝒰.val.p.IsFiberedInSetoids) {K : BigFppfOver B S hS} (e : U.obj ≅ yoneda.obj K) :
    (selfIntersectionGroupoid eU eR hsetU).objects.obj.IsRepresentable :=
  GroupoidInAlgebraicSpaces.isRepresentable_objects (selfIntersectionGroupoid eU eR hsetU) e

/-- **The arrow space of a self-intersection groupoid over a field spectrum of the site is
representable** when the source map is locally of finite type and the arrow space has dimension
at most zero. -/
theorem isRepresentable_arrows_selfIntersectionGroupoid
    (hsetU : 𝒰.val.p.IsFiberedInSetoids) (hZ : B.Contains (⊤_ Scheme.{u}))
    {K : BigFppfOver B S hS} (e : U.obj ≅ yoneda.obj K) {k : Type u} [Field k]
    (eK : (BigFppfOver.toScheme B S hS).obj K ≅ Spec (.of k))
    (hsrc : Space.IsLocallyOfFiniteType B S hS (relationSourceMap eU eR))
    (hdim : Space.dimension B S hS R.obj R.property ≤ 0) :
    (selfIntersectionGroupoid eU eR hsetU).arrows.obj.IsRepresentable :=
  GroupoidInAlgebraicSpaces.isRepresentable_arrows_of_dimension_le_zero
    (selfIntersectionGroupoid eU eR hsetU) hZ e eK hsrc hdim
    (Nonempty.map (Space.pointsMap B S hS (yoneda.obj K) e.inv)
      (Space.nonempty_points_yoneda_of_isoSpec_toScheme B S hS K eK))

end AlgebraicGeometry.Stack.SelfIntersection

namespace AlgebraicGeometry.Stack.SelfIntersection

/-- The arrow space of the self-intersection groupoid of a quasi-DM algebraic stack at an object
of the site that is a field spectrum is representable. -/
private theorem isRepresentable_arrows_pointGroupoid_of_isoSpecField
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (F : FieldSpectrum B S hS)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (ξ : schemeStack.{u, w} B S hS F.base ⟶ 𝒳)
    (Rsp : AlgebraicSpaces B S hS)
    (eR : StacksRepresentableCFG.EquivalenceOver
      (AlgebraicStacks.twoFibreProduct B S hS ξ ξ).val.val.p
      (presheafOfCategories (Rsp.obj ⋙ typeToCat)).p)
    (hZ : B.Contains (⊤_ Scheme.{u})) (h𝒳 : IsQuasiDMOver B S hS 𝒳)
    (hξ : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ) :
    Functor.IsRepresentable (pointGroupoid B S hS F.base ξ Rsp eR).arrows.obj :=
  GroupoidInAlgebraicSpaces.isRepresentable_arrows_of_dimension_le_zero
    (pointGroupoid B S hS F.base ξ Rsp eR) hZ (Iso.refl _) F.isSpec
    (isLocallyOfFiniteType_source_pointGroupoid B S hS F.base ξ Rsp eR hξ)
    (dimension_relation_le_zero_of_isoSpecField B S hS F.base F.carrier F.isSpec ξ Rsp eR h𝒳 hξ)
    (Space.nonempty_points_yoneda_of_isoSpec_toScheme B S hS F.base F.isSpec)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
  {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (ξ : schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)) ⟶ 𝒳)
  (Rsp : AlgebraicSpaces B S hS)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (AlgebraicStacks.twoFibreProduct B S hS ξ ξ).val.val.p
    (presheafOfCategories (Rsp.obj ⋙ typeToCat)).p)

/-- **The object space of the self-intersection groupoid of a field-valued point is
representable**: it is the presheaf of that point's object of the site on the nose. -/
theorem isRepresentable_objects_pointGroupoid :
    Functor.IsRepresentable
      (pointGroupoid B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)) ξ Rsp eR).objects.obj :=
  GroupoidInAlgebraicSpaces.isRepresentable_objects
    (pointGroupoid B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)) ξ Rsp eR)
    (Iso.refl _)

include eR in
/-- **The arrow space of the self-intersection groupoid of a field-valued point of a quasi-DM
algebraic stack is representable**: the algebraic space representing
`Spec(k) ×_{ξ, 𝒳, ξ} Spec(k)` is a scheme. -/
theorem isRepresentable_arrows_pointGroupoid (hZ : B.Contains (⊤_ Scheme.{u}))
    (h𝒳 : IsQuasiDMOver B S hS 𝒳)
    (hξ : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ) :
    Functor.IsRepresentable
      (pointGroupoid B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)) ξ Rsp eR).arrows.obj :=
  isRepresentable_arrows_pointGroupoid_of_isoSpecField B S hS
    ⟨k, Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS), Iso.refl _⟩ ξ Rsp eR hZ h𝒳 hξ

include eR in
/-- **The self-intersection groupoid of a field-valued point of a quasi-DM algebraic stack is a
groupoid scheme over `S`**: `AlgebraicGeometry.GroupoidInAlgebraicSpaces.derealization` of
`AlgebraicGeometry.Stack.SelfIntersection.pointGroupoid`, whose object and arrow schemes represent
`Spec(k)` and the self-intersection. -/
noncomputable def pointGroupoidScheme (hZ : B.Contains (⊤_ Scheme.{u}))
    (h𝒳 : IsQuasiDMOver B S hS 𝒳)
    (hξ : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ) :
    _root_.Stacks.Groupoids.GroupoidScheme S :=
  haveI := isRepresentable_objects_pointGroupoid B S hS k hk toBase ξ Rsp eR
  haveI := isRepresentable_arrows_pointGroupoid B S hS k hk toBase ξ Rsp eR hZ h𝒳 hξ
  GroupoidInAlgebraicSpaces.derealization
    (pointGroupoid B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)) ξ Rsp eR)

end AlgebraicGeometry.Stack.SelfIntersection

namespace AlgebraicGeometry.Stack.SelfIntersection

/-! ### At the field spectrum that Stacks 06MP hands over -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : FieldSpectrum B S hS)
  {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (ξ : schemeStack.{u, w} B S hS F.base ⟶ 𝒳)
  (Rsp : AlgebraicSpaces B S hS)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (AlgebraicStacks.twoFibreProduct B S hS ξ ξ).val.val.p
    (presheafOfCategories (Rsp.obj ⋙ typeToCat)).p)

include eR in
/-- **The self-intersection of the field-valued point of Stacks 06MP has dimension at most
zero.** -/
theorem dimension_relation_le_zero_fieldSpectrum
    (h𝒳 : IsQuasiDMOver B S hS 𝒳)
    (hξ : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ) :
    Space.dimension B S hS Rsp.obj Rsp.property ≤ 0 :=
  dimension_relation_le_zero_of_isoSpecField B S hS F.base F.carrier F.isSpec ξ Rsp eR h𝒳 hξ

include eR in
/-- The source morphism of the self-intersection groupoid of the field spectrum of
**Stacks 06MP** is locally quasi-finite. -/
theorem isLocallyQuasiFinite_source_pointGroupoid_fieldSpectrum
    (h𝒳 : IsQuasiDMOver B S hS 𝒳)
    (hξ : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ) :
    Space.IsLocallyQuasiFinite B S hS
      (pointGroupoid B S hS F.base ξ Rsp eR).source.hom :=
  isLocallyQuasiFinite_source_pointGroupoid_of_isoSpecField B S hS F.base F.carrier F.isSpec
    ξ Rsp eR h𝒳 hξ

include eR in
/-- The target morphism of the self-intersection groupoid of the field spectrum of
**Stacks 06MP** is locally quasi-finite. -/
theorem isLocallyQuasiFinite_target_pointGroupoid_fieldSpectrum
    (h𝒳 : IsQuasiDMOver B S hS 𝒳)
    (hξ : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ) :
    Space.IsLocallyQuasiFinite B S hS
      (pointGroupoid B S hS F.base ξ Rsp eR).target.hom :=
  isLocallyQuasiFinite_target_pointGroupoid_of_isoSpecField B S hS F.base F.carrier F.isSpec
    ξ Rsp eR h𝒳 hξ

/-- **The object space of the self-intersection groupoid of the field spectrum of Stacks 06MP is
representable**: it is the presheaf of that spectrum's object of the site on the nose. -/
theorem isRepresentable_objects_pointGroupoid_fieldSpectrum :
    Functor.IsRepresentable (pointGroupoid B S hS F.base ξ Rsp eR).objects.obj :=
  GroupoidInAlgebraicSpaces.isRepresentable_objects
    (pointGroupoid B S hS F.base ξ Rsp eR) (Iso.refl _)

include eR in
/-- **The arrow space of the self-intersection groupoid of the field spectrum of Stacks 06MP is
representable.** -/
theorem isRepresentable_arrows_pointGroupoid_fieldSpectrum
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h𝒳 : IsQuasiDMOver B S hS 𝒳)
    (hξ : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ) :
    Functor.IsRepresentable (pointGroupoid B S hS F.base ξ Rsp eR).arrows.obj :=
  isRepresentable_arrows_pointGroupoid_of_isoSpecField B S hS F ξ Rsp eR hZ h𝒳 hξ

include eR in
/-- **The self-intersection groupoid of the field spectrum of Stacks 06MP is a groupoid scheme
over `S`**: `AlgebraicGeometry.GroupoidInAlgebraicSpaces.derealization` of
`AlgebraicGeometry.Stack.SelfIntersection.pointGroupoid` at that spectrum. -/
noncomputable def pointGroupoidScheme_fieldSpectrum
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h𝒳 : IsQuasiDMOver B S hS 𝒳)
    (hξ : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ) :
    _root_.Stacks.Groupoids.GroupoidScheme S :=
  haveI := isRepresentable_objects_pointGroupoid_fieldSpectrum B S hS F ξ Rsp eR
  haveI := isRepresentable_arrows_pointGroupoid_fieldSpectrum B S hS F ξ Rsp eR hZ h𝒳 hξ
  GroupoidInAlgebraicSpaces.derealization (pointGroupoid B S hS F.base ξ Rsp eR)

end AlgebraicGeometry.Stack.SelfIntersection

end
