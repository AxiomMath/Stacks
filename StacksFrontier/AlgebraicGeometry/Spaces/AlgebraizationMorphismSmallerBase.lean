module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraizationMorphismAdicFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsSmallerBaseInverse
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionDiagonalTransport
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionDiagonalBootstrap
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSituationSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionSmallerBase

/-!
# Algebraization of morphisms over a base scheme from the affine case

Grothendieck's existence theorem for closed subspaces (Stacks 08BG) over the big fppf site of an
affine Noetherian scheme `Spec R` at its terminal object implies the same statement over the big
fppf site of an arbitrary base scheme `S` at an affine object `V = (Spec R ⟶ S)`. The two are
related by the equivalence of Stacks 04SG (`AlgebraicGeometry.spacesOverSmallerBaseEquivalence`)
between algebraic spaces over `Spec R` and algebraic spaces over `S` with a morphism to `V`. As a
consequence one obtains the algebraization of morphisms (Stacks 0A4Z) for algebraic spaces
proper over such `V`.

A subfunctor `Z` of an algebraic space `X` over `V` gives the subfunctor
`AlgebraicGeometry.Space.overSpecSubfunctor` of the attached space `X_V` over `Spec R`; it
preserves intersections, closed subspaces, properness and the infinitesimal fibres, and it is
injective. Conversely a subfunctor of `X_V` gives the image of its lower-shriek extension in `X`
(`AlgebraicGeometry.Space.overSpecImage`), preserving closed subspaces and properness, and the two
constructions are inverse on that side.

## Main results

* `AlgebraicGeometry.Space.closedSubspaceTowerAlgebraizes_overMk`: Stacks 08BG at `V` over the
  site of `S` from Stacks 08BG at the base over the site of `Spec R`.
* `AlgebraicGeometry.Space.HasProperTowerAlgebraizationOverSpec` and
  `AlgebraicGeometry.Space.hasProperTowerAlgebraizationOverSpec_of_closedSubspaceTowerAlgebraizes`:
  the tower form of Stacks 0A4Z for every affine `V = (Spec R ⟶ S)`, given Stacks 08BG over the
  sites of Noetherian affine schemes.

## References

* [Stacks Project, Tag 0A4Z](https://stacks.math.columbia.edu/tag/0A4Z)
* [Stacks Project, Tag 08BG](https://stacks.math.columbia.edu/tag/08BG)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) {R : Type u} [CommRing R]
  (hR : B.Contains (Spec (.of R))) (g : B.obj hR ⟶ B.obj hS)

/-- The presheaf over `Spec R` attached by Stacks 04SG to a presheaf over `V = (Spec R ⟶ S)`. -/
abbrev overSpecInverse (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :
    (BigFppfOver B (Spec (.of R)) hR)ᵒᵖ ⥤ Type u :=
  (smallerBasePresheafEquivalence B (Spec (.of R)) S hR hS g).inverse.obj X

variable {hS hR g}

/-- The subfunctor of `X_V` cut out by a subfunctor of `X`: a section of `X_V` over `T` is a
section of `X` over `T` viewed over `S`, and it lies in the subfunctor when that section does. -/
def overSpecSubfunctor {X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (Z : Subfunctor X.left) : Subfunctor (overSpecInverse B hS hR g X) where
  obj T := {y | y.1 ∈ Z.obj (op ((Over.map g).obj T.unop))}
  map i _ hy := Z.map ((Over.map g).map i.unop).op hy

/-- A section `y` of `X_V` over `T` lies in `overSpecSubfunctor B Z` exactly when the underlying
section of `X` over `T` viewed over `S` lies in `Z`. -/
theorem mem_overSpecSubfunctor_iff
    {X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (Z : Subfunctor X.left) {T : BigFppfOver B (Spec (.of R)) hR}
    (y : (overSpecInverse B hS hR g X).obj (op T)) :
    y ∈ (overSpecSubfunctor B Z).obj (op T) ↔ y.1 ∈ Z.obj (op ((Over.map g).obj T)) :=
  Iff.rfl

/-- `overSpecSubfunctor` preserves intersections of subfunctors. -/
theorem overSpecSubfunctor_inf
    {X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (Z₁ Z₂ : Subfunctor X.left) :
    overSpecSubfunctor B (Z₁ ⊓ Z₂) = overSpecSubfunctor B Z₁ ⊓ overSpecSubfunctor B Z₂ :=
  rfl

/-- `overSpecSubfunctor` is monotone. -/
theorem overSpecSubfunctor_mono
    {X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    {Z₁ Z₂ : Subfunctor X.left} (h : Z₁ ≤ Z₂) :
    overSpecSubfunctor B Z₁ ≤ overSpecSubfunctor B Z₂ :=
  fun _ _ hy => h _ hy

/-- The section of `X_V` over `(T, ψ)` attached to a section `x` of `X` over `T`, where `ψ` is
the factorization of the structure morphism of `T` read off from `x`. -/
def overSpecSection {X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    {T : BigFppfOver B S hS} (x : X.left.obj (op T)) :
    (overSpecInverse B hS hR g X).obj
      (op (Over.mk (X.hom.app (op T) x).left : BigFppfOver B (Spec (.of R)) hR)) :=
  ⟨X.left.map (smallerBaseFactorHomInv B (Spec (.of R)) S hR hS g
      (Over.w (X.hom.app (op T) x))).op x,
    (NatTrans.naturality_apply X.hom
      (smallerBaseFactorHomInv B (Spec (.of R)) S hR hS g (Over.w (X.hom.app (op T) x))).op
        x).trans (Over.OverMorphism.ext (Category.id_comp _))⟩

/-- Restricting `overSpecSection B x` along the comparison morphism `smallerBaseFactorHom`
recovers the section `x` of `X`. -/
theorem map_smallerBaseFactorHom_overSpecSection
    {X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    {T : BigFppfOver B S hS} (x : X.left.obj (op T)) :
    X.left.map (smallerBaseFactorHom B (Spec (.of R)) S hR hS g
      (Over.w (X.hom.app (op T) x))).op (overSpecSection B x).1 = x := by
  refine (X.left.map_comp_apply _ _ x).symm.trans ?_
  have : smallerBaseFactorHom B (Spec (.of R)) S hR hS g (Over.w (X.hom.app (op T) x)) ≫
      smallerBaseFactorHomInv B (Spec (.of R)) S hR hS g (Over.w (X.hom.app (op T) x)) = 𝟙 _ :=
    Over.OverMorphism.ext (by simp [smallerBaseFactorHom, smallerBaseFactorHomInv])
  have hop : (smallerBaseFactorHomInv B (Spec (.of R)) S hR hS g
      (Over.w (X.hom.app (op T) x))).op ≫ (smallerBaseFactorHom B (Spec (.of R)) S hR hS g
        (Over.w (X.hom.app (op T) x))).op = 𝟙 _ := by
    rw [← op_comp, this, op_id]
  exact (congrArg (fun k => X.left.map k x) hop).trans (X.left.map_id_apply _ x)

/-- A section `x` of `X` lies in `Z` exactly when `overSpecSection B x` lies in
`overSpecSubfunctor B Z`. -/
theorem mem_iff_overSpecSection_mem
    {X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (Z : Subfunctor X.left) {T : BigFppfOver B S hS} (x : X.left.obj (op T)) :
    x ∈ Z.obj (op T) ↔ overSpecSection B x ∈ (overSpecSubfunctor B Z).obj (op _) := by
  refine ⟨fun hx => Z.map _ hx, fun hy => ?_⟩
  have h2 : X.left.map (smallerBaseFactorHom B (Spec (.of R)) S hR hS g
      (Over.w (X.hom.app (op T) x))).op (overSpecSection B x).1 ∈ Z.obj (op T) :=
    Z.map (smallerBaseFactorHom B (Spec (.of R)) S hR hS g (Over.w (X.hom.app (op T) x))).op hy
  rwa [map_smallerBaseFactorHom_overSpecSection] at h2

/-- **The subfunctor of `X_V` determines the subfunctor of `X`.** -/
theorem le_of_overSpecSubfunctor_le
    {X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    {Z₁ Z₂ : Subfunctor X.left} (h : overSpecSubfunctor B Z₁ ≤ overSpecSubfunctor B Z₂) :
    Z₁ ≤ Z₂ := fun _ x hx =>
  (mem_iff_overSpecSection_mem B Z₂ x).2 (h _ ((mem_iff_overSpecSection_mem B Z₁ x).1 hx))

/-- `overSpecSubfunctor` is injective on subfunctors of `X`. -/
theorem overSpecSubfunctor_injective
    {X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    {Z₁ Z₂ : Subfunctor X.left} (h : overSpecSubfunctor B Z₁ = overSpecSubfunctor B Z₂) :
    Z₁ = Z₂ :=
  le_antisymm (le_of_overSpecSubfunctor_le B h.le) (le_of_overSpecSubfunctor_le B h.ge)

/-- `overSpecSubfunctor B Z` is the range of the image of the inclusion of `Z` under the inverse
of `smallerBasePresheafEquivalence`. -/
theorem overSpecSubfunctor_eq_range
    {X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (Z : Subfunctor X.left) :
    overSpecSubfunctor B Z = Subfunctor.range
      ((smallerBasePresheafEquivalence B (Spec (.of R)) S hR hS g).inverse.map
        (Over.homMk Z.ι : Over.mk (Z.ι ≫ X.hom) ⟶ X)) := by
  ext T y
  refine ⟨fun hy => ⟨⟨⟨y.1, hy⟩, y.2⟩, rfl⟩, ?_⟩
  rintro ⟨z, rfl⟩
  exact z.1.2

/-- **Closed subspaces of `X` give closed subspaces of `X_V`.** -/
theorem isClosedSubspace_overSpecSubfunctor
    {X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    {Z : Subfunctor X.left} (hZ : IsClosedSubspace B S hS Z) :
    IsClosedSubspace B (Spec (.of R)) hR (overSpecSubfunctor B Z) := by
  rw [overSpecSubfunctor_eq_range]
  exact isClosedSubspace_range_of_isClosedImmersion B (Spec (.of R)) hR _
    (isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B (Spec (.of R)) S hR hS g _ hZ.1)
    (isClosedImmersion_smallerBaseInverse_map B (Spec (.of R)) S hR hS g _ hZ.2)

/-- The subfunctor of `X` attached to a subfunctor of `X_V`: the image of its lower-shriek
extension. -/
abbrev overSpecImage {X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (Z : Subfunctor (overSpecInverse B hS hR g X)) : Subfunctor X.left :=
  Subfunctor.range ((OverShriek.relocalizePresheafFunctor g).map Z.ι ≫
    (smallerBaseInverseRelocalizeIso B (Spec (.of R)) S hR hS g X).hom)

/-- For an object `T` over `Spec R`, the comparison morphism `smallerBaseFactorHom` attached to
its own structure morphism is the identity. -/
theorem smallerBaseFactorHom_eq_id {T : BigFppfOver B (Spec (.of R)) hR} :
    smallerBaseFactorHom B (Spec (.of R)) S hR hS g (T := (Over.map g).obj T) (ψ := T.hom) rfl =
      𝟙 _ :=
  Over.OverMorphism.ext rfl

/-- **The subfunctor of `X_V` of the image is the subfunctor itself.** -/
theorem overSpecSubfunctor_overSpecImage
    {X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (Z : Subfunctor (overSpecInverse B hS hR g X)) :
    overSpecSubfunctor B (overSpecImage B Z) = Z := by
  ext T y
  change y.1 ∈ (overSpecImage B Z).obj _ ↔ y ∈ Z.obj T
  constructor
  · rintro ⟨⟨⟨ψ, ⟨s, hs⟩⟩, h⟩, hz⟩
    have hz' : X.left.map (smallerBaseFactorHom B (Spec (.of R)) S hR hS g h).op s.1 = y.1 := hz
    have hψ : ψ = T.unop.hom := by
      have e1 : (X.hom.app _ y.1).left = T.unop.hom := congrArg Over.Hom.left y.2
      have e2 := NatTrans.naturality_apply X.hom
        (smallerBaseFactorHom B (Spec (.of R)) S hR hS g h).op s.1
      rw [hz'] at e2
      have e3 : (X.hom.app _ s.1).left = ψ := congrArg Over.Hom.left s.2
      rw [← e1, e2]
      change ψ = 𝟙 _ ≫ (X.hom.app _ s.1).left
      rw [e3]
      exact (Category.id_comp ψ).symm
    subst hψ
    have hys : y = s := by
      refine Subtype.ext (hz'.symm.trans ?_)
      have hid : smallerBaseFactorHom B (Spec (.of R)) S hR hS g h = 𝟙 _ :=
        smallerBaseFactorHom_eq_id B
      exact (congrArg (fun k => X.left.map (Quiver.Hom.op k) s.1) hid).trans
        (X.left.map_id_apply _ s.1)
    rw [hys]
    exact hs
  · intro hy
    refine ⟨OverShriek.relocalizeMk g Z.toFunctor (W := op ((Over.map g).obj T.unop)) T.unop.hom
      ⟨y, hy⟩ rfl, ?_⟩
    change X.left.map (smallerBaseFactorHom B (Spec (.of R)) S hR hS g
      (T := (Over.map g).obj T.unop) (ψ := T.unop.hom) rfl).op y.1 = y.1
    rw [smallerBaseFactorHom_eq_id, op_id]
    exact X.left.map_id_apply _ y.1

/-- The map defining `overSpecImage B Z` is a closed immersion when `Z` is a closed subspace. -/
private theorem isClosedImmersion_relocalizeMap_comp_inverseIso
    {X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    {Z : Subfunctor (overSpecInverse B hS hR g X)}
    (hZ : IsClosedSubspace B (Spec (.of R)) hR Z) :
    IsClosedImmersion B S hS ((OverShriek.relocalizePresheafFunctor g).map Z.ι ≫
      (smallerBaseInverseRelocalizeIso B (Spec (.of R)) S hR hS g X).hom) :=
  isClosedImmersion_comp B S hS _ _
    ((isClosedImmersion_relocalizeMap_iff B (Spec (.of R)) S hR hS g Z.ι).2 hZ.2)
    (isClosedImmersion_of_isIso B S hS _)

/-- **Closed subspaces of `X_V` give closed subspaces of `X`.** -/
theorem isClosedSubspace_overSpecImage
    {X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    {Z : Subfunctor (overSpecInverse B hS hR g X)}
    (hZ : IsClosedSubspace B (Spec (.of R)) hR Z) :
    IsClosedSubspace B S hS (overSpecImage B Z) :=
  isClosedSubspace_range_of_isClosedImmersion B S hS _
    (isAlgebraicSpace_viewOver B (Spec (.of R)) S hR hS g _ hZ.1)
    (isClosedImmersion_relocalizeMap_comp_inverseIso B hZ)

section Properties

variable (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
  (hX : IsAlgebraicSpace B S hS X.left)

include hX in
/-- If `X` is an algebraic space over `S`, then `X_V` is an algebraic space over `Spec R`. -/
theorem isAlgebraicSpace_overSpecInverse :
    IsAlgebraicSpace B (Spec (.of R)) hR (overSpecInverse B hS hR g X) :=
  isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B (Spec (.of R)) S hR hS g X hX

include hX in
/-- **Properness of the structure morphism over a smaller base.** -/
theorem isProper_toYonedaId_overSpecInverse_iff :
    IsProper B (Spec (.of R)) hR (toYonedaId B (Spec (.of R)) hR (overSpecInverse B hS hR g X)) ↔
      IsProper B S hS X.hom := by
  rw [← isProper_relocalizeToYoneda_iff B (Spec (.of R)) S hR hS g _
    (isAlgebraicSpace_overSpecInverse B X hX), relocalizeToYoneda_smallerBaseInverse,
    isProper_isIso_comp_iff]

include hX in
/-- **Separatedness of the structure morphism over a smaller base.** -/
theorem isSeparated_toYonedaId_overSpecInverse (h : IsSeparated B S hS X.hom) :
    IsSeparated B (Spec (.of R)) hR
      (toYonedaId B (Spec (.of R)) hR (overSpecInverse B hS hR g X)) := by
  have _ := isIso_relocalizeToYoneda_yonedaId B (Spec (.of R)) S hR hS g
  have h1 : IsSeparated B S hS
      (OverShriek.relocalizeToYoneda g (overSpecInverse B hS hR g X)) := by
    rw [relocalizeToYoneda_smallerBaseInverse]
    exact isSeparated_comp B S hS _ _ (isSeparated_of_isIso B S hS _) h
  rw [← relocalizeToYoneda_eq_map_toYonedaId B (Spec (.of R)) S hR hS g] at h1
  have h2 : IsSeparated B S hS ((OverShriek.relocalizePresheafFunctor g).map
      (toYonedaId B (Spec (.of R)) hR (overSpecInverse B hS hR g X))) :=
    isSeparated_of_arrowIso B S hS _ _ (𝟙 _)
      (inv (OverShriek.relocalizeToYoneda g (yoneda.obj (Over.mk (𝟙 (B.obj hR)))))) (by simp) h1
  exact isSeparated_of_relocalize B (Spec (.of R)) hR hS g
    (relativelyRepresentable_pullbackDiagonal B (Spec (.of R)) hR _
      (isAlgebraicSpace_overSpecInverse B X hX)) h2

/-- **Finite type of the structure morphism over a smaller base.** -/
theorem isFiniteType_toYonedaId_overSpecInverse (h : IsFiniteType B S hS X.hom) :
    IsFiniteType B (Spec (.of R)) hR
      (toYonedaId B (Spec (.of R)) hR (overSpecInverse B hS hR g X)) := by
  refine ⟨?_, ?_⟩
  · refine (holdsOnEveryEtaleChart_relocalizeToYoneda_iff B (Spec (.of R)) S hR hS g _ _).1 ?_
    rw [relocalizeToYoneda_smallerBaseInverse]
    exact (Space.holdsOnEveryEtaleChart_iso_comp_iff B S hS _ _ X.hom).2 h.1
  · refine (isQuasiCompact_relocalizeToYoneda_iff B (Spec (.of R)) S hR hS g _).1 ?_
    rw [relocalizeToYoneda_smallerBaseInverse]
    exact (isQuasiCompact_isIso_comp_iff B S hS _ X.hom).2 h.2

end Properties

section SubspaceProperties

variable {X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}

/-- The subfunctor of `X_V` cut out by a subfunctor `Z` of `X` is `Z_V`. -/
def overSpecSubfunctorIso (Z : Subfunctor X.left) :
    overSpecInverse B hS hR g (Over.mk (Z.ι ≫ X.hom)) ≅ (overSpecSubfunctor B Z).toFunctor :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun z => ⟨⟨z.1.1, z.2⟩, z.1.2⟩
      invFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl })
    (fun _ => rfl)

/-- **A subfunctor proper over `V` gives a subfunctor proper over `Spec R`.** -/
theorem isProper_overSpecSubfunctor_ι_comp {Z : Subfunctor X.left}
    (hZ : IsAlgebraicSpace B S hS Z.toFunctor) (h : IsProper B S hS (Z.ι ≫ X.hom)) :
    IsProper B (Spec (.of R)) hR ((overSpecSubfunctor B Z).ι ≫
      toYonedaId B (Spec (.of R)) hR (overSpecInverse B hS hR g X)) := by
  have e : (overSpecSubfunctor B Z).ι ≫
      toYonedaId B (Spec (.of R)) hR (overSpecInverse B hS hR g X) =
        (overSpecSubfunctorIso B Z).inv ≫
          toYonedaId B (Spec (.of R)) hR (overSpecInverse B hS hR g (Over.mk (Z.ι ≫ X.hom))) := by
    ext T y
    rfl
  rw [e, isProper_isIso_comp_iff]
  exact (isProper_toYonedaId_overSpecInverse_iff B (Over.mk (Z.ι ≫ X.hom)) hZ).2 h

/-- **A subfunctor of `X_V` proper over `Spec R` gives a subfunctor of `X` proper over `V`.** -/
theorem isProper_overSpecImage_ι_comp {Z : Subfunctor (overSpecInverse B hS hR g X)}
    (hZ : IsClosedSubspace B (Spec (.of R)) hR Z)
    (h : IsProper B (Spec (.of R)) hR
      (Z.ι ≫ toYonedaId B (Spec (.of R)) hR (overSpecInverse B hS hR g X))) :
    IsProper B S hS ((overSpecImage B Z).ι ≫ X.hom) := by
  set m := (OverShriek.relocalizePresheafFunctor g).map Z.ι ≫
    (smallerBaseInverseRelocalizeIso B (Spec (.of R)) S hR hS g X).hom with hm
  have : Mono m :=
    mono_of_isClosedImmersion B S hS m (isClosedImmersion_relocalizeMap_comp_inverseIso B hZ)
  have : Mono (Subfunctor.toRange m) := mono_of_mono_fac (Subfunctor.toRange_ι m)
  have : IsIso (Subfunctor.toRange m) := isIso_of_mono_of_epi _
  have e₁ : (overSpecImage B Z).ι = inv (Subfunctor.toRange m) ≫ m :=
    (IsIso.eq_inv_comp _).2 (Subfunctor.toRange_ι m)
  have e₂ : m ≫ X.hom = OverShriek.relocalizeToYoneda g Z.toFunctor := by
    rw [hm, Category.assoc, ← relocalizeToYoneda_smallerBaseInverse]
    ext T y
    rfl
  rw [e₁, Category.assoc, e₂, isProper_isIso_comp_iff,
    isProper_relocalizeToYoneda_iff B (Spec (.of R)) S hR hS g _ hZ.1]
  have e₃ : toYonedaId B (Spec (.of R)) hR Z.toFunctor =
      Z.ι ≫ toYonedaId B (Spec (.of R)) hR (overSpecInverse B hS hR g X) := by
    ext T y
    rfl
  rw [e₃]
  exact h

end SubspaceProperties

section Fibres

/-- The scheme underlying the object `V = (Spec R ⟶ S)` is affine. -/
theorem isAffine_toScheme_overMk (g : B.obj hR ⟶ B.obj hS) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (Over.mk g)) :=
  inferInstanceAs (IsAffine (Spec (.of R)))

attribute [local instance] isAffine_toScheme_overMk isAffine_toScheme_baseObject

variable (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj (Over.mk g), ⊤))

/-- **The thickenings over `S` and over `Spec R` have the same sections.** A morphism to `V`
factors through `Spec (Γ / Jⁿ) ⟶ V` over `S` exactly when, read over `Spec R`, it factors
through `Spec (Γ / Jⁿ) ⟶ Spec R`. -/
theorem exists_adicCompletionQuotientObj_iff (T : BigFppfOver B (Spec (.of R)) hR) (n : ℕ) :
    (∃ v : (Over.map g).obj T ⟶ adicCompletionQuotientObj B S hS (Over.mk g) J n,
      v ≫ adicCompletionQuotientObjHom B S hS (Over.mk g) J n = OverShriek.overMapTautHom g T) ↔
    ∃ w : T ⟶ adicCompletionQuotientObj B (Spec (.of R)) hR (baseObject R B hR) J n,
      w ≫ adicCompletionQuotientObjHom B (Spec (.of R)) hR (baseObject R B hR) J n =
        Over.homMk T.hom (by simp) := by
  rw [exists_comp_adicCompletionQuotientObjHom_iff, exists_comp_adicCompletionQuotientObjHom_iff]
  rfl

/-- The algebraic space over `Spec R` attached to an algebraic space over `V`. -/
abbrev overSpecSpace {W : AlgebraicSpaces B S hS} (f : W ⟶ schemeSpace (Over.mk g)) :
    AlgebraicSpaces B (Spec (.of R)) hR :=
  ⟨overSpecInverse B hS hR g (Over.mk f.hom),
    isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B (Spec (.of R)) S hR hS g _ W.2⟩

/-- Its structure morphism to `Spec R`. -/
abbrev overSpecStructure {W : AlgebraicSpaces B S hS} (f : W ⟶ schemeSpace (Over.mk g)) :
    overSpecSpace B f ⟶ schemeSpace (baseObject R B hR) :=
  ObjectProperty.homMk (toYonedaId B (Spec (.of R)) hR (overSpecInverse B hS hR g (Over.mk f.hom)))

/-- **The infinitesimal fibres over `S` and over `Spec R` correspond.** -/
theorem overSpecSubfunctor_fibreThickening {W : AlgebraicSpaces B S hS}
    (f : W ⟶ schemeSpace (Over.mk g)) (n : ℕ) :
    overSpecSubfunctor B (X := Over.mk f.hom) (fibreThickening (Over.mk g) J f n).1 =
      (fibreThickening (baseObject R B hR) J (overSpecStructure B f) n).1 := by
  ext T y
  change (∃ v, v ≫ adicCompletionQuotientObjHom B S hS (Over.mk g) J n = f.hom.app _ y.1) ↔
    ∃ w, w ≫ adicCompletionQuotientObjHom B (Spec (.of R)) hR (baseObject R B hR) J n =
      Over.homMk T.unop.hom (by simp)
  rw [show f.hom.app _ y.1 = OverShriek.overMapTautHom g T.unop from y.2]
  exact exists_adicCompletionQuotientObj_iff B J T.unop n

/-- For `R` Noetherian, the scheme underlying `V = (Spec R ⟶ S)` is locally Noetherian. -/
theorem isLocallyNoetherian_toScheme_overMk [IsNoetherianRing R] (g : B.obj hR ⟶ B.obj hS) :
    _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (Over.mk g)) :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsLocallyNoetherian (Spec (.of R)))

/-- For `R` Noetherian, the scheme underlying the terminal object `baseObject R B hR` of the site
of `Spec R` is locally Noetherian. -/
theorem isLocallyNoetherian_toScheme_baseObject [IsNoetherianRing R] :
    _root_.AlgebraicGeometry.IsLocallyNoetherian
      ((BigFppfOver.toScheme B (Spec (.of R)) hR).obj (baseObject R B hR)) :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsLocallyNoetherian (Spec (.of R)))

attribute [local instance] isLocallyNoetherian_toScheme_overMk
  isLocallyNoetherian_toScheme_baseObject

/-- **Stacks 08BG over a base scheme `S`, from Stacks 08BG over a smaller affine base.** Let
`V = (Spec R ⟶ S)` with `R` Noetherian. If the closed-subspace form of Stacks 08BG holds over the
big fppf site of `Spec R` at the base, then it holds over the big fppf site of `S` at `V`: a system
of closed subspaces of an algebraic space over `V` is carried by Stacks 04SG to a system over
`Spec R` (`AlgebraicGeometry.Space.overSpecSubfunctor`), and the algebraization found there comes
back as the image of its lower-shriek extension (`AlgebraicGeometry.Space.overSpecImage`). -/
theorem closedSubspaceTowerAlgebraizes_overMk [IsNoetherianRing R]
    (h : ∀ (W' : AlgebraicSpaces B (Spec (.of R)) hR)
      (f' : W' ⟶ schemeSpace (baseObject R B hR)),
        ClosedSubspaceTowerAlgebraizes (baseObject R B hR) J f')
    {W : AlgebraicSpaces B S hS} (f : W ⟶ schemeSpace (Over.mk g)) :
    ClosedSubspaceTowerAlgebraizes (Over.mk g) J f := by
  intro hcomp hsep hft Z hZle hZcart hZ1
  let Z' : ℕ → ClosedSubspaces B (Spec (.of R)) hR (overSpecSpace B f).1 := fun n =>
    ⟨overSpecSubfunctor B (X := Over.mk f.hom) (Z n).1,
      isClosedSubspace_overSpecSubfunctor B (Z n).2⟩
  obtain ⟨Z'', hZ''p, hZ''⟩ := h (overSpecSpace B f) (overSpecStructure B f) hcomp
    (isSeparated_toYonedaId_overSpecInverse B (Over.mk f.hom) W.2 hsep)
    (isFiniteType_toYonedaId_overSpecInverse B (Over.mk f.hom) hft) Z'
    (fun n hn => by
      rw [← overSpecSubfunctor_fibreThickening]
      exact overSpecSubfunctor_mono B (hZle n hn))
    (fun n hn => by
      change overSpecSubfunctor B (X := Over.mk f.hom) (Z n).1 = _
      rw [← overSpecSubfunctor_fibreThickening, hZcart n hn]
      rfl)
    (isProper_overSpecSubfunctor_ι_comp B (Z 1).2.1 hZ1)
  refine ⟨⟨overSpecImage B Z''.1, isClosedSubspace_overSpecImage B Z''.2⟩,
    isProper_overSpecImage_ι_comp B Z''.2 hZ''p, fun n hn => ?_⟩
  refine overSpecSubfunctor_injective B (X := Over.mk f.hom) ?_
  rw [overSpecSubfunctor_inf, overSpecSubfunctor_overSpecImage, overSpecSubfunctor_fibreThickening]
  exact hZ'' n hn

end Fibres

section Tower

attribute [local instance] isAffine_toScheme_overMk isLocallyNoetherian_toScheme_overMk

variable {B}

/-- **Algebraization of compatible morphisms on the thickenings of a proper algebraic space, over
spectra.** The statement of `AlgebraicGeometry.Space.HasProperTowerAlgebraization` for the
affine objects `V = (Spec R ⟶ S)` of the big fppf site of `S` whose underlying object is a
spectrum: for `R` Noetherian, `I ⊆ Γ(Spec R)` with `Γ(Spec R)` `I`-adically complete, `p : Y ⟶ V`
proper and `gₙ : Y ×_V Spec (R / Iⁿ⁺¹) ⟶ X` compatible, there is `y : Y ⟶ X` restricting to every
`gₙ`. -/
def HasProperTowerAlgebraizationOverSpec (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (R : Type u) [CommRing R] (hR : B.Contains (Spec (.of R))) (g : B.obj hR ⟶ B.obj hS)
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj (Over.mk g), ⊤)),
    IsNoetherianRing R →
    IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj (Over.mk g), ⊤) →
    ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Y →
    ∀ (p : Y ⟶ yoneda.obj (Over.mk g)), IsProper B S hS p →
    ∀ (gs : ∀ n : ℕ,
        pullback p (yoneda.map (adicCompletionQuotientObjHom B S hS (Over.mk g) I (n + 1))) ⟶ X),
      (∀ n, properThickeningTransition I p n ≫ gs (n + 1) = gs n) →
      ∃ y : Y ⟶ X, ∀ n, pullback.fst _ _ ≫ y = gs n

/-- **`AlgebraicGeometry.Space.HasProperTowerAlgebraizationOverSpec`, given Stacks 08BG over the
big fppf sites of Noetherian affine schemes.** -/
theorem hasProperTowerAlgebraizationOverSpec_of_closedSubspaceTowerAlgebraizes
    (h08BG : ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (hR : B.Contains (Spec (.of R)))
      (J : Ideal Γ((BigFppfOver.toScheme B (Spec (.of R)) hR).obj (baseObject R B hR), ⊤))
      (W' : AlgebraicSpaces B (Spec (.of R)) hR) (f' : W' ⟶ schemeSpace (baseObject R B hR)),
        ClosedSubspaceTowerAlgebraizes (baseObject R B hR) J f')
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsSeparated B S hS (terminal.from X))
    (hlft : IsLocallyOfFiniteType B S hS (terminal.from X)) :
    HasProperTowerAlgebraizationOverSpec X := by
  intro R _ hR g I hN hcomp Y hY p hp gs hgs
  have := hN
  have := hcomp
  exact exists_comp_eq_of_properThickeningTransition (Over.mk g) I
    (fun W f => closedSubspaceTowerAlgebraizes_overMk B I (h08BG R hR I) f) hX hsep hlft hY p hp
    gs hgs

end Tower

end AlgebraicGeometry.Space
