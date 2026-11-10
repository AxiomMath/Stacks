module

public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableStackInSetoids
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeSchemePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.StackInSetoidsRepresentableBySpace

/-!
# Residual gerbes cut out by fully faithful 1-morphisms, and substacks of algebraic spaces

This file extends `StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeSchemePoint` with the facts
**Stacks 06MS** needs about residual gerbes of an algebraic space.

## Main definitions

* `AlgebraicGeometry.Stack.IsReducedUniquePointSubstackAt`: the specification
  `AlgebraicGeometry.Stack.IsResidualGerbeAt` of the residual gerbe with its local Noetherianity
  clause dropped.

## Main results

* `AlgebraicGeometry.Stack.exists_isEquivalence_essImage_of_full_of_faithful` and
  `AlgebraicGeometry.Stack.isResidualGerbeAt_essImage_of_full_of_faithful`: the essential image of
  a fully faithful 1-morphism out of the algebraic stack of a field spectrum is an algebraic
  substack satisfying condition (2) of **Stacks 06MP**, and it is the residual gerbe at the image
  of the point of the field spectrum.
* `AlgebraicGeometry.Stack`
  `.imp_of_isReducedLocallyNoetherianUniquePointSubstack_of_isMonomorphism`: the uniqueness
  argument of **Stacks 06MR** for a substack whose inclusion is a monomorphism.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_fullSubcategory`:
  a strictly full algebraic substack of an algebraic space is an algebraic space (**Stacks 04SZ**
  with the bootstrap theorem **Stacks 04S6**).
* `AlgebraicGeometry.Stack.eq_of_isReducedLocallyNoetherianUniquePointSubstack_of_representable`:
  the uniqueness assertion of **Stacks 06MR** for an algebraic space.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06MR](https://stacks.math.columbia.edu/tag/06MR)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The residual gerbe cut out by a fully faithful 1-morphism -/

/-- **A fully faithful 1-morphism out of the algebraic stack of a field spectrum cuts out a
substack of the kind Stacks 06MR produces.** Let `i` be a 1-morphism from the algebraic stack of
a field spectrum `F` to an algebraic stack `𝒳` over `S` whose underlying functor is full and
faithful. Then the essential image of `i` is closed under isomorphism, its full subcategory is an
algebraic stack, and that algebraic stack satisfies condition (2) of **Stacks 06MP**; moreover
`i` factors through the inclusion of that full subcategory by a 1-morphism whose underlying
functor is an equivalence of categories, up to a 2-isomorphism.

The factorization through the essential image is an equivalence of categories, hence an
equivalence over the big fppf site by **Stacks 003Z**; the essential image is therefore an
algebraic stack by **Stacks 03YQ**, and condition (2) of Stacks 06MP travels to it from the
algebraic stack of `F`, where the identity 1-morphism witnesses it. -/
theorem exists_isEquivalence_essImage_of_full_of_faithful
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (F : FieldSpectrum B S hS)
    (i : schemeStack.{u, w} B S hS F.base ⟶ 𝒳)
    (hfull : (CatFiberedInGroupoids.homFunctor i.hom).Full)
    (hfaithful : (CatFiberedInGroupoids.homFunctor i.hom).Faithful) :
    ∃ hP : IsAlgebraicStack.{u, w} B S hS
        (fullSubcategoryBased 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage),
      HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS
          (fullSubcategoryAlgebraicStack 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage hP) ∧
        ∃ t : schemeStack.{u, w} B S hS F.base ⟶
            fullSubcategoryAlgebraicStack 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage hP,
          Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor t.hom) ∧
            Nonempty (t ≫ fullSubcategoryInclusion 𝒳
              (CatFiberedInGroupoids.homFunctor i.hom).essImage hP ≅ i ≫ 𝟙 𝒳) := by
  classical
  set P := (CatFiberedInGroupoids.homFunctor i.hom).essImage with hPdef
  have hequiv : Functor.IsEquivalence (AlgebraicStacks.toEssImageBased i).toFunctor :=
    isEquivalence_toEssImageBased_of_full_of_faithful B S hS i hfull hfaithful
  obtain ⟨e, -⟩ := exists_basedEquivalence_functor_eq B S hS
    (schemeStack.{u, w} B S hS F.base).val (AlgebraicStacks.essImageFibered i)
    (AlgebraicStacks.toEssImageBased i) hequiv
  have hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P) :=
    (isAlgebraicStack_iff_of_equivalence B S hS e).mp
      (schemeStack.{u, w} B S hS F.base).property
  set t : schemeStack.{u, w} B S hS F.base ⟶ fullSubcategoryAlgebraicStack 𝒳 P hP :=
    Bicategory.InducedBicategory.mkHom
      (Bicategory.InducedBicategory.mkHom (AlgebraicStacks.toEssImageBased i)) with ht
  refine ⟨hP, hasLocallyOfFinitePresentationFlatFieldSpectrumCover_of_isEquivalenceFunctor B S hS
      t hequiv (hasLocallyOfFinitePresentationFlatFieldSpectrumCover_schemeStack.{u, w} B S hS F),
    t, hequiv, ⟨Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
      (AlgebraicStacks.toEssImageBasedSquareIso i))⟩⟩

/-- **A fully faithful 1-morphism out of the algebraic stack of a field spectrum cuts out the
residual gerbe at the image of its point.** Let `i` be a 1-morphism from the algebraic stack of a
field spectrum `F` to an algebraic stack `𝒳` over `S` whose underlying functor is full and
faithful, and let `x` be the image in `|𝒳|` of a point of the algebraic stack of `F`. Then the
strictly full subcategory of `𝒳` cut out by the essential image of `i` is the residual gerbe of
`𝒳` at `x`, in the sense of `AlgebraicGeometry.Stack.IsResidualGerbeAt`.

By `AlgebraicGeometry.Stack.exists_isEquivalence_essImage_of_full_of_faithful` the essential
image is an algebraic stack satisfying condition (2) of **Stacks 06MP**; the implication
(2) ⟹ (1) of Stacks 06MP makes it reduced, locally Noetherian and with a single point, and that
point lies over `x` because the factorization followed by the inclusion is 2-isomorphic to
`i`. -/
theorem isResidualGerbeAt_essImage_of_full_of_faithful
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (F : FieldSpectrum B S hS)
    (i : schemeStack.{u, w} B S hS F.base ⟶ 𝒳)
    (hfull : (CatFiberedInGroupoids.homFunctor i.hom).Full)
    (hfaithful : (CatFiberedInGroupoids.homFunctor i.hom).Faithful)
    (x : AlgebraicStacks.points B S hS 𝒳)
    (q : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS F.base))
    (hx : AlgebraicStacks.pointsMap B S hS i q = x) :
    IsResidualGerbeAt B S hS 𝒳 x (CatFiberedInGroupoids.homFunctor i.hom).essImage := by
  classical
  obtain ⟨hP, hcov, t, -, ⟨hκ⟩⟩ :=
    exists_isEquivalence_essImage_of_full_of_faithful.{u, w} B S hS 𝒳 F i hfull hfaithful
  obtain ⟨⟨hred, -, hsub⟩, hln⟩ :=
    isReducedLocallyNoetherianWithUniquePoint_of_locallyOfFinitePresentation.{u, w} B S hS
      (fullSubcategoryAlgebraicStack 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage hP) hcov
  refine ⟨inferInstance, hP, hred, hln,
    AlgebraicStacks.pointsMap B S hS t q, fun z' => hsub.elim z' _, ?_⟩
  calc AlgebraicStacks.pointsMap B S hS
          (fullSubcategoryInclusion 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage hP)
          (AlgebraicStacks.pointsMap B S hS t q)
      = AlgebraicStacks.pointsMap B S hS
          (t ≫ fullSubcategoryInclusion 𝒳
            (CatFiberedInGroupoids.homFunctor i.hom).essImage hP) q := by
        simp only [AlgebraicStacks.pointsMap_comp, Function.comp_apply]
    _ = AlgebraicStacks.pointsMap B S hS (i ≫ 𝟙 𝒳) q := by
        rw [AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS hκ.hom]
    _ = x := by
        simp only [AlgebraicStacks.pointsMap_comp, Function.comp_apply,
          AlgebraicStacks.pointsMap_id, id_eq]
        exact hx

/-! ### The uniqueness argument of Stacks 06MR for a monomorphic inclusion -/

/-- **The uniqueness argument of Stacks 06MR, in the asymmetric form, for a target whose
inclusion is known to be a monomorphism.** Let `P` and `Q` both cut out a strictly full algebraic
subcategory of `𝒵` satisfying condition (2) of **Stacks 06MP**, let `|𝒵|` be a subsingleton, and
let the inclusion of the full subcategory of `Q` be a monomorphism of algebraic stacks
(**Stacks 04ZW**). Then every object of `𝒵` satisfying `P` satisfies `Q`.

This is the argument of
`AlgebraicGeometry.Stack.imp_of_isReducedLocallyNoetherianUniquePointSubstack`, which needs the
monomorphy of the inclusion of `Q` only, and takes it from the granted
`AlgebraicGeometry.Stack.HasRepresentableSubstackInclusions`. -/
theorem imp_of_isReducedLocallyNoetherianUniquePointSubstack_of_isMonomorphism
    (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (hsub : Subsingleton (AlgebraicStacks.points B S hS 𝒵))
    {P Q : ObjectProperty 𝒵.val.val.obj}
    (hP : IsReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒵 P)
    (hQ : IsReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒵 Q)
    (hQmono : AlgebraicStacks.IsMonomorphism B S hS
      (fullSubcategoryInclusion 𝒵 Q hQ.2.choose))
    (X : 𝒵.val.val.obj) (hX : P X) : Q X := by
  obtain ⟨-, hPalg, hPcov⟩ := hP
  obtain ⟨hQiso, hQalg, hQcov⟩ := hQ
  have hWmono : AlgebraicStacks.IsMonomorphism B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS (fullSubcategoryInclusion 𝒵 P hPalg)
        (fullSubcategoryInclusion 𝒵 Q hQalg)).fst :=
    AlgebraicStacks.isMonomorphism_fst_twoFibreProductSquareAlgebraicStacks B S hS
      (fullSubcategoryInclusion 𝒵 P hPalg) (fullSubcategoryInclusion 𝒵 Q hQalg) hQmono
  obtain ⟨zP⟩ := (isReducedLocallyNoetherianWithUniquePoint_of_locallyOfFinitePresentation
    B S hS (fullSubcategoryAlgebraicStack 𝒵 P hPalg) hPcov).1.2.1
  obtain ⟨zQ⟩ := (isReducedLocallyNoetherianWithUniquePoint_of_locallyOfFinitePresentation
    B S hS (fullSubcategoryAlgebraicStack 𝒵 Q hQalg) hQcov).1.2.1
  obtain ⟨w, -, -⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS (fullSubcategoryInclusion 𝒵 P hPalg)
      (fullSubcategoryInclusion 𝒵 Q hQalg))
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
      (fullSubcategoryInclusion 𝒵 P hPalg) (fullSubcategoryInclusion 𝒵 Q hQalg))
    zP zQ (Subsingleton.elim _ _)
  rcases isEmpty_points_or_isEquivalenceOver_of_isMonomorphism B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS (fullSubcategoryInclusion 𝒵 P hPalg)
      (fullSubcategoryInclusion 𝒵 Q hQalg)).pt
    (fullSubcategoryAlgebraicStack 𝒵 P hPalg)
    (twoFibreProductSquareAlgebraicStacks B S hS (fullSubcategoryInclusion 𝒵 P hPalg)
      (fullSubcategoryInclusion 𝒵 Q hQalg)).fst hWmono hPcov with hempty | hne
  · exact (hempty.false w).elim
  · have e := hne.some
    exact Q.prop_of_iso
      ((e.inv.obj ⟨X, hX⟩).iso.symm.trans (P.ι.mapIso (e.counitIso.app ⟨X, hX⟩)))
      (e.inv.obj ⟨X, hX⟩).y.property

/-! ### The residual gerbe without local Noetherianity -/

/-- **The specification of the residual gerbe without local Noetherianity.** A property of the
objects of `𝒳` is closed under isomorphism, its full subcategory is a reduced algebraic stack, and
that subcategory has exactly one point, lying over `x`: this is
`AlgebraicGeometry.Stack.IsResidualGerbeAt` with its local Noetherianity clause dropped, the
naive notion of a residual gerbe discussed at the start of Section 06ML. -/
abbrev IsReducedUniquePointSubstackAt
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val (Classical.choose 𝒳.property))
    (P : ObjectProperty 𝒳.val.val.obj) : Prop :=
  P.IsClosedUnderIsomorphisms ∧
    ∃ hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P),
      IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 P hP) ∧
        HasUniquePointOver B S hS (fullSubcategoryInclusion 𝒳 P hP) x

/-- The residual gerbe meets the specification without local Noetherianity. -/
theorem IsResidualGerbeAt.isReducedUniquePointSubstackAt
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {x : points B S hS 𝒳.val.val (Classical.choose 𝒳.property)}
    {P : ObjectProperty 𝒳.val.val.obj} (h : IsResidualGerbeAt B S hS 𝒳 x P) :
    IsReducedUniquePointSubstackAt B S hS 𝒳 x P :=
  ⟨h.1, h.2.choose, h.2.choose_spec.1, h.2.choose_spec.2.2⟩

/-! ### Strictly full algebraic substacks of an algebraic space -/

/-- **A strictly full algebraic substack of a stack in setoids is a stack in setoids.** Let `𝒳`
be an algebraic stack over `S` which is a stack in setoids, for instance one represented by an
algebraic space, and let `P` cut out a full subcategory which is an algebraic stack. Then that
full subcategory is a stack in setoids: it is a stack, being algebraic, and its fibres embed fully
faithfully into those of `𝒳`, which are thin groupoids. -/
theorem isStackInSetoids_fullSubcategory
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : 𝒳.val.val.p.IsStackInSetoids (BigFppfOver.topology B S hS))
    (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)) :
    (fullSubcategoryAlgebraicStack 𝒳 P hP).val.val.p.IsStackInSetoids
      (BigFppfOver.topology B S hS) := by
  have hrfl : P.ι ⋙ 𝒳.val.val.p = P.ι ⋙ 𝒳.val.val.p := rfl
  have hF := Functor.Fiber.faithful_mapOfComp (p := P.ι ⋙ 𝒳.val.val.p)
    (q := 𝒳.val.val.p) (F := P.ι) hrfl
  refine ⟨isStack_of_isAlgebraicStack B S hS hP, fun V ↦ ?_, fun V ↦ ?_⟩
  · have hL := Functor.Fiber.full_mapOfComp (p := P.ι ⋙ 𝒳.val.val.p) (q := 𝒳.val.val.p)
      (F := P.ι) hrfl V
    have := h𝒳.fiber_isGroupoid V
    exact ⟨fun f ↦ isIso_of_fully_faithful
      (Functor.Fiber.mapOfComp (P.ι ⋙ 𝒳.val.val.p) 𝒳.val.val.p P.ι hrfl V) f⟩
  · have := h𝒳.fiber_isThin V
    exact fun a b ↦ ⟨fun f g ↦
      (Functor.Fiber.mapOfComp (P.ι ⋙ 𝒳.val.val.p) 𝒳.val.val.p P.ι hrfl V).map_injective
        (Subsingleton.elim _ _)⟩

/-- **A strictly full algebraic substack of an algebraic space is an algebraic space.** Let `𝒳`
be an algebraic stack over `S` represented by an algebraic space, and let `P` cut out a full
subcategory which is an algebraic stack. Then that full subcategory is represented by an
algebraic space: it is a stack in setoids by
`AlgebraicGeometry.Stack.isStackInSetoids_fullSubcategory`, and an algebraic stack which is a
stack in setoids is an algebraic space by the implication (1) ⟹ (3) of **Stacks 04SZ**,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isStackInSetoids`. -/
theorem isRepresentableByAlgebraicSpace_fullSubcategory
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳.val)
    (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)) :
    IsRepresentableByAlgebraicSpace B S hS (fullSubcategoryAlgebraicStack 𝒳 P hP).val :=
  isRepresentableByAlgebraicSpace_of_isStackInSetoids B S hS _ hP
    (isStackInSetoids_fullSubcategory B S hS 𝒳
      (isStackInSetoids_of_isRepresentableByAlgebraicSpace B S hS 𝒳.val h𝒳) P hP)

/-- **Stacks 06MR, the uniqueness assertion, for an algebraic space.** Let `𝒳` be an algebraic
stack over `S` with at most one point (the argument does not use that `𝒳` is represented by an
algebraic space). Then at most one strictly full subcategory of `𝒳` is an algebraic stack
satisfying condition (2) of **Stacks 06MP**.

This is the uniqueness argument of Stacks 06MR, whose input — that the inclusions of the two
substacks are monomorphisms — is
`AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_fullSubcategoryInclusion`. -/
theorem eq_of_isReducedLocallyNoetherianUniquePointSubstack_of_representable
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hsub : Subsingleton (AlgebraicStacks.points B S hS 𝒳))
    {P Q : ObjectProperty 𝒳.val.val.obj}
    (hP : IsReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒳 P)
    (hQ : IsReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒳 Q) : P = Q :=
  funext fun X ↦ propext
    ⟨imp_of_isReducedLocallyNoetherianUniquePointSubstack_of_isMonomorphism.{u, w} B S hS 𝒳 hsub
        hP hQ (AlgebraicStacks.isMonomorphism_fullSubcategoryInclusion B S hS 𝒳 Q hQ.2.choose) X,
      imp_of_isReducedLocallyNoetherianUniquePointSubstack_of_isMonomorphism.{u, w} B S hS 𝒳 hsub
        hQ hP (AlgebraicStacks.isMonomorphism_fullSubcategoryInclusion B S hS 𝒳 P hP.2.choose) X⟩

end AlgebraicGeometry.Stack

end
