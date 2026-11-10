module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SectionOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjectiveSchemeTests
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism

/-!
# Sections of an étale morphism extend across a thickening of unbounded order

Let `G ⊂ V` be a thickening of algebraic spaces over `S` — a closed subspace with the same
points, with no bound on the order — and let `g : C ⟶ V` be étale. A section of `g` over `G`
then extends to a section of `g` over `V` in exactly one way.

This is the order-free replacement for the lifting theorem of Stacks 0611, which is available
only at finite order because formal étaleness is a condition about square-zero extensions. The
target here is required to be *étale* and not merely formally étale, and that is what buys the
order: an étale morphism has an open-immersion relative diagonal, so a section is an open
immersion onto an open subspace, and open subspaces of a thickening are the open subspaces of
the ambient space (Stacks 05ZP) with no order hypothesis at all.

## Main results

* `AlgebraicGeometry.Space.isIso_of_isEtale_of_isSurjective_baseChange_isIso`: an étale
  morphism whose base change along a surjective morphism is an isomorphism is an isomorphism.
* `AlgebraicGeometry.Space.hom_ext_of_isThickening_of_isEtale`: two morphisms over a common
  étale target which agree on a thickening of their source are equal.
* `AlgebraicGeometry.Space.existsUnique_section_of_isThickening`: the unique extension of a
  section of an étale morphism across a thickening of unbounded order.
* `AlgebraicGeometry.Space.existsUnique_lift_of_isThickening`: the same in the shape of a
  lifting problem — **Stacks 0611 for an étale target and a thickening of unbounded order.**

## Implementation notes

The section to be extended is turned into an open subspace in three steps. It factors through
the inverse image `C ×_V G` of the thickening, which is a thickening of `C` by the order-free
half of Stacks 09ZX (`AlgebraicGeometry.Space.isThickening_preimage`), as a section of the
projection `C ×_V G ⟶ G`; that projection is a base change of `g`, hence étale, so the section
is an open immersion by Stacks 05W1 in the form
`AlgebraicGeometry.Space.isOpenImmersion_of_isEtale_of_section`; and its range is therefore an
open subspace of `C ×_V G`.

Stacks 05ZP, `AlgebraicGeometry.Space.exists_isOpenSubspace_isPullback_ι_of_isThickening`,
spreads that open subspace to an open subspace `Ω ⊂ C` with `Ω ×_C (C ×_V G) = Ω ×_V G` the
one we started from. The composite `Ω ⟶ C ⟶ V` is étale, and its base change along the
inclusion of the thickening is the inverse of the section, hence an isomorphism; so it is an
isomorphism, and its inverse followed by `Ω ⟶ C` is the section sought.

Descent of the isomorphism from the thickening to the ambient space is
`isIso_of_isEtale_of_isSurjective_baseChange_isIso`: universal injectivity is tested on one
surjective scheme chart by Stacks 03MX
(`AlgebraicGeometry.Space.universallyInjective_tfae`, the fourth clause), where the base change
is a monomorphism because it is an isomorphism, and then Stacks 05W5
(`AlgebraicGeometry.Space.isIso_of_isEtale_of_universallyInjective_of_isSurjective`) applies.
No order enters anywhere.

Uniqueness is separated out as `hom_ext_of_isThickening_of_isEtale`, which is the statement
that an étale target is *unramified*: the two morphisms assemble into a morphism to the fibre
square, whose restriction to the thickening factors through the relative diagonal; the diagonal
is an open immersion by Stacks 05W1, the thickening is surjective on points, so the factoring
already holds on the ambient space by Stacks 03IE.

## References

* [Stacks Project, Tag 05ZP](https://stacks.math.columbia.edu/tag/05ZP)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
* [Stacks Project, Tag 03MX](https://stacks.math.columbia.edu/tag/03MX)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 0611](https://stacks.math.columbia.edu/tag/0611)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_EtaleSectionExtension :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_EtaleSectionExtension
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_EtaleSectionExtension B S hS).has_limit _

/-! ### Descent of isomorphy along a surjective base change -/

/-- A morphism whose base change along a surjective morphism is an isomorphism is surjective:
a point of the target lifts to the surjective morphism, is carried into the fibre product by
the inverse of the base change, and projects to a preimage. -/
private theorem isSurjective_of_isPullback_of_isIso
    {P X A' A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {fst : P ⟶ A'} {snd : P ⟶ X} {p : A' ⟶ A} {g : X ⟶ A}
    (sq : IsPullback fst snd p g) (hfst : IsIso fst) (hp : IsSurjective B S hS p) :
    IsSurjective B S hS g := by
  have := hfst
  intro y
  obtain ⟨y', hy'⟩ := hp y
  obtain ⟨x, hx⟩ := pointsMap_surjective_of_isIso B S hS fst y'
  refine ⟨pointsMap B S hS P snd x, ?_⟩
  have h1 : pointsMap B S hS P (fst ≫ p) x = pointsMap B S hS P (snd ≫ g) x :=
    congrArg (fun k ↦ pointsMap B S hS P k x) sq.w
  rw [pointsMap_comp, pointsMap_comp] at h1
  simp only [Function.comp_apply] at h1
  rw [hx, hy'] at h1
  exact h1.symm

/-- **An étale morphism whose base change along a surjective morphism is an isomorphism is an
isomorphism.** No order and no flatness hypothesis on the surjection is needed.

Universal injectivity is tested, by Stacks 03MX, on a single surjective chart of the target of
the surjection: the base change there is an isomorphism, hence a monomorphism, hence
universally injective. Surjectivity is read off the fibre product. Stacks 05W5 then applies. -/
theorem isIso_of_isEtale_of_isSurjective_baseChange_isIso
    {X A' A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hA' : IsAlgebraicSpace B S hS A')
    (hA : IsAlgebraicSpace B S hS A) (p : A' ⟶ A) (g : X ⟶ A)
    (hp : IsSurjective B S hS p) (hg : IsEtale B S hS g)
    (hbase : IsIso (pullback.fst p g)) : IsIso g := by
  have := hbase
  obtain ⟨U, u, hu, -⟩ := hA'.exists_atlas
  have huPts : IsSurjective B S hS u :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS A' hA' U u).mp hu
  have hgZ : IsSurjective B S hS (u ≫ p) := by
    change Function.Surjective (pointsMap B S hS (yoneda.obj U) (u ≫ p))
    rw [pointsMap_comp]
    exact hp.comp huPts
  have hui : UniversallyInjective B S hS (pullback.snd g (u ≫ p)) := by
    have hinner : IsIso (pullback.fst u (pullback.fst p g)) := inferInstance
    set e : pullback u (pullback.fst p g) ≅ pullback g (u ≫ p) :=
      (pullbackRightPullbackFstIso p g u).trans (pullbackSymmetry g (u ≫ p)).symm with he
    have heproj : e.hom ≫ pullback.snd g (u ≫ p) = pullback.fst u (pullback.fst p g) := by
      simp [he]
    have hcomp : IsIso (e.hom ≫ pullback.snd g (u ≫ p)) := by rw [heproj]; exact hinner
    have htarget : IsIso (pullback.snd g (u ≫ p)) := IsIso.of_isIso_comp_left e.hom _
    exact universallyInjective_of_mono B S hS _ (IsIso.mono_of_iso _)
  have hwit : ∃ (Z : BigFppfOver B S hS) (q : yoneda.obj Z ⟶ A),
      IsSurjective B S hS q ∧ UniversallyInjective B S hS (pullback.snd g q) :=
    ⟨U, u ≫ p, hgZ, hui⟩
  have hInj : UniversallyInjective B S hS g :=
    ((universallyInjective_tfae B S hS hX hA g).out 4 1).mp hwit
  have hSurj : IsSurjective B S hS g :=
    isSurjective_of_isPullback_of_isIso B S hS (IsPullback.of_hasPullback p g) hbase hp
  exact isIso_of_isEtale_of_universallyInjective_of_isSurjective B S hS hX hA g hg hInj hSurj

/-! ### Uniqueness of a lift across a thickening into an étale target -/

/-- The inverse of the corestriction of a morphism to its range, followed by the morphism, is the
inclusion of the range. -/
private theorem inv_toRange_comp_eq_ι {F₀ G₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F₀ ⟶ G₀)
    [IsIso (Subfunctor.toRange p)] : inv (Subfunctor.toRange p) ≫ p = (Subfunctor.range p).ι :=
  (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι _).symm

/-- The range of an open immersion whose source is an algebraic space is an open subspace. -/
private theorem isOpenSubspace_range_of_isOpenImmersion'
    {F₀ G₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF₀ : IsAlgebraicSpace B S hS F₀) (p : F₀ ⟶ G₀)
    (hp : IsOpenImmersion B S hS p) : IsOpenSubspace B S hS (Subfunctor.range p) := by
  have hmono : Mono p :=
    mono_of_isImmersion B S hS (isImmersion_of_isOpenImmersion B S hS hp)
  have hiso : IsIso (Subfunctor.toRange p) := inferInstance
  refine ⟨isAlgebraicSpace_of_iso B S hS (asIso (Subfunctor.toRange p)) hF₀, ?_⟩
  exact inv_toRange_comp_eq_ι B S hS p ▸
    MorphismProperty.RespectsIso.precomp _ (asIso (Subfunctor.toRange p)).inv p hp

/-- **Two morphisms into an étale algebraic space over a common target which agree on a
thickening of their source are equal.** No bound on the order of the thickening.

The pair assembles into a morphism to the fibre square of the étale morphism; its restriction
to the thickening factors through the relative diagonal, which is an open immersion because an
étale morphism is unramified (Stacks 05W1). The thickening is surjective on points, so the
point set of the whole source already lands in the diagonal, and Stacks 03IE factors the
morphism through it; both components of a morphism factoring through the diagonal agree. -/
theorem hom_ext_of_isThickening_of_isEtale
    {V A C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hA : IsAlgebraicSpace B S hS A)
    (hC : IsAlgebraicSpace B S hS C) {G : Subfunctor V}
    (hG : IsThickening B S hS (⟨V, hV⟩ : AlgebraicSpaces B S hS) G)
    (w : C ⟶ A) (hw : IsEtale B S hS w) (α β : V ⟶ C)
    (hαβ : α ≫ w = β ≫ w) (h : G.ι ≫ α = G.ι ≫ β) : α = β := by
  have hΔopen : IsOpenImmersion B S hS (pullback.diagonal w) :=
    isOpenImmersion_diagonal_of_isUnramified B S hS hC hA w (isUnramified_of_isEtale B S hS hw)
  have hΔmono : Mono (pullback.diagonal w) :=
    mono_of_isImmersion B S hS (isImmersion_of_isOpenImmersion B S hS hΔopen)
  have hPB : IsAlgebraicSpace B S hS (pullback w w) :=
    isAlgebraicSpace_pullback B S hS w w hC hC hA
  have hRopen : IsOpenSubspace B S hS (Subfunctor.range (pullback.diagonal w)) :=
    isOpenSubspace_range_of_isOpenImmersion' B S hS hC _ hΔopen
  have hres : G.ι ≫ pullback.lift α β hαβ = (G.ι ≫ α) ≫ pullback.diagonal w := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst,
        Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd,
        Category.comp_id, h]
  have hpts : Set.range (pointsMap B S hS V (pullback.lift α β hαβ)) ⊆
      Set.range (pointsMap B S hS (Subfunctor.range (pullback.diagonal w)).toFunctor
        (Subfunctor.range (pullback.diagonal w)).ι) := by
    rw [AlgebraicGeometry.Space.range_pointsMap_ι_range B S hS (pullback.diagonal w)]
    have hsurjG : Function.Surjective (pointsMap B S hS G.toFunctor G.ι) := hG.2
    rintro z ⟨y, rfl⟩
    obtain ⟨y₀, rfl⟩ := hsurjG y
    have hz : pointsMap B S hS V (pullback.lift α β hαβ)
        (pointsMap B S hS G.toFunctor G.ι y₀) =
        pointsMap B S hS G.toFunctor (G.ι ≫ pullback.lift α β hαβ) y₀ := by
      rw [pointsMap_comp]; rfl
    rw [hz, hres, pointsMap_comp]
    exact ⟨pointsMap B S hS G.toFunctor (G.ι ≫ α) y₀, rfl⟩
  obtain ⟨k, hk⟩ :=
    (factorsThrough_openSubspace_iff_points B S hS hPB hV _ hRopen
      (pullback.lift α β hαβ)).2 hpts
  have hiso : IsIso (Subfunctor.toRange (pullback.diagonal w)) := inferInstance
  have hfac : pullback.lift α β hαβ = (k ≫ inv (Subfunctor.toRange (pullback.diagonal w))) ≫
      pullback.diagonal w := by
    rw [Category.assoc, inv_toRange_comp_eq_ι]
    exact hk.symm
  have hproj : ∀ π : pullback w w ⟶ C, pullback.diagonal w ≫ π = 𝟙 C →
      pullback.lift α β hαβ ≫ π = k ≫ inv (Subfunctor.toRange (pullback.diagonal w)) := by
    intro π hπ
    rw [hfac, Category.assoc, Category.assoc, hπ, Category.comp_id]
  exact ((pullback.lift_fst α β hαβ).symm.trans (hproj _ (pullback.diagonal_fst w))).trans
    ((pullback.lift_snd α β hαβ).symm.trans (hproj _ (pullback.diagonal_snd w))).symm

/-! ### Extension of a section of an étale morphism across a thickening -/

/-! ### The lifting theorem -/

/-- **Stacks 0611 for an étale morphism and a thickening of unbounded order.** An étale
morphism `f : X ⟶ Y` of algebraic spaces over `S` admits exactly one dotted arrow in a solid
square whose right-hand side is a thickening `T ⊂ T'` of algebraic spaces, with no bound on the
order of the thickening.

This is the order-free counterpart of
`AlgebraicGeometry.Space.FormallyEtale.existsUnique_lift_of_isNthOrderThickening`, which is
Stacks 0611 at order `n` for a merely formally étale `f`. Formal étaleness cannot reach an
arbitrary thickening — its defining ideal is nil but need not be nilpotent, so the tower of
infinitesimal neighbourhoods has no global exponent to induct on — and étaleness is what
replaces it: a lift is a section of the base change `X ×_Y T' ⟶ T'`, which is étale, and
sections of an étale morphism extend uniquely across any thickening by
`AlgebraicGeometry.Space.existsUnique_section_of_isThickening`. -/
@[sga "1 I 5.6" "more general", sga "4 XIII 1.5" "more general"]
theorem existsUnique_lift_of_isThickening
    {X Y T' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (T : Subfunctor T'.obj) (hT : IsThickening B S hS T' T)
    (a : T.toFunctor ⟶ X.obj) (b : T'.obj ⟶ Y.obj) (hsq : a ≫ f.hom = T.ι ≫ b) :
    ∃! c : T'.obj ⟶ X.obj, T.ι ≫ c = a ∧ c ≫ f.hom = b := by
  -- The base change of `f` along `b`, an étale algebraic space over `T'`.
  have hC : IsAlgebraicSpace B S hS (pullback f.hom b) :=
    isAlgebraicSpace_pullback B S hS f.hom b X.property T'.property Y.property
  have hgEtale : IsEtale B S hS (pullback.snd f.hom b) := by
    refine isEtale_of_isPullback B S hS
      (X' := (⟨pullback f.hom b, hC⟩ : AlgebraicSpaces B S hS)) (X := X) (Z := T') (Y := Y)
      (ObjectProperty.homMk (pullback.fst f.hom b))
      (ObjectProperty.homMk (pullback.snd f.hom b)) f (ObjectProperty.homMk b) ?_ hf
    exact IsPullback.of_map_of_faithful
      (ObjectProperty.ι (AlgebraicGeometry.IsAlgebraicSpace B S hS))
      (IsPullback.of_hasPullback f.hom b)
  -- A lift is the same datum as a section of that base change.
  have hkey : ∀ c : T'.obj ⟶ X.obj, (T.ι ≫ c = a ∧ c ≫ f.hom = b) →
      ∃ α : T'.obj ⟶ pullback f.hom b, α ≫ pullback.snd f.hom b = 𝟙 T'.obj ∧
        T.ι ≫ α = pullback.lift a T.ι hsq ∧ α ≫ pullback.fst f.hom b = c := by
    rintro c ⟨hc1, hc2⟩
    refine ⟨pullback.lift c (𝟙 T'.obj) (by rw [hc2, Category.id_comp]), pullback.lift_snd _ _ _,
      ?_, pullback.lift_fst _ _ _⟩
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hc1]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]
  obtain ⟨α, ⟨hα1, hα2⟩, hαuniq⟩ :=
    existsUnique_section_of_isThickening B S hS T'.property hC hT
      hgEtale (pullback.lift a T.ι hsq) (pullback.lift_snd _ _ _)
  refine ⟨α ≫ pullback.fst f.hom b, ⟨?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, hα2, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hα1, Category.id_comp]
  · intro c hc
    obtain ⟨β, hβ1, hβ2, hβ3⟩ := hkey c hc
    rw [← hβ3, hαuniq β ⟨hβ1, hβ2⟩]

end AlgebraicGeometry.Space

end
