module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Assembly.Relativize
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineIntersections

/-!
# Separatedness of a formal algebraic space, tested on its reduction

Let `S` be a scheme contained in a big fppf site `B` and let `X` be a formal algebraic space
over `S`. **Stacks 0AJ6** says that the following are equivalent: the reduction of `X` is a
separated algebraic space; and for every pair of affine schemes `U`, `V` over `X` the fibre
product `U ×_X V` is affine and the canonical map `𝒪(U) ⊗_ℤ 𝒪(V) ⟶ 𝒪(U ×_X V)` is surjective.

This file proves the implication from the second condition to the first. The argument is the
one of the source: a fibre product over the reduction of `X` is a fibre product over `X`
itself, the inclusion of the reduction being a monomorphism, so the affineness and
surjectivity condition for `X` restricts to the same condition for the reduction, and for an
algebraic space that condition is separatedness by **Stacks 0AHS**.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasAffineIntersectionsULift`: clause (2) of Stacks 0AJ6 for a
  presheaf in the value universe of the formal algebraic spaces — the affineness and
  surjectivity condition on every object of the site representing the fibre product of two
  affine test objects.

## Main results

* `AlgebraicGeometry.FormalSpace.isAbsolutelySeparated_reduction_of_hasAffineIntersectionsULift`:
  **Stacks 0AJ6, the implication (2) ⟹ (1)**.
* `AlgebraicGeometry.FormalSpace.mono_hom_of_isReduction`: the inclusion of a reduction is a
  monomorphism of presheaves.
* `AlgebraicGeometry.FormalSpace.hasAffineIntersectionsULift_of_mono`: clause (2) passes along
  a monomorphism into a presheaf, which is the whole of the implication at the level of the
  test data.
* `AlgebraicGeometry.FormalSpace.hasAffineIntersectionsULift_comp_uliftFunctor_iff`: clause (2)
  for the universe lift of a presheaf of `Type u` is the affine-intersection condition of
  Stacks 0AHS for that presheaf.

## Implementation notes

The implication is read here against an arbitrary reduction of `X`, a morphism satisfying
`AlgebraicGeometry.FormalSpace.IsReduction`, exactly as in Stacks 0GB8 in
`StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction` and as in Stacks 0AJ5 in
`StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionQuasiSeparated`. That is more general than
the statement about the reduction Stacks 0AIN produces, which it implies — see
`…exists_isReduction_and_isAbsolutelySeparated_iff_hasAffineIntersectionsULift` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSeparatedConverse`, which is Stacks 0AJ6
itself — and it needs no choice.

Clause (1) of Stacks 0AJ6 is separatedness of the reduction *as an algebraic space*, and an
algebraic space over `S` is in this library a presheaf with values in `Type u`, the value
universe of the site, whereas a formal algebraic space is a sheaf of `Type (u + 1)`. The
reduction is therefore presented by a presheaf of `Type u` together with an isomorphism from
its universe lift, and clause (1) is `AlgebraicGeometry.Space.IsAbsolutelySeparated` of that
presheaf.

Clause (2) is the condition already recorded for sheaves as
`AlgebraicGeometry.FormalSpace.IsSeparated` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProduct`, where it is what Stacks 0AN3
consumes; `AlgebraicGeometry.FormalSpace.HasAffineIntersectionsULift` is the same condition
read on the underlying presheaf against the universe-lifted Yoneda embedding, which is the
form that compares with the condition of Stacks 0AHS for a presheaf of `Type u`. The map on
global sections is `AlgebraicGeometry.globalSectionsTensorLift`, the map the carrier of
Stacks 0AHS uses, and it is the same map as the one in `IsSeparated` by definition.

The fibre product of the two test objects is not named by a construction but specified by a
cartesian square over the universe-lifted Yoneda embedding together with an object of the site
representing it, as in `AlgebraicGeometry.Space.HasAffineIntersections`, so neither affineness
nor the surjectivity depends on the choice of a representing object. The condition does not
assert that the fibre product *is* representable: that is Stacks 0AIP, and the source's proof
of 0AJ6 appeals to it only to know that the object whose affineness is at stake is a scheme.
The carrier of Stacks 0AHS reads the identical clause the same way. Stacks 0AIP *is* available
at an arbitrary formal algebraic space, as
`AlgebraicGeometry.FormalSpace.relativelyRepresentable_diag_of_isFormalAlgebraicSpace`
(`StacksFrontier/AlgebraicGeometry/FormalSpace/DiagonalRepresentable.lean:1057`), so the clause in
the source's own form is stated and proved in
`StacksFrontier/AlgebraicGeometry/FormalSpace/ReductionSeparatedRepresentable.lean`; the weaker
reading is kept here because the declarations below are stated against it.

The converse implication, from separatedness of the reduction to clause (2), is proved in
`StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSeparatedConverse`, which also assembles
the two implications into the equivalence Stacks 0AJ6 asserts, as
`AlgebraicGeometry.FormalSpace.isAbsolutelySeparated_reduction_iff_hasAffineIntersectionsULift`.
The source's route through Stacks 07VT, 01KR, 01WM, 01WJ and 04VT is shortened there: affineness
of `U ×_X V` is affineness of a thickening of an affine scheme, which this library carries as
Stacks 06AD rather than in the algebraic-space form of Stacks 07VT, and the surjectivity on
global sections comes from `𝒪(U ×_X V)` being integral over the image of `𝒪(U) ⊗_ℤ 𝒪(V)` —
every section differs from a pulled-back one by a nilpotent — so that the universal closedness
of the source's argument, and with it Stacks 01WM, is not needed.

The inclusion of a reduction is a monomorphism because it is representable and every
represented base change of it is a closed immersion of schemes: a section of the target over
an object of the site then has at most one lift, the base change of the inclusion along that
section being a monomorphism which the lift splits.

## References

* [Stacks Project, Tag 0AHS](https://stacks.math.columbia.edu/tag/0AHS)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AJ5](https://stacks.math.columbia.edu/tag/0AJ5)
* [Stacks Project, Tag 0AJ6](https://stacks.math.columbia.edu/tag/0AJ6)
* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Clause (2) in the value universe of the formal algebraic spaces -/

/-- The universe lift of presheaves on the big fppf site of `S` from the value universe of the
site to the value universe of the formal algebraic spaces. -/
private abbrev affUpFunctor : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⥤
    ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) :=
  (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
    uliftFunctor.{u + 1}

/-- **Clause (2) of Stacks 0AJ6.** For every pair of objects `U`, `V` of the big fppf site of
`S` with affine underlying scheme and every pair of morphisms `h_U ⟶ X`, `h_V ⟶ X` out of
their universe-lifted Yoneda presheaves, every object of the site representing the fibre
product `U ×_X V` has affine underlying scheme, and the canonical map
`Γ(U, ⊤) ⊗_ℤ Γ(V, ⊤) ⟶ Γ(U ×_X V, ⊤)` of `AlgebraicGeometry.globalSectionsTensorLift` is
surjective. -/
abbrev HasAffineIntersectionsULift (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∀ (U V Q : BigFppfOver B S hS)
    (a : (uliftYoneda.{u + 1}).obj U ⟶ X) (b : (uliftYoneda.{u + 1}).obj V ⟶ X)
    (p : Q ⟶ U) (q : Q ⟶ V),
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
    IsPullback ((uliftYoneda.{u + 1}).map p) ((uliftYoneda.{u + 1}).map q) a b →
    IsAffine ((BigFppfOver.toScheme B S hS).obj Q) ∧
      Function.Surjective (globalSectionsTensorLift ((BigFppfOver.toScheme B S hS).map p)
        ((BigFppfOver.toScheme B S hS).map q))

/-- Clause (2) passes along a monomorphism: a cartesian square over a cospan stays cartesian
after composing both its legs with a monomorphism, so a representing object of a fibre product
over the source of the monomorphism represents the fibre product over its target. -/
theorem hasAffineIntersectionsULift_of_mono
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (m : F ⟶ G) [Mono m]
    (h : HasAffineIntersectionsULift B S hS G) :
    HasAffineIntersectionsULift B S hS F := fun U V Q a b p q hU hV sq ↦
  h U V Q (a ≫ m) (b ≫ m) p q hU hV ((isPullback_comp_mono_iff m).mpr sq)

/-- Every morphism from a universe-lifted Yoneda presheaf into the universe lift of a presheaf
of `Type u` is the universe lift of a morphism of presheaves of `Type u`: the universe lift of
presheaves is full, and it carries the Yoneda presheaf of an object of the site to the
universe-lifted one. -/
private theorem exists_map_affUpFunctor_eq (T : BigFppfOver B S hS)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (c : (uliftYoneda.{u + 1}).obj T ⟶ F ⋙ uliftFunctor.{u + 1}) :
    ∃ c₀ : yoneda.obj T ⟶ F,
      ((affUpFunctor B S hS).map c₀ :
        (uliftYoneda.{u + 1}).obj T ⟶ F ⋙ uliftFunctor.{u + 1}) = c :=
  (affUpFunctor B S hS).map_surjective (X := yoneda.obj T) (Y := F) c

/-- Clause (2) for the universe lift of a presheaf of `Type u` on the big fppf site of `S` is
the affine-intersection condition of Stacks 0AHS for that presheaf: the universe lift of
presheaves is fully faithful and preserves fibre products, and it carries the Yoneda embedding
to the universe-lifted one, so the cartesian squares the two conditions quantify over
correspond, and the conclusions of the two conditions are literally the same. -/
theorem hasAffineIntersectionsULift_comp_uliftFunctor_iff (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    HasAffineIntersectionsULift B S hS (F ⋙ uliftFunctor.{u + 1}) ↔
      Space.HasAffineIntersections B S hS F := by
  constructor
  · intro h U V Q a b p q hU hV sq
    exact h U V Q ((affUpFunctor B S hS).map a) ((affUpFunctor B S hS).map b) p q hU hV
      (sq.map (affUpFunctor B S hS))
  · intro h U V Q a b p q hU hV sq
    obtain ⟨a₀, rfl⟩ := exists_map_affUpFunctor_eq B S hS U F a
    obtain ⟨b₀, rfl⟩ := exists_map_affUpFunctor_eq B S hS V F b
    refine h U V Q a₀ b₀ p q hU hV
      (IsPullback.of_map (affUpFunctor B S hS) ((affUpFunctor B S hS).map_injective ?_) sq)
    simp only [Functor.map_comp]
    exact sq.w

/-! ### The comparison with the reduction -/

/-- **The inclusion of a reduction is injective on sections over every object of the site.** A
section of the target over an object `T` has a represented base change along it whose
underlying morphism of schemes is a closed immersion, hence a monomorphism; a lift of that
section along the inclusion splits that base change, so any two lifts induce the same morphism
into the base change and therefore coincide. -/
private theorem injective_hom_app_of_isReduction {X Xr : FppfSheaf B S hS} {i : Xr ⟶ X}
    (hi : IsReduction B S hS X Xr i) (T : BigFppfOver B S hS) :
    Function.Injective (i.hom.app (Opposite.op T)) := by
  intro a₁ a₂ he
  apply uliftYonedaEquiv.{u + 1}.symm.injective
  obtain ⟨b, snd, fst, sq⟩ :=
    hi.representable (uliftYonedaEquiv.{u + 1}.symm (i.hom.app (Opposite.op T) a₁))
  obtain ⟨hclosed, -⟩ := hi.thickening _ fst snd sq
  have _ : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map snd) := hclosed
  have _ : Mono snd := (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  have hw : ∀ a, i.hom.app (Opposite.op T) a = i.hom.app (Opposite.op T) a₁ →
      uliftYonedaEquiv.{u + 1}.symm a ≫ i.hom
        = 𝟙 _ ≫ uliftYonedaEquiv.{u + 1}.symm (i.hom.app (Opposite.op T) a₁) := fun a ha ↦ by
    rw [Category.id_comp, uliftYonedaEquiv_symm_comp, ha]
  have hw₁ := hw a₁ rfl
  have hw₂ := hw a₂ he.symm
  have hl : sq.lift _ (𝟙 _) hw₁ = sq.lift _ (𝟙 _) hw₂ :=
    (cancel_mono ((uliftYoneda.{u + 1}).map snd)).mp (by rw [sq.lift_snd, sq.lift_snd])
  rw [← sq.lift_fst _ _ hw₁, hl, sq.lift_fst]

/-- **The inclusion of a reduction is a monomorphism of presheaves.** A morphism of presheaves
of types is a monomorphism as soon as it is injective on sections over every object of the
site, and the inclusion of a reduction is. -/
theorem mono_hom_of_isReduction {X Xr : FppfSheaf B S hS} {i : Xr ⟶ X}
    (hi : IsReduction B S hS X Xr i) : Mono i.hom := by
  have _ : ∀ T : (BigFppfOver B S hS)ᵒᵖ, Mono (i.hom.app T) := fun T ↦
    (mono_iff_injective (i.hom.app T)).2 (injective_hom_app_of_isReduction B S hS hi T.unop)
  exact NatTrans.mono_of_mono_app i.hom

/-! ### Stacks 0AJ6, the implication (2) ⟹ (1) -/

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 0AJ6, the implication (2) ⟹ (1).** Let `X` be a formal algebraic space over `S`
and let `i : X_red ⟶ X` be a reduction of `X`, presented by a presheaf `Xred` of `Type u`
together with an isomorphism from its universe lift. If for every pair of objects of the big
fppf site of `S` with affine underlying scheme and every pair of morphisms from their
universe-lifted Yoneda presheaves into `X` every object of the site representing the fibre
product has affine underlying scheme and the canonical map from the tensor product over `ℤ` of
the two rings of global sections to its ring of global sections is surjective, then `Xred` is a
separated algebraic space.

The inclusion of a reduction is a monomorphism, so a cartesian square exhibiting a fibre
product over `Xred` also exhibits it over `X`; the condition therefore restricts from `X` to
`Xred`, where it is separatedness by Stacks 0AHS. -/
@[stacks 0AJ6 "(2) implies (1): the affine-intersection and surjectivity condition for X \
gives that the reduction of X is a separated algebraic space. The reduction is a given, in \
the sense of AlgebraicGeometry.FormalSpace.IsReduction and supplied by Stacks 0AIN, and is \
presented by a presheaf of Type u together with an isomorphism from its universe lift, since \
an algebraic space over S is a presheaf of Type u while a formal algebraic space is a sheaf \
of Type (u + 1). Clause (2) \
quantifies over the objects of the site representing the fibre product, as the carrier of \
Stacks 0AHS does for the identical clause, rather than asserting that it is representable, \
which is Stacks 0AIP. The converse implication (1) implies (2), the equivalence read against \
an arbitrary reduction, and the tag itself, whose reduction is produced from Stacks 0AIN, are \
AlgebraicGeometry.FormalSpace.hasAffineIntersectionsULift_of_isReduction, \
AlgebraicGeometry.FormalSpace.isAbsolutelySeparated_reduction_iff_hasAffineIntersectionsULift \
and AlgebraicGeometry.FormalSpace.\
exists_isReduction_and_isAbsolutelySeparated_iff_hasAffineIntersectionsULift in \
StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSeparatedConverse", ega "I 10.15.7" "partial"]
theorem isAbsolutelySeparated_reduction_of_hasAffineIntersectionsULift
    {X Xr : FppfSheaf B S hS} (_hX : IsFormalAlgebraicSpace B S hS X)
    {i : Xr ⟶ X} (hi : IsReduction B S hS X Xr i)
    {Xred : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : Xred ⋙ uliftFunctor.{u + 1} ≅ Xr.obj)
    (h : HasAffineIntersectionsULift B S hS X.obj) :
    Space.IsAbsolutelySeparated B S hS hZ Xred := by
  have _ : Mono i.hom := mono_hom_of_isReduction B S hS hi
  have halg : IsAlgebraicSpace B S hS Xred :=
    (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS Xred).mp
      (Space.isAlgebraicSpaceULift_of_iso B S hS e.symm hi.algebraic)
  refine (Space.isAbsolutelySeparated_iff_hasAffineIntersections B S hS hZ Xred halg).mpr ?_
  refine (hasAffineIntersectionsULift_comp_uliftFunctor_iff B S hS Xred).mp ?_
  exact hasAffineIntersectionsULift_of_mono B S hS e.hom
    (hasAffineIntersectionsULift_of_mono B S hS i.hom h)

end AlgebraicGeometry.FormalSpace

end
