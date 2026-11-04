module

public import StacksFrontier.Algebra.Homology.DerivedCategory.PlusCoproducts
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedBelowDirectSums
public import StacksFrontier.AlgebraicGeometry.ProEtale.FilteredColimitsOfProetaleCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CoproductsFromFiltered
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactnessFromCoverings.CompactnessFromFiniteCoverings
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimit
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived global sections of the pro-étale site and direct sums

Let `X` be a quasi-compact and quasi-separated scheme. Then

> `RΓ(X, -) : D⁺(X_pro-étale) ⥤ D(Ab)`

commutes with direct sums and with homotopy colimits. This is Stacks 09A3.

## Main results

* `AlgebraicGeometry.ProEtale.derivedGlobalSections_preservesCoproducts` — **Stacks 09A3, direct
  sums.** `RΓ(X, -)` carries every colimit cocone on a family of objects of
  `D⁺(X_pro-étale)` indexed by a discrete category to a colimit cocone in `D(Ab)`.
* `AlgebraicGeometry.ProEtale.derivedGlobalSections_preservesHomotopyColimits` — **Stacks 09A3,
  homotopy colimits.** `RΓ(X, -)` carries a homotopy colimit of a system of objects of
  `D⁺(X_pro-étale)` to a homotopy colimit in `D(Ab)`.

## Implementation notes

**The shape of "commutes with direct sums".** An arbitrary direct sum of bounded below objects
need not be bounded below, so `D⁺(X_pro-étale)` has no coproducts and there is no coproduct
functor to preserve; the source conditions on `⊕ E i` being an object of `D⁺` for exactly this
reason. `CategoryTheory.Limits.PreservesColimitsOfShape (Discrete I)` is the statement that
every colimit cocone that *does* exist is carried to one, which presupposes the existence of
none of them and is the source's assertion read through the canonical comparison.

**The route.** The argument is not the source's. The source chooses a hypercovering of `X` each
of whose terms is a single affine weakly contractible object (Stacks 09A1 (2)), computes
`RΓ` by the associated total complex (Stacks 09A2), and pulls the direct sum out of the
totalization using quasi-compactness of the terms (Stacks 0935). That route is blocked in this
library at Stacks 09A1 (2), whose construction needs the quasi-compact quasi-separated
pro-étale site; see, in the namespace `Stacks.CategoryTheory`,
`Hypercovering.exists_singleton_weaklyContractible_hypercovering_of_prop_finiteDisjointUnions`.

What is proved here instead is the same statement by the Grothendieck-abelian route, and it
needs no hypercoverings at all. The ordinary cohomology functors `H^p(X_pro-étale, -)` commute
with filtered colimits (Stacks 0739, available on this site as
`AlgebraicGeometry.ProEtale.isIso_colimit_post_rightDerived_Γ_proetale`, whose input is the
cofinal *finite affine* refinement of coverings of a quasi-compact quasi-separated object) and
with finite coproducts (additivity of a right derived functor), hence with arbitrary direct
sums, a coproduct being the filtered colimit of its finite sub-coproducts. The passage from
that to the bounded below *derived* functor is
`Stacks.EtaleCohomology.preservesColimit_rightDerivedFunctorPlus_of_isGE`: resolve each member
of the family by a complex of injectives bounded below by a common bound (Stacks 07D9), observe
that the termwise direct sum of the resolutions is `Γ`-acyclic because the `H^p` commute with
the direct sum, and apply Leray's acyclicity lemma (Stacks 015E). This is where the
quasi-compactness of `X` is spent, and it is spent only once, inside Stacks 0739.

**The index universe.** `Stacks.EtaleCohomology.preservesColimit_rightDerivedFunctorPlus_of_isGE`
indexes its family by the universe at which the two abelian categories are Grothendieck
abelian, because the termwise direct sum of the resolutions is formed inside them. The source
puts no bound on the family, so the restriction is removed: all but a `Small` set of the
summands of a direct sum are zero objects
(`AlgebraicGeometry.ProEtale.small_nonzero_of_hasCoproduct_plus`, which measures the index set
inside the *endomorphisms of a cohomology object*, one universe below the morphisms of
`D⁺`), and discarding the zero summands changes neither the cofan's being colimiting nor its
image's, by `Stacks.Cohomology.restrictCofanIsColimit` and
`Stacks.Cohomology.cofanIsColimitOfRestriction`.

**The common lower bound.** `preservesColimit_rightDerivedFunctorPlus_of_isGE` asks for one,
and a family admitting a direct sum in `D⁺` has one: the splitting `E i ⟶ ⊕ E j ⟶ E i` makes
each `E i` a retract of the direct sum in every cohomological degree, so a bound for the direct
sum bounds every member. This is
`AlgebraicGeometry.ProEtale.exists_isGE_of_hasCoproduct_plus`.

**Coefficients.** The source's `D⁺(X_pro-étale)` is the bounded below derived category of
abelian sheaves. Coefficients here are `AddCommGrpCat.{max (u + 1) v}` for a scheme universe
`u` and arbitrary `v`, the small pro-étale site of `X : Scheme.{u}` having its objects in
`Type (u + 1)`; `v = 0` is `Ab.{u + 1}`, the first universe in which sheafification on this
site is available.

## References

* [Stacks Project, Tag 09A3](https://stacks.math.columbia.edu/tag/09A3)
* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.CompactExtensionByZero.hasRightDerivedFunctorPlus

universe v u i₀ w₀ v₁ u₁ v₀ u₀

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ
  additive_sheafSections hasSheafify_proetale
  isGrothendieckAbelian_sheaf_proetale enoughInjectives_sheaf_proetale

/-! ### Direct sums indexed by an arbitrary type -/

/-- An object of `D⁺(A)` all of whose cohomology objects vanish is a zero object: it is both
`≥ 1` and `≤ 0`, and no nonzero object of the derived category is both. -/
theorem isZero_of_isZero_homology_plus {A : Type u₀} [Category.{v₀} A] [Abelian A]
    [HasDerivedCategory A] (E : DerivedCategory.Plus A)
    (h : ∀ n, IsZero ((DerivedCategory.Plus.homologyFunctor A n).obj E)) : IsZero E := by
  have : E.obj.IsGE 1 := (DerivedCategory.isGE_iff _ _).mpr (fun i _ ↦ h i)
  have : E.obj.IsLE 0 := (DerivedCategory.isLE_iff _ _).mpr (fun i _ ↦ h i)
  rw [IsZero.iff_id_eq_zero]
  exact DerivedCategory.Plus.ι.map_injective
    ((DerivedCategory.TStructure.t.isZero E.obj 0 1).eq_of_src _ _)

/-- **All but a small set of the summands of a direct sum in `D⁺(A)` are zero**, at the universe
of the morphisms of `A` — one below that of the morphisms of `D⁺(A)`, which is what the
statement is for.

The index set is bounded inside the endomorphisms of the cohomology objects of the direct sum:
a nonzero summand `E i` is sent to the family of endomorphisms `H^n(⊕E) ⟶ H^n(⊕E)` obtained by
projecting to `E i` and including again, and two distinct indices with the same family would
make the identity of `E i` vanish in every degree. -/
theorem small_nonzero_of_hasCoproduct_plus {A : Type u₀} [Category.{v₀} A] [Abelian A]
    [HasDerivedCategory A] {I : Type i₀} (E : I → DerivedCategory.Plus A) [HasCoproduct E] :
    Small.{v₀} {i // ¬ IsZero (E i)} := by
  classical
  let H (n : ℤ) : DerivedCategory.Plus A ⥤ A := DerivedCategory.Plus.homologyFunctor A n
  let f (i : {i // ¬ IsZero (E i)}) : ∀ n, (H n).obj (∐ E) ⟶ (H n).obj (∐ E) :=
    fun n ↦ (H n).map (Sigma.π E i.val ≫ Sigma.ι E i.val)
  apply small_of_injective.{v₀} (f := f)
  intro i j hij
  by_contra h
  have hne : i.val ≠ j.val := fun he ↦ h (Subtype.ext he)
  apply i.property
  refine isZero_of_isZero_homology_plus _ (fun n ↦ ?_)
  rw [IsZero.iff_id_eq_zero]
  have he := congrArg (fun z ↦ (H n).map (Sigma.ι E i.val) ≫ z ≫
    (H n).map (Sigma.π E i.val)) (congrFun hij n)
  dsimp only [f] at he
  rw [← (H n).map_id]
  simpa only [← CategoryTheory.Functor.map_comp, ← Category.assoc, Sigma.ι_π_eq_id,
    Category.id_comp, Sigma.ι_π_of_ne E hne, zero_comp, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_zero] using he

/-- **The bounded below right derived functor of an additive functor is additive.** It is a
triangulated functor, by [Stacks, Tag 0159], and a triangulated functor is additive. -/
theorem additive_rightDerivedFunctorPlus {C : Type u₀} [Category.{v₀} C] {D : Type u₁}
    [Category.{v₁} D] [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] (F : C ⥤ D) [F.Additive] :
    F.rightDerivedFunctorPlus.Additive :=
  let : F.rightDerivedFunctorPlus.CommShift ℤ :=
    CategoryTheory.Functor.commShiftRightDerivedFunctorPlus F
  have : F.rightDerivedFunctorPlus.IsTriangulated :=
    CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus F
  inferInstance

/-- **A functor preserving direct sums indexed by the types of one universe preserves direct
sums indexed by any type, provided the nonzero summands are small in that universe.**

The zero summands are discarded on both sides: the restricted cofan is still colimiting by
`Stacks.Cohomology.restrictCofanIsColimit`, the functor preserves the restricted colimit by
hypothesis, and `Stacks.Cohomology.cofanIsColimitOfRestriction` puts the discarded indices
back, the functor sending a zero object to a zero object. -/
theorem preservesColimitsOfShape_discrete_of_small_nonzero
    {A : Type u₀} [Category.{v₀} A] [HasZeroMorphisms A]
    {D : Type u₁} [Category.{v₁} D] [HasZeroMorphisms D]
    (G : A ⥤ D) [G.PreservesZeroMorphisms]
    (hG : ∀ T : Type w₀, PreservesColimitsOfShape (Discrete T) G) (I : Type i₀)
    (hsmall : ∀ M : I → A, HasCoproduct M → Small.{w₀} {j // ¬ IsZero (M j)}) :
    PreservesColimitsOfShape (Discrete I) G := by
  classical
  have hM (M : I → A) : PreservesColimit (Discrete.functor M) G := by
    refine ⟨fun {c} hc ↦ ⟨?_⟩⟩
    have hcop : HasCoproduct M := ⟨⟨⟨c, hc⟩⟩⟩
    have : Small.{w₀} {j // ¬ IsZero (M j)} := hsmall M hcop
    have := hG (Shrink.{w₀} {j // ¬ IsZero (M j)})
    have : PreservesColimitsOfShape (Discrete {j // ¬ IsZero (M j)}) G :=
      preservesColimitsOfShape_of_equiv
        (Discrete.equivalence (equivShrink.{w₀} {j // ¬ IsZero (M j)}).symm) G
    have hc' : IsColimit (Cofan.mk c.pt
        (fun j : {j // ¬ IsZero (M j)} ↦ Cofan.inj c j.1)) :=
      Stacks.Cohomology.restrictCofanIsColimit c hc _ (fun j hj ↦ not_not.mp hj)
    have hd := isColimitCofanMkObjOfIsColimit G (fun j : {j // ¬ IsZero (M j)} ↦ M j.1)
      (fun j ↦ Cofan.inj c j.1) hc'
    have hfull : IsColimit (Cofan.mk (G.obj c.pt) (fun j ↦ G.map (Cofan.inj c j))) :=
      Stacks.Cohomology.cofanIsColimitOfRestriction _ _
        (fun j hj ↦ G.map_isZero (not_not.mp hj)) hd
    exact (Cofan.isColimitMapCoconeEquiv G M c).symm hfull
  exact preservesColimitsOfShape_of_discrete G

/-- **A family admitting a direct sum in `D⁺(A)` admits a common lower bound.** Each member is a
retract of the direct sum, hence its cohomology in every degree is a retract of that of the
direct sum, so a bound for the direct sum bounds every member. -/
theorem exists_isGE_of_hasCoproduct_plus {A : Type u₀} [Category.{v₀} A] [Abelian A]
    [HasDerivedCategory A] {I : Type i₀} (E : I → DerivedCategory.Plus A) [HasCoproduct E] :
    ∃ n : ℤ, ∀ i, (E i).IsGE n := by
  classical
  obtain ⟨n, hn⟩ := (∐ E).property
  refine ⟨n, fun i ↦ ?_⟩
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
  intro j hj
  let H := DerivedCategory.Plus.homologyFunctor A j
  have hz : IsZero (H.obj (∐ E)) :=
    (DerivedCategory.isGE_iff (∐ E).obj n).mp hn j hj
  rw [IsZero.iff_id_eq_zero]
  calc 𝟙 (H.obj (E i)) = H.map (Sigma.ι E i) ≫ H.map (Sigma.π E i) := by
        rw [← H.map_comp, Sigma.ι_π_eq_id, CategoryTheory.Functor.map_id]
    _ = 0 := by rw [hz.eq_of_src (H.map (Sigma.π E i)) 0, comp_zero]

/-! ### Pro-étale cohomology and direct sums -/

variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]

/-- **Pro-étale cohomology of a quasi-compact quasi-separated scheme preserves filtered
colimits.** This is `AlgebraicGeometry.ProEtale.isIso_colimit_post_rightDerived_Γ_proetale`,
i.e. Stacks 0739 on this site, read through
`CategoryTheory.Limits.preservesColimit_of_isIso_post`. -/
theorem preservesColimitsOfShape_rightDerived_Γ_proetale (p : ℕ)
    (I : Type (max (u + 1) v)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I ((Sheaf.Γ (Scheme.ProEt.topology X)
      AddCommGrpCat.{max (u + 1) v}).rightDerived p) :=
  ⟨fun {F} ↦
    have : IsIso (colimit.post F ((Sheaf.Γ (Scheme.ProEt.topology X)
        AddCommGrpCat.{max (u + 1) v}).rightDerived p)) :=
      isIso_colimit_post_rightDerived_Γ_proetale.{v} X p F
    preservesColimit_of_isIso_post (F := F)
      (G := (Sheaf.Γ (Scheme.ProEt.topology X)
        AddCommGrpCat.{max (u + 1) v}).rightDerived p)⟩

/-- **Pro-étale cohomology of a quasi-compact quasi-separated scheme preserves direct sums.** A
coproduct is the filtered colimit of its finite sub-coproducts; the filtered colimits are
Stacks 0739 and the finite ones are additivity of a right derived functor. -/
theorem preservesColimitsOfShape_discrete_rightDerived_Γ_proetale (p : ℕ)
    (α : Type (max (u + 1) v)) :
    PreservesColimitsOfShape (Discrete α) ((Sheaf.Γ (Scheme.ProEt.topology X)
      AddCommGrpCat.{max (u + 1) v}).rightDerived p) :=
  let : HasColimitsOfSize.{max (u + 1) v, max (u + 1) v}
      (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :=
    CategoryTheory.IsGrothendieckAbelian.hasColimits _
  let : HasCoproducts.{max (u + 1) v}
      (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :=
    fun _ ↦ inferInstance
  let : PreservesColimitsOfShape (Finset (Discrete α))
      ((Sheaf.Γ (Scheme.ProEt.topology X)
        AddCommGrpCat.{max (u + 1) v}).rightDerived p) :=
    preservesColimitsOfShape_rightDerived_Γ_proetale.{v} X p _
  Stacks.CoproductsFromFiltered.preservesColimitsOfShape_discrete _

/-- **Derived global sections commute with a direct sum of a family with a common lower
bound.** The ordinary cohomology functors commute with the direct sum, so the termwise direct
sum of injective resolutions bounded below by the common bound is acyclic and Leray's
acyclicity lemma computes `RΓ` on it; this is
`Stacks.EtaleCohomology.preservesColimit_rightDerivedFunctorPlus_of_isGE`. The inclusion of
`D⁺(Ab)` into `D(Ab)` preserves the resulting direct sum because its members, being images of
objects `≥ a` under a left exact functor, are again `≥ a`. -/
theorem preservesColimit_derivedGlobalSections_of_isGE
    {α : Type (max (u + 1) v)}
    (E : α → DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X)
      AddCommGrpCat.{max (u + 1) v}))
    (a : ℤ) (hE : ∀ i, (E i).IsGE a) :
    PreservesColimit (Discrete.functor E)
      ((Sheaf.Γ (Scheme.ProEt.topology X)
        AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.ι) := by
  have hsums (p : ℕ) : PreservesColimitsOfShape (Discrete α)
      ((Sheaf.Γ (Scheme.ProEt.topology X)
        AddCommGrpCat.{max (u + 1) v}).rightDerived p) :=
    preservesColimitsOfShape_discrete_rightDerived_Γ_proetale.{v} X p α
  have hpres : PreservesColimit (Discrete.functor E)
      (Sheaf.Γ (Scheme.ProEt.topology X)
        AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus :=
    Stacks.EtaleCohomology.preservesColimit_rightDerivedFunctorPlus_of_isGE _ hsums E a hE
  have hι : PreservesColimit (Discrete.functor E ⋙ (Sheaf.Γ (Scheme.ProEt.topology X)
      AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus)
      (DerivedCategory.Plus.ι (C := AddCommGrpCat.{max (u + 1) v})) :=
    DerivedCategory.Plus.preservesColimit_ι_of_isGE (a := a) (fun j ↦ by
      have := hE j.as
      exact CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj _ (E j.as) a)
  exact comp_preservesColimit _ _

/-- **Stacks 09A3, direct sums.** Let `X` be a quasi-compact and quasi-separated scheme. Then

> `RΓ(X, -) : D⁺(X_pro-étale) ⥤ D(Ab)`

commutes with direct sums: every colimit cocone on a family of objects of `D⁺(X_pro-étale)`
indexed by a discrete category is carried to a colimit cocone in `D(Ab)`.

The statement quantifies over colimit cocones rather than preserving a coproduct functor: an
arbitrary direct sum of bounded below objects need not be bounded below, so `D⁺(X_pro-étale)`
has no coproducts, and the source itself conditions on `⊕ E i` being an object of `D⁺`.

The index type is arbitrary. The family is reduced to its nonzero members, which form a set
small in the universe at which the sheaf category is Grothendieck abelian, and there
`preservesColimit_derivedGlobalSections_of_isGE` applies, the common lower bound coming from
the direct sum itself. -/
@[stacks 09A3 "direct sums, for the derived global sections of the small pro-etale site of a \
quasi-compact quasi-separated scheme, as preservation of colimit cocones indexed by a discrete \
category with an arbitrary index type"]
theorem derivedGlobalSections_preservesCoproducts (I : Type i₀) :
    PreservesColimitsOfShape (Discrete I)
      ((Sheaf.Γ (Scheme.ProEt.topology X)
        AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.ι) := by
  have hsmallIdx : ∀ (T : Type (max (u + 1) v)),
      PreservesColimitsOfShape (Discrete T)
        ((Sheaf.Γ (Scheme.ProEt.topology X)
          AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.ι) := by
    intro T
    refine ⟨fun {K} ↦ ?_⟩
    have hK : PreservesColimit (Discrete.functor (fun i ↦ K.obj ⟨i⟩))
        ((Sheaf.Γ (Scheme.ProEt.topology X)
          AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.ι) := by
      refine ⟨fun {c} hc ↦ ?_⟩
      have : HasCoproduct (fun i ↦ K.obj ⟨i⟩) := ⟨⟨⟨c, hc⟩⟩⟩
      obtain ⟨a, ha⟩ := exists_isGE_of_hasCoproduct_plus (fun i ↦ K.obj ⟨i⟩)
      exact (preservesColimit_derivedGlobalSections_of_isGE.{v} X
        (fun i ↦ K.obj ⟨i⟩) a ha).preserves hc
    exact preservesColimit_of_iso_diagram
      (K₁ := Discrete.functor (fun i ↦ K.obj ⟨i⟩)) _
      (Discrete.natIso (fun ⟨i⟩ ↦ Iso.refl _))
  have hadd : ((Sheaf.Γ (Scheme.ProEt.topology X)
      AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus).Additive :=
    additive_rightDerivedFunctorPlus _
  refine preservesColimitsOfShape_discrete_of_small_nonzero _ hsmallIdx I (fun M hM ↦ ?_)
  exact small_nonzero_of_hasCoproduct_plus M

/-- **Stacks 09A3, homotopy colimits.** Let `X` be a quasi-compact and quasi-separated scheme.
Then `RΓ(X, -) : D⁺(X_pro-étale) ⥤ D(Ab)` carries a homotopy colimit of a system of objects of
`D⁺(X_pro-étale)` to a homotopy colimit in `D(Ab)`.

This follows formally from the direct sums half: the functor is triangulated, and a homotopy
colimit is defined by a distinguished triangle whose first vertex is a direct sum. -/
@[stacks 09A3 "homotopy colimits, for the derived global sections of the small pro-etale site \
of a quasi-compact quasi-separated scheme"]
theorem derivedGlobalSections_preservesHomotopyColimits
    (F : ℕ ⥤ DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X)
      AddCommGrpCat.{max (u + 1) v}))
    {K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X)
      AddCommGrpCat.{max (u + 1) v})}
    [HasCoproduct F.obj]
    [HasCoproduct (F ⋙ (Sheaf.Γ (Scheme.ProEt.topology X)
      AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι).obj]
    (hK : Pretriangulated.IsHomotopyColimit F K) :
    Pretriangulated.IsHomotopyColimit
      (F ⋙ (Sheaf.Γ (Scheme.ProEt.topology X)
        AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.ι)
      (((Sheaf.Γ (Scheme.ProEt.topology X)
        AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.ι).obj K) := by
  let G := Sheaf.Γ (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}
  have : G.rightDerivedFunctorPlus.Additive := additive_rightDerivedFunctorPlus _
  let : G.rightDerivedFunctorPlus.CommShift ℤ :=
    CategoryTheory.Functor.commShiftRightDerivedFunctorPlus G
  have : G.rightDerivedFunctorPlus.IsTriangulated :=
    CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus G
  have := derivedGlobalSections_preservesCoproducts.{v} X ℕ
  exact hK.map _

end AlgebraicGeometry.ProEtale

end
