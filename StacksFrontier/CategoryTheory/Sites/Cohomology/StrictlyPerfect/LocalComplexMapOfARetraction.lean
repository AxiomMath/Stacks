module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IteratedSlice
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.BoundedLocalApproximationsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DistinguishedTriangles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LiftHomotopyTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Representatives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalNullHomotopyOfDerivedZeroGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalRepresentationOfADerivedMap
import StacksCore.Tactic.StacksAttribute

/-!
# Both parts of Stacks 08FR applied to one map

Let `(C, O)` be a ringed site, `U` an object of `C`, and let `ℰ`, `𝒦`, `ℳ` be complexes of
`O|_U`-modules with `ℰ` strictly perfect. Suppose `κ : 𝒦 ⟶ ℳ` is a map of complexes which,
in `D(O|_U)`, admits a *section* `t : ℳ ⟶ 𝒦` — that is `t ≫ κ = 𝟙`. Then for any map of
complexes `i : ℰ ⟶ ℳ` there is a covering sieve of `U` along each of whose arrows the
composite `t ∘ i` is given by a map of complexes `σ` with `σ ≫ κ` homotopic to `i`.

This is the two-step manoeuvre of the source's proof of the first assertion of Stacks 0FPV:
"we don't know that the diagram commutes, but we do know it commutes after composing with the
map `K → M`. By Lemma 08FR, after replacing `X` by the members of a covering, we may assume
that `s ∘ i` is given by a map of complexes `σ : ℰ ⟶ 𝒦`. By the same lemma we may assume the
composition of `σ` with the inclusion `𝒦 ⊂ ℳ` is homotopic to" `i`.

## Main results

* `AlgebraicGeometry.RingedSite.exists_coveringSieve_homotopy_zero_of_derived_zero_overMap`:
  Stacks 08FR (2) with the restriction along an arrow of the covering sieve written as
  `SheafOfModules.overMap` rather than as restriction to an iterated slice.
* `AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap_homotopy_of_section`: the two
  applications of Stacks 08FR combined.

## Implementation notes

The two parts of Stacks 08FR are stated against different presentations of "restrict along
`g : V ⟶ U`". Part (1),
`AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap`, uses
`SheafOfModules.overMap O g`, landing in modules on the slice `C/V`; part (2),
`AlgebraicGeometry.RingedSite.exists_coveringSieve_homotopy_zero_of_derived_zero_general`, uses
`SheafOfModules.overFunctor (O|_U) (Over.mk g)`, landing on the iterated slice
`(C/U)/(V → U)`. The first statement here moves part (2) to the `overMap` presentation along
`Stacks.SheafOfModules.sliceBackwardComplexIso`, exactly as the proof of Stacks 08FV part (1)
does for Stacks 08FQ. Neither part had a call site before this file.

What makes the second application of 08FR possible is the computation
`Q(σ ≫ κ) = Q(i)`: part (1) produces `σ` with `Q(σ) = Q(i) ≫ t`, and `t ≫ Q(κ) = 𝟙`, so the
two composites agree in the derived category and their difference is killed by `Q`. The
identity is read through `CategoryTheory.Functor.mapDerivedCategoryFactors`, whose naturality
is what transports it across the restriction to the slice.

The two coverings are combined by transitivity of the topology. The sieve the statement
produces is the sieve of arrows along which the conclusion holds; it is downward closed because
restricting `σ` and the homotopy once more is again such a datum, which is
`AlgebraicGeometry.RingedSite.exists_lift_homotopy_of_natIso_comp` at the comparison
`Stacks.SheafOfModules.overMapCompIso`, which compares a composite restriction with the
restriction along the composite. That lemma, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LiftHomotopyTransport`, is the form
of the file-private `exists_lift_homotopy_of_natIso` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DistinguishedTriangles` taking the
lift already over the composite; the lift of a restriction is pushed to the composite here by
`CategoryTheory.Functor.mapHomotopy`, rather than restating anything.

## References

* [Stacks Project, Tag 08FR](https://stacks.math.columbia.edu/tag/08FR)
* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w d

namespace AlgebraicGeometry.RingedSite

section Transport

/-- Transport of a null-homotopy along an isomorphism `P ⋙ Q ≅ T` of functors: if `P α` is
null-homotopic then so is `T α`. The companion of
`AlgebraicGeometry.RingedSite.exists_lift_homotopy_of_natIso_comp`, which transports a lift up
to homotopy. -/
private def homotopyZeroOfNatIso {A₁ A₂ A₃ : Type*}
    [Category A₁] [Category A₂] [Category A₃]
    [Preadditive A₁] [Preadditive A₂] [Preadditive A₃]
    (P : A₁ ⥤ A₂) (Q : A₂ ⥤ A₃) (T : A₁ ⥤ A₃) [P.Additive] [Q.Additive] [T.Additive]
    (ε : P.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        Q.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      T.mapHomologicalComplex (ComplexShape.up ℤ))
    {E F : CochainComplex A₁ ℤ} (α : E ⟶ F)
    (hα : Homotopy ((P.mapHomologicalComplex (ComplexShape.up ℤ)).map α) 0) :
    Homotopy ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map α) 0 := by
  have h := ((Q.mapHomotopy hα).compLeft (ε.inv.app E)).compRight (ε.hom.app F)
  have hnat := NatIso.naturality_1 ε α
  dsimp only [Functor.comp_map] at hnat
  simpa only [Functor.map_zero, zero_comp, comp_zero, Category.assoc, hnat] using h

end Transport

variable (X : RingedSite.{u, u, w}) (U : X.C)
variable [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{w}]
variable [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasDerivedCategory.{d}
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

/-- **Stacks 08FR (2), with the restriction to the slice over an arrow `V ⟶ U` of the covering
sieve expressed by `SheafOfModules.overMap`** rather than by restriction to an iterated slice.

This is the same statement as
`AlgebraicGeometry.RingedSite.exists_coveringSieve_homotopy_zero_of_derived_zero_general`, in
the presentation of the restriction that Stacks 08FR (1) and pseudo-coherence use. The general
form of 08FR (2) is the one read here, the module sections living in the ring universe `w`. -/
@[stacks 08FR "local_null_homotopy, along an arrow of the site"]
theorem exists_coveringSieve_homotopy_zero_of_derived_zero_overMap
    {E F : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) E) (α : E ⟶ F)
    (hα : DerivedCategory.Q.map α = 0) :
    ∃ S : Sieve U, S ∈ X.J U ∧ ∀ ⦃V : X.C⦄ (g : V ⟶ U), S g →
      Nonempty (Homotopy (((SheafOfModules.overMap.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapHomologicalComplex
          (ComplexShape.up ℤ)).map α) 0) := by
  obtain ⟨S, hS, hnull⟩ :=
    exists_coveringSieve_homotopy_zero_of_derived_zero_general X U hE α hα
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨h⟩ := hnull g hg
  exact ⟨homotopyZeroOfNatIso
    (SheafOfModules.overFunctor.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
      (Over.mk g))
    (Stacks.SheafOfModules.sliceBackward (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)
    (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)
    (Stacks.SheafOfModules.sliceBackwardComplexIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)
    α h⟩

/-- The restriction of a complex of `O|_U`-modules along an arrow of the site. -/
private abbrev restr {V : X.C} (f : V ⟶ U) :
    CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ ⥤
      CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ :=
  (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).mapHomologicalComplex
    (ComplexShape.up ℤ)

variable {E K M :
    CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}

/-- A factorization up to homotopy of `i|_V` through `κ|_V`, given after restricting along
`g : W ⟶ V`, yields one of `i|_W` through `κ|_W` for the composite `g ≫ f`. -/
private theorem exists_factorization_restr_comp (X : RingedSite.{u, u, w}) (U : X.C)
    {E K M : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}
    {V W : X.C} (f : V ⟶ U) (g : W ⟶ V)
    (i : E ⟶ M) (κ : K ⟶ M) (σ : (restr X U f).obj E ⟶ (restr X U f).obj K)
    (h : Homotopy ((restr X V g).map (σ ≫ (restr X U f).map κ))
      ((restr X V g).map ((restr X U f).map i))) :
    ∃ δ : (restr X U (g ≫ f)).obj E ⟶ (restr X U (g ≫ f)).obj K,
      Nonempty (Homotopy (δ ≫ (restr X U (g ≫ f)).map κ) ((restr X U (g ≫ f)).map i)) := by
  refine exists_lift_homotopy_of_natIso_comp
    (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f)
    (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)
    (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (g ≫ f))
    (Functor.mapHomologicalComplexCompIso
      (Stacks.SheafOfModules.overMapCompIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f g)
      (ComplexShape.up ℤ))
    i κ ((restr X V g).map σ) ?_
  exact (Homotopy.ofEq ((restr X V g).map_comp σ _).symm).trans h

/-- The sieve of arrows `f : V ⟶ U` along which `i|_V` factors through `κ|_V` up to homotopy. -/
private def factorsSieve (i : E ⟶ M) (κ : K ⟶ M) : Sieve U where
  arrows V f := ∃ σ : (restr X U f).obj E ⟶ (restr X U f).obj K,
    Nonempty (Homotopy (σ ≫ (restr X U f).map κ) ((restr X U f).map i))
  downward_closed := by
    rintro V W f ⟨σ, ⟨hσ⟩⟩ g
    exact exists_factorization_restr_comp X U f g i κ σ
      ((SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapHomotopy hσ)

/-- **The two applications of Stacks 08FR to `t ∘ i`.** Let `ℰ`, `𝒦`, `ℳ` be complexes of
`O|_U`-modules with `ℰ` strictly perfect, let `i : ℰ ⟶ ℳ` and `κ : 𝒦 ⟶ ℳ` be maps of complexes,
and suppose `κ` admits a section `t` in `D(O|_U)`. Then along the arrows of a covering sieve of
`U` the composite `t ∘ i` is given by a map of complexes `σ`, and `σ ≫ κ` is homotopic to `i`.

This is the manoeuvre of the source's proof of the first assertion of Stacks 0FPV: part (1) of
08FR realizes `s ∘ i` by a map of complexes `σ`, and part (2) then kills the difference between
`σ ≫ κ` and `i`, which has the same class in the derived category because `t` is a section of
`κ` there. -/
theorem exists_coveringSieve_complexMap_homotopy_of_section
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) E)
    (i : E ⟶ M) (κ : K ⟶ M)
    (t : DerivedCategory.Q.obj M ⟶ DerivedCategory.Q.obj K)
    (ht : t ≫ DerivedCategory.Q.map κ = 𝟙 (DerivedCategory.Q.obj M)) :
    ∃ S : Sieve U, S ∈ X.J U ∧ ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
      ∃ σ : Stacks.SheafOfModules.restrictComplexAlongGeneral
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f E ⟶
          Stacks.SheafOfModules.restrictComplexAlongGeneral
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f K,
        Nonempty (Homotopy
          (σ ≫ ((SheafOfModules.overMap.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).mapHomologicalComplex
              (ComplexShape.up ℤ)).map κ)
          (((SheafOfModules.overMap.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).mapHomologicalComplex
              (ComplexShape.up ℤ)).map i)) := by
  refine ⟨factorsSieve X U i κ, ?_, fun V f hf => hf⟩
  obtain ⟨S₁, hS₁, hrep⟩ :=
    exists_coveringSieve_complexMap X U hE (DerivedCategory.Q.map i ≫ t)
  refine X.J.transitive hS₁ _ fun V f hf => ?_
  let _ : HasDerivedCategory
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) :=
    HasDerivedCategory.standard _
  obtain ⟨hsheaf, hlocal, hadd, hlim, hcolim, β, hβ⟩ := hrep f hf
  have hQ : DerivedCategory.Q.map (β ≫ (restr X U f).map κ) =
      DerivedCategory.Q.map ((restr X U f).map i) := by
    rw [← cancel_epi ((SheafOfModules.overMap.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).mapDerivedCategoryFactors.hom.app E),
      Functor.map_comp, ← Category.assoc, ← hβ, Category.assoc,
      ← (SheafOfModules.overMap.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).mapDerivedCategoryFactors_hom_naturality κ,
      ← Category.assoc, ← Functor.map_comp, Category.assoc, ht, Category.comp_id,
      (SheafOfModules.overMap.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).mapDerivedCategoryFactors_hom_naturality i]
  have hzero : DerivedCategory.Q.map (β ≫ (restr X U f).map κ - (restr X U f).map i) = 0 := by
    rw [Functor.map_sub, hQ, sub_self]
  obtain ⟨S₂, hS₂, hnull⟩ := exists_coveringSieve_homotopy_zero_of_derived_zero_overMap X V
    (isStrictlyPerfect_overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f hE)
    (β ≫ (restr X U f).map κ - (restr X U f).map i) hzero
  refine X.J.superset_covering ?_ hS₂
  intro W g hg
  obtain ⟨hgh⟩ := hnull g hg
  refine exists_factorization_restr_comp X U f g i κ β (Homotopy.equivSubZero.symm
    ((Homotopy.ofEq ?_).trans hgh))
  rw [Functor.map_sub]

end AlgebraicGeometry.RingedSite

end
