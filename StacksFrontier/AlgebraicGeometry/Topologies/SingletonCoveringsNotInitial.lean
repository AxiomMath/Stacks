module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import Mathlib.RingTheory.Int.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoveringDisjointUnion
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver

/-!
# One-member coverings are not initial among all coverings

A family of morphisms `𝒰 = {Uᵢ ⟶ T}` whose members have a coproduct is a refinement of the
one-member family `𝒱 = {∐ Uᵢ ⟶ T}`, but not conversely: the affine scheme `Spec ℤ`, covered by
the two basic opens of `2` and of `3`, admits no one-member covering refining that covering at
all, because no one of the two basic opens is already the whole of `Spec ℤ` while every member
of a covering family of a single morphism is surjective. Consequently the one-member coverings
of an object do not form an initial subcategory of the category of all of its coverings, for
any topology on schemes whose coverings are jointly surjective families of morphisms with a
property that open immersions have.

## Main definitions

* `AlgebraicGeometry.isSingletonCovering` is the property of a covering of an object of being a
  one-member family `{V ⟶ T}`.
* `AlgebraicGeometry.SpecIntCovering.covering` is the standard Zariski covering of `Spec ℤ` by
  the basic opens of `2` and of `3`.

## Main results

* `CategoryTheory.PreZeroHypercover.nonempty_hom_singleton_sigmaDesc`: a family is a refinement
  of the one-member family given by the morphism from the coproduct of its members.
* `AlgebraicGeometry.isEmpty_hom_of_forall_not_surjective`: a family none of whose members is
  surjective has no refinement by a family one of whose members is surjective.
* `AlgebraicGeometry.SpecIntCovering.isEmpty_hom_singleton_sigmaDesc`: for the covering of
  `Spec ℤ` above, the one-member family given by the morphism from the disjoint union of its
  members is not a refinement of it.
* `AlgebraicGeometry.SpecIntCovering.isEmpty_hom_singleton_of_mem_precoverage`: no one-member
  covering of `Spec ℤ` is a refinement of that covering.
* `AlgebraicGeometry.SpecIntCovering.not_initial_isSingletonCovering_inclusion`: the one-member
  coverings of `Spec ℤ` are not an initial subcategory of its category of coverings, while
  `AlgebraicGeometry.SpecIntCovering.exists_isSingletonCovering` says that subcategory is not
  empty.

## References

* [Stacks Project, Tag 03P0](https://stacks.math.columbia.edu/tag/03P0)
* [Stacks Project, Tag 03OZ](https://stacks.math.columbia.edu/tag/03OZ)
* [Stacks Project, Tag 00VT](https://stacks.math.columbia.edu/tag/00VT)
* [Stacks Project, Tag 09WP](https://stacks.math.columbia.edu/tag/09WP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v w

namespace CategoryTheory.PreZeroHypercover

/-- A family of morphisms with fixed target whose members have a coproduct is a **refinement of
the one-member family** given by the morphism from that coproduct. -/
@[stacks 03P0 "the covering `𝒰` is a refinement of `𝒱 = {∐ Uᵢ ⟶ U}`, the direction of
  Stacks 03FI (2) that does hold"]
theorem nonempty_hom_singleton_sigmaDesc {C : Type u} [Category.{v} C] {T : C}
    (E : PreZeroHypercover.{w} T) [HasCoproduct E.X] :
    Nonempty (E.Hom (singleton.{w} (Sigma.desc E.f))) :=
  ⟨homOverIdEquivHom _ _ (Stacks.CechSite.coproductRefinement E)⟩

end CategoryTheory.PreZeroHypercover

namespace AlgebraicGeometry

/-- A family of morphisms of schemes with fixed target **none of whose members is surjective has
no refinement by a family one of whose members is surjective**. -/
theorem isEmpty_hom_of_forall_not_surjective {T : Scheme.{u}} {E : PreZeroHypercover.{w} T}
    (hE : ∀ i, ¬ Function.Surjective (E.f i).base) {F : PreZeroHypercover.{v} T} (j : F.I₀)
    (hj : Function.Surjective (F.f j).base) :
    IsEmpty (F.Hom E) := by
  refine ⟨fun φ ↦ hE (φ.s₀ j) fun x ↦ ?_⟩
  obtain ⟨y, hy⟩ := hj x
  exact ⟨(φ.h₀ j).base y, by rwa [← Scheme.Hom.comp_apply, φ.w₀ j]⟩

/-- The property of a covering of `T`, for a precoverage of the category of schemes, of being a
**one-member family** `{V ⟶ T}`. -/
def isSingletonCovering (J : Precoverage Scheme.{u}) (T : Scheme.{u}) :
    ObjectProperty (Precoverage.ZeroHypercover.{w} J T) :=
  fun E ↦ Nonempty (Unique E.I₀)

namespace SpecIntCovering

/-- The ring of integers, in the universe `u`. -/
abbrev ring : CommRingCat.{u} := CommRingCat.of (ULift.{u} ℤ)

/-- The affine scheme `Spec ℤ`. -/
abbrev target : Scheme.{u} := Spec ring.{u}

/-- The integers `2` and `3`, indexed by `Bool`. -/
abbrev gen (b : Bool) : ULift.{u} ℤ := if b then 3 else 2

/-- The integers `2` and `3` as global sections of `Spec ℤ`, indexed by `Bool`. -/
abbrev genSection (b : Bool) : Γ(target.{u}, ⊤) := (Scheme.ΓSpecIso ring.{u}).inv (gen b)

/-- The **covering of `Spec ℤ` by the basic opens of `2` and of `3`**, as a family of morphisms
with fixed target indexed by `Bool`. -/
abbrev covering : PreZeroHypercover.{w} target.{u} :=
  { I₀ := ULift.{w} Bool
    X := fun b ↦ (target.basicOpen (genSection b.down)).toScheme
    f := fun b ↦ (target.basicOpen (genSection b.down)).ι }

/-- A point of `Spec ℤ` lies in the image of the basic open of `2`, resp. of `3`, exactly when
its prime ideal avoids that integer. -/
private theorem mem_range_f_iff (b : Bool) (x : target.{u}) :
    x ∈ Set.range (target.{u}.basicOpen (genSection b)).ι.base ↔ gen b ∉ x.asIdeal := by
  rw [Scheme.Opens.range_ι, SetLike.mem_coe,
    show target.{u}.basicOpen (genSection b) = PrimeSpectrum.basicOpen (gen b) from
      basicOpen_eq_of_affine _]
  exact PrimeSpectrum.mem_basicOpen _ _

/-- Every point of `Spec ℤ` lies in the image of the basic open of `2` or of `3`. -/
private theorem exists_mem_range_f (x : target.{u}) :
    ∃ i : covering.{u, w}.I₀, x ∈ Set.range (covering.{u, w}.f i).base := by
  obtain ⟨b, hb⟩ : ∃ b, gen.{u} b ∉ x.asIdeal := by
    by_contra! hc
    refine x.isPrime.ne_top' ((Ideal.eq_top_iff_one _).mpr ?_)
    rw [show (1 : ULift.{u} ℤ) = gen true - gen false from ULift.ext (by simp [gen])]
    exact sub_mem (hc true) (hc false)
  exact ⟨ULift.up b, (mem_range_f_iff b x).mpr hb⟩

/-- The basic opens of `2` and of `3` cover `Spec ℤ`. -/
theorem iUnion_range_f : (⋃ i, Set.range (covering.{u, w}.f i).base) = Set.univ :=
  Set.eq_univ_iff_forall.mpr fun x ↦ Set.mem_iUnion.mpr (exists_mem_range_f x)

/-- The covering of `Spec ℤ` by the basic opens of `2` and of `3` is a **standard Zariski
covering** of `Spec ℤ`. -/
theorem isStandardCovering_zariski :
    IsStandardCovering .zariski covering.{u, w}.X covering.{u, w}.f :=
  ⟨inferInstance, fun b ↦ (isAffineOpen_top target.{u}).basicOpen (genSection b.down),
    iUnion_range_f, fun b ↦ ⟨genSection b.down, Iso.refl _, (Category.id_comp _).symm⟩⟩

/-- The covering of `Spec ℤ` by the basic opens of `2` and of `3` is also a **standard étale
covering** of `Spec ℤ`. -/
theorem isStandardCovering_etale :
    IsStandardCovering .etale covering.{u, w}.X covering.{u, w}.f :=
  ⟨inferInstance, fun b ↦ (isAffineOpen_top target.{u}).basicOpen (genSection b.down),
    iUnion_range_f, fun b ↦ (inferInstance : Etale (target.{u}.basicOpen (genSection b.down)).ι)⟩

/-- No member of the covering of `Spec ℤ` by the basic opens of `2` and of `3` is surjective. -/
theorem not_surjective_f (i : covering.{u, w}.I₀) :
    ¬ Function.Surjective (covering.{u, w}.f i).base := by
  intro hs
  obtain ⟨x, hx⟩ : ∃ x : PrimeSpectrum (ULift.{u} ℤ), gen.{u} i.down ∈ x.asIdeal := by
    have hp : ∀ b : Bool, Prime (if b then (3 : ℤ) else 2) := by
      intro b
      cases b
      · simpa using Int.prime_two
      · simpa using Int.prime_three
    refine ⟨PrimeSpectrum.comap (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom
      ⟨Ideal.span {if i.down then (3 : ℤ) else 2}, ?_⟩, ?_⟩
    · exact (Ideal.span_singleton_prime (by cases i.down <;> simp)).mpr (hp i.down)
    · rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
        show (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom (gen i.down)
            = (if i.down then (3 : ℤ) else 2) from by
          cases i.down <;> simp [gen, RingEquiv.toRingHom_eq_coe, map_ofNat]]
      exact Ideal.mem_span_singleton_self _
  exact (mem_range_f_iff i.down x).mp (hs x) hx

/-- The morphism from the disjoint union of the basic opens of `2` and of `3` to `Spec ℤ` is
surjective. -/
theorem surjective_sigmaDesc :
    Function.Surjective (Sigma.desc covering.{u, w}.f).base := by
  intro x
  obtain ⟨i, y, hy⟩ := exists_mem_range_f.{u, w} x
  exact ⟨(Sigma.ι covering.{u, w}.X i).base y, by rwa [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]⟩

/-- **The one-member family given by the disjoint union of a covering need not refine it**: for
the covering of `Spec ℤ` by the basic opens of `2` and of `3`, the one-member family given by
the morphism from the disjoint union of its members is not a refinement of it. -/
@[stacks 03P0 "`𝒱 = {∐ Uᵢ ⟶ U}` is not a refinement of `𝒰`, witnessed by the standard Zariski
  covering of `Spec ℤ` by the basic opens of `2` and of `3`"]
theorem isEmpty_hom_singleton_sigmaDesc :
    IsEmpty ((PreZeroHypercover.singleton.{w} (Sigma.desc covering.{u, w}.f)).Hom
      covering.{u, w}) :=
  isEmpty_hom_of_forall_not_surjective not_surjective_f default surjective_sigmaDesc

/-- **No one-member covering of `Spec ℤ` refines the covering by the basic opens of `2` and of
`3`**, for any topology whose coverings are jointly surjective families of morphisms with a
given property. -/
@[stacks 03P0 "no covering of the form `{V ⟶ U}` is a refinement of `𝒰`, witnessed by the
  standard Zariski covering of `Spec ℤ` by the basic opens of `2` and of `3`"]
theorem isEmpty_hom_singleton_of_mem_precoverage {P : MorphismProperty Scheme.{u}}
    {V : Scheme.{u}} (g : V ⟶ target.{u})
    (hg : Presieve.singleton g ∈ Scheme.precoverage P target.{u}) :
    IsEmpty ((PreZeroHypercover.singleton.{w} g).Hom covering.{u, w}) :=
  isEmpty_hom_of_forall_not_surjective not_surjective_f default
    ((Scheme.singleton_mem_precoverage_iff P g).mp hg).1

/-- The covering of `Spec ℤ` by the basic opens of `2` and of `3`, as an object of the category
of coverings of `Spec ℤ` for a topology whose coverings are jointly surjective families of
morphisms with a property that open immersions have. -/
def coveringZeroHypercover (P : MorphismProperty Scheme.{u})
    (hP : (@IsOpenImmersion : MorphismProperty Scheme.{u}) ≤ P) :
    Precoverage.ZeroHypercover.{w} (Scheme.precoverage P) target.{u} where
  toPreZeroHypercover := covering.{u, w}
  mem₀ := by
    rw [show covering.{u, w}.presieve₀ = .ofArrows covering.X covering.f from rfl,
      Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨fun x ↦ Set.mem_iUnion.mp (iUnion_range_f.ge (Set.mem_univ x)),
      fun i ↦ hP _ inferInstance⟩

/-- The identity of `Spec ℤ` is a **one-member covering** of it, so the subcategory of one-member
coverings is not empty. -/
theorem exists_isSingletonCovering (P : MorphismProperty Scheme.{u})
    (hP : (@IsOpenImmersion : MorphismProperty Scheme.{u}) ≤ P) :
    ∃ E : Precoverage.ZeroHypercover.{w} (Scheme.precoverage P) target.{u},
      isSingletonCovering.{u, w} (Scheme.precoverage P) target.{u} E := by
  refine ⟨Precoverage.ZeroHypercover.singleton (𝟙 target.{u})
      ((Scheme.singleton_mem_precoverage_iff P _).mpr
        ⟨fun x ↦ ⟨x, by simp⟩, hP _ inferInstance⟩), ⟨?_⟩⟩
  change Unique (PreZeroHypercover.singleton.{w} (𝟙 target.{u})).I₀
  infer_instance

/-- **The one-member coverings of an object do not form an initial subcategory of its category
of coverings**: for the covering of `Spec ℤ` by the basic opens of `2` and of `3` there is no
one-member covering mapping to it. -/
@[stacks 03P0 "coverings of the form `{V ⟶ U}` are not an initial subcategory of the category
  of all coverings of `U`, witnessed by the standard Zariski covering of `Spec ℤ` by the basic
  opens of `2` and of `3`; the remark's further assertion that Čech cohomology can nonetheless
  be computed from the coverings `{V ⟶ U}` is not proved, the source leaving it unformulated"]
theorem not_initial_isSingletonCovering_inclusion (P : MorphismProperty Scheme.{u})
    (hP : (@IsOpenImmersion : MorphismProperty Scheme.{u}) ≤ P) :
    ¬ (isSingletonCovering.{u, w} (Scheme.precoverage P) target.{u}).ι.Initial := by
  intro h
  have hc := h.out (coveringZeroHypercover.{u, w} P hP)
  obtain ⟨A⟩ := hc.is_nonempty
  obtain ⟨hu⟩ := A.left.property
  let : Unique A.left.obj.I₀ := hu
  have hs : Function.Surjective (A.left.obj.f default).base := by
    have hm := A.left.obj.mem₀
    rw [show A.left.obj.presieve₀ = .ofArrows A.left.obj.X A.left.obj.f from rfl,
      Scheme.ofArrows_mem_precoverage_iff] at hm
    intro x
    obtain ⟨i, hi⟩ := hm.1 x
    rwa [Unique.eq_default i] at hi
  exact (isEmpty_hom_of_forall_not_surjective not_surjective_f default hs).elim A.hom

end SpecIntCovering

end AlgebraicGeometry

end

add_to_stacks 09WP "the definition of an initial functor, and so of an initial subcategory"
  CategoryTheory.Functor.Initial
add_to_sga "4 V 8.1.4" "special case" CategoryTheory.Functor.Initial
