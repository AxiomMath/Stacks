module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.InfiniteProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardRefinement
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Standard coverings as covering sieves of the small étale site

Let `S` be a scheme and let `S_étale` be its small étale site, Mathlib's
`AlgebraicGeometry.Scheme.Etale` with the topology `AlgebraicGeometry.Scheme.smallEtaleTopology`.
This file relates the *standard* étale coverings of [Stacks, Tag 03X9] — finite families of
affines over an affine, each member étale — to the covering sieves of that site, in both
directions:

* a standard étale covering of the scheme underlying an object `U` of `S_étale` lifts to a
  family in `S_étale` and generates a covering sieve of `U`;
* every covering sieve of an object with affine total space contains such a lifted standard
  covering, by [Stacks, Tag 03XA].

It also verifies, for these coverings, the hypotheses of the Čech-vanishing criterion
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_functor` other than the
Čech vanishing itself.

## Main definitions

* `AlgebraicGeometry.IsSmallEtaleStandardCovering`: a family in the small étale site whose
  underlying family of schemes is a standard étale covering of an affine.
* `AlgebraicGeometry.smallEtaleStandardHypercover`: the family in the small étale site
  attached to a family of étale morphisms into the scheme underlying an object.
* `AlgebraicGeometry.smallEtaleAffineObjects`: the objects with affine total space.
* `AlgebraicGeometry.smallEtaleStandardCoverings`: the small-étale-standard coverings of an
  object.

## Main results

* `AlgebraicGeometry.IsSmallEtaleStandardCovering.sieve₀_mem_smallEtaleTopology`: a lifted
  standard étale covering generates a covering sieve of the small étale site.
* `AlgebraicGeometry.exists_isSmallEtaleStandardCovering_sieve₀_le` and
  `AlgebraicGeometry.smallEtaleStandardCoverings_cofinal`: every covering sieve of an object with
  affine total space contains a lifted standard étale covering.
* `AlgebraicGeometry.smallEtaleStandardCoverings_hasProducts` and
  `AlgebraicGeometry.smallEtaleStandardCoverings_hasImageProducts`: the iterated fibre products
  of a covering, and of its image in the slice of all schemes over `S`, exist.
* `AlgebraicGeometry.isAffine_left_piObj`: an iterated fibre product of objects with affine
  total space over an object with affine total space again has affine total space.
* `AlgebraicGeometry.smallEtaleStandardCoverings_covObjects`: the target, the members and the
  iterated fibre products of a small-étale-standard covering have affine total space.

## References

* [Stacks Project, Tag 03X9](https://stacks.math.columbia.edu/tag/03X9)
* [Stacks Project, Tag 03XA](https://stacks.math.columbia.edu/tag/03XA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

variable (S : Scheme.{u})

/-! ### Standard coverings in the small étale site -/

/-- A family in the small étale site of `S` is a *small-étale-standard* covering when its
target has affine total space and the family of schemes underlying it is a standard étale
covering of that total space. -/
public def IsSmallEtaleStandardCovering {U : S.Etale} (E : PreZeroHypercover.{v} U) : Prop :=
  ∃ h : IsAffine U.left,
    @IsStandardCovering .etale U.left h E.I₀ (fun i ↦ (E.X i).left) (fun i ↦ (E.f i).left)

/-- The target of a small-étale-standard covering, and each of its members, has affine total
space. -/
public theorem IsSmallEtaleStandardCovering.isAffine {U : S.Etale}
    {E : PreZeroHypercover.{v} U} (h : IsSmallEtaleStandardCovering S E) :
    IsAffine U.left ∧ ∀ i, IsAffine (E.X i).left := by
  obtain ⟨hU, hstd⟩ := h
  let := hU
  exact ⟨hU, hstd.affine_source⟩

/-- A small-étale-standard covering has finitely many members. -/
public theorem IsSmallEtaleStandardCovering.finite {U : S.Etale}
    {E : PreZeroHypercover.{v} U} (h : IsSmallEtaleStandardCovering S E) : Finite E.I₀ := by
  obtain ⟨hU, hstd⟩ := h
  let := hU
  exact hstd.finite_index

/-- A small-étale-standard covering of an object of the small étale site generates a covering
sieve of that object. -/
@[sga "4 VII 1.2" "special case"]
public theorem IsSmallEtaleStandardCovering.sieve₀_mem_smallEtaleTopology {U : S.Etale}
    (E : PreZeroHypercover.{v} U) (h : IsSmallEtaleStandardCovering S E) :
    E.sieve₀ ∈ Scheme.smallEtaleTopology S U := by
  obtain ⟨hU, hstd⟩ := h
  rw [PreZeroHypercover.sieve₀, Scheme.ofArrows_mem_smallEtaleTopology_iff]
  exact hstd.jointly_surjective

/-- The family in the small étale site attached to a family of étale morphisms into the scheme
underlying an object `U`: its members are the sources, étale over `S` through `U`. -/
public def smallEtaleStandardHypercover {U : S.Etale} {I : Type v} {V : I → Scheme.{u}}
    (g : ∀ i, V i ⟶ U.left) (hg : ∀ i, Etale (g i)) : PreZeroHypercover.{v} U where
  I₀ := I
  X i := haveI := hg i; Scheme.Etale.mk (g i ≫ U.hom)
  f i := MorphismProperty.Over.homMk (g i)

/-- The total space of the `i`-th member of `smallEtaleStandardHypercover S g hg` is `V i`. -/
@[simp]
public theorem smallEtaleStandardHypercover_X_left {U : S.Etale} {I : Type v}
    {V : I → Scheme.{u}} (g : ∀ i, V i ⟶ U.left) (hg : ∀ i, Etale (g i)) (i : I) :
    ((smallEtaleStandardHypercover S g hg).X i).left = V i := rfl

/-- The morphism of schemes underlying the `i`-th map of `smallEtaleStandardHypercover S g hg`
is `g i`. -/
@[simp]
public theorem smallEtaleStandardHypercover_f_left {U : S.Etale} {I : Type v}
    {V : I → Scheme.{u}} (g : ∀ i, V i ⟶ U.left) (hg : ∀ i, Etale (g i)) (i : I) :
    ((smallEtaleStandardHypercover S g hg).f i).left = g i := rfl

/-- The family attached to a standard étale covering of the scheme underlying an object is a
small-étale-standard covering. -/
public theorem isSmallEtaleStandardCovering_smallEtaleStandardHypercover {U : S.Etale}
    [hU : IsAffine U.left] {I : Type v} {V : I → Scheme.{u}} {g : ∀ i, V i ⟶ U.left}
    (hg : IsStandardCovering .etale V g) :
    IsSmallEtaleStandardCovering S (smallEtaleStandardHypercover S g fun i ↦ hg.standard i) :=
  ⟨hU, hg⟩

/-- Every covering sieve of an object of the small étale site with affine total space contains
a small-étale-standard covering. -/
public theorem exists_isSmallEtaleStandardCovering_sieve₀_le {U : S.Etale}
    (hU : IsAffine U.left) {R : Sieve U} (hR : R ∈ Scheme.smallEtaleTopology S U) :
    ∃ E : PreZeroHypercover.{u} U, IsSmallEtaleStandardCovering S E ∧ E.sieve₀ ≤ R := by
  classical
  have := hU
  have : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨𝒰, h𝒰, hp, hle⟩ := (Scheme.mem_smallGrothendieckTopology U R).mp hR
  let : Category.{u} (MorphismProperty.Over (@Etale : MorphismProperty Scheme.{u}) ⊤ S) :=
    inferInstanceAs (Category S.Etale)
  obtain ⟨W, r, hW⟩ := exists_standardCovering_refinement .etale 𝒰.toPreZeroHypercover
    (by simpa [coveringMorphismProperty] using 𝒰.mem₀)
  let E : PreZeroHypercover.{u} U := smallEtaleStandardHypercover S W.f fun j ↦ hW.standard j
  refine ⟨E, isSmallEtaleStandardCovering_smallEtaleStandardHypercover S hW, ?_⟩
  rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, Sieve.generate_le_iff,
    Presieve.ofArrows_le_iff]
  intro i
  let : (𝒰.X (r.s₀ i)).Over S := h𝒰.over (r.s₀ i)
  let : (𝒰.f (r.s₀ i)).IsOver S := h𝒰.isOver_map (r.s₀ i)
  have hfac : r.h₀ i ≫ 𝒰.f (r.s₀ i) = W.f i := r.w₀ i
  let Z : S.Etale := (𝒰.X (r.s₀ i)).asOverProp S (hp (r.s₀ i))
  let c : Z ⟶ U := (𝒰.f (r.s₀ i)).asOverProp S
  have hcR : R.arrows c := hle _ _ ⟨r.s₀ i⟩
  have hw : r.h₀ i ≫ ((Scheme.Etale.forget S).obj Z).hom =
      ((Scheme.Etale.forget S).obj (E.X i)).hom := by
    show r.h₀ i ≫ (𝒰.X (r.s₀ i) ↘ S) = W.f i ≫ U.hom
    rw [← comp_over (𝒰.f (r.s₀ i)) S, ← Category.assoc, hfac]
    rfl
  let g : (Scheme.Etale.forget S).obj (E.X i) ⟶ (Scheme.Etale.forget S).obj Z :=
    CategoryTheory.Over.homMk (r.h₀ i) hw
  let a : E.X i ⟶ Z := (Scheme.Etale.forgetFullyFaithful S).preimage g
  have haleft : a.left = r.h₀ i :=
    congrArg (fun k ↦ k.left) ((Scheme.Etale.forgetFullyFaithful S).map_preimage g)
  have hleft : a.left ≫ 𝒰.f (r.s₀ i) = W.f i :=
    (congrArg (fun k ↦ k ≫ 𝒰.f (r.s₀ i)) haleft).trans hfac
  have heq : a ≫ c = E.f i :=
    (Scheme.Etale.forget S).map_injective (CategoryTheory.Over.OverMorphism.ext hleft)
  exact heq ▸ R.downward_closed hcR a

/-! ### The data of the Čech-vanishing criterion -/

/-- The objects of the small étale site with affine total space. -/
public def smallEtaleAffineObjects : Set S.Etale :=
  {U | IsAffine U.left}

/-- Membership in `AlgebraicGeometry.smallEtaleAffineObjects` is affineness of the total
space. -/
public theorem mem_smallEtaleAffineObjects_iff (U : S.Etale) :
    U ∈ smallEtaleAffineObjects S ↔ IsAffine U.left := Iff.rfl

/-- The small-étale-standard coverings of an object of the small étale site, as coverings of
its topology. -/
public def smallEtaleStandardCoverings (U : S.Etale) :
    Set { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ Scheme.smallEtaleTopology S U } :=
  {E | IsSmallEtaleStandardCovering S E.1}

/-- The target of a small-étale-standard covering, and each of its members, is an object with
affine total space. -/
public theorem mem_smallEtaleAffineObjects_of_mem_smallEtaleStandardCoverings (U : S.Etale)
    (E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ Scheme.smallEtaleTopology S U })
    (hE : E ∈ smallEtaleStandardCoverings S U) :
    U ∈ smallEtaleAffineObjects S ∧ ∀ i, E.1.X i ∈ smallEtaleAffineObjects S :=
  IsSmallEtaleStandardCovering.isAffine S hE

/-- The small étale site has finite wide pullbacks: it has finite limits. -/
public instance hasFiniteWidePullbacks_etale : HasFiniteWidePullbacks S.Etale :=
  hasFiniteWidePullbacks_of_hasFiniteLimits _

/-- The slice of all schemes over `S` has finite wide pullbacks: it has finite limits. -/
public instance hasFiniteWidePullbacks_over : HasFiniteWidePullbacks (Over S) :=
  hasFiniteWidePullbacks_of_hasFiniteLimits _

/-- The functor from the small étale site of `S` to all schemes, taking an object to the total
space of its structure morphism. -/
public abbrev smallEtaleToScheme : S.Etale ⥤ Scheme.{u} :=
  Scheme.Etale.forget S ⋙ Over.forget S

/-- An iterated fibre product, in the small étale site, of objects with affine total space over
an object with affine total space again has affine total space. -/
public theorem isAffine_left_piObj {U : S.Etale} (hU : IsAffine U.left)
    (E : PreZeroHypercover.{u} U) (hX : ∀ i, IsAffine (E.X i).left) (p : ℕ)
    (i : Fin (p + 1) → E.I₀) :
    IsAffine ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left).left := by
  let u : S.Etale ⥤ Scheme.{u} := smallEtaleToScheme S
  let A : Fin (p + 1) → Over U := fun a ↦ Over.mk (E.f (i a))
  let : IsAffine (u.obj U) := hU
  let : PreservesLimit (Discrete.functor A) (Over.post (X := U) u) :=
    Stacks.Sites.preservesLimit_fibreProducts_overPost u E
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) p i
  have hF : ∀ a, IsAffineHom ((Over.post (X := U) u).obj (A a)).hom := fun a ↦ by
    let : IsAffine ((Over.post (X := U) u).obj (A a)).left := hX (i a)
    exact isAffineHom_of_isAffine _
  let : IsAffineHom (∏ᶜ (fun a ↦ (Over.post (X := U) u).obj (A a))).hom :=
    isAffineHom_over_finiteProduct _ hF
  have := isAffine_of_isAffineHom (∏ᶜ (fun a ↦ (Over.post (X := U) u).obj (A a))).hom
  have e : ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left).left ≅
      (∏ᶜ (fun a ↦ (Over.post (X := U) u).obj (A a))).left :=
    (Over.forget (u.obj U)).mapIso (PreservesProduct.iso (Over.post (X := U) u) A)
  exact IsAffine.of_isIso e.hom

/-- The iterated fibre products of a small-étale-standard covering of an object of the small
étale site exist. -/
public theorem smallEtaleStandardCoverings_hasProducts :
    ∀ {U : S.Etale}
      (E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ Scheme.smallEtaleTopology S U }),
      E ∈ smallEtaleStandardCoverings S U → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        HasProduct (fun a ↦ Over.mk (E.1.f (i a))) :=
  fun _ _ _ _ ↦ inferInstance

/-- The iterated fibre products of the image under `AlgebraicGeometry.Scheme.Etale.forget` of a
small-étale-standard covering exist. -/
public theorem smallEtaleStandardCoverings_hasImageProducts :
    ∀ {U : S.Etale}
      (E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ Scheme.smallEtaleTopology S U }),
      E ∈ smallEtaleStandardCoverings S U → ∀ (p : ℕ)
        (i : Fin (p + 1) → (E.1.map (Scheme.Etale.forget S)).I₀),
        HasProduct (fun a ↦ Over.mk ((E.1.map (Scheme.Etale.forget S)).f (i a))) :=
  fun _ _ _ _ ↦ inferInstance

/-- The target of a small-étale-standard covering, each of its members, and each of its iterated
fibre products is an object with affine total space. -/
public theorem smallEtaleStandardCoverings_covObjects :
    ∀ {U : S.Etale}
      (E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ Scheme.smallEtaleTopology S U })
      (hE : E ∈ smallEtaleStandardCoverings S U),
      U ∈ smallEtaleAffineObjects S ∧ (∀ i, E.1.X i ∈ smallEtaleAffineObjects S) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) :=
              smallEtaleStandardCoverings_hasProducts S E hE
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ smallEtaleAffineObjects S := by
  intro U E hE
  obtain ⟨hU, hX⟩ := IsSmallEtaleStandardCovering.isAffine S hE
  exact ⟨hU, hX, fun p i ↦ isAffine_left_piObj S hU E.1 hX p i⟩

/-- Every covering sieve of an object with affine total space of the small étale site contains a
small-étale-standard covering. -/
public theorem smallEtaleStandardCoverings_cofinal :
    ∀ U ∈ smallEtaleAffineObjects S, ∀ R ∈ Scheme.smallEtaleTopology S U,
      ∃ E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ Scheme.smallEtaleTopology S U },
        E ∈ smallEtaleStandardCoverings S U ∧ E.1.sieve₀ ≤ R := by
  intro U hU R hR
  obtain ⟨E, hEstd, hER⟩ := exists_isSmallEtaleStandardCovering_sieve₀_le S hU hR
  exact ⟨⟨E, IsSmallEtaleStandardCovering.sieve₀_mem_smallEtaleTopology S E hEstd⟩, hEstd, hER⟩

end AlgebraicGeometry
