module

public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.BigSchemeCategory
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhCoveringOfHom
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.CoveringsParts0DBI
public import StacksFrontier.CategoryTheory.Sites.Pretopology.CoveringClosure

/-!
# Big ph sites (Stacks 0DBJ)

A big ph site is constructed from a set of schemes `S₀` and a set `Cov₀` of ph coverings among
them, by taking as underlying category the category `Sch_α` that Stacks 000J constructs from
`S₀`, and as coverings a set of ph coverings of `Sch_α` as in Stacks 000X, starting from `Cov₀`.

## Main definitions

* `AlgebraicGeometry.IsPHCoveringIn`: a family of morphisms in a full subcategory of schemes is a
  ph covering if its image in the category of schemes is one (Stacks 0DBG).
* `AlgebraicGeometry.StacksBigPHSite`: the choices defining a big ph site.
* `AlgebraicGeometry.StacksBigPHSite.Schemes`: its underlying category `Sch_α`.
* `AlgebraicGeometry.StacksBigPHSite.Cov`: its set of coverings.
* `AlgebraicGeometry.StacksBigPHSite.topology`: the Grothendieck topology they generate.

## Main results

* `AlgebraicGeometry.StacksBigPHSite.small_objects`: the objects of `Sch_α` form a set.
* `AlgebraicGeometry.StacksBigPHSite.small_Cov`: the coverings form a set.
* `AlgebraicGeometry.StacksBigPHSite.isPHCoveringIn_of_mem_Cov`: every covering is a ph covering.
* `AlgebraicGeometry.StacksBigPHSite.exists_mem_Cov_of_mem_Cov₀`: Stacks 000X (1), `Cov₀ ⊂ Cov`.
* `AlgebraicGeometry.StacksBigPHSite.isSite_Cov`: Stacks 000X (2), the coverings satisfy the
  axioms of a site (Stacks 00VH).
* `AlgebraicGeometry.StacksBigPHSite.exists_combEquiv`: Stacks 000X (3), every ph covering of
  `Sch_α` is combinatorially equivalent to a covering of the site.

## Implementation notes

The underlying category is `AlgebraicGeometry.bigSchemeCategory`, the construction in the proof
of Stacks 000J, and its properties (1)–(4) are proved there. The set of coverings is
`Covering.closure` of the members of `Cov₀` together with, for each ph covering of `Sch_α`, the
covering indexed by its set of arrows; the stages of that closure play the role of the stages
`V_α` in Stacks 000X.

## References

* [Stacks Project, Tag 0DBJ](https://stacks.math.columbia.edu/tag/0DBJ)
* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 000X](https://stacks.math.columbia.edu/tag/000X)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A family of morphisms with fixed target in a full subcategory `P` of schemes is a ph covering
(Stacks 0DBG) if its image in the category of schemes is a ph covering. -/
public abbrev IsPHCoveringIn (P : ObjectProperty Scheme.{u})
    (𝒰 : Covering.{u + 1, u, u} P.FullSubcategory) : Prop :=
  IsPHCovering (𝒰.2.map P.ι).X (𝒰.2.map P.ι).f

variable {P : ObjectProperty Scheme.{u}}

/-- Being a ph covering only depends on the morphisms of the family. -/
private lemma isPHCovering_of_eq {T : Scheme.{u}} {I : Type u} {X : I → Scheme.{u}}
    {f g : ∀ i, X i ⟶ T} (h : IsPHCovering X f) (hfg : ∀ i, f i = g i) : IsPHCovering X g := by
  obtain rfl : f = g := funext hfg
  exact h

/-- Composing a ph covering with the identification of its target with an equal scheme gives a
ph covering. -/
private lemma isPHCovering_comp_eqToHom {T T' : Scheme.{u}} (e : T = T') {I : Type u}
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T} (h : IsPHCovering X f) :
    IsPHCovering X (fun i => f i ≫ eqToHom e) := by
  subst e
  simpa using h

/-- A family combinatorially equivalent (Stacks 00VU (1)) to a ph covering is a ph covering. -/
public theorem IsPHCoveringIn.of_combEquiv {𝒰 𝒱 : Covering.{u + 1, u, u} P.FullSubcategory}
    (h : Covering.CombEquiv 𝒰 𝒱) (h𝒰 : IsPHCoveringIn P 𝒰) : IsPHCoveringIn P 𝒱 := by
  obtain ⟨U, E⟩ := 𝒰
  obtain ⟨W, F⟩ := 𝒱
  obtain ⟨hUW, hc⟩ := h
  change U = W at hUW
  cases hUW
  change PreZeroHypercover.CombinatoriallyEquivalent E F at hc
  obtain ⟨⟨α, hX, hf⟩, ⟨β, hY, hg⟩⟩ := hc
  refine IsPHCovering.of_hom (E := E.map P.ι) (F := F.map P.ι) h𝒰
    ⟨α, fun i => eqToHom (congrArg P.ι.obj (hX i)), fun i => ?_⟩ fun j => ?_
  · change eqToHom _ ≫ P.ι.map (F.f (α i)) = P.ι.map (E.f i)
    rw [hf i, Functor.map_comp, eqToHom_map]
  · have : LocallyOfFiniteType (P.ι.map (E.f (β j))) := h𝒰.1 (β j)
    change LocallyOfFiniteType (P.ι.map (F.f j))
    rw [hg j, Functor.map_comp, eqToHom_map]
    infer_instance

/-- The one-element family of an isomorphism is a ph covering. -/
public theorem isPHCoveringIn_singleton {U V : P.FullSubcategory} (f : V ⟶ U) [IsIso f] :
    IsPHCoveringIn P ⟨U, PreZeroHypercover.singleton.{u} f⟩ := by
  have h := isPHCovering_of_isIso (P.ι.map f)
  exact IsPHCovering.of_hom (E := ⟨Unit, fun _ => P.ι.obj V, fun _ => P.ι.map f⟩) h
    ⟨fun _ => PUnit.unit, fun _ => 𝟙 _, fun _ => Category.id_comp _⟩ fun _ => h.1 ()

/-- **Stacks 0DBI (2).** The composition of ph coverings is a ph covering. -/
public theorem isPHCoveringIn_bind {𝒰 : Covering.{u + 1, u, u} P.FullSubcategory}
    (h𝒰 : IsPHCoveringIn P 𝒰) (𝒱 : 𝒰.2.I₀ → Covering.{u + 1, u, u} P.FullSubcategory)
    (h𝒱 : ∀ i, IsPHCoveringIn P (𝒱 i)) (h : ∀ i, (𝒱 i).1 = 𝒰.2.X i) :
    IsPHCoveringIn P ⟨𝒰.1, 𝒰.2.bind fun i => (𝒱 i).2.pushforward (eqToHom (h i))⟩ := by
  have hF (i : 𝒰.2.I₀) : IsPHCovering (((𝒱 i).2.pushforward (eqToHom (h i))).map P.ι).X
      (((𝒱 i).2.pushforward (eqToHom (h i))).map P.ι).f :=
    isPHCovering_of_eq (isPHCovering_comp_eqToHom (congrArg P.ι.obj (h i)) (h𝒱 i))
      fun j => by
        change P.ι.map ((𝒱 i).2.f j) ≫ eqToHom _ = P.ι.map ((𝒱 i).2.f j ≫ eqToHom (h i))
        rw [Functor.map_comp, eqToHom_map]
  exact isPHCovering_of_eq (isPHCovering_bind (𝒰.2.map P.ι) h𝒰 _ hF)
    fun ij => (P.ι.map_comp _ _).symm

/-- **Stacks 0DBI (3).** The base change of a ph covering along any morphism, by the fibre
products of the full subcategory, is a ph covering, provided these fibre products are fibre
products of schemes. -/
public theorem isPHCoveringIn_baseChange [HasPullbacks P.FullSubcategory]
    [PreservesLimitsOfShape WalkingCospan P.ι] {𝒰 : Covering.{u + 1, u, u} P.FullSubcategory}
    (h𝒰 : IsPHCoveringIn P 𝒰) {V : P.FullSubcategory} (g : V ⟶ 𝒰.1) :
    IsPHCoveringIn P (𝒰.baseChange g) := by
  have h := isPHCovering_pullback h𝒰 (P.ι.map g)
  refine IsPHCovering.of_hom (E := ⟨𝒰.2.I₀, fun i => pullback (P.ι.map (𝒰.2.f i)) (P.ι.map g),
      fun i => pullback.snd _ _⟩) h
    ⟨id, fun i => (PreservesPullback.iso P.ι (𝒰.2.f i) g).inv,
      fun i => PreservesPullback.iso_inv_snd P.ι (𝒰.2.f i) g⟩ fun i => ?_
  change LocallyOfFiniteType (P.ι.map (pullback.snd (𝒰.2.f i) g))
  rw [← PreservesPullback.iso_hom_snd]
  have : LocallyOfFiniteType (P.ι.map (𝒰.2.f i)) := h𝒰.1 i
  infer_instance

/-- The closure step for coverings preserves the property of consisting of ph coverings. -/
public theorem isPHCoveringIn_of_closureStep [HasPullbacks P.FullSubcategory]
    [PreservesLimitsOfShape WalkingCospan P.ι]
    (T : Covering.{u + 1, u, u} P.FullSubcategory → Prop) (hT : ∀ 𝒰, T 𝒰 → IsPHCoveringIn P 𝒰)
    (𝒰 : Covering.{u + 1, u, u} P.FullSubcategory) (h : Covering.closureStep T 𝒰) :
    IsPHCoveringIn P 𝒰 := by
  cases h with
  | of_mem h => exact hT _ h
  | singleton f => exact isPHCoveringIn_singleton f
  | bind h𝒰 𝒱 h𝒱 h => exact isPHCoveringIn_bind (hT _ h𝒰) 𝒱 (fun i => hT _ (h𝒱 i)) h
  | baseChange h𝒰 g => exact isPHCoveringIn_baseChange (hT _ h𝒰) g

/-- **Stacks 0DBJ.** A *big ph site*: a site `Sch_ph` in the sense of Stacks 00VH, whose coverings
form a set, constructed as follows.

1. A set of schemes `S₀`, and a set `Cov₀` of ph coverings (Stacks 0DBG) among these schemes:
   the fields `S₀`, `Cov₀` and the conditions on them.
2. As underlying category the category `Sch_α` constructed as in Stacks 000J starting with `S₀`:
   `AlgebraicGeometry.bigSchemeCategory S₀ ordinal`, for the limit ordinal `ordinal` of
   uncountable cofinality at which the construction in the proof of Stacks 000J is stopped. Its
   objects form a set (`AlgebraicGeometry.StacksBigPHSite.small_objects`), and it satisfies
   (1)–(4) of Stacks 000J (`AlgebraicGeometry.bigSchemeCategory_of_mem`,
   `AlgebraicGeometry.exists_bigSchemeCategory_iso_of_size_le`,
   `AlgebraicGeometry.preservesLimit_bigSchemeCategory_ι`,
   `AlgebraicGeometry.preservesColimit_bigSchemeCategory_ι`).
3. A set of coverings as in Stacks 000X starting with `Sch_α`, the class of ph coverings and
   `Cov₀`: `AlgebraicGeometry.StacksBigPHSite.Cov`. It is a set of ph coverings
   (`AlgebraicGeometry.StacksBigPHSite.small_Cov`,
   `AlgebraicGeometry.StacksBigPHSite.isPHCoveringIn_of_mem_Cov`) containing `Cov₀`
   (`AlgebraicGeometry.StacksBigPHSite.exists_mem_Cov_of_mem_Cov₀`), satisfying the axioms of a
   site (`AlgebraicGeometry.StacksBigPHSite.isSite_Cov`), and every ph covering of `Sch_α` is
   combinatorially equivalent to a member (`AlgebraicGeometry.StacksBigPHSite.exists_combEquiv`).

Lean's type theory has no von Neumann hierarchy in which schemes and families of morphisms live;
what the stages `V_α` provide in Stacks 000J and 000X is that the objects and the coverings form
*sets*, which is `Small.{u}` here, `u` being the universe of the sets underlying the schemes. -/
@[stacks 0DBJ]
public structure StacksBigPHSite where
  /-- The chosen set of schemes. -/
  S₀ : Set Scheme.{u}
  /-- `S₀` is a set. -/
  small_S₀ : Small.{u} S₀
  /-- The chosen set of ph coverings among the schemes of `S₀`. -/
  Cov₀ : Set (Covering.{u + 1, u, u} Scheme.{u})
  /-- `Cov₀` is a set. -/
  small_Cov₀ : Small.{u} Cov₀
  /-- Every member of `Cov₀` is a ph covering. -/
  isPHCovering_of_mem_Cov₀ : ∀ 𝒰 ∈ Cov₀, IsPHCovering 𝒰.2.X 𝒰.2.f
  /-- The target and every source of a member of `Cov₀` belong to `S₀`. -/
  mem_S₀_of_mem_Cov₀ : ∀ 𝒰 ∈ Cov₀, 𝒰.1 ∈ S₀ ∧ ∀ i, 𝒰.2.X i ∈ S₀
  /-- The ordinal at which the construction of Stacks 000J is stopped. -/
  ordinal : Ordinal.{u}
  /-- The ordinal has uncountable cofinality. -/
  aleph0_lt_cof_ordinal : ℵ₀ < ordinal.cof

namespace StacksBigPHSite

variable (B : StacksBigPHSite.{u})

/-- The chosen set of schemes is small. -/
public instance : Small.{u} B.S₀ := B.small_S₀

/-- The chosen set of initial coverings is small. -/
public instance : Small.{u} B.Cov₀ := B.small_Cov₀

/-- The objects of the underlying category `Sch_α` of a big ph site. -/
public abbrev objects : ObjectProperty Scheme.{u} := bigSchemeCategory B.S₀ B.ordinal

/-- The underlying category `Sch_α` of a big ph site. -/
public abbrev Schemes : Type (u + 1) := B.objects.FullSubcategory

/-- The inclusion of the underlying category of a big ph site into the category of schemes. -/
public abbrev inclusion : B.Schemes ⥤ Scheme.{u} := B.objects.ι

/-- The objects of the underlying category of a big ph site form a set. -/
public instance small_objects : ObjectProperty.Small.{u} B.objects :=
  small_bigSchemeCategory

/-- The underlying category of a big ph site has fibre products. -/
public instance hasPullbacks : HasPullbacks B.Schemes :=
  hasPullbacks_bigSchemeCategory B.aleph0_lt_cof_ordinal

/-- The fibre products of the underlying category of a big ph site are fibre products of
schemes. -/
public instance preservesPullbacks_inclusion :
    PreservesLimitsOfShape WalkingCospan B.inclusion :=
  preservesPullbacks_bigSchemeCategory_ι B.aleph0_lt_cof_ordinal

/-- Every scheme of `S₀` is an object of the underlying category. -/
public theorem objects_of_mem_S₀ {X : Scheme.{u}} (hX : X ∈ B.S₀) : B.objects X :=
  bigSchemeCategory_of_mem hX

/-- A member of `Cov₀`, regarded as a family of morphisms of the underlying category. -/
public def liftCov₀ (𝒰 : B.Cov₀) : Covering.{u + 1, u, u} B.Schemes :=
  ⟨⟨𝒰.1.1, B.objects_of_mem_S₀ (B.mem_S₀_of_mem_Cov₀ _ 𝒰.2).1⟩,
    ⟨𝒰.1.2.I₀, fun i => ⟨𝒰.1.2.X i, B.objects_of_mem_S₀ ((B.mem_S₀_of_mem_Cov₀ _ 𝒰.2).2 i)⟩,
      fun i => ObjectProperty.homMk (𝒰.1.2.f i)⟩⟩

/-- The coverings generating the coverings of a big ph site: the members of `Cov₀`, and for each
ph covering of the underlying category the covering indexed by its set of arrows. -/
public def generators (𝒰 : Covering.{u + 1, u, u} B.Schemes) : Prop :=
  𝒰 ∈ Set.range B.liftCov₀ ∨
    ∃ 𝒱 : Covering.{u + 1, u, u} B.Schemes, IsPHCoveringIn B.objects 𝒱 ∧
      𝒰 = Covering.ofArrows 𝒱.1 𝒱.arrows

/-- The generating coverings form a set. -/
public instance small_generators : Small.{u} (Subtype B.generators) := by
  let f : B.Cov₀ ⊕ (Σ U : B.Schemes, Set (Σ V : B.Schemes, V ⟶ U)) →
      Covering.{u + 1, u, u} B.Schemes := fun
    | .inl 𝒰 => B.liftCov₀ 𝒰
    | .inr p => Covering.ofArrows p.1 p.2
  have hsub : {𝒰 | B.generators 𝒰} ⊆ Set.range f := by
    rintro 𝒰 (⟨𝒱, rfl⟩ | ⟨𝒱, -, rfl⟩)
    · exact ⟨.inl 𝒱, rfl⟩
    · exact ⟨.inr ⟨𝒱.1, 𝒱.arrows⟩, rfl⟩
  exact small_subset hsub

/-- **Stacks 0DBJ (3).** The set of coverings of a big ph site, as in Stacks 000X. -/
public def Cov : Set (Covering.{u + 1, u, u} B.Schemes) :=
  {𝒰 | Covering.closure B.generators 𝒰}

/-- The coverings of a big ph site form a set. -/
public theorem small_Cov : Small.{u} B.Cov :=
  Covering.small_closure B.small_generators

/-- Every covering of a big ph site is a ph covering. -/
public theorem isPHCoveringIn_of_mem_Cov {𝒰 : Covering.{u + 1, u, u} B.Schemes}
    (h : 𝒰 ∈ B.Cov) : IsPHCoveringIn B.objects 𝒰 := by
  refine Covering.closure_induction _ ?_ isPHCoveringIn_of_closureStep h
  rintro 𝒰 (⟨𝒱, rfl⟩ | ⟨𝒱, h𝒱, rfl⟩)
  · exact B.isPHCovering_of_mem_Cov₀ _ 𝒱.2
  · exact h𝒱.of_combEquiv (Covering.combEquiv_ofArrows 𝒱)

/-- **Stacks 000X (1).** Every member of `Cov₀` is a covering of the big ph site. -/
public theorem exists_mem_Cov_of_mem_Cov₀ {𝒰 : Covering.{u + 1, u, u} Scheme.{u}}
    (h : 𝒰 ∈ B.Cov₀) : ∃ 𝒱 ∈ B.Cov,
      (⟨B.inclusion.obj 𝒱.1, 𝒱.2.map B.inclusion⟩ : Covering.{u + 1, u, u} Scheme.{u}) = 𝒰 :=
  ⟨B.liftCov₀ ⟨𝒰, h⟩, Covering.le_closure _ (Or.inl ⟨_, rfl⟩), rfl⟩

/-- **Stacks 000X (2).** The coverings of a big ph site satisfy the axioms of a site (Stacks
00VH). -/
public theorem isSite_Cov : IsSite (· ∈ B.Cov) :=
  Covering.isSite_closure

/-- **Stacks 000X (3).** Every ph covering of the underlying category of a big ph site is
combinatorially equivalent (Stacks 00VU (1)) to a covering of the site. -/
public theorem exists_combEquiv {𝒰 : Covering.{u + 1, u, u} B.Schemes}
    (h : IsPHCoveringIn B.objects 𝒰) : ∃ 𝒱 ∈ B.Cov, Covering.CombEquiv 𝒰 𝒱 :=
  ⟨_, Covering.le_closure _ (Or.inr ⟨𝒰, h, rfl⟩), Covering.combEquiv_ofArrows 𝒰⟩

/-- The precoverage of a big ph site: the presieves of its coverings. -/
public def precoverage : Precoverage B.Schemes where
  coverings X := {R | ∃ 𝒰 : PreZeroHypercover.{u} X, R = 𝒰.presieve₀ ∧ ⟨X, 𝒰⟩ ∈ B.Cov}

/-- The Grothendieck topology of a big ph site, generated by its coverings. -/
public abbrev topology : GrothendieckTopology B.Schemes :=
  B.precoverage.toGrothendieck

/-- A covering of a big ph site generates a covering sieve of its topology. -/
public theorem generate_mem_topology {𝒰 : Covering.{u + 1, u, u} B.Schemes} (h : 𝒰 ∈ B.Cov) :
    Sieve.generate 𝒰.2.presieve₀ ∈ B.topology 𝒰.1 :=
  Precoverage.generate_mem_toGrothendieck ⟨𝒰.2, rfl, h⟩

/-- Every ph covering of the underlying category of a big ph site generates a covering sieve of
its topology: it is combinatorially equivalent to a covering of the site, and combinatorially
equivalent families generate the same presieve. -/
public theorem generate_mem_topology_of_isPHCoveringIn {𝒰 : Covering.{u + 1, u, u} B.Schemes}
    (h : IsPHCoveringIn B.objects 𝒰) : Sieve.generate 𝒰.2.presieve₀ ∈ B.topology 𝒰.1 := by
  obtain ⟨𝒱, h𝒱, hUV, hE⟩ := B.exists_combEquiv h
  obtain ⟨U, E⟩ := 𝒰
  obtain ⟨V, F⟩ := 𝒱
  change U = V at hUV
  cases hUV
  change PreZeroHypercover.CombinatoriallyEquivalent E F at hE
  rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hE]
  exact B.generate_mem_topology h𝒱

end StacksBigPHSite

end AlgebraicGeometry
