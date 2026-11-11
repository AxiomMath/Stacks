module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
import StacksCore.Tactic.StacksAttribute

/-!
# Sections of a direct sum of pushforwards along a locally finite open covering

Let `X = ⋃ i, U i` be a locally finite open covering of a topological space, let
`j i : U i → X` be the inclusions, and let `F i` be an abelian sheaf on `U i`. Then the
product `∏ i, (j i)_* (F i)`, together with the canonical injections, is also the direct sum
of the `(j i)_* (F i)` in the category of abelian sheaves on `X`; equivalently the canonical
map `∐ i, (j i)_* (F i) ⟶ ∏ i, (j i)_* (F i)` is an isomorphism. Consequently the sections of
the direct sum over an open `V` are the *product* of the groups `(F i) (V ∩ U i)`.

The point is that the direct sum of a family of sheaves is the sheafification of the
presheaf direct sum, and that for a locally finite covering the presheaf direct sum already
agrees with the product over small enough opens: if `W` meets only finitely many of the
`U i`, then for every open `V ⊆ W` all but finitely many of the groups
`((j i)_* (F i)) (V) = (F i) (V ∩ U i)` vanish, and a direct sum of a family of abelian
groups with only finitely many nonzero members is its product. So the comparison map of
presheaves is locally bijective, hence becomes an isomorphism after sheafification.

## Main results

* `Stacks.isIso_of_isZero_of_notMem`: in a preadditive category, a map from a coproduct to a
  product of the same family which is the identity on the diagonal and zero off the diagonal
  is an isomorphism as soon as all but finitely many members of the family are zero objects.
  This is the algebraic heart of the remark.
* `Stacks.LocallyFiniteCover.isColimitCofanProduct` and
  `Stacks.LocallyFiniteCover.isIso_coproductToProduct`: **Tag 02FT**, second displayed
  formula. The first says that the product of the `(j i)_* (F i)` with the canonical
  injections is a coproduct, the second that the canonical map
  `∐ i, (j i)_* (F i) ⟶ ∏ i, (j i)_* (F i)` is an isomorphism.
* `Stacks.LocallyFiniteCover.isIso_sectionsComparison`: **Tag 02FT**, first displayed
  formula: for every open `V` the canonical comparison from `Γ (V, ∐ i, (j i)_* (F i))` to
  `∏ i, (F i) (V ∩ U i)` is an isomorphism.
* `Stacks.locallyFinite_iInter`: the family of the intersections of the tuples of a locally
  finite family of sets is again locally finite. This is the input that makes the third
  displayed formula of the remark, about the terms of the covering resolution of Tag 02FU,
  follow from the same argument as the second one.

The third displayed formula of the remark, that the degree-`p` term of the covering resolution
of Tag 02FU is the direct sum `⨁ (j_{i₀ … i_p})_* F_{i₀ … i_p}`, is
`Stacks.CechTotalComplex.CoveringResolution.isColimitCoveringTermCofan` in
`StacksFrontier/Topology/Sheaves/Cohomology/CechTotalComplex/CoveringResolutionLocallyFinite.lean`.
It is stated there for sheaves of modules over a ringed space, as the source's Lemma 02FU is,
and proved through `Stacks.SheafOfModules.LocallyFiniteProduct.isColimitCofanDeltaInj`.

## Implementation notes

The covering hypothesis `TopologicalSpace.IsOpenCover U` is carried by the tagged statements
because the source states the remark for a covering of `X`, but it is not used: local
finiteness of the family alone gives the conclusions, and the untagged lemmas below are
stated without it.

Everything is for sheaves of abelian groups on a space `X : TopCat.{u}`, with the index type
and the values of the sheaves in the same universe `u` as the space; this is the universe
range in which sheafification of `AddCommGrpCat.{u}`-valued presheaves on `Opens X` is
available. Sheaves are spelled `CategoryTheory.Sheaf (Opens.grothendieckTopology X) _` rather
than `TopCat.Sheaf _ X`, because the latter carries its own `Category` instance, derived from
and definitionally equal to the former but not syntactically equal to it, which the
sheafification API does not see.

## References

* [Stacks Project, Tag 02FT](https://stacks.math.columbia.edu/tag/02FT)
* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks

/-- Let `A : I → 𝒜` be a family of objects of a preadditive category, let `inj i : A i ⟶ Q`
be a jointly epimorphic family (for instance the injections into a coproduct) and let
`proj i : P ⟶ A i` be a jointly monomorphic family (for instance the projections from a
product). A morphism `f : Q ⟶ P` which is the identity on the diagonal and zero off the
diagonal is an isomorphism as soon as `A i` is a zero object for every `i` outside some
finite set `S`.

The inverse is the finite sum `∑ i ∈ S, proj i ≫ inj i`. -/
theorem isIso_of_isZero_of_notMem {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜]
    {I : Type*} {A : I → 𝒜} {Q P : 𝒜} (inj : ∀ i, A i ⟶ Q) (proj : ∀ i, P ⟶ A i)
    (hepi : ∀ {T : 𝒜} (g h : Q ⟶ T), (∀ i, inj i ≫ g = inj i ≫ h) → g = h)
    (hmono : ∀ {T : 𝒜} (g h : T ⟶ P), (∀ i, g ≫ proj i = h ≫ proj i) → g = h)
    (f : Q ⟶ P) (hdiag : ∀ i, inj i ≫ f ≫ proj i = 𝟙 (A i))
    (hoff : ∀ i j, i ≠ j → inj i ≫ f ≫ proj j = 0)
    (S : Finset I) (hS : ∀ i, i ∉ S → IsZero (A i)) : IsIso f := by
  have hd : ∀ i, (inj i ≫ f) ≫ proj i = 𝟙 (A i) := by simpa using hdiag
  have ho : ∀ i j, i ≠ j → (inj i ≫ f) ≫ proj j = 0 := by simpa using hoff
  refine ⟨∑ i ∈ S, proj i ≫ inj i, ?_, ?_⟩
  · refine hepi _ _ fun i => ?_
    simp only [Category.comp_id, ← Category.assoc, Preadditive.comp_sum]
    by_cases hi : i ∈ S
    · rw [Finset.sum_eq_single_of_mem i hi]
      · rw [hd i, Category.id_comp]
      · intro k _ hk
        rw [ho i k (Ne.symm hk), Limits.zero_comp]
    · rw [(hS i hi).eq_zero_of_src (inj i)]
      simp
  · refine hmono _ _ fun j => ?_
    simp only [Category.id_comp, Category.assoc, Preadditive.sum_comp]
    by_cases hj : j ∈ S
    · rw [Finset.sum_eq_single_of_mem j hj]
      · rw [show inj j ≫ f ≫ proj j = 𝟙 (A j) from hdiag j, Category.comp_id]
      · intro k _ hk
        rw [show inj k ≫ f ≫ proj j = 0 from hoff k j hk, Limits.comp_zero]
    · rw [(hS j hj).eq_zero_of_tgt (proj j)]
      simp

/-- If a family of sets is locally finite, then so is the family of the intersections of its
`J`-tuples, for `J` a finite type: a neighbourhood which meets an intersection meets each of
its factors, so the tuples whose intersection meets it form a subset of a product of finitely
many finite sets. -/
theorem locallyFinite_iInter {Y : Type*} [TopologicalSpace Y] {I J : Type*} [Finite J]
    {V : I → Set Y} (hlf : LocallyFinite V) :
    LocallyFinite fun s : J → I => ⋂ k, V (s k) := by
  intro x
  obtain ⟨t, ht, hfin⟩ := hlf x
  refine ⟨t, ht, Set.Finite.subset
    (Set.Finite.pi (t := fun _ : J => {i | (V i ∩ t).Nonempty}) fun _ => hfin) ?_⟩
  rintro s ⟨y, hy, hyt⟩
  rw [Set.mem_univ_pi]
  exact fun k => ⟨y, Set.mem_iInter.mp hy k, hyt⟩

namespace LocallyFiniteCover

variable {X : TopCat.{u}} {I : Type u}

/-- The Grothendieck topology on the opens of a topological space. -/
abbrev site (X : TopCat.{u}) : GrothendieckTopology (Opens X) :=
  Opens.grothendieckTopology X

/-- Abelian sheaves on the site of opens of a space have coproducts of any family indexed by
a type in the universe of the space: they are the sheafifications of the presheaf coproducts.
This is Mathlib's own construction of those colimits, recorded here as a directly applicable
instance because the general one is out of reach of instance search for this site. -/
instance hasColimitsOfShape_sheafOpens :
    HasColimitsOfShape (Discrete I) (Sheaf (site X) AddCommGrpCat.{u}) :=
  ⟨fun _ => HasColimit.mk ⟨Sheaf.sheafifyCocone (colimit.cocone _),
    Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩

/-- Taking sections over the open `V`, as a functor from abelian sheaves on `X` to abelian
groups. -/
noncomputable abbrev sectionsFunctor (V : Opens X) :
    Sheaf (site X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (site X) AddCommGrpCat.{u} ⋙
    (evaluation ((Opens X)ᵒᵖ) AddCommGrpCat.{u}).obj (op V)

/-- Taking sections over a fixed open commutes with products of sheaves of abelian groups:
products of sheaves are computed in presheaves, and there objectwise. -/
theorem preservesLimit_sectionsFunctor (V : Opens X)
    (G : I → Sheaf (site X) AddCommGrpCat.{u}) :
    PreservesLimit (Discrete.functor G) (sectionsFunctor V) := by
  have a : PreservesLimitsOfShape (Discrete I) (sheafToPresheaf (site X) AddCommGrpCat.{u}) :=
    inferInstance
  have : PreservesLimit (Discrete.functor G)
    (sheafToPresheaf (site X) AddCommGrpCat.{u}) := a.preservesLimit
  exact comp_preservesLimit (K := Discrete.functor G) _ _

variable (U : I → Opens X)
    (F : ∀ i, TopCat.Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj (U i)))

/-- The pushforward `(j i)_* (F i)` of the abelian sheaf `F i` on the open `U i` along the
inclusion `j i : U i → X`. -/
noncomputable abbrev pushforwardOpen (i : I) : Sheaf (site X) AddCommGrpCat.{u} :=
  (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (U i).inclusion').obj (F i)

/-- The sections of `(j i)_* (F i)` over an open `V` are the sections of `F i` over the
preimage of `V` in `U i`, that is over `V ∩ U i`. -/
theorem pushforwardOpen_obj_obj (i : I) (V : Opens X) :
    (pushforwardOpen U F i).obj.obj (op V) =
      (F i).obj.obj (op ((Opens.map (U i).inclusion').obj V)) :=
  rfl

/-- The `i`-th factor of the product of the sections over `V`: the sections of `F i` over
`V ∩ U i`. -/
theorem sectionsFunctor_obj_pushforwardOpen (i : I) (V : Opens X) :
    (sectionsFunctor V).obj (pushforwardOpen U F i) =
      (F i).obj.obj (op ((Opens.map (U i).inclusion').obj V)) :=
  rfl

/-- If the open `V` is disjoint from `U i`, then `(j i)_* (F i)` has no nonzero sections over
`V`: those sections are the sections of `F i` over the empty open of `U i`. -/
theorem isZero_pushforwardOpen_obj (V : Opens X) (i : I)
    (h : (V : Set X) ∩ (U i : Set X) = ∅) :
    IsZero ((pushforwardOpen U F i).obj.obj (op V)) := by
  have hb : (Opens.map (U i).inclusion').obj V = ⊥ :=
    Opens.ext <| Set.eq_empty_iff_forall_notMem.mpr fun y hy =>
      Set.eq_empty_iff_forall_notMem.mp h y.1 ⟨hy, y.2⟩
  change IsZero ((F i).obj.obj (op ((Opens.map (U i).inclusion').obj V)))
  rw [hb]
  exact IsZero.of_iso (isZero_zero _)
    ((TopCat.Sheaf.isTerminalOfEmpty (F i)).uniqueUpToIso (isZero_zero _).isTerminal)

open scoped Classical in
/-- The canonical injection of the `i`-th factor into the product `∏ i, (j i)_* (F i)`: its
`j`-th component is the identity for `j = i` and zero otherwise. -/
noncomputable def deltaInj (i : I) :
    pushforwardOpen U F i ⟶ (∏ᶜ fun i => pushforwardOpen U F i) :=
  Pi.lift fun j =>
    if h : i = j then eqToHom (congrArg (fun k => pushforwardOpen U F k) h) else 0

/-- The `i`-th component of the `i`-th canonical injection is the identity. -/
@[simp]
theorem deltaInj_comp_π_self (i : I) :
    deltaInj U F i ≫ Pi.π (fun i => pushforwardOpen U F i) i = 𝟙 _ := by
  rw [deltaInj, Pi.lift_comp_π]
  simp

/-- The `j`-th component of the `i`-th canonical injection vanishes for `j ≠ i`. -/
@[simp]
theorem deltaInj_comp_π_ne {i j : I} (h : i ≠ j) :
    deltaInj U F i ≫ Pi.π (fun i => pushforwardOpen U F i) j = 0 := by
  rw [deltaInj, Pi.lift_comp_π]
  simp [h]

/-- The presheaf direct sum `V ↦ ⨁ i, (F i) (V ∩ U i)`, that is the coproduct of the
`(j i)_* (F i)` formed in presheaves rather than in sheaves. -/
noncomputable abbrev sumPresheaf : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  colimit (Discrete.functor (fun i => pushforwardOpen U F i) ⋙
    sheafToPresheaf (site X) AddCommGrpCat.{u})

/-- The cofan on the product given by the canonical injections. Saying that it is a colimit
cocone is saying that the product is also the direct sum. -/
noncomputable abbrev productCofan : Cofan (fun i => pushforwardOpen U F i) :=
  Cofan.mk (∏ᶜ fun i => pushforwardOpen U F i) (deltaInj U F)

/-- The comparison map of presheaves from the presheaf direct sum to the sections of the
product sheaf. Over an open `V` it is the inclusion of `⨁ i, (F i) (V ∩ U i)` into
`∏ i, (F i) (V ∩ U i)`. -/
noncomputable def sumToProduct :
    sumPresheaf U F ⟶ (∏ᶜ fun i => pushforwardOpen U F i).obj :=
  colimit.desc _ ((sheafToPresheaf (site X) AddCommGrpCat.{u}).mapCocone (productCofan U F))

/-- The `i`-th leg of the presheaf direct sum, followed by the comparison map, is the `i`-th
canonical injection. -/
theorem ι_comp_sumToProduct (i : I) :
    colimit.ι (Discrete.functor (fun i => pushforwardOpen U F i) ⋙
        sheafToPresheaf (site X) AddCommGrpCat.{u}) ⟨i⟩ ≫ sumToProduct U F =
      (sheafToPresheaf (site X) AddCommGrpCat.{u}).map (deltaInj U F i) :=
  colimit.ι_desc _ _

/-- The `i`-th leg of the presheaf direct sum over an open `V`, followed by the comparison
map over `V`, is the `i`-th canonical injection on sections over `V`. -/
theorem ι_app_comp_sumToProduct_app (i : I) (V : Opens X) :
    (colimit.ι (Discrete.functor (fun i => pushforwardOpen U F i) ⋙
          sheafToPresheaf (site X) AddCommGrpCat.{u}) ⟨i⟩).app (op V) ≫
        (sumToProduct U F).app (op V) =
      (sectionsFunctor V).map (deltaInj U F i) := by
  rw [← NatTrans.comp_app, ι_comp_sumToProduct]
  rfl

/-- **The algebraic heart of Tag 02FT.** If the open `V` meets `U i` only for `i` in the
finite set `S`, then the comparison map from the presheaf direct sum to the sections of the
product sheaf is an isomorphism over `V`: a direct sum and the product of a family of abelian
groups with only finitely many nonzero members agree. -/
theorem isIso_sumToProduct_app (V : Opens X) (S : Finset I)
    (hS : ∀ i, i ∉ S → ((V : Set X) ∩ (U i : Set X)) = ∅) :
    IsIso ((sumToProduct U F).app (op V)) := by
  have := preservesLimit_sectionsFunctor V (fun i => pushforwardOpen U F i)
  have hl := isLimitOfPreserves (sectionsFunctor V)
    (productIsProduct fun i => pushforwardOpen U F i)
  have hc := isColimitOfPreserves ((evaluation ((Opens X)ᵒᵖ) AddCommGrpCat.{u}).obj (op V))
    (colimit.isColimit (Discrete.functor (fun i => pushforwardOpen U F i) ⋙
      sheafToPresheaf (site X) AddCommGrpCat.{u}))
  refine isIso_of_isZero_of_notMem
    (A := fun i => (pushforwardOpen U F i).obj.obj (op V))
    (fun i => (colimit.ι (Discrete.functor (fun i => pushforwardOpen U F i) ⋙
      sheafToPresheaf (site X) AddCommGrpCat.{u}) ⟨i⟩).app (op V))
    (fun i => (sectionsFunctor V).map (Pi.π (fun i => pushforwardOpen U F i) i))
    (fun g h hgh => hc.hom_ext (by rintro ⟨i⟩; exact hgh i))
    (fun g h hgh => hl.hom_ext (by rintro ⟨i⟩; exact hgh i))
    _ ?_ ?_ S (fun i hi => isZero_pushforwardOpen_obj U F V i (hS i hi))
  · intro i
    rw [← Category.assoc, ι_app_comp_sumToProduct_app, ← CategoryTheory.Functor.map_comp,
      deltaInj_comp_π_self, CategoryTheory.Functor.map_id]
    rfl
  · intro i j hij
    rw [← Category.assoc, ι_app_comp_sumToProduct_app, ← CategoryTheory.Functor.map_comp,
      deltaInj_comp_π_ne _ _ hij]
    rfl

/-- For a locally finite family, every point of an open `V` has an open neighbourhood inside
`V` over which the comparison map from the presheaf direct sum to the product sheaf is an
isomorphism. -/
theorem exists_isIso_sumToProduct_app (hlf : LocallyFinite fun i => (U i : Set X))
    (V : Opens X) {x : X} (hx : x ∈ V) :
    ∃ V' : Opens X, V' ≤ V ∧ x ∈ V' ∧ IsIso ((sumToProduct U F).app (op V')) := by
  obtain ⟨t, ht, hfin⟩ := hlf x
  obtain ⟨W, hWt, hWo, hxW⟩ := mem_nhds_iff.mp ht
  refine ⟨V ⊓ ⟨W, hWo⟩, inf_le_left, ⟨hx, hxW⟩, ?_⟩
  exact isIso_sumToProduct_app U F _ hfin.toFinset fun i hi =>
    Set.eq_empty_iff_forall_notMem.mpr fun y hy => hi (hfin.mem_toFinset.mpr ⟨y, hy.2, hWt hy.1.2⟩)

/-- For a locally finite family the comparison map from the presheaf direct sum to the product
sheaf is locally surjective: it is surjective over small enough opens. -/
theorem isLocallySurjective_sumToProduct (hlf : LocallyFinite fun i => (U i : Set X)) :
    Presheaf.IsLocallySurjective (site X) (sumToProduct U F) where
  imageSieve_mem {V} s := by
    intro x hx
    obtain ⟨V', hle, hxV', hiso⟩ := exists_isIso_sumToProduct_app U F hlf V hx
    exact ⟨V', homOfLE hle,
      (ConcreteCategory.bijective_of_isIso ((sumToProduct U F).app (op V'))).2 _, hxV'⟩

/-- For a locally finite family the comparison map from the presheaf direct sum to the product
sheaf is locally injective: it is injective over small enough opens. -/
theorem isLocallyInjective_sumToProduct (hlf : LocallyFinite fun i => (U i : Set X)) :
    Presheaf.IsLocallyInjective (site X) (sumToProduct U F) where
  equalizerSieve_mem {V} a b h := by
    intro x hx
    obtain ⟨V', hle, hxV', hiso⟩ := exists_isIso_sumToProduct_app U F hlf V.unop hx
    refine ⟨V', homOfLE hle, ?_, hxV'⟩
    refine (ConcreteCategory.bijective_of_isIso ((sumToProduct U F).app (op V'))).1 ?_
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h]

/-- The map from the sheafification of the presheaf direct sum to the product sheaf induced by
the comparison map of presheaves. -/
noncomputable def sheafifiedSumToProduct :
    (presheafToSheaf (site X) AddCommGrpCat.{u}).obj (sumPresheaf U F) ⟶
      (∏ᶜ fun i => pushforwardOpen U F i) :=
  ⟨sheafifyLift (site X) (sumToProduct U F) (∏ᶜ fun i => pushforwardOpen U F i).2⟩

/-- For a locally finite family the sheafification of the presheaf direct sum is the product
sheaf: the induced map is an isomorphism, because both the comparison map of presheaves and
the sheafification map are locally bijective. -/
theorem isIso_sheafifiedSumToProduct (hlf : LocallyFinite fun i => (U i : Set X)) :
    IsIso (sheafifiedSumToProduct U F) := by
  have := isLocallySurjective_sumToProduct U F hlf
  have := isLocallyInjective_sumToProduct U F hlf
  have fac : toSheafify (site X) (sumPresheaf U F) ≫ (sheafifiedSumToProduct U F).hom =
      sumToProduct U F := toSheafify_sheafifyLift _ _ _
  have h1 : Presheaf.IsLocallySurjective (site X) (sheafifiedSumToProduct U F).hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ fac
  have h2 : Presheaf.IsLocallyInjective (site X) (sheafifiedSumToProduct U F).hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac _ _ fac
  exact (Sheaf.isLocallyBijective_iff_isIso (sheafifiedSumToProduct U F)).1 ⟨h2, h1⟩

/-- The `i`-th canonical map from `(j i)_* (F i)` to the sheafification of the presheaf direct
sum: the `i`-th leg of the presheaf direct sum followed by the sheafification map. -/
noncomputable def toSheafifiedSum (i : I) :
    pushforwardOpen U F i ⟶
      (presheafToSheaf (site X) AddCommGrpCat.{u}).obj (sumPresheaf U F) :=
  ⟨colimit.ι (Discrete.functor (fun i => pushforwardOpen U F i) ⋙
      sheafToPresheaf (site X) AddCommGrpCat.{u}) ⟨i⟩ ≫ toSheafify (site X) (sumPresheaf U F)⟩

/-- The map out of the sheafification of the presheaf direct sum determined by a family of
maps out of the `(j i)_* (F i)`, by the universal property of sheafification applied to the
universal property of the presheaf direct sum. -/
noncomputable def sheafifiedSumDesc (T : Sheaf (site X) AddCommGrpCat.{u})
    (g : ∀ i, pushforwardOpen U F i ⟶ T) :
    (presheafToSheaf (site X) AddCommGrpCat.{u}).obj (sumPresheaf U F) ⟶ T :=
  ⟨sheafifyLift (site X) (colimit.desc _
    ((sheafToPresheaf (site X) AddCommGrpCat.{u}).mapCocone (Cofan.mk T g))) T.2⟩

/-- The defining property of `sheafifiedSumDesc`: it restricts to the given family along the
canonical maps. -/
theorem toSheafifiedSum_comp_sheafifiedSumDesc (T : Sheaf (site X) AddCommGrpCat.{u})
    (g : ∀ i, pushforwardOpen U F i ⟶ T) (i : I) :
    toSheafifiedSum U F i ≫ sheafifiedSumDesc U F T g = g i := by
  apply Sheaf.hom_ext
  change (colimit.ι (Discrete.functor (fun i => pushforwardOpen U F i) ⋙
        sheafToPresheaf (site X) AddCommGrpCat.{u}) ⟨i⟩ ≫
      toSheafify (site X) (sumPresheaf U F)) ≫
      sheafifyLift (site X) (colimit.desc _
        ((sheafToPresheaf (site X) AddCommGrpCat.{u}).mapCocone (Cofan.mk T g))) T.2 = (g i).hom
  rw [Category.assoc, toSheafify_sheafifyLift, colimit.ι_desc]
  rfl

/-- The canonical maps into the sheafification of the presheaf direct sum, followed by the
induced map to the product sheaf, are the canonical injections of the product. -/
theorem toSheafifiedSum_comp_sheafifiedSumToProduct (i : I) :
    toSheafifiedSum U F i ≫ sheafifiedSumToProduct U F = deltaInj U F i := by
  exact toSheafifiedSum_comp_sheafifiedSumDesc U F _ (deltaInj U F) i

/-- **Stacks Project, Tag 02FT, second displayed formula.** Let `X = ⋃ i, U i` be a locally
finite open covering of a topological space, let `j i : U i → X` be the inclusions and let
`F i` be an abelian sheaf on `U i`. Then the product of the `(j i)_* (F i)`, equipped with
the canonical injections `deltaInj`, is a coproduct of the `(j i)_* (F i)`: that is
`⨁ i, (j i)_* (F i) = ∏ i, (j i)_* (F i)`. -/
@[stacks 02FT "(second displayed formula: ⨁ (j_i)_* F_i = ∏ (j_i)_* F_i)"]
noncomputable def isColimitCofanProduct (_hcov : IsOpenCover U)
    (hlf : LocallyFinite fun i => (U i : Set X)) : IsColimit (productCofan U F) := by
  have hiso : IsIso (sheafifiedSumToProduct U F) := isIso_sheafifiedSumToProduct U F hlf
  have hinv : ∀ i, deltaInj U F i ≫ @CategoryTheory.inv _ _ _ _ _ hiso =
      toSheafifiedSum U F i := by
    intro i
    rw [← toSheafifiedSum_comp_sheafifiedSumToProduct U F i, Category.assoc,
      @IsIso.hom_inv_id _ _ _ _ _ hiso, Category.comp_id]
  refine Cofan.IsColimit.mk _
    (fun t => @CategoryTheory.inv _ _ _ _ _ hiso ≫ sheafifiedSumDesc U F t.pt t.inj)
    (fun t j => ?_) (fun t m hm => ?_)
  · change deltaInj U F j ≫ @CategoryTheory.inv _ _ _ _ _ hiso ≫
        sheafifiedSumDesc U F t.pt t.inj = t.inj j
    rw [← Category.assoc, hinv j, toSheafifiedSum_comp_sheafifiedSumDesc]
  · have hm' : ∀ j, deltaInj U F j ≫ m = t.inj j := fun j => hm j
    have key : sheafifiedSumToProduct U F ≫ m = sheafifiedSumDesc U F t.pt t.inj := by
      apply Sheaf.hom_ext
      refine sheafifyLift_unique (site X) _ t.pt.2 _ ?_
      change toSheafify (site X) (sumPresheaf U F) ≫
        sheafifyLift (site X) (sumToProduct U F)
          (∏ᶜ fun i => pushforwardOpen U F i).2 ≫ m.hom = _
      rw [← Category.assoc, toSheafify_sheafifyLift]
      refine colimit.hom_ext fun j => ?_
      rw [← Category.assoc, ι_comp_sumToProduct, colimit.ι_desc]
      exact congrArg (fun φ : pushforwardOpen U F j.as ⟶ t.pt => φ.hom) (hm' j.as)
    rw [← key, ← Category.assoc, @IsIso.inv_hom_id _ _ _ _ _ hiso]
    exact (Category.id_comp m).symm

/-- The canonical map from the coproduct of the `(j i)_* (F i)` to their product: the map
whose `(i, j)` component is the identity when `i = j` and zero otherwise. -/
noncomputable def coproductToProduct :
    (∐ fun i => pushforwardOpen U F i) ⟶ (∏ᶜ fun i => pushforwardOpen U F i) :=
  Sigma.desc (deltaInj U F)

/-- **Stacks Project, Tag 02FT, second displayed formula.** For a locally finite open
covering the canonical map from the direct sum of the `(j i)_* (F i)` to their direct product
is an isomorphism. -/
@[stacks 02FT "(second displayed formula, as an isomorphism from ∐ to ∏)"]
theorem isIso_coproductToProduct (hcov : IsOpenCover U)
    (hlf : LocallyFinite fun i => (U i : Set X)) : IsIso (coproductToProduct U F) := by
  have h := isColimitCofanProduct U F hcov hlf
  refine ⟨h.desc (Cofan.mk (∐ fun i => pushforwardOpen U F i)
    (Sigma.ι fun i => pushforwardOpen U F i)), ?_, ?_⟩
  · refine colimit.hom_ext fun j => ?_
    obtain ⟨i⟩ := j
    simp only [coproductToProduct, Category.comp_id, ← Category.assoc, colimit.ι_desc]
    exact h.fac _ ⟨i⟩
  · refine h.hom_ext fun j => ?_
    obtain ⟨i⟩ := j
    simp only [coproductToProduct, ← Category.assoc, h.fac]
    exact colimit.ι_desc _ (Discrete.mk i)

/-- **Stacks Project, Tag 02FT, first displayed formula.** With `X = ⋃ i, U i` a locally
finite open covering and `𝒢 = ⨁ i, (j i)_* (F i)`, for every open `V` of `X` the canonical
comparison from `Γ (V, 𝒢)` to `∏ i, (F i) (V ∩ U i)` is an isomorphism: the sections of the
direct sum over `V` are the *product* of the groups `(F i) (V ∩ U i)`.

The comparison is the sections over `V` of the canonical map from the direct sum to the
product, followed by the canonical comparison from the sections of a product of sheaves to
the product of their sections. The `i`-th factor of the target is
`(sectionsFunctor V).obj (pushforwardOpen U F i)`, which is `(F i) (V ∩ U i)` by
`Stacks.LocallyFiniteCover.sectionsFunctor_obj_pushforwardOpen`. -/
@[stacks 02FT "(first displayed formula: Γ(V, 𝒢) = ∏ F_i(V ∩ U_i))"]
theorem isIso_sectionsComparison (hcov : IsOpenCover U)
    (hlf : LocallyFinite fun i => (U i : Set X)) (V : Opens X) :
    IsIso ((sectionsFunctor V).map (coproductToProduct U F) ≫
      piComparison (sectionsFunctor V) (fun i => pushforwardOpen U F i)) := by
  have hpl : PreservesLimit (Discrete.functor fun i => pushforwardOpen U F i)
      (sectionsFunctor V) := preservesLimit_sectionsFunctor V _
  have hc : IsIso (coproductToProduct U F) := isIso_coproductToProduct U F hcov hlf
  have h1 : IsIso ((sectionsFunctor V).map (coproductToProduct U F)) :=
    @Functor.map_isIso _ _ _ _ _ _ (sectionsFunctor V) (coproductToProduct U F) hc
  have h2 : IsIso (piComparison (sectionsFunctor V) (fun i => pushforwardOpen U F i)) := by
    rw [← PreservesProduct.iso_hom (G := sectionsFunctor V)]
    infer_instance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

end LocallyFiniteCover

end Stacks

end
