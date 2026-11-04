module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumBijection
public import StacksFrontier.AlgebraicGeometry.FormalScheme.SchemeToFormalScheme
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The functor of points of a formal scheme

Fix a cardinal `κ` cutting the class of all schemes down to the set `Sch_κ` of schemes of size
below `κ`, as in Stacks 000J. A formal scheme `𝔛` has a *functor of points* on `Sch_κ`, the
presheaf `h_𝔛(S) = Mor_{Formal Schemes}(S, 𝔛)`, a scheme being viewed as a formal scheme through
the fully faithful functor of Stacks 0AI0. Stacks 0AI1 asserts that

`Mor_{Formal Schemes}(𝔛, 𝔜) = Mor_{PSh(Sch_κ)}(h_𝔛, h_𝔜)`

provided the size of `𝔛` is not too large; the source's analysis of what "not too large" has to
mean is that the schemes `Spec (A/I_λ)` cut out of the affine formal charts `Spf A` of `𝔛` by
the ideals of definition `I_λ` must be objects of `Sch_κ`.

The injectivity half of that identification is proved here: a morphism of formal schemes is
determined by the natural transformation it induces on functors of points. The point is that the
morphisms `Spec (A/I_λ) → Spf A ≅ 𝔛|_𝔘 → 𝔛` coming from the charts of `𝔛` are jointly
epimorphic. Their underlying maps cover `𝔛`, because each `Spec (A/I_λ) → Spf A` is a
homeomorphism; and the comparison maps they induce on the sections of `𝒪_𝔛` over an open set are
jointly monomorphic, because `𝒪_𝔛` is a sheaf and `𝒪_{Spf A} = lim 𝒪_λ`.

## Main definitions

* `AlgebraicGeometry.schemeCutoff`: the schemes of size below `κ`, the model of the source's
  category `Sch_α` fixed in `StacksFrontier.AlgebraicGeometry.Size.Cutoff`.
* `AlgebraicGeometry.formalSchemeFunctorOfPoints`: the functor sending a formal scheme to its
  functor of points on `Sch_κ`.
* `AlgebraicGeometry.IsSizeBoundedFormalScheme`: the source's size condition on a formal scheme.
* `AlgebraicGeometry.spfPointOn`: the morphism `Spec (A/I) → Spf A` of presheafed spaces of
  topological rings attached to an ideal of definition `I`.
* `AlgebraicGeometry.formalChartPointOn`: the morphism `Spec (A/I) → 𝔛` of locally topologically
  ringed spaces attached to an affine formal chart `𝔛|_𝔘 ≅ Spf A` of `𝔛`.

## Main results

* `AlgebraicGeometry.injective_formalSchemeFunctorOfPoints_map`: **Stacks 0AI1**, injectivity.
  A morphism between formal schemes whose source satisfies the size condition is determined by
  the natural transformation of functors of points it induces.
* `AlgebraicGeometry.spfPointOn_hom_ext`: two morphisms into the sections of `𝒪_{Spf A}` over an
  open set agree as soon as they agree after composition with the comparison maps of all the
  `Spec (A/I) → Spf A`.
* `AlgebraicGeometry.presheaf_hom_ext_of_cover` and
  `AlgebraicGeometry.presheafedSpace_hom_ext_of_cover`: the two separation statements the proof
  rests on, for a sheaf of topological rings over an open covering and for morphisms of
  presheafed spaces out of a space covered by a family of morphisms.

## Implementation notes

The surjectivity half of the identification is not proved here, but it is proved in
`StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFull`:
`AlgebraicGeometry.exists_formalSchemeFunctorOfPoints_map_eq` says that every transformation
`h_𝔛 → h_𝔜` is induced by a morphism `𝔛 → 𝔜`, and
`AlgebraicGeometry.bijective_formalSchemeFunctorOfPoints_map` is the bijection of the source.
The injectivity below is one of its two halves.

The size condition is phrased exactly as the source's analysis leaves it: it is enough that the
`Spec (A/I_λ)` be isomorphic to objects of `Sch_α`. Since `AlgebraicGeometry.Scheme.size` is an
isomorphism invariant, "isomorphic to an object of `Sch_κ`" is `size _ < κ` on the nose, as
explained in `StacksFrontier.AlgebraicGeometry.Size.Cutoff`.

The pseudo-discrete topology on the sections of the pushforward of a presheaf of rings is taken
over the quasi-compact opens of the target, while that of the pushforward of the
pseudo-discretisation is taken over the quasi-compact opens of the source. The two agree along
`Spec (A/I) → Spf A`, which is a homeomorphism, and `AlgebraicGeometry.spfComponentPDOn` is the
resulting comparison morphism; it is the identity on sections, so it is a monomorphism, which is
all that the separation argument needs of it.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Tag 0AI1](https://stacks.math.columbia.edu/tag/0AI1)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open scoped Topology

universe u

namespace TopCommRingCat

/-- A composite of local homomorphisms of topological rings is a local homomorphism. This is
`CommRingCat.isLocalHom_comp` for topological rings. -/
@[ega "0 1.0.7" "continuous homomorphisms"]
theorem isLocalHom_comp {R S T : TopCommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    [IsLocalHom f.1] [IsLocalHom g.1] : IsLocalHom (f ≫ g).1 :=
  RingHom.isLocalHom_comp g.1 f.1

end TopCommRingCat

namespace AlgebraicGeometry

open TopologicalRing

/-! ### Separation along a covering -/

/-- Two morphisms into the sections of a sheaf of topological rings over an open set agree as
soon as they agree after restriction to each member of a family of opens covering that set. -/
theorem presheaf_hom_ext_of_cover {X : TopCat.{u}} {F : X.Presheaf TopCommRingCat.{u}}
    (hF : F.IsSheaf) {ι : Type u} (V : ι → Opens X) {W : Opens X} (k : ∀ i, V i ⟶ W)
    (hcov : ∀ p ∈ W, ∃ i, p ∈ V i) {R : TopCommRingCat.{u}} {a b : R ⟶ F.obj (op W)}
    (h : ∀ i, a ≫ F.map (k i).op = b ≫ F.map (k i).op) : a = b := by
  have hW : iSup V = W :=
    le_antisymm (iSup_le fun i => leOfHom (k i)) fun p hp => Opens.mem_iSup.2 (hcov p hp)
  subst hW
  obtain ⟨hlim⟩ := hF.isSheafOpensLeCover V
  refine hlim.hom_ext fun j => ?_
  obtain ⟨i, hi⟩ := j.unop.property
  have key : ∀ c : R ⟶ F.obj (op (iSup V)),
      c ≫ (F.mapCone (TopCat.Presheaf.SheafCondition.opensLeCoverCocone V).op).π.app j =
        (c ≫ F.map (k i).op) ≫ F.map (homOfLE hi).op := fun c => by
    rw [Category.assoc, ← F.map_comp]
    rfl
  exact (key a).trans ((congrArg (· ≫ F.map (homOfLE hi).op) (h i)).trans (key b).symm)

/-- Two morphisms of presheafed spaces of topological rings out of `X` agree as soon as they
agree after composition with a family of morphisms into `X` whose underlying maps are jointly
surjective and whose comparison maps are jointly monomorphic. -/
theorem presheafedSpace_hom_ext_of_cover {X Y : PresheafedSpace TopCommRingCat.{u}}
    {ι : Type u} {Z : ι → PresheafedSpace TopCommRingCat.{u}} (t : ∀ i, Z i ⟶ X)
    (hsurj : ∀ x : X, ∃ (i : ι) (y : Z i), (t i).base y = x)
    (hsep : ∀ (W : Opens X) (R : TopCommRingCat.{u}) (a b : R ⟶ X.presheaf.obj (op W)),
      (∀ i, a ≫ (t i).c.app (op W) = b ≫ (t i).c.app (op W)) → a = b)
    (f g : X ⟶ Y) (h : ∀ i, t i ≫ f = t i ≫ g) : f = g := by
  obtain ⟨fb, fc⟩ := f
  obtain ⟨gb, gc⟩ := g
  have hb : fb = gb := by
    refine TopCat.hom_ext (ContinuousMap.ext fun x => ?_)
    obtain ⟨i, y, hy⟩ := hsurj x
    subst hy
    have hbase := congrArg PresheafedSpace.Hom.base (h i)
    simpa using congrArg (fun m : (Z i).carrier ⟶ Y.carrier => m y) hbase
  subst hb
  refine PresheafedSpace.hext _ _ rfl
    (heq_of_eq (NatTrans.ext (funext fun V => hsep _ _ _ _ fun i => ?_)))
  have hheq : (t i ≫ (⟨fb, fc⟩ : X ⟶ Y)).c ≍ (t i ≫ (⟨fb, gc⟩ : X ⟶ Y)).c := by rw [h i]
  exact congrArg (fun η => η.app V) (eq_of_heq hheq)

/-- A composite of morphisms of presheafed spaces of topological rings whose stalk maps are
local homomorphisms has local stalk maps. -/
theorem isLocalHom_stalkMap_comp {X Y Z : PresheafedSpace TopCommRingCat.{u}}
    (α : X ⟶ Y) (β : Y ⟶ Z) (x : X) (hα : IsLocalHom (α.stalkMap x).1)
    (hβ : IsLocalHom (β.stalkMap (α.base x)).1) : IsLocalHom ((α ≫ β).stalkMap x).1 := by
  rw [PresheafedSpace.stalkMap.comp]
  exact @TopCommRingCat.isLocalHom_comp _ _ _ _ _ hβ hα

/-- The stalk maps of an isomorphism of presheafed spaces of topological rings are local
homomorphisms. -/
theorem isLocalHom_stalkMap_of_isIso {X Y : PresheafedSpace TopCommRingCat.{u}} (α : X ⟶ Y)
    [IsIso α] (x : X) : IsLocalHom (α.stalkMap x).1 :=
  TopCommRingCat.isLocalHom_val_of_isIso _

/-- The stalk maps of the inclusion of an open subspace are local homomorphisms, being
isomorphisms. -/
theorem isLocalHom_stalkMap_ofRestrict {X : PresheafedSpace TopCommRingCat.{u}}
    {U : TopCat.{u}} {f : U ⟶ X.carrier} (h : Topology.IsOpenEmbedding f) (x : U) :
    IsLocalHom ((X.ofRestrict h).stalkMap x).1 :=
  TopCommRingCat.isLocalHom_val_of_isIso _

/-- The comparison map of an isomorphism of presheafed spaces of topological rings is a
monomorphism over every open set, being an isomorphism. -/
theorem mono_c_app_of_iso {X Y : PresheafedSpace TopCommRingCat.{u}} (e : X ≅ Y)
    (V : (Opens Y.carrier)ᵒᵖ) : Mono (e.hom.c.app V) := by
  have : IsIso e.hom.c := inferInstance
  infer_instance

/-- If `F` carries `g₁` to a local homomorphism and `F g₂` followed by `s` is local, then
`F (g₁ ≫ g₂)` followed by `s` is local. This is the shape in which the stalk map of a morphism
of presheafed spaces whose comparison map is a composite is seen to be local. -/
theorem isLocalHom_map_comp_comp {C : Type*} [Category C] (F : C ⥤ TopCommRingCat.{u})
    {c₁ c₂ c₃ : C} (g₁ : c₁ ⟶ c₂) (g₂ : c₂ ⟶ c₃) {T : TopCommRingCat.{u}} (s : F.obj c₃ ⟶ T)
    (h₁ : IsLocalHom (F.map g₁).1) (h₂ : IsLocalHom (F.map g₂ ≫ s).1) :
    IsLocalHom (F.map (g₁ ≫ g₂) ≫ s).1 := by
  rw [F.map_comp, Category.assoc]
  exact @TopCommRingCat.isLocalHom_comp _ _ _ _ _ h₁ h₂

/-! ### `Spec (A/I)` as a point of the formal spectrum -/

section Spf

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {P : Ideal A → Prop} [IsWeakIdealSystem A P]

/-- The identification of `Spec (A/I)` with the space of open primes is injective, being the
corestriction of the closed immersion `Spec (A/I) → Spec A`. -/
theorem injective_spfOfQuotientOn (I : SpfIndex A P) :
    Function.Injective (spfOfQuotientOn A I) := fun _ _ h =>
  (PrimeSpectrum.isEmbedding_comap_of_surjective _ _
    Ideal.Quotient.mk_surjective).injective (congrArg Subtype.val h)

/-- The identification of `Spec (A/I)` with the space of open primes is injective, being the
corestriction of the closed immersion `Spec (A/I) → Spec A`.

The ideals-of-definition case of `injective_spfOfQuotientOn`. -/
theorem injective_spfOfQuotient (I : IdealsOfDefinition A) :
    Function.Injective (spfOfQuotient A I) :=
  injective_spfOfQuotientOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-- For an ideal of definition `I` the map `Spec (A/I) → Spf A` is an open embedding, being a
homeomorphism onto the space of open primes. -/
theorem isOpenEmbedding_spfOfQuotientOn (I : SpfIndex A P) :
    Topology.IsOpenEmbedding (spfOfQuotientOn A I) :=
  ⟨⟨isInducing_spfOfQuotientOn A I, injective_spfOfQuotientOn A I⟩, by
    rw [(surjective_spfOfQuotientOn A I).range_eq]; exact isOpen_univ⟩

/-- For an ideal of definition `I` the map `Spec (A/I) → Spf A` is an open embedding, being a
homeomorphism onto the space of open primes.

The ideals-of-definition case of `isOpenEmbedding_spfOfQuotientOn`. -/
theorem isOpenEmbedding_spfOfQuotient (I : IdealsOfDefinition A) :
    Topology.IsOpenEmbedding (spfOfQuotient A I) :=
  isOpenEmbedding_spfOfQuotientOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-- The identification of `Spec (A/I)` with `(Spf A, 𝒪_I)`, read with the pseudo-discrete
topologies on both sides. Pseudo-discretisation does not commute with pushforward in general,
the quasi-compact opens being taken on different spaces; it does along `Spec (A/I) → Spf A`,
which is a homeomorphism. -/
noncomputable def spfComponentPDOn (I : SpfIndex A P) :
    pseudoDiscreteSpace (Spec (spfQuotientOn A I)).toPresheafedSpace ⟶
      pseudoDiscreteSpace (spfComponentSpaceOn A I) where
  base := spfOfQuotientOn A I
  c :=
    { app := fun V => ⟨((spfComponentHomOn A I).c.app V).hom,
        continuous_pseudoDiscrete_embedding (spfComponentHomOn A I)
          (isOpenEmbedding_spfOfQuotientOn A I) V.unop⟩
      naturality := fun _ _ i => Subtype.ext
        (congrArg CommRingCat.Hom.hom ((spfComponentHomOn A I).c.naturality i)) }

/-- The identification of `Spec (A/I)` with `(Spf A, 𝒪_I)`, read with the pseudo-discrete
topologies on both sides. Pseudo-discretisation does not commute with pushforward in general,
the quasi-compact opens being taken on different spaces; it does along `Spec (A/I) → Spf A`,
which is a homeomorphism.

The ideals-of-definition case of `spfComponentPDOn`. -/
@[reducible] noncomputable def spfComponentPD (I : IdealsOfDefinition A) :
    pseudoDiscreteSpace (Spec (spfQuotient A I)).toPresheafedSpace ⟶
      pseudoDiscreteSpace (spfComponentSpace A I) :=
  spfComponentPDOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-- Forgetting the pseudo-discrete topologies, the comparison morphism is the identification of
`Spec (A/I)` with `(Spf A, 𝒪_I)`. -/
theorem forgetPseudoDiscreteHom_spfComponentPDOn (I : SpfIndex A P) :
    forgetPseudoDiscreteHom (spfComponentPDOn A I) = spfComponentHomOn A I := rfl

/-- Forgetting the pseudo-discrete topologies, the comparison morphism is the identification of
`Spec (A/I)` with `(Spf A, 𝒪_I)`.

The ideals-of-definition case of `forgetPseudoDiscreteHom_spfComponentPDOn`. -/
theorem forgetPseudoDiscreteHom_spfComponentPD (I : IdealsOfDefinition A) :
    forgetPseudoDiscreteHom (spfComponentPD A I) = spfComponentHom A I :=
  forgetPseudoDiscreteHom_spfComponentPDOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-- The stalk maps of the comparison morphism are local homomorphisms: pseudo-discretisation
does not change stalks, and the underlying morphism of presheafed spaces of rings is the
identification of `Spec (A/I)` with `(Spf A, 𝒪_I)`. -/
theorem isLocalHom_stalkMap_spfComponentPDOn (I : SpfIndex A P)
    (q : Spec (spfQuotientOn A I)) : IsLocalHom ((spfComponentPDOn A I).stalkMap q).1 :=
  (isLocalHom_stalkMap_iff (spfComponentPDOn A I) q).2 (by
    rw [forgetPseudoDiscreteHom_spfComponentPDOn]
    exact isLocalHom_stalkMap_spfComponentHomOn A I q)

/-- The stalk maps of the comparison morphism are local homomorphisms: pseudo-discretisation
does not change stalks, and the underlying morphism of presheafed spaces of rings is the
identification of `Spec (A/I)` with `(Spf A, 𝒪_I)`.

The ideals-of-definition case of `isLocalHom_stalkMap_spfComponentPDOn`. -/
theorem isLocalHom_stalkMap_spfComponentPD (I : IdealsOfDefinition A)
    (q : Spec (spfQuotient A I)) : IsLocalHom ((spfComponentPD A I).stalkMap q).1 :=
  isLocalHom_stalkMap_spfComponentPDOn (A := A) (P := IsIdealOfDefinition) (I := I) (q := q)

/-- The comparison morphism is the identity on sections, so it is a monomorphism. -/
theorem mono_spfComponentPDOn_c_app (I : SpfIndex A P)
    (V : (Opens (spfSpace A))ᵒᵖ) : Mono ((spfComponentPDOn A I).c.app V) :=
  ConcreteCategory.mono_of_injective _ fun _ _ h => h

/-- The comparison morphism is the identity on sections, so it is a monomorphism.

The ideals-of-definition case of `mono_spfComponentPDOn_c_app`. -/
theorem mono_spfComponentPD_c_app (I : IdealsOfDefinition A)
    (V : (Opens (spfSpace A))ᵒᵖ) : Mono ((spfComponentPD A I).c.app V) :=
  mono_spfComponentPDOn_c_app (A := A) (P := IsIdealOfDefinition) (I := I) (V := V)

/-- The morphism `Spec (A/I) → Spf A` of presheafed spaces of topological rings attached to an
ideal of definition `I`: on points it is the identification of `Spec (A/I)` with the space of
open primes, and on sections it is the projection of `𝒪_{Spf A} = lim 𝒪_λ` onto `𝒪_I`. -/
noncomputable def spfPointOn (I : SpfIndex A P) :
    pseudoDiscreteSpace (Spec (spfQuotientOn A I)).toPresheafedSpace ⟶ SpfOn A P where
  base := spfOfQuotientOn A I
  c := spfProjectionOn A I ≫ (spfComponentPDOn A I).c

/-- The morphism `Spec (A/I) → Spf A` of presheafed spaces of topological rings attached to an
ideal of definition `I`: on points it is the identification of `Spec (A/I)` with the space of
open primes, and on sections it is the projection of `𝒪_{Spf A} = lim 𝒪_λ` onto `𝒪_I`.

The ideals-of-definition case of `spfPointOn`. -/
@[reducible] noncomputable def spfPoint (I : IdealsOfDefinition A) :
    pseudoDiscreteSpace (Spec (spfQuotient A I)).toPresheafedSpace ⟶ Spf A :=
  spfPointOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-- The stalk maps of `Spec (A/I) → Spf A` are local homomorphisms: a germ of `𝒪_{Spf A}` is
invertible as soon as its image in one term of the inverse system is. -/
theorem isLocalHom_stalkMap_spfPointOn (I : SpfIndex A P)
    (q : Spec (spfQuotientOn A I)) : IsLocalHom ((spfPointOn A I).stalkMap q).1 :=
  isLocalHom_map_comp_comp
    (TopCat.Presheaf.stalkFunctor TopCommRingCat.{u} (spfOfQuotientOn A I q))
    (spfProjectionOn A I) ((spfComponentPDOn A I).c)
    ((pseudoDiscrete (Spec (spfQuotientOn A I)).presheaf).stalkPushforward TopCommRingCat.{u}
      (spfOfQuotientOn A I) q)
    (isLocalHom_spfProjectionOn_stalk A I _) (isLocalHom_stalkMap_spfComponentPDOn A I q)

/-- The stalk maps of `Spec (A/I) → Spf A` are local homomorphisms: a germ of `𝒪_{Spf A}` is
invertible as soon as its image in one term of the inverse system is.

The ideals-of-definition case of `isLocalHom_stalkMap_spfPointOn`. -/
theorem isLocalHom_stalkMap_spfPoint (I : IdealsOfDefinition A)
    (q : Spec (spfQuotient A I)) : IsLocalHom ((spfPoint A I).stalkMap q).1 :=
  isLocalHom_stalkMap_spfPointOn (A := A) (P := IsIdealOfDefinition) (I := I) (q := q)

/-- Two morphisms into the sections of `𝒪_{Spf A}` over an open set agree as soon as they agree
after composition with the comparison maps of all the morphisms `Spec (A/I) → Spf A`: the
sections of `𝒪_{Spf A} = lim 𝒪_λ` are a limit, and the comparison morphisms are
monomorphisms. -/
theorem spfPointOn_hom_ext {V : Opens (spfSpace A)} {R : TopCommRingCat.{u}}
    {a b : R ⟶ (spfPresheafOn A P).obj (op V)}
    (h : ∀ I : SpfIndex A P,
      a ≫ (spfPointOn A I).c.app (op V) = b ≫ (spfPointOn A I).c.app (op V)) : a = b := by
  refine spfPresheafOn_obj_hom_ext A fun I => ?_
  have : Mono ((spfComponentPDOn A I).c.app (op V)) := mono_spfComponentPDOn_c_app A I (op V)
  refine (cancel_mono ((spfComponentPDOn A I).c.app (op V))).1 ?_
  exact h I

/-- Two morphisms into the sections of `𝒪_{Spf A}` over an open set agree as soon as they agree
after composition with the comparison maps of all the morphisms `Spec (A/I) → Spf A`: the
sections of `𝒪_{Spf A} = lim 𝒪_λ` are a limit, and the comparison morphisms are
monomorphisms.

The ideals-of-definition case of `spfPointOn_hom_ext`. -/
theorem spfPoint_hom_ext {V : Opens (spfSpace A)} {R : TopCommRingCat.{u}}
    {a b : R ⟶ (spfPresheaf A).obj (op V)}
    (h : ∀ I : IdealsOfDefinition A,
      a ≫ (spfPoint A I).c.app (op V) = b ≫ (spfPoint A I).c.app (op V)) : a = b :=
  spfPointOn_hom_ext (A := A) (P := IsIdealOfDefinition) (V := V) (R := R) (a := a) (b := b)
    (h := h)

end Spf

/-! ### The morphisms out of the affine formal charts of a formal scheme -/

/-- The morphism `Spec (A/I) → 𝔛` of locally topologically ringed spaces attached to an affine
formal chart `𝔛|_𝔘 ≅ Spf A` of `𝔛` and an ideal of definition `I` of `A`: the composite of
`Spec (A/I) → Spf A`, the inverse of the chart, and the inclusion of the open subspace `𝔘`. -/
noncomputable def formalChartPointOn {X : LTRS.{u}} (U : Opens X) (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] {P : Ideal A → Prop} [IsWeakIdealSystem A P]
    (e : X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ SpfOn A P)
    (I : SpfIndex A P) : schemeToLTRSObj (Spec (spfQuotientOn A I)) ⟶ X where
  toHom := spfPointOn A I ≫ e.inv ≫
    X.toPresheafedSpace.ofRestrict (f := U.inclusion') U.isOpenEmbedding'
  isLocalHom q :=
    isLocalHom_stalkMap_comp _ _ q (isLocalHom_stalkMap_spfPointOn A I q)
      (isLocalHom_stalkMap_comp _ _ _
        (isLocalHom_stalkMap_of_isIso e.inv _)
        (isLocalHom_stalkMap_ofRestrict U.isOpenEmbedding' _))

/-- The morphism `Spec (A/I) → 𝔛` of locally topologically ringed spaces attached to an affine
formal chart `𝔛|_𝔘 ≅ Spf A` of `𝔛` and an ideal of definition `I` of `A`: the composite of
`Spec (A/I) → Spf A`, the inverse of the chart, and the inclusion of the open subspace `𝔘`.

The ideals-of-definition case of `formalChartPointOn`. -/
@[reducible] noncomputable def formalChartPoint {X : LTRS.{u}} (U : Opens X) (A : Type u)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (e : X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ Spf A)
    (I : IdealsOfDefinition A) : schemeToLTRSObj (Spec (spfQuotient A I)) ⟶ X :=
  formalChartPointOn (P := IsIdealOfDefinition) (X := X) (U := U) (A := A) (e := e) (I := I)

/-- The underlying morphism of presheafed spaces of `AlgebraicGeometry.formalChartPointOn`. -/
theorem formalChartPointOn_toHom {X : LTRS.{u}} (U : Opens X) (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] {P : Ideal A → Prop} [IsWeakIdealSystem A P]
    (e : X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ SpfOn A P)
    (I : SpfIndex A P) :
    (formalChartPointOn U A e I).toHom = spfPointOn A I ≫ e.inv ≫
      X.toPresheafedSpace.ofRestrict (f := U.inclusion') U.isOpenEmbedding' := rfl

/-- The underlying morphism of presheafed spaces of `AlgebraicGeometry.formalChartPoint`.

The ideals-of-definition case of `formalChartPointOn_toHom`. -/
theorem formalChartPoint_toHom {X : LTRS.{u}} (U : Opens X) (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (e : X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ Spf A)
    (I : IdealsOfDefinition A) :
    (formalChartPoint U A e I).toHom = spfPoint A I ≫ e.inv ≫
      X.toPresheafedSpace.ofRestrict (f := U.inclusion') U.isOpenEmbedding' :=
  formalChartPointOn_toHom (P := IsIdealOfDefinition) (X := X) (U := U) (A := A) (e := e) (I := I)

/-- Every point of the open subspace `𝔘` of an affine formal chart `𝔛|_𝔘 ≅ Spf A` is in the
image of `Spec (A/I) → 𝔛`: the chart is a homeomorphism, and `Spec (A/I) → Spf A` is onto the
space of open primes. -/
theorem exists_formalChartPointOn_base_eq {X : LTRS.{u}} (U : Opens X) (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] {P : Ideal A → Prop} [IsWeakIdealSystem A P]
    (e : X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ SpfOn A P)
    (I : SpfIndex A P) {x : X} (hx : x ∈ U) :
    ∃ y, (formalChartPointOn U A e I).toHom.base y = x := by
  obtain ⟨y, hy⟩ := surjective_spfOfQuotientOn A I (e.hom.base ⟨x, hx⟩)
  refine ⟨y, ?_⟩
  have key : e.inv.base (e.hom.base ⟨x, hx⟩) = ⟨x, hx⟩ :=
    ((PresheafedSpace.forget TopCommRingCat.{u}).mapIso e).hom_inv_id_apply ⟨x, hx⟩
  show (e.inv.base (spfOfQuotientOn A I y)).1 = x
  rw [hy, key]

/-- Every point of the open subspace `𝔘` of an affine formal chart `𝔛|_𝔘 ≅ Spf A` is in the
image of `Spec (A/I) → 𝔛`: the chart is a homeomorphism, and `Spec (A/I) → Spf A` is onto the
space of open primes.

The ideals-of-definition case of `exists_formalChartPointOn_base_eq`. -/
theorem exists_formalChartPoint_base_eq {X : LTRS.{u}} (U : Opens X) (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (e : X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ Spf A)
    (I : IdealsOfDefinition A) {x : X} (hx : x ∈ U) :
    ∃ y, (formalChartPoint U A e I).toHom.base y = x :=
  exists_formalChartPointOn_base_eq (P := IsIdealOfDefinition) (X := X) (U := U) (A := A) (e := e)
    (I := I) (x := x) (hx := hx)

/-! ### The functor of points -/

/-- The schemes of size below `κ`: the model of the source's category `Sch_α` of Stacks 000J
used in `StacksFrontier.AlgebraicGeometry.Size.Cutoff`. -/
def schemeCutoff (κ : Cardinal.{u}) : ObjectProperty Scheme.{u} := fun S => S.size < κ

/-- The *functor of points* of a formal scheme on the schemes of size below `κ`: it sends a
formal scheme `𝔛` to the presheaf `h_𝔛(S) = Mor_{Formal Schemes}(S, 𝔛)` on `Sch_κ`, a scheme
being viewed as a formal scheme through the functor of Stacks 0AI0. -/
noncomputable def formalSchemeFunctorOfPoints (κ : Cardinal.{u}) :
    FormalScheme.{u} ⥤ ((schemeCutoff κ).FullSubcategory)ᵒᵖ ⥤ Type u :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj
    (((schemeCutoff κ).ι ⋙ schemeToFormalScheme).op)

/-- The points of `𝔛` on a scheme `S` of `Sch_κ` are the morphisms of formal schemes from `S`
to `𝔛`. -/
@[simp]
theorem formalSchemeFunctorOfPoints_obj_obj (κ : Cardinal.{u}) (X : FormalScheme.{u})
    (S : (schemeCutoff κ).FullSubcategory) :
    ((formalSchemeFunctorOfPoints κ).obj X).obj (op S) =
      (schemeToFormalScheme.obj S.obj ⟶ X) := rfl

/-- A morphism of formal schemes acts on points by postcomposition. -/
@[simp]
theorem formalSchemeFunctorOfPoints_map_app (κ : Cardinal.{u}) {X Y : FormalScheme.{u}}
    (f : X ⟶ Y) (S : (schemeCutoff κ).FullSubcategory)
    (g : schemeToFormalScheme.obj S.obj ⟶ X) :
    ((formalSchemeFunctorOfPoints κ).map f).app (op S) g = g ≫ f := rfl

/-! ### Objects of `LTRS` charted by formal spectra -/

/-- The data a formal spectrum is taken from: a topological ring together with a weak ideal
system on it. -/
structure SpfSystem where
  /-- The topological ring. -/
  ring : TopCommRingCat.{u}
  /-- The family of ideals along which the formal spectrum is taken. -/
  family : Ideal ring.α → Prop
  /-- The family is a weak ideal system. -/
  isWeakIdealSystem : IsWeakIdealSystem ring.α family

/-- The family of ideals of a bundled system is a weak ideal system. -/
instance (S : SpfSystem.{u}) : IsWeakIdealSystem S.ring.α S.family := S.isWeakIdealSystem

/-- The index of the limit defining the formal spectrum of a bundled system. -/
abbrev SpfSystem.Index (S : SpfSystem.{u}) : Type u := SpfIndex S.ring.α S.family

/-- The formal spectrum of a bundled system. -/
noncomputable abbrev SpfSystem.spectrum (S : SpfSystem.{u}) :
    PresheafedSpace TopCommRingCat.{u} :=
  SpfOn S.ring.α S.family

/-- The chart data on which the source's argument for Stacks 87.2.1 rests: around every point of
`X` an open subspace `𝔘`, a topological ring with a weak ideal system on it having at least one
member and all of whose quotients `Spec (A/I)` are objects of `Sch_κ`, and an isomorphism of
`X|_𝔘` with the formal spectrum taken along that family.

Both an admissible chart `X|_𝔘 ≅ Spf A`, with the family the ideals of definition of `A`, and a
weakly admissible chart, with the family the weak ideals of definition, are of this shape; the
argument sees no more of the ring than this. -/
def IsSizeBoundedFormalSpectrumCharted (κ : Cardinal.{u}) (X : LTRS.{u}) : Prop :=
  ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (S : SpfSystem.{u}),
    Nonempty S.Index ∧
      (∀ I : S.Index, (Spec (spfQuotientOn S.ring.α I)).size < κ) ∧
      Nonempty (X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding'
        ≅ S.spectrum)

/-- Two morphisms out of an object of `LTRS` charted by formal spectra agree as soon as they
agree after every morphism into it from a scheme of `Sch_κ`.

The morphisms `Spec (A/I_λ) → X|_𝔘 → X` attached to the charts are jointly epimorphic. Their
underlying maps cover `X`, because each `Spec (A/I_λ)` is carried homeomorphically onto the
space of open primes of the ring of the chart; and the comparison maps they induce on the
sections of `𝒪_X` over an open set are jointly monomorphic, because `𝒪_X` is a sheaf and the
sections of the structure presheaf of a formal spectrum are a limit over the chart's family. The
size condition is exactly what makes those morphisms morphisms out of objects of `Sch_κ`. -/
theorem ltrs_hom_ext_of_isSizeBoundedFormalSpectrumCharted {κ : Cardinal.{u}} {X Y : LTRS.{u}}
    (hX : IsSizeBoundedFormalSpectrumCharted κ X) {f g : X ⟶ Y}
    (hcomp : ∀ S : Scheme.{u}, S.size < κ → ∀ φ : schemeToLTRSObj S ⟶ X, φ ≫ f = φ ≫ g) :
    f = g := by
  choose U hmem S hne hsize hiso using hX
  refine LocallyTopologicallyRingedSpace.Hom.ext' ?_
  refine presheafedSpace_hom_ext_of_cover
    (Z := fun i : Σ x : X, (S x).Index =>
      pseudoDiscreteSpace (Spec (spfQuotientOn (S i.1).ring.α i.2)).toPresheafedSpace)
    (fun i => (formalChartPointOn (U i.1) (S i.1).ring.α (hiso i.1).some i.2).toHom)
    ?_ ?_ _ _ ?_
  · -- The underlying maps of the family are jointly surjective.
    intro x
    obtain ⟨I⟩ := hne x
    obtain ⟨y, hy⟩ :=
      exists_formalChartPointOn_base_eq (U x) (S x).ring.α (hiso x).some I (hmem x)
    exact ⟨⟨x, I⟩, y, hy⟩
  · -- The family separates the sections of the structure sheaf.
    intro W R a b hab
    have hemb : ∀ x : X, Topology.IsOpenEmbedding ((U x).inclusion') :=
      fun x => (U x).isOpenEmbedding'
    refine presheaf_hom_ext_of_cover X.IsSheaf
      (fun x : X => (hemb x).functor.obj ((Opens.map (U x).inclusion').obj W))
      (fun x => (hemb x).isOpenMap.adjunction.counit.app W)
      (fun q hq => ⟨q, ⟨q, hmem q⟩, hq, rfl⟩) fun x => ?_
    have : Mono ((hiso x).some.inv.c.app
        (op ((Opens.map (U x).inclusion').obj W))) :=
      mono_c_app_of_iso (hiso x).some.symm (op ((Opens.map (U x).inclusion').obj W))
    refine (cancel_mono ((hiso x).some.inv.c.app
      (op ((Opens.map (U x).inclusion').obj W)))).1 ?_
    exact spfPointOn_hom_ext (S x).ring.α fun I => hab ⟨x, I⟩
  · -- The family consists of points of `X` defined over objects of `Sch_κ`.
    intro i
    exact congrArg (fun m : schemeToLTRSObj (Spec (spfQuotientOn (S i.1).ring.α i.2)) ⟶ Y =>
        m.toHom)
      (hcomp (Spec (spfQuotientOn (S i.1).ring.α i.2)) (hsize i.1 i.2)
        (formalChartPointOn (U i.1) (S i.1).ring.α (hiso i.1).some i.2))

/-- The size condition of Stacks 0AI1 on a formal scheme `𝔛`: every point has an affine formal
neighbourhood `𝔛|_𝔘 ≅ Spf A` such that every quotient `Spec (A/I)` by an ideal of definition of
`A` is an object of `Sch_κ`.

This is the source's analysis of "the size of `𝔛` is not too large": the schemes occurring in
the proof are isomorphic to objects of `Sch_α` as soon as the `Spec (A/I_λ)` are, and being an
object of `Sch_κ` is `size _ < κ`, which is isomorphism invariant. It is the strengthening of
`AlgebraicGeometry.IsFormalScheme` by that size clause. -/
def IsSizeBoundedFormalScheme (κ : Cardinal.{u}) (X : LTRS.{u}) : Prop :=
  ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (A : TopCommRingCat.{u}),
    ∃ hlinear : IsLinearTopology A.α A.α,
      letI := hlinear
      TopologicalRing.IsAdmissible A.α ∧
      (∀ I : IdealsOfDefinition A.α, (Spec (spfQuotientOn A.α I)).size < κ) ∧
      Nonempty (X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ Spf A.α)

/-- A formal scheme bounded by the cutoff is charted by formal spectra: the ideals of
definition of an admissible topological ring form a weak ideal system with at least one
member. -/
theorem IsSizeBoundedFormalScheme.isSizeBoundedFormalSpectrumCharted {κ : Cardinal.{u}}
    {X : LTRS.{u}} (hX : IsSizeBoundedFormalScheme κ X) :
    IsSizeBoundedFormalSpectrumCharted κ X := fun x => by
  obtain ⟨U, hxU, A, _, hadm, hsize, he⟩ := hX x
  exact ⟨U, hxU, ⟨A, IsIdealOfDefinition, inferInstance⟩,
    ⟨⟨hadm.1.choose, hadm.1.choose_spec⟩⟩, hsize, he⟩

/-- A formal scheme bounded by the cutoff is a formal scheme. -/
theorem IsSizeBoundedFormalScheme.isFormalScheme {κ : Cardinal.{u}} {X : LTRS.{u}}
    (hX : IsSizeBoundedFormalScheme κ X) : IsFormalScheme X := fun x => by
  obtain ⟨U, hxU, A, hlin, hadm, _, he⟩ := hX x
  exact ⟨U, hxU, A, hlin, hadm, he⟩

/-- **Stacks 0AI1**, injectivity. A morphism of formal schemes whose source satisfies the size
condition is determined by the natural transformation it induces on functors of points on the
schemes of size below `κ`.

The morphisms `Spec (A/I_λ) → Spf A ≅ 𝔛|_𝔘 → 𝔛` attached to the affine formal charts of `𝔛` are
jointly epimorphic, and the size condition is exactly what makes them morphisms out of objects
of `Sch_κ`, hence points of `𝔛` seen by the functor of points. Their underlying maps cover `𝔛`
because each `Spec (A/I_λ) → Spf A` is a homeomorphism; and they separate the sections of
`𝒪_𝔛`, because `𝒪_𝔛` is a sheaf and the sections of `𝒪_{Spf A} = lim 𝒪_λ` are a limit. -/
@[stacks 0AI1 "injectivity: a morphism of formal schemes is determined by the induced \
transformation of functors of points"]
theorem injective_formalSchemeFunctorOfPoints_map {κ : Cardinal.{u}} {X Y : FormalScheme.{u}}
    (hX : IsSizeBoundedFormalScheme κ X.obj) :
    Function.Injective fun f : X ⟶ Y => (formalSchemeFunctorOfPoints κ).map f := by
  intro f g hfg
  refine InducedCategory.hom_ext
    (ltrs_hom_ext_of_isSizeBoundedFormalSpectrumCharted
      hX.isSizeBoundedFormalSpectrumCharted fun T hT φ => ?_)
  exact congrArg (fun m : schemeToFormalScheme.obj T ⟶ Y => m.hom)
    (congrFun (congrArg (fun η => η.app (op ⟨T, hT⟩)) hfg) (ObjectProperty.homMk φ))

end AlgebraicGeometry
