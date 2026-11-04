module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.LocalizedGeneralCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Sheaves

/-!
# Local constancy survives inverse image between small étale sites

Let `g : T ⟶ S` be a morphism of a big étale site. A sheaf on the small étale site of `S` which
is locally constant — with values satisfying any prescribed property, so that the statement
covers finite local constancy and local constancy of finite type at once — has locally constant
inverse image on the small étale site of `T`. No hypothesis on `g` is needed: in particular it
need not be étale, which is the case the constructibility statements of Tag 095E require, since
there `g` is an immersion.

The argument has three steps, of which only the middle one is specific to small étale sites.

* A sheaf trivialized on a covering of the final object is trivialized over every object
  (`Stacks.ConstantSheaf.Localization.exists_trivializing_cover`), so it suffices to produce one
  covering of the final object of the small étale site of `T`. Base change along `g` preserves
  coverings and the final object, so the base change of a trivializing covering of `S` is one.
* Over a member `V` of that covering the trivialization is transported by the *slice
  equivalence*: by `AlgebraicGeometry.nonempty_constantSheafIso_over_iff` the restriction of a
  sheaf to the localization at `V` is constant exactly when its inverse image along the structure
  morphism `v : V ⟶ S` is constant on the small étale site of the scheme `V`. In that second
  form the transport is immediate, because `V ×_S T ⟶ V` and `V ×_S T ⟶ T ⟶ S` fit in the base
  change square, so the composition law
  `AlgebraicGeometry.smallEtaleSheafPullbackCompIso` identifies the two ways around it and
  `AlgebraicGeometry.smallEtaleSheafPullbackConstantSheafIso` says the remaining inverse image of
  a constant sheaf is constant with the same value.
* Transporting back by the slice equivalence over the base-changed member gives the
  trivialization in the localized form the definitions use.

What makes the middle step necessary is that the condition on a member of the covering is stated
on a *localized* site, where the only available comparison for a morphism of the ambient site is
restriction along `CategoryTheory.Over.post`; the inverse image along the latter is not
determined by the hypotheses of the constructibility statements, which provide inverse image only
for base change between objects of the big étale site. The slice equivalence replaces the
localized site by the small étale site of a scheme, where base change *is* provided.

## Main results

* `AlgebraicGeometry.exists_trivializing_cover_smallEtaleSheafPullback` — the transport of a
  trivializing covering, for an arbitrary property of the constant values.
* `AlgebraicGeometry.nonempty_constantSheafIso_baseChange_over` — the transport of a single
  trivialization along the base change square.
* `AlgebraicGeometry.isFiniteLocallyConstant_smallEtaleSheafPullback'` and
  `AlgebraicGeometry.isFiniteTypeLocallyConstant_smallEtaleSheafPullback` — finite local
  constancy, respectively local constancy of finite type, survives inverse image.  The first is
  the primed form of `AlgebraicGeometry.isFiniteLocallyConstant_smallEtaleSheafPullback`, which
  proves the same conclusion but asks in addition that inverse image along
  `CategoryTheory.Over.post` of a base change have a right adjoint; that hypothesis is not
  needed here.

## Implementation notes

The coefficient hypotheses are exactly those of Tags 03RW and 095E: inverse image exists for
base change between objects of the big étale site, and the localized sites admit weak
sheafification. Weak sheafification on the small étale site of a *scheme* appearing in a
covering is deduced from the latter by `AlgebraicGeometry.hasWeakSheafify_smallEtale_of_over`,
not assumed.

No `@[stacks]` attribute appears in this file. Tag 093R is local constancy under the inverse
image of a morphism of topoi and Tag 095A its specialization to étale sites; what is proved here
is the case of the morphism attached to a morphism of schemes, which is an input to those tags
rather than either of them in full.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 095A](https://stacks.math.columbia.edu/tag/095A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₀ t w u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (A : Type w) [Category.{t} A]
  [hra : ∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (X : B.Scheme) (V : SmallEtale B X.obj X.property),
    HasWeakSheafify ((SmallEtale.topology B X.obj X.property).over V) A]

/-- **A trivialization transports along the base change square.** If the restriction of `H` to
the localization at `V` is the constant sheaf on `E`, then the restriction of the inverse image
of `H` along `g` to the localization at the base change of `V` is the constant sheaf on the
*same* `E`.

Read through the slice equivalence the statement becomes one about the small étale sites of the
schemes `V` and `V ×_S T`, where it is the composition law for inverse image applied to the two
sides of the base change square, followed by the preservation of constant sheaves. -/
public theorem nonempty_constantSheafIso_baseChange_over {S T : B.Scheme} (g : T ⟶ S)
    (V : SmallEtale B S.obj S.property)
    (H : Sheaf (SmallEtale.topology B S.obj S.property) A) (E : A)
    (h : Nonempty ((constantSheaf ((SmallEtale.topology B S.obj S.property).over V) A).obj E ≅
      ((SmallEtale.topology B S.obj S.property).overPullback A V).obj H)) :
    Nonempty ((constantSheaf ((SmallEtale.topology B T.obj T.property).over
        ((smallEtaleBaseChange B g).obj V)) A).obj E ≅
      ((SmallEtale.topology B T.obj T.property).overPullback A
        ((smallEtaleBaseChange B g).obj V)).obj
        (((smallEtaleBaseChange B g).sheafPullback A
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).obj H)) := by
  have hwV : HasWeakSheafify (SmallEtale.topology B V.obj.left.1 V.obj.left.property) A :=
    hasWeakSheafify_smallEtale_of_over B S.obj S.property V A
  have hwW : HasWeakSheafify (SmallEtale.topology B
      ((smallEtaleBaseChange B g).obj V).obj.left.1
      ((smallEtaleBaseChange B g).obj V).obj.left.property) A :=
    hasWeakSheafify_smallEtale_of_over B T.obj T.property ((smallEtaleBaseChange B g).obj V) A
  have := hra V.obj.left ((smallEtaleBaseChange B g).obj V).obj.left
    (pullback.fst V.obj.hom g)
  have : Functor.IsContinuous (smallEtaleBaseChange B
      (T := ((smallEtaleBaseChange B g).obj V).obj.left) (pullback.fst V.obj.hom g))
      (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
      (SmallEtale.topology B ((smallEtaleBaseChange B g).obj V).obj.left.1
        ((smallEtaleBaseChange B g).obj V).obj.left.property) :=
    smallEtaleBaseChange_isContinuous B _
  obtain ⟨c⟩ := (nonempty_constantSheafIso_over_iff B S.obj S.property V A H E).mp h
  refine (nonempty_constantSheafIso_over_iff B T.obj T.property
    ((smallEtaleBaseChange B g).obj V) A _ E).mpr ⟨?_⟩
  have hsq : pullback.fst V.obj.hom g ≫ (V.obj.hom : V.obj.left ⟶ S) =
      (((smallEtaleBaseChange B g).obj V).obj.hom :
        ((smallEtaleBaseChange B g).obj V).obj.left ⟶ T) ≫ g :=
    pullback.condition
  refine Iso.symm ?_
  refine ((smallEtaleSheafPullbackCompIso B ((smallEtaleBaseChange B g).obj V).obj.left T S
      ((smallEtaleBaseChange B g).obj V).obj.hom g A).app H) ≪≫ ?_
  refine eqToIso (congrArg (fun m => ((smallEtaleBaseChange B m).sheafPullback A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B ((smallEtaleBaseChange B g).obj V).obj.left.1
        ((smallEtaleBaseChange B g).obj V).obj.left.property)).obj H) hsq.symm) ≪≫ ?_
  refine ((smallEtaleSheafPullbackCompIso B ((smallEtaleBaseChange B g).obj V).obj.left
      V.obj.left S (pullback.fst V.obj.hom g) V.obj.hom A).app H).symm ≪≫ ?_
  exact ((smallEtaleBaseChange B (T := ((smallEtaleBaseChange B g).obj V).obj.left)
        (pullback.fst V.obj.hom g)).sheafPullback A
      (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
      (SmallEtale.topology B ((smallEtaleBaseChange B g).obj V).obj.left.1
        ((smallEtaleBaseChange B g).obj V).obj.left.property)).mapIso c.symm ≪≫
    (smallEtaleSheafPullbackConstantSheafIso B
      (T := ((smallEtaleBaseChange B g).obj V).obj.left) (pullback.fst V.obj.hom g) A).app E

/-- **A trivializing covering transports along inverse image.** If `H` is trivialized, with
values satisfying `Q`, on a covering of every object of the small étale site of `S`, then its
inverse image along `g` is trivialized with values satisfying the same `Q` on a covering of every
object of the small étale site of `T`.

Only the covering of the *final* object of `S` is used: base change carries it to a covering of
the final object of `T`, each member to the base change of a member, and
`Stacks.ConstantSheaf.Localization.exists_trivializing_cover` spreads the result to every
object. -/
public theorem exists_trivializing_cover_smallEtaleSheafPullback {S T : B.Scheme} (g : T ⟶ S)
    (H : Sheaf (SmallEtale.topology B S.obj S.property) A) (Q : A → Prop)
    (hH : ∀ U : SmallEtale B S.obj S.property,
      ∃ (I : Type (u + 1)) (V : I → SmallEtale B S.obj S.property) (f : ∀ i, V i ⟶ U),
        Sieve.ofArrows V f ∈ SmallEtale.topology B S.obj S.property U ∧ ∀ i,
          ∃ E : A, Q E ∧ Nonempty
            ((constantSheaf ((SmallEtale.topology B S.obj S.property).over (V i)) A).obj E ≅
              ((SmallEtale.topology B S.obj S.property).overPullback A (V i)).obj H))
    (U : SmallEtale B T.obj T.property) :
    ∃ (I : Type (u + 1)) (W : I → SmallEtale B T.obj T.property) (f : ∀ i, W i ⟶ U),
      Sieve.ofArrows W f ∈ SmallEtale.topology B T.obj T.property U ∧ ∀ i,
        ∃ E : A, Q E ∧ Nonempty
          ((constantSheaf ((SmallEtale.topology B T.obj T.property).over (W i)) A).obj E ≅
            ((SmallEtale.topology B T.obj T.property).overPullback A (W i)).obj
              (((smallEtaleBaseChange B g).sheafPullback A
                (SmallEtale.topology B S.obj S.property)
                (SmallEtale.topology B T.obj T.property)).obj H)) := by
  obtain ⟨I, V, f, hf, hc⟩ := hH (SmallEtale.final B S.obj S.property)
  have hT := SmallEtale.finalIsTerminal B T.obj T.property
  refine Stacks.ConstantSheaf.Localization.exists_trivializing_cover
    (SmallEtale.topology B T.obj T.property) A hT _ Q
    (X := fun i => (smallEtaleBaseChange B g).obj (V i))
    (f := fun i => hT.from ((smallEtaleBaseChange B g).obj (V i))) ?_ ?_ U
  · have hcp : CoverPreserving (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property) (smallEtaleBaseChange B g) :=
      CoverPreserving.of_isContinuous _ _ _
    have hpush := hcp.cover_preserve hf
    rw [Sieve.functorPushforward_ofArrows] at hpush
    refine (SmallEtale.topology B T.obj T.property).superset_covering ?_
      ((SmallEtale.topology B T.obj T.property).pullback_stable
        (smallEtaleFinalBaseChangeIso B g).inv hpush)
    intro Z k hk
    have hk' : (Sieve.ofArrows (fun i => (smallEtaleBaseChange B g).obj (V i))
        (fun i => (smallEtaleBaseChange B g).map (f i))).arrows
          (k ≫ (smallEtaleFinalBaseChangeIso B g).inv) := hk
    obtain ⟨i, c, hc'⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hk'
    refine (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨i, c, ?_⟩
    calc k = (k ≫ (smallEtaleFinalBaseChangeIso B g).inv) ≫
          (smallEtaleFinalBaseChangeIso B g).hom := by
          rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = c ≫ ((smallEtaleBaseChange B g).map (f i) ≫
          (smallEtaleFinalBaseChangeIso B g).hom) := by rw [hc', Category.assoc]
      _ = c ≫ hT.from ((smallEtaleBaseChange B g).obj (V i)) := by
          rw [hT.hom_ext ((smallEtaleBaseChange B g).map (f i) ≫
            (smallEtaleFinalBaseChangeIso B g).hom)
            (hT.from ((smallEtaleBaseChange B g).obj (V i)))]
  · intro i
    obtain ⟨E, hE, hiso⟩ := hc i
    exact ⟨E, hE, nonempty_constantSheafIso_baseChange_over B A g (V i) H E hiso⟩

/-- **Finite local constancy survives inverse image along any morphism of a big étale site.**

This is the primed form of `AlgebraicGeometry.isFiniteLocallyConstant_smallEtaleSheafPullback`:
the conclusion is the same, but that one additionally assumes a right adjoint for the inverse
image along `CategoryTheory.Over.post` of a base change, which the argument here does not use. -/
public theorem isFiniteLocallyConstant_smallEtaleSheafPullback'
    {FA : A → A → Type*} {CA : A → Type w₀}
    [∀ E E', FunLike (FA E E') (CA E) (CA E')] [ConcreteCategory.{w₀} A FA]
    {S T : B.Scheme} (g : T ⟶ S)
    (H : Sheaf (SmallEtale.topology B S.obj S.property) A)
    [hH : Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FA) (CD := CA)
      (SmallEtale.topology B S.obj S.property) H] :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FA) (CD := CA)
      (SmallEtale.topology B T.obj T.property)
      (((smallEtaleBaseChange B g).sheafPullback A
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).obj H) where
  exists_finite_cover U :=
    exists_trivializing_cover_smallEtaleSheafPullback B A g H (fun E => Finite (CA E))
      hH.exists_finite_cover U

/-- **Local constancy of finite type survives inverse image along any morphism of a big étale
site.** -/
public theorem isFiniteTypeLocallyConstant_smallEtaleSheafPullback (R : Type*) [Ring R]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} R)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (X : B.Scheme) (V : SmallEtale B X.obj X.property),
      HasWeakSheafify ((SmallEtale.topology B X.obj X.property).over V) (ModuleCat.{w} R)]
    {S T : B.Scheme} (g : T ⟶ S)
    (H : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{w} R))
    (hH : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
      (SmallEtale.topology B S.obj S.property) H) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
      (SmallEtale.topology B T.obj T.property)
      (((smallEtaleBaseChange B g).sheafPullback (ModuleCat.{w} R)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).obj H) := fun U =>
  exists_trivializing_cover_smallEtaleSheafPullback B (ModuleCat.{w} R) g H
    (fun E => ModuleCat.isFG R E) hH U

end AlgebraicGeometry

end
