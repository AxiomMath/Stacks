module

public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.MorphismOfSites
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumFormula

/-!
# Exactness of lower shriek on a simplicial site

Stacks 09WG proves that lower shriek on abelian sheaves is exact by the single sentence
*"The exactness properties of `g_{n!}` follow from the formulas given for these functors"*:
by the direct-sum
formula, the restriction of `g_{n!}𝒢` to simplicial degree `m` is `⨁_{φ : [n] ⟶ [m]} f_φ^{-1}𝒢`,
and `[n] ⟶ [m]` is a finite set, so exactness of `g_{n!}` is exactness of the finitely many
`f_φ^{-1}`.

This file carries out that reduction. Right exactness is formal: `g_{n!}` is a left adjoint. Left
exactness is the reduction itself, in three steps.

* Every object of the total category lies in one of the components
  (`exists_componentFunctor_obj`), so limits of abelian sheaves on the total site are detected by
  the restrictions to the components
  (`preservesLimitsOfShape_of_componentRestriction`).
* The direct-sum formula, read in an abelian category over the finite index `[n] ⟶ [m]`, is also
  a *product* formula (`componentLowerShriekRestrictionIsoProduct`,
  `isLimitFanComponentLowerShriekRestriction`).
* A functor exhibited as a product of functors each of which preserves limits of a given shape
  preserves limits of that shape (`CategoryTheory.Limits.preservesLimitsOfShape_of_isLimitFan`).

What the reduction needs as input is left exactness of the transition inverse images
`f_φ^{-1}`, and the two cases of the situation supply it differently. In **case (B)** the
transitions are cocontinuous and `f_φ^{-1}` is `Functor.sheafPullbackCocontinuous`, which is
exact by Stacks 00XL — formalized as
`CategoryTheory.Functor.preservesFiniteLimits_sheafPullbackCocontinuous`. In **case (A)** the
transitions are morphisms of sites and `f_φ^{-1}` is `Functor.sheafPullback`; its exactness on
**abelian** sheaves is the Ab-coefficient form of Stacks 00X1/03CO, which
`Stacks.Sites.AbelianPullback.preservesFiniteLimits_sheafPullback_of_isMorphismOfSites`
supplies at the site's own coefficient universe, by the route of Stacks 04JC. So both cases are
discharged, and the exactness clause holds for an arbitrary `SimplicialSiteSituation`.

## Main results

* `CategoryTheory.Limits.isLimitFanMapOfPreserves`: a functor preserving products of a shape takes
  a limit fan to a limit fan. Dual of
  `CategoryTheory.Limits.isColimitCofanMapOfPreserves`.
* `CategoryTheory.Limits.preservesLimitsOfShape_of_isLimitFan`: a functor between functor
  categories exhibited as a product of functors each preserving limits of shape `K` preserves
  limits of shape `K`.
* `CategoryTheory.SimplicialSiteSituation.exists_componentFunctor_obj` and
  `.preservesLimitsOfShape_of_componentRestriction`: limits of sheaves on the total site are
  detected componentwise, at any category of coefficients.
* `CategoryTheory.SimplicialSiteSituation.componentLowerShriekRestrictionIsoProduct` and
  `.isLimitFanComponentLowerShriekRestriction`: the product form of the direct-sum formula.
* `CategoryTheory.SimplicialSiteSituation.preservesFiniteColimits_componentLowerShriekAb`:
  **Stacks 09WG (7)**, right exactness, unconditionally.
* `CategoryTheory.SimplicialSiteSituation.preservesFiniteLimits_componentLowerShriekAb`: left
  exactness, from left exactness of the transition inverse images.
* `CategoryTheory.SimplicialSite.preservesFiniteLimits_transitionInverseImageAb` and
  `CategoryTheory.CocontinuousSimplicialSite.preservesFiniteLimits_transitionInverseImageAb`:
  left exactness of the transition inverse images in the two cases, and
  `CategoryTheory.SimplicialSiteSituation.preservesFiniteLimits_transitionInverseImageAb` in
  both at once.
* `CategoryTheory.SimplicialSiteSituation.componentLowerShriek_exactFunctor`: **Stacks 09WG
  (7)**, for an arbitrary simplicial-site situation, and
  `CategoryTheory.CocontinuousSimplicialSite.componentLowerShriek_exactFunctor`, its case-(B)
  instance, retained under that name because two modules consume it.

## Implementation notes

The coefficients are abelian groups in the universe of the site. Stacks 09WG (7) says
nothing about universes, and the construction is not available at a coefficient universe
independent of the site universe: neither sheafification on the total site nor the pointwise
right Kan extensions along the component inclusions, which the product formula is stated
through, exists there, and in case (A) the morphism of topoi itself does not — the
`isMorphismOfSites` field of `CategoryTheory.SimplicialSite` fixes the sheaf-value universe of
`CategoryTheory.Functor.IsMorphismOfSites` to the site universe, so Stacks 04JC has no input at
any other.

`preservesLimitsOfShape_of_isLimitFan` is proved from the pointwise product structure, obtained
from the functor-category one by `isLimitFanMapOfPreserves` at the evaluation functors. Its
comparison lift into the `i`-th factor is extracted into the named `factorLift` with the
specification `factorLift_fac`/`factorLift_uniq`, rather than written inline: inline, the lift's
recorded type is `((Cone.postcompose _).obj s).pt ⟶ ((f i).mapCone c).pt`, which is only
definitionally `s.pt ⟶ (f i).obj c.pt`, and the resulting `Fan.mk` is then not type-correct at
`implicit` transparency, after which `rw` fails with a message about the pattern rather than
about the types.

For the same reason the naturality squares are introduced by `have` with their types written
out: `(p i).naturality` produces `(p i).app (((Functor.const K).obj c.pt).obj k)` where the goal
has `(p i).app c.pt`, and `rw` does not match across that.

In case (A) the transition inverse image is the *constructed* pullback
`Functor.sheafPullbackConstruction.sheafPullback`, while Stacks 04JC is available for the
abstract left adjoint `Functor.sheafPullback`; the two are compared by
`Functor.sheafPullbackConstruction.sheafPullbackIso`. The transport along that isomorphism
supplies its `PreservesFiniteLimits` argument explicitly rather than by instance synthesis: the
abstract `Functor.sheafPullback` carries an `IsRightAdjoint` instance argument, and the one
synthesised at the call site is not the one appearing in the hypothesis obtained from 04JC, so
synthesis reports the instance absent while it is present in the context.

## References

* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Pseudofunctor Opposite

namespace CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂ v₃ u₃

variable {I : Type w} {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- A functor preserving products of shape `I` takes a limit fan to a limit fan. This is the dual
of `CategoryTheory.Limits.isColimitCofanMapOfPreserves`. -/
noncomputable def isLimitFanMapOfPreserves (G : A ⥤ B)
    [PreservesLimitsOfShape (Discrete I) G] {f : I → A} {P : A} (p : ∀ i, P ⟶ f i)
    (h : IsLimit (Fan.mk P p)) :
    IsLimit (Fan.mk (G.obj P) fun i => G.map (p i)) := by
  refine (IsLimit.equivOfNatIsoOfIso
    ((Discrete.natIso fun _ => Iso.refl _ :
        Discrete.functor f ⋙ G ≅ Discrete.functor fun i => G.obj (f i)))
    (G.mapCone (Fan.mk P p)) (Fan.mk (G.obj P) fun i => G.map (p i))
    (Cone.ext (Iso.refl _) ?_)) (isLimitOfPreserves G h)
  intro j
  obtain ⟨j⟩ := j
  simp

variable {K : Type u₃} [Category.{v₃} K]

section

variable {f : I → (A ⥤ B)} {P : A ⥤ B} (p : ∀ i, P ⟶ f i) {D : K ⥤ A} {c : Cone D}
  (hc : IsLimit c) [∀ i, PreservesLimitsOfShape K (f i)]

/-- The comparison lift of a cone into the `i`-th factor, for the proof of
`preservesLimitsOfShape_of_isLimitFan`. -/
private noncomputable def factorLift (s : Cone (D ⋙ P)) (i : I) : s.pt ⟶ (f i).obj c.pt :=
  (isLimitOfPreserves (f i) hc).lift ((Cone.postcompose (whiskerLeft D (p i))).obj s)

private lemma factorLift_fac (s : Cone (D ⋙ P)) (i : I) (k : K) :
    factorLift p hc s i ≫ (f i).map (c.π.app k) = s.π.app k ≫ (p i).app (D.obj k) :=
  (isLimitOfPreserves (f i) hc).fac _ k

private lemma factorLift_uniq (s : Cone (D ⋙ P)) (i : I) (x : s.pt ⟶ (f i).obj c.pt)
    (hx : ∀ k, x ≫ (f i).map (c.π.app k) = s.π.app k ≫ (p i).app (D.obj k)) :
    x = factorLift p hc s i :=
  (isLimitOfPreserves (f i) hc).uniq
    ((Cone.postcompose (whiskerLeft D (p i))).obj s) x hx

end

/-- A functor between functor categories exhibited as a product of functors each of which
preserves limits of shape `K` preserves limits of shape `K`. -/
lemma preservesLimitsOfShape_of_isLimitFan {f : I → (A ⥤ B)} {P : A ⥤ B} (p : ∀ i, P ⟶ f i)
    (hP : IsLimit (Fan.mk P p)) [∀ i, PreservesLimitsOfShape K (f i)]
    [HasLimitsOfShape (Discrete I) B] :
    PreservesLimitsOfShape K P := by
  have hpt : ∀ X : A, IsLimit (Fan.mk (P.obj X) fun i => (p i).app X) := fun X =>
    isLimitFanMapOfPreserves ((evaluation A B).obj X) p hP
  constructor
  intro D
  constructor
  intro c hc
  let l (s : Cone (D ⋙ P)) := (hpt c.pt).lift
    (Fan.mk (f := fun i => (f i).obj c.pt) s.pt (factorLift p hc s))
  have key (s : Cone (D ⋙ P)) (i : I) : l s ≫ (p i).app c.pt = factorLift p hc s i :=
    (hpt c.pt).fac _ ⟨i⟩
  refine ⟨l, fun s k => ?_, fun s x hx => ?_⟩
  · refine (hpt (D.obj k)).hom_ext fun ⟨i⟩ => ?_
    change (l s ≫ P.map (c.π.app k)) ≫ (p i).app (D.obj k) =
      s.π.app k ≫ (p i).app (D.obj k)
    rw [Category.assoc, (p i).naturality, ← Category.assoc, key, factorLift_fac]
  · refine (hpt c.pt).hom_ext fun ⟨i⟩ => ?_
    change x ≫ (p i).app c.pt = l s ≫ (p i).app c.pt
    rw [key]
    refine factorLift_uniq p hc s i _ fun k => ?_
    rw [Category.assoc, ← (p i).naturality, ← Category.assoc]
    exact hx k =≫ _

end CategoryTheory.Limits

namespace CategoryTheory.SimplicialSiteSituation

universe u v₄ u₄ v₃ u₃ v₅ u₅

/-- Every object of the total category lies in one of the components: it is the image, under the
inclusion of the component of its own simplicial degree, of its own fibre component. -/
lemma exists_componentFunctor_obj (S : SimplicialSiteSituation.{u}) (W : S.totalCategory) :
    ∃ (m : SimplexCategory) (V : S.component m), (componentFunctor S m).obj V = W := by
  obtain ⟨c⟩ := S
  cases c with
  | inl C => exact ⟨W.base.unop, W.fiber, rfl⟩
  | inr C => exact ⟨W.base.unop, W.fiber, rfl⟩

/-- A functor into sheaves on the total site preserves limits of a given shape as soon as its
composite with restriction to each simplicial degree does.

Limits of sheaves are created by the inclusion into presheaves and limits of presheaves are
pointwise, so this is `exists_componentFunctor_obj`: every object at which the presheaves have to
be tested lies in some component. -/
lemma preservesLimitsOfShape_of_componentRestriction (S : SimplicialSiteSituation.{u})
    {Bc : Type u₄} [Category.{v₄} Bc] (K : Type u₃) [Category.{v₃} K]
    {A : Type u₅} [Category.{v₅} A] [HasLimitsOfShape K A]
    (H : Bc ⥤ Sheaf S.totalTopology A)
    (h : ∀ m : SimplexCategory, PreservesLimitsOfShape K
      (H ⋙ (componentFunctor S m).sheafPushforwardContinuous A
        (S.componentTopology m) S.totalTopology)) :
    PreservesLimitsOfShape K H := by
  have hpsh : PreservesLimitsOfShape K (H ⋙ sheafToPresheaf S.totalTopology A) := by
    refine preservesLimitsOfShape_of_evaluation _ K fun W => ?_
    obtain ⟨W⟩ := W
    obtain ⟨m, V, rfl⟩ := exists_componentFunctor_obj S W
    have := h m
    have h3 := comp_preservesLimitsOfShape (J := K)
      (sheafToPresheaf (S.componentTopology m) A)
      ((evaluation (S.component m)ᵒᵖ A).obj (op V))
    exact comp_preservesLimitsOfShape
      (H ⋙ (componentFunctor S m).sheafPushforwardContinuous A
        (S.componentTopology m) S.totalTopology)
      (sheafToPresheaf (S.componentTopology m) A ⋙
        (evaluation (S.component m)ᵒᵖ A).obj (op V))
  exact preservesLimitsOfShape_of_reflects_of_preserves H (sheafToPresheaf _ _)

variable (S : SimplicialSiteSituation.{u}) (n m : SimplexCategory)

/-- **Stacks 09WG (6)** read as a product formula. The simplex maps `[n] ⟶ [m]` form a finite
set and abelian sheaves form an abelian category, so the direct sum of the transition inverse
images is also their product. -/
noncomputable def componentLowerShriekRestrictionIsoProduct :
    sheafPullbackConstruction.sheafPullback (componentFunctor S n) Ab.{u}
        (S.componentTopology n) S.totalTopology ⋙
      (componentFunctor S m).sheafPushforwardContinuous Ab.{u}
        (S.componentTopology m) S.totalTopology ≅
      ∏ᶜ fun φ : n ⟶ m => transitionInverseImageAb S φ :=
  haveI := HasFiniteBiproducts.of_hasFiniteProducts
    (C := Sheaf (S.componentTopology n) Ab.{u} ⥤ Sheaf (S.componentTopology m) Ab.{u})
  componentLowerShriekRestrictionIsoCoproduct S n m ≪≫
    (biproduct.isoCoproduct _).symm ≪≫ biproduct.isoProduct _

/-- The product formula of `componentLowerShriekRestrictionIsoProduct` as a limit fan, which is
the form `CategoryTheory.Limits.preservesLimitsOfShape_of_isLimitFan` consumes. -/
noncomputable def isLimitFanComponentLowerShriekRestriction :
    IsLimit (Fan.mk (f := fun φ : n ⟶ m => transitionInverseImageAb S φ)
      (sheafPullbackConstruction.sheafPullback (componentFunctor S n) Ab.{u}
          (S.componentTopology n) S.totalTopology ⋙
        (componentFunctor S m).sheafPushforwardContinuous Ab.{u}
          (S.componentTopology m) S.totalTopology)
      fun φ => (componentLowerShriekRestrictionIsoProduct S n m).hom ≫ Pi.π _ φ) := by
  refine IsLimit.ofIsoLimit (productIsProduct _)
    (Cone.ext (componentLowerShriekRestrictionIsoProduct S n m).symm ?_)
  intro j
  obtain ⟨φ⟩ := j
  simp

/-- **Stacks 09WG (7)**, right exactness: lower shriek on abelian sheaves is a left adjoint, so
it preserves all colimits. -/
instance preservesFiniteColimits_componentLowerShriekAb :
    PreservesFiniteColimits (sheafPullbackConstruction.sheafPullback (componentFunctor S n)
      Ab.{u} (S.componentTopology n) S.totalTopology) :=
  haveI : PreservesColimitsOfSize.{u, u}
      (sheafPullbackConstruction.sheafPullback (componentFunctor S n) Ab.{u}
        (S.componentTopology n) S.totalTopology) :=
    (sheafPullbackConstruction.sheafAdjunctionContinuous (componentFunctor S n) Ab.{u}
      (S.componentTopology n) S.totalTopology).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- **Stacks 09WG (7)**, left exactness, reduced to left exactness of the transition inverse
images: *"the exactness properties of `g_{n!}` follow from the formulas given for these
functors"*.

Untagged, because the hypothesis is not one the source makes; it is discharged in both cases of
the situation by
`CategoryTheory.SimplicialSiteSituation.preservesFiniteLimits_transitionInverseImageAb` below. -/
lemma preservesFiniteLimits_componentLowerShriekAb
    (h : ∀ (m : SimplexCategory) (φ : n ⟶ m),
      PreservesFiniteLimits (transitionInverseImageAb S φ)) :
    PreservesFiniteLimits (sheafPullbackConstruction.sheafPullback (componentFunctor S n)
      Ab.{u} (S.componentTopology n) S.totalTopology) := by
  constructor
  intro Kshape _ _
  refine preservesLimitsOfShape_of_componentRestriction S Kshape _ fun m => ?_
  have hφ : ∀ φ : n ⟶ m, PreservesLimitsOfShape Kshape (transitionInverseImageAb S φ) :=
    fun φ => (h m φ).preservesFiniteLimits Kshape
  exact preservesLimitsOfShape_of_isLimitFan _ (isLimitFanComponentLowerShriekRestriction S n m)

end CategoryTheory.SimplicialSiteSituation

namespace CategoryTheory.SimplicialSite

open CategoryTheory.SimplicialSiteSituation

universe u

/-- In case (A) the transition inverse images are the abelian sheaf pullbacks along the
continuous functors representing the transitions. Those functors are morphisms of sites by
definition of `CategoryTheory.SimplicialSite`, so Stacks 04JC applies and they are left exact. -/
@[sga "4 III 1.7" "Clause 4"]
lemma preservesFiniteLimits_transitionInverseImageAb (C : SimplicialSite.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) :
    PreservesFiniteLimits (transitionInverseImageAb
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ) := by
  have hc : ((C.underlying.map φ).toFunctor).IsContinuous
      (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck :=
    (C.isMorphismOfSites φ).isContinuous
  have habs : PreservesFiniteLimits
      (((C.underlying.map φ).toFunctor).sheafPullback Ab.{u}
        (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck) :=
    Stacks.Sites.AbelianPullback.preservesFiniteLimits_sheafPullback_of_isMorphismOfSites
      (C.isMorphismOfSites φ)
  exact @preservesFiniteLimits_of_natIso _ _ _ _ _ _
    (Functor.sheafPullbackConstruction.sheafPullbackIso
      ((C.underlying.map φ).toFunctor) Ab.{u}
      (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck) habs

end CategoryTheory.SimplicialSite

namespace CategoryTheory.CocontinuousSimplicialSite

open CategoryTheory.SimplicialSiteSituation

universe u

variable (C : CocontinuousSimplicialSite.{u}) (n : SimplexCategory)

/-- In case (B) the transition inverse images are the sheaf pullbacks along cocontinuous
functors, hence left exact by Stacks 00XL. -/
lemma preservesFiniteLimits_transitionInverseImageAb {n m : SimplexCategory} (φ : n ⟶ m) :
    PreservesFiniteLimits (transitionInverseImageAb
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ) := by
  have : ((C.underlying.map φ.op).toFunctor).IsCocontinuous
      (topologyOfCoverings (C.coverage (op m))) (topologyOfCoverings (C.coverage (op n))) :=
    C.isCocontinuous φ.op
  exact Functor.preservesFiniteLimits_sheafPullbackCocontinuous _ Ab.{u} _ _

end CategoryTheory.CocontinuousSimplicialSite

namespace CategoryTheory.SimplicialSiteSituation

universe u

/-- Left exactness of the transition inverse images, in both cases of the situation: by
Stacks 00XL in case (B) and by Stacks 04JC in case (A). -/
lemma preservesFiniteLimits_transitionInverseImageAb (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) :
    PreservesFiniteLimits (transitionInverseImageAb S φ) := by
  obtain ⟨c⟩ := S
  cases c with
  | inl C => exact SimplicialSite.preservesFiniteLimits_transitionInverseImageAb C φ
  | inr C => exact CocontinuousSimplicialSite.preservesFiniteLimits_transitionInverseImageAb C φ

/-- **Stacks 09WG (7)** for an arbitrary simplicial-site situation: lower shriek from a
simplicial component is exact on abelian sheaves.

The coefficients here are the abelian groups of the site's own universe. The source says
nothing about universes, and the independent coefficient
universe is not reachable: in case (A) the `isMorphismOfSites` field of
`CategoryTheory.SimplicialSite` fixes the sheaf-value universe of
`CategoryTheory.Functor.IsMorphismOfSites` to the site universe, so Situation 09WE supplies no
morphism of topoi at any other, and Stacks 04JC — which is the source's own Case A argument —
has no input there.

This declaration carries the tag. An independent
coefficient universe is not part of what Stacks 09WG asserts, on three
grounds: the source states clause (7) as *"$g_{n!}$ is exact"* with no universe quantifier at all;
clause (6), `Stmt_09WG__abelian_sum_formula`, which is the
stated *input* of clause (7)'s one-sentence proof, is stated with
`universe u` only and has its conclusion at `Ab.{u}`; and the extra universe is unreachable
from the data Situation 09WE carries, as the paragraph above establishes. So the statement proved
here is the source's clause (7).

The neighbouring clause `09WH__component_injective` is different: its case (A) is not proved
here at all, and whether `ComponentInjective`/`ComponentKInjective` generalise is open. The two are
not symmetric — case (A) of clause (7) *is* proved above. -/
@[stacks 09WG "abelian_exact"]
lemma componentLowerShriek_exactFunctor (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) :
    exactFunctor
      (Sheaf (S.componentTopology n) Ab.{u})
      (Sheaf S.totalTopology Ab.{u})
      (sheafPullbackConstruction.sheafPullback (componentFunctor S n) Ab.{u}
        (S.componentTopology n) S.totalTopology) :=
  ⟨preservesFiniteLimits_componentLowerShriekAb S n
      (fun _ φ => preservesFiniteLimits_transitionInverseImageAb S φ),
    preservesFiniteColimits_componentLowerShriekAb S n⟩

end CategoryTheory.SimplicialSiteSituation

namespace CategoryTheory.CocontinuousSimplicialSite

open CategoryTheory.SimplicialSiteSituation

universe u

/-- **Stacks 09WG (7)** in case (B): the case-(B) instance of
`CategoryTheory.SimplicialSiteSituation.componentLowerShriek_exactFunctor`, retained under this
name because `ComponentInjective` and `ComponentKInjective` consume it. -/
lemma componentLowerShriek_exactFunctor (C : CocontinuousSimplicialSite.{u})
    (n : SimplexCategory) :
    exactFunctor
      (Sheaf ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u})
      (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
      (sheafPullbackConstruction.sheafPullback
        (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n) Ab.{u}
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
        (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology) :=
  SimplicialSiteSituation.componentLowerShriek_exactFunctor _ n

end CategoryTheory.CocontinuousSimplicialSite

end
