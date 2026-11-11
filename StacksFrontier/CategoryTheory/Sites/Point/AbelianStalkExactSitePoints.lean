module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectStalks
public import StacksFrontier.CategoryTheory.Sites.Point.FiberIsoTransport
public import StacksFrontier.CategoryTheory.Sites.Point.OfToposPoint
public import StacksFrontier.CategoryTheory.Sites.Point.StalkFunctor
public import StacksFrontier.CategoryTheory.Sites.Point.StalkOfCoveringFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of abelian sheaves is checked on stalks at points in the sense of Stacks 00Y5

Stacks defines a *point* of a site `C` (Stacks 00Y5) to be a functor `u : C ⥤ Sets` such that

1. for every covering `{U_i → U}` the map `∐ u(U_i) → u(U)` is surjective;
2. for every covering `{U_i → U}` and every morphism `V → U` the maps
   `u(U_i ×_U V) → u(U_i) ×_{u(U)} u(V)` are bijective;
3. the stalk functor `Sh(C) ⥤ Sets`, `F ↦ F_p = colim_{(U, x)} F(U)`, is left exact.

Mathlib's `CategoryTheory.GrothendieckTopology.Point` asks instead that the category of elements
of `u` be cofiltered and initially small. This file shows that every point in the sense of
Stacks is a Mathlib point with the same fibre functor (`Stacks.IsSitePoint.toPoint`), so that the
conservative families of Stacks points and the sites with enough Stacks points (Stacks 00YK) give
conservative families of Mathlib points and Mathlib's `HasEnoughPoints`, and it deduces Stacks
05V3 for the points of Stacks 00Y5.

The cofilteredness is where condition (3) enters. By Stacks 00Y8, conditions (1) and (2) make the
stalk functor a left adjoint (to `u^s`) and make `F_p → (F^#)_p` bijective, so `(sheafStalk, u^s)`
is a point `p` of the topos, and the point of the site attached to `p` by Stacks 00YA (2)
(`PointOfTopos.sitePoint`) has fibre `X ↦ (h_X^#)_p ≅ (h_X)_p ≅ u(X)` (Stacks 00Y8 (3) and
00Y6). Its category of elements is cofiltered because `p⁻¹` is left exact; the point transports
along that isomorphism to a point with fibre `u` itself.

## Main definitions

* `Stacks.IsSitePoint`: a functor `u : C ⥤ Type w` is a point of the site (Stacks 00Y5).
* `Stacks.IsSitePoint.toPoint`: the Mathlib point with fibre functor `u`.
* `Stacks.IsConservativeFamilyOfSitePoints`, `Stacks.HasEnoughSitePoints`: Stacks 00YK.
* `Stacks.abelianStalk`: the stalk `F ↦ F_p` of an abelian sheaf at `u`.

## Main results

* `Stacks.IsSitePoint.isConservativeFamilyOfPoints` and
  `Stacks.HasEnoughSitePoints.hasEnoughPoints`: the transfer to Mathlib's notions.
* `Stacks.StalkExact.exact_iff_forall_abelianStalk_exact`: Stacks 05V3, conservative families.
* `Stacks.StalkExact.exact_iff_forall_abelianStalk_exact_of_hasEnoughSitePoints`: Stacks 05V3,
  enough points.

## Implementation notes

* The site. A site in the sense of Stacks has a *set* of coverings containing `{id_U}` for every
  object `U`, so its objects form a set: the underlying category is small, here
  `C : Type w` with `[SmallCategory C]`, and `Sets` is `Type w`. Its coverings are the coverage
  `K`, as in Stacks 00Y8 (`PresheafPushforwardStalkAdjunction.StalkConditions`), and its sheaves
  are those for `K.toGrothendieck`.
* Condition (2) speaks of the fibre products `U_i ×_U V`, which a Stacks site has by its axioms
  (Stacks 00VH (3)); a Mathlib coverage need not, so their existence is recorded as the field
  `IsSitePoint.hasPullback`. On a site in the sense of Stacks it holds automatically.
* The stalk of an abelian sheaf is the colimit `colim_{(U, x)} F(U)` over the opposite of the
  category of elements of `u`, taken in abelian groups (`Stacks.abelianStalk`).
* A conservative family (Stacks 00YK (1)) is a family whose stalk functors on sheaves of sets
  jointly reflect isomorphisms; an isomorphism of `Type w` is a bijection.

## References

* [Stacks Project, Tag 05V3](https://stacks.math.columbia.edu/tag/05V3)
* [Stacks Project, Tag 00Y5](https://stacks.math.columbia.edu/tag/00Y5)
* [Stacks Project, Tag 00YK](https://stacks.math.columbia.edu/tag/00YK)
* [Stacks Project, Tag 00YA](https://stacks.math.columbia.edu/tag/00YA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite PresheafPushforwardStalkAdjunction

universe t w

namespace Stacks

variable {C : Type w} [SmallCategory C] (K : Coverage C)

/-- **Stacks 00Y5.** A functor `u : C ⥤ Type w` is a *point* of the site `(C, K)` if
(1) for every covering `{U_i → U}` the map `∐ u(U_i) → u(U)` is surjective, (2) for every
covering `{U_i → U}` and every morphism `V → U` the map `u(U_i ×_U V) → u(U_i) ×_{u(U)} u(V)` is
bijective, and (3) the stalk functor `Sh(C) ⥤ Type w`, `F ↦ F_p`, is left exact.

The fibre products in (2) exist on a site in the sense of Stacks (Stacks 00VH (3)); for a
coverage they are the field `hasPullback`. -/
structure IsSitePoint (u : C ⥤ Type w) : Prop where
  /-- (1): `∐ u(U_i) → u(U)` is surjective for every covering `{U_i → U}`. -/
  surjective_cover : ∀ ⦃X : C⦄, ∀ R ∈ K.coverings X, ∀ x : u.obj X,
    ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : u.obj Y), u.map f y = x
  /-- The fibre product `U_i ×_U V` of a member of a covering and a morphism `V → U` exists. -/
  hasPullback : ∀ ⦃X : C⦄, ∀ R ∈ K.coverings X, ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, R f →
    ∀ ⦃V : C⦄ (g : V ⟶ X), HasPullback f g
  /-- (2): `u(U_i ×_U V) → u(U_i) ×_{u(U)} u(V)` is bijective for every covering `{U_i → U}`
  and every morphism `V → U`. -/
  bijective_pullback : ∀ ⦃X : C⦄ (R : Presieve X) (hR : R ∈ K.coverings X) ⦃Y : C⦄ ⦃f : Y ⟶ X⦄
    (hf : R f) ⦃V : C⦄ (g : V ⟶ X),
    haveI := hasPullback R hR hf g
    Function.Bijective (fun z : u.obj (pullback f g) =>
      (⟨(u.map (pullback.fst f g) z, u.map (pullback.snd f g) z), by
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, pullback.condition]⟩ :
        {p : u.obj Y × u.obj V // u.map f p.1 = u.map g p.2}))
  /-- (3): the stalk functor `Sh(C) ⥤ Type w`, `F ↦ F_p`, is left exact. -/
  preservesFiniteLimits : PreservesFiniteLimits (sheafStalk K u)

/-- **Stacks 00YK (1).** A family `{u_i}_{i ∈ I}` of functors `C ⥤ Type w` is *conservative* if
a map of sheaves of sets which induces bijections `F_{p_i} → G_{p_i}` on all the stalks is an
isomorphism. -/
def IsConservativeFamilyOfSitePoints {I : Type t} (u : I → C ⥤ Type w) : Prop :=
  JointlyReflectIsomorphisms fun i => sheafStalk K (u i)

/-- **Stacks 00YK (2).** The site `(C, K)` *has enough points* if there is a conservative family
of points in the sense of Stacks 00Y5. -/
def HasEnoughSitePoints : Prop :=
  ∃ (I : Type w) (u : I → C ⥤ Type w),
    (∀ i, IsSitePoint K (u i)) ∧ IsConservativeFamilyOfSitePoints K u

/-- The stalk `F ↦ F_p = colim_{(U, x)} F(U)` of an abelian sheaf at a functor `u : C ⥤ Type w`,
the colimit over the opposite of the category of elements of `u` taken in abelian groups. -/
abbrev abelianStalk (u : C ⥤ Type w) :
    Sheaf K.toGrothendieck AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
  sheafToPresheaf K.toGrothendieck AddCommGrpCat.{w} ⋙ elementColimit u AddCommGrpCat.{w}

instance (u : C ⥤ Type w) : (abelianStalk K u).Additive := by
  dsimp only [abelianStalk, elementColimit]
  infer_instance

/-- **Stacks 00Y6**, as an isomorphism of functors: `u(U) ≅ (h_U)_p`, naturally in `U`. -/
def fiberIsoYonedaCompPresheafStalk (u : C ⥤ Type w) : u ≅ yoneda ⋙ presheafStalk u :=
  NatIso.ofComponents (fun X => (Equiv.ofBijective _ (Phi_bijective u X)).toIso)
    (fun g => by ext x; exact Phi_naturality u g x)

variable {K}

/-- Under the conditions of Stacks 00Y8, the stalk of a presheaf of sets is the stalk of its
sheafification: the stalk of the unit of the sheafification adjunction is an isomorphism. -/
def presheafStalkIsoSheafify {u : C ⥤ Type w} (h : StalkConditions K u) :
    presheafStalk u ≅
      (presheafToSheaf K.toGrothendieck (Type w) ⋙ sheafToPresheaf K.toGrothendieck (Type w)) ⋙
        presheafStalk u :=
  haveI : ∀ P, IsIso ((Functor.whiskerRight
      (sheafificationAdjunction K.toGrothendieck (Type w)).unit (presheafStalk u)).app P) :=
    fun P => isIso_presheafStalk_map_toSheafify h P
  haveI := NatIso.isIso_of_isIso_app (Functor.whiskerRight
      (sheafificationAdjunction K.toGrothendieck (Type w)).unit (presheafStalk u))
  (Functor.leftUnitor _).symm ≪≫ asIso (Functor.whiskerRight
      (sheafificationAdjunction K.toGrothendieck (Type w)).unit (presheafStalk u))

namespace IsSitePoint

variable {u : C ⥤ Type w} (h : IsSitePoint K u)
include h

/-- Conditions (1) and (2) of a point give the conditions of Stacks 00Y8. -/
theorem stalkConditions : StalkConditions K u where
  surjective_cover := h.surjective_cover
  hasPullback := by
    intro X R hR Y₁ Y₂ f₁ f₂ h₁ _
    exact h.hasPullback R hR h₁ f₂
  surjective_pullback := by
    intro X R hR Y₁ Y₂ f₁ f₂ h₁ _
    exact (h.bijective_pullback R hR h₁ f₂).2

/-- The point of the topos `Sh(C)` attached to a point of the site (Stacks 00YA (1)): its inverse
image is the stalk functor and its pushforward is `u^s` of Stacks 00Y8. -/
def toPointOfTopos : PointOfTopos.{w} K.toGrothendieck where
  pushforward := skyscraper h.stalkConditions
  inverseImage := sheafStalk K u
  adj := sheafAdjunction h.stalkConditions
  preservesFiniteLimits := h.preservesFiniteLimits

/-- The fibre `X ↦ (h_X^#)_p` of the point of the site attached to the point of the topos of `u`
is `u` itself (Stacks 00Y8 (3) and 00Y6). -/
def sitePointFiberIso : h.toPointOfTopos.sitePointFiber ≅ u :=
  (fiberIsoYonedaCompPresheafStalk u ≪≫
    Functor.isoWhiskerRight shrinkYonedaIsoYoneda.symm (presheafStalk u) ≪≫
    Functor.isoWhiskerLeft shrinkYoneda.{w} (presheafStalkIsoSheafify h.stalkConditions)).symm

/-- **A point in the sense of Stacks 00Y5 is a point in the sense of Mathlib**, with the same
fibre functor `u`. Its category of elements is cofiltered because the stalk functor is left
exact (condition (3)). -/
@[stacks 00Y5 "a Stacks point gives a Mathlib `GrothendieckTopology.Point` with fibre `u`"]
def toPoint : K.toGrothendieck.Point.{w} :=
  SitePointFiberIso.pointOfFiberIso h.toPointOfTopos.sitePoint h.sitePointFiberIso

@[simp]
theorem toPoint_fiber : h.toPoint.fiber = u :=
  rfl

/-- The stalk functor on sheaves of sets of `IsSitePoint.toPoint` is the stalk functor of `u`. -/
theorem toPoint_sheafFiber : h.toPoint.sheafFiber (A := Type w) = sheafStalk K u :=
  rfl

/-- The stalk functor on abelian sheaves of `IsSitePoint.toPoint` is the stalk functor of `u`. -/
theorem toPoint_sheafFiber_addCommGrpCat :
    h.toPoint.sheafFiber (A := AddCommGrpCat.{w}) = abelianStalk K u :=
  rfl

end IsSitePoint

/-- A conservative family of points in the sense of Stacks 00YK gives a conservative family of
Mathlib points. -/
theorem IsSitePoint.isConservativeFamilyOfPoints {I : Type t} {u : I → C ⥤ Type w}
    (hu : ∀ i, IsSitePoint K (u i)) (hc : IsConservativeFamilyOfSitePoints K u) :
    (ObjectProperty.ofObj fun i => (hu i).toPoint).IsConservativeFamilyOfPoints where
  jointlyReflectIsomorphisms_type := ⟨fun {F G} φ hφ =>
    haveI : ∀ i, IsIso ((sheafStalk K (u i)).map φ) := fun i =>
      hφ ⟨(hu i).toPoint, ObjectProperty.ofObj_apply _ i⟩
    hc.isIso φ⟩

/-- A site with enough points in the sense of Stacks 00YK has enough points in the sense of
Mathlib. -/
theorem HasEnoughSitePoints.hasEnoughPoints (h : HasEnoughSitePoints K) :
    GrothendieckTopology.HasEnoughPoints.{w} K.toGrothendieck := by
  obtain ⟨I, u, hu, hc⟩ := h
  exact ⟨⟨_, inferInstance, IsSitePoint.isConservativeFamilyOfPoints hu hc⟩⟩

namespace StalkExact

/-- **Stacks 05V3**, for the points of Stacks 00Y5. If `{p_i}_{i ∈ I}` is a conservative family
of points of the site, a short complex of abelian sheaves is exact if and only if its stalks at
the points `p_i` are exact. -/
@[stacks 05V3 "conservative family of points in the sense of Stacks 00Y5"]
theorem exact_iff_forall_abelianStalk_exact {I : Type t} {u : I → C ⥤ Type w}
    (hu : ∀ i, IsSitePoint K (u i)) (hc : IsConservativeFamilyOfSitePoints K u)
    (S : ShortComplex (Sheaf K.toGrothendieck AddCommGrpCat.{w})) :
    S.Exact ↔ ∀ i, (S.map (abelianStalk K (u i))).Exact := by
  rw [exact_iff_forall_sheafFiber_exact (IsSitePoint.isConservativeFamilyOfPoints hu hc) S]
  constructor
  · intro hS i
    exact hS ⟨(hu i).toPoint, ObjectProperty.ofObj_apply _ i⟩
  · rintro hS ⟨Φ, ⟨i⟩⟩
    exact hS i

/-- **Stacks 05V3**, for the points of Stacks 00Y5. If the site has enough points, a short complex
of abelian sheaves is exact if and only if its stalks at all points are exact. -/
@[stacks 05V3 "enough points, for the points of Stacks 00Y5"]
theorem exact_iff_forall_abelianStalk_exact_of_hasEnoughSitePoints (h : HasEnoughSitePoints K)
    (S : ShortComplex (Sheaf K.toGrothendieck AddCommGrpCat.{w})) :
    S.Exact ↔ ∀ u : C ⥤ Type w, IsSitePoint K u → (S.map (abelianStalk K u)).Exact := by
  obtain ⟨I, u, hu, hc⟩ := h
  refine ⟨fun hS v hv => ?_, fun H => (exact_iff_forall_abelianStalk_exact hu hc S).2
    fun i => H _ (hu i)⟩
  exact hS.map (hv.toPoint.sheafFiber (A := AddCommGrpCat.{w}))

end StalkExact

end Stacks
