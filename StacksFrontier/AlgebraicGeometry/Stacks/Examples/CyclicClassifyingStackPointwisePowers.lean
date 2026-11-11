module

public import StacksFrontier.AlgebraicGeometry.Stacks.Examples.CyclicClassifyingStackPointwise
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.ConstantPolynomialSections
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionCanonicalMap

/-!
# The powers of the trivial torsor in the pointwise quotient `[S/_p(ℤ/pℤ)]`

Let `k` be a field, `S = Spec k[x]`, `G = ℤ/pℤ` and let `𝒫 = [S/_pG]` be the pointwise quotient
of `Stacks.Examples.UnboundedDerivedPushforward.cyclicPointwise`, with its object `U` over the
final object `S` of the site (the trivial torsor). An object of `𝒫` over `T` is the unique point
of `S` over `T`, and a morphism `(V, *) ⟶ (T, *)` is a morphism `V ⟶ T` of the site together
with an arrow of the groupoid at `V`, that is a morphism `V ⟶ G_S`. We show that the powers
`U^{n+1}` exist in `𝒫` and lie over the constant group scheme `(G^n)_S`: the first leg of the
limit fan carries the identity arrow and the others the `n` coordinates `(G^n)_S ⟶ G_S`, and a
family of morphisms `(b_i, φ_i)` lifts uniquely to `(b, φ_0)` with `b` the morphism to `(G^n)_S`
whose coordinates are the arrows `φ_{i+1} ∘ φ_0⁻¹`. These are the terms of the Čech complex of
the cover `U` of the final object of `𝒫`, which computes the cohomology of `[S/G]`.

## Main results

* `Stacks.Examples.UnboundedDerivedPushforward.hasProduct_cyclicPointwiseUnitObject`: the power
  `U^{n+1}` exists.
* `Stacks.Examples.UnboundedDerivedPushforward.bijective_cyclicPointwiseUnitObject_hom_pi`: a
  morphism `U ⟶ U^{n+1}` is its base together with its first component.
* `Stacks.Examples.UnboundedDerivedPushforward.isIso_of_cyclicPointwiseUnitObject_endo` and
  `Stacks.Examples.UnboundedDerivedPushforward.natCard_cyclicPointwiseUnitObject_end`: the
  endomorphisms of `U` are automorphisms, and there are `p` of them.
* `Stacks.Examples.UnboundedDerivedPushforward.bijective_structureSheaf_map_cyclicPointwisePi` and
  `Stacks.Examples.UnboundedDerivedPushforward.isAffine_cyclicPointwisePi`: the base of `U^{n+1}`
  is affine, and its functions are the `Γ(S, 𝒪_S)`-valued functions on its points over `S`.
* `Stacks.Examples.UnboundedDerivedPushforward.coversTop_cyclicPointwiseUnitObject`: `U` covers
  the final object of `𝒫`.

## References

* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 07DC](https://stacks.math.columbia.edu/tag/07DC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Examples.UnboundedDerivedPushforward

variable (p : ℕ) [NeZero p] {k : Type u} [Field k] (𝒞 : BigFppfSite.{u})
  (hS : 𝒞.Contains (Spec (.of (Polynomial k))))

/-- The groupoid in functors whose pointwise quotient is `[S/_p(ℤ/pℤ)]`: the trivial action
groupoid of `(ℤ/pℤ)_S` on `S`. -/
abbrev cyclicGroupoidInFunctors := (cyclicActionGroupoid p 𝒞 hS).toGroupoidInFunctors

/-- The groupoid at a test scheme has a single object: the objects are the morphisms to the
final object of the site. -/
instance subsingleton_cyclicGroupoidInFunctors_objects
    (V : (BigFppfOver 𝒞 (Spec (.of (Polynomial k))) hS)ᵒᵖ) :
    Subsingleton ((cyclicGroupoidInFunctors p 𝒞 hS).objects.obj V) :=
  ⟨fun a b => (isTerminalCyclicBaseObject 𝒞 hS).hom_ext a b⟩

/-- The constant group scheme `(ℤ/pℤ)_S`, as an object of the site. -/
abbrev cyclicGroupSiteObject : BigFppfOver 𝒞 (Spec (.of (Polynomial k))) hS :=
  Space.constantGroupSiteObject 𝒞 _ hS (CyclicGroup p) (contains_cyclicGroupScheme p 𝒞 hS)

/-- The first projection of a pullback along an identity is an isomorphism. -/
def pullbackFstIsoOfEqId {C : Type*} [Category* C] {X Y : C} (f : X ⟶ Y) (g : Y ⟶ Y)
    (hg : g = 𝟙 Y) [HasPullback f g] : pullback f g ≅ X :=
  haveI : IsIso g := hg ▸ inferInstance
  asIso (pullback.fst f g)

/-- The arrows of the groupoid are the points of `(ℤ/pℤ)_S`: the arrow space `G ×_S S` is
represented by `G_S`. -/
def cyclicArrowsIso :
    (cyclicGroupoidInFunctors p 𝒞 hS).arrows ≅ yoneda.obj (cyclicGroupSiteObject p 𝒞 hS) :=
  (pullbackFstIsoOfEqId _ _ rfl : (cyclicGroupoidInFunctors p 𝒞 hS).arrows ≅ _) ≪≫
    Space.terminalSpaceProdIso 𝒞 _ hS _ ≪≫
      (Space.pointsOnSiteRepresentableBy 𝒞 _ hS _
        (Space.constantGroupSiteObjectGrpObj 𝒞 _ hS _ _)).toIso.symm

section

variable (H : Type) [Small.{u} H] [Group H]
  (hH : 𝒞.Contains (constantGroupScheme.{u} H (Spec (.of (Polynomial k)))).X.left)

/-- A morphism to a finite constant group scheme of the site is a locally constant map on the
source, by Stacks 03YW. -/
def siteHomEquivLocallyConstant (V : BigFppfOver 𝒞 (Spec (.of (Polynomial k))) hS) :
    (V ⟶ Space.constantGroupSiteObject 𝒞 _ hS H hH) ≃
      LocallyConstant ((Space.toSchemeOver 𝒞 _ hS).obj V).left H :=
  (Space.pointsOnSiteRepresentableBy 𝒞 _ hS _
        (Space.constantGroupSiteObjectGrpObj 𝒞 _ hS H hH)).homEquiv.trans
    (Equiv.ulift.{0}.symm.trans
      ((constantGroupSchemePointsIsoLocallyConstantMaps H (Spec (.of (Polynomial k)))).app
        (op ((Space.toSchemeOver 𝒞 _ hS).obj V))).groupIsoToMulEquiv.toEquiv)

/-- `siteHomEquivLocallyConstant` is natural: precomposition is pullback of locally constant
maps. -/
theorem siteHomEquivLocallyConstant_comp {V V' : BigFppfOver 𝒞 (Spec (.of (Polynomial k))) hS}
    (c : V' ⟶ V) (b : V ⟶ Space.constantGroupSiteObject 𝒞 _ hS H hH) :
    siteHomEquivLocallyConstant 𝒞 hS H hH V' (c ≫ b) =
      (siteHomEquivLocallyConstant 𝒞 hS H hH V b).comap
        ⟨((Space.toSchemeOver 𝒞 _ hS).map c).left.base, by fun_prop⟩ := by
  change ((constantGroupSchemePointsIsoLocallyConstantMaps H (Spec (.of (Polynomial k)))).hom.app _
    (ULift.up ((Space.toSchemeOver 𝒞 _ hS).map (c ≫ b)))) = _
  rw [Functor.map_comp]
  exact ConcreteCategory.congr_hom
    ((constantGroupSchemePointsIsoLocallyConstantMaps H (Spec (.of (Polynomial k)))).hom.naturality
      ((Space.toSchemeOver 𝒞 _ hS).map c).op) (ULift.up ((Space.toSchemeOver 𝒞 _ hS).map b))

end

/-- Locally constant maps to a finite power are families of locally constant maps. -/
theorem bijective_locallyConstant_map_apply {X : Type*} [TopologicalSpace X] (H : Type*)
    (n : ℕ) :
    Function.Bijective (fun (f : LocallyConstant X (Fin n → H)) (i : Fin n) =>
      f.map (fun g => g i)) := by
  refine ⟨fun f g h => LocallyConstant.ext fun x => funext fun i =>
    congrArg (fun F : Fin n → LocallyConstant X H => F i x) h, fun g => ?_⟩
  let : TopologicalSpace H := ⊥
  have : DiscreteTopology H := ⟨rfl⟩
  refine ⟨⟨fun x i => g i x, ?_⟩, ?_⟩
  · rw [IsLocallyConstant.iff_continuous]
    exact continuous_pi fun i => (g i).continuous
  · funext i
    ext x
    rfl

/-- The `n`-th power of `ℤ/pℤ`. -/
abbrev CyclicPowerGroup (n : ℕ) := Fin n → CyclicGroup p

include hS in
/-- The site contains the constant group scheme of `(ℤ/pℤ)^n`. -/
theorem contains_cyclicPowerGroupScheme (n : ℕ) :
    𝒞.Contains (constantGroupScheme.{u} (CyclicPowerGroup p n)
      (Spec (.of (Polynomial k)))).X.left :=
  Space.contains_constantGroupScheme.{u} (CyclicPowerGroup p n) hS

/-- The constant group scheme of `(ℤ/pℤ)^n`, as an object of the site. -/
abbrev cyclicPowerSiteObject (n : ℕ) : BigFppfOver 𝒞 (Spec (.of (Polynomial k))) hS :=
  Space.constantGroupSiteObject 𝒞 _ hS (CyclicPowerGroup p n)
    (contains_cyclicPowerGroupScheme p 𝒞 hS n)

/-- The `i`-th projection `(ℤ/pℤ)^n_S ⟶ (ℤ/pℤ)_S`. -/
def cyclicPowerProj (n : ℕ) (i : Fin n) :
    cyclicPowerSiteObject p 𝒞 hS n ⟶ cyclicGroupSiteObject p 𝒞 hS :=
  (siteHomEquivLocallyConstant 𝒞 hS (CyclicGroup p) _ _).symm
    ((siteHomEquivLocallyConstant 𝒞 hS (CyclicPowerGroup p n) _ _ (𝟙 _)).map
      (fun g => g i))

/-- A morphism followed by the `i`-th projection is read through the `i`-th coordinate. -/
theorem siteHomEquivLocallyConstant_comp_cyclicPowerProj (n : ℕ) (i : Fin n)
    {V : BigFppfOver 𝒞 (Spec (.of (Polynomial k))) hS} (b : V ⟶ cyclicPowerSiteObject p 𝒞 hS n) :
    siteHomEquivLocallyConstant 𝒞 hS (CyclicGroup p) _ V (b ≫ cyclicPowerProj p 𝒞 hS n i) =
      (siteHomEquivLocallyConstant 𝒞 hS (CyclicPowerGroup p n) _ V b).map (fun g => g i) := by
  rw [siteHomEquivLocallyConstant_comp, cyclicPowerProj, Equiv.apply_symm_apply]
  conv_rhs => rw [← Category.comp_id b, siteHomEquivLocallyConstant_comp]
  rfl

/-- **`(ℤ/pℤ)^n_S` is the `n`-th power of `(ℤ/pℤ)_S`**: a morphism to it is the family of its
composites with the projections. -/
theorem bijective_comp_cyclicPowerProj (n : ℕ)
    (V : BigFppfOver 𝒞 (Spec (.of (Polynomial k))) hS) :
    Function.Bijective (fun (b : V ⟶ cyclicPowerSiteObject p 𝒞 hS n) (i : Fin n) =>
      b ≫ cyclicPowerProj p 𝒞 hS n i) := by
  have key : (fun (b : V ⟶ cyclicPowerSiteObject p 𝒞 hS n) (i : Fin n) =>
      b ≫ cyclicPowerProj p 𝒞 hS n i) =
      (Equiv.piCongrRight fun _ => (siteHomEquivLocallyConstant 𝒞 hS (CyclicGroup p) _ V).symm) ∘
        (fun (f : LocallyConstant _ (Fin n → CyclicGroup p)) (i : Fin n) => f.map (fun g => g i)) ∘
          siteHomEquivLocallyConstant 𝒞 hS (CyclicPowerGroup p n) _ V := by
    funext b i
    change _ = (siteHomEquivLocallyConstant 𝒞 hS (CyclicGroup p) _ V).symm
      ((siteHomEquivLocallyConstant 𝒞 hS (CyclicPowerGroup p n) _ V b).map (fun g => g i))
    rw [← siteHomEquivLocallyConstant_comp_cyclicPowerProj, Equiv.symm_apply_apply]
  rw [key]
  exact (Equiv.bijective _).comp
    ((bijective_locallyConstant_map_apply _ n).comp (Equiv.bijective _))

/-- The arrows of the groupoid at `V` are the morphisms `V ⟶ (ℤ/pℤ)_S`. -/
def cyclicArrowsEquiv (V : BigFppfOver 𝒞 (Spec (.of (Polynomial k))) hS) :
    (cyclicGroupoidInFunctors p 𝒞 hS).arrows.obj (op V) ≃ (V ⟶ cyclicGroupSiteObject p 𝒞 hS) :=
  ((cyclicArrowsIso p 𝒞 hS).app (op V)).toEquiv

/-- `cyclicArrowsEquiv` is natural. -/
theorem cyclicArrowsEquiv_map {V V' : BigFppfOver 𝒞 (Spec (.of (Polynomial k))) hS}
    (c : V' ⟶ V) (a : (cyclicGroupoidInFunctors p 𝒞 hS).arrows.obj (op V)) :
    cyclicArrowsEquiv p 𝒞 hS V' ((cyclicGroupoidInFunctors p 𝒞 hS).arrows.map c.op a) =
      c ≫ cyclicArrowsEquiv p 𝒞 hS V a :=
  NatTrans.naturality_apply (cyclicArrowsIso p 𝒞 hS).hom c.op a

section Groupoid

variable {D : Type*} [Category* D] (G : Deformation.GroupoidInFunctors D) (T : D)
  [Subsingleton (G.objects.obj T)]

/-- With a single object, composition of arrows is composition in the evaluated groupoid. -/
theorem compose_eq_of_subsingleton (a b : G.arrows.obj T) (o : G.objects.obj T) :
    G.compose T a b (Subsingleton.elim _ _) =
      (G.evaluationArrowEquiv T o o
        ((G.evaluationArrowEquiv T o o).symm ⟨b, Subsingleton.elim _ _, Subsingleton.elim _ _⟩ ≫
          (G.evaluationArrowEquiv T o o).symm
            ⟨a, Subsingleton.elim _ _, Subsingleton.elim _ _⟩)).1 := by
  rw [G.evaluationArrowEquiv_comp]
  simp only [Equiv.apply_symm_apply]

/-- With a single object, composing on the right with a fixed arrow is a bijection. -/
theorem bijective_compose_of_subsingleton (b : G.arrows.obj T) :
    Function.Bijective (fun a => G.compose T a b (Subsingleton.elim _ _)) := by
  let o := G.source.app T b
  let E := G.evaluationArrowEquiv T o o
  let m₀ := E.symm ⟨b, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hE (a : G.arrows.obj T) :
      E (E.symm ⟨a, Subsingleton.elim _ _, Subsingleton.elim _ _⟩) =
        ⟨a, Subsingleton.elim _ _, Subsingleton.elim _ _⟩ := E.apply_symm_apply _
  refine ⟨fun a a' h => ?_, fun c => ?_⟩
  · simp only [compose_eq_of_subsingleton G T _ _ o] at h
    have h' := (cancel_epi m₀).1 (E.injective (Subtype.ext h))
    have := congrArg (fun m => (E m).1) h'
    simpa only [E, Equiv.apply_symm_apply] using this
  · refine ⟨(E (inv m₀ ≫ E.symm ⟨c, Subsingleton.elim _ _, Subsingleton.elim _ _⟩)).1, ?_⟩
    change G.compose T _ b (Subsingleton.elim _ _) = c
    rw [compose_eq_of_subsingleton G T _ _ o]
    have : E.symm ⟨(E (inv m₀ ≫ E.symm ⟨c, Subsingleton.elim _ _, Subsingleton.elim _ _⟩)).1,
        Subsingleton.elim _ _, Subsingleton.elim _ _⟩ =
          inv m₀ ≫ E.symm ⟨c, Subsingleton.elim _ _, Subsingleton.elim _ _⟩ :=
      E.symm_apply_eq.2 (Subtype.ext rfl)
    change (E (m₀ ≫ E.symm _)).1 = c
    rw [this, IsIso.hom_inv_id_assoc, hE]

/-- With a single object, composing with an identity arrow does nothing. -/
theorem compose_identity_of_subsingleton (x : G.Evaluation T) (b : G.arrows.obj T) :
    G.compose T (G.identity T x) b (Subsingleton.elim _ _) = b := by
  rw [compose_eq_of_subsingleton G T _ _ x]
  have : (G.evaluationArrowEquiv T x x).symm
      ⟨G.identity T x, Subsingleton.elim _ _, Subsingleton.elim _ _⟩ = 𝟙 x :=
    (G.evaluationArrowEquiv T x x).symm_apply_eq.2 (Subtype.ext rfl)
  rw [this, Category.comp_id, Equiv.apply_symm_apply]

end Groupoid

/-- Any two objects of the groupoid at a test scheme agree: the objects are the morphisms to the
final object. -/
theorem cyclicGroupoidInFunctors_objects_eq {V : (BigFppfOver 𝒞 (Spec (.of (Polynomial k))) hS)ᵒᵖ}
    (a b : (cyclicGroupoidInFunctors p 𝒞 hS).objects.obj V) : a = b :=
  Subsingleton.elim a b

/-- The arrow of the groupoid named by a morphism of the pointwise quotient. -/
def cyclicPointwiseHomArrow {x y : (cyclicPointwise p 𝒞 hS).obj} (f : x ⟶ y) :
    (cyclicGroupoidInFunctors p 𝒞 hS).arrows.obj (op ((cyclicPointwise p 𝒞 hS).p.obj x)) :=
  ((cyclicGroupoidInFunctors p 𝒞 hS).evaluationArrowEquiv (op x.base) x.fiber _ f.fiber).1

/-- The morphism of the pointwise quotient with given base and given arrow. -/
def cyclicPointwiseHomMk {x y : (cyclicPointwise p 𝒞 hS).obj}
    (b : (cyclicPointwise p 𝒞 hS).p.obj x ⟶ (cyclicPointwise p 𝒞 hS).p.obj y)
    (a : (cyclicGroupoidInFunctors p 𝒞 hS).arrows.obj (op ((cyclicPointwise p 𝒞 hS).p.obj x))) :
    x ⟶ y :=
  ⟨b, ((cyclicGroupoidInFunctors p 𝒞 hS).evaluationArrowEquiv (op x.base) x.fiber _).symm
    ⟨a, cyclicGroupoidInFunctors_objects_eq p 𝒞 hS _ _,
      cyclicGroupoidInFunctors_objects_eq p 𝒞 hS _ _⟩⟩

/-- The base of `cyclicPointwiseHomMk`. -/
theorem cyclicPointwiseHomMk_base {x y : (cyclicPointwise p 𝒞 hS).obj}
    (b : (cyclicPointwise p 𝒞 hS).p.obj x ⟶ (cyclicPointwise p 𝒞 hS).p.obj y)
    (a : (cyclicGroupoidInFunctors p 𝒞 hS).arrows.obj (op ((cyclicPointwise p 𝒞 hS).p.obj x))) :
    (cyclicPointwise p 𝒞 hS).p.map (cyclicPointwiseHomMk p 𝒞 hS b a) = b :=
  rfl

/-- The arrow of `cyclicPointwiseHomMk`. -/
theorem cyclicPointwiseHomArrow_homMk {x y : (cyclicPointwise p 𝒞 hS).obj}
    (b : (cyclicPointwise p 𝒞 hS).p.obj x ⟶ (cyclicPointwise p 𝒞 hS).p.obj y)
    (a : (cyclicGroupoidInFunctors p 𝒞 hS).arrows.obj (op ((cyclicPointwise p 𝒞 hS).p.obj x))) :
    cyclicPointwiseHomArrow p 𝒞 hS (cyclicPointwiseHomMk p 𝒞 hS b a) = a :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- A morphism of the pointwise quotient is determined by its base and its arrow. -/
theorem cyclicPointwise_hom_ext {x y : (cyclicPointwise p 𝒞 hS).obj} {f g : x ⟶ y}
    (hb : (cyclicPointwise p 𝒞 hS).p.map f = (cyclicPointwise p 𝒞 hS).p.map g)
    (ha : cyclicPointwiseHomArrow p 𝒞 hS f = cyclicPointwiseHomArrow p 𝒞 hS g) : f = g := by
  obtain ⟨b, φ⟩ := f
  obtain ⟨b', φ'⟩ := g
  obtain rfl : b = b' := hb
  obtain rfl : φ = φ' := (Equiv.injective _) (Subtype.ext ha)
  rfl

/-- Composition in the groupoid, with the first arrow read through an equality. -/
theorem compose_congr_left {D : Type*} [Category* D] (G : Deformation.GroupoidInFunctors D)
    (T : D) {a a' : G.arrows.obj T} (b : G.arrows.obj T) (e : a = a')
    (h : G.source.app T a = G.target.app T b) (h' : G.source.app T a' = G.target.app T b) :
    G.compose T a b h = G.compose T a' b h' := by
  subst e
  rfl

/-- Composition in the groupoid, with the second arrow read through an equality. -/
theorem compose_congr_right {D : Type*} [Category* D] (G : Deformation.GroupoidInFunctors D)
    (T : D) (a : G.arrows.obj T) {b b' : G.arrows.obj T} (e : b = b')
    (h : G.source.app T a = G.target.app T b) (h' : G.source.app T a = G.target.app T b') :
    G.compose T a b h = G.compose T a b' h' := by
  subst e
  rfl

/-- The arrow named by a composite is the composite of the arrows named, the second pulled back
along the base of the first. -/
theorem cyclicPointwiseHomArrow_comp {x y z : (cyclicPointwise p 𝒞 hS).obj} (f : x ⟶ y)
    (g : y ⟶ z) :
    cyclicPointwiseHomArrow p 𝒞 hS (f ≫ g) =
      (cyclicGroupoidInFunctors p 𝒞 hS).compose (op ((cyclicPointwise p 𝒞 hS).p.obj x))
        ((cyclicGroupoidInFunctors p 𝒞 hS).arrows.map ((cyclicPointwise p 𝒞 hS).p.map f).op
          (cyclicPointwiseHomArrow p 𝒞 hS g))
        (cyclicPointwiseHomArrow p 𝒞 hS f) (cyclicGroupoidInFunctors_objects_eq p 𝒞 hS _ _) := by
  refine (Deformation.GroupoidInFunctors.evaluationArrowEquiv_comp
    (cyclicGroupoidInFunctors p 𝒞 hS) (op x.base) f.fiber _).trans ?_
  congr 1
  refine (AlgebraicGeometry.Stack.SelfIntersection.evaluationArrowEquiv_comp_catEqToHom
    (cyclicGroupoidInFunctors p 𝒞 hS) (op x.base)
    (((Stack.evaluationGroupoidFunctor (cyclicGroupoidInFunctors p 𝒞 hS) ⋙
      Grpd.forgetToCat).map_comp g.base.op f.base.op).symm) z.fiber _).trans ?_
  exact Deformation.evaluationMap_map_arrow (cyclicGroupoidInFunctors p 𝒞 hS) f.base.op g.fiber

/-- The object of the pointwise quotient over `T`, with the unique point of the final space. -/
def cyclicPointwiseObj (T : BigFppfOver 𝒞 (Spec (.of (Polynomial k))) hS) :
    (cyclicPointwise p 𝒞 hS).obj where
  base := T
  fiber := ((isTerminalCyclicBaseObject 𝒞 hS).from T :
    (yoneda.obj (cyclicBaseObject 𝒞 hS)).obj (op T))

/-- The arrows at `(ℤ/pℤ)^n_S` of the legs of the power fan: the identity, then the
coordinates. -/
def cyclicPowerLegArrow (n : ℕ) :
    Fin (n + 1) →
      (cyclicGroupoidInFunctors p 𝒞 hS).arrows.obj (op (cyclicPowerSiteObject p 𝒞 hS n)) :=
  Fin.cases ((cyclicGroupoidInFunctors p 𝒞 hS).identity _
      ((isTerminalCyclicBaseObject 𝒞 hS).from (cyclicPowerSiteObject p 𝒞 hS n) :
        (yoneda.obj (cyclicBaseObject 𝒞 hS)).obj (op (cyclicPowerSiteObject p 𝒞 hS n))))
    (fun i => (cyclicArrowsEquiv p 𝒞 hS _).symm (cyclicPowerProj p 𝒞 hS n i))

/-- The fan exhibiting `U^{n+1}`: its apex lies over `(ℤ/pℤ)^n_S`. -/
def cyclicPowerFan (n : ℕ) : Fan (fun _ : Fin (n + 1) => cyclicPointwiseUnitObject p 𝒞 hS) :=
  Fan.mk (cyclicPointwiseObj p 𝒞 hS (cyclicPowerSiteObject p 𝒞 hS n)) fun j =>
    cyclicPointwiseHomMk p 𝒞 hS ((isTerminalCyclicBaseObject 𝒞 hS).from _)
      (cyclicPowerLegArrow p 𝒞 hS n j)

/-- The arrow of a morphism to the apex of the power fan followed by a leg. -/
theorem cyclicPointwiseHomArrow_comp_cyclicPowerFan_proj (n : ℕ)
    {x : (cyclicPointwise p 𝒞 hS).obj} (m : x ⟶ (cyclicPowerFan p 𝒞 hS n).pt)
    (j : Fin (n + 1)) :
    cyclicPointwiseHomArrow p 𝒞 hS (m ≫ (cyclicPowerFan p 𝒞 hS n).proj j) =
      (cyclicGroupoidInFunctors p 𝒞 hS).compose (op ((cyclicPointwise p 𝒞 hS).p.obj x))
        ((cyclicGroupoidInFunctors p 𝒞 hS).arrows.map ((cyclicPointwise p 𝒞 hS).p.map m).op
          (cyclicPowerLegArrow p 𝒞 hS n j))
        (cyclicPointwiseHomArrow p 𝒞 hS m) (cyclicGroupoidInFunctors_objects_eq p 𝒞 hS _ _) :=
  (cyclicPointwiseHomArrow_comp p 𝒞 hS m _).trans (compose_congr_left _ _ _
    (congrArg
      ((cyclicGroupoidInFunctors p 𝒞 hS).arrows.map ((cyclicPointwise p 𝒞 hS).p.map m).op)
      (cyclicPointwiseHomArrow_homMk (x := (cyclicPowerFan p 𝒞 hS n).pt)
        (y := cyclicPointwiseUnitObject p 𝒞 hS) p 𝒞 hS _ (cyclicPowerLegArrow p 𝒞 hS n j))) _ _)

/-- The first leg of the power fan does not change the arrow. -/
theorem cyclicPointwiseHomArrow_comp_cyclicPowerFan_proj_zero (n : ℕ)
    {x : (cyclicPointwise p 𝒞 hS).obj} (m : x ⟶ (cyclicPowerFan p 𝒞 hS n).pt) :
    cyclicPointwiseHomArrow p 𝒞 hS (m ≫ (cyclicPowerFan p 𝒞 hS n).proj 0) =
      cyclicPointwiseHomArrow p 𝒞 hS m :=
  (cyclicPointwiseHomArrow_comp_cyclicPowerFan_proj p 𝒞 hS n m 0).trans
    ((compose_congr_left _ _ _ (Deformation.evalMap_identity (cyclicGroupoidInFunctors p 𝒞 hS)
      ((cyclicPointwise p 𝒞 hS).p.map m).op _) _
      (cyclicGroupoidInFunctors_objects_eq p 𝒞 hS _ _)).trans
        (compose_identity_of_subsingleton _ _ _ _))

/-- The other legs of the power fan compose with the coordinates. -/
theorem cyclicPointwiseHomArrow_comp_cyclicPowerFan_proj_succ (n : ℕ)
    {x : (cyclicPointwise p 𝒞 hS).obj} (m : x ⟶ (cyclicPowerFan p 𝒞 hS n).pt) (i : Fin n) :
    cyclicPointwiseHomArrow p 𝒞 hS (m ≫ (cyclicPowerFan p 𝒞 hS n).proj i.succ) =
      (cyclicGroupoidInFunctors p 𝒞 hS).compose (op ((cyclicPointwise p 𝒞 hS).p.obj x))
        ((cyclicArrowsEquiv p 𝒞 hS ((cyclicPointwise p 𝒞 hS).p.obj x)).symm
          ((cyclicPointwise p 𝒞 hS).p.map m ≫ cyclicPowerProj p 𝒞 hS n i))
        (cyclicPointwiseHomArrow p 𝒞 hS m) (cyclicGroupoidInFunctors_objects_eq p 𝒞 hS _ _) := by
  refine (cyclicPointwiseHomArrow_comp_cyclicPowerFan_proj p 𝒞 hS n m i.succ).trans
    (compose_congr_left _ _ _ ?_ _ _)
  refine (cyclicArrowsEquiv p 𝒞 hS ((cyclicPointwise p 𝒞 hS).p.obj x)).injective ?_
  refine (cyclicArrowsEquiv_map p 𝒞 hS ((cyclicPointwise p 𝒞 hS).p.map m) _).trans ?_
  exact (congrArg ((cyclicPointwise p 𝒞 hS).p.map m ≫ ·) (Equiv.apply_symm_apply _ _)).trans
    (Equiv.apply_symm_apply _ _).symm

/-- Composition on the right with the arrow of a morphism, as an equivalence. -/
def cyclicComposeEquiv {x : (cyclicPointwise p 𝒞 hS).obj}
    (f : x ⟶ cyclicPointwiseUnitObject p 𝒞 hS) :
    (cyclicGroupoidInFunctors p 𝒞 hS).arrows.obj (op ((cyclicPointwise p 𝒞 hS).p.obj x)) ≃
      (cyclicGroupoidInFunctors p 𝒞 hS).arrows.obj (op ((cyclicPointwise p 𝒞 hS).p.obj x)) :=
  Equiv.ofBijective _ (bijective_compose_of_subsingleton (cyclicGroupoidInFunctors p 𝒞 hS)
    (op ((cyclicPointwise p 𝒞 hS).p.obj x)) (cyclicPointwiseHomArrow p 𝒞 hS f))

/-- The base of the morphism to the apex of the power fan induced by a family of morphisms. -/
def cyclicPowerLiftBase (n : ℕ) {x : (cyclicPointwise p 𝒞 hS).obj}
    (f : Fin (n + 1) → (x ⟶ cyclicPointwiseUnitObject p 𝒞 hS)) :
    (cyclicPointwise p 𝒞 hS).p.obj x ⟶ cyclicPowerSiteObject p 𝒞 hS n :=
  (Equiv.ofBijective _
      (bijective_comp_cyclicPowerProj p 𝒞 hS n ((cyclicPointwise p 𝒞 hS).p.obj x))).symm fun i =>
    cyclicArrowsEquiv p 𝒞 hS ((cyclicPointwise p 𝒞 hS).p.obj x)
      ((cyclicComposeEquiv p 𝒞 hS (f 0)).symm (cyclicPointwiseHomArrow p 𝒞 hS (f i.succ)))

/-- The base of the induced morphism followed by a projection. -/
theorem cyclicPowerLiftBase_comp (n : ℕ) {x : (cyclicPointwise p 𝒞 hS).obj}
    (f : Fin (n + 1) → (x ⟶ cyclicPointwiseUnitObject p 𝒞 hS)) (i : Fin n) :
    cyclicPowerLiftBase p 𝒞 hS n f ≫ cyclicPowerProj p 𝒞 hS n i =
      cyclicArrowsEquiv p 𝒞 hS ((cyclicPointwise p 𝒞 hS).p.obj x)
        ((cyclicComposeEquiv p 𝒞 hS (f 0)).symm (cyclicPointwiseHomArrow p 𝒞 hS (f i.succ))) :=
  congrFun
    ((Equiv.ofBijective _ (bijective_comp_cyclicPowerProj p 𝒞 hS n
      ((cyclicPointwise p 𝒞 hS).p.obj x))).apply_symm_apply _) i

/-- Two morphisms to `U` agree when their arrows do. -/
theorem cyclicPointwiseUnitObject_hom_ext {x : (cyclicPointwise p 𝒞 hS).obj}
    {f g : x ⟶ cyclicPointwiseUnitObject p 𝒞 hS}
    (h : cyclicPointwiseHomArrow p 𝒞 hS f = cyclicPointwiseHomArrow p 𝒞 hS g) : f = g :=
  cyclicPointwise_hom_ext p 𝒞 hS ((isTerminalCyclicBaseObject 𝒞 hS).hom_ext _ _) h

/-- **The power fan is a limit**: `U^{n+1}` lies over `(ℤ/pℤ)^n_S`. -/
def isLimitCyclicPowerFan (n : ℕ) : IsLimit (cyclicPowerFan p 𝒞 hS n) :=
  Fan.IsLimit.mk _
    (fun s => cyclicPointwiseHomMk p 𝒞 hS (cyclicPowerLiftBase p 𝒞 hS n s.proj)
      (cyclicPointwiseHomArrow p 𝒞 hS (s.proj 0)))
    (fun s j => by
      refine cyclicPointwiseUnitObject_hom_ext p 𝒞 hS ?_
      induction j using Fin.cases with
      | zero =>
        exact (cyclicPointwiseHomArrow_comp_cyclicPowerFan_proj_zero p 𝒞 hS n _).trans
          (cyclicPointwiseHomArrow_homMk p 𝒞 hS _ _)
      | succ i =>
        refine (cyclicPointwiseHomArrow_comp_cyclicPowerFan_proj_succ p 𝒞 hS n _ i).trans ?_
        refine (compose_congr_right _ _ _ (cyclicPointwiseHomArrow_homMk p 𝒞 hS _ _) _
          (cyclicGroupoidInFunctors_objects_eq p 𝒞 hS _ _)).trans ?_
        refine (compose_congr_left _ _ _ ((congrArg (cyclicArrowsEquiv p 𝒞 hS _).symm
          (cyclicPowerLiftBase_comp p 𝒞 hS n s.proj i)).trans (Equiv.symm_apply_apply _ _)) _
          (cyclicGroupoidInFunctors_objects_eq p 𝒞 hS _ _)).trans ?_
        exact (cyclicComposeEquiv p 𝒞 hS (s.proj 0)).apply_symm_apply _)
    (fun s m hm => by
      have ha : cyclicPointwiseHomArrow p 𝒞 hS m = cyclicPointwiseHomArrow p 𝒞 hS (s.proj 0) :=
        (cyclicPointwiseHomArrow_comp_cyclicPowerFan_proj_zero p 𝒞 hS n m).symm.trans
          (congrArg _ (hm 0))
      refine cyclicPointwise_hom_ext p 𝒞 hS ?_
        (ha.trans (cyclicPointwiseHomArrow_homMk p 𝒞 hS _ _).symm)
      refine (Equiv.ofBijective _ (bijective_comp_cyclicPowerProj p 𝒞 hS n _)).injective
        (funext fun i => ?_)
      refine Eq.trans ?_ (cyclicPowerLiftBase_comp p 𝒞 hS n s.proj i).symm
      refine (cyclicArrowsEquiv p 𝒞 hS _).symm_apply_eq.1 ?_
      refine (cyclicComposeEquiv p 𝒞 hS (s.proj 0)).eq_symm_apply.2 ?_
      refine Eq.trans ?_ (congrArg (cyclicPointwiseHomArrow p 𝒞 hS) (hm i.succ))
      refine Eq.trans ?_
        (cyclicPointwiseHomArrow_comp_cyclicPowerFan_proj_succ p 𝒞 hS n m i).symm
      exact compose_congr_right _ _ _ ha.symm _ _)

/-- **`U^{n+1}` exists** in the pointwise quotient. -/
instance hasProduct_cyclicPointwiseUnitObject (n : ℕ) :
    HasProduct (fun _ : Fin (n + 1) => cyclicPointwiseUnitObject p 𝒞 hS) :=
  HasLimit.mk ⟨_, isLimitCyclicPowerFan p 𝒞 hS n⟩

/-- The chosen product `U^{n+1}` is the apex of the power fan. -/
def cyclicPointwisePiIso (n : ℕ) :
    (∏ᶜ fun _ : Fin (n + 1) => cyclicPointwiseUnitObject p 𝒞 hS) ≅
      (cyclicPowerFan p 𝒞 hS n).pt :=
  limit.isoLimitCone ⟨_, isLimitCyclicPowerFan p 𝒞 hS n⟩

/-- The comparison with the power fan commutes with the projections. -/
@[reassoc]
theorem cyclicPointwisePiIso_hom_proj (n : ℕ) (j : Fin (n + 1)) :
    (cyclicPointwisePiIso p 𝒞 hS n).hom ≫ (cyclicPowerFan p 𝒞 hS n).proj j =
      Pi.π (fun _ : Fin (n + 1) => cyclicPointwiseUnitObject p 𝒞 hS) j :=
  limit.isoLimitCone_hom_π _ (Discrete.mk j)

/-- **A morphism `U ⟶ U^{n+1}` is a morphism of the site together with an endomorphism of `U`**:
its base and its first component. -/
theorem bijective_cyclicPointwiseUnitObject_hom_pi (n : ℕ) :
    Function.Bijective (fun f : cyclicPointwiseUnitObject p 𝒞 hS ⟶
        ∏ᶜ (fun _ : Fin (n + 1) => cyclicPointwiseUnitObject p 𝒞 hS) =>
      ((cyclicPointwise p 𝒞 hS).p.map f,
        f ≫ Pi.π (fun _ : Fin (n + 1) => cyclicPointwiseUnitObject p 𝒞 hS) 0)) := by
  obtain ⟨L, hL⟩ : ∃ L : (∏ᶜ fun _ : Fin (n + 1) => cyclicPointwiseUnitObject p 𝒞 hS) ≅
      (cyclicPowerFan p 𝒞 hS n).pt, ∀ j, L.hom ≫ (cyclicPowerFan p 𝒞 hS n).proj j =
        Pi.π (fun _ : Fin (n + 1) => cyclicPointwiseUnitObject p 𝒞 hS) j :=
    ⟨_, cyclicPointwisePiIso_hom_proj p 𝒞 hS n⟩
  have e : ∀ g : cyclicPointwiseUnitObject p 𝒞 hS ⟶
      ∏ᶜ (fun _ : Fin (n + 1) => cyclicPointwiseUnitObject p 𝒞 hS),
      cyclicPointwiseHomArrow p 𝒞 hS (g ≫ L.hom) =
        cyclicPointwiseHomArrow p 𝒞 hS (g ≫ Pi.π _ 0) := fun g =>
    (cyclicPointwiseHomArrow_comp_cyclicPowerFan_proj_zero p 𝒞 hS n (g ≫ L.hom)).symm.trans
      (congrArg _ ((Category.assoc _ _ _).trans (congrArg (g ≫ ·) (hL 0))))
  refine ⟨fun f f' h => ?_, fun be => ?_⟩
  · have h₁ : (cyclicPointwise p 𝒞 hS).p.map f = (cyclicPointwise p 𝒞 hS).p.map f' :=
      congrArg Prod.fst h
    have h₂ : f ≫ Pi.π _ 0 = f' ≫ Pi.π _ 0 := congrArg Prod.snd h
    refine (cancel_mono L.hom).1 (cyclicPointwise_hom_ext p 𝒞 hS ?_ ?_)
    · rw [Functor.map_comp, Functor.map_comp, h₁]
    · exact (e f).trans ((congrArg _ h₂).trans (e f').symm)
  · let g : cyclicPointwiseUnitObject p 𝒞 hS ⟶ (cyclicPowerFan p 𝒞 hS n).pt :=
      cyclicPointwiseHomMk p 𝒞 hS (be.1 ≫ (cyclicPointwise p 𝒞 hS).p.map L.hom)
        (cyclicPointwiseHomArrow p 𝒞 hS be.2)
    have hg : cyclicPointwiseHomArrow p 𝒞 hS g = cyclicPointwiseHomArrow p 𝒞 hS be.2 :=
      cyclicPointwiseHomArrow_homMk (x := cyclicPointwiseUnitObject p 𝒞 hS)
        (y := (cyclicPowerFan p 𝒞 hS n).pt) p 𝒞 hS _ _
    refine ⟨g ≫ L.inv, Prod.ext ?_ ?_⟩
    · refine ((cyclicPointwise p 𝒞 hS).p.map_comp g L.inv).trans ?_
      change (be.1 ≫ (cyclicPointwise p 𝒞 hS).p.map L.hom) ≫
        (cyclicPointwise p 𝒞 hS).p.map L.inv = be.1
      rw [Category.assoc, ← Functor.map_comp, L.hom_inv_id, CategoryTheory.Functor.map_id,
        Category.comp_id]
    · change (g ≫ L.inv) ≫ Pi.π _ 0 = be.2
      rw [Category.assoc, ← hL, L.inv_hom_id_assoc]
      exact cyclicPointwiseUnitObject_hom_ext p 𝒞 hS
        ((cyclicPointwiseHomArrow_comp_cyclicPowerFan_proj_zero p 𝒞 hS n g).trans hg)

/-- Every endomorphism of `U` has a right inverse. -/
theorem exists_comp_eq_id_cyclicPointwiseUnitObject
    (f : cyclicPointwiseUnitObject p 𝒞 hS ⟶ cyclicPointwiseUnitObject p 𝒞 hS) :
    ∃ g, f ≫ g = 𝟙 _ := by
  obtain ⟨a, ha⟩ := (bijective_compose_of_subsingleton (cyclicGroupoidInFunctors p 𝒞 hS) _
    (cyclicPointwiseHomArrow p 𝒞 hS f)).2
      (cyclicPointwiseHomArrow p 𝒞 hS (𝟙 (cyclicPointwiseUnitObject p 𝒞 hS)))
  refine ⟨cyclicPointwiseHomMk p 𝒞 hS (𝟙 _) a, cyclicPointwiseUnitObject_hom_ext p 𝒞 hS ?_⟩
  have hb : (cyclicPointwise p 𝒞 hS).p.map f = 𝟙 _ :=
    (isTerminalCyclicBaseObject 𝒞 hS).hom_ext _ _
  refine (cyclicPointwiseHomArrow_comp p 𝒞 hS _ _).trans (Eq.trans ?_ ha)
  refine compose_congr_left _ _ _ ?_ _ _
  refine (congrArg
    ((cyclicGroupoidInFunctors p 𝒞 hS).arrows.map ((cyclicPointwise p 𝒞 hS).p.map f).op)
    (cyclicPointwiseHomArrow_homMk p 𝒞 hS _ _)).trans ?_
  rw [hb, op_id, Functor.map_id_apply]

/-- **Every endomorphism of `U` is an isomorphism.** -/
theorem isIso_of_cyclicPointwiseUnitObject_endo
    (f : cyclicPointwiseUnitObject p 𝒞 hS ⟶ cyclicPointwiseUnitObject p 𝒞 hS) : IsIso f := by
  obtain ⟨g, hg⟩ := exists_comp_eq_id_cyclicPointwiseUnitObject p 𝒞 hS f
  obtain ⟨h, hh⟩ := exists_comp_eq_id_cyclicPointwiseUnitObject p 𝒞 hS g
  have hfh : f = h := by
    rw [← Category.comp_id f, ← hh, ← Category.assoc, hg, Category.id_comp]
  exact ⟨g, hg, hfh ▸ hh⟩

/-- **`U` covers the final object**: every object of the pointwise quotient maps to `U`. -/
theorem coversTop_cyclicPointwiseUnitObject :
    (cyclicPointwiseTopology p 𝒞 hS).CoversTop
      (fun _ : Unit => cyclicPointwiseUnitObject p 𝒞 hS) :=
  fun X => (cyclicPointwiseTopology p 𝒞 hS).superset_covering (S := ⊤) (by
    intro W g _
    exact ⟨(), ⟨cyclicPointwiseHomMk p 𝒞 hS ((isTerminalCyclicBaseObject 𝒞 hS).from _)
      ((cyclicGroupoidInFunctors p 𝒞 hS).identity _ W.fiber)⟩⟩)
    ((cyclicPointwiseTopology p 𝒞 hS).top_mem X)

/-- **`U` has exactly `p` endomorphisms**: they are the points of `(ℤ/pℤ)_S` over the connected
base `S`. -/
theorem natCard_cyclicPointwiseUnitObject_end :
    Nat.card (cyclicPointwiseUnitObject p 𝒞 hS ⟶ cyclicPointwiseUnitObject p 𝒞 hS) = p := by
  let e : (cyclicPointwiseUnitObject p 𝒞 hS ⟶ cyclicPointwiseUnitObject p 𝒞 hS) ≃
      (cyclicGroupoidInFunctors p 𝒞 hS).arrows.obj (op (cyclicBaseObject 𝒞 hS)) :=
    Equiv.ofBijective (cyclicPointwiseHomArrow p 𝒞 hS)
      ⟨fun _ _ h => cyclicPointwiseUnitObject_hom_ext p 𝒞 hS h,
        fun a => ⟨cyclicPointwiseHomMk p 𝒞 hS (𝟙 _) a,
          cyclicPointwiseHomArrow_homMk (x := cyclicPointwiseUnitObject p 𝒞 hS)
            (y := cyclicPointwiseUnitObject p 𝒞 hS) p 𝒞 hS _ a⟩⟩
  refine (Nat.card_congr (e.trans (cyclicArrowsEquiv p 𝒞 hS _))).trans ?_
  refine (Space.natCard_baseTerminal_hom_constantGroupSiteObject 𝒞 hS (CyclicGroup p)
    (contains_cyclicGroupScheme p 𝒞 hS)).trans ?_
  exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod p)

/-- The base of `U^{n+1}` is `(ℤ/pℤ)^n_S`. -/
def cyclicPointwisePiBaseIso (n : ℕ) :
    (cyclicPointwise p 𝒞 hS).p.obj
        (∏ᶜ fun _ : Fin (n + 1) => cyclicPointwiseUnitObject p 𝒞 hS) ≅
      cyclicPowerSiteObject p 𝒞 hS n :=
  (cyclicPointwise p 𝒞 hS).p.mapIso (cyclicPointwisePiIso p 𝒞 hS n)

/-- The description of the functions on an object of the site by their values at the points over
`S` is invariant under isomorphism. -/
theorem bijective_structureSheaf_map_of_iso
    {X W : BigFppfOver 𝒞 (Spec (.of (Polynomial k))) hS} (e : X ≅ W)
    (h : Function.Bijective (fun (s : ↥((BigFppfOver.structureSheaf 𝒞 _ hS).obj.obj (op W)))
      (b : cyclicBaseObject 𝒞 hS ⟶ W) => (BigFppfOver.structureSheaf 𝒞 _ hS).obj.map b.op s)) :
    Function.Bijective (fun (s : ↥((BigFppfOver.structureSheaf 𝒞 _ hS).obj.obj (op X)))
      (b : cyclicBaseObject 𝒞 hS ⟶ X) => (BigFppfOver.structureSheaf 𝒞 _ hS).obj.map b.op s) := by
  let 𝒪 := (BigFppfOver.structureSheaf 𝒞 _ hS).obj
  let E : ((cyclicBaseObject 𝒞 hS ⟶ W) → ↥(𝒪.obj (op (cyclicBaseObject 𝒞 hS)))) ≃
      ((cyclicBaseObject 𝒞 hS ⟶ X) → ↥(𝒪.obj (op (cyclicBaseObject 𝒞 hS)))) :=
    { toFun F b := F (b ≫ e.hom)
      invFun G c := G (c ≫ e.inv)
      left_inv F := funext fun c => by simp
      right_inv G := funext fun b => by simp }
  have key : (fun (s : ↥(𝒪.obj (op X))) (b : cyclicBaseObject 𝒞 hS ⟶ X) => 𝒪.map b.op s) =
      E ∘ (fun (s : ↥(𝒪.obj (op W))) (b : cyclicBaseObject 𝒞 hS ⟶ W) => 𝒪.map b.op s) ∘
        (𝒪.map e.inv.op) := by
    funext s b
    change 𝒪.map b.op s = 𝒪.map (b ≫ e.hom).op (𝒪.map e.inv.op s)
    rw [← RingCat.comp_apply, ← Functor.map_comp, ← op_comp, Category.assoc, e.hom_inv_id,
      Category.comp_id]
  rw [key]
  exact E.bijective.comp (h.comp (ConcreteCategory.bijective_of_isIso _))

/-- **The functions on the base of `U^{n+1}` are the functions on its points over `S`**, with
values in `Γ(S, 𝒪_S)`. -/
theorem bijective_structureSheaf_map_cyclicPointwisePi (n : ℕ) :
    Function.Bijective (fun (s : ↥((BigFppfOver.structureSheaf 𝒞 _ hS).obj.obj
        (op ((cyclicPointwise p 𝒞 hS).p.obj
          (∏ᶜ fun _ : Fin (n + 1) => cyclicPointwiseUnitObject p 𝒞 hS)))))
      (b : cyclicBaseObject 𝒞 hS ⟶ (cyclicPointwise p 𝒞 hS).p.obj
        (∏ᶜ fun _ : Fin (n + 1) => cyclicPointwiseUnitObject p 𝒞 hS)) =>
        (BigFppfOver.structureSheaf 𝒞 _ hS).obj.map b.op s) :=
  bijective_structureSheaf_map_of_iso 𝒞 hS (cyclicPointwisePiBaseIso p 𝒞 hS n)
    (Space.bijective_structureSheaf_map_constantGroupSiteObject 𝒞 hS (CyclicPowerGroup p n)
      (contains_cyclicPowerGroupScheme p 𝒞 hS n))

/-- **The base of `U^{n+1}` is affine.** -/
theorem isAffine_cyclicPointwisePi (n : ℕ) :
    IsAffine ((BigFppfOver.toScheme 𝒞 _ hS).obj ((cyclicPointwise p 𝒞 hS).p.obj
      (∏ᶜ fun _ : Fin (n + 1) => cyclicPointwiseUnitObject p 𝒞 hS))) :=
  haveI := Space.isAffine_constantGroupSiteObject 𝒞 hS (CyclicPowerGroup p n)
    (contains_cyclicPowerGroupScheme p 𝒞 hS n)
  IsAffine.of_isIso
    ((BigFppfOver.toScheme 𝒞 _ hS).mapIso (cyclicPointwisePiBaseIso p 𝒞 hS n)).hom

end Stacks.Examples.UnboundedDerivedPushforward
