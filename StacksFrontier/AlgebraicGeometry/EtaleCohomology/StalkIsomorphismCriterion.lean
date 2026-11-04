module

public import StacksFrontier.AlgebraicGeometry.Etale.SupportSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.EtaleStalkFunctor
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stalks at geometric points detect isomorphisms of abelian étale sheaves

Let `B` be a big étale site containing a scheme `X`. A morphism of abelian sheaves on the small
étale site of `X` whose induced map on the stalk at every geometric point of `X` is an
isomorphism is itself an isomorphism.

The proof does not go through a conservative family of abstract points of the site. It shows
directly that such a morphism is locally surjective and locally injective, and the covering
sieves witnessing this are produced from the criterion that a sieve of the small étale site
whose members are jointly surjective on points is covering. The link between a point of the
underlying scheme and a geometric point is `AlgebraicGeometry.GeometricPoint.ofPoint`: the
algebraic closure of the residue field there gives a geometric point lying over it, and a lift of
that geometric point to the object we started from. Germs of sections at that lift then move the
hypothesis about stalks to a statement about sections over an étale neighbourhood.

## Main results

* `AlgebraicGeometry.isLocallySurjective_of_surjective_etaleStalkMap` and
  `AlgebraicGeometry.isLocallyInjective_of_injective_etaleStalkMap` — surjectivity,
  respectively injectivity, on all stalks at geometric points implies local surjectivity,
  respectively local injectivity.
* `AlgebraicGeometry.isIso_of_isIso_etaleStalkMap` — a morphism of abelian étale sheaves which
  is an isomorphism on all stalks at geometric points is an isomorphism.
* `AlgebraicGeometry.isIso_of_bijective_geometricSheafFiber` and
  `AlgebraicGeometry.isIso_iff_forall_bijective_geometricSheafFiber` — the same for sheaves of
  **types**, where the coefficient universe is that of the points and the conservative family of
  `AlgebraicGeometry.isConservativeFamilyOfPoints_geometricSitePoints` therefore applies directly,
  so no local-bijectivity detour is needed.

## Implementation notes

The stalk at a geometric point is the fibre of `AlgebraicGeometry.geometricPointSitePoint`, so
Mathlib's germ calculus for a point of a site applies to it verbatim; that is the content of
`AlgebraicGeometry.etaleStalk_eq_presheafFiber`, and the functor
`AlgebraicGeometry.etaleStalkPresheafFunctor` used to state the hypotheses is that fibre functor
on the nose. The geometric point attached to a point of an étale object lives over the base
through the structure morphism of that object, which is why the hypothesis quantifies over
geometric points of `X` and not of the object.

The coefficient universe `v` is a universe of its own, independent of the universe `u` of
schemes: Mathlib's germ calculus takes the universe of the carriers of the coefficient category
independently of the universe of the points of the site, so all that is asked of `v` is
`UnivLE.{u, v}`, which is what makes the colimits defining the stalks exist. The two universes
therefore need not agree, and the germ calculus is used at a coefficient category which is not
concrete over the universe of the points. That is the reason this is proved from local
bijectivity rather than from `ObjectProperty.IsConservativeFamilyOfPoints`, whose conclusion is
available only when the two universes agree.

## References

* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- The geometric point of `X` attached to a point `x` of an object `V` of the small étale site:
the geometric point of `V` with algebraically closed residue field at `x`, pushed down to `X`
along the structure morphism of `V`. -/
public def geometricPointOfEtalePoint (V : SmallEtale B X hX)
    (x : (SmallEtale.toScheme B X hX).obj V) : GeometricPoint X :=
  (GeometricPoint.ofPoint ((SmallEtale.toScheme B X hX).obj V) x).map (B.inclusion.map V.obj.hom)

/-- The tautological lift of `AlgebraicGeometry.geometricPointOfEtalePoint` to the object it was
built from. -/
public def geometricPointOfEtalePointLift (V : SmallEtale B X hX)
    (x : (SmallEtale.toScheme B X hX).obj V) :
    (geometricPointFiber B X hX (geometricPointOfEtalePoint B X hX V x)).obj V :=
  ⟨(GeometricPoint.ofPoint ((SmallEtale.toScheme B X hX).obj V) x).hom, rfl⟩

/-- The tautological lift hits the point it was built from. -/
public theorem geometricPointOfEtalePointLift_base (V : SmallEtale B X hX)
    (x : (SmallEtale.toScheme B X hX).obj V) :
    (geometricPointOfEtalePointLift B X hX V x).1 default = x :=
  GeometricPoint.ofPoint_liesOver _ x

variable {F G : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{v}}

private instance [UnivLE.{u, v}] :
    PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{v}) :=
  preservesFilteredColimitsOfSize_of_univLE.{v, v, u, u} (forget AddCommGrpCat.{v})

/-- A morphism `f : W ⟶ V` through which the tautological lift at `x` factors exhibits `x` in the
image of `f`. -/
private theorem mem_range_of_lift {V W : SmallEtale B X hX}
    (f : W ⟶ V) (x : (SmallEtale.toScheme B X hX).obj V)
    (q : (GeometricPoint.ofPoint ((SmallEtale.toScheme B X hX).obj V) x).source ⟶
      (SmallEtale.toScheme B X hX).obj W)
    (hq : q ≫ (SmallEtale.toScheme B X hX).map f =
      (geometricPointOfEtalePointLift B X hX V x).1) :
    x ∈ Set.range (B.inclusion.map f.hom.left) := by
  refine ⟨q default, .trans ?_ (geometricPointOfEtalePointLift_base B X hX V x)⟩
  rw [← hq]; rfl

/-- Local surjectivity from surjectivity on all stalks at geometric points: a section over `V`
is, near every point of `V`, the image of a section, because its germ at a geometric point there
is, and germs are computed on étale neighbourhoods. -/
public theorem isLocallySurjective_of_surjective_etaleStalkMap [UnivLE.{u, v}] (α : F ⟶ G)
    (h : ∀ s : GeometricPoint X, Function.Surjective
      ((etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{v}).map α.hom)) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B X hX) α.hom := by
  constructor
  intro V b
  apply SmallEtale.mem_topology_of_jointlySurjective
  intro x
  let s := geometricPointOfEtalePoint B X hX V x
  let Φ := geometricPointSitePoint B X hX s
  let p : Φ.fiber.obj V := geometricPointOfEtalePointLift B X hX V x
  obtain ⟨z, hz⟩ := h s (Φ.toPresheafFiber V p G.obj b)
  obtain ⟨W, y, c, rfl⟩ := Φ.toPresheafFiber_jointly_surjective z
  replace hz : (Φ.presheafFiber.map α.hom) (Φ.toPresheafFiber W y F.obj c) =
      Φ.toPresheafFiber V p G.obj b := hz
  rw [Φ.toPresheafFiber_naturality_apply α.hom] at hz
  let ZW : Φ.fiber.Elements := ⟨W, y⟩
  let ZV : Φ.fiber.Elements := ⟨V, p⟩
  let Z : Φ.fiber.Elements := IsCofiltered.min ZW ZV
  let l : Z ⟶ ZW := IsCofiltered.minToLeft ZW ZV
  let r : Z ⟶ ZV := IsCofiltered.minToRight ZW ZV
  have hZ {Z' : Φ.fiber.Elements} (m : Z ⟶ Z') (d : G.obj.obj (op Z'.1)) :
      Φ.toPresheafFiber Z.1 Z.2 G.obj (G.obj.map m.1.op d) =
        Φ.toPresheafFiber Z'.1 Z'.2 G.obj d := by
    have := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w m.1 Z.2 G.obj) d
    rwa [m.2] at this
  obtain ⟨Y, f, y', hy', heq⟩ :=
    (Φ.toPresheafFiber_eq_iff' Z.1 Z.2 (G.obj.map l.1.op (α.hom.app (op W) c))
      (G.obj.map r.1.op b)).1 ((hZ l _).trans (hz.trans (hZ r b).symm))
  refine ⟨Y, f ≫ r.1, ⟨F.obj.map (f ≫ l.1).op c, ?_⟩, ?_⟩
  · rwa [NatTrans.naturality_apply, op_comp, op_comp, G.obj.map_comp, G.obj.map_comp,
      ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  · have h1 : y'.1 ≫ (SmallEtale.toScheme B X hX).map f = Z.2.1 := congrArg Subtype.val hy'
    have h2 : Z.2.1 ≫ (SmallEtale.toScheme B X hX).map r.1 = p.1 := congrArg Subtype.val r.2
    refine mem_range_of_lift B X hX (f ≫ r.1) x y'.1 ?_
    rw [Functor.map_comp]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans h2)

/-- Local injectivity from injectivity on all stalks at geometric points: two sections over `V`
with the same image agree near every point of `V`, because their germs at a geometric point
there agree, and germs are computed on étale neighbourhoods. -/
public theorem isLocallyInjective_of_injective_etaleStalkMap [UnivLE.{u, v}] (α : F ⟶ G)
    (h : ∀ s : GeometricPoint X, Function.Injective
      ((etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{v}).map α.hom)) :
    Presheaf.IsLocallyInjective (SmallEtale.topology B X hX) α.hom := by
  constructor
  intro V a₁ a₂ ha
  obtain ⟨V⟩ := V
  apply SmallEtale.mem_topology_of_jointlySurjective
  intro x
  let s := geometricPointOfEtalePoint B X hX V x
  let Φ := geometricPointSitePoint B X hX s
  let p : Φ.fiber.obj V := geometricPointOfEtalePointLift B X hX V x
  have hgerm : Φ.toPresheafFiber V p F.obj a₁ = Φ.toPresheafFiber V p F.obj a₂ := by
    refine h s ?_
    show (Φ.presheafFiber.map α.hom) (Φ.toPresheafFiber V p F.obj a₁) =
      (Φ.presheafFiber.map α.hom) (Φ.toPresheafFiber V p F.obj a₂)
    rw [Φ.toPresheafFiber_naturality_apply α.hom, Φ.toPresheafFiber_naturality_apply α.hom]
    exact congrArg (Φ.toPresheafFiber V p G.obj) ha
  obtain ⟨Y, f, y', hy', heq⟩ := (Φ.toPresheafFiber_eq_iff' V p a₁ a₂).1 hgerm
  exact ⟨Y, f, heq, mem_range_of_lift B X hX f x y'.1 (congrArg Subtype.val hy')⟩

/-- **Stacks 03PU**, the isomorphism case for abelian sheaves. A morphism of abelian sheaves on
the small étale site of `X` whose induced map on the stalk at every geometric point of `X` is an
isomorphism is an isomorphism: it is locally bijective, and a locally bijective morphism of
sheaves is invertible. -/
public theorem isIso_of_isIso_etaleStalkMap [UnivLE.{u, v}] (α : F ⟶ G)
    (h : ∀ s : GeometricPoint X,
      IsIso ((etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{v}).map α.hom)) :
    IsIso α := by
  have hb (s : GeometricPoint X) : Function.Bijective
      ((etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{v}).map α.hom) :=
    have := h s
    ConcreteCategory.bijective_of_isIso _
  exact (Sheaf.isLocallyBijective_iff_isIso α).1
    ⟨isLocallyInjective_of_injective_etaleStalkMap B X hX α fun s => (hb s).1,
      isLocallySurjective_of_surjective_etaleStalkMap B X hX α fun s => (hb s).2⟩

/-! ### The criterion for sheaves of types -/

section TypeValued

variable {F' G' : Sheaf (SmallEtale.topology B X hX) (Type u)}

/-- **A morphism of sheaves of types on the small étale site which is bijective on every
geometric fibre is an isomorphism.**

This is the type-valued companion of `AlgebraicGeometry.isIso_of_isIso_etaleStalkMap`, which is
stated at `AddCommGrpCat` coefficients, and of
`AlgebraicGeometry.GeometricPoint.isIso_iff_forall_bijective_stalkFunctor`, which is stated for
Mathlib's `AlgebraicGeometry.Scheme.smallEtaleTopology` rather than for
`AlgebraicGeometry.SmallEtale.topology` of a big étale site.

It needs no local-bijectivity detour: the geometric points of `X` form a conservative family of
points of the small étale site
(`AlgebraicGeometry.isConservativeFamilyOfPoints_geometricSitePoints`), and a conservative family
of points jointly reflects isomorphisms of sheaves of *types* by definition
(`CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectIsomorphisms_type`);
only the passage from bijectivity to invertibility in `Type u`
(`CategoryTheory.isIso_iff_bijective`) is added. -/
@[sga "4 VIII 3.13" "E = X", sga "4 VIII 3.5" "b)", sga "4½ Arcata 2.3.2" "partial"]
public theorem isIso_of_bijective_geometricSheafFiber (α : F' ⟶ G')
    (h : ∀ x : X, Function.Bijective
      (((geometricPointSitePoint B X hX (GeometricPoint.ofPoint X x)).sheafFiber
        (A := Type u)).map α)) :
    IsIso α := by
  have : ∀ Φ : (geometricSitePoints B X hX).FullSubcategory,
      IsIso ((Φ.obj.sheafFiber (A := Type u)).map α) := by
    intro Φ
    obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ _).1 Φ.property
    rw [← hx]
    exact (isIso_iff_bijective _).2 (h x)
  exact (isConservativeFamilyOfPoints_geometricSitePoints B X hX).jointlyReflectIsomorphisms_type
    |>.isIso α

/-- **A morphism of sheaves of types on the small étale site is an isomorphism exactly when it is
bijective on every geometric fibre.** -/
public theorem isIso_iff_forall_bijective_geometricSheafFiber (α : F' ⟶ G') :
    IsIso α ↔ ∀ x : X, Function.Bijective
      (((geometricPointSitePoint B X hX (GeometricPoint.ofPoint X x)).sheafFiber
        (A := Type u)).map α) :=
  ⟨fun _ _ => (isIso_iff_bijective _).1 inferInstance,
    isIso_of_bijective_geometricSheafFiber B X hX α⟩

end TypeValued

end AlgebraicGeometry

end
