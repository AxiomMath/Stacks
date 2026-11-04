module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleTopos
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall

/-!
# A geometric point of the spectrum of a field is a conservative point

A family of points of a site is *conservative* when the fibre functors it defines jointly
reflect isomorphisms of sheaves.  Over the spectrum of a field a single geometric point
suffices: a morphism of sheaves on the small étale site of `Spec K` which is bijective on the
stalk at one geometric point is an isomorphism.

The criterion of SGA 4 IV 6.5 reduces this to a statement about covering sieves, and that
statement splits into two halves which are proved here separately.  For an arbitrary base
`S`, a sieve on an object of the small étale site of `S` whose members are jointly surjective
on points is a covering sieve: the small étale precoverage is the étale precoverage of schemes
comapped along the canonical functor to schemes, so joint surjectivity is literally the
covering condition.  Over a field, every point of an object `X` of the site is the image of a
lift of the geometric point, because `X` is étale over `Spec K`, the residue field of the
geometric point is separably closed and the spectrum of a field has one point.  Together, a
sieve which lifts every lift of the geometric point is jointly surjective, hence covering.

## Main definitions

Sheafification of presheaves of sets in the universe of the schemes on the small étale site of
`S` is `AlgebraicGeometry.hasSheafify_smallEtaleTopology_type`, imported from
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints`.

## Main results

* `AlgebraicGeometry.SmallEtale.precoverage_eq_comap_toScheme` — the precoverage of the small
  étale site of `S` is the étale precoverage of schemes, comapped along the canonical functor
  to schemes.
* `AlgebraicGeometry.SmallEtale.mem_precoverage_of_jointly_surjective` and
  `AlgebraicGeometry.SmallEtale.mem_topology_of_jointly_surjective` — a presieve, resp. a
  sieve, whose members are jointly surjective on points is covering.
* `AlgebraicGeometry.exists_geometricPointFiber_apply_eq` — over a field, every point of an
  object of the small étale site is the image of a lift of the geometric point.
* `AlgebraicGeometry.isConservativeFamilyOfPoints_geometricPointSitePoint` — over a field, one
  geometric point is a conservative family of points of the small étale site, so by
  `AlgebraicGeometry.hasEnoughPoints_smallEtale_topology` that site has enough points.
* `AlgebraicGeometry.isIso_of_isIso_sheafFiber_map` — consequently a morphism of sheaves of
  sets on the small étale site of a field which is an isomorphism on the stalk at a geometric
  point is an isomorphism.

## Implementation notes

The conservativity statement is the hypothesis under which the stalk functor of
[Stacks, Tag 03QT] is an equivalence onto continuous Galois sets, and it replaces the
descent computation of the sections of a sheaf over a finite separable extension: a morphism
constructed from the stalk may be recognised as an isomorphism one point at a time.  No
declaration here carries the tag 03QT.

## References

* [Stacks Project, Tag 00YK](https://stacks.math.columbia.edu/tag/00YK)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 03QT](https://stacks.math.columbia.edu/tag/03QT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The big étale category over `S` is essentially small at the universe of its schemes,
because the cutoff category of schemes is and a slice of an essentially small category is. -/
instance essentiallySmall_bigEtaleOver : EssentiallySmall.{u} (BigEtaleOver B S hS) :=
  have := essentiallySmall_schemeBelow B.cutoff
  inferInstanceAs (EssentiallySmall.{u} (CostructuredArrow (Functor.id _) _))

-- NO `HasSheafify (SmallEtale.topology B S hS) (Type u)` INSTANCE HERE. The one that used to
-- sit on this line had the same namespace, the same variables, the same type and the same proof
-- term as `AlgebraicGeometry.hasSheafify_smallEtaleTopology_type`
-- (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/EnoughGeometricPoints.lean`:87); both were
-- plain global `instance`s, so they competed in instance search. That one is imported now.

namespace SmallEtale

/-- The precoverage of the small étale site of `S` is the étale precoverage of schemes,
comapped along the canonical functor to schemes. -/
theorem precoverage_eq_comap_toScheme :
    precoverage B S hS = Scheme.etalePrecoverage.comap (toScheme B S hS) := by
  have h₁ : precoverage B S hS
      = (BigEtaleOver.precoverage B S hS).comap (inclusion B S hS) :=
    smallEtale_precoverage_eq_comap B ⟨S, hS⟩
  have h₂ : BigEtaleOver.precoverage B S hS
      = B.precoverage.comap (Over.forget (B.obj S hS)) :=
    bigEtaleOver_precoverage_eq_comap B S hS
  have h₃ : B.precoverage = Scheme.etalePrecoverage.comap B.inclusion :=
    bigEtalePrecoverage_eq_comap B
  rw [h₁, h₂, h₃, ← Precoverage.comap_comp, ← Precoverage.comap_comp]
  rfl

/-- A presieve on an object of the small étale site of `S` belongs to the small étale
precoverage as soon as the underlying morphisms of schemes are jointly surjective. -/
theorem mem_precoverage_of_jointly_surjective {X : SmallEtale B S hS} {R : Presieve X}
    (h : ∀ x : (toScheme B S hS).obj X, ∃ (Y : SmallEtale B S hS) (g : Y ⟶ X),
      R g ∧ x ∈ Set.range ((toScheme B S hS).map g)) :
    R ∈ precoverage B S hS X := by
  have hetale : Scheme.etalePrecoverage.{u} = Scheme.precoverage @Etale := rfl
  rw [precoverage_eq_comap_toScheme, Precoverage.mem_comap_iff, hetale]
  refine ⟨?_, ?_⟩
  · rw [Presieve.mem_comap_jointlySurjectivePrecoverage_iff]
    intro x
    obtain ⟨Y, g, hg, hx⟩ := h x
    refine ⟨(toScheme B S hS).obj Y, (toScheme B S hS).map g, Presieve.map_map hg, ?_⟩
    exact hx
  · intro Y' f hf
    obtain ⟨Z, hZ, g, -, heq⟩ := Presieve.map_iff.mp hf
    subst hZ
    rw [eqToHom_refl, Category.id_comp] at heq
    rw [← heq]
    exact etale_toScheme_map g

/-- A sieve on an object of the small étale site of `S` is a covering sieve as soon as the
underlying morphisms of schemes of its members are jointly surjective. -/
theorem mem_topology_of_jointly_surjective {X : SmallEtale B S hS} {R : Sieve X}
    (h : ∀ x : (toScheme B S hS).obj X, ∃ (Y : SmallEtale B S hS) (g : Y ⟶ X),
      R g ∧ x ∈ Set.range ((toScheme B S hS).map g)) :
    R ∈ topology B S hS X := by
  have := Precoverage.generate_mem_toGrothendieck
    (mem_precoverage_of_jointly_surjective B S hS h)
  rwa [Sieve.generate_sieve] at this

end SmallEtale

section Field

variable (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (s : GeometricPoint (Spec (.of K)))

/-- Over a field, every point of an object of the small étale site is the image of a lift of
a geometric point: the object is étale over `Spec K`, the spectrum of a field has a single
point and the residue field of a geometric point is separably closed. -/
theorem exists_geometricPointFiber_apply_eq (X : SmallEtale B (Spec (.of K)) hK)
    (x : (SmallEtale.toScheme B (Spec (.of K)) hK).obj X) :
    ∃ p : (geometricPointFiber B (Spec (.of K)) hK s).obj X, p.1 default = x := by
  have : Subsingleton ↥(B.inclusion.obj (B.obj (Spec (.of K)) hK)) :=
    inferInstanceAs (Subsingleton ↥(Spec (CommRingCat.of K)))
  obtain ⟨l, hl, hld⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
    (B.inclusion.map X.obj.hom) s.hom x (Subsingleton.elim _ _)
  exact ⟨⟨l, hl⟩, hld⟩

/-- **A geometric point of the spectrum of a field is a conservative point.**  The fibre
functor of one geometric point of `Spec K` reflects isomorphisms of sheaves of sets on the
small étale site: a sieve which lifts every lift of the geometric point is jointly surjective
on points, hence covering. -/
theorem isConservativeFamilyOfPoints_geometricPointSitePoint :
    (ObjectProperty.singleton
      (geometricPointSitePoint B (Spec (.of K)) hK s)).IsConservativeFamilyOfPoints := by
  refine ObjectProperty.IsConservativeFamilyOfPoints.mk' fun {X} R hR ↦ ?_
  specialize hR ⟨_, ObjectProperty.ofObj_apply _ ()⟩
  refine SmallEtale.mem_topology_of_jointly_surjective B _ hK fun x ↦ ?_
  obtain ⟨p, hp⟩ := exists_geometricPointFiber_apply_eq B K hK s X x
  obtain ⟨Y, g, hg, q, hq⟩ := hR p
  refine ⟨Y, g, hg, q.1 default, ?_⟩
  have hqp : q.1 ≫ (SmallEtale.toScheme B (Spec (.of K)) hK).map g = p.1 :=
    congrArg Subtype.val hq
  rw [← hp, ← hqp]
  simp

include s in
/-- The small étale site of the spectrum of a field has enough points: one geometric point
is a conservative family. -/
theorem hasEnoughPoints_smallEtale_topology :
    GrothendieckTopology.HasEnoughPoints.{u} (SmallEtale.topology B (Spec (.of K)) hK) :=
  ⟨⟨ObjectProperty.singleton (geometricPointSitePoint B (Spec (.of K)) hK s), inferInstance,
    isConservativeFamilyOfPoints_geometricPointSitePoint B K hK s⟩⟩

/-- **Stalkwise isomorphisms of étale sheaves over a field.**  A morphism of sheaves of sets
on the small étale site of `Spec K` which is an isomorphism on the stalk at a geometric point
is an isomorphism. -/
theorem isIso_of_isIso_sheafFiber_map
    {F G : smallEtaleTopos.{u, u} B (Spec (.of K)) hK} (φ : F ⟶ G)
    (hφ : IsIso ((geometricPointSitePoint B (Spec (.of K)) hK s).sheafFiber
      (A := Type u) |>.map φ)) :
    IsIso φ := by
  have hall : ∀ Φ : (ObjectProperty.singleton
      (geometricPointSitePoint B (Spec (.of K)) hK s)).FullSubcategory,
      IsIso ((Φ.obj.sheafFiber (A := Type u)).map φ) := by
    intro Φ
    obtain ⟨-, hΦ⟩ := (ObjectProperty.ofObj_iff _ _).mp Φ.property
    rw [← hΦ]
    exact hφ
  exact (isConservativeFamilyOfPoints_geometricPointSitePoint B K hK
    s).jointlyReflectIsomorphisms_type.isIso φ

end Field

end AlgebraicGeometry

end
