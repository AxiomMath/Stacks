module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.SpecializationLifting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.VanishingCyclesFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.ConstantGerm
public import StacksFrontier.AlgebraicGeometry.Properties.FiniteIrreducibleComponents

/-!
# Germs of a section along a specialization inside an étale neighbourhood

Let `U` be an object of the small étale site of a scheme `S` and let `s` be a geometric point of
the scheme `U`. The strict henselization of `U` at `s` is also the strict henselization of `S` at
the image `s̄` of `s`: the canonical morphism of strict henselizations induced by the structure
morphism of `U`, composed with the factorization of the strict henselization of `S` at `s̄`
through the tautologically pointed neighbourhood `U`, is the structure morphism of the strict
henselization of `U`. Consequently a geometric point `t` of `U` over a generization of the image
of `s` gives a genuine geometric specialization of `s̄` whose associated étale neighbourhood of
`U` is the tautological one at `t`, so for a family of sections over `U` the germ maps at `s` and
at `t` differ by a specialization map on stalks.

The last result turns a property of geometric points of a scheme which is invariant along
specializations into an open subset, whenever every quasi-compact open of the scheme has finitely
many irreducible components.

## Main results

* `AlgebraicGeometry.strictHenselizationSquareMap_comp_strictHenselizationEtaleFactor` — the
  strict henselization of an étale scheme at a geometric point is the strict henselization of the
  base at the image point, compatibly with the structure morphisms.
* `AlgebraicGeometry.bijective_germ_iff_of_specializes` — if all specialization maps on stalks of
  a presheaf are bijective, the germ map of a family of sections over `U` is bijective at a
  geometric point of `U` exactly when it is bijective at any generization of it.
* `AlgebraicGeometry.bijective_germ_lift_iff` — a lift of a geometric point of `S` to `U` is a
  geometric point of the scheme `U`, with the same germ map.
* `AlgebraicGeometry.exists_opens_of_geometricPoint_specialization_invariant` — a
  specialization-invariant property of geometric points cuts out an open subset.

## References

* [Stacks Project, Tag 0GJ5](https://stacks.math.columbia.edu/tag/0GJ5)
* [Stacks Project, Section 0GJ2](https://stacks.math.columbia.edu/tag/0GJ2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The strict henselization of an object `U` of the small étale site of `S` at a geometric point
`s` is the strict henselization of `S` at the image of `s`: the canonical morphism of strict
henselizations, followed by the factorization through the tautologically pointed neighbourhood
`U`, is the structure morphism of the strict henselization of `U`. -/
public theorem strictHenselizationSquareMap_comp_strictHenselizationEtaleFactor
    (U : SmallEtale B S hS) (s : GeometricPoint U.obj.left.1) :
    strictHenselizationSquareMap B U.obj.left.property hS (B.inclusion.map U.obj.hom) s ≫
        strictHenselizationEtaleFactor B S hS (s.map (B.inclusion.map U.obj.hom)) U
          ⟨s.hom, rfl⟩ =
      strictHenselizationToBase B U.obj.left.1 U.obj.left.property s := by
  have hetale : Etale (B.inclusion.map U.obj.hom) := U.property
  have hp : (geometricPointToStrictHenselization B U.obj.left.1 U.obj.left.property s)
        (closedPoint s.residueField) =
      closedPoint (CommRingCat.of ↥(etaleLocalRing B U.obj.left.1 U.obj.left.property s)) := by
    have : IsLocalHom (CommRingCat.ofHom
        (structureSheafStalkToGeometricField B U.obj.left.1 U.obj.left.property s)).hom :=
      isLocalHom_structureSheafStalkToGeometricField B U.obj.left.1 U.obj.left.property s
    exact Spec_closedPoint
  have huniq := exists_lift_of_strictlyHenselian_of_weaklyEtale
    (B.inclusion.map U.obj.hom)
    (strictHenselizationToBase B U.obj.left.1 U.obj.left.property s ≫
      B.inclusion.map U.obj.hom)
    (geometricPointToStrictHenselization B U.obj.left.1 U.obj.left.property s) hp s.hom
    (by rw [← Category.assoc,
      geometricPointToStrictHenselization_comp B U.obj.left.1 U.obj.left.property s])
  refine huniq.unique ⟨?_, ?_⟩
    ⟨rfl, geometricPointToStrictHenselization_comp B U.obj.left.1 U.obj.left.property s⟩
  · rw [Category.assoc, strictHenselizationEtaleFactor_comp]
    exact strictHenselizationSquareMap_comp B U.obj.left.property hS
      (B.inclusion.map U.obj.hom) s
  · rw [← Category.assoc, geometricPointToStrictHenselization_strictHenselizationSquareMap,
      geometricPointToStrictHenselization_comp_strictHenselizationEtaleFactor]

/-- The germ map of a family of sections over `U` depends only on the geometric point of `S` and
on the lift of it to `U`, not on how the two are presented. -/
public theorem bijective_germ_congr (U : SmallEtale B S hS)
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ Type (u + 1)) {A : Type (u + 1)} (z : A → P.obj (op U))
    {s s' : GeometricPoint S} (x : (geometricPointFiber B S hS s).obj U)
    (x' : (geometricPointFiber B S hS s').obj U) (h : s' = s) (hx : HEq x' x) :
    Function.Bijective (fun a : A =>
        (geometricPointSitePoint B S hS s').toPresheafFiber U x' P (z a)) ↔
      Function.Bijective (fun a : A =>
        (geometricPointSitePoint B S hS s).toPresheafFiber U x P (z a)) := by
  subst h
  have hx' := eq_of_heq hx
  subst hx'
  rfl

/-- A lift to `U` of a geometric point `s` of `S` is the same datum as a geometric point of the
scheme `U` with image `s`, so the two germ maps of a family of sections over `U` agree. -/
public theorem bijective_germ_lift_iff (U : SmallEtale B S hS)
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ Type (u + 1)) {A : Type (u + 1)} (z : A → P.obj (op U))
    (s : GeometricPoint S) (x : (geometricPointFiber B S hS s).obj U) :
    Function.Bijective (fun a : A => (geometricPointSitePoint B S hS
        ((⟨s.residueField, x.1⟩ : GeometricPoint U.obj.left.1).map
          (B.inclusion.map U.obj.hom))).toPresheafFiber U ⟨x.1, rfl⟩ P (z a)) ↔
      Function.Bijective (fun a : A =>
        (geometricPointSitePoint B S hS s).toPresheafFiber U x P (z a)) :=
  bijective_germ_congr B S hS U P z
    (s' := (⟨s.residueField, x.1⟩ : GeometricPoint U.obj.left.1).map
      (B.inclusion.map U.obj.hom)) x ⟨x.1, rfl⟩
    (congrArg (fun m => (⟨s.residueField, m⟩ : GeometricPoint S)) x.2)
    ((Subtype.heq_iff_coe_eq fun v => Iff.of_eq (congrArg
      (fun m => v ≫ B.inclusion.map U.obj.hom = m) x.2)).2 rfl)

/-- If all specialization maps on stalks of a presheaf of sets are bijective, then the map
sending an index to the germ over `U` of the corresponding section is bijective at a geometric
point `s` of `U` exactly when it is bijective at a geometric point `t` of `U` lying over a
generization of the image of `s`. -/
public theorem bijective_germ_iff_of_specializes (U : SmallEtale B S hS)
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ Type (u + 1))
    (hsp : ∀ (r : GeometricPoint S) (σ : GeometricSpecialization B S hS r),
      Function.Bijective (specializationMapOnStalks σ P))
    {A : Type (u + 1)} (z : A → P.obj (op U)) (s t : GeometricPoint U.obj.left.1)
    (hts : t.hom default ⤳ s.hom default) :
    Function.Bijective (fun a : A => (geometricPointSitePoint B S hS
        (s.map (B.inclusion.map U.obj.hom))).toPresheafFiber U ⟨s.hom, rfl⟩ P (z a)) ↔
      Function.Bijective (fun a : A => (geometricPointSitePoint B S hS
        (t.map (B.inclusion.map U.obj.hom))).toPresheafFiber U ⟨t.hom, rfl⟩ P (z a)) := by
  obtain ⟨l, hl, -⟩ := exists_lift_toStrictHenselization_of_specializes B U.obj.left.1
    U.obj.left.property (t.hom default) (s.hom default) hts t s rfl rfl
  have hbase := strictHenselizationSquareMap_comp B U.obj.left.property hS
    (B.inclusion.map U.obj.hom) s
  have hfactor := strictHenselizationSquareMap_comp_strictHenselizationEtaleFactor B S hS U s
  let σ : GeometricSpecialization B S hS (s.map (B.inclusion.map U.obj.hom)) :=
    { target := t.map (B.inclusion.map U.obj.hom)
      lift := l ≫ strictHenselizationSquareMap B U.obj.left.property hS
        (B.inclusion.map U.obj.hom) s
      lift_comp := by
        rw [Category.assoc, hbase, ← Category.assoc, hl, GeometricPoint.map_hom] }
  have hσ : (specializationFiberHom σ).app U ⟨s.hom, rfl⟩ = ⟨t.hom, rfl⟩ := by
    apply Subtype.ext
    rw [specializationFiberHom_app_val]
    show (l ≫ strictHenselizationSquareMap B U.obj.left.property hS
      (B.inclusion.map U.obj.hom) s) ≫ _ = t.hom
    rw [Category.assoc, hfactor, hl]
  have hcomp : (fun a : A => (geometricPointSitePoint B S hS
        (t.map (B.inclusion.map U.obj.hom))).toPresheafFiber U ⟨t.hom, rfl⟩ P (z a)) =
      (fun y => specializationMapOnStalks σ P y) ∘
        (fun a : A => (geometricPointSitePoint B S hS
          (s.map (B.inclusion.map U.obj.hom))).toPresheafFiber U ⟨s.hom, rfl⟩ P (z a)) := by
    refine funext fun a => ?_
    refine Eq.symm (Eq.trans (specializationMapOnStalks_ι σ P
      (Functor.elementsMk (geometricPointFiber B S hS
        (s.map (B.inclusion.map U.obj.hom))) U ⟨s.hom, rfl⟩) (z a)) ?_)
    exact congrArg (fun y : (geometricPointFiber B S hS
        (t.map (B.inclusion.map U.obj.hom))).obj U =>
      colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS
        (t.map (B.inclusion.map U.obj.hom)))).op ⋙ P)
        (op (Functor.elementsMk (geometricPointFiber B S hS
          (t.map (B.inclusion.map U.obj.hom))) U y)) (z a)) hσ
  rw [hcomp]
  exact (Function.Bijective.of_comp_iff'
    (hsp (s.map (B.inclusion.map U.obj.hom)) σ) _).symm

/-- A property of geometric points of a scheme which is invariant along specializations cuts out
an open subset, provided every quasi-compact open of the scheme has finitely many irreducible
components. -/
public theorem exists_opens_of_geometricPoint_specialization_invariant {X : Scheme.{u}}
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (P : GeometricPoint X → Prop)
    (hP : ∀ s t : GeometricPoint X, t.hom default ⤳ s.hom default → (P s ↔ P t)) :
    ∃ E : X.Opens, ∀ s : GeometricPoint X, s.hom default ∈ E ↔ P s := by
  have hE : ∀ s : GeometricPoint X,
      s.hom default ∈ {x : X | ∃ r : GeometricPoint X, r.hom default = x ∧ P r} ↔ P s := by
    intro s
    refine ⟨?_, fun hs => ⟨s, rfl, hs⟩⟩
    rintro ⟨r, hr, hPr⟩
    exact (hP r s (by rw [hr])).mp hPr
  have hiff : ∀ y w : X, y ⤳ w →
      (P (GeometricPoint.ofPoint X w) ↔ P (GeometricPoint.ofPoint X y)) := by
    intro y w hyw
    refine hP (GeometricPoint.ofPoint X w) (GeometricPoint.ofPoint X y) ?_
    rw [GeometricPoint.ofPoint_liesOver, GeometricPoint.ofPoint_liesOver]
    exact hyw
  have key : ∀ y : X, y ∈ {x : X | ∃ r : GeometricPoint X, r.hom default = x ∧ P r} ↔
      P (GeometricPoint.ofPoint X y) := fun y => by
    have := hE (GeometricPoint.ofPoint X y)
    rwa [GeometricPoint.ofPoint_liesOver] at this
  have hspec : StableUnderSpecialization
      {x : X | ∃ r : GeometricPoint X, r.hom default = x ∧ P r} :=
    fun y w hyw hy => (key w).mpr ((hiff y w hyw).mpr ((key y).mp hy))
  have hgen : StableUnderGeneralization
      {x : X | ∃ r : GeometricPoint X, r.hom default = x ∧ P r} :=
    fun y w hyw hw => (key w).mpr ((hiff w y hyw).mp ((key y).mp hw))
  exact ⟨⟨_, isOpen_of_stableUnderSpecialization_of_stableUnderGeneralization hX hspec hgen⟩, hE⟩

end AlgebraicGeometry

end
