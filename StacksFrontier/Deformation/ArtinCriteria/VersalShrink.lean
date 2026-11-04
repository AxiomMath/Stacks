module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigSurjective
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.MaximalSlice
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.FibreProducts
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximationSupplement
public import StacksFrontier.Deformation.Artin.Versality.Openness
import all StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.MaximalSlice
import all StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation

/-!
# Shrinking the base of a versal object

Let a category fibred in groupoids over a bounded big fppf site have openness of
versality, and let one of its objects be of finite type over a locally Noetherian
base and versal at a single finite-type point `u₀`.  Shrinking the base to an
affine open neighbourhood of `u₀` inside the open on which versality persists,
and pulling the object back along a strongly Cartesian arrow over that open
immersion, produces an object which is still of finite type and quasi-compact
over the base, still lies over `u₀`, and is versal at *every* finite-type point
of its base.  This is the step of Stacks 07XY reading "by openness of versality
we may shrink `U` and assume that `x` is versal at every finite type point
of `U`".

## Main results

* `Deformation.Artin.exists_shrink_versal_everywhere` is the shrinking step.

## Implementation notes

The mathematical content is that versality at a point is unchanged by restricting
along a strongly Cartesian arrow lying over an open immersion.  This is proved by
rewriting versality as an infinitesimal lifting property at a chosen residue-field
point of the base — a form which refers to no canonical presentation of the local
ring — and then observing two things about that form: a morphism from the spectrum
of an Artinian local algebra whose closed point lands in an open factors through
that open, and the lifting property is insensitive to a change of residue field.
The second is needed because an open immersion identifies the residue field at a
point of the open with the residue field at its image only up to the canonical
isomorphism of residue fields, not on the nose.

No option override is used.  The definitions this development must see through are
named instead: the change-of-residue-field functor on Artinian local algebras and
the slice functor `CategoryTheory.Over.post` carry `attribute
[local implicit_reducible]` where they are first needed.  For the same reason the
`Algebra` instances of the lifting property are passed by name rather than found
by instance search: the canonical residue-field algebra of a point and the
instance synthesized from `[CommRing Λ] [Field k]` agree only up to unfolding.

## References

* [Stacks Project, Tag 07XY](https://stacks.math.columbia.edu/tag/07XY)
* [Stacks Project, Tag 07XQ](https://stacks.math.columbia.edu/tag/07XQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v w u₁ v₁ u₂ v₂ u₃ v₃

/-- A strongly Cartesian arrow over a monomorphism is a monomorphism. -/
private theorem mono_of_stronglyCartesian
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (p : C ⥤ D)
    {x y : C} (r : x ⟶ y) [p.IsStronglyCartesian (p.map r) r]
    [Mono (p.map r)] : Mono r := by
  constructor
  intro z a b h
  have hab : p.map a = p.map b := (cancel_mono (p.map r)).mp (by
    simpa only [← Functor.map_comp] using congrArg p.map h)
  have : p.IsHomLift (p.map a) b := by
    rw [hab]
    infer_instance
  exact Functor.IsStronglyCartesian.ext p (p.map r) r (p.map a) h

/-- A morphism out of the spectrum of a local ring whose closed point lands in
the image of an open immersion factors through that open immersion. -/
private theorem exists_lift_of_closedPoint_mem
    {R : Type u} [CommRing R] [IsLocalRing R] {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (a : Spec (.of R) ⟶ Y)
    (ha : a (IsLocalRing.closedPoint R) ∈ Set.range j) :
    ∃ b : Spec (.of R) ⟶ X, b ≫ j = a := by
  have hsub : Set.range a ⊆ Set.range j := by
    simpa using AlgebraicGeometry.FormalSpace.range_subset_of_closedPoint_mem a j.opensRange ha
  exact ⟨IsOpenImmersion.lift j a hsub, IsOpenImmersion.lift_fac _ _ _⟩

/-! ### The infinitesimal lifting property at a residue-field point -/

-- The change-of-residue-field functor on Artinian local algebras is a plain `def`, so the
-- goals below mentioning one of its values are not type-correct at `implicit` transparency.
-- Naming it here is what lets `simp only` and instance search see through exactly it.
attribute [local implicit_reducible] artinianChangeResidueField

/-- The infinitesimal lifting property of `x` along a chosen residue-field
point `c` of its base, stated without reference to the canonical presentation
of the local ring. -/
private abbrev infinitesimalLiftingAt
    {S : Scheme.{u}} {X : Type v} [Category.{w} X] (q : X ⥤ Over S)
    (x : X) {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (c : Spec (.of k) ⟶ (q.obj x).left) : Prop :=
  ∀ (A B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (f : B ⟶ A), Function.Surjective f.hom →
    ∀ (y z : X)
      (hy : q.obj y = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ))
      (hz : q.obj z = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ))
      (i : y ⟶ z),
      eqToHom (congrArg Over.left hy).symm ≫ (q.map i).left ≫
        eqToHom (congrArg Over.left hz) = Spec.map (CommRingCat.ofHom f.hom.toRingHom) →
      ∀ (a : y ⟶ x),
        Spec.map (CommRingCat.ofHom (residueMap A)) ≫
          eqToHom (congrArg Over.left hy).symm ≫ (q.map a).left = c →
        ∃ b : z ⟶ x, i ≫ b = a

/-- The infinitesimal lifting property is insensitive to a change of residue
field. -/
private theorem infinitesimalLiftingAt_of_residueEquiv
    {S : Scheme.{u}} {X : Type v} [Category.{w} X] (q : X ⥤ Over S)
    (x : X) {Λ k k' : Type u} [CommRing Λ] [Field k] [Field k']
    [Algebra Λ k] [Algebra Λ k'] (e : k ≃ₐ[Λ] k')
    (iΛ : Spec (.of Λ) ⟶ S) (c' : Spec (.of k') ⟶ (q.obj x).left)
    (h : infinitesimalLiftingAt q x iΛ c') :
    infinitesimalLiftingAt q x iΛ
      (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ c') := by
  intro A B f hf y z hy hz i hi a ha
  apply h ((artinianChangeResidueField e).obj A) ((artinianChangeResidueField e).obj B)
    ((artinianChangeResidueField e).map f) hf y z hy hz i hi a
  have he' : CommRingCat.ofHom e.symm.toRingHom ≫ CommRingCat.ofHom e.toRingHom =
      𝟙 (CommRingCat.of k') := by
    ext t
    exact e.apply_symm_apply t
  have he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom e.symm.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, he', Spec.map_id]
  calc
    _ = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom (residueMap A)) ≫
          eqToHom (congrArg Over.left hy).symm ≫ (q.map a).left) := by
      rw [← Spec.map_comp_assoc]
      rfl
    _ = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ c') := congrArg _ ha
    _ = c' := by rw [← Category.assoc, he, Category.id_comp]

/-- Two spellings of a residue-field point give the same lifting property. -/
private theorem infinitesimalLiftingAt_residueEquiv_iff
    {S : Scheme.{u}} {X : Type v} [Category.{w} X] (q : X ⥤ Over S)
    (x : X) {Λ k k' : Type u} [CommRing Λ] [Field k] [Field k']
    [algk : Algebra Λ k] [algk' : Algebra Λ k'] (e : k ≃ₐ[Λ] k')
    (iΛ : Spec (.of Λ) ⟶ S) (c : Spec (.of k) ⟶ (q.obj x).left) :
    infinitesimalLiftingAt q x iΛ c ↔
      infinitesimalLiftingAt q x iΛ (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ c) := by
  refine ⟨infinitesimalLiftingAt_of_residueEquiv q x e.symm iΛ c, fun h => ?_⟩
  have he : CommRingCat.ofHom e.toRingHom ≫ CommRingCat.ofHom e.symm.toRingHom =
      𝟙 (CommRingCat.of k) := by
    ext t
    exact e.symm_apply_apply t
  simpa only [← Spec.map_comp_assoc, he, Spec.map_id, Category.id_comp] using
    infinitesimalLiftingAt_of_residueEquiv q x e iΛ _ h

/-- An arrow whose image factors through a strongly Cartesian arrow's base
factors through that arrow. -/
private theorem exists_factor_of_image_factor
    {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (p : C ⥤ D) (F : D ⥤ E) [F.Full] [F.Faithful]
    {x x' y : C} (r : x' ⟶ x)
    [p.IsStronglyCartesian (p.map r) r]
    (a : y ⟶ x) (g : F.obj (p.obj y) ⟶ F.obj (p.obj x'))
    (h : F.map (p.map a) = g ≫ F.map (p.map r)) :
    ∃ b : y ⟶ x', b ≫ r = a := by
  have h' : F.preimage g ≫ p.map r = p.map a := by
    apply F.map_injective
    simpa only [Functor.map_comp, Functor.map_preimage] using h.symm
  exact ⟨Functor.IsStronglyCartesian.map p (p.map r) r h'.symm a,
    Functor.IsStronglyCartesian.fac p (p.map r) r h'.symm a⟩

/-- An arrow out of an object whose base is the spectrum of a local ring
factors through an open-immersion arrow once its closed point does. -/
public theorem exists_factor_of_closedPoint_mem
    (B : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    {x' x y : X} (r : x' ⟶ x)
    [p.IsStronglyCartesian (p.map r) r]
    [IsOpenImmersion (((p ⋙ Over.post B.inclusion).map r).left)]
    {R : Type u} [CommRing R] [IsLocalRing R]
    (e : Spec (.of R) ≅ ((p ⋙ Over.post B.inclusion).obj y).left)
    (a : y ⟶ x)
    (ha : (e.hom ≫ ((p ⋙ Over.post B.inclusion).map a).left)
      (IsLocalRing.closedPoint R) ∈
        Set.range (((p ⋙ Over.post B.inclusion).map r).left)) :
    ∃ b : y ⟶ x', b ≫ r = a := by
  let q : X ⥤ Over S := p ⋙ Over.post B.inclusion
  obtain ⟨g, hg⟩ := exists_lift_of_closedPoint_mem (q.map r).left
    (e.hom ≫ (q.map a).left) ha
  let g' : q.obj y ⟶ q.obj x' := Over.homMk (e.inv ≫ g) (by
    rw [← Over.w (q.map r), Category.assoc, ← Category.assoc g, hg, Category.assoc,
      Iso.inv_hom_id_assoc, Over.w])
  apply exists_factor_of_image_factor p (Over.post B.inclusion) r a g'
  apply Over.OverMorphism.ext
  show (q.map a).left = (e.inv ≫ g) ≫ (q.map r).left
  rw [Category.assoc, hg, Iso.inv_hom_id_assoc]

/-- The closed point of the spectrum of an Artinian local algebra is the image
of the closed point of its residue field. -/
private theorem residueMap_closedPoint {Λ k : Type u} [CommRing Λ] [Field k]
    [Algebra Λ k] (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    (Spec.map (CommRingCat.ofHom (residueMap A)))
      (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint A := by
  have : IsLocalHom (residueMap A) := by
    dsimp only [residueMap]
    infer_instance
  exact Spec_closedPoint

/-- Infinitesimal lifting is unchanged by restricting along an open-immersion
strongly Cartesian arrow. -/
private theorem infinitesimalLiftingAt_open_iff
    (B : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    {x' x : X} (r : x' ⟶ x)
    [p.IsStronglyCartesian (p.map r) r]
    [IsOpenImmersion (((p ⋙ Over.post B.inclusion).map r).left)]
    {Λ k : Type u} [CommRing Λ] [Field k] [algΛk : Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    (c : Spec (.of k) ⟶ ((p ⋙ Over.post B.inclusion).obj x').left) :
    infinitesimalLiftingAt (p ⋙ Over.post B.inclusion) x' iΛ c ↔
      infinitesimalLiftingAt (p ⋙ Over.post B.inclusion) x iΛ
        (c ≫ ((p ⋙ Over.post B.inclusion).map r).left) := by
  let q : X ⥤ Over S := p ⋙ Over.post B.inclusion
  have : Mono (q.map r).left := inferInstanceAs
    (Mono (((p ⋙ Over.post B.inclusion).map r).left))
  have : Mono ((Over.post B.inclusion).map (p.map r)) :=
    Functor.mono_of_mono_map (Over.forget S) this
  have : Mono (p.map r) := Functor.mono_of_mono_map (Over.post B.inclusion) inferInstance
  have : Mono r := mono_of_stronglyCartesian p r
  constructor
  · intro h A C f hf y z hy hz i hi a ha
    let ey := eqToIso (congrArg Over.left hy).symm
    have ha' : (ey.hom ≫ (q.map a).left) (IsLocalRing.closedPoint A) ∈
        Set.range (q.map r).left :=
      ⟨c (IsLocalRing.closedPoint k), (Scheme.Hom.comp_apply _ _ _).symm.trans <|
        (congrArg (fun g => g (IsLocalRing.closedPoint k)) ha.symm).trans <|
          (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ (residueMap_closedPoint A))⟩
    obtain ⟨a', ha'⟩ := exists_factor_of_closedPoint_mem B hS p r ey a ha'
    have ha'' : Spec.map (CommRingCat.ofHom (residueMap A)) ≫
        ey.hom ≫ (q.map a').left = c := by
      apply (cancel_mono (q.map r).left).mp
      simpa only [ey, q, eqToIso.hom, Category.assoc, ← Over.comp_left,
        ← Functor.map_comp, ha'] using ha
    obtain ⟨b, hb⟩ := h A C f hf y z hy hz i hi a' ha''
    exact ⟨b ≫ r, by rw [← Category.assoc, hb, ha']⟩
  · intro h A C f hf y z hy hz i hi a ha
    let ey := eqToIso (congrArg Over.left hy).symm
    let ez := eqToIso (congrArg Over.left hz).symm
    have hcomp : Spec.map (CommRingCat.ofHom (residueMap A)) ≫
        ey.hom ≫ (q.map (a ≫ r)).left = c ≫ (q.map r).left := by
      simpa only [ey, q, eqToIso.hom, Functor.map_comp, Over.comp_left,
        ← Category.assoc] using congrArg (fun g => g ≫ (q.map r).left) ha
    obtain ⟨b, hb⟩ := h A C f hf y z hy hz i hi (a ≫ r) hcomp
    have hi' : ey.hom ≫ (q.map i).left =
        Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ ez.hom := by
      simpa only [ey, ez, q, eqToIso.hom, eqToIso.inv, Category.assoc, eqToHom_trans,
        eqToHom_refl, Category.comp_id] using congrArg (fun g => g ≫ ez.hom) hi
    have hb' : (ez.hom ≫ (q.map b).left) (IsLocalRing.closedPoint C) ∈
        Set.range (q.map r).left := by
      have hcomp' : Spec.map (CommRingCat.ofHom (residueMap A)) ≫
          Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ ez.hom ≫
          (q.map b).left = c ≫ (q.map r).left := by
        rw [← Category.assoc (Spec.map (CommRingCat.ofHom f.hom.toRingHom)), ← hi']
        simpa only [Category.assoc, ← Over.comp_left, ← Functor.map_comp, hb] using hcomp
      let _ : IsLocalHom (CommRingCat.ofHom f.hom.toRingHom).hom := f.isLocal
      have hc : (Spec.map (CommRingCat.ofHom f.hom.toRingHom))
          (IsLocalRing.closedPoint A) = IsLocalRing.closedPoint C := Spec_closedPoint
      refine ⟨c (IsLocalRing.closedPoint k), ?_⟩
      calc (q.map r).left (c (IsLocalRing.closedPoint k))
          = (c ≫ (q.map r).left) (IsLocalRing.closedPoint k) :=
            (Scheme.Hom.comp_apply _ _ _).symm
        _ = (Spec.map (CommRingCat.ofHom (residueMap A)) ≫
              Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ ez.hom ≫ (q.map b).left)
              (IsLocalRing.closedPoint k) :=
            congrArg (fun g => g (IsLocalRing.closedPoint k)) hcomp'.symm
        _ = (Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ ez.hom ≫ (q.map b).left)
              ((Spec.map (CommRingCat.ofHom (residueMap A))) (IsLocalRing.closedPoint k)) :=
            Scheme.Hom.comp_apply _ _ _
        _ = (Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ ez.hom ≫ (q.map b).left)
              (IsLocalRing.closedPoint A) :=
            congrArg _ (residueMap_closedPoint A)
        _ = (ez.hom ≫ (q.map b).left)
              ((Spec.map (CommRingCat.ofHom f.hom.toRingHom)) (IsLocalRing.closedPoint A)) :=
            Scheme.Hom.comp_apply _ _ _
        _ = (ez.hom ≫ (q.map b).left) (IsLocalRing.closedPoint C) := congrArg _ hc
    obtain ⟨b', hb'⟩ := exists_factor_of_closedPoint_mem B hS p r ez b hb'
    exact ⟨b', (cancel_mono r).mp (by rw [Category.assoc, hb', hb])⟩

/-! ### Versality at a point of an open -/

/-- The canonical residue-field point factors through the local ring. -/
private theorem residueFieldBasePoint_factor
    {U S : Scheme.{u}} (f : U ⟶ S) (u : U) :
    Spec.map (f.stalkMap u ≫ U.residue u) ≫ S.fromSpecStalk (f u) =
      U.fromSpecResidueField u ≫ f := by
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]
  rfl

/-- The canonical local-ring action on the residue field of a point. -/
private abbrev canonicalResidueAlgebra
    {U S : Scheme.{u}} (f : U ⟶ S) (u : U) :
    Algebra (S.presheaf.stalk (f u)) (U.residueField u) :=
  (f.stalkMap u ≫ U.residue u).hom.toAlgebra

/-- Versality at a point is the infinitesimal lifting property at its
canonical residue-field point. -/
private theorem isVersalAt_iff_infinitesimalLiftingAt
    {S : Scheme.{u}} {X : Type v} [Category.{w} X] (q : X ⥤ Over S)
    (x : X) (u : (q.obj x).left) :
    IsVersalAt (q.obj x) q u x rfl ↔
      @infinitesimalLiftingAt S X _ q x _ _ _ _
        (canonicalResidueAlgebra (q.obj x).hom u)
        (S.fromSpecStalk ((q.obj x).hom u))
        ((q.obj x).left.fromSpecResidueField u) := by
  have hloc₁ : IsLocalHom ((q.obj x).hom.stalkMap u).hom := inferInstance
  have hloc₂ : IsLocalHom (((q.obj x).left.residue u)).hom := by
    show IsLocalHom (IsLocalRing.residue ((q.obj x).left.presheaf.stalk u))
    infer_instance
  have hloc : IsLocalHom
      (((q.obj x).hom.stalkMap u ≫ (q.obj x).left.residue u)).hom := by
    show IsLocalHom
      (((q.obj x).left.residue u).hom.comp ((q.obj x).hom.stalkMap u).hom)
    infer_instance
  let P : (Σ s : S, {g : S.presheaf.stalk s ⟶ (q.obj x).left.residueField u //
      IsLocalHom g.hom}) → Prop := fun sg =>
    @infinitesimalLiftingAt S X _ q x _ _ _ _ sg.2.1.hom.toAlgebra
      (S.fromSpecStalk sg.1) ((q.obj x).left.fromSpecResidueField u)
  have hh : SpecToEquivOfLocalRing S ((q.obj x).left.residueField u)
      ((q.obj x).left.fromSpecResidueField u ≫ (q.obj x).hom) =
        ⟨(q.obj x).hom u,
          (q.obj x).hom.stalkMap u ≫ (q.obj x).left.residue u, hloc⟩ := by
    rw [← residueFieldBasePoint_factor (q.obj x).hom u]
    exact (SpecToEquivOfLocalRing S _).apply_symm_apply
      ⟨(q.obj x).hom u, (q.obj x).hom.stalkMap u ≫ (q.obj x).left.residue u, hloc⟩
  simpa only [P, SpecToEquivOfLocalRing, Equiv.coe_fn_mk, IsVersalAt,
    residueFieldAlgebra, basePoint, residueFieldBasePoint, canonicalResidueAlgebra,
    infinitesimalLiftingAt, eqToHom_refl, Category.comp_id] using Iff.of_eq (congrArg P hh)

/-- An open immersion identifies residue fields as algebras over the local
ring of the image point. -/
private def residueFieldAlgEquivOfOpenImmersion
    {U V S : Scheme.{u}} (j : V ⟶ U) [IsOpenImmersion j]
    (f : U ⟶ S) (v : V) :
    letI := canonicalResidueAlgebra f (j v)
    letI : Algebra (S.presheaf.stalk (f (j v))) (V.residueField v) :=
      canonicalResidueAlgebra (j ≫ f) v
    U.residueField (j v) ≃ₐ[S.presheaf.stalk (f (j v))] V.residueField v := by
  letI := canonicalResidueAlgebra f (j v)
  letI : Algebra (S.presheaf.stalk (f (j v))) (V.residueField v) :=
      canonicalResidueAlgebra (j ≫ f) v
  refine { (asIso (j.residueFieldMap v)).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro a
  have h : (f.stalkMap (j v) ≫ U.residue (j v)) ≫ j.residueFieldMap v =
      (j ≫ f).stalkMap v ≫ V.residue v := by
    rw [Category.assoc, Scheme.residue_residueFieldMap, Scheme.Hom.stalkMap_comp]
    exact (Category.assoc _ _ _).symm
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) a

/-- Versality at a point of an open restricts to and from versality at its
image. -/
public theorem isVersalAt_open_iff
    (B : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    {x' x : X} (r : x' ⟶ x)
    [p.IsStronglyCartesian (p.map r) r]
    [IsOpenImmersion (((p ⋙ Over.post B.inclusion).map r).left)]
    (v : ((p ⋙ Over.post B.inclusion).obj x').left) :
    IsVersalAt ((p ⋙ Over.post B.inclusion).obj x')
        (p ⋙ Over.post B.inclusion) v x' rfl ↔
      IsVersalAt ((p ⋙ Over.post B.inclusion).obj x)
        (p ⋙ Over.post B.inclusion)
        (((p ⋙ Over.post B.inclusion).map r).left v) x rfl := by
  rw [isVersalAt_iff_infinitesimalLiftingAt, isVersalAt_iff_infinitesimalLiftingAt,
    ← Over.w ((p ⋙ Over.post B.inclusion).map r)]
  let : Algebra
      (S.presheaf.stalk (((p ⋙ Over.post B.inclusion).obj x).hom
        (((p ⋙ Over.post B.inclusion).map r).left v)))
      (((p ⋙ Over.post B.inclusion).obj x).left.residueField
        (((p ⋙ Over.post B.inclusion).map r).left v)) :=
    canonicalResidueAlgebra ((p ⋙ Over.post B.inclusion).obj x).hom
      (((p ⋙ Over.post B.inclusion).map r).left v)
  let : Algebra
      (S.presheaf.stalk (((p ⋙ Over.post B.inclusion).obj x).hom
        (((p ⋙ Over.post B.inclusion).map r).left v)))
      (((p ⋙ Over.post B.inclusion).obj x').left.residueField v) :=
    canonicalResidueAlgebra
      (((p ⋙ Over.post B.inclusion).map r).left ≫
        ((p ⋙ Over.post B.inclusion).obj x).hom) v
  let e := residueFieldAlgEquivOfOpenImmersion
    (((p ⋙ Over.post B.inclusion).map r).left)
    ((p ⋙ Over.post B.inclusion).obj x).hom v
  have h₁ := infinitesimalLiftingAt_open_iff
    (Λ := S.presheaf.stalk (((p ⋙ Over.post B.inclusion).obj x).hom
      (((p ⋙ Over.post B.inclusion).map r).left v)))
    (k := ((p ⋙ Over.post B.inclusion).obj x').left.residueField v)
    (algΛk := canonicalResidueAlgebra
      (((p ⋙ Over.post B.inclusion).map r).left ≫
        ((p ⋙ Over.post B.inclusion).obj x).hom) v) B hS p r
    (S.fromSpecStalk (((p ⋙ Over.post B.inclusion).obj x).hom
      (((p ⋙ Over.post B.inclusion).map r).left v)))
    (((p ⋙ Over.post B.inclusion).obj x').left.fromSpecResidueField v)
  have h₂ := infinitesimalLiftingAt_residueEquiv_iff
    (Λ := S.presheaf.stalk (((p ⋙ Over.post B.inclusion).obj x).hom
      (((p ⋙ Over.post B.inclusion).map r).left v)))
    (k := ((p ⋙ Over.post B.inclusion).obj x).left.residueField
      (((p ⋙ Over.post B.inclusion).map r).left v))
    (k' := ((p ⋙ Over.post B.inclusion).obj x').left.residueField v)
    (algk := canonicalResidueAlgebra ((p ⋙ Over.post B.inclusion).obj x).hom
      (((p ⋙ Over.post B.inclusion).map r).left v))
    (algk' := canonicalResidueAlgebra
      (((p ⋙ Over.post B.inclusion).map r).left ≫
        ((p ⋙ Over.post B.inclusion).obj x).hom) v)
    (p ⋙ Over.post B.inclusion) x e
    (S.fromSpecStalk (((p ⋙ Over.post B.inclusion).obj x).hom
      (((p ⋙ Over.post B.inclusion).map r).left v)))
    (((p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField
      (((p ⋙ Over.post B.inclusion).map r).left v))
  have he : CommRingCat.ofHom e.toRingHom =
      (((p ⋙ Over.post B.inclusion).map r).left).residueFieldMap v := rfl
  rw [he, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at h₂
  exact h₁.trans h₂.symm

/-! ### Shrinking the base -/

-- The slice functor `CategoryTheory.Over.post` is a plain `def`, so goals reading an object
-- of the site in `Over S` are not type-correct at `implicit` transparency.  Naming it here is
-- what lets `rw`, `change` and instance search see through exactly it and nothing else.
attribute [local implicit_reducible] CategoryTheory.Over.post

/-- Restricting along a strongly Cartesian arrow over the inclusion of an open `W` of the base of
`x` gives an open-immersion arrow `r : x' ⟶ x` whose source has base `W`. -/
private theorem exists_restrict_open
    (B : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (x : X)
    (W : ((p ⋙ Over.post B.inclusion).obj x).left.Opens) :
    ∃ (x' : X) (r : x' ⟶ x)
      (he₀ : ((p ⋙ Over.post B.inclusion).obj x').left = (W : Scheme.{u})),
      ((p ⋙ Over.post B.inclusion).map r).left = eqToHom he₀ ≫ W.ι ∧
      IsOpenImmersion ((p ⋙ Over.post B.inclusion).map r).left ∧
      ((p ⋙ Over.post B.inclusion).obj x').hom =
        eqToHom he₀ ≫ W.ι ≫ ((p ⋙ Over.post B.inclusion).obj x).hom ∧
      ∀ w : (W : Scheme.{u}),
        ((p ⋙ Over.post B.inclusion).map r).left ((eqToHom he₀.symm) w) = W.ι w := by
  have hfib : p.IsFibered := hp.isFibered
  let Uo := p.obj x
  let W' : B.Schemes := ⟨(W : Scheme.{u}),
    (Scheme.size_coe_opens_le _ W).trans_lt Uo.left.property⟩
  let jW : W' ⟶ Uo.left := ObjectProperty.homMk W.ι
  let U' : AlgebraicGeometry.BigFppfOver B S hS := Over.mk (jW ≫ Uo.hom)
  let jU : U' ⟶ Uo := Over.homMk jW
  obtain ⟨x', r, hr⟩ := Functor.IsFibered.exists_isStronglyCartesian p (Y := x) jU
  have hy : p.obj x' = U' :=
    @IsHomLift.domain_eq _ _ _ _ p _ _ _ _ jU r hr.toIsHomLift
  have hmap : p.map r = eqToHom hy ≫ jU := by
    have := hr.toIsHomLift
    simpa using IsHomLift.fac' p jU r
  have he₀ : ((p ⋙ Over.post B.inclusion).obj x').left = (W : Scheme.{u}) :=
    congrArg (fun T : AlgebraicGeometry.BigFppfOver B S hS => B.inclusion.obj T.left) hy
  have hleft : ((p ⋙ Over.post B.inclusion).map r).left = eqToHom he₀ ≫ W.ι := by
    show B.inclusion.map ((p.map r).left) = _
    rw [hmap]
    show B.inclusion.map ((eqToHom hy).left ≫ jW) = _
    rw [Over.eqToHom_left, Functor.map_comp, eqToHom_map]
    rfl
  have hoi : IsOpenImmersion ((p ⋙ Over.post B.inclusion).map r).left := by
    rw [hleft]
    exact @IsOpenImmersion.comp _ _ _ _ _ (IsOpenImmersion.of_isIso _) inferInstance
  have hbase : ((p ⋙ Over.post B.inclusion).obj x').hom =
      eqToHom he₀ ≫ W.ι ≫ ((p ⋙ Over.post B.inclusion).obj x).hom := by
    rw [← Over.w ((p ⋙ Over.post B.inclusion).map r), hleft, Category.assoc]
  refine ⟨x', r, he₀, hleft, hoi, hbase, fun w => ?_⟩
  rw [← Scheme.Hom.comp_apply, hleft, ← Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp]

/-- **Openness of versality shrinks the base.** An object of a category fibred
in groupoids over a locally Noetherian base, of finite type and versal at one
finite-type point, restricts along an arrow over an affine open immersion to an
object of finite type that is versal at *every* finite-type point of its
base.

The hypothesis `hopen` is openness of versality for `p ⋙ Over.post B.inclusion`,
written out: it is by definition `Deformation.Artin.IsOpenVersality
(p ⋙ Over.post B.inclusion) h` for any `h`, whose second argument that predicate
does not use. It is spelled out because `Over.post B.inclusion` is not fibred in
groupoids — a scheme whose size exceeds `B.cutoff` admits a morphism to an object
of `B.Schemes` and has no lift there — so no such `h` exists and quantifying over
one would make the statement vacuous. -/
public theorem exists_shrink_versal_everywhere
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsLocallyNoetherian S]
    {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (hopen : ∀ U : Over S, LocallyOfFiniteType U.hom →
      ∀ (y : X) (hy : (p ⋙ Over.post B.inclusion).obj y = U) (u : U.left),
        AlgebraicGeometry.IsFiniteTypePoint u →
        IsVersalAt U (p ⋙ Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 →
            AlgebraicGeometry.IsFiniteTypePoint u' →
            IsVersalAt U (p ⋙ Over.post B.inclusion) u' y hy)
    (x : X)
    (hfinite : LocallyOfFiniteType ((p ⋙ Over.post B.inclusion).obj x).hom)
    (hqc : QuasiCompact ((p ⋙ Over.post B.inclusion).obj x).hom)
    (u₀ : ((p ⋙ Over.post B.inclusion).obj x).left)
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hversal : IsVersalAt ((p ⋙ Over.post B.inclusion).obj x)
      (p ⋙ Over.post B.inclusion) u₀ x rfl) :
    ∃ (x' : X) (r : x' ⟶ x) (u₀' : ((p ⋙ Over.post B.inclusion).obj x').left),
      IsOpenImmersion (((p ⋙ Over.post B.inclusion).map r).left) ∧
      ((p ⋙ Over.post B.inclusion).map r).left u₀' = u₀ ∧
      AlgebraicGeometry.IsFiniteTypePoint u₀' ∧
      LocallyOfFiniteType ((p ⋙ Over.post B.inclusion).obj x').hom ∧
      QuasiCompact ((p ⋙ Over.post B.inclusion).obj x').hom ∧
      ∀ v : ((p ⋙ Over.post B.inclusion).obj x').left,
        AlgebraicGeometry.IsFiniteTypePoint v →
        IsVersalAt ((p ⋙ Over.post B.inclusion).obj x')
          (p ⋙ Over.post B.inclusion) v x' rfl := by
  obtain ⟨V, hu₀V, hall⟩ :=
    hopen ((p ⋙ Over.post B.inclusion).obj x) hfinite x rfl u₀ hu₀ hversal
  obtain ⟨W, hW, hu₀W, hWV⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
      (X := ((p ⋙ Over.post B.inclusion).obj x).left) (x := u₀) (U := V) hu₀V
  obtain ⟨x', r, he₀, hleft, hoi, hbase, himage⟩ := exists_restrict_open B hS p hp x W
  have hrange : ∀ v : ((p ⋙ Over.post B.inclusion).obj x').left,
      ((p ⋙ Over.post B.inclusion).map r).left v ∈ V.carrier := fun v => by
    rw [hleft, Scheme.Hom.comp_apply]
    exact hWV ((eqToHom he₀) v).2
  -- `W` is a Noetherian space, which is what makes every morphism out of it quasi-compact.
  have hSnoeth : IsLocallyNoetherian (B.inclusion.obj (B.obj hS)) :=
    inferInstanceAs (IsLocallyNoetherian S)
  have hnoeth : IsLocallyNoetherian ((p ⋙ Over.post B.inclusion).obj x).left :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((p ⋙ Over.post B.inclusion).obj x).hom
  have hring : IsNoetherianRing
      Γ(((p ⋙ Over.post B.inclusion).obj x).left, W) :=
    hnoeth.component_noetherian ⟨W, hW⟩
  have hNS : TopologicalSpace.NoetherianSpace (W : Scheme.{u}) :=
    AlgebraicGeometry.noetherianSpace_of_isAffineOpen W hW
  refine ⟨x', r, (eqToHom he₀.symm) (⟨u₀, hu₀W⟩ : (W : Scheme.{u})), hoi, ?_, ?_, ?_, ?_, ?_⟩
  · exact himage ⟨u₀, hu₀W⟩
  · exact AlgebraicGeometry.mapsTo_finiteTypePoints (eqToHom he₀.symm)
      (AlgebraicGeometry.isFiniteTypePoint_of_immersion W.ι
        (⟨u₀, hu₀W⟩ : (W : Scheme.{u})) hu₀)
  · rw [hbase]
    infer_instance
  · rw [hbase]
    infer_instance
  · intro v hv
    have hcart : p.IsStronglyCartesian (p.map r) r := hp.isStronglyCartesian r
    rw [isVersalAt_open_iff B hS p r v]
    exact hall _ (hrange v)
      (AlgebraicGeometry.mapsTo_finiteTypePoints
        (((p ⋙ Over.post B.inclusion).map r).left) hv)

/-- **Shrinking the base to an affine open neighbourhood of a specialization.** Let `x` be an
object of a category fibred in groupoids over a locally Noetherian base, with base locally of
finite type, and let `u ⤳ u₀` be a specialization of finite type points of its base. Restricting
`x` along a strongly cartesian arrow over an affine open neighbourhood of `u₀` which maps into an
affine open of `S` produces an object over an affine scheme, with points `v ⤳ v₀` over `u` and
`u₀`, at which versality is the versality of `x` at `u` and `u₀`.

This is the step "after shrinking `U` we may assume `U` is affine and `U` maps into an affine
open `Spec(Λ)` of `S`" of Stacks 0G2K: `u` lies in every open neighbourhood of `u₀`. -/
public theorem exists_affine_shrink_of_specializes
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (x : X)
    (hfinite : LocallyOfFiniteType ((p ⋙ Over.post B.inclusion).obj x).hom)
    (u u₀ : ((p ⋙ Over.post B.inclusion).obj x).left)
    (hu : AlgebraicGeometry.IsFiniteTypePoint u) (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hspec : u ⤳ u₀) :
    ∃ (x' : X) (_r : x' ⟶ x) (v v₀ : ((p ⋙ Over.post B.inclusion).obj x').left) (W : S.Opens),
      IsAffineOpen W ∧ IsAffine ((p ⋙ Over.post B.inclusion).obj x').left ∧
      LocallyOfFiniteType ((p ⋙ Over.post B.inclusion).obj x').hom ∧
      Set.range ((p ⋙ Over.post B.inclusion).obj x').hom ⊆ (W : Set S) ∧
      AlgebraicGeometry.IsFiniteTypePoint v ∧ AlgebraicGeometry.IsFiniteTypePoint v₀ ∧
      v ⤳ v₀ ∧
      (IsVersalAt ((p ⋙ Over.post B.inclusion).obj x') (p ⋙ Over.post B.inclusion) v x' rfl ↔
        IsVersalAt ((p ⋙ Over.post B.inclusion).obj x) (p ⋙ Over.post B.inclusion) u x rfl) ∧
      (IsVersalAt ((p ⋙ Over.post B.inclusion).obj x') (p ⋙ Over.post B.inclusion) v₀ x' rfl ↔
        IsVersalAt ((p ⋙ Over.post B.inclusion).obj x) (p ⋙ Over.post B.inclusion) u₀ x
          rfl) := by
  let fU := ((p ⋙ Over.post B.inclusion).obj x).hom
  obtain ⟨WS, hWS, hu₀WS, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (X := S) (x := fU u₀) (U := ⊤) trivial
  obtain ⟨W, hW, hu₀W, hWV⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
      (X := ((p ⋙ Over.post B.inclusion).obj x).left) (x := u₀) (U := fU ⁻¹ᵁ WS) hu₀WS
  have huW : u ∈ W := hspec.mem_open W.2 hu₀W
  obtain ⟨x', r, he₀, -, hoi, hbase, himage⟩ := exists_restrict_open B hS p hp x W
  have hcart : p.IsStronglyCartesian (p.map r) r := hp.isStronglyCartesian r
  let v : ((p ⋙ Over.post B.inclusion).obj x').left := (eqToHom he₀.symm) ⟨u, huW⟩
  let v₀ : ((p ⋙ Over.post B.inclusion).obj x').left := (eqToHom he₀.symm) ⟨u₀, hu₀W⟩
  have hv : ((p ⋙ Over.post B.inclusion).map r).left v = u := himage _
  have hv₀ : ((p ⋙ Over.post B.inclusion).map r).left v₀ = u₀ := himage _
  refine ⟨x', r, v, v₀, WS, hWS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he₀]
    exact hW
  · rw [hbase]
    infer_instance
  · rintro _ ⟨w, rfl⟩
    rw [hbase]
    exact hWV ((eqToHom he₀) w).2
  · exact AlgebraicGeometry.mapsTo_finiteTypePoints (eqToHom he₀.symm)
      (AlgebraicGeometry.isFiniteTypePoint_of_immersion W.ι
        (⟨u, huW⟩ : (W : Scheme.{u})) hu)
  · exact AlgebraicGeometry.mapsTo_finiteTypePoints (eqToHom he₀.symm)
      (AlgebraicGeometry.isFiniteTypePoint_of_immersion W.ι
        (⟨u₀, hu₀W⟩ : (W : Scheme.{u})) hu₀)
  · rwa [← ((p ⋙ Over.post B.inclusion).map r).left.isOpenEmbedding.isInducing.specializes_iff,
      hv, hv₀]
  · rw [isVersalAt_open_iff B hS p r v, hv]
  · rw [isVersalAt_open_iff B hS p r v₀, hv₀]

end Deformation.Artin

end
