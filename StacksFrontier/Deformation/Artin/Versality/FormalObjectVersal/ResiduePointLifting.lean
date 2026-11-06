module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.Stalk
public import StacksFrontier.Deformation.Artin.FormalObject
public import StacksFrontier.Deformation.Artin.FormalObject.Predeformation
public import StacksFrontier.Deformation.Artin.FormalObject.Versal
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectVersal.ApproximationLevels
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectVersal.CompletionLifts
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.FormalObject.Associated
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.Groupoid.BaseCategory
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.Basic
public import StacksFrontier.Deformation.Smooth.Pushforward
public import StacksFrontier.Deformation.Smooth.Versal
public import StacksFrontier.RingTheory.Ideal.RadicalMaximalQuotient

/-!
# The lifting property at a residue point and smoothness of the associated morphism

Auxiliary material for `Deformation.Artin.isVersalAt_iff_isVersal`: factorization through
Cartesian arrows read on underlying morphisms of schemes, morphisms of deformations and their
underlying morphisms, the lifting property `Deformation.Artin.LiftsAtResiduePoint` defining
versality at a point and its invariance under change of residue field, and the comparison of
that lifting property with smoothness of the associated morphism of a formal object.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Deformation.Artin

universe u v w

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
attribute [local implicit_reducible] Deformation.Artin.baseOver
attribute [local implicit_reducible] Deformation.Artin.truncationOver

/-- Postcomposing with a transport leaves the underlying morphism of schemes unchanged. -/
private theorem schemeMap_comp_eqToHom
    {S : Scheme.{u}} {F : Type v} [Category.{w} F]
    (q : F ⥤ Over S) {y z z' : F} {Y Z : Over S}
    (hy : q.obj y = Y) (hz : q.obj z = Z) (hz' : q.obj z' = Z)
    (e : z = z') (f : y ⟶ z) :
    schemeMap q hy hz' (f ≫ eqToHom e) = schemeMap q hy hz f := by
  subst z'
  simp

/-- The underlying morphism of schemes is a morphism over `S`. -/
public theorem schemeMap_over
    {S : Scheme.{u}} {F : Type v} [Category.{w} F]
    (q : F ⥤ Over S) {y z : F} {Y Z : Over S}
    (hy : q.obj y = Y) (hz : q.obj z = Z) (f : y ⟶ z) :
    schemeMap q hy hz f ≫ Z.hom = Y.hom := by
  subst Y Z
  simp [schemeMap]

/-- Two morphisms over `S` are equal as soon as their transported underlying morphisms are. -/
private theorem schemeMap_injective
    {S : Scheme.{u}} {Y Z : Over S} {Y' Z' : Over S}
    (hY : Y = Y') (hZ : Z = Z') (f g : Y ⟶ Z)
    (h : eqToHom (congrArg Over.left hY).symm ≫ f.left ≫
        eqToHom (congrArg Over.left hZ) =
      eqToHom (congrArg Over.left hY).symm ≫ g.left ≫
        eqToHom (congrArg Over.left hZ)) : f = g := by
  subst Y' Z'
  apply Over.OverMorphism.ext
  simpa using h

/-- Unique factorization through a Cartesian arrow, stated for underlying morphisms of
schemes in the slice over `S`. -/
public theorem factor_through_cartesian_schemeMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    {y z x : F} {Y Z X : Over S}
    (hy : (p ⋙ Over.post B.inclusion).obj y = Y)
    (hz : (p ⋙ Over.post B.inclusion).obj z = Z)
    (hx : (p ⋙ Over.post B.inclusion).obj x = X)
    (r : z ⟶ x) (a : y ⟶ x) (f : Y.left ⟶ Z.left)
    (hf : f ≫ Z.hom = Y.hom)
    (h : f ≫ schemeMap (p ⋙ Over.post B.inclusion) hz hx r =
      schemeMap (p ⋙ Over.post B.inclusion) hy hx a) :
    ∃! l : y ⟶ z, schemeMap (p ⋙ Over.post B.inclusion) hy hz l = f ∧ l ≫ r = a := by
  subst hy
  subst hz
  let q := p ⋙ Over.post B.inclusion
  let f' : q.obj y ⟶ q.obj z := Over.homMk f hf
  have hf' : f' ≫ q.map r = q.map a := by
    have h' : f ≫ (q.map r).left ≫ eqToHom (congrArg Over.left hx) =
        (q.map a).left ≫ eqToHom (congrArg Over.left hx) := by
      simpa only [schemeMap, eqToHom_refl, Category.id_comp, Category.assoc] using h
    have h2 := congrArg (fun t => t ≫ eqToHom (congrArg Over.left hx).symm) h'
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at h2
    apply Over.OverMorphism.ext
    show f ≫ (q.map r).left = (q.map a).left
    exact h2
  obtain ⟨l, hl, hu⟩ := factor_through_cartesian_comp_fullyFaithful
    p (Over.post B.inclusion) r (hp.isStronglyCartesian r) f' a hf'
  refine ⟨l, ⟨?_, hl.2⟩, ?_⟩
  · show eqToHom _ ≫ (q.map l).left ≫ eqToHom _ = f
    rw [hl.1]
    simp [f']
  · intro l' hl'
    apply hu l'
    refine ⟨?_, hl'.2⟩
    apply schemeMap_injective rfl rfl
    simpa [schemeMap, f', q, Category.assoc] using hl'.1

/-- The underlying object of a deformation lies over the spectrum of the prescribed
Artinian local algebra. -/
public theorem deformationPointBase
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {F : Type v} [Category.{w} F] {q : F ⥤ Over S}
    {x₀ : F} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (C : Deformation.Artin.PredeformationConstruction iΛ q x₀ hx₀)
    (a : C.carrier) (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (h : C.projection.obj a = A) :
    q.obj (C.objects a).point = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) :=
  (C.objects a).base.trans (congrArg
    (fun A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k => Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ))
    ((C.object_projection a).symm.trans h))

/-- A morphism of a predeformation category lies over the arrow of `𝒞_Λ` it is sent to. -/
public theorem deformationMorphism_isHomLift
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {F : Type v} [Category.{w} F] {q : F ⥤ Over S}
    {x₀ : F} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (C : Deformation.Artin.PredeformationConstruction iΛ q x₀ hx₀)
    {a b : C.carrier} (f : a ⟶ b) :
    C.projection.IsHomLift (C.morphisms a b f).ringHom f :=
  IsHomLift.of_fac C.projection _ _ (C.object_projection a) (C.object_projection b)
    (C.morphism_projection f).symm

/-- A morphism lying over `f` has underlying morphism of schemes the spectrum of `f`. -/
public theorem deformationMorphism_base
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {F : Type v} [Category.{w} F] {q : F ⥤ Over S}
    {x₀ : F} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (C : Deformation.Artin.PredeformationConstruction iΛ q x₀ hx₀)
    {a b : C.carrier} {A B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f : A ⟶ B) (j : a ⟶ b) (hj : C.projection.IsHomLift f j)
    (ha : q.obj (C.objects a).point = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ))
    (hb : q.obj (C.objects b).point = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ)) :
    eqToHom (congrArg Over.left hb).symm ≫
        (q.map (C.morphisms a b j).arrow).left ≫ eqToHom (congrArg Over.left ha) =
      Spec.map (CommRingCat.ofHom f.hom.toRingHom) := by
  have := hj
  have hA : A = (C.objects a).algebra :=
    (IsHomLift.domain_eq C.projection f j).symm.trans (C.object_projection a)
  have hB : B = (C.objects b).algebra :=
    (IsHomLift.codomain_eq C.projection f j).symm.trans (C.object_projection b)
  subst A B
  have hf : f = (C.morphisms a b j).ringHom :=
    (IsHomLift.fac C.projection f j).trans (C.morphism_projection j)
  simpa only [hf] using (C.morphisms a b j).arrow_base

/-- A reversed arrow compatible with the arrows out of the closed fibre and lying over `f`
comes from a morphism of the predeformation category. -/
private theorem exists_deformationMorphism
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {F : Type v} [Category.{w} F] {q : F ⥤ Over S}
    {x₀ : F} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (C : Deformation.Artin.PredeformationConstruction iΛ q x₀ hx₀)
    {a b : C.carrier} {A B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f : A ⟶ B) (ha : C.projection.obj a = A) (hb : C.projection.obj b = B)
    (j : (C.objects b).point ⟶ (C.objects a).point)
    (ht : (C.objects b).arrow ≫ j = (C.objects a).arrow)
    (hj : schemeMap q (deformationPointBase C b B hb)
        (deformationPointBase C a A ha) j =
      Spec.map (CommRingCat.ofHom f.hom.toRingHom)) :
    ∃ l : a ⟶ b, C.projection.IsHomLift f l ∧ (C.morphisms a b l).arrow = j := by
  have hA : A = (C.objects a).algebra := ha.symm.trans (C.object_projection a)
  have hB : B = (C.objects b).algebra := hb.symm.trans (C.object_projection b)
  cases hA
  cases hB
  let m : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ (C.objects a) (C.objects b) :=
    { ringHom := f, arrow := j, triangle := ht, arrow_base := hj }
  refine ⟨(C.morphisms a b).symm m, ?_, ?_⟩
  · have h := deformationMorphism_isHomLift C ((C.morphisms a b).symm m)
    simpa only [Equiv.apply_symm_apply] using h
  · exact congrArg Deformation.Artin.DeformationMorphism.arrow
      ((C.morphisms a b).apply_symm_apply m)

/-- Two morphisms into the source of a Cartesian arrow which agree on underlying schemes
and after composing with the arrow are equal. -/
private theorem schemeMap_cartesian_ext
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    {y z x : F} {Y Z : Over S}
    (hy : (p ⋙ Over.post B.inclusion).obj y = Y)
    (hz : (p ⋙ Over.post B.inclusion).obj z = Z)
    (r : z ⟶ x) (s t : y ⟶ z)
    (hb : schemeMap (p ⋙ Over.post B.inclusion) hy hz s =
      schemeMap (p ⋙ Over.post B.inclusion) hy hz t)
    (hc : s ≫ r = t ≫ r) : s = t := by
  have ht : p.map t = p.map s :=
    (Over.post B.inclusion).map_injective (schemeMap_injective hy hz _ _ hb.symm)
  exact factor_through_cartesian_unique p r (hp.isStronglyCartesian r)
    (p.map_comp s r).symm s t rfl ht rfl hc.symm

/-- The arrow of a deformation transports along an equality of deformations. -/
private theorem deformationObject_arrow_congr
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {F : Type v} [Category.{w} F] {q : F ⥤ Over S}
    {x₀ : F} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a b : Deformation.Artin.DeformationObject iΛ q x₀ hx₀} (h : a = b) :
    a.arrow ≫ eqToHom (congrArg Deformation.Artin.DeformationObject.point h) = b.arrow := by
  cases h
  simp

/-- The arrow of a deformation has underlying morphism of schemes the spectrum of the
residue map of its Artinian local algebra. -/
public theorem deformationObject_residueMap
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {F : Type v} [Category.{w} F] {q : F ⥤ Over S}
    {x₀ : F} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (C : Deformation.Artin.PredeformationConstruction iΛ q x₀ hx₀)
    (a : C.carrier) (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : C.projection.obj a = A) :
    schemeMap q hx₀ (deformationPointBase C a A hA) (C.objects a).arrow =
      Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) := by
  have h : A = (C.objects a).algebra := hA.symm.trans (C.object_projection a)
  cases h
  exact (C.objects a).arrow_base

/-- A morphism whose underlying morphism of schemes is an identity is an isomorphism. -/
public theorem schemeMap_id_isIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    {y z : F} {Y : Over S}
    (hy : (p ⋙ Over.post B.inclusion).obj y = Y)
    (hz : (p ⋙ Over.post B.inclusion).obj z = Y)
    (i : y ⟶ z) (hi : schemeMap (p ⋙ Over.post B.inclusion) hy hz i = 𝟙 Y.left) :
    IsIso i := by
  have he : (p ⋙ Over.post B.inclusion).map i = eqToHom (hy.trans hz.symm) := by
    apply schemeMap_injective hy hz
    simpa [schemeMap] using hi
  have hq : IsIso ((Over.post B.inclusion).map (p.map i)) := by
    show IsIso ((p ⋙ Over.post B.inclusion).map i)
    rw [he]
    infer_instance
  have := hq
  have : IsIso (p.map i) := isIso_of_reflects_iso (p.map i) (Over.post B.inclusion)
  have := hp.isStronglyCartesian i
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p (p.map i) i

/-- At an Artinian point `α`, the induced cone has underlying morphism of schemes the
spectrum of `α` followed by the chosen morphism out of the complete local base. -/
public theorem associatedMorphismRestriction_base
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {F : Type v} [Category.{w} F] {q : F ⥤ Over S}
    {x₀ : F} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (C : Deformation.Artin.PredeformationConstruction iΛ q x₀ hx₀)
    (η : Deformation.FormalObject C.projection)
    {P : Deformation.ChosenPushforwards C.projection}
    (H : Deformation.AssociatedMorphism η P)
    {x : F} (r : ∀ n, (deformationForget C).obj (.op (η.level n)) ⟶ x)
    (hr : ∀ n, (deformationForget C).map (η.transition n).op ≫ r (n + 1) = r n)
    (U : Over S) (hx : q.obj x = U) (g : Spec (.of η.base) ⟶ U.left)
    (hbase : ∀ n,
      eqToHom (congrArg Over.left (deformationPointBase C (η.level n)
          (Deformation.AdicTruncation.obj η.base n) (η.level_eq n))).symm ≫
        (q.map (r n)).left ≫ eqToHom (congrArg Over.left hx) =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Deformation.AdicTruncation.ideal η.base n))) ≫ g)
    (α : (Deformation.restrictedCoyoneda η.base).Elements) :
    eqToHom (congrArg Over.left (deformationPointBase C (H.toBasedFunctor.obj α)
        α.1 (H.toBasedFunctor.w_obj α))).symm ≫
      (q.map ((associatedMorphismRestriction η H (deformationForget C) r hr).app
        (.op α))).left ≫ eqToHom (congrArg Over.left hx) =
      Spec.map (CommRingCat.ofHom α.2.hom.toRingHom) ≫ g := by
  let n := H.level α
  let ha := deformationPointBase C (η.level n)
    (Deformation.AdicTruncation.obj η.base n) (η.level_eq n)
  let hb := deformationPointBase C (H.toBasedFunctor.obj α) α.1
    (H.toBasedFunctor.w_obj α)
  have hinc := deformationMorphism_base C (H.factor α) (H.pointInclusion α)
    (associatedMorphism_pointInclusion_isHomLift η H α) ha hb
  show eqToHom (congrArg Over.left hb).symm ≫
    (q.map ((C.morphisms _ _ (H.pointInclusion α)).arrow ≫ r n)).left ≫
      eqToHom (congrArg Over.left hx) = _
  rw [q.map_comp, Over.comp_left]
  calc
    _ = (eqToHom (congrArg Over.left hb).symm ≫
          (q.map (C.morphisms _ _ (H.pointInclusion α)).arrow).left ≫
          eqToHom (congrArg Over.left ha)) ≫
        (eqToHom (congrArg Over.left ha).symm ≫ (q.map (r n)).left ≫
          eqToHom (congrArg Over.left hx)) := by simp [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom (H.factor α).hom.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Deformation.AdicTruncation.ideal η.base n))) ≫ g) := by
      rw [hinc, hbase]
      rfl
    _ = _ := by
      rw [← Spec.map_comp_assoc]
      congr 2
      exact congrArg (fun f => CommRingCat.ofHom f.toRingHom) (H.factor_spec α).2.2

/-- The induced cone is compatible with the arrows out of the closed fibre. -/
public theorem associatedMorphismRestriction_closedPoint
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {F : Type v} [Category.{w} F] {q : F ⥤ Over S}
    {x₀ : F} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (C : Deformation.Artin.PredeformationConstruction iΛ q x₀ hx₀)
    (η : Deformation.FormalObject C.projection)
    {P : Deformation.ChosenPushforwards C.projection}
    (H : Deformation.AssociatedMorphism η P)
    {x : F} (r : ∀ n, (deformationForget C).obj (.op (η.level n)) ⟶ x)
    (hr : ∀ n, (deformationForget C).map (η.transition n).op ≫ r (n + 1) = r n)
    (r₀ : x₀ ⟶ x)
    (hclosed : ∀ n, (C.objects (η.level n)).arrow ≫ r n = r₀)
    (α : (Deformation.restrictedCoyoneda η.base).Elements) :
    (C.objects (H.toBasedFunctor.obj α)).arrow ≫
      (associatedMorphismRestriction η H (deformationForget C) r hr).app (.op α) = r₀ := by
  show (C.objects (H.toBasedFunctor.obj α)).arrow ≫
      ((C.morphisms _ _ (H.pointInclusion α)).arrow ≫ r (H.level α)) = r₀
  rw [← Category.assoc, (C.morphisms _ _ (H.pointInclusion α)).triangle, hclosed]

/-- The lifting property defining versality at a point, stated for an arbitrary
residue-field point `κ` of `U`. -/
public abbrev LiftsAtResiduePoint
    {Λ k : Type u} [CommRing Λ] [Field k] [alg : Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    {F : Type v} [Category.{w} F] (q : F ⥤ Over S)
    (U : Over S) (x : F) (hx : q.obj x = U) (κ : Spec (.of k) ⟶ U.left) : Prop :=
  ∀ (A B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) (f : B ⟶ A),
    Function.Surjective f.hom → ∀ (y z : F)
      (hy : q.obj y = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ))
      (hz : q.obj z = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ))
      (i : y ⟶ z), schemeMap q hy hz i = Spec.map (CommRingCat.ofHom f.hom.toRingHom) →
      ∀ a : y ⟶ x,
        Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫ schemeMap q hy hx a = κ →
        ∃ b : z ⟶ x, i ≫ b = a

/-- Versality at `u₀` is exactly the lifting property at the canonical residue-field point. -/
public theorem isVersalAt_iff_liftsAtResiduePoint
    {S : Scheme.{u}} (U : Over S)
    {F : Type v} [Category.{w} F] (q : F ⥤ Over S)
    (u₀ : U.left) (x : F) (hx : q.obj x = U) :
    Deformation.Artin.IsVersalAt U q u₀ x hx ↔
      LiftsAtResiduePoint (Λ := S.presheaf.stalk (Deformation.Artin.basePoint U u₀))
        (k := U.left.residueField u₀)
        (alg := Deformation.Artin.residueFieldAlgebra U u₀)
        (S.fromSpecStalk (Deformation.Artin.basePoint U u₀))
        q U x hx (U.left.fromSpecResidueField u₀) := Iff.rfl

/-- Precomposing a residue-field point with an isomorphism and then its inverse does nothing. -/
private theorem spec_symm_comp_spec_comp
    {Λ k k' : Type u} [CommRing Λ] [Field k] [Field k']
    [Algebra Λ k] [Algebra Λ k'] (e : k ≃ₐ[Λ] k') {X : Scheme.{u}} (κ : Spec (.of k) ⟶ X) :
    Spec.map (CommRingCat.ofHom e.symm.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom) ≫ κ = κ := by
  have hid : CommRingCat.ofHom e.toAlgHom.toRingHom ≫
      CommRingCat.ofHom e.symm.toAlgHom.toRingHom = 𝟙 (CommRingCat.of k) := by
    ext t
    exact e.symm_apply_apply t
  rw [← Category.assoc, ← Spec.map_comp, hid, Spec.map_id, Category.id_comp]

/-- The lifting property transports along an isomorphism of residue fields over the base. -/
public theorem liftsAtResiduePoint_changeResidueField
    {Λ k k' : Type u} [CommRing Λ] [Field k] [Field k']
    [Algebra Λ k] [Algebra Λ k'] (e : k ≃ₐ[Λ] k')
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    {F : Type v} [Category.{w} F] (q : F ⥤ Over S)
    (U : Over S) (x : F) (hx : q.obj x = U) (κ : Spec (.of k) ⟶ U.left)
    (hl : LiftsAtResiduePoint iΛ q U x hx κ) :
    LiftsAtResiduePoint iΛ q U x hx
      (Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom) ≫ κ) := by
  intro A B f hf y z hy hz i hi a ha
  let A₀ : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k := {
    carrier := A
    residueEquiv := A.residueEquiv.trans e.symm
  }
  let B₀ : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k := {
    carrier := B
    residueEquiv := B.residueEquiv.trans e.symm
  }
  let f₀ : B₀ ⟶ A₀ := {
    hom := f.hom
    isLocal := f.isLocal
    residue_comm := fun b => congrArg e.symm (f.residue_comm b)
  }
  apply hl A₀ B₀ f₀ hf y z hy hz i hi a
  have he : Deformation.Artin.residueMap A₀ = e.symm.toAlgHom.toRingHom.comp
      (Deformation.Artin.residueMap A) := rfl
  rw [he, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ha, spec_symm_comp_spec_comp]

/-- The lifting property at a residue-field point is unchanged by an isomorphism of
residue fields over the base. -/
public theorem liftsAtResiduePoint_iff_changeResidueField
    {Λ k k' : Type u} [CommRing Λ] [Field k] [Field k']
    [Algebra Λ k] [Algebra Λ k'] (e : k ≃ₐ[Λ] k')
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    {F : Type v} [Category.{w} F] (q : F ⥤ Over S)
    (U : Over S) (x : F) (hx : q.obj x = U) (κ : Spec (.of k) ⟶ U.left) :
    LiftsAtResiduePoint iΛ q U x hx κ ↔
      LiftsAtResiduePoint iΛ q U x hx
        (Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom) ≫ κ) := by
  constructor
  · exact liftsAtResiduePoint_changeResidueField e iΛ q U x hx κ
  · intro hl
    have h := liftsAtResiduePoint_changeResidueField e.symm iΛ q U x hx
      (Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom) ≫ κ) hl
    rwa [spec_symm_comp_spec_comp] at h

/-- Versality at `u₀` is the lifting property at the residue field of a presentation of
the completed local ring at `u₀`. -/
theorem isVersalAt_iff_liftsAtCompletionResiduePoint
    {S : Scheme.{u}} (U : Over S) [IsLocallyNoetherian U.left]
    {F : Type v} [Category.{w} F] (q : F ⥤ Over S)
    (u₀ : U.left) (x : F) (hx : q.obj x = U)
    {R : Type u} [CommRing R] [IsLocalRing R]
    [Algebra (S.presheaf.stalk (Deformation.Artin.basePoint U u₀)) R]
    (e : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+* R)
    (g : Spec (.of R) ⟶ U.left)
    (hg : g = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
        (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫ U.left.fromSpecStalk u₀)
    (hbase : Spec.map (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk (Deformation.Artin.basePoint U u₀)) R)) ≫
        S.fromSpecStalk (Deformation.Artin.basePoint U u₀) = g ≫ U.hom) :
    Deformation.Artin.IsVersalAt U q u₀ x hx ↔
      LiftsAtResiduePoint (Λ := S.presheaf.stalk (Deformation.Artin.basePoint U u₀))
        (k := ResidueField R) (alg := ResidueField.algebra R)
        (S.fromSpecStalk (Deformation.Artin.basePoint U u₀)) q U x hx
        (Spec.map (CommRingCat.ofHom (residue R)) ≫ g) := by
  let Λ := S.presheaf.stalk (Deformation.Artin.basePoint U u₀)
  let : Algebra Λ (ResidueField R) := ResidueField.algebra R
  let : Algebra Λ (U.left.residueField u₀) := Deformation.Artin.residueFieldAlgebra U u₀
  let E := completionResidueEquiv U.left u₀ e
  have hE : Spec.map (CommRingCat.ofHom E.toRingHom) ≫ U.left.fromSpecResidueField u₀ =
      Spec.map (CommRingCat.ofHom (residue R)) ≫ g := by
    simpa only [hg] using completionResidueEquiv_spec U.left u₀ e
  have hc : E.toRingHom.comp (algebraMap Λ (U.left.residueField u₀)) =
      algebraMap Λ (ResidueField R) := by
    show (CommRingCat.ofHom (E.toRingHom.comp
      (algebraMap Λ (U.left.residueField u₀)))).hom =
      (CommRingCat.ofHom (algebraMap Λ (ResidueField R))).hom
    apply congrArg CommRingCat.Hom.hom
    apply Spec.map_injective
    apply (cancel_mono (S.fromSpecStalk (Deformation.Artin.basePoint U u₀))).mp
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hk : Spec.map (CommRingCat.ofHom
        (algebraMap Λ (U.left.residueField u₀))) ≫
        S.fromSpecStalk (Deformation.Artin.basePoint U u₀) =
        U.left.fromSpecResidueField u₀ ≫ U.hom :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk (Deformation.Artin.residueFieldBasePoint U u₀)
    rw [hk, ← Category.assoc, hE, Category.assoc, ← hbase, ← Category.assoc,
      ← Spec.map_comp]
    rfl
  let Eₐ : U.left.residueField u₀ ≃ₐ[Λ] ResidueField R :=
    { __ := E, commutes' := DFunLike.congr_fun hc }
  have hequiv := liftsAtResiduePoint_iff_changeResidueField Eₐ
    (S.fromSpecStalk (Deformation.Artin.basePoint U u₀)) q U x hx (U.left.fromSpecResidueField u₀)
  have hEₐ : Spec.map (CommRingCat.ofHom Eₐ.toAlgHom.toRingHom) ≫
      U.left.fromSpecResidueField u₀ = Spec.map (CommRingCat.ofHom (residue R)) ≫ g := hE
  rw [hEₐ] at hequiv
  exact (isVersalAt_iff_liftsAtResiduePoint U q u₀ x hx).trans hequiv

/-- Every deformation carrying a map to `x` over the closed fibre is, after a vertical
arrow, a value of the associated morphism compatible with the induced cone. -/
public theorem restriction_lifts_deformationObject
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {iΛ : Spec (.of Λ) ⟶ S} {x₀ : F}
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (C : Deformation.Artin.PredeformationConstruction iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (H : BasedFunctor
      (BasedCategory.ofFunctor (CategoryOfElements.π (Deformation.restrictedCoyoneda R)))
      (BasedCategory.ofFunctor C.projection))
    {x : F} (U : Over S) (hx : (p ⋙ Over.post B.inclusion).obj x = U)
    (r : H.toFunctor.op ⋙ deformationForget C ⟶ (Functor.const _).obj x)
    (r₀ : x₀ ⟶ x) (g : Spec (.of R) ⟶ U.left)
    (hbase : ∀ α, schemeMap (p ⋙ Over.post B.inclusion)
      (deformationPointBase C (H.obj α) α.1 (H.w_obj α)) hx (r.app (.op α)) =
        Spec.map (CommRingCat.ofHom α.2.hom.toRingHom) ≫ g)
    (hclosed : ∀ α, (C.objects (H.obj α)).arrow ≫ r.app (.op α) = r₀)
    (hpoints : ∀ (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (f : Spec (.of A) ⟶ U.left),
      f ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ →
      Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫ f =
        schemeMap (p ⋙ Over.post B.inclusion) hx₀ hx r₀ →
      ∃ α : R ⟶ Deformation.artinianToComplete.obj A,
        Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫ g = f)
    (y : C.carrier) (b : (deformationForget C).obj (.op y) ⟶ x)
    (hb : (C.objects y).arrow ≫ b = r₀) :
    ∃ (β : (Deformation.restrictedCoyoneda R).Elements) (a : H.obj β ⟶ y),
      C.projection.IsHomLift (𝟙 (C.projection.obj y)) a ∧
        (deformationForget C).map a.op ≫ r.app (.op β) = b := by
  let q := p ⋙ Over.post B.inclusion
  let A := C.projection.obj y
  let hy := deformationPointBase C y A rfl
  let f := schemeMap q hy hx b
  have hf : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫ f =
      schemeMap q hx₀ hx r₀ := by
    rw [← deformationObject_residueMap C y A rfl,
      ← schemeMap_comp q hx₀ hy hx, hb]
  obtain ⟨α, hα⟩ := hpoints A f (schemeMap_over q hy hx b) hf
  let β : (Deformation.restrictedCoyoneda R).Elements := Functor.elementsMk _ A α
  let hβ := deformationPointBase C (H.obj β) A (H.w_obj β)
  obtain ⟨l, hl, _⟩ := factor_through_cartesian_schemeMap B S hS p hp hy hβ hx
    (r.app (.op β)) b (𝟙 _) (by simp) (by
      simpa only [Category.id_comp] using (hbase β).trans hα)
  have ht : (C.objects y).arrow ≫ l = (C.objects (H.obj β)).arrow := by
    apply schemeMap_cartesian_ext B S hS p hp hx₀ hβ (r.app (.op β))
    · rw [schemeMap_comp q hx₀ hy hβ, hl.1, Category.comp_id,
        deformationObject_residueMap C y A rfl,
        deformationObject_residueMap C (H.obj β) A (H.w_obj β)]
    · rw [Category.assoc, hl.2, hb, hclosed]
  obtain ⟨a, ha, he⟩ := exists_deformationMorphism C (𝟙 A) (H.w_obj β) rfl l ht (by
    simpa using hl.1)
  refine ⟨β, a, ha, ?_⟩
  show (C.morphisms _ _ a).arrow ≫ r.app (.op β) = b
  rw [he, hl.2]

/-- A morphism between two values of the associated morphism compatible with the induced
cone comes from a morphism of Artinian points. -/
private theorem restriction_lifts_deformationMorphism
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {iΛ : Spec (.of Λ) ⟶ S} {x₀ : F}
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (C : Deformation.Artin.PredeformationConstruction iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (H : BasedFunctor
      (BasedCategory.ofFunctor (CategoryOfElements.π (Deformation.restrictedCoyoneda R)))
      (BasedCategory.ofFunctor C.projection))
    {x : F} (U : Over S) (hx : (p ⋙ Over.post B.inclusion).obj x = U)
    (r : H.toFunctor.op ⋙ deformationForget C ⟶ (Functor.const _).obj x)
    (g : Spec (.of R) ⟶ U.left)
    (hbase : ∀ α, schemeMap (p ⋙ Over.post B.inclusion)
      (deformationPointBase C (H.obj α) α.1 (H.w_obj α)) hx (r.app (.op α)) =
        Spec.map (CommRingCat.ofHom α.2.hom.toRingHom) ≫ g)
    (hinj : ∀ (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (α β : R ⟶ Deformation.artinianToComplete.obj A),
      Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫ g =
        Spec.map (CommRingCat.ofHom β.hom.toRingHom) ≫ g → α = β)
    {α β : (Deformation.restrictedCoyoneda R).Elements}
    (j : H.obj β ⟶ H.obj α)
    (hj : (deformationForget C).map j.op ≫ r.app (.op β) = r.app (.op α)) :
    ∃ h : β ⟶ α, H.map h = j := by
  let q := p ⋙ Over.post B.inclusion
  let hα := deformationPointBase C (H.obj α) α.1 (H.w_obj α)
  let hβ := deformationPointBase C (H.obj β) β.1 (H.w_obj β)
  let f : β.1 ⟶ α.1 :=
    eqToHom (H.w_obj β).symm ≫ C.projection.map j ≫ eqToHom (H.w_obj α)
  have hf : C.projection.IsHomLift f j :=
    IsHomLift.of_fac C.projection f j (H.w_obj β) (H.w_obj α) rfl
  change (C.morphisms _ _ j).arrow ≫ r.app (.op β) = r.app (.op α) at hj
  have hjbase := deformationMorphism_base C f j hf hβ hα
  have he : (Deformation.restrictedCoyoneda R).map f β.2 = α.2 := by
    apply hinj α.1
    show Spec.map (CommRingCat.ofHom (f.hom.comp β.2.hom).toRingHom) ≫ g = _
    have hsplit : CommRingCat.ofHom (f.hom.comp β.2.hom).toRingHom =
        CommRingCat.ofHom β.2.hom.toRingHom ≫ CommRingCat.ofHom f.hom.toRingHom := rfl
    rw [hsplit, Spec.map_comp, Category.assoc, ← hbase β, ← hjbase,
      ← schemeMap_comp q hα hβ hx, hj, hbase α]
  let h : β ⟶ α := ⟨f, he⟩
  have : (CategoryOfElements.π (Deformation.restrictedCoyoneda R)).IsHomLift f h :=
    IsHomLift.map _ h
  have hh : C.projection.IsHomLift f (H.map h) :=
    (H.isHomLift_iff f h).mpr (IsHomLift.map _ h)
  refine ⟨h, ?_⟩
  apply (C.morphisms _ _).injective
  apply deformationMorphism_ext
  apply schemeMap_cartesian_ext B S hS p hp hα hβ (r.app (.op β))
  · exact (deformationMorphism_base C f (H.map h) hh hβ hα).trans hjbase.symm
  · have hn := r.naturality h.op
    change (deformationForget C).map (H.map h).op ≫ r.app (.op β) =
      r.app (.op α) ≫ 𝟙 x at hn
    exact (hn.trans (Category.comp_id _)).trans hj.symm

/-- Smoothness of the associated morphism is exactly the solvability of the lifting
problems for the induced cone. -/
private theorem isSmooth_iff_restriction_lifts
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {iΛ : Spec (.of Λ) ⟶ S} {x₀ : F}
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (C : Deformation.Artin.PredeformationConstruction iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (H : BasedFunctor
      (BasedCategory.ofFunctor (CategoryOfElements.π (Deformation.restrictedCoyoneda R)))
      (BasedCategory.ofFunctor C.projection))
    {x : F} (U : Over S) (hx : (p ⋙ Over.post B.inclusion).obj x = U)
    (r : H.toFunctor.op ⋙ deformationForget C ⟶ (Functor.const _).obj x)
    (g : Spec (.of R) ⟶ U.left)
    (hbase : ∀ α, schemeMap (p ⋙ Over.post B.inclusion)
      (deformationPointBase C (H.obj α) α.1 (H.w_obj α)) hx (r.app (.op α)) =
        Spec.map (CommRingCat.ofHom α.2.hom.toRingHom) ≫ g)
    (r₀ : x₀ ⟶ x)
    (hclosed : ∀ α, (C.objects (H.obj α)).arrow ≫ r.app (.op α) = r₀)
    (hpoints : ∀ (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (f : Spec (.of A) ⟶ U.left),
      f ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ →
      Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫ f =
        schemeMap (p ⋙ Over.post B.inclusion) hx₀ hx r₀ →
      ∃ α : R ⟶ Deformation.artinianToComplete.obj A,
        Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫ g = f)
    (hinj : ∀ (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (α β : R ⟶ Deformation.artinianToComplete.obj A),
      Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫ g =
        Spec.map (CommRingCat.ofHom β.hom.toRingHom) ≫ g → α = β)
    : Deformation.IsSmooth H ↔
      ∀ {A A' : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
        (f : A' ⟶ A), Function.Surjective f.hom →
        ∀ (y : C.carrier) (α : (Deformation.restrictedCoyoneda R).Elements)
          (i : y ⟶ H.obj α), C.projection.IsHomLift f i →
          ∃ b : (deformationForget C).obj (.op y) ⟶ x,
            (deformationForget C).map i.op ≫ b = r.app (.op α) := by
  constructor
  · intro hs A A' f hf y α i hi
    exact smooth_lifts_restriction_triangle H hs (deformationForget C) r f hf y α i hi
  · intro hl
    apply isSmooth_of_lifts_restriction_triangles H (deformationForget C) r
      (fun y b => (C.objects y).arrow ≫ b = r₀)
    · exact restriction_lifts_deformationObject B S hS p hp hx₀ C R H U hx r r₀ g
        hbase hclosed hpoints
    · exact restriction_lifts_deformationMorphism B S hS p hp hx₀ C R H U hx r g
        hbase hinj
    · intro A A' f hf y α i hi
      obtain ⟨b, hb⟩ := hl f hf y α i hi
      refine ⟨b, ?_, hb⟩
      rw [← (C.morphisms _ _ i).triangle, Category.assoc]
      show (C.objects (H.obj α)).arrow ≫ ((deformationForget C).map i.op ≫ b) = _
      rw [hb, hclosed]

/-- The lifting property at the residue point implies smoothness of the associated
morphism. -/
theorem isSmooth_of_liftsAtResiduePoint
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {iΛ : Spec (.of Λ) ⟶ S} {x₀ : F}
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (C : Deformation.Artin.PredeformationConstruction iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (H : BasedFunctor
      (BasedCategory.ofFunctor (CategoryOfElements.π (Deformation.restrictedCoyoneda R)))
      (BasedCategory.ofFunctor C.projection))
    {x : F} (U : Over S) (hx : (p ⋙ Over.post B.inclusion).obj x = U)
    (r : H.toFunctor.op ⋙ deformationForget C ⟶ (Functor.const _).obj x)
    (g : Spec (.of R) ⟶ U.left)
    (hbase : ∀ α, schemeMap (p ⋙ Over.post B.inclusion)
      (deformationPointBase C (H.obj α) α.1 (H.w_obj α)) hx (r.app (.op α)) =
        Spec.map (CommRingCat.ofHom α.2.hom.toRingHom) ≫ g)
    (r₀ : x₀ ⟶ x)
    (hclosed : ∀ α, (C.objects (H.obj α)).arrow ≫ r.app (.op α) = r₀)
    (hpoints : ∀ (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (f : Spec (.of A) ⟶ U.left),
      f ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ →
      Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫ f =
        schemeMap (p ⋙ Over.post B.inclusion) hx₀ hx r₀ →
      ∃ α : R ⟶ Deformation.artinianToComplete.obj A,
        Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫ g = f)
    (hinj : ∀ (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (α β : R ⟶ Deformation.artinianToComplete.obj A),
      Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫ g =
        Spec.map (CommRingCat.ofHom β.hom.toRingHom) ≫ g → α = β)
    (hl : LiftsAtResiduePoint iΛ (p ⋙ Over.post B.inclusion) U x hx
      (schemeMap (p ⋙ Over.post B.inclusion) hx₀ hx r₀)) : Deformation.IsSmooth H := by
  apply (isSmooth_iff_restriction_lifts B S hS p hp hx₀ C R H U hx r g hbase
    r₀ hclosed hpoints hinj).mpr
  intro A A' f hf y α i hi
  have : C.projection.IsHomLift f i := hi
  have hA : α.1 = A := (H.w_obj α).symm.trans (IsHomLift.codomain_eq C.projection f i)
  subst A
  let hα := deformationPointBase C (H.obj α) α.1 (H.w_obj α)
  let hy := deformationPointBase C y A' (IsHomLift.domain_eq C.projection f i)
  apply hl α.1 A' f hf (C.objects (H.obj α)).point (C.objects y).point hα hy
    (C.morphisms _ _ i).arrow (deformationMorphism_base C f i hi hy hα) (r.app (.op α))
  rw [← deformationObject_residueMap C (H.obj α) α.1 (H.w_obj α),
    ← schemeMap_comp (p ⋙ Over.post B.inclusion) hx₀ hα hx, hclosed]

/-- Smoothness of the associated morphism implies the lifting property at the residue
point. -/
public theorem liftsAtResiduePoint_of_isSmooth
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {iΛ : Spec (.of Λ) ⟶ S} {x₀ : F}
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (C : Deformation.Artin.PredeformationConstruction iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (H : BasedFunctor
      (BasedCategory.ofFunctor (CategoryOfElements.π (Deformation.restrictedCoyoneda R)))
      (BasedCategory.ofFunctor C.projection))
    {x : F} (U : Over S) (hx : (p ⋙ Over.post B.inclusion).obj x = U)
    (r : H.toFunctor.op ⋙ deformationForget C ⟶ (Functor.const _).obj x)
    (g : Spec (.of R) ⟶ U.left)
    (hbase : ∀ α, schemeMap (p ⋙ Over.post B.inclusion)
      (deformationPointBase C (H.obj α) α.1 (H.w_obj α)) hx (r.app (.op α)) =
        Spec.map (CommRingCat.ofHom α.2.hom.toRingHom) ≫ g)
    (r₀ : x₀ ⟶ x)
    (hpoints : ∀ (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (f : Spec (.of A) ⟶ U.left),
      f ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ →
      Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫ f =
        schemeMap (p ⋙ Over.post B.inclusion) hx₀ hx r₀ →
      ∃ α : R ⟶ Deformation.artinianToComplete.obj A,
        Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫ g = f)
    (hs : Deformation.IsSmooth H) :
    LiftsAtResiduePoint iΛ (p ⋙ Over.post B.inclusion) U x hx
      (schemeMap (p ⋙ Over.post B.inclusion) hx₀ hx r₀) := by
  intro A A' f hf y z hy hz i hi a ha
  let q := p ⋙ Over.post B.inclusion
  obtain ⟨α, hα⟩ := hpoints A (schemeMap q hy hx a) (schemeMap_over q hy hx a) ha
  let β : (Deformation.restrictedCoyoneda R).Elements := Functor.elementsMk _ A α
  let hβ := deformationPointBase C (H.obj β) A (H.w_obj β)
  obtain ⟨v, hv, _⟩ := factor_through_cartesian_schemeMap B S hS p hp hβ hy hx
    a (r.app (.op β)) (𝟙 _) (by simp) (by
      simpa only [Category.id_comp] using ((hbase β).trans hα).symm)
  have : IsIso v := schemeMap_id_isIso B S hS p hp hβ hy v hv.1
  let d : Deformation.Artin.DeformationObject iΛ q x₀ hx₀ := {
    algebra := A'
    point := z
    arrow := (C.objects (H.obj β)).arrow ≫ v ≫ i
    base := hz
    arrow_base := by
      show schemeMap q hx₀ hz ((C.objects (H.obj β)).arrow ≫ v ≫ i) = _
      rw [schemeMap_comp q hx₀ hβ hz, schemeMap_comp q hβ hy hz,
        hv.1, Category.id_comp, hi, deformationObject_residueMap C (H.obj β) A (H.w_obj β),
        ← Spec.map_comp]
      exact congrArg Spec.map (congrArg CommRingCat.ofHom (residueMap_comp f))
  }
  let c := C.objects.symm d
  have hc : C.objects c = d := C.objects.apply_symm_apply d
  have hcp : (C.objects c).point = z := congrArg Deformation.Artin.DeformationObject.point hc
  have hcπ : C.projection.obj c = A' :=
    (C.object_projection c).trans (congrArg Deformation.Artin.DeformationObject.algebra hc)
  let hcbase := deformationPointBase C c A' hcπ
  let w : (C.objects (H.obj β)).point ⟶ (C.objects c).point :=
    (v ≫ i) ≫ eqToHom hcp.symm
  have hct : (C.objects (H.obj β)).arrow ≫ w = (C.objects c).arrow := by
    apply (cancel_mono (eqToHom hcp)).mp
    simpa [w, Category.assoc] using (deformationObject_arrow_congr hc).symm
  have hcw : schemeMap q hβ hcbase w = Spec.map (CommRingCat.ofHom f.hom.toRingHom) := by
    rw [schemeMap_comp_eqToHom q hβ hz hcbase hcp.symm (v ≫ i),
      schemeMap_comp q hβ hy hz, hv.1, Category.id_comp, hi]
  obtain ⟨j, hj, hjw⟩ := exists_deformationMorphism C f hcπ (H.w_obj β) w hct hcw
  obtain ⟨b, hb⟩ := smooth_lifts_restriction_triangle H hs (deformationForget C) r f hf c β j hj
  refine ⟨eqToHom hcp.symm ≫ b, ?_⟩
  apply (cancel_epi v).mp
  change (C.morphisms _ _ j).arrow ≫ b = r.app (.op β) at hb
  rw [hjw] at hb
  simpa only [w, Category.assoc, hv.2] using hb

end Deformation.Artin

end
