module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityStalkBase

/-!
# Transporting openness of versality

Openness of versality (Stacks 07XQ, part (1)) for a category `X` over the schemes over `S` is the
statement that whenever an object over a scheme `U` locally of finite type over `S` is versal at
a finite type point `u₀`, it is versal at every finite type point of a neighbourhood of `u₀`.
This file records that statement as `Deformation.Artin.HasOpenVersality` and transports it

* along a fully faithful functor over the base which is essentially surjective by vertical
  isomorphisms, in particular along any equivalence over the big fppf site
  (`Deformation.Artin.hasOpenVersality_of_equivalenceOver`), and
* from a category over the schemes over `V` to the same category over the schemes over `S`
  through a morphism `g : V ⟶ S` (`Deformation.Artin.hasOpenVersality_comp_overMap`).

The second transport is what the proof of Stacks 07Y5 means by "Axiom [5] for `Y` follows
directly from openness of versality for `Δ_𝒳`": openness of versality of the diagonal is
openness of versality of each `(Sch/V)_{fppf} ×_{𝒳 × 𝒳} 𝒳` *over `V`*, while axiom `[5]` for
`Y` is openness of versality over `S`.

## Main definitions

* `Deformation.Artin.HasOpenVersality`: openness of versality, written out.

## Main results

* `Deformation.Artin.liftsAtResiduePoint_iff_of_fullyFaithful`: the lifting property defining
  versality is invariant under a fully faithful functor over the base which is essentially
  surjective by vertical isomorphisms.
* `Deformation.Artin.hasOpenVersality_of_equivalenceOver`: openness of versality transports
  along an equivalence over the big fppf site.
* `Deformation.Artin.isVersalAt_comp_overMap_iff`: versality is unchanged on regarding a
  category over the schemes over `V` as one over the schemes over `S`.
* `Deformation.Artin.hasOpenVersality_comp_overMap`: the corresponding transport of openness
  of versality.

## Implementation notes

`Deformation.Artin.IsOpenVersality` takes, besides the structure functor `q`, a proof that `q`
is fibred in groupoids. For `q = p ⋙ Over.post B.inclusion` with `p` a category fibred in
groupoids over a big fppf site `B` that hypothesis is unsatisfiable as soon as `p` has an
object: `q` would have to lift every morphism of schemes into the base of that object, and the
schemes of size at least the cutoff of `B` carry no object. `Deformation.Artin.HasOpenVersality`
is the body of `Deformation.Artin.IsOpenVersality` without that hypothesis, which is how the
openness hypothesis of Artin's criterion is stated.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

namespace Deformation.Artin

universe u v₁ v₂ w₁ w₂

/-- **Openness of versality** (Stacks 07XQ, part (1)), written out: for every scheme `U` locally
of finite type over `S`, every object `x` of `X` over `U` and every finite type point `u₀` of `U`
at which `x` is versal, there is an open neighbourhood of `u₀` at every finite type point of
which `x` is versal. This is the body of `Deformation.Artin.IsOpenVersality`, without its
fibred-in-groupoids hypothesis on `q`, which is unsatisfiable for a nonempty category over a
big fppf site composed with `Over.post`. -/
public abbrev HasOpenVersality {S : Scheme.{u}} {X : Type v₁} [Category.{w₁} X]
    (q : X ⥤ Over S) : Prop :=
  ∀ (U : Over S), LocallyOfFiniteType U.hom →
    ∀ (x : X) (hx : q.obj x = U) (u₀ : U.left),
      IsFiniteTypePoint u₀ →
      IsVersalAt U q u₀ x hx →
      ∃ V : U.left.Opens, u₀ ∈ V.1 ∧
        ∀ (u : U.left), u ∈ V.1 → IsFiniteTypePoint u → IsVersalAt U q u x hx

/-! ### Transport along a fully faithful functor over the base -/

section FullyFaithful

variable {S : Scheme.{u}} {X₁ : Type v₁} [Category.{w₁} X₁] {X₂ : Type v₂} [Category.{w₂} X₂]

/-- The underlying morphism of schemes of the image of a morphism under a functor over the
base is the underlying morphism of schemes of the morphism. -/
theorem schemeMap_map_of_comp_eq (q₁ : X₁ ⥤ Over S) (q₂ : X₂ ⥤ Over S) (Ψ : X₂ ⥤ X₁)
    (hΨ : Ψ ⋙ q₁ = q₂) {y z : X₂} {Y Z : Over S} (hy : q₂.obj y = Y) (hz : q₂.obj z = Z)
    (hy' : q₁.obj (Ψ.obj y) = Y) (hz' : q₁.obj (Ψ.obj z) = Z) (f : y ⟶ z) :
    schemeMap q₁ hy' hz' (Ψ.map f) = schemeMap q₂ hy hz f := by
  subst hΨ
  rfl

/-- The underlying morphism of schemes of a vertical morphism is the identity. -/
theorem schemeMap_eq_id_of_isHomLift (q : X₁ ⥤ Over S) {y y' : X₁} {Y : Over S}
    (hy : q.obj y = Y) (hy' : q.obj y' = Y) (φ : y ⟶ y') [q.IsHomLift (𝟙 (q.obj y)) φ] :
    schemeMap q hy hy' φ = 𝟙 Y.left := by
  subst hy
  have h := IsHomLift.fac' q (𝟙 (q.obj y)) φ
  simp only [schemeMap, h, Category.id_comp, eqToHom_trans, Over.eqToHom_left, eqToHom_refl]

variable {Λ k : Type u} [CommRing Λ] [Field k] [alg : Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)

/-- **The lifting property defining versality is invariant under a fully faithful functor over
the base which is essentially surjective by vertical isomorphisms.** Let `Ψ : X₂ ⥤ X₁` commute
strictly with the structure functors to the schemes over `S`, be full and faithful, and let
every object of `X₁` be vertically isomorphic to an object in its image. Then an object `x` of
`X₂` has the lifting property of versality exactly when `Ψ x` has it. -/
theorem liftsAtResiduePoint_iff_of_fullyFaithful (q₁ : X₁ ⥤ Over S) (q₂ : X₂ ⥤ Over S)
    (Ψ : X₂ ⥤ X₁) (hΨ : Ψ ⋙ q₁ = q₂) [Ψ.Full] [Ψ.Faithful]
    (hess : ∀ y₁ : X₁, ∃ (y₂ : X₂) (e : y₁ ≅ Ψ.obj y₂), q₁.IsHomLift (𝟙 (q₁.obj y₁)) e.hom)
    (U : Over S) (x : X₂) (hx : q₂.obj x = U) (hx' : q₁.obj (Ψ.obj x) = U)
    (κ : Spec (.of k) ⟶ U.left) :
    LiftsAtResiduePoint iΛ q₁ U (Ψ.obj x) hx' κ ↔ LiftsAtResiduePoint iΛ q₂ U x hx κ := by
  constructor
  · intro h A B f hf y z hy hz i hi a ha
    have hy' : q₁.obj (Ψ.obj y) = _ := (Functor.congr_obj hΨ y).trans hy
    have hz' : q₁.obj (Ψ.obj z) = _ := (Functor.congr_obj hΨ z).trans hz
    obtain ⟨b, hb⟩ := h A B f hf (Ψ.obj y) (Ψ.obj z) hy' hz' (Ψ.map i)
      ((schemeMap_map_of_comp_eq q₁ q₂ Ψ hΨ hy hz hy' hz' i).trans hi) (Ψ.map a)
      ((congrArg _ (schemeMap_map_of_comp_eq q₁ q₂ Ψ hΨ hy hx hy' hx' a)).trans ha)
    refine ⟨Ψ.preimage b, Ψ.map_injective ?_⟩
    rw [Ψ.map_comp, Ψ.map_preimage, hb]
  · intro h A B f hf y z hy hz i hi a ha
    obtain ⟨y₂, ey, hey⟩ := hess y
    obtain ⟨z₂, ez, hez⟩ := hess z
    have hy₁ : q₁.obj (Ψ.obj y₂) = _ :=
      (IsHomLift.codomain_eq q₁ (𝟙 (q₁.obj y)) ey.hom).trans hy
    have hz₁ : q₁.obj (Ψ.obj z₂) = _ :=
      (IsHomLift.codomain_eq q₁ (𝟙 (q₁.obj z)) ez.hom).trans hz
    have hy₂ : q₂.obj y₂ = _ := (Functor.congr_obj hΨ y₂).symm.trans hy₁
    have hz₂ : q₂.obj z₂ = _ := (Functor.congr_obj hΨ z₂).symm.trans hz₁
    let i₂ : y₂ ⟶ z₂ := Ψ.preimage (ey.inv ≫ i ≫ ez.hom)
    let a₂ : y₂ ⟶ x := Ψ.preimage (ey.inv ≫ a)
    have hidy' : schemeMap q₁ hy₁ hy ey.inv = 𝟙 _ := by
      have h2 := schemeMap_comp q₁ hy hy₁ hy ey.hom ey.inv
      rw [ey.hom_inv_id, schemeMap_eq_id_of_isHomLift q₁ hy hy₁ ey.hom, Category.id_comp] at h2
      rw [← h2]
      simp [schemeMap]
    have hidz' : schemeMap q₁ hz hz₁ ez.hom = 𝟙 _ := schemeMap_eq_id_of_isHomLift q₁ hz hz₁ ez.hom
    have hi₂ : schemeMap q₂ hy₂ hz₂ i₂ = Spec.map (CommRingCat.ofHom f.hom.toRingHom) := by
      rw [← schemeMap_map_of_comp_eq q₁ q₂ Ψ hΨ hy₂ hz₂ hy₁ hz₁ i₂, Ψ.map_preimage,
        schemeMap_comp q₁ hy₁ hy hz₁ ey.inv (i ≫ ez.hom), schemeMap_comp q₁ hy hz hz₁ i ez.hom,
        hidy', hidz', Category.id_comp, Category.comp_id, hi]
    have ha₂ : Spec.map (CommRingCat.ofHom (residueMap A)) ≫ schemeMap q₂ hy₂ hx a₂ = κ := by
      rw [← schemeMap_map_of_comp_eq q₁ q₂ Ψ hΨ hy₂ hx hy₁ hx' a₂, Ψ.map_preimage,
        schemeMap_comp q₁ hy₁ hy hx' ey.inv a, hidy', Category.id_comp, ha]
    obtain ⟨b₂, hb₂⟩ := h A B f hf y₂ z₂ hy₂ hz₂ i₂ hi₂ a₂ ha₂
    refine ⟨ez.hom ≫ Ψ.map b₂, ?_⟩
    have hb := congrArg Ψ.map hb₂
    rw [Ψ.map_comp, Ψ.map_preimage, Ψ.map_preimage] at hb
    rw [← cancel_epi ey.inv, ← hb]
    simp only [Category.assoc]

/-- **Openness of versality transports along a fully faithful functor over the base which is
essentially surjective by vertical isomorphisms.** -/
theorem hasOpenVersality_of_fullyFaithful (q₁ : X₁ ⥤ Over S) (q₂ : X₂ ⥤ Over S)
    (Ψ : X₂ ⥤ X₁) (hΨ : Ψ ⋙ q₁ = q₂) [Ψ.Full] [Ψ.Faithful]
    (hess : ∀ y₁ : X₁, ∃ (y₂ : X₂) (e : y₁ ≅ Ψ.obj y₂), q₁.IsHomLift (𝟙 (q₁.obj y₁)) e.hom)
    (h : HasOpenVersality q₁) : HasOpenVersality q₂ := by
  intro U hU x hx u₀ hu₀ hv
  have hx' : q₁.obj (Ψ.obj x) = U := (Functor.congr_obj hΨ x).trans hx
  have key : ∀ u : U.left, IsVersalAt U q₁ u (Ψ.obj x) hx' ↔ IsVersalAt U q₂ u x hx :=
    fun u => liftsAtResiduePoint_iff_of_fullyFaithful (alg := residueFieldAlgebra U u)
      (S.fromSpecStalk (basePoint U u)) q₁ q₂ Ψ hΨ hess U x hx hx'
      (U.left.fromSpecResidueField u)
  obtain ⟨V, hV, hW⟩ := h U hU (Ψ.obj x) hx' u₀ hu₀ ((key u₀).2 hv)
  exact ⟨V, hV, fun u hu hfu => (key u).1 (hW u hu hfu)⟩

/-- **Openness of versality transports along an equivalence over the big fppf site.** If `P`
and `Q` are equivalent over the big fppf site of `S` and `P` (composed with the inclusion into
the schemes over `S`) has openness of versality, so has `Q`. -/
theorem hasOpenVersality_of_equivalenceOver {B : BigFppfSite.{u}} {hS : B.Contains S}
    {P : X₁ ⥤ BigFppfOver B S hS} {Q : X₂ ⥤ BigFppfOver B S hS}
    (e : StacksRepresentableCFG.EquivalenceOver (𝒞 := BigFppfOver B S hS) P Q)
    (h : HasOpenVersality (P ⋙ Over.post B.inclusion)) :
    HasOpenVersality (Q ⋙ Over.post B.inclusion) := by
  have : e.inv.functor.IsEquivalence := e.toEquivalence.isEquivalence_inverse
  refine hasOpenVersality_of_fullyFaithful (P ⋙ Over.post B.inclusion)
    (Q ⋙ Over.post B.inclusion) e.inv.functor
    (by rw [← Functor.assoc, e.inv.w]) ?_ h
  intro y₁
  refine ⟨e.hom.functor.obj y₁, e.unitIso.app y₁, ?_⟩
  have := e.isHomLift_unitIso_hom_app y₁
  have hc := IsHomLift.codomain_eq P (𝟙 (P.obj y₁)) (e.unitIso.hom.app y₁)
  refine IsHomLift.of_fac' _ _ _ rfl (congrArg (Over.post B.inclusion).obj hc) ?_
  apply Over.OverMorphism.ext
  simp [Functor.comp_map, IsHomLift.fac' P (𝟙 (P.obj y₁)) (e.unitIso.hom.app y₁),
    Over.eqToHom_left]
  rfl

end FullyFaithful

/-! ### Local algebras over the local ring of a point -/

section PointStalk

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {V : Scheme.{u}} (v : V)
  [algStalk : Algebra (V.presheaf.stalk v) k]
  (hloc : IsLocalHom (algebraMap (V.presheaf.stalk v) k))

/-- A local homomorphism `r : C ⟶ D` of local algebras over `𝒪_{V,v}` is linear as soon as the
induced morphisms `Spec C ⟶ V` and `Spec D ⟶ V` are compatible. -/
private theorem comp_algebraMap_eq_of_spec_comp {C D : Type u} [CommRing C] [CommRing D]
    [IsLocalRing D] [Algebra (V.presheaf.stalk v) C] [Algebra (V.presheaf.stalk v) D]
    [IsLocalHom (algebraMap (V.presheaf.stalk v) C)]
    [IsLocalHom (algebraMap (V.presheaf.stalk v) D)] (r : C →+* D) [IsLocalHom r]
    (h : Spec.map (CommRingCat.ofHom (algebraMap (V.presheaf.stalk v) D)) ≫ V.fromSpecStalk v =
      Spec.map (CommRingCat.ofHom r) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (V.presheaf.stalk v) C)) ≫ V.fromSpecStalk v) :
    r.comp (algebraMap (V.presheaf.stalk v) C) = algebraMap (V.presheaf.stalk v) D := by
  have : IsLocalHom (r.comp (algebraMap (V.presheaf.stalk v) C)) :=
    RingHom.isLocalHom_comp _ _
  refine localHom_fromSpecStalk_injective V v _ _ ?_
  rw [show CommRingCat.ofHom (r.comp (algebraMap (V.presheaf.stalk v) C)) =
      CommRingCat.ofHom (algebraMap (V.presheaf.stalk v) C) ≫ CommRingCat.ofHom r from rfl,
    Spec.map_comp, Category.assoc]
  exact h.symm

include hloc in
/-- The closed point of `Spec C` maps to `v` under a morphism `φ : Spec C ⟶ V` whose residue
point is the chosen one. -/
theorem closedPoint_eq_of_residuePoint (C : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (φ : Spec (.of (C : Type u)) ⟶ V)
    (hres : Spec.map (CommRingCat.ofHom (residueMap C)) ≫ φ =
      Spec.map (CommRingCat.ofHom (algebraMap (V.presheaf.stalk v) k)) ≫ V.fromSpecStalk v) :
    φ (closedPoint (C : Type u)) = v := by
  have := isLocalHom_residueMap C
  have : IsLocalHom (CommRingCat.ofHom (residueMap C)).hom := isLocalHom_residueMap C
  have : IsLocalHom (CommRingCat.ofHom (algebraMap (V.presheaf.stalk v) k)).hom := hloc
  have h := congrArg (fun g : Spec (CommRingCat.of k) ⟶ V => g (closedPoint k)) hres
  rw [closedPoint_comp_eq (CommRingCat.ofHom (residueMap C)) φ,
    closedPoint_comp_eq (CommRingCat.ofHom (algebraMap (V.presheaf.stalk v) k))
      (V.fromSpecStalk v), Scheme.fromSpecStalk_closedPoint] at h
  exact h

/-- **The algebra structure over the local ring of `V` at `v` defined by a point.** An object of
`𝒞_Λ` together with a morphism `φ : Spec C ⟶ V` whose residue point is the chosen one is an
algebra over `𝒪_{V,v}`: `Deformation.Artin.exists_localHom_fromSpecStalk` factors `φ` through
`Spec 𝒪_{V,v}` by a local homomorphism. This generalizes `Deformation.Artin.stalkAlgebra`, where
`φ` is the structure morphism `Spec C ⟶ Spec Λ ⟶ V`. -/
@[instance_reducible]
public def pointStalkAlgebra (C : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (φ : Spec (.of (C : Type u)) ⟶ V)
    (hres : Spec.map (CommRingCat.ofHom (residueMap C)) ≫ φ =
      Spec.map (CommRingCat.ofHom (algebraMap (V.presheaf.stalk v) k)) ≫ V.fromSpecStalk v) :
    Algebra (V.presheaf.stalk v) (C : Type u) :=
  (Classical.choose (exists_localHom_fromSpecStalk V v φ
    (closedPoint_eq_of_residuePoint v hloc C φ hres))).toAlgebra

variable (C : ArtinianLocalAlgCat.{u, u, u} Λ k) (φ : Spec (.of (C : Type u)) ⟶ V)
  (hres : Spec.map (CommRingCat.ofHom (residueMap C)) ≫ φ =
    Spec.map (CommRingCat.ofHom (algebraMap (V.presheaf.stalk v) k)) ≫ V.fromSpecStalk v)

/-- The structure map of `Deformation.Artin.pointStalkAlgebra` is a local homomorphism. -/
theorem isLocalHom_pointStalkAlgebra :
    letI := pointStalkAlgebra v hloc C φ hres
    IsLocalHom (algebraMap (V.presheaf.stalk v) (C : Type u)) :=
  (Classical.choose_spec (exists_localHom_fromSpecStalk V v φ
    (closedPoint_eq_of_residuePoint v hloc C φ hres))).1

/-- The point `φ` factors through `Spec 𝒪_{V,v}` by `Deformation.Artin.pointStalkAlgebra`. -/
theorem specMap_pointStalkAlgebra :
    letI := pointStalkAlgebra v hloc C φ hres
    Spec.map (CommRingCat.ofHom (algebraMap (V.presheaf.stalk v) (C : Type u))) ≫
        V.fromSpecStalk v = φ :=
  (Classical.choose_spec (exists_localHom_fromSpecStalk V v φ
    (closedPoint_eq_of_residuePoint v hloc C φ hres))).2

include hres in
/-- The composite `𝒪_{V,v} ⟶ C ⟶ k` is the structure map of `k`: both are local homomorphisms
inducing the same morphism `Spec k ⟶ V`. -/
theorem residueMap_comp_pointStalkAlgebra :
    letI := pointStalkAlgebra v hloc C φ hres
    (residueMap C).comp (algebraMap (V.presheaf.stalk v) (C : Type u)) =
      algebraMap (V.presheaf.stalk v) k := by
  let := pointStalkAlgebra v hloc C φ hres
  have := isLocalHom_pointStalkAlgebra v hloc C φ hres
  have := isLocalHom_residueMap C
  have := hloc
  exact comp_algebraMap_eq_of_spec_comp v (residueMap C)
    (by rw [specMap_pointStalkAlgebra v hloc C φ hres]; exact hres.symm)

/-- **An object of `𝒞_Λ` with a point of `V` as an object of `𝒞_{𝒪_{V,v}}`.** The carrier and
the residue identification are those of `C`; only the algebra structure is replaced by
`Deformation.Artin.pointStalkAlgebra`. -/
public def pointStalkObj : ArtinianLocalAlgCat.{u, u, u} (V.presheaf.stalk v) k where
  carrier := C
  algebra := pointStalkAlgebra v hloc C φ hres
  residueEquiv :=
    letI := pointStalkAlgebra v hloc C φ hres
    { C.residueEquiv with
      commutes' := fun t =>
        RingHom.congr_fun (residueMap_comp_pointStalkAlgebra v hloc C φ hres) t }

variable (A B : ArtinianLocalAlgCat.{u, u, u} Λ k)
  (φA : Spec (.of (A : Type u)) ⟶ V) (φB : Spec (.of (B : Type u)) ⟶ V)
  (hresA : Spec.map (CommRingCat.ofHom (residueMap A)) ≫ φA =
    Spec.map (CommRingCat.ofHom (algebraMap (V.presheaf.stalk v) k)) ≫ V.fromSpecStalk v)
  (hresB : Spec.map (CommRingCat.ofHom (residueMap B)) ≫ φB =
    Spec.map (CommRingCat.ofHom (algebraMap (V.presheaf.stalk v) k)) ≫ V.fromSpecStalk v)
  (f : B ⟶ A) (hf : Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ φB = φA)

include hf in
/-- A morphism of `𝒞_Λ` compatible with the two points is `𝒪_{V,v}`-linear. -/
theorem hom_comp_pointStalkAlgebra :
    letI := pointStalkAlgebra v hloc A φA hresA
    letI := pointStalkAlgebra v hloc B φB hresB
    f.hom.toRingHom.comp (algebraMap (V.presheaf.stalk v) (B : Type u)) =
      algebraMap (V.presheaf.stalk v) (A : Type u) := by
  let := pointStalkAlgebra v hloc A φA hresA
  let := pointStalkAlgebra v hloc B φB hresB
  have := isLocalHom_pointStalkAlgebra v hloc A φA hresA
  have := isLocalHom_pointStalkAlgebra v hloc B φB hresB
  have := f.isLocal
  exact comp_algebraMap_eq_of_spec_comp v f.hom.toRingHom
    (by rw [specMap_pointStalkAlgebra v hloc A φA hresA, ← hf,
      specMap_pointStalkAlgebra v hloc B φB hresB])

/-- **A morphism of `𝒞_Λ` compatible with the points as a morphism of `𝒞_{𝒪_{V,v}}`**, with
the same underlying ring map. -/
public def pointStalkHom :
    pointStalkObj v hloc B φB hresB ⟶ pointStalkObj v hloc A φA hresA where
  hom :=
    letI := pointStalkAlgebra v hloc A φA hresA
    letI := pointStalkAlgebra v hloc B φB hresB
    { toRingHom := f.hom.toRingHom
      commutes' := fun t =>
        RingHom.congr_fun (hom_comp_pointStalkAlgebra v hloc A B φA φB hresA hresB f hf) t }
  isLocal := f.isLocal
  residue_comm := f.residue_comm

end PointStalk

/-! ### Changing the base scheme along a morphism -/

section BaseChange

variable {V S : Scheme.{u}} (g : V ⟶ S) {X : Type v₁} [Category.{w₁} X] (q : X ⥤ Over V)

/-- An object of the slice is the slice object of its structure morphism transported along an
identification of its source. -/
theorem over_eq_mk_eqToHom_comp {Y : Over V} {T : Scheme.{u}} (h : Y.left = T) :
    Y = Over.mk (eqToHom h.symm ≫ Y.hom) := by
  obtain ⟨L, ⟨⟨⟩⟩, f⟩ := Y
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  rfl

/-- **Versality over `S` implies versality over `V`.** -/
theorem isVersalAt_of_isVersalAt_comp_overMap (U : Over V) (u₀ : U.left) (x : X)
    (hx : q.obj x = U) (hx' : (q ⋙ Over.map g).obj x = (Over.map g).obj U)
    (h : IsVersalAt ((Over.map g).obj U) (q ⋙ Over.map g) u₀ x hx') :
    IsVersalAt U q u₀ x hx := by
  let := residueFieldAlgebra U u₀
  have L := @liftsAtResiduePoint_base_of_isVersalAt (V.presheaf.stalk (basePoint U u₀)) _ S
    (V.fromSpecStalk (basePoint U u₀) ≫ g) ((Over.map g).obj U) X _ (q ⋙ Over.map g) u₀ x hx'
    (residueFieldAlgebra U u₀) h
  intro A B f hf y z hy hz i hi a ha
  have hobj : ∀ (C : ArtinianLocalAlgCat.{u, u, u} (V.presheaf.stalk
      (basePoint U u₀)) (U.left.residueField u₀)) (w : X),
      q.obj w = Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap (V.presheaf.stalk (basePoint U u₀)) C)) ≫
          V.fromSpecStalk (basePoint U u₀)) →
      (q ⋙ Over.map g).obj w = Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap (V.presheaf.stalk (basePoint U u₀)) C)) ≫
          V.fromSpecStalk (basePoint U u₀) ≫ g) := fun C w h => by
    rw [Functor.comp_obj, h]
    exact congrArg Over.mk (Category.assoc _ _ _)
  exact L A B f hf y z (hobj A y hy) (hobj B z hz) i hi a ha

/-- **Versality over `V` implies versality over `S`.** A lifting problem over the local ring of
`S` is one over the local ring of `V`: each Artinian local algebra occurring in it carries the
point of `V` given by its object, whose residue point is the chosen one, and so is an algebra
over the local ring of `V` (`Deformation.Artin.pointStalkObj`), compatibly with the
surjection. -/
theorem isVersalAt_comp_overMap_of_isVersalAt (U : Over V) (u₀ : U.left) (x : X)
    (hx : q.obj x = U) (hx' : (q ⋙ Over.map g).obj x = (Over.map g).obj U)
    (h : IsVersalAt U q u₀ x hx) :
    IsVersalAt ((Over.map g).obj U) (q ⋙ Over.map g) u₀ x hx' := by
  let algV := residueFieldAlgebra U u₀
  let algS : Algebra (S.presheaf.stalk (basePoint ((Over.map g).obj U) u₀))
      (((Over.map g).obj U).left.residueField u₀) := residueFieldAlgebra ((Over.map g).obj U) u₀
  let algS' : Algebra (S.presheaf.stalk (basePoint ((Over.map g).obj U) u₀))
      (U.left.residueField u₀) := residueFieldAlgebra ((Over.map g).obj U) u₀
  have hloc : IsLocalHom
      (algebraMap (V.presheaf.stalk (basePoint U u₀)) (U.left.residueField u₀)) :=
    show IsLocalHom (Scheme.stalkClosedPointTo (residueFieldBasePoint U u₀)).hom from
      inferInstance
  have hκ : U.left.fromSpecResidueField u₀ ≫ U.hom =
      Spec.map (CommRingCat.ofHom
        (algebraMap (V.presheaf.stalk (basePoint U u₀)) (U.left.residueField u₀))) ≫
        V.fromSpecStalk (basePoint U u₀) :=
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (residueFieldBasePoint U u₀)).symm
  intro A B f hf y z hy hz i hi a ha
  have hLy : (q.obj y).left = Spec (.of (A : Type u)) := congrArg Over.left hy
  have hLz : (q.obj z).left = Spec (.of (B : Type u)) := congrArg Over.left hz
  let φy : Spec (.of (A : Type u)) ⟶ V := eqToHom hLy.symm ≫ (q.obj y).hom
  let φz : Spec (.of (B : Type u)) ⟶ V := eqToHom hLz.symm ≫ (q.obj z).hom
  have hyV : q.obj y = Over.mk φy := over_eq_mk_eqToHom_comp hLy
  have hzV : q.obj z = Over.mk φz := over_eq_mk_eqToHom_comp hLz
  have hiy : schemeMap q hyV hzV i = Spec.map (CommRingCat.ofHom f.hom.toRingHom) := hi
  have hfφ : Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ φz = φy := by
    rw [← hiy]
    exact schemeMap_over q hyV hzV i
  have hresA : Spec.map (CommRingCat.ofHom (residueMap A)) ≫ φy =
      Spec.map (CommRingCat.ofHom
        (algebraMap (V.presheaf.stalk (basePoint U u₀)) (U.left.residueField u₀))) ≫
        V.fromSpecStalk (basePoint U u₀) := by
    have hover : schemeMap q hyV hx a ≫ U.hom = φy := schemeMap_over q hyV hx a
    have ha' : Spec.map (CommRingCat.ofHom (residueMap A)) ≫ schemeMap q hyV hx a =
        U.left.fromSpecResidueField u₀ := ha
    rw [← hover, ← Category.assoc, ha', hκ]
  have hresB : Spec.map (CommRingCat.ofHom (residueMap B)) ≫ φz =
      Spec.map (CommRingCat.ofHom
        (algebraMap (V.presheaf.stalk (basePoint U u₀)) (U.left.residueField u₀))) ≫
        V.fromSpecStalk (basePoint U u₀) := by
    have hrm : CommRingCat.ofHom (residueMap B) =
        CommRingCat.ofHom f.hom.toRingHom ≫ CommRingCat.ofHom (residueMap A) := by
      ext b
      exact (f.residue_comm b).symm
    rwa [hrm, Spec.map_comp, Category.assoc, hfφ]
  let A' := pointStalkObj (basePoint U u₀) hloc A φy hresA
  let B' := pointStalkObj (basePoint U u₀) hloc B φz hresB
  let f' : B' ⟶ A' := pointStalkHom (basePoint U u₀) hloc A B φy φz hresA hresB f hfφ
  have hy'' : q.obj y = Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap (V.presheaf.stalk (basePoint U u₀)) (A' : Type u))) ≫
        V.fromSpecStalk (basePoint U u₀)) :=
    hyV.trans (congrArg Over.mk
      (specMap_pointStalkAlgebra (basePoint U u₀) hloc A φy hresA).symm)
  have hz'' : q.obj z = Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap (V.presheaf.stalk (basePoint U u₀)) (B' : Type u))) ≫
        V.fromSpecStalk (basePoint U u₀)) :=
    hzV.trans (congrArg Over.mk
      (specMap_pointStalkAlgebra (basePoint U u₀) hloc B φz hresB).symm)
  exact h A' B' f' hf y z hy'' hz'' i hi a ha

/-- **Versality is unchanged on regarding a category over the schemes over `V` as one over the
schemes over `S`.** -/
theorem isVersalAt_comp_overMap_iff (U : Over V) (u₀ : U.left) (x : X)
    (hx : q.obj x = U) (hx' : (q ⋙ Over.map g).obj x = (Over.map g).obj U) :
    IsVersalAt ((Over.map g).obj U) (q ⋙ Over.map g) u₀ x hx' ↔ IsVersalAt U q u₀ x hx :=
  ⟨isVersalAt_of_isVersalAt_comp_overMap g q U u₀ x hx hx',
    isVersalAt_comp_overMap_of_isVersalAt g q U u₀ x hx hx'⟩

/-- **Openness of versality over `V` gives openness of versality over `S`.** If `q` has
openness of versality as a category over the schemes over `V`, so has `q ⋙ Over.map g` as a
category over the schemes over `S`: a scheme locally of finite type over `S` carrying an object
is locally of finite type over `V`, and versality is the same over both bases
(`Deformation.Artin.isVersalAt_comp_overMap_iff`). -/
theorem hasOpenVersality_comp_overMap (h : HasOpenVersality q) :
    HasOpenVersality (q ⋙ Over.map g) := by
  intro U hU x hx u₀ hu₀ hv
  subst hx
  have : LocallyOfFiniteType ((q.obj x).hom ≫ g) := hU
  have hU' : LocallyOfFiniteType (q.obj x).hom := locallyOfFiniteType_of_comp _ g
  have key : ∀ u : (q.obj x).left,
      IsVersalAt ((q ⋙ Over.map g).obj x) (q ⋙ Over.map g) u x rfl ↔
        IsVersalAt (q.obj x) q u x rfl :=
    fun u => isVersalAt_comp_overMap_iff g q (q.obj x) u x rfl rfl
  obtain ⟨W, hW, hW'⟩ := h (q.obj x) hU' x rfl u₀ hu₀ ((key u₀).1 hv)
  exact ⟨W, hW, fun u hu hfu => (key u).2 (hW' u hu hfu)⟩

end BaseChange

end Deformation.Artin

end
