module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksCore.Tactic.StacksAttribute

/-!
# A basis for an affine groupoid scheme

For an affine groupoid scheme, suppose that the coordinate ring of the arrow scheme is free
over the coordinate ring of the object scheme, with basis obtained by pulling back a family of
functions along the target map.  Then that family is a basis over the ring of invariant
functions, and the arrow ring is the tensor square of the object ring over the invariant ring.

## Main definitions

* `AlgebraicGeometry.sourceMap` and `AlgebraicGeometry.targetMap` are the maps on global
  functions induced by the source and target of a groupoid scheme.
* `AlgebraicGeometry.invariantRing` is the subring on which these two maps agree.
* `AlgebraicGeometry.GroupoidScheme.invariantRingMap` is the homomorphism of invariant rings
  induced by a morphism of groupoid schemes.

## Main results

* `AlgebraicGeometry.basis_over_invariantRing` gives the asserted basis over invariant
  functions.
* `AlgebraicGeometry.tensorProduct_equiv_arrowRing` identifies the tensor square with the arrow
  ring, including the formula characterizing the canonical isomorphism.

## Implementation notes

Rather than choosing presentations of the two affine schemes as spectra, we use their rings of
global functions.  This is an equivalent, choice-free formulation of the source.  The two
conclusions of the source lemma are stated separately.  In the tensor-product conclusion the
formula on pure tensors records that the isomorphism is the canonical map, not merely an
unspecified ring isomorphism.

## References

* [Stacks Project, Tag 03C8](https://stacks.math.columbia.edu/tag/03C8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u v w z y

/-- Two ring maps out of `A` which agree on `C` and have bases matching under them exhibit the
target as the tensor square `A ⊗[C] A`, by the canonical map `a ⊗ a' ↦ f a * g a'`. -/
private theorem tensorProduct_ringEquiv_of_bases
    {C : Type u} {A : Type v} {B : Type w} [CommRing C] [CommRing A] [CommRing B]
    [Algebra C A] (f g : A →+* B)
    (hfg : g.comp (algebraMap C A) = f.comp (algebraMap C A))
    {I : Type z} (bA : Module.Basis I C A)
    (bB : letI := f.toAlgebra; Module.Basis I A B)
    (hb : ∀ i, bB i = g (bA i)) :
    ∃ e : A ⊗[C] A ≃+* B, ∀ a a', e (a ⊗ₜ[C] a') = f a * g a' := by
  let : Algebra A B := f.toAlgebra
  let : Algebra C B := (f.comp (algebraMap C A)).toAlgebra
  let : IsScalarTower C A B := IsScalarTower.of_algebraMap_eq' rfl
  let ga : A →ₐ[C] B := ⟨g, fun c => congrArg (fun h : C →+* B => h c) hfg⟩
  let φ : A ⊗[C] A →ₐ[A] B :=
    Algebra.TensorProduct.lift (Algebra.ofId A B) ga (fun _ _ => Commute.all _ _)
  have hφ : ∀ i, φ (Algebra.TensorProduct.basis A bA i) = bB i := by
    intro i
    rw [Algebra.TensorProduct.basis_apply]
    simpa [φ, ga] using (hb i).symm
  have hbij : Function.Bijective φ := by
    let e := (Algebra.TensorProduct.basis A bA).equiv bB (Equiv.refl I)
    have he : φ.toLinearMap = e.toLinearMap := by
      refine (Algebra.TensorProduct.basis A bA).ext fun i ↦ ?_
      change φ ((Algebra.TensorProduct.basis A bA) i) =
        e ((Algebra.TensorProduct.basis A bA) i)
      rw [Module.Basis.equiv_apply]
      exact hφ i
    change Function.Bijective φ.toLinearMap
    rw [he]
    exact e.bijective
  exact ⟨RingEquiv.ofBijective φ.toRingHom hbij, fun _ _ => rfl⟩

namespace AlgebraicGeometry

/-- Pullback of global functions along the source map of a groupoid scheme. -/
def sourceMap {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) :
    Γ(G.objects.left, ⊤) →+* Γ(G.arrows.left, ⊤) :=
  (Scheme.Γ.map G.source.left.op).hom

/-- Pullback of global functions along the target map of a groupoid scheme. -/
def targetMap {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) :
    Γ(G.objects.left, ⊤) →+* Γ(G.arrows.left, ⊤) :=
  (Scheme.Γ.map G.target.left.op).hom

/-- The ring of invariant global functions on the object scheme of a groupoid scheme. -/
def invariantRing {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) :
    Subring Γ(G.objects.left, ⊤) :=
  (sourceMap G).eqLocus (targetMap G)

namespace GroupoidScheme

/-- The homomorphism on invariant rings induced by a morphism of groupoid schemes.  A morphism
pulls global functions on the objects of the target groupoid back to global functions on the
objects of the source groupoid, and an invariant function pulls back to an invariant one
because the morphism commutes with the source and target maps. -/
def invariantRingMap {S : Scheme.{u}} {G G' : Stacks.Groupoids.GroupoidScheme S}
    (F : Stacks.Groupoids.GroupoidScheme.Hom G' G) :
    invariantRing G →+* invariantRing G' :=
  ((Scheme.Γ.map F.mapObjects.left.op).hom.comp (invariantRing G).subtype).codRestrict
    (invariantRing G') (by
      rintro ⟨x, hx⟩
      change (Scheme.Γ.map G'.source.left.op).hom
          ((Scheme.Γ.map F.mapObjects.left.op).hom x) =
        (Scheme.Γ.map G'.target.left.op).hom
          ((Scheme.Γ.map F.mapObjects.left.op).hom x)
      have hsx := congrArg (fun q : G'.arrows.left ⟶ G.objects.left => (Scheme.Γ.map q.op).hom x)
        (congrArg Over.Hom.left F.map_source)
      have htx := congrArg (fun q : G'.arrows.left ⟶ G.objects.left => (Scheme.Γ.map q.op).hom x)
        (congrArg Over.Hom.left F.map_target)
      simp only [Over.comp_left, op_comp, Scheme.Γ.map_comp] at hsx htx
      exact hsx.symm.trans
        ((congrArg ((Scheme.Γ.map F.mapArrows.left.op).hom ·) hx).trans htx))

/-- The underlying function of `invariantRingMap` is pullback of global functions along the map
on object schemes. -/
theorem invariantRingMap_comp_subtype {S : Scheme.{u}}
    {G G' : Stacks.Groupoids.GroupoidScheme S}
    (F : Stacks.Groupoids.GroupoidScheme.Hom G' G) :
    (invariantRing G').subtype.comp (invariantRingMap F) =
      (Scheme.Γ.map F.mapObjects.left.op).hom.comp (invariantRing G).subtype := rfl

/-- `invariantRingMap` sends an invariant function to its pullback along the map on object
schemes. -/
theorem coe_invariantRingMap {S : Scheme.{u}} {G G' : Stacks.Groupoids.GroupoidScheme S}
    (F : Stacks.Groupoids.GroupoidScheme.Hom G' G) (c : invariantRing G) :
    ((invariantRingMap F c : invariantRing G') : Γ(G'.objects.left, ⊤)) =
      F.mapObjects.left.appTop.hom (c : Γ(G.objects.left, ⊤)) := rfl

end GroupoidScheme

/-- For an affine groupoid scheme the square of global-function rings attached to the scheme of
composable arrows is a pushout of commutative rings. -/
private theorem groupoidComposable_isPushout {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] :
    IsPushout (CommRingCat.ofHom ((Scheme.Γ.map G.source.left.op).hom))
      (CommRingCat.ofHom ((Scheme.Γ.map G.target.left.op).hom))
      (CommRingCat.ofHom ((Scheme.Γ.map (pullback.fst G.source G.target).left.op).hom))
      (CommRingCat.ofHom ((Scheme.Γ.map (pullback.snd G.source G.target).left.op).hom)) := by
  exact isPushout_appTop_of_isPullback
    ((IsPullback.of_hasPullback G.source G.target).map (Over.forget S))

/-- The algebraic heart of Tag 03C8: a basis of `B` over `A` given by the images under `t` of a
family in `A` is a basis of `A` over the equalizer of `s` and `t`, provided the groupoid
identities relating `s`, `t`, the identity section and composition hold. -/
private theorem basis_over_eqLocus_of_groupoid_bases
    {A : Type u} {B : Type v} {D : Type w}
    [CommRing A] [CommRing B] [CommRing D]
    (s t : A →+* B) (e : B →+* A)
    (p0 p1 c : B →+* D)
    (hes : e.comp s = RingHom.id A) (het : e.comp t = RingHom.id A)
    (hst : p0.comp s = p1.comp t)
    (hcs : c.comp s = p1.comp s) (hct : c.comp t = p0.comp t)
    {I : Type z} (x : I → A)
    (bB : letI := s.toAlgebra; Module.Basis I A B)
    (hbB : ∀ i, bB i = t (x i))
    (bD : letI := p1.toAlgebra; Module.Basis I B D)
    (hbD : ∀ i, bD i = p0 (t (x i))) :
    ∃ b : Module.Basis I (s.eqLocus t) A, ∀ i, b i = x i := by
  classical
  let : Algebra A B := s.toAlgebra
  let : Algebra B D := p1.toAlgebra
  let C : Subring A := s.eqLocus t
  have hexp (a : A) :
      t a = (bB.repr (t a)).sum (fun i ai => s ai * t (x i)) := by
    simpa [Finsupp.linearCombination_apply, hbB, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra] using
      (bB.linearCombination_repr (t a)).symm
  have hinv (a : A) (i : I) :
      s ((bB.repr (t a)) i) = t ((bB.repr (t a)) i) := by
    let v := bB.repr (t a)
    have heq : c (t a) = p0 (t a) := RingHom.congr_fun hct a
    rw [hexp a] at heq
    have hc (r : A) : c (s r) = p1 (s r) := RingHom.congr_fun hcs r
    have ht (r : A) : p0 (s r) = p1 (t r) := RingHom.congr_fun hst r
    have hct' (r : A) : c (t r) = p0 (t r) := RingHom.congr_fun hct r
    have heq' : v.sum (fun j r => s r • bD j) =
        v.sum (fun j r => t r • bD j) := by
      simpa [Finsupp.sum, map_sum, hc, ht, hct', hbD, Algebra.smul_def,
        RingHom.algebraMap_toAlgebra] using heq
    have hi := congrArg (fun d : D => bD.repr d i) heq'
    by_cases hmem : i ∈ v.support
    · simpa [Finsupp.sum, Module.Basis.repr_smul, Finsupp.single_apply, hmem] using hi
    · have hv : v i = 0 := by
        simpa only [Finsupp.mem_support_iff, ne_eq, not_not] using hmem
      simp [v, hv]
  have hli : LinearIndependent C x := by
    apply (linearIndependent_iff').2
    intro F g hsum i hi
    have hst' (z : C) : t z.1 = s z.1 := z.property.symm
    have hCA (z : C) : (algebraMap C A) z = z.1 := rfl
    have hsumB : ∑ j ∈ F, (g j).1 • bB j = 0 := by
      simpa [map_sum, hbB, Algebra.smul_def, RingHom.algebraMap_toAlgebra,
        hCA, hst', mul_comm, C] using congrArg t hsum
    exact Subtype.ext ((linearIndependent_iff').mp bB.linearIndependent F
      (fun j => (g j).1) hsumB i hi)
  have hsp : ⊤ ≤ Submodule.span C (Set.range x) := by
    intro a _
    let v := bB.repr (t a)
    have hs (r : A) : e (s r) = r := RingHom.congr_fun hes r
    have ht (r : A) : e (t r) = r := RingHom.congr_fun het r
    have ha : a = v.sum (fun i ai => ai * x i) := by
      simpa [v, Finsupp.sum, map_sum, hs, ht] using congrArg e (hexp a)
    rw [ha]
    apply Submodule.sum_mem
    intro i _
    have hci : v i ∈ C := hinv a i
    convert (Submodule.span C (Set.range x)).smul_mem ⟨v i, hci⟩
      (Submodule.subset_span (Set.mem_range_self i)) using 1
  exact ⟨Module.Basis.mk hli hsp, Module.Basis.mk_apply hli hsp⟩

/-- A basis transported across a pushout square of commutative rings. -/
private theorem basis_of_ring_pushout
    {A : Type u} {B : Type u} {C : Type u} {D : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (s : A →+* B) (t : A →+* C) (p : B →+* D) (q : C →+* D)
    (hsq : IsPushout (CommRingCat.ofHom t) (CommRingCat.ofHom s)
      (CommRingCat.ofHom q) (CommRingCat.ofHom p))
    {I : Type y} (b : letI := s.toAlgebra; Module.Basis I A B) :
    ∃ bD : (letI := q.toAlgebra; Module.Basis I C D),
      ∀ i, bD i = p (b i) := by
  let : Algebra A B := s.toAlgebra
  let : Algebra A C := t.toAlgebra
  let : Algebra B D := p.toAlgebra
  let : Algebra C D := q.toAlgebra
  let : Algebra A D := (q.comp t).toAlgebra
  have hcomm : q.comp t = p.comp s := by
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using
      congrArg CommRingCat.Hom.hom hsq.w
  let : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq' hcomm
  let : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq' rfl
  have hp : Algebra.IsPushout A C B D :=
    (CommRingCat.isPushout_iff_isPushout).mp hsq
  let e : C ⊗[A] B ≃ₐ[C] D := Algebra.IsPushout.equiv A C B D
  refine ⟨(Algebra.TensorProduct.basis C b).map e.toLinearEquiv, ?_⟩
  intro i
  rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
  change (Algebra.IsPushout.equiv A C B D) (1 ⊗ₜ[A] b i) = p (b i)
  rw [Algebra.IsPushout.equiv_tmul]
  simp only [map_one, one_mul]
  rfl

/-- A commuting square in `Over S` induces a commuting square of global-function rings. -/
theorem over_appTop_comp_eq {S : Scheme.{u}} {X Y Y' Z : Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X ⟶ Y') (g' : Y' ⟶ Z)
    (h : f ≫ g = f' ≫ g') :
    (f.left.appTop.hom).comp g.left.appTop.hom =
      (f'.left.appTop.hom).comp g'.left.appTop.hom := by
  simpa only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
    congrArg (fun m : X.left ⟶ Z.left => m.appTop.hom) (congrArg Over.Hom.left h)

/-- A structure map of a groupoid scheme which is split by the identity section induces a split
map on global functions. -/
private theorem groupoidMap_split {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S)
    (f : G.arrows ⟶ G.objects) (hf : G.identity ≫ f = 𝟙 G.objects) :
    ((Scheme.Γ.map G.identity.left.op).hom).comp
      ((Scheme.Γ.map f.left.op).hom) = RingHom.id _ :=
  over_appTop_comp_eq _ _ (𝟙 G.objects) (𝟙 G.objects) (hf.trans (Category.id_comp _).symm)

/-- A basis of the arrow ring over the object ring pulled back along the source descends to a
basis of the object ring over the invariant ring. -/
@[stacks 03C8 "the basis over invariant functions"]
theorem basis_over_invariantRing {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    {I : Type v} (x : I → Γ(G.objects.left, ⊤))
    (h : letI := (sourceMap G).toAlgebra
      ∃ b : Module.Basis I Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤),
        ∀ i, b i = targetMap G (x i)) :
    ∃ b : Module.Basis I (invariantRing G) Γ(G.objects.left, ⊤), ∀ i, b i = x i := by
  obtain ⟨bB, hbB⟩ := h
  let e : Γ(G.arrows.left, ⊤) →+* Γ(G.objects.left, ⊤) :=
    (Scheme.Γ.map G.identity.left.op).hom
  let p0 : Γ(G.arrows.left, ⊤) →+*
      Γ((pullback G.source G.target).left, ⊤) :=
    (Scheme.Γ.map (pullback.fst G.source G.target).left.op).hom
  let p1 : Γ(G.arrows.left, ⊤) →+*
      Γ((pullback G.source G.target).left, ⊤) :=
    (Scheme.Γ.map (pullback.snd G.source G.target).left.op).hom
  let c : Γ(G.arrows.left, ⊤) →+*
      Γ((pullback G.source G.target).left, ⊤) :=
    (Scheme.Γ.map G.comp.left.op).hom
  obtain ⟨bD, hbD⟩ := basis_of_ring_pushout (sourceMap G) (targetMap G) p0 p1
    (groupoidComposable_isPushout G).flip bB
  exact basis_over_eqLocus_of_groupoid_bases
    (sourceMap G) (targetMap G) e p0 p1 c
    (groupoidMap_split G G.source G.source_identity)
    (groupoidMap_split G G.target G.target_identity)
    (over_appTop_comp_eq _ _ _ _ pullback.condition)
    (over_appTop_comp_eq _ _ _ _ G.source_comp)
    (over_appTop_comp_eq _ _ _ _ G.target_comp)
    x bB hbB bD (by intro i; rw [hbD i, hbB i])

/-- Under the same basis hypothesis, the canonical map from the tensor square of the object
ring over its invariant ring to the arrow ring is an isomorphism. -/
@[stacks 03C8 "the tensor-product description"]
theorem tensorProduct_equiv_arrowRing {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    {I : Type v} (x : I → Γ(G.objects.left, ⊤))
    (h : letI := (sourceMap G).toAlgebra
      ∃ b : Module.Basis I Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤),
        ∀ i, b i = targetMap G (x i)) :
    let A := Γ(G.objects.left, ⊤)
    let B := Γ(G.arrows.left, ⊤)
    let C := invariantRing G
    ∃ e : RingEquiv (A ⊗[C] A) B,
      ∀ a a', e (a ⊗ₜ[C] a') = sourceMap G a * targetMap G a' := by
  obtain ⟨bA, hbA⟩ := basis_over_invariantRing G x h
  obtain ⟨bB, hbB⟩ := h
  let : Algebra (invariantRing G) Γ(G.objects.left, ⊤) :=
    (invariantRing G).subtype.toAlgebra
  exact tensorProduct_ringEquiv_of_bases (sourceMap G) (targetMap G)
    (RingHom.ext fun c => c.property.symm)
    bA bB (fun i ↦ by rw [hbA i, hbB i])

end AlgebraicGeometry

end

end
