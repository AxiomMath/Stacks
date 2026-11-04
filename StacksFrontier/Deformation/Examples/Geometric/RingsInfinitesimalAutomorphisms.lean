module

public import Mathlib.Algebra.Category.Ring.Constructions
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.IdealQuotient
public import StacksFrontier.Deformation.Examples.Geometric.Rings
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic
public import StacksFrontier.Deformation.RimSchlessinger.FibreProduct.Deformations

/-!
# Infinitesimal automorphisms of the deformation category of an algebra (Stacks 0DY3)

Let `k` be a field and `P` a commutative `k`-algebra. The infinitesimal automorphisms of the
deformation category `𝓓_P` of `P` are the `k`-derivations of `P` into itself:
`Inf(𝓓_P) = Der_k(P, P)`.

A point of `𝓓_P` over the dual numbers, together with a lift `i` of the constant inclusion
`k ⟶ k[ε]`, presents the flat algebra of that point as `P[ε]` in coordinates: the base of the
point over the residue field is a field, so its structure map to `(k, P)` is invertible, and
the flat algebra over the dual numbers is the base change of `P` along `k ⟶ k[ε]`, which is
`P[ε]`. In these coordinates an infinitesimal automorphism is an automorphism of `P[ε]` over
`k[ε]` reducing to the identity on `P`, and such an automorphism is `x + yε ↦ x + (D x + y)ε`
for a unique `D ∈ Der_k(P, P)`. Composition of automorphisms is addition of derivations, so
the identification is an isomorphism of groups, and the scalar action of `k` transports.

## Main definitions

* `Deformation.Examples.ringDeformationProjection`: the structure functor of the deformation
  category of `P`.

## Main results

* `Deformation.Examples.exists_infinitesimalAutomorphismGroupMulEquivDerivation`:
  **Stacks 0DY3**, the identification of the infinitesimal automorphism group of the
  deformation category of `P` with the additive group of `k`-derivations of `P`, written
  multiplicatively, together with the coordinates in which it holds.

## Implementation notes

The identification is stated together with the coordinate data that pins it down: a ring
isomorphism `c` of the flat algebra of the point with `P[ε]`, compatible with the reduction to
`P` and with the chosen lift `i`, and the formula saying that the derivation attached to an
automorphism is the `ε`-coefficient of its value on a constant. Without these the statement
would only assert that the two groups are abstractly isomorphic, which is strictly weaker than
the source.

The scalar action of `k` on `Inf(𝓓_P)` is recorded as the existence and uniqueness of a
rescaled automorphism rather than as a `Module` structure, so that no second module structure
on the subgroup has to be installed.

The predeformation-category property is produced inside the statement, from
`Deformation.Examples.ringDeformationCategory_isDeformationCategory`, rather than assumed:
the group of infinitesimal automorphisms depends on it, so a hypothesis would let a caller
supply a different proof and get a different group.

`DualNumber.mapOfAlgebra` of `StacksFrontier.RingTheory.DualNumber.TrivialExtension` is the
special case of `Deformation.dualNumberRingHom` for an `algebraMap`; the general form over an
arbitrary ring map is what the change of Artinian base needs here.

## References

* [Stacks Project, Tag 0DY3](https://stacks.math.columbia.edu/tag/0DY3)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace Deformation.Examples

/-! ### Dual-number coordinates for an extension of scalars -/

/-- An element of a ring `S ≅ k[ε]` is its constant part plus its `ε`-part times `ε`, where
constants come from a ring map `φ` out of `R ≅ k`. -/
private theorem eq_map_fst_add_map_snd_mul
    {R S k : Type*} [CommRing R] [CommRing S] [CommRing k]
    (φ : R →+* S) (b : R ≃+* k) (c : S ≃+* DualNumber k)
    (hc : ∀ r, c (φ r) = TrivSqZeroExt.inl (b r)) (s : S) :
    s = φ (b.symm (c s).fst) + φ (b.symm (c s).snd) * c.symm DualNumber.eps := by
  apply c.injective
  simp only [map_add, map_mul, hc, b.apply_symm_apply, c.apply_symm_apply]
  ext <;> simp

/-- Base change of a ring along a map of dual numbers is again dual numbers: if `S ≅ k[ε]`
compatibly with `R ≅ k`, and `M ≅ P` semilinearly over that, then `S ⊗_R M ≅ P[ε]`, by the
coordinates `s ⊗ x ↦ (image of s) · (constant part of x)`. -/
private theorem exists_tensorRingEquivDualNumber
    {R S k M P : Type*} [CommRing R] [CommRing S] [CommRing k]
    [CommRing M] [CommRing P] [Algebra R S] [Algebra R M] [Algebra k P]
    (b : R ≃+* k) (c : S ≃+* DualNumber k)
    (hc : ∀ r, c (algebraMap R S r) = TrivSqZeroExt.inl (b r))
    (a : M ≃+* P) (ha : ∀ r x, a (r • x) = b r • a x) :
    ∃ E : TensorProduct R S M ≃+* DualNumber P,
      ∀ s x, E (s ⊗ₜ[R] x) =
        dualNumberRingHom (algebraMap k P) (c s) * TrivSqZeroExt.inl (a x) := by
  let : Algebra R k := b.toRingHom.toAlgebra
  let : Algebra R P := ((algebraMap k P).comp b.toRingHom).toAlgebra
  have : IsScalarTower R k P := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let aa : M ≃ₐ[R] P :=
    { a with
      commutes' := fun r => by
        change a (algebraMap R M r) = algebraMap k P (b r)
        simpa [Algebra.smul_def] using ha r 1 }
  let cc : S →ₐ[R] DualNumber P :=
    { (dualNumberRingHom (algebraMap k P)).comp c.toRingHom with
      commutes' := fun r => by
        change dualNumberRingHom (algebraMap k P) (c (algebraMap R S r)) = _
        rw [hc]
        ext <;> simp [dualNumberRingHom, TrivSqZeroExt.algebraMap_eq_inl']
        rfl }
  let h : TensorProduct R S M →ₐ[R] DualNumber P :=
    Algebra.TensorProduct.lift cc
      ((TrivSqZeroExt.inlAlgHom R P P).comp aa.toAlgHom) fun _ _ => Commute.all _ _
  let j : P →ₐ[R] TensorProduct R S M := Algebra.TensorProduct.includeRight.comp aa.symm.toAlgHom
  let t : S := c.symm DualNumber.eps
  have ht : t * t = 0 := c.injective (by simp [t])
  let t' : TensorProduct R S M :=
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] TensorProduct R S M) t
  let h' : DualNumber P →ₐ[R] TensorProduct R S M :=
    DualNumber.lift ⟨(j, t'), by
      simpa [t'] using congrArg
        (Algebra.TensorProduct.includeLeft : S →ₐ[R] TensorProduct R S M) ht,
      fun _ => Commute.all _ _⟩
  have h_inl (p : P) : h (j p) = TrivSqZeroExt.inl p := by simp [h, j]
  have h_t : h t' = DualNumber.eps := by ext <;> simp [h, t', cc, t, dualNumberRingHom]
  have h_right (z : DualNumber P) : h (h' z) = z := by
    simp only [h', DualNumber.lift_apply_apply, map_add, map_mul, h_inl, h_t]
    ext <;> simp
  have h_left : h'.comp h = AlgHom.id R _ := by
    apply Algebra.TensorProduct.ext
    · refine AlgHom.ext fun s => ?_
      change h' (h ((Algebra.TensorProduct.includeLeft : S →ₐ[R]
        TensorProduct R S M) s)) = _
      have hh : h ((Algebra.TensorProduct.includeLeft : S →ₐ[R]
          TensorProduct R S M) s) = cc s := by simp [h]
      rw [hh]
      change h' (dualNumberRingHom (algebraMap k P) (c s)) = _
      have hs := eq_map_fst_add_map_snd_mul (algebraMap R S) b c hc s
      dsimp only [h']
      rw [DualNumber.lift_apply_apply, dualNumberRingHom_fst, dualNumberRingHom_snd]
      change j (algebraMap k P (c s).fst) + j (algebraMap k P (c s).snd) * t' = _
      have hj (r : k) : j (algebraMap k P r) =
          (Algebra.TensorProduct.includeLeft : S →ₐ[R] TensorProduct R S M)
            (algebraMap R S (b.symm r)) := by
        obtain ⟨r, rfl⟩ := b.surjective r
        rw [b.symm_apply_apply]
        exact (j.commutes r).trans
          ((Algebra.TensorProduct.includeLeft : S →ₐ[R] TensorProduct R S M).commutes r).symm
      rw [hj, hj]
      conv_rhs => rw [hs]
      rw [map_add, map_mul]
      simp only [AlgHom.comp_apply, AlgHom.id_apply]
      rfl
    · apply AlgHom.ext
      intro x
      simp [h, h', j]
  refine ⟨AlgEquiv.toRingEquiv (AlgEquiv.ofAlgHom h h' (AlgHom.ext h_right) h_left), fun s x => ?_⟩
  change h (s ⊗ₜ[R] x) = _
  simp [h, cc, aa]

/-! ### Automorphisms of a point of the deformation category -/

variable {Λ : Type u} {k P : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  [CommRing P] [Algebra k P]

/-- The structure functor of the deformation category of a `k`-algebra `P`: it sends a
deformation of `P` to the Artinian local `Λ`-algebra it is flat over. -/
public abbrev ringDeformationProjection (Λ : Type u) (k P : Type w) [CommRing Λ] [Field k]
    [Algebra Λ k] [CommRing P] [Algebra k P] :
    ringDeformationCategory (Λ := Λ) (k := k) P ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k :=
  objectsOverFunctor (FlatAlgebraCategory.projection (Λ := Λ) (k := k))
    (residueFieldAlgebra (Λ := Λ) (k := k) P)

/-- An automorphism of the flat algebra of a point of the deformation category over its own
base, compatible with the reduction to `(k, P)`, is an automorphism of that point in its
fibre. -/
private def fiberAutOfAlgEquiv {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (x : (ringDeformationProjection Λ k P).Fiber A)
    (a : x.1.left.fiber ≃ₐ[x.1.left.base] x.1.left.fiber)
    (hr : ∀ y, x.1.hom.map.hom (a y) = x.1.hom.map.hom y) : Aut x := by
  let X := x.1.left
  have hcart0 : IsPushout (FlatAlgebraCategory.structureMap X) (𝟙 _) (𝟙 _)
      (FlatAlgebraCategory.structureMap X) := IsPushout.of_id_snd
  have hcart : IsPushout (FlatAlgebraCategory.structureMap X)
      (FlatAlgebraCategory.baseMap (𝟙 X.base))
      (CommRingCat.ofHom a.toRingEquiv.toRingHom)
      (FlatAlgebraCategory.structureMap X) :=
    hcart0.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (RingEquiv.toCommRingCatIso a.toRingEquiv)
      (by simp) (by simp [FlatAlgebraCategory.baseMap]) (by ext y; rfl)
      (by
        ext r
        change a (algebraMap X.base X.fiber r) = _
        exact a.commutes' r)
  let f : FlatAlgebraCategory.Hom X X :=
    { base := 𝟙 X.base
      map := CommRingCat.ofHom a.toRingEquiv.toRingHom
      cartesian := hcart }
  have hf : f ≫ x.1.hom = x.1.hom :=
    FlatAlgebraCategory.Hom.ext (Category.id_comp _) (by ext y; exact hr y)
  let ai := a.symm
  have hri (y) : x.1.hom.map.hom (ai y) = x.1.hom.map.hom y := by
    calc
      x.1.hom.map.hom (ai y) = x.1.hom.map.hom (a (ai y)) := (hr (ai y)).symm
      _ = x.1.hom.map.hom y := by rw [a.apply_symm_apply]
  let fi : FlatAlgebraCategory.Hom X X :=
    { base := 𝟙 X.base
      map := CommRingCat.ofHom ai.toRingEquiv.toRingHom
      cartesian := by
        let : Algebra X.base X.fiber := X.algebra
        exact hcart0.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (RingEquiv.toCommRingCatIso ai.toRingEquiv)
          (by simp) (by simp [FlatAlgebraCategory.baseMap]) (by ext y; rfl)
          (by
            ext r
            change ai (algebraMap X.base X.fiber r) = _
            exact ai.commutes' r) }
  have hfi : fi ≫ x.1.hom = x.1.hom :=
    FlatAlgebraCategory.Hom.ext (Category.id_comp _) (by ext y; exact hri y)
  let F : x.1 ⟶ x.1 := Over.homMk f hf
  let FI : x.1 ⟶ x.1 := Over.homMk fi hfi
  have hF : (ringDeformationProjection Λ k P).IsHomLift (𝟙 A) F := by
    apply IsHomLift.of_fac' _ _ _ x.2 x.2
    simp [F, f, FlatAlgebraCategory.projection]
    rfl
  have hFI : (ringDeformationProjection Λ k P).IsHomLift (𝟙 A) FI := by
    apply IsHomLift.of_fac' _ _ _ x.2 x.2
    simp [FI, fi, FlatAlgebraCategory.projection]
    rfl
  exact ⟨⟨F, hF⟩, ⟨FI, hFI⟩,
    Subtype.ext <| Over.OverMorphism.ext <|
      FlatAlgebraCategory.Hom.ext rfl (by ext y; exact a.symm_apply_apply y),
    Subtype.ext <| Over.OverMorphism.ext <|
      FlatAlgebraCategory.Hom.ext rfl (by ext y; exact a.apply_symm_apply y)⟩

/-- An automorphism of a point in its fibre is the identity on the Artinian base. -/
private theorem fiberAut_base_eq_id {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (x : (ringDeformationProjection Λ k P).Fiber A) (a : Aut x) :
    a.hom.val.left.base = 𝟙 x.1.left.base := by
  have := a.hom.property
  simpa [FlatAlgebraCategory.projection] using
    IsHomLift.fac' (ringDeformationProjection Λ k P) (𝟙 A) a.hom.val

/-- Two automorphisms of a point in its fibre agreeing on the flat algebra are equal. -/
private theorem fiberAut_ext {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    {x : (ringDeformationProjection Λ k P).Fiber A} {a b : Aut x}
    (h : ∀ y, a.hom.val.left.map.hom y = b.hom.val.left.map.hom y) : a = b :=
  Iso.ext <| Subtype.ext <| Over.OverMorphism.ext <| FlatAlgebraCategory.Hom.ext
    (by rw [fiberAut_base_eq_id x a, fiberAut_base_eq_id x b]) (by ext y; exact h y)

/-- In coordinates presenting the flat algebra of a point as `P[ε]` over `k[ε]`, a
`k`-derivation of `P` gives an automorphism of that point. -/
private def derivationFiberAut {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (x : (ringDeformationProjection Λ k P).Fiber A)
    (E : x.1.left.fiber ≃+* DualNumber P) (c : x.1.left.base ≃+* DualNumber k)
    (hs : ∀ s y, E (s • y) = dualNumberRingHom (algebraMap k P) (c s) * E y)
    (hr : ∀ y, (E y).fst = x.1.hom.map.hom y) (D : Derivation k P P) : Aut x := by
  let ar := (E.trans (derivationDualNumberAlgEquiv D).toRingEquiv).trans E.symm
  have har (y) : E (ar y) = derivationDualNumberAlgHom D (E y) := E.apply_symm_apply _
  let a : x.1.left.fiber ≃ₐ[x.1.left.base] x.1.left.fiber :=
    { ar with
      commutes' := fun s => by
        apply E.injective
        change E (ar (algebraMap _ _ s)) = E (algebraMap _ _ s)
        rw [har]
        have h := hs s 1
        simp only [Algebra.smul_def, map_one, mul_one] at h
        rw [h, derivationDualNumberAlgHom_scalar] }
  apply fiberAutOfAlgEquiv x a
  intro y
  change x.1.hom.map.hom (ar y) = x.1.hom.map.hom y
  rw [← hr (ar y), har, (derivationDualNumberAlgHom_coordinates D (E y)).1, hr]

private theorem derivationFiberAut_apply {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (x : (ringDeformationProjection Λ k P).Fiber A)
    (E : x.1.left.fiber ≃+* DualNumber P) (c : x.1.left.base ≃+* DualNumber k)
    (hs : ∀ s y, E (s • y) = dualNumberRingHom (algebraMap k P) (c s) * E y)
    (hr : ∀ y, (E y).fst = x.1.hom.map.hom y) (D : Derivation k P P)
    (y : x.1.left.fiber) :
    E ((derivationFiberAut x E c hs hr D).hom.val.left.map.hom y) =
      derivationDualNumberAlgHom D (E y) := by
  unfold derivationFiberAut fiberAutOfAlgEquiv
  dsimp
  change E (((E.trans (derivationDualNumberAlgEquiv D).toRingEquiv).trans E.symm) y) = _
  simp [RingEquiv.trans_apply, derivationDualNumberAlgEquiv]

/-- The `ε`-coefficient of the automorphism attached to `D`, on a constant `z`, is `D z`. -/
private theorem derivationFiberAut_apply_snd {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (x : (ringDeformationProjection Λ k P).Fiber A)
    (E : x.1.left.fiber ≃+* DualNumber P) (c : x.1.left.base ≃+* DualNumber k)
    (hs : ∀ s y, E (s • y) = dualNumberRingHom (algebraMap k P) (c s) * E y)
    (hr : ∀ y, (E y).fst = x.1.hom.map.hom y) (D : Derivation k P P) (z : P) :
    (E ((derivationFiberAut x E c hs hr D).hom.val.left.map.hom
      (E.symm (TrivSqZeroExt.inl z)))).snd = D z := by
  rw [derivationFiberAut_apply, E.apply_symm_apply, derivationDualNumberAlgHom_inl]
  simp

/-- In coordinates presenting the flat algebra of a point as `P[ε]` over `k[ε]`, the
`k`-derivations of `P` are exactly the automorphisms of that point in its fibre. -/
private def derivationMulEquivFiberAut {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (x : (ringDeformationProjection Λ k P).Fiber A)
    (E : x.1.left.fiber ≃+* DualNumber P) (c : x.1.left.base ≃+* DualNumber k)
    (hs : ∀ s y, E (s • y) = dualNumberRingHom (algebraMap k P) (c s) * E y)
    (hr : ∀ y, (E y).fst = x.1.hom.map.hom y) :
    Multiplicative (Derivation k P P) ≃* Aut x := by
  let F : Multiplicative (Derivation k P P) →* Aut x :=
    { toFun := fun D => derivationFiberAut x E c hs hr D.toAdd
      map_one' := by
        refine fiberAut_ext fun y => E.injective ?_
        rw [derivationFiberAut_apply]
        change derivationDualNumberAlgHom (0 : Derivation k P P) (E y) = E y
        rw [derivationDualNumberAlgHom_zero]
        rfl
      map_mul' := fun D D' => by
        refine fiberAut_ext fun y => E.injective ?_
        change E ((derivationFiberAut x E c hs hr (D.toAdd + D'.toAdd)).hom.val.left.map.hom
            y) =
          E ((derivationFiberAut x E c hs hr D.toAdd).hom.val.left.map.hom
            ((derivationFiberAut x E c hs hr D'.toAdd).hom.val.left.map.hom y))
        rw [derivationFiberAut_apply, derivationFiberAut_apply, derivationFiberAut_apply]
        exact AlgHom.congr_fun
          (derivationDualNumberAlgHom_add D.toAdd D'.toAdd) (E y) }
  refine MulEquiv.ofBijective F ⟨?_, ?_⟩
  · intro D D' h
    refine Multiplicative.toAdd.injective (Derivation.ext fun z => ?_)
    rw [← derivationFiberAut_apply_snd x E c hs hr D.toAdd,
      ← derivationFiberAut_apply_snd x E c hs hr D'.toAdd]
    exact congrArg
      (fun a : Aut x => (E (a.hom.val.left.map.hom (E.symm (TrivSqZeroExt.inl z)))).snd) h
  · intro a
    let fr : DualNumber P →+* DualNumber P :=
      E.toRingHom.comp (a.hom.val.left.map.hom.comp E.symm.toRingHom)
    have hes (s : x.1.left.base) :
        E (algebraMap x.1.left.base x.1.left.fiber s) =
          dualNumberRingHom (algebraMap k P) (c s) := by
      simpa [Algebra.smul_def] using hs s 1
    have hfix (s : x.1.left.base) :
        a.hom.val.left.map.hom (algebraMap x.1.left.base x.1.left.fiber s) =
          algebraMap x.1.left.base x.1.left.fiber s := by
      simpa [FlatAlgebraCategory.baseMap, fiberAut_base_eq_id x a] using
        congrArg (fun f => f.hom s) a.hom.val.left.cartesian.w
    have hbase (s : x.1.left.base) :
        fr (dualNumberRingHom (algebraMap k P) (c s)) =
          dualNumberRingHom (algebraMap k P) (c s) := by
      rw [← hes s]
      change E (a.hom.val.left.map.hom
        (E.symm (E (algebraMap x.1.left.base x.1.left.fiber s)))) = _
      rw [E.symm_apply_apply, hfix, hes]
    let f : DualNumber P →ₐ[k] DualNumber P :=
      { fr with
        commutes' := fun r => by
          have hh := hbase (c.symm (TrivSqZeroExt.inl r))
          simpa [dualNumberRingHom, TrivSqZeroExt.algebraMap_eq_inl'] using hh }
    have heps : f DualNumber.eps = DualNumber.eps := by
      have hh := hbase (c.symm DualNumber.eps)
      have hc : dualNumberRingHom (algebraMap k P) (c (c.symm DualNumber.eps)) =
          DualNumber.eps := by
        ext <;> simp [dualNumberRingHom]
      change fr DualNumber.eps = DualNumber.eps
      simpa only [hc] using hbase (c.symm DualNumber.eps)
    have hared (y : x.1.left.fiber) :
        x.1.hom.map.hom (a.hom.val.left.map.hom y) = x.1.hom.map.hom y :=
      congrArg (fun q => q.map.hom y) (Over.w a.hom.val)
    have hred (z : P) : (f (TrivSqZeroExt.inl z)).fst = z := by
      change (E (a.hom.val.left.map.hom (E.symm (TrivSqZeroExt.inl z)))).fst = z
      rw [hr, hared, ← hr (E.symm (TrivSqZeroExt.inl z))]
      simp
    let D := derivationOfDualNumberAlgHom f hred
    have hD : derivationDualNumberAlgHom D = f :=
      derivationDualNumberAlgHom_derivationOfDualNumberAlgHom f hred heps
    refine ⟨Multiplicative.ofAdd D, ?_⟩
    apply fiberAut_ext
    intro y
    apply E.injective
    change E ((derivationFiberAut x E c hs hr D).hom.val.left.map.hom y) =
      E (a.hom.val.left.map.hom y)
    rw [derivationFiberAut_apply x E c hs hr D y,
      derivationDualNumberAlgHom_derivationOfDualNumberAlgHom f hred heps]
    change E (a.hom.val.left.map.hom (E.symm (E y))) = _
    rw [E.symm_apply_apply]

/-! ### The identification of Stacks 0DY3 -/

/-- **Stacks 0DY3.** The infinitesimal automorphisms of the deformation category of a
commutative `k`-algebra `P` are the `k`-derivations of `P` into itself.

The statement also records the coordinates in which this holds: for any point `xε` of the
deformation category over the dual numbers and any lift `i` of the constant inclusion, there
is a ring isomorphism `c` of the flat algebra of `xε` with `P[ε]` compatible with the
reduction to `P` and carrying the lift to the constant inclusion, and the derivation attached
to an infinitesimal automorphism is the `ε`-coefficient of its value on a constant. The
scalar action of `k` on the derivations is reflected by the existence of a unique rescaled
infinitesimal automorphism. -/
@[stacks 0DY3 "infinitesimal automorphisms",
  sga "1 III 6.1" "special case",
  sga "3 VIIA 1.5" "partial"]
public theorem exists_infinitesimalAutomorphismGroupMulEquivDerivation
    {Λ : Type u} {k P : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    [CommRing P] [Algebra k P] :
    ∃ hp : IsPredeformationCategory (ringDeformationProjection Λ k P),
      ∀ {Aε : ArtinianLocalAlgCat.{u, w, w} Λ k}
        {x₀ : (ringDeformationProjection Λ k P).Fiber (residueFieldObject.{u, w, w} Λ k)}
        {xε : (ringDeformationProjection Λ k P).Fiber Aε}
        (g : residueFieldObject.{u, w, w} Λ k ⟶ Aε)
        (e : Aε ⟶ residueFieldObject.{u, w, w} Λ k)
        (hpair : IsCanonicalDualNumberPair g e)
        (i : x₀.1 ⟶ xε.1) (hi : (ringDeformationProjection Λ k P).IsHomLift g i),
        ∃ c : xε.1.left.fiber ≃+* DualNumber P,
          (∀ y : xε.1.left.fiber, (c y).fst = xε.1.hom.map y) ∧
          (∀ y : x₀.1.left.fiber,
            c (i.left.map y) = TrivSqZeroExt.inl (x₀.1.hom.map y)) ∧
          ∃ E : infinitesimalAutomorphismGroup hp g e hpair i hi ≃*
            Multiplicative (Derivation k P P),
            (∀ (a : infinitesimalAutomorphismGroup hp g e hpair i hi) (y : P),
              (c (a.val.hom.val.left.map (c.symm (TrivSqZeroExt.inl y)))).snd =
                (Multiplicative.toAdd (E a)) y) ∧
            (∀ (s : k) (a : infinitesimalAutomorphismGroup hp g e hpair i hi),
              ∃! b : infinitesimalAutomorphismGroup hp g e hpair i hi,
                ∀ y : P,
                  (c (b.val.hom.val.left.map (c.symm (TrivSqZeroExt.inl y)))).snd =
                    s • (c (a.val.hom.val.left.map
                      (c.symm (TrivSqZeroExt.inl y)))).snd) := by
  classical
  have hp : IsPredeformationCategory (ringDeformationProjection Λ k P) :=
    (ringDeformationCategory_isDeformationCategory (Λ := Λ) (k := k) P).predeformation
  refine ⟨hp, ?_⟩
  intro Aε x₀ xε g e hpair i hi
  obtain ⟨i₀, iε, hg, -, -⟩ := id hpair
  have hb₀ : x₀.1.left.base = residueFieldObject.{u, w, w} Λ k := x₀.2
  have hbε : xε.1.left.base = Aε := xε.2
  have hfield₀ : IsField x₀.1.left.base := by
    rw [hb₀]
    change IsField (ULift.{w} k)
    exact MulEquiv.isField (Field.toIsField k) (ULift.ringEquiv : ULift.{w, w} k ≃+* k)
  have hbij := artinianLocalAlgHom_bijective_of_isField _ _ hfield₀ (Field.toIsField k)
    x₀.1.hom.base
  let b : x₀.1.left.base ≃+* k := RingEquiv.ofBijective x₀.1.hom.base.hom.toRingHom hbij
  have : IsIso x₀.1.hom.base := ArtinianLocalAlgCat.isIso_of_bijective_hom _ hbij
  have : IsIso (FlatAlgebraCategory.baseMap x₀.1.hom.base) := by
    change IsIso (CommRingCat.ofHom x₀.1.hom.base.hom.toRingHom)
    exact (RingEquiv.toCommRingCatIso b).isIso_hom
  have hmap : IsIso x₀.1.hom.map := x₀.1.hom.cartesian.isIso_inl_of_isIso
  let a : x₀.1.left.fiber ≃+* P :=
    RingEquiv.ofBijective x₀.1.hom.map.hom
      ((ConcreteCategory.isIso_iff_bijective x₀.1.hom.map).mp hmap)
  let B := (ringEquivOfIso (eqToIso hb₀)).trans i₀.toRingEquiv
  let C := (ringEquivOfIso (eqToIso hbε)).trans iε.toRingEquiv
  have hC (r : x₀.1.left.base) : C (i.left.base.hom r) = TrivSqZeroExt.inl (B r) := by
    have hh : (eqToHom hbε).hom (i.left.base.hom r) = g.hom ((eqToHom hb₀).hom r) :=
      congrArg (fun f => f.hom r) (IsHomLift.commSq (ringDeformationProjection Λ k P) g i).w
    change iε ((eqToHom hbε).hom (i.left.base.hom r)) =
      TrivSqZeroExt.inl (i₀ ((eqToHom hb₀).hom r))
    rw [hh]
    exact AlgHom.congr_fun hg ((eqToHom hb₀).hom r)
  let B' := B.symm.trans b
  let cBase := C.trans (dualNumberRingEquiv B')
  have hc (r : x₀.1.left.base) :
      cBase (i.left.base.hom r) = TrivSqZeroExt.inl (b r) := by
    change dualNumberRingEquiv B' (C (i.left.base.hom r)) = _
    rw [hC]
    ext <;> simp [dualNumberRingEquiv, dualNumberRingHom, B']
  have ha (r : x₀.1.left.base) (x : x₀.1.left.fiber) : a (r • x) = b r • a x := by
    have hcomm : x₀.1.hom.map.hom (algebraMap x₀.1.left.base x₀.1.left.fiber r) =
        algebraMap k P (x₀.1.hom.base.hom r) :=
      congrArg (fun f => f.hom r) x₀.1.hom.cartesian.w
    rw [Algebra.smul_def, Algebra.smul_def]
    change x₀.1.hom.map.hom (algebraMap x₀.1.left.base x₀.1.left.fiber r * x) =
      algebraMap k P (b r) * a x
    rw [map_mul, hcomm]
    congr 1
  let : Algebra x₀.1.left.base xε.1.left.base := i.left.base.hom.toAlgebra
  let : Algebra x₀.1.left.base x₀.1.left.fiber := x₀.1.left.algebra
  let : Algebra xε.1.left.base xε.1.left.fiber := xε.1.left.algebra
  let : Algebra x₀.1.left.fiber xε.1.left.fiber := i.left.map.hom.toAlgebra
  let : Algebra x₀.1.left.base xε.1.left.fiber :=
    (i.left.map.hom.comp (algebraMap x₀.1.left.base x₀.1.left.fiber)).toAlgebra
  have hbaseSquare : i.left.map.hom.comp (algebraMap x₀.1.left.base x₀.1.left.fiber) =
      (algebraMap xε.1.left.base xε.1.left.fiber).comp i.left.base.hom.toRingHom :=
    congrArg
      (fun f : CommRingCat.of x₀.1.left.base ⟶ CommRingCat.of xε.1.left.fiber => f.hom)
      i.left.cartesian.w
  have : IsScalarTower x₀.1.left.base x₀.1.left.fiber xε.1.left.fiber :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower x₀.1.left.base xε.1.left.base xε.1.left.fiber :=
    IsScalarTower.of_algebraMap_eq' hbaseSquare
  have hpush : Algebra.IsPushout x₀.1.left.base x₀.1.left.fiber
      xε.1.left.base xε.1.left.fiber :=
    CommRingCat.isPushout_iff_isPushout.mp i.left.cartesian
  have : Algebra.IsPushout x₀.1.left.base xε.1.left.base x₀.1.left.fiber xε.1.left.fiber :=
    Algebra.IsPushout.symm hpush
  obtain ⟨E₀, hEtmul⟩ := exists_tensorRingEquivDualNumber b cBase hc a ha
  let E : xε.1.left.fiber ≃+* DualNumber P :=
    ((Algebra.IsPushout.equiv x₀.1.left.base xε.1.left.base
      x₀.1.left.fiber xε.1.left.fiber).toRingEquiv.symm).trans E₀
  have hEi (y : x₀.1.left.fiber) :
      E (i.left.map.hom y) = TrivSqZeroExt.inl (a y) := by
    change E₀ ((Algebra.IsPushout.equiv x₀.1.left.base xε.1.left.base
      x₀.1.left.fiber xε.1.left.fiber).symm (algebraMap _ _ y)) = _
    rw [Algebra.IsPushout.equiv_symm_algebraMap_right, hEtmul]
    simp [dualNumberRingHom]
  have hEfst (y : xε.1.left.fiber) : (E y).fst = xε.1.hom.map.hom y := by
    let qbase : xε.1.left.base →+* k := xε.1.hom.base.hom.toRingHom
    let qfiber : xε.1.left.fiber →+* P := xε.1.hom.map.hom
    let t : xε.1.left.base := cBase.symm DualNumber.eps
    have ht : qbase t = 0 := by
      have hnil : t * t = 0 := cBase.injective (by simp [t])
      exact mul_self_eq_zero.mp (by simpa only [map_mul, map_zero] using congrArg qbase hnil)
    have hqbase (s : xε.1.left.base) : qbase s = (cBase s).fst := by
      have hs := eq_map_fst_add_map_snd_mul i.left.base.hom.toRingHom b cBase hc s
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hs
      rw [hs, map_add, map_mul, ht]
      have h0 : qbase (i.left.base.hom (b.symm (cBase s).fst)) =
          b (b.symm (cBase s).fst) := by
        have hh : xε.1.hom.base.hom (i.left.base.hom (b.symm (cBase s).fst)) =
            x₀.1.hom.base.hom (b.symm (cBase s).fst) :=
          congrArg (fun f => f.base.hom (b.symm (cBase s).fst)) (Over.w i)
        change xε.1.hom.base.hom (i.left.base.hom (b.symm (cBase s).fst)) = _
        rw [hh]
        rfl
      rw [map_add, map_mul, hc, hc, h0, b.apply_symm_apply]
      simp
    have hqmap (x : x₀.1.left.fiber) : qfiber (i.left.map.hom x) = a x :=
      congrArg (fun f => f.map.hom x) (Over.w i)
    change (E₀ ((Algebra.IsPushout.equiv x₀.1.left.base xε.1.left.base
      x₀.1.left.fiber xε.1.left.fiber).symm y)).fst = qfiber y
    obtain ⟨z, rfl⟩ := (Algebra.IsPushout.equiv x₀.1.left.base
      xε.1.left.base x₀.1.left.fiber xε.1.left.fiber).surjective y
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, TrivSqZeroExt.fst_add, hz, hz']
    | tmul s x =>
        rw [(Algebra.IsPushout.equiv x₀.1.left.base xε.1.left.base
          x₀.1.left.fiber xε.1.left.fiber).symm_apply_apply, hEtmul,
          Algebra.IsPushout.equiv_tmul]
        have hcomm (s : xε.1.left.base) :
            qfiber (algebraMap xε.1.left.base xε.1.left.fiber s) =
              algebraMap k P (qbase s) :=
          congrArg (fun f => f s) (congrArg (fun f => f.hom) xε.1.hom.cartesian.w)
        have hinc : qfiber (algebraMap x₀.1.left.fiber xε.1.left.fiber x) = a x := hqmap x
        rw [map_mul, hcomm, hinc, hqbase]
        simp [dualNumberRingHom]
  refine ⟨E, hEfst, hEi, ?_⟩
  have hes (s : xε.1.left.base) :
      E (algebraMap xε.1.left.base xε.1.left.fiber s) =
        dualNumberRingHom (algebraMap k P) (cBase s) := by
    change E₀ ((Algebra.IsPushout.equiv x₀.1.left.base xε.1.left.base
      x₀.1.left.fiber xε.1.left.fiber).symm
        (algebraMap xε.1.left.base xε.1.left.fiber s)) = _
    rw [Algebra.IsPushout.equiv_symm_algebraMap_left, hEtmul]
    simp [dualNumberRingHom]
  have hs (s : xε.1.left.base) (y : xε.1.left.fiber) :
      E (s • y) = dualNumberRingHom (algebraMap k P) (cBase s) * E y := by
    rw [Algebra.smul_def, map_mul, hes]
  have htop : infinitesimalAutomorphisms hp.cofibered g e hpair i hi = ⊤ := by
    apply top_unique
    intro γ _
    rw [mem_infinitesimalAutomorphisms_iff]
    let r := (canonicalRetraction hp.cofibered g e hpair.split i hi).val
    change γ.hom.val ≫ r = r
    apply Over.OverMorphism.ext
    apply FlatAlgebraCategory.Hom.ext
    · change γ.hom.val.left.base ≫ r.left.base = r.left.base
      rw [fiberAut_base_eq_id xε γ, Category.id_comp]
    · ext y
      apply a.injective
      have hR (z : xε.1.left.fiber) :
          x₀.1.hom.map.hom (r.left.map.hom z) = xε.1.hom.map.hom z :=
        congrArg (fun f => f.map.hom z) (Over.w r)
      change x₀.1.hom.map.hom (r.left.map.hom (γ.hom.val.left.map.hom y)) =
        x₀.1.hom.map.hom (r.left.map.hom y)
      rw [hR, hR]
      exact congrArg (fun f => f.map.hom y) (Over.w γ.hom.val)
  let H : infinitesimalAutomorphismGroup hp g e hpair i hi ≃* Aut xε :=
    (MulEquiv.subgroupCongr htop).trans (Subgroup.topEquiv (G := Aut xε))
  let F := derivationMulEquivFiberAut xε E cBase hs hEfst
  let Egrp : infinitesimalAutomorphismGroup hp g e hpair i hi ≃*
      Multiplicative (Derivation k P P) := H.trans F.symm
  have hcoords (γ : infinitesimalAutomorphismGroup hp g e hpair i hi) :
      F (Egrp γ) = γ.val :=
    F.apply_symm_apply (H γ)
  have hEgrp (γ : infinitesimalAutomorphismGroup hp g e hpair i hi) (z : P) :
      (E (γ.val.hom.val.left.map.hom (E.symm (TrivSqZeroExt.inl z)))).snd =
        (Multiplicative.toAdd (Egrp γ)) z := by
    rw [← derivationFiberAut_apply_snd xε E cBase hs hEfst (Multiplicative.toAdd (Egrp γ)) z]
    exact congrArg
      (fun α : Aut xε => (E (α.hom.val.left.map.hom (E.symm (TrivSqZeroExt.inl z)))).snd)
      (hcoords γ).symm
  refine ⟨Egrp, hEgrp, fun s γ => ⟨Egrp.symm (Multiplicative.ofAdd
    (s • Multiplicative.toAdd (Egrp γ))), fun z => ?_, fun γ' hγ' => ?_⟩⟩
  · rw [hEgrp, Egrp.apply_symm_apply, hEgrp]
    simp
  · refine Egrp.injective (Multiplicative.toAdd.injective (Derivation.ext fun z => ?_))
    have hh := hγ' z
    rw [hEgrp γ', hEgrp γ] at hh
    simpa using hh

end Deformation.Examples

end
