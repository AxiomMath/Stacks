module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Smooth.Quotient
public import StacksCore.RingTheory.Nakayama
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Geometric.Localization
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.Henselian.Quotient
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.ExistenceData
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Flatness
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.OfHenselization
public import StacksFrontier.RingTheory.HenselizationUniverse.Basic
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples

/-!
# Strict henselization of a deformation

Let `P` be a local `k`-algebra and let `Pˢʰ` be a strict henselization of `P` with respect to a
separable algebraic closure `κ(P) ⊆ κ^sep`. This file shows that strict henselizing the flat
algebra of a deformation of `P` produces a deformation of `Pˢʰ` over the same Artinian base.

For an object `(A, Q) → (k, P)` of the deformation category of `P` the kernel of `Q → P` is
nilpotent, so `Q` is local with the same residue field as `P`; a strict henselization `Qˢʰ` of
`Q` is flat over `Q` and hence over `A`, so `(A, Qˢʰ)` is again a flat algebra over an Artinian
base. That it is again *cartesian* over `(k, Pˢʰ)` is the identification
`Qˢʰ ⊗_A k = Qˢʰ ⊗_Q P = Pˢʰ`: `Qˢʰ/I Qˢʰ` and `Pˢʰ` are both henselian, both ind-étale over
`Q/I = P` and have the same residue field, so the comparison map between them is an isomorphism.

## Main definitions

* `Deformation.Examples.StrictHenselizationFunctorData`: a functor of deformation categories over
  `𝒞_Λ` together with the data exhibiting it as strict henselization.

## Implementation notes

The separable algebraic closure used to characterize the strict henselization of an individual
fibre is `SeparableClosure (maximalIdeal Q).ResidueField`, not the given `κ^sep`: the fibre's
residue field is not literally that of `P`, only isomorphic to it, and `κ^sep` is allowed to live
in a universe of its own. A strict henselization with respect to one separable algebraic closure
is one with respect to any other (`Stacks.StrictHenselization.IsStrictHenselization.reindex`).

## References

* [Stacks Project, Tag 0DYU](https://stacks.math.columbia.edu/tag/0DYU)
-/

@[expose] public section

open CategoryTheory
open IsLocalRing

universe u v w

namespace Deformation.Examples

variable {Λ : Type u} {k P : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  [CommRing P] [Algebra k P] [IsLocalRing P]
variable {κsep : Type v} [Field κsep]
  [Algebra (maximalIdeal P).ResidueField κsep]
  [IsSepClosure (maximalIdeal P).ResidueField κsep]
variable (Psh : Type w) [CommRing Psh] [IsLocalRing Psh]
  [Algebra P Psh] [Algebra k Psh] [IsScalarTower k P Psh]

/-- Strict henselization of deformations, including the identification of the fibre of the value
of the functor as a strict henselization of the original fibre and the compatibilities of the
resulting map out of each flat algebra. -/
structure StrictHenselizationFunctorData where
  /-- The functor of deformation categories over `𝒞_Λ`. -/
  functor : BasedFunctor
    (BasedCategory.ofFunctor
      (Over.forget (residueFieldAlgebra (Λ := Λ) (k := k) P) ⋙
        FlatAlgebraCategory.projection))
    (BasedCategory.ofFunctor
      (Over.forget (residueFieldAlgebra (Λ := Λ) (k := k) Psh) ⋙
        FlatAlgebraCategory.projection))
  /-- The flat algebra of a deformation of a local algebra is local. -/
  fiberLocal (X : ringDeformationCategory (Λ := Λ) (k := k) P) :
    IsLocalRing X.left.fiber
  /-- The flat algebra of the value of the functor is local. -/
  strictFiberLocal (X : ringDeformationCategory (Λ := Λ) (k := k) P) :
    IsLocalRing (functor.obj X).left.fiber
  /-- The strict henselization map out of the flat algebra of each deformation. -/
  fiberMap (X : ringDeformationCategory (Λ := Λ) (k := k) P) :
    X.left.fiber →+* (functor.obj X).left.fiber
  /-- That map exhibits the flat algebra of the value of the functor as a strict henselization of
  the original flat algebra. -/
  fiberStrict (X : ringDeformationCategory (Λ := Λ) (k := k) P) :
    letI : IsLocalRing X.left.fiber := fiberLocal X
    letI : IsLocalRing (functor.obj X).left.fiber := strictFiberLocal X
    letI : Algebra X.left.fiber (functor.obj X).left.fiber :=
      (fiberMap X).toAlgebra
    Stacks.StrictHenselization.IsStrictHenselization X.left.fiber
      (SeparableClosure (maximalIdeal X.left.fiber).ResidueField)
      (functor.obj X).left.fiber
  /-- The strict henselization map is a map of algebras over the common Artinian base. -/
  base_comm (X : ringDeformationCategory (Λ := Λ) (k := k) P)
      (a : X.left.base) :
    fiberMap X (algebraMap X.left.base X.left.fiber a) =
      algebraMap (functor.obj X).left.base (functor.obj X).left.fiber
        (cast (congrArg ArtinianLocalAlgCat.carrier
          (congrArg (fun F => F.obj X) functor.w).symm) a)
  /-- The strict henselization map is compatible with reduction to the special fibre. -/
  special_comm (X : ringDeformationCategory (Λ := Λ) (k := k) P)
      (q : X.left.fiber) :
    (functor.obj X).hom.map.hom (fiberMap X q) =
      algebraMap P Psh (X.hom.map.hom q)
  /-- The strict henselization maps are natural in morphisms of deformations. -/
  naturality {X Y : ringDeformationCategory (Λ := Λ) (k := k) P}
      (f : X ⟶ Y) (q : X.left.fiber) :
    (functor.map f).left.map.hom (fiberMap X q) =
      fiberMap Y (f.left.map.hom q)

/-! ### The fibre of a deformation is a local ring -/

/-- An ideal contained in a nilpotent ideal is nilpotent. -/
private theorem isNilpotent_of_le {R : Type*} [CommRing R] {I J : Ideal R}
    (hle : I ≤ J) (hJ : IsNilpotent J) : IsNilpotent I := by
  obtain ⟨n, hn⟩ := hJ
  have hpow : ∀ m : ℕ, I ^ m ≤ J ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, pow_succ]
        exact Ideal.mul_mono ih hle
  exact ⟨n, le_antisymm ((hpow n).trans (le_of_eq hn)) bot_le⟩

/-- The maximal ideal of an Artinian local ring is nilpotent. -/
private theorem isNilpotent_maximalIdeal_of_isArtinianRing (A : Type*) [CommRing A]
    [IsLocalRing A] [IsArtinianRing A] : IsNilpotent (maximalIdeal A) := by
  rw [← IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top]
  exact IsArtinianRing.isNilpotent_jacobson_bot

omit [IsLocalRing P] in
/-- The kernel of the map from a deformation to its special fibre is nilpotent: it is contained
in the ideal generated by the maximal ideal of the Artinian base, and that one is nilpotent. -/
private theorem deformationSpecialFiber_ker_isNilpotent
    (X : ringDeformationCategory (Λ := Λ) (k := k) P) :
    IsNilpotent (RingHom.ker (X.hom.map.hom : X.left.fiber →+* P)) := by
  refine isNilpotent_of_le (deformationSpecialFiber_ker_le_map_maximalIdeal X) ?_
  obtain ⟨n, hn⟩ := isNilpotent_maximalIdeal_of_isArtinianRing X.left.base
  refine ⟨n, ?_⟩
  rw [← Ideal.map_pow, hn]
  simp

/-- A ring admitting a surjection onto a local ring with nilpotent kernel is local. -/
private theorem isLocalRing_of_surjective_isNilpotent_ker
    {R S : Type w} [CommRing R] [CommRing S] [Nontrivial S] [IsLocalRing R]
    (f : S →+* R) (hf : Function.Surjective f)
    (hker : IsNilpotent (RingHom.ker f)) : IsLocalRing S := by
  have key : ∀ y : S, IsUnit (f y) → IsUnit y := fun y hy => by
    let e := RingHom.quotientKerEquivOfSurjective (f := f) hf
    refine hker.isUnit_quotient_mk_iff.mp ?_
    simpa [e, RingHom.quotientKerEquivOfSurjective_symm_apply] using hy.map e.symm.toRingHom
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  exact (isUnit_or_isUnit_one_sub_self (f x)).imp (key x) (fun h => key _ (by simpa using h))

/-- The flat algebra of a deformation of a local algebra is a local ring: it surjects onto the
special fibre with nilpotent kernel. -/
private theorem deformationFiber_isLocalRing
    (X : ringDeformationCategory (Λ := Λ) (k := k) P) :
    IsLocalRing X.left.fiber := by
  have hs := deformationSpecialFiberMap_surjective X
  change Function.Surjective (X.hom.map.hom : X.left.fiber →+* P) at hs
  have : Nontrivial X.left.fiber := Function.Surjective.nontrivial (β := P) hs
  exact isLocalRing_of_surjective_isNilpotent_ker
    (R := P) (S := X.left.fiber)
    (X.hom.map.hom : X.left.fiber →+* P) hs (deformationSpecialFiber_ker_isNilpotent X)

/-! ### Residue fields of the fibres -/

/-- A surjective local map of local rings induces an isomorphism of residue fields. -/
private noncomputable def maximalResidueFieldMapEquiv
    {Q R : Type w} [CommRing Q] [CommRing R] [IsLocalRing Q] [IsLocalRing R]
    (f : Q →+* R) [IsLocalHom f] (hf : Function.Surjective f) :
    (maximalIdeal Q).ResidueField ≃+* (maximalIdeal R).ResidueField := by
  let g := Ideal.ResidueField.map (maximalIdeal Q) (maximalIdeal R) f
    (maximalIdeal_comap f).symm
  refine RingEquiv.ofBijective g ⟨RingHom.injective _, ?_⟩
  intro y
  obtain ⟨p, rfl⟩ := Ideal.algebraMap_residueField_surjective (maximalIdeal R) y
  obtain ⟨q, hq⟩ := hf p
  exact ⟨algebraMap Q (maximalIdeal Q).ResidueField q, by
    simp [g, Ideal.ResidueField.map_algebraMap, hq]⟩

/-- The two spellings `R ⧸ 𝔪` and `Frac(R ⧸ 𝔪)` of the residue field of a local ring agree. -/
private noncomputable def residueFieldToMaximalResidueField
    (R : Type w) [CommRing R] [IsLocalRing R] :
    ResidueField R ≃+* (maximalIdeal R).ResidueField := by
  let p := maximalIdeal R
  letI : p.IsPrime := (maximalIdeal.isMaximal R).isPrime
  letI : IsLocalization.AtPrime R p := IsLocalization.self fun _ hx =>
    notMem_maximalIdeal.mp (by simpa [p] using hx)
  let e : R ≃+* Localization.AtPrime p :=
    (IsLocalization.algEquiv p.primeCompl R (Localization.AtPrime p)).toRingEquiv
  exact IsLocalRing.ResidueField.mapEquiv e

private theorem residueFieldToMaximalResidueField_residue
    (R : Type w) [CommRing R] [IsLocalRing R] (x : R) :
    residueFieldToMaximalResidueField R (residue R x) =
      algebraMap R (maximalIdeal R).ResidueField x := by
  let p := maximalIdeal R
  let : p.IsPrime := (maximalIdeal.isMaximal R).isPrime
  let : IsLocalization.AtPrime R p := IsLocalization.self fun _ hx =>
    notMem_maximalIdeal.mp (by simpa [p] using hx)
  let e := IsLocalization.algEquiv p.primeCompl R (Localization.AtPrime p)
  change IsLocalRing.ResidueField.mapEquiv e.toRingEquiv (residue R x) = _
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  change residue (Localization.AtPrime p) (e (algebraMap R R x)) = _
  rw [e.commutes]
  change residue (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p) x) =
    algebraMap R (ResidueField (Localization.AtPrime p)) x
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime p)
    (ResidueField (Localization.AtPrime p)) x,
    IsLocalRing.ResidueField.algebraMap_eq]

/-- A strict henselization carries the residue field point of `r` to that of its image. -/
private theorem residueFieldEquiv_algebraMap_apply
    {R S : Type w} {κ : Type v} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Field κ] [Algebra (maximalIdeal R).ResidueField κ]
    [IsSepClosure (maximalIdeal R).ResidueField κ] [Algebra R S]
    (h : Stacks.StrictHenselization.IsStrictHenselization R κ S) (r : R) :
    h.residueFieldEquiv (algebraMap _ κ (algebraMap R (maximalIdeal R).ResidueField r)) =
      residueFieldToMaximalResidueField S (residue S (algebraMap R S r)) := by
  simpa [residueFieldToMaximalResidueField_residue, Ideal.ResidueField.map_algebraMap] using
    RingHom.congr_fun h.residueFieldEquiv_comp (algebraMap R (maximalIdeal R).ResidueField r)

/-! ### A chosen strict henselization of each fibre -/

/-- A chosen strict henselization of the local ring `Q` with respect to a chosen separable
algebraic closure `κ` of its residue field, together with that `κ(Q)`-algebra structure on `κ`.
Both are chosen, which is why they are bundled: the `κ(Q)`-algebra structure on `κ` is
transported from a `κ(P)`-algebra structure along an isomorphism of residue fields. -/
private structure FiberStrictData (Q : Type w) [CommRing Q] [IsLocalRing Q]
    (κ : Type v) [Field κ] where
  /-- The transported `κ(Q)`-algebra structure on `κ`. -/
  residueAlgebra : Algebra (maximalIdeal Q).ResidueField κ
  /-- The transported separable-closure property. -/
  sepClosure : IsSepClosure (maximalIdeal Q).ResidueField κ
  /-- The underlying type of the chosen strict henselization. -/
  carrier : Type w
  [commRing : CommRing carrier]
  [isLocalRing : IsLocalRing carrier]
  [algebra : Algebra Q carrier]
  /-- The chosen algebra is a strict henselization of `Q` with respect to `κ`. -/
  strict : letI := residueAlgebra
    letI := sepClosure
    Stacks.StrictHenselization.IsStrictHenselization Q κ carrier

/-- A chosen strict henselization of the flat algebra of a deformation, with respect to the given
separable algebraic closure of the residue field of `P`, transported to the residue field of the
flat algebra along the isomorphism induced by the surjection onto the special fibre. -/
private noncomputable def fiberStrictData
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    [IsLocalRing X.left.fiber] (κ : Type v) [Field κ]
    [Algebra (maximalIdeal P).ResidueField κ]
    [IsSepClosure (maximalIdeal P).ResidueField κ] :
    FiberStrictData X.left.fiber κ := by
  let Q := X.left.fiber
  let f : Q →+* P := X.hom.map.hom
  have hf : Function.Surjective f := deformationSpecialFiberMap_surjective X
  haveI : IsLocalHom f := IsLocalHom.of_surjective f hf
  let e := maximalResidueFieldMapEquiv f hf
  letI : Algebra (maximalIdeal Q).ResidueField κ :=
    ((algebraMap (maximalIdeal P).ResidueField κ).comp e.toRingHom).toAlgebra
  have hcompat : (algebraMap (maximalIdeal Q).ResidueField κ).comp
      (e.symm : (maximalIdeal P).ResidueField →+* (maximalIdeal Q).ResidueField) =
      algebraMap (maximalIdeal P).ResidueField κ := by
    rw [RingHom.algebraMap_toAlgebra]
    ext x
    simp
  have hsep : Algebra.IsSeparable (maximalIdeal Q).ResidueField κ :=
    Algebra.IsSeparable.of_equiv_equiv
      (e.symm : (maximalIdeal P).ResidueField ≃+* (maximalIdeal Q).ResidueField)
      (RingEquiv.refl κ) hcompat
  letI : IsSepClosure (maximalIdeal Q).ResidueField κ :=
    ⟨IsSepClosure.sep_closed (maximalIdeal P).ResidueField, hsep⟩
  let hExist := Stacks.StrictHenselization.exists_isStrictHenselization Q κ
  let S := Classical.choose hExist
  let h1 := Classical.choose_spec hExist
  let cRing : CommRing S := Classical.choose h1
  let h2 := Classical.choose_spec h1
  let cLocal : IsLocalRing S := Classical.choose h2
  let h3 := Classical.choose_spec h2
  let cAlg : Algebra Q S := Classical.choose h3
  let h4 := Classical.choose_spec h3
  let hS : Stacks.StrictHenselization.IsStrictHenselization Q κ S := Classical.choice h4
  exact {
    residueAlgebra := inferInstance
    sepClosure := inferInstance
    carrier := S
    commRing := cRing
    isLocalRing := cLocal
    algebra := cAlg
    strict := hS }

/-- The chosen strict henselization of a fibre is a strict henselization with respect to the
canonical separable closure of the residue field of that fibre as well. -/
private noncomputable def fiberStrictCanonical
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    [IsLocalRing X.left.fiber] :
    let D := fiberStrictData X κsep
    letI : CommRing D.carrier := D.commRing
    letI : IsLocalRing D.carrier := D.isLocalRing
    letI : Algebra X.left.fiber D.carrier := D.algebra
    Stacks.StrictHenselization.IsStrictHenselization X.left.fiber
      (SeparableClosure (maximalIdeal X.left.fiber).ResidueField) D.carrier := by
  let D := fiberStrictData X κsep
  letI : CommRing D.carrier := D.commRing
  letI : IsLocalRing D.carrier := D.isLocalRing
  letI : Algebra (maximalIdeal X.left.fiber).ResidueField κsep := D.residueAlgebra
  letI : IsSepClosure (maximalIdeal X.left.fiber).ResidueField κsep := D.sepClosure
  letI : Algebra X.left.fiber D.carrier := D.algebra
  exact D.strict.reindex
    (IsSepClosure.equiv (maximalIdeal X.left.fiber).ResidueField
      (SeparableClosure (maximalIdeal X.left.fiber).ResidueField) κsep)

/-! ### Specialization of the chosen strict henselization to `Pˢʰ` -/

/-- The identification of the residue field of the chosen strict henselization of a fibre with
that of `Pˢʰ`: both are identified with `κ^sep`. -/
private noncomputable def fiberSpecializationResidueEquiv
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    [IsLocalRing X.left.fiber]
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    let D := fiberStrictData X κsep
    letI : CommRing D.carrier := D.commRing
    letI : IsLocalRing D.carrier := D.isLocalRing
    ResidueField D.carrier ≃+* ResidueField Psh := by
  let D := fiberStrictData X κsep
  letI : CommRing D.carrier := D.commRing
  letI : IsLocalRing D.carrier := D.isLocalRing
  letI : Algebra X.left.fiber D.carrier := D.algebra
  letI : Algebra (maximalIdeal X.left.fiber).ResidueField κsep := D.residueAlgebra
  letI : IsSepClosure (maximalIdeal X.left.fiber).ResidueField κsep := D.sepClosure
  let eQ := residueFieldToMaximalResidueField D.carrier
  let eP := residueFieldToMaximalResidueField Psh
  exact eQ.trans
    ((D.strict.residueFieldEquiv.symm.trans hsh.residueFieldEquiv).trans eP.symm)

omit [Algebra k Psh] [IsScalarTower k P Psh] in
/-- The chosen strict henselization of a fibre maps to `Pˢʰ`, compatibly with the identification
of residue fields: this is the unique local lift out of an ind-étale algebra into a henselian
local ring inducing a prescribed map of residue fields. -/
private theorem fiberSpecializationMap_exists
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    [IsLocalRing X.left.fiber]
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    let D := fiberStrictData X κsep
    letI : CommRing D.carrier := D.commRing
    letI : IsLocalRing D.carrier := D.isLocalRing
    letI : Algebra X.left.fiber D.carrier := D.algebra
    letI : Algebra X.left.fiber Psh :=
      ((algebraMap P Psh).comp X.hom.map.hom).toAlgebra
    ∃ g : D.carrier →ₐ[X.left.fiber] Psh,
      (residue Psh).comp g.toRingHom =
        (fiberSpecializationResidueEquiv Psh X hsh).toRingHom.comp
          (residue D.carrier) := by
  let D := fiberStrictData X κsep
  let : CommRing D.carrier := D.commRing
  let : IsLocalRing D.carrier := D.isLocalRing
  let : Algebra X.left.fiber D.carrier := D.algebra
  let : Algebra (maximalIdeal X.left.fiber).ResidueField κsep := D.residueAlgebra
  let : IsSepClosure (maximalIdeal X.left.fiber).ResidueField κsep := D.sepClosure
  let f : X.left.fiber →+* P := X.hom.map.hom
  have hf : Function.Surjective f := deformationSpecialFiberMap_surjective X
  have : IsLocalHom f := IsLocalHom.of_surjective f hf
  let : Algebra X.left.fiber Psh :=
    ((algebraMap P Psh).comp f).toAlgebra
  let : HenselianLocalRing Psh := hsh.henselian
  let eQ := residueFieldToMaximalResidueField D.carrier
  let eP := residueFieldToMaximalResidueField Psh
  let φ : ResidueField D.carrier ≃+* ResidueField Psh :=
    fiberSpecializationResidueEquiv Psh X hsh
  let e := maximalResidueFieldMapEquiv f hf
  have hres (y : (maximalIdeal X.left.fiber).ResidueField) :
      algebraMap (maximalIdeal X.left.fiber).ResidueField κsep y =
        algebraMap (maximalIdeal P).ResidueField κsep (e y) := rfl
  have hQP (x : X.left.fiber) :
      algebraMap X.left.fiber Psh x = algebraMap P Psh (f x) := rfl
  have hφ : RingHom.comp (φ : ResidueField D.carrier →+* ResidueField Psh)
      (RingHom.comp (residue D.carrier) (algebraMap X.left.fiber D.carrier)) =
      RingHom.comp (residue Psh) (algebraMap X.left.fiber Psh) := by
    apply RingHom.ext
    intro x
    apply eP.injective
    simp only [RingHom.comp_apply]
    change eP (φ (residue D.carrier (algebraMap X.left.fiber D.carrier x))) =
      eP (residue Psh (algebraMap X.left.fiber Psh x))
    simp only [φ, fiberSpecializationResidueEquiv, RingEquiv.trans_apply]
    rw [RingEquiv.apply_symm_apply]
    have hD' := residueFieldEquiv_algebraMap_apply D.strict x
    have hDsymm : D.strict.residueFieldEquiv.symm
        (eQ (residue D.carrier (algebraMap X.left.fiber D.carrier x))) =
        algebraMap (maximalIdeal X.left.fiber).ResidueField κsep
          (algebraMap X.left.fiber (maximalIdeal X.left.fiber).ResidueField x) := by
      rw [← hD']
      simp
    have hP' := residueFieldEquiv_algebraMap_apply hsh (f x)
    have hresx : e (algebraMap X.left.fiber
        (maximalIdeal X.left.fiber).ResidueField x) =
        algebraMap P (maximalIdeal P).ResidueField (f x) := by
      change Ideal.ResidueField.map (maximalIdeal X.left.fiber) (maximalIdeal P) f
        (maximalIdeal_comap f).symm
        (algebraMap X.left.fiber (maximalIdeal X.left.fiber).ResidueField x) = _
      rw [Ideal.ResidueField.map_algebraMap]
    calc
      hsh.residueFieldEquiv
          (D.strict.residueFieldEquiv.symm
            (eQ (residue D.carrier (algebraMap X.left.fiber D.carrier x)))) =
        hsh.residueFieldEquiv
          (algebraMap (maximalIdeal X.left.fiber).ResidueField κsep
            (algebraMap X.left.fiber (maximalIdeal X.left.fiber).ResidueField x)) := by
          rw [hDsymm]
      _ = hsh.residueFieldEquiv
          (algebraMap (maximalIdeal P).ResidueField κsep
            (algebraMap P (maximalIdeal P).ResidueField (f x))) := by
        rw [hres, hresx]
      _ = eP (residue Psh (algebraMap X.left.fiber Psh x)) := hP'
  let hExist := StacksDraft.existsUnique_isLocalHom_comp_residue_of_indEtale
    D.strict.isFilteredColimitEtale φ.toRingHom hφ
  exact ⟨Classical.choose hExist, (Classical.choose_spec hExist).1.2⟩

/-- The map from the chosen strict henselization of a fibre to `Pˢʰ`. -/
private noncomputable def fiberSpecializationMap
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    [IsLocalRing X.left.fiber]
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    let D := fiberStrictData X κsep
    letI : CommRing D.carrier := D.commRing
    letI : IsLocalRing D.carrier := D.isLocalRing
    letI : Algebra X.left.fiber D.carrier := D.algebra
    letI : Algebra X.left.fiber Psh :=
      ((algebraMap P Psh).comp X.hom.map.hom).toAlgebra
    D.carrier →ₐ[X.left.fiber] Psh :=
  Classical.choose (fiberSpecializationMap_exists Psh X hsh)

omit [Algebra k Psh] [IsScalarTower k P Psh] in
private theorem fiberSpecializationMap_residue
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    [IsLocalRing X.left.fiber]
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    let D := fiberStrictData X κsep
    letI : CommRing D.carrier := D.commRing
    letI : IsLocalRing D.carrier := D.isLocalRing
    letI : Algebra X.left.fiber D.carrier := D.algebra
    letI : Algebra X.left.fiber Psh :=
      ((algebraMap P Psh).comp X.hom.map.hom).toAlgebra
    (residue Psh).comp (fiberSpecializationMap Psh X hsh).toRingHom =
      (fiberSpecializationResidueEquiv Psh X hsh).toRingHom.comp
        (residue D.carrier) :=
  Classical.choose_spec (fiberSpecializationMap_exists Psh X hsh)

omit [Algebra k Psh] [IsScalarTower k P Psh] in
private theorem fiberSpecializationMap_residue_surjective
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    [IsLocalRing X.left.fiber]
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    let D := fiberStrictData X κsep
    letI : CommRing D.carrier := D.commRing
    letI : IsLocalRing D.carrier := D.isLocalRing
    letI : Algebra X.left.fiber D.carrier := D.algebra
    letI : Algebra X.left.fiber Psh :=
      ((algebraMap P Psh).comp X.hom.map.hom).toAlgebra
    Function.Surjective
      ((residue Psh).comp (fiberSpecializationMap Psh X hsh).toRingHom) := by
  let D := fiberStrictData X κsep
  let : CommRing D.carrier := D.commRing
  let : IsLocalRing D.carrier := D.isLocalRing
  let : Algebra X.left.fiber D.carrier := D.algebra
  let : Algebra X.left.fiber Psh :=
    ((algebraMap P Psh).comp X.hom.map.hom).toAlgebra
  rw [fiberSpecializationMap_residue]
  exact (fiberSpecializationResidueEquiv Psh X hsh).surjective.comp
    residue_surjective

omit [Algebra k Psh] [IsScalarTower k P Psh] in
private theorem fiberSpecializationMap_comp
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    [IsLocalRing X.left.fiber]
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh)
    (q : X.left.fiber) :
    let D := fiberStrictData X κsep
    letI : CommRing D.carrier := D.commRing
    letI : IsLocalRing D.carrier := D.isLocalRing
    letI : Algebra X.left.fiber D.carrier := D.algebra
    (fiberSpecializationMap Psh X hsh)
        (algebraMap X.left.fiber D.carrier q) =
      algebraMap P Psh (X.hom.map.hom q) := by
  let D := fiberStrictData X κsep
  let : CommRing D.carrier := D.commRing
  let : IsLocalRing D.carrier := D.isLocalRing
  let : Algebra X.left.fiber D.carrier := D.algebra
  let : Algebra X.left.fiber Psh :=
    ((algebraMap P Psh).comp X.hom.map.hom).toAlgebra
  exact (fiberSpecializationMap Psh X hsh).commutes q

/-! ### The strict henselization of a deformation is a deformation of `Pˢʰ` -/

/-- The flat algebra of a deformation, with its fibre replaced by the chosen strict
henselization: flat over the base, because the strict henselization is flat over the fibre. -/
private noncomputable def fiberStrictFlatObject
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    [IsLocalRing X.left.fiber] :
    FlatAlgebraCategory.{u, w} Λ k := by
  let D := fiberStrictData X κsep
  letI : CommRing D.carrier := D.commRing
  letI : IsLocalRing D.carrier := D.isLocalRing
  letI : Algebra X.left.fiber D.carrier := D.algebra
  letI : Algebra (maximalIdeal X.left.fiber).ResidueField κsep := D.residueAlgebra
  letI : IsSepClosure (maximalIdeal X.left.fiber).ResidueField κsep := D.sepClosure
  letI : Module.Flat X.left.fiber D.carrier := D.strict.flat
  letI : Algebra X.left.base D.carrier :=
    ((algebraMap X.left.fiber D.carrier).comp
      (algebraMap X.left.base X.left.fiber)).toAlgebra
  letI : IsScalarTower X.left.base X.left.fiber D.carrier :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact {
    base := X.left.base
    fiber := D.carrier
    commRing := D.commRing
    algebra := inferInstance
    flat := Module.Flat.trans X.left.base X.left.fiber D.carrier }

/-- Reduction modulo an ideal of the base preserves ind-étaleness: reduction is a pushout. -/
private theorem indEtale_quotient {R S : Type w} [CommRing R] [CommRing S]
    [Algebra R S] (I : Ideal R)
    (h : (CommAlgCat.etale.{w} R).ind.{w} (CommAlgCat.of R S)) :
    letI : Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    (CommAlgCat.etale.{w} (R ⧸ I)).ind.{w}
      (CommAlgCat.of (R ⧸ I) (S ⧸ I.map (algebraMap R S))) := by
  let : Algebra.IsPushout R (R ⧸ I) S
      (S ⧸ I.map (algebraMap R S)) := Stacks.Henselian.isPushout_quotient_map I
  exact CommAlgCat.ind_etale_of_isPushout R (R ⧸ I) S
    (S ⧸ I.map (algebraMap R S)) h

/-- Two henselian local ind-étale algebras with the same residue point are identified by any
algebra map between them compatible with that point. -/
private theorem algHom_bijective_of_indEtale_henselian_residue
    {R S T : Type w} {K : Type v}
    [CommRing R] [CommRing S] [CommRing T] [Field K]
    [Algebra R S] [Algebra R T] [Algebra R K]
    [HenselianLocalRing S] [HenselianLocalRing T]
    (hS : (CommAlgCat.etale.{w} R).ind.{w} (CommAlgCat.of R S))
    (hT : (CommAlgCat.etale.{w} R).ind.{w} (CommAlgCat.of R T))
    (p : S →ₐ[R] K) (q : T →ₐ[R] K)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (f : S →ₐ[R] T) (hf : q.comp f = p) : Function.Bijective f := by
  obtain ⟨e, he⟩ := HenselianLocalRing.existsUnique_algEquiv_of_ind_etale
    hS hT p q hp hq
  have : f = (e : S →ₐ[R] T) := (he f).mp hf
  subst f
  exact e.bijective

/-- The reduction of the chosen strict henselization of a fibre modulo the kernel of the map to
the special fibre, mapped to `Pˢʰ`. -/
private noncomputable def fiberQuotientMap
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    [IsLocalRing X.left.fiber]
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    let Q := X.left.fiber
    let D := fiberStrictData X κsep
    letI : CommRing D.carrier := D.commRing
    letI : IsLocalRing D.carrier := D.isLocalRing
    letI : Algebra Q D.carrier := D.algebra
    let I := RingHom.ker (X.hom.map.hom : Q →+* P)
    D.carrier ⧸ I.map (algebraMap Q D.carrier) →+* Psh := by
  let Q := X.left.fiber
  let D := fiberStrictData X κsep
  letI : CommRing D.carrier := D.commRing
  letI : IsLocalRing D.carrier := D.isLocalRing
  letI : Algebra Q D.carrier := D.algebra
  letI : Algebra Q Psh :=
    ((algebraMap P Psh).comp X.hom.map.hom).toAlgebra
  let I := RingHom.ker (X.hom.map.hom : Q →+* P)
  let J := I.map (algebraMap Q D.carrier)
  let g := fiberSpecializationMap Psh X hsh
  have hJ : J ≤ RingHom.ker g.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro q hq
    change g (algebraMap Q D.carrier q) = 0
    exact (fiberSpecializationMap_comp Psh X hsh q).trans
      ((congrArg (algebraMap P Psh) (RingHom.mem_ker.mp hq)).trans (map_zero _))
  exact Ideal.Quotient.lift J g.toRingHom hJ

omit [Algebra k Psh] [IsScalarTower k P Psh] in
private theorem fiberQuotientMap_residue_surjective
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    [IsLocalRing X.left.fiber]
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    let Q := X.left.fiber
    let D := fiberStrictData X κsep
    letI : CommRing D.carrier := D.commRing
    letI : IsLocalRing D.carrier := D.isLocalRing
    letI : Algebra Q D.carrier := D.algebra
    Function.Surjective
      ((residue Psh).comp (fiberQuotientMap Psh X hsh)) := by
  let Q := X.left.fiber
  let D := fiberStrictData X κsep
  let : CommRing D.carrier := D.commRing
  let : IsLocalRing D.carrier := D.isLocalRing
  let : Algebra Q D.carrier := D.algebra
  let I := RingHom.ker (X.hom.map.hom : Q →+* P)
  change Function.Surjective
    ((residue Psh).comp (fiberQuotientMap Psh X hsh))
  intro y
  obtain ⟨s, hs⟩ := fiberSpecializationMap_residue_surjective Psh X hsh y
  refine ⟨Ideal.Quotient.mk (I.map (algebraMap Q D.carrier)) s, ?_⟩
  change residue Psh ((fiberSpecializationMap Psh X hsh) s) = y
  exact hs

omit [Algebra k Psh] [IsScalarTower k P Psh] in
/-- **Stacks 05WS for the chosen strict henselization of a fibre.** The reduction of the chosen
strict henselization of a fibre modulo the kernel of the map to the special fibre is `Pˢʰ`: both
are henselian local, ind-étale over the special fibre `Q/I = P`, and carry the same residue
point. -/
private theorem fiberQuotientMap_bijective
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    [IsLocalRing X.left.fiber]
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    let Q := X.left.fiber
    let D := fiberStrictData X κsep
    letI : CommRing D.carrier := D.commRing
    letI : IsLocalRing D.carrier := D.isLocalRing
    letI : Algebra Q D.carrier := D.algebra
    Function.Bijective (fiberQuotientMap Psh X hsh) := by
  let Q := X.left.fiber
  let D := fiberStrictData X κsep
  let : CommRing D.carrier := D.commRing
  let : IsLocalRing D.carrier := D.isLocalRing
  let : Algebra Q D.carrier := D.algebra
  let : Algebra (maximalIdeal Q).ResidueField κsep := D.residueAlgebra
  let : IsSepClosure (maximalIdeal Q).ResidueField κsep := D.sepClosure
  let f : Q →+* P := X.hom.map.hom
  let I := RingHom.ker f
  let J := I.map (algebraMap Q D.carrier)
  let e : Q ⧸ I ≃+* P := RingHom.quotientKerEquivOfSurjective
    (deformationSpecialFiberMap_surjective X)
  let : Algebra (Q ⧸ I) (D.carrier ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : Algebra (Q ⧸ I) Psh :=
    ((algebraMap P Psh).comp e.toRingHom).toAlgebra
  let : Algebra (Q ⧸ I) (ResidueField Psh) :=
    ((residue Psh).comp (algebraMap (Q ⧸ I) Psh)).toAlgebra
  let : IsScalarTower (Q ⧸ I) Psh (ResidueField Psh) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : HenselianLocalRing Psh := hsh.henselian
  have hIle : I ≤ maximalIdeal Q := by
    have : IsLocalHom f := IsLocalHom.of_surjective f
      (deformationSpecialFiberMap_surjective X)
    intro q hq
    rw [← IsLocalRing.maximalIdeal_comap f]
    change f q ∈ maximalIdeal P
    rw [RingHom.mem_ker.mp hq]
    exact Ideal.zero_mem _
  have hJle : J ≤ maximalIdeal D.carrier := by
    rw [← D.strict.maximalIdeal_map]
    exact Ideal.map_mono hIle
  let : HenselianLocalRing D.carrier := D.strict.henselian
  let : HenselianLocalRing (D.carrier ⧸ J) :=
    Stacks.Henselian.henselianLocalRing_quotient
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal D.carrier).ne_top hJle)
  have hS : (CommAlgCat.etale.{w} (Q ⧸ I)).ind.{w}
      (CommAlgCat.of (Q ⧸ I) (D.carrier ⧸ J)) :=
    indEtale_quotient I (StacksDraft.indEtale_iff.mp D.strict.isFilteredColimitEtale)
  have hT : (CommAlgCat.etale.{w} (Q ⧸ I)).ind.{w}
      (CommAlgCat.of (Q ⧸ I) Psh) := by
    apply StacksDraft.indEtale_iff.mp
    apply StacksDraft.indEtale_of_equiv e.symm (RingEquiv.refl Psh)
      (fun p => ?_) hsh.isFilteredColimitEtale
    change algebraMap P Psh p = algebraMap (Q ⧸ I) Psh (e.symm p)
    rw [RingHom.algebraMap_toAlgebra]
    simp
  let g : (D.carrier ⧸ J) →ₐ[Q ⧸ I] Psh :=
    { fiberQuotientMap Psh X hsh with
      commutes' := by
        intro x
        obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
        change (fiberSpecializationMap Psh X hsh)
          (algebraMap Q D.carrier q) = algebraMap P Psh (f q)
        exact fiberSpecializationMap_comp Psh X hsh q }
  let q : Psh →ₐ[Q ⧸ I] ResidueField Psh :=
    IsScalarTower.toAlgHom (Q ⧸ I) Psh (ResidueField Psh)
  let p : (D.carrier ⧸ J) →ₐ[Q ⧸ I] ResidueField Psh := q.comp g
  exact algHom_bijective_of_indEtale_henselian_residue hS hT p q
    (fiberQuotientMap_residue_surjective Psh X hsh) residue_surjective g rfl

omit [Algebra k Psh] [IsScalarTower k P Psh] in
/-- The square comparing a fibre with its chosen strict henselization and the special fibre with
`Pˢʰ` is a pushout: the comparison map becomes an isomorphism after reduction. -/
private theorem fiberSpecialization_isPushout
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    [IsLocalRing X.left.fiber]
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    let D := fiberStrictData X κsep
    letI : CommRing D.carrier := D.commRing
    letI : IsLocalRing D.carrier := D.isLocalRing
    letI : Algebra X.left.fiber D.carrier := D.algebra
    letI : Algebra X.left.fiber Psh :=
      ((algebraMap P Psh).comp X.hom.map.hom).toAlgebra
    IsPushout
      (CommRingCat.ofHom (X.hom.map.hom : X.left.fiber →+* P))
      (CommRingCat.ofHom (algebraMap X.left.fiber D.carrier))
      (CommRingCat.ofHom (algebraMap P Psh))
      (CommRingCat.ofHom (fiberSpecializationMap Psh X hsh).toRingHom) := by
  let Q := X.left.fiber
  let D := fiberStrictData X κsep
  let : CommRing D.carrier := D.commRing
  let : IsLocalRing D.carrier := D.isLocalRing
  let : Algebra Q D.carrier := D.algebra
  let : Algebra Q Psh :=
    ((algebraMap P Psh).comp X.hom.map.hom).toAlgebra
  let f : Q →+* P := X.hom.map.hom
  let I := RingHom.ker f
  let J := I.map (algebraMap Q D.carrier)
  let e : Q ⧸ I ≃+* P := RingHom.quotientKerEquivOfSurjective
    (deformationSpecialFiberMap_surjective X)
  let b : D.carrier ⧸ J ≃+* Psh :=
    RingEquiv.ofBijective (fiberQuotientMap Psh X hsh)
      (fiberQuotientMap_bijective Psh X hsh)
  let : Algebra (Q ⧸ I) (D.carrier ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have h₀ : IsPushout
      (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (algebraMap Q D.carrier))
      (CommRingCat.ofHom (algebraMap (Q ⧸ I) (D.carrier ⧸ J)))
      (CommRingCat.ofHom (Ideal.Quotient.mk J)) :=
    (CommRingCat.isPushout_iff_isPushout
      (R := Q) (R' := Q ⧸ I) (S := D.carrier)
      (S' := D.carrier ⧸ J)).mpr (Stacks.Henselian.isPushout_quotient_map I)
  apply h₀.of_iso (Iso.refl _) e.toCommRingCatIso
    (Iso.refl _) b.toCommRingCatIso
  · apply CommRingCat.hom_ext
    ext q
    change e (Ideal.Quotient.mk I q) = f q
    exact RingHom.quotientKerEquivOfSurjective_apply_mk
      (deformationSpecialFiberMap_surjective X) q
  · simp
  · apply CommRingCat.hom_ext
    ext q
    change (fiberSpecializationMap Psh X hsh)
      (algebraMap Q D.carrier q) = algebraMap P Psh (f q)
    exact fiberSpecializationMap_comp Psh X hsh q
  · apply CommRingCat.hom_ext
    ext s
    rfl

/-- The strict henselization of a deformation, as a morphism of flat algebras to `(k, Pˢʰ)`. -/
private noncomputable def fiberStrictSpecializationHom
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    [IsLocalRing X.left.fiber]
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    fiberStrictFlatObject (κsep := κsep) X ⟶
      residueFieldAlgebra (Λ := Λ) (k := k) Psh := by
  let D := fiberStrictData X κsep
  letI : CommRing D.carrier := D.commRing
  letI : IsLocalRing D.carrier := D.isLocalRing
  letI : Algebra X.left.fiber D.carrier := D.algebra
  letI : Algebra X.left.fiber Psh :=
    ((algebraMap P Psh).comp X.hom.map.hom).toAlgebra
  refine {
    base := X.hom.base
    map := CommRingCat.ofHom (fiberSpecializationMap Psh X hsh).toRingHom
    cartesian := ?_ }
  change IsPushout
    (CommRingCat.ofHom
      ((algebraMap X.left.fiber D.carrier).comp
        (algebraMap X.left.base X.left.fiber)))
    (FlatAlgebraCategory.baseMap X.hom.base)
    (CommRingCat.ofHom (fiberSpecializationMap Psh X hsh).toRingHom)
    (CommRingCat.ofHom (algebraMap k Psh))
  convert X.hom.cartesian.paste_horiz
    (fiberSpecialization_isPushout Psh X hsh).flip using 1
  all_goals first
    | rfl
    | apply CommRingCat.hom_ext
      ext x
      change algebraMap k Psh x = algebraMap P Psh (algebraMap k P x)
      exact IsScalarTower.algebraMap_apply k P Psh x

/-- The value of the strict henselization functor on a deformation. -/
private noncomputable def fiberStrictOver
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    (hsh : Stacks.StrictHenselization.IsStrictHenselization P κsep Psh) :
    ringDeformationCategory (Λ := Λ) (k := k) Psh := by
  letI : IsLocalRing X.left.fiber := deformationFiber_isLocalRing X
  exact Over.mk (fiberStrictSpecializationHom Psh X hsh)

end Deformation.Examples

end
