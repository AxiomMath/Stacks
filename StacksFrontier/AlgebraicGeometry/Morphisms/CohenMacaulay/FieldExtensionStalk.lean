module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.FieldToResidue
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.AffineBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Local rings after extension of the ground field

Let `K / k` be an extension of fields and let `Y = X ×[Spec k] Spec K`. At a point `y` of `Y`
lying over `x : X`, the local ring of `Y` is the localization of `𝒪_{X,x} ⊗_k K` at the prime
induced by the map to `κ(y)`.

## Main definitions

* `AlgebraicGeometry.fieldToStalk` is the structural map from the ground field to a stalk.
* `AlgebraicGeometry.fieldToResidue` is the structural map from the ground field to a residue
  field.
* `AlgebraicGeometry.stalkBaseChangeRing` is `𝒪_{X,x} ⊗_k K`, expressed as a pushout of
  commutative rings.
* `AlgebraicGeometry.residueBaseChangeRing` is `κ(x) ⊗_k K`.
* `AlgebraicGeometry.stalkBaseChangePrime` is the inverse image in the stalk tensor product of
  the kernel in the residue-field tensor product.
* `AlgebraicGeometry.stalkBaseChangeResidueMap`,
  `AlgebraicGeometry.residueBaseChangeToResidueField` and
  `AlgebraicGeometry.stalkBaseChangeToStalk` are the canonical maps relating these two tensor
  products with the local ring and the residue field at a point of the base change.

## Main results

* `AlgebraicGeometry.isLocalization_stalkBaseChangePrime` identifies the local ring at a point
  of the base change as the localization of the stalk tensor product at that prime.
* `AlgebraicGeometry.stalkOfBaseChange_isLocalization` identifies the local ring at a point of
  the base change as the localization of that tensor product at the prime induced by its
  residue-field map.

## Implementation notes

Tensor products of commutative algebras are pushouts in `CommRingCat`. The equations in the
result characterize all the canonical maps. In particular, `p₀` is literally the kernel of
`κ(x) ⊗_k K → κ(y)`, and `p` is its inverse image under `𝒪_{X,x} ⊗_k K → κ(x) ⊗_k K`.
`IsLocalization.AtPrime` is the choice-independent form of the displayed equality of local
rings.

## References

* [Stacks Project, Tag 0C4Y](https://stacks.math.columbia.edu/tag/0C4Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The tensor product `𝒪_{X,x} ⊗_k K`, represented by its categorical pushout. -/
public noncomputable def stalkBaseChangeRing {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) : CommRingCat :=
  pushout (fieldToStalk f x) (CommRingCat.ofHom (algebraMap k K : k →+* K))

/-- The tensor product `κ(x) ⊗_k K`, represented by its categorical pushout. -/
public noncomputable def residueBaseChangeRing {k K : Type u}
    [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) : CommRingCat :=
  pushout (fieldToResidue f x) (CommRingCat.ofHom (algebraMap k K : k →+* K))

/-- The inverse image in `𝒪_{X,x} ⊗_k K` of the kernel of the map from the residue-field tensor
product to `κ(y)`. Equivalently, this is the kernel of the composite from the stalk tensor
product to `κ(y)`. -/
public noncomputable def stalkBaseChangePrime {k K : Type u}
    [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X)
    (θ : stalkBaseChangeRing (K := K) f x ⟶ residueBaseChangeRing (K := K) f x)
    (p₀ : Ideal (residueBaseChangeRing (K := K) f x)) :
    Ideal (stalkBaseChangeRing (K := K) f x) :=
  Ideal.comap θ.hom p₀

/-- The structural map from the ground field is natural in the scheme. -/
private lemma fieldToStalk_natural {k : Type u} [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Z ⟶ X) (z : Z) :
    fieldToStalk f (g z) ≫ g.stalkMap z = fieldToStalk (g ≫ f) z := by
  have hz : g z ∈ (⊤ : X.Opens) := by simp
  change (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      (X.presheaf.germ ⊤ (g z) hz ≫ g.stalkMap z) =
    (Scheme.ΓSpecIso (.of k)).inv ≫ (g ≫ f).appTop ≫ Z.presheaf.germ ⊤ z trivial
  rw [Scheme.Hom.germ_stalkMap (f := g) ⊤ z hz, Scheme.Hom.comp_appTop]
  simp [Category.assoc]

/-- For the spectrum of a field extension viewed over the smaller field, the structural map
factors through the extension. -/
private lemma fieldToStalk_specMap (k K : Type u) [Field k] [Field K]
    [Algebra k K] (z : Spec (.of K)) :
    fieldToStalk (Spec.map (CommRingCat.ofHom (algebraMap k K))) z =
      CommRingCat.ofHom (algebraMap k K) ≫ fieldToStalk (𝟙 (Spec (.of K))) z := by
  simp [fieldToStalk]

/-- The structural map from the ground field to a stalk of a base change along a field extension
is the structural map of the original scheme at the image point, followed by the map on stalks. -/
public lemma fieldToStalk_comp_stalkMap_fst {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hy : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x) :
    fieldToStalk f x ≫ (X.presheaf.stalkCongr (.of_eq hy.symm)).hom ≫
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y =
      CommRingCat.ofHom (algebraMap k K : k →+* K) ≫
        fieldToStalk (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y := by
  subst hy
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp]
  calc
    fieldToStalk f ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y) ≫
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y =
        fieldToStalk (pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫ f) y :=
      fieldToStalk_natural f _ y
    _ = fieldToStalk (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k K))) y := by rw [pullback.condition]
    _ = fieldToStalk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y) ≫
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y :=
      (fieldToStalk_natural _ _ _).symm
    _ = (CommRingCat.ofHom (algebraMap k K) ≫ fieldToStalk (𝟙 (Spec (.of K)))
          ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y)) ≫
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y := by
      rw [fieldToStalk_specMap]
    _ = CommRingCat.ofHom (algebraMap k K : k →+* K) ≫
          fieldToStalk (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y := by
      simpa only [Category.assoc, Category.comp_id] using
        congrArg (fun q => CommRingCat.ofHom (algebraMap k K : k →+* K) ≫ q)
          (fieldToStalk_natural (𝟙 (Spec (.of K)))
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y)

/-- The structural map from the ground field to a residue field of a base change along a field
extension is the structural map of the original scheme at the image point, followed by the map
on residue fields. -/
public lemma fieldToResidue_comp_residueFieldMap_fst {k K : Type u} [Field k] [Field K]
    [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hy : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x) :
    fieldToResidue f x ≫ (X.residueFieldCongr hy.symm).hom ≫
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueFieldMap y =
      CommRingCat.ofHom (algebraMap k K : k →+* K) ≫
        fieldToResidue (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y := by
  have hstalk := fieldToStalk_comp_stalkMap_fst f x y hy
  subst hy
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp] at hstalk
  simp only [Scheme.residueFieldCongr_refl, Iso.refl_hom, Category.id_comp, fieldToResidue,
    Category.assoc]
  rw [Scheme.residue_residueFieldMap, ← Category.assoc, hstalk, Category.assoc]

/-- The map `𝒪_{X,x} ⊗_k K ⟶ κ(x) ⊗_k K` induced by the residue map at `x`. -/
public noncomputable def stalkBaseChangeResidueMap {k K : Type u} [Field k] [Field K]
    [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    stalkBaseChangeRing (K := K) f x ⟶ residueBaseChangeRing (K := K) f x :=
  pushout.desc
    (X.residue x ≫ pushout.inl (fieldToResidue f x)
      (CommRingCat.ofHom (algebraMap k K : k →+* K)))
    (pushout.inr (fieldToResidue f x) (CommRingCat.ofHom (algebraMap k K : k →+* K)))
    (by
      change fieldToResidue f x ≫
          pushout.inl (fieldToResidue f x)
            (CommRingCat.ofHom (algebraMap k K : k →+* K)) = _
      exact pushout.condition)

/-- The map `κ(x) ⊗_k K ⟶ κ(y)` determined by a point `y` of the base change lying over `x`. -/
public noncomputable def residueBaseChangeToResidueField {k K : Type u} [Field k] [Field K]
    [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hy : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x) :
    residueBaseChangeRing (K := K) f x ⟶
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).residueField y :=
  pushout.desc
    ((X.residueFieldCongr hy.symm).hom ≫
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueFieldMap y)
    (fieldToResidue (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y)
    (fieldToResidue_comp_residueFieldMap_fst f x y hy)

/-- The map `𝒪_{X,x} ⊗_k K ⟶ 𝒪_{Y,y}` determined by a point `y` of the base change lying
over `x`. -/
public noncomputable def stalkBaseChangeToStalk {k K : Type u} [Field k] [Field K]
    [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hy : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x) :
    stalkBaseChangeRing (K := K) f x ⟶
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        : Scheme.{u}).presheaf.stalk y :=
  pushout.desc
    ((X.presheaf.stalkCongr (.of_eq hy.symm)).hom ≫
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y)
    (fieldToStalk (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y)
    (fieldToStalk_comp_stalkMap_fst f x y hy)

/-- On the stalk factor, the map to the residue-field base change is the residue map. -/
@[simp]
public lemma inl_comp_stalkBaseChangeResidueMap {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    pushout.inl (fieldToStalk f x) (CommRingCat.ofHom (algebraMap k K : k →+* K)) ≫
        stalkBaseChangeResidueMap (K := K) f x =
      X.residue x ≫ pushout.inl (fieldToResidue f x)
        (CommRingCat.ofHom (algebraMap k K : k →+* K)) :=
  pushout.inl_desc _ _ _

/-- On the extension-field factor, the map to the residue-field base change is the identity. -/
@[simp]
public lemma inr_comp_stalkBaseChangeResidueMap {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    pushout.inr (fieldToStalk f x) (CommRingCat.ofHom (algebraMap k K : k →+* K)) ≫
        stalkBaseChangeResidueMap (K := K) f x =
      pushout.inr (fieldToResidue f x) (CommRingCat.ofHom (algebraMap k K : k →+* K)) :=
  pushout.inr_desc _ _ _

/-- On the residue-field factor, the map to `κ(y)` is the map on residue fields. -/
@[simp]
public lemma inl_comp_residueBaseChangeToResidueField {k K : Type u} [Field k] [Field K]
    [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hy : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x) :
    pushout.inl (fieldToResidue f x) (CommRingCat.ofHom (algebraMap k K : k →+* K)) ≫
        residueBaseChangeToResidueField f x y hy =
      (X.residueFieldCongr hy.symm).hom ≫
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueFieldMap y :=
  pushout.inl_desc _ _ _

/-- On the extension-field factor, the map to `κ(y)` is the structural map of the second
projection. -/
@[simp]
public lemma inr_comp_residueBaseChangeToResidueField {k K : Type u} [Field k] [Field K]
    [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hy : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x) :
    pushout.inr (fieldToResidue f x) (CommRingCat.ofHom (algebraMap k K : k →+* K)) ≫
        residueBaseChangeToResidueField f x y hy =
      fieldToResidue (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y :=
  pushout.inr_desc _ _ _

/-- On the stalk factor, the map to `𝒪_{Y,y}` is the map on stalks. -/
@[simp]
public lemma inl_comp_stalkBaseChangeToStalk {k K : Type u} [Field k] [Field K]
    [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hy : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x) :
    pushout.inl (fieldToStalk f x) (CommRingCat.ofHom (algebraMap k K : k →+* K)) ≫
        stalkBaseChangeToStalk f x y hy =
      (X.presheaf.stalkCongr (.of_eq hy.symm)).hom ≫
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y :=
  pushout.inl_desc _ _ _

/-- On the extension-field factor, the map to `𝒪_{Y,y}` is the structural map of the second
projection. -/
@[simp]
public lemma inr_comp_stalkBaseChangeToStalk {k K : Type u} [Field k] [Field K]
    [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hy : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x) :
    pushout.inr (fieldToStalk f x) (CommRingCat.ofHom (algebraMap k K : k →+* K)) ≫
        stalkBaseChangeToStalk f x y hy =
      fieldToStalk (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y :=
  pushout.inr_desc _ _ _

/-- The two presentations of the base change at a point are compatible with the residue map
of the stalk at that point. -/
public lemma stalkBaseChangeResidueMap_comp_residueBaseChangeToResidueField {k K : Type u}
    [Field k] [Field K] [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hy : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x) :
    stalkBaseChangeResidueMap (K := K) f x ≫ residueBaseChangeToResidueField f x y hy =
      stalkBaseChangeToStalk f x y hy ≫
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).residue y := by
  have hres : X.residue x ≫ (X.residueFieldCongr hy.symm).hom ≫
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueFieldMap y =
      ((X.presheaf.stalkCongr (.of_eq hy.symm)).hom ≫
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y) ≫
          (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            : Scheme.{u}).residue y := by
    rw [← Category.assoc, Scheme.residue_residueFieldCongr, Category.assoc,
      Scheme.residue_residueFieldMap, Category.assoc]
  apply pushout.hom_ext
  · exact (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ residueBaseChangeToResidueField f x y hy)
        (inl_comp_stalkBaseChangeResidueMap (K := K) f x)).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg (X.residue x ≫ ·) (inl_comp_residueBaseChangeToResidueField f x y hy)).trans <|
      hres.trans <|
      (congrArg (· ≫ _) (inl_comp_stalkBaseChangeToStalk f x y hy).symm).trans
        (Category.assoc _ _ _)
  · exact (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ residueBaseChangeToResidueField f x y hy)
        (inr_comp_stalkBaseChangeResidueMap (K := K) f x)).trans <|
      (inr_comp_residueBaseChangeToResidueField f x y hy).trans <|
      (congrArg (· ≫ _) (inr_comp_stalkBaseChangeToStalk f x y hy).symm).trans
        (Category.assoc _ _ _)

/-- The local ring at a point of a base change by a field extension is the localization of
`𝒪_{X,x} ⊗_k K` at the prime obtained from the map to the residue field of that point. This is
stated for an arbitrary triple of maps satisfying the characteristic equations. -/
public lemma isLocalization_stalkBaseChangePrime {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hy : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x)
    (θ : stalkBaseChangeRing (K := K) f x ⟶ residueBaseChangeRing (K := K) f x)
    (ψ : residueBaseChangeRing (K := K) f x ⟶
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).residueField y)
    (φ : stalkBaseChangeRing (K := K) f x ⟶
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        : Scheme.{u}).presheaf.stalk y)
    (hφl : pushout.inl (fieldToStalk f x)
        (CommRingCat.ofHom (algebraMap k K : k →+* K)) ≫ φ =
      (X.presheaf.stalkCongr (.of_eq hy.symm)).hom ≫
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y)
    (hφr : pushout.inr (fieldToStalk f x)
        (CommRingCat.ofHom (algebraMap k K : k →+* K)) ≫ φ =
      fieldToStalk (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y)
    (hcomm : θ ≫ ψ = φ ≫
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).residue y) :
    letI : Algebra (stalkBaseChangeRing (K := K) f x)
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          : Scheme.{u}).presheaf.stalk y) := φ.hom.toAlgebra
    let p₀ := RingHom.ker ψ.hom
    let p := stalkBaseChangePrime f x θ p₀
    letI : p₀.IsPrime := RingHom.ker_isPrime _
    letI : p.IsPrime := Ideal.comap_isPrime _ _
    IsLocalization.AtPrime ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      : Scheme.{u}).presheaf.stalk y) p := by
  classical
  subst hy
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp] at hφl
  rcases stalkBaseChange_isLocalization k K X f y with ⟨φ₀, hφ₀l, hφ₀r, hAt⟩
  obtain rfl : φ = φ₀ := pushout.hom_ext (hφl.trans hφ₀l.symm) (hφr.trans hφ₀r.symm)
  let : Algebra (stalkBaseChangeRing (K := K) f
      ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y))
      ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        : Scheme.{u}).presheaf.stalk y) := φ.hom.toAlgebra
  have : (RingHom.ker ψ.hom).IsPrime := RingHom.ker_isPrime _
  have : (stalkBaseChangePrime f _ θ (RingHom.ker ψ.hom)).IsPrime := Ideal.comap_isPrime _ _
  have : (Ideal.comap φ.hom (IsLocalRing.maximalIdeal
      ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        : Scheme.{u}).presheaf.stalk y))).IsPrime := Ideal.comap_isPrime _ _
  have hcomp : ψ.hom.comp θ.hom = (IsLocalRing.residue _).comp φ.hom :=
    congrArg CommRingCat.Hom.hom hcomm
  have hprime : stalkBaseChangePrime f _ θ (RingHom.ker ψ.hom) =
      Ideal.comap φ.hom (IsLocalRing.maximalIdeal _) := by
    ext z
    change (ψ.hom.comp θ.hom) z = 0 ↔ φ.hom z ∈ IsLocalRing.maximalIdeal _
    rw [hcomp]
    exact IsLocalRing.residue_eq_zero_iff (φ.hom z)
  have hcompl : (stalkBaseChangePrime f _ θ (RingHom.ker ψ.hom)).primeCompl =
      (Ideal.comap φ.hom (IsLocalRing.maximalIdeal _)).primeCompl := by
    ext z
    simp only [Ideal.mem_primeCompl_iff]
    rw [hprime]
  change IsLocalization (stalkBaseChangePrime f _ θ (RingHom.ker ψ.hom)).primeCompl _
  rw [hcompl]
  exact hAt

/-- **Stacks Project, Tag 0C4Y (localization description).** The local ring at a point of a base
change by a field extension is the localization of `𝒪_{X,x} ⊗_k K` at the prime obtained from
the map to the residue field of that point. -/
@[stacks 0C4Y "localization_description"]
public theorem stalkOfBaseChange_isLocalization
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hy : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x) :
    let Y := (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})
    let A := stalkBaseChangeRing (K := K) f x
    let B := residueBaseChangeRing (K := K) f x
    ∃ θ : A ⟶ B, ∃ ψ : B ⟶ Y.residueField y, ∃ φ : A ⟶ Y.presheaf.stalk y,
      pushout.inl (fieldToStalk f x)
          (CommRingCat.ofHom (algebraMap k K : k →+* K)) ≫ θ =
        X.residue x ≫ pushout.inl (fieldToResidue f x)
          (CommRingCat.ofHom (algebraMap k K : k →+* K)) ∧
      pushout.inr (fieldToStalk f x)
          (CommRingCat.ofHom (algebraMap k K : k →+* K)) ≫ θ =
        pushout.inr (fieldToResidue f x)
          (CommRingCat.ofHom (algebraMap k K : k →+* K)) ∧
      pushout.inl (fieldToResidue f x)
          (CommRingCat.ofHom (algebraMap k K : k →+* K)) ≫ ψ =
        (X.residueFieldCongr hy.symm).hom ≫
          (pullback.fst f (Spec.map
            (CommRingCat.ofHom (algebraMap k K)))).residueFieldMap y ∧
      pushout.inr (fieldToResidue f x)
          (CommRingCat.ofHom (algebraMap k K : k →+* K)) ≫ ψ =
        fieldToResidue
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y ∧
      pushout.inl (fieldToStalk f x)
          (CommRingCat.ofHom (algebraMap k K : k →+* K)) ≫ φ =
        (X.presheaf.stalkCongr (.of_eq hy.symm)).hom ≫
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y ∧
      pushout.inr (fieldToStalk f x)
          (CommRingCat.ofHom (algebraMap k K : k →+* K)) ≫ φ =
        fieldToStalk
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y ∧
      θ ≫ ψ = φ ≫ Y.residue y ∧
      letI : Algebra A (Y.presheaf.stalk y) := φ.hom.toAlgebra
      let p₀ := RingHom.ker ψ.hom
      let p := stalkBaseChangePrime f x θ p₀
      letI : p₀.IsPrime := RingHom.ker_isPrime _
      letI : p.IsPrime := Ideal.comap_isPrime _ _
      IsLocalization.AtPrime (Y.presheaf.stalk y) p :=
  ⟨stalkBaseChangeResidueMap (K := K) f x, residueBaseChangeToResidueField f x y hy,
    stalkBaseChangeToStalk f x y hy, inl_comp_stalkBaseChangeResidueMap (K := K) f x,
    inr_comp_stalkBaseChangeResidueMap (K := K) f x,
    inl_comp_residueBaseChangeToResidueField f x y hy,
    inr_comp_residueBaseChangeToResidueField f x y hy,
    inl_comp_stalkBaseChangeToStalk f x y hy, inr_comp_stalkBaseChangeToStalk f x y hy,
    stalkBaseChangeResidueMap_comp_residueBaseChangeToResidueField f x y hy,
    isLocalization_stalkBaseChangePrime f x y hy _ _ _
      (inl_comp_stalkBaseChangeToStalk f x y hy) (inr_comp_stalkBaseChangeToStalk f x y hy)
      (stalkBaseChangeResidueMap_comp_residueBaseChangeToResidueField f x y hy)⟩

end AlgebraicGeometry
