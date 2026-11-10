module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.SetTheory.Cardinal.Order
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Basic
public import StacksFrontier.RingTheory.Jacobson.Nullstellensatz

/-!
# Residue fields of closed points after a large field extension

Let `X` be a scheme over a field `k`.  After base change to an extension field `K` of
sufficiently large cardinality, the residue field of every closed point of `X_K` is algebraic
over `K`.  The cardinal threshold is the size of `X` in the sense of Stacks Tag 000I.

## Main definitions

* `residueAlgebraMap g y`: the canonical `K`-algebra structure map on the residue field at a
  point `y` of a scheme over `Spec K`.
* `IsAlgebraicResidue g y`: the predicate that this makes the residue field algebraic over `K`.

## Main results

* `exists_cardinal_isAlgebraic_residueField_of_mem_closedPoints_baseChange` is Tag 0479: a
  cardinal bound beyond which every closed point of the base change has algebraic residue
  field.
* `isAlgebraicResidue_pullback_fst` is the affine case, deduced from the ring-theoretic
  Tag 046V (`Algebra.isAlgebraic_tensorProduct_quotient_of_card_lt`) through `pullbackSpecIso`.
* `isAlgebraicResidue_pullback_opens` is the case of an affine open of `X`, and
  `isoSpec_hom_comp_specMap` records that `V ≅ Spec Γ(X, V)` is a morphism over `Spec k`.

## Implementation notes

The base change is the categorical pullback along `Spec K ⟶ Spec k`, and the `K`-algebra
structure on a residue field is the one induced by the second projection together with the
standard identification of the residue field of the unique point of `Spec K` with `K`.  Since
`residueAlgebraMap` is functorial (`residueAlgebraMap_comp`) and an open immersion induces an
isomorphism of residue fields, algebraicity may be checked on any member of an open cover;
this is what reduces the general statement to the affine one.

## References

* [Stacks Project, Tag 0479](https://stacks.math.columbia.edu/tag/0479)
* [Stacks Project, Tag 046V](https://stacks.math.columbia.edu/tag/046V)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry CommRingCat

universe u

namespace Stacks.AlgebraicGeometry.ClosedPointResidue

/-- The canonical structure map making the residue field of a point of a `K`-scheme a
`K`-algebra: it is the composition of the identification of `K` with the residue field of the
unique point of `Spec K` with the induced map of residue fields. -/
noncomputable def residueAlgebraMap {K : Type u} [Field K] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of K)) (y : Y) : CommRingCat.of K ⟶ Y.residueField y :=
  letI : (g y).asIdeal.IsPrime := (g y).isPrime
  CommRingCat.ofHom (algebraMap K (g y).asIdeal.ResidueField) ≫
    (Scheme.Spec.residueFieldIso (.of K) (g y)).inv ≫ g.residueFieldMap y

/-- The residue field at `y` is algebraic over `K` for the canonical `K`-algebra structure
of `residueAlgebraMap`. -/
def IsAlgebraicResidue {K : Type u} [Field K] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of K)) (y : Y) : Prop :=
  letI := (residueAlgebraMap g y).hom.toAlgebra
  Algebra.IsAlgebraic K (Y.residueField y)

/-- For a morphism `e : Z ⟶ Y` of schemes and `g : Y ⟶ Spec K`, the `K`-algebra structure map
on the residue field of `Z` at `z` is that of `Y` at `e z` followed by the induced map of residue
fields. -/
lemma residueAlgebraMap_comp {K : Type u} [Field K] {Y Z : Scheme.{u}}
    (g : Y ⟶ Spec (.of K)) (e : Z ⟶ Y) (z : Z) :
    residueAlgebraMap (e ≫ g) z =
      residueAlgebraMap g (e z) ≫ e.residueFieldMap z := by
  let _ : (g (e z)).asIdeal.IsPrime := (g (e z)).isPrime
  change CommRingCat.ofHom (algebraMap K (g (e z)).asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso (.of K) (g (e z))).inv ≫
        (e ≫ g).residueFieldMap z =
    CommRingCat.ofHom (algebraMap K (g (e z)).asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso (.of K) (g (e z))).inv ≫
        g.residueFieldMap (e z) ≫ e.residueFieldMap z
  rw [Scheme.residueFieldMap_comp]

/-- Algebraicity over `K` transfers along an isomorphism of rings under `K`. -/
private lemma isAlgebraic_iff_of_comp_eq {K : Type u} [Field K] {A B : CommRingCat.{u}}
    [Algebra K A] (g : CommRingCat.of K ⟶ B) (e : A ≅ B)
    (h : CommRingCat.ofHom (algebraMap K A) ≫ e.hom = g) :
    letI := g.hom.toAlgebra
    Algebra.IsAlgebraic K A ↔ Algebra.IsAlgebraic K B := by
  let _ := g.hom.toAlgebra
  have hcomm : ∀ x : K, e.commRingCatIsoToRingEquiv (algebraMap K A x) = algebraMap K B x :=
    fun x => congrArg (fun ψ : CommRingCat.of K ⟶ B => ψ.hom x) h
  exact (AlgEquiv.ofRingEquiv hcomm).isAlgebraic_iff

/-- The image of a closed point under an isomorphism of schemes is closed. -/
private lemma isClosed_singleton_hom_apply {X Y : Scheme.{u}} (e : X ≅ Y) {x : X}
    (hx : IsClosed ({x} : Set X)) : IsClosed ({e.hom x} : Set Y) := by
  simpa using (e.hom.homeomorph.isClosedEmbedding.isClosed_iff_image_isClosed
    (s := ({x} : Set _))).mp hx

/-- Algebraicity of residue fields transfers along a morphism of `K`-schemes which induces an
isomorphism of residue fields at the point in question. -/
lemma isAlgebraicResidue_comp_iff {K : Type u} [Field K] {Y Z : Scheme.{u}}
    (g : Y ⟶ Spec (.of K)) (e : Z ⟶ Y) (z : Z) [IsIso (e.residueFieldMap z)] :
    IsAlgebraicResidue (e ≫ g) z ↔ IsAlgebraicResidue g (e z) := by
  let _ := (residueAlgebraMap g (e z)).hom.toAlgebra
  exact (isAlgebraic_iff_of_comp_eq _ (asIso (e.residueFieldMap z))
    (residueAlgebraMap_comp g e z).symm).symm

/-- Algebraicity of residue fields is invariant under an isomorphism of `K`-schemes. -/
lemma isAlgebraicResidue_iff_of_comp_eq {K : Type u} [Field K] {Y Z : Scheme.{u}}
    (gY : Y ⟶ Spec (.of K)) (gZ : Z ⟶ Spec (.of K)) (e : Z ⟶ Y)
    (he : e ≫ gY = gZ) (z : Z) [IsIso (e.residueFieldMap z)] :
    IsAlgebraicResidue gZ z ↔ IsAlgebraicResidue gY (e z) := by
  subst he
  exact isAlgebraicResidue_comp_iff gY e z

/-- For a `K`-algebra `T`, the canonical `K`-algebra structure on the scheme-theoretic residue
field of `Spec T` at `q` agrees, through `Scheme.Spec.residueFieldIso`, with the `K`-algebra
structure of the residue field of the prime `q`. -/
lemma residueAlgebraMap_specMap (K T : Type u) [Field K] [CommRing T] [Algebra K T]
    (q : Spec (CommRingCat.of T)) [q.asIdeal.IsPrime] :
    residueAlgebraMap (Spec.map (CommRingCat.ofHom (algebraMap K T))) q =
      CommRingCat.ofHom (algebraMap K q.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (CommRingCat.of T) q).inv := by
  let φ : CommRingCat.of K ⟶ CommRingCat.of T := CommRingCat.ofHom (algebraMap K T)
  let b : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of K) := Spec.map φ
  let p : Spec (CommRingCat.of K) := b q
  let _ : p.asIdeal.IsPrime := p.isPrime
  calc residueAlgebraMap b q
      = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
          (Spec (CommRingCat.of K)).presheaf.germ ⊤ p (by simp) ≫
          (Spec (CommRingCat.of K)).residue p ≫ b.residueFieldMap q :=
        congrArg (fun z => z ≫ b.residueFieldMap q)
          (Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of K) p)
    _ = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
          (Spec (CommRingCat.of K)).presheaf.germ ⊤ p (by simp) ≫
          b.stalkMap q ≫ (Spec (CommRingCat.of T)).residue q := by
        rw [Scheme.residue_residueFieldMap]
    _ = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ b.appTop ≫
          (Spec (CommRingCat.of T)).presheaf.germ ⊤ q (by simp) ≫
          (Spec (CommRingCat.of T)).residue q := by
        rw [Scheme.Hom.germ_stalkMap_assoc]
        simp
    _ = φ ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).inv ≫
          (Spec (CommRingCat.of T)).presheaf.germ ⊤ q (by simp) ≫
          (Spec (CommRingCat.of T)).residue q :=
        congrArg (fun z => z ≫ (Spec (CommRingCat.of T)).presheaf.germ ⊤ q (by simp) ≫
            (Spec (CommRingCat.of T)).residue q)
          (Scheme.ΓSpecIso_inv_naturality φ).symm
    _ = φ ≫ (CommRingCat.ofHom (algebraMap T q.asIdeal.ResidueField) ≫
          (Scheme.Spec.residueFieldIso (CommRingCat.of T) q).inv) :=
        congrArg (fun z => φ ≫ z)
          (Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of T) q).symm
    _ = CommRingCat.ofHom (algebraMap K q.asIdeal.ResidueField) ≫
          (Scheme.Spec.residueFieldIso (CommRingCat.of T) q).inv := by
        rw [IsScalarTower.algebraMap_eq K T q.asIdeal.ResidueField, CommRingCat.ofHom_comp]
        exact (Category.assoc φ _ _).symm

/-- For a `K`-algebra `T` with `K` a field, algebraicity of the residue field of a prime of `T`
over `K` gives algebraicity of the scheme-theoretic residue field of `Spec T` at that point. -/
lemma isAlgebraicResidue_specMap (K T : Type u) [Field K] [CommRing T] [Algebra K T]
    (q : Spec (CommRingCat.of T)) [q.asIdeal.IsPrime]
    (h : Algebra.IsAlgebraic K q.asIdeal.ResidueField) :
    IsAlgebraicResidue (Spec.map (CommRingCat.ofHom (algebraMap K T))) q := by
  let b : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K T))
  let ρ := Scheme.Spec.residueFieldIso (CommRingCat.of T) q
  exact (isAlgebraic_iff_of_comp_eq _ ρ.symm (residueAlgebraMap_specMap K T q).symm).mp h

/-- **Stacks 046V, scheme form.** If `#R < #K`, every closed point of
`Spec K ×_{Spec k} Spec R` has residue field algebraic over `K`. -/
lemma isAlgebraicResidue_pullback_fst (k K R : Type u) [Field k] [Field K] [Algebra k K]
    [CommRing R] [Algebra k R] (hcard : Cardinal.mk R < Cardinal.mk K)
    (x : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) : Scheme.{u}))
    (hx : IsClosed ({x} : Set _)) :
    IsAlgebraicResidue
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (Spec.map (CommRingCat.ofHom (algebraMap k R)))) x := by
  let T : Type u := TensorProduct k K R
  let ε : pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) ≅ Spec (CommRingCat.of T) :=
    pullbackSpecIso k K R
  let q : Spec (CommRingCat.of T) := ε.hom x
  have hqmax : q.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp (isClosed_singleton_hom_apply ε hx)
  have _ : q.asIdeal.IsPrime := q.isPrime
  have hres : Algebra.IsAlgebraic K (T ⧸ q.asIdeal) :=
    Algebra.isAlgebraic_tensorProduct_quotient_of_card_lt k R K (Cardinal.lift_lt.2 hcard)
      q.asIdeal
  have halg : Algebra.IsAlgebraic K q.asIdeal.ResidueField :=
    Algebra.isAlgebraic_iff_isIntegral.mpr <|
      Algebra.IsIntegral.of_surjective
        (IsScalarTower.toAlgHom K (T ⧸ q.asIdeal) q.asIdeal.ResidueField)
        (Ideal.bijective_algebraMap_quotient_residueField q.asIdeal).2
  exact (isAlgebraicResidue_iff_of_comp_eq _ _ ε.hom
    (pullbackSpecIso_hom_fst' k K R) x).mpr (isAlgebraicResidue_specMap K T q halg)

/-- The canonical isomorphism `V ≅ Spec Γ(X, V)` of an affine open of a `k`-scheme `X` is a
morphism of schemes over `Spec k`. -/
lemma isoSpec_hom_comp_specMap {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) {V : X.Opens} (hV : IsAffineOpen V)
    (hle : V ≤ f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of k)).Opens)) :
    hV.isoSpec.hom ≫
        Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V hle) =
      V.ι ≫ f := by
  have hcomp : Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V hle) =
      Spec.map (f.appLE ⊤ V hle) ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv :=
    Scheme.Spec.map_comp _ _
  have hnat := Scheme.Opens.toSpecΓ_SpecMap_appLE (f := f) (U := ⊤) (V := V) hle
  have htop : (⊤ : (Spec (CommRingCat.of k)).Opens).toSpecΓ ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv =
      (⊤ : (Spec (CommRingCat.of k)).Opens).ι := by
    rw [← Scheme.isoSpec_Spec_inv, Scheme.Opens.toSpecΓ_top, Category.assoc,
      Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  rw [hV.isoSpec_hom, hcomp]
  calc V.toSpecΓ ≫ Spec.map (f.appLE ⊤ V hle) ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv
      = Scheme.Hom.resLE f ⊤ V hle ≫ (⊤ : (Spec (CommRingCat.of k)).Opens).toSpecΓ ≫
          Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv :=
        congrArg (fun q => q ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv) hnat
    _ = Scheme.Hom.resLE f ⊤ V hle ≫ (⊤ : (Spec (CommRingCat.of k)).Opens).ι :=
        congrArg (fun q => Scheme.Hom.resLE f ⊤ V hle ≫ q) htop
    _ = V.ι ≫ f := by simp

/-- Over a sufficiently large field extension, every closed point of the base change of an
affine open of a `k`-scheme has residue field algebraic over `K`. -/
lemma isAlgebraicResidue_pullback_opens {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) {V : X.Opens} (hV : IsAffineOpen V)
    (hcard : Cardinal.mk Γ(X, V) < Cardinal.mk K)
    (y : (pullback (V.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hy : IsClosed ({y} : Set _)) :
    IsAlgebraicResidue
      (pullback.snd (V.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y := by
  let R : Type u := Γ(X, V)
  have hle : V ≤ f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of k)).Opens) := by simp
  let _ : Algebra k R :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V hle).hom.toAlgebra
  let σ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let fR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k R))
  have hα : CommRingCat.ofHom (algebraMap k R) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V hle := by
    ext a
    rfl
  have hfV : hV.isoSpec.hom ≫ fR = V.ι ≫ f := by
    rw [show fR = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V hle) from
      congrArg Spec.map hα]
    exact isoSpec_hom_comp_specMap f hV hle
  have hY : IsPullback (pullback.fst (V.ι ≫ f) σ ≫ hV.isoSpec.hom)
      (pullback.snd (V.ι ≫ f) σ) fR σ :=
    (IsPullback.of_hasPullback (V.ι ≫ f) σ).of_iso (Iso.refl _) hV.isoSpec (Iso.refl _)
      (Iso.refl _) rfl rfl hfV.symm rfl
  let e₀ := hY.isoIsPullback _ _ (IsPullback.of_hasPullback fR σ)
  let e₁ := e₀ ≪≫ pullbackSymmetry fR σ
  have hsnd : e₁.hom ≫ pullback.fst σ fR = pullback.snd (V.ι ≫ f) σ := by
    calc e₁.hom ≫ pullback.fst σ fR
        = e₀.hom ≫ pullback.snd fR σ := by
          dsimp only [e₁, Iso.trans_hom]
          rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
      _ = pullback.snd (V.ι ≫ f) σ :=
          IsPullback.isoIsPullback_hom_snd _ _ hY (IsPullback.of_hasPullback fR σ)
  exact (isAlgebraicResidue_iff_of_comp_eq _ _ e₁.hom hsnd y).mpr
    (isAlgebraicResidue_pullback_fst k K R hcard _ (isClosed_singleton_hom_apply e₁ hy))

/-- **Closed points of a base change to a field larger than the scheme have algebraic residue
fields.** Let `X` be a scheme over a field `k` and `K/k` an extension with `#K` above the size of
`X`. Then the residue field of every closed point of `X_K` is algebraic over `K`: a closed point
lies in the base change of an affine open of `X`, whose ring of sections is smaller than `K`. -/
theorem isAlgebraicResidue_of_mem_closedPoints_of_size_lt
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    (K : Type u) [Field K] [Algebra k K] (hK : X.size < Cardinal.mk K)
    (x : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hx : x ∈ closedPoints
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) :
    IsAlgebraicResidue (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) x := by
  let σ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let 𝒰 : X.OpenCover := X.openCoverOfIsOpenCover (fun V : X.affineOpens => (V : X.Opens))
    (iSup_affineOpens_eq_top X)
  let 𝒱 : (pullback f σ).OpenCover := Scheme.Pullback.openCoverOfLeft 𝒰 f σ
  obtain ⟨V, y₀, hy₀⟩ := 𝒱.exists_eq x
  let W : X.affineOpens := V
  let j : (pullback ((W : X.Opens).ι ≫ f) σ : Scheme.{u}) ⟶ pullback f σ :=
    pullback.map ((W : X.Opens).ι ≫ f) σ f σ (W : X.Opens).ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  let y : (pullback ((W : X.Opens).ι ≫ f) σ : Scheme.{u}) := y₀
  have hjy : j y = x := hy₀
  have _ : IsOpenImmersion j := by
    dsimp only [j]
    infer_instance
  have hj : j ≫ pullback.snd f σ = pullback.snd ((W : X.Opens).ι ≫ f) σ := by
    dsimp only [j]
    rw [pullback.lift_snd, Category.comp_id]
  have hyclosed : IsClosed ({y} : Set (pullback ((W : X.Opens).ι ≫ f) σ : Scheme.{u})) :=
    preimage_closedPoints_subset (f := j.base) j.isOpenEmbedding.injective
      j.base.hom.continuous (by simpa [hjy] using hx)
  have hcard : Cardinal.mk Γ(X, (W : X.Opens)) < Cardinal.mk K :=
    (X.mk_sections_le_size W).trans_lt hK
  have h := (isAlgebraicResidue_iff_of_comp_eq _ _ j hj y).mp
    (isAlgebraicResidue_pullback_opens f W.2 hcard y hyclosed)
  rwa [hjy] at h

/-- **Stacks Project, Tag 0479.** For every scheme over a field, after extending the field to one
of sufficiently large cardinality, the residue field of every closed point of the base change is
algebraic over the extended field. -/
theorem exists_isAlgebraicResidue_of_mem_closedPoints
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) :
    ∃ κ : Cardinal.{u}, ∀ (K : Type u) [Field K] [Algebra k K], κ ≤ Cardinal.mk K →
      ∀ x : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}),
        x ∈ closedPoints
            (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) →
          IsAlgebraicResidue
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) x :=
  ⟨Order.succ X.size, fun K _ _ hK =>
    isAlgebraicResidue_of_mem_closedPoints_of_size_lt k X f K
      (lt_of_lt_of_le (Order.lt_succ X.size) hK)⟩

/-- For every scheme over a field, after extending the field to one of sufficiently large
cardinality, the residue field of every closed point of the base change is algebraic over the
extended field. -/
@[stacks 0479 "closed_point_residue_algebraic"]
theorem exists_cardinal_isAlgebraic_residueField_of_mem_closedPoints_baseChange
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    ∃ κ : Cardinal.{u}, ∀ (K : Type u) [Field K] [Algebra k K], κ ≤ Cardinal.mk K →
      ∀ x : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}),
        x ∈ closedPoints
            (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) →
          let p := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          letI : (p x).asIdeal.IsPrime := (p x).isPrime
          letI := ((CommRingCat.ofHom (algebraMap K (p x).asIdeal.ResidueField)) ≫
            (Scheme.Spec.residueFieldIso (.of K) (p x)).inv ≫
            p.residueFieldMap x).hom.toAlgebra
          Algebra.IsAlgebraic K
            ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
              Scheme.{u}).residueField x) :=
  exists_isAlgebraicResidue_of_mem_closedPoints k X f

end Stacks.AlgebraicGeometry.ClosedPointResidue

end
