module

public import StacksFrontier.Deformation.Examples.Geometric.SmoothingLevelFitting
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingTower
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingTowerFitting
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingReduced
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingEssFiniteType

/-!
# The formal smoothing of a curve

Let `X` be a separated scheme of finite type over a field `k`, equidimensional of dimension one, a
local complete intersection over `k`, and smooth over `k` away from finitely many points. Then
there is a tower of flat schemes `X_n` over the thickenings `Spec (k⟦t⟧ / (t)^{n+1})` with
cartesian transition squares, `X_0 ≅ X`, and such that for some `n` the image of `t^n` lies in the
first Fitting ideal of `Ω_{X_n / Spec (k⟦t⟧/(t)^{n+1})}`. This is the first half of the proof of
[Stacks, Tag 0E7Y]: the local smoothings of [Stacks, Tag 0E7X] at the singular points are lifted to
a formal deformation of `X` by [Stacks, Tag 0DZP] and [Stacks, Tag 06HN], and the Fitting ideal of
the differentials is computed in the local rings.

## Main results

* `Deformation.Examples.Smoothing.mem_fittingIdeal_stalk_of_iso_levelHom`: the Fitting ideal at a
  point where the stalk of the deformation is identified with a level of a local smoothing.
* `Deformation.Examples.Smoothing.exists_formalSmoothingTower`: the tower.

## References

* [Stacks Project, Tag 0E7Y](https://stacks.math.columbia.edu/tag/0E7Y)
* [Stacks Project, Tag 0E7X](https://stacks.math.columbia.edu/tag/0E7X)
* [Stacks Project, Tag 0DZP](https://stacks.math.columbia.edu/tag/0DZP)
* [Stacks Project, Tag 06HN](https://stacks.math.columbia.edu/tag/06HN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples.Smoothing

variable {k : Type u} [Field k]

/-- An isomorphism of formal objects has an isomorphism of complete local algebras as its base. -/
def FormalObject.baseIso {F : Type*} [Category F] {p : F ⥤ ArtinianLocalAlgCat.{u, u, u} k k}
    {ξ η : FormalObject p} (m : ξ ≅ η) : ξ.base ≅ η.base where
  hom := m.hom.base
  inv := m.inv.base
  hom_inv_id := congrArg FormalObject.Hom.base m.hom_inv_id
  inv_hom_id := congrArg FormalObject.Hom.base m.inv_hom_id

/-- The level maps of an isomorphism of formal objects compose to the identity. -/
theorem FormalObject.app_hom_inv {F : Type*} [Category F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, u, u} k k} {ξ η : FormalObject p} (m : ξ ≅ η) (n : ℕ) :
    m.hom.app n ≫ m.inv.app n = 𝟙 _ :=
  congrArg (fun f => FormalObject.Hom.app f n) m.hom_inv_id

/-- The level maps of the inverse of an isomorphism of formal objects, followed by those of the
isomorphism, compose to the identity. -/
theorem FormalObject.app_inv_hom {F : Type*} [Category F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, u, u} k k} {ξ η : FormalObject p} (m : ξ ≅ η) (n : ℕ) :
    m.inv.app n ≫ m.hom.app n = 𝟙 _ :=
  congrArg (fun f => FormalObject.Hom.app f n) m.inv_hom_id

/-- The base map of an inverse isomorphism of formal objects, followed by the level map of the
isomorphism, is the identity of the truncation, up to the identifications of the levels. -/
theorem FormalObject.map_inv_base_comp_app_hom {F : Type*} [Category F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, u, u} k k} {ξ η : FormalObject p} (m : ξ ≅ η) (n : ℕ) :
    (AdicTruncation.functor n).map m.inv.base ≫ eqToHom (ξ.level_eq n).symm ≫
        p.map (m.hom.app n) = eqToHom (η.level_eq n).symm := by
  have hlift := m.hom.app_lift n
  rw [IsHomLift.fac' p ((AdicTruncation.functor n).map m.hom.base) (m.hom.app n)]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, ← Functor.map_comp_assoc]
  rw [show m.inv.base ≫ m.hom.base = 𝟙 _ from congrArg FormalObject.Hom.base m.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The Fitting ideal at a smooth point.** At the image in `ξ_n` of a point at which `X` is
smooth over `k`, the first Fitting ideal of the differentials of the stalk of `ξ_n` over the `n`-th
thickening is the unit ideal. -/
theorem mem_fittingIdeal_stalk_of_mem_smoothLocus (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] (hdim : topologicalKrullDim X.left ≤ 1)
    (ξ : FormalObject (schemeDeformationCategoryProjection (Λ := k) (k := k) X))
    (σ : powerSeriesObject k ≅ ξ.base) (n : ℕ) {x : X.left} (hx : x ∈ X.hom.smoothLocus)
    (a : PowerSeries k ⧸ discIdeal k ^ (n + 1)) :
    haveI := locallyOfFiniteType_towerHom X ξ σ n
    letI := stalkAlgebra (PowerSeries k ⧸ discIdeal k ^ (n + 1)) (towerHom X ξ σ n)
      ((ξ.level n).specialMap x)
    letI := moduleFinite_kaehler_stalkAlgebra (PowerSeries k ⧸ discIdeal k ^ (n + 1))
      (towerHom X ξ σ n) ((ξ.level n).specialMap x)
    algebraMap (PowerSeries k ⧸ discIdeal k ^ (n + 1))
        ((ξ.level n).scheme.presheaf.stalk ((ξ.level n).specialMap x)) a ∈
      fittingIdeal (R := (ξ.level n).scheme.presheaf.stalk ((ξ.level n).specialMap x))
        (M := Ω[(ξ.level n).scheme.presheaf.stalk ((ξ.level n).specialMap x)⁄
          (PowerSeries k ⧸ discIdeal k ^ (n + 1))]) ((1 : ℕ) : ℤ) := by
  have := locallyOfFiniteType_towerHom X ξ σ n
  have : LocallyOfFiniteType (ξ.level n).toBase :=
    (Stacks.Thickenings.locallyOfFiniteType_iff_of_isFiniteOrderThickening
      (ξ.level n).specialMap (residueSpecMap (ξ.level n).base) X.hom (ξ.level n).toBase
      (isFiniteOrderThickening_residueSpecMap _) (ξ.level n).specialCartesian).mp inferInstance
  set y := (ξ.level n).specialMap x
  set A' := PowerSeries k ⧸ discIdeal k ^ (n + 1)
  set O := (ξ.level n).scheme.presheaf.stalk y
  let iA : Algebra A' O := stalkAlgebra A' (towerHom X ξ σ n) y
  let := moduleFinite_kaehler_stalkAlgebra A' (towerHom X ξ σ n) y
  let iL : Algebra (ξ.level n).base O := stalkAlgebra (ξ.level n).base (ξ.level n).toBase y
  let := moduleFinite_kaehler_stalkAlgebra (ξ.level n).base (ξ.level n).toBase y
  have htop := fittingIdeal_stalk_eq_top_of_mem_smoothLocus X hdim (ξ.level n) x hx
  have hcompat : ∀ b : A', algebraMap (ξ.level n).base O
      (RingEquiv.ofBijective _ (bijective_towerRingHom X ξ σ n) b) =
      (RingEquiv.refl O) (algebraMap A' O b) := by
    intro b
    have hG1 := algebraMap_stalkAlgebra_comp_specMap (ξ.level n).toBase (towerRingHom X ξ σ n) y b
    have hL := congrArg (fun (i : Algebra (ξ.level n).base O) => @algebraMap _ _ _ _ i
      (towerRingHom X ξ σ n b))
        (stalkAlgebra_eq_stalkMap_comp (ξ.level n).base (ξ.level n).toBase y)
    exact hL.trans hG1.symm
  have hF2 := fittingIdeal_kaehler_of_ringEquiv (R := A') (C := O) (R' := (ξ.level n).base)
    (C' := O) (RingEquiv.refl O) (RingEquiv.ofBijective _ (bijective_towerRingHom X ξ σ n))
    hcompat 1
  have : fittingIdeal (R := O) (M := Ω[O⁄A']) ((1 : ℕ) : ℤ) = ⊤ := by
    have h := hF2.symm.trans htop
    have hid : ∀ I : Ideal O, Ideal.map (RingEquiv.refl O) I = I := fun I => by
      ext z
      rw [show Ideal.map (RingEquiv.refl O) I = Ideal.map ((RingEquiv.refl O : O ≃+* O) : O →+* O) I
        from rfl, Ideal.map_comap_of_equiv, Ideal.mem_comap]
      rfl
    rwa [hid] at h
  rw [this]
  trivial

section Lift

variable (X : Over (Spec (.of k))) {ι : Type u} (p : ι → X.left)
  (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra (PowerSeries k) (B i)]
  [∀ i, Module.Flat (PowerSeries k) (B i)] [∀ i, Algebra k (B i)]
  [∀ i, IsScalarTower k (PowerSeries k) (B i)]

variable {X p B} in
/-- The base of the formal object `ξ` is `k⟦t⟧`, through the base of the comparison isomorphism. -/
def liftBaseIso
    (ξ : FormalObject (schemeDeformationCategoryProjection (Λ := k) (k := k) X))
    (e : letI : ∀ i, Algebra k (X.left.presheaf.stalk (p i)) := fun i => stalkAlgebraOver X (p i)
      ∀ i, (B i ⧸ Ideal.span {algebraMap (PowerSeries k) (B i) PowerSeries.X}) ≃ₐ[k]
        X.left.presheaf.stalk (p i))
    (m : letI : ∀ i, Algebra k (X.left.presheaf.stalk (p i)) := fun i => stalkAlgebraOver X (p i)
      (completionMap (localRingFunctors (Λ := k) X p)).obj ξ ≅
        piFormalObject k B (fun i => X.left.presheaf.stalk (p i)) e) :
    powerSeriesObject k ≅ ξ.base :=
  (FormalObject.baseIso m).symm

variable {X p B} in
/-- **The level maps of the comparison isomorphism invert the identification of the bases.** -/
theorem towerBaseHom_comp_hbase
    (ξ : FormalObject (schemeDeformationCategoryProjection (Λ := k) (k := k) X))
    (e : letI : ∀ i, Algebra k (X.left.presheaf.stalk (p i)) := fun i => stalkAlgebraOver X (p i)
      ∀ i, (B i ⧸ Ideal.span {algebraMap (PowerSeries k) (B i) PowerSeries.X}) ≃ₐ[k]
        X.left.presheaf.stalk (p i))
    (m : letI : ∀ i, Algebra k (X.left.presheaf.stalk (p i)) := fun i => stalkAlgebraOver X (p i)
      (completionMap (localRingFunctors (Λ := k) X p)).obj ξ ≅
        piFormalObject k B (fun i => X.left.presheaf.stalk (p i)) e) (n : ℕ) :
    towerBaseHom X ξ (liftBaseIso ξ e m) n ≫ (m.hom.app n).hbase = 𝟙 _ :=
  FormalObject.map_inv_base_comp_app_hom m n

variable {X p B} in
/-- **The Fitting ideal at a singular point.** At the image in `ξ_n` of the point `p i`, the stalk
of `ξ_n` is identified, through the comparison isomorphism `m`, with the level `B_i / 𝔪^{n+1} B_i`;
so if `t^N` lies in the `d`-th Fitting ideal of `Ω_{B_i/k⟦t⟧}` with `d ≤ 1` and `N ≤ n`, the image
of `t^n` lies in the first Fitting ideal of the differentials of the stalk over the `n`-th
thickening. -/
theorem mem_fittingIdeal_stalk_of_iso_levelHom [LocallyOfFiniteType X.hom]
    (ξ : FormalObject (schemeDeformationCategoryProjection (Λ := k) (k := k) X))
    (e : letI : ∀ i, Algebra k (X.left.presheaf.stalk (p i)) := fun i => stalkAlgebraOver X (p i)
      ∀ i, (B i ⧸ Ideal.span {algebraMap (PowerSeries k) (B i) PowerSeries.X}) ≃ₐ[k]
        X.left.presheaf.stalk (p i))
    (m : letI : ∀ i, Algebra k (X.left.presheaf.stalk (p i)) := fun i => stalkAlgebraOver X (p i)
      (completionMap (localRingFunctors (Λ := k) X p)).obj ξ ≅
        piFormalObject k B (fun i => X.left.presheaf.stalk (p i)) e)
    (i : ι) [Module.Finite (B i) Ω[B i⁄PowerSeries k]] {N d : ℕ} (hd : d ≤ 1)
    (hN : algebraMap (PowerSeries k) (B i) (PowerSeries.X ^ N) ∈
      fittingIdeal (R := B i) (M := Ω[B i⁄PowerSeries k]) (d : ℤ))
    {n : ℕ} (hn : N ≤ n) :
    haveI := locallyOfFiniteType_towerHom X ξ (liftBaseIso ξ e m) n
    letI := stalkAlgebra (PowerSeries k ⧸ discIdeal k ^ (n + 1))
      (towerHom X ξ (liftBaseIso ξ e m) n) ((ξ.level n).specialMap (p i))
    letI := moduleFinite_kaehler_stalkAlgebra (PowerSeries k ⧸ discIdeal k ^ (n + 1))
      (towerHom X ξ (liftBaseIso ξ e m) n) ((ξ.level n).specialMap (p i))
    algebraMap (PowerSeries k ⧸ discIdeal k ^ (n + 1))
        ((ξ.level n).scheme.presheaf.stalk ((ξ.level n).specialMap (p i)))
        (Ideal.Quotient.mk _ (PowerSeries.X ^ n)) ∈
      fittingIdeal (R := (ξ.level n).scheme.presheaf.stalk ((ξ.level n).specialMap (p i)))
        (M := Ω[(ξ.level n).scheme.presheaf.stalk ((ξ.level n).specialMap (p i))⁄
          (PowerSeries k ⧸ discIdeal k ^ (n + 1))]) ((1 : ℕ) : ℤ) := by
  have := locallyOfFiniteType_towerHom X ξ (liftBaseIso ξ e m) n
  let : Algebra (PowerSeries k ⧸ truncIdeal k n) (levelFiber k (B i) n) :=
    Ideal.Quotient.algebraQuotientMapQuotient
  let : ∀ i, Algebra k (X.left.presheaf.stalk (p i)) := fun i => stalkAlgebraOver X (p i)
  set σ := liftBaseIso ξ e m
  set y := (ξ.level n).specialMap (p i)
  set A' := PowerSeries k ⧸ discIdeal k ^ (n + 1)
  set O := (ξ.level n).scheme.presheaf.stalk y
  let := stalkAlgebra A' (towerHom X ξ σ n) y
  let := moduleFinite_kaehler_stalkAlgebra A' (towerHom X ξ σ n) y
  -- The level-`n` comparison of the stalk at `p i` with the level of the local smoothing.
  let c := (m.hom.app n).component i
  let c' := (m.inv.app n).component i
  have hcc : c ≫ c' = 𝟙 _ :=
    congrArg (fun f => PiOver.Hom.component f i) (FormalObject.app_hom_inv m n)
  have hc'c : c' ≫ c = 𝟙 _ :=
    congrArg (fun f => PiOver.Hom.component f i) (FormalObject.app_inv_hom m n)
  let F := c.left
  let G := c'.left
  have hFG : F.map ≫ G.map = 𝟙 _ :=
    congrArg (fun g => FlatAlgebraCategory.Hom.map (CommaMorphism.left g)) hcc
  have hGF : G.map ≫ F.map = 𝟙 _ :=
    congrArg (fun g => FlatAlgebraCategory.Hom.map (CommaMorphism.left g)) hc'c
  let ψ : O ≃+* levelFiber k (B i) n :=
    RingEquiv.ofRingHom F.map.hom G.map.hom (congrArg CommRingCat.Hom.hom hGF)
      (congrArg CommRingCat.Hom.hom hFG)
  -- The base of the comparison inverts the identification of the bases.
  have hbase : F.base = (m.hom.app n).hbase := by
    have := (m.hom.app n).hcomponent i
    have h := IsHomLift.fac' (ringDeformationBasedCategory k k
      (X.left.presheaf.stalk (p i))).p (m.hom.app n).hbase c
    exact h.trans (by rfl)
  have hρ : ∀ a : A', F.base.hom (towerRingHom X ξ σ n a) = discTruncEquiv n a := by
    intro a
    have h := congrArg (fun f => f.hom (discTruncEquiv n a)) (towerBaseHom_comp_hbase ξ e m n)
    rwa [← hbase] at h
  -- Compatibility of the two structure maps.
  have hcompat : ∀ a : A', algebraMap (PowerSeries k ⧸ truncIdeal k n) (levelFiber k (B i) n)
      (discTruncEquiv n a) = ψ (algebraMap A' O a) := by
    intro a
    have hG1 := algebraMap_stalkAlgebra_comp_specMap (ξ.level n).toBase (towerRingHom X ξ σ n) y a
    have hw := congrArg (fun f => f.hom (towerRingHom X ξ σ n a)) F.cartesian.w
    simp only [CommRingCat.hom_comp] at hw
    rw [← hρ a]
    exact hw.symm.trans (congrArg (fun z => F.map.hom z) hG1.symm)
  have := isPushout_quotient_map k (B i) (truncIdeal k n)
  let : Module.Finite (levelFiber k (B i) n)
      Ω[levelFiber k (B i) n⁄(PowerSeries k ⧸ truncIdeal k n)] :=
    Module.Finite.equiv (KaehlerDifferential.tensorKaehlerEquiv (PowerSeries k)
      (PowerSeries k ⧸ truncIdeal k n) (B i) (levelFiber k (B i) n))
  have hF2 := @fittingIdeal_kaehler_of_ringEquiv A' O (PowerSeries k ⧸ truncIdeal k n)
    (levelFiber k (B i) n) _ _ _ _ _ Ideal.Quotient.algebraQuotientMapQuotient ψ (discTruncEquiv n)
    hcompat _ _ 1
  have hlev := algebraMap_pow_X_mem_fittingIdeal_levelFiber k (B i) hd hN hn
  have h1 := hcompat (Ideal.Quotient.mk _ (PowerSeries.X ^ n))
  rw [discTruncEquiv_mk] at h1
  rw [h1, hF2, show Ideal.map ψ _ = Ideal.map (ψ : O →+* levelFiber k (B i) n) _ from rfl,
    Ideal.map_comap_of_equiv, Ideal.mem_comap] at hlev
  simpa using hlev

end Lift

/-- **Local smoothings.** The local ring of a local complete intersection over `k` at a point is
the special fibre of a flat essentially finite type `k⟦t⟧`-algebra `B` with a power of `t` in a
Fitting ideal of `Ω_{B/k⟦t⟧}`. -/
private theorem exists_flat_specialFiber_pow_mem_fittingIdeal_stalk (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (hlci : IsLocalCompleteIntersectionOverField f) (x : X) :
    letI : Algebra k (X.presheaf.stalk x) := stalkAlgebraOver (Over.mk f) x
    ∃ (dimA trdegR N : ℕ),
      ringKrullDim (X.presheaf.stalk x) = (dimA : WithBot ℕ∞) ∧
      Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk x)) = trdegR ∧
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra (PowerSeries k) B)
        (_ : Algebra.EssFiniteType (PowerSeries k) B) (_ : Module.Flat (PowerSeries k) B)
        (_ : Algebra k B) (_ : IsScalarTower k (PowerSeries k) B),
        Nonempty ((B ⧸ Ideal.span {algebraMap (PowerSeries k) B PowerSeries.X}) ≃ₐ[k]
          X.presheaf.stalk x) ∧
        algebraMap (PowerSeries k) B (PowerSeries.X ^ N) ∈
          fittingIdeal (R := B) (M := KaehlerDifferential (PowerSeries k) B)
            ((dimA + trdegR : ℕ) : ℤ) := by
  let : Algebra k (X.presheaf.stalk x) := stalkAlgebraOver (Over.mk f) x
  obtain ⟨hCI, hEss⟩ := isCompleteIntersectionLocalRing_stalk f hlci x
  exact @exists_flat_essFiniteType_specialFiber_pow_mem_fittingIdeal k _ _ _ _ _ hEss hCI

/-- At a closed point of a scheme of dimension at most one, locally of finite type over `k`, the
dimension of the local ring plus the transcendence degree of its residue field is at most one. -/
private theorem ringKrullDim_add_trdeg_stalk_le_one (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (hdim : topologicalKrullDim X ≤ 1) {x : X}
    (hx : IsClosed ({x} : Set X)) {d t : ℕ}
    (hd : ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞))
    (ht : letI : Algebra k (X.presheaf.stalk x) := stalkAlgebraOver (Over.mk f) x
      Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk x)) = t) :
    d + t ≤ 1 := by
  obtain ⟨h1, h2⟩ := ringKrullDim_stalk_le_one_and_trdeg_eq_zero f hdim hx
  have hdA : d ≤ 1 := by exact_mod_cast hd.symm.le.trans h1
  have htR : t = 0 := by exact_mod_cast ht.symm.trans h2
  omega

/-- **The formal smoothing of a curve.** Let `X` be a separated scheme of finite type over a field
`k` with `dim(X) ≤ 1`, a local complete intersection over `k`, and smooth over `k` away from
finitely many points. Then there is a tower `X_n` of schemes flat over the thickenings
`Spec (k⟦t⟧/(t)^{n+1})`, with cartesian transition squares, with `X_0 ≅ X` over `k`, and such that
for some `n` the image of `t^n` lies, on every affine open of `X_n`, in the first Fitting ideal of
the relative differentials of `X_n` over `Spec (k⟦t⟧/(t)^{n+1})`.

This is the first half of the proof of [Stacks, Tag 0E7Y]. At each singular point `p_i` the local
ring is a complete intersection, and [Stacks, Tag 0E7X] gives a flat `k⟦t⟧`-algebra `B_i` with
`B_i/tB_i ≅ 𝒪_{X,p_i}` and `t^{N_i}` in the first Fitting ideal of `Ω_{B_i/k⟦t⟧}`. By
[Stacks, Tag 0DZP] and [Stacks, Tag 06HN] the formal object `(B_i/t^{n+1})` of
`∏ Def_{𝒪_{X,p_i}}` lifts to a formal object `(X_n)` of `Def_X`, and the Fitting ideal is computed
in the local rings of `X_n`: it is the unit ideal at the smooth points, and at `p_i` the local ring
of `X_n` is `B_i/t^{n+1}`, where Fitting ideals commute with base change ([Stacks, Tag 07ZA]). -/
theorem exists_formalSmoothingTower (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hlci : IsLocalCompleteIntersectionOverField f) (hfin : ((f.smoothLocus : Set X)ᶜ).Finite)
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (Xn : ℕ → Scheme.{u}) (q : ∀ n, Xn n ⟶ adicThickening (PowerSeries k) (discIdeal k) n)
      (i : ∀ n, Xn n ⟶ Xn (n + 1)),
      (∀ n, IsPullback (i n) (q n) (q (n + 1))
        (adicThickeningSucc (PowerSeries k) (discIdeal k) n)) ∧
      (∀ n, Flat (q n)) ∧
      (∃ e₀ : X ≅ Xn 0, e₀.hom ≫ q 0 ≫
          Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k ⧸ discIdeal k ^ (0 + 1)))) =
        f) ∧
      ∃ n, ∀ U : (Xn n).affineOpens,
        (q n).appLE ⊤ U.1 (SmoothingCriterion.le_preimage_top (q n) U.1)
            ((Scheme.ΓSpecIso (.of (PowerSeries k ⧸ discIdeal k ^ (n + 1)))).inv
              (Ideal.Quotient.mk (discIdeal k ^ (n + 1)) (PowerSeries.X ^ n))) ∈
          (fittingIdeal (Scheme.Hom.relativeDifferentials (q n)) (1 : ℤ)).ideal U := by
  classical
  let X' : Over (Spec (.of k)) := Over.mk f
  have : IsSeparated X'.hom := ‹_›
  have : LocallyOfFiniteType X'.hom := ‹_›
  have : QuasiCompact X'.hom := ‹_›
  -- The singular points.
  let ι : Type u := ↥((f.smoothLocus : Set X)ᶜ)
  have : Finite ι := hfin.to_subtype
  have : Fintype ι := Fintype.ofFinite ι
  let p : ι → X'.left := Subtype.val
  have hinj : Function.Injective p := Subtype.val_injective
  have hclosed : ∀ i, IsClosed ({p i} : Set X'.left) := fun i =>
    isClosed_singleton_of_notMem_smoothLocus k f hfin i.2
  have hsm : ∀ x : X'.left, x ∉ Set.range p → x ∈ X'.hom.smoothLocus := fun x hx =>
    of_not_not fun h => hx ⟨⟨x, h⟩, rfl⟩
  -- The local smoothings at the singular points (Stacks 0E7X).
  have H := fun i : ι => exists_flat_specialFiber_pow_mem_fittingIdeal_stalk k f hlci (p i)
  choose dimA trdegR N hdimA htr B hB hPS hEss hFl hk hTow he hfit using H
  let : ∀ i, CommRing (B i) := hB
  let : ∀ i, Algebra (PowerSeries k) (B i) := hPS
  have : ∀ i, Algebra.EssFiniteType (PowerSeries k) (B i) := hEss
  have : ∀ i, Module.Flat (PowerSeries k) (B i) := hFl
  let : ∀ i, Algebra k (B i) := hk
  have : ∀ i, IsScalarTower k (PowerSeries k) (B i) := hTow
  have hd : ∀ i, dimA i + trdegR i ≤ 1 := fun i =>
    ringKrullDim_add_trdeg_stalk_le_one k f hdim (hclosed i) (hdimA i) (htr i)
  let e : let : ∀ i, Algebra k (X'.left.presheaf.stalk (p i)) := fun i => stalkAlgebraOver X' (p i)
      ∀ i, (B i ⧸ Ideal.span {algebraMap (PowerSeries k) (B i) PowerSeries.X}) ≃ₐ[k]
        X'.left.presheaf.stalk (p i) := fun i => (he i).some
  -- The formal deformation of `X` (Stacks 0DZP and 06HN).
  obtain ⟨ξ, ⟨m⟩⟩ := exists_formalObject_iso_piFormalObject X' p hdim hinj hclosed hsm B e
  let σ := liftBaseIso ξ e m
  let n₀ := Finset.univ.sup N
  refine ⟨fun n => (ξ.level n).scheme, towerHom X' ξ σ, fun n => (ξ.transition n).map,
    isPullback_towerHom X' ξ σ, flat_towerHom X' ξ σ, exists_iso_towerHom_zero X' ξ σ,
    n₀, fun U => ?_⟩
  have := locallyOfFiniteType_towerHom X' ξ σ n₀
  have key := appLE_mem_fittingIdeal_relativeDifferentials_of_forall_stalk
    (PowerSeries k ⧸ discIdeal k ^ (n₀ + 1)) (towerHom X' ξ σ n₀)
    (Ideal.Quotient.mk (discIdeal k ^ (n₀ + 1)) (PowerSeries.X ^ n₀)) 1 (fun y => ?_) U
  · simpa using key
  obtain ⟨x, rfl⟩ := deformationSpecialMap_surjective (ξ.level n₀) y
  by_cases hx : x ∈ X'.hom.smoothLocus
  · exact mem_fittingIdeal_stalk_of_mem_smoothLocus X' hdim ξ σ n₀ hx _
  · exact mem_fittingIdeal_stalk_of_iso_levelHom ξ e m ⟨x, hx⟩ (hd ⟨x, hx⟩) (hfit ⟨x, hx⟩)
      (Finset.le_sup (Finset.mem_univ _))

end Deformation.Examples.Smoothing

end
