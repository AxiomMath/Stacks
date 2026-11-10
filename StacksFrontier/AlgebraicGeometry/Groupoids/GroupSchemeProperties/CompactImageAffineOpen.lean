module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.JacobsonSpace
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Profinite.ClopenRefinement
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AffineLimits
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.IdentitySubgroup
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Multiplication
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Separated
public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.RationalPointsAffineOpen
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.DescentSituation
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.ResidueField
public import StacksFrontier.Topology.Spectral.ComponentSpace

/-!
# The image of a pro-finite point of a group scheme lies in an affine open

Let `G` be a group scheme over an algebraically closed field `k` whose underlying space is
Jacobson and all of whose closed points are rational.  If a `k`-algebra `A` is a filtered
colimit of finite products of copies of `k`, then the image of every morphism `Spec A ⟶ G`
over `k` is contained in an affine open of `G`.

The argument translates the problem to the identity component.  The saturation of a compact
open neighbourhood of the identity under left translation by the identity component is open
and stable under translation by rational points of the identity component, hence contains the
whole connected component of any of its rational points.  Over a pro-finite base the fibre
product of `G` with `Spec A` is the product of the underlying spaces, so a common translate
can be chosen on a whole compact set of parameters; the resulting affine open is pulled back
along a translation.  Finally the connected components of the compact image are separated by
clopen subsets, and an affine open is assembled from the pieces.

## Main results

* `AlgebraicGeometry.exists_affineOpen_range_subset`: the affine open containing the image.

## Implementation notes

The directed-colimit hypothesis is `AlgebraicGeometry.IsFilteredColimitOfFiniteProducts`, and
rationality of a closed point means that it is the image of a morphism `Spec k ⟶ G` over
`Spec k`.  Translations by rational points are automorphisms of the underlying scheme, so they
are used as homeomorphisms of the underlying space throughout.

## References

* [Stacks Project, Tag 0B7U](https://stacks.math.columbia.edu/tag/0B7U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry

/-- An equation between composites in `Over S` holds pointwise on the underlying spaces. -/
private theorem over_comp_left_base_apply {S : Scheme.{u}} {X Y Z : Over S}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) (x : X.left) :
    g.left.base (f.left.base x) = h.left.base x := by
  rw [← e]
  rfl

/-- The underlying morphism of an isomorphism in `Over S` is an isomorphism. -/
private theorem isIso_hom_left {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y) :
    IsIso e.hom.left :=
  inferInstanceAs (IsIso ((Over.forget S).map e.hom))

/-- The structure morphism to the unit sends every point to the unique point of `Spec k`. -/
private theorem toUnit_left_base_eq_bot {k : Type u} [Field k] (T : Over (Spec (.of k)))
    (t : T.left) : (toUnit T).left.base t = (⊥ : PrimeSpectrum k) := by
  have : Subsingleton (↥((𝟙_ (Over (Spec (.of k)))).left)) := by
    change Subsingleton (PrimeSpectrum k)
    exact Ring.KrullDimLE.subsingleton_primeSpectrum k
  exact Subsingleton.elim _ _

@[sga "3 VIA 2.4" "(i), special case", sga "3 VIA 2.6.5" "(ii)"]
private theorem identityComponent_irreducibleSpace
    (k : Type u) [Field k] (G : Grp (Over (Spec (CommRingCat.of k)))) :
    IrreducibleSpace (identityComponent k G).carrier.X.left := by
  let H := identityComponent k G
  let _inst : GeometricallyIrreducible H.carrier.X.hom :=
    identityComponent_geometricallyIrreducible k G
  exact GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := H.carrier.X.hom)

private noncomputable def graphTranslationIso {k : Type u} [Field k]
    (T G : Over (Spec (.of k))) [GrpObj G] (f : T ⟶ G) : T ⊗ G ≅ T ⊗ G :=
  { hom := lift (fst T G) (lift (fst T G ≫ f) (snd T G) ≫ μ[G])
    inv := lift (fst T G) (lift ((fst T G ≫ f)⁻¹) (snd T G) ≫ μ[G])
    hom_inv_id := by
      apply hom_ext <;> simp [GrpObj.comp_inv, MonObj.comp_mul, MonObj.mul_eq_mul]
    inv_hom_id := by apply hom_ext <;> simp [MonObj.comp_mul, MonObj.mul_eq_mul] }

private noncomputable def groupInverseIso {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k)))) : G.X ≅ G.X := by
  let _inst : GrpObj G.X := G.grp
  exact ⟨GrpObj.inv, GrpObj.inv, by simp, by simp⟩

@[ega "IV 17.12.7" "special case"]
private noncomputable def rationalLeftTranslationIso {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k))))
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) : G.X ≅ G.X := by
  let _inst : GrpObj G.X := G.grp
  exact (groupInverseIso G).trans
    ((GrpObj.mulRight (p ≫ GrpObj.inv)).trans (groupInverseIso G))

@[ega "IV 17.12.7" "formula τ_s = m∘(s×1_G)"]
private theorem rationalLeftTranslationIso_hom {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k))))
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) :
    (rationalLeftTranslationIso G p).hom =
      lift (toUnit G.X ≫ p) (𝟙 G.X) ≫ μ[G.X] := by
  let _inst : GrpObj G.X := G.grp
  have hpair : GrpObj.inv ≫ lift (toUnit G.X ≫ p) GrpObj.inv =
      lift (toUnit G.X ≫ p) (𝟙 G.X) := by
    apply hom_ext
    · simp
    · calc
        GrpObj.inv ≫ lift (toUnit G.X ≫ p) GrpObj.inv ≫ snd G.X G.X =
            GrpObj.inv ≫ GrpObj.inv := by simp
        _ = 𝟙 G.X := by simp
        _ = lift (toUnit G.X ≫ p) (𝟙 G.X) ≫ snd G.X G.X := by simp
  suffices h : GrpObj.inv ≫ lift (toUnit G.X ≫ p) GrpObj.inv ≫ μ[G.X] =
      lift (toUnit G.X ≫ p) (𝟙 G.X) ≫ μ[G.X] by
    simpa [rationalLeftTranslationIso, groupInverseIso, GrpObj.mulRight_hom,
      GrpObj.mul_inv_rev, Category.assoc] using h
  rw [← Category.assoc, hpair]

/-- Precomposing a rational left translation with `b` multiplies `b` on the left. -/
private theorem comp_rationalLeftTranslationIso_hom
    {k : Type u} [Field k] (G : Grp (Over (Spec (.of k))))
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) {Y : Over (Spec (.of k))} (b : Y ⟶ G.X) :
    b ≫ (rationalLeftTranslationIso G p).hom = (toUnit Y ≫ p) * b := by
  rw [rationalLeftTranslationIso_hom, ← Hom.mul_def, MonObj.comp_mul]
  have hu : b ≫ toUnit G.X = toUnit Y := toUnit_unique _ _
  rw [← Category.assoc, hu]
  simp

@[ega "IV 17.12.7" "special case"]
private theorem rationalLeftTranslationIso_comp_rational
    {k : Type u} [Field k] (G : Grp (Over (Spec (.of k))))
    (p q : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) :
    q ≫ (rationalLeftTranslationIso G p).hom = p * q := by
  rw [comp_rationalLeftTranslationIso_hom]
  simp

private theorem rightTranslationIso_comp_mul_cancel
    {k : Type u} [Field k] (G : Grp (Over (Spec (.of k))))
    (p q : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) :
    (q ≫ (rightTranslationIso G (p ≫ GrpObj.inv)).hom) * p = q := by
  rw [rightTranslationIso, GrpObj.mulRight_hom, ← Hom.mul_def, MonObj.comp_mul]
  have hu : q ≫ toUnit G.X = toUnit (𝟙_ (Over (Spec (.of k)))) :=
    toUnit_unique _ _
  rw [← Category.assoc, hu, ← Hom.inv_def]
  simp only [Category.comp_id, toUnit_unit, Category.id_comp]
  rw [mul_assoc, inv_mul_cancel, mul_one]

private theorem rationalLeftRightTranslationIso_commute
    {k : Type u} [Field k] (G : Grp (Over (Spec (.of k))))
    (p q : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) :
    (rationalLeftTranslationIso G p).hom ≫
        (rightTranslationIso G q).hom =
      (rightTranslationIso G q).hom ≫
        (rationalLeftTranslationIso G p).hom := by
  rw [rationalLeftTranslationIso_hom, rightTranslationIso, GrpObj.mulRight_hom]
  simp [comp_lift_assoc, MonObj.lift_lift_assoc]

private theorem rational_translate_connectedComponent_mem_identityComponent
    {k : Type u} [Field k] (G : Grp (Over (Spec (.of k))))
    (p q : 𝟙_ (Over (Spec (.of k))) ⟶ G.X)
    (hq : q.left.base (⊥ : PrimeSpectrum k) ∈
      connectedComponent (p.left.base (⊥ : PrimeSpectrum k))) :
    rightTranslationHomeo G (p ≫ GrpObj.inv)
      (q.left.base (⊥ : PrimeSpectrum k)) ∈
        connectedComponent ((η[G.X]).left.base (⊥ : PrimeSpectrum k)) := by
  let τ := rightTranslationHomeo G (p ≫ GrpObj.inv)
  have hτp : τ (p.left.base (⊥ : PrimeSpectrum k)) =
      (η[G.X]).left.base (⊥ : PrimeSpectrum k) :=
    rightTranslationHomeo_apply_self G p
  have hτ := Homeomorph.image_connectedComponent τ
    (p.left.base (⊥ : PrimeSpectrum k))
  rw [hτp] at hτ
  rw [← hτ]
  exact Set.mem_image_of_mem τ hq

private theorem lift_rational_point_through_identityComponent
    {k : Type u} [Field k] (G : Grp (Over (Spec (.of k))))
    (p : Over.mk (𝟙 (Spec (.of k))) ⟶ G.X)
    (hp : p.left.base (⊥ : PrimeSpectrum k) ∈
      connectedComponent (identityPoint k G)) :
    ∃ q : Over.mk (𝟙 (Spec (.of k))) ⟶
        (identityComponent k G).carrier.X,
      q ≫ (identityComponent k G).ι.hom.hom = p := by
  let H := identityComponent k G
  let i := H.ι.hom.hom.left
  let g := p.left
  have : Subsingleton (↥((Over.mk (𝟙 (Spec (.of k)))).left)) := by
    change Subsingleton (PrimeSpectrum (CommRingCat.of k))
    exact Ring.KrullDimLE.subsingleton_primeSpectrum (CommRingCat.of k)
  let _inst : Flat i := identityComponent_flat k G
  have hrange : Set.range g.base ⊆ Set.range i.base := by
    rw [identityComponent_range]
    rintro _ ⟨s, rfl⟩
    obtain rfl : s = (⊥ : PrimeSpectrum k) := Subsingleton.elim _ _
    exact hp
  have hsurj : Surjective (pullback.fst g i) := by
    rw [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_fst,
      Set.preimage_eq_univ_iff]
    rintro x ⟨s, rfl⟩
    exact hrange ⟨s, rfl⟩
  let _inst : Surjective (pullback.fst g i) := hsurj
  have : IsClosedImmersion i := H.isClosedImmersion
  have : QuasiCompact i := by
    infer_instance
  have : IsIso (pullback.fst g i) :=
    Flat.isIso_of_surjective_of_mono (pullback.fst g i)
  let e : Spec (.of k) ⟶ H.carrier.X.left :=
    inv (pullback.fst g i) ≫ pullback.snd g i
  have he : e ≫ i = g := by
    dsimp [e]
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  have hebase : e ≫ H.carrier.X.hom = 𝟙 (Spec (.of k)) := by
    calc
      e ≫ H.carrier.X.hom = e ≫ i ≫ G.X.hom := by
        simpa only [Category.assoc] using
          (congrArg (fun t : Scheme.Hom H.carrier.X.left (Spec (.of k)) => e ≫ t)
            H.ι.hom.hom.w).symm
      _ = g ≫ G.X.hom := by
        simpa only [Category.assoc] using
          congrArg (fun t : Scheme.Hom (Spec (.of k)) G.X.left => t ≫ G.X.hom) he
      _ = 𝟙 (Spec (.of k)) := Over.w p
  exact ⟨Over.homMk e hebase, Over.OverMorphism.ext he⟩

private theorem leftIdentityComponent_saturation_stable_under_rational_left
    {k : Type u} [Field k] (G : Grp (Over (Spec (.of k))))
    (U : G.X.left.Opens)
    (p : Over.mk (𝟙 (Spec (.of k))) ⟶
      (identityComponent k G).carrier.X)
    (x : G.X.left)
    (hx : x ∈ Set.image
      (lift (fst (identityComponent k G).carrier.X G.X ≫
        (identityComponent k G).ι.hom.hom)
        (snd (identityComponent k G).carrier.X G.X) ≫ μ[G.X]).left.base
      ((snd (identityComponent k G).carrier.X G.X).left.base ⁻¹' U)) :
    (rationalLeftTranslationIso G (p ≫
      (identityComponent k G).ι.hom.hom)).hom.left.base x ∈
      Set.image
        (lift (fst (identityComponent k G).carrier.X G.X ≫
          (identityComponent k G).ι.hom.hom)
          (snd (identityComponent k G).carrier.X G.X) ≫ μ[G.X]).left.base
        ((snd (identityComponent k G).carrier.X G.X).left.base ⁻¹' U) := by
  classical
  let H := identityComponent k G
  let T := H.carrier.X
  let ψ := H.ι.hom.hom
  let m := lift (fst T G.X ≫ ψ) (snd T G.X) ≫ μ[G.X]
  let V := (snd T G.X).left.base ⁻¹' (U : Set G.X.left)
  let pG := p ≫ ψ
  let lH := rationalLeftTranslationIso H.carrier p
  let lG := rationalLeftTranslationIso G pG
  let α : T ⊗ G.X ⟶ T ⊗ G.X := lift (fst T G.X ≫ lH.hom) (snd T G.X)
  have hαsnd : α ≫ snd T G.X = snd T G.X := by simp [α]
  have hαfst : α ≫ fst T G.X = fst T G.X ≫ lH.hom := by simp [α]
  have hfa : α ≫ (fst T G.X ≫ ψ) = (fst T G.X ≫ lH.hom) ≫ ψ := by
    rw [← Category.assoc, hαfst]
  have hright : m ≫ lG.hom = (toUnit (T ⊗ G.X) ≫ pG) * m :=
    comp_rationalLeftTranslationIso_hom G pG m
  have htrans : lH.hom ≫ ψ = ψ ≫ lG.hom := by
    rw [rationalLeftTranslationIso_hom, rationalLeftTranslationIso_hom]
    rw [← Hom.mul_def, ← Hom.mul_def]
    rw [MonObj.mul_comp, MonObj.comp_mul]
    simp [pG]
  have hfirst : (fst T G.X ≫ lH.hom) ≫ ψ =
      (toUnit (T ⊗ G.X) ≫ pG) * (fst T G.X ≫ ψ) := by
    calc
      (fst T G.X ≫ lH.hom) ≫ ψ = fst T G.X ≫ (lH.hom ≫ ψ) := by
        rw [Category.assoc]
      _ = fst T G.X ≫ (ψ ≫ lG.hom) := by rw [htrans]
      _ = (fst T G.X ≫ ψ) ≫ lG.hom := by rw [Category.assoc]
      _ = (toUnit (T ⊗ G.X) ≫ pG) * (fst T G.X ≫ ψ) :=
        comp_rationalLeftTranslationIso_hom G pG _
  have hαm : α ≫ m = m ≫ lG.hom := by
    change α ≫ ((fst T G.X ≫ ψ) * (snd T G.X)) = _
    rw [MonObj.comp_mul, hfa, hαsnd]
    rw [hfirst, hright]
    have hm : m = (fst T G.X ≫ ψ) * (snd T G.X) := by
      exact (Hom.mul_def _ _).symm
    rw [hm]
    exact mul_assoc _ _ _
  rcases (by simpa [m, V, H, T, ψ] using hx) with ⟨z, hz, rfl⟩
  refine ⟨α.left.base z, ?_, ?_⟩
  · change (snd T G.X).left.base (α.left.base z) ∈ U
    rw [over_comp_left_base_apply hαsnd]
    exact hz
  · exact over_comp_left_base_apply hαm z

private theorem leftIdentityComponent_saturation_contains_connectedComponent
    {k : Type u} [Field k] (G : Grp (Over (Spec (CommRingCat.of k))))
    [JacobsonSpace G.X.left]
    (hclosed : ∀ x : G.X.left, IsClosed ({x} : Set G.X.left) →
      ∃ p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        p.left.base (⊥ : PrimeSpectrum k) = x)
    (U : G.X.left.Opens) (_hUcompact : IsCompact (U : Set G.X.left))
    (p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hp : p.left.base (⊥ : PrimeSpectrum k) ∈ Set.image
      (lift (fst (identityComponent k G).carrier.X G.X ≫
        (identityComponent k G).ι.hom.hom)
        (snd (identityComponent k G).carrier.X G.X) ≫ μ[G.X]).left.base
      ((snd (identityComponent k G).carrier.X G.X).left.base ⁻¹'
        (U : Set G.X.left))) :
    connectedComponent (p.left.base (⊥ : PrimeSpectrum k)) ⊆
      Set.image
        (lift (fst (identityComponent k G).carrier.X G.X ≫
          (identityComponent k G).ι.hom.hom)
          (snd (identityComponent k G).carrier.X G.X) ≫ μ[G.X]).left.base
        ((snd (identityComponent k G).carrier.X G.X).left.base ⁻¹'
          (U : Set G.X.left)) := by
  classical
  let H := identityComponent k G
  let T := H.carrier.X
  let ψ := H.ι.hom.hom
  let m := lift (fst T G.X ≫ ψ) (snd T G.X) ≫ μ[G.X]
  let sat := Set.image m.left.base ((snd T G.X).left.base ⁻¹' (U : Set G.X.left))
  have hsatu : IsOpen sat := isOpen_image_mul_of_open G.X T ψ U
  let K := connectedComponent (p.left.base (⊥ : PrimeSpectrum k))
  have hKclosed : IsClosed K := isClosed_connectedComponent
  have hS : IsLocallyClosed (K ∩ sat) :=
    hKclosed.isLocallyClosed.inter hsatu.isLocallyClosed
  have hSne : (K ∩ sat).Nonempty := ⟨_, mem_connectedComponent, hp⟩
  obtain ⟨x, hxS, hxc⟩ := nonempty_inter_closedPoints hSne hS
  obtain ⟨p₀, hp₀⟩ := hclosed x (mem_closedPoints_iff.mp hxc)
  have hp₀sat : p₀.left.base (⊥ : PrimeSpectrum k) ∈ sat := hp₀ ▸ hxS.2
  have hclosedMem : ∀ z : G.X.left, z ∈ K → IsClosed ({z} : Set G.X.left) → z ∈ sat := by
    intro z hzK hzc
    obtain ⟨q, hq⟩ := hclosed z hzc
    change z ∈ connectedComponent (p.left.base (⊥ : PrimeSpectrum k)) at hzK
    have hp₀K : p₀.left.base (⊥ : PrimeSpectrum k) ∈ K := hp₀ ▸ hxS.1
    have hqK : q.left.base (⊥ : PrimeSpectrum k) ∈ K := hq ▸ hzK
    have hcomp : connectedComponent (p₀.left.base (⊥ : PrimeSpectrum k)) =
        connectedComponent (q.left.base (⊥ : PrimeSpectrum k)) :=
      (connectedComponent_eq hp₀K).symm.trans (connectedComponent_eq hqK)
    have hqcomp : q.left.base (⊥ : PrimeSpectrum k) ∈
        connectedComponent (p₀.left.base (⊥ : PrimeSpectrum k)) := by
      rw [hcomp]
      exact mem_connectedComponent
    let r : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X :=
      q ≫ (rightTranslationIso G (p₀ ≫ GrpObj.inv)).hom
    have hrmem : r.left.base (⊥ : PrimeSpectrum k) ∈
        connectedComponent (identityPoint k G) := by
      change rightTranslationHomeo G (p₀ ≫ GrpObj.inv)
        (q.left.base (⊥ : PrimeSpectrum k)) ∈ _
      exact rational_translate_connectedComponent_mem_identityComponent G p₀ q hqcomp
    obtain ⟨rH, hrH⟩ := lift_rational_point_through_identityComponent G r hrmem
    have htrans : p₀ ≫ (rationalLeftTranslationIso G r).hom = q := by
      rw [rationalLeftTranslationIso_comp_rational]
      exact rightTranslationIso_comp_mul_cancel G p₀ q
    have hleftPoint : (rationalLeftTranslationIso G (rH ≫ ψ)).hom.left.base
        (p₀.left.base (⊥ : PrimeSpectrum k)) = z := by
      have htrans' : p₀ ≫ (rationalLeftTranslationIso G (rH ≫ ψ)).hom = q := by
        rwa [← hrH] at htrans
      have h := congrArg Over.Hom.left htrans'
      have h' := congrArg
        (fun f : Scheme.Hom ((𝟙_ (Over (Spec (CommRingCat.of k)))).left) G.X.left =>
          f.base (⊥ : PrimeSpectrum k)) h
      change (p₀.left ≫ (rationalLeftTranslationIso G (rH ≫ ψ)).hom.left).base
          (⊥ : PrimeSpectrum k) = z
      exact h'.trans hq
    have hstable := leftIdentityComponent_saturation_stable_under_rational_left
      G U rH (p₀.left.base (⊥ : PrimeSpectrum k)) hp₀sat
    change (rationalLeftTranslationIso G (rH ≫ ψ)).hom.left.base
      (p₀.left.base (⊥ : PrimeSpectrum k)) ∈ sat at hstable
    rw [hleftPoint] at hstable
    simpa only [sat, m, ψ, T, H] using hstable
  intro z hzK
  by_contra hzsat
  have hbadne : (K \ sat).Nonempty := ⟨z, hzK, hzsat⟩
  have hbadclosed : IsClosed (K \ sat) := hKclosed.sdiff hsatu
  obtain ⟨z₀, hz₀, hzc₀⟩ := nonempty_inter_closedPoints hbadne hbadclosed.isLocallyClosed
  exact hz₀.2 (hclosedMem z₀ hz₀.1 (mem_closedPoints_iff.mp hzc₀))

private theorem translated_leftIdentityComponent_saturation_stable_under_rational_left
    {k : Type u} [Field k] (G : Grp (Over (Spec (CommRingCat.of k))))
    (U : G.X.left.Opens)
    (z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (identityComponent k G).carrier.X)
    (x : G.X.left)
    (hx : x ∈ Set.image
      (rightTranslationIso G (z ≫ GrpObj.inv)).hom.left.base
      (Set.image
        (lift (fst (identityComponent k G).carrier.X G.X ≫
          (identityComponent k G).ι.hom.hom)
          (snd (identityComponent k G).carrier.X G.X) ≫ μ[G.X]).left.base
        ((snd (identityComponent k G).carrier.X G.X).left.base ⁻¹'
          (U : Set G.X.left)))) :
    (rationalLeftTranslationIso G (p ≫
      (identityComponent k G).ι.hom.hom)).hom.left.base x ∈
      Set.image
        (rightTranslationIso G (z ≫ GrpObj.inv)).hom.left.base
        (Set.image
          (lift (fst (identityComponent k G).carrier.X G.X ≫
            (identityComponent k G).ι.hom.hom)
            (snd (identityComponent k G).carrier.X G.X) ≫ μ[G.X]).left.base
          ((snd (identityComponent k G).carrier.X G.X).left.base ⁻¹'
            (U : Set G.X.left))) := by
  classical
  let H := identityComponent k G
  let T := H.carrier.X
  let ψ := H.ι.hom.hom
  let R := rightTranslationIso G (z ≫ GrpObj.inv)
  let L := rationalLeftTranslationIso G (p ≫ ψ)
  let sat := Set.image
    (lift (fst T G.X ≫ ψ) (snd T G.X) ≫ μ[G.X]).left.base
    ((snd T G.X).left.base ⁻¹' (U : Set G.X.left))
  change x ∈ Set.image R.hom.left.base sat at hx
  rcases hx with ⟨x₀, hx₀, rfl⟩
  have hstable := leftIdentityComponent_saturation_stable_under_rational_left
    G U p x₀ hx₀
  have hcomm : R.hom.left.base (L.hom.left.base x₀) =
      L.hom.left.base (R.hom.left.base x₀) :=
    over_comp_left_base_apply
      (rationalLeftRightTranslationIso_commute G (p ≫ ψ) (z ≫ GrpObj.inv)) x₀
  refine ⟨L.hom.left.base x₀, ?_, hcomm⟩
  simpa only [sat, L, T, H, ψ] using hstable

@[ega "IV 15.6.10" "partial", sga "3 VIA 2.6.5" "(iii)"]
private theorem identityComponent_connectedComponent_irreducible
    {k : Type u} [Field k] (G : Grp (Over (Spec (.of k)))) :
    IrreducibleSpace
      {x : G.X.left // x ∈ connectedComponent (identityPoint k G)} := by
  let H := identityComponent k G
  let ψ := H.ι.hom.hom.left
  let _inst : IsClosedImmersion ψ := H.isClosedImmersion
  let e := ψ.isClosedEmbedding.isEmbedding.homeomorphImage Set.univ
  have himage : ψ '' Set.univ = connectedComponent (identityPoint k G) := by
    rw [Set.image_univ, ← identityComponent_range]
  have hH : IrreducibleSpace H.carrier.X.left :=
    identityComponent_irreducibleSpace k G
  have hUniv : IrreducibleSpace ↥Set.univ :=
    (Homeomorph.Set.univ H.carrier.X.left).irreducibleSpace_iff.mpr hH
  have hImage : IrreducibleSpace {x : G.X.left // x ∈ ψ '' Set.univ} :=
    e.irreducibleSpace_iff.mp hUniv
  exact himage ▸ hImage



private theorem specProduct_isHomeomorph {k A : Type u} [Field k] [CommRing A]
    [Algebra k A] (hA : IsFilteredColimitOfFiniteProducts k A)
    (G : Grp (Over (Spec (.of k)))) :
    IsHomeomorph (fun x :
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) G.X.hom : Scheme.{u}) ↦
        ((pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A))) G.X.hom).base x,
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A))) G.X.hom).base x)) := by
  exact isHomeomorph_pullback_to_product k A hA G.X.left G.X.hom

private noncomputable def translatedProductHomeo {k A : Type u} [Field k]
    [CommRing A] [Algebra k A]
    (hA : IsFilteredColimitOfFiniteProducts k A)
    (G : Grp (Over (Spec (.of k)))) (f :
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ G.X) :
    ((Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⊗ G.X).left) ≃ₜ
      G.X.left × PrimeSpectrum A := by
  let T : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  let hτ := ((Over.forget (Spec (.of k))).mapIso
    (graphTranslationIso T G.X f)).hom.homeomorph
  let hp := IsHomeomorph.homeomorph
    (fun x : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) G.X.hom : Scheme.{u}) =>
      ((pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A))) G.X.hom).base x,
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A))) G.X.hom).base x))
    (specProduct_isHomeomorph hA G)
  exact hτ.trans (hp.trans (Homeomorph.prodComm _ _))

private theorem translatedProductHomeo_fst {k A : Type u} [Field k]
    [CommRing A] [Algebra k A]
    (hA : IsFilteredColimitOfFiniteProducts k A)
    (G : Grp (Over (Spec (.of k)))) (f :
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ G.X)
    (p : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⊗ G.X).left) :
    (translatedProductHomeo hA G f p).1 =
      (snd (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))) G.X).left.base
        ((graphTranslationIso _ G.X f).hom.left.base p) := by
  let T : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  let hτ := ((Over.forget (Spec (.of k))).mapIso
    (graphTranslationIso T G.X f)).hom.homeomorph
  let hp := IsHomeomorph.homeomorph
    (fun x : (pullback T.hom G.X.hom : Scheme.{u}) =>
      ((pullback.fst T.hom G.X.hom).base x, (pullback.snd T.hom G.X.hom).base x))
    (specProduct_isHomeomorph hA G)
  change ((hτ.trans (hp.trans (Homeomorph.prodComm _ _))) p).1 = _
  rw [Homeomorph.trans_apply, Homeomorph.trans_apply]
  rfl

private theorem translatedProductHomeo_snd {k A : Type u} [Field k]
    [CommRing A] [Algebra k A]
    (hA : IsFilteredColimitOfFiniteProducts k A)
    (G : Grp (Over (Spec (.of k)))) (f :
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ G.X)
    (p : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⊗ G.X).left) :
    (translatedProductHomeo hA G f p).2 =
      (fst (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))) G.X).left.base p := by
  let T : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  let hτ := ((Over.forget (Spec (.of k))).mapIso
    (graphTranslationIso T G.X f)).hom.homeomorph
  let hp := IsHomeomorph.homeomorph
    (fun x : (pullback T.hom G.X.hom : Scheme.{u}) =>
      ((pullback.fst T.hom G.X.hom).base x, (pullback.snd T.hom G.X.hom).base x))
    (specProduct_isHomeomorph hA G)
  change ((hτ.trans (hp.trans (Homeomorph.prodComm _ _))) p).2 = _
  rw [Homeomorph.trans_apply, Homeomorph.trans_apply]
  change (hp (hτ p)).1 = _
  rw [IsHomeomorph.homeomorph_apply]
  have hfirstHom : (graphTranslationIso T G.X f).hom ≫ fst T G.X = fst T G.X := by
    apply Over.OverMorphism.ext
    simp [graphTranslationIso]
  change (fst T G.X).left.base ((graphTranslationIso T G.X f).hom.left.base p) = _
  change (((graphTranslationIso T G.X f).hom ≫ fst T G.X).left.base p) = _
  rw [hfirstHom]

private theorem exists_common_first_coordinate_of_open_fibres
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    (hX : IsIrreducible (Set.univ : Set X)) (O : Set (X × Y))
    (hO : IsOpen O) (hfib : ∀ y : Y, ∃ x : X, (x, y) ∈ O) :
    ∃ V : TopologicalSpace.Opens X, (V : Set X).Nonempty ∧
      ∀ x ∈ V, ∀ y : Y, (x, y) ∈ O := by
  classical
  choose x hx using hfib
  choose V W hV hW hxV hyW hVW using fun y =>
    isOpen_prod_iff.mp hO (x y) y (hx y)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover W (fun y => hW y)
    (fun y _ => Set.mem_iUnion.mpr ⟨y, hyW y⟩)
  let I : Finset Y → Set X := fun s => {z | ∀ y ∈ s, z ∈ V y}
  have hInter : ∀ s : Finset Y, IsOpen (I s) ∧ (I s).Nonempty := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        obtain ⟨x0, hx0⟩ := hX.1
        have hI : I ∅ = Set.univ := by ext z; simp [I]
        exact ⟨hI ▸ isOpen_univ, ⟨x0, by simp [I]⟩⟩
    | @insert y s hys ih =>
        have hleft : (Set.univ ∩ V y).Nonempty := ⟨x y, by simp [hxV y]⟩
        have hright : (Set.univ ∩ I s).Nonempty := by
          obtain ⟨z, hz⟩ := ih.2
          exact ⟨z, by simp, hz⟩
        obtain ⟨z, _, hz⟩ := hX.2 (V y) (I s) (hV y) ih.1 hleft hright
        have heq : I (insert y s) = V y ∩ I s := by
          ext z
          simp [I, Finset.mem_insert]
        rw [heq]
        exact ⟨(hV y).inter ih.1, z, by simpa using hz⟩
  refine ⟨⟨I s, (hInter s).1⟩, (hInter s).2, ?_⟩
  intro z hz y
  obtain ⟨i, his, hiy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ y))
  exact hVW i ⟨hz i his, hiy⟩


private theorem exists_open_common_coordinate_on_compact_fibre
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (K : Set X) (hK : IrreducibleSpace {x : X // x ∈ K})
    (S : Set Y) (hS : IsCompact S)
    (O : Set (X × Y)) (hO : IsOpen O)
    (hfib : ∀ y ∈ S, ∃ x ∈ K, (x, y) ∈ O) :
    ∃ V : TopologicalSpace.Opens {x : X // x ∈ K},
      (V : Set {x : X // x ∈ K}).Nonempty ∧
      ∀ x ∈ V, ∀ y ∈ S, ((x : X), y) ∈ O := by
  classical
  let _inst : CompactSpace {y : Y // y ∈ S} := isCompact_iff_compactSpace.mp hS
  let pull : ({x : X // x ∈ K} × {y : Y // y ∈ S}) → X × Y :=
    fun p => (p.1.1, p.2.1)
  have hpull : Continuous pull :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  let O' : Set ({x : X // x ∈ K} × {y : Y // y ∈ S}) := pull ⁻¹' O
  have hO' : IsOpen O' := hO.preimage hpull
  have hfib' : ∀ y : {y : Y // y ∈ S},
      ∃ x : {x : X // x ∈ K}, (x, y) ∈ O' := by
    intro y
    obtain ⟨x, hxK, hxO⟩ := hfib y.1 y.2
    exact ⟨⟨x, hxK⟩, hxO⟩
  obtain ⟨V, hV, hVprop⟩ := exists_common_first_coordinate_of_open_fibres
    (IrreducibleSpace.isIrreducible_univ _) O' hO' hfib'
  exact ⟨V, hV, fun x hx y hy => hVprop x hx ⟨y, hy⟩⟩



private theorem graphTranslationIso_inv_snd {k : Type u} [Field k]
    (T G : Over (Spec (.of k))) [GrpObj G] (f : T ⟶ G) :
    (graphTranslationIso T G f).inv ≫ snd T G =
      (fst T G ≫ f)⁻¹ * snd T G := by
  dsimp [graphTranslationIso]
  rw [lift_snd]
  rfl

private theorem graphTranslationIso_hom_snd {k : Type u} [Field k]
    (T G : Over (Spec (.of k))) [GrpObj G] (f : T ⟶ G) :
    (graphTranslationIso T G f).hom ≫ snd T G = (fst T G ≫ f) * snd T G := by
  dsimp [graphTranslationIso]
  rw [lift_snd]
  rfl

private theorem exists_common_translate_fibre_on
    {k A : Type u} [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A]
    (hA : IsFilteredColimitOfFiniteProducts k A)
    (G : Grp (Over (Spec (.of k))))
    (f : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ G.X)
    (K : Set G.X.left) (hK : IrreducibleSpace {x : G.X.left // x ∈ K})
    (hKclosed : IsClosed K)
    (S : Set (PrimeSpectrum A)) (hS : IsCompact S)
    (hf : ∀ t ∈ S, f.left.base t ∈ K)
    [JacobsonSpace G.X.left]
    (hclosed : ∀ x : G.X.left, IsClosed ({x} : Set G.X.left) →
      ∃ p : Over.mk (𝟙 (Spec (.of k))) ⟶ G.X,
        p.left.base (⊥ : PrimeSpectrum k) = x)
    (U : G.X.left.Opens)
    (hU : (η[G.X]).left.base (⊥ : PrimeSpectrum k) ∈ U) :
    ∃ g₀ : G.X.left, g₀ ∈ K ∧
      (∃ p : Over.mk (𝟙 (Spec (.of k))) ⟶ G.X,
        p.left.base (⊥ : PrimeSpectrum k) = g₀) ∧
      ∀ t ∈ S, ∃ p : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⊗ G.X).left,
        ((snd (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))) G.X).left.base p ∈ U ∧
          translatedProductHomeo hA G f p = (g₀, t)) := by
  classical
  let T : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  let e := translatedProductHomeo hA G f
  let V := (snd T G.X).left.base ⁻¹' (U : Set G.X.left)
  let O := e '' V
  have hV : IsOpen V := U.2.preimage (snd T G.X).left.continuous
  have hO : IsOpen O := e.isOpenMap V hV
  let pull : ({x : G.X.left // x ∈ K} × {y : PrimeSpectrum A // y ∈ S}) →
      G.X.left × PrimeSpectrum A := fun p => (p.1.1, p.2.1)
  have hpull : Continuous pull := by
    exact Continuous.prodMk (continuous_subtype_val.comp continuous_fst)
      (continuous_subtype_val.comp continuous_snd)
  let O' : Set ({x : G.X.left // x ∈ K} × {y : PrimeSpectrum A // y ∈ S}) := pull ⁻¹' O
  have hO' : IsOpen O' := hO.preimage hpull
  let _inst : CompactSpace {y : PrimeSpectrum A // y ∈ S} := isCompact_iff_compactSpace.mp hS
  have hfib : ∀ t : {y : PrimeSpectrum A // y ∈ S},
      ∃ x : {x : G.X.left // x ∈ K}, (x, t) ∈ O' := by
    intro t
    let s : T ⟶ T ⊗ G.X := lift (𝟙 T) (toUnit T ≫ η[G.X])
    let p := s.left.base t.1
    have hsnd : s ≫ snd T G.X = toUnit T ≫ (MonObj.one : 𝟙_ _ ⟶ G.X) := by
      simp [s]
    have hfst : s ≫ fst T G.X = 𝟙 T := by simp [s]
    have htranslated : s ≫ (graphTranslationIso T G.X f).hom ≫ snd T G.X = f := by
      rw [graphTranslationIso_hom_snd, MonObj.comp_mul]
      rw [← Category.assoc, hfst, Category.id_comp]
      rw [hsnd]
      simp [Hom.one_def]
    have hpV : p ∈ V := by
      change (snd T G.X).left.base p ∈ U
      have hpunit : (snd T G.X).left.base p = (η[G.X]).left.base (⊥ : PrimeSpectrum k) := by
        have htbase := toUnit_left_base_eq_bot T t.1
        change (s ≫ snd T G.X).left.base t.1 = _
        rw [hsnd]
        change (η[G.X]).left.base ((toUnit T).left.base t.1) = _
        rw [htbase]
      rw [hpunit]
      exact hU
    have hfirst : (translatedProductHomeo hA G f p).1 = f.left.base t.1 := by
      rw [translatedProductHomeo_fst]
      change (s ≫ (graphTranslationIso T G.X f).hom ≫ snd T G.X).left.base t.1 = _
      rw [htranslated]
    have hsecond : (translatedProductHomeo hA G f p).2 = t.1 := by
      rw [translatedProductHomeo_snd]
      change (s ≫ fst T G.X).left.base t.1 = _
      rw [hfst]
      rfl
    refine ⟨⟨f.left.base t.1, hf t.1 t.2⟩, ?_⟩
    change ((f.left.base t.1, t.1) ∈ O)
    refine ⟨p, hpV, ?_⟩
    exact Prod.ext hfirst hsecond
  obtain ⟨V₀, hV₀, hVfiber⟩ :=
    exists_open_common_coordinate_on_compact_fibre K hK S hS O hO
      (by
        intro t ht
        obtain ⟨x, hx⟩ := hfib ⟨t, ht⟩
        change (x.1, t) ∈ O at hx
        exact ⟨x.1, x.2, hx⟩)
  let _inst : JacobsonSpace {x : G.X.left // x ∈ K} :=
    JacobsonSpace.of_isClosedEmbedding hKclosed.isClosedEmbedding_subtypeVal
  obtain ⟨x, hxV, hxc⟩ := nonempty_inter_closedPoints hV₀ V₀.2.isLocallyClosed
  have hxAmbientClosed : IsClosed ({(x : G.X.left)} : Set G.X.left) := by
    have h := hKclosed.isClosedEmbedding_subtypeVal.isClosedMap
      ({x} : Set {y : G.X.left // y ∈ K}) (mem_closedPoints_iff.mp hxc)
    simpa using h
  obtain ⟨p₀, hp₀⟩ := hclosed x.1 hxAmbientClosed
  refine ⟨x.1, x.2, ?_, ?_⟩
  · exact ⟨p₀, hp₀⟩
  · intro t ht
    obtain ⟨q, hqV, hqe⟩ := hVfiber x hxV t ht
    exact ⟨q, hqV, hqe⟩

private theorem graphTranslationIso_fst {k : Type u} [Field k]
    (T G : Over (Spec (.of k))) [GrpObj G] (f : T ⟶ G) :
    (graphTranslationIso T G f).hom ≫ fst T G = fst T G := by
  apply Over.OverMorphism.ext
  simp [graphTranslationIso]

private theorem exists_affineOpen_range_subset_of_irreducible
    {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    (G : Grp (Over (Spec (CommRingCat.of k))))
    [JacobsonSpace G.X.left]
    (hclosed : ∀ x : G.X.left, IsClosed ({x} : Set G.X.left) →
      ∃ p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        p.left.base (⊥ : PrimeSpectrum k) = x)
    (hA : IsFilteredColimitOfFiniteProducts k A)
    (f : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ G.X)
    (K : Set G.X.left) (hK : IrreducibleSpace {x : G.X.left // x ∈ K})
    (hKclosed : IsClosed K) (S : Set (PrimeSpectrum A)) (hS : IsCompact S)
    (hf : ∀ t ∈ S, f.left.base t ∈ K)
    (U : G.X.left.Opens) (hU : IsAffineOpen U)
    (heU : (η[G.X]).left.base (⊥ : PrimeSpectrum k) ∈ U) :
    ∃ g₀ : G.X.left, g₀ ∈ K ∧
      (∃ p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        p.left.base (⊥ : PrimeSpectrum k) = g₀ ∧
        ∃ V : G.X.left.Opens, IsAffineOpen V ∧
          V = ((rationalLeftTranslationIso G p).symm.hom.left ⁻¹ᵁ
            ((groupInverseIso G).hom.left ⁻¹ᵁ U)) ∧
          ∀ t ∈ S, f.left.base t ∈ V) := by
  classical
  let T : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  obtain ⟨g₀, hg₀K, ⟨p, hp⟩, hVfiber⟩ := exists_common_translate_fibre_on
    hA G f K hK hKclosed S hS hf hclosed U heU
  let c : T ⟶ G.X := toUnit T ≫ p
  let s : T ⟶ T ⊗ G.X := lift (𝟙 T) c
  let q : T ⟶ G.X := s ≫ (graphTranslationIso T G.X f).inv ≫ snd T G.X
  let qInv : T ⟶ G.X := q ≫ GrpObj.inv
  let eInv := groupInverseIso G
  let L := rationalLeftTranslationIso G p
  let UInv : G.X.left.Opens := (eInv.hom.left) ⁻¹ᵁ U
  let W : G.X.left.Opens := (L.symm.hom.left) ⁻¹ᵁ UInv
  have := isIso_hom_left eInv
  have := isIso_hom_left L.symm
  have hUInv : IsAffineOpen UInv := hU.preimage_of_isIso eInv.hom.left
  have hW : IsAffineOpen W := hUInv.preimage_of_isIso L.symm.hom.left
  have hsnd : s ≫ snd T G.X = c := by simp [s]
  have hfst : s ≫ fst T G.X = 𝟙 T := by simp [s]
  have hq : q = f⁻¹ * c := by
    dsimp [q]
    rw [graphTranslationIso_inv_snd, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, hfst,
      Category.id_comp, hsnd]
  have hfactor : f = c * q⁻¹ := by
    rw [hq]
    group
  have hleft : qInv ≫ L.hom = c * qInv := comp_rationalLeftTranslationIso_hom G p qInv
  have hqU : ∀ t : T.left, t ∈ S → q.left.base t ∈ U := by
    intro t ht
    obtain ⟨z, hzU, hze⟩ := hVfiber t ht
    let pz : (T ⊗ G.X).left := z
    have hfirst : (snd T G.X).left.base
        ((graphTranslationIso T G.X f).hom.left.base pz) = g₀ := by
      have h := translatedProductHomeo_fst hA G f pz
      rw [hze] at h
      simpa [T] using h.symm
    have hsecondInput : (fst T G.X).left.base pz = t := by
      have h := translatedProductHomeo_snd hA G f pz
      rw [hze] at h
      exact h.symm
    have hsecond : (fst T G.X).left.base
        ((graphTranslationIso T G.X f).hom.left.base pz) = t := by
      have hfstHom : (graphTranslationIso T G.X f).hom ≫ fst T G.X = fst T G.X := by
        exact graphTranslationIso_fst T G.X f
      calc
        _ = (fst T G.X).left.base pz := by
          change (((graphTranslationIso T G.X f).hom ≫ fst T G.X).left.base pz) = _
          rw [hfstHom]
        _ = t := hsecondInput
    have hgpoint : c.left.base t = g₀ := by
      change (toUnit T ≫ p).left.base t = g₀
      change p.left.base ((toUnit T).left.base t) = g₀
      rw [toUnit_left_base_eq_bot T t, hp]
    have hfirstS : (fst T G.X).left.base (s.left.base t) = t := by
      change (s ≫ fst T G.X).left.base t = t
      rw [hfst]
      rfl
    have hsecondS : (snd T G.X).left.base (s.left.base t) = g₀ := by
      change (s ≫ snd T G.X).left.base t = g₀
      rw [hsnd]
      exact hgpoint
    have hpair :
        ((fst T G.X).left.base ((graphTranslationIso T G.X f).hom.left.base pz),
          (snd T G.X).left.base ((graphTranslationIso T G.X f).hom.left.base pz)) =
        ((fst T G.X).left.base (s.left.base t), (snd T G.X).left.base (s.left.base t)) := by
      exact Prod.ext (hsecond.trans hfirstS.symm) (hfirst.trans hsecondS.symm)
    have heq : (graphTranslationIso T G.X f).hom.left.base pz = s.left.base t :=
      (specProduct_isHomeomorph hA G).injective hpair
    have hpz : pz = (graphTranslationIso T G.X f).inv.left.base (s.left.base t) := by
      rw [← heq]
      exact (over_comp_left_base_apply (graphTranslationIso T G.X f).hom_inv_id pz).symm
    change (snd T G.X).left.base
      ((graphTranslationIso T G.X f).inv.left.base (s.left.base t)) ∈ U
    rw [← hpz]
    simpa [T, pz] using hzU
  have hqInvU : ∀ t : T.left, t ∈ S → qInv.left.base t ∈ UInv := by
    intro t ht
    change eInv.hom.left.base (qInv.left.base t) ∈ U
    have hdouble : qInv ≫ eInv.hom = q := by
      dsimp [qInv, eInv, groupInverseIso]
      simp
    rw [over_comp_left_base_apply hdouble]
    exact hqU t ht
  refine ⟨g₀, hg₀K, ⟨p, hp, W, hW, ?_, ?_⟩⟩
  · rfl
  · intro t ht
    change (L.symm.hom.left.base (f.left.base t)) ∈ UInv
    have hfpoint : f.left.base t = L.hom.left.base (qInv.left.base t) := by
      have hmap : f = qInv ≫ L.hom := by
        calc
          f = c * q⁻¹ := hfactor
          _ = c * qInv := by rfl
          _ = qInv ≫ L.hom := hleft.symm
      rw [hmap]
      rfl
    rw [hfpoint]
    rw [show L.symm.hom.left.base (L.hom.left.base (qInv.left.base t)) = qInv.left.base t from
      over_comp_left_base_apply L.hom_inv_id _]
    exact hqInvU t ht

private theorem exists_affineOpen_subset_saturation_for_component_fibre
    {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    (G : Grp (Over (Spec (CommRingCat.of k))))
    [JacobsonSpace G.X.left]
    (hclosed : ∀ x : G.X.left, IsClosed ({x} : Set G.X.left) →
      ∃ p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        p.left.base (⊥ : PrimeSpectrum k) = x)
    (hA : IsFilteredColimitOfFiniteProducts k A)
    (f : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ G.X)
    (U₀ : G.X.left.Opens) (hU₀compact : IsCompact (U₀ : Set G.X.left))
    (S : Set (PrimeSpectrum A)) (hS : IsCompact S)
    (y : G.X.left)
    (hy : y ∈ Set.image
      (lift (fst (identityComponent k G).carrier.X G.X ≫
        (identityComponent k G).ι.hom.hom)
        (snd (identityComponent k G).carrier.X G.X) ≫ μ[G.X]).left.base
      ((snd (identityComponent k G).carrier.X G.X).left.base ⁻¹'
        (U₀ : Set G.X.left)))
    (hf : ∀ t ∈ S, f.left.base t ∈ connectedComponent y) :
    ∃ V : G.X.left.Opens, IsAffineOpen V ∧
      (V : Set G.X.left) ⊆ Set.image
        (lift (fst (identityComponent k G).carrier.X G.X ≫
          (identityComponent k G).ι.hom.hom)
          (snd (identityComponent k G).carrier.X G.X) ≫ μ[G.X]).left.base
        ((snd (identityComponent k G).carrier.X G.X).left.base ⁻¹'
          (U₀ : Set G.X.left)) ∧
      ∀ t ∈ S, f.left.base t ∈ V := by
  classical
  let H := identityComponent k G
  let T := H.carrier.X
  let ψ := H.ι.hom.hom
  let m := lift (fst T G.X ≫ ψ) (snd T G.X) ≫ μ[G.X]
  let sat := Set.image m.left.base ((snd T G.X).left.base ⁻¹' (U₀ : Set G.X.left))
  have hsatOpen : IsOpen sat := isOpen_image_mul_of_open G.X T ψ U₀
  let K := connectedComponent y
  have hKclosed : IsClosed K := isClosed_connectedComponent
  have hKS : IsLocallyClosed (K ∩ sat) := hKclosed.isLocallyClosed.inter hsatOpen.isLocallyClosed
  have hKSne : (K ∩ sat).Nonempty := ⟨y, mem_connectedComponent, hy⟩
  obtain ⟨x, hxKS, hxc⟩ := nonempty_inter_closedPoints hKSne hKS
  obtain ⟨z, hz⟩ := hclosed x (mem_closedPoints_iff.mp hxc)
  have hzK : z.left.base (⊥ : PrimeSpectrum k) ∈ K := hz ▸ hxKS.1
  have hzsat : z.left.base (⊥ : PrimeSpectrum k) ∈ sat := hz ▸ hxKS.2
  have hKsubset : K ⊆ sat := by
    have hKz : K = connectedComponent (z.left.base (⊥ : PrimeSpectrum k)) :=
      connectedComponent_eq hzK
    rw [hKz]
    exact leftIdentityComponent_saturation_contains_connectedComponent
      G hclosed U₀ hU₀compact z hzsat
  have hyz : y ∈ connectedComponent (z.left.base (⊥ : PrimeSpectrum k)) := by
    rw [← connectedComponent_eq hzK]
    exact mem_connectedComponent
  let R := rightTranslationIso G (z ≫ GrpObj.inv)
  let τ := rightTranslationHomeo G (z ≫ GrpObj.inv)
  have hτz : τ (z.left.base (⊥ : PrimeSpectrum k)) =
      identityPoint k G :=
    rightTranslationHomeo_apply_self G z
  have hτK : τ '' K = connectedComponent (identityPoint k G) := by
    rw [show K = connectedComponent (z.left.base (⊥ : PrimeSpectrum k)) from
      connectedComponent_eq hzK]
    rw [Homeomorph.image_connectedComponent, hτz]
  let f' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ G.X := f ≫ R.hom
  have hf' : ∀ t ∈ S, f'.left.base t ∈
      connectedComponent (identityPoint k G) := by
    intro t ht
    change τ (f.left.base t) ∈ connectedComponent (identityPoint k G)
    rw [← hτK]
    exact Set.mem_image_of_mem τ (hf t ht)
  have := isIso_hom_left R
  let Wcomp : G.X.left.Opens :=
    ⟨R.hom.left.base '' sat, R.hom.left.homeomorph.isOpenMap _ hsatOpen⟩
  have heWcomp : (identityPoint k G) ∈ Wcomp := by
    have hτR : τ (z.left.base (⊥ : PrimeSpectrum k)) =
        R.hom.left.base (z.left.base (⊥ : PrimeSpectrum k)) := rfl
    have hEq : R.hom.left.base (z.left.base (⊥ : PrimeSpectrum k)) =
        identityPoint k G := hτR.symm.trans hτz
    rw [← hEq]
    exact ⟨z.left.base (⊥ : PrimeSpectrum k), hzsat, rfl⟩
  let eInv := groupInverseIso G
  let O : G.X.left.Opens := (eInv.hom.left) ⁻¹ᵁ Wcomp
  have heO : (identityPoint k G) ∈ O := by
    change eInv.hom.left.base (identityPoint k G) ∈ Wcomp
    have hInv : eInv.hom.left.base (identityPoint k G) =
        identityPoint k G := by
      have hUnit : (η[G.X] ≫ GrpObj.inv) = η[G.X] := by simp
      exact over_comp_left_base_apply hUnit (⊥ : PrimeSpectrum k)
    rw [hInv]
    exact heWcomp
  obtain ⟨U, hU, heU, hUO⟩ := exists_isAffineOpen_mem_and_subset
    (X := G.X.left) (x := identityPoint k G) (U := O) heO
  let UInv : G.X.left.Opens := (eInv.hom.left) ⁻¹ᵁ U
  have := isIso_hom_left eInv
  have hUInv : IsAffineOpen UInv := hU.preimage_of_isIso eInv.hom.left
  have hUInvsub : (UInv : Set G.X.left) ⊆ (Wcomp : Set G.X.left) := by
    intro a ha
    change eInv.hom.left.base a ∈ U at ha
    have haO : eInv.hom.left.base a ∈ O := hUO ha
    change eInv.hom.left.base (eInv.hom.left.base a) ∈ Wcomp at haO
    have hdouble : eInv.hom.left.base (eInv.hom.left.base a) = a :=
      over_comp_left_base_apply eInv.hom_inv_id a
    rw [hdouble] at haO
    exact haO
  obtain ⟨g₀, hg₀H, ⟨p₀, hp₀, V, hV, hVeq, hVf⟩⟩ :=
    exists_affineOpen_range_subset_of_irreducible G hclosed hA f'
      (connectedComponent (identityPoint k G))
      (identityComponent_connectedComponent_irreducible G)
      isClosed_connectedComponent S hS hf' U hU heU
  have hp₀id : p₀.left.base (⊥ : PrimeSpectrum k) ∈
      connectedComponent (identityPoint k G) := by
    rw [hp₀]
    exact hg₀H
  obtain ⟨pH, hpH⟩ := lift_rational_point_through_identityComponent G p₀ hp₀id
  have hVsubsetWcomp : (V : Set G.X.left) ⊆ Wcomp := by
    intro a ha
    have haUInv : (rationalLeftTranslationIso G p₀).symm.hom.left.base a ∈ UInv := by
      rw [hVeq] at ha
      exact ha
    have haWcomp : (rationalLeftTranslationIso G p₀).symm.hom.left.base a ∈ Wcomp :=
      hUInvsub haUInv
    have hstable := translated_leftIdentityComponent_saturation_stable_under_rational_left
      G U₀ z pH ((rationalLeftTranslationIso G p₀).symm.hom.left.base a) haWcomp
    have hstable' : (rationalLeftTranslationIso G p₀).hom.left.base
        ((rationalLeftTranslationIso G p₀).symm.hom.left.base a) ∈ Wcomp := by
      change _ ∈ Set.image R.hom.left.base sat
      simpa only [hpH] using hstable
    have hcancel : (rationalLeftTranslationIso G p₀).hom.left.base
        ((rationalLeftTranslationIso G p₀).symm.hom.left.base a) = a :=
      over_comp_left_base_apply (rationalLeftTranslationIso G p₀).inv_hom_id a
    rw [hcancel] at hstable'
    exact hstable'
  let Vback : G.X.left.Opens := R.hom.left ⁻¹ᵁ V
  have hVback : IsAffineOpen Vback := hV.preimage_of_isIso R.hom.left
  have hVbacksub : (Vback : Set G.X.left) ⊆ sat := by
    intro a ha
    change τ a ∈ V at ha
    have haWcomp : τ a ∈ Wcomp := hVsubsetWcomp ha
    rcases haWcomp with ⟨b, hb, hba⟩
    have hab : b = a := τ.injective hba
    simpa only [hab] using hb
  refine ⟨Vback, hVback, ?_, ?_⟩
  · simpa only [sat, m, ψ, T, H] using hVbacksub
  · exact hVf



private theorem spectralSpace_of_compact_open_scheme
    (X : Scheme.{u}) [QuasiSeparatedSpace X] (W : X.Opens)
    (hW : IsCompact (W : Set X)) : SpectralSpace W := by
  let _inst : CompactSpace W := isCompact_iff_compactSpace.mp hW
  let h := W.2.isOpenEmbedding_subtypeVal
  exact { toT0Space := h.isEmbedding.t0Space
          toQuasiSober := h.quasiSober
          toQuasiSeparatedSpace := h.quasiSeparatedSpace
          toPrespectralSpace := h.prespectralSpace }


private theorem affineOpen_inf_clopen
    (X : Scheme.{u}) (U V : X.Opens) (hU : IsAffineOpen U)
    (hV : IsClopen (V : Set X)) : IsAffineOpen (U ⊓ V) := by
  classical
  let U' : U.toScheme.Opens := U.ι ⁻¹ᵁ V
  have hU'cl : IsClopen (U' : Set U.toScheme) :=
    ⟨hV.isClosed.preimage U.ι.continuous, hV.isOpen.preimage U.ι.continuous⟩
  let e := hU.isoSpec
  let eTop := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)
  let Dset : Set (PrimeSpectrum Γ(X, U)) := eTop '' (U' : Set U.toScheme)
  have hDcl : IsClopen Dset :=
    ⟨eTop.isClosedMap _ hU'cl.isClosed, eTop.isOpenMap _ hU'cl.isOpen⟩
  obtain ⟨r, hr, hD⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hDcl
  let B : (Spec Γ(X, U)).Opens := PrimeSpectrum.basicOpen r
  have hpre : e.hom ⁻¹ᵁ B = U' := by
    ext x
    change eTop x ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum Γ(X, U))) ↔
      x ∈ (U' : Set U.toScheme)
    rw [← hD]
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := hx
      exact eTop.injective hxy ▸ hy
    · exact Set.mem_image_of_mem eTop
  have hB : IsAffineOpen B := IsAffineOpen.Spec_basicOpen r
  have hU'affine : IsAffineOpen U' := by
    simpa [hpre] using hB.preimage_of_isIso e.hom
  have hEq : U.ι ''ᵁ U' = U ⊓ V := by
    rw [U.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  rw [← hEq]
  exact U.ι.isAffineOpen_iff_of_isOpenImmersion.mpr hU'affine

private theorem exists_affineOpen_cover_from_component_fibres
    (X : Scheme.{u}) {T Q : Type u} [TopologicalSpace T] [CompactSpace T]
    [TopologicalSpace Q] [TotallyDisconnectedSpace Q] [T2Space Q] [CompactSpace Q]
    (f : T → X) (hf : Continuous f) (π : X → Q) (hπ : Continuous π)
    (ψ : T → Q) (hψ : Continuous ψ) (hfac : ∀ t, π (f t) = ψ t)
    (U : Q → X.Opens)
    (hfiber : ∀ q t, ψ t = q → f t ∈ U q)
    (hpiece : ∀ q (D : Clopens Q), IsAffineOpen
      (U q ⊓ ⟨π ⁻¹' (D : Set Q), (D.2.isOpen).preimage hπ⟩)) :
    ∃ V : X.Opens, IsAffineOpen V ∧ Set.range f ⊆ (V : Set X) := by
  classical
  let cover : Q → Opens Q := fun q =>
    ⟨(Set.image ψ {t | f t ∉ U q})ᶜ, by
      have hbad : IsClosed {t | f t ∉ U q} := (U q).2.isClosed_compl.preimage hf
      have hcompact : IsCompact (Set.image ψ {t | f t ∉ U q}) :=
        hbad.isCompact.image hψ
      exact hcompact.isClosed.isOpen_compl⟩
  have hcover : IsOpenCover cover := by
    apply TopologicalSpace.IsOpenCover.of_sets (fun q => (cover q).2)
    ext q
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    refine ⟨q, ?_⟩
    change q ∉ Set.image ψ {t | f t ∉ U q}
    rintro ⟨t, ht, hqt⟩
    exact ht (hfiber q t hqt)
  obtain ⟨n, D, hDref₀, hDcover, hDdisj⟩ :=
    hcover.exists_finite_nonempty_disjoint_clopen_cover
  have hDref : ∀ j, ∃ i, (D j : Set Q) ⊆ (cover i : Set Q) := fun j => (hDref₀ j).2
  choose index hindex using hDref
  let V (j : Fin n) : X.Opens :=
    U (index j) ⊓ ⟨π ⁻¹' (D j : Set Q), (D j).2.isOpen.preimage hπ⟩
  have hVaff (j : Fin n) : IsAffineOpen (V j) := hpiece (index j) (D j)
  have hVdisj : Pairwise fun i j => Disjoint (V i) (V j) := by
    intro i j hij
    rw [← Opens.coe_disjoint]
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hDi : π x ∈ (D i : Set Q) := hxi.2
    have hDj : π x ∈ (D j : Set Q) := hxj.2
    have hmeet : D i ⊓ D j = ⊥ := disjoint_iff.mp (hDdisj hij)
    have hmem : π x ∈ (D i ⊓ D j : Clopens Q) := ⟨hDi, hDj⟩
    rw [hmeet] at hmem
    exact hmem
  let Vall : X.Opens := ⨆ j, V j
  have hVall : IsAffineOpen Vall := IsAffineOpen.iSup_of_disjoint hVaff hVdisj
  refine ⟨Vall, hVall, ?_⟩
  rintro _ ⟨t, rfl⟩
  have hψmem : ψ t ∈ ⋃ j, (D j : Set Q) := hDcover (Set.mem_univ _)
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hψmem
  have hsmall : ψ t ∈ (cover (index j) : Set Q) := hindex j hj
  have hfU : f t ∈ U (index j) := by
    change ψ t ∉ Set.image ψ {t' | f t' ∉ U (index j)} at hsmall
    by_contra hnot
    exact hsmall ⟨t, hnot, rfl⟩
  have hfD : π (f t) ∈ (D j : Set Q) := by
    rwa [hfac]
  exact le_iSup V j ⟨hfU, hfD⟩

private theorem exists_affineOpen_range_subset_of_open_component_fibres
    (X : Scheme.{u}) (W : X.Opens) {T Q : Type u}
    [TopologicalSpace T] [CompactSpace T]
    [TopologicalSpace Q] [TotallyDisconnectedSpace Q] [T2Space Q] [CompactSpace Q]
    (f : T → ↥W.toScheme) (hf : Continuous f)
    (π : ↥W.toScheme → Q) (hπ : Continuous π)
    (ψ : T → Q) (hψ : Continuous ψ) (hfac : ∀ t, π (f t) = ψ t)
    (U : Q → W.toScheme.Opens) (hU : ∀ q, IsAffineOpen (U q))
    (hfiber : ∀ q t, ψ t = q → f t ∈ U q) :
    ∃ V : X.Opens, IsAffineOpen V ∧ Set.range (fun t => W.ι.base (f t)) ⊆ V := by
  have hpiece : ∀ q (D : Clopens Q), IsAffineOpen
      (U q ⊓ ⟨π ⁻¹' (D : Set Q), D.2.isOpen.preimage hπ⟩) := fun q D =>
    affineOpen_inf_clopen W.toScheme (U q) _ (hU q)
      ⟨D.2.isClosed.preimage hπ, D.2.isOpen.preimage hπ⟩
  obtain ⟨V, hV, hVf⟩ := exists_affineOpen_cover_from_component_fibres
    W.toScheme f hf π hπ ψ hψ hfac U hfiber hpiece
  refine ⟨W.ι ''ᵁ V, ?_, ?_⟩
  · exact W.ι.isAffineOpen_iff_of_isOpenImmersion.mpr hV
  · rintro _ ⟨t, rfl⟩
    exact Set.mem_image_of_mem _ (hVf ⟨t, rfl⟩)

private theorem exists_compactOpen_covering_compact_subset
    (X : Scheme.{u}) (K : Set X) (hK : IsCompact K) :
    ∃ W : X.Opens, IsCompact (W : Set X) ∧ K ⊆ W := by
  classical
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun i => (X.affineCover.f i).opensRange)
    (fun i => (X.affineCover.f i).isOpenEmbedding.isOpen_range)
    (by
      intro x hx
      obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
      exact Set.mem_iUnion.mpr ⟨i, ⟨y, rfl⟩⟩)
  let W : X.Opens := ⨆ i ∈ s, (X.affineCover.f i).opensRange
  refine ⟨W, ?_, ?_⟩
  · rw [show (W : Set X) = ⋃ i ∈ s, ((X.affineCover.f i).opensRange : Set X) by
      simp [W]]
    exact s.isCompact_biUnion fun i _ => (isAffineOpen_opensRange (X.affineCover.f i)).isCompact
  · intro x hx
    simpa [W] using hs hx

@[sga "3 VIA 2.6.4" "(i), special case", sga "3 VIB 5.6.2.0" "(iii)(a)"]
private theorem leftIdentityComponent_saturation_isOpen_isCompact
    {k : Type u} [Field k] (G : Grp (Over (Spec (CommRingCat.of k))))
    (U : G.X.left.Opens) (hU : IsCompact (U : Set G.X.left)) :
    IsOpen (Set.image
      (lift (fst (identityComponent k G).carrier.X G.X ≫
        (identityComponent k G).ι.hom.hom)
        (snd (identityComponent k G).carrier.X G.X) ≫ μ[G.X]).left.base
      ((snd (identityComponent k G).carrier.X G.X).left.base ⁻¹'
        (U : Set G.X.left))) ∧
    IsCompact (Set.image
      (lift (fst (identityComponent k G).carrier.X G.X ≫
        (identityComponent k G).ι.hom.hom)
        (snd (identityComponent k G).carrier.X G.X) ≫ μ[G.X]).left.base
      ((snd (identityComponent k G).carrier.X G.X).left.base ⁻¹'
        (U : Set G.X.left))) := by
  let H := identityComponent k G
  let T := H.carrier.X
  let ψ : T ⟶ G.X := H.ι.hom.hom
  let m := lift (fst T G.X ≫ ψ) (snd T G.X) ≫ μ[G.X]
  let V := (snd T G.X).left.base ⁻¹' (U : Set G.X.left)
  let P := Set.image m.left.base V
  have hPopen : IsOpen P := isOpen_image_mul_of_open G.X T ψ U
  let _inst : CompactSpace T.left := identityComponent_compactSpace k G
  let _inst : QuasiCompact T.hom :=
    (AlgebraicGeometry.quasiCompact_iff_compactSpace T.hom).2 inferInstance
  let _inst : QuasiCompact (pullback.snd T.hom G.X.hom) := by infer_instance
  have hVcompact : IsCompact V := by
    change IsCompact ((pullback.snd T.hom G.X.hom).base ⁻¹' (U : Set G.X.left))
    exact QuasiCompact.isCompact_preimage (f := pullback.snd T.hom G.X.hom)
      (U : Set G.X.left) U.2 hU
  have hPcompact : IsCompact P := hVcompact.image m.left.continuous
  exact ⟨by simpa [P, V, m, ψ, T, H] using hPopen,
    by simpa [P, V, m, ψ, T, H] using hPcompact⟩


/-- **Stacks Project, Tag 0B7U.** The image in a Jacobson group scheme of the spectrum of a
filtered colimit of finite products of the algebraically closed ground field is contained in an
affine open, provided every closed point of the group scheme is rational over the ground field. -/
@[stacks 0B7U]
theorem exists_affineOpen_range_subset
    (k A : Type u) [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    (G : Grp (Over (Spec (CommRingCat.of k))))
    [JacobsonSpace G.X.left]
    (hclosed : ∀ x : G.X.left, IsClosed ({x} : Set G.X.left) →
      ∃ p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        p.left.base (⊥ : PrimeSpectrum k) = x)
    (hA : IsFilteredColimitOfFiniteProducts k A)
    (f : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ G.X) :
    ∃ U : G.X.left.Opens, IsAffineOpen U ∧ Set.range f.left.base ⊆ U := by
  classical
  let _inst : CompactSpace (Over.mk (Spec.map
      (CommRingCat.ofHom (algebraMap k A)))).left := by
    change CompactSpace (PrimeSpectrum A)
    infer_instance
  let e := identityPoint k G
  let K₀ : Set G.X.left := Set.range f.left.base ∪ {e}
  have hK₀compact : IsCompact K₀ :=
    (isCompact_range f.left.continuous).union isCompact_singleton
  obtain ⟨U₀, hU₀compact, hK₀U₀⟩ :=
    exists_compactOpen_covering_compact_subset G.X.left K₀ hK₀compact
  have hfU₀ : ∀ t : PrimeSpectrum A, f.left.base t ∈ U₀ := fun t =>
    hK₀U₀ (Set.mem_union_left _ ⟨t, rfl⟩)
  have heU₀ : e ∈ U₀ := hK₀U₀ (Set.mem_union_right _ (Set.mem_singleton _))
  let H := identityComponent k G
  let T := H.carrier.X
  let ψ := H.ι.hom.hom
  let m := lift (fst T G.X ≫ ψ) (snd T G.X) ≫ μ[G.X]
  let sat := Set.image m.left.base ((snd T G.X).left.base ⁻¹' (U₀ : Set G.X.left))
  obtain ⟨hsatOpen, hsatCompact⟩ :=
    leftIdentityComponent_saturation_isOpen_isCompact G U₀ hU₀compact
  let W : G.X.left.Opens := ⟨sat, hsatOpen⟩
  let s : G.X ⟶ T ⊗ G.X :=
    lift (toUnit G.X ≫ (MonObj.one : 𝟙_ _ ⟶ T)) (𝟙 G.X)
  have hsnd : s ≫ snd T G.X = 𝟙 G.X := by simp [s]
  have hfst : s ≫ fst T G.X = toUnit G.X ≫ (MonObj.one : 𝟙_ _ ⟶ T) := by simp [s]
  have hsm : s ≫ m = 𝟙 G.X := by
    change s ≫ ((fst T G.X ≫ ψ) * snd T G.X) = _
    rw [MonObj.comp_mul]
    change ((s ≫ fst T G.X) ≫ ψ) * (s ≫ snd T G.X) = _
    rw [show s ≫ fst T G.X = (1 : G.X ⟶ T) by simpa [Hom.one_def] using hfst,
      hsnd]
    rw [MonObj.one_comp]
    simp
  have hsmPoint : ∀ x : G.X.left, m.left.base (s.left.base x) = x :=
    over_comp_left_base_apply hsm
  have hsndPoint : ∀ x : G.X.left, (snd T G.X).left.base (s.left.base x) = x :=
    over_comp_left_base_apply hsnd
  have hfSat : ∀ t : PrimeSpectrum A, f.left.base t ∈ sat := by
    intro t
    refine ⟨s.left.base (f.left.base t), ?_, hsmPoint (f.left.base t)⟩
    change (snd T G.X).left.base (s.left.base (f.left.base t)) ∈ U₀
    rw [hsndPoint]
    exact hfU₀ t
  have eSat : e ∈ sat := by
    refine ⟨s.left.base e, ?_, hsmPoint e⟩
    change (snd T G.X).left.base (s.left.base e) ∈ U₀
    rw [hsndPoint]
    exact heU₀
  have hfW : Set.range f.left.base ⊆ (W : Set G.X.left) := by
    rintro _ ⟨t, rfl⟩
    exact hfSat t
  let fW : PrimeSpectrum A → ↥W.toScheme := fun t =>
    ⟨f.left.base t, hfW ⟨t, rfl⟩⟩
  have hfWcont : Continuous fW := Continuous.subtype_mk f.left.continuous
    (fun t => hfW ⟨t, rfl⟩)
  let Q := ConnectedComponents W.toScheme
  let π : ↥W.toScheme → Q := fun x => ConnectedComponents.mk x
  let χ : PrimeSpectrum A → Q := fun t => π (fW t)
  have hχ : Continuous χ := ConnectedComponents.continuous_coe.comp hfWcont
  let _inst : QuasiSeparatedSpace G.X.left := by
    let _inst : G.X.left.IsSeparated := isSeparated_of_groupScheme_over_field G
    exact (inferInstance : QuasiSeparatedSpace G.X.left)
  let _inst : SpectralSpace W.toScheme :=
    spectralSpace_of_compact_open_scheme G.X.left W hsatCompact
  have hprofinite := connectedComponents_isProfinite W.toScheme
  let _inst : CompactSpace Q := hprofinite.2.1
  let _inst : T2Space Q := hprofinite.1
  let _inst : TotallyDisconnectedSpace Q := hprofinite.2.2
  have hUq : ∀ q : Q, ∃ V : W.toScheme.Opens, IsAffineOpen V ∧
      ∀ t, χ t = q → fW t ∈ V := by
    intro q
    classical
    by_cases hhit : ∃ t, χ t = q
    · obtain ⟨t₀, ht₀⟩ := hhit
      let S : Set (PrimeSpectrum A) := χ ⁻¹' {q}
      have hScompact : IsCompact S := (isClosed_singleton.preimage hχ).isCompact
      let y : G.X.left := f.left.base t₀
      have hy : y ∈ sat := hfSat t₀
      have hfcomp : ∀ t ∈ S, f.left.base t ∈ connectedComponent y := by
        intro t ht
        have htχ : χ t = χ t₀ := by
          change χ t = q at ht
          rw [ht, ht₀]
        have hcompW : connectedComponent (fW t) = connectedComponent (fW t₀) :=
          ConnectedComponents.coe_eq_coe.mp htχ
        have htcompW : fW t ∈ connectedComponent (fW t₀) := by
          rw [← hcompW]
          exact mem_connectedComponent
        have hvalcont : Continuous (fun x : ↥W.toScheme => W.ι.base x) :=
          W.ι.continuous
        have himage := hvalcont.image_connectedComponent_subset (fW t₀)
        have him : W.ι.base (fW t) ∈
            Set.image (fun x : ↥W.toScheme => W.ι.base x)
              (connectedComponent (fW t₀)) := Set.mem_image_of_mem _ htcompW
        exact himage him
      obtain ⟨V, hV, hVsubset, hVfibre⟩ :=
        exists_affineOpen_subset_saturation_for_component_fibre G hclosed hA f
          U₀ hU₀compact S hScompact y hy hfcomp
      let Vw : W.toScheme.Opens := W.ι ⁻¹ᵁ V
      have hVle : V ≤ W := hVsubset
      have hVrange : V ≤ W.ι.opensRange := by
        simpa only [Scheme.Opens.opensRange_ι] using hVle
      have hVw : IsAffineOpen Vw := hV.preimage_of_isOpenImmersion W.ι hVrange
      exact ⟨Vw, hVw, fun t ht => hVfibre t ht⟩
    · obtain ⟨w, rfl⟩ := ConnectedComponents.surjective_coe q
      obtain ⟨V, hV, hw, -⟩ :=
        exists_isAffineOpen_mem_and_subset (X := W.toScheme) (x := w) (U := ⊤) (by simp)
      exact ⟨V, hV, fun t ht => (hhit ⟨t, by simpa [χ, π] using ht⟩).elim⟩
  choose Vq hVq hVqfibre using hUq
  obtain ⟨V, hV, hVf⟩ := exists_affineOpen_range_subset_of_open_component_fibres
    G.X.left W fW hfWcont π ConnectedComponents.continuous_coe
    χ hχ (fun _ => rfl) Vq hVq hVqfibre
  refine ⟨V, hV, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact hVf ⟨t, rfl⟩

end AlgebraicGeometry

end

/-! ### Additional declarations -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory
universe u
namespace AlgebraicGeometry

end AlgebraicGeometry
end
