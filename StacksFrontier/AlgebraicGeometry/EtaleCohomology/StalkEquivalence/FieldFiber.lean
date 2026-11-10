module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisDescentSheaf.FiberAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisDescentSheaf.FiberAction
import all StacksFrontier.AlgebraicGeometry.FundamentalGroup.SchemesEtalePoint.Basic

/-!
# The fibre of a geometric point of the spectrum of a field

Let `K` be a field, let `sbar` be a geometric point of `Spec K` with algebraically closed field
`Ω`, and let `L` be the separable closure of the residue field `κ` at the image of `sbar` inside
`Ω`. Since `Spec K` has a unique point, the canonical morphism `Spec κ ⟶ Spec K` is an
isomorphism, so every object of the small étale site of `Spec K` is also étale over `Spec κ` and
is therefore a disjoint union of spectra of finite separable extensions of `κ`.

This file proves four consequences of that description: every lift of `sbar` has an open
stabilizer, the pointed neighborhoods whose fibre is a single Galois orbit are cofinal, every point
of an object of the site is the image of a lift, and every open subgroup of the absolute Galois
group contains the stabilizer of a lift.

## Main definitions

* `AlgebraicGeometry.residuePointIso` — the spectrum of the residue field at the image of the
  geometric point, identified with the spectrum of the field itself.
* `AlgebraicGeometry.toResiduePoint` — the structure morphism of an object of the small étale
  site, read over that residue field.

## Main results

* `AlgebraicGeometry.isIso_fromSpecResidueField_of_field` — for a field, the canonical
  morphism from the spectrum of a residue field is an isomorphism.
* `AlgebraicGeometry.exists_finite_separable_factorization` — a lift of the separable-closure
  point factors through a finite separable piece of its target.
* `AlgebraicGeometry.isOpen_stabilizer_galoisFiberAction` — the stabilizer of a lift of the
  geometric point is open in the absolute Galois group.
* `AlgebraicGeometry.exists_transitive_refinement` — the pointed étale neighborhoods whose
  fibre is a single Galois orbit are cofinal.
* `AlgebraicGeometry.exists_geometricPointFiber_base_eq` — every point of an object of the
  small étale site is the image of a lift of the geometric point.
* `AlgebraicGeometry.exists_fiber_point_stabilizer_le` — every open subgroup of the absolute
  Galois group contains the stabilizer of a lift of the geometric point to some object.

## References

* [Stacks Project, Tag 03QT](https://stacks.math.columbia.edu/tag/03QT)
* [Stacks Project, Tag 03PC](https://stacks.math.columbia.edu/tag/03PC)
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
namespace AlgebraicGeometry
attribute [local instance] GeometricPoint.residueFieldAlgebra

/-- For a field `K`, the canonical morphism from the spectrum of the residue field at any point
of `Spec K` to `Spec K` is an isomorphism. -/
public theorem isIso_fromSpecResidueField_of_field (K : Type u) [Field K]
    (x : Spec (CommRingCat.of K)) :
    IsIso ((Spec (CommRingCat.of K)).fromSpecResidueField x) := by
  obtain rfl : x = (𝟙 (Spec (CommRingCat.of K)) : _ ⟶ _).base
      (IsLocalRing.closedPoint K) := Subsingleton.elim _ _
  set h := (Spec (CommRingCat.of K)).descResidueField
    (Scheme.stalkClosedPointTo (𝟙 (Spec (CommRingCat.of K))))
  have key : Spec.map h ≫ (Spec (CommRingCat.of K)).fromSpecResidueField _ = 𝟙 _ :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K
      (Spec (CommRingCat.of K)) (𝟙 _)
  set ι := (Spec (CommRingCat.of K)).fromSpecResidueField
    ((𝟙 (Spec (CommRingCat.of K)) : _ ⟶ _).base (IsLocalRing.closedPoint K))
  set ψ := Spec.preimage ι
  have key3 : ψ ≫ h = 𝟙 _ :=
    Spec.map_inj.mp (by rw [Spec.map_comp, Spec.map_preimage, Spec.map_id]; exact key)
  have hcomp : ∀ a : K, h.hom (ψ.hom a) = a := fun a =>
    congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of K => f.hom a) key3
  have hIso : IsIso h := (ConcreteCategory.isIso_iff_bijective h).mpr
    ⟨h.hom.injective, fun a => ⟨ψ.hom a, hcomp a⟩⟩
  have : IsIso (Spec.map h) := inferInstance
  have : IsIso (Spec.map h ≫ ι) := by rw [key]; infer_instance
  exact IsIso.of_isIso_comp_left (Spec.map h) ι

/-- The spectrum of a finite separable field extension is étale over the base field. -/
public theorem etale_specMap_algebraMap_of_finite_separable (k E : Type u) [Field k] [Field E]
    [Algebra k E] [Module.Finite k E] [Algebra.IsSeparable k E] :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap k E))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  change (algebraMap k E).Etale
  rw [RingHom.etale_algebraMap]
  exact ⟨Algebra.FormallyEtale.of_isSeparable k E,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

section Field
variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K)))

/-- The spectrum of the residue field at the image of a geometric point of the spectrum of a
field, identified with that spectrum. -/
def residuePointIso :
    Spec (CommRingCat.of ↥((Spec (CommRingCat.of K)).residueField (sbar.hom default))) ≅
      Spec (CommRingCat.of K) :=
  haveI : IsIso ((Spec (CommRingCat.of K)).fromSpecResidueField (sbar.hom default)) :=
    isIso_fromSpecResidueField_of_field K _
  asIso ((Spec (CommRingCat.of K)).fromSpecResidueField (sbar.hom default))

/-- The forward map of `residuePointIso` is the canonical morphism from the spectrum of the
residue field. -/
@[simp] theorem residuePointIso_hom :
    (residuePointIso K sbar).hom =
      (Spec (CommRingCat.of K)).fromSpecResidueField (sbar.hom default) := rfl

/-- The structure morphism of an object of the small étale site, read over the residue field
at the image of the geometric point. -/
def toResiduePoint (U : SmallEtale B (Spec (.of K)) hK) :
    (SmallEtale.toScheme B (Spec (.of K)) hK).obj U ⟶
      Spec (CommRingCat.of ↥((Spec (CommRingCat.of K)).residueField (sbar.hom default))) :=
  B.inclusion.map U.obj.hom ≫ (residuePointIso K sbar).inv

/-- The structure morphism `toResiduePoint` of an object of the small étale site is étale. -/
instance etale_toResiduePoint (U : SmallEtale B (Spec (.of K)) hK) :
    Etale (toResiduePoint B K hK sbar U) := by
  rw [toResiduePoint]; infer_instance

/-- The separable-closure point is the structure morphism over the residue field. -/
theorem sepClosureOver_comp_residuePointIso_inv :
    GeometricPoint.sepClosureOver sbar ≫ (residuePointIso K sbar).inv =
      Spec.map (CommRingCat.ofHom (algebraMap
        ((Spec (CommRingCat.of K)).residueField (sbar.hom default))
        ↥(GeometricPoint.separableClosure sbar))) := by
  rw [GeometricPoint.sepClosureOver, Category.assoc, residuePointIso]
  simp

/-- An object of the small étale site is a coproduct of spectra of finite separable extensions of
the residue field, compatibly with the structure morphisms (stated for the inverse). -/
private theorem exists_sigma_spec_iso_toResiduePoint (U : SmallEtale B (Spec (.of K)) hK) :
    ∃ (I : Type u) (E : I → Type u) (_ : ∀ i, Field (E i))
      (_ : ∀ i, Algebra ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) (E i))
      (_ : ∀ i, Module.Finite ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) (E i))
      (_ : ∀ i, Algebra.IsSeparable
        ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) (E i))
      (e : (SmallEtale.toScheme B (Spec (.of K)) hK).obj U ≅ ∐ fun i ↦ Spec (.of (E i))),
      e.inv ≫ toResiduePoint B K hK sbar U =
        Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap
          ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) (E i)))) := by
  obtain ⟨I, E, hEf, hEa, hEfin, hEsep, e, he⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable
      ((Spec (CommRingCat.of K)).residueField (sbar.hom default))
      (toResiduePoint B K hK sbar U)).mp inferInstance
  exact ⟨I, E, hEf, hEa, hEfin, hEsep, e, by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]⟩

/-- **Every lift of the separable-closure point factors through a finite separable piece.**
A lift `y` to an object `U` of the small étale site of `Spec K` factors as `g ≫ j`, where
`j : Spec E ⟶ U` is an open immersion over the residue field `κ` at the image of the geometric
point and `E` is a finite separable extension of `κ`. -/
theorem exists_finite_separable_factorization (U : SmallEtale B (Spec (.of K)) hK)
    (y : (sepClosureFiber B (Spec (.of K)) hK sbar).obj U) :
    ∃ (E : Type u) (_ : Field E)
      (_ : Algebra ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) E)
      (_ : Module.Finite ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) E)
      (_ : Algebra.IsSeparable
        ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) E)
      (j : Spec (.of E) ⟶ (SmallEtale.toScheme B (Spec (.of K)) hK).obj U),
      IsOpenImmersion j ∧
      j ≫ toResiduePoint B K hK sbar U =
        Spec.map (CommRingCat.ofHom (algebraMap
          ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) E)) ∧
      ∃ g : Spec (.of ↥(GeometricPoint.separableClosure sbar)) ⟶ Spec (.of E), y.1 = g ≫ j := by
  classical
  obtain ⟨I, E, hEf, hEa, hEfin, hEsep, e, hinv⟩ :=
    exists_sigma_spec_iso_toResiduePoint B K hK sbar U
  obtain ⟨i, g, hg⟩ := exists_factorization_spec_sigma (fun i ↦ Spec (.of (E i)))
    ↥(GeometricPoint.separableClosure sbar) e y.1
  refine ⟨E i, hEf i, hEa i, hEfin i, hEsep i,
    Sigma.ι (fun i ↦ Spec (.of (E i))) i ≫ e.inv, inferInstance, ?_, g, hg⟩
  rw [Category.assoc, hinv, Sigma.ι_comp_desc]

/-- **The stabilizer of a lift of a geometric point is open.** The stabilizer in the absolute
Galois group of a point of the fibre of `sbar` at an object of the small étale site is open for
the Krull topology. -/
theorem isOpen_stabilizer_galoisFiberAction (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    IsOpen {σ : GeometricPoint.absoluteGaloisGroup sbar |
      galoisFiberAction B K hK sbar σ p = p} := by
  classical
  set y := (geometricPointFiberSepClosureEquiv B K hK sbar U).symm p with hy
  have hpy : geometricPointFiberSepClosureEquiv B K hK sbar U y = p := by
    rw [hy, Equiv.apply_symm_apply]
  obtain ⟨E, hEf, hEa, hEfin, hEsep, j, hj, hover, g, hgy⟩ :=
    exists_finite_separable_factorization B K hK sbar U y
  have hbase : g ≫ Spec.map (CommRingCat.ofHom (algebraMap
        ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) E)) =
      Spec.map (CommRingCat.ofHom (algebraMap
        ((Spec (CommRingCat.of K)).residueField (sbar.hom default))
        ↥(GeometricPoint.separableClosure sbar))) := by
    have h2 : y.1 ≫ toResiduePoint B K hK sbar U =
        Spec.map (CommRingCat.ofHom (algebraMap
          ((Spec (CommRingCat.of K)).residueField (sbar.hom default))
          ↥(GeometricPoint.separableClosure sbar))) := by
      rw [toResiduePoint, ← Category.assoc, y.2]
      exact sepClosureOver_comp_residuePointIso_inv K sbar
    rwa [hgy, Category.assoc, hover] at h2
  have hset : {σ : GeometricPoint.absoluteGaloisGroup sbar |
        galoisFiberAction B K hK sbar σ p = p} =
      {σ : GeometricPoint.absoluteGaloisGroup sbar |
        Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ g = g} := by
    ext σ
    simp only [Set.mem_ofPred_eq]
    rw [galoisFiberAction, ← hy, ← hpy,
      (geometricPointFiberSepClosureEquiv B K hK sbar U).apply_eq_iff_eq]
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      rw [sepClosureFiberSmul_coe, hgy, ← Category.assoc] at h'
      exact (cancel_mono j).mp h'
    · intro h
      apply Subtype.ext
      rw [sepClosureFiberSmul_coe, hgy, ← Category.assoc, h]
  rw [hset]
  exact isOpen_galois_stabilizer_specMap _ _ E g hbase

/-- The algebra map of the residue field at the image of a geometric point is the canonical
residue-field embedding. -/
theorem GeometricPoint.algebraMap_residueField_eq :
    algebraMap ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) sbar.residueField =
      GeometricPoint.residueFieldHom sbar := rfl

/-- The geometric point, read as a morphism over the residue field at its image. -/
theorem specMap_algebraMap_comp_residuePointIso :
    Spec.map (CommRingCat.ofHom (algebraMap
        ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) sbar.residueField)) ≫
      (residuePointIso K sbar).hom = sbar.hom := by
  rw [residuePointIso_hom, GeometricPoint.algebraMap_residueField_eq]
  exact GeometricPoint.specMap_residueFieldHom_comp_fromSpecResidueField sbar

/-- **Every point of an object of the small étale site is the image of a lift of the geometric
point.** -/
theorem exists_geometricPointFiber_base_eq (U : SmallEtale B (Spec (.of K)) hK)
    (x : (SmallEtale.toScheme B (Spec (.of K)) hK).obj U) :
    ∃ p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U, p.1.base default = x := by
  classical
  obtain ⟨I, E, hEf, hEa, hEfin, hEsep, e, hinv⟩ :=
    exists_sigma_spec_iso_toResiduePoint B K hK sbar U
  obtain ⟨⟨i, z⟩, hz⟩ : ∃ w : (i : I) × ↥(Spec (.of (E i))),
      (Sigma.ι (fun i ↦ Spec (.of (E i))) w.1).base w.2 = e.hom.base x := by
    refine ⟨(sigmaMk (fun i ↦ Spec (.of (E i)))).symm (e.hom.base x), ?_⟩
    rw [← sigmaMk_mk (fun i ↦ Spec (.of (E i)))]
    exact (sigmaMk (fun i ↦ Spec (.of (E i)))).apply_symm_apply _
  let φ : E i →ₐ[(Spec (CommRingCat.of K)).residueField (sbar.hom default)]
      sbar.residueField := IsAlgClosed.lift
  have key : (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Sigma.ι (fun i ↦ Spec (.of (E i))) i ≫ e.inv) ≫ toResiduePoint B K hK sbar U =
      Spec.map (CommRingCat.ofHom (algebraMap
        ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) sbar.residueField)) := by
    rw [Category.assoc, Category.assoc, hinv, Sigma.ι_comp_desc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    exact congrArg (fun r ↦ Spec.map (CommRingCat.ofHom r))
      (RingHom.ext fun a ↦ φ.commutes a)
  refine ⟨⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Sigma.ι (fun i ↦ Spec (.of (E i))) i ≫ e.inv, ?_⟩, ?_⟩
  · have h1 : toResiduePoint B K hK sbar U ≫ (residuePointIso K sbar).hom =
        B.inclusion.map U.obj.hom := by
      rw [toResiduePoint, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← h1, ← Category.assoc, key]
    exact specMap_algebraMap_comp_residuePointIso K sbar
  · have hdef : (Spec.map (CommRingCat.ofHom φ.toRingHom)).base default = z :=
      Subsingleton.elim _ _
    change e.inv.base ((Sigma.ι (fun i ↦ Spec (.of (E i))) i).base
      ((Spec.map (CommRingCat.ofHom φ.toRingHom)).base default)) = x
    rw [hdef, hz]
    simp

/-- **The pointed étale neighborhoods whose fibre is a single Galois orbit are cofinal.**
Every pointed neighborhood `(U, p)` is refined by a pointed neighborhood `(V, q)` such that the
absolute Galois group acts transitively on the fibre of `sbar` at `V`. -/
theorem exists_transitive_refinement (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    ∃ (V : SmallEtale B (Spec (.of K)) hK) (f : V ⟶ U)
      (q : (geometricPointFiber B (Spec (.of K)) hK sbar).obj V),
      (geometricPointFiber B (Spec (.of K)) hK sbar).map f q = p ∧
      ∀ r : (geometricPointFiber B (Spec (.of K)) hK sbar).obj V,
        ∃ σ : GeometricPoint.absoluteGaloisGroup sbar,
          galoisFiberAction B K hK sbar σ q = r := by
  classical
  set y := (geometricPointFiberSepClosureEquiv B K hK sbar U).symm p with hy
  have hpy : geometricPointFiberSepClosureEquiv B K hK sbar U y = p := by
    rw [hy, Equiv.apply_symm_apply]
  obtain ⟨E, hEf, hEa, hEfin, hEsep, j, hj, hover, g, hgy⟩ :=
    exists_finite_separable_factorization B K hK sbar U y
  have hEcontains : B.Contains (Spec (.of E)) :=
    (Scheme.size_le_of_locallyOfFiniteType (j ≫ B.inclusion.map U.obj.hom)).trans_lt hK
  let V : SmallEtale B (Spec (.of K)) hK :=
    Stacks.EtaleCohomology.mkObj B hK (Spec (.of E)) (j ≫ B.inclusion.map U.obj.hom)
      hEcontains inferInstance
  have hVhom : B.inclusion.map V.obj.hom = j ≫ B.inclusion.map U.obj.hom := rfl
  let f : V ⟶ U := Stacks.EtaleCohomology.mkHom B hK (V := V) (W := U) j rfl
  have hfj : (SmallEtale.toScheme B (Spec (.of K)) hK).map f = j := rfl
  have hbase : ∀ z : (sepClosureFiber B (Spec (.of K)) hK sbar).obj V,
      z.1 ≫ Spec.map (CommRingCat.ofHom (algebraMap
          ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) E)) =
        Spec.map (CommRingCat.ofHom (algebraMap
          ((Spec (CommRingCat.of K)).residueField (sbar.hom default))
          ↥(GeometricPoint.separableClosure sbar))) := by
    intro z
    have hzj : (z.1 ≫ j) ≫ B.inclusion.map U.obj.hom =
        GeometricPoint.sepClosureOver sbar := (Category.assoc _ _ _).trans z.2
    exact (congrArg (fun w ↦ z.1 ≫ w) hover).symm.trans
      ((Category.assoc z.1 j (toResiduePoint B K hK sbar U)).symm.trans
        ((Category.assoc (z.1 ≫ j) (B.inclusion.map U.obj.hom)
            (residuePointIso K sbar).inv).symm.trans
          ((congrArg (fun w ↦ w ≫ (residuePointIso K sbar).inv) hzj).trans
            (sepClosureOver_comp_residuePointIso_inv K sbar))))
  have hq2 : g ≫ B.inclusion.map V.obj.hom = GeometricPoint.sepClosureOver sbar := by
    rw [hVhom, ← Category.assoc, ← hgy]
    exact y.2
  let q' : (sepClosureFiber B (Spec (.of K)) hK sbar).obj V := ⟨g, hq2⟩
  refine ⟨V, f, geometricPointFiberSepClosureEquiv B K hK sbar V q', ?_, ?_⟩
  · rw [geometricPointFiberSepClosureEquiv_map, ← hpy]
    refine congrArg _ (Subtype.ext ?_)
    change g ≫ (SmallEtale.toScheme B (Spec (.of K)) hK).map f = y.1
    rw [hfj, hgy]
  · intro r
    let r' := (geometricPointFiberSepClosureEquiv B K hK sbar V).symm r
    have hrr : geometricPointFiberSepClosureEquiv B K hK sbar V r' = r :=
      Equiv.apply_symm_apply _ _
    obtain ⟨σ, hσ⟩ := exists_gal_comp_eq_of_finite_separable
      ((Spec (CommRingCat.of K)).residueField (sbar.hom default))
      ↥(GeometricPoint.separableClosure sbar) E
      (specMapOverFieldEquiv _ _ E ⟨g, hbase q'⟩)
      (specMapOverFieldEquiv _ _ E ⟨r'.1, hbase r'⟩)
    refine ⟨σ, ?_⟩
    have hpre := specMapOverFieldEquiv_precomp
      ((Spec (CommRingCat.of K)).residueField (sbar.hom default))
      ↥(GeometricPoint.separableClosure sbar) E σ ⟨g, hbase q'⟩
    have hval : Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ g = r'.1 :=
      congrArg Subtype.val ((specMapOverFieldEquiv
        ((Spec (CommRingCat.of K)).residueField (sbar.hom default))
        ↥(GeometricPoint.separableClosure sbar) E).injective (hpre.trans hσ))
    rw [galoisFiberAction, ← hrr]
    refine congrArg _ ?_
    rw [Equiv.symm_apply_apply]
    exact Subtype.ext (by rw [sepClosureFiberSmul_coe]; exact hval)

/-- **Every open subgroup of the absolute Galois group contains the stabilizer of a lift of the
geometric point.** For an open subgroup `H` there is a point `q` of the fibre of `sbar` at some
object of the small étale site whose stabilizer is contained in `H`. -/
theorem exists_fiber_point_stabilizer_le
    (H : Subgroup (GeometricPoint.absoluteGaloisGroup sbar))
    (hH : IsOpen (H : Set (GeometricPoint.absoluteGaloisGroup sbar))) :
    ∃ (V : SmallEtale B (Spec (.of K)) hK)
      (q : (geometricPointFiber B (Spec (.of K)) hK sbar).obj V),
      ∀ σ : GeometricPoint.absoluteGaloisGroup sbar,
        galoisFiberAction B K hK sbar σ q = q → σ ∈ H := by
  classical
  have : IsGalois ((Spec (CommRingCat.of K)).residueField (sbar.hom default))
      ↥(GeometricPoint.separableClosure sbar) := inferInstance
  have hclosed : IsClosed (H : Set (GeometricPoint.absoluteGaloisGroup sbar)) :=
    OpenSubgroup.isClosed ⟨H, hH⟩
  set E := IntermediateField.fixedField H with hE
  have hfix : E.fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hclosed⟩
  have hdim : FiniteDimensional ((Spec (CommRingCat.of K)).residueField (sbar.hom default))
      ↥E := by
    refine (InfiniteGalois.isOpen_iff_finite E).mp ?_
    change IsOpen (E.fixingSubgroup : Set (GeometricPoint.absoluteGaloisGroup sbar))
    rw [hfix]; exact hH
  have : Algebra.IsSeparable ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) ↥E :=
    Algebra.isSeparable_tower_bot_of_isSeparable _ ↥E
      ↥(GeometricPoint.separableClosure sbar)
  have hEt : Etale (Spec.map (CommRingCat.ofHom (algebraMap
      ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) ↥E))) :=
    etale_specMap_algebraMap_of_finite_separable _ _
  have hVst : Etale (Spec.map (CommRingCat.ofHom (algebraMap
      ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) ↥E)) ≫
      (residuePointIso K sbar).hom) := inferInstance
  have hEcon : B.Contains (Spec (.of ↥E)) :=
    (Scheme.size_le_of_locallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap
      ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) ↥E)) ≫
      (residuePointIso K sbar).hom)).trans_lt hK
  let V : SmallEtale B (Spec (.of K)) hK :=
    Stacks.EtaleCohomology.mkObj B hK (Spec (.of ↥E))
      (Spec.map (CommRingCat.ofHom (algebraMap
        ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) ↥E)) ≫
        (residuePointIso K sbar).hom) hEcon hVst
  have htower : CommRingCat.ofHom (algebraMap
        ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) ↥E) ≫
      CommRingCat.ofHom (algebraMap ↥E ↥(GeometricPoint.separableClosure sbar)) =
      CommRingCat.ofHom (algebraMap
        ((Spec (CommRingCat.of K)).residueField (sbar.hom default))
        ↥(GeometricPoint.separableClosure sbar)) := by
    rw [← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq
      ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) ↥E
      ↥(GeometricPoint.separableClosure sbar)).symm
  have hq2 : Spec.map (CommRingCat.ofHom (algebraMap ↥E
        ↥(GeometricPoint.separableClosure sbar))) ≫ B.inclusion.map V.obj.hom =
      GeometricPoint.sepClosureOver sbar :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun w ↦ w ≫ (residuePointIso K sbar).hom)
        ((Spec.map_comp _ _).symm.trans (congrArg Spec.map htower)))
  let q' : (sepClosureFiber B (Spec (.of K)) hK sbar).obj V :=
    ⟨Spec.map (CommRingCat.ofHom (algebraMap ↥E
      ↥(GeometricPoint.separableClosure sbar))), hq2⟩
  refine ⟨V, geometricPointFiberSepClosureEquiv B K hK sbar V q', ?_⟩
  intro σ hσ
  rw [← hfix, IntermediateField.mem_fixingSubgroup_iff]
  rw [galoisFiberAction, Equiv.symm_apply_apply,
    (geometricPointFiberSepClosureEquiv B K hK sbar V).apply_eq_iff_eq] at hσ
  have h1 := congrArg Subtype.val hσ
  rw [sepClosureFiberSmul_coe] at h1
  have h2 : Spec.map (CommRingCat.ofHom (algebraMap ↥E
        ↥(GeometricPoint.separableClosure sbar)) ≫
      CommRingCat.ofHom σ.toAlgHom.toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap ↥E
        ↥(GeometricPoint.separableClosure sbar))) := by
    rw [Spec.map_comp]; exact h1
  have h3 := Spec.map_inj.mp h2
  intro x hx
  exact congrArg (fun r : CommRingCat.of ↥E ⟶
    CommRingCat.of ↥(GeometricPoint.separableClosure sbar) ↦ r.hom ⟨x, hx⟩) h3

end Field
end AlgebraicGeometry
end
