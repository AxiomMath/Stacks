module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField

/-!
# Finite separable closed points of affine space

Every nonempty open subset of affine space over a field contains a closed point whose residue
field is a finite separable extension of the ground field.

## Main results

* `AlgebraicGeometry.exists_closedPoint_finite_separable_residueField`: a nonempty open subset
  of affine space over a field contains a closed point with finite separable residue field.

## Implementation notes

Affine `d`-space over `k` is `AlgebraicGeometry.AffineSpace (ULift (Fin d)) (Spec (.of k))`,
whose coordinate ring is `MvPolynomial (ULift (Fin d)) k`. The algebra structure on the
residue field at a point is the canonical one induced by the structure morphism of affine
space followed by evaluation at that point.

The point is produced from a `k`-point of the separable closure of `k`: the separable closure
is infinite, so a nonzero polynomial has a nonvanishing point there, which gives a morphism
from the spectrum of the separable closure into the prescribed basic open. Its image is a
point whose residue field embeds into the separable closure, hence is separable, and the
embedding also makes the residue field algebraic over `k`, which forces the point to be
closed.

## References

* [Stacks Project, Tag 055T](https://stacks.math.columbia.edu/tag/055T)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 055T.** A nonempty open subset of affine space over a field contains
a closed point whose residue field is a finite separable extension of the field. -/
@[stacks 055T]
theorem exists_closedPoint_finite_separable_residueField
    {k : Type u} [Field k] {d : ℕ}
    (W : Set (AffineSpace (ULift.{u} (Fin d)) (Spec (.of k))))
    (hWopen : IsOpen W) (hWnonempty : W.Nonempty) :
    ∃ w : AffineSpace (ULift.{u} (Fin d)) (Spec (.of k)),
      w ∈ W ∧ w ∈ closedPoints (AffineSpace (ULift.{u} (Fin d)) (Spec (.of k))) ∧
        let X := AffineSpace (ULift.{u} (Fin d)) (Spec (.of k))
        let f := X ↘ Spec (.of k)
        letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation w).hom.toAlgebra
        Module.Finite k (X.residueField w) ∧
          Algebra.IsSeparable k (X.residueField w) := by
  classical
  let X := AffineSpace (ULift.{u} (Fin d)) (Spec (.of k))
  let f : X ⟶ Spec (.of k) := X ↘ Spec (.of k)
  let R := MvPolynomial (ULift.{u} (Fin d)) k
  let e : X ≅ Spec (.of R) := AffineSpace.SpecIso (ULift.{u} (Fin d)) (.of k)
  obtain ⟨x₀, hx₀⟩ := hWnonempty
  let homeo := Scheme.homeoOfIso e
  have hO : IsOpen (homeo '' W) := homeo.isOpenMap _ hWopen
  let y₀ : PrimeSpectrum R := homeo x₀
  obtain ⟨_, ⟨p, rfl⟩, hp, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hO y₀ ⟨x₀, hx₀, rfl⟩
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  let L := SeparableClosure k
  have hLinfinite : Infinite L := by
    by_cases hk : Infinite k
    · exact Infinite.of_injective (algebraMap k L) (algebraMap k L).injective
    · have : Finite k := Finite.of_not_infinite hk
      have : IsAlgClosed L := (inferInstance : IsAlgClosure k L).isAlgClosed
      infer_instance
  let pL : MvPolynomial (ULift (Fin d)) L := MvPolynomial.map (algebraMap k L) p
  have hpL : pL ≠ 0 := by
    simpa [pL] using (MvPolynomial.map_injective (algebraMap k L) (algebraMap k L).injective).ne hp0
  obtain ⟨a, ha⟩ : ∃ a : ULift (Fin d) → L, MvPolynomial.eval a pL ≠ 0 := by
    by_contra! h; exact hpL (MvPolynomial.funext (fun x => by simpa using h x))
  let ψ : R →ₐ[k] L := MvPolynomial.aeval a
  let q : PrimeSpectrum R := PrimeSpectrum.comap ψ.toRingHom ⊥
  have hq : q ∈ PrimeSpectrum.basicOpen p := by
    rw [PrimeSpectrum.mem_basicOpen]
    change p ∉ Ideal.comap ψ.toRingHom (⊥ : Ideal L)
    rw [Ideal.mem_comap, Ideal.mem_bot]
    change MvPolynomial.eval₂ (algebraMap k L) a p ≠ 0
    rwa [MvPolynomial.eval₂_eq_eval_map]
  have hw₀W : homeo.symm q ∈ W := by
    obtain ⟨x, hx, hxeq⟩ := hsub hq
    simpa [← hxeq] using hx
  let h : Spec (.of L) ⟶ X := Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ e.inv
  let z : Spec (.of L) :=
    OrderDual.ofDual (AlgebraicGeometry.primeSpectrumOrderIsoSpec L (⊥ : PrimeSpectrum L))
  have hqpoint : Spec.map (CommRingCat.ofHom ψ.toRingHom) z = (q : Spec (.of R)) := by
    rw [AlgebraicGeometry.Spec.map_apply]; rfl
  have hpoint : h z = homeo.symm q := by
    change e.inv (Spec.map (CommRingCat.ofHom ψ.toRingHom) z) = homeo.symm q
    rw [hqpoint]; simp [homeo, Scheme.homeoOfIso_symm]
  let w : X := (Scheme.SpecToEquivOfField L X h).1
  have hpair : h z = w := by
    dsimp [w, Scheme.SpecToEquivOfField]; congr 1; exact Subsingleton.elim _ _
  have hwW : w ∈ W := (hpair.symm.trans hpoint).symm ▸ hw₀W
  have hOver : h ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    dsimp [h, f]
    rw [Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
    congr 1
    rw [MvPolynomial.C_eq_algebraMap]; ext x
    rw [CommRingCat.hom_comp]; exact_mod_cast ψ.commutes x
  let : Algebra k (X.residueField w) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation w).hom.toAlgebra
  let σ : X.residueField w ⟶ CommRingCat.of L := (Scheme.SpecToEquivOfField L X h).2
  let σA : X.residueField w →ₐ[k] L :=
    { toRingHom := σ.hom
      commutes' := by
        intro c
        have hEvalW : X.Γevaluation w ≫ σ = h.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom := by
          dsimp [w, σ, Scheme.SpecToEquivOfField]
          have : IsLocalHom (Scheme.stalkClosedPointTo h).hom :=
            Scheme.isLocalHom_stalkClosedPointTo h
          change (X.presheaf.germ ⊤ _ trivial ≫ X.residue _) ≫
              Scheme.descResidueField (Scheme.stalkClosedPointTo h) = _
          rw [Category.assoc, Scheme.residue_descResidueField,
            Scheme.germ_stalkClosedPointTo h ⊤ trivial]
          change h.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom = _
          rfl
        let s : Γ(Spec (.of k), ⊤) := (Scheme.ΓSpecIso (.of k)).inv.hom c
        change (X.Γevaluation w ≫ σ) (f.appTop s) = algebraMap k L c
        rw [congrArg (fun φ : Γ(X, ⊤) ⟶ CommRingCat.of L => φ (f.appTop s)) hEvalW]
        change (Scheme.ΓSpecIso (.of L)).hom (h.appTop (f.appTop s)) = _
        have happ : h.appTop (f.appTop s) =
            (Spec.map (CommRingCat.ofHom (algebraMap k L))).appTop s := by
          have htop := congrArg Scheme.Hom.appTop hOver
          simp only [Scheme.Hom.comp_app] at htop
          exact congrArg (fun φ => φ s) htop
        rw [happ]
        change ((Spec.map (CommRingCat.ofHom (algebraMap k L))).appTop ≫
          (Scheme.ΓSpecIso (.of L)).hom) s = _
        rw [Scheme.ΓSpecIso_naturality]; simp [s] }
  let B := (Spec (.of k)).residueField (f w)
  let φ : k →+* B :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (f w)).hom
  let : Algebra B (X.residueField w) := (f.residueFieldMap w).hom.toAlgebra
  have hcomp : (algebraMap B (X.residueField w)).comp φ = algebraMap k (X.residueField w) := by
    ext c
    change f.residueFieldMap w
        ((Spec (.of k)).Γevaluation (f w) ((Scheme.ΓSpecIso (.of k)).inv c)) =
      X.Γevaluation w (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c))
    exact Scheme.Γevaluation_naturality_apply f w ((Scheme.ΓSpecIso (.of k)).inv c)
  have hφsurj : Function.Surjective φ := by
    let x := f w
    have : x.asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp isClosed_singleton
    change Function.Surjective
      (CommRingCat.Hom.hom ((Scheme.ΓSpecIso (.of k)).inv ≫
        (Spec (.of k)).presheaf.germ ⊤ x trivial ≫ (Spec (.of k)).residue x))
    rw [← Scheme.Spec.algebraMap_residueFieldIso_inv]
    change Function.Surjective
      ((Scheme.Spec.residueFieldIso (.of k) x).inv.hom ∘ algebraMap k x.asIdeal.ResidueField)
    exact (ConcreteCategory.bijective_of_isIso _).surjective.comp
      (Ideal.algebraMap_residueField_surjective x.asIdeal)
  have hAlgB : Algebra.IsAlgebraic B (X.residueField w) := ⟨fun x =>
    ((Algebra.IsAlgebraic.of_injective σA σA.injective).isAlgebraic x).ringHom_of_comp_eq φ
      (RingHom.id (X.residueField w)) (RingHom.injective φ) hcomp⟩
  have hclosed : IsClosed ({w} : Set X) :=
    isClosed_of_isAlgebraic_residueField f w hAlgB isClosed_singleton
  have hf : f = e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
    calc
      f = e.hom ≫ (e.inv ≫ f) := by simp
      _ = _ := by rw [AffineSpace.SpecIso_inv_over]; rfl
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  have : LocallyOfFiniteType f := by rw [hf]; infer_instance
  have hfin : Module.Finite k (X.residueField w) := by
    have hclosedFiber : IsClosed ({f.asFiber w} : Set (f.fiber (f w))) := by
      let H := f.fiberHomeo (f w)
      convert hclosed.preimage (continuous_subtype_val.comp H.continuous) using 1
      ext z
      change z = f.asFiber w ↔ (H z).1 = w
      conv_rhs => rhs; rw [← Scheme.Hom.fiberι_asFiber f w]
      change z = f.asFiber w ↔ (H z).1 = (H (f.asFiber w)).1
      simpa only [Subtype.ext_iff] using
        (H.injective.eq_iff (a := z) (b := f.asFiber w)).symm
    have hfinite := (isClosed_asFiber_iff_finite_residueField f w).mp hclosedFiber
    let : Algebra k B := φ.toAlgebra
    have : IsScalarTower k B (X.residueField w) := IsScalarTower.of_algebraMap_eq fun x =>
      (RingHom.congr_fun hcomp x).symm
    have : Module.Finite k B := Module.Finite.of_surjective (Algebra.linearMap k B) hφsurj
    exact Module.Finite.trans B (X.residueField w)
  exact ⟨w, hwW, hclosed, hfin, Algebra.IsSeparable.of_algHom k L σA⟩

end AlgebraicGeometry
