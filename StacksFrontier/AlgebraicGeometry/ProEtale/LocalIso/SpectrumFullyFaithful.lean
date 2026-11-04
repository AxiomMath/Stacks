module

public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.LocalIsomorphism
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.InverseImageStructureSheaf
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# Spectra of algebras identifying local rings are topologically fully faithful

For an algebra whose structure map identifies local rings, continuous maps of spectra over the
base spectrum come uniquely from algebra homomorphisms.

## Main results

* `AlgebraicGeometry.ProEtale.existsUnique_algHom_of_specTopMap_over` expresses full
  faithfulness on Hom sets: every continuous map over the base spectrum is induced by a unique
  algebra homomorphism in the opposite direction.

## Implementation notes

The conclusion is stated as unique existence on Hom sets, rather than by constructing the
restricted functor. Only the target algebra of the spectral map needs to identify local rings;
the source algebra is arbitrary.

Forgetting the sheaf map is a bijection on morphisms over `X` exactly when the adjoint structure
map `p⁻¹ 𝒪_X ⟶ 𝒪_Y` is an isomorphism. That condition is stalkwise, and for `p = Spec (A → B)`
each stalk map of `p` is the canonical map of local rings, so it is an isomorphism precisely
because `A → B` identifies local rings.

## References

* [Stacks Project, Tag 096L](https://stacks.math.columbia.edu/tag/096L)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.ProEtale

universe u

/-- A morphism of locally ringed spaces all of whose stalk maps are isomorphisms has the
structure sheaf of its source as the inverse image of that of its target. -/
private lemma isIso_inverseImageStructureMap_of_stalkMap_isIso
    {X Y : LocallyRingedSpace.{u}} (p : Y ⟶ X)
    (h : ∀ y : Y, IsIso (p.stalkMap y)) : IsIso (inverseImageStructureMap p) := by
  refine (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).2 fun y => ?_
  have : IsIso ((pullbackStalkComparison p y).inv ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat y).map
        ((TopCat.Sheaf.forget CommRingCat Y.toTopCat).map
          (inverseImageStructureMap p))) := by
    rw [inverseImageStructureMap_stalk_compat p y]
    exact h y
  exact IsIso.of_isIso_comp_left (pullbackStalkComparison p y).inv
    ((TopCat.Presheaf.stalkFunctor CommRingCat y).map
      ((TopCat.Sheaf.forget CommRingCat Y.toTopCat).map (inverseImageStructureMap p)))

/-- If `A → B` identifies local rings, then every stalk map of `Spec B ⟶ Spec A` is an
isomorphism. -/
private lemma specLocalRingedMap_stalk_isIso
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (hB : Algebra.IdentifiesLocalRings A B) (q : Spec (CommRingCat.of B)) :
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A B))).toLRSHom.stalkMap q) := by
  show IsIso ((Spec.sheafedSpaceMap (CommRingCat.ofHom (algebraMap A B))).hom.stalkMap q)
  let p : PrimeSpectrum B := q
  let f : CommRingCat.of A ⟶ CommRingCat.of B :=
    CommRingCat.ofHom (algebraMap A B)
  let pA : PrimeSpectrum A := PrimeSpectrum.comap f.hom p
  have : p.asIdeal.IsPrime := p.2
  have : pA.asIdeal.IsPrime := pA.2
  rw [← AlgebraicGeometry.localRingHom_comp_stalkIso f p]
  let α := CommRingCat.ofHom
    (StructureSheaf.stalkIso (CommRingCat.of A)
      (PrimeSpectrum.comap f.hom p)).symm.toRingEquiv.toRingHom
  let β := CommRingCat.ofHom
    (Localization.localRingHom pA.asIdeal p.asIdeal f.hom rfl)
  let γ := CommRingCat.ofHom
    (StructureSheaf.stalkIso (CommRingCat.of B) p).toRingEquiv.toRingHom
  have : IsIso α := (ConcreteCategory.isIso_iff_bijective _).2 (RingEquiv.bijective _)
  have : IsIso β := (ConcreteCategory.isIso_iff_bijective _).2 (hB p.asIdeal)
  have : IsIso γ := (ConcreteCategory.isIso_iff_bijective _).2 (RingEquiv.bijective _)
  show IsIso (α ≫ β ≫ γ)
  exact IsIso.comp_isIso

/-- If `A → B` identifies local rings, the structure sheaf of `Spec B` is the inverse image of
the structure sheaf of `Spec A`. -/
private lemma specMap_inverseImageStructureMap_isIso
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (hB : Algebra.IdentifiesLocalRings A B) :
    IsIso (inverseImageStructureMap
      (Spec.map (CommRingCat.ofHom (algebraMap A B))).toLRSHom) :=
  isIso_inverseImageStructureMap_of_stalkMap_isIso _ (specLocalRingedMap_stalk_isIso A B hB)

/-- If `A → B` identifies local rings, an `A`-algebra homomorphism `B →ₐ[A] C` is determined by
the continuous map of spectra it induces. -/
private theorem algHom_eq_of_specTopMap_eq
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (hB : Algebra.IdentifiesLocalRings A B) {f₁ f₂ : B →ₐ[A] C}
    (h : Spec.topMap (CommRingCat.ofHom f₁.toRingHom) =
      Spec.topMap (CommRingCat.ofHom f₂.toRingHom)) : f₁ = f₂ := by
  let RA := CommRingCat.of A
  let RB := CommRingCat.of B
  let RC := CommRingCat.of C
  let ab : RA ⟶ RB := CommRingCat.ofHom (algebraMap A B)
  let ac : RA ⟶ RC := CommRingCat.ofHom (algebraMap A C)
  let F := Spec.toLocallyRingedSpace
  let X := F.obj (op RA)
  let Y := F.obj (op RB)
  let Z := F.obj (op RC)
  let p : Y ⟶ X := (Spec.map ab).toLRSHom
  let q : Z ⟶ X := (Spec.map ac).toLRSHom
  have : IsIso (inverseImageStructureMap p) := specMap_inverseImageStructureMap_isIso A B hB
  have hover (f : B →ₐ[A] C) : F.map (CommRingCat.ofHom f.toRingHom : RB ⟶ RC).op ≫ p = q := by
    have hf : ab ≫ CommRingCat.ofHom f.toRingHom = ac := by
      ext a
      exact f.commutes a
    calc
      _ = F.map ((CommRingCat.ofHom f.toRingHom : RB ⟶ RC).op ≫ ab.op) := by
        show F.map _ ≫ F.map ab.op = _
        simp
      _ = F.map (ab ≫ CommRingCat.ofHom f.toRingHom).op := by simp
      _ = F.map ac.op := by rw [hf]
      _ = q := rfl
  have hm : (⟨_, hover f₁⟩ : {k : Z ⟶ Y // k ≫ p = q}) = ⟨_, hover f₂⟩ :=
    (bijective_forgetToTop_morphism_over p q).1 (Subtype.ext h)
  exact AlgHom.ext fun b => DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (Quiver.Hom.op_inj (F.map_injective (congrArg Subtype.val hm)))) b

/-- **Stacks Project, Tag 096L.** A continuous map of affine spectra over `Spec A` is uniquely
induced by an `A`-algebra homomorphism when the structural map of its target identifies local
rings. -/
@[stacks 096L]
theorem existsUnique_algHom_of_specTopMap_over
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (hB : Algebra.IdentifiesLocalRings A B)
    (g : Spec.topObj (CommRingCat.of C) ⟶ Spec.topObj (CommRingCat.of B))
    (hg : g ≫ Spec.topMap (CommRingCat.ofHom (algebraMap A B)) =
      Spec.topMap (CommRingCat.ofHom (algebraMap A C))) :
    ∃! f : B →ₐ[A] C, Spec.topMap (CommRingCat.ofHom f.toRingHom) = g := by
  let RA := CommRingCat.of A
  let RB := CommRingCat.of B
  let RC := CommRingCat.of C
  let ab : RA ⟶ RB := CommRingCat.ofHom (algebraMap A B)
  let ac : RA ⟶ RC := CommRingCat.ofHom (algebraMap A C)
  let F := Spec.toLocallyRingedSpace
  let X := F.obj (op RA)
  let Y := F.obj (op RB)
  let Z := F.obj (op RC)
  let p : Y ⟶ X := (Spec.map ab).toLRSHom
  let q : Z ⟶ X := (Spec.map ac).toLRSHom
  have : IsIso (inverseImageStructureMap p) := by
    show IsIso (inverseImageStructureMap (Spec.map ab).toLRSHom)
    exact specMap_inverseImageStructureMap_isIso A B hB
  have hgbase : g ≫ p.base = q.base := hg
  have hbij := bijective_forgetToTop_morphism_over p q
  obtain ⟨m, hm⟩ := hbij.2 ⟨g, hgbase⟩
  have hmBase : m.1.base = g := congrArg Subtype.val hm
  let φop := F.preimage m.1
  let φ : RB ⟶ RC := φop.unop
  have hmapφ : F.map φ.op = m.1 := F.map_preimage m.1
  have habφ : ab ≫ φ = ac := by
    apply Quiver.Hom.op_inj
    exact (Functor.map_injective F) (by
      calc
        F.map (ab ≫ φ).op = F.map (φ.op ≫ ab.op) := by simp
        _ = F.map φ.op ≫ F.map ab.op := F.map_comp _ _
        _ = m.1 ≫ p := by
          rw [hmapφ]
          rfl
        _ = q := m.2
        _ = F.map ac.op := rfl)
  have hscalar : φ.hom.comp (algebraMap A B) = algebraMap A C := by
    simpa [ab, ac, RA, RB, RC] using congrArg CommRingCat.Hom.hom habφ
  let f : B →ₐ[A] C :=
    { toRingHom := φ.hom
      commutes' := fun a => by
        show φ.hom (algebraMap A B a) = algebraMap A C a
        exact DFunLike.congr_fun hscalar a }
  have htop : Spec.topMap (CommRingCat.ofHom f.toRingHom) = g := by
    show (F.map φ.op).base = g
    rw [hmapφ]
    exact hmBase
  exact ⟨f, htop, fun f' hf' => algHom_eq_of_specTopMap_eq hB (hf'.trans htop.symm)⟩

end AlgebraicGeometry.ProEtale
