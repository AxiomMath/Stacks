module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Generators
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.HomComplex.Composition
public import StacksFrontier.Homology.HomComplex.Currying
public import StacksFrontier.Homology.HomComplex.DerivedTensorHom
public import StacksFrontier.Homology.HomComplex.KoszulBraiding
public import StacksFrontier.Homology.HomComplex.RHom
public import StacksFrontier.Homology.HomComplex.TensorHom
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.LeftDual
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.Tor.DerivedTensorFunctorLargeUniverse
public import StacksFrontier.Homology.TorAmplitude.KFlatRepresentative
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Projective Hom comparison and chain-level currying

This is the first part of the proof that the derived tensor--Hom diagonal is invertible
(see `StacksFrontier.Homology.HomComplex.Evaluation.TensorHom`). For a bounded-above complex of
projective modules the ordinary Hom complex computes the derived internal Hom, naturally in both
variables (`Stacks.DerivedTensorHomDiagonal.ProjectiveComparison.projectiveHomComparison`). The
file also records chain-level currying computations: the uncurrying of maps into Hom complexes,
and its compatibility with composition and with `Stacks.HomComplex.TensorHomComparison.theta`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Pretriangulated ZeroObject

attribute [local instance] HasDerivedCategory.standard

universe u v w w'

set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000

namespace Stacks.DerivedTensorHomDiagonal

open StacksDraft.DerivedHom

/-! ### Derived internal Hom out of a bounded-above complex of projectives

For a bounded-above cochain complex `P` of projective modules and an arbitrary complex `L`, the
ordinary `R`-linear Hom complex represents the derived internal Hom. The comparison is natural in
both complexes and agrees with the defining K-injective comparison on K-injective targets. -/

namespace ProjectiveComparison


/-- The natural comparison with the `R`-linear Hom complex for bounded-above projective
sources. The derived-Hom bifunctor is the fixed construction of 0A63, not extra data supplied
as a hypothesis. The target complex has no boundedness, flatness, or injectivity hypothesis. -/
private structure ProjectiveHomComparison (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] where
  /-- The Hom complex represents the derived internal Hom. -/
  iso (P L : CochainComplex (ModuleCat.{u} R) ℤ) (d : ℤ) [P.IsStrictlyLE d]
      [∀ i, Projective (P.X i)] :
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.obj
        (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (CochainComplex.HomComplexR R P L)
  /-- Contravariant naturality in the projective source and covariant naturality in the
  arbitrary target, for the actual functorial maps of Hom complexes. -/
  naturality (P P' L L' : CochainComplex (ModuleCat.{u} R) ℤ) (d d' : ℤ)
      [P.IsStrictlyLE d] [P'.IsStrictlyLE d']
      [∀ i, Projective (P.X i)] [∀ i, Projective (P'.X i)]
      (f : P' ⟶ P) (g : L ⟶ L') :
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.map
          ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g) ≫
        (iso P' L' d').hom =
      (iso P L d).hom ≫ DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap P P' L
        L' f g)
  /-- On a K-injective target this is the defining comparison of 0A63. -/
  iso_eq_homIso (P I : CochainComplex (ModuleCat.{u} R) ℤ) (d : ℤ)
      [P.IsStrictlyLE d] [∀ i, Projective (P.X i)] [I.IsKInjective] :
    iso P I d = (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).homIso P I

namespace ProjectiveHomComparison

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The comparison square used in the source proof, for a map to a K-injective target.
In particular it applies to every K-injective resolution of the arbitrary target complex. -/
private theorem resolution_comparison (e : ProjectiveHomComparison R)
    (P L I : CochainComplex (ModuleCat.{u} R) ℤ) (d : ℤ)
    [P.IsStrictlyLE d] [∀ i, Projective (P.X i)] [I.IsKInjective] (f : L ⟶ I) :
    (e.iso P L d).hom ≫
        DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap P P L I (𝟙 P) f) =
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.map
          (𝟙 (Opposite.op (DerivedCategory.Q.obj P)), DerivedCategory.Q.map f) ≫
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).homIso P I).hom := by
  simpa only [e.iso_eq_homIso, DerivedCategory.Q.map_id P, op_id] using
    (e.naturality P P L I d d (𝟙 P) f).symm

/-- Hom out of a bounded-above projective complex preserves quasi-isomorphisms.
This includes the map to a K-injective resolution used in the proof of Stacks 0A66. -/
private theorem quasiIso_homCxMap (e : ProjectiveHomComparison R)
    (P L L' : CochainComplex (ModuleCat.{u} R) ℤ) (d : ℤ)
    [P.IsStrictlyLE d] [∀ i, Projective (P.X i)] (f : L ⟶ L')
    [QuasiIso f] :
    QuasiIso (Stacks.HomComplex.TensorHomComparison.HomCxMap P P L L' (𝟙 P) f) := by
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) f).mpr inferInstance
  have : IsIso (show
      (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L) ⟶
        (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L') from
      ((DerivedCategory.Q.map (𝟙 P)).op, DerivedCategory.Q.map f)) :=
    (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  have h := e.naturality P P L L' d d (𝟙 P) f
  have : IsIso ((e.iso P L d).hom ≫
      DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap P P L L' (𝟙 P) f)) := by
    rw [← h]
    infer_instance
  have : IsIso (DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap P P L L' (𝟙 P)
    f)) :=
    IsIso.of_isIso_comp_left (e.iso P L d).hom _
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mp this

end ProjectiveHomComparison

/-! The comparison is constructed using K-injective resolutions. We first check the
quasi-isomorphism on Hom complexes through their explicit cohomology classes. -/

private abbrev C (R : Type u) [CommRing R] := CochainComplex (ModuleCat.{u} R) ℤ

open CochainComplex HomComplex

private lemma postcomp_quasiIso_of_isKProjective {R : Type u} [CommRing R]
    {P L L' : C R} [P.IsKProjective] (f : L ⟶ L') [QuasiIso f] :
    QuasiIso (Stacks.HomComplex.TensorHomMap.postcomp R P L L' f) := by
  rw [StacksDraft.DerivedHom.Construction.homComplex_quasiIso_iff]
  intro n
  apply (Function.Bijective.of_comp_iff' (CohomologyClass.toHom_bijective P L' n) _).1
  have hP := IsKProjective.leftOrthogonal P
  rw [← ObjectProperty.isColocal_trW] at hP
  have hf : HomotopyCategory.quasiIso (ModuleCat R) (.up ℤ)
      ((HomotopyCategory.quotient _ _).map (f⟦n⟧')) := by
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact (inferInstance : QuasiIso (f⟦n⟧'))
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at hf
  simpa only [Function.comp_def,
    StacksDraft.DerivedHom.Construction.homClassesMap_postcomp_toHom] using
    (hP _ hf).comp (CohomologyClass.toHom_bijective P L n)

set_option backward.isDefEq.respectTransparency false in
private lemma homCxMap_eq_precomp_postcomp {R : Type u} [CommRing R]
    (P P' L L' : C R) (f : P' ⟶ P) (g : L ⟶ L') :
    Stacks.HomComplex.TensorHomComparison.HomCxMap P P' L L' f g =
      Stacks.HomComplex.TensorHomMap.precomp R P' P L f ≫ Stacks.HomComplex.TensorHomMap.postcomp R
        P' L L' g := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro p q hpq
  show (Stacks.HomComplex.TensorHomComparison.HomCxMapDeg P P' L L' f g n z).v p q hpq =
    (((Cochain.ofHom f).comp z (zero_add n)).comp (Cochain.ofHom g) (add_zero n)).v p q hpq
  rw [Stacks.HomComplex.TensorHomComparison.HomCxMapDeg_v]
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private lemma homCxMap_id_left {R : Type u} [CommRing R]
    (P L L' : C R) (g : L ⟶ L') :
    Stacks.HomComplex.TensorHomComparison.HomCxMap P P L L' (𝟙 P) g =
      Stacks.HomComplex.TensorHomMap.postcomp R P L L' g := by
  rw [homCxMap_eq_precomp_postcomp, Stacks.HomComplex.TensorHomMap.precomp_id, Category.id_comp]

private lemma homCxMap_quasiIso {R : Type u} [CommRing R]
    (P : C R) [P.IsKProjective] {L I : C R} (i : L ⟶ I) [QuasiIso i] :
    QuasiIso (Stacks.HomComplex.TensorHomComparison.HomCxMap P P L I (𝟙 P) i) := by
  rw [homCxMap_id_left]
  exact postcomp_quasiIso_of_isKProjective i

private def homTargetFunctor {R : Type u} [CommRing R] (P : C R) : C R ⥤ C R where
  obj L := HomComplexR R P L
  map {L L'} g := Stacks.HomComplex.TensorHomComparison.HomCxMap P P L L' (𝟙 P) g
  map_id L := Stacks.HomComplex.TensorHomComparison.HomCxMap_id P L
  map_comp f g := by rw [← Stacks.HomComplex.TensorHomComparison.HomCxMap_comp, Category.id_comp]

private lemma homTargetFunctor_inverts {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (P : C R) [P.IsKProjective] :
    (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).IsInvertedBy
      (homTargetFunctor P ⋙ DerivedCategory.Q) := by
  intro L L' g hg
  have : QuasiIso g := hg
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mpr
    (homCxMap_quasiIso P g)

/-- After localization, postcomposition depends only on the derived morphism. -/
private lemma Q_homCxMap_eq {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (P : C R) [P.IsKProjective]
    {L L' : C R} (f g : L ⟶ L') (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap P P L L' (𝟙 P) f) =
      DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap P P L L' (𝟙 P) g) := by
  let F := homTargetFunctor P ⋙ DerivedCategory.Q (C := ModuleCat R)
  let e := Localization.fac F (homTargetFunctor_inverts P) DerivedCategory.Q
  show F.map f = F.map g
  apply (cancel_epi (e.hom.app L)).1
  rw [← e.hom.naturality f, ← e.hom.naturality g]
  show (Localization.lift F (homTargetFunctor_inverts P) DerivedCategory.Q).map
      (DerivedCategory.Q.map f) ≫ _ =
    (Localization.lift F (homTargetFunctor_inverts P) DerivedCategory.Q).map
      (DerivedCategory.Q.map g) ≫ _
  rw [h]

private structure InjectiveResolution {R : Type u} [CommRing R] (L : C R) where
  I : C R
  ι : L ⟶ I
  quasiIso : QuasiIso ι
  isKInjective : I.IsKInjective

attribute [local instance] InjectiveResolution.quasiIso InjectiveResolution.isKInjective

private def injectiveResolution {R : Type u} [CommRing R] (L : C R) :
    InjectiveResolution L := Classical.choice (by
  obtain ⟨I, i, hi, hI⟩ := CochainComplex.exists_quasiIso_isKInjective L
  exact ⟨⟨I, i, hi, hI⟩⟩)

private def comparisonIso {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (P L : C R) [P.IsKProjective] :
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.obj
        (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (HomComplexR R P L) := by
  let r := injectiveResolution L
  haveI := homCxMap_quasiIso P r.ι
  exact (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.mapIso
      (Iso.prod (Iso.refl _) (asIso (DerivedCategory.Q.map r.ι))) ≪≫
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).homIso P r.I ≪≫
    (asIso (DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap P P L r.I (𝟙 P)
      r.ι))).symm

/-- The chosen comparison commutes with its chosen resolution map. -/
private lemma comparisonIso_resolution {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (P L : C R) [P.IsKProjective] :
    (comparisonIso P L).hom ≫ DerivedCategory.Q.map
        (Stacks.HomComplex.TensorHomComparison.HomCxMap P P L (injectiveResolution L).I (𝟙 P)
          (injectiveResolution L).ι) =
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.map
          (𝟙 (Opposite.op (DerivedCategory.Q.obj P)),
            DerivedCategory.Q.map (injectiveResolution L).ι) ≫
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).homIso P (injectiveResolution
          L).I).hom := by
  have := homCxMap_quasiIso P (injectiveResolution L).ι
  simp [comparisonIso]

private lemma homIso_naturality {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] {P P' I I' : C R}
    [I.IsKInjective] [I'.IsKInjective] (f : P' ⟶ P) (g : I ⟶ I') :
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.map
        ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g) ≫
      ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).homIso P' I').hom =
    ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).homIso P I).hom ≫
      DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap P P' I I' f g) := by
  rw [homCxMap_eq_precomp_postcomp]
  exact (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).homIso_naturality f g

set_option backward.isDefEq.respectTransparency false in
private lemma comparisonIso_eq_homIso {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (P I : C R)
    [P.IsKProjective] [I.IsKInjective] :
    comparisonIso P I = (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).homIso P I := by
  have := homCxMap_quasiIso P (injectiveResolution I).ι
  apply Iso.ext
  apply (cancel_mono (DerivedCategory.Q.map
    (Stacks.HomComplex.TensorHomComparison.HomCxMap P P I (injectiveResolution I).I (𝟙 P)
      (injectiveResolution I).ι))).1
  rw [comparisonIso_resolution]
  simpa only [DerivedCategory.Q.map_id P, op_id] using
    homIso_naturality (𝟙 P) (injectiveResolution I).ι

set_option backward.isDefEq.respectTransparency false in
private lemma comparisonIso_naturality {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (P P' L L' : C R)
    [P.IsKProjective] [P'.IsKProjective] (f : P' ⟶ P) (g : L ⟶ L') :
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.map
        ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g) ≫
      (comparisonIso P' L').hom =
    (comparisonIso P L).hom ≫ DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap
      P P' L L' f g) := by
  let r := injectiveResolution L
  let s := injectiveResolution L'
  let H := (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom
  obtain ⟨k, hk⟩ := (Construction.Q_map_surjective_of_isKInjective r.I s.I)
    (inv (DerivedCategory.Q.map r.ι) ≫ DerivedCategory.Q.map g ≫ DerivedCategory.Q.map s.ι)
  have hsq : DerivedCategory.Q.map (r.ι ≫ k) = DerivedCategory.Q.map (g ≫ s.ι) := by
    simp only [Functor.map_comp, hk, IsIso.hom_inv_id_assoc]
  have hhom := congrArg
    (fun z => DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap P P' L L f (𝟙
      L)) ≫ z)
    (Q_homCxMap_eq P' (r.ι ≫ k) (g ≫ s.ι) hsq)
  simp only [← Functor.map_comp, ← Stacks.HomComplex.TensorHomComparison.HomCxMap_comp,
    Category.id_comp] at hhom
  have hD : H.map (show (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L) ⟶
          (Opposite.op (DerivedCategory.Q.obj P'), DerivedCategory.Q.obj L') from
        ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g)) ≫
        H.map (show (Opposite.op (DerivedCategory.Q.obj P'), DerivedCategory.Q.obj L') ⟶
          (Opposite.op (DerivedCategory.Q.obj P'), DerivedCategory.Q.obj s.I) from
        (𝟙 _, DerivedCategory.Q.map s.ι)) =
      H.map (show (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L) ⟶
          (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj r.I) from
        (𝟙 _, DerivedCategory.Q.map r.ι)) ≫
        H.map (show (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj r.I) ⟶
          (Opposite.op (DerivedCategory.Q.obj P'), DerivedCategory.Q.obj s.I) from
        ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map k)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    refine Prod.ext (by simp) ?_
    show DerivedCategory.Q.map g ≫ DerivedCategory.Q.map s.ι =
      DerivedCategory.Q.map r.ι ≫ DerivedCategory.Q.map k
    simpa only [← Functor.map_comp] using hsq.symm
  have := homCxMap_quasiIso P' s.ι
  apply (cancel_mono (DerivedCategory.Q.map
    (Stacks.HomComplex.TensorHomComparison.HomCxMap P' P' L' s.I (𝟙 P') s.ι))).1
  calc
    _ = H.map (show (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L) ⟶
          (Opposite.op (DerivedCategory.Q.obj P'), DerivedCategory.Q.obj L') from
        ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g)) ≫
        H.map (show (Opposite.op (DerivedCategory.Q.obj P'), DerivedCategory.Q.obj L') ⟶
          (Opposite.op (DerivedCategory.Q.obj P'), DerivedCategory.Q.obj s.I) from
        (𝟙 _, DerivedCategory.Q.map s.ι)) ≫
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).homIso P' s.I).hom := by
      rw [Category.assoc, comparisonIso_resolution]
    _ = H.map (show (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L) ⟶
          (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj r.I) from
        (𝟙 _, DerivedCategory.Q.map r.ι)) ≫
        H.map (show (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj r.I) ⟶
          (Opposite.op (DerivedCategory.Q.obj P'), DerivedCategory.Q.obj s.I) from
        ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map k)) ≫
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).homIso P' s.I).hom := by
      rw [← Category.assoc, hD, Category.assoc]
    _ = H.map (show (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L) ⟶
          (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj r.I) from
        (𝟙 _, DerivedCategory.Q.map r.ι)) ≫
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).homIso P r.I).hom ≫
        DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap P P' r.I s.I f k) :=
          by
      rw [homIso_naturality f k]
    _ = (comparisonIso P L).hom ≫
        DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap P P L r.I (𝟙 P) r.ι) ≫
        DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap P P' r.I s.I f k) :=
          by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap P P' r.I
          s.I f k))
        (comparisonIso_resolution P L).symm
    _ = (comparisonIso P L).hom ≫
        DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap P P' L s.I f (r.ι ≫
          k)) := by
      rw [← Functor.map_comp, ← Stacks.HomComplex.TensorHomComparison.HomCxMap_comp,
        Category.comp_id]
    _ = (comparisonIso P L).hom ≫
        DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap P P' L s.I f (g ≫
          s.ι)) := by
      rw [hhom]
    _ = _ := by
      rw [Category.assoc, ← Functor.map_comp, ← Stacks.HomComplex.TensorHomComparison.HomCxMap_comp,
        Category.id_comp]

/-- **Stacks 0A66.** A bounded-above complex of projective modules computes the derived
internal Hom against every target complex. The comparison is natural in both variables,
recovers the defining K-injective model, and hence is the comparison induced by a
K-injective resolution in the proof of the source lemma. -/
private def projectiveHomComparison {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] : ProjectiveHomComparison R where
  iso P L d _ _ := by
    letI := CochainComplex.isKProjective_of_projective P d
    exact comparisonIso P L
  naturality P P' L L' d d' _ _ _ _ f g := by
    let := CochainComplex.isKProjective_of_projective P d
    let := CochainComplex.isKProjective_of_projective P' d'
    exact comparisonIso_naturality P P' L L' f g
  iso_eq_homIso P I d _ _ _ := by
    let := CochainComplex.isKProjective_of_projective P d
    exact comparisonIso_eq_homIso P I


end ProjectiveComparison

/-! ### Two auxiliary computations -/

namespace CurryingAux

open CochainComplex HomComplex HomologicalComplex TensorProduct

/-- The cochain `Φ^n(β)` sends `y` to the image of `β ⊗ y` in the total complex. -/
private lemma Phiv_v_apply (R : Type u) [CommRing R]
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (β : K.X n)
    (p q : ℤ) (hpq : p + n = q) (y : L.X p) :
    ((Stacks.HomComplex.TensorHomMap.Phiv R K L n β).v p q hpq).hom y =
      (ιTensorObj K L n p q (by omega)).hom (β ⊗ₜ[R] y) := by
  rw [Stacks.HomComplex.TensorHomMap.Phiv_v]
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  congr 1

/-- The degree-zero transpose of a morphism of complexes, evaluated on a pure tensor. -/
private lemma curryIso_zero_apply {R : Type u} [CommRing R]
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ)
    (φ : K ⟶ CochainComplex.HomComplexR R L M) (r s t : ℤ) (hrs : r + s = t)
    (x : K.X r) (y : L.X s) :
    ((((Stacks.HomComplex.Currying.curryIso K L M).hom.f 0).hom
      (CochainComplex.HomComplex.Cochain.ofHom φ)).v t t (add_zero t)).hom
        ((HomologicalComplex.ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y)) =
      ((((CochainComplex.HomComplex.Cochain.ofHom φ).v r (r + 0)
        (by omega)).hom x).v s t (by omega)).hom y :=
  Stacks.HomComplex.Currying.curryIso_hom_apply K L M 0 r s t t hrs (add_zero t)
    (CochainComplex.HomComplex.Cochain.ofHom φ) x y

end CurryingAux

end Stacks.DerivedTensorHomDiagonal


namespace StacksDraft.DerivedHom

namespace DerivedInternalHom.Model

set_option backward.isDefEq.respectTransparency false

/-- Composition of derived internal Homs, precomposed with the tensor product of `a` and `b`, is
the transpose of the composite of `a`, precomposition with the transpose of `b`, and the inverse of
the currying isomorphism. -/
theorem composition_map {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat R)]
    {K L M A B : DerivedCategory (ModuleCat R)}
    (a : A ⟶ (hom R).obj (Opposite.op L, M))
    (b : B ⟶ (hom R).obj (Opposite.op K, L)) :
    (tensor R).map (a, b) ≫ composition K L M =
      homEquiv A B ((hom R).obj (Opposite.op K, M))
        (a ≫ (hom R).map ((homEquiv B K L b).op, 𝟙 M) ≫ (curryingIso B K M).inv) := by
  have hb : (tensor R).map (b, 𝟙 K) ≫ evaluation K L = homEquiv B K L b := by
    simpa only [evaluation, Category.comp_id] using
      ((adjunction R).homEquiv_naturality_left b (𝟙 _)).symm
  rw [← hb]
  have hm : (hom R).map (show (Opposite.op L, M) ⟶
      (Opposite.op ((tensor R).obj (B, K)), M) from
        (((tensor R).map (b, 𝟙 K) ≫ evaluation K L).op, 𝟙 M)) =
      (hom R).map (show (Opposite.op L, M) ⟶
        (Opposite.op ((tensor R).obj ((hom R).obj (Opposite.op K, L), K)), M) from
          ((evaluation K L).op, 𝟙 M)) ≫
        (hom R).map (show
          (Opposite.op ((tensor R).obj ((hom R).obj (Opposite.op K, L), K)), M) ⟶
          (Opposite.op ((tensor R).obj (B, K)), M) from
            (((tensor R).map (b, 𝟙 K)).op, 𝟙 M)) := by
    simp only [← Functor.map_comp, prod_comp, ← op_comp, Category.comp_id]
  rw [hm, Category.assoc, currying_inv_naturality_left,
    ← Category.assoc, ← Category.assoc, (adjunction R).homEquiv_dinaturality,
    (adjunction R).homEquiv_naturality_left]
  rw [composition, (adjunction R).homEquiv_naturality_left]
  simp only [← Category.assoc, (adjunction R).tensor_map_comp,
    Category.id_comp, Category.comp_id]

section Complexes

open CochainComplex HomComplex

variable {R : Type u} [CommRing R]

/-- The morphism of complexes `K ⊗ L ⟶ M` corresponding to a morphism `K ⟶ Hom(L, M)` under
currying. -/
def uncurry {K L M : CochainComplex (ModuleCat R) ℤ}
    (f : K ⟶ HomComplexR R L M) : K ⊗ L ⟶ M :=
  Cocycle.homOf (Cocycle.mk
    (((Stacks.HomComplex.Currying.curryIso K L M).hom.f 0).hom (Cochain.ofHom f))
    1 rfl (by
      have h := congrArg (fun k => k.hom (Cochain.ofHom f))
        ((Stacks.HomComplex.Currying.curryIso K L M).hom.comm 0 1)
      change δ 0 1 _ = 0
      change δ 0 1 (((Stacks.HomComplex.Currying.curryIso K L M).hom.f 0).hom
        (Cochain.ofHom f)) =
        ((Stacks.HomComplex.Currying.curryIso K L M).hom.f 1).hom (δ 0 1 (Cochain.ofHom f)) at h
      simpa only [δ_ofHom, map_zero] using h))

/-- The components of the cochain of a morphism `K ⟶ Hom(L, M)`, evaluated at `x`, are those of
the image of `x` in degree `n`. -/
lemma ofHom_apply_v {K L M : CochainComplex (ModuleCat R) ℤ}
    (f : K ⟶ HomComplexR R L M) (n m : ℤ) (hnm : n + 0 = m)
    (x : K.X n) (p q : ℤ) (hpq : p + m = q) :
    (((Cochain.ofHom f).v n m hnm).hom x).v p q hpq =
      ((f.f n).hom x).v p q (by omega) := by
  have hm : m = n := by omega
  subst hm
  rw [Cochain.ofHom_v]

/-- The uncurried morphism `uncurry f` sends the image of `x ⊗ y` to `f(x)(y)`. -/
lemma uncurry_apply {K L M : CochainComplex (ModuleCat R) ℤ}
    (f : K ⟶ HomComplexR R L M) (r s t : ℤ) (h : r + s = t)
    (x : K.X r) (y : L.X s) :
    (uncurry f).f t ((HomologicalComplex.ιTensorObj K L r s t h).hom (x ⊗ₜ[R] y)) =
      (((f.f r).hom x).v s t (by omega)).hom y := by
  convert! Stacks.DerivedTensorHomDiagonal.CurryingAux.curryIso_zero_apply K L M f r s t h x y using
    1
  exact congrArg (fun g : L.X s ⟶ M.X t => g.hom y)
    (ofHom_apply_v f r (r + 0) rfl x s t (by omega)).symm


/-- Postcomposition with `f : M ⟶ M'` sends a cochain `a` to the cochain with components
`a.v p q ≫ f.f q`. -/
lemma postcomp_apply {L M M' : CochainComplex (ModuleCat R) ℤ}
    (f : M ⟶ M') (n : ℤ) (a : Cochain L M n) (p q : ℤ) (hpq : p + n = q) :
    (((Stacks.HomComplex.TensorHomMap.postcomp R L M M' f).f n).hom a).v p q hpq =
      a.v p q hpq ≫ f.f q :=
  Cochain.comp_zero_cochain_v _ _ _ _ _

/-- Precomposition with `f : L' ⟶ L` sends a cochain `a` to the cochain with components
`f.f p ≫ a.v p q`. -/
lemma precomp_apply {L' L M : CochainComplex (ModuleCat R) ℤ}
    (f : L' ⟶ L) (n : ℤ) (a : Cochain L M n) (p q : ℤ) (hpq : p + n = q) :
    (((Stacks.HomComplex.TensorHomMap.precomp R L' L M f).f n).hom a).v p q hpq =
      f.f p ≫ a.v p q hpq :=
  Cochain.zero_cochain_comp_v _ _ _ _ _

/-- The unit `K ⟶ Hom(L, K ⊗ L)` followed by postcomposition with `uncurry f` is `f`. -/
lemma Phi_postcomp_uncurry {K L M : CochainComplex (ModuleCat R) ℤ}
    (f : K ⟶ HomComplexR R L M) :
    Stacks.HomComplex.TensorHomMap.Phi R K L ≫ Stacks.HomComplex.TensorHomMap.postcomp R L (K ⊗ L) M
      (uncurry f) = f := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Cochain.ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  show ((((Stacks.HomComplex.TensorHomMap.postcomp R L (K ⊗ L) M (uncurry f)).f n).hom
    (Stacks.HomComplex.TensorHomMap.Phiv R K L n x)).v p q hpq).hom y = _
  rw [postcomp_apply]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    Stacks.DerivedTensorHomDiagonal.CurryingAux.Phiv_v_apply,
    uncurry_apply]

/-- The tensor product `f ⊗ₘ g` sends the image of `x ⊗ y` to the image of `f x ⊗ g y`. -/
lemma tensorHom_apply {K K' L L' : CochainComplex (ModuleCat R) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') (p q n : ℤ) (h : p + q = n)
    (x : K.X p) (y : L.X q) :
    (f ⊗ₘ g).f n ((HomologicalComplex.ιTensorObj K L p q n h).hom (x ⊗ₜ[R] y)) =
      (HomologicalComplex.ιTensorObj K' L' p q n h).hom
        ((f.f p).hom x ⊗ₜ[R] (g.f q).hom y) :=
  congrArg (fun k => k.hom (x ⊗ₜ[R] y))
    (CochainComplex.ιTensorObj_tensorHom R f g p q n h)

/-- The composition map `Hom(L, M) ⊗ Hom(K, L) ⟶ Hom(K, M)` sends the image of `a ⊗ b` to the
composite cochain `b.comp a`. -/
lemma compMor_apply (K L M : CochainComplex (ModuleCat R) ℤ)
    (p q n : ℤ) (h : p + q = n) (a : Cochain L M p) (b : Cochain K L q) :
    (compMor K L M).f n
        ((HomologicalComplex.ιTensorObj (HomComplexR R L M) (HomComplexR R K L)
          p q n h).hom (a ⊗ₜ[R] b)) = b.comp a (by omega) :=
  compMor_tmul K L M p q n h a b

/-- Postcomposition with the identity of `L` is the identity of `Hom(K, L)`. -/
lemma postcomp_id (K L : CochainComplex (ModuleCat R) ℤ) :
    Stacks.HomComplex.TensorHomMap.postcomp R K L L (𝟙 L) = 𝟙 _ :=
  Stacks.HomComplex.TensorHomMap.postcomp_id R K L

/-- For `f : B ⟶ Hom(K, L)`, the unit `Hom(L, M) ⟶ Hom(B, Hom(L, M) ⊗ B)`, followed by
postcomposition with `(𝟙 ⊗ₘ f) ≫ compMor K L M` and the currying isomorphism, is precomposition
with `uncurry f : B ⊗ K ⟶ L`. -/
lemma Phi_postcomp_compMor_currying
    (K L M B : CochainComplex (ModuleCat R) ℤ) (f : B ⟶ HomComplexR R K L) :
    Stacks.HomComplex.TensorHomMap.Phi R (HomComplexR R L M) B ≫
        Stacks.HomComplex.TensorHomMap.postcomp R B (HomComplexR R L M ⊗ B) (HomComplexR R K M)
          ((𝟙 (HomComplexR R L M) ⊗ₘ f) ≫ compMor K L M) ≫
        (Stacks.HomComplex.Currying.curryIso B K M).hom =
      Stacks.HomComplex.TensorHomMap.precomp R (B ⊗ K) L M (uncurry f) := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply Cochain.ext
  intro p q hpq
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro r s hrs
  change r + s = p at hrs
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  show ((((Stacks.HomComplex.Currying.curryIso B K M).hom.f n).hom
    (((Stacks.HomComplex.TensorHomMap.postcomp R B (HomComplexR R L M ⊗ B) (HomComplexR R K M)
      ((𝟙 (HomComplexR R L M) ⊗ₘ f) ≫ compMor K L M)).f n).hom
        (Stacks.HomComplex.TensorHomMap.Phiv R (HomComplexR R L M) B n a))).v p q hpq).hom
      ((HomologicalComplex.ιTensorObj B K r s p hrs).hom (x ⊗ₜ[R] y)) =
    ((((Stacks.HomComplex.TensorHomMap.precomp R (B ⊗ K) L M (uncurry f)).f n).hom a).v p q hpq).hom
      ((HomologicalComplex.ιTensorObj B K r s p hrs).hom (x ⊗ₜ[R] y))
  erw [Stacks.HomComplex.Currying.curryIso_hom_apply,
    postcomp_apply, precomp_apply]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    Stacks.DerivedTensorHomDiagonal.CurryingAux.Phiv_v_apply,
    HomologicalComplex.comp_f, tensorHom_apply, HomologicalComplex.id_f,
    ModuleCat.id_apply, uncurry_apply]
  erw [compMor_apply, Cochain.comp_v _ _ _ s p q (by omega) hpq]
  rfl

set_option maxHeartbeats 800000 in
-- Tensor generators require reducing the total-complex module instances.
private lemma compMor_precomp (K K' L I : CochainComplex (ModuleCat R) ℤ)
    (f : K' ⟶ K) :
    (𝟙 (HomComplexR R L I) ⊗ₘ Stacks.HomComplex.TensorHomMap.precomp R K' K L f) ≫ compMor K' L I =
      compMor K L I ≫ Stacks.HomComplex.TensorHomMap.precomp R K' K I f := by
  ext n : 1
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  show (compMor K' L I).f n
    ((𝟙 (HomComplexR R L I) ⊗ₘ Stacks.HomComplex.TensorHomMap.precomp R K' K L f).f n
      ((HomologicalComplex.ιTensorObj (HomComplexR R L I) (HomComplexR R K L)
        p q n hpq).hom (a ⊗ₜ[R] b))) =
    (Stacks.HomComplex.TensorHomMap.precomp R K' K I f).f n
      ((compMor K L I).f n
        ((HomologicalComplex.ιTensorObj (HomComplexR R L I) (HomComplexR R K L)
          p q n hpq).hom (a ⊗ₜ[R] b)))
  rw [tensorHom_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  erw [compMor_apply, compMor_apply]
  exact Cochain.comp_assoc_of_first_is_zero_cochain (Cochain.ofHom f) b a (by omega)

/-- The tensor--Hom chain map `theta` is the unit `K ⟶ Hom(L, K ⊗ L)`, tensored with
`Hom(M, L)`, followed by composition. -/
lemma Phi_tensor_compMor (K L M : CochainComplex (ModuleCat R) ℤ) :
    (Stacks.HomComplex.TensorHomMap.Phi R K L ⊗ₘ 𝟙 (HomComplexR R M L)) ≫ compMor M L (K ⊗ L) =
      Stacks.HomComplex.TensorHomComparison.theta K L M := by
  ext n : 1
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x a
  show (compMor M L (K ⊗ L)).f n
    ((Stacks.HomComplex.TensorHomMap.Phi R K L ⊗ₘ 𝟙 (HomComplexR R M L)).f n
      ((HomologicalComplex.ιTensorObj K (HomComplexR R M L) p q n hpq).hom
        (x ⊗ₜ[R] a))) =
    (Stacks.HomComplex.TensorHomComparison.theta K L M).f n
      ((HomologicalComplex.ιTensorObj K (HomComplexR R M L) p q n hpq).hom
        (x ⊗ₜ[R] a))
  rw [tensorHom_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  erw [compMor_apply]
  apply Cochain.ext
  intro r s hrs
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rw [Cochain.comp_v _ _ _ r (s - p) s (by omega) (by omega)]
  show ((Stacks.HomComplex.TensorHomMap.Phiv R K L p x).v (s - p) s (by omega)).hom
    ((a.v r (s - p) (by omega)).hom y) = _
  rw [Stacks.DerivedTensorHomDiagonal.CurryingAux.Phiv_v_apply]
  exact (Stacks.HomComplex.TensorHomComparison.theta_apply K L M n p q hpq x a r s hrs y).symm

end Complexes

end DerivedInternalHom.Model

end StacksDraft.DerivedHom

end
