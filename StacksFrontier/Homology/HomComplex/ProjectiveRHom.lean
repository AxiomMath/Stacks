module

public import StacksFrontier.Homology.HomComplex.DerivedAdjunction

/-!
# Derived Hom out of a bounded above complex of projectives

Let `R` be a commutative ring. For a bounded above cochain complex `P` of projective `R`-modules
and an arbitrary cochain complex `L`, the `R`-linear Hom complex `Hom^•(P, L)` represents the
derived internal Hom `RHom(P, L)` of [stacks 0A63]: there is an isomorphism
`RHom(P, L) ≅ Hom^•(P, L)` in `D(R)`, natural in both variables for the functorial maps of Hom
complexes, which on a K-injective target is the defining K-injective comparison of the derived
tensor--Hom adjunction.

This is the *bifunctor* form of [stacks 0A66]. It is a different statement from the cohomological
form proved in `StacksFrontier.Homology.HomComplex.RHom`: there the comparison is an isomorphism of
abelian groups `Hⁿ(Hom^•(P, L)) ≃+ Hom_{D(R)}(P, L⟦n⟧)` for each `n`, here it is an isomorphism of
*objects of the derived category* compatible with the fixed adjunction, which is what consumers
that manipulate `RHom` as an object -- duality for perfect complexes, for instance -- require.
Neither form implies the other formally, so both belong to the covering set of the tag.

## Main definitions

* `StacksDraft.DerivedHom.ProjectiveHomComparison`: the comparison isomorphisms, their naturality
  for `Stacks.HomComplex.TensorHomComparison.HomCxMap`, and their compatibility with
    `DerivedHomData.homIso`.

## Main results

* `StacksDraft.DerivedHom.projectiveHomComparison` ([stacks 0A66]): the canonical comparison with
  the fixed derived internal-Hom bifunctor of [stacks 0A63], for bounded above projective sources
  and arbitrary targets.
* `StacksDraft.DerivedHom.projectiveHomComparisonULift` ([stacks 0A66]): the same comparison in an
  independently chosen module universe, over the canonically isomorphic lifted scalar ring.
* `StacksDraft.DerivedHom.ProjectiveHomComparison.resolution_comparison`: the comparison square
  for a map to a K-injective target, which is how the comparison is computed.
* `StacksDraft.DerivedHom.ProjectiveHomComparison.quasiIso_homCxMap`: Hom out of a bounded above
  complex of projectives preserves quasi-isomorphisms.

## Implementation notes

The comparison is constructed from the K-injective comparison `DerivedHomData.homIso` of the fixed
adjunction by transporting along a K-injective resolution of the target; that this is legitimate
is the statement that `Hom^•(P, -)` preserves quasi-isomorphisms for `P` K-projective, which is
proved here through the explicit cohomology classes of Hom complexes. Because the construction
uses a chosen resolution, its value is opaque (`no_expose`) and everything one needs to know about
it is in the three fields of `ProjectiveHomComparison`.

The existing monoidal constructions on complexes force the ring and module universes to agree, so
as in [stacks 0A63] the lifted ring `ULift R` provides the version with an independently chosen
module universe.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A66](https://stacks.math.columbia.edu/tag/0A66)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u w

namespace StacksDraft.DerivedHom

/-- The natural comparison with the `R`-linear Hom complex for bounded-above projective
sources. The derived-Hom bifunctor is the fixed construction of 0A63, not extra data supplied
as a hypothesis. The target complex has no boundedness, flatness, or injectivity hypothesis. -/
structure ProjectiveHomComparison (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] where
  /-- The Hom complex represents the derived internal Hom. -/
  iso (P L : CochainComplex (ModuleCat.{u} R) ℤ) (d : ℤ) [P.IsStrictlyLE d]
      [∀ i, Projective (P.X i)] :
    (derivedHomAdjunction (R := R)).hom.obj
        (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (CochainComplex.HomComplexR R P L)
  /-- Contravariant naturality in the projective source and covariant naturality in the
  arbitrary target, for the actual functorial maps of Hom complexes. -/
  naturality (P P' L L' : CochainComplex (ModuleCat.{u} R) ℤ) (d d' : ℤ)
      [P.IsStrictlyLE d] [P'.IsStrictlyLE d']
      [∀ i, Projective (P.X i)] [∀ i, Projective (P'.X i)]
      (f : P' ⟶ P) (g : L ⟶ L') :
    (derivedHomAdjunction (R := R)).hom.map
          ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g) ≫
        (iso P' L' d').hom =
      (iso P L d).hom ≫ DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap P P' L
        L' f g)
  /-- On a K-injective target this is the defining comparison of 0A63. -/
  iso_eq_homIso (P I : CochainComplex (ModuleCat.{u} R) ℤ) (d : ℤ)
      [P.IsStrictlyLE d] [∀ i, Projective (P.X i)] [I.IsKInjective] :
    iso P I d = (derivedHomAdjunction (R := R)).homIso P I

namespace ProjectiveHomComparison

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The comparison square used in the source proof, for a map to a K-injective target.
In particular it applies to every K-injective resolution of the arbitrary target complex. -/
theorem resolution_comparison (e : ProjectiveHomComparison R)
    (P L I : CochainComplex (ModuleCat.{u} R) ℤ) (d : ℤ)
    [P.IsStrictlyLE d] [∀ i, Projective (P.X i)] [I.IsKInjective] (f : L ⟶ I) :
    (e.iso P L d).hom ≫
        DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap P P L I (𝟙 P) f) =
      (derivedHomAdjunction (R := R)).hom.map
          (𝟙 (Opposite.op (DerivedCategory.Q.obj P)), DerivedCategory.Q.map f) ≫
        ((derivedHomAdjunction (R := R)).homIso P I).hom := by
  simpa only [e.iso_eq_homIso, DerivedCategory.Q.map_id P, op_id] using
    (e.naturality P P L I d d (𝟙 P) f).symm

/-- Hom out of a bounded-above projective complex preserves quasi-isomorphisms.
This includes the map to a K-injective resolution used in the proof of Stacks 0A66. -/
theorem quasiIso_homCxMap (e : ProjectiveHomComparison R)
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

private abbrev Cx (R : Type u) [CommRing R] := CochainComplex (ModuleCat.{u} R) ℤ

open CochainComplex HomComplex

private lemma postcomp_quasiIso_of_isKProjective {R : Type u} [CommRing R]
    {P L L' : Cx R} [P.IsKProjective] (f : L ⟶ L') [QuasiIso f] :
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
    (P P' L L' : Cx R) (f : P' ⟶ P) (g : L ⟶ L') :
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
    (P L L' : Cx R) (g : L ⟶ L') :
    Stacks.HomComplex.TensorHomComparison.HomCxMap P P L L' (𝟙 P) g =
      Stacks.HomComplex.TensorHomMap.postcomp R P L L' g := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro p q hpq
  show (Stacks.HomComplex.TensorHomComparison.HomCxMapDeg P P L L' (𝟙 P) g n z).v p q hpq =
    (z.comp (Cochain.ofHom g) (add_zero n)).v p q hpq
  rw [Stacks.HomComplex.TensorHomComparison.HomCxMapDeg_v]
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    HomologicalComplex.id_f, Category.id_comp]

private lemma homCxMap_quasiIso {R : Type u} [CommRing R]
    (P : Cx R) [P.IsKProjective] {L I : Cx R} (i : L ⟶ I) [QuasiIso i] :
    QuasiIso (Stacks.HomComplex.TensorHomComparison.HomCxMap P P L I (𝟙 P) i) := by
  rw [homCxMap_id_left]
  exact postcomp_quasiIso_of_isKProjective i

private def homTargetFunctor {R : Type u} [CommRing R] (P : Cx R) : Cx R ⥤ Cx R where
  obj L := HomComplexR R P L
  map {L L'} g := Stacks.HomComplex.TensorHomComparison.HomCxMap P P L L' (𝟙 P) g
  map_id L := Stacks.HomComplex.TensorHomComparison.HomCxMap_id P L
  map_comp f g := by rw [← Stacks.HomComplex.TensorHomComparison.HomCxMap_comp, Category.id_comp]

private lemma homTargetFunctor_inverts {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (P : Cx R) [P.IsKProjective] :
    (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).IsInvertedBy
      (homTargetFunctor P ⋙ DerivedCategory.Q) := by
  intro L L' g hg
  have : QuasiIso g := hg
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mpr (homCxMap_quasiIso P g)

/-- After localization, postcomposition depends only on the derived morphism. -/
private lemma Q_homCxMap_eq {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (P : Cx R) [P.IsKProjective]
    {L L' : Cx R} (f g : L ⟶ L') (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
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

private structure InjectiveResolution {R : Type u} [CommRing R] (L : Cx R) where
  I : Cx R
  ι : L ⟶ I
  quasiIso : QuasiIso ι
  isKInjective : I.IsKInjective

attribute [local instance] InjectiveResolution.quasiIso InjectiveResolution.isKInjective

private def injectiveResolution {R : Type u} [CommRing R] (L : Cx R) :
    InjectiveResolution L := Classical.choice (by
  obtain ⟨I, i, hi, hI⟩ := CochainComplex.exists_quasiIso_isKInjective L
  exact ⟨⟨I, i, hi, hI⟩⟩)

private def comparisonIso {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (P L : Cx R) [P.IsKProjective] :
    (derivedHomAdjunction (R := R)).hom.obj
        (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (HomComplexR R P L) := by
  let r := injectiveResolution L
  haveI := homCxMap_quasiIso P r.ι
  exact (derivedHomAdjunction (R := R)).hom.mapIso
      (Iso.prod (Iso.refl _) (asIso (DerivedCategory.Q.map r.ι))) ≪≫
    (derivedHomAdjunction (R := R)).homIso P r.I ≪≫
    (asIso (DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap P P L r.I (𝟙 P)
      r.ι))).symm

/-- The chosen comparison commutes with its chosen resolution map. -/
private lemma comparisonIso_resolution {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (P L : Cx R) [P.IsKProjective] :
    (comparisonIso P L).hom ≫ DerivedCategory.Q.map
        (Stacks.HomComplex.TensorHomComparison.HomCxMap P P L (injectiveResolution L).I (𝟙 P)
          (injectiveResolution L).ι) =
      (derivedHomAdjunction (R := R)).hom.map
          (𝟙 (Opposite.op (DerivedCategory.Q.obj P)),
            DerivedCategory.Q.map (injectiveResolution L).ι) ≫
        ((derivedHomAdjunction (R := R)).homIso P (injectiveResolution L).I).hom := by
  have := homCxMap_quasiIso P (injectiveResolution L).ι
  simp [comparisonIso]

private lemma homIso_naturality {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] {P P' I I' : Cx R}
    [I.IsKInjective] [I'.IsKInjective] (f : P' ⟶ P) (g : I ⟶ I') :
    (derivedHomAdjunction (R := R)).hom.map
        ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g) ≫
      ((derivedHomAdjunction (R := R)).homIso P' I').hom =
    ((derivedHomAdjunction (R := R)).homIso P I).hom ≫
      DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap P P' I I' f g) := by
  rw [homCxMap_eq_precomp_postcomp]
  exact (derivedHomAdjunction (R := R)).homIso_naturality f g

set_option backward.isDefEq.respectTransparency false in
private lemma comparisonIso_eq_homIso {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (P I : Cx R)
    [P.IsKProjective] [I.IsKInjective] :
    comparisonIso P I = (derivedHomAdjunction (R := R)).homIso P I := by
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
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (P P' L L' : Cx R)
    [P.IsKProjective] [P'.IsKProjective] (f : P' ⟶ P) (g : L ⟶ L') :
    (derivedHomAdjunction (R := R)).hom.map
        ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g) ≫
      (comparisonIso P' L').hom =
    (comparisonIso P L).hom ≫ DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap
      P P' L L' f g) := by
  let r := injectiveResolution L
  let s := injectiveResolution L'
  let H := (derivedHomAdjunction (R := R)).hom
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
        ((derivedHomAdjunction (R := R)).homIso P' s.I).hom := by
      rw [Category.assoc, comparisonIso_resolution]
    _ = H.map (show (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L) ⟶
          (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj r.I) from
        (𝟙 _, DerivedCategory.Q.map r.ι)) ≫
        H.map (show (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj r.I) ⟶
          (Opposite.op (DerivedCategory.Q.obj P'), DerivedCategory.Q.obj s.I) from
        ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map k)) ≫
        ((derivedHomAdjunction (R := R)).homIso P' s.I).hom := by
      rw [← Category.assoc, hD, Category.assoc]
    _ = H.map (show (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L) ⟶
          (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj r.I) from
        (𝟙 _, DerivedCategory.Q.map r.ι)) ≫
        ((derivedHomAdjunction (R := R)).homIso P r.I).hom ≫
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
@[stacks 0A66, no_expose]
def projectiveHomComparison {R : Type u} [CommRing R]
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

/-- The comparison of Stacks 0A66 in an independently chosen module universe. The lifted
ring is canonically isomorphic to `R`, and retains all naturality and model comparisons. -/
@[stacks 0A66]
abbrev projectiveHomComparisonULift {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} (ULift.{v} R))] :
    ProjectiveHomComparison (ULift.{v} R) :=
  projectiveHomComparison

end StacksDraft.DerivedHom

end
