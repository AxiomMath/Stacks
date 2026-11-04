module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtaleConstruction.Cardinality
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtaleConstruction.EtalePushout
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtaleConstruction.FiniteStage

/-!
# The colimit of `A → T(A) → T²(A) → ⋯` splits every faithfully flat étale cover

Each stage of the sequence obtained by iterating the splitting construction `T` is a faithfully
flat ind-étale `A`-algebra, hence so is the colimit `C`. A faithfully flat étale `C`-algebra `B`
is, by the spreading-out statement for étale maps out of a filtered colimit, the base change of a
faithfully flat étale algebra `Z` over one of the stages `Tⁿ(A)`; that `Z` maps to `Tⁿ⁺¹(A)` by
construction of `T`, and the resulting map `Z → C` over `Tⁿ(A)` descends to a retraction
of `C → B`.

Together with the cardinality bound this gives the bounded form of the construction: for every
infinite cardinal `k` bounding `#A` there is a faithfully flat ind-étale `A`-algebra `C` of
cardinality at most `k` over which every faithfully flat étale cover splits.

## Main results

* `AlgebraicGeometry.ProEtale.iteratedSplittingColimit_splits_etale`
* `AlgebraicGeometry.ProEtale.exists_small_faithfullyFlat_ind_etale_algebra_splitting_etale`

## Implementation notes

The sequence of iterated splitting rings is defined in `CommRingCat`, but ind-étaleness over `A`
is a statement about `CommAlgCat A`, so the same sequence is built a second time as a diagram of
`A`-algebras and the two are identified by `iteratedSplitting_diagram_map_compat`. The `A`-algebra
structure on the colimit is the one induced by the first coprojection.

## References

* [Stacks Project, Tag 097S](https://stacks.math.columbia.edu/tag/097S)
-/

open Cardinal CategoryTheory CategoryTheory.Limits

@[expose] public section

namespace AlgebraicGeometry.ProEtale

universe u

/-- The `A`-algebra structure on the `n`-th iterated splitting ring of `A`. -/
@[instance_reducible]
private noncomputable def iteratedSplittingAlgebra (A : Type u) [CommRing A] :
    (n : ℕ) → Algebra A (iteratedSplittingRing (CommRingCat.of A) n)
  | 0 => by
      change Algebra A A
      infer_instance
  | n + 1 => by
      letI : Algebra A (iteratedSplittingRing (CommRingCat.of A) n) :=
        iteratedSplittingAlgebra A n
      change Algebra A (splittingAlgebra (iteratedSplittingRing (CommRingCat.of A) n))
      exact Algebra.compHom _
        (algebraMap A (iteratedSplittingRing (CommRingCat.of A) n))

/-- The `n`-th iterated splitting ring of `A`, as an object of `CommAlgCat A`. -/
private noncomputable def iteratedSplittingAlgObject (A : Type u) [CommRing A]
    (n : ℕ) : CommAlgCat.{u} A := by
  letI := iteratedSplittingAlgebra A n
  exact CommAlgCat.of A (iteratedSplittingRing (CommRingCat.of A) n)

/-- A transition map of the sequence of iterated splitting rings, as a map of `A`-algebras. -/
private noncomputable def iteratedSplittingAlgMap (A : Type u) [CommRing A] (n : ℕ) :
    iteratedSplittingAlgObject A n ⟶ iteratedSplittingAlgObject A (n + 1) := by
  letI : Algebra A (iteratedSplittingRing (CommRingCat.of A) n) :=
    iteratedSplittingAlgebra A n
  letI : Algebra A (iteratedSplittingRing (CommRingCat.of A) (n + 1)) :=
    iteratedSplittingAlgebra A (n + 1)
  exact CommAlgCat.ofHom
    { toRingHom := (iteratedSplittingMap (CommRingCat.of A) n).hom
      commutes' := by
        intro a
        change (algebraMap (iteratedSplittingRing (CommRingCat.of A) n)
            (splittingAlgebra (iteratedSplittingRing (CommRingCat.of A) n)))
          (algebraMap A (iteratedSplittingRing (CommRingCat.of A) n) a) =
            algebraMap A (splittingAlgebra (iteratedSplittingRing (CommRingCat.of A) n)) a
        rfl }

/-- The sequence `A → T(A) → T²(A) → ⋯` as a diagram of `A`-algebras. -/
private noncomputable def iteratedSplittingAlgDiagram (A : Type u) [CommRing A] :
    ℕ ⥤ CommAlgCat.{u} A :=
  Functor.ofSequence (iteratedSplittingAlgMap A)

/-- Every stage of the sequence `A → T(A) → T²(A) → ⋯` is an ind-étale `A`-algebra. -/
private lemma iteratedSplitting_ind_etale (A : Type u) [CommRing A] :
    ∀ n : ℕ, (CommAlgCat.etale A).ind.{u} (iteratedSplittingAlgObject A n) := by
  intro n
  induction n with
  | zero =>
      show (CommAlgCat.etale A).ind.{u} (CommAlgCat.of A A)
      apply ObjectProperty.le_ind
      exact inferInstance
  | succ n ih =>
      let B := iteratedSplittingRing (CommRingCat.of A) n
      let : Algebra A B := iteratedSplittingAlgebra A n
      let : Algebra A (splittingAlgebra B) := iteratedSplittingAlgebra A (n + 1)
      let : SMul A (splittingAlgebra B) := (iteratedSplittingAlgebra A (n + 1)).toSMul
      let : IsScalarTower A B (splittingAlgebra B) :=
        IsScalarTower.of_algebraMap_smul (by intro a x; rfl)
      have hB : (CommAlgCat.etale A).ind.{u} (CommAlgCat.of A B) := by
        simpa [B, iteratedSplittingAlgObject] using ih
      show (CommAlgCat.etale A).ind.{u} (CommAlgCat.of A (splittingAlgebra B))
      exact CommAlgCat.ind_etale_comp (A := A) (B := B) (C := splittingAlgebra B)
        hB (splittingAlgebra_ind_etale B)

/-- A transition map of the sequence of iterated splitting rings is the canonical map `A → T(A)`. -/
private lemma iteratedSplittingDiagram_map_succ (A : CommRingCat.{u}) (k : ℕ) :
    (iteratedSplittingDiagram A).map (homOfLE (Nat.le_add_right k 1)) =
      toSplittingRing (iteratedSplittingRing A k) := by
  simp only [iteratedSplittingDiagram, Functor.ofSequence_map_homOfLE_succ]
  rfl

/-- The sequence of iterated splitting rings and its `A`-algebra refinement have the same
transition maps. -/
private lemma iteratedSplitting_diagram_map_compat (A : Type u) [CommRing A]
    (i j : ℕ) (h : i ≤ j) :
    ((iteratedSplittingDiagram (CommRingCat.of A)).map (homOfLE h)).hom =
      (((iteratedSplittingAlgDiagram A).map (homOfLE h)).hom.toRingHom) := by
  let D := iteratedSplittingDiagram (CommRingCat.of A)
  let F := iteratedSplittingAlgDiagram A
  have hstep (k : ℕ) : (D.map (homOfLE (Nat.le_add_right k 1))).hom =
      (F.map (homOfLE (Nat.le_add_right k 1))).hom.toRingHom := by
    simp only [D, F, iteratedSplittingDiagram_map_succ, iteratedSplittingAlgDiagram,
      Functor.ofSequence_map_homOfLE_succ]
    rfl
  induction j generalizing i with
  | zero =>
      obtain rfl : i = 0 := Nat.eq_zero_of_le_zero h
      have hid : (homOfLE h : (0 : ℕ) ⟶ 0) = 𝟙 _ := Subsingleton.elim _ _
      rw [hid, D.map_id, F.map_id]
      rfl
  | succ j ih =>
      by_cases hij : i ≤ j
      · have hu : (homOfLE h : i ⟶ j + 1) =
            (homOfLE hij : i ⟶ j) ≫ homOfLE (Nat.le_add_right j 1) :=
          Subsingleton.elim _ _
        rw [hu, D.map_comp, F.map_comp]
        ext x
        show (D.map (homOfLE (Nat.le_add_right j 1))).hom
            ((D.map (homOfLE hij)).hom x) =
          (F.map (homOfLE (Nat.le_add_right j 1))).hom.toRingHom
            ((F.map (homOfLE hij)).hom.toRingHom x)
        rw [hstep j, ih i hij]
        rfl
      · obtain rfl : i = j + 1 := by omega
        have hid : (homOfLE h : (j + 1) ⟶ j + 1) = 𝟙 _ := Subsingleton.elim _ _
        rw [hid, D.map_id, F.map_id]
        rfl

/-- The cocone on the diagram of `A`-algebra stages whose vertex is the colimit taken in
`CommRingCat`. -/
private noncomputable def iteratedSplittingAlgCocone (A : Type u) [CommRing A] :
    Cocone (iteratedSplittingAlgDiagram A) := by
  let D := iteratedSplittingDiagram (CommRingCat.of A)
  let F := iteratedSplittingAlgDiagram A
  let c := colimit.cocone D
  letI : Algebra A (iteratedSplittingColimit (CommRingCat.of A)) :=
    (colimit.ι D 0).hom.toAlgebra
  refine
    { pt := CommAlgCat.of A (iteratedSplittingColimit (CommRingCat.of A))
      ι :=
        { app := fun n ↦ by
            letI : Algebra A (iteratedSplittingRing (CommRingCat.of A) n) :=
              iteratedSplittingAlgebra A n
            refine CommAlgCat.ofHom
              { toRingHom := (colimit.ι D n).hom
                commutes' := ?_ }
            intro a
            let u : (0 : ℕ) ⟶ n := homOfLE (Nat.zero_le n)
            let : Algebra A (iteratedSplittingRing (CommRingCat.of A) 0) :=
              iteratedSplittingAlgebra A 0
            have hmap : (F.map u).hom.toRingHom
                (algebraMap A (iteratedSplittingRing (CommRingCat.of A) 0) a) =
                  algebraMap A (iteratedSplittingRing (CommRingCat.of A) n) a :=
              (F.map u).hom.commutes a
            have hnat := congrArg (fun f : CommRingCat.Hom _ _ ↦ f.hom a) (c.w u)
            change (colimit.ι D n).hom ((D.map u).hom a) = (colimit.ι D 0).hom a at hnat
            rw [iteratedSplitting_diagram_map_compat A 0 n (Nat.zero_le n)] at hnat
            change (colimit.ι D n).hom (algebraMap A
              (iteratedSplittingRing (CommRingCat.of A) n) a) = (colimit.ι D 0).hom a
            rwa [← hmap]
          naturality := ?_ } }
  intro i j f
  apply CommAlgCat.hom_ext
  ext x
  let xR : D.obj i := x
  have hf : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
  have hnat := congrArg (fun g : CommRingCat.Hom _ _ ↦ g.hom xR) (c.w f)
  change (colimit.ι D j).hom ((D.map f).hom xR) = (colimit.ι D i).hom xR at hnat
  have hD : (D.map f).hom = (F.map f).hom.toRingHom := by
    rw [hf]
    simpa [D, F] using iteratedSplitting_diagram_map_compat A i j (leOfHom f)
  rw [hD] at hnat
  change (colimit.ι D j).hom ((F.map f).hom.toRingHom xR) = (colimit.ι D i).hom xR
  exact hnat

/-- The cocone of `iteratedSplittingAlgCocone` is a colimit: the forgetful functor to
`CommRingCat` preserves and reflects sequential colimits. -/
private noncomputable def iteratedSplittingAlgCocone_isColimit (A : Type u) [CommRing A] :
    IsColimit (iteratedSplittingAlgCocone A) := by
  let D := iteratedSplittingDiagram (CommRingCat.of A)
  let U := forget₂ (CommAlgCat.{u} A) CommRingCat.{u}
  let F := iteratedSplittingAlgDiagram A
  letI : IsFiltered ℕ := inferInstance
  letI : PreservesFilteredColimitsOfSize.{u, u} U :=
    preservesFilteredColimits_forget₂_commAlgCat A
  letI : PreservesFilteredColimitsOfSize.{0, 0} U :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits.{u, u} U
  letI : PreservesColimitsOfShape ℕ U :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits ℕ
  letI : ReflectsColimitsOfShape ℕ U :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms (J := ℕ) (G := U)
  let e : F ⋙ U ≅ D := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro i j f
    have hf : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
    rw [hf]
    simp only [Functor.comp_map]
    apply CommRingCat.hom_ext
    change (F.map (homOfLE (leOfHom f))).hom.toRingHom =
      (D.map (homOfLE (leOfHom f))).hom
    exact (iteratedSplitting_diagram_map_compat A i j (leOfHom f)).symm)
  let c := colimit.cocone D
  let c' := (Cocone.precompose e.hom).obj c
  have hc' : IsColimit c' := (IsColimit.precomposeHomEquiv e c).symm
    (colimit.isColimit D)
  have hIso : U.mapCocone (iteratedSplittingAlgCocone A) ≅ c' :=
    Cocone.ext (Iso.refl _) (fun _ ↦ by
      apply CommRingCat.hom_ext
      ext x
      rfl)
  exact isColimitOfReflects U (IsColimit.ofIsoColimit hc' hIso.symm)

/-- The colimit of the sequence of iterated splitting rings is an ind-étale `A`-algebra. -/
lemma iteratedSplittingColimit_ind_etale (A : Type u) [CommRing A] :
    letI : Algebra A (iteratedSplittingColimit (CommRingCat.of A)) :=
      (colimit.ι (iteratedSplittingDiagram (CommRingCat.of A)) 0).hom.toAlgebra
    (CommAlgCat.etale A).ind.{u}
      (CommAlgCat.of A (iteratedSplittingColimit (CommRingCat.of A))) := by
  let : IsFiltered ℕ := inferInstance
  let : Algebra A (iteratedSplittingColimit (CommRingCat.of A)) :=
    (colimit.ι (iteratedSplittingDiagram (CommRingCat.of A)) 0).hom.toAlgebra
  have hfin : (CommAlgCat.etale A) ≤
      ObjectProperty.isFinitelyPresentable.{u} (CommAlgCat.{u} A) :=
    fun X hX ↦ etale_isFinitelyPresentable A X hX
  have h : ((CommAlgCat.etale A).ind.{u}).ind.{u}
      (CommAlgCat.of A (iteratedSplittingColimit (CommRingCat.of A))) := by
    let E : ℕ ≌ AsSmall.{u} ℕ := AsSmall.equiv
    let c := iteratedSplittingAlgCocone A
    have : E.inverse.IsEquivalence := E.isEquivalence_inverse
    have : E.inverse.Final := inferInstance
    exact ObjectProperty.of_essentiallySmall_index
      { diag := E.inverse ⋙ iteratedSplittingAlgDiagram A
        ι := (c.whisker E.inverse).ι
        isColimit := (Functor.Final.isColimitWhiskerEquiv E.inverse _).symm
          (iteratedSplittingAlgCocone_isColimit A) }
      (fun n ↦ iteratedSplitting_ind_etale A (ULift.down n))
  rwa [ObjectProperty.ind_ind hfin] at h

/-- Every coprojection into the colimit of the sequence of iterated splitting rings is faithfully
flat. -/
lemma iteratedSplittingColimit_leg_faithfullyFlat (A : Type u) [CommRing A] (n : ℕ) :
    ((colimit.ι (iteratedSplittingDiagram (CommRingCat.of A)) n).hom).FaithfullyFlat := by
  let F := iteratedSplittingDiagram (CommRingCat.of A)
  have hstep (k : ℕ) :
      (F.map (homOfLE (Nat.le_add_right k 1))).hom.FaithfullyFlat := by
    rw [iteratedSplittingDiagram_map_succ]
    exact splittingAlgebra_faithfullyFlat _
  have hAll (i : ℕ) (j : Under i) : (F.map j.hom).hom.FaithfullyFlat := by
    have hj : j.hom = homOfLE (leOfHom j.hom) := Subsingleton.elim _ _
    rw [hj]
    exact sequence_map_faithfullyFlat F hstep i j.right (leOfHom j.hom)
  exact faithfullyFlat_colimit_leg F (colimit.cocone F) (colimit.isColimit F) hAll n

/-- The colimit of the sequence of iterated splitting rings is faithfully flat over `A`. -/
lemma iteratedSplittingColimit_faithfullyFlat (A : Type u) [CommRing A] :
    letI : Algebra A (iteratedSplittingColimit (CommRingCat.of A)) :=
      (colimit.ι (iteratedSplittingDiagram (CommRingCat.of A)) 0).hom.toAlgebra
    (algebraMap A (iteratedSplittingColimit (CommRingCat.of A))).FaithfullyFlat := by
  let : Algebra A (iteratedSplittingColimit (CommRingCat.of A)) :=
    (colimit.ι (iteratedSplittingDiagram (CommRingCat.of A)) 0).hom.toAlgebra
  have hmap : algebraMap A (iteratedSplittingColimit (CommRingCat.of A)) =
      (colimit.ι (iteratedSplittingDiagram (CommRingCat.of A)) 0).hom := by
    ext a
    rfl
  rw [hmap]
  exact iteratedSplittingColimit_leg_faithfullyFlat A 0

/-- The sequential colimit of the iterated splitting rings is a faithfully flat ind-étale
`A`-algebra over which every faithfully flat étale algebra admits a retraction. Its `A`-algebra
structure is induced by the first coprojection into the colimit. -/
@[stacks 097S "the properties of the iterated construction"]
theorem iteratedSplittingColimit_splits_etale (A : Type u) [CommRing A] :
    letI : Algebra A (iteratedSplittingColimit (CommRingCat.of A)) :=
      (colimit.ι (iteratedSplittingDiagram (CommRingCat.of A)) (0 : ℕ)).hom.toAlgebra
    (algebraMap A (iteratedSplittingColimit (CommRingCat.of A))).FaithfullyFlat ∧
      ObjectProperty.ind.{u}
        (fun D : Under (CommRingCat.of A) ↦ D.hom.hom.Etale)
        (Under.mk (CommRingCat.ofHom
          (algebraMap A (iteratedSplittingColimit (CommRingCat.of A))))) ∧
      ∀ (B : Type u) [CommRing B]
        [Algebra (iteratedSplittingColimit (CommRingCat.of A)) B],
        (algebraMap (iteratedSplittingColimit (CommRingCat.of A)) B).FaithfullyFlat →
        Algebra.Etale (iteratedSplittingColimit (CommRingCat.of A)) B →
        Nonempty (B →ₐ[(iteratedSplittingColimit (CommRingCat.of A))]
          iteratedSplittingColimit (CommRingCat.of A)) := by
  let C := iteratedSplittingColimit (CommRingCat.of A)
  let : Algebra A C :=
    (colimit.ι (iteratedSplittingDiagram (CommRingCat.of A)) (0 : ℕ)).hom.toAlgebra
  refine ⟨iteratedSplittingColimit_faithfullyFlat A,
    (ind_etale_iff_algebra_ind (A := A) (C := C)).mpr
      (iteratedSplittingColimit_ind_etale A), ?_⟩
  intro B _ _ hCB hEt
  let F := iteratedSplittingDiagram (CommRingCat.of A)
  let c := colimit.cocone F
  let E : AsSmall.{u} ℕ ⥤ ℕ := AsSmall.equiv.inverse
  let d := c.whisker E
  have hd : IsColimit d := (Functor.Final.isColimitWhiskerEquiv E _).symm
    (colimit.isColimit F)
  let p : d.pt ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap C B)
  have hpEt : CommRingCat.etale.{u} p := by
    show (algebraMap C B).Etale
    exact RingHom.etale_algebraMap.mpr hEt
  obtain ⟨n, Z, g, q, hpush, hgEt⟩ := exists_isPushout_etale hd p hpEt
  let k : ℕ := E.obj n
  have hleg : (d.ι.app n).hom.FaithfullyFlat := by
    show (c.ι.app k).hom.FaithfullyFlat
    exact iteratedSplittingColimit_leg_faithfullyFlat A k
  have hgFF : g.hom.FaithfullyFlat :=
    faithfullyFlat_of_isPushout (d.ι.app n) g p q hpush hleg hCB
  algebraize [g.hom]
  let : Algebra (iteratedSplittingRing (CommRingCat.of A) k) Z := g.hom.toAlgebra
  have hZEt : Algebra.Etale (iteratedSplittingRing (CommRingCat.of A) k) Z :=
    RingHom.etale_algebraMap.mp hgEt
  have hZFF :
      (algebraMap (iteratedSplittingRing (CommRingCat.of A) k) Z).FaithfullyFlat := hgFF
  obtain ⟨ψ⟩ := etale_faithfullyFlat_maps_to_splittingAlgebra hZEt hZFF
  let step : k ⟶ k + 1 := homOfLE (Nat.le_add_right k 1)
  let ψ' : Z ⟶ F.obj (k + 1) := CommRingCat.ofHom ψ.toRingHom
  let φ : Z ⟶ c.pt := ψ' ≫ c.ι.app (k + 1)
  have hφ : g ≫ φ = d.ι.app n := by
    have hgψ : g ≫ ψ' = F.map step := by
      apply CommRingCat.hom_ext
      ext x
      show ψ (g.hom x) = (F.map step).hom x
      exact (ψ.commutes x).trans (congrArg (fun f : CommRingCat.Hom _ _ ↦ f.hom x)
        (iteratedSplittingDiagram_map_succ _ k)).symm
    show g ≫ (ψ' ≫ c.ι.app (k + 1)) = d.ι.app n
    rw [← Category.assoc, hgψ]
    simp [d, E, k, c.ι.naturality step]
  obtain ⟨s, hs⟩ := exists_retraction_of_isPushout (d.ι.app n) g p q hpush φ hφ
  exact ⟨{ toRingHom := s.hom
           commutes' := fun x ↦ congrArg (fun f : c.pt ⟶ c.pt ↦ f.hom x) hs }⟩

/-- The faithfully flat ind-étale `A`-algebra splitting all faithfully flat étale covers can be
chosen of cardinality at most any infinite cardinal bounding the cardinality of `A`. -/
@[stacks 097S "the bounded form of the first construction"]
theorem exists_small_faithfullyFlat_ind_etale_algebra_splitting_etale
    (A : Type u) [CommRing A] (k : Cardinal.{u})
    (hk : ℵ₀ ≤ k) (hA : Cardinal.mk A ≤ k) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
      Cardinal.mk C ≤ k ∧
        (algebraMap A C).FaithfullyFlat ∧
        ObjectProperty.ind.{u}
          (fun D : Under (CommRingCat.of A) ↦ D.hom.hom.Etale)
          (Under.mk (CommRingCat.ofHom (algebraMap A C))) ∧
        ∀ (B : Type u) [CommRing B] [Algebra C B],
          (algebraMap C B).FaithfullyFlat → Algebra.Etale C B →
            Nonempty (B →ₐ[C] C) := by
  let C := iteratedSplittingColimit (CommRingCat.of A)
  let : Algebra A C :=
    (colimit.ι (iteratedSplittingDiagram (CommRingCat.of A)) (0 : ℕ)).hom.toAlgebra
  obtain ⟨hff, hind, hsplit⟩ := iteratedSplittingColimit_splits_etale A
  exact ⟨C, inferInstance, inferInstance,
    mk_iteratedSplittingColimit_le (CommRingCat.of A) k hk hA,
    hff, hind, hsplit⟩

end AlgebraicGeometry.ProEtale

end
