module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfGeneric

/-!
# A bounded complex of constructible flat sheaves is locally constant on a dense open

Let `X` be a reduced scheme whose underlying space is Noetherian — a reduced scheme of finite
type over a field, for instance — and `Λ` an arbitrary ring. Given finitely many constructible
flat sheaves of `Λ`-modules on the small étale site of `X`, there is a dense open subscheme of
`X` on which all of them are locally constant with finite projective values. In particular every
term of a bounded complex of constructible flat sheaves is so on one dense open. This is the
dévissage of Step 3 of [Stacks, Tag 03UG]: there `X` is a curve and the complex represents an
object of `D_ctf(X, Λ)`.

## Main results

* `AlgebraicGeometry.isFiniteProjectiveLocallyConstant_of_jointlySurjective` — local constancy
  with finite projective values can be checked on a jointly surjective family of étale morphisms.
* `AlgebraicGeometry.exists_dense_isOpenImmersion_isFiniteProjectiveLocallyConstant` — finitely
  many constructible flat sheaves on a reduced Noetherian scheme are locally constant with finite
  projective values on one dense open.
* `exists_dense_isOpenImmersion_isFiniteProjectiveLocallyConstant_of_complex`, in the namespace
  `Stacks.EtaleCohomology` — the same for the terms of a bounded complex of constructible flat
  sheaves on Mathlib's small étale site.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]

attribute [local instance] SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- A morphism to the final object of the small étale site is the structure morphism. -/
theorem SmallEtale.hom_final_left {S : Scheme.{u}} {hS : B.Contains S} {Y : SmallEtale B S hS}
    (φ : Y ⟶ SmallEtale.final B S hS) : φ.hom.left = Y.obj.hom :=
  (Category.comp_id _).symm.trans (Over.w φ.hom)

/-- **Local constancy with finite projective values is local for jointly surjective étale
families.** If `g i : T i ⟶ S` are étale morphisms of a big étale site whose images cover `S`,
and the inverse image of `H` along each of them is locally constant with finite projective
values, then so is `H`. -/
theorem isFiniteProjectiveLocallyConstant_of_jointlySurjective {S : B.Scheme} {ι : Type*}
    (T : ι → B.Scheme) (g : ∀ i, T i ⟶ S) [∀ i, Etale (B.inclusion.map (g i))]
    (hsurj : ∀ x : S.obj, ∃ i, x ∈ Set.range (B.inclusion.map (g i)).base)
    (H : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{max (u + 1) r} Λ))
    (hH : ∀ i, Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
      (SmallEtale.topology B (T i).obj (T i).property)
      (((smallEtaleBaseChange B (g i)).sheafPullback (ModuleCat.{max (u + 1) r} Λ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B (T i).obj (T i).property)).obj H)) :
    Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
      (SmallEtale.topology B S.obj S.property) H := by
  have hT := SmallEtale.finalIsTerminal B S.obj S.property
  choose I V f hcov hc using fun i => hH i (SmallEtale.final B (T i).obj (T i).property)
  let X' : (Σ i, I i) → SmallEtale B S.obj S.property := fun p =>
    ⟨Over.mk ((V p.1 p.2).obj.hom ≫ g p.1), by
      show Etale (B.inclusion.map ((V p.1 p.2).obj.hom ≫ g p.1))
      rw [Functor.map_comp]
      infer_instance⟩
  have hcov' : Sieve.ofArrows X' (fun p => hT.from (X' p)) ∈
      SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property) := by
    refine SmallEtale.generate_ofArrows_mem_topology_of_jointlySurjective B S.obj S.property
      X' _ (fun x => ?_)
    obtain ⟨i, y, hy⟩ := hsurj x
    obtain ⟨W, g', hg', z, hz⟩ :=
      SmallEtale.exists_mem_arrows_mem_range B (T i).obj (T i).property (hcov i) y
    obtain ⟨k, c, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg'
    refine ⟨⟨i, k⟩, B.inclusion.map c.hom.left z, ?_⟩
    rw [SmallEtale.hom_final_left]
    show (B.inclusion.map ((V i k).obj.hom ≫ g i)).base (B.inclusion.map c.hom.left z) = x
    have hz' : (B.inclusion.map (V i k).obj.hom).base (B.inclusion.map c.hom.left z) = y := by
      rwa [← SmallEtale.hom_final_left B (f i k)]
    rw [Functor.map_comp, Scheme.Hom.comp_apply, hz', hy]
  have hc' : ∀ p : Σ i, I i, ∃ E : ModuleCat.{max (u + 1) r} Λ,
      (Module.Finite Λ E ∧ Module.Projective Λ E) ∧ Nonempty
        ((constantSheaf ((SmallEtale.topology B S.obj S.property).over (X' p))
          (ModuleCat.{max (u + 1) r} Λ)).obj E ≅
          ((SmallEtale.topology B S.obj S.property).overPullback
            (ModuleCat.{max (u + 1) r} Λ) (X' p)).obj H) := by
    rintro ⟨i, k⟩
    obtain ⟨E, hfin, hproj, ⟨e⟩⟩ := hc i k
    have : HasWeakSheafify (SmallEtale.topology B (V i k).obj.left.1 (V i k).obj.left.property)
        (ModuleCat.{max (u + 1) r} Λ) :=
      hasWeakSheafify_smallEtale_of_over B (T i).obj (T i).property (V i k) _
    have : HasWeakSheafify (SmallEtale.topology B (X' ⟨i, k⟩).obj.left.1
        (X' ⟨i, k⟩).obj.left.property) (ModuleCat.{max (u + 1) r} Λ) :=
      hasWeakSheafify_smallEtale_of_over B S.obj S.property (X' ⟨i, k⟩) _
    obtain ⟨c⟩ := (nonempty_constantSheafIso_over_iff B (T i).obj (T i).property (V i k) _ _
      E).mp ⟨e⟩
    refine ⟨E, ⟨hfin, hproj⟩, (nonempty_constantSheafIso_over_iff B S.obj S.property
      (X' ⟨i, k⟩) _ H E).mpr ⟨c ≪≫ (smallEtaleSheafPullbackCompIso B (V i k).obj.left (T i) S
        (V i k).obj.hom (g i) (ModuleCat.{max (u + 1) r} Λ)).app H⟩⟩
  intro U
  obtain ⟨I', W, f', hW, hW'⟩ := Stacks.ConstantSheaf.Localization.exists_trivializing_cover
    (SmallEtale.topology B S.obj S.property) (ModuleCat.{max (u + 1) r} Λ) hT H
    (fun E => Module.Finite Λ E ∧ Module.Projective Λ E) hcov' hc' U
  exact ⟨I', W, f', hW, fun k => (hW' k).imp fun _ => and_assoc.1⟩

/-- **Finitely many constructible flat sheaves are locally constant on one dense open.** Let `X` be
a reduced scheme of a big étale site whose underlying space is Noetherian, and `G j`, for `j` in
a finite type, constructible flat sheaves of `Λ`-modules on its small étale site, for an arbitrary
ring `Λ`. Then there is an open immersion `o : O ⟶ X` with dense image along which the inverse
image of every `G j` is locally constant with finite projective values. -/
theorem exists_dense_isOpenImmersion_isFiniteProjectiveLocallyConstant (X : B.Scheme)
    [IsReduced X.obj] [NoetherianSpace X.obj] {ι : Type*} [Finite ι]
    (G : ι → Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ))
    (hG : ∀ j, IsConstructibleFlatModuleSheaf B X Λ (G j)) :
    ∃ (O : B.Scheme) (o : O ⟶ X), IsOpenImmersion (B.inclusion.map o) ∧
      Dense (Set.range (B.inclusion.map o).base) ∧ ∀ j,
        Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
          (SmallEtale.topology B O.obj O.property)
          (((smallEtaleBaseChange B o).sheafPullback (ModuleCat.{max (u + 1) r} Λ)
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B O.obj O.property)).obj (G j)) := by
  choose O o ho hηo hloc using fun (η : genericPoints X.obj) (j : ι) =>
    exists_isOpenImmersion_isFiniteProjectiveLocallyConstant_of_isConstructibleFlatModuleSheaf
      B Λ X (G j) (hG j) η.2
  let P : genericPoints X.obj → X.obj.Opens := fun η =>
    ⟨⋂ j, Set.range (B.inclusion.map (o η j)).base,
      isOpen_iInter_of_finite fun j => IsOpenImmersion.isOpen_range (B.inclusion.map (o η j))⟩
  let V : X.obj.Opens := ⟨⋃ η, (P η : Set X.obj), isOpen_iUnion fun η => (P η).isOpen⟩
  have hPV (η : genericPoints X.obj) : P η ≤ V := fun x hx => Set.mem_iUnion.2 ⟨η, hx⟩
  let Ob : X.obj.Opens → B.Scheme := fun U =>
    B.obj U.toScheme (Scheme.size_lt_of_isOpenImmersion U.ι X.property)
  let ob : ∀ U : X.obj.Opens, Ob U ⟶ X := fun U => ObjectProperty.homMk U.ι
  refine ⟨Ob V, ob V, inferInstanceAs (IsOpenImmersion V.ι), ?_, fun j => ?_⟩
  · have hrange : Set.range (B.inclusion.map (ob V)).base = (V : Set X.obj) :=
      Scheme.Opens.range_ι V
    rw [hrange]
    refine dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset ?_)
    rw [← genericPoints.closure]
    exact closure_mono fun η hη => Set.mem_iUnion.2 ⟨⟨η, hη⟩, Set.mem_iInter.2 fun j =>
      hηo ⟨η, hη⟩ j⟩
  let g : ∀ η : genericPoints X.obj, Ob (P η) ⟶ Ob V := fun η =>
    ObjectProperty.homMk (X.obj.homOfLE (hPV η))
  have : ∀ η, Etale (B.inclusion.map (g η)) := fun η =>
    inferInstanceAs (Etale (X.obj.homOfLE (hPV η)))
  refine isFiniteProjectiveLocallyConstant_of_jointlySurjective B Λ (fun η => Ob (P η)) g
    (fun x => ?_) _ (fun η => ?_)
  · obtain ⟨η, hη⟩ := Set.mem_iUnion.1 x.2
    exact ⟨η, ⟨x.1, hη⟩, Subtype.ext (Scheme.homOfLE_apply (X := X.obj) (hPV η) ⟨x.1, hη⟩)⟩
  · have hsub : Set.range (P η).ι.base ⊆ Set.range (B.inclusion.map (o η j)).base := by
      intro x hx
      have hx' : x ∈ (P η : Set X.obj) := (Scheme.Opens.range_ι (P η)) ▸ hx
      exact Set.mem_iInter.1 hx' j
    let L : Ob (P η) ⟶ O η j :=
      ObjectProperty.homMk (IsOpenImmersion.lift (B.inclusion.map (o η j)) (P η).ι hsub)
    have e1 : g η ≫ ob V = ob (P η) :=
      B.inclusion.map_injective (X.obj.homOfLE_ι (hPV η))
    have e2 : L ≫ o η j = ob (P η) :=
      B.inclusion.map_injective (IsOpenImmersion.lift_fac _ _ _)
    have hL := isFiniteProjectiveLocallyConstant_smallEtaleSheafPullback B Λ L _ (hloc η j)
    let A := ModuleCat.{max (u + 1) r} Λ
    let pb : ∀ {Y Z : B.Scheme} (m : Y ⟶ Z),
        Sheaf (SmallEtale.topology B Z.obj Z.property) A ⥤
          Sheaf (SmallEtale.topology B Y.obj Y.property) A := fun m =>
      (smallEtaleBaseChange B m).sheafPullback A _ _
    exact Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr _ _
      ((smallEtaleSheafPullbackCompIso B (Ob (P η)) (O η j) X L (o η j) A).app (G j) ≪≫
        eqToIso (congrArg (fun m => (pb m).obj (G j)) (e2.trans e1.symm)) ≪≫
        ((smallEtaleSheafPullbackCompIso B (Ob (P η)) (Ob V) X (g η) (ob V) A).app (G j)).symm) hL

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]

/-- **The dévissage of Step 3 of Tag 03UG, for a complex.** Let `X` be a reduced scheme of a big
étale site whose underlying space is Noetherian (for instance a reduced scheme of finite type over
a field) and `C` a bounded complex of constructible flat sheaves of `Λ`-modules on Mathlib's small
étale site of `X`, for an arbitrary ring `Λ`. Then there is an open immersion `o : O ⟶ X` with
dense image such that the transport of `o^{-1}` of every term of `C` to the small étale site of
Stacks 021B of `O` is locally constant with finite projective values. -/
theorem exists_dense_isOpenImmersion_isFiniteProjectiveLocallyConstant_of_complex
    (X : B.Scheme) [IsReduced X.obj] [NoetherianSpace X.obj]
    (C : CochainComplex (EtaleModules.{u, r} Λ X.obj) ℤ) (a b : ℤ) (ha : C.IsStrictlyGE a)
    (hb : C.IsStrictlyLE b) (hC : ∀ i, IsConstructibleFlatEtaleModule B X Λ (C.X i)) :
    ∃ (O : B.Scheme) (o : O ⟶ X), IsOpenImmersion (B.inclusion.map o) ∧
      Dense (Set.range (B.inclusion.map o).base) ∧ ∀ i : ℤ,
        Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
          (SmallEtale.topology B O.obj O.property)
          ((etaleModulesToSmallEtale B O Λ).obj
            ((etaleModuleInverseImage.{u, r} Λ (B.inclusion.map o)).obj (C.X i))) := by
  obtain ⟨O, o, ho, hd, h⟩ :=
    exists_dense_isOpenImmersion_isFiniteProjectiveLocallyConstant B Λ X
      (ι := Finset.Icc a b) (fun i => (etaleModulesToSmallEtale B X Λ).obj (C.X i))
      (fun i => hC i)
  refine ⟨O, o, ho, hd, fun i => ?_⟩
  by_cases hi : i ∈ Finset.Icc a b
  · exact Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr _ _
      (etaleModulesToSmallEtalePullbackIso B Λ o (C.X i)).symm (h ⟨i, hi⟩)
  · refine isFiniteProjectiveLocallyConstant_of_isZero B Λ O _
      (Functor.map_isZero _ (Functor.map_isZero _ ?_))
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hi
    rcases hi with hi | hi
    · exact C.isZero_of_isStrictlyGE a i hi
    · exact C.isZero_of_isStrictlyLE b i hi

end Stacks.EtaleCohomology
