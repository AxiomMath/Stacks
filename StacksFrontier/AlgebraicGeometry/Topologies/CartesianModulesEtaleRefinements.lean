module

public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesOnAffineSite
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentSheaf

/-!
# A presheaf of modules cartesian along étale arrows is a sheaf for étale coverings

Let `C` be a category with fibre products, with a functor `L : C ⥤ Scheme` preserving them, and
let `R` be a presheaf of commutative rings on `C` whose restriction maps are faithfully flat
along finite étale coverings and which turns fibre product squares into pushout squares. A
presheaf of `R`-modules which is *cartesian along the arrows lying over étale morphisms* — its
base-change comparison is an isomorphism along every arrow `f` with `L.map f` étale — is a sheaf
for every topology all of whose covering sieves contain a finite family which is an étale
covering of schemes under `L`.

Compared with `Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_refinements'`, the covering
families are étale rather than flat, and the base-change comparison is required to be an
isomorphism only along the arrows lying over étale morphisms.

## Main results

* `Stacks.PresheafOfModules.isSheaf_of_isIso_restrictionBaseChange_of_etale_refinements`: a
  presheaf of modules cartesian along the arrows lying over étale morphisms is a sheaf for every
  topology whose covering sieves are refined by finite étale coverings.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 0H0F](https://stacks.math.columbia.edu/tag/0H0F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w r m i

/-- Étaleness of morphisms of schemes, as a `MorphismProperty`. -/
private abbrev AlgebraicGeometry.etalePropertyOfSchemes : MorphismProperty Scheme.{u} := @Etale

namespace Stacks.PresheafOfModules

/-- **A presheaf of modules cartesian along the arrows lying over étale morphisms is a sheaf for
a topology whose covering sieves are refined by finite étale coverings.** -/
theorem isSheaf_of_isIso_restrictionBaseChange_of_etale_refinements
    {C : Type v} [Category.{w} C] [HasPullbacks C]
    (L : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan L]
    (R : Cᵒᵖ ⥤ CommRingCat.{r})
    (hff : ∀ {U : C} (E : PreZeroHypercover.{i} U), Finite E.I₀ →
      (E.map L).presieve₀ ∈ Scheme.precoverage @Etale (L.obj U) →
      (RingHom.pi (fun k => (R.map (E.f k).op).hom)).FaithfullyFlat)
    (hpo : ∀ {X Y Z P : C} {fst : P ⟶ X} {snd : P ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z},
      IsPullback fst snd a b →
      IsPushout (R.map a.op) (R.map b.op) (R.map fst.op) (R.map snd.op))
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : C} (f : X ⟶ Y), Etale (L.map f) →
      IsIso (restrictionBaseChange.{v, w, r, m} M f.op))
    (J : GrothendieckTopology C)
    (hJ : ∀ {U : C} (S : Sieve U), S ∈ J U →
      ∃ E : PreZeroHypercover.{i} U, Finite E.I₀ ∧
        (E.map L).presieve₀ ∈ Scheme.precoverage @Etale (L.obj U) ∧ E.sieve₀ ≤ S) :
    Presheaf.IsSheaf J M.presheaf := by
  apply Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget
  intro U S hS
  obtain ⟨E, hfin, hE, hES⟩ := hJ S hS
  let _ := hfin
  apply Presieve.isSheafFor_subsieve _ hES
  intro V f
  let K := (Scheme.precoverage etalePropertyOfSchemes.{u}).comap L
  let _ : K.IsStableUnderBaseChange :=
    inferInstanceAs (Precoverage.IsStableUnderBaseChange
      ((Scheme.precoverage etalePropertyOfSchemes.{u}).comap L))
  have he : E.presieve₀ ∈ K U := by
    show E.presieve₀.map L ∈ (Scheme.precoverage @Etale) (L.obj U)
    simpa only [PreZeroHypercover.presieve₀_map] using hE
  have he' : (E.pullback₂ f).presieve₀ ∈ K V :=
    K.mem_coverings_of_isPullback _ he _ _ _
      (fun i => (IsPullback.of_hasPullback (E.f i) f).flip)
  let E' := E.pullback₂ f
  let _ : Finite E'.I₀ := hfin
  have he'' : (E'.map L).presieve₀ ∈ Scheme.precoverage @Etale (L.obj V) := by
    simpa only [K, Precoverage.mem_comap_iff, PreZeroHypercover.presieve₀_map] using he'
  have het : ∀ k, Etale (L.map (E'.f k)) := fun k =>
    ((Scheme.presieve₀_mem_precoverage_iff (E'.map L)).mp he'').2 k
  have h : Presieve.IsSheafFor (M.presheaf ⋙ forget AddCommGrpCat) E'.presieve₀ := by
    refine isSheafFor_of_isIso_restrictionBaseChange R M E'.X E'.f
      (fun i j => pullback (E'.f i) (E'.f j))
      (fun i j => pullback.fst (E'.f i) (E'.f j))
      (fun i j => pullback.snd (E'.f i) (E'.f j))
      (fun _ _ => pullback.condition) (hff E' inferInstance he'')
      (fun i j => hpo (IsPullback.of_hasPullback (E'.f i) (E'.f j)))
      (fun k => hM _ (het k)) (fun i j => hM _ ?_)
    have : Etale (L.map (pullback.fst (E'.f i) (E'.f j))) :=
      MorphismProperty.of_isPullback (P := etalePropertyOfSchemes.{u})
        ((IsPullback.of_hasPullback (E'.f i) (E'.f j)).map L).flip (het j)
    rw [L.map_comp]
    have := het i
    infer_instance
  rwa [PreZeroHypercover.presieve₀_pullback₁, Presieve.isSheafFor_iff_generate,
    Sieve.pullbackArrows_comm] at h

end Stacks.PresheafOfModules

end
