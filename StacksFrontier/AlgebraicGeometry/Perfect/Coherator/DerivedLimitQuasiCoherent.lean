module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.LocalKernel
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.AffineSectionsTower
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.AcyclicCoveringFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.AcyclicObject
public import StacksFrontier.Topology.Sheaves.Cohomology.RecoveryB.InverseLimitAsDerivedLimit

/-!
# Derived inverse limits with quasi-coherent cohomology

Let `X` be a scheme and `(Kₙ)` an inverse system in the unbounded derived category of
`𝒪_X`-modules whose cohomology sheaves are all quasi-coherent, and suppose every transition map
`H^q(K_{n+1}) → H^q(K_n)` is surjective. If `K` is a derived limit of the system, then

* `H^q(K) = lim H^q(Kₙ)`;
* the ordinary limit `lim H^q(Kₙ)`, placed in degree zero, is already the derived limit of the
  system of cohomology sheaves;
* `lim H^q(Kₙ)` has no higher cohomology on an affine open.

The three statements are proved in that logical order. The affine opens form a basis of `X` on
which quasi-coherent modules are acyclic, and the surjectivity hypothesis makes the tower of
sections over an affine open Mittag-Leffler, so its first derived inverse limit vanishes. That
is exactly the input the general site-theoretic machinery asks for.

## Main results

* `AlgebraicGeometry.cohomology_isLimit_of_isDerivedLimit_of_epi`: the cohomology of a derived
  limit is the limit of the cohomology sheaves.
* `AlgebraicGeometry.isDerivedLimit_single_limit_homology`: the ordinary limit of the system of
  cohomology sheaves is its derived limit.
* `AlgebraicGeometry.isZero_cohomology_limit_homology_of_isAffineOpen`: that limit is acyclic on
  affine opens.

## Implementation notes

Quasi-coherence of the cohomology is carried as a hypothesis on each cohomology sheaf of each
term rather than by placing the system in a subcategory, so the statements apply to an arbitrary
inverse system in the derived category. Surjectivity of the transition maps is expressed by
epimorphisms. A derived limit is presented by its structural morphism to the product together
with the distinguished triangle that characterises it, so that the statements do not depend on a
chosen construction of derived limits; the existence of the product is part of the conclusion
where it is not a hypothesis.

## References

* [Stacks Project, Tag 0A0J](https://stacks.math.columbia.edu/tag/0A0J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.InternalHom (spaceRingedSite)

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

universe u

/-- The site of opens of a scheme, with its structure sheaf, read as a ringed site. -/
private noncomputable abbrev schemeRingedSite (X : Scheme.{u}) : RingedSite.{u, u, u} :=
  spaceRingedSite X.toRingedSpace.sheaf

private noncomputable instance evaluationAdditive (X : RingedSpace.{u, u})
    (U : Opens X.carrier) : (SheafOfModules.evaluation (structureSheafRing X) (op U)).Additive := by
  unfold SheafOfModules.evaluation
  infer_instance

/-- A basis of opens of a space is a family of objects covering every object of the site of
opens. -/
private lemma hasEnoughObjects_of_isBasis (T : Type u) [TopologicalSpace T]
    (B : Set (Opens T)) (hB : Opens.IsBasis B) :
    (Opens.grothendieckTopology T).HasEnoughObjects (fun U => U ∈ B) := by
  show ∀ U : Opens T, ∃ (I : Type u) (Ui : I → Opens T)
    (f : ∀ i, Ui i ⟶ U), Sieve.ofArrows Ui f ∈ Opens.grothendieckTopology T U ∧
      ∀ i, Ui i ∈ B
  intro U
  refine ⟨{V : Opens T // V ∈ B ∧ V ≤ U}, fun i => i.1, fun i => homOfLE i.2.2,
    ?_, fun i => i.2.1⟩
  refine (Opens.mem_grothendieckTopology T).2 fun x hx => ?_
  obtain ⟨V, hV, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp hB) hx
  exact ⟨V, homOfLE hVU, (Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨V, hV, hVU⟩, 𝟙 V, by simp⟩, hxV⟩

/-- Forgetting the module structure commutes with the right derived functors of sections, since
both are computed from the same injective resolution. -/
private noncomputable def rightDerivedEvaluationForgetIso
    (X : RingedSpace.{u, u}) (U : Opens X.carrier) (n : ℕ)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U))) AddCommGrpCat.{u}).obj
        (((SheafOfModules.evaluation (structureSheafRing X) (op U)).rightDerived n).obj M) ≅
      ((SheafOfModules.evaluation (structureSheafRing X) (op U) ⋙
        forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)))
          AddCommGrpCat.{u}).rightDerived n).obj M :=
  let I := injectiveResolution M
  let E := SheafOfModules.evaluation (structureSheafRing X) (op U)
  let G := forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U))) AddCommGrpCat.{u}
  let K := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  G.mapIso (I.isoRightDerivedObj E n) ≪≫
    G.mapIso ((HomologicalComplex.homologyFunctorIso _ _ n).app K) ≪≫
    ((K.sc n).mapHomologyIso G).symm ≪≫
    ((HomologicalComplex.homologyFunctorIso _ _ n).app
      ((G.mapHomologicalComplex _).obj K)).symm ≪≫
    (I.isoRightDerivedObj (E ⋙ G) n).symm

/-- Higher cohomology of a module sheaf vanishes as a module as soon as it vanishes as an
abelian group. -/
private lemma isZero_rightDerived_evaluation_of_isZero_forget
    (X : RingedSpace.{u, u}) (U : Opens X.carrier) (r : ℕ)
    (M : SheafOfModules.{u} (structureSheafRing X))
    [(SheafOfModules.evaluation (structureSheafRing X) (op U)).Additive]
    [EnoughInjectives (SheafOfModules (structureSheafRing X))]
    (h : IsZero (((SheafOfModules.evaluation (structureSheafRing X) (op U) ⋙
      forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)))
        AddCommGrpCat.{u}).rightDerived r).obj M)) :
    IsZero (((SheafOfModules.evaluation (structureSheafRing X) (op U)).rightDerived r).obj M) := by
  let R := ((SheafOfModules.evaluation (structureSheafRing X) (op U)).rightDerived r).obj M
  have hG : IsZero (AddCommGrpCat.of R) := by
    simpa using (Iso.isZero_iff (rightDerivedEvaluationForgetIso X U r M)).2 h
  have := AddCommGrpCat.subsingleton_of_isZero hG
  exact ModuleCat.isZero_of_subsingleton R

/-- Two distinguished triangles with the same second and third object and the same morphism
between them have isomorphic first objects, compatibly with the structural morphisms. -/
private lemma exists_iso_of_distTriang_of_common_second
    {D : Type u} [Category.{u} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {A B P : D} (pK : A ⟶ P) (pL : B ⟶ P) (d : P ⟶ P)
    (δK : P ⟶ A⟦(1 : ℤ)⟧) (δL : P ⟶ B⟦(1 : ℤ)⟧)
    (hK : Triangle.mk pK d δK ∈ distTriang D)
    (hL : Triangle.mk pL d δL ∈ distTriang D) :
    ∃ e : A ≅ B, e.hom ≫ pL = pK := by
  let T := Triangle.mk pK d δK
  let T' := Triangle.mk pL d δL
  obtain ⟨f, hf₁, hf₂⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁
    T T' hK hL (𝟙 P) (𝟙 P) (by simp [T, T'])
  let φ : T ⟶ T' :=
    { hom₁ := f
      hom₂ := 𝟙 P
      hom₃ := 𝟙 P
      comm₁ := hf₁
      comm₂ := by simp [T, T']
      comm₃ := hf₂ }
  have hf : IsIso φ.hom₁ := Pretriangulated.isIso₁_of_isIso₂₃ φ hK hL (IsIso.id P) (IsIso.id P)
  exact ⟨asIso φ.hom₁, by simpa [φ, T, T'] using hf₁.symm⟩

/-- Quasi-coherent modules have no higher cohomology on an affine open, as modules. -/
private lemma isZero_rightDerived_evaluation_of_isQuasicoherent (X : Scheme.{u})
    (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) (r : ℕ)
    (hr : 0 < r) :
    IsZero (((SheafOfModules.evaluation (structureSheafRing X.toRingedSpace) (op U)).rightDerived
      r).obj F) :=
  isZero_rightDerived_evaluation_of_isZero_forget X.toRingedSpace U r F
    (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F U hU r hr)

/-- **Stacks Project, Tag 0A0J.** The degree-`q` cohomology sheaf of a derived inverse limit of
a tower with quasi-coherent cohomology and surjective transition maps on cohomology is the
ordinary inverse limit of the degree-`q` cohomology sheaves. -/
@[stacks 0A0J "cohomology_limit"]
public theorem cohomology_isLimit_of_isDerivedLimit_of_epi
    (X : Scheme.{u})
    (K : ℕᵒᵖ ⥤ DerivedCategory.{u + 1} X.Modules)
    (L : DerivedCategory.{u + 1} X.Modules)
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p
        (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
              K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory X.Modules))
    (hqc : ∀ (n : ℕ) (q : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules q).obj (K.obj ⟨n⟩)).IsQuasicoherent)
    (hsurj : ∀ (n : ℕ) (q : ℤ),
      Epi ((DerivedCategory.homologyFunctor X.Modules q).map
        (K.map (homOfLE (Nat.le_succ n)).op)))
    (q : ℤ) :
    ∃ τ : (Functor.const ℕᵒᵖ).obj
        ((DerivedCategory.homologyFunctor X.Modules q).obj L) ⟶
        K ⋙ DerivedCategory.homologyFunctor X.Modules q,
      (∀ n : ℕ, τ.app ⟨n⟩ =
        (DerivedCategory.homologyFunctor X.Modules q).map
          (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) ∧
      Nonempty (IsLimit (Cone.mk _ τ)) := by
  let B : Set (Opens X.carrier) := X.affineOpens
  have hacyclic : ∀ U ∈ B, ∀ q : ℤ, ∀ n : ℕ, ∀ r : ℕ, 0 < r →
      IsZero (((SheafOfModules.evaluation (structureSheafRing X.toRingedSpace) (op U)).rightDerived
        r).obj ((DerivedCategory.homologyFunctor X.Modules q).obj (K.obj ⟨n⟩))) :=
    fun U hU q n r hr =>
      have := hqc n q; isZero_rightDerived_evaluation_of_isQuasicoherent X _ U hU r hr
  have hlimOne : ∀ U ∈ B, ∀ q : ℤ,
      IsZero (Rlim.firstDerivedLimit
        (K ⋙ DerivedCategory.homologyFunctor X.Modules q ⋙
          Stacks.Cohomology.Localization.sectionsOverObject (schemeRingedSite X) U)) :=
    fun U hU q => isZero_firstDerivedLimit_sections X K q (fun n => hqc n q)
      (fun n => hsurj n q) U hU
  let K' : ℕᵒᵖ ⥤ DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (schemeRingedSite X).O)) := K
  let L' : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (schemeRingedSite X).O)) := L
  let : HasProduct (fun n : ℕ => K'.obj ⟨n⟩) := ‹HasProduct (fun n : ℕ => K.obj ⟨n⟩)›
  obtain ⟨δ, hδ⟩ := hL
  have hBasis := hasEnoughObjects_of_isBasis X.carrier B X.isBasis_affineOpens
  obtain ⟨p', ⟨δ', hδ'⟩, ⟨τ', hτ', hτlimit⟩⟩ :=
    Stacks.Cohomology.DerivedLimitAcyclic.cohomology_isLimit_of_isDerivedLimit_of_acyclic_cover
      (schemeRingedSite X) K' L' ⟨p, δ, hδ⟩ (fun U => U ∈ B) hBasis hacyclic hlimOne
      (fun M U hU hvan m =>
        Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_acyclic_cover
          (Stacks.SheafOfModules.Tensor.ringSheaf (schemeRingedSite X).O) U M (fun V => V ∈ B)
          hBasis hvan hU m)
      q
  let H := DerivedCategory.homologyFunctor X.Modules q
  obtain ⟨σ, hσ, hσlimit⟩ : ∃ τ : (Functor.const ℕᵒᵖ).obj (H.obj L') ⟶ K' ⋙ H,
      (∀ n : ℕ, τ.app ⟨n⟩ = H.map (p' ≫ Pi.π (fun n : ℕ => K'.obj ⟨n⟩) n)) ∧
        Nonempty (IsLimit (Cone.mk _ τ)) := ⟨τ', hτ', hτlimit⟩
  obtain ⟨e, he⟩ := exists_iso_of_distTriang_of_common_second p p' _ δ δ' hδ hδ'
  refine ⟨(Functor.const ℕᵒᵖ).map (H.map e.hom) ≫ σ, fun n => ?_, ?_⟩
  · show H.map e.hom ≫ σ.app (op n) = H.map (p ≫ Pi.π (fun n : ℕ => K'.obj ⟨n⟩) n)
    rw [hσ n]
    exact (H.map_comp _ _).symm.trans (congrArg H.map
      ((Category.assoc e.hom p' (Pi.π (fun n : ℕ => K'.obj ⟨n⟩) n)).symm.trans
        (congrArg (fun f => f ≫ Pi.π (fun n : ℕ => K'.obj ⟨n⟩) n) he)))
  · exact ⟨IsLimit.ofIsoLimit (Classical.choice hσlimit)
      (Cone.ext (Functor.mapIso H e) (fun n => rfl)).symm⟩

/-- Higher cohomology of a quasi-coherent cohomology sheaf of a term vanishes on an affine open. -/
private lemma isZero_hgroup_homology_of_isAffineOpen (X : Scheme.{u})
    (K : ℕᵒᵖ ⥤ DerivedCategory.{u + 1} X.Modules)
    (hqc : ∀ (n : ℕ) (q : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules q).obj (K.obj ⟨n⟩)).IsQuasicoherent)
    (q : ℤ) (U : X.Opens) (hU : IsAffineOpen U) (n p : ℕ) (hp : 0 < p) :
    IsZero (Hgroup X.ringCatSheaf U p
      ((K ⋙ DerivedCategory.homologyFunctor X.Modules q).obj ⟨n⟩)) :=
  have : ((K ⋙ DerivedCategory.homologyFunctor X.Modules q).obj ⟨n⟩).IsQuasicoherent := hqc n q
  Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X _ U hU p hp

/-- The transition maps on sections of a tower of quasi-coherent cohomology sheaves over an
affine open have an epimorphic difference map. -/
private lemma epi_inverseLimitDifference_sectionsSystem (X : Scheme.{u})
    (K : ℕᵒᵖ ⥤ DerivedCategory.{u + 1} X.Modules)
    (hqc : ∀ (n : ℕ) (q : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules q).obj (K.obj ⟨n⟩)).IsQuasicoherent)
    (hsurj : ∀ (n : ℕ) (q : ℤ),
      Epi ((DerivedCategory.homologyFunctor X.Modules q).map
        (K.map (homOfLE (Nat.le_succ n)).op)))
    (q : ℤ) (U : X.Opens) (hU : IsAffineOpen U) :
    Epi (Stacks.Cohomology.SpaceInverseLimits.inverseLimitDifference
      (Stacks.Cohomology.SpaceInverseLimits.sectionsSystem X.toRingedSpace
        (K ⋙ DerivedCategory.homologyFunctor X.Modules q) U)) := by
  have hdiff : Rlim.delta (sectionsTower X K q U) =
      Stacks.Cohomology.SpaceInverseLimits.inverseLimitDifference
        (Stacks.Cohomology.SpaceInverseLimits.sectionsSystem X.toRingedSpace
          (K ⋙ DerivedCategory.homologyFunctor X.Modules q) U) := by
    rw [Rlim.delta_eq_lift]
    rfl
  apply Preadditive.epi_of_isZero_cokernel
  rw [← hdiff]
  exact isZero_firstDerivedLimit_sections X K q (fun n => hqc n q) (fun n => hsurj n q) U hU

/-- **Stacks Project, Tag 0A0J.** For a tower with quasi-coherent cohomology and surjective
transition maps on cohomology, the ordinary inverse limit of each tower of cohomology sheaves,
placed in degree zero, is its derived inverse limit. -/
@[stacks 0A0J "derived_limit_sheaves"]
public theorem isDerivedLimit_single_limit_homology
    (X : Scheme.{u})
    (K : ℕᵒᵖ ⥤ DerivedCategory.{u + 1} X.Modules)
    (hqc : ∀ (n : ℕ) (q : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules q).obj (K.obj ⟨n⟩)).IsQuasicoherent)
    (hsurj : ∀ (n : ℕ) (q : ℤ),
      Epi ((DerivedCategory.homologyFunctor X.Modules q).map
        (K.map (homOfLE (Nat.le_succ n)).op)))
    (q : ℤ) :
    let F := K ⋙ DerivedCategory.homologyFunctor X.Modules q
    ∃ h : HasProduct (fun n : ℕ =>
        (F ⋙ DerivedCategory.singleFunctor X.Modules 0).obj ⟨n⟩),
      @IsDerivedLimit (DerivedCategory X.Modules) _ _ _ _ _ _
        (F ⋙ DerivedCategory.singleFunctor X.Modules 0) h
        ((DerivedCategory.singleFunctor X.Modules 0).obj (limit F)) := by
  let F : ℕᵒᵖ ⥤ X.Modules := K ⋙ DerivedCategory.homologyFunctor X.Modules q
  exact Stacks.Cohomology.SpaceInverseLimits.isDerivedLimit_single_limit_of_isBasis
    X.toRingedSpace F X.affineOpens X.isBasis_affineOpens
    (fun U hU n p hp => isZero_hgroup_homology_of_isAffineOpen X K hqc q U hU n p hp)
    (fun U hU => epi_inverseLimitDifference_sectionsSystem X K hqc hsurj q U hU)

/-- **Stacks Project, Tag 0A0J.** The inverse limit of a degreewise-surjective tower of
quasi-coherent cohomology sheaves has no higher cohomology on an affine open. -/
@[stacks 0A0J "affine_limit_acyclic"]
public theorem isZero_cohomology_limit_homology_of_isAffineOpen
    (X : Scheme.{u})
    (K : ℕᵒᵖ ⥤ DerivedCategory.{u + 1} X.Modules)
    (hqc : ∀ (n : ℕ) (q : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules q).obj (K.obj ⟨n⟩)).IsQuasicoherent)
    (hsurj : ∀ (n : ℕ) (q : ℤ),
      Epi ((DerivedCategory.homologyFunctor X.Modules q).map
        (K.map (homOfLE (Nat.le_succ n)).op)))
    (U : X.Opens) (hU : IsAffineOpen U) (q : ℤ) (p : ℕ) (hp : 0 < p) :
    let F : ℕᵒᵖ ⥤ X.Modules := K ⋙ DerivedCategory.homologyFunctor X.Modules q
    let h : HasLimit F := inferInstance
    IsZero (Hgroup X.ringCatSheaf U p (@limit _ _ _ _ F h)) := by
  let F : ℕᵒᵖ ⥤ X.Modules := K ⋙ DerivedCategory.homologyFunctor X.Modules q
  refine Stacks.Cohomology.SpaceInverseLimits.isZero_cohomology_limit_of_isBasis
    (X := X.toRingedSpace) (F := F) (B := X.affineOpens) X.isBasis_affineOpens
    (fun V hV n r hr => ?_) (fun V hV => ?_) U hU p hp
  · exact isZero_hgroup_homology_of_isAffineOpen X K hqc q V hV n r hr
  · exact epi_inverseLimitDifference_sectionsSystem X K hqc hsurj q V hV

end AlgebraicGeometry

end
