module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleDerivedSheaves
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedRestrictionProducts
public import StacksFrontier.AlgebraicGeometry.ProEtale.LocallyConstantAdicModel
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.SurjectiveTowerDerivedLimit
public import StacksFrontier.Homology.DerivedComplete.DerivedLimitLeftAdjoint
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleReductionSections

/-!
# The complex of completed constant sheaves is a derived limit

Let `X` be a scheme, `Λ` a ring and `I ⊆ Λ` an ideal. For a complex `N` of `Λ`-modules, the
complex `\underline{N}^∧` whose terms are the completed constant sheaves
`\underline{Nᵏ}^∧ = limₙ \underline{Nᵏ/IⁿNᵏ}` on `X_proét` is the termwise limit of the tower of
complexes `n ↦ \underline{N/IⁿN}`. The transition maps of this tower are termwise surjective, and
`X_proét` has enough weakly contractible objects, so the termwise limit is also the derived limit:
`\underline{N}^∧ = R lim \underline{N/IⁿN}` in `D(X_proét, Λ)` (Stacks 0947 (3)). This is the
identification `\underline{M^•}^∧ = lim \underline{M^•/IⁿM^•} = R lim \underline{M^•/IⁿM^•}` used
in the proof of Stacks 09C6.

## Main definitions

* `CategoryTheory.Functor.mapHomologicalComplexDiagram`: a diagram of functors applied termwise to
  a complex, as a diagram of complexes.
* `AlgebraicGeometry.ProEtale.adicQuotientConstantTower`: the tower of functors
  `M ↦ \underline{M/IⁿM}` from `Λ`-modules to sheaves of coefficient modules on `X_proét`.
* `AlgebraicGeometry.ProEtale.adicQuotientConstantComplexTower`: the tower of complexes
  `n ↦ \underline{N/IⁿN}` of a complex `N` of `Λ`-modules.

## Main results

* `CategoryTheory.Functor.isLimitMapHomologicalComplexCone`: a cone of functors which is a limit
  cone objectwise gives, applied termwise to any complex, a limit cone of complexes.
* `AlgebraicGeometry.ProEtale.isDerivedLimitWithProjections_completedConstantSheaf`: for a complex
  `N` of `Λ`-modules, `\underline{N}^∧` is the derived limit of `n ↦ \underline{N/IⁿN}` in
  `D(X_proét, Λ)`, the projections being the reductions.
* `AlgebraicGeometry.ProEtale.isDerivedLimitWithProjections_completedConstantCoefficientComplex`:
  the same for the complex `\underline{M^•}^∧` attached to a complex `M^•` of `Λ^∧`-modules.

## References

* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947)
* [Stacks Project, Tag 09C6](https://stacks.math.columbia.edu/tag/09C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {J : Type u₁} [Category.{v₁} J] {A : Type u₂} [Category.{v₂} A]
  {B : Type u₃} [Category.{v₃} B]
  [HasZeroMorphisms A] [HasZeroMorphisms B] {ι : Type*} (c : ComplexShape ι)

/-- A diagram `Φ` of functors `A ⥤ B`, each preserving zero morphisms, applied termwise to a
complex `N` in `A`: the diagram `j ↦ Φⱼ(N)` of complexes in `B`. -/
def mapHomologicalComplexDiagram (Φ : J ⥤ A ⥤ B) [∀ j, (Φ.obj j).PreservesZeroMorphisms]
    (N : HomologicalComplex A c) : J ⥤ HomologicalComplex B c where
  obj j := ((Φ.obj j).mapHomologicalComplex c).obj N
  map f := (NatTrans.mapHomologicalComplex (Φ.map f) c).app N
  map_id j := by
    rw [Φ.map_id, NatTrans.mapHomologicalComplex_id]
    rfl
  map_comp f g := by
    rw [Φ.map_comp, NatTrans.mapHomologicalComplex_comp]
    rfl

/-- The value of `Φ.mapHomologicalComplexDiagram c N` at `j` is `Φⱼ(N)`. -/
@[simp]
theorem mapHomologicalComplexDiagram_obj (Φ : J ⥤ A ⥤ B) [∀ j, (Φ.obj j).PreservesZeroMorphisms]
    (N : HomologicalComplex A c) (j : J) :
    (Φ.mapHomologicalComplexDiagram c N).obj j = ((Φ.obj j).mapHomologicalComplex c).obj N :=
  rfl

/-- The component in degree `i` of the image of `f : j ⟶ j'` under
`Φ.mapHomologicalComplexDiagram c N` is the component of `Φ.map f` at `Nᵢ`. -/
@[simp]
theorem mapHomologicalComplexDiagram_map_f (Φ : J ⥤ A ⥤ B)
    [∀ j, (Φ.obj j).PreservesZeroMorphisms] (N : HomologicalComplex A c) {j j' : J} (f : j ⟶ j')
    (i : ι) : ((Φ.mapHomologicalComplexDiagram c N).map f).f i = (Φ.map f).app (N.X i) :=
  rfl

variable {c} in
/-- Two diagrams of functors which become isomorphic after composing with functors `G` and `G'`
give, applied termwise to a complex `N`, isomorphic diagrams of complexes after applying `G` and
`G'` termwise. -/
def mapHomologicalComplexDiagramCompIso {B' : Type*} [Category* B'] [HasZeroMorphisms B']
    {B'' : Type*} [Category* B''] [HasZeroMorphisms B'']
    {Φ : J ⥤ A ⥤ B} {Ψ : J ⥤ A ⥤ B'} [∀ j, (Φ.obj j).PreservesZeroMorphisms]
    [∀ j, (Ψ.obj j).PreservesZeroMorphisms] {G : B ⥤ B''} {G' : B' ⥤ B''}
    [G.PreservesZeroMorphisms] [G'.PreservesZeroMorphisms]
    (e : Φ ⋙ (Functor.whiskeringRight A B B'').obj G ≅
      Ψ ⋙ (Functor.whiskeringRight A B' B'').obj G')
    (N : HomologicalComplex A c) :
    Φ.mapHomologicalComplexDiagram c N ⋙ G.mapHomologicalComplex c ≅
      Ψ.mapHomologicalComplexDiagram c N ⋙ G'.mapHomologicalComplex c :=
  NatIso.ofComponents
    (fun j => HomologicalComplex.Hom.isoOfComponents (fun i => (e.app j).app (N.X i))
      (fun i i' _ => ((e.app j).hom.naturality (N.d i i')).symm))
    (fun {j j'} f => by
      ext i
      exact NatTrans.congr_app (e.hom.naturality f) (N.X i))

variable {c} in
/-- A cone `γ : G ⟶ Φ` over a diagram of functors, applied termwise to a complex `N`: the cone
`G(N) ⟶ Φⱼ(N)` over the diagram of complexes `j ↦ Φⱼ(N)`. -/
def mapHomologicalComplexCone {Φ : J ⥤ A ⥤ B} [∀ j, (Φ.obj j).PreservesZeroMorphisms]
    (s : Cone Φ) [s.pt.PreservesZeroMorphisms] (N : HomologicalComplex A c) :
    Cone (Φ.mapHomologicalComplexDiagram c N) where
  pt := (s.pt.mapHomologicalComplex c).obj N
  π :=
    { app j :=
        { f i := (s.π.app j).app (N.X i)
          comm' i i' _ := ((s.π.app j).naturality (N.d i i')).symm }
      naturality j j' f := by
        ext i
        simp only [Functor.const_obj_obj, Functor.const_obj_map, HomologicalComplex.comp_f,
          Category.id_comp, mapHomologicalComplexDiagram_map_f]
        exact (NatTrans.congr_app (s.w f) (N.X i)).symm }

variable {c} in
/-- **Termwise limits of complexes.** If a cone `s` over a diagram `Φ` of functors `A ⥤ B` is a
limit cone after evaluation at every object of `A`, then applying it termwise to any complex `N`
gives a limit cone over the diagram of complexes `j ↦ Φⱼ(N)`. -/
def isLimitMapHomologicalComplexCone {Φ : J ⥤ A ⥤ B} [∀ j, (Φ.obj j).PreservesZeroMorphisms]
    (s : Cone Φ) [s.pt.PreservesZeroMorphisms]
    (hs : ∀ a : A, IsLimit (((evaluation A B).obj a).mapCone s)) (N : HomologicalComplex A c) :
    IsLimit (mapHomologicalComplexCone s N) :=
  HomologicalComplex.isLimitOfEval _ _ fun i =>
    { lift t := (hs (N.X i)).lift ⟨t.pt, ⟨fun j => t.π.app j, fun _ _ f => t.π.naturality f⟩⟩
      fac t j := (hs (N.X i)).fac ⟨t.pt, ⟨fun j => t.π.app j, fun _ _ f => t.π.naturality f⟩⟩ j
      uniq t m hm := (hs (N.X i)).uniq
        ⟨t.pt, ⟨fun j => t.π.app j, fun _ _ f => t.π.naturality f⟩⟩ m hm }

end CategoryTheory.Functor

universe u w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

variable (X : Scheme.{u}) (Λ : Type (max (u + 1) w)) [CommRing Λ] (I : Ideal Λ)

/-- The tower of functors `M ↦ \underline{M/IⁿM}` from `Λ`-modules to sheaves of modules over the
constant coefficient ring sheaf on `X_proét`, the transition maps being the reductions. -/
def adicQuotientConstantTower :
    ℕᵒᵖ ⥤ ModuleCat.{max (u + 1) w} Λ ⥤
      RingedSite.Modules.{u + 1, u, max (u + 1) w}
        (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ) where
  obj n := (adicQuotientModuleFunctor.{max (u + 1) w, max (u + 1) w} Λ I ⋙
      (evaluation ℕᵒᵖ (ModuleCat.{max (u + 1) w} Λ)).obj n) ⋙
    constantSheafOverCoefficients.{u, max (u + 1) w, w} X Λ
  map f := Functor.whiskerRight
      (Functor.whiskerLeft (adicQuotientModuleFunctor.{max (u + 1) w, max (u + 1) w} Λ I)
        ((evaluation ℕᵒᵖ (ModuleCat.{max (u + 1) w} Λ)).map f))
    (constantSheafOverCoefficients.{u, max (u + 1) w, w} X Λ)
  map_id n := by
    ext M : 2
    simp
  map_comp f g := by
    ext M : 2
    simp

/-- Each functor `M ↦ \underline{M/IⁿM}` of the tower is additive. -/
instance adicQuotientConstantTower_obj_additive (n : ℕᵒᵖ) :
    ((adicQuotientConstantTower.{u, w} X Λ I).obj n).Additive :=
  inferInstanceAs ((_ ⋙ _) ⋙ constantSheafOverCoefficients.{u, max (u + 1) w, w} X Λ).Additive

/-- The reductions `\underline{M}^∧ ⟶ \underline{M/IⁿM}` of the completed constant sheaf of a
`Λ`-module, as a cone over the tower of functors `M ↦ \underline{M/IⁿM}`. -/
def completedConstantCoefficientSheafCone : Cone (adicQuotientConstantTower.{u, w} X Λ I) where
  pt := completedConstantCoefficientSheafFunctor.{u, max (u + 1) w, w} X Λ I
  π :=
    { app n :=
        { app M := (moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, w} X Λ).map
            (limit.π (((Functor.whiskeringRight ℕᵒᵖ _ _).obj (constantSheaf
              (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))).obj
                ((adicQuotientModuleFunctor.{max (u + 1) w, max (u + 1) w} Λ I).obj M)) n)
          naturality M M' g := by
            change (moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, w} X Λ).map
                (lim.map _) ≫
              (moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, w} X Λ).map _ =
              (moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, w} X Λ).map _ ≫
              (moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, w} X Λ).map _
            rw [← Functor.map_comp, ← Functor.map_comp]
            congr 1
            exact limMap_π _ _ }
      naturality n n' f := by
        ext M : 2
        change (moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, w} X Λ).map _ =
          (moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, w} X Λ).map _ ≫
          (moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, w} X Λ).map _
        rw [← Functor.map_comp]
        congr 1
        exact (limit.w _ f).symm }

/-- The completed constant sheaf functor `M ↦ \underline{M}^∧` is additive. -/
instance completedConstantCoefficientSheafCone_pt_additive :
    (completedConstantCoefficientSheafCone.{u, w} X Λ I).pt.Additive :=
  inferInstanceAs (completedConstantCoefficientSheafFunctor.{u, max (u + 1) w, w} X Λ I).Additive

/-- The completed constant sheaf of a module is the limit of the constant sheaves of its adic
quotients, read over the constant coefficient ring sheaf, objectwise. -/
def isLimitEvaluationMapConeCompletedConstantCoefficientSheafCone
    (M : ModuleCat.{max (u + 1) w} Λ) :
    IsLimit (((evaluation _ _).obj M).mapCone
      (completedConstantCoefficientSheafCone.{u, w} X Λ I)) :=
  isLimitOfPreserves (moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, w} X Λ)
    (limit.isLimit (((Functor.whiskeringRight ℕᵒᵖ _ _).obj (constantSheaf
      (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))).obj
        ((adicQuotientModuleFunctor.{max (u + 1) w, max (u + 1) w} Λ I).obj M)))

/-- The tower of complexes `n ↦ \underline{N/IⁿN}` of sheaves of coefficient modules attached to
a complex `N` of `Λ`-modules, the transition maps being the reductions. -/
abbrev adicQuotientConstantComplexTower (N : CochainComplex (ModuleCat.{max (u + 1) w} Λ) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)) ℤ :=
  (adicQuotientConstantTower.{u, w} X Λ I).mapHomologicalComplexDiagram _ N

/-- The transition maps `\underline{N/Iⁿ⁺¹N} ⟶ \underline{N/IⁿN}` of the tower of complexes are
epimorphisms in every degree. -/
theorem epi_adicQuotientConstantComplexTower_map_f
    (N : CochainComplex (ModuleCat.{max (u + 1) w} Λ) ℤ) (n : ℕ) (i : ℤ) :
    Epi (((adicQuotientConstantComplexTower.{u, w} X Λ I N).map
      (homOfLE (Nat.le_succ n)).op).f i) := by
  have : Epi ((adicQuotientModuleSystem Λ I (N.X i)).map (homOfLE (Nat.le_succ n)).op) :=
    (ModuleCat.epi_iff_surjective _).mpr (surjective_adicQuotientModuleSystem_map Λ I (N.X i) n)
  have : (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).IsLeftAdjoint :=
    (constantSheafAdj (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)
      Scheme.ProEt.isTerminal_mk_id).isLeftAdjoint
  change Epi ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, w} X Λ).map
    ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).map
      ((adicQuotientModuleSystem Λ I (N.X i)).map (homOfLE (Nat.le_succ n)).op)))
  have h₁ := (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).map_epi
    ((adicQuotientModuleSystem Λ I (N.X i)).map (homOfLE (Nat.le_succ n)).op)
  have : Functor.PreservesEpimorphisms
      (moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, w} X Λ) :=
    Functor.preservesEpimorphisms_of_isLeftAdjoint _
  exact (moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, w} X Λ).map_epi _

/-- **The complex of completed constant sheaves is a derived limit.** For a complex `N` of
`Λ`-modules, the complex `\underline{N}^∧` of completed constant sheaves on `X_proét` is the
derived limit `R lim \underline{N/IⁿN}` in `D(X_proét, Λ)`, the projections being the
reductions. -/
theorem isDerivedLimitWithProjections_completedConstantSheaf
    (N : CochainComplex (ModuleCat.{max (u + 1) w} Λ) ℤ) :
    NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (adicQuotientConstantComplexTower.{u, w} X Λ I N ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.obj
        (((completedConstantCoefficientSheafFunctor.{u, max (u + 1) w, w} X Λ I)
          |>.mapHomologicalComplex _).obj N))
      (fun n => DerivedCategory.Q.map ((Functor.mapHomologicalComplexCone
        (completedConstantCoefficientSheafCone.{u, w} X Λ I) N).π.app ⟨n⟩)) := by
  let S := (Scheme.ProEt.testingFamily.{max (u + 1) w} X).toSituation
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O)
  let T := adicQuotientConstantComplexTower.{u, w} X Λ I N
  -- The hypothesis is supplied after the tower has been instantiated: elaborating both at once
  -- makes the unifier compare the two presentations of the category of coefficient modules.
  have hT := epi_adicQuotientConstantComplexTower_map_f X Λ I N
  have h := Stacks.WeaklyContractible.isDerivedLimitWithProjections_Q_limit_of_epi_f.{max (u + 1) w,
    u, u + 1, max (u + 1) w} (C := X.ProEt) (J := Scheme.ProEt.topology X) S T
  replace h := h hT
  have hs := Functor.isLimitMapHomologicalComplexCone
    (completedConstantCoefficientSheafCone.{u, w} X Λ I)
    (isLimitEvaluationMapConeCompletedConstantCoefficientSheafCone X Λ I) N
  let e := DerivedCategory.Q.mapIso (hs.conePointUniqueUpToIso (limit.isLimit T))
  have heq : (fun n : ℕ => e.hom ≫ DerivedCategory.Q.map (limit.π T ⟨n⟩)) =
      fun n => DerivedCategory.Q.map ((Functor.mapHomologicalComplexCone
        (completedConstantCoefficientSheafCone.{u, w} X Λ I) N).π.app ⟨n⟩) := by
    funext n
    rw [Functor.mapIso_hom, ← Functor.map_comp]
    exact congrArg _ (IsLimit.conePointUniqueUpToIso_hom_comp hs (limit.isLimit T) ⟨n⟩)
  exact heq ▸ h.ofIso e.symm

/-- **The complex of completed constant sheaves of a complex of `Λ^∧`-modules is a derived
limit.** For a complex `M^•` of `Λ^∧`-modules,
`\underline{M^•}^∧ = R lim \underline{M^•/IⁿM^•}` in `D(X_proét, Λ)`, the projections being the
reductions. -/
theorem isDerivedLimitWithProjections_completedConstantCoefficientComplex
    (M : CochainComplex (ModuleCat.{max (u + 1) w} (AdicCompletion I Λ)) ℤ) :
    NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (adicQuotientConstantComplexTower.{u, w} X Λ I
        (((restrictToCoefficients.{max (u + 1) w, max (u + 1) w} Λ I).mapHomologicalComplex _).obj
          M) ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.obj
        ((completedConstantCoefficientComplex.{u, max (u + 1) w, w} X Λ I).obj M))
      (fun n => DerivedCategory.Q.map ((Functor.mapHomologicalComplexCone
        (completedConstantCoefficientSheafCone.{u, w} X Λ I)
          (((restrictToCoefficients.{max (u + 1) w, max (u + 1) w} Λ I).mapHomologicalComplex
            _).obj M)).π.app ⟨n⟩)) :=
  isDerivedLimitWithProjections_completedConstantSheaf X Λ I _

end AlgebraicGeometry.ProEtale

end
