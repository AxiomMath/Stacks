module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConeDifferentialGradedModuleToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAdmissibleConnecting

/-!
# The base change of an admissible short exact sequence along a morphism of ringed topoi

Let `f : X ⟶ Y` be a morphism of ringed topoi, presented as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedToposDirectImage.lean` by an
additive lax monoidal functor `G` of sheaves of modules together with a unital homomorphism
`ψ : A ⟶ f_*B`. Let `0 → K → L → M → 0` be an admissible short exact sequence of right
differential graded `A`-modules and suppose that each of the three has a base change along
`(f, B, ψ)`, that is, an object corepresenting `Q ↦ Hom_A(-, f_{*,ψ}Q)`. Then **the base changes
form an admissible short exact sequence of right differential graded `B`-modules**, the maps
being the base changes of the two given ones. This is the clause of the source's proof of
Tag 0FSC about the pullback `0 → f^*P → f^*P' → f^*P'' → 0`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.baseChangeGradedHom`: the base change of a
  homomorphism of the underlying graded modules, read off the corepresentability data through
  `SheafOfModules.DifferentialGradedModule.toposGradedEquiv`.
* `SheafOfModules.DifferentialGradedModule.GradedSplitting.toposBaseChange`: the base change of a
  graded splitting.

## Main results

* `SheafOfModules.DifferentialGradedModule.baseChangeGradedHom_comp`, `baseChangeGradedHom_id`,
  `baseChangeGradedHom_add` and `baseChangeGradedHom_ofDifferentialGradedMap`: the base change of
  graded homomorphisms is functorial, additive, and agrees with the base change of morphisms of
  differential graded modules.
* `SheafOfModules.DifferentialGradedModule.IsAdmissibleShortExact.toposBaseChange`: **the base
  change of an admissible short exact sequence is an admissible short exact sequence.**

## Implementation notes

The retraction and the section of a graded splitting are homomorphisms of graded modules only,
so the universal property of a base change, which is about morphisms of differential graded
modules, does not transport them directly. `toposGradedEquiv` does: it reads a graded
homomorphism out of a base change through the cofree differential graded module. Everything
below is computed degreewise from the unit formula `toposGradedEquiv_eq`: the base change of a
graded homomorphism `Φ : P ⟶ P'` is the unique graded homomorphism `Φ'` with
`η_P ≫ f_*Φ' = Φ ≫ η_{P'}` in every degree, `η` being the unit of the base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe w v₁ u₁ v₂ u₂

namespace SheafOfModules.DifferentialGradedModule

section ToposPullback

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (G : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
  [G.LaxMonoidal] [G.Additive]
  {B : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp)}
  (ψ : A ⟶ toposPushforwardAlgebra G B) (hψ : ψ.IsUnital)
  {P P' P'' : DifferentialGradedModule.{w, w, w} A}
  {T T' T'' : DifferentialGradedModule.{w, w, w} B}

/-- **The unit formula, degreewise**: the base change of a graded homomorphism out of `T`, in
degree `n`, is the unit followed by the direct image of the homomorphism. -/
theorem toposGradedEquiv_app
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (Q : DifferentialGradedModule.{w, w, w} B)
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded T)
      (GradedModule.ofDifferentialGraded Q)) (n : ℤ) :
    (toposGradedEquiv G ψ hψ e Q Φ).app n =
      (e.homEquiv (𝟙 T)).toHomologicalComplex.f n ≫ G.map (Φ.app n) := by
  rw [toposGradedEquiv_eq]
  rfl

/-- **The base change of a homomorphism of the underlying graded modules**: the graded
homomorphism between the two base changes whose transpose is the given homomorphism followed by
the unit of the second base change. -/
noncomputable def baseChangeGradedHom
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (e' : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P')).CorepresentableBy T')
    (Φ : GradedModule.ofDifferentialGraded P ⟶ GradedModule.ofDifferentialGraded P') :
    GradedModule.ofDifferentialGraded T ⟶ GradedModule.ofDifferentialGraded T' :=
  (toposGradedEquiv G ψ hψ e T').symm
    (Φ ≫ GradedModule.ofDifferentialGradedMap (e'.homEquiv (𝟙 T')))

/-- The degree-`n` component of the unit `P ⟶ f_{*,ψ}T` of a base change, with its target spelled
`G(T^n)`. -/
noncomputable def baseChangeUnitApp
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T) (n : ℤ) :
    P.complex.X n ⟶ G.obj (T.complex.X n) :=
  (e.homEquiv (𝟙 T)).toHomologicalComplex.f n

/-- **The characterising identity of the base change of a graded homomorphism**, degreewise:
`η_P ≫ f_*Φ' = Φ ≫ η_{P'}`. -/
theorem baseChangeGradedHom_app
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (e' : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P')).CorepresentableBy T')
    (Φ : GradedModule.ofDifferentialGraded P ⟶ GradedModule.ofDifferentialGraded P') (n : ℤ) :
    baseChangeUnitApp G ψ hψ e n ≫ G.map (gradedApp (baseChangeGradedHom G ψ hψ e e' Φ) n) =
      gradedApp Φ n ≫ baseChangeUnitApp G ψ hψ e' n := by
  have h := toposGradedEquiv_app G ψ hψ e T' (baseChangeGradedHom G ψ hψ e e' Φ) n
  rw [baseChangeGradedHom, Equiv.apply_symm_apply] at h
  exact h.symm

/-- A graded homomorphism out of a base change is determined by the identity it satisfies. -/
theorem baseChangeGradedHom_eq_of_app
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (e' : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P')).CorepresentableBy T')
    (Φ : GradedModule.ofDifferentialGraded P ⟶ GradedModule.ofDifferentialGraded P')
    (Ψ : GradedModule.ofDifferentialGraded T ⟶ GradedModule.ofDifferentialGraded T')
    (h : ∀ n, baseChangeUnitApp G ψ hψ e n ≫ G.map (gradedApp Ψ n) =
      gradedApp Φ n ≫ baseChangeUnitApp G ψ hψ e' n) :
    baseChangeGradedHom G ψ hψ e e' Φ = Ψ := by
  refine (toposGradedEquiv G ψ hψ e T').injective (GradedModule.Hom.ext fun n => ?_)
  refine (toposGradedEquiv_app G ψ hψ e T' _ n).trans ?_
  refine Eq.trans ?_ (toposGradedEquiv_app G ψ hψ e T' _ n).symm
  exact (baseChangeGradedHom_app G ψ hψ e e' Φ n).trans (h n).symm

/-- **The base change of graded homomorphisms preserves composition.** -/
theorem baseChangeGradedHom_comp
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (e' : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P')).CorepresentableBy T')
    (e'' : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P'')).CorepresentableBy T'')
    (Φ : GradedModule.ofDifferentialGraded P ⟶ GradedModule.ofDifferentialGraded P')
    (Ψ : GradedModule.ofDifferentialGraded P' ⟶ GradedModule.ofDifferentialGraded P'') :
    baseChangeGradedHom G ψ hψ e e'' (Φ ≫ Ψ) =
      baseChangeGradedHom G ψ hψ e e' Φ ≫ baseChangeGradedHom G ψ hψ e' e'' Ψ := by
  refine baseChangeGradedHom_eq_of_app G ψ hψ e e'' _ _ fun n => ?_
  rw [gradedApp_comp, gradedApp_comp, G.map_comp, ← Category.assoc, baseChangeGradedHom_app,
    Category.assoc, baseChangeGradedHom_app, Category.assoc]

/-- **The base change of the identity is the identity.** -/
theorem baseChangeGradedHom_id
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T) :
    baseChangeGradedHom G ψ hψ e e (𝟙 (GradedModule.ofDifferentialGraded P)) =
      𝟙 (GradedModule.ofDifferentialGraded T) := by
  refine baseChangeGradedHom_eq_of_app G ψ hψ e e _ _ fun n => ?_
  rw [gradedApp_id, gradedApp_id, G.map_id, Category.comp_id, Category.id_comp]

/-- **The base change of graded homomorphisms is additive.** -/
theorem baseChangeGradedHom_add
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (e' : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P')).CorepresentableBy T')
    (Φ Φ' : GradedModule.ofDifferentialGraded P ⟶ GradedModule.ofDifferentialGraded P') :
    baseChangeGradedHom G ψ hψ e e' (Φ + Φ') =
      baseChangeGradedHom G ψ hψ e e' Φ + baseChangeGradedHom G ψ hψ e e' Φ' := by
  refine baseChangeGradedHom_eq_of_app G ψ hψ e e' _ _ fun n => ?_
  rw [gradedApp_add, gradedApp_add, G.map_add, Preadditive.comp_add, Preadditive.add_comp,
    baseChangeGradedHom_app, baseChangeGradedHom_app]

/-- **On morphisms of differential graded modules the graded base change is the base change.** -/
theorem baseChangeGradedHom_ofDifferentialGradedMap
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (e' : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P')).CorepresentableBy T')
    (φ : P ⟶ P') :
    baseChangeGradedHom G ψ hψ e e' (GradedModule.ofDifferentialGradedMap φ) =
      GradedModule.ofDifferentialGradedMap (baseChangeHom G ψ hψ e e' φ) := by
  refine baseChangeGradedHom_eq_of_app G ψ hψ e e' _ _ fun n => ?_
  have h : e.homEquiv (𝟙 T) ≫ (toposPushforward G ψ hψ).map (baseChangeHom G ψ hψ e e' φ) =
      φ ≫ e'.homEquiv (𝟙 T') :=
    (e.homEquiv_comp (baseChangeHom G ψ hψ e e' φ) (𝟙 T)).symm.trans
      ((congrArg e.homEquiv ((Category.id_comp _).trans (Category.comp_id _).symm)).trans
        (homEquiv_baseChangeHom_comp G ψ hψ e e' φ (𝟙 T')))
  exact congrArg (fun χ : P ⟶ (toposPushforward G ψ hψ).obj T' => χ.toHomologicalComplex.f n) h

/-- **The base change of a graded splitting.** -/
noncomputable def GradedSplitting.toposBaseChange {φ : P ⟶ P'} {χ : P' ⟶ P''}
    (S : GradedSplitting φ χ)
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (e' : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P')).CorepresentableBy T')
    (e'' : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P'')).CorepresentableBy T'') :
    GradedSplitting (baseChangeHom G ψ hψ e e' φ) (baseChangeHom G ψ hψ e' e'' χ) where
  r := baseChangeGradedHom G ψ hψ e' e S.r
  s := baseChangeGradedHom G ψ hψ e'' e' S.s
  f_r := by
    rw [← baseChangeGradedHom_ofDifferentialGradedMap, ← baseChangeGradedHom_comp, S.f_r,
      baseChangeGradedHom_id]
  s_g := by
    rw [← baseChangeGradedHom_ofDifferentialGradedMap, ← baseChangeGradedHom_comp, S.s_g,
      baseChangeGradedHom_id]
  id := by
    rw [← baseChangeGradedHom_ofDifferentialGradedMap,
      ← baseChangeGradedHom_ofDifferentialGradedMap, ← baseChangeGradedHom_comp,
      ← baseChangeGradedHom_comp, ← baseChangeGradedHom_add, S.id,
      baseChangeGradedHom_id]

/-- **The base change of an admissible short exact sequence of right differential graded modules
is an admissible short exact sequence**, as soon as each of its three terms has a base change. -/
theorem IsAdmissibleShortExact.toposBaseChange {φ : P ⟶ P'} {χ : P' ⟶ P''}
    (h : IsAdmissibleShortExact φ χ)
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (e' : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P')).CorepresentableBy T')
    (e'' : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P'')).CorepresentableBy T'') :
    IsAdmissibleShortExact (baseChangeHom G ψ hψ e e' φ) (baseChangeHom G ψ hψ e' e'' χ) :=
  Nonempty.elim h fun S ↦ ⟨S.toposBaseChange G ψ hψ e e' e''⟩

end ToposPullback

end SheafOfModules.DifferentialGradedModule

end
