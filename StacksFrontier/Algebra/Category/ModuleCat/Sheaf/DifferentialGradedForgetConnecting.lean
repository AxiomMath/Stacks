module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedForgetHomotopyTriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiIsomorphisms
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedShiftFunctor

/-!
# Forgetting the action on the connecting morphism of a short exact sequence

Let `X` be a ringed site, `(A, d)` a sheaf of differential graded algebras on it, and
`0 → K → L → M → 0` a short exact sequence of right differential graded `A`-modules. The
connecting morphism `δ = - p ∘ q⁻¹ : M ⟶ K[1]` of [Stacks, Tag 0FTB] lives in the derived
category `D(A, d)`. Forgetting the action of `A` sends it to a morphism of the derived category
`D(O)` of the underlying complexes of `O`-modules, and the underlying sequence of complexes is
short exact (Tag 0FRK), so it has its own connecting morphism there,
`DerivedCategory.triangleOfSESδ`. This file proves that the two agree: **forgetting the action
commutes with the connecting morphisms**.

## Main results

* `SheafOfModules.toCochainComplex_faithful`: forgetting the action is faithful.
* `SheafOfModules.DifferentialGradedModule.derivedForget_map_shortExactδTranslate`: forgetting
  the action on `δ`, with the translation of `D(A, d)` moved past the forgetful functor, is
  Mathlib's connecting morphism of the underlying short exact sequence of complexes.

## Implementation notes

Both connecting morphisms are built from the same data. The underlying complex of the cone of
Tag 0FS5 is Mathlib's mapping cone, its comparison `q` with the third term is Mathlib's
`CochainComplex.mappingCone.descShortComplex`, and its projection `p` is, up to the sign the
source attaches to it, the third arrow of Mathlib's mapping-cone triangle. The proof transports
along these identifications of complexes, which are equalities, by `eqToHom`.

## References

* [Stacks Project, Tag 0FTB](https://stacks.math.columbia.edu/tag/0FTB)
* [Stacks Project, Tag 0FRK](https://stacks.math.columbia.edu/tag/0FRK)
-/

@[expose] public section

open CategoryTheory

universe w u

namespace SheafOfModules

/-- **Forgetting the action of a right differential graded module is faithful**: a morphism of
right differential graded modules is its underlying morphism of complexes. -/
instance toCochainComplex_faithful {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (A : DifferentialGradedAlgebra.{u, u} R) :
    (toCochainComplex.{u, u, u} A).Faithful :=
  ⟨fun h => DifferentialGradedModule.Hom.ext fun n => congrArg (fun φ => φ.f n) h⟩

end SheafOfModules

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  [HasDerivedCategory.{w} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- A functor `G` with `T ⋙ G = H` sends `T(f)⁻¹ ≫ T(g)` to `H(f)⁻¹ ≫ H(g)`, up to the
transports along the object-level equalities. -/
private theorem map_inv_comp_map_of_comp_eq {C D E : Type*} [Category* C] [Category* D]
    [Category* E] {T : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (h : T ⋙ G = H) {P Q Z : C}
    (f : P ⟶ Q) (g : P ⟶ Z) [IsIso (T.map f)] [IsIso (H.map f)] :
    G.map (inv (T.map f) ≫ T.map g) =
      eqToHom (Functor.congr_obj h Q) ≫ inv (H.map f) ≫ H.map g ≫
        eqToHom (Functor.congr_obj h Z).symm := by
  subst h
  simp

/-- Forgetting the action on `T(f)⁻¹ ≫ T(g) ≫ e`, for morphisms `f` and `g` of modules, `T` the
localization functor and `e` a transport, is `Q(f)⁻¹ ≫ Q(g)` on the underlying complexes, followed
by the transport. -/
private theorem derivedForget_map_inv_comp_map {P Q Z : DifferentialGradedModule.{u, u, u} A}
    {W : HomotopyCategory.{u, u, u} A}
    {K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : P ⟶ Q) (g : P ⟶ Z) (e : (HomotopyCategory.quotient A).obj Z = W) (hZ : Z.complex = K)
    (e' : DerivedCategory.Q.obj W.as.complex = DerivedCategory.Q.obj K)
    [IsIso ((toDerivedCategory A).map ((HomotopyCategory.quotient A).map f))]
    [IsIso (DerivedCategory.Q.map f.toHomologicalComplex)] :
    (derivedForget.{w} A).map
        (inv ((toDerivedCategory A).map ((HomotopyCategory.quotient A).map f)) ≫
        (toDerivedCategory A).map ((HomotopyCategory.quotient A).map g) ≫
        eqToHom (congrArg (toDerivedCategory A).obj e)) ≫ eqToHom e' =
      inv (DerivedCategory.Q.map f.toHomologicalComplex) ≫
        DerivedCategory.Q.map g.toHomologicalComplex ≫
          eqToHom (congrArg DerivedCategory.Q.obj hZ) := by
  subst e hZ
  have : IsIso ((homotopyForget.{w} A).map ((HomotopyCategory.quotient A).map f)) :=
    inferInstanceAs (IsIso (DerivedCategory.Q.map f.toHomologicalComplex))
  rw [eqToHom_refl, Category.comp_id,
    map_inv_comp_map_of_comp_eq (toDerivedCategory_comp_derivedForget.{w} A)]
  show (𝟙 _ ≫ inv ((homotopyForget.{w} A).map ((HomotopyCategory.quotient A).map f)) ≫
    (homotopyForget.{w} A).map ((HomotopyCategory.quotient A).map g) ≫ 𝟙 _) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id, Category.comp_id, eqToHom_refl, Category.comp_id]
  rfl

/-- In the derived category, `Q(q)⁻¹ ≫ Q(p)` only depends on `q` and `p` up to transport along
equalities of their source and target complexes. -/
private theorem inv_Q_map_comp_Q_map_eq {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory.{w} C] {M₃ K K' L L' : CochainComplex C ℤ} (hK : K = K') (hL : L = L')
    (q : K ⟶ M₃) (q' : K' ⟶ M₃) (hq : HEq q q') (p : K ⟶ L) (p' : K' ⟶ L') (hp : HEq p p')
    [IsIso (DerivedCategory.Q.map q)] [i : IsIso (DerivedCategory.Q.map q')] :
    inv (DerivedCategory.Q.map q) ≫ DerivedCategory.Q.map p ≫
        eqToHom (congrArg DerivedCategory.Q.obj hL) =
      inv (DerivedCategory.Q.map q') ≫ DerivedCategory.Q.map p' := by
  subst hK hL
  obtain rfl := eq_of_heq hq
  obtain rfl := eq_of_heq hp
  simp

/-- **Forgetting the action commutes with the connecting morphisms.** For a short exact sequence
`0 → K → L → M → 0` of right differential graded `A`-modules, the connecting morphism
`δ : M ⟶ K[1]` of `D(A, d)` ([Stacks, Tag 0FTB]), with its action forgotten and the translation
moved past the forgetful functor, is the connecting morphism `M ⟶ K[1]` in `D(O)` of the
underlying short exact sequence of complexes (Tag 0FRK). -/
theorem derivedForget_map_shortExactδTranslate
    {S : ShortComplex (DifferentialGradedModule.{u, u, u} A)} (hS : S.ShortExact) :
    (derivedForget.{w} A).map (shortExactδTranslate hS ≫
        ((toDerivedCategory A).commShiftIso (1 : ℤ)).inv.app
          ((HomotopyCategory.quotient A).obj S.X₁)) ≫
      eqToHom (congrArg DerivedCategory.Q.obj
        (HomotopyCategory.shiftFunctor_obj_complex A 1 S.X₁)) ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app S.X₁.complex =
    DerivedCategory.triangleOfSESδ (toCochainComplex_shortExact A S hS) := by
  have : IsIso ((toDerivedCategory A).map ((HomotopyCategory.quotient A).map (coneDescHom S))) :=
    isIso_moduleToDerivedCategory_map_coneDescHom hS
  have : IsIso (DerivedCategory.Q.map (coneDescHom S).toHomologicalComplex) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (quasiIso_coneDescHom hS)
  have h1 : shortExactδTranslate hS ≫ ((toDerivedCategory A).commShiftIso (1 : ℤ)).inv.app
          ((HomotopyCategory.quotient A).obj S.X₁) =
      inv ((toDerivedCategory A).map ((HomotopyCategory.quotient A).map (coneDescHom S))) ≫
        (toDerivedCategory A).map ((HomotopyCategory.quotient A).map
          (-(conePackage S.f).projection)) ≫
          eqToHom (congrArg (toDerivedCategory A).obj
            (HomotopyCategory.shiftFunctor_obj A S.X₁).symm) := by
    simp [shortExactδTranslate, shiftTranslateIso, shortExactδ]
  have hc := (conePackage S.f).cone_complex
  have hs := (shiftPackage S.X₁).shifted_complex
  have hheq : HEq (-(conePackage S.f).projection).toHomologicalComplex
      (CochainComplex.mappingCone.triangle S.f.toHomologicalComplex).mor₃ :=
    (neg_heq hc hs (conePackage S.f).projection_complex).trans
      (heq_of_eq (CochainComplex.mappingCone.triangle_mor₃_eq _).symm)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _)
    ((congrArg (fun t => (derivedForget.{w} A).map t ≫ eqToHom _) h1).trans
      (derivedForget_map_inv_comp_map _ _ (HomotopyCategory.shiftFunctor_obj A S.X₁).symm hs
        _))).trans ?_
  have := CochainComplex.mappingCone.quasiIso_descShortComplex
    (toCochainComplex_shortExact A S hS)
  have hqheq : HEq (coneDescHom S).toHomologicalComplex
      (CochainComplex.mappingCone.descShortComplex (S.map (toCochainComplex A))) :=
    (conj_eqToHom_iff_heq (coneDescHom S).toHomologicalComplex (coneDesc S) hc rfl).1
      (Category.comp_id _).symm
  rw [inv_Q_map_comp_Q_map_eq hc hs _ _ hqheq _ _ hheq
    (i := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 this)]
  exact Category.assoc _ _ _

end SheafOfModules.DifferentialGradedModule
