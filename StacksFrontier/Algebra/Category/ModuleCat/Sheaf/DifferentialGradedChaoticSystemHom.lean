module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticRealization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiIsoEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionExact

/-!
# Morphisms of inverse systems of differential graded algebras, as maps of sheaves

Let `A` and `B` be inverse systems of differential graded `R`-algebras indexed by a category `C`,
that is functors `Cᵒᵖ ⥤ DGA(R)`, realized as sheaves of differential graded algebras on `C` with
the chaotic topology by `Stacks.ChaoticSite.systemAlgebra`. A representative of a morphism of
pro-objects `(A_i) → (B_i)` — a reindexing functor `F : C ⥤ C` together with a natural
transformation `F.op ⋙ A ⟶ B` — is then a map `g^*𝒜 → ℬ` of sheaves of differential graded
algebras along the morphism of chaotic sites induced by `F`, over the identity of the constant
sheaf of rings: a `SheafOfModules.DifferentialGradedAlgebra.InverseImageHom`.

## Main definitions

* `Stacks.ChaoticSite.constRingInverseImage`: the identity `g⁻¹O ⟶ O` of the constant sheaf of
  rings along a functor of chaotic sites.
* `Stacks.ChaoticSite.systemInverseImageHom`: the map of sheaves of differential graded algebras
  attached to a natural transformation `F.op ⋙ A ⟶ B`.
* `Stacks.ChaoticSite.systemAlgebraHom`: a morphism `A ⟶ B` of inverse systems, as a
  homomorphism of the sheaves of differential graded algebras on the same site; it preserves the
  unit (`systemAlgebraHom_preservesOne`) and is a quasi-isomorphism as soon as every component
  is (`isQuasiIso_systemAlgebraHom`).

## References

* [Stacks Project, Section 24.35 (Tag 0GZG)](https://stacks.math.columbia.edu/tag/0GZG)
* [Stacks Project, Lemma 24.33.4 (Tag 0GZC)](https://stacks.math.columbia.edu/tag/0GZC)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u u₁ v₁ u₂ v₂

namespace Stacks.ChaoticSite

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C'] {Λ : Type u}
  [CommRing Λ]

/-- The identity of the constant sheaf of rings with value `Λ`, read as a map `g⁻¹O ⟶ O` along
the morphism of chaotic sites induced by a functor `F : C' ⥤ C`. -/
def constRingInverseImage (F : C' ⥤ C) :
    F.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.PresheafOfModules.constCommRingSheaf (C := C) Λ)).obj ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.PresheafOfModules.constCommRingSheaf (C := C') Λ)).obj where
  app _ := 𝟙 _
  naturality _ _ _ := rfl

/-- **A representative of a morphism of pro-objects of inverse systems of differential graded
algebras, as a map of the sheaves they define.** For `φ : F.op ⋙ A ⟶ B` the map in degree `n`
over `U'` is the restriction of `φ_{U'} : A(F U') ⟶ B(U')` to the degree-`n` pieces. -/
def systemInverseImageHom {A : Cᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} Λ}
    {B : C'ᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} Λ} (F : C' ⥤ C) (φ : F.op ⋙ A ⟶ B) :
    SheafOfModules.DifferentialGradedAlgebra.InverseImageHom (C := C) (C' := C')
      (Osharp := Stacks.PresheafOfModules.constCommRingSheaf (C := C) Λ)
      (Osharp' := Stacks.PresheafOfModules.constCommRingSheaf (C := C') Λ)
      F (constRingInverseImage F) (systemAlgebra A) (systemAlgebra B) where
  app n U' :=
    { toFun := fun x => ⟨(φ.app U').toAlgebraHom x.val, (φ.app U').map_grading n x.val x.2⟩
      map_zero' := Subtype.ext (map_zero (φ.app U').toAlgebraHom)
      map_add' := fun x y => Subtype.ext (map_add (φ.app U').toAlgebraHom x.val y.val) }
  app_smul n U' r x := Subtype.ext ((φ.app U').toAlgebraHom.map_smul_of_tower (show Λ from r) x.val)
  naturality n U' V' a x := Subtype.ext
    (congrArg (fun g : DifferentialGradedAlgebra.Hom _ _ => g.toAlgebraHom x.val)
      (φ.naturality a))
  app_d n U' x := by
    apply Subtype.ext
    change (φ.app U').toAlgebraHom
        ((((systemComplex A).d n (n + 1)).val.app (F.op.obj U') x).val) =
      (((systemComplex B).d n (n + 1)).val.app U'
        ⟨(φ.app U').toAlgebraHom x.val, (φ.app U').map_grading n x.val x.2⟩).val
    rw [systemComplex_d_val_app, systemComplex_d_val_app]
    exact (φ.app U').map_d x.val
  app_mul n i U' x y := Subtype.ext (map_mul (φ.app U').toAlgebraHom x.val y.val)
  app_one U' := Subtype.ext (map_one (φ.app U').toAlgebraHom)

/-- **A morphism of inverse systems of differential graded algebras, as a homomorphism of the
sheaves of differential graded algebras they define** on the same chaotic site: over `U` it is
`φ_U` on each homogeneous piece. The underlying morphism of complexes is the image under the
realization of the morphism of complexes of functors induced by `φ`. -/
def systemAlgebraHom {A B : Cᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} Λ} (φ : A ⟶ B) :
    systemAlgebra A ⟶ systemAlgebra B where
  toHomologicalComplex :=
    ((Stacks.PresheafOfModules.ofFunctorSheaf Λ).mapHomologicalComplex (ComplexShape.up ℤ)).map
      { f := fun i => Functor.whiskerRight
          (Functor.whiskerRight φ DifferentialGradedAlgebra.toCochainComplexFunctor)
          (HomologicalComplex.eval _ _ i)
        comm' := fun i j _ => NatTrans.ext (funext fun U => (φ.app U).toCochainMap.comm i j) }
  map_mul _ _ U x y := Subtype.ext (map_mul (φ.app U).toAlgebraHom x.val y.val)

/-- The homomorphism attached to a morphism of inverse systems is `φ_U` on sections. -/
theorem systemAlgebraHom_app_val {A B : Cᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} Λ} (φ : A ⟶ B)
    (n : ℤ) (U : Cᵒᵖ) (x : ((systemComplex A).X n).val.obj U) :
    (((systemAlgebraHom φ).toHomologicalComplex.f n).val.app U x).val =
      (φ.app U).toAlgebraHom x.val :=
  rfl

/-- The homomorphism attached to a morphism of inverse systems preserves the unit. -/
theorem systemAlgebraHom_preservesOne {A B : Cᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} Λ}
    (φ : A ⟶ B) : (systemAlgebraHom φ).PreservesOne :=
  fun U => Subtype.ext (map_one (φ.app U).toAlgebraHom)

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective in
/-- **A morphism of inverse systems which is a quasi-isomorphism at every stage is a
quasi-isomorphism of the sheaves of differential graded algebras**: on a chaotic site a morphism
of complexes of sheaves of modules is a quasi-isomorphism exactly when it is one over every
object. -/
theorem isQuasiIso_systemAlgebraHom [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{u}]
    {A B : Cᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} Λ} (φ : A ⟶ B)
    (h : ∀ U : Cᵒᵖ, QuasiIso (φ.app U).toCochainMap) : (systemAlgebraHom φ).IsQuasiIso :=
  (Stacks.SheafOfModules.quasiIso_iff_forall_quasiIso_evaluation _).2 h

end Stacks.ChaoticSite
