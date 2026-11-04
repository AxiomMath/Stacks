module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.RingTheory.Flat.DirectLimit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMap
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedFlatRepresentative
public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.Free

/-!
# K-flat resolutions whose associated sheaf is again K-flat

Let `(X, 𝒪_X)` be a ringed space and `A = Γ(X, 𝒪_X)`.  Every complex `G` of `A`-modules
receives a quasi-isomorphism from a K-flat complex `T` of flat `A`-modules whose associated
sheaf `T ⊗_A 𝒪_X` is in turn a K-flat complex of flat `𝒪_X`-modules.

## Main results

* `Stacks.AssociatedSheaf.KFlatResolution.isFlat_assocSheaf_of_projective`: the sheaf
  associated to a projective `A`-module is a flat `𝒪_X`-module.
* `Stacks.AssociatedSheaf.KFlatResolution.exists_kFlat_resolution_assocFlat`: the
  strengthened form of Stacks 06Y4 described above.

## Implementation notes

The resolution is the one Stacks 06Y4 produces, namely the sequential colimit of the ladder
of complexes of Stacks 06XX resolving the canonical truncations `τ_{≤ n} G` by complexes which
are bounded above with *projective* terms.  Projectivity of the terms, rather than mere
flatness, is what makes the two extra conclusions available: a projective module is a retract
of a free one, the associated sheaf of a free `A`-module is a free sheaf of `𝒪_X`-modules
(Stacks 01BH), hence a direct sum of copies of `𝒪_X` and so flat by Stacks 03EU, and flatness
passes to retracts.

Both extra conclusions are then read off the presentation of the resolution as a colimit
rather than from K-flatness of the resolution itself: the associated-sheaf functor is a left
adjoint, so it commutes with the colimit degreewise, each stage becomes a bounded above complex
of flat `𝒪_X`-modules, and the two clauses of Stacks 06YS's colimit criterion apply to the
resulting sequence.

That the sequential-colimit comparison map is a quasi-isomorphism is
`StacksDraft.UnboundedLeftDerivedFunctor.quasiIso_of_isColimit_of_quasiIso_truncLE`: in each fixed
degree the homology of the ladder is eventually constant, and homology commutes with the colimit
since sequential colimits of `A`-modules are exact.

## References

* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Stacks Project, Tag 06XX](https://stacks.math.columbia.edu/tag/06XX)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 03EU](https://stacks.math.columbia.edu/tag/03EU)
* [Stacks Project, Tag 02N4](https://stacks.math.columbia.edu/tag/02N4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (Modules KFlat)
open Stacks.Cohomology.GlobalKunneth (baseRing)

universe u v w

namespace Stacks.AssociatedSheaf.KFlatResolution

/-! ### The sheaf associated to a projective module -/

attribute [local instance] hasModuleSheafify moduleSheafifyWEqualsLocallyBijective

variable (X : RingedSpace.{u, u})

/-- **The sheaf of `𝒪_X`-modules associated to an `A`-module**, `M ↦ M ⊗_A 𝒪_X` for
`A = Γ(X, 𝒪_X)`: the sheafification of `U ↦ 𝒪_X(U) ⊗_A M`. -/
def assocSheaf : ModuleCat.{u} (baseRing X) ⥤ Modules X :=
  associatedSheafFunctor.{u, u} X (RingHom.id (baseRing X))

/-- **`M ⊗_A 𝒪_X` is left adjoint to `Γ(X, -)`**, the global sections with scalars restricted
to `A`. -/
def assocAdjunction :
    assocSheaf X ⊣ globalSectionsFunctor.{u, u} X (RingHom.id (baseRing X)) :=
  associatedSheafAdjunction.{u, u} X (RingHom.id (baseRing X))

/-- `M ↦ M ⊗_A 𝒪_X` is a left adjoint. -/
instance assocSheaf_isLeftAdjoint : (assocSheaf X).IsLeftAdjoint :=
  ⟨_, ⟨assocAdjunction X⟩⟩

/-- `M ↦ M ⊗_A 𝒪_X` preserves sequential colimits, being a left adjoint. -/
instance assocSheaf_preservesColimitsOfShape_nat :
    PreservesColimitsOfShape ℕ (assocSheaf X) :=
  (assocAdjunction X).leftAdjoint_preservesColimits.preservesColimitsOfShape

/-- The associated-sheaf functor is additive: it is a left adjoint, hence preserves binary
biproducts. -/
instance assocSheaf_additive : (assocSheaf X).Additive := by
  have : PreservesColimitsOfShape (Discrete WalkingPair) (assocSheaf X) :=
    (assocAdjunction X).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (assocSheaf X)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- **The associated sheaf of a complex of `A`-modules**, formed degreewise. -/
abbrev assocSheafComplex :
    CochainComplex (ModuleCat.{u} (baseRing X)) ℤ ⥤ CochainComplex (Modules X) ℤ :=
  (assocSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **The sheaf associated to a free `A`-module is a flat `𝒪_X`-module.**  It is the free sheaf
of `𝒪_X`-modules on the same index set by Stacks 01BH, hence a direct sum of copies of `𝒪_X`,
which is flat by Stacks 03EU. -/
theorem isFlat_assocSheaf_free (I : Type u) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      ((assocSheaf X).obj ((ModuleCat.free (baseRing X)).obj I)) :=
  Stacks.SheafOfModules.FlatRetract.isFlat_of_iso.{u, u, u} X.sheaf
    (freeIsoAssociatedSheaf X (RingHom.id (baseRing X)) I)
    (Stacks.SheafOfModules.FlatCoproduct.isFlat_coproduct.{u, u} (O := X.sheaf)
      (fun _ : I =>
        Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.structureSheafModule X)
      (fun _ =>
        Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.isFlat_structureSheafModule X))

/-- **The sheaf associated to a projective `A`-module is a flat `𝒪_X`-module.**  A projective
module is a retract of a free one, the associated sheaf of a free module is flat, and flatness
of sheaves of modules passes to retracts. -/
theorem isFlat_assocSheaf_of_projective (P : ModuleCat.{u} (baseRing X)) (hP : Projective P) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      ((assocSheaf X).obj P) := by
  let e : (ModuleCat.free (baseRing X)).obj (P : Type u) ⟶ P :=
    ModuleCat.freeDesc (X := (P : Type u)) (M := P) (↾ fun x => x)
  have he : Epi e := (ModuleCat.epi_iff_surjective e).2 fun m => ⟨ModuleCat.freeMk m, by simp [e]⟩
  refine Stacks.SheafOfModules.FlatRetract.isFlat_of_retract.{u, u, u} X.sheaf
    ((assocSheaf X).map (Projective.factorThru (𝟙 P) e)) ((assocSheaf X).map e) ?_
    (isFlat_assocSheaf_free X (P : Type u))
  rw [← (assocSheaf X).map_comp, Projective.factorThru_comp, (assocSheaf X).map_id]

/-- **The associated sheaf of a bounded above complex is bounded above**, by the same bound: the
associated-sheaf functor is additive, hence carries zero objects to zero objects. -/
theorem isStrictlyLE_assocSheafComplex (K : CochainComplex (ModuleCat.{u} (baseRing X)) ℤ)
    (n : ℤ) (hK : K.IsStrictlyLE n) : ((assocSheafComplex X).obj K).IsStrictlyLE n :=
  (((assocSheafComplex X).obj K).isStrictlyLE_iff n).2 fun j hj =>
    (assocSheaf X).map_isZero ((K.isStrictlyLE_iff n).mp hK j hj)

/-! ### Sequential colimits of bounded above complexes of projectives -/

section Colimit

variable (D : ℕ ⥤ CochainComplex (ModuleCat.{u} (baseRing X)) ℤ)

/-- The terms of the associated sheaf of a sequence of complexes of projective `A`-modules are
flat `𝒪_X`-modules. -/
theorem isFlat_assocSheafComplex_comp_X
    (hproj : ∀ (n : ℕ) (i : ℤ), Projective ((D.obj n).X i)) (n : ℕ) (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      (((D ⋙ assocSheafComplex X).obj n).X i) :=
  isFlat_assocSheaf_of_projective X ((D.obj n).X i) (hproj n i)

/-- **The associated sheaf of a sequential colimit of bounded above complexes of projective
`A`-modules is K-flat.**  Each stage becomes a bounded above complex of flat `𝒪_X`-modules,
hence is K-flat by Stacks 06YQ, and K-flatness passes to the colimit. -/
theorem kFlat_assocSheafComplex_colimit
    (hLE : ∀ n : ℕ, ∃ b : ℤ, (D.obj n).IsStrictlyLE b)
    (hproj : ∀ (n : ℕ) (i : ℤ), Projective ((D.obj n).X i)) :
    KFlat X ((assocSheafComplex X).obj (colimit D)) := by
  have hLE' : ∀ n : ℕ, ∃ b : ℤ, ((D ⋙ assocSheafComplex X).obj n).IsStrictlyLE b :=
    fun n => (hLE n).imp fun b => isStrictlyLE_assocSheafComplex X (D.obj n) b
  have hcol : KFlat X (colimit (D ⋙ assocSheafComplex X)) :=
    Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat
      (R := X.sheaf) (D ⋙ assocSheafComplex X) hLE'
      (isFlat_assocSheafComplex_comp_X X D hproj)
  intro E hE n
  exact (hcol E hE n).of_iso <| Functor.mapIso _ (preservesColimitIso (assocSheafComplex X) D).symm

/-- **The terms of the associated sheaf of a sequential colimit of complexes of projective
`A`-modules are flat `𝒪_X`-modules**, by Stacks 03EU: a filtered colimit of flat sheaves of
modules is flat. -/
theorem isFlat_assocSheafComplex_colimit_X
    (hproj : ∀ (n : ℕ) (i : ℤ), Projective ((D.obj n).X i)) (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      (((assocSheafComplex X).obj (colimit D)).X i) :=
  Stacks.SheafOfModules.FlatRetract.isFlat_of_iso.{u, u, u} X.sheaf
    ((HomologicalComplex.eval _ _ i).mapIso (preservesColimitIso (assocSheafComplex X) D).symm)
    (Stacks.SheafOfModules.KFlatResolution.isFlat_colimit_X (R := X.sheaf)
      (D ⋙ assocSheafComplex X) (isFlat_assocSheafComplex_comp_X X D hproj) i)

end Colimit

/-! ### The resolution -/

/-- **Stacks 06Y4, strengthened by Stacks 06YC and 02N4 for the associated sheaf.**  Every
complex `G` of `A`-modules, `A = Γ(X, 𝒪_X)`, admits a quasi-isomorphism from a K-flat complex
`T` of flat `A`-modules whose associated sheaf `T ⊗_A 𝒪_X` is again a K-flat complex, with flat
terms, of `𝒪_X`-modules. -/
theorem exists_kFlat_resolution_assocFlat
    (G : CochainComplex (ModuleCat.{u} (baseRing X)) ℤ) :
    ∃ (T : CochainComplex (ModuleCat.{u} (baseRing X)) ℤ) (t : T ⟶ G),
      T.KFlat ∧ (∀ i : ℤ, Module.Flat (baseRing X) (T.X i)) ∧ QuasiIso t ∧
        Stacks.SheafOfModules.IsKFlat X.sheaf ((assocSheafComplex X).obj T) ∧
        (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
          (((assocSheafComplex X).obj T).X i)) := by
  let A := baseRing X
  let P : ObjectProperty (ModuleCat.{u} A) := fun Y => Projective Y
  let _ : P.ContainsZero := ⟨ModuleCat.of A (Fin 0 → A),
    ModuleCat.isZero_of_subsingleton _, inferInstance⟩
  have hsum : ∀ Y Z : ModuleCat.{u} A, P Y → P Z → P (Y ⊞ Z) :=
    fun Y Z (_ : Projective Y) (_ : Projective Z) => (inferInstance : Projective (Y ⊞ Z))
  have hcover : ∀ Y : ModuleCat.{u} A, ∃ (Z : ModuleCat.{u} A) (_ : P Z) (p : Z ⟶ Y), Epi p :=
    fun Y => ⟨Projective.over Y, inferInstance, Projective.π Y, inferInstance⟩
  obtain ⟨Q, q, g, hq, -, hle, hproj, -, hladder⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncLE P hsum hcover G
  let D := Functor.ofSequence g
  have hc : IsColimit (colimit.cocone D) := colimit.isColimit D
  let s : Cocone D := Cocone.mk G
    (NatTrans.ofSequence (fun n => q n ≫ G.ιTruncLE (n : ℤ)) (fun n => by
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
      exact (hladder n).trans (Category.comp_id _).symm))
  let α : colimit D ⟶ G := hc.desc s
  have hα : ∀ n : ℕ, (colimit.cocone D).ι.app n ≫ α = q n ≫ G.ιTruncLE (n : ℤ) :=
    fun n => hc.fac s n
  have hQproj : ∀ (n : ℕ) (i : ℤ), Projective ((D.obj n).X i) := hproj
  have hQflat : ∀ (n : ℕ) (i : ℤ), Module.Flat A ((Q n).X i) := by
    intro n i
    let _ : Projective ((Q n).X i) := hproj n i
    infer_instance
  have hqi : QuasiIso α :=
    let _ : AB5OfSize.{0, 0, u, u + 1} AddCommGrpCat.{u} :=
      AB5OfSize_of_univLE.{0, 0, u, u} AddCommGrpCat.{u}
    let _ : HasExactColimitsOfShape ℕ (ModuleCat.{u} A) :=
      HasExactColimitsOfShape.domain_of_functor ℕ
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})
    StacksDraft.UnboundedLeftDerivedFunctor.quasiIso_of_isColimit_of_quasiIso_truncLE q hq hc α hα
  have hkQ : ∀ n, (Q n).KFlat := fun n =>
    have := hle n
    have := hQflat n
    CochainComplex.KFlat.kFlat_of_flat (Q n) n
  have hterms : ∀ i : ℤ, Module.Flat A ((colimit D).X i) := by
    intro i
    have ht : Module.Flat A (colimit (D ⋙ HomologicalComplex.eval _ _ i) : ModuleCat A) :=
      CochainComplex.KFlat.flat_colimit.{u, u} _ (fun n => hQflat n i)
    exact @Module.Flat.of_linearEquiv A _ _ _ _ _ _ _ ht
      (preservesColimitIso (HomologicalComplex.eval _ _ i) D).toLinearEquiv
  exact ⟨colimit D, α, CochainComplex.KFlat.kFlat_colimit D hkQ, hterms, hqi,
    kFlat_assocSheafComplex_colimit X D (fun n => ⟨(n : ℤ), hle n⟩) hQproj,
    isFlat_assocSheafComplex_colimit_X X D hQproj⟩

end Stacks.AssociatedSheaf.KFlatResolution

end
