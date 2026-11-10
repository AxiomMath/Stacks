module

public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraAffineSections
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraSheafFunctorial
public import StacksFrontier.LinearAlgebra.SymmetricAlgebra.CorankOneQuotient
public import StacksFrontier.LinearAlgebra.SymmetricAlgebra.AdjoinDegreeOneGraded
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Sections

/-!
# The sections of `Sym(ℱ)` over an affine open are natural in `ℱ`

Let `X` be a scheme, `V ⊆ X` an affine open and `ℱ` a quasi-coherent `𝒪_X`-module. The sections
of the algebra sheaf `Sym(ℱ)` over `V` are the symmetric algebra `Sym_{Γ(X, V)}(Γ(ℱ, V))`
(`Stacks.SymAlgSections.symSectionsRingEquiv`). This file proves that the identification is
natural in `ℱ`: for a morphism `f : ℱ ⟶ 𝒢` of quasi-coherent modules, `Sym(f)` acts on sections
over `V` as the algebra map of symmetric algebras induced by `Γ(f, V)`.

## Main results

* `Stacks.SymAlgSections.symmetricAlgebraGen_app`: the degree-one generator of `Sym(ℱ)` at a
  section `m` is the sheafification unit applied to the generator `ι m`.
* `Stacks.SymAlgSections.symSectionsRingEquiv_ι_eq_ungradedIncl`: the identification carries
  the generator `ι m` to the degree-one section given by the generator of `Sym(ℱ)` at `m`.
* `Stacks.SymAlgSections.symmetricAlgebraSheafMap_symSectionsRingEquiv`: the identification is
  natural in `ℱ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open PresheafOfModules

universe u

namespace Stacks.SymAlgSections

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] {V : X.Opens}
  (hV : IsAffineOpen V)

/-- The degree-one generator of `Sym(ℰ)` at a section `m` of `ℰ` is the sheafification unit
applied to the generator `ι m` of the sectionwise symmetric algebra. -/
theorem symmetricAlgebraGen_app (m : Γ(E, V)) :
    ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op V)) m =
      pieceUnit E hV 1 ⟨SymmetricAlgebra.ι Γ(X, V) Γ(E, V) m,
        SymPow.ι_mem_symmetricPowerInt_one _ _ m⟩ := by
  have htri : ((Scheme.Modules.sheafificationIso X E).hom.val.app (op V))
      (Hom.app ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        E.val) (op V) m) = m :=
    congrArg (fun g => Hom.app g (op V) m)
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).right_triangle_components E)
  have hinv : (Scheme.Modules.sheafificationIso X E).inv.val.app (op V) m =
      Hom.app ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        E.val) (op V) m := by
    conv_lhs => rw [← htri]
    exact congrArg (fun g => (SheafOfModules.Hom.val g).app (op V) _)
      (Scheme.Modules.sheafificationIso X E).hom_inv_id
  change (@PresheafOfModules.symmetricAlgebraSheafifyGen _ _ _ X.sheaf.obj X.ringCatSheaf
      (𝟙 X.ringCatSheaf.obj) (Scheme.Modules.isLocallyInjective_id_ringCatSheaf X)
      (Scheme.Modules.isLocallySurjective_id_ringCatSheaf X)
      inferInstance inferInstance E.val).val.app
    (op V) ((Scheme.Modules.sheafificationIso X E).inv.val.app (op V) m) = _
  rw [hinv]
  exact PresheafOfModules.unit_naturality_apply (symPowIntGen E.val) (op V) m

/-- **The identification of `Γ(V, Sym(ℰ))` with `Sym_{Γ(X, V)}(Γ(ℰ, V))` carries the generator
`ι m` to the degree-one section `m`.** -/
theorem symSectionsRingEquiv_ι_eq_ungradedIncl (m : Γ(E, V)) :
    symSectionsRingEquiv E hV (SymmetricAlgebra.ι Γ(X, V) Γ(E, V) m) =
      (Scheme.Modules.symmetricAlgebra X E).ungradedIncl 1
        (((Scheme.Modules.symmetricAlgebraGen X E).val.app (op V)) m) := by
  rw [symmetricAlgebraGen_app E hV m]
  have hmem := SymmetricAlgebra.ι_mem_symmetricPower_one (R := Γ(X, V)) (M := Γ(E, V)) m
  have hdec := DirectSum.decompose_of_mem
    (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) Γ(E, V)) hmem
  change Stacks.RelativeSpec.totalSectionsRingEquiv X (Scheme.Modules.symmetricAlgebra X E)
      (Scheme.Modules.symmetricAlgebra_mul_comm X E) hV
      (ofSymPowers E hV (DirectSum.decompose
        (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) Γ(E, V))
        (SymmetricAlgebra.ι Γ(X, V) Γ(E, V) m))) = _
  rw [hdec, ofSymPowers_of, symPowerIncl_apply]
  rfl

variable {E} in
/-- **The identification of the affine sections of `Sym(ℱ)` with the symmetric algebra of the
affine sections of `ℱ` is natural in `ℱ`**: `Sym(f)` acts on sections over an affine open as the
algebra map induced by `Γ(f, V)`. -/
theorem symmetricAlgebraSheafMap_symSectionsRingEquiv {G : X.Modules} [G.IsQuasicoherent]
    (f : E ⟶ G) (a : SymmetricAlgebra Γ(X, V) Γ(E, V)) :
    ((Scheme.Modules.symmetricAlgebraSheafMap X f).right.hom.app (op V)).hom
        (symSectionsRingEquiv E hV a) =
      symSectionsRingEquiv G hV
        (SymPow.symAlgMap (Stacks.AlgebraicGeometry.QcohLimits.appₗ f V) a) := by
  induction a using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, symSectionsRingEquiv_algebraMap, symSectionsRingEquiv_algebraMap]
    exact congrArg (fun g => (g.hom.app (op V)).hom r)
      (Under.w (Scheme.Modules.symmetricAlgebraSheafMap X f))
  | ι m =>
    rw [SymPow.symAlgMap_ι, symSectionsRingEquiv_ι_eq_ungradedIncl,
      symSectionsRingEquiv_ι_eq_ungradedIncl]
    refine (Scheme.Modules.symmetricAlgebraSheafMap_ungradedIncl X f (op V) 1 _).trans ?_
    congr 1
    exact congrArg (fun g => ((SheafOfModules.Hom.val g).app (op V)) m)
      (Scheme.Modules.symmetricAlgebraGen_comp_symmetricAlgebraUnitalHom X f)
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

end Stacks.SymAlgSections

end
