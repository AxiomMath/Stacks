module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.OpenExtension
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.FinitePresentationExtension

/-!
# Extending finite type and finitely presented modules from an open subscheme

Modules of finite type, and finitely presented modules, on a quasi-compact open subscheme of a
quasi-compact and quasi-separated scheme extend to the whole scheme while retaining the
corresponding finiteness property.

## Main results

* `AlgebraicGeometry.exists_extension_of_isQuasicoherent_isFiniteType` extends a quasi-coherent
  module of finite type.
* `AlgebraicGeometry.exists_extension_of_isFinitePresentation` extends a finitely presented
  module.

## Implementation notes

The restriction equalities of the source are represented by isomorphisms of sheaves of modules,
and the two independent parts of the source statement are separate theorems.

Part (1) extends the module to a quasi-coherent module by [Stacks, Tag 01PE] and then cuts the
extension down to a finite-type quasi-coherent submodule by [Stacks, Tag 01PF]. Part (2) is the
extension of a morphism, `AlgebraicGeometry.exists_finitePresentation_extension_of_hom`, applied
to the zero module and the zero morphism.

## References

* [Stacks Project, Tag 0G41](https://stacks.math.columbia.edu/tag/0G41)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ZeroObject

universe u

namespace AlgebraicGeometry

/-- A quasi-coherent module of finite type on a quasi-compact open of a quasi-compact and
quasi-separated scheme extends to a quasi-coherent module of finite type on the whole scheme. -/
@[stacks 0G41 "part (1)", ega "I 9.4.8", ega "I 9.4.5"]
lemma exists_extension_of_isQuasicoherent_isFiniteType {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsCompact U.1)
    (G : U.toScheme.Modules) [G.IsQuasicoherent] [G.IsFiniteType] :
    ∃ (G' : X.Modules) (_ : G'.IsQuasicoherent) (_ : G'.IsFiniteType),
      Nonempty (G'.restrict U.ι ≅ G) := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have : QuasiCompact U.ι := inferInstance
  obtain ⟨F, hF, ⟨e⟩⟩ := exists_quasicoherent_restrict_iso U.ι G
  have : F.IsQuasicoherent := hF
  let G₀ : Subobject (F.restrict U.ι) := Subobject.mk e.inv
  let e₀ : (G₀ : U.toScheme.Modules) ≅ G := Subobject.underlyingIso e.inv
  have : (G₀ : U.toScheme.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso e₀.symm inferInstance
  have : (G₀ : U.toScheme.Modules).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} e₀.symm
  obtain ⟨G', hG'qc, hG'ft, ⟨e', _⟩⟩ :=
    exists_finiteTypeQuasicoherentSubobject_extension F U hU G₀
  exact ⟨G', hG'qc, hG'ft, ⟨e'.trans e₀⟩⟩

/-- A finitely presented module on a quasi-compact open of a quasi-compact and quasi-separated
scheme extends to a finitely presented module on the whole scheme. -/
@[stacks 0G41 "part (2)", ega "I 9.4.8" "special case"]
lemma exists_extension_of_isFinitePresentation {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsCompact U.1)
    (G : U.toScheme.Modules) [G.IsFinitePresentation] :
    ∃ (G' : X.Modules) (_ : G'.IsFinitePresentation), Nonempty (G'.restrict U.ι ≅ G) := by
  have : (0 : X.Modules).IsFinitePresentation := isFinitePresentation_zero X
  have : (0 : X.Modules).IsQuasicoherent :=
    _root_.isQuasicoherent_of_isFinitePresentation (0 : X.Modules)
  obtain ⟨G', hG', _, e, _⟩ :=
    exists_finitePresentation_extension_of_hom (F := (0 : X.Modules)) U hU G 0
  exact ⟨G', hG', ⟨e⟩⟩

end AlgebraicGeometry

end
