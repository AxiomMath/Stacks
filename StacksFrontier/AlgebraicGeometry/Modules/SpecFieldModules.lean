module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.KrullDimension.Zero
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde

/-!
# Modules on the spectrum of a field

The spectrum of a field is a one-point space, and a sheaf of modules on it is determined by its
module of global sections: `tilde.functor` and `moduleSpecΓFunctor` are mutually inverse
equivalences between `ModuleCat k` and `(Spec k).Modules`.  Consequently pullback along the
morphism of affine schemes induced by a homomorphism of fields is, up to those equivalences,
extension of scalars, and therefore exact.

## Main definitions

* `AlgebraicGeometry.SpecField.modulesEquiv` is the equivalence
  `ModuleCat R ≌ (Spec R).Modules`.
* `AlgebraicGeometry.SpecField.pullbackIso` presents pullback along `Spec l ⟶ Spec k` as global
  sections, then extension of scalars, then the associated sheaf.

## Main results

* `AlgebraicGeometry.SpecField.isIso_fromTildeΓ`: over a field, every sheaf of modules on the
  spectrum lies in the essential image of the associated-sheaf functor.
* `AlgebraicGeometry.SpecField.preservesFiniteLimits_pullback` and
  `AlgebraicGeometry.SpecField.preservesFiniteColimits_pullback`: pullback along the morphism
  induced by a homomorphism of fields is exact.
* `AlgebraicGeometry.SpecField.finrank_pullback`: the dimension of the global sections of a
  pullback is the dimension of the global sections of the original module.

## Implementation notes

Invertibility of the counit `Scheme.Modules.fromTildeΓ` is checked on the sheaf level, where the
only opens are `⊥` and `⊤` because the carrier of `Spec k` is a subsingleton: at `⊥` both sides
are terminal, and at `⊤` the map is inverse to `tilde.toOpen`, which is invertible by
`AlgebraicGeometry.tilde.isIso_toOpen_top`.  Fullness and faithfulness of
`modulesSpecToSheaf` then transport invertibility back to the module category.

Exactness of pullback is read off the presentation `pullbackIso` rather than from flatness of
the stalk map: the two outer functors are halves of equivalences, and extension of scalars along
a homomorphism out of a field is exact because every module over a field is flat.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.SpecField

universe u

/-- The carrier of the spectrum of a field is a subsingleton: a field has exactly one prime
ideal. -/
public theorem subsingleton_carrier {R : CommRingCat.{u}} (hR : IsField R) :
    Subsingleton (Spec R) := by
  change Subsingleton (PrimeSpectrum R)
  let : Field R := hR.toField
  exact Ring.KrullDimLE.subsingleton_primeSpectrum _

/-- **Over a field every sheaf of modules on the spectrum comes from its global sections.**  The
counit `Scheme.Modules.fromTildeΓ` of the associated-sheaf adjunction is invertible. -/
public theorem isIso_fromTildeΓ {R : CommRingCat.{u}} (hR : IsField R)
    (M : (Spec R).Modules) : IsIso M.fromTildeΓ := by
  have := subsingleton_carrier hR
  let ΓM : ModuleCat R := (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)
  have hmap : IsIso (modulesSpecToSheaf.map M.fromTildeΓ) := by
    apply (isIso_iff_of_reflects_iso (modulesSpecToSheaf.map M.fromTildeΓ)
      (TopCat.Sheaf.forget _ _)).mp
    rw [NatTrans.isIso_iff_isIso_app]
    rintro ⟨U⟩
    rcases U.eq_bot_or_top with rfl | rfl
    · change IsIso ((modulesSpecToSheaf.map M.fromTildeΓ).hom.app (.op ⊥))
      have hF := TopCat.Sheaf.isTerminalOfEmpty (modulesSpecToSheaf.obj M)
      have hT := TopCat.Sheaf.isTerminalOfEmpty (modulesSpecToSheaf.obj (tilde ΓM))
      exact ⟨⟨hT.from _, hT.hom_ext _ _, hF.hom_ext _ _⟩⟩
    · change IsIso ((modulesSpecToSheaf.map M.fromTildeΓ).hom.app (.op ⊤))
      have : IsIso (tilde.toOpen ΓM ⊤) := tilde.isIso_toOpen_top
      have heq : tilde.toOpen ΓM ⊤ ≫
          (modulesSpecToSheaf.map M.fromTildeΓ).hom.app (.op ⊤) = 𝟙 ΓM := by
        simpa using Scheme.Modules.toOpen_fromTildeΓ_app M ⊤
      rw [IsIso.eq_inv_of_hom_inv_id heq]
      infer_instance
  exact SpecModulesToSheafFullyFaithful.isIso_of_isIso_map M.fromTildeΓ

section Equivalence

variable {R : CommRingCat.{u}} (hR : IsField R)

include hR

/-- **A sheaf of modules on the spectrum of a field is its module of global sections.**  The
associated-sheaf adjunction is an equivalence `ModuleCat R ≌ (Spec R).Modules`. -/
public def modulesEquiv : ModuleCat R ≌ (Spec R).Modules :=
  haveI : ∀ M : ModuleCat R, IsIso ((tilde.adjunction (R := R)).unit.app M) := fun M =>
    NatIso.isIso_app_of_isIso (tilde.toTildeΓNatIso (R := R)).hom M
  haveI : ∀ M : (Spec R).Modules, IsIso ((tilde.adjunction (R := R)).counit.app M) := fun M =>
    isIso_fromTildeΓ hR M
  (tilde.adjunction (R := R)).toEquivalence

/-- The functor of `modulesEquiv` is the associated-sheaf functor. -/
@[simp]
public theorem modulesEquiv_functor : (modulesEquiv hR).functor = tilde.functor R := rfl

/-- The inverse of `modulesEquiv` is the global-sections functor. -/
@[simp]
public theorem modulesEquiv_inverse : (modulesEquiv hR).inverse = moduleSpecΓFunctor := rfl

/-- Global sections on the spectrum of a field preserve finite limits. -/
public theorem preservesFiniteLimits_moduleSpecΓFunctor :
    PreservesFiniteLimits (moduleSpecΓFunctor (R := R)) :=
  have : (moduleSpecΓFunctor (R := R)).IsEquivalence := (modulesEquiv hR).isEquivalence_inverse
  inferInstance

/-- The associated-sheaf functor on the spectrum of a field is an equivalence. -/
public theorem isEquivalence_tildeFunctor : (tilde.functor R).IsEquivalence :=
  (modulesEquiv hR).isEquivalence_functor

end Equivalence

section Pullback

variable {R S : CommRingCat.{u}} (hR : IsField R) (hS : IsField S) (φ : R ⟶ S)

include hR in
/-- **Pullback along a morphism of spectra of fields is extension of scalars.**  The pullback
`(Spec φ)^*` is isomorphic to global sections, followed by extension of scalars along `φ`,
followed by the associated-sheaf functor: the affine pullback comparison of Tag 01I9 precomposed
with the inverse of `modulesEquiv`. -/
public def pullbackIso :
    Scheme.Modules.pullback (Spec.map φ) ≅
      moduleSpecΓFunctor (R := R) ⋙ ModuleCat.extendScalars φ.hom ⋙ tilde.functor S :=
  ((modulesEquiv hR).invFunIdAssoc (Scheme.Modules.pullback (Spec.map φ))).symm ≪≫
    Functor.isoWhiskerLeft (moduleSpecΓFunctor (R := R)) (pullbackTildeIso R S φ)

include hR in
/-- A homomorphism out of a field is flat: every module over a field is free, hence flat. -/
public theorem flat_of_field : (CommRingCat.Hom.hom φ).Flat :=
  let := (CommRingCat.Hom.hom φ).toAlgebra
  let : Field R := hR.toField
  have : Module.Free R S := Module.Free.of_divisionRing _ _
  inferInstanceAs (Module.Flat R S)

include hR hS in
/-- **Pullback along a morphism of spectra of fields is left exact.**  In the presentation
`pullbackIso` the outer two functors are halves of equivalences and the middle one is
extension of scalars along a flat homomorphism. -/
public theorem preservesFiniteLimits_pullback :
    PreservesFiniteLimits (Scheme.Modules.pullback (Spec.map φ)) := by
  have : PreservesFiniteLimits (ModuleCat.extendScalars (CommRingCat.Hom.hom φ)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (flat_of_field hR φ)
  have := preservesFiniteLimits_moduleSpecΓFunctor hR
  have := isEquivalence_tildeFunctor hS
  have : PreservesFiniteLimits (tilde.functor S) := inferInstance
  exact preservesFiniteLimits_of_natIso (pullbackIso hR φ).symm

/-- **Pullback along a morphism of spectra of fields is right exact.**  It is a left adjoint. -/
public theorem preservesFiniteColimits_pullback :
    PreservesFiniteColimits (Scheme.Modules.pullback (Spec.map φ)) :=
  have : PreservesColimitsOfSize.{0, 0} (Scheme.Modules.pullback (Spec.map φ)) :=
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).leftAdjoint_preservesColimits
  inferInstance

include hR in
/-- The global sections of a pullback along a morphism of spectra of fields are the extension
of scalars of the global sections. -/
public def pullbackSectionsIso (M : (Spec R).Modules) :
    (moduleSpecΓFunctor (R := S)).obj ((Scheme.Modules.pullback (Spec.map φ)).obj M) ≅
      (ModuleCat.extendScalars (CommRingCat.Hom.hom φ)).obj
        ((moduleSpecΓFunctor (R := R)).obj M) :=
  (moduleSpecΓFunctor (R := S)).mapIso ((pullbackIso hR φ).app M) ≪≫
    (tilde.toTildeΓNatIso (R := S)).symm.app _

include hR hS in
/-- Extension of scalars along a homomorphism of fields does not change the dimension. -/
public theorem finrank_extendScalars (M : ModuleCat R) :
    Module.finrank S ((ModuleCat.extendScalars (CommRingCat.Hom.hom φ)).obj M) =
      Module.finrank R M := by
  let := (CommRingCat.Hom.hom φ).toAlgebra
  let : Field R := hR.toField
  let : Field S := hS.toField
  change Module.finrank S (TensorProduct R S M) = Module.finrank R M
  exact Module.finrank_baseChange

include hR hS in
/-- **The dimension of the global sections is unchanged by pullback along a morphism of spectra
of fields.** -/
public theorem finrank_pullback (M : (Spec R).Modules) :
    Module.finrank S ((moduleSpecΓFunctor (R := S)).obj
        ((Scheme.Modules.pullback (Spec.map φ)).obj M)) =
      Module.finrank R ((moduleSpecΓFunctor (R := R)).obj M) :=
  (pullbackSectionsIso hR φ M).toLinearEquiv.finrank_eq.trans
    (finrank_extendScalars hR hS φ _)

end Pullback

end AlgebraicGeometry.SpecField

end
